import DocGen4

/-!
# Export the doc database to JSON

Reads the database that `doc-gen4 single` fills (with doc-gen4's own reader) and writes the
documented modules to a JSON file that the Astro site in `docs/site` renders.

Usage: `lake env export-docs <database> <library> <output>`, run from `docbuild/`.

Type signatures come out as arrays of segments `{"s": text}`, where a segment may also carry
`"c": name` (a reference to a constant) or `"k": kind` (`keyword`, `string` or `sort`), so the
site can link names. Constants that aren't declared in the documented modules are listed under
`"external"` with the module that declares them, which is looked up in the environment of
`<library>`.

doc-gen4's database schema is internal: re-check this file whenever doc-gen4 is bumped.
-/

open Lean DocGen4 DocGen4.Process DocGen4.DB

namespace ExportDocs

/-- A JSON object, leaving out the fields that are `none`. -/
def obj (fields : List (String × Option Json)) : Json :=
  Json.mkObj (fields.filterMap fun (k, v) => v.map (k, ·))

/--
Flattens rendered code into its text pieces, each with the innermost tag around it. `otherExpr`
tags carry nothing to render, so they keep the tag around them.
-/
partial def flatten (tag : Option RenderedCode.Tag)
    (acc : Array (Option RenderedCode.Tag × String)) : RenderedCode →
    Array (Option RenderedCode.Tag × String)
  | .text "" => acc
  | .text s =>
    match acc.back? with
    | some (t, s') => if t == tag then acc.pop.push (t, s' ++ s) else acc.push (tag, s)
    | none => acc.push (tag, s)
  | .tag .otherExpr inner => flatten tag acc inner
  | .tag t inner => flatten (some t) acc inner
  | .append xs => xs.foldl (flatten tag) acc

/-- The constants rendered code refers to. -/
def constants (code : RenderedCode) : Array Name :=
  (flatten none #[] code).filterMap fun
    | (some (.const n), _) => some n
    | _ => none

def codeToJson (code : RenderedCode) : Json :=
  .arr <| (flatten none #[] code).map fun (tag, s) =>
    Json.mkObj <| ("s", toJson s) :: match tag with
      | some (.const n) => [("c", toJson n.toString)]
      | some .keyword => [("k", "keyword")]
      | some .string => [("k", "string")]
      | some (.sort _) => [("k", "sort")]
      | _ => []

def docToJson : Option (String ⊕ (VersoDocString × String)) → Option Json
  | some (.inl md) | some (.inr (_, md)) => some md
  | none => none

def argToJson (arg : Arg) : Json :=
  obj [("binder", codeToJson arg.binder), ("implicit", toJson arg.implicit)]

/-- What's common to all declarations, and to constructors and structure fields. -/
def infoFields (info : Info) : List (String × Option Json) := [
  ("name", toJson info.name.toString),
  ("args", toJson (info.args.map argToJson)),
  ("type", codeToJson info.type),
  ("doc", docToJson info.doc),
  ("line", toJson info.declarationRange.pos.line),
  ("endLine", toJson info.declarationRange.endPos.line),
  ("attrs", if info.attrs.isEmpty then none else toJson info.attrs),
  ("sorried", if info.sorried then toJson true else none)]

def infoToJson (info : Info) : Json := obj (infoFields info)

/-- The fields particular to a kind of declaration. -/
def kindFields : DocInfo → List (String × Option Json)
  | .instanceInfo i => [
    ("className", toJson i.className.toString),
    ("typeNames", toJson (i.typeNames.map (·.toString)))]
  | .inductiveInfo i | .classInductiveInfo i => [
    ("ctors", toJson (i.ctors.toArray.map infoToJson))]
  | .structureInfo i | .classInfo i => [
    ("ctor", obj [
      ("name", toJson i.ctor.name.toString),
      ("type", codeToJson i.ctor.type),
      ("doc", docToJson i.ctor.doc)]),
    ("fields", toJson (i.fieldInfo.map fun f =>
      obj (infoFields f.toInfo ++ [("isDirect", some (toJson f.isDirect))]))),
    ("parents", toJson (i.parents.map fun p =>
      obj [("projFn", toJson p.projFn.toString), ("type", codeToJson p.type)]))]
  | _ => []

/-- The rendered code of a declaration, including its constructors and fields. -/
def declCode (info : DocInfo) : Array RenderedCode :=
  let own (i : Info) := i.args.map (·.binder) |>.push i.type
  own info.toInfo ++ match info with
    | .inductiveInfo i | .classInductiveInfo i => i.ctors.toArray.flatMap own
    | .structureInfo i | .classInfo i =>
      i.fieldInfo.flatMap (own ·.toInfo) ++ i.parents.map (·.type) |>.push i.ctor.type
    | _ => #[]

/-- The names a declaration introduces: itself, its constructors and fields. -/
def declNames (info : DocInfo) : Array Name :=
  #[info.getName] ++ match info with
    | .inductiveInfo i | .classInductiveInfo i => i.ctors.toArray.map (·.name)
    | .structureInfo i | .classInfo i => i.fieldInfo.map (·.name) |>.push i.ctor.name
    | _ => #[]

def memberToJson : ModuleMember → Json
  | .modDoc doc => obj [
    ("kind", toJson "moduleDoc"),
    ("doc", toJson doc.doc),
    ("line", toJson doc.declarationRange.pos.line)]
  | .docInfo info => obj <|
    [("kind", some (toJson info.getKind)),
      ("kindDescription", some (toJson info.getKindDescription))] ++
      infoFields info.toInfo ++ kindFields info

def moduleToJson (sourceUrls : Std.HashMap Name String) (mod : Process.Module) : Json :=
  obj [
    ("name", toJson mod.name.toString),
    ("imports", toJson (mod.imports.map (·.toString))),
    ("sourceUrl", sourceUrls[mod.name]?.map toJson),
    ("members", toJson (mod.members.filter (·.shouldRender) |>.map memberToJson))]

/-- The module that declares each of `names`, from the environment of `library`. -/
def declaringModules (library : Name) (names : Array Name) : IO (Array (Name × Name)) := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := library }] {}
  return names.filterMap fun n =>
    env.getModuleIdxFor? n |>.bind fun idx => env.header.moduleNames[idx.toNat]? |>.map (n, ·)

end ExportDocs

open ExportDocs in
def main (args : List String) : IO UInt32 := do
  let [dbFile, library, output] := args
    | IO.eprintln "usage: export-docs <database> <library> <output>"
      return 1
  let db ← openForReading dbFile builtinDocstringValues
  let sourceUrls ← db.getModuleSourceUrls
  let names := (← db.getModuleNames).qsort (·.toString < ·.toString)
  let modules ← names.mapM db.loadModule
  let infos := modules.flatMap fun mod => mod.members.filterMap fun
    | .docInfo info => if info.shouldRender then some info else none
    | .modDoc _ => none
  let declared : NameSet := infos.foldl (init := {}) fun s i => (declNames i).foldl .insert s
  let referenced := infos.flatMap declCode |>.flatMap constants
  let external := referenced.foldl (init := ({} : NameSet)) fun s n =>
    if declared.contains n then s else s.insert n
  let external ← declaringModules library.toName external.toArray
  let json := obj [
    ("library", toJson library),
    ("modules", toJson (modules.map (moduleToJson sourceUrls))),
    ("external", Json.mkObj (external.toList.map fun (n, m) => (n.toString, toJson m.toString)))]
  IO.FS.writeFile output json.compress
  IO.println s!"Wrote {modules.size} modules to {output}"
  return 0
