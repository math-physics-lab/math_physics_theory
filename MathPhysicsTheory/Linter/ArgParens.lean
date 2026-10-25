module

public meta import Lean.Elab.Command
public meta import Lean.Linter.Basic
public import Lean.Message

/-!
# The argument parentheses linter

The `argParens` linter requires every explicit argument of a function application to be written
in brackets: `f (x) (y)` instead of `f x y`, `Set.Icc (a) (b)` instead of `Set.Icc a b`.

An argument counts as bracketed when it starts with an opening bracket and ends with the matching
closing bracket, e.g. `(x)`, `(x : ℝ)`, `(a, b)`, `⟨a, b⟩`, `[a, b]` or `{x | p x}`.
Named arguments `(x := e)` and `..` are not linted.
-/

meta section

open Lean Elab Command Linter

namespace MathPhysicsTheory.Linter.ArgParens

/-- The `argParens` linter flags arguments of function applications that are not written in
brackets, e.g. the `x` in `f x`. -/
public register_option linter.argParens : Bool := {
  defValue := false
  descr := "enable the `argParens` linter"
}

/-- Matching pairs of opening and closing brackets. -/
def brackets : List (String × String) :=
  [("(", ")"), ("⟨", "⟩"), ("[", "]"), ("![", "]"), ("#[", "]"), ("{", "}")]

/-- The last atom or identifier of `stx`. -/
partial def lastToken? : Syntax → Option Syntax
  | .node _ _ args => args.foldr (init := none) fun s acc => acc <|> lastToken? s
  | .missing => none
  | s => some s

/-- Whether the argument syntax starts with an opening bracket and ends with the matching closing
bracket. -/
def isBracketed (arg : Syntax) : Bool :=
  match arg.getHead?, lastToken? arg with
  | some (.atom _ o), some (.atom _ c) => brackets.contains (o, c)
  | _, _ => false

/-- The unbracketed arguments of all function applications in `stx`. -/
partial def unbracketedArgs (stx : Syntax) : Array Syntax :=
  let inner := stx.getArgs.foldl (init := #[]) fun acc s => acc ++ unbracketedArgs s
  if stx.isOfKind ``Parser.Term.app then
    inner ++ stx[1].getArgs.filter fun a =>
      !(isBracketed a || a.isOfKind ``Parser.Term.namedArgument ||
        a.isOfKind ``Parser.Term.ellipsis)
  else
    inner

/-- The `argParens` linter: see the module docstring. -/
def argParensLinter : Linter where run := withSetOptionIn fun stx => do
  unless getLinterValue linter.argParens (← getLinterOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  for arg in unbracketedArgs stx do
    logLint linter.argParens arg
      m!"Function arguments should be written in parentheses: `({arg})`."

initialize addLinter argParensLinter

end MathPhysicsTheory.Linter.ArgParens
