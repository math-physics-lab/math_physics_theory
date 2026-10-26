// Loads the docs data exported by `docbuild/ExportDocs.lean` and the per-module notes.

import fs from 'node:fs';
import path from 'node:path';

// Relative to the working directory, `docs/site` (npm runs scripts there): this module's own
// location changes when Astro bundles it.
const REPO_ROOT = path.resolve(process.cwd(), '../..');
const DOCS_JSON = process.env.DOCS_JSON ?? path.join(REPO_ROOT, 'docbuild/.lake/build/docs.json');
const HOME_PAGE = path.join(REPO_ROOT, 'docs/ROOT.md');

/** The Mathlib docs, which also cover Lean core. */
export const MATHLIB_DOCS = 'https://leanprover-community.github.io/mathlib4_docs/';
export const REPO_URL = 'https://github.com/math-physics-lab/math_physics_theory';

/** A piece of rendered code: a constant reference (`c`), a token kind (`k`), or plain text. */
export interface Segment {
	s: string;
	c?: string;
	k?: 'keyword' | 'string' | 'sort';
}
export type Code = Segment[];

export interface Arg {
	binder: Code;
	implicit: boolean;
}

/** What declarations, constructors and structure fields have in common. */
export interface Info {
	name: string;
	args: Arg[];
	type: Code;
	doc?: string;
	line: number;
	endLine: number;
	attrs?: string[];
	sorried?: boolean;
}

export type Kind = 'axiom' | 'theorem' | 'opaque' | 'def' | 'instance' | 'inductive' | 'structure' | 'class';

export interface Declaration extends Info {
	kind: Kind;
	/** E.g. `noncomputable def`, `class inductive`, `abbrev`. */
	kindDescription: string;
	// instance
	className?: string;
	typeNames?: string[];
	// inductive, class inductive
	ctors?: Info[];
	// structure, class
	ctor?: { name: string; type: Code; doc?: string };
	fields?: (Info & { isDirect: boolean })[];
	parents?: { projFn: string; type: Code }[];
}

export interface ModuleDoc {
	kind: 'moduleDoc';
	doc: string;
	line: number;
}

export interface Module {
	name: string;
	imports: string[];
	sourceUrl?: string;
	members: (Declaration | ModuleDoc)[];
}

interface DocsData {
	library: string;
	modules: Module[];
	/** The module declaring each referenced constant from outside the library. */
	external: Record<string, string>;
}

function load(): DocsData {
	if (!fs.existsSync(DOCS_JSON)) {
		throw new Error(`${DOCS_JSON} not found: run \`python3 docbuild/build_docs.py\` first, or set DOCS_JSON`);
	}
	return JSON.parse(fs.readFileSync(DOCS_JSON, 'utf-8'));
}

const data = load();

export const library = data.library;
export const modules = data.modules;

export function declarations(mod: Module): Declaration[] {
	return mod.members.filter((m): m is Declaration => m.kind !== 'moduleDoc');
}

export function moduleDocs(mod: Module): ModuleDoc[] {
	return mod.members.filter((m): m is ModuleDoc => m.kind === 'moduleDoc');
}

/** The site path of a module's page, relative to the base URL, e.g. `MathPhysicsTheory/SturmLiouville/`. */
export function modulePath(module: string): string {
	return module.split('.').join('/') + '/';
}

/** Prefixes `path` with the site's base URL. */
export function url(path: string): string {
	return import.meta.env.BASE_URL.replace(/\/?$/, '/') + path;
}

/** Where each name the library declares is documented: its module, and whether it has its own anchor. */
const declaredIn = new Map<string, string>();
for (const mod of modules) {
	for (const decl of declarations(mod)) {
		declaredIn.set(decl.name, mod.name);
		for (const sub of [...(decl.ctors ?? []), ...(decl.fields ?? []).filter((f) => f.isDirect)]) {
			declaredIn.set(sub.name, mod.name);
		}
		if (decl.ctor && !declaredIn.has(decl.ctor.name)) declaredIn.set(decl.ctor.name, mod.name);
	}
}

/** The link for a constant: its anchor in our docs, the Mathlib docs, or none. */
export function constUrl(name: string): string | undefined {
	const own = declaredIn.get(name);
	if (own) return url(modulePath(own)) + '#' + encodeURIComponent(name);
	const ext = data.external[name];
	if (ext) return MATHLIB_DOCS + ext.split('.').join('/') + '.html#' + encodeURIComponent(name);
	return undefined;
}

export function isDeclared(name: string): boolean {
	return declaredIn.has(name);
}

/** The link for an imported module, or none for library modules that aren't documented (the linters). */
export function importUrl(module: string): string | undefined {
	if (modules.some((m) => m.name === module)) return url(modulePath(module));
	if (module.split('.')[0] === library) return undefined;
	return MATHLIB_DOCS + module.split('.').join('/') + '.html';
}

export function sourceLink(mod: Module, info: { line: number; endLine: number }): string | undefined {
	return mod.sourceUrl && `${mod.sourceUrl}#L${info.line}-L${info.endLine}`;
}

/** The namespaces of `name`, innermost first, ending with the root namespace. */
export function namespaces(name: string): string[] {
	const parts = name.split('.');
	const result = [];
	for (let i = parts.length - 1; i >= 0; i--) result.push(parts.slice(0, i).join('.'));
	return result;
}

/** The front page's content: `docs/ROOT.md`. */
export function homePage(): string {
	return fs.readFileSync(HOME_PAGE, 'utf-8');
}

/** The title of a module: the first heading of its docstring. */
export function moduleTitle(mod: Module): string | undefined {
	return moduleDocs(mod)[0]?.doc.match(/^#\s+(.+)$/m)?.[1];
}

// Per-module notes: `A/B/NOTE.md` for module `A.B`, beside its source `A/B.lean`.

const NOTES_FILE = 'NOTE.md';

function notesFile(module: string): string {
	return path.join(REPO_ROOT, ...module.split('.'), NOTES_FILE);
}

export function notes(module: string): string | undefined {
	const file = notesFile(module);
	return fs.existsSync(file) ? fs.readFileSync(file, 'utf-8') : undefined;
}

/** Notes files that don't belong to any documented module, most likely misplaced. */
export function orphanNotes(): string[] {
	const expected = new Set(modules.map((m) => path.resolve(notesFile(m.name))));
	const libraryDirs = new Set(modules.map((m) => path.join(REPO_ROOT, m.name.split('.')[0])));
	return [...libraryDirs]
		.filter((dir) => fs.existsSync(dir))
		.flatMap((dir) =>
			(fs.readdirSync(dir, { recursive: true, encoding: 'utf-8' }) as string[])
				.filter((f) => path.basename(f) === NOTES_FILE)
				.map((f) => path.resolve(dir, f)),
		)
		.filter((f) => !expected.has(f))
		.map((f) => path.relative(REPO_ROOT, f));
}

const instances = modules.flatMap(declarations).filter((d) => d.kind === 'instance');

/** The library's instances of a class, or for a type. */
export function instancesFor(decl: Declaration): Declaration[] {
	if (decl.kind === 'class') return instances.filter((i) => i.className === decl.name);
	if (decl.kind === 'structure' || decl.kind === 'inductive') {
		return instances.filter((i) => i.typeNames?.includes(decl.name));
	}
	return [];
}

/** `name` without the namespace `ns`, if it's in it. */
export function relativeName(name: string, ns: string): string {
	return ns && name.startsWith(ns + '.') ? name.slice(ns.length + 1) : name;
}
