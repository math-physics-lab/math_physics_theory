// Renders docstrings and notes: Markdown with LaTeX math, highlighted Lean code and links to
// declarations named in inline code.

import { unified, type MarkdownRenderer } from '@astrojs/markdown-remark';
import rehypeKatex from 'rehype-katex';
import remarkMath from 'remark-math';
import { constUrl, namespaces } from './docs';

interface Node {
	type: string;
	tagName?: string;
	lang?: string | null;
	value?: string;
	properties?: Record<string, unknown>;
	children?: Node[];
}

interface Options {
	/** Namespaces that names in inline code are resolved in, innermost first. */
	scopes: string[];
	/** How many levels to demote headings by, so they sit below the page's own headings. */
	headingShift: number;
}

function options(file: { data: { astro?: { frontmatter?: Record<string, any> } } }): Options {
	return file.data.astro?.frontmatter as Options;
}

/** Code blocks in Lean docstrings are Lean unless they say otherwise. */
function remarkDefaultLean() {
	return (tree: Node) => {
		const visit = (node: Node) => {
			if (node.type === 'code' && !node.lang) node.lang = 'lean';
			node.children?.forEach(visit);
		};
		visit(tree);
	};
}

/**
 * `$$…$$` is display math in Lean docstrings, even within a paragraph, where remark-math would
 * render it inline.
 */
function remarkDisplayMath() {
	return (tree: Node & { position?: any }, file: any) => {
		const source = String(file.value);
		const visit = (node: Node & { position?: any; data?: any }) => {
			if (node.type === 'inlineMath' && source.startsWith('$$', node.position?.start?.offset)) {
				node.data = { ...node.data, hProperties: { className: ['language-math', 'math-display'] } };
			}
			node.children?.forEach(visit);
		};
		visit(tree);
	};
}

function text(node: Node): string {
	return node.type === 'text' ? (node.value ?? '') : (node.children ?? []).map(text).join('');
}

/** Links inline code that names a declaration, like doc-gen4 does: `` `operator` `` in its namespace. */
function rehypeLinkNames() {
	return (tree: Node, file: any) => {
		const { scopes } = options(file);
		const visit = (node: Node, inLinkOrPre: boolean) => {
			node.children = node.children?.map((child) => {
				if (child.type !== 'element') return child;
				if (child.tagName === 'code' && !inLinkOrPre) {
					const name = text(child);
					if (/^[^\s()\[\]{}:,]+$/.test(name)) {
						for (const scope of scopes) {
							const href = constUrl(scope ? `${scope}.${name}` : name);
							if (href) return { type: 'element', tagName: 'a', properties: { href }, children: [child] };
						}
					}
				}
				visit(child, inLinkOrPre || child.tagName === 'a' || child.tagName === 'pre');
				return child;
			});
		};
		visit(tree, false);
	};
}

function rehypeShiftHeadings() {
	return (tree: Node, file: any) => {
		const { headingShift } = options(file);
		const visit = (node: Node) => {
			const level = node.tagName?.match(/^h([1-6])$/)?.[1];
			if (level) node.tagName = `h${Math.min(6, Number(level) + headingShift)}`;
			node.children?.forEach(visit);
		};
		visit(tree);
	};
}

let renderer: Promise<MarkdownRenderer> | undefined;

/**
 * Renders `markdown` to HTML. Names in inline code are resolved in the namespaces of `scope`
 * (a declaration or module name), and headings are demoted by `headingShift` levels.
 */
export async function renderMarkdown(markdown: string, scope: string, headingShift: number): Promise<string> {
	renderer ??= unified({
		remarkPlugins: [remarkMath, remarkDisplayMath, remarkDefaultLean],
		rehypePlugins: [rehypeKatex, rehypeLinkNames, rehypeShiftHeadings],
	}).createRenderer({});
	const frontmatter: Options = { scopes: [scope, ...namespaces(scope)], headingShift };
	return (await (await renderer).render(markdown, { frontmatter })).code;
}
