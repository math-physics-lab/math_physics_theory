// The search index: every declaration (with its constructors and fields) and module.
import { declarations, modulePath, modules } from '../lib/docs';

export function GET() {
	const entries = modules.flatMap((mod) => [
		{ name: mod.name, kind: 'module', module: mod.name, path: modulePath(mod.name) },
		...declarations(mod).flatMap((d) =>
			[d, ...(d.ctors ?? []), ...(d.fields ?? []).filter((f) => f.isDirect)].map((x) => ({
				name: x.name,
				kind: x === d ? d.kindDescription : d.ctors?.includes(x) ? 'constructor' : 'field',
				module: mod.name,
				path: modulePath(mod.name) + '#' + encodeURIComponent(x.name),
			})),
		),
	]);
	return new Response(JSON.stringify(entries), { headers: { 'Content-Type': 'application/json' } });
}
