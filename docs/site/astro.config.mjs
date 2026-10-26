// @ts-check
import { defineConfig } from 'astro/config';

// GitHub Pages serves the site from a subpath; CI sets these from `actions/configure-pages`.
export default defineConfig({
	site: process.env.DOCS_SITE || undefined,
	base: process.env.DOCS_BASE || '/',
	trailingSlash: 'always',
	build: { format: 'directory' },
});
