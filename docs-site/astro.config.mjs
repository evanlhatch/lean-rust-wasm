import { defineConfig } from 'astro/config';
import starlight from '@astrojs/starlight';

export default defineConfig({
  site: 'https://evanlhatch.github.io/lean-rust-wasm',
  integrations: [
    starlight({
      title: 'guestlang — the Lean-spec\'d wasm template',
      description:
        'Write the spec in Lean, get a proved, byte-tied WASM component: schema-lang → WIT → wasip3, with a differential duel against Lean\'s own evals.',
      social: [
        { icon: 'github', label: 'GitHub', href: 'https://github.com/evanlhatch/lean-rust-wasm' },
      ],
      sidebar: [
        {
          label: 'Guides',
          items: [
            { slug: 'guides/getting-started' },
          ],
        },
        {
          label: 'API',
          items: [
            { slug: 'api' },
          ],
        },
      ],
      editLink: {
        baseUrl: 'https://github.com/evanlhatch/lean-rust-wasm/edit/main/docs-site/',
      },
      lastUpdated: true,
      pagination: true,
    }),
  ],
});
