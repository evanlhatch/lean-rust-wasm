import { defineConfig } from 'astro/config';
import starlight from '@astrojs/starlight';

export default defineConfig({
  integrations: [
    starlight({
      title: 'lean-rust-wasm',
      sidebar: [
        { label: 'Start', slug: 'start' },
      ],
    }),
  ],
});
