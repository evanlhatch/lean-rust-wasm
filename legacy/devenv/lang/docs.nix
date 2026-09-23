# Docs site (Astro Starlight) — OPT-IN via profile (extends js for bun):
# devenv --profile docs
#
# Scaffolding from flatland's docs-site (astro ^5.7 + @astrojs/starlight
# ^0.34 + mdx). Content lives in docs-site/src/content/docs/; build
# output docs-site/dist/ is deployable to Cloudflare Pages as its own
# Pages project (cloudflare profile).
{ lib, ... }:
{
  env.DOCS_DIR = "docs-site";
}
