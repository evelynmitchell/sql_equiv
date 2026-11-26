# API documentation

The API documentation of `SqlEquiv`, `SqlCore` and `SqlBridge` is generated with
[doc-gen4](https://github.com/leanprover/doc-gen4) and published to GitHub Pages:
<https://evelynmitchell.github.io/sql_equiv/>.

## How it is built

`docbuild/` is a nested Lake project, as doc-gen4 recommends, so that doc-gen4 and its
dependencies stay out of the main project's manifest:

- `docbuild/lakefile.toml` requires doc-gen4 and this package (`path = "../"`), and shares the
  main project's `.lake/packages`. doc-gen4's only dependency in common with ours, `Cli`, is at
  the same revision.
- doc-gen4 is pinned to the release for our toolchain (`v4.36.0-rc2`). When `lean-toolchain`
  moves, move the pin in `docbuild/lakefile.toml` to the matching tag and copy the new
  `lean-toolchain` into `docbuild/`, then run `lake update doc-gen4` there (below).
- `docbuild/mkroot.sh` writes `docbuild/SqlEquivDocs.lean`, the root the docs are built from.
  It imports `SqlEquiv`, `SqlCore` and every `SqlBridge` module, because `SqlBridge` has no root
  module of its own (it is declared by globs). Modules that define a top-level `main`, the
  executables' entry points, are left out, because two would clash. The file is generated, so a
  new bridge module is documented without editing anything; it is gitignored.
- doc-gen4 documents everything the root imports, including the Lean core, Batteries and the
  Mathlib modules our libraries use: about 324 MB of pages.

## Building locally

```bash
cd docbuild
```

```bash
./mkroot.sh && lake build SqlEquivDocs:docs
```

The site is written to `docbuild/.lake/build/doc`. It has to be served over HTTP, as the
browser's same-origin policy breaks some pages opened as files:

```bash
cd docbuild/.lake/build/doc && python3 -m http.server
```

The first build compiles doc-gen4 and documents the Lean core and the imported Mathlib modules
(about 12 minutes here); later builds redo only what changed.

To move doc-gen4 to a new pin (if the project depends on Mathlib, as this one does, doc-gen4 asks
for `MATHLIB_NO_CACHE_ON_UPDATE=1`):

```bash
cd docbuild && MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4
```

## Publishing

`.github/workflows/docs.yml` builds the site and deploys it to GitHub Pages on every push to
`master` that changes Lean sources, the Lake files or `docbuild/`, and on demand
(`workflow_dispatch`). It needs the repository's Pages source set to **GitHub Actions**
(Settings > Pages > Build and deployment > Source), once.

- The build job installs elan, restores its own Actions cache (the Lake packages with doc-gen4,
  and the generated pages), fetches the prebuilt Mathlib (`lake exe cache get`), and builds
  `SqlEquivDocs:docs`.
- The deploy job uploads `docbuild/.lake/build/doc` as the Pages artifact and deploys it. Only
  it holds the `pages: write` and `id-token: write` permissions.
- Deployments do not overlap (`concurrency: pages`); a newer push waits for the one in progress.
