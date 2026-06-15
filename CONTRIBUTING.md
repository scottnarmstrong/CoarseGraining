# Contributing / Building notes

This repository is primarily a finished artifact rather than an actively
solicited collaborative project, but issues and pull requests are welcome.

## Building locally

```bash
lake exe cache get   # prebuilt mathlib oleans
lake build           # build the project
```

A few practical notes for working with a development of this size:

- **Never run `lake clean`.** It wipes the `mathlib` oleans and forces a
  multi-hour rebuild from source. To force a project-only rebuild, remove the
  project build artifacts under `.lake/build/lib/lean/Homogenization` (and the
  corresponding `.lake/build/ir/Homogenization`) and re-run `lake build`.

- **Per-file rebuilds.** Lake invalidates by content hash, not mtime, so
  `touch` does not trigger a rebuild. To force one file, delete its
  `.olean`/`.ilean` under `.lake/build/lib/lean/Homogenization/<path>` and its
  `.c`/`.o` under `.lake/build/ir/Homogenization/<path>`, then
  `lake build Homogenization.<Module>`.

- **Profiling a slow file:**

  ```bash
  lake env lean --profile Homogenization/<...>/YourFile.lean 2>&1 | tail -25
  ```

- **No `sorry`, no custom `axiom`.** Please keep it that way: the development is
  axiom-clean (see [`Homogenization/Meta/AxiomsAudit.lean`](Homogenization/Meta/AxiomsAudit.lean)),
  and CI checks the build.
