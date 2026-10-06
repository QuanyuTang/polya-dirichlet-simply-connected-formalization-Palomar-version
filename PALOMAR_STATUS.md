# Palomar preparation status

This repository is a preparation snapshot for a future Palomar Registry submission.
It preserves the checked final formalization and records the authorship and provenance
needed for the later submission.

Authors and responsible maintainers: **Quanyu Tang** and **Zuoqin Wang**.

The source was copied from the final Dirichlet repository commit `0c42251e2b602c9b49db6f2c37a9d27c858d1475`. The mathematical source is the paper in `paper/`. The Palomar statement/proof pair advertises
`PalomarDirichlet.main_result`, the variational theorem corresponding to
`strict_polya_variational`; the stronger operator-spectral theorem is the
`main` declaration in `RequestProject/MainSpectral.lean` (re-exported by `RequestProject/Main.lean`). The source formalization was
checked locally and by the original GitHub workflow before this preparation copy
was made.

This repository is not yet a Palomar submission. The current development uses
Lean 4.35.0-rc2 and a large legacy modular source tree. The Palomar files are
present, but a submission still requires a supported pinned toolchain, a clean
Comparator run, and an explicit review of the fact that the selected result is
the variational theorem rather than the stronger operator-spectral `main`.

The root Apache-2.0 license is included because Palomar requires a root license.
The current repository is private until the authors decide to make the exact
submission snapshot public.

