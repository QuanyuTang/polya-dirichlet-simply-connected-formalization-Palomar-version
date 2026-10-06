# Palomar preparation status

This repository is a preparation snapshot for a future Palomar Registry submission.
It preserves the checked final formalization and records the authorship and provenance
needed for the later submission.

Authors and responsible maintainers: **Quanyu Tang** and **Zuoqin Wang**.

The source was copied from the final Dirichlet repository commit `0c42251e2b602c9b49db6f2c37a9d27c858d1475`. The mathematical source is the paper in `paper/`, and the formal theorem is the
`main` declaration in `RequestProject/Main.lean`. The source formalization was
checked locally and by the original GitHub workflow before this preparation copy
was made.

This repository is not yet a Palomar submission. The current development uses
Lean 4.28.0 and a large legacy modular source tree. A submission will require a
public GitHub snapshot, a Palomar-compatible `Challenge.lean`/`Solution.lean`
pair, `comparator.json`, and a pinned toolchain supported by Palomar. The
Palomar-specific statement surface must be audited separately before making this
repository public or submitting it.

The root Apache-2.0 license is included because Palomar requires a root license.
The current repository is private until the authors decide to make the exact
submission snapshot public.

