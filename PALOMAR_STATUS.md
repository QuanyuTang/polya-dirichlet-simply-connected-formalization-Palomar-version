# Palomar registration status

This repository contains the public Palomar-compatible source of the strict
Dirichlet Pólya formalization. The exact source snapshot registered by Palomar
is commit `ba3690bfd48618cf48da07fa4555382bd9852ff3` as
`PALOMAR-2026-10-09-000003 v1`.

Authors and responsible maintainers: Quanyu Tang and Zuoqin Wang.

The accompanying manuscript has been submitted to arXiv under submission
number 8203840. The public e-print link will be added once arXiv assigns the
final identifier.

The substantive Lean source was ported from the earlier Dirichlet repository
commit 0c42251e2b602c9b49db6f2c37a9d27c858d1475. The accompanying manuscript
is maintained separately from this Lean repository. The Palomar Challenge/Solution pair advertises
PalomarDirichlet.main_result, the variational theorem corresponding to
strict_polya_variational. The stronger operator-spectral declarations
main and main_counting remain in RequestProject/MainSpectral.lean and
are re-exported by RequestProject/Main.lean; they are proved and audited but
are not selected by the current Comparator configuration.

The repository uses Lean 4.35.0-rc2 and a pinned Mathlib manifest. The latest
local Palomar-style checks validate the metadata and Apache-2.0 license, all
module and source-size requirements, source checksums, and the Comparator.
The Comparator accepts the Solution with the Lean, NanoDa, and con-ron kernels.
The ordinary Lean workflow also builds the source and checks the public
statements and their axiom dependencies.

Challenge.lean contains one deliberate sorry in the statement declaration,
as permitted by Palomar's Challenge/Solution design. The substantive proof
source under RequestProject/ and Solution.lean contain no sorry, admit, or
native_decide; the audited declarations use only propext, Classical.choice,
and Quot.sound.

The root license is Apache-2.0. The repository includes the reproducible Lean
configuration, verification scripts, and Palomar metadata. Palomar mechanical
verification and automated editorial review have been completed for the
registered public commit; the registry record reports no blocking problems.
