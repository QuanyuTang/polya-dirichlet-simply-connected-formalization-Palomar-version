# Palomar preparation status

This repository contains a checked Palomar-compatible snapshot of the strict
Dirichlet Pólya formalization. Its GitHub visibility is intentionally private
during this preparation phase; publication of a final commit is the only
remaining visibility gate.

Authors and responsible maintainers: Quanyu Tang and Zuoqin Wang.

The substantive Lean source was ported from the earlier Dirichlet repository
commit 0c42251e2b602c9b49db6f2c37a9d27c858d1475. The mathematical source is
the paper in paper/. The Palomar Challenge/Solution pair advertises
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

The root license is Apache-2.0. The repository includes the manuscript TeX and
compiled PDF, the reproducible Lean configuration, verification scripts, and
the Palomar metadata. Official Palomar verification and editorial review have
not yet been run; they must be performed on the eventual public commit.

