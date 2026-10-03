# Strict Dirichlet Pólya inequality: Lean formalization

This repository contains a single-file Lean formalization of the strict
Dirichlet Pólya inequality for bounded, nonempty, simply connected planar
domains, together with the accompanying manuscript.

## Mathematical statement and scope

The declaration `main` in `RequestProject/Main.lean` proves, for every
bounded open set `Omega : Set Complex` satisfying `SimplyConnectedSpace Omega`
and every natural number `j >= 1`,

```text
4 * pi * j < area(Omega) * lambda_j_var(Omega).
```

Here `lambda_j_var` denotes the quantity named `dirichletEigenvalue` in
the source. It is the infimum, over j-dimensional real subspaces of smooth
compactly supported test functions on Omega, of the supremum of the Dirichlet
Rayleigh quotient over their nonzero elements. The formal inequality is
expressed in `ENNReal`, the extended nonnegative real numbers.

The manuscript's section **Lean formalization** proves that these variational
values equal the eigenvalues of the form-defined Dirichlet Laplacian, including
multiplicities, without boundary regularity assumptions. It also proves the
equivalence with the spectral counting inequality. These identification and
counting arguments are mathematical proofs in the manuscript; they are not
additional theorems formalized in the Lean artifact.

The formalization was produced with the assistance of Aristotle.

## Files

| File | Purpose |
| --- | --- |
| `RequestProject/Main.lean` | Complete proof development; final theorem `main` |
| `lean-toolchain` | Pins Lean to `leanprover/lean4:v4.28.0` |
| `lakefile.toml` | Lean project and mathlib dependency configuration |
| `lake-manifest.json` | Exact dependency revisions |
| `paper/D_simply_connected_strict_v7.tex` | Manuscript with the spectral identification and formalization section |
| `verification/Audit.lean` | Prints the checked theorem's type and its axioms using the built module |
| `verification/local-build.txt` | Recorded output of the successful local Lean 4.28.0 build |
| `verification/SHA256SUMS` | SHA-256 checksum of the verified proof source |

The manuscript is supplied as LaTeX source. PDF compilation has not yet been
validated for this snapshot because the local built-in LaTeX compiler reported
a platform-directory error.

## Reproduce the Lean check

Install [Git](https://git-scm.com/) and
[elan](https://github.com/leanprover/elan), the Lean toolchain manager.
After cloning this repository, open a terminal in its root directory and run:

```text
elan toolchain install leanprover/lean4:v4.28.0
lake env lean --version
lake exe cache get
lake build +RequestProject.Main
lake env lean verification/Audit.lean
```

The version command should report **Lean 4.28.0**. The local `lean-toolchain`
file selects this version for the project; no change to the global default
toolchain is needed. `lake exe cache get` downloads precompiled dependency
artifacts. The proof file is large, and checking it can take many minutes.

The audit file imports the built proof module and prints the type of `main`
and its transitive axiom dependencies. The expected axiom report is:

```text
'main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are Lean's standard axioms for classical mathematics. There is no
`sorryAx` or additional axiom in this report. The proof source contains no
`sorry`, `admit`, or `native_decide` proof steps.

## Verified snapshot

- Local verification date: **2026-10-03**.
- Lean: **4.28.0**, compiler commit
  `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b`.
- mathlib revision: `8f9d9cff6bd728b17a24e163c9402775d9e6a365`,
  pinned in `lake-manifest.json`.
- The recorded build reports `Build completed successfully (8026 jobs)`,
  `No unused definitions`, and exactly the three axioms listed above.
- SHA-256 of `RequestProject/Main.lean`:

```text
eeb626df2c7cf25ce65cbd466f4eedc43b92a557421c3ebbabf8eeef481a97a5
```

The Lean source is retained byte-for-byte from the verified single-file
export. Downloaded dependencies and generated build artifacts are excluded
from version control. No independent external proof checker was run for this
snapshot.

## 中文说明

本项目固定使用 **Lean 4.28.0**。主要证明在 `RequestProject/Main.lean` 中，
最终定理名是 `main`。论文第七节说明它证明的变分形式为什么与论文主定理等价。

本地编译已成功，最终定理仅依赖 `propext`、`Classical.choice`、`Quot.sound`。
下载后在项目根目录执行上面的命令即可复核；`verification/Audit.lean` 用于
显示最终定理的类型和公理依赖。
