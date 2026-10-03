# Strict Dirichlet Pólya inequality: Lean formalization

This repository contains a single-file Lean proof of the strict Dirichlet
Pólya inequality for bounded, nonempty, simply connected planar domains,
together with the accompanying manuscript.

## Mathematical statement and scope

The declaration `main` in `RequestProject/Main.lean` proves, for every bounded
open `Omega : Set Complex` satisfying `SimplyConnectedSpace Omega` and every
natural number `j >= 1`,

```text
4 * pi * j < area(Omega) * lambda_j(Omega).
```

Here `lambda_j` is `DirichletBridge.spectralDirichletEigenvalue`: the positive
eigenvalues, in nondecreasing order and with multiplicity, of the actual
Dirichlet operator. They are defined independently of the smooth-core min–max,
using finite orthonormal eigenfamilies of its compact inverse. `main_counting`
proves the inclusive counting inequality `N_Omega(E) < area(Omega) * E / (4*pi)`
for every real `E > 0`.

The original Aristotle variational theorem is retained as
`strict_polya_variational`. The added bridge, developed with Codex, proves:

- The real and complex `H_0^1` domains are completions of the actual smooth
  compactly supported cores, with the usual value and weak gradients.
- The closed form is the gradient energy integral on `Omega`; the associated
  real and complex Dirichlet operators are self-adjoint, with compact inverse.
- The original smooth-core min–max equals the independently defined ordered
  operator eigenvalues. These tend to infinity and exhaust the positive
  eigenvalues; occurrence counts equal real and complex eigenspace dimensions.
- The spectral counting and indexed inequalities are equivalent, with the
  endpoint included and repeated eigenvalues counted with multiplicity.

These results are proved in Lean without boundary regularity assumptions.
The manuscript's **Lean formalization** section describes their correspondence
with the paper's main theorem. The development uses finite spectral families;
it does not provide a separate infinite eigenbasis expansion theorem or a
theorem about the full operator `spectrum` set.

## Files

| File | Purpose |
| --- | --- |
| `RequestProject/Main.lean` | Single proof source; final theorems `main` and `main_counting` |
| `lean-toolchain` | Pins Lean to `leanprover/lean4:v4.28.0` |
| `lakefile.toml` | Lean project and mathlib dependency configuration |
| `lake-manifest.json` | Exact dependency revisions |
| `paper/D_simply_connected_strict_v7.tex` | Manuscript and formalization section |
| `paper/D_simply_connected_strict_v7.pdf` | Compiled manuscript PDF |
| `verification/Audit.lean` | Checks the public statements and bridge axiom dependencies |
| `verification/local-build.txt` | Successful local Lean 4.28.0 build output |
| `verification/SHA256SUMS` | SHA-256 checksum of the verified proof source |

Both the LaTeX source and compiled PDF are supplied in `paper/`. To rebuild
the PDF, run from that directory (the recorded build uses TeX Live 2022):

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error D_simply_connected_strict_v7.tex
```

## Reproduce the Lean check

Install [Git](https://git-scm.com/) and
[elan](https://github.com/leanprover/elan). After cloning the repository, run
these commands in its root directory:

```text
elan toolchain install leanprover/lean4:v4.28.0
lake env lean --version
lake exe cache get
lake build +RequestProject.Main
lake env lean verification/Audit.lean
```

The version command should report **Lean 4.28.0**. `lean-toolchain` selects this
version for the project. `lake exe cache get` downloads precompiled dependency
artifacts. The single proof source is large and can take many minutes to check.

The audit reports only Lean's three standard axioms for classical mathematics:

```text
[propext, Classical.choice, Quot.sound]
```

This is checked for both final inequalities and for the semantic bridge
theorems, including the complex form, its smooth core, and operator
representation. None of these results depends on `sorryAx` or an additional
axiom. The source contains no `sorry`, `admit`, or `native_decide` proof steps.

## Verified snapshot

- Local verification date: **2026-10-03**.
- Lean: **4.28.0**, compiler commit `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b`.
- mathlib revision: `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
- The merged single source passed `lake build +RequestProject.Main`; see
  `verification/local-build.txt` for the recorded output.
- SHA-256 of `RequestProject/Main.lean`:

```text
c8cda85243508e881a38b7241b422938e7b221b56035285b348a61ba466d4a53
```

Downloaded dependencies and generated build artifacts are excluded from
version control. Verification uses the pinned Lean compiler and kernel;
no independent implementation of Lean's kernel checked this snapshot.

## 中文说明

本项目固定使用 **Lean 4.28.0**。`RequestProject/Main.lean` 是单文件证明。
原变分结论保留为 `strict_polya_variational`；新增的 `main` 证明实际 Dirichlet
特征值的严格不等式，`main_counting` 证明包含端点、计入重数的谱计数不等式。

光滑核心、闭形式、实际算子、谱值识别及实复重数的桥接均已有 Lean 证明。
论文第七节和 PDF 已同步。最终定理及关键桥接定理仅依赖标准三项公理。
执行上面的构建及审计命令即可复核。
