# Strict Dirichlet Pólya inequality: Lean formalization

This repository contains a modular Lean proof of the strict Dirichlet
Pólya inequality for bounded, nonempty, simply connected planar domains.
`RequestProject/Main.lean` is the aggregate entry point for the three proof modules,
together with the accompanying manuscript.

[Lean source](RequestProject/Main.lean) ·
[Paper PDF](paper/D_simply_connected_strict_v7.pdf) ·
[Paper source](paper/D_simply_connected_strict_v7.tex) ·
[Automatic verification](https://github.com/QuanyuTang/polya-dirichlet-simply-connected-formalization-Palomar-version/actions/workflows/lean.yml)

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
| `RequestProject/Main.lean` | Aggregate entry point; final theorems `main` and `main_counting` |
| `RequestProject/MainBase.lean` | First proof module (under 10,000 lines) |
| `RequestProject/MainMiddle.lean` | Second proof module (under 10,000 lines) |
| `RequestProject/MainSpectral.lean` | Spectral bridge and final theorems (under 10,000 lines) |
| `lean-toolchain` | Pins Lean to `leanprover/lean4:v4.35.0-rc2` |
| `lakefile.toml` | Lean project and mathlib dependency configuration |
| `lake-manifest.json` | Exact dependency revisions |
| `paper/D_simply_connected_strict_v7.tex` | Manuscript and formalization section |
| `paper/D_simply_connected_strict_v7.pdf` | Compiled manuscript PDF |
| `verification/Audit.lean` | Checks public statements and enforces 16 axiom audits |
| `verification/local-build.txt` | Historical pre-Palomar Lean 4.28.0 build record; rerun for the current rc2 snapshot |
| `verification/SHA256SUMS` | SHA-256 checksum of the verified proof source |
| `.github/workflows/lean.yml` | Rebuilds and audits the pinned proof on GitHub Actions |

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
elan toolchain install leanprover/lean4:v4.35.0-rc2
lake env lean --version
lake exe cache get
lake build +RequestProject.Main
lake env lean verification/Audit.lean
```

The version command should report **Lean 4.35.0-rc2**. `lean-toolchain` selects this
version for the project. `lake exe cache get` downloads precompiled dependency
artifacts. The single proof source is large and can take many minutes to check.

The `#print axioms` commands at the end of `Main.lean` report only Lean's
three standard axioms for classical mathematics:

```text
[propext, Classical.choice, Quot.sound]
```

`verification/Audit.lean` enforces these exact dependencies with 16
`#guard_msgs` assertions. Successful guards are silent; an unexpected axiom
list makes the audit fail. It also prints the types of the final theorems
and the principal identification theorems for inspection.

The checks cover both final inequalities and the semantic bridge, including
the complex energy integral, the genuine smooth core, operator representation,
multiplicities, divergence of the eigenvalues, and finite spectral counting.
None of these results depends on `sorryAx` or an additional axiom. The proof
source contains no `sorry`, `admit`, or `native_decide` proof steps.

## Automatic verification

The [Lean verification workflow](.github/workflows/lean.yml) runs on pushes
and pull requests to `main`, and can also be started manually from GitHub's
Actions tab. It uses the official [Lean action](https://github.com/leanprover/lean-action)
with the toolchain and dependency revisions committed to this repository.

Each run checks the source checksum, downloads the mathlib dependency cache,
compiles `RequestProject.Main` on a fresh Ubuntu runner, and runs the guarded
audit. Build warnings cause failure. The workflow also checks that verification
has not changed tracked files. The action versions are pinned to commit hashes.
After changing the proof source, rebuild and audit it before updating
`verification/SHA256SUMS` and the verified snapshot below.

## Palomar build snapshot

The Palomar release pin is Lean 4.35.0-rc2 with the matching Mathlib revision recorded in lake-manifest.json. The original 4.28.0 source snapshot was checked before this preparation work. A fresh Palomar-toolchain build and Comparator run are required for this release snapshot.

## 中文说明

本项目固定使用 **Lean 4.35.0-rc2**。`RequestProject/Main.lean` 是聚合入口，实际证明分为 `MainBase.lean`、`MainMiddle.lean` 和 `MainSpectral.lean` 三个模块。
原变分结论保留为 `strict_polya_variational`；新增的 `main` 证明实际 Dirichlet
特征值的严格不等式，`main_counting` 证明包含端点、计入重数的谱计数不等式。

光滑核心、闭形式、实际算子、谱值识别及实复重数的桥接均已有 Lean 证明。
论文第七节和 PDF 已同步。最终定理及关键桥接定理仅依赖标准三项公理。
执行上面的构建及审计命令即可复核。审计文件包含 16 项断言，成功时不会
逐项打印公理列表；出现意外依赖会直接报错。GitHub Actions 自动执行源码
校验、固定版本构建及上述审计，结果可从仓库的 Actions 页面查看。

## Palomar preparation

This repository is a private preparation snapshot for a future Palomar Registry
submission. The authors and responsible maintainers are Quanyu Tang and Zuoqin
Wang. `formalization.yaml`, `CITATION.cff`, `LICENSE`, and `PALOMAR_STATUS.md`
record the intended provenance and submission status.

The Palomar-compatible statement/proof split is now present in
`Challenge.lean`, `Solution.lean`, and `comparator.json`. The selected
Comparator declaration is `PalomarDirichlet.main_result`, which states the
strict variational inequality proved by `strict_polya_variational`. The stronger
operator-spectral declarations `main` and `main_counting` remain in the source
development but are deliberately not advertised by this configuration, because
their statement-side spectral operator definitions are substantially larger than
Palomar's small Challenge surface. The project still needs a Palomar-supported
Lean toolchain and a successful clean Comparator run before submission. Palomar
submissions must use a public GitHub commit, so this preparation repository
remains private until the authors choose the release snapshot.
