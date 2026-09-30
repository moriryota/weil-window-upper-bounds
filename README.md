# Unconditional upper bounds for the bottom of windowed Weil quadratic forms

This repository contains the code, the Lean 4 formalization and the paper for:

> R. Mori, *Unconditional doubly exponential upper bounds for the bottom of windowed Weil quadratic forms* (2026).

- Paper (Zenodo): [doi:10.5281/zenodo.23059298](https://doi.org/10.5281/zenodo.23059298)
- Code and Lean formalization (Zenodo, all versions): [doi:10.5281/zenodo.23059099](https://doi.org/10.5281/zenodo.23059099)

## Results

Let `λ_min(λ)` be the bottom of the spectrum of Weil's quadratic form restricted to test functions supported in the window `[λ⁻¹, λ]`, and put `μ = λ²`.

The Riemann Hypothesis is equivalent to `λ_min(λ) ≥ 0` for all `λ`. The results below are **upper bounds**. They hold without any hypothesis on the zeros of ζ, and they do **not** address the Riemann Hypothesis.

- **Theorem A.** For every `μ ≥ 5`, `λ_min(λ) ≤ 1.563·10⁹ · μ⁸ · e^{−2πμ}`.
  - The constant is proved on paper, with ball arithmetic.
  - Theorem A with existential constants is formalized in Lean 4 (see below).
- **Theorem B.** For every `μ ≥ 5`, `λ_min(λ) ≤ 1.362·10⁹ · μ²³ · e^{−4πμ}`. The proof uses Kaiser–Bessel windows, and the constants are established with ball arithmetic. For `μ ≥ 5` this bound is stronger than Theorem A. It is a paper proof and is not formalized.
- **Numerical observation.** Connes–Consani–Moscovici (arXiv:2511.22755, Fig. 4) and Connes (arXiv:2602.04022, Fig. 1) observed that `λ_min` tracks the prolate quantity `1 − χ₂(λ) ≍ μ^{9/2} e^{−4πμ}`. We extend this comparison to the certified numerical upper bounds of Zhu (arXiv:2608.24827): divided by `1 − χ₂`, they stay between 3 and 20 over 283 orders of magnitude.

## Lean formalization (`lean/`)

Main declaration: `RhWeil.Concrete.theoremA` in `lean/RhWeil/TheoremAFinal.lean`.

```lean
theorem RhWeil.Concrete.theoremA : ∃ C p lam₀ : ℝ, ∀ lam ≥ lam₀, ∃ k : ℝ → ℂ,
    TheoremA.WindowTest lam k ∧ 0 < TheoremA.l2sq k ∧
    ‖literatureRHS (weilTest k k)‖ ≤ C * lam ^ p * Real.exp (-2 * Real.pi * lam ^ 2) * TheoremA.l2sq k
```

What the statement means:
- `WindowTest lam k` says that `k` is `C²` with `tsupport k ⊆ [−log λ, log λ]`.
- `literatureRHS (weilTest k k)` is the geometric side of Weil's explicit formula (Iwaniec–Kowalski, Thm 5.12) for `k ⋆ k̃`, i.e. the Weil quadratic form `QW(k, k)`, as defined in Zeta23.
- The spectral statement about `λ_min` follows by the Rayleigh principle (Connes–Consani–Moscovici, Thm 3.6). That step is not formalized.

Build (Lean `v4.33.0-rc2`, Mathlib `51e6992e`, Zeta23 at formal-math commit `3635e748`):

```
cd lean
lake exe cache get      # prebuilt Mathlib
lake build RhWeil
```

`#print axioms RhWeil.Concrete.theoremA` reports only `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry`.

## Numerics (`python/`, `outputs/`)

Requirements: Python 3.12, with `pip install -r python/requirements.txt`. Run the scripts from the repository root, e.g. `python python/theoremA_closed_form_rigorous.py`. The outputs used in the paper are in `outputs/`.

| Script | Content |
|---|---|
| `theoremA_explicit.py` | Explicit bound `B(λ)`. Direction check against `A₀ + A₁` computed from the definitions. |
| `theoremA_c0.py` | Rigorous lower bound `‖k‖² ≥ 0.00894`, in ball arithmetic. |
| `theoremA_closed_form_rigorous.py` | `B e^{πμ}/μ⁴ ≤ 12298` for all `μ ≥ 5`, giving the constant `1.563·10⁹`. |
| `smooth_A_check.py`, `identity_checks.py` | Numerical checks of the identities and inequalities used in the proof of Theorem A. |
| `check_B2_B5.py`, `check_bessel_bounds.py`, `check_decay.py`, `kb_kvector.py` | Checks for Theorem B. |
| `theoremB_explicit.py` | Explicit constants of Theorem B for all `μ ≥ 5` (ball arithmetic), with direction checks against the true functions. |
| `check_B3_structure.py`, `check_B3_powers.py` | Powers `λ¹⁸` and `λ²²` in Lemma 5.3 (symbolic and numerical), and the band-edge lower bounds of Remark 5.4. |
| `weil_spectral.py`, `prolate_kvector.py`, `prolate_runs.py` | Legendre–Galerkin discretization of the Weil form, and `λ_min` versus the prolate vector. |

`docs/VERIFICATION.md` summarizes, for each step of the proofs, how it was checked.

## Use of generative AI

This work was carried out with extensive use of generative AI systems (Anthropic Claude, Google Gemini, OpenAI GPT), under the direction of the author. The AI systems drafted the proofs, the Lean development and the paper, ran the computations, and reviewed one another's work. The author takes full responsibility for the content.

The formal result is checked by the Lean kernel. Theorem B and the paper have not yet been reviewed by independent human experts.

## Versions

- **v1.1.0** (paper version 3): Theorem B with explicit constants for all `μ ≥ 5` (new Lemmas 5.5–5.8; domination constant 1 instead of 36.14; lower bound for `‖k_B‖` without limits). Citation of Connes–Consani–Moscovici (3.27) for the monotonicity of `λ_min`. The Lean development is unchanged.
- **v1.0.1** ([doi:10.5281/zenodo.23061318](https://doi.org/10.5281/zenodo.23061318); paper version 2): full proofs in the paper; corrected power in Lemma 5.3 (`λ²²` instead of `λ²⁰` for `ξφ̂_B′`, hence `p = 46` instead of 42); band-edge lower bounds; credit to the prior observations of Connes–Consani–Moscovici and Connes; definition of `χ₂`; notes on the convergence of the Galerkin computations. The Lean development is unchanged.
- **v1.0.0**: initial release ([doi:10.5281/zenodo.23059100](https://doi.org/10.5281/zenodo.23059100)).

## License

- Code (`lean/`, `python/`): Apache License 2.0 (see `LICENSE` and `NOTICE`).
- Paper (`paper/`): CC BY 4.0.
