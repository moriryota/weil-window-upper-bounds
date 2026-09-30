# Verification summary

This document records how each step of the proofs was checked. The numbering follows the paper.

- Section 3 is the master proposition: Lemmas 3.2, 3.3, 3.4, 3.6 and Propositions 3.5, 3.7.
- Section 4 is Theorem A. Section 5 is Theorem B.

## Kinds of checks

| Code | Meaning |
|---|---|
| **P** | Written proof with all constants explicit. |
| **I** | Numerical check of an identity at explicit points, at 15–40 digits. |
| **N** | Numerical check of an inequality, comparing both sides for the same function. |
| **R** | Independent adversarial review by an AI system, with its findings checked by reproduction. |
| **S** | Symbolic computation (sympy). |
| **B** | Ball arithmetic (Arb), including rigorous integration. |
| **L** | Lean 4 formalization, checked by the Lean kernel; `#print axioms` shows only the standard axioms. |

## Theorem A

| Step | Checks | Details |
|---|---|---|
| Explicit formula for piecewise C¹ functions (Lemma 3.2) | P, R, L* | *In Lean the window cut-off is smooth, so the C² explicit formula of Zeta23 applies directly. Its definitions were audited, and the geometric side, the zero side (1000 zeros) and a Galerkin discretization agree to about 10⁻¹² for a test function (`outputs/`, audit). |
| Poisson form of `e` and decay (Lemma 3.3) | P, I, R, L | The identity was checked at 4 points to 15 digits (`identity_checks.out`). |
| Radical lemma `ê(±γ_ρ) = 0` (Lemma 3.4) | P, I, R, L | `ê(z) = ζ(½+iz)Φ(z)` was checked to 12 digits at 3 points. At `z = γ₁` both sides vanish. The Lean proof uses the Mellin transform and the identity theorem, and assumes nothing about where the zeros lie. |
| Zero-side estimate (Proposition 3.5) | P, I, N, R, L | `W(k) = 2Σ\|r̂(t_n)\|²` agrees with the spectral value to 1%. The bound `2S(A₀+A₁)²` exceeds `\|W(k)\|` by a factor 357–3397 for μ = 5–13 (`smooth_A_check.out`). The value of `S` was checked with 600 zeros plus the tail. |
| Explicit tails `B(λ)` (§4.2, (4.3)–(4.4)) | P, N, R | `B` exceeds `A₀+A₁` computed from the definitions by a factor 80–140. The polynomial coefficients were independently re-derived with sympy. |
| `‖k‖² ≥ 0.00894` (Lemma 4.2) | P, ball arithmetic, R, L* | *In Lean, a different argument gives an existential constant. |
| Closed form `1.563·10⁹` | P, ball arithmetic | 48,882 Arb intervals cover 5 ≤ μ ≤ 10⁴. Beyond that, a Laurent polynomial with nonnegative coefficients gives a monotone bound (`closed_form_rigorous.out`). |
| Main statement (existential constants) | L | `RhWeil.Concrete.theoremA`. |

## Theorem B

| Step | Checks | Details |
|---|---|---|
| Sonine–Gegenbauer integral (Lemma 5.1) | P, I, R | Checked at 18 points to relative error ≤ 3·10⁻¹⁷. |
| Bessel bounds (Lemma 5.2: `\|J\| ≤ 1`, two-sided bounds for `I_ν`) | P, N, R | Checked for ν = 2, 2.5 and 3 on z ≤ 2000 (`check_B2_B5.out`). A uniform bound `√(2/π) w^{−1/2}`, proposed during review, was found false for α ≥ 2.5 and is not used (`check_bessel_bounds.out`). |
| Decay exponents 5/2 and 3/2 (Lemma 5.3) | P, N, R | The true decay rates ξ⁻³ and ξ⁻² were checked up to ξ = 1280λ (`check_decay.out`). |
| Powers `λ¹⁸` (for `φ̂_B`) and `λ²²` (for `ξφ̂_B′`) beyond the band edge (Lemma 5.3) | P, S, N, R | The derivative structure and the powers were checked symbolically (`check_B3_structure.out`). The quotients by `λ¹⁸` and `λ²²` stay in 5.67–5.80 and 13.8–15.2 for μ = 5–40 (`check_B3_powers.out`); two independent AI reviews reproduced them up to μ = 60. |
| Band-edge lower bounds `\|ξφ̂_B′(λ)\| ≥ 9.6 λ²² e^{−2πμ}`, `\|φ̂_B(λ)\| ≥ 4.4 λ¹⁸ e^{−2πμ}` (Remark 5.4) | P, S, N, R | They show that the powers in Lemma 5.3 are optimal. They say nothing about the optimality of `p = 46` or about lower bounds for `λ_min`. |
| `g(z) = √z e^{−z} I₂(z)` is nondecreasing, with limit `1/√(2π)` (Lemma 5.5) | P, N, R | The integral representation was checked to relative error ≤ 10⁻¹⁶. Two AI reviews checked monotonicity on fine grids of z ≤ 500. |
| Two-sided bounds for `Φ_β(x/λ)/I₂(β)`: upper bound `e^{−πx²}`, explicit lower bound (Lemma 5.6) | P, N, R | Checked on grids for μ = 5–60. The upper bound replaces the domination constant 36.14 of v1.0.x by 1. |
| `σ ≤ 0.66096` and `‖k_B‖² ≥ 6.549·10⁻⁶` for μ ≥ 5 (Lemma 5.7) | P, B, N, R | Rigorous integration in Arb (`theoremB_explicit.out`). The true values are σ = 0.42–0.47 and ∫e_B² = 5.9·10⁻⁵–9.3·10⁻⁵ for μ = 5–60. |
| `B_{φ_B} ≤ Q(λ)e^{−2πμ}`, `Q(λ)/λ²³ ≤ 310.72` for μ ≥ 5 (Lemma 5.8) | P, B, N, R | The eleven coefficients of `Q` are enclosed in Arb and are positive. The pointwise envelopes used in the proof exceed the true `\|φ̂_B\|`, `\|ξφ̂_B′\|` on ω ∈ [β, 50β] for μ = 5–60. The true `B_{φ_B}` is smaller than `Q e^{−2πμ}` by a factor of about 660 (μ = 5). |
| Final constant `1.362·10⁹` for all μ ≥ 5 | P, B, R | `2 · 0.046192 · 310.72² / 6.549·10⁻⁶ ≤ 1.362·10⁹`. |
| Proposition 3.5 for `φ_B` | N | The bound exceeds `W(k)` by a factor 46–207 for μ = 5, 7 and 11. |

## Errors found and corrected during the work

These errors were found and corrected during the work. They are recorded for transparency.

- In v1.0.x, Theorem B had a non-effective threshold `λ₀`. Release v1.1.0 makes it explicit for all μ ≥ 5. During the review of this change, one printed lower bound had been rounded in the wrong direction (0.92106 instead of 0.9210599), and one chained step did not follow from the rounded numbers. Both were corrected, and the script now asserts the direction of every printed constant.
- A draft of the revised paper stated the power `λ²⁰` for `ξφ̂_B′` in Lemma 5.3 (and `p = 42`); release v1.0.0 gave no explicit powers. The correct power is `λ²²`, and `p = 46`. The error was a miscount of the largest power of ω; it was found by a numerical check. The same check first contained a bug of its own: a central difference at the non-smooth point ξ = λ halved the derivative. The scripts in this release evaluate the derivative exactly.
- An earlier draft of Theorem B claimed `\|ξφ̂'\| ≤ C(1+\|ξ\|)^{−3}`. The true decay is ξ⁻², and the hypothesis was weakened accordingly.
- A proposed uniform Bessel bound was false.
- A sign or coefficient error in a derivative in an auxiliary script was caught by comparison with difference quotients.

## Not verified

- Review by independent human experts.
- The precise section of Watson's treatise for the Sonine–Gegenbauer integral.
