import RhWeil.ZeroSumBound
import RhWeil.RHatBound

/-!
# Theorem A: skeleton

`TheoremA.Inputs` collects the analytic lemmas of the paper draft that are not yet formalised:
the construction of `k = ℰ(φ)·1_window` and `r = ℰ(φ)·1_{(-∞,-a)}` (Lemmas 2.1, 2.2), the bound on
`r̂` (Proposition 3.1 / Lemma 3.2 with the tails of §4), and the lower bound for `‖k‖` (§4).
From these, `TheoremA.main` derives the unconditional bound on the zero side of the Weil form,
using only the summability of `Σ m_ρ/(1+|γ_ρ|²)` over the zeros of Mathlib's `riemannZeta`.
-/

noncomputable section

namespace RhWeil
namespace TheoremA

open Complex Zeta23 Zeta23.WeilEF MeasureTheory

/-- The zeros of `ζ` (Mathlib), as a Zeta23 zero configuration. -/
abbrev Z : ZeroConfig := zetaZeros zetaSeam

/-- Test functions for the window `[lam⁻¹, lam]`, i.e. `[-log lam, log lam]` in log coordinates
(`C²`, as required by Zeta23's explicit formula `EF_lit`). -/
def WindowTest (lam : ℝ) (f : ℝ → ℂ) : Prop :=
  ContDiff ℝ 2 f ∧ tsupport f ⊆ Set.Icc (-Real.log lam) (Real.log lam)

/-- Squared `L²` norm. -/
def l2sq (f : ℝ → ℂ) : ℝ := ∫ y, ‖f y‖ ^ 2

/-- Weighted `L¹` norm `∫ ‖f‖ e^{|y|/2}` (the quantities `A₀`, `A₁` of Proposition 3.1). -/
def wL1 (f : ℝ → ℂ) : ℝ := ∫ y, ‖f y‖ * Real.exp (|y| / 2)

/-- Analytic inputs (to be proved in later files):
* `k` is a smooth window test function with `‖k‖² ≥ c₀`  (§4, lower bound);
* `k̂ = -r̂` at every `±γ_ρ`  (Lemma 2.2: `k + r = ℰ(φ)` lies in the radical);
* `r` is `C¹` with the weighted integrability used in Proposition 3.1;
* `(A₀ + A₁)² ≤ C₁ lam^p e^{-2π lam²}`  (Lemma 3.2 with the tails of §4, explicit in §4 of the paper). -/
structure Inputs : Prop where
  bound : ∃ c₀ C₁ p lam₀ : ℝ, 0 < c₀ ∧ 0 ≤ C₁ ∧ ∀ lam ≥ lam₀, ∃ k r r' : ℝ → ℂ,
    WindowTest lam k ∧ (∀ y, (starRingEnd ℂ) (k y) = k y) ∧ c₀ ≤ l2sq k ∧
    (∀ ρ ∈ Z.carrier, paperFT k (gammaOf ρ) = -paperFT r (gammaOf ρ) ∧
      paperFT k (-gammaOf ρ) = -paperFT r (-gammaOf ρ)) ∧
    (∀ y, HasDerivAt r (r' y) y) ∧ Continuous r' ∧
    Integrable (fun y => ‖r y‖ * Real.exp (|y| / 2)) ∧
    Integrable (fun y => ‖r' y‖ * Real.exp (|y| / 2)) ∧
    (wL1 r + wL1 r') ^ 2 ≤ C₁ * lam ^ p * Real.exp (-2 * Real.pi * lam ^ 2)

/-- Every non-trivial zero has `|Im γ_ρ| ≤ 1/2`. -/
theorem abs_im_gammaOf_le {ρ : ℂ} (h : ρ ∈ Z.carrier) : |(gammaOf ρ).im| ≤ 1 / 2 := by
  obtain ⟨h0, h1⟩ := Z.strip ρ h
  have : (gammaOf ρ).im = 1 / 2 - ρ.re := by
    simp [gammaOf]
  rw [this, abs_le]; constructor <;> linarith

theorem summable_S :
    Summable (fun ρ : Z.carrier => (Z.mult ρ : ℝ) / (1 + normSq (gammaOf ρ))) := by
  simpa [Z, zeroMult] using zero_sum_inv_sq zetaSeam

/-- **Theorem A** (modulo `Inputs`): for large `lam` there is a window test function `k` with
`|W(k)| ≤ C lam^p e^{-2π lam²} ‖k‖²`, where `W(k)` is the zero side of the Weil form. -/
theorem main (H : Inputs) : ∃ C p lam₀ : ℝ, ∀ lam ≥ lam₀, ∃ k : ℝ → ℂ,
    WindowTest lam k ∧ (∀ y, (starRingEnd ℂ) (k y) = k y) ∧ 0 < l2sq k ∧
    ‖zeroSide Z k‖ ≤ C * lam ^ p * Real.exp (-2 * Real.pi * lam ^ 2) * l2sq k := by
  obtain ⟨c₀, C₁, p, lam₀, hc₀, hC₁, hk⟩ := H.bound
  set S := ∑' ρ : Z.carrier, (Z.mult ρ : ℝ) / (1 + normSq (gammaOf ρ))
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => div_nonneg (Nat.cast_nonneg _)
    (add_pos_of_pos_of_nonneg one_pos (Complex.normSq_nonneg _)).le
  refine ⟨2 * C₁ * S / c₀, p, max lam₀ 1, fun lam hlam => ?_⟩
  have hlam0 : lam ≥ lam₀ := le_trans (le_max_left _ _) hlam
  have hlam1 : 0 < lam := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hlam)
  obtain ⟨k, r, r', hW, hreal, hnorm, hvan, hd, hr', hi, hi', hA⟩ := hk lam hlam0
  set E := C₁ * lam ^ p * Real.exp (-2 * Real.pi * lam ^ 2)
  have hE : 0 ≤ E := by positivity
  set A := 2 * (wL1 r + wL1 r') ^ 2
  have hA0 : 0 ≤ A := by positivity
  have hr : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖paperFT r z‖ ^ 2 ≤ A / (1 + normSq z) :=
    fun z hz => norm_paperFT_sq_le hd hr' hi hi' le_rfl le_rfl hz
  have hmain := norm_zeroSide_le Z summable_S k r hA0 hvan hr (fun ρ h => abs_im_gammaOf_le h)
  refine ⟨k, hW, hreal, lt_of_lt_of_le hc₀ hnorm, ?_⟩
  have hAE : A ≤ 2 * E := by simp only [A]; linarith
  calc ‖zeroSide Z k‖ ≤ A * S := hmain
    _ ≤ 2 * E * S := by gcongr
    _ ≤ 2 * E * S * (l2sq k / c₀) := by
        have : 1 ≤ l2sq k / c₀ := (one_le_div hc₀).2 hnorm
        nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hE) hS0]
    _ = 2 * C₁ * S / c₀ * lam ^ p * Real.exp (-2 * Real.pi * lam ^ 2) * l2sq k := by
        simp only [E]; field_simp

end TheoremA
end RhWeil
