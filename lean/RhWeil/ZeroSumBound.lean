import Zeta23.WeilEF.ZeroSummability

/-!
# Theorem A, core estimate (Proposition 3.1 of the paper draft)

If `k̂ = -r̂` at every zero ordinate `±γ_ρ` and `‖r̂ z‖² ≤ A / (1 + |z|²)` there, then the zero side
of the Weil form of `k` is bounded by `A · Σ_ρ m_ρ / (1 + |γ_ρ|²)`. No hypothesis on the location
of the zeros is used.
-/

noncomputable section

namespace RhWeil

open Complex Zeta23

/-- Zero side of the Weil quadratic form of `k`: `Σ_ρ m_ρ k̂(γ_ρ) k̂(-γ_ρ)`. -/
def zeroSide (Z : ZeroConfig) (k : ℝ → ℂ) : ℂ :=
  ∑' ρ : Z.carrier, (Z.mult ρ : ℂ) * paperFT k (gammaOf ρ) * paperFT k (-gammaOf ρ)

theorem norm_zeroSide_le (Z : ZeroConfig)
    (hS : Summable (fun ρ : Z.carrier => (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))))
    (k r : ℝ → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (hvan : ∀ ρ ∈ Z.carrier, paperFT k (gammaOf ρ) = -paperFT r (gammaOf ρ) ∧
      paperFT k (-gammaOf ρ) = -paperFT r (-gammaOf ρ))
    (hr : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖paperFT r z‖ ^ 2 ≤ A / (1 + Complex.normSq z))
    (hstrip : ∀ ρ ∈ Z.carrier, |(gammaOf ρ).im| ≤ 1 / 2) :
    ‖zeroSide Z k‖ ≤ A * ∑' ρ : Z.carrier, (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)) := by
  -- termwise bound
  have hterm : ∀ ρ : Z.carrier,
      ‖(Z.mult ρ : ℂ) * paperFT k (gammaOf ρ) * paperFT k (-gammaOf ρ)‖
        ≤ A * ((Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
    intro ρ
    obtain ⟨h1, h2⟩ := hvan ρ ρ.2
    have hs := hstrip ρ ρ.2
    have hs' : |(-gammaOf ρ).im| ≤ 1 / 2 := by simpa [abs_neg] using hs
    have hpos : 0 < 1 + Complex.normSq (gammaOf ρ) :=
      add_pos_of_pos_of_nonneg one_pos (Complex.normSq_nonneg _)
    have e1 := hr _ hs
    have e2 := hr _ hs'
    rw [Complex.normSq_neg] at e2
    set D := 1 + Complex.normSq (gammaOf ρ)
    set a := ‖paperFT r (gammaOf ρ)‖
    set b := ‖paperFT r (-gammaOf ρ)‖
    have ha : 0 ≤ a := norm_nonneg _
    have hb : 0 ≤ b := norm_nonneg _
    have hab : a * b ≤ A / D := by
      have : (a * b) ^ 2 ≤ (A / D) ^ 2 := by
        rw [mul_pow, sq (A / D)]
        exact mul_le_mul e1 e2 (sq_nonneg _) (div_nonneg hA hpos.le)
      exact (pow_le_pow_iff_left₀ (mul_nonneg ha hb) (div_nonneg hA hpos.le) two_ne_zero).1 this
    calc ‖(Z.mult ρ : ℂ) * paperFT k (gammaOf ρ) * paperFT k (-gammaOf ρ)‖
        = (Z.mult ρ : ℝ) * (a * b) := by
          rw [h1, h2, norm_mul, norm_mul, norm_neg, norm_neg, Complex.norm_natCast]; ring
      _ ≤ (Z.mult ρ : ℝ) * (A / D) := by gcongr
      _ = A * ((Z.mult ρ : ℝ) / D) := by ring
  have hsum : Summable (fun ρ : Z.carrier =>
      ‖(Z.mult ρ : ℂ) * paperFT k (gammaOf ρ) * paperFT k (-gammaOf ρ)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hS.mul_left A)
  calc ‖zeroSide Z k‖
      ≤ ∑' ρ : Z.carrier, ‖(Z.mult ρ : ℂ) * paperFT k (gammaOf ρ) * paperFT k (-gammaOf ρ)‖ :=
        norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' ρ : Z.carrier, A * ((Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) :=
        hsum.tsum_le_tsum hterm (hS.mul_left A)
    _ = A * ∑' ρ : Z.carrier, (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)) := tsum_mul_left

end RhWeil
