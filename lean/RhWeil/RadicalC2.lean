import RhWeil.Poisson
import RhWeil.FourierDecay

/-!
# Radical lemma for even `C²_c` functions with `φ(0) = ∫φ = 0`

The hypotheses of `Radical.paperFT_Esum_zero'` reduce to smoothness, support and two vanishing
conditions.
-/

noncomputable section

namespace RhWeil
namespace Radical

open Complex MeasureTheory Set Filter Asymptotics Topology Real
open scoped FourierTransform

theorem paperFT_Esum_zero_C2 {φ : ℝ → ℂ} {L : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ v, L ≤ |v| → φ v = 0) (heven : ∀ v, φ (-v) = φ v) (h00 : φ 0 = 0)
    (hint : 𝓕 φ 0 = 0) {ρ : ℂ} (hρ : Zeta23.IsNontrivialZero ρ) :
    Zeta23.paperFT (fun y => Esum φ (Real.exp y)) (Zeta23.gammaOf ρ) = 0 ∧
    Zeta23.paperFT (fun y => Esum φ (Real.exp y)) (-Zeta23.gammaOf ρ) = 0 := by
  have hs : HasCompactSupport φ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0:ℝ) L) fun v hv => hsupp v ?_
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hv
    exact hv.le
  exact paperFT_Esum_zero' hφ.continuous hsupp heven h00
    (norm_fourier_le_of_contDiff_two hφ hs hint) (isBigO_sq_of_even hφ heven h00) hρ

end Radical
end RhWeil
