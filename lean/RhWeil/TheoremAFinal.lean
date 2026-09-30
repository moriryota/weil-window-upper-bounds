import RhWeil.LowerBound
import RhWeil.WeilBridge

/-!
# Theorem A, unconditionally

`TheoremA.Inputs` is proved for the concrete test functions `φ_λ = h χ + ε ψ`, hence Theorem A holds:
for large `λ` there is a real window test function `k ∈ C²` (support in `[-log λ, log λ]`, `‖k‖² > 0`)
whose Weil form, on the geometric side of the explicit formula, satisfies
`|W(k)| ≤ C λ^p e^{-2πλ²} ‖k‖²`. No hypothesis on the zeros of `ζ` is used.
-/

noncomputable section

namespace RhWeil
namespace Concrete

open Real MeasureTheory Set Filter Topology Complex Zeta23 Zeta23.EF
open scoped FourierTransform

theorem inputs : TheoremA.Inputs := by
  obtain ⟨C₁, q₁, hC₁, t1⟩ := tail_φ
  obtain ⟨C₂, q₂, hC₂, t2⟩ := tail_psi1
  obtain ⟨c₀, hc₀, lam₀, hl₀, hQ1⟩ := Q1
  refine Construction.inputs_of_tails ⟨c₀, C₁ + C₂, ((q₁ + q₂ : ℕ) : ℝ), lam₀, hc₀, by positivity,
    by linarith, fun lam hlam => ?_⟩
  have hl : 3 ≤ lam := hl₀.trans hlam
  have hl1 : 1 ≤ lam := by linarith
  have hlog := one_le_log hl
  have hδ := δ_pos hl
  have hδ9 := δ_le hl
  set E := Real.exp (-π * lam ^ 2)
  have hE : 0 < E := Real.exp_pos _
  have hq : lam ^ ((q₁ + q₂ : ℕ) : ℝ) = lam ^ (q₁ + q₂) := Real.rpow_natCast _ _
  refine ⟨φ lam, LL lam, δ lam, C₁ * lam ^ q₁ * E, C₂ * lam ^ q₂ * E, Ξ lam,
    contDiff_φ lam, φ_real lam, φ_even lam, φ_zero lam, fourier_φ_zero hl,
    by linarith [one_le_LL hl], LL_le hl, φ_supp hl, hδ, by linarith, by linarith,
    by unfold Ξ; positivity, ?_, fun ξ hξ => ?_, fun ξ hξ => ?_, ?_, ?_, hQ1 lam hlam⟩
  · -- `e^{-log λ + τ} Ξ = 1`
    unfold Ξ
    rw [show -Real.log lam + δ lam = -(Real.log lam - δ lam) by ring, Real.exp_neg,
      Real.exp_sub, Real.exp_log (by linarith)]
    field_simp
    rw [← Real.exp_add]; simp
  · have := t1 lam hl ξ hξ; rwa [mul_div_assoc] at this ⊢
  · have := t2 lam hl ξ hξ; rwa [mul_div_assoc] at this ⊢
  · rw [hq]
    have : lam ^ q₁ ≤ lam ^ (q₁ + q₂) := pow_le_pow_right₀ hl1 (by omega)
    calc C₁ * lam ^ q₁ * E ≤ C₁ * lam ^ (q₁ + q₂) * E := by gcongr
      _ ≤ (C₁ + C₂) * lam ^ (q₁ + q₂) * E := by gcongr; linarith
  · rw [hq]
    have : lam ^ q₂ ≤ lam ^ (q₁ + q₂) := pow_le_pow_right₀ hl1 (by omega)
    calc C₂ * lam ^ q₂ * E ≤ C₂ * lam ^ (q₁ + q₂) * E := by gcongr
      _ ≤ (C₁ + C₂) * lam ^ (q₁ + q₂) * E := by gcongr; linarith

/-- **Theorem A** (unconditional). -/
theorem theoremA : ∃ C p lam₀ : ℝ, ∀ lam ≥ lam₀, ∃ k : ℝ → ℂ,
    TheoremA.WindowTest lam k ∧ 0 < TheoremA.l2sq k ∧
    ‖literatureRHS (weilTest k k)‖ ≤ C * lam ^ p * Real.exp (-2 * Real.pi * lam ^ 2) * TheoremA.l2sq k :=
  TheoremA.main_geometric inputs

end Concrete
end RhWeil
