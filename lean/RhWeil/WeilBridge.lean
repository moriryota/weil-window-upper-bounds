import RhWeil.TheoremA
import Zeta23.WeilEF.Main
import Zeta23.Statement.SeamClosed

/-!
# Zero side = geometric side (explicit formula, Zeta23 `EF_lit_zeta`)

For a real-valued `k ∈ C²_c`, `zeroSide Z k = literatureRHS (k ⋆ k̃)`: the zero side of the Weil
form equals its geometric side (archimedean term, poles, primes), unconditionally.
-/

noncomputable section

namespace RhWeil

open Complex MeasureTheory Zeta23 Zeta23.EF

theorem conj_paperFT_conj_of_real {k : ℝ → ℂ} (hreal : ∀ y, (starRingEnd ℂ) (k y) = k y) (z : ℂ) :
    (starRingEnd ℂ) (paperFT k ((starRingEnd ℂ) z)) = paperFT k (-z) := by
  unfold paperFT
  rw [← integral_conj]
  congr 1; ext y
  rw [map_mul, hreal, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, Complex.conj_I, Complex.conj_conj, Complex.conj_ofReal]
  ring

/-- **Bridge.** For real `k ∈ C²_c`, the zero side of `W(k)` equals the geometric side
`literatureRHS (weilTest k k)` of the explicit formula (Zeta23, `EF_lit_zeta`). -/
theorem zeroSide_eq_literatureRHS {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hks : HasCompactSupport k)
    (hreal : ∀ y, (starRingEnd ℂ) (k y) = k y) :
    zeroSide TheoremA.Z k = literatureRHS (weilTest k k) := by
  have hEF := (WeilEF.EF_lit_zetaZeroConfig) (weilTest k k)
    (weilTest_contDiff hk hk.continuous hks) (weilTest_hasCompactSupport hks hks)
  rw [← hEF.2]
  unfold zeroSide
  congr 1; ext ρ
  rw [paperFT_weilTest hk.continuous hk.continuous hks hks, conj_paperFT_conj_of_real hreal]
  have : (TheoremA.Z.mult ρ : ℂ) = (zetaZeroConfig.mult ρ : ℂ) := rfl
  rw [this]; ring

/-- **Theorem A, geometric form (modulo `Inputs`).** For large `lam` there is a real window test
function `k ∈ C²` whose Weil form, computed on the geometric side of the explicit formula, satisfies
`|W(k)| ≤ C lam^p e^{-2π lam²} ‖k‖²`. -/
theorem TheoremA.main_geometric (H : TheoremA.Inputs) : ∃ C p lam₀ : ℝ, ∀ lam ≥ lam₀, ∃ k : ℝ → ℂ,
    TheoremA.WindowTest lam k ∧ 0 < TheoremA.l2sq k ∧
    ‖literatureRHS (weilTest k k)‖ ≤ C * lam ^ p * Real.exp (-2 * Real.pi * lam ^ 2) * TheoremA.l2sq k := by
  obtain ⟨C, p, lam₀, h⟩ := TheoremA.main H
  refine ⟨C, p, lam₀, fun lam hlam => ?_⟩
  obtain ⟨k, hW, hreal, hpos, hb⟩ := h lam hlam
  have hks : HasCompactSupport k :=
    HasCompactSupport.intro' isCompact_Icc isClosed_Icc (fun y hy => image_eq_zero_of_notMem_tsupport
      (fun h => hy (hW.2 h)))
  refine ⟨k, hW, hpos, ?_⟩
  rw [← zeroSide_eq_literatureRHS hW.1 hks hreal]
  exact hb

end RhWeil
