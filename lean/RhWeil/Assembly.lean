import RhWeil.GTail
import RhWeil.Bump
import RhWeil.Tail

/-!
# The concrete test function `φ_λ = h χ + ε ψ` and its qualitative properties
-/

noncomputable section

namespace RhWeil
namespace Concrete

open Real MeasureTheory Set Filter Topology Cutoff
open scoped FourierTransform

variable {lam : ℝ}

def δ (lam : ℝ) : ℝ := 1 / lam ^ 2
def bb (lam : ℝ) : ℝ := lam - 2 * δ lam
def LL (lam : ℝ) : ℝ := lam - δ lam
def eps (lam : ℝ) : ℝ := ∫ x, g (bb lam) (δ lam) x
def φR (lam : ℝ) (x : ℝ) : ℝ := h x * chi (bb lam) (δ lam) x + eps lam * Bump.psi x
def φ (lam : ℝ) (x : ℝ) : ℂ := (φR lam x : ℂ)

theorem δ_pos (hl : 3 ≤ lam) : 0 < δ lam := by unfold δ; positivity
theorem δ_le (hl : 3 ≤ lam) : δ lam ≤ 1 / 9 := by
  unfold δ; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
theorem bb_ge (hl : 3 ≤ lam) : 1 ≤ bb lam := by unfold bb; linarith [δ_le hl]
theorem LL_eq (lam : ℝ) : LL lam = bb lam + δ lam := by unfold LL bb; ring
theorem LL_le (hl : 3 ≤ lam) : LL lam ≤ lam := by unfold LL; linarith [δ_pos hl]
theorem one_le_LL (hl : 3 ≤ lam) : 1 ≤ LL lam := by rw [LL_eq]; linarith [bb_ge hl, δ_pos hl]

theorem contDiff_φR (lam : ℝ) {n : ℕ∞} : ContDiff ℝ n (φR lam) :=
  (contDiff_h.mul (contDiff_chi _ _)).add (contDiff_const.mul Bump.contDiff_psi)

theorem contDiff_φ (lam : ℝ) {n : ℕ∞} : ContDiff ℝ n (φ lam) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_φR lam)

theorem φ_real (lam x : ℝ) : (starRingEnd ℂ) (φ lam x) = φ lam x := Complex.conj_ofReal _

theorem φ_even (lam x : ℝ) : φ lam (-x) = φ lam x := by
  simp only [φ, φR, h_even, chi_even, Bump.psi_even]

theorem φ_zero (lam : ℝ) : φ lam 0 = 0 := by simp [φ, φR, h_zero, Bump.psi_zero]

theorem φ_supp (hl : 3 ≤ lam) : ∀ v, LL lam ≤ |v| → φ lam v = 0 := by
  intro v hv
  have h1 : chi (bb lam) (δ lam) v = 0 := chi_eq_zero (δ_pos hl) (by rw [← LL_eq]; exact hv)
  have h2 : Bump.psi v = 0 := Bump.psi_eq_zero ((one_le_LL hl).trans hv)
  simp [φ, φR, h1, h2]

/-! Integrability and bounds of `g` and its derivatives (from `GTail`). -/

theorem g_bounds (hl : 3 ≤ lam) : ∃ A : ℝ, ∃ d : ℕ, 0 ≤ A ∧ ∀ n ≤ 3,
    Integrable (iteratedDeriv n (g (bb lam) (δ lam))) ∧
    ∫ x, |iteratedDeriv n (g (bb lam) (δ lam)) x| ≤
      2 * (2 ^ n * A / δ lam ^ n * d.factorial * Real.exp 1 * (1 + bb lam) ^ d *
        Real.exp (-π * bb lam ^ 2)) := by
  obtain ⟨K, d, hK, hh⟩ := exists_bound_h
  obtain ⟨B, hB1, hB⟩ := exists_bound_one_sub_chi
  refine ⟨K * B, d, mul_nonneg hK (by linarith), fun n hn => ?_⟩
  have hδ := δ_pos hl
  have hδ1 : δ lam ≤ 1 := (δ_le hl).trans (by norm_num)
  have hb := bb_ge hl
  have hcont : Continuous (iteratedDeriv n (g (bb lam) (δ lam))) :=
    (contDiff_g (bb lam) (δ lam) (m := n)).continuous_iteratedDeriv' n
  have := integral_abs_le_of_tail hcont (A := 2 ^ n * K * B / δ lam ^ n) (b := bb lam) (d := d)
    (by positivity) hb
    (fun x => abs_iteratedDeriv_g_le hK hh hB1 hB hδ hδ1 (by linarith) hn x)
    (fun x hx => iteratedDeriv_g_eq_zero hδ n hx)
  refine ⟨this.1, this.2.trans (le_of_eq ?_)⟩
  ring

theorem integrable_g (hl : 3 ≤ lam) : Integrable (g (bb lam) (δ lam)) := by
  obtain ⟨A, d, _, hg⟩ := g_bounds hl
  simpa using (hg 0 (by norm_num)).1

theorem integral_φR (hl : 3 ≤ lam) : ∫ x, φR lam x = 0 := by
  have hg := integrable_g hl
  have e : φR lam = fun x => (h x - g (bb lam) (δ lam) x) + eps lam * Bump.psi x := by
    funext x; simp only [φR, g]; ring
  have ipsi : Integrable Bump.psi :=
    (Bump.contDiff_psi (n := 0)).continuous.integrable_of_hasCompactSupport Bump.hasCompactSupport_psi
  have i1 : Integrable (fun x => h x - g (bb lam) (δ lam) x) := integrable_h.sub hg
  have i2 : Integrable (fun x => eps lam * Bump.psi x) := ipsi.const_mul _
  rw [e, integral_add i1 i2, integral_sub integrable_h hg,
    integral_const_mul, Bump.integral_psi, integral_h]
  simp [eps]

theorem fourier_φ_zero (hl : 3 ≤ lam) : 𝓕 (φ lam) 0 = 0 := by
  rw [Construction.fourier_zero_eq_integral]
  simp only [φ]
  rw [integral_complex_ofReal, integral_φR hl]; simp

end Concrete
end RhWeil
