import RhWeil.Assembly

/-!
# Tail bound for `𝓕φ_λ` on `|ξ| ≥ Ξ = λ e^{-1/λ²}`

`𝓕φ = 𝓕h - 𝓕g + ε 𝓕ψ`, each term `≤ (const) λ^q e^{-πλ²} / ξ²`.
-/

noncomputable section

namespace RhWeil
namespace Concrete

open Real MeasureTheory Set Filter Topology Cutoff Complex
open scoped FourierTransform

theorem integrable_char_smul {f : ℝ → ℂ} (hf : Integrable f) (ξ : ℝ) :
    Integrable (fun v : ℝ => 𝐞 (-(v * ξ)) • f v) := by
  refine hf.norm.mono' ?_ (Filter.Eventually.of_forall fun v => by rw [Circle.norm_smul])
  exact (Continuous.aestronglyMeasurable (by fun_prop)).smul hf.aestronglyMeasurable

theorem fourier_lin3 {f₁ f₂ f₃ : ℝ → ℂ} (i1 : Integrable f₁) (i2 : Integrable f₂)
    (i3 : Integrable f₃) (c : ℂ) (ξ : ℝ) :
    𝓕 (fun x => f₁ x - f₂ x + c * f₃ x) ξ = 𝓕 f₁ ξ - 𝓕 f₂ ξ + c * 𝓕 f₃ ξ := by
  simp only [Real.fourier_real_eq]
  have e : (fun v : ℝ => 𝐞 (-(v * ξ)) • (f₁ v - f₂ v + c * f₃ v)) =
      fun v => (𝐞 (-(v * ξ)) • f₁ v - 𝐞 (-(v * ξ)) • f₂ v) + c * 𝐞 (-(v * ξ)) • f₃ v := by
    funext v; simp only [Circle.smul_def, smul_eq_mul]; ring
  have j1 : Integrable (fun v : ℝ => 𝐞 (-(v * ξ)) • f₁ v - 𝐞 (-(v * ξ)) • f₂ v) :=
    (integrable_char_smul i1 ξ).sub (integrable_char_smul i2 ξ)
  have j2 : Integrable (fun v : ℝ => c * 𝐞 (-(v * ξ)) • f₃ v) :=
    (integrable_char_smul i3 ξ).const_mul c
  rw [e, integral_add j1 j2, integral_sub (integrable_char_smul i1 ξ)
    (integrable_char_smul i2 ξ), integral_const_mul]

variable {lam : ℝ}

def Ξ (lam : ℝ) : ℝ := lam * Real.exp (-δ lam)

theorem Ξ_ge_one (hl : 3 ≤ lam) : 1 ≤ Ξ lam := by
  unfold Ξ
  have h1 : 1 - δ lam ≤ Real.exp (-δ lam) := by linarith [Real.add_one_le_exp (-δ lam)]
  have := δ_le hl
  nlinarith

theorem Ξ_le (hl : 3 ≤ lam) : Ξ lam ≤ lam := by
  unfold Ξ
  have : Real.exp (-δ lam) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [δ_pos hl])
  nlinarith

theorem exp_Ξ_le (hl : 3 ≤ lam) :
    Real.exp (-π * Ξ lam ^ 2) ≤ Real.exp (2 * π) * Real.exp (-π * lam ^ 2) := by
  rw [← Real.exp_add]; apply Real.exp_le_exp.2
  have h1 : 1 - 2 * δ lam ≤ Real.exp (-2 * δ lam) := by linarith [Real.add_one_le_exp (-2 * δ lam)]
  have h2 : Ξ lam ^ 2 = lam ^ 2 * Real.exp (-2 * δ lam) := by
    unfold Ξ; rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
  have h3 : lam ^ 2 * δ lam = 1 := by unfold δ; field_simp
  have : lam ^ 2 - 2 ≤ Ξ lam ^ 2 := by rw [h2]; nlinarith [sq_nonneg lam]
  nlinarith [pi_pos]

theorem exp_bb_le (hl : 3 ≤ lam) :
    Real.exp (-π * bb lam ^ 2) ≤ Real.exp (4 * π) * Real.exp (-π * lam ^ 2) := by
  rw [← Real.exp_add]; apply Real.exp_le_exp.2
  have hδ : lam * δ lam ≤ 1 := by
    unfold δ; rw [mul_one_div, div_le_one (by positivity)]; nlinarith
  have : lam ^ 2 - 4 ≤ bb lam ^ 2 := by
    unfold bb; nlinarith [δ_pos hl, sq_nonneg (δ lam)]
  nlinarith [pi_pos]

/-- Uniform-in-`λ` bounds for `g` and its derivatives. -/
theorem g_bounds_unif : ∃ A : ℝ, ∃ d : ℕ, 0 ≤ A ∧ ∀ lam : ℝ, 3 ≤ lam → ∀ n ≤ 3,
    Integrable (iteratedDeriv n (g (bb lam) (δ lam))) ∧
    ∫ x, |iteratedDeriv n (g (bb lam) (δ lam)) x| ≤
      2 * (2 ^ n * A / δ lam ^ n * d.factorial * Real.exp 1 * (1 + bb lam) ^ d *
        Real.exp (-π * bb lam ^ 2)) := by
  obtain ⟨K, d, hK, hh⟩ := exists_bound_h
  obtain ⟨B, hB1, hB⟩ := exists_bound_one_sub_chi
  refine ⟨K * B, d, mul_nonneg hK (by linarith), fun lam hl n hn => ?_⟩
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

theorem one_add_bb_le (hl : 3 ≤ lam) : 1 + bb lam ≤ 2 * lam := by
  unfold bb; linarith [δ_pos hl]

theorem inv_δ (hl : 3 ≤ lam) : 1 / δ lam = lam ^ 2 := by
  unfold δ; field_simp

/-- `λ^k ≤ λ^q` for `λ ≥ 1`, `k ≤ q`. -/
theorem pow_le_pow_of_one_le' {x : ℝ} (hx : 1 ≤ x) {k q : ℕ} (hkq : k ≤ q) : x ^ k ≤ x ^ q :=
  pow_le_pow_right₀ hx hkq

/-- **Tail bound for `𝓕φ_λ`.** -/
theorem tail_φ : ∃ C : ℝ, ∃ q : ℕ, 0 ≤ C ∧ ∀ lam : ℝ, 3 ≤ lam → ∀ ξ : ℝ, Ξ lam ≤ |ξ| →
    ‖𝓕 (φ lam) ξ‖ ≤ C * lam ^ q * Real.exp (-π * lam ^ 2) / ξ ^ 2 := by
  obtain ⟨KF, dF, hKF, hF⟩ := GaussPoly.fourier_F_bound R
  obtain ⟨A, d, hA, hg⟩ := g_bounds_unif
  obtain ⟨Cψ, hψ⟩ := Bump.exists_fourier_bound (fun n => Bump.contDiff_psi) Bump.hasCompactSupport_psi
  set Cψ' := max Cψ 0
  set C1 := KF * ((dF + 2).factorial * Real.exp 1 * 2 ^ (dF + 2) * Real.exp (2 * π))
  set C2 := 2 * (4 * A * d.factorial * Real.exp 1 * 2 ^ d * Real.exp (4 * π)) / (4 * π ^ 2)
  set C3 := 2 * (A * d.factorial * Real.exp 1 * 2 ^ d * Real.exp (4 * π)) * Cψ'
  refine ⟨C1 + C2 + C3, dF + d + 6, by positivity, fun lam hl ξ hξ => ?_⟩
  have hl1 : 1 ≤ lam := by linarith
  have hΞ1 := Ξ_ge_one hl
  have hξ0 : ξ ≠ 0 := by intro h; rw [h, abs_zero] at hξ; linarith
  have hξ2 : 0 < ξ ^ 2 := by positivity
  set E := Real.exp (-π * lam ^ 2)
  have hE : 0 < E := Real.exp_pos _
  -- decomposition
  have hφ : φ lam = fun x => ((h x : ℝ) : ℂ) - ((g (bb lam) (δ lam) x : ℝ) : ℂ) +
      ((eps lam : ℝ) : ℂ) * ((Bump.psi x : ℝ) : ℂ) := by
    funext x; simp only [φ, φR, g]; push_cast; ring
  obtain ⟨ig0, bg0⟩ := hg lam hl 0 (by norm_num)
  obtain ⟨ig1, bg1⟩ := hg lam hl 1 (by norm_num)
  obtain ⟨ig2, bg2⟩ := hg lam hl 2 (by norm_num)
  simp only [iteratedDeriv_zero] at ig0 bg0
  have ipsi : Integrable (fun x => ((Bump.psi x : ℝ) : ℂ)) :=
    ((Bump.contDiff_psi (n := 0)).continuous.integrable_of_hasCompactSupport
      Bump.hasCompactSupport_psi).ofReal
  rw [hφ, fourier_lin3 (f₁ := fun x => ((h x : ℝ) : ℂ)) (f₂ := fun x => ((g (bb lam) (δ lam) x : ℝ) : ℂ))
    (f₃ := fun x => ((Bump.psi x : ℝ) : ℂ)) integrable_h_ofReal ig0.ofReal ipsi]
  -- term 1: 𝓕h
  have t1 : ‖𝓕 (fun x => ((h x : ℝ) : ℂ)) ξ‖ ≤ C1 * lam ^ (dF + d + 6) * E / ξ ^ 2 := by
    have b1 := hF ξ
    have b2 := GaussPoly.sup_tail (dF + 2) hΞ1 hξ
    have b3 : (1 + Ξ lam) ^ (dF + 2) ≤ (2 * lam) ^ (dF + 2) := by
      gcongr; linarith [Ξ_le hl]
    have b4 := exp_Ξ_le hl
    rw [le_div_iff₀ hξ2]
    calc ‖𝓕 (fun x => ((h x : ℝ) : ℂ)) ξ‖ * ξ ^ 2
        ≤ KF * (1 + |ξ|) ^ dF * Real.exp (-π * ξ ^ 2) * (1 + |ξ|) ^ 2 := by
          have hsq : ξ ^ 2 ≤ (1 + |ξ|) ^ 2 := by nlinarith [abs_nonneg ξ, sq_abs ξ]
          exact mul_le_mul b1 hsq (by positivity) (by positivity)
      _ = KF * ((1 + |ξ|) ^ (dF + 2) * Real.exp (-π * ξ ^ 2)) := by ring
      _ ≤ KF * ((dF + 2).factorial * Real.exp 1 * (1 + Ξ lam) ^ (dF + 2) * Real.exp (-π * Ξ lam ^ 2)) := by
          gcongr
      _ ≤ KF * ((dF + 2).factorial * Real.exp 1 * (2 * lam) ^ (dF + 2) * (Real.exp (2 * π) * E)) := by
          gcongr
      _ = C1 * lam ^ (dF + 2) * E := by simp only [C1]; ring
      _ ≤ C1 * lam ^ (dF + d + 6) * E := by
          gcongr <;> omega
  -- term 2: 𝓕g
  have t2 : ‖𝓕 (fun x => ((g (bb lam) (δ lam) x : ℝ) : ℂ)) ξ‖ ≤ C2 * lam ^ (dF + d + 6) * E / ξ ^ 2 := by
    have hsm : ∀ n : ℕ, ContDiff ℝ n (g (bb lam) (δ lam)) := fun n => contDiff_g _ _
    have hdc : ContDiff ℝ 2 (fun x => ((g (bb lam) (δ lam) x : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_g _ _)
    have hint : ∀ n : ℕ, (n : ℕ∞) ≤ (2 : ℕ∞) →
        Integrable (iteratedDeriv n (fun x => ((g (bb lam) (δ lam) x : ℝ) : ℂ))) := by
      intro n hn
      rw [iteratedDeriv_ofReal hsm]
      have hn2 : n ≤ 2 := by exact_mod_cast hn
      exact (hg lam hl n (by omega)).1.ofReal
    have key := norm_fourier_le_of_integrable hdc hint hξ0
    rw [iteratedDeriv_ofReal hsm] at key
    simp only [Complex.norm_real, Real.norm_eq_abs] at key
    refine key.trans ?_
    rw [div_le_div_iff_of_pos_right hξ2]
    have hb2 : (1 + bb lam) ^ d ≤ (2 * lam) ^ d := by gcongr; linarith [bb_ge hl]; exact one_add_bb_le hl
    have hδ4 : 1 / δ lam ^ 2 = lam ^ 4 := by rw [one_div, ← inv_pow, ← one_div, inv_δ hl]; ring
    calc (∫ x, |iteratedDeriv 2 (g (bb lam) (δ lam)) x|) / (4 * π ^ 2)
        ≤ 2 * (2 ^ 2 * A / δ lam ^ 2 * d.factorial * Real.exp 1 * (1 + bb lam) ^ d *
            Real.exp (-π * bb lam ^ 2)) / (4 * π ^ 2) := by gcongr
      _ ≤ 2 * (2 ^ 2 * A * lam ^ 4 * d.factorial * Real.exp 1 * (2 * lam) ^ d *
            (Real.exp (4 * π) * E)) / (4 * π ^ 2) := by
          rw [div_eq_mul_one_div (2 ^ 2 * A) (δ lam ^ 2), hδ4]
          gcongr; exact exp_bb_le hl
      _ = C2 * lam ^ (d + 4) * E := by simp only [C2]; ring
      _ ≤ C2 * lam ^ (dF + d + 6) * E := by gcongr <;> omega
  -- term 3: ε 𝓕ψ
  have t3 : ‖((eps lam : ℝ) : ℂ) * 𝓕 (fun x => ((Bump.psi x : ℝ) : ℂ)) ξ‖ ≤ C3 * lam ^ (dF + d + 6) * E / ξ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have he : |eps lam| ≤ 2 * (A * d.factorial * Real.exp 1 * (2 * lam) ^ d * (Real.exp (4 * π) * E)) := by
      refine (abs_integral_le_integral_abs).trans (bg0.trans ?_)
      simp only [pow_zero, div_one, one_mul]
      gcongr
      · linarith [bb_ge hl]
      · exact one_add_bb_le hl
      · exact exp_bb_le hl
    have hp : ‖𝓕 (fun x => ((Bump.psi x : ℝ) : ℂ)) ξ‖ ≤ Cψ' / ξ ^ 2 :=
      (hψ ξ hξ0).trans (by gcongr; exact le_max_left _ _)
    calc |eps lam| * ‖𝓕 (fun x => ((Bump.psi x : ℝ) : ℂ)) ξ‖
        ≤ 2 * (A * d.factorial * Real.exp 1 * (2 * lam) ^ d * (Real.exp (4 * π) * E)) * (Cψ' / ξ ^ 2) := by
          gcongr
      _ = C3 * lam ^ d * E / ξ ^ 2 := by simp only [C3]; ring
      _ ≤ C3 * lam ^ (dF + d + 6) * E / ξ ^ 2 := by
          gcongr <;> omega
  calc ‖𝓕 (fun x => ((h x : ℝ) : ℂ)) ξ - 𝓕 (fun x => ((g (bb lam) (δ lam) x : ℝ) : ℂ)) ξ +
        ((eps lam : ℝ) : ℂ) * 𝓕 (fun x => ((Bump.psi x : ℝ) : ℂ)) ξ‖
      ≤ ‖𝓕 (fun x => ((h x : ℝ) : ℂ)) ξ‖ + ‖𝓕 (fun x => ((g (bb lam) (δ lam) x : ℝ) : ℂ)) ξ‖ +
        ‖((eps lam : ℝ) : ℂ) * 𝓕 (fun x => ((Bump.psi x : ℝ) : ℂ)) ξ‖ :=
        (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
    _ ≤ C1 * lam ^ (dF + d + 6) * E / ξ ^ 2 + C2 * lam ^ (dF + d + 6) * E / ξ ^ 2 + C3 * lam ^ (dF + d + 6) * E / ξ ^ 2 := by
        gcongr
    _ = (C1 + C2 + C3) * lam ^ (dF + d + 6) * E / ξ ^ 2 := by ring

end Concrete
end RhWeil
