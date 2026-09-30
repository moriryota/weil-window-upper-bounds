import RhWeil.TailPsi1
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# (Q1): `‖k_λ‖² ≥ c₀` for large `λ`

For `|y| ≤ η`: every term `φ((n+1)e^y)`, `n ≥ 1`, is `≥ 0` (`h ≥ 0` on `[1, ∞)`, `ψ = 0` there), so
`Σ φ((n+1)e^y) ≥ φ(e^y) = h(e^y) + ε ψ(e^y) ≥ h(1)/2 - |ε| sup ψ ≥ h(1)/4` for large `λ`.
-/

noncomputable section

namespace RhWeil
namespace Concrete

open Real MeasureTheory Set Filter Topology Cutoff Complex Polynomial GaussPoly

theorem h_eq (x : ℝ) : h x = x ^ 2 * (x ^ 2 - 3 / (2 * π)) * Real.exp (-π * x ^ 2) := by
  simp only [h, F, R, eval_sub, eval_pow, eval_X, eval_mul, eval_C]; ring

theorem c_lt_one : 3 / (2 * π) < 1 := by
  rw [div_lt_one (by positivity)]; linarith [Real.pi_gt_three]

theorem h_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ h x := by
  rw [h_eq]
  have : 3 / (2 * π) ≤ x ^ 2 := by nlinarith [c_lt_one]
  have h2 : 0 ≤ x ^ 2 - 3 / (2 * π) := by linarith
  positivity

theorem h_one_pos : 0 < h 1 := by
  rw [h_eq]
  have := c_lt_one
  have : 0 < (1:ℝ) ^ 2 - 3 / (2 * π) := by norm_num; linarith
  positivity

/-- A neighbourhood `[-η, η]` of `0` on which `h(e^y) ≥ h(1)/2`. -/
theorem exists_eta : ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 10 ∧ ∀ y, |y| ≤ η → h 1 / 2 ≤ h (Real.exp y) := by
  have hc : ContinuousAt (fun y => h (Real.exp y)) 0 :=
    ((contDiff_h (m := 0)).continuous.comp Real.continuous_exp).continuousAt
  rw [Metric.continuousAt_iff] at hc
  obtain ⟨δ₀, hδ₀, hδ⟩ := hc (h 1 / 2) (by linarith [h_one_pos])
  refine ⟨min (δ₀ / 2) (1 / 10), by positivity, min_le_right _ _, fun y hy => ?_⟩
  have hy' : dist y 0 < δ₀ := by
    rw [Real.dist_eq, sub_zero]; linarith [min_le_left (δ₀ / 2) (1 / 10)]
  have := hδ hy'
  rw [Real.dist_eq, Real.exp_zero] at this
  have := (abs_lt.1 this).1
  linarith

variable {lam : ℝ}

theorem bb_ge_114 (hl : 3 ≤ lam) : 11 / 4 ≤ bb lam := by unfold bb; linarith [δ_le hl]

theorem φR_supp (hl : 3 ≤ lam) : ∀ v, LL lam ≤ |v| → φR lam v = 0 := by
  intro v hv
  have h1 : chi (bb lam) (δ lam) v = 0 := chi_eq_zero (δ_pos hl) (by rw [← LL_eq]; exact hv)
  have h2 : Bump.psi v = 0 := Bump.psi_eq_zero ((one_le_LL hl).trans hv)
  simp [φR, h1, h2]

theorem exp_bounds {y : ℝ} (hy : |y| ≤ 1 / 10) :
    9 / 10 ≤ Real.exp y ∧ Real.exp y ≤ 11 / 4 := by
  obtain ⟨h1a, h1b⟩ := abs_le.1 hy
  constructor
  · have := Real.add_one_le_exp y; linarith
  · calc Real.exp y ≤ Real.exp 1 := Real.exp_le_exp.2 (by linarith)
      _ ≤ 11 / 4 := by have := Real.exp_one_lt_d9; linarith

theorem summable_φR (hl : 3 ≤ lam) (y : ℝ) :
    Summable fun n : ℕ => φR lam (((n : ℝ) + 1) * Real.exp y) := by
  refine summable_of_ne_finset_zero (s := Finset.range (Nat.ceil (LL lam / Real.exp y))) fun n hn => ?_
  simp only [Finset.mem_range, not_lt] at hn
  apply φR_supp hl
  have hpos := Real.exp_pos y
  rw [abs_of_nonneg (by positivity)]
  have h1 : LL lam / Real.exp y ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  rw [div_le_iff₀ hpos] at h1
  nlinarith

theorem sum_ge (hl : 3 ≤ lam) {y : ℝ} (hy : |y| ≤ 1 / 10) {M : ℝ}
    (hM : ∀ x, |Bump.psi x| ≤ M) :
    h (Real.exp y) - |eps lam| * M ≤ ∑' n : ℕ, φR lam (((n : ℝ) + 1) * Real.exp y) := by
  obtain ⟨e1, e2⟩ := exp_bounds hy
  have hs := summable_φR hl y
  rw [hs.tsum_eq_zero_add]
  have h0 : φR lam ((((0 : ℕ) : ℝ) + 1) * Real.exp y) = h (Real.exp y) + eps lam * Bump.psi (Real.exp y) := by
    have hchi : chi (bb lam) (δ lam) (Real.exp y) = 1 := by
      apply chi_eq_one (δ_pos hl)
      rw [abs_of_pos (Real.exp_pos y)]; linarith [bb_ge_114 hl]
    simp [φR, hchi]
  have hrest : 0 ≤ ∑' n : ℕ, φR lam ((((n + 1 : ℕ) : ℝ) + 1) * Real.exp y) := by
    refine tsum_nonneg fun n => ?_
    have hx : 1 ≤ (((n + 1 : ℕ) : ℝ) + 1) * Real.exp y := by
      push_cast; nlinarith [n.cast_nonneg (α := ℝ)]
    have hpsi : Bump.psi ((((n + 1 : ℕ) : ℝ) + 1) * Real.exp y) = 0 :=
      Bump.psi_eq_zero (by rw [abs_of_nonneg (by linarith)]; exact hx)
    simp only [φR, hpsi, mul_zero, add_zero]
    exact mul_nonneg (h_nonneg hx) (chi_nonneg _)
  rw [h0]
  have hb : -(|eps lam| * M) ≤ eps lam * Bump.psi (Real.exp y) := by
    have := abs_mul (eps lam) (Bump.psi (Real.exp y))
    have h2 : |eps lam * Bump.psi (Real.exp y)| ≤ |eps lam| * M := by
      rw [this]; exact mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)
    linarith [neg_abs_le (eps lam * Bump.psi (Real.exp y))]
  linarith

theorem one_le_log (hl : 3 ≤ lam) : 1 ≤ Real.log lam := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9; linarith

theorem norm_kF_ge (hl : 3 ≤ lam) {y : ℝ} (hy : |y| ≤ 1 / 10) {M : ℝ}
    (hM : ∀ x, |Bump.psi x| ≤ M) :
    Real.exp (-(1 / 20)) * (h (Real.exp y) - |eps lam| * M) ≤
      ‖Construction.kF (φ lam) (Real.log lam) (δ lam) y‖ := by
  obtain ⟨h1a, h1b⟩ := abs_le.1 hy
  have heta : Construction.eta (Real.log lam) (δ lam) y = 1 := by
    apply Construction.eta_eq_one (δ_pos hl)
    have := one_le_log hl; have := δ_le hl; linarith
  have hS := sum_ge hl hy hM
  set S := ∑' n : ℕ, φR lam (((n : ℝ) + 1) * Real.exp y)
  have heF : Construction.eF (φ lam) y = ((Real.exp (y / 2) * S : ℝ) : ℂ) := by
    simp only [Construction.eF, φ, S]
    rw [Complex.ofReal_mul, Complex.ofReal_tsum]
  rw [Construction.kF, heta, one_mul, heF, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-(1 / 20)) ≤ Real.exp (y / 2) := Real.exp_le_exp.2 (by linarith)
  set X := h (Real.exp y) - |eps lam| * M
  rcases le_or_gt X 0 with hX | hX
  · exact (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hX).trans (by positivity)
  · calc Real.exp (-(1 / 20)) * X ≤ Real.exp (y / 2) * X := by gcongr
      _ ≤ Real.exp (y / 2) * |S| := by gcongr; exact hS.trans (le_abs_self S)

/-- `|ε_λ| sup|ψ| → 0`: an explicit threshold exists. -/
theorem exists_lam_eps {M : ℝ} (hM0 : 0 ≤ M) {t : ℝ} (ht : 0 < t) :
    ∃ lam₀, 3 ≤ lam₀ ∧ ∀ lam, lam₀ ≤ lam → |eps lam| * M ≤ t := by
  obtain ⟨A, d, hA, hg⟩ := g_bounds_unif
  set Cε := 2 * (A * d.factorial * Real.exp 1 * 2 ^ d * Real.exp (4 * π))
  have hC : 0 ≤ Cε := by positivity
  have hT := ((tendsto_pow_mul_exp_neg_atTop_nhds_zero d).const_mul (Cε * M))
  rw [mul_zero] at hT
  obtain ⟨l₁, hl₁⟩ := Filter.eventually_atTop.1 (hT.eventually (Iio_mem_nhds ht))
  refine ⟨max 3 l₁, le_max_left _ _, fun lam hlam => ?_⟩
  have hl : 3 ≤ lam := (le_max_left _ _).trans hlam
  obtain ⟨_, bg0⟩ := hg lam hl 0 (by norm_num)
  simp only [iteratedDeriv_zero, pow_zero, div_one, one_mul] at bg0
  have he : |eps lam| ≤ Cε * (lam ^ d * Real.exp (-lam)) := by
    refine (abs_integral_le_integral_abs).trans (bg0.trans ?_)
    have p1 : (1 + bb lam) ^ d ≤ (2 * lam) ^ d :=
      pow_le_pow_left₀ (by linarith [bb_ge hl]) (one_add_bb_le hl) d
    have p2 : Real.exp (-π * bb lam ^ 2) ≤ Real.exp (4 * π) * Real.exp (-lam) := by
      refine (exp_bb_le hl).trans ?_
      gcongr; nlinarith [Real.pi_gt_three]
    calc 2 * (A * d.factorial * Real.exp 1 * (1 + bb lam) ^ d * Real.exp (-π * bb lam ^ 2))
        ≤ 2 * (A * d.factorial * Real.exp 1 * (2 * lam) ^ d * (Real.exp (4 * π) * Real.exp (-lam))) := by
          gcongr
      _ = Cε * (lam ^ d * Real.exp (-lam)) := by simp only [Cε]; rw [mul_pow]; ring
  have := hl₁ lam ((le_max_right _ _).trans hlam)
  calc |eps lam| * M ≤ Cε * (lam ^ d * Real.exp (-lam)) * M := by gcongr
    _ = Cε * M * (lam ^ d * Real.exp (-lam)) := by ring
    _ ≤ t := le_of_lt (by simpa using this)

theorem kF_cont_supp (hl : 3 ≤ lam) :
    Continuous (Construction.kF (φ lam) (Real.log lam) (δ lam)) ∧
    HasCompactSupport (Construction.kF (φ lam) (Real.log lam) (δ lam)) := by
  have hL : 0 ≤ LL lam := by linarith [one_le_LL hl]
  refine ⟨(Construction.contDiff_kF (a := Real.log lam) (τ := δ lam)
    (contDiff_φ lam (n := 2)) hL (φ_supp hl)).continuous, ?_⟩
  exact HasCompactSupport.intro' isCompact_Icc isClosed_Icc (fun y hy =>
    image_eq_zero_of_notMem_tsupport (fun h => hy (Construction.tsupport_kF (δ_pos hl)
      (by linarith [one_le_LL hl]) (φ_supp hl) h)))

theorem l2sq_ge_of {k : ℝ → ℂ} (hkc : Continuous k) (hks : HasCompactSupport k) {η c : ℝ}
    (hη : 0 < η) (hk : ∀ y ∈ Icc (-η) η, c ^ 2 ≤ ‖k y‖ ^ 2) :
    2 * η * c ^ 2 ≤ TheoremA.l2sq k := by
  have hs2 : HasCompactSupport (fun y => ‖k y‖ ^ 2) := by
    refine hks.mono' fun y hy => subset_tsupport k ?_
    simp only [Function.mem_support, ne_eq, pow_eq_zero_iff, OfNat.ofNat_ne_zero, not_false_eq_true,
      norm_eq_zero] at hy ⊢
    exact hy
  have hint : Integrable (fun y => ‖k y‖ ^ 2) := (hkc.norm.pow 2).integrable_of_hasCompactSupport hs2
  unfold TheoremA.l2sq
  calc 2 * η * c ^ 2 = ∫ y in Icc (-η) η, c ^ 2 := by
        rw [setIntegral_const, measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith),
          smul_eq_mul]; ring
    _ ≤ ∫ y in Icc (-η) η, ‖k y‖ ^ 2 :=
        setIntegral_mono_on (integrableOn_const (by simp)) hint.integrableOn measurableSet_Icc hk
    _ ≤ ∫ y, ‖k y‖ ^ 2 := setIntegral_le_integral hint (Filter.Eventually.of_forall fun _ => by positivity)

/-- **(Q1).** -/
theorem Q1 : ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ lam₀ : ℝ, 3 ≤ lam₀ ∧ ∀ lam, lam₀ ≤ lam →
    c₀ ≤ TheoremA.l2sq (Construction.kF (φ lam) (Real.log lam) (δ lam)) := by
  obtain ⟨η, hη, hη1, hηh⟩ := exists_eta
  obtain ⟨M, hM⟩ := Bump.hasCompactSupport_psi.exists_bound_of_continuous
    (Bump.contDiff_psi (n := 0)).continuous
  have hM' : ∀ x, |Bump.psi x| ≤ max M 0 := fun x => by
    have := hM x; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  have h1 := h_one_pos
  obtain ⟨lam₀, hl₀, hlam₀⟩ := exists_lam_eps (le_max_right M 0) (by linarith : 0 < h 1 / 4)
  have hc : 0 < Real.exp (-(1 / 20)) * (h 1 / 4) := by positivity
  refine ⟨2 * η * (Real.exp (-(1 / 20)) * (h 1 / 4)) ^ 2, by positivity, lam₀, hl₀, fun lam hlam => ?_⟩
  have hl : 3 ≤ lam := hl₀.trans hlam
  obtain ⟨hkc, hks⟩ := kF_cont_supp hl
  refine l2sq_ge_of hkc hks hη fun y hy => ?_
  have hy' : |y| ≤ η := abs_le.2 ⟨hy.1, hy.2⟩
  have b := norm_kF_ge hl (hy'.trans hη1) hM'
  have b2 := hηh y hy'
  have b3 := hlam₀ lam hlam
  have hle : Real.exp (-(1 / 20)) * (h 1 / 4) ≤
      ‖Construction.kF (φ lam) (Real.log lam) (δ lam) y‖ := by
    refine le_trans ?_ b
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  exact pow_le_pow_left₀ hc.le hle 2

end Concrete
end RhWeil
