module

public import SubdiffusiveProcess.Static.ShiftedCutoffCoercivity
public import SubdiffusiveProcess.Static.AffineCoercivity
public import SubdiffusiveProcess.Static.CoercivityMoments

@[expose] public section

/-! # Finite-cutoff coercivity on fixed triadic charts -/

open MeasureTheory _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec TriadicCube
open SubdiffusiveProcess.Static SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

abbrev finiteCoercivityCoefficient {d : ℕ} (M : GMCModel d) (L m : ℕ)
    (z : Vec d) (ω : PotentialSample d) (x : Vec d) : ℝ :=
  (ahom M L)⁻¹ * aCutoff M L ω (z + (3 : ℝ) ^ m • x)

theorem cubeCoercivityEstimates_mono {d : ℕ} {A : Vec d → ℝ} {y : Vec d}
    {s K K' : ℝ} (h : cubeCoercivityEstimates A y s K) (hK : K ≤ K') :
    cubeCoercivityEstimates A y s K' := by
  exact ⟨fun H => (h.1 H).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hK) _),
    fun H => (h.2 H).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hK) _)⟩

theorem cubeCoercivityEstimates_affine {d : ℕ} (y : Vec d) {t K : ℝ}
    (ht : 0 < t) (hK : 0 ≤ K) (A : Vec d → ℝ)
    (h : cubeCoercivityEstimates (fun x => A (y + t • x)) 0 1 K) :
    cubeCoercivityEstimates A y t (K * affineCoercivityPrice d t) := by
  rw [cubeCoercivityEstimates, ← unitCube_eq_ball] at h
  exact ⟨H1_coercivity_affine y ht hK A h.1, H10_coercivity_affine y ht hK A h.2⟩

/-- A uniformly bounded gap between the cutoff and observation scale has
one measurable coercivity factor with uniformly bounded real Lp norm. -/
theorem exists_uniform_bounded_gap_coercivity (d J : ℕ) [NeZero d]
    (q : ℝ) (hq : 1 ≤ q) :
    ∃ δ0 B : ℝ, 0 < δ0 ∧ 0 < B ∧ ∀ M : GMCModel d, M.delta ≤ δ0 →
      ∀ L k : ℕ, L - k ≤ J → ∀ z : Vec d,
        ∃ K : PotentialSample d → ℝ, Measurable K ∧ (∀ ω, 1 ≤ K ω) ∧
          eLpNorm K (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal B ∧
          ∀ᵐ ω ∂M.P.toMeasure,
            cubeCoercivityEstimates (finiteCoercivityCoefficient M L k z ω) 0 1 (K ω) := by
  have h2q : 1 ≤ 2 * q := by linarith
  obtain ⟨δu, Cu, hδu, hCu, hu⟩ := exists_uniform_cutoff_unit_coercivity d (2 * q) h2q
  obtain ⟨δb, Cb, hδb, hCb, hb⟩ :=
    exists_cutoffBlockFactor_moment_bound d (2 * q) 1 h2q zero_lt_one
  let U := Cu ^ (2 * q)⁻¹
  let V := Cb * (3 : ℝ) ^ J
  refine ⟨min δu δb, U * V, lt_min hδu hδb, by dsimp only [U, V]; positivity, ?_⟩
  intro M hM L k hgap z
  obtain ⟨W, hW, hW1, hWmom, hWcoer⟩ := hu M (hM.trans (min_le_left _ _))
    (min L k) k (min_le_right _ _) z
  let F := cutoffBlockFactor M L (min L k) z
  have hF : Measurable F := measurable_cutoffBlockFactor M L (min L k) z
  have hF1 : ∀ ω, 1 ≤ F ω := one_le_cutoffBlockFactor M L (min L k) z
  have hFn : eLpNorm F (ENNReal.ofReal (2 * q)) M.P.toMeasure ≤ ENNReal.ofReal V := by
    refine (hb M (hM.trans (min_le_right _ _)) L (min L k) (min_le_left _ _) z).trans ?_
    apply ENNReal.ofReal_le_ofReal
    dsimp only [V]
    have hg : L - min L k ≤ J := by omega
    have hg' : ((L - min L k : ℕ) : ℝ) ≤ J := by exact_mod_cast hg
    simp only [one_mul]
    rw [← Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hg') hCb.le
  have hWn := coercivity_norm_of_moment M.P.toMeasure (by positivity : 0 < 2 * q)
    hCu.le (fun ω => zero_le_one.trans (hW1 ω)) hWmom
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hW.aestronglyMeasurable] at hWn
  refine ⟨fun ω => W ω * F ω, hW.mul hF,
    fun ω => one_le_mul_of_one_le_of_one_le (hW1 ω) (hF1 ω), ?_, ?_⟩
  · refine (coercivity_norm_product M.P.toMeasure (zero_lt_one.trans_le hq)
      hW.aestronglyMeasurable hF.aestronglyMeasurable).trans ?_
    exact (mul_le_mul' hWn hFn).trans_eq
      (ENNReal.ofReal_mul (Real.rpow_nonneg hCu.le _)).symm
  · filter_upwards [hWcoer] with ω hω
    have hc : cubeCoercivityEstimates
        (fun x => (ahom M (min L k))⁻¹ * aCutoff M (min L k)
          (translatePotentialSample z ω) ((3 : ℝ) ^ k • x)) 0 1 (W ω) := by
      rw [cubeCoercivityEstimates, ← unitCube_eq_ball]
      exact hω
    have hh := cutoff_unit_coercivity_with_block z ω (zero_le_one.trans (hW1 ω)) hc
    simpa only [finiteCoercivityCoefficient, aCutoff_translatePotentialSample, add_comm] using hh

/-- An affine chart whose physical side is exactly a nonnegative triadic
scale inherits the bounded-gap supplier without changing the coefficient. -/
theorem exists_cutoff_chart_coercivity {d : ℕ} (M : GMCModel d) {q B : ℝ}
    (hq : 1 ≤ q) (hB : 0 < B) {L m k : ℕ} (t : ℝ) (ht : 0 < t)
    (hscale : (3 : ℝ) ^ m * t = (3 : ℝ) ^ k) (z y : Vec d)
    (hunit : ∀ w : Vec d, ∃ K : PotentialSample d → ℝ, Measurable K ∧
      (∀ ω, 1 ≤ K ω) ∧ eLpNorm K (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal B ∧
      ∀ᵐ ω ∂M.P.toMeasure,
        cubeCoercivityEstimates (finiteCoercivityCoefficient M L k w ω) 0 1 (K ω)) :
    ∃ K : PotentialSample d → ℝ, Measurable K ∧ (∀ ω, 1 ≤ K ω) ∧
      eLpNorm K (ENNReal.ofReal q) M.P.toMeasure ≤
        ENNReal.ofReal (1 + B * affineCoercivityPrice d t) ∧
      ∀ᵐ ω ∂M.P.toMeasure,
        cubeCoercivityEstimates (finiteCoercivityCoefficient M L m z ω) y t (K ω) := by
  obtain ⟨W, hW, hW1, hWn, hWc⟩ := hunit (z + (3 : ℝ) ^ m • y)
  let T := affineCoercivityPrice d t
  have hT : 0 < T := affineCoercivityPrice_pos d ht
  refine ⟨fun ω => 1 + W ω * T, measurable_const.add (hW.mul measurable_const),
    fun ω => le_add_of_nonneg_right (mul_nonneg (zero_le_one.trans (hW1 ω)) hT.le), ?_, ?_⟩
  · refine (eLpNorm_add_le (ENNReal.one_le_ofReal.mpr hq)).trans ?_
    rw [coercivity_norm_const M.P.toMeasure (zero_lt_one.trans_le hq) zero_le_one,
      ← SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded (hW.mul_const T).aestronglyMeasurable,
      coercivity_norm_scale M.P.toMeasure q hT.le W,
      SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hW.aestronglyMeasurable,
      ENNReal.ofReal_add zero_le_one (mul_nonneg hB.le hT.le),
      ENNReal.ofReal_mul hB.le]
    exact add_le_add le_rfl (by simpa [mul_comm] using mul_le_mul_right hWn (ENNReal.ofReal T))
  · filter_upwards [hWc] with ω hω
    have heq : finiteCoercivityCoefficient M L k (z + (3 : ℝ) ^ m • y) ω =
        fun x => finiteCoercivityCoefficient M L m z ω (y + t • x) := by
      funext x
      simp only [finiteCoercivityCoefficient, smul_add, smul_smul, hscale, add_assoc]
    rw [heq] at hω
    exact cubeCoercivityEstimates_mono
      (cubeCoercivityEstimates_affine y ht (zero_le_one.trans (hW1 ω)) _ hω)
      (le_add_of_nonneg_left zero_le_one)

end SubdiffusiveProcess.Static
