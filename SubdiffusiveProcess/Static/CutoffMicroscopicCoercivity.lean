module

public import SubdiffusiveProcess.Static.CutoffChartCoercivity
public import SubdiffusiveProcess.Static.UnweightedCoercivity
public import SubdiffusiveProcess.CoarseGrainingVocab.ACutoffP4Envelope

@[expose] public section

/-! # Coercivity at finitely many microscopic cutoff scales -/

open MeasureTheory SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec TriadicCube
open SubdiffusiveProcess.Static SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance
open scoped ENNReal BigOperators

noncomputable section
namespace SubdiffusiveProcess.Static

def boundedAffinePrice (d : ℕ) (a b : ℝ) : ℝ :=
  (b ^ ((d : ℝ) + 1 / 2) + b ^ (d + 2)) * ((a ^ d)⁻¹ + (a ^ (d + 2))⁻¹)

theorem boundedAffinePrice_pos (d : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < boundedAffinePrice d a b := by unfold boundedAffinePrice; positivity

theorem affineCoercivityPrice_le {d : ℕ} {a b s : ℝ} (ha : 0 < a)
    (has : a ≤ s) (hsb : s ≤ b) : affineCoercivityPrice d s ≤ boundedAffinePrice d a b := by
  have hs : 0 < s := ha.trans_le has
  have hb : 0 < b := hs.trans_le hsb
  unfold affineCoercivityPrice affineNormPrice boundedAffinePrice
  gcongr

/-- Physical points in a bounded origin cube remain in a fixed larger
triadic cube whenever the physical scale is bounded. -/
theorem microscopic_point_mem_cube {d : ℕ} {J m : ℕ} (hm : m ≤ J)
    {b s : ℝ} (hb : b ≤ (3 : ℝ) ^ J) (hsb : s ≤ b) {x : Vec d}
    (hx : x ∈ Metric.ball (0 : Vec d) (s / 2)) :
    (3 : ℝ) ^ m • x ∈ openCubeSet (originCube d ((2 * J : ℕ) : ℤ)) := by
  have hxnorm : ‖x‖ < s / 2 := by simpa [Metric.mem_ball, dist_zero_right] using hx
  have hp : (3 : ℝ) ^ m ≤ (3 : ℝ) ^ J := pow_le_pow_right₀ (by norm_num) hm
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hxi : |x i| ≤ ‖x‖ := norm_le_pi_norm x i
  have hscale : |((3 : ℝ) ^ m • x) i| < (3 : ℝ) ^ (2 * J) / 2 := by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 3) m)]
    calc
      (3 : ℝ) ^ m * |x i| ≤ (3 : ℝ) ^ m * ‖x‖ := by gcongr
      _ < (3 : ℝ) ^ m * (s / 2) := by gcongr
      _ ≤ (3 : ℝ) ^ J * ((3 : ℝ) ^ J / 2) := by
        exact mul_le_mul hp (by linarith [hsb.trans hb])
          (by linarith [norm_nonneg x]) (by positivity)
      _ = _ := by rw [show 2 * J = J + J by omega, pow_add]; ring
  simpa only [zpow_natCast, div_eq_mul_inv, mul_comm, neg_mul, one_mul] using abs_lt.mp hscale

private theorem expEnvelope_memLp {d : ℕ} (M : GMCModel d) (L : ℕ) (k : ℤ)
    {q : ℝ} (hq : 0 < q) :
    MemLp (fun ω => Real.exp (aCutoffCubeLogEnvelope M L k ω))
      (ENNReal.ofReal q) M.P.toMeasure := by
  have hmeas := (measurable_aCutoffCubeLogEnvelope M L k).exp
  apply (integrable_norm_rpow_iff hmeas.aestronglyMeasurable
    (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top).mp
  simpa only [ENNReal.toReal_ofReal hq.le, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), ← Real.exp_mul, mul_comm] using
    integrable_exp_mul_aCutoffCubeLogEnvelope M L k hq

def microscopicCoercivityFactor {d : ℕ} (M : GMCModel d) (J L : ℕ)
    (ω : PotentialSample d) : ℝ :=
  1 + ahom M L * Real.exp (aCutoffCubeLogEnvelope M L ((2 * J : ℕ) : ℤ) ω)

theorem measurable_microscopicCoercivityFactor {d : ℕ} (M : GMCModel d) (J L : ℕ) :
    Measurable (microscopicCoercivityFactor M J L) :=
  measurable_const.add
    (measurable_const.mul (measurable_aCutoffCubeLogEnvelope M L _).exp)

theorem one_le_microscopicCoercivityFactor {d : ℕ} (M : GMCModel d) (J L : ℕ)
    (ω : PotentialSample d) : 1 ≤ microscopicCoercivityFactor M J L ω :=
  le_add_of_nonneg_right (mul_nonneg (ahom_pos M L).le (Real.exp_pos _).le)

theorem microscopicCoercivityFactor_memLp {d : ℕ} (M : GMCModel d) (J L : ℕ)
    {q : ℝ} (hq : 0 < q) :
    MemLp (microscopicCoercivityFactor M J L) (ENNReal.ofReal q) M.P.toMeasure := by
  exact (memLp_const (1 : ℝ) (μ := M.P.toMeasure) (p := ENNReal.ofReal q)).add
    ((expEnvelope_memLp M L ((2 * J : ℕ) : ℤ) hq).const_mul (ahom M L))

def microscopicCoercivityNormBound {d : ℕ} (M : GMCModel d) (J : ℕ) (q : ℝ) : ℝ :=
  1 + ∑ L ∈ Finset.range J,
    (eLpNorm (microscopicCoercivityFactor M J L) (ENNReal.ofReal q) M.P.toMeasure).toReal

theorem microscopicCoercivityNormBound_pos {d : ℕ} (M : GMCModel d) (J : ℕ) (q : ℝ) :
    0 < microscopicCoercivityNormBound M J q :=
  add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)

theorem microscopicCoercivityFactor_norm_le {d : ℕ} (M : GMCModel d) {J L : ℕ}
    (hL : L < J) {q : ℝ} (hq : 0 < q) (z : Vec d) :
    eLpNorm (microscopicCoercivityFactor M J L ∘ translatePotentialSample z)
      (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal (microscopicCoercivityNormBound M J q) := by
  rw [eLpNorm_comp_measurePreserving (measurable_microscopicCoercivityFactor M J L).aestronglyMeasurable
    (measurePreserving_translatePotentialSample M z)]
  exact coercivity_norm_finite_bank M.P.toMeasure q (microscopicCoercivityFactor M J)
    (Finset.range J) (fun i => (microscopicCoercivityFactor_memLp M J i hq).eLpNorm_lt_top)
    (Finset.mem_range.mpr hL)

theorem microscopicCoercivityFactor_comparison {d : ℕ} (M : GMCModel d) {J m L : ℕ}
    (hm : m ≤ J) {b s : ℝ} (hb : b ≤ (3 : ℝ) ^ J) (hsb : s ≤ b)
    (z : Vec d) (ω : PotentialSample d) {x : Vec d}
    (hx : x ∈ Metric.ball (0 : Vec d) (s / 2)) :
    (1 : ℝ) ≤ microscopicCoercivityFactor M J L (translatePotentialSample z ω) *
      finiteCoercivityCoefficient M L m z ω x := by
  have hp := microscopic_point_mem_cube hm hb hsb hx
  let E := aCutoffCubeLogEnvelope M L ((2 * J : ℕ) : ℤ) (translatePotentialSample z ω)
  have haL := exp_neg_aCutoffCubeLogEnvelope_le_aCutoff M L _ (translatePotentialSample z ω) hp
  have hprod : 1 ≤ Real.exp E * aCutoff M L (translatePotentialSample z ω) ((3 : ℝ) ^ m • x) := by
    have hh := mul_le_mul_of_nonneg_left haL (Real.exp_pos E).le
    simpa only [E, ← Real.exp_add, add_neg_cancel, Real.exp_zero] using hh
  have heq : (ahom M L * Real.exp E) * finiteCoercivityCoefficient M L m z ω x =
      Real.exp E * aCutoff M L (translatePotentialSample z ω) ((3 : ℝ) ^ m • x) := by
    simp only [finiteCoercivityCoefficient, aCutoff_translatePotentialSample, add_comm]
    field_simp [(ahom_pos M L).ne']
  rw [← heq] at hprod
  refine hprod.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) ?_)
  dsimp only [finiteCoercivityCoefficient]
  exact mul_nonneg (inv_nonneg.mpr (ahom_pos M L).le) (aCutoff_pos M L ω _).le

theorem exists_bounded_unweighted_coercivity {d : ℕ} [NeZero d] (M : GMCModel d)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ U : ℝ, 0 < U ∧ ∀ s : ℝ, a ≤ s → s ≤ b →
      cubeCoercivityEstimates (fun _ : Vec d => 1) 0 s U := by
  obtain ⟨D, hD, hDc⟩ := exists_unit_unweighted_coercivity M
  refine ⟨D * boundedAffinePrice d a b,
    mul_pos hD (boundedAffinePrice_pos d ha (ha.trans_le hab)), ?_⟩
  intro s has hsb
  exact cubeCoercivityEstimates_mono
    (cubeCoercivityEstimates_affine (0 : Vec d) (ha.trans_le has) hD.le (fun _ => 1) hDc)
    (mul_le_mul_of_nonneg_left (affineCoercivityPrice_le ha has hsb) hD.le)

/-- Model-dependent finite moment constants suffice at microscopic scales. -/
theorem exists_microscopic_cube_coercivity {d : ℕ} [NeZero d] (M : GMCModel d)
    (J : ℕ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ (3 : ℝ) ^ J)
    (q : ℝ) (hq : 1 ≤ q) :
    ∃ B : ℝ, 0 < B ∧ ∀ L m : ℕ, L ≤ m → m < J →
      ∀ s : ℝ, a ≤ s → s ≤ b → ∀ z : Vec d,
        ∃ K : PotentialSample d → ℝ, Measurable K ∧ (∀ ω, 1 ≤ K ω) ∧
          eLpNorm K (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal B ∧
          ∀ᵐ ω ∂M.P.toMeasure,
            cubeCoercivityEstimates (finiteCoercivityCoefficient M L m z ω) 0 s (K ω) := by
  obtain ⟨U, hU, hUn⟩ := exists_bounded_unweighted_coercivity M a b ha hab
  let B0 := microscopicCoercivityNormBound M J q
  have hB0 : 0 < B0 := microscopicCoercivityNormBound_pos M J q
  refine ⟨1 + B0 * U, by positivity, ?_⟩
  intro L m hLm hm s has hsb z
  let G := microscopicCoercivityFactor M J L ∘ translatePotentialSample z
  have hG : Measurable G := (measurable_microscopicCoercivityFactor M J L).comp
    (measurable_translatePotentialSample z)
  have hG1 : ∀ ω, 1 ≤ G ω := fun ω => one_le_microscopicCoercivityFactor M J L _
  have hGn := microscopicCoercivityFactor_norm_le M (lt_of_le_of_lt hLm hm)
    (zero_lt_one.trans_le hq) z
  let K : PotentialSample d → ℝ := fun ω => 1 + G ω * U
  have hK : Measurable K := measurable_const.add (hG.mul measurable_const)
  have hK1 : ∀ ω, 1 ≤ K ω := fun ω => le_add_of_nonneg_right
    (mul_nonneg (zero_le_one.trans (hG1 ω)) hU.le)
  refine ⟨K, hK, hK1, ?_, Filter.Eventually.of_forall fun ω => ?_⟩
  · refine (eLpNorm_add_le (ENNReal.one_le_ofReal.mpr hq)).trans ?_
    rw [coercivity_norm_const M.P.toMeasure (zero_lt_one.trans_le hq) zero_le_one,
      ← SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded (hG.mul_const U).aestronglyMeasurable,
      coercivity_norm_scale M.P.toMeasure q hU.le G,
      SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hG.aestronglyMeasurable,
      ENNReal.ofReal_add zero_le_one (mul_nonneg hB0.le hU.le), ENNReal.ofReal_mul hB0.le]
    exact add_le_add le_rfl (by simpa [mul_comm] using mul_le_mul_right hGn (ENNReal.ofReal U))
  · exact cubeCoercivityEstimates_mono
      (cubeCoercivityEstimates_of_comparison hU.le (hG1 ω)
        (fun _ hx => microscopicCoercivityFactor_comparison M (le_of_lt hm) hb hsb z ω hx)
        (hUn s has hsb)) (by
          simpa only [K, mul_comm] using (le_add_of_nonneg_left zero_le_one : G ω * U ≤ 1 + G ω * U))

end SubdiffusiveProcess.Static
