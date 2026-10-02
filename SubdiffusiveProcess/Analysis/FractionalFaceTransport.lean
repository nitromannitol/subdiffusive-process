import SubdiffusiveProcess.Analysis.CubeFacePatch
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory Filter Set Homogenization SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace SubdiffusiveProcess


/-- The one-dimensional tail integral used after peeling the normal coordinate. -/
theorem lintegral_Ioi_ofReal_rpow_neg {s a : ℝ} (hs : 0 < s) (ha : 0 < a) :
    (∫⁻ t in Ioi a, ENNReal.ofReal t ^ (-(1 + 2 * s))) =
      (ENNReal.ofReal (2 * s))⁻¹ * ENNReal.ofReal a ^ (-(2 * s)) := by
  have hp : -(1 + 2 * s) < -1 := by linarith
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi a)] fun t : ℝ => t ^ (-(1 + 2 * s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (ha.trans ht).le _
  have hbridge := ofReal_integral_eq_lintegral_ofReal
    (integrableOn_Ioi_rpow_of_lt hp ha) hnonneg
  calc
    _ = ∫⁻ t in Ioi a, ENNReal.ofReal (t ^ (-(1 + 2 * s))) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact ENNReal.ofReal_rpow_of_pos (ha.trans ht)
    _ = ENNReal.ofReal (∫ t in Ioi a, t ^ (-(1 + 2 * s))) := hbridge.symm
    _ = _ := by
      rw [integral_Ioi_rpow_of_lt hp ha]
      have he : -(1 + 2 * s) + 1 = -(2 * s) := by ring
      rw [he, neg_div_neg_eq, div_eq_mul_inv, ENNReal.ofReal_mul
        (Real.rpow_nonneg ha.le _), ENNReal.ofReal_inv_of_pos (by positivity),
        ← ENNReal.ofReal_rpow_of_pos ha]
      exact mul_comm _ _

/-- The incoming mass of the asymmetric face patches. -/
def cubeFaceIncomingMass {d : ℕ} (s lam : ℝ) (upper : Bool) (i : Fin d)
    (y : SpatialCoordinates d) : ℝ≥0∞ :=
  ∫⁻ x in cubeExtensionBox d,
    if y ∈ cubeFacePatch lam upper i x then
      ENNReal.ofReal (cubeFaceDistance upper i x) ^ (-((d : ℝ) + 2 * s)) else 0

theorem cubeFaceIncomingMass_le {d : ℕ} (hd : 0 < d) (s lam : ℝ) (hs : 0 < s)
    (hlam : 0 < lam) (upper : Bool) (i : Fin d) {y : SpatialCoordinates d}
    (hy : y ∈ cubeExtensionBox d) :
    cubeFaceIncomingMass s lam upper i y ≤
      (2 : ℝ≥0∞) ^ (d - 1) * (ENNReal.ofReal (2 * s))⁻¹ *
        ENNReal.ofReal lam ^ (2 * s) * cubeFaceWeight s upper i y := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  let G : SpatialCoordinates (n + 1) → ℝ≥0∞ := fun x =>
    if y ∈ cubeFacePatch lam upper i x then
      ENNReal.ofReal (cubeFaceDistance upper i x) ^ (-((n + 1 : ℕ) + 2 * s)) else 0
  have hrel : MeasurableSet {x : SpatialCoordinates (n + 1) |
      y ∈ cubeFacePatch lam upper i x} :=
    (measurableSet_cubeFacePatch_relation lam upper i).preimage
      (measurable_id.prodMk measurable_const)
  have hG : Measurable G := Measurable.ite hrel
    (((continuous_cubeFaceDistance upper i).measurable.ennreal_ofReal).pow_const _) measurable_const
  have hslice : Measurable (fun p : ℝ × SpatialCoordinates n =>
      G (cubeFaceInsert upper i p.1 p.2)) :=
    hG.comp (continuous_cubeFaceInsert upper i).measurable
  let a := cubeFaceDistance upper i y / lam
  have hdelta := (cubeFaceDistance_pos_lt_one upper i hy).1
  have ha : 0 < a := div_pos hdelta hlam
  have hinner : ∀ t ∈ Ioo (0 : ℝ) 1,
      (∫⁻ z in cubeExtensionBox n, G (cubeFaceInsert upper i t z)) ≤
        (Ioi a).indicator
          (fun u : ℝ => (2 : ℝ≥0∞) ^ n * ENNReal.ofReal u ^ (-(1 + 2 * s))) t := by
    intro t ht
    by_cases hat : a < t
    · rw [Set.indicator_of_mem (show t ∈ Ioi a from hat)]
      let A := ENNReal.ofReal t ^ (-((n + 1 : ℕ) + 2 * s))
      let S : Set (SpatialCoordinates n) :=
        {z | y ∈ cubeFacePatch lam upper i (cubeFaceInsert upper i t z)}
      have hS : MeasurableSet S := hrel.preimage
        ((continuous_cubeFaceInsert upper i).comp
          (continuous_const.prodMk continuous_id)).measurable
      have heq : (∫⁻ z in cubeExtensionBox n, G (cubeFaceInsert upper i t z)) =
          A * volume {z : SpatialCoordinates n | z ∈ cubeExtensionBox n ∧ z ∈ S} := by
        simp only [G, cubeFaceDistance_insert]
        change (∫⁻ z in cubeExtensionBox n, S.indicator (fun _ => A) z) = _
        rw [lintegral_indicator hS]
        simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply,
          univ_inter, Set.setOf_and, Set.setOf_mem_eq, smul_eq_mul]
        rw [Measure.restrict_apply hS, Set.inter_comm]
      rw [heq]
      calc
        _ ≤ A * ENNReal.ofReal ((2 * t) ^ n) :=
          mul_le_mul_of_nonneg_left (volume_cubeFacePatch_incoming_slice_le
            lam upper i y t ht.1) (zero_le _)
        _ = (2 : ℝ≥0∞) ^ n * ENNReal.ofReal t ^ (-(1 + 2 * s)) := by
          dsimp only [A]
          rw [ENNReal.ofReal_pow (mul_nonneg (by norm_num) ht.1.le), ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_ofNat, mul_pow]
          rw [mul_comm, mul_assoc, ← ENNReal.rpow_natCast (ENNReal.ofReal t) n,
            ← ENNReal.rpow_add _ _ (ENNReal.ofReal_ne_zero_iff.mpr ht.1)
              ENNReal.ofReal_ne_top]
          congr 2
          push_cast
          ring
    · rw [Set.indicator_of_notMem (show t ∉ Ioi a from hat)]
      have hz : ∀ z, G (cubeFaceInsert upper i t z) = 0 := by
        intro z
        have hnot : y ∉ cubeFacePatch lam upper i (cubeFaceInsert upper i t z) := by
          intro hm
          have hn := (cubeFacePatch_normal_condition lam upper i hm).2
          rw [cubeFaceDistance_insert] at hn
          exact hat ((div_lt_iff₀ hlam).mpr (by simpa only [mul_comm] using hn))
        simp [G, hnot]
      simp_rw [hz]
      simp
  calc
    cubeFaceIncomingMass s lam upper i y =
        ∫⁻ t in Ioo (0 : ℝ) 1, ∫⁻ z in cubeExtensionBox n,
          G (cubeFaceInsert upper i t z) := by
      rw [cubeFaceIncomingMass, setLIntegral_cubeFaceCoordinates upper i G hG]
      exact (lintegral_lintegral_swap (hslice.comp measurable_swap).aemeasurable)
    _ ≤ ∫⁻ t in Ioo (0 : ℝ) 1, (Ioi a).indicator
          (fun u : ℝ => (2 : ℝ≥0∞) ^ n * ENNReal.ofReal u ^ (-(1 + 2 * s))) t :=
      setLIntegral_mono' measurableSet_Ioo hinner
    _ ≤ ∫⁻ t : ℝ, (Ioi a).indicator
          (fun u : ℝ => (2 : ℝ≥0∞) ^ n * ENNReal.ofReal u ^ (-(1 + 2 * s))) t :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = (2 : ℝ≥0∞) ^ n * ((ENNReal.ofReal (2 * s))⁻¹ *
        ENNReal.ofReal a ^ (-(2 * s))) := by
      rw [lintegral_indicator measurableSet_Ioi,
        lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofNat_ne_top),
        lintegral_Ioi_ofReal_rpow_neg hs ha]
    _ = _ := by
      dsimp only [a, cubeFaceWeight]
      rw [ENNReal.ofReal_div_of_pos hlam, div_eq_mul_inv,
        ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top
          (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hlam)),
        ENNReal.inv_rpow, ENNReal.rpow_neg (ENNReal.ofReal lam), inv_inv]
      ac_rfl

theorem double_lintegral_cubeFacePatch_mass_le {d : ℕ} (hd : 0 < d) (s lam : ℝ)
    (hs : 0 < s) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (upper : Bool) (i : Fin d)
    (f : SpatialCoordinates d → ℝ) (hf : Measurable f) :
    (∫⁻ x in cubeExtensionBox d,
      ENNReal.ofReal (cubeFaceDistance upper i x) ^ (-((d : ℝ) + 2 * s)) *
        ∫⁻ y in cubeFacePatch lam upper i x, ENNReal.ofReal (f y ^ 2)) ≤
      (2 : ℝ≥0∞) ^ (d - 1) * (ENNReal.ofReal (2 * s))⁻¹ *
        ENNReal.ofReal lam ^ (2 * s) * cubeFaceWeightedIntegral s upper i f := by
  let Q := cubeExtensionBox d
  let A : SpatialCoordinates d → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (cubeFaceDistance upper i x) ^ (-((d : ℝ) + 2 * s))
  let F : SpatialCoordinates d → ℝ≥0∞ := fun y => ENNReal.ofReal (f y ^ 2)
  let K : SpatialCoordinates d → SpatialCoordinates d → ℝ≥0∞ := fun x y =>
    if y ∈ cubeFacePatch lam upper i x then A x * F y else 0
  let C := (2 : ℝ≥0∞) ^ (d - 1) * (ENNReal.ofReal (2 * s))⁻¹ * ENNReal.ofReal lam ^ (2 * s)
  have hA : Measurable A :=
    ((continuous_cubeFaceDistance upper i).measurable.ennreal_ofReal).pow_const _
  have hF : Measurable F := (hf.pow_const 2).ennreal_ofReal
  have hK : Measurable (Function.uncurry K) :=
    Measurable.ite (measurableSet_cubeFacePatch_relation lam upper i)
      ((hA.comp measurable_fst).mul (hF.comp measurable_snd)) measurable_const
  have hinner : ∀ x ∈ Q,
      A x * (∫⁻ y in cubeFacePatch lam upper i x, F y) = ∫⁻ y in Q, K x y := by
    intro x hx
    have hP := measurableSet_cubeFacePatch lam upper i x
    have hsub := cubeFacePatch_subset lam hlam0 hlam1 upper i hx
    calc
      _ = ∫⁻ y in cubeFacePatch lam upper i x, A x * F y :=
        (lintegral_const_mul _ hF).symm
      _ = ∫⁻ y in Q, (cubeFacePatch lam upper i x).indicator (fun y => A x * F y) y := by
        rw [lintegral_indicator hP, Measure.restrict_restrict_of_subset hsub]
      _ = _ := by simp only [K, Set.indicator_apply]
  have hincoming : ∀ y,
      (∫⁻ x in Q, K x y) = F y * cubeFaceIncomingMass s lam upper i y := by
    intro y
    calc
      _ = ∫⁻ x in Q, F y * (if y ∈ cubeFacePatch lam upper i x then A x else 0) := by
        apply lintegral_congr
        intro x
        dsimp only [K]
        split_ifs <;> simp [mul_comm]
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rfl
  calc
    _ = ∫⁻ x in Q, ∫⁻ y in Q, K x y :=
      setLIntegral_congr_fun (measurableSet_cubeExtensionBox d) hinner
    _ = ∫⁻ y in Q, ∫⁻ x in Q, K x y := lintegral_lintegral_swap hK.aemeasurable
    _ = ∫⁻ y in Q, F y * cubeFaceIncomingMass s lam upper i y :=
      lintegral_congr hincoming
    _ ≤ ∫⁻ y in Q, C * (F y * cubeFaceWeight s upper i y) := by
      apply setLIntegral_mono' (measurableSet_cubeExtensionBox d)
      intro y hy
      have h := cubeFaceIncomingMass_le hd s lam hs hlam0 upper i hy
      calc
        _ ≤ F y * (C * cubeFaceWeight s upper i y) :=
          mul_le_mul_of_nonneg_left h (zero_le _)
        _ = _ := by ac_rfl
    _ = _ := by
      rw [lintegral_const_mul _ (hF.mul (measurable_cubeFaceWeight s upper i))]
      rfl

end SubdiffusiveProcess
