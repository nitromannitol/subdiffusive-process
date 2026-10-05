module

public import SubdiffusiveProcess.Analysis.CubeBoundaryHardy
public import SubdiffusiveProcess.Analysis.RadialTruncatedKernel

@[expose] public section

open MeasureTheory Filter Set Homogenization _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace SubdiffusiveProcess


/-- The exterior kernel is bounded by the distance to the closest cube face. -/
theorem lintegral_cubeExterior_kernel_le {d : ℕ} (s : ℝ) (hs : 0 < s)
    {x : SpatialCoordinates d} (hx : x ∈ cubeExtensionBox d) :
    (∫⁻ y in (cubeExtensionBox d)ᶜ,
      (ENNReal.ofReal (euclideanDist x y) ^ ((d : ℝ) + 2 * s))⁻¹) ≤
        cubeInterpolationKernelMass d s * ENNReal.ofReal (cubeBoundaryDistance x) ^ (-(2 * s)) := by
  have hdelta := cubeBoundaryDistance_pos hx
  have hdist : ∀ y ∈ (cubeExtensionBox d)ᶜ, cubeBoundaryDistance x ≤ ‖x - y‖ := by
    intro y hy
    have hy' : (1 / 2 : ℝ) ≤ ‖y‖ := by
      apply le_of_not_gt
      intro hh
      apply hy
      rw [cubeExtensionBox_eq]
      change ‖y - 0‖ < 1 / 2
      simpa using hh
    have ht := norm_le_norm_add_norm_sub x y
    dsimp only [cubeBoundaryDistance]
    linarith
  calc
    _ ≤ ∫⁻ y in (cubeExtensionBox d)ᶜ,
        cubeInterpolationKernel s (cubeBoundaryDistance x) (x - y) := by
      apply setLIntegral_mono' (measurableSet_cubeExtensionBox d).compl
      intro y hy
      unfold cubeInterpolationKernel
      rw [max_eq_right (hdist y hy), ENNReal.rpow_neg]
      apply ENNReal.inv_le_inv.mpr
      exact ENNReal.rpow_le_rpow
        (ENNReal.ofReal_le_ofReal (norm_le_euclideanNorm (x - y))) (by positivity)
    _ ≤ ENNReal.ofReal (cubeBoundaryDistance x) ^ (-(2 * s)) *
        cubeInterpolationKernelMass d s :=
      lintegral_cubeInterpolationKernel_sub_le s (cubeBoundaryDistance x) hdelta _ x
    _ = _ := mul_comm _ _

/-- Whole-space energy of the literal zero extension: interior energy and two exterior terms. -/
theorem globalFractionalSqNorm_zeroExtension_le {d : ℕ} (s : ℝ) (hs : 0 < s)
    (f : SpatialCoordinates d → ℝ) (hf : Measurable f) :
    globalFractionalSqNorm s ((cubeExtensionBox d).indicator f) ≤
      (∫⁻ x in cubeExtensionBox d, ENNReal.ofReal (f x ^ 2)) +
        unitCubeFractionalEnergy s f +
          2 * cubeInterpolationKernelMass d s * cubeBoundaryWeightedIntegral s f := by
  let Q := cubeExtensionBox d
  let V := Q.indicator f
  let F : SpatialCoordinates d → ℝ≥0∞ := fun x => ENNReal.ofReal (f x ^ 2)
  let K : SpatialCoordinates d → SpatialCoordinates d → ℝ≥0∞ := cubeFractionalKernel s V
  let J : ℝ≥0∞ := ∫⁻ x in Q, ∫⁻ y in Qᶜ, K x y
  have hQ : MeasurableSet Q := measurableSet_cubeExtensionBox d
  have hV : Measurable V := hf.indicator hQ
  have hF : Measurable F := (hf.pow_const 2).ennreal_ofReal
  have hK : Measurable (Function.uncurry K) := measurable_cubeFractionalKernel s V hV
  have hKin : ∀ S : Set (SpatialCoordinates d),
      Measurable (fun x => ∫⁻ y in S, K x y) := fun _ => hK.lintegral_prod_right
  have hfull : Measurable (fun x => ∫⁻ y, K x y) := hK.lintegral_prod_right
  have hsymm : ∀ x y, K x y = K y x := by
    intro x y
    dsimp only [K, cubeFractionalKernel]
    rw [euclideanDist_comm]
    congr 1
    congr 1
    ring
  have hL2 : (∫⁻ x, ENNReal.ofReal (V x ^ 2)) = ∫⁻ x in Q, F x := by
    have he : (fun x => ENNReal.ofReal (V x ^ 2)) = Q.indicator F := by
      funext x
      by_cases hx : x ∈ Q <;> simp [V, F, hx]
    rw [he, lintegral_indicator hQ]
  have hII : (∫⁻ x in Q, ∫⁻ y in Q, K x y) = unitCubeFractionalEnergy s f := by
    apply setLIntegral_congr_fun hQ
    intro x hx
    apply setLIntegral_congr_fun hQ
    intro y hy
    simp only [K, cubeFractionalKernel, V, Set.indicator_of_mem hx, Set.indicator_of_mem hy]
  have hEE : (∫⁻ x in Qᶜ, ∫⁻ y in Qᶜ, K x y) = 0 := by
    have he : ∀ x ∈ Qᶜ, (∫⁻ y in Qᶜ, K x y) = 0 := by
      intro x hx
      calc
        _ = ∫⁻ y in Qᶜ, (0 : ℝ≥0∞) := by
          apply setLIntegral_congr_fun hQ.compl
          intro y hy
          simp only [K, cubeFractionalKernel, V,
            Set.indicator_of_notMem (show x ∉ Q from hx),
            Set.indicator_of_notMem (show y ∉ Q from hy), sub_self,
            zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero, ENNReal.zero_div]
        _ = 0 := by simp
    calc
      _ = ∫⁻ x in Qᶜ, (0 : ℝ≥0∞) := setLIntegral_congr_fun hQ.compl he
      _ = 0 := by simp
  have hEI : (∫⁻ x in Qᶜ, ∫⁻ y in Q, K x y) = J := by
    rw [lintegral_lintegral_swap hK.aemeasurable]
    apply lintegral_congr
    intro y
    apply lintegral_congr
    intro x
    exact hsymm x y
  have hG : (∫⁻ x, ∫⁻ y, K x y) = unitCubeFractionalEnergy s f + J + J := by
    rw [← lintegral_add_compl (fun x => ∫⁻ y, K x y) hQ]
    have he : ∀ x, (∫⁻ y, K x y) = (∫⁻ y in Q, K x y) + ∫⁻ y in Qᶜ, K x y :=
      fun x => (lintegral_add_compl (K x) hQ).symm
    simp_rw [he]
    rw [lintegral_add_left (hKin Q), lintegral_add_left (hKin Q), hII, hEI, hEE, add_zero]
  have hJ : J ≤ cubeInterpolationKernelMass d s * cubeBoundaryWeightedIntegral s f := by
    calc
      J = ∫⁻ x in Q, F x * ∫⁻ y in Qᶜ,
          (ENNReal.ofReal (euclideanDist x y) ^ ((d : ℝ) + 2 * s))⁻¹ := by
        apply setLIntegral_congr_fun hQ
        intro x hx
        calc
          _ = ∫⁻ y in Qᶜ, F x *
              (ENNReal.ofReal (euclideanDist x y) ^ ((d : ℝ) + 2 * s))⁻¹ := by
            apply setLIntegral_congr_fun hQ.compl
            intro y hy
            simp only [K, cubeFractionalKernel, V, Set.indicator_of_mem hx,
              Set.indicator_of_notMem hy, sub_zero, div_eq_mul_inv, F]
          _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ∫⁻ x in Q, cubeInterpolationKernelMass d s *
          (F x * ENNReal.ofReal (cubeBoundaryDistance x) ^ (-(2 * s))) := by
        apply setLIntegral_mono' hQ
        intro x hx
        calc
          _ ≤ F x * (cubeInterpolationKernelMass d s *
              ENNReal.ofReal (cubeBoundaryDistance x) ^ (-(2 * s))) :=
            mul_le_mul_of_nonneg_left (lintegral_cubeExterior_kernel_le s hs hx) (bot_le)
          _ = _ := by ac_rfl
      _ = _ := by
        have hW : Measurable (fun x : SpatialCoordinates d =>
            F x * ENNReal.ofReal (cubeBoundaryDistance x) ^ (-(2 * s))) := by
          dsimp only [F, cubeBoundaryDistance]
          fun_prop
        rw [lintegral_const_mul _ hW]
        rfl
  have hglobal : globalFractionalSqNorm s V =
      (∫⁻ x in Q, F x) + unitCubeFractionalEnergy s f + 2 * J := by
    unfold globalFractionalSqNorm
    rw [hL2]
    have he : (∫⁻ q : SpatialCoordinates d × SpatialCoordinates d,
        ENNReal.ofReal ((V q.1 - V q.2) ^ 2) /
          ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (q.1 j - q.2 j) ^ 2)) ^ ((d : ℝ) + 2 * s)) =
        ∫⁻ x, ∫⁻ y, K x y := by
      have hfun : (fun q : SpatialCoordinates d × SpatialCoordinates d =>
          ENNReal.ofReal ((V q.1 - V q.2) ^ 2) /
            ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (q.1 j - q.2 j) ^ 2)) ^ ((d : ℝ) + 2 * s)) =
          (fun q => K q.1 q.2) := by
        funext q
        simp only [K, cubeFractionalKernel, euclideanDist, euclideanNorm, vecNormSq,
          vecDot, Pi.sub_apply, pow_two]
      rw [hfun, Measure.volume_eq_prod]
      exact lintegral_prod _ hK.aemeasurable
    rw [he, hG]
    ring
  rw [hglobal]
  calc
    _ ≤ (∫⁻ x in Q, F x) + unitCubeFractionalEnergy s f +
        2 * (cubeInterpolationKernelMass d s * cubeBoundaryWeightedIntegral s f) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hJ (bot_le))
    _ = _ := by rw [mul_assoc]

end SubdiffusiveProcess
