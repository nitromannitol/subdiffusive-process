import SubdiffusiveProcess.CoarseGrainingVocab.RestrictionIndependence
import Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm
import Homogenization.Probability.RegCoeffField.Restriction
import Homogenization.Probability.RegCoeffField.SliceMeasurability
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Topology.UniformSpace.UniformApproximation




namespace SubdiffusiveProcess.CoarseGrainingVocab

open Filter Function Homogenization MeasureTheory Metric Set Topology
open scoped Convolution

noncomputable section

variable {d : ℕ}

private def shrinkingBump (epsilon : ℝ) (hepsilon : 0 < epsilon) (n : ℕ) :
    ContDiffBump (0 : Vec d) where
  rIn := (epsilon / ((n : ℝ) + 1)) / 2
  rOut := epsilon / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have : 0 < epsilon / ((n : ℝ) + 1) := by positivity
    linarith

private theorem shrinkingBump_rOut_tendsto (epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    Tendsto (fun n : ℕ => (shrinkingBump (d := d) epsilon hepsilon n).rOut)
      atTop (nhds 0) := by
  simpa [shrinkingBump, div_eq_mul_inv] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul epsilon

private def mollifierProbe (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (n : ℕ) (x y : Vec d) : ℝ :=
  (shrinkingBump (d := d) epsilon hepsilon n).normed volume (x - y)

private theorem isProbeR_mollifierProbe (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (n : ℕ) (x : Vec d) :
    IsProbeR (mollifierProbe (d := d) epsilon hepsilon n x) := by
  let h : Vec d ≃ₜ Vec d :=
    { toFun := fun y => x - y
      invFun := fun y => x - y
      left_inv := by intro y; simp
      right_inv := by intro y; simp
      continuous_toFun := continuous_const.sub continuous_id
      continuous_invFun := continuous_const.sub continuous_id }
  have hbase : IsProbeR
      ((shrinkingBump (d := d) epsilon hepsilon n).normed volume) :=
    IsProbeR.of_smooth
      (shrinkingBump (d := d) epsilon hepsilon n).contDiff_normed
      (shrinkingBump (d := d) epsilon hepsilon n).hasCompactSupport_normed
  simpa [mollifierProbe, h] using hbase.comp_homeomorph h

private theorem support_mollifierProbe_subset_thickening
    {U : Set (Vec d)} {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (n : ℕ) {x : Vec d} (hx : x ∈ U) :
    support (mollifierProbe (d := d) epsilon hepsilon n x) ⊆
      thickening epsilon U := by
  intro y hy
  have hbump : x - y ∈ support
      ((shrinkingBump (d := d) epsilon hepsilon n).normed volume) := by
    simpa [mollifierProbe] using hy
  rw [(shrinkingBump (d := d) epsilon hepsilon n).support_normed_eq] at hbump
  have hr_le : epsilon / ((n : ℝ) + 1) ≤ epsilon := by
    rw [div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)]
    nlinarith [show 0 ≤ (n : ℝ) by positivity]
  have hyx : dist y x < epsilon := by
    apply lt_of_lt_of_le _ hr_le
    simpa [mem_ball, dist_eq_norm, norm_sub_rev] using hbump
  exact mem_thickening_iff.mpr ⟨x, hx, hyx⟩

private theorem entryTestR_mollifierProbe_eq_convolution
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (n : ℕ) (x : Vec d)
    (i j : Fin d) (a : RegCoeffField d) :
    entryTestR i j (mollifierProbe (d := d) epsilon hepsilon n x) a =
      (((shrinkingBump (d := d) epsilon hepsilon n).normed volume ⋆[
          ContinuousLinearMap.lsmul ℝ ℝ, volume]
        fun y : Vec d => a y i j) x) := by
  rw [MeasureTheory.convolution_eq_swap]
  unfold entryTestR mollifierProbe
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  ring

private theorem measurable_pullback_apply_entry_of_continuous
    {Omega : Type*} (A : Omega → RegCoeffField d)
    (hA : ∀ omega i j, Continuous (fun x : Vec d => A omega x i j))
    {U : Set (Vec d)} {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {x : Vec d} (hx : x ∈ U) (i j : Fin d) :
    @Measurable Omega ℝ
      (MeasurableSpace.comap A (LocalSigmaR (thickening epsilon U))) (borel ℝ)
      (fun omega => A omega x i j) := by
  letI : MeasurableSpace Omega :=
    MeasurableSpace.comap A (LocalSigmaR (thickening epsilon U))
  have hAmeas : @Measurable Omega (RegCoeffField d)
      (MeasurableSpace.comap A (LocalSigmaR (thickening epsilon U)))
      (LocalSigmaR (thickening epsilon U)) A :=
    Measurable.of_comap_le le_rfl
  have hprobeMeas (n : ℕ) :
      @Measurable Omega ℝ
        (MeasurableSpace.comap A (LocalSigmaR (thickening epsilon U))) (borel ℝ)
        (fun omega => entryTestR i j
          (mollifierProbe (d := d) epsilon hepsilon n x) (A omega)) :=
    (measurable_entryTestR_localSigmaR i j
      (isProbeR_mollifierProbe (d := d) epsilon hepsilon n x)
      (support_mollifierProbe_subset_thickening (d := d) hepsilon n hx)).comp hAmeas
  refine measurable_of_tendsto_metrizable hprobeMeas
    (tendsto_pi_nhds.mpr fun omega => ?_)
  rw [show (fun n => entryTestR i j
      (mollifierProbe (d := d) epsilon hepsilon n x) (A omega)) =
      fun n => (((shrinkingBump (d := d) epsilon hepsilon n).normed volume ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume]
        fun y : Vec d => A omega y i j) x) by
      funext n
      exact entryTestR_mollifierProbe_eq_convolution
        (d := d) epsilon hepsilon n x i j (A omega)]
  exact ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := volume) (shrinkingBump_rOut_tendsto (d := d) epsilon hepsilon)
    (hA omega i j) x

private theorem support_indicator_subset (U : Set (Vec d))
    (phi : Vec d → ℝ) :
    support (U.indicator phi) ⊆ U := by
  intro x hx
  by_contra hxU
  exact hx (indicator_of_notMem hxU phi)

/-- Pulling restriction information back along a samplewise continuous carrier
map loses no information after any positive thickening of the integral-local
observation set. -/
theorem comap_restrictionSigmaR_le_comap_localSigmaR_thickening
    {Omega : Type*} (A : Omega → RegCoeffField d)
    (hA : ∀ omega i j, Continuous (fun x : Vec d => A omega x i j))
    (U : Set (Vec d)) (hU : MeasurableSet U)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    MeasurableSpace.comap A (RestrictionSigmaR U hU) ≤
      MeasurableSpace.comap A (LocalSigmaR (thickening epsilon U)) := by
  let mLocal : MeasurableSpace Omega :=
    MeasurableSpace.comap A (LocalSigmaR (thickening epsilon U))
  have hAmeas : @Measurable Omega (RegCoeffField d) mLocal
      (LocalSigmaR (thickening epsilon U)) A :=
    Measurable.of_comap_le le_rfl
  have hrestrict : @Measurable Omega (RegCoeffField d) mLocal
      (inferInstance : MeasurableSpace (RegCoeffField d))
      (restrictReg U hU ∘ A) := by
    refine measurable_into_regCoeffField' ?_ ?_
    · intro x i j
      by_cases hx : x ∈ U
      · have hmeas := measurable_pullback_apply_entry_of_continuous
          (d := d) A hA hepsilon hx i j
        simpa only [Function.comp_apply,
          restrictReg_apply_entry, indicator_of_mem hx] using hmeas
      · have hzero : (fun omega => (restrictReg U hU (A omega)) x i j) =
            fun _ => (0 : ℝ) := by
          funext omega
          rw [restrictReg_apply_entry, indicator_of_notMem hx]
        change Measurable (fun omega => (restrictReg U hU (A omega)) x i j)
        rw [hzero]
        exact measurable_const
    · intro i j phi hphi
      have hsupp : support (U.indicator phi) ⊆ thickening epsilon U :=
        (support_indicator_subset U phi).trans
          (self_subset_thickening hepsilon U)
      have hmeas : @Measurable Omega ℝ mLocal (borel ℝ)
          (fun omega => entryTestR i j (U.indicator phi) (A omega)) :=
        (measurable_entryTestR_localSigmaR i j (hphi.indicator hU) hsupp).comp hAmeas
      have heq : (fun omega => entryTestR i j phi
          (restrictReg U hU (A omega))) =
          fun omega => entryTestR i j (U.indicator phi) (A omega) := by
        funext omega
        exact entryTestR_restrictReg i j phi U hU (A omega)
      change Measurable (fun omega => entryTestR i j phi
        (restrictReg U hU (A omega)))
      rw [heq]
      exact hmeas
  unfold RestrictionSigmaR
  rw [MeasurableSpace.comap_comp]
  exact hrestrict.comap_le

/-- Independence of continuous coefficient realizations on two integral-local
thickenings implies restriction independence under the pushforward law. -/
theorem indep_restrictionSigmaR_map_of_indep_localSigmaR_thickenings
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    (A : Omega → RegCoeffField d) (hAmeas : Measurable A)
    (hA : ∀ omega i j, Continuous (fun x : Vec d => A omega x i j))
    (U V : Set (Vec d)) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hlocal : ProbabilityTheory.Indep
      (MeasurableSpace.comap A (LocalSigmaR (thickening epsilon U)))
      (MeasurableSpace.comap A (LocalSigmaR (thickening epsilon V))) mu) :
    ProbabilityTheory.Indep (RestrictionSigmaR U hU)
      (RestrictionSigmaR V hV) (Measure.map A mu) := by
  have hrestrictComap : ProbabilityTheory.Indep
      (MeasurableSpace.comap A (RestrictionSigmaR U hU))
      (MeasurableSpace.comap A (RestrictionSigmaR V hV)) mu :=
    ProbabilityTheory.indep_of_indep_of_le_right
      (ProbabilityTheory.indep_of_indep_of_le_left hlocal
        (comap_restrictionSigmaR_le_comap_localSigmaR_thickening
          A hA U hU epsilon hepsilon))
      (comap_restrictionSigmaR_le_comap_localSigmaR_thickening
        A hA V hV epsilon hepsilon)
  exact (indep_comap_iff_indep_map
    hAmeas.aemeasurable (restrictionSigmaR_le U hU)
      (restrictionSigmaR_le V hV)).mp hrestrictComap

private theorem ambientNorm_le_vecNorm (v : Vec d) :
    ‖v‖ ≤ Homogenization.Book.Ch02.vecNorm v := by
  rw [pi_norm_le_iff_of_nonneg (Homogenization.Book.Ch02.vecNorm_nonneg v)]
  intro i
  simpa [Homogenization.Book.Ch02.vecNorm] using
    (PiLp.norm_apply_le
      (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d)) i)

/-- Unit separation leaves a strict Euclidean gap between two open
thickenings. -/
theorem rho_lt_vecNorm_sub_of_mem_thickenings
    {U V : Set (Vec d)} (hUV : AreUnitSeparated U V)
    {epsilon rho : ℝ} (hslack : rho + 2 * epsilon ≤ 1)
    {x y : Vec d} (hx : x ∈ thickening epsilon U)
    (hy : y ∈ thickening epsilon V) :
    rho < Homogenization.Book.Ch02.vecNorm (x - y) := by
  obtain ⟨u, huU, hxu⟩ := mem_thickening_iff.mp hx
  obtain ⟨v, hvV, hyv⟩ := mem_thickening_iff.mp hy
  have huv : 1 ≤ dist u v := hUV huU hvV
  have htriangle : dist u v ≤ dist u x + dist x y + dist y v := by
    calc
      dist u v ≤ dist u x + dist x v := dist_triangle _ _ _
      _ ≤ dist u x + (dist x y + dist y v) := by
        gcongr
        exact dist_triangle _ _ _
      _ = dist u x + dist x y + dist y v := by ring
  have hrho : rho < dist x y := by
    have hux : dist u x < epsilon := by simpa [dist_comm] using hxu
    have hyv' : dist y v < epsilon := hyv
    linarith
  exact hrho.trans_le <| by
    simpa [dist_eq_norm] using ambientNorm_le_vecNorm (d := d) (x - y)

/-- Convenient form exposing the strict slack left by two thickenings. -/
theorem one_sub_two_mul_lt_vecNorm_sub_of_mem_thickenings
    {U V : Set (Vec d)} (hUV : AreUnitSeparated U V)
    {epsilon : ℝ} {x y : Vec d}
    (hx : x ∈ thickening epsilon U) (hy : y ∈ thickening epsilon V) :
    1 - 2 * epsilon < Homogenization.Book.Ch02.vecNorm (x - y) := by
  apply rho_lt_vecNorm_sub_of_mem_thickenings hUV (epsilon := epsilon)
    (rho := 1 - 2 * epsilon) (by linarith) hx hy

end


end SubdiffusiveProcess.CoarseGrainingVocab
