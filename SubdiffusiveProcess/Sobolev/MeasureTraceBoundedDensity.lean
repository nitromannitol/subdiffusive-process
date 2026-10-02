import SubdiffusiveProcess.Main.MeasureTrace
import SubdiffusiveProcess.Sobolev.MeasureTraceSmoothDensity
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open MeasureTheory Set TopologicalSpace
open scoped ENNReal ContDiff
noncomputable section
namespace SubdiffusiveProcess

open Filter in
theorem measureTrace_eq_toLp_of_bounded_density
    {d : ℕ} (hd : 2 ≤ d) (Q : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Q)
    (ν : Measure (SpatialCoordinates d)) (K C D : ℝ)
    (T : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder → Lp ℝ 2 ν)
    (hT : MeasureTraceCharacterization hd Q hr ν K C T)
    (hD : 0 ≤ D)
    (hνle : ν ≤ ENNReal.ofReal D •
      volume.restrict (centeredCube (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr : Set (SpatialCoordinates d))) :
    ∀ u : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder,
      MemLp (u.val 0) 2 ν ∧
        ∀ hu : MemLp (u.val 0) 2 ν, T u = hu.toLp (u.val 0) := by
  classical
  let z := Homogenization.cubeCenter Q
  let r := Homogenization.cubeScaleFactor Q
  let U : Set (SpatialCoordinates d) := (centeredCube z r hr : Set (SpatialCoordinates d))
  have hDfin : ENNReal.ofReal D ≠ ⊤ := ENNReal.ofReal_ne_top
  have hνle' : ν ≤ ENNReal.ofReal D • volume.restrict U := hνle
  have hUmeas : MeasurableSet U := (centeredCube z r hr).isOpen.measurableSet
  have hUvol : volume U = ENNReal.ofReal (r ^ d) := centeredCube_volume z hr
  have hUvolfin : volume U < ⊤ := by rw [hUvol]; exact ENNReal.ofReal_lt_top
  have hUeqOpen : U = Homogenization.openCubeSet Q := centeredCube_eq_openCubeSet Q hr
  -- IsFiniteMeasure ν
  have hνuniv : ν Set.univ ≤ ENNReal.ofReal D * volume U := by
    have h1 := Measure.le_iff'.mp hνle' Set.univ
    simpa [Measure.smul_apply, Measure.restrict_apply_univ] using h1
  have hνtop : ν Set.univ < ⊤ :=
    lt_of_le_of_lt hνuniv (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top hDfin hUvolfin.ne))
  haveI : IsFiniteMeasure ν := ⟨hνtop⟩
  -- support of ν
  have hUsubClosure : U ⊆ closure (Homogenization.openCubeSet Q) := by
    rw [hUeqOpen]; exact subset_closure
  have hsupp : ν (closure (Homogenization.openCubeSet Q))ᶜ = 0 := by
    have hsub : (closure (Homogenization.openCubeSet Q))ᶜ ⊆ Uᶜ :=
      compl_subset_compl.mpr hUsubClosure
    have h1 : ν (closure (Homogenization.openCubeSet Q))ᶜ ≤ ν Uᶜ := measure_mono hsub
    have h2 : ν Uᶜ ≤ (ENNReal.ofReal D • volume.restrict U) Uᶜ := Measure.le_iff'.mp hνle' Uᶜ
    have h3 : (ENNReal.ofReal D • volume.restrict U) Uᶜ = 0 := by
      rw [Measure.smul_apply, Measure.restrict_apply' hUmeas]
      simp
    have h4 : ν Uᶜ = 0 := le_antisymm (h2.trans_eq h3) (zero_le _)
    exact le_antisymm (h1.trans h4.le) (zero_le _)
  intro u
  have hUmemLp : MemLp (u.val 0 : SpatialCoordinates d → ℝ) 2 (volume.restrict U) :=
    Lp.memLp (u.val 0)
  have hmemLp : MemLp (u.val 0) 2 ν := MemLp.of_measure_le_smul hDfin hνle' hUmemLp
  refine ⟨hmemLp, ?_⟩
  intro hu
  obtain ⟨a, fSmooth, w, hfcont, hfmem, haeq, hweq, hwlim⟩ :=
    measureTrace_hdense_of_finiteMeasure_supported hd Q hr ν hsupp u
  -- T ∘ a agrees with the smooth-density trace
  have hTa : ∀ n, T (a n) = (hfmem n).toLp (fSmooth n) := fun n =>
    hT.2.2 (fSmooth n) (hfcont n) (a n) (haeq n) (hfmem n)
  -- T u is the limit of T (a n), via the exact Lipschitz bound
  let A : ℝ := C * (K + (ν (closure (Homogenization.openCubeSet Q))).toReal)
  have hsq : ∀ n, ‖T u - T (a n)‖ ^ 2 ≤
      A * (cubeFractionalL2Norm hd z r hr halfFractionalOrder (w n)) ^ 2 :=
    fun n => hT.2.1 u (a n) (w n) (hweq n)
  have harg : Tendsto (fun n => A * (cubeFractionalL2Norm hd z r hr halfFractionalOrder (w n)) ^ 2)
      atTop (nhds 0) := by
    have hpow := hwlim.pow 2
    have hmul := hpow.const_mul A
    simpa using hmul
  have hsqrt : Tendsto (fun n => Real.sqrt
      (A * (cubeFractionalL2Norm hd z r hr halfFractionalOrder (w n)) ^ 2)) atTop (nhds 0) := by
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp harg
    simpa using hs
  have hTutend : Tendsto (fun n => ‖T u - T (a n)‖) atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun n => norm_nonneg _
    · exact Filter.Eventually.of_forall fun n => Real.le_sqrt_of_sq_le (hsq n)
    · exact hsqrt
  have hTutend' : Tendsto (fun n => ‖T (a n) - T u‖) atTop (nhds 0) := by
    have hfe : (fun n => ‖T (a n) - T u‖) = fun n => ‖T u - T (a n)‖ :=
      funext (fun n => norm_sub_rev _ _)
    rw [hfe]; exact hTutend
  have hTseq : Tendsto (fun n => T (a n)) atTop (nhds (T u)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hTutend'
  -- extract ‖(w n).val 0‖ → 0 from the inhomogeneous cube-norm limit
  have hknonneg : 0 ≤ r ^ (-(halfFractionalOrder : ℝ)) /
      Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    div_nonneg (Real.rpow_nonneg hr.le _) (Real.sqrt_nonneg _)
  have hkpos : 0 < r ^ (-(halfFractionalOrder : ℝ)) /
      Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    div_pos (Real.rpow_pos_of_pos hr _) (Real.sqrt_pos.mpr (centeredCube_volume_pos z hr))
  have hcubeeq : ∀ n, cubeFractionalL2Norm hd z r hr halfFractionalOrder (w n) =
      (cubeFractionalL2Seminorm hd z r hr halfFractionalOrder (w n).val).toReal +
        (r ^ (-(halfFractionalOrder : ℝ)) /
          Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) *
          ‖(w n).val 0‖ := by
    intro n
    unfold cubeFractionalL2Norm
    rw [Fin.sum_univ_one, Real.sqrt_sq (norm_nonneg _)]
    ring
  have hterm2nonneg : ∀ n, 0 ≤ (r ^ (-(halfFractionalOrder : ℝ)) /
      Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) *
      ‖(w n).val 0‖ := fun n => mul_nonneg hknonneg (norm_nonneg _)
  have hterm2le : ∀ n, (r ^ (-(halfFractionalOrder : ℝ)) /
      Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) *
      ‖(w n).val 0‖ ≤ cubeFractionalL2Norm hd z r hr halfFractionalOrder (w n) := by
    intro n
    rw [hcubeeq n]
    exact le_add_of_nonneg_left ENNReal.toReal_nonneg
  have hterm2 : Tendsto (fun n => (r ^ (-(halfFractionalOrder : ℝ)) /
      Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) *
      ‖(w n).val 0‖) atTop (nhds 0) := squeeze_zero hterm2nonneg hterm2le hwlim
  have htends0 : Tendsto (fun n => ‖(w n).val 0‖) atTop (nhds 0) := by
    have hκne : (r ^ (-(halfFractionalOrder : ℝ)) /
        Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) ≠ 0 :=
      hkpos.ne'
    have hinv := hterm2.const_mul (r ^ (-(halfFractionalOrder : ℝ)) /
        Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))))⁻¹
    simp only [mul_zero] at hinv
    have hfe : (fun n => (r ^ (-(halfFractionalOrder : ℝ)) /
        Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))))⁻¹ *
        ((r ^ (-(halfFractionalOrder : ℝ)) /
          Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) *
          ‖(w n).val 0‖)) = fun n => ‖(w n).val 0‖ :=
      funext (fun n => by rw [← mul_assoc, inv_mul_cancel₀ hκne, one_mul])
    rwa [hfe] at hinv
  -- relate (w n).val 0 to the smooth-density difference on U
  have hcoe : ∀ n, (⇑((w n).val 0) : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict U]
      (fun x => u.val 0 x - fSmooth n x) := by
    intro n
    rw [hweq n]
    filter_upwards [Lp.coeFn_sub (u.val 0) ((a n).val 0), haeq n] with x hx hxa
    calc (u.val 0 - (a n).val 0) x
        = u.val 0 x - (a n).val 0 x := hx
      _ = u.val 0 x - fSmooth n x := by rw [hxa]
  have hnormeq : ∀ n, ‖(w n).val 0‖ =
      (eLpNorm (⇑((w n).val 0)) 2 (volume.restrict U)).toReal := by
    intro n; rw [Lp.norm_def]
  have hEUeq : ∀ n, eLpNorm (⇑((w n).val 0)) 2 (volume.restrict U) =
      eLpNorm (fun x => fSmooth n x - u.val 0 x) 2 (volume.restrict U) := by
    intro n
    rw [eLpNorm_congr_ae (hcoe n)]
    have hneg : (fun x => u.val 0 x - fSmooth n x) = -(fun x => fSmooth n x - u.val 0 x) :=
      funext (fun x => (neg_sub _ _).symm)
    rw [hneg, eLpNorm_neg]
  have hEUtends : Tendsto (fun n =>
      (eLpNorm (fun x => fSmooth n x - u.val 0 x) 2 (volume.restrict U)).toReal)
      atTop (nhds 0) := by
    have hfe : (fun n => (eLpNorm (fun x => fSmooth n x - u.val 0 x) 2 (volume.restrict U)).toReal) =
        fun n => ‖(w n).val 0‖ := funext (fun n => by rw [hnormeq n, hEUeq n])
    rw [hfe]; exact htends0
  -- bound the ν-side eLpNorm by the U-side eLpNorm and squeeze to 0
  have hp2 : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hκfin : (ENNReal.ofReal D) ^ (1 / (2 : ℝ≥0∞)).toReal ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hDfin
  have hEUfin : ∀ n, eLpNorm (fun x => fSmooth n x - u.val 0 x) 2 (volume.restrict U) ≠ ⊤ := by
    intro n
    rw [← hEUeq n]
    exact (Lp.memLp ((w n).val 0)).2.ne
  have hboundtop : ∀ n, (ENNReal.ofReal D) ^ (1 / (2 : ℝ≥0∞)).toReal *
      eLpNorm (fun x => fSmooth n x - u.val 0 x) 2 (volume.restrict U) ≠ ⊤ :=
    fun n => ENNReal.mul_ne_top hκfin (hEUfin n)
  have hνbound : ∀ n, eLpNorm (fun x => fSmooth n x - u.val 0 x) 2 ν ≤
      (ENNReal.ofReal D) ^ (1 / (2 : ℝ≥0∞)).toReal *
        eLpNorm (fun x => fSmooth n x - u.val 0 x) 2 (volume.restrict U) := by
    intro n
    calc eLpNorm (fun x => fSmooth n x - u.val 0 x) 2 ν ≤
          eLpNorm (fun x => fSmooth n x - u.val 0 x) 2 (ENNReal.ofReal D • volume.restrict U) :=
        eLpNorm_mono_measure _ hνle'
      _ = (ENNReal.ofReal D) ^ (1 / (2 : ℝ≥0∞)).toReal *
          eLpNorm (fun x => fSmooth n x - u.val 0 x) 2 (volume.restrict U) := by
        rw [eLpNorm_smul_measure_of_ne_top hp2]; rfl
  have hνrealbound : ∀ n, (eLpNorm (fun x => fSmooth n x - u.val 0 x) 2 ν).toReal ≤
      ((ENNReal.ofReal D) ^ (1 / (2 : ℝ≥0∞)).toReal).toReal *
        (eLpNorm (fun x => fSmooth n x - u.val 0 x) 2 (volume.restrict U)).toReal := by
    intro n
    rw [← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (hboundtop n) (hνbound n)
  have hνrealtends : Tendsto (fun n =>
      (eLpNorm (fun x => fSmooth n x - u.val 0 x) 2 ν).toReal) atTop (nhds 0) := by
    have hupper : Tendsto (fun n =>
        ((ENNReal.ofReal D) ^ (1 / (2 : ℝ≥0∞)).toReal).toReal *
          (eLpNorm (fun x => fSmooth n x - u.val 0 x) 2 (volume.restrict U)).toReal)
        atTop (nhds 0) := by
      have := hEUtends.const_mul (((ENNReal.ofReal D) ^ (1 / (2 : ℝ≥0∞)).toReal).toReal)
      simpa using this
    exact squeeze_zero (fun n => ENNReal.toReal_nonneg) hνrealbound hupper
  have hνfin : ∀ n, eLpNorm (fun x => fSmooth n x - u.val 0 x) 2 ν ≠ ⊤ :=
    fun n => ne_top_of_le_ne_top (hboundtop n) (hνbound n)
  have hνtends : Tendsto (fun n => eLpNorm (fun x => fSmooth n x - u.val 0 x) 2 ν)
      atTop (nhds 0) := by
    have hfe : (fun n => eLpNorm (fun x => fSmooth n x - u.val 0 x) 2 ν) =
        fun n => ENNReal.ofReal (eLpNorm (fun x => fSmooth n x - u.val 0 x) 2 ν).toReal :=
      funext (fun n => (ENNReal.ofReal_toReal (hνfin n)).symm)
    rw [hfe]
    have hc := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hνrealtends
    simpa using hc
  -- assemble the source-side limit and conclude by uniqueness of limits
  have hsource : Tendsto (fun n => (hfmem n).toLp (fSmooth n)) atTop
      (nhds (hu.toLp (u.val 0))) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' fSmooth hfmem (u.val 0 : SpatialCoordinates d → ℝ) hu).mpr
      hνtends
  have hsource' : Tendsto (fun n => T (a n)) atTop (nhds (hu.toLp (u.val 0))) := by
    have hfe : (fun n => T (a n)) = fun n => (hfmem n).toLp (fSmooth n) := funext hTa
    rw [hfe]; exact hsource
  exact tendsto_nhds_unique hTseq hsource'


end SubdiffusiveProcess
