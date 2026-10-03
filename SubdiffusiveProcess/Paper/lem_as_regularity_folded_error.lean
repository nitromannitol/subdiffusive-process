module

public import SubdiffusiveProcess.Paper.lem_repair_err_fold_paper_comparison
public import SubdiffusiveProcess.Analysis.ContinuousScalarFamily

@[expose] public section

/-! Folding a continuous positive coefficient costs only a dimensional factor
in its discounted homogenization error. The coefficient and reference are
arbitrary; no iteration stopping length or good-event hypothesis is used.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set SubdiffusiveProcess SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal BigOperators
noncomputable section
namespace Paper

/-- An almost-everywhere scalar representative on the normalized cube computes its physical error. -/
theorem aux_lem_as_regularity_folded_error_chart {d : ℕ}
    (E : in_J d) (z : SpatialCoordinates d) (R r : ℝ) (hR : 0 < R) (hr : 0 < r)
    (hrr : r ≤ R) (a : PositiveCoefficient (centeredCube z R hR))
    (f : SpatialCoordinates d → ℝ) (data : ScalarTriadicCoeffData f)
    (hrep : (fun x => a.val (fun i => z i + r * x i)) =ᵐ[
      volume.restrict (openCubeSet (originCube d 0))] f)
    (s alpha : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (ha : 0 < alpha) :
    E.err z R hR a z r alpha s 2 =
      (paperHomogenizationError (originCube d 0) 0 s
        Book.Ch02.MultiscaleExponent.infinity (Book.Ch02.MultiscaleExponent.finite 2)
        data.toTriadicCoeffFamily alpha).toReal := by
  have hinner : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      centeredCube z R hR := Metric.ball_subset_ball (by linarith only [hrr])
  have hchart (k : ℤ) (Q : Homogenization.TriadicCube d)
      (hQ : Q ∈ descendantsAtScale (originCube d 0) k) :
      Book.Ch02.CoeffOn.AEEq ((E.chart z R hR a z r).coeffOn Q)
        (data.toTriadicCoeffFamily.coeffOn Q) := by
    have hsub := openCubeSet_subset_of_mem_descendantsAtScale
      (descendant_scale_le_of_mem_descendantsAtScale hQ) hQ
    have hrepQ := ae_restrict_of_ae_restrict_of_subset hsub hrep
    have hce := E.chart_eq z R hR a z r hr hinner Q hsub
    change _ =ᵐ[volume.restrict (openCubeSet Q)] fun x => scalarMatrix (f x)
    filter_upwards [hce, hrepQ] with x hc hx
    exact hc.trans (congrArg scalarMatrix hx)
  have hpaper := aux_lem_repair_err_fold_carrier_bridge_paper_error_aeeq
    (originCube d 0) s alpha (E.chart z R hR a z r) data.toTriadicCoeffFamily hchart
  have herr := E.err_eq z R hR a z r hr hinner s hs 2 (by norm_num) alpha ha
  have herr' : E.err z R hR a z r alpha s 2 =
      (paperHomogenizationError (originCube d 0) 0 s
        Book.Ch02.MultiscaleExponent.infinity (Book.Ch02.MultiscaleExponent.finite 2)
        (E.chart z R hR a z r) alpha).toReal := by
    simpa only [paperHomogenizationError, show (2 : ℝ≥0∞) ≠ ⊤ by norm_num,
      if_false, ENNReal.toReal_ofNat] using herr
  exact herr'.trans (congrArg ENNReal.toReal hpaper)

/-- A concentric chart transports the coefficient representative to the unit cube. -/
theorem aux_lem_as_regularity_folded_error_pullback {d : ℕ}
    (z : SpatialCoordinates d) (R r : ℝ) (hR : 0 < R) (hr : 0 < r) (hrr : r ≤ R)
    (a : PositiveCoefficient (centeredCube z R hR)) (f : SpatialCoordinates d → ℝ)
    (hrep : (a.val : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] f) :
    (fun x => a.val (fun i => z i + r * x i)) =ᵐ[
      volume.restrict (openCubeSet (originCube d 0))] fun x => f (fun i => z i + r * x i) := by
  have hmp := (measurePreserving_add_left volume z).quasiMeasurePreserving.comp
    (Measure.quasiMeasurePreserving_smul volume hr.ne')
  have hmaps := aux_lem_repair_err_fold_carrier_bridge_affine_maps_root
    z r R hr hR hrr (originCube d 0) (Subset.rfl)
  have hh := (hmp.restrict hmaps).ae_eq_comp hrep
  simpa only [Function.comp_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using! hh

/-- Folding any continuous positive coefficient preserves the error bound up to the fold factor. -/
theorem lem_as_regularity_folded_error
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (z : SpatialCoordinates d) (R r : ℝ) (hR : 0 < R) (hr : 0 < r)
    (hrr : r ≤ R) (I P : Finset (Fin d))
    (a af : PositiveCoefficient (centeredCube z R hR))
    (f : SpatialCoordinates d → ℝ) (hf : Continuous f) (hfpos : ∀ x, 0 < f x)
    (hrep : (a.val : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] f)
    (hfold : (af.val : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
        fun x => a.val (coordinateFold z I P x))
    (s alpha : ℝ) (hs : 0 < s) (hs1 : s < 1 / 2) (ha : 0 < alpha) :
    E.err z R hR af z r alpha s 2 ≤
      (1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * s) - 1)) *
        E.err z R hR a z r alpha s 2 := by
  let g := fun x : SpatialCoordinates d => f (fun i => z i + r * x i)
  have hg : Continuous g := hf.comp (by fun_prop)
  have hgpos : ∀ x, 0 < g x := fun x => hfpos _
  let orig := continuousScalarFamily g hg hgpos
  let folded := continuousScalarFamily (fun x => g (coordinateFold 0 I P x))
    (hg.comp (coordinateFold_continuous 0 I P)) (fun x => hgpos _)
  have hmaps : MapsTo (coordinateFold z I P)
      (centeredCube z R hR : Set (SpatialCoordinates d))
      (centeredCube z R hR : Set (SpatialCoordinates d)) := by
    intro x hx
    change dist (coordinateFold z I P x) z < R / 2
    rw [coordinateFold_dist_center]
    exact hx
  have hfrep := hfold.trans
    (((aux_lem_repair_err_fold_carrier_bridge_fold_qmp z I P).restrict hmaps).ae_eq_comp hrep)
  have hpull := aux_lem_as_regularity_folded_error_pullback z R r hR hr hrr af
    (fun x => f (coordinateFold z I P x)) hfrep
  have hfeq : (fun x => af.val (fun i => z i + r * x i)) =ᵐ[
      volume.restrict (openCubeSet (originCube d 0))]
        fun x => g (coordinateFold 0 I P x) := by
    filter_upwards [hpull] with x hx
    exact hx.trans (congrArg f (aux_lem_repair_err_fold_carrier_bridge_fold_affine z r hr I P x))
  have hsI : s ∈ Ioc (0 : ℝ) 1 := ⟨hs, by linarith only [hs1]⟩
  rw [aux_lem_as_regularity_folded_error_chart E z R r hR hr hrr af _ folded hfeq s alpha hsI ha,
    aux_lem_as_regularity_folded_error_chart E z R r hR hr hrr a g orig
      (aux_lem_as_regularity_folded_error_pullback z R r hR hr hrr a f hrep) s alpha hsI ha]
  have hbound := lem_repair_err_fold_paper_comparison d hd s hs hs1 g alpha ha I P
    hg hgpos orig folded
  have hK : 0 ≤ 1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * s) - 1) := by
    have hden : 0 < (3 : ℝ) ^ (1 - 2 * s) - 1 :=
      sub_pos.mpr (Real.one_lt_rpow (by norm_num) (by linarith only [hs1]))
    positivity
  have hfin := ENNReal.mul_ne_top
    (ENNReal.ofReal_ne_top (r := 1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * s) - 1)))
    (scalarFamily_error_ne_top orig s alpha hs ha)
  have hh := ENNReal.toReal_mono hfin hbound
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK] using hh

end Paper
