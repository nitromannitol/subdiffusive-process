module

public import Mathlib
public import SubdiffusiveProcess.Paper.in_joint_extraction_inprob
public import SubdiffusiveProcess.Lnorm.CoercivityNormalization

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped Topology ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- **Catalogue clause H (`eq:mfd-1`, killed functions) from the `lem_coercivity` constants.**
The normalized `H^{3/4}` coercivity `cubeFractionalSqNorm ≤ K · a(v,v)` (the output shape of
`lem_coercivity` and of the triadic coercivity package) gives the unnormalized clause of
`conv_represented_estimates` with the catalogue constant `KH N β = |Q| · K N β` on one measurable
event of full chaos measure, and the constants keep measurability, nonnegativity and the first
moment bank (scaled by the cube volume). -/
theorem conv_represented_catalogue_coercivity_clause
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (Kc : ℕ → BilateralField d → ℝ)
    (hKcmeas : ∀ N, Measurable (Kc N)) (hKcnonneg : ∀ N β, 0 ≤ Kc N β)
    (hcoer : ∀ N, ∀ᵐ β ∂(chaosSampleLaw model).toMeasure,
      ∀ v : killedSobolevGraph (centeredCube z r hr),
        cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
            (fun _ : Fin 1 => (v : SobolevData (centeredCube z r hr)).1) < ⊤ ∧
        cubeFractionalSqNorm hd z r hr threeQuarterOrder
            (v : SobolevData (centeredCube z r hr)).1 ≤
          Kc N β * sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β N z hr)
            (v : SobolevData (centeredCube z r hr))
            (v : SobolevData (centeredCube z r hr)))
    (Cb : ℝ)
    (hbank : ∀ N, MemLp (Kc N) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ∧
      eLpNorm (Kc N) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal Cb) :
    ∃ (KH : ℕ → BilateralField d → ℝ) (B : ℝ) (G : Set (BilateralField d)),
      MeasurableSet G ∧ (chaosSampleLaw model).toMeasure Gᶜ = 0 ∧
      (∀ N, Measurable (KH N)) ∧ (∀ N β, 0 ≤ KH N β) ∧ 0 ≤ B ∧
      (∀ N, MemLp (KH N) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ∧
        eLpNorm (KH N) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≤
          ENNReal.ofReal B) ∧
      ∀ N, ∀ β ∈ G, ∀ v : S.space,
        cubeFractionalL2Seminorm hd z r hr threeQuarterOrder (fun _ : Fin 1 => v.val.1) < ⊤ ∧
        ‖v.val.1‖ ^ 2 +
            volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
              ((cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
                  (fun _ : Fin 1 => v.val.1)).toReal) ^ 2 ≤
          KH N β * responseForm S (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β N z hr) v v := by
  classical
  set P0 : Measure (BilateralField d) := (chaosSampleLaw model).toMeasure with hP0
  set V : ℝ := volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) with hV
  have hVpos : 0 < V := centeredCube_volume_pos z hr
  let good : BilateralField d → Prop := fun β => ∀ N,
    ∀ v : killedSobolevGraph (centeredCube z r hr),
      cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
          (fun _ : Fin 1 => (v : SobolevData (centeredCube z r hr)).1) < ⊤ ∧
      cubeFractionalSqNorm hd z r hr threeQuarterOrder
          (v : SobolevData (centeredCube z r hr)).1 ≤
        Kc N β * sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β N z hr)
          (v : SobolevData (centeredCube z r hr))
          (v : SobolevData (centeredCube z r hr))
  have hgood : ∀ᵐ β ∂P0, good β := ae_all_iff.2 hcoer
  let G : Set (BilateralField d) := (toMeasurable P0 {β | ¬ good β})ᶜ
  have hGm : MeasurableSet G := (measurableSet_toMeasurable _ _).compl
  have hGnull : P0 Gᶜ = 0 := by
    simp only [G, compl_compl]
    rw [measure_toMeasurable]
    exact ae_iff.1 hgood
  have hGgood : ∀ β ∈ G, good β := by
    intro β hβ
    by_contra hbad
    exact hβ (subset_toMeasurable P0 {β | ¬ good β} hbad)
  refine ⟨fun N β => V * Kc N β, V * max Cb 0, G, hGm, hGnull, fun N => (hKcmeas N).const_mul V,
    fun N β => mul_nonneg hVpos.le (hKcnonneg N β), mul_nonneg hVpos.le (le_max_right _ _),
    fun N => ?_, ?_⟩
  · refine ⟨(hbank N).1.const_mul V, ?_⟩
    calc eLpNorm (fun β => V * Kc N β) (ENNReal.ofReal 1) P0
        ≤ ‖V‖ₑ * eLpNorm (Kc N) (ENNReal.ofReal 1) P0 := by
          simpa [Pi.smul_apply, smul_eq_mul] using!
            (eLpNorm_const_smul_le (c := V) (f := Kc N) (p := ENNReal.ofReal 1) (μ := P0))
      _ ≤ ‖V‖ₑ * ENNReal.ofReal (max Cb 0) :=
          mul_le_mul_right ((hbank N).2.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))) _
      _ = ENNReal.ofReal (V * max Cb 0) := by
          rw [Real.enorm_eq_ofReal hVpos.le]
          exact (ENNReal.ofReal_mul hVpos.le).symm
  · intro N β hβ v
    have hv : (v : SobolevData (centeredCube z r hr)) ∈
        killedSobolevGraph (centeredCube z r hr) := by
      rw [← hS]; exact v.2
    have hc := hGgood β hβ N ⟨(v : SobolevData (centeredCube z r hr)), hv⟩
    refine ⟨hc.1, ?_⟩
    have h1 := SubdiffusiveProcess.Lnorm.fractional_coercivity_unnormalized hd z r hr
      (v : SobolevData (centeredCube z r hr)).1 (Kc N β)
      (sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β N z hr)
        (v : SobolevData (centeredCube z r hr)) (v : SobolevData (centeredCube z r hr))) hc.2
    simpa only [V, responseForm_apply, sobolevCoefficientForm_apply] using! h1

end SubdiffusiveProcess.Paper
