module

public import Mathlib
public import SubdiffusiveProcess.Paper.conv_represented_thm_c1_hyp_grids
public import SubdiffusiveProcess.Paper.Support.RepresentedGridsRegular
public import SubdiffusiveProcess.Paper.conv_represented_catalogue_hdata_grids
public import SubdiffusiveProcess.Paper.model_triadic_cube_coercivity
public import SubdiffusiveProcess.Sobolev.CountableSmoothSources

@[expose] public section





open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped Topology ENNReal NNReal ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.WeightedLimitIdentification
open _root_.SubdiffusiveProcess.Paper

/-- **The expanding-catalogue represented package for the actual model.**  For the actual model with
`δ ≤ δ0`, a countable family of rational-centred triadic cubes containing every such cube, pinned
killed response spaces, and strictly increasing cutoff sequences, there are a strictly increasing `σ`, a
probability space and environments of the chaos law such that the environment-form package
`conv_represented_joint_grids` holds for the refined cutoffs `NE ∘ σ`, `NF ∘ σ`: the coercivity constants,
test sets and the whole finite-cutoff catalogue of every prefix are produced from the model (no
fixed-field boundedness, no assumed catalogue).  Dependencies: the Skorokhod representation and the
smooth test bank. -/
theorem represented_actual_grids_extra_with_ae_descent
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hInterp : CubeFractionalInterpolationInput d hd)
    (E : in_J d) (Pin : in_poincare d hd E) (X : in_extension d hd E)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (alpha eta beta t : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < d) (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (heta : 0 < eta) (hAeta : 1 + eta < 2 * alpha) (hb : 1 / 2 < beta) (hba : beta < alpha) :
    ∃ δ0 : ℝ, 0 < δ0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_hH : InfraredCharacterization M H),
        M.delta ≤ δ0 →
      ∀ (Z : ℕ → SpatialCoordinates d) (R : ℕ → ℝ) (hR : ∀ i, 0 < R i)
        (Sspace : ∀ i, ResponseSpace (centeredCube (Z i) (R i) (hR i)))
        (_hS : ∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (Z i) (R i) (hR i)))
        (_hrat : ∀ i, (∀ c : Fin d, ∃ q : ℚ, Z i c = (q : ℝ)) ∧ ∃ m : ℤ, R i = (3 : ℝ) ^ m)
        (_hcomp : ∀ (z' : SpatialCoordinates d) (r' : ℝ), (∀ c : Fin d, ∃ q : ℚ, z' c = (q : ℝ)) →
          (∃ m : ℤ, r' = (3 : ℝ) ^ m) → ∃ i, Z i = z' ∧ R i = r')
        (NE NF : ℕ → ℕ), StrictMono NE → StrictMono NF →
      ∀ {Y : Type} [Countable Y] (Zx : Y → ℕ → BilateralField d → ℝ),
        (∀ y n, Measurable (Zx y (NE n)) ∧ Measurable (Zx y (NF n))) →
        (∀ y, ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ n,
          (chaosSampleLaw M).toMeasure {β | Mb < |Zx y (NE n) β|} ≤ ENNReal.ofReal rho ∧
          (chaosSampleLaw M).toMeasure {β | Mb < |Zx y (NF n) β|} ≤ ENNReal.ofReal rho) →
      ∃ seq : ℕ → ℕ, StrictMono seq ∧
        ∃ (Ωh : Type) (_ : MeasurableSpace Ωh) (Ph : Measure Ωh) (_ : IsProbabilityMeasure Ph)
          (field : Ωh → BilateralField d) (env : ℕ → Ωh → BilateralField d)
          (GNE GNF : (i : ℕ) → ℕ → Ωh →
            DomainL2 (centeredCube (Z i) (R i) (hR i)) →L[ℝ]
              DomainL2 (centeredCube (Z i) (R i) (hR i)))
          (GE GF : (i : ℕ) → Ωh →
            DomainL2 (centeredCube (Z i) (R i) (hR i)) →L[ℝ]
              DomainL2 (centeredCube (Z i) (R i) (hR i))),
          conv_represented_joint_grids d hd M H Ωh Ph field env env Z R hR Sspace
            GNE GNF GE GF (fun n => NE (seq n)) (fun n => NF (seq n)) alpha eta E beta t ∧
          (∀ᵐ omega ∂Ph, ∀ y, ∃ ZE ZF : ℝ,
            Tendsto (fun n => Zx y (NE (seq n)) (env n omega)) atTop (𝓝 ZE) ∧
            Tendsto (fun n => Zx y (NF (seq n)) (env n omega)) atTop (𝓝 ZF)) ∧
          (∀ p : BilateralField d → Prop,
            (∀ᵐ omega ∂Ph, p (field omega)) → ∀ᵐ β ∂(chaosSampleLaw M).toMeasure, p β) := by
  obtain ⟨δ1, hδ1, hcoerc⟩ := model_triadic_cube_coercivity d hd E Pin Sob
  obtain ⟨δ2, hδ2, hdata⟩ := conv_represented_catalogue_hdata_grids d hd E Pin X W Cp Sob alpha eta beta
    t ht htd ha0 ha1 heta hAeta hb hba
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, ?_⟩
  intro M Rm Sreg It H hH hδ Z R hR Sspace hS hrat hcomp NE NF hNE hNF Y _ Zx hZxm hZxt
  have hrad : ∀ i, R i ≤ 1 ∨ ∃ k : ℕ, 0 < k ∧ R i = (3 : ℝ) ^ k := by
    intro i
    obtain ⟨m, hm⟩ := (hrat i).2
    by_cases hm0 : m ≤ 0
    · left
      rw [hm]
      exact zpow_le_one_of_nonpos₀ (by norm_num) hm0
    · right
      refine ⟨m.toNat, by omega, ?_⟩
      rw [hm, ← zpow_natCast, Int.toNat_of_nonneg (by omega)]
  obtain ⟨Kc, Cb, hCb, hmeas, hnn, hcoer, hL1, htight⟩ :=
    hcoerc M Rm H hH (hδ.trans (min_le_left _ _)) Z R hR hrad
  choose Dsub hDc hDd _ using fun i =>
    SubdiffusiveProcess.SmoothSources.exists_countable_dense_smooth_submodule (Z i) (R i) (hR i)
  let D : (i : ℕ) → Set (DomainL2 (centeredCube (Z i) (R i) (hR i))) := fun i => (Dsub i : Set _)
  have hDcount : ∀ i, Countable (D i) := fun i => (hDc i).to_subtype
  have hDadd : ∀ i, ∀ x ∈ D i, ∀ y ∈ D i, x + y ∈ D i :=
    fun i x hx y hy => (Dsub i).add_mem hx hy
  exact represented_grids_extra_with_ae_descent d hd hInterp M H hH alpha eta E beta t Z R hR Sspace hS D hDd hDadd NE NF
    hNE hNF Kc hmeas hnn hcoer
    (fun i rho hrho => (htight i rho hrho).imp fun Mb hMb n => ⟨hMb (NE n), hMb (NF n)⟩)
    (fun k => hdata M Rm Sreg It H hH (hδ.trans (min_le_right _ _)) Z R hR Sspace hS hrat hcomp
      NE NF hNE hNF k) Zx hZxm hZxt

end SubdiffusiveProcess.WeightedLimitIdentification
