module

public import SubdiffusiveProcess.Paper.inputs_simultaneous
public import SubdiffusiveProcess.Paper.s9_actual_uniqueness
public import SubdiffusiveProcess.Paper.in_killed_inverse_inprob

@[expose] public section








open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.WeightedLimitIdentification
open _root_.SubdiffusiveProcess.Paper

theorem exists_original_inverse_limits
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hInterp : CubeFractionalInterpolationInput d hd)
    (E : in_J d) (Pin : in_poincare d hd E) (X : in_extension d hd E)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) :
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
          (∃ m : ℤ, r' = (3 : ℝ) ^ m) → ∃ i, Z i = z' ∧ R i = r'),
      ∃ G : (i : ℕ) → BilateralField d →
          DomainL2 (centeredCube (Z i) (R i) (hR i)) →L[ℝ]
            DomainL2 (centeredCube (Z i) (R i) (hR i)),
        (∀ i, Measurable (G i)) ∧
        ∀ i, TendstoInMeasure (chaosSampleLaw M).toMeasure
          (fun N β => volumeResponseOperator (Sspace i)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β N (Z i) (hR i))) atTop (G i) := by
  classical
  obtain ⟨Jc, Pc, Xc, Sf, Wc, Cpc, D, hES, Step, Dbase, Interp, BD, BDQ,
    hcontract, hlifetime, EM, deltaR, Cresp, hdeltaR, hCresp, hresponses⟩ :=
    inputs_simultaneous d hd
  obtain ⟨deltaG, hdeltaG, hsupply⟩ :=
    in_killed_inverse_inprob d hd hInterp E Pin X W Cp Sob
      (s9_actual_uniqueness d hd E Pin X Sob W Cp D hES Step Dbase hInterp BD BDQ hcontract)
  refine ⟨deltaG, hdeltaG, ?_⟩
  intro M Rm Sreg It H hH hdelta Z R hR Sspace hS hrat hcomp
  obtain ⟨G, hGmeas, hbounds⟩ := hsupply M Rm Sreg It H hH hdelta
    Z R hR Sspace hS hrat hcomp
  refine ⟨G, hGmeas, ?_⟩
  intro i
  apply (SubdiffusiveProcess.Probability.tendstoInMeasure_iff_probability_bounds
    (chaosSampleLaw M).toMeasure _ (G i)).mpr
  simpa only [dist_eq_norm] using hbounds i

end SubdiffusiveProcess.WeightedLimitIdentification
