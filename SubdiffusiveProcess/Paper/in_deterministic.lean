module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.ResponseMoments.Subdivision
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.EllipticRegularity.InDetCampanatoHolder
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.deterministic_iteration_input
public import SubdiffusiveProcess.Paper.primitive_scores
public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import SubdiffusiveProcess.Paper.deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.obl_ramp
public import SubdiffusiveProcess.Paper.in_deterministic_equal_scale_b12
public import SubdiffusiveProcess.Paper.in_deterministic_good_scale_transfer
public import SubdiffusiveProcess.Paper.in_deterministic_budget_assembly
public import SubdiffusiveProcess.Paper.in_deterministic_matrix_bounds
public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Paper.lem_primitive
public import SubdiffusiveProcess.Paper.coherent_score_attachment
public import SubdiffusiveProcess.Paper.in_deterministic_budget_transfer
public import Homogenization.Book.Ch02.Matrices
public import Homogenization.Book.Ch02.MultiscaleEllipticity
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import SubdiffusiveProcess.Paper.good_event
public import SubdiffusiveProcess.Paper.cell_catalogue
public import SubdiffusiveProcess.Paper.physical_scale_dictionary
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import SubdiffusiveProcess.Paper.lem_finite_trace_holder_beta_bound
public import SubdiffusiveProcess.VariationalResponses.CellAssembly
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Convolution
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import SubdiffusiveProcess.EllipticRegularity.InDetContHalf
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.PhysicalDatumRegularity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.DilationWeakEquation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.PhysicalDirichletCarrier
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsCellTransport
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.Corrector
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.AffineHarmonic
public import SubdiffusiveProcess.CoarseGrainingVocab.DirichletUniqueness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumRepresentative
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.Carrier
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SmallContrastBallRescaling
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.PositiveRescaling
public import SubdiffusiveProcess.Sobolev.NativeH10
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FlatComparatorTransport
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FractionalTransport
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FractionalDatum
public import SubdiffusiveProcess.EllipticRegularity.InDetIterationWindow
public import SubdiffusiveProcess.Paper.prop_folded_iteration
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Data.Int.Interval
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SparseLayerReduction
public import SubdiffusiveProcess.CoarseGrainingVocab.CutoffMoments
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import SubdiffusiveProcess.CoarseGrainingVocab.CrudeJDeterministic
public import SubdiffusiveProcess.EllipticRegularity.InDetLowAlphaCont

public import SubdiffusiveProcess.Paper.Support.InDeterministicPart01


@[expose] public section

section DeterministicRegularity_LowExponent_ContNode




open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable

/-- **`cont` holds for `0 < alpha < 1/2`.** -/
theorem aux_in_deterministic_regularity_cont_of_lowalpha
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha beta s sigma cell epshom : ℝ)
    (Cbound eps0 lam0 delta0 : ℝ) (halpha : alpha ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    aux_in_deterministic_regularity_cont d I alpha beta s sigma cell epshom Cbound eps0 lam0 delta0 := by
  intro cbuf k0 M H hMH k z qside hqpos hqside qcenter hqcenter Enl Shift Cmp _ _ _
    selfE selfShift qRoot hqRoot factor hfactor padE hpad shift hshift rootLevel hrootLevel
    rootSide hrootSide rootCentre hrootCentre rootPos hGridCover parent depth word cmpCentre
    hcmpCentre cmpLevel hcmpLevel cmpSide hcmpSide cmpPos chosen observationCentre
    hObservationCentre eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive
    lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall hdisorder
    prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard sN hsN ellLoN ellHiN hEllLoN hEllHiN
    AEN hAEN errN ratioN hErrN hRatioN Qcentre Qside hQside hRootsQ
    Q q qp Ctotal psource N hkN hcmp harmonicComparison traceEstimate
  refine Filter.Eventually.of_forall fun omega => ?_
  intro f hf fL2 hfL2 fNorm u hu
  exact aux_in_deterministic_lowalpha_cont hd M H omega N Qcentre Qside hQside alpha
    halpha.1 (halpha.2.trans (by norm_num)) f hf fL2 hfL2 u hu



theorem aux_in_deterministic_regularity_cont_of_mem_Ioo
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha beta s sigma cell epshom : ℝ)
    (Cbound eps0 lam0 delta0 : ℝ) (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1) :
    aux_in_deterministic_regularity_cont d I alpha beta s sigma cell epshom Cbound eps0 lam0 delta0 := by
  by_cases hlow : alpha < 1 / 2
  · exact aux_in_deterministic_regularity_cont_of_lowalpha d hd I alpha beta s sigma cell epshom
      Cbound eps0 lam0 delta0 ⟨halpha.1, hlow⟩
  · intro cbuf k0 M H hMH k z qside hqpos hqside qcenter hqcenter Enl Shift Cmp _ _ _
      selfE selfShift qRoot hqRoot factor hfactor padE hpad shift hshift rootLevel hrootLevel
      rootSide hrootSide rootCentre hrootCentre rootPos hGridCover parent depth word cmpCentre
      hcmpCentre cmpLevel hcmpLevel cmpSide hcmpSide cmpPos chosen observationCentre
      hObservationCentre eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive
      lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall hdisorder
      prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard sN hsN ellLoN ellHiN hEllLoN hEllHiN
      AEN hAEN errN ratioN hErrN hRatioN Qcentre Qside hQside hRootsQ
      Q q qp Ctotal psource N hkN hcmp harmonicComparison traceEstimate
    refine Filter.Eventually.of_forall fun omega => ?_
    intro f hf fL2 hfL2 fNorm u hu
    exact aux_in_deterministic_regularity_cont_half hd M H omega N Qcentre Qside hQside alpha
      (not_lt.1 hlow) halpha.2 f hf fL2 hfL2 u hu

end SubdiffusiveProcess.Paper
end
end DeterministicRegularity_LowExponent_ContNode

section InDetCoreChunk_InDetCore_Skeleton




open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable

/-- **The D3 harmonic window.**  For every sample and every native sourced weak solution on `Q`
with a continuous representative `U`, every triadic cube `c + Q_r` (`r = 3^{-l}`) whose closed
outer window `closedBall c (r/18)` lies in a room cube `qd = ball w (27 r / 2) ⊆ Q`, and every
reference `a0 > 0` with `I.err ≤ E0`: a Laplace-harmonic `v` on `qc = c + Q_{r/81}` with a
representative continuous up to the boundary and equal to `U` there, and the interior harmonic
approximation with the source measured on `qd`. -/
def aux_in_deterministic_core_harm_window (d : ℕ) [NeZero d] (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (alpha s : ℝ) (Charm E0 : ℝ) : Prop :=
  ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ)
    (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
    (f : SpatialCoordinates d → ℝ),
    MemLp f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
      (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) →
    ∀ (fL2 : DomainL2 (centeredCube Qcentre Qside hQside)),
    ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] f) →
    ∀ u : weakSobolevGraph (centeredCube Qcentre Qside hQside),
    (∀ psi : killedSobolevGraph (centeredCube Qcentre Qside hQside),
        sobolevCoefficientForm
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
          (u : SobolevData (centeredCube Qcentre Qside hQside))
          (psi : SobolevData (centeredCube Qcentre Qside hQside)) =
        sobolevVolumeLoad fL2 (psi : SobolevData (centeredCube Qcentre Qside hQside))) →
    ∀ U : SpatialCoordinates d → ℝ,
    ContinuousOn U (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) →
    (((u : SobolevData (centeredCube Qcentre Qside hQside)).1 :
        SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] U) →
    ∀ (c : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (l : ℤ), r = (3 : ℝ) ^ (-l) →
    ∀ w : SpatialCoordinates d,
    Metric.closedBall c (r / 18) ⊆ Metric.ball w (27 * r / 2) →
    Metric.ball w (27 * r / 2) ⊆
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) →
    ∀ (a0 : ℝ), 0 < a0 →
    I.err c r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N c hr) c r a0 s 2 ≤ E0 →
    ∃ (v : weakSobolevGraph (centeredCube c (r / 81) (div_pos hr (by norm_num))))
      (V : SpatialCoordinates d → ℝ),
      ContinuousOn V (closure (centeredCube c (r / 81) (div_pos hr (by norm_num)) :
        Set (SpatialCoordinates d))) ∧
      (((v : SobolevData (centeredCube c (r / 81) (div_pos hr (by norm_num)))).1 :
          SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube c (r / 81) (div_pos hr (by norm_num)) : Set (SpatialCoordinates d))] V) ∧
      (∀ x ∈ frontier (centeredCube c (r / 81) (div_pos hr (by norm_num)) :
          Set (SpatialCoordinates d)), V x = U x) ∧
      (∀ psi : killedSobolevGraph (centeredCube c (r / 81) (div_pos hr (by norm_num))),
        inner ℝ (sobolevGradient (v : SobolevData (centeredCube c (r / 81)
            (div_pos hr (by norm_num)))))
          (subspaceGradient (killedSobolevGraph (centeredCube c (r / 81)
            (div_pos hr (by norm_num)))) psi) = 0) ∧
      normalizedL2On (Metric.ball c (r / 1458)) (fun x => U x - V x) ≤
        Charm * I.err c r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N c hr) c r a0 s 2 *
            normalizedL2On (Metric.ball c (r / 18)) (fun x => U x -
              (volume.real (Metric.ball c (r / 18)))⁻¹ * ∫ y in Metric.ball c (r / 18), U y) +
          Charm * (r / 9) ^ 2 * a0⁻¹ *
            ((eLpNorm f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
                (volume.restrict (Metric.ball w (27 * r / 2)))).toReal /
              (volume.real (Metric.ball w (27 * r / 2))) ^ (1 / ((d : ℝ) / (1 - alpha))))

/-- **`harm` from the D3 harmonic window.** -/
theorem aux_in_deterministic_core_harm_of_window
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha beta s sigma cell epshom : ℝ) (hepshom : 0 < epshom)
    (Charm E0 : ℝ) (hCharm : 0 ≤ Charm) (hE0 : 0 < E0)
    (hHW : aux_in_deterministic_core_harm_window d I alpha s Charm E0)
    (Cbound eps0 lam0 delta0 : ℝ) (hCb : Charm ≤ Cbound) (hCbE : epshom / E0 ≤ Cbound) :
    aux_in_deterministic_regularity_harm d I alpha beta s sigma cell epshom
      Cbound eps0 lam0 delta0 := by
  intro cbuf k0 M H hMH k z qside hqpos hqside qcenter hqcenter Enl Shift Cmp _ _ _
    selfE selfShift qRoot hqRoot factor hfactor padE hpad shift hshift rootLevel hrootLevel
    rootSide hrootSide rootCentre hrootCentre rootPos hGridCover parent depth word cmpCentre
    hcmpCentre cmpLevel hcmpLevel cmpSide hcmpSide cmpPos chosen observationCentre
    hObservationCentre eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive
    lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall hdisorder
    prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard sN hsN ellLoN ellHiN hEllLoN hEllHiN
    AEN hAEN errN ratioN hErrN hRatioN Qcentre Qside hQside hRootsQ
    Q q qp Ctotal psource N hkN hcmp harmonicComparison traceEstimate
  have hsNpos := aux_in_deterministic_regularity_sN_pos M H sN hsN
  have hCbpos : 0 < Cbound := lt_of_lt_of_le (div_pos hepshom hE0) hCbE
  refine Filter.Eventually.of_forall (fun omega => ?_)
  intro horizon hev _hb f hf fL2 hfL2 fNorm u hu U hUc hUae
  dsimp only [harmonicComparison]
  intro w hcl hqdQ
  have ha0 := hsNpos N (cmpLevel chosen) (cmpCentre chosen) omega
  have hE : I.err (cmpCentre chosen) (cmpSide chosen) (cmpPos chosen)
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (cmpCentre chosen) (cmpPos chosen))
      (cmpCentre chosen) (cmpSide chosen) (sN N (cmpLevel chosen) (cmpCentre chosen) omega) s 2 ≤
      epshom * cdet := by
    rw [← hErrN N chosen omega]
    exact hev.2.2.1
  have hcdC : epshom * cdet ≤ epshom * Cbound⁻¹ := mul_le_mul_of_nonneg_left hcdetSmall hepshom.le
  have hEC : epshom * Cbound⁻¹ ≤ E0 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hCbpos]
    rw [div_le_iff₀ hE0] at hCbE
    linarith
  obtain ⟨v, V, h1, h2, h3, h4, h5⟩ := hHW M H omega N Qcentre Qside hQside f hf fL2 hfL2 u hu
    U hUc hUae (cmpCentre chosen) (cmpSide chosen) (cmpPos chosen) (cmpLevel chosen)
    (hcmpSide chosen) w hcl hqdQ
    (sN N (cmpLevel chosen) (cmpCentre chosen) omega) ha0 ((hE.trans hcdC).trans hEC)
  refine ⟨v, V, h1, h2, h3, h4, le_trans h5 (add_le_add ?_ ?_)⟩
  · refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    have hA : Charm * Cbound⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hCbpos]
      exact hCb
    calc Charm * I.err (cmpCentre chosen) (cmpSide chosen) (cmpPos chosen)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (cmpCentre chosen) (cmpPos chosen))
          (cmpCentre chosen) (cmpSide chosen) (sN N (cmpLevel chosen) (cmpCentre chosen) omega)
          s 2
        ≤ Charm * (epshom * Cbound⁻¹) := mul_le_mul_of_nonneg_left (hE.trans hcdC) hCharm
      _ = epshom * (Charm * Cbound⁻¹) := by ring
      _ ≤ epshom * 1 := mul_le_mul_of_nonneg_left hA hepshom.le
      _ = epshom := mul_one _
  · have hfN : 0 ≤ (eLpNorm f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
          (volume.restrict (Metric.ball w (27 * cmpSide chosen / 2)))).toReal /
        (volume.real (Metric.ball w (27 * cmpSide chosen / 2))) ^
          (1 / ((d : ℝ) / (1 - alpha))) :=
      div_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg measureReal_nonneg _)
    have hCt : Charm ≤ Ctotal := by
      have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ))) :=
        Real.one_le_rpow (by norm_num) (by positivity)
      calc Charm ≤ Cbound := hCb
        _ ≤ Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ))) :=
          le_mul_of_one_le_right hCbpos.le h3
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCt (sq_nonneg _)) (inv_nonneg.2 ha0.le)) hfN

/-- The Campanato constant of the chain, with the step inputs. -/
theorem aux_in_deterministic_core_camp_of_window
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha beta s sigma cell epshom : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hsSmall : s ≤ (1 / 32 : ℝ))
    (h : ℕ) (theta Ceps Cdel E0 : ℝ) (hh : 0 < h) (htheta : theta ∈ Set.Ioo (0 : ℝ) 1)
    (hthetah : theta ^ h ∈ Set.Ioo (0 : ℝ) (3 / 5))
    (hE0 : 0 < E0) (hCeps : 0 ≤ Ceps) (hCdel : 0 ≤ Cdel)
    (hOS : aux_in_deterministic_onestep_window d I alpha s h theta Ceps Cdel E0) :
    ∃ C1 : ℝ, 0 ≤ C1 ∧ ∃ eAn dAn : ℝ, 0 < eAn ∧ 0 < dAn ∧
      ∀ (Cbound eps0 lam0 delta0 : ℝ), eps0 ≤ eAn → delta0 ≤ dAn →
        aux_in_deterministic_regularity_camp d I alpha beta s sigma cell epshom
          Cbound eps0 lam0 delta0 C1 := by
  obtain ⟨Cit, hCit, hcamp⟩ := aux_in_deterministic_regularity_camp_of_onestep d
  obtain ⟨C2, hC2, eAn, dAn, heAn, hdAn, hone⟩ :=
    aux_in_deterministic_onestep_repaired_of_window d I alpha beta s sigma cell epshom halpha hs
      hsSmall h theta Ceps Cdel E0 hE0 hCeps hCdel hOS
  exact ⟨aux_in_deterministic_regularity_campConst d Cit h C2,
    aux_in_deterministic_regularity_campConst_nonneg d Cit h C2, eAn, dAn, heAn, hdAn,
    fun Cbound eps0 lam0 delta0 he hd => hcamp I alpha beta s sigma cell epshom Cbound eps0 lam0
      delta0 h theta C2 hh htheta hthetah hC2 (hone Cbound eps0 lam0 delta0 he hd)⟩

/-- **R1 and R2 from the two windows**, with one threshold `C1` and caps. -/
theorem aux_in_deterministic_core_R12_of_windows
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha beta s sigma cell epshom : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hsSmall : s ≤ (1 / 32 : ℝ))
    (hepshom : 0 < epshom)
    (h : ℕ) (theta Ceps Cdel E0 : ℝ) (hh : 0 < h) (htheta : theta ∈ Set.Ioo (0 : ℝ) 1)
    (hthetah : theta ^ h ∈ Set.Ioo (0 : ℝ) (3 / 5))
    (hE0 : 0 < E0) (hCeps : 0 ≤ Ceps) (hCdel : 0 ≤ Cdel)
    (hOS : aux_in_deterministic_onestep_window d I alpha s h theta Ceps Cdel E0)
    (Charm Eh : ℝ) (hCharm : 0 ≤ Charm) (hEh : 0 < Eh)
    (hHW : aux_in_deterministic_core_harm_window d I alpha s Charm Eh) :
    ∃ C1 : ℝ, 1 ≤ C1 ∧ ∀ Cbound : ℝ, C1 ≤ Cbound →
      ∃ e1 l1 d1 : ℝ, 0 < e1 ∧ 0 < l1 ∧ 0 < d1 ∧
      ∀ eps0 lam0 delta0 : ℝ, 0 < eps0 → eps0 ≤ e1 → 0 < lam0 → lam0 ≤ l1 →
        0 < delta0 → delta0 ≤ d1 →
        aux_in_deterministic_regularity_R1 d I alpha beta s sigma cell epshom
          Cbound eps0 lam0 delta0 ∧
        aux_in_deterministic_regularity_R2 d I alpha beta s sigma cell epshom
          Cbound eps0 lam0 delta0 := by
  obtain ⟨Cc, hCc, eAn, dAn, heAn, hdAn, hcamp⟩ :=
    aux_in_deterministic_core_camp_of_window d I alpha beta s sigma cell epshom halpha hs hsSmall
      h theta Ceps Cdel E0 hh htheta hthetah hE0 hCeps hCdel hOS
  set Ch := aux_in_deterministic_regularity_holderConst d alpha with hChdef
  have hCh0 : 0 ≤ Ch := aux_in_deterministic_regularity_holderConst_nonneg d halpha.1
  refine ⟨max 1 (max Cc (max (2 * Ch * Cc) (max Charm (epshom / Eh)))), le_max_left _ _,
    fun Cbound hCb => ?_⟩
  have hb1 : Cc ≤ Cbound := ((le_max_left _ _).trans (le_max_right _ _)).trans hCb
  have hb2 : 2 * Ch * Cc ≤ Cbound :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hCb
  have hb3 : Charm ≤ Cbound :=
    ((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans hCb
  have hb4 : epshom / Eh ≤ Cbound :=
    ((((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans hCb
  refine ⟨eAn, 1, dAn, heAn, one_pos, hdAn, fun eps0 lam0 delta0 _ he0 _ _ _ hd0 => ?_⟩
  have hcore := aux_in_deterministic_regularity_core_of_parts d I alpha beta s sigma cell epshom
    Cbound eps0 lam0 delta0 Cc
    (aux_in_deterministic_regularity_cont_of_mem_Ioo d hd I alpha beta s sigma cell epshom
      Cbound eps0 lam0 delta0 halpha)
    (hcamp Cbound eps0 lam0 delta0 he0 hd0)
    (aux_in_deterministic_core_harm_of_window d I alpha beta s sigma cell epshom hepshom
      Charm Eh hCharm hEh hHW Cbound eps0 lam0 delta0 hb3 hb4)
  exact ⟨aux_in_deterministic_regularity_R1_of_core d I alpha beta s sigma cell epshom
      Cbound eps0 lam0 delta0 Cc hCc hb1 hcore,
    aux_in_deterministic_regularity_R2_of_core d I alpha beta s sigma cell epshom
      Cbound eps0 lam0 delta0 halpha Cc hCc hb1 hb2 hcore⟩

end SubdiffusiveProcess.Paper
end
end InDetCoreChunk_InDetCore_Skeleton

section InDetCoreChunk_InDetCore_HarmWindow

/-!
# The D3 harmonic window from the carrier 

`aux_in_deterministic_core_harm_window_holds`: clause 2 of `deterministic_good_scale_input`
supplies `aux_in_deterministic_core_harm_window` for every `alpha ∈ (0,1)`, `0 < s ≤ 1/32`.
The physical room cube `qd = w + Q_{27 r}` is the GMC cube `□_5` under `y ↦ (r/9) y + w`; the
chosen cube is the working cube `z + □_2`, `qo = z + □_0`, `qc = z + □_{-2}`, `qi = z + □_{-4}`.
-/

open MeasureTheory Set Metric Filter Topology TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal Pointwise

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable

/-- The actual cutoff coefficient on a cube is a.e. the continuous `A_N`. -/
theorem aux_in_deterministic_core_cutoff_coeFn {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    (fun x => (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr).val x)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        cutoffCoefficient M H omega N := by
  have : Fact (((centeredCube z r hr : Set (SpatialCoordinates d))) ⊆
      (closedCube z r hr : Set (SpatialCoordinates d))) :=
    ⟨centeredCube_subset_closedCube z hr⟩
  have hval : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∀ hx : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr).val x =
          _root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM M H omega N z hr
            ⟨x, centeredCube_subset_closedCube z hr hx⟩ / 1 :=
    normalizedContinuousPositiveCoefficient_coeFn (Ω := centeredCube z r hr)
    (closedCube z r hr) (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM M H omega N z hr)
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM_pos M H omega N z hr) 1 one_pos
  filter_upwards [hval, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet]
    with x hx hxΩ
  rw [hx hxΩ, div_one]
  rfl

/-- A continuous positive scalar field has the cube-by-cube certificates. -/
theorem aux_in_deterministic_core_scalar_data {d : ℕ} {a : Vec d → ℝ} (ha : Continuous a)
    (hpos : ∀ x, 0 < a x) : Nonempty (ScalarTriadicCoeffData a) :=
  ⟨{ onCube := fun Q => Classical.choice
      (SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.exists_scalarCoeffOnData_of_continuous_pos ha hpos
        (Homogenization.Book.Ch02.cubeDomain Q)) }⟩

/-- The physical ball of centre `μ • y + w`. -/
theorem aux_in_deterministic_core_affine_ball {d : ℕ} {μ : ℝ} (hμ : 0 < μ) (w y : Vec d)
    (ρ : ℝ) : translateSet w (μ • Metric.ball y ρ) = Metric.ball (μ • y + w) (μ * ρ) :=
  aux_in_deterministic_core_translateSet_smul_ball hμ w y ρ

/-- Distance under the affine map. -/
theorem aux_in_deterministic_core_dist_affine {d : ℕ} {μ : ℝ} (hμ : 0 < μ) (w x y : Vec d) :
    dist (μ • x + w) (μ • y + w) = μ * dist x y := by
  rw [dist_eq_norm, dist_eq_norm, add_sub_add_right_eq_sub, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_pos hμ]

/-- Distance under the inverse affine map. -/
theorem aux_in_deterministic_core_dist_affine_inv {d : ℕ} {μ : ℝ} (hμ : 0 < μ) (w x c : Vec d) :
    dist (μ⁻¹ • (x - w)) (μ⁻¹ • (c - w)) = μ⁻¹ * dist x c := by
  rw [dist_smul₀, Real.norm_eq_abs, abs_inv, abs_of_pos hμ, dist_eq_norm, dist_eq_norm,
    sub_sub_sub_cancel_right]

/-! ### Scale bookkeeping for the room cube -/

theorem aux_in_deterministic_core_three_pow_room (r : ℝ) (l : ℤ) (hrl : r = (3 : ℝ) ^ (-l)) :
    (3 : ℝ) ^ (3 - l) = 27 * r := by
  rw [hrl, sub_eq_add_neg, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]; norm_num

theorem aux_in_deterministic_core_room_scale (r : ℝ) (l : ℤ) (hrl : r = (3 : ℝ) ^ (-l)) :
    (3 : ℝ) ^ (3 - l) * ((3 : ℝ) ^ (5 : ℤ))⁻¹ = r / 9 := by
  rw [aux_in_deterministic_core_three_pow_room r l hrl]; norm_num; ring

theorem aux_in_deterministic_core_room_img {d : ℕ} (w : Vec d) {r : ℝ} (hr : 0 < r) :
    translateSet w ((r / 9) • cube d 5) = Metric.ball w (27 * r / 2) := by
  rw [aux_in_deterministic_core_cube_eq_ball, aux_in_deterministic_core_affine_ball (by positivity),
    smul_zero, zero_add]
  congr 1; norm_num; ring

theorem aux_in_deterministic_core_zG_img {d : ℕ} (c w : Vec d) {r : ℝ} (hr : 0 < r) :
    (r / 9) • ((r / 9)⁻¹ • (c - w)) + w = c := by
  rw [smul_smul, mul_inv_cancel₀ (by positivity), one_smul, sub_add_cancel]

theorem aux_in_deterministic_core_zG_ball {d : ℕ} (c w : Vec d) {r : ℝ} (hr : 0 < r)
    (hcl : Metric.closedBall c (r / 18) ⊆ Metric.ball w (27 * r / 2)) :
    Metric.closedBall ((r / 9)⁻¹ • (c - w)) (1 / 2) ⊆ cube d 5 := by
  have hμ : 0 < r / 9 := by positivity
  intro y hy
  have h1 : (r / 9) • y + w ∈ Metric.closedBall c (r / 18) := by
    rw [Metric.mem_closedBall, ← aux_in_deterministic_core_zG_img c w hr,
      aux_in_deterministic_core_dist_affine hμ]
    rw [Metric.mem_closedBall] at hy
    calc r / 9 * dist y ((r / 9)⁻¹ • (c - w)) ≤ r / 9 * (1 / 2) :=
          mul_le_mul_of_nonneg_left hy hμ.le
      _ = r / 18 := by ring
  have h2 := hcl h1
  rw [← aux_in_deterministic_core_room_img w hr, mem_translateSet_iff_sub_mem,
    add_sub_cancel_right] at h2
  exact (Set.smul_mem_smul_set_iff₀ hμ.ne' _ _).1 h2

/-! ### Transport to the room cube, the error identification, the representative -/

theorem aux_in_deterministic_core_transport_room {d : ℕ} [NeZero d] {CT : ℝ}
    (htr : aux_in_deterministic_core_transport_prop d CT)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ)
    (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
    (f : SpatialCoordinates d → ℝ) (fL2 : DomainL2 (centeredCube Qcentre Qside hQside))
    (hfL2 : ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] f))
    (u : weakSobolevGraph (centeredCube Qcentre Qside hQside))
    (hu : ∀ psi : killedSobolevGraph (centeredCube Qcentre Qside hQside),
        sobolevCoefficientForm
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
          (u : SobolevData (centeredCube Qcentre Qside hQside))
          (psi : SobolevData (centeredCube Qcentre Qside hQside)) =
        sobolevVolumeLoad fL2 (psi : SobolevData (centeredCube Qcentre Qside hQside)))
    (w : SpatialCoordinates d) (r : ℝ) (l : ℤ) (hrl : r = (3 : ℝ) ^ (-l))
    (hqdQ : Metric.ball w (27 * r / 2) ⊆
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
    (hf2 : MemLp f 2 (volume.restrict (Metric.ball w (27 * r / 2)))) :
    ∃ (ut : H1Function (openCubeSet (originCube d 5)))
      (F : CubeVectorH1Function (originCube d 0)),
      (∀ y, ut.toFun y = ((u : SobolevData (centeredCube Qcentre Qside hQside)).1 :
          SpatialCoordinates d → ℝ) ((r / 9) • y + w)) ∧
      IsDivFormWeakSolutionOn (fun y => cutoffCoefficient M H omega N ((r / 9) • y + w))
        (cube d 5) ut (Section6Dirichlet.centeredCubeScaledVectorDilation 1 5 F).toField ∧
      Section6Dirichlet.unitCubeVectorH1ENormBudget F ≤
        ENNReal.ofReal (CT * ((27 * r) ^ 2 * Real.sqrt (((27 * r) ^ d)⁻¹) *
          (eLpNorm f 2 (volume.restrict (Metric.ball w (27 * r / 2)))).toReal)) := by
  have h3 := aux_in_deterministic_core_three_pow_room r l hrl
  have hS : ∀ y : Vec d, ((3 : ℝ) ^ (3 - l)) • (((3 : ℝ) ^ (5 : ℤ))⁻¹ • y) + w =
      (r / 9) • y + w := by
    intro y; rw [smul_smul, aux_in_deterministic_core_room_scale r l hrl]
  have hball : Metric.ball w ((3 : ℝ) ^ (3 - l) / 2) = Metric.ball w (27 * r / 2) := by rw [h3]
  obtain ⟨ut, F, hut, hdiv, hbud⟩ := htr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
    (cutoffCoefficient M H omega N)
    (aux_in_deterministic_core_cutoff_coeFn M H omega N Qcentre hQside)
    f fL2 hfL2 u hu w (3 - l) 5 (by rw [hball]; exact hqdQ) (by rw [hball]; exact hf2)
  refine ⟨ut, F, fun y => by rw [hut y, hS y], ?_, ?_⟩
  · have hfun : (fun y => cutoffCoefficient M H omega N
        (((3 : ℝ) ^ (3 - l)) • (((3 : ℝ) ^ (5 : ℤ))⁻¹ • y) + w)) =
        fun y => cutoffCoefficient M H omega N ((r / 9) • y + w) := by
      funext y; rw [hS]
    rw [hfun] at hdiv
    exact hdiv
  · rw [h3] at hbud
    exact hbud

theorem aux_in_deterministic_core_err_room {d : ℕ} (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (c w : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (a0 : ℝ) (ha0 : 0 < a0) (s : ℝ)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ data : ScalarTriadicCoeffData
        (fun y => cutoffCoefficient M H omega N ((r / 9) • (y + (r / 9)⁻¹ • (c - w)) + w)),
      paperHomogenizationError (originCube d 2) 2 s
          Homogenization.Book.Ch02.MultiscaleExponent.infinity
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
          data.toTriadicCoeffFamily a0 ≠ ⊤ ∧
      (paperHomogenizationError (originCube d 2) 2 s
          Homogenization.Book.Ch02.MultiscaleExponent.infinity
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
          data.toTriadicCoeffFamily a0).toReal =
        I.err c r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N c hr) c r a0 s 2 := by
  have hcont : Continuous
      (fun y : Vec d => cutoffCoefficient M H omega N ((r / 9) • (y + (r / 9)⁻¹ • (c - w)) + w)) :=
    (cutoffCoefficient_continuous M H omega N).comp
      (by fun_prop)
  obtain ⟨data⟩ := aux_in_deterministic_core_scalar_data hcont
    (fun y => cutoffCoefficient_pos M H omega N _)
  have ha' : ∀ᵐ y ∂volume.restrict (openCubeSet (originCube d 2)),
      (fun y : Vec d => cutoffCoefficient M H omega N ((r / 9) • y + w))
          (y + (r / 9)⁻¹ • (c - w)) =
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N c hr).val
          (fun i => c i + r * ((3 : ℝ) ^ (2 : ℤ))⁻¹ * y i) := by
    have hco := aux_in_deterministic_core_cutoff_coeFn M H omega N c hr
    have hset : translateSet c ((r / 9) • openCubeSet (originCube d 2)) =
        (centeredCube c r hr : Set (SpatialCoordinates d)) := by
      rw [show openCubeSet (originCube d 2) = cube d 2 from rfl,
        aux_in_deterministic_core_cube_eq_ball, aux_in_deterministic_core_affine_ball
          (by positivity), smul_zero, zero_add]
      change _ = Metric.ball c (r / 2)
      congr 1; norm_num; ring
    obtain ⟨gA, hgA⟩ : ∃ gA : Vec d → ℝ,
        gA = fun x => (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N c hr).val x := ⟨_, rfl⟩
    have hco' : gA =ᵐ[volume.restrict (translateSet c ((r / 9) • openCubeSet (originCube d 2)))]
        cutoffCoefficient M H omega N := by
      rw [hset, hgA]; exact hco
    have hpb := aux_in_deterministic_core_ae_affine (R := r / 9) (by positivity) c
      (openCubeSet (originCube d 2)) hco'
    filter_upwards [hpb] with y hy
    rw [hgA] at hy
    have e1 : (fun i => c i + r * ((3 : ℝ) ^ (2 : ℤ))⁻¹ * y i) = (r / 9) • y + c := by
      funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; norm_num; ring
    have e2 : (r / 9) • (y + (r / 9)⁻¹ • (c - w)) + w = (r / 9) • y + c := by
      rw [smul_add, add_assoc, aux_in_deterministic_core_zG_img c w hr]
    rw [e1]
    show cutoffCoefficient M H omega N ((r / 9) • (y + (r / 9)⁻¹ • (c - w)) + w) = _
    rw [e2]
    exact hy.symm
  obtain ⟨hEeq, hEfin⟩ := aux_in_deterministic_core_err_scaled I c r hr 2
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N c hr)
    (fun y : Vec d => cutoffCoefficient M H omega N ((r / 9) • y + w)) ((r / 9)⁻¹ • (c - w))
    ha' data a0 ha0 s hs
  exact ⟨data, hEfin, hEeq.symm⟩

theorem aux_in_deterministic_core_rep_room {d : ℕ} {Ω : Set (Vec d)}
    (U V0 : Vec d → ℝ) (hUc : ContinuousOn U Ω) (hUae : V0 =ᵐ[volume.restrict Ω] U)
    (ut : H1Function (openCubeSet (originCube d 5))) (w : Vec d) {r : ℝ} (hr : 0 < r)
    (hut : ∀ y, ut.toFun y = V0 ((r / 9) • y + w))
    (hqdQ : Metric.ball w (27 * r / 2) ⊆ Ω) :
    ContinuousOn (fun y => U ((r / 9) • y + w)) (cube d 5) ∧
      ut.toFun =ᵐ[volume.restrict (cube d 5)] (fun y => U ((r / 9) • y + w)) := by
  have hμ : 0 < r / 9 := by positivity
  have hmaps : ∀ y ∈ cube d 5, (r / 9) • y + w ∈ Metric.ball w (27 * r / 2) := by
    intro y hy
    rw [← aux_in_deterministic_core_room_img w hr, mem_translateSet_iff_sub_mem,
      add_sub_cancel_right]
    exact Set.smul_mem_smul_set hy
  refine ⟨hUc.comp (by fun_prop)
    (fun y hy => hqdQ (hmaps y hy)), ?_⟩
  have h1 : ∀ᵐ q ∂volume.restrict (translateSet w ((r / 9) • cube d 5)), V0 q = U q := by
    rw [aux_in_deterministic_core_room_img w hr]
    exact ae_restrict_of_ae_restrict_of_subset hqdQ hUae
  filter_upwards [aux_in_deterministic_core_ae_affine hμ w (cube d 5) h1] with y hy
  rw [hut y]
  exact hy

/-! ### Back to the physical cube -/



theorem aux_in_deterministic_core_phys_room {d : ℕ} (c w : Vec d) {r : ℝ} (hr : 0 < r)
    (U : Vec d → ℝ)
    (v : H1Function (translatedCube d (((0 : ℕ) : ℤ) - 2) ((r / 9)⁻¹ • (c - w))))
    (hvH : IsWeaklyHarmonicOn (fun _ => (1 : ℝ))
      (translatedCube d (((0 : ℕ) : ℤ) - 2) ((r / 9)⁻¹ • (c - w))) v)
    (V : Vec d → ℝ)
    (hVc : ContinuousOn V (closure (Metric.ball ((r / 9)⁻¹ • (c - w)) (1 / 18))))
    (hVae : V =ᵐ[volume.restrict
      (translatedCube d (((0 : ℕ) : ℤ) - 2) ((r / 9)⁻¹ • (c - w)))] v.toFun)
    (hVfr : ∀ x ∈ frontier (Metric.ball ((r / 9)⁻¹ • (c - w)) (1 / 18)),
      V x = U ((r / 9) • x + w)) :
    ∃ (vN : weakSobolevGraph (centeredCube c (r / 81) (div_pos hr (by norm_num))))
      (VP : Vec d → ℝ),
      ContinuousOn VP (closure (centeredCube c (r / 81) (div_pos hr (by norm_num)) :
        Set (SpatialCoordinates d))) ∧
      (((vN : SobolevData (centeredCube c (r / 81) (div_pos hr (by norm_num)))).1 :
          SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube c (r / 81) (div_pos hr (by norm_num)) : Set (SpatialCoordinates d))] VP) ∧
      (∀ x ∈ frontier (centeredCube c (r / 81) (div_pos hr (by norm_num)) :
          Set (SpatialCoordinates d)), VP x = U x) ∧
      (∀ psi : killedSobolevGraph (centeredCube c (r / 81) (div_pos hr (by norm_num))),
        inner ℝ (sobolevGradient (vN : SobolevData (centeredCube c (r / 81)
            (div_pos hr (by norm_num)))))
          (subspaceGradient (killedSobolevGraph (centeredCube c (r / 81)
            (div_pos hr (by norm_num)))) psi) = 0) ∧
      normalizedL2On (Metric.ball c (r / 1458)) (fun x => U x - VP x) =
        normalizedL2On (Metric.ball ((r / 9)⁻¹ • (c - w)) (1 / 162))
          (fun q => U ((r / 9) • q + w) - V q) := by
  have hμ : 0 < r / 9 := by positivity
  have hK : translatedCube d (((0 : ℕ) : ℤ) - 2) ((r / 9)⁻¹ • (c - w)) =
      Metric.ball ((r / 9)⁻¹ • (c - w)) (1 / 18) := by
    rw [aux_in_deterministic_regularity_translatedCube_eq_ball]; norm_num
  have hP : (centeredCube c (r / 81) (div_pos hr (by norm_num)) : Set (Vec d)) =
      translateSet w ((r / 9) • translatedCube d (((0 : ℕ) : ℤ) - 2) ((r / 9)⁻¹ • (c - w))) := by
    rw [hK, aux_in_deterministic_core_affine_ball hμ, aux_in_deterministic_core_zG_img c w hr]
    change Metric.ball c (r / 81 / 2) = _
    congr 1; ring
  obtain ⟨vP, hvPf, hvPH⟩ := aux_in_deterministic_core_harmonic_pushforward hμ w hP v hvH
  refine ⟨⟨sobolevDataOfH1 vP, sobolevDataOfH1_mem_weak vP⟩,
    fun x => V ((r / 9)⁻¹ • (x - w)), ?_, ?_, ?_,
    aux_in_deterministic_core_native_harmonic vP hvPH, ?_⟩
  · have hT : Continuous (fun x : Vec d => (r / 9)⁻¹ • (x - w)) :=
      by fun_prop
    refine hVc.comp hT.continuousOn ?_
    intro x hx
    change x ∈ closure (Metric.ball c (r / 81 / 2)) at hx
    rw [closure_ball _ (by positivity : r / 81 / 2 ≠ 0), Metric.mem_closedBall] at hx
    rw [closure_ball _ (by norm_num : (1 / 18 : ℝ) ≠ 0), Metric.mem_closedBall,
      aux_in_deterministic_core_dist_affine_inv hμ]
    calc (r / 9)⁻¹ * dist x c ≤ (r / 9)⁻¹ * (r / 81 / 2) :=
          mul_le_mul_of_nonneg_left hx (inv_nonneg.2 hμ.le)
      _ = 1 / 18 := by field_simp; ring
  · have hset' : translateSet (-((r / 9)⁻¹ • w))
        ((r / 9)⁻¹ • (centeredCube c (r / 81) (div_pos hr (by norm_num)) : Set (Vec d))) =
        translatedCube d (((0 : ℕ) : ℤ) - 2) ((r / 9)⁻¹ • (c - w)) := by
      rw [hK]
      change translateSet _ ((r / 9)⁻¹ • Metric.ball c (r / 81 / 2)) = _
      rw [aux_in_deterministic_core_affine_ball (inv_pos.2 hμ)]
      congr 1
      · rw [smul_sub]; abel
      · field_simp; ring
    have hae : ∀ᵐ y ∂volume.restrict (translateSet (-((r / 9)⁻¹ • w))
        ((r / 9)⁻¹ • (centeredCube c (r / 81) (div_pos hr (by norm_num)) : Set (Vec d)))),
        v.toFun y = V y := by
      rw [hset']; filter_upwards [hVae] with y hy; exact hy.symm
    have hpb := aux_in_deterministic_core_ae_affine (inv_pos.2 hμ) (-((r / 9)⁻¹ • w)) _ hae
    filter_upwards [hpb, sobolevDataOfH1_fst_coeFn vP] with x hx h1
    change ((sobolevDataOfH1 vP).1 : Vec d → ℝ) x = V ((r / 9)⁻¹ • (x - w))
    rw [h1, hvPf x]
    have e : (r / 9)⁻¹ • x + -((r / 9)⁻¹ • w) = (r / 9)⁻¹ • (x - w) := by
      rw [smul_sub, sub_eq_add_neg]
    rw [e] at hx
    exact hx
  · intro x hx
    change x ∈ frontier (Metric.ball c (r / 81 / 2)) at hx
    rw [frontier_ball _ (by positivity : r / 81 / 2 ≠ 0), Metric.mem_sphere] at hx
    have hT1 : (r / 9)⁻¹ • (x - w) ∈ frontier (Metric.ball ((r / 9)⁻¹ • (c - w)) (1 / 18)) := by
      rw [frontier_ball _ (by norm_num : (1 / 18 : ℝ) ≠ 0), Metric.mem_sphere,
        aux_in_deterministic_core_dist_affine_inv hμ, hx]
      field_simp; ring
    change V ((r / 9)⁻¹ • (x - w)) = U x
    rw [hVfr _ hT1, smul_smul, mul_inv_cancel₀ hμ.ne', one_smul, sub_add_cancel]
  · have hset : Metric.ball c (r / 1458) =
        translateSet w ((r / 9) • Metric.ball ((r / 9)⁻¹ • (c - w)) (1 / 162)) := by
      rw [aux_in_deterministic_core_affine_ball hμ, aux_in_deterministic_core_zG_img c w hr]
      congr 1; ring
    rw [hset, aux_in_deterministic_core_normalizedL2On_affine hμ]
    congr 1
    funext q
    change U ((r / 9) • q + w) - V ((r / 9)⁻¹ • ((r / 9) • q + w - w)) = _
    rw [add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hμ.ne', one_smul]

/-- The window oscillation in GMC and physical coordinates. -/
theorem aux_in_deterministic_core_osc_room {d : ℕ} (c w : Vec d) {r : ℝ} (hr : 0 < r)
    (U : Vec d → ℝ) :
    normalizedL2On (Metric.ball ((r / 9)⁻¹ • (c - w)) (1 / 2))
        (fun q => U ((r / 9) • q + w) -
          averageOn (Metric.ball ((r / 9)⁻¹ • (c - w)) (1 / 2)) (fun q => U ((r / 9) • q + w))) =
      normalizedL2On (Metric.ball c (r / 18)) (fun x => U x -
        (volume.real (Metric.ball c (r / 18)))⁻¹ * ∫ y in Metric.ball c (r / 18), U y) := by
  have hμ : 0 < r / 9 := by positivity
  have hset : Metric.ball c (r / 18) =
      translateSet w ((r / 9) • Metric.ball ((r / 9)⁻¹ • (c - w)) (1 / 2)) := by
    rw [aux_in_deterministic_core_affine_ball hμ, aux_in_deterministic_core_zG_img c w hr]
    congr 1; ring
  have havg : (volume.real (Metric.ball c (r / 18)))⁻¹ * ∫ y in Metric.ball c (r / 18), U y =
      averageOn (Metric.ball ((r / 9)⁻¹ • (c - w)) (1 / 2)) (fun q => U ((r / 9) • q + w)) := by
    have := aux_in_deterministic_core_volumeAverage_affine hμ w
      (Metric.ball ((r / 9)⁻¹ • (c - w)) (1 / 2)) U
    rw [← hset] at this
    unfold averageOn
    rw [← this]
    rfl
  rw [havg, hset, aux_in_deterministic_core_normalizedL2On_affine hμ]

/-- The final arithmetic of the harmonic window. -/
theorem aux_in_deterministic_core_harm_arith {LHS CD sD E Osc a0 G Ks CT r L fN C1 C2 S5 : ℝ}
    (hCD : 0 ≤ CD) (hsD : 0 < sD) (hE : 0 ≤ E) (hOsc : 0 ≤ Osc) (ha0 : 0 < a0) (hKs : 0 ≤ Ks)
    (hCT : 0 ≤ CT) (hr : 0 < r) (hS5 : 0 ≤ S5) (hfN : 0 ≤ fN)
    (hC1 : C1 = CD * sD ^ (-3 / 2 : ℝ))
    (hC2 : C2 = CD * sD ^ (-15 / 2 : ℝ) * (S5 * (Ks * CT)) * 3 ^ 10)
    (hest : LHS ≤ CD * sD ^ (-3 / 2 : ℝ) * E * Osc + CD * sD ^ (-15 / 2 : ℝ) * a0⁻¹ * G)
    (hG : G ≤ S5 * (Ks * (CT * ((27 * r) ^ 2 * L))))
    (hL : L ≤ fN) :
    LHS ≤ max C1 C2 * E * Osc + max C1 C2 * (r / 9) ^ 2 * a0⁻¹ * fN := by
  have hp1 : 0 ≤ sD ^ (-3 / 2 : ℝ) := Real.rpow_nonneg hsD.le _
  have hp2 : 0 ≤ sD ^ (-15 / 2 : ℝ) := Real.rpow_nonneg hsD.le _
  have hC1le : C1 ≤ max C1 C2 := le_max_left _ _
  have hC2le : C2 ≤ max C1 C2 := le_max_right _ _
  have hA : CD * sD ^ (-3 / 2 : ℝ) * E * Osc ≤ max C1 C2 * E * Osc := by
    rw [← hC1]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1le hE) hOsc
  have hB : CD * sD ^ (-15 / 2 : ℝ) * a0⁻¹ * G ≤ max C1 C2 * (r / 9) ^ 2 * a0⁻¹ * fN := by
    have hG' : G ≤ S5 * (Ks * (CT * ((27 * r) ^ 2 * fN))) := by
      refine hG.trans ?_
      gcongr
    have hkey : CD * sD ^ (-15 / 2 : ℝ) * a0⁻¹ * (S5 * (Ks * (CT * ((27 * r) ^ 2 * fN)))) =
        C2 * (r / 9) ^ 2 * a0⁻¹ * fN := by
      rw [hC2]; ring
    have h0 : 0 ≤ CD * sD ^ (-15 / 2 : ℝ) * a0⁻¹ := by positivity
    calc CD * sD ^ (-15 / 2 : ℝ) * a0⁻¹ * G ≤
          CD * sD ^ (-15 / 2 : ℝ) * a0⁻¹ * (S5 * (Ks * (CT * ((27 * r) ^ 2 * fN)))) :=
          mul_le_mul_of_nonneg_left hG' h0
      _ = C2 * (r / 9) ^ 2 * a0⁻¹ * fN := hkey
      _ ≤ max C1 C2 * (r / 9) ^ 2 * a0⁻¹ * fN := by gcongr
  linarith

/-- **The D3 harmonic window from clause 2 of the carrier.** -/
theorem aux_in_deterministic_core_harm_window_holds (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (D : _root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d)
    (alpha s : ℝ) (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (hsSmall : s ≤ (1 / 32 : ℝ)) :
    ∃ Charm Eh : ℝ, 0 ≤ Charm ∧ 0 < Eh ∧
      aux_in_deterministic_core_harm_window d I alpha s Charm Eh := by
  obtain ⟨CD, hCD, hD⟩ := aux_in_deterministic_core_clause2_of_det d D
  obtain ⟨CT, hCT, htr⟩ := aux_in_deterministic_core_transport d
  have hs8 : 0 < 8 * s := by linarith [hs.1]
  have hs84 : 8 * s ≤ 1 / 4 := by linarith
  have hs81 : 8 * s < 1 := by linarith
  obtain ⟨Ks, hKs⟩ : ∃ Ks : ℝ, Ks = (Section6Dirichlet.scaledVectorDatumFractionalConstant
      (⟨8 * s, hs8, hs81⟩ : FractionalOrder) d).toReal := ⟨_, rfl⟩
  have hKs0 : 0 ≤ Ks := by rw [hKs]; exact ENNReal.toReal_nonneg
  obtain ⟨S5, hS5⟩ : ∃ S5 : ℝ, S5 = Real.sqrt (((3 : ℝ) ^ (5 : ℤ)) ^ d) := ⟨_, rfl⟩
  have hS50 : 0 ≤ S5 := by rw [hS5]; exact Real.sqrt_nonneg _
  refine ⟨max (CD * (8 * s) ^ (-3 / 2 : ℝ))
      (CD * (8 * s) ^ (-15 / 2 : ℝ) * (S5 * (Ks * CT)) * 3 ^ 10), 1,
    le_max_of_le_left (by positivity), one_pos, ?_⟩
  intro M H omega N Qcentre Qside hQside f hf fL2 hfL2 u hu U hUc hUae c r hr l hrl w hcl hqdQ
    a0 ha0 hE
  have h1a : 0 < 1 - alpha := by linarith [halpha.2]
  have hp2 : (2 : ℝ) ≤ (d : ℝ) / (1 - alpha) := by
    rw [le_div_iff₀ h1a]
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have : 2 * (1 - alpha) ≤ 2 := by linarith [halpha.1]
    linarith
  have hfqd : MemLp f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
      (volume.restrict (Metric.ball w (27 * r / 2))) :=
    hf.mono_measure (Measure.restrict_mono hqdQ le_rfl)
  have : IsFiniteMeasure (volume.restrict (Metric.ball w (27 * r / 2))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hf2 : MemLp f 2 (volume.restrict (Metric.ball w (27 * r / 2))) := by
    refine hfqd.mono_exponent ?_
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal hp2
  obtain ⟨ut, F, hut, hdiv, hbud⟩ := aux_in_deterministic_core_transport_room htr M H omega N
    Qcentre Qside hQside f fL2 hfL2 u hu w r l hrl hqdQ hf2
  obtain ⟨data, hEfin, hEeq⟩ := aux_in_deterministic_core_err_room I M H omega N c w hr a0 ha0
    s hs
  have herr : paperHomogenizationError (originCube d 2) 2 (8 * s / 8)
      Homogenization.Book.Ch02.MultiscaleExponent.infinity
      (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
      data.toTriadicCoeffFamily a0 ≤ ENNReal.ofReal 1 := by
    rw [show 8 * s / 8 = s by ring, ← ENNReal.ofReal_toReal hEfin, hEeq]
    exact ENNReal.ofReal_le_ofReal hE
  obtain ⟨hUtc, hutU⟩ := aux_in_deterministic_core_rep_room U _ hUc hUae ut w hr hut hqdQ
  have hzball := aux_in_deterministic_core_zG_ball c w hr hcl
  obtain ⟨v, hvH, V, hVc, hVae, hVfr, hest⟩ := aux_in_deterministic_core_harm_gmc hd CD hD
    (8 * s) hs8 hs84 ((r / 9)⁻¹ • (c - w)) hzball
    (fun y => cutoffCoefficient M H omega N ((r / 9) • y + w)) data a0 ha0 herr ut _ hdiv
    ⟨⟨8 * s, hs8, hs81⟩, rfl,
      Section6Dirichlet.memCubeEuclideanFullWsp_centeredCubeScaledVectorDilation 1 5 _ F⟩
    _ hUtc hutU
  obtain ⟨vN, VP, h1, h2, h3, h4, h5⟩ :=
    aux_in_deterministic_core_phys_room c w hr U v hvH V hVc hVae hVfr
  refine ⟨vN, VP, h1, h2, h3, h4, ?_⟩
  rw [h5]
  rw [aux_in_deterministic_core_osc_room c w hr U, show 8 * s / 8 = s by ring, hEeq] at hest
  have hx0 : translatedCube d 0 ((r / 9)⁻¹ • (c - w)) ⊆ cube d 5 := by
    rw [aux_in_deterministic_regularity_translatedCube_eq_ball]
    refine (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall ?_)).trans
      hzball
    norm_num
  have hB0 : 0 ≤ CT * ((27 * r) ^ 2 * Real.sqrt (((27 * r) ^ d)⁻¹) *
      (eLpNorm f 2 (volume.restrict (Metric.ball w (27 * r / 2)))).toReal) := by positivity
  have hsrc := aux_in_deterministic_core_source_window (⟨8 * s, hs8, hs81⟩ : FractionalOrder) F
    ((r / 9)⁻¹ • (c - w)) hx0 _ hB0 hbud
  rw [← hKs, ← hS5] at hsrc
  have hL := aux_in_deterministic_core_L2_le_fNorm w (27 * r) (by positivity)
    ((d : ℝ) / (1 - alpha)) hp2 f hfqd
  have hG : (fractionalSeminormOn (truncatedCube d 5 0 ((r / 9)⁻¹ • (c - w))) (8 * s)
      (Section6Dirichlet.centeredCubeScaledVectorDilation 1 5 F).toField).toReal ≤
      S5 * (Ks * (CT * ((27 * r) ^ 2 * (Real.sqrt (((27 * r) ^ d)⁻¹) *
        (eLpNorm f 2 (volume.restrict (Metric.ball w (27 * r / 2)))).toReal)))) := by
    refine hsrc.trans (le_of_eq ?_)
    ring
  have hfN : 0 ≤ (eLpNorm f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
      (volume.restrict (Metric.ball w (27 * r / 2)))).toReal /
      (volume.real (Metric.ball w (27 * r / 2))) ^ (1 / ((d : ℝ) / (1 - alpha))) :=
    div_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg measureReal_nonneg _)
  exact aux_in_deterministic_core_harm_arith hCD.le hs8
    (I.err_nonneg _ _ _ _ _ _ _ _ _) (Real.sqrt_nonneg _) ha0 hKs0 hCT hr hS50 hfN rfl rfl hest
    hG hL

end SubdiffusiveProcess.Paper
end
end InDetCoreChunk_InDetCore_HarmWindow

section InDetCoreChunk_InDetCore_OneStepHelpers

/-!
# Helpers for the one-step window 

The general error identification, the fractional source bound on `□_{n+5}`, the choice of the
domain cube, and the powers-of-three bookkeeping.
-/

open MeasureTheory Set Metric Filter Topology TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal Pointwise

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable

/-- **General error identification** for the working cube `w + Q_r` seen from the domain
centre `c` at dilation `μ = r 3^{-k}`. -/
theorem aux_in_deterministic_core_err_gen {d : ℕ} (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (c w : SpatialCoordinates d) {μ r : ℝ} (hμ : 0 < μ) (hr : 0 < r) (k : ℤ)
    (hk : r * ((3 : ℝ) ^ k)⁻¹ = μ) (a0 : ℝ) (ha0 : 0 < a0) (s : ℝ)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ data : ScalarTriadicCoeffData
        (fun y => cutoffCoefficient M H omega N (μ • (y + μ⁻¹ • (w - c)) + c)),
      paperHomogenizationError (originCube d k) k s
          Homogenization.Book.Ch02.MultiscaleExponent.infinity
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
          data.toTriadicCoeffFamily a0 ≠ ⊤ ∧
      (paperHomogenizationError (originCube d k) k s
          Homogenization.Book.Ch02.MultiscaleExponent.infinity
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
          data.toTriadicCoeffFamily a0).toReal =
        I.err w r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w r a0 s 2 := by
  have hwc : μ • (μ⁻¹ • (w - c)) + c = w := by
    rw [smul_smul, mul_inv_cancel₀ hμ.ne', one_smul, sub_add_cancel]
  have hcont : Continuous
      (fun y : Vec d => cutoffCoefficient M H omega N (μ • (y + μ⁻¹ • (w - c)) + c)) :=
    (cutoffCoefficient_continuous M H omega N).comp
      (by fun_prop)
  obtain ⟨data⟩ := aux_in_deterministic_core_scalar_data hcont
    (fun y => cutoffCoefficient_pos M H omega N _)
  have ha' : ∀ᵐ y ∂volume.restrict (openCubeSet (originCube d k)),
      (fun y : Vec d => cutoffCoefficient M H omega N (μ • y + c)) (y + μ⁻¹ • (w - c)) =
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr).val
          (fun i => w i + r * ((3 : ℝ) ^ k)⁻¹ * y i) := by
    have hco := aux_in_deterministic_core_cutoff_coeFn M H omega N w hr
    have hset : translateSet w (μ • openCubeSet (originCube d k)) =
        (centeredCube w r hr : Set (SpatialCoordinates d)) := by
      rw [show openCubeSet (originCube d k) = cube d k from rfl,
        aux_in_deterministic_core_cube_eq_ball, aux_in_deterministic_core_affine_ball hμ,
        smul_zero, zero_add]
      change _ = Metric.ball w (r / 2)
      congr 1
      rw [← hk]
      field_simp
    obtain ⟨gA, hgA⟩ : ∃ gA : Vec d → ℝ,
        gA = fun x => (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr).val x := ⟨_, rfl⟩
    have hco' : gA =ᵐ[volume.restrict (translateSet w (μ • openCubeSet (originCube d k)))]
        cutoffCoefficient M H omega N := by
      rw [hset, hgA]; exact hco
    have hpb := aux_in_deterministic_core_ae_affine hμ w (openCubeSet (originCube d k)) hco'
    filter_upwards [hpb] with y hy
    rw [hgA] at hy
    have e1 : (fun i => w i + r * ((3 : ℝ) ^ k)⁻¹ * y i) = μ • y + w := by
      funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; rw [← hk]; ring
    have e2 : μ • (y + μ⁻¹ • (w - c)) + c = μ • y + w := by
      rw [smul_add, add_assoc, hwc]
    rw [e1]
    show cutoffCoefficient M H omega N (μ • (y + μ⁻¹ • (w - c)) + c) = _
    rw [e2]
    exact hy.symm
  obtain ⟨hEeq, hEfin⟩ := aux_in_deterministic_core_err_scaled I w r hr k
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr)
    (fun y : Vec d => cutoffCoefficient M H omega N (μ • y + c)) (μ⁻¹ • (w - c))
    ha' data a0 ha0 s hs
  exact ⟨data, hEfin, hEeq.symm⟩

/-- **Fractional source term on a window `x + □_n` of `□_{n+5}`** (`n ≥ 0`). -/
theorem aux_in_deterministic_core_source_window_gen {d : ℕ} [NeZero d]
    (sOrder : FractionalOrder) (F : CubeVectorH1Function (originCube d 0)) (m n : ℤ)
    (hmn : m = n + 5) (hn : 0 ≤ n) (x : Vec d)
    (hx : translatedCube d n x ⊆ cube d m) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : Section6Dirichlet.unitCubeVectorH1ENormBudget F ≤ ENNReal.ofReal B) :
    (fractionalSeminormOn (truncatedCube d m n x) sOrder.1
        (Section6Dirichlet.centeredCubeScaledVectorDilation 1 m F).toField).toReal ≤
      Real.sqrt (((3 : ℝ) ^ (5 : ℤ)) ^ d) *
        ((Section6Dirichlet.scaledVectorDatumFractionalConstant sOrder d).toReal *
          (((3 : ℝ) ^ m)⁻¹ * B)) := by
  set g := (Section6Dirichlet.centeredCubeScaledVectorDilation 1 m F).toField with hg
  have htr : truncatedCube d m n x = translatedCube d n x := Set.inter_eq_left.2 hx
  have h3n : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hvolW : volume (truncatedCube d m n x) = ENNReal.ofReal (((3 : ℝ) ^ n) ^ d) := by
    rw [htr, aux_in_deterministic_regularity_translatedCube_eq_ball,
      aux_in_deterministic_core_volume_ball x (by positivity)]
    congr 2; ring
  have hvolQ : volume (cube d m) = ENNReal.ofReal (((3 : ℝ) ^ m) ^ d) := by
    rw [aux_in_deterministic_core_cube_eq_ball, aux_in_deterministic_core_volume_ball _ (by positivity)]
    congr 2; ring
  have hQ0 : volume (cube d m) ≠ 0 := by
    rw [hvolQ]; exact ENNReal.ofReal_ne_zero_iff.2 (by positivity)
  have hQtop : volume (cube d m) ≠ ⊤ := by rw [hvolQ]; exact ENNReal.ofReal_ne_top
  have hmono := Section6HarmonicApproximation.fractionalSeminormOn_mono_set
    (show truncatedCube d m n x ⊆ cube d m from Set.inter_subset_right) hQ0 hQtop sOrder.1 g
  have hratio : (volume (truncatedCube d m n x))⁻¹ * volume (cube d m) =
      ENNReal.ofReal (((3 : ℝ) ^ (5 : ℤ)) ^ d) := by
    rw [hvolW, hvolQ, ← ENNReal.ofReal_inv_of_pos (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [hmn, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), mul_pow]
    field_simp
  rw [hratio] at hmono
  have hid : fractionalSeminormOn (cube d m) sOrder.1 g =
      paperFractionalSeminorm (originCube d m) sOrder FiniteLpExponent.two g := by
    change fractionalSeminormOn (openCubeSet (originCube d m)) sOrder.1 g = _
    have hkernel : AEStronglyMeasurable (cubeEuclideanWspKernel sOrder FiniteLpExponent.two g)
        (Gagliardo.gagliardoCubeMeasure (originCube d m)) := by
      simpa only [g] using! (Section6Dirichlet.centeredCubeScaledVectorDilationWspField 1 m sOrder F).kernel_aestronglyMeasurable
    rw [Section6HarmonicApproximation.fractionalSeminormOn_openCubeSet_eq_guarded_of_measurable
      (originCube d m) sOrder g hkernel]
    unfold paperFractionalSeminorm
    norm_num [FiniteLpExponent.two_exponent]
  have hpaper :=
    Section6Dirichlet.paperFractionalSeminorm_centeredCubeScaledVectorDilation_le_h1Budget 1 m sOrder F
  unfold Section6Dirichlet.scaledVectorDatumFractionalENormBound at hpaper
  set K := Section6Dirichlet.scaledVectorDatumFractionalConstant sOrder d with hK
  have hKtop : K ≠ ⊤ := (Section6Dirichlet.scaledVectorDatumFractionalConstant_lt_top sOrder d).ne
  have hm0 : 0 ≤ m := by rw [hmn]; linarith
  have hscale1 : (ENNReal.ofReal (centeredCubeScale m)) ^ (-sOrder.1) ≤ 1 := by
    refine ENNReal.rpow_le_one_of_one_le_of_neg ?_ (by linarith [sOrder.2.1])
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [centeredCubeScale]
    exact one_le_zpow₀ (by norm_num) hm0
  have hscale2 : ‖(1 : ℝ) * (centeredCubeScale m)⁻¹‖ₑ = ENNReal.ofReal (((3 : ℝ) ^ m)⁻¹) := by
    rw [one_mul, ← ofReal_norm, Real.norm_eq_abs, abs_of_pos]
    · rfl
    · simp only [centeredCubeScale]; positivity
  have hchain : fractionalSeminormOn (truncatedCube d m n x) sOrder.1 g ≤
      (ENNReal.ofReal (((3 : ℝ) ^ (5 : ℤ)) ^ d)) ^ (1 / 2 : ℝ) *
        (K * (ENNReal.ofReal (((3 : ℝ) ^ m)⁻¹) * ENNReal.ofReal B)) := by
    refine hmono.trans (mul_le_mul_right ?_ _)
    rw [hid]
    refine hpaper.trans ?_
    rw [hscale2]
    calc K * (ENNReal.ofReal (centeredCubeScale m)) ^ (-sOrder.1) *
          ENNReal.ofReal (((3 : ℝ) ^ m)⁻¹) * Section6Dirichlet.unitCubeVectorH1ENormBudget F
        ≤ K * 1 * ENNReal.ofReal (((3 : ℝ) ^ m)⁻¹) * ENNReal.ofReal B := by gcongr
      _ = K * (ENNReal.ofReal (((3 : ℝ) ^ m)⁻¹) * ENNReal.ofReal B) := by ring
  have hfin : (ENNReal.ofReal (((3 : ℝ) ^ (5 : ℤ)) ^ d)) ^ (1 / 2 : ℝ) *
      (K * (ENNReal.ofReal (((3 : ℝ) ^ m)⁻¹) * ENNReal.ofReal B)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top hKtop (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top))
  refine (ENNReal.toReal_mono hfin hchain).trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal hB0, ← Real.sqrt_eq_rpow]

/-- **Choice of the domain cube** of level `j + 5` inside `c + □_m` around the window. -/
theorem aux_in_deterministic_core_domain_choice {d : ℕ} (c x w : Vec d) (m j : ℤ)
    (hjm : j + 5 ≤ m) (hx : x ∈ Metric.ball c ((3 : ℝ) ^ (m - 1) / 2))
    (hxw : x ∈ Metric.ball w ((3 : ℝ) ^ (j - 3) / 2)) :
    ∃ c' : Vec d, Metric.ball c' ((3 : ℝ) ^ (j + 5) / 2) ⊆ Metric.ball c ((3 : ℝ) ^ m / 2) ∧
      Metric.closedBall x ((3 : ℝ) ^ j / 2) ⊆ Metric.ball c' ((3 : ℝ) ^ (j + 5) / 2) ∧
      w ∈ Metric.ball c' ((3 : ℝ) ^ (j + 5) / 2) := by
  rw [Metric.mem_ball] at hx hxw
  have h3 : ∀ a b : ℤ, a ≤ b → (3 : ℝ) ^ a ≤ (3 : ℝ) ^ b := fun a b hab =>
    zpow_le_zpow_right₀ (by norm_num) hab
  have hp : ∀ a : ℤ, (0 : ℝ) < (3 : ℝ) ^ a := fun a => zpow_pos (by norm_num) a
  have e1 : (3 : ℝ) ^ m = 3 * (3 : ℝ) ^ (m - 1) := by
    rw [show m = (m - 1) + 1 by ring, zpow_add_one₀ (by norm_num)]; ring_nf
  have ej : (3 : ℝ) ^ (j + 5) = 3 ^ 8 * (3 : ℝ) ^ (j - 3) := by
    rw [show j + 5 = (j - 3) + 8 by ring, zpow_add₀ (by norm_num)]; norm_num; ring
  have ej0 : (3 : ℝ) ^ (j + 5) = 3 ^ 5 * (3 : ℝ) ^ j := by
    rw [zpow_add₀ (by norm_num)]; norm_num; ring
  have hj3 := hp (j - 3)
  have hj0 := hp j
  have hm1 := hp (m - 1)
  by_cases hcase : j + 5 = m
  · refine ⟨c, le_of_eq (by rw [hcase]), ?_, ?_⟩
    · intro y hy
      rw [Metric.mem_closedBall] at hy
      rw [Metric.mem_ball]
      have : (3 : ℝ) ^ j ≤ (3 : ℝ) ^ (m - 1) := h3 _ _ (by omega)
      calc dist y c ≤ dist y x + dist x c := dist_triangle _ _ _
        _ < (3 : ℝ) ^ j / 2 + (3 : ℝ) ^ (m - 1) / 2 := by linarith
        _ ≤ (3 : ℝ) ^ (j + 5) / 2 := by rw [hcase, e1]; linarith
    · rw [Metric.mem_ball]
      have : (3 : ℝ) ^ (j - 3) ≤ (3 : ℝ) ^ (m - 1) := h3 _ _ (by omega)
      calc dist w c ≤ dist w x + dist x c := dist_triangle _ _ _
        _ < (3 : ℝ) ^ (j - 3) / 2 + (3 : ℝ) ^ (m - 1) / 2 := by
            rw [dist_comm w x]; linarith
        _ ≤ (3 : ℝ) ^ (j + 5) / 2 := by rw [hcase, e1]; linarith
  · have hjm' : j + 5 ≤ m - 1 := by omega
    have hle : (3 : ℝ) ^ (j + 5) ≤ (3 : ℝ) ^ (m - 1) := h3 _ _ hjm'
    refine ⟨x, ?_, ?_, ?_⟩
    · intro y hy
      rw [Metric.mem_ball] at hy ⊢
      calc dist y c ≤ dist y x + dist x c := dist_triangle _ _ _
        _ < (3 : ℝ) ^ (j + 5) / 2 + (3 : ℝ) ^ (m - 1) / 2 := by linarith
        _ ≤ (3 : ℝ) ^ m / 2 := by rw [e1]; linarith
    · intro y hy
      rw [Metric.mem_closedBall] at hy
      rw [Metric.mem_ball]
      calc dist y x ≤ (3 : ℝ) ^ j / 2 := hy
        _ < (3 : ℝ) ^ (j + 5) / 2 := by rw [ej0]; linarith
    · rw [Metric.mem_ball, dist_comm]
      calc dist x w < (3 : ℝ) ^ (j - 3) / 2 := hxw
        _ < (3 : ℝ) ^ (j + 5) / 2 := by rw [ej]; linarith

/-- **Powers of three** in the source term. -/
theorem aux_in_deterministic_core_pow_identity (d : ℕ) (hd : d ≠ 0) (alpha : ℝ)
    (_h1a : 0 < 1 - alpha) (j : ℤ) (h : ℕ) :
    ((3 : ℝ) ^ (j - (h : ℤ)))⁻¹ * (((3 : ℝ) ^ ((h : ℤ) + 5))⁻¹ * ((3 : ℝ) ^ (j + 5)) ^ 2) /
        (((3 : ℝ) ^ (j + 5)) ^ d) ^ (1 / ((d : ℝ) / (1 - alpha))) =
      (3 : ℝ) ^ (5 * alpha) * (3 : ℝ) ^ (alpha * (j : ℝ)) := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hd
  have z : ∀ a : ℤ, (3 : ℝ) ^ a = (3 : ℝ) ^ (a : ℝ) := fun a => (Real.rpow_intCast 3 a).symm
  rw [z, z, z]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity),
    ← Real.rpow_neg (by positivity), ← Real.rpow_neg (by positivity),
    ← Real.rpow_add (by positivity), ← Real.rpow_add (by positivity),
    ← Real.rpow_sub (by positivity), ← Real.rpow_add (by positivity)]
  congr 1
  push_cast
  field_simp
  ring

end SubdiffusiveProcess.Paper
end
end InDetCoreChunk_InDetCore_OneStepHelpers

section InDetCoreChunk_InDetCore_OneStepWindow

/-!
# The one-step window from the carrier 

`aux_in_deterministic_core_onestep_window_holds`: clause 2 of `deterministic_good_scale_input`
(through `aux_prop_folded_iteration_interior_excess_decay`) supplies the window input
`aux_in_deterministic_onestep_window` with `θ = 3^{-1/4}`.  The physical window `x + □_j` sits in
the domain cube `c' + □_{j+5}` (`c' = c` if `j + 5 = m`, `c' = x` otherwise), which is the GMC
cube `□_{h+5}` under `y ↦ 3^{j-h} y + c'`.
-/

open MeasureTheory Set Metric Filter Topology TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal Pointwise

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable

/-- The domain cube under the affine map. -/
theorem aux_in_deterministic_core_domain_img {d : ℕ} (c' : Vec d) (j : ℤ) (h : ℕ) :
    translateSet c' (((3 : ℝ) ^ (j - (h : ℤ))) • cube d ((h + 5 : ℕ) : ℤ)) =
      Metric.ball c' ((3 : ℝ) ^ (j + 5) / 2) := by
  rw [aux_in_deterministic_core_cube_eq_ball, aux_in_deterministic_core_affine_ball
    (zpow_pos (by norm_num) _), smul_zero, zero_add]
  congr 1
  rw [← mul_div_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  congr 2
  push_cast
  ring

/-- Windows under the affine map. -/
theorem aux_in_deterministic_core_window_img {d : ℕ} (c' x : Vec d) (j n : ℤ) (h : ℕ) :
    translateSet c' (((3 : ℝ) ^ (j - (h : ℤ))) •
        Metric.ball (((3 : ℝ) ^ (j - (h : ℤ)))⁻¹ • (x - c')) ((3 : ℝ) ^ n / 2)) =
      translatedCube d (j - (h : ℤ) + n) x := by
  rw [aux_in_deterministic_core_affine_ball (zpow_pos (by norm_num) _), smul_smul,
    mul_inv_cancel₀ (zpow_ne_zero _ (by norm_num)), one_smul, sub_add_cancel,
    aux_in_deterministic_regularity_translatedCube_eq_ball]
  congr 1
  rw [← mul_div_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]

theorem aux_in_deterministic_core_domain_scale (j : ℤ) (h : ℕ) :
    (3 : ℝ) ^ (j + 5) * ((3 : ℝ) ^ ((h + 5 : ℕ) : ℤ))⁻¹ = (3 : ℝ) ^ (j - (h : ℤ)) := by
  rw [← zpow_neg, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  congr 1
  push_cast
  ring

/-- Transport to the domain cube of the window. -/
theorem aux_in_deterministic_core_transport_domain {d : ℕ} [NeZero d] {CT : ℝ}
    (htr : aux_in_deterministic_core_transport_prop d CT)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ)
    (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
    (f : SpatialCoordinates d → ℝ) (fL2 : DomainL2 (centeredCube Qcentre Qside hQside))
    (hfL2 : ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] f))
    (u : weakSobolevGraph (centeredCube Qcentre Qside hQside))
    (hu : ∀ psi : killedSobolevGraph (centeredCube Qcentre Qside hQside),
        sobolevCoefficientForm
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
          (u : SobolevData (centeredCube Qcentre Qside hQside))
          (psi : SobolevData (centeredCube Qcentre Qside hQside)) =
        sobolevVolumeLoad fL2 (psi : SobolevData (centeredCube Qcentre Qside hQside)))
    (c' : SpatialCoordinates d) (j : ℤ) (h : ℕ)
    (hdomQ : Metric.ball c' ((3 : ℝ) ^ (j + 5) / 2) ⊆
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
    (hf2 : MemLp f 2 (volume.restrict (Metric.ball c' ((3 : ℝ) ^ (j + 5) / 2)))) :
    ∃ (ut : H1Function (openCubeSet (originCube d ((h + 5 : ℕ) : ℤ))))
      (F : CubeVectorH1Function (originCube d 0)),
      (∀ y, ut.toFun y = ((u : SobolevData (centeredCube Qcentre Qside hQside)).1 :
          SpatialCoordinates d → ℝ) (((3 : ℝ) ^ (j - (h : ℤ))) • y + c')) ∧
      IsDivFormWeakSolutionOn
        (fun y => cutoffCoefficient M H omega N (((3 : ℝ) ^ (j - (h : ℤ))) • y + c'))
        (cube d ((h + 5 : ℕ) : ℤ)) ut
        (Section6Dirichlet.centeredCubeScaledVectorDilation 1 ((h + 5 : ℕ) : ℤ) F).toField ∧
      Section6Dirichlet.unitCubeVectorH1ENormBudget F ≤
        ENNReal.ofReal (CT * (((3 : ℝ) ^ (j + 5)) ^ 2 * Real.sqrt ((((3 : ℝ) ^ (j + 5)) ^ d)⁻¹) *
          (eLpNorm f 2 (volume.restrict (Metric.ball c' ((3 : ℝ) ^ (j + 5) / 2)))).toReal)) := by
  have hS : ∀ y : Vec d, ((3 : ℝ) ^ (j + 5)) • (((3 : ℝ) ^ ((h + 5 : ℕ) : ℤ))⁻¹ • y) + c' =
      ((3 : ℝ) ^ (j - (h : ℤ))) • y + c' := by
    intro y; rw [smul_smul, aux_in_deterministic_core_domain_scale]
  obtain ⟨ut, F, hut, hdiv, hbud⟩ := htr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
    (cutoffCoefficient M H omega N)
    (aux_in_deterministic_core_cutoff_coeFn M H omega N Qcentre hQside)
    f fL2 hfL2 u hu c' (j + 5) ((h + 5 : ℕ) : ℤ) hdomQ hf2
  refine ⟨ut, F, fun y => by rw [hut y, hS y], ?_, hbud⟩
  have hfun : (fun y => cutoffCoefficient M H omega N
      (((3 : ℝ) ^ (j + 5)) • (((3 : ℝ) ^ ((h + 5 : ℕ) : ℤ))⁻¹ • y) + c')) =
      fun y => cutoffCoefficient M H omega N (((3 : ℝ) ^ (j - (h : ℤ))) • y + c') := by
    funext y; rw [hS]
  rw [hfun] at hdiv
  exact hdiv

/-- The continuous representative, pulled back to the GMC domain cube. -/
theorem aux_in_deterministic_core_rep_gen {d : ℕ} {Ω : Set (Vec d)} {M' : ℤ}
    (U V0 : Vec d → ℝ) (hUae : V0 =ᵐ[volume.restrict Ω] U)
    (ut : H1Function (openCubeSet (originCube d M'))) (c' : Vec d) {μ : ℝ} (hμ : 0 < μ)
    (hut : ∀ y, ut.toFun y = V0 (μ • y + c'))
    (hdom : translateSet c' (μ • cube d M') ⊆ Ω) :
    ut.toFun =ᵐ[volume.restrict (cube d M')] (fun y => U (μ • y + c')) := by
  have h1 : ∀ᵐ q ∂volume.restrict (translateSet c' (μ • cube d M')), V0 q = U q :=
    ae_restrict_of_ae_restrict_of_subset hdom hUae
  filter_upwards [aux_in_deterministic_core_ae_affine hμ c' (cube d M') h1] with y hy
  rw [hut y]
  exact hy

/-- The final arithmetic of the one-step window. -/
theorem aux_in_deterministic_core_onestep_arith
    {X0 Xj E S G μ C A A3 sD a0 P8 Ks S5 CT J2 L V p Q P5 Pα fpd fp θh E0 r : ℝ}
    (hμ : 0 < μ) (hXj : 0 ≤ Xj) (hC : 0 ≤ C) (hsD : 0 < sD) (hA3 : 0 ≤ A3) (ha0 : 0 < a0)
    (hP8 : 0 ≤ P8) (hKs : 0 ≤ Ks) (hS5 : 0 ≤ S5) (hCT : 0 ≤ CT) (hQ : 0 < Q) (hJ2 : 0 ≤ J2)
    (hVp : 0 < V ^ (1 / p)) (_hP5 : 0 ≤ P5) (_hPα : 0 ≤ Pα)
    (hmain : μ * X0 ≤ C * (r + A * E0) * (μ * Xj) +
      C * A3 * sD ^ (-3 / 2 : ℝ) * E * (μ * S) + C * sD ^ (-15 / 2 : ℝ) * A3 * a0⁻¹ * P8 * G)
    (hA : A = A3 * sD ^ (-3 / 2 : ℝ))
    (hcontr : C * (r + A * E0) ≤ θh)
    (hG : G ≤ S5 * (Ks * (Q⁻¹ * (CT * (J2 * L)))))
    (hL : L ≤ fpd / V ^ (1 / p))
    (hfpd : fpd ≤ fp)
    (hpow : μ⁻¹ * (Q⁻¹ * J2) / V ^ (1 / p) = P5 * Pα) :
    X0 ≤ θh * Xj + C * A * E * S +
      C * sD ^ (-15 / 2 : ℝ) * A3 * P8 * (S5 * (Ks * CT)) * P5 * a0⁻¹ * Pα * fp := by
  have hK : 0 ≤ C * sD ^ (-15 / 2 : ℝ) * A3 * a0⁻¹ * P8 := by positivity
  have h1 : X0 ≤ C * (r + A * E0) * Xj + C * A3 * sD ^ (-3 / 2 : ℝ) * E * S +
      μ⁻¹ * (C * sD ^ (-15 / 2 : ℝ) * A3 * a0⁻¹ * P8 * G) := by
    have e : C * (r + A * E0) * (μ * Xj) + C * A3 * sD ^ (-3 / 2 : ℝ) * E * (μ * S) +
        C * sD ^ (-15 / 2 : ℝ) * A3 * a0⁻¹ * P8 * G =
        μ * (C * (r + A * E0) * Xj + C * A3 * sD ^ (-3 / 2 : ℝ) * E * S) +
          C * sD ^ (-15 / 2 : ℝ) * A3 * a0⁻¹ * P8 * G := by ring
    rw [e] at hmain
    have h' : X0 - (C * (r + A * E0) * Xj + C * A3 * sD ^ (-3 / 2 : ℝ) * E * S) ≤
        (C * sD ^ (-15 / 2 : ℝ) * A3 * a0⁻¹ * P8 * G) / μ := by
      rw [le_div_iff₀ hμ]
      have e2 : (X0 - (C * (r + A * E0) * Xj + C * A3 * sD ^ (-3 / 2 : ℝ) * E * S)) * μ =
          μ * X0 - μ * (C * (r + A * E0) * Xj + C * A3 * sD ^ (-3 / 2 : ℝ) * E * S) := by ring
      rw [e2]; linarith
    rw [div_eq_inv_mul (C * sD ^ (-15 / 2 : ℝ) * A3 * a0⁻¹ * P8 * G) μ] at h'
    linarith
  have h2 : C * (r + A * E0) * Xj ≤ θh * Xj := mul_le_mul_of_nonneg_right hcontr hXj
  have h3 : C * A3 * sD ^ (-3 / 2 : ℝ) * E * S = C * A * E * S := by rw [hA]; ring
  have hL' : J2 * L ≤ J2 * (fp / V ^ (1 / p)) :=
    mul_le_mul_of_nonneg_left (hL.trans (div_le_div_of_nonneg_right hfpd hVp.le)) hJ2
  have hG' : G ≤ S5 * (Ks * (Q⁻¹ * (CT * (J2 * (fp / V ^ (1 / p)))))) := by
    refine hG.trans ?_
    gcongr
  have h4 : μ⁻¹ * (C * sD ^ (-15 / 2 : ℝ) * A3 * a0⁻¹ * P8 * G) ≤
      C * sD ^ (-15 / 2 : ℝ) * A3 * P8 * (S5 * (Ks * CT)) * P5 * a0⁻¹ * Pα * fp := by
    calc μ⁻¹ * (C * sD ^ (-15 / 2 : ℝ) * A3 * a0⁻¹ * P8 * G)
        ≤ μ⁻¹ * (C * sD ^ (-15 / 2 : ℝ) * A3 * a0⁻¹ * P8 *
            (S5 * (Ks * (Q⁻¹ * (CT * (J2 * (fp / V ^ (1 / p)))))))) := by
          gcongr
      _ = C * sD ^ (-15 / 2 : ℝ) * A3 * P8 * (S5 * (Ks * CT)) * a0⁻¹ * fp *
            (μ⁻¹ * (Q⁻¹ * J2) / V ^ (1 / p)) := by
          simp only [div_eq_mul_inv]; ring
      _ = C * sD ^ (-15 / 2 : ℝ) * A3 * P8 * (S5 * (Ks * CT)) * P5 * a0⁻¹ * Pα * fp := by
          rw [hpow]; ring
  linarith

/-- **The one-step window at one window** (all constants fixed in advance). -/
theorem aux_in_deterministic_core_onestep_at {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) {C CT : ℝ} (hC : 0 < C) (hCT : 0 ≤ CT)
    (hstep : aux_in_deterministic_core_step d C)
    (htr : aux_in_deterministic_core_transport_prop d CT)
    (alpha s : ℝ) (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (hsSmall : s ≤ (1 / 32 : ℝ)) (h : ℕ) (hh : 0 < h) (E0 θh : ℝ) (hE0 : 0 < E0)
    (hE01 : E0 ≤ 1)
    (hcontr : C * ((3 : ℝ) ^ (-(h : ℝ) / 2) +
      ((3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) * (8 * s) ^ (-3 / 2 : ℝ)) * E0) ≤ θh)
    (Ks S5 : ℝ) (hs8 : 0 < 8 * s) (hs81 : 8 * s < 1)
    (hKs : Ks = (Section6Dirichlet.scaledVectorDatumFractionalConstant
      (⟨8 * s, hs8, hs81⟩ : FractionalOrder) d).toReal)
    (hS5 : S5 = Real.sqrt (((3 : ℝ) ^ (5 : ℤ)) ^ d))
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ)
    (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
    (c : SpatialCoordinates d) (m : ℤ)
    (hcQ : Metric.ball c ((3 : ℝ) ^ m / 2) ⊆
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
    (f : SpatialCoordinates d → ℝ)
    (hf : MemLp f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
      (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
    (fL2 : DomainL2 (centeredCube Qcentre Qside hQside))
    (hfL2 : ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] f))
    (u : weakSobolevGraph (centeredCube Qcentre Qside hQside))
    (hu : ∀ psi : killedSobolevGraph (centeredCube Qcentre Qside hQside),
        sobolevCoefficientForm
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
          (u : SobolevData (centeredCube Qcentre Qside hQside))
          (psi : SobolevData (centeredCube Qcentre Qside hQside)) =
        sobolevVolumeLoad fL2 (psi : SobolevData (centeredCube Qcentre Qside hQside)))
    (U : SpatialCoordinates d → ℝ)
    (hUae : (((u : SobolevData (centeredCube Qcentre Qside hQside)).1 :
        SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] U))
    (x : SpatialCoordinates d) (hx : x ∈ Metric.ball c ((3 : ℝ) ^ (m - 1) / 2))
    (j l : ℤ) (hjm : j + 5 ≤ m) (hjl : j = -l - 2)
    (w : SpatialCoordinates d) (hxw : x ∈ Metric.ball w ((3 : ℝ) ^ (j - 3) / 2))
    (a0 : ℝ) (ha0 : 0 < a0)
    (hE : I.err w ((3 : ℝ) ^ (-l)) (by positivity)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
        w ((3 : ℝ) ^ (-l)) a0 s 2 ≤ E0)
    (ell : Affine d) (hell : ell ∈ affineMinimizers (translatedCube d j x) U) :
    excess (j - (h : ℤ)) (translatedCube d (j - (h : ℤ)) x) U ≤
      θh * excess j (translatedCube d j x) U +
        C * ((3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) * (8 * s) ^ (-3 / 2 : ℝ)) *
          I.err w ((3 : ℝ) ^ (-l)) (by positivity)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
            w ((3 : ℝ) ^ (-l)) a0 s 2 * Real.sqrt (vecNormSq ell.slope) +
        C * (8 * s) ^ (-15 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) *
          (3 : ℝ) ^ ((8 * s) * h) * (S5 * (Ks * CT)) * (3 : ℝ) ^ (5 * alpha) * a0⁻¹ *
          (3 : ℝ) ^ (alpha * (j : ℝ)) *
          (eLpNorm f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
            (volume.restrict (Metric.ball c ((3 : ℝ) ^ m / 2)))).toReal := by
  have hsD4 : 8 * s ≤ 1 / 4 := by linarith
  have h1a : 0 < 1 - alpha := by linarith [halpha.2]
  have hp2 : (2 : ℝ) ≤ (d : ℝ) / (1 - alpha) := by
    rw [le_div_iff₀ h1a]
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have : 2 * (1 - alpha) ≤ 2 := by linarith [halpha.1]
    linarith
  obtain ⟨c', hdom, hxdom, hwdom⟩ :=
    aux_in_deterministic_core_domain_choice c x w m j hjm hx hxw
  have hdomQ := hdom.trans hcQ
  have hμ : (0 : ℝ) < (3 : ℝ) ^ (j - (h : ℤ)) := zpow_pos (by norm_num) _
  have hfdom : MemLp f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
      (volume.restrict (Metric.ball c' ((3 : ℝ) ^ (j + 5) / 2))) :=
    hf.mono_measure (Measure.restrict_mono hdomQ le_rfl)
  have : IsFiniteMeasure (volume.restrict (Metric.ball c' ((3 : ℝ) ^ (j + 5) / 2))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hf2 : MemLp f 2 (volume.restrict (Metric.ball c' ((3 : ℝ) ^ (j + 5) / 2))) := by
    refine hfdom.mono_exponent ?_
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal hp2
  obtain ⟨ut, F, hut, hdiv, hbud⟩ := aux_in_deterministic_core_transport_domain htr M H omega N
    Qcentre Qside hQside f fL2 hfL2 u hu c' j h hdomQ hf2
  have hr : (0 : ℝ) < (3 : ℝ) ^ (-l) := zpow_pos (by norm_num) _
  have hk : (3 : ℝ) ^ (-l) * ((3 : ℝ) ^ ((h : ℤ) + 2))⁻¹ = (3 : ℝ) ^ (j - (h : ℤ)) := by
    rw [← zpow_neg, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]; congr 1; omega
  obtain ⟨data, hEfin, hEeq⟩ := aux_in_deterministic_core_err_gen I M H omega N c' w hμ hr
    ((h : ℤ) + 2) hk a0 ha0 s hs
  have herr : paperHomogenizationError (originCube d ((h : ℤ) + 2)) ((h : ℤ) + 2) (8 * s / 8)
      Homogenization.Book.Ch02.MultiscaleExponent.infinity
      (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
      data.toTriadicCoeffFamily a0 ≤ ENNReal.ofReal (1 * E0) := by
    rw [show 8 * s / 8 = s by ring, ← ENNReal.ofReal_toReal hEfin, hEeq, one_mul]
    exact ENNReal.ofReal_le_ofReal hE
  have hdomimg := aux_in_deterministic_core_domain_img (d := d) c' j h
  have hxc' : ((3 : ℝ) ^ (j - (h : ℤ))) • (((3 : ℝ) ^ (j - (h : ℤ)))⁻¹ • (x - c')) + c' = x := by
    rw [smul_smul, mul_inv_cancel₀ hμ.ne', one_smul, sub_add_cancel]
  have hxG : Metric.closedBall (((3 : ℝ) ^ (j - (h : ℤ)))⁻¹ • (x - c')) ((3 : ℝ) ^ (h : ℤ) / 2) ⊆
      cube d ((h + 5 : ℕ) : ℤ) := by
    intro y hy
    have h1 : ((3 : ℝ) ^ (j - (h : ℤ))) • y + c' ∈ Metric.closedBall x ((3 : ℝ) ^ j / 2) := by
      rw [Metric.mem_closedBall, ← hxc', aux_in_deterministic_core_dist_affine hμ]
      rw [Metric.mem_closedBall] at hy
      calc (3 : ℝ) ^ (j - (h : ℤ)) * dist y (((3 : ℝ) ^ (j - (h : ℤ)))⁻¹ • (x - c')) ≤
            (3 : ℝ) ^ (j - (h : ℤ)) * ((3 : ℝ) ^ (h : ℤ) / 2) :=
            mul_le_mul_of_nonneg_left hy hμ.le
        _ = (3 : ℝ) ^ j / 2 := by
            rw [← mul_div_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), sub_add_cancel]
    have h2 := hxdom h1
    rw [← hdomimg, mem_translateSet_iff_sub_mem, add_sub_cancel_right] at h2
    exact (Set.smul_mem_smul_set_iff₀ hμ.ne' _ _).1 h2
  have hzG : ((3 : ℝ) ^ (j - (h : ℤ)))⁻¹ • (w - c') ∈ cube d ((h + 5 : ℕ) : ℤ) := by
    have h2 := hwdom
    rw [← hdomimg, mem_translateSet_iff_sub_mem] at h2
    rw [← Set.smul_mem_smul_set_iff₀ hμ.ne', smul_smul, mul_inv_cancel₀ hμ.ne', one_smul]
    exact h2
  have hxz : ((3 : ℝ) ^ (j - (h : ℤ)))⁻¹ • (x - c') ∈
      Metric.ball (((3 : ℝ) ^ (j - (h : ℤ)))⁻¹ • (w - c')) ((3 : ℝ) ^ ((h : ℤ) - 3) / 2) := by
    rw [Metric.mem_ball, aux_in_deterministic_core_dist_affine_inv hμ]
    rw [Metric.mem_ball] at hxw
    calc ((3 : ℝ) ^ (j - (h : ℤ)))⁻¹ * dist x w <
          ((3 : ℝ) ^ (j - (h : ℤ)))⁻¹ * ((3 : ℝ) ^ (j - 3) / 2) :=
          mul_lt_mul_of_pos_left hxw (inv_pos.2 hμ)
      _ = (3 : ℝ) ^ ((h : ℤ) - 3) / 2 := by
          rw [← mul_div_assoc, ← zpow_neg, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
          congr 2; ring
  have hutU := aux_in_deterministic_core_rep_gen U _ hUae ut c' hμ hut (by rw [hdomimg]; exact hdomQ)
  have hwin : translateSet c' (((3 : ℝ) ^ (j - (h : ℤ))) •
      Metric.ball (((3 : ℝ) ^ (j - (h : ℤ)))⁻¹ • (x - c')) ((3 : ℝ) ^ (h : ℤ) / 2)) =
      translatedCube d j x := by
    rw [aux_in_deterministic_core_window_img c' x j (h : ℤ) h, sub_add_cancel]
  have hellG := aux_in_deterministic_core_affineMinimizers_pull hμ c'
    (Metric.ball (((3 : ℝ) ^ (j - (h : ℤ)))⁻¹ • (x - c')) ((3 : ℝ) ^ (h : ℤ) / 2)) U ell
    (by rw [hwin]; exact hell)
  have hmain := aux_in_deterministic_core_onestep_gmc C hstep (8 * s) hs8 hsD4 E0 hE0.le hE01 h hh
    _ _ hxG hzG hxz (fun y => cutoffCoefficient M H omega N (((3 : ℝ) ^ (j - (h : ℤ))) • y + c'))
    data a0 ha0 herr ut _ hdiv
    ⟨⟨8 * s, hs8, hs81⟩, rfl,
      Section6Dirichlet.memCubeEuclideanFullWsp_centeredCubeScaledVectorDilation 1 _ _ F⟩
    _ hutU _ hellG
  -- back to physical windows
  have hw0 : translateSet c' (((3 : ℝ) ^ (j - (h : ℤ))) •
      Metric.ball (((3 : ℝ) ^ (j - (h : ℤ)))⁻¹ • (x - c')) (1 / 2)) =
      translatedCube d (j - (h : ℤ)) x := by
    have := aux_in_deterministic_core_window_img (d := d) c' x j 0 h
    rw [zpow_zero, add_zero] at this
    exact this
  have eL := aux_in_deterministic_core_excess_affine hμ c'
    (Metric.ball (((3 : ℝ) ^ (j - (h : ℤ)))⁻¹ • (x - c')) (1 / 2)) U 0 (j - (h : ℤ))
  rw [hw0, sub_zero] at eL
  have eR := aux_in_deterministic_core_excess_affine hμ c'
    (Metric.ball (((3 : ℝ) ^ (j - (h : ℤ)))⁻¹ • (x - c')) ((3 : ℝ) ^ (h : ℤ) / 2)) U (h : ℤ) j
  rw [hwin] at eR
  have eS := aux_in_deterministic_core_affinePull_slope hμ c' ell
  rw [eL, eR, eS, show 8 * s / 8 = s by ring, hEeq] at hmain
  -- the source
  have hx0 : translatedCube d (h : ℤ) (((3 : ℝ) ^ (j - (h : ℤ)))⁻¹ • (x - c')) ⊆
      cube d ((h + 5 : ℕ) : ℤ) := by
    rw [aux_in_deterministic_regularity_translatedCube_eq_ball]
    exact Metric.ball_subset_closedBall.trans hxG
  have hB0 : 0 ≤ CT * (((3 : ℝ) ^ (j + 5)) ^ 2 * Real.sqrt ((((3 : ℝ) ^ (j + 5)) ^ d)⁻¹) *
      (eLpNorm f 2 (volume.restrict (Metric.ball c' ((3 : ℝ) ^ (j + 5) / 2)))).toReal) := by
    positivity
  have hsrc := aux_in_deterministic_core_source_window_gen (⟨8 * s, hs8, hs81⟩ : FractionalOrder) F
    ((h + 5 : ℕ) : ℤ) (h : ℤ) (by push_cast; ring) (by positivity) _ hx0 _ hB0 hbud
  rw [← hKs, ← hS5] at hsrc
  have hL := aux_in_deterministic_core_L2_le_fNorm c' ((3 : ℝ) ^ (j + 5)) (zpow_pos (by norm_num) _)
    ((d : ℝ) / (1 - alpha)) hp2 f hfdom
  have hvol : volume.real (Metric.ball c' ((3 : ℝ) ^ (j + 5) / 2)) = ((3 : ℝ) ^ (j + 5)) ^ d := by
    rw [Measure.real, aux_in_deterministic_core_volume_ball c' (by positivity),
      ENNReal.toReal_ofReal (by positivity)]
    congr 1; ring
  rw [hvol] at hL
  have hfpd : (eLpNorm f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
      (volume.restrict (Metric.ball c' ((3 : ℝ) ^ (j + 5) / 2)))).toReal ≤
      (eLpNorm f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
        (volume.restrict (Metric.ball c ((3 : ℝ) ^ m / 2)))).toReal := by
    have hfc : MemLp f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
        (volume.restrict (Metric.ball c ((3 : ℝ) ^ m / 2))) :=
      hf.mono_measure (Measure.restrict_mono hcQ le_rfl)
    exact ENNReal.toReal_mono hfc.eLpNorm_ne_top (eLpNorm_mono_measure _ (Measure.restrict_mono hdom le_rfl))
  have hpow := aux_in_deterministic_core_pow_identity d (NeZero.ne d) alpha h1a j h
  have hcast : ((h + 5 : ℕ) : ℤ) = (h : ℤ) + 5 := by push_cast; ring
  rw [← hcast] at hpow
  have hG : (fractionalSeminormOn (truncatedCube d ((h + 5 : ℕ) : ℤ) (h : ℤ)
      (((3 : ℝ) ^ (j - (h : ℤ)))⁻¹ • (x - c'))) (8 * s)
      (Section6Dirichlet.centeredCubeScaledVectorDilation 1 ((h + 5 : ℕ) : ℤ) F).toField).toReal ≤
      S5 * (Ks * (((3 : ℝ) ^ ((h + 5 : ℕ) : ℤ))⁻¹ * (CT * (((3 : ℝ) ^ (j + 5)) ^ 2 *
        (Real.sqrt ((((3 : ℝ) ^ (j + 5)) ^ d)⁻¹) *
          (eLpNorm f 2 (volume.restrict (Metric.ball c' ((3 : ℝ) ^ (j + 5) / 2)))).toReal))))) := by
    refine hsrc.trans (le_of_eq ?_)
    ring
  have hXj : 0 ≤ excess j (translatedCube d j x) U := by
    unfold excess
    refine mul_nonneg (zpow_pos (by norm_num) _).le (Real.sInf_nonneg ?_)
    rintro r ⟨ell', rfl⟩
    exact Real.sqrt_nonneg _
  exact aux_in_deterministic_core_onestep_arith hμ hXj hC.le hs8 (by positivity) ha0
    (by positivity) (by rw [hKs]; exact ENNReal.toReal_nonneg) (by rw [hS5]; positivity) hCT
    (zpow_pos (by norm_num) _) (by positivity) (by positivity) (by positivity) (by positivity)
    hmain rfl hcontr hG hL hfpd hpow

end SubdiffusiveProcess.Paper
end
end InDetCoreChunk_InDetCore_OneStepWindow

section InDetCoreChunk_InDetCore_OneStepMain

/-!
# The window input `aux_in_deterministic_onestep_window` from the carrier 
-/

open MeasureTheory Set Metric Filter Topology TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal Pointwise

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable

/-- **The one-step window from clause 2 of the carrier**, with `θ = 3^{-1/4}`. -/
theorem aux_in_deterministic_core_onestep_window_holds (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (D : _root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d)
    (alpha s : ℝ) (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (hsSmall : s ≤ (1 / 32 : ℝ)) :
    ∃ (h : ℕ) (theta Ceps Cdel E0 : ℝ), 0 < h ∧ theta ∈ Set.Ioo (0 : ℝ) 1 ∧
      theta ^ h ∈ Set.Ioo (0 : ℝ) (3 / 5) ∧ 0 < E0 ∧ 0 ≤ Ceps ∧ 0 ≤ Cdel ∧
      aux_in_deterministic_onestep_window d I alpha s h theta Ceps Cdel E0 := by
  obtain ⟨C, hC, hstep⟩ := aux_in_deterministic_core_step_of_det d hd D
  obtain ⟨CT, hCT, htr⟩ := aux_in_deterministic_core_transport d
  obtain ⟨h, hh, hth35, hthC⟩ := aux_prop_folded_iteration_step_choice C
  have hs8 : 0 < 8 * s := by linarith [hs.1]
  have hs81 : 8 * s < 1 := by linarith
  have hθ0 : 0 < (3 : ℝ) ^ (-(1 / 4 : ℝ)) := by positivity
  have hθ1 : (3 : ℝ) ^ (-(1 / 4 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hA : 0 < (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) * (8 * s) ^ (-3 / 2 : ℝ) := by positivity
  obtain ⟨hE0, hE01, hcontr⟩ := aux_prop_folded_iteration_eta_choice hC hA (pow_pos hθ0 h) hthC
  obtain ⟨Ks, hKs⟩ : ∃ Ks : ℝ, Ks = (Section6Dirichlet.scaledVectorDatumFractionalConstant
      (⟨8 * s, hs8, hs81⟩ : FractionalOrder) d).toReal := ⟨_, rfl⟩
  obtain ⟨S5, hS5⟩ : ∃ S5 : ℝ, S5 = Real.sqrt (((3 : ℝ) ^ (5 : ℤ)) ^ d) := ⟨_, rfl⟩
  have hKs0 : 0 ≤ Ks := by rw [hKs]; exact ENNReal.toReal_nonneg
  have hS50 : 0 ≤ S5 := by rw [hS5]; exact Real.sqrt_nonneg _
  refine ⟨h, (3 : ℝ) ^ (-(1 / 4 : ℝ)),
    C * ((3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) * (8 * s) ^ (-3 / 2 : ℝ)),
    C * (8 * s) ^ (-15 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) * (3 : ℝ) ^ ((8 * s) * h) *
      (S5 * (Ks * CT)) * (3 : ℝ) ^ (5 * alpha),
    min 1 (((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ h /
      (2 * C * ((3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) * (8 * s) ^ (-3 / 2 : ℝ)))),
    hh, ⟨hθ0, hθ1⟩, ⟨pow_pos hθ0 h, hth35⟩, hE0, by positivity, by positivity, ?_⟩
  intro M H omega N Qcentre Qside hQside c m hcQ f hf fL2 hfL2 u hu U _hUc hUae x hx j l hjm
    hjl w _hw hxw a0 ha0 hE ell hell
  exact aux_in_deterministic_core_onestep_at hd I hC hCT hstep htr alpha s halpha hs hsSmall h hh
    _ _ hE0 hE01 hcontr Ks S5 hs8 hs81 hKs hS5 M H omega N Qcentre Qside hQside c m hcQ f hf fL2
    hfL2 u hu U hUae x hx j l hjm hjl w hxw a0 ha0 hE ell hell

end SubdiffusiveProcess.Paper
end
end InDetCoreChunk_InDetCore_OneStepMain

section InDetCoreChunk_InDetCore_Final

/-!
# `in_deterministic` R1 and R2 from the carried deterministic input 
-/

open MeasureTheory Set Metric Filter Topology TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal Pointwise

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- **R1 and R2** of `in_deterministic` from `deterministic_good_scale_input`. -/
theorem aux_in_deterministic_core_R12 (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (D : _root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d)
    (alpha beta s sigma cell epshom : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hsSmall : s ≤ (1 / 32 : ℝ))
    (hepshom : 0 < epshom) :
    ∃ C1 : ℝ, 1 ≤ C1 ∧ ∀ Cbound : ℝ, C1 ≤ Cbound →
      ∃ e1 l1 d1 : ℝ, 0 < e1 ∧ 0 < l1 ∧ 0 < d1 ∧
      ∀ eps0 lam0 delta0 : ℝ, 0 < eps0 → eps0 ≤ e1 → 0 < lam0 → lam0 ≤ l1 →
        0 < delta0 → delta0 ≤ d1 →
        aux_in_deterministic_regularity_R1 d I alpha beta s sigma cell epshom
          Cbound eps0 lam0 delta0 ∧
        aux_in_deterministic_regularity_R2 d I alpha beta s sigma cell epshom
          Cbound eps0 lam0 delta0 := by
  obtain ⟨h, θ, Ceps, Cdel, E0, hh, hθ, hθh, hE0, hCeps, hCdel, hOS⟩ :=
    aux_in_deterministic_core_onestep_window_holds d hd I D alpha s halpha hs hsSmall
  obtain ⟨Charm, Eh, hCharm, hEh, hHW⟩ :=
    aux_in_deterministic_core_harm_window_holds d hd I D alpha s halpha hs hsSmall
  exact aux_in_deterministic_core_R12_of_windows d hd I alpha beta s sigma cell epshom halpha hs
    hsSmall hepshom h θ Ceps Cdel E0 hh hθ hθh hE0 hCeps hCdel hOS Charm Eh hCharm hEh hHW

end SubdiffusiveProcess.Paper
end
end InDetCoreChunk_InDetCore_Final


set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

section R4
open MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
namespace SubdiffusiveProcess.Paper

theorem aux_in_deterministic_trace_infimum_sq
    (S : Set ℝ) (hSne : S.Nonempty) (hSnn : ∀ x ∈ S, 0 ≤ x)
    (R K : ℝ) (hR : 0 ≤ R) (hK : 0 < K)
    (hbound : ∀ x ∈ S, R ≤ K * x ^ 2) :
    R ≤ K * (sInf S) ^ 2 := by
  have hInf0 : 0 ≤ sInf S := le_csInf hSne hSnn
  have hroot : Real.sqrt (R / K) ≤ sInf S := by
    apply le_csInf hSne
    intro x hx
    have hx0 := hSnn x hx
    have hq : R / K ≤ x ^ 2 := (div_le_iff₀ hK).2 (by simpa [mul_comm] using hbound x hx)
    nlinarith [Real.sq_sqrt (div_nonneg hR hK.le), Real.sqrt_nonneg (R / K)]
  have hsq : R / K ≤ (sInf S) ^ 2 := by
    nlinarith [Real.sq_sqrt (div_nonneg hR hK.le), Real.sqrt_nonneg (R / K)]
  simpa [mul_comm] using (div_le_iff₀ hK).1 hsq

theorem aux_in_deterministic_killed_response_space_eq
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (hS : S.space = killedSobolevGraph Ω) :
    S = killedResponseSpace (hS ▸ S.poincare) := by
  cases S with
  | mk space le_weak closed poincare =>
    dsimp at hS ⊢
    cases hS
    rfl

theorem aux_in_deterministic_trace_right_inverse_physical
    {d : ℕ} (hd : 2 ≤ d) (S : SobolevFoundationalInput d hd)
    (beta : ℝ) (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (b : SpatialCoordinates d → ℝ)
    (hb : IsCellBoundaryClass beta z r b) :
    ∃ (extension : weakSobolevGraph (centeredCube z r hr))
      (B : SpatialCoordinates d → ℝ),
      ContinuousOn B (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
      (((extension : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] B) ∧
      (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), B x = b x) := by
  let G := rescaledDatum z r b
  obtain ⟨v, U, hUc, hrep, htrace, -, -⟩ :=
    S.traceRightInverse beta hbeta 0 1 one_pos rfl G hb.1
  obtain ⟨extension, hpush⟩ := aux_lem_extension_weak_pushforward z hr one_pos v
  let B : SpatialCoordinates d → ℝ := fun y => U (r⁻¹ • (y - z))
  refine ⟨extension, B, ?_, ?_, ?_⟩
  · have hB : Continuous B := by
      dsimp [B]
      fun_prop
    exact hB.continuousOn
  · apply (aux_lem_extension_ae_dilation_iff z hr one_pos _).2
    filter_upwards [hpush, hrep] with x hx hux
    simpa only [B, aux_lem_extension_cubeDilation_inv' z hr x] using hx.symm.trans hux
  · intro y hy
    let x := r⁻¹ • (y - z)
    have hxy : cubeDilation z 0 r x = y := aux_lem_extension_cubeDilation_inv z hr y
    have hx : x ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)) :=
      (aux_lem_extension_frontier_dilation z hr one_pos x).mp (hxy ▸ hy)
    change U x = b y
    rw [htrace x hx]
    change b (fun i => z i + r * x i) = b y
    simpa only [aux_lem_extension_cubeDilation_eq, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] using! congrArg b hxy


/-- F1: the closure of the open centred cube is the closed cube. -/
theorem aux_in_deterministic_closure_centeredCube {d : ℕ} (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) :
    closure (centeredCube z r hr : Set (SpatialCoordinates d)) =
      (closedCube z r hr : Set (SpatialCoordinates d)) := by
  change closure (Metric.ball z (r / 2)) = Metric.closedBall z (r / 2)
  exact closure_ball z (by positivity)

/-- F2: the Hölder seminorm is below the `C^β` norm of any constant shift. -/
theorem aux_in_deterministic_holderSeminorm_le_cAlphaNorm_sub {d : ℕ} (beta : ℝ)
    (S : Set (SpatialCoordinates d)) (G : SpatialCoordinates d → ℝ) (c : ℝ) :
    holderSeminorm beta S G ≤ cAlphaNorm beta S (fun x => G x - c) := by
  simp only [cAlphaNorm, holderSeminorm]
  rw [aux_lem_finite_trace_holder_beta_bound_holderRatio_const_sub]
  refine le_add_of_nonneg_left ?_
  exact Real.sSup_nonneg (by rintro v ⟨x, -, rfl⟩; exact abs_nonneg _)

/-- F3: the Hölder ratio set only sees the values on `S`. -/
theorem aux_in_deterministic_holderRatioSet_congr {d : ℕ} (beta : ℝ)
    (S : Set (SpatialCoordinates d)) (G b : SpatialCoordinates d → ℝ)
    (h : ∀ x ∈ S, G x = b x) :
    holderRatioSet beta S G = holderRatioSet beta S b := by
  ext v
  constructor
  · rintro ⟨x, hx, y, hy, hxy, rfl⟩
    exact ⟨x, hx, y, hy, hxy, by rw [h x hx, h y hy]⟩
  · rintro ⟨x, hx, y, hy, hxy, rfl⟩
    exact ⟨x, hx, y, hy, hxy, by rw [h x hx, h y hy]⟩

/-- F4: the rescaled datum is the datum composed with the cube dilation. -/
theorem aux_in_deterministic_rescaledDatum_eq {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (b : SpatialCoordinates d → ℝ) :
    rescaledDatum z r b = fun x => b (cubeDilation z 0 r x) := by
  funext x
  exact congrArg b (aux_lem_extension_cubeDilation_eq z r x).symm

/-- F5: the Hölder seminorm is below the quotient `C^β/ℝ` norm. -/
theorem aux_in_deterministic_holderSeminorm_le_quotient {d : ℕ} (beta : ℝ)
    (S : Set (SpatialCoordinates d)) (G : SpatialCoordinates d → ℝ) :
    holderSeminorm beta S G ≤ quotientCBetaNorm beta S G := by
  unfold quotientCBetaNorm
  refine le_csInf ?_ ?_
  · exact ⟨_, 0, rfl⟩
  · rintro v ⟨c, rfl⟩
    exact aux_in_deterministic_holderSeminorm_le_cAlphaNorm_sub beta S G c

/-- F6: Hölder membership on the unit frontier pulls back to the physical frontier. -/
theorem aux_in_deterministic_isHolderOn_of_dilation {d : ℕ} (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (beta : ℝ) (G : SpatialCoordinates d → ℝ)
    (hG : IsHolderOn beta
      (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))
      (fun x => G (cubeDilation z 0 r x))) :
    IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G := by
  unfold IsHolderOn at hG ⊢
  rw [aux_lem_extension_holderRatioSet_dilation z r hr beta G] at hG
  exact (bddAbove_smul_iff_of_pos (Real.rpow_pos_of_pos hr beta)).mp hG



theorem aux_in_deterministic_trace_extension
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (X : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (Sob : SobolevFoundationalInput d hd)
    (beta : ℝ) (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1) :
    ∃ Cext : ℝ, 0 < Cext ∧ ∀ Cbound : ℝ, Cext ≤ Cbound →
      ∀ (qcenter : SpatialCoordinates d) (qside : ℝ) (hqpos : 0 < qside), qside ≤ 1 →
      ∀ (a : PositiveCoefficient (centeredCube qcenter qside hqpos)),
      ∀ b : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta qcenter qside b →
        ∃ (extension : weakSobolevGraph (centeredCube qcenter qside hqpos))
          (B : SpatialCoordinates d → ℝ),
          ContinuousOn B (closure (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))) ∧
          (((extension : SobolevData (centeredCube qcenter qside hqpos)).1 :
              SpatialCoordinates d → ℝ) =ᵐ[
            volume.restrict (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))] B) ∧
          (∀ x ∈ frontier (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)),
            B x = b x) ∧
          ∀ (Sq : ResponseSpace (centeredCube qcenter qside hqpos)),
            Sq.space = killedSobolevGraph (centeredCube qcenter qside hqpos) →
            dirichletResponse Sq a extension ≤
              Cbound * I.Lam qcenter qside hqpos a qcenter qside ((beta - 1 / 2) / 4) 2 *
                qside ^ ((d : ℝ) - 2) *
                cellBoundaryQuotientNorm beta qcenter qside b ^ 2 := by
  obtain ⟨C, hC, hext⟩ := (lem_extension d hd I X Sob).1 beta hbeta
  refine ⟨C, hC, fun Cbound hCb qcenter qside hqpos hq1 a b hb => ?_⟩
  obtain ⟨extension, B, hBc, hrep, htrace⟩ :=
    aux_in_deterministic_trace_right_inverse_physical hd Sob beta hbeta qcenter qside hqpos b hb
  refine ⟨extension, B, hBc, hrep, htrace, fun Sq hSq => ?_⟩
  have hBc' : ContinuousOn B (closedCube qcenter qside hqpos : Set (SpatialCoordinates d)) := by
    rw [← aux_in_deterministic_closure_centeredCube qcenter hqpos]
    exact hBc
  have hratio : holderRatioSet beta
      (frontier (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))) B =
      holderRatioSet beta
        (frontier (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))) b :=
    aux_in_deterministic_holderRatioSet_congr beta _ B b htrace
  have hresc := aux_in_deterministic_rescaledDatum_eq qcenter qside b
  have hbH : IsHolderOn beta
      (frontier (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))) b := by
    apply aux_in_deterministic_isHolderOn_of_dilation qcenter qside hqpos beta b
    have h1 := hb.1
    rw [hresc] at h1
    exact h1
  have hBH : IsHolderOn beta
      (frontier (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))) B := by
    unfold IsHolderOn
    rw [hratio]
    exact hbH
  have hmain := hext qcenter qside hqpos hq1 (hSq ▸ Sq.poincare) a B extension hBc' hBH hrep
  have hsemi : qside ^ beta * holderSeminorm beta
      (frontier (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))) B ≤
      cellBoundaryQuotientNorm beta qcenter qside b := by
    have h1 : holderSeminorm beta
        (frontier (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))) B =
        holderSeminorm beta
          (frontier (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))) b := by
      unfold holderSeminorm
      rw [hratio]
    unfold cellBoundaryQuotientNorm
    rw [hresc, h1, ← aux_lem_extension_holderSeminorm_dilation qcenter qside hqpos beta b]
    exact aux_in_deterministic_holderSeminorm_le_quotient beta _ _
  have hnn : 0 ≤ qside ^ beta * holderSeminorm beta
      (frontier (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))) B :=
    mul_nonneg (Real.rpow_nonneg hqpos.le _) (aux_lem_extension_holderSeminorm_nonneg _ _ _)
  have hsq := pow_le_pow_left₀ hnn hsemi 2
  have hLam := I.Lam_pos qcenter qside hqpos a qcenter qside ((beta - 1 / 2) / 4) 2
  have hpow : 0 < qside ^ ((d : ℝ) - 2) := Real.rpow_pos_of_pos hqpos _
  have hLP : 0 ≤ I.Lam qcenter qside hqpos a qcenter qside ((beta - 1 / 2) / 4) 2 *
      qside ^ ((d : ℝ) - 2) := (mul_pos hLam hpow).le
  have key := mul_le_mul (mul_le_mul_of_nonneg_right hCb hLP) hsq (sq_nonneg _)
    (mul_nonneg (hC.le.trans hCb) hLP)
  rw [aux_in_deterministic_killed_response_space_eq Sq hSq]
  refine le_trans hmain ?_
  linarith [key]

end SubdiffusiveProcess.Paper
end R4

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable

/-- A common positive disorder threshold for the two scalar estimates used in
the actual good-scale transfer. -/
theorem aux_in_deterministic_small_disorder_choice (s : ℝ) (hs : 0 < s) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ delta : ℝ, 0 ≤ delta → delta ≤ delta0 →
        64 * delta ^ 2 ≤ s ∧ delta ^ 2 ≤ s * Real.log 3 / 16 := by
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hpos : 0 < s * Real.log 3 / 16 := div_pos (mul_pos hs hlog) (by norm_num)
  refine ⟨min (Real.sqrt s / 8) (Real.sqrt (s * Real.log 3 / 16)), ?_, ?_⟩
  · rw [lt_min_iff]
    exact ⟨div_pos (Real.sqrt_pos.mpr hs) (by norm_num),
           Real.sqrt_pos.mpr hpos⟩
  · intro delta hdelta0 hdelta
    have h1 : delta ≤ Real.sqrt s / 8 := hdelta.trans (min_le_left _ _)
    have h2 : delta ≤ Real.sqrt (s * Real.log 3 / 16) := hdelta.trans (min_le_right _ _)
    constructor
    · have hsq : delta ^ 2 ≤ (Real.sqrt s / 8) ^ 2 := pow_le_pow_left₀ hdelta0 h1 2
      have hval : (Real.sqrt s / 8) ^ 2 = s / 64 := by
        rw [div_pow, Real.sq_sqrt (le_of_lt hs)]
        norm_num
      rw [hval] at hsq
      nlinarith
    · have hsq : delta ^ 2 ≤ (Real.sqrt (s * Real.log 3 / 16)) ^ 2 :=
        pow_le_pow_left₀ hdelta0 h2 2
      rwa [Real.sq_sqrt (le_of_lt hpos)] at hsq

/-- A fixed finite prefactor is eventually absorbed by a strictly larger
base-three exponential rate. -/
theorem aux_in_deterministic_eventually_exp_rate
    (A b c : ℝ) (hA : 0 ≤ A) (hbc : b < c) (k0 : ℕ) :
    ∃ D0 : ℕ, k0 ≤ D0 ∧ ∀ D : ℕ, D0 ≤ D →
      A * (3 : ℝ) ^ (b * (D : ℝ)) ≤ (3 : ℝ) ^ (c * (D : ℝ)) := by
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · refine ⟨k0, le_rfl, fun D _ => ?_⟩
    rw [← hA0, zero_mul]
    exact Real.rpow_nonneg (by norm_num) _
  · have hcb : 0 < c - b := sub_pos.mpr hbc
    have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hden : 0 < (c - b) * Real.log 3 := mul_pos hcb hlog3
    obtain ⟨N, hN⟩ := exists_nat_ge (Real.log A / ((c - b) * Real.log 3))
    refine ⟨max k0 N, le_max_left _ _, fun D hD => ?_⟩
    have hND : N ≤ D := le_trans (le_max_right _ _) hD
    have hD' : Real.log A / ((c - b) * Real.log 3) ≤ (D : ℝ) :=
      le_trans hN (by exact_mod_cast hND)
    have h1 : Real.log A ≤ (c - b) * (D : ℝ) * Real.log 3 := by
      rw [div_le_iff₀ hden] at hD'
      nlinarith [hD']
    have h2 : A ≤ (3 : ℝ) ^ ((c - b) * (D : ℝ)) := by
      rw [show A = Real.exp (Real.log A) from (Real.exp_log hApos).symm]
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
      exact Real.exp_le_exp.mpr (by nlinarith [h1])
    calc A * (3 : ℝ) ^ (b * (D : ℝ))
        ≤ (3 : ℝ) ^ ((c - b) * (D : ℝ)) * (3 : ℝ) ^ (b * (D : ℝ)) :=
          mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (by norm_num) _)
      _ = (3 : ℝ) ^ ((c - b) * (D : ℝ) + b * (D : ℝ)) := by
          rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      _ = (3 : ℝ) ^ (c * (D : ℝ)) := by
          congr 1
          ring


/-! ## proved pure-Mathlib helpers (G4 uniform half, `qside ≤ 1`) -/

/-- Auxiliary estimate. -/
theorem aux_in_deterministic_qside_le_one (k : ℕ) (qside : ℝ)
    (hqside : qside = (3 : ℝ) ^ (-(k : ℤ))) : qside ≤ 1 := by
  rw [hqside]
  exact zpow_le_one_of_nonpos₀ (by norm_num : (1:ℝ) ≤ 3) (by simp : -(k : ℤ) ≤ 0)

/-- Auxiliary estimate. -/
theorem aux_in_deterministic_boundary_uniform_limit
    {X : Type*} [TopologicalSpace X] (K B : Set X) (hBK : B ⊆ K)
    (V φ : ℕ → X → ℝ) (U : X → ℝ)
    (hVc : ∀ n, ContinuousOn (V n) K)
    (hVB : ∀ n, ∀ y ∈ B, V n y = φ n y)
    (hmax : ∀ n m : ℕ, ∀ C : ℝ, (∀ y ∈ B, |φ n y - φ m y| ≤ C) →
      ∀ x ∈ K, |V n x - V m x| ≤ C)
    (hφ : TendstoUniformlyOn φ U atTop B) :
    ∃ W : X → ℝ, ContinuousOn W K ∧ TendstoUniformlyOn V W atTop K ∧
      ∀ y ∈ B, W y = U y := by
  have hφcau : UniformCauchySeqOn φ atTop B := hφ.uniformCauchySeqOn
  have hVcau : UniformCauchySeqOn V atTop K := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    have hh : (0 : ℝ) < ε / 2 := by linarith
    rw [Metric.uniformCauchySeqOn_iff] at hφcau
    rcases hφcau (ε / 2) hh with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro m hm n hn x hx
    rw [Real.dist_eq]
    have hC : ∀ y ∈ B, |φ m y - φ n y| ≤ ε / 2 := by
      intro y hy
      have h := hN m hm n hn y hy
      rw [Real.dist_eq] at h
      exact le_of_lt h
    have hle := hmax m n (ε / 2) hC x hx
    linarith
  let W : X → ℝ := fun x => limUnder atTop (fun n => V n x)
  have hpoint : ∀ x ∈ K, Tendsto (fun n => V n x) atTop (𝓝 (W x)) := by
    intro x hx
    have h := (hVcau.cauchySeq hx).tendsto_limUnder
    simpa only [W] using h
  have hT : TendstoUniformlyOn V W atTop K :=
    hVcau.tendstoUniformlyOn_of_tendsto hpoint
  refine ⟨W, ?_, ?_, ?_⟩
  · exact hT.continuousOn (Filter.Eventually.of_forall hVc).frequently
  · exact hT
  · intro y hy
    have hlimV : Tendsto (fun n => V n y) atTop (𝓝 (W y)) := hpoint y (hBK hy)
    have hlimφ : Tendsto (fun n => φ n y) atTop (𝓝 (W y)) :=
      Filter.Tendsto.congr (fun n => hVB n y hy) hlimV
    have hlimU : Tendsto (fun n => φ n y) atTop (𝓝 (U y)) := hφ.tendsto_at hy
    exact tendsto_nhds_unique hlimφ hlimU

/-- Auxiliary estimate. -/
theorem aux_in_deterministic_bump_sequence (d : ℕ) :
    ∃ ψ : ℕ → ContDiffBump (0 : Fin d → ℝ),
      Tendsto (fun n => (ψ n).rOut) atTop (𝓝 0) := by
  refine ⟨fun n => ContDiffBump.mk (1 / (2 * ((n:ℝ) + 1))) (1 / ((n:ℝ) + 1)) ?_ ?_, ?_⟩
  · positivity
  · rw [div_lt_div_iff₀]
    · nlinarith [Nat.cast_add_one_pos n (α := ℝ)]
    · positivity
    · positivity
  · exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- Auxiliary estimate. -/
theorem aux_in_deterministic_indicator_integrable {d : ℕ}
    (C : Set (Fin d → ℝ)) (hC : IsCompact C)
    (g : (Fin d → ℝ) → ℝ) (hg : ContinuousOn g C) :
    LocallyIntegrable (C.indicator g) volume ∧
      AEStronglyMeasurable (C.indicator g) volume := by
  have hI : IntegrableOn g C volume := ContinuousOn.integrableOn_compact hC hg
  have hInt : Integrable (C.indicator g) volume := (integrable_indicator_iff hC.measurableSet).2 hI
  exact ⟨hInt.locallyIntegrable, hInt.aestronglyMeasurable⟩

open scoped Convolution in
/-- Auxiliary estimate. -/
theorem aux_in_deterministic_mollify_smooth {d : ℕ}
    (g : (Fin d → ℝ) → ℝ) (hg : LocallyIntegrable g volume)
    (ψ : ContDiffBump (0 : Fin d → ℝ)) :
    ContDiff ℝ ∞ (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) := by
  exact ψ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) ψ.contDiff_normed hg

open scoped Convolution in
/-- Auxiliary estimate. -/
theorem aux_in_deterministic_mollify_uniform {d : ℕ}
    (K : Set (Fin d → ℝ)) (hK : IsCompact K) (δ : ℝ) (hδ : 0 < δ)
    (g : (Fin d → ℝ) → ℝ) (hmg : AEStronglyMeasurable g volume)
    (hg : ContinuousOn g (Metric.cthickening δ K))
    (ψ : ℕ → ContDiffBump (0 : Fin d → ℝ))
    (hψ : Tendsto (fun n => (ψ n).rOut) atTop (𝓝 0)) :
    TendstoUniformlyOn
      (fun n => (ψ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) g atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hC : IsCompact (Metric.cthickening δ K) := hK.cthickening
  have huc : UniformContinuousOn g (Metric.cthickening δ K) :=
    IsCompact.uniformContinuousOn_of_continuous hC hg
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨η, hη_pos, hη⟩ := huc (ε / 2) (by linarith)
  have hlt : (0 : ℝ) < min δ η := lt_min hδ hη_pos
  filter_upwards [hψ.eventually_lt_const hlt] with n hn
  intro x₀ hx₀
  have hx₀C : x₀ ∈ Metric.cthickening δ K := Metric.self_subset_cthickening K hx₀
  have hbound : ∀ x ∈ Metric.ball x₀ (ψ n).rOut, dist (g x) (g x₀) ≤ ε / 2 := by
    intro x hx
    rw [Metric.mem_ball] at hx
    have hxδ : dist x x₀ ≤ δ :=
      le_of_lt (lt_of_lt_of_le (lt_trans hx hn) (min_le_left δ η))
    have hxC : x ∈ Metric.cthickening δ K :=
      Metric.mem_cthickening_of_dist_le x x₀ δ K hx₀ hxδ
    have hxη : dist x x₀ < η :=
      lt_of_lt_of_le (lt_trans hx hn) (min_le_right δ η)
    exact le_of_lt (hη x hxC x₀ hx₀C hxη)
  have hmain := ContDiffBump.dist_normed_convolution_le (φ := ψ n) hmg hbound
  rw [dist_comm]
  exact lt_of_le_of_lt hmain (by linarith)
/-! ## R3/R4: matrix ellipticity and `traceEstimate`  -/

/-- H1. One constant `Cr` dominating both the matrix threshold (`d/cell²`, `cell⁻¹`) and the
trace-extension constant of `aux_in_deterministic_trace_extension` at `beta`. -/
theorem aux_in_deterministic_R34_constants
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (X : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (beta cell : ℝ) (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1) :
    ∃ Cr : ℝ, 1 ≤ Cr ∧ ∀ Cbound : ℝ, Cr ≤ Cbound →
      (d : ℝ) / cell ^ 2 ≤ Cbound ∧ cell⁻¹ ≤ Cbound ∧ 0 < Cbound ∧
      ∀ (qcenter : SpatialCoordinates d) (qside : ℝ) (hqpos : 0 < qside), qside ≤ 1 →
      ∀ (a : PositiveCoefficient (centeredCube qcenter qside hqpos)),
      ∀ b : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta qcenter qside b →
        ∃ (extension : weakSobolevGraph (centeredCube qcenter qside hqpos))
          (B : SpatialCoordinates d → ℝ),
          ContinuousOn B (closure (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))) ∧
          (((extension : SobolevData (centeredCube qcenter qside hqpos)).1 :
              SpatialCoordinates d → ℝ) =ᵐ[
            volume.restrict (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))] B) ∧
          (∀ x ∈ frontier (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)),
            B x = b x) ∧
          ∀ (Sq : ResponseSpace (centeredCube qcenter qside hqpos)),
            Sq.space = killedSobolevGraph (centeredCube qcenter qside hqpos) →
            dirichletResponse Sq a extension ≤
              Cbound * I.Lam qcenter qside hqpos a qcenter qside ((beta - 1 / 2) / 4) 2 *
                qside ^ ((d : ℝ) - 2) *
                cellBoundaryQuotientNorm beta qcenter qside b ^ 2 := by
  obtain ⟨C3, hC3_1, hC3⟩ := aux_in_deterministic_matrix_bounds_threshold d cell
  obtain ⟨Cext, hCext_pos, hCext⟩ := aux_in_deterministic_trace_extension d hd I X Sob beta hbeta
  refine ⟨max C3 Cext, hC3_1.trans (le_max_left _ _), fun Cbound hCbound => ?_⟩
  have hC3le : C3 ≤ max C3 Cext := le_max_left _ _
  have hCextle : Cext ≤ max C3 Cext := le_max_right _ _
  have hsplit := hC3 Cbound (hC3le.trans hCbound)
  have hext := hCext Cbound (hCextle.trans hCbound)
  exact ⟨hsplit.1, hsplit.2.1, hsplit.2.2, hext⟩



theorem aux_in_deterministic_R34_trace_at
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (X : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (beta sigma cell : ℝ)
    (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hsigma_eq : sigma = (beta - 1 / 2) / 4)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (hcell : cell ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ Cr : ℝ, 1 ≤ Cr ∧ ∀ Cbound : ℝ, Cr ≤ Cbound →
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (k : ℕ) (z : SpatialCoordinates d)
        (qside : ℝ) (hqpos : 0 < qside)
        (_hqside : qside = (3 : ℝ) ^ (-(k : ℤ)))
        (qcenter : SpatialCoordinates d)
        (_hqcenter : qcenter = z)
      (Enl Shift : Type)
        (selfE : Enl) (selfShift : Shift)
        (qRoot : Enl × Shift)
        (_hqRoot : qRoot = (selfE, selfShift))
        (factor : Enl → ℕ)
        (_hfactor : factor selfE = 0)
        (padE : Enl) (_hpad : factor padE = 1)
        (shift : Shift → SpatialCoordinates d)
        (_hshift : shift selfShift = 0)
        (rootLevel : Enl × Shift → ℤ)
        (_hrootLevel : ∀ (e : Enl) (t : Shift),
          rootLevel (e, t) = (k : ℤ) - (factor e : ℤ))
        (rootSide : Enl × Shift → ℝ)
        (_hrootSide : ∀ (U : Enl × Shift),
          rootSide U = (3 : ℝ) ^ (-rootLevel U))
        (rootCentre : Enl × Shift → SpatialCoordinates d)
        (_hrootCentre : ∀ (e : Enl) (t : Shift),
          rootCentre (e, t) = qcenter + rootSide (e, t) • shift t)
        (rootPos : ∀ (U : Enl × Shift), 0 < rootSide U)
        (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
        (ellLoN ellHiN : ℕ → Enl × Shift → BilateralField d → ℝ)
        (_hEllLoN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellLoN N U omega =
            I.lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (_hEllHiN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellHiN N U omega =
            I.Lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (AEN : ℕ → Enl × Shift → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (_hAEN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          AEN N U omega =
            (sN N (rootLevel U) (rootCentre U) omega)⁻¹ •
              Homogenization.Book.Ch02.sigmaCoarse
                (Homogenization.Book.Ch02.cubeDomain
                  (Homogenization.originCube d 0))
                ((I.chart (rootCentre U) (rootSide U) (rootPos U)
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                    (rootCentre U) (rootPos U))
                  (rootCentre U) (rootSide U)).coeffOn
                  (Homogenization.originCube d 0)))
      (N : ℕ) (omega : BilateralField d)
      (_hEll : ∀ U : Enl × Shift,
        cell ≤ ellLoN N U omega ∧ ellHiN N U omega ≤ cell⁻¹),
          (∃ Uq : ℝ,
            Uq = I.Lam qcenter qside hqpos
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N qcenter hqpos)
              qcenter qside sigma 2 ∧
            Cbound⁻¹ * sN N (k : ℤ) qcenter omega ≤ Uq ∧
            Uq ≤ Cbound * sN N (k : ℤ) qcenter omega ∧
            ∀ b : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta qcenter qside b →
              ∃ (extension : weakSobolevGraph (centeredCube qcenter qside hqpos))
                (B : SpatialCoordinates d → ℝ),
                ContinuousOn B
                  (closure (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))) ∧
                (((extension : SobolevData (centeredCube qcenter qside hqpos)).1 :
                    SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict
                    (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))] B) ∧
                (∀ x ∈ frontier (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)),
                  B x = b x) ∧
                ∀ (Sq : ResponseSpace (centeredCube qcenter qside hqpos)),
                  Sq.space = killedSobolevGraph (centeredCube qcenter qside hqpos) →
                  dirichletResponse Sq
                    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N qcenter hqpos)
                    extension ≤
                    Cbound * Uq * qside ^ ((d : ℝ) - 2) *
                      cellBoundaryQuotientNorm beta qcenter qside b ^ 2) := by
  obtain ⟨Cr, hCr1, hCr⟩ := aux_in_deterministic_R34_constants d hd I X Sob beta cell hbeta
  refine ⟨Cr, hCr1, fun Cbound hCbound M H k z qside hqpos hqside qcenter hqcenter
    Enl Shift selfE selfShift qRoot hqRoot factor hfactor padE hpad shift hshift
    rootLevel hrootLevel rootSide hrootSide rootCentre hrootCentre rootPos sN
    ellLoN ellHiN hEllLoN hEllHiN AEN hAEN N omega hEll => ?_⟩
  have hH1 := hCr Cbound hCbound
  have hCinv : cell⁻¹ ≤ Cbound := hH1.2.1
  have hqside_le_one : qside ≤ 1 := by
    rw [hqside]
    exact zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  have hUq := aux_in_deterministic_matrix_bounds_Uq d I sigma cell Cbound hsigma hcell hCinv
    M H k z qside hqpos hqside qcenter hqcenter Enl Shift selfE selfShift qRoot hqRoot
    factor hfactor padE hpad shift hshift rootLevel hrootLevel rootSide hrootSide
    rootCentre hrootCentre rootPos sN ellLoN ellHiN hEllLoN hEllHiN AEN hAEN N omega hEll
  obtain ⟨Uq, hUq_eq, hUq_le1, hUq_le2⟩ := hUq
  have hext := hH1.2.2.2 qcenter qside hqpos hqside_le_one
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N qcenter hqpos)
  refine ⟨Uq, hUq_eq, hUq_le1, hUq_le2, ?_⟩
  rw [hUq_eq, hsigma_eq]
  exact hext

/-- H3. R3 (affine-matrix ellipticity at every root) together with `traceEstimate`, at one
`(N, omega)` from `hEll`, at every `Cbound ≥ Cr`. -/
theorem aux_in_deterministic_R34_pointwise
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (X : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (beta sigma cell : ℝ)
    (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hsigma_eq : sigma = (beta - 1 / 2) / 4)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (hcell : cell ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ Cr : ℝ, 1 ≤ Cr ∧ ∀ Cbound : ℝ, Cr ≤ Cbound →
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (k : ℕ) (z : SpatialCoordinates d)
        (qside : ℝ) (hqpos : 0 < qside)
        (_hqside : qside = (3 : ℝ) ^ (-(k : ℤ)))
        (qcenter : SpatialCoordinates d)
        (_hqcenter : qcenter = z)
      (Enl Shift : Type)
        (selfE : Enl) (selfShift : Shift)
        (qRoot : Enl × Shift)
        (_hqRoot : qRoot = (selfE, selfShift))
        (factor : Enl → ℕ)
        (_hfactor : factor selfE = 0)
        (padE : Enl) (_hpad : factor padE = 1)
        (shift : Shift → SpatialCoordinates d)
        (_hshift : shift selfShift = 0)
        (rootLevel : Enl × Shift → ℤ)
        (_hrootLevel : ∀ (e : Enl) (t : Shift),
          rootLevel (e, t) = (k : ℤ) - (factor e : ℤ))
        (rootSide : Enl × Shift → ℝ)
        (_hrootSide : ∀ (U : Enl × Shift),
          rootSide U = (3 : ℝ) ^ (-rootLevel U))
        (rootCentre : Enl × Shift → SpatialCoordinates d)
        (_hrootCentre : ∀ (e : Enl) (t : Shift),
          rootCentre (e, t) = qcenter + rootSide (e, t) • shift t)
        (rootPos : ∀ (U : Enl × Shift), 0 < rootSide U)
        (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
        (ellLoN ellHiN : ℕ → Enl × Shift → BilateralField d → ℝ)
        (_hEllLoN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellLoN N U omega =
            I.lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (_hEllHiN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellHiN N U omega =
            I.Lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (AEN : ℕ → Enl × Shift → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (_hAEN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          AEN N U omega =
            (sN N (rootLevel U) (rootCentre U) omega)⁻¹ •
              Homogenization.Book.Ch02.sigmaCoarse
                (Homogenization.Book.Ch02.cubeDomain
                  (Homogenization.originCube d 0))
                ((I.chart (rootCentre U) (rootSide U) (rootPos U)
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                    (rootCentre U) (rootPos U))
                  (rootCentre U) (rootSide U)).coeffOn
                  (Homogenization.originCube d 0)))
      (N : ℕ) (omega : BilateralField d)
      (_hEll : ∀ U : Enl × Shift,
        cell ≤ ellLoN N U omega ∧ ellHiN N U omega ≤ cell⁻¹),
        (∀ (Uroot : Enl × Shift) (x : Fin d → ℝ),
            Cbound⁻¹ * Matrix.trace (AEN N Uroot omega) * (x ⬝ᵥ x) ≤
              x ⬝ᵥ (AEN N Uroot omega).mulVec x) ∧
          (∃ Uq : ℝ,
            Uq = I.Lam qcenter qside hqpos
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N qcenter hqpos)
              qcenter qside sigma 2 ∧
            Cbound⁻¹ * sN N (k : ℤ) qcenter omega ≤ Uq ∧
            Uq ≤ Cbound * sN N (k : ℤ) qcenter omega ∧
            ∀ b : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta qcenter qside b →
              ∃ (extension : weakSobolevGraph (centeredCube qcenter qside hqpos))
                (B : SpatialCoordinates d → ℝ),
                ContinuousOn B
                  (closure (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))) ∧
                (((extension : SobolevData (centeredCube qcenter qside hqpos)).1 :
                    SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict
                    (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))] B) ∧
                (∀ x ∈ frontier (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)),
                  B x = b x) ∧
                ∀ (Sq : ResponseSpace (centeredCube qcenter qside hqpos)),
                  Sq.space = killedSobolevGraph (centeredCube qcenter qside hqpos) →
                  dirichletResponse Sq
                    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N qcenter hqpos)
                    extension ≤
                    Cbound * Uq * qside ^ ((d : ℝ) - 2) *
                      cellBoundaryQuotientNorm beta qcenter qside b ^ 2) := by
  obtain ⟨Cr1, hCr1_1, hCr1⟩ := aux_in_deterministic_R34_constants d hd I X Sob beta cell hbeta
  obtain ⟨Cr2, hCr2_1, hCr2⟩ := aux_in_deterministic_R34_trace_at d hd I X Sob beta sigma cell
    hbeta hsigma_eq hsigma hcell
  refine ⟨max Cr1 Cr2, hCr1_1.trans (le_max_left _ _), fun Cbound hCbound M H k z qside hqpos
    hqside qcenter hqcenter Enl Shift selfE selfShift qRoot hqRoot factor hfactor padE hpad shift
    hshift rootLevel hrootLevel rootSide hrootSide rootCentre hrootCentre rootPos sN ellLoN ellHiN
    hEllLoN hEllHiN AEN hAEN N omega hEll => ?_⟩
  have hCr1le : Cr1 ≤ max Cr1 Cr2 := le_max_left _ _
  have hCr2le : Cr2 ≤ max Cr1 Cr2 := le_max_right _ _
  have hH1 := hCr1 Cbound (hCr1le.trans hCbound)
  have hH2 := hCr2 Cbound (hCr2le.trans hCbound) M H k z qside hqpos hqside qcenter hqcenter
    Enl Shift selfE selfShift qRoot hqRoot factor hfactor padE hpad shift hshift rootLevel
    hrootLevel rootSide hrootSide rootCentre hrootCentre rootPos sN ellLoN ellHiN hEllLoN hEllHiN
    AEN hAEN N omega hEll
  have h_first : ∀ (Uroot : Enl × Shift) (x : Fin d → ℝ),
      Cbound⁻¹ * Matrix.trace (AEN N Uroot omega) * (x ⬝ᵥ x) ≤
        x ⬝ᵥ (AEN N Uroot omega).mulVec x :=
    in_deterministic_matrix_bounds d I sigma cell Cbound hsigma hcell hH1.1 hH1.2.2.1
      M H Enl Shift rootLevel rootSide rootCentre rootPos sN ellLoN ellHiN hEllLoN hEllHiN
      AEN hAEN N omega hEll
  exact ⟨h_first, hH2⟩

/-! ## Exact slices of the live principal (generated by `gen_candidate.py`) -/

def aux_in_deterministic_body
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha beta s sigma cell epshom : ℝ)
    (Cbound eps0 lam0 delta0 : ℝ) : Prop :=
      ∀ (cbuf k0 : ℕ)
        (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hMH : InfraredCharacterization M H)
        (k : ℕ) (z : SpatialCoordinates d)
        (qside : ℝ) (hqpos : 0 < qside)
        (hqside : qside = (3 : ℝ) ^ (-(k : ℤ)))
        (qcenter : SpatialCoordinates d)
        (hqcenter : qcenter = z)
        (Enl Shift Cmp : Type)
        [Fintype Enl] [Fintype Shift] [Fintype Cmp]
        (selfE : Enl) (selfShift : Shift)
        (qRoot : Enl × Shift)
        (hqRoot : qRoot = (selfE, selfShift))
        (factor : Enl → ℕ)
        (hfactor : factor selfE = 0)
        (padE : Enl) (hpad : factor padE = 1)
        (shift : Shift → SpatialCoordinates d)
        (hshift : shift selfShift = 0)
        (rootLevel : Enl × Shift → ℤ)
        (hrootLevel : ∀ (e : Enl) (t : Shift),
          rootLevel (e, t) = (k : ℤ) - (factor e : ℤ))
        (rootSide : Enl × Shift → ℝ)
        (hrootSide : ∀ (U : Enl × Shift),
          rootSide U = (3 : ℝ) ^ (-rootLevel U))
        (rootCentre : Enl × Shift → SpatialCoordinates d)
        (hrootCentre : ∀ (e : Enl) (t : Shift),
          rootCentre (e, t) = qcenter + rootSide (e, t) • shift t)
        (rootPos : ∀ (U : Enl × Shift), 0 < rootSide U)
        (hGridCover : ∀ (x : SpatialCoordinates d),
          x ∈ Metric.closedBall z (qside / 2) →
          ∀ rho : ℝ, 0 < rho → rho ≤ qside →
            ∃ (U : Enl × Shift) (D : ℕ) (w : Fin D → OddGridIndex d 1),
              Metric.ball x (rho / 2) ⊆
                Metric.ball (descendantCenter 1 (rootCentre U) (rootSide U) D w)
                  (descendantSide 1 D (rootSide U) / 2) ∧
              descendantSide 1 D (rootSide U) ≤ 9 * rho)
        (parent : Cmp → Enl × Shift)
        (depth : Cmp → ℕ)
        (word : (c : Cmp) → Fin (depth c) → OddGridIndex d 1)
        (cmpCentre : Cmp → SpatialCoordinates d)
        (hcmpCentre : ∀ (c : Cmp),
          cmpCentre c =
            descendantCenter 1 (rootCentre (parent c)) (rootSide (parent c))
              (depth c) (word c))
        (cmpLevel : Cmp → ℤ)
        (hcmpLevel : ∀ (c : Cmp),
          cmpLevel c = rootLevel (parent c) + (depth c : ℤ))
        (cmpSide : Cmp → ℝ)
        (hcmpSide : ∀ (c : Cmp), cmpSide c = (3 : ℝ) ^ (-cmpLevel c))
        (cmpPos : ∀ (c : Cmp), 0 < cmpSide c)
        (chosen : Cmp)
        (observationCentre : ∀ (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            SpatialCoordinates d)
        (hObservationCentre : ∀ (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          observationCentre U D code =
            Sum.elim
              (fun w => descendantCenter 1 (rootCentre U) (rootSide U) D w)
              (fun V => rootCentre V) code)
        (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : Vec d),
            eta N omega i y =
              omega ((i : ℤ) - (N : ℤ))
                (((3 : ℝ) ^ (-(N : ℤ))) • y))
        (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
        (eps : ℝ) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
        (hepsSmall : eps ≤ eps0)
        (hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ N : ℕ,
            primitive_scores d M s eps (eta N omega)
              (fun m y => F N m y omega)
              (fun m y => Praw N m y omega)
              (fun m y => Rraw N m y omega)
              (fun m y => Draw N m y omega)
              (fun m y => Z N m y omega)
              (fun m y => rawGood N m y omega))
        (lambdaCut lambdaLim lambdaDet cdet : ℝ)
        (hThresholds :
          0 < lambdaCut ∧ lambdaCut < lambdaLim ∧
          lambdaLim < lambdaDet ∧ lambdaDet < 1)
        (hcdet : 0 < cdet) (hcdetSmall : cdet ≤ Cbound⁻¹)
        (hlamSmall : lambdaDet ≤ lam0)
        (hdisorder : M.delta ≤ delta0)
        (prefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (prefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (hPrefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift))
          (omega : BilateralField d),
          prefixZ N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  Z N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega
                else 0
            else 0)
        (hPrefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift))
          (omega : BilateralField d),
          prefixD N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  (Draw N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega).toReal
                else 0
            else 0)
        (hFiniteScoreGuard : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
            (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
            rootLevel U + (D : ℤ) ≤ (N : ℤ) →
            ∀ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
              (rootLevel U + (D : ℤ)),
              Draw N ((N : ℤ) - j).toNat
                (((3 : ℝ) ^ N) • observationCentre U D code) omega ≠ ⊤)
        (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
        (hsN : ∀ (N : ℕ) (l : ℤ) (w : SpatialCoordinates d)
          (omega : BilateralField d),
          sN N l w omega =
            if l ≤ (N : ℤ) then
              (let kappa : ℕ → ℝ := fun J =>
                Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
                  SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
               let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
                 fun ell v beta =>
                   if 0 ≤ ell then
                     ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
                   else
                     -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
               kappa ((N : ℤ) - l).toNat / kappa N *
                 Real.exp (H omega w + retained l w omega))
            else 1)
        (ellLoN ellHiN : ℕ → Enl × Shift → BilateralField d → ℝ)
        (hEllLoN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellLoN N U omega =
            I.lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (hEllHiN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellHiN N U omega =
            I.Lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (AEN : ℕ → Enl × Shift → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (hAEN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          AEN N U omega =
            (sN N (rootLevel U) (rootCentre U) omega)⁻¹ •
              Homogenization.Book.Ch02.sigmaCoarse
                (Homogenization.Book.Ch02.cubeDomain
                  (Homogenization.originCube d 0))
                ((I.chart (rootCentre U) (rootSide U) (rootPos U)
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                    (rootCentre U) (rootPos U))
                  (rootCentre U) (rootSide U)).coeffOn
                  (Homogenization.originCube d 0)))
        (errN ratioN : ℕ → Cmp → BilateralField d → ℝ)
        (hErrN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          errN N c omega =
            I.err (cmpCentre c) (cmpSide c) (cmpPos c)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (cmpCentre c) (cmpPos c))
              (cmpCentre c) (cmpSide c)
              (sN N (cmpLevel c) (cmpCentre c) omega) s 2)
        (hRatioN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          ratioN N c omega =
            sN N (k : ℤ) qcenter omega /
              sN N (cmpLevel c) (cmpCentre c) omega)
        (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
        (hRootsQ : ∀ U : Enl × Shift,
          closure (centeredCube (rootCentre U) (rootSide U) (rootPos U) :
            Set (SpatialCoordinates d)) ⊆
            (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ,
      let Q := centeredCube Qcentre Qside hQside
      let q := centeredCube qcenter qside hqpos
      let qp : Set (SpatialCoordinates d) := Metric.ball qcenter (3 * qside / 2)
      let Ctotal := Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ)))
      let psource : ℝ := (d : ℝ) / (1 - alpha)
      ∀ (N : ℕ), k + k0 ≤ N → (∀ c : Cmp, cmpLevel c ≤ (N : ℤ)) →
        let harmonicComparison (omega : BilateralField d)
            (fNorm : Set (SpatialCoordinates d) → ℝ)
            (U : SpatialCoordinates d → ℝ) : Prop :=
          (let qc := centeredCube (cmpCentre chosen) (cmpSide chosen / 81)
                   (div_pos (cmpPos chosen) (by norm_num))
                 let qi : Set (SpatialCoordinates d) :=
                   Metric.ball (cmpCentre chosen) (cmpSide chosen / 1458)
                 let qo : Set (SpatialCoordinates d) :=
                   Metric.ball (cmpCentre chosen) (cmpSide chosen / 18)
                 ∀ w : SpatialCoordinates d,
                 let qd : Set (SpatialCoordinates d) :=
                   Metric.ball w (27 * cmpSide chosen / 2)
                 Metric.closedBall (cmpCentre chosen) (cmpSide chosen / 18) ⊆ qd →
                 qd ⊆ (Q : Set (SpatialCoordinates d)) →
                 ∃ (v : weakSobolevGraph qc) (V : SpatialCoordinates d → ℝ),
                   ContinuousOn V (closure (qc : Set (SpatialCoordinates d))) ∧
                   (((v : SobolevData qc).1 : SpatialCoordinates d → ℝ) =ᵐ[
                     volume.restrict (qc : Set (SpatialCoordinates d))] V) ∧
                   (∀ x ∈ frontier (qc : Set (SpatialCoordinates d)), V x = U x) ∧
                   (∀ psi : killedSobolevGraph qc,
                     inner ℝ (sobolevGradient (v : SobolevData qc))
                       (subspaceGradient (killedSobolevGraph qc) psi) = 0) ∧
                   normalizedL2On qi (fun x => U x - V x) ≤
                     epshom * normalizedL2On qo
                       (fun x => U x - (volume.real qo)⁻¹ * ∫ y in qo, U y) +
                     Ctotal * (cmpSide chosen / 9) ^ 2 *
                       (sN N (cmpLevel chosen) (cmpCentre chosen) omega)⁻¹ * fNorm qd)
        let traceEstimate (omega : BilateralField d) : Prop :=
          (∃ Uq : ℝ,
            Uq = I.Lam qcenter qside hqpos
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N qcenter hqpos)
              qcenter qside sigma 2 ∧
            Cbound⁻¹ * sN N (k : ℤ) qcenter omega ≤ Uq ∧
            Uq ≤ Cbound * sN N (k : ℤ) qcenter omega ∧
            ∀ b : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta qcenter qside b →
              ∃ (extension : weakSobolevGraph q) (B : SpatialCoordinates d → ℝ),
                ContinuousOn B (closure (q : Set (SpatialCoordinates d))) ∧
                (((extension : SobolevData q).1 : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (q : Set (SpatialCoordinates d))] B) ∧
                (∀ x ∈ frontier (q : Set (SpatialCoordinates d)), B x = b x) ∧
                ∀ (Sq : ResponseSpace q), Sq.space = killedSobolevGraph q →
                  dirichletResponse Sq
                    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N qcenter hqpos)
                    extension ≤
                    Cbound * Uq * qside ^ ((d : ℝ) - 2) *
                      cellBoundaryQuotientNorm beta qcenter qside b ^ 2)
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          (∀ horizon : ℕ,
          ((∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D → D ≤ horizon →
              rootLevel U + (D : ℤ) ≤ (N : ℤ) →
              ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
                prefixZ N U D code omega < lambdaCut * (D : ℝ) ∧
                prefixD N U D code omega < lambdaCut * (D : ℝ)) ∧
           (∀ U : Enl × Shift,
              cell ≤ ellLoN N U omega ∧ ellHiN N U omega ≤ cell⁻¹) ∧
           errN N chosen omega ≤ epshom * cdet ∧
           (∀ c : Cmp, ratioN N c omega ∈ Set.Icc (1 / 2 : ℝ) 2)) →
          (∀ (f : SpatialCoordinates d → ℝ),
            MemLp f (ENNReal.ofReal psource) (volume.restrict (Q : Set (SpatialCoordinates d))) →
            ∀ (fL2 : DomainL2 Q),
              ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                (Q : Set (SpatialCoordinates d))] f) →
            let fNorm : Set (SpatialCoordinates d) → ℝ := fun W =>
              (eLpNorm f (ENNReal.ofReal psource) (volume.restrict W)).toReal /
                (volume.real W) ^ (1 / psource)
            ∀ u : weakSobolevGraph Q,
              (∀ psi : killedSobolevGraph Q,
                sobolevCoefficientForm
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
                  (u : SobolevData Q) (psi : SobolevData Q) =
                sobolevVolumeLoad fL2 (psi : SobolevData Q)) →
              ∃ U : SpatialCoordinates d → ℝ,
                ContinuousOn U (Q : Set (SpatialCoordinates d)) ∧
                (((u : SobolevData Q).1 : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
                (∀ (D : ℕ), D ≤ horizon →
                  ∀ x ∈ (q : Set (SpatialCoordinates d)),
                    let B : Set (SpatialCoordinates d) :=
                      Metric.ball x (qside * (3 : ℝ) ^ (-(D : ℤ)) / 2) ∩
                        (q : Set (SpatialCoordinates d))
                    normalizedL2On B
                      (fun y => U y - (volume.real B)⁻¹ * ∫ t in B, U t) ≤
                      Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ))) *
                        (3 : ℝ) ^ (Cbound * (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)) *
                        (3 : ℝ) ^ (-(D : ℝ)) *
                        (normalizedL2On qp
                          (fun y => U y - (volume.real qp)⁻¹ * ∫ t in qp, U t) +
                          qside ^ 2 * (sN N (k : ℤ) qcenter omega)⁻¹ * fNorm qp)) ∧
                harmonicComparison omega fNorm U) ∧
          (∀ (Uroot : Enl × Shift) (x : Fin d → ℝ),
            Cbound⁻¹ * Matrix.trace (AEN N Uroot omega) * (x ⬝ᵥ x) ≤
              x ⬝ᵥ (AEN N Uroot omega).mulVec x) ∧
          traceEstimate omega) ∧
          (          ((∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D →
              rootLevel U + (D : ℤ) ≤ (N : ℤ) →
              ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
                prefixZ N U D code omega < lambdaCut * (D : ℝ) ∧
                prefixD N U D code omega < lambdaCut * (D : ℝ)) ∧
           (∀ U : Enl × Shift,
              cell ≤ ellLoN N U omega ∧ ellHiN N U omega ≤ cell⁻¹) ∧
           errN N chosen omega ≤ epshom * cdet ∧
           (∀ c : Cmp, ratioN N c omega ∈ Set.Icc (1 / 2 : ℝ) 2)) →
          (∀ (Uroot : Enl × Shift) (D : ℕ),
            rootLevel Uroot + (D : ℤ) ≤ (N : ℤ) →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              ((Finset.filter
                (fun j : ℤ => j < rootLevel Uroot + (k0 : ℤ) ∨
                  1 ≤ Z N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre Uroot D code) omega)
                (Finset.Icc (rootLevel Uroot - (cbuf : ℤ))
                  (rootLevel Uroot + (D : ℤ)))).card : ℝ) ≤
                (k0 : ℝ) + (cbuf : ℝ) + lambdaDet * (D : ℝ)) ∧
          (∀ (Uroot : Enl × Shift) (D : ℕ),
            rootLevel Uroot + (D : ℤ) ≤ (N : ℤ) →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              (∑ j ∈ Finset.Icc (rootLevel Uroot - (cbuf : ℤ))
                (rootLevel Uroot + (D : ℤ)),
                if rootLevel Uroot + (k0 : ℤ) ≤ j ∧
                    Z N ((N : ℤ) - j).toNat
                      (((3 : ℝ) ^ N) • observationCentre Uroot D code) omega < 1 then
                  let w := observationCentre Uroot D code
                  let rj := (3 : ℝ) ^ (-j)
                  I.err w rj (by positivity)
                    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
                    w rj (sN N j w omega) s 2
                else 0) ≤
                  Cbound * (M.delta ^ 2 + eps ^ 8 + lambdaDet) * (D : ℝ) +
                    Cbound * ((k0 : ℝ) + (cbuf : ℝ))) ∧
          Cbound * (lambdaDet + M.delta ^ 2 + eps ^ 8) < 1 - alpha ∧
          (∃ D0 : ℕ, k0 ≤ D0 ∧ ∀ D : ℕ, D0 ≤ D →
            (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ))) *
              (3 : ℝ) ^ (Cbound * (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)) ≤
                (3 : ℝ) ^ ((1 - alpha) * (D : ℝ))) ∧
          (∀ (f : SpatialCoordinates d → ℝ),
            MemLp f (ENNReal.ofReal psource) (volume.restrict (Q : Set (SpatialCoordinates d))) →
            ∀ (fL2 : DomainL2 Q),
              ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                (Q : Set (SpatialCoordinates d))] f) →
            let fNorm : Set (SpatialCoordinates d) → ℝ := fun W =>
              (eLpNorm f (ENNReal.ofReal psource) (volume.restrict W)).toReal /
                (volume.real W) ^ (1 / psource)
            ∀ u : weakSobolevGraph Q,
              (∀ psi : killedSobolevGraph Q,
                sobolevCoefficientForm
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
                  (u : SobolevData Q) (psi : SobolevData Q) =
                sobolevVolumeLoad fL2 (psi : SobolevData Q)) →
              ∃ U : SpatialCoordinates d → ℝ,
                ContinuousOn U (Q : Set (SpatialCoordinates d)) ∧
                (((u : SobolevData Q).1 : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
                _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (closure (q : Set (SpatialCoordinates d))) U ∧
                (∃ cq : ℝ,
                  _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
                    (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
                    (fun x => U (qcenter + qside • x) - cq) ≤
                      Ctotal * (normalizedL2On qp
                        (fun x => U x - (volume.real qp)⁻¹ * ∫ y in qp, U y) +
                        qside ^ 2 * (sN N (k : ℤ) qcenter omega)⁻¹ * fNorm qp)) ∧
                harmonicComparison omega fNorm U) ∧
          (∀ (Uroot : Enl × Shift) (x : Fin d → ℝ),
            Cbound⁻¹ * Matrix.trace (AEN N Uroot omega) * (x ⬝ᵥ x) ≤
              x ⬝ᵥ (AEN N Uroot omega).mulVec x) ∧
          traceEstimate omega)

def aux_in_deterministic_remaining_at
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha beta s sigma cell epshom : ℝ)
    (Cbound eps0 lam0 delta0 : ℝ) : Prop :=
      ∀ (cbuf k0 : ℕ)
        (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hMH : InfraredCharacterization M H)
        (k : ℕ) (z : SpatialCoordinates d)
        (qside : ℝ) (hqpos : 0 < qside)
        (hqside : qside = (3 : ℝ) ^ (-(k : ℤ)))
        (qcenter : SpatialCoordinates d)
        (hqcenter : qcenter = z)
        (Enl Shift Cmp : Type)
        [Fintype Enl] [Fintype Shift] [Fintype Cmp]
        (selfE : Enl) (selfShift : Shift)
        (qRoot : Enl × Shift)
        (hqRoot : qRoot = (selfE, selfShift))
        (factor : Enl → ℕ)
        (hfactor : factor selfE = 0)
        (padE : Enl) (hpad : factor padE = 1)
        (shift : Shift → SpatialCoordinates d)
        (hshift : shift selfShift = 0)
        (rootLevel : Enl × Shift → ℤ)
        (hrootLevel : ∀ (e : Enl) (t : Shift),
          rootLevel (e, t) = (k : ℤ) - (factor e : ℤ))
        (rootSide : Enl × Shift → ℝ)
        (hrootSide : ∀ (U : Enl × Shift),
          rootSide U = (3 : ℝ) ^ (-rootLevel U))
        (rootCentre : Enl × Shift → SpatialCoordinates d)
        (hrootCentre : ∀ (e : Enl) (t : Shift),
          rootCentre (e, t) = qcenter + rootSide (e, t) • shift t)
        (rootPos : ∀ (U : Enl × Shift), 0 < rootSide U)
        (hGridCover : ∀ (x : SpatialCoordinates d),
          x ∈ Metric.closedBall z (qside / 2) →
          ∀ rho : ℝ, 0 < rho → rho ≤ qside →
            ∃ (U : Enl × Shift) (D : ℕ) (w : Fin D → OddGridIndex d 1),
              Metric.ball x (rho / 2) ⊆
                Metric.ball (descendantCenter 1 (rootCentre U) (rootSide U) D w)
                  (descendantSide 1 D (rootSide U) / 2) ∧
              descendantSide 1 D (rootSide U) ≤ 9 * rho)
        (parent : Cmp → Enl × Shift)
        (depth : Cmp → ℕ)
        (word : (c : Cmp) → Fin (depth c) → OddGridIndex d 1)
        (cmpCentre : Cmp → SpatialCoordinates d)
        (hcmpCentre : ∀ (c : Cmp),
          cmpCentre c =
            descendantCenter 1 (rootCentre (parent c)) (rootSide (parent c))
              (depth c) (word c))
        (cmpLevel : Cmp → ℤ)
        (hcmpLevel : ∀ (c : Cmp),
          cmpLevel c = rootLevel (parent c) + (depth c : ℤ))
        (cmpSide : Cmp → ℝ)
        (hcmpSide : ∀ (c : Cmp), cmpSide c = (3 : ℝ) ^ (-cmpLevel c))
        (cmpPos : ∀ (c : Cmp), 0 < cmpSide c)
        (chosen : Cmp)
        (observationCentre : ∀ (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            SpatialCoordinates d)
        (hObservationCentre : ∀ (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          observationCentre U D code =
            Sum.elim
              (fun w => descendantCenter 1 (rootCentre U) (rootSide U) D w)
              (fun V => rootCentre V) code)
        (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : Vec d),
            eta N omega i y =
              omega ((i : ℤ) - (N : ℤ))
                (((3 : ℝ) ^ (-(N : ℤ))) • y))
        (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
        (eps : ℝ) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
        (hepsSmall : eps ≤ eps0)
        (hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ N : ℕ,
            primitive_scores d M s eps (eta N omega)
              (fun m y => F N m y omega)
              (fun m y => Praw N m y omega)
              (fun m y => Rraw N m y omega)
              (fun m y => Draw N m y omega)
              (fun m y => Z N m y omega)
              (fun m y => rawGood N m y omega))
        (lambdaCut lambdaLim lambdaDet cdet : ℝ)
        (hThresholds :
          0 < lambdaCut ∧ lambdaCut < lambdaLim ∧
          lambdaLim < lambdaDet ∧ lambdaDet < 1)
        (hcdet : 0 < cdet) (hcdetSmall : cdet ≤ Cbound⁻¹)
        (hlamSmall : lambdaDet ≤ lam0)
        (hdisorder : M.delta ≤ delta0)
        (prefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (prefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (hPrefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift))
          (omega : BilateralField d),
          prefixZ N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  Z N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega
                else 0
            else 0)
        (hPrefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift))
          (omega : BilateralField d),
          prefixD N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  (Draw N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega).toReal
                else 0
            else 0)
        (hFiniteScoreGuard : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
            (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
            rootLevel U + (D : ℤ) ≤ (N : ℤ) →
            ∀ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
              (rootLevel U + (D : ℤ)),
              Draw N ((N : ℤ) - j).toNat
                (((3 : ℝ) ^ N) • observationCentre U D code) omega ≠ ⊤)
        (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
        (hsN : ∀ (N : ℕ) (l : ℤ) (w : SpatialCoordinates d)
          (omega : BilateralField d),
          sN N l w omega =
            if l ≤ (N : ℤ) then
              (let kappa : ℕ → ℝ := fun J =>
                Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
                  SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
               let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
                 fun ell v beta =>
                   if 0 ≤ ell then
                     ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
                   else
                     -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
               kappa ((N : ℤ) - l).toNat / kappa N *
                 Real.exp (H omega w + retained l w omega))
            else 1)
        (ellLoN ellHiN : ℕ → Enl × Shift → BilateralField d → ℝ)
        (hEllLoN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellLoN N U omega =
            I.lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (hEllHiN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellHiN N U omega =
            I.Lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (AEN : ℕ → Enl × Shift → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (hAEN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          AEN N U omega =
            (sN N (rootLevel U) (rootCentre U) omega)⁻¹ •
              Homogenization.Book.Ch02.sigmaCoarse
                (Homogenization.Book.Ch02.cubeDomain
                  (Homogenization.originCube d 0))
                ((I.chart (rootCentre U) (rootSide U) (rootPos U)
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                    (rootCentre U) (rootPos U))
                  (rootCentre U) (rootSide U)).coeffOn
                  (Homogenization.originCube d 0)))
        (errN ratioN : ℕ → Cmp → BilateralField d → ℝ)
        (hErrN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          errN N c omega =
            I.err (cmpCentre c) (cmpSide c) (cmpPos c)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (cmpCentre c) (cmpPos c))
              (cmpCentre c) (cmpSide c)
              (sN N (cmpLevel c) (cmpCentre c) omega) s 2)
        (hRatioN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          ratioN N c omega =
            sN N (k : ℤ) qcenter omega /
              sN N (cmpLevel c) (cmpCentre c) omega)
        (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
        (hRootsQ : ∀ U : Enl × Shift,
          closure (centeredCube (rootCentre U) (rootSide U) (rootPos U) :
            Set (SpatialCoordinates d)) ⊆
            (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ,
      let Q := centeredCube Qcentre Qside hQside
      let q := centeredCube qcenter qside hqpos
      let qp : Set (SpatialCoordinates d) := Metric.ball qcenter (3 * qside / 2)
      let Ctotal := Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ)))
      let psource : ℝ := (d : ℝ) / (1 - alpha)
      ∀ (N : ℕ), k + k0 ≤ N → (∀ c : Cmp, cmpLevel c ≤ (N : ℤ)) →
        let harmonicComparison (omega : BilateralField d)
            (fNorm : Set (SpatialCoordinates d) → ℝ)
            (U : SpatialCoordinates d → ℝ) : Prop :=
          (let qc := centeredCube (cmpCentre chosen) (cmpSide chosen / 81)
                   (div_pos (cmpPos chosen) (by norm_num))
                 let qi : Set (SpatialCoordinates d) :=
                   Metric.ball (cmpCentre chosen) (cmpSide chosen / 1458)
                 let qo : Set (SpatialCoordinates d) :=
                   Metric.ball (cmpCentre chosen) (cmpSide chosen / 18)
                 ∀ w : SpatialCoordinates d,
                 let qd : Set (SpatialCoordinates d) :=
                   Metric.ball w (27 * cmpSide chosen / 2)
                 Metric.closedBall (cmpCentre chosen) (cmpSide chosen / 18) ⊆ qd →
                 qd ⊆ (Q : Set (SpatialCoordinates d)) →
                 ∃ (v : weakSobolevGraph qc) (V : SpatialCoordinates d → ℝ),
                   ContinuousOn V (closure (qc : Set (SpatialCoordinates d))) ∧
                   (((v : SobolevData qc).1 : SpatialCoordinates d → ℝ) =ᵐ[
                     volume.restrict (qc : Set (SpatialCoordinates d))] V) ∧
                   (∀ x ∈ frontier (qc : Set (SpatialCoordinates d)), V x = U x) ∧
                   (∀ psi : killedSobolevGraph qc,
                     inner ℝ (sobolevGradient (v : SobolevData qc))
                       (subspaceGradient (killedSobolevGraph qc) psi) = 0) ∧
                   normalizedL2On qi (fun x => U x - V x) ≤
                     epshom * normalizedL2On qo
                       (fun x => U x - (volume.real qo)⁻¹ * ∫ y in qo, U y) +
                     Ctotal * (cmpSide chosen / 9) ^ 2 *
                       (sN N (cmpLevel chosen) (cmpCentre chosen) omega)⁻¹ * fNorm qd)
        let traceEstimate (omega : BilateralField d) : Prop :=
          (∃ Uq : ℝ,
            Uq = I.Lam qcenter qside hqpos
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N qcenter hqpos)
              qcenter qside sigma 2 ∧
            Cbound⁻¹ * sN N (k : ℤ) qcenter omega ≤ Uq ∧
            Uq ≤ Cbound * sN N (k : ℤ) qcenter omega ∧
            ∀ b : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta qcenter qside b →
              ∃ (extension : weakSobolevGraph q) (B : SpatialCoordinates d → ℝ),
                ContinuousOn B (closure (q : Set (SpatialCoordinates d))) ∧
                (((extension : SobolevData q).1 : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (q : Set (SpatialCoordinates d))] B) ∧
                (∀ x ∈ frontier (q : Set (SpatialCoordinates d)), B x = b x) ∧
                ∀ (Sq : ResponseSpace q), Sq.space = killedSobolevGraph q →
                  dirichletResponse Sq
                    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N qcenter hqpos)
                    extension ≤
                    Cbound * Uq * qside ^ ((d : ℝ) - 2) *
                      cellBoundaryQuotientNorm beta qcenter qside b ^ 2)
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          (∀ horizon : ℕ,
          ((∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D → D ≤ horizon →
              rootLevel U + (D : ℤ) ≤ (N : ℤ) →
              ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
                prefixZ N U D code omega < lambdaCut * (D : ℝ) ∧
                prefixD N U D code omega < lambdaCut * (D : ℝ)) ∧
           (∀ U : Enl × Shift,
              cell ≤ ellLoN N U omega ∧ ellHiN N U omega ≤ cell⁻¹) ∧
           errN N chosen omega ≤ epshom * cdet ∧
           (∀ c : Cmp, ratioN N c omega ∈ Set.Icc (1 / 2 : ℝ) 2)) →
          ((∀ (Uroot : Enl × Shift) (D : ℕ), D ≤ horizon →
            rootLevel Uroot + (D : ℤ) ≤ (N : ℤ) →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              ((Finset.filter
                (fun j : ℤ => j < rootLevel Uroot + (k0 : ℤ) ∨
                  1 ≤ Z N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre Uroot D code) omega)
                (Finset.Icc (rootLevel Uroot - (cbuf : ℤ))
                  (rootLevel Uroot + (D : ℤ)))).card : ℝ) ≤
                (k0 : ℝ) + (cbuf : ℝ) + lambdaDet * (D : ℝ)) ∧
          (∀ (Uroot : Enl × Shift) (D : ℕ), D ≤ horizon →
            rootLevel Uroot + (D : ℤ) ≤ (N : ℤ) →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              (∑ j ∈ Finset.Icc (rootLevel Uroot - (cbuf : ℤ))
                (rootLevel Uroot + (D : ℤ)),
                if rootLevel Uroot + (k0 : ℤ) ≤ j ∧
                    Z N ((N : ℤ) - j).toNat
                      (((3 : ℝ) ^ N) • observationCentre Uroot D code) omega < 1 then
                  let w := observationCentre Uroot D code
                  let rj := (3 : ℝ) ^ (-j)
                  I.err w rj (by positivity)
                    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
                    w rj (sN N j w omega) s 2
                else 0) ≤
                  Cbound * (M.delta ^ 2 + eps ^ 8 + lambdaDet) * (D : ℝ) +
                    Cbound * ((k0 : ℝ) + (cbuf : ℝ)))) →
          (∀ (f : SpatialCoordinates d → ℝ),
            MemLp f (ENNReal.ofReal psource) (volume.restrict (Q : Set (SpatialCoordinates d))) →
            ∀ (fL2 : DomainL2 Q),
              ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                (Q : Set (SpatialCoordinates d))] f) →
            let fNorm : Set (SpatialCoordinates d) → ℝ := fun W =>
              (eLpNorm f (ENNReal.ofReal psource) (volume.restrict W)).toReal /
                (volume.real W) ^ (1 / psource)
            ∀ u : weakSobolevGraph Q,
              (∀ psi : killedSobolevGraph Q,
                sobolevCoefficientForm
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
                  (u : SobolevData Q) (psi : SobolevData Q) =
                sobolevVolumeLoad fL2 (psi : SobolevData Q)) →
              ∃ U : SpatialCoordinates d → ℝ,
                ContinuousOn U (Q : Set (SpatialCoordinates d)) ∧
                (((u : SobolevData Q).1 : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
                (∀ (D : ℕ), D ≤ horizon →
                  ∀ x ∈ (q : Set (SpatialCoordinates d)),
                    let B : Set (SpatialCoordinates d) :=
                      Metric.ball x (qside * (3 : ℝ) ^ (-(D : ℤ)) / 2) ∩
                        (q : Set (SpatialCoordinates d))
                    normalizedL2On B
                      (fun y => U y - (volume.real B)⁻¹ * ∫ t in B, U t) ≤
                      Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ))) *
                        (3 : ℝ) ^ (Cbound * (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)) *
                        (3 : ℝ) ^ (-(D : ℝ)) *
                        (normalizedL2On qp
                          (fun y => U y - (volume.real qp)⁻¹ * ∫ t in qp, U t) +
                          qside ^ 2 * (sN N (k : ℤ) qcenter omega)⁻¹ * fNorm qp)) ∧
                harmonicComparison omega fNorm U) ∧
          (∀ (Uroot : Enl × Shift) (x : Fin d → ℝ),
            Cbound⁻¹ * Matrix.trace (AEN N Uroot omega) * (x ⬝ᵥ x) ≤
              x ⬝ᵥ (AEN N Uroot omega).mulVec x) ∧
          traceEstimate omega) ∧
          (          ((∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D →
              rootLevel U + (D : ℤ) ≤ (N : ℤ) →
              ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
                prefixZ N U D code omega < lambdaCut * (D : ℝ) ∧
                prefixD N U D code omega < lambdaCut * (D : ℝ)) ∧
           (∀ U : Enl × Shift,
              cell ≤ ellLoN N U omega ∧ ellHiN N U omega ≤ cell⁻¹) ∧
           errN N chosen omega ≤ epshom * cdet ∧
           (∀ c : Cmp, ratioN N c omega ∈ Set.Icc (1 / 2 : ℝ) 2)) →
          ((∀ (Uroot : Enl × Shift) (D : ℕ),
            rootLevel Uroot + (D : ℤ) ≤ (N : ℤ) →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              ((Finset.filter
                (fun j : ℤ => j < rootLevel Uroot + (k0 : ℤ) ∨
                  1 ≤ Z N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre Uroot D code) omega)
                (Finset.Icc (rootLevel Uroot - (cbuf : ℤ))
                  (rootLevel Uroot + (D : ℤ)))).card : ℝ) ≤
                (k0 : ℝ) + (cbuf : ℝ) + lambdaDet * (D : ℝ)) ∧
          (∀ (Uroot : Enl × Shift) (D : ℕ),
            rootLevel Uroot + (D : ℤ) ≤ (N : ℤ) →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              (∑ j ∈ Finset.Icc (rootLevel Uroot - (cbuf : ℤ))
                (rootLevel Uroot + (D : ℤ)),
                if rootLevel Uroot + (k0 : ℤ) ≤ j ∧
                    Z N ((N : ℤ) - j).toNat
                      (((3 : ℝ) ^ N) • observationCentre Uroot D code) omega < 1 then
                  let w := observationCentre Uroot D code
                  let rj := (3 : ℝ) ^ (-j)
                  I.err w rj (by positivity)
                    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
                    w rj (sN N j w omega) s 2
                else 0) ≤
                  Cbound * (M.delta ^ 2 + eps ^ 8 + lambdaDet) * (D : ℝ) +
                    Cbound * ((k0 : ℝ) + (cbuf : ℝ))) ∧
          Cbound * (lambdaDet + M.delta ^ 2 + eps ^ 8) < 1 - alpha ∧
          (∃ D0 : ℕ, k0 ≤ D0 ∧ ∀ D : ℕ, D0 ≤ D →
            (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ))) *
              (3 : ℝ) ^ (Cbound * (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)) ≤
                (3 : ℝ) ^ ((1 - alpha) * (D : ℝ)))) →
          (∀ (f : SpatialCoordinates d → ℝ),
            MemLp f (ENNReal.ofReal psource) (volume.restrict (Q : Set (SpatialCoordinates d))) →
            ∀ (fL2 : DomainL2 Q),
              ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                (Q : Set (SpatialCoordinates d))] f) →
            let fNorm : Set (SpatialCoordinates d) → ℝ := fun W =>
              (eLpNorm f (ENNReal.ofReal psource) (volume.restrict W)).toReal /
                (volume.real W) ^ (1 / psource)
            ∀ u : weakSobolevGraph Q,
              (∀ psi : killedSobolevGraph Q,
                sobolevCoefficientForm
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
                  (u : SobolevData Q) (psi : SobolevData Q) =
                sobolevVolumeLoad fL2 (psi : SobolevData Q)) →
              ∃ U : SpatialCoordinates d → ℝ,
                ContinuousOn U (Q : Set (SpatialCoordinates d)) ∧
                (((u : SobolevData Q).1 : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
                _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (closure (q : Set (SpatialCoordinates d))) U ∧
                (∃ cq : ℝ,
                  _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
                    (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
                    (fun x => U (qcenter + qside • x) - cq) ≤
                      Ctotal * (normalizedL2On qp
                        (fun x => U x - (volume.real qp)⁻¹ * ∫ y in qp, U y) +
                        qside ^ 2 * (sN N (k : ℤ) qcenter omega)⁻¹ * fNorm qp)) ∧
                harmonicComparison omega fNorm U) ∧
          (∀ (Uroot : Enl × Shift) (x : Fin d → ℝ),
            Cbound⁻¹ * Matrix.trace (AEN N Uroot omega) * (x ⬝ᵥ x) ≤
              x ⬝ᵥ (AEN N Uroot omega).mulVec x) ∧
          traceEstimate omega)

def aux_in_deterministic_remaining
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha beta s sigma cell epshom : ℝ) : Prop :=
  ∃ Can : ℝ, 1 ≤ Can ∧ ∀ Cbound : ℝ, Can ≤ Cbound →
    ∃ eAn lAn dAn : ℝ, 0 < eAn ∧ 0 < lAn ∧ 0 < dAn ∧
    ∀ eps0 lam0 delta0 : ℝ, 0 < eps0 → eps0 ≤ eAn → 0 < lam0 → lam0 ≤ lAn →
      0 < delta0 → delta0 ≤ dAn →
      aux_in_deterministic_remaining_at d I alpha beta s sigma cell epshom
        Cbound eps0 lam0 delta0

def aux_in_deterministic_R1
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha beta s sigma cell epshom : ℝ)
    (Cbound eps0 lam0 delta0 : ℝ) : Prop :=
      ∀ (cbuf k0 : ℕ)
        (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hMH : InfraredCharacterization M H)
        (k : ℕ) (z : SpatialCoordinates d)
        (qside : ℝ) (hqpos : 0 < qside)
        (hqside : qside = (3 : ℝ) ^ (-(k : ℤ)))
        (qcenter : SpatialCoordinates d)
        (hqcenter : qcenter = z)
        (Enl Shift Cmp : Type)
        [Fintype Enl] [Fintype Shift] [Fintype Cmp]
        (selfE : Enl) (selfShift : Shift)
        (qRoot : Enl × Shift)
        (hqRoot : qRoot = (selfE, selfShift))
        (factor : Enl → ℕ)
        (hfactor : factor selfE = 0)
        (padE : Enl) (hpad : factor padE = 1)
        (shift : Shift → SpatialCoordinates d)
        (hshift : shift selfShift = 0)
        (rootLevel : Enl × Shift → ℤ)
        (hrootLevel : ∀ (e : Enl) (t : Shift),
          rootLevel (e, t) = (k : ℤ) - (factor e : ℤ))
        (rootSide : Enl × Shift → ℝ)
        (hrootSide : ∀ (U : Enl × Shift),
          rootSide U = (3 : ℝ) ^ (-rootLevel U))
        (rootCentre : Enl × Shift → SpatialCoordinates d)
        (hrootCentre : ∀ (e : Enl) (t : Shift),
          rootCentre (e, t) = qcenter + rootSide (e, t) • shift t)
        (rootPos : ∀ (U : Enl × Shift), 0 < rootSide U)
        (hGridCover : ∀ (x : SpatialCoordinates d),
          x ∈ Metric.closedBall z (qside / 2) →
          ∀ rho : ℝ, 0 < rho → rho ≤ qside →
            ∃ (U : Enl × Shift) (D : ℕ) (w : Fin D → OddGridIndex d 1),
              Metric.ball x (rho / 2) ⊆
                Metric.ball (descendantCenter 1 (rootCentre U) (rootSide U) D w)
                  (descendantSide 1 D (rootSide U) / 2) ∧
              descendantSide 1 D (rootSide U) ≤ 9 * rho)
        (parent : Cmp → Enl × Shift)
        (depth : Cmp → ℕ)
        (word : (c : Cmp) → Fin (depth c) → OddGridIndex d 1)
        (cmpCentre : Cmp → SpatialCoordinates d)
        (hcmpCentre : ∀ (c : Cmp),
          cmpCentre c =
            descendantCenter 1 (rootCentre (parent c)) (rootSide (parent c))
              (depth c) (word c))
        (cmpLevel : Cmp → ℤ)
        (hcmpLevel : ∀ (c : Cmp),
          cmpLevel c = rootLevel (parent c) + (depth c : ℤ))
        (cmpSide : Cmp → ℝ)
        (hcmpSide : ∀ (c : Cmp), cmpSide c = (3 : ℝ) ^ (-cmpLevel c))
        (cmpPos : ∀ (c : Cmp), 0 < cmpSide c)
        (chosen : Cmp)
        (observationCentre : ∀ (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            SpatialCoordinates d)
        (hObservationCentre : ∀ (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          observationCentre U D code =
            Sum.elim
              (fun w => descendantCenter 1 (rootCentre U) (rootSide U) D w)
              (fun V => rootCentre V) code)
        (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : Vec d),
            eta N omega i y =
              omega ((i : ℤ) - (N : ℤ))
                (((3 : ℝ) ^ (-(N : ℤ))) • y))
        (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
        (eps : ℝ) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
        (hepsSmall : eps ≤ eps0)
        (hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ N : ℕ,
            primitive_scores d M s eps (eta N omega)
              (fun m y => F N m y omega)
              (fun m y => Praw N m y omega)
              (fun m y => Rraw N m y omega)
              (fun m y => Draw N m y omega)
              (fun m y => Z N m y omega)
              (fun m y => rawGood N m y omega))
        (lambdaCut lambdaLim lambdaDet cdet : ℝ)
        (hThresholds :
          0 < lambdaCut ∧ lambdaCut < lambdaLim ∧
          lambdaLim < lambdaDet ∧ lambdaDet < 1)
        (hcdet : 0 < cdet) (hcdetSmall : cdet ≤ Cbound⁻¹)
        (hlamSmall : lambdaDet ≤ lam0)
        (hdisorder : M.delta ≤ delta0)
        (prefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (prefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (hPrefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift))
          (omega : BilateralField d),
          prefixZ N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  Z N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega
                else 0
            else 0)
        (hPrefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift))
          (omega : BilateralField d),
          prefixD N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  (Draw N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega).toReal
                else 0
            else 0)
        (hFiniteScoreGuard : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
            (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
            rootLevel U + (D : ℤ) ≤ (N : ℤ) →
            ∀ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
              (rootLevel U + (D : ℤ)),
              Draw N ((N : ℤ) - j).toNat
                (((3 : ℝ) ^ N) • observationCentre U D code) omega ≠ ⊤)
        (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
        (hsN : ∀ (N : ℕ) (l : ℤ) (w : SpatialCoordinates d)
          (omega : BilateralField d),
          sN N l w omega =
            if l ≤ (N : ℤ) then
              (let kappa : ℕ → ℝ := fun J =>
                Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
                  SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
               let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
                 fun ell v beta =>
                   if 0 ≤ ell then
                     ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
                   else
                     -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
               kappa ((N : ℤ) - l).toNat / kappa N *
                 Real.exp (H omega w + retained l w omega))
            else 1)
        (ellLoN ellHiN : ℕ → Enl × Shift → BilateralField d → ℝ)
        (hEllLoN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellLoN N U omega =
            I.lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (hEllHiN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellHiN N U omega =
            I.Lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (AEN : ℕ → Enl × Shift → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (hAEN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          AEN N U omega =
            (sN N (rootLevel U) (rootCentre U) omega)⁻¹ •
              Homogenization.Book.Ch02.sigmaCoarse
                (Homogenization.Book.Ch02.cubeDomain
                  (Homogenization.originCube d 0))
                ((I.chart (rootCentre U) (rootSide U) (rootPos U)
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                    (rootCentre U) (rootPos U))
                  (rootCentre U) (rootSide U)).coeffOn
                  (Homogenization.originCube d 0)))
        (errN ratioN : ℕ → Cmp → BilateralField d → ℝ)
        (hErrN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          errN N c omega =
            I.err (cmpCentre c) (cmpSide c) (cmpPos c)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (cmpCentre c) (cmpPos c))
              (cmpCentre c) (cmpSide c)
              (sN N (cmpLevel c) (cmpCentre c) omega) s 2)
        (hRatioN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          ratioN N c omega =
            sN N (k : ℤ) qcenter omega /
              sN N (cmpLevel c) (cmpCentre c) omega)
        (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
        (hRootsQ : ∀ U : Enl × Shift,
          closure (centeredCube (rootCentre U) (rootSide U) (rootPos U) :
            Set (SpatialCoordinates d)) ⊆
            (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ,
      let Q := centeredCube Qcentre Qside hQside
      let q := centeredCube qcenter qside hqpos
      let qp : Set (SpatialCoordinates d) := Metric.ball qcenter (3 * qside / 2)
      let Ctotal := Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ)))
      let psource : ℝ := (d : ℝ) / (1 - alpha)
      ∀ (N : ℕ), k + k0 ≤ N → (∀ c : Cmp, cmpLevel c ≤ (N : ℤ)) →
        let harmonicComparison (omega : BilateralField d)
            (fNorm : Set (SpatialCoordinates d) → ℝ)
            (U : SpatialCoordinates d → ℝ) : Prop :=
          (let qc := centeredCube (cmpCentre chosen) (cmpSide chosen / 81)
                   (div_pos (cmpPos chosen) (by norm_num))
                 let qi : Set (SpatialCoordinates d) :=
                   Metric.ball (cmpCentre chosen) (cmpSide chosen / 1458)
                 let qo : Set (SpatialCoordinates d) :=
                   Metric.ball (cmpCentre chosen) (cmpSide chosen / 18)
                 ∀ w : SpatialCoordinates d,
                 let qd : Set (SpatialCoordinates d) :=
                   Metric.ball w (27 * cmpSide chosen / 2)
                 Metric.closedBall (cmpCentre chosen) (cmpSide chosen / 18) ⊆ qd →
                 qd ⊆ (Q : Set (SpatialCoordinates d)) →
                 ∃ (v : weakSobolevGraph qc) (V : SpatialCoordinates d → ℝ),
                   ContinuousOn V (closure (qc : Set (SpatialCoordinates d))) ∧
                   (((v : SobolevData qc).1 : SpatialCoordinates d → ℝ) =ᵐ[
                     volume.restrict (qc : Set (SpatialCoordinates d))] V) ∧
                   (∀ x ∈ frontier (qc : Set (SpatialCoordinates d)), V x = U x) ∧
                   (∀ psi : killedSobolevGraph qc,
                     inner ℝ (sobolevGradient (v : SobolevData qc))
                       (subspaceGradient (killedSobolevGraph qc) psi) = 0) ∧
                   normalizedL2On qi (fun x => U x - V x) ≤
                     epshom * normalizedL2On qo
                       (fun x => U x - (volume.real qo)⁻¹ * ∫ y in qo, U y) +
                     Ctotal * (cmpSide chosen / 9) ^ 2 *
                       (sN N (cmpLevel chosen) (cmpCentre chosen) omega)⁻¹ * fNorm qd)
        let traceEstimate (omega : BilateralField d) : Prop :=
          (∃ Uq : ℝ,
            Uq = I.Lam qcenter qside hqpos
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N qcenter hqpos)
              qcenter qside sigma 2 ∧
            Cbound⁻¹ * sN N (k : ℤ) qcenter omega ≤ Uq ∧
            Uq ≤ Cbound * sN N (k : ℤ) qcenter omega ∧
            ∀ b : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta qcenter qside b →
              ∃ (extension : weakSobolevGraph q) (B : SpatialCoordinates d → ℝ),
                ContinuousOn B (closure (q : Set (SpatialCoordinates d))) ∧
                (((extension : SobolevData q).1 : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (q : Set (SpatialCoordinates d))] B) ∧
                (∀ x ∈ frontier (q : Set (SpatialCoordinates d)), B x = b x) ∧
                ∀ (Sq : ResponseSpace q), Sq.space = killedSobolevGraph q →
                  dirichletResponse Sq
                    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N qcenter hqpos)
                    extension ≤
                    Cbound * Uq * qside ^ ((d : ℝ) - 2) *
                      cellBoundaryQuotientNorm beta qcenter qside b ^ 2)
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ horizon : ℕ,
          ((∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D → D ≤ horizon →
              rootLevel U + (D : ℤ) ≤ (N : ℤ) →
              ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
                prefixZ N U D code omega < lambdaCut * (D : ℝ) ∧
                prefixD N U D code omega < lambdaCut * (D : ℝ)) ∧
           (∀ U : Enl × Shift,
              cell ≤ ellLoN N U omega ∧ ellHiN N U omega ≤ cell⁻¹) ∧
           errN N chosen omega ≤ epshom * cdet ∧
           (∀ c : Cmp, ratioN N c omega ∈ Set.Icc (1 / 2 : ℝ) 2)) →
          ((∀ (Uroot : Enl × Shift) (D : ℕ), D ≤ horizon →
            rootLevel Uroot + (D : ℤ) ≤ (N : ℤ) →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              ((Finset.filter
                (fun j : ℤ => j < rootLevel Uroot + (k0 : ℤ) ∨
                  1 ≤ Z N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre Uroot D code) omega)
                (Finset.Icc (rootLevel Uroot - (cbuf : ℤ))
                  (rootLevel Uroot + (D : ℤ)))).card : ℝ) ≤
                (k0 : ℝ) + (cbuf : ℝ) + lambdaDet * (D : ℝ)) ∧
          (∀ (Uroot : Enl × Shift) (D : ℕ), D ≤ horizon →
            rootLevel Uroot + (D : ℤ) ≤ (N : ℤ) →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              (∑ j ∈ Finset.Icc (rootLevel Uroot - (cbuf : ℤ))
                (rootLevel Uroot + (D : ℤ)),
                if rootLevel Uroot + (k0 : ℤ) ≤ j ∧
                    Z N ((N : ℤ) - j).toNat
                      (((3 : ℝ) ^ N) • observationCentre Uroot D code) omega < 1 then
                  let w := observationCentre Uroot D code
                  let rj := (3 : ℝ) ^ (-j)
                  I.err w rj (by positivity)
                    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
                    w rj (sN N j w omega) s 2
                else 0) ≤
                  Cbound * (M.delta ^ 2 + eps ^ 8 + lambdaDet) * (D : ℝ) +
                    Cbound * ((k0 : ℝ) + (cbuf : ℝ)))) →
          (∀ (f : SpatialCoordinates d → ℝ),
            MemLp f (ENNReal.ofReal psource) (volume.restrict (Q : Set (SpatialCoordinates d))) →
            ∀ (fL2 : DomainL2 Q),
              ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                (Q : Set (SpatialCoordinates d))] f) →
            let fNorm : Set (SpatialCoordinates d) → ℝ := fun W =>
              (eLpNorm f (ENNReal.ofReal psource) (volume.restrict W)).toReal /
                (volume.real W) ^ (1 / psource)
            ∀ u : weakSobolevGraph Q,
              (∀ psi : killedSobolevGraph Q,
                sobolevCoefficientForm
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
                  (u : SobolevData Q) (psi : SobolevData Q) =
                sobolevVolumeLoad fL2 (psi : SobolevData Q)) →
              ∃ U : SpatialCoordinates d → ℝ,
                ContinuousOn U (Q : Set (SpatialCoordinates d)) ∧
                (((u : SobolevData Q).1 : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
                (∀ (D : ℕ), D ≤ horizon →
                  ∀ x ∈ (q : Set (SpatialCoordinates d)),
                    let B : Set (SpatialCoordinates d) :=
                      Metric.ball x (qside * (3 : ℝ) ^ (-(D : ℤ)) / 2) ∩
                        (q : Set (SpatialCoordinates d))
                    normalizedL2On B
                      (fun y => U y - (volume.real B)⁻¹ * ∫ t in B, U t) ≤
                      Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ))) *
                        (3 : ℝ) ^ (Cbound * (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)) *
                        (3 : ℝ) ^ (-(D : ℝ)) *
                        (normalizedL2On qp
                          (fun y => U y - (volume.real qp)⁻¹ * ∫ t in qp, U t) +
                          qside ^ 2 * (sN N (k : ℤ) qcenter omega)⁻¹ * fNorm qp)) ∧
                harmonicComparison omega fNorm U)

def aux_in_deterministic_R2
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha beta s sigma cell epshom : ℝ)
    (Cbound eps0 lam0 delta0 : ℝ) : Prop :=
      ∀ (cbuf k0 : ℕ)
        (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hMH : InfraredCharacterization M H)
        (k : ℕ) (z : SpatialCoordinates d)
        (qside : ℝ) (hqpos : 0 < qside)
        (hqside : qside = (3 : ℝ) ^ (-(k : ℤ)))
        (qcenter : SpatialCoordinates d)
        (hqcenter : qcenter = z)
        (Enl Shift Cmp : Type)
        [Fintype Enl] [Fintype Shift] [Fintype Cmp]
        (selfE : Enl) (selfShift : Shift)
        (qRoot : Enl × Shift)
        (hqRoot : qRoot = (selfE, selfShift))
        (factor : Enl → ℕ)
        (hfactor : factor selfE = 0)
        (padE : Enl) (hpad : factor padE = 1)
        (shift : Shift → SpatialCoordinates d)
        (hshift : shift selfShift = 0)
        (rootLevel : Enl × Shift → ℤ)
        (hrootLevel : ∀ (e : Enl) (t : Shift),
          rootLevel (e, t) = (k : ℤ) - (factor e : ℤ))
        (rootSide : Enl × Shift → ℝ)
        (hrootSide : ∀ (U : Enl × Shift),
          rootSide U = (3 : ℝ) ^ (-rootLevel U))
        (rootCentre : Enl × Shift → SpatialCoordinates d)
        (hrootCentre : ∀ (e : Enl) (t : Shift),
          rootCentre (e, t) = qcenter + rootSide (e, t) • shift t)
        (rootPos : ∀ (U : Enl × Shift), 0 < rootSide U)
        (hGridCover : ∀ (x : SpatialCoordinates d),
          x ∈ Metric.closedBall z (qside / 2) →
          ∀ rho : ℝ, 0 < rho → rho ≤ qside →
            ∃ (U : Enl × Shift) (D : ℕ) (w : Fin D → OddGridIndex d 1),
              Metric.ball x (rho / 2) ⊆
                Metric.ball (descendantCenter 1 (rootCentre U) (rootSide U) D w)
                  (descendantSide 1 D (rootSide U) / 2) ∧
              descendantSide 1 D (rootSide U) ≤ 9 * rho)
        (parent : Cmp → Enl × Shift)
        (depth : Cmp → ℕ)
        (word : (c : Cmp) → Fin (depth c) → OddGridIndex d 1)
        (cmpCentre : Cmp → SpatialCoordinates d)
        (hcmpCentre : ∀ (c : Cmp),
          cmpCentre c =
            descendantCenter 1 (rootCentre (parent c)) (rootSide (parent c))
              (depth c) (word c))
        (cmpLevel : Cmp → ℤ)
        (hcmpLevel : ∀ (c : Cmp),
          cmpLevel c = rootLevel (parent c) + (depth c : ℤ))
        (cmpSide : Cmp → ℝ)
        (hcmpSide : ∀ (c : Cmp), cmpSide c = (3 : ℝ) ^ (-cmpLevel c))
        (cmpPos : ∀ (c : Cmp), 0 < cmpSide c)
        (chosen : Cmp)
        (observationCentre : ∀ (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            SpatialCoordinates d)
        (hObservationCentre : ∀ (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          observationCentre U D code =
            Sum.elim
              (fun w => descendantCenter 1 (rootCentre U) (rootSide U) D w)
              (fun V => rootCentre V) code)
        (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : Vec d),
            eta N omega i y =
              omega ((i : ℤ) - (N : ℤ))
                (((3 : ℝ) ^ (-(N : ℤ))) • y))
        (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
        (eps : ℝ) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
        (hepsSmall : eps ≤ eps0)
        (hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ N : ℕ,
            primitive_scores d M s eps (eta N omega)
              (fun m y => F N m y omega)
              (fun m y => Praw N m y omega)
              (fun m y => Rraw N m y omega)
              (fun m y => Draw N m y omega)
              (fun m y => Z N m y omega)
              (fun m y => rawGood N m y omega))
        (lambdaCut lambdaLim lambdaDet cdet : ℝ)
        (hThresholds :
          0 < lambdaCut ∧ lambdaCut < lambdaLim ∧
          lambdaLim < lambdaDet ∧ lambdaDet < 1)
        (hcdet : 0 < cdet) (hcdetSmall : cdet ≤ Cbound⁻¹)
        (hlamSmall : lambdaDet ≤ lam0)
        (hdisorder : M.delta ≤ delta0)
        (prefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (prefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (hPrefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift))
          (omega : BilateralField d),
          prefixZ N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  Z N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega
                else 0
            else 0)
        (hPrefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift))
          (omega : BilateralField d),
          prefixD N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  (Draw N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega).toReal
                else 0
            else 0)
        (hFiniteScoreGuard : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
            (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
            rootLevel U + (D : ℤ) ≤ (N : ℤ) →
            ∀ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
              (rootLevel U + (D : ℤ)),
              Draw N ((N : ℤ) - j).toNat
                (((3 : ℝ) ^ N) • observationCentre U D code) omega ≠ ⊤)
        (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
        (hsN : ∀ (N : ℕ) (l : ℤ) (w : SpatialCoordinates d)
          (omega : BilateralField d),
          sN N l w omega =
            if l ≤ (N : ℤ) then
              (let kappa : ℕ → ℝ := fun J =>
                Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
                  SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
               let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
                 fun ell v beta =>
                   if 0 ≤ ell then
                     ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
                   else
                     -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
               kappa ((N : ℤ) - l).toNat / kappa N *
                 Real.exp (H omega w + retained l w omega))
            else 1)
        (ellLoN ellHiN : ℕ → Enl × Shift → BilateralField d → ℝ)
        (hEllLoN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellLoN N U omega =
            I.lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (hEllHiN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellHiN N U omega =
            I.Lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (AEN : ℕ → Enl × Shift → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (hAEN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          AEN N U omega =
            (sN N (rootLevel U) (rootCentre U) omega)⁻¹ •
              Homogenization.Book.Ch02.sigmaCoarse
                (Homogenization.Book.Ch02.cubeDomain
                  (Homogenization.originCube d 0))
                ((I.chart (rootCentre U) (rootSide U) (rootPos U)
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                    (rootCentre U) (rootPos U))
                  (rootCentre U) (rootSide U)).coeffOn
                  (Homogenization.originCube d 0)))
        (errN ratioN : ℕ → Cmp → BilateralField d → ℝ)
        (hErrN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          errN N c omega =
            I.err (cmpCentre c) (cmpSide c) (cmpPos c)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (cmpCentre c) (cmpPos c))
              (cmpCentre c) (cmpSide c)
              (sN N (cmpLevel c) (cmpCentre c) omega) s 2)
        (hRatioN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          ratioN N c omega =
            sN N (k : ℤ) qcenter omega /
              sN N (cmpLevel c) (cmpCentre c) omega)
        (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
        (hRootsQ : ∀ U : Enl × Shift,
          closure (centeredCube (rootCentre U) (rootSide U) (rootPos U) :
            Set (SpatialCoordinates d)) ⊆
            (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ,
      let Q := centeredCube Qcentre Qside hQside
      let q := centeredCube qcenter qside hqpos
      let qp : Set (SpatialCoordinates d) := Metric.ball qcenter (3 * qside / 2)
      let Ctotal := Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ)))
      let psource : ℝ := (d : ℝ) / (1 - alpha)
      ∀ (N : ℕ), k + k0 ≤ N → (∀ c : Cmp, cmpLevel c ≤ (N : ℤ)) →
        let harmonicComparison (omega : BilateralField d)
            (fNorm : Set (SpatialCoordinates d) → ℝ)
            (U : SpatialCoordinates d → ℝ) : Prop :=
          (let qc := centeredCube (cmpCentre chosen) (cmpSide chosen / 81)
                   (div_pos (cmpPos chosen) (by norm_num))
                 let qi : Set (SpatialCoordinates d) :=
                   Metric.ball (cmpCentre chosen) (cmpSide chosen / 1458)
                 let qo : Set (SpatialCoordinates d) :=
                   Metric.ball (cmpCentre chosen) (cmpSide chosen / 18)
                 ∀ w : SpatialCoordinates d,
                 let qd : Set (SpatialCoordinates d) :=
                   Metric.ball w (27 * cmpSide chosen / 2)
                 Metric.closedBall (cmpCentre chosen) (cmpSide chosen / 18) ⊆ qd →
                 qd ⊆ (Q : Set (SpatialCoordinates d)) →
                 ∃ (v : weakSobolevGraph qc) (V : SpatialCoordinates d → ℝ),
                   ContinuousOn V (closure (qc : Set (SpatialCoordinates d))) ∧
                   (((v : SobolevData qc).1 : SpatialCoordinates d → ℝ) =ᵐ[
                     volume.restrict (qc : Set (SpatialCoordinates d))] V) ∧
                   (∀ x ∈ frontier (qc : Set (SpatialCoordinates d)), V x = U x) ∧
                   (∀ psi : killedSobolevGraph qc,
                     inner ℝ (sobolevGradient (v : SobolevData qc))
                       (subspaceGradient (killedSobolevGraph qc) psi) = 0) ∧
                   normalizedL2On qi (fun x => U x - V x) ≤
                     epshom * normalizedL2On qo
                       (fun x => U x - (volume.real qo)⁻¹ * ∫ y in qo, U y) +
                     Ctotal * (cmpSide chosen / 9) ^ 2 *
                       (sN N (cmpLevel chosen) (cmpCentre chosen) omega)⁻¹ * fNorm qd)
        let traceEstimate (omega : BilateralField d) : Prop :=
          (∃ Uq : ℝ,
            Uq = I.Lam qcenter qside hqpos
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N qcenter hqpos)
              qcenter qside sigma 2 ∧
            Cbound⁻¹ * sN N (k : ℤ) qcenter omega ≤ Uq ∧
            Uq ≤ Cbound * sN N (k : ℤ) qcenter omega ∧
            ∀ b : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta qcenter qside b →
              ∃ (extension : weakSobolevGraph q) (B : SpatialCoordinates d → ℝ),
                ContinuousOn B (closure (q : Set (SpatialCoordinates d))) ∧
                (((extension : SobolevData q).1 : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (q : Set (SpatialCoordinates d))] B) ∧
                (∀ x ∈ frontier (q : Set (SpatialCoordinates d)), B x = b x) ∧
                ∀ (Sq : ResponseSpace q), Sq.space = killedSobolevGraph q →
                  dirichletResponse Sq
                    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N qcenter hqpos)
                    extension ≤
                    Cbound * Uq * qside ^ ((d : ℝ) - 2) *
                      cellBoundaryQuotientNorm beta qcenter qside b ^ 2)
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ((∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D →
              rootLevel U + (D : ℤ) ≤ (N : ℤ) →
              ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
                prefixZ N U D code omega < lambdaCut * (D : ℝ) ∧
                prefixD N U D code omega < lambdaCut * (D : ℝ)) ∧
           (∀ U : Enl × Shift,
              cell ≤ ellLoN N U omega ∧ ellHiN N U omega ≤ cell⁻¹) ∧
           errN N chosen omega ≤ epshom * cdet ∧
           (∀ c : Cmp, ratioN N c omega ∈ Set.Icc (1 / 2 : ℝ) 2)) →
          ((∀ (Uroot : Enl × Shift) (D : ℕ),
            rootLevel Uroot + (D : ℤ) ≤ (N : ℤ) →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              ((Finset.filter
                (fun j : ℤ => j < rootLevel Uroot + (k0 : ℤ) ∨
                  1 ≤ Z N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre Uroot D code) omega)
                (Finset.Icc (rootLevel Uroot - (cbuf : ℤ))
                  (rootLevel Uroot + (D : ℤ)))).card : ℝ) ≤
                (k0 : ℝ) + (cbuf : ℝ) + lambdaDet * (D : ℝ)) ∧
          (∀ (Uroot : Enl × Shift) (D : ℕ),
            rootLevel Uroot + (D : ℤ) ≤ (N : ℤ) →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              (∑ j ∈ Finset.Icc (rootLevel Uroot - (cbuf : ℤ))
                (rootLevel Uroot + (D : ℤ)),
                if rootLevel Uroot + (k0 : ℤ) ≤ j ∧
                    Z N ((N : ℤ) - j).toNat
                      (((3 : ℝ) ^ N) • observationCentre Uroot D code) omega < 1 then
                  let w := observationCentre Uroot D code
                  let rj := (3 : ℝ) ^ (-j)
                  I.err w rj (by positivity)
                    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
                    w rj (sN N j w omega) s 2
                else 0) ≤
                  Cbound * (M.delta ^ 2 + eps ^ 8 + lambdaDet) * (D : ℝ) +
                    Cbound * ((k0 : ℝ) + (cbuf : ℝ))) ∧
          Cbound * (lambdaDet + M.delta ^ 2 + eps ^ 8) < 1 - alpha ∧
          (∃ D0 : ℕ, k0 ≤ D0 ∧ ∀ D : ℕ, D0 ≤ D →
            (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ))) *
              (3 : ℝ) ^ (Cbound * (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)) ≤
                (3 : ℝ) ^ ((1 - alpha) * (D : ℝ)))) →
          (∀ (f : SpatialCoordinates d → ℝ),
            MemLp f (ENNReal.ofReal psource) (volume.restrict (Q : Set (SpatialCoordinates d))) →
            ∀ (fL2 : DomainL2 Q),
              ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                (Q : Set (SpatialCoordinates d))] f) →
            let fNorm : Set (SpatialCoordinates d) → ℝ := fun W =>
              (eLpNorm f (ENNReal.ofReal psource) (volume.restrict W)).toReal /
                (volume.real W) ^ (1 / psource)
            ∀ u : weakSobolevGraph Q,
              (∀ psi : killedSobolevGraph Q,
                sobolevCoefficientForm
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
                  (u : SobolevData Q) (psi : SobolevData Q) =
                sobolevVolumeLoad fL2 (psi : SobolevData Q)) →
              ∃ U : SpatialCoordinates d → ℝ,
                ContinuousOn U (Q : Set (SpatialCoordinates d)) ∧
                (((u : SobolevData Q).1 : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
                _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (closure (q : Set (SpatialCoordinates d))) U ∧
                (∃ cq : ℝ,
                  _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
                    (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
                    (fun x => U (qcenter + qside • x) - cq) ≤
                      Ctotal * (normalizedL2On qp
                        (fun x => U x - (volume.real qp)⁻¹ * ∫ y in qp, U y) +
                        qside ^ 2 * (sN N (k : ℤ) qcenter omega)⁻¹ * fNorm qp)) ∧
                harmonicComparison omega fNorm U)

def aux_in_deterministic_R34
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha beta s sigma cell epshom : ℝ)
    (Cbound eps0 lam0 delta0 : ℝ) : Prop :=
      ∀ (cbuf k0 : ℕ)
        (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hMH : InfraredCharacterization M H)
        (k : ℕ) (z : SpatialCoordinates d)
        (qside : ℝ) (hqpos : 0 < qside)
        (hqside : qside = (3 : ℝ) ^ (-(k : ℤ)))
        (qcenter : SpatialCoordinates d)
        (hqcenter : qcenter = z)
        (Enl Shift Cmp : Type)
        [Fintype Enl] [Fintype Shift] [Fintype Cmp]
        (selfE : Enl) (selfShift : Shift)
        (qRoot : Enl × Shift)
        (hqRoot : qRoot = (selfE, selfShift))
        (factor : Enl → ℕ)
        (hfactor : factor selfE = 0)
        (padE : Enl) (hpad : factor padE = 1)
        (shift : Shift → SpatialCoordinates d)
        (hshift : shift selfShift = 0)
        (rootLevel : Enl × Shift → ℤ)
        (hrootLevel : ∀ (e : Enl) (t : Shift),
          rootLevel (e, t) = (k : ℤ) - (factor e : ℤ))
        (rootSide : Enl × Shift → ℝ)
        (hrootSide : ∀ (U : Enl × Shift),
          rootSide U = (3 : ℝ) ^ (-rootLevel U))
        (rootCentre : Enl × Shift → SpatialCoordinates d)
        (hrootCentre : ∀ (e : Enl) (t : Shift),
          rootCentre (e, t) = qcenter + rootSide (e, t) • shift t)
        (rootPos : ∀ (U : Enl × Shift), 0 < rootSide U)
        (hGridCover : ∀ (x : SpatialCoordinates d),
          x ∈ Metric.closedBall z (qside / 2) →
          ∀ rho : ℝ, 0 < rho → rho ≤ qside →
            ∃ (U : Enl × Shift) (D : ℕ) (w : Fin D → OddGridIndex d 1),
              Metric.ball x (rho / 2) ⊆
                Metric.ball (descendantCenter 1 (rootCentre U) (rootSide U) D w)
                  (descendantSide 1 D (rootSide U) / 2) ∧
              descendantSide 1 D (rootSide U) ≤ 9 * rho)
        (parent : Cmp → Enl × Shift)
        (depth : Cmp → ℕ)
        (word : (c : Cmp) → Fin (depth c) → OddGridIndex d 1)
        (cmpCentre : Cmp → SpatialCoordinates d)
        (hcmpCentre : ∀ (c : Cmp),
          cmpCentre c =
            descendantCenter 1 (rootCentre (parent c)) (rootSide (parent c))
              (depth c) (word c))
        (cmpLevel : Cmp → ℤ)
        (hcmpLevel : ∀ (c : Cmp),
          cmpLevel c = rootLevel (parent c) + (depth c : ℤ))
        (cmpSide : Cmp → ℝ)
        (hcmpSide : ∀ (c : Cmp), cmpSide c = (3 : ℝ) ^ (-cmpLevel c))
        (cmpPos : ∀ (c : Cmp), 0 < cmpSide c)
        (chosen : Cmp)
        (observationCentre : ∀ (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            SpatialCoordinates d)
        (hObservationCentre : ∀ (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          observationCentre U D code =
            Sum.elim
              (fun w => descendantCenter 1 (rootCentre U) (rootSide U) D w)
              (fun V => rootCentre V) code)
        (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : Vec d),
            eta N omega i y =
              omega ((i : ℤ) - (N : ℤ))
                (((3 : ℝ) ^ (-(N : ℤ))) • y))
        (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
        (eps : ℝ) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
        (hepsSmall : eps ≤ eps0)
        (hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ N : ℕ,
            primitive_scores d M s eps (eta N omega)
              (fun m y => F N m y omega)
              (fun m y => Praw N m y omega)
              (fun m y => Rraw N m y omega)
              (fun m y => Draw N m y omega)
              (fun m y => Z N m y omega)
              (fun m y => rawGood N m y omega))
        (lambdaCut lambdaLim lambdaDet cdet : ℝ)
        (hThresholds :
          0 < lambdaCut ∧ lambdaCut < lambdaLim ∧
          lambdaLim < lambdaDet ∧ lambdaDet < 1)
        (hcdet : 0 < cdet) (hcdetSmall : cdet ≤ Cbound⁻¹)
        (hlamSmall : lambdaDet ≤ lam0)
        (hdisorder : M.delta ≤ delta0)
        (prefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (prefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (hPrefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift))
          (omega : BilateralField d),
          prefixZ N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  Z N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega
                else 0
            else 0)
        (hPrefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift))
          (omega : BilateralField d),
          prefixD N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  (Draw N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega).toReal
                else 0
            else 0)
        (hFiniteScoreGuard : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
            (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
            rootLevel U + (D : ℤ) ≤ (N : ℤ) →
            ∀ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
              (rootLevel U + (D : ℤ)),
              Draw N ((N : ℤ) - j).toNat
                (((3 : ℝ) ^ N) • observationCentre U D code) omega ≠ ⊤)
        (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
        (hsN : ∀ (N : ℕ) (l : ℤ) (w : SpatialCoordinates d)
          (omega : BilateralField d),
          sN N l w omega =
            if l ≤ (N : ℤ) then
              (let kappa : ℕ → ℝ := fun J =>
                Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
                  SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
               let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
                 fun ell v beta =>
                   if 0 ≤ ell then
                     ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
                   else
                     -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
               kappa ((N : ℤ) - l).toNat / kappa N *
                 Real.exp (H omega w + retained l w omega))
            else 1)
        (ellLoN ellHiN : ℕ → Enl × Shift → BilateralField d → ℝ)
        (hEllLoN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellLoN N U omega =
            I.lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (hEllHiN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellHiN N U omega =
            I.Lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (AEN : ℕ → Enl × Shift → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (hAEN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          AEN N U omega =
            (sN N (rootLevel U) (rootCentre U) omega)⁻¹ •
              Homogenization.Book.Ch02.sigmaCoarse
                (Homogenization.Book.Ch02.cubeDomain
                  (Homogenization.originCube d 0))
                ((I.chart (rootCentre U) (rootSide U) (rootPos U)
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                    (rootCentre U) (rootPos U))
                  (rootCentre U) (rootSide U)).coeffOn
                  (Homogenization.originCube d 0)))
        (errN ratioN : ℕ → Cmp → BilateralField d → ℝ)
        (hErrN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          errN N c omega =
            I.err (cmpCentre c) (cmpSide c) (cmpPos c)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (cmpCentre c) (cmpPos c))
              (cmpCentre c) (cmpSide c)
              (sN N (cmpLevel c) (cmpCentre c) omega) s 2)
        (hRatioN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          ratioN N c omega =
            sN N (k : ℤ) qcenter omega /
              sN N (cmpLevel c) (cmpCentre c) omega)
        (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
        (hRootsQ : ∀ U : Enl × Shift,
          closure (centeredCube (rootCentre U) (rootSide U) (rootPos U) :
            Set (SpatialCoordinates d)) ⊆
            (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ,
      let Q := centeredCube Qcentre Qside hQside
      let q := centeredCube qcenter qside hqpos
      let qp : Set (SpatialCoordinates d) := Metric.ball qcenter (3 * qside / 2)
      let Ctotal := Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ)))
      let psource : ℝ := (d : ℝ) / (1 - alpha)
      ∀ (N : ℕ), k + k0 ≤ N → (∀ c : Cmp, cmpLevel c ≤ (N : ℤ)) →
        let harmonicComparison (omega : BilateralField d)
            (fNorm : Set (SpatialCoordinates d) → ℝ)
            (U : SpatialCoordinates d → ℝ) : Prop :=
          (let qc := centeredCube (cmpCentre chosen) (cmpSide chosen / 81)
                   (div_pos (cmpPos chosen) (by norm_num))
                 let qi : Set (SpatialCoordinates d) :=
                   Metric.ball (cmpCentre chosen) (cmpSide chosen / 1458)
                 let qo : Set (SpatialCoordinates d) :=
                   Metric.ball (cmpCentre chosen) (cmpSide chosen / 18)
                 ∀ w : SpatialCoordinates d,
                 let qd : Set (SpatialCoordinates d) :=
                   Metric.ball w (27 * cmpSide chosen / 2)
                 Metric.closedBall (cmpCentre chosen) (cmpSide chosen / 18) ⊆ qd →
                 qd ⊆ (Q : Set (SpatialCoordinates d)) →
                 ∃ (v : weakSobolevGraph qc) (V : SpatialCoordinates d → ℝ),
                   ContinuousOn V (closure (qc : Set (SpatialCoordinates d))) ∧
                   (((v : SobolevData qc).1 : SpatialCoordinates d → ℝ) =ᵐ[
                     volume.restrict (qc : Set (SpatialCoordinates d))] V) ∧
                   (∀ x ∈ frontier (qc : Set (SpatialCoordinates d)), V x = U x) ∧
                   (∀ psi : killedSobolevGraph qc,
                     inner ℝ (sobolevGradient (v : SobolevData qc))
                       (subspaceGradient (killedSobolevGraph qc) psi) = 0) ∧
                   normalizedL2On qi (fun x => U x - V x) ≤
                     epshom * normalizedL2On qo
                       (fun x => U x - (volume.real qo)⁻¹ * ∫ y in qo, U y) +
                     Ctotal * (cmpSide chosen / 9) ^ 2 *
                       (sN N (cmpLevel chosen) (cmpCentre chosen) omega)⁻¹ * fNorm qd)
        let traceEstimate (omega : BilateralField d) : Prop :=
          (∃ Uq : ℝ,
            Uq = I.Lam qcenter qside hqpos
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N qcenter hqpos)
              qcenter qside sigma 2 ∧
            Cbound⁻¹ * sN N (k : ℤ) qcenter omega ≤ Uq ∧
            Uq ≤ Cbound * sN N (k : ℤ) qcenter omega ∧
            ∀ b : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta qcenter qside b →
              ∃ (extension : weakSobolevGraph q) (B : SpatialCoordinates d → ℝ),
                ContinuousOn B (closure (q : Set (SpatialCoordinates d))) ∧
                (((extension : SobolevData q).1 : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (q : Set (SpatialCoordinates d))] B) ∧
                (∀ x ∈ frontier (q : Set (SpatialCoordinates d)), B x = b x) ∧
                ∀ (Sq : ResponseSpace q), Sq.space = killedSobolevGraph q →
                  dirichletResponse Sq
                    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N qcenter hqpos)
                    extension ≤
                    Cbound * Uq * qside ^ ((d : ℝ) - 2) *
                      cellBoundaryQuotientNorm beta qcenter qside b ^ 2)
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          (∀ horizon : ℕ,
          ((∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D → D ≤ horizon →
              rootLevel U + (D : ℤ) ≤ (N : ℤ) →
              ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
                prefixZ N U D code omega < lambdaCut * (D : ℝ) ∧
                prefixD N U D code omega < lambdaCut * (D : ℝ)) ∧
           (∀ U : Enl × Shift,
              cell ≤ ellLoN N U omega ∧ ellHiN N U omega ≤ cell⁻¹) ∧
           errN N chosen omega ≤ epshom * cdet ∧
           (∀ c : Cmp, ratioN N c omega ∈ Set.Icc (1 / 2 : ℝ) 2)) →
          ((∀ (Uroot : Enl × Shift) (D : ℕ), D ≤ horizon →
            rootLevel Uroot + (D : ℤ) ≤ (N : ℤ) →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              ((Finset.filter
                (fun j : ℤ => j < rootLevel Uroot + (k0 : ℤ) ∨
                  1 ≤ Z N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre Uroot D code) omega)
                (Finset.Icc (rootLevel Uroot - (cbuf : ℤ))
                  (rootLevel Uroot + (D : ℤ)))).card : ℝ) ≤
                (k0 : ℝ) + (cbuf : ℝ) + lambdaDet * (D : ℝ)) ∧
          (∀ (Uroot : Enl × Shift) (D : ℕ), D ≤ horizon →
            rootLevel Uroot + (D : ℤ) ≤ (N : ℤ) →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              (∑ j ∈ Finset.Icc (rootLevel Uroot - (cbuf : ℤ))
                (rootLevel Uroot + (D : ℤ)),
                if rootLevel Uroot + (k0 : ℤ) ≤ j ∧
                    Z N ((N : ℤ) - j).toNat
                      (((3 : ℝ) ^ N) • observationCentre Uroot D code) omega < 1 then
                  let w := observationCentre Uroot D code
                  let rj := (3 : ℝ) ^ (-j)
                  I.err w rj (by positivity)
                    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
                    w rj (sN N j w omega) s 2
                else 0) ≤
                  Cbound * (M.delta ^ 2 + eps ^ 8 + lambdaDet) * (D : ℝ) +
                    Cbound * ((k0 : ℝ) + (cbuf : ℝ)))) →
          ((∀ (Uroot : Enl × Shift) (x : Fin d → ℝ),
            Cbound⁻¹ * Matrix.trace (AEN N Uroot omega) * (x ⬝ᵥ x) ≤
              x ⬝ᵥ (AEN N Uroot omega).mulVec x) ∧
          traceEstimate omega)) ∧
          (((∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D →
              rootLevel U + (D : ℤ) ≤ (N : ℤ) →
              ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
                prefixZ N U D code omega < lambdaCut * (D : ℝ) ∧
                prefixD N U D code omega < lambdaCut * (D : ℝ)) ∧
           (∀ U : Enl × Shift,
              cell ≤ ellLoN N U omega ∧ ellHiN N U omega ≤ cell⁻¹) ∧
           errN N chosen omega ≤ epshom * cdet ∧
           (∀ c : Cmp, ratioN N c omega ∈ Set.Icc (1 / 2 : ℝ) 2)) →
          ((∀ (Uroot : Enl × Shift) (D : ℕ),
            rootLevel Uroot + (D : ℤ) ≤ (N : ℤ) →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              ((Finset.filter
                (fun j : ℤ => j < rootLevel Uroot + (k0 : ℤ) ∨
                  1 ≤ Z N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre Uroot D code) omega)
                (Finset.Icc (rootLevel Uroot - (cbuf : ℤ))
                  (rootLevel Uroot + (D : ℤ)))).card : ℝ) ≤
                (k0 : ℝ) + (cbuf : ℝ) + lambdaDet * (D : ℝ)) ∧
          (∀ (Uroot : Enl × Shift) (D : ℕ),
            rootLevel Uroot + (D : ℤ) ≤ (N : ℤ) →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              (∑ j ∈ Finset.Icc (rootLevel Uroot - (cbuf : ℤ))
                (rootLevel Uroot + (D : ℤ)),
                if rootLevel Uroot + (k0 : ℤ) ≤ j ∧
                    Z N ((N : ℤ) - j).toNat
                      (((3 : ℝ) ^ N) • observationCentre Uroot D code) omega < 1 then
                  let w := observationCentre Uroot D code
                  let rj := (3 : ℝ) ^ (-j)
                  I.err w rj (by positivity)
                    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
                    w rj (sN N j w omega) s 2
                else 0) ≤
                  Cbound * (M.delta ^ 2 + eps ^ 8 + lambdaDet) * (D : ℝ) +
                    Cbound * ((k0 : ℝ) + (cbuf : ℝ))) ∧
          Cbound * (lambdaDet + M.delta ^ 2 + eps ^ 8) < 1 - alpha ∧
          (∃ D0 : ℕ, k0 ≤ D0 ∧ ∀ D : ℕ, D0 ≤ D →
            (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ))) *
              (3 : ℝ) ^ (Cbound * (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)) ≤
                (3 : ℝ) ^ ((1 - alpha) * (D : ℝ)))) →
          ((∀ (Uroot : Enl × Shift) (x : Fin d → ℝ),
            Cbound⁻¹ * Matrix.trace (AEN N Uroot omega) * (x ⬝ᵥ x) ≤
              x ⬝ᵥ (AEN N Uroot omega).mulVec x) ∧
          traceEstimate omega))




/-- Parameter choice after `Cbound`, below arbitrary positive caps. -/
lemma aux_in_deterministic_params_caps (alpha Cbound delta1 eCap lCap : ℝ)
    (halpha : alpha < 1) (hC : 0 < Cbound) (hd1 : 0 < delta1) (he : 0 < eCap)
    (hl : 0 < lCap) :
    ∃ eps0 lam0 delta0 : ℝ, 0 < eps0 ∧ 0 < lam0 ∧ 0 < delta0 ∧ eps0 ≤ eCap ∧
      lam0 ≤ lCap ∧ delta0 ≤ delta1 ∧
      Cbound * (lam0 + delta0 ^ 2 + eps0 ^ 8) < 1 - alpha := by
  obtain ⟨e0, l0, d0, he0, hl0, hd0, hd0le, hsub⟩ :=
    aux_in_deterministic_budget_assembly_params alpha Cbound delta1 halpha hC hd1
  refine ⟨min e0 eCap, min l0 lCap, d0, lt_min he0 he, lt_min hl0 hl, hd0, min_le_right _ _,
    min_le_right _ _, hd0le, lt_of_le_of_lt ?_ hsub⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  have h1 : min l0 lCap ≤ l0 := min_le_left _ _
  have h2 : (min e0 eCap) ^ 8 ≤ e0 ^ 8 :=
    pow_le_pow_left₀ (lt_min he0 he).le (min_le_left _ _) 8
  linarith

/-- The body at fixed constants from the proved transfer and the remaining obligation. -/
theorem aux_in_deterministic_body_of
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha beta s sigma cell epshom : ℝ)
    (Cg delta1 : ℝ) (hCg : 0 < Cg)
    (hT : aux_in_deterministic_budget_assembly_transfer_at d I s Cg delta1)
    (Cbound eps0 lam0 delta0 : ℝ) (hCgC : Cg ≤ Cbound) (hdd : delta0 ≤ delta1)
    (hsub : Cbound * (lam0 + delta0 ^ 2 + eps0 ^ 8) < 1 - alpha)
    (hRemP : aux_in_deterministic_remaining_at d I alpha beta s sigma cell epshom
      Cbound eps0 lam0 delta0) :
    aux_in_deterministic_body d I alpha beta s sigma cell epshom
      Cbound eps0 lam0 delta0 := by
  intro cbuf k0 M H hMH k z qside hqpos hqside qcenter hqcenter Enl Shift Cmp _ _ _
    selfE selfShift qRoot hqRoot factor hfactor padE hpad shift hshift rootLevel hrootLevel
    rootSide hrootSide rootCentre hrootCentre rootPos hGridCover parent depth word cmpCentre
    hcmpCentre cmpLevel hcmpLevel cmpSide hcmpSide cmpPos chosen observationCentre
    hObservationCentre eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive
    lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall hdisorder
    prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard sN hsN ellLoN ellHiN hEllLoN hEllHiN
    AEN hAEN errN ratioN hErrN hRatioN Qcentre Qside hQside hRootsQ
    Q q qp Ctotal psource N hkN hcmp harmonicComparison traceEstimate
  have hR := hRemP cbuf k0 M H hMH k z qside hqpos hqside qcenter hqcenter Enl Shift Cmp
    selfE selfShift qRoot hqRoot factor hfactor padE hpad shift hshift rootLevel hrootLevel
    rootSide hrootSide rootCentre hrootCentre rootPos hGridCover parent depth word cmpCentre
    hcmpCentre cmpLevel hcmpLevel cmpSide hcmpSide cmpPos chosen observationCentre
    hObservationCentre eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive
    lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall hdisorder
    prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard sN hsN ellLoN ellHiN hEllLoN hEllHiN
    AEN hAEN errN ratioN hErrN hRatioN Qcentre Qside hQside hRootsQ N hkN hcmp
  have hCb0 : 0 ≤ Cbound := hCg.le.trans hCgC
  have hT' := hT M H hMH (hdisorder.trans hdd) eps heps eta F Praw Rraw Draw Z rawGood
    hEta hPrimitive sN hsN
  have hZnn : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N m : ℕ) (y : Vec d), 0 ≤ Z N m y omega := by
    filter_upwards [hPrimitive] with omega hP
    intro N m y
    obtain ⟨_, _, _, _, _, _, _, _, _, hZdef, _⟩ := hP N
    exact (hZdef m y).2.1
  have hU0 : rootLevel qRoot ≤ (N : ℤ) := by
    rw [hqRoot, hrootLevel, hfactor]
    push_cast
    omega
  have hBfull := aux_in_deterministic_budget_assembly_budget d I s Cg Cbound hCg.le hCgC cbuf k0 M H
    Enl Shift rootLevel observationCentre Draw Z eps heps.1.le lambdaCut lambdaDet
    hThresholds.1 (hThresholds.2.1.trans hThresholds.2.2.1) prefixZ prefixD hPrefixZ
    hPrefixD hFiniteScoreGuard sN hZnn hT' N qRoot hU0 (fun _ => True) trivial
  have hBh := fun horizon : ℕ => aux_in_deterministic_budget_assembly_budget d I s Cg Cbound hCg.le
    hCgC cbuf k0 M H Enl Shift rootLevel observationCentre Draw Z eps heps.1.le lambdaCut
    lambdaDet hThresholds.1 (hThresholds.2.1.trans hThresholds.2.2.1) prefixZ prefixD
    hPrefixZ hPrefixD hFiniteScoreGuard sN hZnn hT' N qRoot hU0 (fun D => D ≤ horizon)
    (Nat.zero_le horizon)
  have hBh' := ae_all_iff.2 hBh
  have hsubc : Cbound * (lambdaDet + M.delta ^ 2 + eps ^ 8) < 1 - alpha := by
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left ?_ hCb0) hsub
    have h1 : M.delta ^ 2 ≤ delta0 ^ 2 :=
      pow_le_pow_left₀ M.shellPrefix.delta_pos.le hdisorder 2
    have h2 : eps ^ 8 ≤ eps0 ^ 8 := pow_le_pow_left₀ heps.1.le hepsSmall 8
    linarith
  filter_upwards [hR, hBfull, hBh'] with omega hRw hBfw hBhw
  refine ⟨fun horizon hev => hRw.1 horizon hev (hBhw horizon hev.1), fun hev => ?_⟩
  obtain ⟨hcard, herr⟩ := hBfw (fun U D hD _ hN code => hev.1 U D hD hN code)
  have hrest := hRw.2 hev ⟨fun U D hN code => hcard U D trivial hN code,
    fun U D hN code => herr U D trivial hN code, hsubc,
    aux_in_deterministic_budget_assembly_absorb alpha _ _ k0 cbuf hsubc⟩
  exact ⟨fun U D hN code => hcard U D trivial hN code,
    fun U D hN code => herr U D trivial hN code, hsubc,
    aux_in_deterministic_budget_assembly_absorb alpha _ _ k0 cbuf hsubc, hrest⟩

/-- Constants in the required order, against the folded body. -/
theorem aux_in_deterministic_exists
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha beta s sigma cell epshom : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hsSmall : s ≤ (1 / 32 : ℝ))
    (hRem : aux_in_deterministic_remaining d I alpha beta s sigma cell epshom) :
    ∃ Cbound eps0 lam0 delta0 : ℝ,
      1 ≤ Cbound ∧ 0 < eps0 ∧ 0 < lam0 ∧ 0 < delta0 ∧
      aux_in_deterministic_body d I alpha beta s sigma cell epshom
        Cbound eps0 lam0 delta0 := by
  obtain ⟨Cg, delta1, hCg, hdelta1, hT⟩ :=
    aux_in_deterministic_budget_assembly_transfer d I s hs hsSmall
  obtain ⟨Can, hCan, hRemC⟩ := hRem
  obtain ⟨eAn, lAn, dAn, heAn, hlAn, hdAn, hRemP⟩ :=
    hRemC (max Can (max Cg 1)) (le_max_left _ _)
  have hCb1 : 1 ≤ max Can (max Cg 1) := hCan.trans (le_max_left _ _)
  obtain ⟨eps0, lam0, delta0, he0, hl0, hd0, he0c, hl0c, hd0c, hsub⟩ :=
    aux_in_deterministic_params_caps alpha (max Can (max Cg 1)) (min delta1 dAn)
      eAn lAn halpha.2 (by linarith) (lt_min hdelta1 hdAn) heAn hlAn
  exact ⟨max Can (max Cg 1), eps0, lam0, delta0, hCb1, he0, hl0, hd0,
    aux_in_deterministic_body_of d I alpha beta s sigma cell epshom Cg delta1 hCg hT
      _ eps0 lam0 delta0 ((le_max_left _ _).trans (le_max_right _ _))
      (hd0c.trans (min_le_left _ _)) hsub
      (hRemP eps0 lam0 delta0 he0 he0c hl0 hl0c hd0 (hd0c.trans (min_le_right _ _)))⟩

/-- `remaining_at` is exactly the conjunction of R1, R2 and R3/R4. -/
theorem aux_in_deterministic_split
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha beta s sigma cell epshom : ℝ)
    (Cbound eps0 lam0 delta0 : ℝ)
    (h1 : aux_in_deterministic_R1 d I alpha beta s sigma cell epshom Cbound eps0 lam0 delta0)
    (h2 : aux_in_deterministic_R2 d I alpha beta s sigma cell epshom Cbound eps0 lam0 delta0)
    (h34 : aux_in_deterministic_R34 d I alpha beta s sigma cell epshom Cbound eps0 lam0 delta0) :
    aux_in_deterministic_remaining_at d I alpha beta s sigma cell epshom Cbound eps0 lam0 delta0 := by
  intro cbuf k0 M H hMH k z qside hqpos hqside qcenter hqcenter Enl Shift Cmp _ _ _
    selfE selfShift qRoot hqRoot factor hfactor padE hpad shift hshift rootLevel hrootLevel
    rootSide hrootSide rootCentre hrootCentre rootPos hGridCover parent depth word cmpCentre
    hcmpCentre cmpLevel hcmpLevel cmpSide hcmpSide cmpPos chosen observationCentre
    hObservationCentre eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive
    lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall hdisorder
    prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard sN hsN ellLoN ellHiN hEllLoN hEllHiN
    AEN hAEN errN ratioN hErrN hRatioN Qcentre Qside hQside hRootsQ
    Q q qp Ctotal psource N hkN hcmp harmonicComparison traceEstimate
  have a1 := h1 cbuf k0 M H hMH k z qside hqpos hqside qcenter hqcenter Enl Shift Cmp
      selfE selfShift qRoot hqRoot factor hfactor padE hpad shift hshift rootLevel hrootLevel
      rootSide hrootSide rootCentre hrootCentre rootPos hGridCover parent depth word cmpCentre
      hcmpCentre cmpLevel hcmpLevel cmpSide hcmpSide cmpPos chosen observationCentre
      hObservationCentre eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive
      lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall hdisorder
      prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard sN hsN ellLoN ellHiN hEllLoN hEllHiN
      AEN hAEN errN ratioN hErrN hRatioN Qcentre Qside hQside hRootsQ N hkN hcmp
  have a2 := h2 cbuf k0 M H hMH k z qside hqpos hqside qcenter hqcenter Enl Shift Cmp
      selfE selfShift qRoot hqRoot factor hfactor padE hpad shift hshift rootLevel hrootLevel
      rootSide hrootSide rootCentre hrootCentre rootPos hGridCover parent depth word cmpCentre
      hcmpCentre cmpLevel hcmpLevel cmpSide hcmpSide cmpPos chosen observationCentre
      hObservationCentre eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive
      lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall hdisorder
      prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard sN hsN ellLoN ellHiN hEllLoN hEllHiN
      AEN hAEN errN ratioN hErrN hRatioN Qcentre Qside hQside hRootsQ N hkN hcmp
  have a3 := h34 cbuf k0 M H hMH k z qside hqpos hqside qcenter hqcenter Enl Shift Cmp
      selfE selfShift qRoot hqRoot factor hfactor padE hpad shift hshift rootLevel hrootLevel
      rootSide hrootSide rootCentre hrootCentre rootPos hGridCover parent depth word cmpCentre
      hcmpCentre cmpLevel hcmpLevel cmpSide hcmpSide cmpPos chosen observationCentre
      hObservationCentre eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive
      lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall hdisorder
      prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard sN hsN ellLoN ellHiN hEllLoN hEllHiN
      AEN hAEN errN ratioN hErrN hRatioN Qcentre Qside hQside hRootsQ N hkN hcmp
  filter_upwards [a1, a2, a3] with omega b1 b2 b3
  exact ⟨fun horizon hev hb =>
      ⟨b1 horizon hev hb, (b3.1 horizon hev hb).1, (b3.1 horizon hev hb).2⟩,
    fun hev hb => ⟨b2 hev hb, (b3.2 hev hb).1, (b3.2 hev hb).2⟩⟩

/-- G2: the R3/R4 slice at every `Cbound ≥ Cr`, for all `eps0 lam0 delta0`. -/
theorem aux_in_deterministic_R34_holds
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (X : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (alpha beta s sigma cell epshom : ℝ)
    (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hsigma_eq : sigma = (beta - 1 / 2) / 4)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (hcell : cell ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ Cr : ℝ, 1 ≤ Cr ∧ ∀ Cbound : ℝ, Cr ≤ Cbound → ∀ eps0 lam0 delta0 : ℝ,
      aux_in_deterministic_R34 d I alpha beta s sigma cell epshom
        Cbound eps0 lam0 delta0 := by
  obtain ⟨Cr, hCr1, hCr⟩ := aux_in_deterministic_R34_pointwise d hd I X Sob beta sigma cell
    hbeta hsigma_eq hsigma hcell
  refine ⟨Cr, hCr1, fun Cbound hCb eps0 lam0 delta0 => ?_⟩
  intro cbuf k0 M H hMH k z qside hqpos hqside qcenter hqcenter Enl Shift Cmp _ _ _
    selfE selfShift qRoot hqRoot factor hfactor padE hpad shift hshift rootLevel hrootLevel
    rootSide hrootSide rootCentre hrootCentre rootPos hGridCover parent depth word cmpCentre
    hcmpCentre cmpLevel hcmpLevel cmpSide hcmpSide cmpPos chosen observationCentre
    hObservationCentre eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive
    lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall hdisorder
    prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard sN hsN ellLoN ellHiN hEllLoN hEllHiN
    AEN hAEN errN ratioN hErrN hRatioN Qcentre Qside hQside hRootsQ
    Q q qp Ctotal psource N hkN hcmp harmonicComparison traceEstimate
  have key := hCr Cbound hCb M H k z qside hqpos hqside qcenter hqcenter Enl Shift
    selfE selfShift qRoot hqRoot factor hfactor padE hpad shift hshift rootLevel hrootLevel
    rootSide hrootSide rootCentre hrootCentre rootPos sN ellLoN ellHiN hEllLoN hEllHiN
    AEN hAEN N
  exact Filter.Eventually.of_forall (fun omega =>
    ⟨fun _ hev _ => key omega hev.2.1, fun hev _ => key omega hev.2.1⟩)


/-- Constant bookkeeping: `R1`, `R2` (each with its own threshold and caps) and the
`R3/R4` slice (threshold only) give `aux_in_deterministic_remaining`. -/
theorem aux_in_deterministic_remaining_of_parts
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha beta s sigma cell epshom : ℝ)
    (h1 : ∃ C1 : ℝ, 1 ≤ C1 ∧ ∀ Cbound : ℝ, C1 ≤ Cbound →
      ∃ e1 l1 d1 : ℝ, 0 < e1 ∧ 0 < l1 ∧ 0 < d1 ∧
      ∀ eps0 lam0 delta0 : ℝ, 0 < eps0 → eps0 ≤ e1 → 0 < lam0 → lam0 ≤ l1 →
        0 < delta0 → delta0 ≤ d1 →
        aux_in_deterministic_R1 d I alpha beta s sigma cell epshom Cbound eps0 lam0 delta0)
    (h2 : ∃ C2 : ℝ, 1 ≤ C2 ∧ ∀ Cbound : ℝ, C2 ≤ Cbound →
      ∃ e2 l2 d2 : ℝ, 0 < e2 ∧ 0 < l2 ∧ 0 < d2 ∧
      ∀ eps0 lam0 delta0 : ℝ, 0 < eps0 → eps0 ≤ e2 → 0 < lam0 → lam0 ≤ l2 →
        0 < delta0 → delta0 ≤ d2 →
        aux_in_deterministic_R2 d I alpha beta s sigma cell epshom Cbound eps0 lam0 delta0)
    (h34 : ∃ Cr : ℝ, 1 ≤ Cr ∧ ∀ Cbound : ℝ, Cr ≤ Cbound → ∀ eps0 lam0 delta0 : ℝ,
      aux_in_deterministic_R34 d I alpha beta s sigma cell epshom Cbound eps0 lam0 delta0) :
    aux_in_deterministic_remaining d I alpha beta s sigma cell epshom := by
  obtain ⟨C1, hC1, hR1⟩ := h1
  obtain ⟨C2, hC2, hR2⟩ := h2
  obtain ⟨Cr, hCr, hR34⟩ := h34
  refine ⟨max C1 (max C2 Cr), hC1.trans (le_max_left _ _), fun Cbound hCb => ?_⟩
  have hb1 : C1 ≤ Cbound := (le_max_left _ _).trans hCb
  have hb2 : C2 ≤ Cbound := ((le_max_left _ _).trans (le_max_right _ _)).trans hCb
  have hb3 : Cr ≤ Cbound := ((le_max_right _ _).trans (le_max_right _ _)).trans hCb
  obtain ⟨e1, l1, d1, he1, hl1, hd1, hA⟩ := hR1 Cbound hb1
  obtain ⟨e2, l2, d2, he2, hl2, hd2, hB⟩ := hR2 Cbound hb2
  refine ⟨min e1 e2, min l1 l2, min d1 d2, lt_min he1 he2, lt_min hl1 hl2, lt_min hd1 hd2,
    fun eps0 lam0 delta0 he0 he0c hl0 hl0c hd0 hd0c => ?_⟩
  exact aux_in_deterministic_split d I alpha beta s sigma cell epshom Cbound eps0 lam0 delta0
    (hA eps0 lam0 delta0 he0 (he0c.trans (min_le_left _ _)) hl0 (hl0c.trans (min_le_left _ _))
      hd0 (hd0c.trans (min_le_left _ _)))
    (hB eps0 lam0 delta0 he0 (he0c.trans (min_le_right _ _)) hl0 (hl0c.trans (min_le_right _ _))
      hd0 (hd0c.trans (min_le_right _ _)))
    (hR34 Cbound hb3 eps0 lam0 delta0)

/-! ## Auxiliary proof steps (true, bounded; binders = the principal's carriers only) -/

/-- R1 and R2 from the carried `deterministic_good_scale_input` (`InDetCore.Final`): the
one-step window (clause 2 via `aux_prop_folded_iteration_interior_excess_decay`) gives `camp`
through the iteration lemma, the D3 harmonic window (clause 2 plus the boundary-continuous
harmonic replacement) gives `harm`, and `cont` holds for every `alpha ∈ (0,1)`. -/
theorem aux_in_deterministic_R12_holds
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (_X : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (_Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (_MeyersMorrey : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (_Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (_Det : _root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d)
    (alpha beta s sigma cell epshom : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1)
    (_hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (hsSmall : s ≤ (1 / 32 : ℝ))
    (_hsigma_eq : sigma = (beta - 1 / 2) / 4)
    (_hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (_hcell : cell ∈ Set.Ioo (0 : ℝ) 1)
    (hepshom : 0 < epshom) :
    ∃ C1 : ℝ, 1 ≤ C1 ∧ ∀ Cbound : ℝ, C1 ≤ Cbound →
      ∃ e1 l1 d1 : ℝ, 0 < e1 ∧ 0 < l1 ∧ 0 < d1 ∧
      ∀ eps0 lam0 delta0 : ℝ, 0 < eps0 → eps0 ≤ e1 → 0 < lam0 → lam0 ≤ l1 →
        0 < delta0 → delta0 ≤ d1 →
        aux_in_deterministic_R1 d I alpha beta s sigma cell epshom Cbound eps0 lam0 delta0 ∧
        aux_in_deterministic_R2 d I alpha beta s sigma cell epshom Cbound eps0 lam0 delta0 := by
  exact aux_in_deterministic_core_R12 d hd I _Det alpha beta s sigma cell epshom halpha hs hsSmall
    hepshom

/-- **R1** (finite-horizon Campanato branch + harmonic comparison with room, D3).
For every horizon, on the horizon event (with the horizon budget as an extra, ignorable
premise), every sourced native weak solution has a continuous representative with the
finite-depth Campanato bound at the displayed loss, and the chosen-cube harmonic comparison
for every room ball `qd = ball w (27 cmpSide/2)`.  Monotone in `Cbound`; caps after `Cbound`.
Proved from `aux_in_deterministic_R12_holds`: (A) and (B) are supplied by `_Det` clause 2 (D1),
and (C) is removed by the D2 guard. -/
theorem aux_in_deterministic_R1_holds
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (_X : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (_Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (_MeyersMorrey : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (_Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (_Det : _root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d)
    (alpha beta s sigma cell epshom : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1)
    (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (hsSmall : s ≤ (1 / 32 : ℝ))
    (hsigma_eq : sigma = (beta - 1 / 2) / 4)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (hcell : cell ∈ Set.Ioo (0 : ℝ) 1)
    (hepshom : 0 < epshom) :
    ∃ C1 : ℝ, 1 ≤ C1 ∧ ∀ Cbound : ℝ, C1 ≤ Cbound →
      ∃ e1 l1 d1 : ℝ, 0 < e1 ∧ 0 < l1 ∧ 0 < d1 ∧
      ∀ eps0 lam0 delta0 : ℝ, 0 < eps0 → eps0 ≤ e1 → 0 < lam0 → lam0 ≤ l1 →
        0 < delta0 → delta0 ≤ d1 →
        aux_in_deterministic_R1 d I alpha beta s sigma cell epshom Cbound eps0 lam0 delta0 := by
  obtain ⟨C1, hC1, hR⟩ := aux_in_deterministic_R12_holds d hd I _X _Sob _MeyersMorrey _Step _Det
    alpha beta s sigma cell epshom halpha hbeta hs hsSmall hsigma_eq hsigma hcell hepshom
  refine ⟨C1, hC1, fun Cbound hCb => ?_⟩
  obtain ⟨e1, l1, d1, he, hl, hd1, hA⟩ := hR Cbound hCb
  exact ⟨e1, l1, d1, he, hl, hd1, fun eps0 lam0 delta0 a b c e f g =>
    (hA eps0 lam0 delta0 a b c e f g).1⟩

/-- **R2** (all-depth branch): on the full event with the proved budgets as premises,
every sourced native weak solution has a continuous representative, `C^alpha` on `closure q`,
with the `cAlphaNorm` bound at `Ctotal`, and the chosen-cube harmonic comparison (D3 form).
Proved from `aux_in_deterministic_R12_holds`, through `aux_in_deterministic_regularity_R2_of_core`
with `cont`, `camp` and `harm`. -/
theorem aux_in_deterministic_R2_holds
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (_X : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (_Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (_MeyersMorrey : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (_Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (_Det : _root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d)
    (alpha beta s sigma cell epshom : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1)
    (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (hsSmall : s ≤ (1 / 32 : ℝ))
    (hsigma_eq : sigma = (beta - 1 / 2) / 4)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (hcell : cell ∈ Set.Ioo (0 : ℝ) 1)
    (hepshom : 0 < epshom) :
    ∃ C2 : ℝ, 1 ≤ C2 ∧ ∀ Cbound : ℝ, C2 ≤ Cbound →
      ∃ e2 l2 d2 : ℝ, 0 < e2 ∧ 0 < l2 ∧ 0 < d2 ∧
      ∀ eps0 lam0 delta0 : ℝ, 0 < eps0 → eps0 ≤ e2 → 0 < lam0 → lam0 ≤ l2 →
        0 < delta0 → delta0 ≤ d2 →
        aux_in_deterministic_R2 d I alpha beta s sigma cell epshom Cbound eps0 lam0 delta0 := by
  obtain ⟨C1, hC1, hR⟩ := aux_in_deterministic_R12_holds d hd I _X _Sob _MeyersMorrey _Step _Det
    alpha beta s sigma cell epshom halpha hbeta hs hsSmall hsigma_eq hsigma hcell hepshom
  refine ⟨C1, hC1, fun Cbound hCb => ?_⟩
  obtain ⟨e1, l1, d1, he, hl, hd1, hA⟩ := hR Cbound hCb
  exact ⟨e1, l1, d1, he, hl, hd1, fun eps0 lam0 delta0 a b c e f g =>
    (hA eps0 lam0 delta0 a b c e f g).2⟩

/-- The remaining analytic package from the two estimates and the proved R3/R4 slice. -/
theorem aux_in_deterministic_remaining_holds
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (_X : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (_Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (_MeyersMorrey : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (_Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (_Det : _root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d)
    (alpha beta s sigma cell epshom : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1)
    (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (hsSmall : s ≤ (1 / 32 : ℝ))
    (hsigma_eq : sigma = (beta - 1 / 2) / 4)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (hcell : cell ∈ Set.Ioo (0 : ℝ) 1)
    (hepshom : 0 < epshom) :
    aux_in_deterministic_remaining d I alpha beta s sigma cell epshom :=
  aux_in_deterministic_remaining_of_parts d I alpha beta s sigma cell epshom
    (aux_in_deterministic_R1_holds d hd I _X _Sob _MeyersMorrey _Step _Det alpha beta s sigma
      cell epshom halpha hbeta hs hsSmall hsigma_eq hsigma hcell hepshom)
    (aux_in_deterministic_R2_holds d hd I _X _Sob _MeyersMorrey _Step _Det alpha beta s sigma
      cell epshom halpha hbeta hs hsSmall hsigma_eq hsigma hcell hepshom)
    (aux_in_deterministic_R34_holds d hd I _X _Sob alpha beta s sigma cell epshom hbeta
      hsigma_eq hsigma hcell)



theorem in_deterministic
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (_X : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (_Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (_MeyersMorrey : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (_Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (_Det : _root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d)
    (alpha beta s sigma cell epshom : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1)
    (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (hsSmall : s ≤ (1 / 32 : ℝ))
    (hsigma_eq : sigma = (beta - 1 / 2) / 4)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (hcell : cell ∈ Set.Ioo (0 : ℝ) 1)
    (hepshom : 0 < epshom) :
    ∃ Cbound eps0 lam0 delta0 : ℝ,
      1 ≤ Cbound ∧ 0 < eps0 ∧ 0 < lam0 ∧ 0 < delta0 ∧
      ∀ (cbuf k0 : ℕ)
        (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hMH : InfraredCharacterization M H)
        (k : ℕ) (z : SpatialCoordinates d)
        (qside : ℝ) (hqpos : 0 < qside)
        (hqside : qside = (3 : ℝ) ^ (-(k : ℤ)))
        (qcenter : SpatialCoordinates d)
        (hqcenter : qcenter = z)
        (Enl Shift Cmp : Type)
        [Fintype Enl] [Fintype Shift] [Fintype Cmp]
        (selfE : Enl) (selfShift : Shift)
        (qRoot : Enl × Shift)
        (hqRoot : qRoot = (selfE, selfShift))
        (factor : Enl → ℕ)
        (hfactor : factor selfE = 0)
        (padE : Enl) (hpad : factor padE = 1)
        (shift : Shift → SpatialCoordinates d)
        (hshift : shift selfShift = 0)
        (rootLevel : Enl × Shift → ℤ)
        (hrootLevel : ∀ (e : Enl) (t : Shift),
          rootLevel (e, t) = (k : ℤ) - (factor e : ℤ))
        (rootSide : Enl × Shift → ℝ)
        (hrootSide : ∀ (U : Enl × Shift),
          rootSide U = (3 : ℝ) ^ (-rootLevel U))
        (rootCentre : Enl × Shift → SpatialCoordinates d)
        (hrootCentre : ∀ (e : Enl) (t : Shift),
          rootCentre (e, t) = qcenter + rootSide (e, t) • shift t)
        (rootPos : ∀ (U : Enl × Shift), 0 < rootSide U)
        (hGridCover : ∀ (x : SpatialCoordinates d),
          x ∈ Metric.closedBall z (qside / 2) →
          ∀ rho : ℝ, 0 < rho → rho ≤ qside →
            ∃ (U : Enl × Shift) (D : ℕ) (w : Fin D → OddGridIndex d 1),
              Metric.ball x (rho / 2) ⊆
                Metric.ball (descendantCenter 1 (rootCentre U) (rootSide U) D w)
                  (descendantSide 1 D (rootSide U) / 2) ∧
              descendantSide 1 D (rootSide U) ≤ 9 * rho)
        (parent : Cmp → Enl × Shift)
        (depth : Cmp → ℕ)
        (word : (c : Cmp) → Fin (depth c) → OddGridIndex d 1)
        (cmpCentre : Cmp → SpatialCoordinates d)
        (hcmpCentre : ∀ (c : Cmp),
          cmpCentre c =
            descendantCenter 1 (rootCentre (parent c)) (rootSide (parent c))
              (depth c) (word c))
        (cmpLevel : Cmp → ℤ)
        (hcmpLevel : ∀ (c : Cmp),
          cmpLevel c = rootLevel (parent c) + (depth c : ℤ))
        (cmpSide : Cmp → ℝ)
        (hcmpSide : ∀ (c : Cmp), cmpSide c = (3 : ℝ) ^ (-cmpLevel c))
        (cmpPos : ∀ (c : Cmp), 0 < cmpSide c)
        (chosen : Cmp)
        (observationCentre : ∀ (_U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            SpatialCoordinates d)
        (hObservationCentre : ∀ (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          observationCentre U D code =
            Sum.elim
              (fun w => descendantCenter 1 (rootCentre U) (rootSide U) D w)
              (fun V => rootCentre V) code)
        (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : Vec d),
            eta N omega i y =
              omega ((i : ℤ) - (N : ℤ))
                (((3 : ℝ) ^ (-(N : ℤ))) • y))
        (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
        (eps : ℝ) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
        (hepsSmall : eps ≤ eps0)
        (hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ N : ℕ,
            primitive_scores d M s eps (eta N omega)
              (fun m y => F N m y omega)
              (fun m y => Praw N m y omega)
              (fun m y => Rraw N m y omega)
              (fun m y => Draw N m y omega)
              (fun m y => Z N m y omega)
              (fun m y => rawGood N m y omega))
        (lambdaCut lambdaLim lambdaDet cdet : ℝ)
        (hThresholds :
          0 < lambdaCut ∧ lambdaCut < lambdaLim ∧
          lambdaLim < lambdaDet ∧ lambdaDet < 1)
        (hcdet : 0 < cdet) (hcdetSmall : cdet ≤ Cbound⁻¹)
        (hlamSmall : lambdaDet ≤ lam0)
        (hdisorder : M.delta ≤ delta0)
        (prefixZ : ∀ (_N : ℕ) (_U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (prefixD : ∀ (_N : ℕ) (_U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (hPrefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift))
          (omega : BilateralField d),
          prefixZ N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  Z N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega
                else 0
            else 0)
        (hPrefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift))
          (omega : BilateralField d),
          prefixD N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  (Draw N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega).toReal
                else 0
            else 0)
        (hFiniteScoreGuard : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
            (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
            rootLevel U + (D : ℤ) ≤ (N : ℤ) →
            ∀ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
              (rootLevel U + (D : ℤ)),
              Draw N ((N : ℤ) - j).toNat
                (((3 : ℝ) ^ N) • observationCentre U D code) omega ≠ ⊤)
        (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
        (hsN : ∀ (N : ℕ) (l : ℤ) (w : SpatialCoordinates d)
          (omega : BilateralField d),
          sN N l w omega =
            if l ≤ (N : ℤ) then
              (let kappa : ℕ → ℝ := fun J =>
                Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
                  SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
               let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
                 fun ell v beta =>
                   if 0 ≤ ell then
                     ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
                   else
                     -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
               kappa ((N : ℤ) - l).toNat / kappa N *
                 Real.exp (H omega w + retained l w omega))
            else 1)
        (ellLoN ellHiN : ℕ → Enl × Shift → BilateralField d → ℝ)
        (hEllLoN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellLoN N U omega =
            I.lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (hEllHiN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellHiN N U omega =
            I.Lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (AEN : ℕ → Enl × Shift → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (hAEN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          AEN N U omega =
            (sN N (rootLevel U) (rootCentre U) omega)⁻¹ •
              Homogenization.Book.Ch02.sigmaCoarse
                (Homogenization.Book.Ch02.cubeDomain
                  (Homogenization.originCube d 0))
                ((I.chart (rootCentre U) (rootSide U) (rootPos U)
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                    (rootCentre U) (rootPos U))
                  (rootCentre U) (rootSide U)).coeffOn
                  (Homogenization.originCube d 0)))
        (errN ratioN : ℕ → Cmp → BilateralField d → ℝ)
        (hErrN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          errN N c omega =
            I.err (cmpCentre c) (cmpSide c) (cmpPos c)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (cmpCentre c) (cmpPos c))
              (cmpCentre c) (cmpSide c)
              (sN N (cmpLevel c) (cmpCentre c) omega) s 2)
        (hRatioN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          ratioN N c omega =
            sN N (k : ℤ) qcenter omega /
              sN N (cmpLevel c) (cmpCentre c) omega)
        (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
        (hRootsQ : ∀ U : Enl × Shift,
          closure (centeredCube (rootCentre U) (rootSide U) (rootPos U) :
            Set (SpatialCoordinates d)) ⊆
            (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ,
      let Q := centeredCube Qcentre Qside hQside
      let q := centeredCube qcenter qside hqpos
      let qp : Set (SpatialCoordinates d) := Metric.ball qcenter (3 * qside / 2)
      let Ctotal := Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ)))
      let psource : ℝ := (d : ℝ) / (1 - alpha)
      ∀ (N : ℕ), k + k0 ≤ N → (∀ c : Cmp, cmpLevel c ≤ (N : ℤ)) →
        let harmonicComparison (omega : BilateralField d)
            (fNorm : Set (SpatialCoordinates d) → ℝ)
            (U : SpatialCoordinates d → ℝ) : Prop :=
          (let qc := centeredCube (cmpCentre chosen) (cmpSide chosen / 81)
                   (div_pos (cmpPos chosen) (by norm_num))
                 let qi : Set (SpatialCoordinates d) :=
                   Metric.ball (cmpCentre chosen) (cmpSide chosen / 1458)
                 let qo : Set (SpatialCoordinates d) :=
                   Metric.ball (cmpCentre chosen) (cmpSide chosen / 18)
                 ∀ w : SpatialCoordinates d,
                 let qd : Set (SpatialCoordinates d) :=
                   Metric.ball w (27 * cmpSide chosen / 2)
                 Metric.closedBall (cmpCentre chosen) (cmpSide chosen / 18) ⊆ qd →
                 qd ⊆ (Q : Set (SpatialCoordinates d)) →
                 ∃ (v : weakSobolevGraph qc) (V : SpatialCoordinates d → ℝ),
                   ContinuousOn V (closure (qc : Set (SpatialCoordinates d))) ∧
                   (((v : SobolevData qc).1 : SpatialCoordinates d → ℝ) =ᵐ[
                     volume.restrict (qc : Set (SpatialCoordinates d))] V) ∧
                   (∀ x ∈ frontier (qc : Set (SpatialCoordinates d)), V x = U x) ∧
                   (∀ psi : killedSobolevGraph qc,
                     inner ℝ (sobolevGradient (v : SobolevData qc))
                       (subspaceGradient (killedSobolevGraph qc) psi) = 0) ∧
                   normalizedL2On qi (fun x => U x - V x) ≤
                     epshom * normalizedL2On qo
                       (fun x => U x - (volume.real qo)⁻¹ * ∫ y in qo, U y) +
                     Ctotal * (cmpSide chosen / 9) ^ 2 *
                       (sN N (cmpLevel chosen) (cmpCentre chosen) omega)⁻¹ * fNorm qd)
        let traceEstimate (omega : BilateralField d) : Prop :=
          (∃ Uq : ℝ,
            Uq = I.Lam qcenter qside hqpos
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N qcenter hqpos)
              qcenter qside sigma 2 ∧
            Cbound⁻¹ * sN N (k : ℤ) qcenter omega ≤ Uq ∧
            Uq ≤ Cbound * sN N (k : ℤ) qcenter omega ∧
            ∀ b : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta qcenter qside b →
              ∃ (extension : weakSobolevGraph q) (B : SpatialCoordinates d → ℝ),
                ContinuousOn B (closure (q : Set (SpatialCoordinates d))) ∧
                (((extension : SobolevData q).1 : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (q : Set (SpatialCoordinates d))] B) ∧
                (∀ x ∈ frontier (q : Set (SpatialCoordinates d)), B x = b x) ∧
                ∀ (Sq : ResponseSpace q), Sq.space = killedSobolevGraph q →
                  dirichletResponse Sq
                    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N qcenter hqpos)
                    extension ≤
                    Cbound * Uq * qside ^ ((d : ℝ) - 2) *
                      cellBoundaryQuotientNorm beta qcenter qside b ^ 2)
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          (∀ horizon : ℕ,
          ((∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D → D ≤ horizon →
              rootLevel U + (D : ℤ) ≤ (N : ℤ) →
              ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
                prefixZ N U D code omega < lambdaCut * (D : ℝ) ∧
                prefixD N U D code omega < lambdaCut * (D : ℝ)) ∧
           (∀ U : Enl × Shift,
              cell ≤ ellLoN N U omega ∧ ellHiN N U omega ≤ cell⁻¹) ∧
           errN N chosen omega ≤ epshom * cdet ∧
           (∀ c : Cmp, ratioN N c omega ∈ Set.Icc (1 / 2 : ℝ) 2)) →
          (∀ (f : SpatialCoordinates d → ℝ),
            MemLp f (ENNReal.ofReal psource) (volume.restrict (Q : Set (SpatialCoordinates d))) →
            ∀ (fL2 : DomainL2 Q),
              ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                (Q : Set (SpatialCoordinates d))] f) →
            let fNorm : Set (SpatialCoordinates d) → ℝ := fun W =>
              (eLpNorm f (ENNReal.ofReal psource) (volume.restrict W)).toReal /
                (volume.real W) ^ (1 / psource)
            ∀ u : weakSobolevGraph Q,
              (∀ psi : killedSobolevGraph Q,
                sobolevCoefficientForm
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
                  (u : SobolevData Q) (psi : SobolevData Q) =
                sobolevVolumeLoad fL2 (psi : SobolevData Q)) →
              ∃ U : SpatialCoordinates d → ℝ,
                ContinuousOn U (Q : Set (SpatialCoordinates d)) ∧
                (((u : SobolevData Q).1 : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
                (∀ (D : ℕ), D ≤ horizon →
                  ∀ x ∈ (q : Set (SpatialCoordinates d)),
                    let B : Set (SpatialCoordinates d) :=
                      Metric.ball x (qside * (3 : ℝ) ^ (-(D : ℤ)) / 2) ∩
                        (q : Set (SpatialCoordinates d))
                    normalizedL2On B
                      (fun y => U y - (volume.real B)⁻¹ * ∫ t in B, U t) ≤
                      Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ))) *
                        (3 : ℝ) ^ (Cbound * (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)) *
                        (3 : ℝ) ^ (-(D : ℝ)) *
                        (normalizedL2On qp
                          (fun y => U y - (volume.real qp)⁻¹ * ∫ t in qp, U t) +
                          qside ^ 2 * (sN N (k : ℤ) qcenter omega)⁻¹ * fNorm qp)) ∧
                harmonicComparison omega fNorm U) ∧
          (∀ (Uroot : Enl × Shift) (x : Fin d → ℝ),
            Cbound⁻¹ * Matrix.trace (AEN N Uroot omega) * (x ⬝ᵥ x) ≤
              x ⬝ᵥ (AEN N Uroot omega).mulVec x) ∧
          traceEstimate omega) ∧
          (          ((∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D →
              rootLevel U + (D : ℤ) ≤ (N : ℤ) →
              ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
                prefixZ N U D code omega < lambdaCut * (D : ℝ) ∧
                prefixD N U D code omega < lambdaCut * (D : ℝ)) ∧
           (∀ U : Enl × Shift,
              cell ≤ ellLoN N U omega ∧ ellHiN N U omega ≤ cell⁻¹) ∧
           errN N chosen omega ≤ epshom * cdet ∧
           (∀ c : Cmp, ratioN N c omega ∈ Set.Icc (1 / 2 : ℝ) 2)) →
          (∀ (Uroot : Enl × Shift) (D : ℕ),
            rootLevel Uroot + (D : ℤ) ≤ (N : ℤ) →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              ((Finset.filter
                (fun j : ℤ => j < rootLevel Uroot + (k0 : ℤ) ∨
                  1 ≤ Z N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre Uroot D code) omega)
                (Finset.Icc (rootLevel Uroot - (cbuf : ℤ))
                  (rootLevel Uroot + (D : ℤ)))).card : ℝ) ≤
                (k0 : ℝ) + (cbuf : ℝ) + lambdaDet * (D : ℝ)) ∧
          (∀ (Uroot : Enl × Shift) (D : ℕ),
            rootLevel Uroot + (D : ℤ) ≤ (N : ℤ) →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              (∑ j ∈ Finset.Icc (rootLevel Uroot - (cbuf : ℤ))
                (rootLevel Uroot + (D : ℤ)),
                if rootLevel Uroot + (k0 : ℤ) ≤ j ∧
                    Z N ((N : ℤ) - j).toNat
                      (((3 : ℝ) ^ N) • observationCentre Uroot D code) omega < 1 then
                  let w := observationCentre Uroot D code
                  let rj := (3 : ℝ) ^ (-j)
                  I.err w rj (by positivity)
                    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
                    w rj (sN N j w omega) s 2
                else 0) ≤
                  Cbound * (M.delta ^ 2 + eps ^ 8 + lambdaDet) * (D : ℝ) +
                    Cbound * ((k0 : ℝ) + (cbuf : ℝ))) ∧
          Cbound * (lambdaDet + M.delta ^ 2 + eps ^ 8) < 1 - alpha ∧
          (∃ D0 : ℕ, k0 ≤ D0 ∧ ∀ D : ℕ, D0 ≤ D →
            (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ))) *
              (3 : ℝ) ^ (Cbound * (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)) ≤
                (3 : ℝ) ^ ((1 - alpha) * (D : ℝ))) ∧
          (∀ (f : SpatialCoordinates d → ℝ),
            MemLp f (ENNReal.ofReal psource) (volume.restrict (Q : Set (SpatialCoordinates d))) →
            ∀ (fL2 : DomainL2 Q),
              ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                (Q : Set (SpatialCoordinates d))] f) →
            let fNorm : Set (SpatialCoordinates d) → ℝ := fun W =>
              (eLpNorm f (ENNReal.ofReal psource) (volume.restrict W)).toReal /
                (volume.real W) ^ (1 / psource)
            ∀ u : weakSobolevGraph Q,
              (∀ psi : killedSobolevGraph Q,
                sobolevCoefficientForm
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
                  (u : SobolevData Q) (psi : SobolevData Q) =
                sobolevVolumeLoad fL2 (psi : SobolevData Q)) →
              ∃ U : SpatialCoordinates d → ℝ,
                ContinuousOn U (Q : Set (SpatialCoordinates d)) ∧
                (((u : SobolevData Q).1 : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
                _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (closure (q : Set (SpatialCoordinates d))) U ∧
                (∃ cq : ℝ,
                  _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
                    (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
                    (fun x => U (qcenter + qside • x) - cq) ≤
                      Ctotal * (normalizedL2On qp
                        (fun x => U x - (volume.real qp)⁻¹ * ∫ y in qp, U y) +
                        qside ^ 2 * (sN N (k : ℤ) qcenter omega)⁻¹ * fNorm qp)) ∧
                harmonicComparison omega fNorm U) ∧
          (∀ (Uroot : Enl × Shift) (x : Fin d → ℝ),
            Cbound⁻¹ * Matrix.trace (AEN N Uroot omega) * (x ⬝ᵥ x) ≤
              x ⬝ᵥ (AEN N Uroot omega).mulVec x) ∧
          traceEstimate omega)
  := by
  exact aux_in_deterministic_exists d I alpha beta s sigma cell epshom halpha hs hsSmall
    (aux_in_deterministic_remaining_holds d hd I _X _Sob _MeyersMorrey _Step _Det alpha beta s
      sigma cell epshom halpha hbeta hs hsSmall hsigma_eq hsigma hcell hepshom)

end SubdiffusiveProcess.Paper
