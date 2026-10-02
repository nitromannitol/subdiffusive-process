import SubdiffusiveProcess.Paper.candidate_good_estimates_trace_finish
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.EstimateLimits
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.OneStepDatum
import SubdiffusiveProcess.Paper.killed_continuous_boundary_zero
import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Lane2.BoundaryResponse
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Paper.cutoff_good_scale_input
import SubdiffusiveProcess.Paper.candidate_good_event
import SubdiffusiveProcess.Paper.prop_killed_inverse
import SubdiffusiveProcess.Paper.prop_21
import SubdiffusiveProcess.Paper.cor_energy_measures
import SubdiffusiveProcess.Paper.candidate_good_estimates_trace_passage
import SubdiffusiveProcess.Paper.lem_extension
import SubdiffusiveProcess.Paper.in_deterministic
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.prop_growth
import SubdiffusiveProcess.Paper.prop_growth_large_root
import SubdiffusiveProcess.Paper.lem_primitive
import SubdiffusiveProcess.Paper.primitive_scores
import SubdiffusiveProcess.Lane3.Subdivision
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Sobolev.WeakGraphMaxPrinciple
import Homogenization.Book.Ch02.Matrices
import Homogenization.Book.Ch02.MultiscaleEllipticity
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import SubdiffusiveProcess.Paper.lem_prefix_limit
import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input

import SubdiffusiveProcess.Paper.candidate_good_estimates_finite_bank_support
import SubdiffusiveProcess.Paper.candidate_good_estimates_trace_support
import SubdiffusiveProcess.Paper.candidate_good_estimates_constants_support
import SubdiffusiveProcess.Paper.candidate_source_compact_bank
import SubdiffusiveProcess.Paper.candidate_represented_source_bank
import SubdiffusiveProcess.Sobolev.HarmonicWindowNorms

/-! This module proves the candidate good-estimates trace supplier. -/

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

universe uCge

/-- Finite candidate bounds yield the source representative and its Hölder trace estimate. -/
theorem candidate_good_estimates_trace_supplier
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (_X : Paper.in_extension d hd I)
    (_Sob : Lane4.SobolevFoundationalInput d hd)
    (_Poincare : Paper.in_poincare d hd I)
    (_MeyersMorrey : Lane4.SmallPerturbationInput d)
    (_Step : Paper.cutoff_good_scale_input d)
    (D : Paper.lane4_deterministic_good_scale_input d)
    (Cp : Lane4.CampanatoInput d)
    (alpha beta s sigma cell : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1)
    (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (hsSmall : s ≤ (1 / 32 : ℝ))
    (hsigma_eq : sigma = (beta - 1 / 2) / 4)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (hcell : cell ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ Cbound : ℝ, 1 ≤ Cbound ∧ Cbound⁻¹ ≤ cell ∧ cell⁻¹ ≤ Cbound ∧
      (d : ℝ) ≤ Cbound * cell ^ 2 ∧
    ∀ (epshom : ℝ) (hepshom : 0 < epshom), epshom ≤ 1 →
    ∃ eps0 lam0 delta0 : ℝ,
      0 < eps0 ∧ 0 < lam0 ∧ 0 < delta0 ∧
      ∀ (cbuf k0 : ℕ)
        (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (_Rm : Paper.in_responses d M) (Sreg : Paper.in_6_16 d M)
        (_It : Paper.in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hMH : InfraredCharacterization M H)
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (field : Ω → BilateralField d)
        (hfieldMeas : Measurable field)
        (hfieldLaw : Measure.map field P = (chaosSampleLaw M).toMeasure)
        (env : PUnit.{uCge} → ℕ → Ω → BilateralField d)
        (hEnvMeas : ∀ (a : PUnit.{uCge}) (n : ℕ), Measurable (env a n))
        (hEnvLaw : ∀ (a : PUnit.{uCge}) (n : ℕ),
          Measure.map (env a n) P = (chaosSampleLaw M).toMeasure)
        (hEnvConv : ∀ᵐ omega ∂P, ∀ a : PUnit.{uCge},
          Tendsto (fun n => env a n omega) atTop (𝓝 (field omega)))
        (k : ℕ) (z : SpatialCoordinates d)
        (qside : ℝ)
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
        (hGridCover : ∀ (x : SpatialCoordinates d), x ∈ Metric.closedBall z (qside / 2) →
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
        (observationCentre :
          ∀ (U : Enl × Shift) (D : ℕ),
            ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
              SpatialCoordinates d)
        (hObservationCentre : ∀ (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          observationCentre U D code =
            Sum.elim
              (fun w => descendantCenter 1 (rootCentre U) (rootSide U) D w)
              (fun V => rootCentre V) code)
        (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
        (hEta : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : Vec d),
            eta N omega i y =
              omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y)))
        (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
        (eps : ℝ) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
        (hepsSmall : eps ≤ eps0)
        (hPrimitive : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ N : ℕ,
            primitive_scores d M s eps (eta N omega)
              (fun m y => F N m y omega)
              (fun m y => Praw N m y omega)
              (fun m y => Rraw N m y omega)
              (fun m y => Draw N m y omega)
              (fun m y => Z N m y omega)
              (fun m y => rawGood N m y omega)))
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
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) (omega : BilateralField d),
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
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) (omega : BilateralField d),
          prefixD N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  (Draw N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega).toReal
                else 0
            else 0)
        (hFiniteScoreGuard : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
            (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
            rootLevel U + (D : ℤ) ≤ (N : ℤ) →
            ∀ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
              (rootLevel U + (D : ℤ)),
              Draw N ((N : ℤ) - j).toNat
                (((3 : ℝ) ^ N) • observationCentre U D code) omega ≠ ⊤))
        (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
        (hsN : ∀ (N : ℕ) (l : ℤ) (w : SpatialCoordinates d)
          (omega : BilateralField d),
          sN N l w omega =
            if l ≤ (N : ℤ) then
              (let kappa : ℕ → ℝ := fun J =>
                Real.exp (((J : ℝ) + 1) *
                  SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
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
              (SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (hEllHiN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellHiN N U omega =
            I.Lam (rootCentre U) (rootSide U) (rootPos U)
              (SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M H omega N
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
                  (SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M H omega N
                    (rootCentre U) (rootPos U))
                  (rootCentre U) (rootSide U)).coeffOn
                  (Homogenization.originCube d 0)))
        (errN ratioN : ℕ → Cmp → BilateralField d → ℝ)
        (hErrN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          errN N c omega =
            I.err (cmpCentre c) (cmpSide c) (cmpPos c)
              (SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M H omega N
                (cmpCentre c) (cmpPos c))
              (cmpCentre c) (cmpSide c)
              (sN N (cmpLevel c) (cmpCentre c) omega) s 2)
        (hRatioN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          ratioN N c omega =
            sN N (k : ℤ) qcenter omega /
              sN N (cmpLevel c) (cmpCentre c) omega)
        (phi : ℕ → ℕ)
        (hphi : StrictMono phi)
        (prefixZLim : ∀ (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) → Ω → ℝ)
        (prefixDLim : ∀ (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) → Ω → ℝ)
        (ellLoLim ellHiLim : (Enl × Shift) → Ω → ℝ)
        (AE_Lim : (Enl × Shift) → Ω → Matrix (Fin d) (Fin d) ℝ)
        (errLim ratioLim : Cmp → Ω → ℝ)
        (hPrefixZLim : ∀ (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          TendstoInMeasure P
            (fun n omega => prefixZ (phi n) U D code (env PUnit.unit n omega)) atTop
            (prefixZLim U D code))
        (hPrefixDLim : ∀ (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          TendstoInMeasure P
            (fun n omega => prefixD (phi n) U D code (env PUnit.unit n omega)) atTop
            (prefixDLim U D code))
        (hEllLoLim : ∀ (U : Enl × Shift),
          TendstoInMeasure P
            (fun n omega => ellLoN (phi n) U (env PUnit.unit n omega)) atTop (ellLoLim U))
        (hEllHiLim : ∀ (U : Enl × Shift),
          TendstoInMeasure P
            (fun n omega => ellHiN (phi n) U (env PUnit.unit n omega)) atTop (ellHiLim U))
        (hAELim : ∀ (U : Enl × Shift) (i j : Fin d),
          TendstoInMeasure P
            (fun n omega => AEN (phi n) U (env PUnit.unit n omega) i j) atTop
            (fun omega => AE_Lim U omega i j))
        (hErrLim : ∀ (c : Cmp),
          TendstoInMeasure P
            (fun n omega => errN (phi n) c (env PUnit.unit n omega)) atTop (errLim c))
        (hRatioLim : ∀ (c : Cmp),
          TendstoInMeasure P
            (fun n omega => ratioN (phi n) c (env PUnit.unit n omega)) atTop (ratioLim c))
        (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
        (hRootsQ : ∀ U : Enl × Shift,
          closure (centeredCube (rootCentre U) (rootSide U) (rootPos U) :
            Set (SpatialCoordinates d)) ⊆
            (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
        (S : ResponseSpace (centeredCube Qcentre Qside hQside))
        (hS : S.space = killedSobolevGraph (centeredCube Qcentre Qside hQside))
        (GN : ℕ → BilateralField d →
          DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
            DomainL2 (centeredCube Qcentre Qside hQside))
        (hGN : ∀ N omega f, GN N omega f =
          (responseSolution S
            (Lane4.cutoffPositiveCoefficient M H omega N Qcentre hQside)
            ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
        (GE : Ω → DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
          DomainL2 (centeredCube Qcentre Qside hQside))
        (hGE : (∀ᵐ omega ∂P,
          Tendsto (fun n => GN (phi n) (env PUnit.unit n omega)) atTop (𝓝 (GE omega))))
        (E : Ω → DirichletForm.ClosedForm
          (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
        (hE : ∀ omega u, (E omega).energy u = limitFormEnergy (GE omega) u)
        (GammaE : ∀ omega : Ω, DirichletForm.EnergyMeasure (E omega))
        (sE : Ω → ℝ) (sCmp : Cmp → Ω → ℝ)
        (hsE : (∀ᵐ omega ∂P,
          0 < sE omega ∧
          Tendsto (fun n => sN (phi n) (k : ℤ) z (env PUnit.unit n omega)) atTop
            (𝓝 (sE omega))))
        (hsCmp : (∀ᵐ omega ∂P, ∀ c : Cmp,
          0 < sCmp c omega ∧
          Tendsto (fun n => sN (phi n) (cmpLevel c) (cmpCentre c) (env PUnit.unit n omega))
            atTop (𝓝 (sCmp c omega)))),
    let Q := centeredCube Qcentre Qside hQside
    let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
    let q : Set (SpatialCoordinates d) := Metric.ball z (r / 2)
    let p : Set (SpatialCoordinates d) := Metric.ball z (3 * r / 2)
    let Ctotal := Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ)))
    let Good : Set Ω :=
      {omega |
        (∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D →
          ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
            prefixZLim U D code omega < lambdaLim * (D : ℝ) ∧
            prefixDLim U D code omega < lambdaLim * (D : ℝ)) ∧
        (∀ U : Enl × Shift,
          cell ≤ ellLoLim U omega ∧ ellHiLim U omega ≤ cell⁻¹) ∧
        errLim chosen omega ≤ epshom * cdet ∧
        (∀ c : Cmp, ratioLim c omega ∈ Set.Ioo (1 / 2 : ℝ) 2)}
    ∀ᵐ omega ∂P, omega ∈ Good →
      (∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
        ∀ (fL2 : DomainL2 Q),
          ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (Q : Set (SpatialCoordinates d))] f) →
        let u := GE omega fL2
        let fsup := sSup {v : ℝ | ∃ x ∈ closure (Q : Set (SpatialCoordinates d)), v = |f x|}
        ∃ U : SpatialCoordinates d → ℝ,
          ContinuousOn U (closure (Q : Set (SpatialCoordinates d))) ∧
          ((u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (Q : Set (SpatialCoordinates d))] U) ∧
          (∀ x ∈ frontier (Q : Set (SpatialCoordinates d)), U x = 0) ∧
          Lane4.IsHolderOn alpha (closure q) U ∧
          (∃ cq : ℝ,
            Lane4.cAlphaNorm alpha
              (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
              (fun x => U (z + r • x) - cq) ≤
                Ctotal * (normalizedL2On p
                  (fun x => U x - (volume.real p)⁻¹ * ∫ y in p, U y) +
                  r ^ 2 * (sE omega)⁻¹ * fsup))) := by
  let cellDet : ℝ := cell / 2
  have hcellDet : cellDet ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · dsimp [cellDet]
      linarith only [hcell.1]
    · dsimp [cellDet]
      linarith only [hcell.2]
  obtain ⟨Cg, deltaGS, hCg, hdeltaGS, hGST⟩ :=
    in_deterministic_good_scale_transfer d I s hs hsSmall
  obtain ⟨Cbound, Ccamp, hCbound, hCgC, hCloDet, hChiDet, hCdimDet, hCcamp0, hCcampB,
      hCcampHolder, hConstants⟩ :=
    candidate_good_estimates_constants_support d hd I D Cg hCg alpha beta s sigma
      cellDet halpha hs hsSmall hcellDet
  have hClo : Cbound⁻¹ ≤ cell := by
    exact hCloDet.trans (by dsimp [cellDet]; linarith only [hcell.1])
  have hChi : cell⁻¹ ≤ Cbound := by
    have hdetle : cellDet ≤ cell := by dsimp [cellDet]; linarith only [hcell.1]
    calc
      cell⁻¹ ≤ cellDet⁻¹ := by
        simpa only [one_div] using (one_div_le_one_div_of_le hcellDet.1 hdetle)
      _ ≤ Cbound := hChiDet
  have hCbound0 : 0 ≤ Cbound := by linarith only [hCbound]
  have hCdim : (d : ℝ) ≤ Cbound * cell ^ 2 := by
    have hsq : cellDet ^ 2 ≤ cell ^ 2 := by
      dsimp [cellDet]
      nlinarith only [hcell.1]
    calc
      (d : ℝ) ≤ Cbound * cellDet ^ 2 := hCdimDet
      _ ≤ Cbound * cell ^ 2 := mul_le_mul_of_nonneg_left hsq hCbound0
  have hbeta01 : beta ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hbeta.1], hbeta.2⟩
  obtain ⟨deltaGrowth, hdeltaGrowth, hGrowthSupplier⟩ :=
    candidate_good_estimates_trace_support d hd I _Poincare _X
      _MeyersMorrey Cp _Sob beta hbeta01
  refine ⟨Cbound, hCbound, hClo, hChi, hCdim, ?_⟩
  intro epshom hepshom hepshom_le
  obtain ⟨epsCap, lamCap, deltaCap, hepsCap, hlamCap, hdeltaCap, hCaps⟩ :=
    hConstants epshom hepshom hepshom_le
  have hDen : 0 < Cbound := lt_of_lt_of_le zero_lt_one hCbound
  have hNum : 0 < 1 - alpha := by linarith only [halpha.2]
  let T : ℝ := (1 - alpha) / (4 * Cbound)
  have hTpos : 0 < T := by dsimp [T]; exact div_pos hNum (by positivity)
  have hTsqrt : 0 < Real.sqrt T := Real.sqrt_pos.2 hTpos
  let eps0 : ℝ := min epsCap (min 1 T)
  let lam0 : ℝ := min lamCap T
  let deltaDet : ℝ := min deltaCap (Real.sqrt T)
  let delta0 : ℝ := min deltaDet (min deltaGrowth deltaGS)
  have heps0 : 0 < eps0 := lt_min hepsCap (lt_min one_pos hTpos)
  have hlam0 : 0 < lam0 := lt_min hlamCap hTpos
  have hdeltaDet : 0 < deltaDet := lt_min hdeltaCap hTsqrt
  have hdelta0 : 0 < delta0 := lt_min hdeltaDet (lt_min hdeltaGrowth hdeltaGS)
  refine ⟨eps0, lam0, delta0, heps0, hlam0, hdelta0, ?_⟩
  intro cbuf k0 M _Rm Sreg _It H hMH Ω _instΩ P _instP field hfieldMeas hfieldLaw
    env hEnvMeas hEnvLaw hEnvConv k z qside hqside qcenter hqcenter Enl Shift Cmp
    _instEnl _instShift _instCmp selfE selfShift qRoot hqRoot factor hfactor padE hpad
    shift hshift rootLevel hrootLevel rootSide hrootSide rootCentre hrootCentre rootPos
    hGridCover parent depth word cmpCentre hcmpCentre cmpLevel hcmpLevel cmpSide hcmpSide
    cmpPos chosen observationCentre hObservationCentre eta hEta F Praw Rraw Draw Z rawGood
    eps heps hepsSmall hPrimitive lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet
    hcdetSmall hlamSmall hdisorder prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard sN hsN
    ellLoN ellHiN hEllLoN hEllHiN AEN hAEN errN ratioN hErrN hRatioN phi hphi prefixZLim
    prefixDLim ellLoLim ellHiLim AE_Lim errLim ratioLim hPrefixZLim hPrefixDLim hEllLoLim
    hEllHiLim hAELim hErrLim hRatioLim Qcentre Qside hQside hRootsQ S hS GN hGN GE hGE E hE
    GammaE sE sCmp hsE hsCmp
  have hEpsCap : eps ≤ epsCap := by
    exact hepsSmall.trans (by dsimp [eps0]; exact min_le_left _ _)
  have hLamPos : 0 < lambdaDet := hThresholds.1.trans
    (hThresholds.2.1.trans hThresholds.2.2.1)
  have hLamCap : lambdaDet ≤ lamCap := hlamSmall.trans (by dsimp [lam0]; exact min_le_left _ _)
  have hDeltaPos : 0 < M.delta := M.shellPrefix.delta_pos
  have hDeltaCap : M.delta ≤ deltaCap := hdisorder.trans
    (by dsimp [delta0, deltaDet]; exact (min_le_left _ _).trans (min_le_left _ _))
  have hEps0Cap : eps0 ≤ epsCap := by
    dsimp [eps0]
    exact min_le_left _ _
  have hLam0Cap : lam0 ≤ lamCap := by
    dsimp [lam0]
    exact min_le_left _ _
  have hDelta0Cap : delta0 ≤ deltaCap := by
    dsimp [delta0, deltaDet]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hdetCaps := hCaps eps0 lam0 delta0 heps0 hEps0Cap hlam0 hLam0Cap
    hdelta0 hDelta0Cap
  have hqpos : 0 < qside := by rw [hqside]; positivity
  let lambdaA : ℝ := (lambdaLim + lambdaDet) / 2
  let lambdaB : ℝ := (lambdaA + lambdaDet) / 2
  have hThresholdsAux : 0 < lambdaA ∧ lambdaA < lambdaB ∧
      lambdaB < lambdaDet ∧ lambdaDet < 1 := by
    constructor
    · dsimp [lambdaA]
      linarith only [hThresholds.1, hThresholds.2.1, hThresholds.2.2.1]
    constructor
    · dsimp [lambdaA, lambdaB]
      linarith only [hThresholds.2.1, hThresholds.2.2.1]
    constructor
    · dsimp [lambdaA, lambdaB]
      linarith only [hThresholds.2.2.1]
    · exact hThresholds.2.2.2
  have hCampSupplier := hdetCaps.2.2 cbuf k0 M H hMH k z qside hqpos hqside qcenter hqcenter
      Enl Shift Cmp selfE selfShift qRoot hqRoot factor hfactor padE hpad shift hshift
      rootLevel hrootLevel rootSide hrootSide rootCentre hrootCentre rootPos hGridCover
      parent depth word cmpCentre hcmpCentre cmpLevel hcmpLevel cmpSide hcmpSide cmpPos
      chosen observationCentre hObservationCentre eta hEta F Praw Rraw Draw Z rawGood
      eps heps hepsSmall hPrimitive lambdaA lambdaB lambdaDet cdet hThresholdsAux hcdet
      hcdetSmall hlamSmall hdisorder prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard
      sN hsN ellLoN ellHiN hEllLoN hEllHiN AEN hAEN errN ratioN hErrN hRatioN
      Qcentre Qside hQside hRootsQ
  let Q := centeredCube Qcentre Qside hQside
  let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
  let q : Set (SpatialCoordinates d) := Metric.ball z (r / 2)
  let p : Set (SpatialCoordinates d) := Metric.ball z (3 * r / 2)
  let Ctotal := Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ)))
  let Good : Set Ω :=
    {omega |
      (∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D →
        ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
          prefixZLim U D code omega < lambdaLim * (D : ℝ) ∧
          prefixDLim U D code omega < lambdaLim * (D : ℝ)) ∧
      (∀ U : Enl × Shift,
        cell ≤ ellLoLim U omega ∧ ellHiLim U omega ≤ cell⁻¹) ∧
      errLim chosen omega ≤ epshom * cdet ∧
      (∀ c : Cmp, ratioLim c omega ∈ Set.Ioo (1 / 2 : ℝ) 2)}
  dsimp only
  have hGoodLimit : ∀ᵐ omega ∂P, omega ∈ Good →
      (∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D →
        ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
          prefixZLim U D code omega < lambdaA * (D : ℝ) ∧
          prefixDLim U D code omega < lambdaA * (D : ℝ)) ∧
      (∀ U : Enl × Shift,
        cell ≤ ellLoLim U omega ∧ ellHiLim U omega ≤ cell⁻¹) ∧
      errLim chosen omega ≤ epshom * cdet ∧
      (∀ c : Cmp, ratioLim c omega ∈ Set.Ioo (1 / 2 : ℝ) 2) := by
    filter_upwards with omega
    intro hg
    rcases hg with ⟨hprefix, hcellGood, herr, hratio⟩
    refine ⟨?_, ?_, herr, hratio⟩
    · intro U D hD code
      have hLambda : lambdaLim ≤ lambdaA := by
        dsimp [lambdaA]
        linarith only [hThresholds.2.1, hThresholds.2.2.1]
      have hmul : lambdaLim * (D : ℝ) ≤ lambdaA * (D : ℝ) :=
        mul_le_mul_of_nonneg_right hLambda (Nat.cast_nonneg D)
      exact ⟨(hprefix U D hD code).1.trans_le hmul,
        (hprefix U D hD code).2.trans_le hmul⟩
    · exact hcellGood
  let prefixZSeq : ℕ → (U : Enl × Shift) → (D : ℕ) →
      (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift) → Ω → ℝ := fun n U D code omega =>
    prefixZ (phi n) U D code (env PUnit.unit n omega)
  let prefixDSeq : ℕ → (U : Enl × Shift) → (D : ℕ) →
      (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift) → Ω → ℝ := fun n U D code omega =>
    prefixD (phi n) U D code (env PUnit.unit n omega)
  let lowN : (Enl × Shift) → ℕ → Ω → ℝ := fun U n omega =>
    ellLoN (phi n) U (env PUnit.unit n omega)
  let highN : (Enl × Shift) → ℕ → Ω → ℝ := fun U n omega =>
    ellHiN (phi n) U (env PUnit.unit n omega)
  let errorN : ℕ → Ω → ℝ := fun n omega => errN (phi n) chosen (env PUnit.unit n omega)
  let ratioSeq : Cmp → ℕ → Ω → ℝ := fun c n omega =>
    ratioN (phi n) c (env PUnit.unit n omega)
  let FinEvent : ℕ → ℕ → Ω → Prop := fun horizon n omega =>
    (∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D → D ≤ horizon →
      ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
        prefixZSeq n U D code omega < lambdaA * (D : ℝ) ∧
        prefixDSeq n U D code omega < lambdaA * (D : ℝ)) ∧
    (∀ U : Enl × Shift,
      cell / 2 < lowN U n omega ∧ highN U n omega < 2 * cell⁻¹) ∧
    errorN n omega < 2 * epshom * cdet ∧
    (∀ c : Cmp, ratioSeq c n omega ∈ Set.Ioo (1 / 2 : ℝ) 2)
  have hFiniteHorizon : ∀ horizon : ℕ,
      ∃ ns : ℕ → ℕ, StrictMono ns ∧
        ∀ᵐ omega ∂P, omega ∈ Good → ∀ᶠ n in atTop, FinEvent horizon (ns n) omega := by
    intro horizon
    exact candidate_good_estimates_finite_bank_support P horizon k0
      prefixZSeq prefixDSeq prefixZLim prefixDLim lowN highN ellLoLim ellHiLim
      errorN (errLim chosen) ratioSeq ratioLim
      (by intro U D code; simpa only [prefixZSeq] using hPrefixZLim U D code)
      (by intro U D code; simpa only [prefixDSeq] using hPrefixDLim U D code)
      (by intro U; simpa only [lowN] using hEllLoLim U)
      (by intro U; simpa only [highN] using hEllHiLim U)
      (by simpa only [errorN] using hErrLim chosen)
      (by intro c; simpa only [ratioSeq] using hRatioLim c)
      cell epshom cdet lambdaA hcell.1 hepshom hcdet (fun omega => omega ∈ Good) hGoodLimit
  obtain ⟨nu, hnu, hFiniteAll⟩ :=
    aux_candidate_good_estimates_finite_bank_support_diagonal_horizons P (fun omega => omega ∈ Good) FinEvent
      (by intro horizon; exact hFiniteHorizon horizon)
  have hdelta0Growth : delta0 ≤ deltaGrowth := by
    dsimp [delta0]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hdelta0GS : delta0 ≤ deltaGS := by
    dsimp [delta0, deltaDet]
    exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨K, Cgrowth, hCgrowth, hKMem, hKNorm, hKge, hKsource⟩ :=
    hGrowthSupplier M _Rm Sreg _It H hMH (hdisorder.trans hdelta0Growth)
      Qcentre Qside hQside
  have hTransfer : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N : ℕ) (j : ℤ) (w : SpatialCoordinates d), j ≤ (N : ℤ) →
        Draw N ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) omega ≠ ⊤ →
        Z N ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) omega < 1 →
        I.err w ((3 : ℝ) ^ (-j)) (by positivity)
          (SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M H omega N w (by positivity))
          w ((3 : ℝ) ^ (-j)) (sN N j w omega) s 2 ≤
          Cg * (M.delta ^ 2 + eps ^ 8 +
          (Draw N ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) omega).toReal) := by
    exact hGST M H hMH (hdisorder.trans hdelta0GS) eps heps eta F Praw Rraw Draw Z rawGood
      hEta hPrimitive sN hsN
  have hZnonneg : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N m : ℕ) (y : Vec d), 0 ≤ Z N m y omega := by
    filter_upwards [hPrimitive] with omega hP
    intro N m y
    obtain ⟨_, _, _, _, _, _, _, _, _, hZdef, _⟩ := hP N
    exact (hZdef m y).2.1
  let Budget : ℕ → ℕ → BilateralField d → Prop := fun horizon N omega =>
    (∀ (Uroot : Enl × Shift) (D : ℕ), D ≤ horizon →
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
              (SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M H omega N w (by positivity))
              w rj (sN N j w omega) s 2
          else 0) ≤
          Cbound * (M.delta ^ 2 + eps ^ 8 + lambdaDet) * (D : ℝ) +
            Cbound * ((k0 : ℝ) + (cbuf : ℝ)))
  have hBudgetAll : ∀ᵐ omega ∂P, ∀ horizon n : ℕ,
      k + k0 ≤ phi (nu horizon n) →
      (∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D → D ≤ horizon →
        ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
          prefixZ (phi (nu horizon n)) U D code (env PUnit.unit (nu horizon n) omega) <
              lambdaA * (D : ℝ) ∧
          prefixD (phi (nu horizon n)) U D code (env PUnit.unit (nu horizon n) omega) <
              lambdaA * (D : ℝ)) →
      Budget horizon (phi (nu horizon n)) (env PUnit.unit (nu horizon n) omega) := by
    apply ae_all_iff.mpr
    intro horizon
    apply ae_all_iff.mpr
    intro n
    let N := phi (nu horizon n)
    by_cases hkn : k + k0 ≤ N
    · have hroot : rootLevel qRoot ≤ (N : ℤ) := by
        rw [hqRoot, hrootLevel, hfactor]
        push_cast
        omega
      have hBudgetLaw := aux_in_deterministic_budget_assembly_budget d I s Cg Cbound
        hCg.le hCgC cbuf k0 M H Enl Shift rootLevel observationCentre Draw Z eps heps.1.le
        lambdaA lambdaDet hThresholdsAux.1
        (hThresholdsAux.2.1.trans hThresholdsAux.2.2.1)
        prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard sN hZnonneg hTransfer
        N qRoot hroot (fun D => D ≤ horizon) (Nat.zero_le horizon)
      have hBudgetEnv : ∀ᵐ omega ∂P,
          (∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D → D ≤ horizon →
            rootLevel U + (D : ℤ) ≤ (N : ℤ) →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              prefixZ N U D code (env PUnit.unit (nu horizon n) omega) <
                  lambdaA * (D : ℝ) ∧
              prefixD N U D code (env PUnit.unit (nu horizon n) omega) <
                  lambdaA * (D : ℝ)) →
          Budget horizon N (env PUnit.unit (nu horizon n) omega) := by
        exact ae_of_ae_map (hEnvMeas PUnit.unit (nu horizon n)).aemeasurable
          (by rw [hEnvLaw PUnit.unit (nu horizon n)]; exact hBudgetLaw)
      filter_upwards [hBudgetEnv] with omega hbudget
      intro _hkn
      intro hpre
      exact hbudget (fun U D hD hDh _hlevel code => hpre U D hD hDh code)
    · exact Filter.Eventually.of_forall fun omega hk _ => False.elim (hkn hk)
  let CmpBound : ℕ := ∑ c : Cmp, (cmpLevel c).toNat
  have hCmpBound : ∀ c : Cmp, cmpLevel c ≤ (CmpBound : ℤ) := by
    intro c
    have hs := Finset.single_le_sum (fun i _ => Nat.zero_le ((cmpLevel i).toNat))
      (Finset.mem_univ c)
    by_cases hc : 0 ≤ cmpLevel c
    · have hcast : ((cmpLevel c).toNat : ℤ) = cmpLevel c := Int.toNat_of_nonneg hc
      have hs' : ((cmpLevel c).toNat : ℤ) ≤ (CmpBound : ℤ) := by exact_mod_cast hs
      calc
        cmpLevel c = ((cmpLevel c).toNat : ℤ) := hcast.symm
        _ ≤ (CmpBound : ℤ) := hs'
    · have hneg : cmpLevel c ≤ 0 := le_of_not_ge hc
      exact hneg.trans (Nat.cast_nonneg _)
  let Nmin := max (k + k0) CmpBound
  have hNtail : ∀ horizon, ∃ b : ℕ, ∀ m ≥ b, Nmin ≤ phi (nu horizon m) := by
    intro horizon
    have hT := (hphi.comp (hnu horizon)).tendsto_atTop
    have hev : ∀ᶠ m in atTop, Nmin ≤ phi (nu horizon m) :=
      hT.eventually (eventually_ge_atTop Nmin)
    exact Filter.eventually_atTop.1 hev
  choose shiftIndex hshiftIndex using hNtail
  let nuShift : ℕ → ℕ → ℕ := fun horizon n => nu horizon (n + shiftIndex horizon)
  have hAdd : ∀ b : ℕ, StrictMono (fun n : ℕ => n + b) := by
    intro b m n hmn
    change m + b < n + b
    exact Nat.add_lt_add_right hmn b
  have hnuShift : ∀ horizon, StrictMono (nuShift horizon) := by
    intro horizon
    exact (hnu horizon).comp (hAdd (shiftIndex horizon))
  have hNlarge (horizon n : ℕ) : Nmin ≤ phi (nuShift horizon n) := by
    apply hshiftIndex
    omega
  have hFiniteAllShift : ∀ᵐ omega ∂P, omega ∈ Good → ∀ horizon,
      ∀ᶠ n in atTop, FinEvent horizon (nuShift horizon n) omega := by
    filter_upwards [hFiniteAll] with omega hF
    intro hg horizon
    exact (hAdd (shiftIndex horizon)).tendsto_atTop.eventually (hF hg horizon)
  have hCampEvents (horizon m : ℕ) :=
    ae_of_ae_map (hEnvMeas PUnit.unit (nuShift horizon m)).aemeasurable
      (by
        rw [hEnvLaw PUnit.unit (nuShift horizon m)]
        exact hCampSupplier (phi (nuShift horizon m))
          (by exact_mod_cast (Nat.le_trans (Nat.le_max_left _ _) (hNlarge horizon m)))
          (fun c => (hCmpBound c).trans (by
            exact_mod_cast (Nat.le_trans (Nat.le_max_right _ _) (hNlarge horizon m)))))
  have hCampAll := ae_all_iff.mpr (fun horizon => ae_all_iff.mpr (hCampEvents horizon))
  let Cmoment : ℝ≥0 := ⟨Cgrowth, hCgrowth⟩
  have hCmoment : (Cmoment : ℝ≥0∞) = ENNReal.ofReal Cgrowth := by
    exact (ENNReal.ofReal_eq_coe_nnreal hCgrowth).symm
  have hBankEvents (horizon : ℕ) := by
    exact candidate_represented_source_bank (chaosSampleLaw M).toMeasure P
      (fun n omega => env PUnit.unit (nuShift horizon n) omega)
      (fun n => hEnvMeas PUnit.unit (nuShift horizon n))
      (fun n => hEnvLaw PUnit.unit (nuShift horizon n))
      (fun n => phi (nuShift horizon n)) Qcentre Qside hQside beta hbeta S hS
      (fun n xi => SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M H xi n Qcentre hQside)
      GN hGN GE
      (by filter_upwards [hGE] with omega hω; exact hω.comp (hnuShift horizon).tendsto_atTop)
      K Cmoment hKMem (fun n => (hKNorm n).trans_eq hCmoment.symm) hKsource
  have hBankAll := ae_all_iff.mpr hBankEvents
  have hgeom := aux_candidate_good_estimates_trace_support_root_geometry k qside hqside hqpos
    qcenter z hqcenter qRoot selfE selfShift hqRoot factor hfactor padE hpad shift hshift
    rootLevel hrootLevel rootSide hrootSide rootCentre hrootCentre rootPos Qcentre Qside hQside
    hRootsQ
  have hQopen : IsOpen (Q : Set (SpatialCoordinates d)) := Q.isOpen
  have hQcompact : IsCompact (closure (Q : Set (SpatialCoordinates d))) :=
    (centeredCube_isBounded Qcentre hQside).isCompact_closure
  exact candidate_good_estimates_trace_finish
    d hd I alpha beta s cell halpha hcell deltaGS Cbound Ccamp hCbound hCcamp0 hCcampB
    hCcampHolder deltaGrowth epshom epsCap lamCap deltaCap hNum hTpos cbuf k0 M H Ω P
    env k z qside hqside qcenter hqcenter Enl Shift Cmp rootLevel cmpLevel chosen
    observationCentre Z eps heps hepsSmall lambdaLim lambdaDet cdet hLamPos hlamSmall
    hdisorder prefixZ prefixD sN ellLoN ellHiN errN ratioN phi hphi prefixZLim prefixDLim
    ellLoLim ellHiLim errLim ratioLim Qcentre Qside hQside S hS GN hGN GE sE hsE
    hDeltaPos hEps0Cap hqpos hGoodLimit nu (by simpa only [Budget, lambdaA] using hBudgetAll) hCmpBound shiftIndex hnuShift
    hNlarge hFiniteAllShift (by simpa only [cellDet, lambdaA, nuShift, Real.rpow_neg_natCast] using hCampAll) hBankAll hgeom hQopen hQcompact

end Paper
