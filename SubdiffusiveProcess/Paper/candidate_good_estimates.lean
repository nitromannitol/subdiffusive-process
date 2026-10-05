module

public import SubdiffusiveProcess.Paper.candidate_good_estimates_algebraic_assembly
public import SubdiffusiveProcess.Paper.candidate_good_estimates_analytic_assembly
public import SubdiffusiveProcess.Paper.candidate_good_estimates_trace_supplier
public import SubdiffusiveProcess.Paper.candidate_good_event

@[expose] public section

/-! Candidate source regularity, harmonic comparison, and limiting chart bounds.
The proof combines the finite-horizon trace passage with the represented harmonic bank.
-/

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper
universe uCge

/-- The source, harmonic, and chart estimates pass to the actual represented candidate on its strict Good event. -/
theorem candidate_good_estimates
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (_X : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (_Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (_Poincare : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (_MeyersMorrey : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (_Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (D : _root_.SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (alpha beta s sigma cell : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1)
    (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (hsSmall : s ≤ (1 / 32 : ℝ))
    (hsigma_eq : sigma = (beta - 1 / 2) / 4)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (hcell : cell ∈ Set.Ioo (0 : ℝ) 1)
    :
    ∃ Cbound : ℝ, 1 ≤ Cbound ∧
    ∀ (epshom : ℝ) (hepshom : 0 < epshom), epshom ≤ 1 →
    ∃ eps0 lam0 delta0 : ℝ,
      0 < eps0 ∧ 0 < lam0 ∧ 0 < delta0 ∧
      ∀ (cbuf k0 : ℕ)
        (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M) (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M)
        (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hMH : InfraredCharacterization M H)
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (field : Ω → BilateralField d)
        (hfieldMeas : Measurable field)
        (hfieldLaw : Measure.map field P = (chaosSampleLaw M).toMeasure)
        (env : PUnit → ℕ → Ω → BilateralField d)
        (hEnvMeas : ∀ (a : PUnit) (n : ℕ), Measurable (env a n))
        (hEnvLaw : ∀ (a : PUnit) (n : ℕ),
          Measure.map (env a n) P = (chaosSampleLaw M).toMeasure)
        (hEnvConv : ∀ᵐ omega ∂P, ∀ a : PUnit,
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
          ∀ (_U : Enl × Shift) (D : ℕ),
            ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
              SpatialCoordinates d)
        (hObservationCentre : ∀ (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          observationCentre U D code =
            Sum.elim
              (fun w => descendantCenter 1 (rootCentre U) (rootSide U) D w)
              (fun V => rootCentre V) code)
        (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
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
        (prefixZ : ∀ (_N : ℕ) (_U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (prefixD : ∀ (_N : ℕ) (_U : Enl × Shift) (D : ℕ),
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
                  _root_.SubdiffusiveProcess.Model.tauSq M.P) *
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
        (phi : ℕ → ℕ)
        (hphi : StrictMono phi)
        (prefixZLim : ∀ (_U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) → Ω → ℝ)
        (prefixDLim : ∀ (_U : Enl × Shift) (D : ℕ),
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
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
            ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
        (GE : Ω → DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
          DomainL2 (centeredCube Qcentre Qside hQside))
        (hGE : (∀ᵐ omega ∂P,
          Tendsto (fun n => GN (phi n) (env PUnit.unit n omega)) atTop (𝓝 (GE omega))))
        (E : Ω → _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
          (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
        (hE : ∀ omega u, (E omega).energy u = limitFormEnergy (GE omega) u)
        (GammaE : ∀ omega : Ω, _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure (E omega))
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
          _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (closure q) U ∧
          (∃ cq : ℝ,
            _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
              (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
              (fun x => U (z + r • x) - cq) ≤
                Ctotal * (normalizedL2On p
                  (fun x => U x - (volume.real p)⁻¹ * ∫ y in p, U y) +
                  r ^ 2 * (sE omega)⁻¹ * fsup)) ∧
          (let qc := centeredCube (cmpCentre chosen) (cmpSide chosen / 81)
             (div_pos (cmpPos chosen) (by norm_num))
           let qi : Set (SpatialCoordinates d) := Metric.ball (cmpCentre chosen) (cmpSide chosen / 1458)
           let qo : Set (SpatialCoordinates d) := Metric.ball (cmpCentre chosen) (cmpSide chosen / 18)
           ∀ w : SpatialCoordinates d,
           let qd : Set (SpatialCoordinates d) :=
             Metric.ball w (27 * cmpSide chosen / 2)
           Metric.closedBall (cmpCentre chosen) (cmpSide chosen / 18) ⊆ qd →
           qd ⊆ (Q : Set (SpatialCoordinates d)) →
           ∃ (v : weakSobolevGraph qc) (V : SpatialCoordinates d → ℝ),
             ContinuousOn V (closure (qc : Set (SpatialCoordinates d))) ∧
             (((v : SobolevData qc).1 : SpatialCoordinates d → ℝ)
               =ᵐ[volume.restrict (qc : Set (SpatialCoordinates d))] V) ∧
             (∀ x ∈ frontier (qc : Set (SpatialCoordinates d)), V x = U x) ∧
             (∀ psi : killedSobolevGraph qc,
               inner ℝ (sobolevGradient (v : SobolevData qc))
                 (subspaceGradient (killedSobolevGraph qc) psi) = 0) ∧
             normalizedL2On qi (fun x => U x - V x) ≤
               epshom * normalizedL2On qo
                 (fun x => U x - (volume.real qo)⁻¹ * ∫ y in qo, U y) +
               Ctotal * (cmpSide chosen / 9) ^ 2 * (sCmp chosen omega)⁻¹ * fsup)) ∧
      (∀ (Uroot : Enl × Shift) (x : Fin d → ℝ),
        Cbound⁻¹ * Matrix.trace (AE_Lim Uroot omega) * (x ⬝ᵥ x) ≤
          x ⬝ᵥ (AE_Lim Uroot omega).mulVec x) ∧
      (∃ Uq : ℝ,
        Uq = ellHiLim qRoot omega * sE omega ∧
        Cbound⁻¹ * sE omega ≤ Uq ∧ Uq ≤ Cbound * sE omega) := by
  exact candidate_good_estimates_algebraic_assembly d hd I _X _Sob _Poincare _MeyersMorrey _Step D Cp alpha beta s sigma cell halpha hbeta hs hsSmall hsigma_eq hsigma hcell
    (candidate_good_estimates_analytic_assembly d hd I _X _Sob _Poincare _MeyersMorrey _Step D Cp alpha beta s sigma cell halpha hbeta hs hsSmall hsigma_eq hsigma hcell
      (candidate_good_estimates_trace_supplier d hd I _X _Sob _Poincare _MeyersMorrey _Step D Cp alpha beta s sigma cell halpha hbeta hs hsSmall hsigma_eq hsigma hcell))

/-- The canonical environment is the constant-environment instance of the represented estimate. -/
theorem aux_candidate_good_estimates_canonical
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (_X : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (_Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (_Poincare : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (_MeyersMorrey : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (_Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (D : _root_.SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (alpha beta s sigma cell : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1)
    (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (hsSmall : s ≤ (1 / 32 : ℝ))
    (hsigma_eq : sigma = (beta - 1 / 2) / 4)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (hcell : cell ∈ Set.Ioo (0 : ℝ) 1)
    :
    ∃ Cbound : ℝ, 1 ≤ Cbound ∧
    ∀ (epshom : ℝ) (hepshom : 0 < epshom), epshom ≤ 1 →
    ∃ eps0 lam0 delta0 : ℝ,
      0 < eps0 ∧ 0 < lam0 ∧ 0 < delta0 ∧
      ∀ (cbuf k0 : ℕ)
        (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M) (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M)
        (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hMH : InfraredCharacterization M H)
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
          ∀ (_U : Enl × Shift) (D : ℕ),
            ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
              SpatialCoordinates d)
        (hObservationCentre : ∀ (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          observationCentre U D code =
            Sum.elim
              (fun w => descendantCenter 1 (rootCentre U) (rootSide U) D w)
              (fun V => rootCentre V) code)
        (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
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
        (prefixZ : ∀ (_N : ℕ) (_U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (prefixD : ∀ (_N : ℕ) (_U : Enl × Shift) (D : ℕ),
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
                  _root_.SubdiffusiveProcess.Model.tauSq M.P) *
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
        (phi : ℕ → ℕ)
        (hphi : StrictMono phi)
        (prefixZLim : ∀ (_U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (prefixDLim : ∀ (_U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (ellLoLim ellHiLim : (Enl × Shift) → BilateralField d → ℝ)
        (AE_Lim : (Enl × Shift) → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (errLim ratioLim : Cmp → BilateralField d → ℝ)
        (hPrefixZLim : ∀ (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          TendstoInMeasure (chaosSampleLaw M).toMeasure
            (fun n omega => prefixZ (phi n) U D code omega) atTop
            (prefixZLim U D code))
        (hPrefixDLim : ∀ (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          TendstoInMeasure (chaosSampleLaw M).toMeasure
            (fun n omega => prefixD (phi n) U D code omega) atTop
            (prefixDLim U D code))
        (hEllLoLim : ∀ (U : Enl × Shift),
          TendstoInMeasure (chaosSampleLaw M).toMeasure
            (fun n omega => ellLoN (phi n) U omega) atTop (ellLoLim U))
        (hEllHiLim : ∀ (U : Enl × Shift),
          TendstoInMeasure (chaosSampleLaw M).toMeasure
            (fun n omega => ellHiN (phi n) U omega) atTop (ellHiLim U))
        (hAELim : ∀ (U : Enl × Shift) (i j : Fin d),
          TendstoInMeasure (chaosSampleLaw M).toMeasure
            (fun n omega => AEN (phi n) U omega i j) atTop
            (fun omega => AE_Lim U omega i j))
        (hErrLim : ∀ (c : Cmp),
          TendstoInMeasure (chaosSampleLaw M).toMeasure
            (fun n omega => errN (phi n) c omega) atTop (errLim c))
        (hRatioLim : ∀ (c : Cmp),
          TendstoInMeasure (chaosSampleLaw M).toMeasure
            (fun n omega => ratioN (phi n) c omega) atTop (ratioLim c))
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
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
            ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
        (GE : BilateralField d → DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
          DomainL2 (centeredCube Qcentre Qside hQside))
        (hGE : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          Tendsto (fun n => GN (phi n) omega) atTop (𝓝 (GE omega))))
        (E : BilateralField d → _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
          (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
        (hE : ∀ omega u, (E omega).energy u = limitFormEnergy (GE omega) u)
        (GammaE : ∀ omega, _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure (E omega))
        (sE : BilateralField d → ℝ) (sCmp : Cmp → BilateralField d → ℝ)
        (hsE : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          0 < sE omega ∧
          Tendsto (fun n => sN (phi n) (k : ℤ) z omega) atTop (𝓝 (sE omega))))
        (hsCmp : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ c : Cmp,
          0 < sCmp c omega ∧
          Tendsto (fun n => sN (phi n) (cmpLevel c) (cmpCentre c) omega)
            atTop (𝓝 (sCmp c omega)))),
    let Q := centeredCube Qcentre Qside hQside
    let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
    let q : Set (SpatialCoordinates d) := Metric.ball z (r / 2)
    let p : Set (SpatialCoordinates d) := Metric.ball z (3 * r / 2)
    let Ctotal := Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ)))
    let Good : Set (BilateralField d) :=
      candidate_good_event
        d hd I M H hMH k z qside hqside qcenter
        hqcenter Enl Shift Cmp selfE selfShift qRoot hqRoot factor hfactor padE hpad
        shift hshift rootLevel hrootLevel rootSide hrootSide rootCentre hrootCentre rootPos hGridCover
        parent depth word cmpCentre hcmpCentre cmpLevel hcmpLevel cmpSide hcmpSide
        cmpPos chosen observationCentre hObservationCentre eta hEta F Praw Rraw
        Draw Z rawGood s eps hs heps hPrimitive cbuf
        k0 lambdaCut lambdaLim lambdaDet sigma cell epshom cdet
        hThresholds hsigma hcell hepshom hcdet prefixZ prefixD hPrefixZ
        hPrefixD hFiniteScoreGuard sN hsN ellLoN ellHiN hEllLoN hEllHiN AEN
        hAEN errN ratioN hErrN hRatioN phi hphi prefixZLim prefixDLim
        ellLoLim ellHiLim AE_Lim errLim ratioLim hPrefixZLim hPrefixDLim hEllLoLim hEllHiLim
        hAELim hErrLim hRatioLim
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, omega ∈ Good →
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
          _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (closure q) U ∧
          (∃ cq : ℝ,
            _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
              (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
              (fun x => U (z + r • x) - cq) ≤
                Ctotal * (normalizedL2On p
                  (fun x => U x - (volume.real p)⁻¹ * ∫ y in p, U y) +
                  r ^ 2 * (sE omega)⁻¹ * fsup)) ∧
          (let qc := centeredCube (cmpCentre chosen) (cmpSide chosen / 81)
             (div_pos (cmpPos chosen) (by norm_num))
           let qi : Set (SpatialCoordinates d) := Metric.ball (cmpCentre chosen) (cmpSide chosen / 1458)
           let qo : Set (SpatialCoordinates d) := Metric.ball (cmpCentre chosen) (cmpSide chosen / 18)
           ∀ w : SpatialCoordinates d,
           let qd : Set (SpatialCoordinates d) :=
             Metric.ball w (27 * cmpSide chosen / 2)
           Metric.closedBall (cmpCentre chosen) (cmpSide chosen / 18) ⊆ qd →
           qd ⊆ (Q : Set (SpatialCoordinates d)) →
           ∃ (v : weakSobolevGraph qc) (V : SpatialCoordinates d → ℝ),
             ContinuousOn V (closure (qc : Set (SpatialCoordinates d))) ∧
             (((v : SobolevData qc).1 : SpatialCoordinates d → ℝ)
               =ᵐ[volume.restrict (qc : Set (SpatialCoordinates d))] V) ∧
             (∀ x ∈ frontier (qc : Set (SpatialCoordinates d)), V x = U x) ∧
             (∀ psi : killedSobolevGraph qc,
               inner ℝ (sobolevGradient (v : SobolevData qc))
                 (subspaceGradient (killedSobolevGraph qc) psi) = 0) ∧
             normalizedL2On qi (fun x => U x - V x) ≤
               epshom * normalizedL2On qo
                 (fun x => U x - (volume.real qo)⁻¹ * ∫ y in qo, U y) +
               Ctotal * (cmpSide chosen / 9) ^ 2 * (sCmp chosen omega)⁻¹ * fsup)) ∧
      (∀ (Uroot : Enl × Shift) (x : Fin d → ℝ),
        Cbound⁻¹ * Matrix.trace (AE_Lim Uroot omega) * (x ⬝ᵥ x) ≤
          x ⬝ᵥ (AE_Lim Uroot omega).mulVec x) ∧
      (∃ Uq : ℝ,
        Uq = ellHiLim qRoot omega * sE omega ∧
        Cbound⁻¹ * sE omega ≤ Uq ∧ Uq ≤ Cbound * sE omega) := by
  obtain ⟨Cbound, h1, hmain0⟩ :=
    candidate_good_estimates d hd I _X _Sob _Poincare _MeyersMorrey _Step D Cp alpha beta s sigma cell
      halpha hbeta hs hsSmall hsigma_eq hsigma hcell
  refine ⟨Cbound, h1, fun epshom hepshom hepshom1 => ?_⟩
  obtain ⟨eps0, lam0, delta0, h2, h3, h4, hmain⟩ := hmain0 epshom hepshom hepshom1
  refine ⟨eps0, lam0, delta0, h2, h3, h4, ?_⟩
  intro cbuf k0 M _Rm Sreg _It H hMH
  exact hmain cbuf k0 M _Rm Sreg _It H hMH (BilateralField d) (chaosSampleLaw M).toMeasure id
    measurable_id Measure.map_id
    (fun (_ : PUnit.{1}) (_ : ℕ) => (id : BilateralField d → BilateralField d))
    (fun (_ : PUnit.{1}) (_ : ℕ) => measurable_id)
    (fun (_ : PUnit.{1}) (_ : ℕ) => Measure.map_id)
    (Filter.Eventually.of_forall fun (_ : BilateralField d) (_ : PUnit.{1}) => tendsto_const_nhds)


end SubdiffusiveProcess.Paper
