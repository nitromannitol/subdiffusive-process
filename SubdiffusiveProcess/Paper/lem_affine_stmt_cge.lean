module

public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Lane2.LimitForm
public import SubdiffusiveProcess.Lane2.BoundaryResponse
public import SubdiffusiveProcess.Lane4.Inputs
public import SubdiffusiveProcess.Lane3.Forms
public import SubdiffusiveProcess.Lane3.Subdivision
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Lane4.Carriers
public import Homogenization.Book.Ch02.Matrices
public import Homogenization.Book.Ch02.MultiscaleEllipticity
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import SubdiffusiveProcess.Paper.candidate_good_event
public import SubdiffusiveProcess.Paper.cell_catalogue
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.conv_represented_estimates
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_deterministic
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.primitive_scores
public import SubdiffusiveProcess.Paper.in_iteration

@[expose] public section




open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

universe u



def lem_affine_stmt_cge
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (alpha beta s sigma cell : ℝ)
    (epshom Cbound eps0 lam0 delta0 : ℝ) : Prop :=
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
        (env : PUnit.{u} → ℕ → Ω → BilateralField d)
        (hEnvMeas : ∀ (a : PUnit.{u}) (n : ℕ), Measurable (env a n))
        (hEnvLaw : ∀ (a : PUnit.{u}) (n : ℕ),
          Measure.map (env a n) P = (chaosSampleLaw M).toMeasure)
        (hEnvConv : ∀ᵐ omega ∂P, ∀ a : PUnit.{u},
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
        Cbound⁻¹ * sE omega ≤ Uq ∧ Uq ≤ Cbound * sE omega)


end Paper
