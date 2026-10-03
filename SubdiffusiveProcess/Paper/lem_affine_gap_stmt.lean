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

/-- The model-level part of `aux_lem_affine_gap_core_needs` (after the constants
`epshom, Cbound, eps0, lam0, delta0`), copied verbatim from the installed `lem_affine`. -/
def lem_affine_gap_stmt
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (beta alpha gamma zeta rho s sigma cell : ℝ) (cbuf k0 H1 : ℕ)
    (epshom Cbound eps0 lam0 delta0 : ℝ) : Prop :=
  let L : ℝ := (3 : ℝ) ^ H1
         ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
           (H : BilateralField d → C(SpatialCoordinates d, ℝ))
           (hMH : InfraredCharacterization M H)
           (Rm : Paper.in_responses d M)
           (Sreg : Paper.in_6_16 d M)
           (_It : Paper.in_iteration d M I Sreg)
           (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
           (field : Ω → BilateralField d)
           (hfieldMeas : Measurable field)
           (hfieldLaw : Measure.map field P = (chaosSampleLaw M).toMeasure)
           (env : PUnit.{u} → ℕ → Ω → BilateralField d)
           (hEnvMeas : ∀ (a : PUnit.{u}) (n : ℕ), Measurable (env a n))
           (hEnvLaw : ∀ (a : PUnit.{u}) (n : ℕ),
             Measure.map (env a n) P = (chaosSampleLaw M).toMeasure)
           (hEnvConv : ∀ᵐ omega ∂P, ∀ a : PUnit.{u},
             Tendsto (fun n => env a n omega) atTop (𝓝 (field omega))),
           M.delta ≤ delta0 →
           ∀ (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
             (S : ResponseSpace (centeredCube Qcentre Qside hQside))
             (hS : S.space = killedSobolevGraph (centeredCube Qcentre Qside hQside))
             (GN : ℕ → BilateralField d →
               DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
                 DomainL2 (centeredCube Qcentre Qside hQside))
             (hGN : ∀ N omega f, GN N omega f =
               (responseSolution S
                 (Lane4.cutoffPositiveCoefficient M H omega N Qcentre hQside)
                 ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
             (phi : ℕ → ℕ) (hphi : StrictMono phi)
             (RootIndex : Type) [Countable RootIndex] [DecidableEq RootIndex]
             (root0 : RootIndex)
             (zCat : RootIndex → SpatialCoordinates d) (rCat : RootIndex → ℝ)
             (hrCat : ∀ j, 0 < rCat j)
             (SCat : ∀ j, ResponseSpace (centeredCube (zCat j) (rCat j) (hrCat j)))
             (DCat : ∀ j,
               Submodule ℚ (DomainL2 (centeredCube (zCat j) (rCat j) (hrCat j))))
             [hDCatc : ∀ j, Countable (DCat j)]
             (fCat : ∀ j, (DCat j) → SpatialCoordinates d → ℝ)
             (TCat : RootIndex → Type) [hTCatc : ∀ j, Countable (TCat j)]
             (thetaCat : ∀ j, TCat j → SpatialCoordinates d → ℝ)
             (thetaH1Cat : ∀ j, TCat j →
               Homogenization.H1Function
                 (centeredCube (zCat j) (rCat j) (hrCat j) : Set (SpatialCoordinates d)))
             (usrc : PUnit.{u} → ∀ j, (DCat j) → ℕ → Ω → (SCat j).space)
             (srcRep : PUnit.{u} → ∀ j, (DCat j) → ℕ → Ω → SpatialCoordinates d → ℝ)
             (ucell : PUnit.{u} → ∀ j, TCat j → ℕ → Ω →
               Homogenization.H1Function
                 (centeredCube (zCat j) (rCat j) (hrCat j) : Set (SpatialCoordinates d)))
             (Cext : ℝ) (etaCat : ℝ) (t : ℝ) (orders : Finset ℝ)
             (Index : Type) [Countable Index]
             (resp : PUnit.{u} → Index → ℕ → Ω → ℝ)
             (respLim : PUnit.{u} → Index → Ω → ℝ)
             (constants : PUnit.{u} → Index → ℕ → Ω → ℝ) (Gcat : Set Ω)
             (coercivityKey extensionKey lambdaKey : RootIndex → Index)
             (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ j, (DCat j) → Index)
             (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, TCat j → Index)
             (Grid : Type) [Countable Grid]
             (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → RootIndex)
             (gridKey : Grid → Index)
             (hRootCatalogue : zCat root0 = Qcentre ∧ rCat root0 = Qside)
             (hRep : ∀ a : PUnit.{u},
               conv_represented_estimates d hd M H Ω P phi (env a)
                 RootIndex root0 zCat rCat hrCat SCat DCat fCat TCat thetaCat
                 thetaH1Cat (usrc a) (srcRep a) (ucell a) Cext beta alpha etaCat t
                 orders I Index (resp a) (respLim a) (constants a) Gcat
                 coercivityKey extensionKey lambdaKey sourceResponseKey
                 sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey
                 cellHolderKey Grid origin gridRoot gridKey)
             (GE : Ω → DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
               DomainL2 (centeredCube Qcentre Qside hQside))
             (hGE : ∀ᵐ omega ∂P,
               Tendsto (fun n => GN (phi n) (env PUnit.unit.{u} n omega)) atTop (𝓝 (GE omega)))
             (E : Ω → DirichletForm.ClosedForm
               (volume.restrict
                 (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
             (hE : ∀ omega u, (E omega).energy u = limitFormEnergy (GE omega) u)
             (GammaE : ∀ omega : Ω, DirichletForm.EnergyMeasure (E omega))
             (eRef : ℕ → ℝ)
             (heRefPos : ∀ k : ℕ, 0 < eRef k)
             (heRefLim : ∀ k : ℕ,
               Tendsto (fun n : ℕ =>
                 (let kappa : ℕ → ℝ := fun J =>
                    Real.exp (((J : ℝ) + 1) *
                      SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
                      SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
                  kappa (((phi n : ℤ) - (k : ℤ)).toNat) / kappa (phi n)))
                 atTop (𝓝 (eRef k)))
             (c : ℝ) (hc : 0 < c),
           let Q : Opens (SpatialCoordinates d) := centeredCube Qcentre Qside hQside
           ∀ (J : ℕ) (gridChoice : Fin J → Grid)
             (hGridChoice : ∀ j, gridRoot (gridChoice j) = root0),
           let origins : Fin J → SpatialCoordinates d := fun j => origin (gridChoice j)
           ∃ baseMesh : Ω → (SpatialCoordinates d → ℝ) → ℝ,
           (∀ᵐ omega ∂P,
             ∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
               0 < baseMesh omega f) ∧
           ∀ (n : ℕ) (z zP : SpatialCoordinates d) (gridIndex : Fin J)
             (parentIndex : Fin d → ℤ)
             (idx : OddGridIndex d (subdivisionHalfWidth H1)),
             (let k : ℕ := H1 * (n + 1)
              let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
              let q : Set (SpatialCoordinates d) := Metric.ball z (r / 2)
              let parentCell : Set (SpatialCoordinates d) := Metric.ball zP (L * r / 2)
              zP = (fun i => origins gridIndex i + (L * r) * ((parentIndex i : ℝ))) →
              z = oddGridCenter zP (L * r) (subdivisionHalfWidth H1) idx →
              parentCell ⊆ (Q : Set (SpatialCoordinates d)) →
              ∀ (qside : ℝ)
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
                    ∃ (U : Enl × Shift) (D : ℕ)
                      (w : Fin D → OddGridIndex d 1),
                      Metric.ball x (rho / 2) ⊆
                        Metric.ball
                          (descendantCenter 1 (rootCentre U) (rootSide U) D w)
                          (descendantSide 1 D (rootSide U) / 2) ∧
                      descendantSide 1 D (rootSide U) ≤ 9 * rho)
                (parent : Cmp → Enl × Shift)
                (depth : Cmp → ℕ)
                (word : (c : Cmp) → Fin (depth c) → OddGridIndex d 1)
                (cmpCentre : Cmp → SpatialCoordinates d)
                (hcmpCentre : ∀ (c : Cmp),
                  cmpCentre c =
                    descendantCenter 1 (rootCentre (parent c))
                      (rootSide (parent c)) (depth c) (word c))
                (cmpLevel : Cmp → ℤ)
                (hcmpLevel : ∀ (c : Cmp),
                  cmpLevel c = rootLevel (parent c) + (depth c : ℤ))
                (cmpSide : Cmp → ℝ)
                (hcmpSide : ∀ (c : Cmp),
                  cmpSide c = (3 : ℝ) ^ (-cmpLevel c))
                (cmpPos : ∀ (c : Cmp), 0 < cmpSide c)
                (chosen : Cmp)
                (hcmpChosenCentre : cmpCentre chosen = z)
                (hcmpChosenLevel : cmpLevel chosen =
                  (k : ℤ) - (Nat.floor (gamma * (H1 : ℝ)) : ℤ) - 4)
                (hcmpChosenPad : Metric.closedBall z (cmpSide chosen / 2) ⊆
                  parentCell)
                (observationCentre :
                  ∀ (U : Enl × Shift) (D : ℕ),
                    ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
                      SpatialCoordinates d)
                (hObservationCentre : ∀ (U : Enl × Shift) (D : ℕ)
                  (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
                  observationCentre U D code =
                    Sum.elim
                      (fun w => descendantCenter 1 (rootCentre U)
                        (rootSide U) D w)
                      (fun V => rootCentre V) code)
                (eta : ℕ → BilateralField d →
                  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
                (hEta : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                  ∀ (N i : ℕ) (y : Vec d),
                    eta N omega i y =
                      omega ((i : ℤ) - (N : ℤ))
                        (((3 : ℝ) ^ (-(N : ℤ))) • y)))
                (F Praw Rraw Draw :
                  ℕ → ℕ → Vec d → BilateralField d → ENNReal)
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
                            (((3 : ℝ) ^ N) • observationCentre U D code)
                            omega
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
                            (((3 : ℝ) ^ N) • observationCentre U D code)
                            omega).toReal
                        else 0
                    else 0)
                (hFiniteScoreGuard :
                  (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                  ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
                    (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
                    rootLevel U + (D : ℤ) ≤ (N : ℤ) →
                    ∀ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                      (rootLevel U + (D : ℤ)),
                      Draw N ((N : ℤ) - j).toNat
                        (((3 : ℝ) ^ N) • observationCentre U D code)
                        omega ≠ ⊤))
                (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
                (hsN : ∀ (N : ℕ) (l : ℤ) (w : SpatialCoordinates d)
                  (omega : BilateralField d),
                  sN N l w omega =
                    if l ≤ (N : ℤ) then
                      (let kappa : ℕ → ℝ := fun J =>
                        Real.exp (((J : ℝ) + 1) *
                          SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
                          SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
                       let retained :
                         ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
                         fun ell v beta =>
                           if 0 ≤ ell then
                             ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
                           else
                             -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
                       kappa ((N : ℤ) - l).toNat / kappa N *
                         Real.exp (H omega w + retained l w omega))
                    else 1)
                (ellLoN ellHiN : ℕ → Enl × Shift → BilateralField d → ℝ)
                (hEllLoN : ∀ (N : ℕ) (U : Enl × Shift)
                  (omega : BilateralField d),
                  ellLoN N U omega =
                    I.lam (rootCentre U) (rootSide U) (rootPos U)
                      (SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient
                        M H omega N (rootCentre U) (rootPos U))
                      (rootCentre U) (rootSide U) sigma 2 /
                      sN N (rootLevel U) (rootCentre U) omega)
                (hEllHiN : ∀ (N : ℕ) (U : Enl × Shift)
                  (omega : BilateralField d),
                  ellHiN N U omega =
                    I.Lam (rootCentre U) (rootSide U) (rootPos U)
                      (SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient
                        M H omega N (rootCentre U) (rootPos U))
                      (rootCentre U) (rootSide U) sigma 2 /
                      sN N (rootLevel U) (rootCentre U) omega)
                (AEN : ℕ → Enl × Shift → BilateralField d →
                  Matrix (Fin d) (Fin d) ℝ)
                (hAEN : ∀ (N : ℕ) (U : Enl × Shift)
                  (omega : BilateralField d),
                  AEN N U omega =
                    (sN N (rootLevel U) (rootCentre U) omega)⁻¹ •
                      Homogenization.Book.Ch02.sigmaCoarse
                        (Homogenization.Book.Ch02.cubeDomain
                          (Homogenization.originCube d 0))
                        ((I.chart (rootCentre U) (rootSide U) (rootPos U)
                          (SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient
                            M H omega N (rootCentre U) (rootPos U))
                          (rootCentre U) (rootSide U)).coeffOn
                          (Homogenization.originCube d 0)))
                (errN ratioN : ℕ → Cmp → BilateralField d → ℝ)
                (hErrN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
                  errN N c omega =
                    I.err (cmpCentre c) (cmpSide c) (cmpPos c)
                      (SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient
                        M H omega N (cmpCentre c) (cmpPos c))
                      (cmpCentre c) (cmpSide c)
                      (sN N (cmpLevel c) (cmpCentre c) omega) s 2)
                (hRatioN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
                  ratioN N c omega =
                    sN N (k : ℤ) qcenter omega /
                      sN N (cmpLevel c) (cmpCentre c) omega)
                (sE : Ω → ℝ)
                (sCmp : Cmp → Ω → ℝ)
                (hsE : (∀ᵐ omega ∂P,
                    0 < sE omega ∧
                    Tendsto (fun n => sN (phi n) (k : ℤ) z (env PUnit.unit.{u} n omega))
                      atTop (𝓝 (sE omega))) ∧
                  (∀ᵐ omega ∂P,
                    sE omega = eRef k *
                      Real.exp (H (field omega) z +
                        ∑ j ∈ Finset.range k, (field omega) (-(j : ℤ)) z)))
                (hsCmp : ∀ᵐ omega ∂P,
                  ∀ c' : Cmp,
                    0 < sCmp c' omega ∧
                    Tendsto
                      (fun n => sN (phi n) (cmpLevel c') (cmpCentre c')
                        (env PUnit.unit.{u} n omega))
                      atTop (𝓝 (sCmp c' omega)))
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
                    (fun n omega =>
                      prefixZ (phi n) U D code (env PUnit.unit.{u} n omega))
                    atTop (prefixZLim U D code))
                (hPrefixDLim : ∀ (U : Enl × Shift) (D : ℕ)
                  (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
                  TendstoInMeasure P
                    (fun n omega =>
                      prefixD (phi n) U D code (env PUnit.unit.{u} n omega))
                    atTop (prefixDLim U D code))
                (hEllLoLim : ∀ (U : Enl × Shift),
                  TendstoInMeasure P
                    (fun n omega => ellLoN (phi n) U (env PUnit.unit.{u} n omega)) atTop
                    (ellLoLim U))
                (hEllHiLim : ∀ (U : Enl × Shift),
                  TendstoInMeasure P
                    (fun n omega => ellHiN (phi n) U (env PUnit.unit.{u} n omega)) atTop
                    (ellHiLim U))
                (hAELim : ∀ (U : Enl × Shift) (i j : Fin d),
                  TendstoInMeasure P
                    (fun n omega => AEN (phi n) U (env PUnit.unit.{u} n omega) i j) atTop
                    (fun omega => AE_Lim U omega i j))
                (hErrLim : ∀ (c : Cmp),
                  TendstoInMeasure P
                    (fun n omega => errN (phi n) c (env PUnit.unit.{u} n omega)) atTop
                    (errLim c))
                (hRatioLim : ∀ (c : Cmp),
                  TendstoInMeasure P
                    (fun n omega => ratioN (phi n) c (env PUnit.unit.{u} n omega)) atTop
                    (ratioLim c))
                (hRootsQ : ∀ U : Enl × Shift,
                  closure
                    (centeredCube (rootCentre U) (rootSide U)
                      (rootPos U) : Set (SpatialCoordinates d)) ⊆
                    (Q : Set (SpatialCoordinates d))),
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
                ∀ᵐ omega ∂P,
                  ∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
                  ∀ (fL2 : DomainL2 Q),
                    ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                      (Q : Set (SpatialCoordinates d))] f) →
                    (let u := GE omega fL2
                     ∃ U : SpatialCoordinates d → ℝ,
                       ContinuousOn U (closure (Q : Set (SpatialCoordinates d))) ∧
                       ((u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                         (Q : Set (SpatialCoordinates d))] U) ∧
                       (∀ x ∈ frontier (Q : Set (SpatialCoordinates d)), U x = 0) ∧
                       (r ≤ baseMesh omega f → omega ∈ Good →
                         Lane4.IsHolderOn alpha (closure q) U ∧
                         (let lambda : Set (SpatialCoordinates d) → ℝ :=
                            fun A => ((GammaE omega).measure u A).toReal +
                              c * (volume A).toReal
                          lambda parentCell ≤
                            L ^ ((d : ℝ) + zeta) * lambda q →
                          ∃ pc : (Fin d → ℝ) × ℝ,
                            (let ell : SpatialCoordinates d → ℝ :=
                               fun x => (∑ i, pc.1 i * x i) + pc.2
                             let b : SpatialCoordinates d → ℝ :=
                               fun x => U x - ell x
                             let eSet : Set ℝ :=
                               {e : ℝ |
                                 ∃ (v : DomainL2 Q)
                                   (V : SpatialCoordinates d → ℝ),
                                   v ∈ (E omega).domain ∧
                                   ContinuousOn V
                                     (closure (Q : Set (SpatialCoordinates d))) ∧
                                   ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                                     (Q : Set (SpatialCoordinates d))] V) ∧
                                   (∀ x ∈ frontier q, V x = b x) ∧
                                   e = ((GammaE omega).measure v q).toReal}
                             ∃ Lambda : ℝ,
                               IsGLB eSet Lambda ∧
                               eSet.Nonempty ∧
                               Lambda ≤ rho * lambda q)))))



def aux_lem_affine_gap_stmt_trace
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (beta C delta0 : ℝ) : Prop :=
  ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
      (Sreg : in_6_16 d M) (It : in_iteration d M I Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
    InfraredCharacterization M H → M.delta ≤ delta0 →
    ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (S : ResponseSpace (centeredCube z r hr))
      (hS : S.space = killedSobolevGraph (centeredCube z r hr))
      (k : ℕ) (z0 : SpatialCoordinates d) (N : ℕ → ℕ) (hN : StrictMono N)
      (Omega : Type) [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
      (env : ℕ → Omega → BilateralField d)
      (hEnv : ∀ n, Measurable (env n))
      (hLaw : ∀ n, Measure.map (env n) P = (chaosSampleLaw M).toMeasure)
      (GN : ℕ → BilateralField d → DomainL2 (centeredCube z r hr) →L[ℝ]
        DomainL2 (centeredCube z r hr))
      (hGN : ∀ n xi f, GN n xi f =
        (responseSolution S (cutoffPositiveCoefficient M H xi n z hr)
          ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
      (G : Omega → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
      (hG : ∀ᵐ om ∂P, Tendsto (fun n => GN (N n) (env n om)) atTop (𝓝 (G om)))
      (E : Omega → DirichletForm.ClosedForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
      (hE : ∀ om u, (E om).energy u = limitFormEnergy (G om) u)
      (Gamma : ∀ om, DirichletForm.EnergyMeasure (E om))
      (hcont : ∀ᵐ om ∂P, ∀ f : DomainL2 (centeredCube z r hr),
        (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
          tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
          (f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))] fc) →
        ∃ U : SpatialCoordinates d → ℝ,
          ContinuousOn U (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
          (G om f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
          ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), U x = 0)
      (scale : ℕ → Omega → ℝ) (s L : Omega → ℝ)
      (hs : ∀ᵐ om ∂P, 0 < s om ∧ Tendsto (fun n => scale n om) atTop (𝓝 (s om)))
      (hNorm : TendstoInMeasure P
        (fun n om => I.Lam z0 ((3 : ℝ) ^ (-(k : ℤ))) (by positivity)
          (cutoffPositiveCoefficient M H (env n om) (N n) z0 (by positivity))
          z0 ((3 : ℝ) ^ (-(k : ℤ))) ((beta - 1 / 2) / 4) 2 / scale n om) atTop L)
      (cap : ℝ) (hcap : 0 < cap),
    ∀ᵐ om ∂P, L om ≤ cap →
      Metric.ball z0 (3 * ((3 : ℝ) ^ (-(k : ℤ))) / 2) ⊆
        (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∀ b : SpatialCoordinates d → ℝ,
        ContinuousOn b (frontier (Metric.ball z0 (((3 : ℝ) ^ (-(k : ℤ))) / 2))) →
        IsHolderOn beta (frontier (Metric.ball z0 (((3 : ℝ) ^ (-(k : ℤ))) / 2))) b →
        ∃ (v : DomainL2 (centeredCube z r hr)) (V : SpatialCoordinates d → ℝ),
          v ∈ (E om).domain ∧
          ContinuousOn V (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
          (v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))] V ∧
          (∀ x ∈ frontier (Metric.ball z0 (((3 : ℝ) ^ (-(k : ℤ))) / 2)), V x = b x) ∧
          ((Gamma om).measure v (Metric.ball z0 (((3 : ℝ) ^ (-(k : ℤ))) / 2))).toReal ≤
            C * (2 * cap * s om) * ((3 : ℝ) ^ (-(k : ℤ))) ^ ((d : ℝ) - 2) *
              (((3 : ℝ) ^ (-(k : ℤ))) ^ beta * holderSeminorm beta
                (frontier (Metric.ball z0 (((3 : ℝ) ^ (-(k : ℤ))) / 2))) b) ^ 2



def aux_lem_affine_gap_stmt_poinc
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (Pin : Paper.in_poincare d hd I) (delta0 : ℝ) : Prop :=
  ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (Qc : SpatialCoordinates d) (Qs : ℝ) (hQs : 0 < Qs)
        (S : ResponseSpace (centeredCube Qc Qs hQs))
        (hS : S.space = killedSobolevGraph (centeredCube Qc Qs hQs))
        (N : ℕ → ℕ) (hN : StrictMono N)
        (Omega : Type) [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
        (env : ℕ → Omega → BilateralField d)
        (hEnv : ∀ n, Measurable (env n))
        (hLaw : ∀ n, Measure.map (env n) P = (chaosSampleLaw M).toMeasure)
        (GN : ℕ → BilateralField d → DomainL2 (centeredCube Qc Qs hQs) →L[ℝ]
          DomainL2 (centeredCube Qc Qs hQs))
        (hGN : ∀ n xi f, GN n xi f =
          (responseSolution S (cutoffPositiveCoefficient M H xi n Qc hQs)
            ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
        (G : Omega → DomainL2 (centeredCube Qc Qs hQs) →L[ℝ] DomainL2 (centeredCube Qc Qs hQs))
        (hG : ∀ᵐ om ∂P, Tendsto (fun n => GN (N n) (env n om)) atTop (𝓝 (G om)))
        (E : Omega → DirichletForm.ClosedForm
          (volume.restrict (centeredCube Qc Qs hQs : Set (SpatialCoordinates d))))
        (hE : ∀ om u, (E om).energy u = limitFormEnergy (G om) u)
        (Gamma : ∀ om, DirichletForm.EnergyMeasure (E om))
        (hcont : ∀ᵐ om ∂P, ∀ f : DomainL2 (centeredCube Qc Qs hQs),
          (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
            tsupport fc ⊆ (centeredCube Qc Qs hQs : Set (SpatialCoordinates d)) ∧
            (f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
              (centeredCube Qc Qs hQs : Set (SpatialCoordinates d))] fc) →
          ∃ U : SpatialCoordinates d → ℝ,
            ContinuousOn U (closure (centeredCube Qc Qs hQs : Set (SpatialCoordinates d))) ∧
            (G om f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
              (centeredCube Qc Qs hQs : Set (SpatialCoordinates d))] U ∧
            ∀ x ∈ frontier (centeredCube Qc Qs hQs : Set (SpatialCoordinates d)), U x = 0)
        (z : SpatialCoordinates d) (m : ℝ) (hm : 0 < m)
        (hcube : centeredCube z m hm ≤ centeredCube Qc Qs hQs)
        (parentCell : Set (SpatialCoordinates d)) (hparent : IsOpen parentCell)
        (hpad : closure (centeredCube z m hm : Set (SpatialCoordinates d)) ⊆ parentCell)
        (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (hs2 : 2 * s ≤ 1)
        (scale : ℕ → Omega → ℝ) (hscale : ∀ n om, 0 < scale n om) (sLim : Omega → ℝ)
        (hsLim : ∀ᵐ om ∂P, 0 < sLim om ∧ Tendsto (fun n => scale n om) atTop (𝓝 (sLim om)))
        (errLim : Omega → ℝ)
        (herr : TendstoInMeasure P (fun n om => I.err z m hm
          (cutoffPositiveCoefficient M H (env n om) (N n) z hm) z m (scale n om) s 2)
          atTop errLim),
      ∀ᵐ om ∂P, errLim om < 1 →
        ∀ (f : DomainL2 (centeredCube Qc Qs hQs)) (U : SpatialCoordinates d → ℝ),
          (G om f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (centeredCube Qc Qs hQs : Set (SpatialCoordinates d))] U →
          (normalizedL2On (centeredCube z m hm : Set (SpatialCoordinates d))
            (fun x => U x - (volume.real (centeredCube z m hm : Set (SpatialCoordinates d)))⁻¹ *
              ∫ y in (centeredCube z m hm : Set (SpatialCoordinates d)), U y)) ^ 2 ≤
            (Pin.C ^ 2 * m ^ 2 *
              ((Homogenization.Book.Ch02.geometricDiscount s 2 /
                Homogenization.Book.Ch02.geometricDiscount 1 1) * (1 / 5 : ℝ))⁻¹ /
                  volume.real (centeredCube z m hm : Set (SpatialCoordinates d))) * (sLim om)⁻¹ *
              ((Gamma om).measure (G om f) parentCell).toReal

end Paper
end
