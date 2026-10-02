import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.primitive_scores
import SubdiffusiveProcess.Lane3.Subdivision
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Lane4.Carriers
import Homogenization.Book.Ch02.Matrices
import Homogenization.Book.Ch02.MultiscaleEllipticity
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Paper



def candidate_good_event
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
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
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d),
        eta N omega i y =
          omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
    (s eps : ℝ)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
    (hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ N : ℕ,
        primitive_scores d M s eps (eta N omega)
          (fun m y => F N m y omega)
          (fun m y => Praw N m y omega)
          (fun m y => Rraw N m y omega)
          (fun m y => Draw N m y omega)
          (fun m y => Z N m y omega)
          (fun m y => rawGood N m y omega))
    (cbuf k0 : ℕ)
    (lambdaCut lambdaLim lambdaDet sigma cell epshom cdet : ℝ)
    (hThresholds :
      0 < lambdaCut ∧ lambdaCut < lambdaLim ∧
      lambdaLim < lambdaDet ∧ lambdaDet < 1)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (hcell : cell ∈ Set.Ioo (0 : ℝ) 1)
    (hepshom : 0 < epshom)
    (hcdet : 0 < cdet)
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
      ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
        BilateralField d → ℝ)
    (prefixDLim : ∀ (U : Enl × Shift) (D : ℕ),
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
        (fun n omega => ratioN (phi n) c omega) atTop (ratioLim c)) :
    Set (BilateralField d) :=
  {omega |
    (∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D →
      ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
        prefixZLim U D code omega < lambdaLim * (D : ℝ) ∧
        prefixDLim U D code omega < lambdaLim * (D : ℝ)) ∧
    (∀ U : Enl × Shift,
      cell ≤ ellLoLim U omega ∧ ellHiLim U omega ≤ cell⁻¹) ∧
    errLim chosen omega ≤ epshom * cdet ∧
    (∀ c : Cmp, ratioLim c omega ∈ Set.Ioo (1 / 2 : ℝ) 2)}

end Paper
