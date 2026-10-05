module

public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.primitive_scores
public import SubdiffusiveProcess.ResponseMoments.Subdivision
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import Homogenization.Book.Ch02.Matrices
public import Homogenization.Book.Ch02.MultiscaleEllipticity
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SubdiffusiveProcess.Paper

/--
Tick list for G3 bounded carrier-definition rewrite.

1. `d`, `NeZero d`, the standard continuous-field measurable/Borel instances,
   `I : SubdiffusiveProcess.Paper.in_J d`, `M`, `H`, `InfraredCharacterization M H`, and the
   probability measure `P = (chaosSampleLaw M).toMeasure` are fixed first.
2. `k`, `z`, `qcenter = z`, and the scale convention `3^(-(k:Int))` are fixed.
3. `Roots` is exactly `Enl × Shift`; `selfE`, `selfShift`, `factor`, and
   `shift` pin root levels, sides, centres, and the actual centred cubes; the
   root catalogue is inhabited by the two self indices.
4. Every comparison cube is an actual catalogue descendant, with its parent,
   depth, word, centre, integer level, side, and chosen member all pinned.
5. Observation centres are exactly descendant centres plus finite reference-root
   centres, indexed by `((Fin D -> OddGridIndex d 1) ⊕ Roots)`; there is no free
   finite set and no empty-root convention.
6. `eta` is the exact common-scale relabelling and `F`, `Praw`, `Rraw`, `Draw`,
   `Z`, and `rawGood` carry `primitive_scores` almost surely for every cutoff;
   these are the exact raw formulas, not arbitrary score arrays.
7. The thresholds, coarse-order parameter, ellipticity threshold,
   homogenization tolerance, and deterministic comparison constant
   are fixed with their displayed strict ranges.
8. Finite prefixes use the actual observation centre, the exact integer interval
   and physical index `(N:Int)-j`, with zero for invalid initial cutoffs and no
   negative physical index passed to a raw score; the finite-score guard is only
   on the actual countable catalogue indices and is almost sure for all `N`.
9. The reference scalar is the exact `kappa` normalization with the signed
   finite-sum extension at every integer level and centre; it is one only for
   the finitely many invalid initial values `N < l`, and agrees with the
   `coherent_score_attachment`/`reference_coefficients` convention at `k >= 0`.
10. `ellLoN`, `ellHiN`, `AEN`, `errN`, and `ratioN` are tied literally to the
    actual normalized cutoff coefficient, including `H`, `I.lam`, `I.Lam`,
    `I.chart`, `TriadicCoeffFamily.coeffOn`, Ch02 `sigmaCoarse`, and `I.err`.
11. One strictly monotone `phi` is used for every finite quantity. Every limit
    array is pinned by `TendstoInMeasure` of its exact finite array along that
    common subsequence, with matrix convergence entrywise; this is the supplied
    `lem_prefix_limit` version choice, not a new probability estimate.
12. The body is exactly the candidate event: strict limiting prefix bounds,
    the two-sided ellipticity bounds, the chosen comparison error bound, and all comparison
    ratios in the open interval `(1/2,2)` (strictly inside the range consumed by the
    deterministic estimates, ). No Holder, trace, harmonic, witness, or other event
    regularity conclusion is assumed here.
-/
def candidate_good_event
    (d : ℕ) (_hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (_hMH : InfraredCharacterization M H)
    (k : ℕ) (z : SpatialCoordinates d)
    (qside : ℝ)
    (_hqside : qside = (3 : ℝ) ^ (-(k : ℤ)))
    (qcenter : SpatialCoordinates d)
    (_hqcenter : qcenter = z)
    (Enl Shift Cmp : Type)
    [Fintype Enl] [Fintype Shift] [Fintype Cmp]
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
    (_hGridCover : ∀ (x : SpatialCoordinates d), x ∈ Metric.closedBall z (qside / 2) →
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
    (_hcmpCentre : ∀ (c : Cmp),
      cmpCentre c =
        descendantCenter 1 (rootCentre (parent c)) (rootSide (parent c))
          (depth c) (word c))
    (cmpLevel : Cmp → ℤ)
    (_hcmpLevel : ∀ (c : Cmp),
      cmpLevel c = rootLevel (parent c) + (depth c : ℤ))
    (cmpSide : Cmp → ℝ)
    (_hcmpSide : ∀ (c : Cmp), cmpSide c = (3 : ℝ) ^ (-cmpLevel c))
    (cmpPos : ∀ (c : Cmp), 0 < cmpSide c)
    (chosen : Cmp)
    (observationCentre :
      ∀ (_U : Enl × Shift) (D : ℕ),
        ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
          SpatialCoordinates d)
    (_hObservationCentre : ∀ (U : Enl × Shift) (D : ℕ)
      (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
      observationCentre U D code =
        Sum.elim
          (fun w => descendantCenter 1 (rootCentre U) (rootSide U) D w)
          (fun V => rootCentre V) code)
    (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (_hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d),
        eta N omega i y =
          omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
    (s eps : ℝ)
    (_hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (_heps : eps ∈ Set.Ioo (0 : ℝ) 1)
    (_hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
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
    (_hThresholds :
      0 < lambdaCut ∧ lambdaCut < lambdaLim ∧
      lambdaLim < lambdaDet ∧ lambdaDet < 1)
    (_hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (_hcell : cell ∈ Set.Ioo (0 : ℝ) 1)
    (_hepshom : 0 < epshom)
    (_hcdet : 0 < cdet)
    (prefixZ : ∀ (_N : ℕ) (_U : Enl × Shift) (D : ℕ),
      ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
        BilateralField d → ℝ)
    (prefixD : ∀ (_N : ℕ) (_U : Enl × Shift) (D : ℕ),
      ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
        BilateralField d → ℝ)
    (_hPrefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
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
    (_hPrefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
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
    (_hFiniteScoreGuard : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
        (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
        rootLevel U + (D : ℤ) ≤ (N : ℤ) →
        ∀ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
          (rootLevel U + (D : ℤ)),
          Draw N ((N : ℤ) - j).toNat
            (((3 : ℝ) ^ N) • observationCentre U D code) omega ≠ ⊤)
    (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
    (_hsN : ∀ (N : ℕ) (l : ℤ) (w : SpatialCoordinates d)
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
    (errN ratioN : ℕ → Cmp → BilateralField d → ℝ)
    (_hErrN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
      errN N c omega =
        I.err (cmpCentre c) (cmpSide c) (cmpPos c)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
            (cmpCentre c) (cmpPos c))
          (cmpCentre c) (cmpSide c)
          (sN N (cmpLevel c) (cmpCentre c) omega) s 2)
    (_hRatioN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
      ratioN N c omega =
        sN N (k : ℤ) qcenter omega /
          sN N (cmpLevel c) (cmpCentre c) omega)
    (phi : ℕ → ℕ)
    (_hphi : StrictMono phi)
    (prefixZLim : ∀ (_U : Enl × Shift) (D : ℕ),
      ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
        BilateralField d → ℝ)
    (prefixDLim : ∀ (_U : Enl × Shift) (D : ℕ),
      ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
        BilateralField d → ℝ)
    (ellLoLim ellHiLim : (Enl × Shift) → BilateralField d → ℝ)
    (AE_Lim : (Enl × Shift) → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
    (errLim ratioLim : Cmp → BilateralField d → ℝ)
    (_hPrefixZLim : ∀ (U : Enl × Shift) (D : ℕ)
      (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
      TendstoInMeasure (chaosSampleLaw M).toMeasure
        (fun n omega => prefixZ (phi n) U D code omega) atTop
        (prefixZLim U D code))
    (_hPrefixDLim : ∀ (U : Enl × Shift) (D : ℕ)
      (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
      TendstoInMeasure (chaosSampleLaw M).toMeasure
        (fun n omega => prefixD (phi n) U D code omega) atTop
        (prefixDLim U D code))
    (_hEllLoLim : ∀ (U : Enl × Shift),
      TendstoInMeasure (chaosSampleLaw M).toMeasure
        (fun n omega => ellLoN (phi n) U omega) atTop (ellLoLim U))
    (_hEllHiLim : ∀ (U : Enl × Shift),
      TendstoInMeasure (chaosSampleLaw M).toMeasure
        (fun n omega => ellHiN (phi n) U omega) atTop (ellHiLim U))
    (_hAELim : ∀ (U : Enl × Shift) (i j : Fin d),
      TendstoInMeasure (chaosSampleLaw M).toMeasure
        (fun n omega => AEN (phi n) U omega i j) atTop
        (fun omega => AE_Lim U omega i j))
    (_hErrLim : ∀ (c : Cmp),
      TendstoInMeasure (chaosSampleLaw M).toMeasure
        (fun n omega => errN (phi n) c omega) atTop (errLim c))
    (_hRatioLim : ∀ (c : Cmp),
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

end SubdiffusiveProcess.Paper
