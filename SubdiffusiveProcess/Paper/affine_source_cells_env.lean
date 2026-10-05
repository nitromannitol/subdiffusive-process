module

public import SubdiffusiveProcess.Paper.lem_affine
public import SubdiffusiveProcess.EllipticRegularity.GoodCellCatalogue
public import SubdiffusiveProcess.ResponseMoments.ShiftedRootCover
public import SubdiffusiveProcess.Lnorm.CutoffVolumeResponseMeasurability
public import SubdiffusiveProcess.Paper.limit_form_energy_measure_unique
public import SubdiffusiveProcess.Paper.represented_same_law_in_measure
public import Mathlib.Tactic

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

/-! # Affine source-cell estimates for changing represented environments.
The local estimate is applied to the actual environments at each cutoff.
Original-space limit arrays are transported through their common law.
This is an internal consumer: the catalogue, normalization subsequence and array
limits are supplied explicitly; it is not a uniqueness or actual-model export. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The convergence-in-measure clauses of `gcat_prefix_limits` (conjuncts 5-11: `Z`, `D` prefixes, `λ/s`, `Λ/s`,
the normalized coarse matrices, the comparison error and ratio) for ONE cell (level `k`, centre `z`), verbatim,
along the cutoff sequence `phi`. -/
def aux_affine_source_cells_env_cellArrays {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (s sigma : ℝ) (gH cbuf : ℕ)
    (Z : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → ℝ)
    (Draw : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → ENNReal) (phi : ℕ → ℕ)
    (k : ℕ) (z : SpatialCoordinates d)
    (ZLim DLim : ∀ (_U : Fin 3 × (Fin d → Fin 3)) (D : ℕ),
      ((Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) → BilateralField d → ℝ)
    (loLim hiLim : (Fin 3 × (Fin d → Fin 3)) → BilateralField d → ℝ)
    (AELim : (Fin 3 × (Fin d → Fin 3)) → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
    (errLim ratioLim : Unit → BilateralField d → ℝ) : Prop :=
  (∀ U D code, TendstoInMeasure (chaosSampleLaw M).toMeasure
    (fun n omega => gcat_prefix gH cbuf k z Z (phi n) U D code omega) atTop
    (ZLim U D code)) ∧
  (∀ U D code, TendstoInMeasure (chaosSampleLaw M).toMeasure
    (fun n omega => gcat_prefix gH cbuf k z (fun N m w om => (Draw N m w om).toReal)
      (phi n) U D code omega) atTop (DLim U D code)) ∧
  (∀ U, TendstoInMeasure (chaosSampleLaw M).toMeasure
    (fun n omega =>
      I.lam (gcat_rootCentre gH k z U) (gcat_rootSide gH k U) (zpow_pos (by norm_num) _)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (phi n) (gcat_rootCentre gH k z U)
          (zpow_pos (by norm_num) _))
        (gcat_rootCentre gH k z U) (gcat_rootSide gH k U) sigma 2 /
      gcat_sN M H (phi n) (gcat_rootLevel gH k U) (gcat_rootCentre gH k z U) omega)
    atTop (loLim U)) ∧
  (∀ U, TendstoInMeasure (chaosSampleLaw M).toMeasure
    (fun n omega =>
      I.Lam (gcat_rootCentre gH k z U) (gcat_rootSide gH k U) (zpow_pos (by norm_num) _)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (phi n) (gcat_rootCentre gH k z U)
          (zpow_pos (by norm_num) _))
        (gcat_rootCentre gH k z U) (gcat_rootSide gH k U) sigma 2 /
      gcat_sN M H (phi n) (gcat_rootLevel gH k U) (gcat_rootCentre gH k z U) omega)
    atTop (hiLim U)) ∧
  (∀ U (i j : Fin d), TendstoInMeasure (chaosSampleLaw M).toMeasure
    (fun n omega =>
      ((gcat_sN M H (phi n) (gcat_rootLevel gH k U) (gcat_rootCentre gH k z U) omega)⁻¹ •
        Homogenization.Book.Ch02.sigmaCoarse
          (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
          ((I.chart (gcat_rootCentre gH k z U) (gcat_rootSide gH k U) (zpow_pos (by norm_num) _)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (phi n) (gcat_rootCentre gH k z U)
              (zpow_pos (by norm_num) _))
            (gcat_rootCentre gH k z U) (gcat_rootSide gH k U)).coeffOn
            (Homogenization.originCube d 0))) i j)
    atTop (fun omega => AELim U omega i j)) ∧
  TendstoInMeasure (chaosSampleLaw M).toMeasure
    (fun n omega =>
      I.err z ((3 : ℝ) ^ (-((k : ℤ) - (gH : ℤ)))) (zpow_pos (by norm_num) _)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega (phi n) z (zpow_pos (by norm_num) _))
        z ((3 : ℝ) ^ (-((k : ℤ) - (gH : ℤ))))
        (gcat_sN M H (phi n) ((k : ℤ) - (gH : ℤ)) z omega) s 2)
    atTop (errLim ()) ∧
  TendstoInMeasure (chaosSampleLaw M).toMeasure
    (fun n omega => gcat_sN M H (phi n) (k : ℤ) z omega /
      gcat_sN M H (phi n) ((k : ℤ) - (gH : ℤ)) z omega)
    atTop (ratioLim ())

/-- The cell-indexed form (exactly the `gcat_prefix_limits` output, conjuncts 5-11, for every cell). -/
def aux_affine_source_cells_env_arrays {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (s sigma : ℝ) (gH cbuf : ℕ)
    (Z : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → ℝ)
    (Draw : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → ENNReal) (phi : ℕ → ℕ)
    {Cells : Type} (cellLevel : Cells → ℕ) (cellCentre : Cells → SpatialCoordinates d)
    (ZLim DLim : Cells → ∀ (_U : Fin 3 × (Fin d → Fin 3)) (D : ℕ),
      ((Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) → BilateralField d → ℝ)
    (loLim hiLim : Cells → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → ℝ)
    (AELim : Cells → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
    (errLim ratioLim : Cells → Unit → BilateralField d → ℝ) : Prop :=
  ∀ c : Cells, aux_affine_source_cells_env_cellArrays I M H s sigma gH cbuf Z Draw phi
    (cellLevel c) (cellCentre c) (ZLim c) (DLim c) (loLim c) (hiLim c) (AELim c) (errLim c)
    (ratioLim c)

theorem aux_affine_source_cells_env_cellArrays_congr {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (s sigma : ℝ) (gH cbuf : ℕ)
    (Z : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → ℝ)
    (Draw : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → ENNReal) (phi : ℕ → ℕ)
    {k k' : ℕ} {z z' : SpatialCoordinates d} (hk : k = k') (hz : z = z')
    (ZLim DLim : ∀ (_U : Fin 3 × (Fin d → Fin 3)) (D : ℕ),
      ((Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) → BilateralField d → ℝ)
    (loLim hiLim : (Fin 3 × (Fin d → Fin 3)) → BilateralField d → ℝ)
    (AELim : (Fin 3 × (Fin d → Fin 3)) → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
    (errLim ratioLim : Unit → BilateralField d → ℝ)
    (h : aux_affine_source_cells_env_cellArrays I M H s sigma gH cbuf Z Draw phi k z
      ZLim DLim loLim hiLim AELim errLim ratioLim) :
    aux_affine_source_cells_env_cellArrays I M H s sigma gH cbuf Z Draw phi k' z'
      ZLim DLim loLim hiLim AELim errLim ratioLim := by
  subst hk
  subst hz
  exact h


/-- The per-cell part of `lem_affine`'s statement (everything after `∃ baseMesh`), with the actual single represented side `env` in place of the redundant
`PUnit` side index. Cutoff objects use `env n`; limiting objects use `field`. -/
def aux_affine_source_cells_env_LAcell {d : ℕ} (_hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (field : Ω → BilateralField d)
    (env : ℕ → Ω → BilateralField d)
    (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
    (GE : Ω → DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
      DomainL2 (centeredCube Qcentre Qside hQside))
    (E : Ω → _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
    (GammaE : ∀ omega : Ω, _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure (E omega))
    (phi : ℕ → ℕ)
    (alpha gamma zeta rho s sigma cell : ℝ) (cbuf k0 H1 : ℕ)
    (epshom Cbound eps0 lam0 : ℝ) (eRef : ℕ → ℝ)
    (Grid : Type) (origin : Grid → SpatialCoordinates d)
    (c : ℝ) (J : ℕ) (gridChoice : Fin J → Grid)
    (baseMesh : Ω → (SpatialCoordinates d → ℝ) → ℝ) : Prop :=
  let Q : Opens (SpatialCoordinates d) := centeredCube Qcentre Qside hQside
  let L : ℝ := (3 : ℝ) ^ H1
  let origins : Fin J → SpatialCoordinates d := fun j => origin (gridChoice j)
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
                (_hGridCover : ∀ (x : SpatialCoordinates d),
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
                (_hcmpCentre : ∀ (c : Cmp),
                  cmpCentre c =
                    descendantCenter 1 (rootCentre (parent c))
                      (rootSide (parent c)) (depth c) (word c))
                (cmpLevel : Cmp → ℤ)
                (_hcmpLevel : ∀ (c : Cmp),
                  cmpLevel c = rootLevel (parent c) + (depth c : ℤ))
                (cmpSide : Cmp → ℝ)
                (_hcmpSide : ∀ (c : Cmp),
                  cmpSide c = (3 : ℝ) ^ (-cmpLevel c))
                (cmpPos : ∀ (c : Cmp), 0 < cmpSide c)
                (chosen : Cmp)
                (_hcmpChosenCentre : cmpCentre chosen = z)
                (_hcmpChosenLevel : cmpLevel chosen =
                  (k : ℤ) - (Nat.floor (gamma * (H1 : ℝ)) : ℤ) - 4)
                (_hcmpChosenPad : Metric.closedBall z (cmpSide chosen / 2) ⊆
                  parentCell)
                (observationCentre :
                  ∀ (_U : Enl × Shift) (D : ℕ),
                    ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
                      SpatialCoordinates d)
                (_hObservationCentre : ∀ (U : Enl × Shift) (D : ℕ)
                  (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
                  observationCentre U D code =
                    Sum.elim
                      (fun w => descendantCenter 1 (rootCentre U)
                        (rootSide U) D w)
                      (fun V => rootCentre V) code)
                (eta : ℕ → BilateralField d →
                  _root_.SubdiffusiveProcess.Model.PotentialSample d)
                (_hEta : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                  ∀ (N i : ℕ) (y : Vec d),
                    eta N omega i y =
                      omega ((i : ℤ) - (N : ℤ))
                        (((3 : ℝ) ^ (-(N : ℤ))) • y)))
                (F Praw Rraw Draw :
                  ℕ → ℕ → Vec d → BilateralField d → ENNReal)
                (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
                (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
                (eps : ℝ) (_heps : eps ∈ Set.Ioo (0 : ℝ) 1)
                (_hepsSmall : eps ≤ eps0)
                (_hPrimitive : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                  ∀ N : ℕ,
                    primitive_scores d M s eps (eta N omega)
                      (fun m y => F N m y omega)
                      (fun m y => Praw N m y omega)
                      (fun m y => Rraw N m y omega)
                      (fun m y => Draw N m y omega)
                      (fun m y => Z N m y omega)
                      (fun m y => rawGood N m y omega)))
                (lambdaCut lambdaLim lambdaDet cdet : ℝ)
                (_hThresholds :
                  0 < lambdaCut ∧ lambdaCut < lambdaLim ∧
                  lambdaLim < lambdaDet ∧ lambdaDet < 1)
                (_hcdet : 0 < cdet) (_hcdetSmall : cdet ≤ Cbound⁻¹)
                (_hlamSmall : lambdaDet ≤ lam0)
                (prefixZ : ∀ (_N : ℕ) (_U : Enl × Shift) (D : ℕ),
                  ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
                    BilateralField d → ℝ)
                (prefixD : ∀ (_N : ℕ) (_U : Enl × Shift) (D : ℕ),
                  ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
                    BilateralField d → ℝ)
                (_hPrefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
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
                (_hPrefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
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
                (_hFiniteScoreGuard :
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
                (_hsN : ∀ (N : ℕ) (l : ℤ) (w : SpatialCoordinates d)
                  (omega : BilateralField d),
                  sN N l w omega =
                    if l ≤ (N : ℤ) then
                      (let kappa : ℕ → ℝ := fun J =>
                        Real.exp (((J : ℝ) + 1) *
                          _root_.SubdiffusiveProcess.Model.tauSq M.P) *
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
                (_hEllLoN : ∀ (N : ℕ) (U : Enl × Shift)
                  (omega : BilateralField d),
                  ellLoN N U omega =
                    I.lam (rootCentre U) (rootSide U) (rootPos U)
                      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient
                        M H omega N (rootCentre U) (rootPos U))
                      (rootCentre U) (rootSide U) sigma 2 /
                      sN N (rootLevel U) (rootCentre U) omega)
                (_hEllHiN : ∀ (N : ℕ) (U : Enl × Shift)
                  (omega : BilateralField d),
                  ellHiN N U omega =
                    I.Lam (rootCentre U) (rootSide U) (rootPos U)
                      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient
                        M H omega N (rootCentre U) (rootPos U))
                      (rootCentre U) (rootSide U) sigma 2 /
                      sN N (rootLevel U) (rootCentre U) omega)
                (AEN : ℕ → Enl × Shift → BilateralField d →
                  Matrix (Fin d) (Fin d) ℝ)
                (_hAEN : ∀ (N : ℕ) (U : Enl × Shift)
                  (omega : BilateralField d),
                  AEN N U omega =
                    (sN N (rootLevel U) (rootCentre U) omega)⁻¹ •
                      Homogenization.Book.Ch02.sigmaCoarse
                        (Homogenization.Book.Ch02.cubeDomain
                          (Homogenization.originCube d 0))
                        ((I.chart (rootCentre U) (rootSide U) (rootPos U)
                          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient
                            M H omega N (rootCentre U) (rootPos U))
                          (rootCentre U) (rootSide U)).coeffOn
                          (Homogenization.originCube d 0)))
                (errN ratioN : ℕ → Cmp → BilateralField d → ℝ)
                (_hErrN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
                  errN N c omega =
                    I.err (cmpCentre c) (cmpSide c) (cmpPos c)
                      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient
                        M H omega N (cmpCentre c) (cmpPos c))
                      (cmpCentre c) (cmpSide c)
                      (sN N (cmpLevel c) (cmpCentre c) omega) s 2)
                (_hRatioN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
                  ratioN N c omega =
                    sN N (k : ℤ) qcenter omega /
                      sN N (cmpLevel c) (cmpCentre c) omega)
                (sE : Ω → ℝ)
                (sCmp : Cmp → Ω → ℝ)
                (_hsE : (∀ᵐ omega ∂P,
                    0 < sE omega ∧
                    Tendsto (fun n => sN (phi n) (k : ℤ) z (env n omega))
                      atTop (𝓝 (sE omega))) ∧
                  (∀ᵐ omega ∂P,
                    sE omega = eRef k *
                      Real.exp (H (field omega) z +
                        ∑ j ∈ Finset.range k, (field omega) (-(j : ℤ)) z)))
                (_hsCmp : ∀ᵐ omega ∂P,
                  ∀ c' : Cmp,
                    0 < sCmp c' omega ∧
                    Tendsto
                      (fun n => sN (phi n) (cmpLevel c') (cmpCentre c')
                        (env n omega))
                      atTop (𝓝 (sCmp c' omega)))
                (prefixZLim : ∀ (_U : Enl × Shift) (D : ℕ),
                  ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) → Ω → ℝ)
                (prefixDLim : ∀ (_U : Enl × Shift) (D : ℕ),
                  ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) → Ω → ℝ)
                (ellLoLim ellHiLim : (Enl × Shift) → Ω → ℝ)
                (AE_Lim : (Enl × Shift) → Ω → Matrix (Fin d) (Fin d) ℝ)
                (errLim ratioLim : Cmp → Ω → ℝ)
                (_hPrefixZLim : ∀ (U : Enl × Shift) (D : ℕ)
                  (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
                  TendstoInMeasure P
                    (fun n omega =>
                      prefixZ (phi n) U D code (env n omega))
                    atTop (prefixZLim U D code))
                (_hPrefixDLim : ∀ (U : Enl × Shift) (D : ℕ)
                  (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
                  TendstoInMeasure P
                    (fun n omega =>
                      prefixD (phi n) U D code (env n omega))
                    atTop (prefixDLim U D code))
                (_hEllLoLim : ∀ (U : Enl × Shift),
                  TendstoInMeasure P
                    (fun n omega => ellLoN (phi n) U (env n omega)) atTop
                    (ellLoLim U))
                (_hEllHiLim : ∀ (U : Enl × Shift),
                  TendstoInMeasure P
                    (fun n omega => ellHiN (phi n) U (env n omega)) atTop
                    (ellHiLim U))
                (_hAELim : ∀ (U : Enl × Shift) (i j : Fin d),
                  TendstoInMeasure P
                    (fun n omega => AEN (phi n) U (env n omega) i j) atTop
                    (fun omega => AE_Lim U omega i j))
                (_hErrLim : ∀ (c : Cmp),
                  TendstoInMeasure P
                    (fun n omega => errN (phi n) c (env n omega)) atTop
                    (errLim c))
                (_hRatioLim : ∀ (c : Cmp),
                  TendstoInMeasure P
                    (fun n omega => ratioN (phi n) c (env n omega)) atTop
                    (ratioLim c))
                (_hRootsQ : ∀ U : Enl × Shift,
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
                         _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (closure q) U ∧
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


theorem aux_affine_source_cells_env_sum_eq {β : Type*} [AddCommMonoid β] (l : ℕ)
    (f : ℤ → β) :
    ∑ j ∈ Finset.range l, f (j : ℤ) = ∑ j ∈ Finset.Ico (0 : ℤ) (l : ℤ), f j := by
  refine Finset.sum_nbij (fun j : ℕ => (j : ℤ)) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_range] at ha
    simp only [Finset.mem_Ico]
    omega
  · intro a _ b _ h
    exact Nat.cast_injective h
  · intro b hb
    simp only [Finset.mem_coe, Finset.mem_Ico] at hb
    refine ⟨b.toNat, ?_, ?_⟩
    · simp only [Finset.mem_coe, Finset.mem_range]
      omega
    · show ((b.toNat : ℕ) : ℤ) = b
      omega
  · intro a _
    rfl

/-- The reference scalar at a nonnegative level converges along the cutoffs (varying environment). -/
theorem aux_affine_source_cells_env_sN_tendsto {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (eRef : ℕ → ℝ)
    (heRefLim : ∀ k : ℕ,
      Tendsto (fun n : ℕ =>
        (let kappa : ℕ → ℝ := fun J =>
           Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
             SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
         kappa (((phi n : ℤ) - (k : ℤ)).toNat) / kappa (phi n)))
        atTop (𝓝 (eRef k)))
    (l : ℕ) (w : SpatialCoordinates d) (beta : ℕ → BilateralField d)
    (beta0 : BilateralField d) (hbeta : Tendsto beta atTop (𝓝 beta0))
    (hH : Tendsto (fun n => H (beta n) w) atTop (𝓝 (H beta0 w))) :
    Tendsto (fun n => gcat_sN M H (phi n) (l : ℤ) w (beta n)) atTop
      (𝓝 (eRef l * Real.exp (H beta0 w + ∑ j ∈ Finset.range l, beta0 (-(j : ℤ)) w))) := by
  have hev : ∀ᶠ n in atTop, gcat_sN M H (phi n) (l : ℤ) w (beta n) =
      (let kappa : ℕ → ℝ := fun J =>
          Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
       kappa (((phi n : ℤ) - (l : ℤ)).toNat) / kappa (phi n)) *
        Real.exp (H (beta n) w + ∑ j ∈ Finset.range l, (beta n) (-(j : ℤ)) w) := by
    filter_upwards [eventually_ge_atTop l] with n hn
    have hle : (l : ℤ) ≤ (phi n : ℤ) := by
      have h1 : n ≤ phi n := hphi.id_le n
      omega
    have hret : (if 0 ≤ (l : ℤ) then ∑ j ∈ Finset.Ico (0 : ℤ) (l : ℤ), (beta n) (-j) w
        else -∑ j ∈ Finset.Ico (l : ℤ) 0, (beta n) (-j) w) =
        ∑ j ∈ Finset.range l, (beta n) (-(j : ℤ)) w := by
      rw [ite_eq_left (by positivity)]
      exact (aux_affine_source_cells_env_sum_eq l (fun j => (beta n) (-j) w)).symm
    unfold gcat_sN
    rw [ite_eq_left hle]
    simp only [hret]
  have hsum : Tendsto (fun n => ∑ j ∈ Finset.range l, (beta n) (-(j : ℤ)) w)
      atTop (𝓝 (∑ j ∈ Finset.range l, beta0 (-(j : ℤ)) w)) := by
    apply tendsto_finsetSum
    intro j hj
    exact (((continuous_eval_const w).comp (continuous_apply (-(j : ℤ)))).tendsto beta0).comp hbeta
  exact ((heRefLim l).mul ((Real.continuous_exp.tendsto _).comp (hH.add hsum))).congr' (hev.mono fun n hn => hn.symm)

/-- The `gcat` factor of the concentric or tripled root. -/
theorem aux_affine_source_cells_env_factor_castSucc (gH : ℕ) (e : Fin 2) :
    gcat_factor gH (Fin.castSucc e) = e.val := by
  fin_cases e <;> rfl

/-- The finite root catalogue covers: `shifted_root_grid_cover` in `gcat` form. -/
theorem aux_affine_source_cells_env_gridCover {d : ℕ} (gH k : ℕ)
    (z : SpatialCoordinates d) :
    ∀ (x : SpatialCoordinates d), x ∈ Metric.closedBall z ((3 : ℝ) ^ (-(k : ℤ)) / 2) →
      ∀ rho : ℝ, 0 < rho → rho ≤ (3 : ℝ) ^ (-(k : ℤ)) →
        ∃ (U : Fin 3 × (Fin d → Fin 3)) (D : ℕ) (w : Fin D → OddGridIndex d 1),
          Metric.ball x (rho / 2) ⊆
            Metric.ball (descendantCenter 1 (gcat_rootCentre gH k z U) (gcat_rootSide gH k U) D w)
              (descendantSide 1 D (gcat_rootSide gH k U) / 2) ∧
          descendantSide 1 D (gcat_rootSide gH k U) ≤ 9 * rho := by
  intro x hx rho hrho hrho1
  obtain ⟨e, t, D, w, hsub, hle⟩ := shifted_root_grid_cover k z x hx rho hrho hrho1
  refine ⟨(Fin.castSucc e, t), D, w, ?_, ?_⟩
  · have hside : gcat_rootSide gH k (Fin.castSucc e, t) =
        (3 : ℝ) ^ (-((k : ℤ) - (e.val : ℤ))) := by
      simp only [gcat_rootSide, gcat_rootLevel, aux_affine_source_cells_env_factor_castSucc]
    have hcen : gcat_rootCentre gH k z (Fin.castSucc e, t) =
        z + (3 : ℝ) ^ (-((k : ℤ) - (e.val : ℤ))) • shiftedRootShift d t := by
      rw [gcat_rootCentre, hside]
      rfl
    rw [hcen, hside]
    exact hsub
  · have hside : gcat_rootSide gH k (Fin.castSucc e, t) =
        (3 : ℝ) ^ (-((k : ℤ) - (e.val : ℤ))) := by
      simp only [gcat_rootSide, gcat_rootLevel, aux_affine_source_cells_env_factor_castSucc]
    rw [hside]
    exact hle

/-- Algebra of the rational reduction of the source parameter `c`. -/
theorem aux_affine_source_cells_env_c_reduction (gP gQ vP vQ Ld Lz c q rho Lam : ℝ)
    (hgQ : 0 ≤ gQ) (hvQ : 0 ≤ vQ) (hcq : c ≤ q) (hq2 : q ≤ 2 * c) (hrho : 0 ≤ rho)
    (hv : vP = Ld * vQ) (hLd : Ld ≤ Lz)
    (hpar : gP + c * vP ≤ Lz * (gQ + c * vQ)) (hlam : Lam ≤ rho * (gQ + q * vQ)) :
    gP + q * vP ≤ Lz * (gQ + q * vQ) ∧ Lam ≤ (2 * rho) * (gQ + c * vQ) := by
  constructor
  · have h1 : (q - c) * vP ≤ (q - c) * (Lz * vQ) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      rw [hv]
      exact mul_le_mul_of_nonneg_right hLd hvQ
    nlinarith
  · have h2 : gQ + q * vQ ≤ 2 * (gQ + c * vQ) := by nlinarith
    calc Lam ≤ rho * (gQ + q * vQ) := hlam
      _ ≤ rho * (2 * (gQ + c * vQ)) := mul_le_mul_of_nonneg_left h2 hrho
      _ = (2 * rho) * (gQ + c * vQ) := by ring


theorem aux_affine_source_cells_env_shift_one {d : ℕ} :
    gcat_shift (d := d) (fun _ => (1 : Fin 3)) = 0 := by
  funext i
  simp [gcat_shift]

theorem aux_affine_source_cells_env_chosen_centre {d : ℕ} (gH k : ℕ)
    (z : SpatialCoordinates d) (W : Fin 0 → OddGridIndex d 1) :
    descendantCenter 1 (gcat_rootCentre gH k z ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3)))
      (gcat_rootSide gH k ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3))) 0 W = z := by
  show gcat_rootCentre gH k z ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3)) = z
  rw [gcat_rootCentre]
  show z + gcat_rootSide gH k ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3)) •
    gcat_shift (d := d) (fun _ => (1 : Fin 3)) = z
  rw [aux_affine_source_cells_env_shift_one, smul_zero, add_zero]

theorem aux_affine_source_cells_env_chosen_level {d : ℕ} (gH k : ℕ) :
    gcat_rootLevel (d := d) gH k ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3)) =
      (k : ℤ) - (gH : ℤ) := by
  simp [gcat_rootLevel, gcat_factor]


/-- The comparison error only depends on the (equal) centre and side: `subst` lemma for `in_J.err`. -/
theorem aux_affine_source_cells_env_err_congr {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ) (omega : BilateralField d)
    (z1 z2 : SpatialCoordinates d) (r1 r2 : ℝ) (h1 : 0 < r1) (h2 : 0 < r2) (a0 s : ℝ)
    (hz : z1 = z2) (hr : r1 = r2) :
    I.err z1 r1 h1 (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z1 h1) z1 r1 a0 s 2 =
      I.err z2 r2 h2 (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z2 h2) z2 r2 a0 s 2 := by
  subst hz
  subst hr
  rfl

theorem aux_affine_source_cells_env_chosen_level_nat {d : ℕ} (gH k : ℕ) (h : gH ≤ k) :
    gcat_rootLevel (d := d) gH k ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3)) + ((0 : ℕ) : ℤ) =
      ((k - gH : ℕ) : ℤ) := by
  rw [aux_affine_source_cells_env_chosen_level, Nat.cast_zero, add_zero]
  omega



/-- The conclusion of the per-cell instance at one sample `omega`. -/
def aux_affine_source_cells_env_InstConcl {d : ℕ} (Qcentre : SpatialCoordinates d)
    (Qside : ℝ) (hQside : 0 < Qside) {Ω : Type} (field : Ω → BilateralField d)
    (GE : Ω → DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
      DomainL2 (centeredCube Qcentre Qside hQside))
    (E : Ω → _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
    (GammaE : ∀ omega : Ω, _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure (E omega))
    (baseMesh : Ω → (SpatialCoordinates d → ℝ) → ℝ) (c rho zeta : ℝ) (H1 n : ℕ)
    (z zP : SpatialCoordinates d) (k0 : ℕ) (lambdaLim cell epshom cdet : ℝ)
    (ZL DL : ∀ (_U : Fin 3 × (Fin d → Fin 3)) (D : ℕ),
      ((Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) → BilateralField d → ℝ)
    (loL hiL : (Fin 3 × (Fin d → Fin 3)) → BilateralField d → ℝ)
    (errL ratL : Unit → BilateralField d → ℝ) (omega : Ω) : Prop :=
    ∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
      ∀ (fL2 : DomainL2 (centeredCube Qcentre Qside hQside)),
        ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] f) →
        ∃ U : SpatialCoordinates d → ℝ,
          ContinuousOn U (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ∧
          ((GE omega fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] U) ∧
          ((3 : ℝ) ^ (-((H1 * (n + 1) : ℕ) : ℤ)) ≤ baseMesh omega f →
           field omega ∈ gcat_good k0 lambdaLim cell epshom cdet ZL DL loL hiL errL ratL →
           (let lambda : Set (SpatialCoordinates d) → ℝ :=
              fun A => (((GammaE omega).measure (GE omega fL2)) A).toReal + c * (volume A).toReal
            lambda (Metric.ball zP ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-((H1 * (n + 1) : ℕ) : ℤ)) / 2)) ≤
              ((3 : ℝ) ^ H1) ^ ((d : ℝ) + zeta) *
                lambda (Metric.ball z ((3 : ℝ) ^ (-((H1 * (n + 1) : ℕ) : ℤ)) / 2)) →
            ∃ pc : (Fin d → ℝ) × ℝ,
              (let b : SpatialCoordinates d → ℝ :=
                 fun x => U x - ((∑ i, pc.1 i * x i) + pc.2)
               let eSet : Set ℝ :=
                 {e : ℝ |
                   ∃ (v : DomainL2 (centeredCube Qcentre Qside hQside))
                     (V : SpatialCoordinates d → ℝ),
                     v ∈ (E omega).domain ∧
                     ContinuousOn V
                       (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ∧
                     ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                       (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] V) ∧
                     (∀ x ∈ frontier (Metric.ball z ((3 : ℝ) ^ (-((H1 * (n + 1) : ℕ) : ℤ)) / 2)),
                       V x = b x) ∧
                     e = (((GammaE omega).measure v)
                       (Metric.ball z ((3 : ℝ) ^ (-((H1 * (n + 1) : ℕ) : ℤ)) / 2))).toReal}
               ∃ Lambda : ℝ,
                 IsGLB eSet Lambda ∧ eSet.Nonempty ∧
                 Lambda ≤ rho * lambda (Metric.ball z
                   ((3 : ℝ) ^ (-((H1 * (n + 1) : ℕ) : ℤ)) / 2)))))

/-- **One cell of `lem_affine`, instantiated at the concrete good-cell catalogue.**  For the cell
`(n, gridIndex, parentIndex, idx)` with centre `z` and parent `zP`, apply the per-cell statement `hcell`
of `lem_affine` (varying environment) with `Enl := Fin 3` (factors `![0,1,gH]`), `Shift := Fin d → Fin 3`,
`Cmp := Unit`, the `gcat_*` roots, the comparison root of factor `gH`, the prefix / `sN` / `λ`, `Λ`, `A`,
error and ratio arrays of `gcat`, and the limit arrays transferred from the chaos law to `P` through `field`.
The conclusion keeps `U`, the continuity, the a.e. representation and the boundary approximation, with the
good event `field ω ∈ gcat_good …`. -/
theorem aux_affine_source_cells_env_inst {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (field : Ω → BilateralField d)
    (hfieldMeas : Measurable field) (hfieldLaw : Measure.map field P = (chaosSampleLaw M).toMeasure)
    (env : ℕ → Ω → BilateralField d) (hEnvMeas : ∀ n, Measurable (env n))
    (hEnvLaw : ∀ n, Measure.map (env n) P = (chaosSampleLaw M).toMeasure)
    (hEnvConv : ∀ᵐ omega ∂P, Tendsto (fun n => env n omega) atTop (𝓝 (field omega)))
    (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
    (GE : Ω → DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
      DomainL2 (centeredCube Qcentre Qside hQside))
    (E : Ω → _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
    (GammaE : ∀ omega : Ω, _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure (E omega))
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (alpha gamma zeta rho s sigma cell : ℝ) (cbuf k0 H1 : ℕ)
    (epshom Cbound eps0 lam0 : ℝ) (eRef : ℕ → ℝ)
    (heRefPos : ∀ k : ℕ, 0 < eRef k)
    (heRefLim : ∀ k : ℕ,
      Tendsto (fun n : ℕ =>
        (let kappa : ℕ → ℝ := fun J =>
           Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
             SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
         kappa (((phi n : ℤ) - (k : ℤ)).toNat) / kappa (phi n)))
        atTop (𝓝 (eRef k)))
    (Grid : Type) (origin : Grid → SpatialCoordinates d)
    (c : ℝ) (J : ℕ) (gridChoice : Fin J → Grid)
    (baseMesh : Ω → (SpatialCoordinates d → ℝ) → ℝ)
    (hcell : aux_affine_source_cells_env_LAcell hd I M H P field env Qcentre Qside hQside GE E
      GammaE phi alpha gamma zeta rho s sigma cell cbuf k0 H1 epshom Cbound eps0 lam0 eRef Grid
      origin c J gridChoice baseMesh)
    (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hEta : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Fin d → ℝ),
        eta N omega i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y)))
    (F Praw Rraw Draw : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → ℝ)
    (rawGood : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → Prop)
    (eps : ℝ) (heps : eps ∈ Set.Ioo (0 : ℝ) 1) (hepsSmall : eps ≤ eps0)
    (hPrimitive : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ N : ℕ,
        primitive_scores d M s eps (eta N omega)
          (fun m y => F N m y omega) (fun m y => Praw N m y omega)
          (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
          (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)))
    (lambdaCut lambdaLim lambdaDet cdet : ℝ)
    (hThresholds : 0 < lambdaCut ∧ lambdaCut < lambdaLim ∧ lambdaLim < lambdaDet ∧ lambdaDet < 1)
    (hcdet : 0 < cdet) (hcdetSmall : cdet ≤ Cbound⁻¹) (hlamSmall : lambdaDet ≤ lam0)
    (gH : ℕ) (hgH : gH = Nat.floor (gamma * (H1 : ℝ)) + 4) (hgHk : gH ≤ H1)
    (n : ℕ) (gi : Fin J) (pi : Fin d → ℤ) (idx : OddGridIndex d (subdivisionHalfWidth H1))
    (z zP : SpatialCoordinates d)
    (hIRConv : ∀ᵐ omega ∂P, Tendsto (fun n => H (env n omega) z) atTop (𝓝 (H (field omega) z)))
    (hzP : zP = fun i => origin (gridChoice gi) i +
      ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-((H1 * (n + 1) : ℕ) : ℤ))) * ((pi i : ℤ) : ℝ))
    (hz : z = oddGridCenter zP ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-((H1 * (n + 1) : ℕ) : ℤ)))
      (subdivisionHalfWidth H1) idx)
    (hpar : Metric.ball zP ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-((H1 * (n + 1) : ℕ) : ℤ)) / 2) ⊆
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
    (hpad : Metric.closedBall z ((3 : ℝ) ^ (-(((H1 * (n + 1) : ℕ) : ℤ) - (gH : ℤ))) / 2) ⊆
      Metric.ball zP ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-((H1 * (n + 1) : ℕ) : ℤ)) / 2))
    (hroots : ∀ U : Fin 3 × (Fin d → Fin 3),
      closure (centeredCube (gcat_rootCentre gH (H1 * (n + 1)) z U)
        (gcat_rootSide gH (H1 * (n + 1)) U) (zpow_pos (by norm_num) _) :
          Set (SpatialCoordinates d)) ⊆
        (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
    (hFinite : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N : ℕ) (U : Fin 3 × (Fin d → Fin 3)) (D : ℕ)
        (code : (Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))),
        gcat_rootLevel gH (H1 * (n + 1)) U + (D : ℤ) ≤ (N : ℤ) →
        ∀ j ∈ Finset.Icc (gcat_rootLevel gH (H1 * (n + 1)) U - (cbuf : ℤ))
          (gcat_rootLevel gH (H1 * (n + 1)) U + (D : ℤ)),
          Draw N ((N : ℤ) - j).toNat
            (((3 : ℝ) ^ N) • gcat_obsCentre gH (H1 * (n + 1)) z U D code) omega ≠ ⊤))
    (ZL DL : ∀ (_U : Fin 3 × (Fin d → Fin 3)) (D : ℕ),
      ((Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) → BilateralField d → ℝ)
    (loL hiL : (Fin 3 × (Fin d → Fin 3)) → BilateralField d → ℝ)
    (AEL : (Fin 3 × (Fin d → Fin 3)) → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
    (errL ratL : Unit → BilateralField d → ℝ)

    (hmeas : (∀ U D code, Measurable (ZL U D code) ∧ Measurable (DL U D code)) ∧
      (∀ U, Measurable (loL U) ∧ Measurable (hiL U) ∧
        ∀ i j, Measurable (fun omega => AEL U omega i j)) ∧
      Measurable (errL ()) ∧ Measurable (ratL ()))
    (harr : aux_affine_source_cells_env_cellArrays I M H s sigma gH cbuf Z Draw phi
      (H1 * (n + 1)) z ZL DL loL hiL AEL errL ratL) :
    ∀ᵐ omega ∂P, aux_affine_source_cells_env_InstConcl Qcentre Qside hQside field GE E
      GammaE baseMesh c rho zeta H1 n z zP k0 lambdaLim cell epshom cdet ZL DL loL hiL errL ratL
      omega := by
  have htransfer {X : ℕ → BilateralField d → ℝ} {V : BilateralField d → ℝ}
      (hV : Measurable V) (hXV : TendstoInMeasure (chaosSampleLaw M).toMeasure X atTop V) :
      TendstoInMeasure P (fun n omega => X n (env n omega)) atTop (fun omega => V (field omega)) :=
    represented_same_law_in_measure (fun n => ⟨hEnvMeas n, hEnvLaw n⟩)
      ⟨hfieldMeas, hfieldLaw⟩ hEnvConv hV.aestronglyMeasurable hXV
  have hgHk' : gH ≤ H1 * (n + 1) := le_trans hgHk (Nat.le_mul_of_pos_right _ (Nat.succ_pos n))
  have hcen := aux_affine_source_cells_env_chosen_centre gH (H1 * (n + 1)) z
    (fun i => Fin.elim0 i)
  have hlev : gcat_rootLevel gH (H1 * (n + 1)) ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3)) +
      ((0 : ℕ) : ℤ) = ((H1 * (n + 1) : ℕ) : ℤ) - (gH : ℤ) := by
    rw [aux_affine_source_cells_env_chosen_level, Nat.cast_zero, add_zero]
  have hZ := (fun U D code => htransfer (hmeas.1 U D code).1 (harr.1 U D code))
  have hD := (fun U D code => htransfer (hmeas.1 U D code).2 (harr.2.1 U D code))
  have hlo := (fun U => htransfer (hmeas.2.1 U).1 (harr.2.2.1 U))
  have hhi := (fun U => htransfer (hmeas.2.1 U).2.1 (harr.2.2.2.1 U))
  have hA := (fun U i j => htransfer ((hmeas.2.1 U).2.2 i j) (harr.2.2.2.2.1 U i j))
  have herr := htransfer hmeas.2.2.1 harr.2.2.2.2.2.1
  have hrat := htransfer hmeas.2.2.2 harr.2.2.2.2.2.2
  have hres := hcell n z zP gi pi idx hzP hz hpar
    ((3 : ℝ) ^ (-((H1 * (n + 1) : ℕ) : ℤ))) rfl z rfl
    (Fin 3) (Fin d → Fin 3) Unit (0 : Fin 3) (fun _ => (1 : Fin 3))
    ((0 : Fin 3), fun _ : Fin d => (1 : Fin 3)) rfl
    (gcat_factor gH) rfl (1 : Fin 3) rfl gcat_shift
    aux_affine_source_cells_env_shift_one
    (gcat_rootLevel gH (H1 * (n + 1))) (fun e t => rfl)
    (gcat_rootSide gH (H1 * (n + 1))) (fun U => rfl)
    (gcat_rootCentre gH (H1 * (n + 1)) z) (fun e t => rfl)
    (fun U => zpow_pos (by norm_num) _)
    (aux_affine_source_cells_env_gridCover gH (H1 * (n + 1)) z)
    (fun _ => ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3))) (fun _ => 0)
    (fun _ i => Fin.elim0 i)
    (fun c => (descendantCenter 1
          (gcat_rootCentre gH (H1 * (n + 1)) z ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3)))
          (gcat_rootSide gH (H1 * (n + 1)) ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3))) 0
          (fun i => Fin.elim0 i))) (fun c => rfl)
    (fun _ => gcat_rootLevel gH (H1 * (n + 1)) ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3)) +
      ((0 : ℕ) : ℤ)) (fun c => rfl)
    (fun _ => (3 : ℝ) ^ (-(gcat_rootLevel gH (H1 * (n + 1))
      ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3)) + ((0 : ℕ) : ℤ)))) (fun c => rfl)
    (fun _ => zpow_pos (by norm_num) _) () hcen
    (by
      show gcat_rootLevel gH (H1 * (n + 1))
        ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3)) + ((0 : ℕ) : ℤ) = _
      rw [hlev, hgH]
      push_cast
      ring)
    (by
      intro x hx
      apply hpad
      have hr : (3 : ℝ) ^ (-(gcat_rootLevel gH (H1 * (n + 1))
          ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3)) + ((0 : ℕ) : ℤ))) / 2 =
          (3 : ℝ) ^ (-(((H1 * (n + 1) : ℕ) : ℤ) - (gH : ℤ))) / 2 := by
        rw [hlev]
      rw [← hr]
      exact hx)
    (gcat_obsCentre gH (H1 * (n + 1)) z) (fun U D code => rfl)
    eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive lambdaCut lambdaLim
    lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall
    (fun N U D code omega => gcat_prefix gH cbuf (H1 * (n + 1)) z Z N U D code omega)
    (fun N U D code omega => gcat_prefix gH cbuf (H1 * (n + 1)) z
      (fun N m w om => (Draw N m w om).toReal) N U D code omega)
    (fun N U D code omega => rfl) (fun N U D code omega => rfl) hFinite
    (gcat_sN M H) (fun N l w omega => rfl)
    (fun N U omega => I.lam (gcat_rootCentre gH (H1 * (n + 1)) z U)
      (gcat_rootSide gH (H1 * (n + 1)) U) (zpow_pos (by norm_num) _)
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
        (gcat_rootCentre gH (H1 * (n + 1)) z U) (zpow_pos (by norm_num) _))
      (gcat_rootCentre gH (H1 * (n + 1)) z U)
      (gcat_rootSide gH (H1 * (n + 1)) U) sigma 2 /
      gcat_sN M H N (gcat_rootLevel gH (H1 * (n + 1)) U)
        (gcat_rootCentre gH (H1 * (n + 1)) z U) omega)
    (fun N U omega => I.Lam (gcat_rootCentre gH (H1 * (n + 1)) z U)
      (gcat_rootSide gH (H1 * (n + 1)) U) (zpow_pos (by norm_num) _)
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
        (gcat_rootCentre gH (H1 * (n + 1)) z U) (zpow_pos (by norm_num) _))
      (gcat_rootCentre gH (H1 * (n + 1)) z U)
      (gcat_rootSide gH (H1 * (n + 1)) U) sigma 2 /
      gcat_sN M H N (gcat_rootLevel gH (H1 * (n + 1)) U)
        (gcat_rootCentre gH (H1 * (n + 1)) z U) omega)
    (fun N U omega => rfl) (fun N U omega => rfl)
    (fun N U omega =>
      ((gcat_sN M H N (gcat_rootLevel gH (H1 * (n + 1)) U)
        (gcat_rootCentre gH (H1 * (n + 1)) z U) omega)⁻¹ •
        Homogenization.Book.Ch02.sigmaCoarse
          (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
          ((I.chart (gcat_rootCentre gH (H1 * (n + 1)) z U)
            (gcat_rootSide gH (H1 * (n + 1)) U) (zpow_pos (by norm_num) _)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
              (gcat_rootCentre gH (H1 * (n + 1)) z U)
              (zpow_pos (by norm_num) _))
            (gcat_rootCentre gH (H1 * (n + 1)) z U)
            (gcat_rootSide gH (H1 * (n + 1)) U)).coeffOn
            (Homogenization.originCube d 0))))
    (fun N U omega => rfl)
    (fun N c omega => I.err z ((3 : ℝ) ^ (-(((H1 * (n + 1) : ℕ) : ℤ) - (gH : ℤ))))
      (zpow_pos (by norm_num) _)
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z (zpow_pos (by norm_num) _))
      z ((3 : ℝ) ^ (-(((H1 * (n + 1) : ℕ) : ℤ) - (gH : ℤ))))
      (gcat_sN M H N (((H1 * (n + 1) : ℕ) : ℤ) - (gH : ℤ)) z omega) s 2)
    (fun N c omega => gcat_sN M H N ((H1 * (n + 1) : ℕ) : ℤ) z omega /
      gcat_sN M H N (((H1 * (n + 1) : ℕ) : ℤ) - (gH : ℤ)) z omega)
    (by
      intro N c omega
      have ha : gcat_sN M H N (gcat_rootLevel gH (H1 * (n + 1))
          ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3)) + ((0 : ℕ) : ℤ)) (descendantCenter 1
          (gcat_rootCentre gH (H1 * (n + 1)) z ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3)))
          (gcat_rootSide gH (H1 * (n + 1)) ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3))) 0
          (fun i => Fin.elim0 i)) omega =
          gcat_sN M H N (((H1 * (n + 1) : ℕ) : ℤ) - (gH : ℤ)) z omega := by
        rw [hlev, hcen]
      rw [ha]
      exact aux_affine_source_cells_env_err_congr I M H N omega _ _ _ _ _ _ _ s
        hcen.symm (by rw [hlev]))
    (by
      intro N c omega
      rw [hlev, hcen])
    (fun omega => eRef (H1 * (n + 1)) *
      Real.exp (H (field omega) z +
        ∑ j ∈ Finset.range (H1 * (n + 1)), (field omega) (-(j : ℤ)) z))
    (fun _ omega => eRef (H1 * (n + 1) - gH) *
      Real.exp (H (field omega) (descendantCenter 1
          (gcat_rootCentre gH (H1 * (n + 1)) z ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3)))
          (gcat_rootSide gH (H1 * (n + 1)) ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3))) 0
          (fun i => Fin.elim0 i)) +
        ∑ j ∈ Finset.range (H1 * (n + 1) - gH), (field omega) (-(j : ℤ)) (descendantCenter 1
          (gcat_rootCentre gH (H1 * (n + 1)) z ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3)))
          (gcat_rootSide gH (H1 * (n + 1)) ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3))) 0
          (fun i => Fin.elim0 i))))
    ⟨by
      filter_upwards [hEnvConv, hIRConv] with omega henv hir
      exact ⟨mul_pos (heRefPos _) (Real.exp_pos _),
        aux_affine_source_cells_env_sN_tendsto M H phi hphi eRef heRefLim
          (H1 * (n + 1)) z (fun j => env j omega) (field omega) henv hir⟩,
      Filter.Eventually.of_forall fun omega => rfl⟩
    (by
      filter_upwards [hEnvConv, hIRConv] with omega henv hir
      intro c'
      refine ⟨mul_pos (heRefPos _) (Real.exp_pos _), by
        have h := aux_affine_source_cells_env_sN_tendsto M H phi hphi eRef heRefLim
          (H1 * (n + 1) - gH) (descendantCenter 1
          (gcat_rootCentre gH (H1 * (n + 1)) z ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3)))
          (gcat_rootSide gH (H1 * (n + 1)) ((2 : Fin 3), fun _ : Fin d => (1 : Fin 3))) 0
          (fun i => Fin.elim0 i)) (fun j => env j omega) (field omega) henv
          (by simpa only [hcen] using hir)
        rw [← aux_affine_source_cells_env_chosen_level_nat gH (H1 * (n + 1)) hgHk'] at h
        exact h⟩)
    (fun U D code omega => ZL U D code (field omega))
    (fun U D code omega => DL U D code (field omega))
    (fun U omega => loL U (field omega)) (fun U omega => hiL U (field omega))
    (fun U omega => AEL U (field omega))
    (fun c omega => errL c (field omega)) (fun c omega => ratL c (field omega))
    hZ
    hD
    hlo
    hhi
    hA
    (fun c => herr)
    (fun c => hrat)
    hroots
  filter_upwards [hres] with omega hω
  intro f hf fL2 hfae
  obtain ⟨U, h1, h2, h3, h4⟩ := hω f hf fL2 hfae
  exact ⟨U, h1, h2, fun hr hg => (h4 hr hg).2⟩


/-- A representable limit form for a limit operator `G` on the cube `Q`: a Dirichlet form with core and
energy measure whose extended energy is `limitFormEnergy G`. -/
def aux_affine_source_cells_env_side {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (G : DomainL2 Q →L[ℝ] DomainL2 Q) : Prop :=
  ∃ (Ef : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (_Gam : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure Ef.toClosedForm),
    (∀ u, Ef.toClosedForm.energy u = limitFormEnergy G u) ∧
    ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn Ef.toClosedForm (Q : Set (SpatialCoordinates d)) C

/-- Total selection of the limit operator and of a side: if a side exists for a.e. `ω`, there is a total
`sel : Ω → CLM` that equals `GE` a.e. and has a side at EVERY `ω` (the internal total witness uses an existing good `ω₀` outside the full event). -/
theorem aux_affine_source_cells_env_select {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Opens (SpatialCoordinates d))
    (GE : Ω → DomainL2 Q →L[ℝ] DomainL2 Q)
    (hside : ∀ᵐ omega ∂P, aux_affine_source_cells_env_side Q (GE omega)) :
    ∃ sel : Ω → (DomainL2 Q →L[ℝ] DomainL2 Q),
      (∀ omega, aux_affine_source_cells_env_side Q (sel omega)) ∧
      ∀ᵐ omega ∂P, sel omega = GE omega := by
  classical
  obtain ⟨w, hw⟩ := hside.exists
  refine ⟨fun omega => if aux_affine_source_cells_env_side Q (GE omega) then GE omega
    else GE w, fun omega => ?_, ?_⟩
  · by_cases h : aux_affine_source_cells_env_side Q (GE omega)
    · simpa only [ite_eq_left h] using h
    · simpa only [ite_eq_right h] using hw
  · filter_upwards [hside] with omega h
    exact ite_eq_left h


/-- Two forms with the same extended limit energy have the same domain. -/
theorem aux_affine_source_cells_env_domain_eq {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (E F : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u) (hF : ∀ u, F.energy u = limitFormEnergy G u) :
    E.domain = F.domain := by
  apply SetLike.ext
  intro v
  rw [← E.energy_lt_top_iff v, ← F.energy_lt_top_iff v, hE v, hF v]

/-- Arbitrary sides of the same limit operator have the same energy measures on the domain
(`limit_form_energy_measure_unique`; no assumption that arbitrary energy measures coincide). -/
theorem aux_affine_source_cells_env_measure_eq {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (E F : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GammaE : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure F.toClosedForm)
    (hE : ∀ u, E.toClosedForm.energy u = limitFormEnergy G u)
    (hF : ∀ u, F.toClosedForm.energy u = limitFormEnergy G u)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) C)
    (u : DomainL2 Q) (hu : u ∈ F.toClosedForm.domain) :
    GammaE.measure u = GammaF.measure u := by
  refine _root_.SubdiffusiveProcess.Paper.limit_form_energy_measure_unique Q G E F GammaE GammaF hE hF hcore u ?_
  change limitFormEnergy G u < ⊤
  rw [← hF u]
  exact (F.toClosedForm.energy_lt_top_iff u).mpr hu

/-- The boundary energy sets of two sides of the same limit operator coincide (on the sources of the
domain), hence so do their greatest lower bounds. -/
theorem aux_affine_source_cells_env_eSet_eq {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (E F : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GammaE : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure F.toClosedForm)
    (hE : ∀ u, E.toClosedForm.energy u = limitFormEnergy G u)
    (hF : ∀ u, F.toClosedForm.energy u = limitFormEnergy G u)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) C)
    (q : Set (SpatialCoordinates d)) (b : SpatialCoordinates d → ℝ) :
    {e : ℝ | ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
        v ∈ E.toClosedForm.domain ∧ ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
        ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V) ∧
        (∀ x ∈ frontier q, V x = b x) ∧ e = ((GammaE.measure v) q).toReal} =
    {e : ℝ | ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
        v ∈ F.toClosedForm.domain ∧ ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
        ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V) ∧
        (∀ x ∈ frontier q, V x = b x) ∧ e = ((GammaF.measure v) q).toReal} := by
  have hdom := aux_affine_source_cells_env_domain_eq Q G E.toClosedForm F.toClosedForm hE hF
  ext e
  constructor
  · rintro ⟨v, V, hv, hVc, hVa, hVb, rfl⟩
    have hvF : v ∈ F.toClosedForm.domain := hdom ▸ hv
    exact ⟨v, V, hvF, hVc, hVa, hVb, by
      rw [aux_affine_source_cells_env_measure_eq Q G E F GammaE GammaF hE hF hcore v hvF]⟩
  · rintro ⟨v, V, hv, hVc, hVa, hVb, rfl⟩
    have hvE : v ∈ E.toClosedForm.domain := hdom ▸ hv
    exact ⟨v, V, hvE, hVc, hVa, hVb, by
      rw [aux_affine_source_cells_env_measure_eq Q G E F GammaE GammaF hE hF hcore v hv]⟩


/-- Volumes of the parent and cell balls: `vol(ball zP (L r/2)) = L^d vol(ball z (r/2))`. -/
theorem aux_affine_source_cells_env_vol {d : ℕ} (zP z : SpatialCoordinates d) (L r : ℝ)
    (hL : 0 < L) (hr : 0 < r) :
    (volume (Metric.ball zP (L * r / 2))).toReal =
      L ^ d * (volume (Metric.ball z (r / 2))).toReal := by
  have h1 := centeredCube_volume_real zP (mul_pos hL hr)
  have h2 := centeredCube_volume_real z hr
  rw [Measure.real] at h1 h2
  change (volume (Metric.ball zP (L * r / 2))).toReal = (L * r) ^ d at h1
  change (volume (Metric.ball z (r / 2))).toReal = r ^ d at h2
  rw [h1, h2, mul_pow]

theorem aux_affine_source_cells_env_Ld_le {d : ℕ} (L zeta : ℝ) (hL : 1 ≤ L)
    (hzeta : 0 < zeta) : L ^ d ≤ L ^ ((d : ℝ) + zeta) := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hL (by linarith)

/-- Hypothesis transfer for one cell: from the arbitrary side and `c` to the selected side and `q`. -/
theorem aux_affine_source_cells_env_hyp_transfer {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (Ef E' : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gam : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure Ef.toClosedForm)
    (Gam' : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E'.toClosedForm)
    (hEf : ∀ u, Ef.toClosedForm.energy u = limitFormEnergy G u)
    (hE' : ∀ u, E'.toClosedForm.energy u = limitFormEnergy G u)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn Ef.toClosedForm (Q : Set (SpatialCoordinates d)) C)
    (u : DomainL2 Q) (hu : u ∈ E'.toClosedForm.domain)
    (pp qq : Set (SpatialCoordinates d)) (Ld Lz c q : ℝ)
    (hvol : (volume pp).toReal = Ld * (volume qq).toReal) (hLd : Ld ≤ Lz)
    (_hc0 : 0 < c) (hcq : c ≤ q) (hq2 : q ≤ 2 * c)
    (hc : ((Gam'.measure u) pp).toReal + c * (volume pp).toReal ≤
        Lz * (((Gam'.measure u) qq).toReal + c * (volume qq).toReal)) :
    ((Gam.measure u) pp).toReal + q * (volume pp).toReal ≤
      Lz * (((Gam.measure u) qq).toReal + q * (volume qq).toReal) := by
  have hmu : Gam.measure u = Gam'.measure u :=
    aux_affine_source_cells_env_measure_eq Q G Ef E' Gam Gam' hEf hE' hcore u hu
  rw [hmu]
  have hgQ : 0 ≤ ((Gam'.measure u) qq).toReal := ENNReal.toReal_nonneg
  have hvQ : 0 ≤ (volume qq).toReal := ENNReal.toReal_nonneg
  exact (aux_affine_source_cells_env_c_reduction _ _ _ _ Ld Lz c q 0 0 hgQ hvQ hcq hq2
    le_rfl hvol hLd hc (by simp)).1

/-- Conclusion transfer for one cell: the boundary approximation for the selected side and `q` gives the
one for the arbitrary side and `c`, with the constant doubled. -/
theorem aux_affine_source_cells_env_concl_transfer {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (Ef E' : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gam : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure Ef.toClosedForm)
    (Gam' : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E'.toClosedForm)
    (hEf : ∀ u, Ef.toClosedForm.energy u = limitFormEnergy G u)
    (hE' : ∀ u, E'.toClosedForm.energy u = limitFormEnergy G u)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn Ef.toClosedForm (Q : Set (SpatialCoordinates d)) C)
    (u : DomainL2 Q) (hu : u ∈ E'.toClosedForm.domain)
    (qq : Set (SpatialCoordinates d)) (b : SpatialCoordinates d → ℝ) (c q rho : ℝ)
    (_hc0 : 0 < c) (hcq : c ≤ q) (hq2 : q ≤ 2 * c) (hrho : 0 ≤ rho)
    (hin : ∃ Lambda : ℝ,
        IsGLB {e : ℝ | ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
          v ∈ Ef.toClosedForm.domain ∧ ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
          ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V) ∧
          (∀ x ∈ frontier qq, V x = b x) ∧ e = ((Gam.measure v) qq).toReal} Lambda ∧
        {e : ℝ | ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
          v ∈ Ef.toClosedForm.domain ∧ ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
          ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V) ∧
          (∀ x ∈ frontier qq, V x = b x) ∧ e = ((Gam.measure v) qq).toReal}.Nonempty ∧
        Lambda ≤ rho * (((Gam.measure u) qq).toReal + q * (volume qq).toReal)) :
      ∃ Lambda : ℝ,
        IsGLB {e : ℝ | ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
          v ∈ E'.toClosedForm.domain ∧ ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
          ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V) ∧
          (∀ x ∈ frontier qq, V x = b x) ∧ e = ((Gam'.measure v) qq).toReal} Lambda ∧
        {e : ℝ | ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
          v ∈ E'.toClosedForm.domain ∧ ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
          ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V) ∧
          (∀ x ∈ frontier qq, V x = b x) ∧ e = ((Gam'.measure v) qq).toReal}.Nonempty ∧
        Lambda ≤ (2 * rho) * (((Gam'.measure u) qq).toReal + c * (volume qq).toReal) := by
  have hmu : Gam.measure u = Gam'.measure u :=
    aux_affine_source_cells_env_measure_eq Q G Ef E' Gam Gam' hEf hE' hcore u hu
  have hset := aux_affine_source_cells_env_eSet_eq Q G Ef E' Gam Gam' hEf hE' hcore qq b
  obtain ⟨Lambda, hglb, hne, hle⟩ := hin
  rw [hset] at hglb hne
  rw [hmu] at hle
  have hgQ : 0 ≤ ((Gam'.measure u) qq).toReal := ENNReal.toReal_nonneg
  have hvQ : 0 ≤ (volume qq).toReal := ENNReal.toReal_nonneg
  exact ⟨Lambda, hglb, hne,
    (aux_affine_source_cells_env_c_reduction ((Gam'.measure u) qq).toReal
      ((Gam'.measure u) qq).toReal (volume qq).toReal (volume qq).toReal 1 1 c q rho Lambda hgQ hvQ
      hcq hq2 hrho (by ring) le_rfl (by ring_nf; exact le_rfl) hle).2⟩


/-- The conclusion of `affine_source_cells_env` (the almost-sure statement, for the constant
environment `field`, arbitrary limit sides, and all cells of the finite mesh). -/
def aux_affine_source_cells_env_Concl {d : ℕ}
    (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (field : Ω → BilateralField d)
    (GE : Ω → DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
      DomainL2 (centeredCube Qcentre Qside hQside))
    (gamma zeta rho : ℝ) (H1 : ℕ) (k0 : ℕ) (lambdaLim cell epshom cdet : ℝ)
    (Grid : Type) (origin : Grid → SpatialCoordinates d) (J : ℕ) (gridChoice : Fin J → Grid)
    {Cells : Type} (cellLevel : Cells → ℕ) (cellCentre : Cells → SpatialCoordinates d)
    (ZLim DLim : Cells → ∀ (_U : Fin 3 × (Fin d → Fin 3)) (D : ℕ),
      ((Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) → BilateralField d → ℝ)
    (loLim hiLim : Cells → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → ℝ)
    (errLim ratioLim : Cells → Unit → BilateralField d → ℝ) : Prop :=
  ∀ᵐ omega ∂P,
    ∀ (E' : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
      (Gam' : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E'.toClosedForm),
      (∀ u, E'.toClosedForm.energy u = limitFormEnergy (GE omega) u) →
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E'.toClosedForm
        (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) C) →
    ∀ (fL2 : DomainL2 (centeredCube Qcentre Qside hQside)),
      (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧
        ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] fc)) →
      GE omega fL2 ∈ E'.toClosedForm.domain →
    ∀ c : ℝ, 0 < c →
    ∃ baseMesh : ℝ, 0 < baseMesh ∧
    ∀ (n : ℕ) (gridIndex : Fin J) (parentIndex : Fin d → ℤ)
      (idx : OddGridIndex d (subdivisionHalfWidth H1)) (cj : Cells),
      (let L : ℝ := (3 : ℝ) ^ H1
       let k : ℕ := H1 * (n + 1)
       let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
       let zP : SpatialCoordinates d :=
         fun i => origin (gridChoice gridIndex) i + (L * r) * ((parentIndex i : ℝ))
       let z : SpatialCoordinates d := oddGridCenter zP (L * r) (subdivisionHalfWidth H1) idx
       cellCentre cj = z → cellLevel cj = k →
       Metric.ball zP (L * r / 2) ⊆
         (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) →
       Metric.closedBall z
         ((3 : ℝ) ^ (-((k : ℤ) - ((Nat.floor (gamma * (H1 : ℝ)) + 4 : ℕ) : ℤ))) / 2) ⊆
         Metric.ball zP (L * r / 2) →
       (∀ U : Fin 3 × (Fin d → Fin 3),
         closure (centeredCube (gcat_rootCentre (Nat.floor (gamma * (H1 : ℝ)) + 4) k z U)
           (gcat_rootSide (Nat.floor (gamma * (H1 : ℝ)) + 4) k U)
           (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d)) ⊆
         (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) →
       ∃ U : SpatialCoordinates d → ℝ,
         ContinuousOn U
           (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ∧
         ((GE omega fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
           (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] U) ∧
         (r ≤ baseMesh →
          field omega ∈ gcat_good k0 lambdaLim cell epshom cdet
            (ZLim cj) (DLim cj) (loLim cj) (hiLim cj) (errLim cj) (ratioLim cj) →
          (let lambda : Set (SpatialCoordinates d) → ℝ :=
             fun A => ((Gam'.measure (GE omega fL2)) A).toReal +
               c * (volume A).toReal
           lambda (Metric.ball zP (L * r / 2)) ≤
             L ^ ((d : ℝ) + zeta) * lambda (Metric.ball z (r / 2)) →
           ∃ pc : (Fin d → ℝ) × ℝ,
             (let b : SpatialCoordinates d → ℝ :=
                fun x => U x - ((∑ i, pc.1 i * x i) + pc.2)
              let eSet : Set ℝ :=
                {e : ℝ |
                  ∃ (v : DomainL2 (centeredCube Qcentre Qside hQside))
                    (V : SpatialCoordinates d → ℝ),
                    v ∈ E'.toClosedForm.domain ∧
                    ContinuousOn V
                      (closure (centeredCube Qcentre Qside hQside :
                        Set (SpatialCoordinates d))) ∧
                    ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] V) ∧
                    (∀ x ∈ frontier (Metric.ball z (r / 2)), V x = b x) ∧
                    e = ((Gam'.measure v) (Metric.ball z (r / 2))).toReal}
              ∃ Lambda : ℝ,
                IsGLB eSet Lambda ∧ eSet.Nonempty ∧
                Lambda ≤ (2 * rho) * lambda (Metric.ball z (r / 2))))))

/-- **Layer 1: `lem_affine` at the concrete good-cell catalogue, constant environment.**
Restatement of the first conjunct of `SubdiffusiveProcess.Paper.lem_affine` for the represented data of ONE side along the
varying environments `env`, cutoff `phi`, with the finite root/test catalogue instantiated by
`gcat_*` (`Enl := Fin 3` with factors `![0,1,gH]`, `Shift := Fin d → Fin 3`, `Cmp := Unit`, `gH = ⌊γ H1⌋ + 4`),
the good event `field ω ∈ gcat_good …`, and arbitrary limit sides (energy-measure uniqueness), with the order
"a.e. ω, side, source, `c`, `baseMesh`, cells".  Conclusion constant `2ρ` (rational `c'` reduction). -/
theorem affine_source_cells_env
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (_X : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (_Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (_Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (_MeyersMorrey : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Pin : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (D : _root_.SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input d) (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (beta : ℝ) (hbeta : 1 / 2 < beta) (hbeta1 : beta < 1) :
    ∀ (alpha gamma zeta rho s sigma cell : ℝ)
    (_hba : beta < alpha) (_halpha : alpha < 1)
    (_hgamma : 0 < gamma) (_hgamma1 : gamma < 1) (_hzeta : 0 < zeta)
    (_hrho : 0 < rho)
    (_hneg : affineExponent (d : ℝ) alpha beta gamma zeta < 0)
    (_hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (_hsSmall : s ≤ (1 / 32 : ℝ))
    (_hsigma_eq : sigma = (beta - 1 / 2) / 4)
    (_hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (_hcell : cell ∈ Set.Ioo (0 : ℝ) 1)
    (cbuf k0 : ℕ),
    ∃ H0 : ℕ, ∀ H1 : ℕ, H0 ≤ H1 →
      (0 < H1 ∧ (1 : ℝ) < (3 : ℝ) ^ H1 ∧ Nat.floor (gamma * (H1 : ℝ)) + 6 < H1) ∧
      ∃ epshom : ℝ, ∃ (_hepshom : 0 < epshom),
      ∃ Cbound eps0 lam0 delta0 : ℝ,
        (1 : ℝ) ≤ Cbound ∧ 0 < eps0 ∧ 0 < lam0 ∧ 0 < delta0 ∧
        ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
          (H : BilateralField d → C(SpatialCoordinates d, ℝ))
          (_hMH : InfraredCharacterization M H)
          (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
          (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M)
          (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M I Sreg)
          (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (field : Ω → BilateralField d)
          (_hfieldMeas : Measurable field)
          (_hfieldLaw : Measure.map field P = (chaosSampleLaw M).toMeasure)
          (env : ℕ → Ω → BilateralField d) (_hEnvMeas : ∀ n, Measurable (env n))
          (_hEnvLaw : ∀ n, Measure.map (env n) P = (chaosSampleLaw M).toMeasure)
          (_hEnvConv : ∀ᵐ omega ∂P, Tendsto (fun n => env n omega) atTop (𝓝 (field omega))),
          M.delta ≤ delta0 →
          ∀ (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
            (S : ResponseSpace (centeredCube Qcentre Qside hQside))
            (_hS : S.space = killedSobolevGraph (centeredCube Qcentre Qside hQside))
            (phi : ℕ → ℕ) (_hphi : StrictMono phi)
            (RootIndex : Type) [Countable RootIndex] [DecidableEq RootIndex]
            (root0 : RootIndex)
            (zCat : RootIndex → SpatialCoordinates d) (rCat : RootIndex → ℝ)
            (hrCat : ∀ j, 0 < rCat j)
            (SCat : ∀ j, ResponseSpace (centeredCube (zCat j) (rCat j) (hrCat j)))
            (DCat : ∀ j,
              Submodule ℚ (DomainL2 (centeredCube (zCat j) (rCat j) (hrCat j))))
            [_hDCatc : ∀ j, Countable (DCat j)]
            (fCat : ∀ j, (DCat j) → SpatialCoordinates d → ℝ)
            (TCat : RootIndex → Type) [_hTCatc : ∀ j, Countable (TCat j)]
            (thetaCat : ∀ j, TCat j → SpatialCoordinates d → ℝ)
            (thetaH1Cat : ∀ j, TCat j →
              Homogenization.H1Function
                (centeredCube (zCat j) (rCat j) (hrCat j) : Set (SpatialCoordinates d)))
            (usrc : ∀ j, (DCat j) → ℕ → Ω → (SCat j).space)
            (srcRep : ∀ j, (DCat j) → ℕ → Ω → SpatialCoordinates d → ℝ)
            (ucell : ∀ j, TCat j → ℕ → Ω →
              Homogenization.H1Function
                (centeredCube (zCat j) (rCat j) (hrCat j) : Set (SpatialCoordinates d)))
            (Cext : ℝ) (etaCat : ℝ) (t : ℝ) (orders : Finset ℝ)
            (Index : Type) [Countable Index]
            (resp : Index → ℕ → Ω → ℝ)
            (respLim : Index → Ω → ℝ)
            (constants : Index → ℕ → Ω → ℝ) (Gcat : Set Ω)
            (coercivityKey extensionKey lambdaKey : RootIndex → Index)
            (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ j, (DCat j) → Index)
            (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, TCat j → Index)
            (Grid : Type) [Countable Grid]
            (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → RootIndex)
            (gridKey : Grid → Index)
            (_hRootCatalogue : zCat root0 = Qcentre ∧ rCat root0 = Qside)
            (_hRep : conv_represented_estimates d hd M H Ω P phi env
                RootIndex root0 zCat rCat hrCat SCat DCat fCat TCat thetaCat
                thetaH1Cat usrc srcRep ucell Cext beta alpha etaCat t
                orders I Index resp respLim constants Gcat
                coercivityKey extensionKey lambdaKey sourceResponseKey
                sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey
                cellHolderKey Grid origin gridRoot gridKey)
            (GE : Ω → DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
              DomainL2 (centeredCube Qcentre Qside hQside))
            (_hGE : ∀ᵐ omega ∂P,
              Tendsto (fun n => volumeResponseOperator S
                (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n omega) (phi n) Qcentre hQside))
                atTop (𝓝 (GE omega)))
            (_hside : ∀ᵐ omega ∂P,
              ∃ (Ef : _root_.SubdiffusiveProcess.DirichletForm
                  (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
                (_Gam : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure Ef.toClosedForm),
                (∀ u, Ef.toClosedForm.energy u = limitFormEnergy (GE omega) u) ∧
                ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn Ef.toClosedForm
                  (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) C)
            (eRef : ℕ → ℝ)
            (_heRefPos : ∀ k : ℕ, 0 < eRef k)
            (_heRefLim : ∀ k : ℕ,
              Tendsto (fun n : ℕ =>
                (let kappa : ℕ → ℝ := fun J =>
                   Real.exp (((J : ℝ) + 1) *
                     _root_.SubdiffusiveProcess.Model.tauSq M.P) *
                     SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
                 kappa (((phi n : ℤ) - (k : ℤ)).toNat) / kappa (phi n)))
                atTop (𝓝 (eRef k)))
            (J : ℕ) (gridChoice : Fin J → Grid)
            (_hGridChoice : ∀ j, gridRoot (gridChoice j) = root0)
            (Cells : Type) [Countable Cells] (cellLevel : Cells → ℕ)
            (cellCentre : Cells → SpatialCoordinates d)
            (_hIRConv : ∀ᵐ omega ∂P, ∀ c : Cells,
              Tendsto (fun n => H (env n omega) (cellCentre c)) atTop
                (𝓝 (H (field omega) (cellCentre c))))
            (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
            (_hEta : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              ∀ (N i : ℕ) (y : Fin d → ℝ),
                eta N omega i y =
                  omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y)))
            (F Praw Rraw Draw : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → ENNReal)
            (Z : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → ℝ)
            (rawGood : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → Prop)
            (eps : ℝ) (_heps : eps ∈ Set.Ioo (0 : ℝ) 1) (_hepsSmall : eps ≤ eps0)
            (_hPrimitive : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              ∀ N : ℕ,
                primitive_scores d M s eps (eta N omega)
                  (fun m y => F N m y omega)
                  (fun m y => Praw N m y omega)
                  (fun m y => Rraw N m y omega)
                  (fun m y => Draw N m y omega)
                  (fun m y => Z N m y omega)
                  (fun m y => rawGood N m y omega)))
            (lambdaCut lambdaLim lambdaDet cdet : ℝ)
            (_hThresholds :
              0 < lambdaCut ∧ lambdaCut < lambdaLim ∧
              lambdaLim < lambdaDet ∧ lambdaDet < 1)
            (_hcdet : 0 < cdet) (_hcdetSmall : cdet ≤ Cbound⁻¹)
            (_hlamSmall : lambdaDet ≤ lam0)
            (_hFiniteScoreGuard : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              ∀ (c : Cells) (N : ℕ) (U : Fin 3 × (Fin d → Fin 3)) (D : ℕ)
                (code : (Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))),
                gcat_rootLevel (Nat.floor (gamma * (H1 : ℝ)) + 4) (cellLevel c) U + (D : ℤ) ≤ (N : ℤ) →
                ∀ j ∈ Finset.Icc (gcat_rootLevel (Nat.floor (gamma * (H1 : ℝ)) + 4) (cellLevel c) U -
                    (cbuf : ℤ))
                  (gcat_rootLevel (Nat.floor (gamma * (H1 : ℝ)) + 4) (cellLevel c) U + (D : ℤ)),
                  Draw N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • gcat_obsCentre (Nat.floor (gamma * (H1 : ℝ)) + 4)
                      (cellLevel c) (cellCentre c) U D code) omega ≠ ⊤))
            (ZLim DLim : Cells → ∀ (_U : Fin 3 × (Fin d → Fin 3)) (D : ℕ),
              ((Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) → BilateralField d → ℝ)
            (loLim hiLim : Cells → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → ℝ)
            (AELim : Cells → (Fin 3 × (Fin d → Fin 3)) → BilateralField d →
              Matrix (Fin d) (Fin d) ℝ)
            (errLim ratioLim : Cells → Unit → BilateralField d → ℝ)
            (_hArrMeas : ∀ c : Cells,
              (∀ U D code, Measurable (ZLim c U D code) ∧ Measurable (DLim c U D code)) ∧
              (∀ U, Measurable (loLim c U) ∧ Measurable (hiLim c U) ∧
                ∀ i j, Measurable (fun omega => AELim c U omega i j)) ∧
              Measurable (errLim c ()) ∧ Measurable (ratioLim c ()))
            (_hArr : aux_affine_source_cells_env_arrays I M H s sigma
              (Nat.floor (gamma * (H1 : ℝ)) + 4) cbuf Z Draw phi cellLevel cellCentre
              ZLim DLim loLim hiLim AELim errLim ratioLim),
          aux_affine_source_cells_env_Concl Qcentre Qside hQside P field GE gamma zeta rho
            H1 k0 lambdaLim cell epshom cdet Grid origin J gridChoice cellLevel cellCentre ZLim DLim
            loLim hiLim errLim ratioLim := by
  intro alpha gamma zeta rho s sigma cell hba halpha hgamma hgamma1 hzeta hrho hneg hs hsSmall
    hsigma_eq hsigma hcell cbuf k0
  obtain ⟨H0, hH0⟩ := (_root_.SubdiffusiveProcess.Paper.lem_affine.{1} d hd I _X _Sob _Step _MeyersMorrey Pin D Cp beta hbeta
    hbeta1).1 alpha gamma zeta rho s sigma cell hba halpha hgamma hgamma1 hzeta hrho hneg hs
    hsSmall hsigma_eq hsigma hcell cbuf k0
  refine ⟨H0, fun H1 hH1 => ?_⟩
  obtain ⟨hH1pos, hLgt1, hfloor, hcover, epshom, hepshom, Cbound, eps0, lam0, delta0, hC, he0,
    hl0, hd0, hM⟩ := hH0 H1 hH1
  refine ⟨⟨hH1pos, hLgt1, hfloor⟩, epshom, hepshom, Cbound, eps0, lam0, delta0, hC, he0, hl0, hd0,
    ?_⟩
  intro M H hMH Rm Sreg _It Ω _ P _ field hfieldMeas hfieldLaw env hEnvMeas hEnvLaw hEnvConv hdelta Qcentre Qside hQside S hS phi
    hphi RootIndex _ _ root0 zCat rCat hrCat SCat DCat _ fCat TCat _ thetaCat thetaH1Cat usrc srcRep
    ucell Cext etaCat t orders Index _ resp respLim constants Gcat coercivityKey extensionKey
    lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey
    cellHolderKey Grid _ origin gridRoot gridKey hRootCatalogue hRep GE hGE hside eRef heRefPos
    heRefLim J gridChoice hGridChoice Cells _ cellLevel cellCentre hIRConv eta hEta F Praw Rraw Draw Z
    rawGood eps heps hepsSmall hPrimitive lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet
    hcdetSmall hlamSmall hFiniteScoreGuard ZLim DLim loLim hiLim AELim errLim ratioLim hArrMeas hArr
  -- the total selection of a side
  obtain ⟨sel, hsel, hselGE⟩ := aux_affine_source_cells_env_select P
    (centeredCube Qcentre Qside hQside) GE hside
  choose Ef Gam hEf hcoreEf using hsel
  let GNf : ℕ → BilateralField d →
      DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
        DomainL2 (centeredCube Qcentre Qside hQside) :=
    fun N omega => volumeResponseOperator S
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
  have hGN : ∀ N omega f, GNf N omega f =
      (responseSolution S (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1 :=
    fun N omega f => volumeResponseOperator_apply S _ f
  have hGEsel : ∀ᵐ omega ∂P,
      Tendsto (fun n => GNf (phi n) (env n omega)) atTop (𝓝 (sel omega)) := by
    filter_upwards [hGE, hselGE] with omega h1 h2
    rw [h2]
    exact h1
  have hLA := hM M H hMH Rm Sreg _It Ω P field hfieldMeas hfieldLaw (fun _ => env)
    (fun _ => hEnvMeas) (fun _ => hEnvLaw)
    (hEnvConv.mono fun omega h _ => h) hdelta Qcentre Qside hQside
    S hS GNf hGN phi hphi RootIndex root0 zCat rCat hrCat SCat DCat fCat TCat thetaCat thetaH1Cat
    (fun _ => usrc) (fun _ => srcRep) (fun _ => ucell) Cext etaCat t orders Index (fun _ => resp)
    (fun _ => respLim) (fun _ => constants) Gcat coercivityKey extensionKey lambdaKey
    sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey
    Grid origin gridRoot gridKey hRootCatalogue (fun _ => hRep) sel hGEsel
    (fun omega => (Ef omega).toClosedForm) (fun omega u => hEf omega u)
    (fun omega => Gam omega) eRef heRefPos heRefLim
  choose bmQ hposQ hcellQ using fun q : {q : ℚ // 0 < (q : ℝ)} =>
    hLA (q.1 : ℝ) q.2 J gridChoice hGridChoice
  have hLAcell : ∀ q : {q : ℚ // 0 < (q : ℝ)},
      aux_affine_source_cells_env_LAcell hd I M H P field env Qcentre Qside hQside sel
        (fun omega => (Ef omega).toClosedForm) Gam phi alpha gamma zeta rho s sigma cell cbuf k0 H1
        epshom Cbound eps0 lam0 eRef Grid origin (q.1 : ℝ) J gridChoice (bmQ q) :=
    fun q => hcellQ q
  set gH : ℕ := Nat.floor (gamma * (H1 : ℝ)) + 4 with hgH
  have hgH1 : gH ≤ H1 := by omega
  let Lr : ℕ → ℝ := fun n => (3 : ℝ) ^ H1 * (3 : ℝ) ^ (-((H1 * (n + 1) : ℕ) : ℤ))
  let zPf : ℕ → Fin J → (Fin d → ℤ) → SpatialCoordinates d := fun n gi pi i =>
    origin (gridChoice gi) i + Lr n * ((pi i : ℤ) : ℝ)
  let zf : ℕ → Fin J → (Fin d → ℤ) → OddGridIndex d (subdivisionHalfWidth H1) →
      SpatialCoordinates d :=
    fun n gi pi idx => oddGridCenter (zPf n gi pi) (Lr n) (subdivisionHalfWidth H1) idx
  have hinst := fun (q : {q : ℚ // 0 < (q : ℝ)}) (n : ℕ) (gi : Fin J) (pi : Fin d → ℤ)
      (idx : OddGridIndex d (subdivisionHalfWidth H1)) (cj : Cells)
      (hc1 : cellCentre cj = zf n gi pi idx) (hc2 : cellLevel cj = H1 * (n + 1))
      (hpar : Metric.ball (zPf n gi pi) (Lr n / 2) ⊆
        (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
      (hpad : Metric.closedBall (zf n gi pi idx)
        ((3 : ℝ) ^ (-(((H1 * (n + 1) : ℕ) : ℤ) - (gH : ℤ))) / 2) ⊆
          Metric.ball (zPf n gi pi) (Lr n / 2))
      (hroots : ∀ U : Fin 3 × (Fin d → Fin 3),
        closure (centeredCube (gcat_rootCentre gH (H1 * (n + 1)) (zf n gi pi idx) U)
          (gcat_rootSide gH (H1 * (n + 1)) U) (zpow_pos (by norm_num) _) :
            Set (SpatialCoordinates d)) ⊆
          (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) =>
    aux_affine_source_cells_env_inst hd I M H P field hfieldMeas hfieldLaw
      env hEnvMeas hEnvLaw hEnvConv Qcentre Qside
      hQside sel (fun omega => (Ef omega).toClosedForm) Gam phi hphi alpha gamma zeta rho s sigma
      cell cbuf k0 H1 epshom Cbound eps0 lam0 eRef heRefPos heRefLim Grid origin (q.1 : ℝ) J
      gridChoice (bmQ q) (hLAcell q) eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall
      hPrimitive lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall gH hgH
      hgH1 n gi pi idx (zf n gi pi idx) (zPf n gi pi)
      (hIRConv.mono fun omega h => by simpa only [hc1] using h cj) rfl rfl hpar hpad hroots
      (hFiniteScoreGuard.mono fun omega h N U D code => by
        have := h cj N U D code
        rw [hc1, hc2] at this
        exact this)
      (ZLim cj) (DLim cj) (loLim cj) (hiLim cj) (AELim cj) (errLim cj) (ratioLim cj) (hArrMeas cj)
      (aux_affine_source_cells_env_cellArrays_congr I M H s sigma gH cbuf Z Draw phi hc2
        hc1 (ZLim cj) (DLim cj) (loLim cj) (hiLim cj) (AELim cj) (errLim cj) (ratioLim cj)
        (hArr cj))
  have hbmpos : ∀ᵐ omega ∂P, ∀ (q : {q : ℚ // 0 < (q : ℝ)}) (f : SpatialCoordinates d → ℝ),
      ContDiff ℝ ∞ f → 0 < bmQ q omega f := by
    rw [ae_all_iff]
    intro q
    exact hposQ q
  have hcellall : ∀ᵐ omega ∂P, ∀ (q : {q : ℚ // 0 < (q : ℝ)}) (n : ℕ) (gi : Fin J)
      (pi : Fin d → ℤ) (idx : OddGridIndex d (subdivisionHalfWidth H1)) (cj : Cells),
      cellCentre cj = zf n gi pi idx → cellLevel cj = H1 * (n + 1) →
      Metric.ball (zPf n gi pi) (Lr n / 2) ⊆
        (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) →
      Metric.closedBall (zf n gi pi idx)
        ((3 : ℝ) ^ (-(((H1 * (n + 1) : ℕ) : ℤ) - (gH : ℤ))) / 2) ⊆
          Metric.ball (zPf n gi pi) (Lr n / 2) →
      (∀ U : Fin 3 × (Fin d → Fin 3),
        closure (centeredCube (gcat_rootCentre gH (H1 * (n + 1)) (zf n gi pi idx) U)
          (gcat_rootSide gH (H1 * (n + 1)) U) (zpow_pos (by norm_num) _) :
            Set (SpatialCoordinates d)) ⊆
          (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) →
      aux_affine_source_cells_env_InstConcl Qcentre Qside hQside field sel
        (fun omega => (Ef omega).toClosedForm) Gam (bmQ q) (q.1 : ℝ) rho zeta H1 n
        (zf n gi pi idx) (zPf n gi pi) k0 lambdaLim cell epshom cdet (ZLim cj) (DLim cj)
        (loLim cj) (hiLim cj) (errLim cj) (ratioLim cj) omega := by
    rw [ae_all_iff]
    intro q
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro gi
    rw [ae_all_iff]
    intro pi
    rw [ae_all_iff]
    intro idx
    rw [ae_all_iff]
    intro cj
    refine Filter.eventually_imp_distrib_left.2 fun h1 => ?_
    refine Filter.eventually_imp_distrib_left.2 fun h2 => ?_
    refine Filter.eventually_imp_distrib_left.2 fun h3 => ?_
    refine Filter.eventually_imp_distrib_left.2 fun h4 => ?_
    refine Filter.eventually_imp_distrib_left.2 fun h5 => ?_
    exact hinst q n gi pi idx cj h1 h2 h3 h4 h5
  unfold aux_affine_source_cells_env_Concl
  filter_upwards [hbmpos, hcellall, hselGE] with omega hpos hcell hsel
  intro E' Gam' hE' hcore' fL2 hfsmooth hu c hc
  obtain ⟨fc, hfc, hfae⟩ := hfsmooth
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show c < 2 * c by linarith)
  have hq0 : 0 < (q : ℝ) := by linarith
  refine ⟨bmQ ⟨q, hq0⟩ omega fc, hpos ⟨q, hq0⟩ fc hfc, ?_⟩
  intro n gi pi idx cj L k r zP z hc1 hc2 hpar hpad hroots
  have hinstc := hcell ⟨q, hq0⟩ n gi pi idx cj hc1 hc2 hpar hpad hroots
  obtain ⟨U, hU1, hU2, hU3⟩ := hinstc fc hfc fL2 hfae
  have hEfs : ∀ u, (Ef omega).toClosedForm.energy u = limitFormEnergy (sel omega) u := hEf omega
  have hE's : ∀ u, E'.toClosedForm.energy u = limitFormEnergy (sel omega) u := by
    intro u
    rw [hsel]
    exact hE' u
  have hus : sel omega fL2 ∈ E'.toClosedForm.domain := by
    rw [hsel]
    exact hu
  rw [← hsel]
  refine ⟨U, hU1, hU2, fun hr hg hlc => ?_⟩
  have hL1 : (1 : ℝ) ≤ (3 : ℝ) ^ H1 := hLgt1.le
  have hLpos : (0 : ℝ) < (3 : ℝ) ^ H1 := by positivity
  have hrpos : (0 : ℝ) < (3 : ℝ) ^ (-(k : ℤ)) := by positivity
  have hvol := aux_affine_source_cells_env_vol zP z ((3 : ℝ) ^ H1) ((3 : ℝ) ^ (-(k : ℤ)))
    hLpos hrpos
  have hlq := aux_affine_source_cells_env_hyp_transfer
    (centeredCube Qcentre Qside hQside) (sel omega) (Ef omega) E' (Gam omega) Gam' hEfs hE's
    (hcoreEf omega) (sel omega fL2) hus (Metric.ball zP ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-(k : ℤ)) / 2))
    (Metric.ball z ((3 : ℝ) ^ (-(k : ℤ)) / 2)) (((3 : ℝ) ^ H1) ^ d)
    (((3 : ℝ) ^ H1) ^ ((d : ℝ) + zeta)) c q hvol
    (aux_affine_source_cells_env_Ld_le _ zeta hL1 hzeta) hc hq1.le hq2.le hlc
  obtain ⟨pc, hpc⟩ := hU3 hr hg hlq
  refine ⟨pc, ?_⟩
  obtain ⟨Lambda, hglb, hne, hle⟩ := hpc
  exact aux_affine_source_cells_env_concl_transfer (centeredCube Qcentre Qside hQside)
    (sel omega) (Ef omega) E' (Gam omega) Gam' hEfs hE's (hcoreEf omega) (sel omega fL2) hus
    (Metric.ball z ((3 : ℝ) ^ (-(k : ℤ)) / 2)) _ c q rho hc hq1.le hq2.le hrho.le
    ⟨Lambda, hglb, hne, hle⟩

end SubdiffusiveProcess.Paper
end
