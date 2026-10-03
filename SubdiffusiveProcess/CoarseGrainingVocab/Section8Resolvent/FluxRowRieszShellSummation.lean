module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszRepairedInstantiation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionRepairedLevels
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceDecayFluxMoment

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Assumptions
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ} [NeZero d] {base : ℤ}
variable {failure : TriadicCube d → Set (PotentialSample d)}
variable {omega : PotentialSample d}

/-- The unweighted price on the exact `j`-th sphere of the repaired stopping
graph.  This is the sum displayed at manuscript lines 11803--11817, before
multiplication by the graph contraction. -/
def repairedFluxRowRieszRawShell
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsource : source.Nonempty) (R : ℝ)
    (weight : RefinedStoppingCell failure omega base → ℝ) (j : ℕ) : ℝ :=
  ∑ q ∈ stoppingGraphLevelCells repairedStoppingGraph source hsource j,
    ((((3 : ℝ) ^ refinedStoppingScale q) / R) ^ (d + 6)) * weight q

/-- The random factor defined in `e.whole.resolvent.factor.definition`, with
the repaired graph and exact repaired spheres. -/
def repairedFluxRowRieszShellFactor
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsource : source.Nonempty) (R beta : ℝ)
    (weight : RefinedStoppingCell failure omega base → ℝ) : ℝ :=
  1 + ∑' j, beta ^ j *
    repairedFluxRowRieszRawShell source hsource R weight j

/-- The exact repaired shell is nonnegative when its local weights are. -/
theorem repairedFluxRowRieszRawShell_nonneg
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsource : source.Nonempty) {R : ℝ} (hR : 0 < R)
    {weight : RefinedStoppingCell failure omega base → ℝ}
    (hweight : ∀ q, 0 ≤ weight q) (j : ℕ) :
    0 ≤ repairedFluxRowRieszRawShell source hsource R weight j := by
  apply Finset.sum_nonneg
  intro q _hq
  exact mul_nonneg (pow_nonneg (div_nonneg (by positivity) hR.le) _) (hweight q)

/-- The paper's half-distance real power is a geometric sequence in the
integer graph distance. -/
theorem fluxRowRiesz_rpow_half_nat
    {theta : ℝ} (htheta : 0 ≤ theta) (j : ℕ) :
    Real.rpow theta ((j : ℝ) / 2) =
      (Real.rpow theta (1 / 2 : ℝ)) ^ j := by
  calc
    Real.rpow theta ((j : ℝ) / 2) =
        Real.rpow theta ((1 / 2 : ℝ) * (j : ℝ)) := by ring_nf
    _ = Real.rpow (Real.rpow theta (1 / 2 : ℝ)) (j : ℝ) :=
      Real.rpow_mul htheta (1 / 2 : ℝ) (j : ℝ)
    _ = (Real.rpow theta (1 / 2 : ℝ)) ^ j := Real.rpow_natCast _ _

/-- On an exact graph sphere, the sum of the literal per-cell prices factors
as the deterministic PDE scale, the graph contraction, and the raw shell. -/
theorem sum_fluxRowRieszCellPrice_on_repaired_level
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsource : source.Nonempty) (j : ℕ)
    (C ahomValue t R sigma fEnergy theta : ℝ)
    (E1 E2 lambdaInv : RefinedStoppingCell failure omega base → ℝ) :
    (∑ q ∈ stoppingGraphLevelCells repairedStoppingGraph source hsource j,
        fluxRowRieszCellPrice C ahomValue t R sigma fEnergy theta
          ((3 : ℝ) ^ refinedStoppingScale q)
          (stoppingGraphDistance repairedStoppingGraph source hsource q)
          d (E1 q) (E2 q) (lambdaInv q)) =
      C * ahomValue * t⁻¹ * Real.rpow R (2 * sigma) * fEnergy *
        Real.rpow theta ((j : ℝ) / 2) *
        repairedFluxRowRieszRawShell source hsource R
          (fun q ↦ fluxRowRieszCellWeight
            (E1 q) (E2 q) ahomValue (lambdaInv q)) j := by
  let levelCells :=
    stoppingGraphLevelCells repairedStoppingGraph source hsource j
  have hconnected := repairedStoppingGraph_connected failure omega hinitial hrepair
  calc
    (∑ q ∈ levelCells,
        fluxRowRieszCellPrice C ahomValue t R sigma fEnergy theta
          ((3 : ℝ) ^ refinedStoppingScale q)
          (stoppingGraphDistance repairedStoppingGraph source hsource q)
          d (E1 q) (E2 q) (lambdaInv q)) =
      ∑ q ∈ levelCells,
        C * ahomValue * t⁻¹ * Real.rpow R (2 * sigma) * fEnergy *
          Real.rpow theta ((j : ℝ) / 2) *
          ((((3 : ℝ) ^ refinedStoppingScale q) / R) ^ (d + 6)) *
          fluxRowRieszCellWeight (E1 q) (E2 q) ahomValue (lambdaInv q) := by
      apply Finset.sum_congr rfl
      intro q hq
      have hj : stoppingGraphDistance repairedStoppingGraph source hsource q = j :=
        (mem_stoppingGraphLevelCells_iff repairedStoppingGraph hconnected
          hsource j q).1 hq
      rw [fluxRowRieszCellPrice, hj]
    _ = C * ahomValue * t⁻¹ * Real.rpow R (2 * sigma) * fEnergy *
        Real.rpow theta ((j : ℝ) / 2) *
        repairedFluxRowRieszRawShell source hsource R
          (fun q ↦ fluxRowRieszCellWeight
            (E1 q) (E2 q) ahomValue (lambdaInv q)) j := by
      rw [repairedFluxRowRieszRawShell]
      simp only [levelCells, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _hq
      ring

/-- A shell majorant with growth `K D^j` is summable after multiplication by
a graph contraction `beta^j`, provided `beta D < 1`. -/
theorem summable_repairedFluxRowRieszShellMajorant
    {beta D K : ℝ} (hbeta : 0 ≤ beta) (hD : 0 ≤ D)
    (hcontract : beta * D < 1)
    {shell : ℕ → ℝ} (hshell : ∀ j, 0 ≤ shell j)
    (hgrowth : ∀ j, shell j ≤ K * D ^ j) :
    Summable (fun j ↦ beta ^ j * shell j) := by
  simpa using
    (summable_wholeSpaceFluxWeightedSum (Omega := Unit)
      hbeta hD hcontract (shell := fun j (_ : Unit) ↦ shell j)
      (fun j _ ↦ hshell j) (fun j _ ↦ hgrowth j) ())

/-- The geometric shell majorant has its explicit total bound. -/
theorem tsum_repairedFluxRowRieszShellMajorant_le
    {beta D K : ℝ} (hbeta : 0 ≤ beta) (hD : 0 ≤ D)
    (hcontract : beta * D < 1)
    {shell : ℕ → ℝ} (hshell : ∀ j, 0 ≤ shell j)
    (hgrowth : ∀ j, shell j ≤ K * D ^ j) :
    (∑' j, beta ^ j * shell j) ≤ K * (1 - beta * D)⁻¹ := by
  simpa [wholeSpaceFluxWeightedSum] using!
    (wholeSpaceFluxWeightedSum_le_geometric (Omega := Unit)
      hbeta hD hcontract (shell := fun j (_ : Unit) ↦ shell j)
      (fun j _ ↦ hshell j) (fun j _ ↦ hgrowth j) ())

/-- The exact repaired factor is at least one. -/
theorem one_le_repairedFluxRowRieszShellFactor
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsource : source.Nonempty) {R beta : ℝ} (hR : 0 < R)
    (hbeta : 0 ≤ beta)
    {weight : RefinedStoppingCell failure omega base → ℝ}
    (hweight : ∀ q, 0 ≤ weight q) :
    1 ≤ repairedFluxRowRieszShellFactor source hsource R beta weight := by
  unfold repairedFluxRowRieszShellFactor
  apply le_add_of_nonneg_right
  exact tsum_nonneg fun j ↦ mul_nonneg (pow_nonneg hbeta j) <|
    repairedFluxRowRieszRawShell_nonneg source hsource
      hR hweight j

/-- Geometric shell growth gives a pointwise bound for the exact repaired
factor. -/
theorem repairedFluxRowRieszShellFactor_le_geometric
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsource : source.Nonempty) {R beta D K : ℝ}
    (hR : 0 < R) (hbeta : 0 ≤ beta) (hD : 0 ≤ D)
    (hcontract : beta * D < 1)
    {weight : RefinedStoppingCell failure omega base → ℝ}
    (hweight : ∀ q, 0 ≤ weight q)
    (hgrowth : ∀ j,
      repairedFluxRowRieszRawShell source hsource R weight j ≤ K * D ^ j) :
    repairedFluxRowRieszShellFactor source hsource R beta weight ≤
      1 + K * (1 - beta * D)⁻¹ := by
  unfold repairedFluxRowRieszShellFactor
  gcongr
  exact tsum_repairedFluxRowRieszShellMajorant_le hbeta hD hcontract
    (fun j ↦ repairedFluxRowRieszRawShell_nonneg
      source hsource hR hweight j) hgrowth

/-- Finite exact levels transfer a summable shell bound to a bound for the
total price.  This quantitative form complements
`summable_cellPrice_of_stoppingLevel_sums`. -/
theorem tsum_cellPrice_le_tsum_shellPrice_of_stoppingLevel_sums
    {Cell : Type*} [DecidableEq Cell]
    (levelCells : ℕ → Finset Cell) (level : Cell → ℕ)
    (hlevel : ∀ j q, q ∈ levelCells j ↔ level q = j)
    (cellPrice : Cell → ℝ) (hcellPrice : ∀ q, 0 ≤ cellPrice q)
    (shellPrice : ℕ → ℝ) (hshellNonneg : ∀ j, 0 ≤ shellPrice j)
    (hshellSummable : Summable shellPrice)
    (hshell : ∀ j, ∑ q ∈ levelCells j, cellPrice q ≤ shellPrice j) :
    (∑' q, cellPrice q) ≤ ∑' j, shellPrice j := by
  have hpartition : ∀ q, ∃! j, q ∈ (levelCells j : Set Cell) := by
    intro q
    refine ⟨level q, (hlevel (level q) q).2 rfl, ?_⟩
    intro j hj
    exact (hlevel j q).1 hj |>.symm
  have hcellSummable := summable_cellPrice_of_stoppingLevel_sums
    levelCells level hlevel cellPrice hcellPrice shellPrice hshellSummable hshell
  apply (ENNReal.ofReal_le_ofReal_iff
    (tsum_nonneg hshellNonneg)).1
  rw [ENNReal.ofReal_tsum_of_nonneg hcellPrice hcellSummable,
    ENNReal.ofReal_tsum_of_nonneg hshellNonneg hshellSummable]
  calc
    (∑' q, ENNReal.ofReal (cellPrice q)) =
        ∑' x : Σ j, (levelCells j : Set Cell),
          ENNReal.ofReal (cellPrice x.2) := by
      exact (Set.sigmaEquiv (fun j ↦ (levelCells j : Set Cell))
        hpartition).tsum_eq (fun q ↦ ENNReal.ofReal (cellPrice q)) |>.symm
    _ = ∑' j, ∑' q : (levelCells j : Set Cell),
        ENNReal.ofReal (cellPrice q) := ENNReal.tsum_sigma' _
    _ ≤ ∑' j, ENNReal.ofReal (shellPrice j) := by
      apply ENNReal.tsum_le_tsum
      intro j
      calc
        (∑' q : (levelCells j : Set Cell),
            ENNReal.ofReal (cellPrice q)) =
            ∑ q ∈ levelCells j, ENNReal.ofReal (cellPrice q) := by
          simpa using Finset.tsum_subtype' (levelCells j)
            (fun q ↦ ENNReal.ofReal (cellPrice q))
        _ = ENNReal.ofReal (∑ q ∈ levelCells j, cellPrice q) := by
          exact (ENNReal.ofReal_sum_of_nonneg
            (fun q _hq ↦ hcellPrice q)).symm
        _ ≤ ENNReal.ofReal (shellPrice j) :=
          ENNReal.ofReal_le_ofReal (hshell j)

/-- Exact repaired-shell closure, conditional on the local price from item 3
and the shell growth estimate from item 4.  The returned budget has literally
the paper's `theta^(dist/2) (size/R)^(d+6) W_Q` as its cell price. -/
theorem exists_repairedFluxRowRieszCoefficientBudget_of_shell_growth
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (chi : RepairedStoppingCutoff failure omega base)
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsource : source.Nonempty)
    (localNegative : Fin d → RefinedStoppingCell failure omega base → ℝ)
    (Kpair C ahomValue t R sigma fEnergy theta D Kshell : ℝ)
    (E1 E2 lambdaInv : RefinedStoppingCell failure omega base → ℝ)
    (hlocNonneg : ∀ i q, 0 ≤ localNegative i q)
    (hC : 0 ≤ C) (hahom : 0 ≤ ahomValue) (ht : 0 < t) (hR : 0 < R)
    (hfEnergy : 0 ≤ fEnergy) (htheta : 0 ≤ theta) (hD : 0 ≤ D)
    (hcontract : Real.rpow theta (1 / 2 : ℝ) * D < 1)
    (hgrowth : ∀ j,
      repairedFluxRowRieszRawShell source hsource R
          (fun q ↦ fluxRowRieszCellWeight
            (E1 q) (E2 q) ahomValue (lambdaInv q)) j ≤
        Kshell * D ^ j)
    (hlocal : ∀ i q,
      (repairedFluxRowRieszPartition hinitial hrepair chi).cellVolume q *
          localNegative i q ^ 2 ≤
        fluxRowRieszCellPrice C ahomValue t R sigma fEnergy theta
          ((3 : ℝ) ^ refinedStoppingScale q)
          (stoppingGraphDistance repairedStoppingGraph source hsource q)
          d (E1 q) (E2 q) (lambdaInv q)) :
    ∃ B : FluxRowRieszCoefficientBudget
        (repairedFluxRowRieszPartition hinitial hrepair chi) localNegative Kpair,
      (∀ i q,
        B.cellPrice i q =
          fluxRowRieszCellPrice C ahomValue t R sigma fEnergy theta
            ((3 : ℝ) ^ refinedStoppingScale q)
            (stoppingGraphDistance repairedStoppingGraph source hsource q)
            d (E1 q) (E2 q) (lambdaInv q)) ∧
      (∀ i,
        (∑' q, B.cellPrice i q) ≤
          (C * ahomValue * t⁻¹ * Real.rpow R (2 * sigma) * fEnergy) *
            repairedFluxRowRieszShellFactor source hsource R
              (Real.rpow theta (1 / 2 : ℝ))
              (fun q ↦ fluxRowRieszCellWeight
                (E1 q) (E2 q) ahomValue (lambdaInv q))) ∧
      repairedFluxRowRieszShellFactor source hsource R
          (Real.rpow theta (1 / 2 : ℝ))
          (fun q ↦ fluxRowRieszCellWeight
            (E1 q) (E2 q) ahomValue (lambdaInv q)) ≤
        1 + Kshell *
          (1 - Real.rpow theta (1 / 2 : ℝ) * D)⁻¹ := by
  let weight : RefinedStoppingCell failure omega base → ℝ :=
    fun q ↦ fluxRowRieszCellWeight (E1 q) (E2 q) ahomValue (lambdaInv q)
  let rawShell : ℕ → ℝ :=
    repairedFluxRowRieszRawShell source hsource R weight
  let beta : ℝ := Real.rpow theta (1 / 2 : ℝ)
  let pdeScale : ℝ :=
    C * ahomValue * t⁻¹ * Real.rpow R (2 * sigma) * fEnergy
  let cellPrice : Fin d → RefinedStoppingCell failure omega base → ℝ :=
    fun _i q ↦ fluxRowRieszCellPrice C ahomValue t R sigma fEnergy theta
      ((3 : ℝ) ^ refinedStoppingScale q)
      (stoppingGraphDistance repairedStoppingGraph source hsource q)
      d (E1 q) (E2 q) (lambdaInv q)
  let levelCells : ℕ → Finset (RefinedStoppingCell failure omega base) :=
    stoppingGraphLevelCells repairedStoppingGraph source hsource
  let shellPrice : Fin d → ℕ → ℝ :=
    fun _i j ↦ pdeScale * (beta ^ j * rawShell j)
  have hweight : ∀ q, 0 ≤ weight q := by
    intro q
    exact fluxRowRieszCellWeight_nonneg _ _ _ _
  have hrawNonneg : ∀ j, 0 ≤ rawShell j := by
    intro j
    exact repairedFluxRowRieszRawShell_nonneg source hsource hR hweight j
  have hbeta : 0 ≤ beta := Real.rpow_nonneg htheta _
  have hpdeScale : 0 ≤ pdeScale := by
    dsimp only [pdeScale]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg hC hahom) (inv_nonneg.mpr ht.le))
          (Real.rpow_nonneg hR.le _))
      hfEnergy
  have hpriceNonneg : ∀ i q, 0 ≤ cellPrice i q := by
    intro i q
    change 0 ≤ pdeScale *
      Real.rpow theta
        ((stoppingGraphDistance repairedStoppingGraph source hsource q : ℝ) / 2) *
      ((((3 : ℝ) ^ refinedStoppingScale q) / R) ^ (d + 6)) * weight q
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hpdeScale (Real.rpow_nonneg htheta _))
        (pow_nonneg (div_nonneg (by positivity) hR.le) _))
      (hweight q)
  have hlevel : ∀ j q, q ∈ levelCells j ↔
      stoppingGraphDistance repairedStoppingGraph source hsource q = j := by
    intro j q
    exact mem_stoppingGraphLevelCells_iff repairedStoppingGraph
      (repairedStoppingGraph_connected failure omega hinitial hrepair)
      hsource j q
  have hshellSummable : ∀ i, Summable (shellPrice i) := by
    intro i
    have hrawSummable : Summable (fun j ↦ beta ^ j * rawShell j) :=
      summable_repairedFluxRowRieszShellMajorant hbeta hD hcontract
        hrawNonneg hgrowth
    simpa only [shellPrice] using hrawSummable.mul_left pdeScale
  have hshell : ∀ i j,
      ∑ q ∈ levelCells j, cellPrice i q ≤ shellPrice i j := by
    intro i j
    have hfactor := sum_fluxRowRieszCellPrice_on_repaired_level
      hinitial hrepair source hsource j C ahomValue t R sigma fEnergy theta
      E1 E2 lambdaInv
    rw [fluxRowRiesz_rpow_half_nat htheta j] at hfactor
    simpa only [cellPrice, levelCells, shellPrice, pdeScale, beta, rawShell,
      weight, mul_assoc] using hfactor.le
  let B := repairedFluxRowRieszCoefficientBudget hinitial hrepair chi source
    hsource localNegative Kpair hlocNonneg cellPrice hpriceNonneg hlocal
    levelCells hlevel shellPrice hshellSummable hshell
  refine ⟨B, ?_, ?_, ?_⟩
  · intro i q
    rfl
  · intro i
    have htotal : (∑' q, cellPrice i q) ≤ ∑' j, shellPrice i j :=
      tsum_cellPrice_le_tsum_shellPrice_of_stoppingLevel_sums
        levelCells
        (stoppingGraphDistance repairedStoppingGraph source hsource)
        hlevel (cellPrice i) (hpriceNonneg i) (shellPrice i)
        (fun j ↦ mul_nonneg hpdeScale
          (mul_nonneg (pow_nonneg hbeta j) (hrawNonneg j)))
        (hshellSummable i) (hshell i)
    change (∑' q, cellPrice i q) ≤
      pdeScale * (1 + ∑' j, beta ^ j * rawShell j)
    calc
      (∑' q, cellPrice i q) ≤ ∑' j, shellPrice i j := htotal
      _ = pdeScale * ∑' j, beta ^ j * rawShell j := by
        rw [tsum_mul_left]
      _ ≤ pdeScale * (1 + ∑' j, beta ^ j * rawShell j) := by
        gcongr
        exact le_add_of_nonneg_left (by norm_num)
  · exact repairedFluxRowRieszShellFactor_le_geometric source hsource hR
      hbeta hD hcontract hweight hgrowth

omit [NeZero d] in
/-- The coordinate sum in the Fourier-space Riesz estimate has the exact
whole-space scaling once each coordinate price is bounded by the same repaired
shell factor. -/
theorem repairedFluxRowRieszCoefficientPriceSum_le
    {Cell : Type*} [Encodable Cell]
    (overlapCount : ℕ) (fourierComparison C CSigma Z : ℝ)
    (cellPrice : Fin d → Cell → ℝ) (physicalScale : ℝ)
    (hfourier : 0 ≤ fourierComparison)
    (hZ : 0 ≤ Z) (hphysical : 0 ≤ physicalScale)
    (hcell : ∀ i,
      (∑' q, cellPrice i q) ≤ C * physicalScale * Z)
    (hconstant :
      2 * (d : ℝ) * overlapCount * fourierComparison * C ≤ CSigma) :
    (∑ i, 2 * ((overlapCount : ℝ) * fourierComparison) *
        ∑' q, cellPrice i q) ≤
      CSigma * Z * physicalScale := by
  have hfront : 0 ≤ 2 * ((overlapCount : ℝ) * fourierComparison) := by
    positivity
  calc
    (∑ i, 2 * ((overlapCount : ℝ) * fourierComparison) *
        ∑' q, cellPrice i q) ≤
        ∑ _i : Fin d,
          2 * ((overlapCount : ℝ) * fourierComparison) *
            (C * physicalScale * Z) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact mul_le_mul_of_nonneg_left (hcell i) hfront
    _ = (2 * (d : ℝ) * overlapCount * fourierComparison * C) *
        Z * physicalScale := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp only [Finset.card_univ, Fintype.card_fin]
      ring
    _ ≤ CSigma * Z * physicalScale := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hconstant hZ) hphysical

omit [NeZero d] in
/-- Exact specialization of the coordinate-price bound to the whole-space
resolvent scale appearing in the frozen flux row. -/
theorem repairedFluxRowRieszCoefficientPriceSum_le_wholeSpaceScale
    {Cell : Type*} [Encodable Cell]
    (M : GMCModel d) (L : ℕ) (overlapCount : ℕ)
    (fourierComparison C CSigma Z t R sigma : ℝ) (f : Vec d → ℝ)
    (cellPrice : Fin d → Cell → ℝ)
    (hfourier : 0 ≤ fourierComparison) (hZ : 1 ≤ Z)
    (ht : 0 < t) (hR : 0 < R)
    (hcell : ∀ i,
      (∑' q, cellPrice i q) ≤
        C * (ahom M L * t⁻¹ * Real.rpow R (2 * sigma) *
          ∫ x, f x ^ 2 ∂volume) * Z)
    (hconstant :
      2 * (d : ℝ) * overlapCount * fourierComparison * C ≤ CSigma) :
    (∑ i, 2 * ((overlapCount : ℝ) * fourierComparison) *
        ∑' q, cellPrice i q) ≤
      CSigma * Z * ahom M L * t⁻¹ * Real.rpow R (2 * sigma) *
        ∫ x, f x ^ 2 ∂volume := by
  have hphysical : 0 ≤ ahom M L * t⁻¹ * Real.rpow R (2 * sigma) *
      ∫ x, f x ^ 2 ∂volume := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (ahom_pos M L).le (inv_nonneg.mpr ht.le))
          (Real.rpow_nonneg hR.le _))
      (integral_nonneg fun x ↦ sq_nonneg (f x))
  have hbound := repairedFluxRowRieszCoefficientPriceSum_le
    overlapCount fourierComparison C CSigma Z cellPrice
    (ahom M L * t⁻¹ * Real.rpow R (2 * sigma) *
      ∫ x, f x ^ 2 ∂volume)
    hfourier (zero_le_one.trans hZ) hphysical hcell hconstant
  simpa only [mul_assoc] using hbound

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
