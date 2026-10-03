module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor.CellEnvelope

@[expose] public section




open MeasureTheory Homogenization Homogenization.Book Filter
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure
open SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold
open SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-! ## The dependent transport -/

/-- The weak Hessian of a family's Neumann member, named.  `toCellFamily`
builds this internally; exposing it is what lets the cell size be transported
along a cube equation. -/
def nfFamilyNeumannHessian {d : ℕ} {ι Omega : Type*} [MeasurableSpace Omega]
    {s : Finset ι} {cell : ι → TriadicCube d}
    (F : OneStepTwoRadiusNeumannHessianFamily d ι Omega s cell)
    (i : ι) (omega : Omega) :
    HasWeakHessianOn (openCubeSet (cell i)) (F.neumann i omega) :=
  weakHessianOfGradEqAddAdd (F.grad_split i omega)
    (F.dirichletHessian i omega) (F.localHarmonicHessian i omega)
    (F.outerHarmonicHessian i omega)

theorem toCellFamily_neumann_eq_oneStepCellB
    {d : ℕ} {ι Omega : Type*} [MeasurableSpace Omega]
    {s : Finset ι} {cell : ι → TriadicCube d}
    (F : OneStepTwoRadiusNeumannHessianFamily d ι Omega s cell)
    (i : ι) (omega : Omega) :
    F.toCellFamily.neumann i omega =
      oneStepCellB (cell i) (nfFamilyNeumannHessian F i omega) := rfl

/-- **The dependent transport.**  On a cell reached by the family, the
family's Sobolev datum and cell size are available at that cell. -/
theorem exists_cellHessian_of_cell_eq
    {d : ℕ} {ι Omega : Type*} [MeasurableSpace Omega]
    {s : Finset ι} {cell : ι → TriadicCube d}
    (F : OneStepTwoRadiusNeumannHessianFamily d ι Omega s cell)
    {i : ι} {R : TriadicCube d} (hi : cell i = R) (omega : Omega) :
    ∃ (uR : H1Function (openCubeSet R))
      (HR : HasWeakHessianOn (openCubeSet R) uR),
      uR.grad = (F.neumann i omega).grad ∧
      oneStepCellB R HR = F.toCellFamily.neumann i omega := by
  subst hi
  exact ⟨F.neumann i omega, nfFamilyNeumannHessian F i omega, rfl,
    (toCellFamily_neumann_eq_oneStepCellB F i omega).symm⟩

/-! ## The glued cell half-energy, as a function of the sample -/

/-- The glued cell half-energy at the canonical ellipticity witness. -/
def dualGluedCellHalfEnergyAt {d K : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (q : Homogenization.Vec d) (hh : 0 < h)
    (R : TriadicCube d) (omega : Sample d) : ℝ :=
  paperGluedCellHalfEnergy M n h q omega hh
    (dualParentEllipticityData_descendants M (n + h) omega
      (originCube d (K : ℤ)) (K - oneStepLocalizationScale n M.delta)) R

theorem dualGluedCellHalfEnergyAt_nonneg {d K : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (q : Homogenization.Vec d) (hh : 0 < h)
    (R : TriadicCube d) (omega : Sample d) :
    0 ≤ dualGluedCellHalfEnergyAt (K := K) M n h q hh R omega :=
  paperGluedCellHalfEnergy_nonneg M n h q omega hh _ R




/-- The pathwise seam identified by provider-22: the glued cell half-energy is
dominated by a local cutoff envelope in `L⁴` times the ambient cell energy of
the manuscript flux. -/
def DualGluedCellPathwiseEnvelope (d : ℕ) [NeZero d] : Prop :=
  ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ),
    ∃ CW : ℝ, 0 ≤ CW ∧
      ∀ (K : ℕ) (q : Vec d),
      vecNormSq q = 1 → ∀ hh : 0 < h, (h : ℝ) ≤ M.delta⁻¹ →
        16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n →
        oneStepLocalizationScale n M.delta ≤ K →
        ∃ W : TriadicCube d → Sample d → ℝ,
          (∀ R ∈ oneStepSourceCells d K n M.delta, ∀ omega, 0 ≤ W R omega) ∧
          (∀ R ∈ oneStepSourceCells d K n M.delta,
            MemLp (W R) 4 M.P.toMeasure) ∧
          (∀ R ∈ oneStepSourceCells d K n M.delta,
            ∫ omega, W R omega ^ (4 : ℕ) ∂M.P.toMeasure ≤ CW) ∧
          (∀ R ∈ oneStepSourceCells d K n M.delta,
            AEStronglyMeasurable
              (dualGluedCellHalfEnergyAt (K := K) M n h q hh R)
              M.P.toMeasure) ∧
          (∀ R ∈ oneStepSourceCells d K n M.delta, ∀ omega,
            dualGluedCellHalfEnergyAt (K := K) M n h q hh R omega ≤
              W R omega * cubeAverage R (fun x ↦ vecNormSq
                (oneStepPaperNeumannFlux M n h q
                  (originCube d (K : ℤ)) omega hh x)))

/-- The exponent-**four** twin of
`exists_oneStepPaperNeumannSourceCellEnergy_two_budget`. -/
def PaperNeumannSourceCellEnergyFourthBudget (d : ℕ) [NeZero d] : Prop :=
  ∃ a : ℝ, 0 ≤ a ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h K : ℕ) (q : Vec d)
      (hh : 0 < h), vecNormSq q = 1 → (h : ℝ) ≤ M.delta⁻¹ →
      (∀ R ∈ oneStepSourceCells d K n M.delta,
        MemLp (fun omega ↦ cubeAverage R (fun x ↦ vecNormSq
          (oneStepPaperNeumannFlux M n h q
            (originCube d (K : ℤ)) omega hh x))) 4 M.P.toMeasure) ∧
      ((((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          ∫ omega, (cubeAverage R (fun x ↦ vecNormSq
            (oneStepPaperNeumannFlux M n h q
              (originCube d (K : ℤ)) omega hh x))) ^ (4 : ℕ)
            ∂M.P.toMeasure ≤ a ^ (4 : ℕ))

/-- The normalized second moment that `BoundaryLayer.lean` consumes. -/
def DualGluedCellSecondMoment (d : ℕ) [NeZero d] : Prop :=
  ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ),
    ∃ C : ℝ,
      ∀ (K : ℕ) (q : Vec d),
      vecNormSq q = 1 → ∀ hh : 0 < h, (h : ℝ) ≤ M.delta⁻¹ →
        16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n →
        oneStepLocalizationScale n M.delta ≤ K →
        (∀ R ∈ oneStepSourceCells d K n M.delta,
          Integrable (dualGluedCellHalfEnergyAt (K := K) M n h q hh R)
            M.P.toMeasure) ∧
        Integrable (fun omega ↦
          (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
            ∑ R ∈ oneStepSourceCells d K n M.delta,
              dualGluedCellHalfEnergyAt (K := K) M n h q hh R omega ^ (2 : ℕ))
          M.P.toMeasure ∧
        (∫ omega, (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
            ∑ R ∈ oneStepSourceCells d K n M.delta,
              dualGluedCellHalfEnergyAt (K := K) M n h q hh R omega ^ (2 : ℕ)
          ∂M.P.toMeasure ≤ C)



theorem dualGluedCellSecondMoment_of_pathwise_and_fourthBudget
    (d : ℕ) [NeZero d]
    (hpath : DualGluedCellPathwiseEnvelope d)
    (hfour : PaperNeumannSourceCellEnergyFourthBudget d) :
    DualGluedCellSecondMoment d := by
  classical
  obtain ⟨a, ha0, hE⟩ := hfour
  intro M n h
  obtain ⟨CW, hCW0, hW⟩ := hpath M n h
  refine ⟨Real.sqrt CW * a ^ (2 : ℕ), ?_⟩
  intro K q hq hh hblock hsource hK
  haveI : IsProbabilityMeasure M.P.toMeasure := M.P.prop
  letI : ENNReal.HolderTriple (4 : ℝ≥0∞) (4 : ℝ≥0∞) (2 : ℝ≥0∞) := ⟨by
    rw [← two_mul]
    have h4 : (4 : ℝ≥0∞) = 2 * 2 := by norm_num
    rw [h4, ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num),
      one_mul]⟩
  letI : ENNReal.HolderTriple (2 : ℝ≥0∞) (2 : ℝ≥0∞) (1 : ℝ≥0∞) := ⟨by
    rw [inv_one, ← two_mul,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]⟩
  obtain ⟨W, hW0, hWmem, hWbudget, hYmeas, hYle⟩ :=
    hW K q hq hh hblock hsource hK
  obtain ⟨hEmem, hEbudget⟩ := hE M n h K q hh hq hblock
  set cells := oneStepSourceCells d K n M.delta with hcells
  set E : TriadicCube d → Sample d → ℝ := fun R omega ↦
    cubeAverage R (fun x ↦ vecNormSq
      (oneStepPaperNeumannFlux M n h q (originCube d (K : ℤ)) omega hh x))
    with hEdef
  set Y : TriadicCube d → Sample d → ℝ := fun R omega ↦
    dualGluedCellHalfEnergyAt (K := K) M n h q hh R omega with hYdef
  have hY0 : ∀ R omega, 0 ≤ Y R omega := fun R omega ↦
    dualGluedCellHalfEnergyAt_nonneg M n h q hh R omega
  have hE0 : ∀ R omega, 0 ≤ E R omega := fun _R _omega ↦
    cubeAverage_nonneg_of_nonneg_on fun _x _ ↦ vecNormSq_nonneg _
  have hWmem2 : ∀ R ∈ cells, MemLp (W R) 2 M.P.toMeasure := fun R hR ↦
    (hWmem R hR).mono_exponent (by norm_num)
  have hEmem2 : ∀ R ∈ cells, MemLp (E R) 2 M.P.toMeasure := fun R hR ↦
    (hEmem R hR).mono_exponent (by norm_num)
  have hWsq : ∀ R ∈ cells,
      MemLp (fun omega ↦ W R omega ^ (2 : ℕ)) 2 M.P.toMeasure := by
    intro R hR
    simpa only [pow_two] using! (hWmem R hR).mul (hWmem R hR) (r := (2 : ℝ≥0∞))
  have hEsq : ∀ R ∈ cells,
      MemLp (fun omega ↦ E R omega ^ (2 : ℕ)) 2 M.P.toMeasure := by
    intro R hR
    simpa only [pow_two] using! (hEmem R hR).mul (hEmem R hR) (r := (2 : ℝ≥0∞))
  have hWEint : ∀ R ∈ cells,
      Integrable (fun omega ↦ W R omega * E R omega) M.P.toMeasure :=
    fun R hR ↦ (hWmem2 R hR).integrable_mul (hEmem2 R hR)
  have hWEsqInt : ∀ R ∈ cells,
      Integrable (fun omega ↦ W R omega ^ (2 : ℕ) * E R omega ^ (2 : ℕ))
        M.P.toMeasure := fun R hR ↦ (hWsq R hR).integrable_mul (hEsq R hR)
  have hYint : ∀ R ∈ cells, Integrable (Y R) M.P.toMeasure := by
    intro R hR
    refine Integrable.mono' (hWEint R hR) (hYmeas R hR) ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (hY0 R omega)]
    exact hYle R hR omega
  have hYsqInt : ∀ R ∈ cells,
      Integrable (fun omega ↦ Y R omega ^ (2 : ℕ)) M.P.toMeasure := by
    intro R hR
    refine Integrable.mono' (hWEsqInt R hR) ((hYmeas R hR).pow 2) ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ Y R omega ^ (2 : ℕ))]
    have hle := hYle R hR omega
    nlinarith [hY0 R omega, hW0 R hR omega, hE0 R omega]
  -- cellwise Cauchy--Schwarz in the sample
  have hcellsq : ∀ R ∈ cells,
      ∫ omega, Y R omega ^ (2 : ℕ) ∂M.P.toMeasure ≤
        Real.sqrt CW *
          Real.sqrt (∫ omega, E R omega ^ (4 : ℕ) ∂M.P.toMeasure) := by
    intro R hR
    have hstep1 : ∫ omega, Y R omega ^ (2 : ℕ) ∂M.P.toMeasure ≤
        ∫ omega, W R omega ^ (2 : ℕ) * E R omega ^ (2 : ℕ)
          ∂M.P.toMeasure := by
      refine integral_mono (hYsqInt R hR) (hWEsqInt R hR) fun omega ↦ ?_
      have hle := hYle R hR omega
      nlinarith [hY0 R omega, hW0 R hR omega, hE0 R omega]
    have hWfour : Integrable
        (fun omega ↦ (W R omega ^ (2 : ℕ)) ^ 2) M.P.toMeasure :=
      (memLp_two_iff_integrable_sq (hWsq R hR).aestronglyMeasurable).1
        (hWsq R hR)
    have hEfour : Integrable
        (fun omega ↦ (E R omega ^ (2 : ℕ)) ^ 2) M.P.toMeasure :=
      (memLp_two_iff_integrable_sq (hEsq R hR).aestronglyMeasurable).1
        (hEsq R hR)
    have hcs :=
      Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.integral_mul_le_sqrt_integral_sq_mul_sqrt_integral_sq_of_ae_nonneg
        hWfour hEfour
        (Filter.Eventually.of_forall fun omega ↦ by positivity)
        (Filter.Eventually.of_forall fun omega ↦ by positivity)
    have hWrw : ∫ omega, (W R omega ^ (2 : ℕ)) ^ 2 ∂M.P.toMeasure =
        ∫ omega, W R omega ^ (4 : ℕ) ∂M.P.toMeasure := by
      refine integral_congr_ae ?_
      filter_upwards with omega
      ring
    have hErw : ∫ omega, (E R omega ^ (2 : ℕ)) ^ 2 ∂M.P.toMeasure =
        ∫ omega, E R omega ^ (4 : ℕ) ∂M.P.toMeasure := by
      refine integral_congr_ae ?_
      filter_upwards with omega
      ring
    rw [hWrw, hErw] at hcs
    refine hstep1.trans (hcs.trans ?_)
    exact mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt (hWbudget R hR)) (Real.sqrt_nonneg _)
  -- normalized sum
  have hcard0 : (0 : ℝ) ≤ ((cells.card : ℝ))⁻¹ := by positivity
  have hsum := Finset.sum_le_sum hcellsq
  have hstep := mul_le_mul_of_nonneg_left hsum hcard0
  rw [← Finset.mul_sum] at hstep
  have hjensen : ((cells.card : ℝ))⁻¹ *
      ∑ R ∈ cells,
        Real.sqrt (∫ omega, E R omega ^ (4 : ℕ) ∂M.P.toMeasure) ≤
      Real.sqrt (((cells.card : ℝ))⁻¹ *
        ∑ R ∈ cells, ∫ omega, E R omega ^ (4 : ℕ) ∂M.P.toMeasure) := by
    have hbase := normalized_partial_sum_le_sqrt_fraction_mul_sqrt
      cells cells (fun _R hR ↦ hR)
      (fun R ↦ Real.sqrt (∫ omega, E R omega ^ (4 : ℕ) ∂M.P.toMeasure))
      (fun _R _ ↦ Real.sqrt_nonneg _)
    have hone : ((cells.card : ℝ)) / ((cells.card : ℝ)) = 1 := by
      have : (0 : ℝ) < (cells.card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr
          (oneStepSourceCells_nonempty d K n M.delta)
      field_simp
    rw [hone, Real.sqrt_one, one_mul] at hbase
    refine hbase.trans (le_of_eq ?_)
    congr 1
    refine congrArg (fun z ↦ ((cells.card : ℝ))⁻¹ * z) ?_
    exact Finset.sum_congr rfl fun R _ ↦
      Real.sq_sqrt (integral_nonneg fun omega ↦ by positivity)
  have hfinal : ((cells.card : ℝ))⁻¹ *
      ∑ R ∈ cells, ∫ omega, Y R omega ^ (2 : ℕ) ∂M.P.toMeasure ≤
      Real.sqrt CW * a ^ (2 : ℕ) := by
    refine hstep.trans ?_
    rw [show ((cells.card : ℝ))⁻¹ * (Real.sqrt CW *
        ∑ R ∈ cells,
          Real.sqrt (∫ omega, E R omega ^ (4 : ℕ) ∂M.P.toMeasure)) =
        Real.sqrt CW * (((cells.card : ℝ))⁻¹ *
          ∑ R ∈ cells,
            Real.sqrt (∫ omega, E R omega ^ (4 : ℕ) ∂M.P.toMeasure))
      from by ring]
    refine (mul_le_mul_of_nonneg_left hjensen (Real.sqrt_nonneg CW)).trans ?_
    have hbudget : Real.sqrt (((cells.card : ℝ))⁻¹ *
        ∑ R ∈ cells, ∫ omega, E R omega ^ (4 : ℕ) ∂M.P.toMeasure) ≤
        a ^ (2 : ℕ) := by
      have := Real.sqrt_le_sqrt hEbudget
      calc _ ≤ Real.sqrt (a ^ (4 : ℕ)) := this
        _ = a ^ (2 : ℕ) := by
            rw [show a ^ (4 : ℕ) = (a ^ (2 : ℕ)) ^ 2 by ring]
            exact Real.sqrt_sq (by positivity)
    exact mul_le_mul_of_nonneg_left hbudget (Real.sqrt_nonneg CW)
  have hsumInt : Integrable (fun omega ↦ ((cells.card : ℝ))⁻¹ *
      ∑ R ∈ cells, Y R omega ^ (2 : ℕ)) M.P.toMeasure :=
    (MeasureTheory.integrable_finset_sum cells hYsqInt).const_mul _
  refine ⟨hYint, hsumInt, ?_⟩
  rw [integral_const_mul, integral_finset_sum cells hYsqInt]
  exact hfinal

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor
