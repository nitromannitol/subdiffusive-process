module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.LiteralSupMeasurability
public import SubdiffusiveProcess.Assumptions.Sample
public import SubdiffusiveProcess.Assumptions.PotentialField
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.AccumulatedErrorResponse
public import SubdiffusiveProcess.Frozen.Section6.Defs.AccumulatedError

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Assumptions

noncomputable section

/-- The literal cube supremum of a shell potential is measurable in the sample.
This is the third term of `accumulatedError` (at `i = 0`), and the shape every
`shellBlock`-style carrier reduces to. -/
theorem measurable_supNormOn_translatedCube_potentialCoordinate
    {d : ℕ} (k : ℤ) (z : Vec d) (i : ℕ) :
    Measurable (fun omega : PotentialSample d ↦
      supNormOn (translatedCube d k z) (omega i)) :=
  measurable_supNormOn_of_continuous
    (isOpen_translatedCube d k z) (isBounded_translatedCube d k z)
    (fun omega ↦ (PotentialField.contDiff_one (omega i)).continuous)
    (fun x ↦ (PotentialField.measurable_eval x).comp
      (measurable_potentialCoordinate i))

/-- The same over the untranslated cube. -/
theorem measurable_supNormOn_cube_potentialCoordinate
    {d : ℕ} (k : ℤ) (i : ℕ) :
    Measurable (fun omega : PotentialSample d ↦
      supNormOn (cube d k) (omega i)) :=
  measurable_supNormOn_of_continuous
    (isOpen_cube d k) (isBounded_cube d k)
    (fun omega ↦ (PotentialField.contDiff_one (omega i)).continuous)
    (fun x ↦ (PotentialField.measurable_eval x).comp
      (measurable_potentialCoordinate i))

/-! ## The shell-block carrier

`shellBlock m j omega x = ∑ i ∈ Finset.Icc (j + 1) m, omega i x`.  As with the
gradient, `shellBlock_continuous` exists four times in the repo, `private` each
time; re-proved publicly here. -/

theorem continuous_shellBlock {d : ℕ} (m j : ℕ) (omega : PotentialSample d) :
    Continuous (shellBlock m j omega) := by
  unfold shellBlock
  fun_prop

theorem measurable_shellBlock_eval {d : ℕ} (m j : ℕ) (x : Vec d) :
    Measurable (fun omega : PotentialSample d ↦ shellBlock m j omega x) := by
  unfold shellBlock
  exact Finset.measurable_sum _ fun i _ ↦
    (PotentialField.measurable_eval x).comp (measurable_potentialCoordinate i)

/-- The literal cube supremum of a shell block is measurable in the sample.
This is the second term of `accumulatedError`, before its (finite) outer sup
over `j ≤ k`. -/
theorem measurable_supNormOn_translatedCube_shellBlock
    {d : ℕ} (k : ℤ) (z : Vec d) (m j : ℕ) :
    Measurable (fun omega : PotentialSample d ↦
      supNormOn (translatedCube d k z) (shellBlock m j omega)) :=
  measurable_supNormOn_of_continuous
    (isOpen_translatedCube d k z) (isBounded_translatedCube d k z)
    (fun omega ↦ continuous_shellBlock m j omega)
    (fun x ↦ measurable_shellBlock_eval m j x)




theorem continuous_shellGradient {d : ℕ} (g : PotentialField d) :
    Continuous (shellGradient g) := by
  unfold shellGradient
  apply continuous_pi
  intro i
  exact (PotentialField.deriv g).continuous.clm_apply continuous_const

theorem continuous_euclideanNorm {d : ℕ} :
    Continuous (Homogenization.euclideanNorm (d := d)) := by
  rw [show (Homogenization.euclideanNorm (d := d)) =
      fun x ↦ ‖Homogenization.HilbertVec.ofVec x‖ by
    funext x
    rw [Homogenization.euclideanNorm_eq_norm_ofVec]]
  exact continuous_norm.comp (Homogenization.HilbertVec.ofVecL d).continuous

theorem measurable_shellGradient_eval {d : ℕ} (x : Vec d) (i : ℕ) :
    Measurable (fun omega : PotentialSample d ↦ shellGradient (omega i) x) := by
  unfold shellGradient
  apply measurable_pi_lambda
  intro j
  exact ((PotentialField.continuous_eval_deriv x).clm_apply
    continuous_const).measurable.comp (measurable_potentialCoordinate i)

/-- The literal cube supremum of a shell gradient is measurable in the sample.
This is the fourth (tail) term of `accumulatedError`. -/
theorem measurable_vectorSupNormOn_translatedCube_shellGradient
    {d : ℕ} (k : ℤ) (z : Vec d) (i : ℕ) :
    Measurable (fun omega : PotentialSample d ↦
      vectorSupNormOn (translatedCube d k z) (shellGradient (omega i))) :=
  measurable_vectorSupNormOn_of_continuous
    (isOpen_translatedCube d k z) (isBounded_translatedCube d k z)
    (fun omega ↦ continuous_shellGradient (omega i))
    (fun x ↦ measurable_shellGradient_eval x i)
    continuous_euclideanNorm
    continuous_euclideanNorm.measurable

/-! ## Triadic-grid coordinates

`OnTriadicGrid l w ↔ ∀ i, ∃ n : ℤ, w i = 3 ^ l * n`, so the scale-`l` grid is the
image of `Fin d → ℤ` — **countable**.  That is what turns the response term's
outer supremum, which quantifies over centres `z' : Vec d`, into a supremum over
a countable index. -/

/-- The scale-`l` triadic grid point with integer coordinates `n`. -/
def gridPoint {d : ℕ} (l : ℕ) (n : Fin d → ℤ) : Vec d :=
  fun i ↦ (3 : ℝ) ^ l * (n i : ℝ)

theorem onTriadicGrid_gridPoint {d : ℕ} (l : ℕ) (n : Fin d → ℤ) :
    OnTriadicGrid l (gridPoint l n) := fun i ↦ ⟨n i, rfl⟩

theorem exists_gridPoint_of_onTriadicGrid {d : ℕ} {l : ℕ} {w : Vec d}
    (h : OnTriadicGrid l w) : ∃ n : Fin d → ℤ, gridPoint l n = w := by
  choose n hn using h
  exact ⟨n, funext fun i ↦ (hn i).symm⟩

/-! ## The response term -/

/-- **The first term of `accumulatedError`.**  Its outer supremum ranges over
scales `j, l` and centres `z'` on the scale-`l` triadic grid; reindexing the
centres by their integer coordinates makes the index countable, and the inner
unit-sphere supremum is supplied by the landed
`Section6Stopping.measurable_sSup_section6Response_unitSphere`.

The uniform bound is easy: `√(min X 1) ≤ 1`, and the finitely many prefactors
`3 ^ (-(s/2)(k-l))` with `l ≤ k` are dominated by their sum. -/
theorem measurable_accumulatedErrorResponseTerm {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (cutoff : Option ℕ)
    (k : ℕ) (z : Vec d) (s : ℝ) :
    Measurable (fun omega : PotentialSample d ↦
      sSup {r : ℝ | ∃ j l : ℕ, j ≤ k ∧ l + 2 ≤ j ∧
        ∃ z' : Vec d, OnTriadicGrid l (z' - z) ∧
          z' - z ∈ cube d (j : ℤ) \ cube d ((j : ℤ) - 1) ∧
          r = (3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ))) *
            Real.sqrt (min (sSup {t : ℝ | ∃ e : Vec d,
              Homogenization.vecNormSq e = 1 ∧
              t = section6Response M l (min l (cutoff.getD l)) omega z' e}) 1)}) := by
  classical
  let Adm : ℕ × ℕ × (Fin d → ℤ) → Prop := fun p ↦
    p.1 ≤ k ∧ p.2.1 + 2 ≤ p.1 ∧
      gridPoint p.2.1 p.2.2 ∈ cube d (p.1 : ℤ) \ cube d ((p.1 : ℤ) - 1)
  let g : {p : ℕ × ℕ × (Fin d → ℤ) // Adm p} → PotentialSample d → ℝ :=
    fun p omega ↦
      (3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - ((p : ℕ × ℕ × (Fin d → ℤ)).2.1 : ℝ))) *
        Real.sqrt (min (sSup {t : ℝ | ∃ e : Vec d,
          Homogenization.vecNormSq e = 1 ∧
          t = section6Response M (p : ℕ × ℕ × (Fin d → ℤ)).2.1
            (min (p : ℕ × ℕ × (Fin d → ℤ)).2.1
              (cutoff.getD (p : ℕ × ℕ × (Fin d → ℤ)).2.1)) omega
            (z + gridPoint (p : ℕ × ℕ × (Fin d → ℤ)).2.1
              (p : ℕ × ℕ × (Fin d → ℤ)).2.2) e}) 1)
  have hgmeas : ∀ p, Measurable (g p) := by
    intro p
    refine Measurable.const_mul ?_ _
    exact ((Section6Stopping.measurable_sSup_section6Response_unitSphere M _ _ _).min
      measurable_const).sqrt
  have hS : ∀ omega : PotentialSample d,
      {r : ℝ | ∃ j l : ℕ, j ≤ k ∧ l + 2 ≤ j ∧
        ∃ z' : Vec d, OnTriadicGrid l (z' - z) ∧
          z' - z ∈ cube d (j : ℤ) \ cube d ((j : ℤ) - 1) ∧
          r = (3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ))) *
            Real.sqrt (min (sSup {t : ℝ | ∃ e : Vec d,
              Homogenization.vecNormSq e = 1 ∧
              t = section6Response M l (min l (cutoff.getD l)) omega z' e}) 1)} =
        {a : ℝ | ∃ p, g p omega = a} := by
    intro omega
    ext a
    constructor
    · rintro ⟨j, l, hjk, hlj, z', hgrid, hmem, rfl⟩
      obtain ⟨n, hn⟩ := exists_gridPoint_of_onTriadicGrid hgrid
      refine ⟨⟨(j, l, n), hjk, hlj, ?_⟩, ?_⟩
      · rw [hn]; exact hmem
      · simp only [g]
        rw [hn, add_sub_cancel]
    · rintro ⟨p, rfl⟩
      obtain ⟨⟨j, l, n⟩, hjk, hlj, hmem⟩ := p
      refine ⟨j, l, hjk, hlj, z + gridPoint l n, ?_, ?_, ?_⟩
      · rw [add_sub_cancel_left]; exact onTriadicGrid_gridPoint l n
      · rw [add_sub_cancel_left]; exact hmem
      · simp only [g]
  have hbdd : ∀ omega : PotentialSample d,
      BddAbove {r : ℝ | ∃ j l : ℕ, j ≤ k ∧ l + 2 ≤ j ∧
        ∃ z' : Vec d, OnTriadicGrid l (z' - z) ∧
          z' - z ∈ cube d (j : ℤ) \ cube d ((j : ℤ) - 1) ∧
          r = (3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ))) *
            Real.sqrt (min (sSup {t : ℝ | ∃ e : Vec d,
              Homogenization.vecNormSq e = 1 ∧
              t = section6Response M l (min l (cutoff.getD l)) omega z' e}) 1)} := by
    intro omega
    refine ⟨∑ l ∈ Finset.range (k + 1),
      (3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ))), ?_⟩
    rintro r ⟨j, l, hjk, hlj, z', hgrid, hmem, rfl⟩
    have hl : l ≤ k := by omega
    have hsqrt : Real.sqrt (min (sSup {t : ℝ | ∃ e : Vec d,
        Homogenization.vecNormSq e = 1 ∧
        t = section6Response M l (min l (cutoff.getD l)) omega z' e}) 1) ≤ 1 := by
      exact Real.sqrt_le_one.mpr (min_le_right _ _)
    have hpow : (0 : ℝ) < (3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ))) :=
      Real.rpow_pos_of_pos (by norm_num) _
    calc (3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ))) *
          Real.sqrt (min (sSup {t : ℝ | ∃ e : Vec d,
            Homogenization.vecNormSq e = 1 ∧
            t = section6Response M l (min l (cutoff.getD l)) omega z' e}) 1)
        ≤ (3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ))) * 1 :=
          mul_le_mul_of_nonneg_left hsqrt hpow.le
      _ = (3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ))) := mul_one _
      _ ≤ ∑ l' ∈ Finset.range (k + 1),
            (3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l' : ℝ))) :=
          Finset.single_le_sum
            (f := fun l' : ℕ ↦ (3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l' : ℝ))))
            (fun i _ ↦ (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 3) _).le)
            (Finset.mem_range.mpr (Nat.lt_succ_of_le hl))
  exact measurable_sSup_of_countable_range' hgmeas hS hbdd

/-! ## The block and tail terms, and the assembly -/

/-- **The second term of `accumulatedError`.**  Finite index `j ≤ k`, so the
value set is finite and `BddAbove` is free. -/
theorem measurable_accumulatedErrorBlockTerm {d : ℕ} (k : ℕ) (z : Vec d) (s : ℝ) :
    Measurable (fun omega : PotentialSample d ↦
      sSup {r : ℝ | ∃ j ≤ k,
        r = (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) *
          supNormOn (translatedCube d (k : ℤ) z) (shellBlock k j omega)}) := by
  classical
  let g : Fin (k + 1) → PotentialSample d → ℝ := fun i omega ↦
    (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (((i : ℕ) : ℝ)))) *
      supNormOn (translatedCube d (k : ℤ) z) (shellBlock k (i : ℕ) omega)
  have hgmeas : ∀ i, Measurable (g i) := fun i ↦
    Measurable.const_mul
      (measurable_supNormOn_translatedCube_shellBlock (k : ℤ) z k (i : ℕ)) _
  have hS : ∀ omega : PotentialSample d,
      {r : ℝ | ∃ j ≤ k,
        r = (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) *
          supNormOn (translatedCube d (k : ℤ) z) (shellBlock k j omega)} =
        {a : ℝ | ∃ i, g i omega = a} := by
    intro omega
    ext a
    constructor
    · rintro ⟨j, hjk, rfl⟩
      exact ⟨⟨j, Nat.lt_succ_of_le hjk⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨(i : ℕ), Nat.lt_succ_iff.mp i.2, rfl⟩
  have hbdd : ∀ omega : PotentialSample d,
      BddAbove {r : ℝ | ∃ j ≤ k,
        r = (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) *
          supNormOn (translatedCube d (k : ℤ) z) (shellBlock k j omega)} := by
    intro omega
    rw [hS omega]
    exact (Set.finite_range (fun i ↦ g i omega)).bddAbove
  exact measurable_sSup_of_countable_range' hgmeas hS hbdd

theorem vectorSupNormOn_translatedCube_shellGradient_nonneg {d : ℕ} (k : ℤ)
    (z : Vec d) (g : PotentialField d) :
    0 ≤ vectorSupNormOn (translatedCube d k z) (shellGradient g) := by
  unfold vectorSupNormOn
  refine sSup_image_nonneg_of_isBounded (isBounded_translatedCube d k z)
    (continuous_euclideanNorm.comp (continuous_shellGradient g)) (fun x ↦ ?_)
  unfold Homogenization.euclideanNorm
  exact Real.sqrt_nonneg _

/-- **The fourth (tail) term of `accumulatedError`.** -/
theorem measurable_accumulatedErrorTailTerm {d : ℕ} (k : ℕ) (z : Vec d) :
    Measurable (fun omega : PotentialSample d ↦
      ∑' j : ℕ, if k ≤ j then
        (3 : ℝ) ^ k * vectorSupNormOn (translatedCube d (k : ℤ) z)
          (shellGradient (omega j)) else 0) := by
  refine measurable_tsum_of_nonneg (fun j ↦ ?_) (fun j omega ↦ ?_)
  · by_cases h : k ≤ j
    · simp only [if_pos h]
      exact Measurable.const_mul
        (measurable_vectorSupNormOn_translatedCube_shellGradient (k : ℤ) z j) _
    · simp only [if_neg h]
      exact measurable_const
  · by_cases h : k ≤ j
    · simp only [if_pos h]
      exact mul_nonneg (by positivity)
        (vectorSupNormOn_translatedCube_shellGradient_nonneg (k : ℤ) z (omega j))
    · simp only [if_neg h]
      exact le_rfl



theorem measurable_accumulatedError {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (cutoff : Option ℕ)
    (k : ℕ) (z : Vec d) (s : ℝ) :
    Measurable (fun omega : PotentialSample d ↦
      accumulatedError M cutoff k z s omega) := by
  unfold accumulatedError
  refine (((measurable_accumulatedErrorResponseTerm M cutoff k z s).add
    (measurable_accumulatedErrorBlockTerm k z s)).add ?_).add
    (measurable_accumulatedErrorTailTerm k z)
  exact Measurable.const_mul
    (measurable_supNormOn_translatedCube_potentialCoordinate (k : ℤ) z 0) _

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity
