module

public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.lem_mass_grid_partition

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SubdiffusiveProcess MeasureTheory Filter
open scoped Topology

namespace Paper
noncomputable section

lemma aux_lem_mass_interior_collar_measurable_bad
    {X I : Type*} [TopologicalSpace X] [MeasurableSpace X] [Countable I]
    (Q : Set X) (cell parent : I → Set X) (pointIdx : X → I)
    (hQ : MeasurableSet Q) (hcell : ∀ k, MeasurableSet (cell k))
    (hpoint : ∀ x k, x ∈ cell k ↔ k = pointIdx x) :
    MeasurableSet {x | x ∈ Q ∧ ¬ closure (parent (pointIdx x)) ⊆ Q} := by
  classical
  let bad : I → Prop := fun k => ¬ closure (parent k) ⊆ Q
  have heq : {x | x ∈ Q ∧ ¬ closure (parent (pointIdx x)) ⊆ Q} =
      Q ∩ ⋃ k, if bad k then cell k else ∅ := by
    ext x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      let k := pointIdx x
      have hxk : x ∈ cell k := (hpoint x k).2 rfl
      have hbad : bad k := by simpa [bad, k] using hx.2
      exact Set.mem_iUnion.2 ⟨k, by simp [hbad, hxk]⟩
    · rintro ⟨hxQ, hxU⟩
      rcases Set.mem_iUnion.1 hxU with ⟨k, hxk⟩
      by_cases hk : bad k
      · have hxcell : x ∈ cell k := by simpa [hk] using hxk
        have hkp : k = pointIdx x := (hpoint x k).1 hxcell
        refine ⟨hxQ, ?_⟩
        simpa [bad, hkp] using hk
      · simp [hk] at hxk
  rw [heq]
  exact hQ.inter (MeasurableSet.iUnion fun k => by
    by_cases hk : bad k
    · simpa [hk] using hcell k
    · simp [hk])



theorem lem_mass_interior_collar
    (d H1 Mm : ℕ) (hd : 2 ≤ d) (hH1 : 1 ≤ H1) (hMm : 2 ≤ Mm) :
    let L : ℝ := (3 : ℝ) ^ H1
    let Shift : Type := Fin d → Fin Mm
    let shift : Shift → Fin d → ℝ :=
      fun sigma i => ((sigma i).val : ℝ) / (Mm : ℝ)
    let side : ℕ → ℝ := fun n => L ^ (-(n : ℝ))
    let lo : Shift → ℕ → (Fin d → Int) → Fin d → ℝ :=
      fun sigma n k i => shift sigma i + side n * (k i : ℝ)
    let cell : Shift → ℕ → (Fin d → Int) → Set (SpatialCoordinates d) :=
      fun sigma n k => Set.pi Set.univ (fun i =>
        Set.Ico (lo sigma n k i) (lo sigma n k i + side n))
    let parentIdx : (Fin d → Int) → Fin d → Int :=
      fun k i => Int.floor ((k i : ℝ) / L)
    let parent : Shift → ℕ → (Fin d → Int) → Set (SpatialCoordinates d) :=
      fun sigma n k => cell sigma (n - 1) (parentIdx k)
    let pointIdx : Shift → ℕ → SpatialCoordinates d → Fin d → Int :=
      fun sigma n x i => Int.floor ((x i - shift sigma i) / side n)
    (zQ : SpatialCoordinates d) → (rQ : ℝ) → (hrQ : 0 < rQ) →
    (mu : Measure (SpatialCoordinates d)) → [IsFiniteMeasure mu] →
    let Q := centeredCube zQ rQ hrQ
    (hsupp : mu ((Q : Set (SpatialCoordinates d))ᶜ) = 0) →
    (hQpositive : 0 < mu (Q : Set (SpatialCoordinates d))) →
    (epscoll : ℝ) → (hepscoll : 0 < epscoll) →
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n → ∀ sigma : Shift,
        MeasurableSet {x : SpatialCoordinates d |
          x ∈ (Q : Set (SpatialCoordinates d)) ∧
          ¬ closure (parent sigma n (pointIdx sigma n x)) ⊆
            (Q : Set (SpatialCoordinates d))} ∧
        (mu {x : SpatialCoordinates d |
          x ∈ (Q : Set (SpatialCoordinates d)) ∧
          ¬ closure (parent sigma n (pointIdx sigma n x)) ⊆
            (Q : Set (SpatialCoordinates d))}).toReal ≤
          epscoll * (mu (Q : Set (SpatialCoordinates d))).toReal := by
  dsimp
  intro zQ rQ hrQ mu hfin hSupp hPos epscoll hEps
  have hQmeas : MeasurableSet (Metric.ball zQ (rQ / 2)) := measurableSet_ball
  have hQfin : mu (Metric.ball zQ (rQ / 2)) ≠ ⊤ := measure_ne_top _ _
  have hδ : 0 < epscoll * (mu (Metric.ball zQ (rQ / 2))).toReal := by
    have hm : 0 < (mu (Metric.ball zQ (rQ / 2))).toReal :=
      ENNReal.toReal_pos (ne_of_gt hPos) hQfin
    exact mul_pos hEps hm
  have hδ' : ENNReal.ofReal (epscoll * (mu (Metric.ball zQ (rQ / 2))).toReal) ≠ 0 := by
    positivity
  have hK := MeasurableSet.exists_isCompact_isClosed_diff_lt hQmeas hQfin hδ'
  obtain ⟨K, hKsub, hKcomp, hKclosed, hKdiff⟩ := hK
  have hdisj : Disjoint K (Metric.ball zQ (rQ / 2))ᶜ := by
    exact Set.disjoint_left.2 (fun x hxK hxout => hxout (hKsub hxK))
  obtain ⟨rho, hrho, hdist⟩ := Metric.exists_pos_forall_lt_edist hKcomp
    (isClosed_compl_iff.mpr Metric.isOpen_ball) hdisj
  have hLpos : 0 < (3 : ℝ) ^ H1 := by positivity
  have hLone : 1 < (3 : ℝ) ^ H1 := by
    calc
      (1 : ℝ) < (3 : ℝ) ^ 1 := by norm_num
      _ ≤ (3 : ℝ) ^ H1 := by
        gcongr
        norm_num
  have hside : Tendsto (fun m : ℕ => ((3 : ℝ) ^ H1) ^ (-(m : ℝ))) atTop (𝓝 0) := by
    have hpow : Tendsto (fun m : ℕ => ((3 : ℝ) ^ H1)⁻¹ ^ m) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hLpos.le)
        (by exact inv_lt_one_of_one_lt₀ hLone)
    convert hpow using 1
    funext m
    rw [Real.rpow_neg hLpos.le, Real.rpow_natCast]
    simp [inv_pow]
  rcases (Metric.tendsto_atTop.1 hside (rho : ℝ) (by exact_mod_cast hrho)) with ⟨M, hM⟩
  have hgrid := lem_mass_grid_partition d H1 Mm hd hH1 hMm
  dsimp at hgrid
  have hM' : ∀ m : ℕ, M ≤ m → ((3 : ℝ) ^ H1) ^ (-(m : ℝ)) < (rho : ℝ) := by
    intro m hm
    have h := hM m hm
    have hnonneg : 0 ≤ ((3 : ℝ) ^ H1) ^ (-(m : ℝ)) :=
      Real.rpow_nonneg hLpos.le _
    simpa [Real.dist_eq, abs_of_nonneg hnonneg] using h
  refine ⟨M + 1, by omega, ?_⟩
  intro n hn sigma
  have hn1 : 1 ≤ n := by omega
  have hsmall : ((3 : ℝ) ^ H1) ^ (-(n - 1 : ℕ) : ℝ) < (rho : ℝ) := by
    apply hM'
    omega
  let cellN : (Fin d → Int) → Set (SpatialCoordinates d) := fun k =>
    Set.pi Set.univ (fun i =>
      Set.Ico (((sigma i).val : ℝ) / (Mm : ℝ) +
        ((3 : ℝ) ^ H1) ^ (-(n : ℝ)) * (k i : ℝ))
        (((sigma i).val : ℝ) / (Mm : ℝ) +
          ((3 : ℝ) ^ H1) ^ (-(n : ℝ)) * (k i : ℝ) +
          ((3 : ℝ) ^ H1) ^ (-(n : ℝ))))
  let parentN : (Fin d → Int) → Set (SpatialCoordinates d) := fun k =>
    Set.pi Set.univ (fun i =>
      Set.Ico (((sigma i).val : ℝ) / (Mm : ℝ) +
        ((3 : ℝ) ^ H1) ^ (-(n - 1 : ℕ) : ℝ) *
          (Int.floor ((k i : ℝ) / ((3 : ℝ) ^ H1)) : ℝ))
        (((sigma i).val : ℝ) / (Mm : ℝ) +
          ((3 : ℝ) ^ H1) ^ (-(n - 1 : ℕ) : ℝ) *
            (Int.floor ((k i : ℝ) / ((3 : ℝ) ^ H1)) : ℝ) +
          ((3 : ℝ) ^ H1) ^ (-(n - 1 : ℕ) : ℝ)))
  let pointN : SpatialCoordinates d → (Fin d → Int) := fun x i =>
    Int.floor ((x i - ((sigma i).val : ℝ) / (Mm : ℝ)) /
      (((3 : ℝ) ^ H1) ^ (-(n : ℝ))))
  have hcell : ∀ k, MeasurableSet (cellN k) := by
    intro k
    simpa [cellN] using hgrid.1 sigma n k
  have hpoint : ∀ x k, x ∈ cellN k ↔ k = pointN x := by
    intro x k
    simpa [cellN, pointN] using hgrid.2.1 sigma n x k
  have hQmeas' : MeasurableSet (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)) := by
    change MeasurableSet (Metric.ball zQ (rQ / 2))
    exact measurableSet_ball
  have hbad_meas : MeasurableSet {x : SpatialCoordinates d |
      x ∈ (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)) ∧
        ¬ closure (parentN (pointN x)) ⊆
          (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))} := by
    apply aux_lem_mass_interior_collar_measurable_bad
      (Q := (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)))
      (cell := cellN) (parent := parentN) (pointIdx := pointN) hQmeas' hcell hpoint
  have hparent_K : ∀ x ∈ K, closure (parentN (pointN x)) ⊆
      (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)) := by
    intro x hxK y hy
    by_contra hyQ
    have hyout : y ∈ (Metric.ball zQ (rQ / 2))ᶜ := by
      change y ∉ Metric.ball zQ (rQ / 2)
      exact hyQ
    have hd := hdist x hxK y hyout
    have hd' : (rho : ℝ) < dist x y := by
      have hd0 : ENNReal.ofReal (rho : ℝ) < ENNReal.ofReal (dist x y) := by
        simpa [edist_dist, ENNReal.ofReal_coe_nnreal] using hd
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by exact_mod_cast hrho.le)).1 hd0
    have hxcell : x ∈ cellN (pointN x) := (hpoint x (pointN x)).2 rfl
    have hxparent : x ∈ parentN (pointN x) := by
      simpa [cellN, parentN] using
        (hgrid.2.2.1 sigma n hn1 (pointN x)).1 hxcell
    have hsp : 0 < ((3 : ℝ) ^ H1) ^ (-(n - 1 : ℕ) : ℝ) :=
      Real.rpow_pos_of_pos hLpos _
    have hxparent' := hxparent
    simp only [parentN, Set.mem_pi] at hxparent'
    have hy' := hy
    simp only [parentN, closure_pi_set, Set.mem_pi] at hy'
    have hdistxy : dist x y ≤ ((3 : ℝ) ^ H1) ^ (-(n - 1 : ℕ) : ℝ) := by
      apply (dist_pi_le_iff hsp.le).2
      intro i
      rw [Real.dist_eq]
      apply abs_le.2
      have hxcoord := hxparent' i (Set.mem_univ i)
      simp only [Set.mem_Ico] at hxcoord
      have hycoord := hy' i (Set.mem_univ i)
      rw [closure_Ico (by linarith)] at hycoord
      constructor <;> linarith [hxcoord.1, hxcoord.2, hycoord.1, hycoord.2]
    exact (not_lt_of_ge (le_of_lt hsmall)) (lt_of_lt_of_le hd' hdistxy)
  constructor
  · simpa [cellN, parentN, pointN, centeredCube] using hbad_meas
  · have hsubset : {x : SpatialCoordinates d |
        x ∈ (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)) ∧
          ¬ closure (parentN (pointN x)) ⊆
            (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))} ⊆
      (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)) \ K := by
      intro x hx
      refine ⟨hx.1, ?_⟩
      intro hxK
      exact hx.2 (hparent_K x hxK)
    have hKdiff' : (mu (Metric.ball zQ (rQ / 2) \ K)).toReal <
        epscoll * (mu (Metric.ball zQ (rQ / 2))).toReal := by
      exact ENNReal.toReal_lt_of_lt_ofReal hKdiff
    have hmono : (mu {x : SpatialCoordinates d |
        x ∈ (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)) ∧
          ¬ closure (parentN (pointN x)) ⊆
            (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))}).toReal ≤
        (mu ((centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)) \ K)).toReal := by
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      exact measure_mono hsubset
    have hlocal : (mu {x : SpatialCoordinates d |
          x ∈ (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)) ∧
            ¬ closure (parentN (pointN x)) ⊆
              (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))}).toReal <
        epscoll * (mu (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))).toReal := by
      calc
      (mu {x : SpatialCoordinates d |
          x ∈ (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)) ∧
            ¬ closure (parentN (pointN x)) ⊆
              (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))}).toReal ≤
          (mu ((centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)) \ K)).toReal := hmono
      _ < epscoll * (mu (Metric.ball zQ (rQ / 2))).toReal := by
        simpa [centeredCube] using hKdiff'
      _ ≤ epscoll * (mu (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))).toReal := by
        rfl
    simpa [cellN, parentN, pointN, centeredCube] using hlocal.le

end
end Paper
