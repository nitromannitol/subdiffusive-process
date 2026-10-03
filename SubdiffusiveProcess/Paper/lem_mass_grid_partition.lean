module

public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.parameter_chain

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SubdiffusiveProcess MeasureTheory

namespace Paper
noncomputable section

lemma aux_lem_mass_grid_partition_interval_floor {a s x : ℝ} {k : ℤ} (hs : 0 < s) :
    x ∈ Set.Ico (a + s * (k : ℝ)) (a + s * (k : ℝ) + s) ↔
      k = Int.floor ((x - a) / s) := by
  constructor
  · intro hx
    apply Eq.symm
    apply (Int.floor_eq_iff).2
    constructor
    · apply (le_div_iff₀ hs).2
      linarith [hx.1]
    · apply (div_lt_iff₀ hs).2
      linarith [hx.2]
  · intro hk
    have hf : Int.floor ((x - a) / s) = k := hk.symm
    have hf' := (Int.floor_eq_iff).mp hf
    constructor
    · have h := (le_div_iff₀ hs).1 hf'.1
      linarith
    · have h := (div_lt_iff₀ hs).1 hf'.2
      linarith

lemma aux_lem_mass_grid_partition_side_parent (L : ℝ) (hL : 0 < L)
    (n : ℕ) (hn : 1 ≤ n) :
    L ^ (-(n - 1 : ℕ) : ℝ) = L * L ^ (-(n : ℝ)) := by
  have hsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]
    norm_num
  rw [show (-(n - 1 : ℕ) : ℝ) = 1 + -(n : ℝ) by rw [hsub]; ring]
  rw [Real.rpow_add hL, Real.rpow_one]

lemma aux_lem_mass_grid_partition_floor_div_nat (m : ℕ) (k : ℤ) :
    Int.floor ((k : ℝ) / (m : ℝ)) = k / (m : ℤ) := by
  simpa using Int.floor_div_natCast (k : ℝ) m

lemma aux_lem_mass_grid_partition_fiber_card {d : ℕ} (m : ℕ) (hm : 0 < m)
    (p : Fin d → ℤ) :
    Nat.card {k : Fin d → ℤ //
      (fun i => Int.floor ((k i : ℝ) / (m : ℝ))) = p} = m ^ d := by
  let ecoord (q : ℤ) : {k : ℤ // k / (m : ℤ) = q} ≃ Fin m :=
    { toFun := fun k =>
        ⟨(k.1 % (m : ℤ)).toNat,
          (Int.toNat_lt_of_ne_zero (Nat.ne_of_gt hm)).2
            (Int.emod_lt_of_pos _ (by exact_mod_cast hm))⟩
      invFun := fun r =>
        ⟨(r : ℤ) + (m : ℤ) * q, by
          rw [Int.add_mul_ediv_left _ _ (by exact_mod_cast (Nat.ne_of_gt hm))]
          rw [Int.ediv_eq_zero_of_lt (by positivity)]
          · simp
          · exact_mod_cast r.isLt⟩
      left_inv := by
        intro k
        apply Subtype.ext
        have hrem : 0 ≤ k.1 % (m : ℤ) :=
          Int.emod_nonneg _ (by exact_mod_cast (Nat.ne_of_gt hm))
        simpa [Int.natCast_toNat_eq_self.mpr hrem, k.2] using
          (Int.emod_add_mul_ediv k.1 (m : ℤ))
      right_inv := by
        intro r
        apply Fin.ext
        have hdiv : ((r : ℤ) + (m : ℤ) * q) / (m : ℤ) = q := by
          rw [Int.add_mul_ediv_left _ _ (by exact_mod_cast (Nat.ne_of_gt hm))]
          rw [Int.ediv_eq_zero_of_lt (by positivity)]
          · simp
          · exact_mod_cast r.isLt
        have hrem : ((r : ℤ) + (m : ℤ) * q) % (m : ℤ) = (r : ℤ) := by
          have h := Int.emod_add_mul_ediv ((r : ℤ) + (m : ℤ) * q) (m : ℤ)
          rw [hdiv] at h
          omega
        simp [hrem] }
  let e : {k : Fin d → ℤ //
      (fun i => Int.floor ((k i : ℝ) / (m : ℝ))) = p} ≃ (Fin d → Fin m) :=
    { toFun := fun k i =>
        ecoord (p i) ⟨k.1 i, by
          simpa [aux_lem_mass_grid_partition_floor_div_nat] using congrFun k.2 i⟩
      invFun := fun r =>
        ⟨fun i => (ecoord (p i)).symm (r i), by
          funext i
          simpa [aux_lem_mass_grid_partition_floor_div_nat] using
            ((ecoord (p i)).symm (r i)).property⟩
      left_inv := by
        intro k
        apply Subtype.ext
        funext i
        exact congrArg Subtype.val ((ecoord (p i)).left_inv ⟨k.1 i, by
          simpa [aux_lem_mass_grid_partition_floor_div_nat] using congrFun k.2 i⟩
          )
      right_inv := by
        intro r
        funext i
        exact (ecoord (p i)).right_inv (r i) }
  rw [Nat.card_congr e, Nat.card_fun]
  simp

lemma aux_lem_mass_grid_partition_fiber_finite {d : ℕ} (m : ℕ) (hm : 0 < m)
    (p : Fin d → ℤ) :
    {k : Fin d → ℤ | (fun i => Int.floor ((k i : ℝ) / (m : ℝ))) = p}.Finite := by
  classical
  have hsub : {k : Fin d → ℤ |
      (fun i => Int.floor ((k i : ℝ) / (m : ℝ))) = p} ⊆
      Set.univ.pi (fun i => Set.Icc ((m : ℤ) * p i)
        ((m : ℤ) * p i + (m : ℤ) - 1)) := by
    intro k hk
    simp only [Set.mem_pi, Set.mem_univ, true_implies]
    intro i
    have hi := congrFun hk i
    have hdiv : k i / (m : ℤ) = p i := by
      simpa [aux_lem_mass_grid_partition_floor_div_nat] using hi
    have hremnonneg : 0 ≤ k i % (m : ℤ) :=
      Int.emod_nonneg _ (by exact_mod_cast (Nat.ne_of_gt hm))
    have hremlt : k i % (m : ℤ) < (m : ℤ) :=
      Int.emod_lt_of_pos _ (by exact_mod_cast hm)
    have hdecomp := Int.emod_add_mul_ediv (k i) (m : ℤ)
    rw [hdiv] at hdecomp
    constructor <;> omega
  exact (Set.Finite.pi (fun _ => Set.finite_Icc _ _)).subset hsub



theorem lem_mass_grid_partition
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
    (∀ (sigma : Shift) (n : ℕ) (k : Fin d → Int),
      MeasurableSet (cell sigma n k)) ∧
    (∀ (sigma : Shift) (n : ℕ) (x : SpatialCoordinates d) (k : Fin d → Int),
      x ∈ cell sigma n k ↔ k = pointIdx sigma n x) ∧
    (∀ (sigma : Shift) (n : ℕ), 1 ≤ n → ∀ k : Fin d → Int,
      cell sigma n k ⊆ parent sigma n k ∧
      ∀ x : SpatialCoordinates d, x ∈ cell sigma n k →
        pointIdx sigma (n - 1) x = parentIdx k) ∧
    (∀ p : Fin d → Int,
      {k : Fin d → Int | parentIdx k = p}.Finite ∧
      Nat.card {k : Fin d → Int // parentIdx k = p} = (3 ^ H1) ^ d) ∧
    (∀ (sigma : Shift) (n : ℕ) (zQ : SpatialCoordinates d)
      (rQ : ℝ) (hrQ : 0 < rQ),
      {k : Fin d → Int |
        (cell sigma n k ∩ (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))).Nonempty}.Finite) := by
  dsimp
  have hL : 0 < (3 : ℝ) ^ H1 := by positivity
  have hm : 0 < 3 ^ H1 := by positivity
  have hbase : (3 : ℝ) ^ H1 = (3 ^ H1 : ℕ) := by
    norm_num [Nat.cast_pow]
  have hside : ∀ n : ℕ, 0 < ((3 : ℝ) ^ H1) ^ (-(n : ℝ)) := by
    intro n
    positivity
  constructor
  · intro sigma n k
    exact MeasurableSet.univ_pi (fun i => measurableSet_Ico)
  constructor
  · intro sigma n x k
    simp only [Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro hx
      funext i
      exact (aux_lem_mass_grid_partition_interval_floor (a :=
        ((sigma i).val : ℝ) / (Mm : ℝ))
        (s := ((3 : ℝ) ^ H1) ^ (-(n : ℝ))) (x := x i) (k := k i)
        (hside n)).mp (hx i)
    · intro hk i
      exact (aux_lem_mass_grid_partition_interval_floor (a :=
        ((sigma i).val : ℝ) / (Mm : ℝ))
        (s := ((3 : ℝ) ^ H1) ^ (-(n : ℝ))) (x := x i) (k := k i)
        (hside n)).mpr (congrFun hk i)
  constructor
  · intro sigma n hn k
    constructor
    · intro x hx
      simp only [Set.mem_pi, Set.mem_univ, true_implies] at hx ⊢
      intro i
      have hchild := (aux_lem_mass_grid_partition_interval_floor (a :=
        ((sigma i).val : ℝ) / (Mm : ℝ))
        (s := ((3 : ℝ) ^ H1) ^ (-(n : ℝ))) (x := x i) (k := k i)
        (hside n)).mp (hx i)
      have hsparent := aux_lem_mass_grid_partition_side_parent
        ((3 : ℝ) ^ H1) hL n hn
      have hquot :
          (x i - ((sigma i).val : ℝ) / (Mm : ℝ)) /
              (((3 : ℝ) ^ H1) ^ (-(n - 1 : ℕ) : ℝ)) =
            ((x i - ((sigma i).val : ℝ) / (Mm : ℝ)) /
              (((3 : ℝ) ^ H1) ^ (-(n : ℝ))) ) / ((3 : ℝ) ^ H1) := by
        rw [hsparent]
        field_simp [ne_of_gt hL, ne_of_gt (hside n)]
      have hfloor :
          Int.floor ((x i - ((sigma i).val : ℝ) / (Mm : ℝ)) /
              (((3 : ℝ) ^ H1) ^ (-(n - 1 : ℕ) : ℝ))) =
            Int.floor ((k i : ℝ) / ((3 : ℝ) ^ H1)) := by
        calc
          _ = Int.floor (((x i - ((sigma i).val : ℝ) / (Mm : ℝ)) /
              (((3 : ℝ) ^ H1) ^ (-(n : ℝ))) ) / ((3 : ℝ) ^ H1)) := by rw [hquot]
          _ = Int.floor ((x i - ((sigma i).val : ℝ) / (Mm : ℝ)) /
              (((3 : ℝ) ^ H1) ^ (-(n : ℝ)))) / (3 ^ H1 : ℤ) := by
                rw [hbase]
                simpa using Int.floor_div_natCast
                  ((x i - ((sigma i).val : ℝ) / (Mm : ℝ)) /
                    (((3 : ℝ) ^ H1) ^ (-(n : ℝ)))) (3 ^ H1)
          _ = k i / (3 ^ H1 : ℤ) := by rw [hchild]
          _ = Int.floor ((k i : ℝ) / ((3 : ℝ) ^ H1)) := by
                rw [hbase]
                symm
                simpa using Int.floor_div_natCast (k i : ℝ) (3 ^ H1)
      exact (aux_lem_mass_grid_partition_interval_floor (a :=
        ((sigma i).val : ℝ) / (Mm : ℝ))
        (s := ((3 : ℝ) ^ H1) ^ (-(n - 1 : ℕ) : ℝ)) (x := x i)
        (k := Int.floor ((k i : ℝ) / ((3 : ℝ) ^ H1)))
        (by rw [hsparent]; positivity)).mpr hfloor.symm
    · intro x hx
      simp only [Set.mem_pi, Set.mem_univ, true_implies] at hx
      funext i
      have hchild := (aux_lem_mass_grid_partition_interval_floor (a :=
        ((sigma i).val : ℝ) / (Mm : ℝ))
        (s := ((3 : ℝ) ^ H1) ^ (-(n : ℝ))) (x := x i) (k := k i)
        (hside n)).mp (hx i)
      have hsparent := aux_lem_mass_grid_partition_side_parent
        ((3 : ℝ) ^ H1) hL n hn
      have hquot :
          (x i - ((sigma i).val : ℝ) / (Mm : ℝ)) /
              (((3 : ℝ) ^ H1) ^ (-(n - 1 : ℕ) : ℝ)) =
            ((x i - ((sigma i).val : ℝ) / (Mm : ℝ)) /
              (((3 : ℝ) ^ H1) ^ (-(n : ℝ))) ) / ((3 : ℝ) ^ H1) := by
        rw [hsparent]
        field_simp [ne_of_gt hL, ne_of_gt (hside n)]
      have hfloor :
          Int.floor ((x i - ((sigma i).val : ℝ) / (Mm : ℝ)) /
              (((3 : ℝ) ^ H1) ^ (-(n - 1 : ℕ) : ℝ))) =
            Int.floor ((k i : ℝ) / ((3 : ℝ) ^ H1)) := by
        calc
          _ = Int.floor (((x i - ((sigma i).val : ℝ) / (Mm : ℝ)) /
              (((3 : ℝ) ^ H1) ^ (-(n : ℝ))) ) / ((3 : ℝ) ^ H1)) := by rw [hquot]
          _ = Int.floor ((x i - ((sigma i).val : ℝ) / (Mm : ℝ)) /
              (((3 : ℝ) ^ H1) ^ (-(n : ℝ)))) / (3 ^ H1 : ℤ) := by
                rw [hbase]
                simpa using Int.floor_div_natCast
                  ((x i - ((sigma i).val : ℝ) / (Mm : ℝ)) /
                    (((3 : ℝ) ^ H1) ^ (-(n : ℝ)))) (3 ^ H1)
          _ = k i / (3 ^ H1 : ℤ) := by rw [hchild]
          _ = Int.floor ((k i : ℝ) / ((3 : ℝ) ^ H1)) := by
                rw [hbase]
                symm
                simpa using Int.floor_div_natCast (k i : ℝ) (3 ^ H1)
      exact hfloor
  constructor
  · intro p
    constructor
    · simpa only [hbase] using
        aux_lem_mass_grid_partition_fiber_finite (3 ^ H1) hm p
    · simpa only [hbase] using
        aux_lem_mass_grid_partition_fiber_card (3 ^ H1) hm p
  · intro sigma n zQ rQ hrQ
    have hfinite :
        (Set.univ.pi (fun i : Fin d => Set.Icc
          (Int.floor ((zQ i - rQ / 2 - ((sigma i).val : ℝ) / (Mm : ℝ)) /
            (((3 : ℝ) ^ H1) ^ (-(n : ℝ)))))
          (Int.floor ((zQ i + rQ / 2 - ((sigma i).val : ℝ) / (Mm : ℝ)) /
            (((3 : ℝ) ^ H1) ^ (-(n : ℝ))))))).Finite := by
      exact Set.Finite.pi (fun i => Set.finite_Icc _ _)
    apply hfinite.subset
    intro k hk
    rcases hk with ⟨x, hxcell, hxQ⟩
    simp only [Set.mem_pi, Set.mem_univ, true_implies]
    simp only [Set.mem_pi, Set.mem_univ, true_implies] at hxcell
    change x ∈ Metric.ball zQ (rQ / 2) at hxQ
    have hdist : dist x zQ < rQ / 2 := Metric.mem_ball.mp hxQ
    intro i
    have hcoord_abs : |x i - zQ i| < rQ / 2 := by
      have hi : dist (x i) (zQ i) ≤ dist x zQ := dist_le_pi_dist x zQ i
      have hi' := lt_of_le_of_lt hi hdist
      simpa [Real.dist_eq] using hi'
    have hcoord := abs_lt.mp hcoord_abs
    have hxi := hxcell i
    constructor
    · have hlow :
          (zQ i - rQ / 2 - ((sigma i).val : ℝ) / (Mm : ℝ)) /
              (((3 : ℝ) ^ H1) ^ (-(n : ℝ))) < (k i : ℝ) + 1 := by
        apply (div_lt_iff₀ (hside n)).2
        linarith [hxi.2, hcoord.1]
      have hfloor :
          Int.floor ((zQ i - rQ / 2 - ((sigma i).val : ℝ) / (Mm : ℝ)) /
            (((3 : ℝ) ^ H1) ^ (-(n : ℝ)))) < k i + 1 := by
        apply (Int.floor_lt).2
        simpa using hlow
      omega
    · have hupp :
          (k i : ℝ) ≤
            (zQ i + rQ / 2 - ((sigma i).val : ℝ) / (Mm : ℝ)) /
              (((3 : ℝ) ^ H1) ^ (-(n : ℝ))) := by
        apply (le_div_iff₀ (hside n)).2
        linarith [hxi.1, hcoord.2]
      exact (Int.le_floor).2 hupp

end
end Paper
