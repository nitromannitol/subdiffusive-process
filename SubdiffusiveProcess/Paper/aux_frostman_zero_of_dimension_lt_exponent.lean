module

public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Geometry.ClosedOddGridCover
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace SubdiffusiveProcess Filter
open scoped ENNReal Topology

noncomputable section
namespace SubdiffusiveProcess.Paper

/--
- The fixed positive-side cube, finite measure, nonnegative growth
  constant, and local ball-growth hypothesis are the source inputs.
- The strict supercritical range `d < t` is the complementary branch to
  the translated-cover child and is not an extra premise of `lem_strips`.
- The vanishing cube mass is concluded by the finite-cover limit; no zero
  mass, support, or global growth assumption is carried.
- Proof-step fine child of `lem_strips`.
-/
theorem aux_frostman_zero_of_dimension_lt_exponent
    (d : ℕ) (_hd : 1 ≤ d) (z : SpatialCoordinates d)
    (R : ℝ) (hR : 0 < R) (t : ℝ) (ht : (d : ℝ) < t)
    (nu : Measure (SpatialCoordinates d)) [IsFiniteMeasure nu]
    (K : ℝ) (_hK : 0 ≤ K) :
    (∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
      ∀ rad : ℝ, 0 < rad → rad ≤ 1 →
        nu (Metric.ball x rad ∩
          (centeredCube z R hR : Set (SpatialCoordinates d))) ≤
          ENNReal.ofReal (K * rad ^ t)) →
    nu (centeredCube z R hR : Set (SpatialCoordinates d)) = 0 := by
  intro hgrow
  classical
  obtain ⟨M, hM⟩ : ∃ M : ℕ, R < (M : ℝ) := exists_nat_gt R
  let q : ℕ → ℝ := fun m => 2 * ((m + M : ℕ) : ℝ) + 1
  let s : ℕ → ℝ := fun m => R / q m
  let Q : Set (SpatialCoordinates d) := centeredCube z R hR
  have hq_pos : ∀ m : ℕ, 0 < q m := by
    intro m
    dsimp [q]
    positivity
  have hs_pos : ∀ m : ℕ, 0 < s m := by
    intro m
    dsimp [s]
    exact div_pos hR (hq_pos m)
  have hs_le_one : ∀ m : ℕ, s m ≤ 1 := by
    intro m
    dsimp [s, q]
    apply (div_le_one (by positivity)).2
    have hMm : (M : ℝ) ≤ ((m + M : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_left M m
    linarith
  have hcover : ∀ m : ℕ, Q ⊆ ⋃ k : OddGridIndex d (m + M),
      Metric.ball (oddGridCenter z R (m + M) k) (s m) := by
    intro m x hx
    have hxcl : x ∈ closure Q := subset_closure hx
    have hcells := oddGridCell_closure_iUnion_eq_closure_centeredCube z hR (m + M)
    have hxunion : x ∈ ⋃ k : OddGridIndex d (m + M),
        closure (oddGridCell z R hR (m + M) k : Set (SpatialCoordinates d)) := by
      rw [hcells]
      exact hxcl
    rcases mem_iUnion.mp hxunion with ⟨k, hxk⟩
    have hxball : x ∈ Metric.closedBall (oddGridCenter z R (m + M) k)
        (R / (2 * ((m + M : ℕ) : ℝ) + 1) / 2) := by
      have hsubset := Metric.closure_ball_subset_closedBall
        (x := oddGridCenter z R (m + M) k)
        (ε := R / (2 * ((m + M : ℕ) : ℝ) + 1) / 2)
      apply hsubset
      simpa [oddGridCell, centeredCube] using hxk
    have hdist : dist x (oddGridCenter z R (m + M) k) ≤ s m / 2 := by
      simpa [s, q] using hxball
    have hlt : dist x (oddGridCenter z R (m + M) k) < s m := by
      have hqeq : q m = 2 * ((m + M : ℕ) : ℝ) + 1 := rfl
      linarith [hs_pos m]
    exact mem_iUnion.mpr ⟨k, by simpa [Metric.mem_ball, dist_comm] using hlt⟩
  have hcenter_mem : ∀ (m : ℕ) (k : OddGridIndex d (m + M)),
      oddGridCenter z R (m + M) k ∈ Q := by
    intro m k
    apply oddGridCell_subset z hR (m + M) k
    change dist (oddGridCenter z R (m + M) k) (oddGridCenter z R (m + M) k) <
      R / (2 * ((m + M : ℕ) : ℝ) + 1) / 2
    have hs' : 0 < R / (2 * ((m + M : ℕ) : ℝ) + 1) := by
      simpa [s, q] using hs_pos m
    simpa using half_pos hs'
  have hmass : ∀ m : ℕ,
      nu Q ≤
        (((2 * (m + M) + 1 : ℕ) ^ d : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (K * (s m) ^ t) := by
    intro m
    have hsubset : Q ⊆ ⋃ k : OddGridIndex d (m + M),
        (Metric.ball (oddGridCenter z R (m + M) k) (s m) ∩ Q) := by
      intro x hx
      rcases mem_iUnion.mp (hcover m hx) with ⟨k, hxk⟩
      exact mem_iUnion.mpr ⟨k, ⟨hxk, hx⟩⟩
    calc
      nu Q ≤ nu (⋃ k : OddGridIndex d (m + M),
          (Metric.ball (oddGridCenter z R (m + M) k) (s m) ∩ Q)) :=
        measure_mono hsubset
      _ ≤ ∑ k : OddGridIndex d (m + M),
          nu (Metric.ball (oddGridCenter z R (m + M) k) (s m) ∩ Q) :=
        measure_iUnion_fintype_le _ _
      _ ≤ ∑ _k : OddGridIndex d (m + M), ENNReal.ofReal (K * (s m) ^ t) := by
        apply Finset.sum_le_sum
        intro k hk
        exact hgrow _ (hcenter_mem m k) _ (hs_pos m) (hs_le_one m)
      _ = (((2 * (m + M) + 1 : ℕ) ^ d : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (K * (s m) ^ t) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  have hreal_bound : ∀ m : ℕ,
      nu Q ≤ ENNReal.ofReal
        (K * R ^ t * (q m) ^ (-(t - (d : ℝ)))) := by
    intro m
    have hq : 0 < q m := hq_pos m
    have hq0 : 0 ≤ q m := hq.le
    have hRpow : 0 ≤ R ^ t := Real.rpow_nonneg hR.le t
    have hmain :
        (((2 * (m + M) + 1 : ℕ) ^ d : ℕ) : ℝ≥0∞) *
            ENNReal.ofReal (K * (s m) ^ t) =
          ENNReal.ofReal (K * R ^ t * (q m) ^ (-(t - (d : ℝ)))) := by
      rw [← ENNReal.ofReal_natCast]
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤
        (((2 * (m + M) + 1 : ℕ) ^ d : ℕ) : ℝ))]
      congr 1
      dsimp [s, q]
      push_cast
      rw [← Real.rpow_natCast]
      rw [Real.div_rpow hR.le (by positivity)]
      calc
        (2 * (↑m + ↑M) + 1) ^ (d : ℝ) *
              (K * (R ^ t / (2 * (↑m + ↑M) + 1) ^ t)) =
            K * R ^ t *
              ((2 * (↑m + ↑M) + 1) ^ (d : ℝ) /
                (2 * (↑m + ↑M) + 1) ^ t) := by ring
        _ = K * R ^ t * (2 * (↑m + ↑M) + 1) ^ ((d : ℝ) - t) := by
          rw [Real.rpow_sub (by positivity)]
        _ = K * R ^ t * (2 * (↑m + ↑M) + 1) ^ (-(t - (d : ℝ))) := by
          congr 3
          ring
    exact hmain ▸ hmass m
  have hq_tendsto : Tendsto (q : ℕ → ℝ) atTop atTop := by
    have hbase : Tendsto (fun m : ℕ => ((m + M : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat M)
    have hmul : Tendsto (fun m : ℕ => 2 * ((m + M : ℕ) : ℝ)) atTop atTop :=
      hbase.const_mul_atTop (by norm_num)
    simpa [q] using (tendsto_atTop_add_const_right atTop 1 hmul)
  have hdecay : Tendsto (fun m : ℕ =>
      ENNReal.ofReal (K * R ^ t * (q m) ^ (-(t - (d : ℝ))))) atTop (𝓝 0) := by
    have hpow := (tendsto_rpow_neg_atTop (sub_pos.mpr ht)).comp hq_tendsto
    have hconst : Tendsto (fun _ : ℕ => K * R ^ t) atTop (𝓝 (K * R ^ t)) :=
      tendsto_const_nhds
    have hreal : Tendsto (fun m : ℕ =>
        K * R ^ t * (q m) ^ (-(t - (d : ℝ)))) atTop (𝓝 0) := by
      simpa [Function.comp_def] using hconst.mul hpow
    simpa using (ENNReal.tendsto_ofReal hreal)
  have hle : nu Q ≤ 0 := by
    apply ge_of_tendsto' hdecay
    exact hreal_bound
  exact le_antisymm hle bot_le

end SubdiffusiveProcess.Paper
