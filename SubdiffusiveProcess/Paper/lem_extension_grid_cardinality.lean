module

public import SubdiffusiveProcess.Lane4.Carriers

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem lem_extension_grid_cardinality :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (J : ℕ) (origins : Fin J → SpatialCoordinates d),
  ∃ Cgrid : ℕ,
    ∀ (k : ℕ) (index : Fin J),
      ∃ S : Finset (Fin d → ℤ),
        (∀ nidx : Fin d → ℤ,
          nidx ∈ S ↔
            centeredCube
                (fun i => origins index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
                ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤
              centeredCube z0 R hR) ∧
        S.card ≤ Cgrid * 3 ^ (d * k) := by
  intro d hd z0 R hR J origins
  refine ⟨⌈R⌉₊ ^ d, ?_⟩
  intro k index
  let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hrinv : r⁻¹ = (3 : ℝ) ^ k := by
    change ((3 : ℝ) ^ (-(k : ℤ)))⁻¹ = (3 : ℝ) ^ k
    rw [zpow_neg, inv_inv, zpow_natCast]
  let lo : Fin d → ℤ := fun i => ⌈(z0 i - R / 2 + r / 2 - origins index i) / r⌉
  let hi : Fin d → ℤ := fun i => ⌊(z0 i + R / 2 - r / 2 - origins index i) / r⌋
  classical
  let box : Finset (Fin d → ℤ) := Fintype.piFinset (fun i => Finset.Icc (lo i) (hi i))
  have hbox : ∀ nidx : Fin d → ℤ,
      centeredCube (fun i => origins index i + r * nidx i) r hr ≤ centeredCube z0 R hR →
        nidx ∈ box := by
    intro nidx hnidx
    rw [Fintype.mem_piFinset]
    intro i
    have hpi :
        (centeredCube (fun i => origins index i + r * nidx i) r hr :
          Set (SpatialCoordinates d)) ⊆
          (centeredCube z0 R hR : Set (SpatialCoordinates d)) := hnidx
    rw [centeredCube_eq_pi (fun i => origins index i + r * nidx i) hr,
        centeredCube_eq_pi z0 hR] at hpi
    have hsub_all := (Set.univ_pi_subset_univ_pi_iff.mp hpi)
    have hsub_i :
        Set.Ioo (origins index i + r * nidx i - r / 2)
            (origins index i + r * nidx i + r / 2) ⊆
          Set.Ioo (z0 i - R / 2) (z0 i + R / 2) := by
      rcases hsub_all with hsub_all | hempty
      · exact hsub_all i
      · obtain ⟨j, hj⟩ := hempty
        have hjne :
            (Set.Ioo (origins index j + r * nidx j - r / 2)
              (origins index j + r * nidx j + r / 2)).Nonempty :=
          Set.nonempty_Ioo.mpr (by linarith [hr])
        exact (hjne.ne_empty hj).elim
    have hx :=
      (Ioo_subset_Ioo_iff (by linarith [hr] :
        (origins index i + r * nidx i - r / 2) <
          (origins index i + r * nidx i + r / 2))).mp hsub_i
    have hL : (z0 i - R / 2 + r / 2 - origins index i) / r ≤ (nidx i : ℝ) := by
      rw [div_le_iff₀ hr]
      have := hx.1
      nlinarith [this]
    have hU : (nidx i : ℝ) ≤ (z0 i + R / 2 - r / 2 - origins index i) / r := by
      rw [le_div_iff₀ hr]
      have := hx.2
      nlinarith [this]
    exact Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr hL, Int.le_floor.mpr hU⟩
  let S : Finset (Fin d → ℤ) := box.filter (fun nidx =>
    centeredCube (fun i => origins index i + r * nidx i) r hr ≤ centeredCube z0 R hR)
  refine ⟨S, ?_, ?_⟩
  · intro nidx
    change nidx ∈ S ↔
      centeredCube (fun i => origins index i + r * nidx i) r hr ≤
        centeredCube z0 R hR
    simp only [S, Finset.mem_filter]
    constructor
    · intro h
      exact h.2
    · intro h
      exact ⟨hbox nidx h, h⟩
  · have hsub : S ⊆ box := by
      exact Finset.filter_subset _ _
    have hcard3 : (∏ i : Fin d, (Finset.Icc (lo i) (hi i)).card)
        ≤ ∏ _i : Fin d, ⌈R⌉₊ * 3 ^ k := by
      apply Finset.prod_le_prod
      intro i _
      rw [Int.card_Icc]
      have h1 : ((hi i : ℤ) : ℝ) ≤ (z0 i + R / 2 - r / 2 - origins index i) / r :=
        Int.floor_le _
      have h2 : (z0 i - R / 2 + r / 2 - origins index i) / r ≤ ((lo i : ℤ) : ℝ) :=
        Int.le_ceil _
      have hUL : (z0 i + R / 2 - r / 2 - origins index i) / r
          - (z0 i - R / 2 + r / 2 - origins index i) / r = R * 3 ^ k - 1 := by
        rw [← sub_div]
        have hz : z0 i + R / 2 - r / 2 - origins index i
            - (z0 i - R / 2 + r / 2 - origins index i) = R - r := by
          ring
        rw [hz, sub_div, div_self (ne_of_gt hr), div_eq_mul_inv, hrinv]
      have hceil : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
      have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ k := by positivity
      have hstep : R * 3 ^ k ≤ (⌈R⌉₊ : ℝ) * 3 ^ k :=
        mul_le_mul_of_nonneg_right hceil h3
      have hlt : ((hi i - lo i + 1 : ℤ) : ℝ) ≤ ((⌈R⌉₊ * 3 ^ k : ℕ) : ℝ) := by
        push_cast
        linarith [h1, h2, hUL, hstep]
      have hle : hi i - lo i + 1 ≤ ((⌈R⌉₊ * 3 ^ k : ℕ) : ℤ) := by
        exact_mod_cast hlt
      omega
    calc
      S.card ≤ box.card :=
        Finset.card_le_card hsub
      _ = ∏ i : Fin d, (Finset.Icc (lo i) (hi i)).card := by
        dsimp only [box]
        rw [Fintype.card_piFinset]
      _ ≤ ∏ _i : Fin d, ⌈R⌉₊ * 3 ^ k := hcard3
      _ = (⌈R⌉₊ * 3 ^ k) ^ d := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = ⌈R⌉₊ ^ d * 3 ^ (d * k) := by
        rw [mul_pow, ← pow_mul, Nat.mul_comm k d]

end Paper
