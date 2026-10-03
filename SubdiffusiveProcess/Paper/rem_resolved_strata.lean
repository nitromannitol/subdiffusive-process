module

public import Mathlib.MeasureTheory.Integral.Layercake
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Sobolev.BoundaryEnergy
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import SubdiffusiveProcess.Paper.lem_even
public import SubdiffusiveProcess.Paper.prop_folded_iteration
public import SubdiffusiveProcess.Paper.lem_primitive
public import SubdiffusiveProcess.Paper.in_iteration

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

namespace Paper


theorem aux_rem_resolved_strata_half_pos {v : ℝ}
    (hv : v ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2)) : 0 < v := by
  obtain ⟨k, rfl⟩ := hv
  exact div_pos (zpow_pos (by norm_num) k) (by norm_num)

theorem aux_rem_resolved_strata_half_mul3 {v : ℝ}
    (hv : v ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2)) :
    3 * v ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2) := by
  obtain ⟨k, rfl⟩ := hv
  refine ⟨k + 1, ?_⟩
  simp only [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
  ring

theorem aux_rem_resolved_strata_half_div3 {v : ℝ}
    (hv : v ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2)) :
    v / 3 ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2) := by
  obtain ⟨k, rfl⟩ := hv
  refine ⟨k - 1, ?_⟩
  simp only [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
  ring

theorem aux_rem_resolved_strata_least_exists {u : ℝ} (hu : 0 < u) :
    ∃ v : ℝ, IsLeast {v : ℝ | v ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2) ∧ u ≤ v} v := by
  obtain ⟨n, hlo, hhi⟩ := exists_mem_Ioc_zpow (show 0 < (2 : ℝ) * u by positivity)
    (show (1 : ℝ) < 3 by norm_num)
  refine ⟨(3 : ℝ) ^ (n + 1) / 2, ⟨⟨n + 1, rfl⟩, by linarith⟩, ?_⟩
  rintro w ⟨⟨k, rfl⟩, hkw⟩
  have hk : (3 : ℝ) ^ n < (3 : ℝ) ^ k := by linarith
  have hnk : n < k := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 hk
  have : (3 : ℝ) ^ (n + 1) ≤ (3 : ℝ) ^ k :=
    zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (by omega)
  linarith

theorem aux_rem_resolved_strata_greatest_exists {u : ℝ} (hu : 0 < u) :
    ∃ v : ℝ, IsGreatest {v : ℝ | v ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2) ∧ v ≤ u} v := by
  obtain ⟨n, hlo, hhi⟩ := exists_mem_Ico_zpow (show 0 < (2 : ℝ) * u by positivity)
    (show (1 : ℝ) < 3 by norm_num)
  refine ⟨(3 : ℝ) ^ n / 2, ⟨⟨n, rfl⟩, by linarith⟩, ?_⟩
  rintro w ⟨⟨k, rfl⟩, hkw⟩
  have hk : (3 : ℝ) ^ k < (3 : ℝ) ^ (n + 1) := by linarith
  have hnk : k < n + 1 := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 hk
  have : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ n :=
    zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (by omega)
  show (3 : ℝ) ^ k / 2 ≤ (3 : ℝ) ^ n / 2
  linarith

theorem aux_rem_resolved_strata_least_lt {u v : ℝ} (hu : 0 < u)
    (hv : IsLeast {v : ℝ | v ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2) ∧ u ≤ v} v) :
    v < 3 * u := by
  have hvpos : 0 < v := aux_rem_resolved_strata_half_pos hv.1.1
  by_contra hcon
  have hle : u ≤ v / 3 := by linarith
  have := hv.2 ⟨aux_rem_resolved_strata_half_div3 hv.1.1, hle⟩
  linarith

theorem aux_rem_resolved_strata_greatest_gt {u v : ℝ}
    (hv : IsGreatest {v : ℝ | v ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2) ∧ v ≤ u} v) :
    u < 3 * v := by
  have hvpos : 0 < v := aux_rem_resolved_strata_half_pos hv.1.1
  by_contra hcon
  have hle : 3 * v ≤ u := by linarith
  have := hv.2 ⟨aux_rem_resolved_strata_half_mul3 hv.1.1, hle⟩
  linarith

theorem aux_rem_resolved_strata_nfd_le {d : ℕ} (delta : Fin d → ℝ) (I : Finset (Fin d))
    (i : Fin d) (hi : i ∉ I) :
    sInf {v : ℝ | ∃ i : Fin d, i ∉ I ∧ v = delta i} ≤ delta i := by
  apply csInf_le
  · refine ⟨⨅ j, delta j, ?_⟩
    rintro v ⟨j, _, rfl⟩
    exact ciInf_le (Finite.bddBelow_range delta) j
  · exact ⟨i, hi, rfl⟩

theorem aux_rem_resolved_strata_nfd_mem {d : ℕ} (delta : Fin d → ℝ) (I : Finset (Fin d))
    (hI : I ≠ Finset.univ) :
    ∃ i : Fin d, i ∉ I ∧ delta i = sInf {v : ℝ | ∃ i : Fin d, i ∉ I ∧ v = delta i} := by
  have hne : ({v : ℝ | ∃ i : Fin d, i ∉ I ∧ v = delta i}).Nonempty := by
    obtain ⟨i, hi⟩ : ∃ i, i ∉ I := by
      by_contra h
      push_neg at h
      exact hI (Finset.eq_univ_iff_forall.mpr h)
    exact ⟨delta i, i, hi, rfl⟩
  have hfin : ({v : ℝ | ∃ i : Fin d, i ∉ I ∧ v = delta i}).Finite :=
    (Set.finite_range delta).subset (by rintro v ⟨i, _, rfl⟩; exact ⟨i, rfl⟩)
  obtain ⟨i, hi, heq⟩ := hne.csInf_mem hfin
  exact ⟨i, hi, heq.symm⟩

/-- Prepend one stage to a finite chain. -/
theorem aux_rem_resolved_strata_glue {α : Type} (zero : α)
    (Q : ℝ → Prop) (U : α → ℝ → ℝ → Bool → Prop) (S : α → ℝ → ℝ → Bool → α → ℝ → Prop)
    (T : ℝ → Bool → ℝ → Prop)
    (m : ℕ) (I : ℕ → α) (s R : ℕ → ℝ) (used : ℕ → Bool)
    (hQ : ∀ j : ℕ, j ≤ m → Q (s j))
    (hZ : ∀ j : ℕ, m < j → I j = zero ∧ s j = 0 ∧ R j = 0 ∧ used j = false)
    (hU : ∀ j : ℕ, j ≤ m → U (I j) (s j) (R j) (used j))
    (hS : ∀ j : ℕ, j < m → S (I j) (s j) (R j) (used j) (I (j + 1)) (s (j + 1)))
    (hT : T (s m) (used m) (R m))
    (I0 : α) (s0 R0 : ℝ) (u0 : Bool)
    (hQ0 : Q s0) (hU0 : U I0 s0 R0 u0) (hS0 : S I0 s0 R0 u0 (I 0) (s 0)) :
    ∃ (I' : ℕ → α) (s' R' : ℕ → ℝ) (used' : ℕ → Bool),
      I' 0 = I0 ∧ s' 0 = s0 ∧
      (∀ j : ℕ, j ≤ m + 1 → Q (s' j)) ∧
      (∀ j : ℕ, m + 1 < j → I' j = zero ∧ s' j = 0 ∧ R' j = 0 ∧ used' j = false) ∧
      (∀ j : ℕ, j ≤ m + 1 → U (I' j) (s' j) (R' j) (used' j)) ∧
      (∀ j : ℕ, j < m + 1 → S (I' j) (s' j) (R' j) (used' j) (I' (j + 1)) (s' (j + 1))) ∧
      T (s' (m + 1)) (used' (m + 1)) (R' (m + 1)) := by
  refine ⟨fun | 0 => I0 | j + 1 => I j, fun | 0 => s0 | j + 1 => s j,
    fun | 0 => R0 | j + 1 => R j, fun | 0 => u0 | j + 1 => used j, rfl, rfl, ?_, ?_, ?_, ?_, hT⟩
  · intro j hj
    cases j with
    | zero => exact hQ0
    | succ j => exact hQ j (by omega)
  · intro j hj
    cases j with
    | zero => omega
    | succ j => exact hZ j (by omega)
  · intro j hj
    cases j with
    | zero => exact hU0
    | succ j => exact hU j (by omega)
  · intro j hj
    cases j with
    | zero => exact hS0
    | succ j => exact hS j (by omega)

/-- A chain consisting of one terminal stage. -/
theorem aux_rem_resolved_strata_single {α : Type} (zero : α)
    (Q : ℝ → Prop) (U : α → ℝ → ℝ → Bool → Prop) (S : α → ℝ → ℝ → Bool → α → ℝ → Prop)
    (T : ℝ → Bool → ℝ → Prop)
    (I0 : α) (s0 R0 : ℝ) (u0 : Bool)
    (hQ0 : Q s0) (hU0 : U I0 s0 R0 u0) (hT0 : T s0 u0 R0) :
    ∃ (I' : ℕ → α) (s' R' : ℕ → ℝ) (used' : ℕ → Bool),
      I' 0 = I0 ∧ s' 0 = s0 ∧
      (∀ j : ℕ, j ≤ 0 → Q (s' j)) ∧
      (∀ j : ℕ, 0 < j → I' j = zero ∧ s' j = 0 ∧ R' j = 0 ∧ used' j = false) ∧
      (∀ j : ℕ, j ≤ 0 → U (I' j) (s' j) (R' j) (used' j)) ∧
      (∀ j : ℕ, j < 0 → S (I' j) (s' j) (R' j) (used' j) (I' (j + 1)) (s' (j + 1))) ∧
      T (s' 0) (used' 0) (R' 0) := by
  refine ⟨fun | 0 => I0 | _ + 1 => zero, fun | 0 => s0 | _ + 1 => 0,
    fun | 0 => R0 | _ + 1 => 0, fun | 0 => u0 | _ + 1 => false, rfl, rfl, ?_, ?_, ?_, ?_, hT0⟩
  · intro j hj
    obtain rfl : j = 0 := by omega
    exact hQ0
  · intro j hj
    cases j with
    | zero => omega
    | succ j => exact ⟨rfl, rfl, rfl, rfl⟩
  · intro j hj
    obtain rfl : j = 0 := by omega
    exact hU0
  · intro j hj
    omega

/-- One stage of the frozen boundary-strata rule: either the stage terminates, or it
activates one previously inactive coordinate with the prescribed half-triadic rounding. -/
theorem aux_rem_resolved_strata_head (d : ℕ) (Lstar Rstar eps : ℝ) (hL : 10 ≤ Lstar)
    (hRhalf : ∃ k : ℤ, Rstar = (3 : ℝ) ^ k / 2)
    (half : Set ℝ) (hhalf : half = Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2))
    (delta : Fin d → ℝ) (hdelta : ∀ i, 0 < delta i)
    (nextFaceDistance : Finset (Fin d) → ℝ)
    (hNFD : nextFaceDistance = fun I => sInf {v : ℝ | ∃ i : Fin d, i ∉ I ∧ v = delta i})
    (cap : Finset (Fin d) → ℝ)
    (hcap : cap = fun I => if I = Finset.univ then Rstar
      else min Rstar (nextFaceDistance I / (4 * Lstar)))
    (near : Finset (Fin d) → ℝ → Prop)
    (hnear : near = fun I s => ∃ i : Fin d, i ∉ I ∧ delta i ≤ 100 * Lstar * s)
    (I0 : Finset (Fin d)) (s0 : ℝ) (hs0 : s0 ∈ half) (hs0eps : eps / 2 ≤ s0) :
    (∃ (R0 : ℝ) (u0 : Bool),
      ((u0 = true ↔ (s0 < Rstar / 24 ∧ ¬ near I0 s0)) ∧
        (u0 = true →
          IsGreatest {v : ℝ | v ∈ half ∧ v ≤ cap I0} R0 ∧
            8 * s0 < R0 ∧ R0 ≤ Rstar ∧
            (∀ i : Fin d, i ∉ I0 → 4 * Lstar * R0 ≤ delta i)) ∧
        (u0 = false → R0 = 0)) ∧
      (s0 ≥ Rstar / 24 ∨ (u0 = true ∧ R0 = Rstar))) ∨
    (∃ (R0 : ℝ) (u0 : Bool) (i1 : Fin d) (s1 : ℝ), i1 ∉ I0 ∧ s1 ∈ half ∧ eps / 2 ≤ s1 ∧
      ((u0 = true ↔ (s0 < Rstar / 24 ∧ ¬ near I0 s0)) ∧
        (u0 = true →
          IsGreatest {v : ℝ | v ∈ half ∧ v ≤ cap I0} R0 ∧
            8 * s0 < R0 ∧ R0 ≤ Rstar ∧
            (∀ i : Fin d, i ∉ I0 → 4 * Lstar * R0 ≤ delta i)) ∧
        (u0 = false → R0 = 0)) ∧
      (s0 < Rstar / 24 ∧
        ((near I0 s0 ∧
            ∃ i : Fin d, i ∉ I0 ∧ delta i ≤ 100 * Lstar * s0 ∧
              insert i1 I0 = insert i I0 ∧
              IsLeast {v : ℝ | v ∈ half ∧ s0 + delta i ≤ v} s1) ∨
          (¬ near I0 s0 ∧ u0 = true ∧ R0 < Rstar ∧
            ∃ i : Fin d, i ∉ I0 ∧ delta i = nextFaceDistance I0 ∧
              insert i1 I0 = insert i I0 ∧
              IsLeast {v : ℝ | v ∈ half ∧ Lstar * R0 + delta i ≤ v} s1)))) := by
  classical
  subst hhalf
  have hs0pos : 0 < s0 := aux_rem_resolved_strata_half_pos hs0
  have hLpos : 0 < Lstar := by linarith
  by_cases hlarge : Rstar / 24 ≤ s0
  · left
    refine ⟨0, false, ⟨?_, ?_, fun _ => rfl⟩, Or.inl hlarge⟩
    · constructor
      · intro h; exact absurd h (by simp)
      · rintro ⟨h, _⟩; linarith
    · intro h; exact absurd h (by simp)
  have hsmall : s0 < Rstar / 24 := lt_of_not_ge hlarge
  by_cases hnear0 : near I0 s0
  · right
    have hnear' := hnear0
    rw [hnear] at hnear'
    obtain ⟨i, hi, hdi⟩ := hnear'
    obtain ⟨s1, hs1⟩ := aux_rem_resolved_strata_least_exists
      (show 0 < s0 + delta i by linarith [hdelta i])
    refine ⟨0, false, i, s1, hi, hs1.1.1, ?_, ⟨?_, ?_, fun _ => rfl⟩, hsmall,
      Or.inl ⟨hnear0, i, hi, hdi, rfl, hs1⟩⟩
    · linarith [hs1.1.2, hdelta i]
    · constructor
      · intro h; exact absurd h (by simp)
      · rintro ⟨_, h⟩; exact absurd hnear0 h
    · intro h; exact absurd h (by simp)
  · have hfar : ∀ i : Fin d, i ∉ I0 → 100 * Lstar * s0 < delta i := by
      intro i hi
      by_contra hcon
      apply hnear0
      rw [hnear]
      exact ⟨i, hi, le_of_not_gt hcon⟩
    have hcapeq : ∀ I, cap I = if I = Finset.univ then Rstar
        else min Rstar (nextFaceDistance I / (4 * Lstar)) := by
      intro I; rw [hcap]
    have hcap_le : cap I0 ≤ Rstar := by
      rw [hcapeq]; split_ifs
      · exact le_rfl
      · exact min_le_left _ _
    have hcap_big : 24 * s0 < cap I0 := by
      rw [hcapeq]; split_ifs with hI
      · linarith
      · obtain ⟨i, hi, hdi⟩ := aux_rem_resolved_strata_nfd_mem delta I0 hI
        have hN : nextFaceDistance I0 = delta i := by rw [hNFD, hdi]
        apply lt_min (by linarith)
        rw [hN, lt_div_iff₀ (by positivity)]
        have := hfar i hi
        nlinarith
    obtain ⟨R0, hR0⟩ := aux_rem_resolved_strata_greatest_exists
      (show 0 < cap I0 by linarith)
    have hR0le : R0 ≤ Rstar := hR0.1.2.trans hcap_le
    have h3 := aux_rem_resolved_strata_greatest_gt hR0
    have h8 : 8 * s0 < R0 := by linarith
    have hR0pos : 0 < R0 := aux_rem_resolved_strata_half_pos hR0.1.1
    have hclear : ∀ i : Fin d, i ∉ I0 → 4 * Lstar * R0 ≤ delta i := by
      intro i hi
      have hI : I0 ≠ Finset.univ := by
        intro h; exact hi (h ▸ Finset.mem_univ i)
      have hcapN : cap I0 ≤ nextFaceDistance I0 / (4 * Lstar) := by
        rw [hcapeq, if_neg hI]; exact min_le_right _ _
      have hN : nextFaceDistance I0 ≤ delta i := by
        rw [hNFD]; exact aux_rem_resolved_strata_nfd_le delta I0 i hi
      have hRN : R0 ≤ nextFaceDistance I0 / (4 * Lstar) := hR0.1.2.trans hcapN
      rw [le_div_iff₀ (by positivity)] at hRN
      linarith
    have hU : ((true = true ↔ (s0 < Rstar / 24 ∧ ¬ near I0 s0)) ∧
        (true = true →
          IsGreatest {v : ℝ | v ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2) ∧ v ≤ cap I0} R0 ∧
            8 * s0 < R0 ∧ R0 ≤ Rstar ∧
            (∀ i : Fin d, i ∉ I0 → 4 * Lstar * R0 ≤ delta i)) ∧
        (true = false → R0 = 0)) :=
      ⟨by simp [hsmall, hnear0], fun _ => ⟨hR0, h8, hR0le, hclear⟩, fun h => absurd h (by simp)⟩
    by_cases hRe : R0 = Rstar
    · left
      exact ⟨R0, true, hU, Or.inr ⟨rfl, hRe⟩⟩
    · right
      have hRlt : R0 < Rstar := lt_of_le_of_ne hR0le hRe
      have hI0 : I0 ≠ Finset.univ := by
        intro hI
        apply hRe
        have hcapR : cap I0 = Rstar := by rw [hcapeq, if_pos hI]
        obtain ⟨k, hk⟩ := hRhalf
        have hmem : Rstar ∈ {v : ℝ | v ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2) ∧
            v ≤ cap I0} := ⟨⟨k, hk.symm⟩, hcapR.ge⟩
        exact le_antisymm hR0le (hR0.2 hmem)
      obtain ⟨i, hi, hdi⟩ := aux_rem_resolved_strata_nfd_mem delta I0 hI0
      have hdi' : delta i = nextFaceDistance I0 := by rw [hNFD]; exact hdi
      obtain ⟨s1, hs1⟩ := aux_rem_resolved_strata_least_exists
        (show 0 < Lstar * R0 + delta i by have := hdelta i; positivity)
      refine ⟨R0, true, i, s1, hi, hs1.1.1, ?_, hU, hsmall,
        Or.inr ⟨hnear0, rfl, hRlt, i, hi, hdi', rfl, hs1⟩⟩
      have h1 : R0 ≤ Lstar * R0 := by nlinarith
      linarith [hs1.1.2, hdelta i]



theorem aux_rem_resolved_strata_chain (d : ℕ) (Lstar Rstar eps : ℝ) (hL : 10 ≤ Lstar)
    (hRhalf : ∃ k : ℤ, Rstar = (3 : ℝ) ^ k / 2)
    (half : Set ℝ) (hhalf : half = Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2))
    (delta : Fin d → ℝ) (hdelta : ∀ i, 0 < delta i)
    (nextFaceDistance : Finset (Fin d) → ℝ)
    (hNFD : nextFaceDistance = fun I => sInf {v : ℝ | ∃ i : Fin d, i ∉ I ∧ v = delta i})
    (cap : Finset (Fin d) → ℝ)
    (hcap : cap = fun I => if I = Finset.univ then Rstar
      else min Rstar (nextFaceDistance I / (4 * Lstar)))
    (near : Finset (Fin d) → ℝ → Prop)
    (hnear : near = fun I s => ∃ i : Fin d, i ∉ I ∧ delta i ≤ 100 * Lstar * s) :
    ∀ (n : ℕ) (I0 : Finset (Fin d)) (s0 : ℝ), I0.card + n = d → s0 ∈ half → eps / 2 ≤ s0 →
    ∃ (m : ℕ) (I : ℕ → Finset (Fin d)) (s R : ℕ → ℝ) (used : ℕ → Bool),
      m ≤ n ∧ I 0 = I0 ∧ s 0 = s0 ∧
      (∀ j : ℕ, j ≤ m → s j ∈ half ∧ 0 < s j ∧ eps / 2 ≤ s j) ∧
      (∀ j : ℕ, m < j → I j = ∅ ∧ s j = 0 ∧ R j = 0 ∧ used j = false) ∧
      (∀ j : ℕ, j ≤ m →
        (used j = true ↔ (s j < Rstar / 24 ∧ ¬ near (I j) (s j))) ∧
        (used j = true →
          IsGreatest {v : ℝ | v ∈ half ∧ v ≤ cap (I j)} (R j) ∧
            8 * s j < R j ∧ R j ≤ Rstar ∧
            (∀ i : Fin d, i ∉ I j → 4 * Lstar * R j ≤ delta i)) ∧
        (used j = false → R j = 0)) ∧
      (∀ j : ℕ, j < m → s j < Rstar / 24 ∧
        ((near (I j) (s j) ∧
            ∃ i : Fin d, i ∉ I j ∧ delta i ≤ 100 * Lstar * s j ∧
              I (j + 1) = insert i (I j) ∧
              IsLeast {v : ℝ | v ∈ half ∧ s j + delta i ≤ v} (s (j + 1))) ∨
          (¬ near (I j) (s j) ∧ used j = true ∧ R j < Rstar ∧
            ∃ i : Fin d, i ∉ I j ∧ delta i = nextFaceDistance (I j) ∧
              I (j + 1) = insert i (I j) ∧
              IsLeast {v : ℝ | v ∈ half ∧ Lstar * R j + delta i ≤ v} (s (j + 1))))) ∧
      (s m ≥ Rstar / 24 ∨ (used m = true ∧ R m = Rstar)) := by
  classical
  let Q : ℝ → Prop := fun s => s ∈ half ∧ 0 < s ∧ eps / 2 ≤ s
  let U : Finset (Fin d) → ℝ → ℝ → Bool → Prop := fun I s R u =>
    (u = true ↔ (s < Rstar / 24 ∧ ¬ near I s)) ∧
      (u = true →
        IsGreatest {v : ℝ | v ∈ half ∧ v ≤ cap I} R ∧
          8 * s < R ∧ R ≤ Rstar ∧
          (∀ i : Fin d, i ∉ I → 4 * Lstar * R ≤ delta i)) ∧
      (u = false → R = 0)
  let S : Finset (Fin d) → ℝ → ℝ → Bool → Finset (Fin d) → ℝ → Prop := fun I s R u I' s' =>
    s < Rstar / 24 ∧
      ((near I s ∧
          ∃ i : Fin d, i ∉ I ∧ delta i ≤ 100 * Lstar * s ∧
            I' = insert i I ∧
            IsLeast {v : ℝ | v ∈ half ∧ s + delta i ≤ v} s') ∨
        (¬ near I s ∧ u = true ∧ R < Rstar ∧
          ∃ i : Fin d, i ∉ I ∧ delta i = nextFaceDistance I ∧
            I' = insert i I ∧
            IsLeast {v : ℝ | v ∈ half ∧ Lstar * R + delta i ≤ v} s'))
  let T : ℝ → Bool → ℝ → Prop := fun s u R => s ≥ Rstar / 24 ∨ (u = true ∧ R = Rstar)
  have hQ0 : ∀ s0, s0 ∈ half → eps / 2 ≤ s0 → Q s0 := by
    intro s0 hs0 hs0eps
    refine ⟨hs0, ?_, hs0eps⟩
    rw [hhalf] at hs0
    exact aux_rem_resolved_strata_half_pos hs0
  intro n
  induction n with
  | zero =>
    intro I0 s0 hcard hs0 hs0eps
    rcases aux_rem_resolved_strata_head d Lstar Rstar eps hL hRhalf half hhalf delta
        hdelta nextFaceDistance hNFD cap hcap near hnear I0 s0 hs0 hs0eps with
      ⟨R0, u0, hU0, hT0⟩ | ⟨R0, u0, i1, s1, hi1, _, _, _, _⟩
    · obtain ⟨I, s, R, used, hI0, hs0', hQ, hZ, hU, hS, hT⟩ :=
        aux_rem_resolved_strata_single (∅ : Finset (Fin d)) Q U S T I0 s0 R0 u0
          (hQ0 s0 hs0 hs0eps) hU0 hT0
      exact ⟨0, I, s, R, used, le_rfl, hI0, hs0', hQ, hZ, hU, hS, hT⟩
    · exfalso
      have h1 : (insert i1 I0).card = I0.card + 1 := Finset.card_insert_of_notMem hi1
      have h2 : (insert i1 I0).card ≤ d := by
        simpa using Finset.card_le_univ (insert i1 I0)
      omega
  | succ n ih =>
    intro I0 s0 hcard hs0 hs0eps
    rcases aux_rem_resolved_strata_head d Lstar Rstar eps hL hRhalf half hhalf delta
        hdelta nextFaceDistance hNFD cap hcap near hnear I0 s0 hs0 hs0eps with
      ⟨R0, u0, hU0, hT0⟩ | ⟨R0, u0, i1, s1, hi1, hs1, hs1eps, hU0, hS0⟩
    · obtain ⟨I, s, R, used, hI0, hs0', hQ, hZ, hU, hS, hT⟩ :=
        aux_rem_resolved_strata_single (∅ : Finset (Fin d)) Q U S T I0 s0 R0 u0
          (hQ0 s0 hs0 hs0eps) hU0 hT0
      exact ⟨0, I, s, R, used, Nat.zero_le _, hI0, hs0', hQ, hZ, hU, hS, hT⟩
    · have hcard' : (insert i1 I0).card + n = d := by
        rw [Finset.card_insert_of_notMem hi1]; omega
      obtain ⟨m, I, s, R, used, hm, hI0, hs0', hQ, hZ, hU, hS, hT⟩ :=
        ih (insert i1 I0) s1 hcard' hs1 hs1eps
      have hS0' : S I0 s0 R0 u0 (I 0) (s 0) := by
        rw [hI0, hs0']
        rcases hS0 with ⟨hsm, ⟨hn, i, hi, hdi, hins, hleast⟩ | ⟨hn, hu, hR, i, hi, hdi, hins, hleast⟩⟩
        · exact ⟨hsm, Or.inl ⟨hn, i, hi, hdi, hins, hleast⟩⟩
        · exact ⟨hsm, Or.inr ⟨hn, hu, hR, i, hi, hdi, hins, hleast⟩⟩
      obtain ⟨I', s', R', used', hI0', hs0'', hQ', hZ', hU', hS', hT'⟩ :=
        aux_rem_resolved_strata_glue (∅ : Finset (Fin d)) Q U S T m I s R used hQ hZ hU hS hT
          I0 s0 R0 u0 (hQ0 s0 hs0 hs0eps) hU0 hS0'
      exact ⟨m + 1, I', s', R', used', by omega, hI0', hs0'', hQ', hZ', hU', hS', hT'⟩




/-- Telescoping of the radial ratios of the used stages along the first `n` stages. -/
theorem aux_rem_resolved_strata_telescope (m : ℕ) (s R : ℕ → ℝ) (used : ℕ → Bool) (K : ℝ)
    (hK : 1 ≤ K) (hs : ∀ j : ℕ, j ≤ m → 0 < s j)
    (hR : ∀ j : ℕ, j ≤ m → used j = true → 0 < R j)
    (hnextU : ∀ j : ℕ, j < m → used j = true → s (j + 1) ≤ K * R j)
    (hnextN : ∀ j : ℕ, j < m → used j = false → s (j + 1) ≤ K * s j) :
    ∀ n : ℕ, n ≤ m →
      (∏ j ∈ (Finset.range n).filter (fun j => used j = true), (s j / R j)) ≤
        K ^ n * s 0 / s n := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  intro n
  induction n with
  | zero =>
    intro _
    simp [(hs 0 (Nat.zero_le _)).ne']
  | succ n ih =>
    intro hn
    have ihn := ih (by omega)
    have hsn := hs n (by omega)
    have hsn1 := hs (n + 1) hn
    have hs0 := hs 0 (by omega)
    have hKn : 0 < K ^ n := by positivity
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hu : used n = true
    · rw [if_pos hu, Finset.prod_insert (by simp)]
      have hRn := hR n (by omega) hu
      have hstep := hnextU n (by omega) hu
      calc s n / R n * ∏ j ∈ (Finset.range n).filter (fun j => used j = true), (s j / R j)
          ≤ s n / R n * (K ^ n * s 0 / s n) :=
            mul_le_mul_of_nonneg_left ihn (by positivity)
        _ = K ^ n * s 0 / R n := by field_simp
        _ ≤ K ^ (n + 1) * s 0 / s (n + 1) := by
            rw [div_le_div_iff₀ hRn hsn1]
            calc K ^ n * s 0 * s (n + 1) ≤ K ^ n * s 0 * (K * R n) :=
                  mul_le_mul_of_nonneg_left hstep (by positivity)
              _ = K ^ (n + 1) * s 0 * R n := by ring
    · rw [if_neg hu]
      have hu' : used n = false := by simpa using hu
      have hstep := hnextN n (by omega) hu'
      calc (∏ j ∈ (Finset.range n).filter (fun j => used j = true), (s j / R j))
          ≤ K ^ n * s 0 / s n := ihn
        _ ≤ K ^ (n + 1) * s 0 / s (n + 1) := by
            rw [div_le_div_iff₀ hsn hsn1]
            calc K ^ n * s 0 * s (n + 1) ≤ K ^ n * s 0 * (K * s n) :=
                  mul_le_mul_of_nonneg_left hstep (by positivity)
              _ = K ^ (n + 1) * s 0 * s n := by ring

/-- The geometric loss of the whole chain, before raising to the power `t0`. -/
theorem aux_rem_resolved_strata_geom_base (d m : ℕ) (hm : m ≤ d) (s R : ℕ → ℝ)
    (used : ℕ → Bool) (K r Rstar : ℝ) (hK : 1 ≤ K) (hr : 0 < r) (hRstar : 0 < Rstar)
    (hs0 : s 0 < 3 * (r / 2))
    (hs : ∀ j : ℕ, j ≤ m → 0 < s j)
    (hR : ∀ j : ℕ, j ≤ m → used j = true → 0 < R j)
    (hnextU : ∀ j : ℕ, j < m → used j = true → s (j + 1) ≤ K * R j)
    (hnextN : ∀ j : ℕ, j < m → used j = false → s (j + 1) ≤ K * s j)
    (hT : s m ≥ Rstar / 24 ∨ (used m = true ∧ R m = Rstar))
    (hUm : used m = true → s m < Rstar / 24) :
    (∏ j ∈ (Finset.range (m + 1)).filter (fun j => used j = true), (s j / R j)) ≤
      36 * K ^ d * (r / Rstar) := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have htel := aux_rem_resolved_strata_telescope m s R used K hK hs hR hnextU hnextN m le_rfl
  have hsm := hs m le_rfl
  have hs00 := hs 0 (Nat.zero_le _)
  have hKmd : K ^ m ≤ K ^ d := pow_le_pow_right₀ hK hm
  have hKm : 0 < K ^ m := by positivity
  have hprod_nonneg : 0 ≤ ∏ j ∈ (Finset.range m).filter (fun j => used j = true), (s j / R j) := by
    apply Finset.prod_nonneg
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    exact (div_pos (hs j (by omega)) (hR j (by omega) hj.2)).le
  have hfinal : K ^ m * s 0 ≤ K ^ d * (3 * (r / 2)) :=
    mul_le_mul hKmd hs0.le hs00.le (by positivity)
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases hu : used m = true
  · rw [if_pos hu, Finset.prod_insert (by simp)]
    have hRm : R m = Rstar := by
      rcases hT with h | h
      · exact absurd h (not_le.mpr (hUm hu))
      · exact h.2
    rw [hRm]
    calc s m / Rstar * ∏ j ∈ (Finset.range m).filter (fun j => used j = true), (s j / R j)
        ≤ s m / Rstar * (K ^ m * s 0 / s m) :=
          mul_le_mul_of_nonneg_left htel (by positivity)
      _ = (K ^ m * s 0) / Rstar := by field_simp
      _ ≤ (K ^ d * (3 * (r / 2))) / Rstar := div_le_div_of_nonneg_right hfinal hRstar.le
      _ ≤ 36 * K ^ d * (r / Rstar) := by
          rw [div_le_iff₀ hRstar]
          have : 0 ≤ K ^ d * r := by positivity
          field_simp
          nlinarith
  · rw [if_neg hu]
    have hlarge : Rstar / 24 ≤ s m := by
      rcases hT with h | h
      · exact h
      · exact absurd h.1 hu
    calc (∏ j ∈ (Finset.range m).filter (fun j => used j = true), (s j / R j))
        ≤ K ^ m * s 0 / s m := htel
      _ ≤ K ^ m * s 0 / (Rstar / 24) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hlarge
      _ ≤ K ^ d * (3 * (r / 2)) / (Rstar / 24) :=
          div_le_div_of_nonneg_right hfinal (by positivity)
      _ = 36 * K ^ d * (r / Rstar) := by field_simp; ring

/-- The geometric product clause, with the constant `(36 K^d)^t0`. -/
theorem aux_rem_resolved_strata_geom (d m : ℕ) (hm : m ≤ d) (s R : ℕ → ℝ)
    (used : ℕ → Bool) (K r Rstar t0 : ℝ) (hK : 1 ≤ K) (hr : 0 < r) (hRstar : 0 < Rstar)
    (ht0 : 0 < t0)
    (hs0 : s 0 < 3 * (r / 2))
    (hs : ∀ j : ℕ, j ≤ m → 0 < s j)
    (hR : ∀ j : ℕ, j ≤ m → used j = true → 0 < R j)
    (hnextU : ∀ j : ℕ, j < m → used j = true → s (j + 1) ≤ K * R j)
    (hnextN : ∀ j : ℕ, j < m → used j = false → s (j + 1) ≤ K * s j)
    (hT : s m ≥ Rstar / 24 ∨ (used m = true ∧ R m = Rstar))
    (hUm : used m = true → s m < Rstar / 24) :
    (∏ j ∈ (Finset.range (m + 1)).filter (fun j => used j = true), (s j / R j) ^ t0) ≤
      (36 * K ^ d) ^ t0 * (r / Rstar) ^ t0 := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hnn : ∀ j ∈ (Finset.range (m + 1)).filter (fun j => used j = true), 0 ≤ s j / R j := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    exact (div_pos (hs j (by omega)) (hR j (by omega) hj.2)).le
  rw [Real.finset_prod_rpow _ _ hnn t0, ← Real.mul_rpow (by positivity) (by positivity)]
  exact Real.rpow_le_rpow (Finset.prod_nonneg hnn)
    (aux_rem_resolved_strata_geom_base d m hm s R used K r Rstar hK hr hRstar hs0 hs hR
      hnextU hnextN hT hUm) ht0.le

/-- Radius growth across one transition of the frozen chain rule. -/
theorem aux_rem_resolved_strata_next (d : ℕ) (Lstar Rstar : ℝ) (hL : 10 ≤ Lstar)
    (hRhalf : ∃ k : ℤ, Rstar = (3 : ℝ) ^ k / 2)
    (half : Set ℝ) (hhalf : half = Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2))
    (delta : Fin d → ℝ) (hdelta : ∀ i, 0 < delta i)
    (nextFaceDistance : Finset (Fin d) → ℝ)
    (cap : Finset (Fin d) → ℝ)
    (hcap : cap = fun I => if I = Finset.univ then Rstar
      else min Rstar (nextFaceDistance I / (4 * Lstar)))
    (near : Finset (Fin d) → ℝ → Prop)
    (I1 I2 : Finset (Fin d)) (s1 R1 s2 : ℝ) (u : Bool) (hs1 : 0 < s1)
    (hU : (u = true ↔ (s1 < Rstar / 24 ∧ ¬ near I1 s1)) ∧
        (u = true →
          IsGreatest {v : ℝ | v ∈ half ∧ v ≤ cap I1} R1 ∧
            8 * s1 < R1 ∧ R1 ≤ Rstar ∧
            (∀ i : Fin d, i ∉ I1 → 4 * Lstar * R1 ≤ delta i)) ∧
        (u = false → R1 = 0))
    (hS : s1 < Rstar / 24 ∧
        ((near I1 s1 ∧
            ∃ i : Fin d, i ∉ I1 ∧ delta i ≤ 100 * Lstar * s1 ∧
              I2 = insert i I1 ∧
              IsLeast {v : ℝ | v ∈ half ∧ s1 + delta i ≤ v} s2) ∨
          (¬ near I1 s1 ∧ u = true ∧ R1 < Rstar ∧
            ∃ i : Fin d, i ∉ I1 ∧ delta i = nextFaceDistance I1 ∧
              I2 = insert i I1 ∧
              IsLeast {v : ℝ | v ∈ half ∧ Lstar * R1 + delta i ≤ v} s2))) :
    (u = true → s2 ≤ 3 * (1 + 100 * Lstar) * R1) ∧
      (u = false → s2 ≤ 3 * (1 + 100 * Lstar) * s1) := by
  subst hhalf
  have hLpos : 0 < Lstar := by linarith
  rcases hS with ⟨_, ⟨hn, i, hi, hdi, _, hleast⟩ | ⟨hn, hu, hRlt, i, hi, hdi, _, hleast⟩⟩
  · have hu : u = false := by
      cases u with
      | false => rfl
      | true => exact absurd hn (hU.1.mp rfl).2
    refine ⟨fun h => absurd (hu ▸ h) (by simp), fun _ => ?_⟩
    have hlt := aux_rem_resolved_strata_least_lt (show 0 < s1 + delta i by linarith [hdelta i])
      hleast
    nlinarith
  · refine ⟨fun _ => ?_, fun h => absurd (hu ▸ h) (by simp)⟩
    obtain ⟨hgr, h8, _, _⟩ := hU.2.1 hu
    have hR1 : 0 < R1 := aux_rem_resolved_strata_half_pos hgr.1.1
    have hgt := aux_rem_resolved_strata_greatest_gt hgr
    have hI : I1 ≠ Finset.univ := by
      intro h; exact hi (h ▸ Finset.mem_univ i)
    have hcapI : cap I1 = min Rstar (nextFaceDistance I1 / (4 * Lstar)) := by
      rw [hcap]; simp only [if_neg hI]
    have hNlt : nextFaceDistance I1 / (4 * Lstar) < Rstar := by
      by_contra hcon
      push_neg at hcon
      have hcapR : cap I1 = Rstar := by rw [hcapI]; exact min_eq_left hcon
      obtain ⟨k, hk⟩ := hRhalf
      have := hgr.2 ⟨⟨k, hk.symm⟩, hcapR.ge⟩
      linarith
    have hcapN : cap I1 = nextFaceDistance I1 / (4 * Lstar) := by
      rw [hcapI]; exact min_eq_right hNlt.le
    rw [hcapN, div_lt_iff₀ (by positivity)] at hgt
    have hlt := aux_rem_resolved_strata_least_lt
      (show 0 < Lstar * R1 + delta i by have := hdelta i; positivity) hleast
    rw [hdi] at hlt
    nlinarith



theorem aux_rem_resolved_strata_rpow_ratio (s R t e : ℝ) (hs : 0 ≤ s) (hR : 0 < R) :
    (s / R) ^ t * R ^ e = s ^ t * R ^ (e - t) := by
  rw [Real.div_rpow hs hR.le, Real.rpow_sub hR]
  have : 0 < R ^ t := Real.rpow_pos_of_pos hR t
  field_simp

/-- Multiplicative constants of the used stages: allowances add. -/
theorem aux_rem_resolved_strata_prod_allow {ι : Type} (S : Finset ι) (N : ℕ) (hSN : S.card ≤ N)
    (Cstep c : ℝ) (hCstep : 1 ≤ Cstep) (B : ι → ℝ) :
    (∏ j ∈ S, (Cstep * Real.exp (c * B j))) ≤ Cstep ^ N * Real.exp (c * ∑ j ∈ S, B j) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.mul_sum, Real.exp_sum]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hCstep hSN)
    (Finset.prod_nonneg fun j _ => (Real.exp_pos _).le)



theorem aux_rem_resolved_strata_energy_comp (d m : ℕ)
    (s R : ℕ → ℝ) (used : ℕ → Bool) (E G Bv bv : ℕ → ℝ)
    (K t0 Cstep c Kf : ℝ)
    (hK : 1 ≤ K) (ht0 : 0 < t0) (hCstep : 1 ≤ Cstep) (hc : 0 ≤ c)
    (hs : ∀ j : ℕ, j ≤ m → 0 < s j)
    (hR : ∀ j : ℕ, j ≤ m → used j = true → 0 < R j)
    (hB : ∀ j : ℕ, j ≤ m → used j = true → 0 ≤ Bv j)
    (hb : ∀ j : ℕ, j ≤ m → used j = true → 0 < bv j)
    (hE : ∀ j : ℕ, j ≤ m → 0 ≤ E j)
    (hnextU : ∀ j : ℕ, j < m → used j = true → s (j + 1) ≤ K * R j)
    (hnextN : ∀ j : ℕ, j < m → used j = false → s (j + 1) ≤ K * s j)
    (hstepU : ∀ j : ℕ, j ≤ m → used j = true →
        E j ≤ Cstep * Real.exp (c * Bv j) * (s j / R j) ^ t0 *
          (G j + (bv j)⁻¹ * Kf ^ 2 * R j ^ ((d : ℝ) + 2)))
    (hGnext : ∀ j : ℕ, j < m → used j = true → G j ≤ E (j + 1))
    (hstepN : ∀ j : ℕ, j < m → used j = false → E j ≤ E (j + 1)) :
    E 0 ≤ (s 0) ^ t0 *
      (∏ j ∈ Finset.range m,
        (if used j = true then Cstep * Real.exp (c * Bv j) else 1) * K ^ t0) *
      (E m / (s m) ^ t0 + ∑ j ∈ Finset.range m,
        (if used j = true then (bv j)⁻¹ * Kf ^ 2 * R j ^ ((d : ℝ) + 2 - t0) else 0)) := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  refine SubdiffusiveProcess.finite_radius_energy_composition m t0 ht0.le s
    (fun j => if used j = true then R j else s j) E
    (fun j => if used j = true then Cstep * Real.exp (c * Bv j) else 1) (fun _ => K)
    (fun j => if used j = true then (bv j)⁻¹ * Kf ^ 2 * R j ^ ((d : ℝ) + 2 - t0) else 0)
    hs ?_ hE ?_ (fun _ _ => hK) ?_ ?_ ?_
  · intro j hj
    by_cases hu : used j = true
    · simp only [if_pos hu]; exact hR j hj.le hu
    · simp only [if_neg hu]; exact hs j hj.le
  · intro j hj
    by_cases hu : used j = true
    · simp only [if_pos hu]
      have h1 : 1 ≤ Real.exp (c * Bv j) := Real.one_le_exp (mul_nonneg hc (hB j hj.le hu))
      nlinarith
    · simp only [if_neg hu]; exact le_rfl
  · intro j hj
    by_cases hu : used j = true
    · simp only [if_pos hu]
      have := hb j hj.le hu
      have := hR j hj.le hu
      positivity
    · simp only [if_neg hu]; exact le_rfl
  · intro j hj
    by_cases hu : used j = true
    · simp only [if_pos hu]; exact hnextU j hj hu
    · simp only [if_neg hu]; exact hnextN j hj (by simpa using hu)
  · intro j hj
    by_cases hu : used j = true
    · simp only [if_pos hu]
      have hRj := hR j hj.le hu
      have hsj := hs j hj.le
      have hZ0 : 0 ≤ Cstep * Real.exp (c * Bv j) := by
        have := Real.exp_pos (c * Bv j); nlinarith
      have hrat : 0 ≤ (s j / R j) ^ t0 := Real.rpow_nonneg (div_pos hsj hRj).le _
      calc E j ≤ Cstep * Real.exp (c * Bv j) * (s j / R j) ^ t0 *
            (G j + (bv j)⁻¹ * Kf ^ 2 * R j ^ ((d : ℝ) + 2)) := hstepU j hj.le hu
        _ ≤ Cstep * Real.exp (c * Bv j) * (s j / R j) ^ t0 *
            (E (j + 1) + (bv j)⁻¹ * Kf ^ 2 * R j ^ ((d : ℝ) + 2)) := by
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg hZ0 hrat)
            linarith [hGnext j hj hu]
        _ = Cstep * Real.exp (c * Bv j) * ((s j / R j) ^ t0 * E (j + 1) +
            (s j) ^ t0 * ((bv j)⁻¹ * Kf ^ 2 * R j ^ ((d : ℝ) + 2 - t0))) := by
            have := aux_rem_resolved_strata_rpow_ratio (s j) (R j) t0 ((d : ℝ) + 2) hsj.le hRj
            calc _ = Cstep * Real.exp (c * Bv j) * ((s j / R j) ^ t0 * E (j + 1) +
                  (bv j)⁻¹ * Kf ^ 2 * ((s j / R j) ^ t0 * R j ^ ((d : ℝ) + 2))) := by ring
              _ = _ := by rw [this]; ring
    · simp only [if_neg hu]
      have hsj := hs j hj.le
      rw [div_self hsj.ne', Real.one_rpow]
      simpa using hstepN j hj (by simpa using hu)

/-- Terminal stage: either the trivial large-radius bound or the final admissible root. -/
theorem aux_rem_resolved_strata_energy_terminal (d m : ℕ)
    (s R : ℕ → ℝ) (used : ℕ → Bool) (E G Bv bv : ℕ → ℝ)
    (Rstar t0 Cstep c Kf Euniv : ℝ)
    (hRstar : 0 < Rstar) (ht0 : 0 < t0) (hCstep : 1 ≤ Cstep) (hc : 0 ≤ c) (hEuniv : 0 ≤ Euniv)
    (hs : ∀ j : ℕ, j ≤ m → 0 < s j)
    (hR : ∀ j : ℕ, j ≤ m → used j = true → 0 < R j)
    (hB : ∀ j : ℕ, j ≤ m → used j = true → 0 ≤ Bv j)
    (hb : ∀ j : ℕ, j ≤ m → used j = true → 0 < bv j)
    (hstepU : ∀ j : ℕ, j ≤ m → used j = true →
        E j ≤ Cstep * Real.exp (c * Bv j) * (s j / R j) ^ t0 *
          (G j + (bv j)⁻¹ * Kf ^ 2 * R j ^ ((d : ℝ) + 2)))
    (hGlast : used m = true → G m ≤ Euniv)
    (hlastN : used m = false → E m ≤ Euniv)
    (hT : s m ≥ Rstar / 24 ∨ (used m = true ∧ R m = Rstar))
    (hUm : used m = true → s m < Rstar / 24) :
    E m / (s m) ^ t0 + ∑ j ∈ Finset.range m,
        (if used j = true then (bv j)⁻¹ * Kf ^ 2 * R j ^ ((d : ℝ) + 2 - t0) else 0) ≤
      24 ^ t0 * (if used m = true then Cstep * Real.exp (c * Bv m) else 1) *
        (Rstar ^ (-t0) * Euniv + ∑ j ∈ Finset.range (m + 1),
          (if used j = true then (bv j)⁻¹ * Kf ^ 2 * R j ^ ((d : ℝ) + 2 - t0) else 0)) := by
  set F : ℕ → ℝ := fun j =>
    if used j = true then (bv j)⁻¹ * Kf ^ 2 * R j ^ ((d : ℝ) + 2 - t0) else 0 with hFdef
  have hF : ∀ j, j ≤ m → 0 ≤ F j := by
    intro j hj
    simp only [hFdef]
    split_ifs with hu
    · have := hb j hj hu; have := hR j hj hu; positivity
    · exact le_rfl
  have hsumF : 0 ≤ ∑ j ∈ Finset.range m, F j :=
    Finset.sum_nonneg fun j hj => hF j (Finset.mem_range.mp hj).le
  have h24 : 1 ≤ (24 : ℝ) ^ t0 := Real.one_le_rpow (by norm_num) ht0.le
  have hsm := hs m le_rfl
  have hsmt : 0 < (s m) ^ t0 := Real.rpow_pos_of_pos hsm t0
  have hRt : 0 < Rstar ^ (-t0) := Real.rpow_pos_of_pos hRstar _
  rw [Finset.sum_range_succ]
  by_cases hu : used m = true
  · rw [if_pos hu]
    have hRm : R m = Rstar := by
      rcases hT with h | h
      · exact absurd h (not_le.mpr (hUm hu))
      · exact h.2
    have hZ : 1 ≤ Cstep * Real.exp (c * Bv m) := by
      have h1 : 1 ≤ Real.exp (c * Bv m) := Real.one_le_exp (mul_nonneg hc (hB m le_rfl hu))
      nlinarith
    have hFm : F m = (bv m)⁻¹ * Kf ^ 2 * Rstar ^ ((d : ℝ) + 2 - t0) := by
      simp only [hFdef, if_pos hu, hRm]
    have hbm := hb m le_rfl hu
    have hkey : E m / (s m) ^ t0 ≤ Cstep * Real.exp (c * Bv m) * (Rstar ^ (-t0) * Euniv + F m) := by
      rw [div_le_iff₀ hsmt]
      have hst := hstepU m le_rfl hu
      rw [hRm] at hst
      have hrat : 0 ≤ (s m / Rstar) ^ t0 := Real.rpow_nonneg (div_pos hsm hRstar).le _
      have hZ0 : 0 ≤ Cstep * Real.exp (c * Bv m) := by linarith
      have hsR : (s m / Rstar) ^ t0 = (s m) ^ t0 * Rstar ^ (-t0) := by
        rw [Real.div_rpow hsm.le hRstar.le, Real.rpow_neg hRstar.le, div_eq_mul_inv]
      have hid := aux_rem_resolved_strata_rpow_ratio (s m) Rstar t0 ((d : ℝ) + 2) hsm.le hRstar
      calc E m ≤ Cstep * Real.exp (c * Bv m) * (s m / Rstar) ^ t0 *
            (G m + (bv m)⁻¹ * Kf ^ 2 * Rstar ^ ((d : ℝ) + 2)) := hst
        _ ≤ Cstep * Real.exp (c * Bv m) * (s m / Rstar) ^ t0 *
            (Euniv + (bv m)⁻¹ * Kf ^ 2 * Rstar ^ ((d : ℝ) + 2)) := by
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg hZ0 hrat)
            linarith [hGlast hu]
        _ = Cstep * Real.exp (c * Bv m) * ((s m / Rstar) ^ t0 * Euniv +
            (bv m)⁻¹ * Kf ^ 2 * ((s m / Rstar) ^ t0 * Rstar ^ ((d : ℝ) + 2))) := by ring
        _ = Cstep * Real.exp (c * Bv m) * (Rstar ^ (-t0) * Euniv + F m) * (s m) ^ t0 := by
            rw [hid, hFm]
            nth_rewrite 1 [hsR]
            ring
    have hZ0 : 0 ≤ Cstep * Real.exp (c * Bv m) := by linarith
    have hinner : 0 ≤ Rstar ^ (-t0) * Euniv + (∑ j ∈ Finset.range m, F j + F m) := by
      have := hF m le_rfl
      positivity
    calc E m / (s m) ^ t0 + ∑ j ∈ Finset.range m, F j
        ≤ Cstep * Real.exp (c * Bv m) * (Rstar ^ (-t0) * Euniv + F m) +
          Cstep * Real.exp (c * Bv m) * ∑ j ∈ Finset.range m, F j := by
          have : ∑ j ∈ Finset.range m, F j ≤
              Cstep * Real.exp (c * Bv m) * ∑ j ∈ Finset.range m, F j := by nlinarith
          linarith
      _ = 1 * (Cstep * Real.exp (c * Bv m)) *
          (Rstar ^ (-t0) * Euniv + (∑ j ∈ Finset.range m, F j + F m)) := by ring
      _ ≤ 24 ^ t0 * (Cstep * Real.exp (c * Bv m)) *
          (Rstar ^ (-t0) * Euniv + (∑ j ∈ Finset.range m, F j + F m)) := by
          apply mul_le_mul_of_nonneg_right _ hinner
          exact mul_le_mul_of_nonneg_right h24 hZ0
  · rw [if_neg hu]
    have hu' : used m = false := by simpa using hu
    have hFm : F m = 0 := by simp only [hFdef, if_neg hu]
    have hlarge : Rstar / 24 ≤ s m := by
      rcases hT with h | h
      · exact h
      · exact absurd h.1 hu
    have hEm := hlastN hu'
    have hkey : E m / (s m) ^ t0 ≤ 24 ^ t0 * (Rstar ^ (-t0) * Euniv) := by
      rw [div_le_iff₀ hsmt]
      have hpow : Rstar ^ t0 ≤ 24 ^ t0 * (s m) ^ t0 := by
        rw [← Real.mul_rpow (by norm_num) hsm.le]
        exact Real.rpow_le_rpow hRstar.le (by linarith) ht0.le
      have hRt' : Rstar ^ (-t0) * Rstar ^ t0 = 1 := by
        rw [← Real.rpow_add hRstar]; simp
      calc E m ≤ Euniv := hEm
        _ = Rstar ^ (-t0) * Euniv * Rstar ^ t0 := by
            calc Euniv = (Rstar ^ (-t0) * Rstar ^ t0) * Euniv := by rw [hRt', one_mul]
              _ = _ := by ring
        _ ≤ Rstar ^ (-t0) * Euniv * (24 ^ t0 * (s m) ^ t0) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = 24 ^ t0 * (Rstar ^ (-t0) * Euniv) * (s m) ^ t0 := by ring
    simp only [if_neg hu, add_zero, mul_one]
    change _ ≤ 24 ^ t0 * (Rstar ^ (-t0) * Euniv + ∑ j ∈ Finset.range m, F j)
    have h24' : ∑ j ∈ Finset.range m, F j ≤ 24 ^ t0 * ∑ j ∈ Finset.range m, F j := by
      nlinarith
    calc E m / (s m) ^ t0 + ∑ j ∈ Finset.range m, F j
        ≤ 24 ^ t0 * (Rstar ^ (-t0) * Euniv) + 24 ^ t0 * ∑ j ∈ Finset.range m, F j :=
          add_le_add hkey h24'
      _ = 24 ^ t0 * (Rstar ^ (-t0) * Euniv + ∑ j ∈ Finset.range m, F j) := by ring

/-- The constant bookkeeping `s0^t (K^t)^m 24^t ≤ (36 K^d)^t r^t`. -/
theorem aux_rem_resolved_strata_energy_const (d m : ℕ) (hm : m ≤ d) (K r s0 t0 : ℝ)
    (hK : 1 ≤ K) (hr : 0 < r) (hs0pos : 0 < s0) (hs0 : s0 < 3 * (r / 2)) (ht0 : 0 < t0) :
    s0 ^ t0 * (K ^ t0) ^ m * 24 ^ t0 ≤ (36 * K ^ d) ^ t0 * r ^ t0 := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have h1 : s0 ^ t0 ≤ (3 * (r / 2)) ^ t0 := Real.rpow_le_rpow hs0pos.le hs0.le ht0.le
  have h2 : (K ^ t0) ^ m ≤ (K ^ d) ^ t0 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le, mul_comm, Real.rpow_mul hK0.le,
      Real.rpow_natCast]
    exact Real.rpow_le_rpow (by positivity) (pow_le_pow_right₀ hK hm) ht0.le
  calc s0 ^ t0 * (K ^ t0) ^ m * 24 ^ t0 ≤ (3 * (r / 2)) ^ t0 * (K ^ d) ^ t0 * 24 ^ t0 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = (36 * K ^ d) ^ t0 * r ^ t0 := by
        rw [← Real.mul_rpow (by positivity) (by positivity),
          ← Real.mul_rpow (by positivity) (by norm_num),
          ← Real.mul_rpow (by positivity) hr.le]
        congr 1
        ring

/-- The full energy estimate along the chain, as a statement about real numbers. -/
theorem aux_rem_resolved_strata_energy_chain (d m : ℕ) (hm : m ≤ d)
    (s R : ℕ → ℝ) (used : ℕ → Bool) (E G Bv bv : ℕ → ℝ)
    (K r Rstar t0 Cstep c Kf Euniv Estart : ℝ)
    (hK : 1 ≤ K) (hr : 0 < r) (hRstar : 0 < Rstar) (ht0 : 0 < t0) (hCstep : 1 ≤ Cstep)
    (hc : 0 ≤ c) (hEuniv : 0 ≤ Euniv)
    (hs0 : s 0 < 3 * (r / 2))
    (hs : ∀ j : ℕ, j ≤ m → 0 < s j)
    (hR : ∀ j : ℕ, j ≤ m → used j = true → 0 < R j)
    (hB : ∀ j : ℕ, j ≤ m → used j = true → 0 ≤ Bv j)
    (hb : ∀ j : ℕ, j ≤ m → used j = true → 0 < bv j)
    (hE : ∀ j : ℕ, j ≤ m → 0 ≤ E j)
    (hnextU : ∀ j : ℕ, j < m → used j = true → s (j + 1) ≤ K * R j)
    (hnextN : ∀ j : ℕ, j < m → used j = false → s (j + 1) ≤ K * s j)
    (hstepU : ∀ j : ℕ, j ≤ m → used j = true →
        E j ≤ Cstep * Real.exp (c * Bv j) * (s j / R j) ^ t0 *
          (G j + (bv j)⁻¹ * Kf ^ 2 * R j ^ ((d : ℝ) + 2)))
    (hGnext : ∀ j : ℕ, j < m → used j = true → G j ≤ E (j + 1))
    (hGlast : used m = true → G m ≤ Euniv)
    (hstepN : ∀ j : ℕ, j < m → used j = false → E j ≤ E (j + 1))
    (hlastN : used m = false → E m ≤ Euniv)
    (hT : s m ≥ Rstar / 24 ∨ (used m = true ∧ R m = Rstar))
    (hUm : used m = true → s m < Rstar / 24)
    (hstart : Estart ≤ E 0) :
    Estart ≤ (36 * K ^ d) ^ t0 * Cstep ^ (d + 1) *
      Real.exp (c * ∑ j ∈ (Finset.range (m + 1)).filter (fun j => used j = true), Bv j) *
      r ^ t0 *
      (Rstar ^ (-t0) * Euniv + Kf ^ 2 *
        ∑ j ∈ (Finset.range (m + 1)).filter (fun j => used j = true),
          (bv j)⁻¹ * (R j) ^ ((d : ℝ) + 2 - t0)) := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  set Z : ℕ → ℝ := fun j => if used j = true then Cstep * Real.exp (c * Bv j) else 1 with hZdef
  set F : ℕ → ℝ := fun j =>
    if used j = true then (bv j)⁻¹ * Kf ^ 2 * R j ^ ((d : ℝ) + 2 - t0) else 0 with hFdef
  have hcomp := aux_rem_resolved_strata_energy_comp d m s R used E G Bv bv K t0 Cstep c Kf
    hK ht0 hCstep hc hs hR hB hb hE hnextU hnextN hstepU hGnext hstepN
  have hterm := aux_rem_resolved_strata_energy_terminal d m s R used E G Bv bv Rstar t0 Cstep
    c Kf Euniv hRstar ht0 hCstep hc hEuniv hs hR hB hb hstepU hGlast hlastN hT hUm
  have hZ1 : ∀ j, j ≤ m → 1 ≤ Z j := by
    intro j hj
    simp only [hZdef]
    split_ifs with hu
    · have h1 : 1 ≤ Real.exp (c * Bv j) := Real.one_le_exp (mul_nonneg hc (hB j hj hu))
      nlinarith
    · exact le_rfl
  have hF : ∀ j, j ≤ m → 0 ≤ F j := by
    intro j hj
    simp only [hFdef]
    split_ifs with hu
    · have := hb j hj hu; have := hR j hj hu; positivity
    · exact le_rfl
  have hprodZK : (∏ j ∈ Finset.range m, Z j * K ^ t0) =
      (∏ j ∈ Finset.range m, Z j) * (K ^ t0) ^ m := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have hZm : (∏ j ∈ Finset.range m, Z j) * Z m =
      ∏ j ∈ (Finset.range (m + 1)).filter (fun j => used j = true),
        (Cstep * Real.exp (c * Bv j)) := by
    rw [← Finset.prod_range_succ, Finset.prod_filter]
  have hcardJ : ((Finset.range (m + 1)).filter (fun j => used j = true)).card ≤ d + 1 :=
    (Finset.card_filter_le _ _).trans (by simp; omega)
  have hZbound := aux_rem_resolved_strata_prod_allow
    ((Finset.range (m + 1)).filter (fun j => used j = true)) (d + 1) hcardJ Cstep c hCstep Bv
  have hFJ : (∑ j ∈ Finset.range (m + 1), F j) =
      Kf ^ 2 * ∑ j ∈ (Finset.range (m + 1)).filter (fun j => used j = true),
        (bv j)⁻¹ * (R j) ^ ((d : ℝ) + 2 - t0) := by
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    simp only [hFdef]
    split_ifs <;> ring
  have hconst := aux_rem_resolved_strata_energy_const d m hm K r (s 0) t0 hK hr
    (hs 0 (Nat.zero_le _)) hs0 ht0
  have hZprod_nonneg : 0 ≤ ∏ j ∈ Finset.range m, Z j :=
    Finset.prod_nonneg fun j hj => le_trans zero_le_one (hZ1 j (Finset.mem_range.mp hj).le)
  have hW : 0 ≤ Rstar ^ (-t0) * Euniv + ∑ j ∈ Finset.range (m + 1), F j := by
    have : 0 ≤ ∑ j ∈ Finset.range (m + 1), F j :=
      Finset.sum_nonneg fun j hj => hF j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    have : 0 ≤ Rstar ^ (-t0) := (Real.rpow_pos_of_pos hRstar _).le
    positivity
  have hs0t : 0 ≤ (s 0) ^ t0 := Real.rpow_nonneg (hs 0 (Nat.zero_le _)).le _
  have hKt : 0 ≤ (K ^ t0) ^ m := by positivity
  rw [← hFJ]
  calc Estart ≤ E 0 := hstart
    _ ≤ (s 0) ^ t0 * (∏ j ∈ Finset.range m, Z j * K ^ t0) *
        (E m / (s m) ^ t0 + ∑ j ∈ Finset.range m, F j) := hcomp
    _ ≤ (s 0) ^ t0 * (∏ j ∈ Finset.range m, Z j * K ^ t0) *
        (24 ^ t0 * Z m * (Rstar ^ (-t0) * Euniv + ∑ j ∈ Finset.range (m + 1), F j)) := by
        apply mul_le_mul_of_nonneg_left hterm
        rw [hprodZK]; positivity
    _ = ((s 0) ^ t0 * (K ^ t0) ^ m * 24 ^ t0) * ((∏ j ∈ Finset.range m, Z j) * Z m) *
        (Rstar ^ (-t0) * Euniv + ∑ j ∈ Finset.range (m + 1), F j) := by
        rw [hprodZK]; ring
    _ ≤ ((36 * K ^ d) ^ t0 * r ^ t0) *
        (Cstep ^ (d + 1) * Real.exp (c * ∑ j ∈ (Finset.range (m + 1)).filter
          (fun j => used j = true), Bv j)) *
        (Rstar ^ (-t0) * Euniv + ∑ j ∈ Finset.range (m + 1), F j) := by
        apply mul_le_mul_of_nonneg_right _ hW
        rw [hZm]
        apply mul_le_mul hconst hZbound
        · exact Finset.prod_nonneg fun j _ => by
            have := Real.exp_pos (c * Bv j); nlinarith
        · positivity
    _ = _ := by ring



theorem aux_rem_resolved_strata_mem_cube {d : ℕ} {x : SpatialCoordinates d}
    (hx : x ∈ (unitNeumannCube d : Set (SpatialCoordinates d))) :
    ∀ i : Fin d, 0 < x i ∧ x i < 1 := by
  have h : x ∈ Set.pi Set.univ (fun i : Fin d =>
      Set.Ioo ((fun _ => (1 / 2 : ℝ)) i - 1 / 2) ((fun _ => (1 / 2 : ℝ)) i + 1 / 2)) := by
    rw [← centeredCube_eq_pi (fun _ => (1 / 2 : ℝ)) one_pos]
    exact hx
  intro i
  have hi := h i (Set.mem_univ i)
  simp only [Set.mem_Ioo] at hi
  constructor <;> linarith [hi.1, hi.2]

theorem aux_rem_resolved_strata_integrable {d : ℕ} (a : PositiveCoefficient (unitNeumannCube d))
    (u : weakSobolevGraph (unitNeumannCube d)) :
    Integrable (fun y => a.val y *
        ∑ i : Fin d, ((u : SobolevData (unitNeumannCube d)).2 i y) ^ 2)
      (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) := by
  have h : ∀ i : Fin d, Integrable (fun y => a.val y *
      ((u : SobolevData (unitNeumannCube d)).2 i y) ^ 2)
      (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) := by
    intro i
    have := integrable_weighted_inner a.val ((u : SobolevData (unitNeumannCube d)).2 i)
      ((u : SobolevData (unitNeumannCube d)).2 i)
    simpa only [RCLike.inner_apply, conj_trivial, pow_two, mul_comm] using this
  simp_rw [Finset.mul_sum]
  exact integrable_finset_sum _ (fun i _ => h i)

theorem aux_rem_resolved_strata_integrand_nonneg {d : ℕ}
    (a : PositiveCoefficient (unitNeumannCube d)) (u : weakSobolevGraph (unitNeumannCube d)) :
    ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      0 ≤ a.val y * ∑ i : Fin d, ((u : SobolevData (unitNeumannCube d)).2 i y) ^ 2 := by
  filter_upwards [positiveCoefficient_ae_nonneg a] with y hy
  exact mul_nonneg hy (Finset.sum_nonneg fun i _ => sq_nonneg _)

theorem aux_rem_resolved_strata_energy_mono {d : ℕ}
    (a : PositiveCoefficient (unitNeumannCube d)) (u : weakSobolevGraph (unitNeumannCube d))
    {A A' : Set (SpatialCoordinates d)} (h : A ⊆ A') :
    (∫ y in A ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
        a.val y * ∑ i : Fin d, ((u : SobolevData (unitNeumannCube d)).2 i y) ^ 2) ≤
      ∫ y in A' ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
        a.val y * ∑ i : Fin d, ((u : SobolevData (unitNeumannCube d)).2 i y) ^ 2 := by
  have hint := aux_rem_resolved_strata_integrable a u
  have hnn := aux_rem_resolved_strata_integrand_nonneg a u
  apply setIntegral_mono_set
  · exact IntegrableOn.mono_set (t := (unitNeumannCube d : Set (SpatialCoordinates d))) hint Set.inter_subset_right
  · exact ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right hnn
  · exact (Set.inter_subset_inter_left _ h).eventuallyLE

theorem aux_rem_resolved_strata_energy_nonneg {d : ℕ}
    (a : PositiveCoefficient (unitNeumannCube d)) (u : weakSobolevGraph (unitNeumannCube d))
    (A : Set (SpatialCoordinates d)) :
    0 ≤ ∫ y in A ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
        a.val y * ∑ i : Fin d, ((u : SobolevData (unitNeumannCube d)).2 i y) ^ 2 := by
  apply setIntegral_nonneg_of_ae_restrict
  exact ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right
    (aux_rem_resolved_strata_integrand_nonneg a u)

/-- Activating one nearer face: the cube around the old projection sits inside the
cube around the new projection once the radius grows by the face distance. -/
theorem aux_rem_resolved_strata_cube_insert {d : ℕ} (x : SpatialCoordinates d)
    (hx : ∀ i : Fin d, 0 < x i ∧ x i < 1) (I : Finset (Fin d)) (i : Fin d) (ρ ρ' : ℝ)
    (hρ' : ρ + min (x i) (1 - x i) ≤ ρ') :
    {y : SpatialCoordinates d | ∀ k : Fin d,
        |y k - (if k ∈ I then (if x k ≤ 1 / 2 then (0 : ℝ) else 1) else x k)| < ρ} ⊆
      {y : SpatialCoordinates d | ∀ k : Fin d,
        |y k - (if k ∈ insert i I then (if x k ≤ 1 / 2 then (0 : ℝ) else 1) else x k)| < ρ'} := by
  have hdel : 0 ≤ min (x i) (1 - x i) := le_min (hx i).1.le (by linarith [(hx i).2])
  have hρρ : ρ ≤ ρ' := by linarith
  have hface : |x i - (if x i ≤ 1 / 2 then (0 : ℝ) else 1)| ≤ min (x i) (1 - x i) := by
    split_ifs with h
    · rw [sub_zero, abs_of_pos (hx i).1]
      exact le_min le_rfl (by linarith)
    · rw [abs_sub_comm, abs_of_pos (by linarith [(hx i).2])]
      exact le_min (by linarith) le_rfl
  intro y hy k
  have hyk := hy k
  by_cases hkI : k ∈ I
  · have hk' : k ∈ insert i I := Finset.mem_insert_of_mem hkI
    rw [if_pos hkI] at hyk
    rw [if_pos hk']
    linarith
  · by_cases hki : k = i
    · subst hki
      rw [if_neg hkI] at hyk
      rw [if_pos (Finset.mem_insert_self k I)]
      calc |y k - (if x k ≤ 1 / 2 then (0 : ℝ) else 1)|
          ≤ |y k - x k| + |x k - (if x k ≤ 1 / 2 then (0 : ℝ) else 1)| := abs_sub_le _ _ _
        _ < ρ + min (x k) (1 - x k) := by linarith
        _ ≤ ρ' := hρ'
    · have hk' : k ∉ insert i I := by
        rw [Finset.mem_insert]; push_neg; exact ⟨hki, hkI⟩
      rw [if_neg hkI] at hyk
      rw [if_neg hk']
      linarith

theorem aux_rem_resolved_strata_cube_start {d : ℕ} (x : SpatialCoordinates d) (ρ ρ' : ℝ)
    (h : ρ ≤ ρ') :
    {y : SpatialCoordinates d | ∀ k : Fin d, |y k - x k| < ρ} ⊆
      {y : SpatialCoordinates d | ∀ k : Fin d,
        |y k - (if k ∈ (∅ : Finset (Fin d)) then (if x k ≤ 1 / 2 then (0 : ℝ) else 1)
          else x k)| < ρ'} := by
  intro y hy k
  simp only [Finset.notMem_empty, if_false]
  exact lt_of_lt_of_le (hy k) h



/-- The primitive of `t ↦ λ e^{λ t}` on `[0,x]`. -/
theorem aux_rem_resolved_strata_exp_primitive (lam x : ℝ) :
    (∫ t in (0 : ℝ)..x, lam * Real.exp (lam * t)) = Real.exp (lam * x) - 1 := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) x,
      HasDerivAt (fun t => Real.exp (lam * t)) (lam * Real.exp (lam * t)) t := by
    intro t _
    have h := ((hasDerivAt_id t).const_mul lam).exp
    simpa [mul_comm] using h
  have hcont : Continuous fun t : ℝ => lam * Real.exp (lam * t) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable _ _)]
  simp

/-- `∫_{t>0} A λ e^{-(β-λ)t} dt = Aλ/(β-λ)` as a lower integral. -/
theorem aux_rem_resolved_strata_exp_lintegral (A beta lam : ℝ) (hA : 0 ≤ A)
    (hlam : 0 ≤ lam) (hlb : lam < beta) :
    (∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal (A * Real.exp (-beta * t)) * ENNReal.ofReal (lam * Real.exp (lam * t))) =
      ENNReal.ofReal (A * lam / (beta - lam)) := by
  have hk : 0 < beta - lam := sub_pos.mpr hlb
  have heq : ∀ t : ℝ, ENNReal.ofReal (A * Real.exp (-beta * t)) *
      ENNReal.ofReal (lam * Real.exp (lam * t)) =
      ENNReal.ofReal ((A * lam) * Real.exp (-(beta - lam) * t)) := by
    intro t
    rw [← ENNReal.ofReal_mul (mul_nonneg hA (Real.exp_pos _).le)]
    congr 1
    have : Real.exp (-(beta - lam) * t) = Real.exp (-beta * t) * Real.exp (lam * t) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]; ring
  simp_rw [heq]
  have hint : IntegrableOn (fun t : ℝ => (A * lam) * Real.exp (-(beta - lam) * t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hk).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [integral_const_mul]
    have h := integral_exp_mul_Ioi (a := -(beta - lam)) (by linarith) 0
    rw [h]
    simp only [mul_zero, Real.exp_zero]
    field_simp
  · filter_upwards with t
    exact mul_nonneg (mul_nonneg hA hlam) (Real.exp_pos _).le

/-- Sharp real exponential tail to exponential moment, via Mathlib's layer-cake formula. -/
theorem aux_rem_resolved_strata_tail_lintegral {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (hX0 : ∀ ω, 0 ≤ X ω) (A beta lam : ℝ) (hA : 0 ≤ A) (hlam : 0 ≤ lam)
    (hlb : lam < beta)
    (htail : ∀ t : ℝ, 0 ≤ t → P {ω | t < X ω} ≤ ENNReal.ofReal (A * Real.exp (-beta * t))) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω)) ∂P) ≤
      ENNReal.ofReal (1 + A * lam / (beta - lam)) := by
  have hlayer := lintegral_comp_eq_lintegral_meas_lt_mul P
    (f := X) (g := fun t => lam * Real.exp (lam * t))
    (Filter.Eventually.of_forall hX0) hX.aemeasurable
    (fun t _ => (by fun_prop : Continuous fun t : ℝ => lam * Real.exp (lam * t)).intervalIntegrable _ _)
    (Filter.Eventually.of_forall fun t => mul_nonneg hlam (Real.exp_pos _).le)
  simp_rw [aux_rem_resolved_strata_exp_primitive] at hlayer
  have hbound : (∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω) - 1) ∂P) ≤
      ENNReal.ofReal (A * lam / (beta - lam)) := by
    rw [hlayer, ← aux_rem_resolved_strata_exp_lintegral A beta lam hA hlam hlb]
    apply setLIntegral_mono'
    · exact measurableSet_Ioi
    · intro t ht
      exact mul_le_mul_of_nonneg_right (htail t (le_of_lt ht)) bot_le
  have hsplit : ∀ ω, ENNReal.ofReal (Real.exp (lam * X ω)) =
      1 + ENNReal.ofReal (Real.exp (lam * X ω) - 1) := by
    intro ω
    have h1 : 1 ≤ Real.exp (lam * X ω) := Real.one_le_exp (mul_nonneg hlam (hX0 ω))
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by linarith)]
    congr 1; ring
  simp_rw [hsplit]
  rw [lintegral_add_left (f := fun _ => (1 : ℝ≥0∞)) measurable_const]
  simp only [lintegral_const, measure_univ, mul_one]
  rw [ENNReal.ofReal_add zero_le_one
    (div_nonneg (mul_nonneg hA hlam) (sub_pos.mpr hlb).le), ENNReal.ofReal_one]
  exact add_le_add le_rfl hbound

/-- Exponential moment at order `q` from a sharp real exponential tail. -/
theorem aux_rem_resolved_strata_tail_moment {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (hX0 : ∀ ω, 0 ≤ X ω) (A beta c q : ℝ) (hA : 0 ≤ A) (hc : 0 ≤ c) (hq : 0 < q)
    (hlb : q * c < beta)
    (htail : ∀ t : ℝ, 0 ≤ t → P {ω | t < X ω} ≤ ENNReal.ofReal (A * Real.exp (-beta * t))) :
    MemLp (fun ω => Real.exp (c * X ω)) (ENNReal.ofReal q) P ∧
      eLpNorm (fun ω => Real.exp (c * X ω)) (ENNReal.ofReal q) P ≤
        ENNReal.ofReal ((1 + A * (q * c) / (beta - q * c)) ^ (1 / q)) := by
  have hlam : 0 ≤ q * c := mul_nonneg hq.le hc
  have hL := aux_rem_resolved_strata_tail_lintegral P X hX hX0 A beta (q * c) hA hlam hlb htail
  have hM : 0 ≤ 1 + A * (q * c) / (beta - q * c) := by
    have : 0 ≤ A * (q * c) / (beta - q * c) :=
      div_nonneg (mul_nonneg hA hlam) (sub_pos.mpr hlb).le
    linarith
  have hq0 : ENNReal.ofReal q ≠ 0 := by simpa using hq
  have hqtop : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
  have hmeas : AEStronglyMeasurable (fun ω => Real.exp (c * X ω)) P :=
    (by fun_prop : Measurable fun ω => Real.exp (c * X ω)).aestronglyMeasurable
  have hnorm : eLpNorm (fun ω => Real.exp (c * X ω)) (ENNReal.ofReal q) P =
      (∫⁻ ω, ENNReal.ofReal (Real.exp ((q * c) * X ω)) ∂P) ^ (1 / q) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqtop hmeas, ENNReal.toReal_ofReal hq.le]
    congr 1
    apply lintegral_congr
    intro ω
    rw [Real.enorm_eq_ofReal (Real.exp_pos _).le,
      ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hq.le, ← Real.exp_mul]
    congr 2; ring
  have hbound : eLpNorm (fun ω => Real.exp (c * X ω)) (ENNReal.ofReal q) P ≤
      ENNReal.ofReal ((1 + A * (q * c) / (beta - q * c)) ^ (1 / q)) := by
    rw [hnorm, ← ENNReal.ofReal_rpow_of_nonneg hM (by positivity)]
    exact ENNReal.rpow_le_rpow hL (by positivity)
  refine ⟨?_, hbound⟩
  change eLpNorm (fun ω => Real.exp (c * X ω)) (ENNReal.ofReal q) P < ⊤
  exact lt_of_le_of_lt hbound ENNReal.ofReal_lt_top



/-- Finite-product Hölder at a fixed larger order: at most `N` factors, each bounded by `K`
in `L^{N p}`, give a product bounded by `K ^ N` in `L^p`.  No independence is used. -/
theorem aux_rem_resolved_strata_holder {Ω ι : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (S : Finset ι) (N : ℕ) (hSN : S.card ≤ N) (p : ℝ) (hp : 1 ≤ p)
    (f : ι → Ω → ℝ) (K : ℝ) (hK : 1 ≤ K)
    (hmem : ∀ i ∈ S, MemLp (f i) (ENNReal.ofReal ((N : ℝ) * p)) P)
    (hnorm : ∀ i ∈ S, eLpNorm (f i) (ENNReal.ofReal ((N : ℝ) * p)) P ≤ ENNReal.ofReal K) :
    MemLp (fun ω => ∏ i ∈ S, f i ω) (ENNReal.ofReal p) P ∧
      eLpNorm (fun ω => ∏ i ∈ S, f i ω) (ENNReal.ofReal p) P ≤ ENNReal.ofReal (K ^ N) := by
  classical
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpE0 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hpEtop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hKN : 1 ≤ K ^ N := one_le_pow₀ hK
  have hmeas : AEStronglyMeasurable (fun ω => ∏ i ∈ S, f i ω) P :=
    Finset.aestronglyMeasurable_fun_prod S (fun i hi => (hmem i hi).aestronglyMeasurable)
  have hbound : eLpNorm (fun ω => ∏ i ∈ S, f i ω) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (K ^ N) := by
    rcases Nat.eq_zero_or_pos S.card with hcard | hcard
    · have hS : S = ∅ := Finset.card_eq_zero.mp hcard
      subst hS
      simp only [Finset.prod_empty]
      rw [eLpNorm_const _ hpE0 (IsProbabilityMeasure.ne_zero P)]
      simp only [enorm_one, measure_univ, ENNReal.one_rpow, mul_one]
      exact ENNReal.one_le_ofReal.mpr hKN
    · set n : ℕ := S.card with hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hcard
      set r : ℝ := (n : ℝ) * p with hr
      have hr0 : 0 < r := mul_pos hnpos hp0
      have hrE0 : ENNReal.ofReal r ≠ 0 := by simpa using hr0
      -- individual bounds at the order `n p ≤ N p`
      have hL : ∀ i ∈ S, (∫⁻ ω, ‖f i ω‖ₑ ^ r ∂P) ≤ (ENNReal.ofReal K) ^ r := by
        intro i hi
        have hle : eLpNorm (f i) (ENNReal.ofReal r) P ≤ ENNReal.ofReal K := by
          refine le_trans (eLpNorm_le_eLpNorm_of_exponent_le ?_) (hnorm i hi)
          apply ENNReal.ofReal_le_ofReal
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hSN) hp0.le
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hrE0 ENNReal.ofReal_ne_top
            (hmem i hi).aestronglyMeasurable,
          ENNReal.toReal_ofReal hr0.le, one_div, ENNReal.rpow_inv_le_iff hr0] at hle
        exact hle
      have hsum : ∑ _i ∈ S, (n : ℝ)⁻¹ = 1 := by
        rw [Finset.sum_const, ← hn, nsmul_eq_mul]
        exact mul_inv_cancel₀ hnpos.ne'
      have hholder := ENNReal.lintegral_prod_norm_pow_le (μ := P) S
        (f := fun i ω => ‖f i ω‖ₑ ^ r)
        (fun i hi => (hmem i hi).aestronglyMeasurable.enorm.pow_const r) hsum
        (fun i _ => inv_nonneg.mpr hnpos.le)
      have hexp : r * (n : ℝ)⁻¹ = p := by
        rw [hr]; field_simp
      have hlhs : ∀ ω, (∏ i ∈ S, (‖f i ω‖ₑ ^ r) ^ (n : ℝ)⁻¹) =
          ‖∏ i ∈ S, f i ω‖ₑ ^ p := by
        intro ω
        simp_rw [← ENNReal.rpow_mul, hexp]
        rw [ENNReal.prod_rpow_of_nonneg hp0.le]
        congr 1
        simp only [enorm_eq_nnnorm, nnnorm_prod, ENNReal.coe_finset_prod]
      simp_rw [hlhs] at hholder
      have hrhs : (∏ i ∈ S, (∫⁻ ω, ‖f i ω‖ₑ ^ r ∂P) ^ (n : ℝ)⁻¹) ≤
          ((ENNReal.ofReal K) ^ (n : ℝ)) ^ p := by
        calc (∏ i ∈ S, (∫⁻ ω, ‖f i ω‖ₑ ^ r ∂P) ^ (n : ℝ)⁻¹)
            ≤ ∏ _i ∈ S, ((ENNReal.ofReal K) ^ r) ^ (n : ℝ)⁻¹ := by
              apply Finset.prod_le_prod'
              intro i hi
              exact ENNReal.rpow_le_rpow (hL i hi) (inv_nonneg.mpr hnpos.le)
          _ = ((ENNReal.ofReal K) ^ (n : ℝ)) ^ p := by
              rw [Finset.prod_const, ← hn, ← ENNReal.rpow_mul, hexp,
                ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_comm]
      have hint : (∫⁻ ω, ‖∏ i ∈ S, f i ω‖ₑ ^ p ∂P) ≤ ((ENNReal.ofReal K) ^ (n : ℝ)) ^ p :=
        hholder.trans hrhs
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpE0 hpEtop hmeas, ENNReal.toReal_ofReal hp0.le, one_div,
        ENNReal.rpow_inv_le_iff hp0]
      refine hint.trans (ENNReal.rpow_le_rpow ?_ hp0.le)
      rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_pow (le_trans zero_le_one hK)]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ hK hSN)
  exact ⟨lt_of_le_of_lt hbound ENNReal.ofReal_lt_top, hbound⟩


/-- Along the chain, each transition activates one face with the prescribed enlargement. -/
theorem aux_rem_resolved_strata_transitions (d : ℕ) (Lstar Rstar : ℝ) (half : Set ℝ)
    (delta : Fin d → ℝ) (nextFaceDistance cap : Finset (Fin d) → ℝ)
    (near : Finset (Fin d) → ℝ → Prop)
    (m : ℕ) (I : ℕ → Finset (Fin d)) (s R : ℕ → ℝ) (used : ℕ → Bool)
    (hU : ∀ j : ℕ, j ≤ m →
      (used j = true ↔ (s j < Rstar / 24 ∧ ¬ near (I j) (s j))) ∧
      (used j = true →
        IsGreatest {v : ℝ | v ∈ half ∧ v ≤ cap (I j)} (R j) ∧
          8 * s j < R j ∧ R j ≤ Rstar ∧
          (∀ i : Fin d, i ∉ I j → 4 * Lstar * R j ≤ delta i)) ∧
      (used j = false → R j = 0))
    (hS : ∀ j : ℕ, j < m → s j < Rstar / 24 ∧
      ((near (I j) (s j) ∧
          ∃ i : Fin d, i ∉ I j ∧ delta i ≤ 100 * Lstar * s j ∧
            I (j + 1) = insert i (I j) ∧
            IsLeast {v : ℝ | v ∈ half ∧ s j + delta i ≤ v} (s (j + 1))) ∨
        (¬ near (I j) (s j) ∧ used j = true ∧ R j < Rstar ∧
          ∃ i : Fin d, i ∉ I j ∧ delta i = nextFaceDistance (I j) ∧
            I (j + 1) = insert i (I j) ∧
            IsLeast {v : ℝ | v ∈ half ∧ Lstar * R j + delta i ≤ v} (s (j + 1))))) :
    (∀ j : ℕ, j < m → used j = true →
      ∃ i : Fin d, I (j + 1) = insert i (I j) ∧ Lstar * R j + delta i ≤ s (j + 1)) ∧
    (∀ j : ℕ, j < m → used j = false →
      ∃ i : Fin d, I (j + 1) = insert i (I j) ∧ s j + delta i ≤ s (j + 1)) := by
  constructor
  · intro j hj hu
    rcases hS j hj with ⟨_, ⟨hn, _⟩ | ⟨_, _, _, i, _, _, hins, hleast⟩⟩
    · exact absurd hn ((hU j hj.le).1.mp hu).2
    · exact ⟨i, hins, hleast.1.2⟩
  · intro j hj hu
    rcases hS j hj with ⟨_, ⟨_, i, _, _, hins, hleast⟩ | ⟨_, hu', _⟩⟩
    · exact ⟨i, hins, hleast.1.2⟩
    · rw [hu] at hu'; exact absurd hu' (by simp)

/-- The original-domain reflection clause, from `lem_even` on the unit cube. -/
theorem aux_rem_resolved_strata_reflection (d : ℕ) (I : Finset (Fin d))
    (a : PositiveCoefficient (unitNeumannCube d))
    (u : weakSobolevGraph (unitNeumannCube d))
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hFmeas : AEMeasurable F
      (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))))
    (hFbound : ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      |F y| ≤ Kf)
    (hFmean : (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), F y) = 0)
    (hweak : ∀ ψ : weakSobolevGraph (unitNeumannCube d),
      sobolevCoefficientForm a
          (u : SobolevData (unitNeumannCube d))
          (ψ : SobolevData (unitNeumannCube d)) =
        ∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)),
          F y * (ψ : SobolevData (unitNeumannCube d)).1 y)
    (P : Finset (Fin d)) :
    ∃ (af : PositiveCoefficient
          (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P))
      (vf : weakSobolevGraph
          (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)),
      ((af.val : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict
            (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P :
              Set (SpatialCoordinates d))]
        fun y => a.val
          (coordinateFold
            (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P) I P y)) ∧
      ((((vf : SobolevData
              (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)).1 :
            SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict
            (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P :
              Set (SpatialCoordinates d))]
        fun y => (u : SobolevData (unitNeumannCube d)).1
          (coordinateFold
            (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P) I P y))) ∧
      (∀ (Bs : Set (SpatialCoordinates d)) (hBs : MeasurableSet Bs),
        (∀ Js : Finset (Fin d), Js ⊆ I →
          coordinateReflection
            (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P) Js ⁻¹' Bs = Bs) →
        localGradientEnergy af hBs
            (sobolevGradient (vf : SobolevData
              (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P))) =
          2 ^ I.card *
            localGradientEnergy a
              (hBs.inter (unitNeumannCube d).isOpen.measurableSet)
              (sobolevGradient (u : SobolevData (unitNeumannCube d)))) := by
  obtain ⟨af, vf, h1, h2, _, h4⟩ := lem_even d (fun _ => (1 / 2 : ℝ)) 1 one_pos I P
    a F Kf hKf hFmeas hFbound hFmean u hweak
  exact ⟨af, vf, h1, h2, h4⟩

/-- The probabilistic clause at the selected stages: sharp tails give the individual
moments at the larger order, and Hölder bounds the product; no independence is used. -/
theorem aux_rem_resolved_strata_prob (d : ℕ) (t0 c : ℝ) (hc : 0 ≤ c) (J : Finset ℕ)
    (hcardJ : J.card ≤ d + 1) (I : ℕ → Finset (Fin d)) (R : ℕ → ℝ)
    (hRJ : ∀ j ∈ J, 0 < R j) :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (p A beta : ℝ),
      1 ≤ p → 1 ≤ A →
      ((d : ℝ) + 1) * p * max c (t0 * Real.log 3) < beta →
      ∀ (Brand : Finset (Fin d) → ℝ → Ω → ℝ),
        (∀ (I : Finset (Fin d)) (R : ℝ), 0 < R → Measurable (Brand I R)) →
        (∀ (I : Finset (Fin d)) (R : ℝ), 0 < R →
          ∀ ω, 0 ≤ Brand I R ω) →
        (∀ (I : Finset (Fin d)) (R : ℝ), 0 < R →
          ∀ (t : ℝ), 0 ≤ t →
            P {ω | t < Brand I R ω} ≤
              ENNReal.ofReal (A * Real.exp (-beta * t))) →
        let q : ℝ := ((d : ℝ) + 1) * p;
        let Ktail : ℝ := (1 + A * (q * c) / (beta - q * c)) ^ (1 / q);
        (∀ j ∈ J,
          MemLp (fun ω => Real.exp (c * Brand (I j) (R j) ω))
            (ENNReal.ofReal q) P ∧
          eLpNorm (fun ω => Real.exp (c * Brand (I j) (R j) ω))
            (ENNReal.ofReal q) P ≤ ENNReal.ofReal Ktail) ∧
        MemLp (fun ω => Real.exp (c * ∑ j ∈ J, Brand (I j) (R j) ω))
          (ENNReal.ofReal p) P ∧
        eLpNorm (fun ω => Real.exp (c * ∑ j ∈ J, Brand (I j) (R j) ω))
          (ENNReal.ofReal p) P ≤ ENNReal.ofReal (Ktail ^ (d + 1)) := by
  intro Ω _ P _ p A beta hp hA hbeta Brand hmeasB hnnB htail q Ktail
  have hp0 : 0 < p := by linarith
  have hq : 0 < q := by
    show 0 < ((d : ℝ) + 1) * p
    positivity
  have hqc : q * c < beta := by
    have h1 : q * c ≤ q * max c (t0 * Real.log 3) :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hq.le
    exact lt_of_le_of_lt h1 hbeta
  have hmom : ∀ j ∈ J,
      MemLp (fun ω => Real.exp (c * Brand (I j) (R j) ω)) (ENNReal.ofReal q) P ∧
      eLpNorm (fun ω => Real.exp (c * Brand (I j) (R j) ω)) (ENNReal.ofReal q) P ≤
        ENNReal.ofReal Ktail := by
    intro j hj
    have hRj := hRJ j hj
    exact aux_rem_resolved_strata_tail_moment P (Brand (I j) (R j)) (hmeasB _ _ hRj)
      (hnnB _ _ hRj) A beta c q (by linarith) hc hq hqc (htail _ _ hRj)
  have hKt : 1 ≤ Ktail := by
    show 1 ≤ (1 + A * (q * c) / (beta - q * c)) ^ (1 / q)
    apply Real.one_le_rpow _ (by positivity)
    have : 0 ≤ A * (q * c) / (beta - q * c) :=
      div_nonneg (mul_nonneg (by linarith) (mul_nonneg hq.le hc)) (by linarith)
    linarith
  have hN : (((d + 1 : ℕ) : ℝ)) * p = q := by
    show (((d + 1 : ℕ) : ℝ)) * p = ((d : ℝ) + 1) * p
    push_cast; ring
  have hH := aux_rem_resolved_strata_holder P J (d + 1) hcardJ p hp
    (fun j ω => Real.exp (c * Brand (I j) (R j) ω)) Ktail hKt
    (fun j hj => by rw [hN]; exact (hmom j hj).1)
    (fun j hj => by rw [hN]; exact (hmom j hj).2)
  have hfun : (fun ω => Real.exp (c * ∑ j ∈ J, Brand (I j) (R j) ω)) =
      fun ω => ∏ j ∈ J, Real.exp (c * Brand (I j) (R j) ω) := by
    funext ω; rw [Finset.mul_sum, Real.exp_sum]
  refine ⟨hmom, ?_⟩
  rw [hfun]
  exact hH

/-- The standalone generic product implication (finite-product Hölder). -/
theorem aux_rem_resolved_strata_generic (d : ℕ) :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (p : ℝ), 1 ≤ p →
      ∀ (c : ℝ), 0 ≤ c →
      ∀ (m : ℕ), m ≤ d + 1 →
      ∀ (B : Fin m → Ω → ℝ) (K : ℝ), 1 ≤ K →
        (∀ i : Fin m,
          MemLp (fun ω => Real.exp (c * B i ω))
            (ENNReal.ofReal (((d : ℝ) + 1) * p)) P) →
        (∀ i : Fin m,
          eLpNorm (fun ω => Real.exp (c * B i ω))
            (ENNReal.ofReal (((d : ℝ) + 1) * p)) P ≤ ENNReal.ofReal K) →
        MemLp (fun ω => Real.exp (c * ∑ i : Fin m, B i ω))
            (ENNReal.ofReal p) P ∧
          eLpNorm (fun ω => Real.exp (c * ∑ i : Fin m, B i ω))
            (ENNReal.ofReal p) P ≤ ENNReal.ofReal (K ^ (d + 1)) := by
  intro Ω _ P _ p hp c _ m hm B K hK hmem hnorm
  have hfun : (fun ω => Real.exp (c * ∑ i : Fin m, B i ω)) =
      fun ω => ∏ i : Fin m, Real.exp (c * B i ω) := by
    funext ω; rw [Finset.mul_sum, Real.exp_sum]
  have hN : (((d + 1 : ℕ) : ℝ)) * p = ((d : ℝ) + 1) * p := by push_cast; ring
  have hH := aux_rem_resolved_strata_holder P (Finset.univ : Finset (Fin m)) (d + 1)
    (by simpa using hm) p hp (fun i ω => Real.exp (c * B i ω)) K hK
    (fun i _ => by rw [hN]; exact hmem i) (fun i _ => by rw [hN]; exact hnorm i)
  rw [hfun]
  exact hH



theorem rem_resolved_strata (d : ℕ) (hd : 2 ≤ d) (Lstar t0 : ℝ)
    (hLstar : 10 ≤ Lstar) (ht0 : 0 < t0) (ht0d : t0 < (d : ℝ)) :
    ∃ Cgeom : ℝ, 0 < Cgeom ∧
      (∀ (Cstep c : ℝ), 1 ≤ Cstep → 0 ≤ c →
        ∀ (Rstar : ℝ), 0 < Rstar → Rstar < 1 / (100 * Lstar) →
          (∃ k : ℤ, Rstar = (3 : ℝ) ^ k / 2) →
        ∀ (eps : ℝ), 0 < eps → eps ≤ 1 →
        ∀ (x : SpatialCoordinates d),
          x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
        ∀ (r : ℝ), eps ≤ r → r ≤ 1 →
        let half : Set ℝ := Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2);
        let delta : Fin d → ℝ := fun i => min (x i) (1 - x i);
        let face : Fin d → ℝ := fun i => if x i ≤ 1 / 2 then 0 else 1;
        let center : Finset (Fin d) → SpatialCoordinates d :=
          fun I i => if i ∈ I then face i else x i;
        let cube : Finset (Fin d) → ℝ → Set (SpatialCoordinates d) :=
          fun I s => {y : SpatialCoordinates d | ∀ i : Fin d, |y i - center I i| < s};
        let nextFaceDistance : Finset (Fin d) → ℝ :=
          fun I => sInf {v : ℝ | ∃ i : Fin d, i ∉ I ∧ v = delta i};
        let cap : Finset (Fin d) → ℝ :=
          fun I => if I = Finset.univ then Rstar
            else min Rstar (nextFaceDistance I / (4 * Lstar));
        let near : Finset (Fin d) → ℝ → Prop :=
          fun I s => ∃ i : Fin d, i ∉ I ∧ delta i ≤ 100 * Lstar * s;
        ∃ (m : ℕ) (I : ℕ → Finset (Fin d)) (s R : ℕ → ℝ) (used : ℕ → Bool),
          let J : Finset ℕ := (Finset.range (m + 1)).filter (fun j => used j = true);
          (m ≤ d ∧ I 0 = ∅ ∧ IsLeast {v : ℝ | v ∈ half ∧ r / 2 ≤ v} (s 0)) ∧
          (∀ j : ℕ, j ≤ m → s j ∈ half ∧ 0 < s j ∧ eps / 2 ≤ s j) ∧
          (∀ j : ℕ, m < j → I j = ∅ ∧ s j = 0 ∧ R j = 0 ∧ used j = false) ∧
          (∀ j : ℕ, j ≤ m →
            (used j = true ↔ (s j < Rstar / 24 ∧ ¬ near (I j) (s j))) ∧
            (used j = true →
              IsGreatest {v : ℝ | v ∈ half ∧ v ≤ cap (I j)} (R j) ∧
                8 * s j < R j ∧ R j ≤ Rstar ∧
                (∀ i : Fin d, i ∉ I j → 4 * Lstar * R j ≤ delta i)) ∧
            (used j = false → R j = 0)) ∧
          (∀ j : ℕ, j < m → s j < Rstar / 24 ∧
            ((near (I j) (s j) ∧
                ∃ i : Fin d, i ∉ I j ∧ delta i ≤ 100 * Lstar * s j ∧
                  I (j + 1) = insert i (I j) ∧
                  IsLeast {v : ℝ | v ∈ half ∧ s j + delta i ≤ v} (s (j + 1))) ∨
              (¬ near (I j) (s j) ∧ used j = true ∧ R j < Rstar ∧
                ∃ i : Fin d, i ∉ I j ∧ delta i = nextFaceDistance (I j) ∧
                  I (j + 1) = insert i (I j) ∧
                  IsLeast {v : ℝ | v ∈ half ∧ Lstar * R j + delta i ≤ v} (s (j + 1))))) ∧
          (s m ≥ Rstar / 24 ∨ (used m = true ∧ R m = Rstar)) ∧
          (J.card ≤ d + 1) ∧
          (∏ j ∈ J, (s j / R j) ^ t0) ≤ Cgeom * (r / Rstar) ^ t0 ∧
          (∀ (a : PositiveCoefficient (unitNeumannCube d))
              (u : weakSobolevGraph (unitNeumannCube d))
              (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
            AEMeasurable F
              (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
            (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
              |F y| ≤ Kf) →
            (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), F y) = 0 →
            (∀ ψ : weakSobolevGraph (unitNeumannCube d),
              sobolevCoefficientForm a
                  (u : SobolevData (unitNeumannCube d))
                  (ψ : SobolevData (unitNeumannCube d)) =
                ∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)),
                  F y * (ψ : SobolevData (unitNeumannCube d)).1 y) →
            let energy : Set (SpatialCoordinates d) → ℝ := fun A =>
              ∫ y in A ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
                a.val y * ∑ i : Fin d, ((u : SobolevData (unitNeumannCube d)).2 i y) ^ 2;
            let e : Finset (Fin d) → ℝ → ℝ := fun I s => energy (cube I s);
            ∀ (B b : Finset (Fin d) → ℝ → ℝ),
              (∀ (I : Finset (Fin d)) (R : ℝ), 0 < R → 0 ≤ B I R) →
              (∀ (I : Finset (Fin d)) (R : ℝ), 0 < R → 0 < b I R) →
              (∀ (I : Finset (Fin d)) (s R : ℝ),
                s ∈ half → R ∈ half → 0 < s → eps / 2 ≤ s → 8 * s < R → R ≤ Rstar →
                (∀ i : Fin d, i ∉ I → 4 * Lstar * R ≤ delta i) →
                e I s ≤ Cstep * Real.exp (c * B I R) * (s / R) ^ t0 *
                  (e I (Lstar * R) + (b I R)⁻¹ * Kf ^ 2 * R ^ ((d : ℝ) + 2))) →
              (∏ j ∈ J, (Cstep * Real.exp (c * B (I j) (R j)))) ≤
                Cstep ^ (d + 1) * Real.exp (c * ∑ j ∈ J, B (I j) (R j)) ∧
              (energy {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} ≤
                Cgeom * Cstep ^ (d + 1) * Real.exp (c * ∑ j ∈ J, B (I j) (R j)) * r ^ t0 *
                  (Rstar ^ (-t0) * energy Set.univ +
                    Kf ^ 2 * ∑ j ∈ J, (b (I j) (R j))⁻¹ *
                      (R j) ^ ((d : ℝ) + 2 - t0))) ∧
              (∀ (j : ℕ), j ≤ m → ∀ (P : Finset (Fin d)),
                ∃ (af : PositiveCoefficient
                      (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos (I j) P))
                  (vf : weakSobolevGraph
                      (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos (I j) P)),
                  ((af.val : SpatialCoordinates d → ℝ)
                      =ᵐ[volume.restrict
                        (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos (I j) P :
                          Set (SpatialCoordinates d))]
                    fun y => a.val
                      (coordinateFold
                        (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 (I j) P) (I j) P y)) ∧
                  ((((vf : SobolevData
                          (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos (I j) P)).1 :
                        SpatialCoordinates d → ℝ)
                      =ᵐ[volume.restrict
                        (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos (I j) P :
                          Set (SpatialCoordinates d))]
                    fun y => (u : SobolevData (unitNeumannCube d)).1
                      (coordinateFold
                        (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 (I j) P) (I j) P y))) ∧
                  (∀ (Bs : Set (SpatialCoordinates d)) (hBs : MeasurableSet Bs),
                    (∀ Js : Finset (Fin d), Js ⊆ I j →
                      coordinateReflection
                        (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 (I j) P) Js ⁻¹' Bs = Bs) →
                    localGradientEnergy af hBs
                        (sobolevGradient (vf : SobolevData
                          (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos (I j) P))) =
                      2 ^ (I j).card *
                        localGradientEnergy a
                          (hBs.inter (unitNeumannCube d).isOpen.measurableSet)
                          (sobolevGradient (u : SobolevData (unitNeumannCube d)))))) ∧
          (∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
              (p A beta : ℝ),
            1 ≤ p → 1 ≤ A →
            ((d : ℝ) + 1) * p * max c (t0 * Real.log 3) < beta →
            ∀ (Brand : Finset (Fin d) → ℝ → Ω → ℝ),
              (∀ (I : Finset (Fin d)) (R : ℝ), 0 < R → Measurable (Brand I R)) →
              (∀ (I : Finset (Fin d)) (R : ℝ), 0 < R →
                ∀ ω, 0 ≤ Brand I R ω) →
              (∀ (I : Finset (Fin d)) (R : ℝ), 0 < R →
                ∀ (t : ℝ), 0 ≤ t →
                  P {ω | t < Brand I R ω} ≤
                    ENNReal.ofReal (A * Real.exp (-beta * t))) →
              let q : ℝ := ((d : ℝ) + 1) * p;
              let Ktail : ℝ := (1 + A * (q * c) / (beta - q * c)) ^ (1 / q);
              (∀ j ∈ J,
                MemLp (fun ω => Real.exp (c * Brand (I j) (R j) ω))
                  (ENNReal.ofReal q) P ∧
                eLpNorm (fun ω => Real.exp (c * Brand (I j) (R j) ω))
                  (ENNReal.ofReal q) P ≤ ENNReal.ofReal Ktail) ∧
              MemLp (fun ω => Real.exp (c * ∑ j ∈ J, Brand (I j) (R j) ω))
                (ENNReal.ofReal p) P ∧
              eLpNorm (fun ω => Real.exp (c * ∑ j ∈ J, Brand (I j) (R j) ω))
                (ENNReal.ofReal p) P ≤ ENNReal.ofReal (Ktail ^ (d + 1)))
      ) ∧
      (∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (p : ℝ), 1 ≤ p →
        ∀ (c : ℝ), 0 ≤ c →
        ∀ (m : ℕ), m ≤ d + 1 →
        ∀ (B : Fin m → Ω → ℝ) (K : ℝ), 1 ≤ K →
          (∀ i : Fin m,
            MemLp (fun ω => Real.exp (c * B i ω))
              (ENNReal.ofReal (((d : ℝ) + 1) * p)) P) →
          (∀ i : Fin m,
            eLpNorm (fun ω => Real.exp (c * B i ω))
              (ENNReal.ofReal (((d : ℝ) + 1) * p)) P ≤ ENNReal.ofReal K) →
          MemLp (fun ω => Real.exp (c * ∑ i : Fin m, B i ω))
              (ENNReal.ofReal p) P ∧
            eLpNorm (fun ω => Real.exp (c * ∑ i : Fin m, B i ω))
              (ENNReal.ofReal p) P ≤ ENNReal.ofReal (K ^ (d + 1))) := by
  have hK1 : (1 : ℝ) ≤ 3 * (1 + 100 * Lstar) := by linarith
  refine ⟨(36 * (3 * (1 + 100 * Lstar)) ^ d) ^ t0,
    Real.rpow_pos_of_pos (by positivity) t0, ?_, ?_⟩
  · intro Cstep c hCstep hc Rstar hRstar hRsmall hRhalf eps heps heps1 x hx r hr hr1 half delta face
      center cube nextFaceDistance cap near
    have hxI : ∀ i, 0 < x i ∧ x i < 1 := aux_rem_resolved_strata_mem_cube hx
    have hdelta : ∀ i, 0 < delta i := fun i => lt_min (hxI i).1 (sub_pos.mpr (hxI i).2)
    have hrpos : 0 < r := lt_of_lt_of_le heps hr
    have hr2 : 0 < r / 2 := half_pos hrpos
    have hex0 := aux_rem_resolved_strata_least_exists hr2
    rcases hex0 with ⟨s0, hs0⟩
    have hs0lt : s0 < 3 * (r / 2) := aux_rem_resolved_strata_least_lt hr2 hs0
    have hs0eps : eps / 2 ≤ s0 :=
      le_trans (div_le_div_of_nonneg_right hr (by norm_num)) hs0.1.2
    have hcard0 : (∅ : Finset (Fin d)).card + d = d := by rw [Finset.card_empty, zero_add]
    have hch := aux_rem_resolved_strata_chain d Lstar Rstar eps hLstar hRhalf half rfl delta
      hdelta nextFaceDistance rfl cap rfl near rfl d ∅ s0 hcard0 hs0.1.1 hs0eps
    rcases hch with ⟨m, I, s, R, used, hm, hI0, hs0', hQ, hZ, hU, hS, hT⟩
    have hmd : m ≤ d := hm
    have hs : ∀ j : ℕ, j ≤ m → 0 < s j := fun j hj => (hQ j hj).2.1
    have hR : ∀ j : ℕ, j ≤ m → used j = true → 0 < R j := fun j hj hu =>
      aux_rem_resolved_strata_half_pos ((hU j hj).2.1 hu).1.1.1
    have hnext : ∀ j : ℕ, j < m →
        (used j = true → s (j + 1) ≤ 3 * (1 + 100 * Lstar) * R j) ∧
          (used j = false → s (j + 1) ≤ 3 * (1 + 100 * Lstar) * s j) :=
      fun j hj => aux_rem_resolved_strata_next d Lstar Rstar hLstar hRhalf half rfl delta hdelta
        nextFaceDistance cap rfl near (I j) (I (j + 1)) (s j) (R j) (s (j + 1)) (used j)
        (hs j hj.le) (hU j hj.le) (hS j hj)
    have hUm : used m = true → s m < Rstar / 24 := fun hu => ((hU m le_rfl).1.mp hu).1
    have hs00 : s 0 < 3 * (r / 2) := by rw [hs0']; exact hs0lt
    have htrans := aux_rem_resolved_strata_transitions d Lstar Rstar half delta nextFaceDistance
      cap near m I s R used hU hS
    refine ⟨m, I, s, R, used, ?_⟩
    intro J
    have hcardJ : J.card ≤ d + 1 := (Finset.card_filter_le _ _).trans (by simp; omega)
    refine ⟨⟨hmd, hI0, hs0' ▸ hs0⟩, hQ, hZ, hU, hS, hT, hcardJ, ?_, ?_, ?_⟩
    · exact aux_rem_resolved_strata_geom d m hmd s R used (3 * (1 + 100 * Lstar)) r Rstar t0 hK1 hrpos hRstar ht0
        hs00 hs hR (fun j hj => (hnext j hj).1) (fun j hj => (hnext j hj).2) hT hUm
    · intro a u F Kf hKf hFmeas hFbound hFmean hweak energy e B b hBnn hbpos hstep
      refine ⟨aux_rem_resolved_strata_prod_allow J (d + 1) hcardJ Cstep c hCstep
        (fun j => B (I j) (R j)), ?_, ?_⟩
      · have hmono : ∀ {A A' : Set (SpatialCoordinates d)}, A ⊆ A' → energy A ≤ energy A' :=
          fun h => aux_rem_resolved_strata_energy_mono a u h
        have hnn : ∀ A, 0 ≤ energy A := fun A => aux_rem_resolved_strata_energy_nonneg a u A
        exact aux_rem_resolved_strata_energy_chain d m hmd s R used
          (fun j => e (I j) (s j)) (fun j => e (I j) (Lstar * R j))
          (fun j => B (I j) (R j)) (fun j => b (I j) (R j))
          (3 * (1 + 100 * Lstar)) r Rstar t0 Cstep c Kf (energy Set.univ)
          (energy {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2})
          hK1 hrpos hRstar ht0 hCstep hc (hnn _) hs00 hs hR
          (fun j hj hu => hBnn _ _ (hR j hj hu))
          (fun j hj hu => hbpos _ _ (hR j hj hu))
          (fun j _ => hnn _)
          (fun j hj => (hnext j hj).1) (fun j hj => (hnext j hj).2)
          (fun j hj hu => by
            obtain ⟨hgr, h8, hRle, hclear⟩ := (hU j hj).2.1 hu
            exact hstep (I j) (s j) (R j) (hQ j hj).1 hgr.1.1 (hQ j hj).2.1 (hQ j hj).2.2
              h8 hRle hclear)
          (fun j hj hu => by
            obtain ⟨i, hins, hle⟩ := htrans.1 j hj hu
            show energy (cube (I j) (Lstar * R j)) ≤ energy (cube (I (j + 1)) (s (j + 1)))
            rw [hins]
            exact hmono (aux_rem_resolved_strata_cube_insert x hxI (I j) i _ _ hle))
          (fun _ => hmono (Set.subset_univ _))
          (fun j hj hu => by
            obtain ⟨i, hins, hle⟩ := htrans.2 j hj hu
            show energy (cube (I j) (s j)) ≤ energy (cube (I (j + 1)) (s (j + 1)))
            rw [hins]
            exact hmono (aux_rem_resolved_strata_cube_insert x hxI (I j) i _ _ hle))
          (fun _ => hmono (Set.subset_univ _))
          hT hUm
          (by
            show energy _ ≤ energy (cube (I 0) (s 0))
            rw [hI0, hs0']
            exact hmono (aux_rem_resolved_strata_cube_start x _ _ hs0.1.2))
      · exact fun j _ P => aux_rem_resolved_strata_reflection d (I j) a u F Kf hKf hFmeas
          hFbound hFmean hweak P
    · exact aux_rem_resolved_strata_prob d t0 c hc J hcardJ I R (fun j hj =>
        hR j (Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hj).1))
          (Finset.mem_filter.mp hj).2)
  · exact aux_rem_resolved_strata_generic d

end Paper
