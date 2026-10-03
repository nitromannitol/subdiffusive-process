/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedChronologicalSelectionSelect

@[expose] public section




set_option autoImplicit false

open Set MeasureTheory MarkovProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9PathGeometry
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.ChronologicalSelection

attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ### Exit times as hitting times -/

/-- The exit time from `O` is the hit of the closed set `Oᶜ` after time zero. -/
theorem exitTime_eq_hitAfter (O : Set (Vec d)) (p : ContinuousPath (Vec d)) :
    ContinuousPath.exitTime O p = hitAfter Oᶜ 0 p := by
  rw [ContinuousPath.exitTime, SubdiffusiveProcess.CoarseGrainingVocab.Section9PathGeometry.hitAfter]
  congr 1
  ext s
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
  constructor
  · rintro ⟨t, rfl, ht⟩
    exact ⟨t, rfl, zero_le, ht⟩
  · rintro ⟨t, rfl, -, ht⟩
    exact ⟨t, rfl, ht⟩

/-- At a finite exit from an open set, reached from inside, the path is in the closure. -/
theorem mem_closure_of_lt_hitAfter (V : Set (Vec d)) (p : ContinuousPath (Vec d))
    (a : ℝ≥0∞) (t : ℝ≥0) (hlt : a < (t : ℝ≥0∞)) (hcoe : (t : ℝ≥0∞) = hitAfter Vᶜ a p) :
    p t ∈ closure V := by
  have hbefore : ∀ s : ℝ≥0, a < (s : ℝ≥0∞) → s < t → p s ∈ V := by
    intro s h1 h2
    by_contra hs
    have hle := hitAfter_le_of_mem Vᶜ a p s h1.le hs
    rw [← hcoe] at hle
    exact absurd (lt_of_le_of_lt hle (ENNReal.coe_lt_coe.mpr h2)) (lt_irrefl _)
  have hatop : a ≠ ⊤ := ne_top_of_lt hlt
  have hat : a.toNNReal < t := by
    rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hatop]
    exact hlt
  have htpos : (0 : ℝ≥0) < t := lt_of_le_of_lt (zero_le) hat
  haveI : (nhdsWithin t (Set.Iio t)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, htpos⟩
  have htend : Filter.Tendsto (fun s : ℝ≥0 => p s) (nhdsWithin t (Set.Iio t)) (nhds (p t)) :=
    (p.continuous.tendsto t).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto htend ?_
  filter_upwards [Ioo_mem_nhdsLT hat] with s hs
  refine hbefore s ?_ hs.2
  rw [← ENNReal.coe_toNNReal hatop]
  exact ENNReal.coe_lt_coe.mpr hs.1

/-! ### The comparison count -/

/-- **The counting clause.**  If `k D` pairwise separated comparison cubes are all visited by
time `theta`, then the `k`-th entrance has already happened by `theta`. -/
theorem entrance_le_of_card (order : LinearOrder ℕ) (U : ℕ → Cube d) (A : ℝ) (hA : 1 ≤ A)
    (F : Set ℕ) (hside : ∀ i ∈ F, 0 < (U i).2)
    (hloc : LocallyFinite (fun i : F => cubeSet (U i)))
    (D : ℕ) (hD : 1 ≤ D)
    (hdegree : ∀ i ∈ F, {j : ℕ | j ∈ F ∧ ¬ Disjoint
      (SubdiffusiveProcess.Section9.centeredAxisCube (U i).1 (A * (U i).2))
      (SubdiffusiveProcess.Section9.centeredAxisCube (U j).1 (A * (U j).2))}.encard ≤ D)
    (th0 : ℝ≥0∞) (p : ContinuousPath (Vec d)) (theta : ℝ≥0∞)
    (S : Finset ℕ) (hSF : ∀ i ∈ S, i ∈ F)
    (hvis : ∀ i ∈ S, ∃ t : ℝ≥0, th0 ≤ (t : ℝ≥0∞) ∧ (t : ℝ≥0∞) ≤ theta ∧
      p t ∈ middleQuarter (U i))
    (k : ℕ) (hk : 1 ≤ k) (hkD : k * D ≤ S.card) :
    entrance order U A F th0 k p ≤ theta := by
  by_contra hcon
  push_neg at hcon
  have hcharge : ∀ i : ℕ, ∃ rj : ℕ × ℕ, i ∈ S → (1 ≤ rj.1 ∧ rj.1 < k ∧ rj.2 ∈ F ∧
      (greedyRun order U A F th0 p rj.1).2.2.2 = ((rj.2 : ℕ) : WithTop ℕ) ∧
      ¬ Disjoint (SubdiffusiveProcess.Section9.centeredAxisCube (U i).1 (A * (U i).2))
        (SubdiffusiveProcess.Section9.centeredAxisCube (U rj.2).1 (A * (U rj.2).2))) := by
    intro i
    by_cases hi : i ∈ S
    swap
    · exact ⟨(0, 0), fun h => absurd h hi⟩
    obtain ⟨t, ht0, htth, htQ⟩ := hvis i hi
    have hex : ∃ n, (t : ℝ≥0∞) < entrance order U A F th0 n p :=
      ⟨k, lt_of_le_of_lt htth hcon⟩
    have hNspec : (t : ℝ≥0∞) < entrance order U A F th0 (Nat.find hex) p := Nat.find_spec hex
    have hNk : Nat.find hex ≤ k := Nat.find_le (lt_of_le_of_lt htth hcon)
    have hNpos : 0 < Nat.find hex := by
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h
      · rw [h0, entrance_zero] at hNspec
        exact absurd (lt_of_le_of_lt ht0 hNspec) (lt_irrefl _)
      · exact h
    obtain ⟨n, hn⟩ : ∃ n, Nat.find hex = n + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hnk : n < k := by omega
    have hnle : entrance order U A F th0 n p ≤ (t : ℝ≥0∞) :=
      not_lt.mp (Nat.find_min hex (by omega))
    have hNspec' : (t : ℝ≥0∞) < entrance order U A F th0 (n + 1) p := by rw [← hn]; exact hNspec
    by_cases hdept : departure order U A F th0 n p ≤ (t : ℝ≥0∞)
    · have hnotactive : i ∉ (greedyRun order U A F th0 p n).1 := by
        intro hact
        have hle2 : entrance order U A F th0 (n + 1) p ≤ (t : ℝ≥0∞) := by
          rw [entrance_succ]
          exact hitAfter_le_of_mem _ _ p t hdept (Set.mem_biUnion hact (subset_closure htQ))
        exact absurd (lt_of_lt_of_le hNspec' hle2) (lt_irrefl _)
      have hex2 : ∃ r, i ∉ (greedyRun order U A F th0 p r).1 := ⟨n, hnotactive⟩
      have hRspec := Nat.find_spec hex2
      have hRle : Nat.find hex2 ≤ n := Nat.find_le hnotactive
      have hRpos : 0 < Nat.find hex2 := by
        rcases Nat.eq_zero_or_pos (Nat.find hex2) with h0 | h
        · rw [h0] at hRspec
          exact absurd (hSF i hi) hRspec
        · exact h
      obtain ⟨r, hr⟩ : ∃ r, Nat.find hex2 = r + 1 := ⟨Nat.find hex2 - 1, by omega⟩
      have hrin : i ∈ (greedyRun order U A F th0 p r).1 :=
        not_not.mp (Nat.find_min hex2 (by omega))
      rw [hr, greedyRun_succ_fst] at hRspec
      simp only [Set.mem_setOf_eq, not_and, not_forall] at hRspec
      obtain ⟨i', hi'1, hi'2⟩ := hRspec hrin
      have hrfin : entrance order U A F th0 (r + 1) p < ⊤ :=
        lt_of_le_of_lt (le_trans (entrance_mono order U A F th0 p (by omega : r + 1 ≤ n)) hnle)
          ENNReal.coe_lt_top
      obtain ⟨j, hjF, hjsel, -, -⟩ := exists_selected order U A F hside hloc th0 p r hrfin
      have hji : j = i' := by
        have hc : ((j : ℕ) : WithTop ℕ) = ((i' : ℕ) : WithTop ℕ) := by rw [← hjsel, hi'1]
        exact_mod_cast hc
      refine ⟨(r + 1, j), fun _ => ⟨by omega, by omega, hjF, hjsel, ?_⟩⟩
      rw [hji]
      exact hi'2
    · have hlt : (t : ℝ≥0∞) < departure order U A F th0 n p := not_le.mp hdept
      have hnpos : 0 < n := by
        rcases Nat.eq_zero_or_pos n with h0 | h
        · rw [h0, departure_zero] at hlt
          exact absurd (lt_of_le_of_lt ht0 hlt) (lt_irrefl _)
        · exact h
      obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hmfin : entrance order U A F th0 (m + 1) p < ⊤ := by
        rw [← hm]; exact lt_of_le_of_lt hnle ENNReal.coe_lt_top
      obtain ⟨j, hjF, hjsel, -, -⟩ := exists_selected order U A F hside hloc th0 p m hmfin
      have hmem : p t ∈ cubeSet (U j) := by
        refine mem_cubeSet_of_lt_departure order U A F th0 p m j hjsel t ?_ ?_
        · rw [← hm]; exact hnle
        · rw [← hm]; exact hlt
      have hnd : ¬ Disjoint (SubdiffusiveProcess.Section9.centeredAxisCube (U i).1 (A * (U i).2))
          (SubdiffusiveProcess.Section9.centeredAxisCube (U j).1 (A * (U j).2)) :=
        not_disjoint_dilate_of_mem U A hA i j (hside i (hSF i hi)) (hside j hjF) (p t)
          (middleQuarter_subset_cubeSet (U i) (hside i (hSF i hi)) htQ) hmem
      exact ⟨(m + 1, j), fun _ => ⟨by omega, by omega, hjF, hjsel, hnd⟩⟩
  choose f hf using hcharge
  have himgsub : S.image (fun i => (f i).1) ⊆ Finset.Ico 1 k := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_Ico.mpr ⟨(hf i hi).1, (hf i hi).2.1⟩
  have hfiber : ∀ b ∈ S.image (fun i => (f i).1),
      {a ∈ S | (fun i => (f i).1) a = b}.card ≤ D := by
    intro b hb
    obtain ⟨i0, hi0, hb0⟩ := Finset.mem_image.mp hb
    have hspec0 := hf i0 hi0
    have hsub : ((({a ∈ S | (fun i => (f i).1) a = b} : Finset ℕ) : Set ℕ)) ⊆
        {j : ℕ | j ∈ F ∧ ¬ Disjoint
          (SubdiffusiveProcess.Section9.centeredAxisCube (U (f i0).2).1 (A * (U (f i0).2).2))
          (SubdiffusiveProcess.Section9.centeredAxisCube (U j).1 (A * (U j).2))} := by
      intro a ha
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha
      obtain ⟨haS, hab⟩ := ha
      have hspec := hf a haS
      have hjj : (f a).2 = (f i0).2 := by
        have hc : (((f a).2 : ℕ) : WithTop ℕ) = (((f i0).2 : ℕ) : WithTop ℕ) := by
          rw [← hspec.2.2.2.1, ← hspec0.2.2.2.1, hab, hb0]
        exact_mod_cast hc
      refine ⟨hSF a haS, fun hdisj => ?_⟩
      exact hspec.2.2.2.2 (by rw [hjj]; exact hdisj.symm)
    have hcard : ((({a ∈ S | (fun i => (f i).1) a = b} : Finset ℕ) : Set ℕ)).encard ≤ (D : ℕ∞) :=
      le_trans (Set.encard_mono hsub) (hdegree (f i0).2 hspec0.2.2.1)
    rw [Set.encard_coe_eq_coe_finsetCard] at hcard
    exact_mod_cast hcard
  have hScard : S.card ≤ D * (S.image (fun i => (f i).1)).card :=
    Finset.card_le_mul_card_image S D hfiber
  obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have himgcard : (S.image (fun i => (f i).1)).card ≤ m := by
    have hle := Finset.card_le_card himgsub
    rw [Nat.card_Ico, hm] at hle
    simpa using hle
  have hfinal : m * D + D ≤ m * D :=
    calc m * D + D = (m + 1) * D := by ring
      _ = k * D := by rw [hm]
      _ ≤ S.card := hkD
      _ ≤ D * (S.image (fun i => (f i).1)).card := hScard
      _ ≤ D * m := Nat.mul_le_mul_left D himgcard
      _ = m * D := Nat.mul_comm D m
  have h2 : m * D + D ≤ m * D + 0 := by rw [Nat.add_zero]; exact hfinal
  have hD0 : D ≤ 0 := Nat.le_of_add_le_add_left h2
  omega

/-! ### Containment in an open set -/

/-- **The containment clause.** -/
theorem departure_le_exitTime (order : LinearOrder ℕ) (U : ℕ → Cube d) (A : ℝ) (F : Set ℕ)
    (hside : ∀ i ∈ F, 0 < (U i).2)
    (hloc : LocallyFinite (fun i : F => cubeSet (U i)))
    (th0 : ℝ≥0∞) (p : ContinuousPath (Vec d)) (O : Set (Vec d)) (hO : IsOpen O)
    (hcl : ∀ i ∈ F, closure (cubeSet (U i)) ⊆ O)
    (theta : ℝ≥0∞) (n : ℕ)
    (h1 : entrance order U A F th0 (n + 1) p ≤ theta)
    (h2 : theta ≤ ContinuousPath.exitTime O p) :
    departure order U A F th0 (n + 1) p ≤ ContinuousPath.exitTime O p ∧
      (departure order U A F th0 (n + 1) p = ContinuousPath.exitTime O p →
        departure order U A F th0 (n + 1) p = ⊤ ∧ ContinuousPath.exitTime O p = ⊤) := by
  rcases eq_or_lt_of_le (le_top (a := entrance order U A F th0 (n + 1) p)) with htop | hfin
  · have hthetatop : theta = ⊤ := top_le_iff.mp (htop ▸ h1)
    have hexittop : ContinuousPath.exitTime O p = ⊤ := top_le_iff.mp (hthetatop ▸ h2)
    have hdeptop : departure order U A F th0 (n + 1) p = ⊤ :=
      top_le_iff.mp (htop ▸ entrance_le_departure order U A F th0 p (n + 1))
    exact ⟨by rw [hdeptop, hexittop], fun _ => ⟨hdeptop, hexittop⟩⟩
  · obtain ⟨j, hjF, hjsel, -, hstrict⟩ := exists_selected order U A F hside hloc th0 p n hfin
    have hdep : departure order U A F th0 (n + 1) p
        = hitAfter (cubeSet (U j))ᶜ (entrance order U A F th0 (n + 1) p) p := by
      rw [departure_succ_eq_hitAfter, histOf_succ, hjsel]
      rfl
    have hsubO : cubeSet (U j) ⊆ O := subset_trans subset_closure (hcl j hjF)
    have hle : departure order U A F th0 (n + 1) p ≤ ContinuousPath.exitTime O p := by
      rcases eq_or_lt_of_le (le_top (a := ContinuousPath.exitTime O p)) with hetop | hefin
      · rw [hetop]; exact le_top
      · obtain ⟨t0, ht0, -, ht0O⟩ :=
          hitAfter_attained Oᶜ hO.isClosed_compl 0 p (by rw [← exitTime_eq_hitAfter]; exact hefin)
        rw [← exitTime_eq_hitAfter] at ht0
        rw [hdep, ← ht0]
        refine hitAfter_le_of_mem _ _ p t0 ?_ ?_
        · rw [ht0]; exact h1.trans h2
        · exact fun hc => ht0O (hsubO hc)
    refine ⟨hle, fun heq => ?_⟩
    rcases eq_or_lt_of_le (le_top (a := ContinuousPath.exitTime O p)) with hetop | hefin
    · exact ⟨by rw [heq, hetop], hetop⟩
    · exfalso
      obtain ⟨t0, ht0, -, ht0O⟩ :=
        hitAfter_attained Oᶜ hO.isClosed_compl 0 p (by rw [← exitTime_eq_hitAfter]; exact hefin)
      rw [← exitTime_eq_hitAfter] at ht0
      have hdepfin : departure order U A F th0 (n + 1) p < ⊤ := by rw [heq]; exact hefin
      obtain ⟨t1, ht1, -, -⟩ :=
        hitAfter_attained (cubeSet (U j))ᶜ (isOpen_cubeSet (U j)).isClosed_compl
          (entrance order U A F th0 (n + 1) p) p (by rw [← hdep]; exact hdepfin)
      rw [← hdep] at ht1
      have hsame : t0 = t1 := by
        have : ((t0 : ℝ≥0) : ℝ≥0∞) = ((t1 : ℝ≥0) : ℝ≥0∞) := by rw [ht0, ht1, heq]
        exact_mod_cast this
      have hcl1 : p t1 ∈ closure (cubeSet (U j)) := by
        refine mem_closure_of_lt_hitAfter (cubeSet (U j)) p
          (entrance order U A F th0 (n + 1) p) t1 ?_ ?_
        · rw [ht1]; exact hstrict
        · rw [ht1]; exact hdep
      exact ht0O (hcl j hjF (hsame ▸ hcl1))

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.ChronologicalSelection

end
