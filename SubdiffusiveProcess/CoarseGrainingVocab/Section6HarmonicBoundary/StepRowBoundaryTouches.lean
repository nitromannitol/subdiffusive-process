import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.StepRowProjectedParents
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.IntervalGeometry




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- A point reached along a segment from inside a set is in its closure. -/
theorem mem_closure_of_segment {S : Set (Vec d)} {y c : Vec d} {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ i, |y i - c i| ≤ B)
    (h : ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ p : Vec d,
      (∀ i, p i = c i + t * (y i - c i)) → p ∈ S) :
    y ∈ closure S := by
  rw [Metric.mem_closure_iff]
  intro eps heps
  set delta : ℝ := min (1 / 2) (eps / (2 * (B + 1))) with hdelta
  have hB1 : (0 : ℝ) < B + 1 := by linarith
  have hdelta0 : 0 < delta := by
    rw [hdelta]
    exact lt_min (by norm_num) (by positivity)
  have hdelta1 : delta ≤ 1 / 2 := min_le_left _ _
  have hdelta2 : delta ≤ eps / (2 * (B + 1)) := min_le_right _ _
  refine ⟨fun i ↦ c i + (1 - delta) * (y i - c i),
    h (1 - delta) (by linarith) (by linarith) _ (fun i ↦ rfl), ?_⟩
  rw [dist_pi_lt_iff heps]
  intro i
  have hval : y i - (c i + (1 - delta) * (y i - c i)) = delta * (y i - c i) := by
    ring
  rw [Real.dist_eq, hval, abs_mul, abs_of_pos hdelta0]
  have h1 : delta * |y i - c i| ≤ delta * B :=
    mul_le_mul_of_nonneg_left (hB i) hdelta0.le
  have h2 : delta * B ≤ eps / (2 * (B + 1)) * B :=
    mul_le_mul_of_nonneg_right hdelta2 hB0
  have h3 : eps / (2 * (B + 1)) * B < eps := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  linarith

/-- The closed cube of half-side `3^m/2` is inside the closure of `𝔠_m`. -/
theorem mem_closure_cube_of_abs_le {m : ℤ} {y : Vec d}
    (hy : ∀ i, |y i| ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ m) :
    y ∈ closure (cube d m) := by
  refine mem_closure_of_segment (c := (0 : Vec d))
    (B := (1 / 2 : ℝ) * (3 : ℝ) ^ m) (by positivity)
    (fun i ↦ by simpa using hy i) ?_
  intro t ht0 ht1 p hp
  rw [cube, Homogenization.mem_openCubeSet_originCube_iff]
  intro i
  have hpi : p i = t * y i := by
    rw [hp i]; simp
  have habs : |p i| ≤ t * ((1 / 2 : ℝ) * (3 : ℝ) ^ m) := by
    rw [hpi, abs_mul, abs_of_nonneg ht0]
    exact mul_le_mul_of_nonneg_left (hy i) ht0
  have hpos : (0 : ℝ) < (1 / 2 : ℝ) * (3 : ℝ) ^ m := by positivity
  have hlt : t * ((1 / 2 : ℝ) * (3 : ℝ) ^ m) < (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
    nlinarith
  have hbound := abs_lt.mp (lt_of_le_of_lt habs hlt)
  exact ⟨by linarith [hbound.1], by linarith [hbound.2]⟩

/-- A point at sup-distance at most `3^k/2` from the centre lies in the closure
of the translated cube. -/
theorem mem_closure_translatedCube_of_abs_le {k : ℤ} {c y : Vec d}
    (hy : ∀ i, |y i - c i| ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ k) :
    y ∈ closure (translatedCube d k c) := by
  refine mem_closure_of_segment (B := (1 / 2 : ℝ) * (3 : ℝ) ^ k)
    (by positivity) hy ?_
  intro t ht0 ht1 p hp
  rw [mem_translatedCube_iff, cube, Homogenization.mem_openCubeSet_originCube_iff]
  intro i
  have hpi : p i - c i = t * (y i - c i) := by rw [hp i]; ring
  have habs : |p i - c i| ≤ t * ((1 / 2 : ℝ) * (3 : ℝ) ^ k) := by
    rw [hpi, abs_mul, abs_of_nonneg ht0]
    exact mul_le_mul_of_nonneg_left (hy i) ht0
  have hpos : (0 : ℝ) < (1 / 2 : ℝ) * (3 : ℝ) ^ k := by positivity
  have hlt : t * ((1 / 2 : ℝ) * (3 : ℝ) ^ k) < (1 / 2 : ℝ) * (3 : ℝ) ^ k := by
    nlinarith
  have hbound := abs_lt.mp (lt_of_le_of_lt habs hlt)
  simp only [Pi.sub_apply]
  exact ⟨by linarith [hbound.1], by linarith [hbound.2]⟩

/-- **The boundary branch produces the printed boundary indicator.**

If the scale-`(k−1)` patch of a point leaves `𝔠_m`, then the closed projected
parent `q̂ + 𝔠_k` meets `∂𝔠_m`. -/
theorem boundaryTouches_translatedCube_wellPlacedCentre {m k : ℤ} {q : Vec d}
    (hkm : k ≤ m) (hnot : ¬ openCubeAtScale q (k - 1) ⊆ cube d m) :
    BoundaryTouches (translatedCube d k (wellPlacedCentre q m k)) (cube d m) := by
  classical
  set g : ℝ := wellPlacedHalfGap m k with hgdef
  set c : Vec d := wellPlacedCentre q m k with hcdef
  have hcapp : ∀ i, c i = max (-g) (min g (q i)) := fun i ↦ rfl
  have hg0 : 0 ≤ g := wellPlacedHalfGap_nonneg hkm
  have h3k : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  have h3m : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) _
  have hgval : g = (1 / 2 : ℝ) * (3 : ℝ) ^ m - (1 / 2 : ℝ) * (3 : ℝ) ^ k := rfl
  -- the clamp is active in some coordinate
  have hactive : ∃ i : Fin d, g < |q i| := by
    by_contra hall
    push_neg at hall
    have hceq : c = q := by
      funext i
      have hi := abs_le.mp (hall i)
      rw [hcapp i, min_eq_right hi.2, max_eq_right (by linarith [hi.1])]
    refine hnot ?_
    intro p hp
    have hsub : translatedCube d k c ⊆ cube d m := by
      rw [hcdef]
      exact translatedCube_wellPlacedCentre_subset_cube q hkm
    refine hsub ?_
    rw [hceq, mem_translatedCube_iff, cube,
      Homogenization.mem_openCubeSet_originCube_iff]
    intro i
    have hpi := hp i
    have hrpcast : Real.rpow (3 : ℝ) (((k - 1 : ℤ)) : ℝ) = (3 : ℝ) ^ (k - 1) :=
      Real.rpow_intCast 3 (k - 1)
    have hrp : Real.rpow (3 : ℝ) (((k - 1 : ℤ)) : ℝ) = (3 : ℝ) ^ k / 3 := by
      rw [hrpcast, zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
    rw [hrp] at hpi
    have hbound := abs_lt.mp hpi
    simp only [Pi.sub_apply]
    exact ⟨by linarith [hbound.1], by linarith [hbound.2]⟩
  obtain ⟨i0, hi0⟩ := hactive
  have hcbound : ∀ i, |c i| ≤ g := by
    intro i
    rw [abs_le]
    exact ⟨neg_wellPlacedHalfGap_le_wellPlacedCentre q m k i,
      wellPlacedCentre_le_wellPlacedHalfGap hkm q i⟩
  have hci0 : c i0 = g ∨ c i0 = -g := by
    rcases abs_cases (q i0) with ⟨heq, _⟩ | ⟨heq, _⟩
    · left
      have hq : g < q i0 := by rw [heq] at hi0; exact hi0
      rw [hcapp i0, min_eq_left hq.le, max_eq_right (by linarith)]
    · right
      have hq : q i0 < -g := by rw [heq] at hi0; linarith
      rw [hcapp i0, min_eq_right (by linarith), max_eq_left (by linarith)]
  -- the touching point
  set y : Vec d := Function.update c i0
    (if c i0 = g then (1 / 2 : ℝ) * (3 : ℝ) ^ m
      else -((1 / 2 : ℝ) * (3 : ℝ) ^ m)) with hydef
  have hy0 : y i0 = (if c i0 = g then (1 / 2 : ℝ) * (3 : ℝ) ^ m
      else -((1 / 2 : ℝ) * (3 : ℝ) ^ m)) := by
    rw [hydef, Function.update_self]
  have hyval0 : y i0 = (1 / 2 : ℝ) * (3 : ℝ) ^ m ∨
      y i0 = -((1 / 2 : ℝ) * (3 : ℝ) ^ m) := by
    rw [hy0]; split
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hyi0 : |y i0 - c i0| = (1 / 2 : ℝ) * (3 : ℝ) ^ k := by
    rw [hy0]
    by_cases hg : c i0 = g
    · rw [if_pos hg, hg, hgval, abs_of_nonneg (by linarith)]
      ring
    · have hneg : c i0 = -g := hci0.resolve_left hg
      rw [if_neg hg, hneg, hgval, abs_of_nonpos (by linarith)]
      ring
  have hyj : ∀ i, i ≠ i0 → y i = c i := by
    intro i hi
    rw [hydef, Function.update_of_ne hi]
  have hydist : ∀ i, |y i - c i| ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ k := by
    intro i
    by_cases hi : i = i0
    · subst hi; exact le_of_eq hyi0
    · rw [hyj i hi, sub_self, abs_zero]; positivity
  have hyabs : ∀ i, |y i| ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
    intro i
    by_cases hi : i = i0
    · subst hi
      rcases hyval0 with he | he
      · rw [he, abs_of_nonneg (by positivity)]
      · rw [he, abs_of_nonpos (by linarith [h3m])]
        linarith
    · rw [hyj i hi]
      exact (hcbound i).trans (by rw [hgval]; linarith)
  have hynot : y ∉ cube d m := by
    intro hmem
    rw [cube, Homogenization.mem_openCubeSet_originCube_iff] at hmem
    have hb := hmem i0
    rcases hyval0 with he | he <;> rw [he] at hb <;> linarith [hb.1, hb.2]
  have hopen : IsOpen (cube d m) := (isOpenBoundedConvexDomain_cube d m).isOpen
  have hfrontier : y ∈ frontier (cube d m) := by
    simp only [frontier, Set.mem_diff, hopen.interior_eq]
    exact ⟨mem_closure_cube_of_abs_le hyabs, hynot⟩
  exact Set.nonempty_iff_ne_empty.mp
    ⟨y, mem_closure_translatedCube_of_abs_le hydist, hfrontier⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
