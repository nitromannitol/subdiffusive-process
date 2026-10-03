module

public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.lem_mass_grid_partition

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SubdiffusiveProcess MeasureTheory

namespace Paper
noncomputable section

lemma aux_lem_mass_nondoubling_fiber_sum
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (g : α → β) (N : ℕ) (f : β → ℝ)
    (hN : ∀ b : β, (s.filter (fun a => g a = b)).card ≤ N)
    (hf : ∀ b : β, 0 ≤ f b) :
    (∑ a ∈ s, f (g a)) ≤ (N : ℝ) * ∑ b ∈ s.image g, f b := by
  classical
  let P : Finset β := s.image g
  have hmap : ∀ a ∈ s, g a ∈ P := by
    intro a ha
    exact Finset.mem_image.2 ⟨a, ha, rfl⟩
  have hfiber :
      (∑ b ∈ P, ∑ a ∈ s.filter (fun a => g a = b), f b) =
        ∑ a ∈ s, f (g a) := by
    simpa only [P] using
      (Finset.sum_fiberwise_of_maps_to' (s := s) (t := P) (g := g)
        hmap f)
  have hfilter : ∀ b ∈ P,
      (∑ a ∈ s.filter (fun a => g a = b), f b) ≤ (N : ℝ) * f b := by
    intro b hb
    have hcard := hN b
    calc
      (∑ a ∈ s.filter (fun a => g a = b), f b) =
          ((s.filter (fun a => g a = b)).card : ℝ) * f b := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * f b := by
        apply mul_le_mul_of_nonneg_right ?_ (hf b)
        exact_mod_cast hcard
  calc
    (∑ a ∈ s, f (g a)) =
        ∑ b ∈ P, ∑ a ∈ s.filter (fun a => g a = b), f b := hfiber.symm
    _ ≤ ∑ b ∈ P, (N : ℝ) * f b := by
      exact Finset.sum_le_sum (fun b hb => hfilter b hb)
    _ = (N : ℝ) * ∑ b ∈ P, f b := by
      rw [Finset.mul_sum]
    _ = (N : ℝ) * ∑ b ∈ s.image g, f b := by rfl



theorem lem_mass_nondoubling
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
    (zeta : ℝ) → (hzeta : 0 < zeta) →
    (zQ : SpatialCoordinates d) → (rQ : ℝ) → (hrQ : 0 < rQ) →
    (mu : Measure (SpatialCoordinates d)) → [IsFiniteMeasure mu] →
    let Q := centeredCube zQ rQ hrQ
    (hsupp : mu ((Q : Set (SpatialCoordinates d))ᶜ) = 0) →
    ∀ (sigma : Shift) (n : ℕ), 1 ≤ n →
      (mu (⋃ k ∈ {k : Fin d → Int |
        L ^ ((d : ℝ) + zeta) * (mu (cell sigma n k)).toReal <
          (mu (parent sigma n k)).toReal}, cell sigma n k)).toReal ≤
        L ^ (-zeta) * (mu (Q : Set (SpatialCoordinates d))).toReal := by
  dsimp
  intro zeta hzeta zQ rQ hrQ mu hmu hsupp sigma n hn
  have hpart := lem_mass_grid_partition d H1 Mm hd hH1 hMm
  dsimp at hpart
  rcases hpart with ⟨hmeas, hmem, hchild, hcount, hfin⟩
  let L : ℝ := (3 : ℝ) ^ H1
  let K : Type := Fin d → Int
  let Shift : Type := Fin d → Fin Mm
  let shift : Shift → Fin d → ℝ := fun sigma i => ((sigma i).val : ℝ) / (Mm : ℝ)
  let side : ℕ → ℝ := fun j => L ^ (-(j : ℝ))
  let cell : Shift → ℕ → K → Set (SpatialCoordinates d) :=
    fun sigma j k => Set.pi Set.univ (fun i =>
      Set.Ico (shift sigma i + side j * (k i : ℝ))
        (shift sigma i + side j * (k i : ℝ) + side j))
  let parentIdx : K → Fin d → Int := fun k i => Int.floor ((k i : ℝ) / L)
  let parent : Shift → ℕ → K → Set (SpatialCoordinates d) :=
    fun sigma j k => cell sigma (j - 1) (parentIdx k)
  let pointIdx : Shift → ℕ → SpatialCoordinates d → K :=
    fun sigma j x i => Int.floor ((x i - shift sigma i) / side j)
  let Q : Set (SpatialCoordinates d) := centeredCube zQ rQ hrQ
  change (mu (⋃ k ∈ {k : K |
    L ^ ((d : ℝ) + zeta) * (mu (cell sigma n k)).toReal <
      (mu (parent sigma n k)).toReal}, cell sigma n k)).toReal ≤
    L ^ (-zeta) * (mu Q).toReal
  have hmeasC : ∀ (s : Shift) (j : ℕ) (k : K), MeasurableSet (cell s j k) := by
    simpa [cell, K, Shift, shift, side, L] using hmeas
  have hmemC : ∀ (s : Shift) (j : ℕ) (x : SpatialCoordinates d) (k : K),
      x ∈ cell s j k ↔ k = pointIdx s j x := by
    simpa [cell, pointIdx, K, Shift, shift, side, L] using hmem
  have hchildC : ∀ (s : Shift) (j : ℕ), 1 ≤ j → ∀ k : K,
      cell s j k ⊆ parent s j k ∧
        ∀ x : SpatialCoordinates d, x ∈ cell s j k →
          pointIdx s (j - 1) x = parentIdx k := by
    simpa [cell, parent, pointIdx, parentIdx, K, Shift, shift, side, L] using hchild
  have hcountC : ∀ p : K,
      {k : K | parentIdx k = p}.Finite ∧
        Nat.card {k : K // parentIdx k = p} = (3 ^ H1) ^ d := by
    simpa [parentIdx, K, L] using hcount
  let Bad : Set K := {k : K |
    L ^ ((d : ℝ) + zeta) * (mu (cell sigma n k)).toReal <
      (mu (parent sigma n k)).toReal}
  let Relevant : Set K := {k : K | (cell sigma n k ∩ Q).Nonempty}
  have hRelevant : Relevant.Finite := by
    simpa [Relevant, Q, cell, K, Shift, shift, side, L] using
      hfin sigma n zQ rQ hrQ
  let F : Finset K := hRelevant.toFinset.filter (fun k => k ∈ Bad)
  change (mu (⋃ k ∈ Bad, cell sigma n k)).toReal ≤
    L ^ (-zeta) * (mu Q).toReal
  have hsubset : (⋃ k ∈ Bad, cell sigma n k) ⊆
      (⋃ k ∈ F, cell sigma n k) ∪ Qᶜ := by
    intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨k, hx⟩
    rcases Set.mem_iUnion.1 hx with ⟨hkBad, hxk⟩
    by_cases hxQ : x ∈ Q
    · left
      have hkRel : k ∈ Relevant := ⟨x, ⟨hxk, hxQ⟩⟩
      have hkF : k ∈ F := by
        exact Finset.mem_filter.2 ⟨hRelevant.mem_toFinset.2 hkRel, hkBad⟩
      exact Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hkF, hxk⟩⟩
    · exact Or.inr hxQ
  have hQmeas : MeasurableSet Q := by
    change MeasurableSet (Metric.ball zQ (rQ / 2))
    exact Metric.isOpen_ball.measurableSet
  have hsuppQ : mu Qᶜ = 0 := by
    change mu ((centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))ᶜ) = 0
    exact hsupp
  have hQzero : mu.real Qᶜ = 0 := by
    simp [Measure.real, hsuppQ]
  have hunivQ : mu.real Set.univ = mu.real Q := by
    have h := measureReal_add_measureReal_compl (μ := mu) hQmeas
    linarith
  have hmass_subset :
      (mu (⋃ k ∈ Bad, cell sigma n k)).toReal ≤
        ∑ k ∈ F, mu.real (cell sigma n k) := by
    calc
      (mu (⋃ k ∈ Bad, cell sigma n k)).toReal =
          mu.real (⋃ k ∈ Bad, cell sigma n k) := rfl
      _ ≤ mu.real ((⋃ k ∈ F, cell sigma n k) ∪ Qᶜ) :=
        measureReal_mono hsubset
      _ ≤ mu.real (⋃ k ∈ F, cell sigma n k) + mu.real Qᶜ :=
        measureReal_union_le _ _
      _ = mu.real (⋃ k ∈ F, cell sigma n k) := by simp [hQzero]
      _ ≤ ∑ k ∈ F, mu.real (cell sigma n k) :=
        measureReal_biUnion_finset_le F (fun k => cell sigma n k)
  have hdisj : ∀ j : ℕ, Pairwise (fun k l : K =>
      Disjoint (cell sigma j k) (cell sigma j l)) := by
    intro j k l hkl
    refine Set.disjoint_left.2 ?_
    intro x hxk hxl
    exact hkl ((hmemC sigma j x k).1 hxk |>.trans ((hmemC sigma j x l).1 hxl).symm)
  have hparent_meas : ∀ p : K, MeasurableSet (cell sigma (n - 1) p) := by
    intro p
    exact hmeasC sigma (n - 1) p
  have hparent_disj : (↑(F.image parentIdx) : Set K).PairwiseDisjoint
      (fun p => cell sigma (n - 1) p) := by
    intro p hp q hq hpq
    exact hdisj (n - 1) hpq
  have hparent_sum :
      (∑ p ∈ F.image parentIdx, mu.real (cell sigma (n - 1) p)) ≤ mu.real Q := by
    calc
      (∑ p ∈ F.image parentIdx, mu.real (cell sigma (n - 1) p)) ≤ mu.real Set.univ :=
        sum_measureReal_le_measureReal_univ (μ := mu)
          (fun p hp => hparent_meas p) hparent_disj
      _ = mu.real Q := hunivQ
  let N : ℕ := (3 ^ H1) ^ d
  let c : ℝ := L ^ (-((d : ℝ) + zeta))
  have hL : 0 < L := by
    dsimp [L]
    positivity
  have hN : (N : ℝ) = L ^ (d : ℝ) := by
    dsimp [N, L]
    rw [Real.rpow_natCast]
    norm_num [Nat.cast_pow]
  have hbadmass : ∀ k ∈ F,
      mu.real (cell sigma n k) ≤
        c * mu.real (cell sigma (n - 1) (parentIdx k)) := by
    intro k hk
    have hkbad := (Finset.mem_filter.1 hk).2
    change L ^ ((d : ℝ) + zeta) * mu.real (cell sigma n k) <
      mu.real (cell sigma (n - 1) (parentIdx k)) at hkbad
    have hfac : 0 < L ^ ((d : ℝ) + zeta) := by positivity
    have hdiv : mu.real (cell sigma n k) ≤
        mu.real (cell sigma (n - 1) (parentIdx k)) /
          L ^ ((d : ℝ) + zeta) := by
      apply (le_div_iff₀ hfac).2
      simpa [mul_comm] using (le_of_lt hkbad)
    calc
      mu.real (cell sigma n k) ≤
          mu.real (cell sigma (n - 1) (parentIdx k)) /
            L ^ ((d : ℝ) + zeta) := hdiv
      _ = c * mu.real (cell sigma (n - 1) (parentIdx k)) := by
        dsimp [c]
        rw [div_eq_mul_inv, Real.rpow_neg (le_of_lt hL)]
        ring
  have hsum_parent :
      (∑ k ∈ F, mu.real (cell sigma (n - 1) (parentIdx k))) ≤
        (N : ℝ) * mu.real Q := by
    have hcardle : ∀ p : K,
        (F.filter (fun k => parentIdx k = p)).card ≤ N := by
      intro p
      let A : Finset K := (hcountC p).1.toFinset
      have hsub : F.filter (fun k => parentIdx k = p) ⊆ A := by
        intro k hk
        exact (hcountC p).1.mem_toFinset.2 ((Finset.mem_filter.1 hk).2)
      have hcardA : A.card = N := by
        dsimp [A, N]
        rw [← Set.ncard_eq_toFinset_card _ (hcountC p).1]
        exact (hcountC p).2
      exact (Finset.card_le_card hsub).trans_eq hcardA
    have hsumfiber := aux_lem_mass_nondoubling_fiber_sum F parentIdx N
      (fun p => mu.real (cell sigma (n - 1) p)) hcardle
      (fun p => measureReal_nonneg)
    calc
      (∑ k ∈ F, mu.real (cell sigma (n - 1) (parentIdx k))) ≤
          (N : ℝ) * ∑ p ∈ F.image parentIdx,
            mu.real (cell sigma (n - 1) p) := hsumfiber
      _ ≤ (N : ℝ) * mu.real Q := by
        exact mul_le_mul_of_nonneg_left hparent_sum (by positivity)
  have hchildsum :
      (∑ k ∈ F, mu.real (cell sigma n k)) ≤
        L ^ (-zeta) * mu.real Q := by
    calc
      (∑ k ∈ F, mu.real (cell sigma n k)) ≤
          ∑ k ∈ F, c * mu.real (cell sigma (n - 1) (parentIdx k)) := by
            exact Finset.sum_le_sum (fun k hk => hbadmass k hk)
      _ = c * ∑ k ∈ F, mu.real (cell sigma (n - 1) (parentIdx k)) := by
        rw [Finset.mul_sum]
      _ ≤ c * ((N : ℝ) * mu.real Q) := by
        exact mul_le_mul_of_nonneg_left hsum_parent (by positivity)
      _ = L ^ (-zeta) * mu.real Q := by
        have hfactor : (N : ℝ) * c = L ^ (-zeta) := by
          rw [hN]
          dsimp [c]
          calc
            L ^ (d : ℝ) * L ^ (-((d : ℝ) + zeta)) =
                L ^ ((d : ℝ) + (-((d : ℝ) + zeta))) := by
                  rw [Real.rpow_add hL]
            _ = L ^ (-zeta) := by congr 1; ring
        calc
          c * ((N : ℝ) * mu.real Q) = ((N : ℝ) * c) * mu.real Q := by ring
          _ = L ^ (-zeta) * mu.real Q := by rw [hfactor]
  exact hmass_subset.trans hchildsum

end
end Paper
