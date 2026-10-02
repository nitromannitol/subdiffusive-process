import SubdiffusiveProcess.Paper.lem_finite_stopping_partition_tree
import Mathlib.MeasureTheory.Measure.Real
open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal BigOperators Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper
open Classical

/-- Selected unstopped steps of a tree with monotone mass must be bad,
non-padded, or strict mass drops. This applies to arbitrary finite measures. -/
theorem aux_density_stopping_measure_hits
    (d m J : ℕ) (mass : (n : ℕ) → (Fin n → OddGridIndex d m) → ℝ)
    (Sel : ℕ → Prop) (Good : (n : ℕ) → (Fin n → OddGridIndex d m) → Prop)
    (Pad : OddGridIndex d m → Prop) (LD fl : ℝ) (hLD : 1 < LD) (hfl : 0 < fl)
    (hmono : ∀ n (w : Fin (n + 1) → OddGridIndex d m),
      mass (n + 1) w ≤ mass n (fun i => w i.castSucc))
    (nsel nbad g : ℕ) (w : Fin J → OddGridIndex d m)
    (hno : ∀ (k : ℕ) (hk : k ≤ J),
      ¬ aux_lem_finite_stopping_partition_stopRule Sel Good Pad mass LD k
        (aux_lem_finite_stopping_partition_wordPrefix w k hk))
    (hbad : ((Finset.univ : Finset (Fin J)).filter fun i =>
      ¬ Good (i.val + 1) (aux_lem_finite_stopping_partition_wordPrefix w (i.val + 1) i.isLt)).card ≤ nbad)
    (hsel : nsel ≤ ((Finset.univ : Finset (Fin J)).filter fun i => Sel (i.val + 1)).card)
    (hfinal : fl ≤ mass J w)
    (hinit : mass 0 (aux_lem_finite_stopping_partition_wordPrefix w 0 (Nat.zero_le J)) < LD ^ (g + 1) * fl) :
    nsel - nbad - g ≤ ((Finset.univ : Finset (Fin J)).filter fun i =>
      w i ∈ (Finset.univ.filter fun l => ¬ Pad l)).card := by
  classical
  let lam : ℕ → ℝ := fun k => if hk : k ≤ J then
    mass k (aux_lem_finite_stopping_partition_wordPrefix w k hk) else mass J w
  have hlam : ∀ k (hk : k ≤ J),
      lam k = mass k (aux_lem_finite_stopping_partition_wordPrefix w k hk) := fun k hk => dif_pos hk
  have hmono' : ∀ k, lam (k + 1) ≤ lam k := by
    intro k
    by_cases hk : k + 1 ≤ J
    · rw [hlam (k + 1) hk, hlam k (by omega)]
      exact hmono k (aux_lem_finite_stopping_partition_wordPrefix w (k + 1) hk)
    · have h1 : lam (k + 1) = mass J w := dif_neg hk
      by_cases hk' : k ≤ J
      · have hkJ : k = J := by omega
        subst hkJ
        rw [h1, hlam k hk', aux_lem_finite_stopping_partition_wordPrefix_self]
      · rw [h1, show lam k = mass J w from dif_neg hk']
  have hfinal' : fl ≤ lam J := by
    rw [hlam J le_rfl, aux_lem_finite_stopping_partition_wordPrefix_self]
    exact hfinal
  have hinit' : lam 0 < LD ^ (g + 1) * fl := by
    rw [hlam 0 (Nat.zero_le J)]
    exact hinit
  have hdrop := aux_lem_finite_stopping_partition_dropCount_le lam LD fl hLD hfl
    hmono' J g hfinal' hinit'
  have hclass : ∀ i ∈ (Finset.univ : Finset (Fin J)), Sel (i.val + 1) →
      ¬ Good (i.val + 1) (aux_lem_finite_stopping_partition_wordPrefix w (i.val + 1) i.isLt) ∨
        w i ∈ (Finset.univ.filter fun l => ¬ Pad l) ∨ LD * lam (i.val + 1) < lam i.val := by
    intro i _ hSel
    have hns := hno (i.val + 1) i.isLt
    have hlast : aux_lem_finite_stopping_partition_wordPrefix w (i.val + 1) i.isLt (Fin.last i.val) = w i :=
      congrArg w (Fin.ext rfl)
    have hinitw : (fun j : Fin i.val => aux_lem_finite_stopping_partition_wordPrefix w (i.val + 1) i.isLt j.castSucc) =
        aux_lem_finite_stopping_partition_wordPrefix w i.val (Nat.le_of_lt i.isLt) := by
      funext j
      rfl
    simp only [aux_lem_finite_stopping_partition_stopRule, not_and, not_le] at hns
    by_cases hG : Good (i.val + 1) (aux_lem_finite_stopping_partition_wordPrefix w (i.val + 1) i.isLt)
    · by_cases hP : Pad (w i)
      · right; right
        have h := hns hSel hG (by rw [hlast]; exact hP)
        rw [hlam (i.val + 1) i.isLt, hlam i.val (Nat.le_of_lt i.isLt)]
        rw [hinitw] at h
        exact h
      · right; left
        simp [hP]
    · exact Or.inl hG
  have hcount := aux_lem_finite_stopping_partition_card_filter_le_three (Finset.univ : Finset (Fin J))
    (fun i => Sel (i.val + 1))
    (fun i => ¬ Good (i.val + 1) (aux_lem_finite_stopping_partition_wordPrefix w (i.val + 1) i.isLt))
    (fun i => w i ∈ (Finset.univ.filter fun l => ¬ Pad l))
    (fun i => LD * lam (i.val + 1) < lam i.val) hclass
  have hdropeq : ((Finset.univ : Finset (Fin J)).filter
      (fun i => LD * lam (i.val + 1) < lam i.val)).card = aux_lem_finite_stopping_partition_dropCount lam LD J :=
    aux_lem_finite_stopping_partition_card_filter_fin_eq_range J (fun s => LD * lam (s + 1) < lam s)
  omega

/-- Monotonicity and the positive volume floor for the literal regularized measure. -/
theorem aux_density_stopping_measure_properties
    (d m : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (nu : Measure (SpatialCoordinates d)) [IsFiniteMeasure nu] (c : ℝ) (hc : 0 < c) :
    let mu := nu + ENNReal.ofReal c • volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))
    let mass := fun n w => mu.real (descendantCell m z hr n w : Set (SpatialCoordinates d))
    IsFiniteMeasure mu ∧
    (∀ n (w : Fin (n + 1) → OddGridIndex d m), mass (n + 1) w ≤ mass n (fun i => w i.castSucc)) ∧
    (∀ n (w : Fin n → OddGridIndex d m), c * (descendantSide m n r) ^ d ≤ mass n w) := by
  intro mu mass
  have hvolQ : volume (centeredCube z r hr : Set (SpatialCoordinates d)) ≠ ⊤ := by
    rw [centeredCube_volume]
    exact ENNReal.ofReal_ne_top
  letI : IsFiniteMeasure (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    ⟨by simpa using hvolQ.lt_top⟩
  haveI : IsFiniteMeasure (ENNReal.ofReal c • volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  haveI : IsFiniteMeasure mu := inferInstanceAs (IsFiniteMeasure
    (nu + ENNReal.ofReal c • volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
  have hmono : ∀ n (w : Fin (n + 1) → OddGridIndex d m),
      mass (n + 1) w ≤ mass n (fun i => w i.castSucc) := by
    intro n w
    refine measureReal_mono ?_ (measure_ne_top mu _)
    exact aux_lem_finite_stopping_partition_descendantCell_subset_prefix m z hr
      (n + 1) w n (Nat.le_succ n)
  have hfloor : ∀ n (w : Fin n → OddGridIndex d m), c * (descendantSide m n r) ^ d ≤ mass n w := by
    intro n w
    have hsub := aux_lem_finite_stopping_partition_descendantCell_subset_root m z hr n w
    have hmeas := (descendantCell m z hr n w).isOpen.measurableSet
    change _ ≤ (mu _).toReal
    have heq : (ENNReal.ofReal c • volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))
        (descendantCell m z hr n w : Set (SpatialCoordinates d)) =
        ENNReal.ofReal c * ENNReal.ofReal ((descendantSide m n r) ^ d) := by
      rw [Measure.smul_apply, Measure.restrict_apply hmeas, Set.inter_eq_left.mpr hsub]
      change _ * volume _ = _
      rw [show (descendantCell m z hr n w) = centeredCube (descendantCenter m z r n w) (descendantSide m n r) (descendantSide_pos m n hr) from rfl, centeredCube_volume]
    have hle : ENNReal.ofReal c * ENNReal.ofReal ((descendantSide m n r) ^ d) ≤
        mu (descendantCell m z hr n w : Set (SpatialCoordinates d)) := by
      rw [← heq]
      change _ ≤ nu _ + _
      exact le_add_of_nonneg_left (zero_le _)
    have ht := ENNReal.toReal_mono (measure_ne_top mu _) hle
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le,
      ENNReal.toReal_ofReal (pow_nonneg (descendantSide_pos m n hr).le d)] using ht
  exact ⟨inferInstance, hmono, hfloor⟩

/-- All leaves of any finite stopping rule have total mass at most the root. -/
theorem aux_density_stopping_measure_sum
    (d m : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (mu : Measure (SpatialCoordinates d)) [IsFiniteMeasure mu]
    (stop : (n : ℕ) → (Fin n → OddGridIndex d m) → Prop) (J : ℕ) :
    let leaves := aux_lem_finite_stopping_partition_leafFinset stop J
    (∑ p ∈ leaves, mu.real (descendantCell m z hr p.1 p.2 : Set (SpatialCoordinates d))) ≤
      mu.real (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  intro leaves
  have hdisj : Set.PairwiseDisjoint (leaves : Set (Σ n : Fin (J + 1), Fin n → OddGridIndex d m))
      (fun p => (descendantCell m z hr p.1 p.2 : Set (SpatialCoordinates d))) := by
    intro p hp q hq hpq
    apply aux_lem_finite_stopping_partition_leaf_cells_disjoint z hr stop J
      ((aux_lem_finite_stopping_partition_mem_leafFinset stop J p).mp hp)
      ((aux_lem_finite_stopping_partition_mem_leafFinset stop J q).mp hq)
    intro heq
    apply hpq
    rcases p with ⟨⟨a, ha⟩, u⟩
    rcases q with ⟨⟨b, hb⟩, v⟩
    simp only [Sigma.mk.inj_iff] at heq
    obtain ⟨rfl, h⟩ := heq
    obtain rfl := eq_of_heq h
    rfl
  rw [← measureReal_biUnion_finset hdisj
    (fun p _ => (descendantCell m z hr p.1 p.2).isOpen.measurableSet)]
  refine measureReal_mono ?_ (measure_ne_top mu _)
  exact Set.iUnion₂_subset fun p _ =>
    aux_lem_finite_stopping_partition_descendantCell_subset_root m z hr p.1 p.2

/-- Finite stopping for the regularized limit measure. The stopping rule uses
actual descendant cubes and their measure, and the residual family is the
literal set of leaves that have not stopped by depth J. -/
theorem density_stopping_measure
    (d m : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (nu : Measure (SpatialCoordinates d)) [IsFiniteMeasure nu]
    (c LD : ℝ) (hc : 0 < c) (hLD : 1 < LD)
    (Sel : ℕ → Prop) (Good : (n : ℕ) → (Fin n → OddGridIndex d m) → Prop)
    (Pad : OddGridIndex d m → Prop) (J nsel nbad g : ℕ)
    (hbad : ∀ w : Fin J → OddGridIndex d m,
      ((Finset.univ : Finset (Fin J)).filter fun i =>
        ¬ Good (i.val + 1) (aux_lem_finite_stopping_partition_wordPrefix w (i.val + 1) i.isLt)).card ≤ nbad)
    (hsel : nsel ≤ ((Finset.univ : Finset (Fin J)).filter fun i => Sel (i.val + 1)).card) :
    let mu := nu + ENNReal.ofReal c • volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))
    let mass := fun n w => mu.real (descendantCell m z hr n w : Set (SpatialCoordinates d))
    let stop := aux_lem_finite_stopping_partition_stopRule Sel Good Pad mass LD
    let leaves := aux_lem_finite_stopping_partition_leafFinset stop J
    mu.real (centeredCube z r hr : Set (SpatialCoordinates d)) <
      LD ^ (g + 1) * (c * (descendantSide m J r) ^ d) →
    ((leaves.filter (fun p => ¬ stop p.1 p.2)).card ≤
      2 ^ J * (Finset.univ.filter fun l => ¬ Pad l).card ^ (nsel - nbad - g) *
        ((2 * m + 1) ^ d) ^ (J - (nsel - nbad - g))) ∧
    (∑ p ∈ leaves, mass p.1 p.2) ≤ mu.real (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  classical
  intro mu mass stop leaves hmass
  obtain ⟨hfinite, hmono, hfloor⟩ := aux_density_stopping_measure_properties d m z r hr nu c hc
  letI : IsFiniteMeasure mu := hfinite
  constructor
  · let T := nsel - nbad - g
    let NP := (Finset.univ.filter fun l : OddGridIndex d m => ¬ Pad l)
    let Hs := (Finset.univ : Finset (Fin J → OddGridIndex d m)).filter
      (fun w => T ≤ ((Finset.univ : Finset (Fin J)).filter fun i => w i ∈ NP).card)
    let inject : (Fin J → OddGridIndex d m) → Σ n : Fin (J + 1), Fin n → OddGridIndex d m :=
      fun w => ⟨⟨J, Nat.lt_succ_self J⟩, w⟩
    have hsub : leaves.filter (fun p => ¬ stop p.1 p.2) ⊆ Hs.image inject := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hp, hnstop⟩
      have hleaf := (aux_lem_finite_stopping_partition_mem_leafFinset stop J p).mp hp
      rcases p with ⟨⟨s, hs⟩, w⟩
      have hsJ : s = J := hleaf.2.1.resolve_left hnstop
      subst s
      apply Finset.mem_image.mpr
      refine ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      apply aux_density_stopping_measure_hits d m J mass Sel Good Pad LD
        (c * (descendantSide m J r) ^ d) hLD (mul_pos hc (pow_pos (descendantSide_pos m J hr) d))
        hmono nsel nbad g w
      · intro k hk
        rcases lt_or_eq_of_le hk with hlt | rfl
        · exact hleaf.2.2 k hlt
        · simpa only [aux_lem_finite_stopping_partition_wordPrefix_self] using hnstop
      · exact hbad w
      · exact hsel
      · exact hfloor J w
      · apply lt_of_le_of_lt (measureReal_mono
          (aux_lem_finite_stopping_partition_descendantCell_subset_root m z hr 0 _)) hmass
    calc (leaves.filter _).card ≤ (Hs.image inject).card := Finset.card_le_card hsub
      _ ≤ Hs.card := Finset.card_image_le
      _ ≤ _ := by
        simpa [Fintype.card_fun, Fintype.card_fin] using
          aux_lem_finite_stopping_partition_card_many_hits_le J T NP
  · exact aux_density_stopping_measure_sum d m z r hr mu stop J

end Paper
