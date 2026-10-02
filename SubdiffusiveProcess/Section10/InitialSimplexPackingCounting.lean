import SubdiffusiveProcess.Section10.InitialSimplexPackingGeometryOrder

/-! Finite grid counting for the coordinate-order facets. -/

namespace SubdiffusiveProcess.Section10

open Homogenization Homogenization.Book MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

private def equalCoordinateFunctionEquiv {α β : Type*} [DecidableEq α]
    (a b : α) (hab : a ≠ b) :
    {f : α → β // f a = f b} ≃ ({j : α // j ≠ a} → β) where
  toFun f := fun j => f.1 j.1
  invFun g := ⟨fun j => if h : j = a then g ⟨b, hab.symm⟩ else g ⟨j, h⟩,
    by simp [hab.symm]⟩
  left_inv f := by
    ext j
    by_cases h : j = a
    · subst j
      simp [f.2]
    · simp [h]
  right_inv g := by
    funext j
    simp [j.2]

theorem card_digits_equal_coordinates (a b : Fin d) (hab : a ≠ b) :
    ((Finset.univ : Finset (Fin d → Fin 3)).filter
      (fun digits => digits a = digits b)).card = 3 ^ (d - 1) := by
  classical
  rw [← Fintype.card_subtype (fun digits : Fin d → Fin 3 => digits a = digits b)]
  have hcard := Fintype.card_congr (equalCoordinateFunctionEquiv a b hab (β := Fin 3))
  rw [Fintype.card_fun] at hcard
  have hcompl : Fintype.card {j : Fin d // j ≠ a} = d - 1 := by
    have h := Fintype.card_subtype_compl (fun j : Fin d => j = a)
    simp [Fintype.card_fin] at h ⊢
  simpa [Fintype.card_fin, hcompl] using hcard

theorem childCubes_equal_indices_card (P : TriadicCube d) (a b : Fin d)
    (hab : a ≠ b) (hP : P.index a = P.index b) :
    ((childCubes P).filter (fun Q => Q.index a = Q.index b)).card = 3 ^ (d - 1) := by
  classical
  let childOf : (Fin d → Fin 3) → TriadicCube d := fun digits =>
    {scale := P.scale - 1, index := fun k => 3 * P.index k + (digits k : ℤ) - 1}
  have hinj : Function.Injective childOf := by
    intro v w h
    funext k
    apply Fin.ext
    have hindex := congrArg (fun Q : TriadicCube d => Q.index k) h
    change 3 * P.index k + (v k : ℤ) - 1 = 3 * P.index k + (w k : ℤ) - 1 at hindex
    have hcast : (v k : ℤ) = (w k : ℤ) := by omega
    exact Int.ofNat_inj.mp (by simpa using hcast)
  have hfilter : (childCubes P).filter (fun Q => Q.index a = Q.index b) =
      ((Finset.univ : Finset (Fin d → Fin 3)).filter
        (fun digits => digits a = digits b)).image childOf := by
    unfold childCubes
    rw [Finset.filter_image]
    apply congrArg (Finset.image childOf)
    ext digits
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change 3 * P.index a + (digits a : ℤ) - 1 =
      3 * P.index b + (digits b : ℤ) - 1 ↔ digits a = digits b
    rw [hP]
    constructor
    · intro h
      apply Fin.ext
      have hcast : (digits a : ℤ) = (digits b : ℤ) := by omega
      exact Int.ofNat_inj.mp (by simpa using hcast)
    · intro h
      rw [h]
  rw [hfilter, Finset.card_image_of_injective _ hinj]
  exact card_digits_equal_coordinates a b hab

def equalIndexDescendants (R : TriadicCube d) (n : ℕ) (a b : Fin d) :
    Finset (TriadicCube d) :=
  (descendantsAtDepth R n).filter fun Q => Q.index a = Q.index b

theorem equalIndexDescendants_succ_subset (R : TriadicCube d) (n : ℕ) (a b : Fin d) :
    equalIndexDescendants R (n + 1) a b ⊆
      (equalIndexDescendants R n a b).biUnion
        (fun P => (childCubes P).filter (fun Q => Q.index a = Q.index b)) := by
  classical
  intro Q hQ
  obtain ⟨hQR, heq⟩ := Finset.mem_filter.mp hQ
  obtain ⟨hPR, hQC⟩ := parent_mem_of_mem_descendants_succ hQR
  have hparent : (parentCube Q).index a = (parentCube Q).index b := by
    change (Q.index a + 1) / 3 = (Q.index b + 1) / 3
    rw [heq]
  exact Finset.mem_biUnion.mpr ⟨parentCube Q, Finset.mem_filter.mpr ⟨hPR, hparent⟩,
    Finset.mem_filter.mpr ⟨hQC, heq⟩⟩

/-- Each equality facet has at most 3^((d-1)n) grid cubes at depth n. -/
theorem equalIndexDescendants_card_le (R : TriadicCube d) (n : ℕ)
    (a b : Fin d) (hab : a ≠ b) :
    (equalIndexDescendants R n a b).card ≤ (3 ^ (d - 1)) ^ n := by
  classical
  induction n with
  | zero =>
    simpa [equalIndexDescendants] using
      Finset.card_filter_le ({R} : Finset (TriadicCube d)) (fun Q => Q.index a = Q.index b)
  | succ n ih =>
    calc
      _ ≤ ((equalIndexDescendants R n a b).biUnion
        (fun P => (childCubes P).filter (fun Q => Q.index a = Q.index b))).card :=
          Finset.card_le_card (equalIndexDescendants_succ_subset R n a b)
      _ ≤ ∑ P ∈ equalIndexDescendants R n a b,
          ((childCubes P).filter (fun Q => Q.index a = Q.index b)).card :=
        Finset.card_biUnion_le
      _ = (equalIndexDescendants R n a b).card * 3 ^ (d - 1) := by
        calc
          _ = ∑ P ∈ equalIndexDescendants R n a b, 3 ^ (d - 1) := by
            apply Finset.sum_congr rfl
            intro P hP
            exact childCubes_equal_indices_card P a b hab (Finset.mem_filter.mp hP).2
          _ = _ := by simp
      _ ≤ (3 ^ (d - 1)) ^ n * 3 ^ (d - 1) := Nat.mul_le_mul_right _ ih
      _ = _ := (pow_succ _ _).symm

def simplexFacetPairs (d : ℕ) : Finset (Fin d × Fin d) :=
  Finset.univ.filter fun p => p.1.val < p.2.val

theorem initialSimplexUnresolved_card_le (ell n : ℕ) (pi : Equiv.Perm (Fin d)) :
    (initialSimplexUnresolved ell pi n).card ≤ d ^ 2 * (3 ^ (d - 1)) ^ n := by
  classical
  have hsub : initialSimplexUnresolved ell pi n ⊆
      (simplexFacetPairs d).biUnion (fun p =>
        equalIndexDescendants (originCube d (ell : ℤ)) n (pi p.1) (pi p.2)) := by
    intro Q hQ
    obtain ⟨i, j, hij, heq⟩ := unresolved_initialSimplex_has_equal_indices hQ
    exact Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩,
      Finset.mem_filter.mpr ⟨(mem_unresolvedAtDepth.mp hQ).1, heq⟩⟩
  calc
    _ ≤ ((simplexFacetPairs d).biUnion (fun p =>
      equalIndexDescendants (originCube d (ell : ℤ)) n (pi p.1) (pi p.2))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ p ∈ simplexFacetPairs d,
        (equalIndexDescendants (originCube d (ell : ℤ)) n (pi p.1) (pi p.2)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ simplexFacetPairs d, (3 ^ (d - 1)) ^ n := by
      apply Finset.sum_le_sum
      intro p hp
      apply equalIndexDescendants_card_le
      apply pi.injective.ne
      have hij : p.1.val < p.2.val := (Finset.mem_filter.mp hp).2
      intro heq
      have := congrArg Fin.val heq
      omega
    _ = (simplexFacetPairs d).card * (3 ^ (d - 1)) ^ n := by simp
    _ ≤ d ^ 2 * (3 ^ (d - 1)) ^ n := by
      apply Nat.mul_le_mul_right
      have h := Finset.card_filter_le (Finset.univ : Finset (Fin d × Fin d))
        (fun p => p.1.val < p.2.val)
      simpa [simplexFacetPairs, Fintype.card_prod, pow_two] using h

theorem initialSimplexPacking_atDepth_card_le (ell : ℕ) (pi : Equiv.Perm (Fin d))
    (i : ℕ) (hi : 0 < i) :
    (maximalContainedAtDepth (originCube d (ell : ℤ))
      (initialSimplex ell pi).openCarrier i).card ≤
        3 ^ d * d ^ 2 * (3 ^ (d - 1)) ^ i := by
  have heq : i = (i - 1) + 1 := by omega
  have h := maximalContainedAtDepth_card_le (originCube d (ell : ℤ))
    (initialSimplex ell pi).openCarrier (i - 1)
  rw [← heq] at h
  have hp : (3 ^ (d - 1)) ^ (i - 1) ≤ (3 ^ (d - 1)) ^ i := by
    exact pow_le_pow_right₀ (one_le_pow₀ (by decide : (1 : ℕ) ≤ 3)) (by omega)
  calc
    _ ≤ (initialSimplexUnresolved ell pi (i - 1)).card * 3 ^ d := h
    _ ≤ (d ^ 2 * (3 ^ (d - 1)) ^ (i - 1)) * 3 ^ d :=
      Nat.mul_le_mul_right _ (initialSimplexUnresolved_card_le ell (i - 1) pi)
    _ ≤ (d ^ 2 * (3 ^ (d - 1)) ^ i) * 3 ^ d := by gcongr
    _ = _ := by ring

end
end SubdiffusiveProcess.Section10
