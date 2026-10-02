import Mathlib
import SubdiffusiveProcess.Geometry.RationalTriadicCatalogue

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- **Catalogue geometry (clause C of `conv_represented_estimates`, with rational grid origins).**  Let
`(Z i, R i)` be a countable family of rational-centred cubes with triadic sides that contains EVERY such cube.
For every `k` there is a root cube `(Z (e root), R (e root))` centred at a point of the family with
triadic side, containing the unit cube and the first `k+1` cubes of the family, and an enumeration `e` of
exactly the family cubes inside it, such that: all `Z (e j)` are rational and all `R (e j)` triadic, every
rational-centred triadic cube inside the root occurs as some `(Z (e j), R (e j))`, and there is a countable grid
family `(origin g, gridRoot g)` with rational origins in which EVERY catalogue cube `j` is the root of a grid at
EVERY rational origin (in particular at its own centre). -/
theorem conv_represented_catalogue_geometry (d : ℕ) (Z : ℕ → SpatialCoordinates d) (R : ℕ → ℝ)
    (hR : ∀ i, 0 < R i)
    (hrat : ∀ i, (∀ c : Fin d, ∃ q : ℚ, Z i c = (q : ℝ)) ∧ ∃ k : ℤ, R i = (3 : ℝ) ^ k)
    (hcomp : ∀ (z' : SpatialCoordinates d) (r' : ℝ), (∀ c : Fin d, ∃ q : ℚ, z' c = (q : ℝ)) →
      (∃ k : ℤ, r' = (3 : ℝ) ^ k) → ∃ i, Z i = z' ∧ R i = r')
    (k : ℕ) :
    ∃ (e : ℕ → ℕ) (root : ℕ) (origin : ℕ → SpatialCoordinates d) (gridRoot : ℕ → ℕ),
      (∀ i ≤ k, ∃ j, e j = i) ∧
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) ⊆
        (centeredCube (Z (e root)) (R (e root)) (hR (e root)) : Set (SpatialCoordinates d)) ∧
      (∀ j, (centeredCube (Z (e j)) (R (e j)) (hR (e j)) : Set (SpatialCoordinates d)) ⊆
        (centeredCube (Z (e root)) (R (e root)) (hR (e root)) : Set (SpatialCoordinates d))) ∧
      (∀ (j : ℕ) (c : Fin d), ∃ q : ℚ, Z (e j) c = (q : ℝ)) ∧
      (∀ j, ∃ m : ℤ, R (e j) = (3 : ℝ) ^ m) ∧
      (∀ (z' : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r'),
        (∀ c : Fin d, ∃ q : ℚ, z' c = (q : ℝ)) → (∃ m : ℤ, r' = (3 : ℝ) ^ m) →
        (centeredCube z' r' hr' : Set (SpatialCoordinates d)) ⊆
          (centeredCube (Z (e root)) (R (e root)) (hR (e root)) : Set (SpatialCoordinates d)) →
        ∃ j, Z (e j) = z' ∧ R (e j) = r') ∧
      (∀ (g : ℕ) (c : Fin d), ∃ q : ℚ, origin g c = (q : ℝ)) ∧
      (∀ (j : ℕ) (o : SpatialCoordinates d), (∀ c : Fin d, ∃ q : ℚ, o c = (q : ℝ)) →
        ∃ g : ℕ, gridRoot g = j ∧ origin g = o) := by
  classical
  have hcube : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      (centeredCube z r hr : Set (SpatialCoordinates d)) = Metric.ball z (r / 2) :=
    fun _ _ _ => rfl
  obtain ⟨m, hm⟩ := exists_triadic_root_for_prefix Z R hR k
  obtain ⟨i0, hi0z, hi0r⟩ := hcomp 0 ((3 : ℝ) ^ m) (fun c => ⟨0, by simp⟩)
    ⟨(m : ℤ), by simp⟩
  let A : Set ℕ := {i | (centeredCube (Z i) (R i) (hR i) : Set (SpatialCoordinates d)) ⊆
    (centeredCube (Z i0) (R i0) (hR i0) : Set (SpatialCoordinates d))}
  have hA0 : i0 ∈ A := fun x hx => hx
  have hAk : ∀ i ≤ k, i ∈ A := by
    intro i hi
    have h1 := (subset_closure).trans (hm i hi)
    intro x hx
    have := h1 hx
    rw [hcube] at this ⊢
    rw [hi0z, hi0r]
    exact this
  haveI : Nonempty A := ⟨⟨i0, hA0⟩⟩
  obtain ⟨f, hf⟩ := exists_surjective_nat A
  let e : ℕ → ℕ := fun n => (f n).1
  obtain ⟨root, hroot⟩ := hf ⟨i0, hA0⟩
  have heroot : e root = i0 := congrArg Subtype.val hroot
  have hrootcube : ∀ p : ℕ, p = i0 →
      (centeredCube (Z p) (R p) (hR p) : Set (SpatialCoordinates d)) =
        (centeredCube (Z i0) (R i0) (hR i0) : Set (SpatialCoordinates d)) := by
    intro p hp; subst hp; rfl
  have hrc := hrootcube (e root) heroot
  -- grid family: a surjection from `ℕ` onto catalogue indices × rational origins
  obtain ⟨σ, hσ⟩ := exists_surjective_nat (ℕ × (Fin d → ℚ))
  refine ⟨e, root, fun g c => ((σ g).2 c : ℝ), fun g => (σ g).1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨n, hn⟩ := hf ⟨i, hAk i hi⟩
    exact ⟨n, congrArg Subtype.val hn⟩
  · have hcubeR : (centeredCube (Z i0) (R i0) (hR i0) : Set (SpatialCoordinates d)) =
        Metric.ball (0 : SpatialCoordinates d) ((3 : ℝ) ^ m / 2) := by
      rw [hcube, hi0z, hi0r]
    rw [hrc, hcubeR]
    intro x hx
    rw [hcube] at hx
    have hx' : dist x 0 < 1 / 2 := hx
    have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ m := one_le_pow₀ (by norm_num)
    change dist x 0 < (3 : ℝ) ^ m / 2
    linarith
  · intro j
    rw [hrc]
    exact (f j).2
  · intro j c
    exact (hrat (e j)).1 c
  · intro j
    exact (hrat (e j)).2
  · intro z' r' hr' hz' hr'' hsub
    rw [hrc] at hsub
    obtain ⟨i, hiz, hir⟩ := hcomp z' r' hz' hr''
    have hiA : i ∈ A := by
      intro x hx
      apply hsub
      have h1 : (centeredCube (Z i) (R i) (hR i) : Set (SpatialCoordinates d)) =
          (centeredCube z' r' hr' : Set (SpatialCoordinates d)) := by
        rw [hcube, hcube, hiz, hir]
      rw [← h1]
      exact hx
    obtain ⟨n, hn⟩ := hf ⟨i, hiA⟩
    have hne : e n = i := congrArg Subtype.val hn
    exact ⟨n, by rw [hne]; exact hiz, by rw [hne]; exact hir⟩
  · intro g c
    exact ⟨(σ g).2 c, rfl⟩
  · intro j o ho
    choose q hq using ho
    obtain ⟨g, hg⟩ := hσ (j, q)
    refine ⟨g, by show (σ g).1 = j; rw [hg], ?_⟩
    funext c
    show (((σ g).2 c : ℚ) : ℝ) = o c
    rw [hg]
    exact (hq c).symm

end Paper
