module

public import Mathlib
public import SubdiffusiveProcess.Paper.conv_represented_root_family

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- **Catalogue geometry for a rooted family** (the single-root analogue of `conv_represented_catalogue_geometry`).
Let `(Z i, R i)` be a countable family of rational-centred cubes with triadic sides which is a rooted family
(`conv_represented_root_family`: root member `j0` containing the unit cube, all members inside it, every rational triadic
cube inside it occurring).  Then, for every `k`, the enumeration `e = id` and the root `j0` give the conclusion of
`conv_represented_catalogue_geometry`: `e` covers the first `k+1` cubes, all `Z (e j)` are rational and all `R (e j)` triadic,
every rational-centred triadic cube inside the root occurs, and there is a countable grid family `(origin g, gridRoot g)` with
rational origins in which EVERY catalogue cube `j` is the root of a grid at EVERY rational origin. -/
theorem conv_represented_catalogue_geometry_root (d : ℕ) (Z : ℕ → SpatialCoordinates d) (R : ℕ → ℝ)
    (hR : ∀ i, 0 < R i)
    (hrat : ∀ i, (∀ c : Fin d, ∃ q : ℚ, Z i c = (q : ℝ)) ∧ ∃ k : ℤ, R i = (3 : ℝ) ^ k)
    (hfam : conv_represented_root_family d Z R hR)
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
  obtain ⟨j0, hunit, hsub, hcomp⟩ := hfam
  obtain ⟨σ, hσ⟩ := exists_surjective_nat (ℕ × (Fin d → ℚ))
  refine ⟨fun n => n, j0, fun g c => ((σ g).2 c : ℝ), fun g => (σ g).1, fun i _ => ⟨i, rfl⟩,
    hunit, hsub, fun j c => (hrat j).1 c, fun j => (hrat j).2, hcomp, ?_, ?_⟩
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
