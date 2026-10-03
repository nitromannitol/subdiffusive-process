module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.WindowGeometry
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.AnchorInterior

@[expose] public section

/-!
# Geometry of a projected cell in the non-touching regime

When the ambient scale-`n` window does not touch the domain boundary, its full
translated cube lies in the domain.  Hence every descendant centre's
scale-`n-3` patch is interior, and the projected origin-frame patch lies inside
the projected cube.  This is the geometry consumed by interior Caccioppoli.

PROVENANCE: mirrors `CaccioppoliInteriorGeometry.lean` in Algsuperdiff and
reuses GMC's already-proved exact interior/boundary dichotomy.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03

noncomputable section

variable {d : ℕ}

/-- In the complement of the frozen boundary-touching event, the full window
cube is contained in the ambient domain cube. -/
theorem translatedCube_subset_domain_of_not_boundaryTouches
    {m n : ℤ} {x : Vec d} (hx : x ∈ cube d m)
    (hnot : ¬ BoundaryTouches (truncatedCube d m n x) (cube d m)) :
    translatedCube d n x ⊆ cube d m := by
  by_contra hsub
  exact hnot (Section6ExcessDecay.boundaryTouches_of_not_translatedCube_subset
    hx (le_refl n) hsub)

/-- A scale-`n-3` patch around a point of `U_(m,n-1)(x)` stays inside the full
scale-`n` cube centred at `x`. -/
theorem openCubeAtScale_predTwo_subset_translatedCube_next
    {m n : ℤ} {x q : Vec d}
    (hq : q ∈ truncatedCube d m (n - 1) x) :
    openCubeAtScale q (n - 3) ⊆ translatedCube d n x := by
  intro p hp
  have hqx := Section6ExcessDecay.sub_mem_cube_of_mem_truncatedCube hq
  rw [cube, mem_openCubeSet_originCube_iff] at hqx
  rw [Section6ExcessDecay.mem_translatedCube_iff, cube,
    mem_openCubeSet_originCube_iff]
  intro i
  have hpq := hp i
  change |p i - q i| < Real.rpow 3 (((n - 3 : ℤ) : ℝ)) / 2 at hpq
  have hrpow : Real.rpow (3 : ℝ) (((n - 3 : ℤ) : ℝ)) =
      (3 : ℝ) ^ (n - 3) := Real.rpow_intCast 3 (n - 3)
  rw [hrpow] at hpq
  have hbase : (0 : ℝ) < (3 : ℝ) ^ (n - 3) := zpow_pos (by norm_num) _
  have h1 : (3 : ℝ) ^ (n - 1) = 9 * (3 : ℝ) ^ (n - 3) := by
    rw [show n - 1 = (n - 3) + 2 by ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
    ring
  have h2 : (3 : ℝ) ^ n = 27 * (3 : ℝ) ^ (n - 3) := by
    rw [show n = (n - 3) + 3 by ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
    ring
  have hpq' := abs_lt.mp hpq
  have hqi := hqx i
  simp only [Pi.sub_apply] at hqi ⊢
  rw [h1] at hqi
  have hid : p i - x i = (p i - q i) + (q i - x i) := by ring
  rw [hid, h2]
  constructor <;> linarith only [hpq'.1, hpq'.2, hqi.1, hqi.2, hbase]

/-- The preceding patch is an interior patch whenever the ambient truncated
window does not touch the domain boundary. -/
theorem openCubeAtScale_predTwo_subset_domain_of_not_boundaryTouches
    {m n : ℤ} {x q : Vec d} (hx : x ∈ cube d m)
    (hq : q ∈ truncatedCube d m (n - 1) x)
    (hnot : ¬ BoundaryTouches (truncatedCube d m n x) (cube d m)) :
    openCubeAtScale q (n - 3) ⊆ cube d m :=
  (openCubeAtScale_predTwo_subset_translatedCube_next hq).trans
    (translatedCube_subset_domain_of_not_boundaryTouches hx hnot)

/-- Pulling an interior physical patch back by the well-placed centre gives
the patch inclusion required by interior Caccioppoli on the origin cube. -/
theorem openCubeAtScale_wellPlaced_pullback_subset_originCube
    {m k : ℤ} {q : Vec d} (hkm : k ≤ m)
    (hpatch : openCubeAtScale q (k - 1) ⊆ cube d m) :
    openCubeAtScale
        (q - Section6ExcessDecay.wellPlacedCentre q m k) (k - 1) ⊆
      openCubeSet (originCube d k) := by
  let c := Section6ExcessDecay.wellPlacedCentre q m k
  intro p hp
  have hphysical : p + c ∈ openCubeAtScale q (k - 1) := by
    intro i
    have hi := hp i
    change |(p + c) i - q i| < Real.rpow 3 (((k - 1 : ℤ) : ℝ)) / 2
    change |p i - (q - Section6ExcessDecay.wellPlacedCentre q m k) i| < _ at hi
    rw [show (p + c) i - q i =
      p i - (q - Section6ExcessDecay.wellPlacedCentre q m k) i by
        simp only [Pi.add_apply, Pi.sub_apply, c]
        ring]
    exact hi
  have htrunc : p + c ∈ truncatedCube d m (k - 1) q := by
    refine ⟨?_, hpatch hphysical⟩
    rw [Section6ExcessDecay.mem_translatedCube_iff, cube,
      mem_openCubeSet_originCube_iff]
    intro i
    have hi := hphysical i
    change |(p + c) i - q i| < Real.rpow 3 (((k - 1 : ℤ) : ℝ)) / 2 at hi
    have hrpow : Real.rpow (3 : ℝ) (((k - 1 : ℤ) : ℝ)) =
        (3 : ℝ) ^ (k - 1) := Real.rpow_intCast 3 (k - 1)
    rw [hrpow] at hi
    rw [abs_lt] at hi
    simp only [Pi.sub_apply]
    exact ⟨by linarith only [hi.1], by linarith only [hi.2]⟩
  have hwell := Section6ExcessDecay.truncatedCube_subset_translatedCube_wellPlacedCentre
    q hkm (by omega : k - 1 ≤ k) htrunc
  rw [Section6ExcessDecay.mem_translatedCube_iff] at hwell
  simpa only [c, add_sub_cancel_right] using! hwell

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
