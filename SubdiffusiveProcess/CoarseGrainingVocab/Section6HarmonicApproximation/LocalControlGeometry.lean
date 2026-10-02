import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.Windows
import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability.OffGridStabilityGeometry

/-!
# Geometry for harmonic-approximation local control

The printed placement `x ∈ U_{m,n-3}(z)` and
`y + □_{n-2} ⊆ U_{m,n-1}(x)` puts the whole comparison cube inside
`z + □_{n+2}`.  This is the containment used by off-grid stability.

PROVENANCE: mirrors `Algsuperdiff/Section4/Provider/ExcessDecay/
InteriorGlueWindow.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

variable {d : ℕ}

theorem translatedCube_subset_anchorParent {m n : ℤ} {x y z : Vec d}
    (hx : x ∈ truncatedCube d m (n - 3) z)
    (hD : translatedCube d (n - 2) y ⊆ truncatedCube d m (n - 1) x) :
    translatedCube d (n - 2) y ⊆ translatedCube d (n + 2) z := by
  intro p hp
  have hpx : p - x ∈ cube d (n - 1) :=
    sub_mem_cube_of_mem_truncatedCube (hD hp)
  have hxz : x - z ∈ cube d (n - 3) :=
    sub_mem_cube_of_mem_truncatedCube hx
  rw [cube, Homogenization.mem_openCubeSet_originCube_iff] at hpx hxz
  rw [mem_translatedCube_iff, cube,
    Homogenization.mem_openCubeSet_originCube_iff]
  intro i
  have hbase : (0 : ℝ) < (3 : ℝ) ^ (n - 3) := zpow_pos (by norm_num) _
  have h1 : (3 : ℝ) ^ (n - 1) = 9 * (3 : ℝ) ^ (n - 3) := by
    rw [show n - 1 = (n - 3) + 2 by ring, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
    ring
  have h2 : (3 : ℝ) ^ (n + 2) = 243 * (3 : ℝ) ^ (n - 3) := by
    rw [show n + 2 = (n - 3) + 5 by ring, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
    ring
  have hid : p i - z i = (p i - x i) + (x i - z i) := by ring
  simp only [Pi.sub_apply] at hpx hxz ⊢
  rw [h1] at hpx
  rw [hid, h2]
  constructor <;> linarith only [(hpx i).1, (hpx i).2, (hxz i).1, (hxz i).2, hbase]

/-- Recenter the preceding containment into the off-grid stability frame. -/
theorem offGridCube_subset_origin_anchorParent {m n : ℤ} {x y z : Vec d}
    (hx : x ∈ truncatedCube d m (n - 3) z)
    (hD : translatedCube d (n - 2) y ⊆ truncatedCube d m (n - 1) x) :
    SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport.offGridCube
        (y - z) (Homogenization.originCube d (n - 2)) ⊆
      Homogenization.cubeSet (Homogenization.originCube d (n + 2)) := by
  intro p hp
  have hp' : z + p ∈ translatedCube d (n - 2) y := by
    rw [mem_translatedCube_iff]
    have hp0 : p - (y - z) ∈ cube d (n - 2) := by
      exact Homogenization.mem_translateSet_iff_sub_mem.mp hp
    convert hp0 using 1
    ext i
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  have hz := translatedCube_subset_anchorParent hx hD hp'
  have hback : z + p - z = p := by abel
  rw [mem_translatedCube_iff, hback] at hz
  exact Homogenization.openCubeSet_subset_cubeSet _ hz

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
