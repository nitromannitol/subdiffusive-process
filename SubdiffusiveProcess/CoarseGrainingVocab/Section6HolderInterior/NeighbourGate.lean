import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.EnergyCoverGate

/-!
# The cell-interiority gate at a grid neighbour

`WindowMonotone.interiorGate_of_descendant` needs the centre to sit *inside* a
window of the interior base point.  A grid neighbour `y` of `x` sits at
sup-distance up to `3^n`, hence on the boundary of the scale-`n` window and not
inside it, so that lemma does not apply.

The geometry nevertheless holds with room to spare, and a direct distance
estimate is the cleanest way to see it: from `x ∈ cube d (m-1)` and
`n ≤ m - 5`, a cell of a neighbour reaches at most

```text
  3^{m-1}/2 + 2·3^n + 3^{n-3}/2  ≤  3^{m-1}(1/2 + 1/81·(2 + 1/54))  <  3^m/2 ,
```

so it stays in the domain by a wide margin.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- **A cell near an interior point stays in the domain.** -/
theorem openCubeAtScale_subset_cube_of_dist {m n : ℤ} {x q : Vec d}
    (hx : x ∈ cube d (m - 1)) (hn : n ≤ m - 5)
    (hdist : ∀ i : Fin d, |x i - q i| ≤ 2 * (3 : ℝ) ^ n) :
    openCubeAtScale q (n - 3) ⊆ cube d m := by
  intro p hp
  rw [cube, mem_openCubeSet_originCube_iff]
  intro i
  have hpq := hp i
  change |p i - q i| < Real.rpow 3 (((n - 3 : ℤ) : ℝ)) / 2 at hpq
  have hrpow : Real.rpow (3 : ℝ) (((n - 3 : ℤ) : ℝ)) = (3 : ℝ) ^ (n - 3) :=
    Real.rpow_intCast 3 (n - 3)
  rw [hrpow] at hpq
  have hxi := (mem_openCubeSet_originCube_iff.mp
    (by rw [cube] at hx; exact hx)) i
  have hbase : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  -- rewrite the three scales against `3^n`
  have h3 : (3 : ℝ) ^ (n - 3) = (3 : ℝ) ^ n / 27 := by
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
  have hm1 : (3 : ℝ) ^ (m - 1) = (3 : ℝ) ^ m / 3 := by
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
  have hnm : (3 : ℝ) ^ n ≤ (3 : ℝ) ^ (m - 5) :=
    zpow_le_zpow_right₀ (by norm_num) hn
  have hm5 : (3 : ℝ) ^ (m - 5) = (3 : ℝ) ^ m / 243 := by
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
  have hmpos : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hdi := abs_le.mp (hdist i)
  have hpqi := abs_lt.mp hpq
  rw [hm1] at hxi
  rw [h3] at hpqi
  rw [hm5] at hnm
  constructor <;> nlinarith [hxi.1, hxi.2, hdi.1, hdi.2, hpqi.1, hpqi.2, hnm,
    hbase, hmpos]

/-- **The Step-6 cell hypothesis at a grid neighbour.**  Every cell of the
neighbour's window stays in the domain. -/
theorem neighbour_cells_subset_cube {m n : ℤ} {x y : Vec d}
    (hx : x ∈ cube d (m - 1)) (hn : n ≤ m - 5)
    (hxy : ∀ i : Fin d, |x i - y i| ≤ (3 : ℝ) ^ n) :
    ∀ q, q ∈ truncatedCube d m (n - 1) y →
      openCubeAtScale q (n - 3) ⊆ cube d m := by
  intro q hq
  refine openCubeAtScale_subset_cube_of_dist hx hn ?_
  intro i
  have hyq : |y i - q i| ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ (n - 1) := by
    have hmem := (mem_openCubeSet_originCube_iff.mp
      (Section6ExcessDecay.mem_translatedCube_iff.mp hq.1)) i
    simp only [Pi.sub_apply] at hmem
    rw [abs_le]
    constructor <;> linarith [hmem.1, hmem.2]
  have hstep : (3 : ℝ) ^ (n - 1) = (3 : ℝ) ^ n / 3 := by
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
  have hbase : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have htri : |x i - q i| ≤ |x i - y i| + |y i - q i| :=
    abs_sub_le (x i) (y i) (q i)
  rw [hstep] at hyq
  linarith [htri, hxy i, hyq, hbase]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
