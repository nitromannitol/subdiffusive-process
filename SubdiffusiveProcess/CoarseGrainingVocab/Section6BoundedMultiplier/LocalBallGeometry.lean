module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.LocalRatioTail

@[expose] public section

/-!
# Uniform collared balls in the one-third mesh cover

The unit cubes used by the probability event are centred on a `1/3` mesh.
Consequently every point has a deterministic `1/6` collar inside one such
cube.  Combining that collar with the middle-half condition keeps a short
Euclidean ball inside both the selected unit cube and the ambient cube.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- A middle-half point and every point in a sufficiently short Euclidean
ball around it lie in one common clipped cover cell. -/
theorem exists_coverCell_euclideanBall_subset
    {m : ℤ} {z x : Vec d} {rho : ℝ}
    (hcollar : ‖x - z‖ ≤ (3 : ℝ) ^ m / 4)
    (hrho : 0 < rho) (hrhoMesh : rho ≤ (6 : ℝ)⁻¹)
    (hrhoAmbient : rho ≤ (3 : ℝ) ^ m / 4) :
    ∃ p ∈ shellCoverShifts d m,
      x ∈ boundedMultiplierCoverCell d m z p ∧
        euclideanBall x rho ⊆ boundedMultiplierCoverCell d m z p := by
  let u : Vec d := x - z
  let p : Fin d → ℤ := fun i ↦ round ((3 : ℝ) * u i)
  have hscale : 0 < (3 : ℝ) ^ m := zpow_pos (by norm_num) _
  have hu : u ∈ openCubeSet (originCube d m) := by
    rw [mem_openCubeSet_originCube_iff]
    intro i
    have hi : |u i| ≤ ‖u‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm u i
    have hub : |u i| ≤ (3 : ℝ) ^ m / 4 := hi.trans hcollar
    have hub' := abs_le.mp hub
    exact ⟨by nlinarith [hscale], by nlinarith [hscale]⟩
  have hpMem : p ∈ shellCoverShifts d m := by
    rw [shellCoverShifts, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have hui := (mem_openCubeSet_originCube_iff.mp hu) i
    have hround := abs_le.mp (abs_sub_round ((3 : ℝ) * u i))
    have hR1 : (1 : ℝ) ≤ (shellCoverRadius m : ℝ) := by
      exact_mod_cast Nat.one_le_pow (m + 1).toNat 3 (by norm_num)
    have hRpow : (3 : ℝ) ^ (m + 1) ≤ (shellCoverRadius m : ℝ) := by
      have hcast : ((shellCoverRadius m : ℕ) : ℝ) =
          (3 : ℝ) ^ (((m + 1).toNat : ℕ) : ℤ) := by
        rw [zpow_natCast, shellCoverRadius]
        norm_cast
      rw [hcast]
      exact zpow_le_zpow_right₀ (by norm_num) (Int.self_le_toNat _)
    have hthree : (3 : ℝ) * ((1 / 2 : ℝ) * (3 : ℝ) ^ m) =
        (1 / 2 : ℝ) * (3 : ℝ) ^ (m + 1) := by
      rw [zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
      ring
    constructor
    · have hlow : -((shellCoverRadius m : ℤ) : ℝ) ≤
          ((p i : ℤ) : ℝ) := by
        dsimp [p]
        push_cast
        nlinarith [hui.1, hui.2]
      exact_mod_cast hlow
    · have hhigh : ((p i : ℤ) : ℝ) ≤
          ((shellCoverRadius m : ℤ) : ℝ) := by
        dsimp [p]
        push_cast
        nlinarith [hui.1, hui.2]
      exact_mod_cast hhigh
  have hnear : ∀ i, |u i - shellCoverCenter (d := d) p i| ≤ (6 : ℝ)⁻¹ := by
    intro i
    have hround := abs_le.mp (abs_sub_round ((3 : ℝ) * u i))
    have hrw : u i - shellCoverCenter (d := d) p i =
        (3 : ℝ)⁻¹ * ((3 : ℝ) * u i - ((round ((3 : ℝ) * u i) : ℤ) : ℝ)) := by
      dsimp [p, shellCoverCenter]
      ring
    rw [hrw, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < (3 : ℝ)⁻¹)]
    have habs := abs_le.mpr hround
    nlinarith [habs,
      abs_nonneg ((3 : ℝ) * u i - ((round ((3 : ℝ) * u i) : ℤ) : ℝ))]
  have hxAmbient : x ∈ translatedCube d m z := by
    refine ⟨u, hu, ?_⟩
    dsimp [u]
    abel
  have hxUnit : x ∈ translatedCube d 0
      (z + physicalShellCoverCenter 0 p) := by
    refine ⟨u - shellCoverCenter p, ?_, ?_⟩
    · change u - shellCoverCenter p ∈ openCubeSet (originCube d 0)
      rw [mem_openCubeSet_originCube_iff]
      intro i
      have hi := abs_le.mp (hnear i)
      norm_num
      exact ⟨by linarith, by linarith⟩
    · dsimp [u, physicalShellCoverCenter]
      ext i
      simp
  refine ⟨p, hpMem, ⟨hxAmbient, hxUnit⟩, ?_⟩
  intro y hy
  have hyDist : ‖y - x‖ < rho :=
    euclideanBall_subset_metricBall hrho hy
  have hyAmbient : y ∈ translatedCube d m z := by
    refine ⟨y - z, ?_, by ext i; simp⟩
    change y - z ∈ openCubeSet (originCube d m)
    rw [mem_openCubeSet_originCube_iff]
    intro i
    have hxi : |(x - z) i| ≤ ‖x - z‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (x - z) i
    have hyxi : |(y - x) i| ≤ ‖y - x‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (y - x) i
    have hcoord : (y - z) i = (y - x) i + (x - z) i := by simp
    have habs := abs_add_le ((y - x) i) ((x - z) i)
    have habs' : |(y - z) i| ≤ |(y - x) i| + |(x - z) i| := by
      rw [hcoord]
      exact habs
    have hupper : |(y - z) i| < (3 : ℝ) ^ m / 2 := by
      calc
        |(y - z) i| ≤ |(y - x) i| + |(x - z) i| := habs'
        _ < rho + (3 : ℝ) ^ m / 4 := by
          linarith [hyxi, hxi.trans hcollar]
        _ ≤ (3 : ℝ) ^ m / 2 := by linarith
    have hh := abs_lt.mp hupper
    constructor <;> nlinarith [hh.1, hh.2]
  have hyUnit : y ∈ translatedCube d 0
      (z + physicalShellCoverCenter 0 p) := by
    refine ⟨y - (z + physicalShellCoverCenter 0 p), ?_, by ext i; simp⟩
    change y - (z + physicalShellCoverCenter 0 p) ∈
      openCubeSet (originCube d 0)
    rw [mem_openCubeSet_originCube_iff]
    intro i
    have hyxi : |(y - x) i| ≤ ‖y - x‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (y - x) i
    have hcoord : (y - (z + physicalShellCoverCenter 0 p)) i =
        (y - x) i + (u i - shellCoverCenter p i) := by
      dsimp [u, physicalShellCoverCenter]
      simp
      ring
    have habs := abs_add_le ((y - x) i) (u i - shellCoverCenter p i)
    have habs' : |(y - (z + physicalShellCoverCenter 0 p)) i| ≤
        |(y - x) i| + |u i - shellCoverCenter p i| := by
      rw [hcoord]
      exact habs
    have hupper : |(y - (z + physicalShellCoverCenter 0 p)) i| < 1 / 2 := by
      calc
        |(y - (z + physicalShellCoverCenter 0 p)) i| ≤
            |(y - x) i| + |u i - shellCoverCenter p i| := habs'
        _ < rho + (6 : ℝ)⁻¹ := by linarith [hyxi, hnear i]
        _ ≤ 1 / 2 := by norm_num at hrhoMesh ⊢; linarith
    have hh := abs_lt.mp hupper
    simpa only [Pi.sub_apply, Pi.add_apply, zpow_zero, mul_one] using hh
  exact ⟨hyAmbient, hyUnit⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
