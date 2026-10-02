import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.BoundaryTileResidualCap

/-!
# The half of a cube cut by a coordinate hyperplane through its centre

The tile of `ledger/reports/provider-48-harmonic-boundary.md` §12.3 is centred
on the met face `∂𝔠_m`, so the zero extension of `u − h ∈ H¹₀(𝔠_m)` vanishes on
exactly the half of the tile lying outside `𝔠_m`.  This module supplies that
geometric input in the form the vanishing-fraction mean bound consumes: the
open half `cubeUpperHalf Q j0` cut off by the hyperplane through the cube
centre orthogonal to `e_{j0}` is measurable, contained in the open cube, and
has exactly half its volume — so `θ = 1/2` is admissible.

Combined with `exists_boundaryTileResidualMeanCap` this gives the fully
explicit tile price with no free geometric hypothesis left.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The open half of a triadic cube on the far side of the coordinate
hyperplane through its centre orthogonal to `e_{j0}`. -/
def cubeUpperHalf (Q : TriadicCube d) (j0 : Fin d) : Set (Vec d) :=
  Set.pi Set.univ fun i : Fin d =>
    Set.Ioo
      (if i = j0 then (Q.index i : ℝ) * cubeScaleFactor Q
        else ((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q)
      (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q)

theorem measurableSet_cubeUpperHalf (Q : TriadicCube d) (j0 : Fin d) :
    MeasurableSet (cubeUpperHalf Q j0) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

theorem cubeUpperHalf_subset_openCubeSet (Q : TriadicCube d) (j0 : Fin d) :
    cubeUpperHalf Q j0 ⊆ openCubeSet Q := by
  have hs : (0 : ℝ) < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  have hlo : ∀ i : Fin d,
      ((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q ≤
        (if i = j0 then (Q.index i : ℝ) * cubeScaleFactor Q
          else ((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q) := by
    intro i
    by_cases h : i = j0
    · simp only [if_pos h]
      nlinarith [hs]
    · simp only [if_neg h]
      exact le_rfl
  intro x hx
  rw [openCubeSet_eq_pi_Ioo]
  intro i _
  have hxi := hx i (Set.mem_univ i)
  exact ⟨lt_of_le_of_lt (hlo i) hxi.1, hxi.2⟩

/-- Membership in the half is membership in the cube together with the
half-space condition. -/
theorem mem_cubeUpperHalf_iff (Q : TriadicCube d) (j0 : Fin d) (x : Vec d) :
    x ∈ cubeUpperHalf Q j0 ↔
      x ∈ openCubeSet Q ∧ (Q.index j0 : ℝ) * cubeScaleFactor Q < x j0 := by
  have hs : (0 : ℝ) < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  constructor
  · intro hx
    refine ⟨cubeUpperHalf_subset_openCubeSet Q j0 hx, ?_⟩
    have hj := (hx j0 (Set.mem_univ j0)).1
    simpa using hj
  · rintro ⟨hxQ, hxj⟩
    intro i _
    have hxi := hxQ i
    by_cases h : i = j0
    · subst h
      exact ⟨by simpa using hxj, hxi.2⟩
    · exact ⟨by simpa [h] using hxi.1, hxi.2⟩

/-- **The half of a cube has half its volume.** -/
theorem volume_cubeUpperHalf_toReal (Q : TriadicCube d) (j0 : Fin d) :
    (volume (cubeUpperHalf Q j0)).toReal = cubeVolume Q / 2 := by
  have hs : (0 : ℝ) < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  set lo : Fin d → ℝ := fun i =>
    if i = j0 then (Q.index i : ℝ) * cubeScaleFactor Q
      else ((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q with hlo
  set hi : Fin d → ℝ := fun i => ((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q with hhi
  have hab : lo ≤ hi := by
    intro i
    rw [hlo, hhi]
    by_cases h : i = j0
    · simp only [if_pos h]
      nlinarith [hs]
    · simp only [if_neg h]
      nlinarith [hs]
  have hvol : (volume (cubeUpperHalf Q j0)).toReal = ∏ i : Fin d, (hi i - lo i) := by
    simpa [cubeUpperHalf, hlo, hhi] using Real.volume_pi_Ioo_toReal (ι := Fin d) hab
  rw [hvol]
  have hside : ∀ i : Fin d,
      hi i - lo i = cubeScaleFactor Q * (if i = j0 then (1 / 2 : ℝ) else 1) := by
    intro i
    rw [hlo, hhi]
    by_cases h : i = j0
    · simp only [if_pos h]
      ring
    · simp only [if_neg h]
      ring
  calc
    ∏ i : Fin d, (hi i - lo i)
        = ∏ i : Fin d, (cubeScaleFactor Q * (if i = j0 then (1 / 2 : ℝ) else 1)) :=
          Finset.prod_congr rfl fun i _ => hside i
    _ = (∏ _i : Fin d, cubeScaleFactor Q) *
          ∏ i : Fin d, (if i = j0 then (1 / 2 : ℝ) else 1) := Finset.prod_mul_distrib
    _ = cubeVolume Q / 2 := by
          rw [Finset.prod_ite_eq' Finset.univ j0 (fun _ : Fin d => (1 / 2 : ℝ))]
          simp [cubeVolume]
          ring

/-- The vanishing fraction supplied by a tile centred on the met face is
`θ = 1/2`. -/
theorem half_mul_volume_openCubeSet_le_volume_cubeUpperHalf
    (Q : TriadicCube d) (j0 : Fin d) :
    (1 / 2 : ℝ) * (volume (openCubeSet Q)).toReal ≤
      (volume (cubeUpperHalf Q j0)).toReal := by
  rw [volume_openCubeSet_toReal, volume_cubeUpperHalf_toReal]
  ring_nf
  exact le_rfl

/-- **The boundary tile price with the geometry discharged.**  Specialisation of
`exists_boundaryTileResidualMeanCap` to a tile whose met face is the coordinate
hyperplane through its centre: the vanishing fraction is exactly `1/2`, so no
geometric hypothesis remains. -/
theorem exists_boundaryTileResidualMeanCap_half (d : ℕ) [NeZero d] :
    ∃ Ctile : ℝ, 0 < Ctile ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L n : ℕ, n + 2 ≤ L → ∀ (k : ℤ) omega y z,
        translateSet (y - z) (cubeSet (originCube d k)) ⊆
          cubeSet (originCube d ((n : ℤ) + 2)) →
        omega ∈ goodEvent M none (n + 2) z 1 (s / 8) →
        let T := originCube d k
        let A := aCutoffFamily M L (translatePotentialSample y omega)
        let sigma := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
        ∀ (w : H1Function (openCubeSet T)) (j0 : Fin d),
          (∀ x ∈ cubeUpperHalf T j0, w.toFun x = 0) →
          IntegrableOn w.toFun (openCubeSet T) →
          IntegrableOn (fun x => w.toFun x ^ 2) (openCubeSet T) →
          MemLp (fun x => w.toFun x - cubeAverage T w.toFun) 2
            (volume.restrict (openCubeSet T)) →
          cubeAverage T w.toFun ^ 2 ≤
            Ctile *
                (3 : ℝ) ^ (s / 4 * ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ)) *
                sigma⁻¹ * cubeScaleFactor T ^ 2 *
              cubeAverage T (coefficientEnergyDensity (publicCoeffField T A) w.grad) := by
  obtain ⟨C, hC, hcap⟩ := exists_boundaryTileResidualMeanCap d
  refine ⟨2 * C, by linarith, ?_⟩
  intro M s hs L n hnL k omega y z hcontain hgood
  dsimp only
  intro w j0 hzero hf hf2 hmem
  have hraw := hcap M s hs L n hnL k omega y z hcontain hgood w
    (cubeUpperHalf (originCube d k) j0) (1 / 2 : ℝ)
    (measurableSet_cubeUpperHalf _ j0)
    (cubeUpperHalf_subset_openCubeSet _ j0) (by norm_num)
    (half_mul_volume_openCubeSet_le_volume_cubeUpperHalf _ j0)
    hzero hf hf2 hmem
  have hinv : ((1 : ℝ) / 2)⁻¹ = 2 := by norm_num
  rw [hinv] at hraw
  refine hraw.trans (le_of_eq ?_)
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
