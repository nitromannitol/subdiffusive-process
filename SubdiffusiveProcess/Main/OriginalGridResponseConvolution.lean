import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient
import SubdiffusiveProcess.Sobolev.GridFoldConvolution
import SubdiffusiveProcess.Sobolev.DomainPoincare
import SubdiffusiveProcess.Sobolev.AdaptiveDirichletResponse
import SubdiffusiveProcess.Sobolev.AdaptiveNeumannResponse
import SubdiffusiveProcess.Geometry.TriadicAdaptiveCover

open MeasureTheory Set TopologicalSpace
open scoped NNReal
noncomputable section

namespace SubdiffusiveProcess

theorem originalGridResponseConvolution
    {d : ℕ} (z : SpatialCoordinates d) (M : ℤ)
    (hr : 0 < (3 : ℝ) ^ M)
    (I P : Finset (Fin d)) (hI : I.Nonempty)
    (a₀ : ℝ) (ha₀ : 0 < a₀)
    (a : C(closedCube z ((3 : ℝ) ^ M) hr, ℝ))
    (ha : ∀ x, 0 < a x) :
    ∃
      (hD : ∀ J (k : OddGridIndex d (triadicHalf J)), ∃ K : ℝ≥0,
        ∀ u : killedSobolevGraph
            (oddGridCell z ((3 : ℝ) ^ M) hr (triadicHalf J) k),
          ‖(u : SobolevData
            (oddGridCell z ((3 : ℝ) ^ M) hr (triadicHalf J) k)).1‖ ≤
            K * ‖subspaceGradient (killedSobolevGraph
              (oddGridCell z ((3 : ℝ) ^ M) hr (triadicHalf J) k)) u‖)
      (hN : ∀ J (k : OddGridIndex d (triadicHalf J)), ∃ K : ℝ≥0,
        ∀ u : meanZeroSobolevGraph
            (oddGridCell z ((3 : ℝ) ^ M) hr (triadicHalf J) k),
          ‖(u : SobolevData
            (oddGridCell z ((3 : ℝ) ^ M) hr (triadicHalf J) k)).1‖ ≤
            K * ‖subspaceGradient (meanZeroSobolevGraph
              (oddGridCell z ((3 : ℝ) ^ M) hr (triadicHalf J) k)) u‖),
      ∀ n : ℤ, n ≤ M →
        let hd : 0 < d := by
          obtain ⟨i, _⟩ := hI
          exact Nat.zero_lt_of_lt i.isLt
        let hroot : Fact (((centeredCube z ((3 : ℝ) ^ M) hr :
            Set (SpatialCoordinates d)) ⊆ closedCube z ((3 : ℝ) ^ M) hr)) :=
          ⟨centeredCube_subset_closedCube z hr⟩
        let original : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ M) hr) :=
          @normalizedContinuousPositiveCoefficient d
            (centeredCube z ((3 : ℝ) ^ M) hr)
            (closedCube z ((3 : ℝ) ^ M) hr) hroot a ha a₀ ha₀
        let foldedA := a.comp (coordinateFoldOnCube z hr I P)
        let folded : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ M) hr) :=
          @normalizedContinuousPositiveCoefficient d
            (centeredCube z ((3 : ℝ) ^ M) hr)
            (closedCube z ((3 : ℝ) ^ M) hr) hroot foldedA (fun x => ha _) a₀ ha₀
        triadicDefectSup z hr hD hN folded hd (M - n).toNat ≤
          triadicDefectSup z hr hD hN original hd (M - n).toNat +
            3 * (d : ℝ) * ∑' j : ℕ, (3 : ℝ) ^ (-(j + 1 : ℤ)) *
              triadicDefectSup z hr hD hN original hd
                (M - (n - (j + 1 : ℕ))).toNat
 := by
  obtain ⟨i, hi⟩ := hI
  letI : NeZero d := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt)⟩
  have hP : ∀ J (k : OddGridIndex d (triadicHalf J)),
      (∃ K : ℝ≥0, ∀ u : killedSobolevGraph
          (oddGridCell z ((3 : ℝ) ^ M) hr (triadicHalf J) k),
        ‖(u : SobolevData
          (oddGridCell z ((3 : ℝ) ^ M) hr (triadicHalf J) k)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph
            (oddGridCell z ((3 : ℝ) ^ M) hr (triadicHalf J) k)) u‖) ∧
      (∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph
          (oddGridCell z ((3 : ℝ) ^ M) hr (triadicHalf J) k),
        ‖(u : SobolevData
          (oddGridCell z ((3 : ℝ) ^ M) hr (triadicHalf J) k)).1‖ ≤
          K * ‖subspaceGradient (meanZeroSobolevGraph
            (oddGridCell z ((3 : ℝ) ^ M) hr (triadicHalf J) k)) u‖) := by
    intro J k
    let Ω := oddGridCell z ((3 : ℝ) ^ M) hr (triadicHalf J) k
    have hΩ : Homogenization.IsOpenBoundedConvexDomain
        (Ω : Set (SpatialCoordinates d)) := by
      refine ⟨Ω.isOpen, ?_, ?_⟩
      · simpa [Ω] using
          (Homogenization.Bornology.IsBounded.isBoundedDomain
            (centeredCube_isBounded (oddGridCenter z ((3 : ℝ) ^ M)
              (triadicHalf J) k) (div_pos hr (by positivity))))
      · simpa [Ω, centeredCube] using
          (convex_ball (oddGridCenter z ((3 : ℝ) ^ M)
            (triadicHalf J) k)
            (((3 : ℝ) ^ M / (2 * (triadicHalf J : ℝ) + 1)) / 2))
    simpa [Ω] using
      (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain Ω hΩ)
  let hD : ∀ J (k : OddGridIndex d (triadicHalf J)), ∃ K : ℝ≥0,
      ∀ u : killedSobolevGraph
          (oddGridCell z ((3 : ℝ) ^ M) hr (triadicHalf J) k),
        ‖(u : SobolevData
          (oddGridCell z ((3 : ℝ) ^ M) hr (triadicHalf J) k)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph
            (oddGridCell z ((3 : ℝ) ^ M) hr (triadicHalf J) k)) u‖ :=
    fun J k => (hP J k).1
  let hN : ∀ J (k : OddGridIndex d (triadicHalf J)), ∃ K : ℝ≥0,
      ∀ u : meanZeroSobolevGraph
          (oddGridCell z ((3 : ℝ) ^ M) hr (triadicHalf J) k),
        ‖(u : SobolevData
          (oddGridCell z ((3 : ℝ) ^ M) hr (triadicHalf J) k)).1‖ ≤
          K * ‖subspaceGradient (meanZeroSobolevGraph
            (oddGridCell z ((3 : ℝ) ^ M) hr (triadicHalf J) k)) u‖ :=
    fun J k => (hP J k).2
  refine ⟨hD, hN, ?_⟩
  intro n hn
  dsimp
  let hd : 0 < d := Nat.zero_lt_of_lt i.isLt
  let hroot : Fact (((centeredCube z ((3 : ℝ) ^ M) hr :
      Set (SpatialCoordinates d)) ⊆ closedCube z ((3 : ℝ) ^ M) hr)) :=
    ⟨centeredCube_subset_closedCube z hr⟩
  let g : C(closedCube z ((3 : ℝ) ^ M) hr, ℝ) :=
    continuousPositiveLog a ha - ContinuousMap.const _ (Real.log a₀)
  let original : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ M) hr) :=
    @normalizedContinuousPositiveCoefficient d
      (centeredCube z ((3 : ℝ) ^ M) hr)
      (closedCube z ((3 : ℝ) ^ M) hr) hroot a ha a₀ ha₀
  let foldedA := a.comp (coordinateFoldOnCube z hr I P)
  let folded : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ M) hr) :=
    @normalizedContinuousPositiveCoefficient d
      (centeredCube z ((3 : ℝ) ^ M) hr)
      (closedCube z ((3 : ℝ) ^ M) hr) hroot foldedA (fun x => ha _) a₀ ha₀
  have hlog :
      continuousPositiveLog foldedA (fun x => ha _) -
          ContinuousMap.const _ (Real.log a₀) =
        g.comp (coordinateFoldOnCube z hr I P) := by
    ext x
    rfl
  have horiginal : original = expPotentialCoefficient
      (compactPotentialLp (Ω := centeredCube z ((3 : ℝ) ^ M) hr)
        (closedCube z ((3 : ℝ) ^ M) hr) g) := by
    simp only [original, normalizedContinuousPositiveCoefficient, g,
      compactPotentialToLp_apply]
  have hfolded : folded = expPotentialCoefficient
      (compactPotentialLp (Ω := centeredCube z ((3 : ℝ) ^ M) hr)
        (closedCube z ((3 : ℝ) ^ M) hr)
        (g.comp (coordinateFoldOnCube z hr I P))) := by
    simp only [folded, normalizedContinuousPositiveCoefficient,
      compactPotentialToLp_apply, hlog]
  let N := (M - n).toNat
  have hseries := triadicDefectSup_fold_le_series z hr hD hN hd N I P g (by
    intro k p
    dsimp
    intro J hdisj hcover
    let w := oddGridCenter z ((3 : ℝ) ^ M) (triadicHalf N) k
    let s := (3 : ℝ) ^ M / (2 * (triadicHalf N : ℝ) + 1)
    let hs : 0 < s := div_pos hr (by positivity)
    let I' := triadicObservationPlanes N I k
    let afU := positiveCoefficientRestrict
      (oddGridCell_subset z hr (triadicHalf N) k)
      (expPotentialCoefficient (compactPotentialLp
        (Ω := centeredCube z ((3 : ℝ) ^ M) hr)
        (closedCube z ((3 : ℝ) ^ M) hr)
        (g.comp (coordinateFoldOnCube z hr I P))))
    have hI' : I'.Nonempty :=
      triadicAdaptivePlanes_nonempty_of_ae_cover w hs I' J hcover
    have hdir := triadicAdaptive_affineDirichletResponse_le_sum
      w hs hI' J (hD N k)
      (observation_killedPoincare z hr hD N k)
      afU p
    have hneu := triadicAdaptive_affineInverseNeumannResponse_le_sum
      w hs hI' J (hN N k)
      (observation_meanZeroPoincare z hr hN N k)
      afU p
    exact ⟨by simpa [afU, w, s, hs, I'] using hdir,
      by simpa [afU, w, s, hs, I'] using hneu⟩
    )
  have hidx (j : ℕ) : N + (j + 1) =
      (M - (n - (j + 1 : ℕ))).toNat := by
    dsimp [N]
    have hn0 : 0 ≤ M - n := by omega
    rw [show M - (n - ((j : ℤ) + 1)) = (M - n) + ((j : ℤ) + 1) by ring]
    rw [Int.toNat_add hn0 (by positivity)]
    have hj : ((j : ℤ) + 1).toNat = j + 1 := by omega
    rw [hj]
  have hcoef (j : ℕ) :
      (d : ℝ) / (3 : ℝ) ^ j = 3 * (d : ℝ) * (3 : ℝ) ^ (-(j + 1 : ℤ)) := by
    rw [zpow_neg]
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
    field_simp
  have hseries' := hseries
  rw [← hfolded, ← horiginal] at hseries'
  let R : ℕ → ℝ := fun m =>
    triadicDefectSup z hr hD hN original hd m
  have hseriesR :
      triadicDefectSup z hr hD hN folded hd N ≤
        triadicDefectSup z hr hD hN original hd N +
          ∑' j : ℕ, ((d : ℝ) / (3 : ℝ)^j) * R (N + (j + 1)) := by
    simpa only [R] using hseries'
  have hsum :
      (∑' j : ℕ, ((d : ℝ) / (3 : ℝ)^j) * R (N + (j + 1))) =
        3 * (d : ℝ) * ∑' j : ℕ, (3 : ℝ) ^ (-(j + 1 : ℤ)) *
          R (M - (n - (j + 1 : ℕ))).toNat := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    rw [hidx, hcoef]
    ring
  calc
    triadicDefectSup z hr hD hN folded hd N ≤
        triadicDefectSup z hr hD hN original hd N +
          ∑' j : ℕ, ((d : ℝ) / (3 : ℝ)^j) * R (N + (j + 1)) := hseriesR
    _ = triadicDefectSup z hr hD hN original hd N +
        3 * (d : ℝ) * ∑' j : ℕ, (3 : ℝ) ^ (-(j + 1 : ℤ)) *
          R (M - (n - (j + 1 : ℕ))).toNat := by rw [hsum]


end SubdiffusiveProcess
