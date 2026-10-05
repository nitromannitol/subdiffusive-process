module

public import SubdiffusiveProcess.BesovComparison.CenterGeometry
public import SubdiffusiveProcess.BesovComparison.ScalarDepth

@[expose] public section

/-! Exact identification of the real-centre norm with the overlap norm. -/
open Homogenization MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec Mat TriadicCube
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.BesovComparison
variable {d : ℕ}

theorem normalized_root_measure (m : ℤ) :
    normalizedCubeMeasure (originCube d m) =
      (volume (cube d m))⁻¹ • volume.restrict (cube d m) := by
  unfold normalizedCubeMeasure cubeMeasure cube
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  congr 1
  rw [ENNReal.ofReal_inv_of_pos (cubeVolume_pos _)]
  congr 1
  rw [← volume_openCubeSet_toReal, ENNReal.ofReal_toReal (volume_openCubeSet_lt_top _).ne]

theorem normalized_overlap_measure (S : TriadicCube d) :
    ScalarOverlap.normalizedCubeMeasure S =
      (volume (ScalarOverlap.openCubeSet S))⁻¹ • volume.restrict (ScalarOverlap.openCubeSet S) := by
  unfold ScalarOverlap.normalizedCubeMeasure ScalarOverlap.cubeMeasure
  rw [ScalarOverlap.volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  congr 1
  rw [ENNReal.ofReal_inv_of_pos (ScalarOverlap.cubeVolume_pos _)]
  congr 1
  rw [← ScalarOverlap.volume_openCubeSet_toReal,
    ENNReal.ofReal_toReal (by
      rw [← measure_congr (ScalarOverlap.cubeSet_ae_eq_openCubeSet S)]
      exact (ScalarOverlap.volume_cubeSet_lt_top _).ne)]

theorem local_mean_eq_average (S : TriadicCube d) (u : Vec d → ℝ)
    (hu : Integrable u (ScalarOverlap.normalizedCubeMeasure S)) :
    exactOverlapLocalMean S u hu = ⨍ y in ScalarOverlap.openCubeSet S, u y := by
  rw [exactOverlapLocalMean_eq, normalized_overlap_measure]
  rw [average_eq']
  simp

theorem local_oscillation_eq (S : TriadicCube d) (p : ℝ≥0∞) (u : Vec d → ℝ)
    (hu : Integrable u (ScalarOverlap.normalizedCubeMeasure S)) :
    exactOverlapLocalOscillation S p u hu =
      normalizedLp (translatedCube d (S.scale + 1) (cubeCenter S)) p
        (fun x => u x - ⨍ y in translatedCube d (S.scale + 1) (cubeCenter S), u y) := by
  rw [← overlap_openCube_eq_translatedCube]
  unfold exactOverlapLocalOscillation normalizedLp
  rw [local_mean_eq_average, normalized_overlap_measure]

theorem average_eq_depth (m : ℤ) (j : ℕ) (p : ℝ) (u : Vec d → ℝ)
    (hu : ExactOverlapIntegrable (originCube d m) u) (hp : 0 ≤ p) :
    averageLp (positiveCenters d m (m - (j : ℤ))) (ENNReal.ofReal p)
      (fun z => normalizedLp (translatedCube d (m - (j : ℤ)) z) (ENNReal.ofReal p)
        (fun x => u x - ⨍ y in translatedCube d (m - (j : ℤ)) z, u y)) =
      exactOverlapDepthAverage (originCube d m) p u hu j ^ p⁻¹ := by
  classical
  rw [averageLp, ite_eq_right ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp,
    positiveCenters_eq_image, Set.InjOn.ncard_image (cubeCenter_injective_on_centers _ _),
    Set.ncard_coe_finset, finsum_mem_image (cubeCenter_injective_on_centers _ _),
    finsum_mem_coe_finset]
  rw [one_div]
  congr 1
  unfold exactOverlapDepthAverage
  congr 1
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro T _
  let S := T.val
  have hS : S ∈ ScalarOverlap.centersAtDepth (originCube d m) j := T.property
  have hscale := scale_eq_sub_of_mem_descendantsAtDepth
    (ScalarOverlap.mem_descendantsAtDepth_of_mem_centersAtDepth hS)
  have hn : S.scale + 1 = m - (j : ℤ) := by dsimp [originCube] at hscale; omega
  change _ = exactOverlapLocalOscillation S (ENNReal.ofReal p) u (hu.overlap j S hS) ^ p
  rw [local_oscillation_eq, hn]

theorem integer_tsum_depth (m : ℤ) (f : ℤ → ℝ≥0∞) :
    (∑' n : ℤ, if n ≤ m then f n else 0) = ∑' j : ℕ, f (m - (j : ℤ)) := by
  let g : ℕ → ℤ := fun j => m - (j : ℤ)
  have hg : Function.Injective g := by intro a b h; dsimp [g] at h; omega
  have hs : Function.support (fun n : ℤ => if n ≤ m then f n else 0) ⊆ Set.range g := by
    intro n hn
    have hnm : n ≤ m := by
      by_contra h
      simp only [ite_eq_right h, Function.mem_support, ne_eq, not_true_eq_false] at hn
    exact ⟨(m - n).toNat, by dsimp [g]; rw [Int.toNat_of_nonneg (by omega)]; omega⟩
  rw [← hg.tsum_eq hs]
  apply tsum_congr
  intro j
  exact ite_eq_left (by dsimp [g]; omega)

theorem besov_eq_overlap (m : ℤ) (s p : ℝ) (hp : 0 ≤ p)
    (P : ExactOverlapFiniteParameters) (hPs : P.s = s) (hPp : P.p = p) (hPq : P.q = p)
    (u : Vec d → ℝ) (hu : ExactOverlapIntegrable (originCube d m) u) :
    besov d m s (ENNReal.ofReal p) (ENNReal.ofReal p) (ENNReal.ofReal p) u =
      ENNReal.ofReal s ^ p⁻¹ * exactOverlapFiniteSeminorm P (originCube d m) u hu := by
  unfold besov aggregate
  rw [ite_eq_right ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp, integer_tsum_depth,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), one_div]
  congr 1
  unfold exactOverlapFiniteSeminorm
  rw [hPq]
  congr 1
  apply tsum_congr
  intro j
  dsimp only
  rw [average_eq_depth m j p u hu hp]
  unfold exactOverlapDepthTerm
  rw [hPs, hPp]
  congr 2
  unfold exactOverlapDepthWeight exactOverlapSourceDepth
  dsimp [originCube]
  simpa using (ENNReal.ofReal_rpow_of_pos (p := -((m - (j : ℤ) : ℤ) : ℝ) * s)
    (by norm_num : (0 : ℝ) < 3)).symm

end SubdiffusiveProcess.BesovComparison
