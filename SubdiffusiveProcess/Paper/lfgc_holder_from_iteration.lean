module

public import SubdiffusiveProcess.Paper.in_deterministic
public import SubdiffusiveProcess.Analysis.HolderDilationToolkit

@[expose] public section

/-! Quantitative finite-step excess data imply the rescaled Holder bound.
No stochastic prefix or PDE estimate is supplied by this assembly lemma. -/

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology
noncomputable section
namespace Paper

/-- The explicit exceptional-step, error, and source budgets used by the iteration lemma. -/
def aux_lfgc_holder_from_iteration_data (d k h : ℕ) (theta C2 a t S r : ℝ)
    (U : SpatialCoordinates d → ℝ) (D : ℕ) (x : SpatialCoordinates d) : Prop :=
  ∃ bad : Finset ℤ, bad ⊆ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(k : ℤ)) ∧
  ∃ epsilon defect : ℤ → ℝ,
    (∀ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(k : ℤ)), 0 ≤ epsilon j ∧ 0 ≤ defect j) ∧
    (∀ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(k : ℤ)), j ∉ bad →
      ∀ ell : Affine d, ell ∈ affineMinimizers (translatedCube d j x) U →
        excess (j - (h : ℤ)) (translatedCube d (j - (h : ℤ)) x) U ≤
          theta ^ h * excess j (translatedCube d j x) U +
            epsilon j * Real.sqrt (vecNormSq ell.slope) + defect j) ∧
    (bad.card : ℝ) ≤ C2 * (1 + (a + t * (D : ℝ))) ∧
    ∑ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(k : ℤ)), epsilon j ≤ C2 * (1 + (a + t * (D : ℝ))) ∧
    r * ∑ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(k : ℤ)), defect j ≤
      C2 * (3 : ℝ) ^ (C2 * (a + t * (D : ℝ))) * S

/-- Excess iteration gives the Campanato estimate on every depth of the observation cube. -/
theorem aux_lfgc_holder_from_iteration_camp (d h : ℕ) (theta C2 : ℝ)
    (hh : 0 < h) (htheta : theta ∈ Set.Ioo (0 : ℝ) 1)
    (hthetah : theta ^ h ∈ Set.Ioo (0 : ℝ) (3 / 5)) (hC2 : 0 ≤ C2) :
    ∃ C1 : ℝ, 0 ≤ C1 ∧
      ∀ (k : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
        r = (3 : ℝ) ^ (-(k : ℤ)) →
      ∀ (U : SpatialCoordinates d → ℝ), ContinuousOn U (Metric.closedBall z (3 * r / 2)) →
      ∀ (a t S : ℝ), 0 ≤ a → 0 ≤ t → 0 ≤ S →
        (∀ (D : ℕ), 0 < D → ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
          aux_lfgc_holder_from_iteration_data d k h theta C2 a t S r U D x) →
      ∀ (D : ℕ) (x : SpatialCoordinates d), x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) →
        let B : Set (SpatialCoordinates d) := Metric.ball x (r * (3 : ℝ) ^ (-(D : ℤ)) / 2) ∩
          (centeredCube z r hr : Set (SpatialCoordinates d))
        normalizedL2On B (fun y => U y - (volume.real B)⁻¹ * ∫ v in B, U v) ≤
          C1 * (3 : ℝ) ^ (C1 * a) * (3 : ℝ) ^ (C1 * t * (D : ℝ)) * (3 : ℝ) ^ (-(D : ℝ)) *
            (normalizedL2On (Metric.ball z (3 * r / 2))
              (fun y => U y - (volume.real (Metric.ball z (3 * r / 2)))⁻¹ *
                ∫ v in Metric.ball z (3 * r / 2), U v) + S) := by
  obtain ⟨Cit, hCit, hiter⟩ := aux_in_deterministic_regularity_translatedCube_iteration d
  refine ⟨aux_in_deterministic_regularity_campConst d Cit h C2,
    aux_in_deterministic_regularity_campConst_nonneg d Cit h C2, ?_⟩
  intro k z r hr hrk U hU a t S ha ht hS hdata D x hx
  have hosc : 0 ≤ normalizedL2On (Metric.ball z (3 * r / 2))
      (fun y => U y - (volume.real (Metric.ball z (3 * r / 2)))⁻¹ *
        ∫ v in Metric.ball z (3 * r / 2), U v) := Real.sqrt_nonneg _
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · have hc := aux_in_deterministic_regularity_camp_of_iteration z r hr k hrk U hU x hx
      0 1 0 zero_le_one (by simp only [Nat.cast_zero, add_zero, one_mul, le_refl])
    exact aux_in_deterministic_regularity_camp_arith0 d _ _ _ _ _ _ r
      ((le_max_left _ _).trans (le_max_left _ _)) ha hosc hS hc
  · obtain ⟨bad, hbad, epsilon, defect, hnn, hstep, hcard, hsumE, hsumD⟩ := hdata D hD x hx
    have hWK : translatedCube d (-(k : ℤ)) x ⊆ Metric.closedBall z (3 * r / 2) := by
      rw [aux_in_deterministic_regularity_translatedCube_eq_ball, ← hrk]
      intro y hy
      have hx' : dist x z < r / 2 := hx
      rw [Metric.mem_ball] at hy
      rw [Metric.mem_closedBall]
      linarith only [dist_triangle y x z, hx', hy, hr]
    have hWm : MeasurableSet (translatedCube d (-(k : ℤ)) x) := by
      rw [aux_in_deterministic_regularity_translatedCube_eq_ball]
      exact Metric.isOpen_ball.measurableSet
    obtain ⟨Cb, hCb⟩ := (isCompact_closedBall z (3 * r / 2)).exists_bound_of_continuousOn hU
    haveI instFiniteTranslated : IsFiniteMeasure (volume.restrict (translatedCube d (-(k : ℤ)) x)) := by
      rw [aux_in_deterministic_regularity_translatedCube_eq_ball]
      exact isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    have hMem : MemLp U 2 (volume.restrict (translatedCube d (-(k : ℤ)) x)) :=
      MemLp.of_bound ((hU.mono hWK).aestronglyMeasurable hWm) Cb
        (ae_restrict_of_forall_mem hWm fun y hy => hCb y (hWK hy))
    have hit := hiter h hh theta htheta hthetah (-((k : ℤ) + (D : ℤ))) (-(k : ℤ))
      (by omega) x U hMem bad hbad epsilon defect hnn hstep
    have hc := aux_in_deterministic_regularity_camp_of_iteration z r hr k hrk U hU x hx D _ _
      (Real.exp_pos _).le hit
    exact aux_in_deterministic_regularity_camp_arith d Cit C2 h a t (D : ℝ) _ S _ _ _ r _
      hCit.le hC2 ha ht (Nat.cast_nonneg D) hosc hS hr.le
      (Finset.sum_nonneg fun j hj => (hnn j hj).2) hcard hsumE hsumD hc

/-- Subcritical iteration budgets give the full anchored Holder norm with a uniform constant. -/
theorem lfgc_holder_from_iteration (d : ℕ) (alpha : ℝ) (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1)
    (h : ℕ) (theta C2 : ℝ) (hh : 0 < h) (htheta : theta ∈ Set.Ioo (0 : ℝ) 1)
    (hthetah : theta ^ h ∈ Set.Ioo (0 : ℝ) (3 / 5)) (hC2 : 0 ≤ C2) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (k : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
        r = (3 : ℝ) ^ (-(k : ℤ)) →
      ∀ (U : SpatialCoordinates d → ℝ), ContinuousOn U (Metric.closedBall z (3 * r / 2)) →
      ∀ (a t S : ℝ), 0 ≤ a → 0 ≤ t → 0 ≤ S → C * t < 1 - alpha →
        (∀ (D : ℕ), 0 < D → ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
          aux_lfgc_holder_from_iteration_data d k h theta C2 a t S r U D x) →
      IsHolderOn alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
        (fun x => U (z + r • x) - U z) ∧
      cAlphaNorm alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
        (fun x => U (z + r • x) - U z) ≤
          C * (3 : ℝ) ^ (C * a) *
            (normalizedL2On (Metric.ball z (3 * r / 2))
              (fun y => U y - (volume.real (Metric.ball z (3 * r / 2)))⁻¹ *
                ∫ v in Metric.ball z (3 * r / 2), U v) + S) := by
  obtain ⟨C1, hC1, hcamp⟩ := aux_lfgc_holder_from_iteration_camp d h theta C2 hh htheta hthetah hC2
  let C := max 1 (max C1 (2 * aux_in_deterministic_regularity_holderConst d alpha * C1))
  have hC1b : C1 ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCh : 2 * aux_in_deterministic_regularity_holderConst d alpha * C1 ≤ C :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, le_max_left _ _, ?_⟩
  intro k z r hr hrk U hU a t S ha ht hS hsub hdata
  obtain ⟨hHol, hnorm⟩ := aux_in_deterministic_regularity_glue_holder alpha halpha
    (Metric.ball z (3 * r / 2)) Metric.isOpen_ball z r hr (Subset.rfl) U (fun _ => U)
    (fun _ => hU.mono Metric.ball_subset_closedBall) (fun _ => Filter.EventuallyEq.rfl)
    C1 C a t S hC1 hC1b hCh ha ht hsub hS
    (fun _ D _ x hx => hcamp k z r hr hrk U hU a t S ha ht hS hdata D x hx)
  have hclosed : closure (centeredCube z r hr : Set (SpatialCoordinates d)) =
      (closedCube z r hr : Set (SpatialCoordinates d)) := closure_ball z (by positivity : r / 2 ≠ 0)
  rw [hclosed] at hHol
  have hscaled := aux_hDet_isHolderOn_dilation z r hr alpha U _ _
    (aux_hDet_mem_closedCube_dilation z r hr) hHol
  have hdil (x : SpatialCoordinates d) : cubeDilation z 0 r x = z + r • x := by
    ext i
    simp only [cubeDilation, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, sub_zero, smul_eq_mul]
  simp only [hdil] at hscaled
  have hdiff (x y : SpatialCoordinates d) :
      (U (z + r • x) - U z) - (U (z + r • y) - U z) = U (z + r • x) - U (z + r • y) := by ring
  exact ⟨by simpa only [IsHolderOn, holderRatioSet, hdiff] using hscaled, hnorm⟩

end Paper
