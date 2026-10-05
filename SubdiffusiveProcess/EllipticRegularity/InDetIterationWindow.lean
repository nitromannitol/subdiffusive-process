module

public import SubdiffusiveProcess.EllipticRegularity.InDetCampanatoHolder
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.TranslatedIteration

@[expose] public section




open MeasureTheory Set Metric Filter Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec

noncomputable section
namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable

/-- The iteration lemma on concentric translated cubes, for a plain `L²` function. -/
theorem aux_in_deterministic_regularity_translatedCube_iteration (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℕ, 0 < h → ∀ theta ∈ Set.Ioo (0 : ℝ) 1,
      theta ^ h ∈ Set.Ioo (0 : ℝ) (3 / 5) →
      ∀ n m : ℤ, n < m → ∀ z : Vec d,
      ∀ u : Vec d → ℝ, MemLp u 2 (volume.restrict (translatedCube d m z)) →
      ∀ bad : Finset ℤ, bad ⊆ Finset.Icc n m →
      ∀ epsilon defect : ℤ → ℝ,
        (∀ j ∈ Finset.Icc n m, 0 ≤ epsilon j ∧ 0 ≤ defect j) →
        (∀ j ∈ Finset.Icc n m, j ∉ bad →
          ∀ ell : Affine d,
            ell ∈ affineMinimizers (translatedCube d j z) u →
            excess (j - h) (translatedCube d (j - h) z) u ≤
              theta ^ h * excess j (translatedCube d j z) u +
                epsilon j * Real.sqrt (vecNormSq ell.slope) + defect j) →
        (3 : ℝ) ^ (-n) *
            normalizedL2On (translatedCube d n z)
              (fun x ↦ u x - averageOn (translatedCube d n z) u) ≤
          Real.exp (C * (h + 1) * (bad.card + 1) + C * ∑ j ∈ Finset.Icc n m, epsilon j) *
            ((3 : ℝ) ^ (-m) *
              normalizedL2On (translatedCube d m z)
                (fun x ↦ u x - averageOn (translatedCube d m z) u) +
              ∑ j ∈ Finset.Icc n m, defect j) := by
  obtain ⟨C, hC, hiter⟩ := _root_.SubdiffusiveProcess.Section6.iteration_lemma d
  refine ⟨C, hC, ?_⟩
  intro h hh theta htheta hthetah n m hnm z u hu bad hbad epsilon defect hnonneg hrec
  have hmono : ∀ {a b : ℤ}, a ≤ b → translatedCube d a z ⊆ translatedCube d b z := by
    intro a b hab
    rintro p ⟨q, hq, rfl⟩
    exact ⟨q, Section6ExcessDecay.cube_subset_cube_of_le hab hq, rfl⟩
  let U : ℤ → Set (Vec d) := fun j ↦ translatedCube d j z
  have hUmb : ∀ j, MeasurableSet (U j) ∧ Bornology.IsBounded (U j) := by
    intro j
    exact ⟨(Section6CutoffRegularity.isOpen_translatedCube d j z).measurableSet,
      Section6CutoffRegularity.isBounded_translatedCube d j z⟩
  have hnest : ∀ j ≤ m, U (j - 1) ⊆ U j := fun j _ => hmono (by omega)
  have hsand : ∀ j ≤ m, ∃ x y : Vec d,
      translatedCube d (j - 2) x ⊆ U j ∧ U j ⊆ translatedCube d j y :=
    fun j _ => ⟨z, z, hmono (by omega), Set.Subset.rfl⟩
  have huAll : ∀ j ≤ m, MemLp u 2 (volume.restrict (U j)) := fun j hj =>
    hu.mono_measure (Measure.restrict_mono (hmono hj) le_rfl)
  have hexists : ∀ j ≤ m, ∃ ell : Affine d, ell ∈ affineMinimizers (U j) u := by
    intro j hj
    have hWm : MeasurableSet (U j) :=
      (Section6CutoffRegularity.isOpen_translatedCube d j z).measurableSet
    have hcube : U j = axisCube (Section6BoundaryL2.cubeCorner j z) ((3 : ℝ) ^ j) :=
      Section6BoundaryL2.translatedCube_eq_axisCube d j z
    obtain ⟨c, g, hcg⟩ :=
      Section6Iteration.exists_isAffineMinimizer_of_axisCubeSandwich
        (zpow_pos (by norm_num : (0 : ℝ) < 3) j)
        (zpow_pos (by norm_num : (0 : ℝ) < 3) j) hWm
        (by rw [hcube]) (by rw [hcube]) u (huAll j hj)
    exact ⟨⟨c, g⟩, Section6Iteration.mem_affineMinimizers_iff.2 hcg⟩
  let fit : ℤ → Affine d := fun j ↦
    if hj : j ≤ m then Classical.choose (hexists j hj) else ⟨0, 0⟩
  have hfit : ∀ j ≤ m, fit j ∈ affineMinimizers (U j) u := by
    intro j hj
    simpa only [fit, dite_eq_left hj] using! Classical.choose_spec (hexists j hj)
  exact (hiter h hh theta htheta hthetah n m hnm U hUmb hnest hsand u hu bad hbad epsilon defect
    hnonneg fit hfit (fun j hj hnot ↦ hrec j hj hnot (fit j)
      (hfit j (Finset.mem_Icc.1 hj).2))).1

/-- The translated paper cube is the sup-ball of radius `3^j / 2`. -/
theorem aux_in_deterministic_regularity_translatedCube_eq_ball {d : ℕ} (j : ℤ) (z : Vec d) :
    translatedCube d j z = Metric.ball z ((3 : ℝ) ^ j / 2) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [Metric.mem_ball, dist_pi_lt_iff (by positivity)]
    intro i
    have hqi := hq i
    simp only [originCube, cubeScaleFactor, Pi.zero_apply, Int.cast_zero, zero_sub,
      zero_add] at hqi
    have hsimp : (fun x => z + x) q i - z i = q i := by simp
    rw [Real.dist_eq, hsimp, abs_lt]
    constructor <;> linarith [hqi.1, hqi.2]
  · intro hy
    refine ⟨y - z, ?_, by simp⟩
    rw [Metric.mem_ball, dist_pi_lt_iff (by positivity)] at hy
    intro i
    have hyi := hy i
    rw [Real.dist_eq, abs_lt] at hyi
    simp only [originCube, cubeScaleFactor, Pi.zero_apply, Int.cast_zero, zero_sub, zero_add,
      Pi.sub_apply]
    constructor <;> linarith [hyi.1, hyi.2]

/-- The mean minimizes the mean-square deviation. -/
theorem aux_in_deterministic_regularity_mean_min {d : ℕ} {B : Set (SpatialCoordinates d)}
    (hvol : volume B ≠ ⊤) {g : SpatialCoordinates d → ℝ} (hi : IntegrableOn g B)
    (hi2 : IntegrableOn (fun y => g y ^ 2) B) (c : ℝ) :
    (volume.real B)⁻¹ * ∫ y in B, (g y - (volume.real B)⁻¹ * ∫ t in B, g t) ^ 2 ≤
      (volume.real B)⁻¹ * ∫ y in B, (g y - c) ^ 2 := by
  rcases (measureReal_nonneg : 0 ≤ volume.real B).eq_or_lt with hV0 | hVpos
  · rw [← hV0]; simp
  have hint : ∫ y in B, g y = volume.real B * ((volume.real B)⁻¹ * ∫ y in B, g y) := by
    rw [← mul_assoc, mul_inv_cancel₀ hVpos.ne', one_mul]
  generalize hm : (volume.real B)⁻¹ * ∫ y in B, g y = m at hint ⊢
  have hexp : ∀ a : ℝ, ∫ y in B, (g y - a) ^ 2 =
      ((∫ y in B, g y ^ 2) - 2 * a * (∫ y in B, g y)) + a ^ 2 * volume.real B := by
    intro a
    have hlin : IntegrableOn (fun y => 2 * a * g y) B := hi.const_mul _
    have hconst : IntegrableOn (fun _ : SpatialCoordinates d => a ^ 2) B := integrableOn_const hvol
    have hpt : (fun y => (g y - a) ^ 2) = fun y => (g y ^ 2 - 2 * a * g y) + a ^ 2 := by
      funext y; ring
    rw [hpt, integral_add (f := fun y => g y ^ 2 - 2 * a * g y) (g := fun _ => a ^ 2)
      (by simpa only [Pi.sub_apply] using! hi2.sub hlin) hconst,
      integral_sub (f := fun y => g y ^ 2) (g := fun y => 2 * a * g y) hi2 hlin,
      integral_const_mul, setIntegral_const, smul_eq_mul]
    ring
  rw [hexp m, hexp c, hint]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 hVpos.le)
  nlinarith [sq_nonneg (m - c)]

/-- Oscillation on a subwindow is controlled by the oscillation on the window. -/
theorem aux_in_deterministic_regularity_osc_sub_le {d : ℕ}
    {Kset B B' : Set (SpatialCoordinates d)} (hK : IsCompact Kset)
    {U : SpatialCoordinates d → ℝ} (hU : ContinuousOn U Kset) (hBK : B ⊆ Kset)
    (hB'B : B' ⊆ B) (hvol' : 0 < volume.real B') :
    normalizedL2On B' (fun y => U y - (volume.real B')⁻¹ * ∫ t in B', U t) ≤
      Real.sqrt (volume.real B / volume.real B') *
        normalizedL2On B (fun y => U y - (volume.real B)⁻¹ * ∫ t in B, U t) := by
  set A := (volume.real B)⁻¹ * ∫ t in B, U t with hA
  have hKfin : volume Kset ≠ ⊤ := hK.measure_lt_top.ne
  have hBfin : volume B ≠ ⊤ := ne_top_of_le_ne_top hKfin (measure_mono hBK)
  have hB'fin : volume B' ≠ ⊤ := ne_top_of_le_ne_top hBfin (measure_mono hB'B)
  have hUK : IntegrableOn U Kset := hU.integrableOn_compact hK
  have hU2K : ∀ c : ℝ, IntegrableOn (fun y => (U y - c) ^ 2) Kset := fun c =>
    ((hU.sub continuousOn_const).pow 2).integrableOn_compact hK
  have hVle : volume.real B' ≤ volume.real B := measureReal_mono hB'B hBfin
  have hVpos : 0 < volume.real B := hvol'.trans_le hVle
  have hmin := aux_in_deterministic_regularity_mean_min hB'fin
    (hUK.mono_set (hB'B.trans hBK))
    (((hU.pow 2).integrableOn_compact hK).mono_set (hB'B.trans hBK)) A
  have hmono : ∫ y in B', (U y - A) ^ 2 ≤ ∫ y in B, (U y - A) ^ 2 :=
    setIntegral_mono_set ((hU2K A).mono_set hBK) (Eventually.of_forall fun y => sq_nonneg _)
      (Eventually.of_forall hB'B)
  have hstep : (volume.real B')⁻¹ * ∫ y in B', (U y - A) ^ 2 ≤
      (volume.real B / volume.real B') *
        ((volume.real B)⁻¹ * ∫ y in B, (U y - A) ^ 2) := by
    have heq : (volume.real B / volume.real B') *
        ((volume.real B)⁻¹ * ∫ y in B, (U y - A) ^ 2) =
        (volume.real B')⁻¹ * ∫ y in B, (U y - A) ^ 2 := by
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_left hmono (inv_nonneg.2 hvol'.le)
  have hn1 : normalizedL2On B' (fun y => U y - (volume.real B')⁻¹ * ∫ t in B', U t) =
      Real.sqrt ((volume.real B')⁻¹ *
        ∫ y in B', (U y - (volume.real B')⁻¹ * ∫ t in B', U t) ^ 2) := rfl
  have hn2 : normalizedL2On B (fun y => U y - A) =
      Real.sqrt ((volume.real B)⁻¹ * ∫ y in B, (U y - A) ^ 2) := rfl
  rw [hn1, hn2, ← Real.sqrt_mul (div_nonneg hVpos.le hvol'.le)]
  exact Real.sqrt_le_sqrt (hmin.trans hstep)



theorem aux_in_deterministic_regularity_camp_of_iteration {d : ℕ}
    (qcenter : SpatialCoordinates d) (qside : ℝ) (hqpos : 0 < qside) (k : ℕ)
    (hqside : qside = (3 : ℝ) ^ (-(k : ℤ)))
    (U : SpatialCoordinates d → ℝ)
    (hU : ContinuousOn U (closedBall qcenter (3 * qside / 2)))
    (x : SpatialCoordinates d)
    (hx : x ∈ (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))) (D : ℕ)
    (eA Sdef : ℝ) (heA : 0 ≤ eA)
    (hiter : (3 : ℝ) ^ (-(-((k : ℤ) + (D : ℤ)))) *
        normalizedL2On (translatedCube d (-((k : ℤ) + (D : ℤ))) x)
          (fun y ↦ U y - averageOn (translatedCube d (-((k : ℤ) + (D : ℤ))) x) U) ≤
      eA * ((3 : ℝ) ^ (-(-(k : ℤ))) *
        normalizedL2On (translatedCube d (-(k : ℤ)) x)
          (fun y ↦ U y - averageOn (translatedCube d (-(k : ℤ)) x) U) + Sdef)) :
    let B : Set (SpatialCoordinates d) :=
      Metric.ball x (qside * (3 : ℝ) ^ (-(D : ℤ)) / 2) ∩
        (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))
    normalizedL2On B (fun y => U y - (volume.real B)⁻¹ * ∫ t in B, U t) ≤
      Real.sqrt (2 ^ d) * eA * (3 : ℝ) ^ (-(D : ℝ)) *
        (Real.sqrt (3 ^ d) *
          normalizedL2On (Metric.ball qcenter (3 * qside / 2))
            (fun y => U y - (volume.real (Metric.ball qcenter (3 * qside / 2)))⁻¹ *
              ∫ t in Metric.ball qcenter (3 * qside / 2), U t) + qside * Sdef) := by
  intro B
  set Kset := closedBall qcenter (3 * qside / 2) with hKset
  have hK : IsCompact Kset := isCompact_closedBall _ _
  have hxc : x ∈ closedBall qcenter (qside / 2) := ball_subset_closedBall hx
  have hρ : 0 < qside * (3 : ℝ) ^ (-(D : ℤ)) :=
    mul_pos hqpos (aux_in_deterministic_regularity_three_zpow_pos D)
  have hρs : qside * (3 : ℝ) ^ (-(D : ℤ)) ≤ qside :=
    mul_le_of_le_one_right hqpos.le (aux_in_deterministic_regularity_three_zpow_le_one D)
  -- the bottom window
  have hn : translatedCube d (-((k : ℤ) + (D : ℤ))) x =
      Metric.ball x (qside * (3 : ℝ) ^ (-(D : ℤ)) / 2) := by
    have e : (3 : ℝ) ^ (-((k : ℤ) + (D : ℤ))) = qside * (3 : ℝ) ^ (-(D : ℤ)) := by
      rw [hqside, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      congr 1; ring
    rw [aux_in_deterministic_regularity_translatedCube_eq_ball, e]
  have hm : translatedCube d (-(k : ℤ)) x = Metric.ball x (qside / 2) := by
    rw [aux_in_deterministic_regularity_translatedCube_eq_ball, hqside]
  have hbotK : Metric.ball x (qside * (3 : ℝ) ^ (-(D : ℤ)) / 2) ⊆ Kset := by
    intro y hy
    rw [mem_ball] at hy
    rw [mem_closedBall] at hxc ⊢
    have := dist_triangle y x qcenter
    linarith
  have htopK : Metric.ball x (qside / 2) ⊆ Metric.ball qcenter (3 * qside / 2) := by
    intro y hy
    rw [mem_ball] at hy ⊢
    rw [mem_closedBall] at hxc
    have := dist_triangle y x qcenter
    linarith
  have hqpK : Metric.ball qcenter (3 * qside / 2) ⊆ Kset := ball_subset_closedBall
  obtain ⟨hlo, -⟩ := aux_in_deterministic_regularity_window_volume qcenter x hρ hρs hxc
  have hBpos : 0 < volume.real B := lt_of_lt_of_le (by positivity) hlo
  -- step 1: `B` inside the bottom window
  have h1 := aux_in_deterministic_regularity_osc_sub_le hK hU hbotK
    (inter_subset_left : B ⊆ _) hBpos
  have hs1 : Real.sqrt (volume.real (Metric.ball x (qside * (3 : ℝ) ^ (-(D : ℤ)) / 2)) /
      volume.real B) ≤ Real.sqrt (2 ^ d) := by
    apply Real.sqrt_le_sqrt
    rw [aux_in_deterministic_regularity_volume_ball x (by positivity), div_le_iff₀ hBpos]
    calc (2 * (qside * (3 : ℝ) ^ (-(D : ℤ)) / 2)) ^ d
        = 2 ^ d * (qside * (3 : ℝ) ^ (-(D : ℤ)) / 2) ^ d := by rw [mul_pow]
      _ ≤ 2 ^ d * volume.real B := mul_le_mul_of_nonneg_left hlo (by positivity)
  -- step 2: the top window inside `qp`
  have hmpos : 0 < volume.real (Metric.ball x (qside / 2)) := by
    rw [aux_in_deterministic_regularity_volume_ball x (by positivity)]; positivity
  have h2 := aux_in_deterministic_regularity_osc_sub_le hK hU hqpK htopK hmpos
  have hs2 : Real.sqrt (volume.real (Metric.ball qcenter (3 * qside / 2)) /
      volume.real (Metric.ball x (qside / 2))) = Real.sqrt (3 ^ d) := by
    rw [aux_in_deterministic_regularity_volume_ball x (by positivity),
      aux_in_deterministic_regularity_volume_ball qcenter (by positivity), ← div_pow]
    congr 2
    field_simp
  rw [hs2] at h2
  -- step 3: the iteration inequality, rescaled
  rw [hn, hm] at hiter
  have hscale : (3 : ℝ) ^ (-(-((k : ℤ) + (D : ℤ)))) =
      qside⁻¹ * ((3 : ℝ) ^ (-(D : ℝ)))⁻¹ := by
    calc (3 : ℝ) ^ (-(-((k : ℤ) + (D : ℤ)))) = (3 : ℝ) ^ ((k : ℤ) + (D : ℤ)) := by
          rw [neg_neg]
      _ = (3 : ℝ) ^ (k : ℤ) * (3 : ℝ) ^ (D : ℤ) := zpow_add₀ (by norm_num) _ _
      _ = ((3 : ℝ) ^ (-(k : ℤ)))⁻¹ * ((3 : ℝ) ^ (-(D : ℝ)))⁻¹ := by
          rw [zpow_neg, inv_inv, Real.rpow_neg (by norm_num), inv_inv, Real.rpow_natCast,
            zpow_natCast, zpow_natCast]
      _ = qside⁻¹ * ((3 : ℝ) ^ (-(D : ℝ)))⁻¹ := by rw [hqside]
  have hscale' : (3 : ℝ) ^ (-(-(k : ℤ))) = qside⁻¹ := by
    rw [hqside, neg_neg, zpow_neg, inv_inv]
  rw [hscale, hscale'] at hiter
  have h3pos : 0 < (3 : ℝ) ^ (-(D : ℝ)) := by positivity
  set ob := normalizedL2On (Metric.ball x (qside * (3 : ℝ) ^ (-(D : ℤ)) / 2))
    (fun y ↦ U y - averageOn (Metric.ball x (qside * (3 : ℝ) ^ (-(D : ℤ)) / 2)) U) with hob
  set ot := normalizedL2On (Metric.ball x (qside / 2))
    (fun y ↦ U y - averageOn (Metric.ball x (qside / 2)) U) with hot
  have hiter' : ob ≤ eA * (3 : ℝ) ^ (-(D : ℝ)) * (ot + qside * Sdef) := by
    have hq' : 0 < qside⁻¹ * ((3 : ℝ) ^ (-(D : ℝ)))⁻¹ := by positivity
    have := hiter
    rw [← le_div_iff₀' hq'] at this
    calc ob ≤ eA * (qside⁻¹ * ot + Sdef) / (qside⁻¹ * ((3 : ℝ) ^ (-(D : ℝ)))⁻¹) := this
      _ = eA * (3 : ℝ) ^ (-(D : ℝ)) * (ot + qside * Sdef) := by
          field_simp
  have hob' : ob = normalizedL2On (Metric.ball x (qside * (3 : ℝ) ^ (-(D : ℤ)) / 2))
      (fun y => U y - (volume.real (Metric.ball x (qside * (3 : ℝ) ^ (-(D : ℤ)) / 2)))⁻¹ *
        ∫ t in Metric.ball x (qside * (3 : ℝ) ^ (-(D : ℤ)) / 2), U t) := rfl
  have hot' : ot = normalizedL2On (Metric.ball x (qside / 2))
      (fun y => U y - (volume.real (Metric.ball x (qside / 2)))⁻¹ *
        ∫ t in Metric.ball x (qside / 2), U t) := rfl
  rw [← hob'] at h1
  rw [← hot'] at h2
  have hob0 : 0 ≤ ob := Real.sqrt_nonneg _
  calc normalizedL2On B (fun y => U y - (volume.real B)⁻¹ * ∫ t in B, U t)
      ≤ Real.sqrt (volume.real (Metric.ball x (qside * (3 : ℝ) ^ (-(D : ℤ)) / 2)) /
          volume.real B) * ob := h1
    _ ≤ Real.sqrt (2 ^ d) * ob := mul_le_mul_of_nonneg_right hs1 hob0
    _ ≤ Real.sqrt (2 ^ d) * (eA * (3 : ℝ) ^ (-(D : ℝ)) * (ot + qside * Sdef)) :=
        mul_le_mul_of_nonneg_left hiter' (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (2 ^ d) * (eA * (3 : ℝ) ^ (-(D : ℝ)) *
          (Real.sqrt (3 ^ d) *
            normalizedL2On (Metric.ball qcenter (3 * qside / 2))
              (fun y => U y - (volume.real (Metric.ball qcenter (3 * qside / 2)))⁻¹ *
                ∫ t in Metric.ball qcenter (3 * qside / 2), U t) + qside * Sdef)) := by
        gcongr
    _ = _ := by ring

end SubdiffusiveProcess.Paper
