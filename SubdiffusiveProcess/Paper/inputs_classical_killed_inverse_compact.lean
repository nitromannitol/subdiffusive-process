import SubdiffusiveProcess.Paper.inputs_classical_e4_h1_finite
import SubdiffusiveProcess.Paper.inputs_classical_e4_rellich
import SubdiffusiveProcess.Sobolev.ResponseSpace
import SubdiffusiveProcess.Geometry.Cube
import Mathlib.Analysis.Normed.Operator.Compact




set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace SubdiffusiveProcess Filter
open scoped NNReal ENNReal Topology

namespace Paper
noncomputable section
namespace KIC
open F5

variable {d : ℕ}

theorem aux_kic_gradSq_bounded (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (u : weakSobolevGraph (centeredCube z r hr)) (φ : ℕ → SpatialCoordinates d → ℝ)
    (hgrad : ∀ i : Fin d, Tendsto (fun n => eLpNorm
          (fun x => fderiv ℝ (φ n) x (Pi.single i 1) - (u : SobolevData (centeredCube z r hr)).2 i x) 2
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))) atTop (𝓝 0)) :
    ∀ᶠ n in atTop,
      ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)), ENNReal.ofReal (aux_f5_gradSq (φ n) x) ≤
        ∑ i : Fin d, (1 + eLpNorm ((u : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ) 2
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))) ^ 2 := by
  classical
  set μ := volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) with hμ
  set U2 : Fin d → ℝ≥0∞ := fun i => eLpNorm ((u : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ) 2 μ
  have hU2 : ∀ i, U2 i < ⊤ := fun i => Lp.eLpNorm_lt_top _
  have hev : ∀ᶠ n in atTop, ∀ i : Fin d, eLpNorm
      (fun x => fderiv ℝ (φ n) x (Pi.single i 1) - (u : SobolevData (centeredCube z r hr)).2 i x) 2 μ ≤ 1 := by
    rw [Filter.eventually_all]
    intro i
    exact (hgrad i).eventually (Iic_mem_nhds (by norm_num))
  filter_upwards [hev] with n hn
  -- each coordinate: ∫⁻ ofReal(f^2) = (eLpNorm f 2)^2 ≤ (1 + U2 i)^2
  have hcoord : ∀ i : Fin d, ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ENNReal.ofReal ((fderiv ℝ (φ n) x (Pi.single i 1)) ^ 2) ≤ (1 + U2 i) ^ 2 := by
    intro i
    set f : SpatialCoordinates d → ℝ := fun x => fderiv ℝ (φ n) x (Pi.single i 1) with hf
    set w : SpatialCoordinates d → ℝ := ((u : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ)
    have hfm : AEStronglyMeasurable f μ :=
      (measurable_fderiv_apply_const ℝ (φ n) (Pi.single i 1)).aestronglyMeasurable
    have hwm : AEStronglyMeasurable w μ := Lp.aestronglyMeasurable _
    have hsq : ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)), ENNReal.ofReal (f x ^ 2) =
        eLpNorm f 2 μ ^ 2 := by
      rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
      refine lintegral_congr fun x => ?_
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    have htri : eLpNorm f 2 μ ≤ 1 + U2 i := by
      calc eLpNorm f 2 μ = eLpNorm ((fun x => f x - w x) + w) 2 μ := by congr 1; funext x; simp
        _ ≤ eLpNorm (fun x => f x - w x) 2 μ + eLpNorm w 2 μ :=
            eLpNorm_add_le (hfm.sub hwm) hwm (by norm_num)
        _ ≤ 1 + U2 i := add_le_add (hn i) le_rfl
    rw [hsq]
    exact pow_le_pow_left₀ (zero_le _) htri 2
  calc ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)), ENNReal.ofReal (aux_f5_gradSq (φ n) x)
      = ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ∑ i : Fin d, ENNReal.ofReal ((fderiv ℝ (φ n) x (Pi.single i 1)) ^ 2) := by
        refine lintegral_congr fun x => ?_
        rw [aux_f5_gradSq, ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
    _ ≤ ∑ i : Fin d, ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ENNReal.ofReal ((fderiv ℝ (φ n) x (Pi.single i 1)) ^ 2) :=
        (lintegral_finset_sum _ fun i _ =>
          ((measurable_fderiv_apply_const ℝ (φ n) (Pi.single i 1)).pow_const 2).ennreal_ofReal).le
    _ ≤ ∑ i : Fin d, (1 + U2 i) ^ 2 := Finset.sum_le_sum fun i _ => hcoord i


/-- The Gagliardo double integral of an `H¹` graph element is bounded by its gradient norms. -/
theorem aux_kic_gagliardo (hd : 2 ≤ d) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ u : weakSobolevGraph (centeredCube z r hr),
      ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
            aux_f5_gq s ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) x y ≤
        C * ∑ i : Fin d, (1 + eLpNorm ((u : SobolevData (centeredCube z r hr)).2 i :
          SpatialCoordinates d → ℝ) 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))) ^ 2 := by
  obtain ⟨C, hC, hsm⟩ := aux_f5_smooth_bound hd z hr s hs0 hs1
  refine ⟨C, hC, fun u => ?_⟩
  obtain ⟨φ, hφ, hval, hgrad⟩ := aux_f5_smooth_approx z hr u
  have hBev := aux_kic_gradSq_bounded z hr u φ hgrad
  have hM : ∀ᶠ n in atTop, ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)), aux_f5_gq s (φ n) x y ≤
        C * ∑ i : Fin d, (1 + eLpNorm ((u : SobolevData (centeredCube z r hr)).2 i :
          SpatialCoordinates d → ℝ) 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))) ^ 2 := by
    filter_upwards [hBev] with n hn
    exact (hsm (φ n) (hφ n)).trans (mul_le_mul_right hn C)
  exact aux_f5_fatou_limit z hr s _ φ (Lp.aestronglyMeasurable _) (fun n => (hφ n).continuous) hval _ hM

theorem aux_kic_eLpNorm_eq {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    (f : DomainL2 (centeredCube z r hr)) :
    eLpNorm (f : SpatialCoordinates d → ℝ) 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) =
      ENNReal.ofReal ‖f‖ := by
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)]

/-- The normalized fractional norm of an `H¹` graph element is controlled by its `H¹` norms. -/
theorem aux_kic_sqnorm_le (hd : 2 ≤ d) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (s : Set.Ioo (0 : ℝ) 1) (C : ℝ≥0∞) (hC : C < ⊤)
    (hgag : ∀ u : weakSobolevGraph (centeredCube z r hr),
      ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
            aux_f5_gq s ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) x y ≤
        C * ∑ i : Fin d, (1 + eLpNorm ((u : SobolevData (centeredCube z r hr)).2 i :
          SpatialCoordinates d → ℝ) 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))) ^ 2)
    (u : weakSobolevGraph (centeredCube z r hr)) (R R' : ℝ)
    (hR : ∀ i, ‖(u : SobolevData (centeredCube z r hr)).2 i‖ ≤ R)
    (hR' : ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤ R') :
    SubdiffusiveProcess.Lane4.cubeFractionalSqNorm hd z r hr s (u : SobolevData (centeredCube z r hr)).1 ≤
      (ENNReal.ofReal (s : ℝ) / volume (centeredCube z r hr : Set (SpatialCoordinates d)) *
        (C * ∑ _i : Fin d, (1 + ENNReal.ofReal R) ^ 2)).toReal +
      R' ^ 2 / volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  have hvol := SubdiffusiveProcess.centeredCube_volume_pos z hr
  have hvolne : volume (centeredCube z r hr : Set (SpatialCoordinates d)) ≠ 0 := by
    intro h; rw [Measure.real, h] at hvol; simp at hvol
  have hfin' : ENNReal.ofReal (s : ℝ) / volume (centeredCube z r hr : Set (SpatialCoordinates d)) *
      (C * ∑ _i : Fin d, (1 + ENNReal.ofReal R) ^ 2) < ⊤ := by
    refine ENNReal.mul_lt_top (ENNReal.div_lt_top ENNReal.ofReal_ne_top hvolne) (ENNReal.mul_lt_top hC ?_)
    exact ENNReal.sum_lt_top.mpr fun i _ =>
      ENNReal.pow_lt_top (ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, ENNReal.ofReal_lt_top⟩)
  set A : ℝ≥0∞ := ENNReal.ofReal (s : ℝ) / volume (centeredCube z r hr : Set (SpatialCoordinates d)) *
    ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ENNReal.ofReal (∑ _i : Fin 1, (((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) x -
          ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^ ((d : ℝ) + 2 * (s : ℝ)) with hA
  have hAle : A ≤ ENNReal.ofReal (s : ℝ) / volume (centeredCube z r hr : Set (SpatialCoordinates d)) *
      (C * ∑ _i : Fin d, (1 + ENNReal.ofReal R) ^ 2) := by
    rw [hA]
    refine mul_le_mul_right ?_ _
    have h1 := hgag u
    simp only [Fin.sum_univ_one]
    refine h1.trans (mul_le_mul_right (Finset.sum_le_sum fun i _ => ?_) C)
    rw [aux_kic_eLpNorm_eq]
    gcongr
    exact hR i
  have hAfin : A < ⊤ := hAle.trans_lt hfin'
  have hsemi : ((SubdiffusiveProcess.cubeFractionalL2Seminorm hd z r hr s
      (fun _ : Fin 1 => (u : SobolevData (centeredCube z r hr)).1)).toReal) ^ 2 = A.toReal := by
    unfold SubdiffusiveProcess.cubeFractionalL2Seminorm
    rw [← hA, ← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt ENNReal.toReal_nonneg]
  unfold SubdiffusiveProcess.Lane4.cubeFractionalSqNorm SubdiffusiveProcess.Lane4.cubeFractionalVecSqNorm
    SubdiffusiveProcess.Lane4.cubeFractionalVecSeminormSq
  rw [hsemi, Fin.sum_univ_one]
  refine add_le_add ((ENNReal.toReal_le_toReal hAfin.ne hfin'.ne).mpr hAle) ?_
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hR' 2) hvol.le

/-- Energy estimate for the inverse on a response space. -/
theorem aux_kic_energy {Ω : Opens (SpatialCoordinates d)} (S : ResponseSpace Ω)
    (a : PositiveCoefficient Ω) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ f : DomainL2 Ω,
      ‖subspaceGradient S.space (responseSolution S a
        ((sobolevVolumeLoad f).comp S.space.subtypeL))‖ ≤ Kc * ‖f‖ := by
  obtain ⟨K, hK⟩ := S.poincare
  obtain ⟨c, hc, ha⟩ := a.property
  obtain ⟨c', hc', hb⟩ := weightedGradientForm_coercive a.val hc ha
  refine ⟨K / c', div_nonneg K.2 hc'.le, fun f => ?_⟩
  have h1 := responseSolution_spec S a ((sobolevVolumeLoad f).comp S.space.subtypeL)
    (responseSolution S a ((sobolevVolumeLoad f).comp S.space.subtypeL))
  generalize responseSolution S a ((sobolevVolumeLoad f).comp S.space.subtypeL) = u at h1 ⊢
  have h2 : ((sobolevVolumeLoad f).comp S.space.subtypeL) u =
      inner ℝ f ((u : SobolevData Ω).1) := rfl
  have h3 : responseForm S a u u =
      weightedGradientForm a.val (subspaceGradient S.space u) (subspaceGradient S.space u) := rfl
  have h4 := hb (subspaceGradient S.space u)
  have h5 : inner ℝ f ((u : SobolevData Ω).1) ≤ ‖f‖ * ‖(u : SobolevData Ω).1‖ :=
    real_inner_le_norm _ _
  have h6 : ‖(u : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient S.space u‖ := hK u
  have hg0 : 0 ≤ ‖subspaceGradient S.space u‖ := norm_nonneg _
  have hf0 : 0 ≤ ‖f‖ := norm_nonneg _
  have hK0 : (0 : ℝ) ≤ K := K.2
  have hmain : c' * ‖subspaceGradient S.space u‖ * ‖subspaceGradient S.space u‖ ≤
      K * ‖f‖ * ‖subspaceGradient S.space u‖ := by
    calc c' * ‖subspaceGradient S.space u‖ * ‖subspaceGradient S.space u‖
        ≤ weightedGradientForm a.val (subspaceGradient S.space u) (subspaceGradient S.space u) := h4
      _ = inner ℝ f ((u : SobolevData Ω).1) := by rw [← h3, h1, h2]
      _ ≤ ‖f‖ * ‖(u : SobolevData Ω).1‖ := h5
      _ ≤ ‖f‖ * (K * ‖subspaceGradient S.space u‖) := mul_le_mul_of_nonneg_left h6 hf0
      _ = K * ‖f‖ * ‖subspaceGradient S.space u‖ := by ring
  have hkey : c' * ‖subspaceGradient S.space u‖ ≤ K * ‖f‖ := by
    rcases hg0.eq_or_lt with hg | hg
    · rw [← hg, mul_zero]; exact mul_nonneg hK0 hf0
    · exact le_of_mul_le_mul_right hmain hg
  rw [div_mul_eq_mul_div, le_div_iff₀ hc']
  linarith

end KIC

open KIC in
/-- The killed inverse for a fixed bounded positive coefficient on a bounded cube is compact on L2. -/
theorem inputs_classical_killed_inverse_compact
    (d : ℕ) (_hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
      ‖w.val.1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (a : PositiveCoefficient (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (_hG : ∀ f, G f =
      (responseSolution (killedResponseSpace hP) a
        ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL)).val.1) :
    IsCompactOperator G := by
  classical
  have hvol := SubdiffusiveProcess.centeredCube_volume_pos z hr
  obtain ⟨Kc, hKc0, hen⟩ := aux_kic_energy (killedResponseSpace hP) a
  have hP' := hP
  obtain ⟨K, hK⟩ := hP'
  let s : Set.Ioo (0 : ℝ) 1 := ⟨1 / 2, by norm_num, by norm_num⟩
  obtain ⟨C, hC, hgag⟩ := aux_kic_gagliardo _hd z hr (s : ℝ) s.2.1 s.2.2
  -- the solution of the load `f`, as a weak graph element
  let U : DomainL2 (centeredCube z r hr) → weakSobolevGraph (centeredCube z r hr) := fun f =>
    ⟨(responseSolution (killedResponseSpace hP) a
        ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL)).val,
      killedSobolevGraph_le_weakSobolevGraph (responseSolution (killedResponseSpace hP) a
        ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL)).property⟩
  have hGU : ∀ f, G f = ((U f : SobolevData (centeredCube z r hr)).1) := fun f => _hG f
  have hgradU : ∀ f, ‖f‖ ≤ 1 → ∀ i, ‖(U f : SobolevData (centeredCube z r hr)).2 i‖ ≤ Kc := by
    intro f hf i
    have hg := hen f
    calc ‖(U f : SobolevData (centeredCube z r hr)).2 i‖
        = ‖(subspaceGradient (killedResponseSpace hP).space (responseSolution (killedResponseSpace hP) a
            ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL))) i‖ := rfl
      _ ≤ ‖subspaceGradient (killedResponseSpace hP).space (responseSolution (killedResponseSpace hP) a
            ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL))‖ := PiLp.norm_apply_le _ _
      _ ≤ Kc * ‖f‖ := hg
      _ ≤ Kc * 1 := mul_le_mul_of_nonneg_left hf hKc0
      _ = Kc := mul_one _
  have hL2U : ∀ f, ‖f‖ ≤ 1 → ‖(U f : SobolevData (centeredCube z r hr)).1‖ ≤ K * Kc := by
    intro f hf
    calc ‖(U f : SobolevData (centeredCube z r hr)).1‖
        ≤ K * ‖subspaceGradient (killedResponseSpace hP).space (responseSolution (killedResponseSpace hP) a
            ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL))‖ := hK _
      _ ≤ K * (Kc * ‖f‖) := mul_le_mul_of_nonneg_left (hen f) K.2
      _ ≤ K * Kc := mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hKc0 hf) K.2
  set B : ℝ := (ENNReal.ofReal (s : ℝ) / volume (centeredCube z r hr : Set (SpatialCoordinates d)) *
      (C * ∑ _i : Fin d, (1 + ENNReal.ofReal Kc) ^ 2)).toReal +
    (K * Kc) ^ 2 / volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) with hB
  refine (isCompactOperator_iff_isCompact_closure_image_ball G.toLinearMap one_pos).mpr ?_
  apply IsSeqCompact.isCompact
  intro x hx
  have happrox : ∀ n, ∃ f : DomainL2 (centeredCube z r hr), ‖f‖ < 1 ∧
      dist (x n) (G f) < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨y, ⟨f, hf, rfl⟩, hy⟩ := Metric.mem_closure_iff.mp (hx n) (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨f, mem_ball_zero_iff.mp hf, hy⟩
  choose f hf1 hfd using happrox
  let v : ℕ → DomainL2 (centeredCube z r hr) := fun n => G (f n)
  have hfinite : ∀ n, SubdiffusiveProcess.cubeFractionalL2Seminorm _hd z r hr s
      (fun _ : Fin 1 => v n) < ⊤ := by
    intro n
    have h := inputs_classical_e4_h1_finite d _hd s z r hr (U (f n))
    simpa only [v, hGU] using h
  have hbound : ∀ n, SubdiffusiveProcess.Lane4.cubeFractionalSqNorm _hd z r hr s (v n) ≤ B := by
    intro n
    have h := aux_kic_sqnorm_le _hd z hr s C hC hgag (U (f n)) Kc (K * Kc)
      (hgradU (f n) (hf1 n).le) (hL2U (f n) (hf1 n).le)
    simpa only [v, hGU] using h
  obtain ⟨phi, w, hphi, hconv⟩ := inputs_classical_e4_rellich d _hd s z r hr v B hfinite hbound
  refine ⟨w, ?_, phi, hphi, ?_⟩
  · refine mem_closure_of_tendsto hconv (Eventually.of_forall fun n => ?_)
    exact ⟨f (phi n), mem_ball_zero_iff.mpr (hf1 (phi n)), rfl⟩
  · rw [tendsto_iff_dist_tendsto_zero]
    have hsmall : Tendsto (fun n : ℕ => 1 / ((phi n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hphi.tendsto_atTop
    have hvw : Tendsto (fun n => dist (v (phi n)) w) atTop (𝓝 0) :=
      (tendsto_iff_dist_tendsto_zero.mp hconv)
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) (by simpa using hsmall.add hvw)
    calc dist ((x ∘ phi) n) w ≤ dist (x (phi n)) (v (phi n)) + dist (v (phi n)) w := dist_triangle _ _ _
      _ ≤ ((phi n : ℝ) + 1)⁻¹ + dist (v (phi n)) w := by
          rw [← one_div]
          gcongr
          exact (hfd (phi n)).le

end
end Paper
