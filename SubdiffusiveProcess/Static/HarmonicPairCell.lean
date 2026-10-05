module

public import SubdiffusiveProcess.Static.HarmonicPairGeometry
public import SubdiffusiveProcess.Static.CutoffHarmonicCellCarrier

@[expose] public section

/-! # Native cell corrections and exact energy scaling -/
open MeasureTheory Homogenization Metric
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open scoped ENNReal Pointwise
noncomputable section
namespace SubdiffusiveProcess.Static

/-- Unit-cell growth extends to every radius because its diameter is at most one. -/
theorem pair_unit_energy_all_radii {d : ℕ} (hd : 1 ≤ d)
    (Phi : Vec d → ℝ≥0∞) {G : ℝ} (hG : 0 ≤ G)
    (hgrowth : ∀ x ∈ openCubeSet (originCube d 0), ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∫⁻ w in ball x r ∩ openCubeSet (originCube d 0), Phi w ≤
        ENNReal.ofReal (G * r ^ ((d : ℝ) - 1 / 2)))
    (x : Vec d) (hx : x ∈ openCubeSet (originCube d 0)) {r : ℝ} (hr : 0 < r) :
    ∫⁻ w in ball x r ∩ openCubeSet (originCube d 0), Phi w ≤
      ENNReal.ofReal (G * r ^ ((d : ℝ) - 1 / 2)) := by
  by_cases hr1 : r ≤ 1
  · exact hgrowth x hx r hr hr1
  · have hraw := hgrowth x hx 1 zero_lt_one le_rfl
    rw [Set.inter_eq_right.mpr (pair_unitCube_subset_ball_one hx)] at hraw
    simp only [Real.one_rpow, mul_one] at hraw
    refine (lintegral_mono_set Set.inter_subset_right).trans (hraw.trans ?_)
    apply ENNReal.ofReal_le_ofReal
    have ht : 0 ≤ (d : ℝ) - 1 / 2 := by
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    exact le_mul_of_one_le_right hG (Real.one_le_rpow (by linarith) ht)

/-- A unit-cell Dirichlet solution pushes to a correction with raw cost
`h^(-3/2)`, including physical windows larger than the cell. -/
theorem exists_pair_cell_correction {d : ℕ} (hd : 1 ≤ d)
    (y : Vec d) {h T K B : ℝ} (hh : 0 < h) (hT : 0 ≤ T) (hK : 0 ≤ K) (_hB : 0 ≤ B)
    (A b : Vec d → ℝ) (hb : Continuous b) (hbpos : ∀ x, 0 < b x)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (hf01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hcomp : ∀ w ∈ openCubeSet (originCube d 0), A (y + h • w) ≤ T * b w)
    (hgrowth : ∀ u : H1Function (openCubeSet (originCube d 0)),
      IsWeaklyHarmonicOn b (openCubeSet (originCube d 0)) u →
      HasZeroTraceDifferenceOn (openCubeSet (originCube d 0)) u
        (cutoffHarmonicCellDatum (fun w => f (y + h • w))
          (pair_affine_smooth_compact y hh f hf hc).1
          (pair_affine_smooth_compact y hh f hf hc).2) →
      ∀ x ∈ openCubeSet (originCube d 0), ∀ r : ℝ, 0 < r → r ≤ 1 →
        ∫⁻ w in ball x r ∩ openCubeSet (originCube d 0),
          ENNReal.ofReal (b w * vecDot (u.grad w) (u.grad w)) ≤
            ENNReal.ofReal (K * B ^ 2 * r ^ ((d : ℝ) - 1 / 2))) :
    ∃ e : H10Function (ball y (h / 2)),
      (∀ᵐ x ∂(volume.restrict (ball y (h / 2))),
        0 ≤ f x + e.toFun x ∧ f x + e.toFun x ≤ 1) ∧
      ∀ x ∈ ball y (h / 2), ∀ r : ℝ, 0 < r → r ≤ 1 →
        ∫⁻ w in ball x r ∩ ball y (h / 2),
          ENNReal.ofReal (A w * vecDot (aux_hcut_gradVec f w + e.grad w)
            (aux_hcut_gradVec f w + e.grad w)) ≤
          ENNReal.ofReal (T * K * B ^ 2 * h ^ (-(3 / 2 : ℝ)) *
            r ^ ((d : ℝ) - 1 / 2)) := by
  have : NeZero d := ⟨by omega⟩
  let f0 := fun w => f (y + h • w)
  let datum := cutoffHarmonicCellDatum f0
    (pair_affine_smooth_compact y hh f hf hc).1
    (pair_affine_smooth_compact y hh f hf hc).2

  have hcpt := isCompact_closedBall (0 : Vec d) (1 / 2)
  obtain ⟨lam, hlam, hlb⟩ := hcpt.exists_forall_le' hb.continuousOn
    (a := 0) (fun x _ => hbpos x)
  obtain ⟨Lam, hLb⟩ := hcpt.exists_bound_of_continuousOn hb.continuousOn
  have hbnd : ∀ x ∈ openCubeSet (originCube d 0), lam ≤ b x ∧ b x ≤ Lam := by
    intro x hx
    rw [unitCube_eq_ball] at hx
    exact ⟨hlb x (ball_subset_closedBall hx),
      (le_abs_self _).trans (hLb x (ball_subset_closedBall hx))⟩
  have hEll := _root_.SubdiffusiveProcess.isEllipticFieldOn_scalar (isOpen_openCubeSet _).measurableSet
    hb.measurable hlam hbnd
  have hgeom := isOpenBoundedConvexDomain_openCubeSet (originCube d 0)
  have hne : (openCubeSet (originCube d 0)).Nonempty := by
    rw [unitCube_eq_ball]
    exact ⟨0, mem_ball_self (by norm_num)⟩
  obtain ⟨u, hu, htr⟩ := exists_isWeaklyHarmonicOn_and_hasZeroTraceDifferenceOn
    hgeom hne hEll datum
  have hbd : ∀ᵐ x ∂volume.restrict (openCubeSet (originCube d 0)),
      lam ≤ b x ∧ b x ≤ Lam := by
    filter_upwards [ae_restrict_mem (isOpen_openCubeSet _).measurableSet] with x hx
    exact hbnd x hx
  have hlo := le_ae_of_harmonic hgeom hlam hb.aestronglyMeasurable hbd hu htr
    (m := 0) (fun x _ => (hf01 (y + h • x)).1)
  have hup := ae_le_of_harmonic hgeom hlam hb.aestronglyMeasurable hbd hu htr
    (M := 1) (fun x _ => (hf01 (y + h • x)).2)
  have henergy := hgrowth u hu htr
  obtain ⟨e0, hef, heg⟩ := htr
  let e := pairCellPushH10 y hh e0
  have hinv : ∀ w : Vec d, h⁻¹ • (y + h • w - y) = w := by
    intro w
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hh.ne', one_smul]
  have hgrad : ∀ w, aux_hcut_gradVec f (y + h • w) + e.grad (y + h • w) =
      h⁻¹ • u.grad w := by
    intro w
    rw [show e.grad (y + h • w) = h⁻¹ • e0.grad w by
      simp only [e, pairCellPushH10_grad, hinv]]
    rw [heg w]
    change _ = h⁻¹ • (aux_hcut_gradVec f0 w + e0.grad w)
    rw [show aux_hcut_gradVec f0 w = h • aux_hcut_gradVec f (y + h • w) from
      pair_affine_gradVec y h f (hf.differentiable (by simp)) w,
      smul_add, smul_smul, inv_mul_cancel₀ hh.ne', one_smul]
  refine ⟨e, ?_, ?_⟩
  · have hb01 : ∀ᵐ w ∂volume, w ∈ openCubeSet (originCube d 0) →
        0 ≤ u.toFun w ∧ u.toFun w ≤ 1 := by
      apply (ae_restrict_iff' (isOpen_openCubeSet _).measurableSet).mp
      exact hlo.and hup
    have hqm : Measure.QuasiMeasurePreserving (fun x : Vec d => h⁻¹ • (x - y))
        volume volume :=
      (Measure.quasiMeasurePreserving_smul (μ := volume) (inv_ne_zero hh.ne')).comp
        (measurePreserving_sub_right volume y).quasiMeasurePreserving
    filter_upwards [ae_restrict_of_ae (hqm.ae hb01), ae_restrict_mem measurableSet_ball]
      with x hx hxcell
    have hunit : h⁻¹ • (x - y) ∈ openCubeSet (originCube d 0) := by
      rw [← pair_affine_preimage_cell y hh]
      change y + h • (h⁻¹ • (x - y)) ∈ ball y (h / 2)
      simpa [smul_smul, hh.ne'] using hxcell
    have heval : f x + e.toFun x = u.toFun (h⁻¹ • (x - y)) := by
      rw [hef]
      simp only [e, pairCellPushH10_fun, datum, cutoffHarmonicCellDatum,
        H1Function.ofContDiff, f0, smul_smul, mul_inv_cancel₀ hh.ne', one_smul,
        add_sub_cancel]
    rw [heval]
    exact hx hunit
  · intro x hx r hr _
    let x0 := h⁻¹ • (x - y)
    have hx0 : x0 ∈ openCubeSet (originCube d 0) := by
      rw [← pair_affine_preimage_cell y hh]
      change y + h • x0 ∈ ball y (h / 2)
      simpa [x0, smul_smul, hh.ne'] using hx
    have hraw := pair_unit_energy_all_radii hd
      (fun w => ENNReal.ofReal (b w * vecDot (u.grad w) (u.grad w)))
      (mul_nonneg hK (sq_nonneg B)) henergy x0 hx0 (div_pos hr hh)
    rw [lintegral_window_affine y hh (measurableSet_ball.inter measurableSet_ball),
      Set.preimage_inter, pair_affine_preimage_ball y x hh, pair_affine_preimage_cell y hh]
    have hpoint : ∀ᵐ w ∂volume.restrict (ball x0 (r / h) ∩ openCubeSet (originCube d 0)),
        ENNReal.ofReal (A (y + h • w) * vecDot
          (aux_hcut_gradVec f (y + h • w) + e.grad (y + h • w))
          (aux_hcut_gradVec f (y + h • w) + e.grad (y + h • w))) ≤
        ENNReal.ofReal (T * h⁻¹ ^ 2) *
          ENNReal.ofReal (b w * vecDot (u.grad w) (u.grad w)) := by
      filter_upwards [ae_restrict_mem (measurableSet_ball.inter (isOpen_openCubeSet _).measurableSet)]
        with w hw
      rw [hgrad w, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [Homogenization.vecDot_smul_left, Homogenization.vecDot_smul_right]
      have h := mul_le_mul_of_nonneg_right (hcomp w hw.2)
        (mul_nonneg (sq_nonneg h⁻¹) (vecNormSq_nonneg (u.grad w)))
      dsimp only [vecNormSq] at h
      nlinarith only [h]
    refine (mul_le_mul_of_nonneg_left (lintegral_mono_ae hpoint) zero_le).trans ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hraw zero_le) zero_le).trans_eq ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ h ^ d),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ h ^ d * (T * h⁻¹ ^ 2))]
    congr 1
    have hpowers : h ^ d * h⁻¹ ^ 2 * (r / h) ^ ((d : ℝ) - 1 / 2) =
        h ^ (-(3 / 2 : ℝ)) * r ^ ((d : ℝ) - 1 / 2) := by
      rw [Real.div_rpow hr.le hh.le, ← Real.rpow_natCast h d,
        inv_pow, ← Real.rpow_two h, ← Real.rpow_neg hh.le]
      have hs : h ^ (d : ℝ) * h ^ (-2 : ℝ) =
          h ^ (-(3 / 2 : ℝ)) * h ^ ((d : ℝ) - 1 / 2) := by
        rw [← Real.rpow_add hh, ← Real.rpow_add hh]
        congr 1
        ring
      rw [hs]
      field_simp
    calc
      _ = T * K * B ^ 2 * (h ^ d * h⁻¹ ^ 2 * (r / h) ^ ((d : ℝ) - 1 / 2)) := by ring
      _ = _ := by rw [hpowers]; ring

end SubdiffusiveProcess.Static
