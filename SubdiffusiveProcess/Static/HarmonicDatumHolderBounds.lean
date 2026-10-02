import SubdiffusiveProcess.Static.HarmonicCellSmoothDatum
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.CenteredDilation
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.WindowSeminorms
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Discharge
import Homogenization.Deterministic.ConstantCoefficientDirichletBesov.PartitionDerivatives

/-! # Quantitative global Hölder bounds for smooth harmonic cell data -/
open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
noncomputable section
namespace SubdiffusiveProcess.Static

/-- A bounded Lipschitz vector field has a dimension-priced half-Hölder bound. -/
theorem half_holder_bound_of_norm_bounds {d : ℕ} (F : Vec d → Vec d)
    {B : ℝ} (hB : 0 ≤ B) (hsize : ∀ x, ‖F x‖ ≤ B)
    (hlip : ∀ x y, ‖F x - F y‖ ≤ B * ‖x - y‖) (W : Set (Vec d)) :
    HolderSeminormBoundOn W (1 / 2) (2 * (d : ℝ) * B) F := by
  intro x _hx y _hy
  let t := euclideanNorm (x - y)
  have ht : 0 ≤ t := euclideanNorm_nonneg _
  rw [← Real.sqrt_eq_rpow]
  by_cases ht1 : t ≤ 1
  · have hts : t ≤ Real.sqrt t := by
      nlinarith [Real.sq_sqrt ht, Real.sqrt_nonneg t]
    calc
      _ ≤ (d : ℝ) * ‖F x - F y‖ := euclideanNorm_le_dimension_mul_norm _
      _ ≤ (d : ℝ) * (B * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left (hlip x y) (Nat.cast_nonneg _)
      _ ≤ (d : ℝ) * (B * t) := by
        gcongr
        exact norm_le_euclideanNorm _
      _ ≤ (d : ℝ) * (B * Real.sqrt t) := by gcongr
      _ ≤ 2 * (d : ℝ) * B * Real.sqrt t := by
        have hnonneg : 0 ≤ (d : ℝ) * B * Real.sqrt t := by positivity
        nlinarith only [hnonneg]
  · have hts : 1 ≤ Real.sqrt t := by
      nlinarith [Real.sq_sqrt ht, Real.sqrt_nonneg t]
    calc
      _ ≤ (d : ℝ) * ‖F x - F y‖ := euclideanNorm_le_dimension_mul_norm _
      _ ≤ (d : ℝ) * (‖F x‖ + ‖F y‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (Nat.cast_nonneg _)
      _ ≤ (d : ℝ) * (B + B) :=
        mul_le_mul_of_nonneg_left (add_le_add (hsize x) (hsize y)) (Nat.cast_nonneg _)
      _ = 2 * (d : ℝ) * B := by ring
      _ ≤ 2 * (d : ℝ) * B * Real.sqrt t := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hts (by positivity)

/-- The native smooth datum gradient is globally bounded and Lipschitz. -/
theorem harmonicDatum_gradient_norm_bounds {d : ℕ}
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    {B : ℝ} (hB : 0 ≤ B) (hb : HarmonicCutoffDatumSizeBound f B) :
    (∀ x, ‖(cutoffHarmonicCellDatum f hf hc).grad x‖ ≤ B) ∧
      ∀ x y, ‖(cutoffHarmonicCellDatum f hf hc).grad x -
        (cutoffHarmonicCellDatum f hf hc).grad y‖ ≤ B * ‖x - y‖ := by
  have hcoord := harmonicCutoffDatum_coordinate_bounds f hf hb
  refine ⟨fun x => (pi_norm_le_iff_of_nonneg hB).mpr (fun i => ?_), ?_⟩
  · exact (hcoord x).1 i
  · intro x y
    have hdf : Differentiable ℝ (fderiv ℝ f) :=
      ((contDiff_succ_iff_fderiv.mp
        (hf.of_le (WithTop.coe_le_coe.mpr le_top) : ContDiff ℝ (1 + 1) f)).2.2).differentiable
          (by simp)
    have hdiff : ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ B * ‖x - y‖ := by
      simpa only [mul_comm] using
        (Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
          (f := fderiv ℝ f) (s := Set.univ) (C := B) (x := y) (y := x)
          (fun z _ => hdf z) (fun z _ => (hb z).2.2)
          convex_univ (Set.mem_univ _) (Set.mem_univ _))
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hB (norm_nonneg _))).mpr
    intro i
    change ‖(fderiv ℝ f x - fderiv ℝ f y) (basisVec i)‖ ≤ _
    exact ((fderiv ℝ f x - fderiv ℝ f y).le_opNorm _).trans
      (by simpa only [Homogenization.norm_basisVec, mul_one] using hdiff)

private theorem vectorSupNormOn_le_global {d : ℕ} (W : Set (Vec d))
    (F : Vec d → Vec d) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ x, euclideanNorm (F x) ≤ C) : vectorSupNormOn W F ≤ C := by
  unfold vectorSupNormOn
  by_cases hne : {r : ℝ | ∃ x ∈ W, r = euclideanNorm (F x)}.Nonempty
  · apply csSup_le hne
    rintro r ⟨x, _hx, rfl⟩
    exact hF x
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Real.sSup_empty]
    exact hC

/-- The raw physical datum has the literal half-Hölder price `3*d*B*S^-3/2`. -/
theorem harmonicDatum_rawDilation_holder_bounds {d : ℕ}
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    {B : ℝ} (hB : 0 ≤ B) (hb : HarmonicCutoffDatumSizeBound f B) (k : ℤ) :
    let h := centeredCubeRawDilation k (cutoffHarmonicCellDatum f hf hc)
    MemHolder (cube d k) (1 / 2) h.grad ∧
      fractionalInfinityNormOnReal (cube d k) ((3 : ℝ) ^ k) (1 / 2) h.grad ≤
        3 * (d : ℝ) * B * ((3 : ℝ) ^ k) ^ (-(3 / 2 : ℝ)) := by
  dsimp only
  let S := centeredCubeScale k
  have hS : 0 < S := centeredCubeScale_pos k
  have hSinv : 0 < S⁻¹ := inv_pos.mpr hS
  have hscale : S⁻¹ * (S⁻¹) ^ (1 / 2 : ℝ) = S ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_mul hS.le, ← Real.rpow_add hS]
    norm_num
  obtain ⟨hsize, hlip⟩ := harmonicDatum_gradient_norm_bounds f hf hc hB hb
  have hunit := half_holder_bound_of_norm_bounds _ hB hsize hlip Set.univ
  let C := 2 * (d : ℝ) * B * S ^ (-(3 / 2 : ℝ))
  let V := (d : ℝ) * B * S⁻¹
  let H := (centeredCubeRawDilation k (cutoffHarmonicCellDatum f hf hc)).grad
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hhalf : HolderSeminormBoundOn (cube d k) (1 / 2) C H := by
    intro x _hx y _hy
    dsimp only [H]
    rw [centeredCubeRawDilation_grad, centeredCubeRawDilation_grad, ← smul_sub,
      euclideanNorm_smul, abs_of_pos hSinv]
    have hu := hunit (S⁻¹ • x) (Set.mem_univ _) (S⁻¹ • y) (Set.mem_univ _)
    rw [← smul_sub, euclideanNorm_smul, abs_of_pos hSinv,
      Real.mul_rpow hSinv.le (euclideanNorm_nonneg _)] at hu
    refine (mul_le_mul_of_nonneg_left hu hSinv.le).trans_eq ?_
    dsimp only [C]
    calc
      _ = (2 * (d : ℝ) * B) * (S⁻¹ * (S⁻¹) ^ (1 / 2 : ℝ)) *
          euclideanNorm (x - y) ^ (1 / 2 : ℝ) := by ring
      _ = _ := by rw [hscale]
  have hvalue : ∀ x, euclideanNorm (H x) ≤ V := by
    intro x
    dsimp only [H]
    rw [centeredCubeRawDilation_grad, euclideanNorm_smul, abs_of_pos hSinv]
    exact (mul_le_mul_of_nonneg_left ((euclideanNorm_le_dimension_mul_norm _).trans
      (mul_le_mul_of_nonneg_left (hsize _) (Nat.cast_nonneg _))) hSinv.le).trans_eq
        (by dsimp only [V]; ring)
  have hvalues : BddAbove {r : ℝ | ∃ x ∈ cube d k, r = euclideanNorm (H x)} := by
    refine ⟨V, ?_⟩
    rintro r ⟨x, _hx, rfl⟩
    exact hvalue x
  refine ⟨⟨C, hC, hhalf⟩, ?_⟩
  change fractionalInfinityNormOnReal (cube d k) S (1 / 2) H hS ≤
    3 * (d : ℝ) * B * S ^ (-(3 / 2 : ℝ))
  rw [fractionalInfinityNormOnReal_eq_of_bddAbove hS
    (bddAbove_holderQuotients_of_holderSeminormBoundOn hC hhalf) hvalues]
  calc
    _ ≤ C + S ^ (-(1 / 2 : ℝ)) * V :=
      add_le_add (Section6Holder.holderSeminormOn_le_of_bound hC hhalf)
        (mul_le_mul_of_nonneg_left (vectorSupNormOn_le_global _ _ hV hvalue) (by positivity))
    _ = _ := by
      have hp : S ^ (-(1 / 2 : ℝ)) * S⁻¹ = S ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hS]
        norm_num
      dsimp only [C, V]
      calc
        _ = 2 * (d : ℝ) * B * S ^ (-(3 / 2 : ℝ)) +
            (d : ℝ) * B * (S ^ (-(1 / 2 : ℝ)) * S⁻¹) := by ring
        _ = _ := by rw [hp]; ring

end SubdiffusiveProcess.Static
