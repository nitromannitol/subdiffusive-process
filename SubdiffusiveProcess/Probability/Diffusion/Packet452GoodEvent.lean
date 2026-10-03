module

public import SubdiffusiveProcess.Probability.Diffusion.Packet452RateApprox

@[expose] public section




set_option autoImplicit false

open Filter Homogenization MeasureTheory MarkovProcess Set

open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.Packet452Route

variable {d : ℕ}

/-! ## Two arithmetic helpers -/

theorem tsum_four_pow_mul_ne_top {M : ℕ → ℝ≥0∞} {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (h : ∀ k, M k ≤ C * ((16 : ℝ≥0∞)⁻¹) ^ k) :
    (∑' k : ℕ, (4 : ℝ≥0∞) ^ k * M k) ≠ ⊤ := by
  have h16 : ((16 : ℝ≥0∞)⁻¹) * 4 = 4⁻¹ := by
    rw [show (16 : ℝ≥0∞) = 4 * 4 by norm_num,
      ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), mul_assoc,
      ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
  have harith : ∀ k : ℕ, (4 : ℝ≥0∞) ^ k * (C * ((16 : ℝ≥0∞)⁻¹) ^ k)
      = C * ((4 : ℝ≥0∞)⁻¹) ^ k := by
    intro k
    calc (4 : ℝ≥0∞) ^ k * (C * ((16 : ℝ≥0∞)⁻¹) ^ k)
        = C * (((16 : ℝ≥0∞)⁻¹) ^ k * (4 : ℝ≥0∞) ^ k) := by ring
      _ = C * (((16 : ℝ≥0∞)⁻¹ * 4) ^ k) := by rw [← mul_pow]
      _ = C * ((4 : ℝ≥0∞)⁻¹) ^ k := by rw [h16]
  have hmaj : (∑' k : ℕ, (4 : ℝ≥0∞) ^ k * (C * ((16 : ℝ≥0∞)⁻¹) ^ k)) ≠ ⊤ := by
    simp only [harith]
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top hC tsum_geometric_four_inv_ne_top
  exact ne_top_of_le_ne_top hmaj (ENNReal.tsum_le_tsum fun k => by gcongr; exact h k)

theorem ofReal_maximal_rhs {T : ℝ≥0} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ENNReal.ofReal (32 * (A + (T : ℝ) * B))
      = 32 * (ENNReal.ofReal A + (T : ℝ≥0∞) * ENNReal.ofReal B) := by
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 32),
    ENNReal.ofReal_add hA (mul_nonneg T.coe_nonneg hB),
    ENNReal.ofReal_mul T.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  norm_num

theorem inv_four_pow_sq (k : ℕ) : (((4 : ℝ≥0∞)⁻¹) ^ k) ^ 2 = ((16 : ℝ≥0∞)⁻¹) ^ k := by
  rw [← pow_mul, mul_comm, pow_mul]
  congr 1
  rw [← ENNReal.inv_pow]
  norm_num

/-! ## `L²` membership of the zero extension -/

theorem memLp_zeroExtension_two {U : Set (Vec d)} (hU : IsOpen U) (u : H10Function U) :
    MemLp u.zeroExtension 2 volume :=
  u.memLp_zeroExtension hU.measurableSet u.toH1Function.memL2

theorem memLp_zeroExtensionGrad_two {U : Set (Vec d)} (hU : IsOpen U) (u : H10Function U)
    (i : Fin d) : MemLp (fun x => u.zeroExtensionGrad x i) 2 volume := by
  have h : MemLp (fun x => u.zeroExtensionGrad x i) 2 (volume.restrict Set.univ) :=
    u.gradMemLp_zeroExtensionGrad hU.measurableSet u.toH1Function.gradMemL2 i
  rwa [Measure.restrict_univ] at h

/-! ## The maximal bound on the sup-increments -/

variable {U : Set (Vec d)} {u : H10Function U}

theorem lintegral_sq_supIncr_le (hmax : maximalEstimateGoal d) (a : RateApprox d U u)
    (hz : AEStronglyMeasurable u.zeroExtension volume)
    (hzg : ∀ i : Fin d, AEStronglyMeasurable (fun x => u.zeroExtensionGrad x i) volume)
    (T : ℝ≥0) (k : ℕ) :
    (∫⁻ ω, (supIncr (fun k t => a.fn k (ω t)) T k) ^ 2 ∂(pathMeasure d))
      ≤ (128 * (1 + (T : ℝ≥0∞) * d)) * ((16 : ℝ≥0∞)⁻¹) ^ k := by
  set f := a.fn (k + 1) with hfdef
  set g := a.fn k with hgdef
  have hsq : ∀ ω : ContinuousPath (Vec d),
      (supIncr (fun k t => a.fn k (ω t)) T k) ^ 2
        = ⨆ t : ℝ≥0, ⨆ (_ : t ≤ T), ENNReal.ofReal ((f (ω t) - g (ω t)) ^ 2) := fun ω =>
    supIncr_sq (fun k t => a.fn k (ω t)) T k
  have hmeasF : Measurable fun ω : ContinuousPath (Vec d) =>
      ⨆ t : ℝ≥0, ⨆ (_ : t ≤ T), ENNReal.ofReal ((f (ω t) - g (ω t)) ^ 2) := by
    refine measurable_iSup_le_of_continuous
      (F := fun (ω : ContinuousPath (Vec d)) (t : ℝ≥0) =>
        ENNReal.ofReal ((f (ω t) - g (ω t)) ^ 2)) ?_ ?_ T
    · intro ω
      exact ENNReal.continuous_ofReal.comp
        (((f.continuous.comp ω.continuous).sub (g.continuous.comp ω.continuous)).pow 2)
    · intro t
      have hev : Measurable fun ω : ContinuousPath (Vec d) => ω t :=
        ContinuousPath.measurable_coordinateProcess t
      exact ENNReal.measurable_ofReal.comp
        (((f.continuous.measurable.comp hev).sub
          (g.continuous.measurable.comp hev)).pow_const 2)
  -- integrability of the squares appearing on the right-hand side
  have hintA : Integrable (fun x => (f x - g x) ^ 2) volume :=
    integrable_sq_of_continuous_of_hasCompactSupport (f.continuous.sub g.continuous)
      ((a.compact (k + 1)).sub (a.compact k))
  have hintB : ∀ i : Fin d, Integrable (fun x =>
      (fderiv ℝ f x (Pi.single i 1) - fderiv ℝ g x (Pi.single i 1)) ^ 2) volume := by
    intro i
    exact integrable_sq_of_continuous_of_hasCompactSupport
      ((continuous_fderiv_apply (a.smooth (k + 1)) i).sub (continuous_fderiv_apply (a.smooth k) i))
      ((hasCompactSupport_fderiv_apply (a.compact (k + 1)) i).sub
        (hasCompactSupport_fderiv_apply (a.compact k) i))
  have hgradSum : ∑ i : Fin d, (2 * ((4 : ℝ≥0∞)⁻¹) ^ k) ^ 2
      = (d : ℝ≥0∞) * (2 * ((4 : ℝ≥0∞)⁻¹) ^ k) ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc (∫⁻ ω, (supIncr (fun k t => a.fn k (ω t)) T k) ^ 2 ∂(pathMeasure d))
      = ∫⁻ ω, (⨆ t : ℝ≥0, ⨆ (_ : t ≤ T),
          ENNReal.ofReal ((f (ω t) - g (ω t)) ^ 2)) ∂(pathMeasure d) := by simp only [hsq]
    _ = ∫⁻ x, ∫⁻ ω, (⨆ t : ℝ≥0, ⨆ (_ : t ≤ T),
          ENNReal.ofReal ((f (ω t) - g (ω t)) ^ 2))
          ∂(laplacianContinuousLaw d x) ∂volume := lintegral_pathMeasure hmeasF
    _ ≤ ENNReal.ofReal (32 * ((∫ x, (f x - g x) ^ 2) + (T : ℝ) * ∫ x, ∑ i : Fin d,
          (fderiv ℝ f x (Pi.single i 1) - fderiv ℝ g x (Pi.single i 1)) ^ 2)) :=
        maximalEstimate_sub hmax (a.smooth (k + 1)) (a.compact (k + 1)) (a.smooth k)
          (a.compact k) T
    _ = 32 * (ENNReal.ofReal (∫ x, (f x - g x) ^ 2)
          + (T : ℝ≥0∞) * ENNReal.ofReal (∫ x, ∑ i : Fin d,
            (fderiv ℝ f x (Pi.single i 1) - fderiv ℝ g x (Pi.single i 1)) ^ 2)) :=
        ofReal_maximal_rhs (integral_nonneg fun x => sq_nonneg _)
          (integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _)
    _ = 32 * ((eLpNorm (fun x => f x - g x) 2 volume) ^ 2
          + (T : ℝ≥0∞) * ∑ i : Fin d, (eLpNorm (fun x =>
            fderiv ℝ f x (Pi.single i 1) - fderiv ℝ g x (Pi.single i 1)) 2 volume) ^ 2) := by
        rw [ofReal_integral_sq_eq_eLpNorm_sq hintA,
          ofReal_integral_sum_sq_eq_sum_eLpNorm_sq hintB]
        have hf : AEStronglyMeasurable (fun x => f x - g x) volume := by
          simpa only [Pi.sub_apply] using! (f.continuous.sub g.continuous).aestronglyMeasurable
        have hg : ∀ i : Fin d, AEStronglyMeasurable (fun x =>
            fderiv ℝ f x (Pi.single i 1) - fderiv ℝ g x (Pi.single i 1)) volume := by
          intro i
          simpa only [Pi.sub_apply] using! ((continuous_fderiv_apply (a.smooth (k + 1)) i).sub (continuous_fderiv_apply (a.smooth k) i)).aestronglyMeasurable
        rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hf]
        simp_rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded (hg _)]

    _ ≤ 32 * ((2 * ((4 : ℝ≥0∞)⁻¹) ^ k) ^ 2
          + (T : ℝ≥0∞) * ∑ _i : Fin d, (2 * ((4 : ℝ≥0∞)⁻¹) ^ k) ^ 2) := by
        gcongr with i
        · exact a.rate_sub hz k
        · exact a.rateGrad_sub i (hzg i) k
    _ = (128 * (1 + (T : ℝ≥0∞) * d)) * ((16 : ℝ≥0∞)⁻¹) ^ k := by
        rw [hgradSum, mul_pow, inv_four_pow_sq]
        ring

/-! ## The good event -/

theorem ae_mem_goodSet (hmax : maximalEstimateGoal d) (hU : IsOpen U) (a : RateApprox d U u) :
    ∀ᵐ ω ∂(pathMeasure d), ω ∈ goodSet a.fn := by
  have hz : AEStronglyMeasurable u.zeroExtension volume :=
    (memLp_zeroExtension_two hU u).aestronglyMeasurable
  have hzg : ∀ i : Fin d, AEStronglyMeasurable (fun x => u.zeroExtensionGrad x i) volume :=
    fun i => (memLp_zeroExtensionGrad_two hU u i).aestronglyMeasurable
  have hmain : ∀ N : ℕ, ∀ᵐ ω ∂(pathMeasure d),
      (∑' k : ℕ, supIncr (fun k t => a.fn k (ω t)) (N : ℝ≥0) k) ≠ ⊤ := by
    intro N
    refine ae_tsum_lt_top_of_lintegral_sq
      (fun k => (measurable_supIncr_comp a.fn (N : ℝ≥0) k).aemeasurable) ?_
    refine tsum_four_pow_mul_ne_top ?_ (fun k =>
      lintegral_sq_supIncr_le hmax a hz hzg (N : ℝ≥0) k)
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.add_ne_top.mpr ⟨by norm_num,
        ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.natCast_ne_top d)⟩)
  filter_upwards [ae_all_iff.mpr hmain] with ω hω
  exact hω

end SubdiffusiveProcess.Probability.Diffusion.Packet452Route
