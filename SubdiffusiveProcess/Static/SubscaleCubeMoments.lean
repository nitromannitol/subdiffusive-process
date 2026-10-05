module

public import SubdiffusiveProcess.Static.CutoffBlockComparison
public import SubdiffusiveProcess.Static.InfraredComparison

@[expose] public section

/-! # Two-sided mass moment transport below a finite cutoff

The shell-block comparison is integrated on a translated triadic cube.
Cauchy--Schwarz combines its arbitrary small geometric cost with the
matching-cutoff positive and inverse mass moments.
-/
open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab _root_.SubdiffusiveProcess.Model
open Homogenization hiding Vec TriadicCube
open SubdiffusiveProcess.Static
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Static

/-- The block factor compares both normalized spatial masses. -/
theorem cutoffCubeAverage_block_comparison {d : ℕ} (M : GMCModel d)
    {L k : ℕ} (hkL : k ≤ L) (Q : TriadicCube d) (hQ : Q.scale = (k : ℤ))
    (ω : PotentialSample d) :
    SubdiffusiveProcess.Section9.cutoffCubeAverage M L Q ω ≤
        cutoffBlockFactor M L k (triadicCubeShift Q) ω *
          SubdiffusiveProcess.Section9.cutoffCubeAverage M k Q ω ∧
      (SubdiffusiveProcess.Section9.cutoffCubeAverage M L Q ω)⁻¹ ≤
        cutoffBlockFactor M L k (triadicCubeShift Q) ω *
          (SubdiffusiveProcess.Section9.cutoffCubeAverage M k Q ω)⁻¹ := by
  have hshift : ∀ x ∈ openCubeSet Q,
      x - triadicCubeShift Q ∈ openCubeSet (originCube d (k : ℤ)) := by
    intro x hx
    rw [openCubeSet_eq_translateSet_originCube_of_triadicCube,
      mem_translateSet_iff_sub_mem, hQ] at hx
    exact hx
  have hi (j : ℕ) : Integrable (aCutoff M j ω) (normalizedCubeMeasure Q) :=
    (exactCircIntegrable_of_continuous Q (continuous_aCutoff M j ω)).block 0 Q (by
      simp only [descendantsAtDepth_zero, Finset.mem_singleton])
  have hforward : SubdiffusiveProcess.Section9.cutoffCubeAverage M L Q ω ≤
      cutoffBlockFactor M L k (triadicCubeShift Q) ω *
        SubdiffusiveProcess.Section9.cutoffCubeAverage M k Q ω := by
    simp only [SubdiffusiveProcess.Section9.cutoffCubeAverage, cubeAverage_eq_integral_normalizedCubeMeasure]
    rw [← integral_const_mul]
    apply integral_mono_ae (hi L) ((hi k).const_mul _)
    filter_upwards [ae_openCubeSet_normalizedCubeMeasure Q] with x hx
    exact (cutoffBlockFactor_comparison M hkL _ ω (hshift x hx)).1
  have hback : SubdiffusiveProcess.Section9.cutoffCubeAverage M k Q ω ≤
      cutoffBlockFactor M L k (triadicCubeShift Q) ω *
        SubdiffusiveProcess.Section9.cutoffCubeAverage M L Q ω := by
    simp only [SubdiffusiveProcess.Section9.cutoffCubeAverage, cubeAverage_eq_integral_normalizedCubeMeasure]
    rw [← integral_const_mul]
    apply integral_mono_ae (hi k) ((hi L).const_mul _)
    filter_upwards [ae_openCubeSet_normalizedCubeMeasure Q] with x hx
    exact (cutoffBlockFactor_comparison M hkL _ ω (hshift x hx)).2
  refine ⟨hforward, ?_⟩
  have hL := cutoffCubeAverage_pos M L Q ω
  have hk := cutoffCubeAverage_pos M k Q ω
  apply (mul_le_mul_iff_right₀ hk).mp
  apply (mul_le_mul_iff_left₀ hL).mp
  field_simp
  simpa only [mul_comm] using! hback

/-- An `Lᵖ` bound implies the corresponding nonnegative real moment bound. -/
theorem moment_le_of_eLpNorm_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) {q B : ℝ} (hq : 0 < q) (hB : 0 ≤ B)
    (h : SubdiffusiveProcess.RawLp.eLpNorm f (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B) :
    (∫⁻ ω, ENNReal.ofReal (f ω ^ q) ∂μ) ≤ ENNReal.ofReal (B ^ q) := by
  rw [lintegral_rpow_eq_eLpNorm_rpow μ f hf hq]
  exact (ENNReal.rpow_le_rpow h hq.le).trans_eq
    (ENNReal.ofReal_rpow_of_nonneg hB hq.le)

/-- Both signs have any prescribed geometric cost in the cutoff gap.
The threshold is chosen before the model, both scales and the cube. -/
theorem exists_uniform_subscale_cube_mass_moments (d : ℕ) (q η : ℝ)
    (hq : 1 ≤ q) (hη : 0 < η) :
    ∃ δ0 C : ℝ, 0 < δ0 ∧ 0 < C ∧
      ∀ M : GMCModel d, M.delta ≤ δ0 → ∀ L k : ℕ, k ≤ L →
        ∀ Q : TriadicCube d, Q.scale = (k : ℤ) →
          (∫⁻ ω, ENNReal.ofReal (SubdiffusiveProcess.Section9.cutoffCubeAverage M L Q ω ^ q)
            ∂M.P.toMeasure) ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (q * η * (L - k : ℕ))) ∧
          (∫⁻ ω, ENNReal.ofReal ((SubdiffusiveProcess.Section9.cutoffCubeAverage M L Q ω)⁻¹ ^ q)
            ∂M.P.toMeasure) ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (q * η * (L - k : ℕ))) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have h2q : 1 ≤ 2 * q := by linarith
  obtain ⟨δb, B, hδb, hB, hb⟩ := exists_cutoffBlockFactor_moment_bound d (2 * q) η h2q hη
  obtain ⟨δa, A, hδa, hA, ha⟩ := exists_uniform_cutoffCube_mass_moments d (2 * q) h2q
  refine ⟨min δb δa, (B ^ (2 * q) * A) ^ (1 / 2 : ℝ),
    lt_min hδb hδa, by positivity, ?_⟩
  intro M hM L k hkL Q hQ
  let F := cutoffBlockFactor M L k (triadicCubeShift Q)
  have hF : Measurable F := measurable_cutoffBlockFactor M L k _
  have hF0 : ∀ ω, 0 ≤ F ω := fun ω => zero_le_one.trans (one_le_cutoffBlockFactor M L k _ ω)
  have hFmoment : (∫⁻ ω, ENNReal.ofReal (F ω ^ (2 * q)) ∂M.P.toMeasure) ≤
      ENNReal.ofReal ((B * (3 : ℝ) ^ (η * (L - k : ℕ))) ^ (2 * q)) :=
    moment_le_of_eLpNorm_le _ F hF0 (by positivity) (by positivity)
      ((SubdiffusiveProcess.RawLp.eLpNorm_le_guarded F (ENNReal.ofReal (2 * q)) M.P.toMeasure).trans
        (hb M (hM.trans (min_le_left _ _)) L k hkL _))
  obtain ⟨hapos, hainv⟩ := ha M (hM.trans (min_le_right _ _)) k k le_rfl Q hQ
  have hbound : ∀ (f g : PotentialSample d → ℝ), Measurable g →
      (∀ ω, 0 ≤ f ω) → (∀ ω, 0 ≤ g ω) → (∀ ω, f ω ≤ F ω * g ω) →
      (∫⁻ ω, ENNReal.ofReal (g ω ^ (2 * q)) ∂M.P.toMeasure) ≤ ENNReal.ofReal A →
      (∫⁻ ω, ENNReal.ofReal (f ω ^ q) ∂M.P.toMeasure) ≤
        ENNReal.ofReal ((B ^ (2 * q) * A) ^ (1 / 2 : ℝ) *
          (3 : ℝ) ^ (q * η * (L - k : ℕ))) := by
    intro f g hg hf0 hg0 hfg hgM
    calc
      _ ≤ ∫⁻ ω, ENNReal.ofReal ((F ω * g ω) ^ q) ∂M.P.toMeasure :=
        lintegral_mono fun ω => ENNReal.ofReal_le_ofReal
          (Real.rpow_le_rpow (hf0 ω) (hfg ω) hq0.le)
      _ ≤ (∫⁻ ω, ENNReal.ofReal (F ω ^ (2 * q)) ∂M.P.toMeasure) ^ (1 / 2 : ℝ) *
          (∫⁻ ω, ENNReal.ofReal (g ω ^ (2 * q)) ∂M.P.toMeasure) ^ (1 / 2 : ℝ) :=
        product_moment_le _ hF hg hF0 hg0 q
      _ ≤ ENNReal.ofReal ((B * (3 : ℝ) ^ (η * (L - k : ℕ))) ^ (2 * q)) ^ (1 / 2 : ℝ) *
          ENNReal.ofReal A ^ (1 / 2 : ℝ) :=
        mul_le_mul' (ENNReal.rpow_le_rpow hFmoment (by norm_num))
          (ENNReal.rpow_le_rpow hgM (by norm_num))
      _ = _ := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg hA.le (by norm_num),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [← Real.rpow_mul (by positivity), show (2 * q) * (1 / 2 : ℝ) = q by ring,
          Real.mul_rpow hB.le (by positivity),
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
          Real.mul_rpow (by positivity) hA.le, ← Real.rpow_mul hB.le]
        rw [show (2 * q) * (1 / 2 : ℝ) = q by ring,
          show η * (L - k : ℕ) * q = q * η * (L - k : ℕ) by ring]
        ring
  constructor
  · exact hbound _ _ (SubdiffusiveProcess.Section9.measurable_cutoffCubeAverage M k Q)
      (fun ω => (cutoffCubeAverage_pos M L Q ω).le)
      (fun ω => (cutoffCubeAverage_pos M k Q ω).le)
      (fun ω => (cutoffCubeAverage_block_comparison M hkL Q hQ ω).1) hapos
  · exact hbound _ _ (SubdiffusiveProcess.Section9.measurable_cutoffCubeAverage M k Q).inv
      (fun ω => inv_nonneg.mpr (cutoffCubeAverage_pos M L Q ω).le)
      (fun ω => inv_nonneg.mpr (cutoffCubeAverage_pos M k Q ω).le)
      (fun ω => (cutoffCubeAverage_block_comparison M hkL Q hQ ω).2) hainv

end SubdiffusiveProcess.Static
