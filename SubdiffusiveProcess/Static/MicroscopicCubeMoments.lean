module

public import SubdiffusiveProcess.Static.InitialShellFactor
public import SubdiffusiveProcess.Static.MomentProducts

@[expose] public section

/-! # Mass moments on physical cubes below the initial shell -/
open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.Frozen.Assumptions
open Homogenization hiding Vec TriadicCube
open SubdiffusiveProcess.Static
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Static

/-- The initial shell and the finite suffix bound both signs of the mass
on every cube whose physical scale is nonpositive. -/
theorem microscopicCubeAverage_bounds {d : ℕ} (M : GMCModel d) (L : ℕ)
    {k : ℤ} (hk : k ≤ 0) (ω : PotentialSample d) :
    SubdiffusiveProcess.Section9.cutoffCubeAverage M L (originCube d k) ω ≤
        cutoffBlockFactor M L 0 0 ω * initialShellFactor M ω ∧
      (SubdiffusiveProcess.Section9.cutoffCubeAverage M L (originCube d k) ω)⁻¹ ≤
        cutoffBlockFactor M L 0 0 ω * initialShellFactor M ω := by
  let Q := originCube d k
  letI : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
    ⟨normalizedCubeMeasure_apply_univ Q⟩
  let T := cutoffBlockFactor M L 0 0 ω * initialShellFactor M ω
  have hT : 0 < T := mul_pos
    (zero_lt_one.trans_le (one_le_cutoffBlockFactor M L 0 0 ω))
    (zero_lt_one.trans_le (one_le_initialShellFactor M ω))
  have hpoint : ∀ x ∈ openCubeSet Q, aCutoff M L ω x ≤ T ∧ T⁻¹ ≤ aCutoff M L ω x := by
    intro x hx
    have hxu := openCubeSet_originCube_subset_of_scale_le hk hx
    have hxb : x - 0 ∈ openCubeSet (originCube d (0 : ℤ)) := by simpa using hxu
    obtain ⟨hf, hb⟩ := cutoffBlockFactor_comparison M (Nat.zero_le L) 0 ω hxb
    obtain ⟨h0, hi0⟩ := initialShellFactor_bounds M ω hxu
    have hF : 0 ≤ cutoffBlockFactor M L 0 0 ω :=
      zero_le_one.trans (one_le_cutoffBlockFactor M L 0 0 ω)
    have hInv : (aCutoff M L ω x)⁻¹ ≤ T := by
      have hi : (aCutoff M L ω x)⁻¹ ≤ cutoffBlockFactor M L 0 0 ω * (aCutoff M 0 ω x)⁻¹ := by
        simp only [inv_eq_one_div, mul_one_div]
        apply (div_le_div_iff₀ (aCutoff_pos M L ω x) (aCutoff_pos M 0 ω x)).mpr
        simpa only [one_mul, mul_comm] using hb
      exact hi.trans (mul_le_mul_of_nonneg_left hi0 hF)
    refine ⟨hf.trans (mul_le_mul_of_nonneg_left h0 hF), ?_⟩
    exact (inv_le_inv₀ (aCutoff_pos M L ω x) (inv_pos.mpr hT)).mp
      (by simpa only [inv_inv] using hInv)
  have hi : Integrable (aCutoff M L ω) (normalizedCubeMeasure Q) :=
    (exactCircIntegrable_of_continuous Q (continuous_aCutoff M L ω)).block 0 Q (by
      simp only [descendantsAtDepth_zero, Finset.mem_singleton])
  have hupper : SubdiffusiveProcess.Section9.cutoffCubeAverage M L Q ω ≤ T := by
    rw [SubdiffusiveProcess.Section9.cutoffCubeAverage, cubeAverage_eq_integral_normalizedCubeMeasure]
    calc
      _ ≤ ∫ _x, T ∂normalizedCubeMeasure Q := by
        apply integral_mono_ae hi (integrable_const _)
        filter_upwards [ae_openCubeSet_normalizedCubeMeasure Q] with x hx using (hpoint x hx).1
      _ = T := by simp
  have hlower : T⁻¹ ≤ SubdiffusiveProcess.Section9.cutoffCubeAverage M L Q ω := by
    rw [SubdiffusiveProcess.Section9.cutoffCubeAverage, cubeAverage_eq_integral_normalizedCubeMeasure]
    calc
      T⁻¹ = ∫ _x, T⁻¹ ∂normalizedCubeMeasure Q := by simp
      _ ≤ _ := by
        apply integral_mono_ae (integrable_const _) hi
        filter_upwards [ae_openCubeSet_normalizedCubeMeasure Q] with x hx using (hpoint x hx).2
  refine ⟨hupper, ?_⟩
  have hInv := (inv_le_inv₀ (cutoffCubeAverage_pos M L Q ω) (inv_pos.mpr hT)).mpr hlower
  simpa only [inv_inv] using hInv

/-- Both microscopic moments grow with the cutoff, independently of the
physical size of the microscopic cube. -/
theorem exists_uniform_microscopic_cube_mass_moments (d : ℕ) (q η : ℝ)
    (hq : 1 ≤ q) (hη : 0 < η) :
    ∃ δ0 C : ℝ, 0 < δ0 ∧ 0 < C ∧
      ∀ M : GMCModel d, M.delta ≤ δ0 → ∀ L : ℕ, ∀ k : ℤ, k ≤ 0 →
        (∫⁻ ω, ENNReal.ofReal (SubdiffusiveProcess.Section9.cutoffCubeAverage M L (originCube d k) ω ^ q)
          ∂M.P.toMeasure) ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (q * η * L)) ∧
        (∫⁻ ω, ENNReal.ofReal ((SubdiffusiveProcess.Section9.cutoffCubeAverage M L (originCube d k) ω)⁻¹ ^ q)
          ∂M.P.toMeasure) ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (q * η * L)) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨δ0, B, hδ0, hB, hb⟩ := exists_cutoffBlockFactor_moment_bound d (2 * q) η
    (by linarith) hη
  obtain ⟨A, hA, ha⟩ := initialShellFactor_moment_bound d (2 * q) (by positivity)
  refine ⟨δ0, (B ^ (2 * q) * A) ^ (1 / 2 : ℝ), hδ0, by positivity, ?_⟩
  intro M hM L k hk
  let F := cutoffBlockFactor M L 0 0
  let G := initialShellFactor M
  have hF : Measurable F := measurable_cutoffBlockFactor M L 0 0
  have hG : Measurable G := measurable_initialShellFactor M
  have hF0 : ∀ ω, 0 ≤ F ω := fun ω => zero_le_one.trans (one_le_cutoffBlockFactor M L 0 0 ω)
  have hG0 : ∀ ω, 0 ≤ G ω := fun ω => zero_le_one.trans (one_le_initialShellFactor M ω)
  have hFM : (∫⁻ ω, ENNReal.ofReal (F ω ^ (2 * q)) ∂M.P.toMeasure) ≤
      ENNReal.ofReal ((B * (3 : ℝ) ^ (η * L)) ^ (2 * q)) := by
    apply moment_le_of_eLpNorm_le _ F hF0 (by positivity) (by positivity)
    apply (SubdiffusiveProcess.RawLp.eLpNorm_le_guarded F _ _).trans
    simpa only [Nat.sub_zero] using hb M hM L 0 (Nat.zero_le L) 0
  have hTpow : ((3 : ℝ) ^ (η * L)) ^ q = (3 : ℝ) ^ (q * η * L) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1; ring
  constructor
  · have h := moment_le_of_product_bounds M.P.toMeasure
      (SubdiffusiveProcess.Section9.cutoffCubeAverage M L (originCube d k)) F G hF hG
      (fun ω => (cutoffCubeAverage_pos M L _ ω).le) hF0 hG0 hq0 hB.le hA.le
      (by positivity : 0 ≤ (3 : ℝ) ^ (η * L))
      (fun ω => (microscopicCubeAverage_bounds M L hk ω).1) hFM (ha M)
    simpa only [hTpow] using h
  · have h := moment_le_of_product_bounds M.P.toMeasure
      (fun ω => (SubdiffusiveProcess.Section9.cutoffCubeAverage M L (originCube d k) ω)⁻¹) F G hF hG
      (fun ω => inv_nonneg.mpr (cutoffCubeAverage_pos M L _ ω).le) hF0 hG0 hq0 hB.le hA.le
      (by positivity : 0 ≤ (3 : ℝ) ^ (η * L))
      (fun ω => (microscopicCubeAverage_bounds M L hk ω).2) hFM (ha M)
    simpa only [hTpow] using h

end SubdiffusiveProcess.Static
