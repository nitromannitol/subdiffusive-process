module

public import SubdiffusiveProcess.Static.CutoffFiniteNestedCoercivity
public import SubdiffusiveProcess.Static.AnchoredTailMoments
public import SubdiffusiveProcess.Static.LocalConstantAssembly

@[expose] public section

/-! # Transport of nested coercivity through finite and infinite anchored tails -/

open MeasureTheory _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec TriadicCube
open SubdiffusiveProcess.Static
open scoped ENNReal BigOperators

noncomputable section
namespace SubdiffusiveProcess.Static

theorem exists_coercivity_window {d p : ℕ} (c : Fin p → Vec d) (s1 : Fin p → ℝ) :
    ∃ J : ℕ, ∀ (m : ℕ) (i : Fin p) (x : Vec d), x ∈ Metric.ball (c i) (s1 i / 2) →
      (3 : ℝ) ^ m • x ∈ openCubeSet (originCube d ((m : ℤ) + (J : ℤ))) := by
  classical
  let R : ℝ := 1 + ∑ i : Fin p, (2 * ‖c i‖ + |s1 i|)
  obtain ⟨J, hJ⟩ := ((tendsto_pow_atTop_atTop_of_one_lt
    (by norm_num : (1 : ℝ) < 3)).eventually (Filter.eventually_gt_atTop R)).exists
  refine ⟨J, ?_⟩
  intro m i x hx
  have hi : 2 * ‖c i‖ + |s1 i| ≤ ∑ i : Fin p, (2 * ‖c i‖ + |s1 i|) :=
    Finset.single_le_sum (f := fun i : Fin p => 2 * ‖c i‖ + |s1 i|)
      (fun _ _ => by positivity) (Finset.mem_univ i)
  have hc : 2 * ‖c i‖ + s1 i < (3 : ℝ) ^ J := by
    have hs := le_abs_self (s1 i)
    dsimp only [R] at hJ
    linarith
  have hx' : ‖x - c i‖ < s1 i / 2 := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hxnorm : ‖x‖ < (3 : ℝ) ^ J / 2 := by
    have htri : ‖x‖ ≤ ‖x - c i‖ + ‖c i‖ := by
      simpa only [sub_add_cancel] using norm_add_le (x - c i) (c i)
    linarith
  rw [mem_openCubeSet_originCube_iff]
  intro j
  have hxj : |x j| ≤ ‖x‖ := norm_le_pi_norm x j
  have hh := mul_lt_mul_of_pos_left (hxj.trans_lt hxnorm)
    (pow_pos (by norm_num : (0 : ℝ) < 3) m)
  have heq : (3 : ℝ) ^ ((m : ℤ) + (J : ℤ)) = (3 : ℝ) ^ m * (3 : ℝ) ^ J := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast, zpow_natCast]
  have hh' : |((3 : ℝ) ^ m • x) j| < (3 : ℝ) ^ ((m : ℤ) + (J : ℤ)) / 2 := by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul,
      abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 3) m), heq]
    convert hh using 1; ring
  simpa only [div_eq_mul_inv, one_mul, mul_comm, neg_mul] using abs_lt.mp hh'

theorem localCoercivityEstimates_of_comparison {d p : ℕ} {A0 A1 : Vec d → ℝ}
    (c : Fin p → Vec d) (s0 s1 : Fin p → ℝ)
    (hs : ∀ i, s0 i ≤ s1 i) {K F : ℝ} (hK : 1 ≤ K) (hF : 1 ≤ F)
    (hA : ∀ i, ∀ x ∈ Metric.ball (c i) (s1 i / 2), A0 x ≤ F * A1 x)
    (h : localCoercivityEstimates A0 c s0 s1 K 5) :
    localCoercivityEstimates A1 c s0 s1 (K * F) 5 := by
  intro i n k hk
  let k' : Fin (2 ^ n + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
  have hh := dyadic_side_bounds (hs i) n k'
  have hsub : Metric.ball (c i)
      (((1 - (k : ℝ) / 2 ^ n) * s0 i + ((k : ℝ) / 2 ^ n) * s1 i) / 2) ⊆
      Metric.ball (c i) (s1 i / 2) := Metric.ball_subset_ball (by simpa using div_le_div_of_nonneg_right hh.2 (by norm_num : (0 : ℝ) ≤ 2))
  have hc : cubeCoercivityEstimates A0 (c i)
      ((1 - (k : ℝ) / 2 ^ n) * s0 i + ((k : ℝ) / 2 ^ n) * s1 i)
      (K * (2 : ℝ) ^ (5 * (n : ℝ))) := h i n k hk
  have hc' := cubeCoercivityEstimates_of_comparison (by positivity : 0 ≤ K * (2 : ℝ) ^ (5 * (n : ℝ)))
    hF (fun x hx => hA i x (hsub hx)) hc
  have heq : K * (2 : ℝ) ^ (5 * (n : ℝ)) * F = (K * F) * (2 : ℝ) ^ (5 * (n : ℝ)) := by ring
  rw [heq] at hc'
  exact hc'

theorem tail_coercivity_comparison {d : ℕ} (M : GMCModel d) {L : WithTop ℕ} {m : ℕ}
    (hmL : (m : WithTop ℕ) ≤ L) (z : Vec d) (ω : AnchoredC11Sample d) {F : ℝ}
    (hF : 1 ≤ F) {x : Vec d}
    (ht : F⁻¹ * aCutoff M m ω.1 (z + (3 : ℝ) ^ m • x) ≤ localDensity M L m z ω x) :
    localCoefficient M (m : WithTop ℕ) m z ω x ≤ F * localCoefficient M L m z ω x := by
  have hj : localIndex L m = m := by
    cases L using WithTop.recTopCoe
    · rfl
    · exact min_eq_left (WithTop.coe_le_coe.mp hmL)
  have ha : aCutoff M m ω.1 (z + (3 : ℝ) ^ m • x) ≤ F * localDensity M L m z ω x := by
    have hh := mul_le_mul_of_nonneg_left ht (zero_le_one.trans hF)
    rwa [← mul_assoc, mul_inv_cancel₀ (zero_lt_one.trans_le hF).ne', one_mul] at hh
  have hj0 : localIndex (m : WithTop ℕ) m = m := by
    change min m m = m
    exact min_self m
  have hleft : localCoefficient M (m : WithTop ℕ) m z ω x =
      (ahom M m)⁻¹ * aCutoff M m ω.1 (z + (3 : ℝ) ^ m • x) := by
    rw [localCoefficient, hj0, localDensity_finite_of_le M le_rfl]
  rw [hleft, localCoefficient, hj]
  calc
    (ahom M m)⁻¹ * aCutoff M m ω.1 (z + (3 : ℝ) ^ m • x) ≤
        (ahom M m)⁻¹ * (F * localDensity M L m z ω x) :=
      mul_le_mul_of_nonneg_left ha (inv_nonneg.mpr (ahom_pos M m).le)
    _ = _ := by ring

theorem exists_uniform_tail_nested_coercivity (d p : ℕ) [NeZero d]
    (c : Fin p → Vec d) (s0 s1 : Fin p → ℝ)
    (hs : ∀ i, 0 < s0 i ∧ s0 i < s1 i) (q : ℝ) (hq : 1 ≤ q) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ M : GMCModel d, M.delta ≤ δ0 →
      ∃ C : ℝ, 0 < C ∧ ∀ (L : WithTop ℕ) (m : ℕ), (m : WithTop ℕ) ≤ L → ∀ z : Vec d,
        ∃ K : AnchoredC11Sample d → ℝ, Measurable K ∧ (∀ ω, 1 ≤ K ω) ∧
          (∫⁻ ω, ENNReal.ofReal (K ω ^ q) ∂localAnchoredLaw M) ≤ ENNReal.ofReal C ∧
          ∀ᵐ ω ∂localAnchoredLaw M,
            localCoercivityEstimates (localCoefficient M L m z ω) c s0 s1 (K ω) 5 := by
  have h2q : 1 ≤ 2 * q := by linarith
  obtain ⟨δf, hδf, hf⟩ := exists_uniform_finite_nested_coercivity d p c s0 s1 hs (2 * q) h2q
  obtain ⟨J, hJ⟩ := exists_coercivity_window c s1
  obtain ⟨Ct, hCt, ht⟩ := exists_uniform_local_tail_comparison d J (2 * q) h2q
  refine ⟨min δf 1, lt_min hδf zero_lt_one, ?_⟩
  intro M hM
  obtain ⟨Cf, hCf, hfM⟩ := hf M (hM.trans (min_le_left _ _))
  let B : ℝ := Cf ^ (2 * q)⁻¹ * Ct ^ (2 * q)⁻¹
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B ^ q, by positivity, ?_⟩
  intro L m hmL z
  obtain ⟨W, hW, hW1, hWmom, hWc⟩ := hfM m m le_rfl z
  obtain ⟨F, hF, hF1, hFmom, hFc⟩ := ht M (hM.trans (min_le_right _ _)) m z
  let K : AnchoredC11Sample d → ℝ := fun ω => W ω * F ω
  have hKn : eLpNorm K (ENNReal.ofReal q) (localAnchoredLaw M) ≤ ENNReal.ofReal B := by
    have hWn := coercivity_norm_of_moment (localAnchoredLaw M) (by positivity : 0 < 2 * q)
      hCf.le (fun ω => zero_le_one.trans (hW1 ω)) hWmom
    have hFn := coercivity_norm_of_moment (localAnchoredLaw M) (by positivity : 0 < 2 * q)
      hCt.le (fun ω => zero_le_one.trans (hF1 ω)) hFmom
    rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hW.aestronglyMeasurable] at hWn
    rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hF.aestronglyMeasurable] at hFn
    exact (coercivity_norm_product (localAnchoredLaw M) (zero_lt_one.trans_le hq)
      hW.aestronglyMeasurable hF.aestronglyMeasurable).trans
      ((mul_le_mul' hWn hFn).trans_eq (ENNReal.ofReal_mul (Real.rpow_nonneg hCf.le _)).symm)
  have hK1 : ∀ ω, 1 ≤ K ω := fun ω => one_le_mul_of_one_le_of_one_le (hW1 ω) (hF1 ω)
  refine ⟨K, hW.mul hF, hK1,
    coercivity_moment_of_norm (localAnchoredLaw M) (zero_lt_one.trans_le hq) hB.le
      (fun ω => zero_le_one.trans (hK1 ω))
      ((SubdiffusiveProcess.RawLp.eLpNorm_le_guarded K _ _).trans hKn), ?_⟩
  filter_upwards [hWc, hFc] with ω hω hωF
  exact localCoercivityEstimates_of_comparison c s0 s1 (fun i => (hs i).2.le)
    (hW1 ω) (hF1 ω)
    (fun i x hx => tail_coercivity_comparison M hmL z ω (hF1 ω) (hωF L hmL x (hJ m i x hx)).1) hω

end SubdiffusiveProcess.Static
