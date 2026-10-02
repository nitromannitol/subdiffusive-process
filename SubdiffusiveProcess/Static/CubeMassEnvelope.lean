import SubdiffusiveProcess.Static.GridMassGeometry
import SubdiffusiveProcess.Probability.GrowingMeshEnvelope

/-! # One measurable envelope for all local positive and inverse cube masses -/
open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.Frozen.Assumptions
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.Static

/-- The two tests per spatial mesh centre. -/
def massMeshBank (d : ℕ) (R : ℝ) (n : ℕ) :=
  Bool × {k : Fin d → ℤ // k ∈ MassGrid.catalogue R n}

instance massMeshBank_fintype (d : ℕ) (R : ℝ) (n : ℕ) : Fintype (massMeshBank d R n) := by
  classical
  unfold massMeshBank
  infer_instance

/-- The deterministic cardinality of the cube bank. -/
def massMeshCard (d : ℕ) (R : ℝ) (n : ℕ) : ℕ := Fintype.card (massMeshBank d R n)

theorem massMeshCard_le (d : ℕ) {R : ℝ} (hR : 0 ≤ R) (n : ℕ) :
    (massMeshCard d R n : ℝ) ≤
      (2 * (2 * R + 3) ^ d) * ((n : ℝ) + 1) ^ (0 : ℕ) * (3 : ℝ) ^ ((d : ℝ) * n) := by
  classical
  have hc := MassGrid.card_catalogue (d := d) hR n
  simp only [massMeshCard, massMeshBank, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_coe, Nat.cast_mul, Nat.cast_ofNat, pow_zero, mul_one]
  calc
    2 * ((MassGrid.catalogue (d := d) R n).card : ℝ) ≤
        2 * (((2 * R + 3) * (3 : ℝ) ^ n) ^ d) := mul_le_mul_of_nonneg_left hc (by norm_num)
    _ = _ := by
      rw [mul_pow]
      have heq : ((3 : ℝ) ^ n) ^ d = (3 : ℝ) ^ ((d : ℝ) * n) := by
        rw [← pow_mul, ← Real.rpow_natCast]
        congr 1
        push_cast
        ring_nf
      rw [heq]
      ring_nf

/-- Large-cube mass and small-cube inverse mass at one mesh centre. -/
def massMeshVariable {d : ℕ} (M : GMCModel d) (j m : ℕ) (z y0 : Vec d) (R : ℝ)
    (n : ℕ) (i : Fin (massMeshCard d R n)) (ω : PotentialSample d) : ℝ :=
  let b := (Fintype.equivFin (massMeshBank d R n)).symm i
  let c := z + (3 : ℝ) ^ m • (y0 + MassGrid.cc ((3 : ℝ) ^ n)⁻¹ b.2.1)
  if b.1 then (translatedCutoffAverage M j ((m : ℤ) - n) c ω)⁻¹
  else translatedCutoffAverage M j ((m : ℤ) - n + 3) c ω

theorem measurable_massMeshVariable {d : ℕ} (M : GMCModel d) (j m : ℕ)
    (z y0 : Vec d) (R : ℝ) (n : ℕ) (i : Fin (massMeshCard d R n)) :
    Measurable (massMeshVariable M j m z y0 R n i) := by
  unfold massMeshVariable
  dsimp only
  split
  · exact (measurable_translatedCutoffAverage M j _ _).inv
  · exact measurable_translatedCutoffAverage M j _ _

theorem massMeshVariable_pos {d : ℕ} (M : GMCModel d) (j m : ℕ)
    (z y0 : Vec d) (R : ℝ) (n : ℕ) (i : Fin (massMeshCard d R n)) (ω : PotentialSample d) :
    0 < massMeshVariable M j m z y0 R n i ω := by
  dsimp only [massMeshVariable]
  split
  · exact inv_pos.mpr (translatedCutoffAverage_pos M j _ _ ω)
  · exact translatedCutoffAverage_pos M j _ _ ω

/-- The all-depth mesh envelope has uniform moments and is everywhere at least
one. The two mesh tests grow only by the square root of the inverse radius. -/
theorem exists_uniform_cube_mass_envelope (d : ℕ) (y0 : Vec d) (R p : ℝ)
    (hR : 0 ≤ R) (hp : 1 ≤ p) :
    ∃ δ0 C : ℝ, 0 < δ0 ∧ 0 < C ∧
      ∀ M : GMCModel d, M.delta ≤ δ0 → ∀ j m : ℕ, j ≤ m → ∀ z : Vec d,
        ∃ W : PotentialSample d → ℝ, Measurable W ∧ (∀ ω, 1 ≤ W ω) ∧
          (∫⁻ ω, ENNReal.ofReal (W ω ^ p) ∂M.P.toMeasure) ≤ ENNReal.ofReal C ∧
          ∀ᵐ ω ∂M.P.toMeasure, ∀ n : ℕ, ∀ k ∈ MassGrid.catalogue R n,
            (translatedCutoffAverage M j ((m : ℤ) - n)
              (z + (3 : ℝ) ^ m • (y0 + MassGrid.cc ((3 : ℝ) ^ n)⁻¹ k)) ω)⁻¹ ≤
                W ω * (3 : ℝ) ^ ((1 / 2 : ℝ) * n) ∧
            translatedCutoffAverage M j ((m : ℤ) - n + 3)
              (z + (3 : ℝ) ^ m • (y0 + MassGrid.cc ((3 : ℝ) ^ n)⁻¹ k)) ω ≤
                W ω * (3 : ℝ) ^ ((1 / 2 : ℝ) * n) := by
  classical
  let r := p + 8 * (d + 1 : ℝ)
  have hr : 1 ≤ r := by dsimp only [r]; nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hpr : p ≤ r := by dsimp only [r]; nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hgap : (d : ℝ) < r * (1 / 4 : ℝ) := by dsimp only [r]; nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  obtain ⟨δ0, A, hδ0, hA, hmoment⟩ :=
    exists_uniform_signed_cube_mass_moments d r (1 / 4) hr (by norm_num)
  let card := massMeshCard d R
  let a : ℕ → ℝ := fun n => (3 : ℝ) ^ (-(1 / 4 : ℝ) * n) * (card n : ℝ) ^ (1 / r)
  have ha0 : ∀ n, 0 ≤ a n := fun n => by dsimp only [a]; positivity
  have hasum : Summable a := SubdiffusiveProcess.summable_triadic_mesh_cardinality
    card d 0 (2 * (2 * R + 3) ^ d) r (1 / 4) (by positivity) hr hgap
      (massMeshCard_le d hR)
  let B := (∑' n, a n) * A ^ r⁻¹
  have hB : 0 ≤ B := mul_nonneg (tsum_nonneg ha0) (Real.rpow_nonneg hA.le _)
  refine ⟨δ0, (1 + B) ^ p, hδ0, Real.rpow_pos_of_pos (by positivity) _, ?_⟩
  intro M hM j m hjm z
  let Z := massMeshVariable M j m z y0 R
  have hZnorm : ∀ n i, eLpNorm (Z n i) (ENNReal.ofReal r) M.P.toMeasure ≤
      ENNReal.ofReal (A ^ r⁻¹) * ENNReal.ofReal (Real.exp (((1 / 4 : ℝ) * Real.log 3) * n)) := by
    intro n i
    have hmo : (∫⁻ ω, ENNReal.ofReal (Z n i ω ^ r) ∂M.P.toMeasure) ≤
        ENNReal.ofReal (A * (3 : ℝ) ^ (r * (1 / 4 : ℝ) * n)) := by
      dsimp only [Z, massMeshVariable]
      split
      · exact (hmoment M hM j m n hjm _ (by omega) _).2
      · exact (hmoment M hM j m n hjm _ (by omega) _).1
    have h := eLpNorm_le_of_moment_le M.P.toMeasure (Z n i)
      (fun ω => (massMeshVariable_pos M j m z y0 R n i ω).le) hr0 (by positivity) hmo
    have heq : (A * (3 : ℝ) ^ (r * (1 / 4 : ℝ) * n)) ^ r⁻¹ =
        A ^ r⁻¹ * Real.exp (((1 / 4 : ℝ) * Real.log 3) * n) := by
      rw [Real.mul_rpow hA.le (by positivity), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      rw [show (r * (1 / 4 : ℝ) * n) * r⁻¹ = (1 / 4 : ℝ) * n by field_simp]
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
      congr 2
      ring_nf
    rw [heq, ENNReal.ofReal_mul (Real.rpow_nonneg hA.le _)] at h
    exact h
  obtain ⟨V, hVmem, hVdom, hVnorm⟩ :=
    SubdiffusiveProcess.exists_triadic_mesh_envelope_of_exponential_growth M.P.toMeasure
      card d 0 (2 * (2 * R + 3) ^ d) (1 / 2) ((1 / 4 : ℝ) * Real.log 3)
      (by positivity) (by positivity)
      (p := ENNReal.ofReal p) (q := ENNReal.ofReal r)
      (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp) (ENNReal.ofReal_le_ofReal hpr) ENNReal.ofReal_ne_top
      (by rw [ENNReal.toReal_ofReal hr0.le]; nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 3)])
      (massMeshCard_le d hR) Z
      (fun n i => (measurable_massMeshVariable M j m z y0 R n i).aestronglyMeasurable)
      (ENNReal.ofReal (A ^ r⁻¹)) ENNReal.ofReal_ne_top hZnorm
  have hbound : eLpNorm V (ENNReal.ofReal p) M.P.toMeasure ≤ ENNReal.ofReal B := by
    refine hVnorm.trans_eq ?_
    dsimp only [B]
    rw [ENNReal.ofReal_mul (tsum_nonneg ha0)]
    congr 1
    rw [ENNReal.ofReal_tsum_of_nonneg ha0 hasum, ENNReal.toReal_ofReal hr0.le]
    apply tsum_congr
    intro n
    rw [← ENNReal.ofReal_natCast (card n),
      ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg (card n)) (by positivity)]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    dsimp only [a]
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), ← Real.exp_add]
    congr 1
    ring_nf
  let W : PotentialSample d → ℝ := fun ω => 1 + ‖hVmem.1.mk V ω‖
  have hW : Measurable W := measurable_const.add hVmem.1.measurable_mk.norm
  have hW0 : ∀ ω, 1 ≤ W ω := fun ω => by dsimp only [W]; linarith [norm_nonneg (hVmem.1.mk V ω)]
  refine ⟨W, hW, hW0, ?_, ?_⟩
  · apply moment_le_of_eLpNorm_le M.P.toMeasure W (fun ω => (zero_le_one.trans (hW0 ω)))
      (lt_of_lt_of_le zero_lt_one hp) (by positivity)
    have heq : (fun ω => 1 + ‖hVmem.1.mk V ω‖) =
        (fun _ : PotentialSample d => (1 : ℝ)) + (fun ω => ‖hVmem.1.mk V ω‖) := rfl
    change eLpNorm (fun ω => 1 + ‖hVmem.1.mk V ω‖) (ENNReal.ofReal p) _ ≤ _
    rw [heq]
    calc
      _ ≤ eLpNorm (fun _ : PotentialSample d => (1 : ℝ)) (ENNReal.ofReal p) M.P.toMeasure +
          eLpNorm (fun ω => ‖hVmem.1.mk V ω‖) (ENNReal.ofReal p) M.P.toMeasure :=
        eLpNorm_add_le aestronglyMeasurable_const
          hVmem.1.stronglyMeasurable_mk.norm.aestronglyMeasurable (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp)
      _ ≤ 1 + ENNReal.ofReal B := by
        rw [eLpNorm_norm, ← eLpNorm_congr_ae hVmem.1.ae_eq_mk]
        have hc : eLpNorm (fun _ : PotentialSample d => (1 : ℝ)) (ENNReal.ofReal p)
            M.P.toMeasure = 1 := by
          rw [eLpNorm_const (1 : ℝ) (by simpa using (ENNReal.ofReal_pos.mpr (by linarith : 0 < p)).ne')
            (IsProbabilityMeasure.ne_zero _)]
          simp
        rw [hc]
        exact add_le_add_right hbound 1
      _ = ENNReal.ofReal (1 + B) := by rw [ENNReal.ofReal_add zero_le_one hB]; simp
  · filter_upwards [hVdom, hVmem.1.ae_eq_mk] with ω hω heq
    intro n k hk
    have hdom (b : Bool) :
        massMeshVariable M j m z y0 R n
          ((Fintype.equivFin (massMeshBank d R n)) (b, ⟨k, hk⟩)) ω ≤
            W ω * (3 : ℝ) ^ ((1 / 2 : ℝ) * n) := by
      have hh := hω.2 n ((Fintype.equivFin (massMeshBank d R n)) (b, ⟨k, hk⟩))
      apply (le_abs_self _).trans (hh.trans _)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      dsimp only [W]
      rw [← heq, Real.norm_eq_abs, abs_of_nonneg hω.1]
      linarith
    exact ⟨by simpa only [massMeshVariable, Equiv.symm_apply_apply, Bool.true_eq_false,
        ↓reduceIte] using hdom true,
      by simpa only [massMeshVariable, Equiv.symm_apply_apply, Bool.false_eq_true,
        ↓reduceIte] using hdom false⟩

end SubdiffusiveProcess.Static
