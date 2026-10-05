module

public import SubdiffusiveProcess.Paper.primitive_scores_finite
public import SubdiffusiveProcess.Paper.Foundations.PrefixActualJMeas
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ResponseSupremum
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.MomentAggregation

@[expose] public section

/-!
# Literal prefix response-atom moments

This file bounds the exact `aux_psf_Jval` score atom uniformly in the cutoff
and deterministic spatial center. The moment order is fixed before the
small-disorder threshold. The carrier is the potential-sample law `M.P`;
transport to the bilateral-field law is a separate step.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Paper
open _root_.SubdiffusiveProcess.Model

private theorem prefixJ_Jval_measurable {d : ℕ} (M : GMCModel d)
    (n : ℕ) (x : Vec d) :
    Measurable (fun omega : PotentialSample d => aux_psf_Jval M n omega x) := by
  by_cases hd : d = 0
  · subst d
    have hzero : (fun omega : PotentialSample 0 => aux_psf_Jval M n omega x) =
        fun _ => 0 := by
      funext omega
      simp [aux_psf_Jval, Homogenization.vecNormSq, Homogenization.vecDot]
    rw [hzero]
    exact measurable_const
  · let : NeZero d := ⟨hd⟩
    exact aux_lem_prefix_limit_actual_J_meas M n x

theorem aux_psf_Jval_le_centered_defect {d : ℕ}
    (M : GMCModel d) (n : ℕ) (omega : PotentialSample d) :
    aux_psf_Jval M n omega 0 ≤
      normalizedDefect M n
        (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (n : ℤ))) omega := by
  have hrepr := SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ofReal_cutoffResponseSupremum_zero_eq_normalizedDefect M n n omega
  simp only [min_self] at hrepr
  rw [← hrepr]
  unfold aux_psf_Jval
  refine sSup_le ?_
  rintro v ⟨e, he, rfl⟩
  apply ENNReal.ofReal_le_ofReal
  unfold SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.cutoffResponseSupremum
  simp only [min_self]
  apply le_csSup (bddAbove_section6Response_unitSphere M n n omega 0)
  exact ⟨e, he, rfl⟩

theorem aux_psf_Jval_origin_moment_bound {d : ℕ}
    (M : GMCModel d) (q C : ℝ) (hq : 1 ≤ q)
    (hC : ∀ L n : ℕ,
      paperENNRealLpNorm M.P.toMeasure q
        (normalizedDefect M (min n L)
          (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (n : ℤ)))) ≤
        ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2))
    (n : ℕ) :
    eLpNorm (fun omega : PotentialSample d => (aux_psf_Jval M n omega 0).toReal)
      (ENNReal.ofReal q) M.P.toMeasure ≤
      ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2) := by
  have hp : 0 < q := by linarith
  calc
    eLpNorm (fun omega : PotentialSample d => (aux_psf_Jval M n omega 0).toReal)
        (ENNReal.ofReal q) M.P.toMeasure ≤
      eLpNorm (fun omega : PotentialSample d =>
        normalizedDefect M n
          (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (n : ℤ))) omega)
        (ENNReal.ofReal q) M.P.toMeasure := by
          apply eLpNorm_mono_enorm_ae
            ((prefixJ_Jval_measurable M n 0).ennreal_toReal.aestronglyMeasurable)
          exact Filter.Eventually.of_forall fun omega => by
            rw [← ofReal_norm, Real.norm_eq_abs,
              abs_of_nonneg ENNReal.toReal_nonneg, enorm_eq_self]
            exact (ENNReal.ofReal_toReal_le).trans
              (aux_psf_Jval_le_centered_defect M n omega)
    _ = paperENNRealLpNorm M.P.toMeasure q
        (fun omega => normalizedDefect M n
          (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (n : ℤ))) omega) := by
          exact (paperENNRealLpNorm_eq_eLpNorm_of_aestronglyMeasurable M.P.toMeasure hp _
            ((measurable_normalizedDefect_potentialShellIndexSigma_Iic M n
              (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (n : ℤ)))).mono
                (potentialShellIndexSigma_le_borel (d := d) (Set.Iic n)) le_rfl).aestronglyMeasurable).symm
    _ ≤ _ := by simpa only [min_self] using hC n n

theorem aux_psf_exists_Jval_origin_moment_bound (d : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (M : GMCModel d) (q : ℝ), 1 ≤ q →
        q ≤ C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
        ∀ n : ℕ,
          eLpNorm (fun omega : PotentialSample d => (aux_psf_Jval M n omega 0).toReal)
            (ENNReal.ofReal q) M.P.toMeasure ≤
            ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2) := by
  obtain ⟨c, C, hc, hC, hm⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.exists_cutoffNormalizedResponse_moment_bound d
  refine ⟨c, C, hc, hC, ?_⟩
  intro M q hq hqMax n
  exact aux_psf_Jval_origin_moment_bound M q C hq (hm M q hq hqMax) n

theorem aux_psf_Jval_translate {d : ℕ}
    (M : GMCModel d) (n : ℕ) (omega : PotentialSample d) (x : Vec d) :
    aux_psf_Jval M n omega x =
      aux_psf_Jval M n
        (translatePotentialSample x omega) 0 := by
  unfold aux_psf_Jval
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, he, congrArg ENNReal.ofReal
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.section6Response_eq_translate_zero M n n omega x e)⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, he, congrArg ENNReal.ofReal
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.section6Response_eq_translate_zero M n n omega x e).symm⟩

theorem aux_psf_small_disorder_admissible (C q : ℝ) (hC : 0 < C) (hq : 1 ≤ q) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ0 →
      q ≤ C⁻¹ * (δ ^ 2)⁻¹ * |Real.log δ|⁻¹ := by
  have hqpos : 0 < q := by linarith
  let δ0 := min (1 / 2 : ℝ) (C * q)⁻¹
  refine ⟨δ0, lt_min (by norm_num) (inv_pos.mpr (mul_pos hC hqpos)), ?_⟩
  intro δ hδ hδsmall
  have hδhalf : δ ≤ 1 / 2 := hδsmall.trans (min_le_left _ _)
  have hδCq : δ ≤ (C * q)⁻¹ := hδsmall.trans (min_le_right _ _)
  have hδone : δ ≤ 1 := by linarith
  have hlogneg : Real.log δ < 0 := Real.log_neg hδ (by linarith)
  have habspos : 0 < |Real.log δ| := abs_pos.mpr (ne_of_lt hlogneg)
  have hlogmul : |Real.log δ| * δ < 1 := by
    simpa [abs_mul, abs_of_pos hδ] using Real.abs_log_mul_self_lt δ hδ hδone
  have hCqδ : C * q * δ ≤ 1 := by
    calc
      C * q * δ ≤ C * q * (C * q)⁻¹ :=
        mul_le_mul_of_nonneg_left hδCq (mul_pos hC hqpos).le
      _ = 1 := mul_inv_cancel₀ (ne_of_gt (mul_pos hC hqpos))
  have hden : 0 < C * δ ^ 2 * |Real.log δ| := by positivity
  have hprod : q * (C * δ ^ 2 * |Real.log δ|) ≤ 1 := by
    have ha : 0 ≤ C * q * δ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hlogmul.le ha]
  have hformula : C⁻¹ * (δ ^ 2)⁻¹ * |Real.log δ|⁻¹ =
      (C * δ ^ 2 * |Real.log δ|)⁻¹ := by ring
  rw [hformula]
  simpa only [one_div] using (le_div_iff₀ hden).2 hprod

theorem aux_psf_exists_Jval_origin_moment_small_disorder (d : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ q : ℝ, 1 ≤ q → ∃ δ0 : ℝ, 0 < δ0 ∧
        ∀ (M : GMCModel d), 0 < M.delta → M.delta ≤ δ0 → ∀ n : ℕ,
          eLpNorm (fun omega : PotentialSample d => (aux_psf_Jval M n omega 0).toReal)
            (ENNReal.ofReal q) M.P.toMeasure ≤
            ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2) := by
  obtain ⟨c, C, hc, hC, hm⟩ := aux_psf_exists_Jval_origin_moment_bound d
  refine ⟨c, C, hc, hC, ?_⟩
  intro q hq
  obtain ⟨δ0, hδ0, hδ⟩ := aux_psf_small_disorder_admissible C q hC hq
  refine ⟨δ0, hδ0, ?_⟩
  intro M hM hM0 n
  exact hm M q hq (hδ M.delta hM hM0) n

theorem aux_psf_Jval_spatial_moment_of_origin {d : ℕ}
    (M : GMCModel d) (n : ℕ) (x : Vec d) (q C : ℝ) (hq : 1 ≤ q)
    (hmoment : paperENNRealLpNorm M.P.toMeasure q
      (normalizedDefect M n
        (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (n : ℤ)))) ≤
      ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2)) :
    eLpNorm (fun omega : PotentialSample d => (aux_psf_Jval M n omega x).toReal)
      (ENNReal.ofReal q) M.P.toMeasure ≤
      ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2) := by
  let F := fun omega : PotentialSample d =>
    normalizedDefect M n
      (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (n : ℤ))) omega
  have hFmeas : Measurable F := by
    exact (measurable_normalizedDefect_potentialShellIndexSigma_Iic M n
      (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (n : ℤ)))).mono
      (potentialShellIndexSigma_le_borel (d := d) (Set.Iic n)) le_rfl
  have hpres :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.measurePreserving_translatePotentialSample M x
  have hcomp := eLpNorm_comp_measurePreserving
    (p := ENNReal.ofReal q) hFmeas.aestronglyMeasurable hpres
  have hp : 0 < q := by linarith
  calc
    eLpNorm (fun omega : PotentialSample d => (aux_psf_Jval M n omega x).toReal)
        (ENNReal.ofReal q) M.P.toMeasure ≤
      eLpNorm (F ∘ translatePotentialSample x)
        (ENNReal.ofReal q) M.P.toMeasure := by
          apply eLpNorm_mono_enorm_ae
            ((prefixJ_Jval_measurable M n x).ennreal_toReal.aestronglyMeasurable)
          exact Filter.Eventually.of_forall fun omega => by
            rw [← ofReal_norm, Real.norm_eq_abs,
              abs_of_nonneg ENNReal.toReal_nonneg, enorm_eq_self]
            exact (ENNReal.ofReal_toReal_le).trans (by
              rw [aux_psf_Jval_translate M n omega x]
              exact aux_psf_Jval_le_centered_defect M n
                (translatePotentialSample x omega))
    _ = eLpNorm F (ENNReal.ofReal q) M.P.toMeasure := hcomp
    _ = paperENNRealLpNorm M.P.toMeasure q F := by
      exact (paperENNRealLpNorm_eq_eLpNorm_of_aestronglyMeasurable M.P.toMeasure hp F hFmeas.aestronglyMeasurable).symm
    _ ≤ _ := hmoment

/-- A cutoff-uniform moment bank for the literal response atom at every
deterministic center, under a moment-dependent small-disorder threshold. -/
theorem aux_psf_exists_Jval_spatial_moment_small_disorder (d : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ q : ℝ, 1 ≤ q → ∃ δ0 : ℝ, 0 < δ0 ∧
        ∀ (M : GMCModel d), 0 < M.delta → M.delta ≤ δ0 →
          ∀ (n : ℕ) (x : Vec d),
          eLpNorm (fun omega : PotentialSample d => (aux_psf_Jval M n omega x).toReal)
            (ENNReal.ofReal q) M.P.toMeasure ≤
            ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2) := by
  obtain ⟨c, C, hc, hC, hm⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.exists_cutoffNormalizedResponse_moment_bound d
  refine ⟨c, C, hc, hC, ?_⟩
  intro q hq
  obtain ⟨δ0, hδ0, hδ⟩ := aux_psf_small_disorder_admissible C q hC hq
  refine ⟨δ0, hδ0, ?_⟩
  intro M hM hM0 n x
  have hraw := hm M q hq (hδ M.delta hM hM0) n n
  simp only [min_self] at hraw
  exact aux_psf_Jval_spatial_moment_of_origin M n x q C hq hraw

end SubdiffusiveProcess.Paper

