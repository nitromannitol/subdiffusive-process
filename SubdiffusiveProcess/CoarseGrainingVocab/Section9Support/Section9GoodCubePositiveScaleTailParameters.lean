module

public import SubdiffusiveProcess.Section9.SmallDisorderExponent
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.BadEventEstimates
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeDescendantMoments
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeDescendantBesovTests
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeFiniteTail
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeEllipticityPrice
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Action
@[expose] public section

/-!
# Moment parameters for one positive-scale good-cube test

The selected exponent is large enough for both the actual descendant response
moment and the parent cutoff-ratio Besov moment. The constants precede the
model and all cutoff/translation choices.
-/

set_option autoImplicit false
open Homogenization MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.Section9
open SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
theorem exists_goodCube_smallDisorder_parameters
    (B eta epsilon R K : ℝ) (hB : 0 < B) (heta : 0 < eta)
    (hepsilon : 0 < epsilon) (hK : 0 < K) :
    ∃ a delta0 : ℝ, 0 < a ∧ 0 < delta0 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta0 →
        delta ≤ 1 / 2 ∧ 2 ≤ smallDisorderExponent a delta ∧
        R ≤ smallDisorderExponent a delta ∧
        smallDisorderExponent a delta ≤ K⁻¹ * (delta ^ 2)⁻¹ * |Real.log delta|⁻¹ ∧
        smallDisorderExponent a delta * delta ^ 2 *
          Real.log (2 + smallDisorderExponent a delta) ≤ eta ∧
        B * delta * Real.sqrt (smallDisorderExponent a delta) *
          Real.log (smallDisorderExponent a delta) ≤ epsilon := by
  obtain ⟨a, δzero, ha, hδzero, hprop⟩ :=
    exists_smallDisorderExponent_parameters B eta epsilon hB heta hepsilon
  have hevent := eventually_smallDisorderExponent_exp_neg_ge a R ha
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨TR, hTR⟩ := hevent
  set M : ℝ := max 1 (max (K * a) TR) with hMdef
  refine ⟨a, min δzero (Real.exp (-M)), ha,
    lt_min hδzero (Real.exp_pos _), ?_⟩
  intro δ hδ hδle
  obtain ⟨hhalf, hp2, heta', heps'⟩ := hprop δ hδ (hδle.trans (min_le_left _ _))
  have hδM : δ ≤ Real.exp (-M) := hδle.trans (min_le_right _ _)
  set t : ℝ := -Real.log δ with htdef
  have htM : M ≤ t := by
    have hlog := Real.log_le_log hδ hδM
    rw [Real.log_exp] at hlog
    rw [htdef]
    linarith
  have hlogneg : Real.log δ < 0 :=
    Real.log_neg hδ (lt_of_le_of_lt hhalf (by norm_num))
  have hpos : 0 < t := by rw [htdef]; linarith
  have hδexp : Real.exp (-t) = δ := by rw [htdef, neg_neg, Real.exp_log hδ]
  have hkaM : K * a ≤ M := by rw [hMdef]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hTRM : TR ≤ M := by
    rw [hMdef]
    exact (le_max_right (K * a) TR).trans (le_max_right (1:ℝ) _)
  have habslog : |Real.log δ| = t := by
    have hlogδ : Real.log δ = -t := by rw [htdef, neg_neg]
    rw [hlogδ, abs_neg, abs_of_nonneg hpos.le]
  have hkale : K * a ≤ t := hkaM.trans htM
  refine ⟨hhalf, hp2, ?_, ?_, heta', heps'⟩
  · rw [← hδexp]
    exact hTR t (hTRM.trans htM)
  · unfold smallDisorderExponent
    rw [habslog, inv_pow, inv_pow]
    have hd2pos : 0 < (δ ^ 2)⁻¹ := inv_pos.2 (sq_pos_of_pos hδ)
    have key : a * (t ^ 2)⁻¹ ≤ (K * t)⁻¹ := by
      rw [← div_eq_mul_inv, inv_eq_one_div,
        div_le_div_iff₀ (sq_pos_of_pos hpos) (mul_pos hK hpos)]
      have h2 : a * K * t ≤ t * t :=
        mul_le_mul_of_nonneg_right (by rw [mul_comm]; exact hkale) hpos.le
      nlinarith
    have hlhs : a * (δ ^ 2)⁻¹ * (t ^ 2)⁻¹ = (δ ^ 2)⁻¹ * (a * (t ^ 2)⁻¹) := by ring
    have hrhs : K⁻¹ * (δ ^ 2)⁻¹ * t⁻¹ = (δ ^ 2)⁻¹ * (K * t)⁻¹ := by
      rw [mul_inv_rev]
      ring
    rw [hlhs, hrhs]
    exact mul_le_mul_of_nonneg_left key hd2pos.le



theorem goodCube_markov_quarter_tail
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (p t : ℝ) (hp : 0 < p) (ht : 0 < t) (X : Omega → ℝ≥0∞)
    (hX : Measurable X)
    (hnorm : paperENNRealLpNorm mu p X ≤ ENNReal.ofReal (t / 4)) :
    MeasurableSet {omega | ENNReal.ofReal t < X omega} ∧
      mu {omega | ENNReal.ofReal t < X omega} ≤
        ENNReal.ofReal (Real.exp (-p * Real.log 4)) := by
  have hmeas : MeasurableSet {omega | ENNReal.ofReal t < X omega} :=
    measurableSet_lt measurable_const hX
  have hsub : {omega | ENNReal.ofReal t < X omega} ⊆
      {omega | ENNReal.ofReal t ≤ X omega} := by
    intro omega homega
    exact (show ENNReal.ofReal t < X omega from homega).le
  have hbound := measure_le_ratio_rpow_of_paperENNRealLpNorm
    (xi := p) (t := t) hp ht hX hnorm hsub
  refine ⟨hmeas, ?_⟩
  have hdiv : ENNReal.ofReal (t / 4) / ENNReal.ofReal t
      = ENNReal.ofReal ((t / 4) / t) :=
    (ENNReal.ofReal_div_of_pos ht).symm
  have hval : ((t / 4) / t) ^ p = Real.exp (-p * Real.log 4) := by
    have h1 : (t / 4) / t = (1 / 4 : ℝ) := by
      field_simp
    rw [h1, Real.rpow_def_of_pos (by positivity : (0:ℝ) < 1 / 4)]
    simp [Real.log_inv, mul_comm]
  calc
    mu {omega | ENNReal.ofReal t < X omega}
        ≤ (ENNReal.ofReal (t / 4) / ENNReal.ofReal t) ^ p := hbound
    _ = (ENNReal.ofReal ((t / 4) / t)) ^ p := by rw [hdiv]
    _ = ENNReal.ofReal (((t / 4) / t) ^ p) :=
      ENNReal.ofReal_rpow_of_pos (by positivity : 0 < (t / 4) / t)
    _ = ENNReal.ofReal (Real.exp (-p * Real.log 4)) := by rw [hval]


noncomputable def goodCubeParentBesovObservable {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ) (p : ℝ) (z : Vec d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ≥0∞ :=
  ENNReal.ofReal ((3 : ℝ)^(-(1 / 16 : ℝ) * (n : ℝ))) *
    cutoffRatioNegativeBesov M n (-1) (1 / 16) p (translatePotentialSample z omega)

theorem measurable_goodCubeParentBesovObservable {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ) (p : ℝ) (z : Vec d) :
    Measurable (goodCubeParentBesovObservable M n p z) :=
  measurable_const.mul ((measurable_cutoffRatioNegativeBesov M n (-1) (1 / 16) p).comp
    (SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.measurable_translatePotentialSample z))

theorem goodCubeParentBesovObservable_eq {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ) (p : ℝ) (z : Vec d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hf : ExactCircIntegrable (originCube d (n : ℤ))
      (fun x => _root_.SubdiffusiveProcess.Model.aCutoff M n (translatePotentialSample z omega) x - 1)) :
    goodCubeParentBesovObservable M n p z omega =
      ENNReal.ofReal ((3 : ℝ)^(-(1 / 16 : ℝ) * (n : ℝ))) *
        paperNegativeBesovCircDiagonal (originCube d (n : ℤ)) (1 / 16) p
          (fun x => _root_.SubdiffusiveProcess.Model.aCutoff M n (translatePotentialSample z omega) x - 1) hf := by
  have hr : cutoffRatioMinusOne M n (-1) (translatePotentialSample z omega) =
      (fun x => _root_.SubdiffusiveProcess.Model.aCutoff M n (translatePotentialSample z omega) x - 1) := by
    funext x
    simp [cutoffRatioMinusOne, aCutoffAtInt]
  unfold goodCubeParentBesovObservable cutoffRatioNegativeBesov
  simp only [hr]

theorem exists_goodCube_parent_besov_moment_constants (d : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (p : ℝ),
        2 ≤ p → C * p * M.delta^2 ≤ 1 →
        p * M.delta^2 * Real.log (2 + p) ≤ c → ∀ n : ℕ, ∀ z : Vec d,
          paperENNRealLpNorm M.P.toMeasure p (goodCubeParentBesovObservable M n p z) ≤
            ENNReal.ofReal (C * M.delta * Real.sqrt p * Real.log p) := by
  obtain ⟨C0, c, hC0, hc, hmoment⟩ := negativeBesov_cutoffRatio_scaleSum_moment (d := d)
  refine ⟨16 * C0, c, by positivity, hc, ?_⟩
  intro M p hp hscale hsmall n z
  have hp0 : 0 < p := by linarith
  have hsrc := hmoment M (1 / 16) p (by norm_num) (by norm_num) hp
    (by nlinarith : C0 * p * M.delta^2 ≤ 1 / 16) hsmall n (-1)
    (by norm_num) (by omega)
  unfold goodCubeParentBesovObservable
  have hmeas : Measurable (fun omega =>
      cutoffRatioNegativeBesov M n (-1) (1 / 16) p (translatePotentialSample z omega)) :=
    (measurable_cutoffRatioNegativeBesov M n (-1) (1 / 16) p).comp
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.measurable_translatePotentialSample z)
  rw [paperENNRealLpNorm_const_mul_eq M.P.toMeasure hp0 _
    (fun omega => cutoffRatioNegativeBesov M n (-1) (1 / 16) p (translatePotentialSample z omega))
    hmeas]
  rw [paperENNRealLpNorm_comp_translatePotentialSample_eq M z
    (cutoffRatioNegativeBesov M n (-1) (1 / 16) p)
    (measurable_cutoffRatioNegativeBesov M n (-1) (1 / 16) p)]
  norm_num only [one_div, inv_inv] at hsrc
  simpa only [mul_comm C0 (16 : ℝ)] using! hsrc


theorem goodCube_response_moment_quarter_budget
    {K G e T : ℝ} (hK : 0 < K) (hG : 0 < G) (he : 0 < e)
    (hT : T ≤ (e / (4 * K * G))^2 / K) :
    K * Real.sqrt (K * T) * G ≤ e / 4 := by
  have hroot : Real.sqrt (K * T) ≤ e / (4 * K * G) := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    have hmul := (le_div_iff₀ hK).mp hT
    simpa only [mul_comm T K] using hmul
  calc
    K * Real.sqrt (K * T) * G ≤ K * (e / (4 * K * G)) * G :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hroot hK.le) hG.le
    _ = e / 4 := by field_simp [hK.ne', hG.ne']


theorem exists_goodCube_positiveScale_moment_parameters
    (d J : ℕ) (e beta : ℝ) (he : 0 < e) (hbeta : 0 < beta) :
    ∃ a delta0 : ℝ, 0 < a ∧ 0 < delta0 ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ delta0 →
        let p := smallDisorderExponent a M.delta
        2 ≤ p ∧ 32 * (d : ℝ) ≤ p ∧
        ∀ n m : ℕ, m ≤ n → n - m ≤ J → ∀ z : Vec d,
          paperENNRealLpNorm M.P.toMeasure p (goodCubeParentBesovObservable M n p z) ≤
            ENNReal.ofReal (beta / 4) ∧
          paperENNRealLpNorm M.P.toMeasure p (fun omega =>
            ellipticityMomentObservable M n (m : ℤ) (1 / 8)
              (translatePotentialSample z omega)) ≤ ENNReal.ofReal (e / 4) := by
  obtain ⟨C, c, hC, hc, hbesov⟩ := exists_goodCube_parent_besov_moment_constants d
  obtain ⟨K, hK1, herror⟩ := exists_goodCube_descendant_error_moment_constant d
  have hK : 0 < K := zero_lt_one.trans_le hK1
  let G : ℝ := (3 : ℝ)^((J : ℝ) / 8)
  have hG : 0 < G := Real.rpow_pos_of_pos (by norm_num) _
  let eta : ℝ := min c (min C⁻¹ (min (2 * K)⁻¹ ((e / (4 * K * G))^2 / K)))
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hetaC : eta ≤ c := min_le_left _ _
  have hetaInvC : eta ≤ C⁻¹ := (min_le_left _ _).trans' (min_le_right _ _)
  have hetaInvK : eta ≤ (2 * K)⁻¹ :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hetaE : eta ≤ (e / (4 * K * G))^2 / K :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨a, delta0, ha, hdelta0, hchoice⟩ :=
    exists_goodCube_smallDisorder_parameters C eta (beta / 4) (max 6 (32 * (d : ℝ))) K
      hC heta (by positivity) hK
  refine ⟨a, delta0, ha, hdelta0, ?_⟩
  intro M hM
  let p := smallDisorderExponent a M.delta
  obtain ⟨hhalf, hp2, hpR, hprange, htau, hZsmall⟩ :=
    hchoice M.delta M.shellPrefix.delta_pos hM
  change 2 ≤ p ∧ 32 * (d : ℝ) ≤ p ∧ _
  have hp6 : 6 ≤ p := (le_max_left _ _).trans hpR
  have hp32 : 32 * (d : ℝ) ≤ p := (le_max_right _ _).trans hpR
  have hp0 : 0 < p := by linarith
  have hlog : 1 ≤ Real.log (2 + p) := by
    rw [← Real.exp_le_exp, Real.exp_log (by linarith : 0 < 2 + p)]
    exact (Real.exp_one_lt_d9.trans (by linarith : (2.7182818286 : ℝ) < 2 + p)).le
  have htau' : p * M.delta^2 * Real.log (2 + p) ≤ eta := htau
  have hCeta : C * eta ≤ 1 := by
    have h := (le_div_iff₀ hC).mp (show eta ≤ 1 / C by simpa only [one_div] using hetaInvC)
    nlinarith only [h]
  have hKeta : K * eta ≤ 1 / 2 := by
    have h := (le_div_iff₀ (show 0 < 2 * K by positivity)).mp
      (show eta ≤ 1 / (2 * K) by simpa only [one_div] using hetaInvK)
    nlinarith only [h]
  have hpdelta : p * M.delta^2 ≤ p * M.delta^2 * Real.log (2 + p) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hlog
      (mul_nonneg hp0.le (sq_nonneg M.delta))
  have hscale : C * p * M.delta^2 ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left (hpdelta.trans htau') hC.le
    nlinarith only [h, hCeta]
  have hEsml : K * p * Real.log (2 + p) * M.delta^2 < 1 := by
    have h := mul_le_mul_of_nonneg_left htau' hK.le
    nlinarith only [h, hKeta]
  refine ⟨hp2, hp32, ?_⟩
  intro n m hmn hmJ z
  refine ⟨(hbesov M p hp2 hscale (htau'.trans hetaC) n z).trans
    (ENNReal.ofReal_le_ofReal hZsmall), ?_⟩
  have hsrc := herror M p hp6 hp32 hprange hEsml n m J hmn hmJ z
  have hbudget := goodCube_response_moment_quarter_budget hK hG he (htau'.trans hetaE)
  have heq : K * p * Real.log (2 + p) * M.delta^2 =
      K * (p * M.delta^2 * Real.log (2 + p)) := by ring
  rw [heq] at hsrc
  exact hsrc.trans (ENNReal.ofReal_le_ofReal hbudget)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
