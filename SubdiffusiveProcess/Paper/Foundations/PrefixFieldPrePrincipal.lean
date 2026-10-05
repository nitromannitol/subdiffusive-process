module

public import SubdiffusiveProcess.Paper.in_common_scale_coupling
public import SubdiffusiveProcess.Paper.layer_regularity_moments
public import SubdiffusiveProcess.Paper.primitive_scores
public import SubdiffusiveProcess.Paper.primitive_scores_finite
public import SubdiffusiveProcess.Paper.score_family_interface
public import SubdiffusiveProcess.Paper.coherent_score_attachment
public import SubdiffusiveProcess.Paper.prop_response_compact
public import SubdiffusiveProcess.Paper.branch_candidate_setup
public import SubdiffusiveProcess.Paper.conv_represented_sequence
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.prefix_score_cauchy
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Paper.Foundations.PrefixActualPrawMeas
public import SubdiffusiveProcess.Paper.Foundations.PrefixActualFMeas
public import SubdiffusiveProcess.Paper.Foundations.PrefixActualJMeas
public import SubdiffusiveProcess.Paper.Foundations.PrefixActualRMeas
public import SubdiffusiveProcess.Paper.Foundations.PrefixActualRBank
public import SubdiffusiveProcess.Paper.Foundations.PrefixActualDMeas
public import SubdiffusiveProcess.Paper.Foundations.PrefixActualZMeas
public import Homogenization.Book.Ch02.Matrices
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Tactic



@[expose] public section

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- `L^p`-Cauchy from `L^p`-convergence to a *measurable* limit.  Mathlib's
`eLpNorm` triangle inequality needs `AEStronglyMeasurable` on both summands, and
there is no measurability-free variant (the lower Lebesgue integral is
super-additive), so the measurability of the limit is exactly what makes the
passage from clause 2 of `hResponse` to the Cauchy conclusion legal. -/
theorem aux_prefix_limit_cauchy_of_tendsto
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    (p : ℝ) (hp : 1 ≤ p) (v : ℕ → Omega → ℝ) (lim : Omega → ℝ)
    (_hv : ∀ n, AEStronglyMeasurable (v n) P)
    (_hlim : AEStronglyMeasurable lim P)
    (h : Tendsto (fun n => eLpNorm (fun om => v n om - lim om) (ENNReal.ofReal p) P)
      atTop (𝓝 0))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ n0 : ℕ, ∀ n n' : ℕ, n0 ≤ n → n0 ≤ n' →
      eLpNorm (fun om => v n om - v n' om) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal eps := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hhalf : (0 : ℝ≥0∞) < ENNReal.ofReal (eps / 2) :=
    ENNReal.ofReal_pos.mpr (by linarith)
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 ((ENNReal.tendsto_nhds_zero.mp h) _ hhalf)
  refine ⟨n0, fun n n' hn hn' => ?_⟩
  have hsplit : (fun om => v n om - v n' om) =
      (fun om => v n om - lim om) + (fun om => lim om - v n' om) := by
    funext om; simp only [Pi.add_apply]; ring
  have hadd : eLpNorm ((fun om => v n om - lim om) + fun om => lim om - v n' om)
      (ENNReal.ofReal p) P ≤
      eLpNorm (fun om => v n om - lim om) (ENNReal.ofReal p) P +
        eLpNorm (fun om => lim om - v n' om) (ENNReal.ofReal p) P :=
    eLpNorm_add_le hp1
  have hsym : eLpNorm (fun om => lim om - v n' om) (ENNReal.ofReal p) P =
      eLpNorm (fun om => v n' om - lim om) (ENNReal.ofReal p) P := by
    have hneg : (fun om => lim om - v n' om) = -(fun om => v n' om - lim om) := by
      funext om; simp only [Pi.neg_apply]; ring
    rw [hneg, eLpNorm_neg]
  rw [hsplit]
  refine hadd.trans ?_
  rw [hsym]
  refine le_trans (add_le_add (hn0 n hn) (hn0 n' hn')) ?_
  rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

section PrefixRawHelpers

theorem aux_lem_prefix_limit_actual_coordinate_cauchy_smul_mem
    {d : ℕ} {a : ℤ} {w x : Vec d} (k : ℕ) (hx : x ∈ translatedCube d a w) :
    ((3 : ℝ) ^ k) • x ∈ translatedCube d (a + k) (((3 : ℝ) ^ k) • w) := by
  rw [aux_psf_mem_translatedCube_iff] at hx ⊢
  intro i
  have h := hx i
  have h3 : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  have hsub : (((3 : ℝ) ^ k) • x) i - (((3 : ℝ) ^ k) • w) i = (3 : ℝ) ^ k * (x i - w i) := by
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [hsub, abs_mul, abs_of_pos h3, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
  calc (3 : ℝ) ^ k * |x i - w i| < (3 : ℝ) ^ k * ((3 : ℝ) ^ a / 2) :=
        mul_lt_mul_of_pos_left h h3
    _ = (3 : ℝ) ^ a * (3 : ℝ) ^ k / 2 := by ring

theorem aux_lem_prefix_limit_actual_coordinate_cauchy_self_mem
    {d : ℕ} (a : ℤ) (w : Vec d) : w ∈ translatedCube d a w := by
  rw [aux_psf_mem_translatedCube_iff]
  intro i
  simp only [sub_self, abs_zero]
  positivity

theorem aux_lem_prefix_limit_actual_coordinate_cauchy_eta_shift
    {d : ℕ} (omega : BilateralField d)
    (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hEta : ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (N k i : ℕ) (x : Vec d) :
    eta (N + k) omega (i + k) (((3 : ℝ) ^ k) • x) = eta N omega i x := by
  rw [hEta, hEta, smul_smul]
  have hidx : ((i + k : ℕ) : ℤ) - ((N + k : ℕ) : ℤ) = (i : ℤ) - (N : ℤ) := by
    push_cast; ring
  have hsc : (3 : ℝ) ^ (-((N + k : ℕ) : ℤ)) * (3 : ℝ) ^ k = (3 : ℝ) ^ (-(N : ℤ)) := by
    rw [show (-((N + k : ℕ) : ℤ)) = -(N : ℤ) + -(k : ℤ) by push_cast; ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), _root_.zpow_neg (3 : ℝ) (k : ℤ), zpow_natCast]
    field_simp
  rw [hidx, hsc]

/-- The product score is nondecreasing along the cutoff under the exact reindexing. -/
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_Psc_le
    {d : ℕ} (s : ℝ) (om1 om2 : _root_.SubdiffusiveProcess.Model.PotentialSample d) (k : ℕ)
    (hrel : ∀ (i : ℕ) (x : Vec d), om2 (i + k) (((3 : ℝ) ^ k) • x) = om1 i x)
    (P1 P2 : ℕ → Vec d → ℝ≥0∞)
    (h1 : ∀ (m : ℕ) (z : Vec d),
      P1 m z = sSup {v : ENNReal | ∃ j : ℕ,
        v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
          sSup {w : ENNReal | ∃ x : Vec d, x ∈ translatedCube d (m + 1 + j) z ∧
            w = (∏ i ∈ Finset.Icc (m - j) (m + j),
                  ENNReal.ofReal (Real.exp |om1 i x|)) +
                sSup {u : ENNReal | ∃ K : ℕ,
                  u = ∏ i ∈ Finset.Icc (m + j) (m + j + K),
                    ENNReal.ofReal (Real.exp (4 * |om1 i x - om1 i z|))}}})
    (h2 : ∀ (m : ℕ) (z : Vec d),
      P2 m z = sSup {v : ENNReal | ∃ j : ℕ,
        v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
          sSup {w : ENNReal | ∃ x : Vec d, x ∈ translatedCube d (m + 1 + j) z ∧
            w = (∏ i ∈ Finset.Icc (m - j) (m + j),
                  ENNReal.ofReal (Real.exp |om2 i x|)) +
                sSup {u : ENNReal | ∃ K : ℕ,
                  u = ∏ i ∈ Finset.Icc (m + j) (m + j + K),
                    ENNReal.ofReal (Real.exp (4 * |om2 i x - om2 i z|))}}})
    (m : ℕ) (w : Vec d) :
    P1 m w ≤ P2 (m + k) (((3 : ℝ) ^ k) • w) := by
  rw [h1, h2]
  refine sSup_le ?_
  rintro v ⟨j, rfl⟩
  refine le_sSup_of_le ⟨j, rfl⟩ ?_
  refine mul_le_mul_right ?_ _
  refine sSup_le ?_
  rintro u ⟨x, hx, rfl⟩
  have hx' : ((3 : ℝ) ^ k) • x ∈
      translatedCube d (((m + k : ℕ) : ℤ) + 1 + (j : ℤ)) (((3 : ℝ) ^ k) • w) := by
    have := aux_lem_prefix_limit_actual_coordinate_cauchy_smul_mem k hx
    convert this using 2
    push_cast; ring
  refine le_sSup_of_le ⟨((3 : ℝ) ^ k) • x, hx', rfl⟩ ?_
  refine add_le_add ?_ ?_
  · -- the pointwise product over the window: a subproduct of factors `≥ 1`
    have hL : (∏ i ∈ Finset.Icc (m - j) (m + j), ENNReal.ofReal (Real.exp |om1 i x|)) =
        ∏ i ∈ (Finset.Icc (m - j) (m + j)).map (addRightEmbedding k),
          ENNReal.ofReal (Real.exp |om2 i (((3 : ℝ) ^ k) • x)|) := by
      rw [Finset.prod_map]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      simp only [addRightEmbedding_apply, hrel]
    rw [hL]
    refine Finset.prod_le_prod_of_subset_of_one_le ?_ ?_
    · rw [Finset.map_add_right_Icc]
      intro i hi
      simp only [Finset.mem_Icc] at hi ⊢
      omega
    · intro i _ _
      exact ENNReal.one_le_ofReal.mpr (Real.one_le_exp (abs_nonneg _))
  · -- the tail product is reindexed exactly
    refine sSup_le ?_
    rintro u ⟨K, rfl⟩
    refine le_sSup_of_le ⟨K, rfl⟩ (le_of_eq ?_)
    have hIcc : Finset.Icc (m + k + j) (m + k + j + K) =
        (Finset.Icc (m + j) (m + j + K)).map (addRightEmbedding k) := by
      rw [Finset.map_add_right_Icc]
      congr 1 <;> omega
    rw [hIcc, Finset.prod_map]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp only [addRightEmbedding_apply, hrel]

/-- Evaluating the product score at the anchor point. -/
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_Psc_ge
    {d : ℕ} (s : ℝ) (om : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (P : ℕ → Vec d → ℝ≥0∞)
    (h : ∀ (m : ℕ) (z : Vec d),
      P m z = sSup {v : ENNReal | ∃ j : ℕ,
        v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
          sSup {w : ENNReal | ∃ x : Vec d, x ∈ translatedCube d (m + 1 + j) z ∧
            w = (∏ i ∈ Finset.Icc (m - j) (m + j),
                  ENNReal.ofReal (Real.exp |om i x|)) +
                sSup {u : ENNReal | ∃ K : ℕ,
                  u = ∏ i ∈ Finset.Icc (m + j) (m + j + K),
                    ENNReal.ofReal (Real.exp (4 * |om i x - om i z|))}}})
    (m j : ℕ) (w : Vec d) :
    ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
      ENNReal.ofReal (Real.exp (∑ i ∈ Finset.Icc (m - j) (m + j), |om i w|)) ≤ P m w := by
  rw [h]
  refine le_sSup_of_le ⟨j, rfl⟩ ?_
  refine mul_le_mul_right ?_ _
  refine le_sSup_of_le ⟨w, aux_lem_prefix_limit_actual_coordinate_cauchy_self_mem _ w, rfl⟩ ?_
  rw [aux_psf_prod_ofReal_exp]
  exact le_self_add

open _root_.SubdiffusiveProcess.Model

/-- The stored-gradient chain rule under the exact cutoff reindexing. -/
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_grad_shift
    {d : ℕ} (om1 om2 : PotentialSample d) (k : ℕ)
    (hrel : ∀ (i : ℕ) (x : Vec d), om2 (i + k) (((3 : ℝ) ^ k) • x) = om1 i x)
    (i : ℕ) (x : Vec d) :
    shellGradient (om2 (i + k)) (((3 : ℝ) ^ k) • x) =
      ((3 : ℝ) ^ k)⁻¹ • shellGradient (om1 i) x := by
  have h3 : (3 : ℝ) ^ k ≠ 0 := by positivity
  have hfun : om2 (i + k) = _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale (((3 : ℝ) ^ k)⁻¹) (om1 i) := by
    apply _root_.SubdiffusiveProcess.Model.PotentialField.ext
    intro y
    rw [_root_.SubdiffusiveProcess.Model.PotentialField.spatialScale_apply, ← hrel i]
    rw [smul_smul, mul_inv_cancel₀ h3, one_smul]
  have hder : _root_.SubdiffusiveProcess.Model.PotentialField.deriv (om2 (i + k)) (((3 : ℝ) ^ k) • x) =
      ((3 : ℝ) ^ k)⁻¹ • _root_.SubdiffusiveProcess.Model.PotentialField.deriv (om1 i) x := by
    rw [hfun, aux_psf_deriv_spatialScale, smul_smul, inv_mul_cancel₀ h3, one_smul]
  funext c
  simp only [shellGradient, hder, _root_.smul_apply, Pi.smul_apply, smul_eq_mul]

/-- The field score is nondecreasing along the cutoff under the exact reindexing. -/
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_Fsc_le
    {d : ℕ} (s : ℝ) (om1 om2 : PotentialSample d) (k : ℕ)
    (hrel : ∀ (i : ℕ) (x : Vec d), om2 (i + k) (((3 : ℝ) ^ k) • x) = om1 i x)
    (F1 F2 : ℕ → Vec d → ℝ≥0∞)
    (h1 : ∀ (m : ℕ) (z : Vec d),
      F1 m z = sSup {v : ENNReal | ∃ j : ℕ,
        v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
          ∑ i ∈ Finset.Icc (m - j) (m + j),
            sSup {v : ENNReal | ∃ x : Vec d, x ∈ translatedCube d (m + 1 + j) z ∧
              v = ENNReal.ofReal |(|om1 i x| + (3 : ℝ) ^ (i : ℝ) *
                Homogenization.euclideanNorm (shellGradient (om1 i) x))|}})
    (h2 : ∀ (m : ℕ) (z : Vec d),
      F2 m z = sSup {v : ENNReal | ∃ j : ℕ,
        v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
          ∑ i ∈ Finset.Icc (m - j) (m + j),
            sSup {v : ENNReal | ∃ x : Vec d, x ∈ translatedCube d (m + 1 + j) z ∧
              v = ENNReal.ofReal |(|om2 i x| + (3 : ℝ) ^ (i : ℝ) *
                Homogenization.euclideanNorm (shellGradient (om2 i) x))|}})
    (m : ℕ) (w : Vec d) :
    F1 m w ≤ F2 (m + k) (((3 : ℝ) ^ k) • w) := by
  rw [h1, h2]
  refine sSup_le ?_
  rintro v ⟨j, rfl⟩
  refine le_sSup_of_le ⟨j, rfl⟩ ?_
  refine mul_le_mul_right ?_ _
  have hterm : ∀ i : ℕ,
      sSup {v : ENNReal | ∃ x : Vec d, x ∈ translatedCube d (m + 1 + j) w ∧
        v = ENNReal.ofReal |(|om1 i x| + (3 : ℝ) ^ (i : ℝ) *
          Homogenization.euclideanNorm (shellGradient (om1 i) x))|} ≤
      sSup {v : ENNReal | ∃ x : Vec d,
        x ∈ translatedCube d ((m + k : ℕ) + 1 + j) (((3 : ℝ) ^ k) • w) ∧
        v = ENNReal.ofReal |(|om2 (i + k) x| + (3 : ℝ) ^ ((i + k : ℕ) : ℝ) *
          Homogenization.euclideanNorm (shellGradient (om2 (i + k)) x))|} := by
    intro i
    refine sSup_le ?_
    rintro v ⟨x, hx, rfl⟩
    have hx' : ((3 : ℝ) ^ k) • x ∈
        translatedCube d (((m + k : ℕ) : ℤ) + 1 + (j : ℤ)) (((3 : ℝ) ^ k) • w) := by
      have := aux_lem_prefix_limit_actual_coordinate_cauchy_smul_mem k hx
      convert this using 2
      push_cast; ring
    refine le_sSup_of_le ⟨((3 : ℝ) ^ k) • x, hx', ?_⟩ le_rfl
    rw [hrel, aux_lem_prefix_limit_actual_coordinate_cauchy_grad_shift om1 om2 k hrel,
      Homogenization.euclideanNorm_smul]
    have h3 : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
    have hpow : (3 : ℝ) ^ ((i + k : ℕ) : ℝ) = (3 : ℝ) ^ (i : ℝ) * (3 : ℝ) ^ k := by
      rw [Nat.cast_add, Real.rpow_add (by norm_num), Real.rpow_natCast, Real.rpow_natCast]
    rw [hpow, abs_inv, abs_of_pos h3]
    congr 3
    field_simp
  calc (∑ i ∈ Finset.Icc (m - j) (m + j),
        sSup {v : ENNReal | ∃ x : Vec d, x ∈ translatedCube d (m + 1 + j) w ∧
          v = ENNReal.ofReal |(|om1 i x| + (3 : ℝ) ^ (i : ℝ) *
            Homogenization.euclideanNorm (shellGradient (om1 i) x))|})
      ≤ ∑ i ∈ Finset.Icc (m - j) (m + j),
        sSup {v : ENNReal | ∃ x : Vec d,
          x ∈ translatedCube d ((m + k : ℕ) + 1 + j) (((3 : ℝ) ^ k) • w) ∧
          v = ENNReal.ofReal |(|om2 (i + k) x| + (3 : ℝ) ^ ((i + k : ℕ) : ℝ) *
            Homogenization.euclideanNorm (shellGradient (om2 (i + k)) x))|} :=
        Finset.sum_le_sum (fun i _ => hterm i)
    _ = ∑ i ∈ (Finset.Icc (m - j) (m + j)).map (addRightEmbedding k),
        sSup {v : ENNReal | ∃ x : Vec d,
          x ∈ translatedCube d ((m + k : ℕ) + 1 + j) (((3 : ℝ) ^ k) • w) ∧
          v = ENNReal.ofReal |(|om2 i x| + (3 : ℝ) ^ (i : ℝ) *
            Homogenization.euclideanNorm (shellGradient (om2 i) x))|} := by
        rw [Finset.sum_map]
        rfl
    _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset ?_
        rw [Finset.map_add_right_Icc]
        intro i hi
        simp only [Finset.mem_Icc] at hi ⊢
        omega


/-- Dominated almost-everywhere convergence gives the `L^p`-Cauchy property
along the sequence. -/
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_of_dominated
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega) [IsFiniteMeasure P]
    (p : ℝ) (hp : 1 ≤ p) (v : ℕ → Omega → ℝ) (lim G : Omega → ℝ)
    (hv : ∀ n, AEStronglyMeasurable (v n) P)
    (hG : MemLp G (ENNReal.ofReal p) P)
    (hbound : ∀ n, ∀ᵐ om ∂P, |v n om| ≤ G om)
    (hlim : ∀ᵐ om ∂P, Tendsto (fun n => v n om) atTop (𝓝 (lim om)))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ n0 : ℕ, ∀ n n' : ℕ, n0 ≤ n → n0 ≤ n' →
      eLpNorm (fun om => v n om - v n' om) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal eps := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hlimmeas : AEStronglyMeasurable lim P :=
    aestronglyMeasurable_of_tendsto_ae atTop hv hlim
  have hlimbound : ∀ᵐ om ∂P, |lim om| ≤ G om := by
    have hall : ∀ᵐ om ∂P, ∀ n, |v n om| ≤ G om := ae_all_iff.mpr hbound
    filter_upwards [hall, hlim] with om hom hlom
    exact le_of_tendsto' ((continuous_abs.tendsto _).comp hlom) hom
  have hlimLp : MemLp lim (ENNReal.ofReal p) P := by
    refine hG.of_le hlimmeas ?_
    filter_upwards [hlimbound] with om hom
    have hG0 : 0 ≤ G om := (abs_nonneg _).trans hom
    simpa [Real.norm_eq_abs, abs_of_nonneg hG0] using hom
  have hui : UnifIntegrable v (ENNReal.ofReal p) P := by
    apply unifIntegrable_iff'.mpr
    intro ε hε
    obtain ⟨δ, hδ, hδG⟩ := hG.eLpNorm_indicator_le hp1 hptop hε
    refine ⟨δ, hδ, fun n s hs hμs => le_trans ?_ (hδG s hs hμs)⟩
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict (f := v n) hs]
    refine eLpNorm_mono_ae (f := s.indicator (v n)) (g := s.indicator G) ((hv n).indicator hs) ?_
    filter_upwards [hbound n] with om hom
    by_cases hmem : om ∈ s
    · have hG0 : 0 ≤ G om := (abs_nonneg _).trans hom
      simpa [Set.indicator_of_mem hmem, Real.norm_eq_abs, abs_of_nonneg hG0] using hom
    · simp [Set.indicator_of_notMem hmem]
  have htend : Tendsto (fun n => eLpNorm (v n - lim) (ENNReal.ofReal p) P) atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendsto_ae hp1 hptop hv hlimLp hui hlim
  have hp1' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := hp1
  have hhalf : (0 : ℝ≥0∞) < ENNReal.ofReal (eps / 2) :=
    ENNReal.ofReal_pos.mpr (by linarith)
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 ((ENNReal.tendsto_nhds_zero.mp htend) _ hhalf)
  refine ⟨n0, fun n n' hn hn' => ?_⟩
  have hsplit : (fun om => v n om - v n' om) = (v n - lim) + (lim - v n') := by
    funext om; simp only [Pi.add_apply, Pi.sub_apply]; ring
  have hsym : eLpNorm (lim - v n') (ENNReal.ofReal p) P =
      eLpNorm (v n' - lim) (ENNReal.ofReal p) P := by
    rw [← neg_sub, eLpNorm_neg]
  rw [hsplit]
  refine (eLpNorm_add_le hp1').trans ?_
  rw [hsym]
  refine le_trans (add_le_add (hn0 n hn) (hn0 n' hn')) ?_
  rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- A uniformly bounded, almost-everywhere convergent sequence is `L^p`-Cauchy. -/
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_of_bounded
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega) [IsFiniteMeasure P]
    (p : ℝ) (hp : 1 ≤ p) (v : ℕ → Omega → ℝ) (lim : Omega → ℝ) (C : ℝ)
    (hv : ∀ n, AEStronglyMeasurable (v n) P)
    (hbound : ∀ n, ∀ᵐ om ∂P, |v n om| ≤ C)
    (hlim : ∀ᵐ om ∂P, Tendsto (fun n => v n om) atTop (𝓝 (lim om)))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ n0 : ℕ, ∀ n n' : ℕ, n0 ≤ n → n0 ≤ n' →
      eLpNorm (fun om => v n om - v n' om) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal eps :=
  aux_lem_prefix_limit_actual_coordinate_cauchy_of_dominated P p hp v lim (fun _ => C)
    hv (memLp_const C) hbound hlim eps heps

/-- A nondecreasing `ENNReal` sequence with finite supremum converges after `toReal`. -/
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_toReal_tendsto
    (a : ℕ → ℝ≥0∞) (ha : Monotone a) (hfin : (⨆ n, a n) ≠ ⊤) :
    Tendsto (fun n => (a n).toReal) atTop (𝓝 (⨆ n, a n).toReal) :=
  (ENNReal.tendsto_toReal hfin).comp (tendsto_atTop_iSup ha)

/-- The raw field and product scores of the actual prefix coordinate are
nondecreasing in the cutoff, almost surely. -/
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_raw_mono
    {d : ℕ} [NeZero d] (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s eps : ℝ)
    (omega : BilateralField d)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
    (hPrim : ∀ N, primitive_scores d M s eps (eta N omega)
        (fun m y => F N m y omega) (fun m y => Praw N m y omega)
        (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
        (fun m y => Z N m y omega) (fun m y => rawGood N m y omega))
    (n : ℤ) (z : Vec d) (N N' : ℕ) (hn : n ≤ (N : ℤ)) (hNN' : N ≤ N') :
    F N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega ≤
        F N' ((N' : ℤ) - n).toNat ((3 : ℝ) ^ N' • z) omega ∧
      Praw N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega ≤
        Praw N' ((N' : ℤ) - n).toNat ((3 : ℝ) ^ N' • z) omega := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hNN'
  have hm : (((N + k : ℕ) : ℤ) - n).toNat = ((N : ℤ) - n).toNat + k := by
    push_cast; omega
  have hw : (3 : ℝ) ^ (N + k) • z = (3 : ℝ) ^ k • ((3 : ℝ) ^ N • z) := by
    rw [smul_smul, pow_add, mul_comm]
  have hrel := aux_lem_prefix_limit_actual_coordinate_cauchy_eta_shift omega eta hEta N k
  rw [hm, hw]
  exact ⟨aux_lem_prefix_limit_actual_coordinate_cauchy_Fsc_le s (eta N omega)
      (eta (N + k) omega) k hrel _ _ (hPrim N).2.2.2.2.1 (hPrim (N + k)).2.2.2.2.1 _ _,
    aux_lem_prefix_limit_actual_coordinate_cauchy_Psc_le s (eta N omega)
      (eta (N + k) omega) k hrel _ _ (hPrim N).2.2.2.2.2.1 (hPrim (N + k)).2.2.2.2.2.1 _ _⟩

/-- The anchor-point lower bound on the raw product score of the actual prefix
coordinate, in bilateral-layer coordinates. -/
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_Praw_ge
    {d : ℕ} [NeZero d] (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s eps : ℝ)
    (omega : BilateralField d)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
    (hPrim : ∀ N, primitive_scores d M s eps (eta N omega)
        (fun m y => F N m y omega) (fun m y => Praw N m y omega)
        (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
        (fun m y => Z N m y omega) (fun m y => rawGood N m y omega))
    (z : Vec d) (N m j : ℕ) :
    ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
        ENNReal.ofReal (Real.exp (∑ i ∈ Finset.Icc (m - j) (m + j),
          |omega ((i : ℤ) - (N : ℤ)) z|)) ≤
      Praw N m ((3 : ℝ) ^ N • z) omega := by
  have h := aux_lem_prefix_limit_actual_coordinate_cauchy_Psc_ge s (eta N omega)
    (fun m y => Praw N m y omega) (hPrim N).2.2.2.2.2.1 m j ((3 : ℝ) ^ N • z)
  have hval : ∀ i : ℕ, eta N omega i ((3 : ℝ) ^ N • z) = omega ((i : ℤ) - (N : ℤ)) z := by
    intro i
    rw [hEta, smul_smul, _root_.zpow_neg, zpow_natCast, inv_mul_cancel₀ (by positivity), one_smul]
  simp only [hval] at h
  exact h


/-- Almost-sure form of `aux_lem_prefix_limit_actual_coordinate_cauchy_raw_mono`,
stated with exactly the target's `hEta` and `hPrimitive`. -/
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_raw_mono_ae
    {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s eps : ℝ)
    (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
    (hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      primitive_scores d M s eps (eta N omega)
        (fun m y => F N m y omega) (fun m y => Praw N m y omega)
        (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
        (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (n : ℤ) (z : Vec d) (N N' : ℕ), n ≤ (N : ℤ) → N ≤ N' →
        F N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega ≤
            F N' ((N' : ℤ) - n).toNat ((3 : ℝ) ^ N' • z) omega ∧
          Praw N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega ≤
            Praw N' ((N' : ℤ) - n).toNat ((3 : ℝ) ^ N' • z) omega := by
  filter_upwards [hEta, hPrimitive] with omega hE hP
  intro n z N N' hn hNN'
  exact aux_lem_prefix_limit_actual_coordinate_cauchy_raw_mono M s eps omega eta hE
    F Praw Rraw Draw Z rawGood hP n z N N' hn hNN'

end PrefixRawHelpers

section PrefixScaledHelpers
open MeasureTheory _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab

theorem aux_prefix_actual_layer_rescaled_cube
    {d : ℕ} (i n : ℕ) (hin : i ≤ n) (z x : Vec d)
    (hx : x ∈ translatedCube d (n : ℤ) z) :
    ((3 : ℝ) ^ (-(i : ℤ))) • (x - z) ∈
      translatedCube d ((n - i : ℕ) : ℤ) (0 : Vec d) := by
  rw [aux_psf_mem_translatedCube_iff] at hx ⊢
  intro k
  have h := hx k
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.zero_apply, sub_zero, abs_mul]
  have h3 : 0 < (3 : ℝ) ^ (-(i : ℤ)) := zpow_pos (by norm_num) _
  rw [abs_of_pos h3]
  have hscale : (3 : ℝ) ^ (-(i : ℤ)) * ((3 : ℝ) ^ (n : ℤ) / 2) =
      (3 : ℝ) ^ (((n - i : ℕ) : ℤ)) / 2 := by
    rw [← mul_div_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    rw [Int.natCast_sub hin]
    ring
  calc
    (3 : ℝ) ^ (-(i : ℤ)) * |x k - z k| <
        (3 : ℝ) ^ (-(i : ℤ)) * ((3 : ℝ) ^ (n : ℤ) / 2) :=
      mul_lt_mul_of_pos_left h h3
    _ = _ := hscale

/-- Scale-adapted finite cell cover; its index cardinality depends on `n-i`. -/
theorem aux_prefix_actual_layer_scale_cover
    {d : ℕ} (i n : ℕ) (hin : i ≤ n) (z x : Vec d)
    (hx : x ∈ translatedCube d (n : ℤ) z) :
    ∃ k : Fin d → Fin (2 * 3 ^ (n - i) + 1),
      ((3 : ℝ) ^ (-(i : ℤ))) • (x - z) -
        aux_psf_center (n - i) (0 : Vec d) (fun j => (k j : ℕ)) ∈ cube d 0 :=
  aux_psf_cover (n - i) 0 _ (aux_prefix_actual_layer_rescaled_cube i n hin z x hx)

/-- The adapted cell catalogue for every layer in the raw field-score window
has a cardinal bound independent of the cutoff `m`. -/
theorem aux_prefix_actual_scale_gap_card_bound (d m j i : ℕ)
    (hi : i ∈ Finset.Icc (m - j) (m + j)) :
    (2 * 3 ^ ((m + 1 + j) - i) + 1) ^ d ≤
      (2 * 3 ^ (2 * j + 1) + 1) ^ d := by
  have hi_lo : m - j ≤ i := (Finset.mem_Icc.mp hi).1
  have hgap : (m + 1 + j) - i ≤ 2 * j + 1 := by omega
  exact Nat.pow_le_pow_left (by
    have hp : 3 ^ ((m + 1 + j) - i) ≤ 3 ^ (2 * j + 1) := Nat.pow_le_pow_right (by omega) hgap
    omega) d


theorem aux_prefix_actual_unscale_shell {d : ℕ} (i : ℕ) (g : PotentialField d) :
    _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale ((3 : ℝ) ^ i) (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale i g) = g := by
  apply _root_.SubdiffusiveProcess.Model.PotentialField.ext
  intro x
  rw [_root_.SubdiffusiveProcess.Model.PotentialField.spatialScale_apply, _root_.SubdiffusiveProcess.Model.PotentialField.triadicScale_apply, smul_smul]
  rw [inv_mul_cancel₀ (by positivity : (3 : ℝ) ^ i ≠ 0), one_smul]

/-- The scale-adapted cell field has exactly the zero-layer law. -/
theorem aux_prefix_actual_scaled_cell_law {d : ℕ} (M : GMCModel d)
    (i : ℕ) (y : Vec d) :
    Measure.map (fun omega : PotentialSample d =>
        _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale ((3 : ℝ) ^ i)
          (_root_.SubdiffusiveProcess.Model.PotentialField.translate (((3 : ℝ) ^ i) • y) (omega i)))
        M.P.toMeasure = (zeroPotentialLaw M.P).toMeasure := by
  let r : ℝ := (3 : ℝ) ^ i
  have hs : Measurable (_root_.SubdiffusiveProcess.Model.PotentialField.spatialScale (d := d) r) :=
    (_root_.SubdiffusiveProcess.Model.PotentialField.continuous_spatialScale r).measurable
  have ht : Measurable (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale (d := d) i) :=
    _root_.SubdiffusiveProcess.Model.PotentialField.measurable_triadicScale i
  have htr : Measurable (fun omega : PotentialSample d =>
      _root_.SubdiffusiveProcess.Model.PotentialField.translate (r • y) (omega i)) :=
    (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate (r • y)).comp
      (measurable_potentialCoordinate (d := d) i)
  calc
    Measure.map (fun omega : PotentialSample d =>
        _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale r (_root_.SubdiffusiveProcess.Model.PotentialField.translate (r • y) (omega i)))
        M.P.toMeasure =
        Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.spatialScale r)
          (Measure.map (fun omega : PotentialSample d =>
            _root_.SubdiffusiveProcess.Model.PotentialField.translate (r • y) (omega i)) M.P.toMeasure) :=
      (Measure.map_map hs htr).symm
    _ = Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.spatialScale r)
          (Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale i)
            (zeroPotentialLaw M.P).toMeasure) := by
      rw [aux_psf_map_cell M i (r • y)]
    _ = Measure.map (fun g : PotentialField d =>
          _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale r (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale i g))
            (zeroPotentialLaw M.P).toMeasure := Measure.map_map hs ht
    _ = (zeroPotentialLaw M.P).toMeasure := by
      have hf : (fun g : PotentialField d =>
          _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale r (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale i g)) = id := by
        funext g
        exact aux_prefix_actual_unscale_shell i g
      rw [hf, Measure.map_id]

/-- The actual layer value and scaled gradient on a physical `3^i` cell are
bounded by the existing unit-cell observable of its unscaled field. -/
theorem aux_prefix_actual_scaled_cellObs_bound {d : ℕ} (i : ℕ)
    (omega : PotentialSample d) (y u : Vec d) (hu : u ∈ cube d 0) :
    let r : ℝ := (3 : ℝ) ^ i
    let v : PotentialField d := _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale r
      (_root_.SubdiffusiveProcess.Model.PotentialField.translate (r • y) (omega i))
    |omega i (r • (u + y))| + r *
      Homogenization.euclideanNorm (shellGradient (omega i) (r • (u + y))) ≤
      aux_psf_cellObs 0 (0 : Vec d) (fun _ => v) := by
  dsimp
  set r : ℝ := (3 : ℝ) ^ i with hr
  set x : Vec d := r • (u + y) with hx
  set v : PotentialField d := _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale r
    (_root_.SubdiffusiveProcess.Model.PotentialField.translate (r • y) (omega i)) with hv
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hval : v u = omega i x := by
    rw [hv, _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale_apply,
      _root_.SubdiffusiveProcess.Model.PotentialField.translate_apply, ← smul_add]
  have hder : _root_.SubdiffusiveProcess.Model.PotentialField.deriv v u = r • _root_.SubdiffusiveProcess.Model.PotentialField.deriv (omega i) x := by
    rw [hv, aux_psf_deriv_spatialScale, aux_psf_deriv_translate]
    rw [← smul_add]
  have hgrad : shellGradient v u = r • shellGradient (omega i) x := by
    funext k
    simp only [shellGradient, hder, Pi.smul_apply, _root_.smul_apply,
      smul_eq_mul]
  have hnorm : Homogenization.euclideanNorm (shellGradient v u) =
      r * Homogenization.euclideanNorm (shellGradient (omega i) x) := by
    rw [hgrad, Homogenization.euclideanNorm_smul, abs_of_pos hrpos]
  have hunit : u - (0 : Vec d) ∈ cube d 0 := by simpa using hu
  have hbound := aux_psf_le_cellObs 0 (0 : Vec d) u (fun _ => v) hunit
  simpa only [pow_zero, one_mul, hval, hnorm] using! hbound

/-- The scale-adapted observable has the same sub-Gaussian moment as the
original unit-cell observable, uniformly over layer and cell centre. -/
theorem aux_prefix_actual_scaled_cell_exp {d : ℕ} (M : GMCModel d)
    (i : ℕ) (y : Vec d) :
    (∫⁻ omega : PotentialSample d,
      ENNReal.ofReal (Real.exp
        ((aux_psf_cellObs 0 (0 : Vec d) (fun _ =>
          _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale ((3 : ℝ) ^ i)
            (_root_.SubdiffusiveProcess.Model.PotentialField.translate (((3 : ℝ) ^ i) • y) (omega i))) /
          aux_psf_sigma M) ^ (2 : ℕ))) ∂M.P.toMeasure) ≤ 2 := by
  let f : PotentialSample d → PotentialField d := fun omega =>
    _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale ((3 : ℝ) ^ i)
      (_root_.SubdiffusiveProcess.Model.PotentialField.translate (((3 : ℝ) ^ i) • y) (omega i))
  let X : PotentialField d → ℝ := fun g =>
    g.unitCubeValueNorm + (d : ℝ) * g.unitCubeDerivNorm
  let F : PotentialField d → ENNReal := fun g =>
    ENNReal.ofReal (Real.exp ((X g / aux_psf_sigma M) ^ (2 : ℕ)))
  have hfmeas : Measurable f :=
    ((_root_.SubdiffusiveProcess.Model.PotentialField.continuous_spatialScale ((3 : ℝ) ^ i)).measurable).comp
      ((_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate (((3 : ℝ) ^ i) • y)).comp
        (measurable_potentialCoordinate (d := d) i))
  have hFmeas : Measurable F := by
    dsimp [F, X]
    exact (((_root_.SubdiffusiveProcess.Model.PotentialField.unitCubeValueNorm_measurable.add
      (_root_.SubdiffusiveProcess.Model.PotentialField.unitCubeDerivNorm_measurable.const_mul _)).div_const _).pow_const _).exp.ennreal_ofReal
  have hsig : 0 < aux_psf_sigma M := aux_psf_sigma_pos M
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hpoint : ∀ g : PotentialField d, F g ≤
      ENNReal.ofReal (Real.exp
        ((_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g / M.delta) ^ (2 : ℕ))) := by
    intro g
    have hval := _root_.SubdiffusiveProcess.Model.PotentialField.unitCubeValueNorm_nonneg g
    have hder := _root_.SubdiffusiveProcess.Model.PotentialField.unitCubeDerivNorm_nonneg g
    have hlip := _root_.SubdiffusiveProcess.Model.PotentialField.unitCubeDerivLipschitzSeminorm_nonneg g
    have hg2 : _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g =
        g.unitCubeValueNorm + g.unitCubeDerivNorm +
          g.unitCubeDerivLipschitzSeminorm := rfl
    have hX0 : 0 ≤ X g := by dsimp [X]; positivity
    have hg0 : 0 ≤ _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g :=
      _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg g
    have hratio : X g / aux_psf_sigma M ≤
        _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g / M.delta := by
      rw [div_le_div_iff₀ hsig hdelta]
      have hXle : X g ≤ (1 + (d : ℝ)) * _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g := by
        dsimp [X]
        rw [hg2]
        nlinarith [mul_nonneg (Nat.cast_nonneg d) hval,
          mul_nonneg (Nat.cast_nonneg d) hlip]
      have hmul := mul_le_mul_of_nonneg_right hXle hdelta.le
      dsimp [aux_psf_sigma]
      nlinarith
    have hsq : (X g / aux_psf_sigma M) ^ (2 : ℕ) ≤
        (_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g / M.delta) ^ (2 : ℕ) := by
      have h0 : 0 ≤ X g / aux_psf_sigma M := div_nonneg hX0 hsig.le
      nlinarith
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hsq)
  have hrewrite : ∀ omega : PotentialSample d,
      aux_psf_cellObs 0 (0 : Vec d) (fun _ => f omega) = X (f omega) := by
    intro omega
    have htrans : _root_.SubdiffusiveProcess.Model.PotentialField.translate (0 : Vec d) (f omega) = f omega := by
      apply _root_.SubdiffusiveProcess.Model.PotentialField.ext
      intro x
      simp [_root_.SubdiffusiveProcess.Model.PotentialField.translate_apply]
    simp [aux_psf_cellObs, X, htrans]
  change (∫⁻ omega, ENNReal.ofReal (Real.exp
    ((aux_psf_cellObs 0 (0 : Vec d) (fun _ => f omega) / aux_psf_sigma M) ^ (2 : ℕ)))
      ∂M.P.toMeasure) ≤ 2
  simp_rw [hrewrite]
  change (∫⁻ omega, F (f omega) ∂M.P.toMeasure) ≤ 2
  calc
    (∫⁻ omega, F (f omega) ∂M.P.toMeasure) =
        ∫⁻ g, F g ∂Measure.map f M.P.toMeasure :=
      (lintegral_map hFmeas hfmeas).symm
    _ = ∫⁻ g, F g ∂(zeroPotentialLaw M.P).toMeasure := by
      rw [aux_prefix_actual_scaled_cell_law M i y]
    _ ≤ ∫⁻ g, ENNReal.ofReal (Real.exp
        ((_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g / M.delta) ^ (2 : ℕ)))
          ∂(zeroPotentialLaw M.P).toMeasure := lintegral_mono hpoint
    _ ≤ 2 := aux_psf_orlicz M

end PrefixScaledHelpers

section PrefixRawAlongPhi
open MeasureTheory Filter Topology SubdiffusiveProcess _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab

/-- The exact coupled raw field/product scores increase along the prescribed cutoff subsequence. -/
theorem aux_prefix_actual_raw_scores_mono_along_phi
    {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (s eps : ℝ)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
    (hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      primitive_scores d M s eps (eta N omega)
        (fun m y => F N m y omega) (fun m y => Praw N m y omega)
        (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
        (fun m y => Z N m y omega) (fun m y => rawGood N m y omega))
    (phi : ℕ → ℕ) (hphi : StrictMono phi) (n : ℤ) (z : Vec d) :
    ∃ k0 : ℕ, ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ k k' : ℕ, k0 ≤ k → k ≤ k' →
        F (phi k) (((phi k : ℕ) : ℤ) - n).toNat ((3 : ℝ) ^ (phi k) • z) omega ≤
          F (phi k') (((phi k' : ℕ) : ℤ) - n).toNat
            ((3 : ℝ) ^ (phi k') • z) omega ∧
        Praw (phi k) (((phi k : ℕ) : ℤ) - n).toNat ((3 : ℝ) ^ (phi k) • z) omega ≤
          Praw (phi k') (((phi k' : ℕ) : ℤ) - n).toNat
            ((3 : ℝ) ^ (phi k') • z) omega := by
  refine ⟨n.toNat, ?_⟩
  filter_upwards [aux_lem_prefix_limit_actual_coordinate_cauchy_raw_mono_ae
      M s eps eta hEta F Praw Rraw Draw Z rawGood hPrimitive] with omega hω
  intro k k' hk hkk'
  have hn : n ≤ (phi k : ℤ) := by
    have hphi_k : k ≤ phi k := hphi.id_le k
    have hk' : n ≤ (k : ℤ) := by omega
    exact hk'.trans (by exact_mod_cast hphi_k)
  exact hω n z (phi k) (phi k') hn (hphi.monotone hkk')


/-- Eventual monotonicity yields convergence in `ENNReal`, possibly to infinity. -/
theorem aux_prefix_actual_tail_mono_tendsto (a : ℕ → ENNReal) (k0 : ℕ)
    (hmono : ∀ k k', k0 ≤ k → k ≤ k' → a k ≤ a k') :
    Tendsto a atTop (𝓝 (⨆ j, a (j + k0))) := by
  have hshift : Monotone (fun j => a (j + k0)) := by
    intro j j' hj
    exact hmono (j + k0) (j' + k0) (Nat.le_add_left _ _) (Nat.add_le_add_right hj _)
  exact (tendsto_add_atTop_iff_nat k0).mp (tendsto_atTop_iSup hshift)


/-- The actual raw field and product scores have extended-real limits along `phi`. -/
theorem aux_prefix_actual_raw_scores_tendsto_along_phi
    {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (s eps : ℝ)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
    (hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      primitive_scores d M s eps (eta N omega)
        (fun m y => F N m y omega) (fun m y => Praw N m y omega)
        (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
        (fun m y => Z N m y omega) (fun m y => rawGood N m y omega))
    (phi : ℕ → ℕ) (hphi : StrictMono phi) (n : ℤ) (z : Vec d) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ k0 : ℕ,
      Tendsto (fun k => F (phi k) (((phi k : ℕ) : ℤ) - n).toNat
        ((3 : ℝ) ^ (phi k) • z) omega) atTop
        (𝓝 (⨆ j, F (phi (j + k0))
          (((phi (j + k0) : ℕ) : ℤ) - n).toNat
          ((3 : ℝ) ^ (phi (j + k0)) • z) omega)) ∧
      Tendsto (fun k => Praw (phi k) (((phi k : ℕ) : ℤ) - n).toNat
        ((3 : ℝ) ^ (phi k) • z) omega) atTop
        (𝓝 (⨆ j, Praw (phi (j + k0))
          (((phi (j + k0) : ℕ) : ℤ) - n).toNat
          ((3 : ℝ) ^ (phi (j + k0)) • z) omega)) := by
  obtain ⟨k0, hmono⟩ := aux_prefix_actual_raw_scores_mono_along_phi M s eps eta hEta
    F Praw Rraw Draw Z rawGood hPrimitive phi hphi n z
  filter_upwards [hmono] with omega hω
  refine ⟨k0, aux_prefix_actual_tail_mono_tendsto _ k0
      (fun k k' hk hkk' => (hω k k' hk hkk').1),
    aux_prefix_actual_tail_mono_tendsto _ k0
      (fun k k' hk hkk' => (hω k k' hk hkk').2)⟩

end PrefixRawAlongPhi
open _root_.SubdiffusiveProcess.Model

/-- A finite maximum inherits a square-exponential moment by a union bound. -/
theorem aux_prefix_finite_max_exp_sq
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) (s : Finset ι) (hs : s.Nonempty)
    (f : ι → Ω → ℝ) (σ : ℝ)
    (hf : ∀ i ∈ s, Measurable (f i))
    (hcell : ∀ i ∈ s,
      (∫⁻ ω, ENNReal.ofReal (Real.exp (((f i ω) / σ) ^ (2 : ℕ))) ∂μ) ≤ 2) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp
      (((s.sup' hs (fun i => f i ω)) / σ) ^ (2 : ℕ))) ∂μ) ≤
      ((s.card : ℝ≥0∞) * 2) := by
  have hpt : ∀ ω : Ω,
      ENNReal.ofReal (Real.exp (((s.sup' hs (fun i => f i ω)) / σ) ^ (2 : ℕ))) ≤
        ∑ i ∈ s, ENNReal.ofReal (Real.exp (((f i ω) / σ) ^ (2 : ℕ))) := by
    intro ω
    obtain ⟨i, hi, heq⟩ := s.exists_mem_eq_sup' hs (fun i => f i ω)
    rw [heq]
    exact Finset.single_le_sum (f := fun i =>
      ENNReal.ofReal (Real.exp (((f i ω) / σ) ^ (2 : ℕ))))
      (fun i _ => zero_le) hi
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_finsetSum _ (fun i hi =>
    ((((hf i hi).div_const _).pow_const _).exp).ennreal_ofReal)]
  calc
    (∑ i ∈ s, ∫⁻ ω, ENNReal.ofReal (Real.exp (((f i ω) / σ) ^ (2 : ℕ))) ∂μ) ≤
        ∑ _i ∈ s, (2 : ℝ≥0∞) := Finset.sum_le_sum (fun i hi => hcell i hi)
    _ = (s.card : ℝ≥0∞) * 2 := by rw [Finset.sum_const, nsmul_eq_mul]

/-- Measurability of a scale-adapted cell observation. -/
theorem aux_prefix_bank_cell_measurable {d : ℕ} (i : ℕ) (y : Vec d) :
    Measurable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      aux_psf_cellObs 0 (0 : Vec d) (fun _ =>
        _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale ((3 : ℝ) ^ i)
          (_root_.SubdiffusiveProcess.Model.PotentialField.translate (((3 : ℝ) ^ i) • y)
            (omega i)))) := by
  let f : _root_.SubdiffusiveProcess.Model.PotentialSample d →
      _root_.SubdiffusiveProcess.Model.PotentialField d := fun omega =>
    _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale ((3 : ℝ) ^ i)
      (_root_.SubdiffusiveProcess.Model.PotentialField.translate (((3 : ℝ) ^ i) • y)
        (omega i))
  have hf : Measurable f :=
    ((_root_.SubdiffusiveProcess.Model.PotentialField.continuous_spatialScale
      ((3 : ℝ) ^ i)).measurable).comp
      ((_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate
        (((3 : ℝ) ^ i) • y)).comp
          (measurable_potentialCoordinate (d := d) i))
  have hobs : Measurable (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d =>
      g.unitCubeValueNorm + (d : ℝ) * g.unitCubeDerivNorm) :=
    _root_.SubdiffusiveProcess.Model.PotentialField.unitCubeValueNorm_measurable.add
      (_root_.SubdiffusiveProcess.Model.PotentialField.unitCubeDerivNorm_measurable.const_mul _)
  have hzero : ∀ g : _root_.SubdiffusiveProcess.Model.PotentialField d,
      aux_psf_cellObs 0 (0 : Vec d) (fun _ => g) =
        g.unitCubeValueNorm + (d : ℝ) * g.unitCubeDerivNorm := by
    intro g
    have ht : _root_.SubdiffusiveProcess.Model.PotentialField.translate (0 : Vec d) g = g := by
      apply _root_.SubdiffusiveProcess.Model.PotentialField.ext
      intro x
      simp [_root_.SubdiffusiveProcess.Model.PotentialField.translate_apply]
    simp [aux_psf_cellObs, ht]
  simpa only [hzero] using! hobs.comp hf

/-- Sub-Gaussian moment for the actual scale-adapted finite bank. -/
theorem aux_prefix_bank_maxObs_exp_sq {d : ℕ} (M : GMCModel d)
    (i n : ℕ) (z : Vec d) :
    (∫⁻ omega : PotentialSample d,
      ENNReal.ofReal (Real.exp
        ((aux_prefix_bank_maxObs i n z omega / aux_psf_sigma M) ^ (2 : ℕ)))
          ∂M.P.toMeasure) ≤
      (((aux_psf_cells d (n - i)).card : ℝ≥0∞) * 2) := by
  classical
  let q : ℝ := (3 : ℝ) ^ (-(i : ℤ))
  let r : ℝ := (3 : ℝ) ^ i
  let f : (Fin d → ℕ) → PotentialSample d → ℝ := fun k omega =>
    aux_psf_cellObs 0 (0 : Vec d) (fun _ =>
      _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale r
        (_root_.SubdiffusiveProcess.Model.PotentialField.translate
          (r • aux_psf_center (n - i) (q • z) k) (omega i)))
  have hf : ∀ k ∈ aux_psf_cells d (n - i), Measurable (f k) := by
    intro k _
    exact aux_prefix_bank_cell_measurable i (aux_psf_center (n - i) (q • z) k)
  have hcell : ∀ k ∈ aux_psf_cells d (n - i),
      (∫⁻ omega : PotentialSample d,
        ENNReal.ofReal (Real.exp ((f k omega / aux_psf_sigma M) ^ (2 : ℕ)))
          ∂M.P.toMeasure) ≤ 2 := by
    intro k _
    exact aux_prefix_actual_scaled_cell_exp M i (aux_psf_center (n - i) (q • z) k)
  exact aux_prefix_finite_max_exp_sq M.P.toMeasure (aux_psf_cells d (n - i))
    (aux_psf_cells_nonempty d (n - i)) f (aux_psf_sigma M) hf hcell

/-- The window's exponential moment uses only a bank of size depending on
the discount depth, never on the cutoff. -/
theorem aux_prefix_bank_raw_window_exp_sq {d : ℕ} (M : GMCModel d)
    (m j i : ℕ) (hi : i ∈ Finset.Icc (m - j) (m + j)) (z : Vec d) :
    (∫⁻ omega : PotentialSample d,
      ENNReal.ofReal (Real.exp
        ((aux_prefix_bank_maxObs i (m + 1 + j) z omega / aux_psf_sigma M) ^ (2 : ℕ)))
          ∂M.P.toMeasure) ≤
      (((2 * 3 ^ (2 * j + 1) + 1) ^ d : ℕ) : ℝ≥0∞) * 2 := by
  refine (aux_prefix_bank_maxObs_exp_sq M i (m + 1 + j) z).trans ?_
  have hcard : (aux_psf_cells d ((m + 1 + j) - i)).card ≤
      (2 * 3 ^ (2 * j + 1) + 1) ^ d := by
    rw [aux_psf_cells_card]
    exact aux_prefix_actual_scale_gap_card_bound d m j i hi
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) zero_le

end SubdiffusiveProcess.Paper
