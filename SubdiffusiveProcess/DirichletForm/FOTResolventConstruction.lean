import SubdiffusiveProcess.DirichletForm.FOTConstructionData
import SubdiffusiveProcess.DirichletForm.FOTDomainHilbert
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open MeasureTheory Filter Set Topology
open scoped RealInnerProductSpace NNReal

noncomputable section

namespace DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

theorem exists_resolvent (F : _root_.DirichletForm m) (α : ℝ) (hα : 0 < α) :
    ∃ G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m, IsResolvent F.toClosedForm α G := by
  let H := EnergyHilbert.EnergySpace F.toClosedForm
  let i : H →L[ℝ] Lp ℝ 2 m := EnergyHilbert.energyInclusion F.toClosedForm
  let A : H →L[ℝ] H := (ContinuousLinearMap.adjoint i).comp i
  let T : H →L[ℝ] H := ContinuousLinearMap.id ℝ H + (α - 1) • A
  let B : H →L[ℝ] H →L[ℝ] ℝ := (innerSL ℝ).comp T
  have hB : ∀ x y : H, B x y = F.form x.1 y.1 + α * ⟪x.1, y.1⟫ := by
    intro x y
    change ⟪x + (α - 1) • (ContinuousLinearMap.adjoint i) (i x), y⟫ = _
    rw [inner_add_left, real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left]
    rw [EnergyHilbert.energy_inner]
    change F.form x.1 y.1 + ⟪x.1, y.1⟫ + (α - 1) * ⟪x.1, y.1⟫ = _
    ring
  have hc : IsCoercive B := by
    refine ⟨min 1 α, lt_min (by norm_num) hα, ?_⟩
    intro x
    rw [hB, real_inner_self_eq_norm_sq]
    have hn := EnergyHilbert.energy_norm_sq F.toClosedForm x
    have hE := F.form_nonneg x.1 x.2
    have h1 : min 1 α ≤ 1 := min_le_left _ _
    have h2 : min 1 α ≤ α := min_le_right _ _
    nlinarith [sq_nonneg ‖x.1‖]
  let S := hc.continuousLinearEquivOfBilin
  let G := i.comp (S.symm.toContinuousLinearMap.comp (ContinuousLinearMap.adjoint i))
  refine ⟨G, ?_⟩
  intro f
  let x : H := S.symm ((ContinuousLinearMap.adjoint i) f)
  refine ⟨x.2, ?_⟩
  intro v hv
  let y : H := ⟨v, hv⟩
  have heq := hc.continuousLinearEquivOfBilin_apply x y
  have hx : S x = (ContinuousLinearMap.adjoint i) f := S.apply_symm_apply _
  rw [show hc.continuousLinearEquivOfBilin x = S x from rfl, hx,
    ContinuousLinearMap.adjoint_inner_left, hB] at heq
  change ⟪f, v⟫ = F.form (G f) v + α * ⟪G f, v⟫ at heq
  linarith

theorem inner_eq_integral_mul (f v : Lp ℝ 2 m) :
    ⟪f, v⟫ = ∫ x, f x * v x ∂m := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [mul_comm]

theorem integrable_mul_Lp (f v : Lp ℝ 2 m) :
    Integrable (fun x => f x * v x) m := by
  simpa [mul_comm] using (L2.integrable_inner (𝕜 := ℝ) f v)

/-- A pointwise contraction that decreases the resolvent objective fixes its minimizer. -/
theorem resolvent_fixed_of_contraction (F : _root_.DirichletForm m)
    {α : ℝ} (hα : 0 < α) {G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m}
    (hG : IsResolvent F.toClosedForm α G) {f : Lp ℝ 2 m}
    {T : ℝ → ℝ} (hT : LipschitzWith 1 T) (hT0 : T 0 = 0)
    (hpoint : ∀ᵐ x ∂m,
      α * T ((G f) x) ^ 2 - 2 * (f x * T ((G f) x)) ≤
        α * (G f) x ^ 2 - 2 * (f x * (G f) x)) :
    G f = hT.compLp hT0 (G f) := by
  let z := G f
  let v := hT.compLp hT0 z
  have hz : z ∈ F.domain := hG.mem_domain f
  have hvrep : ⇑v =ᵐ[m] fun x => T (z x) := LipschitzWith.coeFn_compLp _ _ _
  have hv := lipschitz_comp_mem F hT hT0 hz hvrep
  have hpoint' : ∀ᵐ x ∂m,
      α * v x ^ 2 - 2 * (f x * v x) ≤ α * z x ^ 2 - 2 * (f x * z x) := by
    filter_upwards [hvrep, hpoint] with x hx h
    rwa [hx]
  have hi := integral_mono_ae
    (((Lp.memLp v).integrable_sq.const_mul α).sub ((integrable_mul_Lp f v).const_mul 2))
    (((Lp.memLp z).integrable_sq.const_mul α).sub ((integrable_mul_Lp f z).const_mul 2)) hpoint'
  have hi' : α * ‖v‖ ^ 2 - 2 * ⟪f, v⟫ ≤ α * ‖z‖ ^ 2 - 2 * ⟪f, z⟫ := by
    simp only [Pi.sub_apply] at hi
    rw [integral_sub ((Lp.memLp v).integrable_sq.const_mul α)
        ((integrable_mul_Lp f v).const_mul 2),
      integral_sub ((Lp.memLp z).integrable_sq.const_mul α)
        ((integrable_mul_Lp f z).const_mul 2)] at hi
    simpa only [integral_const_mul, ← norm_sq_eq_integral,
      ← inner_eq_integral_mul] using hi
  have heq := hG.eq f (F.domain.sub_mem hv.1 hz)
  change α * ⟪z, v - z⟫ + F.toClosedForm.form z (v - z) = ⟪f, v - z⟫ at heq
  simp only [inner_sub_right, F.toClosedForm.form_sub_right hz hv.1 hz] at heq
  rw [real_inner_self_eq_norm_sq, real_inner_comm v z] at heq
  have hs := F.toClosedForm.form_sub_self hv.1 hz
  have hsym := F.form_symm v hv.1 z hz
  have hn := norm_sub_sq_real v z
  have hvE : F.form v v ≤ F.form z z := by simpa using hv.2
  have hE := F.form_nonneg (v - z) (F.domain.sub_mem hv.1 hz)
  have hzero : ‖v - z‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖v - z‖]
  have he : v = z := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero))
  exact he.symm

theorem resolvent_positive (F : _root_.DirichletForm m) {α : ℝ} (hα : 0 < α)
    {G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} (hG : IsResolvent F.toClosedForm α G)
    {f : Lp ℝ 2 m} (hf : 0 ≤ᵐ[m] f) : 0 ≤ᵐ[m] G f := by
  let T : ℝ → ℝ := fun s => max 0 s
  have hT : LipschitzWith 1 T := LipschitzWith.id.const_max 0
  have hT0 : T 0 = 0 := by simp [T]
  have heq := resolvent_fixed_of_contraction F hα hG hT hT0 (by
    filter_upwards [hf] with x hx
    dsimp [T]
    by_cases hs : 0 ≤ (G f) x
    · rw [max_eq_right hs]
    · rw [max_eq_left (le_of_not_ge hs)]
      have hp : f x * (G f) x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx (le_of_not_ge hs)
      nlinarith [sq_nonneg ((G f) x)])
  have hrep := LipschitzWith.coeFn_compLp hT hT0 (G f)
  rw [← heq] at hrep
  filter_upwards [hrep] with x hx
  rw [hx]
  exact le_max_left _ _

theorem resolvent_submarkov (F : _root_.DirichletForm m) {α : ℝ} (hα : 0 < α)
    {G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} (hG : IsResolvent F.toClosedForm α G)
    {f : Lp ℝ 2 m} (hf0 : 0 ≤ᵐ[m] f) (hf1 : ∀ᵐ x ∂m, f x ≤ 1) :
    ∀ᵐ x ∂m, 0 ≤ α * (G f) x ∧ α * (G f) x ≤ 1 := by
  have hc : 0 < α⁻¹ := inv_pos.mpr hα
  have heq := resolvent_fixed_of_contraction F hα hG (lipschitzWith_ramp α⁻¹)
    (ramp_zero α⁻¹) (by
      filter_upwards [hf0, hf1] with x h0 h1
      by_cases hs0 : (G f) x ≤ 0
      · rw [ramp_of_nonpos hs0]
        have hp := mul_nonpos_of_nonneg_of_nonpos h0 hs0
        nlinarith [sq_nonneg ((G f) x)]
      · by_cases hs1 : (G f) x ≤ α⁻¹
        · rw [ramp_of_le (le_of_not_ge hs0) hs1]
        · rw [ramp_of_ge hc.le (le_of_not_ge hs1)]
          have ha : α * α⁻¹ = 1 := mul_inv_cancel₀ hα.ne'
          have hs : 0 ≤ (G f) x - α⁻¹ := by linarith
          nlinarith [mul_nonneg hs (sub_nonneg.mpr h1),
            mul_nonneg hα.le (sq_nonneg ((G f) x - α⁻¹))])
  have hrep := LipschitzWith.coeFn_compLp (lipschitzWith_ramp α⁻¹) (ramp_zero α⁻¹) (G f)
  rw [← heq] at hrep
  filter_upwards [hrep] with x hx
  rw [hx]
  constructor
  · exact mul_nonneg hα.le (ramp_nonneg _ _)
  · have h := mul_le_mul_of_nonneg_left (ramp_le (s := (G f) x) hc.le) hα.le
    simpa only [mul_inv_cancel₀ hα.ne'] using h

theorem coeFn_quadratic_combination (a b c : Lp ℝ 2 m) (r s : ℝ) :
    ⇑(a - r • b + s • c) =ᵐ[m] fun x => a x - r * b x + s * c x := by
  filter_upwards [Lp.coeFn_add (a - r • b) (s • c), Lp.coeFn_sub a (r • b),
    Lp.coeFn_smul r b, Lp.coeFn_smul s c] with x h1 h2 h3 h4
  simp only [h1, Pi.add_apply, h2, Pi.sub_apply, h3, h4, Pi.smul_apply, smul_eq_mul]

theorem resolvent_mixed_square_le (F : _root_.DirichletForm m) {α : ℝ} (hα : 0 < α)
    {G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} (hG : IsResolvent F.toClosedForm α G)
    {u u2 ξ w : Lp ℝ 2 m}
    (hu2 : ⇑u2 =ᵐ[m] fun x => u x ^ 2)
    (hξ01 : ∀ᵐ x ∂m, 0 ≤ ξ x ∧ ξ x ≤ 1)
    (hw : ⇑w =ᵐ[m] fun x => u x * ξ x) :
    ∀ᵐ x ∂m, (α * (G w) x) ^ 2 ≤ α * (G u2) x := by
  let ξ2 : Lp ℝ 2 m := (lipschitzWith_sqClamp 1).compLp (sqClamp_zero (by norm_num)) ξ
  have hξ2 : ⇑ξ2 =ᵐ[m] fun x => ξ x ^ 2 := by
    filter_upwards [LipschitzWith.coeFn_compLp (lipschitzWith_sqClamp 1)
      (sqClamp_zero (by norm_num)) ξ, hξ01] with x hx h
    simp only [Function.comp_apply, NNReal.coe_one] at hx
    rw [hx, sqClamp_of_abs_le]
    simpa [abs_of_nonneg h.1] using h.2
  have hξ20 : 0 ≤ᵐ[m] ξ2 := by
    filter_upwards [hξ2] with x hx
    rw [hx]
    positivity
  have hξ21 : ∀ᵐ x ∂m, ξ2 x ≤ 1 := by
    filter_upwards [hξ2, hξ01] with x hx h
    rw [hx]
    nlinarith
  have hbound := resolvent_submarkov F hα hG hξ20 hξ21
  have hq : ∀ c : ℚ, ∀ᵐ x ∂m,
      0 ≤ α * (G u2) x - 2 * (c : ℝ) * (α * (G w) x) +
        (c : ℝ) ^ 2 * (α * (G ξ2) x) := by
    intro c
    let q := u2 - (2 * (c : ℝ)) • w + (c : ℝ) ^ 2 • ξ2
    have hpos : 0 ≤ᵐ[m] q := by
      filter_upwards [coeFn_quadratic_combination u2 w ξ2 (2 * (c : ℝ)) ((c : ℝ) ^ 2),
        hu2, hξ2, hw] with x h1 h2 h3 h4
      change 0 ≤ (u2 - (2 * (c : ℝ)) • w + (c : ℝ) ^ 2 • ξ2) x
      rw [h1, h2, h3]
      have he := congrArg (fun t : ℝ => (2 * (c : ℝ)) * t) h4
      nlinarith [sq_nonneg (u x - (c : ℝ) * ξ x)]
    have hg : G q = G u2 - (2 * (c : ℝ)) • G w + (c : ℝ) ^ 2 • G ξ2 := by
      simp [q]
    have hgp := resolvent_positive F hα hG hpos
    rw [hg] at hgp
    filter_upwards [hgp, coeFn_quadratic_combination (G u2) (G w) (G ξ2)
      (2 * (c : ℝ)) ((c : ℝ) ^ 2)] with x h1 h2
    rw [h2] at h1
    nlinarith [mul_nonneg hα.le h1]
  filter_upwards [ae_all_iff.mpr hq, hbound] with x hx hbd
  let P : ℝ → ℝ := fun c => α * (G u2) x - 2 * c * (α * (G w) x) +
    c ^ 2 * (α * (G ξ2) x)
  have hc : IsClosed {c : ℝ | 0 ≤ P c} := isClosed_le continuous_const (by fun_prop)
  have hall : ∀ c : ℝ, 0 ≤ P c := by
    have hs : range (fun c : ℚ => (c : ℝ)) ⊆ {c : ℝ | 0 ≤ P c} := by
      rintro _ ⟨c, rfl⟩
      exact hx c
    have hs' := hc.closure_subset_iff.mpr hs
    rw [Rat.denseRange_cast.closure_range] at hs'
    exact fun c => hs' (mem_univ c)
  have h := hall (α * (G w) x)
  dsimp [P] at h
  nlinarith [mul_nonneg (sq_nonneg (α * (G w) x)) (sub_nonneg.mpr hbd.2)]

theorem resolvent_square_le (F : _root_.DirichletForm m) {α : ℝ} (hα : 0 < α)
    {G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} (hG : IsResolvent F.toClosedForm α G)
    {u u2 ξ : Lp ℝ 2 m}
    (hu2 : ⇑u2 =ᵐ[m] fun x => u x ^ 2)
    (hξ01 : ∀ᵐ x ∂m, 0 ≤ ξ x ∧ ξ x ≤ 1)
    (hξu : ∀ᵐ x ∂m, u x * ξ x = u x) :
    ∀ᵐ x ∂m, (α * (G u) x) ^ 2 ≤ α * (G u2) x := by
  apply resolvent_mixed_square_le F hα hG hu2 hξ01
  filter_upwards [hξu] with x hx
  exact hx.symm

theorem weak_form_tendsto (E : ClosedForm m) {u : ℕ → Lp ℝ 2 m} {z a : Lp ℝ 2 m}
    (hu : ∀ n, u n ∈ E.domain) (hz : z ∈ E.domain) (ha : a ∈ E.domain)
    (hlim : Tendsto u atTop (𝓝 z)) {B : ℝ} (hB : ∀ n, E.form (u n) (u n) ≤ B) :
    Tendsto (fun n => E.form (u n) a) atTop (𝓝 (E.form z a)) := by
  have hw : ∀ n, u n - z ∈ E.domain := fun n => E.domain.sub_mem (hu n) hz
  have hbound : ∀ n, E.form (u n - z) (u n - z) ≤ 2 * B + 2 * E.form z z :=
    fun n => (E.form_sub_self_le (hu n) hz).trans (by linarith [hB n])
  have hnorm := tendsto_iff_norm_sub_tendsto_zero.mp hlim
  have h := EnergyHilbert.weak_null_form_tendsto_zero E
    (fun n => u n - z) hw _ hbound hnorm a ha
  have hzero : Tendsto (fun n => E.form (u n) a - E.form z a) atTop (𝓝 0) := by
    apply h.congr
    intro n
    rw [E.form_sub_right ha (hu n) hz, E.form_symm _ ha _ (hu n), E.form_symm _ ha _ hz]
  simpa only [sub_add_cancel, zero_add] using hzero.add_const (E.form z a)

theorem energy_tendsto_of_limsup_le (E : ClosedForm m)
    {u : ℕ → Lp ℝ 2 m} {z : Lp ℝ 2 m} (hu : ∀ n, u n ∈ E.domain)
    (hz : z ∈ E.domain) (hlim : Tendsto u atTop (𝓝 z))
    (hE : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, E.form (u n) (u n) ≤ E.form z z + ε) :
    Tendsto (fun n => E.energyNormSq (u n - z)) atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hE 1 (by norm_num))
  let S : ℝ := ∑ k ∈ Finset.range N, E.form (u k) (u k)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun k _ => E.form_nonneg _ (hu k))
  have hB : ∀ n, E.form (u n) (u n) ≤ E.form z z + 1 + S := by
    intro n
    by_cases hn : N ≤ n
    · linarith [hN n hn]
    · have hs : E.form (u n) (u n) ≤ S :=
        Finset.single_le_sum (fun k _ => E.form_nonneg _ (hu k)) (Finset.mem_range.mpr (by omega))
      linarith [E.form_nonneg z hz]
  have hcross := weak_form_tendsto E hu hz hz hlim hB
  have hnorm : Tendsto (fun n => ‖u n - z‖ ^ 2) atTop (𝓝 0) := by
    simpa using (tendsto_iff_norm_sub_tendsto_zero.mp hlim).pow 2
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [] with n
    exact ha.trans_le (E.energyNormSq_nonneg (E.domain.sub_mem (hu n) hz))
  · intro b hb
    have hc : ∀ᶠ n in atTop, E.form z z - b / 4 < E.form (u n) z :=
      hcross.eventually (lt_mem_nhds (by linarith))
    have hn : ∀ᶠ n in atTop, ‖u n - z‖ ^ 2 < b / 4 :=
      hnorm.eventually (gt_mem_nhds (by linarith))
    filter_upwards [hE (b / 4) (by linarith), hc, hn] with n h1 h2 h3
    rw [ClosedForm.energyNormSq, E.form_sub_self (hu n) hz]
    linarith

theorem scaled_resolvent_energy_bound (F : _root_.DirichletForm m)
    {α : ℝ} (hα : 0 < α) {G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m}
    (hG : IsResolvent F.toClosedForm α G) {f : Lp ℝ 2 m} (hf : f ∈ F.domain) :
    F.form (α • G f) (α • G f) + α * ‖α • G f - f‖ ^ 2 ≤ F.form f f := by
  let r := α • G f
  have hg := hG.mem_domain f
  have hr : r ∈ F.domain := F.domain.smul_mem α hg
  have heq : α * ⟪r - f, r - f⟫ + F.form r (r - f) = 0 := by
    have h := hG.eq f (F.domain.sub_mem hr hf)
    change α * ⟪α • G f - f, r - f⟫ + F.form (α • G f) (r - f) = 0
    rw [inner_sub_left, real_inner_smul_left,
      F.toClosedForm.form_smul_left α (G f) hg (r - f) (F.domain.sub_mem hr hf)]
    nlinarith
  rw [real_inner_self_eq_norm_sq, F.toClosedForm.form_sub_right hr hr hf] at heq
  have hp := F.form_nonneg (r - f) (F.domain.sub_mem hr hf)
  rw [F.toClosedForm.form_sub_self hr hf] at hp
  have hn := mul_nonneg hα.le (sq_nonneg ‖r - f‖)
  change F.form r r + α * ‖r - f‖ ^ 2 ≤ F.form f f
  linarith

theorem tendsto_resolvent_form (F : _root_.DirichletForm m)
    {G : ℕ → Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m}
    (hG : ∀ n : ℕ, IsResolvent F.toClosedForm (n + 1) (G n))
    {u v : Lp ℝ 2 m} (hu : u ∈ F.domain) (hv : v ∈ F.domain) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) *
      ⟪u - ((n : ℝ) + 1) • G n u, v⟫) atTop (𝓝 (F.form u v)) := by
  let r : ℕ → Lp ℝ 2 m := fun n => ((n : ℝ) + 1) • G n u
  have ha : ∀ n : ℕ, 0 < (n : ℝ) + 1 := fun n => by positivity
  have hr : ∀ n, r n ∈ F.domain := fun n => F.domain.smul_mem _ ((hG n).mem_domain u)
  have hb := fun n => scaled_resolvent_energy_bound F (ha n) (hG n) hu
  have hE : ∀ n, F.form (r n) (r n) ≤ F.form u u := by
    intro n
    have hn := mul_nonneg (ha n).le (sq_nonneg ‖r n - u‖)
    linarith [hb n]
  have hnormsq : ∀ n, ‖r n - u‖ ^ 2 ≤ F.form u u / ((n : ℝ) + 1) := by
    intro n
    apply (le_div_iff₀ (ha n)).mpr
    have hp := F.form_nonneg (r n) (hr n)
    nlinarith [hb n]
  have hs : Tendsto (fun n => ‖r n - u‖ ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sq_nonneg _) hnormsq
    simpa only [div_eq_mul_inv, one_div, one_mul, mul_zero] using
      (tendsto_const_nhds (x := F.form u u)).mul tendsto_one_div_add_atTop_nhds_zero_nat
  have hn : Tendsto (fun n => ‖r n - u‖) atTop (𝓝 0) := by
    have ht : Tendsto (fun n => Real.sqrt (‖r n - u‖ ^ 2)) atTop (𝓝 0) := by
      simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hs
    apply ht.congr
    intro n
    exact Real.sqrt_sq (norm_nonneg _)
  have hlim := tendsto_iff_norm_sub_tendsto_zero.mpr hn
  have he := energy_tendsto_of_limsup_le F.toClosedForm hr hu hlim
    (fun ε hε => Eventually.of_forall (fun n => (hE n).trans (by linarith)))
  have hform := F.toClosedForm.tendsto_form_of_tendsto_energyNormSq hr hu hv he
  apply hform.congr
  intro n
  symm
  have hg := (hG n).mem_domain u
  have h := (hG n).eq u hv
  change ((n : ℝ) + 1) * ⟪u - ((n : ℝ) + 1) • G n u, v⟫ = F.form (r n) v
  rw [inner_sub_left, real_inner_smul_left]
  change _ = F.form (((n : ℝ) + 1) • G n u) v
  rw [F.toClosedForm.form_smul_left _ (G n u) hg v hv]
  nlinarith


/-- Jensen's square inequality without a finite-mass state space. -/
theorem resolvent_square_le_general (F : _root_.DirichletForm m) {α : ℝ} (hα : 0 < α)
    {G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} (hG : IsResolvent F.toClosedForm α G)
    {u u2 : Lp ℝ 2 m} (hu2 : ⇑u2 =ᵐ[m] fun x => u x ^ 2) :
    ∀ᵐ x ∂m, (α * (G u) x) ^ 2 ≤ α * (G u2) x := by
  let T : ℕ → ℝ → ℝ := fun n s => ramp 1 (((n : ℝ) + 1) * |s|)
  have hT : ∀ n : ℕ, LipschitzWith ((n : ℝ≥0) + 1) (T n) := by
    intro n
    apply LipschitzWith.of_dist_le_mul
    intro a b
    have h := (lipschitzWith_ramp 1).dist_le_mul (((n : ℝ) + 1) * |a|)
      (((n : ℝ) + 1) * |b|)
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at h
    change |T n a - T n b| ≤ ((n : ℝ) + 1) * |a - b|
    calc
      _ ≤ |(((n : ℝ) + 1) * |a| - ((n : ℝ) + 1) * |b|)| := h
      _ = ((n : ℝ) + 1) * abs (|a| - |b|) := by
        rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)]
      _ ≤ _ := mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub a b) (by positivity)
  have hT0 : ∀ n, T n 0 = 0 := fun n => by simp [T]
  let ξ : ℕ → Lp ℝ 2 m := fun n => (hT n).compLp (hT0 n) u
  have hξ : ∀ n, ⇑(ξ n) =ᵐ[m] fun x => T n (u x) :=
    fun n => LipschitzWith.coeFn_compLp _ _ _
  have h01 : ∀ n s, 0 ≤ T n s ∧ T n s ≤ 1 :=
    fun n s => ⟨ramp_nonneg _ _, ramp_le (by norm_num)⟩
  have hwLp : ∀ n, MemLp (fun x => u x * T n (u x)) 2 m := by
    intro n
    apply (Lp.memLp u).mono
    · exact (Lp.aestronglyMeasurable u).mul ((hT n).continuous.comp_aestronglyMeasurable
        (Lp.aestronglyMeasurable u))
    · filter_upwards [] with x
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (h01 n (u x)).1]
      exact mul_le_of_le_one_right (abs_nonneg _) (h01 n (u x)).2
  let w : ℕ → Lp ℝ 2 m := fun n => (hwLp n).toLp _
  have hw : ∀ n, ⇑(w n) =ᵐ[m] fun x => u x * T n (u x) :=
    fun n => MemLp.coeFn_toLp _
  have hlim : Tendsto w atTop (𝓝 u) := by
    refine tendsto_Lp_of_tendsto_comp (u := u) (Gs := fun n s => s * T n s)
      (G := id) hw (EventuallyEq.rfl) ?_ (K := 2) ?_
    · intro s
      by_cases hs : s = 0
      · simp [hs]
      · have habs : 0 < |s| := abs_pos.mpr hs
        obtain ⟨N, hN⟩ := exists_nat_gt (1 / |s|)
        have hn : ∀ᶠ n : ℕ in atTop, s * T n s = s := by
          filter_upwards [eventually_ge_atTop N] with n hn
          have hle : 1 ≤ ((n : ℝ) + 1) * |s| := by
            have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
            have hbase := (div_lt_iff₀ habs).mp hN
            nlinarith
          simp [T, ramp_of_ge (by norm_num : (0 : ℝ) ≤ 1) hle]
        exact tendsto_const_nhds.congr' (hn.mono fun n hn => hn.symm)
    · intro n s
      change |s * T n s - s| ≤ 2 * |s|
      have h := h01 n s
      rw [show s * T n s - s = s * (T n s - 1) by ring, abs_mul,
        abs_of_nonpos (by linarith : T n s - 1 ≤ 0)]
      nlinarith [abs_nonneg s]
  have hineq : ∀ n, ∀ᵐ x ∂m, (α * (G (w n)) x) ^ 2 ≤ α * (G u2) x := by
    intro n
    apply resolvent_mixed_square_le F hα hG hu2 (ξ := ξ n)
    · filter_upwards [hξ n] with x hx
      rw [hx]
      exact h01 n (u x)
    · filter_upwards [hw n, hξ n] with x h1 h2
      rw [h1, h2]
  obtain ⟨seq, _, hseq⟩ := (tendstoInMeasure_of_tendsto_Lp
    ((G.continuous.tendsto u).comp hlim)).exists_seq_tendsto_ae
  filter_upwards [hseq, ae_all_iff.mpr hineq] with x hx hi
  exact le_of_tendsto ((hx.const_mul α).pow 2) (Eventually.of_forall fun n => hi (seq n))

theorem tendsto_mul_ramp_nat {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun n : ℕ => s * ramp 1 (((n : ℝ) + 1) * s)) atTop (𝓝 s) := by
  by_cases hzero : s = 0
  · simp [hzero]
  · have hpos : 0 < s := lt_of_le_of_ne hs (Ne.symm hzero)
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / s)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hbase := (div_lt_iff₀ hpos).mp hN
    have hle : 1 ≤ ((n : ℝ) + 1) * s := by nlinarith
    simp [ramp_of_ge (by norm_num : (0 : ℝ) ≤ 1) hle]

/-- A symmetric sub-Markov resolvent contracts nonnegative integrable inputs in L1. -/
theorem resolvent_integrable (F : _root_.DirichletForm m) {α : ℝ} (hα : 0 < α)
    {G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} (hG : IsResolvent F.toClosedForm α G)
    {f : Lp ℝ 2 m} (hf0 : 0 ≤ᵐ[m] f) (hf : Integrable (⇑f) m) :
    Integrable (⇑(α • G f)) m ∧ ∫ x, (α • G f) x ∂m ≤ ∫ x, f x ∂m := by
  let z := α • G f
  have hz0 : 0 ≤ᵐ[m] z := by
    filter_upwards [Lp.coeFn_smul α (G f), resolvent_positive F hα hG hf0] with x hx h0
    change 0 ≤ (α • G f) x
    simpa only [hx, Pi.smul_apply, smul_eq_mul] using mul_nonneg hα.le h0
  let ξ : ℕ → Lp ℝ 2 m := fun n => rampLp 1 (((n : ℝ) + 1) • z)
  have hξ : ∀ n, ⇑(ξ n) =ᵐ[m] fun x => ramp 1 (((n : ℝ) + 1) * z x) := by
    intro n
    filter_upwards [coeFn_rampLp 1 (((n : ℝ) + 1) • z),
      Lp.coeFn_smul ((n : ℝ) + 1) z] with x h1 h2
    change (rampLp 1 (((n : ℝ) + 1) • z)) x = _
    simp only [h1, h2, Pi.smul_apply, smul_eq_mul]
  have h01 : ∀ n, ∀ᵐ x ∂m, 0 ≤ (ξ n) x ∧ (ξ n) x ≤ 1 := by
    intro n
    filter_upwards [hξ n] with x hx
    rw [hx]
    exact ⟨ramp_nonneg _ _, ramp_le (by norm_num)⟩
  have hb : ∀ n, ∫ x, z x * (ξ n) x ∂m ≤ ∫ x, f x ∂m := by
    intro n
    have hm := resolvent_submarkov F hα hG ((h01 n).mono fun x h => h.1)
      ((h01 n).mono fun x h => h.2)
    have htest : ⟪z, ξ n⟫ = ⟪f, α • G (ξ n)⟫ := by
      change ⟪α • G f, ξ n⟫ = _
      rw [real_inner_smul_left, real_inner_smul_right]
      have hc := hG.inner_comm f (ξ n)
      have hi : ⟪G f, ξ n⟫ = ⟪ξ n, G f⟫ := real_inner_comm _ _
      rw [hi, ← hc]
    rw [← inner_eq_integral_mul, htest, inner_eq_integral_mul]
    apply integral_mono_ae (integrable_mul_Lp f (α • G (ξ n))) hf
    filter_upwards [hf0, hm, Lp.coeFn_smul α (G (ξ n))] with x h0 h1 h2
    simp only [h2, Pi.smul_apply, smul_eq_mul]
    exact mul_le_of_le_one_right h0 h1.2
  have hprod0 : ∀ n, 0 ≤ᵐ[m] fun x => z x * (ξ n) x := by
    intro n
    filter_upwards [hz0, h01 n] with x h0 h1
    exact mul_nonneg h0 h1.1
  have hlim : ∀ᵐ x ∂m,
      Tendsto (fun n : ℕ => ENNReal.ofReal (z x * (ξ n) x)) atTop (𝓝 (ENNReal.ofReal (z x))) := by
    filter_upwards [hz0, ae_all_iff.mpr hξ] with x h0 hx
    have ht := tendsto_mul_ramp_nat h0
    apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    apply ht.congr
    intro n
    rw [hx n]
  have hbound : ∫⁻ x, ENNReal.ofReal (z x) ∂m ≤ ENNReal.ofReal (∫ x, f x ∂m) := by
    calc
      _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal (z x * (ξ n) x)) atTop ∂m :=
        lintegral_congr_ae (hlim.mono fun x hx => hx.liminf_eq.symm)
      _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (z x * (ξ n) x) ∂m) atTop :=
        lintegral_liminf_le' (fun n => (integrable_mul_Lp z (ξ n)).aemeasurable.ennreal_ofReal)
      _ ≤ _ := liminf_le_of_frequently_le' (Frequently.of_forall fun n => by
        rw [← ofReal_integral_eq_lintegral_ofReal (integrable_mul_Lp z (ξ n)) (hprod0 n)]
        exact ENNReal.ofReal_le_ofReal (hb n))
  have hz : Integrable (⇑z) m := ⟨Lp.aestronglyMeasurable z,
    (hasFiniteIntegral_iff_ofReal hz0).mpr (hbound.trans_lt (by finiteness))⟩
  refine ⟨hz, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hz hz0] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg_of_ae hf0)).mp hbound

end DirichletForm.FOTConstruction
