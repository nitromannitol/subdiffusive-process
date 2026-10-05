module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.relative_response_variation
public import SubdiffusiveProcess.Paper.thm_C0

@[expose] public section

/-! Normalization steps. The random growth constant is
constructed from unnormalized growth and reciprocal response moments. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper
noncomputable section

/-- Coordinate primal-dual coercivity bounds the reciprocal normalized trace.
The factor `d⁻¹` is retained before taking any moments. -/
theorem aux_prop_conc_reciprocal_trace_le {d : ℕ} (hd : 0 < d)
    (A : Matrix (Fin d) (Fin d) ℝ) (K : ℝ)
    (hdiag : ∀ i, 0 ≤ A i i) (hcoercive : ∀ i, 1 ≤ K * A i i) :
    0 < Matrix.trace A ∧ (Matrix.trace A)⁻¹ ≤ K / d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsum : (d : ℝ) ≤ K * Matrix.trace A := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, Finset.mul_sum, Matrix.trace, Matrix.diag] using!
      Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcoercive i)
  have htr0 : 0 ≤ Matrix.trace A := Finset.sum_nonneg (fun i _ => hdiag i)
  have htr : 0 < Matrix.trace A := by
    by_contra h
    have hz : Matrix.trace A = 0 := le_antisymm (le_of_not_gt h) htr0
    rw [hz, mul_zero] at hsum
    exact (not_le_of_gt hdR) hsum
  refine ⟨htr, ?_⟩
  apply (le_div_iff₀ hdR).mpr
  apply (inv_mul_le_iff₀ htr).mpr
  simpa only [mul_comm] using hsum

/-- Once positivity is known, all fixed inverse moments pass to a response
limit. This strengthens the earlier nondegeneracy step without redoing it. -/
theorem aux_prop_conc_limit_reciprocal_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (R : ℕ → Ω → ℝ) (T : Ω → ℝ) (p C : ℝ≥0∞)
    (hR : ∀ n, AEStronglyMeasurable (R n) P)
    (hT : ∀ᵐ ω ∂P, 0 < T ω)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => R n ω) atTop (𝓝 (T ω)))
    (hbound : ∀ n, eLpNorm (fun ω => (R n ω)⁻¹) p P ≤ C) :
    eLpNorm (fun ω => (T ω)⁻¹) p P ≤ C := by
  have hRinv : ∀ n, AEStronglyMeasurable (fun ω => (R n ω)⁻¹) P :=
    fun n => (hR n).aemeasurable.inv.aestronglyMeasurable
  have hlimInv : ∀ᵐ ω ∂P, Tendsto (fun n => (R n ω)⁻¹) atTop (𝓝 ((T ω)⁻¹)) := by
    filter_upwards [hT, hlim] with ω hpos hconv
    exact hconv.inv₀ hpos.ne'
  exact Lp.eLpNorm_le_of_ae_tendsto (u := atTop)
    (f := fun n ω => (R n ω)⁻¹) (Filter.Eventually.of_forall hbound)
    hRinv (aestronglyMeasurable_of_tendsto_ae atTop hRinv hlimInv) hlimInv

/-- Apply primal-dual coercivity to each finite matrix, then pass its fixed
moment bound to the limiting reciprocal trace. The moment constant retains
the dimension factor and is unchanged by subsequence extraction. -/
theorem aux_prop_conc_reciprocal_trace_moment_of_limits
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {d : ℕ} (hd : 0 < d) (AN : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ)
    (A : Ω → Matrix (Fin d) (Fin d) ℝ) (KN : ℕ → Ω → ℝ)
    (p C : ℝ≥0∞)
    (htrace : ∀ n, AEStronglyMeasurable (fun ω => Matrix.trace (AN n ω)) P)
    (hKpos : ∀ n, ∀ᵐ ω ∂P, 0 ≤ KN n ω)
    (hdiag : ∀ n, ∀ᵐ ω ∂P, ∀ i, 0 ≤ AN n ω i i)
    (hcoercive : ∀ n, ∀ᵐ ω ∂P, ∀ i, 1 ≤ KN n ω * AN n ω i i)
    (hpositive : ∀ᵐ ω ∂P, 0 < Matrix.trace (A ω))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => Matrix.trace (AN n ω))
      atTop (𝓝 (Matrix.trace (A ω))))
    (hmoment : ∀ n, eLpNorm (KN n) p P ≤ C) :
    eLpNorm (fun ω => (Matrix.trace (A ω))⁻¹) p P ≤
      ENNReal.ofReal ((d : ℝ)⁻¹) * C := by
  apply aux_prop_conc_limit_reciprocal_moment P
    (fun n ω => Matrix.trace (AN n ω)) (fun ω => Matrix.trace (A ω))
    p _ htrace hpositive hlim
  intro n
  have hpoint : ∀ᵐ ω ∂P,
      ‖(Matrix.trace (AN n ω))⁻¹‖ ≤ (d : ℝ)⁻¹ * KN n ω := by
    filter_upwards [hKpos n, hdiag n, hcoercive n] with ω hK hD hco
    have hb := aux_prop_conc_reciprocal_trace_le hd (AN n ω) (KN n ω) hD hco
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hb.1)]
    simpa only [div_eq_mul_inv, mul_comm] using hb.2
  have hh := eLpNorm_mono_ae_real (p := p) (htrace n).aemeasurable.inv.aestronglyMeasurable hpoint
  change eLpNorm (fun ω => (Matrix.trace (AN n ω))⁻¹) p P ≤ _
  refine hh.trans ?_
  change eLpNorm ((d : ℝ)⁻¹ • KN n) p P ≤ _
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity)]
  exact mul_le_mul_right (hmoment n) _

/-- The scalar calculation behind the deterministic reference-ratio bound.
Here `yE,yF` are the inverse responses with their reference factors removed. -/
theorem aux_prop_conc_reference_ratio_bounds
    (r m M A yE yF : ℝ) (hr : 0 < r) (hm : 0 ≤ m) (hM : 0 ≤ M)
    (hA : 0 < A) (hyE : A⁻¹ ≤ yE ∧ yE ≤ A)
    (hyF : A⁻¹ ≤ yF ∧ yF ≤ A)
    (horder : m * yF ≤ r * yE ∧ r * yE ≤ M * yF) :
    m / A ^ 2 ≤ r ∧ r ≤ M * A ^ 2 := by
  have hlow : m / A ≤ r * A := by
    calc
      m / A = m * A⁻¹ := div_eq_mul_inv _ _
      _ ≤ m * yF := mul_le_mul_of_nonneg_left hyF.1 hm
      _ ≤ r * yE := horder.1
      _ ≤ r * A := mul_le_mul_of_nonneg_left hyE.2 hr.le
  have hupp : r / A ≤ M * A := by
    calc
      r / A = r * A⁻¹ := div_eq_mul_inv _ _
      _ ≤ r * yE := mul_le_mul_of_nonneg_left hyE.1 hr.le
      _ ≤ M * yF := horder.2
      _ ≤ M * A := mul_le_mul_of_nonneg_left hyF.2 hM
  constructor
  · apply (div_le_iff₀ (sq_pos_of_pos hA)).mpr
    have h := (div_le_iff₀ hA).mp hlow
    nlinarith only [h]
  · have h := (div_le_iff₀ hA).mp hupp
    nlinarith only [h]

/-- A positive-probability joint response event bounds a deterministic
reference ratio everywhere. No intersection over infinitely many cells is
needed for this deterministic conclusion. -/
theorem aux_prop_conc_reference_ratio_of_event
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (yE yF : Ω → ℝ) (r m M A : ℝ) (hr : 0 < r)
    (hm : 0 ≤ m) (hM : 0 ≤ M) (hA : 0 < A)
    (hgood : P {ω | (A⁻¹ ≤ yE ω ∧ yE ω ≤ A) ∧
      (A⁻¹ ≤ yF ω ∧ yF ω ≤ A)} ≠ 0)
    (horder : ∀ᵐ ω ∂P, m * yF ω ≤ r * yE ω ∧ r * yE ω ≤ M * yF ω) :
    m / A ^ 2 ≤ r ∧ r ≤ M * A ^ 2 := by
  obtain ⟨ω, hω, ho⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hgood
    (ae_restrict_of_ae horder)
  exact aux_prop_conc_reference_ratio_bounds r m M A (yE ω) (yF ω)
    hr hm hM hA hω.1 hω.2 ho

/-- Four first-moment bounds give the joint positive-probability event used in the normalized growth argument. Independence between the two candidate responses is unnecessary. -/
theorem aux_prop_conc_joint_reference_event
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (yE yF : Ω → ℝ) (C A : ℝ) (hA : 0 < A) (hCA : 8 * C ≤ A)
    (hEpos : ∀ᵐ ω ∂P, 0 < yE ω) (hFpos : ∀ᵐ ω ∂P, 0 < yF ω)
    (hE : MemLp yE 1 P) (hF : MemLp yF 1 P)
    (hEi : MemLp (fun ω => (yE ω)⁻¹) 1 P)
    (hFi : MemLp (fun ω => (yF ω)⁻¹) 1 P)
    (hEn : eLpNorm yE 1 P ≤ ENNReal.ofReal C)
    (hFn : eLpNorm yF 1 P ≤ ENNReal.ofReal C)
    (hEin : eLpNorm (fun ω => (yE ω)⁻¹) 1 P ≤ ENNReal.ofReal C)
    (hFin : eLpNorm (fun ω => (yF ω)⁻¹) 1 P ≤ ENNReal.ofReal C) :
    P {ω | (A⁻¹ ≤ yE ω ∧ yE ω ≤ A) ∧ (A⁻¹ ≤ yF ω ∧ yF ω ≤ A)} ≠ 0 := by
  have hlo (y : Ω → ℝ) (hy : ∀ᵐ ω ∂P, 0 < y ω)
      (hyi : MemLp (fun ω => (y ω)⁻¹) 1 P)
      (hyn : eLpNorm (fun ω => (y ω)⁻¹) 1 P ≤ ENNReal.ofReal C) :
      P {ω | y ω < A⁻¹} ≤ 1 / 8 := by
    apply le_trans (measure_mono_ae ?_)
      (aux_thm_C0_markov_eighth P (fun ω => (y ω)⁻¹) C A hA hCA hyi hyn)
    filter_upwards [hy] with ω hω hlt
    simpa only [inv_inv] using
      (inv_lt_inv₀ (inv_pos.mpr hA) hω).mpr hlt
  simpa only [and_assoc] using aux_thm_C0_pos_of_tails P yE yF A
    (hlo yE hEpos hEi hEin) (aux_thm_C0_markov_eighth P yE C A hA hCA hE hEn)
    (hlo yF hFpos hFi hFin) (aux_thm_C0_markov_eighth P yF C A hA hCA hF hFn)

/-- The inverse-form order has the required normalized form when the
reference factors are restored. -/
theorem aux_prop_conc_normalized_inverse_order
    (sE sF YE YF m M : ℝ) (hsE : 0 < sE) (hsF : 0 ≤ sF)
    (horder : m * YF ≤ YE ∧ YE ≤ M * YF) :
    m * (sF * YF) ≤ (sF / sE) * (sE * YE) ∧
      (sF / sE) * (sE * YE) ≤ M * (sF * YF) := by
  have he : (sF / sE) * (sE * YE) = sF * YE := by field_simp
  rw [he]
  constructor
  · nlinarith only [mul_le_mul_of_nonneg_left horder.1 hsF]
  · nlinarith only [mul_le_mul_of_nonneg_left horder.2 hsF]

/-- Endpoint bounds replace the random-cell reference coefficient by a
constant depending only on `C0` and the fixed moment-bank cutoff `A`. -/
theorem aux_prop_conc_reference_coefficient_uniform
    (C0 m M r A : ℝ) (hC0 : 1 ≤ C0) (hm : C0⁻¹ ≤ m)
    (hM : M ≤ C0) (hr : r ≤ M * A ^ 2) :
    m⁻¹ * r ≤ C0 ^ 2 * A ^ 2 := by
  have hCpos : 0 < C0 := zero_lt_one.trans_le hC0
  have hmpos : 0 < m := (inv_pos.mpr hCpos).trans_le hm
  have hi : m⁻¹ ≤ C0 := by
    simpa only [inv_inv] using (inv_le_inv₀ hmpos (inv_pos.mpr hCpos)).mpr hm
  calc
    m⁻¹ * r ≤ m⁻¹ * (M * A ^ 2) := mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr hmpos.le)
    _ ≤ m⁻¹ * (C0 * A ^ 2) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hM (sq_nonneg A)) (inv_nonneg.mpr hmpos.le)
    _ ≤ C0 * (C0 * A ^ 2) := mul_le_mul_of_nonneg_right hi (by positivity)
    _ = C0 ^ 2 * A ^ 2 := by ring

/-- Dividing two unnormalized energy-growth bounds by the trace preserves
the growth power. The reference ratio is removed by its deterministic bound. -/
theorem aux_prop_conc_normalized_growth_bound
    (nu D sE sF gE gF m R a : ℝ)
    (hD : 0 < D) (hsE : 0 < sE) (hm : 0 < m)
    (hgF : 0 ≤ gF) (ha : 0 ≤ a) (hratio : sF / sE ≤ R)
    (hnu : nu ≤ (sE * gE * a + m⁻¹ * (sF * gF * a)) / D) :
    nu ≤ ((gE + m⁻¹ * R * gF) * (D / sE)⁻¹) * a := by
  have href : sF ≤ R * sE := (div_le_iff₀ hsE).mp hratio
  have hb : m⁻¹ * (sF * gF * a) ≤ m⁻¹ * (R * sE * gF * a) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right href hgF) ha)
      (inv_nonneg.mpr hm.le)
  calc
    nu ≤ (sE * gE * a + m⁻¹ * (sF * gF * a)) / D := hnu
    _ ≤ (sE * gE * a + m⁻¹ * (R * sE * gF * a)) / D :=
      div_le_div_of_nonneg_right (add_le_add_right hb _) hD.le
    _ = ((gE + m⁻¹ * R * gF) * (D / sE)⁻¹) * a := by
      field_simp

/-- Hölder's inequality at the preselected doubled moment order constructs
the normalized random growth majorant and its uniform `Lᵖ` bound. -/
theorem aux_prop_conc_normalized_growth_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (gE gF invTrace : Ω → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (p : ℝ≥0∞) (hp : 1 ≤ p)
    (hE : AEStronglyMeasurable gE P) (hF : AEStronglyMeasurable gF P)
    (hInv : AEStronglyMeasurable invTrace P)
    (CE CF CI : ℝ≥0∞)
    (hEmom : eLpNorm gE (2 * p) P ≤ CE)
    (hFmom : eLpNorm gF (2 * p) P ≤ CF)
    (hImom : eLpNorm invTrace (2 * p) P ≤ CI) :
    AEStronglyMeasurable (fun ω => (gE ω + c * gF ω) * invTrace ω) P ∧
    eLpNorm (fun ω => (gE ω + c * gF ω) * invTrace ω) p P ≤
      (CE + ENNReal.ofReal c * CF) * CI := by
  have hsum : AEStronglyMeasurable (fun ω => gE ω + c * gF ω) P :=
    hE.add (hF.const_mul c)
  have hp2 : 1 ≤ 2 * p := hp.trans (le_mul_of_one_le_left' (by norm_num))
  have hs : eLpNorm (fun ω => gE ω + c * gF ω) (2 * p) P ≤
      CE + ENNReal.ofReal c * CF := by
    refine (eLpNorm_add_le hp2).trans ?_
    apply add_le_add hEmom
    change eLpNorm (c • gF) (2 * p) P ≤ _
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hc]
    exact mul_le_mul_right hFmom _
  let : ENNReal.HolderTriple (2 * p) (2 * p) p := ⟨by
    rw [ENNReal.mul_inv (by norm_num) (by norm_num), ← add_mul,
      ENNReal.inv_two_add_inv_two, one_mul]⟩
  constructor
  · exact hsum.mul hInv
  · have hh := eLpNorm_smul_le_mul_eLpNorm (p := 2 * p) (q := 2 * p)
      (r := p) hsum hInv
    exact hh.trans (mul_le_mul' hs hImom)

/-- The previous normalization acts on the actual sum of minimizing energy
measures. The cross energy is transferred from `Γ_F` by local measure order;
the cell restriction and reference-scalar factors remain explicit. -/
theorem aux_prop_conc_normalized_energy_measure_growth
    {X ι : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {μ : Measure X} (E F : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm μ)
    (GammaE : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
    (GammaF : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure F)
    (s : Finset ι) (uE uF : ι → Lp ℝ 2 μ)
    (huE : ∀ i ∈ s, uE i ∈ E.domain)
    (huFE : ∀ i ∈ s, uF i ∈ E.domain)
    (B : Set X) (D sE sF m R a : ℝ)
    (hD : 0 < D) (hsE : 0 < sE) (hm : 0 < m) (ha : 0 ≤ a)
    (gE gF : ι → ℝ) (hgF : ∀ i ∈ s, 0 ≤ gF i)
    (hratio : sF / sE ≤ R)
    (horder : ∀ i ∈ s,
      (GammaE.measure (uF i) B).toReal ≤ m⁻¹ * (GammaF.measure (uF i) B).toReal)
    (hgrowthE : ∀ i ∈ s, (GammaE.measure (uE i) B).toReal ≤ sE * gE i * a)
    (hgrowthF : ∀ i ∈ s, (GammaF.measure (uF i) B).toReal ≤ sF * gF i * a) :
    let nu := ENNReal.ofReal D⁻¹ •
      ∑ i ∈ s, (GammaE.measure (uE i) + GammaE.measure (uF i))
    (nu B).toReal ≤
      (((∑ i ∈ s, gE i) + m⁻¹ * R * (∑ i ∈ s, gF i)) * (D / sE)⁻¹) * a := by
  dsimp only
  rw [aux_relative_response_variation_normalized_sum_toReal D hD s _ B
    (fun i hi => by
      rw [Measure.add_apply]
      exact ENNReal.add_ne_top.mpr
        ⟨GammaE.measure_ne_top (huE i hi) B, GammaE.measure_ne_top (huFE i hi) B⟩)]
  apply aux_prop_conc_normalized_growth_bound _ D sE sF _ _ m R a hD hsE hm
    (Finset.sum_nonneg hgF) ha hratio
  have hsum :
      (∑ i ∈ s, ((GammaE.measure (uE i) + GammaE.measure (uF i)) B).toReal) ≤
        sE * (∑ i ∈ s, gE i) * a + m⁻¹ * (sF * (∑ i ∈ s, gF i) * a) := by
    calc
      _ ≤ ∑ i ∈ s, (sE * gE i * a + m⁻¹ * (sF * gF i * a)) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Measure.add_apply, ENNReal.toReal_add
          (GammaE.measure_ne_top (huE i hi) B) (GammaE.measure_ne_top (huFE i hi) B)]
        exact add_le_add (hgrowthE i hi) ((horder i hi).trans
          (mul_le_mul_of_nonneg_left (hgrowthF i hi) (inv_nonneg.mpr hm.le)))
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
          ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hD.le)).trans_eq (by ring)

end
end SubdiffusiveProcess.Paper



set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace SubdiffusiveProcess.Paper
noncomputable section

/-- Normalized growth on one supplied cell. `muE`,
`muEF`, and `muF` are respectively the sums of the E-minimizer energies,
the E-energies of the F-minimizers, and the F-minimizer energies.
The reference coefficient and reciprocal-trace moments are separate,
independently supplied inputs, not positivity in place of inverse moments. -/
theorem prop_conc_normalized_growth
    {Ω X : Type*} [MeasurableSpace Ω] [PseudoMetricSpace X] [MeasurableSpace X]
    (P : Measure Ω) (q : Set X)
    (muE muEF muF : Ω → Measure X) (D gE gF : Ω → ℝ)
    (sE sF m c t : ℝ) (hsE : 0 < sE) (hm : 0 < m) (hc : 0 ≤ c)
    (hcoeff : m⁻¹ * (sF / sE) ≤ c)
    (hD : ∀ᵐ ω ∂P, 0 < D ω)
    (hgE : ∀ᵐ ω ∂P, 0 ≤ gE ω) (hgF : ∀ᵐ ω ∂P, 0 ≤ gF ω)
    (hfinite : ∀ᵐ ω ∂P, muE ω q ≠ ⊤ ∧ muEF ω q ≠ ⊤ ∧ muF ω q ≠ ⊤)
    (horder : ∀ᵐ ω ∂P, ∀ B : Set X, B ⊆ q →
      (muEF ω B).toReal ≤ m⁻¹ * (muF ω B).toReal)
    (hgrowth : ∀ᵐ ω ∂P, ∀ (x : X) (rho : ℝ), 0 < rho → rho ≤ 1 →
      (muE ω (Metric.ball x rho ∩ q)).toReal ≤ sE * gE ω * rho ^ t ∧
      (muF ω (Metric.ball x rho ∩ q)).toReal ≤ sF * gF ω * rho ^ t)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (CE CF CI : ℝ≥0)
    (hEmeas : AEStronglyMeasurable gE P) (hFmeas : AEStronglyMeasurable gF P)
    (hImeas : AEStronglyMeasurable (fun ω => (D ω / sE)⁻¹) P)
    (hEmom : eLpNorm gE (2 * p) P ≤ CE)
    (hFmom : eLpNorm gF (2 * p) P ≤ CF)
    (hImom : eLpNorm (fun ω => (D ω / sE)⁻¹) (2 * p) P ≤ CI) :
    ∃ K : Ω → ℝ,
      AEStronglyMeasurable K P ∧
      (∀ᵐ ω ∂P, 0 ≤ K ω) ∧
      eLpNorm K p P ≤ (CE + ENNReal.ofReal c * CF) * CI ∧
      (∀ᵐ ω ∂P, ∀ (x : X) (rho : ℝ), 0 < rho → rho ≤ 1 →
        ((ENNReal.ofReal (D ω)⁻¹ • (muE ω + muEF ω))
          (Metric.ball x rho ∩ q)).toReal ≤ K ω * rho ^ t) := by
  let K : Ω → ℝ := fun ω => (gE ω + c * gF ω) * (D ω / sE)⁻¹
  have hK := aux_prop_conc_normalized_growth_moment P gE gF
    (fun ω => (D ω / sE)⁻¹) c hc p hp hEmeas hFmeas hImeas CE CF CI
    hEmom hFmom hImom
  refine ⟨K, hK.1, ?_, hK.2, ?_⟩
  · filter_upwards [hD, hgE, hgF] with ω hDω hEω hFω
    exact mul_nonneg (add_nonneg hEω (mul_nonneg hc hFω))
      (inv_nonneg.mpr (div_nonneg hDω.le hsE.le))
  · filter_upwards [hD, hgF, hfinite, horder, hgrowth] with ω hDω hFω hfin ho hg
    intro x rho hrho hrho1
    let B := Metric.ball x rho ∩ q
    have hBq : B ⊆ q := Set.inter_subset_right
    have hEfin : muE ω B ≠ ⊤ := ne_top_of_le_ne_top hfin.1 (measure_mono hBq)
    have hEFfin : muEF ω B ≠ ⊤ := ne_top_of_le_ne_top hfin.2.1 (measure_mono hBq)
    have hnu : ((ENNReal.ofReal (D ω)⁻¹ • (muE ω + muEF ω)) B).toReal =
        ((muE ω B).toReal + (muEF ω B).toReal) / D ω := by
      rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (inv_nonneg.mpr hDω.le),
        Measure.add_apply, ENNReal.toReal_add hEfin hEFfin]
      ring
    rw [hnu]
    have hraw := add_le_add (hg x rho hrho hrho1).1
      ((ho B hBq).trans (mul_le_mul_of_nonneg_left (hg x rho hrho hrho1).2
        (inv_nonneg.mpr hm.le)))
    have hn := aux_prop_conc_normalized_growth_bound
      (((muE ω B).toReal + (muEF ω B).toReal) / D ω)
      (D ω) sE sF (gE ω) (gF ω) m (sF / sE) (rho ^ t)
      hDω hsE hm hFω (Real.rpow_nonneg hrho.le _) le_rfl
      (div_le_div_of_nonneg_right hraw hDω.le)
    apply hn.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (add_le_add_right (mul_le_mul_of_nonneg_right hcoeff hFω) (gE ω))
        (inv_nonneg.mpr (div_nonneg hDω.le hsE.le))) (Real.rpow_nonneg hrho.le _)

end
end SubdiffusiveProcess.Paper
