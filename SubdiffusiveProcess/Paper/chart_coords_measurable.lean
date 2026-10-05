module

public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.good_event
public import SubdiffusiveProcess.Paper.lem_neumann_error_volume_measurable
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.VariationalResponses.CellDirichlet
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
public import Homogenization.Book.Ch02.Matrices
public import Homogenization.Book.Ch02.MultiscaleEllipticity
public import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
public import SubdiffusiveProcess.CoarseGrainingVocab.Sensitivity
public import SubdiffusiveProcess.CoarseGrainingVocab.HomogenizationError
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Tactic

@[expose] public section




set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped ENNReal NNReal BigOperators Topology

noncomputable section
namespace SubdiffusiveProcess.Paper


/-! # Measurability of chart coordinates

The coordinate-value construction combines continuity of the charts with
measurability of the observation maps. The auxiliary declarations below
supply the component statements used by
`aux_lem_band_piece_coords_value_measurable_core`. -/

/-! # Coordinate measurability

The coordinate statements use the continuity of the charts and the
measurability of the coefficient and observation maps. Each theorem below
retains its displayed hypotheses; the construction of charts and observations
belongs to the cited suppliers. -/






theorem aux_continuity_scalarRatioLInf_le_of_ae_bound {d : ℕ}
    {U : Ch02.Domain d} {a b : Vec d → ℝ} {W : ℝ} (hW0 : 0 ≤ W)
    (h : ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), |a x / b x - 1| ≤ W) :
    scalarRatioLInf U a b ≤ W := by
  unfold scalarRatioLInf
  rw [SubdiffusiveProcess.RawLp.eLpNorm_top_exponent]
  have hess : eLpNormEssSup (fun x => a x / b x - 1) (volumeMeasureOn (U : Set (Vec d))) ≤
      ENNReal.ofReal W := eLpNormEssSup_le_of_ae_bound (by simpa [Real.norm_eq_abs] using h)
  calc
    (eLpNormEssSup (fun x => a x / b x - 1)
        (volumeMeasureOn (U : Set (Vec d)))).toReal ≤ (ENNReal.ofReal W).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hess
    _ = W := ENNReal.toReal_ofReal hW0

/-- If `b` is within a uniform factor `exp ε` of `a` (both directions, a.e.), the scalar ratio
`L^∞` errors `scalarRatioLInf U b a` and `scalarRatioLInf U a b` are both `≤ exp ε - 1`. -/
theorem aux_continuity_scalarRatioLInf_le_of_ratio_bound {d : ℕ} {U : Ch02.Domain d}
    {a b : Vec d → ℝ} (ha : ScalarCoeffOnData U a) (hb : ScalarCoeffOnData U b)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hupper : ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), b x ≤ Real.exp ε * a x)
    (hlower : ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), Real.exp (-ε) * a x ≤ b x) :
    scalarRatioLInf U b a ≤ Real.exp ε - 1 ∧ scalarRatioLInf U a b ≤ Real.exp ε - 1 := by
  have hW0 : (0 : ℝ) ≤ Real.exp ε - 1 := by
    have := Real.one_le_exp hε
    linarith
  have hexpsum : (2 : ℝ) ≤ Real.exp ε + Real.exp (-ε) := by
    have h1 := Real.add_one_le_exp ε
    have h2 := Real.add_one_le_exp (-ε)
    linarith
  have hbound : ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)),
      |b x / a x - 1| ≤ Real.exp ε - 1 := by
    filter_upwards [ha.aeBounds, hupper, hlower] with x hax hux hlx
    have hapos : 0 < a x := lt_of_lt_of_le ha.lam_pos hax.1
    have hratio_le : b x / a x ≤ Real.exp ε := by
      rw [div_le_iff₀ hapos]; linarith
    have hratio_ge : Real.exp (-ε) ≤ b x / a x := by
      rw [le_div_iff₀ hapos]; linarith
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hbound' : ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)),
      |a x / b x - 1| ≤ Real.exp ε - 1 := by
    filter_upwards [ha.aeBounds, hb.aeBounds, hupper, hlower] with x hax hbx hux hlx
    have hapos : 0 < a x := lt_of_lt_of_le ha.lam_pos hax.1
    have hbpos : 0 < b x := lt_of_lt_of_le hb.lam_pos hbx.1
    have hepos : 0 < Real.exp ε := Real.exp_pos ε
    have hratio_le : a x / b x ≤ Real.exp ε := by
      rw [div_le_iff₀ hbpos]
      have hlx' : Real.exp (-ε) * a x ≤ b x := hlx
      have hprod : Real.exp ε * Real.exp (-ε) = 1 := by
        rw [Real.exp_neg]; exact mul_inv_cancel₀ hepos.ne'
      have : a x ≤ Real.exp ε * b x := by
        have hstep : Real.exp ε * (Real.exp (-ε) * a x) ≤ Real.exp ε * b x :=
          mul_le_mul_of_nonneg_left hlx' hepos.le
        rwa [← mul_assoc, hprod, one_mul] at hstep
      linarith
    have hratio_ge : Real.exp (-ε) ≤ a x / b x := by
      rw [le_div_iff₀ hbpos]
      have hprod : Real.exp (-ε) * Real.exp ε = 1 := by
        rw [Real.exp_neg]; exact inv_mul_cancel₀ hepos.ne'
      have hstep : Real.exp (-ε) * b x ≤ Real.exp (-ε) * (Real.exp ε * a x) :=
        mul_le_mul_of_nonneg_left hux (Real.exp_nonneg (-ε))
      rwa [← mul_assoc, hprod, one_mul] at hstep
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  exact ⟨aux_continuity_scalarRatioLInf_le_of_ae_bound hW0 hbound,
    aux_continuity_scalarRatioLInf_le_of_ae_bound hW0 hbound'⟩

/-- For a scalar coefficient, `J(U,p,q;a) + p·q ≥ 0`: by `responseJ_split` (available
unconditionally for symmetric coefficients, and every scalar coefficient is symmetric),
`J + p·q` is the sum of two quadratic forms `½ p·sigmaCoarse·p` and `½ q·sigmaStarInvCoarse·q`,
both PSD (`sigmaStarInvCoarse` is always `PosDef`; `sigmaCoarse = bCoarse` for symmetric
coefficients by `derived_matrices`, and `bCoarse` is always `PosSemidef`). -/
theorem aux_continuity_responseJ_add_vecDot_nonneg {d : ℕ} {U : Ch02.Domain d}
    {a : Vec d → ℝ} (ha : ScalarCoeffOnData U a) (p q : Vec d) :
    0 ≤ Ch02.responseJ U ha.toCoeffOn p q + vecDot p q := by
  have hsym : Ch02.CoeffOn.IsSymmetric ha.toCoeffOn := ha.isSymmetric
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory U ha.toCoeffOn hsym
  have hsplit := hTheory.response_dirichlet_neumann_split p q
  have hD := hTheory.dirichlet_value_by_sigma p
  have hN := hTheory.neumann_value_by_sigmaStarInv q
  have hbeq := hTheory.derived_matrices.2.2
  have hSigmaPSD : (Ch02.sigmaCoarse U ha.toCoeffOn).PosSemidef := hbeq ▸ Ch02.bCoarse_posSemidef U ha.toCoeffOn
  have hSigma : 0 ≤ vecDot p (matVecMul (Ch02.sigmaCoarse U ha.toCoeffOn) p) := by
    simpa [vecDot, matVecMul, dotProduct, Matrix.mulVec] using
      hSigmaPSD.dotProduct_mulVec_nonneg p
  have hSSI : 0 ≤ vecDot q (matVecMul (Ch02.sigmaStarInvCoarse U ha.toCoeffOn) q) := by
    simpa [vecDot, matVecMul, dotProduct, Matrix.mulVec] using
      (Ch02.sigmaStarInvCoarse_posDef U ha.toCoeffOn).posSemidef.dotProduct_mulVec_nonneg q
  rw [hsplit, hD, hN]
  linarith




theorem aux_continuity_responseJ_sensitivity_one {d : ℕ} {U : Ch02.Domain d}
    {a b : Vec d → ℝ} (ha : ScalarCoeffOnData U a) (hb : ScalarCoeffOnData U b)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta ≤ 1) (p q : Vec d) :
    Ch02.responseJ U hb.toCoeffOn p q ≤
      (1 + delta) * Ch02.responseJ U ha.toCoeffOn p q +
        3 / delta * (scalarRatioLInf U a b ^ 2 + scalarRatioLInf U b a ^ 2) *
          (Ch02.responseJ U ha.toCoeffOn p q + vecDot p q) := by
  have h := SubdiffusiveProcess.CoarseGrainingVocab.responseJ_sensitivity ha hb one_pos hdelta hdelta_one p q
  have hfa : (fun x => (1:ℝ) * a x) = a := funext fun x => one_mul (a x)
  have hfb : (fun x => (1:ℝ)⁻¹ * b x) = b := by
    funext x; simp
  rw [hfa, hfb] at h
  simp only [SubdiffusiveProcess.CoarseGrainingVocab.J, Real.sqrt_one, inv_one, one_smul] at h
  exact h

/-- Generic real-number combination lemma: two "one-directional" `(1+7δ)`-Lipschitz-type
bounds (each direction bounded using the OTHER side as base point, `δ ∈ (0,1]`) combine into a
genuine two-sided bound `|Y − X| ≤ 56δ(X+Z)`. Not tied to `responseJ`; reusable for any pair of
quantities related by such sensitivity estimates. -/
theorem aux_continuity_combine_two_sided {X Y Z δ : ℝ} (hδpos : 0 < δ) (hδ1 : δ ≤ 1)
    (hX0 : 0 ≤ X) (hZ0 : 0 ≤ Z)
    (h1 : Y ≤ (1 + 7 * δ) * X + 7 * δ * Z) (h2 : X ≤ (1 + 7 * δ) * Y + 7 * δ * Z) :
    |Y - X| ≤ 56 * δ * (X + Z) := by
  have hYbound : Y ≤ 8 * X + 7 * δ * Z := by
    have hcoef : (0 : ℝ) ≤ (7 - 7 * δ) * X := mul_nonneg (by linarith) hX0
    nlinarith [h1, hcoef]
  have hstep : 7 * δ * Y ≤ 7 * δ * (8 * X + 7 * δ * Z) :=
    mul_le_mul_of_nonneg_left hYbound (by positivity)
  have hδsq : δ * δ ≤ δ := by nlinarith [mul_nonneg hδpos.le (by linarith : (0:ℝ) ≤ 1 - δ)]
  have hδsqZ : 7 * δ * (7 * δ * Z) ≤ 49 * δ * Z := by
    have : δ * δ * Z ≤ δ * Z := mul_le_mul_of_nonneg_right hδsq hZ0
    nlinarith [this]
  have key3 : X - Y ≤ 56 * δ * X + 56 * δ * Z := by nlinarith [h2, hstep, hδsqZ]
  rw [abs_le]
  refine ⟨by nlinarith [key3], by nlinarith [h1, hδpos, hX0, hZ0]⟩

/-- One-directional half of (C1): `Jb ≤ (1+7δ)·Ja + 7δ·|p·q|`, given the combined sensitivity
bound `3/δ·(ratio² sum) ≤ 6δ`. Isolated as its own lemma (with `δ` a genuine bound variable,
not a `let`) so the nonlinear arithmetic steps stay within the heartbeat budget and match
reliably; folding `δ := exp ε − 1` via `set` in the caller made the analogous inline steps
fail (the `let`-bound `δ` confused `nlinarith`'s atom matching). -/
theorem aux_continuity_one_direction {d : ℕ} {U : Ch02.Domain d}
    {a b : Vec d → ℝ} (ha : ScalarCoeffOnData U a) (hb : ScalarCoeffOnData U b)
    {δ : ℝ} (hδpos : 0 < δ) (hδ1 : δ ≤ 1)
    (hcombine : 3 / δ * (scalarRatioLInf U a b ^ 2 + scalarRatioLInf U b a ^ 2) ≤ 6 * δ)
    (p q : Vec d) :
    Ch02.responseJ U hb.toCoeffOn p q ≤
      (1 + 7 * δ) * Ch02.responseJ U ha.toCoeffOn p q + 7 * δ * |vecDot p q| := by
  have hsumA : 0 ≤ Ch02.responseJ U ha.toCoeffOn p q + vecDot p q :=
    aux_continuity_responseJ_add_vecDot_nonneg ha p q
  have hb_le := aux_continuity_responseJ_sensitivity_one ha hb hδpos hδ1 p q
  have hmul := mul_le_mul_of_nonneg_right hcombine hsumA
  have hstep : Ch02.responseJ U hb.toCoeffOn p q ≤
      (1 + δ) * Ch02.responseJ U ha.toCoeffOn p q +
        6 * δ * (Ch02.responseJ U ha.toCoeffOn p q + vecDot p q) :=
    hb_le.trans (by linarith [hmul])
  have hpq1 : vecDot p q ≤ |vecDot p q| := le_abs_self _
  have hpqδ : 6 * δ * vecDot p q ≤ 6 * δ * |vecDot p q| :=
    mul_le_mul_of_nonneg_left hpq1 (by positivity)
  have hpqδ0 : (0:ℝ) ≤ δ * |vecDot p q| := mul_nonneg hδpos.le (abs_nonneg _)
  nlinarith [hstep, hpqδ, hpqδ0]

/-- **(C1)** `Ch02.responseJ` is continuous in the coefficient under a uniform multiplicative
`exp(±ε)` perturbation, `ε ≤ log 2`: `|J(b) − J(a)| ≤ 56·(exp ε − 1)·(J(a) + |p·q|)`. General
statement over any `Ch02.Domain d` and any two `ScalarCoeffOnData` witnesses for the SAME
scalar functions being compared (not tied to any particular chart or cube). -/
theorem aux_continuity_responseJ_ratio {d : ℕ} {U : Ch02.Domain d}
    {a b : Vec d → ℝ} (ha : ScalarCoeffOnData U a) (hb : ScalarCoeffOnData U b)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ Real.log 2)
    (hupper : ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), b x ≤ Real.exp ε * a x)
    (hlower : ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), Real.exp (-ε) * a x ≤ b x)
    (p q : Vec d) :
    |Ch02.responseJ U hb.toCoeffOn p q - Ch02.responseJ U ha.toCoeffOn p q| ≤
      56 * (Real.exp ε - 1) * (Ch02.responseJ U ha.toCoeffOn p q + |vecDot p q|) := by
  set δ : ℝ := Real.exp ε - 1 with hδdef
  have hδpos : 0 < δ := by
    have := Real.exp_lt_exp.mpr hε
    simp only [Real.exp_zero] at this
    linarith
  have hδ1 : δ ≤ 1 := by
    have h2 : Real.exp ε ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hε1
    rw [Real.exp_log (by norm_num)] at h2
    linarith
  obtain ⟨hWab, hWba⟩ :=
    aux_continuity_scalarRatioLInf_le_of_ratio_bound ha hb hε.le hupper hlower
  have hWab0 : 0 ≤ scalarRatioLInf U b a := scalarRatioLInf_nonneg U b a
  have hWba0 : 0 ≤ scalarRatioLInf U a b := scalarRatioLInf_nonneg U a b
  have hW2 : scalarRatioLInf U b a ^ 2 + scalarRatioLInf U a b ^ 2 ≤ 2 * δ ^ 2 := by
    have h1 : scalarRatioLInf U b a ^ 2 ≤ δ ^ 2 := by
      have := mul_le_mul hWab hWab hWab0 (hWab0.trans hWab); nlinarith [this]
    have h2 : scalarRatioLInf U a b ^ 2 ≤ δ ^ 2 := by
      have := mul_le_mul hWba hWba hWba0 (hWba0.trans hWba); nlinarith [this]
    linarith
  have hcombine : 3 / δ * (scalarRatioLInf U b a ^ 2 + scalarRatioLInf U a b ^ 2) ≤ 6 * δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hδpos]; nlinarith [hW2]
  have hpq1 : vecDot p q ≤ |vecDot p q| := le_abs_self _
  have hsumA : 0 ≤ Ch02.responseJ U ha.toCoeffOn p q + vecDot p q :=
    aux_continuity_responseJ_add_vecDot_nonneg ha p q
  have hsumB : 0 ≤ Ch02.responseJ U hb.toCoeffOn p q + vecDot p q :=
    aux_continuity_responseJ_add_vecDot_nonneg hb p q
  have hcombine' : 3 / δ * (scalarRatioLInf U a b ^ 2 + scalarRatioLInf U b a ^ 2) ≤ 6 * δ := by
    rw [add_comm]; exact hcombine
  have key1 := aux_continuity_one_direction ha hb hδpos hδ1 hcombine' p q
  have key2 := aux_continuity_one_direction hb ha hδpos hδ1 hcombine p q
  exact aux_continuity_combine_two_sided hδpos hδ1
    (Ch02.responseJ_nonneg U ha.toCoeffOn p q) (abs_nonneg (vecDot p q)) key1 key2




/-- Corollary of (C1) at `q = 0` (`vecDot p 0 = 0` kills the additive term). -/
theorem aux_continuity_responseJ_ratio_zero_right {d : ℕ} {U : Ch02.Domain d}
    {a b : Vec d → ℝ} (ha : ScalarCoeffOnData U a) (hb : ScalarCoeffOnData U b)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ Real.log 2)
    (hupper : ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), b x ≤ Real.exp ε * a x)
    (hlower : ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), Real.exp (-ε) * a x ≤ b x)
    (p : Vec d) :
    |Ch02.responseJ U hb.toCoeffOn p 0 - Ch02.responseJ U ha.toCoeffOn p 0| ≤
      56 * (Real.exp ε - 1) * Ch02.responseJ U ha.toCoeffOn p 0 := by
  have h := aux_continuity_responseJ_ratio ha hb hε hε1 hupper hlower p 0
  simpa [vecDot_zero_right] using h

/-- Corollary of (C1) at `p = 0` (`vecDot 0 q = 0` kills the additive term). -/
theorem aux_continuity_responseJ_ratio_zero_left {d : ℕ} {U : Ch02.Domain d}
    {a b : Vec d → ℝ} (ha : ScalarCoeffOnData U a) (hb : ScalarCoeffOnData U b)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ Real.log 2)
    (hupper : ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), b x ≤ Real.exp ε * a x)
    (hlower : ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), Real.exp (-ε) * a x ≤ b x)
    (q : Vec d) :
    |Ch02.responseJ U hb.toCoeffOn 0 q - Ch02.responseJ U ha.toCoeffOn 0 q| ≤
      56 * (Real.exp ε - 1) * Ch02.responseJ U ha.toCoeffOn 0 q := by
  have h := aux_continuity_responseJ_ratio ha hb hε hε1 hupper hlower 0 q
  simpa [vecDot_zero_left] using h

/-- **(C2a)** `sigmaStarInvCoarse` entrywise continuity (unconditional, no symmetry needed):
direct from the definitional polarization `sigmaStarInvEntry` and (C1) at `p = 0`. -/
theorem aux_continuity_sigmaStarInvEntry {d : ℕ} {U : Ch02.Domain d}
    {a b : Vec d → ℝ} (ha : ScalarCoeffOnData U a) (hb : ScalarCoeffOnData U b)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ Real.log 2)
    (hupper : ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), b x ≤ Real.exp ε * a x)
    (hlower : ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), Real.exp (-ε) * a x ≤ b x)
    (i j : Fin d) :
    |Ch02.sigmaStarInvEntry U hb.toCoeffOn i j - Ch02.sigmaStarInvEntry U ha.toCoeffOn i j| ≤
      168 * (Real.exp ε - 1) * (Ch02.responseJ U ha.toCoeffOn 0 (Pi.single i 1) +
        Ch02.responseJ U ha.toCoeffOn 0 (Pi.single j 1) +
        Ch02.responseJ U ha.toCoeffOn 0 (Pi.single i 1 + Pi.single j 1)) := by
  have hJnonneg : ∀ v : Vec d, 0 ≤ Ch02.responseJ U ha.toCoeffOn 0 v :=
    fun v => Ch02.responseJ_nonneg U ha.toCoeffOn 0 v
  have hε0 : 0 ≤ Real.exp ε - 1 := by have := Real.one_le_exp hε.le; linarith
  rw [abs_le]
  by_cases hij : i = j
  · subst hij
    rw [show Ch02.sigmaStarInvEntry U hb.toCoeffOn i i =
          2 * Ch02.responseJ U hb.toCoeffOn 0 (Pi.single i 1) from dite_eq_left rfl,
        show Ch02.sigmaStarInvEntry U ha.toCoeffOn i i =
          2 * Ch02.responseJ U ha.toCoeffOn 0 (Pi.single i 1) from dite_eq_left rfl]
    have h := aux_continuity_responseJ_ratio_zero_left ha hb hε hε1 hupper hlower (Pi.single i 1)
    rw [abs_le] at h
    obtain ⟨h1, h2⟩ := h
    constructor
    · nlinarith [h1, hJnonneg (Pi.single i 1), hJnonneg (Pi.single i 1 + Pi.single i 1)]
    · nlinarith [h2, hJnonneg (Pi.single i 1), hJnonneg (Pi.single i 1 + Pi.single i 1)]
  · rw [show Ch02.sigmaStarInvEntry U hb.toCoeffOn i j =
          Ch02.responseJ U hb.toCoeffOn 0 (Pi.single i 1 + Pi.single j 1) -
            Ch02.responseJ U hb.toCoeffOn 0 (Pi.single i 1) -
            Ch02.responseJ U hb.toCoeffOn 0 (Pi.single j 1) from dite_eq_right hij,
        show Ch02.sigmaStarInvEntry U ha.toCoeffOn i j =
          Ch02.responseJ U ha.toCoeffOn 0 (Pi.single i 1 + Pi.single j 1) -
            Ch02.responseJ U ha.toCoeffOn 0 (Pi.single i 1) -
            Ch02.responseJ U ha.toCoeffOn 0 (Pi.single j 1) from dite_eq_right hij]
    have h1 := aux_continuity_responseJ_ratio_zero_left ha hb hε hε1 hupper hlower (Pi.single i 1)
    have h2 := aux_continuity_responseJ_ratio_zero_left ha hb hε hε1 hupper hlower (Pi.single j 1)
    have h3 := aux_continuity_responseJ_ratio_zero_left ha hb hε hε1 hupper hlower
      (Pi.single i 1 + Pi.single j 1)
    rw [abs_le] at h1 h2 h3
    obtain ⟨h1a, h1b⟩ := h1
    obtain ⟨h2a, h2b⟩ := h2
    obtain ⟨h3a, h3b⟩ := h3
    constructor
    · nlinarith [h1a, h1b, h2a, h2b, h3a, h3b, hJnonneg (Pi.single i 1), hJnonneg (Pi.single j 1),
        hJnonneg (Pi.single i 1 + Pi.single j 1)]
    · nlinarith [h1a, h1b, h2a, h2b, h3a, h3b, hJnonneg (Pi.single i 1), hJnonneg (Pi.single j 1),
        hJnonneg (Pi.single i 1 + Pi.single j 1)]

/-- The quadratic form of `sigmaCoarse` is exactly `2·J(·,0)`, for any scalar (hence symmetric)
coefficient: `response_dirichlet_neumann_split` at `q = 0` kills `symmetricNeumannNu(0) = 0`
(`neumann_value_by_sigmaStarInv` at `q=0`, `vecDot 0 0 = 0`) and `vecDot p 0 = 0`, leaving
`J(p,0) = symmetricDirichletNu(p) = ½ p·sigmaCoarse·p` (`dirichlet_value_by_sigma`). -/
theorem aux_continuity_sigmaCoarse_quadratic {d : ℕ} {U : Ch02.Domain d}
    {a : Vec d → ℝ} (ha : ScalarCoeffOnData U a) (p : Vec d) :
    vecDot p (matVecMul (Ch02.sigmaCoarse U ha.toCoeffOn) p) =
      2 * Ch02.responseJ U ha.toCoeffOn p 0 := by
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory U ha.toCoeffOn ha.isSymmetric
  have hsplit := hTheory.response_dirichlet_neumann_split p 0
  have hD := hTheory.dirichlet_value_by_sigma p
  have hN := hTheory.neumann_value_by_sigmaStarInv (0 : Vec d)
  rw [matVecMul_zero, vecDot_zero_right] at hN
  rw [vecDot_zero_right] at hsplit
  rw [hD, hN] at hsplit
  linarith [hsplit]



theorem aux_continuity_sigmaCoarse_entry {d : ℕ} {U : Ch02.Domain d}
    {a : Vec d → ℝ} (ha : ScalarCoeffOnData U a) (i j : Fin d) :
    Ch02.sigmaCoarse U ha.toCoeffOn i j =
      if i = j then 2 * Ch02.responseJ U ha.toCoeffOn (Pi.single i 1) 0
      else Ch02.responseJ U ha.toCoeffOn (Pi.single i 1 + Pi.single j 1) 0 -
        Ch02.responseJ U ha.toCoeffOn (Pi.single i 1) 0 -
        Ch02.responseJ U ha.toCoeffOn (Pi.single j 1) 0 := by
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl]
    have hQ := aux_continuity_sigmaCoarse_quadratic ha (Pi.single i 1)
    rw [vecDot_single_left, matVecMul_single] at hQ
    linarith [hQ]
  · rw [ite_eq_right hij]
    have hQij := aux_continuity_sigmaCoarse_quadratic ha (Pi.single i 1 + Pi.single j 1)
    have hQi := aux_continuity_sigmaCoarse_quadratic ha (Pi.single i 1)
    have hQj := aux_continuity_sigmaCoarse_quadratic ha (Pi.single j 1)
    rw [vecDot_single_left, matVecMul_single] at hQi hQj
    rw [basis_sum_pairing] at hQij
    have hsymm : Ch02.sigmaCoarse U ha.toCoeffOn i j = Ch02.sigmaCoarse U ha.toCoeffOn j i :=
      (Ch02.sigmaCoarse_isSymm U ha.toCoeffOn).apply j i
    linarith [hQij, hQi, hQj, hsymm]

/-- **(C2b)** `sigmaCoarse` entrywise continuity for scalar (symmetric) coefficients, from
(C1) at `q = 0` applied to the polarization formula above. Same shape as (C2a); the Dirichlet
side needs symmetry (`ScalarCoeffOnData.isSymmetric`) where the Neumann side did not. -/
theorem aux_continuity_sigmaCoarse_entry_ratio {d : ℕ} {U : Ch02.Domain d}
    {a b : Vec d → ℝ} (ha : ScalarCoeffOnData U a) (hb : ScalarCoeffOnData U b)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ Real.log 2)
    (hupper : ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), b x ≤ Real.exp ε * a x)
    (hlower : ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), Real.exp (-ε) * a x ≤ b x)
    (i j : Fin d) :
    |Ch02.sigmaCoarse U hb.toCoeffOn i j - Ch02.sigmaCoarse U ha.toCoeffOn i j| ≤
      168 * (Real.exp ε - 1) * (Ch02.responseJ U ha.toCoeffOn (Pi.single i 1) 0 +
        Ch02.responseJ U ha.toCoeffOn (Pi.single j 1) 0 +
        Ch02.responseJ U ha.toCoeffOn (Pi.single i 1 + Pi.single j 1) 0) := by
  have hJnonneg : ∀ v : Vec d, 0 ≤ Ch02.responseJ U ha.toCoeffOn v 0 :=
    fun v => Ch02.responseJ_nonneg U ha.toCoeffOn v 0
  have hε0 : 0 ≤ Real.exp ε - 1 := by have := Real.one_le_exp hε.le; linarith
  rw [aux_continuity_sigmaCoarse_entry hb i j, aux_continuity_sigmaCoarse_entry ha i j, abs_le]
  by_cases hij : i = j
  · subst hij
    simp only [ite_true]
    have h := aux_continuity_responseJ_ratio_zero_right ha hb hε hε1 hupper hlower (Pi.single i 1)
    rw [abs_le] at h
    obtain ⟨h1, h2⟩ := h
    exact ⟨by nlinarith [h1, hJnonneg (Pi.single i 1), hJnonneg (Pi.single i 1 + Pi.single i 1)],
      by nlinarith [h2, hJnonneg (Pi.single i 1), hJnonneg (Pi.single i 1 + Pi.single i 1)]⟩
  · simp only [ite_eq_right hij]
    have h1 := aux_continuity_responseJ_ratio_zero_right ha hb hε hε1 hupper hlower (Pi.single i 1)
    have h2 := aux_continuity_responseJ_ratio_zero_right ha hb hε hε1 hupper hlower (Pi.single j 1)
    have h3 := aux_continuity_responseJ_ratio_zero_right ha hb hε hε1 hupper hlower
      (Pi.single i 1 + Pi.single j 1)
    rw [abs_le] at h1 h2 h3
    obtain ⟨h1a, h1b⟩ := h1
    obtain ⟨h2a, h2b⟩ := h2
    obtain ⟨h3a, h3b⟩ := h3
    exact ⟨by nlinarith [h1a, h1b, h2a, h2b, h3a, h3b, hJnonneg (Pi.single i 1),
        hJnonneg (Pi.single j 1), hJnonneg (Pi.single i 1 + Pi.single j 1)],
      by nlinarith [h1a, h1b, h2a, h2b, h3a, h3b, hJnonneg (Pi.single i 1),
        hJnonneg (Pi.single j 1), hJnonneg (Pi.single i 1 + Pi.single j 1)]⟩

/-- **(C2b)** `bCoarse` entrywise continuity: `bCoarse = sigmaCoarse` for every scalar
(symmetric) coefficient (`derived_matrices`), so this is exactly
`aux_continuity_sigmaCoarse_entry_ratio` transported along that equality. -/
theorem aux_continuity_bCoarse_entry_ratio {d : ℕ} {U : Ch02.Domain d}
    {a b : Vec d → ℝ} (ha : ScalarCoeffOnData U a) (hb : ScalarCoeffOnData U b)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ Real.log 2)
    (hupper : ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), b x ≤ Real.exp ε * a x)
    (hlower : ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), Real.exp (-ε) * a x ≤ b x)
    (i j : Fin d) :
    |Ch02.bCoarse U hb.toCoeffOn i j - Ch02.bCoarse U ha.toCoeffOn i j| ≤
      168 * (Real.exp ε - 1) * (Ch02.responseJ U ha.toCoeffOn (Pi.single i 1) 0 +
        Ch02.responseJ U ha.toCoeffOn (Pi.single j 1) 0 +
        Ch02.responseJ U ha.toCoeffOn (Pi.single i 1 + Pi.single j 1) 0) := by
  have hbeq_a := (Ch02.responseSymmetricDirichletNeumannTheory U ha.toCoeffOn
    ha.isSymmetric).derived_matrices.2.2
  have hbeq_b := (Ch02.responseSymmetricDirichletNeumannTheory U hb.toCoeffOn
    hb.isSymmetric).derived_matrices.2.2
  rw [hbeq_a, hbeq_b]
  exact aux_continuity_sigmaCoarse_entry_ratio ha hb hε hε1 hupper hlower i j

/-! ## (C2, `paperScalarProbeMax`)

`paperScalarProbeMax Q a alpha = ⨆ e ∈ unit sphere, ENNReal.ofReal (J (α^{-1/2}e, α^{1/2}e))`
(`SubdiffusiveProcess/Vocab/PaperScalarProbeMax.lean`). (C1) gives a UNIFORM (in `e`) bound since
`|p·q| = |e·e| = 1` for every unit `e`, so continuity transfers through the `iSup` by
monotonicity — no summability issue at all (`ℝ≥0∞`-valued). -/

/-! ## (C3) Weighted-series ratio continuity

The two functionals are `LambdaSqFinite`
(uppercase, no reciprocal) and `lambdaSqFinite` (lowercase, `= (∑' ...)⁻¹`) and their global-modulus bounds must be distinguished. The proposed conclusion `|f b - f a| ≤ ε(f a + C)`. The uppercase clause is TRUE (direct
weighted average, no reciprocal). The LOWERCASE clause is FALSE as stated: from `|S_b − S_a| ≤
ε S_a` alone (even at `C = 0`) one only gets `|S_b⁻¹ − S_a⁻¹| ≤ ε/((1−ε)S_a)`, NOT `ε·S_a⁻¹`; with
`C > 0`, `S_b` can approach `0` while `S_a` stays fixed, blowing up `S_b⁻¹` with no bound of the
claimed form. Accordingly, `LambdaSqFinite` keeps the global form; `lambdaSqFinite` is
restated as LOCAL (pointwise `ε`-`δ`) continuity at each `a` with `S_a > 0`, matching the
shape (C4) needs. -/

/-! ## (C4) measurability composition.

Audit finding: the ORIGINAL `aux_continuity_measurable_of_ratio_continuous_HOLE` used a FIXED
global modulus `56(e^ε−1)(F a + 1)` in its `hFratio` hypothesis. This cannot be instantiated at
`F = I.lam` (etc.): `I.lam`'s own modulus, transported through `lambdaSqFinite`'s RECIPROCAL,
grows like the coefficient's SIZE (roughly `λ_a²`), not a universal constant times `(F a + 1)` —
exactly the reciprocal blow-up (C3a) hit. FIXED below: `hFcont` is now POINTWISE/LOCAL (`∀a, ∀η>0,
∃ε>0, ...`), matching what (C3a)'s lowercase clause (and any other reciprocal-shaped functional)
actually supplies. Proved: `𝒱 := {x : Lp ℝ ∞ μ | ∃c>0, c ≤ x a.e.}`; `F' := F∘(⇑·)`
is `ContinuousOn 𝒱` (at each `x∈𝒱` with witness `c_x`, `hFcont` gives `ε`, and `δ := c_x(1-e^{-ε})`
works, via the same AM-GM computation as (C1)); this transports through
`continuousOn_iff_continuous_restrict` + `Measurable.subtype_mk` + `Continuous.measurable` — no
countable exhaustion needed, since `𝒱` itself (not a fixed-`c` piece of it) is the right domain. -/

/-- Build a `ScalarCoeffOnData` witness from a.e. two-sided bounds and a.e. strong measurability
of the raw representative. Generic helper, not tied to any particular `a`. -/
noncomputable def aux_ccm_scalarCoeffOnDataOfBounds {d : ℕ} {U : Ch02.Domain d} (a : Vec d → ℝ)
    {lam Lam : ℝ} (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (haemeas : AEStronglyMeasurable a (volumeMeasureOn (U : Set (Vec d))))
    (haebounds : ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), lam ≤ a x ∧ a x ≤ Lam) :
    ScalarCoeffOnData U a where
  lam := lam
  Lam := Lam
  lam_pos := hlam
  lam_le_Lam := hlamLam
  aeStronglyMeasurable := by
    intro i j
    have hrestrict : (fun x : Vec d => Homogenization.restrictCoeffField (U : Set (Vec d))
        (scalarCoeffField a) x i j) =ᵐ[volumeMeasureOn (U : Set (Vec d))]
        (fun x => if i = j then a x else 0) := by
      filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with x hx
      simp [Homogenization.restrictCoeffField_apply_of_mem hx, scalarCoeffField,
        Homogenization.scalarMatrix, Matrix.one_apply]
    have hentry : AEStronglyMeasurable (fun x => if i = j then a x else 0)
        (volumeMeasureOn (U : Set (Vec d))) := by
      split_ifs with hij
      · exact haemeas
      · exact aestronglyMeasurable_const
    exact hentry.congr hrestrict.symm
  aeBounds := haebounds

/-- The essential-sup of `|f|` gives an a.e. real bound, for `f` with finite `L^∞` seminorm. -/
theorem aux_ae_bound_of_eLpNorm_top_lt_top {d : ℕ} {U : Ch02.Domain d} (f : Vec d → ℝ)
    (hf : eLpNorm f ⊤ (volumeMeasureOn (U : Set (Vec d))) < ⊤) :
    ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)),
      |f x| ≤ (eLpNormEssSup f (volumeMeasureOn (U : Set (Vec d)))).toReal := by
  have hfm : AEStronglyMeasurable f (volumeMeasureOn (U : Set (Vec d))) :=
    (show MemLp f ⊤ (volumeMeasureOn (U : Set (Vec d))) from hf).aestronglyMeasurable
  rw [eLpNorm_exponent_top hfm] at hf
  filter_upwards [ae_le_eLpNormEssSup (μ := volumeMeasureOn (U : Set (Vec d))) (f := f)]
    with x hx
  have hmono := ENNReal.toReal_mono hf.ne hx
  simpa [Real.norm_eq_abs] using hmono

/-- If `‖y - x‖ < δ` in `Lp ℝ ∞ μ`, then `|y t - x t| ≤ δ` for a.e. `t`. -/
theorem aux_ae_close_of_norm_sub_lt {d : ℕ} {U : Ch02.Domain d}
    (x y : Lp ℝ ∞ (volumeMeasureOn (U : Set (Vec d)))) {δ : ℝ} (hδ : 0 < δ)
    (hdist : ‖y - x‖ < δ) :
    ∀ᵐ t ∂ volumeMeasureOn (U : Set (Vec d)),
      |(y : Vec d → ℝ) t - (x : Vec d → ℝ) t| ≤ δ := by
  have heLp : eLpNorm (⇑(y - x)) ⊤ (volumeMeasureOn (U : Set (Vec d))) < ENNReal.ofReal δ := by
    rw [← Lp.enorm_def (y - x), ← ofReal_norm]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _) |>.mpr hdist
  have hfin : eLpNorm (⇑(y - x)) ⊤ (volumeMeasureOn (U : Set (Vec d))) < ⊤ :=
    heLp.trans ENNReal.ofReal_lt_top
  have hbound := aux_ae_bound_of_eLpNorm_top_lt_top (⇑(y - x)) hfin
  have hle : (eLpNormEssSup (⇑(y - x)) (volumeMeasureOn (U : Set (Vec d)))).toReal ≤ δ := by
    rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable (y - x))] at heLp
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top heLp.le
    rwa [ENNReal.toReal_ofReal hδ.le] at h2
  have hsub : ∀ᵐ t ∂ (volumeMeasureOn (U : Set (Vec d))),
      (⇑(y - x) : Vec d → ℝ) t = (y : Vec d → ℝ) t - (x : Vec d → ℝ) t :=
    Lp.coeFn_sub y x
  filter_upwards [hbound, hsub] with t ht heq
  calc |(y : Vec d → ℝ) t - (x : Vec d → ℝ) t| = |(⇑(y - x) : Vec d → ℝ) t| := by rw [heq]
    _ ≤ (eLpNormEssSup (⇑(y - x)) (volumeMeasureOn (U : Set (Vec d)))).toReal := ht
    _ ≤ δ := hle

/-- **(C4), fixed.** Measurability composition from POINTWISE (local) ratio-continuity:
`g : Ω → Lp ℝ ∞ μ` measurable, a.e. bounded below by a measurable-witnessed `c : Ω → (0,∞)`; `F`
is continuous at every `ScalarCoeffOnData`-admissible `a` in the (C1)/(C2) ratio sense (a genuine
`ε`-`δ` statement, no single global modulus). Then `ω ↦ F (g ω)` is measurable. -/
theorem aux_continuity_measurable_of_local_ratio_continuous
    {d : ℕ} {U : Ch02.Domain d}
    [MeasurableSpace (Lp ℝ ∞ (volumeMeasureOn (U : Set (Vec d))))]
    [BorelSpace (Lp ℝ ∞ (volumeMeasureOn (U : Set (Vec d))))]
    {Ω : Type*} [MeasurableSpace Ω]
    (g : Ω → Lp ℝ ∞ (volumeMeasureOn (U : Set (Vec d)))) (hg : Measurable g)
    (c : Ω → ℝ) (hcpos : ∀ ω, 0 < c ω)
    (hgc : ∀ ω, ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), c ω ≤ (g ω : Vec d → ℝ) x)
    (F : (Vec d → ℝ) → ℝ)
    (hFcont : ∀ (a : Vec d → ℝ), ScalarCoeffOnData U a → ∀ η : ℝ, 0 < η →
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.log 2 ∧
        ∀ (b : Vec d → ℝ), ScalarCoeffOnData U b →
          (∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), b x ≤ Real.exp ε * a x) →
          (∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), Real.exp (-ε) * a x ≤ b x) →
          |F b - F a| ≤ η) :
    Measurable (fun ω => F (g ω : Vec d → ℝ)) := by
  classical
  have hgV : ∀ ω, g ω ∈ {x : Lp ℝ ∞ (volumeMeasureOn (U : Set (Vec d))) |
      ∃ c : ℝ, 0 < c ∧ ∀ᵐ t ∂ volumeMeasureOn (U : Set (Vec d)), c ≤ (x : Vec d → ℝ) t} :=
    fun ω => ⟨c ω, hcpos ω, hgc ω⟩
  have hcont : ContinuousOn (fun x : Lp ℝ ∞ (volumeMeasureOn (U : Set (Vec d))) =>
      F (x : Vec d → ℝ)) {x | ∃ c : ℝ, 0 < c ∧
        ∀ᵐ t ∂ volumeMeasureOn (U : Set (Vec d)), c ≤ (x : Vec d → ℝ) t} := by
    intro x hx
    obtain ⟨cx, hcxpos, hcxle⟩ := hx
    have hxae : AEStronglyMeasurable (x : Vec d → ℝ) (volumeMeasureOn (U : Set (Vec d))) :=
      Lp.aestronglyMeasurable x
    have hxupper : ∀ᵐ t ∂ volumeMeasureOn (U : Set (Vec d)), |(x : Vec d → ℝ) t| ≤
        (eLpNormEssSup (x : Vec d → ℝ) (volumeMeasureOn (U : Set (Vec d)))).toReal :=
      aux_ae_bound_of_eLpNorm_top_lt_top (x : Vec d → ℝ) (Lp.eLpNorm_lt_top x)
    set Lamx : ℝ := max ((eLpNormEssSup (x : Vec d → ℝ)
      (volumeMeasureOn (U : Set (Vec d)))).toReal) cx with hLamxdef
    have hLamxpos : 0 < Lamx := lt_of_lt_of_le hcxpos (le_max_right _ _)
    have hcxLamx : cx ≤ Lamx := le_max_right _ _
    have hxbounds : ∀ᵐ t ∂ volumeMeasureOn (U : Set (Vec d)),
        cx ≤ (x : Vec d → ℝ) t ∧ (x : Vec d → ℝ) t ≤ Lamx := by
      filter_upwards [hcxle, hxupper] with t ht1 ht2
      exact ⟨ht1, (le_abs_self _).trans ht2 |>.trans (le_max_left _ _)⟩
    have hxdata : ScalarCoeffOnData U (x : Vec d → ℝ) :=
      aux_ccm_scalarCoeffOnDataOfBounds (U := U) (x : Vec d → ℝ) hcxpos hcxLamx hxae hxbounds
    rw [Metric.continuousWithinAt_iff]
    intro η hη
    obtain ⟨ε, hεpos, hε1, hFbound⟩ := hFcont (x : Vec d → ℝ) hxdata (η / 2) (by linarith)
    have hexpεlt1 : Real.exp (-ε) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hexpεpos : 0 < Real.exp (-ε) := Real.exp_pos _
    refine ⟨cx * (1 - Real.exp (-ε)), by nlinarith, ?_⟩
    intro y hyV hdist
    have hyae : AEStronglyMeasurable (y : Vec d → ℝ) (volumeMeasureOn (U : Set (Vec d))) :=
      Lp.aestronglyMeasurable y
    set δ : ℝ := cx * (1 - Real.exp (-ε)) with hδdef
    have hδpos : 0 < δ := by nlinarith
    have hclose : ∀ᵐ t ∂ volumeMeasureOn (U : Set (Vec d)),
        |(y : Vec d → ℝ) t - (x : Vec d → ℝ) t| ≤ δ :=
      aux_ae_close_of_norm_sub_lt x y hδpos (by simpa [dist_eq_norm] using hdist)
    have hupper : ∀ᵐ t ∂ volumeMeasureOn (U : Set (Vec d)),
        (y : Vec d → ℝ) t ≤ Real.exp ε * (x : Vec d → ℝ) t := by
      filter_upwards [hclose, hxbounds] with t ht hxt
      have h1 : (y : Vec d → ℝ) t ≤ (x : Vec d → ℝ) t + δ := by
        have := (abs_le.mp ht).2; linarith
      have h2 : (x : Vec d → ℝ) t + δ ≤ Real.exp ε * (x : Vec d → ℝ) t := by
        have hexpge : (1 : ℝ) - Real.exp (-ε) ≤ Real.exp ε - 1 := by
          have h3 := Real.add_one_le_exp ε
          have h4 := Real.add_one_le_exp (-ε)
          nlinarith
        have : δ ≤ (x : Vec d → ℝ) t * (Real.exp ε - 1) := by
          have hxcx : cx ≤ (x : Vec d → ℝ) t := hxt.1
          calc δ = cx * (1 - Real.exp (-ε)) := hδdef
            _ ≤ cx * (Real.exp ε - 1) := by
                apply mul_le_mul_of_nonneg_left hexpge hcxpos.le
            _ ≤ (x : Vec d → ℝ) t * (Real.exp ε - 1) := by
                apply mul_le_mul_of_nonneg_right hxcx
                nlinarith [Real.add_one_le_exp ε]
        nlinarith
      linarith
    have hlower : ∀ᵐ t ∂ volumeMeasureOn (U : Set (Vec d)),
        Real.exp (-ε) * (x : Vec d → ℝ) t ≤ (y : Vec d → ℝ) t := by
      filter_upwards [hclose, hxbounds] with t ht hxt
      have h1 : (x : Vec d → ℝ) t - δ ≤ (y : Vec d → ℝ) t := by
        have := (abs_le.mp ht).1; linarith
      have h2 : Real.exp (-ε) * (x : Vec d → ℝ) t ≤ (x : Vec d → ℝ) t - δ := by
        have hxcx : cx ≤ (x : Vec d → ℝ) t := hxt.1
        have : δ ≤ (x : Vec d → ℝ) t * (1 - Real.exp (-ε)) := by
          calc δ = cx * (1 - Real.exp (-ε)) := hδdef
            _ ≤ (x : Vec d → ℝ) t * (1 - Real.exp (-ε)) := by
                apply mul_le_mul_of_nonneg_right hxcx
                linarith
        nlinarith
      linarith
    have hLamy_ge : Real.exp (-ε) * cx ≤ Real.exp ε * Lamx := by
      have h1 : Real.exp (-ε) ≤ Real.exp ε := Real.exp_le_exp.mpr (by linarith)
      calc Real.exp (-ε) * cx ≤ Real.exp ε * cx :=
            mul_le_mul_of_nonneg_right h1 hcxpos.le
        _ ≤ Real.exp ε * Lamx := mul_le_mul_of_nonneg_left hcxLamx (Real.exp_pos ε).le
    have hydata : ScalarCoeffOnData U (y : Vec d → ℝ) :=
      aux_ccm_scalarCoeffOnDataOfBounds (U := U) (y : Vec d → ℝ)
        (mul_pos hexpεpos hcxpos) hLamy_ge hyae
        (by
          filter_upwards [hupper, hlower, hxbounds] with t htu htl hxt
          refine ⟨?_, ?_⟩
          · calc Real.exp (-ε) * cx ≤ Real.exp (-ε) * (x : Vec d → ℝ) t :=
                  mul_le_mul_of_nonneg_left hxt.1 hexpεpos.le
              _ ≤ (y : Vec d → ℝ) t := htl
          · calc (y : Vec d → ℝ) t ≤ Real.exp ε * (x : Vec d → ℝ) t := htu
              _ ≤ Real.exp ε * Lamx := mul_le_mul_of_nonneg_left hxt.2 (Real.exp_pos ε).le)
    have := hFbound (y : Vec d → ℝ) hydata hupper hlower
    calc dist (F (y : Vec d → ℝ)) (F (x : Vec d → ℝ)) = |F (y : Vec d → ℝ) - F (x : Vec d → ℝ)| :=
          Real.dist_eq _ _
      _ ≤ η / 2 := this
      _ < η := by linarith
  have hg' : Measurable (fun ω => (⟨g ω, hgV ω⟩ :
      {x : Lp ℝ ∞ (volumeMeasureOn (U : Set (Vec d))) |
        ∃ c : ℝ, 0 < c ∧ ∀ᵐ t ∂ volumeMeasureOn (U : Set (Vec d)), c ≤ (x : Vec d → ℝ) t})) :=
    hg.subtype_mk
  have hFrestrict : Continuous
      ({x : Lp ℝ ∞ (volumeMeasureOn (U : Set (Vec d))) |
          ∃ c : ℝ, 0 < c ∧ ∀ᵐ t ∂ volumeMeasureOn (U : Set (Vec d)), c ≤ (x : Vec d → ℝ) t}.domRestrict
        (fun x => F (x : Vec d → ℝ))) :=
    continuousOn_iff_continuous_domRestrict.mp hcont
  exact hFrestrict.measurable.comp hg'

/-! ## `reference` measurability: The `j = 1` case extends to any fixed `(k,y)`, `kappa` does not depend on `omega`. -/

/-! The ratio helpers transfer per-cube response bounds to finite suprema. The epsilon choice converts a global linear ratio bound into the local continuity estimate. -/

theorem aux_core_openCubeSet_originCube_eq {d : ℕ} :
    Homogenization.openCubeSet (Homogenization.originCube d 0) =
      (centeredCube (0 : Vec d) 1 one_pos : Set (Vec d)) := by
  rw [centeredCube_eq_pi (0 : Vec d) one_pos]
  ext x
  simp only [Homogenization.openCubeSet, Homogenization.originCube,
    Homogenization.cubeScaleFactor, mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_true_left,
    Set.mem_Ioo, Pi.zero_apply]
  norm_num

theorem aux_core_rescale_qmp {d : ℕ} (w : Vec d) {r : ℝ} (hr : r ≠ 0) :
    MeasureTheory.Measure.QuasiMeasurePreserving (fun x : Vec d => w + r • x)
      volume volume :=
  (measurePreserving_add_left volume w).quasiMeasurePreserving.comp
    (MeasureTheory.Measure.quasiMeasurePreserving_smul volume hr)

theorem aux_core_rescale_mem_centeredCube {d : ℕ} (w : Vec d) {r : ℝ} (hr : 0 < r)
    {x : Vec d} (hx : x ∈ (centeredCube (0 : Vec d) 1 one_pos : Set (Vec d))) :
    w + r • x ∈ (centeredCube w r hr : Set (Vec d)) := by
  rw [centeredCube_eq_pi (0 : Vec d) one_pos] at hx
  rw [centeredCube_eq_pi w hr]
  intro i _
  have hxi := hx i (Set.mem_univ i)
  simp only [Pi.zero_apply, zero_sub, zero_add, Set.mem_Ioo] at hxi
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Set.mem_Ioo]
  constructor
  · nlinarith [hxi.1, hxi.2]
  · nlinarith [hxi.1, hxi.2]

/-- The one bridging fact the order's docstring asked for: precomposition of an a.e. statement on
the outer cube by the fixed rescaling `x ↦ w + r • x` stays true a.e. on any measurable subset of
the unit root, PROVIDED that subset's image lands in the outer cube (always true here since the
whole unit root does). No genuine `Lp`-precomposition isometry is built; a.e. statements pull back
directly through the quasi-measure-preserving map. -/
theorem aux_core_ae_pullback {d : ℕ} (w : Vec d) {r : ℝ} (hr : 0 < r)
    {S : Set (Vec d)} (hS : MeasurableSet S)
    (hSC : S ⊆ (centeredCube (0 : Vec d) 1 one_pos : Set (Vec d)))
    {p : Vec d → Prop}
    (hp : ∀ᵐ y ∂ volume.restrict (centeredCube w r hr : Set (Vec d)), p y) :
    ∀ᵐ x ∂ volume.restrict S, p (w + r • x) := by
  have hqmp := aux_core_rescale_qmp w hr.ne'
  have hglobal : ∀ᵐ y ∂ volume, y ∈ (centeredCube w r hr : Set (Vec d)) → p y :=
    (ae_restrict_iff' (centeredCube w r hr).isOpen.measurableSet).mp hp
  have hpulled : ∀ᵐ x ∂ volume,
      (w + r • x) ∈ (centeredCube w r hr : Set (Vec d)) → p (w + r • x) :=
    hqmp.ae hglobal
  have hpulled' : ∀ᵐ x ∂ volume, x ∈ S → p (w + r • x) := by
    filter_upwards [hpulled] with x hx hxS
    exact hx (aux_core_rescale_mem_centeredCube w hr (hSC hxS))
  exact (ae_restrict_iff' hS).mpr hpulled'

noncomputable def aux_core_outerDomain {d : ℕ} (z : Vec d) (r : ℝ) (hr : 0 < r) :
    Ch02.Domain d where
  carrier := (centeredCube z r hr : Set (Vec d))
  isDomain := isOpenBoundedConvexDomain_centeredCube z hr
  nonempty := ⟨z, Metric.mem_ball_self (half_pos hr)⟩

@[simp] theorem aux_core_outerDomain_coe {d : ℕ} (z : Vec d) (r : ℝ) (hr : 0 < r) :
    ((aux_core_outerDomain z r hr : Ch02.Domain d) : Set (Vec d)) =
      (centeredCube z r hr : Set (Vec d)) := rfl

open Classical in
/-- Total, `Subtype.ext`-safe wrap of a raw function into a `PositiveCoefficient` of the outer
cube: junk (the constant coefficient `1`) off the `MemLp ⊤`-and-bounded-below set. Since
`PositiveCoefficient`'s second component is a `Prop`, `Subtype.ext` makes this depend only on the
underlying `Lp` VALUE — so whenever `a` genuinely is (the coercion of) a `PositiveCoefficient`, or
witnesses a `ScalarCoeffOnData`, this recovers exactly that value (`aux_core_wrapPC_eq`,
`aux_core_wrapPC_ae`), never a different reconstruction. -/
noncomputable def aux_core_wrapPC {d : ℕ} (z : Vec d) (r : ℝ) (hr : 0 < r)
    (a : Vec d → ℝ) : PositiveCoefficient (centeredCube z r hr) :=
  if h : MemLp a ⊤ (volume.restrict (centeredCube z r hr : Set (Vec d))) ∧
      ∃ c : ℝ, 0 < c ∧
        ∀ᵐ x ∂ volume.restrict (centeredCube z r hr : Set (Vec d)), c ≤ a x then
    ⟨h.1.toLp a, h.2.choose, h.2.choose_spec.1, by
      filter_upwards [h.1.coeFn_toLp, h.2.choose_spec.2] with x hx1 hx2
      rw [hx1]; exact hx2⟩
  else
    haveI : IsFiniteMeasure (volume.restrict (centeredCube z r hr : Set (Vec d))) :=
      centeredCube_isFiniteMeasure z r hr
    ⟨(memLp_const (1 : ℝ)).toLp (fun _ => (1 : ℝ)), 1, one_pos, by
      filter_upwards [(memLp_const (1 : ℝ)).coeFn_toLp
        (μ := volume.restrict (centeredCube z r hr : Set (Vec d)))] with x hx
      rw [hx]⟩

theorem aux_core_wrapPC_eq {d : ℕ} (z : Vec d) (r : ℝ) (hr : 0 < r)
    (aP : PositiveCoefficient (centeredCube z r hr)) :
    aux_core_wrapPC z r hr (fun x => (aP.val : Vec d → ℝ) x) = aP := by
  have hMemLp : MemLp (fun x => (aP.val : Vec d → ℝ) x) ⊤
      (volume.restrict (centeredCube z r hr : Set (Vec d))) := Lp.memLp aP.val
  obtain ⟨c, hc, hcle⟩ := aP.property
  have hcond : MemLp (fun x => (aP.val : Vec d → ℝ) x) ⊤
      (volume.restrict (centeredCube z r hr : Set (Vec d))) ∧
      ∃ c : ℝ, 0 < c ∧
        ∀ᵐ x ∂ volume.restrict (centeredCube z r hr : Set (Vec d)),
          c ≤ (aP.val : Vec d → ℝ) x := ⟨hMemLp, c, hc, hcle⟩
  try dsimp only [PositiveCoefficient] at *
  unfold aux_core_wrapPC
  try dsimp only [PositiveCoefficient] at *
  rw [dite_eq_left hcond]
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [hcond.1.coeFn_toLp] with x hx using hx

theorem aux_core_aestronglyMeasurable_rescale {d : ℕ} (w : Vec d) {r : ℝ}
    (hr : 0 < r) {S : Set (Vec d)} (hS : MeasurableSet S)
    (hSC : S ⊆ (centeredCube (0 : Vec d) 1 one_pos : Set (Vec d)))
    {a : Vec d → ℝ}
    (ha : AEStronglyMeasurable a (volume.restrict (centeredCube w r hr : Set (Vec d)))) :
    AEStronglyMeasurable (fun x => a (w + r • x)) (volume.restrict S) := by
  obtain ⟨g, hg_meas, hg_eq⟩ := ha
  refine ⟨fun x => g (w + r • x), ?_, ?_⟩
  · exact hg_meas.measurable.comp
      (by fun_prop : Measurable (fun x : Vec d => w + r • x)) |>.stronglyMeasurable
  · exact aux_core_ae_pullback w hr hS hSC (p := fun y => a y = g y) hg_eq

theorem aux_core_scalarCoeffOnData_aestronglyMeasurable {d : ℕ} {U : Ch02.Domain d}
    {a : Vec d → ℝ} (ha : ScalarCoeffOnData U a) (i0 : Fin d) :
    AEStronglyMeasurable a (volumeMeasureOn (U : Set (Vec d))) := by
  have hrestrict : (fun x : Vec d => Homogenization.restrictCoeffField
      (U : Set (Vec d)) (scalarCoeffField a) x i0 i0) =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      (fun x => a x) := by
    filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with x hx
    simp [Homogenization.restrictCoeffField_apply_of_mem hx, scalarCoeffField,
      Homogenization.scalarMatrix]
  exact (ha.aeStronglyMeasurable i0 i0).congr hrestrict

/-- Transport a `ScalarCoeffOnData` witness on the outer cube down to any sub-cube `S` of the unit
root `Ω' := openCubeSet (originCube d 0)` via the affine rescaling `x ↦ w + r • x`. Reusable at
EVERY descendant `Q` of the unit root (not just `Q = originCube d 0`), since only `S ⊆ Ω'` is
needed. -/
noncomputable def aux_core_scalarCoeffOnData_rescale {d : ℕ} (w : Vec d) {r : ℝ}
    (hr : 0 < r) {U : Ch02.Domain d} {S : Set (Vec d)}
    (hUS : (U : Set (Vec d)) = S) (hS : MeasurableSet S)
    (hSC : S ⊆ (centeredCube (0 : Vec d) 1 one_pos : Set (Vec d)))
    {a : Vec d → ℝ}
    (ha : ScalarCoeffOnData (aux_core_outerDomain w r hr) a) (i0 : Fin d) :
    ScalarCoeffOnData U (fun x => a (w + r • x)) := by
  have haemeas := aux_core_scalarCoeffOnData_aestronglyMeasurable ha i0
  refine aux_ccm_scalarCoeffOnDataOfBounds (U := U) (fun x => a (w + r • x)) ha.lam_pos ha.lam_le_Lam ?_ ?_
  · have := aux_core_aestronglyMeasurable_rescale w hr hS hSC
      (a := a) (by simpa [aux_core_outerDomain_coe] using haemeas)
    simpa [volumeMeasureOn, hUS] using! this
  · have := aux_core_ae_pullback w hr (S := S) hS hSC (p := fun y => ha.lam ≤ a y ∧ a y ≤ ha.Lam)
      (by simpa [aux_core_outerDomain_coe] using ha.aeBounds)
    simpa [volumeMeasureOn, hUS] using! this

theorem aux_core_scalarCoeffOnData_memLp {d : ℕ} {U : Ch02.Domain d} {a : Vec d → ℝ}
    (ha : ScalarCoeffOnData U a) (i0 : Fin d) :
    MemLp a ⊤ (volumeMeasureOn (U : Set (Vec d))) := by
  have haem := aux_core_scalarCoeffOnData_aestronglyMeasurable ha i0
  apply memLp_top_of_bound haem ha.Lam
  filter_upwards [ha.aeBounds] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (ha.lam_pos.trans_le hx.1)]
  exact hx.2

theorem aux_core_wrapPC_ae {d : ℕ} (z : Vec d) (r : ℝ) (hr : 0 < r)
    {a : Vec d → ℝ} (ha : ScalarCoeffOnData (aux_core_outerDomain z r hr) a)
    (i0 : Fin d) :
    (aux_core_wrapPC z r hr a).val =ᵐ[volume.restrict (centeredCube z r hr : Set (Vec d))] a := by
  have hMemLp : MemLp a ⊤ (volume.restrict (centeredCube z r hr : Set (Vec d))) := by
    simpa [aux_core_outerDomain_coe] using aux_core_scalarCoeffOnData_memLp ha i0
  have haelam : ∀ᵐ x ∂ volume.restrict (centeredCube z r hr : Set (Vec d)), ha.lam ≤ a x := by
    have h := ha.aeBounds
    simp only [aux_core_outerDomain_coe] at h
    filter_upwards [h] with x hx using hx.1
  have hcond : MemLp a ⊤ (volume.restrict (centeredCube z r hr : Set (Vec d))) ∧
      ∃ c : ℝ, 0 < c ∧
        ∀ᵐ x ∂ volume.restrict (centeredCube z r hr : Set (Vec d)), c ≤ a x :=
    ⟨hMemLp, ha.lam, ha.lam_pos, haelam⟩
  show (aux_core_wrapPC z r hr a).val =ᵐ[volume.restrict (centeredCube z r hr : Set (Vec d))] a
  try dsimp only [PositiveCoefficient] at *
  unfold aux_core_wrapPC
  try dsimp only [PositiveCoefficient] at *
  rw [dite_eq_left hcond]
  exact hcond.1.coeFn_toLp



theorem aux_core_chart_scalarCoeffOnData_AEEq {d : ℕ} (I : _root_.SubdiffusiveProcess.Paper.in_J d) (w : Vec d)
    {r : ℝ} (hr : 0 < r) {a : Vec d → ℝ}
    (ha : ScalarCoeffOnData (aux_core_outerDomain w r hr) a) (i0 : Fin d)
    (Q : Homogenization.TriadicCube d)
    (hQ : Homogenization.openCubeSet Q ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0)) :
    Ch02.CoeffOn.AEEq ((I.chart w r hr (aux_core_wrapPC w r hr a) w r).coeffOn Q)
      ((aux_core_scalarCoeffOnData_rescale w hr (U := Ch02.cubeDomain Q)
          (S := Homogenization.openCubeSet Q) (Ch02.cubeDomain_coe Q)
          (Ch02.cubeDomain Q).isOpen.measurableSet
          (hQ.trans (aux_core_openCubeSet_originCube_eq.le)) ha i0).toCoeffOn) := by
  have hchart := I.chart_eq w r hr (aux_core_wrapPC w r hr a) w r hr (Set.Subset.rfl) Q hQ
  have hpulled := aux_core_ae_pullback w hr
    (S := Homogenization.openCubeSet Q) (Ch02.cubeDomain Q).isOpen.measurableSet
    (hQ.trans (aux_core_openCubeSet_originCube_eq.le))
    (p := fun y => (aux_core_wrapPC w r hr a).val y = a y) (aux_core_wrapPC_ae w r hr ha i0)
  show ((I.chart w r hr (aux_core_wrapPC w r hr a) w r).coeffOn Q).toCoeffField
      =ᵐ[volumeMeasureOn (Homogenization.openCubeSet Q)]
      (fun x => scalarMatrix (a (fun i => w i + r * x i)))
  filter_upwards [hchart, hpulled] with x hx1 hx2
  rw [hx1]
  exact congrArg scalarMatrix hx2

/-- `exp ε - 1 ≤ 2ε` for `ε ∈ [0, log 2]`: `1 - e^{-ε} ≤ ε` (`Real.add_one_le_exp`) times `e^ε ≤ 2`. -/
theorem aux_core_exp_sub_one_le {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ Real.log 2) :
    Real.exp ε - 1 ≤ 2 * ε := by
  have h1 : 1 - Real.exp (-ε) ≤ ε := by nlinarith [Real.add_one_le_exp (-ε)]
  have h2 : Real.exp ε ≤ 2 := by
    calc Real.exp ε ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hε1
      _ = 2 := Real.exp_log (by norm_num)
  have h4 : (1 - Real.exp (-ε)) * Real.exp ε = Real.exp ε - 1 := by
    rw [sub_mul, one_mul, ← Real.exp_add]
    simp
  nlinarith [mul_le_mul_of_nonneg_right h1 (Real.exp_pos ε).le, h4, h2, Real.exp_pos ε]

/-- Turns a GLOBAL linear ratio bound `|F b - F a| ≤ K·(e^ε−1)·C` (the shape (C2)'s entry/matrix-
norm lemmas give) into the POINTWISE/LOCAL form (C4)'s `hFcont` needs, by picking
`ε := min(log 2, η/(2KC+1))`. -/
theorem aux_core_eps_of_linear (K C η : ℝ) (hK0 : 0 ≤ K) (hC0 : 0 ≤ C) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.log 2 ∧ K * (Real.exp ε - 1) * C ≤ η := by
  set ε : ℝ := min (Real.log 2) (η / (2 * K * C + 1)) with hεdef
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hdenpos : (0 : ℝ) < 2 * K * C + 1 := by positivity
  have hfrac_pos : 0 < η / (2 * K * C + 1) := div_pos hη hdenpos
  have hεpos : 0 < ε := lt_min hlog2pos hfrac_pos
  have hεlog2 : ε ≤ Real.log 2 := min_le_left _ _
  have hεfrac : ε ≤ η / (2 * K * C + 1) := min_le_right _ _
  refine ⟨ε, hεpos, hεlog2, ?_⟩
  have hexp := aux_core_exp_sub_one_le hεpos.le hεlog2
  have hstep : K * (Real.exp ε - 1) * C ≤ K * (2 * ε) * C := by
    apply mul_le_mul_of_nonneg_right _ hC0
    exact mul_le_mul_of_nonneg_left hexp hK0
  have hratio : (2 * K * C) / (2 * K * C + 1) ≤ 1 :=
    (div_le_one hdenpos).mpr (by linarith)
  have hfinal : K * (2 * ε) * C ≤ η := by
    have h5 : 2 * K * C * ε ≤ 2 * K * C * (η / (2 * K * C + 1)) :=
      mul_le_mul_of_nonneg_left hεfrac (by positivity)
    have h6 : 2 * K * C * (η / (2 * K * C + 1)) = η * ((2 * K * C) / (2 * K * C + 1)) := by
      ring
    have h7 : η * ((2 * K * C) / (2 * K * C + 1)) ≤ η * 1 :=
      mul_le_mul_of_nonneg_left hratio hη.le
    nlinarith [h5, h6, h7]
  linarith [hstep, hfinal]





/-! ## Measurability of I.lam / I.Lam / I.err (no continuity route) -/

section MeasLamGeneric
variable {Ω : Type*} [MeasurableSpace Ω]

theorem aux_measlam_finsetSupReal {α : Type*} (s : Finset α) (f : α → Ω → ℝ)
    (hf : ∀ a ∈ s, Measurable (f a)) :
    Measurable (fun ω => Homogenization.Book.Ch02.finsetSupReal s (fun a => f a ω)) := by
  unfold Homogenization.Book.Ch02.finsetSupReal
  simp only [Set.image_eq_range]
  show Measurable fun ω => ⨆ x : ↥(↑s : Set α), f ↑x ω
  exact Measurable.iSup fun x => hf ↑x x.2

theorem aux_measlam_matrixNorm {d : ℕ} (A : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ i j, Measurable (fun ω => A ω i j)) :
    Measurable (fun ω => Homogenization.Book.Ch02.matrixNorm (A ω)) := by
  have hcont : Continuous (fun M : Matrix (Fin d) (Fin d) ℝ =>
      Homogenization.Book.Ch02.matrixNorm M) := by
    unfold Homogenization.Book.Ch02.matrixNorm
    have h1 : Continuous (fun M : Matrix (Fin d) (Fin d) ℝ =>
        Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) M) :=
      LinearMap.continuous_of_finiteDimensional
        ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)).toAlgEquiv.toLinearMap)
    exact continuous_norm.comp h1
  have hmeas : Measurable (fun ω => A ω) := by
    measurability
  exact hcont.measurable.comp hmeas

theorem aux_measlam_lambdaSqFinite {d : ℕ} (Q : Homogenization.TriadicCube d) (s q : ℝ)
    (hs : 0 < s) (hq : 0 < q) (A : Ω → Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (h : ∀ n : ℕ, Measurable (fun ω =>
      Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
        (Q.scale - (n : ℤ)) (A ω))) :
    Measurable (fun ω => Homogenization.Book.Ch02.lambdaSqFinite Q s q (A ω)) := by
  unfold Homogenization.Book.Ch02.lambdaSqFinite
  have hg_meas : ∀ n : ℕ, Measurable (fun ω : Ω =>
      Homogenization.Book.Ch02.geometricWeight s q n *
        (Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
          (Q.scale - (n : ℤ)) (A ω)) ^ (q / 2)) := by
    intro n
    exact Measurable.const_mul ((h n).pow_const (q / 2)) _
  have hg_nn : ∀ (n : ℕ) (ω : Ω), 0 ≤
      Homogenization.Book.Ch02.geometricWeight s q n *
        (Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
          (Q.scale - (n : ℤ)) (A ω)) ^ (q / 2) := by
    intro n ω
    have hdisc : 0 ≤ Homogenization.Book.Ch02.geometricDiscount s q := by
      unfold Homogenization.Book.Ch02.geometricDiscount
      have h1 : Real.rpow (3 : ℝ) (-s * q) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by nlinarith [hs, hq])
      exact sub_nonneg.mpr h1
    have hw : 0 ≤ Homogenization.Book.Ch02.geometricWeight s q n := by
      unfold Homogenization.Book.Ch02.geometricWeight
      exact mul_nonneg hdisc (Real.rpow_nonneg (by norm_num) _)
    have hM : 0 ≤ Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
        (Q.scale - (n : ℤ)) (A ω) := by
      unfold Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
      apply Homogenization.Book.Ch02.finsetSupReal_nonneg
      intro R _
      exact Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm_nonneg R (A ω)
    exact mul_nonneg hw (Real.rpow_nonneg hM _)
  have hsum : Measurable (fun ω : Ω => ∑' n : ℕ,
      Homogenization.Book.Ch02.geometricWeight s q n *
        (Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
          (Q.scale - (n : ℤ)) (A ω)) ^ (q / 2)) := by
    have heq : (fun ω : Ω => ∑' n : ℕ,
        Homogenization.Book.Ch02.geometricWeight s q n *
          (Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
            (Q.scale - (n : ℤ)) (A ω)) ^ (q / 2))
        = fun ω : Ω => (∑' n : ℕ, ENNReal.ofReal
            (Homogenization.Book.Ch02.geometricWeight s q n *
              (Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
                (Q.scale - (n : ℤ)) (A ω)) ^ (q / 2))).toReal := by
      funext ω
      rw [ENNReal.tsum_toReal_eq (fun n => ENNReal.ofReal_ne_top)]
      exact (tsum_congr (fun n => ENNReal.toReal_ofReal (hg_nn n ω))).symm
    rw [heq]
    exact Measurable.ennreal_toReal
      (Measurable.tsum (fun n => (hg_meas n).ennreal_ofReal))
  exact hsum.pow_const (-(2 / q))

theorem aux_measlam_LambdaSqFinite {d : ℕ} (Q : Homogenization.TriadicCube d) (s q : ℝ)
    (hs : 0 < s) (hq : 0 < q) (A : Ω → Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (h : ∀ n : ℕ, Measurable (fun ω =>
      Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale Q
        (Q.scale - (n : ℤ)) (A ω))) :
    Measurable (fun ω => Homogenization.Book.Ch02.LambdaSqFinite Q s q (A ω)) := by
  have hm : ∀ (k : ℤ) (a : Homogenization.Book.Ch02.TriadicCoeffFamily d),
      0 ≤ Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale Q k a := by
    intro k a
    unfold Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale Homogenization.Book.Ch02.finsetSupReal
    apply Real.sSup_nonneg
    rintro y ⟨R, -, rfl⟩
    exact Homogenization.Book.Ch02.coarseBMatrixNorm_nonneg R a
  have hg : ∀ n : ℕ, 0 ≤ Homogenization.Book.Ch02.geometricWeight s q n := by
    intro n
    unfold Homogenization.Book.Ch02.geometricWeight Homogenization.Book.Ch02.geometricDiscount
    apply mul_nonneg
    · exact sub_nonneg.mpr (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by nlinarith [mul_pos hs hq]))
    · exact Real.rpow_nonneg (by norm_num) _
  unfold Homogenization.Book.Ch02.LambdaSqFinite
  have hbase : Measurable (fun ω => ∑' n : ℕ,
      Homogenization.Book.Ch02.geometricWeight s q n *
        (Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) (A ω)) ^ (q / 2)) := by
    have hT : Measurable (fun ω => ∑' n : ℕ, ENNReal.ofReal
        (Homogenization.Book.Ch02.geometricWeight s q n *
          (Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) (A ω)) ^ (q / 2))) := by
      apply Measurable.tsum
      intro n
      measurability
    convert hT.ennreal_toReal using 1
    funext ω
    rw [ENNReal.tsum_toReal_eq (fun n => ENNReal.ofReal_ne_top)]
    refine tsum_congr fun n => ?_
    rw [ENNReal.toReal_ofReal]
    exact mul_nonneg (hg n) (Real.rpow_nonneg (hm (Q.scale - (n : ℤ)) (A ω)) _)
  have hcont : Continuous (fun x : ℝ => x ^ (2 / q)) := Real.continuous_rpow_const (by positivity)
  exact hcont.measurable.comp hbase

end MeasLamGeneric

section MeasLamChart
variable {Ω : Type*} [MeasurableSpace Ω]

theorem aux_measlam_lam_of_entries {d : ℕ} (I : _root_.SubdiffusiveProcess.Paper.in_J d) (w : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (a : Ω → PositiveCoefficient (centeredCube w r hr))
    (sigma : ℝ) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (hent : ∀ R : Homogenization.TriadicCube d,
      Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0) →
      ∀ i j : Fin d, Measurable (fun ω =>
        Homogenization.Book.Ch02.sigmaStarInvCoarse (Homogenization.Book.Ch02.cubeDomain R)
          ((I.chart w r hr (a ω) w r).coeffOn R) i j)) :
    Measurable (fun ω => I.lam w r hr (a ω) w r sigma 2) := by
  have hfun : (fun ω => I.lam w r hr (a ω) w r sigma 2)
      = (fun ω => Homogenization.Book.Ch02.lambdaSqFinite (Homogenization.originCube d 0) sigma 2
          (I.chart w r hr (a ω) w r)) := by
    funext ω
    rw [I.lam_eq w r hr (a ω) w r hr subset_rfl sigma hsigma 2 one_le_two]
    rw [ite_eq_right ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat,
      Homogenization.Book.Ch02.lambdaSq_finite]
  rw [hfun]
  apply aux_measlam_lambdaSqFinite (Q := Homogenization.originCube d 0) (s := sigma) (q := 2)
    hsigma.1 (by norm_num)
  intro n
  unfold Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
  apply aux_measlam_finsetSupReal
  intro R hR
  unfold Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm
  apply aux_measlam_matrixNorm
  intro i j
  apply hent R _ i j
  exact Homogenization.openCubeSet_subset_of_mem_descendantsAtScale
    (by simp [Homogenization.originCube]) hR

theorem aux_measlam_Lam_of_entries {d : ℕ} (I : _root_.SubdiffusiveProcess.Paper.in_J d) (w : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (a : Ω → PositiveCoefficient (centeredCube w r hr))
    (sigma : ℝ) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (hent : ∀ R : Homogenization.TriadicCube d,
      Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0) →
      ∀ i j : Fin d, Measurable (fun ω =>
        Homogenization.Book.Ch02.bCoarse (Homogenization.Book.Ch02.cubeDomain R)
          ((I.chart w r hr (a ω) w r).coeffOn R) i j)) :
    Measurable (fun ω => I.Lam w r hr (a ω) w r sigma 2) := by
  rw [show (fun ω => I.Lam w r hr (a ω) w r sigma 2) =
      (fun ω => Homogenization.Book.Ch02.LambdaSqFinite (Homogenization.originCube d 0) sigma 2
        (I.chart w r hr (a ω) w r)) from by
    funext ω
    rw [I.Lam_eq w r hr (a ω) w r hr subset_rfl sigma hsigma 2 one_le_two]
    rw [ite_eq_right ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat,
      Homogenization.Book.Ch02.LambdaSq_finite]]
  apply aux_measlam_LambdaSqFinite (Q := Homogenization.originCube d 0) sigma 2 hsigma.1 (by norm_num)
  intro n
  unfold Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale
  apply aux_measlam_finsetSupReal
  intro R hR
  unfold Homogenization.Book.Ch02.coarseBMatrixNorm
  apply aux_measlam_matrixNorm
  intro i j
  apply hent R _ i j
  have hk : (Homogenization.originCube d 0).scale - (n : ℤ) ≤ (Homogenization.originCube d 0).scale := by
    omega
  rw [Homogenization.descendantsAtScale_eq_descendantsAtDepth (Homogenization.originCube d 0) hk] at hR
  exact Homogenization.openCubeSet_subset_of_mem_descendantsAtDepth hR

end MeasLamChart



section MeasErrGeneric
variable {Ω : Type*} [MeasurableSpace Ω]

theorem aux_measerr_sphere_sup {d : ℕ} (G : Ω → Homogenization.Vec d → ℝ)
    (hGmeas : ∀ e, Measurable (fun ω => G ω e)) (hGcont : ∀ ω, Continuous (G ω)) :
    Measurable (fun ω => ⨆ e : {e : Homogenization.Vec d // Homogenization.vecNormSq e = 1},
      ENNReal.ofReal (G ω e)) := by
  obtain ⟨D, hDcount, hDdense⟩ :=
    TopologicalSpace.exists_countable_dense {e : Homogenization.Vec d // Homogenization.vecNormSq e = 1}
  have : Countable D := hDcount.to_subtype
  have hkey : ∀ ω, (⨆ e : {e : Homogenization.Vec d // Homogenization.vecNormSq e = 1},
      ENNReal.ofReal (G ω e.1)) = ⨆ e : D, ENNReal.ofReal (G ω e.1.1) := by
    intro ω
    refine le_antisymm ?_ ?_
    · refine le_of_forall_lt (fun c hc => ?_)
      obtain ⟨e0, he0⟩ := lt_iSup_iff.mp hc
      have hcont : Continuous (fun e : {e : Homogenization.Vec d //
          Homogenization.vecNormSq e = 1} => ENNReal.ofReal (G ω e.1)) :=
        ENNReal.continuous_ofReal.comp ((hGcont ω).comp continuous_subtype_val)
      have hUopen : IsOpen {e : {e : Homogenization.Vec d //
          Homogenization.vecNormSq e = 1} | c < ENNReal.ofReal (G ω e.1)} :=
        isOpen_lt continuous_const hcont
      have hUne : ({e : {e : Homogenization.Vec d //
          Homogenization.vecNormSq e = 1} | c < ENNReal.ofReal (G ω e.1)}).Nonempty :=
        ⟨e0, he0⟩
      obtain ⟨e1, he1D, he1U⟩ := hDdense.exists_mem_open hUopen hUne
      exact lt_of_lt_of_le he1U (le_iSup (fun e : D => ENNReal.ofReal (G ω e.1.1))
        ⟨e1, he1D⟩)
    · refine iSup_le (fun e => ?_)
      exact le_iSup (fun e : {e : Homogenization.Vec d // Homogenization.vecNormSq e = 1} =>
        ENNReal.ofReal (G ω e.1)) e.1
  rw [funext hkey]
  exact Measurable.iSup (fun e => (hGmeas e.1.1).ennreal_ofReal)

theorem aux_measerr_quadratic_caratheodory {d : ℕ}
    (S T : Ω → Matrix (Fin d) (Fin d) ℝ) (alpha : Ω → ℝ)
    (hS : ∀ i j, Measurable (fun ω => S ω i j)) (hT : ∀ i j, Measurable (fun ω => T ω i j))
    (halpha : Measurable alpha) :
    (∀ e : Homogenization.Vec d, Measurable (fun ω =>
      (1 / 2 : ℝ) * (alpha ω)⁻¹ * Homogenization.vecDot e (Homogenization.matVecMul (S ω) e) +
        (1 / 2 : ℝ) * alpha ω * Homogenization.vecDot e (Homogenization.matVecMul (T ω) e) - 1)) ∧
    (∀ ω, Continuous (fun e : Homogenization.Vec d =>
      (1 / 2 : ℝ) * (alpha ω)⁻¹ * Homogenization.vecDot e (Homogenization.matVecMul (S ω) e) +
        (1 / 2 : ℝ) * alpha ω * Homogenization.vecDot e (Homogenization.matVecMul (T ω) e) - 1)) := by
  constructor
  · intro e
    simp only [Homogenization.vecDot, Homogenization.matVecMul]
    fun_prop
  · intro ω
    simp only [Homogenization.vecDot, Homogenization.matVecMul]
    fun_prop

theorem aux_measerr_errorFinite_of_probeMax {d : ℕ} (s : ℝ) (_hs : 0 < s)
    (A : Ω → Homogenization.Book.Ch02.TriadicCoeffFamily d) (alpha : Ω → ℝ)
    (hR : ∀ R : Homogenization.TriadicCube d,
      Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0) →
      Measurable (fun ω => SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R (A ω) (alpha ω))) :
    Measurable (fun ω => (SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite
      (Homogenization.originCube d 0) 0 s Homogenization.Book.Ch02.MultiscaleExponent.infinity 2
      (A ω) (alpha ω)).toReal) := by
  apply Measurable.ennreal_toReal
  simp only [SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite,
    SubdiffusiveProcess.CoarseGrainingVocab.paperScaleResponseAtScale,
    SubdiffusiveProcess.CoarseGrainingVocab.paperMaxDescendantProbeAtScale]
  apply Measurable.pow_const
  apply Measurable.tsum
  intro l
  apply Measurable.const_mul
  apply Measurable.pow_const
  apply Measurable.pow_const
  apply Measurable.iSup
  intro R
  refine hR R.val ?_
  have hle : (0 : ℤ) - (l : ℤ) ≤ (Homogenization.originCube d 0).scale := by
    rw [show (Homogenization.originCube d 0).scale = 0 from rfl]
    omega
  exact Homogenization.openCubeSet_subset_of_mem_descendantsAtDepth (by
    rw [← Homogenization.descendantsAtScale_eq_descendantsAtDepth (Homogenization.originCube d 0) hle]
    exact R.property)

end MeasErrGeneric

section MeasErrChart
variable {Ω : Type*} [MeasurableSpace Ω]

theorem aux_measerr_err_of_formula {d : ℕ} (I : _root_.SubdiffusiveProcess.Paper.in_J d) (w : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (a : Ω → PositiveCoefficient (centeredCube w r hr))
    (ref : Ω → ℝ) (href : Measurable ref) (hpos : ∀ ω, 0 < ref ω)
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (hform : ∀ R : Homogenization.TriadicCube d,
      Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0) →
      ∀ ω (e : Homogenization.Vec d), Homogenization.vecNormSq e = 1 →
        SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbe R (I.chart w r hr (a ω) w r) (ref ω) e =
          (1 / 2 : ℝ) * (ref ω)⁻¹ * Homogenization.vecDot e (Homogenization.matVecMul
            (Homogenization.Book.Ch02.sigmaCoarse (Homogenization.Book.Ch02.cubeDomain R)
              ((I.chart w r hr (a ω) w r).coeffOn R)) e) +
          (1 / 2 : ℝ) * ref ω * Homogenization.vecDot e (Homogenization.matVecMul
            (Homogenization.Book.Ch02.sigmaStarInvCoarse (Homogenization.Book.Ch02.cubeDomain R)
              ((I.chart w r hr (a ω) w r).coeffOn R)) e) - 1)
    (hsig : ∀ R : Homogenization.TriadicCube d,
      Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0) →
      ∀ i j : Fin d, Measurable (fun ω =>
        Homogenization.Book.Ch02.sigmaCoarse (Homogenization.Book.Ch02.cubeDomain R)
          ((I.chart w r hr (a ω) w r).coeffOn R) i j))
    (hsiginv : ∀ R : Homogenization.TriadicCube d,
      Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0) →
      ∀ i j : Fin d, Measurable (fun ω =>
        Homogenization.Book.Ch02.sigmaStarInvCoarse (Homogenization.Book.Ch02.cubeDomain R)
          ((I.chart w r hr (a ω) w r).coeffOn R) i j)) :
    Measurable (fun ω => I.err w r hr (a ω) w r (ref ω) s 2) := by
  have h1 : (fun ω => I.err w r hr (a ω) w r (ref ω) s 2) =
      (fun ω => (SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite
        (Homogenization.originCube d 0) 0 s Homogenization.Book.Ch02.MultiscaleExponent.infinity 2
        (I.chart w r hr (a ω) w r) (ref ω)).toReal) := by
    funext ω
    rw [I.err_eq w r hr (a ω) w r hr subset_rfl s hs 2 one_le_two (ref ω) (hpos ω),
      ite_eq_right (ENNReal.ofNat_ne_top (n := 2)), ENNReal.toReal_ofNat]
  rw [h1]
  refine aux_measerr_errorFinite_of_probeMax s hs.1 (fun ω => I.chart w r hr (a ω) w r) ref ?_
  intro R hR
  have hcar := aux_measerr_quadratic_caratheodory (d := d)
    (S := fun ω => Homogenization.Book.Ch02.sigmaCoarse (Homogenization.Book.Ch02.cubeDomain R)
        ((I.chart w r hr (a ω) w r).coeffOn R))
    (T := fun ω => Homogenization.Book.Ch02.sigmaStarInvCoarse (Homogenization.Book.Ch02.cubeDomain R)
        ((I.chart w r hr (a ω) w r).coeffOn R))
    ref (hsig R hR) (hsiginv R hR) href
  have hmain : Measurable (fun ω => ⨆ e : {e : Homogenization.Vec d // Homogenization.vecNormSq e = 1},
      ENNReal.ofReal ((1 / 2 : ℝ) * (ref ω)⁻¹ * Homogenization.vecDot (e : Homogenization.Vec d)
          (Homogenization.matVecMul (Homogenization.Book.Ch02.sigmaCoarse (Homogenization.Book.Ch02.cubeDomain R)
            ((I.chart w r hr (a ω) w r).coeffOn R)) (e : Homogenization.Vec d)) +
        (1 / 2 : ℝ) * ref ω * Homogenization.vecDot (e : Homogenization.Vec d)
          (Homogenization.matVecMul (Homogenization.Book.Ch02.sigmaStarInvCoarse (Homogenization.Book.Ch02.cubeDomain R)
            ((I.chart w r hr (a ω) w r).coeffOn R)) (e : Homogenization.Vec d)) - 1)) :=
    aux_measerr_sphere_sup
      (G := fun ω (e : Homogenization.Vec d) =>
        (1 / 2 : ℝ) * (ref ω)⁻¹ * Homogenization.vecDot e
            (Homogenization.matVecMul (Homogenization.Book.Ch02.sigmaCoarse (Homogenization.Book.Ch02.cubeDomain R)
              ((I.chart w r hr (a ω) w r).coeffOn R)) e) +
          (1 / 2 : ℝ) * ref ω * Homogenization.vecDot e
            (Homogenization.matVecMul (Homogenization.Book.Ch02.sigmaStarInvCoarse (Homogenization.Book.Ch02.cubeDomain R)
              ((I.chart w r hr (a ω) w r).coeffOn R)) e) - 1)
      hcar.1 hcar.2
  have heq : (fun ω => SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R (I.chart w r hr (a ω) w r) (ref ω)) =
      (fun ω => ⨆ e : {e : Homogenization.Vec d // Homogenization.vecNormSq e = 1},
        ENNReal.ofReal ((1 / 2 : ℝ) * (ref ω)⁻¹ * Homogenization.vecDot (e : Homogenization.Vec d)
            (Homogenization.matVecMul (Homogenization.Book.Ch02.sigmaCoarse (Homogenization.Book.Ch02.cubeDomain R)
              ((I.chart w r hr (a ω) w r).coeffOn R)) (e : Homogenization.Vec d)) +
          (1 / 2 : ℝ) * ref ω * Homogenization.vecDot (e : Homogenization.Vec d)
            (Homogenization.matVecMul (Homogenization.Book.Ch02.sigmaStarInvCoarse (Homogenization.Book.Ch02.cubeDomain R)
              ((I.chart w r hr (a ω) w r).coeffOn R)) (e : Homogenization.Vec d)) - 1)) := by
    funext ω
    simp only [SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax]
    apply iSup_congr
    intro e
    rw [hform R hR ω (e : Homogenization.Vec d) e.2]
  rw [heq]
  exact hmain

end MeasErrChart



noncomputable def aux_core_probe_formula_R_scalarCoeffOnData {d : ℕ} (w : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (a : PositiveCoefficient (centeredCube w r hr)) :
    ScalarCoeffOnData (aux_core_outerDomain w r hr) (a.val : Vec d → ℝ) := by
  set a' := (a.val : Vec d → ℝ) with ha'def
  let c := a.property.choose
  have hcpos : 0 < c := a.property.choose_spec.1
  have hcle := a.property.choose_spec.2
  have haemeas : AEStronglyMeasurable a' (volumeMeasureOn (aux_core_outerDomain w r hr : Set (Vec d))) := by
    simpa [aux_core_outerDomain_coe, ha'def] using Lp.aestronglyMeasurable a.val
  have hEsup : ∀ᵐ x ∂ volumeMeasureOn (aux_core_outerDomain w r hr : Set (Vec d)),
      a' x ≤ (eLpNormEssSup a' (volumeMeasureOn (aux_core_outerDomain w r hr : Set (Vec d)))).toReal := by
    have hfin : eLpNorm a' ⊤ (volumeMeasureOn (aux_core_outerDomain w r hr : Set (Vec d))) < ⊤ :=
      by
        simpa [aux_core_outerDomain_coe, ha'def] using Lp.eLpNorm_lt_top a.val
    have hbound := aux_ae_bound_of_eLpNorm_top_lt_top a' hfin
    filter_upwards [hbound] with x hx
    exact (le_abs_self _).trans hx
  have hbounds : ∀ᵐ x ∂ volumeMeasureOn (aux_core_outerDomain w r hr : Set (Vec d)),
      c ≤ a' x ∧ a' x ≤ (eLpNormEssSup a' (volumeMeasureOn (aux_core_outerDomain w r hr : Set (Vec d)))).toReal := by
    filter_upwards [hcle, hEsup] with x hx1 hx2
    exact ⟨hx1, hx2⟩
  set Lam := max ((eLpNormEssSup a' (volumeMeasureOn (aux_core_outerDomain w r hr : Set (Vec d)))).toReal) c with hLamdef
  have hlamLam : c ≤ Lam := le_max_right _ _
  have hbounds' : ∀ᵐ x ∂ volumeMeasureOn (aux_core_outerDomain w r hr : Set (Vec d)),
      c ≤ a' x ∧ a' x ≤ Lam := by
    filter_upwards [hbounds] with x hx
    exact ⟨hx.1, hx.2.trans (le_max_left _ _)⟩
  exact aux_ccm_scalarCoeffOnDataOfBounds (U := aux_core_outerDomain w r hr) a' hcpos hlamLam haemeas hbounds'

/-- **Symmetric probe formula on a descendant** (preparer carve for `I.err` measurability):
for any cube `R` inside the unit root, the paper probe of the chart family is the explicit
quadratic form `½ α⁻¹ e·σ e + ½ α e·σ*⁻¹ e − 1` (unit `e`). Route: `Ch02.responseJ_eq_ofAEEq` +
`Ch02.sigmaCoarse_eq_ofAEEq` + `Ch02.sigmaStarInvCoarse_eq_ofAEEq` transport everything across
`aux_core_chart_scalarCoeffOnData_AEEq` to the rescaled SCALAR data, where
`Ch02.responseSymmetricDirichletNeumannTheory` (fields `response_dirichlet_neumann_split`,
`dirichlet_value_by_sigma`, `neumann_value_by_sigmaStarInv`) gives `J(p,q) = ½p·σp + ½q·σ*⁻¹q − p·q`
with `p = (√α)⁻¹ • e`, `q = √α • e`. -/
theorem aux_core_probe_formula_R {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube w r hr))
    (R : Homogenization.TriadicCube d)
    (hR : Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0))
    (alpha : ℝ) (halpha : 0 < alpha) (e : Homogenization.Vec d)
    (he : Homogenization.vecNormSq e = 1) :
    SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbe R (I.chart w r hr a w r) alpha e =
      (1 / 2 : ℝ) * alpha⁻¹ * Homogenization.vecDot e (Homogenization.matVecMul
        (Homogenization.Book.Ch02.sigmaCoarse (Homogenization.Book.Ch02.cubeDomain R)
          ((I.chart w r hr a w r).coeffOn R)) e) +
      (1 / 2 : ℝ) * alpha * Homogenization.vecDot e (Homogenization.matVecMul
        (Homogenization.Book.Ch02.sigmaStarInvCoarse (Homogenization.Book.Ch02.cubeDomain R)
          ((I.chart w r hr a w r).coeffOn R)) e) - 1 := by
  set ha := aux_core_probe_formula_R_scalarCoeffOnData w hr a with ha'def
  have i0 : Fin d := ⟨0, by omega⟩
  have hQsub : Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0) :=
    hR
  set haQ := aux_core_scalarCoeffOnData_rescale w hr (U := Ch02.cubeDomain R)
    (S := Homogenization.openCubeSet R) (Ch02.cubeDomain_coe R)
    (Ch02.cubeDomain R).isOpen.measurableSet
    (hQsub.trans aux_core_openCubeSet_originCube_eq.le) ha i0 with haQdef
  have hAE : Ch02.CoeffOn.AEEq ((I.chart w r hr a w r).coeffOn R) haQ.toCoeffOn := by
    have h0 := aux_core_chart_scalarCoeffOnData_AEEq I w hr ha i0 R hR
    have hw : aux_core_wrapPC w r hr (a.val : Vec d → ℝ) = a := aux_core_wrapPC_eq w r hr a
    rw [hw] at h0
    exact h0
  unfold SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbe SubdiffusiveProcess.CoarseGrainingVocab.J
  rw [Ch02.responseJ_eq_ofAEEq hAE]
  rw [Ch02.sigmaCoarse_eq_ofAEEq hAE, Ch02.sigmaStarInvCoarse_eq_ofAEEq hAE]
  let T := Ch02.responseSymmetricDirichletNeumannTheory (Ch02.cubeDomain R) haQ.toCoeffOn haQ.isSymmetric
  rw [T.response_dirichlet_neumann_split ((Real.sqrt alpha)⁻¹ • e) (Real.sqrt alpha • e)]
  rw [T.dirichlet_value_by_sigma ((Real.sqrt alpha)⁻¹ • e)]
  rw [T.neumann_value_by_sigmaStarInv (Real.sqrt alpha • e)]
  have hsqrtpos : Real.sqrt alpha ≠ 0 := by
    exact Real.sqrt_ne_zero'.mpr halpha
  have hdot : Homogenization.vecDot ((Real.sqrt alpha)⁻¹ • e) (Real.sqrt alpha • e) = 1 := by
    calc
      Homogenization.vecDot ((Real.sqrt alpha)⁻¹ • e) (Real.sqrt alpha • e)
          = ((Real.sqrt alpha)⁻¹ * Real.sqrt alpha) * Homogenization.vecDot e e := by
        simp [Homogenization.vecDot_smul_left, Homogenization.vecDot_smul_right, mul_comm, mul_left_comm]
      _ = 1 * Homogenization.vecDot e e := by
        field_simp [hsqrtpos]
      _ = Homogenization.vecDot e e := by simp
      _ = Homogenization.vecNormSq e := rfl
      _ = 1 := he
  have hsq1 : ((Real.sqrt alpha)⁻¹)^2 = alpha⁻¹ := by
    have hsq : (Real.sqrt alpha)^2 = alpha := Real.sq_sqrt halpha.le
    field_simp [hsqrtpos]
    nlinarith
  have hsq2 : (Real.sqrt alpha)^2 = alpha := Real.sq_sqrt halpha.le
  have hdirichlet_smul : Homogenization.vecDot ((Real.sqrt alpha)⁻¹ • e)
      (Homogenization.matVecMul (Ch02.sigmaCoarse (Ch02.cubeDomain R) haQ.toCoeffOn) ((Real.sqrt alpha)⁻¹ • e)) =
      alpha⁻¹ * Homogenization.vecDot e (Homogenization.matVecMul (Ch02.sigmaCoarse (Ch02.cubeDomain R) haQ.toCoeffOn) e) := by
    calc
      Homogenization.vecDot ((Real.sqrt alpha)⁻¹ • e)
          (Homogenization.matVecMul (Ch02.sigmaCoarse (Ch02.cubeDomain R) haQ.toCoeffOn) ((Real.sqrt alpha)⁻¹ • e))
        = Homogenization.vecDot ((Real.sqrt alpha)⁻¹ • e)
            (((Real.sqrt alpha)⁻¹) • Homogenization.matVecMul (Ch02.sigmaCoarse (Ch02.cubeDomain R) haQ.toCoeffOn) e) := by
        rw [Homogenization.matVecMul_smul]
      _ = ((Real.sqrt alpha)⁻¹) * Homogenization.vecDot e
            (((Real.sqrt alpha)⁻¹) • Homogenization.matVecMul (Ch02.sigmaCoarse (Ch02.cubeDomain R) haQ.toCoeffOn) e) := by
        rw [Homogenization.vecDot_smul_left]
      _ = ((Real.sqrt alpha)⁻¹) * (((Real.sqrt alpha)⁻¹) * Homogenization.vecDot e
            (Homogenization.matVecMul (Ch02.sigmaCoarse (Ch02.cubeDomain R) haQ.toCoeffOn) e)) := by
        rw [Homogenization.vecDot_smul_right]
      _ = ((Real.sqrt alpha)⁻¹ * (Real.sqrt alpha)⁻¹) * Homogenization.vecDot e
            (Homogenization.matVecMul (Ch02.sigmaCoarse (Ch02.cubeDomain R) haQ.toCoeffOn) e) := by
        ring
      _ = alpha⁻¹ * Homogenization.vecDot e (Homogenization.matVecMul (Ch02.sigmaCoarse (Ch02.cubeDomain R) haQ.toCoeffOn) e) := by
        rw [← sq, hsq1]
  have hneumann_smul : Homogenization.vecDot (Real.sqrt alpha • e)
      (Homogenization.matVecMul (Ch02.sigmaStarInvCoarse (Ch02.cubeDomain R) haQ.toCoeffOn) (Real.sqrt alpha • e)) =
      alpha * Homogenization.vecDot e (Homogenization.matVecMul (Ch02.sigmaStarInvCoarse (Ch02.cubeDomain R) haQ.toCoeffOn) e) := by
    calc
      Homogenization.vecDot (Real.sqrt alpha • e)
          (Homogenization.matVecMul (Ch02.sigmaStarInvCoarse (Ch02.cubeDomain R) haQ.toCoeffOn) (Real.sqrt alpha • e))
        = Homogenization.vecDot (Real.sqrt alpha • e)
            ((Real.sqrt alpha) • Homogenization.matVecMul (Ch02.sigmaStarInvCoarse (Ch02.cubeDomain R) haQ.toCoeffOn) e) := by
        rw [Homogenization.matVecMul_smul]
      _ = Real.sqrt alpha * Homogenization.vecDot e
            ((Real.sqrt alpha) • Homogenization.matVecMul (Ch02.sigmaStarInvCoarse (Ch02.cubeDomain R) haQ.toCoeffOn) e) := by
        rw [Homogenization.vecDot_smul_left]
      _ = Real.sqrt alpha * (Real.sqrt alpha * Homogenization.vecDot e
            (Homogenization.matVecMul (Ch02.sigmaStarInvCoarse (Ch02.cubeDomain R) haQ.toCoeffOn) e)) := by
        rw [Homogenization.vecDot_smul_right]
      _ = (Real.sqrt alpha * Real.sqrt alpha) * Homogenization.vecDot e
            (Homogenization.matVecMul (Ch02.sigmaStarInvCoarse (Ch02.cubeDomain R) haQ.toCoeffOn) e) := by
        ring
      _ = alpha * Homogenization.vecDot e (Homogenization.matVecMul (Ch02.sigmaStarInvCoarse (Ch02.cubeDomain R) haQ.toCoeffOn) e) := by
        rw [← sq, hsq2]
  rw [hdot, hdirichlet_smul, hneumann_smul]
  ring

/-- **`σ = b` on a descendant** for the chart family (symmetric scalar data, transported by
`Ch02.sigmaCoarse_eq_ofAEEq` / `Ch02.bCoarse_eq_ofAEEq` across
`aux_core_chart_scalarCoeffOnData_AEEq`; `derived_matrices.2.2` of the symmetric theory). -/
theorem aux_core_sigmaCoarse_eq_bCoarse_R {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube w r hr))
    (R : Homogenization.TriadicCube d)
    (hR : Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0)) :
    Homogenization.Book.Ch02.sigmaCoarse (Homogenization.Book.Ch02.cubeDomain R)
        ((I.chart w r hr a w r).coeffOn R) =
      Homogenization.Book.Ch02.bCoarse (Homogenization.Book.Ch02.cubeDomain R)
        ((I.chart w r hr a w r).coeffOn R) := by
  set ha := aux_core_probe_formula_R_scalarCoeffOnData w hr a with ha'def
  have i0 : Fin d := ⟨0, by omega⟩
  have hQsub : Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0) :=
    hR
  set haQ := aux_core_scalarCoeffOnData_rescale w hr (U := Ch02.cubeDomain R)
    (S := Homogenization.openCubeSet R) (Ch02.cubeDomain_coe R)
    (Ch02.cubeDomain R).isOpen.measurableSet
    (hQsub.trans aux_core_openCubeSet_originCube_eq.le) ha i0 with haQdef
  have hAE : Ch02.CoeffOn.AEEq ((I.chart w r hr a w r).coeffOn R) haQ.toCoeffOn := by
    have h0 := aux_core_chart_scalarCoeffOnData_AEEq I w hr ha i0 R hR
    have hw : aux_core_wrapPC w r hr (a.val : Vec d → ℝ) = a := aux_core_wrapPC_eq w r hr a
    rw [hw] at h0
    exact h0
  rw [Ch02.sigmaCoarse_eq_ofAEEq hAE, Ch02.bCoarse_eq_ofAEEq hAE]
  exact ((Ch02.responseSymmetricDirichletNeumannTheory (Ch02.cubeDomain R) haQ.toCoeffOn haQ.isSymmetric).derived_matrices.2.2).symm



/-- `Measurable H` variant (`hH` was only used as `hH.1`), for the
`Hused = 0` branch of lem_finite_good_cell's good event. -/
theorem aux_lem_band_piece_coords_value_measurable_aN_meas_gen
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hHm : Measurable H)
    (N : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    [MeasurableSpace (Lp ℝ ∞ (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))]
    [BorelSpace (Lp ℝ ∞ (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))] :
    Measurable (fun omega : BilateralField d =>
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr).val) := by
  let Om : Opens (SpatialCoordinates d) := centeredCube z r hr
  let K : Compacts (SpatialCoordinates d) := closedCube z r hr
  have : Fact ((Om : Set (SpatialCoordinates d)) ⊆ (K : Set (SpatialCoordinates d))) :=
    ⟨centeredCube_subset_closedCube z hr⟩
  let : MeasurableSpace C(K, ℝ) := borel _
  let : BorelSpace C(K, ℝ) := ⟨rfl⟩
  have hHmeas : Measurable H := hHm
  -- Build the log-potential as a C(K, ℝ)-valued measurable function
  have hlogpot : Measurable (fun omega : BilateralField d =>
      (H omega).restrict (K : Set (SpatialCoordinates d)) +
      (∑ j ∈ Finset.range (N + 1), (omega (-(Int.ofNat j))).restrict (K : Set (SpatialCoordinates d))) -
      ContinuousMap.const K ((N + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) +
      ContinuousMap.const K (Real.log ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹))) := by
    have hHrestrict : Measurable (fun omega : BilateralField d =>
        (H omega).restrict (K : Set (SpatialCoordinates d))) :=
      (ContinuousMap.continuous_restrict (K : Set (SpatialCoordinates d))).measurable.comp hHmeas
    have hsum : Measurable (fun omega : BilateralField d =>
        ∑ j ∈ Finset.range (N + 1), (omega (-(Int.ofNat j))).restrict (K : Set (SpatialCoordinates d))) := by
      refine Finset.measurable_sum _ ?_
      intro j hj
      exact (ContinuousMap.continuous_restrict (K : Set (SpatialCoordinates d))).measurable.comp
        (measurable_pi_apply _)
    exact ((hHrestrict.add hsum).sub measurable_const).add measurable_const
  -- Lift to Lp∞ via compactPotentialToLp
  have hload : Measurable (fun omega : BilateralField d =>
      compactPotentialToLp (Ω := Om) K
        ((H omega).restrict (K : Set (SpatialCoordinates d)) +
        (∑ j ∈ Finset.range (N + 1), (omega (-(Int.ofNat j))).restrict (K : Set (SpatialCoordinates d))) -
        ContinuousMap.const K ((N + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) +
        ContinuousMap.const K (Real.log ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹)))) :=
    (compactPotentialToLp (Ω := Om) K).continuous.measurable.comp hlogpot
  -- Key lemma: for f : C(K, ℝ), (expPotentialCoefficient (compactPotentialToLp K f)).val
  -- = compactPotentialToLp K (Real.exp ∘ f)
  have h_exp_val_eq (f : C(K, ℝ)) :
      (expPotentialCoefficient (compactPotentialToLp (Ω := Om) K f)).val =
      compactPotentialToLp (Ω := Om) K
        (⟨Real.exp ∘ f, Real.continuous_exp.comp f.continuous⟩ : C(K, ℝ)) := by
    apply Lp.ext
    filter_upwards [
      expPotentialCoefficient_coeFn (compactPotentialToLp (Ω := Om) K f),
      compactPotentialToLp_on_domain (Ω := Om) K f,
      compactPotentialToLp_on_domain (Ω := Om) K
        (⟨Real.exp ∘ f, Real.continuous_exp.comp f.continuous⟩ : C(K, ℝ)),
      ae_restrict_mem Om.isOpen.measurableSet] with x hexp hroot hroot_exp xhx
    rw [hexp, hroot xhx, hroot_exp xhx]
    simp
  -- Equality of the PositiveCoefficient elements (following lem_neumann_error_volume_measurable)
  have hcoef_eq : ∀ omega : BilateralField d,
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr) =
      expPotentialCoefficient (compactPotentialToLp (Ω := Om) K
        ((H omega).restrict (K : Set (SpatialCoordinates d)) +
        (∑ j ∈ Finset.range (N + 1), (omega (-(Int.ofNat j))).restrict (K : Set (SpatialCoordinates d))) -
        ContinuousMap.const K ((N + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) +
        ContinuousMap.const K (Real.log ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹)))) := by
    intro omega
    unfold _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient SubdiffusiveProcess.normalizedContinuousPositiveCoefficient
    rw [aux_lem_neumann_error_volume_measurable_log_eq M H omega N z hr]
    simp only [Real.log_one, ContinuousMap.const_zero, sub_zero]
    apply congrArg (fun q : Lp ℝ ∞
      (volume.restrict (Om : Set (SpatialCoordinates d))) =>
      expPotentialCoefficient q)
    rfl
  -- The function f ↦ Real.exp ∘ f is continuous on C(K, ℝ)
  have h_cexp_cont : Continuous (fun (f : C(K, ℝ)) =>
      (⟨Real.exp ∘ f, Real.continuous_exp.comp f.continuous⟩ : C(K, ℝ))) := by
    have h := ContinuousMap.continuous_comp' (X := K) (Y := ℝ) (Z := ℝ)
    have hconst : Continuous (fun (_ : C(K, ℝ)) => (⟨Real.exp, Real.continuous_exp⟩ : C(ℝ, ℝ))) :=
      continuous_const
    refine h.comp (continuous_id.prodMk hconst)
  -- Real.exp ∘ logpotential is measurable into C(K, ℝ)
  set logpotential' : BilateralField d → C(K, ℝ) := fun omega =>
    (H omega).restrict (K : Set (SpatialCoordinates d)) +
    (∑ j ∈ Finset.range (N + 1), (omega (-(Int.ofNat j))).restrict (K : Set (SpatialCoordinates d))) -
    ContinuousMap.const K ((N + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) +
    ContinuousMap.const K (Real.log ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹))
  with hlogpotential'_def
  have hlogpot'_meas : Measurable logpotential' := hlogpot
  let hlogpot_exp_val (omega : BilateralField d) : C(K, ℝ) :=
    ⟨Real.exp ∘ logpotential' omega, Real.continuous_exp.comp (logpotential' omega).continuous⟩
  have hlogpot_exp : Measurable (fun omega : BilateralField d => hlogpot_exp_val omega) := by
    simpa [hlogpot_exp_val] using! h_cexp_cont.measurable.comp hlogpot'_meas
  -- Lift to Lp∞ via compactPotentialToLp
  have hload_exp : Measurable (fun omega : BilateralField d =>
      compactPotentialToLp (Ω := Om) K (hlogpot_exp_val omega)) :=
    (compactPotentialToLp (Ω := Om) K).continuous.measurable.comp hlogpot_exp
  -- Combine: (cutoffPositiveCoefficient...).val = compactPotentialToLp K (Real.exp ∘ logpotential)
  have h_fun_eq : (fun omega : BilateralField d =>
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr).val) =
    (fun omega : BilateralField d =>
      compactPotentialToLp (Ω := Om) K (hlogpot_exp_val omega)) := by
    funext omega
    calc
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr).val
          = (expPotentialCoefficient (compactPotentialToLp (Ω := Om) K
              (logpotential' omega))).val := by
        rw [hcoef_eq omega, hlogpotential'_def]
      _ = compactPotentialToLp (Ω := Om) K
          (⟨Real.exp ∘ logpotential' omega, Real.continuous_exp.comp (logpotential' omega).continuous⟩) := by
        rw [h_exp_val_eq (logpotential' omega), hlogpotential'_def]
      _ = compactPotentialToLp (Ω := Om) K (hlogpot_exp_val omega) := by
        dsimp [hlogpot_exp_val]
  rw [h_fun_eq]
  exact hload_exp

/-- `Measurable H` variant (`hH` was only used as `hH.1`), for the
`Hused = 0` branch of lem_finite_good_cell's good event. -/
theorem aux_core_sigmaCoarse_measurable_HOLE_gen {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hHm : Measurable H)
    (N : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (i j : Fin d) :
    Measurable (fun omega : BilateralField d =>
      Homogenization.Book.Ch02.sigmaCoarse
        (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
        ((I.chart w r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w r).coeffOn
          (Homogenization.originCube d 0)) i j) := by
  let : MeasurableSpace (Lp ℝ ∞ (volume.restrict (centeredCube w r hr : Set (Vec d)))) :=
    borel _
  have : BorelSpace (Lp ℝ ∞ (volume.restrict (centeredCube w r hr : Set (Vec d)))) :=
    ⟨rfl⟩
  let : MeasurableSpace (Lp ℝ ∞ (volumeMeasureOn (aux_core_outerDomain w r hr : Set (Vec d)))) :=
    ‹MeasurableSpace (Lp ℝ ∞ (volume.restrict (centeredCube w r hr : Set (Vec d))))›
  have : BorelSpace (Lp ℝ ∞ (volumeMeasureOn (aux_core_outerDomain w r hr : Set (Vec d)))) :=
    ‹BorelSpace (Lp ℝ ∞ (volume.restrict (centeredCube w r hr : Set (Vec d))))›
  have i0 : Fin d := ⟨0, by omega⟩
  set Q := Homogenization.originCube d 0 with hQdef
  have hg : Measurable (fun omega : BilateralField d =>
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr).val) :=
    aux_lem_band_piece_coords_value_measurable_aN_meas_gen M H hHm N w r hr
  set F : (Vec d → ℝ) → ℝ := fun a =>
    Ch02.sigmaCoarse (Ch02.cubeDomain Q) ((I.chart w r hr (aux_core_wrapPC w r hr a) w r).coeffOn Q) i j
    with hFdef
  have hFeq : (fun omega : BilateralField d => F (fun x => (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr).val x))
      = (fun omega : BilateralField d =>
          Homogenization.Book.Ch02.sigmaCoarse (Homogenization.Book.Ch02.cubeDomain Q)
            ((I.chart w r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w r).coeffOn Q) i j) := by
    funext omega
    simp only [hFdef, aux_core_wrapPC_eq]
  rw [← hFeq]
  apply aux_continuity_measurable_of_local_ratio_continuous (U := aux_core_outerDomain w r hr) _ hg
    (c := fun omega => (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr).property.choose)
    (fun omega => (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr).property.choose_spec.1)
    (fun omega => by
      have := (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr).property.choose_spec.2
      simpa [aux_core_outerDomain_coe] using this)
    F
  intro a ha η hη
  have hQsub : Homogenization.openCubeSet Q ⊆ Homogenization.openCubeSet Q := Set.Subset.rfl
  set haQ := aux_core_scalarCoeffOnData_rescale w hr (U := Ch02.cubeDomain Q)
    (S := Homogenization.openCubeSet Q) (Ch02.cubeDomain_coe Q)
    (Ch02.cubeDomain Q).isOpen.measurableSet
    (hQsub.trans (aux_core_openCubeSet_originCube_eq.le))
    (a := a) ha i0 with haQdef
  set Ca : ℝ := Ch02.responseJ (Ch02.cubeDomain Q) haQ.toCoeffOn (Pi.single i 1) 0 +
    Ch02.responseJ (Ch02.cubeDomain Q) haQ.toCoeffOn (Pi.single j 1) 0 +
    Ch02.responseJ (Ch02.cubeDomain Q) haQ.toCoeffOn (Pi.single i 1 + Pi.single j 1) 0 with hCadef
  obtain ⟨ε, hεpos, hεlog2, hεbound⟩ := aux_core_eps_of_linear 168 Ca η (by norm_num) (by
    rw [hCadef]
    have h1 := Ch02.responseJ_nonneg (Ch02.cubeDomain Q) haQ.toCoeffOn (Pi.single i 1) 0
    have h2 := Ch02.responseJ_nonneg (Ch02.cubeDomain Q) haQ.toCoeffOn (Pi.single j 1) 0
    have h3 := Ch02.responseJ_nonneg (Ch02.cubeDomain Q) haQ.toCoeffOn
      (Pi.single i 1 + Pi.single j 1) 0
    linarith) hη
  refine ⟨ε, hεpos, hεlog2, ?_⟩
  intro b hb hupper hlower
  set hbQ := aux_core_scalarCoeffOnData_rescale w hr (U := Ch02.cubeDomain Q)
    (S := Homogenization.openCubeSet Q) (Ch02.cubeDomain_coe Q)
    (Ch02.cubeDomain Q).isOpen.measurableSet
    (hQsub.trans (aux_core_openCubeSet_originCube_eq.le))
    (a := b) hb i0 with hbQdef
  have hupper' : ∀ᵐ x ∂ volumeMeasureOn (Homogenization.openCubeSet Q), b (fun i => w i + r * x i) ≤
      Real.exp ε * a (fun i => w i + r * x i) := by
    have := aux_core_ae_pullback w hr (S := Homogenization.openCubeSet Q)
      (Ch02.cubeDomain Q).isOpen.measurableSet (hQsub.trans (aux_core_openCubeSet_originCube_eq.le))
      (p := fun y => b y ≤ Real.exp ε * a y) hupper
    simpa [volumeMeasureOn] using! this
  have hlower' : ∀ᵐ x ∂ volumeMeasureOn (Homogenization.openCubeSet Q),
      Real.exp (-ε) * a (fun i => w i + r * x i) ≤ b (fun i => w i + r * x i) := by
    have := aux_core_ae_pullback w hr (S := Homogenization.openCubeSet Q)
      (Ch02.cubeDomain Q).isOpen.measurableSet (hQsub.trans (aux_core_openCubeSet_originCube_eq.le))
      (p := fun y => Real.exp (-ε) * a y ≤ b y) hlower
    simpa [volumeMeasureOn] using! this
  have hFa : F a = Ch02.sigmaCoarse (Ch02.cubeDomain Q) haQ.toCoeffOn i j := by
    simp only [hFdef]
    rw [haQdef]
    exact congrFun (congrFun (Ch02.sigmaCoarse_eq_ofAEEq (aux_core_chart_scalarCoeffOnData_AEEq I w hr (a := a)
      ha i0 Q hQsub)) i) j
  have hFb : F b = Ch02.sigmaCoarse (Ch02.cubeDomain Q) hbQ.toCoeffOn i j := by
    simp only [hFdef]
    rw [hbQdef]
    exact congrFun (congrFun (Ch02.sigmaCoarse_eq_ofAEEq (aux_core_chart_scalarCoeffOnData_AEEq I w hr (a := b)
      hb i0 Q hQsub)) i) j
  rw [hFa, hFb]
  calc |Ch02.sigmaCoarse (Ch02.cubeDomain Q) hbQ.toCoeffOn i j -
        Ch02.sigmaCoarse (Ch02.cubeDomain Q) haQ.toCoeffOn i j| ≤
      168 * (Real.exp ε - 1) * Ca :=
        aux_continuity_sigmaCoarse_entry_ratio haQ hbQ hεpos hεlog2 hupper' hlower' i j
    _ ≤ η := hεbound

/-- `Measurable H` variant (`hH` was only used as `hH.1`), for the
`Hused = 0` branch of lem_finite_good_cell's good event. -/
theorem aux_core_sigmaStarInvCoarse_measurable_HOLE_gen {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hHm : Measurable H)
    (N : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (i j : Fin d) :
    Measurable (fun omega : BilateralField d =>
      Homogenization.Book.Ch02.sigmaStarInvCoarse
        (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
        ((I.chart w r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w r).coeffOn
          (Homogenization.originCube d 0)) i j) := by
  let : MeasurableSpace (Lp ℝ ∞ (volume.restrict (centeredCube w r hr : Set (Vec d)))) :=
    borel _
  have : BorelSpace (Lp ℝ ∞ (volume.restrict (centeredCube w r hr : Set (Vec d)))) :=
    ⟨rfl⟩
  let : MeasurableSpace (Lp ℝ ∞ (volumeMeasureOn (aux_core_outerDomain w r hr : Set (Vec d)))) :=
    ‹MeasurableSpace (Lp ℝ ∞ (volume.restrict (centeredCube w r hr : Set (Vec d))))›
  have : BorelSpace (Lp ℝ ∞ (volumeMeasureOn (aux_core_outerDomain w r hr : Set (Vec d)))) :=
    ‹BorelSpace (Lp ℝ ∞ (volume.restrict (centeredCube w r hr : Set (Vec d))))›
  have i0 : Fin d := ⟨0, by omega⟩
  set Q := Homogenization.originCube d 0 with hQdef
  have hg : Measurable (fun omega : BilateralField d =>
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr).val) :=
    aux_lem_band_piece_coords_value_measurable_aN_meas_gen M H hHm N w r hr
  set F : (Vec d → ℝ) → ℝ := fun a =>
    Ch02.sigmaStarInvCoarse (Ch02.cubeDomain Q) ((I.chart w r hr (aux_core_wrapPC w r hr a) w r).coeffOn Q) i j
    with hFdef
  have hFeq : (fun omega : BilateralField d => F (fun x => (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr).val x))
      = (fun omega : BilateralField d =>
          Homogenization.Book.Ch02.sigmaStarInvCoarse (Homogenization.Book.Ch02.cubeDomain Q)
            ((I.chart w r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w r).coeffOn Q) i j) := by
    funext omega
    simp only [hFdef, aux_core_wrapPC_eq]
  rw [← hFeq]
  apply aux_continuity_measurable_of_local_ratio_continuous (U := aux_core_outerDomain w r hr) _ hg
    (c := fun omega => (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr).property.choose)
    (fun omega => (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr).property.choose_spec.1)
    (fun omega => by
      have := (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr).property.choose_spec.2
      simpa [aux_core_outerDomain_coe] using this)
    F
  intro a ha η hη
  have hQsub : Homogenization.openCubeSet Q ⊆ Homogenization.openCubeSet Q := Set.Subset.rfl
  set haQ := aux_core_scalarCoeffOnData_rescale w hr (U := Ch02.cubeDomain Q)
    (S := Homogenization.openCubeSet Q) (Ch02.cubeDomain_coe Q)
    (Ch02.cubeDomain Q).isOpen.measurableSet
    (hQsub.trans (aux_core_openCubeSet_originCube_eq.le))
    (a := a) ha i0 with haQdef
  set Ca : ℝ := Ch02.responseJ (Ch02.cubeDomain Q) haQ.toCoeffOn 0 (Pi.single i 1) +
    Ch02.responseJ (Ch02.cubeDomain Q) haQ.toCoeffOn 0 (Pi.single j 1) +
    Ch02.responseJ (Ch02.cubeDomain Q) haQ.toCoeffOn 0 (Pi.single i 1 + Pi.single j 1) with hCadef
  obtain ⟨ε, hεpos, hεlog2, hεbound⟩ := aux_core_eps_of_linear 168 Ca η (by norm_num) (by
    rw [hCadef]
    have h1 := Ch02.responseJ_nonneg (Ch02.cubeDomain Q) haQ.toCoeffOn 0 (Pi.single i 1)
    have h2 := Ch02.responseJ_nonneg (Ch02.cubeDomain Q) haQ.toCoeffOn 0 (Pi.single j 1)
    have h3 := Ch02.responseJ_nonneg (Ch02.cubeDomain Q) haQ.toCoeffOn
      0 (Pi.single i 1 + Pi.single j 1)
    linarith) hη
  refine ⟨ε, hεpos, hεlog2, ?_⟩
  intro b hb hupper hlower
  set hbQ := aux_core_scalarCoeffOnData_rescale w hr (U := Ch02.cubeDomain Q)
    (S := Homogenization.openCubeSet Q) (Ch02.cubeDomain_coe Q)
    (Ch02.cubeDomain Q).isOpen.measurableSet
    (hQsub.trans (aux_core_openCubeSet_originCube_eq.le))
    (a := b) hb i0 with hbQdef
  have hupper' : ∀ᵐ x ∂ volumeMeasureOn (Homogenization.openCubeSet Q), b (fun i => w i + r * x i) ≤
      Real.exp ε * a (fun i => w i + r * x i) := by
    have := aux_core_ae_pullback w hr (S := Homogenization.openCubeSet Q)
      (Ch02.cubeDomain Q).isOpen.measurableSet (hQsub.trans (aux_core_openCubeSet_originCube_eq.le))
      (p := fun y => b y ≤ Real.exp ε * a y) hupper
    simpa [volumeMeasureOn] using! this
  have hlower' : ∀ᵐ x ∂ volumeMeasureOn (Homogenization.openCubeSet Q),
      Real.exp (-ε) * a (fun i => w i + r * x i) ≤ b (fun i => w i + r * x i) := by
    have := aux_core_ae_pullback w hr (S := Homogenization.openCubeSet Q)
      (Ch02.cubeDomain Q).isOpen.measurableSet (hQsub.trans (aux_core_openCubeSet_originCube_eq.le))
      (p := fun y => Real.exp (-ε) * a y ≤ b y) hlower
    simpa [volumeMeasureOn] using! this
  have hFa : F a = Ch02.sigmaStarInvCoarse (Ch02.cubeDomain Q) haQ.toCoeffOn i j := by
    simp only [hFdef]
    rw [haQdef]
    exact congrFun (congrFun (Ch02.sigmaStarInvCoarse_eq_ofAEEq (aux_core_chart_scalarCoeffOnData_AEEq I w hr (a := a)
      ha i0 Q hQsub)) i) j
  have hFb : F b = Ch02.sigmaStarInvCoarse (Ch02.cubeDomain Q) hbQ.toCoeffOn i j := by
    simp only [hFdef]
    rw [hbQdef]
    exact congrFun (congrFun (Ch02.sigmaStarInvCoarse_eq_ofAEEq (aux_core_chart_scalarCoeffOnData_AEEq I w hr (a := b)
      hb i0 Q hQsub)) i) j
  rw [hFa, hFb]
  calc |Ch02.sigmaStarInvCoarse (Ch02.cubeDomain Q) hbQ.toCoeffOn i j -
        Ch02.sigmaStarInvCoarse (Ch02.cubeDomain Q) haQ.toCoeffOn i j| ≤
      168 * (Real.exp ε - 1) * Ca :=
        aux_continuity_sigmaStarInvEntry haQ hbQ hεpos hεlog2 hupper' hlower' i j
    _ ≤ η := hεbound

/-- `Measurable H` variant (`hH` was only used as `hH.1`), for the
`Hused = 0` branch of lem_finite_good_cell's good event. -/
theorem aux_core_sigmaStarInvCoarse_measurable_R_gen {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hHm : Measurable H)
    (N : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (R : Homogenization.TriadicCube d)
    (hR : Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0))
    (i j : Fin d) :
    Measurable (fun omega : BilateralField d =>
      Homogenization.Book.Ch02.sigmaStarInvCoarse
        (Homogenization.Book.Ch02.cubeDomain R)
        ((I.chart w r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w r).coeffOn R) i j) := by
  let : MeasurableSpace (Lp ℝ ∞ (volume.restrict (centeredCube w r hr : Set (Vec d)))) :=
    borel _
  have : BorelSpace (Lp ℝ ∞ (volume.restrict (centeredCube w r hr : Set (Vec d)))) :=
    ⟨rfl⟩
  let : MeasurableSpace (Lp ℝ ∞ (volumeMeasureOn (aux_core_outerDomain w r hr : Set (Vec d)))) :=
    ‹MeasurableSpace (Lp ℝ ∞ (volume.restrict (centeredCube w r hr : Set (Vec d))))›
  have : BorelSpace (Lp ℝ ∞ (volumeMeasureOn (aux_core_outerDomain w r hr : Set (Vec d)))) :=
    ‹BorelSpace (Lp ℝ ∞ (volume.restrict (centeredCube w r hr : Set (Vec d))))›
  have i0 : Fin d := ⟨0, by omega⟩
  have hg : Measurable (fun omega : BilateralField d =>
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr).val) :=
    aux_lem_band_piece_coords_value_measurable_aN_meas_gen M H hHm N w r hr
  set F : (Vec d → ℝ) → ℝ := fun a =>
    Ch02.sigmaStarInvCoarse (Ch02.cubeDomain R) ((I.chart w r hr (aux_core_wrapPC w r hr a) w r).coeffOn R) i j
    with hFdef
  have hFeq : (fun omega : BilateralField d => F (fun x => (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr).val x))
      = (fun omega : BilateralField d =>
          Homogenization.Book.Ch02.sigmaStarInvCoarse (Homogenization.Book.Ch02.cubeDomain R)
            ((I.chart w r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w r).coeffOn R) i j) := by
    funext omega
    simp only [hFdef, aux_core_wrapPC_eq]
  rw [← hFeq]
  apply aux_continuity_measurable_of_local_ratio_continuous (U := aux_core_outerDomain w r hr) _ hg
    (c := fun omega => (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr).property.choose)
    (fun omega => (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr).property.choose_spec.1)
    (fun omega => by
      have := (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr).property.choose_spec.2
      simpa [aux_core_outerDomain_coe] using this)
    F
  intro a ha η hη
  set haQ := aux_core_scalarCoeffOnData_rescale w hr (U := Ch02.cubeDomain R)
    (S := Homogenization.openCubeSet R) (Ch02.cubeDomain_coe R)
    (Ch02.cubeDomain R).isOpen.measurableSet
    (hR.trans (aux_core_openCubeSet_originCube_eq.le))
    (a := a) ha i0 with haQdef
  set Ca : ℝ := Ch02.responseJ (Ch02.cubeDomain R) haQ.toCoeffOn 0 (Pi.single i 1) +
    Ch02.responseJ (Ch02.cubeDomain R) haQ.toCoeffOn 0 (Pi.single j 1) +
    Ch02.responseJ (Ch02.cubeDomain R) haQ.toCoeffOn 0 (Pi.single i 1 + Pi.single j 1) with hCadef
  obtain ⟨ε, hεpos, hεlog2, hεbound⟩ := aux_core_eps_of_linear 168 Ca η (by norm_num) (by
    rw [hCadef]
    have h1 := Ch02.responseJ_nonneg (Ch02.cubeDomain R) haQ.toCoeffOn 0 (Pi.single i 1)
    have h2 := Ch02.responseJ_nonneg (Ch02.cubeDomain R) haQ.toCoeffOn 0 (Pi.single j 1)
    have h3 := Ch02.responseJ_nonneg (Ch02.cubeDomain R) haQ.toCoeffOn
      0 (Pi.single i 1 + Pi.single j 1)
    linarith) hη
  refine ⟨ε, hεpos, hεlog2, ?_⟩
  intro b hb hupper hlower
  set hbQ := aux_core_scalarCoeffOnData_rescale w hr (U := Ch02.cubeDomain R)
    (S := Homogenization.openCubeSet R) (Ch02.cubeDomain_coe R)
    (Ch02.cubeDomain R).isOpen.measurableSet
    (hR.trans (aux_core_openCubeSet_originCube_eq.le))
    (a := b) hb i0 with hbQdef
  have hupper' : ∀ᵐ x ∂ volumeMeasureOn (Homogenization.openCubeSet R), b (fun i => w i + r * x i) ≤
      Real.exp ε * a (fun i => w i + r * x i) := by
    have := aux_core_ae_pullback w hr (S := Homogenization.openCubeSet R)
      (Ch02.cubeDomain R).isOpen.measurableSet (hR.trans (aux_core_openCubeSet_originCube_eq.le))
      (p := fun y => b y ≤ Real.exp ε * a y) hupper
    simpa [volumeMeasureOn] using! this
  have hlower' : ∀ᵐ x ∂ volumeMeasureOn (Homogenization.openCubeSet R),
      Real.exp (-ε) * a (fun i => w i + r * x i) ≤ b (fun i => w i + r * x i) := by
    have := aux_core_ae_pullback w hr (S := Homogenization.openCubeSet R)
      (Ch02.cubeDomain R).isOpen.measurableSet (hR.trans (aux_core_openCubeSet_originCube_eq.le))
      (p := fun y => Real.exp (-ε) * a y ≤ b y) hlower
    simpa [volumeMeasureOn] using! this
  have hFa : F a = Ch02.sigmaStarInvCoarse (Ch02.cubeDomain R) haQ.toCoeffOn i j := by
    simp only [hFdef]
    rw [haQdef]
    exact congrFun (congrFun (Ch02.sigmaStarInvCoarse_eq_ofAEEq (aux_core_chart_scalarCoeffOnData_AEEq I w hr (a := a)
      ha i0 R hR)) i) j
  have hFb : F b = Ch02.sigmaStarInvCoarse (Ch02.cubeDomain R) hbQ.toCoeffOn i j := by
    simp only [hFdef]
    rw [hbQdef]
    exact congrFun (congrFun (Ch02.sigmaStarInvCoarse_eq_ofAEEq (aux_core_chart_scalarCoeffOnData_AEEq I w hr (a := b)
      hb i0 R hR)) i) j
  rw [hFa, hFb]
  calc |Ch02.sigmaStarInvCoarse (Ch02.cubeDomain R) hbQ.toCoeffOn i j -
        Ch02.sigmaStarInvCoarse (Ch02.cubeDomain R) haQ.toCoeffOn i j| ≤
      168 * (Real.exp ε - 1) * Ca :=
        aux_continuity_sigmaStarInvEntry haQ hbQ hεpos hεlog2 hupper' hlower' i j
    _ ≤ η := hεbound

/-- `Measurable H` variant (`hH` was only used as `hH.1`), for the
`Hused = 0` branch of lem_finite_good_cell's good event. -/
theorem aux_core_bCoarse_measurable_R_gen {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hHm : Measurable H)
    (N : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (R : Homogenization.TriadicCube d)
    (hR : Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0))
    (i j : Fin d) :
    Measurable (fun omega : BilateralField d =>
      Homogenization.Book.Ch02.bCoarse
        (Homogenization.Book.Ch02.cubeDomain R)
        ((I.chart w r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w r).coeffOn R) i j) := by
  let : MeasurableSpace (Lp ℝ ∞ (volume.restrict (centeredCube w r hr : Set (Vec d)))) :=
    borel _
  have : BorelSpace (Lp ℝ ∞ (volume.restrict (centeredCube w r hr : Set (Vec d)))) :=
    ⟨rfl⟩
  let : MeasurableSpace (Lp ℝ ∞ (volumeMeasureOn (aux_core_outerDomain w r hr : Set (Vec d)))) :=
    ‹MeasurableSpace (Lp ℝ ∞ (volume.restrict (centeredCube w r hr : Set (Vec d))))›
  have : BorelSpace (Lp ℝ ∞ (volumeMeasureOn (aux_core_outerDomain w r hr : Set (Vec d)))) :=
    ‹BorelSpace (Lp ℝ ∞ (volume.restrict (centeredCube w r hr : Set (Vec d))))›
  have i0 : Fin d := ⟨0, by omega⟩
  have hg : Measurable (fun omega : BilateralField d =>
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr).val) :=
    aux_lem_band_piece_coords_value_measurable_aN_meas_gen M H hHm N w r hr
  set F : (Vec d → ℝ) → ℝ := fun a =>
    Ch02.bCoarse (Ch02.cubeDomain R) ((I.chart w r hr (aux_core_wrapPC w r hr a) w r).coeffOn R) i j
    with hFdef
  have hFeq : (fun omega : BilateralField d => F (fun x => (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr).val x))
      = (fun omega : BilateralField d =>
          Homogenization.Book.Ch02.bCoarse (Homogenization.Book.Ch02.cubeDomain R)
            ((I.chart w r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w r).coeffOn R) i j) := by
    funext omega
    simp only [hFdef, aux_core_wrapPC_eq]
  rw [← hFeq]
  apply aux_continuity_measurable_of_local_ratio_continuous (U := aux_core_outerDomain w r hr) _ hg
    (c := fun omega => (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr).property.choose)
    (fun omega => (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr).property.choose_spec.1)
    (fun omega => by
      have := (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr).property.choose_spec.2
      simpa [aux_core_outerDomain_coe] using this)
    F
  intro a ha η hη
  set haQ := aux_core_scalarCoeffOnData_rescale w hr (U := Ch02.cubeDomain R)
    (S := Homogenization.openCubeSet R) (Ch02.cubeDomain_coe R)
    (Ch02.cubeDomain R).isOpen.measurableSet
    (hR.trans (aux_core_openCubeSet_originCube_eq.le))
    (a := a) ha i0 with haQdef
  set Ca : ℝ := Ch02.responseJ (Ch02.cubeDomain R) haQ.toCoeffOn (Pi.single i 1) 0 +
    Ch02.responseJ (Ch02.cubeDomain R) haQ.toCoeffOn (Pi.single j 1) 0 +
    Ch02.responseJ (Ch02.cubeDomain R) haQ.toCoeffOn (Pi.single i 1 + Pi.single j 1) 0 with hCadef
  obtain ⟨ε, hεpos, hεlog2, hεbound⟩ := aux_core_eps_of_linear 168 Ca η (by norm_num) (by
    rw [hCadef]
    have h1 := Ch02.responseJ_nonneg (Ch02.cubeDomain R) haQ.toCoeffOn (Pi.single i 1) 0
    have h2 := Ch02.responseJ_nonneg (Ch02.cubeDomain R) haQ.toCoeffOn (Pi.single j 1) 0
    have h3 := Ch02.responseJ_nonneg (Ch02.cubeDomain R) haQ.toCoeffOn
      (Pi.single i 1 + Pi.single j 1) 0
    linarith) hη
  refine ⟨ε, hεpos, hεlog2, ?_⟩
  intro b hb hupper hlower
  set hbQ := aux_core_scalarCoeffOnData_rescale w hr (U := Ch02.cubeDomain R)
    (S := Homogenization.openCubeSet R) (Ch02.cubeDomain_coe R)
    (Ch02.cubeDomain R).isOpen.measurableSet
    (hR.trans (aux_core_openCubeSet_originCube_eq.le))
    (a := b) hb i0 with hbQdef
  have hupper' : ∀ᵐ x ∂ volumeMeasureOn (Homogenization.openCubeSet R), b (fun i => w i + r * x i) ≤
      Real.exp ε * a (fun i => w i + r * x i) := by
    have := aux_core_ae_pullback w hr (S := Homogenization.openCubeSet R)
      (Ch02.cubeDomain R).isOpen.measurableSet (hR.trans (aux_core_openCubeSet_originCube_eq.le))
      (p := fun y => b y ≤ Real.exp ε * a y) hupper
    simpa [volumeMeasureOn] using! this
  have hlower' : ∀ᵐ x ∂ volumeMeasureOn (Homogenization.openCubeSet R),
      Real.exp (-ε) * a (fun i => w i + r * x i) ≤ b (fun i => w i + r * x i) := by
    have := aux_core_ae_pullback w hr (S := Homogenization.openCubeSet R)
      (Ch02.cubeDomain R).isOpen.measurableSet (hR.trans (aux_core_openCubeSet_originCube_eq.le))
      (p := fun y => Real.exp (-ε) * a y ≤ b y) hlower
    simpa [volumeMeasureOn] using! this
  have hFa : F a = Ch02.bCoarse (Ch02.cubeDomain R) haQ.toCoeffOn i j := by
    simp only [hFdef]
    rw [haQdef]
    exact congrFun (congrFun (Ch02.bCoarse_eq_ofAEEq (aux_core_chart_scalarCoeffOnData_AEEq I w hr (a := a)
      ha i0 R hR)) i) j
  have hFb : F b = Ch02.bCoarse (Ch02.cubeDomain R) hbQ.toCoeffOn i j := by
    simp only [hFdef]
    rw [hbQdef]
    exact congrFun (congrFun (Ch02.bCoarse_eq_ofAEEq (aux_core_chart_scalarCoeffOnData_AEEq I w hr (a := b)
      hb i0 R hR)) i) j
  rw [hFa, hFb]
  calc |Ch02.bCoarse (Ch02.cubeDomain R) hbQ.toCoeffOn i j -
        Ch02.bCoarse (Ch02.cubeDomain R) haQ.toCoeffOn i j| ≤
      168 * (Real.exp ε - 1) * Ca :=
        aux_continuity_bCoarse_entry_ratio haQ hbQ hεpos hεlog2 hupper' hlower' i j
    _ ≤ η := hεbound

/-- `Measurable H` variant (`hH` was only used as `hH.1`), for the
`Hused = 0` branch of lem_finite_good_cell's good event. -/
theorem aux_core_lam_measurable_HOLE_gen {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hHm : Measurable H)
    (N : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (sigma : ℝ)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) :
    Measurable (fun omega : BilateralField d =>
      I.lam w r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w r sigma 2) := by
  exact aux_measlam_lam_of_entries I w r hr
    (fun omega => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) sigma hsigma
    (fun R hR i j => aux_core_sigmaStarInvCoarse_measurable_R_gen hd I M H hHm N w r hr R hR i j)

/-- `Measurable H` variant (`hH` was only used as `hH.1`), for the
`Hused = 0` branch of lem_finite_good_cell's good event. -/
theorem aux_core_Lam_measurable_HOLE_gen {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hHm : Measurable H)
    (N : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (sigma : ℝ)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) :
    Measurable (fun omega : BilateralField d =>
      I.Lam w r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w r sigma 2) := by
  exact aux_measlam_Lam_of_entries I w r hr
    (fun omega => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) sigma hsigma
    (fun R hR i j => aux_core_bCoarse_measurable_R_gen hd I M H hHm N w r hr R hR i j)

/-- `Measurable H` variant (`hH` was only used as `hH.1`), for the
`Hused = 0` branch of lem_finite_good_cell's good event. -/
theorem aux_core_err_measurable_HOLE_gen {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hHm : Measurable H)
    (N : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (s : ℝ)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (ref : BilateralField d → ℝ) (href : Measurable ref) (hrefpos : ∀ omega, 0 < ref omega) :
    Measurable (fun omega : BilateralField d =>
      I.err w r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w r (ref omega) s 2) := by
  refine aux_measerr_err_of_formula I w r hr
    (fun omega => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) ref href hrefpos s hs
    (fun R hR omega e he => aux_core_probe_formula_R hd I w r hr _ R hR (ref omega) (hrefpos omega) e he)
    (fun R hR i j => ?_)
    (fun R hR i j => aux_core_sigmaStarInvCoarse_measurable_R_gen hd I M H hHm N w r hr R hR i j)
  have hEq : ∀ omega : BilateralField d,
      Homogenization.Book.Ch02.sigmaCoarse (Homogenization.Book.Ch02.cubeDomain R)
          ((I.chart w r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w r).coeffOn R) =
        Homogenization.Book.Ch02.bCoarse (Homogenization.Book.Ch02.cubeDomain R)
          ((I.chart w r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w r).coeffOn R) :=
    fun omega => aux_core_sigmaCoarse_eq_bCoarse_R hd I w r hr _ R hR
  simp_rw [hEq]
  exact aux_core_bCoarse_measurable_R_gen hd I M H hHm N w r hr R hR i j


/-- `InfraredCharacterization` form (as consumed by `lem_band`): `I.lam` measurability. -/
theorem aux_core_lam_measurable_HOLE {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (N : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (sigma : ℝ)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) :
    Measurable (fun omega : BilateralField d =>
      I.lam w r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w r sigma 2) :=
  aux_core_lam_measurable_HOLE_gen hd I M H hH.1 N w r hr sigma hsigma

/-- `InfraredCharacterization` form: `I.Lam` measurability. -/
theorem aux_core_Lam_measurable_HOLE {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (N : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (sigma : ℝ)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) :
    Measurable (fun omega : BilateralField d =>
      I.Lam w r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w r sigma 2) :=
  aux_core_Lam_measurable_HOLE_gen hd I M H hH.1 N w r hr sigma hsigma

/-- `InfraredCharacterization` form: unit-root `σ` entry measurability. -/
theorem aux_core_sigmaCoarse_measurable_HOLE {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (N : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (i j : Fin d) :
    Measurable (fun omega : BilateralField d =>
      Homogenization.Book.Ch02.sigmaCoarse
        (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
        ((I.chart w r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w r).coeffOn
          (Homogenization.originCube d 0)) i j) :=
  aux_core_sigmaCoarse_measurable_HOLE_gen hd I M H hH.1 N w r hr i j

/-- `InfraredCharacterization` form: unit-root `σ*⁻¹` entry measurability. -/
theorem aux_core_sigmaStarInvCoarse_measurable_HOLE {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (N : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (i j : Fin d) :
    Measurable (fun omega : BilateralField d =>
      Homogenization.Book.Ch02.sigmaStarInvCoarse
        (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
        ((I.chart w r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w r).coeffOn
          (Homogenization.originCube d 0)) i j) :=
  aux_core_sigmaStarInvCoarse_measurable_HOLE_gen hd I M H hH.1 N w r hr i j

/-- `InfraredCharacterization` form: `I.err` measurability. -/
theorem aux_core_err_measurable_HOLE {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (N : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (s : ℝ)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (ref : BilateralField d → ℝ) (href : Measurable ref) (hrefpos : ∀ omega, 0 < ref omega) :
    Measurable (fun omega : BilateralField d =>
      I.err w r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w r (ref omega) s 2) :=
  aux_core_err_measurable_HOLE_gen hd I M H hH.1 N w r hr s hs ref href hrefpos

/-- The ellipticity-consumption clause `∀ x, c0 tr A (x·x) ≤ x·Ax` is a closed condition on the
matrix, hence measurable in the sample when the entries are. -/
theorem aux_goodev_trace_clause_measurable {Om : Type*} [MeasurableSpace Om] {d : ℕ}
    (A : Om → Matrix (Fin d) (Fin d) ℝ) (hA : ∀ i j, Measurable (fun ω => A ω i j)) (c0 : ℝ) :
    MeasurableSet {ω | ∀ x : Fin d → ℝ,
      c0 * Matrix.trace (A ω) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A ω).mulVec x} := by
  have htr : Measurable (fun ω : Om => (A ω).trace) := by
    simp only [Matrix.trace]
    exact Finset.measurable_sum Finset.univ (fun i _ => hA i i)
  have hpi : DenseRange (fun q : Fin d → ℚ => fun i => (q i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  have hset : {ω : Om | ∀ x : Fin d → ℝ, c0 * (A ω).trace * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A ω) *ᵥ x}
      = ⋂ q : Fin d → ℚ, {ω : Om | c0 * (A ω).trace
          * ((fun i => (q i : ℝ)) ⬝ᵥ (fun i => (q i : ℝ)))
            ≤ (fun i => (q i : ℝ)) ⬝ᵥ (A ω) *ᵥ (fun i => (q i : ℝ))} := by
    ext ω
    rw [mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h q
      exact h (fun i => (q i : ℝ))
    · intro h x
      have hc1 : Continuous (fun y : Fin d → ℝ => c0 * (A ω).trace * (y ⬝ᵥ y)) := by fun_prop
      have hc2 : Continuous (fun y : Fin d → ℝ => y ⬝ᵥ (A ω) *ᵥ y) := by fun_prop
      have hclosed : IsClosed {y : Fin d → ℝ | c0 * (A ω).trace * (y ⬝ᵥ y) ≤ y ⬝ᵥ (A ω) *ᵥ y} :=
        isClosed_le hc1 hc2
      have hsub : Set.range (fun q : Fin d → ℚ => fun i => (q i : ℝ)) ⊆
          {y : Fin d → ℝ | c0 * (A ω).trace * (y ⬝ᵥ y) ≤ y ⬝ᵥ (A ω) *ᵥ y} := by
        rintro y ⟨q, rfl⟩
        exact h q
      have hall : Set.univ ⊆ {y : Fin d → ℝ | c0 * (A ω).trace * (y ⬝ᵥ y) ≤ y ⬝ᵥ (A ω) *ᵥ y} := by
        rw [← hpi.closure_eq]
        exact hclosed.closure_subset_iff.2 hsub
      exact hall (Set.mem_univ x)
  rw [hset]
  apply MeasurableSet.iInter
  intro q
  apply measurableSet_le
  · exact (measurable_const.mul htr).mul measurable_const
  · show Measurable (fun ω : Om => ∑ i, (q i : ℝ) * ∑ j, A ω i j * (q j : ℝ))
    apply Finset.measurable_sum
    intro i _
    exact measurable_const.mul (Finset.measurable_sum Finset.univ (fun j _ => (hA i j).mul measurable_const))

/-- `good_event` is measurable in the sample when every random ingredient is measurable. -/
theorem aux_goodev_measurableSet (Om : Type) [MeasurableSpace Om] (d : ℕ) (Roots Enl Cmp : Type)
    [Fintype Enl] [Fintype Cmp] [Countable Roots]
    (centres : Roots → ℕ → Finset (Fin d → ℝ))
    (pre : Roots → ℕ → (Fin d → ℝ) → Finset ℤ)
    (Z Dsc : ℤ → (Fin d → ℝ) → Om → ℝ)
    (ellipMin ellipMax : Enl → Om → ℝ)
    (AE : Enl → Om → Matrix (Fin d) (Fin d) ℝ)
    (coarseErr refRatio : Cmp → Om → ℝ) (chosen : Cmp)
    (c0 Cd cell lam lamDet epshom cdet : ℝ) (k0 : ℕ)
    (hZ : ∀ j w, Measurable (Z j w)) (hD : ∀ j w, Measurable (Dsc j w))
    (hmin : ∀ e, Measurable (ellipMin e)) (hmax : ∀ e, Measurable (ellipMax e))
    (hAE : ∀ e i j, Measurable (fun ω => AE e ω i j))
    (herr : Measurable (coarseErr chosen)) (hrat : ∀ c, Measurable (refRatio c)) :
    MeasurableSet {ω | good_event Om d Roots Enl Cmp centres pre Z Dsc ellipMin ellipMax AE
      coarseErr refRatio chosen c0 Cd cell lam lamDet epshom cdet k0 ω} := by
  unfold good_event
  rw [ofPred_and]; refine MeasurableSet.inter (MeasurableSet.const _) ?_
  rw [ofPred_and]; refine MeasurableSet.inter (MeasurableSet.const _) ?_
  rw [ofPred_and]; refine MeasurableSet.inter (MeasurableSet.const _) ?_
  rw [ofPred_and]; refine MeasurableSet.inter (MeasurableSet.const _) ?_
  rw [ofPred_and]; refine MeasurableSet.inter (MeasurableSet.const _) ?_
  rw [ofPred_and]; refine MeasurableSet.inter (MeasurableSet.const _) ?_
  rw [ofPred_and]; refine MeasurableSet.inter (MeasurableSet.const _) ?_
  rw [ofPred_and]; refine MeasurableSet.inter ?_ ?_
  · rw [ofPred_forall]
    refine MeasurableSet.iInter (fun U => ?_)
    rw [ofPred_forall]
    refine MeasurableSet.iInter (fun D => ?_)
    refine MeasurableSet.imp (MeasurableSet.const _) ?_
    have hset : {ω : Om | ∀ w ∈ centres U D,
        ((∑ j ∈ pre U D w, Z j w ω) < lam * (D : ℝ) ∧
          (∑ j ∈ pre U D w, Dsc j w ω) < lam * (D : ℝ))} =
        ⋂ w ∈ centres U D, {ω : Om |
          ((∑ j ∈ pre U D w, Z j w ω) < lam * (D : ℝ) ∧
            (∑ j ∈ pre U D w, Dsc j w ω) < lam * (D : ℝ))} := by
      ext ω
      simp only [Set.mem_iInter, mem_ofPred_eq]
    rw [hset]
    refine Finset.measurableSet_biInter (centres U D) (fun w hw => ?_)
    rw [ofPred_and]
    exact MeasurableSet.inter
      (measurableSet_lt (Finset.measurable_sum (pre U D w) (fun j _ => hZ j w)) measurable_const)
      (measurableSet_lt (Finset.measurable_sum (pre U D w) (fun j _ => hD j w)) measurable_const)
  · rw [ofPred_and]; refine MeasurableSet.inter (MeasurableSet.const _) ?_
    rw [ofPred_and]; refine MeasurableSet.inter ?_ ?_
    · rw [ofPred_forall]
      refine MeasurableSet.iInter (fun e => ?_)
      rw [ofPred_and]
      exact MeasurableSet.inter (measurableSet_le measurable_const (hmin e))
        (measurableSet_le (hmax e) measurable_const)
    · rw [ofPred_and]; refine MeasurableSet.inter ?_ ?_
      · rw [ofPred_forall]
        refine MeasurableSet.iInter (fun e => ?_)
        have htr : Measurable (fun ω : Om => (AE e ω).trace) := by
          unfold Matrix.trace Matrix.diag
          exact Finset.measurable_sum Finset.univ (fun i _ => hAE e i i)
        have hDense : Dense (Set.range (fun v : Fin d → ℚ => fun i => (v i : ℝ))) :=
          DenseRange.piMap (fun _ : Fin d => Rat.denseRange_cast)
        have hmvcont : ∀ M : Matrix (Fin d) (Fin d) ℝ,
            Continuous (fun y : Fin d → ℝ => M.mulVec y) := by
          intro M
          rw [continuous_pi_iff]
          intro i
          have hp : Continuous (fun y : Fin d → ℝ => ∑ j, M i j * y j) :=
            continuous_finsetSum Finset.univ
              (fun j _ => continuous_const.mul (continuous_apply j))
          simpa only [Matrix.mulVec, dotProduct] using hp
        have hfiber : ∀ x : Fin d → ℝ,
            MeasurableSet {ω : Om | c0 * (AE e ω).trace * (x ⬝ᵥ x) ≤ x ⬝ᵥ (AE e ω).mulVec x} := by
          intro x
          refine measurableSet_le ?_ ?_
          · exact (htr.const_mul c0).mul_const (x ⬝ᵥ x)
          · have hmv : Measurable (fun ω : Om => (AE e ω).mulVec x) := by
              rw [measurable_pi_iff]
              intro i
              have hp : Measurable (fun ω : Om => ∑ j, (AE e ω) i j * x j) :=
                Finset.measurable_sum Finset.univ
                  (fun j _ => (hAE e i j).mul_const (x j))
              simpa only [Matrix.mulVec, dotProduct] using hp
            have hp : Measurable (fun ω : Om => ∑ i, x i * ((AE e ω).mulVec x) i) :=
              Finset.measurable_sum Finset.univ
                (fun i _ => measurable_const.mul (measurable_pi_iff.mp hmv i))
            simpa only [dotProduct] using hp
        have heq : {ω : Om | ∀ x : Fin d → ℝ,
              c0 * (AE e ω).trace * (x ⬝ᵥ x) ≤ x ⬝ᵥ (AE e ω).mulVec x}
            = {ω : Om | ∀ x ∈ Set.range (fun v : Fin d → ℚ => fun i => (v i : ℝ)),
              c0 * (AE e ω).trace * (x ⬝ᵥ x) ≤ x ⬝ᵥ (AE e ω).mulVec x} := by
          ext ω
          simp only [mem_ofPred_eq]
          constructor
          · intro h x hx; exact h x
          · intro h x
            have hcl : IsClosed {y : Fin d → ℝ |
                c0 * (AE e ω).trace * (y ⬝ᵥ y) ≤ y ⬝ᵥ (AE e ω).mulVec y} :=
              isClosed_le (continuous_const.mul (continuous_id.dotProduct continuous_id))
                (continuous_id.dotProduct (hmvcont (AE e ω)))
            have hsub : Set.range (fun v : Fin d → ℚ => fun i => (v i : ℝ)) ⊆
                {y : Fin d → ℝ | c0 * (AE e ω).trace * (y ⬝ᵥ y) ≤ y ⬝ᵥ (AE e ω).mulVec y} :=
              fun y hy => h y hy
            have hxmem : x ∈ closure (Set.range (fun v : Fin d → ℚ => fun i => (v i : ℝ))) := by
              rw [hDense.closure_eq]; exact Set.mem_univ x
            exact closure_minimal hsub hcl hxmem
        rw [heq]
        have hset : {ω : Om | ∀ x ∈ Set.range (fun v : Fin d → ℚ => fun i => (v i : ℝ)),
              c0 * (AE e ω).trace * (x ⬝ᵥ x) ≤ x ⬝ᵥ (AE e ω).mulVec x}
            = ⋂ v : Fin d → ℚ, {ω : Om |
              c0 * (AE e ω).trace * ((fun i => (v i : ℝ)) ⬝ᵥ (fun i => (v i : ℝ)))
                ≤ (fun i => (v i : ℝ)) ⬝ᵥ (AE e ω).mulVec (fun i => (v i : ℝ))} := by
          ext ω
          simp only [Set.mem_iInter, mem_ofPred_eq, Set.forall_mem_range]
        rw [hset]
        exact MeasurableSet.iInter (fun v => hfiber (fun i => (v i : ℝ)))
      · rw [ofPred_and]
        exact MeasurableSet.inter (measurableSet_le herr measurable_const)
          (by rw [ofPred_forall]
              refine MeasurableSet.iInter (fun cq => ?_)
              exact (hrat cq) measurableSet_Icc)



/-- **Measurability of the rescaled-chart coarse functionals** (paper 
 and the good event `mfd:sec-branches` whose ellipticity, coarse-matrix and
coarse-error tests are functions of these quantities). For every measurable field map `H`, every
cutoff `N` and every cube `(w, r)`, the coarse ellipticities `I.lam`, `I.Lam` at exponent `2` and
order `σ ∈ (0, 1]`, the unit-root coarse matrices `σ(Q₀)`, `σ*⁻¹(Q₀)` and the coarse error `I.err`
at exponent `2` (for any positive measurable normalization) of the rescaled chart of the cutoff
coefficient are measurable functions of the sample. -/
theorem chart_coords_measurable (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hHm : Measurable H)
    (N : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    (∀ sigma ∈ Set.Ioc (0 : ℝ) 1, Measurable (fun omega : BilateralField d =>
      I.lam w r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w r sigma 2)) ∧
    (∀ sigma ∈ Set.Ioc (0 : ℝ) 1, Measurable (fun omega : BilateralField d =>
      I.Lam w r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w r sigma 2)) ∧
    (∀ i j : Fin d, Measurable (fun omega : BilateralField d =>
      Homogenization.Book.Ch02.sigmaCoarse
        (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
        ((I.chart w r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w r).coeffOn
          (Homogenization.originCube d 0)) i j)) ∧
    (∀ i j : Fin d, Measurable (fun omega : BilateralField d =>
      Homogenization.Book.Ch02.sigmaStarInvCoarse
        (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
        ((I.chart w r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w r).coeffOn
          (Homogenization.originCube d 0)) i j)) ∧
    (∀ s ∈ Set.Ioc (0 : ℝ) 1, ∀ ref : BilateralField d → ℝ, Measurable ref →
      (∀ omega, 0 < ref omega) → Measurable (fun omega : BilateralField d =>
        I.err w r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w r (ref omega) s 2)) :=
  ⟨fun sigma hsigma => aux_core_lam_measurable_HOLE_gen hd I M H hHm N w r hr sigma hsigma,
    fun sigma hsigma => aux_core_Lam_measurable_HOLE_gen hd I M H hHm N w r hr sigma hsigma,
    fun i j => aux_core_sigmaCoarse_measurable_HOLE_gen hd I M H hHm N w r hr i j,
    fun i j => aux_core_sigmaStarInvCoarse_measurable_HOLE_gen hd I M H hHm N w r hr i j,
    fun s hs ref href hrefpos =>
      aux_core_err_measurable_HOLE_gen hd I M H hHm N w r hr s hs ref href hrefpos⟩


end SubdiffusiveProcess.Paper
