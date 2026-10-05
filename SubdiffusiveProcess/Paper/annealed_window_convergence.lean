module

public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_moments
public import SubdiffusiveProcess.Paper.stationary_family
public import SubdiffusiveProcess.Paper.stationary_defects
public import SubdiffusiveProcess.Paper.lem_fmono
public import SubdiffusiveProcess.Paper.near_extremal_member
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import Homogenization.Book.Ch02.Matrices
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter SubdiffusiveProcess Homogenization Homogenization.Book.Ch02
open scoped ENNReal NNReal BigOperators Topology

namespace SubdiffusiveProcess.Paper
/-- The actual finite-cutoff coefficient `A_N^0(omega)` as a continuous field. -/
def aux_awc_field {d : ℕ} (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ)
    (omega : BilateralField d) : C(SpatialCoordinates d, ℝ) :=
  ⟨fun x =>
    (Real.exp (((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
      SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
      Real.exp (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) x), by continuity⟩

theorem aux_awc_field_pos {d : ℕ} (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ)
    (omega : BilateralField d) (x : SpatialCoordinates d) :
    0 < aux_awc_field model N omega x := by
  have ha : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom model N :=
    SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model N
  simp only [aux_awc_field, ContinuousMap.coe_mk]
  positivity

/-- The scalar pure-flux response of the actual coefficient on the origin cube
of side `3^n`, as a Chapter 4 restriction observable. -/
def aux_awc_Jc {d : ℕ} (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (N n : ℕ)
    (q : Vec d) (omega : BilateralField d) : ℝ :=
  Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
    (originCube d (n : ℤ)) 0 q
    (aux_annealed_limit_response_transport_scalarRegCoeffField
      (aux_awc_field model N omega))

/-- Law transport of one pure-flux response from the stationary family to the
finite-cutoff GMC coefficient on the dilated cube. -/
theorem aux_awc_ident {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (N n : ℕ) (q : Vec d) :
    ProbabilityTheory.IdentDistrib (aux_awc_Jc model N n q)
      (fun omega => SubdiffusiveProcess.CoarseGrainingVocab.ahom model N *
        SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube model N 0 q
          (originCube d ((N + n : ℕ) : ℤ)) omega)
      (chaosSampleLaw model).toMeasure model.P.toMeasure := by
  let s : ℝ := (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹
  have hs : 0 < s := inv_pos.mpr (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model N)
  let r : ℝ := s * Real.exp (-(N : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq model.P)
  let c : ℝ := s⁻¹
  have hc : 0 < c := inv_pos.mpr hs
  have hnorm := aux_annealed_limit_response_transport_normalized_field_law
    (model := model) N
  have hnormR0 : ProbabilityTheory.IdentDistrib
      (fun omega => aux_awc_field model N omega)
      (fun omega =>
        ⟨fun x => s * Real.exp (∑ j ∈ Finset.range (N + 1),
          (omega (j : ℤ) ((3 : ℝ) ^ N • x) -
            _root_.SubdiffusiveProcess.Model.tauSq model.P)), by continuity⟩)
      (chaosSampleLaw model).toMeasure (chaosSampleLaw model).toMeasure := by
    simpa [aux_awc_field, s] using hnorm
  have hscaledID := aux_annealed_limit_response_transport_scaled_response
    model N n (originCube d (n : ℤ)) (originCube d ((N + n : ℕ) : ℤ))
    (aux_awc_field model N) s r c hnormR0 (by dsimp [r])
      (by dsimp [c, r]; field_simp) rfl rfl 0 q
  have hmul := hscaledID.comp (measurable_const_mul c)
  have hleft : ((fun x : ℝ => c * x) ∘ fun omega =>
      Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
        (originCube d (n : ℤ)) 0 q
        (c • aux_annealed_limit_response_transport_scalarRegCoeffField
          (aux_awc_field model N omega))) = aux_awc_Jc model N n q := by
    funext omega
    simp only [Function.comp_apply, aux_awc_Jc]
    rw [aux_annealed_limit_response_transport_response_zero_q_smul _ _ c hc q]
    field_simp
  have hright : ((fun x : ℝ => c * x) ∘ fun omega =>
      Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
        (originCube d (n : ℤ)) 0 q
        (Homogenization.rescaleReg N
          (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega))) =
      fun omega => SubdiffusiveProcess.CoarseGrainingVocab.ahom model N *
        SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube model N 0 q
          (originCube d ((N + n : ℕ) : ℤ)) omega := by
    funext omega
    simp only [Function.comp_apply]
    rw [Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
      (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField_aeLocallyUniformlyEllipticField
        model N omega) N n 0 q,
      SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.restrictionResponseJ_aCutoff_eq_cutoffResponseOnCube]
    simp [c, s]
  rw [hleft, hright] at hmul
  exact hmul


/-- The chaos pure-flux observable is the pure-flux response of any coefficient
carrier with the same pointwise scalar field. -/
theorem aux_awc_Jc_eq_responseJ {d : ℕ} [NeZero d]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (N n : ℕ) (q : Vec d)
    (omega : BilateralField d)
    (a : Homogenization.Book.Ch02.CoeffOn (cubeDomain (originCube d (n : ℤ))))
    (ha : ∀ x, a.toCoeffField x = scalarMatrix (aux_awc_field model N omega x)) :
    aux_awc_Jc model N n q omega =
      (1 / 2 : ℝ) * q ⬝ᵥ (Homogenization.Book.Ch02.sigmaStarInvCoarse
        (cubeDomain (originCube d (n : ℤ))) a).mulVec q := by
  have hfun : (aux_annealed_limit_response_transport_scalarRegCoeffField
      (aux_awc_field model N omega)).toFun = a.toCoeffField := by
    funext x
    rw [ha x]
    rfl
  have h1 : aux_awc_Jc model N n q omega =
      Homogenization.Book.Ch02.responseJ (cubeDomain (originCube d (n : ℤ))) a 0 q := by
    unfold aux_awc_Jc Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
    rw [Homogenization.responseJ_cubeSet_eq_openCubeSet_of_triadicCube,
      Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ, hfun]
    rfl
  rw [h1, Homogenization.Book.Ch02.responseJ_zero_q_eq_sigmaStarInvCoarse]
  rfl

/-- Pointwise nonnegativity of the chaos pure-flux observable. -/
theorem aux_awc_Jc_nonneg {d : ℕ} (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (N n : ℕ) (q : Vec d) (omega : BilateralField d) :
    0 ≤ aux_awc_Jc model N n q omega :=
  Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet_nonneg _ _ _ _

/-- The inverse-Neumann quadratic form at a unit slope is controlled by the full
unit-slope response, using the symmetric split of `in_J`. -/
theorem aux_awc_star_unit_le {d : ℕ} (hJ : in_J d) (U : Homogenization.Book.Ch02.Domain d)
    (b : Homogenization.Book.Ch02.CoeffOn U)
    (hb : Homogenization.Book.Ch02.CoeffOn.IsSymmetric b)
    (e : Fin d → ℝ) (he : ∑ i, e i ^ 2 = 1) :
    (1 / 2 : ℝ) * e ⬝ᵥ (Homogenization.Book.Ch02.sigmaStarInvCoarse U b).mulVec e ≤
      1 + Homogenization.Book.Ch02.responseJ U b e e := by
  have hsplit := hJ.responseJ_split U b hb e e
  have hord := (hJ.ord_bounds U b hb e).2.1
  have hstar : 0 ≤ Homogenization.vecDot e
      (Homogenization.matVecMul (Homogenization.Book.Ch02.sigmaStarCoarse U b) e) := by
    have h := (Homogenization.Book.Ch02.sigmaStarCoarse_posDef U b).posSemidef.dotProduct_mulVec_nonneg e
    simpa [Homogenization.vecDot, Homogenization.matVecMul, star_trivial] using! h
  have hee : Homogenization.vecDot e e = 1 := by
    rw [← he]
    simp [Homogenization.vecDot, sq]
  have hq : Homogenization.vecDot e (Homogenization.matVecMul
      (Homogenization.Book.Ch02.sigmaStarInvCoarse U b) e) =
      e ⬝ᵥ (Homogenization.Book.Ch02.sigmaStarInvCoarse U b).mulVec e := rfl
  rw [← hq]
  rw [hee] at hsplit
  linarith

/-- Homogeneity: a unit-slope bound on a quadratic form bounds it at every slope. -/
theorem aux_awc_quad_le_scaled {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (B : ℝ)
    (h : ∀ e : Fin d → ℝ, ∑ i, e i ^ 2 = 1 → (1 / 2 : ℝ) * e ⬝ᵥ M.mulVec e ≤ B)
    (q : Fin d → ℝ) :
    (1 / 2 : ℝ) * q ⬝ᵥ M.mulVec q ≤ (∑ i, q i ^ 2) * B := by
  set s : ℝ := ∑ i, q i ^ 2 with hs
  have hs0 : 0 ≤ s := Finset.sum_nonneg (fun i _ => sq_nonneg (q i))
  rcases hs0.lt_or_eq with hpos | hzero
  · set e : Fin d → ℝ := (Real.sqrt s)⁻¹ • q with he
    have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hpos
    have he1 : ∑ i, e i ^ 2 = 1 := by
      simp only [he, Pi.smul_apply, smul_eq_mul, mul_pow, inv_pow,
        Real.sq_sqrt hs0, ← Finset.mul_sum, ← hs]
      field_simp
    have hq : q = Real.sqrt s • e := by
      rw [he, smul_smul, mul_inv_cancel₀ hsq.ne', one_smul]
    have hb := h e he1
    rw [hq, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
      smul_eq_mul]
    have : Real.sqrt s * (Real.sqrt s * e ⬝ᵥ M.mulVec e) =
        s * e ⬝ᵥ M.mulVec e := by
      rw [← mul_assoc, Real.mul_self_sqrt hs0]
    rw [this]
    nlinarith
  · have hq0 : q = 0 := by
      funext i
      have : q i ^ 2 = 0 := by
        have hle : q i ^ 2 ≤ s := by
          rw [hs]
          exact Finset.single_le_sum (f := fun j => q j ^ 2)
            (fun j _ => sq_nonneg (q j)) (Finset.mem_univ i)
        nlinarith [sq_nonneg (q i)]
      simpa using this
    subst hq0
    simp [← hzero]


/-- A uniform `L^xi` bound with `xi ≥ 3` controls the third moment. -/
theorem aux_awc_third_moment {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (_hX : AEStronglyMeasurable X μ)
    (hX0 : ∀ ω, 0 ≤ X ω) (xi B : ℝ) (hxi : 3 ≤ xi) (hB0 : 0 ≤ B)
    (hB : eLpNorm X (ENNReal.ofReal xi) μ ≤ ENNReal.ofReal B) :
    Integrable (fun ω => X ω ^ 3) μ ∧ ∫ ω, X ω ^ 3 ∂μ ≤ B ^ 3 := by
  have hmemxi : MemLp X (ENNReal.ofReal xi) μ :=
    lt_of_le_of_lt hB ENNReal.ofReal_lt_top
  have h3le : (3 : ℝ≥0∞) ≤ ENNReal.ofReal xi := by
    rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by simp]
    exact ENNReal.ofReal_le_ofReal hxi
  have hmem3 : MemLp X 3 μ := hmemxi.mono_exponent h3le
  have hnorm : (fun ω => ‖X ω‖ ^ 3) = fun ω => X ω ^ 3 := by
    funext ω
    rw [Real.norm_of_nonneg (hX0 ω)]
  have hint : Integrable (fun ω => X ω ^ 3) μ := by
    have h := hmem3.integrable_norm_pow (p := 3) (by norm_num)
    rw [hnorm] at h
    exact h
  refine ⟨hint, ?_⟩
  have hle : eLpNorm X 3 μ ≤ ENNReal.ofReal B :=
    (eLpNorm_le_eLpNorm_of_exponent_le (f := X) (μ := μ) h3le).trans hB
  rw [hmem3.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.ofReal_le_ofReal_iff hB0] at hle
  have h3r : (3 : ℝ≥0∞).toReal = (3 : ℝ) := by norm_num
  rw [h3r] at hle
  have hfun : (fun ω => ‖X ω‖ ^ (3 : ℝ)) = fun ω => X ω ^ 3 := by
    funext ω
    rw [Real.norm_of_nonneg (hX0 ω), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  rw [hfun] at hle
  have hI0 : 0 ≤ ∫ ω, X ω ^ 3 ∂μ :=
    integral_nonneg (fun ω => pow_nonneg (hX0 ω) 3)
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hI0 _) hle (by norm_num : (0 : ℝ) ≤ 3)
  rw [Real.rpow_inv_rpow hI0 (by norm_num), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast] at hpow
  exact hpow

theorem aux_awc_cube_le (x y s : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hs : 0 ≤ s)
    (hxy : x ≤ s * (1 + y)) : x ^ 3 ≤ 7 * s ^ 3 * (1 + y ^ 3) := by
  have h1 : x ^ 3 ≤ (s * (1 + y)) ^ 3 := pow_le_pow_left₀ hx hxy 3
  have h2 : (1 + y) ^ 3 ≤ 7 * (1 + y ^ 3) := by nlinarith [sq_nonneg (y - 1), sq_nonneg y]
  calc x ^ 3 ≤ (s * (1 + y)) ^ 3 := h1
    _ = s ^ 3 * (1 + y) ^ 3 := by ring
    _ ≤ s ^ 3 * (7 * (1 + y ^ 3)) := by gcongr
    _ = 7 * s ^ 3 * (1 + y ^ 3) := by ring


theorem aux_awc_sq_le_interp (x t : ℝ) (hx : 0 ≤ x) (ht : 0 < t) :
    x ^ 2 ≤ t * x + x ^ 3 / t := by
  rw [div_eq_mul_inv]
  have htinv : 0 < t⁻¹ := inv_pos.mpr ht
  have hkey : 0 ≤ x * (t - x) ^ 2 * t⁻¹ := by positivity
  have hexp : x * (t - x) ^ 2 * t⁻¹ = t * x - 2 * x ^ 2 + x ^ 3 * t⁻¹ := by
    field_simp
    ring
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

theorem aux_awc_eLpNorm_two_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (f : Ω → ℝ) (hf : AEStronglyMeasurable f μ)
    (hsq : Integrable (fun ω => f ω ^ 2) μ) {B : ℝ}
    (hB : ∫ ω, f ω ^ 2 ∂μ ≤ B) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt B) := by
  have hmem : MemLp f 2 μ := (memLp_two_iff_integrable_sq hf).2 hsq
  rw [hmem.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  apply ENNReal.ofReal_le_ofReal
  have hfun : (fun ω => ‖f ω‖ ^ (2 : ℝ≥0∞).toReal) = fun ω => f ω ^ 2 := by
    funext ω
    rw [show (2 : ℝ≥0∞).toReal = (2 : ℝ) by norm_num, Real.rpow_two,
      Real.norm_eq_abs, sq_abs]
  rw [hfun, show (2 : ℝ≥0∞).toReal = (2 : ℝ) by norm_num,
    show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  exact Real.sqrt_le_sqrt hB


theorem aux_awc_core_abstract {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (s : Finset ι) (hs : s.Nonempty)
    (Y : Ω → ℝ) (Z : ι → Ω → ℝ) (μ0 t K3 V : ℝ) (ht : 0 < t)
    (hY0 : ∀ ω, 0 ≤ Y ω) (hZ0 : ∀ i ∈ s, ∀ ω, 0 ≤ Z i ω)
    (hsub : ∀ ω, Y ω ≤ (s.card : ℝ)⁻¹ * ∑ i ∈ s, Z i ω)
    (hYint : Integrable Y P) (hZint : ∀ i ∈ s, Integrable (Z i) P)
    (hmean : ∀ i ∈ s, ∫ ω, Z i ω ∂P = μ0)
    (hZ3 : ∀ i ∈ s, Integrable (fun ω => Z i ω ^ 3) P)
    (h3 : ∀ i ∈ s, ∫ ω, Z i ω ^ 3 ∂P ≤ K3)
    (hV : eLpNorm (fun ω => (s.card : ℝ)⁻¹ * ∑ i ∈ s, Z i ω - μ0) 2 P ≤
      ENNReal.ofReal V) :
    eLpNorm (fun ω => Y ω - μ0) 2 P ≤
      ENNReal.ofReal V +
        ENNReal.ofReal (Real.sqrt (t * (μ0 - ∫ ω, Y ω ∂P) + K3 / t)) := by
  set w : ℝ := (s.card : ℝ)⁻¹ with hw
  have hcard : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  have hw0 : 0 ≤ w := by positivity
  let A : Ω → ℝ := fun ω => w * ∑ i ∈ s, Z i ω
  let X : Ω → ℝ := fun ω => A ω - Y ω
  have hAint : Integrable A P :=
    (integrable_finsetSum s (fun i hi => hZint i hi)).const_mul w
  have hAm : AEStronglyMeasurable A P := hAint.aestronglyMeasurable
  have hXint : Integrable X P := hAint.sub hYint
  have hXm : AEStronglyMeasurable X P := hXint.aestronglyMeasurable
  have hX0 : ∀ ω, 0 ≤ X ω := fun ω => sub_nonneg.mpr (hsub ω)
  have hXA : ∀ ω, X ω ≤ A ω := fun ω => by
    have := hY0 ω
    dsimp only [X]
    linarith
  have hwsum : ∑ i ∈ s, w = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, hw, mul_inv_cancel₀ hcard]
  have hpow : ∀ ω, A ω ^ 3 ≤ w * ∑ i ∈ s, Z i ω ^ 3 := by
    intro ω
    have h := Real.pow_arith_mean_le_arith_mean_pow s (fun _ => w) (fun i => Z i ω)
      (fun _ _ => hw0) hwsum (fun i hi => hZ0 i hi ω) 3
    simpa [A, Finset.mul_sum] using h
  let B3 : Ω → ℝ := fun ω => w * ∑ i ∈ s, Z i ω ^ 3
  have hB3int : Integrable B3 P :=
    (integrable_finsetSum s (fun i hi => hZ3 i hi)).const_mul w
  have hdom : ∀ ω, X ω ^ 2 ≤ t * X ω + B3 ω / t := by
    intro ω
    have h1 := aux_awc_sq_le_interp (X ω) t (hX0 ω) ht
    have h2 : X ω ^ 3 ≤ A ω ^ 3 := by
      exact pow_le_pow_left₀ (hX0 ω) (hXA ω) 3
    have h3' : X ω ^ 3 / t ≤ B3 ω / t :=
      div_le_div_of_nonneg_right (h2.trans (hpow ω)) ht.le
    linarith
  have hboundInt : Integrable (fun ω => t * X ω + B3 ω / t) P :=
    (hXint.const_mul t).add (hB3int.div_const t)
  have hXsq : Integrable (fun ω => X ω ^ 2) P := by
    refine hboundInt.mono' (hXm.pow 2) ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hdom ω
  have hintX : ∫ ω, X ω ∂P = μ0 - ∫ ω, Y ω ∂P := by
    have hA : ∫ ω, A ω ∂P = μ0 := by
      simp only [A]
      rw [integral_const_mul, integral_finsetSum s (fun i hi => hZint i hi),
        Finset.sum_congr rfl hmean, Finset.sum_const, nsmul_eq_mul, hw]
      field_simp
    simp only [X]
    rw [integral_sub hAint hYint, hA]
  have hintB3 : ∫ ω, B3 ω ∂P ≤ K3 := by
    simp only [B3]
    rw [integral_const_mul, integral_finsetSum s (fun i hi => hZ3 i hi)]
    calc w * ∑ i ∈ s, ∫ ω, Z i ω ^ 3 ∂P ≤ w * ∑ _i ∈ s, K3 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum h3) hw0
      _ = K3 := by
          rw [Finset.sum_const, nsmul_eq_mul, hw]
          field_simp
  have hXsqB : ∫ ω, X ω ^ 2 ∂P ≤ t * (μ0 - ∫ ω, Y ω ∂P) + K3 / t := by
    calc ∫ ω, X ω ^ 2 ∂P ≤ ∫ ω, (t * X ω + B3 ω / t) ∂P :=
          integral_mono hXsq hboundInt hdom
      _ = t * ∫ ω, X ω ∂P + (∫ ω, B3 ω ∂P) / t := by
          rw [integral_add (hXint.const_mul t) (hB3int.div_const t),
            integral_const_mul, integral_div]
      _ ≤ t * (μ0 - ∫ ω, Y ω ∂P) + K3 / t := by
          rw [hintX]
          have := div_le_div_of_nonneg_right hintB3 ht.le
          linarith
  have hXnorm := aux_awc_eLpNorm_two_le X hXm hXsq hXsqB
  have hsplit : (fun ω => Y ω - μ0) = fun ω => (A ω - μ0) - X ω := by
    funext ω
    simp only [X]
    ring
  rw [hsplit]
  calc eLpNorm (fun ω => (A ω - μ0) - X ω) 2 P
      ≤ eLpNorm (fun ω => A ω - μ0) 2 P + eLpNorm X 2 P :=
        eLpNorm_sub_le (by norm_num)
    _ ≤ ENNReal.ofReal V +
        ENNReal.ofReal (Real.sqrt (t * (μ0 - ∫ ω, Y ω ∂P) + K3 / t)) := by
        gcongr

/-- Pointwise nonnegativity of the literal cutoff response. -/
theorem aux_awc_cutoff_nonneg {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ) (q : Vec d)
    (R : TriadicCube d) (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube M N 0 q R ω := by
  rw [← SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.restrictionResponseJ_aCutoff_eq_cutoffResponseOnCube]
  exact Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet_nonneg _ _ _ _

/-- Stationarity of the cubed scaled response: every translated cell has the
law of the origin cube at the same scale. -/
theorem aux_awc_cube_stationary {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ) (q : Vec d) (c : ℝ)
    (R : TriadicCube d) :
    (Integrable (fun ω => (c * SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube M N 0 q R ω) ^ 3)
        M.P.toMeasure ↔
      Integrable (fun ω => (c * SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube M N 0 q
        (originCube d R.scale) ω) ^ 3) M.P.toMeasure) ∧
    ∫ ω, (c * SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube M N 0 q R ω) ^ 3 ∂M.P.toMeasure =
      ∫ ω, (c * SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube M N 0 q
        (originCube d R.scale) ω) ^ 3 ∂M.P.toMeasure := by
  let T := SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSequence
    (Homogenization.triadicCubeShift R)
  let g : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun ω =>
    (c * SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube M N 0 q (originCube d R.scale) ω) ^ 3
  have hT : MeasurePreserving T M.P.toMeasure M.P.toMeasure :=
    ⟨SubdiffusiveProcess.CoarseGrainingVocab.measurable_translatePotentialSequence _,
      SubdiffusiveProcess.CoarseGrainingVocab.potentialSequenceLaw_stationary M _⟩
  have hgm : Measurable g :=
    ((SubdiffusiveProcess.CoarseGrainingVocab.measurable_cutoffResponseOnCube M N 0 q
      (originCube d R.scale)).const_mul c).pow_const 3
  have heq : (fun ω =>
      (c * SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube M N 0 q R ω) ^ 3) = g ∘ T := by
    funext ω
    simp only [g, T, Function.comp_apply]
    rw [SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube_eq_originCube_translate M N 0 q R ω]
  rw [heq]
  refine ⟨hT.integrable_comp hgm.aestronglyMeasurable, ?_⟩
  simpa [Function.comp_def] using
    Homogenization.integral_comp_eq_of_map_eq
      (SubdiffusiveProcess.CoarseGrainingVocab.measurable_translatePotentialSequence _)
      (SubdiffusiveProcess.CoarseGrainingVocab.potentialSequenceLaw_stationary M _) g
      hgm.aestronglyMeasurable


theorem aux_awc_sq_le_one_add_cube (x : ℝ) (hx : 0 ≤ x) : x ^ 2 ≤ 1 + x ^ 3 := by
  rcases le_total x 1 with h | h
  · have : x ^ 2 ≤ 1 := by nlinarith
    have : 0 ≤ x ^ 3 := by positivity
    linarith
  · have : x ^ 2 ≤ x ^ 3 := by nlinarith
    linarith

/-- The centered origin response has a second moment controlled by the third
moment of the scaled response. -/
theorem aux_awc_centered_sq {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N l : ℕ) (q : Vec d) (c K3 : ℝ)
    (hc : 0 < c)
    (h3int : Integrable (fun ω => (c * SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube M N 0 q
      (originCube d (l : ℤ)) ω) ^ 3) M.P.toMeasure)
    (h3 : ∫ ω, (c * SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube M N 0 q
      (originCube d (l : ℤ)) ω) ^ 3 ∂M.P.toMeasure ≤ K3) :
    Integrable (fun ω => |SubdiffusiveProcess.CoarseGrainingVocab.centeredCutoffResponseOnCube M N l 0 q
      (originCube d (l : ℤ)) ω| ^ (2 : ℝ)) M.P.toMeasure ∧
    (∫ ω, |SubdiffusiveProcess.CoarseGrainingVocab.centeredCutoffResponseOnCube M N l 0 q
      (originCube d (l : ℤ)) ω| ^ (2 : ℝ) ∂M.P.toMeasure) ^ (2 : ℝ)⁻¹ ≤
        c⁻¹ * Real.sqrt (1 + K3) := by
  set G : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun ω =>
    SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube M N 0 q (originCube d (l : ℤ)) ω with hG
  have hGm : Measurable G :=
    SubdiffusiveProcess.CoarseGrainingVocab.measurable_cutoffResponseOnCube M N 0 q _
  have hG0 : ∀ ω, 0 ≤ G ω := fun ω => aux_awc_cutoff_nonneg M N q _ ω
  have hfun : (fun ω => |SubdiffusiveProcess.CoarseGrainingVocab.centeredCutoffResponseOnCube M N l 0 q
      (originCube d (l : ℤ)) ω| ^ (2 : ℝ)) =
      fun ω => (G ω - ∫ η, G η ∂M.P.toMeasure) ^ 2 := by
    funext ω
    rw [Real.rpow_two, sq_abs]
    rfl
  have hdom : ∀ ω, G ω ^ 2 ≤ c⁻¹ ^ 2 * (1 + (c * G ω) ^ 3) := by
    intro ω
    have h := aux_awc_sq_le_one_add_cube (c * G ω) (mul_nonneg hc.le (hG0 ω))
    have hc2 : 0 < c⁻¹ ^ 2 := by positivity
    have : G ω ^ 2 = c⁻¹ ^ 2 * (c * G ω) ^ 2 := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left h hc2.le
  have hGsq : Integrable (fun ω => G ω ^ 2) M.P.toMeasure := by
    refine ((integrable_const 1).add h3int).const_mul (c⁻¹ ^ 2) |>.mono'
      (hGm.pow_const 2).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hdom ω
  have hGmem : MemLp G 2 M.P.toMeasure :=
    (memLp_two_iff_integrable_sq hGm.aestronglyMeasurable).2 hGsq
  have hcen : MemLp (fun ω => G ω - ∫ η, G η ∂M.P.toMeasure) 2 M.P.toMeasure :=
    hGmem.sub (memLp_const _)
  have hcensq : Integrable (fun ω => (G ω - ∫ η, G η ∂M.P.toMeasure) ^ 2)
      M.P.toMeasure :=
    (memLp_two_iff_integrable_sq hcen.aestronglyMeasurable).1 hcen
  have hvar : ∫ ω, (G ω - ∫ η, G η ∂M.P.toMeasure) ^ 2 ∂M.P.toMeasure ≤
      ∫ ω, G ω ^ 2 ∂M.P.toMeasure := by
    rw [← ProbabilityTheory.variance_eq_integral hGm.aemeasurable]
    exact ProbabilityTheory.variance_le_expectation_sq hGm.aestronglyMeasurable
  have hsecond : ∫ ω, G ω ^ 2 ∂M.P.toMeasure ≤ c⁻¹ ^ 2 * (1 + K3) := by
    calc ∫ ω, G ω ^ 2 ∂M.P.toMeasure
        ≤ ∫ ω, c⁻¹ ^ 2 * (1 + (c * G ω) ^ 3) ∂M.P.toMeasure :=
          integral_mono hGsq (((integrable_const 1).add h3int).const_mul _) hdom
      _ = c⁻¹ ^ 2 * (1 + ∫ ω, (c * G ω) ^ 3 ∂M.P.toMeasure) := by
          rw [integral_const_mul, integral_add (integrable_const 1) h3int,
            integral_const, probReal_univ, one_smul]
      _ ≤ c⁻¹ ^ 2 * (1 + K3) := by
          gcongr
  rw [hfun]
  refine ⟨hcensq, ?_⟩
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  calc Real.sqrt (∫ ω, (G ω - ∫ η, G η ∂M.P.toMeasure) ^ 2 ∂M.P.toMeasure)
      ≤ Real.sqrt (c⁻¹ ^ 2 * (1 + K3)) := Real.sqrt_le_sqrt (hvar.trans hsecond)
    _ = c⁻¹ * Real.sqrt (1 + K3) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]


/-- The finite-range colored variance estimate for the scaled descendant
average, with its second-moment budget read from the third moment. -/
theorem aux_awc_rosenthal_scaled (d : ℕ) [NeZero d] :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N l m : ℕ), N ≤ l → l ≤ m →
        ∀ (q : Vec d) (c K3 : ℝ), 0 < c →
        Integrable (fun ω => (c * SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube M N 0 q
          (originCube d (l : ℤ)) ω) ^ 3) M.P.toMeasure →
        ∫ ω, (c * SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube M N 0 q
          (originCube d (l : ℤ)) ω) ^ 3 ∂M.P.toMeasure ≤ K3 →
        eLpNorm (fun ω =>
            ((descendantsAtScale (originCube d (m : ℤ)) (l : ℤ)).card : ℝ)⁻¹ *
              ∑ R ∈ descendantsAtScale (originCube d (m : ℤ)) (l : ℤ),
                c * SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube M N 0 q R ω -
            c * ∫ η, SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube M N 0 q
              (originCube d (l : ℤ)) η ∂M.P.toMeasure) 2 M.P.toMeasure ≤
          ENNReal.ofReal (C0 * Real.sqrt (1 + K3) *
            Real.rpow 3 (-((d : ℝ) / 2) * ((m - l : ℕ) : ℝ))) := by
  obtain ⟨C, hC, hR⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.exists_centeredCutoffResponseAverage_dimensional_bound d
  refine ⟨2 * C, by positivity, ?_⟩
  intro M N l m hNl hlm q c K3 hc h3int h3
  obtain ⟨hint2, hroot⟩ := aux_awc_centered_sq M N l q c K3 hc h3int h3
  have hK : 0 ≤ c⁻¹ * Real.sqrt (1 + K3) := by positivity
  have hbound := hR M N l m hNl hlm 0 q 2 (c⁻¹ * Real.sqrt (1 + K3)) le_rfl hK hint2 hroot
  set s := descendantsAtScale (originCube d (m : ℤ)) (l : ℤ) with hs
  have hsne : s.Nonempty := descendantsAtScale_nonempty _ (by
    change (l : ℤ) ≤ (m : ℤ)
    exact_mod_cast hlm)
  have hcard : (s.card : ℝ) ≠ 0 := by exact_mod_cast hsne.card_ne_zero
  set H : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun ω =>
    (s.card : ℝ)⁻¹ * ∑ R ∈ s,
      SubdiffusiveProcess.CoarseGrainingVocab.centeredCutoffResponseOnCube M N l 0 q R ω with hH
  have hcell : ∀ R ∈ s, MemLp
      (SubdiffusiveProcess.CoarseGrainingVocab.centeredCutoffResponseOnCube M N l 0 q R) 2 M.P.toMeasure := by
    intro R hR
    have hRs : R.scale = (l : ℤ) := scale_eq_of_mem_descendantsAtScale hR
    have hi := (SubdiffusiveProcess.CoarseGrainingVocab.integrable_abs_centeredCutoffResponseOnCube_rpow_iff_originCube
      M N l 0 q R hRs 2 (by norm_num)).2 hint2
    have hm := SubdiffusiveProcess.CoarseGrainingVocab.measurable_centeredCutoffResponseOnCube M N l 0 q R
    refine (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 ?_
    refine hi.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    rw [Real.rpow_two, sq_abs]
  have hHmem : MemLp H 2 M.P.toMeasure := by
    have hsum : MemLp (fun ω => ∑ R ∈ s,
        SubdiffusiveProcess.CoarseGrainingVocab.centeredCutoffResponseOnCube M N l 0 q R ω) 2
        M.P.toMeasure := memLp_finsetSum' s hcell |>.congr_norm
          (by
            exact (memLp_finsetSum' s hcell).aestronglyMeasurable.congr
              (Filter.Eventually.of_forall fun ω => by simp [Finset.sum_apply]))
          (Filter.Eventually.of_forall fun ω => by simp [Finset.sum_apply])
    exact hsum.const_mul _
  have hHnorm : eLpNorm H 2 M.P.toMeasure ≤
      ENNReal.ofReal (C * 2 * (c⁻¹ * Real.sqrt (1 + K3)) *
        Real.rpow 3 (-((d : ℝ) / 2) * ((m - l : ℕ) : ℝ))) := by
    rw [hHmem.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
    apply ENNReal.ofReal_le_ofReal
    rw [show (2 : ℝ≥0∞).toReal = (2 : ℝ) by norm_num]
    simpa only [hH, Real.norm_eq_abs] using hbound
  have hF : (fun ω => (s.card : ℝ)⁻¹ * ∑ R ∈ s,
        c * SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube M N 0 q R ω -
      c * ∫ η, SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube M N 0 q
        (originCube d (l : ℤ)) η ∂M.P.toMeasure) = c • H := by
    funext ω
    simp only [hH, Pi.smul_apply, smul_eq_mul,
      SubdiffusiveProcess.CoarseGrainingVocab.centeredCutoffResponseOnCube, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    field_simp
  rw [hF, eLpNorm_const_smul, Real.enorm_eq_ofReal hc.le]
  calc ENNReal.ofReal c * eLpNorm H 2 M.P.toMeasure
      ≤ ENNReal.ofReal c * ENNReal.ofReal (C * 2 * (c⁻¹ * Real.sqrt (1 + K3)) *
          Real.rpow 3 (-((d : ℝ) / 2) * ((m - l : ℕ) : ℝ))) := by gcongr
    _ = ENNReal.ofReal (2 * C * Real.sqrt (1 + K3) *
          Real.rpow 3 (-((d : ℝ) / 2) * ((m - l : ℕ) : ℝ))) := by
        rw [← ENNReal.ofReal_mul hc.le]
        congr 1
        field_simp

/-- The fixed-direction Neumann window in the finite-cutoff GMC probability
space: pointwise response subadditivity over the scale-`l` descendants,
the annealed defect, a third-moment interpolation and the finite-range
colored variance bound. -/
theorem aux_awc_gmc_window (d : ℕ) [NeZero d] :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N l m : ℕ), N ≤ l → l ≤ m →
        ∀ (q : Vec d) (c t K3 : ℝ), 0 < c → 0 < t →
        Integrable (fun ω => (c * SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube M N 0 q
          (originCube d (l : ℤ)) ω) ^ 3) M.P.toMeasure →
        ∫ ω, (c * SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube M N 0 q
          (originCube d (l : ℤ)) ω) ^ 3 ∂M.P.toMeasure ≤ K3 →
        eLpNorm (fun ω => c * SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube M N 0 q
            (originCube d (m : ℤ)) ω -
          c * ∫ η, SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube M N 0 q
            (originCube d (l : ℤ)) η ∂M.P.toMeasure) 2 M.P.toMeasure ≤
          ENNReal.ofReal (C0 * Real.sqrt (1 + K3) *
            Real.rpow 3 (-((d : ℝ) / 2) * ((m - l : ℕ) : ℝ))) +
          ENNReal.ofReal (Real.sqrt (t *
            (c * ∫ η, SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube M N 0 q
                (originCube d (l : ℤ)) η ∂M.P.toMeasure -
              ∫ η, c * SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube M N 0 q
                (originCube d (m : ℤ)) η ∂M.P.toMeasure) + K3 / t)) := by
  obtain ⟨C0, hC0, hros⟩ := aux_awc_rosenthal_scaled d
  refine ⟨C0, hC0, ?_⟩
  intro M N l m hNl hlm q c t K3 hc ht h3int h3
  set s := descendantsAtScale (originCube d (m : ℤ)) (l : ℤ) with hs
  have hsne : s.Nonempty := descendantsAtScale_nonempty _ (by
    change (l : ℤ) ≤ (m : ℤ)
    exact_mod_cast hlm)
  have hcard : (s.card : ℝ) ≠ 0 := by exact_mod_cast hsne.card_ne_zero
  have hsub : ∀ ω, c * SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube M N 0 q
      (originCube d (m : ℤ)) ω ≤ (s.card : ℝ)⁻¹ * ∑ R ∈ s,
        c * SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube M N 0 q R ω := by
    intro ω
    have h := SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube_le_centeredDescendantAverage_add_mean
      M N l m hlm 0 q ω
    have halg : (s.card : ℝ)⁻¹ * ∑ R ∈ s,
          SubdiffusiveProcess.CoarseGrainingVocab.centeredCutoffResponseOnCube M N l 0 q R ω +
        ∫ η, SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube M N 0 q
          (originCube d (l : ℤ)) η ∂M.P.toMeasure =
        (s.card : ℝ)⁻¹ * ∑ R ∈ s,
          SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube M N 0 q R ω := by
      simp only [SubdiffusiveProcess.CoarseGrainingVocab.centeredCutoffResponseOnCube,
        Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      field_simp
      ring
    rw [← hs, halg] at h
    rw [← Finset.mul_sum, ← mul_assoc, mul_comm (s.card : ℝ)⁻¹ c, mul_assoc]
    exact mul_le_mul_of_nonneg_left h hc.le
  have hmean : ∀ R ∈ s, ∫ ω, c * SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube M N 0 q R ω
      ∂M.P.toMeasure = c * ∫ η, SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube M N 0 q
        (originCube d (l : ℤ)) η ∂M.P.toMeasure := by
    intro R hR
    have hRs : R.scale = (l : ℤ) := scale_eq_of_mem_descendantsAtScale hR
    rw [integral_const_mul,
      SubdiffusiveProcess.CoarseGrainingVocab.integral_cutoffResponseOnCube_eq_originCube M N 0 q R, hRs]
  have hZ3 : ∀ R ∈ s, Integrable (fun ω =>
      (c * SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube M N 0 q R ω) ^ 3) M.P.toMeasure ∧
      ∫ ω, (c * SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube M N 0 q R ω) ^ 3
        ∂M.P.toMeasure ≤ K3 := by
    intro R hR
    have hRs : R.scale = (l : ℤ) := scale_eq_of_mem_descendantsAtScale hR
    obtain ⟨hiff, heq⟩ := aux_awc_cube_stationary M N q c R
    rw [hRs] at hiff heq
    exact ⟨hiff.2 h3int, heq ▸ h3⟩
  have hV := hros M N l m hNl hlm q c K3 hc h3int h3
  exact aux_awc_core_abstract s hsne
    (fun ω => c * SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube M N 0 q
      (originCube d (m : ℤ)) ω)
    (fun R ω => c * SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube M N 0 q R ω)
    (c * ∫ η, SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube M N 0 q
      (originCube d (l : ℤ)) η ∂M.P.toMeasure) t K3 _ ht
    (fun ω => mul_nonneg hc.le (aux_awc_cutoff_nonneg M N q _ ω))
    (fun R _ ω => mul_nonneg hc.le (aux_awc_cutoff_nonneg M N q R ω))
    hsub
    ((SubdiffusiveProcess.CoarseGrainingVocab.integrable_cutoffResponseOnCube M N 0 q _).const_mul c)
    (fun R _ => (SubdiffusiveProcess.CoarseGrainingVocab.integrable_cutoffResponseOnCube M N 0 q R).const_mul c)
    hmean (fun R hR => (hZ3 R hR).1) (fun R hR => (hZ3 R hR).2) hV


theorem aux_awc_psd_quad {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) (s t : ℝ) :
    (fun k => (if k = i then s else 0) + if k = j then t else 0) ⬝ᵥ
      S.mulVec (fun k => (if k = i then s else 0) + if k = j then t else 0)
      = S i i * s ^ 2 + s * t * S i j + s * t * S j i + t ^ 2 * S j j := by
  simp [dotProduct, Matrix.mulVec, mul_add, add_mul, Finset.sum_add_distrib, mul_ite, ite_mul]
  ring

theorem aux_awc_psd_diag_nonneg {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (hpsd : ∀ x : Fin d → ℝ, 0 ≤ x ⬝ᵥ S.mulVec x) (k : Fin d) : 0 ≤ S k k := by
  have h := hpsd (fun m => (if m = k then (1:ℝ) else 0) + if m = k then (0:ℝ) else 0)
  rw [aux_awc_psd_quad S k k 1 0] at h
  linarith

theorem aux_awc_psd_abs_entry_le {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (hsym : S.IsSymm) (hpsd : ∀ x : Fin d → ℝ, 0 ≤ x ⬝ᵥ S.mulVec x) (i j : Fin d) :
    |S i j| ≤ Real.sqrt (S i i) * Real.sqrt (S j j) := by
  have hji : S j i = S i j := by
    have h := congrFun (congrFun hsym i) j
    simpa [Matrix.transpose_apply] using h
  have hdiag := aux_awc_psd_diag_nonneg S hpsd
  have hkey : ∀ x : ℝ, 0 ≤ (S j j) * (x * x) + (2 * S i j) * x + S i i := by
    intro x
    have h := hpsd (fun k => (if k = i then (1:ℝ) else 0) + if k = j then x else 0)
    rw [aux_awc_psd_quad S i j 1 x, hji] at h
    nlinarith [h]
  have hdis := discrim_le_zero hkey
  rw [discrim] at hdis
  have hsq : (S i j) ^ 2 ≤ (S i i) * (S j j) := by nlinarith [hdis]
  calc |S i j| = Real.sqrt ((S i j) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((S i i) * (S j j)) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (S i i) * Real.sqrt (S j j) := Real.sqrt_mul (hdiag i) _

theorem aux_awc_psd_diag_le_trace {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (hpsd : ∀ x : Fin d → ℝ, 0 ≤ x ⬝ᵥ S.mulVec x) (i : Fin d) :
    S i i ≤ Matrix.trace S := by
  rw [Matrix.trace]
  exact Finset.single_le_sum (f := fun k => S k k)
    (fun k _ => aux_awc_psd_diag_nonneg S hpsd k) (Finset.mem_univ i)

theorem aux_awc_psd_abs_entry_le_trace {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (hsym : S.IsSymm) (hpsd : ∀ x : Fin d → ℝ, 0 ≤ x ⬝ᵥ S.mulVec x) (i j : Fin d) :
    |S i j| ≤ Matrix.trace S := by
  have htr0 : 0 ≤ Matrix.trace S :=
    (aux_awc_psd_diag_nonneg S hpsd i).trans (aux_awc_psd_diag_le_trace S hpsd i)
  calc |S i j| ≤ Real.sqrt (S i i) * Real.sqrt (S j j) :=
        aux_awc_psd_abs_entry_le S hsym hpsd i j
    _ ≤ Real.sqrt (Matrix.trace S) * Real.sqrt (Matrix.trace S) := by
        gcongr
        · exact aux_awc_psd_diag_le_trace S hpsd i
        · exact aux_awc_psd_diag_le_trace S hpsd j
    _ = Matrix.trace S := Real.mul_self_sqrt htr0

theorem aux_awc_psd_quad_le_trace {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (hsym : S.IsSymm) (hpsd : ∀ x : Fin d → ℝ, 0 ≤ x ⬝ᵥ S.mulVec x)
    (e : Fin d → ℝ) :
    e ⬝ᵥ S.mulVec e ≤ (∑ i, e i ^ 2) * Matrix.trace S := by
  have hdiag := aux_awc_psd_diag_nonneg S hpsd
  have hexp : e ⬝ᵥ S.mulVec e = ∑ i, ∑ j, e i * (S i j * e j) := by
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
  have hstep1 : ∑ i, ∑ j, e i * (S i j * e j)
      ≤ ∑ i, ∑ j, (|e i| * Real.sqrt (S i i)) * (|e j| * Real.sqrt (S j j)) := by
    refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
    have hb := aux_awc_psd_abs_entry_le S hsym hpsd i j
    have h2 : |e i| * |S i j| * |e j| ≤
        |e i| * (Real.sqrt (S i i) * Real.sqrt (S j j)) * |e j| := by
      have h3 := mul_le_mul_of_nonneg_left hb (abs_nonneg (e i))
      exact mul_le_mul_of_nonneg_right h3 (abs_nonneg (e j))
    calc e i * (S i j * e j) ≤ |e i * (S i j * e j)| := le_abs_self _
      _ = |e i| * |S i j| * |e j| := by rw [abs_mul, abs_mul]; ring
      _ ≤ |e i| * (Real.sqrt (S i i) * Real.sqrt (S j j)) * |e j| := h2
      _ = (|e i| * Real.sqrt (S i i)) * (|e j| * Real.sqrt (S j j)) := by ring
  have hfact : ∑ i, ∑ j, (|e i| * Real.sqrt (S i i)) * (|e j| * Real.sqrt (S j j))
      = (∑ i, |e i| * Real.sqrt (S i i)) ^ 2 := by
    rw [sq, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => by rw [Finset.mul_sum])
  have hcs : (∑ i, |e i| * Real.sqrt (S i i)) ^ 2
      ≤ (∑ i, |e i| ^ 2) * ∑ i, (Real.sqrt (S i i)) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have he2 : (∑ i, |e i| ^ 2) = ∑ i, e i ^ 2 :=
    Finset.sum_congr rfl (fun i _ => sq_abs _)
  have hd2 : (∑ i, (Real.sqrt (S i i)) ^ 2) = Matrix.trace S := by
    rw [Matrix.trace]
    exact Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (hdiag i))
  rw [hexp]
  calc ∑ i, ∑ j, e i * (S i j * e j)
      ≤ ∑ i, ∑ j, (|e i| * Real.sqrt (S i i)) * (|e j| * Real.sqrt (S j j)) := hstep1
    _ = (∑ i, |e i| * Real.sqrt (S i i)) ^ 2 := hfact
    _ ≤ (∑ i, |e i| ^ 2) * ∑ i, (Real.sqrt (S i i)) ^ 2 := hcs
    _ = (∑ i, e i ^ 2) * Matrix.trace S := by rw [he2, hd2]

theorem aux_awc_mono_iter {d : ℕ} (E : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hmono : ∀ k (p : Fin d → ℝ), p ⬝ᵥ (E (k + 1)).mulVec p ≤ p ⬝ᵥ (E k).mulVec p)
    {n m : ℕ} (hnm : n ≤ m) (p : Fin d → ℝ) :
    0 ≤ p ⬝ᵥ (E n - E m).mulVec p := by
  rw [Matrix.sub_mulVec, dotProduct_sub, sub_nonneg]
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih => exact (hmono m p).trans ih

theorem aux_awc_trace_nonneg {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (hpsd : ∀ x : Fin d → ℝ, 0 ≤ x ⬝ᵥ S.mulVec x) : 0 ≤ Matrix.trace S := by
  rw [Matrix.trace]
  exact Finset.sum_nonneg (fun i _ => aux_awc_psd_diag_nonneg S hpsd i)

/-- The deterministic content of both windows: annealed Loewner monotonicity,
the trace-defect identity and the near-extremal choice. -/
theorem aux_awc_windows_det {d : ℕ} (EP ER : ℕ → ℕ → Matrix (Fin d) (Fin d) ℝ)
    (f : ℕ → ℕ → ℝ) (Fk : ℕ → ℝ) (idx : ℕ → ℕ)
    (hPs : ∀ N k, (EP N k).IsSymm) (hRs : ∀ N k, (ER N k).IsSymm)
    (hPmono : ∀ N k (p : Fin d → ℝ), p ⬝ᵥ (EP N (k + 1)).mulVec p ≤ p ⬝ᵥ (EP N k).mulVec p)
    (hRmono : ∀ N k (p : Fin d → ℝ), p ⬝ᵥ (ER N (k + 1)).mulVec p ≤ p ⬝ᵥ (ER N k).mulVec p)
    (hf : ∀ N k, f N k =
      Matrix.trace (EP N k + ER N k - 2 • (1 : Matrix (Fin d) (Fin d) ℝ)) / 2)
    (hF : ∀ k, IsLUB (Set.range fun N => f N k) (Fk k)) (hFanti : Antitone Fk)
    (hnear : ∀ n : ℕ, 1 ≤ n → Fk (4 * n) - (n : ℝ)⁻¹ ≤ f (idx n) (4 * n)) :
    (∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, k ≤ n → n ≤ 4 * k →
      ∑ a : Fin d, ∑ b : Fin d, |EP (idx k) n a b - EP (idx k) (4 * k) a b| ≤
        2 * (d : ℝ) ^ 2 * (Fk k - Fk (4 * k) + (k : ℝ)⁻¹)) ∧
    (∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, k ≤ n → n ≤ 4 * k → ∀ q : Fin d → ℝ,
      q ⬝ᵥ (ER (idx k) k - ER (idx k) n).mulVec q ≤
        (∑ i, q i ^ 2) * (2 * (Fk k - Fk (4 * k) + (k : ℝ)⁻¹))) := by
  have hdiff : ∀ N n m, f N n - f N m =
      (Matrix.trace (EP N n - EP N m) + Matrix.trace (ER N n - ER N m)) / 2 := by
    intro N n m
    rw [hf, hf]
    simp only [Matrix.trace_add, Matrix.trace_sub]
    ring
  have hfanti : ∀ N {n m : ℕ}, n ≤ m → f N m ≤ f N n := by
    intro N n m hnm
    have h1 := aux_awc_trace_nonneg _ (aux_awc_mono_iter (EP N) (hPmono N) hnm)
    have h2 := aux_awc_trace_nonneg _ (aux_awc_mono_iter (ER N) (hRmono N) hnm)
    have := hdiff N n m
    linarith
  have hwin : ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, n ≤ 4 * k → k ≤ n →
      f (idx k) n - f (idx k) (4 * k) ≤ Fk k - Fk (4 * k) + (k : ℝ)⁻¹ := by
    intro k hk n _ hkn
    have hup : f (idx k) n ≤ Fk n := (hF n).1 ⟨idx k, rfl⟩
    have hFn : Fk n ≤ Fk k := hFanti hkn
    have hlow := hnear k hk
    linarith
  refine ⟨?_, ?_⟩
  · intro k hk n hkn hn4
    set D := EP (idx k) n - EP (idx k) (4 * k) with hD
    have hDpsd := aux_awc_mono_iter (EP (idx k)) (hPmono (idx k)) hn4
    have hDs : D.IsSymm := (hPs _ _).sub (hPs _ _)
    have hRpsd := aux_awc_trace_nonneg _ (aux_awc_mono_iter (ER (idx k)) (hRmono (idx k)) hn4)
    have htrD : Matrix.trace D ≤ 2 * (Fk k - Fk (4 * k) + (k : ℝ)⁻¹) := by
      have := hdiff (idx k) n (4 * k)
      have := hwin k hk n hn4 hkn
      rw [hD]
      linarith
    calc ∑ a : Fin d, ∑ b : Fin d, |EP (idx k) n a b - EP (idx k) (4 * k) a b|
        = ∑ a : Fin d, ∑ b : Fin d, |D a b| := by
          simp only [hD, Matrix.sub_apply]
      _ ≤ ∑ _a : Fin d, ∑ _b : Fin d, Matrix.trace D := by
          gcongr with a _ b _
          exact aux_awc_psd_abs_entry_le_trace D hDs hDpsd a b
      _ = (d : ℝ) ^ 2 * Matrix.trace D := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
      _ ≤ (d : ℝ) ^ 2 * (2 * (Fk k - Fk (4 * k) + (k : ℝ)⁻¹)) := by
          gcongr
      _ = 2 * (d : ℝ) ^ 2 * (Fk k - Fk (4 * k) + (k : ℝ)⁻¹) := by ring
  · intro k hk n hkn hn4 q
    set E := ER (idx k) k - ER (idx k) n with hE
    have hEpsd := aux_awc_mono_iter (ER (idx k)) (hRmono (idx k)) hkn
    have hEs : E.IsSymm := (hRs _ _).sub (hRs _ _)
    have hPpsd := aux_awc_trace_nonneg _ (aux_awc_mono_iter (EP (idx k)) (hPmono (idx k)) hkn)
    have htrE : Matrix.trace E ≤ 2 * (Fk k - Fk (4 * k) + (k : ℝ)⁻¹) := by
      have h1 := hdiff (idx k) k n
      have h2 := hwin k hk k (by omega) le_rfl
      have h3 := hfanti (idx k) hn4
      rw [hE]
      linarith
    calc q ⬝ᵥ E.mulVec q ≤ (∑ i, q i ^ 2) * Matrix.trace E :=
          aux_awc_psd_quad_le_trace E hEs hEpsd q
      _ ≤ (∑ i, q i ^ 2) * (2 * (Fk k - Fk (4 * k) + (k : ℝ)⁻¹)) := by
          gcongr


/-- The fixed-direction Neumann window for the stationary family, transported
from the finite-cutoff GMC window. -/
theorem aux_awc_chaos_window (d : ℕ) [NeZero d] :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (N k n : ℕ), k ≤ n →
        ∀ (q : Vec d) (t K3 : ℝ), 0 < t →
        Integrable (fun ω => aux_awc_Jc model N k q ω ^ 3)
          (chaosSampleLaw model).toMeasure →
        ∫ ω, aux_awc_Jc model N k q ω ^ 3 ∂(chaosSampleLaw model).toMeasure ≤ K3 →
        eLpNorm (fun ω => aux_awc_Jc model N n q ω -
            ∫ η, aux_awc_Jc model N k q η ∂(chaosSampleLaw model).toMeasure) 2
            (chaosSampleLaw model).toMeasure ≤
          ENNReal.ofReal (C0 * Real.sqrt (1 + K3) *
            Real.rpow 3 (-((d : ℝ) / 2) * ((n - k : ℕ) : ℝ))) +
          ENNReal.ofReal (Real.sqrt (t *
            (∫ η, aux_awc_Jc model N k q η ∂(chaosSampleLaw model).toMeasure -
              ∫ η, aux_awc_Jc model N n q η ∂(chaosSampleLaw model).toMeasure) +
            K3 / t)) := by
  obtain ⟨C0, hC0, hwin⟩ := aux_awc_gmc_window d
  refine ⟨C0, hC0, ?_⟩
  intro _ _ model N k n hkn q t K3 ht h3i h3
  set c : ℝ := SubdiffusiveProcess.CoarseGrainingVocab.ahom model N with hcdef
  have hc : 0 < c := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model N
  have hidk := aux_awc_ident model N k q
  have hidn := aux_awc_ident model N n q
  have hcube := hidk.comp (measurable_id.pow_const 3)
  have h3int' : Integrable (fun ω => (c * SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube
      model N 0 q (originCube d ((N + k : ℕ) : ℤ)) ω) ^ 3) model.P.toMeasure := by
    have := hcube.integrable_iff.mp h3i
    simpa [Function.comp_def] using this
  have h3' : ∫ ω, (c * SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube
      model N 0 q (originCube d ((N + k : ℕ) : ℤ)) ω) ^ 3 ∂model.P.toMeasure ≤ K3 := by
    have := hcube.integral_eq
    simp only [Function.comp_def, id] at this
    rw [← this]
    exact h3
  have hw := hwin model N (N + k) (N + n) (Nat.le_add_right N k)
    (Nat.add_le_add_left hkn N) q c t K3 hc ht h3int' h3'
  have hmk : ∫ η, aux_awc_Jc model N k q η ∂(chaosSampleLaw model).toMeasure =
      c * ∫ η, SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube model N 0 q
        (originCube d ((N + k : ℕ) : ℤ)) η ∂model.P.toMeasure := by
    rw [hidk.integral_eq, integral_const_mul]
  have hmn : ∫ η, aux_awc_Jc model N n q η ∂(chaosSampleLaw model).toMeasure =
      ∫ η, c * SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube model N 0 q
        (originCube d ((N + n : ℕ) : ℤ)) η ∂model.P.toMeasure :=
    hidn.integral_eq
  have hsub := (hidn.comp (measurable_sub_const
    (c * ∫ η, SubdiffusiveProcess.CoarseGrainingVocab.cutoffResponseOnCube model N 0 q
      (originCube d ((N + k : ℕ) : ℤ)) η ∂model.P.toMeasure))).eLpNorm_eq 2
  have hnk : N + n - (N + k) = n - k := Nat.add_sub_add_left N n k
  rw [hmk, hmn]
  rw [hnk] at hw
  simp only [Function.comp_def] at hsub
  rw [hsub]
  exact hw

theorem aux_awc_domain {d : ℕ}
    (U : ℕ → Homogenization.Book.Ch02.Domain d)
    (hU : ∀ k, (U k : Set (Homogenization.Vec d)) =
      (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
        (pow_pos (by norm_num) k) : Set (SpatialCoordinates d)))
    (k : ℕ) :
    U k = Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (k : ℤ)) := by
  have hcar : (U k : Set (Homogenization.Vec d)) =
      (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (k : ℤ)) :
        Set (Homogenization.Vec d)) := by
    rw [hU k]
    have hr : (0 : ℝ) < (3 : ℝ) ^ (k : ℤ) := by positivity
    simpa [zpow_natCast] using
      (_root_.SubdiffusiveProcess.EllipticRegularity.centeredCube_zero_eq_openCubeSet_originCube
        (d := d) (k : ℤ) hr)
  cases hUk : U k with
  | mk carrier hdom hne =>
      have hcar' : carrier =
          (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (k : ℤ)) :
            Set (Homogenization.Vec d)) := by
        simpa [hUk] using hcar
      subst carrier
      rfl

theorem aux_awc_integral_quad {Om : Type*} [MeasurableSpace Om] (mu : Measure Om)
    {d : ℕ} (M : Om → Matrix (Fin d) (Fin d) ℝ)
    (hint : ∀ i j, Integrable (fun om => M om i j) mu) (e : Fin d → ℝ) :
    (∫ om, e ⬝ᵥ (M om).mulVec e ∂mu)
      = e ⬝ᵥ (Matrix.of fun i j => ∫ om, M om i j ∂mu).mulVec e := by
  have hexp : ∀ om : Om, e ⬝ᵥ (M om).mulVec e = ∑ i, ∑ j, e i * (M om i j * e j) := by
    intro om; simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
  have hrhs : e ⬝ᵥ (Matrix.of fun i j => ∫ om, M om i j ∂mu).mulVec e
      = ∑ i, ∑ j, e i * ((∫ om, M om i j ∂mu) * e j) := by
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
  have hint2 : ∀ i j, Integrable (fun om => e i * (M om i j * e j)) mu :=
    fun i j => ((hint i j).mul_const (e j)).const_mul (e i)
  simp only [hexp]
  rw [hrhs, integral_finsetSum _
    (fun i _ => integrable_finsetSum _ (fun j _ => hint2 i j))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_finsetSum _ (fun j _ => hint2 i j)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [integral_const_mul, integral_mul_const]

theorem aux_awc_integral_trace {Om : Type*} [MeasurableSpace Om] (mu : Measure Om)
    {d : ℕ} (M : Om → Matrix (Fin d) (Fin d) ℝ)
    (hint : ∀ i, Integrable (fun om => M om i i) mu) :
    (∫ om, Matrix.trace (M om) ∂mu) = ∑ i, ∫ om, M om i i ∂mu := by
  simp only [Matrix.trace, Matrix.diag]
  rw [integral_finsetSum _ (fun i _ => hint i)]

theorem aux_awc_single_sq {d : ℕ} (i : Fin d) :
    ∑ k, (Pi.single i (1 : ℝ) : Fin d → ℝ) k ^ 2 = 1 := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem aux_awc_pair_sq {d : ℕ} (i j : Fin d) (hij : i ≠ j) :
    ∑ k, ((Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ) : Fin d → ℝ) k) ^ 2 = 2 := by
  have h : ∀ k : Fin d, ((Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ) : Fin d → ℝ) k) ^ 2 =
      (Pi.single i (1 : ℝ) : Fin d → ℝ) k ^ 2 + (Pi.single j (1 : ℝ) : Fin d → ℝ) k ^ 2 := by
    intro k
    rw [Pi.add_apply]
    by_cases hki : k = i
    · subst hki
      simp [hij]
    · by_cases hkj : k = j
      · subst hkj
        simp [hki]
      · simp [hki, hkj]
  simp only [h, Finset.sum_add_distrib, aux_awc_single_sq]
  norm_num

/-- Matrix-entry windows from fixed-slope windows: each entry of a matrix whose
entries are the polarization combinations of three fixed-slope responses. -/
theorem aux_awc_entries_eLpNorm {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ}
    (R : Ω → Matrix (Fin d) (Fin d) ℝ) (Rbar : Matrix (Fin d) (Fin d) ℝ)
    (F : (Fin d → ℝ) → Ω → ℝ) (m : (Fin d → ℝ) → ℝ) (β : ℝ≥0∞)
    (hR : ∀ ω i j, R ω i j = if i = j then 2 * F (Pi.single i 1) ω else
      F (Pi.single i 1 + Pi.single j 1) ω - F (Pi.single i 1) ω - F (Pi.single j 1) ω)
    (hRbar : ∀ i j, Rbar i j = if i = j then 2 * m (Pi.single i 1) else
      m (Pi.single i 1 + Pi.single j 1) - m (Pi.single i 1) - m (Pi.single j 1))
    (hFm : ∀ q, AEStronglyMeasurable (F q) μ)
    (hβ : ∀ q : Fin d → ℝ, ∑ i, q i ^ 2 ≤ 2 →
      eLpNorm (fun ω => F q ω - m q) 2 μ ≤ β) :
    ∑ i, ∑ j, eLpNorm (fun ω => R ω i j - Rbar i j) 2 μ ≤
      ∑ _i : Fin d, ∑ _j : Fin d, 3 * β := by
  gcongr with i _ j _
  have hβi := hβ (Pi.single i 1) (by rw [aux_awc_single_sq]; norm_num)
  by_cases hij : i = j
  · subst hij
    have hfun : (fun ω => R ω i i - Rbar i i) =
        (2 : ℝ) • fun ω => F (Pi.single i 1) ω - m (Pi.single i 1) := by
      funext ω
      rw [hR ω i i, hRbar i i, ite_eq_left rfl, ite_eq_left rfl]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hfun, eLpNorm_const_smul]
    have h2 : ‖(2 : ℝ)‖ₑ = 2 := by
      rw [Real.enorm_eq_ofReal (by norm_num)]
      simp
    rw [h2]
    calc 2 * eLpNorm (fun ω => F (Pi.single i 1) ω - m (Pi.single i 1)) 2 μ
        ≤ 2 * β := by gcongr
      _ ≤ 3 * β := by gcongr; norm_num
  · have hβj := hβ (Pi.single j 1) (by rw [aux_awc_single_sq]; norm_num)
    have hβij := hβ (Pi.single i 1 + Pi.single j 1) (by rw [aux_awc_pair_sq i j hij])
    have hfun : (fun ω => R ω i j - Rbar i j) =
        fun ω => ((F (Pi.single i 1 + Pi.single j 1) ω - m (Pi.single i 1 + Pi.single j 1)) -
          (F (Pi.single i 1) ω - m (Pi.single i 1))) -
          (F (Pi.single j 1) ω - m (Pi.single j 1)) := by
      funext ω
      rw [hR ω i j, hRbar i j, ite_eq_right hij, ite_eq_right hij]
      ring
    rw [hfun]
    have hA := (hFm (Pi.single i 1 + Pi.single j 1)).sub
      (aestronglyMeasurable_const (b := m (Pi.single i 1 + Pi.single j 1)))
    have hB := (hFm (Pi.single i 1)).sub
      (aestronglyMeasurable_const (b := m (Pi.single i 1)))
    have hC := (hFm (Pi.single j 1)).sub
      (aestronglyMeasurable_const (b := m (Pi.single j 1)))
    calc eLpNorm (fun ω => ((F (Pi.single i 1 + Pi.single j 1) ω -
            m (Pi.single i 1 + Pi.single j 1)) -
          (F (Pi.single i 1) ω - m (Pi.single i 1))) -
          (F (Pi.single j 1) ω - m (Pi.single j 1))) 2 μ
        ≤ eLpNorm (fun ω => (F (Pi.single i 1 + Pi.single j 1) ω -
            m (Pi.single i 1 + Pi.single j 1)) -
          (F (Pi.single i 1) ω - m (Pi.single i 1))) 2 μ +
          eLpNorm (fun ω => F (Pi.single j 1) ω - m (Pi.single j 1)) 2 μ :=
          eLpNorm_sub_le (by norm_num)
      _ ≤ (eLpNorm (fun ω => F (Pi.single i 1 + Pi.single j 1) ω -
            m (Pi.single i 1 + Pi.single j 1)) 2 μ +
          eLpNorm (fun ω => F (Pi.single i 1) ω - m (Pi.single i 1)) 2 μ) +
          eLpNorm (fun ω => F (Pi.single j 1) ω - m (Pi.single j 1)) 2 μ := by
          gcongr
          exact eLpNorm_sub_le (by norm_num)
      _ ≤ (β + β) + β := by gcongr
      _ = 3 * β := by ring

theorem aux_awc_responseJ_eq_ofAEEq {d : ℕ} {U : Homogenization.Book.Ch02.Domain d}
    {a b : Homogenization.Book.Ch02.CoeffOn U}
    (h : Homogenization.Book.Ch02.CoeffOn.AEEq a b) (p q : Vec d) :
    Homogenization.Book.Ch02.responseJ U a p q = Homogenization.Book.Ch02.responseJ U b p q := by
  rw [Homogenization.Book.Ch02.responseJ_eq_coarseMatrices_formula_canonical,
    Homogenization.Book.Ch02.responseJ_eq_coarseMatrices_formula_canonical,
    Homogenization.Book.Ch02.sigmaCoarse_eq_ofAEEq h,
    Homogenization.Book.Ch02.kappaCoarse_eq_ofAEEq h,
    Homogenization.Book.Ch02.sigmaStarInvCoarse_eq_ofAEEq h]

theorem aux_awc_rpow_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (fun k : ℕ => Real.rpow 3 (-((d : ℝ) / 2) * (k : ℝ))) atTop (𝓝 0) := by
  have hb0 : 0 ≤ Real.rpow 3 (-((d : ℝ) / 2)) := Real.rpow_nonneg (by norm_num) _
  have hb1 : Real.rpow 3 (-((d : ℝ) / 2)) < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    have : (0 : ℝ) < d := by exact_mod_cast hd
    linarith
  have heq : (fun k : ℕ => Real.rpow 3 (-((d : ℝ) / 2) * (k : ℝ))) =
      fun k : ℕ => (Real.rpow 3 (-((d : ℝ) / 2))) ^ k := by
    funext k
    change (3 : ℝ) ^ (-((d : ℝ) / 2) * (k : ℝ)) = ((3 : ℝ) ^ (-((d : ℝ) / 2))) ^ k
    rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
  rw [heq]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one hb0 hb1

/-- The final choice of the interpolation parameter and of the scale threshold. -/
theorem aux_awc_eps_choice (K3 D : ℝ) (hK3 : 0 ≤ K3) (hD : 0 < D) (w r : ℕ → ℝ)
    (hw : Tendsto w atTop (𝓝 0)) (hr : Tendsto r atTop (𝓝 0))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ t : ℝ, 0 < t ∧ ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      D * (r k + Real.sqrt (t * (2 * w k) + K3 / t)) ≤ eps := by
  set η : ℝ := eps / (2 * D) with hη
  have hη0 : 0 < η := by positivity
  set t : ℝ := 2 * K3 / η ^ 2 + 1 with ht
  have ht0 : 0 < t := by positivity
  have hKt : K3 / t ≤ η ^ 2 / 2 := by
    rw [div_le_iff₀ ht0, ht]
    have : η ^ 2 / 2 * (2 * K3 / η ^ 2 + 1) = K3 + η ^ 2 / 2 := by
      field_simp
    rw [this]
    have : 0 ≤ η ^ 2 / 2 := by positivity
    linarith
  have hw' : Tendsto (fun k => t * (2 * w k)) atTop (𝓝 0) := by
    simpa using (hw.const_mul 2).const_mul t
  obtain ⟨k1, hk1⟩ := eventually_atTop.mp
    ((tendsto_order.1 hw').2 (η ^ 2 / 2) (by positivity))
  obtain ⟨k2, hk2⟩ := eventually_atTop.mp ((tendsto_order.1 hr).2 η hη0)
  refine ⟨t, ht0, max k1 k2, fun k hk => ?_⟩
  have h1 := hk1 k (le_of_max_le_left hk)
  have h2 := hk2 k (le_of_max_le_right hk)
  have hsq : Real.sqrt (t * (2 * w k) + K3 / t) ≤ η := by
    rw [Real.sqrt_le_left hη0.le]
    linarith
  calc D * (r k + Real.sqrt (t * (2 * w k) + K3 / t)) ≤ D * (η + η) := by
        gcongr
    _ = eps := by rw [hη]; field_simp; norm_num



theorem annealed_window_convergence (d : ℕ) (hd : 2 ≤ d) (hJ : in_J d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : _root_.SubdiffusiveProcess.Model.GMCModel d),
        model.delta ≤ delta0 →
      ∀ (U : ℕ → Homogenization.Book.Ch02.Domain d)
        (hU : ∀ k, (U k : Set (Homogenization.Vec d)) =
          (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
            (pow_pos (by norm_num) k) : Set (SpatialCoordinates d)))
        (a0 : (N k : ℕ) → BilateralField d → Homogenization.Book.Ch02.CoeffOn (U k))
        (ha0 : ∀ N k omega x, (a0 N k omega).toCoeffField x =
          ((Real.exp (((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
              SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
            Real.exp (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) x)) •
            (1 : Homogenization.Mat d)),
      let Pm := fun (N k : ℕ) (omega : BilateralField d) =>
        Homogenization.Book.Ch02.sigmaCoarse (U k) (a0 N k omega)
      let Rm := fun (N k : ℕ) (omega : BilateralField d) =>
        Homogenization.Book.Ch02.sigmaStarInvCoarse (U k) (a0 N k omega)
      let EP := fun (N k : ℕ) (a b : Fin d) =>
        ∫ omega, Pm N k omega a b ∂(chaosSampleLaw model).toMeasure
      let ER := fun (N k : ℕ) (a b : Fin d) =>
        ∫ omega, Rm N k omega a b ∂(chaosSampleLaw model).toMeasure
      let f := fun (N k : ℕ) => (1 / 2 : ℝ) *
        (∫ omega, Matrix.trace (Pm N k omega + Rm N k omega -
          2 • (1 : Matrix (Fin d) (Fin d) ℝ)) ∂(chaosSampleLaw model).toMeasure)
      ∀ (Fk : ℕ → ℝ) (hF : ∀ k : ℕ, IsLUB (Set.range fun N => f N k) (Fk k))
        (idx : ℕ → ℕ)
        (hnear : ∀ n : ℕ, 1 ≤ n → Fk (4 * n) - (n : ℝ)⁻¹ ≤ f (idx n) (4 * n)),
      (∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
          ∀ n ∈ Finset.Icc k (4 * k),
            ∑ a : Fin d, ∑ b : Fin d,
              |EP (idx k) n a b - EP (idx k) (4 * k) a b| ≤ eps) ∧
        ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
          ∀ n ∈ Finset.Icc (2 * k) (4 * k),
            ∑ a : Fin d, ∑ b : Fin d,
              eLpNorm (fun omega => Rm (idx k) n omega a b - ER (idx k) k a b) 2
                (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal eps := by

  classical
  have : NeZero d := ⟨by omega⟩
  obtain ⟨Cc, hCc, hmom⟩ := in_moments d hd hJ
  obtain ⟨dz, hdz, hmom2⟩ := hmom (128 * d) ⟨64 * d, by ring⟩ le_rfl
  obtain ⟨delta0, hdelta0, hfm⟩ := lem_fmono d hd hJ
  obtain ⟨C0, hC0, hchaos⟩ := aux_awc_chaos_window d
  refine ⟨min dz delta0, lt_min hdz hdelta0, ?_⟩
  intro instM instB model hmodel U hU a0 ha0
  have hmz : model.delta ≤ dz := le_trans hmodel (min_le_left _ _)
  have hm0 : model.delta ≤ delta0 := le_trans hmodel (min_le_right _ _)
  have hUeq : U = fun k : ℕ =>
      Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (k : ℤ)) :=
    funext (aux_awc_domain U hU)
  subst hUeq
  intro Pm Rm EP ER f Fk hF idx hnear
  set μc : Measure (BilateralField d) := (chaosSampleLaw model).toMeasure with hμc
  obtain ⟨family, Jsup, -, hfamAE, hJsup, hJsupm, hJsupL, -, -⟩ := hmom2 model hmz
  have hcut : ∀ (N : ℕ) (omega : BilateralField d) (x : SpatialCoordinates d),
      cutoffCoefficient model (fun _ => (0 : C(SpatialCoordinates d, ℝ))) omega N x =
        (Real.exp (((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
          Real.exp (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) x) := by
    simpa using (stationary_family d hd model).1
  have ha0f : ∀ N k omega x, (a0 N k omega).toCoeffField x =
      scalarMatrix (aux_awc_field model N omega x) := by
    intro N k omega x
    rw [ha0]
    simp [aux_awc_field, scalarMatrix]
  have hAE : ∀ (N k : ℕ) (omega : BilateralField d),
      Homogenization.Book.Ch02.CoeffOn.AEEq (a0 N k omega)
        ((family N omega).coeffOn (Homogenization.originCube d (k : ℤ))) := by
    intro N k omega
    have h := hfamAE N omega (Homogenization.originCube d (k : ℤ))
    filter_upwards [h] with x hx
    rw [ha0 N k omega x, hx, hcut]
  have hPeq : ∀ (N k : ℕ) (omega : BilateralField d), Pm N k omega =
      Homogenization.Book.Ch02.sigmaCoarse
        (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (k : ℤ)))
        ((family N omega).coeffOn (Homogenization.originCube d (k : ℤ))) :=
    fun N k omega => Homogenization.Book.Ch02.sigmaCoarse_eq_ofAEEq (hAE N k omega)
  have hReq : ∀ (N k : ℕ) (omega : BilateralField d), Rm N k omega =
      Homogenization.Book.Ch02.sigmaStarInvCoarse
        (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (k : ℤ)))
        ((family N omega).coeffOn (Homogenization.originCube d (k : ℤ))) :=
    fun N k omega => Homogenization.Book.Ch02.sigmaStarInvCoarse_eq_ofAEEq (hAE N k omega)
  -- the family-based annealed matrices of `lem_fmono`
  let EPf : ℕ → ℕ → Matrix (Fin d) (Fin d) ℝ := fun N k i j =>
    ∫ omega, Homogenization.Book.Ch02.sigmaCoarse
      (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (k : ℤ)))
      ((family N omega).coeffOn (Homogenization.originCube d (k : ℤ))) i j ∂μc
  let ERf : ℕ → ℕ → Matrix (Fin d) (Fin d) ℝ := fun N k i j =>
    ∫ omega, Homogenization.Book.Ch02.sigmaStarInvCoarse
      (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (k : ℤ)))
      ((family N omega).coeffOn (Homogenization.originCube d (k : ℤ))) i j ∂μc
  let ff : ℕ → ℕ → ℝ := fun N k =>
    Matrix.trace (EPf N k + ERf N k - 2 • (1 : Matrix (Fin d) (Fin d) ℝ)) / 2
  have hEP : ∀ N k, EP N k = EPf N k := by
    intro N k
    funext i j
    exact integral_congr_ae (Filter.Eventually.of_forall fun omega => by
      simp only [hPeq])
  have hER : ∀ N k, ER N k = ERf N k := by
    intro N k
    funext i j
    exact integral_congr_ae (Filter.Eventually.of_forall fun omega => by
      simp only [hReq])
  have hsubadd := lem_fmono_annealed_subadditivity d hd model family hfamAE
  dsimp only at hsubadd
  obtain ⟨hintfam, hPmono, hRmono, -⟩ := hsubadd
  have hfmono := hfm model hm0 family hfamAE
  dsimp only at hfmono
  obtain ⟨-, -, -, hfanti, Fk', eta, hLUB', -, hFanti', hFconv'⟩ := hfmono
  have hIP : ∀ N k i j, Integrable (fun omega => Pm N k omega i j) μc := by
    intro N k i j
    simp only [hPeq]
    exact (hintfam N k i j).1
  have hIR : ∀ N k i j, Integrable (fun omega => Rm N k omega i j) μc := by
    intro N k i j
    simp only [hReq]
    exact (hintfam N k i j).2
  have hfeq : ∀ N k, f N k = ff N k := by
    intro N k
    have hdiag : ∀ i : Fin d,
        (fun omega => (Pm N k omega + Rm N k omega -
          2 • (1 : Matrix (Fin d) (Fin d) ℝ)) i i) =
        fun omega => (Pm N k omega i i + Rm N k omega i i) - 2 := by
      intro i
      funext omega
      rw [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq]
      simp only [nsmul_eq_mul, Nat.cast_ofNat, mul_one]
    have hsum : ∀ i : Fin d, Integrable
        (fun omega => Pm N k omega i i + Rm N k omega i i) μc :=
      fun i => (hIP N k i i).add (hIR N k i i)
    have hM : ∀ i : Fin d, Integrable (fun omega => (Pm N k omega + Rm N k omega -
        2 • (1 : Matrix (Fin d) (Fin d) ℝ)) i i) μc := by
      intro i
      rw [hdiag i]
      exact (hsum i).sub (integrable_const (2 : ℝ))
    show (1 / 2 : ℝ) * ∫ omega, Matrix.trace (Pm N k omega + Rm N k omega -
      2 • (1 : Matrix (Fin d) (Fin d) ℝ)) ∂μc = ff N k
    rw [aux_awc_integral_trace μc _ hM]
    simp only [ff, Matrix.trace, Matrix.diag_apply, Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hdiag i, integral_sub (hsum i) (integrable_const (2 : ℝ)),
      integral_add (hIP N k i i) (hIR N k i i)]
    rw [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq]
    have hone : μc.real Set.univ = 1 := by
      simp [MeasureTheory.measureReal_def, hμc]
    have h1 : ∫ omega, Pm N k omega i i ∂μc = EPf N k i i := by
      simp only [EPf, hPeq]
    have h2 : ∫ omega, Rm N k omega i i ∂μc = ERf N k i i := by
      simp only [ERf, hReq]
    rw [h1, h2]
    simp only [integral_const, hone, smul_eq_mul, one_mul, nsmul_eq_mul, Nat.cast_ofNat,
      mul_one]
    ring
  have hF' : ∀ k, IsLUB (Set.range fun N => ff N k) (Fk k) := by
    intro k
    have h := hF k
    simp only [hfeq] at h
    exact h
  have hFeq : Fk = Fk' := funext fun k => (hF' k).unique (hLUB' k)
  have hFanti : Antitone Fk := hFeq ▸ hFanti'
  have hFconv : Tendsto Fk atTop (𝓝 eta) := hFeq ▸ hFconv'
  obtain ⟨-, -, -, hw⟩ := near_extremal_member ff Fk hfanti hF' hFanti eta hFconv
  have hnear' : ∀ n : ℕ, 1 ≤ n → Fk (4 * n) - (n : ℝ)⁻¹ ≤ ff (idx n) (4 * n) := by
    intro n hn
    rw [← hfeq]
    exact hnear n hn
  have hsymP : ∀ N k, (EPf N k).IsSymm := by
    intro N k
    ext i j
    rw [Matrix.transpose_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun omega => ?_))
    have h := Homogenization.Book.Ch02.sigmaCoarse_isSymm
      (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (k : ℤ)))
      ((family N omega).coeffOn (Homogenization.originCube d (k : ℤ)))
    simpa [Matrix.transpose_apply] using congrFun (congrFun h i) j
  have hsymR : ∀ N k, (ERf N k).IsSymm := by
    intro N k
    ext i j
    rw [Matrix.transpose_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun omega => ?_))
    have h := Homogenization.Book.Ch02.sigmaStarInvCoarse_isSymm
      (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (k : ℤ)))
      ((family N omega).coeffOn (Homogenization.originCube d (k : ℤ)))
    simpa [Matrix.transpose_apply] using congrFun (congrFun h i) j
  obtain ⟨hDir, hNeu⟩ := aux_awc_windows_det EPf ERf ff Fk idx hsymP hsymR hPmono hRmono
    (fun N k => rfl) hF' hFanti hnear'
  refine ⟨?_, ?_⟩
  · intro eps heps
    have hw2 : Tendsto (fun k : ℕ => 2 * (d : ℝ) ^ 2 *
        (Fk k - Fk (4 * k) + (k : ℝ)⁻¹)) atTop (𝓝 0) := by
      simpa using hw.const_mul (2 * (d : ℝ) ^ 2)
    obtain ⟨k1, hk1⟩ := eventually_atTop.mp ((tendsto_order.1 hw2).2 eps heps)
    refine ⟨max k1 1, fun k hk n hn => ?_⟩
    have hk1' := hk1 k (le_of_max_le_left hk)
    have hk1'' : 1 ≤ k := le_of_max_le_right hk
    rw [Finset.mem_Icc] at hn
    have h := hDir k hk1'' n hn.1 hn.2
    rw [hEP (idx k) n, hEP (idx k) (4 * k)]
    exact h.trans hk1'.le
  · intro eps heps
    have hxi3 : (3 : ℝ) ≤ ((128 * d : ℕ) : ℝ) := by
      have : 3 ≤ 128 * d := by omega
      exact_mod_cast this
    set B1 : ℝ := Cc * ((128 * d : ℕ) : ℝ) * Real.log (2 + ((128 * d : ℕ) : ℝ)) *
      model.delta ^ 2 with hB1
    have hB10 : 0 ≤ B1 := by
      have hlog : 0 ≤ Real.log (2 + ((128 * d : ℕ) : ℝ)) :=
        Real.log_nonneg (by have : (0 : ℝ) ≤ ((128 * d : ℕ) : ℝ) := by positivity
                            linarith)
      rw [hB1]
      positivity
    have hJsup0 : ∀ N k omega, 0 ≤ Jsup N k omega := by
      intro N k omega
      have i0 : Fin d := ⟨0, by omega⟩
      have hmem := (hJsup N k omega).2 ⟨Pi.single i0 1, aux_awc_single_sq i0, rfl⟩
      exact (Homogenization.Book.Ch02.responseJ_nonneg _ _ _ _).trans hmem
    have hmom3 : ∀ N k, Integrable (fun omega => Jsup N k omega ^ 3) μc ∧
        ∫ omega, Jsup N k omega ^ 3 ∂μc ≤ B1 ^ 3 := fun N k =>
      aux_awc_third_moment (Jsup N k) (hJsupm N k) (hJsup0 N k) _ B1 hxi3 hB10 (hJsupL N k)
    set K3 : ℝ := 56 * (1 + B1 ^ 3) with hK3
    have hK30 : 0 ≤ K3 := by positivity
    have hJc_eq : ∀ N k q omega, aux_awc_Jc model N k q omega =
        (1 / 2 : ℝ) * q ⬝ᵥ (Rm N k omega).mulVec q :=
      fun N k q omega => aux_awc_Jc_eq_responseJ model N k q omega (a0 N k omega)
        (ha0f N k omega)
    have hJc_le : ∀ N k q omega, aux_awc_Jc model N k q omega ≤
        (∑ i, q i ^ 2) * (1 + Jsup N k omega) := by
      intro N k q omega
      rw [hJc_eq]
      apply aux_awc_quad_le_scaled
      intro e he
      have hsym : Homogenization.Book.Ch02.CoeffOn.IsSymmetric (a0 N k omega) := by
        filter_upwards with x
        rw [ha0 N k omega x]
        exact Homogenization.scalarMatrix_isSymm _
      have h1 := aux_awc_star_unit_le hJ _ (a0 N k omega) hsym e he
      have h2 : Homogenization.Book.Ch02.responseJ _ (a0 N k omega) e e ≤ Jsup N k omega := by
        rw [aux_awc_responseJ_eq_ofAEEq (hAE N k omega)]
        exact (hJsup N k omega).2 ⟨e, he, rfl⟩
      linarith
    have hJcm : ∀ N k q, AEStronglyMeasurable (aux_awc_Jc model N k q) μc :=
      fun N k q => (aux_awc_ident model N k q).aemeasurable_fst.aestronglyMeasurable
    have hmomJc : ∀ N k (q : Fin d → ℝ), ∑ i, q i ^ 2 ≤ 2 →
        Integrable (fun omega => aux_awc_Jc model N k q omega ^ 3) μc ∧
        ∫ omega, aux_awc_Jc model N k q omega ^ 3 ∂μc ≤ K3 := by
      intro N k q hq
      have hs0 : 0 ≤ ∑ i, q i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
      have hpt : ∀ omega, aux_awc_Jc model N k q omega ^ 3 ≤
          56 * (1 + Jsup N k omega ^ 3) := by
        intro omega
        have h := aux_awc_cube_le _ _ _ (aux_awc_Jc_nonneg model N k q omega)
          (hJsup0 N k omega) hs0 (hJc_le N k q omega)
        have hs3 : (∑ i, q i ^ 2) ^ 3 ≤ 8 := by
          calc (∑ i, q i ^ 2) ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ hs0 hq 3
            _ = 8 := by norm_num
        have h0 : 0 ≤ 1 + Jsup N k omega ^ 3 := by
          have := hJsup0 N k omega
          positivity
        nlinarith
      have hbint : Integrable (fun omega => 56 * (1 + Jsup N k omega ^ 3)) μc :=
        ((integrable_const 1).add (hmom3 N k).1).const_mul 56
      have hint : Integrable (fun omega => aux_awc_Jc model N k q omega ^ 3) μc := by
        refine hbint.mono' ((hJcm N k q).pow 3) ?_
        filter_upwards with omega
        rw [Real.norm_of_nonneg (pow_nonneg (aux_awc_Jc_nonneg model N k q omega) 3)]
        exact hpt omega
      refine ⟨hint, ?_⟩
      calc ∫ omega, aux_awc_Jc model N k q omega ^ 3 ∂μc
          ≤ ∫ omega, 56 * (1 + Jsup N k omega ^ 3) ∂μc := integral_mono hint hbint hpt
        _ = 56 * (1 + ∫ omega, Jsup N k omega ^ 3 ∂μc) := by
            rw [integral_const_mul, integral_add (integrable_const 1) (hmom3 N k).1,
              integral_const, probReal_univ, one_smul]
        _ ≤ K3 := by
            have := (hmom3 N k).2
            rw [hK3]
            linarith
    have hJcint : ∀ N k q, Integrable (aux_awc_Jc model N k q) μc := fun N k q =>
      (aux_awc_ident model N k q).integrable_iff.mpr
        ((SubdiffusiveProcess.CoarseGrainingVocab.integrable_cutoffResponseOnCube model N 0 q _).const_mul _)
    have hJc_mean : ∀ N k q, ∫ omega, aux_awc_Jc model N k q omega ∂μc =
        (1 / 2 : ℝ) * q ⬝ᵥ (ERf N k).mulVec q := by
      intro N k q
      rw [integral_congr_ae (Filter.Eventually.of_forall (hJc_eq N k q)),
        integral_const_mul, aux_awc_integral_quad μc (Rm N k) (hIR N k) q]
      congr 3
      ext i j
      simp only [Matrix.of_apply, ERf, hReq]
    have hwnn : ∀ k : ℕ, 0 ≤ Fk k - Fk (4 * k) + (k : ℝ)⁻¹ := by
      intro k
      have h1 : Fk (4 * k) ≤ Fk k := hFanti (by omega)
      have h2 : 0 ≤ (k : ℝ)⁻¹ := by positivity
      linarith
    have hslope : ∀ t : ℝ, 0 < t → ∀ k : ℕ, 1 ≤ k →
        ∀ n ∈ Finset.Icc (2 * k) (4 * k), ∀ q : Fin d → ℝ, ∑ i, q i ^ 2 ≤ 2 →
        eLpNorm (fun omega => aux_awc_Jc model (idx k) n q omega -
            ∫ η, aux_awc_Jc model (idx k) k q η ∂μc) 2 μc ≤
          ENNReal.ofReal (C0 * Real.sqrt (1 + K3) *
              Real.rpow 3 (-((d : ℝ) / 2) * (k : ℝ)) +
            Real.sqrt (t * (2 * (Fk k - Fk (4 * k) + (k : ℝ)⁻¹)) + K3 / t)) := by
      intro t ht k hk n hn q hq
      rw [Finset.mem_Icc] at hn
      have hkn : k ≤ n := by omega
      obtain ⟨h3i, h3⟩ := hmomJc (idx k) k q hq
      have hmain := hchaos model (idx k) k n hkn q t K3 ht h3i h3
      refine hmain.trans ?_
      have hr0 : 0 ≤ C0 * Real.sqrt (1 + K3) *
          Real.rpow 3 (-((d : ℝ) / 2) * ((n - k : ℕ) : ℝ)) :=
        mul_nonneg (mul_nonneg hC0.le (Real.sqrt_nonneg _)) (Real.rpow_nonneg (by norm_num) _)
      rw [← ENNReal.ofReal_add hr0 (Real.sqrt_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC0.le (Real.sqrt_nonneg _))
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hkk : (k : ℝ) ≤ ((n - k : ℕ) : ℝ) := by exact_mod_cast (by omega : k ≤ n - k)
        have hd0 : 0 ≤ (d : ℝ) / 2 := by positivity
        nlinarith
      · apply Real.sqrt_le_sqrt
        have hdef := hNeu k hk n hkn hn.2 q
        rw [Matrix.sub_mulVec, dotProduct_sub] at hdef
        rw [hJc_mean, hJc_mean]
        have hs0 : 0 ≤ ∑ i, q i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
        have hw0 := hwnn k
        have hbound : (1 / 2 : ℝ) * q ⬝ᵥ (ERf (idx k) k).mulVec q -
            (1 / 2 : ℝ) * q ⬝ᵥ (ERf (idx k) n).mulVec q ≤
            2 * (Fk k - Fk (4 * k) + (k : ℝ)⁻¹) := by
          have : (∑ i, q i ^ 2) * (2 * (Fk k - Fk (4 * k) + (k : ℝ)⁻¹)) ≤
              2 * (2 * (Fk k - Fk (4 * k) + (k : ℝ)⁻¹)) :=
            mul_le_mul_of_nonneg_right hq (by positivity)
          linarith
        have := mul_le_mul_of_nonneg_left hbound ht.le
        linarith
    have hstar : ∀ (N j : ℕ) (omega : BilateralField d) (a b : Fin d),
        Rm N j omega a b = if a = b then 2 * aux_awc_Jc model N j (Pi.single a 1) omega else
          aux_awc_Jc model N j (Pi.single a 1 + Pi.single b 1) omega -
            aux_awc_Jc model N j (Pi.single a 1) omega -
            aux_awc_Jc model N j (Pi.single b 1) omega := fun N j omega a b =>
      aux_annealed_limit_response_transport_star_entry_response (originCube d (j : ℤ))
        (aux_awc_field model N omega) (aux_awc_field_pos model N omega) (a0 N j omega)
        (ha0f N j omega) a b
    have hERentry : ∀ (N j : ℕ) (a b : Fin d),
        ER N j a b = if a = b then 2 * ∫ η, aux_awc_Jc model N j (Pi.single a 1) η ∂μc else
          (∫ η, aux_awc_Jc model N j (Pi.single a 1 + Pi.single b 1) η ∂μc) -
            (∫ η, aux_awc_Jc model N j (Pi.single a 1) η ∂μc) -
            ∫ η, aux_awc_Jc model N j (Pi.single b 1) η ∂μc := by
      intro N j a b
      show ∫ omega, Rm N j omega a b ∂μc = _
      rw [integral_congr_ae (Filter.Eventually.of_forall (fun omega => hstar N j omega a b))]
      by_cases hab : a = b
      · simp only [ite_eq_left hab]
        rw [integral_const_mul]
      · simp only [ite_eq_right hab]
        rw [integral_sub, integral_sub]
        all_goals first
          | exact hJcint N j _
          | exact (hJcint N j _).sub (hJcint N j _)
    have hentries : ∀ t : ℝ, 0 < t → ∀ k : ℕ, 1 ≤ k →
        ∀ n ∈ Finset.Icc (2 * k) (4 * k),
        ∑ a : Fin d, ∑ b : Fin d,
          eLpNorm (fun omega => Rm (idx k) n omega a b - ER (idx k) k a b) 2 μc ≤
        ∑ _a : Fin d, ∑ _b : Fin d, 3 * ENNReal.ofReal (C0 * Real.sqrt (1 + K3) *
              Real.rpow 3 (-((d : ℝ) / 2) * (k : ℝ)) +
            Real.sqrt (t * (2 * (Fk k - Fk (4 * k) + (k : ℝ)⁻¹)) + K3 / t)) := by
      intro t ht k hk n hn
      exact aux_awc_entries_eLpNorm (Rm (idx k) n) (ER (idx k) k)
        (fun q => aux_awc_Jc model (idx k) n q)
        (fun q => ∫ η, aux_awc_Jc model (idx k) k q η ∂μc) _
        (hstar (idx k) n) (hERentry (idx k) k) (fun q => hJcm (idx k) n q)
        (fun q hq => hslope t ht k hk n hn q hq)
    have hr : Tendsto (fun k : ℕ => C0 * Real.sqrt (1 + K3) *
        Real.rpow 3 (-((d : ℝ) / 2) * (k : ℝ))) atTop (𝓝 0) := by
      simpa using (aux_awc_rpow_tendsto d (by omega)).const_mul (C0 * Real.sqrt (1 + K3))
    obtain ⟨t, ht, k1, hk1⟩ := aux_awc_eps_choice K3 (3 * (d : ℝ) ^ 2) hK30 (by positivity)
      (fun k : ℕ => Fk k - Fk (4 * k) + (k : ℝ)⁻¹)
      (fun k : ℕ => C0 * Real.sqrt (1 + K3) * Real.rpow 3 (-((d : ℝ) / 2) * (k : ℝ)))
      hw hr eps heps
    refine ⟨max k1 1, fun k hk n hn => ?_⟩
    have hk1' := hk1 k (le_of_max_le_left hk)
    have hk1'' : 1 ≤ k := le_of_max_le_right hk
    refine (hentries t ht k hk1'' n hn).trans ?_
    set ρ : ℝ := C0 * Real.sqrt (1 + K3) * Real.rpow 3 (-((d : ℝ) / 2) * (k : ℝ)) +
      Real.sqrt (t * (2 * (Fk k - Fk (4 * k) + (k : ℝ)⁻¹)) + K3 / t) with hρ
    have hρ0 : 0 ≤ ρ := add_nonneg
      (mul_nonneg (mul_nonneg hC0.le (Real.sqrt_nonneg _)) (Real.rpow_nonneg (by norm_num) _))
      (Real.sqrt_nonneg _)
    have hsum : ∑ _a : Fin d, ∑ _b : Fin d, 3 * ENNReal.ofReal ρ =
        ENNReal.ofReal (3 * (d : ℝ) ^ 2 * ρ) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
      rw [show ENNReal.ofReal 3 = 3 by simp]
      ring
    rw [hsum]
    exact ENNReal.ofReal_le_ofReal hk1'

end SubdiffusiveProcess.Paper
