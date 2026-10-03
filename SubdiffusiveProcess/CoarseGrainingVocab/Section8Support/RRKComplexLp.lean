module

public import Mathlib.Analysis.Complex.OperatorNorm
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.HeatKernelRegularity

@[expose] public section

/-!
# Complexifying `L²(μ;ℝ)` and its bounded operators

Mathlib's continuous functional calculus lives on **complex** C⋆-algebras
(`CStarAlgebra` is a `NormedAlgebra ℂ`), and `Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ` is not one.
But `Lp ℂ 2 μ` is a complex Hilbert space
(`Mathlib/MeasureTheory/Function/L2Space.lean`), so `Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ` *is* a
C⋆-algebra (`Mathlib/Analysis/CStarAlgebra/ContinuousLinearMap.lean`) and carries the
real continuous functional calculus for self-adjoint elements.  This file builds the
transfer both ways.

* `toC`, `reC`, `imC` — the inclusion `L²(μ;ℝ) → L²(μ;ℂ)` and the real and imaginary
  parts, all obtained from `ContinuousLinearMap.compLpL`;
* `cxOp R` — the complexification of a real bounded operator, a **unital ring
  homomorphism** (`cxOp_one`, `cxOp_mul`, `cxOp_pow`) sending symmetric operators to
  self-adjoint ones (`isSelfAdjoint_cxOp`);
* `realOp T` — the real operator `f ↦ Re (T f)`, `1`-Lipschitz in `T`
  (`lipschitzWith_realOp`), sending self-adjoint operators to symmetric ones
  (`isSymmetricOp_realOp`), and satisfying the one multiplicativity identity the
  construction needs, `realOp (cxOp R * T) = R ∘ realOp T` (`realOp_cxOp_mul`).

`realOp` is *not* multiplicative in general — `realOp (T * S)` and
`realOp T ∘ realOp S` differ by `imC (T (I · imC (S ·)))` — which is why
`realOp_cxOp_mul` keeps the manifestly real factor `cxOp R` on the left.  Every
identity the (RRK) operator half needs is of that shape.
-/

open MeasureTheory Complex
open scoped RealInnerProductSpace ENNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKComplexLp

open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.HeatKernelRegularity

variable {X : Type*} [MeasurableSpace X] {mu : Measure X}

/-- The real-to-complex inclusion `L²(μ;ℝ) → L²(μ;ℂ)`. -/
def toC (mu : Measure X) : Lp ℝ 2 mu →L[ℝ] Lp ℂ 2 mu := Complex.ofRealCLM.compLpL 2 mu

/-- The real part `L²(μ;ℂ) → L²(μ;ℝ)`. -/
def reC (mu : Measure X) : Lp ℂ 2 mu →L[ℝ] Lp ℝ 2 mu := Complex.reCLM.compLpL 2 mu

/-- The imaginary part `L²(μ;ℂ) → L²(μ;ℝ)`. -/
def imC (mu : Measure X) : Lp ℂ 2 mu →L[ℝ] Lp ℝ 2 mu := Complex.imCLM.compLpL 2 mu

theorem coeFn_toC (f : Lp ℝ 2 mu) : (toC mu f : X → ℂ) =ᵐ[mu] fun x => ((f x : ℝ) : ℂ) :=
  ContinuousLinearMap.coeFn_compLpL _ _

theorem coeFn_reC (u : Lp ℂ 2 mu) : (reC mu u : X → ℝ) =ᵐ[mu] fun x => (u x).re :=
  ContinuousLinearMap.coeFn_compLpL _ _

theorem coeFn_imC (u : Lp ℂ 2 mu) : (imC mu u : X → ℝ) =ᵐ[mu] fun x => (u x).im :=
  ContinuousLinearMap.coeFn_compLpL _ _

@[simp] theorem reC_toC (f : Lp ℝ 2 mu) : reC mu (toC mu f) = f := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_reC (toC mu f), coeFn_toC f] with x h1 h2
  rw [h1, h2, Complex.ofReal_re]

@[simp] theorem imC_toC (f : Lp ℝ 2 mu) : imC mu (toC mu f) = 0 := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_imC (toC mu f), coeFn_toC f, Lp.coeFn_zero ℝ 2 mu] with x h1 h2 h3
  rw [h1, h2, h3, Complex.ofReal_im]
  rfl

theorem toC_reC_add_smul (u : Lp ℂ 2 mu) :
    toC mu (reC mu u) + Complex.I • toC mu (imC mu u) = u := by
  rw [Lp.ext_iff]
  filter_upwards [Lp.coeFn_add (toC mu (reC mu u)) (Complex.I • toC mu (imC mu u)),
    Lp.coeFn_smul Complex.I (toC mu (imC mu u)), coeFn_toC (reC mu u), coeFn_toC (imC mu u),
    coeFn_reC u, coeFn_imC u] with x h1 h2 h3 h4 h5 h6
  rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, h5, h6, smul_eq_mul]
  rw [mul_comm]
  exact Complex.re_add_im (u x)

/-- The complex inner product of two real functions is the real inner product. -/
theorem inner_toC_toC (f g : Lp ℝ 2 mu) :
    inner ℂ (toC mu f) (toC mu g) = ((⟪f, g⟫ : ℝ) : ℂ) := by
  rw [L2.inner_def]
  have hae : ∀ᵐ x ∂mu,
      inner ℂ ((toC mu f) x) ((toC mu g) x) = (((f x * g x : ℝ)) : ℂ) := by
    filter_upwards [coeFn_toC f, coeFn_toC g] with x h1 h2
    rw [h1, h2, RCLike.inner_apply, Complex.conj_ofReal]
    push_cast
    ring
  rw [integral_congr_ae hae, integral_complex_ofReal, inner_eq_integral f g]

/-- Reading a real pairing off a complex one. -/
theorem re_inner_toC (w : Lp ℂ 2 mu) (g : Lp ℝ 2 mu) :
    (inner ℂ w (toC mu g)).re = ⟪reC mu w, g⟫ := by
  conv_lhs => rw [← toC_reC_add_smul w]
  rw [inner_add_left, inner_smul_left, inner_toC_toC, inner_toC_toC]
  simp

@[simp] theorem reC_smul_I (u : Lp ℂ 2 mu) : reC mu (Complex.I • u) = - imC mu u := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_reC (Complex.I • u), Lp.coeFn_smul Complex.I u, coeFn_imC u,
    Lp.coeFn_neg (imC mu u)] with x h1 h2 h3 h4
  rw [h1, h2, h4, Pi.neg_apply, h3, Pi.smul_apply, smul_eq_mul, Complex.I_mul_re]

@[simp] theorem imC_smul_I (u : Lp ℂ 2 mu) : imC mu (Complex.I • u) = reC mu u := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_imC (Complex.I • u), Lp.coeFn_smul Complex.I u, coeFn_reC u]
    with x h1 h2 h3
  rw [h1, h2, h3, Pi.smul_apply, smul_eq_mul, Complex.I_mul_im]

/-- An `ℝ`-linear continuous map between complex normed spaces that commutes with
multiplication by `I` is `ℂ`-linear. -/
def ofRealLinearCLM {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (T : E →L[ℝ] F)
    (h : ∀ u, T (Complex.I • u) = Complex.I • T u) : E →L[ℂ] F where
  toFun := T
  map_add' := T.map_add
  map_smul' c u := by
    have hsmul : ∀ (r : ℝ) (v : E), (r : ℝ) • v = ((r : ℂ)) • v := fun r v => by
      rw [← Complex.coe_algebraMap, algebraMap_smul]
    have hsmul' : ∀ (r : ℝ) (v : F), (r : ℝ) • v = ((r : ℂ)) • v := fun r v => by
      rw [← Complex.coe_algebraMap, algebraMap_smul]
    have hc : c • u = ((c.re : ℂ)) • u + ((c.im : ℂ)) • ((Complex.I : ℂ) • u) := by
      rw [smul_smul, ← add_smul, Complex.re_add_im]
    have hd : c • T u = ((c.re : ℂ)) • T u + ((c.im : ℂ)) • ((Complex.I : ℂ) • T u) := by
      rw [smul_smul, ← add_smul, Complex.re_add_im]
    simp only [RingHom.id_apply]
    rw [hc, hd, ← hsmul, ← hsmul, map_add, T.map_smul, T.map_smul, h, hsmul', hsmul']
  cont := T.continuous

@[simp] theorem ofRealLinearCLM_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (T : E →L[ℝ] F)
    (h : ∀ u, T (Complex.I • u) = Complex.I • T u) (u : E) :
    ofRealLinearCLM T h u = T u := rfl

/-- The complexification of a real bounded operator on `L²`. -/
def cxOp (R : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu) : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu :=
  ofRealLinearCLM
    ((toC mu).comp (R.comp (reC mu)) + Complex.I • ((toC mu).comp (R.comp (imC mu))))
    (by
      intro u
      change toC mu (R (reC mu (Complex.I • u))) +
        Complex.I • toC mu (R (imC mu (Complex.I • u))) =
        Complex.I • (toC mu (R (reC mu u)) + Complex.I • toC mu (R (imC mu u)))
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smul_apply, reC_smul_I, imC_smul_I, map_neg]
      rw [smul_add, smul_smul, Complex.I_mul_I]
      module)

theorem cxOp_apply (R : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu) (u : Lp ℂ 2 mu) :
    cxOp R u = toC mu (R (reC mu u)) + Complex.I • toC mu (R (imC mu u)) := rfl

@[simp] theorem reC_cxOp (R : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu) (u : Lp ℂ 2 mu) :
    reC mu (cxOp R u) = R (reC mu u) := by
  rw [cxOp_apply, map_add, reC_smul_I, reC_toC, imC_toC, neg_zero, add_zero]

@[simp] theorem imC_cxOp (R : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu) (u : Lp ℂ 2 mu) :
    imC mu (cxOp R u) = R (imC mu u) := by
  rw [cxOp_apply, map_add, imC_smul_I, imC_toC, reC_toC, zero_add]

@[simp] theorem cxOp_toC (R : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu) (f : Lp ℝ 2 mu) :
    cxOp R (toC mu f) = toC mu (R f) := by
  rw [cxOp_apply, reC_toC, imC_toC, map_zero, map_zero, smul_zero, add_zero]

@[simp] theorem cxOp_one : cxOp (1 : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu) = 1 := by
  refine ContinuousLinearMap.ext fun u => ?_
  rw [cxOp_apply]
  exact toC_reC_add_smul u

theorem cxOp_mul (R S : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu) : cxOp (R * S) = cxOp R * cxOp S := by
  refine ContinuousLinearMap.ext fun u => ?_
  rw [ContinuousLinearMap.mul_apply, cxOp_apply, cxOp_apply, reC_cxOp, imC_cxOp]
  rfl

theorem cxOp_pow (R : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu) (n : ℕ) : cxOp (R ^ n) = (cxOp R) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, cxOp_mul, ih]

/-- The complex inner product in terms of real ones. -/
theorem inner_decomp (p q c d : Lp ℝ 2 mu) :
    inner ℂ (toC mu p + Complex.I • toC mu q) (toC mu c + Complex.I • toC mu d)
      = ((⟪p, c⟫ + ⟪q, d⟫ : ℝ) : ℂ) + Complex.I * ((⟪p, d⟫ - ⟪q, c⟫ : ℝ) : ℂ) := by
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    inner_toC_toC, Complex.conj_I]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The complexification of a symmetric real operator is self-adjoint. -/
theorem isSelfAdjoint_cxOp {R : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu} (hR : IsSymmetricOp R) :
    IsSelfAdjoint (cxOp R) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u v
  have hu : u = toC mu (reC mu u) + Complex.I • toC mu (imC mu u) := (toC_reC_add_smul u).symm
  have hv : v = toC mu (reC mu v) + Complex.I • toC mu (imC mu v) := (toC_reC_add_smul v).symm
  have hLu : (cxOp R : Lp ℂ 2 mu →ₗ[ℂ] Lp ℂ 2 mu) u = cxOp R u := rfl
  have hLv : (cxOp R : Lp ℂ 2 mu →ₗ[ℂ] Lp ℂ 2 mu) v = cxOp R v := rfl
  rw [hLu, hLv, cxOp_apply R u, cxOp_apply R v]
  conv_lhs => rw [hv]
  conv_rhs => rw [hu]
  rw [inner_decomp, inner_decomp, hR, hR, hR, hR]

/-- The real operator determined by a complex one: `f ↦ Re (T f)`. -/
def realOp (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu :=
  (reC mu).comp ((T.restrictScalars ℝ).comp (toC mu))

theorem realOp_apply (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) (f : Lp ℝ 2 mu) :
    realOp T f = reC mu (T (toC mu f)) := rfl

theorem realOp_cxOp (R : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu) : realOp (cxOp R) = R := by
  refine ContinuousLinearMap.ext fun f => ?_
  rw [realOp_apply, cxOp_toC, reC_toC]

/-- The real operator of a symmetric complex one is symmetric. -/
theorem isSymmetricOp_realOp {T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu} (hT : IsSelfAdjoint T) :
    IsSymmetricOp (realOp T) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at hT
  intro f g
  have h1 : ⟪realOp T f, g⟫ = (inner ℂ (T (toC mu f)) (toC mu g)).re := by
    rw [realOp_apply, re_inner_toC]
  have h2 : ⟪realOp T g, f⟫ = (inner ℂ (T (toC mu g)) (toC mu f)).re := by
    rw [realOp_apply, re_inner_toC]
  have h3 : inner ℂ (T (toC mu f)) (toC mu g) = inner ℂ (toC mu f) (T (toC mu g)) := hT _ _
  have h4 : (starRingEnd ℂ) (inner ℂ (T (toC mu g)) (toC mu f))
      = inner ℂ (toC mu f) (T (toC mu g)) := inner_conj_symm _ _
  rw [h1, h3, ← h4, Complex.conj_re, ← h2, real_inner_comm]

/-- `realOp` intertwines left multiplication by a complexified real operator with
left composition by that operator. -/
theorem realOp_cxOp_mul (R : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu) (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) :
    realOp ((cxOp R) * T) = R.comp (realOp T) := by
  refine ContinuousLinearMap.ext fun f => ?_
  rw [realOp_apply, ContinuousLinearMap.mul_apply, reC_cxOp]
  rfl

theorem realOp_sub (T S : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) :
    realOp (T - S) = realOp T - realOp S := by
  refine ContinuousLinearMap.ext fun f => ?_
  simp only [realOp_apply, ContinuousLinearMap.sub_apply, map_sub]

theorem norm_toC_le (f : Lp ℝ 2 mu) : ‖toC mu f‖ ≤ ‖f‖ := by
  have h := (Complex.ofRealCLM.compLpL 2 mu).le_opNorm f
  have hb : ‖(Complex.ofRealCLM.compLpL 2 mu : Lp ℝ 2 mu →L[ℝ] Lp ℂ 2 mu)‖ ≤ 1 := by
    simpa [Complex.ofRealCLM_norm] using
      (ContinuousLinearMap.norm_compLpL_le (p := (2 : ℝ≥0∞)) (μ := mu) Complex.ofRealCLM)
  calc ‖toC mu f‖ ≤ ‖(Complex.ofRealCLM.compLpL 2 mu : Lp ℝ 2 mu →L[ℝ] Lp ℂ 2 mu)‖ * ‖f‖ := h
    _ ≤ 1 * ‖f‖ := by
        exact mul_le_mul_of_nonneg_right hb (norm_nonneg f)
    _ = ‖f‖ := one_mul _

theorem norm_reC_le (u : Lp ℂ 2 mu) : ‖reC mu u‖ ≤ ‖u‖ := by
  have h := (Complex.reCLM.compLpL 2 mu).le_opNorm u
  have hb : ‖(Complex.reCLM.compLpL 2 mu : Lp ℂ 2 mu →L[ℝ] Lp ℝ 2 mu)‖ ≤ 1 := by
    simpa [Complex.reCLM_norm] using
      (ContinuousLinearMap.norm_compLpL_le (p := (2 : ℝ≥0∞)) (μ := mu) Complex.reCLM)
  calc ‖reC mu u‖ ≤ ‖(Complex.reCLM.compLpL 2 mu : Lp ℂ 2 mu →L[ℝ] Lp ℝ 2 mu)‖ * ‖u‖ := h
    _ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg u)
    _ = ‖u‖ := one_mul _

theorem norm_realOp_le (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) : ‖realOp T‖ ≤ ‖T‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) fun f => ?_
  calc ‖realOp T f‖ ≤ ‖T (toC mu f)‖ := by rw [realOp_apply]; exact norm_reC_le _
    _ ≤ ‖T‖ * ‖toC mu f‖ := T.le_opNorm _
    _ ≤ ‖T‖ * ‖f‖ := mul_le_mul_of_nonneg_left (norm_toC_le f) (norm_nonneg T)

theorem lipschitzWith_realOp :
    LipschitzWith 1 (realOp (mu := mu)) := by
  refine LipschitzWith.of_dist_le_mul fun T S => ?_
  rw [dist_eq_norm, dist_eq_norm, ← realOp_sub, NNReal.coe_one, one_mul]
  exact norm_realOp_le _

theorem continuous_realOp : Continuous (realOp (mu := mu)) :=
  lipschitzWith_realOp.continuous

/-! ### The real structure

Pointwise complex conjugation `J` is an `ℝ`-linear isometric involution of `L²(μ;ℂ)`
whose fixed points are exactly the real functions.  Conjugating an operator, `T ↦ J T J`,
is an `ℝ`-linear `⋆`-automorphism of the C⋆-algebra `Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ` fixing
`cxOp R`.  Its fixed operators are exactly the complexifications of real ones
(`cxOp_realOp_of_conjOp`), and on those `realOp` *is* multiplicative
(`realOp_mul_of_conjOp`). -/

/-- Pointwise complex conjugation on `L²(μ;ℂ)`. -/
def conjC (mu : Measure X) : Lp ℂ 2 mu →L[ℝ] Lp ℂ 2 mu :=
  (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.compLpL 2 mu

theorem coeFn_conjC (u : Lp ℂ 2 mu) :
    (conjC mu u : X → ℂ) =ᵐ[mu] fun x => (starRingEnd ℂ) (u x) :=
  ContinuousLinearMap.coeFn_compLpL _ _

@[simp] theorem conjC_conjC (u : Lp ℂ 2 mu) : conjC mu (conjC mu u) = u := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_conjC (conjC mu u), coeFn_conjC u] with x h1 h2
  rw [h1, h2, Complex.conj_conj]

theorem conjC_smul (c : ℂ) (u : Lp ℂ 2 mu) :
    conjC mu (c • u) = (starRingEnd ℂ) c • conjC mu u := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_conjC (c • u), Lp.coeFn_smul c u,
    Lp.coeFn_smul ((starRingEnd ℂ) c) (conjC mu u), coeFn_conjC u] with x h1 h2 h3 h4
  rw [h1, h2, h3, Pi.smul_apply, Pi.smul_apply, h4, smul_eq_mul, smul_eq_mul, map_mul]

@[simp] theorem reC_conjC (u : Lp ℂ 2 mu) : reC mu (conjC mu u) = reC mu u := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_reC (conjC mu u), coeFn_conjC u, coeFn_reC u] with x h1 h2 h3
  rw [h1, h2, h3, Complex.conj_re]

@[simp] theorem imC_conjC (u : Lp ℂ 2 mu) : imC mu (conjC mu u) = - imC mu u := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_imC (conjC mu u), coeFn_conjC u, Lp.coeFn_neg (imC mu u),
    coeFn_imC u] with x h1 h2 h3 h4
  rw [h1, h2, h3, Pi.neg_apply, h4, Complex.conj_im]

@[simp] theorem conjC_toC (f : Lp ℝ 2 mu) : conjC mu (toC mu f) = toC mu f := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_conjC (toC mu f), coeFn_toC f] with x h1 h2
  rw [h1, h2, Complex.conj_ofReal]

theorem inner_conjC (u v : Lp ℂ 2 mu) : inner ℂ (conjC mu u) (conjC mu v) = inner ℂ v u := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_conjC u, coeFn_conjC v] with x h1 h2
  rw [h1, h2, RCLike.inner_apply, RCLike.inner_apply, Complex.conj_conj]
  ring

/-- An operator is *real* when it is fixed by conjugation. -/
theorem toC_realOp_of_conjC {T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu}
    (h : ∀ u, conjC mu (T (conjC mu u)) = T u) (f : Lp ℝ 2 mu) :
    T (toC mu f) = toC mu (realOp T f) := by
  have hfix : conjC mu (T (toC mu f)) = T (toC mu f) := by
    have := h (toC mu f); rwa [conjC_toC] at this
  have him : imC mu (T (toC mu f)) = 0 := by
    have hneg := congrArg (imC mu) hfix
    rw [imC_conjC] at hneg
    have h2 : (2 : ℝ) • imC mu (T (toC mu f)) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← hneg]
      abel
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  have := toC_reC_add_smul (T (toC mu f))
  rw [him, map_zero, smul_zero, add_zero] at this
  rw [← this, realOp_apply]


theorem norm_conjC_le (u : Lp ℂ 2 mu) : ‖conjC mu u‖ ≤ ‖u‖ := by
  have h := ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.compLpL 2 mu).le_opNorm u
  have hb : ‖(((Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.compLpL 2 mu) :
      Lp ℂ 2 mu →L[ℝ] Lp ℂ 2 mu)‖ ≤ 1 := by
    simpa [Complex.conjCLE_norm] using
      (ContinuousLinearMap.norm_compLpL_le (p := (2 : ℝ≥0∞)) (μ := mu)
        (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap)
  calc ‖conjC mu u‖ ≤ _ * ‖u‖ := h
    _ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg u)
    _ = ‖u‖ := one_mul _

/-- Conjugating an operator by the real structure, `T ↦ J T J`. -/
def conjOp (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu :=
  ofRealLinearCLM ((conjC mu).comp ((T.restrictScalars ℝ).comp (conjC mu)))
    (by
      intro u
      show conjC mu (T (conjC mu (Complex.I • u))) = Complex.I • conjC mu (T (conjC mu u))
      rw [conjC_smul, Complex.conj_I, map_smul, conjC_smul, map_neg, Complex.conj_I, neg_neg])

theorem conjOp_apply (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) (u : Lp ℂ 2 mu) :
    conjOp T u = conjC mu (T (conjC mu u)) := rfl

@[simp] theorem conjOp_one : conjOp (1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) = 1 := by
  refine ContinuousLinearMap.ext fun u => ?_
  rw [conjOp_apply]
  simp

theorem conjOp_mul (T S : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) :
    conjOp (T * S) = conjOp T * conjOp S := by
  refine ContinuousLinearMap.ext fun u => ?_
  rw [conjOp_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, conjOp_apply,
    conjOp_apply, conjC_conjC]

@[simp] theorem conjOp_zero : conjOp (0 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) = 0 := by
  refine ContinuousLinearMap.ext fun u => ?_
  simp [conjOp_apply]

theorem conjOp_add (T S : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) :
    conjOp (T + S) = conjOp T + conjOp S := by
  refine ContinuousLinearMap.ext fun u => ?_
  rw [conjOp_apply]
  simp [conjOp_apply]

theorem conjOp_smul_real (r : ℝ) (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) :
    conjOp (r • T) = r • conjOp T := by
  refine ContinuousLinearMap.ext fun u => ?_
  rw [conjOp_apply]
  simp [conjOp_apply]

theorem conjOp_sub (T S : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) :
    conjOp (T - S) = conjOp T - conjOp S := by
  refine ContinuousLinearMap.ext fun u => ?_
  rw [conjOp_apply]
  simp [conjOp_apply]

theorem conjOp_star (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) :
    conjOp (star T) = star (conjOp T) := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  have e1 : inner ℂ (conjOp (ContinuousLinearMap.adjoint T) x) y
      = inner ℂ (conjC mu y) ((ContinuousLinearMap.adjoint T) (conjC mu x)) := by
    rw [conjOp_apply]
    conv_lhs => rw [← conjC_conjC y]
    exact inner_conjC _ _
  have e2 : inner ℂ x (conjOp T y) = inner ℂ (T (conjC mu y)) (conjC mu x) := by
    rw [conjOp_apply]
    conv_lhs => rw [← conjC_conjC x]
    exact inner_conjC _ _
  rw [e1, e2, ContinuousLinearMap.adjoint_inner_right]

theorem norm_conjOp_le (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) : ‖conjOp T‖ ≤ ‖T‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) fun u => ?_
  calc ‖conjOp T u‖ = ‖conjC mu (T (conjC mu u))‖ := by rw [conjOp_apply]
    _ ≤ ‖T (conjC mu u)‖ := norm_conjC_le _
    _ ≤ ‖T‖ * ‖conjC mu u‖ := T.le_opNorm _
    _ ≤ ‖T‖ * ‖u‖ := mul_le_mul_of_nonneg_left (norm_conjC_le u) (norm_nonneg T)

theorem continuous_conjOp : Continuous (conjOp (mu := mu)) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun T S => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, ← conjOp_sub, NNReal.coe_one, one_mul]
  exact norm_conjOp_le _

/-- Conjugation by the real structure, as an `ℝ`-linear `⋆`-algebra endomorphism of the
C⋆-algebra `Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ`. -/
def conjOpHom (mu : Measure X) :
    (Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) →⋆ₐ[ℝ] (Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) where
  toFun := conjOp
  map_one' := conjOp_one
  map_mul' := conjOp_mul
  map_zero' := conjOp_zero
  map_add' := conjOp_add
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, conjOp_smul_real, conjOp_one]
  map_star' := conjOp_star

@[simp] theorem conjOpHom_apply (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) :
    conjOpHom mu T = conjOp T := rfl

theorem continuous_conjOpHom : Continuous (conjOpHom mu) := continuous_conjOp

/-- The complexification of a real operator is fixed by conjugation. -/
@[simp] theorem conjOp_cxOp (R : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu) : conjOp (cxOp R) = cxOp R := by
  refine ContinuousLinearMap.ext fun u => ?_
  rw [conjOp_apply, cxOp_apply, cxOp_apply, reC_conjC, imC_conjC]
  simp [conjC_smul, Complex.conj_I]

/-- A conjugation-fixed operator is the complexification of its real part. -/
theorem cxOp_realOp_of_conjOp {T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu} (h : conjOp T = T) :
    cxOp (realOp T) = T := by
  have hreal : ∀ f : Lp ℝ 2 mu, T (toC mu f) = toC mu (realOp T f) := by
    refine toC_realOp_of_conjC fun u => ?_
    rw [← conjOp_apply, h]
  refine ContinuousLinearMap.ext fun u => ?_
  rw [cxOp_apply, ← hreal, ← hreal, ← map_smul, ← map_add, toC_reC_add_smul]

/-- `realOp` is multiplicative when the left factor is conjugation-fixed. -/
theorem realOp_mul_of_conjOp {T S : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu} (h : conjOp T = T) :
    realOp (T * S) = (realOp T).comp (realOp S) := by
  conv_lhs => rw [← cxOp_realOp_of_conjOp h]
  exact realOp_cxOp_mul _ _

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKComplexLp
