module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SimplexGapEquality
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.MeanOneFubini
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.CellSupMeasurability
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletMatrixBridge

@[expose] public section

/-!
# Step 1 in expectation: the strict one-cell gap at a fixed slope

Define

```text
q_* = max_pi sup_{|p| = 1} E[ min_{u in linear_p + H_0^1(spx_0^pi)}
                                fint_{spx_0^pi} B_0 |grad u|^2 ]
```

and proves `q_* < 1`.  The proof has two halves: an inequality
(`q_* <= 1`, from the affine competitor and `E[B_0] = 1`) and the refutation of
equality (Step 1's rigidity argument).  This file runs both **at a fixed pair
`(pi, p)`**, which is the whole content of the source's argument; what it does
not do is the compactness/finiteness selection that turns the family of strict
inequalities into a single number `q_* < 1`.

The chain, in order:

* `measurable_dirichletInfOn_shellFactor` -- the measurability argument's measurability obligation, at
  the GMC carrier's own field `B_0`;
* `integrable_dirichletInfOn_shellFactor` -- integrability, by domination
  against `|p|^2 int_{spx} B_0`, whose integrability is the Fubini layer;
* `integral_dirichletInfOn_shellFactor_le` -- **`q_*(pi, p) <= |p|^2`**, the
  source's *"the affine competitor gives `q_* <= 1`"*;
* `integral_dirichletInfOn_shellFactor_lt` -- **`q_*(pi, p) < |p|^2`** for
  `p != 0`.  Equality would force the almost-sure pointwise equality (a
  nonnegative integrable difference of vanishing expectation vanishes almost
  surely), which `SimplexGapEquality.lean` refutes through the nondegeneracy argument;
* `integral_vecDot_randomShellMatrix_lt` -- the same statement in the source's
  own notation `E[p . B_0(spx) p] < |p|^2`, through the identification of the
  finite-volume matrix with the Dirichlet minimum.

## Scope

* The strict inequality is proved **for each fixed `(pi, p)` with `p != 0`**.
  The passage to `q_* < 1` needs, in addition, that
  `p |-> E[dirichletInfOn B_0 spx p]` is continuous on the unit sphere, so that
  its supremum is attained and the strict inequality survives; that continuity
  is **not** proved here.
* No dimension restriction beyond the model's own `2 <= d`, and no `|p| = 1`.
* Nothing about the discrete minima `Q_{R,pi}` or the limit `q_R -> q_*` is
  proved here.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open MeasureTheory Homogenization Homogenization.Book
open _root_.SubdiffusiveProcess.Model

noncomputable section

variable {d : ℕ}

/-! ## The triadic simplex as a public domain -/

/-- **The source's cell `spx_n^pi(z)` as a public bounded domain.**  The
`IsOpenBoundedConvexDomain` witness is the cube geometry's; nonemptiness is the nondegeneracy argument's. -/
def kuhnCellDomain (T : Kuhn.KuhnCell d) : Ch02.Domain d where
  carrier := T.openCarrier
  isDomain := isOpenBoundedConvexDomain_openCarrier T
  nonempty := triadicSimplex_nonempty _ _ _

@[simp] theorem kuhnCellDomain_coe (T : Kuhn.KuhnCell d) :
    ((kuhnCellDomain T : Ch02.Domain d) : Set (Vec d)) = T.openCarrier :=
  rfl

theorem isBounded_openCarrier (T : Kuhn.KuhnCell d) :
    Bornology.IsBounded T.openCarrier :=
  (isBoundedDomain_openCarrier T).isBounded

/-- **The one-cell random matrix `B_0(spx)`**,
in the shape of the `randomAMatrix`. -/
def randomShellMatrix (M : GMCModel d) (k : ℕ) (T : Kuhn.KuhnCell d)
    (omega : PotentialSample d) : Mat d :=
  aMatrix (kuhnCellDomain T)
    (shellFactorCoeffOnData M k omega (kuhnCellDomain T)).toCoeffOn

/-! ## Measurability and integrability of the one-cell minimum -/

/-- the measurability argument's measurability obligation at the GMC carrier's own field. -/
theorem measurable_dirichletInfOn_shellFactor (M : GMCModel d)
    (T : Kuhn.KuhnCell d) (p : Vec d) :
    Measurable fun omega : PotentialSample d =>
      dirichletInfOn (shellFactor M 0 omega) T.openCarrier p := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, d = n + 1 :=
    ⟨d - 1, by have := M.shellPrefix.dimension; omega⟩
  exact measurable_dirichletInfOn_of_measurable_apply
    (isOpenBoundedConvexDomain_openCarrier T) T.openCarrier_subset_openCubeSet
    (fun omega => continuous_shellFactor M 0 omega)
    (fun omega x => (shellFactor_pos M 0 omega x).le)
    (fun y => (measurable_shell_eval 0 y).sub measurable_const |>.exp) p

/-- The one-cell minimum is dominated by the affine competitor's energy. -/
theorem dirichletInfOn_shellFactor_le (M : GMCModel d) (T : Kuhn.KuhnCell d)
    (p : Vec d) (omega : PotentialSample d) :
    dirichletInfOn (shellFactor M 0 omega) T.openCarrier p ≤
      vecNormSq p * ∫ x in T.openCarrier, shellFactor M 0 omega x := by
  have h := dirichletInfOn_le_affine
    (B := shellFactor M 0 omega) (U := T.openCarrier) (p := p)
    (Kuhn.isOpen_openCarrier T).measurableSet
    (fun x => (shellFactor_pos M 0 omega x).le)
  calc
    dirichletInfOn (shellFactor M 0 omega) T.openCarrier p
        ≤ ∫ x in T.openCarrier, shellFactor M 0 omega x * vecNormSq p := h
    _ = vecNormSq p * ∫ x in T.openCarrier, shellFactor M 0 omega x := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)

/-- The one-cell minimum is integrable in the sample. -/
theorem integrable_dirichletInfOn_shellFactor (M : GMCModel d)
    (T : Kuhn.KuhnCell d) (p : Vec d) :
    Integrable (fun omega : PotentialSample d =>
      dirichletInfOn (shellFactor M 0 omega) T.openCarrier p) M.P.toMeasure := by
  have hdom : Integrable (fun omega : PotentialSample d =>
      vecNormSq p * ∫ x in T.openCarrier, shellFactor M 0 omega x)
      M.P.toMeasure :=
    (integrable_setIntegral_shellFactor M 0
      (Kuhn.isOpen_openCarrier T).measurableSet
      (isBounded_openCarrier T)).const_mul _
  refine Integrable.mono' hdom
    (measurable_dirichletInfOn_shellFactor M T p).aestronglyMeasurable
    (Filter.Eventually.of_forall fun omega => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (dirichletInfOn_nonneg
    (Kuhn.isOpen_openCarrier T).measurableSet
    (fun x => (shellFactor_pos M 0 omega x).le))]
  exact dirichletInfOn_shellFactor_le M T p omega

/-! ## `q_*(pi, p) <= |p|^2` -/

/-- **"The affine competitor gives `q_* <= 1`"**, in
expectation and without the normalization by `|spx|`. -/
theorem integral_dirichletInfOn_shellFactor_le (M : GMCModel d)
    (T : Kuhn.KuhnCell d) (p : Vec d) :
    ∫ omega, dirichletInfOn (shellFactor M 0 omega) T.openCarrier p
        ∂M.P.toMeasure ≤
      (volume T.openCarrier).toReal * vecNormSq p := by
  have hdom : Integrable (fun omega : PotentialSample d =>
      vecNormSq p * ∫ x in T.openCarrier, shellFactor M 0 omega x)
      M.P.toMeasure :=
    (integrable_setIntegral_shellFactor M 0
      (Kuhn.isOpen_openCarrier T).measurableSet
      (isBounded_openCarrier T)).const_mul _
  have hle := integral_mono (integrable_dirichletInfOn_shellFactor M T p) hdom
    (fun omega => dirichletInfOn_shellFactor_le M T p omega)
  rwa [integral_const_mul, integral_setIntegral_shellFactor M 0
    (Kuhn.isOpen_openCarrier T).measurableSet (isBounded_openCarrier T),
    mul_comm] at hle

/-! ## `q_*(pi, p) < |p|^2` -/

/-- **The strict one-cell gap at a fixed slope.**  This is Step 1  with the compactness selection removed: for every
nonzero `p` and every triadic simplex, the expected continuum Dirichlet minimum
is *strictly* below the affine energy. -/
theorem integral_dirichletInfOn_shellFactor_lt (M : GMCModel d)
    (T : Kuhn.KuhnCell d) {p : Vec d} (hp : p ≠ 0) :
    ∫ omega, dirichletInfOn (shellFactor M 0 omega) T.openCarrier p
        ∂M.P.toMeasure <
      (volume T.openCarrier).toReal * vecNormSq p := by
  have hUmeas : MeasurableSet T.openCarrier :=
    (Kuhn.isOpen_openCarrier T).measurableSet
  set F : PotentialSample d → ℝ := fun omega =>
    ∫ x in T.openCarrier, shellFactor M 0 omega x * vecNormSq p with hF
  set G : PotentialSample d → ℝ := fun omega =>
    dirichletInfOn (shellFactor M 0 omega) T.openCarrier p with hG
  have hGF : ∀ omega, G omega ≤ F omega := fun omega =>
    dirichletInfOn_le_affine hUmeas fun x => (shellFactor_pos M 0 omega x).le
  have hFeq : F = fun omega =>
      vecNormSq p * ∫ x in T.openCarrier, shellFactor M 0 omega x := by
    funext omega
    rw [hF, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  have hFint : Integrable F M.P.toMeasure := by
    rw [hFeq]
    exact (integrable_setIntegral_shellFactor M 0 hUmeas
      (isBounded_openCarrier T)).const_mul _
  have hGint : Integrable G M.P.toMeasure :=
    integrable_dirichletInfOn_shellFactor M T p
  have hFI : ∫ omega, F omega ∂M.P.toMeasure =
      (volume T.openCarrier).toReal * vecNormSq p := by
    rw [hFeq, integral_const_mul,
      integral_setIntegral_shellFactor M 0 hUmeas (isBounded_openCarrier T),
      mul_comm]
  by_contra hcon
  push Not at hcon
  have heq : ∫ omega, G omega ∂M.P.toMeasure =
      (volume T.openCarrier).toReal * vecNormSq p :=
    le_antisymm (integral_dirichletInfOn_shellFactor_le M T p) hcon
  have hzero : ∫ omega, (F omega - G omega) ∂M.P.toMeasure = 0 := by
    rw [integral_sub hFint hGint, hFI, heq, sub_self]
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall fun omega => sub_nonneg.mpr (hGF omega))
    (hFint.sub hGint)).mp hzero
  refine not_ae_dirichletInfOn_eq_affine_kuhnCell M T hp ?_
  filter_upwards [hae] with omega homega
  have hval : F omega - G omega = 0 := homega
  have : G omega = F omega := by linarith
  exact this

/-! ## The same statement in the source's matrix notation -/

/-- **`E[p . B_0(spx) p] < |p|^2`**, the source's own display  at a fixed pair `(pi, p)`.  This is the previous
theorem transported through the identification of the finite-volume matrix with
the continuum Dirichlet minimum. -/
theorem integral_vecDot_randomShellMatrix_lt (M : GMCModel d)
    (T : Kuhn.KuhnCell d) {p : Vec d} (hp : p ≠ 0) :
    ∫ omega, vecDot p (matVecMul (randomShellMatrix M 0 T omega) p)
        ∂M.P.toMeasure < vecNormSq p := by
  have hvol : 0 < (volume T.openCarrier).toReal := volume_toReal_pos (kuhnCellDomain T)
  have hpt : ∀ omega : PotentialSample d,
      vecDot p (matVecMul (randomShellMatrix M 0 T omega) p) =
        (volume T.openCarrier).toReal⁻¹ *
          dirichletInfOn (shellFactor M 0 omega) T.openCarrier p := fun omega =>
    vecDot_aMatrix_eq_dirichletInfOn (shellFactorCoeffOnData M 0 omega _)
      (fun x => (shellFactor_pos M 0 omega x).le) p
  simp only [hpt]
  rw [integral_const_mul]
  have hlt := integral_dirichletInfOn_shellFactor_lt M T hp
  calc
    (volume T.openCarrier).toReal⁻¹ *
        ∫ omega, dirichletInfOn (shellFactor M 0 omega) T.openCarrier p
          ∂M.P.toMeasure
        < (volume T.openCarrier).toReal⁻¹ *
            ((volume T.openCarrier).toReal * vecNormSq p) :=
      mul_lt_mul_of_pos_left hlt (inv_pos.mpr hvol)
    _ = vecNormSq p := by field_simp

/-! ## The sparse coefficient, in the same vocabulary -/

/-- **`p . A_N^{(R)}(V) p = min_u fint_V A_N^{(R)} |grad u|^2`**, the object
Step 3's induction  and Step 4's comparison
 are stated for. -/
theorem vecDot_randomSparseMatrix_eq (M : GMCModel d) (R N : ℕ)
    (U : Ch02.Domain d) (omega : PotentialSample d) (p : Vec d) :
    vecDot p (matVecMul (randomSparseMatrix M R N U omega) p) =
      (volume (U : Set (Vec d))).toReal⁻¹ *
        dirichletInfOn (sparseLayerCoefficient M R N omega)
          (U : Set (Vec d)) p :=
  vecDot_aMatrix_eq_dirichletInfOn (sparseLayerCoeffOnData M R N omega U)
    (fun x => (sparseLayerCoefficient_pos M R N omega x).le) p

/-- **The `A_N^{(R)}`-Dirichlet minimizer with boundary values `linear_p`
exists** on every public bounded domain.  This is the per-cell minimizer Step 3
solves for. -/
theorem exists_sparse_dirichletMinimizer (M : GMCModel d) (R N : ℕ)
    (U : Ch02.Domain d) (omega : PotentialSample d) (p : Vec d) :
    ∃ w : H10Function (U : Set (Vec d)),
      dirichletEnergyOn' (sparseLayerCoefficient M R N omega)
          (U : Set (Vec d)) p w.toH1Function.grad =
        dirichletInfOn (sparseLayerCoefficient M R N omega)
          (U : Set (Vec d)) p :=
  exists_h10Function_dirichletEnergyOn'_eq_dirichletInfOn
    (sparseLayerCoeffOnData M R N omega U)
    (fun x => (sparseLayerCoefficient_pos M R N omega x).le) p

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
