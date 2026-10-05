module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SimplexEulerRigidity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletInfimum

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open MeasureTheory Homogenization
open _root_.SubdiffusiveProcess.Model
open scoped ContDiff

noncomputable section

variable {d : ℕ}

/-! ## Smooth compactly supported competitors -/

/-- The weak gradient of the `H_0^1` witness of a smooth compactly supported
function is its coordinate gradient. -/
theorem grad_h10Function_ofContDiff {U : Set (Vec d)} (hU : IsOpen U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ U) :
    (H10Function.ofContDiff hU hφ hφc hφs).toH1Function.grad = gradVec φ :=
  rfl

/-- **A smooth compactly supported perturbation is an admissible competitor.**
This is the inclusion `C_c^infinity(U) subset H_0^1(U)` that lets predicate be read off the continuum minimum. -/
theorem dirichletInfOn_le_gradVec {B : Vec d → ℝ} {U : Set (Vec d)} {p : Vec d}
    (hU : IsOpen U) (hB0 : ∀ x, 0 ≤ B x) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ U) :
    dirichletInfOn B U p ≤ dirichletEnergyOn' B U p (gradVec φ) := by
  have h := dirichletInfOn_le (B := B) (U := U) (p := p) hU.measurableSet hB0
    (H10Function.ofContDiff hU hφ hφc hφs)
  rwa [grad_h10Function_ofContDiff] at h

/-! ## The two energy notations agree -/

/-- The affine competitor's energy. -/
theorem dirichletEnergyOn_linearFn {B : Vec d → ℝ} {U : Set (Vec d)} (p : Vec d) :
    dirichletEnergyOn B U (Kuhn.linearFn p) = ∫ x in U, B x * vecNormSq p := by
  simp [dirichletEnergyOn]

/-- The perturbed competitor's energy, in the shape `dirichletInfOn` compares
against. -/
theorem dirichletEnergyOn_linearFn_add {B : Vec d → ℝ} {U : Set (Vec d)}
    {p : Vec d} {φ : Vec d → ℝ} (hφ : Differentiable ℝ φ) :
    dirichletEnergyOn B U (fun x => Kuhn.linearFn p x + φ x) =
      dirichletEnergyOn' B U p (gradVec φ) := by
  unfold dirichletEnergyOn dirichletEnergyOn'
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show B x * vecNormSq (gradVec (fun y => Kuhn.linearFn p y + φ y) x) = _
  rw [gradVec_linearFn_add (hφ x)]

/-! ## The equality case -/

/-- **The equality case of paper label `p.homogenized.coefficient.strict.decay`.**  If the continuum
Dirichlet minimum on `U` equals the energy of the affine function itself, then
`linear_p` is a minimizer in the sense refutes. -/
theorem isAffineMinimalOn_of_dirichletInfOn_eq {B : Vec d → ℝ} {U : Set (Vec d)}
    {p : Vec d} (hU : IsOpen U) (hB0 : ∀ x, 0 ≤ B x)
    (heq : dirichletInfOn B U p = ∫ x in U, B x * vecNormSq p) :
    IsAffineMinimalOn B U p := by
  intro φ hφ hφc hφs
  rw [dirichletEnergyOn_linearFn, dirichletEnergyOn_linearFn_add
    (hφ.differentiable (by simp)), ← heq]
  exact dirichletInfOn_le_gradVec hU hB0 hφ hφc hφs

/-! ## The refutation -/



theorem not_ae_dirichletInfOn_eq_affine_kuhnCell (M : GMCModel d)
    (T : Kuhn.KuhnCell d) {p : Vec d} (hp : p ≠ 0) :
    ¬ (∀ᵐ omega ∂M.P.toMeasure,
        dirichletInfOn (shellFactor M 0 omega) T.openCarrier p =
          ∫ x in T.openCarrier, shellFactor M 0 omega x * vecNormSq p) := by
  intro hae
  refine not_ae_isAffineMinimalOn_kuhnCell M T hp ?_
  filter_upwards [hae] with omega homega
  exact isAffineMinimalOn_of_dirichletInfOn_eq (Kuhn.isOpen_openCarrier T)
    (fun x => (shellFactor_pos M 0 omega x).le) homega

/-- The same statement on the source's own cell `spx_0^pi`
(paper label `p.homogenized.coefficient.strict.decay`). -/
theorem not_ae_dirichletInfOn_eq_affine_originSimplex (M : GMCModel d)
    (pi : Equiv.Perm (Fin d)) {p : Vec d} (hp : p ≠ 0) :
    ¬ (∀ᵐ omega ∂M.P.toMeasure,
        dirichletInfOn (shellFactor M 0 omega)
            (Kuhn.KuhnCell.mk (Homogenization.originCube d 0) pi).openCarrier p =
          ∫ x in (Kuhn.KuhnCell.mk (Homogenization.originCube d 0) pi).openCarrier,
            shellFactor M 0 omega x * vecNormSq p) :=
  not_ae_dirichletInfOn_eq_affine_kuhnCell M _ hp

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
