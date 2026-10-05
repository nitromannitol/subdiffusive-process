module

public import SubdiffusiveProcess.DirichletForm.FOTCoreMeasureData
public import SubdiffusiveProcess.DirichletForm.FOTCoreMeasureUniqueness
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped NNReal CompactlySupported BoundedContinuousFunction

noncomputable section

namespace SubdiffusiveProcess.DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}
variable (F : _root_.SubdiffusiveProcess.DirichletForm m) (U : Set X)

/-- The vector space of domain elements with a continuous compactly supported representative. -/
def coreDomain : Submodule ℝ (Lp ℝ 2 m) where
  carrier := {u | F.toClosedForm.MemCoreOn U u}
  zero_mem' := ⟨F.domain.zero_mem, hasCoreRep_zero U⟩
  add_mem' := fun hu hv => hu.add hv
  smul_mem' := fun c _ hu => hu.smul c

variable {F U}

private def coreBound (u : coreDomain F U) : ℝ :=
  Classical.choose (ae_abs_le_of_memCoreOn u.property)

private theorem coreBound_ae (u : coreDomain F U) :
    ∀ᵐ x ∂m, |u.1 x| ≤ coreBound u :=
  Classical.choose_spec (ae_abs_le_of_memCoreOn u.property)

public theorem coreProduct_exists (u v : coreDomain F U) :
    ∃ w : Lp ℝ 2 m, w ∈ F.domain ∧ ⇑w =ᵐ[m] fun x => u.1 x * v.1 x :=
  exists_mul_mem F u.property.1 v.property.1
    ((coreBound_ae u).mono fun _x hx => hx.trans (le_max_left (coreBound u) (coreBound v)))
    ((coreBound_ae v).mono fun _x hx => hx.trans (le_max_right (coreBound u) (coreBound v)))

def coreProduct (u v : coreDomain F U) : Lp ℝ 2 m := Classical.choose (coreProduct_exists u v)

theorem coreProduct_mem (u v : coreDomain F U) : coreProduct u v ∈ F.domain :=
  (Classical.choose_spec (coreProduct_exists u v)).1

theorem coreProduct_ae (u v : coreDomain F U) :
    ⇑(coreProduct u v) =ᵐ[m] fun x => u.1 x * v.1 x :=
  (Classical.choose_spec (coreProduct_exists u v)).2

theorem coreProduct_comm (u v : coreDomain F U) : coreProduct u v = coreProduct v u := by
  apply Lp.ext
  filter_upwards [coreProduct_ae u v, coreProduct_ae v u] with x h1 h2
  rw [h1, h2, mul_comm]

theorem coreProduct_add_left (u v w : coreDomain F U) :
    coreProduct (u + v) w = coreProduct u w + coreProduct v w := by
  apply Lp.ext
  filter_upwards [coreProduct_ae (u + v) w, coreProduct_ae u w, coreProduct_ae v w,
    Lp.coeFn_add u.1 v.1, Lp.coeFn_add (coreProduct u w) (coreProduct v w)] with x h1 h2 h3 h4 h5
  rw [h1, h5, Pi.add_apply, h2, h3]
  change (u.1 + v.1) x * w.1 x = _
  rw [h4, Pi.add_apply, add_mul]

theorem coreProduct_add_right (u v w : coreDomain F U) :
    coreProduct u (v + w) = coreProduct u v + coreProduct u w := by
  rw [coreProduct_comm u (v + w), coreProduct_add_left,
    coreProduct_comm v u, coreProduct_comm w u]

theorem coreProduct_smul_left (c : ℝ) (u v : coreDomain F U) :
    coreProduct (c • u) v = c • coreProduct u v := by
  apply Lp.ext
  filter_upwards [coreProduct_ae (c • u) v, coreProduct_ae u v,
    Lp.coeFn_smul c u.1, Lp.coeFn_smul c (coreProduct u v)] with x h1 h2 h3 h4
  rw [h1, h4, Pi.smul_apply, smul_eq_mul, h2]
  change (c • u.1) x * v.1 x = _
  rw [h3, Pi.smul_apply, smul_eq_mul]
  ring

theorem coreProduct_smul_right (c : ℝ) (u v : coreDomain F U) :
    coreProduct u (c • v) = c • coreProduct u v := by
  rw [coreProduct_comm u (c • v), coreProduct_smul_left, coreProduct_comm v u]

/-- The representative chosen for a uniform core test gives a core vector. -/
def coreTest (f : _root_.SubdiffusiveProcess.DirichletForm.FOTConstruction.CoreRiesz.tests F U) : coreDomain F U :=
  ⟨_root_.SubdiffusiveProcess.DirichletForm.FOTConstruction.CoreRiesz.testLp f, _root_.SubdiffusiveProcess.DirichletForm.FOTConstruction.CoreRiesz.testLp_core f⟩

/-- The polarized defining functional on the continuous core. -/
def coreBilinear (φ : _root_.SubdiffusiveProcess.DirichletForm.FOTConstruction.CoreRiesz.tests F U) :
    coreDomain F U →ₗ[ℝ] coreDomain F U →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun u v => F.form u.1 (coreProduct v (coreTest φ)) -
      (1 / 2 : ℝ) * F.form (coreProduct u v) (_root_.SubdiffusiveProcess.DirichletForm.FOTConstruction.CoreRiesz.testLp φ))
    (by
      intro u v w
      rw [Submodule.coe_add, coreProduct_add_left,
        F.form_add_left u.1 u.property.1 v.1 v.property.1 _ (coreProduct_mem w (coreTest φ)),
        F.form_add_left _ (coreProduct_mem u w) _ (coreProduct_mem v w) _ (_root_.SubdiffusiveProcess.DirichletForm.FOTConstruction.CoreRiesz.testLp_mem φ)]
      ring)
    (by
      intro c u v
      rw [Submodule.coe_smul, coreProduct_smul_left,
        F.form_smul_left c u.1 u.property.1 _ (coreProduct_mem v (coreTest φ)),
        F.form_smul_left c _ (coreProduct_mem u v) _ (_root_.SubdiffusiveProcess.DirichletForm.FOTConstruction.CoreRiesz.testLp_mem φ)]
      simp only [smul_eq_mul]
      ring)
    (by
      intro u v w
      rw [coreProduct_add_left, coreProduct_add_right,
        F.toClosedForm.form_add_right u.property.1 (coreProduct_mem v (coreTest φ))
          (coreProduct_mem w (coreTest φ)),
        F.form_add_left _ (coreProduct_mem u v) _ (coreProduct_mem u w) _ (_root_.SubdiffusiveProcess.DirichletForm.FOTConstruction.CoreRiesz.testLp_mem φ)]
      ring)
    (by
      intro c u v
      rw [coreProduct_smul_left, coreProduct_smul_right,
        F.toClosedForm.form_smul_right c u.property.1 (coreProduct_mem v (coreTest φ)),
        F.form_smul_left c _ (coreProduct_mem u v) _ (_root_.SubdiffusiveProcess.DirichletForm.FOTConstruction.CoreRiesz.testLp_mem φ)]
      simp only [smul_eq_mul]
      ring)

theorem CoreMeasure.integral_test (Γ : CoreMeasure F U) (u : coreDomain F U)
    (φ : _root_.SubdiffusiveProcess.DirichletForm.FOTConstruction.CoreRiesz.tests F U) :
    (∫ x, φ.1 x ∂Γ.measure u.1) = coreBilinear φ u u := by
  obtain ⟨f, hf, hfc, hfU, hfae⟩ := u.property.2
  apply Γ.defining u.1 (_root_.SubdiffusiveProcess.DirichletForm.FOTConstruction.CoreRiesz.testLp φ) u.property (_root_.SubdiffusiveProcess.DirichletForm.FOTConstruction.CoreRiesz.testLp_core φ)
    f φ.1 hf φ.1.continuous hfae (_root_.SubdiffusiveProcess.DirichletForm.FOTConstruction.CoreRiesz.testLp_ae φ)
    (coreProduct u (coreTest φ)) (coreProduct u u)
    (coreProduct_mem u (coreTest φ)) (coreProduct_mem u u)
  · filter_upwards [coreProduct_ae u (coreTest φ), hfae, _root_.SubdiffusiveProcess.DirichletForm.FOTConstruction.CoreRiesz.testLp_ae φ] with x h1 h2 h3
    rw [h1, h2]
    change f x * _root_.SubdiffusiveProcess.DirichletForm.FOTConstruction.CoreRiesz.testLp φ x = f x * φ.1 x
    rw [h3]
  · filter_upwards [coreProduct_ae u u, hfae] with x h1 h2
    rw [h1, h2, sq]

end SubdiffusiveProcess.DirichletForm.FOTConstruction
