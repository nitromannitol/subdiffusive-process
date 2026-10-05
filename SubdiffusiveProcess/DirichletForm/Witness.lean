/-
# Inhabitation witnesses for every structure of the library
-/
module

public import SubdiffusiveProcess.DirichletForm.ImageDensity
public import SubdiffusiveProcess.DirichletForm.Weighted
public import SubdiffusiveProcess.DirichletForm.Gradient
public import SubdiffusiveProcess.DirichletForm.Killed
public import SubdiffusiveProcess.DirichletForm.Resolvent

@[expose] public section

/-!
# Inhabitation witnesses

Every structure of this library is inhabited; this file provides the witnesses,
and each structure's docstring names its witness on an `Inhabited by:` line.
The point is not that the witnesses are interesting — they are the **zero form**
`E = 0` with `D(E) = L²(X, m)` — but that no structure is vacuous, so that a
theorem taking one of them as a hypothesis is not vacuously true.

## Honest limits of these witnesses

The zero form is degenerate.  A *nonzero* witness would be the Dirichlet form of
the Laplacian on `ℝ^d`, i.e. `E(u) = ∫ |∇u|²`, whose energy measure is
`|∇u|² dx`.  **Mathlib 4.26 cannot construct it**: it has no Sobolev space and no
weak gradient (the only Sobolev file is
`Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`, the
Gagliardo–Nirenberg–Sobolev inequality), so `H¹(ℝ^d)` and its closedness are not
available.  That is precisely why the existence of an energy measure for the
paper's form is carried as the external input
`SubdiffusiveProcess.DirichletForm.HasEnergyMeasure` rather than constructed: the input IS the
assertion of a nonzero witness.

A zero-form witness would also not, by itself, refute the emptiness argument  §0.1, which concerns nonzero forms.
That argument is defeated structurally instead, by restricting every calculus
field of `EnergyMeasure` to `D(E)`: with `locality`, `abs_cross_le` and
bilinearity available only on the domain, no step of the argument can be taken.

The witnesses over the **zero measure** (`m = 0`), where `L²(X, 0)` is trivial,
are used for the structures that require a core or an approximation property
(`IsCore`, `IsRegular`, `IsCoreAlgebra`, `IsKilledDomain`): over a general `(X, m)`
the zero form has no reason to be regular, since regularity is a statement about
`C_c(X)`, not about the form.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace SubdiffusiveProcess.DirichletForm

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]

/-! ## The zero form on an arbitrary `L²(X, m)` -/

/-- The zero form: domain all of `L²(X, m)`, energy identically `0`. -/
def zeroClosedForm (m : Measure X) : ClosedForm m where
  domain := ⊤
  form := fun _ _ => 0
  denseDomain := by
    rw [Submodule.top_coe]
    exact dense_univ
  form_symm := by intro u _ v _; rfl
  form_add_left := by intro u _ v _ w _; simp
  form_smul_left := by intro c u _ v _; simp
  form_nonneg := by intro u _; exact le_rfl
  complete := by
    intro u _ hc
    have hcauchy : CauchySeq u := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := hc (ε ^ 2) (by positivity)
      refine ⟨N, fun p hp q hq => ?_⟩
      have h := hN p hp q hq
      rw [zero_add] at h
      rw [dist_eq_norm]
      exact lt_of_pow_lt_pow_left₀ 2 hε.le (by simpa using h)
    obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hcauchy
    refine ⟨w, Submodule.mem_top, ?_⟩
    have hn : Tendsto (fun n => ‖u n - w‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hw
    simpa using (hn.pow 2)

omit [TopologicalSpace X] in
@[simp] theorem zeroClosedForm_form {X : Type*} [MeasurableSpace X] [_top : TopologicalSpace X]
    (m : Measure X) (u v : Lp ℝ 2 m) :
    (zeroClosedForm m).form u v = 0 := rfl

omit [TopologicalSpace X] in
@[simp] theorem zeroClosedForm_domain {X : Type*} [MeasurableSpace X] [_top : TopologicalSpace X]
    (m : Measure X) :
    (zeroClosedForm m).domain = ⊤ := rfl

omit [TopologicalSpace X] in
theorem mem_zeroClosedForm_domain {X : Type*} [MeasurableSpace X] [_top : TopologicalSpace X]
    {m : Measure X} (u : Lp ℝ 2 m) :
    u ∈ (zeroClosedForm m).domain := Submodule.mem_top

@[simp] theorem zeroClosedForm_energy (m : Measure X) (u : Lp ℝ 2 m) :
    (zeroClosedForm m).energy u = 0 := by
  rw [_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energy_of_mem _ (mem_zeroClosedForm_domain u)]
  simp

/-- The zero form is a Dirichlet form. -/
def zeroDirichletForm (m : Measure X) : _root_.SubdiffusiveProcess.DirichletForm m where
  toClosedForm := zeroClosedForm m
  markov := fun _ _ _ _ => ⟨Submodule.mem_top, le_rfl⟩

omit [TopologicalSpace X] in
/-- Every normal contraction operates on the zero form. -/
theorem zeroHasNormalContractions {X : Type*} [MeasurableSpace X] [_top : TopologicalSpace X]
    (m : Measure X) :
    HasNormalContractions (zeroDirichletForm m) :=
  ⟨fun _ _ _ _ _ _ => ⟨Submodule.mem_top, le_rfl⟩⟩

/-- The zero form is strongly local. -/
theorem zeroIsStronglyLocal (m : Measure X) : IsStronglyLocal (zeroClosedForm m) := by
  intro u _ v _ _ _ _ _ _ _ _
  rfl

/-- The zero form is strongly local on its core. -/
theorem zeroIsStronglyLocalOnCore (m : Measure X) :
    IsStronglyLocalOnCore (zeroClosedForm m) := by
  intro u v _ _ _ _ _ _ _ _ _ _ _ _ _ _
  rfl

/-- Beurling–Deny holds vacuously for the zero form. -/
theorem zeroHasBeurlingDenyLocality (m : Measure X) :
    HasBeurlingDenyLocality (zeroClosedForm m) :=
  ⟨fun _ _ => zeroIsStronglyLocal m⟩

omit [TopologicalSpace X] in
@[simp] theorem signedIntegralOn_zero_measure {X : Type*} [MeasurableSpace X] [_top : TopologicalSpace X]
    (B : Set X) (f : X → ℝ) :
    signedIntegralOn (0 : SignedMeasure X) B f = 0 := by
  simp [signedIntegralOn, SignedMeasure.toJordanDecomposition_zero]

/-- The zero energy measure of the zero form. -/
def zeroEnergyMeasure (m : Measure X) : EnergyMeasure (zeroClosedForm m) where
  measure := fun _ => 0
  cross := fun _ _ => 0
  measure_univ_lt_top := by intro u _; simp
  measure_univ := by intro u _; simp
  cross_symm := by intro u _ v _; rfl
  cross_self := by intro u _ B _; simp
  cross_add_right := by intro u _ v _ w _; simp
  cross_smul_right := by intro c u _ v _; simp
  cross_univ := by intro u _ v _; simp
  abs_cross_le := by intro u _ v _ B _; simp
  locality := by intro u _ w _ O _ _; simp
  regular := by intro u _; infer_instance
  measure_compl_tsupport := by intro u _ f _ _; rfl
  chain_rule := by intro u _ uc _ _ Φ _ _ w _ _ B _; simp
  leibniz := by intro u v _ _ uc vc _ _ _ _ Φ _ w _ _ B _; simp
  defining_identity := by
    intro u φ _ _ uc φc _ _ _ _ uφ u2 _ _ _ _; simp

@[simp] theorem zeroEnergyMeasure_measure (m : Measure X) (u : Lp ℝ 2 m) :
    (zeroEnergyMeasure m).measure u = 0 := rfl

@[simp] theorem zeroEnergyMeasure_cross (m : Measure X) (u v : Lp ℝ 2 m) :
    (zeroEnergyMeasure m).cross u v = 0 := rfl

/-- The zero form carries the Bouleau–Hirsch property. -/
theorem zeroHasEnergyImageDensity (m : Measure X) :
    HasEnergyImageDensity (E := zeroDirichletForm m) (zeroEnergyMeasure m) where
  measure_preimage_eq_zero := by intro v _ vc _ _ N _ _; rfl
  lipschitz_chain_rule := by
    intro v _ vc _ _ T _ _ Td _ _ Tv _ _ B _; simp

/-- The zero form is the weighted zero form, for any weight. -/
theorem zeroIsWeightedForm (m : Measure X) (w : X → ℝ) :
    IsWeightedForm (zeroClosedForm m) (zeroClosedForm m) (zeroEnergyMeasure m) w where
  domain_eq := rfl
  energy_eq := by intro u _; simp
  form_eq := by intro u _ v _; simp

/-- The constant sequence at the zero form Mosco-converges to it. -/
theorem zeroMoscoConverges (m : Measure X) :
    MoscoConverges (fun _ : ℕ => zeroClosedForm m) (zeroClosedForm m) where
  liminf_le := by
    intro u w _
    simp
  exists_recovery := by
    intro w
    refine ⟨fun _ => w, tendsto_const_nhds, ?_⟩
    simp

omit [TopologicalSpace X] in
/-- The identity is the `1`-resolvent of the zero form. -/
theorem zeroIsResolvent {X : Type*} [MeasurableSpace X] [_top : TopologicalSpace X]
    (m : Measure X) :
    IsResolvent (zeroClosedForm m) 1 (ContinuousLinearMap.id ℝ (Lp ℝ 2 m)) := by
  intro f
  refine ⟨Submodule.mem_top, fun v _ => ?_⟩
  simp

/-! ## The zero gradient energy -/

/-- The zero gradient energy on a one-point carrier. -/
def zeroGradientEnergy (μ : Measure X) : GradientEnergy μ ℝ Unit where
  value := fun _ _ => 0
  grad := fun _ _ => 0
  integrand := fun _ _ => 0
  energy := fun _ => 0
  integrand_nonneg := by intro x ξ; exact le_rfl
  integrand_smul := by intro x c ξ; simp
  energy_eq := by intro u; simp
  integrable := by intro u; simp

omit [TopologicalSpace X] in
/-- The zero gradient energy satisfies the contraction chain rule. -/
theorem zeroHasContractionChainRule {X : Type*} [MeasurableSpace X] [_top : TopologicalSpace X]
    (μ m : Measure X) :
    HasContractionChainRule (zeroGradientEnergy μ) m where
  exists_comp := by
    intro u T hT
    refine ⟨(), fun _ => 1, fun _ => le_of_eq (abs_one), ?_, ?_⟩
    · filter_upwards with x
      simpa [zeroGradientEnergy] using hT.map_zero.symm
    · filter_upwards with x
      simp [zeroGradientEnergy]

/-! ## Witnesses over the zero measure, where `L²` is trivial -/

instance instSubsingletonLpZero : Subsingleton (Lp ℝ 2 (0 : Measure X)) :=
  ⟨fun x y => Lp.ext_iff.2 (by rw [ae_zero]; exact Filter.eventually_bot)⟩

omit [TopologicalSpace X] in
theorem eventuallyEq_of_measure_zero {X : Type*} [MeasurableSpace X] [_top : TopologicalSpace X]
    {f g : X → ℝ} : f =ᵐ[(0 : Measure X)] g := by
  rw [Filter.EventuallyEq, ae_zero]
  exact Filter.eventually_bot

omit [TopologicalSpace X] in
theorem norm_eq_zero_of_measure_zero {X : Type*} [MeasurableSpace X] [_top : TopologicalSpace X]
    (u : Lp ℝ 2 (0 : Measure X)) : ‖u‖ = 0 := by
  rw [Subsingleton.elim u 0, norm_zero]

theorem memCoreOn_zero_measure (U : Set X) (u : Lp ℝ 2 (0 : Measure X)) :
    (zeroClosedForm (0 : Measure X)).MemCoreOn U u := by
  refine ⟨Submodule.mem_top, ⟨0, continuous_const, ?_, ?_, eventuallyEq_of_measure_zero⟩⟩
  · simp [HasCompactSupport, tsupport]
  · simp [tsupport]

/-- Over the zero measure the zero form is regular. -/
theorem zeroIsCoreOn : IsCoreOn (zeroClosedForm (0 : Measure X)) Set.univ Set.univ where
  memCoreOn := fun u _ => memCoreOn_zero_measure Set.univ u
  denseEnergy := by
    intro u _ ε hε
    refine ⟨0, Set.mem_univ _, ?_⟩
    simp [_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energyNormSq, hε]
  denseUniform := by
    intro f hf hcs _ ε hε
    exact ⟨0, Set.mem_univ _, f, hf, hcs, Set.subset_univ _,
      eventuallyEq_of_measure_zero, fun x => by simpa using hε⟩

theorem zeroIsRegular : IsRegular (zeroClosedForm (0 : Measure X)) :=
  ⟨Set.univ, isOpen_univ, by simp, Set.univ, zeroIsCoreOn⟩

/-- Over the zero measure the core of the zero form is an algebra. -/
theorem zeroIsCoreAlgebra : IsCoreAlgebra (zeroClosedForm (0 : Measure X)) where
  isRegular := zeroIsRegular
  mul_mem := fun _ _ _ _ => ⟨0, memCoreOn_zero_measure _ 0, eventuallyEq_of_measure_zero⟩
  comp_mem := fun _ _ _ _ _ => ⟨0, memCoreOn_zero_measure _ 0, eventuallyEq_of_measure_zero⟩
  mul_comp_mem := fun U _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    ⟨0, memCoreOn_zero_measure U 0, eventuallyEq_of_measure_zero⟩
  mul_mem_of_bounded := fun U _ _ _ _ _ _ _ _ _ _ _ =>
    ⟨0, memCoreOn_zero_measure U 0, eventuallyEq_of_measure_zero⟩

/-- Over the zero measure the zero form carries an energy measure. -/
theorem zeroHasEnergyMeasure :
    HasEnergyMeasure (zeroDirichletForm (0 : Measure X)) :=
  ⟨fun _ _ => ⟨zeroEnergyMeasure (0 : Measure X)⟩⟩

/-- Over the zero measure the whole space is the killed domain of every open
set. -/
theorem zeroIsKilledDomain (U : Set X) :
    IsKilledDomain (zeroClosedForm (0 : Measure X)) U ⊤ where
  le_domain := le_rfl
  memCoreOn_mem := fun _ _ => Submodule.mem_top
  approx := by
    intro u _ ε hε
    exact ⟨0, memCoreOn_zero_measure U 0, by
      simp [_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energyNormSq, hε]⟩
  isClosed := fun _ _ _ _ _ => Submodule.mem_top

/-- Over the zero measure the zero form is its own killed part. -/
theorem zeroIsKilledPart (U : Set X) :
    IsKilledPart (zeroClosedForm (0 : Measure X)) U (zeroClosedForm (0 : Measure X)) where
  isKilledDomain := zeroIsKilledDomain U
  form_eq := fun _ _ _ _ => rfl

end SubdiffusiveProcess.DirichletForm
