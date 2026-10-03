/-
# Cores, regularity and strong locality
-/
module

public import SubdiffusiveProcess.DirichletForm.Energy
public import Mathlib.Topology.Algebra.Support

@[expose] public section

/-!
# Cores, regularity and strong locality

A **core** of a closed form `E` on `L²(X, m)` is a set of elements of
`D(E) ∩ C_c(X)` which is dense in `D(E)` for the energy norm and dense in
`C_c(X)` for the uniform norm; `E` is **regular** if it has one.  `E` is
**strongly local** if `E(u, v) = 0` whenever `u, v ∈ D(E)` vanish outside
compact sets and `u` is constant on an open set outside which `v` vanishes.

## Main definitions

* `DirichletForm.HasCoreRep m U u`: `u` has a continuous representative whose
  (compact) support lies in `U`.
* `DirichletForm.ClosedForm.MemCoreOn E U`, `DirichletForm.ClosedForm.MemCore E`:
  the cores `D(E) ∩ C_c(U)` and `D(E) ∩ C_c(X)`.
* `DirichletForm.IsCore`, `DirichletForm.IsRegular`.
* `DirichletForm.IsStronglyLocalOnCore`, `DirichletForm.IsStronglyLocal`.

## References

* Fukushima–Oshima–Takeda, *Dirichlet Forms and Symmetric Markov Processes*,
  §1.1 (regularity) and §3.2 (strong locality).
-/

open MeasureTheory Filter Topology

noncomputable section

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}

namespace DirichletForm

/-- `u ∈ L²(X, m)` has a continuous representative with compact support contained
in `U`. -/
def HasCoreRep (m : Measure X) (U : Set X) (u : Lp ℝ 2 m) : Prop :=
  ∃ f : X → ℝ, Continuous f ∧ HasCompactSupport f ∧ tsupport f ⊆ U ∧ ⇑u =ᵐ[m] f

/-- `u ∈ L²(X, m)` vanishes almost everywhere outside a compact set. -/
def HasCompactSupportAE (m : Measure X) (u : Lp ℝ 2 m) : Prop :=
  ∃ K : Set X, IsCompact K ∧ ∀ᵐ x ∂m, x ∉ K → u x = 0

theorem HasCoreRep.mono {U V : Set X} {u : Lp ℝ 2 m} (hUV : U ⊆ V)
    (hu : HasCoreRep m U u) : HasCoreRep m V u := by
  obtain ⟨f, hf, hcs, hsupp, hae⟩ := hu
  exact ⟨f, hf, hcs, hsupp.trans hUV, hae⟩

theorem HasCoreRep.hasCompactSupportAE {U : Set X} {u : Lp ℝ 2 m}
    (hu : HasCoreRep m U u) : HasCompactSupportAE m u := by
  obtain ⟨f, _, hcs, _, hae⟩ := hu
  refine ⟨tsupport f, hcs, ?_⟩
  filter_upwards [hae] with x hx hxK
  rw [hx]
  exact image_eq_zero_of_notMem_tsupport hxK

theorem hasCoreRep_zero (U : Set X) : HasCoreRep m U (0 : Lp ℝ 2 m) := by
  refine ⟨0, continuous_const, ?_, ?_, Lp.coeFn_zero ℝ 2 m⟩
  · simp [HasCompactSupport, tsupport]
  · simp [tsupport]

theorem HasCoreRep.add {U : Set X} {u v : Lp ℝ 2 m} (hu : HasCoreRep m U u)
    (hv : HasCoreRep m U v) : HasCoreRep m U (u + v) := by
  obtain ⟨f, hf, hcf, hsf, haf⟩ := hu
  obtain ⟨g, hg, hcg, hsg, hag⟩ := hv
  refine ⟨f + g, hf.add hg, hcf.add hcg, ?_, ?_⟩
  · have h1 : tsupport (f + g) ⊆ tsupport f ∪ tsupport g := by
      refine (closure_mono (Function.support_add f g)).trans ?_
      exact closure_union.le
    exact h1.trans (Set.union_subset hsf hsg)
  · exact (Lp.coeFn_add u v).trans (haf.add hag)

theorem HasCoreRep.smul {U : Set X} (c : ℝ) {u : Lp ℝ 2 m} (hu : HasCoreRep m U u) :
    HasCoreRep m U (c • u) := by
  obtain ⟨f, hf, hcf, hsf, haf⟩ := hu
  refine ⟨c • f, hf.const_smul c, hcf.smul_left, ?_, ?_⟩
  · exact (tsupport_smul_subset_right (fun _ => c) f).trans hsf
  · exact (Lp.coeFn_smul c u).trans (haf.const_smul c)

namespace ClosedForm

/-- The core `D(E) ∩ C_c(U)`: elements of the domain with a continuous
representative compactly supported inside `U`. -/
def MemCoreOn (E : ClosedForm m) (U : Set X) (u : Lp ℝ 2 m) : Prop :=
  u ∈ E.domain ∧ HasCoreRep m U u

/-- The core `D(E) ∩ C_c(X)`. -/
def MemCore (E : ClosedForm m) (u : Lp ℝ 2 m) : Prop := E.MemCoreOn Set.univ u

variable {E : ClosedForm m}

theorem MemCoreOn.mem_domain {U : Set X} {u : Lp ℝ 2 m} (hu : E.MemCoreOn U u) :
    u ∈ E.domain := hu.1

theorem MemCoreOn.hasCoreRep {U : Set X} {u : Lp ℝ 2 m} (hu : E.MemCoreOn U u) :
    HasCoreRep m U u := hu.2

theorem MemCoreOn.mono {U V : Set X} {u : Lp ℝ 2 m} (hUV : U ⊆ V)
    (hu : E.MemCoreOn U u) : E.MemCoreOn V u := ⟨hu.1, hu.2.mono hUV⟩

theorem MemCoreOn.memCore {U : Set X} {u : Lp ℝ 2 m} (hu : E.MemCoreOn U u) :
    E.MemCore u := hu.mono (Set.subset_univ U)

theorem MemCore.mem_domain {u : Lp ℝ 2 m} (hu : E.MemCore u) : u ∈ E.domain := hu.1

theorem MemCoreOn.hasCompactSupportAE {U : Set X} {u : Lp ℝ 2 m}
    (hu : E.MemCoreOn U u) : HasCompactSupportAE m u := hu.2.hasCompactSupportAE

theorem memCoreOn_zero (E : ClosedForm m) (U : Set X) : E.MemCoreOn U 0 :=
  ⟨E.domain.zero_mem, hasCoreRep_zero U⟩

theorem MemCoreOn.add {U : Set X} {u v : Lp ℝ 2 m} (hu : E.MemCoreOn U u)
    (hv : E.MemCoreOn U v) : E.MemCoreOn U (u + v) :=
  ⟨E.domain.add_mem hu.1 hv.1, hu.2.add hv.2⟩

theorem MemCoreOn.smul {U : Set X} (c : ℝ) {u : Lp ℝ 2 m} (hu : E.MemCoreOn U u) :
    E.MemCoreOn U (c • u) := ⟨E.domain.smul_mem c hu.1, hu.2.smul c⟩

end ClosedForm

/-- `C` is a **core** of `E` relative to the open state space `U`: a set of
elements of `D(E) ∩ C_c(U)` which is dense in `D(E)` for the energy norm and
dense in `C_c(U)` for the uniform norm.

The state space `U` is not cosmetic.  Fukushima–Oshima–Takeda's regularity is
density in `C_c(X)` where `X` is the space the form lives on; for a form on
`L²(U, m|_U)` inside a bigger ambient `X` — which is how every concrete instance
arises — core functions vanish outside `U`, so no core function is uniformly
close to an `f ∈ C_c(X)` whose support meets `X \ U`.  Quantifying `denseUniform`
over all of `C_c(X)` therefore makes the structure **unsatisfiable**, and with it
`IsRegular`, and with it the antecedent of `HasEnergyMeasure`.

Inhabited by: `DirichletForm.zeroIsCoreOn`. The witness establishes NON-VACUITY
only; inhabitation at the paper's form is the external input
`DirichletForm.HasEnergyMeasure`. -/
structure IsCoreOn (E : ClosedForm m) (U : Set X) (C : Set (Lp ℝ 2 m)) : Prop where
  /-- Every element of `C` lies in `D(E) ∩ C_c(U)`. -/
  memCoreOn : ∀ u ∈ C, E.MemCoreOn U u
  /-- `C` is dense in `D(E)` for the energy norm. -/
  denseEnergy : ∀ u ∈ E.domain, ∀ ε : ℝ, 0 < ε → ∃ w ∈ C, E.energyNormSq (u - w) < ε
  /-- `C` is dense in `C_c(U)` for the uniform norm. -/
  denseUniform : ∀ f : X → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U →
    ∀ ε : ℝ, 0 < ε →
    ∃ w ∈ C, ∃ g : X → ℝ, Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ U ∧
      ⇑w =ᵐ[m] g ∧ ∀ x : X, |g x - f x| < ε

/-- `E` is **regular** if it admits a core relative to an open set carrying `m`.

The state space is existentially bound, so the arity of `IsRegular` is unchanged
and every consumer (`IsCoreAlgebra`, `HasEnergyMeasure`,
`HasBeurlingDenyLocality`) is untouched, while the statement is now satisfiable
for a form living on a proper open subset of the ambient space. -/
def IsRegular (E : ClosedForm m) : Prop :=
  ∃ U : Set X, IsOpen U ∧ m Uᶜ = 0 ∧ ∃ C : Set (Lp ℝ 2 m), IsCoreOn E U C

/-- **Strong locality on the core**: `E(u, v) = 0` whenever `u, v` are core
functions and `u` is constant on an open set containing the support of a
continuous representative of `v`. -/
def IsStronglyLocalOnCore (E : ClosedForm m) : Prop :=
  ∀ u v : Lp ℝ 2 m, E.MemCore u → E.MemCore v →
    ∀ uc vc : X → ℝ, ⇑u =ᵐ[m] uc → ⇑v =ᵐ[m] vc → Continuous uc → Continuous vc →
      HasCompactSupport vc →
      ∀ (c : ℝ) (W : Set X), IsOpen W → tsupport vc ⊆ W → (∀ x ∈ W, uc x = c) →
        E.form u v = 0

/-- **Strong locality**: `E(u, v) = 0` whenever `u, v ∈ D(E)` vanish a.e. outside
compact sets, `v` vanishes a.e. outside an open set `W`, and `u` is a.e. equal to
a constant on `W`. -/
def IsStronglyLocal (E : ClosedForm m) : Prop :=
  ∀ u ∈ E.domain, ∀ v ∈ E.domain, HasCompactSupportAE m u → HasCompactSupportAE m v →
    ∀ (c : ℝ) (W : Set X), IsOpen W →
      (∀ᵐ x ∂m, x ∉ W → v x = 0) → (∀ᵐ x ∂m, x ∈ W → u x = c) →
        E.form u v = 0



structure HasBeurlingDenyLocality (E : ClosedForm m) : Prop where
  /-- A regular form that is strongly local on its core is strongly local. -/
  isStronglyLocal_of_onCore : IsRegular E → IsStronglyLocalOnCore E → IsStronglyLocal E

/-- Strong locality implies strong locality on the core. -/
theorem IsStronglyLocal.onCore {E : ClosedForm m} (h : IsStronglyLocal E) :
    IsStronglyLocalOnCore E := by
  intro u v hu hv uc vc huc hvc _ _ _ c W hW hsupp hconst
  refine h u hu.mem_domain v hv.mem_domain hu.hasCompactSupportAE hv.hasCompactSupportAE
    c W hW ?_ ?_
  · filter_upwards [hvc] with x hx hxW
    rw [hx]
    exact image_eq_zero_of_notMem_tsupport fun hmem => hxW (hsupp hmem)
  · filter_upwards [huc] with x hx hxW
    rw [hx]
    exact hconst x hxW

end DirichletForm
