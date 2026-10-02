/-
# Energy measures of a strongly local Dirichlet form
-/
import SubdiffusiveProcess.DirichletForm.Killed
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Energy measures

For a regular strongly local Dirichlet form `E` on `L²(X, m)` the *energy
measure* (carré du champ) `Γ(u)` of `u ∈ D(E)` is the finite Borel measure with
`∫ φ dΓ(u) = E(u, uφ) - ½ E(u², φ)`; the polarized cross measure `Γ(u, v)` is a
signed measure.  This file carries the calculus of these measures as a structure
`DirichletForm.EnergyMeasure`, whose fields are exactly the properties used in
applications: total mass, bilinearity, Cauchy–Schwarz, locality on open sets,
the chain rule and the Leibniz rule.

Existence of an energy measure is **not proved here**.  It is an accepted
external input, recorded as the `Prop`-valued structure
`DirichletForm.HasEnergyMeasure`, together with the algebra property of the core
(`DirichletForm.IsCoreAlgebra`).  Neither is an axiom; both are passed as
hypotheses.

## References

* M. Fukushima, Y. Oshima, M. Takeda, *Dirichlet Forms and Symmetric Markov
  Processes*, 2nd edition, §3.2 (Theorem 3.2.2, Lemma 3.2.5) and Theorem 1.4.2.
* A. Beurling, J. Deny, *Dirichlet spaces*, Proc. Nat. Acad. Sci. 45 (1959).
-/

open MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}

namespace DirichletForm

/-- Integral of a real function over a set against a signed measure, through the
Jordan decomposition. -/
def signedIntegralOn (ν : SignedMeasure X) (B : Set X) (f : X → ℝ) : ℝ :=
  (∫ x in B, f x ∂ν.toJordanDecomposition.posPart) -
    (∫ x in B, f x ∂ν.toJordanDecomposition.negPart)

omit [TopologicalSpace X] in
theorem signedIntegralOn_congr (ν : SignedMeasure X) (B : Set X) {f g : X → ℝ}
    (h : ∀ x, f x = g x) : signedIntegralOn ν B f = signedIntegralOn ν B g := by
  simp only [signedIntegralOn]
  congr 1 <;> exact integral_congr_ae (Filter.Eventually.of_forall h)

omit [TopologicalSpace X] in
@[simp] theorem signedIntegralOn_zero (ν : SignedMeasure X) (B : Set X) :
    signedIntegralOn ν B (fun _ => 0) = 0 := by
  simp [signedIntegralOn]

omit [TopologicalSpace X] in
theorem signedIntegralOn_neg (ν : SignedMeasure X) (B : Set X) (f : X → ℝ) :
    signedIntegralOn ν B (fun x => -f x) = -signedIntegralOn ν B f := by
  simp only [signedIntegralOn, integral_neg]
  ring

omit [TopologicalSpace X] in
/-- Two integrands summing to zero pointwise contribute nothing.  This is the
cancellation of the cross terms in the sine/cosine argument, and it needs no
integrability hypothesis. -/
theorem signedIntegralOn_add_eq_zero (ν : SignedMeasure X) (B : Set X) {f g : X → ℝ}
    (h : ∀ x, f x + g x = 0) :
    signedIntegralOn ν B f + signedIntegralOn ν B g = 0 := by
  have hg : ∀ x, g x = -f x := fun x => by linarith [h x]
  rw [signedIntegralOn_congr ν B hg, signedIntegralOn_neg]
  ring



structure EnergyMeasure (E : ClosedForm m) where
  /-- The energy measure `Γ(u)`. -/
  measure : Lp ℝ 2 m → Measure X
  /-- The cross energy measure `Γ(u, v)`. -/
  cross : Lp ℝ 2 m → Lp ℝ 2 m → SignedMeasure X
  /-- `Γ(u)` is a finite measure for `u ∈ D(E)`. -/
  measure_univ_lt_top : ∀ u ∈ E.domain, measure u Set.univ < ⊤
  /-- `Γ(u)(X) = E(u, u)`. -/
  measure_univ : ∀ u ∈ E.domain, (measure u Set.univ).toReal = E.form u u
  /-- `Γ(u, v) = Γ(v, u)` for `u, v ∈ D(E)`. -/
  cross_symm : ∀ u ∈ E.domain, ∀ v ∈ E.domain, cross u v = cross v u
  /-- `Γ(u, u) = Γ(u)`. -/
  cross_self : ∀ u ∈ E.domain, ∀ B : Set X, MeasurableSet B →
    cross u u B = (measure u B).toReal
  /-- `Γ` is additive in its second argument, on `D(E)`. -/
  cross_add_right : ∀ u ∈ E.domain, ∀ v ∈ E.domain, ∀ w ∈ E.domain,
    cross u (v + w) = cross u v + cross u w
  /-- `Γ` is homogeneous in its second argument, on `D(E)`. -/
  cross_smul_right : ∀ (c : ℝ), ∀ u ∈ E.domain, ∀ v ∈ E.domain,
    cross u (c • v) = c • cross u v
  /-- `Γ(u, v)(X) = E(u, v)`. -/
  cross_univ : ∀ u ∈ E.domain, ∀ v ∈ E.domain, cross u v Set.univ = E.form u v
  /-- Cauchy–Schwarz for the cross measure, on `D(E)`. -/
  abs_cross_le : ∀ u ∈ E.domain, ∀ v ∈ E.domain, ∀ B : Set X, MeasurableSet B →
    |cross u v B| ≤
      Real.sqrt (measure u B).toReal * Real.sqrt (measure v B).toReal
  /-- Locality: `Γ(u)` and `Γ(w)` agree **as measures restricted to** an open set
  on which `u = w`, for `u, w ∈ D(E)`.

  The paper's display is the total mass
  `Γ(u)(O) = Γ(w)(O)`, which is recovered as `locality_apply` below.  The
  restricted form is what Fukushima–Oshima–Takeda Theorem 3.2.2 gives (`Γ` is a
  local functional) and it is what the paper's own use at line 2385 needs: there
  `Γ(w_ε)` is identified with `1_{q ∩ {|v|>ε}} Γ(v)` as measures, which the
  total-mass version cannot deliver. -/
  locality : ∀ u ∈ E.domain, ∀ w ∈ E.domain, ∀ O : Set X, IsOpen O →
    (⇑u =ᵐ[m.restrict O] ⇑w) → (measure u).restrict O = (measure w).restrict O
  /-- `Γ(u)` is a Radon measure.  Fukushima–Oshima–Takeda's energy measures are
  Radon; without it the passage from test functions to Borel sets fails (audit
  §3.4, doubled-space counterexample). -/
  regular : ∀ u ∈ E.domain, (measure u).Regular
  /-- `Γ(u)` is carried by the support of `u`. -/
  measure_compl_tsupport : ∀ u : Lp ℝ 2 m, u ∈ E.domain →
    ∀ f : X → ℝ, Continuous f → (⇑u =ᵐ[m] f) → measure u (tsupport f)ᶜ = 0
  /-- Chain rule `Γ(Φ(u)) = Φ'(u)² Γ(u)` for `Φ ∈ C¹` with `Φ 0 = 0`.  The
  integrand is evaluated on a continuous representative `uc` of `u`: energy
  measures need not be absolutely continuous with respect to `m`, so the
  representative is part of the statement. -/
  chain_rule : ∀ u ∈ E.domain, ∀ uc : X → ℝ, Continuous uc → (⇑u =ᵐ[m] uc) →
    ∀ Φ : ℝ → ℝ, ContDiff ℝ 1 Φ → Φ 0 = 0 →
    ∀ w ∈ E.domain, (⇑w =ᵐ[m] fun x => Φ (uc x)) →
    ∀ B : Set X, MeasurableSet B →
      (measure w B).toReal = ∫ x in B, (deriv Φ (uc x)) ^ 2 ∂(measure u)
  /-- Leibniz rule
  `Γ(vΦ(u)) = v²Φ'(u)²Γ(u) + 2vΦ(u)Φ'(u)Γ(u,v) + Φ(u)²Γ(v)` for core `u, v` and
  `Φ ∈ C¹`, evaluated on continuous representatives `uc`, `vc`. -/
  leibniz : ∀ u v : Lp ℝ 2 m, E.MemCore u → E.MemCore v →
    ∀ uc vc : X → ℝ, Continuous uc → Continuous vc → (⇑u =ᵐ[m] uc) → (⇑v =ᵐ[m] vc) →
    ∀ Φ : ℝ → ℝ, ContDiff ℝ 1 Φ →
    ∀ w ∈ E.domain, (⇑w =ᵐ[m] fun x => vc x * Φ (uc x)) →
    ∀ B : Set X, MeasurableSet B →
      (measure w B).toReal =
        (∫ x in B, (vc x) ^ 2 * (deriv Φ (uc x)) ^ 2 ∂(measure u)) +
          2 * signedIntegralOn (cross u v) B
              (fun x => vc x * Φ (uc x) * deriv Φ (uc x)) +
          (∫ x in B, (Φ (uc x)) ^ 2 ∂(measure v))
  /-- The identity that DEFINES the energy measure
  (`mfd:prop-killed-consistency`): `∫ φ dΓ(u) = E(u, uφ) - ½ E(u², φ)` for a
  core function `u` and a core test function `φ`.  It is what makes `Γ(u)`
  unique, and it is what `mfd:lem-borel-weights` consumes at line 2287. -/
  defining_identity : ∀ u φ : Lp ℝ 2 m, E.MemCore u → E.MemCore φ →
    ∀ uc φc : X → ℝ, Continuous uc → Continuous φc →
      (⇑u =ᵐ[m] uc) → (⇑φ =ᵐ[m] φc) →
    ∀ uφ u2 : Lp ℝ 2 m, uφ ∈ E.domain → u2 ∈ E.domain →
      (⇑uφ =ᵐ[m] fun x => uc x * φc x) → (⇑u2 =ᵐ[m] fun x => uc x ^ 2) →
      (∫ x, φc x ∂(measure u)) = E.form u uφ - (1 / 2 : ℝ) * E.form u2 φ

namespace EnergyMeasure

variable {E : ClosedForm m} (Γ : EnergyMeasure E)

/-- The paper's locality display:
`Γ(u)(O) = Γ(w)(O)` on an open set where `u = w`. -/
theorem locality_apply {u w : Lp ℝ 2 m} (hu : u ∈ E.domain) (hw : w ∈ E.domain)
    {O : Set X} (hO : IsOpen O) (h : ⇑u =ᵐ[m.restrict O] ⇑w) :
    Γ.measure u O = Γ.measure w O := by
  have hres := Γ.locality u hu w hw O hO h
  have h1 := congrArg (fun μ : Measure X => μ O) hres
  simpa [Measure.restrict_apply_self] using h1

/-- `Γ` is additive in its first argument, on `D(E)`. -/
theorem cross_add_left {u v w : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (hw : w ∈ E.domain) : Γ.cross (u + v) w = Γ.cross u w + Γ.cross v w := by
  rw [Γ.cross_symm _ (E.domain.add_mem hu hv) w hw, Γ.cross_add_right w hw u hu v hv,
    Γ.cross_symm w hw u hu, Γ.cross_symm w hw v hv]

/-- `Γ` is homogeneous in its first argument, on `D(E)`. -/
theorem cross_smul_left (c : ℝ) {u v : Lp ℝ 2 m} (hu : u ∈ E.domain)
    (hv : v ∈ E.domain) : Γ.cross (c • u) v = c • Γ.cross u v := by
  rw [Γ.cross_symm _ (E.domain.smul_mem c hu) v hv, Γ.cross_smul_right c v hv u hu,
    Γ.cross_symm v hv u hu]

/-- Expansion of `Γ(u + v, u + v)` on a set, for `u, v ∈ D(E)`. -/
theorem cross_add_self_apply {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (B : Set X) :
    Γ.cross (u + v) (u + v) B =
      Γ.cross u u B + 2 * Γ.cross u v B + Γ.cross v v B := by
  have huv := E.domain.add_mem hu hv
  rw [Γ.cross_add_left hu hv huv, VectorMeasure.add_apply,
    Γ.cross_add_right u hu u hu v hv, Γ.cross_add_right v hv u hu v hv,
    VectorMeasure.add_apply, VectorMeasure.add_apply, Γ.cross_symm v hv u hu]
  ring

/-- Expansion of `Γ(u - v, u - v)` on a set, for `u, v ∈ D(E)`. -/
theorem cross_sub_self_apply {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (B : Set X) :
    Γ.cross (u - v) (u - v) B =
      Γ.cross u u B - 2 * Γ.cross u v B + Γ.cross v v B := by
  have hnv : (-1 : ℝ) • v ∈ E.domain := E.domain.smul_mem _ hv
  have h : u - v = u + (-1 : ℝ) • v := by rw [neg_one_smul, ← sub_eq_add_neg]
  rw [h, Γ.cross_add_self_apply hu hnv, Γ.cross_smul_right (-1) u hu v hv,
    Γ.cross_smul_left (-1) hv hnv, Γ.cross_smul_right (-1) v hv v hv,
    VectorMeasure.smul_apply, VectorMeasure.smul_apply, VectorMeasure.smul_apply,
    smul_eq_mul, smul_eq_mul, smul_eq_mul]
  ring

/-- Polarization of the energy measure, for `u, v ∈ D(E)`. -/
theorem cross_eq_polarization {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (B : Set X) :
    Γ.cross u v B =
      (Γ.cross (u + v) (u + v) B - Γ.cross (u - v) (u - v) B) / 4 := by
  rw [Γ.cross_add_self_apply hu hv, Γ.cross_sub_self_apply hu hv]
  ring

/-- `Γ(u)` is finite on every set, for `u ∈ D(E)`. -/
theorem measure_lt_top {u : Lp ℝ 2 m} (hu : u ∈ E.domain) (B : Set X) :
    Γ.measure u B < ⊤ :=
  lt_of_le_of_lt (measure_mono (Set.subset_univ B)) (Γ.measure_univ_lt_top u hu)

theorem measure_ne_top {u : Lp ℝ 2 m} (hu : u ∈ E.domain) (B : Set X) :
    Γ.measure u B ≠ ⊤ := (Γ.measure_lt_top hu B).ne

/-- `Γ(u, u) ≥ 0` on measurable sets. -/
theorem cross_self_nonneg {u : Lp ℝ 2 m} (hu : u ∈ E.domain) {B : Set X}
    (hB : MeasurableSet B) : 0 ≤ Γ.cross u u B := by
  rw [Γ.cross_self u hu B hB]
  exact ENNReal.toReal_nonneg

/-- The energy measure of an element of the domain is monotone in the set. -/
theorem toReal_measure_mono {u : Lp ℝ 2 m} (hu : u ∈ E.domain) {B C : Set X}
    (hBC : B ⊆ C) : (Γ.measure u B).toReal ≤ (Γ.measure u C).toReal :=
  ENNReal.toReal_mono (Γ.measure_ne_top hu C) (measure_mono hBC)

/-- The total mass of `Γ(u)` is the energy of `u`. -/
theorem toReal_measure_le_form {u : Lp ℝ 2 m} (hu : u ∈ E.domain) (B : Set X) :
    (Γ.measure u B).toReal ≤ E.form u u := by
  rw [← Γ.measure_univ u hu]
  exact Γ.toReal_measure_mono hu (Set.subset_univ B)

/-- **Uniqueness of the energy measure on core test functions.**  The defining
identity pins `∫ φ dΓ(u)` to `E(u, uφ) − ½E(u², φ)`, which does not mention `Γ`;
so two energy measures of the same form assign the same integral to every core
test function.  Together with regularity and the Radon property this is what
determines `Γ(u)`, and it is the uniqueness input of `mfd:lem-borel-weights`
(`mfd:lem-borel-weights`). -/
theorem integral_eq_of_defining (Γ Γ' : EnergyMeasure E) {u φ : Lp ℝ 2 m}
    (hu : E.MemCore u) (hφ : E.MemCore φ) {uc φc : X → ℝ} (huc : Continuous uc)
    (hφc : Continuous φc) (huae : ⇑u =ᵐ[m] uc) (hφae : ⇑φ =ᵐ[m] φc)
    {uφ u2 : Lp ℝ 2 m} (huφ : uφ ∈ E.domain) (hu2 : u2 ∈ E.domain)
    (huφrep : ⇑uφ =ᵐ[m] fun x => uc x * φc x)
    (hu2rep : ⇑u2 =ᵐ[m] fun x => uc x ^ 2) :
    (∫ x, φc x ∂(Γ.measure u)) = ∫ x, φc x ∂(Γ'.measure u) := by
  rw [Γ.defining_identity u φ hu hφ uc φc huc hφc huae hφae uφ u2 huφ hu2 huφrep hu2rep,
    Γ'.defining_identity u φ hu hφ uc φc huc hφc huae hφae uφ u2 huφ hu2 huφrep hu2rep]

end EnergyMeasure

/-- **External input** (Fukushima–Oshima–Takeda, Theorem 1.4.2): the core
`D(E) ∩ C_c(X)` of a regular Dirichlet form is an algebra, stable under
composition with `C¹` functions vanishing at the origin, and stable under
multiplication by a bounded `C¹` function of another core element without
enlarging the support.

This is a `Prop`-valued hypothesis structure, never an axiom.

**Instantiate only for a regular Dirichlet form.**  FOT Theorem 1.4.2 is stated
there, and the `isRegular` field records the hypothesis; the Markov property is
supplied by the `DirichletForm` the caller starts from.

Inhabited by: `DirichletForm.zeroIsCoreAlgebra`. The witness establishes
NON-VACUITY only; inhabitation at the paper's form is the external input
`DirichletForm.HasEnergyMeasure`. -/
structure IsCoreAlgebra (E : ClosedForm m) : Prop where
  /-- Fukushima–Oshima–Takeda Theorem 1.4.2 is stated for a *regular* Dirichlet
  form; the hypothesis is carried here so that the input asserts exactly the
  cited fact and nothing more. -/
  isRegular : IsRegular E
  /-- The core is stable under products. -/
  mul_mem : ∀ u v : Lp ℝ 2 m, E.MemCore u → E.MemCore v →
    ∃ w : Lp ℝ 2 m, E.MemCore w ∧ (⇑w =ᵐ[m] fun x => u x * v x)
  /-- The core is stable under composition with `C¹` functions vanishing at `0`. -/
  comp_mem : ∀ u : Lp ℝ 2 m, E.MemCore u → ∀ Φ : ℝ → ℝ, ContDiff ℝ 1 Φ → Φ 0 = 0 →
    ∃ w : Lp ℝ 2 m, E.MemCore w ∧ (⇑w =ᵐ[m] fun x => Φ (u x))
  /-- `v · Φ(u)` is a core function supported where `v` is, for bounded `C¹` `Φ`. -/
  mul_comp_mem : ∀ (U : Set X) (u v : Lp ℝ 2 m), E.MemCore u → E.MemCoreOn U v →
    ∀ uc vc : X → ℝ, Continuous uc → Continuous vc → (⇑u =ᵐ[m] uc) → (⇑v =ᵐ[m] vc) →
    ∀ Φ : ℝ → ℝ, ContDiff ℝ 1 Φ → (∃ M : ℝ, ∀ t : ℝ, |Φ t| ≤ M) →
    ∃ w : Lp ℝ 2 m, E.MemCoreOn U w ∧ (⇑w =ᵐ[m] fun x => vc x * Φ (uc x))
  /-- Fukushima–Oshima–Takeda Theorem 1.4.2(ii): a **bounded** element of the
  domain times a core function supported in `U` is again a core function
  supported in `U`.  Consumed by `mfd:lem-truncation` at
  `mfd:lem-truncation`, where `T_ε(v)` is bounded and in the domain but
  not compactly supported. -/
  mul_mem_of_bounded : ∀ (U : Set X) (u v : Lp ℝ 2 m), u ∈ E.domain →
    ∀ uc : X → ℝ, Continuous uc → (⇑u =ᵐ[m] uc) → (∃ M : ℝ, ∀ x : X, |uc x| ≤ M) →
    E.MemCoreOn U v → ∀ vc : X → ℝ, Continuous vc → (⇑v =ᵐ[m] vc) →
    ∃ w : Lp ℝ 2 m, E.MemCoreOn U w ∧ (⇑w =ᵐ[m] fun x => uc x * vc x)

end DirichletForm



structure DirichletForm.HasEnergyMeasure {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] {m : Measure X} (E : DirichletForm m) : Prop where
  /-- A regular strongly local Dirichlet form carries an energy measure. -/
  exists_energyMeasure : DirichletForm.IsRegular E.toClosedForm →
    DirichletForm.IsStronglyLocal E.toClosedForm →
    Nonempty (DirichletForm.EnergyMeasure E.toClosedForm)
