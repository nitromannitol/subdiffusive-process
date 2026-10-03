/-
# Killed parts of a closed form on an open set
-/
module

public import SubdiffusiveProcess.DirichletForm.Regular
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# Killed parts

The **part** of a closed form `E` on an open set `U` (the form "killed" outside
`U`) is the restriction of `E` to the closure, for the energy norm, of the core
functions supported in `U`.  This file axiomatizes that domain
(`DirichletForm.IsKilledDomain`), shows it is unique, and proves the two facts
the applications need:

* `DirichletForm.IsKilledDomain.le_of_subset`: consistency of killed parts,
  `q ⊆ U` implies `D(E^q) ⊆ D(E^U)`, with the forms agreeing;
* `DirichletForm.IsKilledDomain.eq_domain_of_isRegular`: for a regular form the
  killed domain on the whole space is the full domain.

## References

* Fukushima–Oshima–Takeda, *Dirichlet Forms and Symmetric Markov Processes*,
  §4.4 (parts of Dirichlet forms).
-/

open MeasureTheory Filter Topology

noncomputable section

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}

namespace DirichletForm

/-- `D` is the **killed domain** of `E` on `U`: it contains the core functions
supported in `U`, every element is an energy-norm limit of such functions, and
it is closed for the energy norm.

Inhabited by: `DirichletForm.zeroIsKilledDomain`. The witness establishes
NON-VACUITY only; inhabitation at the paper's form is the external input
`DirichletForm.HasEnergyMeasure`. -/
structure IsKilledDomain (E : ClosedForm m) (U : Set X) (D : Submodule ℝ (Lp ℝ 2 m)) :
    Prop where
  /-- The killed domain is contained in `D(E)`. -/
  le_domain : D ≤ E.domain
  /-- The killed domain contains every core function supported in `U`. -/
  memCoreOn_mem : ∀ u : Lp ℝ 2 m, E.MemCoreOn U u → u ∈ D
  /-- Every element of the killed domain is an energy-norm limit of core
  functions supported in `U`. -/
  approx : ∀ u ∈ D, ∀ ε : ℝ, 0 < ε →
    ∃ w : Lp ℝ 2 m, E.MemCoreOn U w ∧ E.energyNormSq (u - w) < ε
  /-- The killed domain is closed for the energy norm. -/
  isClosed : ∀ (u : ℕ → Lp ℝ 2 m) (w : Lp ℝ 2 m), (∀ n, u n ∈ D) → w ∈ E.domain →
    Tendsto (fun n => E.energyNormSq (u n - w)) atTop (𝓝 0) → w ∈ D

/-- `F` is the **killed part** of `E` on the open set `U`: its domain is the
killed domain and its form is the restriction of `E`.

Inhabited by: `DirichletForm.zeroIsKilledPart`. The witness establishes
NON-VACUITY only; inhabitation at the paper's form is the external input
`DirichletForm.HasEnergyMeasure`. -/
structure IsKilledPart (E : ClosedForm m) (U : Set X) (F : ClosedForm m) : Prop where
  /-- The domain of `F` is the killed domain of `E` on `U`. -/
  isKilledDomain : IsKilledDomain E U F.domain
  /-- `F` agrees with `E` on its domain. -/
  form_eq : ∀ u ∈ F.domain, ∀ v ∈ F.domain, F.form u v = E.form u v

namespace IsKilledDomain

variable {E : ClosedForm m}

/-- An element of the killed domain is an energy-norm limit of core functions
supported in `U`. -/
theorem exists_seq {U : Set X} {D : Submodule ℝ (Lp ℝ 2 m)} (h : IsKilledDomain E U D)
    {u : Lp ℝ 2 m} (hu : u ∈ D) :
    ∃ w : ℕ → Lp ℝ 2 m, (∀ n, E.MemCoreOn U (w n)) ∧
      Tendsto (fun n => E.energyNormSq (u - w n)) atTop (𝓝 0) := by
  choose w hw hlt using fun n : ℕ => h.approx u hu (1 / (n + 1)) (by positivity)
  refine ⟨w, hw, squeeze_zero (fun n => E.energyNormSq_nonneg ?_) (fun n => (hlt n).le) ?_⟩
  · exact E.domain.sub_mem (h.le_domain hu) (hw n).mem_domain
  · exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- **Consistency of killed parts.**  If `q ⊆ U` then the killed domain on `q`
is contained in the killed domain on `U`. -/
theorem le_of_subset {q U : Set X} {D₁ D₂ : Submodule ℝ (Lp ℝ 2 m)} (hqU : q ⊆ U)
    (h₁ : IsKilledDomain E q D₁) (h₂ : IsKilledDomain E U D₂) : D₁ ≤ D₂ := by
  intro u hu
  obtain ⟨w, hw, hconv⟩ := h₁.exists_seq hu
  have hud : u ∈ E.domain := h₁.le_domain hu
  refine h₂.isClosed w u (fun n => h₂.memCoreOn_mem _ ((hw n).mono hqU)) hud ?_
  refine hconv.congr fun n => ?_
  exact E.energyNormSq_sub_comm hud (hw n).mem_domain

/-- The killed domain is unique. -/
theorem eq_of_isKilledDomain {U : Set X} {D₁ D₂ : Submodule ℝ (Lp ℝ 2 m)}
    (h₁ : IsKilledDomain E U D₁) (h₂ : IsKilledDomain E U D₂) : D₁ = D₂ :=
  le_antisymm (le_of_subset (le_refl U) h₁ h₂) (le_of_subset (le_refl U) h₂ h₁)

/-- For a regular form the killed domain on the whole space is the full
domain. -/
theorem eq_domain_of_isRegular {D : Submodule ℝ (Lp ℝ 2 m)}
    (h : IsKilledDomain E Set.univ D) (hreg : IsRegular E) : D = E.domain := by
  refine le_antisymm h.le_domain fun u hu => ?_
  obtain ⟨U, -, -, C, hC⟩ := hreg
  choose w hwC hlt using fun n : ℕ => hC.denseEnergy u hu (1 / (n + 1)) (by positivity)
  have hcore : ∀ n : ℕ, E.MemCoreOn Set.univ (w n) := fun n =>
    (hC.memCoreOn _ (hwC n)).mono (Set.subset_univ U)
  have hmem : ∀ n, w n ∈ D := fun n => h.memCoreOn_mem _ (hcore n)
  refine h.isClosed w u hmem hu ?_
  have hnn : ∀ n, 0 ≤ E.energyNormSq (w n - u) := fun n =>
    E.energyNormSq_nonneg (E.domain.sub_mem (hcore n).mem_domain hu)
  refine squeeze_zero hnn (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
  rw [← E.energyNormSq_sub_comm hu (hcore n).mem_domain]
  exact (hlt n).le

end IsKilledDomain

/-- **Consistency of killed parts**, for the forms: if `q ⊆ U` then the killed
part on `q` has a smaller domain than the killed part on `U`, and the two forms
agree on it. -/
theorem IsKilledPart.le_of_subset {E Fq FU : ClosedForm m} {q U : Set X} (hqU : q ⊆ U)
    (hq : IsKilledPart E q Fq) (hU : IsKilledPart E U FU) :
    Fq.domain ≤ FU.domain ∧
      ∀ u ∈ Fq.domain, ∀ v ∈ Fq.domain, Fq.form u v = FU.form u v := by
  have hle := IsKilledDomain.le_of_subset hqU hq.isKilledDomain hU.isKilledDomain
  refine ⟨hle, fun u hu v hv => ?_⟩
  rw [hq.form_eq u hu v hv, hU.form_eq u (hle hu) v (hle hv)]

end DirichletForm
