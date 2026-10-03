module

public import SubdiffusiveProcess.Paper.lem_sincos

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

section Generic

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {μ : Measure X}

/-- Minkowski inequality for an energy measure: `√Γ(u)(A) ≤ √Γ(v)(A) + √Γ(u - v)(A)`, from the
expansion of `Γ(v + (u - v))` and Cauchy–Schwarz for the cross measure. -/
theorem aux_energy_order_of_form_order_sqrt_le {E : DirichletForm.ClosedForm μ}
    (Γ : DirichletForm.EnergyMeasure E) {u v : Lp ℝ 2 μ} (hu : u ∈ E.domain)
    (hv : v ∈ E.domain) {A : Set X} (hA : MeasurableSet A) :
    Real.sqrt (Γ.measure u A).toReal ≤
      Real.sqrt (Γ.measure v A).toReal + Real.sqrt (Γ.measure (u - v) A).toReal := by
  have huv : u - v ∈ E.domain := E.domain.sub_mem hu hv
  have ha0 : 0 ≤ (Γ.measure v A).toReal := ENNReal.toReal_nonneg
  have hb0 : 0 ≤ (Γ.measure (u - v) A).toReal := ENNReal.toReal_nonneg
  have hexp := Γ.cross_add_self_apply hv huv A
  have hsum : v + (u - v) = u := by abel
  rw [hsum, Γ.cross_self u hu A hA, Γ.cross_self v hv A hA, Γ.cross_self _ huv A hA] at hexp
  have hcs := (abs_le.mp (Γ.abs_cross_le v hv (u - v) huv A hA)).2
  have hle : (Γ.measure u A).toReal ≤
      (Real.sqrt (Γ.measure v A).toReal + Real.sqrt (Γ.measure (u - v) A).toReal) ^ 2 := by
    rw [hexp, add_sq, Real.sq_sqrt ha0, Real.sq_sqrt hb0]
    linarith
  calc Real.sqrt (Γ.measure u A).toReal
      ≤ Real.sqrt ((Real.sqrt (Γ.measure v A).toReal +
          Real.sqrt (Γ.measure (u - v) A).toReal) ^ 2) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt (Γ.measure v A).toReal + Real.sqrt (Γ.measure (u - v) A).toReal :=
        Real.sqrt_sq (by positivity)

/-- A core function supported in `U` carries no energy outside `U`: `Γ(w)` vanishes off the
support of a continuous representative (`measure_compl_tsupport`). -/
theorem aux_energy_order_of_form_order_inter {E : DirichletForm.ClosedForm μ}
    (Γ : DirichletForm.EnergyMeasure E) {U : Set X} {w : Lp ℝ 2 μ} (hw : E.MemCoreOn U w)
    (A : Set X) : Γ.measure w (A ∩ U) = Γ.measure w A := by
  obtain ⟨hwE, f, hf, -, hfU, hae⟩ := hw
  exact measure_inter_conull
    (measure_mono_null (compl_subset_compl.mpr hfU) (Γ.measure_compl_tsupport w hwE f hf hae))

end Generic

/-- Passage to the limit: if `α x' ≤ β y'` for approximants with `√x ≤ √x' + ε` and
`√y' ≤ √y + ε` for every `ε > 0`, then `α x ≤ β y`. -/
theorem aux_energy_order_of_form_order_le_of_approx {α β x y : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : ∀ ε : ℝ, 0 < ε → ∃ x' y' : ℝ, 0 ≤ x' ∧ 0 ≤ y' ∧
      Real.sqrt x ≤ Real.sqrt x' + ε ∧ Real.sqrt y' ≤ Real.sqrt y + ε ∧ α * x' ≤ β * y') :
    α * x ≤ β * y := by
  have key : Real.sqrt α * Real.sqrt x ≤ Real.sqrt β * Real.sqrt y := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have ha := Real.sqrt_nonneg α
    have hb := Real.sqrt_nonneg β
    have hs1 : 0 < Real.sqrt α + Real.sqrt β + 1 := by positivity
    have hε : 0 < δ / (Real.sqrt α + Real.sqrt β + 1) := div_pos hδ hs1
    obtain ⟨x', y', -, -, h1, h2, h3⟩ := h _ hε
    have h3' : Real.sqrt α * Real.sqrt x' ≤ Real.sqrt β * Real.sqrt y' := by
      rw [← Real.sqrt_mul hα, ← Real.sqrt_mul hβ]
      exact Real.sqrt_le_sqrt h3
    have hsε : (Real.sqrt α + Real.sqrt β) * (δ / (Real.sqrt α + Real.sqrt β + 1)) ≤ δ := by
      calc (Real.sqrt α + Real.sqrt β) * (δ / (Real.sqrt α + Real.sqrt β + 1))
          ≤ (Real.sqrt α + Real.sqrt β + 1) * (δ / (Real.sqrt α + Real.sqrt β + 1)) :=
            mul_le_mul_of_nonneg_right (by linarith) hε.le
        _ = δ := mul_div_cancel₀ δ hs1.ne'
    have e1 := mul_le_mul_of_nonneg_left h1 ha
    have e2 := mul_le_mul_of_nonneg_left h2 hb
    rw [mul_add] at e1 e2
    rw [add_mul] at hsε
    linarith
  have hsq := pow_le_pow_left₀ (by positivity) key 2
  rwa [mul_pow, mul_pow, Real.sq_sqrt hα, Real.sq_sqrt hx, Real.sq_sqrt hβ,
    Real.sq_sqrt hy] at hsq

variable {d : ℕ}

/-- Upper measure order on core functions supported in `Q`, on every set: `lem_sincos` at
`q = Q`, `C = M`, on `A ∩ Q`, and no energy outside `Q`. -/
theorem aux_energy_order_of_form_order_core_upper (Q : Opens (SpatialCoordinates d))
    (E F : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hEreg : ∃ Cc : Set (DomainL2 Q),
      DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) Cc)
    (hEloc : DirichletForm.IsStronglyLocal E.toClosedForm)
    (hFreg : ∃ Cc : Set (DomainL2 Q),
      DirichletForm.IsCoreOn F.toClosedForm (Q : Set (SpatialCoordinates d)) Cc)
    (hFloc : DirichletForm.IsStronglyLocal F.toClosedForm)
    (hdom : E.domain = F.domain)
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (M : ℝ) (hform : ∀ u ∈ E.domain, F.form u u ≤ M * E.form u u)
    {w : DomainL2 Q} (hw : E.toClosedForm.MemCoreOn (Q : Set (SpatialCoordinates d)) w)
    (A : Set (SpatialCoordinates d)) :
    (GammaF.measure w A).toReal ≤ M * (GammaE.measure w A).toReal := by
  have hwF : F.toClosedForm.MemCoreOn (Q : Set (SpatialCoordinates d)) w :=
    ⟨hdom ▸ hw.1, hw.2⟩
  have h := lem_sincos E F hEreg hEloc hFreg hFloc hdom GammaE GammaF M
    (Q : Set (SpatialCoordinates d)) Q.isOpen subset_rfl
    (fun v hv => hform v hv.mem_domain) w hw.memCore (A ∩ (Q : Set (SpatialCoordinates d)))
    inter_subset_right
  rwa [aux_energy_order_of_form_order_inter GammaF hwF,
    aux_energy_order_of_form_order_inter GammaE hw] at h

/-- Lower measure order on core functions supported in `Q`, on every set: `lem_sincos` with
`E, F` exchanged at `C = m⁻¹`. -/
theorem aux_energy_order_of_form_order_core_lower (Q : Opens (SpatialCoordinates d))
    (E F : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hEreg : ∃ Cc : Set (DomainL2 Q),
      DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) Cc)
    (hEloc : DirichletForm.IsStronglyLocal E.toClosedForm)
    (hFreg : ∃ Cc : Set (DomainL2 Q),
      DirichletForm.IsCoreOn F.toClosedForm (Q : Set (SpatialCoordinates d)) Cc)
    (hFloc : DirichletForm.IsStronglyLocal F.toClosedForm)
    (hdom : E.domain = F.domain)
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (m : ℝ) (hm : 0 < m) (hform : ∀ u ∈ E.domain, m * E.form u u ≤ F.form u u)
    {w : DomainL2 Q} (hw : E.toClosedForm.MemCoreOn (Q : Set (SpatialCoordinates d)) w)
    (A : Set (SpatialCoordinates d)) :
    m * (GammaE.measure w A).toReal ≤ (GammaF.measure w A).toReal := by
  have hwF : F.toClosedForm.MemCoreOn (Q : Set (SpatialCoordinates d)) w :=
    ⟨hdom ▸ hw.1, hw.2⟩
  have h := lem_sincos F E hFreg hFloc hEreg hEloc hdom.symm GammaF GammaE m⁻¹
    (Q : Set (SpatialCoordinates d)) Q.isOpen subset_rfl
    (fun v hv => (le_inv_mul_iff₀ hm).mpr (hform v (hdom ▸ hv.mem_domain))) w hwF.memCore
    (A ∩ (Q : Set (SpatialCoordinates d))) inter_subset_right
  rw [aux_energy_order_of_form_order_inter GammaF hwF,
    aux_energy_order_of_form_order_inter GammaE hw] at h
  exact (le_inv_mul_iff₀ hm).mp h

/-- Energy-measure bound for an element of small energy norm: with `F ≤ M E` and `M ≥ 0`,
`E₁(v) < ε² / (M + 1)` gives `√Γ_E(v)(A) ≤ ε` and `√Γ_F(v)(A) ≤ ε`. -/
theorem aux_energy_order_of_form_order_small {Q : Opens (SpatialCoordinates d)}
    (E F : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hdom : E.domain = F.domain)
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (M : ℝ) (hM : 0 ≤ M) (hform : ∀ u ∈ E.domain, F.form u u ≤ M * E.form u u)
    {ε : ℝ} (hε : 0 < ε) {v : DomainL2 Q} (hv : v ∈ E.domain)
    (hsmall : E.toClosedForm.energyNormSq v < ε ^ 2 / (M + 1))
    (A : Set (SpatialCoordinates d)) :
    Real.sqrt (GammaE.measure v A).toReal ≤ ε ∧ Real.sqrt (GammaF.measure v A).toReal ≤ ε := by
  have hvF : v ∈ F.domain := hdom ▸ hv
  have hM1 : 0 < M + 1 := by linarith
  have hEv : E.form v v < ε ^ 2 / (M + 1) :=
    lt_of_le_of_lt E.toClosedForm.form_le_energyNormSq hsmall
  have hE0 := E.form_nonneg v hv
  have hδ : ε ^ 2 / (M + 1) ≤ ε ^ 2 := div_le_self (sq_nonneg ε) (by linarith)
  have hδM : (M + 1) * (ε ^ 2 / (M + 1)) = ε ^ 2 := mul_div_cancel₀ _ hM1.ne'
  have hGE : (GammaE.measure v A).toReal ≤ ε ^ 2 :=
    ((GammaE.toReal_measure_le_form hv A).trans hEv.le).trans hδ
  have hGF : (GammaF.measure v A).toReal ≤ ε ^ 2 := by
    have h1 := GammaF.toReal_measure_le_form hvF A
    have h2 := hform v hv
    have h3 : M * E.form v v ≤ (M + 1) * (ε ^ 2 / (M + 1)) :=
      mul_le_mul (by linarith) hEv.le hE0 hM1.le
    linarith
  exact ⟨(Real.sqrt_le_sqrt hGE).trans_eq (Real.sqrt_sq hε.le),
    (Real.sqrt_le_sqrt hGF).trans_eq (Real.sqrt_sq hε.le)⟩

/-- Form order implies energy-measure order (paper, measure order after `eq:mfd-21`,
`mfd:lem-sincos`), for two regular strongly local Dirichlet forms on `L²(Q)` with the same
domain, on every Borel set and for every element of the domain.

On core functions supported in `Q` this is `lem_sincos` at `q = Q` (both directions, the lower
one with `E, F` exchanged), and such functions carry no energy outside `Q`.  A general `u` is
approximated in the energy norm by core functions (regularity of `E`); the Minkowski inequality
for energy measures and `F ≤ M E` pass both inequalities to the limit. -/
theorem energy_order_of_form_order
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E F : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hEreg : ∃ Cc : Set (DomainL2 Q),
      DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) Cc)
    (hEloc : DirichletForm.IsStronglyLocal E.toClosedForm)
    (hFreg : ∃ Cc : Set (DomainL2 Q),
      DirichletForm.IsCoreOn F.toClosedForm (Q : Set (SpatialCoordinates d)) Cc)
    (hFloc : DirichletForm.IsStronglyLocal F.toClosedForm)
    (hdom : E.domain = F.domain)
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (m M : ℝ) (hm : 0 < m)
    (hform : ∀ u ∈ E.domain,
      m * E.form u u ≤ F.form u u ∧ F.form u u ≤ M * E.form u u) :
    ∀ u ∈ E.domain, ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
      m * (GammaE.measure u A).toReal ≤ (GammaF.measure u A).toReal ∧
        (GammaF.measure u A).toReal ≤ M * (GammaE.measure u A).toReal := by
  intro u hu A hA
  have huF : u ∈ F.domain := hdom ▸ hu
  rcases lt_or_ge M 0 with hM | hM
  · -- `M < 0 < m`: the form order forces `E(u) = F(u) = 0`, so both measures vanish
    obtain ⟨h1, h2⟩ := hform u hu
    have hE0 := E.form_nonneg u hu
    have hEu : E.form u u = 0 := le_antisymm (by nlinarith) hE0
    have hFu : F.form u u ≤ 0 := by rw [hEu, mul_zero] at h2; exact h2
    have hGE : (GammaE.measure u A).toReal = 0 :=
      le_antisymm ((GammaE.toReal_measure_le_form hu A).trans hEu.le) ENNReal.toReal_nonneg
    have hGF : (GammaF.measure u A).toReal = 0 :=
      le_antisymm ((GammaF.toReal_measure_le_form huF A).trans hFu) ENNReal.toReal_nonneg
    rw [hGE, hGF, mul_zero, mul_zero]
    exact ⟨le_rfl, le_rfl⟩
  have hformU : ∀ v ∈ E.domain, F.form v v ≤ M * E.form v v := fun v hv => (hform v hv).2
  have hformL : ∀ v ∈ E.domain, m * E.form v v ≤ F.form v v := fun v hv => (hform v hv).1
  obtain ⟨Cc, hCc⟩ := id hEreg
  -- core approximants of `u` whose energy measures on `A` are `ε`-close in square root
  have happrox : ∀ ε : ℝ, 0 < ε → ∃ w : DomainL2 Q,
      E.toClosedForm.MemCoreOn (Q : Set (SpatialCoordinates d)) w ∧
      Real.sqrt (GammaE.measure u A).toReal ≤ Real.sqrt (GammaE.measure w A).toReal + ε ∧
      Real.sqrt (GammaE.measure w A).toReal ≤ Real.sqrt (GammaE.measure u A).toReal + ε ∧
      Real.sqrt (GammaF.measure u A).toReal ≤ Real.sqrt (GammaF.measure w A).toReal + ε ∧
      Real.sqrt (GammaF.measure w A).toReal ≤ Real.sqrt (GammaF.measure u A).toReal + ε := by
    intro ε hε
    have hδ : 0 < ε ^ 2 / (M + 1) := by positivity
    obtain ⟨w, hwC, hsmall⟩ := hCc.denseEnergy u hu _ hδ
    have hw := hCc.memCoreOn w hwC
    have hwE : w ∈ E.domain := hw.mem_domain
    have hwF : w ∈ F.domain := hdom ▸ hwE
    have huw : u - w ∈ E.domain := E.domain.sub_mem hu hwE
    have hwu : w - u ∈ E.domain := E.domain.sub_mem hwE hu
    have hsmall' : E.toClosedForm.energyNormSq (w - u) < ε ^ 2 / (M + 1) := by
      rw [← E.toClosedForm.energyNormSq_sub_comm hu hwE]; exact hsmall
    obtain ⟨s1, s2⟩ := aux_energy_order_of_form_order_small E F hdom GammaE GammaF M hM hformU
      hε huw hsmall A
    obtain ⟨s3, s4⟩ := aux_energy_order_of_form_order_small E F hdom GammaE GammaF M hM hformU
      hε hwu hsmall' A
    have m1 := aux_energy_order_of_form_order_sqrt_le GammaE hu hwE hA
    have m2 := aux_energy_order_of_form_order_sqrt_le GammaE hwE hu hA
    have m3 := aux_energy_order_of_form_order_sqrt_le GammaF huF hwF hA
    have m4 := aux_energy_order_of_form_order_sqrt_le GammaF hwF huF hA
    exact ⟨w, hw, by linarith, by linarith, by linarith, by linarith⟩
  constructor
  · have h := aux_energy_order_of_form_order_le_of_approx hm.le zero_le_one
      (ENNReal.toReal_nonneg : 0 ≤ (GammaE.measure u A).toReal)
      (ENNReal.toReal_nonneg : 0 ≤ (GammaF.measure u A).toReal) (fun ε hε => by
        obtain ⟨w, hw, a1, -, -, a4⟩ := happrox ε hε
        refine ⟨_, _, ENNReal.toReal_nonneg, ENNReal.toReal_nonneg, a1, a4, ?_⟩
        rw [one_mul]
        exact aux_energy_order_of_form_order_core_lower Q E F hEreg hEloc hFreg hFloc hdom
          GammaE GammaF m hm hformL hw A)
    rwa [one_mul] at h
  · have h := aux_energy_order_of_form_order_le_of_approx zero_le_one hM
      (ENNReal.toReal_nonneg : 0 ≤ (GammaF.measure u A).toReal)
      (ENNReal.toReal_nonneg : 0 ≤ (GammaE.measure u A).toReal) (fun ε hε => by
        obtain ⟨w, hw, -, a2, a3, -⟩ := happrox ε hε
        refine ⟨_, _, ENNReal.toReal_nonneg, ENNReal.toReal_nonneg, a3, a2, ?_⟩
        rw [one_mul]
        exact aux_energy_order_of_form_order_core_upper Q E F hEreg hEloc hFreg hFloc hdom
          GammaE GammaF M hformU hw A)
    rwa [one_mul] at h

end Paper
