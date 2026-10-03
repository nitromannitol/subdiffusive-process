module

public import SubdiffusiveProcess.DirichletForm.FOTProduct
public import SubdiffusiveProcess.DirichletForm.EnergyMeasure
public import SubdiffusiveProcess.DirichletForm.MeasureOrder
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

@[expose] public section

/-! Reusable scaling facts for energy measures. -/

open MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal CompactlySupported

noncomputable section

namespace DirichletForm

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}

/-- A diagonal scaling identity for closed forms polarizes to a bilinear scaling identity. -/
theorem ClosedForm.form_eq_smul_of_diagonal_eq (E F : ClosedForm m) (c : ℝ)
    (hdom : F.domain = E.domain)
    (hdiag : ∀ u ∈ E.domain, F.form u u = c * E.form u u)
    {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain) :
    F.form u v = c * E.form u v := by
  have hsum := hdiag (u + v) (E.domain.add_mem hu hv)
  rw [F.form_add_self (hdom.symm ▸ hu) (hdom.symm ▸ hv),
    E.form_add_self hu hv, hdiag u hu, hdiag v hv] at hsum
  nlinarith only [hsum]

/-- The diagonal energy of a sum is bounded by twice the sum of the diagonal energies. -/
theorem ClosedForm.form_add_self_le_two (E : ClosedForm m) {u v : Lp ℝ 2 m}
    (hu : u ∈ E.domain) (hv : v ∈ E.domain) :
    E.form (u + v) (u + v) ≤ 2 * (E.form u u + E.form v v) := by
  have hU : 0 ≤ E.form u u := E.form_nonneg u hu
  have hV : 0 ≤ E.form v v := E.form_nonneg v hv
  have hC := E.abs_form_le hu hv
  have hS : 2 * Real.sqrt (E.form u u) * Real.sqrt (E.form v v) ≤
      E.form u u + E.form v v := by
    have h := sq_nonneg (Real.sqrt (E.form u u) - Real.sqrt (E.form v v))
    have hUeq := Real.sq_sqrt hU
    have hVeq := Real.sq_sqrt hV
    nlinarith [h, hUeq, hVeq]
  have hC' : E.form u v ≤ Real.sqrt (E.form u u) * Real.sqrt (E.form v v) :=
    (abs_le.mp hC).2
  rw [E.form_add_self hu hv]
  nlinarith [hC', hS]

namespace EnergyMeasure

variable {E F : DirichletForm m} (ΓE : EnergyMeasure E.toClosedForm)
  (ΓF : EnergyMeasure F.toClosedForm)

/-- A local energy measure is continuous in the form norm, uniformly over the
measurable set at which it is evaluated. -/
theorem abs_toReal_measure_sub_le_form {u v : Lp ℝ 2 m}
    (hu : u ∈ E.toClosedForm.domain) (hv : v ∈ E.toClosedForm.domain)
    {B : Set X} (hB : MeasurableSet B) :
    |(ΓE.measure u B).toReal - (ΓE.measure v B).toReal| ≤
      Real.sqrt (E.toClosedForm.form (u + v) (u + v)) *
        Real.sqrt (E.toClosedForm.form (u - v) (u - v)) := by
  have hsum : u + v ∈ E.toClosedForm.domain := E.toClosedForm.domain.add_mem hu hv
  have hdiff : u - v ∈ E.toClosedForm.domain := E.toClosedForm.domain.sub_mem hu hv
  have hneg : (-1 : ℝ) • v ∈ E.toClosedForm.domain := E.toClosedForm.domain.smul_mem _ hv
  have hsub : u - v = u + (-1 : ℝ) • v := by
    rw [neg_one_smul, ← sub_eq_add_neg]
  have hcu : ΓE.cross u (u - v) B = ΓE.cross u u B - ΓE.cross u v B := by
    rw [hsub, ΓE.cross_add_right u hu u hu ((-1 : ℝ) • v) hneg,
      ΓE.cross_smul_right (-1) u hu v hv, VectorMeasure.add_apply,
      VectorMeasure.smul_apply, smul_eq_mul]
    ring
  have hcv : ΓE.cross v (u - v) B = ΓE.cross v u B - ΓE.cross v v B := by
    rw [hsub, ΓE.cross_add_right v hv u hu ((-1 : ℝ) • v) hneg,
      ΓE.cross_smul_right (-1) v hv v hv, VectorMeasure.add_apply,
      VectorMeasure.smul_apply, smul_eq_mul]
    ring
  have hcross : ΓE.cross (u + v) (u - v) B =
      ΓE.cross u u B - ΓE.cross v v B := by
    have h := congrArg (fun ν : SignedMeasure X => ν B)
      (ΓE.cross_add_left (w := u - v) hu hv hdiff)
    change ΓE.cross (u + v) (u - v) B =
      ΓE.cross u (u - v) B + ΓE.cross v (u - v) B at h
    rw [hcu, hcv, ΓE.cross_symm v hv u hu] at h
    linarith
  have hcs := ΓE.abs_cross_le (u + v) hsum (u - v) hdiff B hB
  have hmu := ΓE.toReal_measure_le_form hsum B
  have hmv := ΓE.toReal_measure_le_form hdiff B
  calc
    |(ΓE.measure u B).toReal - (ΓE.measure v B).toReal| =
        |ΓE.cross (u + v) (u - v) B| := by
          rw [hcross, ΓE.cross_self u hu B hB, ΓE.cross_self v hv B hB]
    _ ≤ Real.sqrt (ΓE.measure (u + v) B).toReal *
        Real.sqrt (ΓE.measure (u - v) B).toReal := hcs
    _ ≤ Real.sqrt (E.toClosedForm.form (u + v) (u + v)) *
        Real.sqrt (E.toClosedForm.form (u - v) (u - v)) := by
      exact mul_le_mul (Real.sqrt_le_sqrt hmu) (Real.sqrt_le_sqrt hmv)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- The defining identities force proportional integrals on core tests. The product
and square witnesses are supplied by the Dirichlet-form core algebra theorem. -/
theorem integral_eq_smul_of_core {c : ℝ} (hc : 0 < c)
    (hdom : F.toClosedForm.domain = E.toClosedForm.domain)
    (hform : ∀ u ∈ E.toClosedForm.domain,
      F.toClosedForm.form u u = c * E.toClosedForm.form u u)
    {u φ : Lp ℝ 2 m} (hu : E.toClosedForm.MemCore u)
    (hφ : E.toClosedForm.MemCore φ)
    {uc φc : X → ℝ} (huc : Continuous uc) (hφc : Continuous φc)
    (huae : (u : X → ℝ) =ᵐ[m] uc) (hφae : (φ : X → ℝ) =ᵐ[m] φc) :
    (∫ x, φc x ∂ΓF.measure u) =
      ∫ x, φc x ∂(ENNReal.ofReal c • ΓE.measure u) := by
  have huD : u ∈ E.toClosedForm.domain := hu.1
  have hφD : φ ∈ E.toClosedForm.domain := hφ.1
  obtain ⟨uφ, huφcore, huφrep⟩ := DirichletForm.mul_mem E u φ hu hφ
  obtain ⟨u2, hu2core, hu2raw⟩ := DirichletForm.mul_mem E u u hu hu
  have huφD : uφ ∈ E.toClosedForm.domain := huφcore.1
  have hu2D : u2 ∈ E.toClosedForm.domain := hu2core.1
  have huφrep' : (uφ : X → ℝ) =ᵐ[m] fun x => uc x * φc x := by
    filter_upwards [huφrep, huae, hφae] with x h1 h2 h3
    rw [h1, h2, h3]
  have hu2rep : (u2 : X → ℝ) =ᵐ[m] fun x => uc x ^ 2 := by
    filter_upwards [hu2raw, huae] with x h1 h2
    rw [h1, h2]
    ring
  have huF : F.toClosedForm.MemCore u := ⟨hdom.symm ▸ huD, hu.2⟩
  have hφF : F.toClosedForm.MemCore φ := ⟨hdom.symm ▸ hφD, hφ.2⟩
  have hFuphi : uφ ∈ F.toClosedForm.domain := hdom.symm ▸ huφD
  have hFu2 : u2 ∈ F.toClosedForm.domain := hdom.symm ▸ hu2D
  have hF1 := ClosedForm.form_eq_smul_of_diagonal_eq E.toClosedForm F.toClosedForm c
    hdom hform huD huφD
  have hF2 := ClosedForm.form_eq_smul_of_diagonal_eq E.toClosedForm F.toClosedForm c
    hdom hform hu2D hφD
  have hIDE := ΓE.defining_identity u φ hu hφ uc φc huc hφc huae hφae
    uφ u2 huφD hu2D huφrep' hu2rep
  have hIDF := ΓF.defining_identity u φ huF hφF uc φc huc hφc huae hφae
    uφ u2 hFuphi hFu2 huφrep' hu2rep
  calc
    (∫ x, φc x ∂ΓF.measure u) =
        F.toClosedForm.form u uφ - (1 / 2 : ℝ) * F.toClosedForm.form u2 φ := hIDF
    _ = c * (E.toClosedForm.form u uφ -
        (1 / 2 : ℝ) * E.toClosedForm.form u2 φ) := by rw [hF1, hF2]; ring
    _ = c * (∫ x, φc x ∂ΓE.measure u) := by rw [← hIDE]
    _ = ∫ x, φc x ∂(ENNReal.ofReal c • ΓE.measure u) := by
      rw [integral_smul_measure]
      simp [ENNReal.toReal_ofReal hc.le]

/-- On a common open core, the defining identity and Radon uniqueness identify the
energy measures of two proportionally scaled forms for every core element. -/
theorem measure_eq_smul_of_core [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [OpensMeasurableSpace X] (Q : Opens X) {C : Set (Lp ℝ 2 m)}
    (hCore : IsCoreOn E.toClosedForm (Q : Set X) C)
    {c : ℝ} (hc : 0 < c) (hdom : F.toClosedForm.domain = E.toClosedForm.domain)
    (hform : ∀ u ∈ E.toClosedForm.domain,
      F.toClosedForm.form u u = c * E.toClosedForm.form u u)
    {u : Lp ℝ 2 m} (huC : u ∈ C) :
    ΓF.measure u = ENNReal.ofReal c • ΓE.measure u := by
  obtain ⟨huD, ⟨uc, huc, hucs, hucQ, huae⟩⟩ := hCore.memCoreOn u huC
  have huFD : u ∈ F.toClosedForm.domain := hdom.symm ▸ huD
  let μ := ΓF.measure u
  let ν := ENNReal.ofReal c • ΓE.measure u
  have hμtop : μ Set.univ < ⊤ := ΓF.measure_univ_lt_top u huFD
  have hνtop : ν Set.univ < ⊤ := by
    dsimp [ν]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ΓE.measure_univ_lt_top u huD)
  letI : IsFiniteMeasure μ := ⟨hμtop⟩
  letI : IsFiniteMeasure ν := ⟨hνtop⟩
  haveI : μ.Regular := ΓF.regular u huFD
  haveI : ΓE.measure u |>.Regular := ΓE.regular u huD
  haveI : ν.Regular := by
    dsimp [ν]
    exact Measure.Regular.smul (x := ENNReal.ofReal c) ENNReal.ofReal_ne_top
  have hμQ : μ (Q : Set X)ᶜ = 0 := by
    apply measure_mono_null (Set.compl_subset_compl.mpr hucQ)
    exact ΓF.measure_compl_tsupport u huFD uc huc huae
  have hνQ : ν (Q : Set X)ᶜ = 0 := by
    have hEzero : ΓE.measure u (Q : Set X)ᶜ = 0 :=
      measure_mono_null (Set.compl_subset_compl.mpr hucQ)
        (ΓE.measure_compl_tsupport u huD uc huc huae)
    dsimp [ν]
    rw [hEzero, mul_zero]
  have hμQae : ∀ᵐ x ∂μ, x ∈ (Q : Set X) := by
    rw [ae_iff]
    simpa using! hμQ
  have hνQae : ∀ᵐ x ∂ν, x ∈ (Q : Set X) := by
    rw [ae_iff]
    simpa using! hνQ
  have htest : ∀ f : C_c(X, ℝ), tsupport (f : X → ℝ) ⊆ (Q : Set X) →
      (∫ x, f x ∂μ) = ∫ x, f x ∂ν := by
    intro f hfQ
    have hfb : ∃ M : ℝ, ∀ x : X, |f x| ≤ M :=
      f.hasCompactSupport.exists_bound_of_continuous f.continuous
    obtain ⟨Mφ, hφb⟩ := hfb
    have hforward : (∫ x, f x ∂μ) ≤ ∫ x, f x ∂ν := by
      change (∫ x, f.toContinuousMap x ∂μ) ≤ ∫ x, f.toContinuousMap x ∂ν
      have hbound : (∫ x, f.toContinuousMap x ∂μ) ≤
          1 * ∫ x, f.toContinuousMap x ∂ν := by
        refine EnergyMeasure.integral_le_of_unifApprox (ν := μ) (μ := ν)
          (C := 1) (by norm_num) f.continuous hφb ?_
        intro ε hε
        obtain ⟨w, hwC, g, hg, hgcs, hgQ, hwg, hclose⟩ :=
          hCore.denseUniform f f.continuous f.hasCompactSupport hfQ ε hε
        obtain ⟨M, hM⟩ := hgcs.exists_bound_of_continuous hg
        have hwcore := (hCore.memCoreOn w hwC).memCore
        have hucore := (hCore.memCoreOn u huC).memCore
        have hscale := ΓE.integral_eq_smul_of_core ΓF hc hdom hform hucore hwcore
          huc hg huae hwg
        refine ⟨g, hg, ⟨M, hM⟩, ?_, ?_⟩
        · intro x
          exact (hclose x).le
        · simpa only [one_mul] using hscale.le
      simpa only [one_mul] using hbound
    have hback : (∫ x, f x ∂ν) ≤ ∫ x, f x ∂μ := by
      change (∫ x, f.toContinuousMap x ∂ν) ≤ ∫ x, f.toContinuousMap x ∂μ
      have hbound : (∫ x, f.toContinuousMap x ∂ν) ≤
          1 * ∫ x, f.toContinuousMap x ∂μ := by
        refine EnergyMeasure.integral_le_of_unifApprox (ν := ν) (μ := μ)
          (C := 1) (by norm_num) f.continuous hφb ?_
        intro ε hε
        obtain ⟨w, hwC, g, hg, hgcs, hgQ, hwg, hclose⟩ :=
          hCore.denseUniform f f.continuous f.hasCompactSupport hfQ ε hε
        obtain ⟨M, hM⟩ := hgcs.exists_bound_of_continuous hg
        have hwcore := (hCore.memCoreOn w hwC).memCore
        have hucore := (hCore.memCoreOn u huC).memCore
        have hscale := ΓE.integral_eq_smul_of_core ΓF hc hdom hform hucore hwcore
          huc hg huae hwg
        refine ⟨g, hg, ⟨M, hM⟩, ?_, ?_⟩
        · intro x
          exact (hclose x).le
        · simpa only [one_mul] using hscale.symm.le
      simpa only [one_mul] using hbound
    exact le_antisymm hforward hback
  have hμleν : μ ≤ ν := by
    intro B
    have hμB : μ B = μ (B ∩ (Q : Set X)) := by
      calc
        μ B = μ ((Q : Set X) ∩ B) :=
          (Measure.measure_inter_eq_of_ae (μ := μ) (s := B) hμQae).symm
        _ = μ (B ∩ (Q : Set X)) := congrArg μ (inter_comm (Q : Set X) B)
    have hνB : ν (B ∩ (Q : Set X)) = ν B := by
      calc
        ν (B ∩ (Q : Set X)) = ν ((Q : Set X) ∩ B) :=
          congrArg ν (inter_comm B (Q : Set X))
        _ = ν B := Measure.measure_inter_eq_of_ae (μ := ν) (s := B) hνQae
    rw [hμB, ← hνB]
    simpa only [one_mul, ENNReal.coe_one] using (measure_le_of_integral_le (ν := μ) (μ := ν)
      (C := 1) Q.isOpen
      (fun f hf hcs hs hf0 hf1 => by
        have h := htest ⟨⟨f, hf⟩, hcs⟩ (by simpa using hs)
        change (∫ x, f x ∂μ) = ∫ x, f x ∂ν at h
        simpa using h.le)
      (B := B ∩ (Q : Set X)) inter_subset_right)
  have hνleμ : ν ≤ μ := by
    intro B
    have hνB : ν B = ν (B ∩ (Q : Set X)) := by
      calc
        ν B = ν ((Q : Set X) ∩ B) :=
          (Measure.measure_inter_eq_of_ae (μ := ν) (s := B) hνQae).symm
        _ = ν (B ∩ (Q : Set X)) := congrArg ν (inter_comm (Q : Set X) B)
    have hμB : μ (B ∩ (Q : Set X)) = μ B := by
      calc
        μ (B ∩ (Q : Set X)) = μ ((Q : Set X) ∩ B) :=
          congrArg μ (inter_comm B (Q : Set X))
        _ = μ B := Measure.measure_inter_eq_of_ae (μ := μ) (s := B) hμQae
    rw [hνB, ← hμB]
    simpa only [one_mul, ENNReal.coe_one] using (measure_le_of_integral_le (ν := ν) (μ := μ)
      (C := 1) Q.isOpen
      (fun f hf hcs hs hf0 hf1 => by
        have h := htest ⟨⟨f, hf⟩, hcs⟩ (by simpa using hs)
        change (∫ x, f x ∂μ) = ∫ x, f x ∂ν at h
        simpa using h.symm.le)
      (B := B ∩ (Q : Set X)) inter_subset_right)
  exact le_antisymm hμleν hνleμ

/-- Form-norm density extends energy-measure scaling from a regular core to the
whole common form domain. No equality of the energy measures is assumed: it is
deduced on the core from their defining identities and Radon uniqueness. -/
theorem measure_eq_smul_of_form_scale [BorelSpace X] [T2Space X]
    [LocallyCompactSpace X] [OpensMeasurableSpace X] (Q : Opens X)
    {C : Set (Lp ℝ 2 m)} (hCore : IsCoreOn E.toClosedForm (Q : Set X) C)
    {c : ℝ} (hc : 0 < c) (hdom : F.toClosedForm.domain = E.toClosedForm.domain)
    (hform : ∀ u ∈ E.toClosedForm.domain,
      F.toClosedForm.form u u = c * E.toClosedForm.form u u)
    {u : Lp ℝ 2 m} (hu : u ∈ E.toClosedForm.domain) :
    ΓF.measure u = ENNReal.ofReal c • ΓE.measure u := by
  apply Measure.ext
  intro B hB
  have hFu : u ∈ F.toClosedForm.domain := hdom.symm ▸ hu
  have hEuNonneg : 0 ≤ E.toClosedForm.form u u := E.toClosedForm.form_nonneg u hu
  let K := 6 * E.toClosedForm.form u u + 4
  have hK : 0 < K := by dsimp [K]; linarith
  let a := (ΓF.measure u B).toReal
  let b := (ΓE.measure u B).toReal
  let D := |a - c * b|
  by_contra hneq
  have hDpos : 0 < D := by
    dsimp [D]
    have hreal : a ≠ c * b := by
      intro heq
      have htoReal : (ΓF.measure u B).toReal =
          (ENNReal.ofReal c * ΓE.measure u B).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le]
        simpa [a, b] using heq
      apply hneq
      apply (ENNReal.toReal_eq_toReal_iff'
        (ΓF.measure_ne_top hFu B) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ΓE.measure_ne_top hu B))).mp htoReal
    exact abs_pos.mpr (sub_ne_zero.mpr hreal)
  let δ := min 1 (D ^ 2 / (16 * c ^ 2 * K))
  have hδpos : 0 < δ := by
    dsimp [δ]
    apply lt_min
    · norm_num
    · positivity
  have hδle : δ ≤ D ^ 2 / (16 * c ^ 2 * K) := min_le_right _ _
  obtain ⟨w, hwC, hwapprox⟩ := hCore.denseEnergy u hu δ hδpos
  have hwD : w ∈ E.toClosedForm.domain := (hCore.memCoreOn w hwC).mem_domain
  have heps : E.toClosedForm.energyNormSq (u - w) < δ := hwapprox
  have hresNonneg := E.toClosedForm.form_nonneg (u - w)
    (E.toClosedForm.domain.sub_mem hu hwD)
  have hres : E.toClosedForm.form (u - w) (u - w) < δ :=
    lt_of_le_of_lt E.toClosedForm.form_le_energyNormSq heps
  have hresD : u - w ∈ E.toClosedForm.domain :=
    E.toClosedForm.domain.sub_mem hu hwD
  have hwu : E.toClosedForm.form (w - u) (w - u) =
      E.toClosedForm.form (u - w) (u - w) := by
    have hneg : w - u = -(u - w) := by abel
    rw [hneg, E.toClosedForm.form_neg_left hresD
      (E.toClosedForm.domain.neg_mem hresD), E.toClosedForm.form_neg_right hresD hresD]
    ring
  have hWbound : E.toClosedForm.form w w ≤
      2 * (E.toClosedForm.form u u + E.toClosedForm.form (u - w) (u - w)) := by
    have h := ClosedForm.form_add_self_le_two E.toClosedForm hu
      (E.toClosedForm.domain.sub_mem hwD hu)
    have hsum : u + (w - u) = w := by abel
    calc
      E.toClosedForm.form w w =
          E.toClosedForm.form (u + (w - u)) (u + (w - u)) := by rw [hsum]
      _ ≤ 2 * (E.toClosedForm.form u u + E.toClosedForm.form (w - u) (w - u)) := h
      _ = 2 * (E.toClosedForm.form u u + E.toClosedForm.form (u - w) (u - w)) := by rw [hwu]
  have hplus := ClosedForm.form_add_self_le_two E.toClosedForm hu hwD
  have hA : E.toClosedForm.form (u + w) (u + w) ≤ K := by
    dsimp [K]
    have hresle : E.toClosedForm.form (u - w) (u - w) ≤ 1 :=
      hres.le.trans (min_le_left _ _)
    nlinarith
  let A := E.toClosedForm.form (u + w) (u + w)
  let R := E.toClosedForm.form (u - w) (u - w)
  have hAnonneg : 0 ≤ A := E.toClosedForm.form_nonneg (u + w)
    (E.toClosedForm.domain.add_mem hu hwD)
  have hRnonneg : 0 ≤ R := hresNonneg
  have hRle : R ≤ δ := hres.le
  have hFw : w ∈ F.toClosedForm.domain := hdom.symm ▸ hwD
  have hmeasureCore := ΓE.measure_eq_smul_of_core ΓF Q hCore hc hdom hform hwC
  have hscaleW : (ΓF.measure w B).toReal = c * (ΓE.measure w B).toReal := by
    have hmass : ΓF.measure w B = (ENNReal.ofReal c • ΓE.measure w) B :=
      congrArg (fun μ : Measure X => μ B) hmeasureCore
    rw [Measure.smul_apply, smul_eq_mul] at hmass
    rw [hmass, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le]
  have hdevF := ΓF.abs_toReal_measure_sub_le_form hFu hFw hB
  have hdevE := ΓE.abs_toReal_measure_sub_le_form hu hwD hB
  have hformPlus := hform (u + w) (E.toClosedForm.domain.add_mem hu hwD)
  have hformMinus := hform (u - w) (E.toClosedForm.domain.sub_mem hu hwD)
  have hdevF' : |a - (ΓF.measure w B).toReal| ≤
      c * (Real.sqrt A * Real.sqrt R) := by
    calc
      |(ΓF.measure u B).toReal - (ΓF.measure w B).toReal| ≤
          Real.sqrt (c * E.toClosedForm.form (u + w) (u + w)) *
            Real.sqrt (c * E.toClosedForm.form (u - w) (u - w)) := by
              simpa [hformPlus, hformMinus] using hdevF
      _ = c * (Real.sqrt (E.toClosedForm.form (u + w) (u + w)) *
            Real.sqrt (E.toClosedForm.form (u - w) (u - w))) := by
              rw [Real.sqrt_mul hc.le, Real.sqrt_mul hc.le]
              calc
                (Real.sqrt c * Real.sqrt (E.toClosedForm.form (u + w) (u + w))) *
                    (Real.sqrt c * Real.sqrt (E.toClosedForm.form (u - w) (u - w))) =
                    (Real.sqrt c * Real.sqrt c) *
                      (Real.sqrt (E.toClosedForm.form (u + w) (u + w)) *
                        Real.sqrt (E.toClosedForm.form (u - w) (u - w))) := by ring
                _ = c * (Real.sqrt (E.toClosedForm.form (u + w) (u + w)) *
                      Real.sqrt (E.toClosedForm.form (u - w) (u - w))) := by
                    rw [← pow_two, Real.sq_sqrt hc.le]
  have hdevE' : |(ΓE.measure u B).toReal - (ΓE.measure w B).toReal| ≤
      Real.sqrt A * Real.sqrt R := by
    simpa [A, R] using hdevE
  have htriangle : D ≤ 2 * c * (Real.sqrt A * Real.sqrt R) := by
    have hdecomp : a - c * b =
        ((ΓF.measure u B).toReal - (ΓF.measure w B).toReal) +
          c * ((ΓE.measure w B).toReal - (ΓE.measure u B).toReal) := by
      rw [hscaleW]
      dsimp [a, b]
      ring
    have habs := abs_add_le
      ((ΓF.measure u B).toReal - (ΓF.measure w B).toReal)
      (c * ((ΓE.measure w B).toReal - (ΓE.measure u B).toReal))
    have hsecond : |c * ((ΓE.measure w B).toReal - (ΓE.measure u B).toReal)| =
        c * |(ΓE.measure u B).toReal - (ΓE.measure w B).toReal| := by
      rw [abs_mul, abs_of_pos hc, abs_sub_comm]
    calc
      |a - c * b| =
          |((ΓF.measure u B).toReal - (ΓF.measure w B).toReal) +
            c * ((ΓE.measure w B).toReal - (ΓE.measure u B).toReal)| := by rw [hdecomp]
      _ ≤ |(ΓF.measure u B).toReal - (ΓF.measure w B).toReal| +
          |c * ((ΓE.measure w B).toReal - (ΓE.measure u B).toReal)| := habs
      _ = |(ΓF.measure u B).toReal - (ΓF.measure w B).toReal| +
          c * |(ΓE.measure u B).toReal - (ΓE.measure w B).toReal| := by rw [hsecond]
      _ ≤ c * (Real.sqrt A * Real.sqrt R) + c * (Real.sqrt A * Real.sqrt R) := by
        exact add_le_add hdevF' (mul_le_mul_of_nonneg_left hdevE' hc.le)
      _ = 2 * c * (Real.sqrt A * Real.sqrt R) := by ring
  have hsqrtbound : 2 * c * (Real.sqrt A * Real.sqrt R) ≤ D / 2 := by
    have hsA : Real.sqrt A ≤ Real.sqrt K := Real.sqrt_le_sqrt hA
    have hsR : Real.sqrt R ≤ Real.sqrt δ := Real.sqrt_le_sqrt hRle
    have hsprod : Real.sqrt A * Real.sqrt R ≤ Real.sqrt K * Real.sqrt δ :=
      mul_le_mul hsA hsR (Real.sqrt_nonneg R) (Real.sqrt_nonneg K)
    have hKδ : K * δ ≤ D ^ 2 / (16 * c ^ 2) := by
      calc
        K * δ ≤ K * (D ^ 2 / (16 * c ^ 2 * K)) :=
          mul_le_mul_of_nonneg_left hδle hK.le
        _ = D ^ 2 / (16 * c ^ 2) := by
          field_simp [ne_of_gt hc, ne_of_gt hK]
    have hroot : Real.sqrt (K * δ) ≤ D / (4 * c) := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · calc
          K * δ ≤ D ^ 2 / (16 * c ^ 2) := hKδ
          _ = (D / (4 * c)) ^ 2 := by
            field_simp [ne_of_gt hc]
            <;> ring
    calc
      2 * c * (Real.sqrt A * Real.sqrt R) ≤
          2 * c * (Real.sqrt K * Real.sqrt δ) :=
        mul_le_mul_of_nonneg_left hsprod (by positivity)
      _ = 2 * c * Real.sqrt (K * δ) := by
        rw [← Real.sqrt_mul hK.le]
      _ ≤ 2 * c * (D / (4 * c)) := mul_le_mul_of_nonneg_left hroot (by positivity)
      _ = D / 2 := by field_simp [ne_of_gt hc] <;> norm_num
  linarith

/-- Event-level supplier with exactly the `hGammaScale` implication shape. Its
additional premise is the regular relative core needed for the Radon uniqueness
argument. -/
theorem ae_measure_scale_of_relative_core [BorelSpace X] [T2Space X]
    [LocallyCompactSpace X] [OpensMeasurableSpace X] {ι Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (Q : ι → Opens X) (m : ι → Measure X)
    (E F : (i : ι) → Ω → DirichletForm (m i))
    (ΓE : (i : ι) → (ω : Ω) → EnergyMeasure (E i ω).toClosedForm)
    (ΓF : (i : ι) → (ω : Ω) → EnergyMeasure (F i ω).toClosedForm)
    (hCore : ∀ᵐ ω ∂P, ∀ i, ∃ C,
      IsCoreOn (E i ω).toClosedForm (Q i : Set X) C) :
    ∀ᵐ ω ∂P, ∀ i (c : ℝ), 0 < c →
      (F i ω).toClosedForm.domain = (E i ω).toClosedForm.domain →
      (∀ u ∈ (E i ω).toClosedForm.domain,
        (F i ω).toClosedForm.form u u = c * (E i ω).toClosedForm.form u u) →
      ∀ u ∈ (E i ω).toClosedForm.domain,
        (ΓF i ω).measure u = ENNReal.ofReal c • (ΓE i ω).measure u := by
  filter_upwards [hCore] with ω hCoreω
  intro i c hc hdom hform u hu
  obtain ⟨C, hC⟩ := hCoreω i
  exact (ΓE i ω).measure_eq_smul_of_form_scale (ΓF i ω) (Q i) hC hc hdom hform hu

end EnergyMeasure

end DirichletForm
