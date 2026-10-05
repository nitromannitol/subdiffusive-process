module

public import SubdiffusiveProcess.Paper.cor_14
public import SubdiffusiveProcess.Paper.lem_borel_weights
public import SubdiffusiveProcess.Paper.lem_common_perturbation_equations
public import SubdiffusiveProcess.Paper.lem_common_identity_step
public import SubdiffusiveProcess.Paper.lem_common_energy_estimate
public import SubdiffusiveProcess.Paper.lem_diff
public import SubdiffusiveProcess.Paper.lem_sincos
public import SubdiffusiveProcess.Paper.optimal_endpoints
public import SubdiffusiveProcess.Paper.common_trace_class
public import SubdiffusiveProcess.Paper.prop_boundary
public import SubdiffusiveProcess.Paper.prop_killed_consistency
public import SubdiffusiveProcess.Paper.thm_C0
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Filter TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

namespace SubdiffusiveProcess.Paper
noncomputable section

theorem aux_lem_relvar_localized_weighted_minimizer_difference_killed_measure_compl
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    {m : Measure X} {E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m}
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E) (U : Set X) (hU : IsOpen U)
    (D : Submodule ℝ (Lp ℝ 2 m))
    (hD : _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E U D)
    {v : Lp ℝ 2 m} (hv : v ∈ D) :
    Gamma.measure v Uᶜ = 0 := by
  obtain ⟨w, hw, hconv⟩ := hD.exists_seq hv
  have hdomv : v ∈ E.domain := hD.le_domain hv
  have hA : MeasurableSet Uᶜ := hU.measurableSet.compl
  have hle : ∀ n : ℕ,
      (Gamma.measure v Uᶜ).toReal ≤ E.energyNormSq (v - w n) := by
    intro n
    have hwn : w n ∈ E.domain := (hw n).mem_domain
    have hvwn : v - w n ∈ E.domain := E.domain.sub_mem hdomv hwn
    obtain ⟨f, hf, hcs, hsupp, ha⟩ := (hw n).hasCoreRep
    have hzero : Gamma.measure (w n) Uᶜ = 0 := by
      apply measure_mono_null
        (show Uᶜ ⊆ (tsupport f)ᶜ by
          intro x hxU hxF
          exact hxU (hsupp hxF))
      exact Gamma.measure_compl_tsupport (w n) hwn f hf ha
    have hcross : Gamma.cross (v - w n) (w n) Uᶜ = 0 := by
      have hc := Gamma.abs_cross_le (v - w n) hvwn (w n) hwn Uᶜ hA
      rw [hzero] at hc
      have habs : |Gamma.cross (v - w n) (w n) Uᶜ| ≤ 0 := by simpa using hc
      exact abs_eq_zero.mp (le_antisymm habs (abs_nonneg _))
    have hvsplit : v = (v - w n) + w n := by abel
    have hdiag : (Gamma.measure v Uᶜ).toReal =
        (Gamma.measure (v - w n) Uᶜ).toReal := by
      calc
        (Gamma.measure v Uᶜ).toReal = Gamma.cross v v Uᶜ :=
          (Gamma.cross_self v hdomv Uᶜ hA).symm
        _ = Gamma.cross ((v - w n) + w n) ((v - w n) + w n) Uᶜ := by
          exact congrArg (fun x => Gamma.cross x x Uᶜ) hvsplit
        _ = Gamma.cross (v - w n) (v - w n) Uᶜ +
            2 * Gamma.cross (v - w n) (w n) Uᶜ +
            Gamma.cross (w n) (w n) Uᶜ :=
          Gamma.cross_add_self_apply hvwn hwn Uᶜ
        _ = (Gamma.measure (v - w n) Uᶜ).toReal := by
          rw [hcross, Gamma.cross_self (w n) hwn Uᶜ hA, hzero,
            Gamma.cross_self (v - w n) hvwn Uᶜ hA]
          simp
    calc
      (Gamma.measure v Uᶜ).toReal = (Gamma.measure (v - w n) Uᶜ).toReal := hdiag
      _ ≤ (Gamma.measure (v - w n) Set.univ).toReal :=
        Gamma.toReal_measure_mono hvwn (Set.subset_univ _)
      _ = E.form (v - w n) (v - w n) := Gamma.measure_univ _ hvwn
      _ ≤ E.energyNormSq (v - w n) := E.form_le_energyNormSq
  have hlim : Tendsto (fun n : ℕ => E.energyNormSq (v - w n)) atTop (𝓝 0) := hconv
  have hconst : Tendsto (fun _ : ℕ => (Gamma.measure v Uᶜ).toReal)
      atTop (𝓝 (Gamma.measure v Uᶜ).toReal) := tendsto_const_nhds
  have hzero_real : (Gamma.measure v Uᶜ).toReal = 0 := by
    exact tendsto_nhds_unique hconst (squeeze_zero
      (fun _ => ENNReal.toReal_nonneg) hle hlim)
  exact ((ENNReal.toReal_eq_zero_iff _).mp hzero_real).resolve_right
    (Gamma.measure_ne_top hdomv Uᶜ)

theorem aux_lem_relvar_localized_weighted_minimizer_difference_measure_min_to_form
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    {m : Measure X} {E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m}
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E) (U : Set X) (hU : IsOpen U)
    (D : Submodule ℝ (Lp ℝ 2 m))
    (hDdom : D ≤ E.domain)
    (hvanish : ∀ v ∈ D, Gamma.measure v Uᶜ = 0)
    {u u₀ : Lp ℝ 2 m} (hu : u ∈ E.domain)
    (htrace : u - u₀ ∈ D)
    (hmin : ∀ v ∈ E.domain, v - u₀ ∈ D →
      (Gamma.measure u U).toReal ≤ (Gamma.measure v U).toReal) :
    ∀ v ∈ D, E.form u u ≤ E.form (u + v) (u + v) := by
  intro v hv
  have hvE : v ∈ E.domain := hDdom hv
  have huvE : u + v ∈ E.domain := E.domain.add_mem hu hvE
  have hUmeas : MeasurableSet U := hU.measurableSet
  have hvzero : Gamma.measure v Uᶜ = 0 :=
    hvanish v hv
  have hcrosszero : Gamma.cross u v Uᶜ = 0 := by
    have hc := Gamma.abs_cross_le u hu v hvE Uᶜ hUmeas.compl
    rw [hvzero] at hc
    exact abs_eq_zero.mp (le_antisymm (by simpa using hc) (abs_nonneg _))
  have hpart : ∀ (x : Lp ℝ 2 m), x ∈ E.domain →
      (Gamma.measure x U).toReal + (Gamma.measure x Uᶜ).toReal = E.form x x := by
    intro x hx
    calc
      (Gamma.measure x U).toReal + (Gamma.measure x Uᶜ).toReal =
          (Gamma.measure x U + Gamma.measure x Uᶜ).toReal := by
            rw [ENNReal.toReal_add (Gamma.measure_ne_top hx U)
              (Gamma.measure_ne_top hx Uᶜ)]
      _ = (Gamma.measure x Set.univ).toReal := by rw [measure_add_measure_compl hUmeas]
      _ = E.form x x := Gamma.measure_univ x hx
  have hout : (Gamma.measure (u + v) Uᶜ).toReal =
      (Gamma.measure u Uᶜ).toReal := by
    rw [← Gamma.cross_self (u + v) huvE Uᶜ hUmeas.compl,
      Gamma.cross_add_self_apply hu hvE Uᶜ,
      Gamma.cross_self u hu Uᶜ hUmeas.compl,
      Gamma.cross_self v hvE Uᶜ hUmeas.compl, hvzero, hcrosszero]
    simp
  have hlocaldiff :
      (Gamma.measure (u + v) U).toReal - (Gamma.measure u U).toReal =
        E.form (u + v) (u + v) - E.form u u := by
    linarith [hpart u hu, hpart (u + v) huvE, hout]
  have hmin' : (Gamma.measure u U).toReal ≤
      (Gamma.measure (u + v) U).toReal := by
    apply hmin (u + v) huvE
    rw [show u + v - u₀ = (u - u₀) + v by abel]
    exact D.add_mem htrace hv
  linarith



theorem lem_relvar_localized_weighted_minimizer_difference
    (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (d : ℕ) (_hd : 2 ≤ d)
      (slopes : Finset (Fin d → ℝ))
      (_hslopes : ∀ p : Fin d → ℝ,
        p ∈ slopes ↔ (∃ i : Fin d, p = Pi.single i (1 : ℝ)) ∨
          (∃ i j : Fin d, p = Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ))),
    ∀ (Q : Opens (SpatialCoordinates d)) (z : SpatialCoordinates d) (r : ℝ)
      (hr : 0 < r)
      (_hQ : ∃ (zQ : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ),
        Q = centeredCube zQ rQ hrQ),
    let q := centeredCube z r hr
    ∀ (_hinside : closure (q : Set (SpatialCoordinates d)) ⊆
        (Q : Set (SpatialCoordinates d)))
      (E F Eg Fg : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
        (volume.restrict (Q : Set (SpatialCoordinates d))))
      (GammaE : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
      (GammaF : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure F)
      (GammaEg : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure Eg)
      (GammaFg : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure Fg)
      (_hdomEF : E.domain = F.domain)
      (_hdomEg : Eg.domain = E.domain)
      (_hdomFg : Fg.domain = E.domain)
      (V0 : Submodule ℝ (DomainL2 Q))
      (_hzero : _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E (q : Set (SpatialCoordinates d)) V0)
      (m M c : ℝ) (_hm : C0⁻¹ ≤ m) (_hmM : m ≤ M) (_hM : M ≤ C0)
      (_hmc : m ≤ c) (_hcM : c ≤ M)
      (_horder : ∀ u ∈ E.domain, ∀ A : Set (SpatialCoordinates d),
        MeasurableSet A →
          m * (GammaE.measure u A).toReal ≤ (GammaF.measure u A).toReal ∧
            (GammaF.measure u A).toReal ≤ M * (GammaE.measure u A).toReal)
      (g : SpatialCoordinates d → ℝ) (_hg : Measurable g)
      (B : Set (SpatialCoordinates d)) (_hB : MeasurableSet B)
      (_hBq : B ⊆ (q : Set (SpatialCoordinates d)))
      (_hsupp : ∀ x, x ∉ B → g x = 0)
      (G : ℝ) (_hG : IsLUB (Set.range (fun x => |g x|)) G)
      (_hbdd : BddAbove (Set.range (fun x => |g x|)))
      (_hweightE : ∀ u ∈ E.domain, ∀ A : Set (SpatialCoordinates d),
        MeasurableSet A →
          GammaEg.measure u A =
            ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(GammaE.measure u))
      (_hweightF : ∀ u ∈ F.domain, ∀ A : Set (SpatialCoordinates d),
        MeasurableSet A →
          GammaFg.measure u A =
            ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(GammaF.measure u))
      (_hweightE_cross : ∀ u ∈ E.domain, ∀ v ∈ E.domain,
        ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
          GammaEg.cross u v A =
            _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (GammaE.cross u v) A
              (fun x => Real.exp (g x)))
      (_hweightF_cross : ∀ u ∈ F.domain, ∀ v ∈ F.domain,
        ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
          GammaFg.cross u v A =
            _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (GammaF.cross u v) A
              (fun x => Real.exp (g x)))
      (uE uF uEg uFg : (Fin d → ℝ) → DomainL2 Q)
      (_huE : ∀ p, uE p ∈ E.domain)
      (_huF : ∀ p, uF p ∈ F.domain)
      (_huEg : ∀ p, uEg p ∈ Eg.domain)
      (_huFg : ∀ p, uFg p ∈ Fg.domain)
      (_htraceF : ∀ p, uF p - uE p ∈ V0)
      (_htraceEg : ∀ p, uEg p - uE p ∈ V0)
      (_htraceFg : ∀ p, uFg p - uE p ∈ V0)
      (_hminE : ∀ p, ∀ v ∈ E.domain, v - uE p ∈ V0 →
        (GammaE.measure (uE p) q).toReal ≤ (GammaE.measure v q).toReal)
      (_hminF : ∀ p, ∀ v ∈ F.domain, v - uE p ∈ V0 →
        (GammaF.measure (uF p) q).toReal ≤ (GammaF.measure v q).toReal)
      (_hminEg : ∀ p, ∀ v ∈ Eg.domain, v - uE p ∈ V0 →
        (GammaEg.measure (uEg p) q).toReal ≤ (GammaEg.measure v q).toReal)
      (_hminFg : ∀ p, ∀ v ∈ Fg.domain, v - uE p ∈ V0 →
        (GammaFg.measure (uFg p) q).toReal ≤ (GammaFg.measure v q).toReal),
    ∀ p ∈ slopes,
      (let w := uF p - uE p;
       let vE := uEg p - uE p;
       let vF := uFg p - uF p;
       let z := vF - vE;
      (GammaEg.measure z q).toReal ≤
        C * G ^ 2 * Real.exp (C * G) *
          ((GammaE.measure w B).toReal +
            (M - m) ^ 2 * (GammaE.measure (uE p) B).toReal)) := by
  obtain ⟨C, hCpos, hEst⟩ := lem_common_energy_estimate C0 hC0
  refine ⟨C, hCpos, ?_⟩
  intro d hd slopes hslopes Q z r hr hQ q hinside E F Eg Fg GammaE GammaF GammaEg GammaFg hdomEF hdomEg hdomFg V0 hzero m M c hm hmM hM hmc hcM horder g hg B hB hBq hsupp G hG hbdd hweightE hweightF hweightE_cross hweightF_cross uE uF uEg uFg huE huF huEg huFg htraceF htraceEg htraceFg hminE hminF hminEg hminFg p hp
  have hqmeas : MeasurableSet (q : Set (SpatialCoordinates d)) :=
    q.isOpen.measurableSet
  have hvanishE : ∀ v ∈ V0,
      GammaE.measure v (q : Set (SpatialCoordinates d))ᶜ = 0 := by
    intro v hv
    exact aux_lem_relvar_localized_weighted_minimizer_difference_killed_measure_compl
      GammaE (q : Set (SpatialCoordinates d)) q.isOpen V0 hzero hv
  have hVdomF : V0 ≤ F.domain := by
    intro v hv
    rw [← hdomEF]
    exact hzero.le_domain hv
  have hVdomEg : V0 ≤ Eg.domain := by
    intro v hv
    rw [hdomEg]
    exact hzero.le_domain hv
  have hVdomFg : V0 ≤ Fg.domain := by
    intro v hv
    rw [hdomFg]
    exact hzero.le_domain hv
  have hvanishF : ∀ v ∈ V0,
      GammaF.measure v (q : Set (SpatialCoordinates d))ᶜ = 0 := by
    intro v hv
    have hvE : v ∈ E.domain := hzero.le_domain hv
    have hvF : v ∈ F.domain := hVdomF hv
    have hup := (horder v hvE (q : Set (SpatialCoordinates d))ᶜ hqmeas.compl).2
    rw [hvanishE v hv] at hup
    have hzero_real : (GammaF.measure v (q : Set (SpatialCoordinates d))ᶜ).toReal = 0 :=
      le_antisymm (by simpa using hup) ENNReal.toReal_nonneg
    exact ((ENNReal.toReal_eq_zero_iff _).mp hzero_real).resolve_right
      (GammaF.measure_ne_top hvF (q : Set (SpatialCoordinates d))ᶜ)
  have hvanishEg : ∀ v ∈ V0,
      GammaEg.measure v (q : Set (SpatialCoordinates d))ᶜ = 0 := by
    intro v hv
    have hvE : v ∈ E.domain := hzero.le_domain hv
    have hzeroE := hvanishE v hv
    have hrst : (GammaE.measure v).restrict
        (q : Set (SpatialCoordinates d))ᶜ = 0 :=
      Measure.restrict_zero_set hzeroE
    rw [hweightE v hvE _ hqmeas.compl]
    simp [hrst]
  have hvanishFg : ∀ v ∈ V0,
      GammaFg.measure v (q : Set (SpatialCoordinates d))ᶜ = 0 := by
    intro v hv
    have hvF : v ∈ F.domain := hVdomF hv
    have hzeroF := hvanishF v hv
    have hrst : (GammaF.measure v).restrict
        (q : Set (SpatialCoordinates d))ᶜ = 0 :=
      Measure.restrict_zero_set hzeroF
    rw [hweightF v hvF _ hqmeas.compl]
    simp [hrst]
  have hminE' : ∀ v ∈ V0, E.form (uE p) (uE p) ≤
      E.form (uE p + v) (uE p + v) :=
    aux_lem_relvar_localized_weighted_minimizer_difference_measure_min_to_form
      GammaE (q : Set (SpatialCoordinates d)) q.isOpen V0 hzero.le_domain hvanishE
      (huE p) (by simp) (hminE p)
  have hminF' : ∀ v ∈ V0, F.form (uF p) (uF p) ≤
      F.form (uF p + v) (uF p + v) :=
    aux_lem_relvar_localized_weighted_minimizer_difference_measure_min_to_form
      GammaF (q : Set (SpatialCoordinates d)) q.isOpen V0 hVdomF hvanishF
      (huF p) (htraceF p) (hminF p)
  have hminEg' : ∀ v ∈ V0, Eg.form (uEg p) (uEg p) ≤
      Eg.form (uEg p + v) (uEg p + v) :=
    aux_lem_relvar_localized_weighted_minimizer_difference_measure_min_to_form
      GammaEg (q : Set (SpatialCoordinates d)) q.isOpen V0 hVdomEg hvanishEg
      (huEg p) (htraceEg p) (hminEg p)
  have hminFg' : ∀ v ∈ V0, Fg.form (uFg p) (uFg p) ≤
      Fg.form (uFg p + v) (uFg p + v) :=
    aux_lem_relvar_localized_weighted_minimizer_difference_measure_min_to_form
      GammaFg (q : Set (SpatialCoordinates d)) q.isOpen V0 hVdomFg hvanishFg
      (huFg p) (htraceFg p) (hminFg p)
  have hpert := lem_common_perturbation_equations d hd Q z r hr hQ hinside
    E F Eg Fg GammaE GammaF GammaEg GammaFg hdomEF hdomEg hdomFg V0 hzero
    g hg B hB hBq hsupp G hG hbdd hweightE hweightF
    (uE p) (uF p) (uEg p) (uFg p) (huE p) (huF p) (huEg p) (huFg p)
    (htraceF p) (htraceEg p) (htraceFg p)
    hminE' hminF' hminEg' hminFg'
  have hid := lem_common_identity_step d hd Q z r hr hQ hinside
    E F Eg Fg GammaE GammaF GammaEg GammaFg hdomEF hdomEg hdomFg
    V0 hzero.le_domain g hg hbdd B hB c
    (uE p) (uF p) (uEg p) (uFg p) (huE p) (huF p) (huEg p) (huFg p) hpert
  have hest := hEst d hd Q z r hr hQ hinside E F Eg Fg GammaE GammaF GammaEg GammaFg
    hdomEF hdomEg hdomFg V0 hzero m M c hm hmM hM hmc hcM horder
    g hg B hB hBq hsupp G hG hbdd hweightE hweightF
    (uE p) (uF p) (uEg p) (uFg p) (huE p) (huF p) (huEg p) (huFg p)
    (htraceF p) (htraceEg p) (htraceFg p)
    hminE' hminF' hminEg' hminFg' hid
  dsimp only
  have htraceFgF : uFg p - uF p ∈ V0 := by
    rw [show uFg p - uF p = (uFg p - uE p) - (uF p - uE p) by abel]
    exact V0.sub_mem (htraceFg p) (htraceF p)
  have hzV : (uFg p - uF p) - (uEg p - uE p) ∈ V0 :=
    V0.sub_mem htraceFgF (htraceEg p)
  have hzEg : (uFg p - uF p) - (uEg p - uE p) ∈ Eg.domain :=
    hVdomEg hzV
  have hpartEg :
      (GammaEg.measure ((uFg p - uF p) - (uEg p - uE p))
        (q : Set (SpatialCoordinates d))).toReal +
        (GammaEg.measure ((uFg p - uF p) - (uEg p - uE p))
          (q : Set (SpatialCoordinates d))ᶜ).toReal =
        Eg.form ((uFg p - uF p) - (uEg p - uE p))
          ((uFg p - uF p) - (uEg p - uE p)) := by
    calc
      _ = (GammaEg.measure ((uFg p - uF p) - (uEg p - uE p))
          (q : Set (SpatialCoordinates d)) +
          GammaEg.measure ((uFg p - uF p) - (uEg p - uE p))
            (q : Set (SpatialCoordinates d))ᶜ).toReal := by
        rw [ENNReal.toReal_add
          (GammaEg.measure_ne_top hzEg (q : Set (SpatialCoordinates d)))
          (GammaEg.measure_ne_top hzEg (q : Set (SpatialCoordinates d))ᶜ)]
      _ = (GammaEg.measure ((uFg p - uF p) - (uEg p - uE p)) Set.univ).toReal := by
        rw [measure_add_measure_compl hqmeas]
      _ = Eg.form ((uFg p - uF p) - (uEg p - uE p))
          ((uFg p - uF p) - (uEg p - uE p)) := GammaEg.measure_univ _ hzEg
  have hmeasure_form :
      (GammaEg.measure ((uFg p - uF p) - (uEg p - uE p))
        (q : Set (SpatialCoordinates d))).toReal =
        Eg.form ((uFg p - uF p) - (uEg p - uE p))
          ((uFg p - uF p) - (uEg p - uE p)) := by
    rw [hvanishEg _ hzV] at hpartEg
    simpa using hpartEg
  rw [hmeasure_form]
  exact hest

end
end SubdiffusiveProcess.Paper
