module

public import SubdiffusiveProcess.DirichletForm.FOTEnergyFamily

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped NNReal ContDiff

noncomputable section

namespace DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [BorelSpace X] {m : Measure X}

/-- Relative compact support, expressed in the form used by strong locality. -/
theorem core_compact_support {F : _root_.DirichletForm m} {U : Set X}
    {u : Lp ℝ 2 m} (hu : F.toClosedForm.MemCoreOn U u) :
    ∃ K : Set X, IsCompact K ∧ K ⊆ U ∧ ∀ᵐ x ∂m, x ∉ K → u x = 0 := by
  obtain ⟨f, _, hf, hfU, hae⟩ := hu.2
  refine ⟨tsupport f, hf, hfU, ?_⟩
  filter_upwards [hae] with x hx hxK
  rw [hx]
  exact image_eq_zero_of_notMem_tsupport hxK

/-- A core function constant on an open set has zero energy there. -/
theorem EnergyFamily.measure_eq_zero_of_core_constant {F : _root_.DirichletForm m}
    {U : Set X} (h : Data F U) (Γ : EnergyFamily F U) {u : Lp ℝ 2 m}
    (hu : F.toClosedForm.MemCoreOn U u) {uc : X → ℝ} (huc : Continuous uc)
    (huae : ⇑u =ᵐ[m] uc) {O : Set X} (hO : IsOpen O) {c : ℝ}
    (hc : ∀ x ∈ O, uc x = c) : Γ.measure u O = 0 := by
  letI : (Γ.measure u).Regular := Γ.regular u hu.1
  letI : IsFiniteMeasure (Γ.measure u) := ⟨Γ.finite u hu.1⟩
  have hKzero : ∀ K : Set X, K ⊆ O ∩ U → IsCompact K → Γ.measure u K = 0 := by
    intro K hKO hK
    obtain ⟨C, hcore⟩ := h.core
    obtain ⟨φ, φc, V, hφ, hφc, hφcs, hφO, hφae, hφ01, _, hKV, hφV⟩ :=
      hcore.exists_cutoff F hK (hO.inter h.isOpen) hKO inter_subset_right
    have hφUW : tsupport φc ⊆ U ∩ O :=
      fun x hx => ⟨(hφO hx).2, (hφO hx).1⟩
    have hφsupp : ∃ L : Set X, IsCompact L ∧ L ⊆ U ∩ O ∧
        ∀ᵐ x ∂m, x ∉ L → φ x = 0 := by
      refine ⟨tsupport φc, hφcs, hφUW, ?_⟩
      filter_upwards [hφae] with x hx hxL
      rw [hx]
      exact image_eq_zero_of_notMem_tsupport hxL
    have hconst : ∀ᵐ x ∂m, x ∈ O → u x = c := by
      filter_upwards [huae] with x hx hxO
      rw [hx, hc x hxO]
    have huφ : ⇑(c • φ) =ᵐ[m] fun x => uc x * φc x := by
      filter_upwards [Lp.coeFn_smul c φ, hφae] with x h1 h2
      simp only [h1, Pi.smul_apply, smul_eq_mul, h2]
      by_cases hx : x ∈ O
      · rw [hc x hx]
      · have hz : φc x = 0 := image_eq_zero_of_notMem_tsupport
          (fun ht => hx (hφO ht).1)
        rw [hz, mul_zero, mul_zero]
    obtain ⟨R, hR⟩ := ae_abs_le_of_memCoreOn hu
    obtain ⟨u2, hu2, hu2ae⟩ := F.exists_mul_mem hu.1 hu.1 hR hR
    have hu2sq : ⇑u2 =ᵐ[m] fun x => uc x ^ 2 := by
      filter_upwards [hu2ae, huae] with x hx hy
      rw [hx, hy, pow_two]
    have hu2core : F.toClosedForm.MemCoreOn U u2 := by
      obtain ⟨f, hf, hfc, hfU, hfae⟩ := hu.2
      refine ⟨hu2, fun x => f x ^ 2, hf.pow 2,
        hfc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num), ?_, ?_⟩
      · exact (tsupport_comp_subset (g := fun t : ℝ => t ^ 2) (by norm_num) f).trans hfU
      · filter_upwards [hu2ae, hfae] with x hx hy
        rw [hx, hy, pow_two]
    have hu2const : ∀ᵐ x ∂m, x ∈ O → u2 x = c ^ 2 := by
      filter_upwards [hu2sq] with x hx hxO
      rw [hx, hc x hxO]
    have hE1 := h.stronglyLocal u hu.1 φ hφ.1 (core_compact_support hu)
      c O hO hφsupp hconst
    have hE2 := h.stronglyLocal u2 hu2 φ hφ.1 (core_compact_support hu2core)
      (c ^ 2) O hO hφsupp hu2const
    have hi : ∫ x, φc x ∂Γ.measure u = 0 := by
      rw [Γ.defining u φ hu hφ uc φc huc hφc huae hφae (c • φ) u2
        (F.domain.smul_mem c hφ.1) hu2 huφ hu2sq,
        F.toClosedForm.form_smul_right c hu.1 hφ.1, hE1, hE2]
      ring
    have hφint : Integrable φc (Γ.measure u) := by
      exact hφc.integrable_of_hasCompactSupport hφcs
    have hb := hφint.measure_le_integral
      (Eventually.of_forall fun x => (hφ01 x).1)
      (fun x hx => (hφV x (hKV hx)).ge)
    rw [hi, ENNReal.ofReal_zero] at hb
    exact le_zero_iff.mp hb
  have hOU : Γ.measure u (O ∩ U) = 0 := by
    rw [(hO.inter h.isOpen).measure_eq_iSup_isCompact (Γ.measure u)]
    exact ENNReal.iSup_eq_zero.mpr fun K => ENNReal.iSup_eq_zero.mpr fun hKO =>
      ENNReal.iSup_eq_zero.mpr fun hK => hKzero K hKO hK
  rw [← measure_inter_conull (Γ.carried u hu.1)]
  exact hOU

/-- Zero local energy of a difference implies equality of the two local energies. -/
theorem EnergyFamily.toReal_measure_eq_of_difference_zero {F : _root_.DirichletForm m}
    {U : Set X} (Γ : EnergyFamily F U) {u v : Lp ℝ 2 m}
    (hu : u ∈ F.domain) (hv : v ∈ F.domain) {B : Set X} (hB : MeasurableSet B)
    (hd : Γ.measure (u - v) B = 0) :
    (Γ.measure u B).toReal = (Γ.measure v B).toReal := by
  have hdiff := F.domain.sub_mem hu hv
  have hz (w : Lp ℝ 2 m) (hw : w ∈ F.domain) : Γ.cross (u - v) w B = 0 := by
    have hle := Γ.cross_le (u - v) hdiff w hw B hB
    rw [hd, ENNReal.toReal_zero, Real.sqrt_zero, zero_mul] at hle
    exact abs_nonpos_iff.mp hle
  have hdu := hz u hu
  have hdv := hz v hv
  have hs : u - v = u + (-1 : ℝ) • v := by module
  rw [hs, Γ.cross_add_left hu (F.domain.smul_mem (-1) hv) hu,
    Γ.cross_smul_left (-1) hv hu, VectorMeasure.add_apply, VectorMeasure.smul_apply,
    smul_eq_mul, Γ.cross_self u hu B hB, Γ.cross_symm v hv u hu] at hdu
  rw [hs, Γ.cross_add_left hu (F.domain.smul_mem (-1) hv) hv,
    Γ.cross_smul_left (-1) hv hv, VectorMeasure.add_apply, VectorMeasure.smul_apply,
    smul_eq_mul, Γ.cross_self v hv B hB] at hdv
  linarith only [hdu, hdv]

/-- Continuous representatives of the same `Lp` element agree for every energy measure. -/
theorem EnergyFamily.ae_eq_of_continuous {F : _root_.DirichletForm m} {U : Set X}
    (h : Data F U) (Γ : EnergyFamily F U) {f g : X → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hae : f =ᵐ[m] g)
    {v : Lp ℝ 2 m} (hv : v ∈ F.domain) : f =ᵐ[Γ.measure v] g := by
  let O : Set X := {x | f x ≠ g x}
  have hO : IsOpen O := (isClosed_eq hf hg).isOpen_compl
  have hmO : m O = 0 := by
    exact ae_iff.mp hae
  have hv0 : ⇑v =ᵐ[m.restrict O] ⇑(0 : Lp ℝ 2 m) := by
    rw [Measure.restrict_eq_zero.mpr hmO]
    simp only [ae_zero, Filter.EventuallyEq, Filter.eventually_bot]
  have heq := Γ.locality h hv F.domain.zero_mem hO hv0
  have hz : Γ.measure (0 : Lp ℝ 2 m) = 0 := by
    apply Measure.measure_univ_eq_zero.mp
    have hr : (Γ.measure (0 : Lp ℝ 2 m) univ).toReal = 0 := by
      rw [Γ.mass _ F.domain.zero_mem, F.toClosedForm.form_zero_left F.domain.zero_mem]
    exact ((ENNReal.toReal_eq_zero_iff _).mp hr).resolve_right
      (Γ.measure_ne_top F.domain.zero_mem univ)
  have hvO : Γ.measure v O = 0 := by
    have hh := congrArg (fun μ : Measure X => μ univ) heq
    simpa [hz] using hh
  exact ae_iff.mpr hvO

/-- The zero function has zero energy measure. -/
theorem EnergyFamily.measure_zero {F : _root_.DirichletForm m} {U : Set X}
    (Γ : EnergyFamily F U) : Γ.measure (0 : Lp ℝ 2 m) = 0 := by
  apply Measure.measure_univ_eq_zero.mp
  have hr : (Γ.measure (0 : Lp ℝ 2 m) univ).toReal = 0 := by
    rw [Γ.mass _ F.domain.zero_mem, F.toClosedForm.form_zero_left F.domain.zero_mem]
  exact ((ENNReal.toReal_eq_zero_iff _).mp hr).resolve_right
    (Γ.measure_ne_top F.domain.zero_mem univ)

/-- A continuous representative carries its energy measure on its closed support. -/
theorem EnergyFamily.measure_compl_tsupport {F : _root_.DirichletForm m} {U : Set X}
    (h : Data F U) (Γ : EnergyFamily F U) {u : Lp ℝ 2 m} (hu : u ∈ F.domain)
    {f : X → ℝ} (hae : ⇑u =ᵐ[m] f) : Γ.measure u (tsupport f)ᶜ = 0 := by
  have hO : IsOpen (tsupport f)ᶜ := (isClosed_tsupport f).isOpen_compl
  have hu0 : ⇑u =ᵐ[m.restrict (tsupport f)ᶜ] ⇑(0 : Lp ℝ 2 m) := by
    apply (ae_restrict_iff' hO.measurableSet).mpr
    filter_upwards [hae, Lp.coeFn_zero ℝ 2 m] with x hx hz hxO
    rw [hx, hz]
    exact image_eq_zero_of_notMem_tsupport hxO
  have hh := congrArg (fun μ : Measure X => μ univ)
    (Γ.locality h hu F.domain.zero_mem hO hu0)
  simpa [Γ.measure_zero] using hh

end DirichletForm.FOTConstruction
