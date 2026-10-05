module

public import SubdiffusiveProcess.DirichletForm.FOTCoreCalculusResolvent

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped NNReal ContDiff RealInnerProductSpace

noncomputable section

namespace SubdiffusiveProcess.DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [BorelSpace X] {m : Measure X}

/-- Core test inequalities determine domination of the finite relative-core measures. -/
theorem EnergyFamily.measure_le_of_core_integral_le {F : _root_.SubdiffusiveProcess.DirichletForm m}
    {U : Set X} (h : Data F U) (Γ : EnergyFamily F U) {u w : Lp ℝ 2 m}
    (hu : u ∈ F.domain) (hw : w ∈ F.domain) {C : ℝ} (hC : 0 ≤ C)
    (htest : ∀ φ : Lp ℝ 2 m, F.toClosedForm.MemCoreOn U φ →
      ∀ φc : X → ℝ, Continuous φc → HasCompactSupport φc →
        tsupport φc ⊆ U → ⇑φ =ᵐ[m] φc → (∀ x, φc x ∈ Icc 0 1) →
          (∫ x, φc x ∂Γ.measure w) ≤ C * ∫ x, φc x ∂Γ.measure u) :
    Γ.measure w ≤ ENNReal.ofReal C • Γ.measure u := by
  let : (Γ.measure u).Regular := Γ.regular u hu
  let : (Γ.measure w).Regular := Γ.regular w hw
  let : IsFiniteMeasure (Γ.measure u) := ⟨Γ.finite u hu⟩
  let : IsFiniteMeasure (Γ.measure w) := ⟨Γ.finite w hw⟩
  have hcompact : ∀ K : Set X, IsCompact K → K ⊆ U →
      (Γ.measure w K).toReal ≤ C * (Γ.measure u K).toReal := by
    intro K hK hKU
    apply le_of_forall_pos_le_add
    intro ε hε
    let δ : ℝ := ε / (C + 1)
    have hδ : 0 < δ := div_pos hε (by linarith)
    obtain ⟨O, hKO, hO, hμO⟩ := K.exists_isOpen_lt_add
      (μ := Γ.measure u) (Γ.measure_ne_top hu K) (ENNReal.ofReal_pos.mpr hδ).ne'
    obtain ⟨Ccore, hcore⟩ := h.core
    obtain ⟨φ, φc, V, hφ, hφc, hφcs, hφO, hφae, hφ01, _, hKV, hφV⟩ :=
      hcore.exists_cutoff F hK (hO.inter h.isOpen)
        (fun x hx => ⟨hKO hx, hKU hx⟩) inter_subset_right
    have hi := htest φ hφ φc hφc hφcs (hφO.trans inter_subset_right) hφae hφ01
    have hwint : Integrable φc (Γ.measure w) := hφc.integrable_of_hasCompactSupport hφcs
    have hwK : (Γ.measure w K).toReal ≤ ∫ x, φc x ∂Γ.measure w := by
      apply (ENNReal.le_ofReal_iff_toReal_le (Γ.measure_ne_top hw K)
        (integral_nonneg fun x => (hφ01 x).1)).mp
      exact hwint.measure_le_integral (Eventually.of_forall fun x => (hφ01 x).1)
        (fun x hx => (hφV x (hKV hx)).ge)
    have huO : (∫ x, φc x ∂Γ.measure u) ≤ (Γ.measure u O).toReal := by
      apply (ENNReal.ofReal_le_iff_le_toReal (Γ.measure_ne_top hu O)).mp
      exact integral_le_measure (fun x _ => (hφ01 x).2) (fun x hx => by
        have hz : φc x = 0 := image_eq_zero_of_notMem_tsupport
          (fun ht => hx (hφO ht).1)
        exact hz.le)
    have hμOreal : (Γ.measure u O).toReal ≤ (Γ.measure u K).toReal + δ := by
      have hle := ENNReal.toReal_mono
        (ENNReal.add_ne_top.mpr ⟨Γ.measure_ne_top hu K, ENNReal.ofReal_ne_top⟩) hμO.le
      simpa only [ENNReal.toReal_add (Γ.measure_ne_top hu K) ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hδ.le] using hle
    have hCδ : C * δ ≤ ε := by
      dsimp [δ]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by linarith : 0 < C + 1)).mpr
      nlinarith only [hε]
    calc
      (Γ.measure w K).toReal ≤ C * (Γ.measure u O).toReal :=
        hwK.trans (hi.trans (mul_le_mul_of_nonneg_left huO hC))
      _ ≤ C * ((Γ.measure u K).toReal + δ) := mul_le_mul_of_nonneg_left hμOreal hC
      _ ≤ C * (Γ.measure u K).toReal + ε := by nlinarith only [hCδ]
  have hcompactENN : ∀ K : Set X, IsCompact K → K ⊆ U →
      Γ.measure w K ≤ (ENNReal.ofReal C • Γ.measure u) K := by
    intro K hK hKU
    rw [Measure.smul_apply, smul_eq_mul]
    apply (ENNReal.toReal_le_toReal (Γ.measure_ne_top hw K)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Γ.measure_ne_top hu K))).mp
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC]
    exact hcompact K hK hKU
  have hopen : ∀ O : Set X, IsOpen O →
      Γ.measure w O ≤ (ENNReal.ofReal C • Γ.measure u) O := by
    intro O hO
    rw [← measure_inter_conull (Γ.carried w hw),
      (hO.inter h.isOpen).measure_eq_iSup_isCompact (Γ.measure w)]
    apply iSup_le
    intro K
    apply iSup_le
    intro hKO
    apply iSup_le
    intro hK
    exact (hcompactENN K hK (hKO.trans inter_subset_right)).trans
      (measure_mono (hKO.trans inter_subset_left))
  apply Measure.le_iff'.mpr
  intro B
  let : (ENNReal.ofReal C • Γ.measure u).Regular :=
    Measure.Regular.smul ENNReal.ofReal_ne_top
  rw [B.measure_eq_iInf_isOpen (ENNReal.ofReal C • Γ.measure u)]
  exact le_iInf fun O => le_iInf fun hBO => le_iInf fun hO =>
    (measure_mono hBO).trans (hopen O hO)

omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [BorelSpace X] in
/-- Lipschitz domination of the energy functional in the form domain. -/
theorem core_lipschitz_functional_le [_instPreserved0 : TopologicalSpace X] [_instPreserved1 : T2Space X] [_instPreserved2 : LocallyCompactSpace X] [_instPreserved3 : BorelSpace X] {m : Measure X} (F : _root_.SubdiffusiveProcess.DirichletForm m)
    {T : ℝ → ℝ} {L : ℝ≥0} (hT : LipschitzWith L T) (hT0 : T 0 = 0)
    {u u2 w w2 φ uφ wφ : Lp ℝ 2 m}
    (hu : u ∈ F.domain) (hu2mem : u2 ∈ F.domain)
    (hwmem : w ∈ F.domain) (hw2mem : w2 ∈ F.domain) (hφmem : φ ∈ F.domain)
    (huφmem : uφ ∈ F.domain) (hwφmem : wφ ∈ F.domain) (hφ : 0 ≤ᵐ[m] φ)
    (hu2 : ⇑u2 =ᵐ[m] fun x => u x ^ 2)
    (hw : ⇑w =ᵐ[m] fun x => T (u x))
    (hw2 : ⇑w2 =ᵐ[m] fun x => w x ^ 2)
    (huφ : ⇑uφ =ᵐ[m] fun x => u x * φ x)
    (hwφ : ⇑wφ =ᵐ[m] fun x => w x * φ x) :
    F.form w wφ - (1 / 2 : ℝ) * F.form w2 φ ≤
      (L : ℝ) ^ 2 * (F.form u uφ - (1 / 2 : ℝ) * F.form u2 φ) := by
  choose G hG using fun n : ℕ => exists_resolvent F ((n : ℝ) + 1) (by positivity)
  have h1 := (tendsto_resolvent_form F hG hwmem hwφmem).sub
    ((tendsto_resolvent_form F hG hw2mem hφmem).const_mul (1 / 2))
  have h2 := ((tendsto_resolvent_form F hG hu huφmem).sub
    ((tendsto_resolvent_form F hG hu2mem hφmem).const_mul (1 / 2))).const_mul ((L : ℝ) ^ 2)
  apply le_of_tendsto_of_tendsto h1 h2
  filter_upwards [] with n
  simpa only [mul_assoc] using resolvent_lipschitz_functional_le F
    (by positivity : 0 < (n : ℝ) + 1) (hG n) hT hT0 hφ hu2 hw hw2 huφ hwφ

omit [T2Space X] [LocallyCompactSpace X] [BorelSpace X] in
/-- The defining identity can use products written with the canonical `Lp` functions. -/
theorem EnergyFamily.defining_of_ae_products [_instPreserved0 : T2Space X] [_instPreserved1 : LocallyCompactSpace X] [_instPreserved2 : BorelSpace X] {m : Measure X} {F : _root_.SubdiffusiveProcess.DirichletForm m} {U : Set X}
    (Γ : EnergyFamily F U) {u φ : Lp ℝ 2 m}
    (hu : F.toClosedForm.MemCoreOn U u) (hφ : F.toClosedForm.MemCoreOn U φ)
    {φc : X → ℝ} (hφc : Continuous φc) (hφae : ⇑φ =ᵐ[m] φc)
    {uφ u2 : Lp ℝ 2 m} (huφ : uφ ∈ F.domain) (hu2 : u2 ∈ F.domain)
    (hprod : ⇑uφ =ᵐ[m] fun x => u x * φ x)
    (hsq : ⇑u2 =ᵐ[m] fun x => u x ^ 2) :
    (∫ x, φc x ∂Γ.measure u) = F.form u uφ - (1 / 2 : ℝ) * F.form u2 φ := by
  obtain ⟨uc, huc, _, _, huae⟩ := hu.2
  apply Γ.defining u φ hu hφ uc φc huc hφc huae hφae uφ u2 huφ hu2
  · filter_upwards [hprod, huae, hφae] with x hp hu hφ
    rw [hp, hu, hφ]
  · filter_upwards [hsq, huae] with x hs hu
    rw [hs, hu]

/-- A zero-preserving Lipschitz map dominates energy measures on the continuous core. -/
theorem EnergyFamily.core_lipschitz_measure_le {F : _root_.SubdiffusiveProcess.DirichletForm m} {U : Set X}
    (h : Data F U) (Γ : EnergyFamily F U) {u w : Lp ℝ 2 m}
    (hu : F.toClosedForm.MemCoreOn U u) (hw : F.toClosedForm.MemCoreOn U w)
    {T : ℝ → ℝ} {L : ℝ≥0} (hT : LipschitzWith L T) (hT0 : T 0 = 0)
    (hwae : ⇑w =ᵐ[m] fun x => T (u x)) :
    Γ.measure w ≤ ENNReal.ofReal ((L : ℝ) ^ 2) • Γ.measure u := by
  apply Γ.measure_le_of_core_integral_le h hu.1 hw.1 (sq_nonneg _)
  intro φ hφ φc hφc _ _ hφae hφ01
  obtain ⟨Ru, huR⟩ := ae_abs_le_of_memCoreOn hu
  obtain ⟨Rw, hwR⟩ := ae_abs_le_of_memCoreOn hw
  let M := max (max Ru Rw) 1
  have huM : ∀ᵐ x ∂m, |u x| ≤ M := huR.mono fun x hx =>
    hx.trans ((le_max_left _ _).trans (le_max_left _ _))
  have hwM : ∀ᵐ x ∂m, |w x| ≤ M := hwR.mono fun x hx =>
    hx.trans ((le_max_right _ _).trans (le_max_left _ _))
  have hφM : ∀ᵐ x ∂m, |φ x| ≤ M := by
    filter_upwards [hφae] with x hx
    rw [hx, abs_of_nonneg (hφ01 x).1]
    exact (hφ01 x).2.trans (le_max_right _ _)
  have hφ0 : 0 ≤ᵐ[m] φ := hφae.mono fun x hx => hx.symm ▸ (hφ01 x).1
  obtain ⟨u2, hu2, hu2ae⟩ := F.exists_mul_mem hu.1 hu.1 huM huM
  obtain ⟨w2, hw2, hw2ae⟩ := F.exists_mul_mem hw.1 hw.1 hwM hwM
  obtain ⟨uφ, huφ, huφae⟩ := F.exists_mul_mem hu.1 hφ.1 huM hφM
  obtain ⟨wφ, hwφ, hwφae⟩ := F.exists_mul_mem hw.1 hφ.1 hwM hφM
  have hu2sq : ⇑u2 =ᵐ[m] fun x => u x ^ 2 := by
    simpa only [pow_two] using hu2ae
  have hw2sq : ⇑w2 =ᵐ[m] fun x => w x ^ 2 := by
    simpa only [pow_two] using hw2ae
  rw [Γ.defining_of_ae_products hw hφ hφc hφae hwφ hw2 hwφae hw2sq,
    Γ.defining_of_ae_products hu hφ hφc hφae huφ hu2 huφae hu2sq]
  exact core_lipschitz_functional_le F hT hT0 hu.1 hu2 hw.1 hw2 hφ.1 huφ hwφ
    hφ0 hu2sq hwae hw2sq huφae hwφae

end SubdiffusiveProcess.DirichletForm.FOTConstruction
