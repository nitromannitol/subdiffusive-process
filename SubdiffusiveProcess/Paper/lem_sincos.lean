module

public import SubdiffusiveProcess.Lane2.LimitForm
public import SubdiffusiveProcess.Lane2.BoundaryPackaging
public import SubdiffusiveProcess.Lane2.NativeBridge
public import SubdiffusiveProcess.Lane2.ResponseMarkov
public import SubdiffusiveProcess.Main.MeasureTrace
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.DirichletForm.FOTProduct
public import SubdiffusiveProcess.Paper.obl_FOT
public import SubdiffusiveProcess.Lane4.Carriers

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}



theorem aux_lem_sincos_conditional
    (E F : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GE GF : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hEform : ∀ w : DomainL2 Q, E.energy w = limitFormEnergy GE w)
    (hFform : ∀ w : DomainL2 Q, F.energy w = limitFormEnergy GF w)
    (GammaE : DirichletForm.EnergyMeasure E)
    (GammaF : DirichletForm.EnergyMeasure F)
    (hdom : E.domain = F.domain)
    (C : ℝ) (hC : 0 ≤ C)
    (q : Set (SpatialCoordinates d)) (hq : IsOpen q)
    (horder : ∀ w : DomainL2 Q, MemFormCore GE w →
      ∀ wc : SpatialCoordinates d → ℝ,
        (w : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] wc →
        Continuous wc → tsupport wc ⊆ q →
        limitFormEnergy GF w ≤ ((C : ℝ) : EReal) * limitFormEnergy GE w)
    (hcore_alg : ∀ w v : DomainL2 Q, MemFormCore GE w → MemFormCore GE v →
      ∀ Phi : ℝ → ℝ, ContDiff ℝ 1 Phi →
      (∃ L : ℝ, ∀ s : ℝ, |deriv Phi s| ≤ L) →
      ∃ p : DomainL2 Q, MemFormCore GE p ∧
        (p : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
          (fun x => (v : SpatialCoordinates d → ℝ) x *
            Phi ((w : SpatialCoordinates d → ℝ) x)))
    (hreg : ∀ φ : SpatialCoordinates d → ℝ, Continuous φ → HasCompactSupport φ →
      tsupport φ ⊆ q → ∀ ε : ℝ, 0 < ε →
      ∃ (w : DomainL2 Q) (wc : SpatialCoordinates d → ℝ),
        MemFormCore GE w ∧ Continuous wc ∧ tsupport wc ⊆ q ∧
        (w : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] wc ∧
        ∀ x : SpatialCoordinates d, |wc x - φ x| ≤ ε)
    (u : DomainL2 Q) (hu : MemFormCore GE u)
    (B : Set (SpatialCoordinates d)) (hB : MeasurableSet B) (hBq : B ⊆ q) :
    (GammaF.measure u B).toReal ≤ C * (GammaE.measure u B).toReal := by
  classical
  have hmem : ∀ w : DomainL2 Q, MemFormCore GE w → w ∈ E.domain := by
    intro w hw
    refine E.mem_domain_of_energy_lt_top ?_
    rw [hEform w]
    exact hw.1
  have hcore : ∀ w : DomainL2 Q, MemFormCore GE w → E.MemCore w := by
    intro w hw
    have hwE : w ∈ E.domain := hmem w hw
    obtain ⟨-, f, hfc, hfcs, -, hfae⟩ := hw
    exact ⟨hwE, f, hfc, hfcs, Set.subset_univ _, hfae⟩
  have hordR : ∀ w : DomainL2 Q, MemFormCore GE w →
      ∀ wc : SpatialCoordinates d → ℝ,
        (w : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] wc →
        Continuous wc → tsupport wc ⊆ q → F.form w w ≤ C * E.form w w := by
    intro w hw wc hwae hwc hwsupp
    have h := horder w hw wc hwae hwc hwsupp
    have hwE : w ∈ E.domain := hmem w hw
    have hwF : w ∈ F.domain := hdom ▸ hwE
    rw [← hFform w, ← hEform w, F.energy_of_mem hwF, E.energy_of_mem hwE,
      ← EReal.coe_mul] at h
    exact_mod_cast h
  obtain ⟨-, uc, hucont, -, -, huae⟩ := id hu
  have hCeq : ((C.toNNReal : ℝ≥0) : ℝ) = C := Real.coe_toNNReal C hC
  have huE : u ∈ E.domain := hmem u hu
  have key : GammaF.measure u B ≤ ((C.toNNReal : ℝ≥0) : ℝ≥0∞) * GammaE.measure u B := by
    refine GammaE.measure_le_of_form_le_core GammaF hdom hq (hcore u hu) hucont huae ?_ hBq
    intro φ hφ hφcs hφsupp ε hε
    obtain ⟨w, wc, hw, hwc, hwsupp, hwae, hclose⟩ := hreg φ hφ hφcs hφsupp ε hε
    refine ⟨w, wc, hcore w hw, hwc, hwae, hclose, ?_⟩
    intro Phi hPhi hPhid
    obtain ⟨p, hp, hprep⟩ := hcore_alg u w hu hw Phi hPhi hPhid
    have hpc : (p : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
          fun x => wc x * Phi (uc x) := by
      filter_upwards [hprep, hwae, huae] with x h1 h2 h3
      rw [h1, h2, h3]
    refine ⟨p, hmem p hp, ?_, hpc⟩
    rw [hCeq]
    refine hordR p hp (fun x => wc x * Phi (uc x)) hpc ?_ ?_
    · exact hwc.mul (hPhi.continuous.comp hucont)
    · exact tsupport_mul_subset_left.trans hwsupp
  have hfinE : GammaE.measure u B ≠ ⊤ := GammaE.measure_ne_top huE B
  calc (GammaF.measure u B).toReal
      ≤ (((C.toNNReal : ℝ≥0) : ℝ≥0∞) * GammaE.measure u B).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hfinE) key
    _ = C * (GammaE.measure u B).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.coe_toReal, hCeq]

section Ramps

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

/-- The ramp `t ↦ min (max t 0) a`, written through the unit contraction. -/
def aux_lem_sincos_ramp (a t : ℝ) : ℝ := a * DirichletForm.unitTruncation (a⁻¹ * t)

theorem aux_lem_sincos_ramp_continuous (a : ℝ) : Continuous (aux_lem_sincos_ramp a) := by
  unfold aux_lem_sincos_ramp
  exact continuous_const.mul
    (DirichletForm.lipschitzWith_unitTruncation.continuous.comp (continuous_const.mul continuous_id))

theorem aux_lem_sincos_ramp_of_nonpos {a t : ℝ} (ha : 0 < a) (ht : t ≤ 0) :
    aux_lem_sincos_ramp a t = 0 := by
  have h : a⁻¹ * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ha.le) ht
  simp [aux_lem_sincos_ramp, DirichletForm.unitTruncation, min_le_of_left_le h]

theorem aux_lem_sincos_ramp_of_le {a t : ℝ} (ha : 0 < a) (ht0 : 0 ≤ t) (hta : t ≤ a) :
    aux_lem_sincos_ramp a t = t := by
  have h0 : 0 ≤ a⁻¹ * t := mul_nonneg (inv_nonneg.mpr ha.le) ht0
  have h1 : a⁻¹ * t ≤ 1 := by
    rw [inv_mul_le_iff₀ ha]; linarith
  simp only [aux_lem_sincos_ramp, DirichletForm.unitTruncation, min_eq_left h1, max_eq_left h0]
  field_simp

theorem aux_lem_sincos_ramp_of_ge {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) :
    aux_lem_sincos_ramp a t = a := by
  have h1 : 1 ≤ a⁻¹ * t := by
    rw [le_inv_mul_iff₀ ha]; linarith
  simp [aux_lem_sincos_ramp, DirichletForm.unitTruncation, min_eq_right h1]

/-- The Markov property of a Dirichlet form (the unit contraction operates) lets every ramp
operate: `ramp a ∘ w = a · unitTruncation (a⁻¹ w)`. -/
theorem aux_lem_sincos_ramp_mem (E : _root_.DirichletForm m) {w : Lp ℝ 2 m}
    (hw : w ∈ E.domain) (a : ℝ) :
    ∃ z : Lp ℝ 2 m, z ∈ E.domain ∧ ⇑z =ᵐ[m] fun x => aux_lem_sincos_ramp a (w x) := by
  have hw' : a⁻¹ • w ∈ E.domain := E.domain.smul_mem _ hw
  set v : Lp ℝ 2 m := DirichletForm.lipschitzWith_unitTruncation.compLp
    DirichletForm.unitTruncation_zero (a⁻¹ • w) with hvdef
  have hv : ⇑v =ᵐ[m] fun x => DirichletForm.unitTruncation ((a⁻¹ • w : Lp ℝ 2 m) x) :=
    LipschitzWith.coeFn_compLp _ _ _
  obtain ⟨hvdom, -⟩ := E.markov _ hw' v hv
  refine ⟨a • v, E.domain.smul_mem a hvdom, ?_⟩
  filter_upwards [Lp.coeFn_smul a v, hv, Lp.coeFn_smul a⁻¹ w] with x h1 h2 h3
  rw [h1, Pi.smul_apply, h2, h3, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  rfl

/-- The two-sided soft threshold `t ↦ (ramp M t - ramp δ t) - (ramp M (-t) - ramp δ (-t))`. -/
def aux_lem_sincos_thr (δ M t : ℝ) : ℝ :=
  (aux_lem_sincos_ramp M t - aux_lem_sincos_ramp δ t) -
    (aux_lem_sincos_ramp M (-t) - aux_lem_sincos_ramp δ (-t))

theorem aux_lem_sincos_thr_continuous (δ M : ℝ) : Continuous (aux_lem_sincos_thr δ M) := by
  unfold aux_lem_sincos_thr
  have h1 := aux_lem_sincos_ramp_continuous M
  have h2 := aux_lem_sincos_ramp_continuous δ
  exact (h1.sub h2).sub ((h1.comp continuous_neg).sub (h2.comp continuous_neg))

theorem aux_lem_sincos_thr_of_abs_le {δ M t : ℝ} (hδ : 0 < δ) (hδM : δ ≤ M) (ht : |t| ≤ δ) :
    aux_lem_sincos_thr δ M t = 0 := by
  have hM : 0 < M := lt_of_lt_of_le hδ hδM
  obtain ⟨h1, h2⟩ := abs_le.mp ht
  rcases le_total 0 t with h0 | h0
  · simp only [aux_lem_sincos_thr, aux_lem_sincos_ramp_of_le hM h0 (by linarith),
      aux_lem_sincos_ramp_of_le hδ h0 h2, aux_lem_sincos_ramp_of_nonpos hM (by linarith : -t ≤ 0),
      aux_lem_sincos_ramp_of_nonpos hδ (by linarith : -t ≤ 0)]
    ring
  · simp only [aux_lem_sincos_thr, aux_lem_sincos_ramp_of_nonpos hM h0,
      aux_lem_sincos_ramp_of_nonpos hδ h0,
      aux_lem_sincos_ramp_of_le hM (by linarith : 0 ≤ -t) (by linarith),
      aux_lem_sincos_ramp_of_le hδ (by linarith : 0 ≤ -t) (by linarith)]
    ring

theorem aux_lem_sincos_abs_thr_sub_le {δ M t : ℝ} (hδ : 0 < δ) (hδM : δ ≤ M) (ht : |t| ≤ M) :
    |aux_lem_sincos_thr δ M t - t| ≤ δ := by
  have hM : 0 < M := lt_of_lt_of_le hδ hδM
  obtain ⟨h1, h2⟩ := abs_le.mp ht
  rcases le_or_gt |t| δ with hs | hs
  · rw [aux_lem_sincos_thr_of_abs_le hδ hδM hs, zero_sub, abs_neg]
    exact hs
  · rcases le_total 0 t with h0 | h0
    · have htδ : δ ≤ t := by rw [abs_of_nonneg h0] at hs; exact hs.le
      simp only [aux_lem_sincos_thr, aux_lem_sincos_ramp_of_le hM h0 h2,
        aux_lem_sincos_ramp_of_ge hδ htδ, aux_lem_sincos_ramp_of_nonpos hM (by linarith : -t ≤ 0),
        aux_lem_sincos_ramp_of_nonpos hδ (by linarith : -t ≤ 0)]
      rw [abs_le]; constructor <;> linarith
    · have htδ : δ ≤ -t := by rw [abs_of_nonpos h0] at hs; exact hs.le
      simp only [aux_lem_sincos_thr, aux_lem_sincos_ramp_of_nonpos hM h0,
        aux_lem_sincos_ramp_of_nonpos hδ h0,
        aux_lem_sincos_ramp_of_le hM (by linarith : 0 ≤ -t) (by linarith),
        aux_lem_sincos_ramp_of_ge hδ htδ]
      rw [abs_le]; constructor <;> linarith

/-- The soft threshold operates on a Dirichlet form: four ramps, by the Markov property. -/
theorem aux_lem_sincos_thr_mem (E : _root_.DirichletForm m) {w : Lp ℝ 2 m}
    (hw : w ∈ E.domain) (δ M : ℝ) :
    ∃ z : Lp ℝ 2 m, z ∈ E.domain ∧ ⇑z =ᵐ[m] fun x => aux_lem_sincos_thr δ M (w x) := by
  have hnw : -w ∈ E.domain := E.domain.neg_mem hw
  obtain ⟨z1, hz1, hr1⟩ := aux_lem_sincos_ramp_mem E hw M
  obtain ⟨z2, hz2, hr2⟩ := aux_lem_sincos_ramp_mem E hw δ
  obtain ⟨z3, hz3, hr3⟩ := aux_lem_sincos_ramp_mem E hnw M
  obtain ⟨z4, hz4, hr4⟩ := aux_lem_sincos_ramp_mem E hnw δ
  refine ⟨(z1 - z2) - (z3 - z4),
    E.domain.sub_mem (E.domain.sub_mem hz1 hz2) (E.domain.sub_mem hz3 hz4), ?_⟩
  filter_upwards [Lp.coeFn_sub (z1 - z2) (z3 - z4), Lp.coeFn_sub z1 z2, Lp.coeFn_sub z3 z4,
    hr1, hr2, hr3, hr4, Lp.coeFn_neg w] with x e0 e1 e2 e3 e4 e5 e6 e7
  rw [e0, Pi.sub_apply, e1, e2, Pi.sub_apply, Pi.sub_apply, e3, e4, e5, e6, e7, Pi.neg_apply]
  rfl

end Ramps

section Approx

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}

/-- **Regularity plus the Markov property give core functions supported in `q`.**  The
uniform density of the core in `C_c(U)` produces a core approximant `g` of `φ` whose support
may leave `q`; the soft threshold at level `δ` kills it wherever `φ` vanishes, so the result is
supported inside `supp φ ⊆ q` and still within `2δ` of `φ`.  This replaces the plateau `ϑ` of
the paper's proof (lines 2214-2216) and uses no input beyond the two paper hypotheses. -/
theorem aux_lem_sincos_approx (E : _root_.DirichletForm m) {U : Set X}
    (hreg : ∃ Cc : Set (Lp ℝ 2 m), DirichletForm.IsCoreOn E.toClosedForm U Cc)
    {q : Set X} (hqU : q ⊆ U) {φ : X → ℝ} (hφ : Continuous φ) (hcs : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ q) {ε : ℝ} (hε : 0 < ε) :
    ∃ (v : Lp ℝ 2 m) (vc : X → ℝ), E.toClosedForm.MemCoreOn q v ∧ Continuous vc ∧
      (⇑v =ᵐ[m] vc) ∧ ∀ x : X, |vc x - φ x| ≤ ε := by
  obtain ⟨Cc, hCc⟩ := hreg
  obtain ⟨Mφ, hMφ⟩ := DirichletForm.exists_bound_of_hasCompactSupport hcs hφ
  set δ : ℝ := min (ε / 2) (1 / 2) with hδdef
  have hδ0 : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδε : δ ≤ ε / 2 := min_le_left _ _
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  set M : ℝ := max Mφ 0 + 1 with hMdef
  have hδM : δ ≤ M := by
    have := le_max_right Mφ 0; rw [hMdef]; linarith
  obtain ⟨w, hwC, g, hg, -, -, hwg, hclose⟩ :=
    hCc.denseUniform φ hφ hcs (hsupp.trans hqU) δ hδ0
  have hw : w ∈ E.domain := (hCc.memCoreOn w hwC).1
  obtain ⟨z, hz, hzr⟩ := aux_lem_sincos_thr_mem E hw δ M
  set vc : X → ℝ := fun x => aux_lem_sincos_thr δ M (g x) with hvcdef
  have hvc : Continuous vc := (aux_lem_sincos_thr_continuous δ M).comp hg
  have hzae : ⇑z =ᵐ[m] vc := by
    filter_upwards [hzr, hwg] with x h1 h2
    rw [h1, h2]
  -- the support of `vc` lies in `{δ ≤ |g|}`, which lies in `support φ`
  have hsupp_vc : Function.support vc ⊆ {x | δ ≤ |g x|} := by
    intro x hx
    by_contra hlt
    simp only [Set.mem_setOf_eq, not_le] at hlt
    exact hx (aux_lem_sincos_thr_of_abs_le hδ0 hδM hlt.le)
  have hlevel : {x | δ ≤ |g x|} ⊆ Function.support φ := by
    intro x hx hφx
    simp only [Set.mem_setOf_eq] at hx
    have := hclose x
    rw [hφx, sub_zero] at this
    linarith
  have hclosed : IsClosed {x | δ ≤ |g x|} :=
    isClosed_le continuous_const (continuous_abs.comp hg)
  have htsupp : tsupport vc ⊆ Function.support φ :=
    (closure_minimal hsupp_vc hclosed).trans hlevel
  have hcsvc : HasCompactSupport vc :=
    hcs.mono' ((subset_tsupport vc).trans (htsupp.trans (subset_tsupport φ)))
  refine ⟨z, vc, ⟨hz, vc, hvc, hcsvc, ?_, hzae⟩, hvc, hzae, fun x => ?_⟩
  · exact htsupp.trans ((subset_tsupport φ).trans hsupp)
  · have hgx := abs_le.mp (hclose x).le
    have hφx := hMφ x
    have hgM : |g x| ≤ M := by
      have := le_max_left Mφ 0
      rw [abs_le]; constructor <;>
        · have := abs_le.mp hφx; rw [hMdef]; linarith [this.1, this.2]
    have h1 := aux_lem_sincos_abs_thr_sub_le hδ0 hδM hgM
    calc |vc x - φ x| = |(aux_lem_sincos_thr δ M (g x) - g x) + (g x - φ x)| := by
          rw [hvcdef]; ring_nf
      _ ≤ |aux_lem_sincos_thr δ M (g x) - g x| + |g x - φ x| := abs_add_le _ _
      _ ≤ δ + δ := add_le_add h1 (hclose x).le
      _ ≤ ε := by linarith

end Approx

/-- `E.MemCoreOn` only reads the domain, so it transfers along `D(E) = D(F)`. -/
theorem aux_lem_sincos_memCoreOn_of_domain_eq
    {E F : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d)))}
    (hdom : E.domain = F.domain) {U : Set (SpatialCoordinates d)} {w : DomainL2 Q}
    (hw : E.MemCoreOn U w) : F.MemCoreOn U w :=
  ⟨hdom ▸ hw.1, hw.2⟩

/-- The source argument (steps 6-7 of `mfd:lem-sincos`) for `C ≥ 0`, taking the product clause of Fukushima-Oshima-Takeda Theorem 1.4.2 as a local
parameter. The principal lemma supplies that clause via proved `DirichletForm.mul_comp_mem`.
Regularity of `E` and its Markov property give the core approximants. -/
theorem aux_lem_sincos_of_mul_comp
    (E F : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hEreg : ∃ Cc : Set (DomainL2 Q),
      DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) Cc)
    (hdom : E.domain = F.domain)
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (q : Set (SpatialCoordinates d)) (hq : IsOpen q) (hqQ : q ⊆ Q)
    (hmul : ∀ u v : DomainL2 Q, E.toClosedForm.MemCore u → E.toClosedForm.MemCoreOn q v →
      ∀ uc vc : SpatialCoordinates d → ℝ, Continuous uc → Continuous vc →
      ((u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] uc) →
      ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] vc) →
      ∀ Φ : ℝ → ℝ, ContDiff ℝ 1 Φ → (∃ M : ℝ, ∀ t : ℝ, |Φ t| ≤ M) →
      ∃ w : DomainL2 Q, E.toClosedForm.MemCoreOn q w ∧
        (w : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] fun x => vc x * Φ (uc x))
    (C : ℝ≥0)
    (horder : ∀ w : DomainL2 Q, E.toClosedForm.MemCoreOn q w →
      F.form w w ≤ (C : ℝ) * E.form w w)
    (u : DomainL2 Q) (hu : E.toClosedForm.MemCore u)
    (B : Set (SpatialCoordinates d)) (hBq : B ⊆ q) :
    GammaF.measure u B ≤ (C : ℝ≥0∞) * GammaE.measure u B := by
  obtain ⟨-, uc, huc, hucs, -, huae⟩ := id hu
  obtain ⟨R, hR⟩ := DirichletForm.exists_bound_of_hasCompactSupport hucs huc
  refine GammaE.measure_le_of_form_le_core GammaF hdom hq hu huc huae ?_ hBq
  intro φ hφ hφcs hφsupp ε hε
  obtain ⟨v, vc, hvq, hvc, hvae, hclose⟩ :=
    aux_lem_sincos_approx E hEreg hqQ hφ hφcs hφsupp hε
  refine ⟨v, vc, hvq.memCore, hvc, hvae, hclose, ?_⟩
  intro Φ hΦ _
  -- `Φ` need not be bounded; cut it off outside the (bounded) range of `uc`
  let b : ContDiffBump (0 : ℝ) := ⟨max R 0 + 1, max R 0 + 2, by positivity, by linarith⟩
  have hΨ : ContDiff ℝ 1 (Φ * ⇑b) := hΦ.mul b.contDiff
  have hΨb : ∃ M : ℝ, ∀ t : ℝ, |(Φ * ⇑b) t| ≤ M :=
    DirichletForm.exists_bound_of_hasCompactSupport b.hasCompactSupport.mul_left hΨ.continuous
  obtain ⟨p, hpq, hprep⟩ := hmul u v hu hvq uc vc huc hvc huae hvae (Φ * ⇑b) hΨ hΨb
  have hpΦ : (p : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] fun x => vc x * Φ (uc x) := by
    filter_upwards [hprep] with x hx
    have hmem : uc x ∈ Metric.closedBall (0 : ℝ) b.rIn := by
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
      have := le_max_left R 0
      show |uc x| ≤ max R 0 + 1
      linarith [hR x]
    rw [hx, Pi.mul_apply, b.one_of_mem_closedBall hmem, mul_one]
  exact ⟨p, hpq.mem_domain, horder p hpq, hpΦ⟩

/-- lemma `mfd:lem-sincos` (paper lines 2194-2221): form order implies measure order.

`E, F` are regular (core on `Q`) strongly local Dirichlet forms with `D(E) = D(F)`, `q ⊆ Q`
is open and `F(w) ≤ C E(w)` for every core `w` supported in `q`; then
`Γ_F(u)(B) ≤ C Γ_E(u)(B)` for every core `u` and every `B ⊆ q`, for any energy measures
`Γ_E, Γ_F` (supplied from these hypotheses by `obl_FOT`).  No sign condition on `C` is
assumed: for `C < 0` both measures vanish on `q`.

The product clause cited from Fukushima-Oshima-Takeda Theorem 1.4.2 is supplied by the
proved `DirichletForm.mul_comp_mem`; `GammaE` and `GammaF` are supplied by `obl_FOT`.
The core approximants supported in `q` (lines 2214-2216) follow from regularity and
the Markov property (`aux_lem_sincos_approx`). -/
theorem lem_sincos
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
    (C : ℝ) (q : Set (SpatialCoordinates d)) (hq : IsOpen q) (hqQ : q ⊆ Q)
    (horder : ∀ w : DomainL2 Q, E.toClosedForm.MemCoreOn q w → F.form w w ≤ C * E.form w w)
    (u : DomainL2 Q) (hu : E.toClosedForm.MemCore u)
    (B : Set (SpatialCoordinates d)) (hBq : B ⊆ q) :
    (GammaF.measure u B).toReal ≤ C * (GammaE.measure u B).toReal := by
  have huE : u ∈ E.domain := hu.mem_domain
  have huF : u ∈ F.domain := hdom ▸ huE
  have hmulE := DirichletForm.mul_comp_mem E q
  rcases le_or_gt 0 C with hC | hC
  · have hCeq : ((C.toNNReal : ℝ≥0) : ℝ) = C := Real.coe_toNNReal C hC
    have key := aux_lem_sincos_of_mul_comp E F hEreg hdom GammaE GammaF q hq hqQ hmulE
      C.toNNReal (by rw [hCeq]; exact horder) u hu B hBq
    calc (GammaF.measure u B).toReal
        ≤ (((C.toNNReal : ℝ≥0) : ℝ≥0∞) * GammaE.measure u B).toReal :=
          ENNReal.toReal_mono
            (ENNReal.mul_ne_top ENNReal.coe_ne_top (GammaE.measure_ne_top huE B)) key
      _ = C * (GammaE.measure u B).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.coe_toReal, hCeq]
  · -- `C < 0`: the form bound forces `E = F = 0` on the admissible functions, and the
    -- argument with constant `0`, run in both directions, gives `Γ_F(u) = Γ_E(u) = 0` on `q`
    have hzero : ∀ w : DomainL2 Q, E.toClosedForm.MemCoreOn q w →
        E.form w w = 0 ∧ F.form w w = 0 := by
      intro w hw
      have hE0 := E.form_nonneg w hw.mem_domain
      have hF0 := F.form_nonneg w (hdom ▸ hw.mem_domain)
      have h := horder w hw
      have hE : E.form w w = 0 := by nlinarith
      exact ⟨hE, by rw [hE, mul_zero] at h; linarith⟩
    have hFB := aux_lem_sincos_of_mul_comp E F hEreg hdom GammaE GammaF q hq hqQ hmulE 0
      (fun w hw => by rw [(hzero w hw).2]; simp) u hu B hBq
    have hmulF : ∀ u v : DomainL2 Q, F.toClosedForm.MemCore u → F.toClosedForm.MemCoreOn q v →
        ∀ uc vc : SpatialCoordinates d → ℝ, Continuous uc → Continuous vc →
        ((u : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] uc) →
        ((v : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] vc) →
        ∀ Φ : ℝ → ℝ, ContDiff ℝ 1 Φ → (∃ M : ℝ, ∀ t : ℝ, |Φ t| ≤ M) →
        ∃ w : DomainL2 Q, F.toClosedForm.MemCoreOn q w ∧
          (w : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] fun x => vc x * Φ (uc x) := by
      intro u' v hu' hv uc vc huc hvc huae hvae Φ hΦ hΦb
      obtain ⟨w, hw, hwrep⟩ := hmulE u' v
        (aux_lem_sincos_memCoreOn_of_domain_eq hdom.symm hu')
        (aux_lem_sincos_memCoreOn_of_domain_eq hdom.symm hv) uc vc huc hvc huae hvae Φ hΦ hΦb
      exact ⟨w, aux_lem_sincos_memCoreOn_of_domain_eq hdom hw, hwrep⟩
    have hEB := aux_lem_sincos_of_mul_comp F E hFreg hdom.symm GammaF GammaE q hq hqQ hmulF 0
      (fun w hw => by
        rw [(hzero w (aux_lem_sincos_memCoreOn_of_domain_eq hdom.symm hw)).1]; simp)
      u (aux_lem_sincos_memCoreOn_of_domain_eq hdom hu) B hBq
    simp only [ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero] at hFB hEB
    rw [hFB, hEB]
    simp

end Paper
