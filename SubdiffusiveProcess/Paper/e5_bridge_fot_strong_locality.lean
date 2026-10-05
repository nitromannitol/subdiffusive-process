module

public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Sobolev.ResponseSpace
public import SubdiffusiveProcess.Paper.e5_fot_strongly_local
public import SubdiffusiveProcess.Paper.obl_BH_quasi_continuous_representative
public import SubdiffusiveProcess.Paper.inputs_classical_fot_normal_contractions
public import SubdiffusiveProcess.Paper.inputs_classical_fot_energy_measure_qc

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The Lipschitz function `t ↦ |t - c| - |c|`; it vanishes at `0` and is even about `c` up to the constant. -/
def aux_e5_bridge_T (c t : ℝ) : ℝ := |t - c| - |c|

/-- Its a.e. derivative `sign (t - c)`. -/
def aux_e5_bridge_Td (c t : ℝ) : ℝ := if c < t then 1 else if t < c then -1 else 0

theorem aux_e5_bridge_T_zero (c : ℝ) : aux_e5_bridge_T c 0 = 0 := by
  unfold aux_e5_bridge_T
  simp

theorem aux_e5_bridge_T_lipschitz (c : ℝ) : LipschitzWith 1 (aux_e5_bridge_T c) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro s t
  rw [Real.dist_eq, Real.dist_eq]
  simp only [aux_e5_bridge_T]
  have h : (|s - c| - |c|) - (|t - c| - |c|) = |s - c| - |t - c| := by ring
  rw [h]
  have h2 : |(|s - c| - |t - c|)| ≤ |(s - c) - (t - c)| := abs_abs_sub_abs_le_abs_sub (s - c) (t - c)
  have h3 : (s - c) - (t - c) = s - t := by ring
  rw [h3] at h2
  have : (↑(1 : ℝ≥0) : ℝ) * |s - t| = |s - t| := by rw [NNReal.coe_one, one_mul]
  rw [this]
  exact h2

theorem aux_e5_bridge_T_normalContraction (c : ℝ) :
    _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction (aux_e5_bridge_T c) := by
  constructor
  · exact aux_e5_bridge_T_zero c
  · intro s t
    simp only [aux_e5_bridge_T]
    have h := abs_abs_sub_abs_le_abs_sub (s - c) (t - c)
    rw [sub_sub_sub_cancel_right] at h
    have heq : |s - c| - |c| - (|t - c| - |c|) = |s - c| - |t - c| := by ring
    rw [heq]
    exact h

theorem aux_e5_bridge_T_hasDerivAt (c s : ℝ) (hs : s ≠ c) :
    HasDerivAt (aux_e5_bridge_T c) (aux_e5_bridge_Td c s) s := by
  rcases lt_or_gt_of_ne hs with h | h
  · have ht' := h
    have hderiv : HasDerivAt (fun t : ℝ => (c - t) - |c|) (-1) s := by
      have h1 : HasDerivAt (fun x : ℝ => c - x) (-1) s := by
        simpa using! (hasDerivAt_id s).const_sub c
      simpa using! h1.sub_const (|c|)
    have heq : aux_e5_bridge_T c =ᶠ[𝓝 s] fun t => (c - t) - |c| := by
      filter_upwards [Iio_mem_nhds h] with t ht
      have ht' : t < c := ht
      unfold aux_e5_bridge_T
      rw [abs_of_neg (by linarith : t - c < 0)]
      ring
    have hTd : aux_e5_bridge_Td c s = -1 := by
      unfold aux_e5_bridge_Td
      rw [ite_eq_right (not_lt.2 h.le), ite_eq_left h]
    rw [hTd]
    exact hderiv.congr_of_eventuallyEq heq
  · have hderiv : HasDerivAt (fun t : ℝ => (t - c) - |c|) 1 s := by
      have h1 : HasDerivAt (fun x : ℝ => x - c) 1 s := by
        simpa using! (hasDerivAt_id s).sub_const c
      simpa using! h1.sub_const (|c|)
    have heq : aux_e5_bridge_T c =ᶠ[𝓝 s] fun t => (t - c) - |c| := by
      filter_upwards [Ioi_mem_nhds h] with t ht
      have ht' : c < t := ht
      unfold aux_e5_bridge_T
      rw [abs_of_pos (by linarith : 0 < t - c)]
    have hTd : aux_e5_bridge_Td c s = 1 := by
      unfold aux_e5_bridge_Td
      rw [ite_eq_left h]
    rw [hTd]
    exact hderiv.congr_of_eventuallyEq heq

theorem aux_e5_bridge_Td_measurable (c : ℝ) : Measurable (aux_e5_bridge_Td c) := by
  unfold aux_e5_bridge_Td
  apply Measurable.ite
  · exact measurableSet_lt measurable_const measurable_id
  · exact measurable_const
  · apply Measurable.ite
    · exact measurableSet_lt measurable_id measurable_const
    · exact measurable_const
    · exact measurable_const

theorem aux_e5_bridge_Td_sq (c s : ℝ) :
    (aux_e5_bridge_Td c s) ^ 2 = if s = c then 0 else 1 := by
  unfold aux_e5_bridge_Td
  rcases lt_trichotomy c s with h | h | h
  · simp [h, h.ne']
  · simp [h]
  · simp [h, h.ne, lt_asymm]

/-- Evenness: `T (c + s) = T (c - s)`. -/
theorem aux_e5_bridge_T_even (c s : ℝ) : aux_e5_bridge_T c (c + s) = aux_e5_bridge_T c (c - s) := by
  unfold aux_e5_bridge_T
  have h1 : c + s - c = s := by ring
  have h2 : c - s - c = -s := by ring
  rw [h1, h2, abs_neg]

/-- A normal contraction of an element of the domain is represented by an element of the domain. -/
theorem aux_e5_bridge_exists {X : Type*} [MeasurableSpace X] {m : Measure X}
    (E : _root_.SubdiffusiveProcess.DirichletForm m) (hnc : _root_.SubdiffusiveProcess.DirichletForm.HasNormalContractions E)
    {T : ℝ → ℝ} (hT : _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T) {h : Lp ℝ 2 m}
    (hh : h ∈ E.toClosedForm.domain) :
    ∃ w : Lp ℝ 2 m, w ∈ E.toClosedForm.domain ∧ (⇑w =ᵐ[m] fun x => T (h x)) := by
  let w := (hT.lipschitzWith).compLp hT.map_zero h
  have hcoe : ⇑w =ᵐ[m] fun x => T (h x) := by
    have h1 := LipschitzWith.coeFn_compLp hT.lipschitzWith hT.map_zero h
    simpa [w, Function.comp] using! h1
  refine ⟨w, ?_, hcoe⟩
  exact (hnc.operatesOn T hT h hh w hcoe).1

/-- `E(T_c ∘ h) = E(h)`: the chain rule with the level-set property. -/
theorem aux_e5_bridge_energy_eq {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Γ : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (hq : obl_BH_quasi_continuous_representative E Γ) (c : ℝ)
    {h w : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d)))}
    (hh : h ∈ E.toClosedForm.domain) (hw : w ∈ E.toClosedForm.domain)
    (hwh : ⇑w =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
      fun x => aux_e5_bridge_T c (h x)) :
    E.toClosedForm.form w w = E.toClosedForm.form h h := by
  classical
  obtain ⟨rep, hmeas, hae, hlevel, hchain⟩ := hq
  have hae_deriv : ∀ᵐ s : ℝ, HasDerivAt (aux_e5_bridge_T c) (aux_e5_bridge_Td c s) s := by
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) c] with s hs
    exact aux_e5_bridge_T_hasDerivAt c s hs
  have hwrep : ⇑w =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
      fun x => aux_e5_bridge_T c (rep h hh x) := by
    filter_upwards [hwh, hae h hh] with x hx hx'
    rw [hx, hx']
  have hchain' := hchain h hh (aux_e5_bridge_T c)
      ⟨1, aux_e5_bridge_T_lipschitz c⟩ (aux_e5_bridge_T_zero c)
      (aux_e5_bridge_Td c) (aux_e5_bridge_Td_measurable c) hae_deriv w hw hwrep
      (Set.univ : Set (SpatialCoordinates d)) MeasurableSet.univ
  have hlevel0 : Γ.measure h ((rep h hh) ⁻¹' ({c} : Set ℝ)) = 0 :=
    hlevel h hh {c} isCompact_singleton Real.volume_singleton
  have hae_ne : ∀ᵐ x ∂(Γ.measure h), rep h hh x ≠ c := by
    rw [measure_eq_zero_iff_ae_notMem] at hlevel0
    filter_upwards [hlevel0] with x hx
    simpa using! hx
  have hTd1 : ∀ᵐ x ∂(Γ.measure h), (aux_e5_bridge_Td c (rep h hh x)) ^ 2 = 1 := by
    filter_upwards [hae_ne] with x hx
    rw [aux_e5_bridge_Td_sq]
    simp [hx]
  have hint : ∫ x in (Set.univ : Set (SpatialCoordinates d)),
        (aux_e5_bridge_Td c (rep h hh x)) ^ 2 ∂(Γ.measure h)
      = (Γ.measure h univ).toReal := by
    rw [Measure.restrict_univ]
    have hint2 : ∫ x, (aux_e5_bridge_Td c (rep h hh x)) ^ 2 ∂(Γ.measure h)
        = ∫ x, (1:ℝ) ∂(Γ.measure h) := integral_congr_ae hTd1
    rw [hint2, integral_const]
    simp [Measure.real]
  have hmw := (_root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure.measure_univ Γ w hw).symm
  have hmh := (_root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure.measure_univ Γ h hh).symm
  rw [hmw, hmh, hchain', ← hint]

/-- `T_c (u + v) = T_c (u - v)` a.e. when `u = c` on `W` and `v = 0` off `W`. -/
theorem aux_e5_bridge_ae_eq {X : Type*} [MeasurableSpace X] {m : Measure X}
    {u v p q : Lp ℝ 2 m} {W : Set X} {c : ℝ}
    (hp : ⇑p =ᵐ[m] ⇑u + ⇑v) (hq : ⇑q =ᵐ[m] ⇑u - ⇑v)
    (hv : ∀ᵐ x ∂m, x ∉ W → v x = 0) (hu : ∀ᵐ x ∂m, x ∈ W → u x = c) :
    (fun x => aux_e5_bridge_T c (p x)) =ᵐ[m] fun x => aux_e5_bridge_T c (q x) := by
  filter_upwards [hp, hq, hv, hu] with x hpx hqx hvx hux
  by_cases hxW : x ∈ W
  · rw [hpx, hqx, Pi.add_apply, Pi.sub_apply, hux hxW]
    exact aux_e5_bridge_T_even c (v x)
  · rw [hpx, hqx, Pi.add_apply, Pi.sub_apply, hvx hxW]
    simp

/-- Domain form of locality: no compact supports, arbitrary `c`, no condition on `∂W`. -/
theorem aux_e5_bridge_domain {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hnc : _root_.SubdiffusiveProcess.DirichletForm.HasNormalContractions E)
    (Γ : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (hq : obl_BH_quasi_continuous_representative E Γ) :
    ∀ u ∈ E.toClosedForm.domain, ∀ v ∈ E.toClosedForm.domain, ∀ (c : ℝ) (W : Set (SpatialCoordinates d)),
      IsOpen W →
      (∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))), x ∉ W → v x = 0) →
      (∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))), x ∈ W → u x = c) →
      E.toClosedForm.form u v = 0 := by
  intro u hu v hv c W _hW hv0 huc
  have hp : u + v ∈ E.toClosedForm.domain := E.toClosedForm.domain.add_mem hu hv
  have hm : u - v ∈ E.toClosedForm.domain := E.toClosedForm.domain.sub_mem hu hv
  obtain ⟨wp, hwp, hwpe⟩ := aux_e5_bridge_exists E hnc (aux_e5_bridge_T_normalContraction c) hp
  obtain ⟨wm, hwm, hwme⟩ := aux_e5_bridge_exists E hnc (aux_e5_bridge_T_normalContraction c) hm
  have h1 := aux_e5_bridge_energy_eq E Γ hq c hp hwp hwpe
  have h2 := aux_e5_bridge_energy_eq E Γ hq c hm hwm hwme
  have hae : (fun x => aux_e5_bridge_T c ((u + v : Lp ℝ 2 _) x)) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
      fun x => aux_e5_bridge_T c ((u - v : Lp ℝ 2 _) x) :=
    aux_e5_bridge_ae_eq (Lp.coeFn_add u v) (Lp.coeFn_sub u v) hv0 huc
  have hwpm : wp = wm := by
    apply Lp.ext
    filter_upwards [hwpe, hwme, hae] with x h₁ h₂ h₃
    rw [h₁, h₂]; exact h₃
  subst hwpm
  have h12 : E.toClosedForm.form (u + v) (u + v) = E.toClosedForm.form (u - v) (u - v) := by
    rw [← h1, ← h2]
  have hs := E.toClosedForm.form_add_self hu hv
  have hd : E.toClosedForm.form (u - v) (u - v) =
      E.toClosedForm.form u u - 2 * E.toClosedForm.form u v + E.toClosedForm.form v v := by
    have := E.toClosedForm.form_add_smul_self (-1) hu hv
    rw [show u + (-1 : ℝ) • v = u - v by rw [neg_one_smul, sub_eq_add_neg]] at this
    rw [this]; ring
  rw [hs, hd] at h12
  linarith



theorem e5_bridge_fot_strong_locality (d : ℕ) (Ω : Opens (SpatialCoordinates d))
    (F : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Ω : Set (SpatialCoordinates d))))
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (hUfull : (volume.restrict (Ω : Set (SpatialCoordinates d))) Uᶜ = 0)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm U C)
    (hfot : e5_fot_strongly_local F.toClosedForm U) :
    _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal F.toClosedForm := by
  obtain ⟨Γ, hq⟩ := inputs_classical_fot_energy_measure_qc d Ω F U hU hUfull hcore hfot
  have hnc := inputs_classical_fot_normal_contractions _ F
  intro u hu v hv _ _ c W hW hvz huc
  exact aux_e5_bridge_domain F hnc Γ hq u hu v hv c W hW hvz huc

end SubdiffusiveProcess.Paper
