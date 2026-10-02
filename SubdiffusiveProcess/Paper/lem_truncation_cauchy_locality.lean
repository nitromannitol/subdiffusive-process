import SubdiffusiveProcess.Paper.prop_locality
import SubdiffusiveProcess.Paper.obl_FOT
import SubdiffusiveProcess.DirichletForm.All
import Mathlib
import SubdiffusiveProcess.Lane4.Carriers

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]

namespace DirichletForm

variable {m : Measure X} {E : ClosedForm m}

theorem aux_ennreal_eq_of_toReal_eq {a b : ℝ≥0∞}
    (ha : a ≠ ⊤) (hb : b ≠ ⊤) (h : a.toReal = b.toReal) : a = b := by
  calc
    a = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal ha).symm
    _ = ENNReal.ofReal b.toReal := congrArg ENNReal.ofReal h
    _ = b := ENNReal.ofReal_toReal hb

theorem aux_measure_mono_null (μ : Measure X) {A B : Set X}
    (hAB : A ⊆ B) (hB : μ B = 0) : μ A = 0 := by
  apply le_antisymm ?_ bot_le
  calc
    μ A ≤ μ B := measure_mono hAB
    _ = 0 := hB

theorem aux_measure_ne_top (Γ : EnergyMeasure E)
    (u : Lp ℝ 2 m) (hu : u ∈ E.domain) (B : Set X) : Γ.measure u B ≠ ⊤ := by
  have hle : Γ.measure u B ≤ Γ.measure u Set.univ :=
    measure_mono (Set.subset_univ B)
  exact (lt_of_le_of_lt hle (Γ.measure_univ_lt_top u hu)).ne

theorem aux_measure_eq_zero_of_toReal_eq_zero (Γ : EnergyMeasure E)
    (u : Lp ℝ 2 m) (hu : u ∈ E.domain) (B : Set X)
    (h : (Γ.measure u B).toReal = 0) : Γ.measure u B = 0 := by
  apply aux_ennreal_eq_of_toReal_eq (aux_measure_ne_top Γ u hu B) (by simp)
  simpa only [ENNReal.toReal_zero] using h

theorem aux_toReal_measure_le_energy (Γ : EnergyMeasure E)
    (u : Lp ℝ 2 m) (hu : u ∈ E.domain) (B : Set X) :
    (Γ.measure u B).toReal ≤ E.form u u := by
  calc
    (Γ.measure u B).toReal ≤ (Γ.measure u Set.univ).toReal :=
      ENNReal.toReal_mono (Γ.measure_univ_lt_top u hu).ne
        (measure_mono (Set.subset_univ B))
    _ = E.form u u := Γ.measure_univ u hu

theorem aux_cross_apply_eq_zero_of_measure_eq_zero (Γ : EnergyMeasure E)
    (u v : Lp ℝ 2 m) (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (B : Set X) (hB : MeasurableSet B) (hzero : Γ.measure u B = 0) :
    Γ.cross u v B = 0 := by
  have hbound := Γ.abs_cross_le u hu v hv B hB
  rw [hzero, ENNReal.toReal_zero, Real.sqrt_zero, zero_mul] at hbound
  exact abs_eq_zero.mp (le_antisymm hbound (abs_nonneg _))

theorem aux_measure_add_of_right_null (Γ : EnergyMeasure E)
    (u v : Lp ℝ 2 m) (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (B : Set X) (hB : MeasurableSet B) (hzero : Γ.measure v B = 0) :
    Γ.measure (u + v) B = Γ.measure u B := by
  have huv : u + v ∈ E.domain := E.domain.add_mem hu hv
  have huvzero : Γ.cross u v B = 0 := by
    rw [Γ.cross_symm u hu v hv]
    exact aux_cross_apply_eq_zero_of_measure_eq_zero Γ v u hv hu B hB hzero
  have hsumvzero : Γ.cross (u + v) v B = 0 := by
    rw [Γ.cross_symm (u + v) huv v hv]
    exact aux_cross_apply_eq_zero_of_measure_eq_zero Γ v (u + v) hv huv B hB hzero
  apply aux_ennreal_eq_of_toReal_eq
    (aux_measure_ne_top Γ (u + v) huv B) (aux_measure_ne_top Γ u hu B)
  rw [← Γ.cross_self (u + v) huv B hB,
    Γ.cross_add_right (u + v) huv u hu v hv,
    VectorMeasure.add_apply, hsumvzero, add_zero,
    Γ.cross_symm (u + v) huv u hu,
    Γ.cross_add_right u hu u hu v hv,
    VectorMeasure.add_apply, huvzero, add_zero,
    Γ.cross_self u hu B hB]

theorem aux_measure_compl_core_carrier [OpensMeasurableSpace X]
    (Γ : EnergyMeasure E) {U : Set X} (hU : IsOpen U)
    {C : Set (Lp ℝ 2 m)} (hcore : IsCoreOn E U C)
    (f : Lp ℝ 2 m) (hf : f ∈ E.domain) : Γ.measure f Uᶜ = 0 := by
  classical
  apply aux_measure_eq_zero_of_toReal_eq_zero Γ f hf Uᶜ
  apply le_antisymm ?_ ENNReal.toReal_nonneg
  by_contra hnot
  have hpos : 0 < (Γ.measure f Uᶜ).toReal := lt_of_not_ge hnot
  obtain ⟨g, hgC, hsmall⟩ :=
    hcore.denseEnergy f hf (Γ.measure f Uᶜ).toReal hpos
  rcases hcore.memCoreOn g hgC with ⟨hg, gc, hgc, hgcs, hgcU, hgrepr⟩
  have hsubset : Uᶜ ⊆ (tsupport gc)ᶜ := by
    intro x hx hxgc
    exact hx (hgcU hxgc)
  have hgzero : Γ.measure g Uᶜ = 0 :=
    aux_measure_mono_null (Γ.measure g) hsubset
      (Γ.measure_compl_tsupport g hg gc hgc hgrepr)
  have hdiff : f - g ∈ E.domain := E.domain.sub_mem hf hg
  have hmass : Γ.measure f Uᶜ = Γ.measure (f - g) Uᶜ := by
    have hadd := aux_measure_add_of_right_null Γ (f - g) g hdiff hg Uᶜ
      hU.measurableSet.compl hgzero
    simpa only [sub_add_cancel] using hadd
  have hle : (Γ.measure f Uᶜ).toReal ≤ E.form (f - g) (f - g) := by
    rw [hmass]
    exact aux_toReal_measure_le_energy Γ (f - g) hdiff Uᶜ
  change E.form (f - g) (f - g) + ‖f - g‖ ^ 2 <
    (Γ.measure f Uᶜ).toReal at hsmall
  have hnorm : 0 ≤ ‖f - g‖ ^ 2 := sq_nonneg _
  linarith

def aux_plateau (c t : ℝ) : ℝ := c * Real.smoothTransition (2 * t)

theorem aux_plateau_contDiff (c : ℝ) : ContDiff ℝ 1 (aux_plateau c) := by
  change ContDiff ℝ 1 (fun t : ℝ => c * Real.smoothTransition (2 * t))
  have hstep : ContDiff ℝ 1 Real.smoothTransition :=
    Real.smoothTransition.contDiff (n := (1 : ℕ∞))
  have hlinear : ContDiff ℝ 1 (fun t : ℝ => 2 * t) :=
    contDiff_const.mul contDiff_id
  exact contDiff_const.mul (hstep.comp hlinear)

theorem aux_plateau_zero (c : ℝ) : aux_plateau c 0 = 0 := by
  simp only [aux_plateau, mul_zero, Real.smoothTransition.zero]

theorem aux_plateau_eq (c : ℝ) {t : ℝ} (ht : (1 / 2 : ℝ) < t) :
    aux_plateau c t = c := by
  have htwo : 1 ≤ 2 * t := by linarith
  rw [aux_plateau, Real.smoothTransition.one_of_one_le htwo, mul_one]

theorem aux_plateau_deriv (c : ℝ) {t : ℝ} (ht : (1 / 2 : ℝ) < t) :
    deriv (aux_plateau c) t = 0 := by
  have heq : aux_plateau c =ᶠ[𝓝 t] (fun _ : ℝ => c) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact aux_plateau_eq c hs
  calc
    deriv (aux_plateau c) t = deriv (fun _ : ℝ => c) t := heq.deriv_eq
    _ = 0 := deriv_const t c

section LocalCompact

variable [T2Space X] [LocallyCompactSpace X] [RegularSpace X]

theorem aux_core_rep_large_on_compact
    {U : Set X} (hU : IsOpen U) {C : Set (Lp ℝ 2 m)}
    (hcore : IsCoreOn E U C) {K : Set X} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ g : Lp ℝ 2 m, E.MemCore g ∧
      ∃ gc : X → ℝ, Continuous gc ∧ (⇑g =ᵐ[m] gc) ∧
        ∀ x ∈ K, (1 / 2 : ℝ) < gc x := by
  classical
  obtain ⟨L, hLcompact, hLclosed, hKL, hLU⟩ :=
    exists_compact_closed_between hK hU hKU
  have hdisjoint : Disjoint K (interior L)ᶜ := by
    apply Set.disjoint_left.mpr
    intro x hxK hxL
    exact hxL (hKL hxK)
  obtain ⟨b, hbK, hbzero, hbcompact, hbrange⟩ :=
    exists_continuous_one_zero_of_isCompact hK
      (isOpen_interior : IsOpen (interior L)).isClosed_compl hdisjoint
  have hsupport : Function.support (⇑b) ⊆ L := by
    intro x hx
    change b x ≠ 0 at hx
    by_contra hxL
    have hxoutside : x ∈ (interior L)ᶜ := by
      intro hxinside
      exact hxL (interior_subset hxinside)
    exact hx (hbzero hxoutside)
  have htsupport : tsupport (⇑b) ⊆ U := by
    change closure (Function.support (⇑b)) ⊆ U
    exact (closure_minimal hsupport hLclosed).trans hLU
  obtain ⟨g, hgC, gc, hgc, hgccompact, hgcU, hgrepr, happrox⟩ :=
    hcore.denseUniform (⇑b) b.continuous hbcompact htsupport
      (1 / 4 : ℝ) (by norm_num)
  refine ⟨g, ?_, gc, hgc, hgrepr, ?_⟩
  · change g ∈ E.domain ∧ HasCoreRep m Set.univ g
    exact ⟨(hcore.memCoreOn g hgC).1, gc, hgc, hgccompact,
      Set.subset_univ _, hgrepr⟩
  · intro x hxK
    have hbval : b x = 1 := hbK hxK
    have hlow : -(1 / 4 : ℝ) < gc x - b x := (abs_lt.mp (happrox x)).1
    rw [hbval] at hlow
    linarith

variable [OpensMeasurableSpace X]

theorem aux_compact_local_const_null (Γ : EnergyMeasure E)
    (halg : IsCoreAlgebra E) {U : Set X} (hU : IsOpen U)
    {C : Set (Lp ℝ 2 m)} (hcore : IsCoreOn E U C)
    (f : Lp ℝ 2 m) (hf : f ∈ E.domain)
    (O : Set X) (hO : IsOpen O) (c : ℝ)
    (hconst : ⇑f =ᵐ[m.restrict O] (fun _ : X => c))
    (K : Set X) (hK : IsCompact K) (hKO : K ⊆ O ∩ U) :
    Γ.measure f K = 0 := by
  obtain ⟨g, hg, gc, hgc, hgrepr, hlarge⟩ :=
    aux_core_rep_large_on_compact hU hcore hK (fun x hx => (hKO hx).2)
  obtain ⟨q, hq, hqg⟩ :=
    halg.comp_mem g hg (aux_plateau c) (aux_plateau_contDiff c) (aux_plateau_zero c)
  have hqrepr : ⇑q =ᵐ[m] (fun x => aux_plateau c (gc x)) := by
    filter_upwards [hqg, hgrepr] with x hxq hxg
    exact hxq.trans (congrArg (aux_plateau c) hxg)
  let V : Set X := O ∩ {x : X | (1 / 2 : ℝ) < gc x}
  have hV : IsOpen V := hO.inter (isOpen_lt continuous_const hgc)
  have hKV : K ⊆ V := by
    intro x hx
    exact ⟨(hKO hx).1, hlarge x hx⟩
  have hconstV : ⇑f =ᵐ[m.restrict V] (fun _ : X => c) :=
    ae_restrict_of_ae_restrict_of_subset
      (show V ⊆ O from Set.inter_subset_left) hconst
  have hqreprV : ⇑q =ᵐ[m.restrict V] (fun x => aux_plateau c (gc x)) :=
    ae_restrict_of_ae hqrepr
  have hfq : ⇑f =ᵐ[m.restrict V] ⇑q := by
    filter_upwards [hconstV, hqreprV, ae_restrict_mem hV.measurableSet]
      with x hfx hqx hxV
    have hxgc : (1 / 2 : ℝ) < gc x := hxV.2
    calc
      f x = c := hfx
      _ = aux_plateau c (gc x) := (aux_plateau_eq c hxgc).symm
      _ = q x := hqx.symm
  have hqzero : Γ.measure q V = 0 := by
    apply aux_measure_eq_zero_of_toReal_eq_zero Γ q hq.1 V
    calc
      (Γ.measure q V).toReal =
          ∫ x in V, (deriv (aux_plateau c) (gc x)) ^ 2 ∂(Γ.measure g) :=
        Γ.chain_rule g hg.1 gc hgc hgrepr (aux_plateau c)
          (aux_plateau_contDiff c) (aux_plateau_zero c)
          q hq.1 hqrepr V hV.measurableSet
      _ = ∫ x in V, (0 : ℝ) ∂(Γ.measure g) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hV.measurableSet] with x hxV
        have hxgc : (1 / 2 : ℝ) < gc x := hxV.2
        rw [aux_plateau_deriv c hxgc]
        norm_num
      _ = 0 := by simp only [integral_zero]
  have hrestr : (Γ.measure f).restrict V = (Γ.measure q).restrict V :=
    Γ.locality f hf q hq.1 V hV hfq
  have hmass : Γ.measure f V = Γ.measure q V := by
    have h := congrArg (fun ν : Measure X => ν Set.univ) hrestr
    simpa only [Measure.restrict_apply_univ] using h
  exact aux_measure_mono_null (Γ.measure f) hKV (hmass.trans hqzero)

theorem aux_restrict_zero_on_constant_open (Γ : EnergyMeasure E)
    (halg : IsCoreAlgebra E) (f : Lp ℝ 2 m) (hf : f ∈ E.domain)
    (O : Set X) (hO : IsOpen O) (c : ℝ)
    (hconst : ⇑f =ᵐ[m.restrict O] (fun _ : X => c)) :
    (Γ.measure f).restrict O = 0 := by
  classical
  rcases halg.isRegular with ⟨U, hU, hcarrier, C, hcore⟩
  have hout : Γ.measure f Uᶜ = 0 :=
    aux_measure_compl_core_carrier Γ hU hcore f hf
  letI : (Γ.measure f).Regular := Γ.regular f hf
  have hinside : Γ.measure f (O ∩ U) = 0 := by
    by_contra hnot
    have hpos : (0 : ℝ≥0∞) < Γ.measure f (O ∩ U) :=
      bot_lt_iff_ne_bot.mpr hnot
    obtain ⟨K, hKO, hK, hKpos⟩ :=
      Measure.Regular.innerRegular (μ := Γ.measure f) (hO.inter hU) 0 hpos
    have hKzero :=
      aux_compact_local_const_null Γ halg hU hcore f hf O hO c hconst K hK hKO
    rw [hKzero] at hKpos
    exact (lt_irrefl (0 : ℝ≥0∞)) hKpos
  have hcover : O ⊆ (O ∩ U) ∪ Uᶜ := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact Or.inl ⟨hx, hxU⟩
    · exact Or.inr hxU
  apply Measure.restrict_eq_zero.mpr
  apply le_antisymm ?_ bot_le
  calc
    Γ.measure f O ≤ Γ.measure f ((O ∩ U) ∪ Uᶜ) := measure_mono hcover
    _ ≤ Γ.measure f (O ∩ U) + Γ.measure f Uᶜ := measure_union_le _ _
    _ = 0 := by rw [hinside, hout, zero_add]

theorem aux_restrict_congr_constant (Γ : EnergyMeasure E)
    (halg : IsCoreAlgebra E) (u w : Lp ℝ 2 m)
    (hu : u ∈ E.domain) (hw : w ∈ E.domain)
    (O : Set X) (hO : IsOpen O) (c : ℝ)
    (hconst : ⇑u =ᵐ[m.restrict O] (fun x => w x + c)) :
    (Γ.measure u).restrict O = (Γ.measure w).restrict O := by
  have hdiff : u - w ∈ E.domain := E.domain.sub_mem hu hw
  have hsub : ⇑(u - w) =ᵐ[m.restrict O] (fun x => u x - w x) :=
    ae_restrict_of_ae (Lp.coeFn_sub u w)
  have hdiffconst : ⇑(u - w) =ᵐ[m.restrict O] (fun _ : X => c) := by
    filter_upwards [hsub, hconst] with x hxsub hxconst
    rw [hxsub, hxconst]
    ring
  have hzero :=
    aux_restrict_zero_on_constant_open Γ halg (u - w) hdiff O hO c hdiffconst
  have hmass : Γ.measure (u - w) O = 0 := Measure.restrict_eq_zero.mp hzero
  apply Measure.ext
  intro B hB
  rw [Measure.restrict_apply hB, Measure.restrict_apply hB]
  have hnull : Γ.measure (u - w) (B ∩ O) = 0 :=
    aux_measure_mono_null (Γ.measure (u - w)) Set.inter_subset_right hmass
  have hadd := aux_measure_add_of_right_null Γ w (u - w) hw hdiff (B ∩ O)
    (hB.inter hO.measurableSet) hnull
  rw [add_comm w (u - w), sub_add_cancel] at hadd
  exact hadd

end LocalCompact

end DirichletForm


namespace Paper



theorem lem_truncation_cauchy_locality
    (d : ℕ) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (EQ : _root_.DirichletForm
      (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))))
    (hFOT : obl_FOT EQ)
    (Gamma : DirichletForm.EnergyMeasure EQ.toClosedForm)
    (halg : DirichletForm.IsCoreAlgebra EQ.toClosedForm)
    (hloc : DirichletForm.IsStronglyLocal EQ.toClosedForm)
    (u w : DomainL2 (centeredCube z R hR))
    (hu : u ∈ EQ.toClosedForm.domain)
    (hw : w ∈ EQ.toClosedForm.domain)
    (O : Set (SpatialCoordinates d)) (hO : IsOpen O)
    (c : ℝ)
    (hconst : (u : SpatialCoordinates d → ℝ)
      =ᵐ[((volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))).restrict O)]
        (fun x => (w : SpatialCoordinates d → ℝ) x + c)) :
    (Gamma.measure u).restrict O = (Gamma.measure w).restrict O := by
  exact DirichletForm.aux_restrict_congr_constant Gamma halg u w hu hw O hO c hconst

end Paper
