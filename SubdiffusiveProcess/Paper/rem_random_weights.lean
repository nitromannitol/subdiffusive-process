import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.DirichletForm.All
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.ContinuousMap.Compact
import SubdiffusiveProcess.Sobolev.ResponseComparison
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.TietzeExtension
import SubdiffusiveProcess.Paper.prop_21
import SubdiffusiveProcess.Paper.rem_random_weights_catalog_transfer
import SubdiffusiveProcess.Paper.prop_killed_inverse
import SubdiffusiveProcess.Paper.conv_energy_measure_normalization
import SubdiffusiveProcess.Paper.prop_response_compact
import SubdiffusiveProcess.Paper.conv_represented_sequence

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology

namespace Paper
theorem aux_rem_random_weights_pot_bound {d : ℕ}
    (Q : Opens (SpatialCoordinates d))
    [CompactSpace ↥(closure (Q : Set (SpatialCoordinates d)))]
    (potEval : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ) → SpatialCoordinates d → ℝ)
    (hpotEval : ∀ (v : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ))
      (x : SpatialCoordinates d) (hx : x ∈ closure (Q : Set (SpatialCoordinates d))),
      potEval v x = v ⟨x, hx⟩)
    (v : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ))
    (x : SpatialCoordinates d) (hx : x ∈ closure (Q : Set (SpatialCoordinates d))) :
    |potEval v x| ≤ ‖v‖ := by
  rw [hpotEval v x hx]
  simpa [Real.norm_eq_abs] using v.norm_coe_le_norm (⟨x, hx⟩ : ↥(closure (Q : Set (SpatialCoordinates d))))

theorem aux_rem_random_weights_pot_diff_bound {d : ℕ}
    (Q : Opens (SpatialCoordinates d))
    [CompactSpace ↥(closure (Q : Set (SpatialCoordinates d)))]
    (potEval : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ) → SpatialCoordinates d → ℝ)
    (hpotEval : ∀ (v : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ))
      (x : SpatialCoordinates d) (hx : x ∈ closure (Q : Set (SpatialCoordinates d))),
      potEval v x = v ⟨x, hx⟩)
    (v w : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ))
    (x : SpatialCoordinates d) (hx : x ∈ closure (Q : Set (SpatialCoordinates d))) :
    |potEval v x - potEval w x| ≤ ‖v - w‖ := by
  rw [hpotEval v x hx, hpotEval w x hx]
  have := (v - w).norm_coe_le_norm (⟨x, hx⟩ : ↥(closure (Q : Set (SpatialCoordinates d))))
  simpa [Real.norm_eq_abs] using this

theorem aux_rem_random_weights_exp_integrableOn {d : ℕ}
    (Q : Opens (SpatialCoordinates d))
    [CompactSpace ↥(closure (Q : Set (SpatialCoordinates d)))]
    (potEval : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ) → SpatialCoordinates d → ℝ)
    (hpotEval : ∀ (v : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ))
      (x : SpatialCoordinates d) (hx : x ∈ closure (Q : Set (SpatialCoordinates d))),
      potEval v x = v ⟨x, hx⟩)
    (v : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ))
    (mu : Measure (SpatialCoordinates d)) (hmu : mu Set.univ ≠ ⊤) :
    IntegrableOn (fun x => Real.exp (potEval v x)) (Q : Set (SpatialCoordinates d)) mu := by
  obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq (Y := ℝ)
    (isClosed_closure (s := (Q : Set (SpatialCoordinates d)))) v
  have hgeq : ∀ x ∈ closure (Q : Set (SpatialCoordinates d)), g x = potEval v x := by
    intro x hx
    have := congrArg (fun (h : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ)) => h ⟨x, hx⟩) hg
    simp only [ContinuousMap.restrict_apply] at this
    rw [hpotEval v x hx]
    exact this
  haveI : IsFiniteMeasure (mu.restrict (Q : Set (SpatialCoordinates d))) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (measure_mono (subset_univ _)) hmu.lt_top
  have hQae : ∀ᵐ x ∂(mu.restrict (Q : Set (SpatialCoordinates d))),
      x ∈ (Q : Set (SpatialCoordinates d)) := ae_restrict_mem Q.isOpen.measurableSet
  refine ⟨?_, ?_⟩
  · refine (Measurable.aestronglyMeasurable (by fun_prop : Measurable fun x => Real.exp (g x))).congr ?_
    filter_upwards [hQae] with x hx
    rw [hgeq x (subset_closure hx)]
  · refine HasFiniteIntegral.of_bounded (C := Real.exp ‖v‖) ?_
    filter_upwards [hQae] with x hx
    have hb := aux_rem_random_weights_pot_bound Q potEval hpotEval v x (subset_closure hx)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((abs_le.mp hb).2)


theorem aux_rem_random_weights_energy_smul {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E)
    (c : ℝ) (u : DomainL2 Q) (hu : u ∈ E.domain) :
    Gamma.measure (c • u) = ENNReal.ofReal (c ^ 2) • Gamma.measure u := by
  have hcu : c • u ∈ E.domain := E.domain.smul_mem c hu
  refine Measure.ext fun B hB => ?_
  have h1 : Gamma.cross (c • u) (c • u) B = (c * c) * Gamma.cross u u B := by
    have e1 : Gamma.cross (c • u) (c • u) = c • Gamma.cross (c • u) u :=
      Gamma.cross_smul_right c (c • u) hcu u hu
    have e2 : Gamma.cross (c • u) u = Gamma.cross u (c • u) :=
      Gamma.cross_symm (c • u) hcu u hu
    have e3 : Gamma.cross u (c • u) = c • Gamma.cross u u :=
      Gamma.cross_smul_right c u hu u hu
    rw [e1, e2, e3]
    simp [mul_assoc]
  rw [Gamma.cross_self (c • u) hcu B hB, Gamma.cross_self u hu B hB] at h1
  have hfin : Gamma.measure u B ≠ ⊤ := Gamma.measure_ne_top hu B
  have hfin' : Gamma.measure (c • u) B ≠ ⊤ := Gamma.measure_ne_top hcu B
  rw [Measure.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_toReal hfin', ← ENNReal.ofReal_toReal hfin, h1,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- Half of the two-sided multiplicative comparison of the limiting weighted responses. -/
theorem aux_rem_random_weights_R_half {d : ℕ}
    (Q : Opens (SpatialCoordinates d))
    [CompactSpace ↥(closure (Q : Set (SpatialCoordinates d)))]
    (potEval : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ) → SpatialCoordinates d → ℝ)
    (hpotEval : ∀ (v : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ))
      (x : SpatialCoordinates d) (hx : x ∈ closure (Q : Set (SpatialCoordinates d))),
      potEval v x = v ⟨x, hx⟩)
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E)
    (R : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ) → DomainL2 Q → ℝ)
    (hR : ∀ v f, IsLUB {t : ℝ | ∃ u : DomainL2 Q, u ∈ E.domain ∧
      t = 2 * inner ℝ f u - ∫ x in (Q : Set (SpatialCoordinates d)),
        Real.exp (potEval v x) ∂(Gamma.measure u)} (R v f))
    (v w : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ)) (f : DomainL2 Q) :
    R v f ≤ Real.exp ‖v - w‖ * R w f := by
  classical
  set D : ℝ := ‖v - w‖ with hD
  set s : ℝ := Real.exp (-D) with hs
  have hspos : 0 < s := Real.exp_pos _
  have hsinv : s⁻¹ = Real.exp D := by rw [hs, ← Real.exp_neg, neg_neg]
  refine (hR v f).2 ?_
  rintro t ⟨u, hu, rfl⟩
  have hsu : s • u ∈ E.domain := E.domain.smul_mem s hu
  set Iv : ℝ := ∫ x in (Q : Set (SpatialCoordinates d)),
    Real.exp (potEval v x) ∂(Gamma.measure u) with hIv
  set Iw : ℝ := ∫ x in (Q : Set (SpatialCoordinates d)),
    Real.exp (potEval w x) ∂(Gamma.measure u) with hIw
  have hmem : 2 * inner ℝ f (s • u) - ∫ x in (Q : Set (SpatialCoordinates d)),
      Real.exp (potEval w x) ∂(Gamma.measure (s • u)) ≤ R w f :=
    (hR w f).1 ⟨s • u, hsu, rfl⟩
  have hinner : (inner ℝ f (s • u) : ℝ) = s * inner ℝ f u := real_inner_smul_right f u s
  have hscale : (∫ x in (Q : Set (SpatialCoordinates d)),
        Real.exp (potEval w x) ∂(Gamma.measure (s • u))) = s ^ 2 * Iw := by
    rw [hIw, aux_rem_random_weights_energy_smul Q E Gamma s u hu, Measure.restrict_smul, integral_smul_measure,
      ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  have hcompare : Iw ≤ s⁻¹ * Iv := by
    rw [hsinv, hIw, hIv, ← integral_const_mul]
    refine integral_mono_of_nonneg ?_ ?_ ?_
    · filter_upwards with x using (Real.exp_pos _).le
    · exact ((aux_rem_random_weights_exp_integrableOn Q potEval hpotEval v (Gamma.measure u)
        (Gamma.measure_ne_top hu _)).const_mul (Real.exp D))
    · filter_upwards [ae_restrict_mem Q.isOpen.measurableSet] with x hx
      have hb := aux_rem_random_weights_pot_diff_bound Q potEval hpotEval w v x (subset_closure hx)
      have hDw : ‖w - v‖ = D := by rw [hD, ← norm_neg]; congr 1; abel
      have hle : potEval w x ≤ D + potEval v x := by
        have h := (abs_le.mp hb).2
        rw [hDw] at h
        linarith
      calc Real.exp (potEval w x) ≤ Real.exp (D + potEval v x) := Real.exp_le_exp.mpr hle
        _ = Real.exp D * Real.exp (potEval v x) := Real.exp_add _ _
  have hfinal : s * (2 * inner ℝ f u - Iv) ≤ R w f := by
    refine le_trans ?_ hmem
    rw [hinner, hscale]
    have h2 := mul_le_mul_of_nonneg_left hcompare (by positivity : (0:ℝ) ≤ s ^ 2)
    have h3 : s ^ 2 * (s⁻¹ * Iv) = s * Iv := by
      field_simp
    rw [h3] at h2
    linarith
  have hdiv : 2 * inner ℝ f u - Iv ≤ R w f / s := by
    rw [le_div_iff₀ hspos]
    linarith [hfinal]
  calc 2 * inner ℝ f u - Iv ≤ R w f / s := hdiv
    _ = Real.exp D * R w f := by rw [div_eq_inv_mul, hsinv]


theorem aux_rem_random_weights_energy_zero {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E) :
    Gamma.measure (0 : DomainL2 Q) = 0 := by
  have hcs := Gamma.cross_smul_right (0 : ℝ) (0 : DomainL2 Q) E.domain.zero_mem
    (0 : DomainL2 Q) E.domain.zero_mem
  refine Measure.ext fun B hB => ?_
  have h1 : Gamma.cross (0 : DomainL2 Q) (0 : DomainL2 Q) B = 0 := by
    have : ((0 : ℝ) • (0 : DomainL2 Q)) = (0 : DomainL2 Q) := smul_zero _
    rw [this] at hcs
    rw [hcs]
    simp
  rw [Gamma.cross_self (0 : DomainL2 Q) E.domain.zero_mem B hB] at h1
  have hfin : Gamma.measure (0 : DomainL2 Q) B ≠ ⊤ :=
    Gamma.measure_ne_top E.domain.zero_mem B
  rw [← ENNReal.ofReal_toReal hfin, h1]
  simp

theorem aux_rem_random_weights_R_nonneg {d : ℕ}
    (Q : Opens (SpatialCoordinates d))
    [CompactSpace ↥(closure (Q : Set (SpatialCoordinates d)))]
    (potEval : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ) → SpatialCoordinates d → ℝ)
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E)
    (R : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ) → DomainL2 Q → ℝ)
    (hR : ∀ v f, IsLUB {t : ℝ | ∃ u : DomainL2 Q, u ∈ E.domain ∧
      t = 2 * inner ℝ f u - ∫ x in (Q : Set (SpatialCoordinates d)),
        Real.exp (potEval v x) ∂(Gamma.measure u)} (R v f))
    (v : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ)) (f : DomainL2 Q) :
    0 ≤ R v f := by
  refine (hR v f).1 ⟨0, E.domain.zero_mem, ?_⟩
  rw [aux_rem_random_weights_energy_zero Q E Gamma]
  simp


/-- Two-sided exponential comparison of the catalogue-weighted coefficients. -/
theorem aux_rem_random_weights_coeff_exp {d : ℕ}
    (Q : Opens (SpatialCoordinates d))
    [CompactSpace ↥(closure (Q : Set (SpatialCoordinates d)))]
    {Ω : Type*}
    (a : ℕ → Ω → PositiveCoefficient Q)
    (potEval : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ) → SpatialCoordinates d → ℝ)
    (hpotEval : ∀ (v : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ))
      (x : SpatialCoordinates d) (hx : x ∈ closure (Q : Set (SpatialCoordinates d))),
      potEval v x = v ⟨x, hx⟩)
    (aw : ℕ → Ω → C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ) → PositiveCoefficient Q)
    (haw : ∀ n ω v, ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
      (aw n ω v).val x = Real.exp (potEval v x) * (a n ω).val x)
    (n : ℕ) (ω : Ω) (v w : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ)) :
    (∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
        Real.exp (-‖v - w‖) * (aw n ω w).val x ≤ (aw n ω v).val x) ∧
      (∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
        (aw n ω v).val x ≤ Real.exp ‖v - w‖ * (aw n ω w).val x) := by
  obtain ⟨ca, hca, hage⟩ := (a n ω).property
  have hmem : ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
      x ∈ (Q : Set (SpatialCoordinates d)) := ae_restrict_mem Q.isOpen.measurableSet
  constructor
  · filter_upwards [hmem, haw n ω v, haw n ω w, hage] with x hx hv hw hax
    have hb := aux_rem_random_weights_pot_diff_bound Q potEval hpotEval v w x (subset_closure hx)
    have hlow : Real.exp (-‖v - w‖) * Real.exp (potEval w x) ≤ Real.exp (potEval v x) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp hb).1])
    have haxpos : (0 : ℝ) ≤ (a n ω).val x := le_trans hca.le hax
    rw [hv, hw, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hlow haxpos
  · filter_upwards [hmem, haw n ω v, haw n ω w, hage] with x hx hv hw hax
    have hb := aux_rem_random_weights_pot_diff_bound Q potEval hpotEval v w x (subset_closure hx)
    have hhigh : Real.exp (potEval v x) ≤ Real.exp ‖v - w‖ * Real.exp (potEval w x) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp hb).2])
    have haxpos : (0 : ℝ) ≤ (a n ω).val x := le_trans hca.le hax
    rw [hv, hw, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hhigh haxpos

/-- Two-sided exponential comparison of the finite inverse responses. -/
theorem aux_rem_random_weights_IR_exp {d : ℕ}
    (Q : Opens (SpatialCoordinates d))
    [CompactSpace ↥(closure (Q : Set (SpatialCoordinates d)))]
    {Ω : Type*}
    (S : ResponseSpace Q)
    (a : ℕ → Ω → PositiveCoefficient Q)
    (potEval : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ) → SpatialCoordinates d → ℝ)
    (hpotEval : ∀ (v : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ))
      (x : SpatialCoordinates d) (hx : x ∈ closure (Q : Set (SpatialCoordinates d))),
      potEval v x = v ⟨x, hx⟩)
    (aw : ℕ → Ω → C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ) → PositiveCoefficient Q)
    (haw : ∀ n ω v, ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
      (aw n ω v).val x = Real.exp (potEval v x) * (a n ω).val x)
    (n : ℕ) (ω : Ω) (v w : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ))
    (L : S.space →L[ℝ] ℝ) :
    Real.exp (-‖v - w‖) * inverseResponse S (aw n ω w) L ≤ inverseResponse S (aw n ω v) L ∧
      inverseResponse S (aw n ω v) L ≤ Real.exp ‖v - w‖ * inverseResponse S (aw n ω w) L := by
  obtain ⟨hl, hu⟩ := aux_rem_random_weights_coeff_exp Q a potEval hpotEval aw haw n ω v w
  exact inverseResponse_exp_comparison S (aw n ω w) (aw n ω v) L ‖v - w‖ hl hu


/-- An a.e.-measurable real function on a finite measure space has vanishing tails. -/
theorem aux_rem_random_weights_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (Y : Ω → ℝ) (hY : AEMeasurable Y P) (eta : ℝ≥0∞) (heta : 0 < eta) :
    ∃ C : ℝ, 0 ≤ C ∧ P {ω | C < Y ω} ≤ eta := by
  classical
  set Y' : Ω → ℝ := hY.mk Y with hY'
  have hY'meas : Measurable Y' := hY.measurable_mk
  have hY'eq : Y =ᵐ[P] Y' := hY.ae_eq_mk
  set A : ℕ → Set Ω := fun k => {ω | (k : ℝ) < Y' ω} with hA
  have hAmeas : ∀ k, NullMeasurableSet (A k) P := fun k =>
    (hY'meas measurableSet_Ioi).nullMeasurableSet
  have hAanti : Antitone A := by
    intro j k hjk ω hω
    have : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk
    exact lt_of_le_of_lt this hω
  have hinter : (⋂ k, A k) = (∅ : Set Ω) := by
    ext ω
    simp only [mem_iInter, hA, mem_setOf_eq, mem_empty_iff_false, iff_false, not_forall, not_lt]
    obtain ⟨k, hk⟩ := exists_nat_gt (Y' ω)
    exact ⟨k, hk.le⟩
  have hlim : Tendsto (fun k => P (A k)) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (μ := P) hAmeas hAanti ⟨0, measure_ne_top P _⟩
    rw [hinter] at this
    simpa using this
  obtain ⟨k, hk⟩ := (ENNReal.tendsto_nhds_zero.mp hlim eta heta).exists
  refine ⟨(k : ℝ), Nat.cast_nonneg k, ?_⟩
  have hsub : {ω | (k : ℝ) < Y ω} ⊆ A k ∪ {ω | Y ω ≠ Y' ω} := by
    intro ω hω
    by_cases h : Y ω = Y' ω
    · exact Or.inl (by simpa [hA, ← h] using hω)
    · exact Or.inr h
  have hnull : P {ω | Y ω ≠ Y' ω} = 0 := hY'eq
  calc P {ω | (k : ℝ) < Y ω} ≤ P (A k ∪ {ω | Y ω ≠ Y' ω}) := measure_mono hsub
    _ ≤ P (A k) + P {ω | Y ω ≠ Y' ω} := measure_union_le _ _
    _ ≤ eta := by rw [hnull, add_zero]; exact hk


/-- The law of the random potential on the separable Banach space of continuous
potentials is tight. -/
theorem aux_rem_random_weights_tight {d : ℕ}
    (Q : Opens (SpatialCoordinates d))
    [CompactSpace ↥(closure (Q : Set (SpatialCoordinates d)))]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (V : Ω → C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ))
    (hV : @Measurable Ω C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ)
      _ (borel C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ)) V)
    (epsilon : ℝ) (heps : 0 < epsilon) :
    ∃ K : Set C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ),
      IsCompact K ∧ P {ω | V ω ∉ K} ≤ ENNReal.ofReal epsilon := by
  classical
  letI : MeasurableSpace C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ) :=
    borel C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ)
  haveI : BorelSpace C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ) := ⟨rfl⟩
  haveI : IsFiniteMeasure (P.map V) := by
    constructor
    rw [Measure.map_apply hV MeasurableSet.univ]
    simp
  have htight : IsTightMeasureSet {P.map V} := isTightMeasureSet_singleton
  obtain ⟨K, hK, hKmass⟩ :=
    (IsTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight)
      (ENNReal.ofReal epsilon) (by simpa using heps)
  refine ⟨K, hK, ?_⟩
  have hpre : {ω | V ω ∉ K} = V ⁻¹' Kᶜ := rfl
  rw [hpre, ← Measure.map_apply hV hK.isClosed.measurableSet.compl]
  exact hKmass _ rfl

/-- A finite measurable catalogue selection at scale `delta` on a compact set of
potentials. -/
theorem aux_rem_random_weights_select {d : ℕ}
    (Q : Opens (SpatialCoordinates d))
    [CompactSpace ↥(closure (Q : Set (SpatialCoordinates d)))]
    {Ω : Type*} [MeasurableSpace Ω]
    (catalog : ℕ → C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ))
    (hdense : DenseRange catalog)
    (V : Ω → C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ))
    (hV : @Measurable Ω C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ)
      _ (borel C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ)) V)
    (K : Set C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ)) (hK : IsCompact K)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ (F : Finset ℕ) (sel : Ω → ℕ),
      Measurable sel ∧ (∀ ω, sel ω ∈ F) ∧
      ∀ ω, V ω ∈ K → ‖V ω - catalog (sel ω)‖ ≤ delta := by
  classical
  letI : MeasurableSpace C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ) :=
    borel C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ)
  haveI : BorelSpace C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ) := ⟨rfl⟩
  have hcover : K ⊆ ⋃ k : ℕ, Metric.ball (catalog k) delta := by
    intro v _
    obtain ⟨k, hk⟩ := hdense.exists_dist_lt v hdelta
    exact mem_iUnion.2 ⟨k, by simpa [Metric.mem_ball] using hk⟩
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover (fun k : ℕ => Metric.ball (catalog k) delta)
    (fun _ => Metric.isOpen_ball) hcover
  set m : ℕ := F.sup id + 1 with hm
  have hmF : ∀ k ∈ F, k < m := by
    intro k hk
    have : k ≤ F.sup id := Finset.le_sup (f := id) hk
    omega
  set p : ℕ → Ω → Prop := fun k ω => (k ∈ F ∧ ‖V ω - catalog k‖ ≤ delta) ∨ k = m with hp
  have hpex : ∀ ω, ∃ k, p k ω := fun ω => ⟨m, Or.inr rfl⟩
  have hpmeas : ∀ k, MeasurableSet {ω | p k ω} := by
    intro k
    have hnorm : Measurable (fun ω => ‖V ω - catalog k‖) :=
      (continuous_id.sub continuous_const).norm.measurable.comp hV
    by_cases hkF : k ∈ F
    · by_cases hkm : k = m
      · have : {ω | p k ω} = Set.univ := by ext ω; simp [hp, hkm]
        rw [this]; exact MeasurableSet.univ
      · have : {ω | p k ω} = {ω | ‖V ω - catalog k‖ ≤ delta} := by
          ext ω; simp [hp, hkF, hkm]
        rw [this]
        exact hnorm measurableSet_Iic
    · by_cases hkm : k = m
      · have : {ω | p k ω} = Set.univ := by ext ω; simp [hp, hkm]
        rw [this]; exact MeasurableSet.univ
      · have : {ω | p k ω} = (∅ : Set Ω) := by ext ω; simp [hp, hkF, hkm]
        rw [this]; exact MeasurableSet.empty
  have hselm : Measurable (fun ω => Nat.find (hpex ω)) :=
    Measurable.find (f := fun n (_ : Ω) => n) (fun n => measurable_const) hpmeas hpex
  refine ⟨insert m F, fun ω => Nat.find (hpex ω), hselm, ?_, ?_⟩
  · intro ω
    show Nat.find (hpex ω) ∈ insert m F
    rcases Nat.find_spec (hpex ω) with h | h
    · exact Finset.mem_insert_of_mem h.1
    · rw [h]
      exact Finset.mem_insert_self m F
  · intro ω hω
    show ‖V ω - catalog (Nat.find (hpex ω))‖ ≤ delta
    obtain ⟨k, hkF, hkball⟩ : ∃ k ∈ F, V ω ∈ Metric.ball (catalog k) delta := by
      simpa only [mem_iUnion, exists_prop] using hF hω
    have hk : p k ω := Or.inl ⟨hkF, le_of_lt (by
      simpa [Metric.mem_ball, dist_eq_norm] using hkball)⟩
    have hle : Nat.find (hpex ω) ≤ k := Nat.find_le hk
    rcases Nat.find_spec (hpex ω) with h | h
    · exact h.2
    · rw [h] at hle
      exact absurd hle (not_le.mpr (hmF k hkF))
/-- The elementary two-sided estimate behind the random-weight convergence: a
multiplicative comparison at scale `D` plus an additive comparison of the two
catalogue quantities gives an additive comparison of the random ones. -/
theorem aux_rem_random_weights_gap (ep An Bn Rk Rv D delta Cc : ℝ)
    (hep0 : 0 < ep) (hDnn : 0 ≤ D) (hDle : D ≤ delta) (hdeltapos : 0 < delta)
    (hexp2 : Real.exp delta ≤ 2)
    (hgapbound : 2 * (Real.exp delta - 1) * Cc ≤ ep / 4)
    (hCcnn : 0 ≤ Cc)
    (hIRlo : Real.exp (-D) * An ≤ Bn) (hIRhi : Bn ≤ Real.exp D * An)
    (hRlo : Real.exp (-D) * Rk ≤ Rv) (hRhi : Rv ≤ Real.exp D * Rk)
    (hRknn : 0 ≤ Rk) (hRkC : Rk ≤ Cc) (hclose : |An - Rk| < ep / 8) :
    |Bn - Rv| < ep := by
  set eD : ℝ := Real.exp D with heD
  set emD : ℝ := Real.exp (-D) with hemD
  have heDpos : 0 < eD := Real.exp_pos _
  have hemDpos : 0 < emD := Real.exp_pos _
  have heDone : 1 ≤ eD := Real.one_le_exp hDnn
  have hemDone : emD ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have heDdel : eD ≤ Real.exp delta := Real.exp_le_exp.mpr hDle
  have hemDdel : Real.exp (-delta) ≤ emD := Real.exp_le_exp.mpr (by linarith)
  have hgap : eD - emD ≤ 2 * (Real.exp delta - 1) := by
    have hX1 : 1 ≤ Real.exp delta := Real.one_le_exp hdeltapos.le
    have hX0 : 0 < Real.exp delta := Real.exp_pos _
    have hinv : Real.exp (-delta) = (Real.exp delta)⁻¹ := Real.exp_neg _
    have hXX : Real.exp delta * (Real.exp delta)⁻¹ = 1 := by field_simp
    have hle : (Real.exp delta)⁻¹ ≤ emD := by rw [← hinv]; exact hemDdel
    nlinarith [sq_nonneg (Real.exp delta - 1)]
  have hgapnn : (0 : ℝ) ≤ eD - emD := by linarith
  have hgapC : (eD - emD) * Rk ≤ ep / 4 := by
    have h1' : (eD - emD) * Rk ≤ (eD - emD) * Cc :=
      mul_le_mul_of_nonneg_left hRkC hgapnn
    have h2' : (eD - emD) * Cc ≤ 2 * (Real.exp delta - 1) * Cc :=
      mul_le_mul_of_nonneg_right hgap hCcnn
    linarith
  have h8 : eD * (ep / 8) ≤ ep / 4 := by
    have hle2 : eD ≤ 2 := le_trans heDdel hexp2
    nlinarith [hep0.le]
  have hupper1 : Bn - Rv ≤ (eD - emD) * Rk + eD * (ep / 8) := by
    have hA : An ≤ Rk + ep / 8 := by linarith [(abs_lt.mp hclose).2]
    nlinarith [mul_le_mul_of_nonneg_left hA heDpos.le, hIRhi, hRlo]
  have hupper2 : Rv - Bn ≤ (eD - emD) * Rk + eD * (ep / 8) := by
    have hA : Rk - ep / 8 ≤ An := by linarith [(abs_lt.mp hclose).1]
    have h6 : emD * (ep / 8) ≤ eD * (ep / 8) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hA hemDpos.le, hRhi, hIRlo]
  rw [abs_lt]
  constructor <;> linarith


/-- The scale chosen from the tail constant absorbs the multiplicative error. -/
theorem aux_rem_random_weights_theta (ep Cc : ℝ) (hep : 0 < ep) (hCc : 0 ≤ Cc) :
    2 * (ep / (8 * (Cc + 1))) * Cc ≤ ep / 4 := by
  have hpos : (0 : ℝ) < Cc + 1 := by linarith
  have key : 2 * (ep / (8 * (Cc + 1))) * Cc = ep / 4 * (Cc / (Cc + 1)) := by
    field_simp
    ring
  have hle : Cc / (Cc + 1) ≤ 1 := by
    rw [div_le_one hpos]
    linarith
  rw [key]
  calc ep / 4 * (Cc / (Cc + 1)) ≤ ep / 4 * 1 :=
        mul_le_mul_of_nonneg_left hle (by linarith)
    _ = ep / 4 := by ring

/-- The exceptional set of the random-weight convergence: off the compact set of
potentials, the tail event of the catalogue limit at the zero potential, and the
finitely many catalogue convergence events, the random inverse response is within
`ep` of its limit. -/
theorem aux_rem_random_weights_exceptional {d : ℕ}
    (Q : Opens (SpatialCoordinates d))
    [CompactSpace ↥(closure (Q : Set (SpatialCoordinates d)))]
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ResponseSpace Q)
    (a : ℕ → Ω → PositiveCoefficient Q)
    (potEval : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ) → SpatialCoordinates d → ℝ)
    (hpotEval : ∀ (v : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ))
      (x : SpatialCoordinates d) (hx : x ∈ closure (Q : Set (SpatialCoordinates d))),
      potEval v x = v ⟨x, hx⟩)
    (aw : ℕ → Ω → C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ) → PositiveCoefficient Q)
    (haw : ∀ n ω v, ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
      (aw n ω v).val x = Real.exp (potEval v x) * (a n ω).val x)
    (E : Ω → DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : ∀ ω, DirichletForm.EnergyMeasure (E ω))
    (R : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ) → Ω → DomainL2 Q → ℝ)
    (hR : ∀ v ω f, IsLUB {t : ℝ | ∃ u : DomainL2 Q, u ∈ (E ω).domain ∧
      t = 2 * inner ℝ f u - ∫ x in (Q : Set (SpatialCoordinates d)),
        Real.exp (potEval v x) ∂((Gamma ω).measure u)} (R v ω f))
    (catalog : ℕ → C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ))
    (hzero : catalog 0 = 0)
    (V : Ω → C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ))
    (g : DomainL2 Q)
    (K : Set C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ))
    (M Ct Cc delta ep : ℝ)
    (hKball : K ⊆ Metric.closedBall 0 M)
    (hCc : Cc = Real.exp (M + 1) * Ct) (hCcnn : 0 ≤ Cc)
    (hdeltapos : 0 < delta) (hdelta1 : delta ≤ 1) (hexp2 : Real.exp delta ≤ 2)
    (hgapbound : 2 * (Real.exp delta - 1) * Cc ≤ ep / 4) (hep0 : 0 < ep)
    (F : Finset ℕ) (sel : Ω → ℕ) (hselF : ∀ ω, sel ω ∈ F)
    (hselclose : ∀ ω, V ω ∈ K → ‖V ω - catalog (sel ω)‖ ≤ delta)
    (n : ℕ) :
    {ω | ENNReal.ofReal ep ≤ edist (inverseResponse S (aw n ω (V ω))
        ((sobolevVolumeLoad g).comp S.space.subtypeL)) (R (V ω) ω g)} ⊆
      {ω | V ω ∉ K} ∪ ({ω | Ct < R (catalog 0) ω g} ∪
        ⋃ k ∈ F, {ω | ENNReal.ofReal (ep / 8) ≤
          edist (inverseResponse S (aw n ω (catalog k))
            ((sobolevVolumeLoad g).comp S.space.subtypeL)) (R (catalog k) ω g)}) := by
  classical
  set L0 : S.space →L[ℝ] ℝ := (sobolevVolumeLoad g).comp S.space.subtypeL with hL0
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω
  by_cases h1 : V ω ∉ K
  · exact Or.inl h1
  refine Or.inr ?_
  rw [not_not] at h1
  by_cases h2 : Ct < R (catalog 0) ω g
  · exact Or.inl h2
  refine Or.inr ?_
  by_cases h3 : ∃ k ∈ F, ENNReal.ofReal (ep / 8) ≤
      edist (inverseResponse S (aw n ω (catalog k)) L0) (R (catalog k) ω g)
  · obtain ⟨k, hkF, hk⟩ := h3
    exact mem_biUnion hkF hk
  exfalso
  push_neg at h2 h3
  set k : ℕ := sel ω with hk
  have hkF : k ∈ F := hselF ω
  set D : ℝ := ‖V ω - catalog k‖ with hD
  have hDnn : (0 : ℝ) ≤ D := norm_nonneg _
  have hDle : D ≤ delta := hselclose ω h1
  set An : ℝ := inverseResponse S (aw n ω (catalog k)) L0 with hAn
  set Bn : ℝ := inverseResponse S (aw n ω (V ω)) L0 with hBn
  set Rk : ℝ := R (catalog k) ω g with hRk
  set Rv : ℝ := R (V ω) ω g with hRv
  have hemDpos : 0 < Real.exp (-D) := Real.exp_pos _
  have hIR := aux_rem_random_weights_IR_exp Q S a potEval hpotEval aw haw n ω (V ω)
    (catalog k) L0
  have hIRlo : Real.exp (-D) * An ≤ Bn := hIR.1
  have hIRhi : Bn ≤ Real.exp D * An := hIR.2
  have hRhi : Rv ≤ Real.exp D * Rk :=
    aux_rem_random_weights_R_half Q potEval hpotEval (E ω) (Gamma ω)
      (fun v f => R v ω f) (fun v f => hR v ω f) (V ω) (catalog k) g
  have hRlo : Real.exp (-D) * Rk ≤ Rv := by
    have h := aux_rem_random_weights_R_half Q potEval hpotEval (E ω) (Gamma ω)
      (fun v f => R v ω f) (fun v f => hR v ω f) (catalog k) (V ω) g
    rw [norm_sub_rev] at h
    have hmul := mul_le_mul_of_nonneg_left h hemDpos.le
    have hassoc : Real.exp (-D) * (Real.exp D * Rv) = Rv := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    rw [hassoc] at hmul
    exact hmul
  have hRknn : (0 : ℝ) ≤ Rk :=
    aux_rem_random_weights_R_nonneg Q potEval (E ω) (Gamma ω)
      (fun v f => R v ω f) (fun v f => hR v ω f) (catalog k) g
  have hclose : |An - Rk| < ep / 8 := by
    have h := h3 k hkF
    rw [edist_dist, Real.dist_eq] at h
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mp h
  have hVnorm : ‖V ω‖ ≤ M := by
    have h := hKball h1
    simpa [Metric.mem_closedBall, dist_eq_norm] using h
  have hcatnorm : ‖catalog k - catalog 0‖ ≤ M + 1 := by
    rw [hzero, sub_zero]
    have hsplit : ‖catalog k‖ ≤ ‖V ω‖ + ‖catalog k - V ω‖ := by
      calc ‖catalog k‖ = ‖V ω + (catalog k - V ω)‖ := by congr 1; abel
        _ ≤ ‖V ω‖ + ‖catalog k - V ω‖ := norm_add_le _ _
    have hrev : ‖catalog k - V ω‖ = D := by rw [hD, norm_sub_rev]
    rw [hrev] at hsplit
    linarith
  have hRkC : Rk ≤ Cc := by
    have h := aux_rem_random_weights_R_half Q potEval hpotEval (E ω) (Gamma ω)
      (fun v f => R v ω f) (fun v f => hR v ω f) (catalog k) (catalog 0) g
    have h0nn : (0 : ℝ) ≤ R (catalog 0) ω g :=
      aux_rem_random_weights_R_nonneg Q potEval (E ω) (Gamma ω)
        (fun v f => R v ω f) (fun v f => hR v ω f) (catalog 0) g
    have hmono : Real.exp ‖catalog k - catalog 0‖ ≤ Real.exp (M + 1) :=
      Real.exp_le_exp.mpr hcatnorm
    calc Rk ≤ Real.exp ‖catalog k - catalog 0‖ * R (catalog 0) ω g := h
      _ ≤ Real.exp (M + 1) * R (catalog 0) ω g :=
          mul_le_mul_of_nonneg_right hmono h0nn
      _ ≤ Real.exp (M + 1) * Ct := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = Cc := hCc.symm
  have hfinal : |Bn - Rv| < ep :=
    aux_rem_random_weights_gap ep An Bn Rk Rv D delta Cc hep0 hDnn hDle hdeltapos hexp2
      hgapbound hCcnn hIRlo hIRhi hRlo hRhi hRknn hRkC hclose
  have hge : ep ≤ |Bn - Rv| := by
    have h := hω
    rw [edist_dist, Real.dist_eq] at h
    exact (ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)).mp h
  linarith

/-- Convergence in probability of the finite inverse responses at the *random*
potential, for one volume source.  This is conjunct (C) of the remark at a single
load; the tail bound on the catalogue limit is supplied by the `AEMeasurable`
conclusions of `rem_random_weights_catalog_transfer`. -/
theorem aux_rem_random_weights_single {d : ℕ}
    (Q : Opens (SpatialCoordinates d))
    [CompactSpace ↥(closure (Q : Set (SpatialCoordinates d)))]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ResponseSpace Q)
    (a : ℕ → Ω → PositiveCoefficient Q)
    (potEval : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ) → SpatialCoordinates d → ℝ)
    (hpotEval : ∀ (v : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ))
      (x : SpatialCoordinates d) (hx : x ∈ closure (Q : Set (SpatialCoordinates d))),
      potEval v x = v ⟨x, hx⟩)
    (aw : ℕ → Ω → C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ) → PositiveCoefficient Q)
    (haw : ∀ n ω v, ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
      (aw n ω v).val x = Real.exp (potEval v x) * (a n ω).val x)
    (E : Ω → DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : ∀ ω, DirichletForm.EnergyMeasure (E ω))
    (R : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ) → Ω → DomainL2 Q → ℝ)
    (hR : ∀ v ω f, IsLUB {t : ℝ | ∃ u : DomainL2 Q, u ∈ (E ω).domain ∧
      t = 2 * inner ℝ f u - ∫ x in (Q : Set (SpatialCoordinates d)),
        Real.exp (potEval v x) ∂((Gamma ω).measure u)} (R v ω f))
    (catalog : ℕ → C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ))
    (hdense : DenseRange catalog) (hzero : catalog 0 = 0)
    (hdet : ∀ k : ℕ, ∀ f : DomainL2 Q,
      TendstoInMeasure P (fun n ω => inverseResponse S (aw n ω (catalog k))
        ((sobolevVolumeLoad f).comp S.space.subtypeL)) atTop (fun ω => R (catalog k) ω f))
    (hRmeas : ∀ (k : ℕ) (f : DomainL2 Q),
      AEMeasurable (fun ω => R (catalog k) ω f) P)
    (V : Ω → C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ))
    (hV : @Measurable Ω C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ)
      _ (borel C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ)) V)
    (g : DomainL2 Q) :
    TendstoInMeasure P (fun n ω => inverseResponse S (aw n ω (V ω))
      ((sobolevVolumeLoad g).comp S.space.subtypeL)) atTop (fun ω => R (V ω) ω g) := by
  classical
  refine tendstoInMeasure_of_ne_top ?_
  intro ε hε hεtop
  obtain ⟨ep, hep0, rfl⟩ : ∃ ep : ℝ, 0 < ep ∧ ε = ENNReal.ofReal ep :=
    ⟨ε.toReal, ENNReal.toReal_pos hε.ne' hεtop, (ENNReal.ofReal_toReal hεtop).symm⟩
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  obtain ⟨r, hr0, hrη⟩ : ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r ≤ η := by
    rcases eq_or_ne η ⊤ with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · exact ⟨η.toReal, ENNReal.toReal_pos hη.ne' h, by rw [ENNReal.ofReal_toReal h]⟩
  have hr4 : (0 : ℝ) < r / 4 := by linarith
  obtain ⟨K, hK, hKmass⟩ := aux_rem_random_weights_tight Q P V hV (r / 4) hr4
  obtain ⟨M0, hM0⟩ := hK.isBounded.subset_closedBall
    (0 : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ))
  have hMnn : (0 : ℝ) ≤ max M0 0 := le_max_right _ _
  have hKball : K ⊆ Metric.closedBall 0 (max M0 0) :=
    hM0.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  obtain ⟨Ct, hCt0, hCt⟩ := aux_rem_random_weights_tail P (fun ω => R (catalog 0) ω g)
    (hRmeas 0 g) (ENNReal.ofReal (r / 4)) (by simpa using hr4)
  have hCcnn : (0 : ℝ) ≤ Real.exp (max M0 0 + 1) * Ct := by positivity
  have hθpos : 0 < ep / (8 * (Real.exp (max M0 0 + 1) * Ct + 1)) :=
    div_pos hep0 (by linarith)
  have hdeltapos : 0 < min (Real.log 2)
      (Real.log (1 + ep / (8 * (Real.exp (max M0 0 + 1) * Ct + 1)))) :=
    lt_min (Real.log_pos (by norm_num)) (Real.log_pos (by linarith))
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  have hdelta1 : min (Real.log 2)
      (Real.log (1 + ep / (8 * (Real.exp (max M0 0 + 1) * Ct + 1)))) ≤ 1 :=
    le_trans (min_le_left _ _) hlog2
  have hexp2 : Real.exp (min (Real.log 2)
      (Real.log (1 + ep / (8 * (Real.exp (max M0 0 + 1) * Ct + 1))))) ≤ 2 := by
    calc Real.exp (min (Real.log 2)
        (Real.log (1 + ep / (8 * (Real.exp (max M0 0 + 1) * Ct + 1)))))
        ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (min_le_left _ _)
      _ = 2 := Real.exp_log (by norm_num)
  have hgapbound : 2 * (Real.exp (min (Real.log 2)
      (Real.log (1 + ep / (8 * (Real.exp (max M0 0 + 1) * Ct + 1))))) - 1) *
        (Real.exp (max M0 0 + 1) * Ct) ≤ ep / 4 := by
    have hexpθ : Real.exp (min (Real.log 2)
        (Real.log (1 + ep / (8 * (Real.exp (max M0 0 + 1) * Ct + 1))))) - 1 ≤
        ep / (8 * (Real.exp (max M0 0 + 1) * Ct + 1)) := by
      have h : Real.exp (min (Real.log 2)
          (Real.log (1 + ep / (8 * (Real.exp (max M0 0 + 1) * Ct + 1))))) ≤
          Real.exp (Real.log (1 + ep / (8 * (Real.exp (max M0 0 + 1) * Ct + 1)))) :=
        Real.exp_le_exp.mpr (min_le_right _ _)
      rw [Real.exp_log (by linarith)] at h
      linarith
    have h2' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hexpθ (by norm_num : (0:ℝ) ≤ 2)) hCcnn
    exact le_trans h2'
      (aux_rem_random_weights_theta ep (Real.exp (max M0 0 + 1) * Ct) hep0 hCcnn)
  obtain ⟨F, sel, hselm, hselF, hselclose⟩ :=
    aux_rem_random_weights_select Q catalog hdense V hV K hK _ hdeltapos
  have hep8 : (0 : ℝ≥0∞) < ENNReal.ofReal (ep / 8) := ENNReal.ofReal_pos.mpr (by linarith)
  have hSig : Tendsto (fun n => ∑ k ∈ F,
      P {ω | ENNReal.ofReal (ep / 8) ≤
        edist (inverseResponse S (aw n ω (catalog k))
          ((sobolevVolumeLoad g).comp S.space.subtypeL)) (R (catalog k) ω g)})
      atTop (𝓝 0) := by
    have h := tendsto_finset_sum F (fun k (_ : k ∈ F) =>
      hdet k g (ENNReal.ofReal (ep / 8)) hep8)
    simpa using h
  filter_upwards [ENNReal.tendsto_nhds_zero.mp hSig (ENNReal.ofReal (r / 4))
    (by simpa using hr4)] with n hn
  have hsub := aux_rem_random_weights_exceptional Q S a potEval hpotEval aw haw E Gamma
    R hR catalog hzero V g K (max M0 0) Ct (Real.exp (max M0 0 + 1) * Ct) _ ep
    hKball rfl hCcnn hdeltapos hdelta1 hexp2 hgapbound hep0 F sel hselF hselclose n
  have hcount := measure_biUnion_finset_le (μ := P) F
    (fun k => {ω | ENNReal.ofReal (ep / 8) ≤
      edist (inverseResponse S (aw n ω (catalog k))
        ((sobolevVolumeLoad g).comp S.space.subtypeL)) (R (catalog k) ω g)})
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_union_le _ _) ?_
  refine le_trans (add_le_add hKmass
    (le_trans (measure_union_le _ _) (add_le_add hCt (le_trans hcount hn)))) ?_
  rw [← ENNReal.ofReal_add (by linarith) (by linarith),
    ← ENNReal.ofReal_add (by linarith) (by linarith)]
  exact le_trans (ENNReal.ofReal_le_ofReal (by linarith)) hrη

/-- Convergence in measure is unaffected by a common first coordinate. -/
theorem aux_rem_random_weights_pair {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {X : Type*} [PseudoEMetricSpace X] {Y : Type*} [PseudoEMetricSpace Y]
    (V : Ω → X) (Fn : ℕ → Ω → Y) (G : Ω → Y)
    (h : TendstoInMeasure P Fn atTop G) :
    TendstoInMeasure P (fun n ω => (V ω, Fn n ω)) atTop (fun ω => (V ω, G ω)) := by
  intro ε hε
  have hset : ∀ n : ℕ, {ω | ε ≤ edist (V ω, Fn n ω) (V ω, G ω)} =
      {ω | ε ≤ edist (Fn n ω) (G ω)} := by
    intro n
    ext ω
    simp [Prod.edist_eq]
  simp only [hset]
  exact h ε hε

/-- Finitely many coordinates converge in measure jointly. -/
theorem aux_rem_random_weights_fin {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {m : ℕ} (Fn : Fin m → ℕ → Ω → ℝ) (G : Fin m → Ω → ℝ)
    (h : ∀ i, TendstoInMeasure P (Fn i) atTop (G i)) :
    TendstoInMeasure P (fun n ω i => Fn i n ω) atTop (fun ω i => G i ω) := by
  intro ε hε
  have hsub : ∀ n : ℕ, {ω | ε ≤ edist (fun i => Fn i n ω) (fun i => G i ω)} ⊆
      ⋃ i : Fin m, {ω | ε ≤ edist (Fn i n ω) (G i ω)} := by
    intro n ω hω
    simp only [Set.mem_setOf_eq] at hω
    rw [edist_pi_def] at hω
    obtain ⟨i, _, hi⟩ := (Finset.le_sup_iff hε).mp hω
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  have hsum : Tendsto (fun n : ℕ => ∑ i : Fin m,
      P {ω | ε ≤ edist (Fn i n ω) (G i ω)}) atTop (𝓝 0) := by
    have hh := tendsto_finset_sum Finset.univ
      (fun (i : Fin m) (_ : i ∈ Finset.univ) => h i ε hε)
    simpa using hh
  filter_upwards [ENNReal.tendsto_nhds_zero.mp hsum η hη] with n hn
  exact le_trans (le_trans (measure_mono (hsub n))
    (measure_iUnion_fintype_le _ _)) hn

/-- Finite measurable selection from a dense catalogue on a compact set of
potentials of probability at least `1 - epsilon`. -/
theorem aux_rem_random_weights_selection {d : ℕ}
    (Q : Opens (SpatialCoordinates d))
    [CompactSpace ↥(closure (Q : Set (SpatialCoordinates d)))]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (catalog : ℕ → C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ))
    (hdense : DenseRange catalog)
    (V : Ω → C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ))
    (hV : @Measurable Ω C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ)
      _ (borel C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ)) V) :
    ∀ (epsilon : ℝ), 0 < epsilon → ∀ (delta : ℝ), 0 < delta →
      ∃ (K : Set C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ))
        (F : Finset ℕ) (sel : Ω → ℕ),
        IsCompact K ∧ Measurable sel ∧ (∀ ω, sel ω ∈ F) ∧
        P {ω | V ω ∉ K} ≤ ENNReal.ofReal epsilon ∧
        ∀ ω, V ω ∈ K → ‖V ω - catalog (sel ω)‖ ≤ delta := by
  intro epsilon heps delta hdelta
  obtain ⟨K, hK, hKmass⟩ := aux_rem_random_weights_tight Q P V hV epsilon heps
  obtain ⟨F, sel, hselm, hselF, hselclose⟩ :=
    aux_rem_random_weights_select Q catalog hdense V hV K hK delta hdelta
  exact ⟨K, F, sel, hK, hselm, hselF, hKmass, hselclose⟩

/-- The pointwise two-sided comparison of two catalogue-weighted coefficients. -/
theorem aux_rem_random_weights_coeff_comparison {d : ℕ}
    (Q : Opens (SpatialCoordinates d))
    [CompactSpace ↥(closure (Q : Set (SpatialCoordinates d)))]
    {Ω : Type*}
    (a : ℕ → Ω → PositiveCoefficient Q)
    (potEval : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ) → SpatialCoordinates d → ℝ)
    (aw : ℕ → Ω → C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ) → PositiveCoefficient Q)
    (haw : ∀ n ω v, ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
      (aw n ω v).val x = Real.exp (potEval v x) * (a n ω).val x)
    (n : ℕ) (ω : Ω) (v w : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ)) (ε : ℝ)
    (hratio : ∀ x ∈ Q, |Real.exp (potEval v x) / Real.exp (potEval w x) - 1| ≤ ε) :
    ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
      (1 - ε) * (aw n ω w).val x ≤ (aw n ω v).val x ∧
        (aw n ω v).val x ≤ (1 + ε) * (aw n ω w).val x := by
  classical
  have hmem : ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
      x ∈ (Q : Set (SpatialCoordinates d)) := ae_restrict_mem Q.isOpen.measurableSet
  obtain ⟨ca, hca, hage⟩ := (a n ω).property
  filter_upwards [hmem, haw n ω v, haw n ω w, hage] with x hx hv hw hax
  have hexw : (0 : ℝ) < Real.exp (potEval w x) := Real.exp_pos _
  have hdiv : Real.exp (potEval v x) / Real.exp (potEval w x) *
      Real.exp (potEval w x) = Real.exp (potEval v x) := by
    field_simp
  obtain ⟨hlo, hhi⟩ := abs_le.mp (hratio x hx)
  have hlow : (1 - ε) * Real.exp (potEval w x) ≤ Real.exp (potEval v x) := by
    have h1 : (1 : ℝ) - ε ≤ Real.exp (potEval v x) / Real.exp (potEval w x) := by linarith
    have h2 := mul_le_mul_of_nonneg_right h1 hexw.le
    rwa [hdiv] at h2
  have hhigh : Real.exp (potEval v x) ≤ (1 + ε) * Real.exp (potEval w x) := by
    have h1 : Real.exp (potEval v x) / Real.exp (potEval w x) ≤ 1 + ε := by linarith
    have h2 := mul_le_mul_of_nonneg_right h1 hexw.le
    rwa [hdiv] at h2
  have haxpos : (0 : ℝ) ≤ (a n ω).val x := le_trans hca.le hax
  rw [hv, hw]
  constructor
  · calc (1 - ε) * (Real.exp (potEval w x) * (a n ω).val x)
        = ((1 - ε) * Real.exp (potEval w x)) * (a n ω).val x := by ring
      _ ≤ Real.exp (potEval v x) * (a n ω).val x :=
          mul_le_mul_of_nonneg_right hlow haxpos
  · calc Real.exp (potEval v x) * (a n ω).val x
        ≤ ((1 + ε) * Real.exp (potEval w x)) * (a n ω).val x :=
          mul_le_mul_of_nonneg_right hhigh haxpos
      _ = (1 + ε) * (Real.exp (potEval w x) * (a n ω).val x) := by ring

/-- Two weights whose exponential ratio is within `ε` of one give response forms
within the same two-sided factor. -/
theorem aux_rem_random_weights_form_comparison {d : ℕ}
    (Q : Opens (SpatialCoordinates d))
    [CompactSpace ↥(closure (Q : Set (SpatialCoordinates d)))]
    {Ω : Type*}
    (S : ResponseSpace Q)
    (a : ℕ → Ω → PositiveCoefficient Q)
    (potEval : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ) → SpatialCoordinates d → ℝ)
    (aw : ℕ → Ω → C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ) → PositiveCoefficient Q)
    (haw : ∀ n ω v, ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
      (aw n ω v).val x = Real.exp (potEval v x) * (a n ω).val x) :
    ∀ (n : ℕ) (ω : Ω)
      (v w : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ)) (ε : ℝ),
      0 ≤ ε →
      (∀ x ∈ Q, |Real.exp (potEval v x) / Real.exp (potEval w x) - 1| ≤ ε) →
      ∀ u : S.space,
        (1 - ε) * responseForm S (aw n ω w) u u ≤ responseForm S (aw n ω v) u u ∧
        responseForm S (aw n ω v) u u ≤ (1 + ε) * responseForm S (aw n ω w) u u := by
  classical
  intro n ω v w ε hε hratio u
  have hcomp := aux_rem_random_weights_coeff_comparison Q a potEval aw haw n ω v w ε hratio
  have hupper : responseForm S (aw n ω v) u u ≤ (1 + ε) * responseForm S (aw n ω w) u u := by
    have hpos : (0 : ℝ) < 1 + ε := by linarith
    have hae : ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
        (aw n ω v).val x ≤ (scalePositiveCoefficient (1 + ε) hpos (aw n ω w)).val x := by
      filter_upwards [hcomp, scalePositiveCoefficient_coeFn (1 + ε) hpos (aw n ω w)]
        with x hx he
      rw [he]
      exact hx.2
    have hmono := responseForm_mono S (aw n ω v)
      (scalePositiveCoefficient (1 + ε) hpos (aw n ω w)) hae u
    exact le_of_le_of_eq hmono (responseForm_scale_coefficient S (1 + ε) hpos (aw n ω w) u u)
  refine ⟨?_, hupper⟩
  rcases lt_or_ge ε 1 with hlt | hge
  · have hpos : (0 : ℝ) < 1 - ε := by linarith
    have hae : ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
        (scalePositiveCoefficient (1 - ε) hpos (aw n ω w)).val x ≤ (aw n ω v).val x := by
      filter_upwards [hcomp, scalePositiveCoefficient_coeFn (1 - ε) hpos (aw n ω w)]
        with x hx he
      rw [he]
      exact hx.1
    have hmono := responseForm_mono S (scalePositiveCoefficient (1 - ε) hpos (aw n ω w))
      (aw n ω v) hae u
    exact le_of_eq_of_le
      (responseForm_scale_coefficient S (1 - ε) hpos (aw n ω w) u u).symm hmono
  · have hnn := responseForm_nonneg S (aw n ω v) u
    have hnn' := responseForm_nonneg S (aw n ω w) u
    have h1 : (1 : ℝ) - ε ≤ 0 := by linarith
    have h2 : (1 - ε) * responseForm S (aw n ω w) u u ≤
        0 * responseForm S (aw n ω w) u u := mul_le_mul_of_nonneg_right h1 hnn'
    rw [zero_mul] at h2
    linarith





theorem rem_random_weights
    {d : ℕ} (hd : 2 ≤ d) (Q : Opens (SpatialCoordinates d))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hQ : (Q : Set (SpatialCoordinates d)) = Metric.ball z (r / 2))
    [CompactSpace ↥(closure (Q : Set (SpatialCoordinates d)))]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ResponseSpace Q) (hS : S.space = killedSobolevGraph Q)
    (a : ℕ → Ω → PositiveCoefficient Q)
    (potEval : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ) → SpatialCoordinates d → ℝ)
    (hpotEval : ∀ (v : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ))
      (x : SpatialCoordinates d) (hx : x ∈ closure (Q : Set (SpatialCoordinates d))),
      potEval v x = v ⟨x, hx⟩)
    (aw : ℕ → Ω → C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ) → PositiveCoefficient Q)
    (haw : ∀ n ω v, ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
      (aw n ω v).val x = Real.exp (potEval v x) * (a n ω).val x)
    (E : Ω → DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : ∀ ω, DirichletForm.EnergyMeasure (E ω))
    (hGammaQ : ∀ ω u, u ∈ (E ω).domain →
      (Gamma ω).measure u (Q : Set (SpatialCoordinates d))ᶜ = 0)
    (R : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ) → Ω → DomainL2 Q → ℝ)
    (hR : ∀ v ω f, IsLUB {t : ℝ | ∃ u : DomainL2 Q, u ∈ (E ω).domain ∧
      t = 2 * inner ℝ f u - ∫ x in (Q : Set (SpatialCoordinates d)),
        Real.exp (potEval v x) ∂((Gamma ω).measure u)} (R v ω f))
    (catalog : ℕ → C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ))
    (hdense : DenseRange catalog) (hzero : catalog 0 = 0)
    (hdet : ∀ k : ℕ, ∀ f : DomainL2 Q,
      TendstoInMeasure P (fun n ω => inverseResponse S (aw n ω (catalog k))
        ((sobolevVolumeLoad f).comp S.space.subtypeL)) atTop (fun ω => R (catalog k) ω f))
    (hdetmeas : ∀ (k : ℕ) (n : ℕ) (f : DomainL2 Q),
      AEMeasurable (fun ω => inverseResponse S (aw n ω (catalog k))
        ((sobolevVolumeLoad f).comp S.space.subtypeL)) P)
    (hdetlim : ∀ (k : ℕ) (f : DomainL2 Q),
      AEMeasurable (fun ω => R (catalog k) ω f) P)
    (V : Ω → C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ))
    (hV : @Measurable Ω C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ)
      _ (borel C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ)) V) (m : ℕ) (f : Fin m → DomainL2 Q) :
    (∀ (epsilon : ℝ), 0 < epsilon → ∀ (delta : ℝ), 0 < delta →
      ∃ (K : Set C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ))
        (F : Finset ℕ) (sel : Ω → ℕ),
        IsCompact K ∧ Measurable sel ∧ (∀ ω, sel ω ∈ F) ∧
        P {ω | V ω ∉ K} ≤ ENNReal.ofReal epsilon ∧
        ∀ ω, V ω ∈ K → ‖V ω - catalog (sel ω)‖ ≤ delta) ∧
    (∀ (n : ℕ) (ω : Ω)
      (v w : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ)) (ε : ℝ),
      0 ≤ ε →
      (∀ x ∈ Q, |Real.exp (potEval v x) / Real.exp (potEval w x) - 1| ≤ ε) →
      ∀ u : S.space,
        (1 - ε) * responseForm S (aw n ω w) u u ≤ responseForm S (aw n ω v) u u ∧
        responseForm S (aw n ω v) u u ≤ (1 + ε) * responseForm S (aw n ω w) u u) ∧
    TendstoInMeasure P
      (fun n ω => (V ω, fun i : Fin m => inverseResponse S (aw n ω (V ω))
        ((sobolevVolumeLoad (f i)).comp S.space.subtypeL))) atTop
      (fun ω => (V ω, fun i : Fin m => R (V ω) ω (f i))) := by
  refine ⟨aux_rem_random_weights_selection Q P catalog hdense V hV,
    aux_rem_random_weights_form_comparison Q S a potEval aw haw, ?_⟩
  exact aux_rem_random_weights_pair P V _ _
    (aux_rem_random_weights_fin P _ _ (fun i =>
      aux_rem_random_weights_single Q P S a potEval hpotEval aw haw E Gamma R hR
        catalog hdense hzero hdet hdetlim V hV (f i)))

end Paper
