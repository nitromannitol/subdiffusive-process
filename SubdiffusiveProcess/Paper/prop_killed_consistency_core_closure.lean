module

public import SubdiffusiveProcess.Paper.prop_regularity
public import SubdiffusiveProcess.Paper.prop_killed_consistency_zero_extension
public import SubdiffusiveProcess.Paper.prop_killed_consistency_cutoff_localization
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Sobolev.EvenReflectionGraph
public import SubdiffusiveProcess.VariationalResponses.OddExtension

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper



theorem prop_killed_consistency_core_closure
    (d : ℕ) (_hd : 2 ≤ d)
    (zQ zq : SpatialCoordinates d) (R r : ℝ) (hR0 : 0 < R) (hr0 : 0 < r)
    (hqQ : (centeredCube zq r hr0 : Set (SpatialCoordinates d)) ⊆
      (centeredCube zQ R hR0 : Set (SpatialCoordinates d)))
    (EQ : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))))
    (Eq : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (centeredCube zq r hr0 : Set (SpatialCoordinates d))))
    (hqRegular : ∃ C : Set (DomainL2 (centeredCube zq r hr0)),
      _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn Eq
        (centeredCube zq r hr0 : Set (SpatialCoordinates d)) C)
    (hLower : ∀ u : DomainL2 (centeredCube zq r hr0), u ∈ Eq.domain →
      (EQ.energy (zeroExtensionLp hqQ u) : EReal) ≤ (Eq.energy u : EReal))
    (hUpper : ∀ w : DomainL2 (centeredCube zQ R hR0), w ∈ EQ.domain →
      (∃ wc : SpatialCoordinates d → ℝ, Continuous wc ∧
        HasCompactSupport wc ∧
        tsupport wc ⊆ (centeredCube zq r hr0 : Set (SpatialCoordinates d)) ∧
        (w : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))] wc) →
      ∃ wq : DomainL2 (centeredCube zq r hr0),
        wq ∈ Eq.domain ∧ zeroExtensionLp hqQ wq = w ∧
        (Eq.energy wq : EReal) ≤ (EQ.energy w : EReal)) :
    ∀ u : DomainL2 (centeredCube zq r hr0), u ∈ Eq.domain →
      zeroExtensionLp hqQ u ∈ EQ.domain ∧
      (EQ.energy (zeroExtensionLp hqQ u) : EReal) = (Eq.energy u : EReal) ∧
      (∀ v : DomainL2 (centeredCube zq r hr0), v ∈ Eq.domain →
        EQ.form (zeroExtensionLp hqQ u) (zeroExtensionLp hqQ v) =
          Eq.form u v) := by
  obtain ⟨C, hC⟩ := hqRegular
  have hmem : ∀ f : DomainL2 (centeredCube zq r hr0), f ∈ Eq.domain →
      zeroExtensionLp hqQ f ∈ EQ.domain := by
    intro f hf
    have hlt : Eq.energy f < ⊤ := by
      rw [Eq.energy_of_mem hf]
      exact EReal.coe_lt_top _
    exact EQ.mem_domain_of_energy_lt_top (lt_of_le_of_lt (hLower f hf) hlt)
  have zesub : ∀ f g : DomainL2 (centeredCube zq r hr0),
      zeroExtensionLp hqQ (f - g) = zeroExtensionLp hqQ f - zeroExtensionLp hqQ g :=
    fun f g => zeroExtensionLp_sub hqQ f g
  have zeadd : ∀ f g : DomainL2 (centeredCube zq r hr0),
      zeroExtensionLp hqQ (f + g) = zeroExtensionLp hqQ f + zeroExtensionLp hqQ g := by
    intro f g
    have h := zeroExtensionLp_sub hqQ (f + g) g
    rw [add_sub_cancel_right] at h
    rw [h]
    abel
  have hinj : ∀ f g : DomainL2 (centeredCube zq r hr0),
      zeroExtensionLp hqQ f = zeroExtensionLp hqQ g → f = g := by
    intro f g hfg
    have h0 : zeroExtensionLp hqQ (f - g) = 0 := by
      rw [zesub f g, hfg, sub_self]
    have hn : ‖f - g‖ = 0 := by
      have h2 := norm_zeroExtensionLp hqQ (f - g)
      rw [h0, norm_zero] at h2
      exact h2.symm
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  have hRev : ∀ f : DomainL2 (centeredCube zq r hr0), f ∈ Eq.domain →
      _root_.SubdiffusiveProcess.DirichletForm.HasCoreRep
        (volume.restrict (centeredCube zq r hr0 : Set (SpatialCoordinates d)))
        (centeredCube zq r hr0 : Set (SpatialCoordinates d)) f →
      (Eq.energy f : EReal) ≤ (EQ.energy (zeroExtensionLp hqQ f) : EReal) := by
    intro f hf hrep
    obtain ⟨fc, hfc, hfcs, hfsub, hfae⟩ := hrep
    have hbig : ∀ᵐ x ∂(volume.restrict
        (centeredCube zQ R hR0 : Set (SpatialCoordinates d))),
        x ∈ (centeredCube zq r hr0 : Set (SpatialCoordinates d)) → f x = fc x :=
      ae_restrict_of_ae (s := (centeredCube zQ R hR0 : Set (SpatialCoordinates d)))
        ((ae_restrict_iff' (centeredCube zq r hr0).isOpen.measurableSet).mp hfae)
    have hze : (zeroExtensionLp hqQ f : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))] fc := by
      filter_upwards [zeroExtensionLp_coeFn hqQ f, hbig] with x hx hb
      rw [hx]
      by_cases hxq : x ∈ (centeredCube zq r hr0 : Set (SpatialCoordinates d))
      · rw [Set.indicator_of_mem hxq]
        exact hb hxq
      · rw [Set.indicator_of_notMem hxq]
        exact (image_eq_zero_of_notMem_tsupport (fun h => hxq (hfsub h))).symm
    obtain ⟨fq, _hfqm, hfqZ, hfqle⟩ :=
      hUpper (zeroExtensionLp hqQ f) (hmem f hf) ⟨fc, hfc, hfcs, hfsub, hze⟩
    have hfqf : fq = f := hinj fq f hfqZ
    rwa [hfqf] at hfqle
  have hcore : ∀ f : DomainL2 (centeredCube zq r hr0), f ∈ Eq.domain →
      _root_.SubdiffusiveProcess.DirichletForm.HasCoreRep
        (volume.restrict (centeredCube zq r hr0 : Set (SpatialCoordinates d)))
        (centeredCube zq r hr0 : Set (SpatialCoordinates d)) f →
      EQ.form (zeroExtensionLp hqQ f) (zeroExtensionLp hqQ f) = Eq.form f f := by
    intro f hf hrep
    have hE : (EQ.energy (zeroExtensionLp hqQ f) : EReal) = (Eq.energy f : EReal) :=
      le_antisymm (hLower f hf) (hRev f hf hrep)
    rw [EQ.energy_of_mem (hmem f hf), Eq.energy_of_mem hf] at hE
    exact EReal.coe_injective hE
  have hrep_sub : ∀ f g : DomainL2 (centeredCube zq r hr0),
      _root_.SubdiffusiveProcess.DirichletForm.HasCoreRep
        (volume.restrict (centeredCube zq r hr0 : Set (SpatialCoordinates d)))
        (centeredCube zq r hr0 : Set (SpatialCoordinates d)) f →
      _root_.SubdiffusiveProcess.DirichletForm.HasCoreRep
        (volume.restrict (centeredCube zq r hr0 : Set (SpatialCoordinates d)))
        (centeredCube zq r hr0 : Set (SpatialCoordinates d)) g →
      _root_.SubdiffusiveProcess.DirichletForm.HasCoreRep
        (volume.restrict (centeredCube zq r hr0 : Set (SpatialCoordinates d)))
        (centeredCube zq r hr0 : Set (SpatialCoordinates d)) (f - g) := by
    intro f g hf hg
    have h := hf.add (hg.smul (-1))
    simpa [sub_eq_add_neg] using h
  have polarQ : ∀ (a b : DomainL2 (centeredCube zQ R hR0)),
      a ∈ EQ.domain → b ∈ EQ.domain →
      EQ.form a b = (1 / 4) *
        (EQ.form (a + b) (a + b) - EQ.form (a - b) (a - b)) := by
    intro a b ha hb
    have hsum : EQ.form (a + b) (a + b) =
        EQ.form a a + 2 * EQ.form a b + EQ.form b b := EQ.form_add_self ha hb
    have hdif : EQ.form (a - b) (a - b) =
        EQ.form a a - 2 * EQ.form a b + EQ.form b b := by
      have h1 := EQ.form_sub_left ha hb (EQ.domain.sub_mem ha hb)
      have h2 := EQ.form_sub_right ha ha hb
      have h3 := EQ.form_sub_right hb ha hb
      have h4 := EQ.form_symm b hb a ha
      rw [h1, h2, h3, h4]
      ring
    rw [hsum, hdif]
    ring
  have polarq : ∀ (a b : DomainL2 (centeredCube zq r hr0)),
      a ∈ Eq.domain → b ∈ Eq.domain →
      Eq.form a b = (1 / 4) *
        (Eq.form (a + b) (a + b) - Eq.form (a - b) (a - b)) := by
    intro a b ha hb
    have hsum : Eq.form (a + b) (a + b) =
        Eq.form a a + 2 * Eq.form a b + Eq.form b b := Eq.form_add_self ha hb
    have hdif : Eq.form (a - b) (a - b) =
        Eq.form a a - 2 * Eq.form a b + Eq.form b b := by
      have h1 := Eq.form_sub_left ha hb (Eq.domain.sub_mem ha hb)
      have h2 := Eq.form_sub_right ha ha hb
      have h3 := Eq.form_sub_right hb ha hb
      have h4 := Eq.form_symm b hb a ha
      rw [h1, h2, h3, h4]
      ring
    rw [hsum, hdif]
    ring
  have hgen : ∀ f : DomainL2 (centeredCube zq r hr0), f ∈ Eq.domain →
      EQ.form (zeroExtensionLp hqQ f) (zeroExtensionLp hqQ f) = Eq.form f f := by
    intro f hf
    have hw : ∀ n : ℕ, ∃ w ∈ C, Eq.energyNormSq (f - w) < 1 / (n + 1 : ℝ) :=
      fun n => hC.denseEnergy f hf (1 / (n + 1 : ℝ)) (by positivity)
    choose w hwC hwE using hw
    have hwdom : ∀ n, w n ∈ Eq.domain :=
      fun n => (hC.memCoreOn (w n) (hwC n)).mem_domain
    have hwrep : ∀ n, _root_.SubdiffusiveProcess.DirichletForm.HasCoreRep
        (volume.restrict (centeredCube zq r hr0 : Set (SpatialCoordinates d)))
        (centeredCube zq r hr0 : Set (SpatialCoordinates d)) (w n) :=
      fun n => (hC.memCoreOn (w n) (hwC n)).hasCoreRep
    have hzero : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hlimE : Tendsto (fun n => Eq.energyNormSq (f - w n)) atTop (𝓝 0) :=
      squeeze_zero
        (fun n => Eq.energyNormSq_nonneg (Eq.domain.sub_mem hf (hwdom n)))
        (fun n => le_of_lt (hwE n)) hzero
    have hlimnorm : Tendsto (fun n => ‖f - w n‖) atTop (𝓝 0) := by
      have hsqrt : Tendsto
          (fun n => Real.sqrt (Eq.energyNormSq (f - w n))) atTop (𝓝 0) := by
        have hc : Tendsto Real.sqrt (𝓝 0) (𝓝 0) := by
          simpa using Real.continuous_sqrt.tendsto 0
        exact hc.comp hlimE
      refine squeeze_zero (fun n => norm_nonneg _) ?_ hsqrt
      intro n
      rw [← Real.sqrt_sq (norm_nonneg (f - w n))]
      exact Real.sqrt_le_sqrt ((Eq.sq_norm_le_energyNormSq
        (Eq.domain.sub_mem hf (hwdom n))))
    have hL2 : Tendsto (fun n => zeroExtensionLp hqQ (w n)) atTop
        (𝓝 (zeroExtensionLp hqQ f)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      have hd : ∀ n, dist (zeroExtensionLp hqQ (w n))
          (zeroExtensionLp hqQ f) = ‖f - w n‖ := by
        intro n
        rw [dist_eq_norm, ← zesub (w n) f]
        simpa only [norm_sub_rev] using! (norm_zeroExtensionLp hqQ (w n - f))
      simpa only [hd] using hlimnorm
    have hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ r ≥ N,
        EQ.form (zeroExtensionLp hqQ (w p) - zeroExtensionLp hqQ (w r))
          (zeroExtensionLp hqQ (w p) - zeroExtensionLp hqQ (w r)) < ε := by
      intro ε hε
      have hδ : Tendsto (fun n => Real.sqrt (Eq.energyNormSq (f - w n))) atTop (𝓝 0) := by
        have h := (Real.continuous_sqrt.tendsto 0).comp hlimE
        simpa only [Function.comp_apply, Real.sqrt_zero] using! h
      have hev : ∀ᶠ n in atTop,
          Real.sqrt (Eq.energyNormSq (f - w n)) < Real.sqrt ε / 2 :=
        (tendsto_order.1 hδ).2 _ (by positivity)
      obtain ⟨N, hN⟩ := eventually_atTop.1 hev
      refine ⟨N, fun p hp r hr => ?_⟩
      have hd1 : Real.sqrt (Eq.energyNormSq (f - w p)) < Real.sqrt ε / 2 := hN p hp
      have hd2 : Real.sqrt (Eq.energyNormSq (f - w r)) < Real.sqrt ε / 2 := hN r hr
      rw [← zesub (w p) (w r),
        hcore (w p - w r) (Eq.domain.sub_mem (hwdom p) (hwdom r))
          (hrep_sub (w p) (w r) (hwrep p) (hwrep r))]
      have htri : Real.sqrt (Eq.energyNormSq (w p - w r)) ≤
          Real.sqrt (Eq.energyNormSq (f - w p)) + Real.sqrt (Eq.energyNormSq (f - w r)) := by
        have h := Eq.sqrt_energyNormSq_sub_le (hwdom p) hf (hwdom r)
        rwa [Eq.energyNormSq_sub_comm (hwdom p) hf] at h
      have h2 : Eq.form (w p - w r) (w p - w r) ≤
          (Real.sqrt (Eq.energyNormSq (f - w p)) +
            Real.sqrt (Eq.energyNormSq (f - w r))) ^ 2 := by
        refine (Eq.form_le_energyNormSq).trans ?_
        rw [← Real.sq_sqrt (Eq.energyNormSq_nonneg
          (Eq.domain.sub_mem (hwdom p) (hwdom r)))]
        exact (sq_le_sq₀
          (Real.sqrt_nonneg (Eq.energyNormSq (w p - w r)))
          (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2 htri
      have h3 : (Real.sqrt (Eq.energyNormSq (f - w p)) +
          Real.sqrt (Eq.energyNormSq (f - w r))) ^ 2 < ε := by
        have hs : Real.sqrt (Eq.energyNormSq (f - w p)) +
            Real.sqrt (Eq.energyNormSq (f - w r)) < Real.sqrt ε := by
          linarith [hd1, hd2]
        have hnn : 0 ≤ Real.sqrt (Eq.energyNormSq (f - w p)) +
            Real.sqrt (Eq.energyNormSq (f - w r)) :=
          add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        rw [← Real.sq_sqrt (le_of_lt hε)]
        exact (sq_lt_sq₀ hnn (Real.sqrt_nonneg ε)).2 hs
      exact lt_of_le_of_lt h2 h3
    have hWmem : ∀ n, zeroExtensionLp hqQ (w n) ∈ EQ.domain :=
      fun n => hmem (w n) (hwdom n)
    obtain ⟨_, hconv⟩ :=
      _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.mem_domain_of_tendsto_of_formCauchy EQ
        (fun n => zeroExtensionLp hqQ (w n)) hWmem (zeroExtensionLp hqQ f) hL2 hcauchy
    have hEQconv : Tendsto
        (fun n => EQ.form (zeroExtensionLp hqQ (w n)) (zeroExtensionLp hqQ (w n))) atTop
        (𝓝 (EQ.form (zeroExtensionLp hqQ f) (zeroExtensionLp hqQ f))) :=
      _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.tendsto_form_self_of_tendsto_energyNormSq EQ hWmem
        (hmem f hf) hconv
    have hlimE' : Tendsto (fun n => Eq.energyNormSq (w n - f)) atTop (𝓝 0) := by
      have hsub : (fun n => Eq.energyNormSq (w n - f)) =
          fun n => Eq.energyNormSq (f - w n) := by
        funext n
        exact (Eq.energyNormSq_sub_comm hf (hwdom n)).symm
      rw [hsub]
      exact hlimE
    have hEqconv : Tendsto (fun n => Eq.form (w n) (w n)) atTop (𝓝 (Eq.form f f)) :=
      _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.tendsto_form_self_of_tendsto_energyNormSq Eq hwdom hf hlimE'
    have hfun : (fun n => EQ.form (zeroExtensionLp hqQ (w n))
        (zeroExtensionLp hqQ (w n))) = fun n => Eq.form (w n) (w n) :=
      funext (fun n => hcore (w n) (hwdom n) (hwrep n))
    rw [hfun] at hEQconv
    exact tendsto_nhds_unique hEQconv hEqconv
  intro u hu
  refine ⟨hmem u hu, ?_, ?_⟩
  · rw [EQ.energy_of_mem (hmem u hu), Eq.energy_of_mem hu, hgen u hu]
  · intro v hv
    rw [polarQ (zeroExtensionLp hqQ u) (zeroExtensionLp hqQ v)
      (hmem u hu) (hmem v hv), ← zeadd u v, ← zesub u v,
      hgen (u + v) (Eq.domain.add_mem hu hv),
      hgen (u - v) (Eq.domain.sub_mem hu hv), polarq u v hu hv]

end SubdiffusiveProcess.Paper

