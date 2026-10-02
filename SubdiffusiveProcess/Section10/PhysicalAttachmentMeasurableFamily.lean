import SubdiffusiveProcess.Section10.PhysicalAttachmentMeasurableGraph
import MarkovProcess.Examples.Identity
open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess MarkovProcess.Semigroup Set
open scoped ENNReal NNReal ZeroAtInfty
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalAttachment

/-- Measurable transition integrals of the constructed reversible resolvent family.
The weak equation is used to place the actual resolvent on the proved analytic graph. -/
theorem pa_measurable_orbit {d : ℕ} {Theta : Type*} [MeasurableSpace Theta]
    [MeasurableSpace C(Fin d → ℝ, ℝ)] [BorelSpace C(Fin d → ℝ, ℝ)]
    (Pot : Theta → C(Fin d → ℝ, ℝ)) (hPot : Measurable Pot)
    (Q : Theta → SubMarkovKernelSemigroup (Fin d → ℝ))
    (hQ : ∀ theta, (Q theta).IsFellerKernelSemigroup) (G : Set Theta)
    (hG : ∀ theta ∈ G, ∃ D : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum
        (Fin d → ℝ),
      SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent
        (fun x => Real.exp (Pot theta x)) (fun x => Real.exp (Pot theta x)) D ∧
      ∀ (mu : PositiveShift) (f : C₀(Fin d → ℝ, ℝ)) (x : Fin d → ℝ),
        D.solution mu f x = ∫ t in Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
          kernelIntegral (Q theta (Real.toNNReal t)) f x)
    (t : NNReal) (f : C₀(Fin d → ℝ, ℝ)) (x : Fin d → ℝ) :
    Measurable fun theta : G => kernelIntegral (Q theta t) f x := by
  letI : MeasurableSpace C₀(Fin d → ℝ, ℝ) := borel _
  haveI : BorelSpace C₀(Fin d → ℝ, ℝ) := ⟨rfl⟩
  haveI := pa_c0_secondCountable d
  have hR : ∀ (mu : PositiveShift) (g : C₀(Fin d → ℝ, ℝ)),
      Measurable fun theta : G => (hQ theta).c0Semigroup.toContractiveResolvent.operator mu g := by
    intro mu g
    refine pa_measurable_section (a := 1) (z := 0) one_pos mu.2 g Pot hPot G
      (fun theta => (hQ theta).c0Semigroup.toContractiveResolvent.operator mu g) ?_
    intro theta htheta
    obtain ⟨D, hweak, hlap⟩ := hG theta htheta
    have heq : (hQ theta).c0Semigroup.toContractiveResolvent.operator mu g = D.solution mu g := by
      ext y
      rw [StronglyContinuousContractionSemigroup.toContractiveResolvent_operator,
        SubMarkovKernelSemigroup.IsFellerKernelSemigroup.resolvent_apply_apply, hlap]
    dsimp only
    rw [heq]
    intro k
    have h := pa_cubeRel_of_weak hweak mu g k
    simpa only [pa_coefFun, pa_rhoFun, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk, sub_zero, one_mul] using h
  have hgen := pa_measurable_generated
    (fun theta : G => (hQ theta).c0Semigroup.toContractiveResolvent) hR t f
  simp only [StronglyContinuousContractionSemigroup.generatedSemigroup_toContractiveResolvent] at hgen
  exact (pa_c0_continuous_eval x).measurable.comp hgen
open Classical in
/-- **Joint measurability of the patched transition integrals.** Environment measurability on a
measurable set, together with joint continuity of Feller orbits in time and state, gives joint
measurability of the family patched by the identity off that set. -/
theorem pa_measurable_patched_integral {d : ℕ} {Theta : Type*} [MeasurableSpace Theta]
    (Q : Theta → SubMarkovKernelSemigroup ((Fin d → ℝ)))
    (hQ : ∀ omega, (Q omega).IsFellerKernelSemigroup) {G : Set (Theta)}
    (hGm : MeasurableSet G)
    (horbit : ∀ (t : NNReal) (f : C₀((Fin d → ℝ), ℝ)) (x : (Fin d → ℝ)),
      Measurable fun omega : G ↦ kernelIntegral (Q omega t) f x)
    (f : C₀((Fin d → ℝ), ℝ)) :
    Measurable fun q : Theta × (NNReal × (Fin d → ℝ)) ↦
      if q.1 ∈ G then kernelIntegral (Q q.1 q.2.1) f q.2.2 else f q.2.2 := by
  classical
  let u : NNReal × (Fin d → ℝ) → Theta → ℝ := fun tx omega ↦
    if omega ∈ G then kernelIntegral (Q omega tx.1) f tx.2 else f tx.2
  have hcont : ∀ omega, Continuous fun tx : NNReal × (Fin d → ℝ) ↦ u tx omega := by
    intro omega
    by_cases h : omega ∈ G
    · simp only [u, h, if_true]
      exact (hQ omega).c0Semigroup.continuous_apply_apply f
    · simp only [u, h, if_false]
      exact f.continuous.comp continuous_snd
  have hmeas : ∀ tx, Measurable (u tx) := by
    intro tx
    refine measurable_of_restrict_of_restrict_compl hGm ?_ ?_
    · have h := horbit tx.1 f tx.2
      have heq : G.restrict (u tx) = fun omega : G ↦ kernelIntegral (Q omega tx.1) f tx.2 := by
        funext omega
        simp [u, Set.restrict, omega.2]
      rw [heq]
      exact h
    · have heq : Gᶜ.restrict (u tx) = fun _ : (Gᶜ : Set (Theta)) ↦ f tx.2 := by
        funext omega
        have : (omega : Theta) ∉ G := omega.2
        simp [u, Set.restrict, this]
      rw [heq]
      exact measurable_const
  have hjoint := measurable_uncurry_of_continuous_of_measurable hcont hmeas
  exact hjoint.comp (measurable_snd.prodMk measurable_fst)





open scoped ZeroAtInfty

/-- A measurable full-measure set on which an almost-sure property holds everywhere. -/
theorem pa_exists_measurable_good
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {p : Ω → Prop} (h : ∀ᵐ ω ∂μ, p ω) :
    ∃ G : Set Ω, MeasurableSet G ∧ (∀ᵐ ω ∂μ, ω ∈ G) ∧ ∀ ω ∈ G, p ω := by
  refine ⟨(toMeasurable μ {ω | ¬ p ω})ᶜ, (measurableSet_toMeasurable _ _).compl, ?_, ?_⟩
  · rw [ae_iff] at h ⊢
    simp only [Set.mem_compl_iff, not_not, Set.setOf_mem_eq, measure_toMeasurable]
    exact h
  · intro ω hω
    by_contra hp
    exact hω (subset_toMeasurable _ _ hp)

/-- The Feller family patched by the identity semigroup off a measurable event, jointly measurable
in environment, time and starting point once its orbits are measurable on the event. -/
def pa_patched {d : ℕ} {Theta : Type*} [MeasurableSpace Theta]
    (Q : Theta → SubMarkovKernelSemigroup ((Fin d → ℝ)))
    (hQ : ∀ omega, (Q omega).IsFellerKernelSemigroup) {G : Set (Theta)}
    (hGm : MeasurableSet G)
    (horbit : ∀ (t : NNReal) (f : C₀((Fin d → ℝ), ℝ)) (x : (Fin d → ℝ)),
      Measurable fun omega : G ↦ kernelIntegral (Q omega t) f x) :
    ParameterizedSubMarkovKernelSemigroup (Theta) ((Fin d → ℝ)) := by
  classical
  exact {
  kernel omega t := if omega ∈ G then Q omega t else Kernel.id
  measurable_kernel := by
    let μq : Theta × (NNReal × (Fin d → ℝ)) → Measure ((Fin d → ℝ)) :=
      fun q ↦ (if q.1 ∈ G then Q q.1 q.2.1 else Kernel.id) q.2.2
    haveI hfin : ∀ q, IsFiniteMeasure (μq q) := by
      intro q
      by_cases h : q.1 ∈ G
      · haveI : IsFiniteKernel (Q q.1 q.2.1) := ((Q q.1).isSubMarkovKernel q.2.1).isFiniteKernel
        simp only [μq, h, if_true]
        infer_instance
      · simp only [μq, h, if_false, Kernel.id_apply]
        infer_instance
    haveI : ∀ q, (μq q).Regular := fun q ↦ inferInstance
    refine measurable_measure_of_measurable_integral_compactlySupported μq fun f ↦ ?_
    let f₀ : C₀((Fin d → ℝ), ℝ) :=
      PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f
    have hf₀ : ∀ y, f₀ y = f y := fun y ↦
      PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply f y
    have hmeas := pa_measurable_patched_integral
      Q hQ hGm horbit f₀
    have heq : (fun q ↦ ∫ x, f x ∂μq q) = fun q : Theta × (NNReal × (Fin d → ℝ)) ↦
        if q.1 ∈ G then kernelIntegral (Q q.1 q.2.1) f₀ q.2.2 else f₀ q.2.2 := by
      funext q
      by_cases h : q.1 ∈ G
      · simp only [μq, h, if_true, kernelIntegral, hf₀]
      · simp only [μq, h, if_false, Kernel.id_apply, hf₀]
        exact integral_dirac' _ _ f.continuous.stronglyMeasurable
    rw [heq]
    convert hmeas using 2
  kernel_zero omega := by
    by_cases h : omega ∈ G <;> simp [h, (Q omega).kernel_zero]
  kernel_add omega s t := by
    by_cases h : omega ∈ G
    · simp [h, (Q omega).kernel_add s t]
    · simp [h]
  isSubMarkovKernel omega t := by
    by_cases h : omega ∈ G
    · simpa [h] using (Q omega).isSubMarkovKernel t
    · simpa [h] using (IsSubMarkovKernel.id : IsSubMarkovKernel (Kernel.id :
        Kernel ((Fin d → ℝ)) ((Fin d → ℝ))))
  }

theorem pa_patched_of_mem {d : ℕ} {Theta : Type*} [MeasurableSpace Theta]
    (Q : Theta → SubMarkovKernelSemigroup ((Fin d → ℝ)))
    (hQ : ∀ omega, (Q omega).IsFellerKernelSemigroup) {G : Set (Theta)}
    (hGm : MeasurableSet G)
    (horbit : ∀ (t : NNReal) (f : C₀((Fin d → ℝ), ℝ)) (x : (Fin d → ℝ)),
      Measurable fun omega : G ↦ kernelIntegral (Q omega t) f x)
    {omega : Theta} (h : omega ∈ G) :
    (pa_patched Q hQ hGm horbit
      ).toSubMarkovKernelSemigroup omega = Q omega := by
  apply SubMarkovKernelSemigroup.ext
  intro t
  simp [pa_patched, h]

theorem pa_patched_of_not_mem {d : ℕ} {Theta : Type*} [MeasurableSpace Theta]
    (Q : Theta → SubMarkovKernelSemigroup ((Fin d → ℝ)))
    (hQ : ∀ omega, (Q omega).IsFellerKernelSemigroup) {G : Set (Theta)}
    (hGm : MeasurableSet G)
    (horbit : ∀ (t : NNReal) (f : C₀((Fin d → ℝ), ℝ)) (x : (Fin d → ℝ)),
      Measurable fun omega : G ↦ kernelIntegral (Q omega t) f x)
    {omega : Theta} (h : omega ∉ G) :
    (pa_patched Q hQ hGm horbit
      ).toSubMarkovKernelSemigroup omega = MarkovProcess.idSemigroup := by
  apply SubMarkovKernelSemigroup.ext
  intro t
  simp [pa_patched, h, MarkovProcess.idSemigroup]


end SubdiffusiveProcess.Section10.PhysicalAttachment
