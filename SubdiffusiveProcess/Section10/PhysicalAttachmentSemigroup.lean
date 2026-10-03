module

public import SubdiffusiveProcess.Section10.PhysicalAttachmentCoefficients
public import SubdiffusiveProcess.Section10.PhysicalAttachmentMeasurableFamily
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationResolventSupport

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess Homogenization Set
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open scoped ENNReal NNReal ZeroAtInfty
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalAttachment

/-- Actual weak resolvents, conservativity and continuous-path support, simultaneously
for all finite cutoffs and top. The reversible growth estimate supplies the construction. -/
theorem ae_exists_physical_resolvents {d : ℕ} [NeZero d] (M : GMCModel d) :
    ∀ᵐ omega ∂(physicalLaw M).toMeasure, ∀ L : WithTop ℕ,
      ∃ D : C0ResolventDatum (Vec d), ∃ hdense : ∀ mu, DenseRange (D.operator mu),
        IsWeakEllipticResolvent (coefficientAt M L omega) (coefficientAt M L omega) D ∧
        ∃ hcons : (D.fellerKernelSemigroup hdense).IsConservative,
          Kernel.IsSupportedOnContinuousPaths
            (SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectory
              (D.fellerKernelSemigroup hdense) hcons
              DenseTime.enumeration DenseTime.castOrderEmbedding.toEmbedding) := by
  filter_upwards [ae_reversible_family_linearGrowth M] with omega homega
  obtain ⟨K, hK, hfamily⟩ := homega
  intro L
  have hmem : coefficientAt M L omega = aAnchored M omega ∨
      (∃ n : ℕ, coefficientAt M L omega = aCutoff M n omega.val) ∨
      (∃ n : ℕ, coefficientAt M L omega = anchoredCutoff M n omega.val) := by
    cases L with
    | top => exact Or.inl rfl
    | coe n => exact Or.inr (Or.inl ⟨n, rfl⟩)
  obtain ⟨hc, hpos, hgrowth⟩ := hfamily _ hmem
  let B := reversibleMassiveCubeBounds M L omega
  have hsolve := hasC0MassiveSolutionsOnCompactData_of_linearGrowth
    M L omega B hpos hK hgrowth
  let R := MassiveC0Resolvent.ofHasC0MassiveSolutions
    (hasC0MassiveSolutions_reversible_of_solvability M L omega hsolve)
  obtain ⟨D, hdense, hweak⟩ := exists_c0ResolventDatum_of_massiveC0Resolvent B R
    (hasStrongMassiveResolventLimit_of_hasDenseMassiveResolventRange B
      (hasDenseMassiveResolventRange_reversible M L omega) R)
  have hcons := isConservative_of_weakResolvent_linearGrowth B hc hc.continuous
    D hdense hweak (fun x => (hpos x).le) hK hgrowth
  exact ⟨D, hdense, hweak, hcons,
    supportedOnContinuousPaths_of_weakResolvent_linearGrowth B hc hc.continuous
      D hdense hweak (fun x => (hpos x).le) hcons hK hgrowth⟩

/-- A jointly measurable family of the actual reversible physical semigroups.
The exceptional complement is explicitly patched by the identity semigroup.
On one common full source event, every fibre is the constructed weak-resolvent
semigroup and its dense-time trajectory has continuous-path support at every start. -/
theorem exists_physical_semigroups {d : ℕ} [NeZero d]
    [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)] (M : GMCModel d) :
    ∃ P : WithTop ℕ → ParameterizedSubMarkovKernelSemigroup (AnchoredC11Sample d) (Vec d),
      ∃ hPcons : ∀ L, (P L).IsConservative,
      (∀ L omega, ((P L).toSubMarkovKernelSemigroup omega).IsFellerKernelSemigroup) ∧
      ∀ᵐ omega ∂(physicalLaw M).toMeasure, ∀ L : WithTop ℕ,
        ∃ D : C0ResolventDatum (Vec d), ∃ hdense : ∀ mu, DenseRange (D.operator mu),
          IsWeakEllipticResolvent (coefficientAt M L omega) (coefficientAt M L omega) D ∧
          (P L).toSubMarkovKernelSemigroup omega = D.fellerKernelSemigroup hdense ∧
          Kernel.IsSupportedOnContinuousPaths
            (SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectory
              ((P L).toSubMarkovKernelSemigroup omega) (hPcons L omega)
              DenseTime.enumeration DenseTime.castOrderEmbedding.toEmbedding) := by
  classical
  obtain ⟨G, hGm, hGae, hGgood⟩ :=
    pa_exists_measurable_good (ae_exists_physical_resolvents M)
  choose D hdense hweak hcons hsupport using
    (fun (omega : G) (L : WithTop ℕ) => hGgood omega.val omega.property L)
  let Q : WithTop ℕ → AnchoredC11Sample d → SubMarkovKernelSemigroup (Vec d) :=
    fun L omega => if h : omega ∈ G then
      (D ⟨omega, h⟩ L).fellerKernelSemigroup (hdense ⟨omega, h⟩ L)
      else MarkovProcess.idSemigroup
  have hQcons : ∀ L omega, (Q L omega).IsConservative := by
    intro L omega
    by_cases h : omega ∈ G
    · simpa only [Q, dif_pos h] using hcons ⟨omega, h⟩ L
    · simpa only [Q, dif_neg h] using MarkovProcess.isConservative_idSemigroup (alpha := Vec d)
  have hQf : ∀ L omega, (Q L omega).IsFellerKernelSemigroup := by
    intro L omega
    by_cases h : omega ∈ G
    · simpa only [Q, dif_pos h] using
        (D ⟨omega, h⟩ L).isFellerKernelSemigroup_fellerKernelSemigroup (hdense ⟨omega, h⟩ L)
    · simpa only [Q, dif_neg h] using MarkovProcess.isFellerKernelSemigroup_idSemigroup (alpha := Vec d)
  have horbit : ∀ (L : WithTop ℕ) (t : NNReal) (f : C₀(Vec d, ℝ)) (x : Vec d),
      Measurable fun omega : G => kernelIntegral (Q L omega t) f x := by
    intro L t f x
    refine pa_measurable_orbit (physicalPotential M L) (measurable_physicalPotential M L)
      (Q L) (hQf L) G ?_ t f x
    intro omega homega
    refine ⟨D ⟨omega, homega⟩ L, ?_, ?_⟩
    · simpa only [exp_physicalPotential] using hweak ⟨omega, homega⟩ L
    · intro mu g y
      simpa only [Q, dif_pos homega] using
        (D ⟨omega, homega⟩ L).solution_eq_laplace (hdense ⟨omega, homega⟩ L) mu g y
  let P := fun L => pa_patched (Q L) (hQf L) hGm (horbit L)
  have hPcons : ∀ L, (P L).IsConservative := by
    intro L omega
    by_cases h : omega ∈ G
    · rw [pa_patched_of_mem _ _ _ _ h]
      exact hQcons L omega
    · rw [pa_patched_of_not_mem _ _ _ _ h]
      exact MarkovProcess.isConservative_idSemigroup
  refine ⟨P, hPcons, ?_, ?_⟩
  · intro L omega
    by_cases h : omega ∈ G
    · rw [pa_patched_of_mem _ _ _ _ h]
      exact hQf L omega
    · rw [pa_patched_of_not_mem _ _ _ _ h]
      exact MarkovProcess.isFellerKernelSemigroup_idSemigroup
  · filter_upwards [hGae] with omega homega
    intro L
    refine ⟨D ⟨omega, homega⟩ L, hdense ⟨omega, homega⟩ L,
      hweak ⟨omega, homega⟩ L, ?_, ?_⟩
    · rw [pa_patched_of_mem _ _ _ _ homega]
      simp only [Q, dif_pos homega]
    · have heq : (P L).toSubMarkovKernelSemigroup omega =
          (D ⟨omega, homega⟩ L).fellerKernelSemigroup (hdense ⟨omega, homega⟩ L) := by
        rw [pa_patched_of_mem _ _ _ _ homega]
        simp only [Q, dif_pos homega]
      simpa only [heq] using hsupport ⟨omega, homega⟩ L

end SubdiffusiveProcess.Section10.PhysicalAttachment
