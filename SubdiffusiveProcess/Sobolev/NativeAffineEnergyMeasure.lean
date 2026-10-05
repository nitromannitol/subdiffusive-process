module

public import SubdiffusiveProcess.Sobolev.NativeHarmonicMinimum

@[expose] public section

/-! Native affine harmonic functions carry the same energy measure as the killed graph minimizer.
All identities concern one fixed coefficient and do not assert a limiting or moment bound. -/
open MeasureTheory Set TopologicalSpace Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped NNReal BigOperators
namespace SubdiffusiveProcess
noncomputable section

/-- A native harmonic function with affine trace is the canonical affine graph minimizer. -/
theorem native_affine_harmonic_minimizer_eq
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Q : Set (SpatialCoordinates d)))]
    (hQ : Bornology.IsBounded (Q : Set (SpatialCoordinates d)))
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph Q,
      ‖w.val.1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Q) w‖)
    (a : PositiveCoefficient Q) (c : SpatialCoordinates d → ℝ)
    (hc : (fun x => a.val x) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] c)
    (beta v : H1Function (Q : Set (SpatialCoordinates d))) (p : Fin d → ℝ)
    (hbeta : beta.toFun =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
      fun x => ∑ i, p i * x i)
    (htrace : HasZeroTraceDifferenceOn (Q : Set (SpatialCoordinates d)) v beta)
    (hharm : IsWeaklyHarmonicOn c (Q : Set (SpatialCoordinates d)) v) :
    (⟨sobolevDataOfH1 v, sobolevDataOfH1_mem_weak v⟩ : weakSobolevGraph Q) =
      dirichletMinimizer (killedResponseSpace hP) a (affineSobolev hQ p 0) := by
  have hb : (⟨sobolevDataOfH1 beta, sobolevDataOfH1_mem_weak beta⟩ : weakSobolevGraph Q) =
      affineSobolev hQ p 0 := by
    apply Subtype.ext
    exact sobolevDataOfH1_eq_affine_of_ae hQ beta p 0
      (by simpa only [affineSlope_apply, add_zero] using hbeta)
  rw [native_boundary_minimizer_eq hP a c hc beta v htrace
    (native_harmonic_energy_eq_infimum a c hc beta v htrace hharm).le, hb]

/-- Native and graph affine minimizers define identical coefficient energy measures. -/
theorem native_affine_harmonic_energyMeasure_eq
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Q : Set (SpatialCoordinates d)))]
    (hQ : Bornology.IsBounded (Q : Set (SpatialCoordinates d)))
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph Q,
      ‖w.val.1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Q) w‖)
    (a : PositiveCoefficient Q) (c : SpatialCoordinates d → ℝ)
    (hc : (fun x => a.val x) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] c)
    (beta v : H1Function (Q : Set (SpatialCoordinates d))) (p : Fin d → ℝ)
    (hbeta : beta.toFun =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
      fun x => ∑ i, p i * x i)
    (htrace : HasZeroTraceDifferenceOn (Q : Set (SpatialCoordinates d)) v beta)
    (hharm : IsWeaklyHarmonicOn c (Q : Set (SpatialCoordinates d)) v) :
    (volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
      (fun x => ENNReal.ofReal (c x * ∑ i : Fin d, (v.grad x i) ^ 2)) =
    (volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
      (fun x => ENNReal.ofReal (a.val x * ∑ i : Fin d,
        ((dirichletMinimizer (killedResponseSpace hP) a (affineSobolev hQ p 0)).val.2 i x) ^ 2)) := by
  have hv := congrArg Subtype.val (native_affine_harmonic_minimizer_eq hQ hP a c hc beta v p
    hbeta htrace hharm)
  rw [← hv]
  apply withDensity_congr_ae
  filter_upwards [hc, ae_all_iff.mpr (fun i => sobolevDataOfH1_snd_coeFn v i)] with x hx hgrad
  rw [hx]
  congr 2
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun y : ℝ => y ^ 2) (hgrad i).symm)

/-- Restricting a padded native affine harmonic energy measure gives the observation-cell graph measure. -/
theorem padded_native_affine_energyMeasure_restrict
    {d : ℕ} {Q q : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (q : Set (SpatialCoordinates d)))]
    (hqq : (q : Set (SpatialCoordinates d)) ⊆ Q)
    (hq : Bornology.IsBounded (q : Set (SpatialCoordinates d)))
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph q,
      ‖w.val.1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph q) w‖)
    (aQ : PositiveCoefficient Q) (aq : PositiveCoefficient q) (c : SpatialCoordinates d → ℝ)
    (hQ : (fun x => aQ.val x) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] c)
    (hc : (fun x => aq.val x) =ᵐ[volume.restrict (q : Set (SpatialCoordinates d))] c)
    (v : H1Function (Q : Set (SpatialCoordinates d))) (w : SobolevData Q)
    (hw : w = sobolevDataOfH1 v)
    (beta : H1Function (q : Set (SpatialCoordinates d))) (p : Fin d → ℝ)
    (hbeta : beta.toFun =ᵐ[volume.restrict (q : Set (SpatialCoordinates d))]
      fun x => ∑ i, p i * x i)
    (htrace : HasZeroTraceDifferenceOn (q : Set (SpatialCoordinates d))
      (v.restrict q.isOpen hqq) beta)
    (hharm : IsWeaklyHarmonicOn c (q : Set (SpatialCoordinates d)) (v.restrict q.isOpen hqq)) :
    ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
      (fun x => ENNReal.ofReal (aQ.val x * ∑ i : Fin d, (w.2 i x) ^ 2))).restrict q =
    (volume.restrict (q : Set (SpatialCoordinates d))).withDensity
      (fun x => ENNReal.ofReal (aq.val x * ∑ i : Fin d,
        ((dirichletMinimizer (killedResponseSpace hP) aq (affineSobolev hq p 0)).val.2 i x) ^ 2)) := by
  rw [restrict_withDensity q.isOpen.measurableSet, Measure.restrict_restrict_of_subset hqq]
  rw [← native_affine_harmonic_energyMeasure_eq hq hP aq c hc beta
    (v.restrict q.isOpen hqq) p hbeta htrace hharm]
  apply withDensity_congr_ae
  have hgrad := ae_all_iff.mpr (fun i => sobolevDataOfH1_snd_coeFn v i)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hqq hQ,
    ae_restrict_of_ae_restrict_of_subset hqq hgrad] with x hx hg
  rw [hw, hx]
  congr 2
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun y : ℝ => y ^ 2) (hg i))

end
end SubdiffusiveProcess
