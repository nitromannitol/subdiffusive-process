import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceDecayFiniteCutoff
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceProviderCarrierOps




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Set Topology
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Section8
open scoped CompactlySupported

noncomputable section

variable {d : ℕ}

/-- A globally integrable function whose integrals over every centred cube are
bounded by `C` has global integral at most `C`. -/
theorem integral_le_of_forall_setIntegral_cube_le
    {h : Vec d → ℝ} (hint : Integrable h volume) {C : ℝ}
    (hcube : ∀ k : ℕ, ∫ x in cube d (k : ℤ), h x ∂volume ≤ C) :
    ∫ x, h x ∂volume ≤ C := by
  have hmeas : ∀ k : ℕ, MeasurableSet (cube d (k : ℤ)) := fun k ↦
    (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d
      (k : ℤ)).isOpen.measurableSet
  have hunion : IntegrableOn h (⋃ k : ℕ, cube d (k : ℤ)) volume := by
    rw [iUnion_cube_nat_eq_univ]
    simpa only [IntegrableOn, Measure.restrict_univ] using hint
  have htend :=
    tendsto_setIntegral_of_monotone (μ := volume) (f := h) hmeas
      monotone_cube_nat hunion
  rw [iUnion_cube_nat_eq_univ, Measure.restrict_univ] at htend
  exact le_of_tendsto htend (Filter.Eventually.of_forall hcube)

variable [NeZero d]



theorem exists_finiteCutoffWholeSpaceSolution_of_compactSupport_with_energy
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {t : ℝ} (ht : 0 < t) (f : C_c(Vec d, ℝ)) :
    ∃ u : WholeSpaceDivergenceResolventSolution
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) t f,
      (∫ x, u.toFun x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume) ∧
      (∫ x, SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
          vecNormSq (u.grad x) ∂volume ≤
        2⁻¹ * t⁻¹ * ∫ x, f x ^ 2 ∂volume) := by
  have hmu : 0 < t⁻¹ := inv_pos.mpr ht
  set mu : ℝ := t⁻¹ with hmuDef
  let B := finiteCutoffDivergenceMassiveCubeBounds M L omega
  obtain ⟨u, huMem, huL2, huLocal⟩ :=
    exists_localNormalizedMassiveWeakSolution_with_sharp_l2_and_energy
      B hmu f
  set C : ℝ := 2⁻¹ * mu * ∫ x, f x ^ 2 ∂volume with hCdef
  have huLocalBound : ∀ k : ℕ,
      ∃ uLocal : H1Function (cube d (k : ℤ)),
        uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
        IsMassiveWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
          (fun _ ↦ (1 : ℝ)) mu (cube d (k : ℤ)) uLocal
          (fun x ↦ mu * f x) ∧
        (∫ x in cube d (k : ℤ),
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
            vecNormSq (uLocal.grad x) ∂volume) ≤ C := by
    intro k
    obtain ⟨uLocal, huAE, huSolution, huEnergy⟩ := huLocal k
    refine ⟨uLocal, huAE, huSolution, ?_⟩
    have htwo : (0 : ℝ) < 2 * mu := by positivity
    have := (le_div_iff₀ htwo).2 (by linarith [huEnergy] :
      (∫ x in cube d (k : ℤ),
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
          vecNormSq (uLocal.grad x) ∂volume) * (2 * mu) ≤
        mu ^ 2 * ∫ x, f x ^ 2 ∂volume)
    refine this.trans (le_of_eq ?_)
    rw [hCdef]
    field_simp
  obtain ⟨grad, henergy, hgrad⟩ :=
    exists_globalGradient_with_integrable_energy_of_cube_locals
      B huLocalBound
  have hgradSolution : ∀ k : ℕ,
      ∃ uLocal : H1Function (cube d (k : ℤ)),
        uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
        uLocal.grad =ᵐ[volume.restrict (cube d (k : ℤ))] grad ∧
        IsMassiveWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
          (fun _ ↦ (1 : ℝ)) mu (cube d (k : ℤ)) uLocal
          (fun x ↦ mu * f x) := by
    intro k
    obtain ⟨uLocal, huAE, huGrad, huSolution, _⟩ := hgrad k
    exact ⟨uLocal, huAE, huGrad, huSolution⟩
  have hglobalEnergy :
      ∫ x, SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
          vecNormSq (grad x) ∂volume ≤ C := by
    refine integral_le_of_forall_setIntegral_cube_le henergy ?_
    intro k
    obtain ⟨uLocal, _, huGrad, _, huEnergy⟩ := hgrad k
    refine le_trans (le_of_eq (integral_congr_ae ?_)) huEnergy
    filter_upwards [huGrad] with x hx
    rw [hx]
  have hdomains :=
    exists_exact_localMassiveWeakSolutionOn_of_forall_cube hgradSolution
  refine ⟨{ toFun := u
            grad := grad
            memL2_toFun := huMem
            integrable_energy := henergy
            locally_weak_solution := by simpa only using hdomains }, huL2, ?_⟩
  simpa only [hCdef, hmuDef, mul_assoc] using hglobalEnergy

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
