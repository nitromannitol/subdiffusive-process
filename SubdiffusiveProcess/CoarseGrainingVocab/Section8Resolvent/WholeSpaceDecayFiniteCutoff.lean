import SubdiffusiveProcess.Assumptions.Cutoff
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceDecayCarrier
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceDecaySignedSharp




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Set
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Section8
open scoped CompactlySupported

noncomputable section

variable {d : ℕ}



theorem exists_finiteCutoffDivergenceMassiveCubeBounds [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    Nonempty (MassiveCubeBounds (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
      (fun _ ↦ (1 : ℝ))) := by
  let a := SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega
  have hbounds : ∀ n : ℕ, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ closure (cube d (n : ℤ)), lam ≤ a x ∧ a x ≤ Lam := by
    intro n
    have hcompact :=
      (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d
        (n : ℤ)).isBoundedDomain.isBounded.isCompact_closure
    have hnonempty : (closure (cube d (n : ℤ))).Nonempty :=
      ⟨0, subset_closure (Section6ExcessDecay.zero_mem_cube d (n : ℤ))⟩
    obtain ⟨xmin, hxmin, hmin⟩ := hcompact.exists_isMinOn hnonempty
      (SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M L omega).continuousOn
    obtain ⟨xmax, hxmax, hmax⟩ := hcompact.exists_isMaxOn hnonempty
      (SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M L omega).continuousOn
    exact ⟨a xmin, a xmax, SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega xmin,
      fun x hx ↦ ⟨hmin hx, hmax hx⟩⟩
  choose lam Lam hlam hb using hbounds
  refine ⟨{
    lam := lam
    Lam := Lam
    rhoMin := fun _ ↦ 1
    rhoMax := fun _ ↦ 1
    lam_pos := hlam
    rhoMin_pos := fun _ ↦ one_pos
    ell := ?_
    coeff_lower := ?_
    rho_measurable := ?_
    rho_lower := ?_
    rho_bounded := ?_ }⟩
  · intro n
    apply Section6BoundedMultiplier.isEllipticFieldOn_scalarCoeffField_of_continuousOn
      (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d
        (n : ℤ)).isOpen.measurableSet
      (SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M L omega).continuousOn
      (hlam n)
    intro x hx
    exact hb n x (subset_closure hx)
  · intro n x hx
    exact (hb n x (subset_closure hx)).1
  · intro _n
    exact aestronglyMeasurable_const
  · intro _n _x _hx
    exact le_rfl
  · intro _n
    exact Filter.Eventually.of_forall fun _ ↦ by norm_num

/-- A fixed cube-bounds package for a raw finite-cutoff sample. -/
noncomputable def finiteCutoffDivergenceMassiveCubeBounds [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    MassiveCubeBounds (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
      (fun _ ↦ (1 : ℝ)) :=
  Classical.choice (exists_finiteCutoffDivergenceMassiveCubeBounds M L omega)



theorem exists_finiteCutoffNormalizedMassiveWeakSolution_with_globalGradient
    [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {mu : ℝ} (hmu : 0 < mu) (f : C_c(Vec d, ℝ)) :
    ∃ u : Vec d → ℝ, ∃ grad : Vec d → Vec d,
      MemLp u 2 volume ∧
      (∫ x, u x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume) ∧
      Integrable (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
        vecNormSq (grad x)) volume ∧
      ∀ W : Set (Vec d), IsOpenBoundedConvexDomain W →
        ∃ uW : H1Function W,
          (∀ x ∈ W, uW.toFun x = u x) ∧
          uW.grad =ᵐ[volume.restrict W] grad ∧
          IsMassiveWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (fun _ ↦ (1 : ℝ)) mu W uW (fun x ↦ mu * f x) := by
  let B := finiteCutoffDivergenceMassiveCubeBounds M L omega
  obtain ⟨u, huMem, huL2, huLocal⟩ :=
    exists_localNormalizedMassiveWeakSolution_with_sharp_l2_and_energy
      B hmu f
  let C : ℝ :=
    (mu ^ 2 * ∫ x, f x ^ 2 ∂volume) / (2 * mu)
  have htwoMu : 0 < 2 * mu := mul_pos two_pos hmu
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
    apply (le_div_iff₀ htwoMu).2
    simpa only [mul_comm] using huEnergy
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
    obtain ⟨uLocal, huAE, huGrad, huSolution, _huEnergy⟩ := hgrad k
    exact ⟨uLocal, huAE, huGrad, huSolution⟩
  have hdomains :=
    exists_exact_localMassiveWeakSolutionOn_of_forall_cube hgradSolution
  exact ⟨u, grad, huMem, huL2, henergy, hdomains⟩



theorem exists_finiteCutoffWholeSpaceDivergenceResolventSolution_of_compactSupport
    [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {t : ℝ} (ht : 0 < t) (f : C_c(Vec d, ℝ)) :
    ∃ u : WholeSpaceDivergenceResolventSolution
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) t f,
      ∫ x, u.toFun x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume := by
  have hmu : 0 < t⁻¹ := inv_pos.mpr ht
  obtain ⟨u, grad, huMem, huL2, henergy, hdomains⟩ :=
    exists_finiteCutoffNormalizedMassiveWeakSolution_with_globalGradient
      M L omega hmu f
  let solution : WholeSpaceDivergenceResolventSolution
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) t f := {
    toFun := u
    grad := grad
    memL2_toFun := huMem
    integrable_energy := henergy
    locally_weak_solution := by
      simpa only using hdomains }
  exact ⟨solution, huL2⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
