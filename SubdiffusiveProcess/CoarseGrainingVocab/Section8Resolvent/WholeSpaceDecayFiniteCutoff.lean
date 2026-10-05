module

public import SubdiffusiveProcess.Assumptions.Cutoff
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceDecayCarrier
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceDecaySignedSharp

@[expose] public section

/-!
# Finite-cutoff whole-space carrier on raw potential samples

The frozen whole-space estimate quantifies a raw `PotentialSample` and the
finite coefficient `aCutoff M L omega`.  The all-cutoff Section 8 solver API
uses `AnchoredC11Sample` only because its `L = top` branch needs the anchored
limit.  At finite cutoff no such restriction is needed: a finite exponential
sum is continuous and positive for every raw sample.

This file constructs the local cube-bounds package directly for `aCutoff` and
specializes the sharp signed limit, global-gradient construction, and global
weighted-energy closure to the exact sample type.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Set
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open _root_.SubdiffusiveProcess.Section8
open scoped CompactlySupported

noncomputable section

variable {d : ℕ}

/-- Raw finite-cutoff samples have the cube-by-cube bounds needed by the
massive exhaustion.
-/
theorem exists_finiteCutoffDivergenceMassiveCubeBounds [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    Nonempty (MassiveCubeBounds (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
      (fun _ ↦ (1 : ℝ))) := by
  let a := _root_.SubdiffusiveProcess.Model.aCutoff M L omega
  have hbounds : ∀ n : ℕ, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ closure (cube d (n : ℤ)), lam ≤ a x ∧ a x ≤ Lam := by
    intro n
    have hcompact :=
      (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d
        (n : ℤ)).isBoundedDomain.isBounded.isCompact_closure
    have hnonempty : (closure (cube d (n : ℤ))).Nonempty :=
      ⟨0, subset_closure (Section6ExcessDecay.zero_mem_cube d (n : ℤ))⟩
    obtain ⟨xmin, hxmin, hmin⟩ := hcompact.exists_isMinOn hnonempty
      (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M L omega).continuousOn
    obtain ⟨xmax, hxmax, hmax⟩ := hcompact.exists_isMaxOn hnonempty
      (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M L omega).continuousOn
    exact ⟨a xmin, a xmax, _root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega xmin,
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
      (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M L omega).continuousOn
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
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    MassiveCubeBounds (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
      (fun _ ↦ (1 : ℝ)) :=
  Classical.choice (exists_finiteCutoffDivergenceMassiveCubeBounds M L omega)

/-- Exact raw-sample compact-data endpoint: sharp `L²` contraction, one
global weak gradient with integrable coefficient energy, and pointwise
representatives solving the normalized massive equation on every bounded
open convex domain.
-/
theorem exists_finiteCutoffNormalizedMassiveWeakSolution_with_globalGradient
    [NeZero d] (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {mu : ℝ} (hmu : 0 < mu) (f : C_c(Vec d, ℝ)) :
    ∃ u : Vec d → ℝ, ∃ grad : Vec d → Vec d,
      MemLp u 2 volume ∧
      (∫ x, u x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume) ∧
      Integrable (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
        vecNormSq (grad x)) volume ∧
      ∀ W : Set (Vec d), IsOpenBoundedConvexDomain W →
        ∃ uW : H1Function W,
          (∀ x ∈ W, uW.toFun x = u x) ∧
          uW.grad =ᵐ[volume.restrict W] grad ∧
          IsMassiveWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
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
        IsMassiveWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
          (fun _ ↦ (1 : ℝ)) mu (cube d (k : ℤ)) uLocal
          (fun x ↦ mu * f x) ∧
        (∫ x in cube d (k : ℤ),
          _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
            vecNormSq (uLocal.grad x) ∂volume) ≤ C := by
    intro k
    obtain ⟨uLocal, huAE, huSolution, huEnergy⟩ := huLocal k
    refine ⟨uLocal, huAE, huSolution, ?_⟩
    apply (le_div_iff₀ htwoMu).2
    simpa only [mul_comm] using! huEnergy
  obtain ⟨grad, henergy, hgrad⟩ :=
    exists_globalGradient_with_integrable_energy_of_cube_locals
      B huLocalBound
  have hgradSolution : ∀ k : ℕ,
      ∃ uLocal : H1Function (cube d (k : ℤ)),
        uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
        uLocal.grad =ᵐ[volume.restrict (cube d (k : ℤ))] grad ∧
        IsMassiveWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
          (fun _ ↦ (1 : ℝ)) mu (cube d (k : ℤ)) uLocal
          (fun x ↦ mu * f x) := by
    intro k
    obtain ⟨uLocal, huAE, huGrad, huSolution, _huEnergy⟩ := hgrad k
    exact ⟨uLocal, huAE, huGrad, huSolution⟩
  have hdomains :=
    exists_exact_localMassiveWeakSolutionOn_of_forall_cube hgradSolution
  exact ⟨u, grad, huMem, huL2, henergy, hdomains⟩

/-- A raw finite-cutoff sample and compactly supported continuous datum yield
the exact frozen whole-space divergence-resolvent carrier, with sharp `L²`
contraction.
-/
theorem exists_finiteCutoffWholeSpaceDivergenceResolventSolution_of_compactSupport
    [NeZero d] (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {t : ℝ} (ht : 0 < t) (f : C_c(Vec d, ℝ)) :
    ∃ u : WholeSpaceDivergenceResolventSolution
        (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) t f,
      ∫ x, u.toFun x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume := by
  have hmu : 0 < t⁻¹ := inv_pos.mpr ht
  obtain ⟨u, grad, huMem, huL2, henergy, hdomains⟩ :=
    exists_finiteCutoffNormalizedMassiveWeakSolution_with_globalGradient
      M L omega hmu f
  let solution : WholeSpaceDivergenceResolventSolution
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) t f := {
    toFun := u
    grad := grad
    memL2_toFun := huMem
    integrable_energy := henergy
    locally_weak_solution := by
      simpa only using! hdomains }
  exact ⟨solution, huL2⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
