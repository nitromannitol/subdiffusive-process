module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceEstimatesUniqueness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceDecayCarrier
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.MassiveWeakSolutionAlgebra
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SmallContrastScalarBridge
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Set Topology
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Section8

noncomputable section

variable {d : ℕ}

/-! ### The centred cube exhaustion -/

/-- The centred cubes exhaust the whole space. -/
theorem iUnion_cube_nat_eq_univ :
    (⋃ k : ℕ, cube d (k : ℤ)) = (Set.univ : Set (Vec d)) := by
  refine Set.eq_univ_of_forall fun x ↦ ?_
  exact Set.mem_iUnion.2 ⟨wholeSpaceDecayCubeIndex x,
    mem_cube_wholeSpaceDecayCubeIndex x⟩

/-- The centred cubes are monotone in the natural-number index. -/
theorem monotone_cube_nat : Monotone (fun k : ℕ ↦ cube d (k : ℤ)) := by
  intro j k hjk
  exact Section6ExcessDecay.cube_subset_cube_of_le (by exact_mod_cast hjk)

/-! ### Two-sided coefficient bounds on bounded sets -/

/-- A continuous positive coefficient is bounded above and below by positive
constants on every bounded set. -/
theorem exists_coeff_bounds_of_isBounded {a : Vec d → ℝ}
    (hcont : Continuous a) (hpos : ∀ x, 0 < a x) {W : Set (Vec d)}
    (hW : Bornology.IsBounded W) :
    ∃ lam Lam : ℝ, 0 < lam ∧ ∀ x ∈ W, lam ≤ a x ∧ a x ≤ Lam := by
  classical
  obtain ⟨r, hr⟩ := hW.subset_closedBall (0 : Vec d)
  set s : ℝ := max r 0 with hs
  have hsr : (0 : ℝ) ≤ s := le_max_right _ _
  have hsub : W ⊆ Metric.closedBall (0 : Vec d) s :=
    hr.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  have hK : IsCompact (Metric.closedBall (0 : Vec d) s) :=
    isCompact_closedBall _ _
  have hne : (Metric.closedBall (0 : Vec d) s).Nonempty :=
    ⟨0, Metric.mem_closedBall_self hsr⟩
  obtain ⟨xmin, _, hmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
  obtain ⟨xmax, _, hmax⟩ := hK.exists_isMaxOn hne hcont.continuousOn
  exact ⟨a xmin, a xmax, hpos xmin, fun x hx ↦
    ⟨hmin (hsub hx), hmax (hsub hx)⟩⟩

/-- A continuous positive coefficient is uniformly elliptic on every bounded
measurable set. -/
theorem exists_isEllipticFieldOn_of_isBounded {a : Vec d → ℝ}
    (hcont : Continuous a) (hpos : ∀ x, 0 < a x) {W : Set (Vec d)}
    (hWmeas : MeasurableSet W) (hW : Bornology.IsBounded W) :
    ∃ lam Lam : ℝ, 0 < lam ∧
      IsEllipticFieldOn lam Lam W (scalarCoeffField a) ∧
      ∀ x ∈ W, lam ≤ a x ∧ a x ≤ Lam := by
  obtain ⟨lam, Lam, hlam, hbounds⟩ :=
    exists_coeff_bounds_of_isBounded hcont hpos hW
  exact ⟨lam, Lam, hlam,
    Section6BoundedMultiplier.isEllipticFieldOn_scalarCoeffField_of_continuousOn
      hWmeas hcont.continuousOn hlam hbounds, hbounds⟩

/-! ### Measurability of the carrier gradient -/

namespace WholeSpaceDivergenceResolventSolution

variable {a : Vec d → ℝ} {t : ℝ} {f : Vec d → ℝ}

/-- Every gradient coordinate of a whole-space carrier is a.e. strongly
measurable: the cube-local Sobolev representatives supply the property on each
centred cube, and the centred cubes exhaust the space. -/
theorem aestronglyMeasurable_grad_apply
    (u : WholeSpaceDivergenceResolventSolution a t f) (i : Fin d) :
    AEStronglyMeasurable (fun x ↦ u.grad x i) volume := by
  have hcube : ∀ k : ℕ,
      AEStronglyMeasurable (fun x ↦ u.grad x i)
        (volume.restrict (cube d (k : ℤ))) := by
    intro k
    obtain ⟨uW, _, hgrad, _⟩ :=
      u.locally_weak_solution (cube d (k : ℤ))
        (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (k : ℤ))
    refine ((uW.gradMemL2 i).aestronglyMeasurable).congr ?_
    filter_upwards [hgrad] with x hx
    rw [hx]
  have hunion :
      AEStronglyMeasurable (fun x ↦ u.grad x i)
        (volume.restrict (⋃ k : ℕ, cube d (k : ℤ))) :=
    aestronglyMeasurable_iUnion_iff.2 hcube
  rw [iUnion_cube_nat_eq_univ, Measure.restrict_univ] at hunion
  exact hunion



def sub (hcont : Continuous a) (hpos : ∀ x, 0 < a x)
    {g : Vec d → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (v : WholeSpaceDivergenceResolventSolution a t g) :
    WholeSpaceDivergenceResolventSolution a t (fun x ↦ f x - g x) where
  toFun := fun x ↦ u.toFun x - v.toFun x
  grad := fun x ↦ u.grad x - v.grad x
  memL2_toFun := u.memL2_toFun.sub v.memL2_toFun
  integrable_energy := by
    have hcoord : ∀ i : Fin d,
        AEStronglyMeasurable (fun x ↦ u.grad x i - v.grad x i) volume :=
      fun i ↦ (aestronglyMeasurable_grad_apply u i).sub
        (aestronglyMeasurable_grad_apply v i)
    have hmeas : AEStronglyMeasurable
        (fun x ↦ a x * vecNormSq (u.grad x - v.grad x)) volume := by
      have hsum : AEStronglyMeasurable
          (fun x ↦ ∑ i, (u.grad x i - v.grad x i) *
            (u.grad x i - v.grad x i)) volume :=
        Finset.aestronglyMeasurable_fun_sum _ fun i _ ↦ (hcoord i).mul (hcoord i)
      exact hcont.aestronglyMeasurable.mul hsum
    refine Integrable.mono'
      ((u.integrable_energy.add v.integrable_energy).const_mul 2) hmeas ?_
    refine Filter.Eventually.of_forall fun x ↦ ?_
    have hax : 0 ≤ a x := (hpos x).le
    have hbound := vecNormSq_sub_le (u.grad x) (v.grad x)
    have hnn : 0 ≤ a x * vecNormSq (u.grad x - v.grad x) :=
      mul_nonneg hax (vecNormSq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have := mul_le_mul_of_nonneg_left hbound hax
    calc a x * vecNormSq (u.grad x - v.grad x)
        ≤ a x * (2 * (vecNormSq (u.grad x) + vecNormSq (v.grad x))) := this
      _ = 2 * (a x * vecNormSq (u.grad x) + a x * vecNormSq (v.grad x)) := by
          ring
  locally_weak_solution := by
    intro W hW
    obtain ⟨uW, huValue, huGrad, huSol⟩ := u.locally_weak_solution W hW
    obtain ⟨vW, hvValue, hvGrad, hvSol⟩ := v.locally_weak_solution W hW
    obtain ⟨lam, Lam, _, hEll, _⟩ :=
      exists_isEllipticFieldOn_of_isBounded hcont hpos
        (W := W) hW.isOpen.measurableSet hW.isBoundedDomain.isBounded
    refine ⟨uW - vW, ?_, ?_, ?_⟩
    · intro x hx
      simp only [H1Function.sub_toFun, huValue x hx, hvValue x hx]
    · filter_upwards [huGrad, hvGrad] with x hx hy
      simp only [H1Function.sub_grad, hx, hy]
    · have hsub :=
        IsMassiveWeakSolutionOn.sub (c := a) (rho := fun _ ↦ (1 : ℝ))
          (mu := t⁻¹) (lam := lam) (Lam := Lam) (rhoMax := 1) hEll
          aestronglyMeasurable_const
          (Filter.Eventually.of_forall fun _ ↦ by norm_num)
          (f := fun x ↦ t⁻¹ * f x) (g := fun x ↦ t⁻¹ * g x)
          ((hf.const_mul t⁻¹).restrict W) ((hg.const_mul t⁻¹).restrict W)
          huSol hvSol
      have hforcing :
          ((fun x ↦ t⁻¹ * f x) - fun x ↦ t⁻¹ * g x) =
            fun x ↦ t⁻¹ * (f x - g x) := by
        funext x
        simp only [Pi.sub_apply]
        ring
      rwa [hforcing] at hsub

end WholeSpaceDivergenceResolventSolution

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
