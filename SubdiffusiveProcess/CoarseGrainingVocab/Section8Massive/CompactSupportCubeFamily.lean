import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.MassiveSolver
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.C0CompactSupportExtension
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.DomainMonotonicity
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.MassiveContraction
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.MassiveMaximumPrinciple
import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.Windows

/-!
# The massive Dirichlet solutions on an exhausting family of cubes

This is the finite-volume part of the compact-support construction.  Under
ellipticity and weight bounds on every centered cube, compactly supported
continuous data give a zero-trace massive solution on every cube.  The family
obeys the weighted `L²` and energy estimates and the uniform maximum-principle
bound, with constants independent of the cube except for the coefficients
inside the weighted integrals.

Passing this family to an `H¹_loc` weak limit is deliberately not asserted in
this file; it requires a local Sobolev compactness theorem for the explicit
`H1Function` graph carrier.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped CompactlySupported ZeroAtInfty

noncomputable section

variable {d : ℕ}

/-- Chosen local ellipticity and weight bounds on the centered cube exhaustion. -/
structure MassiveCubeBounds (c rho : Vec d → ℝ) where
  lam : ℕ → ℝ
  Lam : ℕ → ℝ
  rhoMin : ℕ → ℝ
  rhoMax : ℕ → ℝ
  lam_pos : ∀ n : ℕ, 0 < lam n
  rhoMin_pos : ∀ n : ℕ, 0 < rhoMin n
  ell : ∀ n : ℕ, IsEllipticFieldOn (lam n) (Lam n) (cube d (n : ℤ))
    (scalarCoeffField c)
  coeff_lower : ∀ (n : ℕ) x, x ∈ cube d (n : ℤ) → lam n ≤ c x
  rho_measurable : ∀ n : ℕ,
    AEStronglyMeasurable rho (volume.restrict (cube d (n : ℤ)))
  rho_lower : ∀ (n : ℕ) x, x ∈ cube d (n : ℤ) → rhoMin n ≤ rho x
  rho_bounded : ∀ n : ℕ,
    ∀ᵐ x ∂(volume.restrict (cube d (n : ℤ))), |rho x| ≤ rhoMax n

/-- The three estimates retained for each member of the cube family. -/
def IsControlledMassiveCubeSolution (c rho : Vec d → ℝ) (mu : ℝ)
    (f : C_c(Vec d, ℝ)) (n : ℕ) (u : H10Function (cube d (n : ℤ))) : Prop :=
  IsMassiveWeakSolutionOn c rho mu (cube d (n : ℤ)) u.toH1Function f ∧
    mu ^ 2 * ∫ x in cube d (n : ℤ),
        rho x * u.toH1Function.toFun x * u.toH1Function.toFun x ∂volume ≤
      ∫ x in cube d (n : ℤ), rho x * f x * f x ∂volume ∧
    2 * mu * ∫ x in cube d (n : ℤ),
        c x * vecNormSq (u.toH1Function.grad x) ∂volume ≤
      ∫ x in cube d (n : ℤ), rho x * f x * f x ∂volume ∧
    ∀ᵐ x ∂(volume.restrict (cube d (n : ℤ))),
      |u.toH1Function.toFun x| ≤ ‖compactSupportToC0 f‖ / mu

private theorem memL2On_compactSupport (f : C_c(Vec d, ℝ)) (W : Set (Vec d)) :
    MemL2On W f :=
  (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport).restrict W

private theorem h10_of_zeroDirichletSolution
    {W : Set (Vec d)} {c rho : Vec d → ℝ} {mu : ℝ} {f : Vec d → ℝ}
    {v : H1Function W}
    (hv : IsMassiveDirichletSolutionOn c rho mu W v 0 f) :
    ∃ u : H10Function W,
      IsMassiveWeakSolutionOn c rho mu W u.toH1Function f := by
  obtain ⟨u, hfun, hgrad⟩ := hv.1
  have hfun' : v.toFun = u.toH1Function.toFun := by
    funext x
    simpa using hfun x
  have hgrad' : v.grad = u.toH1Function.grad := by
    funext x
    simpa using hgrad x
  have huv : v = u.toH1Function := H1Function.ext hfun' hgrad'
  exact ⟨u, by simpa only [← huv] using hv.2⟩

/-- Compactly supported continuous data produce a uniformly controlled massive
Dirichlet solution on every cube of the centered exhaustion.  This is the
finite-volume sequence to which the local compactness/diagonal argument must
be applied. -/
theorem exists_massiveCubeSolutionFamily_of_compactSupport [NeZero d]
    {c rho : Vec d → ℝ} (B : MassiveCubeBounds c rho)
    {mu : ℝ} (hmu : 0 < mu) (f : C_c(Vec d, ℝ)) :
    ∃ u : ∀ n : ℕ, H10Function (cube d (n : ℤ)),
      ∀ n, IsControlledMassiveCubeSolution c rho mu f n (u n) := by
  classical
  have hexists : ∀ n : ℕ, ∃ u : H10Function (cube d (n : ℤ)),
      IsControlledMassiveCubeSolution c rho mu f n u := by
    intro n
    let W := cube d (n : ℤ)
    have hW := Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (n : ℤ)
    have hf : MemL2On W f := memL2On_compactSupport f W
    obtain ⟨v, hv⟩ := exists_isMassiveDirichletSolutionOn hW hmu
      (B.rhoMin_pos n) (B.lam_pos n) (B.ell n) (B.rho_measurable n)
      (B.rho_lower n) (B.rho_bounded n) (0 : H1Function W) hf
    obtain ⟨u, hu⟩ := h10_of_zeroDirichletSolution hv
    refine ⟨u, hu, ?_, ?_, ?_⟩
    · exact massive_l2_contraction hW.isOpen.measurableSet hmu
        (B.rhoMin_pos n) (B.lam_pos n) (B.coeff_lower n)
        (B.rho_measurable n) (B.rho_lower n) (B.rho_bounded n) hf hu
    · exact massive_energy_bound hW.isOpen.measurableSet hmu
        (B.rhoMin_pos n) (B.rho_measurable n) (B.rho_lower n)
        (B.rho_bounded n) hf hu
    · have hk : 0 ≤ ‖compactSupportToC0 f‖ / mu :=
        div_nonneg (norm_nonneg _) hmu.le
      apply ae_abs_le_of_isMassiveWeakSolutionOn hW hmu hk
        (B.rhoMin_pos n) (B.lam_pos n) (B.coeff_lower n)
        (B.rho_measurable n) (B.rho_lower n) (B.rho_bounded n) hf
      · intro x hx
        have hpoint : |f x| ≤ ‖compactSupportToC0 f‖ := by
          simpa only [Real.norm_eq_abs, compactSupportToC0_apply] using
            BoundedContinuousFunction.norm_coe_le_norm
              (ZeroAtInftyContinuousMap.toBCF (compactSupportToC0 f)) x
        convert hpoint using 1
        field_simp [hmu.ne']
      · exact hu
  choose u hu using hexists
  exact ⟨u, hu⟩

/-- For nonnegative compactly supported data, the centered-cube solutions can
be chosen as an a.e. monotone exhaustion.  In fact domain monotonicity applies
to every family of the solutions constructed above. -/
theorem exists_monotoneMassiveCubeSolutionFamily_of_compactSupport [NeZero d]
    {c rho : Vec d → ℝ} (B : MassiveCubeBounds c rho)
    {mu : ℝ} (hmu : 0 < mu) (f : C_c(Vec d, ℝ))
    (hf : ∀ x, 0 ≤ f x) :
    ∃ u : ∀ n : ℕ, H10Function (cube d (n : ℤ)),
      (∀ n, IsControlledMassiveCubeSolution c rho mu f n (u n)) ∧
        ∀ n : ℕ, (u n).toH1Function.toFun ≤ᵐ[volume.restrict (cube d (n : ℤ))]
          (u (n + 1)).toH1Function.toFun := by
  obtain ⟨u, hu⟩ := exists_massiveCubeSolutionFamily_of_compactSupport B hmu f
  refine ⟨u, hu, fun n ↦ ?_⟩
  let W := cube d (n : ℤ)
  let V := cube d ((n + 1 : ℕ) : ℤ)
  have hW := Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (n : ℤ)
  have hV := Section6ExcessDecay.isOpenBoundedConvexDomain_cube d ((n + 1 : ℕ) : ℤ)
  have hWV : W ⊆ V := by
    exact Section6ExcessDecay.cube_subset_cube_of_le (by omega)
  exact ae_le_of_massiveWeakSolutionsOn_nestedDomains hW hV hWV hmu
    (B.rhoMin_pos n) (B.rhoMin_pos (n + 1)) (B.lam_pos n) (B.lam_pos (n + 1))
    (B.ell n) (B.coeff_lower n) (B.coeff_lower (n + 1))
    (B.rho_measurable n) (B.rho_measurable (n + 1))
    (B.rho_lower n) (B.rho_lower (n + 1))
    (B.rho_bounded n) (B.rho_bounded (n + 1))
    (memL2On_compactSupport f V) (fun x _ ↦ hf x) (hu n).1 (hu (n + 1)).1

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
