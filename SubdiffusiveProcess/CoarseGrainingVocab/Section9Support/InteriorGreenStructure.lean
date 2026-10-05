module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.InteriorVariationalGreen
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.MoserVariationalGreen

@[expose] public section

/-!
# Uniqueness and harmonic correction for the variational Green solution

The inverse is unique as a Sobolev equivalence class. Its harmonic correction
is proved for the original almost everywhere measurable coefficient; a
continuous representative of that correction is a separate regularity step.
-/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Changing the elliptic coefficient on a null set does not change the
weak equation. -/
theorem interior_massiveWeakSolution_congr_coefficient {d : ℕ} {U : Set (Vec d)}
    {c a rho f : Vec d → ℝ} {mu : ℝ} {u : H1Function U}
    (hca : c =ᵐ[volume.restrict U] a)
    (hu : IsMassiveWeakSolutionOn c rho mu U u f) :
    IsMassiveWeakSolutionOn a rho mu U u f := by
  intro phi
  have henergy : (∫ x in U, vecDot (a x • u.grad x) (phi.toH1Function.grad x)) =
      ∫ x in U, vecDot (c x • u.grad x) (phi.toH1Function.grad x) := by
    apply integral_congr_ae
    filter_upwards [hca] with x hx
    rw [hx]
  rw [henergy]
  exact hu phi

/-- The zero-boundary Green solution is unique in both value and weak
gradient, without choosing a pointwise measurable coefficient as an input. -/
theorem interior_variational_green_unique {d : ℕ} [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)
    {c rho f : Vec d → ℝ} (hc : CoefficientOn U c)
    {g v : H10Function U}
    (hg : IsMassiveWeakSolutionOn c rho 0 U g.toH1Function f)
    (hv : IsMassiveWeakSolutionOn c rho 0 U v.toH1Function f) :
    g.toH1Function.toFun =ᵐ[volume.restrict U] v.toH1Function.toFun ∧
      g.toH1Function.grad =ᵐ[volume.restrict U] v.toH1Function.grad := by
  obtain ⟨a, lam, Lam, hEll, hca⟩ := exists_interior_elliptic_representative hU.isOpen.measurableSet hc
  have hga := interior_massiveWeakSolution_congr_coefficient hca hg
  have hva := interior_massiveWeakSolution_congr_coefficient hca hv
  have htrace (w : H10Function U) : HasZeroTraceDifferenceOn U w.toH1Function 0 := by
    refine ⟨w, ?_, ?_⟩
    · intro x
      change w.toH1Function.toFun x = 0 + w.toH1Function.toFun x
      ring
    · intro x
      change w.toH1Function.grad x = 0 + w.toH1Function.grad x
      rw [zero_add]
  apply ae_eq_of_hasZeroTraceDifferenceOn_of_forall_flux_pairing_eq
    hU hne hEll (htrace g) (htrace v)
  intro phi
  have hgphi := hga phi
  have hvphi := hva phi
  simp only [zero_mul, zero_add] at hgphi hvphi
  simpa only [scalarCoeffField, matVecMul_scalarMatrix] using hgphi.trans hvphi.symm

/-- The chosen Green solution agrees with every variational solution of the
same datum; hence its Sobolev class is independent of the existence choice. -/
theorem interiorGreen_ae_eq_of_solution {d : ℕ} [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)
    {c rho : Vec d → ℝ} (hc : CoefficientOn U c) (hr : CoefficientOn U rho)
    {f : Vec d → ℝ} (hf : MemLp f 2 ((weightedMeasure rho).restrict U))
    {g : H10Function U} (hg : IsMassiveWeakSolutionOn c rho 0 U g.toH1Function f) :
    (interiorGreen hU hne hc hr hf).toH1Function.toFun =ᵐ[volume.restrict U] g.toH1Function.toFun ∧
      (interiorGreen hU hne hc hr hf).toH1Function.grad =ᵐ[volume.restrict U] g.toH1Function.grad :=
  interior_variational_green_unique hU hne hc (interiorGreen_spec hU hne hc hr hf) hg

/-- The massive solution plus its variational Green correction is weakly
harmonic. The hypothesis is the `CoefficientOn` predicate. -/
theorem interior_add_green_harmonic {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) {c rho : Vec d → ℝ} (hc : CoefficientOn U c)
    {mu : ℝ} (u g : H1Function U)
    (hu : IsMassiveWeakSolutionOn c rho mu U u (fun _ => 0))
    (hg : IsMassiveWeakSolutionOn c rho 0 U g u.toFun) :
    IsWeaklyHarmonicOn c U (u + mu • g) := by
  obtain ⟨a, lam, Lam, hEll, hca⟩ := exists_interior_elliptic_representative hU hc
  have h := isWeaklyHarmonicOn_add_green_correction hEll u g
    (interior_massiveWeakSolution_congr_coefficient hca hu)
    (interior_massiveWeakSolution_congr_coefficient hca hg)
  intro phi
  refine (integral_congr_ae ?_).trans (h phi)
  filter_upwards [hca] with x hx
  rw [hx]

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
