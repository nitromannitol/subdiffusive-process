module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.CompactSupportMonotoneLimit
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface

@[expose] public section

/-!
# Local cube bounds for the GMC massive exhaustion

This file instantiates the abstract cube-by-cube ellipticity package used by
the massive Dirichlet exhaustion for the two coefficient/weight pairs in the
paper.  The bounds are deliberately allowed to depend on the cube: the GMC
coefficient is only locally elliptic.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Set Topology
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped CompactlySupported ZeroAtInfty

noncomputable section

variable {d : ℕ}

/-- The reversible pair `(c, ρ) = (a, a)` has the local bounds required by the
centered-cube massive exhaustion. -/
theorem exists_reversibleMassiveCubeBounds [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : WithTop ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d) :
    Nonempty (MassiveCubeBounds (coefficientAt M L omega)
      (coefficientAt M L omega)) := by
  have hbounds : ∀ n : ℕ, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ closure (cube d (n : ℤ)),
        lam ≤ coefficientAt M L omega x ∧ coefficientAt M L omega x ≤ Lam := by
    intro n
    exact exists_bounds_coefficientAt_of_isCompact M L omega
      (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d
        (n : ℤ)).2.1.isBounded.isCompact_closure
  choose lam Lam hlam hb using hbounds
  refine ⟨{
    lam := lam
    Lam := Lam
    rhoMin := lam
    rhoMax := Lam
    lam_pos := hlam
    rhoMin_pos := hlam
    ell := ?_
    coeff_lower := ?_
    rho_measurable := ?_
    rho_lower := ?_
    rho_bounded := ?_ }⟩
  · intro n
    apply isEllipticFieldOn_coefficientAt M L omega
      (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (n : ℤ)).isOpen.measurableSet
      (hlam n)
    intro x hx
    exact hb n x (subset_closure hx)
  · intro n x hx
    exact (hb n x (subset_closure hx)).1
  · intro n
    exact (continuous_coefficientAt M L omega).aestronglyMeasurable
  · intro n x hx
    exact (hb n x (subset_closure hx)).1
  · intro n
    filter_upwards [ae_restrict_mem
      (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (n : ℤ)).isOpen.measurableSet]
      with x hx
    rw [abs_of_pos (coefficientAt_pos M L omega x)]
    exact (hb n x (subset_closure hx)).2

/-- The divergence-form pair `(c, ρ) = (a, 1)` has the local bounds required
by the centered-cube massive exhaustion. -/
theorem exists_divergenceMassiveCubeBounds [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : WithTop ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d) :
    Nonempty (MassiveCubeBounds (coefficientAt M L omega) (fun _ ↦ (1 : ℝ))) := by
  have hbounds : ∀ n : ℕ, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ closure (cube d (n : ℤ)),
        lam ≤ coefficientAt M L omega x ∧ coefficientAt M L omega x ≤ Lam := by
    intro n
    exact exists_bounds_coefficientAt_of_isCompact M L omega
      (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d
        (n : ℤ)).2.1.isBounded.isCompact_closure
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
    apply isEllipticFieldOn_coefficientAt M L omega
      (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (n : ℤ)).isOpen.measurableSet
      (hlam n)
    intro x hx
    exact hb n x (subset_closure hx)
  · intro n x hx
    exact (hb n x (subset_closure hx)).1
  · intro n
    exact aestronglyMeasurable_const
  · intro n x hx
    exact le_rfl
  · intro n
    exact Filter.Eventually.of_forall fun _ ↦ by norm_num

/-- A fixed choice of cube bounds for the reversible GMC pair. -/
noncomputable def reversibleMassiveCubeBounds [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : WithTop ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d) :
    MassiveCubeBounds (coefficientAt M L omega) (coefficientAt M L omega) :=
  Classical.choice (exists_reversibleMassiveCubeBounds M L omega)

/-- A fixed choice of cube bounds for the divergence-form GMC pair. -/
noncomputable def divergenceMassiveCubeBounds [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : WithTop ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d) :
    MassiveCubeBounds (coefficientAt M L omega) (fun _ ↦ (1 : ℝ)) :=
  Classical.choice (exists_divergenceMassiveCubeBounds M L omega)

/-- The reversible GMC pair reaches the bounded pointwise monotone endpoint of
the compact-data cube exhaustion. -/
theorem exists_pointwiseMonotoneReversibleMassiveCubeLimit [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : WithTop ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d)
    {mu : ℝ} (hmu : 0 < mu) (f : C_c(Vec d, ℝ)) (hf : ∀ x, 0 ≤ f x) :
    ∃ uCube : ∀ n : ℕ, H10Function (cube d (n : ℤ)),
      ∃ v : ℕ → Vec d → ℝ, ∃ u : Vec d → ℝ,
        (∀ n, IsControlledMassiveCubeSolution (coefficientAt M L omega)
          (coefficientAt M L omega) mu f n (uCube n)) ∧
        (∀ n, v n =ᵐ[volume] (uCube n).zeroExtension) ∧
        (∀ x, Monotone fun n ↦ v n x) ∧
        (∀ n x, 0 ≤ v n x ∧ v n x ≤ ‖compactSupportToC0 f‖ / mu) ∧
        ∀ x, Tendsto (fun n ↦ v n x) atTop (𝓝 (u x)) :=
  exists_pointwiseMonotoneMassiveCubeLimit_of_compactSupport
    (reversibleMassiveCubeBounds M L omega) hmu f hf

/-- The divergence-form GMC pair reaches the bounded pointwise monotone
endpoint of the compact-data cube exhaustion. -/
theorem exists_pointwiseMonotoneDivergenceMassiveCubeLimit [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : WithTop ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d)
    {mu : ℝ} (hmu : 0 < mu) (f : C_c(Vec d, ℝ)) (hf : ∀ x, 0 ≤ f x) :
    ∃ uCube : ∀ n : ℕ, H10Function (cube d (n : ℤ)),
      ∃ v : ℕ → Vec d → ℝ, ∃ u : Vec d → ℝ,
        (∀ n, IsControlledMassiveCubeSolution (coefficientAt M L omega)
          (fun _ ↦ (1 : ℝ)) mu f n (uCube n)) ∧
        (∀ n, v n =ᵐ[volume] (uCube n).zeroExtension) ∧
        (∀ x, Monotone fun n ↦ v n x) ∧
        (∀ n x, 0 ≤ v n x ∧ v n x ≤ ‖compactSupportToC0 f‖ / mu) ∧
        ∀ x, Tendsto (fun n ↦ v n x) atTop (𝓝 (u x)) :=
  exists_pointwiseMonotoneMassiveCubeLimit_of_compactSupport
    (divergenceMassiveCubeBounds M L omega) hmu f hf

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
