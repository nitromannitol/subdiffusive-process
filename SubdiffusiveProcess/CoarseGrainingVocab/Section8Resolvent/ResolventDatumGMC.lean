module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumInterface
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.ResolventDatumBoundedContinuousLimit

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open MarkovProcess MarkovProcess.Semigroup
open scoped ZeroAtInfty CompactlySupported

noncomputable section

variable {d : ℕ}

/-! ### Compactly supported data -/

/-- **The compact-support input in the shape the datum consumes.**
For every positive shift and every compactly supported datum, the massive
equation has *some* solution in `C₀(ℝᵈ)`, with the local `H¹`
representatives the resolvent interface asks for.

This existence form is what the whole chain
`exists_c0MassiveSolution_of_zeroAtInfty` → `HasC0MassiveSolutions` → the
frozen datum consumes.  By the whole-space maximum principle
(`forall_abs_le_of_localMassiveWeakSolution_of_tendsto_cocompact`) the solution
it produces is unique and satisfies `μ ‖u‖ ≤ ‖f‖`, so no canonicity is lost. -/
def HasC0MassiveSolutionsOnCompactData (c rho : Vec d → ℝ) : Prop :=
  ∀ mu : ℝ, 0 < mu → ∀ f : C_c(Vec d, ℝ),
    ∃ g : C₀(Vec d, ℝ), ∀ k : ℕ, ∃ v : H1Function (cube d (k : ℤ)),
      (∀ x, v.toFun x = g x) ∧
        IsMassiveWeakSolutionOn c rho mu (cube d (k : ℤ)) v (fun x ↦ f x)

/-- **The Section 8 resolvent datum for one coefficient pair.**  A whole-space
massive solution operator with the strong-convergence property yields a `C₀`
resolvent datum with dense range and the weak elliptic characterization. -/
theorem exists_c0ResolventDatum_of_massiveC0Resolvent
    {c rho : Vec d → ℝ} (B : MassiveCubeBounds c rho)
    (R : MassiveC0Resolvent c rho)
    (hstrong : ∀ f : C₀(Vec d, ℝ),
      Tendsto (fun mu : PositiveShift ↦ (mu : ℝ) • R.sol mu f) atTop (nhds f)) :
    ∃ D : C0ResolventDatum (Vec d),
      (∀ mu, DenseRange (D.operator mu)) ∧ IsWeakEllipticResolvent c rho D :=
  ⟨R.toC0ResolventDatum B, R.denseRange_operator B hstrong,
    R.isWeakEllipticResolvent B⟩



theorem exists_gmc_resolvent_data_of_massiveC0Resolvents [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : WithTop ℕ)
    (RX : ∀ omega : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d,
      MassiveC0Resolvent (coefficientAt M L omega) (coefficientAt M L omega))
    (RY : ∀ omega : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d,
      MassiveC0Resolvent (coefficientAt M L omega) (fun _ ↦ (1 : ℝ)))
    (hX : ∀ (omega : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d)
      (f : C₀(Vec d, ℝ)),
      Tendsto (fun mu : PositiveShift ↦ (mu : ℝ) • (RX omega).sol mu f)
        atTop (nhds f))
    (hY : ∀ (omega : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d)
      (f : C₀(Vec d, ℝ)),
      Tendsto (fun mu : PositiveShift ↦ (mu : ℝ) • (RY omega).sol mu f)
        atTop (nhds f)) :
    ∃ DX DY : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d →
        C0ResolventDatum (Vec d),
      ∀ omega,
        (∀ mu, DenseRange ((DX omega).operator mu)) ∧
        IsWeakEllipticResolvent (coefficientAt M L omega)
          (coefficientAt M L omega) (DX omega) ∧
        (∀ mu, DenseRange ((DY omega).operator mu)) ∧
        IsWeakEllipticResolvent (coefficientAt M L omega)
          (fun _ ↦ (1 : ℝ)) (DY omega) := by
  refine ⟨fun omega ↦ (RX omega).toC0ResolventDatum
      (reversibleMassiveCubeBounds M L omega),
    fun omega ↦ (RY omega).toC0ResolventDatum
      (divergenceMassiveCubeBounds M L omega), fun omega ↦ ⟨?_, ?_, ?_, ?_⟩⟩
  · exact (RX omega).denseRange_operator _ (hX omega)
  · exact (RX omega).isWeakEllipticResolvent _
  · exact (RY omega).denseRange_operator _ (hY omega)
  · exact (RY omega).isWeakEllipticResolvent _



theorem exists_gmc_resolvent_data_of_hasC0MassiveSolutions [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : WithTop ℕ)
    (hX : ∀ omega : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d,
      HasC0MassiveSolutions (coefficientAt M L omega) (coefficientAt M L omega))
    (hY : ∀ omega : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d,
      HasC0MassiveSolutions (coefficientAt M L omega) (fun _ ↦ (1 : ℝ)))
    (hXs : ∀ omega : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d,
      HasStrongMassiveResolventLimit (coefficientAt M L omega)
        (coefficientAt M L omega))
    (hYs : ∀ omega : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d,
      HasStrongMassiveResolventLimit (coefficientAt M L omega)
        (fun _ ↦ (1 : ℝ))) :
    ∃ DX DY : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d →
        C0ResolventDatum (Vec d),
      ∀ omega,
        (∀ mu, DenseRange ((DX omega).operator mu)) ∧
        IsWeakEllipticResolvent (coefficientAt M L omega)
          (coefficientAt M L omega) (DX omega) ∧
        (∀ mu, DenseRange ((DY omega).operator mu)) ∧
        IsWeakEllipticResolvent (coefficientAt M L omega)
          (fun _ ↦ (1 : ℝ)) (DY omega) :=
  exists_gmc_resolvent_data_of_massiveC0Resolvents M L
    (fun omega ↦ MassiveC0Resolvent.ofHasC0MassiveSolutions (hX omega))
    (fun omega ↦ MassiveC0Resolvent.ofHasC0MassiveSolutions (hY omega))
    (fun omega ↦ hXs omega _) (fun omega ↦ hYs omega _)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
