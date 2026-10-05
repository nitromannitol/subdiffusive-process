module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase

@[expose] public section

/-!
# The zero divergence datum

Theorem C's proof specializes `p.cutoff.Holder.regularity` by taking `g = 0`
(`p.cutoff.Holder.regularity` and `e.eq.for.u.holder.estimate` and `e.Holder.estimate.boxes.local` and `e.energy.density.estimate`): the boundary-value problem
`e.eq.for.u.holder.estimate` (`p.cutoff.Holder.regularity` and `e.eq.for.u.holder.estimate` and `e.Holder.estimate.boxes.local` and `e.energy.density.estimate`) degenerates from
`-∇·a∇u = ∇·g` to the harmonic equation `-∇·a∇u = 0`.

This file collects the consequences of that choice which the specialization
needs:

* the Hölder seminorm `[g]_{W̲^{1/2,∞}(𝔠_m)}` appearing on the right of both
  `e.Holder.estimate.boxes.local` and `e.energy.density.estimate` vanishes
  (`holderSeminormOn_zero`), so the whole datum term drops out;
* the zero datum is an admissible `C^{0,1/2}` field (`memHolder_zero`), which
  is what the hypothesis of `p.cutoff.Holder.regularity` demands;
* a weakly harmonic function is a Dirichlet solution with datum `g = 0` and its
  own boundary values (`isDirichletSolutionOn_self_zero_of_isWeaklyHarmonicOn`).

The last item deliberately presents `u` as its own boundary datum `h = u`.
That is the only presentation available from Theorem C's hypothesis
`IsWeaklyHarmonicOn`, and it leaves the remaining hypothesis of
`p.cutoff.Holder.regularity` — `MemHolder (cube d m) (1/2) h.grad`, i.e.
`h ∈ C^{1,1/2}(𝔠_m)` — undischarged.  Supplying it is exactly the trace
approximation step of `p.cutoff.Holder.regularity` and `e.eq.for.u.holder.estimate` and `e.Holder.estimate.boxes.local` and `e.energy.density.estimate` ("Approximation of the trace
in `H^{1/2}(∂𝔠_m)` extends the conclusion from smooth to arbitrary `H¹`
boundary data"), which is *not* proved here; see the bundle report.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-! ### The Hölder data terms vanish -/

/-- The Hölder seminorm of the zero field vanishes, so the datum term
`(β_{L,m})⁻¹ 3^{3m/2} [g]_{W̲^{1/2,∞}(𝔠_m)}` of
`e.Holder.estimate.boxes.local` and its counterpart in
`e.energy.density.estimate` drop out when `g = 0`. -/
theorem holderSeminormOn_zero (W : Set (Vec d)) (alpha : ℝ) :
    holderSeminormOn W alpha (fun _ ↦ (0 : Vec d)) = 0 := by
  have hsub : {r : ℝ | ∃ x ∈ W, ∃ y ∈ W, x ≠ y ∧
      r = euclideanNorm ((0 : Vec d) - (0 : Vec d)) /
        euclideanNorm (x - y) ^ alpha} ⊆ {0} := by
    rintro r ⟨x, -, y, -, -, rfl⟩
    simp
  rcases Set.subset_singleton_iff_eq.1 hsub with h | h
  · rw [holderSeminormOn, h, Real.sSup_empty]
  · rw [holderSeminormOn, h, csSup_singleton]

/-- The zero field is Hölder continuous of every exponent: this discharges the
hypothesis `g ∈ C^{0,1/2}(𝔠_m;ℝᵈ)` of `p.cutoff.Holder.regularity`
(`p.cutoff.Holder.regularity`). -/
theorem memHolder_zero (W : Set (Vec d)) (alpha : ℝ) :
    MemHolder W alpha (fun _ ↦ (0 : Vec d)) :=
  ⟨0, le_refl 0, by
    intro x _ y _
    simp⟩

/-! ### The zero-datum Dirichlet presentation -/

/-- Every `H¹` function has zero trace difference with itself, witnessed by the
zero element of `H¹₀`. -/
theorem hasZeroTraceDifferenceOn_self (W : Set (Vec d)) (u : H1Function W) :
    HasZeroTraceDifferenceOn W u u :=
  ⟨0, fun x ↦ by
      show u.toFun x = u.toFun x + (0 : H1Function W).toFun x
      simp, fun x ↦ by
      show u.grad x = u.grad x + (0 : H1Function W).grad x
      simp⟩

/-- With the zero divergence datum, the weak equation `-∇·a∇u = ∇·g` of
`e.eq.for.u.holder.estimate` is exactly weak harmonicity. -/
theorem isDivFormWeakSolutionOn_zero_iff (a : Vec d → ℝ) (W : Set (Vec d))
    (u : H1Function W) :
    IsDivFormWeakSolutionOn a W u (fun _ ↦ (0 : Vec d)) ↔
      IsWeaklyHarmonicOn a W u := by
  have hz : ∀ φ : H10Function W,
      -∫ x in W, vecDot (0 : Vec d) (φ.toH1Function.grad x) ∂volume =
        (0 : ℝ) := by
    intro φ
    simp [vecDot]
  constructor
  · intro h φ
    have := h φ
    rwa [hz φ] at this
  · intro h φ
    rw [hz φ]
    exact h φ

/-- The presentation of a weakly harmonic function as a Dirichlet solution with
zero divergence datum and its own boundary values.  This is the shape required
by the hypothesis of `p.cutoff.Holder.regularity` at `p.cutoff.Holder.regularity`,
with `g = 0` as directed at `p.cutoff.Holder.regularity`. -/
theorem isDirichletSolutionOn_self_zero_of_isWeaklyHarmonicOn
    {a : Vec d → ℝ} {Q : TriadicCube d} {u : H1Function (openCubeSet Q)}
    (hu : IsWeaklyHarmonicOn a (openCubeSet Q) u) :
    IsDirichletSolutionOn a Q u u (fun _ ↦ (0 : Vec d)) :=
  ⟨hasZeroTraceDifferenceOn_self _ u,
    (isDivFormWeakSolutionOn_zero_iff a _ u).2 hu⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
