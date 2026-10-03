module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumUniqueness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.MassiveWeakSolutionAlgebra
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeSmoothCore

@[expose] public section




open MeasureTheory MarkovProcess
open Homogenization (H1Function)
open SubdiffusiveProcess.CoarseGrainingVocab (cube)
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ZeroAtInfty

noncomputable section
namespace SubdiffusiveProcess

variable {d : ℕ}

/-- A continuous positive pair `(c, ρ)` admits the local cube bounds of the whole-space theory. -/
theorem nonempty_massiveCubeBounds_of_continuous_pos
    {c rho : SubdiffusiveProcess.CoarseGrainingVocab.Vec d → ℝ}
    (hc : Continuous c) (hrho : Continuous rho)
    (hcp : ∀ x, 0 < c x) (hrhop : ∀ x, 0 < rho x) :
    Nonempty (MassiveCubeBounds c rho) := by
  choose p hp hcb using fun n ↦
    SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.exists_cube_bounds hc hcp n
  choose q hq hρb using fun n ↦
    SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.exists_cube_bounds hrho hrhop n
  refine ⟨{
    lam := fun n ↦ (p n).1
    Lam := fun n ↦ (p n).2
    rhoMin := fun n ↦ (q n).1
    rhoMax := fun n ↦ (q n).2
    lam_pos := fun n ↦ (hp n)
    rhoMin_pos := fun n ↦ (hq n)
    ell := ?_
    coeff_lower := ?_
    rho_measurable := ?_
    rho_lower := ?_
    rho_bounded := ?_ }⟩
  · intro n
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.isEllipticFieldOn_scalarCoeffField_of_continuousOn
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.isOpenBoundedConvexDomain_cube d
        (n : ℤ)).isOpen.measurableSet
      hc.continuousOn (hp n) (hcb n)
  · intro n x hx
    exact (hcb n x hx).1
  · intro n
    exact hrho.aestronglyMeasurable.restrict
  · intro n x hx
    exact (hρb n x hx).1
  · intro n
    filter_upwards [ae_restrict_mem
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.isOpenBoundedConvexDomain_cube d
        (n : ℤ)).isOpen.measurableSet] with x hx
    rw [abs_of_pos (hrhop x)]
    exact (hρb n x hx).2

/-- **Uniqueness of the resolvent datum of a weak elliptic pair.**  Two `C₀` resolvent data that
are weak elliptic resolvents for the same pair `(c, ρ)` have the same solutions. -/
theorem solution_eq_of_isWeakEllipticResolvent
    {c rho : SubdiffusiveProcess.CoarseGrainingVocab.Vec d → ℝ} (B : MassiveCubeBounds c rho)
    {D D' : C0ResolventDatum (SubdiffusiveProcess.CoarseGrainingVocab.Vec d)}
    (hD : IsWeakEllipticResolvent c rho D) (hD' : IsWeakEllipticResolvent c rho D')
    (mu : Semigroup.PositiveShift) (f : C₀(SubdiffusiveProcess.CoarseGrainingVocab.Vec d, ℝ))
    (x : SubdiffusiveProcess.CoarseGrainingVocab.Vec d) :
    D.solution mu f x = D'.solution mu f x := by
  set g := D.solution mu f with hg
  set g' := D'.solution mu f with hg'
  have hzero : ∀ y, g y - g' y = 0 := by
    refine eq_zero_of_localMassiveWeakSolution_of_tendsto_cocompact B mu.property
      (u := fun y ↦ g y - g' y) (g.continuous.sub g'.continuous) ?_ ?_
    · simpa only [sub_zero] using (zero_at_infty g).sub (zero_at_infty g')
    · intro k
      set W := cube d (k : ℤ) with hWdef
      have hW := SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.isOpenBoundedConvexDomain_cube d
        (k : ℤ)
      have hWmeas : MeasurableSet W := hW.isOpen.measurableSet
      obtain ⟨v1, hv1, hs1⟩ := hD mu f W hW
      obtain ⟨v2, hv2, hs2⟩ := hD' mu f W hW
      have hsub := IsMassiveWeakSolutionOn.sub (B.ell k) (B.rho_measurable k)
        (B.rho_bounded k) (memL2On_of_zeroAtInfty hW f) (memL2On_of_zeroAtInfty hW f)
        hs1 hs2
      refine ⟨v1 - v2, ?_, IsMassiveWeakSolutionOn.congr_forcing ?_ hsub⟩
      · filter_upwards [ae_restrict_mem hWmeas] with y hy
        simp only [H1Function.sub_toFun, hv1 y hy, hv2 y hy]
        rfl
      · funext y
        simp only [Pi.sub_apply, sub_self]
  exact sub_eq_zero.mp (hzero x)

end SubdiffusiveProcess
