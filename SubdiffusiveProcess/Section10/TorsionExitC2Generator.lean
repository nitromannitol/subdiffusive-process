import SubdiffusiveProcess.Section10.TorsionExitC2WeakTest

/-! Generator-domain identification for the textbook `C²` compact test class.
The same native massive weak equation and whole-space uniqueness are used as
for the existing smooth-test theorem. No stronger coefficient hypothesis is
introduced, and neither the speed nor the generator clock is changed. -/

noncomputable section
open Homogenization MeasureTheory Filter Topology MarkovProcess
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock
open MarkovProcess.Semigroup
open scoped ZeroAtInfty CompactlySupported
namespace SubdiffusiveProcess.Section10

theorem solution_eq_of_c2MassiveForcing {d : ℕ} {c rho : Vec d → ℝ}
    (B : MassiveCubeBounds c rho) (hc : ContDiff ℝ 1 c)
    (D : C0ResolventDatum (Vec d)) (hD : IsWeakEllipticResolvent c rho D)
    (mu : PositiveShift) (w f : C₀(Vec d, ℝ))
    (hw : ContDiff ℝ 2 (w : Vec d → ℝ))
    (hf : ∀ x, f x = smoothMassiveForcing c rho (mu : ℝ) w x) :
    D.solution mu f = w := by
  let R := massiveResolventOfWeak D hD
  have hcont : Continuous (fun x ↦ D.solution mu f x - w x) :=
    (D.solution mu f).continuous.sub w.continuous
  have hdecay : Tendsto (fun x ↦ D.solution mu f x - w x)
      (cocompact (Vec d)) (nhds 0) := by
    simpa using (zero_at_infty (D.solution mu f)).sub (zero_at_infty w)
  have hlocal : ∀ k : ℕ, ∃ v : H1Function (cube d (k : ℤ)),
      v.toFun =ᵐ[volume.restrict (cube d (k : ℤ))]
        (fun x ↦ D.solution mu f x - w x) ∧
      IsMassiveWeakSolutionOn c rho (mu : ℝ) (cube d (k : ℤ)) v (fun _ ↦ 0) := by
    intro k
    have hW := Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (k : ℤ)
    obtain ⟨v, hv, hsol⟩ := R.sol_local mu f k
    let u := H1Function.ofContDiffOnIsOpenBoundedConvexDomain hW (hw.of_le (by simp))
    have hsmooth : IsMassiveWeakSolutionOn c rho (mu : ℝ) (cube d (k : ℤ)) u
        (smoothMassiveForcing c rho (mu : ℝ) w) :=
      isMassiveWeakSolutionOn_ofContDiffOnBounded_of_two hc hw hW (B.rho_measurable k)
        (B.rho_bounded k) (fun x ↦ (B.weight_pos x).ne')
    have hsmooth' : IsMassiveWeakSolutionOn c rho (mu : ℝ) (cube d (k : ℤ)) u
        (fun x ↦ f x) :=
      IsMassiveWeakSolutionOn.congr_forcing (funext fun x ↦ (hf x).symm) hsmooth
    have hfL2 := memL2On_of_zeroAtInfty hW f
    have hsub := IsMassiveWeakSolutionOn.sub (B.ell k) (B.rho_measurable k)
      (B.rho_bounded k) hfL2 hfL2 hsol hsmooth'
    refine ⟨v - u, ?_, IsMassiveWeakSolutionOn.congr_forcing ?_ hsub⟩
    · refine Eventually.of_forall fun x ↦ ?_
      rw [H1Function.sub_toFun]
      change v.toFun x - w x = D.solution mu f x - w x
      rw [hv x]
      rfl
    · funext x
      simp
  have hzero := eq_zero_of_localMassiveWeakSolution_of_tendsto_cocompact B mu.2
    hcont hdecay hlocal
  exact ZeroAtInftyContinuousMap.ext fun x ↦ sub_eq_zero.mp (hzero x)

theorem exists_generator_of_c2_c0 {d : ℕ} {c rho : Vec d → ℝ}
    (B : MassiveCubeBounds c rho) (hc : ContDiff ℝ 1 c)
    (D : C0ResolventDatum (Vec d)) (hdense : ∀ mu, DenseRange (D.operator mu))
    (hD : IsWeakEllipticResolvent c rho D) (w g : C₀(Vec d, ℝ))
    (hw : ContDiff ℝ 2 (w : Vec d → ℝ))
    (hg : ∀ x, g x = coeffFluxDiv c w x / rho x) :
    let S := (D.isFellerKernelSemigroup_fellerKernelSemigroup hdense).c0Semigroup
    ∃ hm : w ∈ S.generatorDomain, S.generator ⟨w, hm⟩ = g := by
  classical
  let hF := D.isFellerKernelSemigroup_fellerKernelSemigroup hdense
  have mu : PositiveShift := ⟨1, by norm_num⟩
  set f : C₀(Vec d, ℝ) := ((mu : ℝ) • w - g) with hfdef
  have hf : ∀ x, f x = (mu : ℝ) * w x - coeffFluxDiv c w x / rho x := by
    intro x
    simp [hfdef, hg x]
  have hsol : D.solution mu f = w :=
    solution_eq_of_c2MassiveForcing B hc D hD mu w f hw hf
  have hres : hF.c0Semigroup.resolvent mu f = w := by
    rw [resolvent_c0Semigroup_eq_solution hdense hF rfl mu f, hsol]
  obtain ⟨hm, hgen⟩ :=
    generator_eq_of_resolvent_witness hF.c0Semigroup mu w f hres
  refine ⟨hm, ?_⟩
  rw [hgen, hfdef]
  abel


end SubdiffusiveProcess.Section10
