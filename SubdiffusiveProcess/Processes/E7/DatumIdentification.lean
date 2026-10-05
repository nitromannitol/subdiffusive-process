module

public import SubdiffusiveProcess.Processes.E7.LocalWeakEquation
public import SubdiffusiveProcess.Processes.E7.AeLimits
public import SubdiffusiveProcess.Processes.E7.TruncationUniqueness
public import SubdiffusiveProcess.Processes.ResolventSolutionUniqueness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.MassiveMaximumPrinciple
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumInterface
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.Windows
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.C0CompactSupportExtension

@[expose] public section

/-!
# Identification of the `C₀` resolvent datum with the resolvent of the gradient form

For a positive continuous pair `(c, ρ)` let `D` be a `C₀` resolvent datum that is a weak elliptic
resolvent for `(c, ρ)` and `G` the resolvent of the closure of the smooth weighted gradient form
on `L²(ρ dx)`. Then `D_μ f = G_μ f` almost everywhere for every continuous compactly supported
`f`.

For `f ≥ 0` the centred-cube Dirichlet solutions `v_n ∈ H¹₀` satisfy `0 ≤ v_n ≤ D_μ f` (weak
comparison) and converge to `G_μ f` in `L²(ρ)` (Galerkin/Céa), so `0 ≤ G_μ f ≤ D_μ f`. The
difference `D_μ f - G_μ f` is a nonnegative local solution of the homogeneous equation dominated
by the continuous function `D_μ f` vanishing at infinity, hence `≤ 0` by truncation. The signed
case follows by linearity.
-/
open MeasureTheory Filter Set Topology Homogenization MarkovProcess
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal CompactlySupported ZeroAtInfty
noncomputable section
namespace SubdiffusiveProcess.E7

variable {d : ℕ}

/-- The support of a test function lies in every sufficiently large centred cube. -/
theorem exists_cube_of_testFn {φ : St d → ℝ} (hφ : φ ∈ testFns d) :
    ∃ n0 : ℕ, ∀ n ≥ n0, tsupport φ ⊆ cube d (n : ℤ) := by
  obtain ⟨n0, hn0⟩ := exists_nat_cube_superset
    (show IsCompact (tsupport φ) from hφ.2).isBounded
  exact ⟨n0, fun n hn => hn0.trans
    (Section6ExcessDecay.cube_subset_cube_of_le (by exact_mod_cast hn))⟩

theorem datum_eq_resolvent_of_nonneg [NeZero d]
    {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x)
    {D : C0ResolventDatum (Homogenization.Vec d)} (hD : IsWeakEllipticResolvent c ρ D)
    (mu : Semigroup.PositiveShift)
    {G : Lp ℝ 2 (wm ρ) →L[ℝ] Lp ℝ 2 (wm ρ)}
    (hG : _root_.SubdiffusiveProcess.DirichletForm.IsResolvent (gradClosedForm hc hρ hcpos hρpos) (mu : ℝ) G)
    (f : C_c(Homogenization.Vec d, ℝ)) (hf : ∀ x, 0 ≤ f x)
    (hfL2 : MemLp (fun x => f x) 2 (wm ρ)) :
    (fun x => D.solution mu (compactSupportToC0 f) x) =ᵐ[volume]
      ⇑(G (hfL2.toLp (fun x => f x))) := by
  classical
  have hμ : 0 < (mu : ℝ) := mu.property
  obtain ⟨B⟩ := SubdiffusiveProcess.nonempty_massiveCubeBounds_of_continuous_pos
    hc hρ hcpos hρpos
  obtain ⟨uc, huc⟩ := exists_massiveCubeSolutionFamily_of_compactSupport B hμ f
  have hWd : ∀ n : ℕ, IsOpenBoundedConvexDomain (cube d (n : ℤ)) := fun n =>
    Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (n : ℤ)
  have hWo : ∀ n : ℕ, IsOpen (cube d (n : ℤ)) := fun n => (hWd n).isOpen
  have hWm : ∀ n : ℕ, MeasurableSet (cube d (n : ℤ)) := fun n => (hWo n).measurableSet
  have hWb : ∀ n : ℕ, Bornology.IsBounded (cube d (n : ℤ)) := fun n =>
    (hWd n).isBoundedDomain.isBounded
  have hgal := galerkin_tendsto hc hρ hcpos hρpos hμ hG hfL2 hWo hWb
    (fun φ hφ => exists_cube_of_testFn hφ) uc (fun n φ => (huc n).1 φ)
  set g := G (hfL2.toLp (fun x => f x)) with hg
  set U := D.solution mu (compactSupportToC0 f) with hU
  have hUnn : ∀ x, 0 ≤ U x := D.solution_nonneg mu _ (fun x => hf x)
  have hUcont : Continuous U := U.continuous
  have hUdecay : Tendsto U (cocompact _) (nhds 0) := zero_at_infty U
  have hfL2on : ∀ n : ℕ, MemL2On (cube d (n : ℤ)) (fun x => f x) := fun n =>
    (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport).restrict _
  -- comparison of the cube solutions with the datum
  have hcmp : ∀ n : ℕ, (uc n).toH1Function.toFun ≤ᵐ[volume.restrict (cube d (n : ℤ))] U := by
    intro n
    obtain ⟨v0, hv0, hsol0⟩ := hD mu (compactSupportToC0 f) (cube d (n : ℤ)) (hWd n)
    have hae : U =ᵐ[volume.restrict (cube d (n : ℤ))] v0.toFun := by
      filter_upwards [ae_restrict_mem (hWm n)] with x hx
      exact (hv0 x hx).symm
    set v : H1Function (cube d (n : ℤ)) := H1Function.ofAEEq v0 U hae with hv
    have hsol : IsMassiveWeakSolutionOn c ρ (mu : ℝ) (cube d (n : ℤ)) v
        (fun x => compactSupportToC0 f x) :=
      IsMassiveWeakSolutionOn.congr (u := v0) (v := v) hae.symm
        (Filter.Eventually.of_forall fun _ => rfl) hsol0
    exact ae_le_of_massiveWeakSolutions_of_nonneg_comparison (hWd n) hμ (B.rhoMin_pos n)
      (B.lam_pos n) (B.ell n) (B.coeff_lower n) (B.rho_measurable n) (B.rho_lower n)
      (B.rho_bounded n) (fun x => hUnn x) (huc n).1 hsol
  have hcmp0 : ∀ n : ℕ, 0 ≤ᵐ[volume.restrict (cube d (n : ℤ))]
      (uc n).toH1Function.toFun := fun n =>
    ae_nonneg_of_isMassiveWeakSolutionOn (hWd n) hμ (B.rhoMin_pos n) (B.lam_pos n)
      (B.coeff_lower n) (B.rho_measurable n) (B.rho_lower n) (B.rho_bounded n) (hfL2on n)
      (fun x _ => hf x) (huc n).1
  have hzext : ∀ n : ℕ, (⇑(zextL hρ (hWo n) (hWb n) (uc n))) =ᵐ[volume]
      (uc n).zeroExtension := fun n =>
    ae_volume_of_ae_wm hρ hρpos (MemLp.coeFn_toLp _)
  have hzle : ∀ n : ℕ, ∀ᵐ x ∂(volume : Measure (St d)),
      zextL hρ (hWo n) (hWb n) (uc n) x ≤ U x := by
    intro n
    filter_upwards [hzext n, (ae_restrict_iff' (hWm n)).1 (hcmp n)] with x hx hx2
    rw [hx]
    by_cases hxW : x ∈ cube d (n : ℤ)
    · rw [(uc n).zeroExtension_apply_of_mem hxW]
      exact hx2 hxW
    · rw [(uc n).zeroExtension_apply_of_not_mem hxW]
      exact hUnn x
  have hzge : ∀ n : ℕ, ∀ᵐ x ∂(volume : Measure (St d)),
      0 ≤ zextL hρ (hWo n) (hWb n) (uc n) x := by
    intro n
    filter_upwards [hzext n, (ae_restrict_iff' (hWm n)).1 (hcmp0 n)] with x hx hx2
    rw [hx]
    by_cases hxW : x ∈ cube d (n : ℤ)
    · rw [(uc n).zeroExtension_apply_of_mem hxW]
      exact hx2 hxW
    · rw [(uc n).zeroExtension_apply_of_not_mem hxW]
  have hg_le : g ≤ᵐ[wm ρ] U :=
    ae_le_of_tendsto_Lp hgal hUcont.aestronglyMeasurable
      (fun n => ae_wm_of_ae_volume hρ hρpos (hzle n))
  have hg_ge : (fun _ => (0 : ℝ)) ≤ᵐ[wm ρ] g := by
    have h := ae_le_of_tendsto_Lp (hgal.neg) (B := fun _ => (0 : ℝ))
      aestronglyMeasurable_const (fun n => by
        filter_upwards [Lp.coeFn_neg (zextL hρ (hWo n) (hWb n) (uc n)),
          ae_wm_of_ae_volume hρ hρpos (hzge n)] with x hx hx2
        rw [hx]
        simpa using hx2)
    filter_upwards [h, Lp.coeFn_neg g] with x hx hx2
    rw [hx2] at hx
    simpa using hx
  have hg_le' : ∀ᵐ x ∂(volume : Measure (St d)), g x ≤ U x :=
    ae_volume_of_ae_wm hρ hρpos hg_le
  have hg_ge' : ∀ᵐ x ∂(volume : Measure (St d)), 0 ≤ g x :=
    ae_volume_of_ae_wm hρ hρpos hg_ge
  -- the difference is a local solution of the homogeneous equation
  have hloc : ∀ k : ℕ, ∃ v : H1Function (cube d (k : ℤ)),
      v.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] (fun x => U x - g x) ∧
        IsMassiveWeakSolutionOn c ρ (mu : ℝ) (cube d (k : ℤ)) v (fun _ => (0 : ℝ)) := by
    intro k
    obtain ⟨v1, hv1, hs1⟩ := hD mu (compactSupportToC0 f) (cube d (k : ℤ)) (hWd k)
    set v2 := h1OfDomain hc hρ hcpos hρpos (hWo k) (hWb k) g (hG.mem_domain _) with hv2
    have hs2 : IsMassiveWeakSolutionOn c ρ (mu : ℝ) (cube d (k : ℤ)) v2 (fun x => f x) := by
      intro φ
      exact weak_equation_of_resolvent hc hρ hcpos hρpos hG (hWo k) (hWb k) hfL2 φ
    have hsub := IsMassiveWeakSolutionOn.sub (B.ell k) (B.rho_measurable k) (B.rho_bounded k)
      (hfL2on k) (hfL2on k) hs1 hs2
    refine ⟨v1 - v2, ?_, IsMassiveWeakSolutionOn.congr_forcing ?_ hsub⟩
    · filter_upwards [ae_restrict_mem (hWm k)] with x hx
      simp only [H1Function.sub_toFun, hv1 x hx]
      rfl
    · funext x
      simp
  have hdom : ∀ᵐ x ∂(volume : Measure (St d)), U x - g x ≤ U x := by
    filter_upwards [hg_ge'] with x hx
    linarith
  have hnp := ae_nonpos_of_local_solution_dominated B hμ hUcont hUdecay hdom hloc
  filter_upwards [hnp, hg_le'] with x h1 h2
  linarith

/-- The positive part of a continuous compactly supported function. -/
def ccPos (f : C_c(Homogenization.Vec d, ℝ)) : C_c(Homogenization.Vec d, ℝ) where
  toFun x := max (f x) 0
  continuous_toFun := f.continuous.max continuous_const
  hasCompactSupport' := f.hasCompactSupport.comp_left (g := fun t : ℝ => max t 0) (by simp)

theorem ccPos_apply (f : C_c(Homogenization.Vec d, ℝ)) (x : Homogenization.Vec d) :
    ccPos f x = max (f x) 0 := rfl

theorem eq_ccPos_sub (f : C_c(Homogenization.Vec d, ℝ)) : f = ccPos f - ccPos (-f) := by
  ext x
  simp only [ccPos_apply, CompactlySupportedContinuousMap.coe_sub, Pi.sub_apply,
    CompactlySupportedContinuousMap.coe_neg, Pi.neg_apply]
  rcases le_total 0 (f x) with h | h
  · simp [h]
  · simp [h]

/-- **Identification of the datum with the resolvent of the gradient form**, for every continuous
compactly supported datum. -/
theorem datum_eq_resolvent [NeZero d]
    {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x)
    {D : C0ResolventDatum (Homogenization.Vec d)} (hD : IsWeakEllipticResolvent c ρ D)
    (mu : Semigroup.PositiveShift)
    {G : Lp ℝ 2 (wm ρ) →L[ℝ] Lp ℝ 2 (wm ρ)}
    (hG : _root_.SubdiffusiveProcess.DirichletForm.IsResolvent (gradClosedForm hc hρ hcpos hρpos) (mu : ℝ) G)
    (f : C_c(Homogenization.Vec d, ℝ)) (hfL2 : MemLp (fun x => f x) 2 (wm ρ)) :
    (fun x => D.solution mu (compactSupportToC0 f) x) =ᵐ[volume]
      ⇑(G (hfL2.toLp (fun x => f x))) := by
  have hp : MemLp (fun x => ccPos f x) 2 (wm ρ) :=
    memLp_wm_of_cont_compact hρ (ccPos f).continuous (ccPos f).hasCompactSupport
  have hm : MemLp (fun x => ccPos (-f) x) 2 (wm ρ) :=
    memLp_wm_of_cont_compact hρ (ccPos (-f)).continuous (ccPos (-f)).hasCompactSupport
  have h1 := datum_eq_resolvent_of_nonneg hc hρ hcpos hρpos hD mu hG (ccPos f)
    (fun x => le_max_right _ _) hp
  have h2 := datum_eq_resolvent_of_nonneg hc hρ hcpos hρpos hD mu hG (ccPos (-f))
    (fun x => le_max_right _ _) hm
  have hfe := eq_ccPos_sub f
  have hD' : ∀ x, D.solution mu (compactSupportToC0 f) x =
      D.solution mu (compactSupportToC0 (ccPos f)) x -
        D.solution mu (compactSupportToC0 (ccPos (-f))) x := by
    intro x
    have : compactSupportToC0 f = compactSupportToC0 (ccPos f) - compactSupportToC0 (ccPos (-f)) := by
      rw [← map_sub, ← hfe]
    rw [this]
    have hh := (D.linearMap mu).map_sub (compactSupportToC0 (ccPos f))
      (compactSupportToC0 (ccPos (-f)))
    exact congrArg (fun z => z x) hh
  have hG' : hfL2.toLp (fun x => f x) =
      hp.toLp (fun x => ccPos f x) - hm.toLp (fun x => ccPos (-f) x) := by
    apply Lp.ext
    filter_upwards [hfL2.coeFn_toLp, hp.coeFn_toLp, hm.coeFn_toLp,
      Lp.coeFn_sub (hp.toLp (fun x => ccPos f x)) (hm.toLp (fun x => ccPos (-f) x))]
      with x h1 h2 h3 h4
    rw [h1, h4, Pi.sub_apply, h2, h3]
    have := congrArg (fun z : C_c(Homogenization.Vec d, ℝ) => z x) hfe
    simpa using this
  rw [hG', map_sub]
  filter_upwards [h1, h2, ae_volume_of_ae_wm hρ hρpos (Lp.coeFn_sub
    (G (hp.toLp fun x => ccPos f x)) (G (hm.toLp fun x => ccPos (-f) x)))] with x hx1 hx2 hx3
  rw [hD' x, hx3, Pi.sub_apply, ← hx1, ← hx2]

end SubdiffusiveProcess.E7
