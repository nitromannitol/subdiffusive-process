module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumUniqueness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumBarrier
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.DomainMonotonicity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.CompactSupportCubeFamily

@[expose] public section

/-!
# Whole-space uniqueness for a dominated local solution that need not be continuous

The library's whole-space maximum principle
(`SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.eq_zero_of_localMassiveWeakSolution_of_tendsto_cocompact`)
is stated for a continuous decaying solution. Here the solution `w` is only an `H¹` representative
on each centred cube, but it is pointwise (or almost everywhere) dominated by a continuous
function `U` vanishing at infinity; this is all the truncation argument uses.
-/
open MeasureTheory Filter Set Topology Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.E7

variable {d : ℕ}

/-- **Pointwise dominated version.** -/
theorem ae_nonpos_of_local_solution_dominated_pointwise
    {c rho : Homogenization.Vec d → ℝ} (B : MassiveCubeBounds c rho) {mu : ℝ} (hmu : 0 < mu)
    {U w : Homogenization.Vec d → ℝ} (hcont : Continuous U)
    (hdecay : Tendsto U (cocompact (Homogenization.Vec d)) (nhds 0))
    (hdom : ∀ x, w x ≤ U x)
    (hlocal : ∀ k : ℕ, ∃ v : H1Function (cube d (k : ℤ)),
      v.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] w ∧
        IsMassiveWeakSolutionOn c rho mu (cube d (k : ℤ)) v (fun _ ↦ (0 : ℝ))) :
    ∀ᵐ x ∂(volume : Measure (Homogenization.Vec d)), w x ≤ 0 := by
  classical
  have hstep : ∀ eps : ℝ, 0 < eps → ∀ᵐ x ∂(volume : Measure (Homogenization.Vec d)), w x ≤ eps := by
    intro eps heps
    set K : Set (Homogenization.Vec d) := {x | eps ≤ U x} with hKdef
    have hKclosed : IsClosed K := isClosed_le continuous_const hcont
    have hnear : {t : ℝ | |t| < eps} ∈ nhds (0 : ℝ) := by
      simpa only [abs_lt] using! Ioo_mem_nhds (neg_lt_zero.mpr heps) heps
    obtain ⟨C, hCcompact, hC⟩ := mem_cocompact.mp (tendsto_def.mp hdecay _ hnear)
    have hKC : K ⊆ C := by
      intro x hx
      by_contra hxC
      have hxlt : |U x| < eps := hC hxC
      exact absurd hx (by simpa [hKdef] using! (abs_lt.mp hxlt).2)
    have hKcompact : IsCompact K := hCcompact.of_isClosed_subset hKclosed hKC
    obtain ⟨n, hKW⟩ := exists_nat_cube_superset hKcompact.isBounded
    set W : Set (Homogenization.Vec d) := cube d (n : ℤ) with hWdef
    have hW := Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (n : ℤ)
    have hWmeas : MeasurableSet W := hW.isOpen.measurableSet
    obtain ⟨v0, hv0ae, hv0sol⟩ := hlocal n
    set v : H1Function W := H1Function.ofAEEq v0 w hv0ae.symm with hvdef
    have hvfun : v.toFun = w := rfl
    have hvsol : IsMassiveWeakSolutionOn c rho mu W v (fun _ ↦ (0 : ℝ)) :=
      IsMassiveWeakSolutionOn.congr (u := v0) (v := v) hv0ae
        (Filter.Eventually.of_forall fun _ ↦ rfl) hv0sol
    obtain ⟨wt, hwf, hwg⟩ := exists_h1_max_sub_const hW v eps
    have hwfx : ∀ x, wt.toFun x = max (w x - eps) 0 := by
      intro x; simp only [hwf, hvfun]
    have hwzero : ∀ x, x ∉ K → wt.toFun x = 0 := by
      intro x hx
      have hxlt : U x < eps := lt_of_not_ge (by simpa [hKdef] using! hx)
      rw [hwfx x, max_eq_right (by linarith [hdom x])]
    obtain ⟨φ, hφ⟩ := memH10_of_compactSupport hW wt hKcompact hKW hwzero
    have hφfun : ∀ x, φ.toH1Function.toFun x = max (w x - eps) 0 := by
      intro x; rw [hφ, hwfx]
    have hφgrad : φ.toH1Function.grad =ᵐ[volume.restrict W] wt.grad :=
      Homogenization.Book.Ch03.H1Function.grad_ae_eq_of_toFun_ae_eq hW.isOpen
        (Filter.Eventually.of_forall fun x ↦ by rw [hφ])
    have hEq := hvsol φ
    have henNonneg : 0 ≤ ∫ x in W,
        vecDot (c x • v.grad x) (φ.toH1Function.grad x) ∂volume := by
      refine integral_nonneg_of_ae ?_
      filter_upwards [hφgrad, hwg, ae_restrict_mem hWmeas] with x hxg hxw hxW
      have hcx : 0 < c x := lt_of_lt_of_le (B.lam_pos n) (B.coeff_lower n x hxW)
      rw [hxg, hxw]
      by_cases hx : x ∈ {y | eps < v.toFun y}
      · rw [Set.indicator_of_mem hx, vecDot_smul_left]
        exact mul_nonneg hcx.le (vecNormSq_nonneg _)
      · rw [Set.indicator_of_notMem hx, vecDot_zero_right]
        exact le_rfl
    have hmassI : Integrable
        (fun x ↦ rho x * v.toFun x * φ.toH1Function.toFun x) (volume.restrict W) :=
      (integrableOn_mass_term (B.rho_measurable n) (B.rho_bounded n) v.memL2
        φ.toH1Function.memL2).integrable
    have hdefectNonneg : ∀ᵐ x ∂(volume.restrict W),
        0 ≤ rho x * v.toFun x * φ.toH1Function.toFun x := by
      filter_upwards [ae_restrict_mem hWmeas] with x hx
      have hrhox : 0 < rho x := lt_of_lt_of_le (B.rhoMin_pos n) (B.rho_lower n x hx)
      rw [hvfun, hφfun x]
      rcases le_or_gt (w x) eps with hle | hgt
      · rw [max_eq_right (by linarith)]; simp
      · rw [max_eq_left (by linarith)]
        have h2 : (0 : ℝ) < w x - eps := by linarith
        have h3 : 0 < w x := by linarith
        exact (mul_pos (mul_pos hrhox h3) h2).le
    have hEq0 : mu * ∫ x in W, rho x * v.toFun x * φ.toH1Function.toFun x ∂volume +
        ∫ x in W, vecDot (c x • v.grad x) (φ.toH1Function.grad x) ∂volume = 0 := by
      simpa using! hEq
    have hzero : (∫ x in W, rho x * v.toFun x * φ.toH1Function.toFun x ∂volume) = 0 := by
      refine le_antisymm ?_ (integral_nonneg_of_ae hdefectNonneg)
      nlinarith [henNonneg]
    have hdefectAe : (fun x ↦ rho x * v.toFun x * φ.toH1Function.toFun x)
        =ᵐ[volume.restrict W] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hdefectNonneg hmassI).1 hzero
    have hae : ∀ᵐ x ∂(volume.restrict W), w x ≤ eps := by
      filter_upwards [hdefectAe, ae_restrict_mem hWmeas] with x hx hxW
      by_contra hgt
      push_neg at hgt
      have hrhox : 0 < rho x := lt_of_lt_of_le (B.rhoMin_pos n) (B.rho_lower n x hxW)
      have h2 : (0 : ℝ) < w x - eps := by linarith
      have h3 : 0 < w x := by linarith
      have hpos : 0 < rho x * v.toFun x * φ.toH1Function.toFun x := by
        rw [hvfun, hφfun x, max_eq_left (by linarith)]
        exact mul_pos (mul_pos hrhox h3) h2
      have hz : rho x * v.toFun x * φ.toH1Function.toFun x = 0 := hx
      linarith
    -- outside the cube `w ≤ U < eps` pointwise
    have hnull : volume.restrict W {x | ¬ w x ≤ eps} = 0 := ae_iff.mp hae
    rw [Measure.restrict_apply' hWmeas] at hnull
    have hsub : {x | ¬ w x ≤ eps} ⊆ W := by
      intro x hx
      apply hKW
      show eps ≤ U x
      have : eps < w x := lt_of_not_ge hx
      linarith [hdom x]
    rw [Set.inter_eq_left.mpr hsub] at hnull
    exact ae_iff.mpr hnull
  have hall : ∀ᵐ x ∂(volume : Measure (Homogenization.Vec d)), ∀ m : ℕ, w x ≤ 1 / ((m : ℝ) + 1) :=
    ae_all_iff.mpr fun m => hstep _ (by positivity)
  filter_upwards [hall] with x hx
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  linarith [hx m]

/-- **Almost-everywhere dominated version.** -/
theorem ae_nonpos_of_local_solution_dominated
    {c rho : Homogenization.Vec d → ℝ} (B : MassiveCubeBounds c rho) {mu : ℝ} (hmu : 0 < mu)
    {U w : Homogenization.Vec d → ℝ} (hcont : Continuous U)
    (hdecay : Tendsto U (cocompact (Homogenization.Vec d)) (nhds 0))
    (hdom : ∀ᵐ x ∂(volume : Measure (Homogenization.Vec d)), w x ≤ U x)
    (hlocal : ∀ k : ℕ, ∃ v : H1Function (cube d (k : ℤ)),
      v.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] w ∧
        IsMassiveWeakSolutionOn c rho mu (cube d (k : ℤ)) v (fun _ ↦ (0 : ℝ))) :
    ∀ᵐ x ∂(volume : Measure (Homogenization.Vec d)), w x ≤ 0 := by
  set w' : Homogenization.Vec d → ℝ := fun x => min (w x) (U x) with hw'
  have hww' : w =ᵐ[volume] w' := by
    filter_upwards [hdom] with x hx
    simp [hw', hx]
  have hres : ∀ k : ℕ, w =ᵐ[volume.restrict (cube d (k : ℤ))] w' :=
    fun k => ae_restrict_of_ae hww'
  have hloc' : ∀ k : ℕ, ∃ v : H1Function (cube d (k : ℤ)),
      v.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] w' ∧
        IsMassiveWeakSolutionOn c rho mu (cube d (k : ℤ)) v (fun _ ↦ (0 : ℝ)) := by
    intro k
    obtain ⟨v, hv, hsol⟩ := hlocal k
    exact ⟨v, hv.trans (hres k), hsol⟩
  have h := ae_nonpos_of_local_solution_dominated_pointwise B hmu hcont hdecay
    (fun x => min_le_right _ _) hloc'
  filter_upwards [h, hww'] with x hx hx'
  rw [hx']
  exact hx

end SubdiffusiveProcess.E7
