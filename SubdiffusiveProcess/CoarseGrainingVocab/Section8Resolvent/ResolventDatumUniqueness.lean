import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumRepresentative
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.CompactSupportCubeFamily




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Metric
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-- A compact subset of `ℝᵈ` is contained in one member of the centred cube
exhaustion. -/
theorem exists_nat_cube_superset {K : Set (Vec d)} (hK : Bornology.IsBounded K) :
    ∃ n : ℕ, K ⊆ cube d (n : ℤ) := by
  obtain ⟨R, hR⟩ := hK.subset_ball (0 : Vec d)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * R) (by norm_num : (1 : ℝ) < 3)
  refine ⟨n, fun x hx ↦ ?_⟩
  have hxNorm : ‖x‖ < R := mem_ball_zero_iff.mp (hR hx)
  rw [cube, mem_openCubeSet_originCube_iff]
  intro i
  have hi : |x i| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  have hi' : -‖x‖ ≤ x i ∧ x i ≤ ‖x‖ := abs_le.mp hi
  have hpow : (3 : ℝ) ^ (n : ℤ) = (3 : ℝ) ^ n := zpow_natCast 3 n
  rw [hpow]
  constructor <;> linarith only [hn, hxNorm, hi'.1, hi'.2]

/-- **The one-sided whole-space maximum principle.**  Let `u` be continuous,
vanish at infinity, and solve `μ ρ u − ∇·(c∇u) = ρ f` weakly on every centred
cube.  If `f ≤ μ k₀` with `k₀ ≥ 0`, then `u ≤ k₀` everywhere.

The proof truncates at the strictly positive level `k₀ + ε`.  Decay makes
`{u ≥ k₀ + ε}` compact, so `(u − k₀ − ε)₊` vanishes off a compact subset of a
large cube and is an admissible `H¹₀` test function there
(`Homogenization.memH10_of_compactSupport`); no boundary trace theory is used.
Testing the equation against it makes the energy term nonnegative and forces
the mass term `∫ ρ (μ u − f) (u − k₀ − ε)₊` to vanish, whose integrand is
strictly positive wherever `u > k₀ + ε`. -/
theorem forall_le_of_localMassiveWeakSolution_of_tendsto_cocompact
    {c rho : Vec d → ℝ} (B : MassiveCubeBounds c rho)
    {mu : ℝ} (hmu : 0 < mu)
    {u f : Vec d → ℝ} (hcont : Continuous u)
    (hdecay : Tendsto u (cocompact (Vec d)) (nhds 0))
    (hfL2 : ∀ k : ℕ, MemL2On (cube d (k : ℤ)) f)
    (hlocal : ∀ k : ℕ, ∃ v : H1Function (cube d (k : ℤ)),
      v.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
        IsMassiveWeakSolutionOn c rho mu (cube d (k : ℤ)) v f)
    {k0 : ℝ} (hk0 : 0 ≤ k0) (hf : ∀ x, f x ≤ mu * k0) :
    ∀ x, u x ≤ k0 := by
  classical
  have hstep : ∀ eps : ℝ, 0 < eps → ∀ x, u x ≤ k0 + eps := by
    intro eps heps
    set lev : ℝ := k0 + eps with hlevdef
    have hlev : 0 < lev := by positivity
    -- the superlevel set `{u ≥ lev}` is compact
    set K : Set (Vec d) := {x | lev ≤ u x} with hKdef
    have hKclosed : IsClosed K := isClosed_le continuous_const hcont
    have hnear : {t : ℝ | |t| < lev} ∈ nhds (0 : ℝ) := by
      simpa only [abs_lt] using Ioo_mem_nhds (neg_lt_zero.mpr hlev) hlev
    obtain ⟨C, hCcompact, hC⟩ := mem_cocompact.mp (tendsto_def.mp hdecay _ hnear)
    have hKC : K ⊆ C := by
      intro x hx
      by_contra hxC
      have hxlt : |u x| < lev := hC hxC
      exact absurd hx (by simpa [hKdef] using (abs_lt.mp hxlt).2)
    have hKcompact : IsCompact K := hCcompact.of_isClosed_subset hKclosed hKC
    obtain ⟨n, hKW⟩ := exists_nat_cube_superset hKcompact.isBounded
    set W : Set (Vec d) := cube d (n : ℤ) with hWdef
    have hW := Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (n : ℤ)
    have hWmeas : MeasurableSet W := hW.isOpen.measurableSet
    -- the local solution, re-based on `u` itself
    obtain ⟨v0, hv0ae, hv0sol⟩ := hlocal n
    set v : H1Function W := H1Function.ofAEEq v0 u hv0ae.symm with hvdef
    have hvfun : v.toFun = u := rfl
    have hvsol : IsMassiveWeakSolutionOn c rho mu W v f :=
      IsMassiveWeakSolutionOn.congr (u := v0) (v := v) hv0ae
        (Filter.Eventually.of_forall fun _ ↦ rfl) hv0sol
    -- the truncation at the strictly positive level `lev`
    obtain ⟨w, hwf, hwg⟩ := exists_h1_max_sub_const hW v lev
    have hwfx : ∀ x, w.toFun x = max (u x - lev) 0 := by
      intro x; simp only [hwf, hvfun]
    have hwzero : ∀ x, x ∉ K → w.toFun x = 0 := by
      intro x hx
      have hxlt : u x < lev := lt_of_not_ge (by simpa [hKdef] using hx)
      rw [hwfx x, max_eq_right (by linarith)]
    obtain ⟨φ, hφ⟩ := memH10_of_compactSupport hW w hKcompact hKW hwzero
    have hφfun : ∀ x, φ.toH1Function.toFun x = max (u x - lev) 0 := by
      intro x; rw [hφ, hwfx]
    have hφgrad : φ.toH1Function.grad =ᵐ[volume.restrict W] w.grad :=
      Homogenization.Book.Ch03.H1Function.grad_ae_eq_of_toFun_ae_eq hW.isOpen
        (Filter.Eventually.of_forall fun x ↦ by rw [hφ])
    -- the tested equation
    have hEq := hvsol φ
    -- the energy term is nonnegative
    have henNonneg : 0 ≤ ∫ x in W,
        vecDot (c x • v.grad x) (φ.toH1Function.grad x) ∂volume := by
      refine integral_nonneg_of_ae ?_
      filter_upwards [hφgrad, hwg, ae_restrict_mem hWmeas] with x hxg hxw hxW
      have hcx : 0 < c x := lt_of_lt_of_le (B.lam_pos n) (B.coeff_lower n x hxW)
      rw [hxg, hxw]
      by_cases hx : x ∈ {y | lev < v.toFun y}
      · rw [Set.indicator_of_mem hx, vecDot_smul_left]
        exact mul_nonneg hcx.le (vecNormSq_nonneg _)
      · rw [Set.indicator_of_notMem hx, vecDot_zero_right]
        exact le_rfl
    -- the mass defect is nonnegative and integrates to zero
    have hmassInt : IntegrableOn
        (fun x ↦ rho x * v.toFun x * φ.toH1Function.toFun x) W :=
      integrableOn_mass_term (B.rho_measurable n) (B.rho_bounded n) v.memL2
        φ.toH1Function.memL2
    have hrhsInt : IntegrableOn
        (fun x ↦ rho x * f x * φ.toH1Function.toFun x) W :=
      integrableOn_mass_term (B.rho_measurable n) (B.rho_bounded n) (hfL2 n)
        φ.toH1Function.memL2
    have hmassI : Integrable
        (fun x ↦ rho x * v.toFun x * φ.toH1Function.toFun x)
        (volume.restrict W) := hmassInt.integrable
    have hrhsI : Integrable
        (fun x ↦ rho x * f x * φ.toH1Function.toFun x)
        (volume.restrict W) := hrhsInt.integrable
    have hdefectI : Integrable
        (fun x ↦ mu * (rho x * v.toFun x * φ.toH1Function.toFun x) -
          rho x * f x * φ.toH1Function.toFun x) (volume.restrict W) :=
      (hmassI.const_mul mu).sub hrhsI
    have hdefectNonneg : ∀ᵐ x ∂(volume.restrict W),
        0 ≤ mu * (rho x * v.toFun x * φ.toH1Function.toFun x) -
          rho x * f x * φ.toH1Function.toFun x := by
      filter_upwards [ae_restrict_mem hWmeas] with x hx
      have hrhox : 0 < rho x := lt_of_lt_of_le (B.rhoMin_pos n) (B.rho_lower n x hx)
      rw [hvfun, hφfun x]
      rcases le_or_gt (u x) lev with hle | hgt
      · rw [max_eq_right (by linarith)]; simp
      · rw [max_eq_left (by linarith)]
        have hfx : f x ≤ mu * k0 := hf x
        have h1 : mu * k0 + mu * eps ≤ mu * u x := by
          have : mu * lev ≤ mu * u x := by
            exact mul_le_mul_of_nonneg_left hgt.le hmu.le
          simpa [hlevdef, mul_add] using this
        have h2 : (0 : ℝ) < u x - lev := by linarith
        have h3 : 0 < mu * u x - f x := by nlinarith [mul_pos hmu heps]
        nlinarith [mul_pos (mul_pos hrhox h3) h2]
    have hdefectNonnegInt : 0 ≤ ∫ x in W,
        (mu * (rho x * v.toFun x * φ.toH1Function.toFun x) -
          rho x * f x * φ.toH1Function.toFun x) ∂volume :=
      integral_nonneg_of_ae hdefectNonneg
    have hdefectZero : (∫ x in W,
        (mu * (rho x * v.toFun x * φ.toH1Function.toFun x) -
          rho x * f x * φ.toH1Function.toFun x) ∂volume) = 0 := by
      refine le_antisymm ?_ hdefectNonnegInt
      rw [integral_sub (hmassI.const_mul mu) hrhsI, integral_const_mul]
      linarith [hEq, henNonneg]
    have hdefectAe : (fun x ↦ mu * (rho x * v.toFun x * φ.toH1Function.toFun x) -
        rho x * f x * φ.toH1Function.toFun x) =ᵐ[volume.restrict W] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hdefectNonneg hdefectI).1 hdefectZero
    -- hence `u ≤ lev` a.e. on the cube
    have hae : ∀ᵐ x ∂(volume.restrict W), u x ≤ lev := by
      filter_upwards [hdefectAe, ae_restrict_mem hWmeas] with x hx hxW
      by_contra hgt
      push_neg at hgt
      have hrhox : 0 < rho x := lt_of_lt_of_le (B.rhoMin_pos n) (B.rho_lower n x hxW)
      have hfx : f x ≤ mu * k0 := hf x
      have h1 : mu * k0 + mu * eps ≤ mu * u x := by
        have : mu * lev ≤ mu * u x := mul_le_mul_of_nonneg_left hgt.le hmu.le
        simpa [hlevdef, mul_add] using this
      have h2 : (0 : ℝ) < u x - lev := by linarith
      have h3 : 0 < mu * u x - f x := by nlinarith [mul_pos hmu heps]
      have hpos : 0 < mu * (rho x * v.toFun x * φ.toH1Function.toFun x) -
          rho x * f x * φ.toH1Function.toFun x := by
        rw [hvfun, hφfun x, max_eq_left (by linarith)]
        nlinarith [mul_pos (mul_pos hrhox h3) h2]
      have hzero : mu * (rho x * v.toFun x * φ.toH1Function.toFun x) -
          rho x * f x * φ.toH1Function.toFun x = 0 := hx
      linarith
    -- upgrade to every point
    intro x
    by_contra hx
    push_neg at hx
    have hxK : x ∈ K := by simpa [hKdef] using hx.le
    have hxW : x ∈ W := hKW hxK
    set S : Set (Vec d) := {y | lev < u y} ∩ W with hSdef
    have hSopen : IsOpen S := (isOpen_lt continuous_const hcont).inter hW.isOpen
    have hSzero : volume S = 0 := by
      have hnull : volume.restrict W {y | lev < u y} = 0 := by
        have := ae_iff.mp hae
        simpa using this
      have hSrestrict : volume.restrict W S = volume S := by
        rw [Measure.restrict_apply hSopen.measurableSet]
        congr 1
        exact Set.inter_eq_self_of_subset_left Set.inter_subset_right
      rw [← hSrestrict]
      exact measure_mono_null Set.inter_subset_left hnull
    have hSne : S.Nonempty := ⟨x, hx, hxW⟩
    exact absurd hSzero (ne_of_gt (hSopen.measure_pos volume hSne))
  intro x
  exact le_of_forall_pos_le_add fun eps heps ↦ hstep eps heps x

/-- The negative of a local massive weak solution solves with the negated
forcing. -/
theorem neg_localMassiveWeakSolution {c rho : Vec d → ℝ} {mu : ℝ}
    {u f : Vec d → ℝ}
    (hlocal : ∀ k : ℕ, ∃ v : H1Function (cube d (k : ℤ)),
      v.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
        IsMassiveWeakSolutionOn c rho mu (cube d (k : ℤ)) v f) :
    ∀ k : ℕ, ∃ v : H1Function (cube d (k : ℤ)),
      v.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] (fun y ↦ -u y) ∧
        IsMassiveWeakSolutionOn c rho mu (cube d (k : ℤ)) v (fun y ↦ -f y) := by
  intro k
  obtain ⟨v, hvae, hvsol⟩ := hlocal k
  refine ⟨-v, ?_, ?_⟩
  · filter_upwards [hvae] with x hx
    simp only [H1Function.neg_toFun, hx]
  · exact isMassiveWeakSolutionOn_neg hvsol



theorem forall_abs_le_of_localMassiveWeakSolution_of_tendsto_cocompact
    {c rho : Vec d → ℝ} (B : MassiveCubeBounds c rho)
    {mu : ℝ} (hmu : 0 < mu)
    {u f : Vec d → ℝ} (hcont : Continuous u)
    (hdecay : Tendsto u (cocompact (Vec d)) (nhds 0))
    (hfL2 : ∀ k : ℕ, MemL2On (cube d (k : ℤ)) f)
    (hlocal : ∀ k : ℕ, ∃ v : H1Function (cube d (k : ℤ)),
      v.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
        IsMassiveWeakSolutionOn c rho mu (cube d (k : ℤ)) v f)
    {k0 : ℝ} (hk0 : 0 ≤ k0) (hf : ∀ x, |f x| ≤ mu * k0) :
    ∀ x, |u x| ≤ k0 := by
  have hup := forall_le_of_localMassiveWeakSolution_of_tendsto_cocompact B hmu
    hcont hdecay hfL2 hlocal hk0 (fun x ↦ le_trans (le_abs_self _) (hf x))
  have hdown := forall_le_of_localMassiveWeakSolution_of_tendsto_cocompact B hmu
    hcont.neg (by simpa using hdecay.neg) (fun k ↦ (hfL2 k).neg)
    (neg_localMassiveWeakSolution hlocal) hk0
    (fun x ↦ le_trans (neg_le_abs _) (hf x))
  intro x
  exact abs_le.2 ⟨by linarith [hdown x], hup x⟩

/-- **Whole-space positivity.**  A nonnegative datum gives a nonnegative
solution. -/
theorem forall_nonneg_of_localMassiveWeakSolution_of_tendsto_cocompact
    {c rho : Vec d → ℝ} (B : MassiveCubeBounds c rho)
    {mu : ℝ} (hmu : 0 < mu)
    {u f : Vec d → ℝ} (hcont : Continuous u)
    (hdecay : Tendsto u (cocompact (Vec d)) (nhds 0))
    (hfL2 : ∀ k : ℕ, MemL2On (cube d (k : ℤ)) f)
    (hlocal : ∀ k : ℕ, ∃ v : H1Function (cube d (k : ℤ)),
      v.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
        IsMassiveWeakSolutionOn c rho mu (cube d (k : ℤ)) v f)
    (hf : ∀ x, 0 ≤ f x) :
    ∀ x, 0 ≤ u x := by
  have hdown := forall_le_of_localMassiveWeakSolution_of_tendsto_cocompact B hmu
    hcont.neg (by simpa using hdecay.neg) (fun k ↦ (hfL2 k).neg)
    (neg_localMassiveWeakSolution hlocal) le_rfl
    (fun x ↦ by simpa using neg_nonpos.mpr (hf x))
  intro x
  linarith [hdown x]

/-- **Whole-space uniqueness for the massive resolvent equation.**  A continuous
function vanishing at infinity that solves `μ ρ u − ∇·(c∇u) = 0` weakly on every
centred cube vanishes identically. -/
theorem eq_zero_of_localMassiveWeakSolution_of_tendsto_cocompact
    {c rho : Vec d → ℝ} (B : MassiveCubeBounds c rho)
    {mu : ℝ} (hmu : 0 < mu)
    {u : Vec d → ℝ} (hcont : Continuous u)
    (hdecay : Tendsto u (cocompact (Vec d)) (nhds 0))
    (hlocal : ∀ k : ℕ, ∃ v : H1Function (cube d (k : ℤ)),
      v.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
        IsMassiveWeakSolutionOn c rho mu (cube d (k : ℤ)) v (fun _ ↦ (0 : ℝ))) :
    ∀ x, u x = 0 := by
  have hzeroL2 : ∀ k : ℕ, MemL2On (cube d (k : ℤ)) (fun _ ↦ (0 : ℝ)) := by
    intro k
    simp
  have habs := forall_abs_le_of_localMassiveWeakSolution_of_tendsto_cocompact B
    hmu hcont hdecay hzeroL2 hlocal le_rfl (fun x ↦ by simp)
  intro x
  have := habs x
  simpa using abs_nonpos_iff.mp (by simpa using this)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
