import SubdiffusiveProcess.Paper.lem_extension_cell_moment_uniform_root
import SubdiffusiveProcess.Paper.thm_c1_response_negative_moment
import SubdiffusiveProcess.Paper.rem_bank_response_moments
import SubdiffusiveProcess.Sobolev.UnitResponseSource
import SubdiffusiveProcess.Sobolev.NativeRepresentativeData
import SubdiffusiveProcess.Lane2.MeshGluing
import SubdiffusiveProcess.Lane2.OddExtension
import SubdiffusiveProcess.Sobolev.MeshResponseTest
import SubdiffusiveProcess.Sobolev.BoundaryGrowthEnergy
import SubdiffusiveProcess.Probability.FiniteWeightedMoments

/-! The reciprocal moments of the quadratic form `⟨f, G_N^Q f⟩` of a nonzero smooth source on an
arbitrary cube `Q`: a triadic subcube `Q'` of `Q` on which `f` keeps its sign carries a harmonic
mesh interpolant of a bump; its zero extension is an admissible competitor in the dual formula on
`Q`, with source pairing bounded below by half the pairing with the bump, and its energy is a
finite weighted sum of cell extension energies with model-uniform `L^p` envelopes at every cutoff. -/

open MeasureTheory Set TopologicalSpace Homogenization SubdiffusiveProcess
open SubdiffusiveProcess.Lane4 SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal BigOperators ContDiff Distributions

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Paper
noncomputable section

/-- A nonzero test function keeps its sign on a triadic-side cube inside the domain. -/
theorem aux_lem_response_reciprocal_negative_subcube {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (f : 𝓓(Ω, ℝ)) (hf : f ≠ 0) :
    ∃ (x0 : SpatialCoordinates d) (k : ℕ),
      centeredCube x0 ((3 : ℝ) ^ (-(k : ℤ))) (zpow_pos zero_lt_three _) ≤ Ω ∧
      ∀ x ∈ (centeredCube x0 ((3 : ℝ) ^ (-(k : ℤ))) (zpow_pos zero_lt_three _) :
        Set (SpatialCoordinates d)), 0 < f x0 * f x := by
  obtain ⟨x0, hx0⟩ : ∃ x, f x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (DFunLike.ext _ _ h)
  have hx0Ω : x0 ∈ (Ω : Set (SpatialCoordinates d)) :=
    f.tsupport_subset (subset_tsupport _ hx0)
  have hcont : Continuous f := f.contDiff.continuous
  have hopen : IsOpen ({x | 0 < f x0 * f x} ∩ (Ω : Set (SpatialCoordinates d))) :=
    (isOpen_lt continuous_const (continuous_const.mul hcont)).inter Ω.isOpen
  have hmem : x0 ∈ {x | 0 < f x0 * f x} ∩ (Ω : Set (SpatialCoordinates d)) :=
    ⟨mul_self_pos.2 hx0, hx0Ω⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen x0 hmem
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 3 : ℝ) < 1)
  have hs : (3 : ℝ) ^ (-(k : ℤ)) = (1 / 3) ^ k := by
    rw [zpow_neg, zpow_natCast, one_div, inv_pow]
  have hsub : Metric.ball x0 ((3 : ℝ) ^ (-(k : ℤ)) / 2) ⊆ Metric.ball x0 ε := by
    apply Metric.ball_subset_ball
    rw [hs]
    have : (0 : ℝ) < (1 / 3) ^ k := by positivity
    linarith
  refine ⟨x0, k, ?_, ?_⟩
  · intro x hx
    exact (hball (hsub hx)).2
  · intro x hx
    exact (hball (hsub hx)).1

/-- A smooth bump of side at most `s`, supported in the cube of side `s` about `x0`. -/
def aux_lem_response_reciprocal_negative_bump {d : ℕ} (x0 : SpatialCoordinates d) (s : ℝ)
    (hs : 0 < s) : ContDiffBump x0 :=
  ⟨s / 8, s / 4, by positivity, by linarith⟩

/-- The bump, scaled by a constant, as a test function on the cube. -/
def aux_lem_response_reciprocal_negative_test {d : ℕ} (x0 : SpatialCoordinates d) (s : ℝ)
    (hs : 0 < s) (c : ℝ) : 𝓓(centeredCube x0 s hs, ℝ) :=
  ⟨fun x => c * aux_lem_response_reciprocal_negative_bump x0 s hs x,
    contDiff_const.mul (aux_lem_response_reciprocal_negative_bump x0 s hs).contDiff,
    (aux_lem_response_reciprocal_negative_bump x0 s hs).hasCompactSupport.mul_left, by
      refine (tsupport_mul_subset_right (f := fun _ : SpatialCoordinates d => c)).trans ?_
      rw [(aux_lem_response_reciprocal_negative_bump x0 s hs).tsupport_eq]
      exact Metric.closedBall_subset_ball (by
        change s / 4 < s / 2
        linarith)⟩

/-- The `L²` pairing of a test function with a test function is the integral of the product. -/
theorem aux_lem_response_reciprocal_negative_inner_test {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (f g : 𝓓(Ω, ℝ)) :
    inner ℝ (testL2 f) (testL2 g) = ∫ x in (Ω : Set (SpatialCoordinates d)), f x * g x := by
  rw [L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial]
  refine integral_congr_ae ?_
  filter_upwards [testL2_coeFn f, testL2_coeFn g] with x hf hg
  rw [hf, hg, mul_comm]

/-- The pairing of a test function with the extended bump is positive when the test function keeps
its sign on the cube of the bump. -/
theorem aux_lem_response_reciprocal_negative_pairing_pos {d : ℕ}
    {Ω : Opens (SpatialCoordinates d)} (f : 𝓓(Ω, ℝ)) (x0 : SpatialCoordinates d) (s : ℝ)
    (hs : 0 < s) (hsub : centeredCube x0 s hs ≤ Ω) (hf0 : f x0 ≠ 0)
    (hsign : ∀ x ∈ (centeredCube x0 s hs : Set (SpatialCoordinates d)), 0 < f x0 * f x) :
    0 < inner ℝ (testL2 f)
      (testL2 (extendTest hsub (aux_lem_response_reciprocal_negative_test x0 s hs (f x0)))) := by
  set ψ := aux_lem_response_reciprocal_negative_bump x0 s hs with hψ
  rw [aux_lem_response_reciprocal_negative_inner_test]
  have hval : ∀ x, (extendTest hsub (aux_lem_response_reciprocal_negative_test x0 s hs (f x0))) x =
      f x0 * ψ x := fun x => rfl
  simp only [hval]
  have hzero : ∀ x, x ∉ (centeredCube x0 s hs : Set (SpatialCoordinates d)) → ψ x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hxt
    apply hx
    rw [hψ, (aux_lem_response_reciprocal_negative_bump x0 s hs).tsupport_eq] at hxt
    exact Metric.closedBall_subset_ball (by
      change s / 4 < s / 2
      linarith) hxt
  have hint : (∫ x in (Ω : Set (SpatialCoordinates d)), f x * (f x0 * ψ x)) =
      ∫ x, f x * (f x0 * ψ x) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have : x ∉ (centeredCube x0 s hs : Set (SpatialCoordinates d)) := fun h => hx (hsub h)
    rw [hzero x this, mul_zero, mul_zero]
  rw [hint]
  have hcont : Continuous (fun x => f x * (f x0 * ψ x)) :=
    f.contDiff.continuous.mul (continuous_const.mul ψ.continuous)
  have hcs : HasCompactSupport (fun x => f x * (f x0 * ψ x)) :=
    (ψ.hasCompactSupport.mul_left (f := fun _ => f x0)).mul_left (f := f)
  have hnonneg : 0 ≤ fun x => f x * (f x0 * ψ x) := by
    intro x
    by_cases hx : x ∈ (centeredCube x0 s hs : Set (SpatialCoordinates d))
    · have h1 := hsign x hx
      have h2 : 0 ≤ ψ x := ψ.nonneg
      show 0 ≤ f x * (f x0 * ψ x)
      nlinarith [mul_nonneg h1.le h2]
    · show 0 ≤ f x * (f x0 * ψ x)
      rw [hzero x hx]
      simp
  refine hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs hnonneg (x := x0) ?_
  have h1 : ψ x0 = 1 := ψ.one_of_mem_closedBall (Metric.mem_closedBall_self ψ.rIn_pos.le)
  show f x0 * (f x0 * ψ x0) ≠ 0
  rw [h1, mul_one]
  exact mul_ne_zero hf0 hf0

/-- Restricting the zero extension of a class recovers the class. -/
theorem aux_lem_response_reciprocal_negative_restrict_zeroExt {d : ℕ}
    {V U : Opens (SpatialCoordinates d)} (hV : V ≤ U) (f : DomainL2 V) :
    domainLpRestrict hV (zeroExtensionLp hV f) = f := by
  apply Lp.ext
  filter_upwards [domainLpRestrict_coeFn hV (zeroExtensionLp hV f),
    ae_restrict_of_ae_restrict_of_subset (μ := (volume : Measure (SpatialCoordinates d)))
      (show (V : Set (SpatialCoordinates d)) ⊆ U from hV) (zeroExtensionLp_coeFn hV f),
    ae_restrict_mem V.isOpen.measurableSet] with x h1 h2 h3
  rw [h1, h2, Set.indicator_of_mem h3]

/-- Restricting the zero extension of Sobolev data recovers the data. -/
theorem aux_lem_response_reciprocal_negative_restrict_zeroExtData {d : ℕ}
    {V U : Opens (SpatialCoordinates d)} (hV : V ≤ U) (u : SobolevData V) :
    sobolevDataRestrict hV (zeroExtensionSobolevData hV u) = u := by
  refine Prod.ext ?_ (funext fun j => ?_)
  · exact aux_lem_response_reciprocal_negative_restrict_zeroExt hV u.1
  · exact aux_lem_response_reciprocal_negative_restrict_zeroExt hV (u.2 j)


/-- The `L²` norm on a cube is at most a constant times an almost sure bound. -/
theorem aux_lem_response_reciprocal_negative_l2_le {d : ℕ} (z : SpatialCoordinates d) (R : ℝ)
    (hR : 0 < R) :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ (f : DomainL2 (centeredCube z R hR)) (C : ℝ), 0 ≤ C →
      (∀ᵐ x ∂volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d)), ‖f x‖ ≤ C) →
        ‖f‖ ≤ V * C :=
  ⟨((measureUnivNNReal (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))) ^
      (2 : ℝ≥0∞).toReal⁻¹ : ℝ≥0) : ℝ), NNReal.coe_nonneg _,
    fun _ _ hC hf => Lp.norm_le_of_ae_bound hC hf⟩

/-- The zero extension of a harmonic mesh interpolant of a smooth datum on a subcube is an
admissible competitor on the cube, with source pairing at least half that of the datum, and its
energy is the sum of the cell Dirichlet infima of the mesh. -/
theorem aux_lem_response_reciprocal_negative_mesh {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (x0 : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
    (hsub : centeredCube x0 s hs ≤ centeredCube z R hR)
    (f0 : DomainL2 (centeredCube z R hR)) (hf0 : f0 ≠ 0)
    (phi : H1Function (centeredCube x0 s hs : Set (SpatialCoordinates d)))
    (hphi : ContDiff ℝ ∞ phi.toFun) (hcompact : HasCompactSupport phi.toFun)
    (hsupport : tsupport phi.toFun ⊆ (centeredCube x0 s hs : Set (SpatialCoordinates d)))
    (hpair : 0 < inner ℝ f0 (zeroExtensionLp hsub (sobolevDataOfH1 phi).1)) :
    ∃ J : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ (S : ResponseSpace (centeredCube z R hR)),
      S.space = killedSobolevGraph (centeredCube z R hR) →
      ∀ (a : PositiveCoefficient (centeredCube z R hR))
        (a' : PositiveCoefficient (centeredCube x0 s hs))
        (c : SpatialCoordinates d → ℝ) (lam Lam : ℝ),
      0 < lam → Continuous c →
      (∀ x ∈ (centeredCube x0 s hs : Set (SpatialCoordinates d)), lam ≤ c x ∧ c x ≤ Lam) →
      ((fun x => a.val x) =ᵐ[volume.restrict
        (centeredCube x0 s hs : Set (SpatialCoordinates d))] c) →
      ((fun x => a'.val x) =ᵐ[volume.restrict
        (centeredCube x0 s hs : Set (SpatialCoordinates d))] c) →
      0 < inverseResponse S a ((sobolevVolumeLoad f0).comp S.space.subtypeL) ∧
        (inverseResponse S a ((sobolevVolumeLoad f0).comp S.space.subtypeL))⁻¹ ≤
          B * ∑ k : OddGridIndex d (triadicHalf J),
            cellDirichletInfimum c
              (oddGridCell x0 s hs (triadicHalf J) k : Set (SpatialCoordinates d))
              (phi.restrict (oddGridCell x0 s hs (triadicHalf J) k).isOpen
                (oddGridCell_subset x0 hs (triadicHalf J) k)) := by
  obtain ⟨C, hC, hmesh⟩ := lane2_meshInterpolator hd
  obtain ⟨V, hV, hVl⟩ := aux_lem_response_reciprocal_negative_l2_le x0 s hs
  let D := sSup ((fun y => ‖fderiv ℝ phi.toFun y‖) ''
    closure (centeredCube x0 s hs : Set (SpatialCoordinates d)))
  let gQ : DomainL2 (centeredCube z R hR) := zeroExtensionLp hsub (sobolevDataOfH1 phi).1
  have hnf : 0 < ‖f0‖ := norm_pos_iff.mpr hf0
  have hε : 0 < inner ℝ f0 gQ / (2 * ‖f0‖) := div_pos hpair (by positivity)
  obtain ⟨J, hJ⟩ := exists_triadic_mesh_error_lt (V * C * s) D (inner ℝ f0 gQ / (2 * ‖f0‖)) hε
  refine ⟨J, (((inner ℝ f0 gQ) / 2) ^ 2)⁻¹, by positivity, ?_⟩
  intro S hS a a' c lam Lam hlam hc hbounds hac ha'c
  obtain ⟨v, _hcont, _hcells, henergy, herror⟩ :=
    hmesh x0 s hs J c lam Lam hlam hc hbounds phi hphi hcompact hsupport
  have hu : sobolevDataOfH1 v.toH1Function ∈ killedSobolevGraph (centeredCube x0 s hs) :=
    sobolevDataOfH1_mem_killed v
  let w : S.space := ⟨zeroExtensionSobolevData hsub (sobolevDataOfH1 v.toH1Function), by
    rw [hS]
    exact lane2_zeroExtensionSobolevData_mem_killed hsub hu⟩
  have hclose0 : ‖(sobolevDataOfH1 v.toH1Function).1 - (sobolevDataOfH1 phi).1‖ ≤
      V * (C * (s / (3 : ℝ) ^ J) * |D|) := by
    apply hVl _ _ (mul_nonneg (mul_nonneg hC (by positivity)) (abs_nonneg D))
    filter_upwards [Lp.coeFn_sub (sobolevDataOfH1 v.toH1Function).1 (sobolevDataOfH1 phi).1,
      sobolevDataOfH1_fst_coeFn v.toH1Function, sobolevDataOfH1_fst_coeFn phi,
      ae_restrict_mem (centeredCube x0 s hs).isOpen.measurableSet]
      with x hsub' hv hp hx
    rw [hsub', Pi.sub_apply]
    change ‖(sobolevDataOfH1 v.toH1Function).1 x - (sobolevDataOfH1 phi).1 x‖ ≤ _
    rw [hv, hp, Real.norm_eq_abs]
    exact (herror x hx).trans
      (mul_le_mul_of_nonneg_left (le_abs_self D) (mul_nonneg hC (by positivity)))
  have hclose : ‖w.val.1 - gQ‖ ≤ inner ℝ f0 gQ / (2 * ‖f0‖) := by
    have h1 : w.val.1 - gQ =
        zeroExtensionLp hsub ((sobolevDataOfH1 v.toH1Function).1 - (sobolevDataOfH1 phi).1) := by
      rw [lane2_zeroExtensionLp_sub]
      rfl
    rw [h1, lane2_norm_zeroExtensionLp]
    refine hclose0.trans (le_of_eq_of_le ?_ hJ.le)
    ring
  have hload : inner ℝ f0 gQ / 2 ≤ ((sobolevVolumeLoad f0).comp S.space.subtypeL) w := by
    have hcs : |inner ℝ f0 (w.val.1 - gQ)| ≤ ‖f0‖ * (inner ℝ f0 gQ / (2 * ‖f0‖)) :=
      (abs_real_inner_le_norm f0 (w.val.1 - gQ)).trans
        (mul_le_mul_of_nonneg_left hclose hnf.le)
    have hcs' : ‖f0‖ * (inner ℝ f0 gQ / (2 * ‖f0‖)) = inner ℝ f0 gQ / 2 := by
      field_simp
    have hlow := (neg_le_abs (inner ℝ f0 (w.val.1 - gQ))).trans hcs
    rw [hcs', inner_sub_right] at hlow
    change inner ℝ f0 gQ / 2 ≤ inner ℝ f0 w.val.1
    linarith
  have htest := inverseResponse_inv_le_of_load_lower S a
    ((sobolevVolumeLoad f0).comp S.space.subtypeL) w (half_pos hpair) hload
  refine ⟨htest.1, htest.2.trans_eq ?_⟩
  have hab : (a.val : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube x0 s hs : Set (SpatialCoordinates d))] a'.val := hac.trans ha'c.symm
  have heq : responseForm S a w w =
      energy c (centeredCube x0 s hs : Set (SpatialCoordinates d)) v.toH1Function := by
    have h1 : responseForm S a w w = sobolevCoefficientForm a w.val w.val := rfl
    rw [h1, sobolevCoefficientForm_zeroExtension hsub a a' hab _ _,
      aux_lem_response_reciprocal_negative_restrict_zeroExtData hsub]
    exact (energy_eq_sobolevCoefficientForm a' c ha'c v.toH1Function).symm
  rw [heq, henergy, div_eq_mul_inv, mul_comm]
  rfl


/-- Cubes with equal centre and equal side are equal. -/
theorem aux_lem_response_reciprocal_negative_cube_congr {d : ℕ} (w : SpatialCoordinates d)
    {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s') (h : s = s') :
    centeredCube w s hs = centeredCube w s' hs' := by
  subst h
  rfl

/-- The side of a depth-`J` cell of a triadic cube of depth `m` is the triadic scale `3^{-(m+J)}`. -/
theorem aux_lem_response_reciprocal_negative_radius (R : ℝ) (m J : ℕ)
    (hm : R = (3 : ℝ) ^ (-(m : ℤ))) :
    R / (2 * (triadicHalf J : ℝ) + 1) = (3 : ℝ) ^ (-((m + J : ℕ) : ℤ)) := by
  rw [triadic_denominator, hm, Nat.cast_add, neg_add,
    zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_neg (3 : ℝ) (J : ℤ), zpow_natCast, div_eq_mul_inv,
    mul_comm]

/-- A nonzero test function is a nonzero `L²` class. -/
theorem aux_lem_response_reciprocal_negative_testL2_ne_zero {d : ℕ}
    {Ω : Opens (SpatialCoordinates d)} (f : 𝓓(Ω, ℝ)) (hf : f ≠ 0) : testL2 f ≠ 0 := by
  intro hzero
  have hae : (f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
      (fun _ => 0) := by
    have h := (testL2_coeFn f).symm
    rw [hzero] at h
    exact h.trans (Lp.coeFn_zero _ _ _)
  have heq := Measure.eqOn_of_ae_eq hae f.contDiff.continuous.continuousOn continuousOn_const
    (by rw [Ω.isOpen.interior_eq]; exact subset_closure)
  apply hf
  refine DFunLike.ext _ _ fun x => ?_
  by_cases hx : x ∈ (Ω : Set (SpatialCoordinates d))
  · exact heq hx
  · exact image_eq_zero_of_notMem_tsupport (fun h => hx (f.tsupport_subset h))

/-- A test function has native `H¹` data with its literal smooth representative. -/
theorem aux_lem_response_reciprocal_negative_native {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (f : 𝓓(Ω, ℝ)) :
    ∃ phi : H1Function (Ω : Set (SpatialCoordinates d)),
      phi.toFun = f ∧ (sobolevDataOfH1 phi).1 = testL2 f := by
  obtain ⟨phi, hphi, hdata⟩ := exists_nativeH1Function_of_ae_representative
    ⟨smoothSobolevData f, smoothSobolevData_mem f⟩ f (testL2_coeFn f)
  exact ⟨phi, hphi, congrArg Prod.fst hdata⟩

/-- Every continuous positive cutoff coefficient has ordinary ellipticity bounds on a cube. -/
theorem aux_lem_response_reciprocal_negative_elliptic {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ) (om : BilateralField d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) :
    ∃ lo hi : ℝ, 0 < lo ∧
      ∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
        lo ≤ cutoffCoefficient M H om N x ∧ cutoffCoefficient M H om N x ≤ hi := by
  have hc := cutoffCoefficient_continuous M H om N
  obtain ⟨lo, hlo, hlow⟩ := (closedCube z R hR).isCompact.exists_forall_le'
    hc.continuousOn (fun x _ => cutoffCoefficient_pos M H om N x)
  obtain ⟨hi, hhigh⟩ := (closedCube z R hR).isCompact.bddAbove_image hc.continuousOn
  refine ⟨lo, hi, hlo, fun x hx => ?_⟩
  have hx' := centeredCube_subset_closedCube z hR hx
  exact ⟨hlow x hx', hhigh (mem_image_of_mem _ hx')⟩

/-- The upper ellipticity of a cell of the root is independent of the enclosing root. -/
theorem aux_lem_response_reciprocal_negative_Lam_eq {d : ℕ} [NeZero d] (E : in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ) (om : BilateralField d)
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hsub : centeredCube w r hr ≤ centeredCube z0 R hR) :
    E.Lam w r hr (cutoffPositiveCoefficient M H om N w hr) w r (1 / 16) 2 =
      E.Lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w r (1 / 16) 2 := by
  have hs : (1 / 16 : ℝ) ∈ Ioc (0 : ℝ) 1 := by constructor <;> norm_num
  rw [aux_lem_extension_cell_moment_Lam_eq_tsum E w r hr _ w r hr le_rfl _ hs,
    aux_lem_extension_cell_moment_Lam_eq_tsum E z0 R hR _ w r hr hsub _ hs]
  apply tsum_congr
  intro n
  rw [aux_lem_extension_cell_moment_maxB_chart_eq E M H om N w r hr w r hr le_rfl n,
    aux_lem_extension_cell_moment_maxB_chart_eq E M H om N z0 R hR w r hr hsub n]

/-- The ellipticity envelope of a cell of side `3^{-k}` relative to a root cube. -/
def aux_lem_response_reciprocal_negative_field {d : ℕ} (E : in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (w : SpatialCoordinates d) (k N : ℕ) (om : BilateralField d) : ℝ :=
  E.Lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w ((3 : ℝ) ^ (-(k : ℤ))) (1 / 16) 2 +
    (E.lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w ((3 : ℝ) ^ (-(k : ℤ)))
      (1 / 16) 2)⁻¹

/-- The cell envelope is pointwise nonnegative. -/
theorem aux_lem_response_reciprocal_negative_field_nonneg {d : ℕ} (E : in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (w : SpatialCoordinates d) (k N : ℕ) (om : BilateralField d) :
    0 ≤ aux_lem_response_reciprocal_negative_field E M H z0 R hR w k N om :=
  add_nonneg (E.Lam_pos _ _ _ _ _ _ _ _).le (inv_nonneg.mpr (E.lam_pos _ _ _ _ _ _ _ _).le)

/-- A smooth cell extension bounds the native cell infimum by the cell envelope, for a datum on a
root cube. -/
theorem aux_lem_response_reciprocal_negative_cell {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (E : in_J d) (X : in_extension d hd E)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ) (om : BilateralField d)
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (phi : H1Function (centeredCube z0 R hR : Set (SpatialCoordinates d)))
    (hphi : ContDiff ℝ 2 phi.toFun)
    (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (k : ℕ)
    (hk : r = (3 : ℝ) ^ (-(k : ℤ)))
    (hsub : centeredCube w r hr ≤ centeredCube z0 R hR) :
    cellDirichletInfimum (cutoffCoefficient M H om N)
      (centeredCube w r hr : Set (SpatialCoordinates d))
      (phi.restrict (centeredCube w r hr).isOpen hsub) ≤
      aux_thm_c1_response_negative_moment_weight X.C phi.toFun w r hr *
        aux_lem_response_reciprocal_negative_field E M H z0 R hR w k N om := by
  let v := phi.restrict (centeredCube w r hr).isOpen hsub
  let hP := centeredCube_killedPoincare w hr
  rw [cellDirichletInfimum_eq_dirichletResponse hP
    (cutoffPositiveCoefficient M H om N w hr) _
    (aux_rem_bank_response_moments_lc_cutoff_positive_coe M H om N w hr)]
  have hb := aux_rem_bank_response_moments_cell_smooth hd E X w r hr hr1 hP
    (cutoffPositiveCoefficient M H om N w hr) phi.toFun hphi
    (c2Norm (closedCube w r hr : Set (SpatialCoordinates d)) phi.toFun) le_rfl
    ⟨sobolevDataOfH1 v, sobolevDataOfH1_mem_weak v⟩ (sobolevDataOfH1_fst_coeFn v)
  have heq := aux_lem_response_reciprocal_negative_Lam_eq E M H N om z0 R hR w r hr hsub
  norm_num only [show ((3 / 4 : ℝ) - 1 / 2) / 4 = 1 / 16 by norm_num] at hb
  rw [heq] at hb
  have hw : aux_rem_bank_response_moments_Csm d X.C *
        E.Lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w r (1 / 16) 2 *
        r ^ ((d : ℝ) - 2) * r ^ 2 * c2Norm (closedCube w r hr : Set (SpatialCoordinates d)) phi.toFun ^ 2 =
      aux_thm_c1_response_negative_moment_weight X.C phi.toFun w r hr *
        E.Lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w r (1 / 16) 2 := by
    unfold aux_thm_c1_response_negative_moment_weight; ring
  refine (hb.trans_eq hw).trans ?_
  subst hk
  unfold aux_lem_response_reciprocal_negative_field
  exact mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_right (inv_nonneg.mpr (E.lam_pos _ _ _ _ _ _ _ _).le))
    (aux_thm_c1_response_negative_moment_weight_nonneg _ _ _ _ _)

/-- The mesh energy is bounded by a finite weighted sum of the moment envelopes. -/
theorem aux_lem_response_reciprocal_negative_mesh_energy {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (E : in_J d) (X : in_extension d hd E)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ) (om : BilateralField d)
    (x0 : SpatialCoordinates d) (s : ℝ) (hs : 0 < s) (m J : ℕ) (hm : s = (3 : ℝ) ^ (-(m : ℤ)))
    (phi : H1Function (centeredCube x0 s hs : Set (SpatialCoordinates d)))
    (hphi : ContDiff ℝ 2 phi.toFun) :
    (∑ k : OddGridIndex d (triadicHalf J),
      cellDirichletInfimum (cutoffCoefficient M H om N)
        (oddGridCell x0 s hs (triadicHalf J) k : Set (SpatialCoordinates d))
        (phi.restrict (oddGridCell x0 s hs (triadicHalf J) k).isOpen
          (oddGridCell_subset x0 hs (triadicHalf J) k))) ≤
      ∑ k : OddGridIndex d (triadicHalf J),
        aux_thm_c1_response_negative_moment_weight X.C phi.toFun (oddGridCenter x0 s (triadicHalf J) k)
          (s / (2 * (triadicHalf J : ℝ) + 1)) (div_pos hs (by positivity)) *
        aux_lem_response_reciprocal_negative_field E M H x0 s hs
          (oddGridCenter x0 s (triadicHalf J) k) (m + J) N om := by
  have hs1 : s ≤ 1 := by
    rw [hm]
    exact zpow_le_one_of_nonpos₀ (by norm_num) (by simp)
  apply Finset.sum_le_sum
  intro k _hk
  have hr1 : s / (2 * (triadicHalf J : ℝ) + 1) ≤ 1 := by
    refine (div_le_self hs.le ?_).trans hs1
    linarith only [(Nat.cast_nonneg (triadicHalf J) : (0 : ℝ) ≤ (triadicHalf J : ℝ))]
  exact aux_lem_response_reciprocal_negative_cell hd E X M H N om x0 s hs phi hphi
    (oddGridCenter x0 s (triadicHalf J) k) _ (div_pos hs (by positivity)) hr1 (m + J)
    (aux_lem_response_reciprocal_negative_radius s m J hm)
    (oddGridCell_subset x0 hs (triadicHalf J) k)

/-- A fixed mesh has a model-uniform `L^q` envelope at every cutoff, for every `q ≥ 1`. -/
theorem aux_lem_response_reciprocal_negative_envelope {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (q : ℝ) (hq : 1 ≤ q)
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (k : ℕ) :
    ∃ delta C : ℝ, 0 < delta ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta →
      ∀ w : SpatialCoordinates d,
      centeredCube w ((3 : ℝ) ^ (-(k : ℤ))) (zpow_pos zero_lt_three _) ≤ centeredCube z0 R hR →
      ∀ N : ℕ,
        MemLp (aux_lem_response_reciprocal_negative_field E M H z0 R hR w k N)
          (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ∧
        eLpNorm (aux_lem_response_reciprocal_negative_field E M H z0 R hR w k N)
          (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal C := by
  obtain ⟨delta, Cd, hdelt, hCd, Cq, hCq, hmono, h⟩ :=
    lem_extension_cell_moment_uniform_root hd E (3 / 4) q
      (by constructor <;> norm_num) hq z0 R hR
  have hqq : 0 ≤ q + q ^ 2 := by nlinarith
  let C := Cq delta * Real.exp (Cd * (q + q ^ 2) * delta ^ 2 * k)
  refine ⟨delta, C, hdelt, mul_pos (hCq delta) (Real.exp_pos _), ?_⟩
  intro M H hH hdelta w hcell N
  obtain ⟨hmeas, hnorm⟩ := h M H hH hdelta w N k hcell
  norm_num only [show ((3 / 4 : ℝ) - 1 / 2) / 4 = 1 / 16 by norm_num] at hmeas hnorm
  have hbound : eLpNorm (aux_lem_response_reciprocal_negative_field E M H z0 R hR w k N)
      (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal C := by
    refine hnorm.trans (ENNReal.ofReal_le_ofReal ?_)
    dsimp only [C]
    have hsq : M.delta ^ 2 ≤ delta ^ 2 :=
      pow_le_pow_left₀ M.shellPrefix.delta_pos.le hdelta 2
    apply mul_le_mul (hmono M.delta delta M.shellPrefix.delta_pos.le hdelta)
      (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (hCq delta).le
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsq (mul_nonneg hCd.le hqq)) (Nat.cast_nonneg k)
  exact ⟨⟨hmeas, hbound.trans_lt ENNReal.ofReal_lt_top⟩, hbound⟩


/-- The reciprocal `L^p` moment of the quadratic form of a nonzero smooth source on an arbitrary
cube has one bound chosen before the model and the cutoff. -/
theorem lem_response_reciprocal_negative {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (X : in_extension d hd E)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (f : 𝓓(centeredCube z R hR, ℝ)) (hf : f ≠ 0) (p : ℝ) (hp : 1 ≤ p) :
    ∃ delta C : ℝ, 0 < delta ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta →
      ∀ (S : ResponseSpace (centeredCube z R hR)),
      S.space = killedSobolevGraph (centeredCube z R hR) →
      ∀ N : ℕ,
        (∀ om, 0 < inverseResponse S (cutoffPositiveCoefficient M H om N z hR)
          ((sobolevVolumeLoad (testL2 f)).comp S.space.subtypeL)) ∧
        MemLp (fun om => (inverseResponse S (cutoffPositiveCoefficient M H om N z hR)
          ((sobolevVolumeLoad (testL2 f)).comp S.space.subtypeL))⁻¹) (ENNReal.ofReal p)
          (chaosSampleLaw M).toMeasure ∧
        eLpNorm (fun om => (inverseResponse S (cutoffPositiveCoefficient M H om N z hR)
          ((sobolevVolumeLoad (testL2 f)).comp S.space.subtypeL))⁻¹) (ENNReal.ofReal p)
          (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal C := by
  haveI instDim : NeZero d := ⟨by omega⟩
  obtain ⟨x0, k0, hsub, hsign⟩ := aux_lem_response_reciprocal_negative_subcube f hf
  set s : ℝ := (3 : ℝ) ^ (-(k0 : ℤ)) with hs_def
  have hs : 0 < s := zpow_pos zero_lt_three _
  have hfx0 : f x0 ≠ 0 := by
    intro h
    have := hsign x0 (Metric.mem_ball_self (by positivity))
    rw [h, zero_mul] at this
    exact lt_irrefl _ this
  -- the datum on the subcube and its native representative
  obtain ⟨phi, hphi, hdata⟩ := aux_lem_response_reciprocal_negative_native
    (aux_lem_response_reciprocal_negative_test x0 s hs (f x0))
  have hphismooth : ContDiff ℝ ∞ phi.toFun :=
    hphi.symm ▸ (aux_lem_response_reciprocal_negative_test x0 s hs (f x0)).contDiff
  have hphisupport : tsupport phi.toFun ⊆ (centeredCube x0 s hs : Set (SpatialCoordinates d)) :=
    hphi.symm ▸ (aux_lem_response_reciprocal_negative_test x0 s hs (f x0)).tsupport_subset
  have hpair : 0 < inner ℝ (testL2 f) (zeroExtensionLp hsub (sobolevDataOfH1 phi).1) := by
    rw [hdata, lane2_zeroExtensionLp_testL2]
    exact aux_lem_response_reciprocal_negative_pairing_pos f x0 s hs hsub hfx0 hsign
  obtain ⟨J, B, hB, htest⟩ := aux_lem_response_reciprocal_negative_mesh hd z R hR x0 s hs hsub
    (testL2 f) (aux_lem_response_reciprocal_negative_testL2_ne_zero f hf) phi hphismooth
    (hphi.symm ▸ (aux_lem_response_reciprocal_negative_test x0 s hs (f x0)).hasCompactSupport)
    hphisupport hpair
  obtain ⟨delta, K, hdelta, hK, hmoment⟩ :=
    aux_lem_response_reciprocal_negative_envelope hd E p hp x0 s hs (k0 + J)
  let weight (k : OddGridIndex d (triadicHalf J)) : ℝ :=
    aux_thm_c1_response_negative_moment_weight X.C phi.toFun (oddGridCenter x0 s (triadicHalf J) k)
      (s / (2 * (triadicHalf J : ℝ) + 1)) (div_pos hs (by positivity))
  have hweight : ∀ k, 0 ≤ weight k := fun k =>
    aux_thm_c1_response_negative_moment_weight_nonneg _ _ _ _ _
  have hcell (k : OddGridIndex d (triadicHalf J)) :
      centeredCube (oddGridCenter x0 s (triadicHalf J) k) ((3 : ℝ) ^ (-((k0 + J : ℕ) : ℤ)))
        (zpow_pos zero_lt_three _) ≤ centeredCube x0 s hs := by
    have hc := aux_lem_response_reciprocal_negative_cube_congr
      (oddGridCenter x0 s (triadicHalf J) k) (div_pos hs (by positivity))
      (zpow_pos zero_lt_three ((-((k0 + J : ℕ) : ℤ))))
      (aux_lem_response_reciprocal_negative_radius s k0 J hs_def)
    rw [← hc]
    exact oddGridCell_subset x0 hs (triadicHalf J) k
  refine ⟨delta, max 1 (B * ((∑ k, weight k) * K)), hdelta, lt_max_of_lt_left one_pos, ?_⟩
  intro M H hH hMd S hS N
  let F (k : OddGridIndex d (triadicHalf J)) : BilateralField d → ℝ :=
    aux_lem_response_reciprocal_negative_field E M H x0 s hs
      (oddGridCenter x0 s (triadicHalf J) k) (k0 + J) N
  have hFm k : MemLp (F k) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure :=
    (hmoment M H hH hMd _ (hcell k) N).1
  have hFb k : eLpNorm (F k) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal K :=
    (hmoment M H hH hMd _ (hcell k) N).2
  have hsum := finite_weighted_memLp_bound (chaosSampleLaw M).toMeasure (ENNReal.ofReal p)
    (ENNReal.one_le_ofReal.2 hp) weight hweight F hK.le hFm hFb
  have hpoint (om : BilateralField d) :
      0 < inverseResponse S (cutoffPositiveCoefficient M H om N z hR)
          ((sobolevVolumeLoad (testL2 f)).comp S.space.subtypeL) ∧
        (inverseResponse S (cutoffPositiveCoefficient M H om N z hR)
          ((sobolevVolumeLoad (testL2 f)).comp S.space.subtypeL))⁻¹ ≤
          B * ∑ k, weight k * F k om := by
    obtain ⟨lo, hi, hlo, hcoeff⟩ :=
      aux_lem_response_reciprocal_negative_elliptic M H N om x0 s hs
    obtain ⟨hpos, hbound⟩ := htest S hS (cutoffPositiveCoefficient M H om N z hR)
      (cutoffPositiveCoefficient M H om N x0 hs)
      (cutoffCoefficient M H om N) lo hi hlo (cutoffCoefficient_continuous M H om N) hcoeff
      (ae_restrict_of_ae_restrict_of_subset (μ := (volume : Measure (SpatialCoordinates d)))
        (show (centeredCube x0 s hs : Set (SpatialCoordinates d)) ⊆
          (centeredCube z R hR : Set (SpatialCoordinates d)) from hsub)
        (aux_rem_bank_response_moments_lc_cutoff_positive_coe M H om N z hR))
      (aux_rem_bank_response_moments_lc_cutoff_positive_coe M H om N x0 hs)
    exact ⟨hpos, hbound.trans (mul_le_mul_of_nonneg_left
      (aux_lem_response_reciprocal_negative_mesh_energy hd E X M H N om x0 s hs k0 J hs_def phi
        (hphismooth.of_le (WithTop.coe_le_coe.mpr
          (show (2 : ℕ∞) ≤ ⊤ from le_top)))) hB.le)⟩
  have hRmeas := (aux_rem_bank_response_moments_measurable_inverseResponse M H hH.1 N
    z hR S ((sobolevVolumeLoad (testL2 f)).comp S.space.subtypeL)).inv
  have hout := aux_rem_bank_response_moments_memLp_of_envelope (chaosSampleLaw M).toMeasure
    (fun om => (inverseResponse S (cutoffPositiveCoefficient M H om N z hR)
      ((sobolevVolumeLoad (testL2 f)).comp S.space.subtypeL))⁻¹)
    (fun om => ∑ k, weight k * F k om) B ((∑ k, weight k) * K) hB.le (ENNReal.ofReal p)
    hRmeas.aestronglyMeasurable hsum.1 hsum.2 (Filter.Eventually.of_forall fun om => ?_)
  · exact ⟨fun om => (hpoint om).1, hout.1,
      hout.2.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))⟩
  · refine ⟨(inv_pos.mpr (hpoint om).1).le, ?_, ?_⟩
    · exact Finset.sum_nonneg fun k _ => mul_nonneg (hweight k)
        (aux_lem_response_reciprocal_negative_field_nonneg E M H x0 s hs _ (k0 + J) N om)
    · rw [mul_comm]
      exact (hpoint om).2


end
end Paper
