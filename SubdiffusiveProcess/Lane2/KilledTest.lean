module

public import SubdiffusiveProcess.Analysis.RawLp

public import SubdiffusiveProcess.Lane2.OddIteration
public import SubdiffusiveProcess.Lane4.Bridge
public import SubdiffusiveProcess.Lane2.DivLoad
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

@[expose] public section

/-!
# Killed tests survive the reflection

For `ψ` in the killed space of the doubled domain, the combination
`ψ|_Ω - R*(ψ|_{ρΩ})` lies in the killed space of the lower half.  This is what
lets the odd-extension transport be run on the killed test class, which is the
class a Dirichlet cell problem actually supplies.

The proof is the slab cutoff: the combination is, for a smooth test `χ` on the
doubled domain, the restriction of `F = χ - χ ∘ ρ`, which vanishes on the
reflection plane; multiplying by a smooth cutoff that kills an `ε`-slab around
the plane gives genuine tests on `Ω`, and the gradient error is bounded on a
slab of vanishing measure because `F` vanishes linearly at the plane.
-/

open MeasureTheory Set TopologicalSpace Filter
open scoped ENNReal ContDiff Distributions Topology

noncomputable section

namespace SubdiffusiveProcess

variable {d : ℕ}

/-! ## The scalar transition and its derivative bound -/

/-- `Real.smoothTransition` has a bounded derivative: it is constant off the
unit interval, and its derivative is continuous there. -/
theorem lane2_exists_deriv_bound_smoothTransition :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ C := by
  have hcont : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 2)).continuous_deriv (by norm_num)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
  · exact le_trans (hC t ht) (le_max_left _ _)
  · have hzero : deriv Real.smoothTransition t = 0 := by
      rcases not_and_or.mp ht with h | h
      · have hlt : t < 0 := lt_of_not_ge h
        have hev : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
          filter_upwards [Iio_mem_nhds hlt] with s hs
          exact Real.smoothTransition.zero_of_nonpos (le_of_lt hs)
        rw [hev.deriv_eq, deriv_const]
      · have hlt : (1 : ℝ) < t := lt_of_not_ge h
        have hev : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
          filter_upwards [Ioi_mem_nhds hlt] with s hs
          exact Real.smoothTransition.one_of_one_le (le_of_lt hs)
        rw [hev.deriv_eq, deriv_const]
    rw [hzero, abs_zero]
    exact le_max_right _ _

/-! ## The slab cutoff -/

/-- A smooth function of `x` which vanishes on the closed `ε`-slab below the
plane `{x i = z i}` and equals `1` beyond the `2ε`-slab. -/
def lane2_slabCutoff (z : SpatialCoordinates d) (i : Fin d) (eps : ℝ)
    (x : SpatialCoordinates d) : ℝ :=
  Real.smoothTransition ((z i - x i) / eps - 1)

theorem lane2_slabCutoff_contDiff (z : SpatialCoordinates d) (i : Fin d) (eps : ℝ) :
    ContDiff ℝ ∞ (lane2_slabCutoff z i eps) := by
  have hinner : ContDiff ℝ ∞ (fun x : SpatialCoordinates d =>
      (z i - x i) / eps - 1) :=
    ((contDiff_const.sub (contDiff_apply ℝ ℝ i)).div_const eps).sub contDiff_const
  exact Real.smoothTransition.contDiff.comp hinner

theorem lane2_slabCutoff_nonneg (z : SpatialCoordinates d) (i : Fin d) (eps : ℝ)
    (x : SpatialCoordinates d) : 0 ≤ lane2_slabCutoff z i eps x :=
  Real.smoothTransition.nonneg _

theorem lane2_slabCutoff_le_one (z : SpatialCoordinates d) (i : Fin d) (eps : ℝ)
    (x : SpatialCoordinates d) : lane2_slabCutoff z i eps x ≤ 1 :=
  Real.smoothTransition.le_one _

theorem lane2_slabCutoff_eq_zero {z : SpatialCoordinates d} {i : Fin d} {eps : ℝ}
    (heps : 0 < eps) {x : SpatialCoordinates d} (hx : z i - eps ≤ x i) :
    lane2_slabCutoff z i eps x = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  have : (z i - x i) / eps ≤ 1 := by
    rw [div_le_one heps]
    linarith
  linarith

theorem lane2_slabCutoff_eq_one {z : SpatialCoordinates d} {i : Fin d} {eps : ℝ}
    (heps : 0 < eps) {x : SpatialCoordinates d} (hx : x i ≤ z i - 2 * eps) :
    lane2_slabCutoff z i eps x = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  have : (2 : ℝ) ≤ (z i - x i) / eps := by
    rw [le_div_iff₀ heps]
    linarith
  linarith

theorem lane2_hasFDerivAt_slabCutoff (z : SpatialCoordinates d) (i : Fin d)
    {eps : ℝ} (heps : 0 < eps) (x : SpatialCoordinates d) :
    HasFDerivAt (lane2_slabCutoff z i eps)
      ((deriv Real.smoothTransition ((z i - x i) / eps - 1)) •
        ((-(1 / eps)) • (ContinuousLinearMap.proj i :
          SpatialCoordinates d →L[ℝ] ℝ))) x := by
  have hproj : HasFDerivAt (fun y : SpatialCoordinates d => y i)
      (ContinuousLinearMap.proj i : SpatialCoordinates d →L[ℝ] ℝ) x :=
    (ContinuousLinearMap.proj i : SpatialCoordinates d →L[ℝ] ℝ).hasFDerivAt
  have hfun : (fun y : SpatialCoordinates d => (z i - y i) / eps - 1)
      = fun y : SpatialCoordinates d => (-(1 / eps)) * y i + (z i / eps - 1) := by
    funext y
    field_simp
    ring
  have hdiv : HasFDerivAt (fun y : SpatialCoordinates d => (z i - y i) / eps - 1)
      ((-(1 / eps)) • (ContinuousLinearMap.proj i :
        SpatialCoordinates d →L[ℝ] ℝ)) x := by
    rw [hfun]
    have h := (hproj.const_mul (-(1 / eps))).add_const (z i / eps - 1)
    convert h using 1
  have hST : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition ((z i - x i) / eps - 1))
      ((z i - x i) / eps - 1) :=
    ((Real.smoothTransition.contDiff (n := 2)).differentiable
      (by norm_num)).differentiableAt.hasDerivAt
  exact hST.comp_hasFDerivAt x hdiv

/-- The gradient of the slab cutoff is bounded by `C / ε`. -/
theorem lane2_slabCutoff_fderiv_bound (z : SpatialCoordinates d) (i : Fin d)
    {eps : ℝ} (heps : 0 < eps) {C : ℝ} (hC : 0 ≤ C)
    (hCb : ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ C)
    (x : SpatialCoordinates d) (j : Fin d) :
    |fderiv ℝ (lane2_slabCutoff z i eps) x (Pi.single j 1)| ≤ C / eps := by
  rw [(lane2_hasFDerivAt_slabCutoff z i heps x).fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul]
  rw [abs_mul]
  have h1 : |(Pi.single j (1 : ℝ) : SpatialCoordinates d) i| ≤ 1 := by
    by_cases hij : i = j
    · subst hij; simp
    · rw [Pi.single_eq_of_ne hij]; simp
  have h2 : |(-(1 / eps)) * (Pi.single j (1 : ℝ) : SpatialCoordinates d) i| ≤ 1 / eps := by
    rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / eps)]
    calc (1 / eps) * |(Pi.single j (1 : ℝ) : SpatialCoordinates d) i| ≤ (1 / eps) * 1 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 / eps := by ring
  calc |deriv Real.smoothTransition ((z i - x i) / eps - 1)| *
        |(-(1 / eps)) * (Pi.single j (1 : ℝ) : SpatialCoordinates d) i|
      ≤ C * (1 / eps) := by
        exact mul_le_mul (hCb _) h2 (abs_nonneg _) hC
    _ = C / eps := by ring

/-! ## The odd part of a test function on the doubled domain -/

theorem lane2_contDiff_coordinateReflection (z : SpatialCoordinates d)
    (I : Finset (Fin d)) : ContDiff ℝ ∞ (coordinateReflection z I) := by
  rw [contDiff_pi]
  intro j
  by_cases hj : j ∈ I
  · have he : (fun x : SpatialCoordinates d => coordinateReflection z I x j)
        = fun x : SpatialCoordinates d => 2 * z j - x j := by
      funext x; simp [coordinateReflection, hj]
    rw [he]
    exact contDiff_const.sub (contDiff_apply ℝ ℝ j)
  · have he : (fun x : SpatialCoordinates d => coordinateReflection z I x j)
        = fun x : SpatialCoordinates d => x j := by
      funext x; simp [coordinateReflection, hj]
    rw [he]
    exact contDiff_apply ℝ ℝ j

theorem lane2_coordinateReflection_preimage_eq_image (z : SpatialCoordinates d)
    (I : Finset (Fin d)) (K : Set (SpatialCoordinates d)) :
    coordinateReflection z I ⁻¹' K = coordinateReflection z I '' K := by
  ext x
  constructor
  · intro hx
    exact ⟨coordinateReflection z I x, hx, coordinateReflection_involutive z I x⟩
  · rintro ⟨y, hy, rfl⟩
    rw [Set.mem_preimage, coordinateReflection_involutive z I y]
    exact hy

/-- A bound on the derivative of a smooth compactly supported function. -/
theorem lane2_exists_fderiv_bound {f : SpatialCoordinates d → ℝ}
    (hf : ContDiff ℝ ∞ f) (hsupp : HasCompactSupport f) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x, ‖fderiv ℝ f x‖ ≤ L := by
  have hcont : Continuous (fun x => fderiv ℝ f x) := hf.continuous_fderiv (by simp)
  have hcs : HasCompactSupport (fun x => fderiv ℝ f x) := hsupp.fderiv ℝ
  obtain ⟨L, hL⟩ := hcs.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max L 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ tsupport (fun y => fderiv ℝ f y)
  · exact le_trans (hL x hx) (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
    exact le_max_right _ _

namespace EvenReflectionDomain

variable (D : EvenReflectionDomain d)

/-- The odd part of a test function on the doubled domain. -/
def lane2_oddTestFun (χ : 𝓓(D.U, ℝ)) : SpatialCoordinates d → ℝ :=
  fun x => χ x - χ (coordinateReflection D.z {D.i} x)

variable (χ : 𝓓(D.U, ℝ))

theorem lane2_oddTestFun_contDiff : ContDiff ℝ ∞ (D.lane2_oddTestFun χ) :=
  χ.contDiff.sub
    (χ.contDiff.comp (lane2_contDiff_coordinateReflection D.z {D.i}))

theorem lane2_oddTestFun_eq_zero_of_plane {x : SpatialCoordinates d}
    (hx : x D.i = D.z D.i) : D.lane2_oddTestFun χ x = 0 := by
  rw [lane2_oddTestFun, coordinateReflection_single_eq_self D.z D.i hx, sub_self]

theorem lane2_oddTestFun_support_subset :
    Function.support (D.lane2_oddTestFun χ) ⊆
      tsupport (χ : SpatialCoordinates d → ℝ) ∪
        coordinateReflection D.z {D.i} ⁻¹'
          tsupport (χ : SpatialCoordinates d → ℝ) := by
  intro x hx
  by_contra hcon
  rw [Set.mem_union, not_or] at hcon
  have h1 : (χ : SpatialCoordinates d → ℝ) x = 0 :=
    image_eq_zero_of_notMem_tsupport hcon.1
  have h2 : (χ : SpatialCoordinates d → ℝ)
      (coordinateReflection D.z {D.i} x) = 0 :=
    image_eq_zero_of_notMem_tsupport hcon.2
  exact hx (by simp [lane2_oddTestFun, h1, h2])

theorem lane2_oddTestFun_hasCompactSupport :
    HasCompactSupport (D.lane2_oddTestFun χ) := by
  have hrefl : IsCompact (coordinateReflection D.z {D.i} ⁻¹'
      tsupport (χ : SpatialCoordinates d → ℝ)) := by
    rw [lane2_coordinateReflection_preimage_eq_image]
    exact χ.hasCompactSupport.image
      (lane2_contDiff_coordinateReflection D.z {D.i}).continuous
  have hK : IsCompact (tsupport (χ : SpatialCoordinates d → ℝ) ∪
      coordinateReflection D.z {D.i} ⁻¹'
        tsupport (χ : SpatialCoordinates d → ℝ)) :=
    χ.hasCompactSupport.union hrefl
  exact hK.of_isClosed_subset isClosed_closure
    (closure_minimal (D.lane2_oddTestFun_support_subset χ) hK.isClosed)

theorem lane2_oddTestFun_tsupport_subset :
    tsupport (D.lane2_oddTestFun χ) ⊆ (D.U : Set (SpatialCoordinates d)) := by
  have hK : IsCompact (tsupport (χ : SpatialCoordinates d → ℝ) ∪
      coordinateReflection D.z {D.i} ⁻¹'
        tsupport (χ : SpatialCoordinates d → ℝ)) := by
    refine χ.hasCompactSupport.union ?_
    rw [lane2_coordinateReflection_preimage_eq_image]
    exact χ.hasCompactSupport.image
      (lane2_contDiff_coordinateReflection D.z {D.i}).continuous
  refine Set.Subset.trans
    (closure_minimal (D.lane2_oddTestFun_support_subset χ) hK.isClosed) ?_
  refine Set.union_subset χ.tsupport_subset ?_
  intro x hx
  have : coordinateReflection D.z {D.i} x ∈ (D.U : Set (SpatialCoordinates d)) :=
    χ.tsupport_subset hx
  exact (D.reflection_mem_U_iff x).mp this

/-- The odd test vanishes linearly at the reflection plane. -/
theorem lane2_oddTestFun_linear_bound :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x : SpatialCoordinates d,
      |D.lane2_oddTestFun χ x| ≤ L * |x D.i - D.z D.i| := by
  obtain ⟨L, hL0, hL⟩ := lane2_exists_fderiv_bound
    (D.lane2_oddTestFun_contDiff χ) (D.lane2_oddTestFun_hasCompactSupport χ)
  refine ⟨L, hL0, fun x => ?_⟩
  have hzero : D.lane2_oddTestFun χ (Function.update x D.i (D.z D.i)) = 0 :=
    D.lane2_oddTestFun_eq_zero_of_plane χ (by rw [Function.update_self])
  have hmvt : ‖D.lane2_oddTestFun χ x -
      D.lane2_oddTestFun χ (Function.update x D.i (D.z D.i))‖ ≤
      L * ‖x - Function.update x D.i (D.z D.i)‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => ((D.lane2_oddTestFun_contDiff χ).differentiable
        (by simp)).differentiableAt)
      (fun y _ => hL y) convex_univ (Set.mem_univ _) (Set.mem_univ _)
  have hnorm : ‖x - Function.update x D.i (D.z D.i)‖ ≤ |x D.i - D.z D.i| := by
    refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 (fun j => ?_)
    by_cases hj : j = D.i
    · subst hj
      simp [Function.update_self]
    · simp [Function.update_of_ne hj]
  rw [hzero, sub_zero] at hmvt
  calc |D.lane2_oddTestFun χ x| = ‖D.lane2_oddTestFun χ x‖ := rfl
    _ ≤ L * ‖x - Function.update x D.i (D.z D.i)‖ := hmvt
    _ ≤ L * |x D.i - D.z D.i| := mul_le_mul_of_nonneg_left hnorm hL0

end EvenReflectionDomain

/-! ## The slab-cut approximants -/

section Approx

variable (D : EvenReflectionDomain d)

/-- The `n`-th slab radius. -/
def lane2_slabEps (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

theorem lane2_slabEps_pos (n : ℕ) : 0 < lane2_slabEps n := by
  rw [lane2_slabEps]
  positivity

theorem lane2_slabEps_antitone : Antitone lane2_slabEps := by
  intro m n hmn
  rw [lane2_slabEps, lane2_slabEps]
  have h1 : (0:ℝ) < (m : ℝ) + 1 := by positivity
  have h2 : ((m : ℝ) + 1) ≤ ((n : ℝ) + 1) := by
    have hc : ((m : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) := Nat.cast_le.mpr hmn
    linarith
  exact inv_anti₀ h1 h2

theorem lane2_slabEps_tendsto : Filter.Tendsto lane2_slabEps Filter.atTop (𝓝 0) := by
  have h : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  simpa [lane2_slabEps] using! h.inv_tendsto_atTop

/-- The `n`-th approximant of a smooth odd datum: cut off the slab around the
reflection plane. -/
def lane2_slabApprox {F : SpatialCoordinates d → ℝ} (hFsmooth : ContDiff ℝ ∞ F)
    (hFsupp : HasCompactSupport F) (hFsub : tsupport F ⊆ (D.U : Set (SpatialCoordinates d)))
    (n : ℕ) : 𝓓(D.Ω, ℝ) where
  toFun := fun x => F x * lane2_slabCutoff D.z D.i (lane2_slabEps n) x
  contDiff' := hFsmooth.mul (lane2_slabCutoff_contDiff D.z D.i (lane2_slabEps n))
  hasCompactSupport' := hFsupp.mul_right
  tsupport_subset' := by
    have hclosed : IsClosed (tsupport F ∩
        {x : SpatialCoordinates d | x D.i ≤ D.z D.i - lane2_slabEps n}) :=
      isClosed_closure.inter (isClosed_le (continuous_apply D.i) continuous_const)
    refine Set.Subset.trans (closure_minimal ?_ hclosed) ?_
    · intro x hx
      have hne : F x ≠ 0 ∧ lane2_slabCutoff D.z D.i (lane2_slabEps n) x ≠ 0 := by
        constructor
        · intro h; exact hx (by simp [h])
        · intro h; exact hx (by simp [h])
      refine ⟨subset_tsupport _ hne.1, ?_⟩
      rcases le_or_gt (x D.i) (D.z D.i - lane2_slabEps n) with h | h
      · exact h
      · exact absurd (lane2_slabCutoff_eq_zero (lane2_slabEps_pos n) (le_of_lt h)) hne.2
    · rintro x ⟨hxK, hxslab⟩
      refine (D.mem_iff x).mpr ⟨hFsub hxK, ?_⟩
      have := lane2_slabEps_pos n
      simp only [Set.mem_setOf_eq] at hxslab
      linarith

theorem lane2_slabApprox_apply {F : SpatialCoordinates d → ℝ} (hFsmooth : ContDiff ℝ ∞ F)
    (hFsupp : HasCompactSupport F) (hFsub : tsupport F ⊆ (D.U : Set (SpatialCoordinates d)))
    (n : ℕ) (x : SpatialCoordinates d) :
    (lane2_slabApprox D hFsmooth hFsupp hFsub n : SpatialCoordinates d → ℝ) x
      = F x * lane2_slabCutoff D.z D.i (lane2_slabEps n) x := rfl

end Approx

/-! ## The slab estimate -/

section SlabEstimate

variable (D : EvenReflectionDomain d)

/-- The `n`-th slab inside the lower half, intersected with a compact set. -/
def lane2_slabSet (D : EvenReflectionDomain d) (K : Set (SpatialCoordinates d))
    (n : ℕ) : Set (SpatialCoordinates d) :=
  (D.Ω : Set (SpatialCoordinates d)) ∩ K ∩
    {x : SpatialCoordinates d | D.z D.i - 2 * lane2_slabEps n ≤ x D.i}

theorem lane2_slabSet_measurableSet {K : Set (SpatialCoordinates d)}
    (hK : IsClosed K) (n : ℕ) : MeasurableSet (lane2_slabSet D K n) :=
  (D.Ω.isOpen.measurableSet.inter hK.measurableSet).inter
    (isClosed_le continuous_const (continuous_apply D.i)).measurableSet

theorem lane2_slabSet_subset (K : Set (SpatialCoordinates d)) (n : ℕ) :
    lane2_slabSet D K n ⊆ K := fun _ hx => hx.1.2

theorem lane2_slabSet_antitone (K : Set (SpatialCoordinates d)) :
    Antitone (lane2_slabSet D K) := by
  intro m n hmn x hx
  obtain ⟨h1, h2⟩ := hx
  refine ⟨h1, ?_⟩
  have hx2 : D.z D.i - 2 * lane2_slabEps n ≤ x D.i := h2
  have he := lane2_slabEps_antitone hmn
  show D.z D.i - 2 * lane2_slabEps m ≤ x D.i
  linarith

theorem lane2_iInter_slabSet (K : Set (SpatialCoordinates d)) :
    (⋂ n, lane2_slabSet D K n) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  rw [Set.mem_iInter] at hx
  have hΩ : x ∈ D.Ω := (hx 0).1.1
  have hlt : x D.i < D.z D.i := ((D.mem_iff x).mp hΩ).2
  have hall : ∀ n : ℕ, D.z D.i - x D.i ≤ 2 * lane2_slabEps n := by
    intro n
    have := (hx n).2
    simp only [Set.mem_setOf_eq] at this
    linarith
  have hlim : Filter.Tendsto (fun n : ℕ => 2 * lane2_slabEps n) Filter.atTop (𝓝 0) := by
    simpa using! lane2_slabEps_tendsto.const_mul 2
  have : D.z D.i - x D.i ≤ 0 := ge_of_tendsto hlim (Filter.Eventually.of_forall hall)
  linarith

end SlabEstimate

/-- **The slab estimate.**  A uniformly bounded family vanishing off the slabs
tends to zero in `L²` on the lower half. -/
theorem lane2_eLpNorm_tendsto_zero_of_slab (D : EvenReflectionDomain d)
    {K : Set (SpatialCoordinates d)} (hKc : IsCompact K)
    {g : ℕ → SpatialCoordinates d → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hzero : ∀ (n : ℕ), ∀ x ∈ (D.Ω : Set (SpatialCoordinates d)),
      x ∉ lane2_slabSet D K n → g n x = 0)
    (hle : ∀ (n : ℕ), ∀ x ∈ (D.Ω : Set (SpatialCoordinates d)), |g n x| ≤ B) :
    Filter.Tendsto (fun n => SubdiffusiveProcess.RawLp.eLpNorm (g n) 2
      (volume.restrict (D.Ω : Set (SpatialCoordinates d)))) Filter.atTop (𝓝 0) := by
  have hKcl : IsClosed K := hKc.isClosed
  have hmeas : ∀ n, MeasurableSet (lane2_slabSet D K n) :=
    fun n => lane2_slabSet_measurableSet D hKcl n
  have hmu : Filter.Tendsto (fun n => volume (lane2_slabSet D K n))
      Filter.atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop
      (μ := (volume : Measure (SpatialCoordinates d)))
      (fun n => (hmeas n).nullMeasurableSet) (lane2_slabSet_antitone D K)
      ⟨0, ne_of_lt (lt_of_le_of_lt (measure_mono (lane2_slabSet_subset D K 0))
        hKc.measure_lt_top)⟩
    rwa [lane2_iInter_slabSet, measure_empty] at h
  have hbound : ∀ n, SubdiffusiveProcess.RawLp.eLpNorm (g n) 2
      (volume.restrict (D.Ω : Set (SpatialCoordinates d))) ≤
      ‖B‖ₑ * (volume (lane2_slabSet D K n)) ^ (1 / (2:ℝ)) := by
    intro n
    have hcmp : SubdiffusiveProcess.RawLp.eLpNorm (g n) 2
        (volume.restrict (D.Ω : Set (SpatialCoordinates d))) ≤
        eLpNorm ((lane2_slabSet D K n).indicator (fun _ => B)) 2
          (volume.restrict (D.Ω : Set (SpatialCoordinates d))) := by
      refine le_trans (SubdiffusiveProcess.RawLp.eLpNorm_mono_ae ?_) (SubdiffusiveProcess.RawLp.eLpNorm_le_guarded _ _ _)
      filter_upwards [ae_restrict_mem D.Ω.isOpen.measurableSet] with x hx
      by_cases hxS : x ∈ lane2_slabSet D K n
      · rw [Set.indicator_of_mem hxS]
        simpa [Real.norm_eq_abs, abs_of_nonneg hB] using! hle n x hx
      · rw [hzero n x hx hxS, Set.indicator_of_notMem hxS]
    refine le_trans hcmp ?_
    rw [eLpNorm_indicator_const (hmeas n).nullMeasurableSet (by norm_num) (by norm_num)]
    have hres : (volume.restrict (D.Ω : Set (SpatialCoordinates d)))
        (lane2_slabSet D K n) = volume (lane2_slabSet D K n) := by
      rw [Measure.restrict_apply (hmeas n)]
      congr 1
      exact Set.inter_eq_left.mpr (fun x hx => hx.1.1)
    rw [hres]
    norm_num
  have hupper : Filter.Tendsto
      (fun n => ‖B‖ₑ * (volume (lane2_slabSet D K n)) ^ (1 / (2:ℝ)))
      Filter.atTop (𝓝 0) := by
    have hrpow : Filter.Tendsto
        (fun n => (volume (lane2_slabSet D K n)) ^ (1 / (2:ℝ)))
        Filter.atTop (𝓝 0) := by
      have hct := (ENNReal.continuous_rpow_const (y := 1 / (2:ℝ))).tendsto 0
      have := hct.comp hmu
      simpa [ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 1 / 2)] using! this
    simpa using! ENNReal.Tendsto.const_mul hrpow (Or.inr enorm_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun n => bot_le) hbound

theorem lane2_exists_bound_of_compactSupport {f : SpatialCoordinates d → ℝ}
    (hf : Continuous f) (hsupp : HasCompactSupport f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |f x| ≤ M := by
  obtain ⟨M, hM⟩ := hsupp.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact le_trans (hM x hx) (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx, abs_zero]
    exact le_max_right _ _

/-- **The killed membership of an odd smooth datum.**  A smooth compactly
supported function on the doubled domain which vanishes linearly at the
reflection plane has its data on the lower half in the killed space. -/
theorem lane2_oddSmooth_mem_killed (D : EvenReflectionDomain d)
    {F : SpatialCoordinates d → ℝ} (hFsmooth : ContDiff ℝ ∞ F)
    (hFsupp : HasCompactSupport F)
    (hFsub : tsupport F ⊆ (D.U : Set (SpatialCoordinates d)))
    {L : ℝ} (hL0 : 0 ≤ L) (hFlin : ∀ x, |F x| ≤ L * |x D.i - D.z D.i|)
    (hmem : MemLp F 2 (volume.restrict (D.Ω : Set (SpatialCoordinates d))))
    (hmemg : ∀ j : Fin d, MemLp (fun x => fderiv ℝ F x (Pi.single j 1)) 2
      (volume.restrict (D.Ω : Set (SpatialCoordinates d)))) :
    ((hmem.toLp F, fun j => (hmemg j).toLp
      (fun x => fderiv ℝ F x (Pi.single j 1))) : SobolevData D.Ω)
      ∈ killedSobolevGraph D.Ω := by
  classical
  obtain ⟨C, hC0, hCb⟩ := lane2_exists_deriv_bound_smoothTransition
  obtain ⟨M, hM0, hM⟩ := lane2_exists_bound_of_compactSupport hFsmooth.continuous hFsupp
  set app : ℕ → 𝓓(D.Ω, ℝ) := fun n => lane2_slabApprox D hFsmooth hFsupp hFsub n
    with happ
  have hKc : IsCompact (tsupport F) := hFsupp
  -- off the slab the approximant is the datum, locally
  have hEq : ∀ (n : ℕ) (x : SpatialCoordinates d),
      x D.i < D.z D.i - 2 * lane2_slabEps n →
      (app n : SpatialCoordinates d → ℝ) =ᶠ[𝓝 x] F := by
    intro n x hx
    have hopen : IsOpen {y : SpatialCoordinates d |
        y D.i < D.z D.i - 2 * lane2_slabEps n} :=
      isOpen_lt (continuous_apply D.i) continuous_const
    filter_upwards [hopen.mem_nhds hx] with y hy
    rw [lane2_slabApprox_apply, lane2_slabCutoff_eq_one (lane2_slabEps_pos n)
      (le_of_lt hy), mul_one]
  -- the scalar estimate
  have hscal : Filter.Tendsto (fun n => eLpNorm
      (fun x => (app n : SpatialCoordinates d → ℝ) x - F x) 2
      (volume.restrict (D.Ω : Set (SpatialCoordinates d)))) Filter.atTop (𝓝 0) := by
    have hbridge : (fun n => eLpNorm
        (fun x => (app n : SpatialCoordinates d → ℝ) x - F x) 2
        (volume.restrict (D.Ω : Set (SpatialCoordinates d)))) =
        (fun n => SubdiffusiveProcess.RawLp.eLpNorm
          (fun x => (app n : SpatialCoordinates d → ℝ) x - F x) 2
          (volume.restrict (D.Ω : Set (SpatialCoordinates d)))) := by
      funext n
      symm
      apply SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded
      exact ((app n).continuous.aestronglyMeasurable.sub hFsmooth.continuous.aestronglyMeasurable)
    rw [hbridge]
    refine lane2_eLpNorm_tendsto_zero_of_slab D hKc (B := M) hM0 ?_ ?_
    · intro n x hx hxS
      by_cases hxK : x ∈ tsupport F
      · have hslab : ¬ (D.z D.i - 2 * lane2_slabEps n ≤ x D.i) := by
          intro h
          exact hxS ⟨⟨hx, hxK⟩, h⟩
        push_neg at hslab
        rw [lane2_slabApprox_apply, lane2_slabCutoff_eq_one (lane2_slabEps_pos n)
          (le_of_lt hslab), mul_one, sub_self]
      · rw [lane2_slabApprox_apply, image_eq_zero_of_notMem_tsupport hxK]
        ring
    · intro n x hx
      rw [lane2_slabApprox_apply]
      have hcut := lane2_slabCutoff_nonneg D.z D.i (lane2_slabEps n) x
      have hcut1 := lane2_slabCutoff_le_one D.z D.i (lane2_slabEps n) x
      have : F x * lane2_slabCutoff D.z D.i (lane2_slabEps n) x - F x
          = F x * (lane2_slabCutoff D.z D.i (lane2_slabEps n) x - 1) := by ring
      rw [this, abs_mul]
      have habs : |lane2_slabCutoff D.z D.i (lane2_slabEps n) x - 1| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith
      calc |F x| * |lane2_slabCutoff D.z D.i (lane2_slabEps n) x - 1|
          ≤ M * 1 := mul_le_mul (hM x) habs (abs_nonneg _) hM0
        _ = M := mul_one M
  -- the gradient estimate
  have hgrad : ∀ j : Fin d, Filter.Tendsto (fun n => eLpNorm
      (fun x => fderiv ℝ ((app n : 𝓓(D.Ω, ℝ)) : SpatialCoordinates d → ℝ) x
          (Pi.single j 1) - fderiv ℝ F x (Pi.single j 1)) 2
      (volume.restrict (D.Ω : Set (SpatialCoordinates d)))) Filter.atTop (𝓝 0) := by
    intro j
    have hcontg : Continuous (fun x => fderiv ℝ F x (Pi.single j 1)) :=
      (hFsmooth.continuous_fderiv_apply (by simp)).comp
        (continuous_id.prodMk continuous_const)
    obtain ⟨Mg, hMg0, hMg⟩ := lane2_exists_bound_of_compactSupport hcontg
      (hFsupp.fderiv_apply ℝ (Pi.single j 1))
    have hB0 : 0 ≤ Mg + 2 * L * C :=
      add_nonneg hMg0 (mul_nonneg (mul_nonneg (by norm_num) hL0) hC0)
    have hdiffF : ∀ y, DifferentiableAt ℝ F y :=
      fun y => (hFsmooth.differentiable (by simp)).differentiableAt
    have hbridge : (fun n => eLpNorm
        (fun x => fderiv ℝ (app n : SpatialCoordinates d → ℝ) x (Pi.single j 1) -
          fderiv ℝ F x (Pi.single j 1)) 2
        (volume.restrict (D.Ω : Set (SpatialCoordinates d)))) =
        (fun n => SubdiffusiveProcess.RawLp.eLpNorm
          (fun x => fderiv ℝ (app n : SpatialCoordinates d → ℝ) x (Pi.single j 1) -
            fderiv ℝ F x (Pi.single j 1)) 2
          (volume.restrict (D.Ω : Set (SpatialCoordinates d)))) := by
      funext n
      symm
      apply SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded
      exact (((app n).contDiff.continuous_fderiv_apply (by simp)).comp
        (continuous_id.prodMk continuous_const)).aestronglyMeasurable.sub hcontg.aestronglyMeasurable
    rw [hbridge]
    refine lane2_eLpNorm_tendsto_zero_of_slab D hKc (B := Mg + 2 * L * C) hB0 ?_ ?_
    · intro n x hx hxS
      by_cases hxK : x ∈ tsupport F
      · have hslab : ¬ (D.z D.i - 2 * lane2_slabEps n ≤ x D.i) := fun h =>
          hxS ⟨⟨hx, hxK⟩, h⟩
        push_neg at hslab
        rw [(hEq n x hslab).fderiv_eq, sub_self]
      · have hFnb : F =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
          filter_upwards [(isOpen_compl_iff.2 isClosed_closure).mem_nhds hxK] with y hy
          exact image_eq_zero_of_notMem_tsupport hy
        have happ0 : ((app n : 𝓓(D.Ω, ℝ)) : SpatialCoordinates d → ℝ)
            =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
          filter_upwards [(isOpen_compl_iff.2 isClosed_closure).mem_nhds hxK] with y hy
          rw [lane2_slabApprox_apply, image_eq_zero_of_notMem_tsupport hy, zero_mul]
        rw [happ0.fderiv_eq, hFnb.fderiv_eq, sub_self]
    · intro n x hx
      by_cases hslab : D.z D.i - 2 * lane2_slabEps n ≤ x D.i
      · have hprod : fderiv ℝ ((app n : 𝓓(D.Ω, ℝ)) : SpatialCoordinates d → ℝ) x
            = F x • fderiv ℝ (lane2_slabCutoff D.z D.i (lane2_slabEps n)) x
              + lane2_slabCutoff D.z D.i (lane2_slabEps n) x • fderiv ℝ F x := by
          have he : ((app n : 𝓓(D.Ω, ℝ)) : SpatialCoordinates d → ℝ)
              = F * lane2_slabCutoff D.z D.i (lane2_slabEps n) := by
            funext y
            exact lane2_slabApprox_apply D hFsmooth hFsupp hFsub n y
          rw [he]
          exact fderiv_mul (hdiffF x)
            (((lane2_slabCutoff_contDiff D.z D.i (lane2_slabEps n)).differentiable
              (by simp)).differentiableAt)
        rw [hprod]
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          smul_eq_mul]
        have hxlt : x D.i < D.z D.i := ((D.mem_iff x).mp hx).2
        have hdist : |x D.i - D.z D.i| ≤ 2 * lane2_slabEps n := by
          rw [abs_of_nonpos (by linarith)]
          linarith
        have hcut1 := lane2_slabCutoff_le_one D.z D.i (lane2_slabEps n) x
        have hcut0 := lane2_slabCutoff_nonneg D.z D.i (lane2_slabEps n) x
        have hterm1 : |(lane2_slabCutoff D.z D.i (lane2_slabEps n) x - 1) *
            fderiv ℝ F x (Pi.single j 1)| ≤ Mg := by
          rw [abs_mul]
          have h1 : |lane2_slabCutoff D.z D.i (lane2_slabEps n) x - 1| ≤ 1 := by
            rw [abs_le]; constructor <;> linarith
          calc |lane2_slabCutoff D.z D.i (lane2_slabEps n) x - 1| *
                |fderiv ℝ F x (Pi.single j 1)|
              ≤ 1 * Mg := mul_le_mul h1 (hMg x) (abs_nonneg _) (by norm_num)
            _ = Mg := one_mul Mg
        have hterm2 : |F x * fderiv ℝ
            (lane2_slabCutoff D.z D.i (lane2_slabEps n)) x (Pi.single j 1)|
            ≤ 2 * L * C := by
          rw [abs_mul]
          have hFb : |F x| ≤ L * (2 * lane2_slabEps n) :=
            le_trans (hFlin x) (mul_le_mul_of_nonneg_left hdist hL0)
          have hcb := lane2_slabCutoff_fderiv_bound D.z D.i
            (lane2_slabEps_pos n) hC0 hCb x j
          have hCe : 0 ≤ C / lane2_slabEps n := div_nonneg hC0 (lane2_slabEps_pos n).le
          calc |F x| * |fderiv ℝ (lane2_slabCutoff D.z D.i (lane2_slabEps n)) x
                (Pi.single j 1)|
              ≤ (L * (2 * lane2_slabEps n)) * (C / lane2_slabEps n) :=
                mul_le_mul hFb hcb (abs_nonneg _)
                  (mul_nonneg hL0 (by linarith [lane2_slabEps_pos n]))
            _ = 2 * L * C := by
                field_simp [ne_of_gt (lane2_slabEps_pos n)]
        have hsplit : F x * fderiv ℝ (lane2_slabCutoff D.z D.i (lane2_slabEps n)) x
              (Pi.single j 1) +
            lane2_slabCutoff D.z D.i (lane2_slabEps n) x *
              fderiv ℝ F x (Pi.single j 1) - fderiv ℝ F x (Pi.single j 1)
            = (lane2_slabCutoff D.z D.i (lane2_slabEps n) x - 1) *
              fderiv ℝ F x (Pi.single j 1) +
              F x * fderiv ℝ (lane2_slabCutoff D.z D.i (lane2_slabEps n)) x
                (Pi.single j 1) := by ring
        rw [hsplit]
        exact le_trans (abs_add_le _ _) (add_le_add hterm1 hterm2)
      · push_neg at hslab
        rw [(hEq n x hslab).fderiv_eq, sub_self, abs_zero]
        exact hB0
  -- assemble the two convergences into the killed space
  have hmemn : ∀ n, MemLp ((app n : 𝓓(D.Ω, ℝ)) : SpatialCoordinates d → ℝ) 2
      (volume.restrict (D.Ω : Set (SpatialCoordinates d))) := fun n =>
    (Lp.memLp (testL2 (app n))).ae_eq (testL2_coeFn (app n))
  have hmemgn : ∀ (n : ℕ) (j : Fin d), MemLp
      (fun x => fderiv ℝ ((app n : 𝓓(D.Ω, ℝ)) : SpatialCoordinates d → ℝ) x
        (Pi.single j 1)) 2
      (volume.restrict (D.Ω : Set (SpatialCoordinates d))) := fun n j =>
    (Lp.memLp (testPartialL2 (app n) j)).ae_eq (testPartialL2_coeFn (app n) j)
  have hid1 : ∀ n, (hmemn n).toLp _ = testL2 (app n) := fun n =>
    Lp.ext ((MemLp.coeFn_toLp _).trans (testL2_coeFn (app n)).symm)
  have hid2 : ∀ (n : ℕ) (j : Fin d), (hmemgn n j).toLp _ = testPartialL2 (app n) j :=
    fun n j => Lp.ext ((MemLp.coeFn_toLp _).trans (testPartialL2_coeFn (app n) j).symm)
  have h1 : Filter.Tendsto (fun n => testL2 (app n)) Filter.atTop
      (𝓝 (hmem.toLp F)) := by
    have h := Lane4.tendsto_toLp_of_eLpNorm_sub_tendsto
      (volume.restrict (D.Ω : Set (SpatialCoordinates d))) hmem hmemn hscal
    simpa [hid1] using! h
  have h2 : ∀ j : Fin d, Filter.Tendsto (fun n => testPartialL2 (app n) j)
      Filter.atTop (𝓝 ((hmemg j).toLp (fun x => fderiv ℝ F x (Pi.single j 1)))) := by
    intro j
    have h := Lane4.tendsto_toLp_of_eLpNorm_sub_tendsto
      (volume.restrict (D.Ω : Set (SpatialCoordinates d))) (hmemg j)
      (fun n => hmemgn n j) (hgrad j)
    simpa [hid2] using! h
  have hconv : Filter.Tendsto (fun n => smoothSobolevData (app n)) Filter.atTop
      (𝓝 ((hmem.toLp F, fun j => (hmemg j).toLp
        (fun x => fderiv ℝ F x (Pi.single j 1))) : SobolevData D.Ω)) :=
    Filter.Tendsto.prodMk_nhds h1 (tendsto_pi_nhds.2 h2)
  rw [← SetLike.mem_coe, killedSobolevGraph_coe_eq_closure]
  exact mem_closure_of_tendsto hconv (Filter.Eventually.of_forall fun n => ⟨app n, rfl⟩)

/-! ## The chain rule for a coordinate reflection -/

/-- The derivative of a coordinate reflection: it flips the sign of the selected
coordinates. -/
def lane2_reflectionCLM (I : Finset (Fin d)) :
    SpatialCoordinates d →L[ℝ] SpatialCoordinates d :=
  ContinuousLinearMap.pi fun j =>
    coordinateReflectionSign I j • (ContinuousLinearMap.proj j :
      SpatialCoordinates d →L[ℝ] ℝ)

theorem lane2_hasFDerivAt_coordinateReflection (z : SpatialCoordinates d)
    (I : Finset (Fin d)) (x : SpatialCoordinates d) :
    HasFDerivAt (coordinateReflection z I) (lane2_reflectionCLM I) x := by
  have hfun : coordinateReflection z I
      = fun y : SpatialCoordinates d =>
        ((fun j => if j ∈ I then 2 * z j else 0) : SpatialCoordinates d)
          + lane2_reflectionCLM I y := by
    funext y j
    simp only [Pi.add_apply, lane2_reflectionCLM, ContinuousLinearMap.pi_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
      coordinateReflection, coordinateReflectionSign]
    by_cases hj : j ∈ I <;> simp [hj] <;> ring
  rw [hfun]
  exact (lane2_reflectionCLM I).hasFDerivAt.const_add _

theorem lane2_reflectionCLM_single (I : Finset (Fin d)) (j : Fin d) :
    lane2_reflectionCLM I (Pi.single j (1 : ℝ))
      = coordinateReflectionSign I j • (Pi.single j (1 : ℝ)) := by
  funext k
  simp only [lane2_reflectionCLM, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    Pi.smul_apply]
  by_cases hk : k = j
  · subst hk; simp
  · simp [Pi.single_eq_of_ne hk]

/-- The chain rule for a smooth function composed with a coordinate
reflection. -/
theorem lane2_fderiv_comp_coordinateReflection {f : SpatialCoordinates d → ℝ}
    (hf : ContDiff ℝ ∞ f) (z : SpatialCoordinates d) (I : Finset (Fin d))
    (x : SpatialCoordinates d) (j : Fin d) :
    fderiv ℝ (fun y => f (coordinateReflection z I y)) x (Pi.single j 1)
      = coordinateReflectionSign I j *
        fderiv ℝ f (coordinateReflection z I x) (Pi.single j 1) := by
  have hcomp : HasFDerivAt (fun y => f (coordinateReflection z I y))
      ((fderiv ℝ f (coordinateReflection z I x)).comp (lane2_reflectionCLM I)) x :=
    (hf.differentiable (by simp)).differentiableAt.hasFDerivAt.comp x
      (lane2_hasFDerivAt_coordinateReflection z I x)
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  rw [lane2_reflectionCLM_single, map_smul, smul_eq_mul]

/-! ## The killed test combination -/

namespace EvenReflectionDomain

variable (D : EvenReflectionDomain d)

/-- The combination `ψ|_Ω - R*(ψ|_{ρΩ})` of a SMOOTH test on the doubled domain
lies in the killed space of the lower half. -/
theorem lane2_restrictSub_smooth_mem_killed (χ : 𝓓(D.U, ℝ)) :
    sobolevDataRestrict D.Ω_le (smoothSobolevData χ)
      - D.reflectedRestrict (smoothSobolevData χ) ∈ killedSobolevGraph D.Ω := by
  have hFsmooth := D.lane2_oddTestFun_contDiff χ
  have hFsupp := D.lane2_oddTestFun_hasCompactSupport χ
  have hFsub := D.lane2_oddTestFun_tsupport_subset χ
  obtain ⟨L, hL0, hFlin⟩ := D.lane2_oddTestFun_linear_bound χ
  have hmem : MemLp (D.lane2_oddTestFun χ) 2
      (volume.restrict (D.Ω : Set (SpatialCoordinates d))) :=
    hFsmooth.continuous.memLp_of_hasCompactSupport hFsupp
  have hmemg : ∀ j : Fin d, MemLp
      (fun x => fderiv ℝ (D.lane2_oddTestFun χ) x (Pi.single j 1)) 2
      (volume.restrict (D.Ω : Set (SpatialCoordinates d))) := by
    intro j
    refine Continuous.memLp_of_hasCompactSupport ?_ (hFsupp.fderiv_apply ℝ _)
    exact (hFsmooth.continuous_fderiv_apply (by simp)).comp
      (continuous_id.prodMk continuous_const)
  have hkey := lane2_oddSmooth_mem_killed D hFsmooth hFsupp hFsub hL0 hFlin hmem hmemg
  -- the measure-preserving reflection, used to transport the a.e. identities
  have hmp : MeasurePreserving (coordinateReflection D.z {D.i})
      (volume.restrict (D.Ω : Set (SpatialCoordinates d)))
      (volume.restrict (D.reflected : Set (SpatialCoordinates d))) :=
    coordinateReflection_domain_measurePreserving D.z {D.i} D.preimage_reflected
  -- the chain rule for the reflected piece
  have hchain : ∀ (x : SpatialCoordinates d) (j : Fin d),
      fderiv ℝ (D.lane2_oddTestFun χ) x (Pi.single j 1)
        = fderiv ℝ (χ : SpatialCoordinates d → ℝ) x (Pi.single j 1)
          - coordinateReflectionSign {D.i} j *
            fderiv ℝ (χ : SpatialCoordinates d → ℝ)
              (coordinateReflection D.z {D.i} x) (Pi.single j 1) := by
    intro x j
    have hdiff1 : DifferentiableAt ℝ (χ : SpatialCoordinates d → ℝ) x :=
      (χ.contDiff.differentiable (by simp)).differentiableAt
    have hdiff2 : DifferentiableAt ℝ
        (fun y => (χ : SpatialCoordinates d → ℝ)
          (coordinateReflection D.z {D.i} y)) x :=
      ((χ.contDiff.comp
        (lane2_contDiff_coordinateReflection D.z {D.i})).differentiable
          (by simp)).differentiableAt
    have hsub : fderiv ℝ (D.lane2_oddTestFun χ) x
        = fderiv ℝ (χ : SpatialCoordinates d → ℝ) x
          - fderiv ℝ (fun y => (χ : SpatialCoordinates d → ℝ)
            (coordinateReflection D.z {D.i} y)) x := by
      exact fderiv_sub hdiff1 hdiff2
    rw [hsub, ContinuousLinearMap.sub_apply,
      lane2_fderiv_comp_coordinateReflection χ.contDiff D.z {D.i} x j]
  -- identify the two data
  have hcomp1 : (sobolevDataRestrict D.Ω_le (smoothSobolevData χ)
      - D.reflectedRestrict (smoothSobolevData χ)).1 = hmem.toLp _ := by
    refine Lp.ext ?_
    refine Filter.EventuallyEq.trans ?_ (MemLp.coeFn_toLp hmem).symm
    have h1 := Lp.coeFn_sub (domainLpRestrict D.Ω_le (testL2 χ))
      (reflectionLp D.z {D.i} D.preimage_reflected
        (domainLpRestrict D.reflected_le (testL2 χ)))
    have h2 := domainLpRestrict_coeFn D.Ω_le (testL2 χ)
    have h3 := ae_restrict_of_ae_restrict_of_subset
      (μ := (volume : Measure (SpatialCoordinates d))) D.Ω_le (testL2_coeFn χ)
    have h4 := reflectionLp_coeFn D.z {D.i} D.preimage_reflected
      (domainLpRestrict D.reflected_le (testL2 χ))
    have h5 := hmp.quasiMeasurePreserving.ae
      (domainLpRestrict_coeFn D.reflected_le (testL2 χ))
    have h6 := hmp.quasiMeasurePreserving.ae
      (ae_restrict_of_ae_restrict_of_subset
        (μ := (volume : Measure (SpatialCoordinates d))) D.reflected_le
        (testL2_coeFn χ))
    filter_upwards [h1, h2, h3, h4, h5, h6] with x e1 e2 e3 e4 e5 e6
    show (((domainLpRestrict D.Ω_le (testL2 χ) -
        reflectionLp D.z {D.i} D.preimage_reflected
          (domainLpRestrict D.reflected_le (testL2 χ))) : DomainL2 D.Ω) :
        SpatialCoordinates d → ℝ) x = _
    rw [e1, Pi.sub_apply, e2, e3]
    simp only [Function.comp_apply] at e4 e5 e6 ⊢
    rw [e4, e5, e6]
    rfl
  have hcomp2 : ∀ j : Fin d, (sobolevDataRestrict D.Ω_le (smoothSobolevData χ)
      - D.reflectedRestrict (smoothSobolevData χ)).2 j = (hmemg j).toLp _ := by
    intro j
    refine Lp.ext ?_
    refine Filter.EventuallyEq.trans ?_ (MemLp.coeFn_toLp (hmemg j)).symm
    have h1 := Lp.coeFn_sub (domainLpRestrict D.Ω_le (testPartialL2 χ j))
      ((D.reflectedRestrict (smoothSobolevData χ)).2 j)
    have h2 := domainLpRestrict_coeFn D.Ω_le (testPartialL2 χ j)
    have h3 := ae_restrict_of_ae_restrict_of_subset
      (μ := (volume : Measure (SpatialCoordinates d))) D.Ω_le
      (testPartialL2_coeFn χ j)
    have h4 := D.reflectedRestrict_snd_coeFn (smoothSobolevData χ) j
    have h5 := hmp.quasiMeasurePreserving.ae
      (domainLpRestrict_coeFn D.reflected_le (testPartialL2 χ j))
    have h6 := hmp.quasiMeasurePreserving.ae
      (ae_restrict_of_ae_restrict_of_subset
        (μ := (volume : Measure (SpatialCoordinates d))) D.reflected_le
        (testPartialL2_coeFn χ j))
    filter_upwards [h1, h2, h3, h4, h5, h6] with x e1 e2 e3 e4 e5 e6
    show (((domainLpRestrict D.Ω_le (testPartialL2 χ j) -
        (D.reflectedRestrict (smoothSobolevData χ)).2 j) : DomainL2 D.Ω) :
        SpatialCoordinates d → ℝ) x = _
    have e4' : (((D.reflectedRestrict (smoothSobolevData χ)).2 j : DomainL2 D.Ω) :
        SpatialCoordinates d → ℝ) x
        = coordinateReflectionSign {D.i} j *
          ((domainLpRestrict D.reflected_le (testPartialL2 χ j) :
              DomainL2 D.reflected) : SpatialCoordinates d → ℝ)
            (coordinateReflection D.z {D.i} x) := e4
    rw [e1, Pi.sub_apply, e2, e3, e4', e5, e6, hchain x j]
  have hEq : sobolevDataRestrict D.Ω_le (smoothSobolevData χ)
      - D.reflectedRestrict (smoothSobolevData χ)
      = ((hmem.toLp (D.lane2_oddTestFun χ), fun j => (hmemg j).toLp
        (fun x => fderiv ℝ (D.lane2_oddTestFun χ) x (Pi.single j 1))) :
          SobolevData D.Ω) :=
    Prod.ext hcomp1 (funext hcomp2)
  rw [hEq]
  exact hkey

end EvenReflectionDomain

/-- Restriction of Sobolev data to a subdomain is continuous. -/
theorem lane2_continuous_sobolevDataRestrict {V U : Opens (SpatialCoordinates d)}
    (hV : V ≤ U) : Continuous (sobolevDataRestrict (V := V) (U := U) hV) := by
  have hsub : ∀ f g : DomainL2 U, domainLpRestrict hV (f - g)
      = domainLpRestrict hV f - domainLpRestrict hV g := by
    intro f g
    have h : f - g = f + (-1 : ℝ) • g := by module
    rw [h, domainLpRestrict_add, domainLpRestrict_smul]
    module
  have hlip : LipschitzWith 1 (fun f : DomainL2 U => domainLpRestrict hV f) := by
    refine LipschitzWith.of_dist_le_mul fun f g => ?_
    rw [dist_eq_norm, dist_eq_norm, ← hsub]
    simpa using! domainLpRestrict_norm_le hV (f - g)
  refine Continuous.prodMk (hlip.continuous.comp continuous_fst) ?_
  refine continuous_pi fun j => ?_
  exact hlip.continuous.comp (((continuous_apply j).comp continuous_snd))

namespace EvenReflectionDomain

variable (D : EvenReflectionDomain d)

/-- **Killed tests survive the reflection.**  For `ψ` in the killed space of the
doubled domain, `ψ|_Ω - R*(ψ|_{ρΩ})` lies in the killed space of the lower
half.  This is what lets the odd-extension transport be run on the killed test
class, which is the class a Dirichlet cell problem supplies. -/
theorem lane2_restrictSub_mem_killed {ψ : SobolevData D.U}
    (hψ : ψ ∈ killedSobolevGraph D.U) :
    sobolevDataRestrict D.Ω_le ψ - D.reflectedRestrict ψ
      ∈ killedSobolevGraph D.Ω := by
  have hcont : Continuous (fun w : SobolevData D.U =>
      sobolevDataRestrict D.Ω_le w - D.reflectedRestrict w) := by
    refine Continuous.sub (lane2_continuous_sobolevDataRestrict D.Ω_le) ?_
    exact (reflectionSobolevData D.z {D.i} D.preimage_reflected).continuous.comp
      (lane2_continuous_sobolevDataRestrict D.reflected_le)
  have hm : Set.MapsTo (fun w : SobolevData D.U =>
      sobolevDataRestrict D.Ω_le w - D.reflectedRestrict w)
      (Set.range (smoothSobolevData (Ω := D.U)))
      (killedSobolevGraph D.Ω : Set (SobolevData D.Ω)) := by
    rintro w ⟨χ, rfl⟩
    exact D.lane2_restrictSub_smooth_mem_killed χ
  apply hm.closure_left hcont isClosed_killedSobolevGraph
  rw [← killedSobolevGraph_coe_eq_closure]
  exact hψ

end EvenReflectionDomain

end SubdiffusiveProcess
