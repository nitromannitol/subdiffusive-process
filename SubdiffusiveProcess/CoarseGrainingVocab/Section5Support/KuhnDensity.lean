module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn.ZeroExtension
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.KuhnInterpolationError
public import Homogenization.Sobolev.H1.BasicLemmas
public import Homogenization.Sobolev.Truncation.Basic

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open Homogenization Kuhn MeasureTheory Metric Set
open scoped ENNReal

noncomputable section

/-! ## The mesh of a triadic cube as a closed cover -/

variable {d : ℕ}

/-- The closed hull of the canonical mesh of a triadic cube is the closed cube. -/
theorem meshClosedCarrier_triadicSimplexPartition (Q : TriadicCube d) {j : ℤ}
    (hj : j ≤ Q.scale) :
    meshClosedCarrier (triadicSimplexPartition Q j) =
      Metric.closedBall (cubeCenter Q) (cubeRadius Q) := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    obtain ⟨T, hT, hxT⟩ := mem_meshClosedCarrier_iff.mp hx
    exact closedCarrier_subset_closedBall_of_mem_triadicSimplexPartition hj hT hxT
  · refine (closedBall_subset_closure_cubeSet Q).trans ?_
    refine closure_minimal ?_ (isClosed_meshClosedCarrier _)
    rw [cubeSet_eq_iUnion_triadicSimplexPartition Q hj]
    exact Set.iUnion₂_mono fun T _ => T.carrier_subset_closedCarrier

/-- The open cube lies in the interior of the mesh hull. -/
theorem openCubeSet_subset_interior_meshClosedCarrier (Q : TriadicCube d) {j : ℤ}
    (hj : j ≤ Q.scale) :
    openCubeSet Q ⊆ interior (meshClosedCarrier (triadicSimplexPartition Q j)) := by
  refine interior_maximal ?_ (isOpen_openCubeSet Q)
  rw [meshClosedCarrier_triadicSimplexPartition Q hj]
  exact (openCubeSet_subset_cubeSet Q).trans (cubeSet_subset_closedBall Q)

/-! ## Cells that carry the datum -/

/-- **A cell with a loaded vertex lies inside `U`.**  If the closed cell has a
vertex in `K` and its side is below the thickening radius that keeps `K` inside
`U`, then the whole cell is inside `U`. -/
theorem closedCarrier_subset_of_vertex_mem {U K : Set (Vec d)} {delta : ℝ}
    (hKU : Metric.cthickening delta K ⊆ U) {T : KuhnCell d}
    (hside : cubeScaleFactor T.supportCube ≤ delta) {k : Fin (d + 1)}
    (hk : T.vertex k ∈ K) : T.closedCarrier ⊆ U := by
  intro w hw
  refine hKU (Metric.mem_cthickening_of_dist_le w (T.vertex k) delta K hk ?_)
  exact (dist_le_cubeScaleFactor_of_mem_closedCarrier T hw
    (T.vertex_mem_closedCarrier k)).trans hside

/-- **A cell leaving `U` carries no datum.**  Contrapositive of the previous
statement: an interpolant on such a cell is identically zero. -/
theorem kuhnInterp_eq_zero_of_not_subset {U K : Set (Vec d)} {delta : ℝ}
    (hKU : Metric.cthickening delta K ⊆ U) {phi : Vec d → ℝ}
    (hphi : ∀ x, x ∉ K → phi x = 0) {T : KuhnCell d}
    (hside : cubeScaleFactor T.supportCube ≤ delta)
    (hT : ¬ T.closedCarrier ⊆ U) : kuhnInterp T phi = 0 := by
  refine kuhnInterp_eq_zero_of_vertex_eq_zero T fun k => hphi _ fun hk => ?_
  exact hT (closedCarrier_subset_of_vertex_mem hKU hside hk)

/-! ## The `H^1` competitor built from one smooth function -/

variable {n : ℕ}

/-- **(S2a) for one smooth compactly supported function.**  For every `eps > 0`
there is a mesh scale `j` at which the Kuhn interpolant of `phi` is a genuine
`H^1(U)` function, cellwise affine, vanishing off a compact subset of `U`, and
with gradient within `eps` of `nabla phi` almost everywhere on `U`.

This is the whole content of the source's "conforming piecewise-affine functions
are dense": the passage from a general `H_0^1` function to a smooth one is
carried by the `H10Function` package itself. -/
theorem exists_kuhnAffine_h1_approx {Q : TriadicCube (n + 1)}
    {U : Set (Vec (n + 1))} (hUopen : IsOpen U) (hUbdd : Bornology.IsBounded U)
    (hUQ : U ⊆ openCubeSet Q) {phi : Vec (n + 1) → ℝ} (hphi : ContDiff ℝ 1 phi)
    (hphic : HasCompactSupport phi) (hphisub : tsupport phi ⊆ U) {eps : ℝ}
    (heps : 0 < eps) :
    ∃ (j : ℤ) (w : H1Function U) (Kw : Set (Vec (n + 1))),
      j ≤ Q.scale ∧
      w.toFun = zeroExtendedKuhnAffine (triadicSimplexPartition Q j) phi ∧
      IsCompact Kw ∧ Kw ⊆ U ∧ (∀ x ∉ Kw, w.toFun x = 0) ∧
      (∀ T ∈ triadicSimplexPartition Q j, ∀ x ∈ T.openCarrier,
        w.grad x = kuhnSlope T phi) ∧
      (∀ i : Fin (n + 1), ∀ᵐ x ∂(volume.restrict U),
        |w.grad x i - fderiv ℝ phi x (basisVec i)| ≤ eps) := by
  classical
  -- finiteness of the ambient measure on `U`
  have hUfin : volume U < ⊤ := by
    have hcl : IsCompact (closure U) :=
      Metric.isCompact_of_isClosed_isBounded isClosed_closure hUbdd.closure
    exact lt_of_le_of_lt (measure_mono subset_closure) hcl.measure_lt_top
  haveI : IsFiniteMeasure (volume.restrict U) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hUfin⟩
  -- the separation of the datum from the boundary
  obtain ⟨delta, hdelta, hKU⟩ :=
    IsCompact.exists_cthickening_subset_open hphic hUopen hphisub
  -- the mesh scale
  obtain ⟨s₁, hs₁⟩ :=
    exists_scale_forall_vecNormSq_kuhnSlope_sub_gradVec_le hphi
      (K := Metric.closedBall (cubeCenter Q) (cubeRadius Q)) (isCompact_closedBall _ _)
      (eps := eps ^ 2) (by positivity)
  obtain ⟨s₂, hs₂⟩ := Kuhn.exists_zpow_three_lt hdelta
  set j : ℤ := min (min s₁ s₂) Q.scale with hj_def
  have hjQ : j ≤ Q.scale := min_le_right _ _
  have hj₁ : j ≤ s₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hj₂ : j ≤ s₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  set cells : Finset (KuhnCell (n + 1)) := triadicSimplexPartition Q j with hcells
  have hscale : ∀ T ∈ cells, T.supportCube.scale = j := fun T hT =>
    supportCube_scale_eq_of_mem_triadicSimplexPartition hjQ hT
  have hside : ∀ T ∈ cells, cubeScaleFactor T.supportCube ≤ delta := by
    intro T hT
    rw [cubeScaleFactor, hscale T hT]
    exact le_of_lt (lt_of_le_of_lt (zpow_le_zpow_right₀ (by norm_num) hj₂) hs₂)
  have hsideK : ∀ T ∈ cells, T.supportCube.scale ≤ s₁ := fun T hT => (hscale T hT) ▸ hj₁
  have hcellK : ∀ T ∈ cells,
      T.closedCarrier ⊆ Metric.closedBall (cubeCenter Q) (cubeRadius Q) := fun T hT =>
    closedCarrier_subset_closedBall_of_mem_triadicSimplexPartition hjQ hT
  -- vanishing of the interpolant on the cells that leave `U`
  have hzerocell : ∀ T ∈ cells, ¬ T.closedCarrier ⊆ U → kuhnInterp T phi = 0 := by
    intro T hT hnot
    exact kuhnInterp_eq_zero_of_not_subset hKU
      (fun x hx => image_eq_zero_of_notMem_tsupport hx) (hside T hT) hnot
  -- continuity of the zero extension
  have hcont : Continuous (zeroExtendedKuhnAffine cells phi) := by
    refine continuous_zeroExtendedKuhnAffine_of_kuhnInterp_eq_zero hscale phi ?_
    intro T hT x hxT hxint
    have hzz : kuhnInterp T phi = 0 := by
      refine hzerocell T hT fun hsub => ?_
      exact hxint (openCubeSet_subset_interior_meshClosedCarrier Q hjQ (hUQ (hsub hxT)))
    simpa using congrFun hzz x
  -- the compact support inside `U`
  set loaded : Finset (KuhnCell (n + 1)) :=
    cells.filter (fun T => T.closedCarrier ⊆ U) with hloaded
  set Kw : Set (Vec (n + 1)) := meshClosedCarrier loaded with hKw
  have hKwcompact : IsCompact Kw :=
    loaded.finite_toSet.isCompact_biUnion fun T _ => isCompact_closedCarrier T
  have hKwsub : Kw ⊆ U := by
    intro x hx
    obtain ⟨T, hT, hxT⟩ := mem_meshClosedCarrier_iff.mp hx
    exact (Finset.mem_filter.mp hT).2 hxT
  have hzeroKw : ∀ x ∉ Kw, zeroExtendedKuhnAffine cells phi x = 0 := by
    intro x hx
    by_cases hmem : ∃ T ∈ cells, x ∈ T.closedCarrier
    · obtain ⟨T, hT, hxT⟩ := hmem
      rw [zeroExtendedKuhnAffine_of_mem_closedCarrier hscale phi hT hxT]
      have hzz : kuhnInterp T phi = 0 := by
        refine hzerocell T hT fun hsub => ?_
        exact hx (mem_meshClosedCarrier_iff.mpr
          ⟨T, Finset.mem_filter.mpr ⟨hT, hsub⟩, hxT⟩)
      simpa using congrFun hzz x
    · push_neg at hmem
      exact zeroExtendedKuhnAffine_of_forall_notMem cells phi hmem
  have hcompactsupport : HasCompactSupport (zeroExtendedKuhnAffine cells phi) :=
    HasCompactSupport.intro hKwcompact hzeroKw
  -- the `H^1` witness
  refine ⟨j,
    ⟨zeroExtendedKuhnAffine cells phi,
      fun x i => zeroExtendedKuhnAffineCoordDeriv cells phi i x,
      (hcont.memLp_of_hasCompactSupport hcompactsupport).mono_measure
        Measure.restrict_le_self,
      ?_,
      fun i => (hasWeakPartialDerivOn_univ_zeroExtendedKuhnAffine cells phi hscale hcont
        i).restrict hUopen (Set.subset_univ _)⟩,
    Kw, hjQ, rfl, hKwcompact, hKwsub, hzeroKw, ?_, ?_⟩
  · -- the coordinate derivatives are square integrable
    intro i
    refine MemLp.of_bound
      (measurable_zeroExtendedKuhnAffineCoordDeriv cells phi hcont i).aestronglyMeasurable
      (zeroExtendedKuhnAffineCoordBound cells phi i) ?_
    exact Filter.Eventually.of_forall fun x =>
      norm_zeroExtendedKuhnAffineCoordDeriv_le cells phi hscale hcont i x
  · -- the gradient is cellwise the Kuhn slope
    intro T hT x hxT
    funext i
    exact zeroExtendedKuhnAffineCoordDeriv_eq_of_mem_openCarrier hscale hT hxT i
  · -- the almost-everywhere gradient estimate
    intro i
    have hUmeas : MeasurableSet U := hUopen.measurableSet
    -- almost every point of `U` lies in the interior of some cell
    have hnull : volume (U \ ⋃ T ∈ (cells : Set (KuhnCell (n + 1))), T.openCarrier) = 0 := by
      refine measure_mono_null (t := ⋃ T ∈ (cells : Set (KuhnCell (n + 1))),
        (T.closedCarrier \ T.openCarrier)) ?_ ?_
      · rintro x ⟨hxU, hxout⟩
        have hxcube : x ∈ cubeSet Q :=
          openCubeSet_subset_cubeSet Q (hUQ hxU)
        rw [cubeSet_eq_iUnion_triadicSimplexPartition Q hjQ] at hxcube
        obtain ⟨T, hT, hxT⟩ := by simpa only [Set.mem_iUnion] using hxcube
        refine Set.mem_iUnion₂.mpr ⟨T, hT, T.carrier_subset_closedCarrier hxT, ?_⟩
        exact fun hxop => hxout (Set.mem_iUnion₂.mpr ⟨T, hT, hxop⟩)
      · exact (measure_biUnion_null_iff cells.finite_toSet.countable).mpr
          fun T _ => volume_closedCarrier_diff_openCarrier T
    have hae : ∀ᵐ x ∂volume,
        x ∈ U → ∃ T ∈ cells, x ∈ T.openCarrier := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx hxU
      by_contra hcon
      refine hx ⟨hxU, fun hmem => ?_⟩
      obtain ⟨T, hT, hxT⟩ := Set.mem_iUnion₂.mp hmem
      exact hcon ⟨T, hT, hxT⟩
    rw [ae_restrict_iff' hUmeas]
    filter_upwards [hae] with x hx hxU
    obtain ⟨T, hT, hxT⟩ := hx hxU
    have hxC : x ∈ T.closedCarrier := T.openCarrier_subset_closedCarrier hxT
    have hslope := hs₁ T (hsideK T hT) (hcellK T hT) x hxC
    have hderiv : zeroExtendedKuhnAffineCoordDeriv cells phi i x = kuhnSlope T phi i :=
      zeroExtendedKuhnAffineCoordDeriv_eq_of_mem_openCarrier hscale hT hxT i
    have hvns : vecNormSq (kuhnSlope T phi - gradVec phi x) =
        ∑ m, (kuhnSlope T phi - gradVec phi x) m *
          (kuhnSlope T phi - gradVec phi x) m := rfl
    have hsingle := Finset.single_le_sum (f := fun m : Fin (n + 1) =>
      (kuhnSlope T phi - gradVec phi x) m * (kuhnSlope T phi - gradVec phi x) m)
      (fun m _ => mul_self_nonneg _) (Finset.mem_univ i)
    rw [← hvns] at hsingle
    have hcoord : (kuhnSlope T phi i - gradVec phi x i) ^ 2 ≤ eps ^ 2 := by
      have hrw : (kuhnSlope T phi i - gradVec phi x i) ^ 2 =
          (kuhnSlope T phi - gradVec phi x) i * (kuhnSlope T phi - gradVec phi x) i := by
        rw [Pi.sub_apply]; ring
      rw [hrw]
      exact hsingle.trans hslope
    have habs : |kuhnSlope T phi i - gradVec phi x i| ≤ eps := by
      have h1 : Real.sqrt ((kuhnSlope T phi i - gradVec phi x i) ^ 2) ≤
          Real.sqrt (eps ^ 2) := Real.sqrt_le_sqrt hcoord
      rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq heps.le] at h1
    show |zeroExtendedKuhnAffineCoordDeriv cells phi i x -
      fderiv ℝ phi x (basisVec i)| ≤ eps
    rw [hderiv]
    exact habs

/-! ## The source's simplex as a domain -/

/-- One convex-combination step for a strict linear inequality. -/
private theorem convex_step {a b xi xj yi yj ci cj : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (hx : xi - ci < xj - cj) (hy : yi - ci < yj - cj) :
    a * xi + b * yi - ci < a * xj + b * yj - cj := by
  have hci : a * ci + b * ci = ci := by rw [← add_mul, hab, one_mul]
  have hcj : a * cj + b * cj = cj := by rw [← add_mul, hab, one_mul]
  rcases lt_or_eq_of_le ha with hapos | ha0
  · have h1 : a * (xi - ci) < a * (xj - cj) := mul_lt_mul_of_pos_left hx hapos
    have h2 : b * (yi - ci) ≤ b * (yj - cj) := mul_le_mul_of_nonneg_left hy.le hb
    have e1 : a * (xi - ci) = a * xi - a * ci := by ring
    have e2 : a * (xj - cj) = a * xj - a * cj := by ring
    have e3 : b * (yi - ci) = b * yi - b * ci := by ring
    have e4 : b * (yj - cj) = b * yj - b * cj := by ring
    rw [e1, e2] at h1
    rw [e3, e4] at h2
    linarith
  · have hb1 : b = 1 := by linarith
    have ha' : a = 0 := ha0.symm
    rw [ha', hb1]
    linarith

/-- The open Kuhn simplex is convex: it is a box cut by strict order
conditions, all of them linear. -/
theorem convex_openCarrier (T : KuhnCell d) : Convex ℝ T.openCarrier := by
  intro x hx y hy a b ha hb hab
  rw [KuhnCell.mem_openCarrier_iff] at hx hy ⊢
  refine ⟨convex_openCubeSet T.supportCube hx.1 hy.1 ha hb hab, ?_⟩
  intro i j hij
  have hxo := hx.2 i j hij
  have hyo := hy.2 i j hij
  simp only [triadicLocalCoordinate, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hxo hyo ⊢
  exact convex_step ha hb hab hxo hyo

/-- The open Kuhn simplex is a bounded domain. -/
theorem isBoundedDomain_openCarrier (T : KuhnCell d) :
    IsBoundedDomain T.openCarrier := by
  obtain ⟨R, hR, hbound⟩ := isBoundedDomain_openCubeSet T.supportCube
  exact ⟨R, hR, fun x hx i => hbound x (T.openCarrier_subset_openCubeSet hx) i⟩

/-- **The source's `spx_n^pi(z)` is an open bounded convex domain.**  This is the
hypothesis under which the library's `H_0^1` machinery applies to it. -/
theorem isOpenBoundedConvexDomain_openCarrier (T : KuhnCell d) :
    IsOpenBoundedConvexDomain T.openCarrier :=
  ⟨isOpen_openCarrier T, isBoundedDomain_openCarrier T, convex_openCarrier T⟩

/-! ## (S2a): density of the conforming Kuhn space in `H_0^1` -/



theorem exists_kuhn_h10_approx {Q : TriadicCube (n + 1)} {U : Set (Vec (n + 1))}
    (hU : IsOpenBoundedConvexDomain U) (hUQ : U ⊆ openCubeSet Q)
    (u : H10Function U) {eps : ℝ} (heps : 0 < eps) :
    ∃ (j : ℤ) (phi : Vec (n + 1) → ℝ) (w : H1Function U),
      j ≤ Q.scale ∧
      MemH10 U w.toFun ∧
      w.toFun = zeroExtendedKuhnAffine (triadicSimplexPartition Q j) phi ∧
      (∀ T ∈ triadicSimplexPartition Q j, ∀ x ∈ T.openCarrier,
        w.grad x = kuhnSlope T phi) ∧
      (∀ i : Fin (n + 1),
        eLpNorm (fun x => w.grad x i - u.toH1Function.grad x i) 2
          (volume.restrict U) ≤ ENNReal.ofReal eps) := by
  classical
  have hUfin : volume U ≠ ⊤ := ne_of_lt hU.isBoundedDomain.volume_lt_top
  set M : ℝ≥0∞ := volume U ^ ((2 : ℝ≥0∞).toReal)⁻¹ with hM
  have hMtop : M ≠ ⊤ :=
    ne_of_lt (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hUfin)
  set Mr : ℝ := M.toReal with hMr
  have hMr0 : 0 ≤ Mr := ENNReal.toReal_nonneg
  set t : ℝ := (eps / 2) / (Mr + 1) with ht
  have htpos : 0 < t := by
    have : (0 : ℝ) < Mr + 1 := by linarith
    positivity
  have hMt : Mr * t ≤ eps / 2 := by
    rw [ht]
    rw [mul_div_assoc']
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < Mr + 1)]
    nlinarith [heps.le]
  -- a single smooth approximation good in every coordinate
  have hhalf : (0 : ℝ≥0∞) < ENNReal.ofReal (eps / 2) :=
    ENNReal.ofReal_pos.mpr (by linarith)
  have hev : ∀ᶠ m in Filter.atTop, ∀ i : Fin (n + 1),
      eLpNorm (fun x => fderiv ℝ (u.approx m) x (basisVec i) -
        u.toH1Function.grad x i) 2 (volume.restrict U) <
          ENNReal.ofReal (eps / 2) := by
    refine Filter.eventually_all.mpr fun i => ?_
    exact (u.tendsto_approx_grad i).eventually (gt_mem_nhds hhalf)
  obtain ⟨m, hm⟩ := hev.exists
  set phi : Vec (n + 1) → ℝ := u.approx m with hphi_def
  have hphi1 : ContDiff ℝ 1 phi := (u.approx_smooth m).of_le (by simp)
  have hphic : HasCompactSupport phi := u.approx_hasCompactSupport m
  have hphisub : tsupport phi ⊆ U := u.approx_support_subset m
  obtain ⟨j, w, Kw, hjQ, hwfun, hKwc, hKwU, hKwzero, hcell, haeb⟩ :=
    exists_kuhnAffine_h1_approx hU.isOpen hU.isBoundedDomain.isBounded hUQ hphi1
      hphic hphisub htpos
  refine ⟨j, phi, w, hjQ,
    memH10_of_compactSupport hU w hKwc hKwU hKwzero, hwfun, hcell, ?_⟩
  intro i
  -- the interpolation half
  have hphicont : Continuous (fun x => fderiv ℝ phi x (basisVec i)) :=
    ((u.approx_smooth m).continuous_fderiv (by simp)).clm_apply continuous_const
  have hA : eLpNorm (fun x => w.grad x i - fderiv ℝ phi x (basisVec i)) 2
      (volume.restrict U) ≤ ENNReal.ofReal (eps / 2) := by
    have hb : ∀ᵐ x ∂(volume.restrict U),
        ‖w.grad x i - fderiv ℝ phi x (basisVec i)‖ ≤ t := by
      filter_upwards [haeb i] with x hx
      simpa [Real.norm_eq_abs] using hx
    have hmeas : AEStronglyMeasurable
        (fun x => w.grad x i - fderiv ℝ phi x (basisVec i))
        (volume.restrict U) :=
      (w.gradMemL2 i).aestronglyMeasurable.sub hphicont.aestronglyMeasurable
    have hbound := MeasureTheory.eLpNorm_le_of_ae_bound (p := 2) hmeas hb
    rw [Measure.restrict_apply_univ] at hbound
    refine hbound.trans ?_
    have hMeq : M = ENNReal.ofReal Mr := (ENNReal.ofReal_toReal hMtop).symm
    calc
      volume U ^ ((2 : ℝ≥0∞).toReal)⁻¹ * ENNReal.ofReal t
          = ENNReal.ofReal Mr * ENNReal.ofReal t := by rw [← hM, hMeq]
      _ = ENNReal.ofReal (Mr * t) := (ENNReal.ofReal_mul hMr0).symm
      _ ≤ ENNReal.ofReal (eps / 2) := ENNReal.ofReal_le_ofReal hMt
  -- the smoothing half
  have hB : eLpNorm (fun x => u.toH1Function.grad x i -
      fderiv ℝ phi x (basisVec i)) 2 (volume.restrict U) ≤
        ENNReal.ofReal (eps / 2) := by
    have hneg : (fun x => u.toH1Function.grad x i - fderiv ℝ phi x (basisVec i)) =
        -(fun x => fderiv ℝ phi x (basisVec i) - u.toH1Function.grad x i) := by
      funext x
      simp
    rw [hneg, eLpNorm_neg]
    exact (hm i).le
  -- the triangle inequality
  have hmeasA : AEStronglyMeasurable
      (fun x => w.grad x i - fderiv ℝ phi x (basisVec i)) (volume.restrict U) :=
    (w.gradMemL2 i).aestronglyMeasurable.sub hphicont.aestronglyMeasurable
  have hmeasB : AEStronglyMeasurable
      (fun x => u.toH1Function.grad x i - fderiv ℝ phi x (basisVec i))
      (volume.restrict U) :=
    (u.toH1Function.gradMemL2 i).aestronglyMeasurable.sub hphicont.aestronglyMeasurable
  have hsplit : (fun x => w.grad x i - u.toH1Function.grad x i) =
      (fun x => w.grad x i - fderiv ℝ phi x (basisVec i)) -
        (fun x => u.toH1Function.grad x i - fderiv ℝ phi x (basisVec i)) := by
    funext x
    simp only [Pi.sub_apply]
    ring
  rw [hsplit]
  refine le_trans (eLpNorm_sub_le (by norm_num)) ?_
  calc
    eLpNorm (fun x => w.grad x i - fderiv ℝ phi x (basisVec i)) 2 (volume.restrict U) +
        eLpNorm (fun x => u.toH1Function.grad x i - fderiv ℝ phi x (basisVec i)) 2
          (volume.restrict U)
        ≤ ENNReal.ofReal (eps / 2) + ENNReal.ofReal (eps / 2) := add_le_add hA hB
    _ = ENNReal.ofReal eps := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
        norm_num

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
