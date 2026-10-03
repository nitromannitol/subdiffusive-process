module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryPhysicalResidualMean
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryGoodEventInverseRatio
public import Homogenization.Sobolev.FiniteLpCoordinate
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ReflectionParentApprox

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

variable {d : ℕ}

/-- The coordinate-summed raw `L²` norm is bounded by `d` times the Hilbert
realization.  This deliberately keeps the harmless dimension loss explicit. -/
theorem sum_toReal_eLpNorm_le_dimension_mul_hilbert
    {W : Set (Vec d)} {F : Vec d → Vec d}
    (hF : MemLp (fun x ↦ HilbertVec.ofVec (F x)) 2
      (volume.restrict W)) :
    ∑ i : Fin d, (eLpNorm (fun x ↦ F x i) 2
        (volume.restrict W)).toReal ≤
      (d : ℝ) * (eLpNorm (fun x ↦ HilbertVec.ofVec (F x)) 2
        (volume.restrict W)).toReal := by
  calc
    ∑ i : Fin d, (eLpNorm (fun x ↦ F x i) 2
          (volume.restrict W)).toReal ≤
        ∑ _i : Fin d, (eLpNorm (fun x ↦ HilbertVec.ofVec (F x)) 2
          (volume.restrict W)).toReal := by
      apply Finset.sum_le_sum
      intro i _
      exact ENNReal.toReal_mono hF.eLpNorm_ne_top
        (coordinate_eLpNorm_le_euclidean (volume.restrict W)
          FiniteLpExponent.two F i)
    _ = (d : ℝ) * (eLpNorm (fun x ↦ HilbertVec.ofVec (F x)) 2
          (volume.restrict W)).toReal := by
      simp [nsmul_eq_mul]

/-- A pointwise inverse-ratio cap converts the raw residual-gradient `L²`
square on a measurable window to the literal coefficient energy there. -/
theorem sigma_mul_toReal_eLpNorm_hilbert_grad_sq_le_coeffEnergy
    {W : Set (Vec d)} (hW : MeasurableSet W) {F : Vec d → Vec d}
    (hF : MemLp (fun x ↦ HilbertVec.ofVec (F x)) 2
      (volume.restrict W))
    {sigma B : ℝ} {a : Vec d → ℝ}
    (ha : ∀ x ∈ W, 0 < a x)
    (hratio : ∀ x ∈ W, sigma / a x ≤ B)
    (hplain : IntegrableOn (fun x ↦ vecNormSq (F x)) W)
    (henergy : IntegrableOn (fun x ↦ a x * vecNormSq (F x)) W) :
    sigma * (eLpNorm (fun x ↦ HilbertVec.ofVec (F x)) 2
        (volume.restrict W)).toReal ^ 2 ≤
      B * ∫ x in W, a x * vecNormSq (F x) ∂volume := by
  have hpoint : ∀ x ∈ W,
      sigma * vecNormSq (F x) ≤
        B * (a x * vecNormSq (F x)) := by
    intro x hx
    have hnorm : 0 ≤ vecNormSq (F x) := vecNormSq_nonneg _
    calc
      sigma * vecNormSq (F x) =
          (sigma / a x) * (a x * vecNormSq (F x)) := by
            field_simp [(ha x hx).ne']
      _ ≤ B * (a x * vecNormSq (F x)) :=
        mul_le_mul_of_nonneg_right (hratio x hx)
          (mul_nonneg (ha x hx).le hnorm)
  have hint :
      ∫ x in W, sigma * vecNormSq (F x) ∂volume ≤
        ∫ x in W, B * (a x * vecNormSq (F x)) ∂volume := by
    exact setIntegral_mono_on
      (hplain.const_mul sigma) (henergy.const_mul B)
      hW hpoint
  have hnormSq := toReal_eLpNorm_two_sq_eq_integral_norm_sq hF
  rw [integral_const_mul, integral_const_mul] at hint
  rw [hnormSq]
  have hnormPoint : ∀ x, ‖HilbertVec.ofVec (F x)‖ ^ 2 =
      vecNormSq (F x) := by
    intro x
    exact HilbertVec.norm_sq_ofVec (F x)
  simp_rw [hnormPoint]
  exact hint

/-- The physical residual window is contained in the good event's anchor
cube.  The deliberately generous four-scale gap keeps this geometry
independent of the ambient truncation face. -/
theorem boundaryResidualWindow_subset_anchorParent
    {m : ℤ} {n : ℕ} {z x q : Vec d}
    (hx : x ∈ truncatedCube d m ((n : ℤ) - 3) z)
    (hq : q ∈ truncatedCube d m ((n : ℤ) - 1) x) :
    translatedCube d ((n : ℤ) - 1) q ∩ cube d m ⊆
      translatedCube d ((n : ℤ) + 2) z := by
  intro p hp
  have hpq : p - q ∈ cube d ((n : ℤ) - 1) :=
    Section6ExcessDecay.mem_translatedCube_iff.mp hp.1
  have hqx : q - x ∈ cube d ((n : ℤ) - 1) :=
    Section6ExcessDecay.sub_mem_cube_of_mem_truncatedCube hq
  have hxz : x - z ∈ cube d ((n : ℤ) - 3) :=
    Section6ExcessDecay.sub_mem_cube_of_mem_truncatedCube hx
  rw [cube, mem_openCubeSet_originCube_iff] at hpq hqx hxz
  rw [Section6ExcessDecay.mem_translatedCube_iff, cube,
    mem_openCubeSet_originCube_iff]
  intro i
  have hbase : (0 : ℝ) < (3 : ℝ) ^ ((n : ℤ) - 3) :=
    zpow_pos (by norm_num) _
  have hsmall : (3 : ℝ) ^ ((n : ℤ) - 1) =
      9 * (3 : ℝ) ^ ((n : ℤ) - 3) := by
    rw [show (n : ℤ) - 1 = ((n : ℤ) - 3) + 2 by ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
    ring
  have hlarge : (3 : ℝ) ^ ((n : ℤ) + 2) =
      243 * (3 : ℝ) ^ ((n : ℤ) - 3) := by
    rw [show (n : ℤ) + 2 = ((n : ℤ) - 3) + 5 by ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
    ring
  have hid : p i - z i = (p i - q i) + (q i - x i) + (x i - z i) := by
    ring
  simp only [Pi.sub_apply] at hpq hqx hxz ⊢
  rw [hsmall] at hpq hqx
  rw [hid, hlarge]
  constructor <;>
    linarith only [(hpq i).1, (hpq i).2, (hqx i).1, (hqx i).2,
      (hxz i).1, (hxz i).2, hbase]

/-- The good event supplies the pointwise inverse-ratio premise needed by the
coefficient-energy insertion on every boundary residual window. -/
theorem tailAverage_div_aCutoff_le_on_boundaryResidualWindow
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m n : ℕ}
    (hnL : n + 2 ≤ L) {s : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (z x q : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hx : x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z)
    (hq : q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x)
    (hgood : omega ∈ goodEvent M none (n + 2) z 1 s)
    {p : Vec d}
    (hp : p ∈ translatedCube d ((n : ℤ) - 1) q ∩ cube d (m : ℤ)) :
    tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z) /
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p ≤
      1 + Section6Localization.subunitCollapseConstant d *
        Section6Localization.subunitEnvelope s (n + 2) *
          Section6Localization.subunitDeviation M (n + 2)
            (translatePotentialSample z omega) := by
  have hpAnchor : p ∈ translatedCube d ((n : ℤ) + 2) z :=
    boundaryResidualWindow_subset_anchorParent hx hq hp
  simpa only [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by norm_num] using!
    tailAverage_div_aCutoff_le_one_add_subunitEnvelope M hnL hsLower hsUpper
      omega z hgood hpAnchor

/-- The residual coefficient energy on an arbitrary measurable subwindow
splits into the physical solution and datum energies.  This is the exact
energy triangle needed after the scalar-mean reduction. -/
theorem setIntegral_aCutoff_residual_grad_le_two_solution_add_datum
    [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (m : ℤ)
    (u h : H1Function (openCubeSet (originCube d m)))
    (rho : H10Function (openCubeSet (originCube d m)))
    (hgrad : ∀ y, u.grad y = h.grad y + rho.grad y)
    {W : Set (Vec d)} (hW : MeasurableSet W)
    (hWsub : W ⊆ openCubeSet (originCube d m)) :
    ∫ y in W, SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y *
          vecNormSq (rho.grad y) ∂volume ≤
      2 * ∫ y in W, SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y *
          vecNormSq (u.grad y) ∂volume +
        2 * ∫ y in W, SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y *
          vecNormSq (h.grad y) ∂volume := by
  let a : Vec d → ℝ := SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega
  have hrhoInt : IntegrableOn (fun y ↦ a y * vecNormSq (rho.grad y)) W :=
    (integrableOn_aCutoff_energy M L omega (originCube d m)
      rho.toH1Function).mono_set hWsub
  have huInt : IntegrableOn (fun y ↦ a y * vecNormSq (u.grad y)) W :=
    (integrableOn_aCutoff_energy M L omega (originCube d m) u).mono_set hWsub
  have hhInt : IntegrableOn (fun y ↦ a y * vecNormSq (h.grad y)) W :=
    (integrableOn_aCutoff_energy M L omega (originCube d m) h).mono_set hWsub
  have hpoint : ∀ y ∈ W,
      a y * vecNormSq (rho.grad y) ≤
        2 * (a y * vecNormSq (u.grad y)) +
          2 * (a y * vecNormSq (h.grad y)) := by
    intro y _hy
    have hrho : rho.grad y = u.grad y - h.grad y := by
      rw [hgrad y]
      abel
    have hnorm := vecNormSq_sub_le (u.grad y) (h.grad y)
    have ha0 : 0 ≤ a y :=
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega y).le
    rw [hrho]
    calc
      a y * vecNormSq (u.grad y - h.grad y) ≤
          a y * (2 * (vecNormSq (u.grad y) + vecNormSq (h.grad y))) :=
        mul_le_mul_of_nonneg_left hnorm ha0
      _ = 2 * (a y * vecNormSq (u.grad y)) +
          2 * (a y * vecNormSq (h.grad y)) := by ring
  have hraw :
      ∫ y in W, a y * vecNormSq (rho.grad y) ∂volume ≤
        ∫ y in W, (2 * (a y * vecNormSq (u.grad y)) +
          2 * (a y * vecNormSq (h.grad y))) ∂volume := by
    exact setIntegral_mono_on hrhoInt
      ((huInt.const_mul 2).add (hhInt.const_mul 2)) hW hpoint
  rw [integral_add (huInt.const_mul 2) (hhInt.const_mul 2),
    integral_const_mul, integral_const_mul] at hraw
  simpa only [a] using! hraw

/-- The coefficient-dependent continuation of the physical residual-mean
reduction.  Once the inverse ratio is known, the sole remaining quantity is
the coefficient energy of the ambient zero-trace residual on the next
boundary window. -/
theorem physicalResidualMean_weighted_le_boundaryWindowCoeffEnergy
    [NeZero d]
    {m k : ℤ} {q : Vec d}
    (u h : H1Function (openCubeSet (originCube d m)))
    (rho : H10Function (openCubeSet (originCube d m)))
    (hval : ∀ x, u.toFun x = h.toFun x + rho.toH1Function.toFun x)
    (hkm : k ≤ m) (hq : q ∈ cube d m)
    (hnot : ¬ translatedCube d (k - 1) q ⊆ cube d m)
    {sigma B : ℝ} {a : Vec d → ℝ}
    (hsigma : 0 ≤ sigma)
    (ha : ∀ x ∈ translatedCube d (k + 1) q ∩ cube d m, 0 < a x)
    (hratio : ∀ x ∈ translatedCube d (k + 1) q ∩ cube d m,
      sigma / a x ≤ B)
    (henergy : IntegrableOn (fun x ↦ a x * vecNormSq (rho.grad x))
      (translatedCube d (k + 1) q ∩ cube d m)) :
    let c := Section6ExcessDecay.wellPlacedCentre q m k
    let P := translatedCube d k c
    let W := translatedCube d (k + 1) q ∩ cube d m
    sigma * Real.rpow (3 : ℝ) (-2 * (k : ℝ)) *
          volumeAverage P (fun x ↦ u.toFun x - h.toFun x) ^ 2 ≤
      Real.rpow (3 : ℝ) (-2 * (k : ℝ)) *
        (projectedBoundaryWindowPoincareConst d * (3 : ℝ) ^ k /
          Real.sqrt ((volume P).toReal)) ^ 2 *
        (d : ℝ) ^ 2 * B *
          ∫ x in W, a x * vecNormSq (rho.grad x) ∂volume := by
  classical
  dsimp only
  let W : Set (Vec d) := translatedCube d (k + 1) q ∩ cube d m
  have hWsub : W ⊆ openCubeSet (originCube d m) := by
    intro x hx
    exact hx.2
  have hWmeas : MeasurableSet W :=
    (Section6Schauder.isOpen_translatedCube d (k + 1) q).measurableSet.inter
      (isOpen_openCubeSet (originCube d m)).measurableSet
  have hgradW : MemVectorL2 W rho.grad :=
    rho.toH1Function.grad_memVectorL2.mono_measure
      (Measure.restrict_mono_set volume hWsub)
  have hvecW : MemLp (fun x ↦ HilbertVec.ofVec (rho.grad x)) 2
      (volume.restrict W) := by
    simpa only [MemVectorL2, volumeMeasureOn] using!
      memHilbertVectorL2_hilbertifyVecField hgradW
  have hplainW : IntegrableOn (fun x ↦ vecNormSq (rho.grad x)) W :=
    (integrableOn_vecNormSq_zeroTraceGrad rho).mono_set hWsub
  have hmean := physicalResidualMean_weighted_le_boundaryWindowGradient
    u h rho hval hkm hq hnot hsigma
  have hsum := sum_toReal_eLpNorm_le_dimension_mul_hilbert hvecW
  have hsum0 : 0 ≤ ∑ j : Fin d,
      (eLpNorm (fun x ↦ rho.grad x j) 2 (volume.restrict W)).toReal :=
    Finset.sum_nonneg fun _ _ ↦ ENNReal.toReal_nonneg
  have hsumSq :
      (∑ j : Fin d,
          (eLpNorm (fun x ↦ rho.grad x j) 2 (volume.restrict W)).toReal) ^ 2 ≤
        ((d : ℝ) *
          (eLpNorm (fun x ↦ HilbertVec.ofVec (rho.grad x)) 2
            (volume.restrict W)).toReal) ^ 2 := by
    exact pow_le_pow_left₀ hsum0 (by simpa [W] using! hsum) 2
  have hcoeff := sigma_mul_toReal_eLpNorm_hilbert_grad_sq_le_coeffEnergy
    hWmeas hvecW (by simpa [W] using! ha)
      (by simpa [W] using! hratio) hplainW (by simpa [W] using! henergy)
  let A : ℝ := Real.rpow (3 : ℝ) (-2 * (k : ℝ)) *
    (projectedBoundaryWindowPoincareConst d * (3 : ℝ) ^ k /
      Real.sqrt ((volume (translatedCube d k
        (Section6ExcessDecay.wellPlacedCentre q m k))).toReal)) ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let S : ℝ := ∑ j : Fin d,
    (eLpNorm (fun x ↦ rho.grad x j) 2 (volume.restrict W)).toReal
  let V : ℝ := (eLpNorm (fun x ↦ HilbertVec.ofVec (rho.grad x)) 2
    (volume.restrict W)).toReal
  let I : ℝ := ∫ x in W, a x * vecNormSq (rho.grad x) ∂volume
  have hsumSq' : S ^ 2 ≤ ((d : ℝ) * V) ^ 2 := by
    simpa only [S, V] using! hsumSq
  have hcoeff' : sigma * V ^ 2 ≤ B * I := by
    simpa only [V, I] using! hcoeff
  have hscaleNonneg : 0 ≤ A * (d : ℝ) ^ 2 :=
    mul_nonneg hA (sq_nonneg _)
  calc
    sigma * Real.rpow (3 : ℝ) (-2 * (k : ℝ)) *
          volumeAverage (translatedCube d k
            (Section6ExcessDecay.wellPlacedCentre q m k))
              (fun x ↦ u.toFun x - h.toFun x) ^ 2 ≤
        sigma * A * S ^ 2 := by
      have hmean' := hmean
      dsimp only [W] at hmean'
      dsimp only [A, S]
      calc
        sigma * Real.rpow (3 : ℝ) (-2 * (k : ℝ)) *
              volumeAverage (translatedCube d k
                (Section6ExcessDecay.wellPlacedCentre q m k))
                  (fun x ↦ u.toFun x - h.toFun x) ^ 2 ≤
            sigma * Real.rpow (3 : ℝ) (-2 * (k : ℝ)) *
              (projectedBoundaryWindowPoincareConst d * (3 : ℝ) ^ k /
                  Real.sqrt ((volume (translatedCube d k
                    (Section6ExcessDecay.wellPlacedCentre q m k))).toReal) *
                ∑ j : Fin d,
                  (eLpNorm (fun x ↦ rho.grad x j) 2
                    (volume.restrict (translatedCube d (k + 1) q ∩ cube d m))).toReal) ^ 2 :=
          hmean'
        _ = sigma *
              (Real.rpow (3 : ℝ) (-2 * (k : ℝ)) *
                (projectedBoundaryWindowPoincareConst d * (3 : ℝ) ^ k /
                  Real.sqrt ((volume (translatedCube d k
                    (Section6ExcessDecay.wellPlacedCentre q m k))).toReal)) ^ 2) *
              (∑ j : Fin d,
                (eLpNorm (fun x ↦ rho.grad x j) 2
                  (volume.restrict (translatedCube d (k + 1) q ∩ cube d m))).toReal) ^ 2 := by
          ring
    _ ≤ sigma * A * ((d : ℝ) * V) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hsumSq' (mul_nonneg hsigma hA)
    _ = (A * (d : ℝ) ^ 2) * (sigma * V ^ 2) := by ring
    _ ≤ (A * (d : ℝ) ^ 2) * (B * I) :=
      mul_le_mul_of_nonneg_left hcoeff' hscaleNonneg
    _ = Real.rpow (3 : ℝ) (-2 * (k : ℝ)) *
        (projectedBoundaryWindowPoincareConst d * (3 : ℝ) ^ k /
          Real.sqrt ((volume (translatedCube d k
            (Section6ExcessDecay.wellPlacedCentre q m k))).toReal)) ^ 2 *
        (d : ℝ) ^ 2 * B *
          ∫ x in translatedCube d (k + 1) q ∩ cube d m,
            a x * vecNormSq (rho.grad x) ∂volume := by
      simp only [A, I, W]
      ring

/-- Model-facing form of the coefficient-energy insertion.  The good event
discharges the pointwise inverse-ratio premise on the literal boundary
window; the remaining right side is the residual coefficient energy that the
printed boundary Caccioppoli/hole-filling step must price. -/
theorem physicalResidualMean_weighted_le_boundaryWindowCoeffEnergy_of_goodEvent
    [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (sOrder : FractionalOrder)
    (hs : sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
    (L m n : ℕ) (hmL : m ≤ L) (hnm : n + 5 ≤ m)
    (z x q : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hx : x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z)
    (hq : q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x)
    (hnot : ¬ translatedCube d ((n : ℤ) - 3) q ⊆ cube d (m : ℤ))
    (hgood : omega ∈ goodEvent M none (n + 2) z 1 (sOrder.1 / 8))
    (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
    (rho : H10Function (openCubeSet (originCube d (m : ℤ))))
    (hval : ∀ y, u.toFun y = h.toFun y + rho.toH1Function.toFun y)
    (henergy : IntegrableOn (fun y ↦
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y * vecNormSq (rho.grad y))
      (translatedCube d ((n : ℤ) - 1) q ∩ cube d (m : ℤ))) :
    let k : ℤ := (n : ℤ) - 2
    let c := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
    let P := translatedCube d k c
    let W := translatedCube d (k + 1) q ∩ cube d (m : ℤ)
    let sigma := tailAverage M L (n + 2) omega
      (translatedCube d ((n : ℤ) + 2) z)
    let B := 1 + Section6Localization.subunitCollapseConstant d *
      Section6Localization.subunitEnvelope (sOrder.1 / 8) (n + 2) *
        Section6Localization.subunitDeviation M (n + 2)
          (translatePotentialSample z omega)
    sigma * Real.rpow (3 : ℝ) (-2 * (k : ℝ)) *
          volumeAverage P (fun y ↦ u.toFun y - h.toFun y) ^ 2 ≤
      Real.rpow (3 : ℝ) (-2 * (k : ℝ)) *
        (projectedBoundaryWindowPoincareConst d * (3 : ℝ) ^ k /
          Real.sqrt ((volume P).toReal)) ^ 2 *
        (d : ℝ) ^ 2 * B *
          ∫ y in W, SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y *
            vecNormSq (rho.grad y) ∂volume := by
  dsimp only
  let sigma : ℝ := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  let B : ℝ := 1 + Section6Localization.subunitCollapseConstant d *
    Section6Localization.subunitEnvelope (sOrder.1 / 8) (n + 2) *
      Section6Localization.subunitDeviation M (n + 2)
        (translatePotentialSample z omega)
  have hnL : n + 2 ≤ L := by omega
  have hkm : (n : ℤ) - 2 ≤ (m : ℤ) := by omega
  have hqDomain : q ∈ cube d (m : ℤ) :=
    Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ)
      ((n : ℤ) - 1) x hq
  have hsigma : 0 ≤ sigma := by
    dsimp only [sigma]
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact (tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)).le
  have hnot' : ¬ translatedCube d ((n : ℤ) - 2 - 1) q ⊆
      cube d (m : ℤ) := by
    simpa only [show (n : ℤ) - 2 - 1 = (n : ℤ) - 3 by ring] using! hnot
  have hratio : ∀ y ∈
      translatedCube d ((n : ℤ) - 1) q ∩ cube d (m : ℤ),
      sigma / SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y ≤ B := by
    intro y hy
    exact tailAverage_div_aCutoff_le_on_boundaryResidualWindow M hnL
      (by linarith only [hs.1]) (by linarith only [hs.2]) z x q omega
      hx hq hgood hy
  have hmain := physicalResidualMean_weighted_le_boundaryWindowCoeffEnergy
    (B := B) u h rho hval hkm hqDomain hnot' hsigma
    (fun y _ ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega y)
    (by
      simpa only [show (n : ℤ) - 2 + 1 = (n : ℤ) - 1 by ring] using! hratio)
    (by
      simpa only [show (n : ℤ) - 2 + 1 = (n : ℤ) - 1 by ring] using! henergy)
  simpa only [sigma, B,
    show (n : ℤ) - 2 + 1 = (n : ℤ) - 1 by ring] using! hmain



theorem physicalResidualMean_weighted_le_boundaryWindowSolutionDatumEnergy_of_goodEvent
    [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (sOrder : FractionalOrder)
    (hs : sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
    (L m n : ℕ) (hmL : m ≤ L) (hnm : n + 5 ≤ m)
    (z x q : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hx : x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z)
    (hq : q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x)
    (hnot : ¬ translatedCube d ((n : ℤ) - 3) q ⊆ cube d (m : ℤ))
    (hgood : omega ∈ goodEvent M none (n + 2) z 1 (sOrder.1 / 8))
    (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
    (rho : H10Function (openCubeSet (originCube d (m : ℤ))))
    (hval : ∀ y, u.toFun y = h.toFun y + rho.toH1Function.toFun y)
    (hgrad : ∀ y, u.grad y = h.grad y + rho.grad y) :
    let k : ℤ := (n : ℤ) - 2
    let c := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
    let P := translatedCube d k c
    let W := translatedCube d (k + 1) q ∩ cube d (m : ℤ)
    let sigma := tailAverage M L (n + 2) omega
      (translatedCube d ((n : ℤ) + 2) z)
    let B := 1 + Section6Localization.subunitCollapseConstant d *
      Section6Localization.subunitEnvelope (sOrder.1 / 8) (n + 2) *
        Section6Localization.subunitDeviation M (n + 2)
          (translatePotentialSample z omega)
    sigma * Real.rpow (3 : ℝ) (-2 * (k : ℝ)) *
          volumeAverage P (fun y ↦ u.toFun y - h.toFun y) ^ 2 ≤
      Real.rpow (3 : ℝ) (-2 * (k : ℝ)) *
        (projectedBoundaryWindowPoincareConst d * (3 : ℝ) ^ k /
          Real.sqrt ((volume P).toReal)) ^ 2 *
        (d : ℝ) ^ 2 * B *
          (2 * ∫ y in W, SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y *
              vecNormSq (u.grad y) ∂volume +
            2 * ∫ y in W, SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y *
              vecNormSq (h.grad y) ∂volume) := by
  dsimp only
  rw [show (n : ℤ) - 2 + 1 = (n : ℤ) - 1 by ring]
  let W : Set (Vec d) :=
    translatedCube d ((n : ℤ) - 1) q ∩ cube d (m : ℤ)
  have hWsub : W ⊆ openCubeSet (originCube d (m : ℤ)) := fun _ hy ↦ hy.2
  have hWmeas : MeasurableSet W :=
    (Section6Schauder.isOpen_translatedCube d ((n : ℤ) - 1) q).measurableSet.inter
      (isOpen_openCubeSet (originCube d (m : ℤ))).measurableSet
  have henergy : IntegrableOn (fun y ↦
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y * vecNormSq (rho.grad y)) W :=
    (integrableOn_aCutoff_energy M L omega (originCube d (m : ℤ))
      rho.toH1Function).mono_set hWsub
  have hmean :=
    physicalResidualMean_weighted_le_boundaryWindowCoeffEnergy_of_goodEvent
      M sOrder hs L m n hmL hnm z x q omega hx hq hnot hgood
      u h rho hval (by simpa only [W] using! henergy)
  have hsplit := setIntegral_aCutoff_residual_grad_le_two_solution_add_datum
    M L omega (m : ℤ) u h rho hgrad hWmeas hWsub
  let B : ℝ := 1 + Section6Localization.subunitCollapseConstant d *
    Section6Localization.subunitEnvelope (sOrder.1 / 8) (n + 2) *
      Section6Localization.subunitDeviation M (n + 2)
        (translatePotentialSample z omega)
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact add_nonneg zero_le_one <| mul_nonneg
      (mul_nonneg (Section6Localization.subunitCollapseConstant_pos d).le
        (Section6Localization.subunitEnvelope_pos (sOrder.1 / 8) (n + 2)).le)
      (subunitDeviation_nonneg M (n + 2) (translatePotentialSample z omega))
  let A : ℝ := Real.rpow (3 : ℝ) (-2 * ((((n : ℤ) - 2 : ℤ) : ℝ))) *
    (projectedBoundaryWindowPoincareConst d * (3 : ℝ) ^ ((n : ℤ) - 2) /
      Real.sqrt ((volume (translatedCube d ((n : ℤ) - 2)
        (Section6ExcessDecay.wellPlacedCentre q (m : ℤ)
          ((n : ℤ) - 2)))).toReal)) ^ 2 * (d : ℝ) ^ 2 * B
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
          (sq_nonneg _))
        (sq_nonneg _))
      hB
  have hsplitScaled := mul_le_mul_of_nonneg_left hsplit hA
  have hmean' := hmean
  dsimp only at hmean'
  rw [show (n : ℤ) - 2 + 1 = (n : ℤ) - 1 by ring] at hmean'
  dsimp only [W] at hsplitScaled
  dsimp only [B, A, W] at hmean' hsplitScaled ⊢
  exact hmean'.trans (by simpa only [mul_assoc] using! hsplitScaled)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
