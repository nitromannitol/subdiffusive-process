import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryAffineCoarsePrice
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryAdaptiveGoodEventPrices

/-!
# Affine/residual boundary decomposition

The boundary radius iteration must see only the non-affine part of the datum.
We subtract the canonical zero-force affine Dirichlet lift from the solution
itself.  The residual therefore has the same forcing and the residual datum,
while the zero-trace relation is preserved exactly.  The affine energy is
kept as a single external coarse-matrix price.

PROVENANCE: mirrors the solution-level affine split in
`Algsuperdiff/Section4/Provider/ExcessDecay/AffineSplitHarmonic.lean` and
`BoundaryOuterAssembly.lean`.  Here the lift is the canonical symmetric
Dirichlet minimizer constructed in `BoundaryAffineCoarsePrice.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
private theorem matVecMul_sub_right' (A : Mat d) (x y : Vec d) :
    matVecMul A (x - y) = matVecMul A x - matVecMul A y := by
  rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg, sub_eq_add_neg]

omit [NeZero d] in
/-- Subtracting a zero-force solution preserves the forcing. -/
theorem isForcedEquation_sub_zero
    {Q : TriadicCube d} {A : CoeffFamily d} {g : Vec d → Vec d}
    {u v : H1Function (openCubeSet Q)}
    (hu : IsForcedEquation Q A u g)
    (hv : IsForcedEquation Q A v (fun _ ↦ 0)) :
    IsForcedEquation Q A (u - v) g := by
  intro phi
  have hfluxu := integrableOn_flux_pairing Q A u phi
  have hfluxv := integrableOn_flux_pairing Q A v phi
  have hpoint : ∀ x,
      vecDot (matVecMul ((A.coeffOn Q).toCoeffField x) ((u - v).grad x))
          (phi.toH1Function.grad x) =
        vecDot (matVecMul ((A.coeffOn Q).toCoeffField x) (u.grad x))
            (phi.toH1Function.grad x) -
          vecDot (matVecMul ((A.coeffOn Q).toCoeffField x) (v.grad x))
            (phi.toH1Function.grad x) := by
    intro x
    rw [H1Function.sub_grad]
    show vecDot
        (matVecMul ((A.coeffOn Q).toCoeffField x) (u.grad x - v.grad x)) _ = _
    rw [matVecMul_sub_right']
    simp only [vecDot, Pi.sub_apply]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  calc
    ∫ x in openCubeSet Q,
        vecDot (matVecMul ((A.coeffOn Q).toCoeffField x) ((u - v).grad x))
          (phi.toH1Function.grad x) ∂volume =
      ∫ x in openCubeSet Q,
        (vecDot (matVecMul ((A.coeffOn Q).toCoeffField x) (u.grad x))
            (phi.toH1Function.grad x) -
          vecDot (matVecMul ((A.coeffOn Q).toCoeffField x) (v.grad x))
            (phi.toH1Function.grad x)) ∂volume :=
        integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = (∫ x in openCubeSet Q,
          vecDot (matVecMul ((A.coeffOn Q).toCoeffField x) (u.grad x))
            (phi.toH1Function.grad x) ∂volume) -
        ∫ x in openCubeSet Q,
          vecDot (matVecMul ((A.coeffOn Q).toCoeffField x) (v.grad x))
            (phi.toH1Function.grad x) ∂volume :=
      integral_sub hfluxu hfluxv
    _ = ∫ x in openCubeSet Q,
        vecDot (g x) (phi.toH1Function.grad x) ∂volume := by
      have hu' := hu phi
      have hv' := hv phi
      simp only [Ch02.cubeDomain_coe] at hu' hv'
      rw [hu', hv']
      simp [vecDot]

omit [NeZero d] in
/-- Weak equations depend only on the a.e. gradient representative. -/
theorem isForcedEquation_congr_grad_ae
    {Q : TriadicCube d} {A : CoeffFamily d} {g : Vec d → Vec d}
    {u v : H1Function (openCubeSet Q)}
    (hu : IsForcedEquation Q A u g)
    (hgrad : v.grad =ᵐ[volume.restrict (openCubeSet Q)] u.grad) :
    IsForcedEquation Q A v g := by
  intro phi
  calc
    ∫ x in openCubeSet Q,
        vecDot (matVecMul ((A.coeffOn Q).toCoeffField x) (v.grad x))
          (phi.toH1Function.grad x) ∂volume =
      ∫ x in openCubeSet Q,
        vecDot (matVecMul ((A.coeffOn Q).toCoeffField x) (u.grad x))
          (phi.toH1Function.grad x) ∂volume := by
        apply integral_congr_ae
        filter_upwards [hgrad] with x hx
        rw [hx]
    _ = _ := hu phi

/-- Replace a Dirichlet solution by the pointwise representative
`ell + w`, where `w` is its chosen zero-trace representative.  This exposes
the exact pointwise trace identity needed by localized Caccioppoli. -/
theorem exists_pointwiseAffineDirichletRepresentative
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q : TriadicCube d) {t K sigma : ℝ}
    (ht : 0 < t) (hsigma : 0 < sigma)
    (hcap : sigma⁻¹ * Ch02.LambdaSq Q t (.finite 2)
      (aCutoffFamily M L omega) ≤ K) (p : Vec d) :
    let ell : H1Function (openCubeSet Q) :=
      H1Function.affineOnIsSobolevRegularDomain
        (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain p
    ∃ v : H1Function (openCubeSet Q),
      IsForcedEquation Q (aCutoffFamily M L omega) v (fun _ ↦ 0) ∧
      LocalizedZeroTraceFunctionOn (openCubeSet Q) (Set.univ : Set (Vec d))
        (fun x ↦ v.toFun x - ell.toFun x) ∧
      localizedCoeffEnergyValue (openCubeSet Q)
          ((aCutoffFamily M L omega).coeffOn Q) v ≤
        K * sigma * vecNormSq p := by
  dsimp only
  let ell : H1Function (openCubeSet Q) :=
    H1Function.affineOnIsSobolevRegularDomain
      (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain p
  obtain ⟨v0, hv0datum, hv0energy⟩ :=
    exists_aCutoffAffineDirichletLift_energy_le_normalizedCap
      M L omega Q ht hsigma hcap p
  let w : H10Function (openCubeSet Q) := v0.zeroTraceDifferenceH10
  let v : H1Function (openCubeSet Q) := ell + w.toH1Function
  have hwVal : w.toH1Function.toFun
      =ᵐ[volume.restrict (openCubeSet Q)]
        fun x ↦ v0.toH1.toFun x - ell.toFun x := by
    simpa only [w, hv0datum] using
      v0.zeroTraceDifferenceH10_toFun_ae_eq
  have hvVal : v.toFun =ᵐ[volume.restrict (openCubeSet Q)] v0.toH1.toFun := by
    filter_upwards [hwVal] with x hx
    simp only [v, H1Function.add_toFun, hx]
    ring
  have hvGrad : v.grad =ᵐ[volume.restrict (openCubeSet Q)] v0.toH1.grad :=
    H1Function.grad_ae_eq_of_toFun_ae_eq (isOpen_openCubeSet Q) hvVal
  have hvEq : IsForcedEquation Q (aCutoffFamily M L omega) v (fun _ ↦ 0) :=
    isForcedEquation_congr_grad_ae v0.weakSolution hvGrad
  have hvTrace : LocalizedZeroTraceFunctionOn (openCubeSet Q)
      (Set.univ : Set (Vec d)) (fun x ↦ v.toFun x - ell.toFun x) := by
    have hwTrace : LocalizedZeroTraceFunctionOn (openCubeSet Q)
        (Set.univ : Set (Vec d)) w.toH1Function.toFun :=
      localizedZeroTraceFunctionOn_of_h10_any w
    exact Section6SchauderDatum.localizedZeroTraceFunctionOn_congr
      (fun x ↦ by simp [v]) hwTrace
  have hvEnergy : localizedCoeffEnergyValue (openCubeSet Q)
      ((aCutoffFamily M L omega).coeffOn Q) v =
      localizedCoeffEnergyValue (openCubeSet Q)
        ((aCutoffFamily M L omega).coeffOn Q) v0.toH1 := by
    unfold localizedCoeffEnergyValue
    apply volumeAverage_eq_of_ae_eq
    filter_upwards [hvGrad] with x hx
    rw [hx]
  refine ⟨v, hvEq, hvTrace, ?_⟩
  rw [hvEnergy]
  exact hv0energy

/-- Subtract the canonical affine harmonic representative from both the
solution and its datum.  The residual carries the original force, while its
datum gradient is exactly the fluctuation around `p`. -/
theorem exists_affineResidualSolution
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q : TriadicCube d) {V : Set (Vec d)}
    {g : Vec d → Vec d} (u h : H1Function (openCubeSet Q))
    (hu : IsForcedEquation Q (aCutoffFamily M L omega) u g)
    (htrace : LocalizedZeroTraceFunctionOn (openCubeSet Q) V
      (fun x ↦ u.toFun x - h.toFun x))
    {t K sigma : ℝ} (ht : 0 < t) (hsigma : 0 < sigma)
    (hcap : sigma⁻¹ * Ch02.LambdaSq Q t (.finite 2)
      (aCutoffFamily M L omega) ≤ K) (p : Vec d) :
    let ell : H1Function (openCubeSet Q) :=
      H1Function.affineOnIsSobolevRegularDomain
        (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain p
    ∃ v uRes hRes : H1Function (openCubeSet Q),
      IsForcedEquation Q (aCutoffFamily M L omega) v (fun _ ↦ 0) ∧
      localizedCoeffEnergyValue (openCubeSet Q)
          ((aCutoffFamily M L omega).coeffOn Q) v ≤
        K * sigma * vecNormSq p ∧
      uRes = u - v ∧ hRes = h - ell ∧
      IsForcedEquation Q (aCutoffFamily M L omega) uRes g ∧
      LocalizedZeroTraceFunctionOn (openCubeSet Q) V
        (fun x ↦ uRes.toFun x - hRes.toFun x) ∧
      (∀ x, hRes.grad x = h.grad x - p) ∧
      (∀ x, u.grad x = uRes.grad x + v.grad x) := by
  dsimp only
  let ell : H1Function (openCubeSet Q) :=
    H1Function.affineOnIsSobolevRegularDomain
      (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain p
  obtain ⟨v, hvEq, hvTraceUniv, hvEnergy⟩ :=
    exists_pointwiseAffineDirichletRepresentative M L omega Q ht hsigma hcap p
  let uRes : H1Function (openCubeSet Q) := u - v
  let hRes : H1Function (openCubeSet Q) := h - ell
  have hvTrace : LocalizedZeroTraceFunctionOn (openCubeSet Q) V
      (fun x ↦ v.toFun x - ell.toFun x) := by
    intro eta heta hetaCompact hetaV
    exact hvTraceUniv eta heta hetaCompact (fun x _ ↦ Set.mem_univ x)
  have hresTraceRaw :=
    Homogenization.localizedZeroTraceFunctionOn_sub htrace hvTrace
  have hresTrace : LocalizedZeroTraceFunctionOn (openCubeSet Q) V
      (fun x ↦ uRes.toFun x - hRes.toFun x) := by
    exact Section6SchauderDatum.localizedZeroTraceFunctionOn_congr
      (fun x ↦ by simp [uRes, hRes]; ring) hresTraceRaw
  have huRes : IsForcedEquation Q (aCutoffFamily M L omega) uRes g := by
    simpa only [uRes] using isForcedEquation_sub_zero hu hvEq
  refine ⟨v, uRes, hRes, hvEq, hvEnergy, rfl, rfl, huRes, hresTrace, ?_, ?_⟩
  · intro x
    simp [hRes, ell, H1Function.affineOnIsSobolevRegularDomain_grad]
  · intro x
    simp [uRes]

/-- Subtract the affine harmonic lift from both the solution and its comparison
datum.  Unlike the affine-function residual, this version preserves the
active-cell difference `u-h` pointwise; it is the form consumed by the
affine-external radius recurrence. -/
theorem exists_affineExternalComparison
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q : TriadicCube d) {V : Set (Vec d)}
    {g : Vec d → Vec d} (u h : H1Function (openCubeSet Q))
    (hu : IsForcedEquation Q (aCutoffFamily M L omega) u g)
    (htrace : LocalizedZeroTraceFunctionOn (openCubeSet Q) V
      (fun x ↦ u.toFun x - h.toFun x))
    {t K sigma : ℝ} (ht : 0 < t) (hsigma : 0 < sigma)
    (hcap : sigma⁻¹ * Ch02.LambdaSq Q t (.finite 2)
      (aCutoffFamily M L omega) ≤ K) (p : Vec d) :
    ∃ v uRes hComp : H1Function (openCubeSet Q),
      IsForcedEquation Q (aCutoffFamily M L omega) v (fun _ ↦ 0) ∧
      localizedCoeffEnergyValue (openCubeSet Q)
          ((aCutoffFamily M L omega).coeffOn Q) v ≤
        K * sigma * vecNormSq p ∧
      uRes = u - v ∧ hComp = h - v ∧
      IsForcedEquation Q (aCutoffFamily M L omega) uRes g ∧
      LocalizedZeroTraceFunctionOn (openCubeSet Q) V
        (fun x ↦ uRes.toFun x - hComp.toFun x) ∧
      (∀ x, uRes.toFun x - hComp.toFun x = u.toFun x - h.toFun x) ∧
      (∀ x, u.grad x = uRes.grad x + v.grad x) := by
  obtain ⟨v, hvEq, _hvTrace, hvEnergy⟩ :=
    exists_pointwiseAffineDirichletRepresentative M L omega Q ht hsigma hcap p
  let uRes : H1Function (openCubeSet Q) := u - v
  let hComp : H1Function (openCubeSet Q) := h - v
  have huRes : IsForcedEquation Q (aCutoffFamily M L omega) uRes g := by
    simpa only [uRes] using isForcedEquation_sub_zero hu hvEq
  have hpoint : ∀ x,
      uRes.toFun x - hComp.toFun x = u.toFun x - h.toFun x := by
    intro x
    simp only [uRes, hComp, H1Function.sub_toFun]
    ring
  have hresTrace : LocalizedZeroTraceFunctionOn (openCubeSet Q) V
      (fun x ↦ uRes.toFun x - hComp.toFun x) :=
    Section6SchauderDatum.localizedZeroTraceFunctionOn_congr
      (fun x ↦ (hpoint x).symm) htrace
  refine ⟨v, uRes, hComp, hvEq, hvEnergy, rfl, rfl, huRes,
    hresTrace, hpoint, ?_⟩
  intro x
  simp [uRes]

/-- The local energy profile of a solution is the residual profile plus one
external full-cube affine energy. -/
theorem boundaryCrossScaleEnergyProfile_aCutoff_le_residual_add_affine
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q R : TriadicCube d) (center : Vec d) (rho : ℝ)
    (u uRes v : H1Function (openCubeSet Q))
    (hgrad : ∀ x, u.grad x = uRes.grad x + v.grad x) :
    boundaryCrossScaleEnergyProfile Q R center rho (fun x ↦
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)) ≤
      2 * boundaryCrossScaleEnergyProfile Q R center rho (fun x ↦
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (uRes.grad x)) +
      2 * localizedCoeffEnergyValue (openCubeSet Q)
        ((aCutoffFamily M L omega).coeffOn Q) v := by
  let patch := coarseCaccioppoliLocalClosedCube R center rho
  let eu : Vec d → ℝ := fun x ↦
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)
  let er : Vec d → ℝ := fun x ↦
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (uRes.grad x)
  let ev : Vec d → ℝ := fun x ↦
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (v.grad x)
  have heu : IntegrableOn eu (openCubeSet Q) := by
    simpa only [eu] using integrableOn_aCutoff_energy M L omega Q u
  have her : IntegrableOn er (openCubeSet Q) := by
    simpa only [er] using integrableOn_aCutoff_energy M L omega Q uRes
  have hev : IntegrableOn ev (openCubeSet Q) := by
    simpa only [ev] using integrableOn_aCutoff_energy M L omega Q v
  have hpoint : ∀ x ∈ openCubeSet Q,
      patch.indicator eu x ≤ 2 * patch.indicator er x + 2 * ev x := by
    intro x hx
    by_cases hxl : x ∈ patch
    · simp only [Set.indicator_of_mem hxl, eu, er, ev]
      have hsq := vecNormSq_add_le (uRes.grad x) (v.grad x)
      rw [hgrad x]
      have hm := mul_le_mul_of_nonneg_left hsq
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).le
      nlinarith only [hm]
    · simp only [Set.indicator_of_notMem hxl, mul_zero, zero_add]
      exact mul_nonneg (by norm_num)
        (mul_nonneg (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).le
          (vecNormSq_nonneg _))
  have hmono : volumeAverage (openCubeSet Q) (patch.indicator eu) ≤
      volumeAverage (openCubeSet Q) (fun x ↦
        2 * patch.indicator er x + 2 * ev x) := by
    apply volumeAverage_le_volumeAverage_of_le_on (measurableSet_openCubeSet Q)
    · exact heu.indicator
        (measurableSet_coarseCaccioppoliLocalClosedCube R center rho)
    · exact (her.indicator
          (measurableSet_coarseCaccioppoliLocalClosedCube R center rho)).const_mul 2
        |>.add (hev.const_mul 2)
    · exact hpoint
  have hsplit : volumeAverage (openCubeSet Q) (fun x ↦
      2 * patch.indicator er x + 2 * ev x) =
      2 * volumeAverage (openCubeSet Q) (patch.indicator er) +
        2 * volumeAverage (openCubeSet Q) ev := by
    unfold volumeAverage
    rw [integral_add, integral_const_mul, integral_const_mul]
    · ring
    · exact (her.indicator
        (measurableSet_coarseCaccioppoliLocalClosedCube R center rho)).const_mul 2
    · exact hev.const_mul 2
  have hevEq : volumeAverage (openCubeSet Q) ev =
      localizedCoeffEnergyValue (openCubeSet Q)
        ((aCutoffFamily M L omega).coeffOn Q) v := by
    rw [localizedCoeffEnergyValue_eq_volumeAverage_publicCoeffField_of_subset_openCubeSet
      (Set.Subset.rfl) v]
    apply volumeAverage_eq_of_ae_eq
    filter_upwards
        [publicCoeffField_ae_eq_openCubeSet Q (aCutoffFamily M L omega)] with x hx
    simp only [ev, coefficientEnergyDensity, hx]
    simp [aCutoffFamily, aCutoffTriadicData,
      ScalarTriadicCoeffData.toTriadicCoeffFamily, aCutoffCoeffOnData,
      ScalarCoeffOnData.toCoeffOn, scalarCoeffField,
      Ch02.symmPart_scalarMatrix, matVecMul_scalarMatrix,
      vecDot_smul_right, vecNormSq]
  unfold boundaryCrossScaleEnergyProfile
  dsimp only [patch, eu, er] at hmono hsplit
  rw [hsplit, hevEq] at hmono
  exact hmono

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
