import SubdiffusiveProcess.Geometry.Cube
import SubdiffusiveProcess.Sobolev.PotentialResponses
import SubdiffusiveProcess.Sobolev.GradientRange
import SubdiffusiveProcess.Main.CutoffPotential
import SubdiffusiveProcess.Lane2.CellDirichlet
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace Filter SubdiffusiveProcess
open scoped ENNReal NNReal ContDiff

namespace Paper

private theorem aux_expPotentialCoefficient_sub_const
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
    (g : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d)))) (c : ℝ) :
    expPotentialCoefficient
        (g - Lp.const ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))) c) =
      scalePositiveCoefficient (Real.exp (-c)) (Real.exp_pos (-c))
        (expPotentialCoefficient g) := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [
    expPotentialCoefficient_coeFn
      (g - Lp.const ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))) c),
    expPotentialCoefficient_coeFn g,
    scalePositiveCoefficient_coeFn (Real.exp (-c)) (Real.exp_pos (-c))
      (expPotentialCoefficient g),
    Lp.coeFn_sub g (Lp.const ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))) c),
    Lp.coeFn_const ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))) c] with
      x hsub hg hscale hgc hconst
  rw [hsub, hscale, hg, hgc]
  simp only [Pi.sub_apply, hconst, Function.const_apply]
  rw [Real.exp_sub]
  calc
    Real.exp (g x) / Real.exp c = Real.exp (g x) * Real.exp (-c) := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
    _ = Real.exp (-c) * Real.exp (g x) := mul_comm _ _

private theorem aux_volumeLoad_comp_ne_zero
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Ω,
      ‖(u : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) u‖)
    (f : SpatialCoordinates d → ℝ) (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f)
    (hfsupp : tsupport f ⊆ (Ω : Set (SpatialCoordinates d)))
    (hf0 : ∃ x ∈ (Ω : Set (SpatialCoordinates d)), f x ≠ 0)
    (fL2 : DomainL2 Ω)
    (hfL2 : (fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] f) :
    (sobolevVolumeLoad fL2).comp (killedResponseSpace hP).space.subtypeL ≠ 0 := by
  have hfL2_ne : fL2 ≠ 0 := by
    intro hfL2_zero
    have hf_ae : f =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] 0 := by
      filter_upwards [hfL2, Lp.coeFn_zero ℝ 2
        (volume.restrict (Ω : Set (SpatialCoordinates d)))] with x hfx hx
      rw [← hfx, hfL2_zero, hx]
    obtain ⟨x, hxΩ, hfx⟩ := hf0
    have hcont : Continuous (fun y => f y ^ 2) := hf.continuous.pow 2
    have hcomp : HasCompactSupport (fun y => f y ^ 2) := by
      simpa only [pow_two] using hfc.mul_right
    have hint : Integrable (fun y => f y ^ 2) volume :=
      hcont.integrable_of_hasCompactSupport hcomp
    have hpos_support : 0 < volume
        (Function.support (fun y => f y ^ 2) ∩ (Ω : Set (SpatialCoordinates d))) := by
      apply IsOpen.measure_pos volume (hcont.isOpen_support.inter Ω.isOpen)
      refine ⟨x, ?_, hxΩ⟩
      exact pow_ne_zero 2 hfx
    have hpos : 0 < ∫ y in (Ω : Set (SpatialCoordinates d)), f y ^ 2 := by
      apply (setIntegral_pos_iff_support_of_nonneg_ae
        (μ := volume) (s := (Ω : Set (SpatialCoordinates d)))
        (f := fun y => f y ^ 2) (Filter.Eventually.of_forall (fun y => sq_nonneg (f y)))
        hint.integrableOn).2
      exact hpos_support
    have hzero : ∫ y in (Ω : Set (SpatialCoordinates d)), f y ^ 2 = 0 := by
      change (∫ y, f y ^ 2 ∂volume.restrict (Ω : Set (SpatialCoordinates d))) = 0
      apply integral_eq_zero_of_ae
      filter_upwards [hf_ae] with y hy
      simp [hy]
    exact (ne_of_gt hpos) hzero
  intro hL
  let ψ : TestFunction Ω ℝ ⊤ :=
    { toFun := f, contDiff' := hf, hasCompactSupport' := hfc, tsupport_subset' := hfsupp }
  let w : (killedResponseSpace hP).space :=
    ⟨smoothSobolevData ψ, smoothSobolevData_mem_killed ψ⟩
  have hwzero : sobolevVolumeLoad fL2 (w : SobolevData Ω) = 0 := by
    have h := congrArg (fun L : (killedResponseSpace hP).space →L[ℝ] ℝ => L w) hL
    simpa only [ContinuousLinearMap.zero_apply, ContinuousLinearMap.comp_apply] using h
  have hweq : (w : SobolevData Ω).1 = fL2 := by
    apply Lp.ext
    filter_upwards [testL2_coeFn ψ, hfL2,
      Lp.coeFn_zero ℝ 2 (volume.restrict (Ω : Set (SpatialCoordinates d)))] with x hψ hfx hx
    change (testL2 ψ : SpatialCoordinates d → ℝ) x = (fL2 : SpatialCoordinates d → ℝ) x
    calc
      (testL2 ψ : SpatialCoordinates d → ℝ) x = ψ x := hψ
      _ = f x := rfl
      _ = (fL2 : SpatialCoordinates d → ℝ) x := hfx.symm
  have hwpos : 0 < sobolevVolumeLoad fL2 (w : SobolevData Ω) := by
    change 0 < inner ℝ fL2 (w : SobolevData Ω).1
    rw [hweq]
    exact real_inner_self_pos.mpr hfL2_ne
  exact (ne_of_gt hwpos) hwzero

private theorem aux_normalization
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
    (S : ResponseSpace Ω) (b : weakSobolevGraph Ω) (L : S.space →L[ℝ] ℝ)
    (hN : ℕ → Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))))
    (kappa : ℕ → ℝ) (hkappa : ∀ N, 0 < kappa N) (aN : ℕ → PositiveCoefficient Ω)
    (haN : ∀ N, (aN N).val = (kappa N)⁻¹ • (expPotentialCoefficient (hN N)).val) :
    ∀ N, dirichletResponse S (aN N) b =
        dirichletResponse S (expPotentialCoefficient (hN N -
          Lp.const ∞ (volume.restrict (Ω : Set (SpatialCoordinates d)))
            (Real.log (kappa N)))) b ∧
      inverseResponse S (aN N) L =
        inverseResponse S (expPotentialCoefficient (hN N -
          Lp.const ∞ (volume.restrict (Ω : Set (SpatialCoordinates d)))
            (Real.log (kappa N)))) L := by
  intro N
  have hk : 0 < (kappa N)⁻¹ := inv_pos.mpr (hkappa N)
  have ha : aN N = scalePositiveCoefficient (kappa N)⁻¹ hk
      (expPotentialCoefficient (hN N)) := by
    apply Subtype.ext
    simpa [scalePositiveCoefficient] using haN N
  have hcoef : expPotentialCoefficient (hN N -
      Lp.const ∞ (volume.restrict (Ω : Set (SpatialCoordinates d)))
        (Real.log (kappa N))) =
      scalePositiveCoefficient (kappa N)⁻¹ hk (expPotentialCoefficient (hN N)) := by
    rw [aux_expPotentialCoefficient_sub_const]
    congr 1
    rw [Real.exp_neg, Real.exp_log (hkappa N)]
  constructor
  · rw [ha, hcoef, dirichletResponse_scale_coefficient]
  · rw [ha, hcoef, inverseResponse_scale_coefficient, inv_inv]

private theorem aux_dirichletResponse_pos
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ ∞ phi)
    (hnonconst : ∃ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∃ y ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), phi x ≠ phi y)
    (b : weakSobolevGraph (centeredCube z r hr))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi)
    (a : PositiveCoefficient (centeredCube z r hr)) :
    0 < dirichletResponse (killedResponseSpace hP) a b := by
  letI : NeZero d := ⟨by omega⟩
  let Ω := centeredCube z r hr
  let S := killedResponseSpace hP
  have hnonneg : 0 ≤ dirichletResponse S a b := dirichletResponse_nonneg S a b
  by_contra hnot
  have hzero : dirichletResponse S a b = 0 :=
    le_antisymm (not_lt.mp hnot) hnonneg
  let q := dirichletMinimizer S a b
  have hform : sobolevCoefficientForm a q.val q.val = 0 := by
    simpa [q, dirichletResponse] using hzero
  obtain ⟨c, hc, hac⟩ := a.property
  have hform' : weightedGradientForm a.val (sobolevGradient q.val)
      (sobolevGradient q.val) = 0 := by
    simpa [sobolevCoefficientForm] using hform
  have hqgrad : sobolevGradient q.val = 0 :=
    eq_zero_of_coercive_self_le_zero
      (weightedGradientForm_coercive a.val hc hac) hform'.le
  have hqcoords : q.val.2 = 0 := by
    have h := congrArg
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => DomainL2 Ω)) hqgrad
    simpa [sobolevGradient] using h
  obtain ⟨Q, hQval, hQgrad⟩ := exists_nativeH1Function_of_weakSobolevGraph q
  obtain ⟨B, hBval, hBgrad⟩ := exists_nativeH1Function_of_weakSobolevGraph b
  have hBphi : B.toFun =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] phi := by
    filter_upwards [hb] with x hbx
    rw [hBval]
    exact hbx
  have hgeom : Homogenization.IsOpenBoundedConvexDomain
      (Ω : Set (SpatialCoordinates d)) :=
    lane2_isOpenBoundedConvexDomain_centeredCube z hr
  let phiH : Homogenization.H1Function (Ω : Set (SpatialCoordinates d)) :=
    Homogenization.H1Function.ofContDiffOnIsOpenBoundedConvexDomain hgeom
      (hphi.of_le (by simp))
  have hphiH : ContDiff ℝ ∞ phiH.toFun := by
    simpa [phiH, Homogenization.H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
      Homogenization.H1Function.ofContDiffOnIsSobolevRegularDomain] using hphi
  have hBphiH : B.toFun =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
      phiH.toFun := by
    simpa [phiH, Homogenization.H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
      Homogenization.H1Function.ofContDiffOnIsSobolevRegularDomain] using hBphi
  have hgradBphi : ∀ i : Fin d,
      (fun x => phiH.grad x i) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
        fun x => (b : SobolevData Ω).2 i x := by
    intro i
    have h := lane2_grad_ae_eq_of_ae_eq Ω.isOpen
      (centeredCube_isBounded z hr) B phiH hBphiH i
    filter_upwards [h] with x hx
    calc
      phiH.grad x i = B.grad x i := hx.symm
      _ = (b : SobolevData Ω).2 i x := by
        exact congrFun (congrFun hBgrad x) i
  have hdiffmem : q.val - b.val ∈ killedSobolevGraph Ω := by
    change q.val - b.val ∈ S.space
    exact dirichletMinimizer_mem_affine S a b
  let w : killedSobolevGraph Ω := ⟨q.val - b.val, hdiffmem⟩
  obtain ⟨V, hVval, hVgrad⟩ := exists_nativeH10Function_of_killedSobolevGraph w
  have hQzero : ∀ i : Fin d,
      (fun x => Q.grad x i) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] 0 := by
    intro i
    have hi : q.val.2 i = 0 := congrFun hqcoords i
    have hqi : (fun x => (q.val.2 i : DomainL2 Ω) x) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] 0 := by
      rw [hi]
      exact Lp.coeFn_zero ℝ 2 (volume.restrict (Ω : Set (SpatialCoordinates d)))
    filter_upwards [hqi] with x hz
    change Q.grad x i = 0
    rw [congrFun (congrFun hQgrad x) i]
    exact hz
  let value : SpatialCoordinates d → ℝ := fun x => phi x + V.toH1Function.toFun x
  let grad : SpatialCoordinates d → Homogenization.Vec d :=
    fun x i => phiH.grad x i + V.toH1Function.grad x i
  have hvalueQ : value =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] Q.toFun := by
    filter_upwards [hb, Lp.coeFn_sub q.val.1 b.val.1] with x hb' hs
    change phi x + V.toH1Function.toFun x = Q.toFun x
    rw [hQval, hVval]
    change phi x + ((q.val.1 - b.val.1 : DomainL2 Ω) : SpatialCoordinates d → ℝ) x =
      (q.val.1 : SpatialCoordinates d → ℝ) x
    rw [hs]
    simp only [Pi.sub_apply]
    rw [hb']
    ring
  have hgradzero : ∀ i : Fin d,
      (fun x => grad x i) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] 0 := by
    intro i
    have hi : q.val.2 i = 0 := congrFun hqcoords i
    filter_upwards [hgradBphi i, Lp.coeFn_sub (q.val.2 i) (b.val.2 i),
      Lp.coeFn_zero ℝ 2 (volume.restrict (Ω : Set (SpatialCoordinates d)))] with
        x hphi' hv hqz
    change phiH.grad x i + V.toH1Function.grad x i = 0
    rw [show V.toH1Function.grad x i = (w : SobolevData Ω).2 i x by
      exact congrFun (congrFun hVgrad x) i]
    change phiH.grad x i + ((q.val.2 i - b.val.2 i : DomainL2 Ω) :
      SpatialCoordinates d → ℝ) x = 0
    rw [hv, hi, hphi']
    simp only [Pi.sub_apply]
    rw [hqz]
    simp
  have hgradQ : ∀ i : Fin d,
      (fun x => grad x i) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
        fun x => Q.grad x i := by
    intro i
    exact (hgradzero i).trans (hQzero i).symm
  let U := lane2_H1ofAEEq2 Q value grad hvalueQ hgradQ
  have htrace : SubdiffusiveProcess.CoarseGrainingVocab.HasZeroTraceDifferenceOn
      (Ω : Set (SpatialCoordinates d)) U phiH := by
    refine ⟨V, ?_, ?_⟩
    · intro x
      rfl
    · intro x
      rfl
  have hharm : SubdiffusiveProcess.CoarseGrainingVocab.IsWeaklyHarmonicOn
      (fun _ : SpatialCoordinates d => (1 : ℝ)) (Ω : Set (SpatialCoordinates d)) U := by
    intro ψ
    have hall : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
        ∀ i : Fin d, U.grad x i = 0 := by
      rw [ae_all_iff]
      intro i
      simpa [U, lane2_H1ofAEEq2] using hgradzero i
    apply integral_eq_zero_of_ae
    filter_upwards [hall] with x hx
    have hvec : U.grad x = 0 := by
      funext i
      exact hx i
    simp [Homogenization.vecDot, hvec]
  have hvalue_const : ∃ C : ℝ,
      U.toFun =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] fun _ => C := by
    let W : Homogenization.H1MeanZeroFunction (Ω : Set (SpatialCoordinates d)) :=
      ⟨U.subAverage, U.meanZeroOn_subAverage⟩
    have hC := (Homogenization.h1CoerciveEstimate_of_isOpenBoundedConvexDomain hgeom).bound W
    have hUgradLp : U.gradToVectorL2 = 0 := by
      apply Lp.ext
      filter_upwards [Homogenization.H1Function.coeFn_gradToVectorL2 U,
        (ae_all_iff.mpr hgradzero),
        Lp.coeFn_zero (Homogenization.Vec d) 2
          (volume.restrict (Ω : Set (SpatialCoordinates d)))] with x hx hz hzero
      rw [hx, hzero]
      funext i
      simpa [U, lane2_H1ofAEEq2] using (hz i)
    have hWgrad : W.gradientL2Norm = 0 := by
      change ‖U.subAverage.gradToVectorL2‖ = 0
      rw [Homogenization.H1Function.gradToVectorL2_subAverage_eq]
      exact norm_eq_zero.mpr hUgradLp
    have hWval : W.valueL2Norm = 0 := by
      apply le_antisymm
      · simpa [hWgrad] using hC
      · exact norm_nonneg _
    have hLp : W.toH1Function.toScalarL2 = 0 := by
      apply norm_eq_zero.mp
      exact hWval
    refine ⟨Homogenization.integralAverage (Ω : Set (SpatialCoordinates d)) U.toFun, ?_⟩
    have hLpzero : (W.toH1Function.toScalarL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] 0 := by
      rw [hLp]
      exact Lp.coeFn_zero ℝ 2 (volume.restrict (Ω : Set (SpatialCoordinates d)))
    filter_upwards [Homogenization.H1Function.coeFn_toScalarL2 W.toH1Function,
      hLpzero] with x hx hz
    calc
      U.toFun x = U.subAverage.toFun x +
          Homogenization.integralAverage (Ω : Set (SpatialCoordinates d)) U.toFun := by
        rw [Homogenization.H1Function.subAverage_apply]
        ring
      _ = W.toH1Function.toFun x +
          Homogenization.integralAverage (Ω : Set (SpatialCoordinates d)) U.toFun := by rfl
      _ = (W.toH1Function.toScalarL2 : SpatialCoordinates d → ℝ) x +
          Homogenization.integralAverage (Ω : Set (SpatialCoordinates d)) U.toFun := by
        rw [hx]
      _ = Homogenization.integralAverage (Ω : Set (SpatialCoordinates d)) U.toFun := by
        rw [hz]
        simp
  obtain ⟨C, hUC⟩ := hvalue_const
  obtain ⟨x, hx, y, hy, hxy⟩ := hnonconst
  have hboundary (p : SpatialCoordinates d)
      (hp : p ∈ frontier (Ω : Set (SpatialCoordinates d))) : phi p = C := by
    have hlocal := lane2_localBoundaryRep_aux (a := fun _ : SpatialCoordinates d => (1 : ℝ))
      (lam := 1) (Lam := 1) hd (centeredCube_eq_openBox z hr)
      (fun j => by linarith) (by norm_num : (0 : ℝ) < 1) continuous_const
      (by intro q hq; exact ⟨by norm_num, by norm_num⟩)
      phiH U hphiH hharm htrace (fun _ => C) continuous_const.continuousOn hUC.symm p hp
    obtain ⟨T, hTopen, hpT, g, hgcont, hgzero, hagree⟩ := hlocal
    letI : (nhdsWithin p (Ω : Set (SpatialCoordinates d))).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp hp.1
    have hlim := tendsto_boundary_of_local_continuous_vanishing
      hTopen hpT hgcont hgzero hagree hphi.continuous.continuousAt
    have hlimC : Tendsto (fun _ : SpatialCoordinates d => C)
        (nhdsWithin p (Ω : Set (SpatialCoordinates d))) (nhds C) := tendsto_const_nhds
    exact (tendsto_nhds_unique hlimC hlim).symm
  exact hxy (hboundary x hx |>.trans (hboundary y hy).symm)



theorem response_convention
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ ∞ phi)
    (hnonconst : ∃ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∃ y ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), phi x ≠ phi y)
    (b : weakSobolevGraph (centeredCube z r hr))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi)
    (f : SpatialCoordinates d → ℝ) (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f)
    (hfsupp : tsupport f ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hf0 : ∃ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), f x ≠ 0)
    (fL2 : DomainL2 (centeredCube z r hr))
    (hfL2 : (fL2 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f)
    (hN : ℕ → Lp ℝ ∞ (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (kappa : ℕ → ℝ) (hkappa : ∀ N, 0 < kappa N)
    (aN : ℕ → PositiveCoefficient (centeredCube z r hr))
    (haN : ∀ N, (aN N).val = (kappa N)⁻¹ • (expPotentialCoefficient (hN N)).val) :
    let S := killedResponseSpace hP
    let L := (sobolevVolumeLoad fL2).comp S.space.subtypeL
    (∀ g : Lp ℝ ∞ (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
      0 < dirichletResponse S (expPotentialCoefficient g) b ∧
      0 < inverseResponse S (expPotentialCoefficient g) L) ∧
    (∀ N, dirichletResponse S (aN N) b =
        dirichletResponse S (expPotentialCoefficient (hN N -
          Lp.const ∞ (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))
            (Real.log (kappa N)))) b ∧
      inverseResponse S (aN N) L =
        inverseResponse S (expPotentialCoefficient (hN N -
          Lp.const ∞ (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))
            (Real.log (kappa N)))) L) := by
  dsimp
  constructor
  · intro g
    constructor
    · exact aux_dirichletResponse_pos d hd z r hr hP phi hphi hnonconst b hb
        (expPotentialCoefficient g)
    · apply (inverseResponse_pos_iff (killedResponseSpace hP)
        (expPotentialCoefficient g)
        ((sobolevVolumeLoad fL2).comp (killedResponseSpace hP).space.subtypeL)).2
      exact aux_volumeLoad_comp_ne_zero hP f hf hfc hfsupp hf0 fL2 hfL2
  · exact aux_normalization (killedResponseSpace hP) b
      ((sobolevVolumeLoad fL2).comp (killedResponseSpace hP).space.subtypeL)
      hN kappa hkappa aN haN

end Paper
