module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceDecaySigned

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Set Topology
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped CompactlySupported ENNReal ZeroAtInfty

noncomputable section

variable {d : ℕ}



theorem integrableOn_scalarCoeffEnergy
    {W : Set (Vec d)} {c : Vec d → ℝ} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c))
    (u : H1Function W) :
    IntegrableOn (fun x ↦ c x * vecNormSq (u.grad x)) W := by
  have hflux : MemVectorL2 W (fun x ↦ c x • u.grad x) := by
    simpa only [scalarCoeffField, matVecMul_scalarMatrix] using!
      memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.grad_memVectorL2
  simpa only [vecDot_smul_left, vecNormSq] using!
    integrableOn_vecDot_of_memVectorL2 hflux u.grad_memVectorL2



private theorem scalarCoeffEnergy_eq_bilin
    {W : Set (Vec d)} {c : Vec d → ℝ} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c))
    (u : H1Function W) :
    (∫ x in W, c x * vecNormSq (u.grad x) ∂volume) =
      MassiveH1Hilbert.coeffGradientBilin hEll
        (MassiveH1Hilbert.ofH1Function u)
        (MassiveH1Hilbert.ofH1Function u) := by
  symm
  simpa only [vecDot_smul_left, vecNormSq] using!
    MassiveH1Hilbert.coeffGradientBilin_apply_ofH1Function hEll u u



private theorem scalarCoeffCross_eq_inner
    {W : Set (Vec d)} {c : Vec d → ℝ} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c))
    (u v : H1Function W) :
    (∫ x in W, c x * vecDot (u.grad x) (v.grad x) ∂volume) =
      inner ℝ u.gradToHilbertVectorL2
        (hilbertCoeffOperator hEll v.gradToHilbertVectorL2) := by
  calc
    (∫ x in W, c x * vecDot (u.grad x) (v.grad x) ∂volume) =
        ∫ x in W, vecDot (c x • v.grad x) (u.grad x) ∂volume := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        simp only [Pi.smul_apply, smul_eq_mul, vecDot, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        ring_nf
    _ = MassiveH1Hilbert.coeffGradientBilin hEll
          (MassiveH1Hilbert.ofH1Function v)
          (MassiveH1Hilbert.ofH1Function u) :=
      (MassiveH1Hilbert.coeffGradientBilin_apply_ofH1Function hEll v u).symm
    _ = inner ℝ (hilbertCoeffOperator hEll v.gradToHilbertVectorL2)
          u.gradToHilbertVectorL2 := by
      rw [MassiveH1Hilbert.coeffGradientBilin_apply,
        MassiveH1Hilbert.gradient_ofH1Function,
        MassiveH1Hilbert.gradient_ofH1Function]
    _ = inner ℝ u.gradToHilbertVectorL2
          (hilbertCoeffOperator hEll v.gradToHilbertVectorL2) :=
      real_inner_comm _ _



theorem scalarCoeffEnergy_le_of_tendsto_inner_gradient
    {W : Set (Vec d)} {c : Vec d → ℝ} {lam Lam C : ℝ}
    (hlam : 0 ≤ lam)
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c))
    (w : ℕ → H1Function W) (u : H1Function W) (phi : ℕ → ℕ)
    (hgradient : ∀ z : HilbertVectorL2 W,
      Tendsto (fun n ↦ inner ℝ (w (phi n)).gradToHilbertVectorL2 z) atTop
        (nhds (inner ℝ u.gradToHilbertVectorL2 z)))
    (henergy : ∀ n,
      ∫ x in W, c x * vecNormSq ((w n).grad x) ∂volume ≤ C) :
    ∫ x in W, c x * vecNormSq (u.grad x) ∂volume ≤ C := by
  let A : HilbertVectorL2 W →L[ℝ] HilbertVectorL2 W :=
    hilbertCoeffOperator hEll
  let E : H1Function W → ℝ := fun q ↦
    ∫ x in W, c x * vecNormSq (q.grad x) ∂volume
  let B : H1Function W → H1Function W → ℝ := fun q r ↦
    ∫ x in W, c x * vecDot (q.grad x) (r.grad x) ∂volume
  have hcross : Tendsto (fun n ↦ B (w (phi n)) u) atTop (nhds (E u)) := by
    have h := hgradient (A u.gradToHilbertVectorL2)
    simpa only [B, E, A, scalarCoeffCross_eq_inner hEll,
      scalarCoeffEnergy_eq_bilin hEll,
      MassiveH1Hilbert.coeffGradientBilin_apply,
      MassiveH1Hilbert.gradient_ofH1Function,
      real_inner_comm] using! h
  have hbound : ∀ n, 2 * B (w (phi n)) u ≤ C + E u := by
    intro n
    let q : H1Function W := w (phi n) - u
    have hqNonneg : 0 ≤ E q := by
      have hcoercive := MassiveH1Hilbert.coeffGradientBilin_self_ge hEll
        (MassiveH1Hilbert.ofH1Function q)
      rw [← scalarCoeffEnergy_eq_bilin hEll q] at hcoercive
      exact (mul_nonneg hlam (sq_nonneg _)).trans hcoercive
    have hwInt := integrableOn_scalarCoeffEnergy hEll (w (phi n))
    have huInt := integrableOn_scalarCoeffEnergy hEll u
    have hcrossInt : IntegrableOn
        (fun x ↦ c x * vecDot ((w (phi n)).grad x) (u.grad x)) W := by
      have hflux : MemVectorL2 W (fun x ↦ c x • (w (phi n)).grad x) := by
        simpa only [scalarCoeffField, matVecMul_scalarMatrix] using!
          memVectorL2_matVecMul_of_isEllipticFieldOn hEll
            (w (phi n)).grad_memVectorL2
      simpa only [vecDot_smul_left] using!
        integrableOn_vecDot_of_memVectorL2 hflux u.grad_memVectorL2
    have hqExpand : E q = E (w (phi n)) - 2 * B (w (phi n)) u + E u := by
      dsimp only [E, B, q]
      rw [H1Function.sub_grad]
      calc
        (∫ x in W, c x * vecNormSq ((w (phi n)).grad x - u.grad x) ∂volume) =
            ∫ x in W,
              (c x * vecNormSq ((w (phi n)).grad x) -
                2 * (c x * vecDot ((w (phi n)).grad x) (u.grad x))) +
                c x * vecNormSq (u.grad x) ∂volume := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x ↦ by
            simp only [vecNormSq, vecDot, Pi.sub_apply, Finset.mul_sum,
              ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
            ring_nf
        _ = (∫ x in W,
              c x * vecNormSq ((w (phi n)).grad x) -
                2 * (c x * vecDot ((w (phi n)).grad x) (u.grad x)) ∂volume) +
              ∫ x in W, c x * vecNormSq (u.grad x) ∂volume := by
          simpa only [Pi.add_apply] using!
            integral_add (μ := volume.restrict W)
              (hwInt.sub (hcrossInt.const_mul 2)) huInt
        _ = (∫ x in W, c x * vecNormSq ((w (phi n)).grad x) ∂volume) -
              2 * (∫ x in W,
                c x * vecDot ((w (phi n)).grad x) (u.grad x) ∂volume) +
              ∫ x in W, c x * vecNormSq (u.grad x) ∂volume := by
          rw [integral_sub hwInt (hcrossInt.const_mul 2), integral_const_mul]
    rw [hqExpand] at hqNonneg
    linarith only [hqNonneg, henergy (phi n)]
  have hlimit : 2 * E u ≤ C + E u := by
    apply le_of_tendsto (hcross.const_mul 2)
    exact Filter.Eventually.of_forall hbound
  linarith



theorem exists_localMassiveWeakSolutions_with_energy_of_pointwise_cube_limit
    [NeZero d] {c : Vec d → ℝ}
    (B : MassiveCubeBounds c (fun _ ↦ (1 : ℝ)))
    {mu : ℝ} (hmu : 0 < mu) (f : C_c(Vec d, ℝ))
    (uCube : ∀ n : ℕ, H10Function (cube d (n : ℤ)))
    (v : ℕ → Vec d → ℝ) (u : Vec d → ℝ)
    (hcontrolled : ∀ n,
      IsControlledMassiveCubeSolution c (fun _ ↦ 1) mu f n (uCube n))
    (hvEq : ∀ n, v n =ᵐ[volume] (uCube n).zeroExtension)
    (hvLim : ∀ x, Tendsto (fun n ↦ v n x) atTop (nhds (u x))) :
    ∀ k : ℕ, ∃ uLocal : H1Function (cube d (k : ℤ)),
      uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
      IsMassiveWeakSolutionOn c (fun _ ↦ 1) mu
        (cube d (k : ℤ)) uLocal f ∧
      2 * mu * (∫ x in cube d (k : ℤ),
        c x * vecNormSq (uLocal.grad x) ∂volume) ≤
        ∫ x, f x ^ 2 ∂volume := by
  intro k
  let hcube := Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (k : ℤ)
  letI : IsFiniteMeasure (volumeMeasureOn (cube d (k : ℤ))) :=
    hcube.isBoundedDomain.isFiniteMeasure_restrict_volume
  let hsubset (n : ℕ) : cube d (k : ℤ) ⊆ cube d ((k + n : ℕ) : ℤ) :=
    Section6ExcessDecay.cube_subset_cube_of_le (by omega)
  let w (n : ℕ) : H1Function (cube d (k : ℤ)) :=
    (uCube (k + n)).toH1Function.restrict hcube.isOpen (hsubset n)
  obtain ⟨Cgrad, _hCgrad, hgradient⟩ :=
    exists_uniform_local_gradient_norm_bound B hmu f uCube hcontrolled k
  have hbound : ∀ n, ∀ᵐ x ∂(volumeMeasureOn (cube d (k : ℤ))),
      |(w n).toFun x| ≤ ‖compactSupportToC0 f‖ / mu := by
    intro n
    exact (hcontrolled (k + n)).2.2.2.filter_mono <|
      ae_mono (Measure.restrict_mono (hsubset n) le_rfl)
  have hwEq : ∀ n, (w n).toFun =ᵐ[
      volumeMeasureOn (cube d (k : ℤ))] v (k + n) := by
    intro n
    have hvLocal : v (k + n) =ᵐ[
        volumeMeasureOn (cube d (k : ℤ))] (uCube (k + n)).zeroExtension :=
      (hvEq (k + n)).filter_mono <|
        ae_mono (show volumeMeasureOn (cube d (k : ℤ)) ≤ volume from
          Measure.restrict_le_self)
    filter_upwards [hvLocal,
      ae_restrict_mem hcube.isOpen.measurableSet] with x hx hxCube
    change (uCube (k + n)).toH1Function.toFun x = v (k + n) x
    rw [hx, (uCube (k + n)).zeroExtension_apply_of_mem ((hsubset n) hxCube)]
  have hpoint : ∀ᵐ x ∂(volumeMeasureOn (cube d (k : ℤ))),
      Tendsto (fun n ↦ (w n).toFun x) atTop (nhds (u x)) := by
    filter_upwards [ae_all_iff.2 hwEq] with x hx
    have hvSub : Tendsto (fun n ↦ v (k + n) x) atTop (nhds (u x)) := by
      simpa only [Function.comp_apply] using!
        (hvLim x).comp (strictMono_id.const_add k).tendsto_atTop
    apply Filter.Tendsto.congr' _ hvSub
    exact Filter.Eventually.of_forall fun n ↦ (hx n).symm
  have hw : ∀ n, IsMassiveWeakSolutionOn c (fun _ ↦ 1) mu
      (cube d (k : ℤ)) (w n) f := by
    intro n
    exact IsMassiveWeakSolutionOn.restrict hcube.isOpen
      (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d
        ((k + n : ℕ) : ℤ)).isOpen
      (hsubset n) (hcontrolled (k + n)).1
  have hfMem : MemLp (fun x : Vec d ↦ f x) 2 volume :=
    f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport
  have hfLocal : MemL2On (cube d (k : ℤ)) f := hfMem.restrict _
  have hwMeas : ∀ n,
      AEStronglyMeasurable (w n).toFun
        (volumeMeasureOn (cube d (k : ℤ))) :=
    fun n ↦ (w n).memL2.aestronglyMeasurable
  have huMeas : AEStronglyMeasurable u
      (volumeMeasureOn (cube d (k : ℤ))) :=
    aestronglyMeasurable_of_tendsto_ae atTop hwMeas hpoint
  have huBound : ∀ᵐ x ∂(volumeMeasureOn (cube d (k : ℤ))),
      ‖u x‖ ≤ ‖compactSupportToC0 f‖ / mu := by
    filter_upwards [hpoint, ae_all_iff.2 hbound] with x hx hxb
    have hmem : -(‖compactSupportToC0 f‖ / mu) ≤ u x ∧
        u x ≤ ‖compactSupportToC0 f‖ / mu := by
      have hclosed := isClosed_Icc.mem_of_tendsto hx
        (Filter.Eventually.of_forall fun n ↦ by
          change -(‖compactSupportToC0 f‖ / mu) ≤ (w n).toFun x ∧
            (w n).toFun x ≤ ‖compactSupportToC0 f‖ / mu
          exact abs_le.mp (hxb n))
      exact hclosed
    simpa only [Real.norm_eq_abs] using! abs_le.mpr hmem
  have hu : MemL2On (cube d (k : ℤ)) u :=
    MemLp.of_bound huMeas (‖compactSupportToC0 f‖ / mu) huBound
  have hvalue : Tendsto
      (fun n ↦ eLpNorm (fun x ↦ (w n).toFun x - u x) 2
        (volumeMeasureOn (cube d (k : ℤ)))) atTop (nhds 0) :=
    tendsto_eLpNorm_two_of_tendsto_ae_of_dominated hwMeas hu
      (memLp_const (‖compactSupportToC0 f‖ / mu)) hbound hpoint
  obtain ⟨uLocal, phi, _hphi, huLocal, hvalueSub, hgradientSub⟩ :=
    exists_h1Function_of_tendsto_value_of_gradient_norm_le w hu hvalue
      Cgrad (by simpa only [w] using! hgradient)
  have hsolution : IsMassiveWeakSolutionOn c (fun _ ↦ 1) mu
      (cube d (k : ℤ)) uLocal f :=
    isMassiveWeakSolutionOn_of_tendsto_value_of_tendsto_inner_gradient
      (B.ell k) (B.rho_measurable k) (B.rho_bounded k) hfLocal
      w uLocal phi hvalueSub hgradientSub hw
  have htwoMu : 0 < 2 * mu := mul_pos two_pos hmu
  have henergySequence : ∀ n,
      ∫ x in cube d (k : ℤ), c x * vecNormSq ((w n).grad x) ∂volume ≤
        (∫ x, f x ^ 2 ∂volume) / (2 * mu) := by
    intro n
    have hlarge := Section6ExcessDecay.isOpenBoundedConvexDomain_cube d
      ((k + n : ℕ) : ℤ)
    have henergyIntegrable : IntegrableOn
        (fun x ↦ c x * vecNormSq ((uCube (k + n)).toH1Function.grad x))
        (cube d ((k + n : ℕ) : ℤ)) :=
      integrableOn_scalarCoeffEnergy (B.ell (k + n))
        (uCube (k + n)).toH1Function
    have henergyNonneg : 0 ≤ᵐ[
        volume.restrict (cube d ((k + n : ℕ) : ℤ))]
        fun x ↦ c x * vecNormSq ((uCube (k + n)).toH1Function.grad x) := by
      filter_upwards [ae_restrict_mem hlarge.isOpen.measurableSet] with x hx
      exact mul_nonneg
        ((B.lam_pos (k + n)).le.trans (B.coeff_lower (k + n) x hx))
        (vecNormSq_nonneg _)
    have hlocalEnergy :
        (∫ x in cube d (k : ℤ), c x * vecNormSq ((w n).grad x) ∂volume) ≤
          ∫ x in cube d ((k + n : ℕ) : ℤ),
            c x * vecNormSq ((uCube (k + n)).toH1Function.grad x) ∂volume := by
      have hmono := setIntegral_mono_set henergyIntegrable henergyNonneg
        (Filter.Eventually.of_forall (hsubset n))
      simpa only [w, H1Function.restrict] using! hmono
    apply (le_div_iff₀ htwoMu).2
    calc
      (∫ x in cube d (k : ℤ),
          c x * vecNormSq ((w n).grad x) ∂volume) * (2 * mu) =
          2 * mu * ∫ x in cube d (k : ℤ),
            c x * vecNormSq ((w n).grad x) ∂volume := by ring
      _ ≤ 2 * mu * ∫ x in cube d ((k + n : ℕ) : ℤ),
          c x * vecNormSq ((uCube (k + n)).toH1Function.grad x) ∂volume :=
        mul_le_mul_of_nonneg_left hlocalEnergy htwoMu.le
      _ ≤ ∫ x in cube d ((k + n : ℕ) : ℤ), f x ^ 2 ∂volume := by
        simpa only [one_mul, pow_two] using! (hcontrolled (k + n)).2.2.1
      _ ≤ ∫ x, f x ^ 2 ∂volume :=
        setIntegral_le_integral hfMem.integrable_sq
          (Filter.Eventually.of_forall fun x ↦ sq_nonneg (f x))
  have henergyLocal := scalarCoeffEnergy_le_of_tendsto_inner_gradient
    (B.lam_pos k).le (B.ell k) w uLocal phi hgradientSub henergySequence
  have hscaled := (le_div_iff₀ htwoMu).1 henergyLocal
  refine ⟨uLocal, huLocal, hsolution, ?_⟩
  simpa only [mul_comm] using! hscaled

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
