import SubdiffusiveProcess.Paper.obl_BH_lipschitz_smooth_approx
import SubdiffusiveProcess.Paper.obl_BH_compact_preimage_nullity
import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.DirichletForm.All
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal Topology ContDiff

namespace Paper



theorem obl_BH_energy_measure_convergence
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : _root_.DirichletForm
      (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (halg : DirichletForm.IsCoreAlgebra E.toClosedForm)
    (hnc : DirichletForm.HasNormalContractions E)
    (v : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hv : v ∈ E.toClosedForm.domain)
    (vc : SpatialCoordinates d → ℝ) (hvc : Continuous vc)
    (hrep : (⇑v =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] vc))
    (T : ℝ → ℝ)
    (hLip : ∃ K : ℝ≥0, LipschitzWith K T)
    (hT0 : T 0 = 0)
    (Tderiv : ℝ → ℝ)
    (hderiv_meas : Measurable Tderiv)
    (hderiv : ∀ᵐ s : ℝ, HasDerivAt T (Tderiv s) s)
    (w : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hw : w ∈ E.toClosedForm.domain)
    (hwrep : (⇑w =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
      (fun x => T (vc x)))) :
    ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
      (Gamma.measure w B).toReal =
        ∫ x in B, (Tderiv (vc x)) ^ 2 ∂(Gamma.measure v) := by
  rcases hLip with ⟨K, hKT⟩
  obtain ⟨Tk, Dk, C, hC, hTk, hTk_lim, hDk_lim⟩ :=
    obl_BH_lipschitz_smooth_approx T ⟨K, hKT⟩ hT0 Tderiv hderiv_meas hderiv
  have hvcLp : MemLp vc 2 (volume.restrict (Q : Set (SpatialCoordinates d))) :=
    (memLp_congr_ae hrep).mp (Lp.memLp v)
  have hTmem : MemLp (fun x => T (vc x)) 2
      (volume.restrict (Q : Set (SpatialCoordinates d))) := by
    simpa [Function.comp_def] using hKT.comp_memLp hT0 hvcLp
  let Cnn : ℝ≥0 := ⟨C, hC⟩
  have hTk_lip : ∀ k : ℕ, LipschitzWith Cnn (Tk k) := by
    intro k
    apply lipschitzWith_of_nnnorm_deriv_le
    · exact (hTk k).1.differentiable (by norm_num)
    · intro s
      rw [show deriv (Tk k) s = Dk k s from (hTk k).2.2.2.1 s |>.deriv]
      apply NNReal.coe_le_coe.mp
      simpa [Real.norm_eq_abs] using hTk k |>.2.2.2.2 s
  have hTk_mem : ∀ k : ℕ, MemLp (fun x => Tk k (vc x)) 2
      (volume.restrict (Q : Set (SpatialCoordinates d))) := by
    intro k
    simpa [Function.comp_def] using (hTk_lip k).comp_memLp (hTk k).2.1 hvcLp
  have hTk_sq_bound : ∀ k : ℕ, ∀ x : SpatialCoordinates d,
      |Tk k (vc x)| ≤ C * |vc x| := by
    intro k x
    have h := (hTk_lip k).norm_sub_le (vc x) 0
    simpa [Cnn, hTk k |>.2.1, Real.norm_eq_abs, abs_zero, mul_comm] using h
  have hT_sq_bound : ∀ x : SpatialCoordinates d, |T (vc x)| ≤ K * |vc x| := by
    intro x
    have h := hKT.norm_sub_le (vc x) 0
    simpa [hT0, Real.norm_eq_abs, abs_zero, mul_comm] using h
  have hL2_lim : Tendsto (fun k : ℕ =>
      eLpNorm (fun x => Tk k (vc x) - T (vc x)) 2
        (volume.restrict (Q : Set (SpatialCoordinates d)))) atTop (𝓝 0) := by
    let μ := volume.restrict (Q : Set (SpatialCoordinates d))
    let F : ℕ → SpatialCoordinates d → ℝ :=
      fun k x => Tk k (vc x) - T (vc x)
    have hFmem : ∀ k : ℕ, MemLp (F k) 2 μ := by
      intro k
      simpa [F, μ] using (hTk_mem k).sub hTmem
    have hFmeas : ∀ k : ℕ, AEStronglyMeasurable (F k) μ := by
      intro k
      exact (hFmem k).1
    have hFbound : ∀ k : ℕ, ∀ x : SpatialCoordinates d,
        |F k x| ≤ (C + (K : ℝ)) * |vc x| := by
      intro k x
      dsimp [F]
      calc
        |Tk k (vc x) - T (vc x)| ≤ |Tk k (vc x)| + |T (vc x)| := abs_sub _ _
        _ ≤ C * |vc x| + (K : ℝ) * |vc x| :=
          add_le_add (hTk_sq_bound k x) (hT_sq_bound x)
        _ = (C + (K : ℝ)) * |vc x| := by ring
    have hbound_int : Integrable (fun x : SpatialCoordinates d =>
        (C + (K : ℝ)) ^ 2 * vc x ^ 2) μ := by
      simpa [μ] using (hvcLp.integrable_sq.const_mul ((C + (K : ℝ)) ^ 2))
    have hsq_lim : Tendsto (fun k : ℕ =>
        ∫ x, (F k x) ^ 2 ∂μ) atTop (𝓝 0) := by
      have hmeas : ∀ k : ℕ,
          AEStronglyMeasurable (fun x : SpatialCoordinates d => (F k x) ^ 2) μ := by
        intro k
        simpa only [Pi.pow_apply] using (hFmeas k).pow (2 : ℕ)
      have hbound : ∀ k : ℕ, ∀ᵐ x : SpatialCoordinates d ∂μ,
          ‖(F k x) ^ 2‖ ≤ (C + (K : ℝ)) ^ 2 * vc x ^ 2 := by
        intro k
        filter_upwards with x
        have h := hFbound k x
        have hnonneg : 0 ≤ (C + (K : ℝ)) * |vc x| := by positivity
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (F k x))]
        calc
          F k x ^ 2 = |F k x| ^ 2 := by rw [sq_abs]
          _ ≤ ((C + (K : ℝ)) * |vc x|) ^ 2 :=
            (sq_le_sq₀ (abs_nonneg (F k x)) hnonneg).2 h
          _ = (C + (K : ℝ)) ^ 2 * vc x ^ 2 := by
            rw [mul_pow, sq_abs]
      have hlim : ∀ᵐ x : SpatialCoordinates d ∂μ,
          Tendsto (fun k => (F k x) ^ 2) atTop (𝓝 ((0 : ℝ))) := by
        have hpoint : ∀ᵐ x : SpatialCoordinates d ∂μ,
            Tendsto (fun k => F k x) atTop (𝓝 0) := by
          filter_upwards with x
          have hc : Tendsto (fun _ : ℕ => T (vc x)) atTop (𝓝 (T (vc x))) :=
            tendsto_const_nhds
          simpa [F] using (hTk_lim (vc x)).sub hc
        filter_upwards [hpoint] with x hx
        simpa using hx.pow (2 : ℕ)
      have h := tendsto_integral_of_dominated_convergence (G := ℝ)
        (F := fun k x => (F k x) ^ 2)
        (f := fun _ : SpatialCoordinates d => (0 : ℝ))
        (fun x : SpatialCoordinates d => (C + (K : ℝ)) ^ 2 * vc x ^ 2)
        hmeas hbound_int hbound hlim
      simpa only [integral_zero] using h
    have hpow : ∀ k : ℕ, (eLpNorm (F k) (2 : ℝ≥0∞) μ).toReal ^ 2 =
        ∫ x, (F k x) ^ 2 ∂μ := by
      intro k
      have hmem := hFmem k
      have hcoe := hmem.coeFn_toLp
      have hleft : (∫ x, (F k x) ^ 2 ∂μ) =
          ∫ x, inner ℝ ((hmem.toLp (F k)) x) ((hmem.toLp (F k)) x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hcoe] with x hx
        rw [hx]
        simp [real_inner_self_eq_norm_sq]
      calc
        (eLpNorm (F k) (2 : ℝ≥0∞) μ).toReal ^ 2 =
            ‖hmem.toLp (F k)‖ ^ 2 := by rw [Lp.norm_toLp]
        _ = inner ℝ (hmem.toLp (F k)) (hmem.toLp (F k)) := by
          rw [real_inner_self_eq_norm_sq]
        _ = ∫ x, inner ℝ ((hmem.toLp (F k)) x) ((hmem.toLp (F k)) x) ∂μ :=
          L2.inner_def _ _
        _ = ∫ x, (F k x) ^ 2 ∂μ := hleft.symm
    have hq : Tendsto (fun k : ℕ =>
        (eLpNorm (F k) (2 : ℝ≥0∞) μ).toReal ^ 2)
        atTop (𝓝 0) := by
      simpa [hpow] using hsq_lim
    have hq' : Tendsto (fun k : ℕ =>
        (eLpNorm (F k) (2 : ℝ≥0∞) μ).toReal)
        atTop (𝓝 0) := by
      have hs := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hq
      have hs' : Tendsto (fun k : ℕ =>
          Real.sqrt ((eLpNorm (F k) (2 : ℝ≥0∞) μ).toReal ^ 2))
          atTop (𝓝 (Real.sqrt 0)) := by
        simpa only [Function.comp_apply] using hs
      simpa only [Real.sqrt_sq (ENNReal.toReal_nonneg), Real.sqrt_zero] using hs'
    have hq'' : Tendsto (fun k : ℕ =>
        eLpNorm (F k) (2 : ℝ≥0∞) μ) atTop (𝓝 0) := by
      exact (ENNReal.tendsto_toReal_iff (fun k => (hFmem k).eLpNorm_ne_top)
        ENNReal.zero_ne_top).mp hq'
    simpa [F, μ] using hq''
  have hcomp_mem : ∀ k : ℕ, ∃ uk : Lp ℝ 2
      (volume.restrict (Q : Set (SpatialCoordinates d))),
      uk ∈ E.toClosedForm.domain ∧
        (⇑uk =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
          (fun x => Tk k (vc x))) := by
    intro k
    let A : ℝ := C + 1
    have hA : 0 < A := by dsimp [A]; linarith
    let S : ℝ → ℝ := fun s => A⁻¹ * Tk k s
    have hSzero : S 0 = 0 := by simp [S, A, hTk k |>.2.1]
    have hSlip : LipschitzWith 1 S := by
      rw [lipschitzWith_iff_dist_le_mul]
      intro x y
      have hxy := (hTk_lip k).dist_le_mul x y
      simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hxy ⊢
      calc
        |S x - S y| = |A⁻¹| * |Tk k x - Tk k y| := by
          rw [show S x - S y = A⁻¹ * (Tk k x - Tk k y) by
            simp only [S]; ring, abs_mul]
        _ = A⁻¹ * |Tk k x - Tk k y| := by
          rw [abs_of_pos (inv_pos.mpr hA)]
        _ ≤ A⁻¹ * ((C : ℝ) * |x - y|) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt (inv_pos.mpr hA))
          simpa [Cnn] using hxy
        _ ≤ |x - y| := by
          have hratio : A⁻¹ * C ≤ (1 : ℝ) := by
            have hratio' : C / A ≤ (1 : ℝ) := by
              apply (div_le_iff₀ hA).2
              dsimp [A]
              linarith
            convert hratio' using 1 <;> ring
          calc
            A⁻¹ * (C * |x - y|) = (A⁻¹ * C) * |x - y| := by ring
            _ ≤ 1 * |x - y| := mul_le_mul_of_nonneg_right hratio (abs_nonneg _)
            _ = |x - y| := by ring
    have hScomp : MemLp (fun x => S (vc x)) 2
        (volume.restrict (Q : Set (SpatialCoordinates d))) := by
      simpa [Function.comp_def] using hSlip.comp_memLp hSzero hvcLp
    have hSnormal : DirichletForm.IsNormalContraction S :=
      { map_zero := hSzero
        dist_le := by
          intro x y
          simpa [Real.dist_eq] using hSlip.dist_le_mul x y }
    let u₀ : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))) :=
      hScomp.toLp (fun x => S (vc x))
    have hu₀rep : (⇑u₀ =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
        (fun x => S (v x))) := by
      filter_upwards [hScomp.coeFn_toLp, hrep] with x hxv hx
      rw [hxv, hx]
    have hu₀ : u₀ ∈ E.toClosedForm.domain ∧
        E.form u₀ u₀ ≤ E.form v v :=
      hnc.operatesOn S hSnormal v hv u₀ hu₀rep
    refine ⟨A • u₀, E.toClosedForm.domain.smul_mem A hu₀.1, ?_⟩
    filter_upwards [Lp.coeFn_smul A u₀, hScomp.coeFn_toLp] with x hx₁ hx₂
    have hx₀ : u₀ x = S (vc x) := by simpa [u₀] using hx₂
    rw [hx₁]
    change A * u₀ x = _
    rw [hx₀]
    simp only [smul_eq_mul, S]
    field_simp
  classical
  let uk : ℕ → Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))) :=
    fun k => Classical.choose (hcomp_mem k)
  have huk : ∀ k : ℕ, uk k ∈ E.toClosedForm.domain := by
    intro k
    exact (Classical.choose_spec (hcomp_mem k)).1
  have hukrep : ∀ k : ℕ,
      (⇑(uk k) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
        (fun x => Tk k (vc x))) := by
    intro k
    exact (Classical.choose_spec (hcomp_mem k)).2
  have hdiffrep : ∀ p r : ℕ,
      (⇑(uk p - uk r) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
        (fun x => Tk p (vc x) - Tk r (vc x))) := by
    intro p r
    filter_upwards [Lp.coeFn_sub (uk p) (uk r), hukrep p, hukrep r] with x hx hxp hxr
    rw [hx]
    simp only [Pi.sub_apply]
    rw [hxp, hxr]
  let μΓ : Measure (SpatialCoordinates d) := Gamma.measure v
  haveI : IsFiniteMeasure μΓ :=
    ⟨Gamma.measure_univ_lt_top v hv⟩
  have hDk_ae : ∀ᵐ x : SpatialCoordinates d ∂μΓ,
      Tendsto (fun k => Dk k (vc x)) atTop (𝓝 (Tderiv (vc x))) := by
    have hbad : volume {s : ℝ |
        ¬ Tendsto (fun k => Dk k s) atTop (𝓝 (Tderiv s))} = 0 :=
      (ae_iff.mp hDk_lim)
    obtain ⟨N, hsub, hNmeas, hNzero⟩ := exists_measurable_superset_of_null hbad
    have hpre := obl_BH_compact_preimage_nullity E Gamma halg hnc v hv vc hvc hrep
      N hNmeas hNzero
    rw [ae_iff]
    change μΓ (vc ⁻¹' {s : ℝ |
      ¬ Tendsto (fun k => Dk k s) atTop (𝓝 (Tderiv s))}) = 0
    exact measure_mono_null (preimage_mono hsub) (by simpa [μΓ] using hpre)
  have hTderiv_bound : ∀ᵐ x : SpatialCoordinates d ∂μΓ,
      |Tderiv (vc x)| ≤ C := by
    filter_upwards [hDk_ae] with x hx
    have hup : Tderiv (vc x) ≤ C :=
      le_of_tendsto hx (Filter.Eventually.of_forall fun k =>
        (abs_le.mp (hTk k |>.2.2.2.2 (vc x))).2)
    have hlo : -C ≤ Tderiv (vc x) :=
      ge_of_tendsto hx (Filter.Eventually.of_forall fun k =>
        (abs_le.mp (hTk k |>.2.2.2.2 (vc x))).1)
    exact (abs_le).2 ⟨hlo, hup⟩
  have hDmeas : ∀ k : ℕ,
      AEStronglyMeasurable (fun x : SpatialCoordinates d => Dk k (vc x)) μΓ := by
    intro k
    exact ((hTk k).2.2.1.comp hvc.measurable).aestronglyMeasurable
  have hTderiv_meas_Γ :
      AEStronglyMeasurable (fun x : SpatialCoordinates d => Tderiv (vc x)) μΓ :=
    (hderiv_meas.comp hvc.measurable).aestronglyMeasurable
  let G : ℕ → SpatialCoordinates d → ℝ :=
    fun k x => Dk k (vc x) - Tderiv (vc x)
  have hGmeas : ∀ k : ℕ, AEStronglyMeasurable (G k) μΓ := by
    intro k
    simpa [G] using (hDmeas k).sub hTderiv_meas_Γ
  have hGbound : ∀ k : ℕ, ∀ᵐ x : SpatialCoordinates d ∂μΓ,
      |G k x| ≤ 2 * C := by
    intro k
    filter_upwards [hTderiv_bound] with x hx
    dsimp [G]
    calc
      |Dk k (vc x) - Tderiv (vc x)| ≤
          |Dk k (vc x)| + |Tderiv (vc x)| := abs_sub _ _
      _ ≤ C + C := add_le_add
        (hTk k |>.2.2.2.2 (vc x)) hx
      _ = 2 * C := by ring
  have hGsq_int : ∀ k : ℕ, Integrable (fun x => (G k x) ^ 2) μΓ := by
    intro k
    apply Integrable.mono (integrable_const ((2 * C) ^ 2))
      ((hGmeas k).pow (2 : ℕ))
    filter_upwards [hGbound k] with x hx
    change |G k x ^ 2| ≤ ‖(2 * C) ^ 2‖
    rw [abs_of_nonneg (sq_nonneg (G k x)), Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (2 * C))]
    calc
      G k x ^ 2 = |G k x| ^ 2 := by rw [sq_abs]
      _ ≤ (2 * C) ^ 2 := (sq_le_sq₀ (abs_nonneg (G k x)) (by positivity)).2 hx
  have hGint_lim : Tendsto (fun k : ℕ =>
      ∫ x, (G k x) ^ 2 ∂μΓ) atTop (𝓝 0) := by
    have hlim : ∀ᵐ x : SpatialCoordinates d ∂μΓ,
        Tendsto (fun k => (G k x) ^ 2) atTop (𝓝 ((0 : ℝ))) := by
      filter_upwards [hDk_ae] with x hx
      have hc : Tendsto (fun _ : ℕ => Tderiv (vc x)) atTop
          (𝓝 (Tderiv (vc x))) := tendsto_const_nhds
      simpa [G] using (hx.sub hc).pow (2 : ℕ)
    have hbound : ∀ k : ℕ, ∀ᵐ x : SpatialCoordinates d ∂μΓ,
        ‖(G k x) ^ 2‖ ≤ (2 * C) ^ 2 := by
      intro k
      filter_upwards [hGbound k] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (G k x))]
      calc
        G k x ^ 2 = |G k x| ^ 2 := by rw [sq_abs]
        _ ≤ (2 * C) ^ 2 := (sq_le_sq₀ (abs_nonneg (G k x)) (by positivity)).2 hx
    have h := tendsto_integral_of_dominated_convergence (G := ℝ)
      (F := fun k x => (G k x) ^ 2)
      (f := fun _ : SpatialCoordinates d => (0 : ℝ))
      (fun _ : SpatialCoordinates d => (2 * C) ^ 2)
      (fun k => (hGmeas k).pow (2 : ℕ)) (integrable_const ((2 * C) ^ 2)) hbound hlim
    simpa only [integral_zero] using h
  have hPhi : ∀ p r : ℕ, ContDiff ℝ 1 (fun s => Tk p s - Tk r s) := by
    intro p r
    exact ((hTk p).1.sub (hTk r).1).of_le (by norm_num)
  have hPhi_zero : ∀ p r : ℕ, (fun s => Tk p s - Tk r s) 0 = 0 := by
    intro p r
    simp [hTk p |>.2.1, hTk r |>.2.1]
  have hderivPhi : ∀ p r : ℕ, ∀ s : ℝ,
      deriv (fun t => Tk p t - Tk r t) s = Dk p s - Dk r s := by
    intro p r s
    exact (((hTk p).2.2.2.1 s).sub ((hTk r).2.2.2.1 s)).deriv
  have hform_diff_eq : ∀ p r : ℕ,
      E.form (uk p - uk r) (uk p - uk r) =
        ∫ x, (Dk p (vc x) - Dk r (vc x)) ^ 2 ∂μΓ := by
    intro p r
    have hsubmem := E.toClosedForm.domain.sub_mem (huk p) (huk r)
    have hchain := Gamma.chain_rule v hv vc hvc hrep
      (fun s => Tk p s - Tk r s) (hPhi p r) (hPhi_zero p r)
      (uk p - uk r) hsubmem (hdiffrep p r) Set.univ MeasurableSet.univ
    calc
      E.form (uk p - uk r) (uk p - uk r) =
          (Gamma.measure (uk p - uk r) Set.univ).toReal :=
        (Gamma.measure_univ (uk p - uk r) hsubmem).symm
      _ = ∫ x in Set.univ,
          (deriv (fun s => Tk p s - Tk r s) (vc x)) ^ 2 ∂μΓ := by
        simpa [μΓ] using hchain
      _ = ∫ x, (Dk p (vc x) - Dk r (vc x)) ^ 2 ∂μΓ := by
        simp only [Measure.restrict_univ]
        apply integral_congr_ae
        filter_upwards with x
        rw [hderivPhi]
  have hform_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ r ≥ N,
      E.form (uk p - uk r) (uk p - uk r) < ε := by
    intro ε hε
    have hev : ∀ᶠ k : ℕ in atTop,
        ∫ x, (G k x) ^ 2 ∂μΓ < ε / 8 :=
      (tendsto_order.1 hGint_lim).2 (ε / 8) (by positivity)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    refine ⟨N, fun p hp r hr => ?_⟩
    have hRint : Integrable (fun x =>
        2 * (G p x) ^ 2 + 2 * (G r x) ^ 2) μΓ :=
      (hGsq_int p).const_mul 2 |>.add ((hGsq_int r).const_mul 2)
    have hHmeas : AEStronglyMeasurable
        (fun x => (Dk p (vc x) - Dk r (vc x)) ^ 2) μΓ := by
      have hh := ((hGmeas p).sub (hGmeas r)).pow (2 : ℕ)
      convert hh using 1
      funext x
      dsimp [G]
      ring
    have hHint : Integrable (fun x =>
        (Dk p (vc x) - Dk r (vc x)) ^ 2) μΓ := by
      apply hRint.mono hHmeas
      filter_upwards with x
      have hid : Dk p (vc x) - Dk r (vc x) = G p x - G r x := by
        simp [G]
      rw [hid]
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (G p x - G r x))]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
        0 ≤ 2 * (G p x) ^ 2 + 2 * (G r x) ^ 2)]
      nlinarith [sq_nonneg (G p x + G r x)]
    have hineq : ∀ᵐ x : SpatialCoordinates d ∂μΓ,
        (Dk p (vc x) - Dk r (vc x)) ^ 2 ≤
          2 * (G p x) ^ 2 + 2 * (G r x) ^ 2 := by
      filter_upwards with x
      have hid : Dk p (vc x) - Dk r (vc x) = G p x - G r x := by
        simp [G]
      rw [hid]
      nlinarith [sq_nonneg (G p x + G r x)]
    have hint := integral_mono_ae hHint hRint hineq
    have hRval : (∫ x, 2 * (G p x) ^ 2 + 2 * (G r x) ^ 2 ∂μΓ) =
        2 * (∫ x, (G p x) ^ 2 ∂μΓ) + 2 * (∫ x, (G r x) ^ 2 ∂μΓ) := by
      rw [integral_add ((hGsq_int p).const_mul 2) ((hGsq_int r).const_mul 2),
        integral_const_mul, integral_const_mul]
    rw [hform_diff_eq p r]
    calc
      (∫ x, (Dk p (vc x) - Dk r (vc x)) ^ 2 ∂μΓ) ≤
          ∫ x, 2 * (G p x) ^ 2 + 2 * (G r x) ^ 2 ∂μΓ := hint
      _ = 2 * (∫ x, (G p x) ^ 2 ∂μΓ) +
          2 * (∫ x, (G r x) ^ 2 ∂μΓ) := hRval
      _ < ε := by nlinarith [hN p hp, hN r hr]
  have hL2real : Tendsto (fun k : ℕ =>
      (eLpNorm (fun x => Tk k (vc x) - T (vc x)) 2
        (volume.restrict (Q : Set (SpatialCoordinates d)))).toReal)
      atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hL2_lim
  have hukL2 : Tendsto uk atTop
      (𝓝 w) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      ((Metric.tendsto_nhds.1 hL2real) ε hε)
    refine ⟨N, fun k hk => ?_⟩
    rw [Lp.dist_def]
    have haef : (⇑(uk k) - ⇑w =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
        (fun x => Tk k (vc x) - T (vc x))) := by
      filter_upwards [hukrep k, hwrep] with x hxk hxw
      simp only [Pi.sub_apply]
      rw [hxk, hxw]
    rw [eLpNorm_congr_ae haef]
    simpa [Real.dist_eq, abs_of_nonneg ENNReal.toReal_nonneg] using hN k hk
  have hclosed := E.toClosedForm.mem_domain_of_tendsto_of_formCauchy
    uk huk w hukL2 hform_cauchy
  have hw_mem : w ∈ E.toClosedForm.domain := hclosed.1
  have henergy : Tendsto (fun k : ℕ =>
      E.energyNormSq (uk k - w)) atTop (𝓝 0) := hclosed.2
  have hform_zero : Tendsto (fun k : ℕ =>
      E.form (uk k - w) (uk k - w)) atTop (𝓝 0) := by
    refine squeeze_zero (fun k => E.form_nonneg (uk k - w)
      (E.toClosedForm.domain.sub_mem (huk k) hw_mem))
      (fun k => E.form_le_energyNormSq) henergy
  intro B hB
  let μB : Measure (SpatialCoordinates d) := μΓ.restrict B
  haveI : IsFiniteMeasure μB := by
    refine ⟨?_⟩
    change (μΓ.restrict B) Set.univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (measure_mono (subset_univ B))
      (Gamma.measure_univ_lt_top v hv)
  have hDmeasB : ∀ k : ℕ,
      AEStronglyMeasurable (fun x : SpatialCoordinates d => Dk k (vc x)) μB := by
    intro k
    exact ((hTk k).2.2.1.comp hvc.measurable).aestronglyMeasurable
  have hboundB : ∀ k : ℕ, ∀ᵐ x : SpatialCoordinates d ∂μB,
      ‖(Dk k (vc x)) ^ 2‖ ≤ C ^ 2 := by
    intro k
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Dk k (vc x)))]
    calc
      Dk k (vc x) ^ 2 = |Dk k (vc x)| ^ 2 := by rw [sq_abs]
      _ ≤ C ^ 2 := (sq_le_sq₀ (abs_nonneg _) hC).2
        (hTk k |>.2.2.2.2 (vc x))
  have hlimB : ∀ᵐ x : SpatialCoordinates d ∂μB,
      Tendsto (fun k => (Dk k (vc x)) ^ 2) atTop
        (𝓝 ((Tderiv (vc x)) ^ 2)) := by
    filter_upwards [(ae_mono Measure.restrict_le_self) hDk_ae] with x hx
    simpa using hx.pow (2 : ℕ)
  have htarget : Tendsto (fun k : ℕ =>
      ∫ x, (Dk k (vc x)) ^ 2 ∂μB) atTop
        (𝓝 (∫ x, (Tderiv (vc x)) ^ 2 ∂μB)) := by
    have h := tendsto_integral_of_dominated_convergence (G := ℝ)
      (F := fun k x => (Dk k (vc x)) ^ 2)
      (f := fun x => (Tderiv (vc x)) ^ 2)
      (fun _ : SpatialCoordinates d => C ^ 2)
      (fun k => (hDmeasB k).pow (2 : ℕ)) (integrable_const (C ^ 2)) hboundB hlimB
    exact h
  have hchain_k : ∀ k : ℕ,
      (Gamma.measure (uk k) B).toReal =
        ∫ x in B, (Dk k (vc x)) ^ 2 ∂μΓ := by
    intro k
    have hchain := Gamma.chain_rule v hv vc hvc hrep (Tk k)
      ((hTk k).1.of_le (by norm_num)) (hTk k |>.2.1)
      (uk k) (huk k) (hukrep k) B hB
    have hderivTk : ∀ x : SpatialCoordinates d,
        deriv (Tk k) (vc x) = Dk k (vc x) := fun x =>
      ((hTk k).2.2.2.1 (vc x)).deriv
    simpa only [hderivTk] using hchain
  have hmass_uk_tendsto : Tendsto (fun k : ℕ =>
      (Gamma.measure (uk k) B).toReal) atTop
        (𝓝 (∫ x in B, (Tderiv (vc x)) ^ 2 ∂μΓ)) := by
    have hh := htarget.congr' (Filter.Eventually.of_forall fun k => by
      simpa [μB] using (hchain_k k).symm)
    simpa [μB] using hh
  have hmeasure_form : ∀ k : ℕ,
      (Gamma.measure (uk k - w) B).toReal ≤
        E.form (uk k - w) (uk k - w) := by
    intro k
    have hzmem := E.toClosedForm.domain.sub_mem (huk k) hw_mem
    have hmono : Gamma.measure (uk k - w) B ≤
        Gamma.measure (uk k - w) Set.univ := measure_mono (subset_univ B)
    calc
      (Gamma.measure (uk k - w) B).toReal ≤
          (Gamma.measure (uk k - w) Set.univ).toReal :=
        ENNReal.toReal_mono (ne_of_lt (Gamma.measure_univ_lt_top _ hzmem)) hmono
      _ = E.form (uk k - w) (uk k - w) := Gamma.measure_univ _ hzmem
  have hcross_eq : ∀ k : ℕ,
      Gamma.cross (uk k) (uk k) B =
        Gamma.cross w w B + Gamma.cross w (uk k - w) B +
          Gamma.cross (uk k - w) w B + Gamma.cross (uk k - w) (uk k - w) B := by
    intro k
    let z : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))) := uk k - w
    have hzmem : z ∈ E.toClosedForm.domain := by
      exact E.toClosedForm.domain.sub_mem (huk k) hw_mem
    have hsum : w + z ∈ E.toClosedForm.domain :=
      E.toClosedForm.domain.add_mem hw hzmem
    have hdecomp : uk k = w + z := by
      dsimp [z]
      abel
    change Gamma.cross (uk k) (uk k) B =
      Gamma.cross w w B + Gamma.cross w z B +
        Gamma.cross z w B + Gamma.cross z z B
    have h1 := Gamma.cross_add_right (w + z) hsum w hw z hzmem
    have h2 := Gamma.cross_symm (w + z) hsum w hw
    have h3 := Gamma.cross_add_right w hw w hw z hzmem
    have h4 := Gamma.cross_symm (w + z) hsum z hzmem
    have h5 := Gamma.cross_add_right z hzmem w hw z hzmem
    rw [hdecomp]
    calc
      Gamma.cross (w + z) (w + z) B =
          (Gamma.cross (w + z) w + Gamma.cross (w + z) z) B := by
            exact congrArg (fun ν : SignedMeasure (SpatialCoordinates d) => ν B) h1
      _ = (Gamma.cross w (w + z) + Gamma.cross z (w + z)) B := by
            rw [h2, h4]
      _ = (Gamma.cross w w + Gamma.cross w z +
          (Gamma.cross z w + Gamma.cross z z)) B := by
            rw [h3, h5]
      _ = Gamma.cross w w B + Gamma.cross w z B +
          Gamma.cross z w B + Gamma.cross z z B := by
            rw [VectorMeasure.add_apply, VectorMeasure.add_apply, VectorMeasure.add_apply]
            ring
  have hzz_abs : ∀ k : ℕ,
      |Gamma.cross (uk k - w) (uk k - w) B| ≤
        E.form (uk k - w) (uk k - w) := by
    intro k
    have hzmem := E.toClosedForm.domain.sub_mem (huk k) hw_mem
    calc
      |Gamma.cross (uk k - w) (uk k - w) B| =
          (Gamma.measure (uk k - w) B).toReal := by
            rw [Gamma.cross_self (uk k - w) hzmem B hB]
            exact abs_of_nonneg ENNReal.toReal_nonneg
      _ ≤ (Gamma.measure (uk k - w) Set.univ).toReal := by
        exact ENNReal.toReal_mono (ne_of_lt (Gamma.measure_univ_lt_top _ hzmem))
          (measure_mono (subset_univ B))
      _ = E.form (uk k - w) (uk k - w) := Gamma.measure_univ _ hzmem
  have hcross_wz_abs : ∀ k : ℕ,
      |Gamma.cross w (uk k - w) B| ≤
        Real.sqrt ((Gamma.measure w B).toReal) *
          Real.sqrt (E.form (uk k - w) (uk k - w)) := by
    intro k
    have hzmem := E.toClosedForm.domain.sub_mem (huk k) hw_mem
    calc
      |Gamma.cross w (uk k - w) B| ≤
          Real.sqrt ((Gamma.measure w B).toReal) *
            Real.sqrt ((Gamma.measure (uk k - w) B).toReal) :=
        Gamma.abs_cross_le w hw (uk k - w) hzmem B hB
      _ ≤ Real.sqrt ((Gamma.measure w B).toReal) *
          Real.sqrt (E.form (uk k - w) (uk k - w)) := by
        exact mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (hmeasure_form k)) (Real.sqrt_nonneg _)
  have hcross_wz_zero : Tendsto (fun k : ℕ =>
      Gamma.cross w (uk k - w) B) atTop (𝓝 0) := by
    have hsqrt : Tendsto (fun k : ℕ =>
        Real.sqrt (E.form (uk k - w) (uk k - w))) atTop (𝓝 0) := by
      simpa using (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hform_zero
    have hbound : Tendsto (fun k : ℕ =>
        Real.sqrt ((Gamma.measure w B).toReal) *
          Real.sqrt (E.form (uk k - w) (uk k - w))) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hsqrt)
    have habs : Tendsto (fun k : ℕ =>
        |Gamma.cross w (uk k - w) B|) atTop (𝓝 0) :=
      squeeze_zero (fun k => abs_nonneg _)
        hcross_wz_abs hbound
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [(Metric.tendsto_nhds.1 habs) ε hε] with k hk
    simpa [Real.dist_eq, abs_abs] using hk
  have hcross_zw_zero : Tendsto (fun k : ℕ =>
      Gamma.cross (uk k - w) w B) atTop (𝓝 0) := by
    have heq : ∀ k : ℕ,
        Gamma.cross (uk k - w) w B = Gamma.cross w (uk k - w) B := by
      intro k
      exact congrArg (fun ν : SignedMeasure (SpatialCoordinates d) => ν B)
        (Gamma.cross_symm (uk k - w)
          (E.toClosedForm.domain.sub_mem (huk k) hw_mem) w hw)
    exact hcross_wz_zero.congr' (Filter.Eventually.of_forall fun k => (heq k).symm)
  have hzz_zero : Tendsto (fun k : ℕ =>
      Gamma.cross (uk k - w) (uk k - w) B) atTop (𝓝 0) := by
    have habs : Tendsto (fun k : ℕ =>
        |Gamma.cross (uk k - w) (uk k - w) B|) atTop (𝓝 0) :=
      squeeze_zero (fun k => abs_nonneg _)
        hzz_abs hform_zero
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [(Metric.tendsto_nhds.1 habs) ε hε] with k hk
    simpa [Real.dist_eq, abs_abs] using hk
  have hmass_eq : ∀ k : ℕ,
      (Gamma.measure (uk k) B).toReal - (Gamma.measure w B).toReal =
        Gamma.cross w (uk k - w) B + Gamma.cross (uk k - w) w B +
          Gamma.cross (uk k - w) (uk k - w) B := by
    intro k
    rw [← Gamma.cross_self (uk k) (huk k) B hB,
      ← Gamma.cross_self w hw B hB, hcross_eq k]
    ring
  have hmass_diff_zero : Tendsto (fun k : ℕ =>
      (Gamma.measure (uk k) B).toReal - (Gamma.measure w B).toReal) atTop (𝓝 0) := by
    have hh := (hcross_wz_zero.add hcross_zw_zero).add hzz_zero
    have hhc := hh.congr' (Filter.Eventually.of_forall fun k => (hmass_eq k).symm)
    simpa only [zero_add, add_zero] using hhc
  have hmass_w_tendsto : Tendsto (fun k : ℕ =>
      (Gamma.measure (uk k) B).toReal) atTop (𝓝 (Gamma.measure w B).toReal) := by
    have hh := hmass_diff_zero.add
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (Gamma.measure w B).toReal)
        atTop (𝓝 (Gamma.measure w B).toReal))
    simpa [sub_add_cancel] using hh
  exact tendsto_nhds_unique hmass_w_tendsto hmass_uk_tendsto

end Paper
