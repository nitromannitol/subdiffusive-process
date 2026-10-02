import SubdiffusiveProcess.Paper.lem_20_product_h10
import SubdiffusiveProcess.Geometry.Cube
import SubdiffusiveProcess.Sobolev.ResponseSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology

namespace Paper

open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedSubunitKilledLower

theorem aux_lem_20_product_leibniz_product
    {d : ℕ} {W : Set (SpatialCoordinates d)}
    (hW : IsOpenBoundedConvexDomain W) (u chi : H10Function W)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hu : ∀ᵐ x ∂(volume.restrict W), |u.toH1Function.toFun x| ≤ A)
    (hchi : ∀ n x, |chi.approx n x| ≤ B)
    (hchival : ∀ x, |chi.toH1Function.toFun x| ≤ B) :
    ∃ p : H10Function W,
      (p.toH1Function.toFun = fun x => chi.toH1Function.toFun x * u.toH1Function.toFun x) ∧
      p.toH1Function.grad =
        fun x i => chi.toH1Function.toFun x * u.toH1Function.grad x i +
          u.toH1Function.toFun x * chi.toH1Function.grad x i := by
  letI : IsFiniteMeasure (volume.restrict W) := hW.isFiniteMeasure_restrict_volume
  let μ : Measure (SpatialCoordinates d) := volume.restrict W
  have huTop : MemLp u.toH1Function.toFun ∞ μ := by
    exact MemLp.of_bound u.toH1Function.memL2.1 A hu
  have hchiTop : MemLp chi.toH1Function.toFun ∞ μ := by
    exact MemLp.of_bound chi.toH1Function.memL2.1 B
      (Filter.Eventually.of_forall hchival)
  have hprod : MemLp (fun x => chi.toH1Function.toFun x * u.toH1Function.toFun x) 2 μ := by
    simpa [μ, mul_comm] using hchiTop.mul' u.toH1Function.memL2
  have hprodgrad (i : Fin d) :
      MemLp (fun x => chi.toH1Function.toFun x * u.toH1Function.grad x i +
        u.toH1Function.toFun x * chi.toH1Function.grad x i) 2 μ := by
    simpa only [mul_comm] using
      ((u.toH1Function.gradMemL2 i).mul' (r := 2) hchiTop).add
        (huTop.mul' (r := 2) (chi.toH1Function.gradMemL2 i))
  obtain ⟨σ, hσmono, hσae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num)
      (fun n => (chi.approx_smooth n).continuous.aestronglyMeasurable)
      chi.toH1Function.memL2.1 chi.tendsto_approx).exists_seq_tendsto_ae
  have happroxMem (n : ℕ) : MemLp (chi.approx (σ n)) 2 μ :=
    ((chi.approx_smooth (σ n)).continuous.memLp_of_hasCompactSupport
      (chi.approx_hasCompactSupport (σ n))).restrict W
  have hprodVal : Tendsto
      (fun n => eLpNorm
        (fun x => (chi.approx (σ n) x * u.toH1Function.toFun x) -
          chi.toH1Function.toFun x * u.toH1Function.toFun x) 2 μ)
      atTop (𝓝 0) := by
    have h :=
      tendsto_eLpNorm_mul_of_memLp_top huTop chi.toH1Function.memL2
        (fun n => chi.approx (σ n)) happroxMem
        (chi.tendsto_approx.comp hσmono.tendsto_atTop)
    simpa only [mul_comm] using h
  have hprodGrad (i : Fin d) : Tendsto
      (fun n => eLpNorm
        (fun x =>
          ((chi.approx (σ n) x) * u.toH1Function.grad x i +
            u.toH1Function.toFun x *
              (fderiv ℝ (chi.approx (σ n)) x) (basisVec i)) -
          (chi.toH1Function.toFun x * u.toH1Function.grad x i +
            u.toH1Function.toFun x * chi.toH1Function.grad x i)) 2 μ)
      atTop (𝓝 0) := by
    let TA : ℕ → SpatialCoordinates d → ℝ := fun n x =>
      (chi.approx (σ n) x - chi.toH1Function.toFun x) * u.toH1Function.grad x i
    let TB : ℕ → SpatialCoordinates d → ℝ := fun n x =>
      u.toH1Function.toFun x *
        ((fderiv ℝ (chi.approx (σ n)) x) (basisVec i) -
          chi.toH1Function.grad x i)
    have hmeasA (n : ℕ) : AEStronglyMeasurable (TA n) μ := by
      exact ((chi.approx_smooth (σ n)).continuous.aestronglyMeasurable.sub
        chi.toH1Function.memL2.1).mul (u.toH1Function.gradMemL2 i).1
    have hmeasB (n : ℕ) : AEStronglyMeasurable (TB n) μ := by
      exact huTop.1.mul
        ((((chi.approx_smooth (σ n)).continuous_fderiv (by norm_num)).clm_apply
          continuous_const).aestronglyMeasurable.sub
          (chi.toH1Function.gradMemL2 i).1)
    have hAconv : Tendsto (fun n => eLpNorm (TA n) 2 μ) atTop (𝓝 0) := by
      have hdom := ((u.toH1Function.gradMemL2 i).const_mul (2 * B)).norm
      have hboundA (n : ℕ) : ∀ᵐ x ∂μ, ‖TA n x‖ ≤
          ‖(2 * B) * u.toH1Function.grad x i‖ := by
        filter_upwards with x
        simp only [TA, norm_mul, Real.norm_eq_abs, abs_of_nonneg hB,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        calc
          |chi.approx (σ n) x - chi.toH1Function.toFun x| ≤
              |chi.approx (σ n) x| + |chi.toH1Function.toFun x| := abs_sub _ _
          _ ≤ B + B := add_le_add (hchi (σ n) x) (hchival x)
          _ = 2 * B := by ring
      have hlimA : ∀ᵐ x ∂μ, Tendsto (fun n => TA n x) atTop (𝓝 0) := by
        filter_upwards [hσae] with x hx
        have h := (hx.sub (tendsto_const_nhds (x := chi.toH1Function.toFun x))).mul_const
          (u.toH1Function.grad x i)
        simpa only [TA, sub_self, zero_mul] using h
      simpa using tendsto_eLpNorm_two_of_tendsto_ae_of_dominated hmeasA
        (memLp_const (0 : ℝ)) hdom hboundA hlimA
    have hBconv : Tendsto (fun n => eLpNorm (TB n) 2 μ) atTop (𝓝 0) := by
      have h :=
        tendsto_eLpNorm_mul_of_memLp_top huTop (chi.toH1Function.gradMemL2 i)
          (fun n x => (fderiv ℝ (chi.approx (σ n)) x) (basisVec i))
          (fun n => (((chi.approx_smooth (σ n)).continuous_fderiv (by norm_num)).clm_apply
            continuous_const).memLp_of_hasCompactSupport
              ((chi.approx_hasCompactSupport (σ n)).fderiv_apply (𝕜 := ℝ) (basisVec i)) |>.restrict W)
          ((chi.tendsto_approx_grad i).comp hσmono.tendsto_atTop)
      simpa only [TB, Pi.sub_apply, mul_sub] using h
    have hsum : Tendsto (fun n => eLpNorm (TA n) 2 μ + eLpNorm (TB n) 2 μ)
        atTop (𝓝 0) := by simpa using hAconv.add hBconv
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => zero_le _) (fun n => ?_)
    calc
      _ = eLpNorm (fun x => TA n x + TB n x) 2 μ := by
        apply eLpNorm_congr_ae
        filter_upwards with x
        dsimp only [TA, TB]
        ring
      _ ≤ _ := eLpNorm_add_le (hmeasA n) (hmeasB n) (by norm_num)

  let P : ℕ → H10Function W := fun n =>
    u.mulContDiffHasCompactSupport (chi.approx_smooth (σ n))
      (chi.approx_hasCompactSupport (σ n))
  have hPval (n : ℕ) :
      (P n).toH1Function.toFun =
        fun x => chi.approx (σ n) x * u.toH1Function.toFun x := by
    simpa [P] using H10Function.mulContDiffHasCompactSupport_toFun u
      (chi.approx_smooth (σ n)) (chi.approx_hasCompactSupport (σ n))
  have hPgrad (n : ℕ) :
      (P n).toH1Function.grad =
        fun x i => chi.approx (σ n) x * u.toH1Function.grad x i +
          u.toH1Function.toFun x *
            (fderiv ℝ (chi.approx (σ n)) x) (basisVec i) := by
    simpa [P, H10Function.mulContDiffHasCompactSupport,
      H1Function.mulContDiffHasCompactSupport_grad]
  let ε : ℕ → ℝ≥0∞ := fun n => (↑(n + 1))⁻¹
  have hεpos (n : ℕ) : 0 < ε n := by
    simp only [ε]
    exact ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top (n + 1))
  have hεtend : Tendsto ε atTop (𝓝 0) := by
    convert (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)) using 1 <;>
      simp [ε, Nat.cast_add, Nat.cast_one]
  have hchoose : ∀ n : ℕ, ∃ k : ℕ,
      eLpNorm (fun x => (P n).approx k x - (P n).toH1Function.toFun x) 2 μ < ε n ∧
      ∀ i : Fin d, eLpNorm
        (fun x => (fderiv ℝ ((P n).approx k) x) (basisVec i) -
          (P n).toH1Function.grad x i) 2 μ < ε n := by
    intro n
    have h1 : ∀ᶠ k : ℕ in atTop,
        eLpNorm (fun x => (P n).approx k x - (P n).toH1Function.toFun x) 2 μ < ε n :=
      (P n).tendsto_approx.eventually_lt_const (hεpos n)
    have h2 : ∀ i : Fin d, ∀ᶠ k : ℕ in atTop,
        eLpNorm (fun x => (fderiv ℝ ((P n).approx k) x) (basisVec i) -
          (P n).toH1Function.grad x i) 2 μ < ε n := by
      intro i
      exact (P n).tendsto_approx_grad i |>.eventually_lt_const (hεpos n)
    exact (h1.and (Filter.eventually_all.2 h2)).exists
  choose k hk using hchoose
  let f : ℕ → SpatialCoordinates d → ℝ := fun n => (P n).approx (k n)
  have hvalueBound (n : ℕ) :
      eLpNorm (fun x => f n x -
        chi.toH1Function.toFun x * u.toH1Function.toFun x) 2 μ ≤
        ε n + eLpNorm (fun x => (P n).toH1Function.toFun x -
          chi.toH1Function.toFun x * u.toH1Function.toFun x) 2 μ := by
    have hfa : AEStronglyMeasurable (fun x => f n x - (P n).toH1Function.toFun x) μ :=
      ((P n).approx_smooth (k n)).continuous.aestronglyMeasurable.sub
        (P n).toH1Function.memL2.1
    have hpa : AEStronglyMeasurable
        (fun x => (P n).toH1Function.toFun x -
          chi.toH1Function.toFun x * u.toH1Function.toFun x) μ :=
      (P n).toH1Function.memL2.1.sub hprod.aestronglyMeasurable
    calc
      _ = eLpNorm (fun x => (f n x - (P n).toH1Function.toFun x) +
          ((P n).toH1Function.toFun x -
            chi.toH1Function.toFun x * u.toH1Function.toFun x)) 2 μ := by
        apply eLpNorm_congr_ae
        exact Filter.Eventually.of_forall (fun x => by ring)
      _ ≤ eLpNorm (fun x => f n x - (P n).toH1Function.toFun x) 2 μ +
          eLpNorm (fun x => (P n).toH1Function.toFun x -
            chi.toH1Function.toFun x * u.toH1Function.toFun x) 2 μ :=
        eLpNorm_add_le hfa hpa (by norm_num)
      _ ≤ _ := add_le_add (le_of_lt (by simpa [f] using (hk n).1)) (le_rfl)
  have hvalue : Tendsto
      (fun n => eLpNorm (fun x => f n x -
        chi.toH1Function.toFun x * u.toH1Function.toFun x) 2 μ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa [P, H10Function.mulContDiffHasCompactSupport_toFun] using
        hεtend.add hprodVal) (fun _ => zero_le _) hvalueBound
  have hgradBound (i : Fin d) (n : ℕ) :
      eLpNorm (fun x => (fderiv ℝ (f n) x) (basisVec i) -
        (chi.toH1Function.toFun x * u.toH1Function.grad x i +
          u.toH1Function.toFun x * chi.toH1Function.grad x i)) 2 μ ≤
        ε n + eLpNorm (fun x => (P n).toH1Function.grad x i -
          (chi.toH1Function.toFun x * u.toH1Function.grad x i +
            u.toH1Function.toFun x * chi.toH1Function.grad x i)) 2 μ := by
    have hfa : AEStronglyMeasurable
        (fun x => (fderiv ℝ (f n) x) (basisVec i) -
          (P n).toH1Function.grad x i) μ :=
      (((P n).approx_smooth (k n)).continuous_fderiv (by norm_num)).clm_apply
        continuous_const |>.aestronglyMeasurable.sub
          ((P n).toH1Function.gradMemL2 i).1
    have hpa : AEStronglyMeasurable
        (fun x => (P n).toH1Function.grad x i -
          (chi.toH1Function.toFun x * u.toH1Function.grad x i +
            u.toH1Function.toFun x * chi.toH1Function.grad x i)) μ :=
      (P n).toH1Function.gradMemL2 i |>.1.sub (hprodgrad i).aestronglyMeasurable
    calc
      _ = eLpNorm (fun x => ((fderiv ℝ (f n) x) (basisVec i) -
          (P n).toH1Function.grad x i) +
          ((P n).toH1Function.grad x i -
            (chi.toH1Function.toFun x * u.toH1Function.grad x i +
              u.toH1Function.toFun x * chi.toH1Function.grad x i))) 2 μ := by
        apply eLpNorm_congr_ae
        exact Filter.Eventually.of_forall (fun x => by ring)
      _ ≤ eLpNorm (fun x => (fderiv ℝ (f n) x) (basisVec i) -
          (P n).toH1Function.grad x i) 2 μ +
          eLpNorm (fun x => (P n).toH1Function.grad x i -
            (chi.toH1Function.toFun x * u.toH1Function.grad x i +
              u.toH1Function.toFun x * chi.toH1Function.grad x i)) 2 μ :=
        eLpNorm_add_le hfa hpa (by norm_num)
      _ ≤ _ := add_le_add (le_of_lt (by simpa [f] using (hk n).2 i)) (le_rfl)
  have hgrad (i : Fin d) : Tendsto
      (fun n => eLpNorm (fun x => (fderiv ℝ (f n) x) (basisVec i) -
        (chi.toH1Function.toFun x * u.toH1Function.grad x i +
          u.toH1Function.toFun x * chi.toH1Function.grad x i)) 2 μ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [hPgrad, add_zero, zero_add] using
        hεtend.add (hprodGrad i)) (fun _ => zero_le _) (hgradBound i)
  let pair : SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedSubunitKilledLower.DirichletSobolevPair
      W (fun x => chi.toH1Function.toFun x * u.toH1Function.toFun x)
      (fun x i => chi.toH1Function.toFun x * u.toH1Function.grad x i +
        u.toH1Function.toFun x * chi.toH1Function.grad x i) := by
    refine ⟨hprod, fun i => hprodgrad i, f, ?_, ?_, ?_, hvalue, hgrad⟩
    · intro n
      exact (P n).approx_smooth (k n)
    · intro n
      exact (P n).approx_hasCompactSupport (k n)
    · intro n
      exact (P n).approx_support_subset (k n)
  obtain ⟨p, hp, hpg⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedSubunitKilledLower.DirichletSobolevPair.exists_h10
      pair
  exact ⟨p, hp, hpg⟩



theorem lem_20_product_leibniz
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (hS : S.space = killedSobolevGraph (centeredCube z R hR))
    (u chi : S.space) (uc : SpatialCoordinates d → ℝ)
    (huc : (u.val.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] uc)
    (hcontinuous : ContinuousOn uc
      (closure (centeredCube z R hR : Set (SpatialCoordinates d))))
    (hchi : ∀ᵐ x ∂(volume.restrict
        (centeredCube z R hR : Set (SpatialCoordinates d))),
      0 ≤ (chi.val.1 : SpatialCoordinates d → ℝ) x ∧
        (chi.val.1 : SpatialCoordinates d → ℝ) x ≤ 1)
    (prod : S.space)
    (hprod : (prod.val.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
        (fun x => uc x * (1 - (chi.val.1 : SpatialCoordinates d → ℝ) x))) :
    ∀ i : Fin d, (prod.val.2 i : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
        (fun x => (1 - (chi.val.1 : SpatialCoordinates d → ℝ) x) *
          (u.val.2 i : SpatialCoordinates d → ℝ) x -
            uc x * (chi.val.2 i : SpatialCoordinates d → ℝ) x) := by
  let W : Set (SpatialCoordinates d) := centeredCube z R hR
  have hW : IsOpenBoundedConvexDomain W := by
    simpa [W, centeredCube] using
      (isOpenBoundedConvexDomain_ball z (half_pos hR))
  have huK : (u.val : SobolevData (centeredCube z R hR)) ∈
      killedSobolevGraph (centeredCube z R hR) := by
    rw [← hS]
    exact u.property
  have hchiK : (chi.val : SobolevData (centeredCube z R hR)) ∈
      killedSobolevGraph (centeredCube z R hR) := by
    rw [← hS]
    exact chi.property
  obtain ⟨uH, huHval, huHgrad⟩ := aux_lem_20_product_h10_killed_to_h10 huK
  obtain ⟨chiH, hchiHval, hchiHgrad⟩ := aux_lem_20_product_h10_killed_to_h10 hchiK
  have hWmeas : MeasurableSet W := by
    simpa [W] using (centeredCube z R hR).isOpen.measurableSet
  obtain ⟨C, hC⟩ :=
    (centeredCube_isBounded z hR).isCompact_closure.exists_bound_of_continuousOn
      hcontinuous.norm
  let A : ℝ := max C 0
  have hA : 0 ≤ A := le_max_right C 0
  have huBound : ∀ᵐ x ∂(volume.restrict W),
      |uH.toH1Function.toFun x| ≤ A := by
    filter_upwards [huc, ae_restrict_mem hWmeas] with x hx hxW
    rw [huHval, hx]
    have hcx := hC x (subset_closure hxW)
    have habs : |uc x| ≤ C := by simpa [Real.norm_eq_abs] using hcx
    exact habs.trans (le_max_left C 0)
  have hchiHBound : ∀ᵐ x ∂(volume.restrict W),
      |chiH.toH1Function.toFun x| ≤ 1 := by
    filter_upwards [hchi] with x hx
    rw [hchiHval, abs_of_nonneg hx.1]
    exact hx.2
  let b : ContDiffBump (0 : ℝ) :=
    ⟨2, 3, by norm_num, by norm_num⟩
  let G : ℝ → ℝ := fun t => b t * t
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := by
    simpa [G] using b.contDiff.mul (contDiff_id : ContDiff ℝ (⊤ : ℕ∞) id)
  have hG0 : G 0 = 0 := by simp [G]
  have hGcomp : HasCompactSupport G := by
    simpa [G] using b.hasCompactSupport.mul_right
  obtain ⟨B₀, hB₀⟩ := hGcomp.exists_bound_of_continuous hG.continuous
  let B : ℝ := max B₀ 0
  have hB : 0 ≤ B := le_max_right B₀ 0
  have hbound : ∀ t, |G t| ≤ B := by
    intro t
    have ht : |G t| ≤ B₀ := by
      simpa only [Real.norm_eq_abs] using hB₀ t
    exact ht.trans (le_max_left B₀ 0)
  have hGone {t : ℝ} (ht : |t| ≤ 1) : G t = t := by
    have hb : b t = 1 := b.one_of_mem_closedBall (by
      rw [mem_closedBall_zero_iff]
      exact (by simpa [Real.norm_eq_abs] using ht.trans (by norm_num : (1 : ℝ) ≤ 2)))
    simp [G, hb]
  obtain ⟨D, hD⟩ :=
    (by
      have hGderivcomp : HasCompactSupport (deriv G) := by
        simpa only [fderiv_deriv] using hGcomp.fderiv_apply ℝ (1 : ℝ)
      exact hGderivcomp.exists_bound_of_continuous
        (hG.continuous_deriv (by norm_num)))
  let M : ℝ := max D 0
  have hM : 0 ≤ M := le_max_right D 0
  have hderiv : ∀ t, |deriv G t| ≤ M := by
    intro t
    have ht : |deriv G t| ≤ D := by
      simpa only [Real.norm_eq_abs] using hD t
    exact ht.trans (le_max_left D 0)
  have hGone0 {t : ℝ} (ht : |t| ≤ 1) : G t = t := hGone ht
  obtain ⟨chiB, hchiBval, hchiBgrad, hchiBapprox⟩ :=
    aux_lem_20_product_h10_bounded_comp hW chiH (by norm_num)
      hchiHBound hG hG0 hM hderiv hbound
  have hchiBpoint : ∀ x, |chiB.toH1Function.toFun x| ≤ B := by
    intro x
    rw [hchiBval]
    exact hbound _
  have hchiBae : chiB.toH1Function.toFun =ᵐ[volume.restrict W]
      (chi.val.1 : SpatialCoordinates d → ℝ) := by
    filter_upwards [hchi] with x hx
    rw [hchiBval, hchiHval]
    apply hGone0
    rw [abs_of_nonneg hx.1]
    exact hx.2
  obtain ⟨pchi, hpchi, hpchigrad⟩ :=
    aux_lem_20_product_leibniz_product hW uH chiB hA hB huBound
      hchiBapprox hchiBpoint
  let pfinal : H10Function W := uH - pchi
  have hpfinal : pfinal.toH1Function.toFun = fun x =>
      uH.toH1Function.toFun x - pchi.toH1Function.toFun x := by
    change (uH.toH1Function - pchi.toH1Function).toFun = _
    rw [H1Function.sub_toFun]
  have hpfinalgrad : pfinal.toH1Function.grad = fun x i =>
      uH.toH1Function.grad x i - pchi.toH1Function.grad x i := by
    change (uH.toH1Function - pchi.toH1Function).grad = _
    rw [H1Function.sub_grad]
    funext x i
    rfl
  obtain ⟨q, hqval, hqgrad⟩ :=
    SubdiffusiveProcess.Lane4.exists_killedSobolevGraph_of_nativeH10 pfinal
  have hqweak : (q.val : SobolevData (centeredCube z R hR)) ∈
      weakSobolevGraph (centeredCube z R hR) :=
    killedSobolevGraph_le_weakSobolevGraph q.property
  have hprodweak : (prod.val : SobolevData (centeredCube z R hR)) ∈
      weakSobolevGraph (centeredCube z R hR) :=
    S.le_weak prod.property
  have hqvalue : (q.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict W]
      (fun x => uc x * (1 - (chi.val.1 : SpatialCoordinates d → ℝ) x)) := by
    filter_upwards [hqval, hchiBae, huc] with x hq hcb hu
    calc
      (q.val.1 : SpatialCoordinates d → ℝ) x = pfinal.toH1Function.toFun x := hq
      _ = uH.toH1Function.toFun x - pchi.toH1Function.toFun x := by rw [hpfinal]
      _ = uH.toH1Function.toFun x - chiB.toH1Function.toFun x *
          uH.toH1Function.toFun x := by rw [hpchi]
      _ = (u.val.1 : SpatialCoordinates d → ℝ) x -
          (chi.val.1 : SpatialCoordinates d → ℝ) x *
            (u.val.1 : SpatialCoordinates d → ℝ) x := by
        rw [huHval, hcb]
      _ = uc x * (1 - (chi.val.1 : SpatialCoordinates d → ℝ) x) := by
        rw [hu]
        ring
  obtain ⟨qB, hqBval, hqBgrad⟩ :=
    SubdiffusiveProcess.Lane4.exists_killedSobolevGraph_of_nativeH10 chiB
  obtain ⟨qH, hqHval, hqHgrad⟩ :=
    SubdiffusiveProcess.Lane4.exists_killedSobolevGraph_of_nativeH10 chiH
  have hqBvalH : (qB.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict W]
      (qH.val.1 : SpatialCoordinates d → ℝ) := by
    filter_upwards [hqBval, hchiBae, hqHval] with x hB hcb hH
    calc
      (qB.val.1 : SpatialCoordinates d → ℝ) x = chiB.toH1Function.toFun x := hB
      _ = (chi.val.1 : SpatialCoordinates d → ℝ) x := hcb
      _ = chiH.toH1Function.toFun x := by rw [hchiHval]
      _ = (qH.val.1 : SpatialCoordinates d → ℝ) x := hH.symm
  have hqBvalLp : qB.val.1 = qH.val.1 := by
    apply Lp.ext
    exact hqBvalH
  have hqBweak : (qB.val : SobolevData (centeredCube z R hR)) ∈
      weakSobolevGraph (centeredCube z R hR) :=
    killedSobolevGraph_le_weakSobolevGraph qB.property
  have hqHweak : (qH.val : SobolevData (centeredCube z R hR)) ∈
      weakSobolevGraph (centeredCube z R hR) :=
    killedSobolevGraph_le_weakSobolevGraph qH.property
  have hqHweak' : (qB.val.1, qH.val.2) ∈
      weakSobolevGraph (centeredCube z R hR) := by
    rw [hqBvalLp]
    exact hqHweak
  have hqBgradEq : qB.val.2 = qH.val.2 :=
    weakSobolevGraph_gradient_unique hqBweak hqHweak'
  have hchiBgradAe (i : Fin d) :
      (fun x => chiB.toH1Function.grad x i) =ᵐ[volume.restrict W]
        (fun x => chiH.toH1Function.grad x i) := by
    filter_upwards [hqBgrad i, hqHgrad i] with x hBgrad hHgrad
    rw [← hBgrad, ← hHgrad]
    have hi := congrFun hqBgradEq i
    rw [hi]
  have hqgradFormula (i : Fin d) :
      (q.val.2 i : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict W]
        (fun x => (1 - (chi.val.1 : SpatialCoordinates d → ℝ) x) *
          (u.val.2 i : SpatialCoordinates d → ℝ) x -
            uc x * (chi.val.2 i : SpatialCoordinates d → ℝ) x) := by
    filter_upwards [hqgrad i, hchiBae, hchiBgradAe i, huc] with x hq hcb hcbg hu
    rw [hq]
    change pfinal.toH1Function.grad x i = _
    rw [hpfinalgrad, hpchigrad]
    change uH.toH1Function.grad x i -
      (chiB.toH1Function.toFun x * uH.toH1Function.grad x i +
        uH.toH1Function.toFun x * chiB.toH1Function.grad x i) = _
    rw [hcb, huHval, huHgrad, hcbg, hchiHgrad]
    rw [hu]
    ring
  have hprodqval : (prod.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict W]
      (q.val.1 : SpatialCoordinates d → ℝ) := hprod.trans hqvalue.symm
  have hprodqvalLp : prod.val.1 = q.val.1 := by
    apply Lp.ext
    exact hprodqval
  have hqweak' : (prod.val.1, q.val.2) ∈
      weakSobolevGraph (centeredCube z R hR) := by
    rw [hprodqvalLp]
    exact hqweak
  have hgradEq : prod.val.2 = q.val.2 :=
    weakSobolevGraph_gradient_unique hprodweak hqweak'
  intro i
  have hi : prod.val.2 i = q.val.2 i := congrFun hgradEq i
  have hiae : (prod.val.2 i : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict W]
      (q.val.2 i : SpatialCoordinates d → ℝ) := by
    rw [hi]
  exact hiae.trans (hqgradFormula i)

end Paper

