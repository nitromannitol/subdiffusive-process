module

public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Sobolev.ResponseSpace
public import SubdiffusiveProcess.Sobolev.ReflectionGraph
public import SubdiffusiveProcess.Lane4.Bridge
public import Homogenization.Sobolev.Truncation.H10Limit
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.MoserBoundedComposition
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedSubunitKilledLowerSobolevPair
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedSubunitKilledLowerSobolevMultiplier
public import Mathlib.Analysis.Calculus.BumpFunction.Basic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology

namespace Paper

open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedSubunitKilledLower

theorem aux_lem_20_product_h10_killed_to_h10
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)} {w : SobolevData Ω}
    (hw : w ∈ killedSobolevGraph Ω) :
    ∃ v : H10Function (Ω : Set (SpatialCoordinates d)),
      v.toH1Function.toFun = (w.1 : SpatialCoordinates d → ℝ) ∧
      v.toH1Function.grad =
        (fun x i => (w.2 i : SpatialCoordinates d → ℝ) x) := by
  change w ∈ (killedSobolevGraph Ω : Set (SobolevData Ω)) at hw
  rw [killedSobolevGraph_coe_eq_closure] at hw
  have hchoose : ∀ n : ℕ, ∃ b ∈ Set.range (smoothSobolevData (Ω := Ω)),
      dist w b < 1 / ((n : ℝ) + 1) := by
    intro n
    exact (Metric.mem_closure_iff.mp hw) (1 / ((n : ℝ) + 1)) (by positivity)
  choose b hb hdist using hchoose
  choose φ hφ using hb
  have hbtend : Tendsto b atTop (𝓝 w) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hev : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε :=
      (tendsto_one_div_add_atTop_nhds_zero_nat.eventually (Iio_mem_nhds hε))
    rcases (eventually_atTop.1 hev) with ⟨N, hN⟩
    refine ⟨N, fun n hn => ?_⟩
    exact (dist_comm w (b n)).symm ▸ (hdist n).trans_le (le_of_lt (hN n hn))
  have hφtend : Tendsto (fun n => smoothSobolevData (φ n)) atTop (𝓝 w) := by
    refine hbtend.congr' ?_
    exact Filter.Eventually.of_forall (fun n => (hφ n).symm)
  have hvalueLp : Tendsto (fun n => testL2 (φ n)) atTop
      (𝓝 (w.1 : DomainL2 Ω)) := by
    have h := (continuous_fst.tendsto w).comp hφtend
    exact h
  have hgradLp (i : Fin d) : Tendsto (fun n => testPartialL2 (φ n) i) atTop
      (𝓝 (w.2 i : DomainL2 Ω)) := by
    have h := (((continuous_apply i).comp continuous_snd).tendsto w).comp hφtend
    exact h
  have hvalue : Tendsto
      (fun n => eLpNorm (fun x => φ n x - (w.1 : SpatialCoordinates d → ℝ) x) 2
        (volume.restrict (Ω : Set (SpatialCoordinates d)))) atTop (𝓝 0) := by
    have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'
      (fun n => testL2 (φ n)) w.1).mp hvalueLp
    refine h.congr' (Filter.Eventually.of_forall (fun n => ?_))
    apply eLpNorm_congr_ae
    filter_upwards [testL2_coeFn (φ n)] with x hx₁
    simp only [Pi.sub_apply, hx₁]
  have hgrad (i : Fin d) : Tendsto
      (fun n => eLpNorm
        (fun x => fderiv ℝ (φ n) x (Pi.single i 1) -
          (w.2 i : SpatialCoordinates d → ℝ) x) 2
        (volume.restrict (Ω : Set (SpatialCoordinates d)))) atTop (𝓝 0) := by
    have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'
      (fun n => testPartialL2 (φ n) i) (w.2 i)).mp (hgradLp i)
    refine h.congr' (Filter.Eventually.of_forall (fun n => ?_))
    apply eLpNorm_congr_ae
    filter_upwards [testPartialL2_coeFn (φ n) i] with x hx₁
    simp only [Pi.sub_apply, hx₁]
  have hpair : SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedSubunitKilledLower.DirichletSobolevPair
      (Ω : Set (SpatialCoordinates d))
      (w.1 : SpatialCoordinates d → ℝ)
      (fun x i => (w.2 i : SpatialCoordinates d → ℝ) x) := by
    refine ⟨Lp.memLp w.1, ?_, ?_⟩
    · intro i
      exact Lp.memLp (w.2 i)
    · refine ⟨(fun n => (φ n : SpatialCoordinates d → ℝ)), ?_, ?_, ?_, hvalue, ?_⟩
      · intro n
        exact (φ n).contDiff
      · intro n
        exact (φ n).hasCompactSupport
      · intro n
        exact (φ n).tsupport_subset
      · intro i
        exact hgrad i
  obtain ⟨v, hv, hvg⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedSubunitKilledLower.DirichletSobolevPair.exists_h10
      hpair
  exact ⟨v, hv, hvg⟩

theorem aux_lem_20_product_h10_bounded_comp
    {d : ℕ} {W : Set (SpatialCoordinates d)}
    (hW : IsOpenBoundedConvexDomain W) (u : H10Function W)
    {A : ℝ} (hA : 0 ≤ A)
    (hub : ∀ᵐ x ∂(volume.restrict W),
      |u.toH1Function.toFun x| ≤ A)
    {G : ℝ → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hG0 : G 0 = 0)
    {M B : ℝ} (hM : 0 ≤ M)
    (hderiv : ∀ t, |deriv G t| ≤ M)
    (hbound : ∀ t, |G t| ≤ B) :
    ∃ v : H10Function W,
      v.toH1Function.toFun = (fun x => G (u.toH1Function.toFun x)) ∧
      v.toH1Function.grad =
        (fun x i => deriv G (u.toH1Function.toFun x) * u.toH1Function.grad x i) ∧
      (∀ n x, |v.approx n x| ≤ B) := by
  letI : IsFiniteMeasure (volume.restrict W) := hW.isFiniteMeasure_restrict_volume
  obtain ⟨v, hv, hvg⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.exists_moser_h1_comp hW
      u.toH1Function hA hub (hG.of_le (by norm_num))
  have hdiff : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hLip : LipschitzWith M.toNNReal G :=
    lipschitzWith_of_abs_deriv_le hM hdiff hderiv
  have hDc : Continuous (deriv G) := hG.continuous_deriv (by norm_num)
  have hsm (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => G (u.approx n x)) := by
    simpa only [Function.comp_apply] using! hG.comp (u.approx_smooth n)
  have hsupp (n : ℕ) : HasCompactSupport (fun x => G (u.approx n x)) := by
    exact (u.approx_hasCompactSupport n).of_isClosed_subset
      (isClosed_tsupport _) (tsupport_comp_subset hG0 (u.approx n))
  have hsub (n : ℕ) : tsupport (fun x => G (u.approx n x)) ⊆ W := by
    exact (tsupport_comp_subset hG0 (u.approx n)).trans (u.approx_support_subset n)
  obtain ⟨σ, hσmono, hσae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num)
      u.tendsto_approx).exists_seq_tendsto_ae
  let μ : Measure (SpatialCoordinates d) := volume.restrict W
  refine ⟨{ toH1Function := v
            approx := fun n x => G (u.approx (σ n) x)
            approx_smooth := fun n => hsm (σ n)
            approx_hasCompactSupport := fun n => hsupp (σ n)
            approx_support_subset := fun n => hsub (σ n)
            tendsto_approx := ?_
            tendsto_approx_grad := ?_ }, hv, hvg, ?_⟩
  · have hupper : Tendsto (fun n => ENNReal.ofReal M *
        eLpNorm (fun x => u.approx (σ n) x - u.toH1Function.toFun x) 2 μ)
        atTop (𝓝 0) := by
      simpa using! ENNReal.Tendsto.const_mul
        (u.tendsto_approx.comp hσmono.tendsto_atTop)
        (Or.inr ENNReal.ofReal_ne_top)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun _ => zero_le) (fun n => ?_)
    calc
      _ = eLpNorm (fun x => G (u.approx (σ n) x) -
          G (u.toH1Function.toFun x)) 2 μ :=
        eLpNorm_congr_ae (Filter.Eventually.of_forall (fun x => by
          rw [hv]))
      _ ≤ _ := eLpNorm_comp_sub_le_of_lipschitz hM hLip _ _
          (u.approx_smooth (σ n)).continuous.aestronglyMeasurable
          u.toH1Function.memL2.aestronglyMeasurable
  · intro i
    let TA : ℕ → SpatialCoordinates d → ℝ := fun n x =>
      deriv G (u.approx (σ n) x) *
        ((fderiv ℝ (u.approx (σ n)) x) (basisVec i) - u.toH1Function.grad x i)
    let TB : ℕ → SpatialCoordinates d → ℝ := fun n x =>
      (deriv G (u.approx (σ n) x) - deriv G (u.toH1Function.toFun x)) *
        u.toH1Function.grad x i
    have hmeasA (n : ℕ) : AEStronglyMeasurable (TA n) μ :=
      (hDc.comp (u.approx_smooth (σ n)).continuous).aestronglyMeasurable.mul
        ((((u.approx_smooth (σ n)).continuous_fderiv (by norm_num)).clm_apply
          continuous_const).aestronglyMeasurable.sub (u.toH1Function.gradMemL2 i).aestronglyMeasurable)
    have hmeasB (n : ℕ) : AEStronglyMeasurable (TB n) μ :=
      ((hDc.comp (u.approx_smooth (σ n)).continuous).aestronglyMeasurable.sub
        (hDc.comp_aestronglyMeasurable u.toH1Function.memL2.aestronglyMeasurable)).mul
          (u.toH1Function.gradMemL2 i).aestronglyMeasurable
    have hTA : Tendsto (fun n => eLpNorm (TA n) 2 μ) atTop (𝓝 0) := by
      have hupper : Tendsto (fun n => ENNReal.ofReal M *
          eLpNorm (fun x => (fderiv ℝ (u.approx (σ n)) x) (basisVec i) -
            u.toH1Function.grad x i) 2 μ) atTop (𝓝 0) := by
        simpa using! ENNReal.Tendsto.const_mul
          ((u.tendsto_approx_grad i).comp hσmono.tendsto_atTop)
          (Or.inr ENNReal.ofReal_ne_top)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
        (fun _ => zero_le) (fun n => ?_)
      calc
        _ ≤ eLpNorm (M • fun x => (fderiv ℝ (u.approx (σ n)) x) (basisVec i) -
            u.toH1Function.grad x i) 2 μ := by
          apply eLpNorm_mono (hmeasA n)
          intro x
          simp only [TA, Pi.smul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs,
            abs_of_nonneg hM]
          exact mul_le_mul_of_nonneg_right (hderiv _) (abs_nonneg _)
        _ = _ := by rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hM]
    have hTB : Tendsto (fun n => eLpNorm (TB n) 2 μ) atTop (𝓝 0) := by
      have hdom := ((u.toH1Function.gradMemL2 i).const_mul (2 * M)).norm
      have hboundTB (n : ℕ) : ∀ᵐ x ∂μ,
          ‖TB n x‖ ≤ ‖(2 * M) * u.toH1Function.grad x i‖ := by
        filter_upwards with x
        simp only [TB, norm_mul, Real.norm_eq_abs, abs_of_nonneg hM,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        calc
          _ ≤ |deriv G (u.approx (σ n) x)| +
              |deriv G (u.toH1Function.toFun x)| := abs_sub _ _
          _ ≤ M + M := add_le_add (hderiv _) (hderiv _)
          _ = 2 * M := by ring
      have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => TB n x) atTop (𝓝 0) := by
        filter_upwards [hσae] with x hx
        have h := (((hDc.tendsto _).comp hx).sub
          (tendsto_const_nhds (x := deriv G (u.toH1Function.toFun x)))).mul_const
          (u.toH1Function.grad x i)
        simpa only [TB, sub_self, zero_mul] using! h
      simpa using! tendsto_eLpNorm_two_of_tendsto_ae_of_dominated hmeasB
        (memLp_const (0 : ℝ)) hdom hboundTB hlim
    have hsum : Tendsto (fun n => eLpNorm (TA n) 2 μ + eLpNorm (TB n) 2 μ)
        atTop (𝓝 0) := by simpa using! hTA.add hTB
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => zero_le) (fun n => ?_)
    calc
      _ = eLpNorm (fun x => TA n x + TB n x) 2 μ := by
        apply eLpNorm_congr_ae
        filter_upwards with x
        dsimp only [TA, TB]
        rw [congrFun (congrFun hvg x) i]
        rw [fderiv_comp_basisVec hdiff.differentiableAt
          ((u.approx_smooth (σ n)).differentiable (by norm_num)).differentiableAt]
        ring
      _ ≤ _ := eLpNorm_add_le (by norm_num)
  · intro n x
    exact hbound _

theorem aux_lem_20_product_h10_product
    {d : ℕ} {W : Set (SpatialCoordinates d)}
    (hW : IsOpenBoundedConvexDomain W) (u chi : H10Function W)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hu : ∀ᵐ x ∂(volume.restrict W), |u.toH1Function.toFun x| ≤ A)
    (hchi : ∀ n x, |chi.approx n x| ≤ B)
    (hchival : ∀ x, |chi.toH1Function.toFun x| ≤ B) :
    ∃ p : H10Function W,
      p.toH1Function.toFun = fun x => chi.toH1Function.toFun x * u.toH1Function.toFun x := by
  letI : IsFiniteMeasure (volume.restrict W) := hW.isFiniteMeasure_restrict_volume
  let μ : Measure (SpatialCoordinates d) := volume.restrict W
  have huTop : MemLp u.toH1Function.toFun ∞ μ := by
    exact MemLp.of_bound u.toH1Function.memL2.aestronglyMeasurable A hu
  have hchiTop : MemLp chi.toH1Function.toFun ∞ μ := by
    exact MemLp.of_bound chi.toH1Function.memL2.aestronglyMeasurable B
      (Filter.Eventually.of_forall hchival)
  have hprod : MemLp (fun x => chi.toH1Function.toFun x * u.toH1Function.toFun x) 2 μ := by
    simpa [μ, mul_comm] using! hchiTop.mul' u.toH1Function.memL2
  have hprodgrad (i : Fin d) :
      MemLp (fun x => chi.toH1Function.toFun x * u.toH1Function.grad x i +
        u.toH1Function.toFun x * chi.toH1Function.grad x i) 2 μ := by
    simpa only [mul_comm] using!
      ((u.toH1Function.gradMemL2 i).mul' (r := 2) hchiTop).add
        (huTop.mul' (r := 2) (chi.toH1Function.gradMemL2 i))
  obtain ⟨σ, hσmono, hσae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num)
      chi.tendsto_approx).exists_seq_tendsto_ae
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
    simpa only [mul_comm] using! h
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
        chi.toH1Function.memL2.aestronglyMeasurable).mul (u.toH1Function.gradMemL2 i).aestronglyMeasurable
    have hmeasB (n : ℕ) : AEStronglyMeasurable (TB n) μ := by
      exact huTop.aestronglyMeasurable.mul
        ((((chi.approx_smooth (σ n)).continuous_fderiv (by norm_num)).clm_apply
          continuous_const).aestronglyMeasurable.sub
          (chi.toH1Function.gradMemL2 i).aestronglyMeasurable)
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
        simpa only [TA, sub_self, zero_mul] using! h
      simpa using! tendsto_eLpNorm_two_of_tendsto_ae_of_dominated hmeasA
        (memLp_const (0 : ℝ)) hdom hboundA hlimA
    have hBconv : Tendsto (fun n => eLpNorm (TB n) 2 μ) atTop (𝓝 0) := by
      have h :=
        tendsto_eLpNorm_mul_of_memLp_top huTop (chi.toH1Function.gradMemL2 i)
          (fun n x => (fderiv ℝ (chi.approx (σ n)) x) (basisVec i))
          (fun n => (((chi.approx_smooth (σ n)).continuous_fderiv (by norm_num)).clm_apply
            continuous_const).memLp_of_hasCompactSupport
              ((chi.approx_hasCompactSupport (σ n)).fderiv_apply (𝕜 := ℝ) (basisVec i)) |>.restrict W)
          ((chi.tendsto_approx_grad i).comp hσmono.tendsto_atTop)
      simpa only [TB, Pi.sub_apply, mul_sub] using! h
    have hsum : Tendsto (fun n => eLpNorm (TA n) 2 μ + eLpNorm (TB n) 2 μ)
        atTop (𝓝 0) := by simpa using! hAconv.add hBconv
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => zero_le) (fun n => ?_)
    calc
      _ = eLpNorm (fun x => TA n x + TB n x) 2 μ := by
        apply eLpNorm_congr_ae
        filter_upwards with x
        dsimp only [TA, TB]
        ring
      _ ≤ _ := eLpNorm_add_le (by norm_num)
  let P : ℕ → H10Function W := fun n =>
    u.mulContDiffHasCompactSupport (chi.approx_smooth (σ n))
      (chi.approx_hasCompactSupport (σ n))
  have hPval (n : ℕ) :
      (P n).toH1Function.toFun =
        fun x => chi.approx (σ n) x * u.toH1Function.toFun x := by
    simpa [P] using! H10Function.mulContDiffHasCompactSupport_toFun u
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
    simpa only [ε, Function.comp_def, Nat.cast_add, Nat.cast_one] using!
      (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1))
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
        (P n).toH1Function.memL2.aestronglyMeasurable
    have hpa : AEStronglyMeasurable
        (fun x => (P n).toH1Function.toFun x -
          chi.toH1Function.toFun x * u.toH1Function.toFun x) μ :=
      (P n).toH1Function.memL2.aestronglyMeasurable.sub hprod.aestronglyMeasurable
    calc
      _ = eLpNorm (fun x => (f n x - (P n).toH1Function.toFun x) +
          ((P n).toH1Function.toFun x -
            chi.toH1Function.toFun x * u.toH1Function.toFun x)) 2 μ := by
        apply eLpNorm_congr_ae
        exact Filter.Eventually.of_forall (fun x => by ring)
      _ ≤ eLpNorm (fun x => f n x - (P n).toH1Function.toFun x) 2 μ +
          eLpNorm (fun x => (P n).toH1Function.toFun x -
            chi.toH1Function.toFun x * u.toH1Function.toFun x) 2 μ :=
        eLpNorm_add_le (by norm_num)
      _ ≤ _ := add_le_add (le_of_lt (by simpa [f] using! (hk n).1)) (le_rfl)
  have hvalue : Tendsto
      (fun n => eLpNorm (fun x => f n x -
        chi.toH1Function.toFun x * u.toH1Function.toFun x) 2 μ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa [P, H10Function.mulContDiffHasCompactSupport_toFun] using
        hεtend.add hprodVal) (fun _ => zero_le) hvalueBound
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
          ((P n).toH1Function.gradMemL2 i).aestronglyMeasurable
    have hpa : AEStronglyMeasurable
        (fun x => (P n).toH1Function.grad x i -
          (chi.toH1Function.toFun x * u.toH1Function.grad x i +
            u.toH1Function.toFun x * chi.toH1Function.grad x i)) μ :=
      (P n).toH1Function.gradMemL2 i |>.aestronglyMeasurable.sub (hprodgrad i).aestronglyMeasurable
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
        eLpNorm_add_le (by norm_num)
      _ ≤ _ := add_le_add (le_of_lt (by simpa [f] using! (hk n).2 i)) (le_rfl)
  have hgrad (i : Fin d) : Tendsto
      (fun n => eLpNorm (fun x => (fderiv ℝ (f n) x) (basisVec i) -
        (chi.toH1Function.toFun x * u.toH1Function.grad x i +
          u.toH1Function.toFun x * chi.toH1Function.grad x i)) 2 μ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [hPgrad, add_zero, zero_add] using
        hεtend.add (hprodGrad i)) (fun _ => zero_le) (hgradBound i)
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
  obtain ⟨p, hp, _⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedSubunitKilledLower.DirichletSobolevPair.exists_h10
      pair
  exact ⟨p, hp⟩



theorem lem_20_product_h10
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
        (chi.val.1 : SpatialCoordinates d → ℝ) x ≤ 1) :
    ∃ prod : S.space,
      (prod.val.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
          (fun x => uc x * (1 - (chi.val.1 : SpatialCoordinates d → ℝ) x)) := by
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
    simpa [W] using! (centeredCube z R hR).isOpen.measurableSet
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
    have habs : |uc x| ≤ C := by simpa [Real.norm_eq_abs] using! hcx
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
    simpa [G] using! b.contDiff.mul (contDiff_id : ContDiff ℝ (⊤ : ℕ∞) id)
  have hG0 : G 0 = 0 := by simp [G]
  have hGcomp : HasCompactSupport G := by
    simpa [G] using! b.hasCompactSupport.mul_right
  obtain ⟨B₀, hB₀⟩ := hGcomp.exists_bound_of_continuous hG.continuous
  let B : ℝ := max B₀ 0
  have hB : 0 ≤ B := le_max_right B₀ 0
  have hbound : ∀ t, |G t| ≤ B := by
    intro t
    have ht : |G t| ≤ B₀ := by
      simpa only [Real.norm_eq_abs] using! hB₀ t
    exact ht.trans (le_max_left B₀ 0)
  have hGderivcomp : HasCompactSupport (deriv G) := by
    simpa only [fderiv_apply_one_eq_deriv] using! hGcomp.fderiv_apply ℝ (1 : ℝ)
  obtain ⟨D, hD⟩ := hGderivcomp.exists_bound_of_continuous
    (hG.continuous_deriv (by norm_num))
  let M : ℝ := max D 0
  have hM : 0 ≤ M := le_max_right D 0
  have hderiv : ∀ t, |deriv G t| ≤ M := by
    intro t
    have ht : |deriv G t| ≤ D := by
      simpa only [Real.norm_eq_abs] using! hD t
    exact ht.trans (le_max_left D 0)
  have hGone {t : ℝ} (ht : |t| ≤ 1) : G t = t := by
    have hb : b t = 1 := b.one_of_mem_closedBall (by
      rw [mem_closedBall_zero_iff]
      exact (by simpa [Real.norm_eq_abs] using! ht.trans (by norm_num : (1 : ℝ) ≤ 2)))
    simp [G, hb]
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
    apply hGone
    rw [abs_of_nonneg hx.1]
    exact hx.2
  obtain ⟨pchi, hpchi⟩ :=
    aux_lem_20_product_h10_product hW uH chiB hA hB huBound hchiBapprox hchiBpoint
  let pfinal : H10Function W := uH - pchi
  have hpfinal : pfinal.toH1Function.toFun = fun x =>
      uH.toH1Function.toFun x - pchi.toH1Function.toFun x := by
    change (uH.toH1Function - pchi.toH1Function).toFun = _
    rw [H1Function.sub_toFun]
  obtain ⟨q, hqval, hqgrad⟩ :=
    SubdiffusiveProcess.Lane4.exists_killedSobolevGraph_of_nativeH10 pfinal
  have hqS : (q.val : SobolevData (centeredCube z R hR)) ∈ S.space := by
    rw [hS]
    exact q.property
  let prod : S.space := ⟨q.val, hqS⟩
  refine ⟨prod, ?_⟩
  filter_upwards [hqval, hchiBae, huc] with x hq hcb hu
  calc
    (prod.val.1 : SpatialCoordinates d → ℝ) x =
        ((q : killedSobolevGraph (centeredCube z R hR)).val.1 :
          SpatialCoordinates d → ℝ) x := rfl
    _ = pfinal.toH1Function.toFun x := hq
    _ = uH.toH1Function.toFun x - pchi.toH1Function.toFun x := by
      rw [hpfinal]
    _ = uH.toH1Function.toFun x - chiB.toH1Function.toFun x *
        uH.toH1Function.toFun x := by rw [hpchi]
    _ = (u.val.1 : SpatialCoordinates d → ℝ) x -
        (chi.val.1 : SpatialCoordinates d → ℝ) x *
          (u.val.1 : SpatialCoordinates d → ℝ) x := by
      rw [huHval, hcb]
    _ = uc x * (1 - (chi.val.1 : SpatialCoordinates d → ℝ) x) := by
      rw [hu]
      ring

end Paper

