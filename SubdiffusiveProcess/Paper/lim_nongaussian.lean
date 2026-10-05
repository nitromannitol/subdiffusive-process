module

public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.lim_measure
public import SubdiffusiveProcess.Paper.lim_transition_domination
public import SubdiffusiveProcess.Paper.prop_chaos_growth
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.MultiplicativeChaos.SpeedBasic
public import SubdiffusiveProcess.Geometry.GrowthBoundary
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import MarkovProcess.Path.ExitTime
public import SubdiffusiveProcess.Main.JointPathProbabilityMeasure
public import SubdiffusiveProcess.Main.PathLevyProkhorovDist
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.MutuallySingular
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import SubdiffusiveProcess.Probability.Diffusion.BrownianDensity
public import SubdiffusiveProcess.Probability.Diffusion.StandardGaussianMoments
public import SubdiffusiveProcess.Main.DiffusionPath

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Asymptotics
open MarkovProcess
open SubdiffusiveProcess
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SubdiffusiveProcess.Paper

theorem aux_lim_nongaussian_frostman
    {d : ℕ} (hd : 2 ≤ d) (ν : Measure (SpatialCoordinates d))
    [IsFiniteMeasureOnCompacts ν] (C : Set (SpatialCoordinates d))
    (hC : IsCompact C) (K t : ℝ) (hK : 0 ≤ K) (ht : (d : ℝ) - 1 < t)
    (hsupp : ν Cᶜ = 0)
    (hgrowth : ∀ x ∈ C, ∀ r : ℝ, 0 < r → r ≤ 1 →
      ν (Metric.ball x r) ≤ ENNReal.ofReal (K * r ^ t)) :
    ∀ s : Set (SpatialCoordinates d),
      dimH s < ENNReal.ofReal t → ν s = 0 := by
  classical
  let νC : Measure (SpatialCoordinates d) := ν.restrict C
  have htpos : 0 < t := by
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    linarith
  have hsuppC : νC Cᶜ = 0 := by
    change ν.restrict C Cᶜ = 0
    rw [Measure.restrict_apply hC.measurableSet.compl]
    simp
  have hgrowthC : ∀ x ∈ C, ∀ r : ℝ, 0 < r → r ≤ 1 →
      νC (Metric.ball x r) ≤ ENNReal.ofReal (K * r ^ t) := by
    intro x hx r hr hr1
    change ν.restrict C (Metric.ball x r) ≤ _
    rw [Measure.restrict_apply measurableSet_ball]
    exact (measure_mono Set.inter_subset_left).trans (hgrowth x hx r hr hr1)
  have hatom : ∀ x : SpatialCoordinates d, νC {x} = 0 := by
    intro x
    by_cases hx : x ∈ C
    · let r : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
      have hrpos : ∀ n, 0 < r n := by
        intro n
        dsimp [r]
        positivity
      have hrle : ∀ n, r n ≤ 1 := by
        intro n
        dsimp [r]
        have hn : (1 : ℝ) ≤ n + 1 := by norm_num
        exact (div_le_iff₀ (by positivity)).2 (by simp)
      have hle : ∀ n, νC {x} ≤ ENNReal.ofReal (K * (r n) ^ t) := by
        intro n
        exact (measure_mono (by
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst y
          simp [Metric.mem_ball, hrpos n])).trans
          (hgrowthC x hx (r n) (hrpos n) (hrle n))
      have hr_real : Tendsto r atTop (𝓝 0) := by
        simpa [r] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have hr_tendsto : Tendsto (fun n : ℕ => ENNReal.ofReal (r n)) atTop (𝓝 0) := by
        simpa only [Function.comp_def, ENNReal.ofReal_zero] using! ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr_real
      have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (K * (r n) ^ t)) atTop (𝓝 0) := by
        have hcomp := (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos
            (c := ENNReal.ofReal K) ENNReal.ofReal_ne_top htpos).comp hr_tendsto
        convert hcomp using 1
        funext n
        simp only [Function.comp_apply]
        rw [ENNReal.ofReal_mul hK,
          ← ENNReal.ofReal_rpow_of_nonneg (hrpos n).le htpos.le]
      exact le_antisymm
        (ge_of_tendsto' (f := fun n : ℕ => ENNReal.ofReal (K * (r n) ^ t)) hlim hle)
        zero_le
    · exact measure_mono_null (Set.singleton_subset_iff.mpr hx) hsuppC
  let dt : ℝ≥0 := ⟨t, htpos.le⟩
  let c0 : ℝ≥0∞ := ENNReal.ofReal (1 + K * (2 : ℝ) ^ t)
  let m : ℝ≥0∞ → ℝ≥0∞ := fun z => c0 * z ^ t
  have hc00 : c0 ≠ 0 := by
    have hnonneg : 0 ≤ K * (2 : ℝ) ^ t :=
      mul_nonneg hK (Real.rpow_nonneg (by norm_num) _)
    simp only [c0, ne_eq, ENNReal.ofReal_eq_zero]
    nlinarith
  have hc0top : c0 ≠ ∞ := by simp [c0]
  have hνmk : νC ≤ Measure.mkMetric m := by
    apply Measure.le_mkMetric m νC (1 / 2)
    · norm_num
    · intro s hs
      by_cases hsempty : s.Nonempty
      · rcases hsempty with ⟨z, hz⟩
        by_cases hD : Metric.ediam s = 0
        · have hsub : s ⊆ {z} := by
            intro y hy
            apply Set.mem_singleton_iff.mpr
            apply edist_eq_zero.mp
            have hdist0 : edist y z ≤ 0 := by
              rw [← hD]
              exact Metric.edist_le_ediam_of_mem hy hz
            exact le_antisymm hdist0 (by exact bot_le)
          rw [measure_mono_null hsub (hatom z)]
          exact bot_le
        · by_cases hxsC : ∃ x, x ∈ s ∧ x ∈ C
          · rcases hxsC with ⟨x, hxs, hxC⟩
            let D : ℝ≥0∞ := Metric.ediam s
            have hD0 : D ≠ 0 := hD
            have hDtop : D ≠ ∞ := by
              exact ne_of_lt (lt_of_le_of_lt hs (by norm_num))
            have hDreal : 0 < D.toReal := ENNReal.toReal_pos hD0 hDtop
            have hdist : ∀ y ∈ s, dist y x ≤ D.toReal := by
              intro y hy
              have hxy := Metric.edist_le_ediam_of_mem hy hxs
              have hxy' : ENNReal.ofReal (dist y x) ≤ D := by
                simpa [D, edist_dist] using hxy
              simpa using ENNReal.toReal_mono hDtop hxy'
            have hball : s ⊆ Metric.ball x (2 * D.toReal) := by
              intro y hy
              rw [Metric.mem_ball]
              exact (hdist y hy).trans_lt (by nlinarith)
            have hrad : 0 < 2 * D.toReal := by positivity
            have hradle : 2 * D.toReal ≤ 1 := by
              have hDreal_le : D.toReal ≤ (1 / 2 : ℝ) := by
                change D ≤ (1 / 2 : ℝ≥0∞) at hs
                exact ENNReal.toReal_mono (by norm_num) hs |>.trans_eq (by norm_num)
              linarith
            have hsmeasure : νC s ≤ νC (Metric.ball x (2 * D.toReal)) :=
              measure_mono hball
            have hg := hgrowthC x hxC (2 * D.toReal) hrad hradle
            have hpow : D ^ t = ENNReal.ofReal (D.toReal ^ t) := by
              rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg htpos.le,
                ENNReal.ofReal_toReal hDtop]
            have hbound : ENNReal.ofReal (K * (2 * D.toReal) ^ t) ≤ m D := by
              change ENNReal.ofReal (K * (2 * D.toReal) ^ t) ≤ c0 * D ^ t
              simp only [hpow, c0]
              rw [← ENNReal.ofReal_mul (by positivity)]
              apply ENNReal.ofReal_le_ofReal
              rw [Real.mul_rpow (by norm_num) ENNReal.toReal_nonneg]
              have hp : 0 ≤ D.toReal ^ t := Real.rpow_nonneg (by positivity) t
              calc
                K * ((2 : ℝ) ^ t * D.toReal ^ t) =
                    (K * (2 : ℝ) ^ t) * D.toReal ^ t := by ring
                _ ≤ (1 + K * (2 : ℝ) ^ t) * D.toReal ^ t := by
                  exact mul_le_mul_of_nonneg_right (by linarith) hp
            exact hsmeasure.trans (hg.trans hbound)
          · have hsub : s ⊆ Cᶜ := by
              intro y hy
              by_contra hyC
              exact hxsC ⟨y, hy, Classical.not_not.mp hyC⟩
            calc
              νC s = 0 := measure_mono_null hsub hsuppC
              _ ≤ m (Metric.ediam s) := bot_le
      · have hs0 : s = ∅ := Set.not_nonempty_iff_eq_empty.mp hsempty
        subst s
        simp [m]
  have hνac : νC ≪ MeasureTheory.Measure.hausdorffMeasure (dt : ℝ) := by
    apply Measure.absolutelyContinuous_of_le_smul
    have hmk : Measure.mkMetric m ≤ c0 •
        (Measure.mkMetric (fun z : ℝ≥0∞ => z ^ (dt : ℝ)) : Measure (SpatialCoordinates d)) := by
      apply Measure.mkMetric_mono_smul hc0top hc00
      filter_upwards [] with z
      simp [m, dt]
      rfl
    have hmk' : Measure.mkMetric m ≤ c0 •
        (MeasureTheory.Measure.hausdorffMeasure (X := SpatialCoordinates d) (dt : ℝ)) := by
      simpa [Measure.hausdorffMeasure] using! hmk
    exact hνmk.trans hmk'
  intro s hs
  have hs' : dimH s < (dt : ℝ≥0∞) := by
    simpa [dt, ENNReal.ofReal_eq_coe_nnreal htpos.le] using! hs
  have hsc : νC s = 0 := measure_zero_of_dimH_lt hνac hs'
  apply le_antisymm
  · calc
    ν s ≤ ν (s ∩ C ∪ Cᶜ) := measure_mono (by
      intro x hx
      by_cases hxc : x ∈ C
      · exact Or.inl ⟨hx, hxc⟩
      · exact Or.inr hxc)
    _ ≤ ν (s ∩ C) + ν Cᶜ := measure_union_le _ _
    _ = 0 := by
      rw [hsupp]
      have hrestrict : νC s = ν (s ∩ C) := by
        change ν.restrict C s = ν (s ∩ C)
        rw [Measure.restrict_apply' hC.measurableSet]
      rw [← hrestrict, hsc]
      simp
  · exact zero_le

theorem aux_lim_nongaussian_hyperplane_null
    {d : ℕ} (hd : 2 ≤ d) (ν : Measure (SpatialCoordinates d))
    [IsFiniteMeasureOnCompacts ν] (t : ℝ) (ht : (d : ℝ) - 1 < t)
    (hgrowth : ∀ n : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ x ∈ Metric.closedBall (0 : SpatialCoordinates d) n, ∀ r : ℝ,
        0 < r → r ≤ 1 → ν (Metric.ball x r) ≤ ENNReal.ofReal (K * r ^ t)) :
    ∀ (L : SpatialCoordinates d →L[ℝ] ℝ) (_hL : L ≠ 0) (c : ℝ),
      ν {x | L x = c} = 0 := by
  classical
  intro L hL c
  have hLv : ∃ v : SpatialCoordinates d, L v ≠ 0 := by
    by_contra h
    push Not at h
    exact hL (by ext x; exact h x)
  obtain ⟨v, hv⟩ := hLv
  have hdim :
      dimH ({x : SpatialCoordinates d | L x = c}) < ENNReal.ofReal t := by
    have hLker : L.toLinearMap ≠ 0 := by
      intro hzero
      apply hL
      ext x
      exact congrArg (fun f => f x) hzero
    let A : (LinearMap.ker L.toLinearMap) → SpatialCoordinates d := fun y =>
      y.1 + ((c - L y.1) / L v) • v
    have hAcont : ContDiff ℝ 1 A := by
      change ContDiff ℝ 1 (fun y : LinearMap.ker L.toLinearMap =>
        (LinearMap.ker L.toLinearMap).subtypeL y +
          ((c - L ((LinearMap.ker L.toLinearMap).subtypeL y)) / L v) • v)
      fun_prop
    have hArange : Set.range A = {x : SpatialCoordinates d | L x = c} := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        change L (y.1 + ((c - L y.1) / L v) • v) = c
        simp only [map_add, map_smul, smul_eq_mul]
        field_simp [hv]
        ring
      · intro hx
        let y : LinearMap.ker L.toLinearMap :=
          ⟨x - (L x / L v) • v, by
            change L (x - (L x / L v) • v) = 0
            simp only [map_sub, map_smul, smul_eq_mul]
            field_simp [hv]
            ring
          ⟩
        refine ⟨y, ?_⟩
        have hyL : L (x - (L x / L v) • v) = 0 := by
          simp only [map_sub, map_smul, smul_eq_mul]
          field_simp [hv]
          ring
        dsimp [A, y]
        rw [hyL]
        simp only [sub_zero]
        change x - (L x / L v) • v + (c / L v) • v = x
        rw [hx]
        ring
    have hfinrank : Module.finrank ℝ (LinearMap.ker L.toLinearMap) + 1 = d := by
      simpa [Module.finrank_pi] using
        (Module.Dual.finrank_ker_add_one_of_ne_zero (f := L.toLinearMap) hLker)
    have hdimrange : dimH (Set.range A) ≤
        (Module.finrank ℝ (LinearMap.ker L.toLinearMap) : ℝ≥0∞) := by
      exact Differentiable.dimH_range_le (hAcont.differentiable (by norm_num))
    have hdimlt : (Module.finrank ℝ (LinearMap.ker L.toLinearMap) : ℝ≥0∞) <
        ENNReal.ofReal t := by
      have htpos : 0 < t := by
        have hd' : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
        linarith
      rw [ENNReal.ofReal_eq_coe_nnreal htpos.le,
        ← ENNReal.coe_natCast (Module.finrank ℝ (LinearMap.ker L.toLinearMap)),
        ENNReal.coe_lt_coe]
      have hker_nat : Module.finrank ℝ (LinearMap.ker L.toLinearMap) = d - 1 := by omega
      rw [hker_nat]
      change ((d - 1 : ℕ) : ℝ) < t
      rw [Nat.cast_sub (show 1 ≤ d by omega)]
      norm_num
      exact ht
    have hdimlevel : dimH {x : SpatialCoordinates d | L x = c} < ENNReal.ofReal t := by
      rw [← hArange]
      exact hdimrange.trans_lt hdimlt
    exact hdimlevel
  have hlevel_null : ∀ n : ℕ,
      ν ({x : SpatialCoordinates d | L x = c} ∩ Metric.closedBall 0 n) = 0 := by
    intro n
    exact (by
      have hC : IsCompact (Metric.closedBall (0 : SpatialCoordinates d) n) :=
        isCompact_closedBall _ _
      obtain ⟨K, hK, hKgrowth⟩ := hgrowth n
      let νC : Measure (SpatialCoordinates d) :=
        ν.restrict (Metric.closedBall (0 : SpatialCoordinates d) n)
      have hνC_support : νC (Metric.closedBall (0 : SpatialCoordinates d) n)ᶜ = 0 := by
        change ν.restrict (Metric.closedBall (0 : SpatialCoordinates d) n)
            (Metric.closedBall (0 : SpatialCoordinates d) n)ᶜ = 0
        rw [Measure.restrict_apply hC.measurableSet.compl]
        simp
      have hνC_growth : ∀ x ∈ Metric.closedBall (0 : SpatialCoordinates d) n,
          ∀ r : ℝ, 0 < r → r ≤ 1 →
          νC (Metric.ball x r) ≤ ENNReal.ofReal (K * r ^ t) := by
        intro x hx r hr hr1
        change ν.restrict (Metric.closedBall (0 : SpatialCoordinates d) n)
            (Metric.ball x r) ≤ _
        rw [Measure.restrict_apply measurableSet_ball]
        exact (measure_mono Set.inter_subset_left).trans (hKgrowth x hx r hr hr1)
      let : IsFiniteMeasureOnCompacts νC := inferInstance
      have hzero := aux_lim_nongaussian_frostman hd νC
        (Metric.closedBall (0 : SpatialCoordinates d) n) hC K t hK ht
        hνC_support hνC_growth {x : SpatialCoordinates d | L x = c} hdim
      change ν.restrict (Metric.closedBall (0 : SpatialCoordinates d) n)
          {x : SpatialCoordinates d | L x = c} = 0 at hzero
      rw [Measure.restrict_apply' hC.measurableSet] at hzero
      exact hzero)
  apply measure_mono_null (s := {x : SpatialCoordinates d | L x = c})
    (t := ⋃ n : ℕ, {x : SpatialCoordinates d | L x = c} ∩
      Metric.closedBall (0 : SpatialCoordinates d) n)
  · intro x hx
    obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
    refine Set.mem_iUnion.2 ⟨n, ⟨hx, ?_⟩⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hn.le
  · exact measure_iUnion_null hlevel_null

theorem aux_lim_nongaussian_gaussian_ac
    {d : ℕ} (γ : Measure (SpatialCoordinates d)) (hγ : IsGaussian γ)
    (hvar : ∀ (L : SpatialCoordinates d →L[ℝ] ℝ) (_hL : L ≠ 0),
      0 < Var[L; γ]) :
    γ ≪ volume := by
  classical
  let coord : Fin d → SpatialCoordinates d → ℝ := fun i x => x i
  have hcoord : ∀ i, MemLp (coord i) 2 γ := by
    intro i
    simpa [coord] using! hγ.memLp_dual γ (ContinuousLinearMap.proj i) 2 (by norm_num)
  let A : Matrix (Fin d) (Fin d) ℝ := fun i j => cov[coord i, coord j; γ]
  have hA_symm : A.IsHermitian := by
    ext i j
    change cov[coord j, coord i; γ] = cov[coord i, coord j; γ]
    exact covariance_comm _ _
  have hA_pos : ∀ v : SpatialCoordinates d, v ≠ 0 →
      0 < dotProduct (star v) (Matrix.mulVec A v) := by
    intro v hv
    let X : Fin d → SpatialCoordinates d → ℝ := fun i x => v i * coord i x
    have hX : ∀ i, MemLp (X i) 2 γ := by
      intro i
      exact (hcoord i).const_mul _
    have hsum : Var[∑ i, X i; γ] =
        ∑ i, ∑ j, cov[X i, X j; γ] := variance_sum hX
    have hform : (∑ i, X i) =
        (∑ i, v i • (ContinuousLinearMap.proj i :
          SpatialCoordinates d →L[ℝ] ℝ)) := by
      funext x
      simp [X, coord, sum_apply, ContinuousLinearMap.proj_apply,
        smul_eq_mul]
    have hL : (∑ i, v i • (ContinuousLinearMap.proj i :
          SpatialCoordinates d →L[ℝ] ℝ)) ≠ 0 := by
      intro hzero
      apply hv
      ext i
      have hi := congrArg (fun L : SpatialCoordinates d →L[ℝ] ℝ => L (Pi.single i 1)) hzero
      simpa [sum_apply, ContinuousLinearMap.proj_apply,
        Pi.single_apply] using hi
    have hstrict := hvar (∑ i, v i • (ContinuousLinearMap.proj i :
          SpatialCoordinates d →L[ℝ] ℝ)) hL
    rw [← hform, hsum] at hstrict
    have hstrict' : 0 < ∑ i, ∑ j, v j * (v i * cov[coord i, coord j; γ]) := by
      simpa [X, covariance_const_mul_left, covariance_const_mul_right] using hstrict
    convert hstrict' using 1
    simp only [A, dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hA : A.PosDef := Matrix.PosDef.of_dotProduct_mulVec_pos hA_symm hA_pos
  obtain ⟨B, hB, hABraw⟩ :=
    (CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self (a := A)).mp hA.isStrictlyPositive
  have hAB : A = Matrix.conjTranspose B * B := by
    simpa only [Matrix.star_eq_conjTranspose] using hABraw
  let m : SpatialCoordinates d := ∫ x, x ∂γ
  let Tlin : SpatialCoordinates d →ₗ[ℝ] SpatialCoordinates d :=
    Matrix.toLin' (Matrix.conjTranspose B)
  let T : SpatialCoordinates d →L[ℝ] SpatialCoordinates d :=
    LinearMap.toContinuousLinearMap Tlin
  have hBT : IsUnit (Matrix.conjTranspose B) := by
    exact hB.star
  have hTinj : Function.Injective Tlin := by
    simpa only [Tlin, Matrix.mulVecLin_apply] using!
      (Matrix.mulVec_injective_iff_isUnit.mpr hBT)
  have hTsurj : Function.Surjective Tlin :=
    LinearMap.surjective_of_injective hTinj
  let eTlin : SpatialCoordinates d ≃ₗ[ℝ] SpatialCoordinates d :=
    LinearEquiv.ofBijective Tlin ⟨hTinj, hTsurj⟩
  let eT : SpatialCoordinates d ≃L[ℝ] SpatialCoordinates d := eTlin.toContinuousLinearEquiv
  have hdetT : LinearMap.det Tlin ≠ 0 := by
    have hdet : IsUnit (Matrix.conjTranspose B).det :=
      (Matrix.isUnit_iff_isUnit_det (A := Matrix.conjTranspose B)).mp hBT
    simpa [Tlin] using hdet.ne_zero
  have hGcoord : ∀ i, MemLp (coord i)
      2 (SubdiffusiveProcess.Model.HeatSemigroupVec.gaussianVec d 0 1) := by
    intro i
    change MemLp (Function.eval i) 2
      (Measure.pi (fun _ : Fin d => gaussianReal (0 : ℝ) 1))
    have hmap : Measure.map (Function.eval i)
        (Measure.pi (fun _ : Fin d => gaussianReal (0 : ℝ) 1)) =
        gaussianReal (0 : ℝ) 1 := by
      rw [Measure.pi_map_eval]
      simp
    have hbase : MemLp id 2
        (Measure.map (Function.eval i)
          (Measure.pi (fun _ : Fin d => gaussianReal (0 : ℝ) 1))) := by
      rw [hmap]
      exact memLp_id_gaussianReal' 2 (by norm_num)
    simpa [Function.comp_def] using
      hbase.comp_of_map (measurable_pi_apply i).aemeasurable
  have hGmean : ∫ z : SpatialCoordinates d, z ∂
      (SubdiffusiveProcess.Model.HeatSemigroupVec.gaussianVec d 0 1) = 0 := by
    have hGid : Integrable (id : Homogenization.Vec d → Homogenization.Vec d)
        (SubdiffusiveProcess.Model.HeatSemigroupVec.gaussianVec d 0 1) :=
      Integrable.of_eval (fun i => by
        simpa [coord, id] using (hGcoord i).integrable (by norm_num))
    apply funext
    intro i
    have hi := (ContinuousLinearMap.proj i :
        Homogenization.Vec d →L[ℝ] ℝ).integral_comp_comm hGid
    have hi0 : (∫ x : Homogenization.Vec d, x i ∂
          SubdiffusiveProcess.Model.HeatSemigroupVec.gaussianVec d 0 1) = 0 := by
      simpa using SubdiffusiveProcess.Probability.Diffusion.integral_coord (d := d) i
    simpa [ContinuousLinearMap.proj_apply, id] using hi.symm.trans hi0
  have hGcov : ∀ (v : SpatialCoordinates d),
      Var[fun z => ∑ i, v i * coord i z;
        SubdiffusiveProcess.Model.HeatSemigroupVec.gaussianVec d 0 1] = ∑ i, v i ^ 2 := by
    intro v
    let G := SubdiffusiveProcess.Model.HeatSemigroupVec.gaussianVec d 0 1
    have hcov : ∀ i j, cov[coord i, coord j; G] = if i = j then 1 else 0 := by
      intro i j
      by_cases hij : i = j
      · subst j
        have hcoordAe : AEMeasurable (coord i) G := by
          change AEMeasurable (coord i)
            (SubdiffusiveProcess.Model.HeatSemigroupVec.gaussianVec d 0 1)
          exact (hGcoord i).aemeasurable
        rw [covariance_self hcoordAe,
          variance_eq_integral hcoordAe]
        rw [SubdiffusiveProcess.Probability.Diffusion.integral_coord (d := d) i]
        simp only [sub_zero, sq]
        simpa [coord, G, pow_two] using
          SubdiffusiveProcess.Probability.Diffusion.integral_coord_sq (d := d) i
      · rw [covariance_eq_sub (hGcoord i) (hGcoord j)]
        rw [SubdiffusiveProcess.Probability.Diffusion.integral_coord (d := d) i,
          SubdiffusiveProcess.Probability.Diffusion.integral_coord (d := d) j]
        simp only [sub_zero, mul_zero, ite_eq_right hij]
        simpa [G, coord] using
          SubdiffusiveProcess.Probability.Diffusion.integral_coord_mul_of_ne (d := d) hij
    have hX : ∀ i, MemLp (fun z => v i * coord i z) 2 G := by
      intro i
      exact (hGcoord i).const_mul _
    rw [variance_fun_sum hX]
    simp only [covariance_const_mul_left, covariance_const_mul_right, hcov]
    simp [pow_two]
  have hGgauss : IsGaussian
      (SubdiffusiveProcess.Model.HeatSemigroupVec.gaussianVec d 0 1) := by
    apply isGaussian_of_charFunDual_eq
    intro L
    let v : SpatialCoordinates d := fun i => L (Pi.single i 1)
    have hsingle : ∀ (i : Fin d) (a : ℝ),
        L (Pi.single i a) = a * v i := by
      intro i a
      calc
        L (Pi.single i a) = L (a • (Pi.single i (1 : ℝ) : SpatialCoordinates d)) := by
          congr 1
          ext j
          by_cases hji : j = i <;> simp [hji]
        _ = a * v i := by simp [v, smul_eq_mul]
    have hLsum : L = ∑ i, v i • (ContinuousLinearMap.proj i :
        SpatialCoordinates d →L[ℝ] ℝ) := by
      ext x
      conv_lhs => rw [← Finset.univ_sum_single x]
      rw [map_sum]
      simp only [sum_apply, smul_apply,
        ContinuousLinearMap.proj_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i hi
      simpa [mul_comm] using hsingle i (x i)
    have hLmean : (∫ z, L z ∂
        (SubdiffusiveProcess.Model.HeatSemigroupVec.gaussianVec d 0 1)) = 0 := by
      rw [hLsum]
      have hfun : (fun z => (∑ i, v i • (ContinuousLinearMap.proj i :
          SpatialCoordinates d →L[ℝ] ℝ)) z) =
          (fun z => ∑ i, v i * coord i z) := by
        funext z
        simp [coord, sum_apply, ContinuousLinearMap.proj_apply,
          smul_eq_mul]
      rw [hfun, integral_finsetSum]
      · simp only [integral_const_mul]
        apply Finset.sum_eq_zero
        intro i hi
        rw [SubdiffusiveProcess.Probability.Diffusion.integral_coord (d := d) i]
        simp
      · intro i hi
        exact Integrable.const_mul ((hGcoord i).integrable (by norm_num)) _
    have hLvar : Var[L;
        SubdiffusiveProcess.Model.HeatSemigroupVec.gaussianVec d 0 1] = ∑ i, v i ^ 2 := by
      rw [hLsum]
      have hfun : (fun z => (∑ i, v i • (ContinuousLinearMap.proj i :
          SpatialCoordinates d →L[ℝ] ℝ)) z) =
          (fun z => ∑ i, v i * coord i z) := by
        funext z
        simp [coord, sum_apply, ContinuousLinearMap.proj_apply,
          smul_eq_mul]
      change Var[fun z => (∑ i, v i • (ContinuousLinearMap.proj i :
          SpatialCoordinates d →L[ℝ] ℝ)) z;
        SubdiffusiveProcess.Model.HeatSemigroupVec.gaussianVec d 0 1] = ∑ i, v i ^ 2
      rw [hfun]
      exact hGcov v
    have hfactor : ∀ i, charFunDual
        (gaussianReal (0 : ℝ) 1)
        (L.comp (ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i)) =
        Complex.exp (-((v i) ^ 2) / 2) := by
      intro i
      have hcomp : L.comp (ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i) =
          (v i) • (ContinuousLinearMap.id ℝ ℝ) := by
        ext
        simp [v, ContinuousLinearMap.single_apply, smul_eq_mul]
      rw [hcomp, IsGaussian.charFunDual_eq]
      simp only [smul_apply, ContinuousLinearMap.id_apply,
        smul_eq_mul]
      rw [integral_complex_ofReal]
      change Complex.exp
        ((↑(∫ x : ℝ, v i * x ∂gaussianReal (0 : ℝ) 1) : ℂ) * Complex.I -
          ↑(Var[fun x : ℝ => v i * x; gaussianReal (0 : ℝ) 1]) / 2) = _
      rw [integral_const_mul, variance_const_mul]
      simp [v, integral_id_gaussianReal]
      congr 1
      ring_nf
    change charFunDual
      (Measure.pi (fun _ : Fin d => gaussianReal (0 : ℝ) 1)) L = _
    rw [charFunDual_pi]
    simp_rw [hfactor]
    rw [← Complex.exp_sum]
    rw [integral_complex_ofReal, hLmean, hLvar]
    congr 1
    simp only [← Complex.ofReal_pow, ← Complex.ofReal_neg]
    rw [← Finset.sum_div]
    rw [← Complex.ofReal_sum]
    rw [Finset.sum_neg_distrib]
    simp ; ring
  have hquad : ∀ v : SpatialCoordinates d,
      Var[fun x => ∑ i, v i * coord i x; γ] =
        dotProduct (star v) (Matrix.mulVec A v) := by
    intro v
    let X : Fin d → SpatialCoordinates d → ℝ := fun i x => v i * coord i x
    have hX : ∀ i, MemLp (X i) 2 γ := by
      intro i
      exact (hcoord i).const_mul _
    rw [variance_fun_sum hX]
    simp only [A, X, covariance_const_mul_left, covariance_const_mul_right,
      dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hTform : ∀ (v z : SpatialCoordinates d),
      (∑ i, v i * coord i (T z)) =
        ∑ i, (Matrix.mulVec B v) i * coord i z := by
    intro v z
    change (∑ i, v i * ∑ j, B j i * z j) =
      ∑ i, (∑ j, B i j * v j) * z i
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hTvar : ∀ (L : SpatialCoordinates d →L[ℝ] ℝ),
      Var[fun z => L (T z);
        SubdiffusiveProcess.Model.HeatSemigroupVec.gaussianVec d 0 1] =
        Var[fun x => L x; γ] := by
    intro L
    let v : SpatialCoordinates d := fun i => L (Pi.single i 1)
    have hLv : ∀ x, L x = ∑ i, v i * coord i x := by
      intro x
      conv_lhs => rw [← Finset.univ_sum_single x]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : L (Pi.single i (x i)) = (x i) * v i := by
        calc
          L (Pi.single i (x i)) = L ((x i) • (Pi.single i (1 : ℝ) : SpatialCoordinates d)) := by
            congr 1
            ext j
            by_cases hji : j = i <;> simp [hji]
          _ = (x i) * v i := by simp [v, smul_eq_mul]
      simpa [coord, mul_comm] using hi'
    have hleft : (fun z => L (T z)) =
        (fun z => ∑ i, v i * coord i (T z)) := by
      funext z
      exact hLv (T z)
    have hright : (fun x => L x) =
        (fun x => ∑ i, v i * coord i x) := by
      funext x
      exact hLv x
    have hTformFun : (fun z => ∑ i, v i * coord i (T z)) =
        (fun z => ∑ i, (Matrix.mulVec B v) i * coord i z) := by
      funext z
      exact hTform v z
    rw [hleft, hright, hTformFun]
    calc
      Var[fun z => ∑ i, (Matrix.mulVec B v) i * coord i z;
          SubdiffusiveProcess.Model.HeatSemigroupVec.gaussianVec d 0 1] =
          ∑ i, (Matrix.mulVec B v) i ^ 2 := hGcov (Matrix.mulVec B v)
      _ = dotProduct (star (Matrix.mulVec B v)) (Matrix.mulVec B v) := by
        simp [dotProduct, pow_two]
      _ = dotProduct (star v) (Matrix.mulVec (B.conjTranspose * B) v) := by
        calc
          dotProduct (star (Matrix.mulVec B v)) (Matrix.mulVec B v) =
              dotProduct (Matrix.vecMul (star (Matrix.mulVec B v)) B) v := by
                exact Matrix.dotProduct_mulVec (star (Matrix.mulVec B v)) B v
          _ = dotProduct (Matrix.vecMul (star v) (B.conjTranspose * B)) v := by
                rw [Matrix.star_mulVec, Matrix.vecMul_vecMul]
          _ = dotProduct (star v) (Matrix.mulVec (B.conjTranspose * B) v) := by
                symm
                exact Matrix.dotProduct_mulVec (star v) (B.conjTranspose * B) v
      _ = Var[fun x => ∑ i, v i * coord i x; γ] := by
        rw [← hAB]
        exact (hquad v).symm
  have hTmean : ∀ (L : SpatialCoordinates d →L[ℝ] ℝ),
      (∫ z, L (T z) ∂(SubdiffusiveProcess.Model.HeatSemigroupVec.gaussianVec d 0 1)) = L 0 := by
    intro L
    let G := SubdiffusiveProcess.Model.HeatSemigroupVec.gaussianVec d 0 1
    have hGid : Integrable id G :=
      Integrable.of_eval (fun i => by
        simpa [G, coord, id] using (hGcoord i).integrable (by norm_num))
    change (∫ z, (L.comp T) (id z) ∂G) = L 0
    rw [(L.comp T).integral_comp_comm hGid]
    have hGmean' : (∫ x, x ∂G) = 0 := by simpa [G] using hGmean
    rw [show (∫ x, id x ∂G) = 0 by simpa using hGmean']
    simp
  have hrepr : γ = (SubdiffusiveProcess.Model.HeatSemigroupVec.gaussianVec d 0 1).map
      (fun z => T z + m) := by
    have hmap : (SubdiffusiveProcess.Model.HeatSemigroupVec.gaussianVec d 0 1).map
          (fun z => T z + m) =
        ((SubdiffusiveProcess.Model.HeatSemigroupVec.gaussianVec d 0 1).map T).map
          (fun z => z + m) := by
      calc
        _ = (SubdiffusiveProcess.Model.HeatSemigroupVec.gaussianVec d 0 1).map
            ((fun z => z + m) ∘ T) := by
              congr 1
        _ = _ := by rw [Measure.map_map (by fun_prop) (by fun_prop)]
    refine Measure.ext_of_charFunDual ?_
    ext L
    rw [hγ.charFunDual_eq L]
    rw [hmap, charFunDual_map_add_const]
    rw [charFunDual_map]
    rw [hGgauss.charFunDual_eq]
    have hLm : (∫ x, L x ∂γ) = L m := by
      exact L.integral_comp_id_comm hγ.integrable_id
    have hcompmean : (∫ x, (L.comp T) x ∂
        (SubdiffusiveProcess.Model.HeatSemigroupVec.gaussianVec d 0 1)) = L 0 := by
      simpa [ContinuousLinearMap.comp_apply] using hTmean L
    have hcompvar : Var[L.comp T;
        SubdiffusiveProcess.Model.HeatSemigroupVec.gaussianVec d 0 1] = Var[L; γ] := hTvar L
    have hcompmeanC : (∫ x, (↑((L.comp T) x) : ℂ) ∂
        (SubdiffusiveProcess.Model.HeatSemigroupVec.gaussianVec d 0 1)) =
        (L 0 : ℂ) := by
      rw [integral_complex_ofReal]
      exact congrArg Complex.ofReal hcompmean
    have hLmC : (∫ x, (↑(L x) : ℂ) ∂γ) = (L m : ℂ) := by
      rw [integral_complex_ofReal]
      exact congrArg Complex.ofReal hLm
    rw [hLmC, hcompmeanC, hcompvar]
    rw [← Complex.exp_add]
    congr 1
    have hLzero : L (0 : SpatialCoordinates d) = 0 := map_zero L
    rw [hLzero]
    simp
    ring
  rw [hrepr]
  have hGac : SubdiffusiveProcess.Model.HeatSemigroupVec.gaussianVec d 0 1 ≪
      (volume : Measure (SpatialCoordinates d)) := by
    exact SubdiffusiveProcess.Probability.Diffusion.gaussianVec_absolutelyContinuous 0 (by norm_num)
  have hTac : (SubdiffusiveProcess.Model.HeatSemigroupVec.gaussianVec d 0 1).map T ≪
      (volume : Measure (SpatialCoordinates d)) := by
    have h₁ : (SubdiffusiveProcess.Model.HeatSemigroupVec.gaussianVec d 0 1).map T ≪
        (volume : Measure (SpatialCoordinates d)).map T := by
      apply (eT.toHomeomorph.measurableEmbedding.absolutelyContinuous_map hGac)
    have h₂ : (volume : Measure (SpatialCoordinates d)).map T ≪ volume := by
      rw [show (volume : Measure (SpatialCoordinates d)).map T =
        Measure.map Tlin volume by rfl]
      rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi hdetT]
      exact Measure.smul_absolutelyContinuous
    exact h₁.trans h₂
  rw [show (SubdiffusiveProcess.Model.HeatSemigroupVec.gaussianVec d 0 1).map
      (fun z => T z + m) =
      ((SubdiffusiveProcess.Model.HeatSemigroupVec.gaussianVec d 0 1).map T).map (fun z => z + m) by
        calc
          _ = (SubdiffusiveProcess.Model.HeatSemigroupVec.gaussianVec d 0 1).map
              ((fun z => z + m) ∘ T) := by
                congr 1
          _ = _ := by rw [Measure.map_map (by fun_prop) (by fun_prop)]]
  have hadd := (Homeomorph.addRight m).measurableEmbedding.absolutelyContinuous_map hTac
  have hadd' : Measure.map (fun z : SpatialCoordinates d => z + m)
      ((SubdiffusiveProcess.Model.HeatSemigroupVec.gaussianVec d 0 1).map T) ≪
      Measure.map (fun z : SpatialCoordinates d => z + m)
        (volume : Measure (SpatialCoordinates d)) := by
    simpa [Homeomorph.addRight] using hadd
  simpa only [map_add_right_eq_self (volume : Measure (SpatialCoordinates d)) m] using hadd'

theorem aux_lim_nongaussian_gaussian
    {d : ℕ} (_hd : 2 ≤ d) (γ μ lm : Measure (SpatialCoordinates d))
    (hγ : IsGaussian γ) (hμ : γ ≪ μ) (hlm : γ ≪ lm)
    (hlmsing : lm ⟂ₘ volume)
    [IsFiniteMeasureOnCompacts μ]
    (hμhyper : ∀ (L : SpatialCoordinates d →L[ℝ] ℝ) (_hL : L ≠ 0) (c : ℝ),
      μ {x | L x = c} = 0) :
    False := by
  classical
  let : IsProbabilityMeasure γ := hγ.toIsProbabilityMeasure
  have hsingγ : γ ⟂ₘ volume :=
    hlmsing.mono_ac hlm Measure.AbsolutelyContinuous.rfl
  have hvar : ∀ (L : SpatialCoordinates d →L[ℝ] ℝ) (hL : L ≠ 0),
      0 < Var[L; γ] := by
      intro L hL
      have hne : Var[L; γ] ≠ 0 := by
        intro hzero
        have hLp : MemLp L 2 γ := hγ.memLp_dual γ L 2 (by norm_num)
        have hevar : evariance L γ = 0 := by
          rw [variance] at hzero
          exact (ENNReal.toReal_eq_zero_iff _).mp hzero |>.resolve_right hLp.evariance_ne_top
        have hae : L =ᵐ[γ] (fun _ => γ[L]) :=
          (evariance_eq_zero_iff hLp.aemeasurable).mp hevar
        let c : ℝ := γ[L]
        have hlevel : γ {x : SpatialCoordinates d | L x = c} = 1 := by
          calc
            γ {x : SpatialCoordinates d | L x = c} = γ Set.univ := by
              apply measure_congr
              filter_upwards [hae] with x hx
              apply propext
              constructor
              · intro _
                exact Set.mem_univ x
              · intro _
                simpa [c] using hx
            _ = 1 := measure_univ
        have hlevelμ : μ {x : SpatialCoordinates d | L x = c} = 0 :=
          hμhyper L hL c
        have hlevelγ : γ {x : SpatialCoordinates d | L x = c} = 0 := hμ hlevelμ
        rw [hlevel] at hlevelγ
        exact one_ne_zero hlevelγ
      exact lt_of_le_of_ne (variance_nonneg L γ) (Ne.symm hne)
  have hγac : γ ≪ volume := aux_lim_nongaussian_gaussian_ac γ hγ hvar
  have hγzero : γ = 0 :=
    Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular hγac hsingγ
  have hγuniv : γ Set.univ = 1 := by simp
  rw [hγzero] at hγuniv
  simp at hγuniv

theorem lim_nongaussian
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd) (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M Jc Sreg),
        M.delta ≤ delta0 →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_hH : InfraredCharacterization M H)
        (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
        (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
        (hKN : ∀ N, IsMarkovKernel (KN N))
        (_hin : in_crossing M H PN KN)
        (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d)
          (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
        (_hL : ∀ N omega x,
          Measure.map MarkovProcess.LifetimePath.ofContinuousPath (KN N (omega, x)) =
            L N omega x)
        (_hLloc : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
          SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusion
            (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (L N omega))
        (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
        (hK : IsMarkovKernel K)
        (_hconv : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ B : Set (SpatialCoordinates d), IsCompact B →
            ∀ epsilon : ℝ, 0 < epsilon → ∃ N0 : ℕ, ∀ N, N0 ≤ N → ∀ x ∈ B,
              pathLevyProkhorovDist
                (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
                (jointPathProbabilityMeasure K hK omega x) < epsilon),
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (x : SpatialCoordinates d) (t : ℝ≥0), 0 < t →
            ¬ IsGaussian ((K (omega, x)).map (fun w : DiffusionPath d => w t)) := by
  obtain ⟨deltaM, hdeltaM, hM⟩ := lim_measure (d := d) hd
  have heps : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> norm_num
  have hp : (d : ℝ) < ((2 * d + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) := by
    norm_num
    nlinarith
  obtain ⟨deltaT, hdeltaT, hT⟩ :=
    lim_transition_domination (d := d) hd Jc Pc Xc Sf W Cp
  obtain ⟨deltaG, hdeltaG, hG⟩ :=
    prop_chaos_growth (d := d) hd (1 / 2 : ℝ) heps (2 * d + 1) hp
  refine ⟨min deltaM (min deltaT deltaG), ?_, ?_⟩
  · exact lt_min hdeltaM (lt_min hdeltaT hdeltaG)
  · intro M Rm Sreg It hdM
    have hdM_M : M.delta ≤ deltaM := le_trans hdM (min_le_left _ _)
    have hdM_T : M.delta ≤ deltaT := le_trans hdM (le_trans (min_le_right _ _) (min_le_left _ _))
    have hdM_G : M.delta ≤ deltaG := le_trans hdM (le_trans (min_le_right _ _) (min_le_right _ _))
    intro H hH PN KN hKN hin L hL hLloc K hK hconv
    obtain ⟨Mlim, hMlim_meas, hMlim_ae, hMlim_nondet, hMlim_mean, hMlim_stat,
      hMlim_indep⟩ := hM M H hH hdM_M
    obtain ⟨mu, hmu_meas, hmu_ae, hmu_growth⟩ := hG M H hH hdM_G
    have hTD := hT M Rm Sreg It hdM_T H hH PN KN hKN hin L hL hLloc K hK hconv
    have hgrowth_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧
          ∀ x ∈ Metric.closedBall (0 : SpatialCoordinates d) n, ∀ r : ℝ,
            0 < r → r ≤ 1 → mu omega (Metric.ball x r) ≤
              ENNReal.ofReal (C * r ^ ((d : ℝ) - (1 / 2 : ℝ))) := by
      apply ae_all_iff.2
      intro n
      obtain ⟨C, hCmem, hCae⟩ := hmu_growth (Metric.closedBall (0 : SpatialCoordinates d) n)
        (Metric.isBounded_closedBall)
      filter_upwards [hCae] with omega hω
      refine ⟨C omega, hω.1, ?_⟩
      intro x hx r hr hr1
      exact hω.2.2 x hx r hr hr1
    filter_upwards [hTD, hMlim_ae, hmu_ae, hgrowth_ae] with omega hTDω hMω hmuω hgrowthω
    obtain ⟨hcut, hweighted, hfinM, hnoM, hopenM, hsingM,
      hfinW, hnoW, hopenW, hsingW⟩ := hMω
    obtain ⟨hmuconv, hmuloc, hmuopen, hmuno, hmufront⟩ := hmuω
    let : IsLocallyFiniteMeasure (mu omega) := hmuloc
    intro x t ht hgauss
    let μsing : Measure (SpatialCoordinates d) :=
      (Mlim omega).withDensity (fun y => ENNReal.ofReal (Real.exp (H omega y)))
    have hconv_sing : MeasuresConvergeLocally
        (fun N => cutoffSpeedMeasure M H omega N) (μsing) := by
      apply measuresConvergeLocally_congr
        (fun N => weightedChaosCutoff M H N omega)
        (fun N => cutoffSpeedMeasure M H omega N) μsing
        (fun N => (cutoffSpeedMeasure_eq_weightedChaosCutoff M H omega N).symm)
      exact hweighted
    have hconv_growth : MeasuresConvergeLocally
        (fun N => cutoffSpeedMeasure M H omega N) (mu omega) := by
      apply measuresConvergeLocally_congr
        (fun N => weightedChaosCutoff M H N omega)
        (fun N => cutoffSpeedMeasure M H omega N) (mu omega)
        (fun N => (cutoffSpeedMeasure_eq_weightedChaosCutoff M H omega N).symm)
      exact hmuconv
    have hac_sing := hTDω μsing hconv_sing x t ht
    have hac_growth := hTDω (mu omega) hconv_growth x t ht
    have hsing : μsing ⟂ₘ volume := hsingW
    have hnot := aux_lim_nongaussian_hyperplane_null hd (mu omega)
      ((d : ℝ) - (1 / 2 : ℝ))
      (by
        have hdreal : (1 : ℝ) ≤ d := by
          exact_mod_cast (show 1 ≤ d by omega)
        linarith)
      hgrowthω
    exact aux_lim_nongaussian_gaussian hd
      ((K (omega, x)).map (fun w : DiffusionPath d => w t)) (mu omega) μsing
      hgauss hac_growth hac_sing hsing hnot

end SubdiffusiveProcess.Paper
