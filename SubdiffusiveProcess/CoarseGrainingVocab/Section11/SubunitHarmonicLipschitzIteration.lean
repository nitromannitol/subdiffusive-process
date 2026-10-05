module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonicInterior
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.OneStep
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# The Lipschitz endpoint from uniform gradient averages

The exact harmonic-comparison factor is iterated with summable coefficient
oscillations. Uniform gradient averages then give a common Campanato bound
for every exponent below one, for the same continuous representative.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section11.HarmonicLipschitz
open MeasureTheory Homogenization Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonic
noncomputable section


theorem le_exp_sum_of_mul_recursion {a b : ℕ → ℝ}
 (ha : ∀ n, 0≤a n) (_hb : ∀ n, 0≤b n)
 (hrec : ∀ n, a (n+1)≤(1+b n)*a n) (n : ℕ) :
 a n≤Real.exp (∑ i∈Finset.range n,b i)*a 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (1 + b n) ≤ Real.exp (b n) := by
      simpa only [add_comm] using! Real.add_one_le_exp (b n)
    have h2 : (1 + b n) * a n ≤ Real.exp (b n) * a n :=
      mul_le_mul_of_nonneg_right h1 (ha n)
    have h3 : a (n+1) ≤ Real.exp (b n) * a n := le_trans (hrec n) h2
    have h4 : Real.exp (b n) * a n ≤
        Real.exp (b n) * (Real.exp (∑ i∈Finset.range n, b i) * a 0) :=
      mul_le_mul_of_nonneg_left ih (Real.exp_pos (b n)).le
    have h5 : a (n+1) ≤ Real.exp (b n) * (Real.exp (∑ i∈Finset.range n, b i) * a 0) :=
      le_trans h3 h4
    rw [Finset.sum_range_succ, Real.exp_add]
    linarith [h5]

theorem le_exp_of_dyadic_mul_recursion {a : ℕ → ℝ} {M : ℝ}
 (ha : ∀ n, 0≤a n) (hM : 0≤M)
 (hrec : ∀ n, a (n+1)≤(1+M*(1/2:ℝ)^n)*a n) (n : ℕ) :
 a n≤Real.exp (2*M)*a 0 := by
  have hhalf : 0 ≤ (1/2:ℝ) := by norm_num
  have hb : ∀ i, 0 ≤ M*(1/2:ℝ)^i := fun i => mul_nonneg hM (pow_nonneg hhalf i)
  calc a n ≤ Real.exp (∑ i∈Finset.range n, M*(1/2:ℝ)^i)*a 0 :=
      le_exp_sum_of_mul_recursion ha hb hrec n
    _ ≤ Real.exp (2*M)*a 0 := by
        refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (ha 0)
        have hsum : ∑ i∈Finset.range n, M*(1/2:ℝ)^i
            = M * ∑ i∈Finset.range n, (1/2:ℝ)^i := by
          rw [Finset.mul_sum]
        rw [hsum]
        calc M * ∑ i∈Finset.range n, (1/2:ℝ)^i
            ≤ M * 2 := by
              exact mul_le_mul_of_nonneg_left (sum_geometric_two_le n) hM
          _ ≤ 2 * M := le_of_eq (mul_comm M 2)

theorem le_mul_of_le_mul_rpow {A K r : ℝ} (hr : 0≤r)
 (h : ∀ alpha : ℝ, alpha∈Set.Ico (1/2:ℝ) 1 → A≤K*r^alpha) :
 A≤K*r := by
  rcases eq_or_lt_of_le hr with rfl | hr0
  · have hh := h (1/2) ⟨by norm_num, by norm_num⟩
    simpa using! hh
  · have hc : ContinuousAt (fun alpha:ℝ => K*r^alpha) 1 :=
      continuousAt_const.mul (continuousAt_const.rpow continuousAt_id (Or.inl hr0.ne'))
    have ht : Tendsto (fun alpha:ℝ=>K*r^alpha) (𝓝[Set.Iio 1] 1) (𝓝 (K*r)) :=
      by simpa only [Real.rpow_one] using! (hc.tendsto.mono_left nhdsWithin_le_nhds)
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin,
      (nhdsWithin_le_nhds (Ici_mem_nhds (by norm_num : (1/2:ℝ)<1)) : Set.Ici (1/2:ℝ) ∈ 𝓝[Set.Iio 1] 1)] with a ha1 ha0
    exact h a ⟨ha0,ha1⟩

theorem interiorGradientScaleBound_of_uniform {d : ℕ} {K alpha : ℝ}
    {u : H1Function (smallContrastUnitBall d)}
    (halpha : alpha ≤ 1)
    (hg : ∀ z ∈ smallContrastBall d (1/2), ∀ r : ℝ, 0 < r → r ≤ 1/2 →
      vectorNormalizedL2On (euclideanBall z r) u.grad ≤ K) :
    HasInteriorSmallContrastGradientScaleBound alpha K u := by
  intro z hz r hr hrhalf
  have hexp : 0 ≤ 1 - alpha := by linarith
  have hrpow_le_one : r ^ (1 - alpha) ≤ 1 :=
    Real.rpow_le_one hr.le (by linarith : r ≤ 1) hexp
  have hgnonneg : 0 ≤ vectorNormalizedL2On (euclideanBall z r) u.grad :=
    Real.sqrt_nonneg _
  calc r ^ (1 - alpha) * vectorNormalizedL2On (euclideanBall z r) u.grad
      ≤ 1 * vectorNormalizedL2On (euclideanBall z r) u.grad :=
        mul_le_mul_of_nonneg_right hrpow_le_one hgnonneg
    _ = vectorNormalizedL2On (euclideanBall z r) u.grad := by ring
    _ ≤ K := hg z hz r hr hrhalf

theorem campanatoRepresentative_lipschitz_of_uniform_gradient {d : ℕ} [NeZero d]
 {K : ℝ} {u : H1Function (smallContrastUnitBall d)} (hK : 0≤K)
 (hg : ∀ z∈smallContrastBall d (1/2), ∀ r:ℝ, 0<r → r≤1/2 →
 vectorNormalizedL2On (euclideanBall z r) u.grad≤K)
 {x y : Vec d} (hx : x∈smallContrastBall d (1/2)) (hy : y∈smallContrastBall d (1/2)) :
 |smallContrastCampanatoRepresentative (d:=d) u.toFun x-
 smallContrastCampanatoRepresentative (d:=d) u.toFun y|≤
 (smallContrastHolderChainLength d:ℝ)*smallContrastLocalHolderConstant d*K*‖x-y‖ := by
  apply le_mul_of_le_mul_rpow (norm_nonneg _)
  intro alpha halpha
  have hgrad := interiorGradientScaleBound_of_uniform (halpha.2.le) hg
  have hcamp := ballCampanatoBound_of_interiorGradient halpha hgrad
  exact holder_smallContrastCampanatoRepresentative halpha hK hcamp x hx y hy

theorem oneStep_scalar_normalizedGradient_half {d : ℕ} [NeZero d]
    {s : Vec d → ℝ} {z : Vec d} {r delta kappa : ℝ} (hr : 0 < r)
    {u : H1Function (euclideanBall z r)}
    (hs : ContinuousOn s (euclideanBall z r))
    (hu : IsWeaklyHarmonicOn s (euclideanBall z r) u)
    (hd0 : 0 ≤ delta) (hdthr : delta ≤ smallContrastThreshold d (1/2:ℝ)) (hd1 : delta < 1)
    (hclose : ∀ y ∈ euclideanBall z r, |kappa⁻¹ * s y - 1| ≤ delta) :
    vectorNormalizedL2On (euclideanBall z (r/2)) u.grad ≤
      (1 + 2 * delta * (1/2:ℝ)^(-(d:ℝ)/2)) * vectorNormalizedL2On (euclideanBall z r) u.grad := by
  -- The rescaled coefficient field b := fun y => kappa⁻¹ * s y is continuous.
  have hbc : ContinuousOn (fun y => kappa⁻¹ * s y) (euclideanBall z r) :=
    continuousOn_const.mul hs
  -- From the closeness hypothesis we get two-sided bounds on b.
  have hbnd : ∀ y ∈ euclideanBall z r,
      (1 - delta) ≤ kappa⁻¹ * s y ∧ kappa⁻¹ * s y ≤ (1 + delta) := by
    intro y hy
    have habs := hclose y hy
    have ⟨hlo, hhi⟩ := abs_le.mp habs
    constructor
    · linarith
    · linarith
  have hlam : 0 < (1 - delta : ℝ) := by linarith
  -- Measurability of the ball.
  have hW : MeasurableSet (euclideanBall z r) :=
    (isOpen_euclideanBall z r).measurableSet
  -- Ellipticity of the scalar coefficient field b on the ball.
  have hEll := isEllipticFieldOn_scalarCoeffField_of_continuousOn hW hbc hlam hbnd
  -- Coefficient-identity distance estimate.
  have hdist := coefficientIdentityDistanceLE_scalarCoeffField hW hclose
  -- The rescaled weakly harmonic function is still weakly harmonic for b.
  have hnorm := IsWeaklyHarmonicOn.const_inv_mul kappa hu
  have hmatrix := isMatrixDivFormWeakSolutionOn_zero_of_isWeaklyHarmonicOn hnorm
  -- The forcing term is the zero function, which is in L².
  have hfzero : MemVectorL2 (euclideanBall z r) (fun _ => (0 : Vec d)) := by
    simp [MemVectorL2]
  -- Apply the one-step half-ball estimate with the zero forcing term.
  have hstep := oneStep_normalizedGradient_half z hr hEll hdist
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1) hd0 hdthr hmatrix hfzero
  -- The zero forcing contribution vanishes, leaving exactly the claimed bound.
  simpa [vectorNormalizedL2On, normalizedL2On, volumeAverage, euclideanNorm,
    vecNormSq, vecDot] using! hstep

theorem abs_normalized_sub_one_le_twice_log_lipschitz {d : ℕ}
    {s : Vec d → ℝ} {z : Vec d} {r L : ℝ}
    (hr : 0 < r) (hL : 0 ≤ L) (hsmall : L * r ≤ 1)
    (hsz : 0 < s z) (hpos : ∀ y ∈ euclideanBall z r, 0 < s y)
    (hlog : ∀ y ∈ euclideanBall z r, |Real.log (s y) - Real.log (s z)| ≤ L * ‖y - z‖) :
    ∀ y ∈ euclideanBall z r, |(s z)⁻¹ * s y - 1| ≤ 2 * L * r := by
  intro y hy
  have hdist : ‖y - z‖ ≤ r := by
    have h1 := euclideanBall_subset_metricBall hr hy
    rw [mem_ball_iff_norm] at h1
    exact le_of_lt h1
  have h1 : |Real.log (s y) - Real.log (s z)| ≤ L * ‖y - z‖ := hlog y hy
  have h2 : L * ‖y - z‖ ≤ L * r := mul_le_mul_of_nonneg_left hdist hL
  have habs1 : |Real.log (s y) - Real.log (s z)| ≤ 1 := by linarith
  have hnz : 0 < s z := hsz
  have hny : 0 < s y := hpos y hy
  have hratio : (s z)⁻¹ * s y = Real.exp (Real.log (s y) - Real.log (s z)) := by
    rw [Real.exp_sub, Real.exp_log hny, Real.exp_log hnz]
    field_simp
  have h2pos : (0 : ℝ) ≤ 2 := by norm_num
  calc |(s z)⁻¹ * s y - 1|
      = |Real.exp (Real.log (s y) - Real.log (s z)) - 1| := by rw [hratio]
    _ ≤ 2 * |Real.log (s y) - Real.log (s z)| :=
      Real.abs_exp_sub_one_le habs1
    _ ≤ 2 * (L * ‖y - z‖) := mul_le_mul_of_nonneg_left h1 h2pos
    _ ≤ 2 * (L * r) := mul_le_mul_of_nonneg_left h2 h2pos
    _ = 2 * L * r := by ring

theorem linear_dyadic_contrast_le {d : ℕ} {D : ℝ} (hD : 0≤D)
 (hsmall : D≤ smallContrastThreshold d (1/2:ℝ)) (n : ℕ) :
 0≤D*(1/2:ℝ)^n ∧ D*(1/2:ℝ)^n≤ smallContrastThreshold d (1/2:ℝ) := by
  constructor
  · exact mul_nonneg hD (pow_nonneg (by norm_num) n)
  · have hpow : (1/2:ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h1 : D*(1/2:ℝ)^n ≤ D*1 := mul_le_mul_of_nonneg_left hpow hD
    have h2 : D*(1/2:ℝ)^n ≤ D := by simpa using! h1
    exact h2.trans hsmall

theorem exists_lipschitz_representative_of_uniform_gradient {d : ℕ} [NeZero d]
 {K : ℝ} {u : H1Function (smallContrastUnitBall d)} (hK : 0≤K)
 (hg : ∀ z∈smallContrastBall d (1/2), ∀ r:ℝ, 0<r → r≤1/2 →
 vectorNormalizedL2On (euclideanBall z r) u.grad≤K) :
 ∃ g : Vec d → ℝ, ContinuousOn g (smallContrastBall d (1/2)) ∧
 g=ᵐ[volume.restrict (smallContrastUnitBall d)]u.toFun ∧
 EuclideanHolderBoundOn (smallContrastBall d (1/2)) 1
 ((smallContrastHolderChainLength d:ℝ)*smallContrastLocalHolderConstant d*K) g := by
  have halpha : (1/2:ℝ) ∈ Set.Ico (1/2:ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hgrad := interiorGradientScaleBound_of_uniform (d:=d) (K:=K) (u:=u) halpha.2.le hg
  have hcamp := ballCampanatoBound_of_interiorGradient halpha hgrad
  refine ⟨smallContrastSchauderRepresentative u,
    continuousOn_smallContrastSchauderRepresentative halpha hK hcamp,
    smallContrastSchauderRepresentative_ae_eq halpha hcamp, ?_⟩
  intro x hx y hy
  have hcoef : 0 ≤ (smallContrastHolderChainLength d:ℝ)*smallContrastLocalHolderConstant d*K := by
    exact mul_nonneg (mul_nonneg (by exact_mod_cast Nat.zero_le _) (smallContrastLocalHolderConstant_nonneg d)) hK
  have hlip := campanatoRepresentative_lipschitz_of_uniform_gradient (d:=d) hK hg hx hy
  rw [smallContrastSchauderRepresentative_of_mem hx, smallContrastSchauderRepresentative_of_mem hy]
  rw [Real.rpow_one]
  calc |smallContrastCampanatoRepresentative (d:=d) u.toFun x -
        smallContrastCampanatoRepresentative (d:=d) u.toFun y|
      ≤ (smallContrastHolderChainLength d:ℝ)*smallContrastLocalHolderConstant d*K*‖x-y‖ := hlip
    _ ≤ (smallContrastHolderChainLength d:ℝ)*smallContrastLocalHolderConstant d*K*
        euclideanNorm (x - y) := by
        exact mul_le_mul_of_nonneg_left (norm_le_euclideanNorm (x - y)) hcoef


end
end SubdiffusiveProcess.CoarseGrainingVocab.Section11.HarmonicLipschitz
