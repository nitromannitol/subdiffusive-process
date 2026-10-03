module

public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.CommonScaleLaw
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.InfraredPartialSum
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Sobolev.PotentialResponses
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Analysis.CompactShellSummability
public import SubdiffusiveProcess.Probability.NativeShellSummability
public import SubdiffusiveProcess.Probability.CopyLayerBlock
public import SubdiffusiveProcess.Probability.CommonScaleReindex
public import SubdiffusiveProcess.Sobolev.DirichletResponseLpDifference
public import SubdiffusiveProcess.Sobolev.InverseResponseLpDifference
public import SubdiffusiveProcess.Probability.AbsoluteSeries
public import SubdiffusiveProcess.Paper.cor_14
public import SubdiffusiveProcess.Paper.lem_infrared
public import SubdiffusiveProcess.Paper.layer_regularity_moments

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Topology
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

noncomputable section
namespace Paper

lemma aux_prop_16_coarse_block_dirichlet_one_sided
    (s x y : ℝ) (hs : 0 ≤ s)
    (hxy : Real.exp (-s) * x ≤ y) :
    x - y ≤ s * |x| := by
  have hexp : Real.exp (-s) ≤ 1 := by
    calc
      Real.exp (-s) ≤ Real.exp 0 :=
        Real.exp_le_exp.mpr (neg_nonpos.mpr hs)
      _ = 1 := Real.exp_zero
  have hlinear : 1 - Real.exp (-s) ≤ s := by
    have htangent : -s + 1 ≤ Real.exp (-s) := Real.add_one_le_exp (-s)
    linarith
  calc
    x - y ≤ x - Real.exp (-s) * x := sub_le_sub_left hxy x
    _ = (1 - Real.exp (-s)) * x := by ring
    _ ≤ (1 - Real.exp (-s)) * |x| :=
      mul_le_mul_of_nonneg_left (le_abs_self x) (sub_nonneg.mpr hexp)
    _ ≤ s * |x| := mul_le_mul_of_nonneg_right hlinear (abs_nonneg x)

lemma aux_prop_16_coarse_block_dirichlet_abs_sub
    (s x y : ℝ) (hs : 0 ≤ s)
    (hxy : Real.exp (-s) * x ≤ y)
    (hyx : Real.exp (-s) * y ≤ x) :
    |x - y| ≤ s * (|x| + |y|) := by
  have h1 : x - y ≤ s * |x| :=
    aux_prop_16_coarse_block_dirichlet_one_sided s x y hs hxy
  have h2 : y - x ≤ s * |y| :=
    aux_prop_16_coarse_block_dirichlet_one_sided s y x hs hyx
  have hx : 0 ≤ s * |x| := mul_nonneg hs (abs_nonneg x)
  have hy : 0 ≤ s * |y| := mul_nonneg hs (abs_nonneg y)
  rw [mul_add]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma aux_prop_16_coarse_block_dirichlet_exp_response_difference
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (S : ResponseSpace Q) (L : S.space →L[ℝ] ℝ)
    (b : weakSobolevGraph Q) (dirichlet : Bool)
    (u v : Lp ℝ ∞ (volume.restrict (Q : Set (SpatialCoordinates d)))) :
    |(if dirichlet then dirichletResponse S (expPotentialCoefficient u) b
      else inverseResponse S (expPotentialCoefficient u) L) -
      (if dirichlet then dirichletResponse S (expPotentialCoefficient v) b
      else inverseResponse S (expPotentialCoefficient v) L)| ≤
      ‖u - v‖ *
        ((if dirichlet then dirichletResponse S (expPotentialCoefficient u) b
          else inverseResponse S (expPotentialCoefficient u) L) +
         (if dirichlet then dirichletResponse S (expPotentialCoefficient v) b
          else inverseResponse S (expPotentialCoefficient v) L)) := by
  have hsupp : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      x ∉ (Set.univ : Set (SpatialCoordinates d)) →
        (0 : Lp ℝ ∞ (volume.restrict (Q : Set (SpatialCoordinates d)))) x = 0 := by
    refine Eventually.of_forall ?_
    intro x hx
    exact (hx (Set.mem_univ x)).elim
  obtain ⟨_, _, hInv, hDir⟩ :=
    cor_14.1 d Q S 0 0 Set.univ MeasurableSet.univ hsupp L b
  have hrev : ‖v - u‖ = ‖u - v‖ := norm_sub_rev v u
  cases dirichlet with
  | false =>
      change |inverseResponse S (expPotentialCoefficient u) L -
          inverseResponse S (expPotentialCoefficient v) L| ≤
        ‖u - v‖ * (inverseResponse S (expPotentialCoefficient u) L +
          inverseResponse S (expPotentialCoefficient v) L)
      have hh := aux_prop_16_coarse_block_dirichlet_abs_sub
        ‖u - v‖ (inverseResponse S (expPotentialCoefficient u) L)
          (inverseResponse S (expPotentialCoefficient v) L)
          (norm_nonneg (u - v))
          (by simpa only [hrev] using (hInv v u).1) (hInv u v).1
      simpa only [abs_of_nonneg (inverseResponse_nonneg S _ L),
        abs_of_nonneg (inverseResponse_nonneg S _ L)] using hh
  | true =>
      change |dirichletResponse S (expPotentialCoefficient u) b -
          dirichletResponse S (expPotentialCoefficient v) b| ≤
        ‖u - v‖ * (dirichletResponse S (expPotentialCoefficient u) b +
          dirichletResponse S (expPotentialCoefficient v) b)
      have hh := aux_prop_16_coarse_block_dirichlet_abs_sub
        ‖u - v‖ (dirichletResponse S (expPotentialCoefficient u) b)
          (dirichletResponse S (expPotentialCoefficient v) b)
          (norm_nonneg (u - v))
          (by simpa only [hrev] using (hDir v u).1) (hDir u v).1
      simpa only [abs_of_nonneg (dirichletResponse_nonneg S _ b),
        abs_of_nonneg (dirichletResponse_nonneg S _ b)] using hh

lemma aux_prop_16_coarse_block_dirichlet_holder
    {A : Type*} [MeasurableSpace A] (mu : Measure A)
    (p : ℝ) (hp : 0 < p) (f g : A → ℝ)
    (hf : AEStronglyMeasurable f mu)
    (hg : AEStronglyMeasurable g mu) :
    eLpNorm (fun x : A => f x * g x) (ENNReal.ofReal (2 * p)) mu ≤
      eLpNorm f (ENNReal.ofReal (6 * p)) mu *
        eLpNorm g (ENNReal.ofReal (3 * p)) mu := by
  have hp2 : 0 < 2 * p := by linarith
  have hp3 : 0 < 3 * p := by linarith
  have hp6 : 0 < 6 * p := by linarith
  have hp26 : 2 * p < 6 * p := by linarith
  have hpne : p ≠ 0 := ne_of_gt hp
  have h2ne : ENNReal.ofReal (2 * p) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hp2)
  have h3ne : ENNReal.ofReal (3 * p) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hp3)
  have h6ne : ENNReal.ofReal (6 * p) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hp6)
  have hexponents : 1 / (2 * p) = 1 / (6 * p) + 1 / (3 * p) := by
    field_simp [hpne] <;> ring
  change eLpNorm (f * g) (ENNReal.ofReal (2 * p)) mu ≤
    eLpNorm f (ENNReal.ofReal (6 * p)) mu * eLpNorm g (ENNReal.ofReal (3 * p)) mu
  rw [eLpNorm_eq_eLpNorm' h2ne ENNReal.ofReal_ne_top (hf.mul hg),
    eLpNorm_eq_eLpNorm' h6ne ENNReal.ofReal_ne_top hf,
    eLpNorm_eq_eLpNorm' h3ne ENNReal.ofReal_ne_top hg,
    ENNReal.toReal_ofReal hp2.le,
    ENNReal.toReal_ofReal hp6.le,
    ENNReal.toReal_ofReal hp3.le]
  have hHolder :
      eLpNorm' (f • g) (2 * p) mu ≤
        eLpNorm' f (6 * p) mu * eLpNorm' g (3 * p) mu :=
    eLpNorm'_smul_le_mul_eLpNorm' (f := g) (φ := f)
      hg hf hp2 hp26 hexponents
  exact hHolder

lemma aux_prop_16_coarse_block_dirichlet_moment
    {A : Type*} [MeasurableSpace A] (mu : Measure A)
    (p K B : ℝ) (hp : 2 ≤ p) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (T X Y : A → ℝ)
    (hT : MemLp T (ENNReal.ofReal (6 * p)) mu)
    (hX : MemLp X (ENNReal.ofReal (3 * p)) mu)
    (hY : MemLp Y (ENNReal.ofReal (3 * p)) mu)
    (hTbound : eLpNorm T (ENNReal.ofReal (6 * p)) mu ≤ ENNReal.ofReal K)
    (hXbound : eLpNorm X (ENNReal.ofReal (3 * p)) mu ≤ ENNReal.ofReal B)
    (hYbound : eLpNorm Y (ENNReal.ofReal (3 * p)) mu ≤ ENNReal.ofReal B)
    (hpoint : ∀ᵐ x ∂mu, |X x - Y x| ≤ T x * (|X x| + |Y x|)) :
    eLpNorm (fun x : A => X x - Y x) (ENNReal.ofReal (2 * p)) mu ≤
      ENNReal.ofReal (K * (2 * B)) := by
  have hp0 : 0 < p := by linarith
  have hp3real : (1 : ℝ) ≤ 3 * p := by linarith
  have hp3 : 1 ≤ ENNReal.ofReal (3 * p) := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp3real
  let W : A → ℝ := fun x : A => ‖X x‖ + ‖Y x‖
  have hWm : AEStronglyMeasurable W mu :=
    hX.aestronglyMeasurable.norm.add hY.aestronglyMeasurable.norm
  have hWbound : eLpNorm W (ENNReal.ofReal (3 * p)) mu ≤
      ENNReal.ofReal (2 * B) := by
    calc
      eLpNorm W (ENNReal.ofReal (3 * p)) mu ≤
          eLpNorm X (ENNReal.ofReal (3 * p)) mu +
            eLpNorm Y (ENNReal.ofReal (3 * p)) mu := by
        have hsum := eLpNorm_add_le (μ := mu)
          (f := fun x => ‖X x‖) (g := fun x => ‖Y x‖) hp3
        rw [eLpNorm_norm X hX.aestronglyMeasurable,
          eLpNorm_norm Y hY.aestronglyMeasurable] at hsum
        exact hsum
      _ ≤ ENNReal.ofReal B + ENNReal.ofReal B := add_le_add hXbound hYbound
      _ = ENNReal.ofReal (2 * B) := by
        rw [← ENNReal.ofReal_add hB hB]
        congr 1
        ring
  have hdom : ∀ᵐ x ∂mu, ‖X x - Y x‖ ≤ T x * W x := by
    filter_upwards [hpoint] with x hx
    simpa only [W, Real.norm_eq_abs] using hx
  calc
    eLpNorm (fun x : A => X x - Y x) (ENNReal.ofReal (2 * p)) mu ≤
        eLpNorm (fun x : A => T x * W x) (ENNReal.ofReal (2 * p)) mu :=
      eLpNorm_mono_ae_real (hX.aestronglyMeasurable.sub hY.aestronglyMeasurable) hdom
    _ ≤ eLpNorm T (ENNReal.ofReal (6 * p)) mu *
        eLpNorm W (ENNReal.ofReal (3 * p)) mu :=
      aux_prop_16_coarse_block_dirichlet_holder mu p hp0 T W
        hT.aestronglyMeasurable hWm
    _ ≤ ENNReal.ofReal K * ENNReal.ofReal (2 * B) :=
      mul_le_mul' hTbound hWbound
    _ = ENNReal.ofReal (K * (2 * B)) := (ENNReal.ofReal_mul hK).symm

lemma aux_prop_16_coarse_block_dirichlet_g2_integral
    {d : ℕ} (delta : ℝ) (hdelta : 0 < delta)
    (Praw : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d))
    (G2 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2 d delta Praw) :
    Integrable SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure ∧
      ∫ g, SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable g
          ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure ≤ 2 * delta := by
  let X : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ :=
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
  let E : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ := fun g =>
    Real.exp ((delta⁻¹ * max (X g) 0) ^ (2 : ℕ))
  have hXnonneg : ∀ g, 0 ≤ X g :=
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable_nonneg
  have hpoint : ∀ g, X g ≤ delta * E g := by
    intro g
    let y := delta⁻¹ * X g
    have hy : 0 ≤ y := mul_nonneg (inv_nonneg.mpr hdelta.le) (hXnonneg g)
    have hxy : X g = delta * y := by
      dsimp [y]
      field_simp
    have hyexp := Real.add_one_le_exp (y ^ 2)
    have hyle : y ≤ Real.exp (y ^ 2) := by
      nlinarith [hyexp, sq_nonneg (y - (1 / 2 : ℝ))]
    rw [hxy]
    calc
      delta * y ≤ delta * Real.exp (y ^ 2) :=
        mul_le_mul_of_nonneg_left hyle hdelta.le
      _ = delta * E g := by simp [E, y, max_eq_left (hXnonneg g)]
  have hEint : Integrable E
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure := by
    simpa [E, X, SubdiffusiveProcess.OGammaLE] using G2.regularity_expectation.1
  have hXint : Integrable X
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure := by
    apply (hEint.const_mul delta).mono'
    · exact SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable_measurable.aestronglyMeasurable
    · filter_upwards with g
      rw [Real.norm_of_nonneg (hXnonneg g)]
      exact hpoint g
  refine ⟨hXint, ?_⟩
  calc
    ∫ g, X g ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure ≤
        ∫ g, delta * E g ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure :=
      integral_mono_ae hXint (hEint.const_mul delta)
        (Filter.Eventually.of_forall hpoint)
    _ = delta * ∫ g, E g
          ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure :=
      integral_const_mul delta E
    _ ≤ delta * 2 := mul_le_mul_of_nonneg_left (by
      simpa [E, X, SubdiffusiveProcess.OGammaLE] using G2.regularity_expectation.2) hdelta.le
    _ = 2 * delta := by ring

lemma aux_prop_16_coarse_block_dirichlet_raw_lipschitz
    {d : ℕ} (delta : ℝ) (hdelta : 0 < delta)
    (Praw : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d))
    (G1 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 d Praw)
    (G2 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2 d delta Praw)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ W : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ≥0,
      Integrable (fun g => (W g : ℝ))
          (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure ∧
      ∀ g, LipschitzOnWith (W g) (fun x => g x)
        (Metric.closedBall (0 : SpatialCoordinates d) R) := by
  classical
  let μ₀ : Measure (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :=
    (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure
  obtain ⟨S₀, hS₀⟩ :=
    (isCompact_closedBall (0 : SpatialCoordinates d) R).elim_finite_subcover
      (fun z : SpatialCoordinates d => Metric.ball z (1 / 4 : ℝ))
      (fun _ => Metric.isOpen_ball) (by
        intro x hx
        exact mem_iUnion.2 ⟨x, Metric.mem_ball_self (by norm_num)⟩)
  let S : Finset (SpatialCoordinates d) := insert 0 S₀
  have hSne : S.Nonempty := ⟨0, Finset.mem_insert_self 0 S₀⟩
  have hS : Metric.closedBall (0 : SpatialCoordinates d) R ⊆
      ⋃ z ∈ S, Metric.ball z (1 / 4 : ℝ) := by
    intro x hx
    obtain ⟨z, hzS₀, hzx⟩ : ∃ z, ∃ (_ : z ∈ S₀),
        x ∈ Metric.ball z (1 / 4 : ℝ) := by
      simpa only [mem_iUnion] using hS₀ hx
    exact mem_iUnion.2 ⟨z, mem_iUnion.2 ⟨Finset.mem_insert_of_mem hzS₀, hzx⟩⟩
  have hball_cube {z x : SpatialCoordinates d}
      (hx : x ∈ Metric.ball z (1 / 4 : ℝ)) :
      x - z ∈ Homogenization.openCubeSet (Homogenization.originCube d 0) := by
    have hxm : x - z ∈ Metric.ball (0 : SpatialCoordinates d) (1 / 2 : ℝ) := by
      have hxnorm : ‖x - z‖ < (1 / 4 : ℝ) := by
        simpa [Metric.mem_ball, dist_eq_norm] using hx
      have hx' : ‖x - z‖ < (1 / 2 : ℝ) := by linarith
      simpa [Metric.mem_ball, dist_zero_right, sub_zero] using hx'
    rw [← Homogenization.ball_cubeCenter_eq_openCubeSet]
    have hcenter : Homogenization.cubeCenter
        (Homogenization.originCube d 0) = (0 : SpatialCoordinates d) := by
      ext i
      simp [Homogenization.cubeCenter, Homogenization.originCube]
    have hradius : Homogenization.cubeRadius
        (Homogenization.originCube d 0) = (1 / 2 : ℝ) := by
      unfold Homogenization.cubeRadius
      rw [Homogenization.cubeScaleFactor_eq_one_of_scale_eq_zero]
      · norm_num
      · rfl
    rw [hcenter, hradius]
    exact hxm
  let Wnn : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ≥0 := fun g =>
    ∑ z ∈ S, (⟨SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z g),
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable_nonneg _⟩ : ℝ≥0)
  let W : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ := fun g => Wnn g
  have hGint := aux_prop_16_coarse_block_dirichlet_g2_integral
    delta hdelta Praw G2
  have htrans (z : SpatialCoordinates d) :
      Integrable (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
        SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z g)) μ₀ := by
    have hmap : Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z) μ₀ = μ₀ :=
      G1.stationary z
    have hm : Integrable SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
        (Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z) μ₀) := by
      rw [hmap]
      exact hGint.1
    exact (integrable_map_measure
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable_measurable.aestronglyMeasurable
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_translate z).aemeasurable).mp hm
  have hWint : Integrable (fun g => W g) μ₀ := by
    have hs := integrable_finset_sum S (fun z hz => htrans z)
    have heq : (fun g => W g) =
        (fun g => ∑ z ∈ S,
          SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z g)) := by
      funext g
      dsimp [W, Wnn]
      exact NNReal.coe_sum S (fun z =>
        (⟨SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z g),
          SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable_nonneg _⟩ : ℝ≥0))
    rw [heq]
    exact hs
  have hderiv_bound (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d)
      {x : SpatialCoordinates d} (hx : x ∈ Metric.closedBall 0 R) :
      ‖SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g x‖ ≤ W g := by
    obtain ⟨z, hzS, hzx⟩ : ∃ z, ∃ (_ : z ∈ S),
        x ∈ Metric.ball z (1 / 4 : ℝ) := by
      simpa only [mem_iUnion] using hS hx
    have hlocal := SubdiffusiveProcess.Frozen.Assumptions.PotentialField.norm_deriv_le_g2Observable
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z g) (hball_cube hzx)
    have hderiv :
        fderiv ℝ ((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z g :
          SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :
          SpatialCoordinates d → ℝ) (x - z) =
          fderiv ℝ (fun y => g y) x := by
      change fderiv ℝ (fun y => g (y + z)) (x - z) = _
      rw [fderiv_comp_add_right, sub_add_cancel]
    have hlocal' :
        ‖SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g x‖ ≤
          SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z g) := by
      calc
        ‖SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g x‖ =
            ‖fderiv ℝ (fun y => g y) x‖ := by
              rw [(g.hasFDerivAt x).fderiv]
        _ = ‖fderiv ℝ ((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z g :
              SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :
              SpatialCoordinates d → ℝ) (x - z)‖ := by rw [hderiv]
        _ = ‖(SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z g).deriv (x - z)‖ := by
              rw [(SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z g).hasFDerivAt
                (x - z) |>.fderiv]
        _ ≤ _ := hlocal
    change ‖SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g x‖ ≤ (Wnn g : ℝ)
    exact hlocal'.trans (by
      exact_mod_cast Finset.single_le_sum
        (fun y _ => (show (0 : ℝ≥0) ≤
          ⟨SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate y g),
            SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable_nonneg _⟩ from zero_le)) hzS)
  refine ⟨Wnn, hWint, ?_⟩
  intro g
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · intro x hx
    exact (g.hasFDerivAt x).differentiableAt
  · intro x hx
    have hb : (‖fderiv ℝ (fun y => g y) x‖₊ : ℝ) ≤ (Wnn g : ℝ) := by
      have hb' := hderiv_bound g hx
      change ‖g.deriv x‖ ≤ (Wnn g : ℝ) at hb'
      simpa [(g.hasFDerivAt x).fderiv] using hb'
    exact_mod_cast hb
  · exact convex_closedBall 0 R
lemma aux_prop_16_coarse_block_dirichlet_positive_compact
    {d : ℕ} (delta : ℝ) (hdelta : 0 < delta)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Praw : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d))
    (G1 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 d Praw)
    (G2 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2 d delta Praw)
    (K : Compacts (SpatialCoordinates d)) (R : ℝ) (hR : 0 ≤ R)
    (hK : ∀ x ∈ (K : Set (SpatialCoordinates d)), ‖x‖ ≤ R) :
    let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
        C(SpatialCoordinates d, ℝ)) :=
      ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
    let nu := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
      forget
    let P := (commonScaleLaw d nu).toMeasure
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      let F : BilateralField d → C(K, ℝ) := fun omega =>
        (omega ((n : ℤ) + 1) -
          ContinuousMap.const _ (omega ((n : ℤ) + 1) 0)).restrict
            (K : Set (SpatialCoordinates d))
      Integrable F P ∧
        (∫ omega, ‖F omega‖ ∂P) ≤ C * (1 / 3 : ℝ) ^ (n + 1) := by
  letI : MeasurableSpace C(K, ℝ) := borel _
  letI : BorelSpace C(K, ℝ) := ⟨rfl⟩
  dsimp
  let μ₀ : Measure (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :=
    (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure
  let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
      C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  let nu := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
    forget
  obtain ⟨W, hWint, hWLip⟩ :=
    aux_prop_16_coarse_block_dirichlet_raw_lipschitz
      delta hdelta Praw G1 G2 R hR
  refine ⟨R * (∫ g, (W g : ℝ) ∂μ₀),
    mul_nonneg hR (integral_nonneg (fun g => (W g).coe_nonneg)), ?_⟩
  intro n
  let laws : ℤ → Measure C(SpatialCoordinates d, ℝ) :=
    fun j => (scaledLayerLaw d nu j : Measure C(SpatialCoordinates d, ℝ))
  let P : Measure (BilateralField d) := Measure.infinitePi laws
  let F : BilateralField d → C(K, ℝ) := fun omega =>
    (omega ((n : ℤ) + 1) -
      ContinuousMap.const _ (omega ((n : ℤ) + 1) 0)).restrict
        (K : Set (SpatialCoordinates d))
  let A : C(SpatialCoordinates d, ℝ) → C(K, ℝ) := fun f =>
    (f - ContinuousMap.const _ (f 0)).restrict (K : Set (SpatialCoordinates d))
  have hA : Continuous A := by
    exact (ContinuousMap.continuous_restrict (K : Set (SpatialCoordinates d))).comp
      (continuous_id.sub (ContinuousMap.continuous_const'.comp
        (continuous_eval_const (0 : SpatialCoordinates d))))
  let j : ℤ := (n : ℤ) + 1
  let c : ℝ := (3 : ℝ) ^ (-j)
  have hc : 0 < c := by
    dsimp [c, j]
    positivity
  have hc1 : c ≤ 1 := by
    dsimp [c, j]
    rw [show -((n : ℤ) + 1) = -((n + 1 : ℕ) : ℤ) by omega,
      zpow_neg, zpow_natCast]
    exact (inv_le_one₀ (by positivity)).2 (one_le_pow₀ (by norm_num))
  have hpoint (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :
      ‖A ((layerScaling d j) (forget g))‖ ≤ c * R * (W g : ℝ) := by
    have hbase := norm_anchored_contraction_on_compact_le K
      (forget g) hc.le hc1 hR hK (hWLip g)
    have heq : A ((layerScaling d j) (forget g)) =
        ((forget g).comp (⟨fun x : SpatialCoordinates d => c • x,
          by fun_prop⟩ :
            C(SpatialCoordinates d, SpatialCoordinates d))).restrict
          (K : Set (SpatialCoordinates d)) -
        ContinuousMap.const K ((forget g) 0) := by
      apply ContinuousMap.ext
      intro x
      change (forget g) ((3 : ℝ) ^ (-j) • (x : SpatialCoordinates d)) -
          (forget g) ((3 : ℝ) ^ (-j) • (0 : SpatialCoordinates d)) =
        (forget g) (c • (x : SpatialCoordinates d)) - (forget g) 0
      rw [smul_zero]
    rw [heq]
    exact hbase
  have hrawInt : Integrable (fun g => A ((layerScaling d j) (forget g))) μ₀ := by
    apply (hWint.const_mul (c * R)).mono'
    · exact (hA.comp ((layerScaling d j).continuous.comp forget.continuous)).measurable.aestronglyMeasurable
    · exact Filter.Eventually.of_forall hpoint
  have hraw_bound :
      ∫ g, ‖A ((layerScaling d j) (forget g))‖ ∂μ₀ ≤
        c * R * ∫ g, (W g : ℝ) ∂μ₀ := by
    calc
      _ ≤ ∫ g, c * R * (W g : ℝ) ∂μ₀ :=
        integral_mono_ae hrawInt.norm (hWint.const_mul (c * R))
          (Filter.Eventually.of_forall hpoint)
      _ = c * R * ∫ g, (W g : ℝ) ∂μ₀ := by
        rw [integral_const_mul]
  have hFint : Integrable F P := by
    have hAmap : Integrable A
        (Measure.map (layerScaling d j) (Measure.map forget μ₀)) := by
      apply (integrable_map_measure hA.measurable.aestronglyMeasurable
        (layerScaling d j).continuous.measurable.aemeasurable).2
      apply (integrable_map_measure
        (hA.comp (layerScaling d j).continuous).measurable.aestronglyMeasurable
        forget.continuous.measurable.aemeasurable).2
      exact hrawInt
    have heval := measurePreserving_eval_infinitePi laws j
    have hcomp : (fun omega => A (omega j)) = F := by
      funext omega
      rfl
    rw [← hcomp]
    exact heval.integrable_comp_of_integrable (by
      simpa only [laws, scaledLayerLaw, nu, forget, μ₀,
        ProbabilityMeasure.toMeasure_map] using hAmap)
  have hIntegralEval :
      (∫ omega, ‖F omega‖ ∂P) =
        ∫ f, ‖A f‖ ∂(scaledLayerLaw d nu j : Measure C(SpatialCoordinates d, ℝ)) := by
    have heval := measurePreserving_eval_infinitePi laws j
    change (∫ omega, ‖A (omega j)‖ ∂Measure.infinitePi laws) =
      ∫ f, ‖A f‖ ∂laws j
    rw [← heval.map_eq]
    exact (integral_map heval.measurable.aemeasurable
      hA.norm.measurable.aestronglyMeasurable).symm
  have hIntegralLayer :
      (∫ f, ‖A f‖ ∂(scaledLayerLaw d nu j : Measure C(SpatialCoordinates d, ℝ))) =
        ∫ g, ‖A ((layerScaling d j) g)‖ ∂(nu : Measure C(SpatialCoordinates d, ℝ)) := by
    simpa only [scaledLayerLaw, ProbabilityMeasure.toMeasure_map] using
      (integral_map (layerScaling d j).continuous.measurable.aemeasurable
        hA.norm.measurable.aestronglyMeasurable)
  have hIntegralForget :
      (∫ g, ‖A ((layerScaling d j) g)‖ ∂(nu : Measure C(SpatialCoordinates d, ℝ))) =
        ∫ g, ‖A ((layerScaling d j) (forget g))‖ ∂μ₀ := by
    exact integral_map forget.continuous.measurable.aemeasurable
      (hA.comp (layerScaling d j).continuous).norm.measurable.aestronglyMeasurable
  refine ⟨hFint, ?_⟩
  change (∫ omega, ‖F omega‖ ∂P) ≤
    (R * (∫ g, (W g : ℝ) ∂μ₀)) * (1 / 3 : ℝ) ^ (n + 1)
  rw [hIntegralEval, hIntegralLayer, hIntegralForget]
  have hWnonneg : 0 ≤ ∫ g, (W g : ℝ) ∂μ₀ :=
    integral_nonneg (fun g => (W g).coe_nonneg)
  have hgeom : c = (1 / 3 : ℝ) ^ (n + 1) := by
    dsimp [c, j]
    rw [show -((n : ℤ) + 1) = -((n + 1 : ℕ) : ℤ) by omega,
      zpow_neg, zpow_natCast]
    simp [one_div]
  calc
    (∫ g, ‖A ((layerScaling d j) (forget g))‖ ∂μ₀) ≤
        c * R * ∫ g, (W g : ℝ) ∂μ₀ := hraw_bound
    _ = R * (∫ g, (W g : ℝ) ∂μ₀) * c := by ring
    _ = R * (∫ g, (W g : ℝ) ∂μ₀) * (1 / 3 : ℝ) ^ (n + 1) := by rw [hgeom]



theorem prop_16_coarse_block_dirichlet :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (b : weakSobolevGraph (centeredCube z r hr))
    (fL2 : DomainL2 (centeredCube z r hr))
    (t p B : ℝ) (ht_lower : (d : ℝ) - 1 < t) (ht_upper : t < (d : ℝ))
    (hp : 2 ≤ p) (hB : 0 ≤ B) (dirichlet : Bool),
    let S := killedResponseSpace hP
    let L := (sobolevVolumeLoad fL2).comp S.space.subtypeL
    ∀ (Ctail : ℝ), 0 < Ctail →
    ∃ C : ℝ, 0 < C ∧
      ∀ (delta : ℝ), 0 < delta → delta ≤ 1 →
        ∀ (Praw : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d))
          (_G1 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 d Praw)
          (_G2 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2 d delta Praw),
          let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
              C(SpatialCoordinates d, ℝ)) :=
            ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
          let nu := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
            forget
          let P := (commonScaleLaw d nu).toMeasure
          ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
            Measurable H →
            (∀ᵐ omega ∂P,
              Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega))) →
            ∀ (kappa : ℕ → ℝ), (∀ N, 0 < kappa N) →
            ∀ (aN : ℕ → BilateralField d → PositiveCoefficient (centeredCube z r hr)),
              (∀ N omega,
                (aN N omega).val =ᵐ[volume.restrict
                  (centeredCube z r hr : Set (SpatialCoordinates d))]
                  (fun x => Real.exp (cutoffPotential H omega N x - Real.log (kappa N)))) →
          let RN : ℕ → BilateralField d → ℝ :=
            fun N omega =>
              if dirichlet then
                dirichletResponse S (aN N omega) b
              else
                inverseResponse S (aN N omega) L
          let coarseTail : ℕ → (BilateralField d × BilateralField d) → ℝ :=
            fun h pair =>
              sSup ((fun x : SpatialCoordinates d =>
                |∑' n : ℕ,
                  ((pair.2 ((n : ℤ) + (h : ℤ) + 1) x -
                      pair.2 ((n : ℤ) + (h : ℤ) + 1) 0) -
                    (pair.1 ((n : ℤ) + (h : ℤ) + 1) x -
                      pair.1 ((n : ℤ) + (h : ℤ) + 1) 0))|) ''
                (centeredCube z r hr : Set (SpatialCoordinates d)))
          (hTail :
            (∀ (h : ℕ) (q : ℝ), 2 ≤ q →
              MemLp (coarseTail h) (ENNReal.ofReal q) (P.prod P) ∧
              eLpNorm (coarseTail h) (ENNReal.ofReal q) (P.prod P) ≤
                ENNReal.ofReal (Ctail * delta * Real.sqrt q *
                  (3 : ℝ) ^ (-(h : ℝ)))) ∧
            (∀ (lambda : ℝ), 0 ≤ lambda →
              ∃ C_lambda : ℝ, 0 < C_lambda ∧
                ∀ h : ℕ,
                  Integrable (fun pair =>
                    Real.exp (lambda * coarseTail h pair)) (P.prod P) ∧
                  (∫ pair, Real.exp (lambda * coarseTail h pair) ∂(P.prod P)) ≤
                    C_lambda)) →
          ∀ (hR : ∀ N,
            MemLp (RN N) (ENNReal.ofReal (3 * p)) P ∧
            eLpNorm (RN N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B),
            ∀ (h N : ℕ),
              eLpNorm
                (fun pair : BilateralField d × BilateralField d =>
                  RN N pair.1 -
                    RN N (fun j =>
                      if (h : ℤ) < j then pair.2 j else pair.1 j))
                (ENNReal.ofReal (2 * p)) (P.prod P) ≤
              ENNReal.ofReal (C * delta * (3 : ℝ) ^ (-(h : ℝ)))
    := by
  intro d hd instM instB z r hr hP b fL2 t p B ht_lower ht_upper hp hB dirichlet
  dsimp
  intro Ctail hCtail
  refine ⟨1 + Ctail * (2 * B) * Real.sqrt (6 * p), ?_, ?_⟩
  · have hp0 : 0 < p := by linarith
    positivity
  intro delta hdelta hdelta1 Praw G1 G2
  intro H hH hHconv kappa hkappa aN haN
  intro hTail hR h N
  let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
      C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  let nu := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
    forget
  let P : Measure (BilateralField d) := (commonScaleLaw d nu).toMeasure
  let T : BilateralField d × BilateralField d → BilateralField d :=
    fun pair j => if (h : ℤ) < j then pair.2 j else pair.1 j
  have hTmeas : Measurable T := by
    unfold T
    apply measurable_pi_lambda
    intro j
    by_cases hj : (h : ℤ) < j
    · simp only [if_pos hj]
      exact (measurable_pi_apply j).comp measurable_snd
    · simp only [if_neg hj]
      exact (measurable_pi_apply j).comp measurable_fst
  have hTmap : Measure.map T (P.prod P) = P := by
    exact
      (measurePreserving_copy_infinitePi_block
        (fun j : ℤ => (scaledLayerLaw d nu j : Measure C(SpatialCoordinates d, ℝ)))
        {j : ℤ | (h : ℤ) < j}).map_eq
  have hTMP : MeasurePreserving T (P.prod P) P := ⟨hTmeas, hTmap⟩
  have hHconv_fst : ∀ᵐ pair : BilateralField d × BilateralField d ∂(P.prod P),
      Tendsto (infraredPartialSum pair.1) atTop (𝓝 (H pair.1)) :=
    (measurePreserving_fst :
      MeasurePreserving (Prod.fst : BilateralField d × BilateralField d → BilateralField d)
        (P.prod P) P).quasiMeasurePreserving.ae hHconv
  have hHconv_T : ∀ᵐ pair : BilateralField d × BilateralField d ∂(P.prod P),
      Tendsto (infraredPartialSum (T pair)) atTop (𝓝 (H (T pair))) :=
    hTMP.quasiMeasurePreserving.ae hHconv
  let K : Compacts (SpatialCoordinates d) :=
    ⟨Metric.closedBall z (r / 2), isCompact_closedBall z (r / 2)⟩
  have hQK : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ K := by
    intro x hx
    apply Metric.mem_closedBall.mpr
    exact (Metric.mem_ball.mp hx).le
  letI : Fact ((centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ K) :=
    ⟨hQK⟩
  have hKradius : ∀ x ∈ (K : Set (SpatialCoordinates d)),
      ‖x‖ ≤ ‖z‖ + r / 2 := by
    intro x hx
    have hdist : dist x z ≤ r / 2 := Metric.mem_closedBall.mp hx
    calc
      ‖x‖ = ‖(x - z) + z‖ := by ring_nf
      _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
      _ = dist x z + ‖z‖ := by rw [dist_eq_norm]
      _ ≤ ‖z‖ + r / 2 := by linarith
  obtain ⟨C₀, hC₀, hF₀⟩ :=
    aux_prop_16_coarse_block_dirichlet_positive_compact
      delta hdelta Praw G1 G2 K (‖z‖ + r / 2) (by positivity) hKradius
  let Fpos : ℕ → BilateralField d → C(K, ℝ) := fun n omega =>
    (omega ((n : ℤ) + 1) -
      ContinuousMap.const _ (omega ((n : ℤ) + 1) 0)).restrict (K : Set (SpatialCoordinates d))
  have hFpos : ∀ n, Integrable (Fpos n) P ∧
      (∫ omega, ‖Fpos n omega‖ ∂P) ≤ C₀ * (1 / 3 : ℝ) ^ (n + 1) := by
    intro n
    simpa only [Fpos, P, nu, forget] using hF₀ n
  have hsumF : Summable (fun n => ∫ omega, ‖Fpos n omega‖ ∂P) := by
    apply Summable.of_nonneg_of_le
      (fun n => integral_nonneg (fun omega => norm_nonneg _))
      (fun n => (hFpos n).2)
    have hgeo : Summable (fun n : ℕ => (1 / 3 : ℝ) ^ (n + 1)) := by
      have h := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 3)
        (by norm_num : (1 : ℝ) / 3 < 1))
      exact (summable_nat_add_iff 1).2 h
    exact hgeo.mul_left C₀
  have hsumF_ae : ∀ᵐ omega ∂P, Summable (fun n => Fpos n omega) := by
    have hnorm := ae_summable_norm_of_summable_integral_norm
      (fun n => (hFpos n).1) hsumF
    filter_upwards [hnorm] with omega hω
    exact hω.of_norm
  have hfst0 : MeasurePreserving
      (Prod.fst : BilateralField d × BilateralField d → BilateralField d)
      (P.prod P) P := measurePreserving_fst
  have hseries_tail :
      ∀ᵐ pair : BilateralField d × BilateralField d ∂(P.prod P),
        Summable (fun n : ℕ => Fpos n pair.1) ∧
        Summable (fun n : ℕ => Fpos n (T pair)) := by
    filter_upwards [hfst0.quasiMeasurePreserving.ae hsumF_ae,
      hTMP.quasiMeasurePreserving.ae hsumF_ae] with pair h₁ h₂
    exact ⟨h₁, h₂⟩
  have hordered_tail_bridge :
      ∀ᵐ pair : BilateralField d × BilateralField d ∂(P.prod P),
        (H (T pair)).restrict (K : Set (SpatialCoordinates d)) -
            (H pair.1).restrict (K : Set (SpatialCoordinates d)) =
          ∑' n : ℕ,
            (Fpos (n + h) (T pair) - Fpos (n + h) pair.1) := by
    filter_upwards [hHconv_fst, hHconv_T, hseries_tail] with pair h₁ h₂ hs
    let u : ℕ → C(K, ℝ) := fun n => Fpos n pair.1
    let v : ℕ → C(K, ℝ) := fun n => Fpos n (T pair)
    have hEq : ∀ n < h, u n = v n := by
      intro n hn
      have hnZ : (n : ℤ) < (h : ℤ) := by exact_mod_cast hn
      have hneg : ¬ (h : ℤ) < (n : ℤ) + 1 := by omega
      ext x
      simp only [u, v, Fpos, T, if_neg hneg]
    have hU : Tendsto (fun L : ℕ => ∑ n ∈ Finset.range L, u n)
        atTop (𝓝 ((H pair.1).restrict (K : Set (SpatialCoordinates d)))) := by
      have hres := (ContinuousMap.continuous_restrict
        (K : Set (SpatialCoordinates d))).continuousAt.tendsto.comp h₁
      have heq : (fun L => ∑ n ∈ Finset.range L, u n) =
          (fun L => (ContinuousMap.restrict (K : Set (SpatialCoordinates d)))
            (infraredPartialSum pair.1 L)) := by
        funext L
        ext x
        simp [u, Fpos, infraredPartialSum, ContinuousMap.restrict,
          ContinuousMap.coe_mk, Function.comp_apply, Finset.sum_sub_distrib]
      rw [heq]
      exact hres
    have hV : Tendsto (fun L : ℕ => ∑ n ∈ Finset.range L, v n)
        atTop (𝓝 ((H (T pair)).restrict (K : Set (SpatialCoordinates d)))) := by
      have hres := (ContinuousMap.continuous_restrict
        (K : Set (SpatialCoordinates d))).continuousAt.tendsto.comp h₂
      have heq : (fun L => ∑ n ∈ Finset.range L, v n) =
          (fun L => (ContinuousMap.restrict (K : Set (SpatialCoordinates d)))
            (infraredPartialSum (T pair) L)) := by
        funext L
        ext x
        simp [v, Fpos, infraredPartialSum, ContinuousMap.restrict,
          ContinuousMap.coe_mk, Function.comp_apply, Finset.sum_sub_distrib]
      rw [heq]
      exact hres
    have hu : Summable u := hs.1
    have hv : Summable v := hs.2
    have hU' : (H pair.1).restrict (K : Set (SpatialCoordinates d)) = ∑' n : ℕ, u n :=
      tendsto_nhds_unique hU hu.hasSum.tendsto_sum_nat
    have hV' : (H (T pair)).restrict (K : Set (SpatialCoordinates d)) = ∑' n : ℕ, v n :=
      tendsto_nhds_unique hV hv.hasSum.tendsto_sum_nat
    have huh : Summable (fun n : ℕ => u (n + h)) :=
      (summable_nat_add_iff h).2 hu
    have hvh : Summable (fun n : ℕ => v (n + h)) :=
      (summable_nat_add_iff h).2 hv
    have htail : ∀ n, v (n + h) =
        Fpos (n + h) (T pair) := by
      intro n
      rfl
    have htail_sum :
        (∑' n : ℕ, (v (n + h) - u (n + h))) =
          ∑' n : ℕ, (Fpos (n + h) (T pair) - Fpos (n + h) pair.1) := by
      apply tsum_congr
      intro n
      rw [htail]
    rw [hU', hV', ← hv.sum_add_tsum_nat_add h, ← hu.sum_add_tsum_nat_add h]
    rw [← htail_sum]
    rw [hvh.tsum_sub huh]
    simp only [Nat.add_comm]
    have hfinite : (∑ i ∈ Finset.range h, v i) =
        ∑ i ∈ Finset.range h, u i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (hEq i (Finset.mem_range.mp hi)).symm
    rw [hfinite]
    abel
  have hresponse :
      eLpNorm
          (fun pair : BilateralField d × BilateralField d =>
            (if dirichlet then
                dirichletResponse (killedResponseSpace hP) (aN N pair.1) b
              else
                inverseResponse (killedResponseSpace hP) (aN N pair.1)
                  ((sobolevVolumeLoad fL2).comp
                    (killedResponseSpace hP).space.subtypeL)) -
              (if dirichlet then
                  dirichletResponse (killedResponseSpace hP) (aN N
                    (fun j => if (h : ℤ) < j then pair.2 j else pair.1 j)) b
                else
                  inverseResponse (killedResponseSpace hP) (aN N
                    (fun j => if (h : ℤ) < j then pair.2 j else pair.1 j))
                    ((sobolevVolumeLoad fL2).comp
                      (killedResponseSpace hP).space.subtypeL)))
          (ENNReal.ofReal (2 * p)) (P.prod P) ≤
        ENNReal.ofReal ((1 + Ctail * (2 * B) * Real.sqrt (6 * p)) * delta *
          (3 : ℝ) ^ (-(h : ℝ))) := by
    let S : ResponseSpace (centeredCube z r hr) := killedResponseSpace hP
    let L : S.space →L[ℝ] ℝ :=
      (sobolevVolumeLoad fL2).comp S.space.subtypeL
    let RN' : BilateralField d → ℝ := fun omega =>
      if dirichlet then
        dirichletResponse S (aN N omega) b
      else
        inverseResponse S (aN N omega) L
    have hRN : MemLp RN' (ENNReal.ofReal (3 * p)) P := by
      simpa only [RN', S, L, P] using (hR N).1
    have hfst : MeasurePreserving
        (Prod.fst : BilateralField d × BilateralField d → BilateralField d)
        (P.prod P) P := measurePreserving_fst
    have hX : MemLp (fun pair : BilateralField d × BilateralField d => RN' pair.1)
        (ENNReal.ofReal (3 * p)) (P.prod P) :=
      hRN.comp_measurePreserving hfst
    have hY : MemLp (fun pair : BilateralField d × BilateralField d => RN' (T pair))
        (ENNReal.ofReal (3 * p)) (P.prod P) :=
      hRN.comp_measurePreserving hTMP
    have hXbound : eLpNorm (fun pair : BilateralField d × BilateralField d => RN' pair.1)
        (ENNReal.ofReal (3 * p)) (P.prod P) ≤ ENNReal.ofReal B := by
      calc
        eLpNorm (fun pair : BilateralField d × BilateralField d => RN' pair.1)
            (ENNReal.ofReal (3 * p)) (P.prod P) =
        eLpNorm RN' (ENNReal.ofReal (3 * p)) P :=
          (eLpNorm_comp_measurePreserving (f := Prod.fst) (g := RN')
            hRN.aestronglyMeasurable hfst)
        _ ≤ ENNReal.ofReal B := by simpa only [RN', S, L, P] using (hR N).2
    have hYbound : eLpNorm (fun pair : BilateralField d × BilateralField d => RN' (T pair))
        (ENNReal.ofReal (3 * p)) (P.prod P) ≤ ENNReal.ofReal B := by
      calc
        eLpNorm (fun pair : BilateralField d × BilateralField d => RN' (T pair))
            (ENNReal.ofReal (3 * p)) (P.prod P) =
            eLpNorm RN' (ENNReal.ofReal (3 * p)) P :=
          (eLpNorm_comp_measurePreserving (f := T) (g := RN')
            hRN.aestronglyMeasurable hTMP)
        _ ≤ ENNReal.ofReal B := by simpa only [RN', S, L, P] using (hR N).2
    let U : BilateralField d → C(K, ℝ) := fun omega =>
      (ContinuousMap.restrict (K : Set (SpatialCoordinates d)) (H omega)) +
        ((Finset.range (N + 1)).sum (fun j =>
          ContinuousMap.restrict (K : Set (SpatialCoordinates d))
            (omega (-(Int.ofNat j))))) -
        ContinuousMap.const K (Real.log (kappa N))
    let uLp : BilateralField d →
        Lp ℝ ∞ (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      fun omega => compactPotentialToLp K (U omega)
    have hcoef : ∀ omega, aN N omega =
        expPotentialCoefficient (uLp omega) := by
      intro omega
      apply Subtype.ext
      apply Lp.ext
      filter_upwards [haN N omega,
        expPotentialCoefficient_coeFn (uLp omega),
        compactPotentialToLp_on_domain K (U omega),
        ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with
        x hx ha hu hxQ
      rw [hx, ha, hu hxQ]
      simp only [uLp, U, ContinuousMap.coe_sub, ContinuousMap.coe_add,
        ContinuousMap.coe_sum, ContinuousMap.coe_restrict, ContinuousMap.const_apply]
      simp [cutoffPotential, ContinuousMap.restrict_apply, ContinuousMap.sum_apply]
      rfl
    let CT : BilateralField d × BilateralField d → ℝ := fun pair =>
      sSup ((fun x : SpatialCoordinates d =>
        |∑' n : ℕ,
          ((pair.2 ((n : ℤ) + (h : ℤ) + 1) x -
              pair.2 ((n : ℤ) + (h : ℤ) + 1) 0) -
            (pair.1 ((n : ℤ) + (h : ℤ) + 1) x -
              pair.1 ((n : ℤ) + (h : ℤ) + 1) 0))|) ''
        (centeredCube z r hr : Set (SpatialCoordinates d)))
    have hCT_nonneg : ∀ pair, 0 ≤ CT pair := by
      intro pair
      apply Real.sSup_nonneg
      rintro y ⟨x, hx, rfl⟩
      exact abs_nonneg _
    have hnorm : ∀ᵐ pair : BilateralField d × BilateralField d ∂(P.prod P),
        ‖uLp pair.1 - uLp (T pair)‖ ≤ CT pair := by
      filter_upwards [hordered_tail_bridge, hseries_tail] with pair hbridge hs
      let Dk : C(K, ℝ) := U pair.1 - U (T pair)
      let D0 : C(SpatialCoordinates d, ℝ) := H pair.1 - H (T pair)
      let wK : ℕ → C(K, ℝ) := fun n =>
        Fpos (n + h) (T pair) - Fpos (n + h) pair.1
      have hwK : Summable wK := by
        dsimp [wK]
        exact ((summable_nat_add_iff h).2 hs.2).sub
          ((summable_nat_add_iff h).2 hs.1)
      let w : ℕ → C(SpatialCoordinates d, ℝ) := fun n =>
        pair.2 ((n : ℤ) + (h : ℤ) + 1) -
            ContinuousMap.const _ (pair.2 ((n : ℤ) + (h : ℤ) + 1) 0) -
          (pair.1 ((n : ℤ) + (h : ℤ) + 1) -
            ContinuousMap.const _ (pair.1 ((n : ℤ) + (h : ℤ) + 1) 0))
      have hbridge_point (x : SpatialCoordinates d) (hxK : x ∈ K) :
          (H (T pair) - H pair.1) x = ∑' n : ℕ, w n x := by
        have he := congrArg (fun g : C(K, ℝ) => g ⟨x, hxK⟩) hbridge
        change (H (T pair) - H pair.1) x =
          (∑' n : ℕ, wK n) ⟨x, hxK⟩ at he
        have hsx : (∑' n : ℕ, wK n) ⟨x, hxK⟩ = ∑' n : ℕ, w n x := by
          rw [← ContinuousMap.tsum_apply hwK]
          apply tsum_congr
          intro n
          simp only [wK, w, Fpos, ContinuousMap.coe_sub,
            ContinuousMap.sub_apply, ContinuousMap.coe_restrict,
            ContinuousMap.restrict_apply, ContinuousMap.const_apply]
          rw [show ((n + h : ℕ) : ℤ) + 1 =
              (n : ℤ) + (h : ℤ) + 1 by omega]
          simp only [T]
          rw [if_pos (by omega)]
          change
            (pair.2 ((n : ℤ) + (h : ℤ) + 1) x -
                (pair.2 ((n : ℤ) + (h : ℤ) + 1)) 0) -
              ((pair.1 ((n : ℤ) + (h : ℤ) + 1) x -
                (pair.1 ((n : ℤ) + (h : ℤ) + 1)) 0)) =
            (pair.2 ((n : ℤ) + (h : ℤ) + 1) x -
                (pair.2 ((n : ℤ) + (h : ℤ) + 1)) 0) -
              ((pair.1 ((n : ℤ) + (h : ℤ) + 1) x -
                (pair.1 ((n : ℤ) + (h : ℤ) + 1)) 0))
          rfl
        simpa only [ContinuousMap.coe_sub] using he.trans hsx
      have hDkval : ∀ x : K, Dk x = D0 x := by
        intro x
        have hsum :
            (Finset.range (N + 1)).sum (fun j =>
              ContinuousMap.restrict (K : Set (SpatialCoordinates d))
                (T pair (-(Int.ofNat j)))) =
            (Finset.range (N + 1)).sum (fun j =>
              ContinuousMap.restrict (K : Set (SpatialCoordinates d))
                (pair.1 (-(Int.ofNat j)))) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hj' : ¬ (h : ℤ) < -(Int.ofNat j) :=
            not_lt_of_ge ((neg_nonpos.mpr (Int.ofNat_zero_le j)).trans
              (Int.ofNat_zero_le h))
          simp only [T, if_neg hj']
        simp only [Dk, D0, U, ContinuousMap.coe_sub, ContinuousMap.coe_add,
          ContinuousMap.coe_sum, ContinuousMap.const_apply,
          ContinuousMap.add_apply, ContinuousMap.sub_apply]
        have hsumx := congrArg (fun g : C(K, ℝ) => g x) hsum
        simp only [ContinuousMap.coe_sum, ContinuousMap.coe_restrict] at hsumx
        rw [hsumx]
        abel
      have htail_bdd : BddAbove
          ((fun x : SpatialCoordinates d => |∑' n : ℕ, w n x|) ''
            (centeredCube z r hr : Set (SpatialCoordinates d))) := by
        refine ⟨‖Dk‖, ?_⟩
        rintro y ⟨x, hx, rfl⟩
        have hxK : x ∈ K := hQK hx
        have he := hbridge_point x (hQK hx)
        have hdk := ContinuousMap.norm_coe_le_norm Dk ⟨x, hxK⟩
        have hdk0 : Dk ⟨x, hxK⟩ = D0 x := hDkval ⟨x, hxK⟩
        calc
          |∑' n : ℕ, w n x| = ‖(H (T pair) - H pair.1) x‖ := by
            rw [hbridge_point x (hQK hx)]
            simp only [Real.norm_eq_abs]
          _ = ‖Dk ⟨x, hxK⟩‖ := by
            rw [hdk0]
            simp only [D0, ContinuousMap.coe_sub]
            exact norm_sub_rev _ _
          _ ≤ ‖Dk‖ := hdk
      have htail_le (x : SpatialCoordinates d) (hx : x ∈ centeredCube z r hr) :
          |∑' n : ℕ, w n x| ≤ CT pair := by
        exact le_csSup (show BddAbove _ from htail_bdd) ⟨x, hx, rfl⟩
      have hAclosed : IsClosed
          {x : SpatialCoordinates d | ‖D0 x‖ ≤ CT pair} := by
        exact isClosed_le (continuous_norm.comp D0.continuous) continuous_const
      have hAQ : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
          {x : SpatialCoordinates d | ‖D0 x‖ ≤ CT pair} := by
        intro x hx
        have he := hbridge_point x (hQK hx)
        have ht := htail_le x hx
        rw [← he] at ht
        simpa [D0, ContinuousMap.coe_sub, Real.norm_eq_abs, abs_sub_comm] using ht
      have hAclosure : closure (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
          {x : SpatialCoordinates d | ‖D0 x‖ ≤ CT pair} :=
        (hAclosed.closure_subset_iff).2 hAQ
      have hDknorm : ‖Dk‖ ≤ CT pair := by
        apply (ContinuousMap.norm_le Dk (hCT_nonneg pair)).2
        intro x
        have hxcl : (x : SpatialCoordinates d) ∈
            closure (centeredCube z r hr : Set (SpatialCoordinates d)) := by
          rw [show closure (centeredCube z r hr : Set (SpatialCoordinates d)) =
              Metric.closedBall z (r / 2) by
                simp [centeredCube, closure_ball, ne_of_gt (half_pos hr)]]
          exact x.property
        have ha := hAclosure hxcl
        calc
          ‖Dk x‖ = ‖D0 (x : SpatialCoordinates d)‖ :=
            congrArg norm (hDkval x)
          _ ≤ CT pair := ha
      exact (compactPotentialToLp_sub_norm_le K (U pair.1) (U (T pair))).trans
        hDknorm
    change eLpNorm
      (fun pair : BilateralField d × BilateralField d => RN' pair.1 - RN' (T pair))
        (ENNReal.ofReal (2 * p)) (P.prod P) ≤
      ENNReal.ofReal ((1 + Ctail * (2 * B) * Real.sqrt (6 * p)) * delta *
        (3 : ℝ) ^ (-(h : ℝ)))
    have hpoint : ∀ᵐ pair : BilateralField d × BilateralField d ∂(P.prod P),
        |RN' pair.1 - RN' (T pair)| ≤
          CT pair * (|RN' pair.1| + |RN' (T pair)|) := by
      cases dirichlet with
      | false =>
          filter_upwards [hnorm] with pair hpair
          have hdifference :=
            aux_prop_16_coarse_block_dirichlet_exp_response_difference
              (centeredCube z r hr) S L b false
              (uLp pair.1) (uLp (T pair))
          rw [← hcoef pair.1, ← hcoef (T pair)] at hdifference
          have hdiff : |RN' pair.1 - RN' (T pair)| ≤
              ‖uLp pair.1 - uLp (T pair)‖ *
                (RN' pair.1 + RN' (T pair)) := by
            simpa only [RN', if_false] using hdifference
          have hnonneg : 0 ≤ RN' pair.1 + RN' (T pair) := by
            dsimp [RN']
            exact add_nonneg
              (inverseResponse_nonneg S _ L)
              (inverseResponse_nonneg S _ L)
          calc
            |RN' pair.1 - RN' (T pair)| ≤
                ‖uLp pair.1 - uLp (T pair)‖ *
                  (RN' pair.1 + RN' (T pair)) := hdiff
            _ ≤ CT pair * (RN' pair.1 + RN' (T pair)) :=
              mul_le_mul_of_nonneg_right hpair hnonneg
            _ = CT pair * (|RN' pair.1| + |RN' (T pair)|) := by
              rw [abs_of_nonneg (by
                dsimp [RN']; exact inverseResponse_nonneg S _ L),
                abs_of_nonneg (by
                  dsimp [RN']; exact inverseResponse_nonneg S _ L)]
      | true =>
          filter_upwards [hnorm] with pair hpair
          have hdifference :=
            aux_prop_16_coarse_block_dirichlet_exp_response_difference
              (centeredCube z r hr) S L b true
              (uLp pair.1) (uLp (T pair))
          rw [← hcoef pair.1, ← hcoef (T pair)] at hdifference
          have hdiff : |RN' pair.1 - RN' (T pair)| ≤
              ‖uLp pair.1 - uLp (T pair)‖ *
                (RN' pair.1 + RN' (T pair)) := by
            simpa only [RN', if_true] using hdifference
          have hnonneg : 0 ≤ RN' pair.1 + RN' (T pair) := by
            dsimp [RN']
            exact add_nonneg
              (dirichletResponse_nonneg S _ b)
              (dirichletResponse_nonneg S _ b)
          calc
            |RN' pair.1 - RN' (T pair)| ≤
                ‖uLp pair.1 - uLp (T pair)‖ *
                  (RN' pair.1 + RN' (T pair)) := hdiff
            _ ≤ CT pair * (RN' pair.1 + RN' (T pair)) :=
              mul_le_mul_of_nonneg_right hpair hnonneg
            _ = CT pair * (|RN' pair.1| + |RN' (T pair)|) := by
              rw [abs_of_nonneg (by
                dsimp [RN']; exact dirichletResponse_nonneg S _ b),
                abs_of_nonneg (by
                  dsimp [RN']; exact dirichletResponse_nonneg S _ b)]
    have hq : 2 ≤ 6 * p := by linarith
    have hCT := hTail.1 h (6 * p) hq
    have hK : 0 ≤ Ctail * delta * Real.sqrt (6 * p) *
        (3 : ℝ) ^ (-(h : ℝ)) := by positivity
    have hmoment :=
      aux_prop_16_coarse_block_dirichlet_moment
        (P.prod P) p (Ctail * delta * Real.sqrt (6 * p) *
          (3 : ℝ) ^ (-(h : ℝ))) B hp hK hB CT
        (fun pair : BilateralField d × BilateralField d => RN' pair.1)
        (fun pair => RN' (T pair))
        hCT.1 hX hY hCT.2 hXbound hYbound hpoint
    have hreal :
        (Ctail * delta * Real.sqrt (6 * p) * (3 : ℝ) ^ (-(h : ℝ))) *
            (2 * B) ≤
          (1 + Ctail * (2 * B) * Real.sqrt (6 * p)) * delta *
            (3 : ℝ) ^ (-(h : ℝ)) := by
      have htailnonneg : 0 ≤ delta * (3 : ℝ) ^ (-(h : ℝ)) := by
        positivity
      have hcoefnonneg : 0 ≤ Ctail * (2 * B) * Real.sqrt (6 * p) := by
        positivity
      calc
        (Ctail * delta * Real.sqrt (6 * p) * (3 : ℝ) ^ (-(h : ℝ))) *
              (2 * B) =
            (Ctail * (2 * B) * Real.sqrt (6 * p)) *
              (delta * (3 : ℝ) ^ (-(h : ℝ))) := by ring
        _ ≤ (1 + Ctail * (2 * B) * Real.sqrt (6 * p)) *
              (delta * (3 : ℝ) ^ (-(h : ℝ))) := by
          gcongr
          linarith
        _ = (1 + Ctail * (2 * B) * Real.sqrt (6 * p)) * delta *
              (3 : ℝ) ^ (-(h : ℝ)) := by ring
    exact hmoment.trans (ENNReal.ofReal_le_ofReal hreal)
  simpa [P, nu, forget] using hresponse

end Paper

