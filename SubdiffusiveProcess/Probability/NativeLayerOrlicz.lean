module

public import SubdiffusiveProcess.Sobolev.GMCAnchoredOrlicz
public import SubdiffusiveProcess.Main.PositiveScaledNativeLayer_apply
public import SubdiffusiveProcess.Main.PositiveScaledNativeLayer_deriv
public import SubdiffusiveProcess.Main.CompactPotentialC1Norm
public import SubdiffusiveProcess.Main.CompactGradientLipschitzObservable

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess

private theorem finite_sum_translated_g2_exp_square
    {d : ℕ} (S : Finset (Homogenization.Vec d)) (hSne : S.Nonempty)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    (∫⁻ g, ENNReal.ofReal (Real.exp
      (((∑ z ∈ S, _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
          (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g)) /
        (∑ _z ∈ S, M.delta)) ^ 2)) ∂
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ≤ 2 := by
  let μ₀ : Measure (_root_.SubdiffusiveProcess.Model.PotentialField d) :=
    (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  let Xz : Homogenization.Vec d →
      _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ := fun z g =>
    _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
      (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g)
  let f₀ : _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ≥0∞ := fun g =>
    ENNReal.ofReal (Real.exp
      ((_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g / M.delta) ^ 2))
  have hδ : 0 < M.delta := M.shellPrefix.delta_pos
  have hG2 :
      Integrable (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d =>
        Real.exp
          ((_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g / M.delta) ^ 2)) μ₀ ∧
        (∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d,
          Real.exp
            ((_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g / M.delta) ^ 2)
          ∂μ₀) ≤ 2 := by
    apply (SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.ogammaLE_two_iff_of_nonneg
      hδ (fun g => _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg g)).mp
    simpa [μ₀] using! M.G2.regularity_expectation
  have hbaseAE : AEMeasurable f₀ μ₀ := by
    change AEMeasurable (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d =>
      ENNReal.ofReal (Real.exp
        ((_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g / M.delta) ^ 2))) μ₀
    have hgm : AEMeasurable
        (_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
          : _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ) μ₀ :=
      (_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_measurable).aemeasurable
    exact (((hgm.div_const M.delta).pow_const 2).exp).ennreal_ofReal
  have hbaseLin : (∫⁻ g, f₀ g ∂μ₀) ≤ 2 := by
    change (∫⁻ g, ENNReal.ofReal (Real.exp
      ((_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g / M.delta) ^ 2)) ∂μ₀) ≤ 2
    have hpos : ∀ᵐ g ∂μ₀, 0 ≤ Real.exp
        ((_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g / M.delta) ^ 2) :=
      Filter.Eventually.of_forall fun g => (Real.exp_pos _).le
    have heq := ofReal_integral_eq_lintegral_ofReal hG2.1 hpos
    calc
      (∫⁻ g, ENNReal.ofReal (Real.exp
          ((_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g / M.delta) ^ 2)) ∂μ₀) =
          ENNReal.ofReal (∫ g, Real.exp
            ((_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g / M.delta) ^ 2) ∂μ₀) :=
        heq.symm
      _ ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hG2.2
      _ = 2 := by norm_num
  have hXmeas : ∀ z ∈ S, AEStronglyMeasurable (Xz z) μ₀ := by
    intro z hz
    exact (_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_measurable.comp
      (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate z)).aestronglyMeasurable
  have hX0 : ∀ z ∈ S, ∀ᵐ g ∂μ₀, 0 ≤ Xz z g := by
    intro z hz
    exact Filter.Eventually.of_forall fun g =>
      _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg _
  have hXExp : ∀ z ∈ S, (∫⁻ g, ENNReal.ofReal
      (Real.exp ((Xz z g / M.delta) ^ 2)) ∂μ₀) ≤ 2 := by
    intro z hz
    have hbaseMap : AEMeasurable f₀
        (Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.translate z) μ₀) := by
      rw [show Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.translate z) μ₀ = μ₀ by
        simpa [μ₀] using! M.G1.stationary z]
      exact hbaseAE
    have hmap := lintegral_map' hbaseMap
      (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate z).aemeasurable
    calc
      (∫⁻ g, ENNReal.ofReal (Real.exp ((Xz z g / M.delta) ^ 2)) ∂μ₀) =
          ∫⁻ g, f₀ (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g) ∂μ₀ := by
            rfl
      _ = ∫⁻ g, f₀ g ∂Measure.map
          (_root_.SubdiffusiveProcess.Model.PotentialField.translate z) μ₀ := hmap.symm
      _ = ∫⁻ g, f₀ g ∂μ₀ := by
        rw [show Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.translate z) μ₀ = μ₀ by
          simpa [μ₀] using! M.G1.stationary z]
      _ ≤ 2 := hbaseLin
  have hsum := lintegral_exp_sq_finset_sum_le μ₀ S Xz
    (fun _ => M.delta) hSne hXmeas hX0
    (fun z hz => hδ) hXExp
  simpa only [Xz] using! hsum

private theorem max_scaled_bound
    {a b c w R : ℝ} (hc : 0 < c) (hw : 0 ≤ w)
    (ha : a ≤ c * (R + 1) * w) (hb : b ≤ 8 * c^2 * w) :
    max (a / c) (b / c^2) ≤ max (R + 1) 8 * w := by
  have hc2 : 0 < c^2 := sq_pos_of_pos hc
  apply max_le
  · apply (div_le_iff₀ hc).2
    calc
      a ≤ c * (R + 1) * w := ha
      _ ≤ max (R + 1) 8 * w * c := by
        calc
          c * (R + 1) * w = (c * w) * (R + 1) := by ring
          _ ≤ (c * w) * max (R + 1) 8 :=
            mul_le_mul_of_nonneg_left (le_max_left _ _) (mul_nonneg hc.le hw)
          _ = max (R + 1) 8 * w * c := by ring
  · apply (div_le_iff₀ hc2).2
    calc
      b ≤ 8 * c^2 * w := hb
      _ ≤ max (R + 1) 8 * w * c^2 := by
        calc
          8 * c^2 * w = (c^2 * w) * 8 := by ring
          _ ≤ (c^2 * w) * max (R + 1) 8 :=
            mul_le_mul_of_nonneg_left (le_max_right _ _) (mul_nonneg (sq_nonneg c) hw)
          _ = max (R + 1) 8 * w * c^2 := by ring

private theorem scale_den_identity
    {w q B δ : ℝ} (hq : 0 < q) (hδ : 0 < δ) :
    B * w = (w / (q * δ)) * (q * B * δ) := by
  field_simp [ne_of_gt hq, ne_of_gt hδ]

private theorem compact_c1_nonneg
    {d : ℕ} (K : Compacts (SpatialCoordinates d))
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) :
    0 ≤ compactPotentialC1Norm K g := by
  unfold compactPotentialC1Norm
  exact add_nonneg
    (norm_nonneg (⟨fun x : K => g x.1,
      g.1.1.continuous.comp continuous_subtype_val⟩ : C(K, ℝ)))
    (norm_nonneg (⟨fun x : K =>
      _root_.SubdiffusiveProcess.Model.PotentialField.deriv g x.1,
      (_root_.SubdiffusiveProcess.Model.PotentialField.deriv g).continuous.comp
        continuous_subtype_val⟩ : C(K, SpatialCoordinates d →L[ℝ] ℝ)))

private theorem lintegral_le_of_measurePreserving_comp
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {g : α → β}
    {F : β → ℝ≥0∞} {L : α → ℝ≥0∞}
    (hg : MeasurePreserving g μ ν) (hF : Measurable F)
    (hL : ∀ a, L a ≤ F (g a)) (hroot : (∫⁻ b, F b ∂ν) ≤ 2) :
    (∫⁻ a, L a ∂μ) ≤ 2 := by
  calc
    (∫⁻ a, L a ∂μ) ≤ ∫⁻ a, F (g a) ∂μ := lintegral_mono hL
    _ = ∫⁻ b, F b ∂ν := hg.lintegral_comp hF
    _ ≤ 2 := hroot

private theorem cover_regularities
    {d : ℕ} (R : ℝ) (S : Finset (Homogenization.Vec d))
    (hS : Metric.closedBall (0 : Homogenization.Vec d) R ⊆
      ⋃ z ∈ S, Metric.ball z (1 / 4 : ℝ))
    (hball_cube : ∀ {z x : Homogenization.Vec d},
      x ∈ Metric.ball z (1 / 4 : ℝ) →
        x - z ∈ Homogenization.openCubeSet (Homogenization.originCube d 0))
    (hball_cube_half : ∀ {z x : Homogenization.Vec d},
      x ∈ Metric.ball z (1 / 2 : ℝ) →
        x - z ∈ Homogenization.openCubeSet (Homogenization.originCube d 0)) :
    ∃ Wnn : _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ≥0,
      ∃ W : _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ,
        (∀ g, W g = Wnn g) ∧
        (∀ g, Wnn g = ∑ z ∈ S,
          (⟨_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
            (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g),
            _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg _⟩ : ℝ≥0)) ∧
        (∀ g {x}, x ∈ Metric.closedBall (0 : Homogenization.Vec d) R →
          ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv g x‖ ≤ W g) ∧
        (∀ g, LipschitzOnWith (Wnn g) (fun x => g x)
          (Metric.closedBall (0 : Homogenization.Vec d) R)) ∧
        (∀ g {x y}, x ∈ Metric.closedBall (0 : Homogenization.Vec d) R →
          y ∈ Metric.closedBall (0 : Homogenization.Vec d) R →
          ‖x - y‖ < (1 / 4 : ℝ) →
          ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv g x -
            _root_.SubdiffusiveProcess.Model.PotentialField.deriv g y‖ ≤
            W g * ‖x - y‖) := by
  classical
  let Wnn : _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ≥0 := fun g =>
    ∑ z ∈ S, (⟨_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
      (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g),
      _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg _⟩ : ℝ≥0)
  let W : _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ := fun g => Wnn g
  have hderiv_bound (g : _root_.SubdiffusiveProcess.Model.PotentialField d)
      {x : Homogenization.Vec d}
      (hx : x ∈ Metric.closedBall (0 : Homogenization.Vec d) R) :
      ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv g x‖ ≤ W g := by
    obtain ⟨z, hzS, hzx⟩ : ∃ z, ∃ (_ : z ∈ S),
        x ∈ Metric.ball z (1 / 4 : ℝ) := by
      simpa only [mem_iUnion] using! hS hx
    have hlocal := _root_.SubdiffusiveProcess.Model.PotentialField.norm_deriv_le_g2Observable
      (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g) (hball_cube hzx)
    have hderiv :
        fderiv ℝ ((_root_.SubdiffusiveProcess.Model.PotentialField.translate z g :
          _root_.SubdiffusiveProcess.Model.PotentialField d) :
          Homogenization.Vec d → ℝ) (x - z) =
          fderiv ℝ (fun y => g y) x := by
      change fderiv ℝ (fun q => g (q + z)) (x - z) = _
      simpa only [sub_add_cancel] using!
        (fderiv_comp_add_right (𝕜 := ℝ) (f := (fun y => g y)) z (x := x - z))
    calc
      ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv g x‖ =
          ‖fderiv ℝ (fun y => g y) x‖ := by rw [(g.hasFDerivAt x).fderiv]
      _ = ‖fderiv ℝ ((_root_.SubdiffusiveProcess.Model.PotentialField.translate z g :
          _root_.SubdiffusiveProcess.Model.PotentialField d) :
          Homogenization.Vec d → ℝ) (x - z)‖ := by rw [hderiv]
      _ = ‖(_root_.SubdiffusiveProcess.Model.PotentialField.translate z g).deriv (x - z)‖ := by
        rw [(_root_.SubdiffusiveProcess.Model.PotentialField.translate z g).hasFDerivAt
          (x - z) |>.fderiv]
      _ ≤ (Wnn g : ℝ) := hlocal.trans (by
        change _ ≤ (Wnn g : ℝ)
        exact_mod_cast Finset.single_le_sum
          (fun y _ => bot_le (a :=
            (⟨_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
              (_root_.SubdiffusiveProcess.Model.PotentialField.translate y g),
              _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg _⟩ : ℝ≥0))) hzS)
  refine ⟨Wnn, W, ?_, ?_, hderiv_bound, ?_, ?_⟩
  · intro g
    rfl
  · intro g
    rfl
  · intro g
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    · intro x hx
      exact (g.hasFDerivAt x).differentiableAt
    · intro x hx
      have hb : (‖fderiv ℝ (fun y => g y) x‖₊ : ℝ) ≤ (Wnn g : ℝ) := by
        have hb' := hderiv_bound g hx
        change ‖g.deriv x‖ ≤ (Wnn g : ℝ) at hb'
        simpa [(g.hasFDerivAt x).fderiv] using! hb'
      exact_mod_cast hb
    · exact convex_closedBall (0 : Homogenization.Vec d) R
  · intro g x y hx hy hxy
    obtain ⟨z, hzS, hzx⟩ : ∃ z, ∃ (_ : z ∈ S),
        x ∈ Metric.ball z (1 / 4 : ℝ) := by
      simpa only [mem_iUnion] using! hS hx
    have hzy : y ∈ Metric.ball z (1 / 2 : ℝ) := by
      rw [Metric.mem_ball, dist_eq_norm] at hzx
      have hzx' : ‖x - z‖ < (1 / 4 : ℝ) := by simpa [dist_eq_norm] using! hzx
      have hxy_rev : ‖y - x‖ < (1 / 4 : ℝ) := by simpa only [norm_sub_rev] using! hxy
      have htri : ‖y - z‖ ≤ ‖y - x‖ + ‖x - z‖ := by
        calc
          ‖y - z‖ = ‖(y - x) + (x - z)‖ := by congr 1; abel
          _ ≤ ‖y - x‖ + ‖x - z‖ := norm_add_le _ _
      have hy_norm : ‖y - z‖ < (1 / 2 : ℝ) := by linarith [htri, hxy_rev, hzx']
      simpa [Metric.mem_ball, dist_eq_norm] using! hy_norm
    have hlocal := _root_.SubdiffusiveProcess.Model.PotentialField.norm_deriv_sub_deriv_le_g2Observable_mul
      (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g)
      (hball_cube hzx) (hball_cube_half hzy)
    have hderiv :
        fderiv ℝ ((_root_.SubdiffusiveProcess.Model.PotentialField.translate z g :
          _root_.SubdiffusiveProcess.Model.PotentialField d) : Homogenization.Vec d → ℝ) (x-z) =
          fderiv ℝ (fun q => g q) x := by
      change fderiv ℝ (fun q => g (q + z)) (x - z) = _
      simpa only [sub_add_cancel] using!
        (fderiv_comp_add_right (𝕜 := ℝ) (f := (fun q => g q)) z (x := x-z))
    have hderiv' :
        fderiv ℝ ((_root_.SubdiffusiveProcess.Model.PotentialField.translate z g :
          _root_.SubdiffusiveProcess.Model.PotentialField d) : Homogenization.Vec d → ℝ) (y-z) =
          fderiv ℝ (fun q => g q) y := by
      change fderiv ℝ (fun q => g (q + z)) (y-z) = _
      simpa only [sub_add_cancel] using!
        (fderiv_comp_add_right (𝕜 := ℝ) (f := (fun q => g q)) z (x := y-z))
    calc
      ‖g.deriv x - g.deriv y‖ =
          ‖(_root_.SubdiffusiveProcess.Model.PotentialField.translate z g).deriv (x-z) -
            (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g).deriv (y-z)‖ := by
              rw [← (g.hasFDerivAt x).fderiv, ← (g.hasFDerivAt y).fderiv,
                ← (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g).hasFDerivAt
                  (x-z) |>.fderiv,
                ← (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g).hasFDerivAt
                  (y-z) |>.fderiv]
              rw [hderiv, hderiv']
      _ ≤ (Wnn g : ℝ) * ‖(x-z) - (y-z)‖ := hlocal.trans (by
        change _ ≤ (Wnn g : ℝ) * ‖(x-z) - (y-z)‖
        have hcoef := Finset.single_le_sum
          (fun q _ => bot_le (a :=
            (⟨_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
              (_root_.SubdiffusiveProcess.Model.PotentialField.translate q g),
              _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg _⟩ : ℝ≥0))) hzS
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcoef) (norm_nonneg _))
      _ = W g * ‖x-y‖ := by simp [W]

theorem exists_native_layer_joint_exp_square_bound
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (R : ℝ) (hR : 0 < R) :
  ∃ A : ℝ, 0 < A ∧
    ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ K : Compacts (SpatialCoordinates d),
        (∀ x ∈ (K : Set (SpatialCoordinates d)), ‖x‖ ≤ R) →
        ∀ n : ℕ,
          let μ : Measure (NativeBilateralPotentialSample d) :=
            Measure.infinitePi (fun _ : ℤ =>
              (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)
          let c : ℝ := (3 : ℝ) ^ (-(n + 1 : ℤ))
          let X : NativeBilateralPotentialSample d → ℝ := fun ω =>
            compactPotentialC1Norm K
              (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
                (positiveScaledNativeLayer ω n))
          let Y : NativeBilateralPotentialSample d → ℝ := fun ω =>
            compactGradientLipschitzObservable K
              (positiveScaledNativeLayer ω n)
          (∫⁻ ω, ENNReal.ofReal (Real.exp
            ((max (X ω / c) (Y ω / c^2) / (A * M.delta)) ^ 2)) ∂μ) ≤ 2 ∧
          (∀ ω, 0 ≤ X ω) ∧ (∀ ω, 0 ≤ Y ω)
    := by
  classical
  obtain ⟨S₀, hS₀⟩ :=
    (isCompact_closedBall (0 : Homogenization.Vec d) R).elim_finite_subcover
      (fun z : Homogenization.Vec d => Metric.ball z (1 / 4 : ℝ))
      (fun _ => Metric.isOpen_ball) (by
        intro x hx
        exact mem_iUnion.2 ⟨x, Metric.mem_ball_self (by norm_num)⟩)
  let S : Finset (Homogenization.Vec d) := insert 0 S₀
  have hSne : S.Nonempty := ⟨0, Finset.mem_insert_self 0 S₀⟩
  have hS : Metric.closedBall (0 : Homogenization.Vec d) R ⊆
      ⋃ z ∈ S, Metric.ball z (1 / 4 : ℝ) := by
    intro x hx
    obtain ⟨z, hzS₀, hzx⟩ : ∃ z, ∃ (_ : z ∈ S₀),
        x ∈ Metric.ball z (1 / 4 : ℝ) := by
      simpa only [mem_iUnion] using! hS₀ hx
    exact mem_iUnion.2 ⟨z, mem_iUnion.2 ⟨Finset.mem_insert_of_mem hzS₀, hzx⟩⟩
  have hball_cube {z x : Homogenization.Vec d}
      (hx : x ∈ Metric.ball z (1 / 4 : ℝ)) :
      x - z ∈ Homogenization.openCubeSet (Homogenization.originCube d 0) := by
    have hxm : x - z ∈ Metric.ball (0 : Homogenization.Vec d) (1 / 2 : ℝ) := by
      have hxnorm : ‖x - z‖ < (1 / 4 : ℝ) := by
        simpa [Metric.mem_ball, dist_eq_norm] using! hx
      have hx' : ‖x - z‖ < (1 / 2 : ℝ) := by
        linarith
      simpa [Metric.mem_ball, dist_zero_right, sub_zero] using! hx'
    rw [← Homogenization.ball_cubeCenter_eq_openCubeSet]
    have hcenter : Homogenization.cubeCenter
        (Homogenization.originCube d 0) = (0 : Homogenization.Vec d) := by
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
  have hball_cube_half {z x : Homogenization.Vec d}
      (hx : x ∈ Metric.ball z (1 / 2 : ℝ)) :
      x - z ∈ Homogenization.openCubeSet (Homogenization.originCube d 0) := by
    have hxm : x - z ∈ Metric.ball (0 : Homogenization.Vec d) (1 / 2 : ℝ) := by
      simpa [Metric.mem_ball, dist_zero_right, sub_zero, dist_eq_norm] using! hx
    rw [← Homogenization.ball_cubeCenter_eq_openCubeSet]
    have hcenter : Homogenization.cubeCenter
        (Homogenization.originCube d 0) = (0 : Homogenization.Vec d) := by
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
  obtain ⟨Wnn, W, hW, hWnn, hderiv_bound, hLipschitz, hderiv_diff⟩ :=
    cover_regularities R S hS hball_cube hball_cube_half
  have hExp : ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      (∫⁻ g, ENNReal.ofReal (Real.exp
        ((W g / ((S.card : ℝ) * M.delta)) ^ 2)) ∂
          (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ≤ 2 := by
    intro M
    have hWsum : ∀ g, W g = ∑ z ∈ S,
        _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
          (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g) := by
      intro g
      rw [hW g, hWnn g]
      exact NNReal.coe_sum S (fun z =>
        (⟨_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
          (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g),
          _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg _⟩ : ℝ≥0))
    simpa [hWsum, Finset.sum_const, nsmul_eq_mul] using
      (finite_sum_translated_g2_exp_square S hSne M)
  refine ⟨(S.card : ℝ) * max (R + 1) 8, ?_, ?_⟩
  · positivity
  intro M K hK n
  let μ₀ : Measure (_root_.SubdiffusiveProcess.Model.PotentialField d) :=
    (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  let μ : Measure (NativeBilateralPotentialSample d) :=
    Measure.infinitePi (fun _ : ℤ => μ₀)
  let c : ℝ := (3 : ℝ) ^ (-(n + 1 : ℤ))
  let g : NativeBilateralPotentialSample d →
      _root_.SubdiffusiveProcess.Model.PotentialField d := fun ω => ω (n + 1)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hc1 : c ≤ 1 := by
    dsimp [c]
    have he : -(n + 1 : ℤ) = -((n + 1 : ℕ) : ℤ) := by norm_num
    rw [he, zpow_neg, zpow_natCast]
    have hp : 0 < (3 : ℝ) ^ (n + 1) := by positivity
    exact (inv_le_one₀ hp).2 (one_le_pow₀ (by norm_num))
  have hcx (ω : NativeBilateralPotentialSample d)
      (x : K) : c • (x : SpatialCoordinates d) ∈
        Metric.closedBall (0 : SpatialCoordinates d) R := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hc.le]
    exact (mul_le_mul_of_nonneg_left (hK x x.property) hc.le).trans
      (by nlinarith [hc1])
  have hroot_value (ω : NativeBilateralPotentialSample d) :
      ‖(⟨fun x : K =>
          _root_.SubdiffusiveProcess.Model.PotentialField.anchor
            (positiveScaledNativeLayer ω n) x.1,
          (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
            (positiveScaledNativeLayer ω n)).1.1.continuous.comp
            continuous_subtype_val⟩ : C(K, ℝ))‖ ≤
        c * R * W (g ω) := by
    have hbase := norm_anchored_contraction_on_compact_le K
      (g ω).1.1 hc.le hc1 hR.le hK (hLipschitz (g ω))
    have heq :
        (⟨fun x : K =>
          _root_.SubdiffusiveProcess.Model.PotentialField.anchor
            (positiveScaledNativeLayer ω n) x.1,
          (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
            (positiveScaledNativeLayer ω n)).1.1.continuous.comp
            continuous_subtype_val⟩ : C(K, ℝ)) =
          ((g ω).1.1.comp (⟨fun x : SpatialCoordinates d =>
              c • x, by fun_prop⟩ :
            C(SpatialCoordinates d, SpatialCoordinates d))).restrict
              (K : Set (SpatialCoordinates d)) -
            ContinuousMap.const K ((g ω).1.1 0) := by
      apply ContinuousMap.ext
      intro x
      have he : -(n + 1 : ℤ) = -((n + 1 : ℕ) : ℤ) := by norm_num
      change (positiveScaledNativeLayer ω n).anchor x.1 =
        (g ω).1.1 (c • x.1) - (g ω).1.1 0
      simp [g, c, positiveScaledNativeLayer, he, zpow_neg, _root_.SubdiffusiveProcess.Model.PotentialField.anchor_apply,
        _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale_apply]
    rw [heq]
    rw [hW (g ω)]
    exact hbase
  have hroot_deriv (ω : NativeBilateralPotentialSample d) (x : K) :
      ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv
          (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
            (positiveScaledNativeLayer ω n)) x.1‖ ≤ c * W (g ω) := by
    rw [_root_.SubdiffusiveProcess.Model.PotentialField.anchor_deriv,
      positiveScaledNativeLayer_deriv]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc.le]
    exact mul_le_mul_of_nonneg_left (hderiv_bound (g ω) (hcx ω x)) hc.le
  have hW0 (ω : NativeBilateralPotentialSample d) : 0 ≤ W (g ω) := by
    rw [hW (g ω)]
    exact NNReal.zero_le_coe
  have hXbound (ω : NativeBilateralPotentialSample d) :
      compactPotentialC1Norm K
          (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
            (positiveScaledNativeLayer ω n)) ≤
        c * (R + 1) * W (g ω) := by
    unfold compactPotentialC1Norm
    have hv := hroot_value ω
    have hWω : 0 ≤ W (g ω) := hW0 ω
    have hd : ‖(⟨fun x : K =>
        _root_.SubdiffusiveProcess.Model.PotentialField.deriv
          (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
            (positiveScaledNativeLayer ω n)) x.1,
        (_root_.SubdiffusiveProcess.Model.PotentialField.deriv
          (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
            (positiveScaledNativeLayer ω n))).continuous.comp
          continuous_subtype_val⟩ : C(K, SpatialCoordinates d →L[ℝ] ℝ))‖ ≤
          c * W (g ω) := by
      apply (ContinuousMap.norm_le _ (mul_nonneg hc.le hWω)).2
      intro x
      exact hroot_deriv ω x
    nlinarith [hWω, hc.le]
  have hYratio (ω : NativeBilateralPotentialSample d)
      {x y : K} (hxy : x ≠ y) :
      ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv
          (positiveScaledNativeLayer ω n) x.1 -
        _root_.SubdiffusiveProcess.Model.PotentialField.deriv
          (positiveScaledNativeLayer ω n) y.1‖ /
          ‖x.1 - y.1‖ ≤ 8 * c^2 * W (g ω) := by
    have hcx' := hcx ω x
    have hcy' := hcx ω y
    have hxyv : (x : SpatialCoordinates d) ≠ y := by
      intro h
      apply hxy
      exact Subtype.ext h
    have hden : 0 < ‖x.1 - y.1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxyv)
    by_cases hs : ‖c • (x.1 - y.1)‖ < (1 / 4 : ℝ)
    · have hsmall : ‖c • (x.1 - y.1)‖ < (1 / 4 : ℝ) := hs
      have hsmall' : ‖c • x.1 - c • y.1‖ < (1 / 4 : ℝ) := by
        rw [← smul_sub]
        exact hsmall
      have hdsmall := hderiv_diff (g ω) hcx' hcy' (by
        exact hsmall')
      have hdx : _root_.SubdiffusiveProcess.Model.PotentialField.deriv
          (positiveScaledNativeLayer ω n) x.1 =
          c • (g ω).deriv (c • x.1) := by
        simpa only [g, c, Nat.cast_add, Nat.cast_one] using! positiveScaledNativeLayer_deriv ω n x.1
      have hdy : _root_.SubdiffusiveProcess.Model.PotentialField.deriv
          (positiveScaledNativeLayer ω n) y.1 =
          c • (g ω).deriv (c • y.1) := by
        simpa only [g, c, Nat.cast_add, Nat.cast_one] using! positiveScaledNativeLayer_deriv ω n y.1
      have hsmul : c • (g ω).deriv (c • x.1) - c • (g ω).deriv (c • y.1) =
          c • ((g ω).deriv (c • x.1) - (g ω).deriv (c • y.1)) := by
        rw [smul_sub]
      rw [hdx, hdy, hsmul, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hc.le, div_le_iff₀ hden]
      have hnorm : ‖c • (x.1 - y.1)‖ = c * ‖x.1 - y.1‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc.le]
      have hnorm' : ‖c • x.1 - c • y.1‖ = c * ‖x.1 - y.1‖ := by
        rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc.le]
      rw [hnorm'] at hdsmall
      calc
        c * ‖(g ω).deriv (c • x.1) - (g ω).deriv (c • y.1)‖ ≤
            c * (W (g ω) * (c * ‖x.1 - y.1‖)) :=
          mul_le_mul_of_nonneg_left hdsmall hc.le
        _ = c^2 * W (g ω) * ‖x.1 - y.1‖ := by ring
        _ ≤ 8 * c^2 * W (g ω) * ‖x.1 - y.1‖ := by
          have hprod : 0 ≤ c^2 * W (g ω) * ‖x.1 - y.1‖ :=
            mul_nonneg (mul_nonneg (sq_nonneg c)
              (hW0 ω))
              (norm_nonneg (x.1 - y.1))
          nlinarith [hprod]
    · have hfar : (1 / 4 : ℝ) ≤ ‖c • (x.1 - y.1)‖ := le_of_not_gt hs
      have hdxy := hderiv_bound (g ω) hcx'
      have hdyy := hderiv_bound (g ω) hcy'
      have hdx : _root_.SubdiffusiveProcess.Model.PotentialField.deriv
          (positiveScaledNativeLayer ω n) x.1 =
          c • (g ω).deriv (c • x.1) := by
        simpa only [g, c, Nat.cast_add, Nat.cast_one] using! positiveScaledNativeLayer_deriv ω n x.1
      have hdy : _root_.SubdiffusiveProcess.Model.PotentialField.deriv
          (positiveScaledNativeLayer ω n) y.1 =
          c • (g ω).deriv (c • y.1) := by
        simpa only [g, c, Nat.cast_add, Nat.cast_one] using! positiveScaledNativeLayer_deriv ω n y.1
      have hsmul : c • (g ω).deriv (c • x.1) - c • (g ω).deriv (c • y.1) =
          c • ((g ω).deriv (c • x.1) - (g ω).deriv (c • y.1)) := by
        rw [smul_sub]
      rw [hdx, hdy, hsmul, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hc.le, div_le_iff₀ hden]
      have hnorm : ‖c • (x.1 - y.1)‖ = c * ‖x.1 - y.1‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc.le]
      have hdiff : ‖(g ω).deriv (c • x.1) - (g ω).deriv (c • y.1)‖ ≤
          2 * W (g ω) := by
        calc
          _ ≤ ‖(g ω).deriv (c • x.1)‖ + ‖(g ω).deriv (c • y.1)‖ := norm_sub_le _ _
          _ ≤ 2 * W (g ω) := by nlinarith
      have hfactor : 2 ≤ 8 * c * ‖x.1 - y.1‖ := by
        rw [hnorm] at hfar
        nlinarith [hfar]
      have hcw : 0 ≤ c * W (g ω) := mul_nonneg hc.le
        (hW0 ω)
      calc
        c * ‖(g ω).deriv (c • x.1) - (g ω).deriv (c • y.1)‖ ≤
            c * (2 * W (g ω)) := mul_le_mul_of_nonneg_left hdiff hc.le
        _ = (c * W (g ω)) * 2 := by ring
        _ ≤ (c * W (g ω)) * (8 * c * ‖x.1 - y.1‖) :=
          mul_le_mul_of_nonneg_left hfactor hcw
        _ = 8 * c^2 * W (g ω) * ‖x.1 - y.1‖ := by ring
  have hYbound (ω : NativeBilateralPotentialSample d) :
      compactGradientLipschitzObservable K
          (positiveScaledNativeLayer ω n) ≤ 8 * c^2 * W (g ω) := by
    unfold compactGradientLipschitzObservable
    apply Real.sSup_le
    · rintro q ⟨x, y, hxy, rfl⟩
      exact hYratio ω hxy
    · exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg c))
        (hW0 ω)
  have hApos : 0 < (S.card : ℝ) * max (R + 1) 8 := by
    have hcard : 0 < (S.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hSne
    have hmax : 0 < max (R + 1) 8 :=
      lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    exact mul_pos hcard hmax
  have hpoint (ω : NativeBilateralPotentialSample d) :
      max (
          compactPotentialC1Norm K
            (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
              (positiveScaledNativeLayer ω n)) / c)
        (compactGradientLipschitzObservable K
          (positiveScaledNativeLayer ω n) / c^2) /
          ((S.card : ℝ) * max (R + 1) 8 * M.delta) ≤
        W (g ω) / ((S.card : ℝ) * M.delta) := by
    have hcard : 0 < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hSne
    have hδ : 0 < M.delta := M.shellPrefix.delta_pos
    have hc2 : 0 < c^2 := sq_pos_of_pos hc
    have hX := hXbound ω
    have hY := hYbound ω
    have hmax : max
          (compactPotentialC1Norm K
            (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
              (positiveScaledNativeLayer ω n)) / c)
          (compactGradientLipschitzObservable K
            (positiveScaledNativeLayer ω n) / c^2) ≤
        max (R + 1) 8 * W (g ω) :=
      max_scaled_bound hc (hW0 ω) hX hY
    have hdenpos : 0 < (S.card : ℝ) * max (R + 1) 8 * M.delta := by
      exact mul_pos (mul_pos hcard
        (lt_of_lt_of_le (by norm_num) (le_max_right _ _))) hδ
    apply (div_le_iff₀ hdenpos).2
    calc
      _ ≤ max (R + 1) 8 * W (g ω) := hmax
      _ = (W (g ω) / ((S.card : ℝ) * M.delta)) *
          ((S.card : ℝ) * max (R + 1) 8 * M.delta) := by
        exact scale_den_identity hcard hδ
  have hX0 (ω : NativeBilateralPotentialSample d) :
      0 ≤ compactPotentialC1Norm K
        (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
          (positiveScaledNativeLayer ω n)) := by
    exact compact_c1_nonneg K
      (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
        (positiveScaledNativeLayer ω n))
  have hY0 (ω : NativeBilateralPotentialSample d) :
      0 ≤ compactGradientLipschitzObservable K
        (positiveScaledNativeLayer ω n) := by
    unfold compactGradientLipschitzObservable
    apply Real.sSup_nonneg
    rintro q ⟨x, y, hxy, rfl⟩
    exact div_nonneg
      (norm_nonneg
        (_root_.SubdiffusiveProcess.Model.PotentialField.deriv
            (positiveScaledNativeLayer ω n) x.1 -
          _root_.SubdiffusiveProcess.Model.PotentialField.deriv
            (positiveScaledNativeLayer ω n) y.1))
      (norm_nonneg (x.1 - y.1))
  let F : _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ≥0∞ := fun g =>
    ENNReal.ofReal (Real.exp ((W g / ((S.card : ℝ) * M.delta)) ^ 2))
  have hFmeas : Measurable F := by
    have hWmeas : Measurable W := by
      have hWmeas' : Measurable (fun g => ∑ z ∈ S,
          _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
            (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g)) := by
        apply Finset.measurable_sum
        intro z hz
        exact _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_measurable.comp
          (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate z)
      have heq : W = fun g => ∑ z ∈ S,
          _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
            (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g) := by
        funext g
        rw [hW g, hWnn g]
        exact NNReal.coe_sum S (fun z =>
          (⟨_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
            (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g),
            _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg _⟩ : ℝ≥0))
      rw [heq]
      exact hWmeas'
    exact (((hWmeas.div_const _).pow_const 2).exp).ennreal_ofReal
  have heval := measurePreserving_eval_infinitePi
    (fun _ : ℤ => μ₀) (n + 1)
  have hroot := hExp M
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · change (∫⁻ ω, ENNReal.ofReal (Real.exp
      ((max (_ / c) (_ / c^2) /
        ((S.card : ℝ) * max (R + 1) 8 * M.delta)) ^ 2)) ∂μ) ≤ 2
    apply lintegral_le_of_measurePreserving_comp heval hFmeas
    · intro ω
      have hleft : 0 ≤ max
          (compactPotentialC1Norm K
            (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
              (positiveScaledNativeLayer ω n)) / c)
          (compactGradientLipschitzObservable K
            (positiveScaledNativeLayer ω n) / c^2) /
          ((S.card : ℝ) * max (R + 1) 8 * M.delta) := by
        have hcard : 0 < (S.card : ℝ) := by
          exact_mod_cast Finset.card_pos.mpr hSne
        have hδ : 0 < M.delta := M.shellPrefix.delta_pos
        have hden : 0 < (S.card : ℝ) * max (R + 1) 8 * M.delta := by
          exact mul_pos (mul_pos hcard
            (lt_of_lt_of_le (by norm_num) (le_max_right _ _))) hδ
        apply div_nonneg _ hden.le
        exact (div_nonneg (hX0 ω) hc.le).trans (le_max_left _ _)
      have hright : 0 ≤ W (g ω) / ((S.card : ℝ) * M.delta) :=
        div_nonneg (hW0 ω) (mul_nonneg (by positivity)
          M.shellPrefix.delta_pos.le)
      exact ENNReal.ofReal_mono
        (Real.exp_le_exp.mpr ((sq_le_sq₀ hleft hright).2 (hpoint ω)))
    · simpa [F, g, μ₀] using! hroot
  · exact hX0
  · exact hY0


end SubdiffusiveProcess
