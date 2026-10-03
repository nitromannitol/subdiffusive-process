module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowFractionalCellCutoff

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Homogenization
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The squared modulus density of a scalar field, in the exact shape of
`fluxRowInverseFourierDensity`. -/
def fluxRowFractionalDensityOf (v : Vec d → ℂ) (x : Vec d) : ℝ≥0∞ :=
  ENNReal.ofReal ‖v x‖ ^ 2

theorem fluxRowFractionalDensityOf_eq (v : Vec d → ℂ) (x : Vec d) :
    fluxRowFractionalDensityOf v x = ENNReal.ofReal (‖v x‖ ^ 2) := by
  rw [fluxRowFractionalDensityOf, ← ENNReal.ofReal_pow (norm_nonneg _)]

theorem measurable_fluxRowFractionalDensityOf {v : Vec d → ℂ}
    (hv : Measurable v) : Measurable (fluxRowFractionalDensityOf v) :=
  (hv.norm.ennreal_ofReal).pow_const 2

/-- The mass of a cutoff-localized field is at most the mass on the cell. -/
theorem fluxRowFractional_lintegral_densityOf_cutoff_le {U : Set (Vec d)}
    (hU : MeasurableSet U) {chi : Vec d → ℝ} (hchi0 : ∀ x, 0 ≤ chi x)
    (hchi1 : ∀ x, chi x ≤ 1) (hchisupp : ∀ x, x ∉ U → chi x = 0)
    (v : Vec d → ℂ) :
    ∫⁻ x, fluxRowFractionalDensityOf (fun x ↦ (chi x : ℂ) * v x) x ∂volume ≤
      ∫⁻ x in U, fluxRowFractionalDensityOf v x ∂volume := by
  classical
  have hpoint : ∀ x, fluxRowFractionalDensityOf (fun x ↦ (chi x : ℂ) * v x) x ≤
      U.indicator (fluxRowFractionalDensityOf v) x := by
    intro x
    by_cases hx : x ∈ U
    · rw [Set.indicator_of_mem hx]
      simp only [fluxRowFractionalDensityOf, norm_mul, Complex.norm_real,
        Real.norm_eq_abs]
      have habs : |chi x| ≤ 1 := abs_le.2 ⟨by linarith [hchi0 x], hchi1 x⟩
      have : ENNReal.ofReal (|chi x| * ‖v x‖) ≤ ENNReal.ofReal ‖v x‖ := by
        apply ENNReal.ofReal_le_ofReal
        nlinarith [norm_nonneg (v x), abs_nonneg (chi x)]
      exact pow_le_pow_left' this 2
    · rw [Set.indicator_of_notMem hx]
      simp [fluxRowFractionalDensityOf, hchisupp x hx]
  calc ∫⁻ x, fluxRowFractionalDensityOf (fun x ↦ (chi x : ℂ) * v x) x ∂volume
      ≤ ∫⁻ x, U.indicator (fluxRowFractionalDensityOf v) x ∂volume :=
        lintegral_mono hpoint
    _ = ∫⁻ x in U, fluxRowFractionalDensityOf v x ∂volume :=
        lintegral_indicator hU _

/-- **The cutoff energy transfer.**  The whole-space positive energy of the
cutoff-localized field is bounded by the cell energy of the field, with a
constant depending only on `d`, `sigma` and the Lipschitz constant. -/
theorem fluxRowFractional_cutoff_globalPositiveEnergy_le {sigma Lam : ℝ}
    (hsigma : 0 ≤ sigma) (hLam : 0 < Lam) {U : Set (Vec d)}
    (hU : MeasurableSet U) {chi : Vec d → ℝ} (hchi0 : ∀ x, 0 ≤ chi x)
    (hchi1 : ∀ x, chi x ≤ 1) (hchisupp : ∀ x, x ∉ U → chi x = 0)
    (hchiLip : ∀ x y, |chi x - chi y| ≤ Lam * ‖x - y‖)
    {v : Vec d → ℂ} (hv : Measurable v) (W : ℝ≥0∞) :
    fluxRowGlobalPositiveEnergy volume W
        (fluxRowFractionalKernelOf sigma (fun x ↦ (chi x : ℂ) * v x))
        (fluxRowFractionalDensityOf (fun x ↦ (chi x : ℂ) * v x)) ≤
      2 * ∫⁻ z in U ×ˢ U, fluxRowFractionalKernelOf sigma v z
          ∂((volume : Measure (Vec d)).prod volume) +
        (4 * ENNReal.ofReal sigma * ENNReal.ofReal (Real.rpow Lam (2 * sigma)) *
          fluxRowFractionalCutoffConst d sigma + W) *
          ∫⁻ x in U, fluxRowFractionalDensityOf v x ∂volume := by
  have hgag := fluxRowFractional_cutoff_gagliardo_le hsigma hLam hU hchi0 hchi1
    hchisupp hchiLip hv
  have hmass := fluxRowFractional_lintegral_densityOf_cutoff_le hU hchi0 hchi1
    hchisupp v
  have hdens : ∫⁻ x in U, ENNReal.ofReal (‖v x‖ ^ 2) ∂volume =
      ∫⁻ x in U, fluxRowFractionalDensityOf v x ∂volume :=
    lintegral_congr fun x ↦ (fluxRowFractionalDensityOf_eq v x).symm
  rw [hdens] at hgag
  calc fluxRowGlobalPositiveEnergy volume W
        (fluxRowFractionalKernelOf sigma (fun x ↦ (chi x : ℂ) * v x))
        (fluxRowFractionalDensityOf (fun x ↦ (chi x : ℂ) * v x))
      = (∫⁻ z, fluxRowFractionalKernelOf sigma (fun x ↦ (chi x : ℂ) * v x) z
            ∂((volume : Measure (Vec d)).prod volume)) +
          W * ∫⁻ x, fluxRowFractionalDensityOf (fun x ↦ (chi x : ℂ) * v x) x
            ∂volume := rfl
    _ ≤ (2 * ∫⁻ z in U ×ˢ U, fluxRowFractionalKernelOf sigma v z
            ∂((volume : Measure (Vec d)).prod volume) +
          4 * ENNReal.ofReal sigma * ENNReal.ofReal (Real.rpow Lam (2 * sigma)) *
            fluxRowFractionalCutoffConst d sigma *
            ∫⁻ x in U, fluxRowFractionalDensityOf v x ∂volume) +
          W * ∫⁻ x in U, fluxRowFractionalDensityOf v x ∂volume :=
        add_le_add hgag (mul_le_mul' le_rfl hmass)
    _ = 2 * ∫⁻ z in U ×ˢ U, fluxRowFractionalKernelOf sigma v z
            ∂((volume : Measure (Vec d)).prod volume) +
          (4 * ENNReal.ofReal sigma *
            ENNReal.ofReal (Real.rpow Lam (2 * sigma)) *
            fluxRowFractionalCutoffConst d sigma + W) *
            ∫⁻ x in U, fluxRowFractionalDensityOf v x ∂volume := by
        rw [add_mul]
        ring

/-- The cutoff energy transfer against a single cell constant. -/
theorem fluxRowFractional_cutoff_globalPositiveEnergy_le_local {sigma Lam : ℝ}
    (hsigma : 0 ≤ sigma) (hLam : 0 < Lam) {U : Set (Vec d)}
    (hU : MeasurableSet U) {chi : Vec d → ℝ} (hchi0 : ∀ x, 0 ≤ chi x)
    (hchi1 : ∀ x, chi x ≤ 1) (hchisupp : ∀ x, x ∉ U → chi x = 0)
    (hchiLip : ∀ x y, |chi x - chi y| ≤ Lam * ‖x - y‖)
    {v : Vec d → ℂ} (hv : Measurable v) (W w K : ℝ≥0∞) (hK : 2 ≤ K)
    (hKw : 4 * ENNReal.ofReal sigma *
      ENNReal.ofReal (Real.rpow Lam (2 * sigma)) *
      fluxRowFractionalCutoffConst d sigma + W ≤ K * w) :
    fluxRowGlobalPositiveEnergy volume W
        (fluxRowFractionalKernelOf sigma (fun x ↦ (chi x : ℂ) * v x))
        (fluxRowFractionalDensityOf (fun x ↦ (chi x : ℂ) * v x)) ≤
      K * fluxRowLocalPositiveEnergy volume U w
        (fluxRowFractionalKernelOf sigma v) (fluxRowFractionalDensityOf v) := by
  refine (fluxRowFractional_cutoff_globalPositiveEnergy_le hsigma hLam hU hchi0
    hchi1 hchisupp hchiLip hv W).trans ?_
  rw [fluxRowLocalPositiveEnergy, mul_add]
  refine add_le_add (mul_le_mul' hK le_rfl) ?_
  rw [← mul_assoc]
  exact mul_le_mul' hKw le_rfl

/-- The cutoff-localized physical pairing on a cell, normalized by the cell
volume, in the shape of `FluxRowRieszPartition.cellPairing`. -/
def fluxRowFractionalCellPairing (chi : Vec d → ℝ) (cellVolume : ℝ)
    (F : Vec d → Vec d) (i : Fin d) (v : Vec d → ℂ) : ℂ :=
  (cellVolume : ℂ)⁻¹ *
    ∫ x, Complex.ofReal (F x i) * ((chi x : ℂ) * v x) ∂volume

theorem re_fluxRowFractionalCellPairing (chi : Vec d → ℝ) (cellVolume : ℝ)
    (F : Vec d → Vec d) (i : Fin d) (v : Vec d → ℂ) :
    (fluxRowFractionalCellPairing chi cellVolume F i v).re =
      cellVolume⁻¹ *
        (∫ x, Complex.ofReal (F x i) * ((chi x : ℂ) * v x) ∂volume).re := by
  unfold fluxRowFractionalCellPairing
  rw [← Complex.ofReal_inv, Complex.mul_re]
  simp

/-- **The per-cell pairing bound.**  A whole-space dual bound for the flux
against the cutoff-localized test yields the pairing inequality in exactly the
currency of `FluxRowRieszPartitionInput.pairing_re_le`: a per-cell negative
constant times `sqrt (localPositiveEnergy / cellVolume)`. -/
theorem fluxRowFractional_abs_re_cellPairing_le {sigma Lam : ℝ}
    (hsigma : 0 ≤ sigma) (hLam : 0 < Lam) {U : Set (Vec d)}
    (hU : MeasurableSet U) {chi : Vec d → ℝ} (hchi0 : ∀ x, 0 ≤ chi x)
    (hchi1 : ∀ x, chi x ≤ 1) (hchisupp : ∀ x, x ∉ U → chi x = 0)
    (hchiLip : ∀ x y, |chi x - chi y| ≤ Lam * ‖x - y‖)
    {v : Vec d → ℂ} (hv : Measurable v) (F : Vec d → Vec d) (i : Fin d)
    (W w K : ℝ≥0∞) (hK : 2 ≤ K) (hKtop : K ≠ ∞)
    (hKw : 4 * ENNReal.ofReal sigma *
      ENNReal.ofReal (Real.rpow Lam (2 * sigma)) *
      fluxRowFractionalCutoffConst d sigma + W ≤ K * w)
    (hlocal : fluxRowLocalPositiveEnergy volume U w
      (fluxRowFractionalKernelOf sigma v) (fluxRowFractionalDensityOf v) ≠ ∞)
    (cellVolume N : ℝ) (hcell : 0 < cellVolume) (hN : 0 ≤ N)
    (hdual : |(∫ x, Complex.ofReal (F x i) * ((chi x : ℂ) * v x) ∂volume).re| ≤
      N * Real.sqrt (fluxRowGlobalPositiveEnergy volume W
        (fluxRowFractionalKernelOf sigma (fun x ↦ (chi x : ℂ) * v x))
        (fluxRowFractionalDensityOf (fun x ↦ (chi x : ℂ) * v x))).toReal) :
    |(fluxRowFractionalCellPairing chi cellVolume F i v).re| ≤
      (N * Real.sqrt K.toReal / Real.sqrt cellVolume) *
        Real.sqrt ((fluxRowLocalPositiveEnergy volume U w
          (fluxRowFractionalKernelOf sigma v)
          (fluxRowFractionalDensityOf v)).toReal / cellVolume) := by
  set L : ℝ≥0∞ := fluxRowLocalPositiveEnergy volume U w
    (fluxRowFractionalKernelOf sigma v) (fluxRowFractionalDensityOf v) with hLdef
  set G : ℝ≥0∞ := fluxRowGlobalPositiveEnergy volume W
    (fluxRowFractionalKernelOf sigma (fun x ↦ (chi x : ℂ) * v x))
    (fluxRowFractionalDensityOf (fun x ↦ (chi x : ℂ) * v x)) with hGdef
  have htransfer : G ≤ K * L :=
    fluxRowFractional_cutoff_globalPositiveEnergy_le_local hsigma hLam hU hchi0
      hchi1 hchisupp hchiLip hv W w K hK hKw
  have hKL : K * L ≠ ∞ := ENNReal.mul_ne_top hKtop hlocal
  have htoReal : G.toReal ≤ K.toReal * L.toReal := by
    have := ENNReal.toReal_mono hKL htransfer
    rwa [ENNReal.toReal_mul] at this
  have hsqrtG : Real.sqrt G.toReal ≤ Real.sqrt K.toReal * Real.sqrt L.toReal := by
    rw [← Real.sqrt_mul ENNReal.toReal_nonneg]
    exact Real.sqrt_le_sqrt htoReal
  have hcv : Real.sqrt cellVolume > 0 := Real.sqrt_pos.2 hcell
  have hsplit : Real.sqrt (L.toReal / cellVolume) =
      Real.sqrt L.toReal / Real.sqrt cellVolume :=
    Real.sqrt_div ENNReal.toReal_nonneg cellVolume
  calc |(fluxRowFractionalCellPairing chi cellVolume F i v).re|
      = cellVolume⁻¹ *
        |(∫ x, Complex.ofReal (F x i) * ((chi x : ℂ) * v x) ∂volume).re| := by
        rw [re_fluxRowFractionalCellPairing chi cellVolume F i v, abs_mul,
          abs_of_pos (inv_pos.2 hcell)]
    _ ≤ cellVolume⁻¹ * (N * Real.sqrt G.toReal) :=
        mul_le_mul_of_nonneg_left hdual (inv_pos.2 hcell).le
    _ ≤ cellVolume⁻¹ * (N * (Real.sqrt K.toReal * Real.sqrt L.toReal)) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hcell).le
        exact mul_le_mul_of_nonneg_left hsqrtG hN
    _ = (N * Real.sqrt K.toReal / Real.sqrt cellVolume) *
          Real.sqrt (L.toReal / cellVolume) := by
        rw [hsplit]
        have hmm : Real.sqrt cellVolume ^ 2 = cellVolume := Real.sq_sqrt hcell.le
        field_simp
        rw [hmm]
        ring

theorem im_fluxRowFractionalCellPairing (chi : Vec d → ℝ) (cellVolume : ℝ)
    (F : Vec d → Vec d) (i : Fin d) (v : Vec d → ℂ) :
    (fluxRowFractionalCellPairing chi cellVolume F i v).im =
      cellVolume⁻¹ *
        (∫ x, Complex.ofReal (F x i) * ((chi x : ℂ) * v x) ∂volume).im := by
  unfold fluxRowFractionalCellPairing
  rw [← Complex.ofReal_inv, Complex.mul_im]
  simp

/-- **The per-cell pairing bound.**  A whole-space dual bound for the flux
against the cutoff-localized test yields the pairing inequality in exactly the
currency of `FluxRowRieszPartitionInput.pairing_im_le`: a per-cell negative
constant times `sqrt (localPositiveEnergy / cellVolume)`. -/
theorem fluxRowFractional_abs_im_cellPairing_le {sigma Lam : ℝ}
    (hsigma : 0 ≤ sigma) (hLam : 0 < Lam) {U : Set (Vec d)}
    (hU : MeasurableSet U) {chi : Vec d → ℝ} (hchi0 : ∀ x, 0 ≤ chi x)
    (hchi1 : ∀ x, chi x ≤ 1) (hchisupp : ∀ x, x ∉ U → chi x = 0)
    (hchiLip : ∀ x y, |chi x - chi y| ≤ Lam * ‖x - y‖)
    {v : Vec d → ℂ} (hv : Measurable v) (F : Vec d → Vec d) (i : Fin d)
    (W w K : ℝ≥0∞) (hK : 2 ≤ K) (hKtop : K ≠ ∞)
    (hKw : 4 * ENNReal.ofReal sigma *
      ENNReal.ofReal (Real.rpow Lam (2 * sigma)) *
      fluxRowFractionalCutoffConst d sigma + W ≤ K * w)
    (hlocal : fluxRowLocalPositiveEnergy volume U w
      (fluxRowFractionalKernelOf sigma v) (fluxRowFractionalDensityOf v) ≠ ∞)
    (cellVolume N : ℝ) (hcell : 0 < cellVolume) (hN : 0 ≤ N)
    (hdual : |(∫ x, Complex.ofReal (F x i) * ((chi x : ℂ) * v x) ∂volume).im| ≤
      N * Real.sqrt (fluxRowGlobalPositiveEnergy volume W
        (fluxRowFractionalKernelOf sigma (fun x ↦ (chi x : ℂ) * v x))
        (fluxRowFractionalDensityOf (fun x ↦ (chi x : ℂ) * v x))).toReal) :
    |(fluxRowFractionalCellPairing chi cellVolume F i v).im| ≤
      (N * Real.sqrt K.toReal / Real.sqrt cellVolume) *
        Real.sqrt ((fluxRowLocalPositiveEnergy volume U w
          (fluxRowFractionalKernelOf sigma v)
          (fluxRowFractionalDensityOf v)).toReal / cellVolume) := by
  set L : ℝ≥0∞ := fluxRowLocalPositiveEnergy volume U w
    (fluxRowFractionalKernelOf sigma v) (fluxRowFractionalDensityOf v) with hLdef
  set G : ℝ≥0∞ := fluxRowGlobalPositiveEnergy volume W
    (fluxRowFractionalKernelOf sigma (fun x ↦ (chi x : ℂ) * v x))
    (fluxRowFractionalDensityOf (fun x ↦ (chi x : ℂ) * v x)) with hGdef
  have htransfer : G ≤ K * L :=
    fluxRowFractional_cutoff_globalPositiveEnergy_le_local hsigma hLam hU hchi0
      hchi1 hchisupp hchiLip hv W w K hK hKw
  have hKL : K * L ≠ ∞ := ENNReal.mul_ne_top hKtop hlocal
  have htoReal : G.toReal ≤ K.toReal * L.toReal := by
    have := ENNReal.toReal_mono hKL htransfer
    rwa [ENNReal.toReal_mul] at this
  have hsqrtG : Real.sqrt G.toReal ≤ Real.sqrt K.toReal * Real.sqrt L.toReal := by
    rw [← Real.sqrt_mul ENNReal.toReal_nonneg]
    exact Real.sqrt_le_sqrt htoReal
  have hcv : Real.sqrt cellVolume > 0 := Real.sqrt_pos.2 hcell
  have hsplit : Real.sqrt (L.toReal / cellVolume) =
      Real.sqrt L.toReal / Real.sqrt cellVolume :=
    Real.sqrt_div ENNReal.toReal_nonneg cellVolume
  calc |(fluxRowFractionalCellPairing chi cellVolume F i v).im|
      = cellVolume⁻¹ *
        |(∫ x, Complex.ofReal (F x i) * ((chi x : ℂ) * v x) ∂volume).im| := by
        rw [im_fluxRowFractionalCellPairing chi cellVolume F i v, abs_mul,
          abs_of_pos (inv_pos.2 hcell)]
    _ ≤ cellVolume⁻¹ * (N * Real.sqrt G.toReal) :=
        mul_le_mul_of_nonneg_left hdual (inv_pos.2 hcell).le
    _ ≤ cellVolume⁻¹ * (N * (Real.sqrt K.toReal * Real.sqrt L.toReal)) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hcell).le
        exact mul_le_mul_of_nonneg_left hsqrtG hN
    _ = (N * Real.sqrt K.toReal / Real.sqrt cellVolume) *
          Real.sqrt (L.toReal / cellVolume) := by
        rw [hsplit]
        have hmm : Real.sqrt cellVolume ^ 2 = cellVolume := Real.sq_sqrt hcell.le
        field_simp
        rw [hmm]
        ring

/-! ### Reconstruction of the whole-space pairing from cutoff pairings -/

open Filter Topology in
/-- Dominated convergence for a bounded pointwise-convergent multiplier. -/
theorem fluxRowFractional_tendsto_integral_mul {X : Type*} [MeasurableSpace X]
    (mu : Measure X) {f : X → ℂ} (hf : Integrable f mu) (g : ℕ → X → ℝ)
    (hgm : ∀ n, Measurable (g n)) (hg0 : ∀ n x, 0 ≤ g n x)
    (hg1 : ∀ n x, g n x ≤ 1)
    (hglim : ∀ x, Tendsto (fun n ↦ g n x) atTop (𝓝 1)) :
    Tendsto (fun n ↦ ∫ x, (g n x : ℂ) * f x ∂mu) atTop (𝓝 (∫ x, f x ∂mu)) := by
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun x ↦ ‖f x‖) (fun n ↦ ?_) hf.norm (fun n ↦ ?_)
    (Filter.Eventually.of_forall fun x ↦ ?_)
  · exact MeasureTheory.AEStronglyMeasurable.mul
      ((hgm n).complex_ofReal.aestronglyMeasurable) hf.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x ↦ ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg0 n x)]
    exact mul_le_of_le_one_left (norm_nonneg (f x)) (hg1 n x)
  · have h1 : Tendsto (fun n ↦ ((g n x : ℝ) : ℂ)) atTop (𝓝 1) := by
      simpa only [Function.comp_apply, Complex.ofReal_one] using! (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp (hglim x)
    simpa using h1.mul_const (f x)

open Filter Topology in
/-- **The cutoff pairings reconstruct the physical pairing.**  For a smooth
partition of unity exhausted by the finite families `cells n`, the volume
weighted sums of the cutoff cell pairings converge to the whole-space
pairing.  This is exactly the `hlimit` hypothesis of
`exists_fluxHat_massiveNegativeSobolevNormSq_le_of_stopping_exhaustion`, so
the abstract Riesz engine accepts smooth cutoffs in place of indicator
ownership pieces without any change. -/
theorem fluxRowFractional_tendsto_cellPairing {Cell : Type*} [DecidableEq Cell]
    (cells : ℕ → Finset Cell) (chi : Cell → Vec d → ℝ)
    (hchim : ∀ q, Measurable (chi q)) (hchi0 : ∀ q x, 0 ≤ chi q x)
    (hchi1 : ∀ q x, chi q x ≤ 1)
    (hsum1 : ∀ n x, ∑ q ∈ cells n, chi q x ≤ 1)
    (hsumlim : ∀ x, Tendsto (fun n ↦ ∑ q ∈ cells n, chi q x) atTop (𝓝 1))
    (cellVolume : Cell → ℝ) (hvol : ∀ q, cellVolume q ≠ 0)
    (F : Vec d → Vec d) (i : Fin d) (v : Vec d → ℂ)
    (hint : Integrable (fun x ↦ Complex.ofReal (F x i) * v x) volume) :
    Tendsto (fun n ↦ Complex.mk
        (fluxRowLocalizedPairing (cells n) cellVolume
          (fun q ↦ (fluxRowFractionalCellPairing (chi q) (cellVolume q) F i v).re))
        (fluxRowLocalizedPairing (cells n) cellVolume
          (fun q ↦ (fluxRowFractionalCellPairing (chi q) (cellVolume q) F i v).im)))
      atTop (𝓝 (∫ x, Complex.ofReal (F x i) * v x ∂volume)) := by
  classical
  set f : Vec d → ℂ := fun x ↦ Complex.ofReal (F x i) * v x with hfdef
  have hintq : ∀ q : Cell,
      Integrable (fun x ↦ (chi q x : ℂ) * f x) volume := by
    intro q
    refine hint.bdd_mul (c := 1) ((hchim q).complex_ofReal).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hchi0 q x)]
    exact hchi1 q x
  have hZ : ∀ q : Cell,
      ∫ x, Complex.ofReal (F x i) * ((chi q x : ℂ) * v x) ∂volume =
        ∫ x, (chi q x : ℂ) * f x ∂volume := by
    intro q
    exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by
      simp only [hfdef]; ring)
  have hkey : ∀ n, Complex.mk
      (fluxRowLocalizedPairing (cells n) cellVolume
        (fun q ↦ (fluxRowFractionalCellPairing (chi q) (cellVolume q) F i v).re))
      (fluxRowLocalizedPairing (cells n) cellVolume
        (fun q ↦ (fluxRowFractionalCellPairing (chi q) (cellVolume q) F i v).im)) =
      ∫ x, ((∑ q ∈ cells n, chi q x : ℝ) : ℂ) * f x ∂volume := by
    intro n
    have hre : fluxRowLocalizedPairing (cells n) cellVolume
        (fun q ↦ (fluxRowFractionalCellPairing (chi q) (cellVolume q) F i v).re) =
        ∑ q ∈ cells n, (∫ x, (chi q x : ℂ) * f x ∂volume).re := by
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      show cellVolume q *
        (fluxRowFractionalCellPairing (chi q) (cellVolume q) F i v).re = _
      rw [re_fluxRowFractionalCellPairing (chi q) (cellVolume q) F i v, hZ q,
        ← mul_assoc, mul_inv_cancel₀ (hvol q), one_mul]
    have him : fluxRowLocalizedPairing (cells n) cellVolume
        (fun q ↦ (fluxRowFractionalCellPairing (chi q) (cellVolume q) F i v).im) =
        ∑ q ∈ cells n, (∫ x, (chi q x : ℂ) * f x ∂volume).im := by
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      show cellVolume q *
        (fluxRowFractionalCellPairing (chi q) (cellVolume q) F i v).im = _
      rw [im_fluxRowFractionalCellPairing (chi q) (cellVolume q) F i v, hZ q,
        ← mul_assoc, mul_inv_cancel₀ (hvol q), one_mul]
    have hsum : ∑ q ∈ cells n, ∫ x, (chi q x : ℂ) * f x ∂volume =
        ∫ x, ((∑ q ∈ cells n, chi q x : ℝ) : ℂ) * f x ∂volume := by
      rw [← integral_finset_sum _ fun q _ ↦ hintq q]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
      show ∑ q ∈ cells n, (chi q x : ℂ) * f x =
        ((∑ q ∈ cells n, chi q x : ℝ) : ℂ) * f x
      rw [Complex.ofReal_sum, Finset.sum_mul]
    rw [hre, him, ← Complex.re_sum, ← Complex.im_sum, hsum]
  refine Tendsto.congr (fun n ↦ (hkey n).symm) ?_
  exact fluxRowFractional_tendsto_integral_mul volume hint
    (fun n x ↦ ∑ q ∈ cells n, chi q x)
    (fun n ↦ Finset.measurable_sum _ fun q _ ↦ hchim q)
    (fun n x ↦ Finset.sum_nonneg fun q _ ↦ hchi0 q x) hsum1 hsumlim

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
