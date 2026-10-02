import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowMomentShellAmplitude




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- An `ENNReal` observable with a finite positive paper `L^p` norm is finite
almost everywhere. -/
theorem ae_ne_top_of_paperENNRealLpNorm_ne_top
    (mu : Measure Omega) {p : ℝ} (hp : 0 < p)
    {X : Omega → ℝ≥0∞} (hX : Measurable X)
    (hnorm : paperENNRealLpNorm mu p X ≠ ∞) :
    ∀ᵐ omega ∂mu, X omega ≠ ∞ := by
  have heLp : eLpNorm X (ENNReal.ofReal p) mu < ∞ := by
    rw [← paperENNRealLpNorm_eq_eLpNorm mu hp X]
    exact lt_top_iff_ne_top.mpr hnorm
  have hlintegral := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top heLp
  have hpow : ∀ᵐ omega ∂mu, X omega ^ p < ∞ := by
    apply ae_lt_top' (hX.pow_const p).aemeasurable
    simpa [ENNReal.toReal_ofReal hp.le, enorm_eq_self] using hlintegral.ne
  filter_upwards [hpow] with omega homega
  exact ((ENNReal.rpow_lt_top_iff_of_pos hp).mp homega).ne

/-- The level-`j` shell normalized by the geometric factor `D ^ j`. -/
def fluxRowMomentGeometricallyNormalizedShell
    (D : ℝ) (shell : ℕ → Omega → ℝ) (j : ℕ) (omega : Omega) : ℝ≥0∞ :=
  ENNReal.ofReal (D ^ (-(j : ℤ)) * shell j omega)

/-- The real random amplitude obtained from the supremum of geometrically
normalized shells.  Its value is zero on the exceptional set where that
supremum is infinite. -/
def fluxRowMomentGeometricRealAmplitude
    (D : ℝ) (shell : ℕ → Omega → ℝ) (omega : Omega) : ℝ :=
  (fluxRowMomentShellAmplitude
    (fluxRowMomentGeometricallyNormalizedShell D shell) omega).toReal

/-- Measurability of every normalized shell. -/
theorem measurable_fluxRowMomentGeometricallyNormalizedShell
    {D : ℝ} {shell : ℕ → Omega → ℝ}
    (hshell : ∀ j, Measurable (shell j)) (j : ℕ) :
    Measurable (fluxRowMomentGeometricallyNormalizedShell D shell j) := by
  exact ENNReal.measurable_ofReal.comp
    (measurable_const.mul (hshell j))

/-- The real geometric amplitude is measurable. -/
theorem measurable_fluxRowMomentGeometricRealAmplitude
    {D : ℝ} {shell : ℕ → Omega → ℝ}
    (hshell : ∀ j, Measurable (shell j)) :
    Measurable (fluxRowMomentGeometricRealAmplitude D shell) := by
  exact ENNReal.measurable_toReal.comp
    (measurable_fluxRowMomentShellAmplitude fun j ↦
      measurable_fluxRowMomentGeometricallyNormalizedShell hshell j)

/-- For a nonnegative real observable, the paper's `ENNReal` moment carrier
is exactly its ordinary `eLpNorm`. -/
theorem paperENNRealLpNorm_ofReal_eq_eLpNorm_of_nonnegative
    (mu : Measure Omega) {p : ℝ} (hp : 0 < p)
    {X : Omega → ℝ} (hX0 : ∀ omega, 0 ≤ X omega) :
    paperENNRealLpNorm mu p (fun omega ↦ ENNReal.ofReal (X omega)) =
      eLpNorm X (ENNReal.ofReal p) mu := by
  unfold paperENNRealLpNorm
  rw [eLpNorm_eq_lintegral_rpow_enorm
    (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top]
  rw [ENNReal.toReal_ofReal hp.le, one_div]
  congr 2
  funext omega
  congr 1
  rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_of_nonneg (hX0 omega)]

omit [MeasurableSpace Omega] in
/-- Pointwise form of the normalization comparison.  Unlike the older
global helper, this asks for finiteness only at the sample being estimated. -/
theorem shell_le_geometricRealAmplitude_mul_pow_of_ne_top
    {shell : ℕ → Omega → ℝ} (hshell : ∀ j omega, 0 ≤ shell j omega)
    {D : ℝ} (hD : 0 < D) {omega : Omega}
    (hfinite : fluxRowMomentShellAmplitude
      (fluxRowMomentGeometricallyNormalizedShell D shell) omega ≠ ∞)
    (j : ℕ) :
    shell j omega ≤
      fluxRowMomentGeometricRealAmplitude D shell omega * D ^ j := by
  have hDj : 0 < D ^ (j : ℤ) := zpow_pos hD _
  have hnorm0 : 0 ≤ D ^ (-(j : ℤ)) * shell j omega :=
    mul_nonneg (zpow_nonneg hD.le _) (hshell j omega)
  have hle := le_fluxRowMomentShellAmplitude
    (fluxRowMomentGeometricallyNormalizedShell D shell) j omega
  have hreal := ENNReal.toReal_mono hfinite hle
  rw [fluxRowMomentGeometricallyNormalizedShell,
    ENNReal.toReal_ofReal hnorm0] at hreal
  have hcancel : D ^ (-(j : ℤ)) * D ^ (j : ℤ) = 1 := by
    rw [← zpow_add₀ hD.ne', neg_add_cancel, zpow_zero]
  calc
    shell j omega =
        (D ^ (-(j : ℤ)) * D ^ (j : ℤ)) * shell j omega := by
      rw [hcancel, one_mul]
    _ = (D ^ (-(j : ℤ)) * shell j omega) * D ^ (j : ℤ) := by ring
    _ ≤ (fluxRowMomentShellAmplitude
          (fluxRowMomentGeometricallyNormalizedShell D shell) omega).toReal *
        D ^ (j : ℤ) :=
      mul_le_mul_of_nonneg_right hreal hDj.le
    _ = fluxRowMomentGeometricRealAmplitude D shell omega * D ^ j := by
      norm_num [fluxRowMomentGeometricRealAmplitude]

/-- A summable family of normalized level moments produces a measurable
conull event and a measurable real amplitude with geometric growth.  The last
clause retains the sharp countable-Minkowski bound on that amplitude.

This is deliberately source-independent: a Euclidean counting argument only
has to prove finiteness of the displayed sum. -/
theorem exists_conull_geometric_shell_amplitude_of_summable_normalized_moments
    (mu : Measure Omega) {p : ℝ} (hp : 1 ≤ p)
    {shell : ℕ → Omega → ℝ}
    (hshell0 : ∀ j omega, 0 ≤ shell j omega)
    (hshell : ∀ j, Measurable (shell j))
    {D : ℝ} (hD : 1 < D)
    (hsum : (∑' j, paperENNRealLpNorm mu p
      (fluxRowMomentGeometricallyNormalizedShell D shell j)) ≠ ∞) :
    ∃ G : Set Omega,
      MeasurableSet G ∧
      (∀ᵐ omega ∂mu, omega ∈ G) ∧
      Measurable (fluxRowMomentGeometricRealAmplitude D shell) ∧
      (∀ omega ∈ G, ∀ j,
        shell j omega ≤
          fluxRowMomentGeometricRealAmplitude D shell omega * D ^ j) ∧
      paperENNRealLpNorm mu p (fun omega ↦
          ENNReal.ofReal (fluxRowMomentGeometricRealAmplitude D shell omega)) ≤
        ∑' j, paperENNRealLpNorm mu p
          (fluxRowMomentGeometricallyNormalizedShell D shell j) := by
  let normalizedShell : ℕ → Omega → ℝ≥0∞ :=
    fluxRowMomentGeometricallyNormalizedShell D shell
  let amplitude : Omega → ℝ≥0∞ :=
    fluxRowMomentShellAmplitude normalizedShell
  let G : Set Omega := {omega | amplitude omega < ∞}
  have hnormalized : ∀ j, Measurable (normalizedShell j) := fun j ↦
    measurable_fluxRowMomentGeometricallyNormalizedShell hshell j
  have hamplitude : Measurable amplitude :=
    measurable_fluxRowMomentShellAmplitude hnormalized
  have hnorm : paperENNRealLpNorm mu p amplitude ≤
      ∑' j, paperENNRealLpNorm mu p (normalizedShell j) :=
    paperENNRealLpNorm_fluxRowMomentShellAmplitude_le_tsum
      mu hp normalizedShell hnormalized
  have hnormTop : paperENNRealLpNorm mu p amplitude ≠ ∞ :=
    ne_top_of_le_ne_top hsum hnorm
  have hGae : ∀ᵐ omega ∂mu, omega ∈ G := by
    filter_upwards [ae_ne_top_of_paperENNRealLpNorm_ne_top mu
      (zero_lt_one.trans_le hp) hamplitude hnormTop] with omega homega
    exact lt_top_iff_ne_top.mpr homega
  have hGmeas : MeasurableSet G := by
    exact measurableSet_lt hamplitude measurable_const
  refine ⟨G, hGmeas, hGae,
    measurable_fluxRowMomentGeometricRealAmplitude hshell, ?_, ?_⟩
  · intro omega homega j
    apply shell_le_geometricRealAmplitude_mul_pow_of_ne_top hshell0
      (zero_lt_one.trans hD)
    exact (lt_top_iff_ne_top.mp homega)
  · have hpoint : ∀ omega,
        ENNReal.ofReal (fluxRowMomentGeometricRealAmplitude D shell omega) ≤
          amplitude omega := by
      intro omega
      simpa [fluxRowMomentGeometricRealAmplitude, amplitude, normalizedShell]
        using ENNReal.ofReal_toReal_le
    exact (paperENNRealLpNorm_mono_ae mu (zero_le_one.trans hp)
      (Filter.Eventually.of_forall hpoint)).trans hnorm

/-- Practical bounded form of
`exists_conull_geometric_shell_amplitude_of_summable_normalized_moments`.
The caller may supply any summable deterministic majorant for the normalized
per-level moments; in the Euclidean application it is a polynomial in `j`
times a geometric factor smaller than one. -/
theorem exists_conull_geometric_shell_amplitude_of_level_moment_bound
    (mu : Measure Omega) {p : ℝ} (hp : 1 ≤ p)
    {shell : ℕ → Omega → ℝ}
    (hshell0 : ∀ j omega, 0 ≤ shell j omega)
    (hshell : ∀ j, Measurable (shell j))
    {D : ℝ} (hD : 1 < D) (bound : ℕ → ℝ≥0∞)
    (hboundSum : (∑' j, bound j) ≠ ∞)
    (hbound : ∀ j, paperENNRealLpNorm mu p
      (fluxRowMomentGeometricallyNormalizedShell D shell j) ≤ bound j) :
    ∃ G : Set Omega,
      MeasurableSet G ∧
      (∀ᵐ omega ∂mu, omega ∈ G) ∧
      Measurable (fluxRowMomentGeometricRealAmplitude D shell) ∧
      (∀ omega ∈ G, ∀ j,
        shell j omega ≤
          fluxRowMomentGeometricRealAmplitude D shell omega * D ^ j) ∧
      paperENNRealLpNorm mu p (fun omega ↦
          ENNReal.ofReal (fluxRowMomentGeometricRealAmplitude D shell omega)) ≤
        ∑' j, bound j := by
  have hsumLe : (∑' j, paperENNRealLpNorm mu p
      (fluxRowMomentGeometricallyNormalizedShell D shell j)) ≤
      ∑' j, bound j := ENNReal.tsum_le_tsum hbound
  have hsum : (∑' j, paperENNRealLpNorm mu p
      (fluxRowMomentGeometricallyNormalizedShell D shell j)) ≠ ∞ :=
    ne_top_of_le_ne_top hboundSum hsumLe
  obtain ⟨G, hGmeas, hGae, hamplitude, hgrowth, hmoment⟩ :=
    exists_conull_geometric_shell_amplitude_of_summable_normalized_moments
      mu hp hshell0 hshell hD hsum
  exact ⟨G, hGmeas, hGae, hamplitude, hgrowth, hmoment.trans hsumLe⟩

/-- The same summable normalized level estimate places the resulting real
geometric amplitude in the requested `L^p` space. -/
theorem memLp_fluxRowMomentGeometricRealAmplitude_of_level_moment_bound
    (mu : Measure Omega) {p : ℝ} (hp : 1 ≤ p)
    {shell : ℕ → Omega → ℝ} (hshell : ∀ j, Measurable (shell j))
    {D : ℝ} (bound : ℕ → ℝ≥0∞)
    (hboundSum : (∑' j, bound j) ≠ ∞)
    (hbound : ∀ j, paperENNRealLpNorm mu p
      (fluxRowMomentGeometricallyNormalizedShell D shell j) ≤ bound j) :
    MemLp (fluxRowMomentGeometricRealAmplitude D shell)
      (ENNReal.ofReal p) mu := by
  let normalizedShell : ℕ → Omega → ℝ≥0∞ :=
    fluxRowMomentGeometricallyNormalizedShell D shell
  let amplitude : Omega → ℝ≥0∞ :=
    fluxRowMomentShellAmplitude normalizedShell
  have hnormalized : ∀ j, Measurable (normalizedShell j) := fun j ↦
    measurable_fluxRowMomentGeometricallyNormalizedShell hshell j
  have hnorm : paperENNRealLpNorm mu p amplitude ≤ ∑' j, bound j :=
    (paperENNRealLpNorm_fluxRowMomentShellAmplitude_le_tsum
      mu hp normalizedShell hnormalized).trans (ENNReal.tsum_le_tsum hbound)
  have hrealNorm : paperENNRealLpNorm mu p (fun omega ↦
      ENNReal.ofReal (fluxRowMomentGeometricRealAmplitude D shell omega)) ≤
      ∑' j, bound j := by
    refine (paperENNRealLpNorm_mono_ae mu (zero_le_one.trans hp) ?_).trans hnorm
    refine Filter.Eventually.of_forall fun omega ↦ ?_
    simpa [fluxRowMomentGeometricRealAmplitude, amplitude, normalizedShell]
      using ENNReal.ofReal_toReal_le
  refine ⟨(measurable_fluxRowMomentGeometricRealAmplitude hshell).aestronglyMeasurable,
    ?_⟩
  rw [← paperENNRealLpNorm_ofReal_eq_eLpNorm_of_nonnegative mu
    (X := fluxRowMomentGeometricRealAmplitude D shell)
    (zero_lt_one.trans_le hp) (fun _ ↦ ENNReal.toReal_nonneg)]
  exact hrealNorm.trans_lt (lt_top_iff_ne_top.mpr hboundSum)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
