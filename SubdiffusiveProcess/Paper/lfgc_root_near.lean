import SubdiffusiveProcess.Paper.lfgc_root_stat

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# Nearness of all root charts: norm form and transfer between infrared fields

`aux_lfgc_root_stat_nearAll ... θ ω` is equivalent to `‖aux_lfgc_root_stat_selOf (aux_lfgc_root_stat_bandCoords ...)‖ ≤ θ`, and it transfers from an
infrared field `H` to `H'` when `H' - H` oscillates by at most `ε` on every root cube.
Deterministic.
-/

open MeasureTheory Homogenization Homogenization.Book.Ch02 SubdiffusiveProcess
open scoped ENNReal

namespace Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem aux_lfgc_near_tests_NearChart.mono {σ : ℝ} {F : TriadicCoeffFamily d} {ref θ θ' : ℝ}
    (h : aux_lfgc_near_tests_NearChart σ F ref θ) (hθ : θ ≤ θ') : aux_lfgc_near_tests_NearChart σ F ref θ' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1.trans hθ, h2.trans hθ, fun i j => (h3 i j).trans hθ, h4.trans hθ⟩

theorem aux_lfgc_root_near_nearAll_iff_norm [NeZero d] (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (sigma : ℝ)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) (T : ℕ) (offset : Fin T → ℤ)
    (shift : Fin T → SpatialCoordinates d) (N : ℕ) (n : ℤ) (z : SpatialCoordinates d)
    {θ : ℝ} (hθ : 0 ≤ θ) (omega : BilateralField d) :
    aux_lfgc_root_stat_nearAll I M H sigma T offset shift N n z θ omega ↔
      ‖aux_lfgc_root_stat_selOf (aux_lfgc_root_stat_bandCoords I M H sigma sigma T offset shift N n z omega)‖ ≤ θ := by
  rw [pi_norm_le_iff_of_nonneg hθ]
  constructor
  · intro h p
    obtain ⟨i, j⟩ := p
    obtain ⟨e1, e2, e3, e4⟩ := lfgc_root_stat I M H sigma hsigma T offset shift N n z omega i
    obtain ⟨h1, h2, h3, h4⟩ := h i
    rw [Real.norm_eq_abs]
    rcases j with j | ⟨a, b⟩
    · fin_cases j
      · simp only [Fin.zero_eta] at e1 ⊢; rw [e1]; exact h1
      · simp only [Fin.mk_one] at e2 ⊢; rw [e2]; exact h2
      · have : ((⟨2, by norm_num⟩ : Fin 3)) = 2 := rfl
        rw [this, e3]
        have h0 : 0 ≤ Paper.aux_lem_band_U2_errF sigma
            (aux_lfgc_root_stat_rootChart I M H omega N (n + offset i) (z + ((3 : ℝ) ^ (-n)) • shift i))
            (Paper.aux_lem_band_U2_reference M H N (n + offset i)
              (z + ((3 : ℝ) ^ (-n)) • shift i) omega) := ENNReal.toReal_nonneg
        rw [abs_of_nonneg h0]; exact h4
    · rw [e4 a b]; exact h3 a b
  · intro h i
    obtain ⟨e1, e2, e3, e4⟩ := lfgc_root_stat I M H sigma hsigma T offset shift N n z omega i
    have g1 := h (i, Sum.inl 0)
    have g2 := h (i, Sum.inl 1)
    have g3 := h (i, Sum.inl 2)
    rw [Real.norm_eq_abs] at g1 g2 g3
    rw [e1] at g1; rw [e2] at g2; rw [e3] at g3
    refine ⟨g1, g2, fun a b => ?_, (le_abs_self _).trans g3⟩
    have g4 := h (i, Sum.inr (a, b))
    rw [Real.norm_eq_abs, e4 a b] at g4
    exact g4

theorem aux_lfgc_root_near_reference_ratio (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H H' : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ) (m : ℤ)
    (w : SpatialCoordinates d) (omega : BilateralField d) :
    Paper.aux_lem_band_U2_reference M H' N m w omega =
      Real.exp (H' omega w - H omega w) * Paper.aux_lem_band_U2_reference M H N m w omega := by
  unfold Paper.aux_lem_band_U2_reference
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  ring

/-- Oscillation of a function on a root cube relative to its centre. -/
def aux_lfgc_root_near_OscLe (f : SpatialCoordinates d → ℝ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (ε : ℝ) : Prop :=
  ∀ y ∈ (centeredCube w r hr : Set (SpatialCoordinates d)), |f y - f w| ≤ ε

/-- Transfer of `aux_lfgc_root_stat_nearAll` from `H` to `H'`. -/
theorem lfgc_root_near [NeZero d] (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H H' : BilateralField d → C(SpatialCoordinates d, ℝ)) (sigma : ℝ)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) (T : ℕ) (offset : Fin T → ℤ)
    (shift : Fin T → SpatialCoordinates d) (N : ℕ) (n : ℤ) (z : SpatialCoordinates d)
    {θ ε : ℝ} (hθ : 0 ≤ θ) (hε : 0 ≤ ε) (omega : BilateralField d)
    (hosc : ∀ i : Fin T, aux_lfgc_root_near_OscLe (fun y => H' omega y - H omega y)
      (z + ((3 : ℝ) ^ (-n)) • shift i) ((3 : ℝ) ^ (-(n + offset i))) (by positivity) ε)
    (h : aux_lfgc_root_stat_nearAll I M H sigma T offset shift N n z θ omega) :
    aux_lfgc_root_stat_nearAll I M H' sigma T offset shift N n z (aux_lfgc_near_tests_tolTransfer ε θ) omega := by
  intro i
  set m := n + offset i
  set w := z + ((3 : ℝ) ^ (-n)) • shift i
  have hr : (0 : ℝ) < (3 : ℝ) ^ (-m) := by positivity
  have hclose := lfgc_cutoff_charts I M H H' omega N w hr ε (hosc i)
  have hκ : 0 < Real.exp (H' omega w - H omega w) := Real.exp_pos _
  have href := Paper.aux_lem_band_U2_reference_pos M H N m w omega
  have hlampos : ∀ G : BilateralField d → C(SpatialCoordinates d, ℝ),
      0 < Paper.aux_lem_band_U2_lamF sigma (aux_lfgc_root_stat_rootChart I M G omega N m w) := by
    intro G
    have := I.lam_pos w ((3 : ℝ) ^ (-m)) hr (Lane4.cutoffPositiveCoefficient M G omega N w hr) w
      ((3 : ℝ) ^ (-m)) sigma 2
    rwa [Paper.aux_lem_band_U2_lam_eq I w _ hr _ sigma hsigma] at this
  have hLampos : ∀ G : BilateralField d → C(SpatialCoordinates d, ℝ),
      0 < Paper.aux_lem_band_U2_LamF sigma (aux_lfgc_root_stat_rootChart I M G omega N m w) := by
    intro G
    have := I.Lam_pos w ((3 : ℝ) ^ (-m)) hr (Lane4.cutoffPositiveCoefficient M G omega N w hr) w
      ((3 : ℝ) ^ (-m)) sigma 2
    rwa [Paper.aux_lem_band_U2_Lam_eq I w _ hr _ sigma hsigma] at this
  have hfin : ∀ (G : BilateralField d → C(SpatialCoordinates d, ℝ)) (a0 : ℝ), 0 < a0 →
      SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite (originCube d 0) 0 sigma
        MultiscaleExponent.infinity 2 (aux_lfgc_root_stat_rootChart I M G omega N m w) a0 < ⊤ := by
    intro G a0 ha0
    have := I.err_finite w ((3 : ℝ) ^ (-m)) hr (Lane4.cutoffPositiveCoefficient M G omega N w hr) w
      ((3 : ℝ) ^ (-m)) hr subset_rfl sigma hsigma 2 (by norm_num) a0 ha0
    simp only [ENNReal.ofNat_ne_top, if_false, ENNReal.toReal_ofNat] at this
    exact this
  have hn := aux_lfgc_near_tests_NearChart.transfer hκ hε hclose sigma hsigma.1 _ href (hlampos H) (hlampos H')
    (hLampos H) (hLampos H') (hfin H _ href) (hfin H' _ (mul_pos hκ href)) hθ (h i)
  rw [← aux_lfgc_root_near_reference_ratio M H H' N m w omega] at hn
  exact hn

end Paper
