module

public import SubdiffusiveProcess.Paper.lfgc_single_main

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# The single-point tests have interval witnesses (main statement)
-/

open MeasureTheory Filter Topology SubdiffusiveProcess Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem aux_lfgc_single_theorem_single_bad_bound (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (T : ℕ) (offset : Fin T → ℤ)
    (shift : Fin T → SpatialCoordinates d) (hoff : ∀ i, -3 ≤ offset i ∧ offset i ≤ 0)
    (k : ℕ) (z : SpatialCoordinates d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Carrier : Set (BilateralField d)) (hCnull : (chaosSampleLaw M).toMeasure Carrierᶜ = 0)
    (hconv : ∀ omega ∈ Carrier, Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega)))
    (hcanon : ∀ omega ∈ Carrier, ∀ (j : ℕ) (y : SubdiffusiveProcess.CoarseGrainingVocab.Vec d),
      (aux_lfgc_layer_tail_canonEta 0 omega j : SubdiffusiveProcess.CoarseGrainingVocab.Vec d → ℝ) y = omega (j : ℤ) y)
    {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) (Hs : ℕ) (hHs : k ≤ Hs) (hd : 0 < d)
    (hc1 : R + 1 ≤ (2 * ε * d / 27 / _root_.SubdiffusiveProcess.Paper.aux_psf_sigma M) ^ 2)
    (hc2 : 16 * T * 57 ^ d * Real.exp (-(2 * ε * d / 27 / _root_.SubdiffusiveProcess.Paper.aux_psf_sigma M) ^ 2) ≤ 1) :
    (chaosSampleLaw M).toMeasure {omega | ¬ aux_lfgc_root_impl_allOscLe T offset shift (k : ℤ) z H
        (fun omega => infraredPartialSum omega (Hs - k)) ε omega} ≤
      ENNReal.ofReal (Real.exp (-(R * Hs)) / 8) := by
  set L := Hs - k
  have hsub : {omega | ¬ aux_lfgc_root_impl_allOscLe T offset shift (k : ℤ) z H
      (fun omega => infraredPartialSum omega L) ε omega} ⊆
      Carrierᶜ ∪ (⋃ (i : Fin T) (l : ℕ) (_ : L ≤ l)
        (y ∈ aux_lfgc_layer_osc_cells_cellCenters (z + ((3 : ℝ) ^ (-(k : ℤ))) • shift i)),
        aux_lfgc_single_cover1_cellEvent T offset (k : ℤ) ε i l y) := by
    intro omega homega
    by_cases hC : omega ∈ Carrier
    · right
      simp only [aux_lfgc_root_impl_allOscLe, Set.mem_ofPred_eq, not_forall] at homega
      obtain ⟨i, hi⟩ := homega
      have hi' : ¬ aux_lfgc_root_near_OscLe (fun y => H omega y - infraredPartialSum omega L y)
          (z + ((3 : ℝ) ^ (-(k : ℤ))) • shift i) ((3 : ℝ) ^ (-((k : ℤ) + offset i)))
          (by positivity) ε := fun h => hi h.symm
      have hr27 : ∀ i, (3 : ℝ) ^ (-((k : ℤ) + offset i)) ≤ 27 := by
        intro i
        have h1 : (3 : ℝ) ^ (-((k : ℤ) + offset i)) ≤ (3 : ℝ) ^ (3 : ℤ) :=
          zpow_le_zpow_right₀ (by norm_num) (by have := (hoff i).1; omega)
        have h2 : (3 : ℝ) ^ (3 : ℤ) = 27 := by norm_num
        rw [h2] at h1; exact h1
      obtain ⟨l, hl, y, hy, hev⟩ := aux_lfgc_single_cover1_tail_osc_to_cell hd T offset shift (k : ℤ) z hr27 H omega
        (hconv omega hC) (hcanon omega hC) L hε.le i hi'
      simp only [Set.mem_iUnion]
      exact ⟨i, l, hl, y, hy, hev⟩
    · exact Or.inl hC
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [hCnull, zero_add]
  refine (lfgc_obad_bound M offset shift k z (fun i => (hoff i).1) hε.le (by linarith) L
    hc1 hc2).trans (ENNReal.ofReal_le_ofReal ?_)
  have hcast : ((L + 1 + k : ℕ) : ℝ) = (Hs : ℝ) + 1 := by
    have : L + 1 + k = Hs + 1 := by omega
    rw [this]; push_cast; ring
  rw [hcast]
  exact lfgc_single_num2 hR (by positivity)

theorem aux_lfgc_single_theorem_single_chain_meas (hd : 2 ≤ d) [NeZero d] (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (sigma : ℝ) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (T : ℕ) (offset : Fin T → ℤ) (shift : Fin T → SpatialCoordinates d)
    (hoff : ∀ i, -3 ≤ offset i ∧ offset i ≤ 0) (m k : ℕ) (z : SpatialCoordinates d) (K : ℝ)
    (W₀ : ℕ) (hW₀ : 0 < W₀) (Yb : ℕ → BilateralField d → ℝ)
    (hYb : ∀ h : ℕ, 1 ≤ h → StronglyMeasurable[layerWindow C(SpatialCoordinates d, ℝ)
      (Set.Icc (-(k : ℤ) - (W₀ * (h + 1) : ℕ)) (-(k : ℤ) + (W₀ * (h + 1) : ℕ)))] (Yb h)) :
    ∀ ℓ ≤ m + k + 3, Measurable[aux_lfgc_family_cover_nodeWin d k (aux_lfgc_chain_cover_chainWin W₀ hW₀ ℓ)]
      (aux_lfgc_chain_prob_chainY Yb (aux_lfgc_root_impl_rootX I M sigma T offset shift (m + k) (k : ℤ) z K
        (fun omega => infraredPartialSum omega (W₀ * (m + k + 3 + 2) - k))) (m + k + 3) ℓ) := by
  intro ℓ hℓ
  by_cases hlt : ℓ < m + k + 3
  · have hY : aux_lfgc_chain_prob_chainY Yb (aux_lfgc_root_impl_rootX I M sigma T offset shift (m + k) (k : ℤ) z K
        (fun omega => infraredPartialSum omega (W₀ * (m + k + 3 + 2) - k))) (m + k + 3) ℓ =
        Yb (ℓ + 1) := by simp [aux_lfgc_chain_prob_chainY, hlt]
    rw [hY]
    refine ((hYb (ℓ + 1) (by omega)).measurable).mono ?_ le_rfl
    refine layerWindow_mono ?_
    intro j hj
    simp only [aux_lfgc_chain_cover_chainWin, PNat.mk_coe]
    have hW : (0 : ℤ) ≤ ((W₀ * (ℓ + 2) : ℕ) : ℤ) := by positivity
    have e : ((W₀ * (ℓ + 1 + 1) : ℕ) : ℤ) = ((W₀ * (ℓ + 2) : ℕ) : ℤ) := by ring_nf
    have h1 := hj.1
    have h2 := hj.2
    rw [e] at h1 h2
    exact ⟨by linarith, by linarith⟩
  · have hEq : ℓ = m + k + 3 := by omega
    subst hEq
    have hY : aux_lfgc_chain_prob_chainY Yb (aux_lfgc_root_impl_rootX I M sigma T offset shift (m + k) (k : ℤ) z K
        (fun omega => infraredPartialSum omega (W₀ * (m + k + 3 + 2) - k))) (m + k + 3)
        (m + k + 3) = aux_lfgc_root_impl_rootX I M sigma T offset shift (m + k) (k : ℤ) z K
        (fun omega => infraredPartialSum omega (W₀ * (m + k + 3 + 2) - k)) := by simp [aux_lfgc_chain_prob_chainY]
    rw [hY]
    have hHs : m + k + 3 + 2 ≤ W₀ * (m + k + 3 + 2) := Nat.le_mul_of_pos_left _ hW₀
    show Measurable[layerWindow C(SpatialCoordinates d, ℝ)
      (Set.Icc (-(k : ℤ) - 2 * ((W₀ * (m + k + 3 + 2) : ℕ) : ℤ))
        (-(k : ℤ) + ((W₀ * (m + k + 3 + 2) : ℕ) : ℤ)))] _
    have hH' : ((m + k + 3 + 2 : ℕ) : ℤ) ≤ ((W₀ * (m + k + 3 + 2) : ℕ) : ℤ) := by exact_mod_cast hHs
    have hsubc : (((W₀ * (m + k + 3 + 2) - k : ℕ)) : ℤ) = ((W₀ * (m + k + 3 + 2) : ℕ) : ℤ) - k := by
      rw [Nat.cast_sub (by omega)]
    refine lfgc_endpoint_meas hd I M sigma hsigma T offset shift (m + k) (k : ℤ) z K _ hoff
      (by positivity) (by push_cast; omega) _ _ ?_ ?_ ?_
    · generalize ((W₀ * (m + k + 3 + 2) : ℕ) : ℤ) = X at hH' ⊢
      push_cast at hH' ⊢; omega
    · rw [hsubc]; linarith
    · generalize ((W₀ * (m + k + 3 + 2) : ℕ) : ℤ) = X at hH' ⊢
      push_cast at hH' ⊢; omega

theorem lfgc_single_theorem (hd : 2 ≤ d) [NeZero d] (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Poincare : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I) (Extension : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (MeyersMorrey : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d) (Sobolev : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (D : _root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d) (Dbase : _root_.SubdiffusiveProcess.Paper.sum_errors_baseline_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp) (sigma : ℝ) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (eps : ℝ) (heps : eps ∈ Set.Ioo (0 : ℝ) 1) {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hθ₀8 : θ₀ ≤ 1 / 8)
    (T : ℕ) (offset : Fin T → ℤ) (shift : Fin T → SpatialCoordinates d)
    (hoff : ∀ i, -3 ≤ offset i ∧ offset i ≤ 0) {R : ℝ} (hR : 0 < R) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ delta0 →
      ∀ (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
            omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
      ∀ (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
          _root_.SubdiffusiveProcess.Paper.primitive_scores d M sigma eps (eta N omega)
            (fun m y => F N m y omega) (fun m y => Praw N m y omega)
            (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
            (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)) →
      ∀ (Carrier : Set (BilateralField d)), (chaosSampleLaw M).toMeasure Carrierᶜ = 0 →
        (∀ omega ∈ Carrier, Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega))) →
        (∀ omega ∈ Carrier, ∀ (j : ℕ) (y : SubdiffusiveProcess.CoarseGrainingVocab.Vec d),
          (aux_lfgc_layer_tail_canonEta 0 omega j : SubdiffusiveProcess.CoarseGrainingVocab.Vec d → ℝ) y = omega (j : ℤ) y) →
      ∀ (m k : ℕ) (z : SpatialCoordinates d),
        IsTailCover (chaosSampleLaw M).toMeasure (aux_lfgc_family_cover_nodeWin d k)
          (Carrier ∩ ({omega | ¬ aux_lfgc_root_stat_nearAll I M H sigma T offset shift (m + k) (k : ℤ) z θ₀ omega} ∪
            {omega | ¬ aux_lfgc_root_stat_nearAll I M 0 sigma T offset shift (m + k) (k : ℤ) z θ₀ omega}))
          (fun h => ENNReal.ofReal (Real.exp (-R * (h : ℝ)) / 2)) := by
  have hdpos : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
  -- oscillation tolerances
  obtain ⟨ε₁, hε₁, hε₁1, hs₁⟩ := lfgc_single_num (show 0 < 3 * θ₀ / 4 by positivity)
  obtain ⟨ε₂, hε₂, hε₂1, hs₂⟩ := lfgc_single_num (show 0 < θ₀ / 16 by positivity)
  obtain ⟨ε₃, hε₃, hε₃1, hs₃⟩ := lfgc_single_num (show 0 < θ₀ / 64 by positivity)
  have htol1 : aux_lfgc_near_tests_tolTransfer ε₁ (θ₀ / 4) ≤ θ₀ :=
    (aux_lfgc_root_impl_tolTransfer_le hε₁.le (by positivity) (by linarith)).trans (by linarith)
  have htol2 : aux_lfgc_near_tests_tolTransfer ε₂ (θ₀ / 8) < θ₀ / 4 :=
    (aux_lfgc_root_impl_tolTransfer_le hε₂.le (by positivity) (by linarith)).trans_lt (by linarith)
  have hslack3 : 2 / θ₀ * aux_lfgc_root_impl_tolSlack ε₃ ≤ 1 / 32 := by
    calc 2 / θ₀ * aux_lfgc_root_impl_tolSlack ε₃ ≤ 2 / θ₀ * (θ₀ / 64) :=
          mul_le_mul_of_nonneg_left hs₃ (by positivity)
      _ = 1 / 32 := by field_simp; ring
  -- lem_band and the coordinate tails
  obtain ⟨a, c, W₀, ha, hc, hW₀, hband⟩ := lfgc_root_band hd I Poincare Extension MeyersMorrey Sobolev D
    Dbase Cresp hCresp sigma hsigma eps heps hθ₀ T offset shift
  obtain ⟨c', hc', htail⟩ := lfgc_root_tail2 hd I Poincare Extension MeyersMorrey Sobolev D Cresp hCresp
    sigma hsigma
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set p : ℝ := max 1 (2 * R * W₀ / (a * Real.log 3)) with hpdef
  have hp1 : 1 ≤ p := le_max_left _ _
  have hp0 : 0 < p := by linarith
  have hpc : R * (W₀ : ℝ) ≤ a / 2 * p * Real.log 3 := by
    have h := le_max_right 1 (2 * R * W₀ / (a * Real.log 3))
    rw [← hpdef, div_le_iff₀ (by positivity)] at h
    nlinarith
  obtain ⟨δb, Cp, hδb, hCp, hbandp⟩ := hband p hp1
  obtain ⟨δt, C', hδt, hδt1, hC', htailp⟩ := htail p hp1
  -- constants for the thresholds
  set ρ : ℝ := (3 : ℝ) ^ (-a / 2) with hρdef
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set E : ℝ := Real.exp (-(2 * R * W₀)) / 8 with hEdef
  have hE : 0 < E := by positivity
  set τ : ℝ := (1 - ρ) / 32 * E ^ (1 / p) with hτdef
  have hτ : 0 < τ := by
    have : 0 < 1 - ρ := by linarith
    positivity
  obtain ⟨δK, hδK, hδKle⟩ := lfgc_single_main (C := Cp) hc hτ
  set card : ℝ := (Fintype.card (Fin T × aux_lfgc_root_stat_SelIdx d) : ℝ) with hcard
  set τ' : ℝ := (θ₀ / 64) ^ 2 * (E / (card + 1)) ^ (1 / p) with hτ'def
  have hτ' : 0 < τ' := by positivity
  obtain ⟨δB, hδB, hδBle⟩ := lfgc_single_main (C := C') hc' hτ'
  set Λ : ℝ := max (R + 1) (Real.log (16 * T * 57 ^ d)) + 1 with hΛdef
  have hΛ : 0 < Λ := by
    have := le_max_left (R + 1) (Real.log (16 * T * 57 ^ d)); linarith
  set δε : ℝ := min (min (2 * ε₁ * d / (27 * (1 + d) * Real.sqrt Λ))
    (2 * ε₂ * d / (27 * (1 + d) * Real.sqrt Λ))) (2 * ε₃ * d / (27 * (1 + d) * Real.sqrt Λ))
  have hδε : 0 < δε := by
    have hs := Real.sqrt_pos.mpr hΛ
    refine lt_min (lt_min ?_ ?_) ?_ <;> positivity
  refine ⟨min (min (min δb δt) (min δK δB)) (min δε 1), ?_, ?_⟩
  · exact lt_min (lt_min (lt_min hδb hδt) (lt_min hδK hδB)) (lt_min hδε one_pos)
  intro M hM Rm hRm Sreg It H hH eta hEta F Praw Rraw Draw Zs rawGood hPrim Carrier hCnull hconv
    hcanon m k z
  have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hMb : M.delta ≤ δb :=
    hM.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hMt : M.delta ≤ δt :=
    hM.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hMK : M.delta ≤ δK :=
    hM.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hMB : M.delta ≤ δB :=
    hM.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hMε : M.delta ≤ δε := hM.trans ((min_le_right _ _).trans (min_le_left _ _))
  -- the cell constants
  have hσ : _root_.SubdiffusiveProcess.Paper.aux_psf_sigma M = (1 + d) * M.delta := rfl
  have hcell : ∀ ε : ℝ, 0 < ε → M.delta ≤ 2 * ε * d / (27 * (1 + d) * Real.sqrt Λ) →
      R + 1 ≤ (2 * ε * d / 27 / _root_.SubdiffusiveProcess.Paper.aux_psf_sigma M) ^ 2 ∧
      16 * T * 57 ^ d * Real.exp (-(2 * ε * d / 27 / _root_.SubdiffusiveProcess.Paper.aux_psf_sigma M) ^ 2) ≤ 1 := by
    intro ε hε hle
    have hC := aux_lfgc_single_num2_cell_const_ge hdpos hε hΛ hδpos hle
    rw [← hσ] at hC
    refine ⟨le_trans (by linarith [le_max_left (R + 1) (Real.log (16 * T * 57 ^ d))]) hC, ?_⟩
    exact aux_lfgc_single_num2_exp_neg_le_inv_of_log_le (by positivity)
      (le_trans (by linarith [le_max_right (R + 1) (Real.log (16 * T * 57 ^ d))]) hC)
  have hc1 := hcell ε₁ hε₁ (hMε.trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hc2 := hcell ε₂ hε₂ (hMε.trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hc3 := hcell ε₃ hε₃ (hMε.trans (min_le_right _ _))
  -- the band approximants
  set N := m + k with hNdef
  have hkN : (k : ℤ) ≤ (N : ℤ) := by omega
  have hoffN : ∀ i, (k : ℤ) + offset i ≤ (N : ℤ) := fun i => by have := (hoff i).2; omega
  set P := (chaosSampleLaw M).toMeasure
  set X := aux_lfgc_root_impl_rootX I M sigma T offset shift N (k : ℤ) z (2 / θ₀) H with hXdef
  have hex : ∀ h : ℕ, ∃ Y : BilateralField d → ℝ, StronglyMeasurable Y ∧ (1 ≤ h →
      StronglyMeasurable[layerWindow C(SpatialCoordinates d, ℝ)
        (Set.Icc (-(k : ℤ) - (W₀ * (h + 1) : ℕ)) (-(k : ℤ) + (W₀ * (h + 1) : ℕ)))] Y ∧
      eLpNorm (fun omega => X omega - Y omega) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (Cp * M.delta ^ c * (3 : ℝ) ^ (-(a * (h : ℝ))))) := by
    intro h
    by_cases hh : 1 ≤ h
    · obtain ⟨Y, h1, -, h3⟩ := hbandp M hMb Rm hRm Sreg It H hH eta hEta F Praw Rraw Draw Zs
        rawGood hPrim N (k : ℤ) z hkN hoffN h hh
      exact ⟨Y, h1.mono (layerWindow_le_pi _), fun _ => ⟨h1, h3⟩⟩
    · exact ⟨0, stronglyMeasurable_const, fun h' => absurd h' hh⟩
  choose Yb hYbm hYb using hex
  set ℓs := m + k + 3 with hℓsdef
  set Hs := W₀ * (ℓs + 2) with hHsdef
  have hHs : ℓs + 2 ≤ Hs := Nat.le_mul_of_pos_left _ hW₀
  set L := Hs - k with hLdef
  set HL : BilateralField d → C(SpatialCoordinates d, ℝ) := fun omega => infraredPartialSum omega L
  set Zend := aux_lfgc_root_impl_rootX I M sigma T offset shift N (k : ℤ) z (2 / θ₀) HL with hZdef
  set Obad := {omega | ¬ aux_lfgc_root_impl_allOscLe T offset shift (k : ℤ) z H HL ε₃ omega}
  have hρ0 : 0 ≤ ρ := by positivity
  -- chain probabilities
  have hXm : AEStronglyMeasurable X P :=
    (aux_lfgc_endpoint_meas_rootX_measurable hd I M H hH.1 sigma hsigma T offset shift N (k : ℤ) z (2 / θ₀)).aestronglyMeasurable
  have hCδ : 0 ≤ Cp * M.delta ^ c := mul_nonneg hCp.le (Real.rpow_nonneg hδpos.le c)
  have herr : ∀ h : ℕ, 1 ≤ h → eLpNorm (fun omega => X omega - Yb h omega) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal ((Cp * M.delta ^ c) * (3 : ℝ) ^ (-(a * (h : ℝ)))) := fun h hh => (hYb h hh).2
  have hZ : ∀ omega ∉ Obad, |Zend omega - X omega| ≤ 1 / 32 := by
    intro omega homega
    simp only [Obad, Set.mem_ofPred_eq, not_not] at homega
    exact lfgc_single_parts I M sigma hsigma T offset shift N (k : ℤ) z hθ₀ (by linarith) hε₃.le hslack3
      H HL omega homega
  have hKp : (32 * (Cp * M.delta ^ c) / (1 - (3 : ℝ) ^ (-a / 2))) ^ p ≤
      Real.exp (-(2 * R * W₀)) / 8 :=
    aux_lfgc_single_main_Kp_of_small hρ1 hE hp0 rfl hCδ (hδKle M.delta hδpos hMK)
  have hbase : P {omega | 1 / 32 < X omega} ≤ ENNReal.ofReal (Real.exp (-(2 * R * W₀)) / 8) := by
    have hq := fun q s hs hs1 => htailp M hMt Rm hRm Sreg It H hH T offset shift N (k : ℤ) z hoffN q s
      hs hs1
    have hs1 : (1 / 32 : ℝ) * θ₀ / 2 ≤ 1 := by linarith
    refine (aux_lfgc_single_parts_rootX_base_tail P I M sigma T offset shift N (k : ℤ) z hθ₀ (by norm_num)
      hs1 H hq).trans ?_
    have hB := hδBle M.delta hδpos hMB
    have hs : (1 / 32 : ℝ) * θ₀ / 2 = θ₀ / 64 := by ring
    rw [hs, aux_lfgc_chain_bound_ennreal_ratio_rpow (by positivity) (by positivity) hp0.le]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (aux_lfgc_single_main_base_of_small (Nat.cast_nonneg _) hp0 hE (by positivity)
      (by positivity) rfl hB)
  have hbad : P Obad ≤ ENNReal.ofReal (Real.exp (-(R * W₀ * ((ℓs : ℝ) + 2))) / 8) := by
    have h := aux_lfgc_single_theorem_single_bad_bound M T offset shift hoff k z H Carrier hCnull hconv hcanon hε₃ hR Hs
      (by omega) hdpos hc3.1 hc3.2
    have e : R * W₀ * ((ℓs : ℝ) + 2) = R * Hs := by simp only [Hs]; push_cast; ring
    rw [e]; exact h
  have hprob := lfgc_chain_bound P X Zend hXm Yb (fun h => (hYbm h).aestronglyMeasurable) ha hp1 hCδ
    herr ℓs (by omega) Obad hZ hpc hKp hbase hbad
  -- assemble
  refine lfgc_single_assemble hd I M sigma hsigma T offset shift hoff m k z hθ₀ hε₁.le hε₂.le htol1 htol2
    H Carrier hconv hcanon W₀ hW₀ (aux_lfgc_chain_prob_chainY Yb Zend ℓs) (aux_lfgc_chain_num_chainTheta ρ ℓs)
    (lfgc_chain_num hρ0 hρ1 ℓs) (by simp only [aux_lfgc_chain_prob_chainY, hℓsdef, lt_irrefl, ite_false]; rfl) ?_ ?_
    (le_trans (by linarith) hc1.1) hc1.2 (le_trans (by linarith) hc2.1) hc2.2
  · exact aux_lfgc_single_theorem_single_chain_meas hd I M sigma hsigma T offset shift hoff m k z (2 / θ₀) W₀ hW₀ Yb
      (fun h hh => (hYb h hh).1)
  · intro ℓ hℓ
    refine (hprob ℓ hℓ).trans (le_of_eq ?_)
    have e : -(R * (W₀ : ℝ) * ((ℓ : ℝ) + 2)) = -R * ((aux_lfgc_chain_cover_chainWin W₀ hW₀ ℓ : ℕ) : ℝ) := by
      simp only [aux_lfgc_chain_cover_chainWin, PNat.mk_coe]; push_cast; ring
    rw [e]

end SubdiffusiveProcess.Paper
