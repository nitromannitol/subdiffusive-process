module

public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.Paper.lem_19_limit_membership_ae_subsequence
public import SubdiffusiveProcess.Paper.lem_19_limit_membership_fractional_fatou
public import SubdiffusiveProcess.Paper.lem_19_limit_membership_l2_term

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_lem_19_limit_membership_fatou
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r)
    (threeQuarters : Set.Ioo (0 : ℝ) 1)
    (w : ℕ → CubeFractionalL2 (k := 1) hd z r hr threeQuarters)
    (vlim : DomainL2 (centeredCube z r hr))
    (sigma : ℕ → ℕ)
    (hae : ∀ᵐ x ∂volume.restrict
        (centeredCube z r hr : Set (SpatialCoordinates d)),
      Tendsto (fun j => (w (sigma j)).val 0 x) atTop
        (𝓝 (vlim x))) :
    cubeFractionalL2Seminorm hd z r hr threeQuarters
        (fun _ : Fin 1 => vlim) ≤
      liminf (fun j =>
        cubeFractionalL2Seminorm hd z r hr threeQuarters (w (sigma j)).val)
        atTop := by
  classical
  let U : Set (SpatialCoordinates d) := centeredCube z r hr
  let μ : Measure (SpatialCoordinates d) := volume.restrict U
  let F : ℕ → (SpatialCoordinates d × SpatialCoordinates d) → ℝ≥0∞ := fun j q =>
    ENNReal.ofReal (((w (sigma j)).val 0 q.1 - (w (sigma j)).val 0 q.2) ^ 2) /
      (ENNReal.ofReal (Real.sqrt (∑ k : Fin d, (q.1 k - q.2 k) ^ 2))) ^
        ((d : ℝ) + 2 * (threeQuarters : ℝ))
  let F₀ : (SpatialCoordinates d × SpatialCoordinates d) → ℝ≥0∞ := fun q =>
    ENNReal.ofReal ((vlim q.1 - vlim q.2) ^ 2) /
      (ENNReal.ofReal (Real.sqrt (∑ k : Fin d, (q.1 k - q.2 k) ^ 2))) ^
        ((d : ℝ) + 2 * (threeQuarters : ℝ))
  have hw (j : ℕ) : AEStronglyMeasurable
      (fun x : SpatialCoordinates d => (w (sigma j)).val 0 x) μ := by
    simpa only [μ] using Lp.aestronglyMeasurable ((w (sigma j)).val 0)
  have hv : AEStronglyMeasurable
      (fun x : SpatialCoordinates d => vlim x) μ := by
    simpa only [μ] using Lp.aestronglyMeasurable vlim
  have hden : Measurable
      (fun q : SpatialCoordinates d × SpatialCoordinates d =>
        (ENNReal.ofReal (Real.sqrt (∑ k : Fin d, (q.1 k - q.2 k) ^ 2))) ^
          ((d : ℝ) + 2 * (threeQuarters : ℝ))) := by
    apply Measurable.pow
    · apply Measurable.ennreal_ofReal
      apply Measurable.sqrt
      exact Finset.measurable_sum Finset.univ fun k _ =>
        (((measurable_pi_apply k).comp measurable_fst).sub
          ((measurable_pi_apply k).comp measurable_snd)).pow_const 2
    · exact measurable_const
  have hF : ∀ j, AEMeasurable (F j) (μ.prod μ) := by
    intro j
    have hnum : AEMeasurable
        (fun q : SpatialCoordinates d × SpatialCoordinates d =>
          ((w (sigma j)).val 0 q.1 - (w (sigma j)).val 0 q.2) ^ 2) (μ.prod μ) :=
      (((hw j).aemeasurable.comp_fst).sub ((hw j).aemeasurable.comp_snd)).pow_const 2
    exact hnum.ennreal_ofReal.div hden.aemeasurable
  have hF_x (j : ℕ) (x : SpatialCoordinates d) :
      AEMeasurable (fun y : SpatialCoordinates d => F j (x, y)) μ := by
    have hnum : AEMeasurable
        (fun y : SpatialCoordinates d =>
          ((w (sigma j)).val 0 x - (w (sigma j)).val 0 y) ^ 2) μ :=
      ((measurable_const.aemeasurable.sub (hw j).aemeasurable).pow_const 2)
    have hdenx : Measurable
        (fun y : SpatialCoordinates d =>
          (ENNReal.ofReal (Real.sqrt (∑ k : Fin d, (x k - y k) ^ 2))) ^
            ((d : ℝ) + 2 * (threeQuarters : ℝ))) := by
      apply Measurable.pow
      · apply Measurable.ennreal_ofReal
        apply Measurable.sqrt
        exact Finset.measurable_sum Finset.univ fun k _ =>
          (measurable_const.sub (measurable_pi_apply k)).pow_const 2
      · exact measurable_const
    exact hnum.ennreal_ofReal.div hdenx.aemeasurable
  have hinner_meas : ∀ j, AEMeasurable
      (fun x : SpatialCoordinates d => ∫⁻ y, F j (x, y) ∂μ) μ := by
    intro j
    exact (hF j).lintegral_prod_right
  have hlim_pair : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ,
      Tendsto (fun j => F j (x, y)) atTop (𝓝 (F₀ (x, y))) := by
    have hae' : ∀ᵐ x ∂μ, Tendsto
        (fun j => (w (sigma j)).val 0 x) atTop (𝓝 (vlim x)) := by
      simpa only [μ, U] using hae
    filter_upwards [hae'] with x hx
    filter_upwards [hae'] with y hy
    by_cases hxy : x = y
    · subst y
      simp only [F, F₀, sub_self, sq, mul_zero, ENNReal.ofReal_zero]
      exact tendsto_const_nhds
    · have hsumpos : 0 < ∑ k : Fin d, (x k - y k) ^ 2 := by
        obtain ⟨k, hk⟩ : ∃ k : Fin d, x k ≠ y k := by
          simpa only [Function.ne_iff] using hxy
        exact Finset.sum_pos' (fun k _ => sq_nonneg _) ⟨k, Finset.mem_univ _,
          sq_pos_of_ne_zero (sub_ne_zero.mpr hk)⟩
      have hdenpos : 0 <
          (ENNReal.ofReal (Real.sqrt (∑ k : Fin d, (x k - y k) ^ 2))) ^
            ((d : ℝ) + 2 * (threeQuarters : ℝ)) := by
        positivity
      have hnum : Tendsto
          (fun j => ENNReal.ofReal
            (((w (sigma j)).val 0 x - (w (sigma j)).val 0 y) ^ 2)) atTop
          (𝓝 (ENNReal.ofReal ((vlim x - vlim y) ^ 2))) := by
        apply ENNReal.tendsto_ofReal
        exact (hx.sub hy).pow 2
      simpa only [F, F₀, Prod.fst, Prod.snd] using
        (ENNReal.Tendsto.div_const
          (b := (ENNReal.ofReal (Real.sqrt (∑ k : Fin d, (x k - y k) ^ 2))) ^
            ((d : ℝ) + 2 * (threeQuarters : ℝ))) hnum (Or.inr hdenpos.ne'))
  have hinner_fatou : ∀ᵐ x ∂μ,
      (∫⁻ y, F₀ (x, y) ∂μ) ≤
        liminf (fun j => ∫⁻ y, F j (x, y) ∂μ) atTop := by
    filter_upwards [hlim_pair] with x hx
    calc
      (∫⁻ y, F₀ (x, y) ∂μ) =
          ∫⁻ y, liminf (fun j => F j (x, y)) atTop ∂μ := by
        apply lintegral_congr_ae
        exact hx.mono fun y hy => hy.liminf_eq.symm
      _ ≤ liminf (fun j => ∫⁻ y, F j (x, y) ∂μ) atTop :=
        lintegral_liminf_le' (μ := μ) (fun j => hF_x j x)
  have houter_fatou :
      (∫⁻ x, ∫⁻ y, F₀ (x, y) ∂μ ∂μ) ≤
        liminf (fun j => ∫⁻ x, ∫⁻ y, F j (x, y) ∂μ ∂μ) atTop := by
    calc
      (∫⁻ x, ∫⁻ y, F₀ (x, y) ∂μ ∂μ) ≤
          ∫⁻ x, liminf (fun j => ∫⁻ y, F j (x, y) ∂μ) atTop ∂μ :=
        lintegral_mono_ae hinner_fatou
      _ ≤ liminf (fun j => ∫⁻ x, ∫⁻ y, F j (x, y) ∂μ ∂μ) atTop :=
        lintegral_liminf_le' (μ := μ) hinner_meas
  let a : ℝ≥0∞ := ENNReal.ofReal (threeQuarters : ℝ) / volume U
  have hvol_ne_zero : volume U ≠ 0 := by
    simp only [U, centeredCube_volume]
    exact (ENNReal.ofReal_pos.mpr (pow_pos hr _)).ne'
  have ha_ne_top : a ≠ ⊤ := by
    exact ENNReal.div_ne_top ENNReal.ofReal_ne_top hvol_ne_zero
  have hmul_liminf :
      a * liminf (fun j => ∫⁻ x, ∫⁻ y, F j (x, y) ∂μ ∂μ) atTop =
        liminf (fun j => a * (∫⁻ x, ∫⁻ y, F j (x, y) ∂μ ∂μ)) atTop := by
    exact Monotone.map_liminf_of_continuousAt
      (fun x y hxy => by gcongr)
      (fun j => ∫⁻ x, ∫⁻ y, F j (x, y) ∂μ ∂μ)
      (ENNReal.continuous_const_mul ha_ne_top).continuousAt
      (by all_goals isBoundedDefault)
  have hroot :
      (a * (∫⁻ x, ∫⁻ y, F₀ (x, y) ∂μ ∂μ)) ^ (1 / 2 : ℝ) ≤
        liminf (fun j =>
          (a * (∫⁻ x, ∫⁻ y, F j (x, y) ∂μ ∂μ)) ^ (1 / 2 : ℝ)) atTop := by
    have hmul : a * (∫⁻ x, ∫⁻ y, F₀ (x, y) ∂μ ∂μ) ≤
        a * liminf (fun j => ∫⁻ x, ∫⁻ y, F j (x, y) ∂μ ∂μ) atTop :=
      by gcongr
    have hpow : (a * (∫⁻ x, ∫⁻ y, F₀ (x, y) ∂μ ∂μ)) ^ (1 / 2 : ℝ) ≤
        (a * liminf (fun j => ∫⁻ x, ∫⁻ y, F j (x, y) ∂μ ∂μ) atTop) ^
          (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow hmul (by norm_num)
    have hliminf_pow :
        (liminf (fun j => a * (∫⁻ x, ∫⁻ y, F j (x, y) ∂μ ∂μ)) atTop) ^
            (1 / 2 : ℝ) =
          liminf (fun j =>
            (a * (∫⁻ x, ∫⁻ y, F j (x, y) ∂μ ∂μ)) ^ (1 / 2 : ℝ)) atTop := by
      exact (ENNReal.orderIsoRpow (1 / 2 : ℝ) (by norm_num)).liminf_apply
        (by all_goals isBoundedDefault)
    have hliminf_pow' :
        (a * liminf (fun j => ∫⁻ x, ∫⁻ y, F j (x, y) ∂μ ∂μ) atTop) ^
            (1 / 2 : ℝ) =
          liminf (fun j =>
            (a * (∫⁻ x, ∫⁻ y, F j (x, y) ∂μ ∂μ)) ^ (1 / 2 : ℝ)) atTop := by
      rw [hmul_liminf]
      exact hliminf_pow
    exact hpow.trans_eq hliminf_pow'
  simpa only [U, μ, a, F, F₀, cubeFractionalL2Seminorm, Fin.sum_univ_one] using hroot

/-- Limit-membership step implicit in the final interpolation sentence of
Lemma 19; expansion recorded in

Carried-input Scope and inputs:
- SOURCE: an H3/4 sequence on the actual cube, a uniform norm bound M,
  and convergence of its actual values to an L2 class vlim.
- TYPING: threeQuarters is in (0,1) and is pinned to 3/4.
- DEPENDENCY lem_19_limit_membership_ae_subsequence concludes the a.e.
  convergent subsequence used in the paper's Fatou step.
- DEPENDENCY lem_19_limit_membership_fractional_fatou concludes the
  lower-semicontinuity inequality for the nonnegative Gagliardo integral.
- DEPENDENCY lem_19_limit_membership_l2_term concludes convergence of the
  L2 term along the original sequence.
- CONCLUDED HERE: the L2 limit has an H3/4 representative with the same bound.
The bounded-ball closure follows from those three paper proof steps; neither
fractional membership of vlim nor a compactness conclusion is a premise. This
supplies the limit needed before applying the paper's interpolation inequality
to differences. -/
theorem lem_19_limit_membership
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r)
    (threeQuarters : Set.Ioo (0 : ℝ) 1)
    (hthree : (threeQuarters : ℝ) = 3 / 4)
    (w : ℕ → CubeFractionalL2 (k := 1) hd z r hr threeQuarters)
    (vlim : DomainL2 (centeredCube z r hr)) (M : ℝ)
    (hbound : ∀ n, cubeFractionalL2Norm hd z r hr threeQuarters (w n) ≤ M)
    (hlim : Tendsto (fun n : ℕ => (w n).val 0) atTop (𝓝 vlim)) :
    ∃ vthree : CubeFractionalL2 (k := 1) hd z r hr threeQuarters,
      vthree.val 0 = vlim ∧
      cubeFractionalL2Norm hd z r hr threeQuarters vthree ≤ M := by
  classical
  obtain ⟨sigma, hsigma, hae⟩ :=
    lem_19_limit_membership_ae_subsequence d hd z r hr threeQuarters hthree w vlim hlim
  have hfatou := aux_lem_19_limit_membership_fatou d hd z r hr threeQuarters
    w vlim sigma hae
  have hl2 := lem_19_limit_membership_l2_term d hd z r hr threeQuarters hthree w vlim hlim
  let S : ℕ → ℝ≥0∞ := fun n =>
    cubeFractionalL2Seminorm hd z r hr threeQuarters (w n).val
  let A : ℕ → ℝ := fun n => (S n).toReal
  let B : ℕ → ℝ := fun n =>
    r ^ (-(threeQuarters : ℝ)) *
      (‖(w n).val 0‖ /
        Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))))
  let Sσ : ℕ → ℝ≥0∞ := fun j => S (sigma j)
  let Aσ : ℕ → ℝ := fun j => A (sigma j)
  let Bσ : ℕ → ℝ := fun j => B (sigma j)
  have hdecomp : ∀ n, cubeFractionalL2Norm hd z r hr threeQuarters (w n) =
      A n + B n := by
    intro n
    unfold A B S
    unfold cubeFractionalL2Norm
    simp only [Fin.sum_univ_one]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hB_nonneg : ∀ n, 0 ≤ B n := by
    intro n
    unfold B
    positivity
  have hA_nonneg : ∀ n, 0 ≤ A n := by
    intro n
    exact ENNReal.toReal_nonneg
  have hfull_nonneg : 0 ≤ cubeFractionalL2Norm hd z r hr threeQuarters (w 0) := by
    rw [hdecomp]
    exact add_nonneg (hA_nonneg 0) (hB_nonneg 0)
  have hM : 0 ≤ M := hfull_nonneg.trans (hbound 0)
  have hfull_sigma : ∀ j,
      Aσ j + Bσ j ≤ M := by
    intro j
    simpa only [Aσ, Bσ, Function.comp_apply, ← hdecomp (sigma j)] using hbound (sigma j)
  have hA_sigma_le : ∀ j, Aσ j ≤ M := by
    intro j
    linarith [hfull_sigma j, hB_nonneg (sigma j)]
  have hS_sigma_le : ∀ j, Sσ j ≤ ENNReal.ofReal M := by
    intro j
    have hSj : Sσ j ≠ ⊤ := by
      exact ne_of_lt (by simpa only [Sσ, S] using (w (sigma j)).property)
    apply (ENNReal.le_ofReal_iff_toReal_le hSj hM).2
    exact hA_sigma_le j
  have hliminfS_le : liminf Sσ atTop ≤ ENNReal.ofReal M := by
    apply liminf_le_of_le
      (isBoundedUnder_of_eventually_ge (Eventually.of_forall (fun j => bot_le)))
    intro b hb
    obtain ⟨j, hj⟩ := (hb.and (Eventually.of_forall hS_sigma_le)).exists
    exact hj.1.trans hj.2
  have hliminfS_ne_top : liminf Sσ atTop ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hliminfS_le
  have hS_lim_ne_top :
      cubeFractionalL2Seminorm hd z r hr threeQuarters
          (fun _ : Fin 1 => vlim) ≠ ⊤ := by
    apply ne_top_of_le_ne_top hliminfS_ne_top
    exact hfatou
  have hreal_fatou :
      (cubeFractionalL2Seminorm hd z r hr threeQuarters
          (fun _ : Fin 1 => vlim)).toReal ≤
        liminf Aσ atTop := by
    have h₁ := ENNReal.toReal_mono hliminfS_ne_top hfatou
    have h₂ : liminf (fun j => (Sσ j).toReal) atTop =
        (liminf Sσ atTop).toReal := by
      exact ENNReal.liminf_toReal_eq ENNReal.ofReal_ne_top
        (Eventually.of_forall hS_sigma_le)
    exact h₁.trans_eq h₂.symm
  have hnorm_sigma :
      Tendsto (fun j => ‖(w (sigma j)).val 0‖) atTop (𝓝 ‖vlim‖) :=
    hl2.comp hsigma.tendsto_atTop
  let B_lim : ℝ :=
    r ^ (-(threeQuarters : ℝ)) *
      (‖vlim‖ /
        Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))))
  have hB_tendsto : Tendsto Bσ atTop (𝓝 B_lim) := by
    dsimp [Bσ, B, B_lim]
    exact (hnorm_sigma.div_const _).const_mul _
  have hliminfB : liminf Bσ atTop = B_lim := hB_tendsto.liminf_eq
  have hA_lower : IsBoundedUnder (· ≥ ·) atTop Aσ := by
    exact isBoundedUnder_of_eventually_ge
      (Eventually.of_forall (fun j => hA_nonneg (sigma j)))
  have hA_upper : IsBoundedUnder (· ≤ ·) atTop Aσ := by
    exact isBoundedUnder_of_eventually_le
      (Eventually.of_forall (fun j => hA_sigma_le j))
  have hB_lower : IsBoundedUnder (· ≥ ·) atTop Bσ := by
    exact isBoundedUnder_of_eventually_ge
      (Eventually.of_forall (fun j => hB_nonneg (sigma j)))
  have hB_sigma_le : ∀ j, Bσ j ≤ M := by
    intro j
    linarith [hfull_sigma j, hA_nonneg (sigma j)]
  have hB_upper : IsBoundedUnder (· ≤ ·) atTop Bσ := by
    exact isBoundedUnder_of_eventually_le
      (Eventually.of_forall (fun j => hB_sigma_le j))
  have hliminf_add :
      liminf Aσ atTop + liminf Bσ atTop ≤ liminf (Aσ + Bσ) atTop := by
    exact le_liminf_add hA_lower hA_upper hB_lower hB_upper.isCoboundedUnder_ge
  have hsum_bound : ∀ j, Aσ j + Bσ j ≤ M := hfull_sigma
  have hliminf_sum_le : liminf (Aσ + Bσ) atTop ≤ M := by
    apply liminf_le_of_le
      (isBoundedUnder_of_eventually_ge (Eventually.of_forall (fun j =>
        add_nonneg (hA_nonneg (sigma j)) (hB_nonneg (sigma j)))))
    intro b hb
    obtain ⟨j, hj⟩ := (hb.and (Eventually.of_forall hsum_bound)).exists
    exact hj.1.trans hj.2
  have hfull_lim :
      (cubeFractionalL2Seminorm hd z r hr threeQuarters
          (fun _ : Fin 1 => vlim)).toReal + B_lim ≤ M := by
    calc
      _ = (cubeFractionalL2Seminorm hd z r hr threeQuarters
          (fun _ : Fin 1 => vlim)).toReal + liminf Bσ atTop := by rw [hliminfB]
      _ ≤ liminf Aσ atTop + liminf Bσ atTop := by
        gcongr
      _ ≤ liminf (Aσ + Bσ) atTop := hliminf_add
      _ ≤ M := hliminf_sum_le
  refine ⟨⟨fun _ : Fin 1 => vlim, lt_top_iff_ne_top.mpr hS_lim_ne_top⟩, ?_, ?_⟩
  · rfl
  · simpa only [cubeFractionalL2Norm, B_lim, Fin.sum_univ_one,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg vlim)] using hfull_lim

end SubdiffusiveProcess.Paper

