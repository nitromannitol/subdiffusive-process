module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.UniformProbeDecay
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.ResponseStationarity

@[expose] public section

/-!
# One `L^xi` bound for the probe sum on **every** triadic cube

The union bound over a descendant family needs the per-cube `L^xi` moment of
`finiteProbeSum` as a function of the *cube*, not of a centred scale: a decaying
bound

    `‖finiteProbeSum M L (ahom M L) R‖_{L^xi} ≤ Cst xi * 3^{-rho * R.scale}`

valid for every triadic cube `R` of every scale, positive or negative, with a
**dimension-only** `rho`.

Two ingredients are combined: `UniformProbeDecay.lean` (decay at large positive
centred scales, dimension-only rate) and `ProbeMomentNonpos.lean` (a single
bound valid on every cube, no decay).  Stationarity of the probe sum across
cubes of a fixed scale — proved here from the response stationarity of
`ResponseStationarity.lean` — moves both from centred cubes to arbitrary ones.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators

noncomputable section


variable {d : ℕ}

/-! ## Stationarity of the probe sum -/

/-- The probe sum on a cube is the probe sum on the centred cube of the same
scale, evaluated at the translated sample. -/
theorem finiteProbeSum_cube_eq_originCube_translate
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (alpha : ℝ)
    (R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    finiteProbeSum M L alpha R omega =
      finiteProbeSum M L alpha (originCube d R.scale)
        (translatePotentialSequence (triadicCubeShift R) omega) := by
  simp only [finiteProbeSum, cutoffProbeForm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [cutoffResponseOnCube_cube_eq_originCube_translate M L _ _ R omega,
    cutoffResponseOnCube_cube_eq_originCube_translate M L _ _ R omega,
    cutoffResponseOnCube_cube_eq_originCube_translate M L _ _ R omega]

/-- The probe sum is measurable. -/
theorem measurable_finiteProbeSum [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (alpha : ℝ)
    (R : TriadicCube d) :
    Measurable fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => finiteProbeSum M L alpha R omega := by
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  exact (((measurable_cutoffResponseOnCube M L _ _ R).add
    (measurable_cutoffResponseOnCube M L _ _ R)).add
    (measurable_cutoffResponseOnCube M L _ _ R)).const_mul _

/-- Every cube of a given scale carries the same `L^xi` probe moment as the
centred cube of that scale. -/
theorem lpMoment_finiteProbeSum_eq_originCube [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (alpha : ℝ)
    (R : TriadicCube d) (xi : ℝ) :
    lpMoment M.P.toMeasure xi
        (fun omega => finiteProbeSum M L alpha R omega) =
      lpMoment M.P.toMeasure xi
        (fun omega => finiteProbeSum M L alpha (originCube d R.scale) omega) := by
  have hfun : (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      |finiteProbeSum M L alpha R omega| ^ xi) =
      fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        (fun eta : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
          |finiteProbeSum M L alpha (originCube d R.scale) eta| ^ xi)
          (translatePotentialSequence (triadicCubeShift R) omega) := by
    funext omega
    rw [finiteProbeSum_cube_eq_originCube_translate M L alpha R omega]
  simp only [lpMoment]
  congr 1
  rw [hfun]
  refine Homogenization.integral_comp_eq_of_map_eq
    (measurable_translatePotentialSequence (triadicCubeShift R))
    (potentialSequenceLaw_stationary M (triadicCubeShift R))
    (fun eta : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      |finiteProbeSum M L alpha (originCube d R.scale) eta| ^ xi) ?_
  have habs : Measurable fun eta : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      |finiteProbeSum M L alpha (originCube d R.scale) eta| := by
    simpa only [Real.norm_eq_abs] using!
      (measurable_finiteProbeSum M L alpha (originCube d R.scale)).norm
  exact (habs.pow_const xi).aestronglyMeasurable

/-! ## The all-cube decaying bound -/

/-- **One decaying `L^xi` bound on every triadic cube, at a dimension-only
rate.** -/
theorem exists_allScale_lpMoment_finiteProbeSum_bound (d : ℕ) [NeZero d]
    (hd : 2 ≤ d) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ 1 / 16 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ),
        ∃ Cst : ℝ → ℝ, (∀ xi : ℝ, 0 ≤ Cst xi) ∧
          ∀ xi : ℝ, 2 ≤ xi → ∀ R : TriadicCube d,
            lpMoment M.P.toMeasure xi
                (fun omega => finiteProbeSum M L (ahom M L) R omega) ≤
              Cst xi * Real.rpow (3 : ℝ) (-rho * ((R.scale : ℤ) : ℝ)) := by
  classical
  obtain ⟨rho0, hrho0, hdecay⟩ := exists_uniform_lpMoment_finiteProbeSum_decay d hd
  refine ⟨min rho0 (1 / 16), lt_min hrho0 (by norm_num), min_le_right _ _, ?_⟩
  set rho : ℝ := min rho0 (1 / 16) with hrhodef
  have hrhopos : 0 < rho := lt_min hrho0 (by norm_num)
  have hrhole : rho ≤ rho0 := min_le_left _ _
  intro M L
  have halpha : 0 < ahom M L :=
    (Real.exp_pos _).trans_le
      (_root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M L)
  obtain ⟨m₀, Cst0, hCst0⟩ := hdecay M L
  have huniform : ∀ xi : ℝ, 2 ≤ xi → ∃ B : ℝ, 0 ≤ B ∧
      ∀ R : TriadicCube d,
        lpMoment M.P.toMeasure xi
          (fun omega => finiteProbeSum M L (ahom M L) R omega) ≤ B := by
    intro xi hxi
    exact exists_uniform_lpMoment_finiteProbeSum M L halpha
      (le_trans (by norm_num) hxi)
  have hBex : ∀ xi : ℝ, ∃ B : ℝ, 0 ≤ B ∧ (2 ≤ xi →
      ∀ R : TriadicCube d,
        lpMoment M.P.toMeasure xi
          (fun omega => finiteProbeSum M L (ahom M L) R omega) ≤ B) := by
    intro xi
    by_cases hxi : 2 ≤ xi
    · obtain ⟨B, hB0, hB⟩ := huniform xi hxi
      exact ⟨B, hB0, fun _ => hB⟩
    · exact ⟨0, le_rfl, fun h => absurd h hxi⟩
  choose B hB0 hB using hBex
  refine ⟨fun xi => max (Cst0 xi) (B xi * Real.rpow (3 : ℝ) (rho * (m₀ : ℝ))), ?_, ?_⟩
  · intro xi
    refine le_trans ?_ (le_max_right (Cst0 xi) _)
    have : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (rho * (m₀ : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    exact mul_nonneg (hB0 xi) this
  · intro xi hxi R
    rw [lpMoment_finiteProbeSum_eq_originCube M L (ahom M L) R xi]
    have hpow : (0 : ℝ) < Real.rpow (3 : ℝ) (-rho * ((R.scale : ℤ) : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    rcases le_or_gt ((m₀ : ℤ)) R.scale with hcase | hcase
    · -- large positive scale: use the decay
      have hnn : (0 : ℤ) ≤ R.scale := le_trans (Int.natCast_nonneg m₀) hcase
      set m : ℕ := R.scale.toNat with hm
      have hmz : ((m : ℕ) : ℤ) = R.scale := Int.toNat_of_nonneg hnn
      have hm0 : m₀ ≤ m := by omega
      have hbound := hCst0 xi hxi m hm0
      have hcubeeq : originCube d ((m : ℕ) : ℤ) = originCube d R.scale := by
        rw [hmz]
      rw [hcubeeq] at hbound
      have hCst0nonneg : 0 ≤ Cst0 xi := by
        by_contra hneg
        push Not at hneg
        have hp : (0 : ℝ) < Real.rpow (3 : ℝ) (-rho0 * (m : ℝ)) :=
          Real.rpow_pos_of_pos (by norm_num) _
        have : Cst0 xi * Real.rpow (3 : ℝ) (-rho0 * (m : ℝ)) < 0 :=
          mul_neg_of_neg_of_pos hneg hp
        have hge := lpMoment_nonneg M.P.toMeasure xi
          (fun omega => finiteProbeSum M L (ahom M L) (originCube d R.scale) omega)
        linarith
      have hexp : Real.rpow (3 : ℝ) (-rho0 * (m : ℝ)) ≤
          Real.rpow (3 : ℝ) (-rho * ((R.scale : ℤ) : ℝ)) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        have hmr : ((R.scale : ℤ) : ℝ) = (m : ℝ) := by
          rw [← hmz]; push_cast; ring
        rw [hmr]
        nlinarith [Nat.cast_nonneg (α := ℝ) m, hrhole]
      refine le_trans hbound ?_
      refine le_trans (mul_le_mul_of_nonneg_left hexp hCst0nonneg) ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hpow.le
    · -- small or negative scale: use the uniform bound
      have hstep := hB xi hxi (originCube d R.scale)
      refine le_trans hstep ?_
      have hone : (1 : ℝ) ≤ Real.rpow (3 : ℝ)
          (rho * (m₀ : ℝ) + -rho * ((R.scale : ℤ) : ℝ)) := by
        have hlt : ((R.scale : ℤ) : ℝ) ≤ (m₀ : ℝ) := by
          have : R.scale ≤ (m₀ : ℤ) := le_of_lt hcase
          exact_mod_cast this
        have hnonneg : (0 : ℝ) ≤ rho * (m₀ : ℝ) + -rho * ((R.scale : ℤ) : ℝ) := by
          nlinarith [hrhopos]
        have := Real.rpow_le_rpow_of_exponent_le
          (x := (3 : ℝ)) (by norm_num) hnonneg
        simpa using! this
      have hsplit : Real.rpow (3 : ℝ) (rho * (m₀ : ℝ)) *
          Real.rpow (3 : ℝ) (-rho * ((R.scale : ℤ) : ℝ)) =
          Real.rpow (3 : ℝ) (rho * (m₀ : ℝ) + -rho * ((R.scale : ℤ) : ℝ)) :=
        (Real.rpow_add (by norm_num) _ _).symm
      have hchain : B xi ≤ (B xi * Real.rpow (3 : ℝ) (rho * (m₀ : ℝ))) *
          Real.rpow (3 : ℝ) (-rho * ((R.scale : ℤ) : ℝ)) := by
        rw [mul_assoc, hsplit]
        nlinarith [hB0 xi, hone]
      refine le_trans hchain ?_
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hpow.le

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge
