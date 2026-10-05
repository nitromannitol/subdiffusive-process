module

public import SubdiffusiveProcess.Paper.lem_as_regularity_neumann_root_decay

@[expose] public section

/-! The physical root decay extends to every resolved radius with an
exponential cost in the actual finite allowance. Short windows use energy
monotonicity. No moment or cutoff-uniform allowance bound is asserted here.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- A resolved triadic radius has a nonnegative native index below its root. -/
theorem aux_lem_as_regularity_neumann_onestep_index (N k : ℕ) (hkN : k ≤ N)
    (s : ℝ) (hs : s ∈ Set.range (fun j : ℤ => (3 : ℝ) ^ j / 2))
    (hmin : (3 : ℝ) ^ (-(N : ℤ)) / 2 ≤ s) (hs0 : 0 < s)
    (hsR : 8 * s < (3 : ℝ) ^ (-(k : ℤ)) / 2) :
    ∃ n : ℕ, n ≤ N - k + 1 ∧ s = (3 : ℝ) ^ ((n : ℤ) - N) / 2 := by
  obtain ⟨q, rfl⟩ := hs
  have hlo : -(N : ℤ) ≤ q := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).mp
    (by linarith only [hmin])
  have hhi : q ≤ -(k : ℤ) := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).mp
    (by linarith only [hsR, hs0])
  refine ⟨(q + N).toNat, by omega, ?_⟩
  congr 2
  omega

/-- Every resolved radius has the rooted estimate with the actual allowance penalty. -/
theorem lem_as_regularity_neumann_onestep (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (D : deterministic_good_scale_input d)
    (t : ℝ) (ht1 : (d : ℝ) - 1 < t) (ht2 : t < (d : ℝ)) :
    ∃ eps rate delta0 C c : ℝ,
      eps ∈ Ioo (0 : ℝ) 1 ∧ 0 < rate ∧ 0 < delta0 ∧ 1 ≤ C ∧ 0 ≤ c ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (F P R Draw : ℕ → ℕ → Vec d → BilateralField d → ℝ≥0∞)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (good : ℕ → ℕ → Vec d → BilateralField d → Prop),
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ (N i : ℕ) (y : Vec d),
        eta N omega i y = omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
        primitive_scores d M (1 / 32) eps (eta N omega)
          (fun m y => F N m y omega) (fun m y => P N m y omega)
          (fun m y => R N m y omega) (fun m y => Draw N m y omega)
          (fun m y => Z N m y omega) (fun m y => good N m y omega)) →
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N : ℕ) (f : SpatialCoordinates d → ℝ),
        AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
      ∀ Kf : ℝ, 0 ≤ Kf →
        (∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)), |f x| ≤ Kf) →
        (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), f x) = 0 →
      ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
        SolvesNeumann (cutoffPositiveCoefficient M H omega N (fun _ => (1 / 2 : ℝ)) one_pos) f u →
      ∀ (y : SpatialCoordinates d), y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
      ∀ (I : Finset (Fin d)) (Lstar : ℝ), 10 ≤ Lstar →
      ∀ (s : ℝ) (k : ℕ), 1 ≤ k → k ≤ N →
        s ∈ Set.range (fun j : ℤ => (3 : ℝ) ^ j / 2) →
        (3 : ℝ) ^ (-(N : ℤ)) / 2 ≤ s → 0 < s → 8 * s < (3 : ℝ) ^ (-(k : ℤ)) / 2 →
        (∀ i, i ∉ I → 4 * Lstar * ((3 : ℝ) ^ (-(k : ℤ)) / 2) ≤ min (y i) (1 - y i)) →
        aux_rem_resolved_meshes_energy
          (cutoffPositiveCoefficient M H omega N (fun _ => (1 / 2 : ℝ)) one_pos) u
          (Metric.ball (aux_rem_resolved_meshes_center y I) s) ≤
          C * Real.exp (c * (nativeScoreAllowance
            (fun j => Z N j ((3 : ℝ) ^ N • aux_rem_resolved_meshes_center y I) omega)
            (fun j => Draw N j ((3 : ℝ) ^ N • aux_rem_resolved_meshes_center y I) omega)
            (N - k + 1) rate : ℝ)) * (s / ((3 : ℝ) ^ (-(k : ℤ)) / 2)) ^ t *
            (aux_rem_resolved_meshes_energy
              (cutoffPositiveCoefficient M H omega N (fun _ => (1 / 2 : ℝ)) one_pos) u
              (Metric.ball (aux_rem_resolved_meshes_center y I) (Lstar * ((3 : ℝ) ^ (-(k : ℤ)) / 2))) +
              (aux_in_deterministic_onestep_sref M H omega N ((k : ℤ) - 1)
                (aux_rem_resolved_meshes_center y I))⁻¹ * Kf ^ 2 *
                  ((3 : ℝ) ^ (-(k : ℤ)) / 2) ^ ((d : ℝ) + 2)) := by
  obtain ⟨eps, rate, delta0, C0, heps, hrate, hd0, hC0, hdecay⟩ :=
    lem_as_regularity_neumann_root_decay d hd E D t ht1 ht2
  have ht : 0 ≤ t := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [ht1, hdR]
  have hc : 0 ≤ t * Real.log 3 := mul_nonneg ht (Real.log_nonneg (by norm_num))
  refine ⟨eps, rate, delta0, max 1 C0, t * Real.log 3, heps, hrate, hd0, le_max_left _ _, hc, ?_⟩
  intro M Rm H hIR hdelta eta F P R Draw Z good hEta hPS
  filter_upwards [hdecay M Rm H hIR hdelta eta F P R Draw Z good hEta hPS] with omega hdec
  intro N f hf Kf hKf hfb hf0 u hu y hy I Lstar hLstar s k hk1 hkN hs hsmin hs0 hsR hI
  obtain ⟨n, hnm, hseq⟩ := aux_lem_as_regularity_neumann_onestep_index N k hkN s hs hsmin hs0 hsR
  let a := cutoffPositiveCoefficient M H omega N (fun _ => (1 / 2 : ℝ)) one_pos
  let B := nativeScoreAllowance (fun j => Z N j ((3 : ℝ) ^ N • aux_rem_resolved_meshes_center y I) omega)
    (fun j => Draw N j ((3 : ℝ) ^ N • aux_rem_resolved_meshes_center y I) omega) (N - k + 1) rate
  let Rk := (3 : ℝ) ^ (-(k : ℤ)) / 2
  let src := (aux_in_deterministic_onestep_sref M H omega N ((k : ℤ) - 1)
    (aux_rem_resolved_meshes_center y I))⁻¹ * Kf ^ 2 * Rk ^ ((d : ℝ) + 2)
  have hRk : 0 < Rk := by dsimp only [Rk]; positivity
  have hsrc : 0 ≤ src := by
    have hh := aux_in_deterministic_onestep_sref_pos M H omega N ((k : ℤ) - 1)
      (aux_rem_resolved_meshes_center y I)
    dsimp only [src]
    positivity
  have hEnn : ∀ S, 0 ≤ aux_rem_resolved_meshes_energy a u S :=
    fun S => aux_rem_resolved_strata_energy_nonneg a ⟨u.1, u.2.1⟩ S
  have hmono : ∀ S T, S ⊆ T → aux_rem_resolved_meshes_energy a u S ≤ aux_rem_resolved_meshes_energy a u T :=
    fun S T hST => aux_rem_resolved_strata_energy_mono a ⟨u.1, u.2.1⟩ hST
  have houter : aux_rem_resolved_meshes_energy a u
      (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * Rk)) ≤
        aux_rem_resolved_meshes_energy a u (Metric.ball (aux_rem_resolved_meshes_center y I) (Lstar * Rk)) :=
    hmono _ _ (Metric.ball_subset_ball (mul_le_mul_of_nonneg_right (by linarith only [hLstar]) hRk.le))
  have hexp : 1 ≤ Real.exp ((t * Real.log 3) * (B : ℝ)) :=
    Real.one_le_exp (mul_nonneg hc (Nat.cast_nonneg _))
  have hmult : C0 ≤ max 1 C0 * Real.exp ((t * Real.log 3) * (B : ℝ)) :=
    (le_max_right _ _).trans (le_mul_of_one_le_right (le_trans zero_le_one (le_max_left _ _)) hexp)
  have hpow : 0 ≤ (s / Rk) ^ t := Real.rpow_nonneg (div_nonneg hs0.le hRk.le) _
  change aux_rem_resolved_meshes_energy a u (Metric.ball (aux_rem_resolved_meshes_center y I) s) ≤
    max 1 C0 * Real.exp ((t * Real.log 3) * (B : ℝ)) * (s / Rk) ^ t *
      (aux_rem_resolved_meshes_energy a u (Metric.ball (aux_rem_resolved_meshes_center y I) (Lstar * Rk)) + src)
  by_cases hB : B ≤ N - k + 1 - n
  · have hh := hdec N f hf Kf hKf hfb hf0 u hu y hy I Lstar hLstar n k hk1 hkN hnm hI hB
    rw [← hseq] at hh
    refine hh.trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_right hmult hpow) (add_le_add houter (le_refl src))
      (add_nonneg (hEnn _) hsrc) (mul_nonneg (mul_nonneg (le_trans zero_le_one (le_max_left _ _))
        (Real.exp_pos _).le) hpow)
  · have hBl : ((N - k + 1 : ℕ) : ℝ) - n ≤ (B : ℝ) := by
      have hh : N - k + 1 - n ≤ B := by omega
      exact_mod_cast (show (N - k + 1 : ℕ) - n ≤ B from hh)
    have hm : ((N - k + 1 : ℕ) : ℝ) = (N : ℝ) - k + 1 := by
      rw [Nat.cast_add, Nat.cast_sub hkN, Nat.cast_one]
    have hpen : 1 ≤ Real.exp ((t * Real.log 3) * (B : ℝ)) * (s / Rk) ^ t := by
      rw [hseq, aux_rem_resolved_meshes_arith_sigma t n N k (N - k + 1) hm, ← Real.exp_add]
      apply Real.one_le_exp
      have hh := mul_nonneg hc (show 0 ≤ (B : ℝ) + n - (N - k + 1 : ℕ) + 1 by linarith only [hBl])
      nlinarith only [hh]
    have hfac : 1 ≤ max 1 C0 * Real.exp ((t * Real.log 3) * (B : ℝ)) * (s / Rk) ^ t := by
      rw [mul_assoc]
      exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) hpen
    have hsL : s ≤ Lstar * Rk := by
      change 8 * s < Rk at hsR
      nlinarith only [hsR, hs0, hLstar, hRk]
    exact (hmono _ _ (Metric.ball_subset_ball hsL)).trans
      ((le_add_of_nonneg_right hsrc).trans (le_mul_of_one_le_left
        (add_nonneg (hEnn _) hsrc) hfac))

end SubdiffusiveProcess.Paper
