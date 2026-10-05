module

public import SubdiffusiveProcess.Paper.lem_as_regularity_actual_iteration
public import SubdiffusiveProcess.Paper.lem_as_regularity_actual_root
public import SubdiffusiveProcess.Analysis.ContinuousScalarFamily

@[expose] public section

/-! The actual native iteration transports to physical energy decay for a
reflected Neumann root beyond its finite score allowance. The estimate is
simultaneous in the source and solution; no mesh envelope is assumed.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The original score allowance gives the physical Neumann root energy decay. -/
theorem lem_as_regularity_neumann_root_decay (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (D : deterministic_good_scale_input d)
    (t : ℝ) (ht1 : (d : ℝ) - 1 < t) (ht2 : t < (d : ℝ)) :
    ∃ eps rate delta0 C : ℝ,
      eps ∈ Ioo (0 : ℝ) 1 ∧ 0 < rate ∧ 0 < delta0 ∧ 0 < C ∧
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
      ∀ (n k : ℕ), 1 ≤ k → k ≤ N → n ≤ N - k + 1 →
        (∀ i, i ∉ I → 4 * Lstar * ((3 : ℝ) ^ (-(k : ℤ)) / 2) ≤ min (y i) (1 - y i)) →
        nativeScoreAllowance (fun j => Z N j ((3 : ℝ) ^ N • aux_rem_resolved_meshes_center y I) omega)
          (fun j => Draw N j ((3 : ℝ) ^ N • aux_rem_resolved_meshes_center y I) omega)
            (N - k + 1) rate ≤ N - k + 1 - n →
        aux_rem_resolved_meshes_energy
          (cutoffPositiveCoefficient M H omega N (fun _ => (1 / 2 : ℝ)) one_pos) u
          (Metric.ball (aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ ((n : ℤ) - N) / 2)) ≤
          C * (((3 : ℝ) ^ ((n : ℤ) - N) / 2) / ((3 : ℝ) ^ (-(k : ℤ)) / 2)) ^ t *
            (aux_rem_resolved_meshes_energy
              (cutoffPositiveCoefficient M H omega N (fun _ => (1 / 2 : ℝ)) one_pos) u
              (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-(k : ℤ)) / 2))) +
              (aux_in_deterministic_onestep_sref M H omega N ((k : ℤ) - 1)
                (aux_rem_resolved_meshes_center y I))⁻¹ * Kf ^ 2 *
                  ((3 : ℝ) ^ (-(k : ℤ)) / 2) ^ ((d : ℝ) + 2)) := by
  have hrho : 0 < ((d : ℝ) - t) / 2 := by linarith only [ht2]
  have hrho1 : ((d : ℝ) - t) / 2 ≤ 1 := by linarith only [ht1]
  obtain ⟨eps, rate, delta0, Cf, heps, hrate, hd0, hCf, hiter⟩ :=
    lem_as_regularity_actual_iteration d hd E D (((d : ℝ) - t) / 2) hrho hrho1
  obtain ⟨Ch, hCh, hsrc⟩ := aux_rem_resolved_meshes_fin_source d hd
  have hCpos : 0 < 2 * Cf ^ 2 * max 1 (Ch ^ 2 * d * 6 ^ (d + 2)) :=
    mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hCf)) (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  refine ⟨eps, rate, delta0, 2 * Cf ^ 2 * max 1 (Ch ^ 2 * d * 6 ^ (d + 2)),
    heps, hrate, hd0, hCpos, ?_⟩
  intro M Rm H hIR hdelta eta F P R Draw Z good hEta hPS
  filter_upwards [hiter M Rm H hIR hdelta eta F P R Draw Z good hEta hPS] with omega hw
  intro N f hf Kf hKf hfb hf0 u hu y hy I Lstar hLstar n k hk1 hkN hnm hI hallow
  let a := cutoffPositiveCoefficient M H omega N (fun _ => (1 / 2 : ℝ)) one_pos
  obtain ⟨f2, hf2m, hf2b, hff2⟩ := aux_rem_resolved_meshes_clamp f hf Kf hKf hfb
  have hf20 : (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), f2 x) = 0 := by
    rw [← hf0]
    exact integral_congr_ae hff2.symm
  have hu2 : SolvesNeumann a f2 u := by
    intro ψ
    rw [hu ψ]
    apply integral_congr_ae
    filter_upwards [hff2] with x hx
    rw [hx]
  have hl : (0 : ℝ) < (3 : ℝ) ^ N := by positivity
  have hR : (0 : ℝ) < (3 : ℝ) ^ (N - k + 1) := by positivity
  have hRk : (0 : ℝ) < (3 : ℝ) ^ (-(k : ℤ)) / 2 := by positivity
  have h3m : (3 : ℝ) ^ (N - k + 1) = (3 : ℝ) ^ N * (3 * (3 : ℝ) ^ (-(k : ℤ))) := by
    simpa only [zpow_natCast] using aux_rem_resolved_meshes_fin_scales N k hkN
  have hscale : (3 : ℝ) ^ (N - k + 1) / 2 =
      (3 : ℝ) ^ N * (3 * ((3 : ℝ) ^ (-(k : ℤ)) / 2)) := by rw [h3m]; ring
  obtain ⟨fc, ut, hfc, hueq, hE⟩ := lem_as_regularity_actual_root M H omega N (N - k + 1) hR
    f2 hf2m Kf hKf hf2b hf20 u hu2 y hy I Lstar ((3 : ℝ) ^ (-(k : ℤ)) / 2) hLstar hRk
    (aux_rem_resolved_meshes_fin_Rk k hk1) hI hscale
  let Fr := fun x : SpatialCoordinates d => ((3 : ℝ) ^ N)⁻¹ *
    f2 (((3 : ℝ) ^ N)⁻¹ • coordinateFold ((3 : ℝ) ^ N • aux_rem_resolved_meshes_center y I)
      I (aux_rem_resolved_meshes_faceSet y I) x)
  have hFrm : Measurable Fr := measurable_const.mul (hf2m.comp
    ((continuous_const_smul _).comp (coordinateFold_continuous _ _ _)).measurable)
  have hMF : 0 ≤ ((3 : ℝ) ^ N)⁻¹ * Kf := by positivity
  have hFrb : ∀ x, |Fr x| ≤ ((3 : ℝ) ^ N)⁻¹ * Kf := by
    intro x
    dsimp only [Fr]
    rw [abs_mul, abs_of_pos (inv_pos.mpr hl)]
    exact mul_le_mul_of_nonneg_left (hf2b _) (inv_pos.mpr hl).le
  obtain ⟨g, hgrad, hg, hgae, hid, hGb⟩ := hsrc ((3 : ℝ) ^ N • aux_rem_resolved_meshes_center y I)
    ((3 : ℝ) ^ (N - k + 1)) hR Fr hFrm (((3 : ℝ) ^ N)⁻¹ * Kf) hMF hFrb
  let coef := fun x => cutoffCoefficient M H omega N
    (coordinateFold (aux_rem_resolved_meshes_center y I) I (aux_rem_resolved_meshes_faceSet y I)
      ((3 : ℝ) ^ (-(N : ℤ)) • x + aux_rem_resolved_meshes_center y I))
  have hchart : Continuous (fun x : SpatialCoordinates d =>
      (3 : ℝ) ^ (-(N : ℤ)) • x + aux_rem_resolved_meshes_center y I) := by
    fun_prop
  have hc : Continuous coef := (cutoffCoefficient_continuous M H omega N).comp
    ((coordinateFold_continuous _ _ _).comp hchart)
  have hpos : ∀ x, 0 < coef x := fun x => cutoffCoefficient_pos M H omega N _
  let data := continuousScalarFamily (fun x => coef (x + 0))
    (hc.comp (continuous_id.add continuous_const)) (fun x => hpos _)
  have hcore := hw N (N - k + 1) n hnm (aux_rem_resolved_meshes_center y I)
    I (aux_rem_resolved_meshes_faceSet y I) hallow hR g hg data fc hfc ut hgrad hgae
    (fun φ => (hueq φ).trans (hid φ))
  have hn3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hnR : (3 : ℝ) ^ n ≤ (3 : ℝ) ^ (N - k + 1) := pow_le_pow_right₀ (by norm_num) hnm
  have hEs := hE ((3 : ℝ) ^ n) hn3 hnR
  have hEm := hE ((3 : ℝ) ^ (N - k + 1)) hR le_rfl
  have hvol : ∀ (r : ℝ) (hr : 0 < r), volume.real (centeredCube
      ((3 : ℝ) ^ N • aux_rem_resolved_meshes_center y I) r hr : Set (SpatialCoordinates d)) = r ^ d := by
    intro r hr
    rw [measureReal_def, centeredCube_volume, ENNReal.toReal_ofReal (by positivity)]
  simp only [normalizedEnergyNorm] at hcore
  rw [hEs, hEm, hvol, hvol] at hcore
  have hrs : (3 : ℝ) ^ n / (2 * (3 : ℝ) ^ N) = (3 : ℝ) ^ ((n : ℤ) - N) / 2 := by
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
    simp only [zpow_natCast]
    ring
  have hrm : (3 : ℝ) ^ (N - k + 1) / (2 * (3 : ℝ) ^ N) = 3 * ((3 : ℝ) ^ (-(k : ℤ)) / 2) := by
    rw [h3m]
    field_simp
  have hlevel : (N : ℤ) - (N - k + 1 : ℕ) = (k : ℤ) - 1 := by omega
  rw [hrs, hrm, hlevel] at hcore
  have hEnn : ∀ S : Set (SpatialCoordinates d), MeasurableSet S →
      0 ≤ aux_rem_resolved_meshes_energy a u S := fun S hS => by
    rw [aux_rem_resolved_meshes_energy_local a u S hS]
    exact localGradientEnergy_nonneg _ _ _
  have hm : ((N - k + 1 : ℕ) : ℝ) = (N : ℝ) - k + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hkN, Nat.cast_one]
  have hG0 : 0 ≤ halfHolderSeminorm (centeredCube ((3 : ℝ) ^ N •
      aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ (N - k + 1)) hR : Set (SpatialCoordinates d)) g :=
    aux_prop_folded_iteration_halfHolder_nonneg _ _
  have ht0 : 0 ≤ t := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [ht1, hdR]
  have hh := aux_rem_resolved_meshes_final_arith d t (1 - ((d : ℝ) - t) / 2) (by ring) ht0
    n (N - k + 1) N k I.card hm Cf Ch 1
    (aux_in_deterministic_onestep_sref M H omega N ((k : ℤ) - 1) (aux_rem_resolved_meshes_center y I))
    Kf (aux_rem_resolved_meshes_energy a u
      (Metric.ball (aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ ((n : ℤ) - N) / 2)))
    (aux_rem_resolved_meshes_energy a u
      (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-(k : ℤ)) / 2))))
    (halfHolderSeminorm (centeredCube ((3 : ℝ) ^ N • aux_rem_resolved_meshes_center y I)
      ((3 : ℝ) ^ (N - k + 1)) hR : Set (SpatialCoordinates d)) g)
    hCf.le hCh zero_lt_one (aux_in_deterministic_onestep_sref_pos M H omega N _ _)
    hKf (hEnn _ measurableSet_ball) (hEnn _ measurableSet_ball) hG0 ?_ ?_
  · simpa only [one_mul] using hh
  · simpa only [inv_one, mul_one, zpow_natCast, sub_sub_cancel, Real.sqrt_inv, mul_assoc] using hcore
  · simpa only [one_mul, zpow_natCast] using hGb

end SubdiffusiveProcess.Paper
