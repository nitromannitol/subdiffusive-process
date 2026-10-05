module

public import SubdiffusiveProcess.CoarseGrainingVocab.AhomCharacterization
public import SubdiffusiveProcess.CoarseGrainingVocab.ReciprocalLowerSupport

@[expose] public section

/-!
# Planar self-duality support

This file formalizes the algebraic and probabilistic part of the proof of
`p.special.two.d.exact.formula` : the normalization
`lambda_m`, reciprocal truncation, and the self-duality in law inherited from
(G3).  The analytic Dykhne formula and the degenerate stationary-corrector
limit are deliberately outside this file; neither theorem is presently in the
CoarseGraining library.

The independent-coordinate law transport uses the product-measure argument.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open Filter MeasureTheory ProbabilityTheory Homogenization
open scoped Matrix.Norms.Elementwise

noncomputable section

private abbrev Sample (d : ℕ) := _root_.SubdiffusiveProcess.Model.PotentialSample d
private abbrev Field (d : ℕ) := _root_.SubdiffusiveProcess.Model.PotentialField d

/-- The paper's normalization
`lambda_m = exp (-(m+1) tau^2)`. -/
noncomputable def planarLambda (M : _root_.SubdiffusiveProcess.Model.GMCModel 2)
    (m : ℕ) : ℝ :=
  Real.exp (-(m + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)

theorem planarLambda_pos (M : _root_.SubdiffusiveProcess.Model.GMCModel 2) (m : ℕ) :
    0 < planarLambda M m := by
  exact Real.exp_pos _

theorem planarLambda_ne_zero (M : _root_.SubdiffusiveProcess.Model.GMCModel 2) (m : ℕ) :
    planarLambda M m ≠ 0 :=
  (planarLambda_pos M m).ne'

theorem planarLambda_sq (M : _root_.SubdiffusiveProcess.Model.GMCModel 2) (m : ℕ) :
    planarLambda M m ^ 2 =
      Real.exp (-2 * (m + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) := by
  rw [planarLambda, pow_two, ← Real.exp_add]
  congr 1
  ring

/-- Symmetric reciprocal truncation `min N (max N⁻¹ t)`. -/
def planarSymmetricClip (N t : ℝ) : ℝ :=
  min N (max N⁻¹ t)

/-- The uniformly elliptic truncation `a_m^(N)`. -/
noncomputable def planarTruncatedCutoff
    (M : _root_.SubdiffusiveProcess.Model.GMCModel 2) (m : ℕ) (N : ℝ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample 2) (x : Vec 2) : ℝ :=
  planarLambda M m *
    planarSymmetricClip N
      (_root_.SubdiffusiveProcess.Model.aCutoff M m omega x / planarLambda M m)

theorem planarSymmetricClip_inv {N t : ℝ} (hN : 1 ≤ N) (ht : 0 < t) :
    planarSymmetricClip N t⁻¹ = (planarSymmetricClip N t)⁻¹ := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hNinvpos : 0 < N⁻¹ := inv_pos.mpr hNpos
  have hNinv_le_N : N⁻¹ ≤ N := by
    exact (inv_le_one₀ hNpos).mpr hN |>.trans hN
  by_cases hlo : t < N⁻¹
  · have htinv : N < t⁻¹ := by
      simpa [hNpos.ne'] using (inv_lt_inv₀ hNinvpos ht).mpr hlo
    simp only [planarSymmetricClip]
    rw [max_eq_right (hNinv_le_N.trans (le_of_lt htinv)),
      min_eq_left (le_of_lt htinv)]
    rw [max_eq_left (le_of_lt hlo), min_eq_right hNinv_le_N]
    simp
  · have hlo' : N⁻¹ ≤ t := le_of_not_gt hlo
    by_cases hhi : N < t
    · have htinv : t⁻¹ < N⁻¹ := (inv_lt_inv₀ ht hNpos).mpr hhi
      simp only [planarSymmetricClip]
      rw [max_eq_left (le_of_lt htinv), min_eq_right hNinv_le_N]
      rw [max_eq_right hlo', min_eq_left (le_of_lt hhi)]
    · have hhi' : t ≤ N := le_of_not_gt hhi
      have htinv_le_N : t⁻¹ ≤ N := by
        exact (inv_le_comm₀ ht hNpos).mpr hlo'
      have hNinv_le_tinv : N⁻¹ ≤ t⁻¹ :=
        (inv_le_inv₀ hNpos ht).mpr hhi'
      simp only [planarSymmetricClip]
      rw [max_eq_right hlo', min_eq_right hhi']
      rw [max_eq_right hNinv_le_tinv, min_eq_right htinv_le_N]

theorem planarSymmetricClip_lower {N t : ℝ} (hN : 1 ≤ N) (_ht : 0 < t) :
    N⁻¹ ≤ planarSymmetricClip N t := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hNinv_le_N : N⁻¹ ≤ N := by
    exact (inv_le_one₀ hNpos).mpr hN |>.trans hN
  exact le_min hNinv_le_N (le_max_left _ _)

theorem planarSymmetricClip_upper (N t : ℝ) :
    planarSymmetricClip N t ≤ N :=
  min_le_left _ _

theorem planarSymmetricClip_pos {N t : ℝ} (hN : 1 ≤ N) (ht : 0 < t) :
    0 < planarSymmetricClip N t :=
  lt_of_lt_of_le (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hN))
    (planarSymmetricClip_lower hN ht)

theorem planarTruncatedCutoff_pos
    (M : _root_.SubdiffusiveProcess.Model.GMCModel 2) (m : ℕ) {N : ℝ}
    (hN : 1 ≤ N) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample 2) (x : Vec 2) :
    0 < planarTruncatedCutoff M m N omega x := by
  apply mul_pos (planarLambda_pos M m)
  apply planarSymmetricClip_pos hN
  exact div_pos (_root_.SubdiffusiveProcess.Model.aCutoff_pos M m omega x)
    (planarLambda_pos M m)

theorem planarTruncatedCutoff_lower
    (M : _root_.SubdiffusiveProcess.Model.GMCModel 2) (m : ℕ) {N : ℝ}
    (hN : 1 ≤ N) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample 2) (x : Vec 2) :
    planarLambda M m * N⁻¹ ≤ planarTruncatedCutoff M m N omega x := by
  exact mul_le_mul_of_nonneg_left
    (planarSymmetricClip_lower hN
      (div_pos (_root_.SubdiffusiveProcess.Model.aCutoff_pos M m omega x)
        (planarLambda_pos M m)))
    (planarLambda_pos M m).le

theorem planarTruncatedCutoff_upper
    (M : _root_.SubdiffusiveProcess.Model.GMCModel 2) (m : ℕ) (N : ℝ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample 2) (x : Vec 2) :
    planarTruncatedCutoff M m N omega x ≤ planarLambda M m * N := by
  exact mul_le_mul_of_nonneg_left (planarSymmetricClip_upper N _)
    (planarLambda_pos M m).le

theorem continuous_planarTruncatedCutoff
    (M : _root_.SubdiffusiveProcess.Model.GMCModel 2) (m : ℕ) (N : ℝ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample 2) :
    Continuous (planarTruncatedCutoff M m N omega) := by
  exact continuous_const.mul
    (continuous_const.min
      (continuous_const.max
        ((_root_.SubdiffusiveProcess.Model.continuous_aCutoff M m omega).div
          continuous_const (fun _ => planarLambda_ne_zero M m))))

/-- The truncation packaged as an explicitly uniformly elliptic coefficient
on any public bounded domain. -/
noncomputable def planarTruncatedCoeffOnData
    (M : _root_.SubdiffusiveProcess.Model.GMCModel 2) (m : ℕ) (N : ℝ)
    (hN : 1 ≤ N) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample 2) (U : Homogenization.Book.Ch02.Domain 2) :
    ScalarCoeffOnData U (planarTruncatedCutoff M m N omega) where
  lam := planarLambda M m * N⁻¹
  Lam := planarLambda M m * N
  lam_pos := mul_pos (planarLambda_pos M m)
    (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hN))
  lam_le_Lam := mul_le_mul_of_nonneg_left
    (((inv_le_one₀ (lt_of_lt_of_le zero_lt_one hN)).mpr hN).trans hN)
    (planarLambda_pos M m).le
  aeStronglyMeasurable := by
    intro i j
    have hcont : Continuous (fun x : Vec 2 =>
        Homogenization.scalarMatrix (d := 2)
          (planarTruncatedCutoff M m N omega x)) :=
      (continuous_planarTruncatedCutoff M m N omega).smul continuous_const
    have hentry : Continuous (fun x : Vec 2 =>
        Homogenization.scalarMatrix (d := 2)
          (planarTruncatedCutoff M m N omega x) i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp hcont)
    have hmeas : AEStronglyMeasurable
        (fun x : Vec 2 => Homogenization.scalarMatrix (d := 2)
          (planarTruncatedCutoff M m N omega x) i j)
        (Homogenization.volumeMeasureOn (U : Set (Vec 2))) :=
      hentry.aestronglyMeasurable
    have hmem : ∀ᵐ x ∂ Homogenization.volumeMeasureOn (U : Set (Vec 2)),
        x ∈ (U : Set (Vec 2)) :=
      MeasureTheory.ae_restrict_mem U.measurableSet
    refine hmeas.congr ?_
    filter_upwards [hmem] with x hx
    simp only [scalarCoeffField,
      Homogenization.restrictCoeffField_apply_of_mem hx]
  aeBounds := Eventually.of_forall fun x =>
    ⟨planarTruncatedCutoff_lower M m hN omega x,
      planarTruncatedCutoff_upper M m N omega x⟩

/-- Finite-volume primal coarse matrix for the truncated coefficient. -/
noncomputable def planarTruncatedRandomAMatrix
    (M : _root_.SubdiffusiveProcess.Model.GMCModel 2) (m : ℕ) (N : ℝ)
    (hN : 1 ≤ N) (U : Homogenization.Book.Ch02.Domain 2)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample 2) : Mat 2 :=
  aMatrix U (planarTruncatedCoeffOnData M m N hN omega U).toCoeffOn

/-- Annealed finite-volume primal coarse matrix for the truncation.  This is
the concrete target used by the Dykhne SHAPE-CHECK boundary. -/
noncomputable def planarTruncatedAbar
    (M : _root_.SubdiffusiveProcess.Model.GMCModel 2) (m : ℕ) (N : ℝ)
    (hN : 1 ≤ N) (U : Homogenization.Book.Ch02.Domain 2) : Mat 2 :=
  ∫ omega, planarTruncatedRandomAMatrix M m N hN U omega ∂M.P.toMeasure

/-- Componentwise signed-coordinate rotation of the shell sequence. -/
def rotatePotentialSample {d : ℕ} (R : Mat d)
    (hR : IsSignedPermutationMatrix R) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : _root_.SubdiffusiveProcess.Model.PotentialSample d :=
  fun k => _root_.SubdiffusiveProcess.Model.PotentialField.rotate R hR (omega k)

theorem measurable_rotatePotentialSample {d : ℕ} (R : Mat d)
    (hR : IsSignedPermutationMatrix R) :
    Measurable (rotatePotentialSample (d := d) R hR) := by
  apply measurable_pi_iff.mpr
  intro k
  exact (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_rotate R hR).comp
    (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate k)

private theorem rotate_triadicScale {d : ℕ} (R : Mat d)
    (hR : IsSignedPermutationMatrix R) (k : ℕ) (g : _root_.SubdiffusiveProcess.Model.PotentialField d) :
    _root_.SubdiffusiveProcess.Model.PotentialField.rotate R hR
        (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k g) =
      _root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k
        (_root_.SubdiffusiveProcess.Model.PotentialField.rotate R hR g) := by
  apply _root_.SubdiffusiveProcess.Model.PotentialField.ext
  intro x
  simp [matVecMul_smul]

private theorem potentialMarginalLaw_rotation {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (k : ℕ) (R : Mat d)
    (hR : IsSignedPermutationMatrix R) :
    Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.rotate R hR)
        (_root_.SubdiffusiveProcess.Model.potentialMarginalLaw M.P k).toMeasure =
      (_root_.SubdiffusiveProcess.Model.potentialMarginalLaw M.P k).toMeasure := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d099_potentialMarginalLaw_isotropic (d := d) (M := M) (k := k) (R := R) (hR := hR)

--  product-law uniqueness mirrors

theorem potentialSequenceLaw_rotation {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (R : Mat d)
    (hR : IsSignedPermutationMatrix R) :
    Measure.map (rotatePotentialSample (d := d) R hR) M.P.toMeasure =
      M.P.toMeasure := by
  have hprod := (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun k : ℕ => _root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate k)).mp
      M.shellPrefix.independent
  have hrotInd : iIndepFun
      (fun k : ℕ => fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        _root_.SubdiffusiveProcess.Model.PotentialField.rotate R hR (omega k)) M.P.toMeasure :=
    M.shellPrefix.independent.comp
      (fun _ => _root_.SubdiffusiveProcess.Model.PotentialField.rotate R hR)
      (fun _ => _root_.SubdiffusiveProcess.Model.PotentialField.measurable_rotate R hR)
  have hrotProd := (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun _ : ℕ =>
      (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_rotate R hR).comp
        (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate _))).mp hrotInd
  calc
    Measure.map (rotatePotentialSample (d := d) R hR) M.P.toMeasure =
      Measure.infinitePi (fun k : ℕ =>
        Measure.map (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
          _root_.SubdiffusiveProcess.Model.PotentialField.rotate R hR (omega k))
          M.P.toMeasure) := by
      simpa only [rotatePotentialSample, Function.comp_def] using! hrotProd
    _ = Measure.infinitePi (fun k : ℕ =>
        Measure.map (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => omega k) M.P.toMeasure) := by
      apply congrArg Measure.infinitePi
      funext k
      calc
        Measure.map (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
            _root_.SubdiffusiveProcess.Model.PotentialField.rotate R hR (omega k))
            M.P.toMeasure =
          Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.rotate R hR)
            (Measure.map (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => omega k) M.P.toMeasure) := by
            change Measure.map
              (_root_.SubdiffusiveProcess.Model.PotentialField.rotate R hR ∘
                fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => omega k) M.P.toMeasure = _
            rw [Measure.map_map
              (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_rotate R hR)
              (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate k)]
        _ = Measure.map (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => omega k) M.P.toMeasure :=
          potentialMarginalLaw_rotation M k R hR
    _ = Measure.map (fun omega (k : ℕ) => omega k) M.P.toMeasure := hprod.symm
    _ = M.P.toMeasure := Measure.map_id'

theorem aCutoff_rotatePotentialSample {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (R : Mat d)
    (hR : IsSignedPermutationMatrix R) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Vec d) :
    _root_.SubdiffusiveProcess.Model.aCutoff M m
        (rotatePotentialSample R hR omega) x =
      _root_.SubdiffusiveProcess.Model.aCutoff M m omega (matVecMul R x) := by
  simp [_root_.SubdiffusiveProcess.Model.aCutoff, rotatePotentialSample]

/-- The sample transformation representing planar reciprocal rotation. -/
def planarDualPotentialSample (R : Mat 2) (hR : IsSignedPermutationMatrix R)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample 2) : _root_.SubdiffusiveProcess.Model.PotentialSample 2 :=
  negatePotentialSequence (rotatePotentialSample R hR omega)

theorem measurable_planarDualPotentialSample (R : Mat 2)
    (hR : IsSignedPermutationMatrix R) :
    Measurable (planarDualPotentialSample R hR) :=
  measurable_negatePotentialSequence.comp (measurable_rotatePotentialSample R hR)

theorem potentialSequenceLaw_planarDual
    (M : _root_.SubdiffusiveProcess.Model.GMCModel 2) (R : Mat 2)
    (hR : IsSignedPermutationMatrix R) :
    Measure.map (planarDualPotentialSample R hR) M.P.toMeasure = M.P.toMeasure := by
  calc
    Measure.map (planarDualPotentialSample R hR) M.P.toMeasure =
      Measure.map negatePotentialSequence
        (Measure.map (rotatePotentialSample R hR) M.P.toMeasure) := by
          exact (Measure.map_map measurable_negatePotentialSequence
            (measurable_rotatePotentialSample R hR)).symm
    _ = Measure.map negatePotentialSequence M.P.toMeasure := by
      rw [potentialSequenceLaw_rotation M R hR]
    _ = M.P.toMeasure := potentialSequenceLaw_negation M

theorem aCutoff_planarDualPotentialSample
    (M : _root_.SubdiffusiveProcess.Model.GMCModel 2) (m : ℕ) (R : Mat 2)
    (hR : IsSignedPermutationMatrix R) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample 2) (x : Vec 2) :
    _root_.SubdiffusiveProcess.Model.aCutoff M m
        (planarDualPotentialSample R hR omega) x =
      planarLambda M m ^ 2 *
        (_root_.SubdiffusiveProcess.Model.aCutoff M m omega (matVecMul R x))⁻¹ := by
  rw [planarDualPotentialSample, aCutoff_negatePotentialSequence,
    aCutoff_rotatePotentialSample, planarLambda_sq]

theorem normalizedCutoff_planarDualPotentialSample
    (M : _root_.SubdiffusiveProcess.Model.GMCModel 2) (m : ℕ) (R : Mat 2)
    (hR : IsSignedPermutationMatrix R) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample 2) (x : Vec 2) :
    _root_.SubdiffusiveProcess.Model.aCutoff M m
        (planarDualPotentialSample R hR omega) x / planarLambda M m =
      (_root_.SubdiffusiveProcess.Model.aCutoff M m omega (matVecMul R x) /
        planarLambda M m)⁻¹ := by
  rw [aCutoff_planarDualPotentialSample]
  field_simp [planarLambda_ne_zero M m,
    (_root_.SubdiffusiveProcess.Model.aCutoff_pos M m omega (matVecMul R x)).ne']

theorem planarTruncatedCutoff_planarDualPotentialSample
    (M : _root_.SubdiffusiveProcess.Model.GMCModel 2) (m : ℕ) {N : ℝ}
    (hN : 1 ≤ N) (R : Mat 2) (hR : IsSignedPermutationMatrix R)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample 2) (x : Vec 2) :
    planarTruncatedCutoff M m N (planarDualPotentialSample R hR omega) x =
    planarLambda M m ^ 2 *
        (planarTruncatedCutoff M m N omega (matVecMul R x))⁻¹ := by
  have hclip : 0 < planarSymmetricClip N
      (_root_.SubdiffusiveProcess.Model.aCutoff M m omega (matVecMul R x) /
        planarLambda M m) :=
    planarSymmetricClip_pos hN
      (div_pos (_root_.SubdiffusiveProcess.Model.aCutoff_pos M m omega (matVecMul R x))
        (planarLambda_pos M m))
  rw [planarTruncatedCutoff, normalizedCutoff_planarDualPotentialSample,
    planarSymmetricClip_inv hN]
  · simp only [planarTruncatedCutoff]
    field_simp [planarLambda_ne_zero M m, hclip.ne']
  · exact div_pos
      (_root_.SubdiffusiveProcess.Model.aCutoff_pos M m omega (matVecMul R x))
      (planarLambda_pos M m)

theorem measurable_planarTruncatedCutoff
    (M : _root_.SubdiffusiveProcess.Model.GMCModel 2) (m : ℕ) (N : ℝ) :
    Measurable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample 2 => planarTruncatedCutoff M m N omega) := by
  apply Measurable.of_eval
  intro x
  exact measurable_const.mul
    (measurable_const.min
      (measurable_const.max
        ((_root_.SubdiffusiveProcess.Model.measurable_aCutoff M m x).div measurable_const)))

/-- The truncated coefficient has the full field-level self-duality in law.
This is the probabilistic input immediately preceding Dykhne's formula in the
paper. -/
theorem planarTruncatedCutoff_selfDual_law
    (M : _root_.SubdiffusiveProcess.Model.GMCModel 2) (m : ℕ) {N : ℝ}
    (hN : 1 ≤ N) (R : Mat 2) (hR : IsSignedPermutationMatrix R) :
    Measure.map (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample 2 => planarTruncatedCutoff M m N omega)
        M.P.toMeasure =
      Measure.map (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample 2 => fun x : Vec 2 =>
        planarLambda M m ^ 2 *
          (planarTruncatedCutoff M m N omega (matVecMul R x))⁻¹)
        M.P.toMeasure := by
  let F : _root_.SubdiffusiveProcess.Model.PotentialSample 2 → (Vec 2 → ℝ) :=
    fun omega => planarTruncatedCutoff M m N omega
  let T : _root_.SubdiffusiveProcess.Model.PotentialSample 2 → _root_.SubdiffusiveProcess.Model.PotentialSample 2 := planarDualPotentialSample R hR
  have hF : Measurable F := measurable_planarTruncatedCutoff M m N
  calc
    Measure.map F M.P.toMeasure =
      Measure.map F (Measure.map T M.P.toMeasure) := by
        rw [potentialSequenceLaw_planarDual M R hR]
    _ = Measure.map (F ∘ T) M.P.toMeasure :=
      Measure.map_map hF (measurable_planarDualPotentialSample R hR)
    _ = Measure.map (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample 2 => fun x : Vec 2 =>
        planarLambda M m ^ 2 *
          (planarTruncatedCutoff M m N omega (matVecMul R x))⁻¹)
        M.P.toMeasure := by
      apply congrArg (fun f : _root_.SubdiffusiveProcess.Model.PotentialSample 2 → (Vec 2 → ℝ) =>
        Measure.map f M.P.toMeasure)
      funext omega x
      exact planarTruncatedCutoff_planarDualPotentialSample
        M m hN R hR omega x

/-- The quarter-turn matrix `[[0,1],[-1,0]]`, represented in the signed
permutation convention used by `Homogenization`. -/
def planarQuarterTurn : Mat 2 :=
  fun i j =>
    if i = Equiv.swap (0 : Fin 2) 1 j then
      if j = 0 then -1 else 1
    else 0

theorem planarQuarterTurn_entries :
    planarQuarterTurn 0 0 = 0 ∧
    planarQuarterTurn 0 1 = 1 ∧
    planarQuarterTurn 1 0 = -1 ∧
    planarQuarterTurn 1 1 = 0 := by
  simp [planarQuarterTurn]

theorem planarQuarterTurn_isSignedPermutation :
    IsSignedPermutationMatrix planarQuarterTurn := by
  refine ⟨Equiv.swap (0 : Fin 2) 1,
    fun j => if j = 0 then -1 else 1, ?_, ?_⟩
  · intro j
    by_cases hj : j = 0
    · simp [hj]
    · simp [hj]
  · intro i j
    rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab
