import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Main.ChaosSampleLaw
import Homogenization.Book.Ch02.Matrices
import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Localization
import SubdiffusiveProcess.CoarseGrainingVocab.HomogenizationError
import SubdiffusiveProcess.Paper.lem_prefix_limit_g9_cell_compact
import SubdiffusiveProcess.Paper.lem_prefix_limit_g9_cell_moment
import SubdiffusiveProcess.Paper.lem_prefix_limit_g9_series_compact
import SubdiffusiveProcess.Paper.lem_prefix_limit_g9_inv_compact

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

noncomputable section
namespace Paper

abbrev aux_lem_prefix_limit_g9_unit_chart_compact_D {d : ℕ} (n : ℕ) :
    Finset (Homogenization.TriadicCube d) :=
  Homogenization.descendantsAtScale (Homogenization.originCube d 0)
    ((Homogenization.originCube d 0).scale - (n : ℤ))

theorem aux_lem_prefix_limit_g9_unit_chart_compact_D_nonempty {d : ℕ} (n : ℕ) :
    (aux_lem_prefix_limit_g9_unit_chart_compact_D (d := d) n).Nonempty := by
  apply Homogenization.descendantsAtScale_nonempty
  simp [aux_lem_prefix_limit_g9_unit_chart_compact_D, Homogenization.originCube]

theorem aux_lem_prefix_limit_g9_unit_chart_compact_D_card {d : ℕ} (n : ℕ) :
    ((aux_lem_prefix_limit_g9_unit_chart_compact_D (d := d) n).card : ℝ) ≤
      (3 : ℝ) ^ ((d : ℝ) * (n : ℝ)) := by
  rw [show aux_lem_prefix_limit_g9_unit_chart_compact_D (d := d) n =
      Homogenization.descendantsAtDepth (Homogenization.originCube d 0) n by
        unfold aux_lem_prefix_limit_g9_unit_chart_compact_D
        rw [Homogenization.descendantsAtScale_eq_descendantsAtDepth]
        · simp [Homogenization.originCube]
        · simp [Homogenization.originCube]]
  have h := Homogenization.descendantsAtDepth_card (Homogenization.originCube d 0) n
  rw [h]
  norm_num [Nat.cast_pow, ← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]

theorem aux_lem_prefix_limit_g9_unit_chart_compact_weight_card_exp
    {d : ℕ} (D : ℕ → Finset (Homogenization.TriadicCube d))
    (hcard : ∀ n, ((D n).card : ℝ) ≤ (3 : ℝ) ^ ((d : ℝ) * (n : ℝ)))
    (t q C A delta : ℝ) (ht : 0 < t) (hq : 0 < q) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hgap : A * delta ^ 2 < (2 * t - d / q) * Real.log 3) :
    Summable (fun n => Homogenization.Book.Ch02.geometricWeight t 2 n *
      ((D n).card : ℝ) ^ (1 / q) * (C * Real.exp (A * delta ^ 2 * (n : ℝ)))) := by
  have hlog : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hq' : 0 < q := hq
  have ha : d / q + A * delta ^ 2 / Real.log 3 < 2 * t := by
    have hAdiv : A * delta ^ 2 / Real.log 3 < 2 * t - d / q :=
      (div_lt_iff₀ hlog).2 hgap
    linarith
  have hbase := SubdiffusiveProcess.CoarseGrainingVocab.summable_geometricWeight_mul_shifted_rpow
    (s := 2 * t) (a := d / q + A * delta ^ 2 / Real.log 3) (A := C) 0 ha
  refine Summable.of_nonneg_of_le ?_ ?_ hbase
  · intro n
    have hw : 0 ≤ Homogenization.Book.Ch02.geometricWeight t 2 n := by
      rw [Homogenization.Book.Ch02.geometricWeight_eq_old]
      exact Homogenization.geometricWeight_nonneg n (by positivity)
    have hc : 0 ≤ ((D n).card : ℝ) ^ (1 / q) := by positivity
    have he : 0 ≤ C * Real.exp (A * delta ^ 2 * (n : ℝ)) := by positivity
    positivity
  · intro n
    have hweight : Homogenization.Book.Ch02.geometricWeight t 2 n =
        Homogenization.Book.Ch02.geometricWeight (2 * t) 1 n := by
      rw [Homogenization.Book.Ch02.geometricWeight_eq_old,
        Homogenization.Book.Ch02.geometricWeight_eq_old]
      convert Homogenization.geometricWeight_eq_mul_one t 2 n using 1 <;> ring
    have hcardpow : ((D n).card : ℝ) ^ (1 / q) ≤
        (3 : ℝ) ^ ((d / q) * (n : ℝ)) := by
      have hc : (D n).card ≤ (3 : ℝ) ^ ((d : ℝ) * (n : ℝ)) := hcard n
      have hpow := Real.rpow_le_rpow (by positivity) hc (by positivity : 0 ≤ (1 / q : ℝ))
      rw [← Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ))] at hpow
      convert hpow using 1 <;> ring
    have hexp : Real.exp (A * delta ^ 2 * (n : ℝ)) =
        (3 : ℝ) ^ ((A * delta ^ 2 / Real.log 3) * (n : ℝ)) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
      congr 1
      field_simp
    rw [hweight, hexp]
    calc
      Homogenization.Book.Ch02.geometricWeight (2 * t) 1 n *
          ((D n).card : ℝ) ^ (1 / q) *
          (C * (3 : ℝ) ^ ((A * delta ^ 2 / Real.log 3) * (n : ℝ))) ≤
        Homogenization.Book.Ch02.geometricWeight (2 * t) 1 n *
          (3 : ℝ) ^ ((d / q) * (n : ℝ)) *
          (C * (3 : ℝ) ^ ((A * delta ^ 2 / Real.log 3) * (n : ℝ))) := by
            have hgw : 0 ≤ Homogenization.Book.Ch02.geometricWeight (2 * t) 1 n := by
              rw [Homogenization.Book.Ch02.geometricWeight_eq_old]
              exact Homogenization.geometricWeight_nonneg n (by positivity)
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hcardpow hgw) (by positivity)
      _ = Homogenization.Book.Ch02.geometricWeight (2 * t) 1 n *
          (C * (3 : ℝ) ^ ((d / q + A * delta ^ 2 / Real.log 3) * (n : ℝ))) := by
            have hp : (3 : ℝ) ^ ((d / q) * (n : ℝ)) *
                (3 : ℝ) ^ ((A * delta ^ 2 / Real.log 3) * (n : ℝ)) =
                (3 : ℝ) ^ ((d / q + A * delta ^ 2 / Real.log 3) * (n : ℝ)) := by
              rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
              congr 1
              ring
            calc
              Homogenization.Book.Ch02.geometricWeight (2 * t) 1 n *
                  (3 : ℝ) ^ ((d / q) * (n : ℝ)) *
                  (C * (3 : ℝ) ^ ((A * delta ^ 2 / Real.log 3) * (n : ℝ))) =
                Homogenization.Book.Ch02.geometricWeight (2 * t) 1 n * C *
                  ((3 : ℝ) ^ ((d / q) * (n : ℝ)) *
                    (3 : ℝ) ^ ((A * delta ^ 2 / Real.log 3) * (n : ℝ))) := by ring
              _ = _ := by rw [hp]; ring
    norm_num

theorem aux_lem_prefix_limit_g9_unit_chart_compact_lam_inv_eq
    {d : ℕ} (sigma : ℝ) (F : Homogenization.Book.Ch02.TriadicCoeffFamily d) :
    (Homogenization.Book.Ch02.lambdaSq (Homogenization.originCube d 0) sigma
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) F)⁻¹ =
      ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight sigma 2 n *
        (aux_lem_prefix_limit_g9_unit_chart_compact_D (d := d) n).sup'
          (aux_lem_prefix_limit_g9_unit_chart_compact_D_nonempty n)
          (fun R => Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R F) := by
  unfold Homogenization.Book.Ch02.lambdaSq Homogenization.Book.Ch02.lambdaSqFinite
  have h22 : (2 : ℝ) / 2 = 1 := by norm_num
  simp only [h22, Real.rpow_eq_pow, Real.rpow_one, Real.rpow_neg_one, inv_inv]
  refine tsum_congr (fun n => ?_)
  congr 1
  unfold Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
    Homogenization.Book.Ch02.finsetSupReal
  rw [Finset.sup'_eq_csSup_image]

theorem aux_lem_prefix_limit_g9_unit_chart_compact_Lam_eq
    {d : ℕ} (sigma : ℝ) (F : Homogenization.Book.Ch02.TriadicCoeffFamily d) :
    Homogenization.Book.Ch02.LambdaSq (Homogenization.originCube d 0) sigma
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) F =
      ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight sigma 2 n *
        (aux_lem_prefix_limit_g9_unit_chart_compact_D (d := d) n).sup'
          (aux_lem_prefix_limit_g9_unit_chart_compact_D_nonempty n)
          (fun R => Homogenization.Book.Ch02.coarseBMatrixNorm R F) := by
  unfold Homogenization.Book.Ch02.LambdaSq Homogenization.Book.Ch02.LambdaSqFinite
  have h22 : (2 : ℝ) / 2 = 1 := by norm_num
  simp only [h22, Real.rpow_eq_pow, Real.rpow_one]
  refine tsum_congr (fun n => ?_)
  congr 1
  unfold Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale
    Homogenization.Book.Ch02.finsetSupReal
  rw [Finset.sup'_eq_csSup_image]

theorem aux_lem_prefix_limit_g9_unit_chart_compact_iSup_toReal_eq_sup'
    {ι : Type*} (D : Finset ι) (hD : D.Nonempty) (f : ι → ℝ≥0∞)
    (hf : ∀ i ∈ D, f i ≠ ⊤) :
    (⨆ R : {R : ι // R ∈ D}, f R).toReal =
      D.sup' hD (fun R => (f R).toReal) := by
  rw [ENNReal.toReal_iSup (f := fun R : {R : ι // R ∈ D} => f R)
      (fun R => hf R.1 R.2), Finset.sup'_eq_csSup_image]
  show sSup (Set.range fun R : {R : ι // R ∈ D} => (f R).toReal) = _
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_image, Finset.mem_coe, Subtype.exists]
  constructor
  · rintro ⟨R, hR, rfl⟩
    exact ⟨R, hR, rfl⟩
  · rintro ⟨R, hR, rfl⟩
    exact ⟨R, hR, rfl⟩

theorem aux_lem_prefix_limit_g9_unit_chart_compact_err_eq
    {d : ℕ} (s : ℝ) (hs : 0 < s)
    (F : Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (hfin : SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite
      (Homogenization.originCube d 0) 0 s
      Homogenization.Book.Ch02.MultiscaleExponent.infinity 2 F 1 < ⊤) :
    (SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite
      (Homogenization.originCube d 0) 0 s
      Homogenization.Book.Ch02.MultiscaleExponent.infinity 2 F 1).toReal =
      Real.sqrt (∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight s 2 n *
        (aux_lem_prefix_limit_g9_unit_chart_compact_D (d := d) n).sup'
          (aux_lem_prefix_limit_g9_unit_chart_compact_D_nonempty n)
          (fun R =>
            (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R F 1).toReal)) := by
  set M : ℕ → ℝ≥0∞ := fun l => ⨆ R : {R : Homogenization.TriadicCube d //
      R ∈ aux_lem_prefix_limit_g9_unit_chart_compact_D (d := d) l},
      SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax (R : Homogenization.TriadicCube d) F 1
    with hM
  set T : ℕ → ℝ≥0∞ := fun l =>
    ENNReal.ofReal (Homogenization.Book.Ch02.geometricWeight s 2 l) * M l with hT
  have hE : SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite
      (Homogenization.originCube d 0) 0 s
      Homogenization.Book.Ch02.MultiscaleExponent.infinity 2 F 1 =
      (∑' l, T l) ^ (1 / (2 : ℝ)) := by
    unfold SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite
      SubdiffusiveProcess.CoarseGrainingVocab.paperScaleResponseAtScale
      SubdiffusiveProcess.CoarseGrainingVocab.paperMaxDescendantProbeAtScale
    dsimp only
    congr 1
    refine tsum_congr (fun l => ?_)
    simp only [hT, hM]
    congr 1
    rw [← ENNReal.rpow_mul]
    norm_num
    rfl
  have hS : ∑' l, T l ≠ ⊤ := by
    intro htop
    rw [hE, htop, ENNReal.top_rpow_of_pos (by norm_num)] at hfin
    exact lt_irrefl _ hfin
  have hTfin : ∀ l, T l ≠ ⊤ := fun l => ne_top_of_le_ne_top hS (ENNReal.le_tsum l)
  have hMfin : ∀ l, M l ≠ ⊤ := by
    intro l hMl
    have hTl := hTfin l
    simp only [hT] at hTl
    have hw : 0 < Homogenization.Book.Ch02.geometricWeight s 2 l := by
      rw [Homogenization.Book.Ch02.geometricWeight_eq_old]
      exact Homogenization.geometricWeight_pos l (by positivity)
    have hwo : ENNReal.ofReal (Homogenization.Book.Ch02.geometricWeight s 2 l) ≠ 0 := by
      exact (ENNReal.ofReal_pos.mpr hw).ne'
    rw [hMl, ENNReal.mul_top hwo] at hTl
    exact hTl rfl
  have hMreal : ∀ l,
      M l = ENNReal.ofReal ((aux_lem_prefix_limit_g9_unit_chart_compact_D (d := d) l).sup'
        (aux_lem_prefix_limit_g9_unit_chart_compact_D_nonempty l)
        (fun R => (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R F 1).toReal)) := by
    intro l
    have hi := aux_lem_prefix_limit_g9_unit_chart_compact_iSup_toReal_eq_sup'
      (aux_lem_prefix_limit_g9_unit_chart_compact_D (d := d) l)
      (aux_lem_prefix_limit_g9_unit_chart_compact_D_nonempty l)
      (fun R : Homogenization.TriadicCube d =>
        SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R F 1)
      (fun R hR => by
        intro htop
        apply hMfin l
        rw [hM]
        refine eq_top_iff.mpr ?_
        rw [← htop]
        exact le_iSup (fun R : {R : Homogenization.TriadicCube d //
          R ∈ aux_lem_prefix_limit_g9_unit_chart_compact_D (d := d) l} =>
          SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax
            (R : Homogenization.TriadicCube d) F 1) ⟨R, hR⟩)
    calc
      M l = ENNReal.ofReal (M l).toReal :=
        (ENNReal.ofReal_toReal (hMfin l)).symm
      _ = ENNReal.ofReal ((aux_lem_prefix_limit_g9_unit_chart_compact_D (d := d) l).sup'
          (aux_lem_prefix_limit_g9_unit_chart_compact_D_nonempty l)
          (fun R => (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R F 1).toReal) : ℝ) := by
        exact congrArg ENNReal.ofReal (by simpa [hM] using hi)
  have hTreal : ∀ l,
      T l = ENNReal.ofReal
        (Homogenization.Book.Ch02.geometricWeight s 2 l *
          (aux_lem_prefix_limit_g9_unit_chart_compact_D (d := d) l).sup'
            (aux_lem_prefix_limit_g9_unit_chart_compact_D_nonempty l)
            (fun R => (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R F 1).toReal)) := by
    intro l
    change ENNReal.ofReal (Homogenization.Book.Ch02.geometricWeight s 2 l) * M l = _
    rw [hMreal l, ← ENNReal.ofReal_mul]
    have hgw : 0 ≤ Homogenization.Book.Ch02.geometricWeight s 2 l := by
      rw [Homogenization.Book.Ch02.geometricWeight_eq_old]
      exact Homogenization.geometricWeight_nonneg l (by positivity)
    exact hgw
  rw [hE]
  have hsum_eq : (∑' l, T l) = ENNReal.ofReal
      (∑' l : ℕ, Homogenization.Book.Ch02.geometricWeight s 2 l *
        (aux_lem_prefix_limit_g9_unit_chart_compact_D (d := d) l).sup'
          (aux_lem_prefix_limit_g9_unit_chart_compact_D_nonempty l)
          (fun R => (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R F 1).toReal)) := by
    rw [show (fun l => T l) = fun l => ENNReal.ofReal
        (Homogenization.Book.Ch02.geometricWeight s 2 l *
          (aux_lem_prefix_limit_g9_unit_chart_compact_D (d := d) l).sup'
            (aux_lem_prefix_limit_g9_unit_chart_compact_D_nonempty l)
            (fun R => (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R F 1).toReal)) by
      funext l; exact hTreal l]
    symm
    apply ENNReal.ofReal_tsum_of_nonneg
    · intro l
      have hw : 0 ≤ Homogenization.Book.Ch02.geometricWeight s 2 l := by
        rw [Homogenization.Book.Ch02.geometricWeight_eq_old]
        exact Homogenization.geometricWeight_nonneg l (by positivity)
      obtain ⟨R, hR⟩ := aux_lem_prefix_limit_g9_unit_chart_compact_D_nonempty l
      have hsup : 0 ≤ (aux_lem_prefix_limit_g9_unit_chart_compact_D (d := d) l).sup'
          (aux_lem_prefix_limit_g9_unit_chart_compact_D_nonempty l)
          (fun R => (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R F 1).toReal) :=
        (show 0 ≤ (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R F 1).toReal from
          ENNReal.toReal_nonneg).trans
          (Finset.le_sup' (fun R =>
            (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R F 1).toReal) hR)
      exact mul_nonneg hw hsup
    · have hsumreal : Summable (fun l : ℕ =>
          Homogenization.Book.Ch02.geometricWeight s 2 l *
            (aux_lem_prefix_limit_g9_unit_chart_compact_D (d := d) l).sup'
              (aux_lem_prefix_limit_g9_unit_chart_compact_D_nonempty l)
              (fun R => (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R F 1).toReal)) := by
        have hst := ENNReal.summable_toReal hS
        apply hst.congr
        intro l
        rw [hTreal l]
        exact ENNReal.toReal_ofReal (by
          have hw : 0 ≤ Homogenization.Book.Ch02.geometricWeight s 2 l := by
            rw [Homogenization.Book.Ch02.geometricWeight_eq_old]
            exact Homogenization.geometricWeight_nonneg l (by positivity)
          obtain ⟨R, hR⟩ := aux_lem_prefix_limit_g9_unit_chart_compact_D_nonempty l
          have hsup : 0 ≤ (aux_lem_prefix_limit_g9_unit_chart_compact_D (d := d) l).sup'
              (aux_lem_prefix_limit_g9_unit_chart_compact_D_nonempty l)
              (fun R => (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R F 1).toReal) :=
            (show 0 ≤ (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R F 1).toReal from
              ENNReal.toReal_nonneg).trans
              (Finset.le_sup' (fun R =>
                (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R F 1).toReal) hR)
          exact mul_nonneg hw hsup)
      exact hsumreal
  rw [hsum_eq]
  have hnonneg : 0 ≤ ∑' l : ℕ, Homogenization.Book.Ch02.geometricWeight s 2 l *
        (aux_lem_prefix_limit_g9_unit_chart_compact_D (d := d) l).sup'
          (aux_lem_prefix_limit_g9_unit_chart_compact_D_nonempty l)
          (fun R => (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R F 1).toReal) := by
    exact tsum_nonneg (fun l => by
      have hw : 0 ≤ Homogenization.Book.Ch02.geometricWeight s 2 l := by
        rw [Homogenization.Book.Ch02.geometricWeight_eq_old]
        exact Homogenization.geometricWeight_nonneg l (by positivity)
      obtain ⟨R, hR⟩ := aux_lem_prefix_limit_g9_unit_chart_compact_D_nonempty l
      have hsup : 0 ≤ (aux_lem_prefix_limit_g9_unit_chart_compact_D (d := d) l).sup'
          (aux_lem_prefix_limit_g9_unit_chart_compact_D_nonempty l)
          (fun R => (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R F 1).toReal) :=
        (show 0 ≤ (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R F 1).toReal from
          ENNReal.toReal_nonneg).trans
          (Finset.le_sup' (fun R =>
            (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R F 1).toReal) hR)
      exact mul_nonneg hw hsup)
  have hrpow : (ENNReal.ofReal (∑' l : ℕ, Homogenization.Book.Ch02.geometricWeight s 2 l *
        (aux_lem_prefix_limit_g9_unit_chart_compact_D (d := d) l).sup'
          (aux_lem_prefix_limit_g9_unit_chart_compact_D_nonempty l)
          (fun R => (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R F 1).toReal))) ^
        (1 / (2 : ℝ)) =
      ENNReal.ofReal ((∑' l : ℕ, Homogenization.Book.Ch02.geometricWeight s 2 l *
        (aux_lem_prefix_limit_g9_unit_chart_compact_D (d := d) l).sup'
          (aux_lem_prefix_limit_g9_unit_chart_compact_D_nonempty l)
          (fun R => (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R F 1).toReal)) ^
        (1 / (2 : ℝ))) := by
    exact ENNReal.ofReal_rpow_of_nonneg hnonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [hrpow]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hnonneg _), Real.sqrt_eq_rpow]

theorem aux_lem_prefix_limit_g9_unit_chart_compact_sup_pow_le_sum
    {α : Type*} (s : Finset α) (hs : s.Nonempty) (f : α → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (q : ℝ) (hq : 0 ≤ q) :
    (s.sup' hs f) ^ q ≤ ∑ i ∈ s, |f i| ^ q := by
  obtain ⟨i, hi, hfi⟩ := Finset.exists_mem_eq_sup' hs f
  calc
    (s.sup' hs f) ^ q = f i ^ q := by rw [hfi]
    _ = |f i| ^ q := by rw [abs_of_nonneg (hf i hi)]
    _ ≤ ∑ j ∈ s, |f j| ^ q := by
      apply Finset.single_le_sum (f := fun j => |f j| ^ q)
      · intro j hj
        exact Real.rpow_nonneg (abs_nonneg _) q
      · exact hi

theorem aux_lem_prefix_limit_g9_unit_chart_compact_sup_lip
    {α : Type*} (s : Finset α) (hs : s.Nonempty) (f g : α → ℝ) :
    |s.sup' hs f - s.sup' hs g| ≤ ∑ i ∈ s, |f i - g i| := by
  have hsum_nonneg : 0 ≤ ∑ i ∈ s, |f i - g i| := by positivity
  have hsingle : ∀ i ∈ s, |f i - g i| ≤ ∑ j ∈ s, |f j - g j| := by
    intro i hi
    exact Finset.single_le_sum (fun j _ => abs_nonneg (f j - g j)) hi
  have hfg : ∀ i ∈ s, f i ≤ s.sup' hs g + ∑ j ∈ s, |f j - g j| := by
    intro i hi
    calc
      f i ≤ g i + |f i - g i| := by
        linarith [le_abs_self (f i - g i)]
      _ ≤ s.sup' hs g + ∑ j ∈ s, |f j - g j| := by
        gcongr
        · exact Finset.le_sup' g hi
        · exact hsingle i hi
  have hgf : ∀ i ∈ s, g i ≤ s.sup' hs f + ∑ j ∈ s, |f j - g j| := by
    intro i hi
    calc
      g i ≤ f i + |f i - g i| := by
        have h := le_abs_self (g i - f i)
        rw [abs_sub_comm] at h
        linarith
      _ ≤ s.sup' hs f + ∑ j ∈ s, |f j - g j| := by
        gcongr
        · exact Finset.le_sup' f hi
        · exact hsingle i hi
  have h1 : s.sup' hs f ≤ s.sup' hs g + ∑ i ∈ s, |f i - g i| :=
    Finset.sup'_le hs f hfg
  have h2 : s.sup' hs g ≤ s.sup' hs f + ∑ i ∈ s, |f i - g i| :=
    Finset.sup'_le hs g hgf
  rw [abs_le]
  constructor <;> linarith

theorem aux_lem_prefix_limit_g9_unit_chart_compact_aesm_sup'
    {Ω α : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : Finset α) (hs : s.Nonempty) (f : α → Ω → ℝ)
    (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun o => s.sup' hs (fun i => f i o)) μ := by
  classical
  let g : α → Ω → ℝ := fun i => if h : i ∈ s then (hf i h).mk (f i) else 0
  have hg : ∀ i ∈ s, Measurable (g i) := by
    intro i hi
    simp only [g, dif_pos hi]
    exact (hf i hi).stronglyMeasurable_mk.measurable
  refine ⟨fun o => s.sup' hs (fun i => g i o), ?_, ?_⟩
  · have hm : Measurable (s.sup' hs g) := Finset.measurable_sup' hs hg
    have heq : (fun o => s.sup' hs (fun i => g i o)) = s.sup' hs g := by
      funext o
      rw [Finset.sup'_apply]
    rw [heq]
    exact hm.stronglyMeasurable
  · have hall : ∀ᵐ o ∂μ, ∀ i ∈ s, f i o = g i o := by
      rw [Filter.eventually_all_finset]
      intro i hi
      have hmk := (hf i hi).ae_eq_mk
      filter_upwards [hmk] with o ho
      simp only [g, dif_pos hi]
      exact ho
    filter_upwards [hall] with o ho
    exact Finset.sup'_congr hs rfl (fun i hi => ho i hi)

theorem aux_lem_prefix_limit_g9_unit_chart_compact_max_series
    {Ω α : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : ℕ → Finset α) (hD : ∀ n, (D n).Nonempty)
    (V : ℕ → α → ℕ → Ω → ℝ) (hVnonneg : ∀ n a N ω, 0 ≤ V n a N ω)
    (w C : ℕ → ℝ) (q : ℝ) (hq : 1 < q)
    (hw : ∀ n, 0 ≤ w n)
    (hVm : ∀ n a, a ∈ D n → ∃ hm : ∀ N, MemLp (V n a N) 1 μ,
      IsCompact (closure (Set.range (fun N => (hm N).toLp (V n a N)))))
    (hVq : ∀ n a, a ∈ D n → ∀ N, eLpNorm (V n a N) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (C n))
    (hsum : Summable (fun n => w n * (D n).card ^ (1 / q) * C n)) :
    ∃ hm : ∀ N, MemLp
        (fun ω => ∑' n, w n * (D n).sup' (hD n) (fun a => V n a N ω)) 1 μ,
      IsCompact (closure (Set.range (fun N =>
        (hm N).toLp (fun ω => ∑' n, w n *
          (D n).sup' (hD n) (fun a => V n a N ω))))) := by
  let X : (n : ℕ) → {a // a ∈ D n} → ℕ → Ω → ℝ :=
    fun n a N ω => V n a.1 N ω
  let Y : ℕ → ℕ → Ω → ℝ := fun n N ω =>
    (D n).sup' (hD n) (fun a => V n a N ω)
  letI (n : ℕ) : Fintype {a // a ∈ D n} := inferInstance
  have hYm : ∀ n N, AEStronglyMeasurable (Y n N) μ := by
    intro n N
    simpa [Y] using aux_lem_prefix_limit_g9_unit_chart_compact_aesm_sup' μ
      (D n) (hD n) (fun a => V n a N)
      (fun a ha => (hVm n a ha).choose N |>.aestronglyMeasurable)
  have hYle : ∀ n N ω, |Y n N ω| ^ q ≤
      ∑ a, |X n a N ω| ^ q := by
    intro n N ω
    dsimp [X, Y]
    have h := aux_lem_prefix_limit_g9_unit_chart_compact_sup_pow_le_sum
      (D n) (hD n) (fun a => V n a N ω)
      (fun a ha => hVnonneg n a N ω) q (by linarith)
    change |(D n).sup' (hD n) (fun a => V n a N ω)| ^ q ≤
      ∑ a : {a // a ∈ D n}, |V n a.1 N ω| ^ q
    obtain ⟨i, hi⟩ := hD n
    rw [abs_of_nonneg ((hVnonneg n i N ω).trans
      (Finset.le_sup' (fun a => V n a N ω) hi))]
    rw [Finset.sum_coe_sort (D n) (fun i => |V n i N ω| ^ q)]
    exact h
  have hYlip : ∀ n N N' ω, |Y n N ω - Y n N' ω| ≤
      ∑ a, |X n a N ω - X n a N' ω| := by
    intro n N N' ω
    dsimp [X, Y]
    have h := aux_lem_prefix_limit_g9_unit_chart_compact_sup_lip (D n) (hD n)
      (fun a => V n a N ω) (fun a => V n a N' ω)
    change |(D n).sup' (hD n) (fun a => V n a N ω) -
        (D n).sup' (hD n) (fun a => V n a N' ω)| ≤
      ∑ a : {a // a ∈ D n}, |V n a.1 N ω - V n a.1 N' ω|
    rw [Finset.sum_coe_sort (D n)
      (fun i => |V n i N ω - V n i N' ω|)]
    exact h
  have hXq : ∀ n a N, eLpNorm (X n a N) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (C n) := by
    intro n a N
    exact hVq n a.1 a.2 N
  have hcomp : ∀ n a, ∃ hm : ∀ N, MemLp (X n a N) 1 μ,
      IsCompact (closure (Set.range fun N => (hm N).toLp (X n a N))) := by
    intro n a
    simpa [X] using hVm n a.1 a.2
  obtain ⟨hm, hcompact⟩ := lem_prefix_limit_g9_series_compact μ
    (fun n => {a // a ∈ D n}) X Y w C q hq
    hw hYm hYle hYlip hXq
      (by simpa [Fintype.card_coe] using hsum) hcomp
  refine ⟨hm, ?_⟩
  simpa [Y] using hcompact

theorem aux_lem_prefix_limit_g9_unit_chart_compact_D_subset {d : ℕ} (n : ℕ)
    (R : Homogenization.TriadicCube d)
    (hR : R ∈ aux_lem_prefix_limit_g9_unit_chart_compact_D (d := d) n) :
    Homogenization.openCubeSet R ⊆
      Homogenization.openCubeSet (Homogenization.originCube d 0) := by
  refine Homogenization.openCubeSet_subset_of_mem_descendantsAtScale ?_ hR
  simp [aux_lem_prefix_limit_g9_unit_chart_compact_D, Homogenization.originCube]

theorem aux_lem_prefix_limit_g9_unit_chart_compact_compact_congr
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : ℕ → Ω → ℝ)
    (hf : ∀ N, MemLp (f N) 1 μ)
    (hg : ∀ N, MemLp (g N) 1 μ)
    (hfg : ∀ N, f N = g N)
    (hc : IsCompact (closure (Set.range (fun N => (hf N).toLp (f N))))) :
    IsCompact (closure (Set.range (fun N => (hg N).toLp (g N)))) := by
  have heq : (Set.range (fun N => (hf N).toLp (f N))) =
      Set.range (fun N => (hg N).toLp (g N)) := by
    ext z
    constructor
    · rintro ⟨N, rfl⟩
      refine ⟨N, ?_⟩
      exact (MemLp.toLp_congr (hf N) (hg N)
        (Filter.Eventually.of_forall (fun x => congrFun (hfg N) x))).symm
    · rintro ⟨N, rfl⟩
      refine ⟨N, ?_⟩
      exact MemLp.toLp_congr (hf N) (hg N)
        (Filter.Eventually.of_forall (fun x => congrFun (hfg N) x))
  rw [heq] at hc
  exact hc

theorem aux_lem_prefix_limit_g9_unit_chart_compact_of_sqrt_dist
    {E : Type*} [PseudoMetricSpace E] [CompleteSpace E] (f g : ℕ → E)
    (hc : IsCompact (closure (Set.range f)))
    (hrel : ∀ n m, dist (g n) (g m) ≤ Real.sqrt (dist (f n) (f m))) :
    IsCompact (closure (Set.range g)) := by
  classical
  have htot : TotallyBounded (Set.range f) :=
    hc.totallyBounded.subset subset_closure
  refine TotallyBounded.isCompact_of_isClosed ?_ isClosed_closure
  rw [totallyBounded_closure, Metric.totallyBounded_iff]
  intro ε hε
  let δ : ℝ := (ε / 2) ^ 2
  have hδ : 0 < δ := sq_pos_of_pos (by linarith)
  obtain ⟨t, ht, htfinite, hcover⟩ :=
    Metric.finite_approx_of_totallyBounded htot δ hδ
  let k : E → ℕ := fun y => if hy : y ∈ Set.range f then Classical.choose hy else 0
  have hk : ∀ y, y ∈ t → f (k y) = y := by
    intro y hy
    dsimp [k]
    rw [dif_pos (ht hy)]
    exact Classical.choose_spec (ht hy)
  refine ⟨(fun y => g (k y)) '' t, htfinite.image _, ?_⟩
  intro z hz
  rcases hz with ⟨n, rfl⟩
  have hn : f n ∈ Set.range f := ⟨n, rfl⟩
  rcases Set.mem_iUnion₂.1 (hcover hn) with ⟨y, hy, hny⟩
  refine Set.mem_iUnion₂.2 ⟨g (k y), ⟨y, hy, rfl⟩, ?_⟩
  have hdist : dist (f n) (f (k y)) < δ := by simpa [hk y hy] using hny
  calc
    dist (g n) (g (k y)) ≤ Real.sqrt (dist (f n) (f (k y))) := hrel n (k y)
    _ < Real.sqrt δ := Real.sqrt_lt_sqrt dist_nonneg hdist
    _ = ε / 2 := by
      dsimp [δ]
      rw [Real.sqrt_sq_eq_abs, abs_of_pos (by linarith)]
    _ < ε := by linarith

theorem aux_lem_prefix_limit_g9_unit_chart_compact_sqrt_l1_dist
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f g : Ω → ℝ}
    (hf : MemLp f 1 μ) (hg : MemLp g 1 μ)
    (hsf : MemLp (fun x => Real.sqrt (f x)) 1 μ)
    (hsg : MemLp (fun x => Real.sqrt (g x)) 1 μ)
    (hfn : ∀ᵐ x ∂μ, 0 ≤ f x) (hgn : ∀ᵐ x ∂μ, 0 ≤ g x) :
    dist (hsf.toLp (fun x => Real.sqrt (f x)))
        (hsg.toLp (fun x => Real.sqrt (g x))) ≤
      Real.sqrt (dist (hf.toLp f) (hg.toLp g)) := by
  have hsqrt_diff : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt |a - b| := by
    intro a b ha hb
    apply Real.abs_le_sqrt
    by_cases hab : a ≤ b
    · have hsab : Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt hab
      have hprod : a ≤ Real.sqrt a * Real.sqrt b := by
        have hmul := mul_le_mul_of_nonneg_left hsab (Real.sqrt_nonneg a)
        nlinarith [Real.sq_sqrt ha]
      have hsq : (Real.sqrt a - Real.sqrt b) ^ 2 =
          a + b - 2 * (Real.sqrt a * Real.sqrt b) := by
        nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb]
      rw [hsq, abs_of_nonpos (sub_nonpos.mpr hab)]
      nlinarith
    · have hba : b ≤ a := le_of_not_ge hab
      have hsab : Real.sqrt b ≤ Real.sqrt a := Real.sqrt_le_sqrt hba
      have hprod : b ≤ Real.sqrt a * Real.sqrt b := by
        have hmul := mul_le_mul_of_nonneg_left hsab (Real.sqrt_nonneg b)
        nlinarith [Real.sq_sqrt hb]
      have hsq : (Real.sqrt a - Real.sqrt b) ^ 2 =
          a + b - 2 * (Real.sqrt a * Real.sqrt b) := by
        nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb]
      rw [hsq, abs_of_nonneg (sub_nonneg.mpr hba)]
      nlinarith
  have hpoint : ∀ᵐ x ∂μ,
      ‖Real.sqrt (f x) - Real.sqrt (g x)‖ ≤
        Real.sqrt ‖f x - g x‖ := by
    filter_upwards [hfn, hgn] with x hfx hgx
    simpa [Real.norm_eq_abs] using hsqrt_diff (f x) (g x) hfx hgx
  have hdiff : MemLp (fun x => f x - g x) 1 μ := hf.sub hg
  have hroot : MemLp (fun x => |f x - g x| ^ (1 / 2 : ℝ)) 2 μ := by
    simpa [Real.norm_eq_abs] using
      (hdiff.norm_rpow_div (q := ENNReal.ofReal (1 / 2 : ℝ)))
  have hrootmono : eLpNorm (fun x => Real.sqrt ‖f x - g x‖) 1 μ ≤
      eLpNorm (fun x => Real.sqrt ‖f x - g x‖) 2 μ := by
    apply eLpNorm_le_eLpNorm_of_exponent_le (f := fun x => Real.sqrt ‖f x - g x‖)
      (p := (1 : ENNReal)) (q := (2 : ENNReal)) (by norm_num)
    exact (hroot.1.congr (Filter.Eventually.of_forall (fun x => by
      simp [Real.sqrt_eq_rpow, Real.norm_eq_abs])))
  have hroot_eq : eLpNorm (fun x => Real.sqrt ‖f x - g x‖) 2 μ =
      eLpNorm (fun x => f x - g x) 1 μ ^ (1 / 2 : ℝ) := by
    rw [show (fun x => Real.sqrt ‖f x - g x‖) =
        (fun x => ‖f x - g x‖ ^ (1 / 2 : ℝ)) by
          funext x; rw [Real.sqrt_eq_rpow]]
    rw [eLpNorm_norm_rpow (f := fun x => f x - g x) (p := (2 : ENNReal))
      (q := (1 / 2 : ℝ)) (by norm_num)]
    rw [show (2 : ENNReal) * ENNReal.ofReal (1 / 2 : ℝ) = 1 by
      calc
        (2 : ENNReal) * ENNReal.ofReal (1 / 2 : ℝ) =
            ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal (1 / 2 : ℝ) := by norm_num
        _ = ENNReal.ofReal ((2 : ℝ) * (1 / 2 : ℝ)) :=
          (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)).symm
        _ = 1 := by norm_num]
  have hnorm : (eLpNorm (fun x => Real.sqrt (f x) - Real.sqrt (g x)) 1 μ).toReal ≤
      Real.sqrt (eLpNorm (fun x => f x - g x) 1 μ).toReal := by
    have hmono := eLpNorm_mono_ae_real (p := (1 : ENNReal)) hpoint
    have hle : eLpNorm (fun x => Real.sqrt (f x) - Real.sqrt (g x)) 1 μ ≤
        eLpNorm (fun x => Real.sqrt ‖f x - g x‖) 1 μ := hmono
    have hle' := hle.trans (hrootmono.trans_eq hroot_eq)
    have hfinite : eLpNorm (fun x => f x - g x) 1 μ ≠ ⊤ := hdiff.2.ne
    have hdiffsqrt : MemLp (fun x => Real.sqrt (f x) - Real.sqrt (g x)) 1 μ :=
      hsf.sub hsg
    have hrightlt : eLpNorm (fun x => f x - g x) 1 μ ^ (1 / 2 : ℝ) < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg (by norm_num) (by finiteness)
    have hreal := ENNReal.toReal_mono (ne_of_lt hrightlt) (hle')
    rw [← ENNReal.toReal_rpow] at hreal
    simpa [Real.sqrt_eq_rpow] using hreal
  rw [Lp.dist_def, Lp.dist_def]
  have hleft : eLpNorm (⇑(hsf.toLp (fun x => Real.sqrt (f x))) -
        ⇑(hsg.toLp (fun x => Real.sqrt (g x)))) 1 μ =
      eLpNorm (fun x => Real.sqrt (f x) - Real.sqrt (g x)) 1 μ := by
    apply eLpNorm_congr_ae
    filter_upwards [hsf.coeFn_toLp, hsg.coeFn_toLp] with x hxf hxg
    simp [Pi.sub_apply, hxf, hxg]
  have hright : eLpNorm (⇑(hf.toLp f) - ⇑(hg.toLp g)) 1 μ =
      eLpNorm (fun x => f x - g x) 1 μ := by
    apply eLpNorm_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hxf hxg
    simp [Pi.sub_apply, hxf, hxg]
  rw [hleft, hright]
  exact hnorm



theorem lem_prefix_limit_g9_unit_chart_compact {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (_Poincare : Paper.in_poincare d hd I)
    (_Extension : Paper.in_extension d hd I) (_Perturbation : Lane4.SmallPerturbationInput d)
    (_Sobolev : Lane4.SobolevFoundationalInput d hd)
    (D : Paper.lane4_deterministic_good_scale_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp) (sigma s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : Paper.in_6_16 d M) (_It : Paper.in_iteration d M I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      let F : ℕ → BilateralField d → Homogenization.Book.Ch02.TriadicCoeffFamily d :=
        fun K omega => I.chart 0 1 one_pos (Lane4.cutoffPositiveCoefficient M H omega K 0 one_pos) 0 1
      let uVal : ℕ → BilateralField d → Fin 3 ⊕ ((Bool × (Fin d × Fin d)) ⊕ Unit) → ℝ :=
        fun K omega rt =>
          Sum.elim
            (fun j => if j = 0 then
                Homogenization.Book.Ch02.lambdaSq (Homogenization.originCube d 0) sigma
                  (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) (F K omega)
              else if j = 1 then
                Homogenization.Book.Ch02.LambdaSq (Homogenization.originCube d 0) sigma
                  (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) (F K omega)
              else (Homogenization.Book.Ch02.lambdaSq (Homogenization.originCube d 0) sigma
                  (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) (F K omega))⁻¹)
            (Sum.elim
              (fun ab => if ab.1 then
                  Homogenization.Book.Ch02.sigmaCoarse
                    (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                    ((F K omega).coeffOn (Homogenization.originCube d 0)) ab.2.1 ab.2.2
                else Homogenization.Book.Ch02.sigmaStarInvCoarse
                    (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                    ((F K omega).coeffOn (Homogenization.originCube d 0)) ab.2.1 ab.2.2)
              (fun _ => (SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite
                  (Homogenization.originCube d 0) 0 s
                  Homogenization.Book.Ch02.MultiscaleExponent.infinity 2 (F K omega) 1).toReal)) rt
      ∀ rt : Fin 3 ⊕ ((Bool × (Fin d × Fin d)) ⊕ Unit),
        ∃ hmem : ∀ K, MemLp (uVal K · rt) 1 (chaosSampleLaw M).toMeasure,
          IsCompact (closure (Set.range (fun K => (hmem K).toLp (uVal K · rt)))) := by
  have ht : 0 < min sigma s := lt_min hsigma.1 hs.1
  let q : ℝ := max 2 ((d : ℝ) / min sigma s + 1)
  have hqpos : 0 < q := by
    dsimp [q]
    exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hq : 1 < q := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hqgap : (d : ℝ) / q < min sigma s := by
    have hqt : (d : ℝ) / min sigma s < q := by
      dsimp [q]
      exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
    apply (div_lt_iff₀ hqpos).2
    have hqmul : (d : ℝ) < q * min sigma s :=
      (div_lt_iff₀ ht).1 hqt
    nlinarith
  have hqgap' : (d : ℝ) / q < 2 * min sigma s := by linarith
  obtain ⟨deltaCell, hdeltaCell, hcell⟩ :=
    lem_prefix_limit_g9_cell_compact hd I _Poincare _Extension _Perturbation _Sobolev D
      Cresp hCresp
  obtain ⟨deltaMoment, A, hdeltaMoment, hA, hmoment⟩ :=
    lem_prefix_limit_g9_cell_moment hd I _Poincare _Extension _Perturbation _Sobolev D
      Cresp hCresp q (le_of_lt hq)
  let gap : ℝ := (2 * min sigma s - (d : ℝ) / q) * Real.log 3
  have hgap : 0 < gap := by
    dsimp [gap]
    exact mul_pos (by linarith) (Real.log_pos (by norm_num))
  let delta0 : ℝ := min deltaCell
    (min deltaMoment (Real.sqrt (gap / (A + 1))))
  have hdelta0 : 0 < delta0 := by
    dsimp [delta0]
    positivity
  refine ⟨delta0, hdelta0, ?_⟩
  intro M hM Rm hRm Sreg _It H hH
  dsimp
  let F : ℕ → BilateralField d → Homogenization.Book.Ch02.TriadicCoeffFamily d :=
    fun K omega => I.chart 0 1 one_pos
      (Lane4.cutoffPositiveCoefficient M H omega K 0 one_pos) 0 1
  let μ : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  have hMdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hMcell : M.delta ≤ deltaCell := hM.trans (min_le_left _ _)
  have hMmoment : M.delta ≤ deltaMoment :=
    hM.trans (le_trans (min_le_right deltaCell _) (min_le_left _ _))
  have hMsqrt : M.delta ≤ Real.sqrt (gap / (A + 1)) :=
    hM.trans (le_trans (min_le_right deltaCell _) (min_le_right _ _))
  have hA1 : 0 < A + 1 := by linarith
  have hsq : M.delta ^ 2 ≤ gap / (A + 1) := by
    have hsqrt : 0 ≤ Real.sqrt (gap / (A + 1)) := Real.sqrt_nonneg _
    have hsqrt2 : (Real.sqrt (gap / (A + 1))) ^ 2 = gap / (A + 1) :=
      Real.sq_sqrt (le_of_lt (div_pos hgap hA1))
    nlinarith
  have hgapM : A * M.delta ^ 2 < gap := by
    calc
      A * M.delta ^ 2 ≤ A * (gap / (A + 1)) :=
        mul_le_mul_of_nonneg_left hsq hA
      _ < gap := by
        have hden : 0 < A + 1 := hA1
        rw [show A * (gap / (A + 1)) = (A * gap) / (A + 1) by ring]
        apply (div_lt_iff₀ hden).2
        nlinarith
  have hgapSigma : A * M.delta ^ 2 < (2 * sigma - (d : ℝ) / q) * Real.log 3 := by
    apply lt_of_lt_of_le hgapM
    have hmin : min sigma s ≤ sigma := min_le_left _ _
    have hlog : 0 ≤ Real.log (3 : ℝ) := le_of_lt (Real.log_pos (by norm_num))
    exact mul_le_mul_of_nonneg_right (by linarith) hlog
  have hgapS : A * M.delta ^ 2 < (2 * s - (d : ℝ) / q) * Real.log 3 := by
    apply lt_of_lt_of_le hgapM
    have hmin : min sigma s ≤ s := min_le_right _ _
    have hlog : 0 ≤ Real.log (3 : ℝ) := le_of_lt (Real.log_pos (by norm_num))
    exact mul_le_mul_of_nonneg_right (by linarith) hlog
  have hcellM := hcell M hMcell Rm hRm Sreg _It H hH
  dsimp at hcellM
  obtain ⟨C, hC, hmomentM⟩ := hmoment M hMmoment Rm hRm Sreg _It H hH
  dsimp at hmomentM
  have hDroot : ∀ n (R : Homogenization.TriadicCube d),
      R ∈ aux_lem_prefix_limit_g9_unit_chart_compact_D (d := d) n →
      R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0) (-(n : ℤ)) := by
    intro n R hR
    simpa [aux_lem_prefix_limit_g9_unit_chart_compact_D, Homogenization.originCube] using hR
  let Cn : ℕ → ℝ := fun n => C * Real.exp (A * M.delta ^ 2 * (n : ℝ))
  have hsum (t : ℝ) (ht0 : 0 < t)
      (hgt : A * M.delta ^ 2 < (2 * t - (d : ℝ) / q) * Real.log 3) :
      Summable (fun n => Homogenization.Book.Ch02.geometricWeight t 2 n *
        ((aux_lem_prefix_limit_g9_unit_chart_compact_D (d := d) n).card : ℝ) ^ (1 / q) * Cn n) := by
    simpa [Cn] using aux_lem_prefix_limit_g9_unit_chart_compact_weight_card_exp
      (D := aux_lem_prefix_limit_g9_unit_chart_compact_D (d := d))
      (fun n => aux_lem_prefix_limit_g9_unit_chart_compact_D_card n)
      t q C A M.delta ht0 hqpos (le_of_lt hC) hA hgt
  have hcompCell : ∀ (n : ℕ) (R : Homogenization.TriadicCube d),
      R ∈ aux_lem_prefix_limit_g9_unit_chart_compact_D (d := d) n →
      ∀ tag : Fin 3 ⊕ (Bool × (Fin d × Fin d)),
      ∃ hm : ∀ K, MemLp
          (fun omega =>
            Sum.elim
              (fun j => if j = 0 then
                Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R (F K omega)
                else if j = 1 then
                Homogenization.Book.Ch02.coarseBMatrixNorm R (F K omega)
                else (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R (F K omega) 1).toReal)
              (fun ab => if ab.1 then
                Homogenization.Book.Ch02.sigmaCoarse
                  (Homogenization.Book.Ch02.cubeDomain R) ((F K omega).coeffOn R)
                  ab.2.1 ab.2.2
                else Homogenization.Book.Ch02.sigmaStarInvCoarse
                  (Homogenization.Book.Ch02.cubeDomain R) ((F K omega).coeffOn R)
                  ab.2.1 ab.2.2) tag) 1 μ,
        IsCompact (closure (Set.range (fun K =>
          (hm K).toLp (fun omega =>
            Sum.elim
              (fun j => if j = 0 then
                Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R (F K omega)
                else if j = 1 then
                Homogenization.Book.Ch02.coarseBMatrixNorm R (F K omega)
                else (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R (F K omega) 1).toReal)
              (fun ab => if ab.1 then
                Homogenization.Book.Ch02.sigmaCoarse
                  (Homogenization.Book.Ch02.cubeDomain R) ((F K omega).coeffOn R)
                  ab.2.1 ab.2.2
                else Homogenization.Book.Ch02.sigmaStarInvCoarse
                  (Homogenization.Book.Ch02.cubeDomain R) ((F K omega).coeffOn R)
                  ab.2.1 ab.2.2) tag)))) := by
    intro n R hR tag
    simpa [F, μ] using hcellM R (aux_lem_prefix_limit_g9_unit_chart_compact_D_subset n R hR) tag
  let Sσ : ℕ → BilateralField d → ℝ := fun K omega => ∑' n,
    Homogenization.Book.Ch02.geometricWeight sigma 2 n *
      (aux_lem_prefix_limit_g9_unit_chart_compact_D (d := d) n).sup'
        (aux_lem_prefix_limit_g9_unit_chart_compact_D_nonempty n)
        (fun R => Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R (F K omega))
  have hseriesSigma : ∃ hm : ∀ K, MemLp (Sσ K) 1 μ,
      IsCompact (closure (Set.range (fun K => (hm K).toLp (Sσ K)))) := by
    apply aux_lem_prefix_limit_g9_unit_chart_compact_max_series μ
      (aux_lem_prefix_limit_g9_unit_chart_compact_D (d := d))
      (fun n => aux_lem_prefix_limit_g9_unit_chart_compact_D_nonempty n)
      (fun n R K omega => Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R (F K omega))
      (fun n R K omega => by
        unfold Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm
          Homogenization.Book.Ch02.matrixNorm
        exact norm_nonneg _)
      (fun n => Homogenization.Book.Ch02.geometricWeight sigma 2 n) Cn q hq
      (fun n => by
        change 0 ≤ Homogenization.Book.Ch02.geometricWeight sigma 2 n
        rw [Homogenization.Book.Ch02.geometricWeight_eq_old]
        exact Homogenization.geometricWeight_nonneg (s := sigma) (q := 2) n
          (mul_nonneg (le_of_lt hsigma.1) (by norm_num)))
      (fun n R hR => by
        simpa [F, μ] using hcompCell n R hR (Sum.inl 0))
      (fun n R hR K => by
        exact (hmomentM.1 n R (hDroot n R hR) K).1)
      (by simpa [Sσ] using hsum sigma hsigma.1 hgapSigma)
  let SΛ : ℕ → BilateralField d → ℝ := fun K omega => ∑' n,
    Homogenization.Book.Ch02.geometricWeight sigma 2 n *
      (aux_lem_prefix_limit_g9_unit_chart_compact_D (d := d) n).sup'
        (aux_lem_prefix_limit_g9_unit_chart_compact_D_nonempty n)
        (fun R => Homogenization.Book.Ch02.coarseBMatrixNorm R (F K omega))
  have hseriesLam : ∃ hm : ∀ K, MemLp (SΛ K) 1 μ,
      IsCompact (closure (Set.range (fun K => (hm K).toLp (SΛ K)))) := by
    apply aux_lem_prefix_limit_g9_unit_chart_compact_max_series μ
      (aux_lem_prefix_limit_g9_unit_chart_compact_D (d := d))
      (fun n => aux_lem_prefix_limit_g9_unit_chart_compact_D_nonempty n)
      (fun n R K omega => Homogenization.Book.Ch02.coarseBMatrixNorm R (F K omega))
      (fun n R K omega => by
        unfold Homogenization.Book.Ch02.coarseBMatrixNorm
          Homogenization.Book.Ch02.matrixNorm
        exact norm_nonneg _)
      (fun n => Homogenization.Book.Ch02.geometricWeight sigma 2 n) Cn q hq
      (fun n => by
        change 0 ≤ Homogenization.Book.Ch02.geometricWeight sigma 2 n
        rw [Homogenization.Book.Ch02.geometricWeight_eq_old]
        exact Homogenization.geometricWeight_nonneg (s := sigma) (q := 2) n
          (mul_nonneg (le_of_lt hsigma.1) (by norm_num)))
      (fun n R hR => by
        simpa [F, μ] using hcompCell n R hR (Sum.inl 1))
      (fun n R hR K => by
        exact (hmomentM.1 n R (hDroot n R hR) K).2.1)
      (by simpa [SΛ] using hsum sigma hsigma.1 hgapSigma)
  let SE : ℕ → BilateralField d → ℝ := fun K omega => ∑' n,
    Homogenization.Book.Ch02.geometricWeight s 2 n *
      (aux_lem_prefix_limit_g9_unit_chart_compact_D (d := d) n).sup'
        (aux_lem_prefix_limit_g9_unit_chart_compact_D_nonempty n)
        (fun R => (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R (F K omega) 1).toReal)
  have hseriesProbe : ∃ hm : ∀ K, MemLp (SE K) 1 μ,
      IsCompact (closure (Set.range (fun K => (hm K).toLp (SE K)))) := by
    apply aux_lem_prefix_limit_g9_unit_chart_compact_max_series μ
      (aux_lem_prefix_limit_g9_unit_chart_compact_D (d := d))
      (fun n => aux_lem_prefix_limit_g9_unit_chart_compact_D_nonempty n)
      (fun n R K omega => (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R (F K omega) 1).toReal)
      (fun n R K omega => ENNReal.toReal_nonneg)
      (fun n => Homogenization.Book.Ch02.geometricWeight s 2 n) Cn q hq
      (fun n => by
        change 0 ≤ Homogenization.Book.Ch02.geometricWeight s 2 n
        rw [Homogenization.Book.Ch02.geometricWeight_eq_old]
        exact Homogenization.geometricWeight_nonneg (s := s) (q := 2) n
          (mul_nonneg (le_of_lt hs.1) (by norm_num)))
      (fun n R hR => by
        simpa [F, μ] using hcompCell n R hR (Sum.inl 2))
      (fun n R hR K => by
        exact (hmomentM.1 n R (hDroot n R hR) K).2.2)
      (by simpa [SE] using hsum s hs.1 hgapS)
  have hlamInvEq : ∀ K,
      (fun omega =>
        (Homogenization.Book.Ch02.lambdaSq (Homogenization.originCube d 0) sigma
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) (F K omega))⁻¹) =
        Sσ K := by
    intro K
    funext omega
    simpa [Sσ] using
      (aux_lem_prefix_limit_g9_unit_chart_compact_lam_inv_eq sigma (F K omega))
  have hLamEq : ∀ K,
      (fun omega => Homogenization.Book.Ch02.LambdaSq (Homogenization.originCube d 0) sigma
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) (F K omega)) =
        SΛ K := by
    intro K
    funext omega
    simpa [SΛ] using
      (aux_lem_prefix_limit_g9_unit_chart_compact_Lam_eq sigma (F K omega))
  have hErrFin : ∀ K omega,
      SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite
        (Homogenization.originCube d 0) 0 s
        Homogenization.Book.Ch02.MultiscaleExponent.infinity 2 (F K omega) 1 < ⊤ := by
    intro K omega
    simpa [F] using I.err_finite 0 1 one_pos
      (Lane4.cutoffPositiveCoefficient M H omega K 0 one_pos) 0 1 one_pos subset_rfl
      s hs 2 (by norm_num) 1 one_pos
  have hErrEq : ∀ K,
      (fun omega =>
        (SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite
          (Homogenization.originCube d 0) 0 s
          Homogenization.Book.Ch02.MultiscaleExponent.infinity 2 (F K omega) 1).toReal) =
        fun omega => Real.sqrt (SE K omega) := by
    intro K
    funext omega
    exact aux_lem_prefix_limit_g9_unit_chart_compact_err_eq s hs.1 (F K omega)
      (hErrFin K omega)
  rcases hseriesSigma with ⟨hmSigma, hcSigma⟩
  rcases hseriesLam with ⟨hmLam, hcLam⟩
  rcases hseriesProbe with ⟨hmProbe, hcProbe⟩
  have hSigmaInvEq : ∀ K omega,
      (Sσ K omega)⁻¹ = Homogenization.Book.Ch02.lambdaSq
        (Homogenization.originCube d 0) sigma
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) (F K omega) := by
    intro K omega
    rw [← congrFun (hlamInvEq K) omega, inv_inv]
  have hLambdaMem : ∀ K, MemLp (fun omega =>
      Homogenization.Book.Ch02.lambdaSq (Homogenization.originCube d 0) sigma
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) (F K omega))
      (ENNReal.ofReal q) μ := by
    intro K
    have hroot := hmomentM.2 K
    have hlae : AEStronglyMeasurable (fun omega =>
        Homogenization.Book.Ch02.lambdaSq (Homogenization.originCube d 0) sigma
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) (F K omega)) μ := by
      rw [show (fun omega => Homogenization.Book.Ch02.lambdaSq
          (Homogenization.originCube d 0) sigma
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) (F K omega)) =
          (fun omega => (Sσ K omega)⁻¹) by
            funext omega; exact (hSigmaInvEq K omega).symm]
      exact ((hmSigma K).1.aemeasurable.inv).aestronglyMeasurable
    refine ⟨hlae, ?_⟩
    apply lt_of_le_of_lt (eLpNorm_mono (fun omega => ?_))
      (lt_of_le_of_lt hroot.2 (ENNReal.ofReal_lt_top))
    simp only [Real.norm_eq_abs, abs_of_nonneg (le_of_lt
      (Homogenization.Book.Ch02.lambdaSq_finite_pos
        (Homogenization.originCube d 0) (F K omega) (s := sigma) (q := (2 : ℝ))
          hsigma.1 (by norm_num)))]
    have hcoarse : 0 ≤ Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm
        (Homogenization.originCube d 0) (F K omega) := by
      unfold Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm
        Homogenization.Book.Ch02.matrixNorm
      exact norm_nonneg _
    rw [abs_of_nonneg (inv_nonneg.mpr (by simpa [F] using hcoarse))]
    simpa [F] using (Homogenization.Book.Ch02.lambdaSq_le_oneCube
      (Homogenization.originCube d 0) (F K omega) (s := sigma)
      (q := Homogenization.Book.Ch02.MultiscaleExponent.finite 2) hsigma.1 (by norm_num))
  have hLambdaBound : ∀ K, eLpNorm (fun omega =>
      Homogenization.Book.Ch02.lambdaSq (Homogenization.originCube d 0) sigma
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) (F K omega))
      (ENNReal.ofReal q) μ ≤ ENNReal.ofReal C := by
    intro K
    have hroot := hmomentM.2 K
    apply le_trans (eLpNorm_mono (fun omega => ?_)) hroot.2
    simp only [Real.norm_eq_abs, abs_of_nonneg (le_of_lt
      (Homogenization.Book.Ch02.lambdaSq_finite_pos
        (Homogenization.originCube d 0) (F K omega) (s := sigma) (q := (2 : ℝ))
          hsigma.1 (by norm_num)))]
    have hcoarse : 0 ≤ Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm
        (Homogenization.originCube d 0) (F K omega) := by
      unfold Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm
        Homogenization.Book.Ch02.matrixNorm
      exact norm_nonneg _
    rw [abs_of_nonneg (inv_nonneg.mpr (by simpa [F] using hcoarse))]
    simpa [F] using (Homogenization.Book.Ch02.lambdaSq_le_oneCube
      (Homogenization.originCube d 0) (F K omega) (s := sigma)
      (q := Homogenization.Book.Ch02.MultiscaleExponent.finite 2) hsigma.1 (by norm_num))
  have hcompactLambda : ∃ hm : ∀ K, MemLp (fun omega =>
      Homogenization.Book.Ch02.lambdaSq (Homogenization.originCube d 0) sigma
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) (F K omega)) 1 μ,
      IsCompact (closure (Set.range (fun K => (hm K).toLp (fun omega =>
        Homogenization.Book.Ch02.lambdaSq (Homogenization.originCube d 0) sigma
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) (F K omega))))) := by
    have hLambdaMem1 : ∀ K, MemLp (fun omega =>
        Homogenization.Book.Ch02.lambdaSq (Homogenization.originCube d 0) sigma
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) (F K omega)) 1 μ := by
      intro K
      exact MemLp.mono_exponent (hLambdaMem K)
        (ENNReal.one_le_ofReal.mpr (le_of_lt hq))
    have hInvCompact := lem_prefix_limit_g9_inv_compact μ Sσ q C hq
      (by
        intro K
        filter_upwards with omega
        rw [← congrFun (hlamInvEq K) omega]
        exact inv_pos.mpr (Homogenization.Book.Ch02.lambdaSq_finite_pos
          (Homogenization.originCube d 0) (F K omega) (s := sigma) (q := (2 : ℝ))
          hsigma.1 (by norm_num)))
      ⟨hmSigma, hcSigma⟩
      (by
        intro K
        have hmem := (memLp_congr_ae (μ := μ) (p := ENNReal.ofReal q)
          (Filter.Eventually.of_forall (fun omega => hSigmaInvEq K omega))).2
            (hLambdaMem K)
        have hbound : eLpNorm (fun omega => (Sσ K omega)⁻¹)
            (ENNReal.ofReal q) μ ≤ ENNReal.ofReal C := by
          rw [eLpNorm_congr_ae
            (Filter.Eventually.of_forall (fun omega => hSigmaInvEq K omega))]
          exact hLambdaBound K
        exact ⟨hmem, hbound⟩)
    obtain ⟨hmInv, hcInv⟩ := hInvCompact
    refine ⟨hLambdaMem1, ?_⟩
    exact aux_lem_prefix_limit_g9_unit_chart_compact_compact_congr μ
      (fun K omega => (Sσ K omega)⁻¹)
      (fun K omega => Homogenization.Book.Ch02.lambdaSq
        (Homogenization.originCube d 0) sigma
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) (F K omega))
      hmInv hLambdaMem1
      (fun K => funext (hSigmaInvEq K)) hcInv
  rcases hcompactLambda with ⟨hmLambda, hcLambda⟩
  have hSEnonneg : ∀ K omega, 0 ≤ SE K omega := by
    intro K omega
    dsimp [SE]
    apply tsum_nonneg
    intro n
    have hw : 0 ≤ Homogenization.Book.Ch02.geometricWeight s 2 n := by
      rw [Homogenization.Book.Ch02.geometricWeight_eq_old]
      exact Homogenization.geometricWeight_nonneg (s := s) (q := 2) n
        (mul_nonneg (le_of_lt hs.1) (by norm_num))
    obtain ⟨R, hR⟩ := aux_lem_prefix_limit_g9_unit_chart_compact_D_nonempty n
    have hsup : 0 ≤ (aux_lem_prefix_limit_g9_unit_chart_compact_D (d := d) n).sup'
        (aux_lem_prefix_limit_g9_unit_chart_compact_D_nonempty n)
        (fun R => (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R (F K omega) 1).toReal) :=
      (show 0 ≤ (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R (F K omega) 1).toReal from
        ENNReal.toReal_nonneg).trans
        (Finset.le_sup' (fun R =>
          (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R (F K omega) 1).toReal) hR)
    exact mul_nonneg hw hsup
  have hmErr : ∀ K, MemLp (fun omega => Real.sqrt (SE K omega)) 1 μ := by
    intro K
    have hbase : MemLp (fun omega => (1 : ℝ) + SE K omega) 1 μ :=
      (memLp_const (μ := μ) (p := (1 : ENNReal)) (1 : ℝ)).add (hmProbe K)
    apply MemLp.of_le hbase
    · exact ((hmProbe K).1.aemeasurable.sqrt).aestronglyMeasurable
    · filter_upwards with omega
      have hsqrt : Real.sqrt (SE K omega) ≤ 1 + SE K omega := by
        apply (Real.sqrt_le_left (by linarith [hSEnonneg K omega])).2
        nlinarith [sq_nonneg (SE K omega)]
      have habs : Real.sqrt (SE K omega) ≤ |1 + SE K omega| := by
        rw [abs_of_nonneg (by linarith [hSEnonneg K omega])]
        exact hsqrt
      simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using habs
  have hcErr : IsCompact (closure (Set.range (fun K =>
      (hmErr K).toLp (fun omega => Real.sqrt (SE K omega))))) := by
    apply aux_lem_prefix_limit_g9_unit_chart_compact_of_sqrt_dist
      (fun K => (hmProbe K).toLp (SE K))
      (fun K => (hmErr K).toLp (fun omega => Real.sqrt (SE K omega))) hcProbe
    intro K K'
    exact aux_lem_prefix_limit_g9_unit_chart_compact_sqrt_l1_dist μ
      (hmProbe K) (hmProbe K') (hmErr K) (hmErr K')
      (Filter.Eventually.of_forall (fun omega => hSEnonneg K omega))
      (Filter.Eventually.of_forall (fun omega => hSEnonneg K' omega))
  intro rt
  rcases rt with j | rest
  · fin_cases j
    · refine ⟨fun K => ?_, ?_⟩
      · simpa [F] using hmLambda K
      · simpa [F] using hcLambda
    · refine ⟨fun K => ?_, ?_⟩
      · have hmem : MemLp (fun omega =>
            Homogenization.Book.Ch02.LambdaSq (Homogenization.originCube d 0) sigma
              (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) (F K omega)) 1 μ :=
          (memLp_congr_ae (μ := μ) (p := (1 : ENNReal)) (Filter.Eventually.of_forall
            (fun omega => congrFun (hLamEq K) omega))).2 (hmLam K)
        simpa [F] using hmem
      · exact aux_lem_prefix_limit_g9_unit_chart_compact_compact_congr μ
          (fun K omega => SΛ K omega)
          (fun K omega => Homogenization.Book.Ch02.LambdaSq (Homogenization.originCube d 0)
            sigma (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) (F K omega))
          hmLam
          (fun K => (memLp_congr_ae (μ := μ) (p := (1 : ENNReal)) (Filter.Eventually.of_forall
            (fun omega => congrFun (hLamEq K) omega))).2 (hmLam K))
          (fun K => (hLamEq K).symm) hcLam
    · refine ⟨fun K => ?_, ?_⟩
      · have hmem : MemLp (fun omega =>
            (Homogenization.Book.Ch02.lambdaSq (Homogenization.originCube d 0) sigma
              (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) (F K omega))⁻¹) 1 μ :=
          (memLp_congr_ae (p := (1 : ENNReal)) (Filter.Eventually.of_forall
            (fun omega => congrFun (hlamInvEq K) omega))).2 (hmSigma K)
        simpa [F] using hmem
      · exact aux_lem_prefix_limit_g9_unit_chart_compact_compact_congr μ
          (fun K omega => Sσ K omega)
          (fun K omega =>
            (Homogenization.Book.Ch02.lambdaSq (Homogenization.originCube d 0) sigma
              (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) (F K omega))⁻¹)
          hmSigma
          (fun K => (memLp_congr_ae (p := (1 : ENNReal)) (Filter.Eventually.of_forall
            (fun omega => congrFun (hlamInvEq K) omega))).2 (hmSigma K))
          (fun K => (hlamInvEq K).symm) hcSigma
  · rcases rest with ab | unit
    · obtain ⟨hm, hc⟩ := hcellM (Homogenization.originCube d 0) subset_rfl
        (Sum.inr ab)
      refine ⟨fun K => ?_, ?_⟩
      · by_cases hab : ab.1
        · simpa [F, μ, hab] using hm K
        · simpa [F, μ, hab] using hm K
      · by_cases hab : ab.1
        · simpa [F, μ, hab] using hc
        · simpa [F, μ, hab] using hc
    · refine ⟨fun K => ?_, ?_⟩
      · simpa [F] using
          ((memLp_congr_ae (μ := μ) (p := (1 : ENNReal))
            (Filter.Eventually.of_forall (fun omega => congrFun (hErrEq K) omega))).2
            (hmErr K))
      · simpa [F] using
          (aux_lem_prefix_limit_g9_unit_chart_compact_compact_congr μ
            (fun K omega => Real.sqrt (SE K omega))
            (fun K omega =>
              (SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite
                (Homogenization.originCube d 0) 0 s
                Homogenization.Book.Ch02.MultiscaleExponent.infinity 2 (F K omega) 1).toReal)
            hmErr
            (fun K =>
              (memLp_congr_ae (μ := μ) (p := (1 : ENNReal))
                (Filter.Eventually.of_forall (fun omega => congrFun (hErrEq K).symm omega))).1
                (hmErr K))
            (fun K => (hErrEq K).symm) hcErr)

end Paper
