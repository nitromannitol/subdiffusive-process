module

public import SubdiffusiveProcess.Paper.obl_ramp_site_inputs
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.GoodScaleSaturation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6AnnularResummation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.GoodEventCap
public import SubdiffusiveProcess.Paper.product_threshold_regularities
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.AnnularLocalization
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.LongRatioEvent

@[expose] public section

/-!
# Threshold-12 coarse homogenization error

The two cutoff branches establish the fourth conjunct of
`product_threshold_regularities d 12`.
-/




set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

namespace SubdiffusiveProcess.Paper

variable {d : ℕ}

/-! ## Elementary sup-norm reads -/

private theorem aux_obl_ramp_threshold12_fourth_ieb12_supNormOn_nonneg (W : Set (Vec d)) (f : Vec d → ℝ) :
    0 ≤ supNormOn W f := by
  refine Real.sSup_nonneg ?_
  rintro a ⟨x, _, rfl⟩
  exact abs_nonneg _

private theorem aux_obl_ramp_threshold12_fourth_ieb12_abs_le_supNormOn {W : Set (Vec d)} {f : Vec d → ℝ}
    (hB : BddAbove ((fun x => |f x|) '' W)) {x : Vec d} (hx : x ∈ W) :
    |f x| ≤ supNormOn W f := by
  unfold supNormOn
  refine le_csSup (hB.mono ?_) ⟨x, hx, rfl⟩
  rintro r ⟨y, hy, rfl⟩
  exact ⟨y, hy, rfl⟩

private theorem aux_obl_ramp_threshold12_fourth_ieb12_shellBlock_continuous (m n : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    Continuous (shellBlock m n omega) := by
  unfold shellBlock
  fun_prop

private theorem aux_obl_ramp_threshold12_fourth_ieb12_bddAbove_abs_values_cube (m : ℕ) {f : Vec d → ℝ}
    (hf : Continuous f) :
    BddAbove {a : ℝ | ∃ x ∈ cube d m, a = |f x|} := by
  let Q := originCube d (m : ℤ)
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (cubeCenter Q) (cubeRadius Q)).exists_bound_of_continuousOn
      ((continuous_abs.comp hf).continuousOn)
  refine ⟨max 0 C, ?_⟩
  rintro a ⟨x, hx, rfl⟩
  have hx' : x ∈ Metric.closedBall (cubeCenter Q) (cubeRadius Q) :=
    cubeSet_subset_closedBall Q (openCubeSet_subset_cubeSet Q hx)
  have h := hC x hx'
  simpa only [Function.comp_apply, Real.norm_eq_abs, abs_abs] using
    h.trans (le_max_right _ _)

private theorem aux_obl_ramp_threshold12_fourth_ieb12_zero_mem_cube (k : ℤ) : (0 : Vec d) ∈ cube d k := by
  rw [cube, mem_openCubeSet_originCube_iff]
  intro i
  have hp : 0 < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  constructor <;> simp only [Pi.zero_apply] <;> nlinarith

/-! ## Site (ii): the combined-ratio error from `obl_ramp_site_inputs` -/

/-- The two-squared-`L^∞` sensitivity error on a local cube, read from the
threshold-12 sup-norm bound of `obl_ramp_site_inputs` (clause (ii)). -/
theorem aux_obl_ramp_threshold12_fourth_ieb12_cutoffRatioError_le
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m n : ℕ} (hnm : n ≤ m) (hmL : m ≤ L)
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d) (z : Vec d) {W : ℝ}
    (hB1 : BddAbove ((fun x : Vec d =>
      |combinedCoefficientRatio M L m n eta z x - 1|) '' cube d n))
    (hB2 : BddAbove ((fun x : Vec d =>
      |combinedCoefficientRatioInv M L m n eta z x - 1|) '' cube d n))
    (hsum : supNormOn (cube d n)
          (fun x => combinedCoefficientRatio M L m n eta z x - 1) +
        supNormOn (cube d n)
          (fun x => combinedCoefficientRatioInv M L m n eta z x - 1) ≤ W) :
    cutoffRatioError M n L (translatePotentialSample z eta)
        (Ch02.cubeDomain (originCube d (n : ℤ)))
        (tailCoefficientCubeAverage M L m eta) ≤ 2 * W ^ 2 := by
  set U : Ch02.Domain d := Ch02.cubeDomain (originCube d (n : ℤ)) with hU
  have h1 := aux_obl_ramp_threshold12_fourth_ieb12_supNormOn_nonneg (cube d n)
    (fun x => combinedCoefficientRatio M L m n eta z x - 1)
  have h2 := aux_obl_ramp_threshold12_fourth_ieb12_supNormOn_nonneg (cube d n)
    (fun x => combinedCoefficientRatioInv M L m n eta z x - 1)
  have hW0 : 0 ≤ W := by linarith
  have hfwd : ∀ x ∈ (U : Set (Vec d)),
      |combinedCoefficientRatio M L m n eta z x - 1| ≤ W := by
    intro x hx
    have hx' : x ∈ cube d n := by exact hx
    have h := aux_obl_ramp_threshold12_fourth_ieb12_abs_le_supNormOn
      (f := fun x => combinedCoefficientRatio M L m n eta z x - 1) hB1 hx'
    linarith
  have hrev : ∀ x ∈ (U : Set (Vec d)),
      |combinedCoefficientRatioInv M L m n eta z x - 1| ≤ W := by
    intro x hx
    have hx' : x ∈ cube d n := by exact hx
    have h := aux_obl_ramp_threshold12_fourth_ieb12_abs_le_supNormOn
      (f := fun x => combinedCoefficientRatioInv M L m n eta z x - 1) hB2 hx'
    linarith
  have hforward := scalarRatioLInf_one_le_of_forall_bound hW0 hfwd
  have hreverse := scalarRatioLInf_one_le_of_forall_bound hW0 hrev
  rw [cutoffRatioError_tailAverage_eq_combined M hnm hmL eta z U]
  have hf0 := scalarRatioLInf_nonneg U
    (combinedCoefficientRatio M L m n eta z) (fun _ => 1)
  have hr0 := scalarRatioLInf_nonneg U
    (combinedCoefficientRatioInv M L m n eta z) (fun _ => 1)
  have hfsq := mul_self_le_mul_self hf0 hforward
  have hrsq := mul_self_le_mul_self hr0 hreverse
  nlinarith only [hfsq, hrsq]

/-! ## Response weighting and split (upstream `ResponseWeighting` /
`ResponseBudgetSplit`, with the site constant `CB`) -/

/-- Response weighting on an annular descendant.  Only the response clause of
the event is read. -/
theorem aux_obl_ramp_threshold12_fourth_ieb12_weighted_probe_le
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m n j : ℕ}
    (hnm : n ≤ m) {s CB : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s)
    (hj : j ≤ m) (hnj : n + 2 ≤ j)
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {R : SubdiffusiveProcess.CoarseGrainingVocab.TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ))
    (hann : triadicCubeShift R ∈ cube d j \ cube d (j - 1))
    {e : Vec d} (he : vecNormSq e = 1)
    (hresp : GoodResponse M none m 0 1 s eta)
    (hE : cutoffRatioError M n L
        (translatePotentialSample (triadicCubeShift R) eta)
        (Ch02.cubeDomain (originCube d (n : ℤ)))
        (tailCoefficientCubeAverage M L m eta) ≤
      2 * (CB * (3 : ℝ) ^ ((3 * s * ((m - n : ℕ) : ℝ)) / 16) *
        min 1 (longRatioGradientTail m eta +
          supNormOn (cube d n)
            (shellBlock m n
              (translatePotentialSample (triadicCubeShift R) eta)) +
          _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m - n : ℕ) : ℝ))) ^ 2) :
    (3 : ℝ) ^ (-(3 / 2) * (s * ((m - n : ℕ) : ℝ))) *
        paperScalarProbe (originCube d (n : ℤ))
          (aCutoffFamily M L
            (translatePotentialSample (triadicCubeShift R) eta))
          (tailCoefficientCubeAverage M L m eta) e ≤
      2 * (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
          section6Response M n n eta (triadicCubeShift R) e +
        12 * CB ^ 2 *
          (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
          (min 1 (longRatioGradientTail m eta +
            supNormOn (cube d n)
              (shellBlock m n
                (translatePotentialSample (triadicCubeShift R) eta)) +
            _root_.SubdiffusiveProcess.Model.tauSq M.P *
              ((m - n : ℕ) : ℝ))) ^ 2 := by
  let T : ℝ := ((m - n : ℕ) : ℝ)
  let u : ℝ := s * T
  let A : ℝ := (3 : ℝ) ^ ((3 * s * T) / 16)
  let B : ℝ := min 1 (longRatioGradientTail m eta +
    supNormOn (cube d n)
      (shellBlock m n
        (translatePotentialSample (triadicCubeShift R) eta)) +
    _root_.SubdiffusiveProcess.Model.tauSq M.P * T)
  let Jloc : ℝ := section6Response M n n eta (triadicCubeShift R) e
  let E : ℝ := cutoffRatioError M n L
    (translatePotentialSample (triadicCubeShift R) eta)
    (Ch02.cubeDomain (originCube d (n : ℤ)))
    (tailCoefficientCubeAverage M L m eta)
  let P : ℝ := paperScalarProbe (originCube d (n : ℤ))
    (aCutoffFamily M L
      (translatePotentialSample (triadicCubeShift R) eta))
    (tailCoefficientCubeAverage M L m eta) e
  let G : ℝ := (3 : ℝ) ^ (u / 8)
  let w : ℝ := (3 : ℝ) ^ (-(3 / 2) * u)
  let v : ℝ := (3 : ℝ) ^ (-u)
  have hgap : (m : ℝ) - (n : ℝ) = T := by
    dsimp only [T]
    rw [Nat.cast_sub hnm]
  have hRscale : R.scale = (n : ℤ) :=
    scale_eq_of_mem_descendantsAtScale hR
  have hgrid : OnTriadicGrid n (triadicCubeShift R) :=
    onTriadicGrid_triadicCubeShift_of_scale hRscale
  have hJ : Jloc ≤ G := by
    have hraw := hresp j n hj hnj (triadicCubeShift R)
      (by simpa using hgrid) (by simpa using hann) e he
    simpa only [Option.getD_none, min_self, one_pow, one_mul, sub_zero,
      hgap, Jloc, G, u] using hraw
  have hJ0 : 0 ≤ Jloc := by
    dsimp only [Jloc, section6Response, paperScalarProbe]
    exact Ch02.responseJ_nonneg _ _ _ _
  have hP : P ≤ 2 * Jloc + 3 * E * (Jloc + 1) := by
    exact paperScalarProbe_translatedCutoff_tailAverage_le_section6Response
      M L m n eta (triadicCubeShift R) e he
  have hE' : E ≤ 2 * (CB * A * B) ^ 2 := by
    simpa only [E, A, B, T] using hE
  have hu0 : 0 ≤ u := by
    dsimp only [u, T]
    exact mul_nonneg (le_trans (mul_nonneg (by norm_num) (sq_nonneg M.delta)) hsLower)
      (by positivity)
  have hG1 : 1 ≤ G := one_le_responseGrowth hu0
  have hw0 : 0 ≤ w := Real.rpow_nonneg (by norm_num) _
  have hwv : w ≤ v := responseOuterWeight_le_residualWeight hu0
  have hcollapse : w * A ^ 2 * G = v := by
    dsimp only [w, A, G, v, u]
    convert responseErrorWeight_identity (s * T) using 1
    all_goals ring_nf
  have hweighted := weightedTransport_of_bounds hP hE' hJ0 hJ hG1 hw0 hwv hcollapse
  simpa only [P, Jloc, B, w, v, u, T] using hweighted

/-- The split weighted response budget with the site constant. -/
theorem aux_obl_ramp_threshold12_fourth_ieb12_weighted_probe_le_split
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m n j : ℕ}
    (hnm : n ≤ m) {s CB : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s)
    (hj : j ≤ m) (hnj : n + 2 ≤ j)
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {R : SubdiffusiveProcess.CoarseGrainingVocab.TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ))
    (hann : triadicCubeShift R ∈ cube d j \ cube d (j - 1))
    {e : Vec d} (he : vecNormSq e = 1)
    (hresp : GoodResponse M none m 0 1 s eta)
    (hE : cutoffRatioError M n L
        (translatePotentialSample (triadicCubeShift R) eta)
        (Ch02.cubeDomain (originCube d (n : ℤ)))
        (tailCoefficientCubeAverage M L m eta) ≤
      2 * (CB * (3 : ℝ) ^ ((3 * s * ((m - n : ℕ) : ℝ)) / 16) *
        min 1 (longRatioGradientTail m eta +
          supNormOn (cube d n)
            (shellBlock m n
              (translatePotentialSample (triadicCubeShift R) eta)) +
          _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m - n : ℕ) : ℝ))) ^ 2) :
    (3 : ℝ) ^ (-(3 / 2) * (s * ((m - n : ℕ) : ℝ))) *
        paperScalarProbe (originCube d (n : ℤ))
          (aCutoffFamily M L
            (translatePotentialSample (triadicCubeShift R) eta))
          (tailCoefficientCubeAverage M L m eta) e ≤
      2 * (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
          section6Response M n n eta (triadicCubeShift R) e +
        36 * CB ^ 2 *
          ((3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
              longRatioGradientTail m eta ^ 2 +
            (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
              supNormOn (cube d n)
                (shellBlock m n
                  (translatePotentialSample (triadicCubeShift R) eta)) ^ 2 +
            2 * (s⁻¹) ^ 2 * M.delta ^ 4) := by
  let T : ℝ := ((m - n : ℕ) : ℝ)
  let v : ℝ := (3 : ℝ) ^ (-(s * T))
  let S : ℝ := longRatioGradientTail m eta
  let G : ℝ := supNormOn (cube d n)
    (shellBlock m n (translatePotentialSample (triadicCubeShift R) eta))
  let D : ℝ := _root_.SubdiffusiveProcess.Model.tauSq M.P * T
  let Main : ℝ := 2 * v * section6Response M n n eta (triadicCubeShift R) e
  let Pweighted : ℝ := (3 : ℝ) ^ (-(3 / 2) * (s * T)) *
    paperScalarProbe (originCube d (n : ℤ))
      (aCutoffFamily M L
        (translatePotentialSample (triadicCubeShift R) eta))
      (tailCoefficientCubeAverage M L m eta) e
  have hraw : Pweighted ≤ Main + 12 * CB ^ 2 * v * min 1 (S + G + D) ^ 2 := by
    simpa only [Pweighted, Main, v, S, G, D, T] using
      aux_obl_ramp_threshold12_fourth_ieb12_weighted_probe_le M hnm hsLower hj hnj eta hR hann he hresp hE
  have hv : 0 ≤ v := Real.rpow_nonneg (by norm_num) _
  have hsplit : Pweighted ≤ Main + 36 * CB ^ 2 * v * (S ^ 2 + G ^ 2 + D ^ 2) :=
    split_weighted_transport_budget hv hraw
  have hdrift : v * D ^ 2 ≤ 2 * (s⁻¹) ^ 2 * M.delta ^ 4 := by
    simpa only [v, D, T] using
      three_rpow_neg_mul_tauSq_sq_le M hsLower (t := T) (by positivity)
  have hbudget : v * (S ^ 2 + G ^ 2 + D ^ 2) ≤
      v * S ^ 2 + v * G ^ 2 + 2 * (s⁻¹) ^ 2 * M.delta ^ 4 := by
    calc
      v * (S ^ 2 + G ^ 2 + D ^ 2) = v * S ^ 2 + v * G ^ 2 + v * D ^ 2 := by ring
      _ ≤ v * S ^ 2 + v * G ^ 2 + 2 * (s⁻¹) ^ 2 * M.delta ^ 4 :=
        add_le_add le_rfl hdrift
  have hscaled : 36 * CB ^ 2 * (v * (S ^ 2 + G ^ 2 + D ^ 2)) ≤
      36 * CB ^ 2 * (v * S ^ 2 + v * G ^ 2 + 2 * (s⁻¹) ^ 2 * M.delta ^ 4) :=
    mul_le_mul_of_nonneg_left hbudget (mul_nonneg (by norm_num) (sq_nonneg CB))
  have hfinal : Pweighted ≤ Main + 36 * CB ^ 2 *
      (v * S ^ 2 + v * G ^ 2 + 2 * (s⁻¹) ^ 2 * M.delta ^ 4) := by
    calc
      Pweighted ≤ Main + 36 * CB ^ 2 * v * (S ^ 2 + G ^ 2 + D ^ 2) := hsplit
      _ = Main + 36 * CB ^ 2 * (v * (S ^ 2 + G ^ 2 + D ^ 2)) := by ring
      _ ≤ Main + 36 * CB ^ 2 *
          (v * S ^ 2 + v * G ^ 2 + 2 * (s⁻¹) ^ 2 * M.delta ^ 4) :=
        add_le_add le_rfl hscaled
  simpa only [Pweighted, Main, v, S, G, T] using hfinal

/-! ## Response-clause reads (upstream `Section6GoodScale`, with only the
response clause as hypothesis) -/

/-- `goodResponse_discounted_atom_le`, reading only `GoodResponse`. -/
theorem aux_obl_ramp_threshold12_fourth_ieb12_response_atom_le
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {m : ℕ} {epsilon s : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hs0 : 0 ≤ s)
    {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d}
    (hresp : GoodResponse M none m 0 epsilon s omega)
    {r : ℝ}
    (hr : r ∈ {r : ℝ | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧
        ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d j \ cube d (j - 1) ∧
        r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
          Real.sqrt (sSup {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
            t = section6Response M n n omega z e})}) :
    r ≤ epsilon := by
  rcases hr with ⟨j, n, hjm, hnj, z, hzgrid, hzann, rfl⟩
  have hnm : n ≤ m := by omega
  have hgap0 : 0 ≤ (m : ℝ) - (n : ℝ) := by
    exact sub_nonneg.mpr (by exact_mod_cast hnm)
  let A : Set ℝ := {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
    t = section6Response M n n omega z e}
  have hAbdd : BddAbove A := by
    simpa only [A] using bddAbove_section6Response_unitSphere M n n omega z
  have hAne : A.Nonempty := by
    let i : Fin d := ⟨0, lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension⟩
    refine ⟨section6Response M n n omega z (Pi.single i 1), Pi.single i 1, ?_, rfl⟩
    rw [vecNormSq, vecDot, Finset.sum_eq_single i]
    · simp
    · intro b _ hbi
      simp [Pi.single_eq_of_ne hbi]
    · simp
  have hresp' : sSup A ≤ epsilon ^ 2 *
      (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 8) := by
    refine csSup_le hAne ?_
    intro t ht
    rcases ht with ⟨e, he, rfl⟩
    simpa using hresp j n hjm hnj z (by simpa using hzgrid)
      (by simpa using hzann) e he
  have hsqrt : Real.sqrt (sSup A) ≤ epsilon *
      (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 16) := by
    have hright0 : 0 ≤ epsilon *
        (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 16) :=
      mul_nonneg hepsilon0 (Real.rpow_nonneg (by norm_num) _)
    rw [Real.sqrt_le_iff]
    refine ⟨hright0, ?_⟩
    calc
      sSup A ≤ epsilon ^ 2 *
          (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 8) := hresp'
      _ = (epsilon *
          (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 16)) ^ 2 := by
        rw [mul_pow]
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
        congr 1
        push_cast
        ring
  calc
    (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) * Real.sqrt (sSup A) ≤
        (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
          (epsilon * (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 16)) := by
      gcongr
    _ = epsilon * (3 : ℝ) ^
        (-(7 * s / 16) * ((m : ℝ) - (n : ℝ))) := by
      rw [mul_left_comm, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 2
      ring
    _ ≤ epsilon * 1 := by
      gcongr
      exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) hgap0)
    _ = epsilon := mul_one _

private theorem aux_obl_ramp_threshold12_fourth_ieb12_responseSlot_bddAbove
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {s : ℝ} {m : ℕ}
    {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d}
    (hs0 : 0 ≤ s) (hresp : GoodResponse M none m 0 1 s omega) :
    BddAbove {r : ℝ | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧
      ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d j \ cube d (j - 1) ∧
      r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
        Real.sqrt (sSup {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
          t = section6Response M n n omega z e})} := by
  refine ⟨1, ?_⟩
  intro r hr
  exact aux_obl_ramp_threshold12_fourth_ieb12_response_atom_le M zero_le_one hs0 hresp hr

/-! ## Slot domination (upstream `AnnularAggregation`) -/

private theorem aux_obl_ramp_threshold12_fourth_ieb12_supNormOn_mono_cube {n m : ℕ}
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {R : SubdiffusiveProcess.CoarseGrainingVocab.TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)) :
    supNormOn (cube d n)
        (shellBlock m n (translatePotentialSample (triadicCubeShift R) omega)) ≤
      supNormOn (cube d m) (shellBlock m n omega) := by
  unfold supNormOn
  apply csSup_le
  · exact ⟨|shellBlock m n (translatePotentialSample (triadicCubeShift R) omega) 0|,
      0, aux_obl_ramp_threshold12_fourth_ieb12_zero_mem_cube (n : ℤ), rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hscale : R.scale = (n : ℤ) := scale_eq_of_mem_descendantsAtScale hR
    have hxR : triadicCubeShift R + x ∈ openCubeSet R := by
      rw [openCubeSet_eq_translateSet_originCube_of_triadicCube,
        mem_translateSet_iff_sub_mem]
      simp only [hscale, add_sub_cancel_left]
      exact hx
    have hxM : triadicCubeShift R + x ∈ cube d m :=
      openCubeSet_subset_of_mem_descendantsAtScale
        (scale_le_of_mem_descendantsAtScale hR) hR hxR
    have hle : |shellBlock m n omega (triadicCubeShift R + x)| ≤
        sSup {a : ℝ | ∃ y ∈ cube d m, a = |shellBlock m n omega y|} :=
      le_csSup (aux_obl_ramp_threshold12_fourth_ieb12_bddAbove_abs_values_cube m
        (aux_obl_ramp_threshold12_fourth_ieb12_shellBlock_continuous m n omega))
        ⟨triadicCubeShift R + x, hxM, rfl⟩
    simp only [shellBlock_translatePotentialSample]
    convert hle using 1 ; first | rfl | simp only [add_comm]

private theorem aux_obl_ramp_threshold12_fourth_ieb12_shellSlot_bddAbove
    (s : ℝ) (m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    BddAbove {r : ℝ | ∃ j ≤ m,
      r = (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
        supNormOn (cube d m) (shellBlock m j omega)} := by
  let F : ℕ → ℝ := fun j =>
    (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
      supNormOn (cube d m) (shellBlock m j omega)
  refine ⟨Finset.sup' (Finset.range (m + 1))
      (Finset.nonempty_range_iff.mpr (by omega)) F, ?_⟩
  rintro r ⟨j, hj, rfl⟩
  exact Finset.le_sup' F (Finset.mem_range.mpr (by omega))

private theorem aux_obl_ramp_threshold12_fourth_ieb12_response_weight_le_slot_sq
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {m n j : ℕ}
    (hnm : n ≤ m) {s : ℝ} (hs0 : 0 ≤ s)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hresp : GoodResponse M none m 0 1 s omega)
    (hj : j ≤ m) (hnj : n + 2 ≤ j) {z : Vec d}
    (hzgrid : OnTriadicGrid n z) (hzann : z ∈ cube d j \ cube d (j - 1))
    {e : Vec d} (he : vecNormSq e = 1) :
    (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
        section6Response M n n omega z e ≤
      goodScaleResponseSlot M s m omega ^ 2 := by
  let A : Set ℝ := {t : ℝ | ∃ u : Vec d, vecNormSq u = 1 ∧
    t = section6Response M n n omega z u}
  have hAbdd : BddAbove A := by
    simpa only [A] using bddAbove_section6Response_unitSphere M n n omega z
  have hJle : section6Response M n n omega z e ≤ sSup A :=
    le_csSup hAbdd ⟨e, he, rfl⟩
  have hJ0 : 0 ≤ section6Response M n n omega z e := by
    unfold section6Response paperScalarProbe
    exact Ch02.responseJ_nonneg _ _ _ _
  have hA0 : 0 ≤ sSup A := hJ0.trans hJle
  let atom := (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) * Real.sqrt (sSup A)
  have hatomMem : atom ∈ {r : ℝ | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧
      ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d j \ cube d (j - 1) ∧
      r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
        Real.sqrt (sSup {t : ℝ | ∃ u : Vec d, vecNormSq u = 1 ∧
          t = section6Response M n n omega z u})} := by
    exact ⟨j, n, hj, hnj, z, hzgrid, hzann, by simp only [atom, A]⟩
  have hatomLe : atom ≤ goodScaleResponseSlot M s m omega := by
    unfold goodScaleResponseSlot
    exact le_csSup (aux_obl_ramp_threshold12_fourth_ieb12_responseSlot_bddAbove M hs0 hresp) hatomMem
  have hatom0 : 0 ≤ atom := mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (Real.sqrt_nonneg _)
  have hgap : (m : ℝ) - (n : ℝ) = ((m - n : ℕ) : ℝ) := by
    rw [Nat.cast_sub hnm]
  calc
    (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
        section6Response M n n omega z e ≤
      (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) * sSup A := by gcongr
    _ = atom ^ 2 := by
      dsimp [atom]
      rw [mul_pow, Real.sq_sqrt hA0]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 2
      rw [hgap]
      ring
    _ ≤ goodScaleResponseSlot M s m omega ^ 2 :=
      pow_le_pow_left₀ hatom0 hatomLe 2

private theorem aux_obl_ramp_threshold12_fourth_ieb12_shell_weight_le_slot_sq
    {m n : ℕ} (hnm : n ≤ m) {s : ℝ} (hs0 : 0 ≤ s)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) {R : SubdiffusiveProcess.CoarseGrainingVocab.TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)) :
    (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
        supNormOn (cube d n)
          (shellBlock m n (translatePotentialSample (triadicCubeShift R) omega)) ^ 2 ≤
      goodScaleShellSlot s m omega ^ 2 := by
  let G := supNormOn (cube d m) (shellBlock m n omega)
  let atom := (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (n : ℝ))) * G
  have hGlocal := aux_obl_ramp_threshold12_fourth_ieb12_supNormOn_mono_cube omega hR
  have hG0 : 0 ≤ G := aux_obl_ramp_threshold12_fourth_ieb12_supNormOn_nonneg _ _
  have hatomMem : atom ∈ {r : ℝ | ∃ j ≤ m,
      r = (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
        supNormOn (cube d m) (shellBlock m j omega)} :=
    ⟨n, hnm, by simp only [atom, G]⟩
  have hatomLe : atom ≤ goodScaleShellSlot s m omega := by
    unfold goodScaleShellSlot
    exact le_csSup (aux_obl_ramp_threshold12_fourth_ieb12_shellSlot_bddAbove s m omega) hatomMem
  have hatom0 : 0 ≤ atom := mul_nonneg (Real.rpow_nonneg (by norm_num) _) hG0
  have hw : (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) ≤
      ((3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (n : ℝ)))) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      Nat.cast_ofNat, Nat.cast_sub hnm]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hmn : (0 : ℝ) ≤ (m : ℝ) - (n : ℝ) :=
      sub_nonneg.mpr (by exact_mod_cast hnm)
    nlinarith
  have hlocal0 : 0 ≤ supNormOn (cube d n)
      (shellBlock m n (translatePotentialSample (triadicCubeShift R) omega)) :=
    aux_obl_ramp_threshold12_fourth_ieb12_supNormOn_nonneg _ _
  calc
    (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
        supNormOn (cube d n)
          (shellBlock m n (translatePotentialSample (triadicCubeShift R) omega)) ^ 2 ≤
      (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) * G ^ 2 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hlocal0 hGlocal 2)
          (Real.rpow_nonneg (by norm_num) _)
    _ ≤ ((3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (n : ℝ)))) ^ 2 * G ^ 2 := by
        gcongr
    _ = atom ^ 2 := by simp only [atom]; ring
    _ ≤ goodScaleShellSlot s m omega ^ 2 :=
      pow_le_pow_left₀ hatom0 hatomLe 2

/-- The threshold-12 positive-scale square budget. -/
def aux_obl_ramp_threshold12_fourth_ieb12_positiveBudget (CB : ℝ) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (s : ℝ) (m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  2 * goodScaleResponseSlot M s m omega ^ 2 +
    36 * CB ^ 2 *
      (goodScaleGradientSlot m omega ^ 2 +
        goodScaleShellSlot s m omega ^ 2 +
        2 * (s⁻¹ * M.delta ^ 2) ^ 2)

theorem aux_obl_ramp_threshold12_fourth_ieb12_positiveBudget_nonneg (CB : ℝ)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (s : ℝ) (m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ aux_obl_ramp_threshold12_fourth_ieb12_positiveBudget CB M s m omega := by
  unfold aux_obl_ramp_threshold12_fourth_ieb12_positiveBudget
  positivity



def aux_obl_ramp_threshold12_fourth_ieb12_SiteTwo (CB : ℝ) (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s : ℝ)
    (L m : ℕ) (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d) : Prop :=
  ∀ n : ℕ, n ≤ m → ∀ z : Vec d,
    translatedCube d n z ⊆ cube d m →
    BddAbove ((fun x : Vec d =>
      |combinedCoefficientRatio M L m n eta z x - 1|) '' cube d n) ∧
    BddAbove ((fun x : Vec d =>
      |combinedCoefficientRatioInv M L m n eta z x - 1|) '' cube d n) ∧
    supNormOn (cube d n)
        (fun x => combinedCoefficientRatio M L m n eta z x - 1) +
      supNormOn (cube d n)
        (fun x => combinedCoefficientRatioInv M L m n eta z x - 1) ≤
      CB * (3 : ℝ) ^ (3 * s * ((m : ℝ) - (n : ℝ)) / 16) *
        min 1 (longRatioGradientTail m eta +
          supNormOn (cube d n)
            (shellBlock m n (translatePotentialSample z eta)) +
          _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m : ℝ) - (n : ℝ)))

/-- Every nonnegative-scale annular atom is dominated by the threshold-12
positive budget. -/
theorem aux_obl_ramp_threshold12_fourth_ieb12_positive_annular_atom_le_budget
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ} (hmL : m ≤ L) {s CB : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s)
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hresp : GoodResponse M none m 0 1 s eta)
    (hsite : aux_obl_ramp_threshold12_fourth_ieb12_SiteTwo CB M s L m eta)
    (p : AnnularPairTwo d (m : ℤ)) (hscale0 : 0 ≤ p.1.1.scale) :
    ENNReal.ofReal
          ((3 : ℝ) ^ (-(3 * s / 2) *
            ((m : ℝ) - (p.1.1.scale : ℝ)))) *
        section6LocalProbeMax M L eta 0
          (tailCoefficientCubeAverage M L m eta) p.1.1 ≤
      ENNReal.ofReal (aux_obl_ramp_threshold12_fourth_ieb12_positiveBudget CB M s m eta) := by
  have hs0 : 0 ≤ s := le_trans (mul_nonneg (by norm_num) (sq_nonneg M.delta)) hsLower
  obtain ⟨hj, hscale, hann⟩ := p.2
  let n : ℕ := p.1.1.scale.toNat
  let jn : ℕ := p.1.2.toNat
  have hncast : (n : ℤ) = p.1.1.scale := Int.toNat_of_nonneg hscale0
  have hj0 : 0 ≤ p.1.2 := by omega
  have hjcast : (jn : ℤ) = p.1.2 := Int.toNat_of_nonneg hj0
  have hnmZ : (n : ℤ) ≤ (m : ℤ) := by rw [hncast]; omega
  have hjmZ : (jn : ℤ) ≤ (m : ℤ) := by rw [hjcast]; exact hj
  have hnjZ : (n : ℤ) + 2 ≤ (jn : ℤ) := by rw [hncast, hjcast]; omega
  have hnm : n ≤ m := by exact_mod_cast hnmZ
  have hjm : jn ≤ m := by exact_mod_cast hjmZ
  have hnj : n + 2 ≤ jn := by exact_mod_cast hnjZ
  have hR : p.1.1 ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ) := by
    rw [hncast]
    exact annularCube_mem_descendantsAtScale hj hscale hann
  have hann' : triadicCubeShift p.1.1 ∈ cube d jn \ cube d (jn - 1) := by
    simpa only [hjcast] using hann
  -- the site-(ii) read at the centre of `p.1.1`
  have hsub : translatedCube d n (triadicCubeShift p.1.1) ⊆ cube d m := by
    rintro y ⟨x, hx, rfl⟩
    have hRscale : p.1.1.scale = (n : ℤ) := scale_eq_of_mem_descendantsAtScale hR
    have hxR : triadicCubeShift p.1.1 + x ∈ openCubeSet p.1.1 := by
      rw [openCubeSet_eq_translateSet_originCube_of_triadicCube,
        mem_translateSet_iff_sub_mem]
      simp only [hRscale, add_sub_cancel_left]
      exact hx
    exact openCubeSet_subset_of_mem_descendantsAtScale
      (scale_le_of_mem_descendantsAtScale hR) hR hxR
  obtain ⟨hB1, hB2, hsum⟩ := hsite n hnm (triadicCubeShift p.1.1) hsub
  have hgapR : (m : ℝ) - (n : ℝ) = ((m - n : ℕ) : ℝ) := by rw [Nat.cast_sub hnm]
  have hE := aux_obl_ramp_threshold12_fourth_ieb12_cutoffRatioError_le M hnm hmL eta
    (triadicCubeShift p.1.1) hB1 hB2 hsum
  rw [hgapR] at hE
  have hweight :
      (3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (p.1.1.scale : ℝ))) =
        (3 : ℝ) ^ (-(3 / 2) * (s * ((m - n : ℕ) : ℝ))) := by
    congr 1
    have hnreal : (n : ℝ) = (p.1.1.scale : ℝ) := by exact_mod_cast hncast
    rw [← hnreal, hgapR]
    ring
  unfold section6LocalProbeMax
  rw [ENNReal.mul_iSup]
  refine iSup_le fun e => ?_
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _), hweight]
  apply ENNReal.ofReal_le_ofReal
  rw [Section6Covariance.translatePotentialSample_zero]
  have hraw := aux_obl_ramp_threshold12_fourth_ieb12_weighted_probe_le_split M hnm hsLower hjm hnj eta hR hann' e.2
    hresp (by simpa only [mul_assoc] using hE)
  have hresp2 := aux_obl_ramp_threshold12_fourth_ieb12_response_weight_le_slot_sq M hnm hs0 eta hresp hjm hnj
    (onTriadicGrid_triadicCubeShift_of_scale
      (scale_eq_of_mem_descendantsAtScale hR)) hann' e.2
  have hshell := aux_obl_ramp_threshold12_fourth_ieb12_shell_weight_le_slot_sq hnm hs0 eta hR
  have hv : (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (neg_nonpos.mpr (mul_nonneg hs0 (by positivity)))
  have hgrad0 : 0 ≤ goodScaleGradientSlot m eta := by
    rw [goodScaleGradientSlot_eq_longRatioGradientTail]
    exact longRatioGradientTail_nonneg m eta
  have hgrad : (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
      longRatioGradientTail m eta ^ 2 ≤ goodScaleGradientSlot m eta ^ 2 := by
    rw [← goodScaleGradientSlot_eq_longRatioGradientTail]
    nlinarith [sq_nonneg (goodScaleGradientSlot m eta)]
  have hdrift : 2 * (s⁻¹) ^ 2 * M.delta ^ 4 = 2 * (s⁻¹ * M.delta ^ 2) ^ 2 := by ring
  have hresp3 : 2 * (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
      section6Response M n n eta (triadicCubeShift p.1.1) e ≤
      2 * goodScaleResponseSlot M s m eta ^ 2 := by
    nlinarith only [hresp2]
  have hbudget :
      (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) * longRatioGradientTail m eta ^ 2 +
          (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
            supNormOn (cube d n)
              (shellBlock m n (translatePotentialSample (triadicCubeShift p.1.1) eta)) ^ 2 +
          2 * (s⁻¹) ^ 2 * M.delta ^ 4 ≤
        goodScaleGradientSlot m eta ^ 2 + goodScaleShellSlot s m eta ^ 2 +
          2 * (s⁻¹ * M.delta ^ 2) ^ 2 := by
    rw [hdrift]
    exact add_le_add (add_le_add hgrad hshell) le_rfl
  have hcoef : 0 ≤ 36 * CB ^ 2 := by positivity
  have hfinal := hraw.trans (add_le_add hresp3 (mul_le_mul_of_nonneg_left hbudget hcoef))
  simpa only [aux_obl_ramp_threshold12_fourth_ieb12_positiveBudget, hncast] using hfinal

/-! ## The subunit branch (upstream `SubunitTail`, site (iii)) -/

private theorem aux_obl_ramp_threshold12_fourth_ieb12_three_rpow_add (a b : ℝ) :
    (3 : ℝ) ^ a * (3 : ℝ) ^ b = (3 : ℝ) ^ (a + b) :=
  (Real.rpow_add (by norm_num) a b).symm

private theorem aux_obl_ramp_threshold12_fourth_ieb12_three_rpow_sq (a : ℝ) :
    ((3 : ℝ) ^ a) ^ 2 = (3 : ℝ) ^ (2 * a) := by
  rw [pow_two, aux_obl_ramp_threshold12_fourth_ieb12_three_rpow_add]
  ring_nf

private theorem aux_obl_ramp_threshold12_fourth_ieb12_subunit_envelope_weight {s : ℝ} (hs0 : 0 ≤ s)
    (hs2 : s ≤ 1 / 2) (m : ℕ) :
    (3 : ℝ) ^ (-(3 * s / 2) * (m : ℝ)) * subunitEnvelope s m ^ 2 ≤
      108 * (3 : ℝ) ^ (-(s * (m : ℝ))) := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have henv : subunitEnvelope s m ^ 2 =
      36 * (3 : ℝ) ^ (2 * ((s * (m : ℝ)) / 8) + 2 * ((s * ((m : ℝ) + 1)) / 16)) := by
    unfold subunitEnvelope
    rw [mul_pow, mul_pow, aux_obl_ramp_threshold12_fourth_ieb12_three_rpow_sq, aux_obl_ramp_threshold12_fourth_ieb12_three_rpow_sq, mul_assoc,
      aux_obl_ramp_threshold12_fourth_ieb12_three_rpow_add]
    norm_num
  rw [henv, ← mul_assoc, mul_comm ((3 : ℝ) ^ (-(3 * s / 2) * (m : ℝ))) 36,
    mul_assoc, aux_obl_ramp_threshold12_fourth_ieb12_three_rpow_add]
  have hexp : -(3 * s / 2) * (m : ℝ) +
      (2 * ((s * (m : ℝ)) / 8) + 2 * ((s * ((m : ℝ) + 1)) / 16)) =
      -(s * (m : ℝ)) + s * (1 - (m : ℝ)) / 8 := by ring
  rw [hexp, ← aux_obl_ramp_threshold12_fourth_ieb12_three_rpow_add]
  have hle : s * (1 - (m : ℝ)) / 8 ≤ 1 := by nlinarith
  have hstep : (3 : ℝ) ^ (s * (1 - (m : ℝ)) / 8) ≤ 3 := by
    calc
      (3 : ℝ) ^ (s * (1 - (m : ℝ)) / 8) ≤ (3 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
      _ = 3 := Real.rpow_one 3
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (-(s * (m : ℝ))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  nlinarith [hstep, hpos]

/-- The threshold-12 subunit budget; the collapse constant is `2 * CB`
because the site envelope `12 * ...` is twice `subunitEnvelope`. -/
def aux_obl_ramp_threshold12_fourth_ieb12_subunitBudget (CB : ℝ) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (s : ℝ) (m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  324 * (2 * CB) ^ 2 *
    (goodScaleGradientSlot m omega ^ 2 +
      goodScaleFullSlot s m omega ^ 2 +
      6 * (s⁻¹ * M.delta ^ 2) ^ 2)

theorem aux_obl_ramp_threshold12_fourth_ieb12_subunitBudget_nonneg (CB : ℝ)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (s : ℝ) (m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ aux_obl_ramp_threshold12_fourth_ieb12_subunitBudget CB M s m omega := by
  unfold aux_obl_ramp_threshold12_fourth_ieb12_subunitBudget
  positivity

/-- Every nonpositive-scale annular atom is dominated by the threshold-12
subunit budget.  The pointwise ratio energy is site (iii) of
`obl_ramp_site_inputs`. -/
theorem aux_obl_ramp_threshold12_fourth_ieb12_subunit_atom_le_budget [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ} {s CB : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hsite : ∀ x ∈ cube d (m : ℤ),
      (_root_.SubdiffusiveProcess.Model.aCutoff M L eta x /
            tailCoefficientCubeAverage M L m eta - 1) ^ 2 +
          (tailCoefficientCubeAverage M L m eta /
            _root_.SubdiffusiveProcess.Model.aCutoff M L eta x - 1) ^ 2 ≤
        ((2 * CB) * subunitEnvelope s m * subunitDeviation M m eta) ^ 2)
    {R : SubdiffusiveProcess.CoarseGrainingVocab.TriadicCube d} {j : ℤ} (hj : j ≤ (m : ℤ)) (hscale : R.scale ≤ j - 2)
    (hann : triadicCubeShift R ∈ cube d j \ cube d (j - 1))
    (hneg : R.scale ≤ 0) :
    ENNReal.ofReal ((3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (R.scale : ℝ)))) *
        section6LocalProbeMax M L eta 0
          (tailCoefficientCubeAverage M L m eta) R ≤
      ENNReal.ofReal (aux_obl_ramp_threshold12_fourth_ieb12_subunitBudget CB M s m eta) := by
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hsLower
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  set K : ℝ := ((2 * CB) * subunitEnvelope s m * subunitDeviation M m eta) ^ 2 with hK
  set omega' : _root_.SubdiffusiveProcess.Model.PotentialSample d :=
    translatePotentialSample (triadicCubeShift R) eta with homega'
  have hRdesc : R ∈ descendantsAtScale (originCube d (m : ℤ)) R.scale :=
    annularCube_mem_descendantsAtScale hj hscale hann
  have hpoint : ∀ x ∈ ((Ch02.cubeDomain (originCube d R.scale) :
      Ch02.Domain d) : Set (Vec d)),
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega' x /
            tailCoefficientCubeAverage M L m eta - 1) ^ 2 +
          (tailCoefficientCubeAverage M L m eta /
            _root_.SubdiffusiveProcess.Model.aCutoff M L omega' x - 1) ^ 2 ≤ K := by
    intro x hx
    have hxcube : x ∈ cube d R.scale := by
      exact hx
    have hxR : triadicCubeShift R + x ∈ openCubeSet R := by
      rw [openCubeSet_eq_translateSet_originCube_of_triadicCube,
        mem_translateSet_iff_sub_mem]
      simp only [add_sub_cancel_left]
      exact hxcube
    have hxM : triadicCubeShift R + x ∈ cube d (m : ℤ) :=
      openCubeSet_subset_of_mem_descendantsAtScale
        (scale_le_of_mem_descendantsAtScale hRdesc) hRdesc hxR
    have hxM' : x + triadicCubeShift R ∈ cube d (m : ℤ) := by
      rwa [add_comm] at hxM
    rw [homega', Section6Covariance.aCutoff_translatePotentialSample]
    exact hsite _ hxM'
  have haverage : Ch02.average (Ch02.cubeDomain (originCube d R.scale))
      (fun x =>
        (_root_.SubdiffusiveProcess.Model.aCutoff M L omega' x /
          tailCoefficientCubeAverage M L m eta - 1) ^ 2 +
        (tailCoefficientCubeAverage M L m eta /
          _root_.SubdiffusiveProcess.Model.aCutoff M L omega' x - 1) ^ 2) ≤ K := by
    set U : Ch02.Domain d := Ch02.cubeDomain (originCube d R.scale) with hU
    have ha_pos : ∀ x, 0 < _root_.SubdiffusiveProcess.Model.aCutoff M L omega' x :=
      _root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega'
    have hcontinuous : Continuous (fun x =>
        (_root_.SubdiffusiveProcess.Model.aCutoff M L omega' x /
          tailCoefficientCubeAverage M L m eta - 1) ^ 2 +
          (tailCoefficientCubeAverage M L m eta /
            _root_.SubdiffusiveProcess.Model.aCutoff M L omega' x - 1) ^ 2) :=
      ((((_root_.SubdiffusiveProcess.Model.continuous_aCutoff M L omega').div_const _).sub
        continuous_const).pow 2).add
        (((continuous_const.div
          (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M L omega')
          (fun x => (ha_pos x).ne')).sub continuous_const).pow 2)
    exact average_le_of_le_on U
      ((hcontinuous.continuousOn.integrableOn_compact
        U.isDomain.isBoundedDomain.isBounded.isCompact_closure).mono_set
          subset_closure) hpoint
  have hprobe : section6LocalProbeMax M L eta 0
      (tailCoefficientCubeAverage M L m eta) R ≤ ENNReal.ofReal K :=
    (section6LocalProbeMax_le_ratioEnergy_average M L m eta R).trans
      (ENNReal.ofReal_le_ofReal haverage)
  have hweight : (3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (R.scale : ℝ))) ≤
      (3 : ℝ) ^ (-(3 * s / 2) * (m : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hkr : ((R.scale : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hneg
    nlinarith
  have hw0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (R.scale : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hfinal : (3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (R.scale : ℝ))) * K ≤
      aux_obl_ramp_threshold12_fourth_ieb12_subunitBudget CB M s m eta := by
    set S : ℝ := longRatioGradientTail m eta with hS
    set G : ℝ := supNormOn (cube d (m : ℤ)) (fullShellBlock m eta) with hG
    set Rho : ℝ := _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m : ℝ) + 1) with hRho
    have henv := aux_obl_ramp_threshold12_fourth_ieb12_subunit_envelope_weight (s := s) hs0.le hsUpper m
    have hsplit : subunitDeviation M m eta ^ 2 ≤ 3 * (S ^ 2 + G ^ 2 + Rho ^ 2) := by
      rw [subunitDeviation, ← hS, ← hG, ← hRho]
      exact min_one_add_three_sq_le_three_sum_sq S G Rho
    have hstep1 : (3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (R.scale : ℝ))) * K ≤
        (2 * CB) ^ 2 * (108 * (3 : ℝ) ^ (-(s * (m : ℝ)))) *
          subunitDeviation M m eta ^ 2 := by
      have hKexp : K = (2 * CB) ^ 2 * subunitEnvelope s m ^ 2 *
          subunitDeviation M m eta ^ 2 := by rw [hK]; ring
      rw [hKexp]
      have h1 : (3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (R.scale : ℝ))) *
          ((2 * CB) ^ 2 * subunitEnvelope s m ^ 2 *
            subunitDeviation M m eta ^ 2) =
          (2 * CB) ^ 2 *
            ((3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (R.scale : ℝ))) *
              subunitEnvelope s m ^ 2) * subunitDeviation M m eta ^ 2 := by ring
      rw [h1]
      have henv0 : (0 : ℝ) ≤ subunitEnvelope s m ^ 2 := sq_nonneg _
      have hchain : (3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (R.scale : ℝ))) *
          subunitEnvelope s m ^ 2 ≤ 108 * (3 : ℝ) ^ (-(s * (m : ℝ))) :=
        le_trans (mul_le_mul_of_nonneg_right hweight henv0) henv
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hchain (sq_nonneg _)) (sq_nonneg _)
    have hone : (3 : ℝ) ^ (-(s * (m : ℝ))) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      have : 0 ≤ s * (m : ℝ) := mul_nonneg hs0.le hm0
      linarith
    have hgrad : (3 : ℝ) ^ (-(s * (m : ℝ))) * S ^ 2 ≤
        goodScaleGradientSlot m eta ^ 2 := by
      have hslot : goodScaleGradientSlot m eta = S := by
        rw [hS]
        exact goodScaleGradientSlot_eq_longRatioGradientTail m eta
      rw [hslot]
      calc
        (3 : ℝ) ^ (-(s * (m : ℝ))) * S ^ 2 ≤ 1 * S ^ 2 :=
          mul_le_mul_of_nonneg_right hone (sq_nonneg S)
        _ = S ^ 2 := one_mul _
    have hfull : (3 : ℝ) ^ (-(s * (m : ℝ))) * G ^ 2 ≤
        goodScaleFullSlot s m eta ^ 2 := by
      have hslot : goodScaleFullSlot s m eta ^ 2 =
          (3 : ℝ) ^ (2 * (-(s / 8) * (m : ℝ))) * G ^ 2 := by
        rw [goodScaleFullSlot, mul_pow, aux_obl_ramp_threshold12_fourth_ieb12_three_rpow_sq, ← hG]
      rw [hslot]
      have hexp : -(s * (m : ℝ)) ≤ 2 * (-(s / 8) * (m : ℝ)) := by nlinarith
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp)
        (sq_nonneg G)
    have hdrift : (3 : ℝ) ^ (-(s * (m : ℝ))) * Rho ^ 2 ≤
        6 * (s⁻¹ * M.delta ^ 2) ^ 2 := by
      have hcore := three_rpow_neg_mul_tauSq_sq_le M hsLower
        (t := (m : ℝ) + 1) (by positivity)
      have hshift : (3 : ℝ) ^ (-(s * (m : ℝ))) ≤
          3 * (3 : ℝ) ^ (-(s * ((m : ℝ) + 1))) := by
        have : (3 : ℝ) ^ (-(s * (m : ℝ))) =
            (3 : ℝ) ^ s * (3 : ℝ) ^ (-(s * ((m : ℝ) + 1))) := by
          rw [aux_obl_ramp_threshold12_fourth_ieb12_three_rpow_add]
          congr 1
          ring
        rw [this]
        have hs3 : (3 : ℝ) ^ s ≤ 3 := by
          calc
            (3 : ℝ) ^ s ≤ (3 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 3 := Real.rpow_one 3
        have hp : (0 : ℝ) < (3 : ℝ) ^ (-(s * ((m : ℝ) + 1))) :=
          Real.rpow_pos_of_pos (by norm_num) _
        nlinarith
      have hsq0 : (0 : ℝ) ≤ Rho ^ 2 := sq_nonneg _
      calc
        (3 : ℝ) ^ (-(s * (m : ℝ))) * Rho ^ 2 ≤
            3 * (3 : ℝ) ^ (-(s * ((m : ℝ) + 1))) * Rho ^ 2 :=
          mul_le_mul_of_nonneg_right hshift hsq0
        _ = 3 * ((3 : ℝ) ^ (-(s * ((m : ℝ) + 1))) *
            (_root_.SubdiffusiveProcess.Model.tauSq M.P * ((m : ℝ) + 1)) ^ 2) := by
          rw [hRho]; ring
        _ ≤ 3 * (2 * (s⁻¹) ^ 2 * M.delta ^ 4) :=
          mul_le_mul_of_nonneg_left hcore (by norm_num)
        _ = 6 * (s⁻¹ * M.delta ^ 2) ^ 2 := by ring
    refine hstep1.trans ?_
    unfold aux_obl_ramp_threshold12_fourth_ieb12_subunitBudget
    have hexpand : (2 * CB) ^ 2 *
        (108 * (3 : ℝ) ^ (-(s * (m : ℝ)))) * subunitDeviation M m eta ^ 2 ≤
        (2 * CB) ^ 2 * (108 * (3 : ℝ) ^ (-(s * (m : ℝ)))) *
          (3 * (S ^ 2 + G ^ 2 + Rho ^ 2)) := by
      refine mul_le_mul_of_nonneg_left hsplit ?_
      have : (0 : ℝ) ≤ 108 * (3 : ℝ) ^ (-(s * (m : ℝ))) := by positivity
      positivity
    refine hexpand.trans ?_
    have hsum : (3 : ℝ) ^ (-(s * (m : ℝ))) * (S ^ 2 + G ^ 2 + Rho ^ 2) ≤
        goodScaleGradientSlot m eta ^ 2 + goodScaleFullSlot s m eta ^ 2 +
          6 * (s⁻¹ * M.delta ^ 2) ^ 2 := by
      have hexp2 : (3 : ℝ) ^ (-(s * (m : ℝ))) * (S ^ 2 + G ^ 2 + Rho ^ 2) =
          (3 : ℝ) ^ (-(s * (m : ℝ))) * S ^ 2 +
          (3 : ℝ) ^ (-(s * (m : ℝ))) * G ^ 2 +
          (3 : ℝ) ^ (-(s * (m : ℝ))) * Rho ^ 2 := by ring
      rw [hexp2]
      exact add_le_add (add_le_add hgrad hfull) hdrift
    have hrearrange : (2 * CB) ^ 2 *
        (108 * (3 : ℝ) ^ (-(s * (m : ℝ)))) * (3 * (S ^ 2 + G ^ 2 + Rho ^ 2)) =
        324 * (2 * CB) ^ 2 *
          ((3 : ℝ) ^ (-(s * (m : ℝ))) * (S ^ 2 + G ^ 2 + Rho ^ 2)) := by ring
    rw [hrearrange]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  calc
    ENNReal.ofReal ((3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (R.scale : ℝ)))) *
        section6LocalProbeMax M L eta 0
          (tailCoefficientCubeAverage M L m eta) R ≤
        ENNReal.ofReal ((3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (R.scale : ℝ)))) *
          ENNReal.ofReal K := by
      gcongr
    _ = ENNReal.ofReal ((3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (R.scale : ℝ))) * K) :=
      (ENNReal.ofReal_mul hw0).symm
    _ ≤ ENNReal.ofReal (aux_obl_ramp_threshold12_fourth_ieb12_subunitBudget CB M s m eta) :=
      ENNReal.ofReal_le_ofReal hfinal

/-! ## The complete annular supremum and the base display -/

/-- The site-(iii) hypothesis of `obl_ramp_site_inputs` at `L = m`, written
with the upstream envelope (`12 * ... = 2 * subunitEnvelope`). -/
def aux_obl_ramp_threshold12_fourth_ieb12_SiteThree (CB : ℝ) (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s : ℝ)
    (L m : ℕ) (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d) : Prop :=
  ∀ x ∈ cube d (m : ℤ),
    (_root_.SubdiffusiveProcess.Model.aCutoff M L eta x /
          tailCoefficientCubeAverage M L m eta - 1) ^ 2 +
        (tailCoefficientCubeAverage M L m eta /
          _root_.SubdiffusiveProcess.Model.aCutoff M L eta x - 1) ^ 2 ≤
      ((2 * CB) * subunitEnvelope s m * subunitDeviation M m eta) ^ 2

theorem aux_obl_ramp_threshold12_fourth_ieb12_annularSupTwo_le_budget [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ} (hmL : m ≤ L) {s CB : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hresp : GoodResponse M none m 0 1 s eta)
    (hsiteTwo : aux_obl_ramp_threshold12_fourth_ieb12_SiteTwo CB M s L m eta)
    (hsiteThree : aux_obl_ramp_threshold12_fourth_ieb12_SiteThree CB M s L m eta) :
    annularSupTwo s (m : ℤ)
        (section6LocalProbeMax M L eta 0 (tailCoefficientCubeAverage M L m eta)) ≤
      ENNReal.ofReal (aux_obl_ramp_threshold12_fourth_ieb12_positiveBudget CB M s m eta +
        aux_obl_ramp_threshold12_fourth_ieb12_subunitBudget CB M s m eta) := by
  refine iSup_le fun p => ?_
  rcases le_or_gt 0 p.1.1.scale with hscale0 | hscaleneg
  · refine (aux_obl_ramp_threshold12_fourth_ieb12_positive_annular_atom_le_budget M hmL hsLower eta hresp hsiteTwo
      p hscale0).trans (ENNReal.ofReal_le_ofReal ?_)
    have := aux_obl_ramp_threshold12_fourth_ieb12_subunitBudget_nonneg CB M s m eta
    linarith
  · obtain ⟨hj, hsc, hann⟩ := p.2
    refine (aux_obl_ramp_threshold12_fourth_ieb12_subunit_atom_le_budget M hsLower hsUpper eta hsiteThree
      hj hsc hann hscaleneg.le).trans (ENNReal.ofReal_le_ofReal ?_)
    have := aux_obl_ramp_threshold12_fourth_ieb12_positiveBudget_nonneg CB M s m eta
    linarith

/-- The square of the threshold-12 base constant. -/
def aux_obl_ramp_threshold12_fourth_ieb12_squareConstant (CB : ℝ) : ℝ := 384 + 1506816 * CB ^ 2

private theorem aux_obl_ramp_threshold12_fourth_ieb12_budget_le_square (CB A D Bs Bf Bg : ℝ) :
    192 * ((2 * A ^ 2 + 36 * CB ^ 2 * (Bg ^ 2 + Bs ^ 2 + 2 * D ^ 2)) +
        324 * (2 * CB) ^ 2 * (Bg ^ 2 + Bf ^ 2 + 6 * D ^ 2)) ≤
      aux_obl_ramp_threshold12_fourth_ieb12_squareConstant CB * (A ^ 2 + D ^ 2 + Bs ^ 2 + Bf ^ 2 + Bg ^ 2) := by
  unfold aux_obl_ramp_threshold12_fourth_ieb12_squareConstant
  have h1 := mul_nonneg (sq_nonneg CB) (sq_nonneg A)
  have h2 := mul_nonneg (sq_nonneg CB) (sq_nonneg Bs)
  have h3 := mul_nonneg (sq_nonneg CB) (sq_nonneg Bf)
  have h4 := mul_nonneg (sq_nonneg CB) (sq_nonneg Bg)
  have h5 := sq_nonneg D
  have h6 := sq_nonneg Bs
  have h7 := sq_nonneg Bf
  have h8 := sq_nonneg Bg
  have hexp : aux_obl_ramp_threshold12_fourth_ieb12_squareConstant CB * (A ^ 2 + D ^ 2 + Bs ^ 2 + Bf ^ 2 + Bg ^ 2) -
      192 * ((2 * A ^ 2 + 36 * CB ^ 2 * (Bg ^ 2 + Bs ^ 2 + 2 * D ^ 2)) +
        324 * (2 * CB) ^ 2 * (Bg ^ 2 + Bf ^ 2 + 6 * D ^ 2)) =
      1506816 * (CB ^ 2 * A ^ 2) + 384 * D ^ 2 + 384 * Bs ^ 2 + 384 * Bf ^ 2 +
        384 * Bg ^ 2 + 1499904 * (CB ^ 2 * Bs ^ 2) + 1257984 * (CB ^ 2 * Bf ^ 2) +
        1251072 * (CB ^ 2 * Bg ^ 2) := by
    unfold aux_obl_ramp_threshold12_fourth_ieb12_squareConstant
    ring
  unfold aux_obl_ramp_threshold12_fourth_ieb12_squareConstant at hexp
  linarith

/-- Nonnegativity of the five display slots. -/
private theorem aux_obl_ramp_threshold12_fourth_ieb12_slots_nonneg
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {m : ℕ} {s : ℝ} (hs0 : 0 < s)
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ goodScaleResponseSlot M s m eta ∧ 0 ≤ s⁻¹ * M.delta ^ 2 ∧
      0 ≤ goodScaleShellSlot s m eta ∧ 0 ≤ goodScaleFullSlot s m eta ∧
      0 ≤ goodScaleGradientSlot m eta := by
  refine ⟨?_, mul_nonneg (inv_nonneg.2 hs0.le) (sq_nonneg _), ?_, ?_, ?_⟩
  · refine Real.sSup_nonneg ?_
    rintro a ⟨j, n, -, -, z, -, -, rfl⟩
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)
  · refine Real.sSup_nonneg ?_
    rintro a ⟨j, -, rfl⟩
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (aux_obl_ramp_threshold12_fourth_ieb12_supNormOn_nonneg _ _)
  · exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (aux_obl_ramp_threshold12_fourth_ieb12_supNormOn_nonneg _ _)
  · rw [goodScaleGradientSlot_eq_longRatioGradientTail]
    exact longRatioGradientTail_nonneg m eta

/-- The square-root arithmetic of the base display. -/
private theorem aux_obl_ramp_threshold12_fourth_ieb12_sqrt_budget_le
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {m : ℕ} {s CB : ℝ} (hs0 : 0 < s)
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    (192 * (aux_obl_ramp_threshold12_fourth_ieb12_positiveBudget CB M s m eta +
        aux_obl_ramp_threshold12_fourth_ieb12_subunitBudget CB M s m eta)) ^ (1 / 2 : ℝ) ≤
      Real.sqrt (aux_obl_ramp_threshold12_fourth_ieb12_squareConstant CB) *
        (goodScaleResponseSlot M s m eta + s⁻¹ * M.delta ^ 2 +
          goodScaleShellSlot s m eta + goodScaleFullSlot s m eta +
          goodScaleGradientSlot m eta) := by
  obtain ⟨hA0, hD0, hBs0, hBf0, hBg0⟩ := aux_obl_ramp_threshold12_fourth_ieb12_slots_nonneg M (m := m) hs0 eta
  set A : ℝ := goodScaleResponseSlot M s m eta with hAdef
  set D : ℝ := s⁻¹ * M.delta ^ 2 with hDdef
  set Bs : ℝ := goodScaleShellSlot s m eta with hBsdef
  set Bf : ℝ := goodScaleFullSlot s m eta with hBfdef
  set Bg : ℝ := goodScaleGradientSlot m eta with hBgdef
  set Sigma : ℝ := A + D + Bs + Bf + Bg with hSigmadef
  have hSigma0 : 0 ≤ Sigma := by rw [hSigmadef]; linarith
  rw [← Real.sqrt_eq_rpow]
  have hsq : A ^ 2 + D ^ 2 + Bs ^ 2 + Bf ^ 2 + Bg ^ 2 ≤ Sigma ^ 2 := by
    rw [hSigmadef]
    nlinarith [mul_nonneg hA0 hD0, mul_nonneg hA0 hBs0, mul_nonneg hA0 hBf0,
      mul_nonneg hA0 hBg0, mul_nonneg hD0 hBs0, mul_nonneg hD0 hBf0,
      mul_nonneg hD0 hBg0, mul_nonneg hBs0 hBf0, mul_nonneg hBs0 hBg0,
      mul_nonneg hBf0 hBg0]
  have hcoef : 192 * (aux_obl_ramp_threshold12_fourth_ieb12_positiveBudget CB M s m eta +
      aux_obl_ramp_threshold12_fourth_ieb12_subunitBudget CB M s m eta) ≤ aux_obl_ramp_threshold12_fourth_ieb12_squareConstant CB *
      (A ^ 2 + D ^ 2 + Bs ^ 2 + Bf ^ 2 + Bg ^ 2) := by
    rw [aux_obl_ramp_threshold12_fourth_ieb12_positiveBudget, aux_obl_ramp_threshold12_fourth_ieb12_subunitBudget,
      ← hAdef, ← hDdef, ← hBsdef, ← hBfdef, ← hBgdef]
    exact aux_obl_ramp_threshold12_fourth_ieb12_budget_le_square CB A D Bs Bf Bg
  have hT0 : 0 ≤ aux_obl_ramp_threshold12_fourth_ieb12_squareConstant CB := by
    unfold aux_obl_ramp_threshold12_fourth_ieb12_squareConstant
    positivity
  calc
    Real.sqrt (192 * (aux_obl_ramp_threshold12_fourth_ieb12_positiveBudget CB M s m eta +
        aux_obl_ramp_threshold12_fourth_ieb12_subunitBudget CB M s m eta)) ≤
        Real.sqrt (aux_obl_ramp_threshold12_fourth_ieb12_squareConstant CB * Sigma ^ 2) :=
      Real.sqrt_le_sqrt (hcoef.trans (mul_le_mul_of_nonneg_left hsq hT0))
    _ = Real.sqrt (aux_obl_ramp_threshold12_fourth_ieb12_squareConstant CB) * Sigma := by
      rw [Real.sqrt_mul hT0, Real.sqrt_sq hSigma0]

/-- The threshold-12 base display for the `ℝ≥0∞`-valued paper error itself
(no `toReal`): the weighted descendant series is bounded through the annular
supremum, so the paper error is finite on the event. -/
theorem aux_obl_ramp_threshold12_fourth_ieb12_paperError_le_base [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ} (hmL : m ≤ L) {s CB : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hresp : GoodResponse M none m 0 1 s eta)
    (hsiteTwo : aux_obl_ramp_threshold12_fourth_ieb12_SiteTwo CB M s L m eta)
    (hsiteThree : aux_obl_ramp_threshold12_fourth_ieb12_SiteThree CB M s L m eta) :
    paperHomogenizationError (originCube d (m : ℤ)) (m : ℤ) s .infinity (.finite 2)
        (aCutoffFamily M L eta) (tailCoefficientCubeAverage M L m eta) ≤
      ENNReal.ofReal (Real.sqrt (aux_obl_ramp_threshold12_fourth_ieb12_squareConstant CB) *
        (goodScaleResponseSlot M s m eta + s⁻¹ * M.delta ^ 2 +
          goodScaleShellSlot s m eta + goodScaleFullSlot s m eta +
          goodScaleGradientSlot m eta)) := by
  have hdim : 2 ≤ d := M.shellPrefix.dimension
  have hd1 : 1 ≤ d := by omega
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hsLower
  set alpha : ℝ := tailCoefficientCubeAverage M L m eta with halpha
  set g : SubdiffusiveProcess.CoarseGrainingVocab.TriadicCube d → ℝ≥0∞ :=
    section6LocalProbeMax M L eta 0 alpha with hg
  set B : ℝ := aux_obl_ramp_threshold12_fourth_ieb12_positiveBudget CB M s m eta +
    aux_obl_ramp_threshold12_fourth_ieb12_subunitBudget CB M s m eta with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    have h1 := aux_obl_ramp_threshold12_fourth_ieb12_positiveBudget_nonneg CB M s m eta
    have h2 := aux_obl_ramp_threshold12_fourth_ieb12_subunitBudget_nonneg CB M s m eta
    linarith
  have hseries := tsum_geometricWeight_descendantSup_le_annularSup hs0 hsUpper hd1 m g
    (fun n _ => section6LocalProbeMax_originCube_le_onion M L eta 0 alpha n)
  have hthree := annularSup_le_three_mul_annularSupTwo (m := (m : ℤ)) hsUpper g
    (section6LocalProbeMax_le_child M L eta 0 alpha)
  have hstep2 : annularSupTwo s (m : ℤ) g ≤ ENNReal.ofReal B :=
    aux_obl_ramp_threshold12_fourth_ieb12_annularSupTwo_le_budget M hmL hsLower hsUpper eta hresp hsiteTwo hsiteThree
  have htotal : ∑' l : ℕ, ENNReal.ofReal (Ch02.geometricWeight s 2 l) *
      (⨆ R : {R : SubdiffusiveProcess.CoarseGrainingVocab.TriadicCube d //
          R ∈ descendantsAtScale (originCube d (m : ℤ)) ((m : ℤ) - (l : ℤ))},
        g R.1) ≤ ENNReal.ofReal (192 * B) := by
    calc
      _ ≤ 64 * annularSup s (m : ℤ) g := hseries
      _ ≤ 64 * (3 * annularSupTwo s (m : ℤ) g) := by gcongr
      _ ≤ 64 * (3 * ENNReal.ofReal B) := by gcongr
      _ = 192 * ENNReal.ofReal B := by ring
      _ = ENNReal.ofReal (192 * B) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 192), ENNReal.ofReal_ofNat]
  have hrw : (∑' l : ℕ, ENNReal.ofReal (Ch02.geometricWeight s 2 l) *
      paperMaxDescendantProbeAtScale (originCube d (m : ℤ)) ((m : ℤ) - (l : ℤ))
        (aCutoffFamily M L eta) alpha) =
      ∑' l : ℕ, ENNReal.ofReal (Ch02.geometricWeight s 2 l) *
      (⨆ R : {R : SubdiffusiveProcess.CoarseGrainingVocab.TriadicCube d //
          R ∈ descendantsAtScale (originCube d (m : ℤ)) ((m : ℤ) - (l : ℤ))},
        g R.1) := by
    refine tsum_congr fun l => ?_
    rw [paperMaxDescendantProbeAtScale_aCutoffFamily_eq_transported]
    congr 1
    refine iSup_congr fun R => ?_
    rw [hg, section6LocalProbeMax, Section6Covariance.translatePotentialSample_zero,
      scale_eq_of_mem_descendantsAtScale R.2]
  rw [paperHomogenizationError_infinity_two_eq_weighted_series, hrw]
  calc
    _ ≤ (ENNReal.ofReal (192 * B)) ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow htotal (by norm_num)
    _ = ENNReal.ofReal ((192 * B) ^ (1 / 2 : ℝ)) :=
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)
    _ ≤ _ := ENNReal.ofReal_le_ofReal (aux_obl_ramp_threshold12_fourth_ieb12_sqrt_budget_le M hs0 eta)


/-! ## Response truncation (upstream `RefinedLocalMathcalE`) -/

private theorem aux_obl_ramp_threshold12_fourth_ieb12_truncatedResponseSet_bddAbove
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {m : ℕ} {s : ℝ}
    (hs : 0 ≤ s) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    BddAbove {r : ℝ | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧
      ∃ z : Vec d, OnTriadicGrid n (z - 0) ∧
        z - 0 ∈ cube d j \ cube d (j - 1) ∧
        r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
          Real.sqrt (min (sSup {q : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
            q = section6Response M n (min n (none.getD n)) omega z e}) 1)} := by
  refine ⟨1, ?_⟩
  rintro r ⟨j, n, hjm, hnj, z, hzgrid, hzann, rfl⟩
  have hnm : n ≤ m := by omega
  have hgap : 0 ≤ (m : ℝ) - (n : ℝ) := by
    exact sub_nonneg.mpr (Nat.cast_le.2 hnm)
  have hw : (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hgap
  have hsqrt : Real.sqrt (min
      (sSup {q : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
        q = section6Response M n (min n (none.getD n)) omega z e}) 1) ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (min_le_right _ 1)
  exact (mul_le_mul hw hsqrt (Real.sqrt_nonneg _) (by positivity)).trans_eq (mul_one 1)

/-- The untruncated response slot is bounded by the truncated response slot in
`accumulatedError`, plus `epsilon^8`; only the response clause is read. -/
theorem aux_obl_ramp_threshold12_fourth_ieb12_responseSlot_le_accumulatedError
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {m : ℕ} {epsilon s : ℝ}
    (hepsilon : 0 ≤ epsilon) (hs : 0 ≤ s)
    {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d}
    (hresp : GoodResponse M none m 0 epsilon s omega) :
    goodScaleResponseSlot M s m omega ≤
      accumulatedError M none m 0 s omega + epsilon ^ 8 := by
  unfold goodScaleResponseSlot
  let S : Set ℝ := {r : ℝ | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧
    ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d j \ cube d (j - 1) ∧
    r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
      Real.sqrt (sSup {q : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
        q = section6Response M n n omega z e})}
  change sSup S ≤ _
  by_cases hS : S.Nonempty
  · apply csSup_le hS
    intro r hr
    rcases hr with ⟨j, n, hjm, hnj, z, hzgrid, hzann, rfl⟩
    let A : Set ℝ := {q : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
      q = section6Response M n (min n (none.getD n)) omega z e}
    have hAbdd : BddAbove A := by
      simpa only [A, Option.getD_none, min_self] using
        bddAbove_section6Response_unitSphere M n n omega z
    have hAne : A.Nonempty := by
      have hd : 2 ≤ d := M.shellPrefix.dimension
      let i : Fin d := ⟨0, by omega⟩
      let e : Vec d := Pi.single i 1
      refine ⟨section6Response M n (min n (none.getD n)) omega z e, e, ?_, rfl⟩
      rw [vecNormSq, vecDot, Finset.sum_eq_single i]
      · simp [e]
      · intro b _ hbi
        simp [e, Pi.single_eq_of_ne hbi]
      · simp
    have hresp' : sSup A ≤ epsilon ^ 2 *
        (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 8) := by
      refine csSup_le hAne ?_
      intro q hq
      rcases hq with ⟨e, he, rfl⟩
      simpa only [A, sub_zero, Option.getD_none, min_self] using hresp j n hjm hnj z
        (by simpa only [sub_zero] using hzgrid)
        (by simpa only [sub_zero] using hzann) e he
    have hsqrt : Real.sqrt (sSup A) ≤ epsilon *
        (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 16) := by
      have hright : 0 ≤ epsilon *
          (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 16) := by positivity
      rw [Real.sqrt_le_iff]
      refine ⟨hright, hresp'.trans_eq ?_⟩
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      ring
    let t : ℝ := (3 : ℝ) ^ (-(s * ((m : ℝ) - (n : ℝ))) / 16)
    have ht0 : 0 < t := Real.rpow_pos_of_pos (by norm_num) _
    have htinv : t⁻¹ =
        (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 16) := by
      dsimp only [t]
      rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      ring
    have htrunc := Section6Holder.pow_eight_mul_le_truncated_add_pow_eight ht0 hepsilon
      (Real.sqrt_nonneg _) (by rwa [htinv])
    have hsqrtMin : min (Real.sqrt (sSup A)) 1 =
        Real.sqrt (min (sSup A) 1) := by
      have hmono : Monotone Real.sqrt := fun _ _ h ↦ Real.sqrt_le_sqrt h
      symm
      calc
        Real.sqrt (min (sSup A) 1) =
            min (Real.sqrt (sSup A)) (Real.sqrt 1) := hmono.map_min
        _ = min (Real.sqrt (sSup A)) 1 := by rw [Real.sqrt_one]
    have hweight : t ^ 8 =
        (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) := by
      dsimp only [t]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      ring
    rw [hweight, hsqrtMin] at htrunc
    have htruncated :
        (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
            Real.sqrt (min (sSup A) 1) ≤
          accumulatedError M none m 0 s omega := by
      apply Section6Holder.truncatedResponseAtom_le_accumulatedError M none s m 0 omega
        (aux_obl_ramp_threshold12_fourth_ieb12_truncatedResponseSet_bddAbove M hs omega) hjm hnj
      · simpa only [sub_zero] using hzgrid
      · simpa only [sub_zero] using hzann
    have hadd := add_le_add htruncated (le_refl (epsilon ^ 8))
    simpa only [A, Option.getD_none, min_self] using htrunc.trans hadd
  · have hEmpty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    rw [hEmpty, Real.sSup_empty]
    exact add_nonneg (Section6Holder.accumulatedError_nonneg M none s m 0 omega)
      (pow_nonneg hepsilon 8)

/-! ## The epsilon cap (upstream provider reads; only `GoodFieldOne` and
`GoodResponse` are consumed) -/

private theorem aux_obl_ramp_threshold12_fourth_ieb12_bddAbove_abs_values_cube_int {k : ℤ} {f : Vec d → ℝ}
    (hf : Continuous f) :
    BddAbove {a : ℝ | ∃ x ∈ cube d k, a = |f x|} := by
  let Q := originCube d k
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (cubeCenter Q) (cubeRadius Q)).exists_bound_of_continuousOn
      ((continuous_abs.comp hf).continuousOn)
  refine ⟨max 0 C, ?_⟩
  rintro a ⟨x, hx, rfl⟩
  have hx' : x ∈ Metric.closedBall (cubeCenter Q) (cubeRadius Q) :=
    cubeSet_subset_closedBall Q (openCubeSet_subset_cubeSet Q hx)
  have h := hC x hx'
  simpa only [Function.comp_apply, Real.norm_eq_abs, abs_abs] using
    h.trans (le_max_right _ _)

private theorem aux_obl_ramp_threshold12_fourth_ieb12_abs_apply_le_supNormOn_cube_int {k : ℤ} {f : Vec d → ℝ}
    (hf : Continuous f) {x : Vec d} (hx : x ∈ cube d k) :
    |f x| ≤ supNormOn (cube d k) f :=
  le_csSup (aux_obl_ramp_threshold12_fourth_ieb12_bddAbove_abs_values_cube_int hf) ⟨x, hx, rfl⟩

private theorem aux_obl_ramp_threshold12_fourth_ieb12_translatedCube_zero (k : ℤ) :
    translatedCube d k 0 = cube d k := by
  unfold translatedCube
  simp

private theorem aux_obl_ramp_threshold12_fourth_ieb12_shellGradient_continuous
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) :
    Continuous (shellGradient g) := by
  unfold shellGradient
  apply continuous_pi
  intro i
  exact (_root_.SubdiffusiveProcess.Model.PotentialField.deriv g).continuous.clm_apply
    continuous_const

private theorem aux_obl_ramp_threshold12_fourth_ieb12_shellControl_continuous
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) (i : ℕ) :
    Continuous (fun x => |g x| + (3 : ℝ) ^ i *
      euclideanNorm (shellGradient g x)) := by
  have hnorm : Continuous (fun x => euclideanNorm (shellGradient g x)) := by
    rw [show (fun x => euclideanNorm (shellGradient g x)) =
        fun x => ‖HilbertVec.ofVec (shellGradient g x)‖ by
      funext x
      rw [euclideanNorm_eq_norm_ofVec]]
    exact continuous_norm.comp
      ((HilbertVec.ofVecL d).continuous.comp (aux_obl_ramp_threshold12_fourth_ieb12_shellGradient_continuous g))
  exact (continuous_abs.comp g.1.1.continuous).add (continuous_const.mul hnorm)

private theorem aux_obl_ramp_threshold12_fourth_ieb12_sum_abs_le_of_goodFieldOne (m q : ℕ) {epsilon s : ℝ}
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hgood : GoodFieldOne m 0 epsilon s omega)
    {T : Finset ℕ} (hT : T ⊆ Finset.Icc (m - q) (m + q))
    {x : Vec d} (hx : x ∈ cube d (m : ℤ)) :
    ∑ i ∈ T, |omega i x| ≤ epsilon * (3 : ℝ) ^ ((s * (q : ℝ)) / 8) := by
  have hevent := hgood q
  rw [aux_obl_ramp_threshold12_fourth_ieb12_translatedCube_zero] at hevent
  have hxlarge : x ∈ cube d ((m : ℤ) + 1 + (q : ℤ)) := by
    refine openCubeSet_originCube_subset_of_scale_le ?_ hx
    omega
  have hterm : ∀ i ∈ Finset.Icc (m - q) (m + q), |omega i x| ≤
      supNormOn (cube d ((m : ℤ) + 1 + (q : ℤ))) (fun y =>
        |omega i y| + (3 : ℝ) ^ i * euclideanNorm (shellGradient (omega i) y)) := by
    intro i _
    have hcontrol := aux_obl_ramp_threshold12_fourth_ieb12_abs_apply_le_supNormOn_cube_int
      (aux_obl_ramp_threshold12_fourth_ieb12_shellControl_continuous (omega i) i) hxlarge
    have hnonneg : 0 ≤ |omega i x| + (3 : ℝ) ^ i *
        euclideanNorm (shellGradient (omega i) x) :=
      add_nonneg (abs_nonneg _)
        (mul_nonneg (by positivity) (euclideanNorm_nonneg _))
    rw [abs_of_nonneg hnonneg] at hcontrol
    refine le_trans ?_ hcontrol
    have : 0 ≤ (3 : ℝ) ^ i * euclideanNorm (shellGradient (omega i) x) :=
      mul_nonneg (by positivity) (euclideanNorm_nonneg _)
    linarith
  calc
    ∑ i ∈ T, |omega i x| ≤ ∑ i ∈ Finset.Icc (m - q) (m + q), |omega i x| :=
      Finset.sum_le_sum_of_subset_of_nonneg hT (fun i _ _ => abs_nonneg _)
    _ ≤ ∑ i ∈ Finset.Icc (m - q) (m + q),
        supNormOn (cube d ((m : ℤ) + 1 + (q : ℤ))) (fun y =>
          |omega i y| + (3 : ℝ) ^ i *
            euclideanNorm (shellGradient (omega i) y)) :=
      Finset.sum_le_sum hterm
    _ ≤ epsilon * (3 : ℝ) ^ ((s * (q : ℝ)) / 8) := hevent

private theorem aux_obl_ramp_threshold12_fourth_ieb12_supNormOn_shellBlock_le_of_goodFieldOne
    (m j : ℕ) (hj : j ≤ m) {epsilon s : ℝ}
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hgood : GoodFieldOne m 0 epsilon s omega) :
    supNormOn (cube d (m : ℤ)) (shellBlock m j omega) ≤
      epsilon * (3 : ℝ) ^ ((s * ((m - j : ℕ) : ℝ)) / 8) := by
  refine csSup_le ?_ ?_
  · exact ⟨|shellBlock m j omega 0|, 0, aux_obl_ramp_threshold12_fourth_ieb12_zero_mem_cube (m : ℤ), rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hsubset : Finset.Icc (j + 1) m ⊆
        Finset.Icc (m - (m - j)) (m + (m - j)) := by
      intro i hi
      simp only [Finset.mem_Icc] at hi ⊢
      omega
    have hsum := aux_obl_ramp_threshold12_fourth_ieb12_sum_abs_le_of_goodFieldOne m (m - j) omega hgood hsubset hx
    refine le_trans ?_ hsum
    exact Finset.abs_sum_le_sum_abs _ _

private theorem aux_obl_ramp_threshold12_fourth_ieb12_supNormOn_fullShellBlock_le_of_goodFieldOne
    (m : ℕ) {epsilon s : ℝ}
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hgood : GoodFieldOne m 0 epsilon s omega) :
    supNormOn (cube d (m : ℤ)) (fullShellBlock m omega) ≤
      epsilon * (3 : ℝ) ^ ((s * (m : ℝ)) / 8) := by
  refine csSup_le ?_ ?_
  · exact ⟨|fullShellBlock m omega 0|, 0, aux_obl_ramp_threshold12_fourth_ieb12_zero_mem_cube (m : ℤ), rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hsubset : Finset.range (m + 1) ⊆ Finset.Icc (m - m) (m + m) := by
      intro i hi
      simp only [Finset.mem_Icc, Finset.mem_range] at hi ⊢
      omega
    have hsum := aux_obl_ramp_threshold12_fourth_ieb12_sum_abs_le_of_goodFieldOne m m omega hgood hsubset hx
    refine le_trans ?_ hsum
    exact Finset.abs_sum_le_sum_abs _ _

theorem aux_obl_ramp_threshold12_fourth_ieb12_goodScaleShellSlot_le (m : ℕ) {epsilon s : ℝ}
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hgood : GoodFieldOne m 0 epsilon s omega) :
    goodScaleShellSlot s m omega ≤ epsilon := by
  refine csSup_le ⟨_, m, le_rfl, rfl⟩ ?_
  rintro _ ⟨j, hj, rfl⟩
  have hgap : (m : ℝ) - (j : ℝ) = ((m - j : ℕ) : ℝ) := by
    rw [Nat.cast_sub hj]
  have hsup := aux_obl_ramp_threshold12_fourth_ieb12_supNormOn_shellBlock_le_of_goodFieldOne m j hj omega hgood
  have hw : (0 : ℝ) ≤ (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  calc
    (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
        supNormOn (cube d (m : ℤ)) (shellBlock m j omega) ≤
        (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
          (epsilon * (3 : ℝ) ^ ((s * ((m - j : ℕ) : ℝ)) / 8)) :=
      mul_le_mul_of_nonneg_left hsup hw
    _ = epsilon := by
      rw [← hgap, ← mul_assoc, mul_comm _ epsilon, mul_assoc,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      rw [show -(s / 8) * ((m : ℝ) - (j : ℝ)) + s * ((m : ℝ) - (j : ℝ)) / 8 = 0 by
        ring]
      rw [Real.rpow_zero, mul_one]

theorem aux_obl_ramp_threshold12_fourth_ieb12_goodScaleFullSlot_le (m : ℕ) {epsilon s : ℝ}
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hgood : GoodFieldOne m 0 epsilon s omega) :
    goodScaleFullSlot s m omega ≤ epsilon := by
  have hsup := aux_obl_ramp_threshold12_fourth_ieb12_supNormOn_fullShellBlock_le_of_goodFieldOne m omega hgood
  have hw : (0 : ℝ) ≤ (3 : ℝ) ^ (-(s / 8) * (m : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  unfold goodScaleFullSlot
  calc
    (3 : ℝ) ^ (-(s / 8) * (m : ℝ)) *
        supNormOn (cube d (m : ℤ)) (fullShellBlock m omega) ≤
        (3 : ℝ) ^ (-(s / 8) * (m : ℝ)) *
          (epsilon * (3 : ℝ) ^ ((s * (m : ℝ)) / 8)) :=
      mul_le_mul_of_nonneg_left hsup hw
    _ = epsilon := by
      rw [← mul_assoc, mul_comm _ epsilon, mul_assoc,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      rw [show -(s / 8) * (m : ℝ) + s * (m : ℝ) / 8 = 0 by ring]
      rw [Real.rpow_zero, mul_one]

theorem aux_obl_ramp_threshold12_fourth_ieb12_responseSlot_le_epsilon
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {m : ℕ} {epsilon s : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hs0 : 0 ≤ s)
    {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d}
    (hresp : GoodResponse M none m 0 epsilon s omega) :
    goodScaleResponseSlot M s m omega ≤ epsilon := by
  unfold goodScaleResponseSlot
  exact Real.sSup_le (fun r hr => aux_obl_ramp_threshold12_fourth_ieb12_response_atom_le M hepsilon0 hs0 hresp hr)
    hepsilon0

/-! ## The `m ≤ L` half of the fourth conjunct at threshold 12 -/

/-- **Threshold-12 coarse error below the cutoff.**  The fourth conjunct of
`product_threshold_regularities d 12`, restricted to `m ≤ L`: both the
`min epsilon` display and the `C * epsilon` cap, with one dimension-only
constant chosen before the model. -/
theorem aux_obl_ramp_threshold12_fourth_scale_le_cutoff_error (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ L : ℕ,
      ∀ s ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ),
        _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ s * Real.log 3 / 16 →
        ∀ epsilon ∈ Set.Icc (s⁻¹ * M.delta ^ 2) 1, ∀ m : ℕ, m ≤ L → ∀ z : Vec d,
          ∀ ω,
            indicatorValue (_root_.SubdiffusiveProcess.Paper.product_threshold_good_scale d M 12 (some L) m z epsilon s)
                (fun ω' => section6HomogenizationError M s L m ω' z) ω ≤
              C * min epsilon
                (s⁻¹ * M.delta ^ 2 + epsilon ^ 8 +
                  accumulatedError M (some L) m z s ω) ∧
            indicatorValue (_root_.SubdiffusiveProcess.Paper.product_threshold_good_scale d M 12 (some L) m z epsilon s)
                (fun ω' => section6HomogenizationError M s L m ω' z) ω ≤ C * epsilon := by
  obtain ⟨CB, hCB, hsites⟩ := _root_.SubdiffusiveProcess.Paper.obl_ramp_site_inputs d
  have hT0 : 0 < aux_obl_ramp_threshold12_fourth_ieb12_squareConstant CB := by
    unfold aux_obl_ramp_threshold12_fourth_ieb12_squareConstant
    positivity
  set K : ℝ := Real.sqrt (aux_obl_ramp_threshold12_fourth_ieb12_squareConstant CB) with hKdef
  have hK0 : 0 < K := Real.sqrt_pos.2 hT0
  refine ⟨7 * K, by positivity, ?_⟩
  intro M L s hs htau epsilon hepsilon m hmL z omega
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hD0 : 0 ≤ s⁻¹ * M.delta ^ 2 := mul_nonneg (inv_nonneg.2 hs0.le) (sq_nonneg _)
  have heps0' : 0 ≤ epsilon := hD0.trans hepsilon.1
  have hEsome0 := Section6Holder.accumulatedError_nonneg M (some L) s m z omega
  by_cases homega : omega ∈ _root_.SubdiffusiveProcess.Paper.product_threshold_good_scale d M 12 (some L) m z epsilon s
  · simp only [indicatorValue, ite_eq_left homega]
    obtain ⟨hBpos, hspos, hs1, heps0, heps1, hfield, hprod, hresp⟩ := homega
    have hone : omega ∈ _root_.SubdiffusiveProcess.Paper.product_threshold_good_scale d M 12 (some L) m z 1 s :=
      ⟨hBpos, hspos, hs1, one_pos, le_rfl,
        Section6ExcessDecay.goodFieldOne_mono heps1 hfield, hprod,
        Section6ExcessDecay.goodResponse_mono heps0.le heps1 hresp⟩
    have hsite := hsites M s hs htau L m hmL z omega hone
    set eta : _root_.SubdiffusiveProcess.Model.PotentialSample d :=
      translatePotentialSample z omega with heta
    obtain ⟨_, hII, _, _, hIII⟩ := hsite
    have hsiteTwo : aux_obl_ramp_threshold12_fourth_ieb12_SiteTwo CB M s L m eta := by
      intro n hn z' hz'
      obtain ⟨h1, h2, _, _, _, h6⟩ := hII n hn z' hz'
      exact ⟨h1, h2, h6⟩
    have hsiteThree : aux_obl_ramp_threshold12_fourth_ieb12_SiteThree CB M s L m eta := by
      intro x hx
      have h := (hIII x hx).2
      have henv : (CB * (12 * (3 : ℝ) ^ (s * (m : ℝ) / 8) *
              (3 : ℝ) ^ (s * ((m : ℝ) + 1) / 16)) *
            min 1 (longRatioGradientTail m eta +
              supNormOn (cube d m) (fullShellBlock m eta) +
              _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m : ℝ) + 1))) =
          (2 * CB) * subunitEnvelope s m * subunitDeviation M m eta := by
        unfold subunitEnvelope subunitDeviation
        ring_nf
      rw [henv] at h
      exact h
    have hrespEta : GoodResponse M none m 0 epsilon s eta := by
      have h0 : GoodResponse M (some L) m 0 epsilon s eta :=
        (Section6Covariance.goodResponse_translatePotentialSample
          M (some L) m 0 epsilon s z omega).2 (by simpa only [add_zero] using hresp)
      exact (Section6Cutoff.goodResponse_some_iff_none_of_scale_le_cutoff
        M hmL 0 epsilon s eta).1 h0
    have hfieldEta : GoodFieldOne m 0 epsilon s eta :=
      (Section6Covariance.goodFieldOne_translatePotentialSample m 0 epsilon s z omega).2
        (by simpa only [add_zero] using hfield)
    have hrespOne : GoodResponse M none m 0 1 s eta :=
      Section6ExcessDecay.goodResponse_mono heps0.le heps1 hrespEta
    have hbase := aux_obl_ramp_threshold12_fourth_ieb12_paperError_le_base M hmL hs.1 hs.2 eta hrespOne
      hsiteTwo hsiteThree
    obtain ⟨hA0, _, hBs0, hBf0, hBg0⟩ := aux_obl_ramp_threshold12_fourth_ieb12_slots_nonneg M (m := m) hs0 eta
    set Sigma : ℝ := goodScaleResponseSlot M s m eta + s⁻¹ * M.delta ^ 2 +
      goodScaleShellSlot s m eta + goodScaleFullSlot s m eta +
      goodScaleGradientSlot m eta with hSigma
    have hSigma0 : 0 ≤ Sigma := by rw [hSigma]; linarith
    have hreal : section6HomogenizationError M s L m omega z ≤ K * Sigma := by
      unfold section6HomogenizationError
      exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hK0.le hSigma0) hbase
    -- the truncated display
    set E : ℝ := accumulatedError M none m 0 s eta with hEdef
    have hA := aux_obl_ramp_threshold12_fourth_ieb12_responseSlot_le_accumulatedError M heps0.le hspos.le hrespEta
    have hBs := Section6Holder.goodScaleShellSlot_le_accumulatedError M s m eta
    have hBf := Section6Holder.goodScaleFullSlot_le_two_mul_accumulatedError M s m eta
    have hBg := Section6Holder.goodScaleGradientSlot_le_accumulatedError M s m eta
    have hsum5 : Sigma ≤ 5 * (s⁻¹ * M.delta ^ 2 + epsilon ^ 8 + E) := by
      rw [← hEdef] at hA hBs hBf hBg
      have heps8 : 0 ≤ epsilon ^ 8 := pow_nonneg heps0.le 8
      rw [hSigma]
      linarith
    -- the epsilon cap
    have hAe := aux_obl_ramp_threshold12_fourth_ieb12_responseSlot_le_epsilon M heps0.le hspos.le hrespEta
    have hBse := aux_obl_ramp_threshold12_fourth_ieb12_goodScaleShellSlot_le m eta hfieldEta
    have hBfe := aux_obl_ramp_threshold12_fourth_ieb12_goodScaleFullSlot_le m eta hfieldEta
    have hBge : goodScaleGradientSlot m eta ≤ 3 * epsilon := by
      rw [goodScaleGradientSlot_eq_longRatioGradientTail]
      exact longRatioGradientTail_le_three_mul_of_goodFieldOne m heps0.le hs.2
        eta hfieldEta
    have hsum7 : Sigma ≤ 7 * epsilon := by
      rw [hSigma]
      linarith [hepsilon.1]
    have hcarrier : E = accumulatedError M (some L) m z s omega := by
      rw [hEdef, ← Section6Cutoff.accumulatedError_some_eq_none_of_scale_le_cutoff
        M hmL 0 s eta, heta,
        Section6Holder.accumulatedError_translatePotentialSample]
    rw [← hcarrier]
    have hX0 : 0 ≤ s⁻¹ * M.delta ^ 2 + epsilon ^ 8 + E := by
      have := Section6Holder.accumulatedError_nonneg M none s m 0 eta
      rw [← hEdef] at this
      positivity
    have h5 : section6HomogenizationError M s L m omega z ≤
        K * (5 * (s⁻¹ * M.delta ^ 2 + epsilon ^ 8 + E)) :=
      hreal.trans (mul_le_mul_of_nonneg_left hsum5 hK0.le)
    have h7 : section6HomogenizationError M s L m omega z ≤ K * (7 * epsilon) :=
      hreal.trans (mul_le_mul_of_nonneg_left hsum7 hK0.le)
    refine ⟨?_, by linarith⟩
    rcases le_total epsilon (s⁻¹ * M.delta ^ 2 + epsilon ^ 8 + E) with hle | hle
    · rw [min_eq_left hle]
      linarith
    · rw [min_eq_right hle]
      nlinarith
  · simp only [indicatorValue, ite_eq_right homega]
    exact ⟨by positivity, by positivity⟩

/-- The requested equal-scale estimate is the `L = m` specialization. -/
theorem aux_obl_ramp_threshold12_fourth_in_deterministic_equal_scale_b12_error_of_scale_le_cutoff
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ),
      _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ s * Real.log 3 / 16 →
      ∀ epsilon ∈ Set.Icc (s⁻¹ * M.delta ^ 2) 1,
      ∀ (m : ℕ) (z : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d),
        omega ∈ _root_.SubdiffusiveProcess.Paper.product_threshold_good_scale d M 12 (some m) m z epsilon s →
        section6HomogenizationError M s m m omega z ≤
          C * (s⁻¹ * M.delta ^ 2 + epsilon ^ 8 +
            accumulatedError M (some m) m z s omega) := by
  obtain ⟨C, hC, hbound⟩ := aux_obl_ramp_threshold12_fourth_scale_le_cutoff_error d
  refine ⟨C, hC, ?_⟩
  intro M s hs htau epsilon hepsilon m z omega homega
  have h := (hbound M m s hs htau epsilon hepsilon m le_rfl z omega).1
  simp only [indicatorValue, ite_eq_left homega] at h
  exact h.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le)

/-! ## Combining the cutoff branches -/

/-- Reduction, not a proof of the conjunct: the literal fourth
conjunct of `product_threshold_regularities d 12` follows from the `m ≤ L`
theorem above together with an `L < m` saturation branch of the same shape
(`hsat`).  It records that `hsat` is exactly what remains for this conjunct. -/
theorem aux_obl_ramp_threshold12_fourth_fourth_of_saturation (d : ℕ) [NeZero d]
    (hsat :
      ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
        ∀ L : ℕ,
        ∀ s ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ),
          _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ s * Real.log 3 / 16 →
          ∀ epsilon ∈ Set.Icc (s⁻¹ * M.delta ^ 2) 1, ∀ m : ℕ, L < m → ∀ z : Vec d,
            ∀ ω,
              indicatorValue (_root_.SubdiffusiveProcess.Paper.product_threshold_good_scale d M 12 (some L) m z epsilon s)
                  (fun ω' => section6HomogenizationError M s L m ω' z) ω ≤
                C * min epsilon
                  (s⁻¹ * M.delta ^ 2 + epsilon ^ 8 +
                    accumulatedError M (some L) m z s ω) ∧
              indicatorValue (_root_.SubdiffusiveProcess.Paper.product_threshold_good_scale d M 12 (some L) m z epsilon s)
                  (fun ω' => section6HomogenizationError M s L m ω' z) ω ≤ C * epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ L : ℕ,
      ∀ s ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ),
        _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ s * Real.log 3 / 16 →
        ∀ epsilon ∈ Set.Icc (s⁻¹ * M.delta ^ 2) 1, ∀ m : ℕ, ∀ z : Vec d,
          ∀ ω,
            indicatorValue (_root_.SubdiffusiveProcess.Paper.product_threshold_good_scale d M 12 (some L) m z epsilon s)
                (fun ω' => section6HomogenizationError M s L m ω' z) ω ≤
              C * min epsilon
                (s⁻¹ * M.delta ^ 2 + epsilon ^ 8 +
                  accumulatedError M (some L) m z s ω) ∧
            indicatorValue (_root_.SubdiffusiveProcess.Paper.product_threshold_good_scale d M 12 (some L) m z epsilon s)
                (fun ω' => section6HomogenizationError M s L m ω' z) ω ≤ C * epsilon := by
  obtain ⟨C1, hC1, h1⟩ := aux_obl_ramp_threshold12_fourth_scale_le_cutoff_error d
  obtain ⟨C2, hC2, h2⟩ := hsat
  refine ⟨max C1 C2, lt_max_of_lt_left hC1, ?_⟩
  intro M L s hs htau epsilon hepsilon m z ω
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hD0 : 0 ≤ s⁻¹ * M.delta ^ 2 := mul_nonneg (inv_nonneg.2 hs0.le) (sq_nonneg _)
  have heps0 : 0 ≤ epsilon := hD0.trans hepsilon.1
  have hE0 := Section6Holder.accumulatedError_nonneg M (some L) s m z ω
  have hmin0 : 0 ≤ min epsilon (s⁻¹ * M.delta ^ 2 + epsilon ^ 8 +
      accumulatedError M (some L) m z s ω) := le_min heps0 (by positivity)
  have hup : ∀ {Ci : ℝ}, Ci ≤ max C1 C2 → ∀ {X Y : ℝ}, 0 ≤ Y → X ≤ Ci * Y →
      X ≤ max C1 C2 * Y := fun hCi _ _ hY hX =>
    hX.trans (mul_le_mul_of_nonneg_right hCi hY)
  rcases le_or_gt m L with hmL | hLm
  · obtain ⟨ha, hb⟩ := h1 M L s hs htau epsilon hepsilon m hmL z ω
    exact ⟨hup (le_max_left _ _) hmin0 ha, hup (le_max_left _ _) heps0 hb⟩
  · obtain ⟨ha, hb⟩ := h2 M L s hs htau epsilon hepsilon m hLm z ω
    exact ⟨hup (le_max_right _ _) hmin0 ha, hup (le_max_right _ _) heps0 hb⟩

/-- The copied goal above is literally the fourth conjunct. -/
example (d : ℕ) [NeZero d] (h : product_threshold_regularities d 12) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ L : ℕ,
      ∀ s ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ),
        _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ s * Real.log 3 / 16 →
        ∀ epsilon ∈ Set.Icc (s⁻¹ * M.delta ^ 2) 1, ∀ m : ℕ, ∀ z : Vec d,
          ∀ ω,
            indicatorValue (_root_.SubdiffusiveProcess.Paper.product_threshold_good_scale d M 12 (some L) m z epsilon s)
                (fun ω' => section6HomogenizationError M s L m ω' z) ω ≤
              C * min epsilon
                (s⁻¹ * M.delta ^ 2 + epsilon ^ 8 +
                  accumulatedError M (some L) m z s ω) ∧
            indicatorValue (_root_.SubdiffusiveProcess.Paper.product_threshold_good_scale d M 12 (some L) m z epsilon s)
                (fun ω' => section6HomogenizationError M s L m ω' z) ω ≤ C * epsilon := h.2.2.2

end SubdiffusiveProcess.Paper

open SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff

namespace SubdiffusiveProcess.Paper

variable {d : ℕ}

/-! ## The threshold-12 product clause at base point `0` -/

/-- The literal threshold-12 product clause of
`SubdiffusiveProcess.Paper.product_threshold_good_scale`, read on a sample at base point `0`. -/
def aux_obl_ramp_threshold12_fourth_t12sat_ProductTwelve (m : ℕ) (s : ℝ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : Prop :=
  ∀ j : ℕ,
    supNormOn (translatedCube d ((m + 1 + j : ℕ) : ℤ) 0) (fun x =>
      (∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |omega i x|) +
        ∏' i : ℕ, if m + j ≤ i then
          Real.exp (4 * |omega i x - omega i 0|) else 1) ≤
      12 * (3 : ℝ) ^ ((s * (j : ℝ)) / 8)

/-- The product clause of the event, transported to the translated sample. -/
theorem aux_obl_ramp_threshold12_fourth_t12sat_productTwelve_of_mem
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ} {z : Vec d} {epsilon s : ℝ}
    {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d}
    (homega : omega ∈ _root_.SubdiffusiveProcess.Paper.product_threshold_good_scale d M 12 (some L) m z epsilon s) :
    aux_obl_ramp_threshold12_fourth_t12sat_ProductTwelve m s (translatePotentialSample z omega) := by
  let eta := translatePotentialSample z omega
  have hmem : 0 < (12 : ℝ) ∧ 0 < s ∧ s ≤ 1 ∧ 0 < epsilon ∧
      epsilon ≤ 1 ∧ GoodFieldOne m z epsilon s omega ∧
      (∀ j : ℕ,
        (∀ x ∈ translatedCube d (m + 1 + j) z,
          Multipliable (fun i : ℕ =>
            if m + j ≤ i then Real.exp (4 * |omega i x - omega i z|) else 1)) ∧
        BddAbove ((fun x : Vec d =>
          |(∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |omega i x|) +
            ∏' i : ℕ, if m + j ≤ i then
              Real.exp (4 * |omega i x - omega i z|) else 1|) ''
          translatedCube d (m + 1 + j) z) ∧
        supNormOn (translatedCube d (m + 1 + j) z) (fun x =>
          (∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |omega i x|) +
            ∏' i : ℕ, if m + j ≤ i then
              Real.exp (4 * |omega i x - omega i z|) else 1) ≤
          12 * (3 : ℝ) ^ ((s * (j : ℝ)) / 8)) ∧
      GoodResponse M (some L) m z epsilon s omega := by
    simpa only [product_threshold_good_scale, Set.mem_ofPred_eq] using homega
  rcases hmem with ⟨_, _, _, _, _, _, hprod0, _⟩
  intro j
  have hraw := (hprod0 j).2.2
  calc
    supNormOn (translatedCube d ((m + 1 + j : ℕ) : ℤ) 0) (fun x =>
        (∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |eta i x|) +
          ∏' i : ℕ, if m + j ≤ i then
            Real.exp (4 * |eta i x - eta i 0|) else 1) =
        supNormOn (translatedCube d ((m + 1 + j : ℕ) : ℤ) 0) (fun x =>
          (∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |omega i (x + z)|) +
            ∏' i : ℕ, if m + j ≤ i then
              Real.exp (4 * |omega i (x + z) - omega i z|) else 1) := by
          congr 1
          funext x
          simp only [eta, translatePotentialSample,
            _root_.SubdiffusiveProcess.Model.PotentialField.translate_apply]
          ring_nf
    _ = supNormOn (translatedCube d ((m + 1 + j : ℕ) : ℤ) z) (fun x =>
          (∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |omega i x|) +
            ∏' i : ℕ, if m + j ≤ i then
              Real.exp (4 * |omega i x - omega i z|) else 1) := by
          simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_zero] using
            (SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.supNormOn_translatedCube_comp_add
              z 0 ((m + 1 + j : ℕ) : ℤ) (fun x =>
                (∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |omega i x|) +
                  ∏' i : ℕ, if m + j ≤ i then
                    Real.exp (4 * |omega i x - omega i z|) else 1))
    _ ≤ 12 * (3 : ℝ) ^ ((s * (j : ℝ)) / 8) := hraw

/-! ## Elementary sup-norm reads -/

private theorem aux_obl_ramp_threshold12_fourth_t12sat_zero_mem_cube (k : ℤ) : (0 : Vec d) ∈ cube d k := by
  rw [cube, mem_openCubeSet_originCube_iff]
  intro i
  have hp : 0 < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  constructor <;> simp only [Pi.zero_apply] <;> nlinarith

private theorem aux_obl_ramp_threshold12_fourth_t12sat_shellBlock_continuous (m n : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    Continuous (shellBlock m n omega) := by
  unfold shellBlock
  fun_prop

private theorem aux_obl_ramp_threshold12_fourth_t12sat_fullShellBlock_continuous (m : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    Continuous (fullShellBlock m omega) := by
  unfold fullShellBlock
  fun_prop

private theorem aux_obl_ramp_threshold12_fourth_t12sat_supNormOn_cube_nonneg (k : ℕ) {f : Vec d → ℝ}
    (hf : Continuous f) : 0 ≤ supNormOn (cube d k) f :=
  (abs_nonneg (f 0)).trans
    (abs_apply_le_supNormOn_cube_of_continuous hf (aux_obl_ramp_threshold12_fourth_t12sat_zero_mem_cube (k : ℤ)))

private theorem aux_obl_ramp_threshold12_fourth_t12sat_supNormOn_nonneg (W : Set (Vec d)) (f : Vec d → ℝ) :
    0 ≤ supNormOn W f := by
  refine Real.sSup_nonneg ?_
  rintro a ⟨x, _, rfl⟩
  exact abs_nonneg _

private theorem aux_obl_ramp_threshold12_fourth_t12sat_supNormOn_cube_mono {n L : ℕ} (hnL : n ≤ L)
    {f : Vec d → ℝ} (hf : Continuous f) :
    supNormOn (cube d n) f ≤ supNormOn (cube d L) f := by
  unfold supNormOn
  apply csSup_le
  · exact ⟨|f 0|, 0, aux_obl_ramp_threshold12_fourth_t12sat_zero_mem_cube _, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hxL : x ∈ cube d L :=
      openCubeSet_originCube_subset_of_scale_le (by exact_mod_cast hnL) hx
    exact abs_apply_le_supNormOn_cube_of_continuous hf hxL

/-! ## The clipped shell read from the threshold-12 product clause -/

/-- A shell block with indices in `[n+1, k] ⊆ [n+1, m]` is dominated by the
single finite product at parent gap `m - n`. -/
private theorem aux_obl_ramp_threshold12_fourth_t12sat_exp_abs_shellBlock_le_finiteProduct
    {n k m : ℕ} (hnk : n ≤ k) (hkm : k ≤ m)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Vec d) :
    Real.exp |shellBlock k n omega x| ≤
      ∏ i ∈ Finset.Icc (m - (m - n)) (m + (m - n)),
        Real.exp |omega i x| := by
  unfold shellBlock
  calc
    Real.exp |∑ i ∈ Finset.Icc (n + 1) k, omega i x| ≤
        Real.exp (∑ i ∈ Finset.Icc (n + 1) k, |omega i x|) :=
      Real.exp_le_exp.mpr (Finset.abs_sum_le_sum_abs _ _)
    _ = ∏ i ∈ Finset.Icc (n + 1) k, Real.exp |omega i x| := by
      rw [Real.exp_sum]
    _ ≤ ∏ i ∈ Finset.Icc (m - (m - n)) (m + (m - n)),
        Real.exp |omega i x| := by
      let u := Finset.Icc (n + 1) k
      let v := Finset.Icc (m - (m - n)) (m + (m - n))
      have huv : u ⊆ v := by
        intro i hi
        simp only [u, v, Finset.mem_Icc] at hi ⊢
        omega
      have hu0 : 0 ≤ ∏ i ∈ u, Real.exp |omega i x| := by positivity
      have hrest : 1 ≤ ∏ i ∈ v \ u, Real.exp |omega i x| := by
        induction v \ u using Finset.induction_on with
        | empty => simp
        | @insert a w haw ih =>
            rw [Finset.prod_insert haw]
            exact one_le_mul_of_one_le_of_one_le
              (Real.one_le_exp (abs_nonneg _)) ih
      change (∏ i ∈ u, Real.exp |omega i x|) ≤
        ∏ i ∈ v, Real.exp |omega i x|
      calc
        (∏ i ∈ u, Real.exp |omega i x|) =
            1 * ∏ i ∈ u, Real.exp |omega i x| := by rw [one_mul]
        _ ≤ (∏ i ∈ v \ u, Real.exp |omega i x|) *
            ∏ i ∈ u, Real.exp |omega i x| :=
          mul_le_mul_of_nonneg_right hrest hu0
        _ = ∏ i ∈ v, Real.exp |omega i x| := Finset.prod_sdiff huv

private theorem aux_obl_ramp_threshold12_fourth_t12sat_tail_one (m q : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x y : Vec d) :
    1 ≤ ∏' i : ℕ, if m + q ≤ i then
      Real.exp (4 * |omega i x - omega i y|) else 1 := by
  let f : ℕ → ℝ := fun i => if m + q ≤ i then
    Real.exp (4 * |omega i x - omega i y|) else 1
  have hf : ∀ i, 1 ≤ f i := by
    intro i
    dsimp [f]
    split
    · exact Real.one_le_exp (by positivity)
    · exact le_rfl
  by_cases hmult : Multipliable f
  · apply le_hasProd_of_le_prod hmult.hasProd
    intro u
    induction u using Finset.induction_on with
    | empty => simp
    | @insert a w haw ih =>
        rw [Finset.prod_insert haw]
        exact one_le_mul_of_one_le_of_one_le (hf a) ih
  · rw [tprod_eq_one_of_not_multipliable hmult]

/-- The finite product at gap `q` is read at a point of the parent cube from
the threshold-12 product clause. -/
private theorem aux_obl_ramp_threshold12_fourth_t12sat_finiteProduct_le
    {m q : ℕ} {epsilon s : ℝ} (hepsilon : 0 ≤ epsilon) (hsUpper : s ≤ 1 / 2)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hfield : GoodFieldOne m 0 epsilon s omega)
    (hprod : aux_obl_ramp_threshold12_fourth_t12sat_ProductTwelve m s omega)
    {y : Vec d} (hy : y ∈ cube d m) :
    ∏ i ∈ Finset.Icc (m - q) (m + q), Real.exp |omega i y| ≤
      12 * (3 : ℝ) ^ ((s * (q : ℝ)) / 8) := by
  have hBdd := bddAbove_goodFieldTwo_values_of_goodFieldOne
    m q hepsilon hsUpper omega hfield
  have hyLarge : y ∈ translatedCube d ((m + 1 + q : ℕ) : ℤ) 0 := by
    refine ⟨y, openCubeSet_originCube_subset_of_scale_le ?_ hy, by simp⟩
    exact_mod_cast (show m ≤ m + 1 + q by omega)
  let finitePart : ℝ :=
    ∏ i ∈ Finset.Icc (m - q) (m + q), Real.exp |omega i y|
  let tailPart : ℝ := ∏' i : ℕ, if m + q ≤ i then
    Real.exp (4 * |omega i y - omega i 0|) else 1
  have hfinite0 : 0 ≤ finitePart := by dsimp only [finitePart]; positivity
  have htailOne : 1 ≤ tailPart := aux_obl_ramp_threshold12_fourth_t12sat_tail_one m q omega y 0
  have htail0 : 0 ≤ tailPart := zero_le_one.trans htailOne
  have hpoint : finitePart + tailPart ≤
      supNormOn (translatedCube d ((m + 1 + q : ℕ) : ℤ) 0)
        (fun x ↦
          (∏ i ∈ Finset.Icc (m - q) (m + q), Real.exp |omega i x|) +
            ∏' i : ℕ, if m + q ≤ i then
              Real.exp (4 * |omega i x - omega i 0|) else 1) := by
    unfold supNormOn
    have hle := le_csSup hBdd
      (show |finitePart + tailPart| ∈ {a : ℝ | ∃ x ∈
          translatedCube d ((m + 1 + q : ℕ) : ℤ) 0,
        a = |(∏ i ∈ Finset.Icc (m - q) (m + q), Real.exp |omega i x|) +
          ∏' i : ℕ, if m + q ≤ i then
            Real.exp (4 * |omega i x - omega i 0|) else 1|} by
        exact ⟨y, hyLarge, rfl⟩)
    rwa [abs_of_nonneg (add_nonneg hfinite0 htail0)] at hle
  exact (le_add_of_nonneg_right htail0).trans (hpoint.trans (hprod q))

/-- Threshold-12 exponential bound for a shell block `g_(k,n)` with
`n ≤ k ≤ m`, read from the single finite product at parent gap `m - n`. -/
theorem aux_obl_ramp_threshold12_fourth_t12sat_exp_abs_shellBlock_le
    {n k m : ℕ} (hnk : n ≤ k) (hkm : k ≤ m) {epsilon s : ℝ}
    (hepsilon : 0 ≤ epsilon) (hsUpper : s ≤ 1 / 2)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hfield : GoodFieldOne m 0 epsilon s omega)
    (hprod : aux_obl_ramp_threshold12_fourth_t12sat_ProductTwelve m s omega)
    {y : Vec d} (hy : y ∈ cube d m) :
    Real.exp |shellBlock k n omega y| ≤
      12 * (3 : ℝ) ^ ((s * ((m - n : ℕ) : ℝ)) / 8) :=
  (aux_obl_ramp_threshold12_fourth_t12sat_exp_abs_shellBlock_le_finiteProduct hnk hkm omega y).trans
    (aux_obl_ramp_threshold12_fourth_t12sat_finiteProduct_le hepsilon hsUpper omega hfield hprod hy)

/-- Threshold-12 exponential bound for the full low block `g_m`. -/
theorem aux_obl_ramp_threshold12_fourth_t12sat_exp_supNormOn_fullShellBlock_le
    (m : ℕ) {epsilon s : ℝ} (hepsilon : 0 ≤ epsilon) (hsUpper : s ≤ 1 / 2)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hfield : GoodFieldOne m 0 epsilon s omega)
    (hprod : aux_obl_ramp_threshold12_fourth_t12sat_ProductTwelve m s omega) :
    Real.exp (supNormOn (cube d m) (fullShellBlock m omega)) ≤
      12 * (3 : ℝ) ^ ((s * (m : ℝ)) / 8) := by
  let B : ℝ := 12 * (3 : ℝ) ^ ((s * (m : ℝ)) / 8)
  have hBpos : 0 < B := by dsimp only [B]; positivity
  have hpoint : ∀ x ∈ cube d m, Real.exp |fullShellBlock m omega x| ≤ B := by
    intro x hx
    have hfinite : Real.exp |fullShellBlock m omega x| ≤
        ∏ i ∈ Finset.Icc (m - m) (m + m), Real.exp |omega i x| := by
      unfold fullShellBlock
      have hsum : |∑ i ∈ Finset.range (m + 1), omega i x| ≤
          ∑ i ∈ Finset.range (m + 1), |omega i x| :=
        Finset.abs_sum_le_sum_abs _ _
      have hsubset : Finset.range (m + 1) ⊆ Finset.Icc (m - m) (m + m) := by
        intro i hi
        rw [Finset.mem_range] at hi
        rw [Finset.mem_Icc]
        omega
      have hsum2 : ∑ i ∈ Finset.range (m + 1), |omega i x| ≤
          ∑ i ∈ Finset.Icc (m - m) (m + m), |omega i x| :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun i _ _ => abs_nonneg _)
      rw [← Real.exp_sum]
      exact Real.exp_le_exp.mpr (hsum.trans hsum2)
    exact hfinite.trans (aux_obl_ramp_threshold12_fourth_t12sat_finiteProduct_le hepsilon hsUpper omega
      hfield hprod hx)
  have hsup : supNormOn (cube d m) (fullShellBlock m omega) ≤ Real.log B := by
    unfold supNormOn
    apply csSup_le
    · exact ⟨|fullShellBlock m omega 0|, 0, aux_obl_ramp_threshold12_fourth_t12sat_zero_mem_cube _, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      rw [← Real.log_exp |fullShellBlock m omega x|]
      exact Real.log_le_log (Real.exp_pos _) (hpoint x hx)
  calc
    Real.exp (supNormOn (cube d m) (fullShellBlock m omega)) ≤
        Real.exp (Real.log B) := Real.exp_le_exp.mpr hsup
    _ = B := Real.exp_log hBpos

/-! ## The finite-cutoff coefficient ratio below `L` (threshold 12) -/

/-- Threshold-12 analogue of `cutoffFiniteRatio_deviation_sum_le`: the
constant `24` becomes `48` because the clipped shell envelope is
`12 * 3^(s(m-n)/8)`. -/
theorem aux_obl_ramp_threshold12_fourth_t12sat_cutoffFiniteRatio_deviation_sum_le
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {n L m : ℕ}
    (hnL : n ≤ L) (hLm : L ≤ m) {epsilon s : ℝ}
    (hepsilon : 0 ≤ epsilon) (hsLower : 64 * M.delta ^ 2 ≤ s)
    (hsUpper : s ≤ 1 / 2) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hfield : GoodFieldOne m 0 epsilon s omega)
    (hprod : aux_obl_ramp_threshold12_fourth_t12sat_ProductTwelve m s omega) {z x : Vec d}
    (hx : x ∈ cube d n) (hy : x + z ∈ cube d m) :
    |Real.exp (shellBlock L n (translatePotentialSample z omega) x +
          normalizerLogError M L n) - 1| +
        |Real.exp (-(shellBlock L n (translatePotentialSample z omega) x +
          normalizerLogError M L n)) - 1| ≤
      48 * (3 : ℝ) ^ ((3 * s * ((m - n : ℕ) : ℝ)) / 16) *
        min 1 (supNormOn (cube d n)
              (shellBlock m n (translatePotentialSample z omega)) +
            supNormOn (cube d n)
              (shellBlock m L (translatePotentialSample z omega)) +
            _root_.SubdiffusiveProcess.Model.tauSq M.P * ((L - n : ℕ) : ℝ)) := by
  let g := shellBlock L n (translatePotentialSample z omega) x
  let r := normalizerLogError M L n
  let G := |g|
  let R := |r|
  let Eg := 12 * (3 : ℝ) ^ ((s * ((m - n : ℕ) : ℝ)) / 8)
  let Er := (3 : ℝ) ^ ((s * ((m - n : ℕ) : ℝ)) / 16)
  have hs0 : 0 ≤ s :=
    (mul_nonneg (by norm_num) (sq_nonneg M.delta)).trans hsLower
  have hG0 : 0 ≤ G := by dsimp only [G]; exact abs_nonneg _
  have hR0 : 0 ≤ R := by dsimp only [R]; exact abs_nonneg _
  have hg : |g| ≤ G := le_rfl
  have hr : |r| ≤ R := le_rfl
  have hEg : Real.exp G ≤ Eg := by
    dsimp only [G, g, Eg]
    rw [shellBlock_translatePotentialSample L n omega z x]
    exact aux_obl_ramp_threshold12_fourth_t12sat_exp_abs_shellBlock_le hnL hLm hepsilon hsUpper omega
      hfield hprod hy
  have hErRaw := exp_abs_normalizerLogError_le_three_rpow M hnL hsLower
  have hEr : Real.exp R ≤ Er := by
    have hgapReal : ((L - n : ℕ) : ℝ) ≤ ((m - n : ℕ) : ℝ) := by
      exact_mod_cast (show L - n ≤ m - n by omega)
    have hmono : (3 : ℝ) ^ ((s * ((L - n : ℕ) : ℝ)) / 16) ≤
        (3 : ℝ) ^ ((s * ((m - n : ℕ) : ℝ)) / 16) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have := mul_le_mul_of_nonneg_left hgapReal hs0
      linarith
    dsimp only [R, r, Er]
    exact hErRaw.trans hmono
  have hraw := combined_ratio_deviation_sum_le_weighted_min
    (A := (1 : ℝ)) (Ainv := (1 : ℝ)) (g := g) (r := r)
    (S := (0 : ℝ)) (G := G) (R := R) (C := (0 : ℝ))
    (Eg := Eg) (Er := Er) (by norm_num) (by norm_num) hG0 hR0
    (by norm_num) (by norm_num) hg hr hEg hEr
  have hfactor : 2 * ((0 : ℝ) + 2) * (Eg * Er) =
      48 * (3 : ℝ) ^ ((3 * s * ((m - n : ℕ) : ℝ)) / 16) := by
    dsimp only [Eg, Er]
    calc
      2 * ((0 : ℝ) + 2) *
          (12 * (3 : ℝ) ^ (s * ((m - n : ℕ) : ℝ) / 8) *
            (3 : ℝ) ^ (s * ((m - n : ℕ) : ℝ) / 16)) =
        48 * ((3 : ℝ) ^ (s * ((m - n : ℕ) : ℝ) / 8) *
          (3 : ℝ) ^ (s * ((m - n : ℕ) : ℝ) / 16)) := by ring
      _ = 48 * (3 : ℝ) ^ ((3 * s * ((m - n : ℕ) : ℝ)) / 16) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        congr 2
        ring
  have hrho : R ≤ _root_.SubdiffusiveProcess.Model.tauSq M.P * ((L - n : ℕ) : ℝ) := by
    dsimp only [R, r]
    exact abs_normalizerLogError_le_of_le M hnL
  have hshell : G ≤ supNormOn (cube d n)
        (shellBlock m n (translatePotentialSample z omega)) +
      supNormOn (cube d n)
        (shellBlock m L (translatePotentialSample z omega)) := by
    dsimp only [G, g]
    exact abs_cutoffShellBlock_le_parentShellSup_add hnL hLm omega z hx
  have hmin : min 1 (0 + G + R) ≤ min 1
      (supNormOn (cube d n)
          (shellBlock m n (translatePotentialSample z omega)) +
        supNormOn (cube d n)
          (shellBlock m L (translatePotentialSample z omega)) +
        _root_.SubdiffusiveProcess.Model.tauSq M.P * ((L - n : ℕ) : ℝ)) := by
    apply min_le_min le_rfl
    linarith
  dsimp only [g, r, G, R] at hraw ⊢
  rw [hfactor] at hraw
  have hscaled := mul_le_mul_of_nonneg_left hmin (show
    0 ≤ 48 * (3 : ℝ) ^ ((3 * s * ((m - n : ℕ) : ℝ)) / 16) by
      positivity)
  have hfinal := hraw.trans hscaled
  simpa only [one_mul, mul_one, zero_add] using hfinal

/-- The two-`L^∞` sensitivity error below the cutoff on a scale-`n`
descendant, at threshold 12. -/
theorem aux_obl_ramp_threshold12_fourth_t12sat_cutoffRatioError_ahom_le
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {n L m : ℕ}
    (hnL : n ≤ L) (hLm : L ≤ m) {epsilon s : ℝ}
    (hepsilon : 0 ≤ epsilon) (hsLower : 64 * M.delta ^ 2 ≤ s)
    (hsUpper : s ≤ 1 / 2) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hfield : GoodFieldOne m 0 epsilon s omega)
    (hprod : aux_obl_ramp_threshold12_fourth_t12sat_ProductTwelve m s omega)
    {R : SubdiffusiveProcess.CoarseGrainingVocab.TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)) :
    cutoffRatioError M n L
        (translatePotentialSample (triadicCubeShift R) omega)
        (Ch02.cubeDomain (originCube d (n : ℤ))) (ahom M L) ≤
      2 * (48 * (3 : ℝ) ^
          ((3 * s * ((m - n : ℕ) : ℝ)) / 16) *
        min 1 (supNormOn (cube d n)
              (shellBlock m n
                (translatePotentialSample (triadicCubeShift R) omega)) +
            supNormOn (cube d n)
              (shellBlock m L
                (translatePotentialSample (triadicCubeShift R) omega)) +
            _root_.SubdiffusiveProcess.Model.tauSq M.P * ((L - n : ℕ) : ℝ))) ^ 2 := by
  let z := triadicCubeShift R
  let U := Ch02.cubeDomain (originCube d (n : ℤ))
  let W := 48 * (3 : ℝ) ^
      ((3 * s * ((m - n : ℕ) : ℝ)) / 16) *
    min 1 (supNormOn (cube d n)
          (shellBlock m n (translatePotentialSample z omega)) +
        supNormOn (cube d n)
          (shellBlock m L (translatePotentialSample z omega)) +
        _root_.SubdiffusiveProcess.Model.tauSq M.P * ((L - n : ℕ) : ℝ))
  have hpoint : ∀ x ∈ cube d n,
      |Real.exp (shellBlock L n (translatePotentialSample z omega) x +
            normalizerLogError M L n) - 1| +
          |Real.exp (-(shellBlock L n (translatePotentialSample z omega) x +
            normalizerLogError M L n)) - 1| ≤ W := by
    intro x hx
    have hRscale : R.scale = (n : ℤ) := scale_eq_of_mem_descendantsAtScale hR
    have hxR : z + x ∈ openCubeSet R := by
      rw [openCubeSet_eq_translateSet_originCube_of_triadicCube,
        mem_translateSet_iff_sub_mem]
      simp only [z, hRscale, add_sub_cancel_left]
      exact hx
    have hy : x + z ∈ cube d m := by
      rw [add_comm]
      exact openCubeSet_subset_of_mem_descendantsAtScale
        (scale_le_of_mem_descendantsAtScale hR) hR hxR
    exact aux_obl_ramp_threshold12_fourth_t12sat_cutoffFiniteRatio_deviation_sum_le M hnL hLm hepsilon hsLower
      hsUpper omega hfield hprod hx hy
  have hW0 : 0 ≤ W :=
    (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans
      (hpoint 0 (aux_obl_ramp_threshold12_fourth_t12sat_zero_mem_cube _))
  have hfwd := scalarRatioLInf_one_le_of_forall_bound (U := U) hW0 (by
    intro x hx
    exact (le_add_of_nonneg_right (abs_nonneg _)).trans
      (hpoint x (by exact hx)))
  have hrev := scalarRatioLInf_one_le_of_forall_bound (U := U) hW0 (by
    intro x hx
    exact (le_add_of_nonneg_left (abs_nonneg _)).trans
      (hpoint x (by exact hx)))
  have hbL := tailCoefficientCubeAverage_eq_ahom_of_cutoff_le_scale
    M (show L ≤ L from le_rfl) omega
  have hrepacked := cutoffRatioError_tailAverage_eq_combined
    M hnL (show L ≤ L from le_rfl) omega z U
  rw [hbL] at hrepacked
  have hcombined : combinedCoefficientRatio M L L n omega z =
      fun x ↦ Real.exp (shellBlock L n (translatePotentialSample z omega) x +
        normalizerLogError M L n) := by
    funext x
    unfold combinedCoefficientRatio
    rw [Section4Recursion.tailCoefficient_of_ge M (show L ≤ L from le_rfl), hbL,
      div_self (ahom_pos M L).ne', one_mul]
  have hcombinedInv : combinedCoefficientRatioInv M L L n omega z =
      fun x ↦ Real.exp (-(shellBlock L n
        (translatePotentialSample z omega) x + normalizerLogError M L n)) := by
    funext x
    unfold combinedCoefficientRatioInv
    rw [Section4Recursion.tailCoefficient_of_ge M (show L ≤ L from le_rfl), hbL,
      div_self (ahom_pos M L).ne', mul_one]
  rw [hcombined, hcombinedInv] at hrepacked
  rw [hrepacked]
  have hfwd0 := scalarRatioLInf_nonneg U
    (fun x ↦ Real.exp (shellBlock L n (translatePotentialSample z omega) x +
      normalizerLogError M L n)) (fun _ ↦ 1)
  have hrev0 := scalarRatioLInf_nonneg U
    (fun x ↦ Real.exp (-(shellBlock L n (translatePotentialSample z omega) x +
      normalizerLogError M L n))) (fun _ ↦ 1)
  have hfwdSq := mul_self_le_mul_self hfwd0 hfwd
  have hrevSq := mul_self_le_mul_self hrev0 hrev
  dsimp only [W, z, U] at hfwdSq hrevSq ⊢
  nlinarith only [hfwdSq, hrevSq]


/-! ## Weighted positive-scale localization below `L` (threshold 12) -/

/-- Threshold-12 analogue of
`weightedPaperScalarProbe_cutoff_le_response_add_shells`; only the field
clause, the product clause and the cutoff response clause are read. -/
theorem aux_obl_ramp_threshold12_fourth_t12sat_weightedProbe_le_response_add_shells
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {n L m j : ℕ}
    (hnL : n ≤ L) (hLm : L ≤ m) {epsilon s : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (hj : j ≤ m) (hnj : n + 2 ≤ j) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hfield : GoodFieldOne m 0 epsilon s omega)
    (hprod : aux_obl_ramp_threshold12_fourth_t12sat_ProductTwelve m s omega)
    (hresp : GoodResponse M (some L) m 0 epsilon s omega)
    {R : SubdiffusiveProcess.CoarseGrainingVocab.TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ))
    (hann : triadicCubeShift R ∈ cube d j \ cube d (j - 1))
    {e : Vec d} (he : vecNormSq e = 1) :
    (3 : ℝ) ^ (-(3 / 2) * (s * ((m - n : ℕ) : ℝ))) *
        paperScalarProbe (originCube d (n : ℤ))
          (aCutoffFamily M L
            (translatePotentialSample (triadicCubeShift R) omega))
          (tailCoefficientCubeAverage M L m omega) e ≤
      2 * (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
          section6Response M n n omega (triadicCubeShift R) e +
        12 * (48 : ℝ) ^ 2 *
          (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
          (min 1 (supNormOn (cube d n)
                (shellBlock m n
                  (translatePotentialSample (triadicCubeShift R) omega)) +
              supNormOn (cube d n)
                (shellBlock m L
                  (translatePotentialSample (triadicCubeShift R) omega)) +
              _root_.SubdiffusiveProcess.Model.tauSq M.P * ((L - n : ℕ) : ℝ))) ^ 2 := by
  let T : ℝ := ((m - n : ℕ) : ℝ)
  let u : ℝ := s * T
  let A : ℝ := (3 : ℝ) ^ ((3 * s * T) / 16)
  let B : ℝ := min 1 (supNormOn (cube d n)
      (shellBlock m n (translatePotentialSample (triadicCubeShift R) omega)) +
    supNormOn (cube d n)
      (shellBlock m L (translatePotentialSample (triadicCubeShift R) omega)) +
    _root_.SubdiffusiveProcess.Model.tauSq M.P * ((L - n : ℕ) : ℝ))
  let Jloc : ℝ := section6Response M n n omega (triadicCubeShift R) e
  let E : ℝ := cutoffRatioError M n L
    (translatePotentialSample (triadicCubeShift R) omega)
    (Ch02.cubeDomain (originCube d (n : ℤ))) (ahom M L)
  let P : ℝ := paperScalarProbe (originCube d (n : ℤ))
    (aCutoffFamily M L
      (translatePotentialSample (triadicCubeShift R) omega))
    (ahom M L) e
  let G : ℝ := (3 : ℝ) ^ (u / 8)
  let w : ℝ := (3 : ℝ) ^ (-(3 / 2) * u)
  let v : ℝ := (3 : ℝ) ^ (-u)
  have hnm : n ≤ m := hnL.trans hLm
  have hgap : (m : ℝ) - (n : ℝ) = T := by
    dsimp only [T]
    rw [Nat.cast_sub hnm]
  have hRscale : R.scale = (n : ℤ) := scale_eq_of_mem_descendantsAtScale hR
  have hgrid : OnTriadicGrid n (triadicCubeShift R) :=
    onTriadicGrid_triadicCubeShift_of_scale hRscale
  have hJraw := hresp j n hj hnj (triadicCubeShift R)
    (by simpa using hgrid) (by simpa using hann) e he
  have hJ : Jloc ≤ G := by
    have hepsq : epsilon ^ 2 ≤ 1 := by nlinarith [sq_nonneg epsilon]
    have hpow0 : 0 ≤ (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 8) :=
      Real.rpow_nonneg (by norm_num) _
    have := hJraw.trans (mul_le_mul_of_nonneg_right hepsq hpow0)
    simpa only [Option.getD_some, min_eq_left hnL, one_mul, hgap, Jloc, G, u]
      using this
  have hJ0 : 0 ≤ Jloc := by
    dsimp only [Jloc, section6Response, paperScalarProbe]
    exact Ch02.responseJ_nonneg _ _ _ _
  have hP : P ≤ 2 * Jloc + 3 * E * (Jloc + 1) := by
    exact paperScalarProbe_translatedCutoff_le_section6Response_add_ratioError
      M n L omega (triadicCubeShift R) (ahom_pos M L) e he
  have hE : E ≤ 2 * ((48 : ℝ) * A * B) ^ 2 := by
    simpa only [E, A, B, T] using
      aux_obl_ramp_threshold12_fourth_t12sat_cutoffRatioError_ahom_le M hnL hLm hepsilon0
        hsLower hsUpper omega hfield hprod hR
  have hu0 : 0 ≤ u := by
    dsimp only [u, T]
    exact mul_nonneg
      ((mul_nonneg (by norm_num) (sq_nonneg M.delta)).trans hsLower)
      (by positivity)
  have hG1 : 1 ≤ G := one_le_responseGrowth hu0
  have hw0 : 0 ≤ w := Real.rpow_nonneg (by norm_num) _
  have hwv : w ≤ v := responseOuterWeight_le_residualWeight hu0
  have hcollapse : w * A ^ 2 * G = v := by
    dsimp only [w, A, G, v, u]
    convert responseErrorWeight_identity (s * T) using 1
    all_goals ring_nf
  have hweighted := weightedTransport_of_bounds hP hE hJ0 hJ hG1 hw0 hwv hcollapse
  have hb := tailCoefficientCubeAverage_eq_ahom_of_cutoff_le_scale M hLm omega
  rw [hb]
  simpa only [P, Jloc, B, w, v, u, T] using hweighted

/-! ## The cutoff response slot, read from the cutoff response clause -/

/-- Every atom of the cutoff response slot is at most `epsilon`; only the
cutoff response clause is read. -/
theorem aux_obl_ramp_threshold12_fourth_t12sat_cutoff_response_atom_le
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) {m : ℕ}
    {epsilon s : ℝ} (hepsilon0 : 0 ≤ epsilon) (hs0 : 0 ≤ s)
    {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d}
    (hresp : GoodResponse M (some L) m 0 epsilon s omega)
    {r : ℝ}
    (hr : r ∈ {r : ℝ | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧
        ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d j \ cube d (j - 1) ∧
        r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
          Real.sqrt (sSup {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
            t = section6Response M n (min n L) omega z e})}) :
    r ≤ epsilon := by
  rcases hr with ⟨j, n, hjm, hnj, z, hzgrid, hzann, rfl⟩
  have hnm : n ≤ m := by omega
  have hgap0 : 0 ≤ (m : ℝ) - (n : ℝ) :=
    sub_nonneg.mpr (by exact_mod_cast hnm)
  let A : Set ℝ := {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
    t = section6Response M n (min n L) omega z e}
  have hAne : A.Nonempty := by
    let i : Fin d := ⟨0, lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension⟩
    refine ⟨section6Response M n (min n L) omega z (Pi.single i 1),
      Pi.single i 1, ?_, rfl⟩
    rw [vecNormSq, vecDot, Finset.sum_eq_single i]
    · simp
    · intro b _ hbi
      simp [Pi.single_eq_of_ne hbi]
    · simp
  have hrespA : sSup A ≤ epsilon ^ 2 *
      (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 8) := by
    refine csSup_le hAne ?_
    rintro _ ⟨e, he, rfl⟩
    simpa only [A, Option.getD_some] using
      hresp j n hjm hnj z
        (by simpa only [sub_zero] using hzgrid)
        (by simpa only [sub_zero] using hzann) e he
  have hsqrt : Real.sqrt (sSup A) ≤ epsilon *
      (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 16) := by
    have hright0 : 0 ≤ epsilon *
        (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 16) := by positivity
    rw [Real.sqrt_le_iff]
    refine ⟨hright0, hrespA.trans_eq ?_⟩
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  calc
    (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) * Real.sqrt (sSup A) ≤
        (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
          (epsilon * (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 16)) := by
      gcongr
    _ = epsilon * (3 : ℝ) ^
        (-(7 * s / 16) * ((m : ℝ) - (n : ℝ))) := by
      calc
        _ = epsilon * ((3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
            (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 16)) := by ring
        _ = epsilon * (3 : ℝ) ^
            (-(s / 2) * ((m : ℝ) - (n : ℝ)) +
              (s * ((m : ℝ) - (n : ℝ))) / 16) := by
          rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        _ = _ := by
          congr 1
          ring_nf
    _ ≤ epsilon * 1 := by
      gcongr
      exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) hgap0)
    _ = epsilon := mul_one _

private theorem aux_obl_ramp_threshold12_fourth_t12sat_cutoffResponseSlot_bddAbove
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) {m : ℕ}
    {epsilon s : ℝ} (hepsilon0 : 0 ≤ epsilon) (hs0 : 0 ≤ s)
    {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d}
    (hresp : GoodResponse M (some L) m 0 epsilon s omega) :
    BddAbove {r : ℝ | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧
      ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d j \ cube d (j - 1) ∧
      r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
        Real.sqrt (sSup {q : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
          q = section6Response M n (min n L) omega z e})} :=
  ⟨epsilon, fun _ hr => aux_obl_ramp_threshold12_fourth_t12sat_cutoff_response_atom_le M L hepsilon0 hs0 hresp hr⟩

/-- The cutoff response slot is at most `epsilon` on the cutoff response
clause (the response part of the epsilon cap). -/
theorem aux_obl_ramp_threshold12_fourth_t12sat_cutoffResponseSlot_le_epsilon
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) {m : ℕ}
    {epsilon s : ℝ} (hepsilon0 : 0 ≤ epsilon) (hs0 : 0 ≤ s)
    {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d}
    (hresp : GoodResponse M (some L) m 0 epsilon s omega) :
    cutoffGoodScaleResponseSlot M L s m omega ≤ epsilon := by
  unfold cutoffGoodScaleResponseSlot
  exact Real.sSup_le
    (fun r hr => aux_obl_ramp_threshold12_fourth_t12sat_cutoff_response_atom_le M L hepsilon0 hs0 hresp hr)
    hepsilon0

private theorem aux_obl_ramp_threshold12_fourth_t12sat_cutoff_response_weight_le_slot_sq
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    {m n j : ℕ} (hnm : n ≤ m) {epsilon s : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hs0 : 0 ≤ s)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hresp : GoodResponse M (some L) m 0 epsilon s omega)
    (hjm : j ≤ m) (hnj : n + 2 ≤ j) {z e : Vec d}
    (hzgrid : OnTriadicGrid n z) (hzann : z ∈ cube d j \ cube d (j - 1))
    (he : vecNormSq e = 1) :
    (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
        section6Response M n (min n L) omega z e ≤
      cutoffGoodScaleResponseSlot M L s m omega ^ 2 := by
  let A : Set ℝ := {q : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
    q = section6Response M n (min n L) omega z e}
  have hAbdd : BddAbove A := by
    simpa only [A] using
      bddAbove_section6Response_unitSphere M n (min n L) omega z
  have hJ0 : 0 ≤ section6Response M n (min n L) omega z e := by
    unfold section6Response paperScalarProbe
    exact Ch02.responseJ_nonneg _ _ _ _
  have hA0 : 0 ≤ sSup A := hJ0.trans (le_csSup hAbdd ⟨e, he, rfl⟩)
  let atom := (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
    Real.sqrt (sSup A)
  have hatomMem : atom ∈ {r : ℝ | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧
      ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d j \ cube d (j - 1) ∧
      r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
        Real.sqrt (sSup {q : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
          q = section6Response M n (min n L) omega z e})} :=
    ⟨j, n, hjm, hnj, z, hzgrid, hzann, by simp only [atom, A]⟩
  have hatomLe : atom ≤ cutoffGoodScaleResponseSlot M L s m omega := by
    unfold cutoffGoodScaleResponseSlot
    exact le_csSup
      (aux_obl_ramp_threshold12_fourth_t12sat_cutoffResponseSlot_bddAbove M L hepsilon0 hs0 hresp) hatomMem
  have hatom0 : 0 ≤ atom := by dsimp only [atom]; positivity
  have hgap : (m : ℝ) - (n : ℝ) = ((m - n : ℕ) : ℝ) := by
    rw [Nat.cast_sub hnm]
  calc
    (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
        section6Response M n (min n L) omega z e ≤
      (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) * sSup A := by
        exact mul_le_mul_of_nonneg_left
          (le_csSup hAbdd ⟨e, he, rfl⟩) (Real.rpow_nonneg (by norm_num) _)
    _ = atom ^ 2 := by
      dsimp only [atom]
      rw [mul_pow, Real.sq_sqrt hA0, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 2
      rw [hgap]
      ring
    _ ≤ cutoffGoodScaleResponseSlot M L s m omega ^ 2 :=
      pow_le_pow_left₀ hatom0 hatomLe 2

/-! ## Shell and drift slots (event-free, copied from the upstream cutoff file) -/

private theorem aux_obl_ramp_threshold12_fourth_t12sat_localShellBlockSup_le_parent
    {m n k : ℕ} (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {R : SubdiffusiveProcess.CoarseGrainingVocab.TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)) :
    supNormOn (cube d n)
        (shellBlock m k (translatePotentialSample (triadicCubeShift R) omega)) ≤
      supNormOn (cube d m) (shellBlock m k omega) := by
  unfold supNormOn
  apply csSup_le
  · exact ⟨|shellBlock m k (translatePotentialSample (triadicCubeShift R) omega) 0|,
      0, aux_obl_ramp_threshold12_fourth_t12sat_zero_mem_cube _, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hscale : R.scale = (n : ℤ) := scale_eq_of_mem_descendantsAtScale hR
    have hxR : triadicCubeShift R + x ∈ openCubeSet R := by
      rw [openCubeSet_eq_translateSet_originCube_of_triadicCube,
        mem_translateSet_iff_sub_mem]
      simp only [hscale, add_sub_cancel_left]
      exact hx
    have hxM : triadicCubeShift R + x ∈ cube d m :=
      openCubeSet_subset_of_mem_descendantsAtScale
        (scale_le_of_mem_descendantsAtScale hR) hR hxR
    have hle := abs_apply_le_supNormOn_cube_of_continuous
      (aux_obl_ramp_threshold12_fourth_t12sat_shellBlock_continuous m k omega) hxM
    simp only [shellBlock_translatePotentialSample]
    convert hle using 1 <;> first | rfl | simp only [add_comm]

private theorem aux_obl_ramp_threshold12_fourth_t12sat_shellSlot_bddAbove
    (s : ℝ) (m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    BddAbove {r : ℝ | ∃ j ≤ m,
      r = (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
        supNormOn (cube d m) (shellBlock m j omega)} := by
  let F : ℕ → ℝ := fun j ↦
    (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
      supNormOn (cube d m) (shellBlock m j omega)
  refine ⟨Finset.sup' (Finset.range (m + 1))
      (Finset.nonempty_range_iff.mpr (by omega)) F, ?_⟩
  rintro _ ⟨j, hj, rfl⟩
  exact Finset.le_sup' F (Finset.mem_range.mpr (by omega))

private theorem aux_obl_ramp_threshold12_fourth_t12sat_shell_weight_le_slot_sq
    {m n k : ℕ} (hnk : n ≤ k) (hkm : k ≤ m) {s : ℝ} (hs0 : 0 ≤ s)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {R : SubdiffusiveProcess.CoarseGrainingVocab.TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)) :
    (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
        supNormOn (cube d n)
          (shellBlock m k (translatePotentialSample (triadicCubeShift R) omega)) ^ 2 ≤
      goodScaleShellSlot s m omega ^ 2 := by
  let G := supNormOn (cube d m) (shellBlock m k omega)
  let atom := (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (k : ℝ))) * G
  have hlocal := aux_obl_ramp_threshold12_fourth_t12sat_localShellBlockSup_le_parent (k := k) omega hR
  have hG0 : 0 ≤ G :=
    aux_obl_ramp_threshold12_fourth_t12sat_supNormOn_cube_nonneg m (aux_obl_ramp_threshold12_fourth_t12sat_shellBlock_continuous m k omega)
  have hatomMem : atom ∈ {r : ℝ | ∃ j ≤ m,
      r = (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
        supNormOn (cube d m) (shellBlock m j omega)} :=
    ⟨k, hkm, by simp only [atom, G]⟩
  have hatomLe : atom ≤ goodScaleShellSlot s m omega := by
    unfold goodScaleShellSlot
    exact le_csSup (aux_obl_ramp_threshold12_fourth_t12sat_shellSlot_bddAbove s m omega) hatomMem
  have hatom0 : 0 ≤ atom := by dsimp only [atom]; positivity
  have hlocal0 : 0 ≤ supNormOn (cube d n)
      (shellBlock m k (translatePotentialSample (triadicCubeShift R) omega)) :=
    aux_obl_ramp_threshold12_fourth_t12sat_supNormOn_cube_nonneg n (aux_obl_ramp_threshold12_fourth_t12sat_shellBlock_continuous m k _)
  have hw : (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) ≤
      ((3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (k : ℝ)))) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hgapReal : ((m - k : ℕ) : ℝ) ≤ ((m - n : ℕ) : ℝ) := by
      exact_mod_cast (show m - k ≤ m - n by omega)
    have hcast : (m : ℝ) - (k : ℝ) = ((m - k : ℕ) : ℝ) := by
      rw [Nat.cast_sub hkm]
    rw [hcast]
    have h0 : (0 : ℝ) ≤ ((m - k : ℕ) : ℝ) := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left hgapReal hs0
    push_cast
    nlinarith
  calc
    (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
        supNormOn (cube d n)
          (shellBlock m k (translatePotentialSample (triadicCubeShift R) omega)) ^ 2 ≤
      (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) * G ^ 2 := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlocal0 hlocal 2)
          (Real.rpow_nonneg (by norm_num) _)
    _ ≤ ((3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (k : ℝ)))) ^ 2 * G ^ 2 := by
      gcongr
    _ = atom ^ 2 := by simp only [atom]; ring
    _ ≤ goodScaleShellSlot s m omega ^ 2 :=
      pow_le_pow_left₀ hatom0 hatomLe 2

private theorem aux_obl_ramp_threshold12_fourth_t12sat_drift_weight_le
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {n L m : ℕ}
    (hnL : n ≤ L) (hLm : L ≤ m) {s : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) :
    (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
        (_root_.SubdiffusiveProcess.Model.tauSq M.P * ((L - n : ℕ) : ℝ)) ^ 2 ≤
      2 * (s⁻¹ * M.delta ^ 2) ^ 2 := by
  have hgapReal : ((L - n : ℕ) : ℝ) ≤ ((m - n : ℕ) : ℝ) := by
    exact_mod_cast (show L - n ≤ m - n by omega)
  have htau0 : 0 ≤ _root_.SubdiffusiveProcess.Model.tauSq M.P := M.G4.tauSq_pos.le
  have hsmall : (_root_.SubdiffusiveProcess.Model.tauSq M.P * ((L - n : ℕ) : ℝ)) ^ 2 ≤
      (_root_.SubdiffusiveProcess.Model.tauSq M.P * ((m - n : ℕ) : ℝ)) ^ 2 := by
    apply pow_le_pow_left₀ (mul_nonneg htau0 (by positivity))
    exact mul_le_mul_of_nonneg_left hgapReal htau0
  calc
    _ ≤ (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
        (_root_.SubdiffusiveProcess.Model.tauSq M.P * ((m - n : ℕ) : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg (by norm_num) _)
    _ ≤ 2 * (s⁻¹) ^ 2 * M.delta ^ 4 :=
      three_rpow_neg_mul_tauSq_sq_le M hsLower (by positivity)
    _ = 2 * (s⁻¹ * M.delta ^ 2) ^ 2 := by ring

/-! ## The positive-scale budget -/

/-- Threshold-12 square budget for every nonnegative cutoff annular atom. -/
def aux_obl_ramp_threshold12_fourth_t12sat_positiveBudget
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (s : ℝ) (m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  2 * cutoffGoodScaleResponseSlot M L s m omega ^ 2 +
    36 * (48 : ℝ) ^ 2 *
      (2 * goodScaleShellSlot s m omega ^ 2 +
        2 * (s⁻¹ * M.delta ^ 2) ^ 2)

theorem aux_obl_ramp_threshold12_fourth_t12sat_positiveBudget_nonneg
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (s : ℝ) (m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ aux_obl_ramp_threshold12_fourth_t12sat_positiveBudget M L s m omega := by
  unfold aux_obl_ramp_threshold12_fourth_t12sat_positiveBudget
  positivity

private theorem aux_obl_ramp_threshold12_fourth_t12sat_weightedProbe_below_le_budget
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {n L m j : ℕ}
    (hnL : n ≤ L) (hLm : L ≤ m) {epsilon s : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (hj : j ≤ m) (hnj : n + 2 ≤ j) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hfield : GoodFieldOne m 0 epsilon s omega)
    (hprod : aux_obl_ramp_threshold12_fourth_t12sat_ProductTwelve m s omega)
    (hresp : GoodResponse M (some L) m 0 epsilon s omega)
    {R : SubdiffusiveProcess.CoarseGrainingVocab.TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ))
    (hann : triadicCubeShift R ∈ cube d j \ cube d (j - 1))
    {e : Vec d} (he : vecNormSq e = 1) :
    (3 : ℝ) ^ (-(3 / 2) * (s * ((m - n : ℕ) : ℝ))) *
        paperScalarProbe (originCube d (n : ℤ))
          (aCutoffFamily M L
            (translatePotentialSample (triadicCubeShift R) omega))
          (tailCoefficientCubeAverage M L m omega) e ≤
      aux_obl_ramp_threshold12_fourth_t12sat_positiveBudget M L s m omega := by
  have hnm : n ≤ m := hnL.trans hLm
  have hs0 : 0 ≤ s :=
    (mul_nonneg (by norm_num) (sq_nonneg M.delta)).trans hsLower
  have hraw := aux_obl_ramp_threshold12_fourth_t12sat_weightedProbe_le_response_add_shells
    M hnL hLm hepsilon0 hepsilon1 hsLower hsUpper hj hnj omega hfield hprod hresp
    hR hann he
  have hrespSq := aux_obl_ramp_threshold12_fourth_t12sat_cutoff_response_weight_le_slot_sq M L hnm hepsilon0 hs0
    omega hresp hj hnj
    (onTriadicGrid_triadicCubeShift_of_scale
      (scale_eq_of_mem_descendantsAtScale hR)) hann he
  have hrespN : (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
      section6Response M n n omega (triadicCubeShift R) e ≤
      cutoffGoodScaleResponseSlot M L s m omega ^ 2 := by
    simpa only [min_eq_left hnL] using hrespSq
  have hshellN := aux_obl_ramp_threshold12_fourth_t12sat_shell_weight_le_slot_sq (show n ≤ n from le_rfl)
    hnm hs0 omega hR
  have hshellL := aux_obl_ramp_threshold12_fourth_t12sat_shell_weight_le_slot_sq hnL hLm hs0 omega hR
  have hdrift := aux_obl_ramp_threshold12_fourth_t12sat_drift_weight_le M hnL hLm hsLower
  let v : ℝ := (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ)))
  let G1 := supNormOn (cube d n)
    (shellBlock m n (translatePotentialSample (triadicCubeShift R) omega))
  let G2 := supNormOn (cube d n)
    (shellBlock m L (translatePotentialSample (triadicCubeShift R) omega))
  let rho := _root_.SubdiffusiveProcess.Model.tauSq M.P * ((L - n : ℕ) : ℝ)
  have hv0 : 0 ≤ v := Real.rpow_nonneg (by norm_num) _
  have hsplit := min_one_add_three_sq_le_three_sum_sq G1 G2 rho
  have hweightedSplit : v * min 1 (G1 + G2 + rho) ^ 2 ≤
      3 * (v * G1 ^ 2 + v * G2 ^ 2 + v * rho ^ 2) := by
    have := mul_le_mul_of_nonneg_left hsplit hv0
    linarith
  have hcomponents : v * G1 ^ 2 + v * G2 ^ 2 + v * rho ^ 2 ≤
      2 * goodScaleShellSlot s m omega ^ 2 +
        2 * (s⁻¹ * M.delta ^ 2) ^ 2 := by
    dsimp only [v, G1, G2, rho]
    linarith
  have herror : 12 * (48 : ℝ) ^ 2 *
      (v * min 1 (G1 + G2 + rho) ^ 2) ≤
      36 * (48 : ℝ) ^ 2 *
        (2 * goodScaleShellSlot s m omega ^ 2 +
          2 * (s⁻¹ * M.delta ^ 2) ^ 2) := by
    calc
      _ ≤ 12 * (48 : ℝ) ^ 2 *
          (3 * (v * G1 ^ 2 + v * G2 ^ 2 + v * rho ^ 2)) := by
        gcongr
      _ = 36 * (48 : ℝ) ^ 2 *
          (v * G1 ^ 2 + v * G2 ^ 2 + v * rho ^ 2) := by ring
      _ ≤ _ := by gcongr
  unfold aux_obl_ramp_threshold12_fourth_t12sat_positiveBudget
  dsimp only [v, G1, G2, rho] at herror
  calc
    _ ≤ 2 * (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
          section6Response M n n omega (triadicCubeShift R) e +
        12 * (48 : ℝ) ^ 2 *
          ((3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
            min 1 (supNormOn (cube d n)
                  (shellBlock m n
                    (translatePotentialSample (triadicCubeShift R) omega)) +
                supNormOn (cube d n)
                  (shellBlock m L
                    (translatePotentialSample (triadicCubeShift R) omega)) +
                _root_.SubdiffusiveProcess.Model.tauSq M.P * ((L - n : ℕ) : ℝ)) ^ 2) := by
      simpa only [mul_assoc] using hraw
    _ ≤ 2 * cutoffGoodScaleResponseSlot M L s m omega ^ 2 +
        36 * (48 : ℝ) ^ 2 *
          (2 * goodScaleShellSlot s m omega ^ 2 +
            2 * (s⁻¹ * M.delta ^ 2) ^ 2) := by
      have hmain' : 2 * (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
          section6Response M n n omega (triadicCubeShift R) e ≤
          2 * cutoffGoodScaleResponseSlot M L s m omega ^ 2 := by
        linarith
      exact add_le_add hmain' herror

/-- Every nonnegative annular atom on a parent scale above `L` is controlled
by the threshold-12 cutoff positive budget.  The local scale is split at `L`:
below it by sensitivity, above it by literal coefficient equality. -/
theorem aux_obl_ramp_threshold12_fourth_t12sat_positive_annular_atom_le_budget
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ} (hLm : L ≤ m)
    {epsilon s : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hfield : GoodFieldOne m 0 epsilon s omega)
    (hprod : aux_obl_ramp_threshold12_fourth_t12sat_ProductTwelve m s omega)
    (hresp : GoodResponse M (some L) m 0 epsilon s omega)
    (p : AnnularPairTwo d (m : ℤ)) (hscale0 : 0 ≤ p.1.1.scale) :
    ENNReal.ofReal ((3 : ℝ) ^ (-(3 * s / 2) *
          ((m : ℝ) - (p.1.1.scale : ℝ)))) *
        section6LocalProbeMax M L omega 0
          (tailCoefficientCubeAverage M L m omega) p.1.1 ≤
      ENNReal.ofReal (aux_obl_ramp_threshold12_fourth_t12sat_positiveBudget M L s m omega) := by
  obtain ⟨hj, hscale, hann⟩ := p.2
  let n : ℕ := p.1.1.scale.toNat
  let jn : ℕ := p.1.2.toNat
  have hncast : (n : ℤ) = p.1.1.scale := Int.toNat_of_nonneg hscale0
  have hj0 : 0 ≤ p.1.2 := by omega
  have hjcast : (jn : ℤ) = p.1.2 := Int.toNat_of_nonneg hj0
  have hnmZ : (n : ℤ) ≤ (m : ℤ) := by rw [hncast]; omega
  have hjmZ : (jn : ℤ) ≤ (m : ℤ) := by rw [hjcast]; exact hj
  have hnjZ : (n : ℤ) + 2 ≤ (jn : ℤ) := by rw [hncast, hjcast]; omega
  have hnm : n ≤ m := by exact_mod_cast hnmZ
  have hjm : jn ≤ m := by exact_mod_cast hjmZ
  have hnj : n + 2 ≤ jn := by exact_mod_cast hnjZ
  have hR : p.1.1 ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ) := by
    rw [hncast]
    exact annularCube_mem_descendantsAtScale hj hscale hann
  have hweight :
      (3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (p.1.1.scale : ℝ))) =
        (3 : ℝ) ^ (-(3 / 2) * (s * ((m - n : ℕ) : ℝ))) := by
    congr 1
    have hgap : (m : ℝ) - (n : ℝ) = ((m - n : ℕ) : ℝ) := by
      rw [Nat.cast_sub hnm]
    have hnreal : (n : ℝ) = (p.1.1.scale : ℝ) := by exact_mod_cast hncast
    rw [← hnreal, hgap]
    ring
  have hs0 : 0 ≤ s :=
    (mul_nonneg (by norm_num) (sq_nonneg M.delta)).trans hsLower
  unfold section6LocalProbeMax
  rw [ENNReal.mul_iSup]
  refine iSup_le fun e ↦ ?_
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _), hweight]
  apply ENNReal.ofReal_le_ofReal
  rcases le_total n L with hnL | hLn
  · simpa only [hncast, Section6Covariance.translatePotentialSample_zero] using
      aux_obl_ramp_threshold12_fourth_t12sat_weightedProbe_below_le_budget M hnL hLm hepsilon0 hepsilon1
        hsLower hsUpper hjm hnj omega hfield hprod hresp hR
        (by simpa only [hjcast] using hann) e.2
  · have hmin : min n L = L := min_eq_right hLn
    have hrespSq := aux_obl_ramp_threshold12_fourth_t12sat_cutoff_response_weight_le_slot_sq M L hnm hepsilon0 hs0
      omega hresp hjm hnj
      (onTriadicGrid_triadicCubeShift_of_scale
        (scale_eq_of_mem_descendantsAtScale hR))
      (by simpa only [hjcast] using hann) e.2
    rw [hmin] at hrespSq
    have hu0 : 0 ≤ s * ((m - n : ℕ) : ℝ) :=
      mul_nonneg hs0 (by positivity)
    have houter := responseOuterWeight_le_residualWeight hu0
    have hJ0 : 0 ≤ section6Response M n L omega (triadicCubeShift p.1.1) e := by
      unfold section6Response paperScalarProbe
      exact Ch02.responseJ_nonneg _ _ _ _
    have hb := tailCoefficientCubeAverage_eq_ahom_of_cutoff_le_scale M hLm omega
    have heq : paperScalarProbe (originCube d (n : ℤ))
        (aCutoffFamily M L
          (translatePotentialSample (triadicCubeShift p.1.1) omega))
        (tailCoefficientCubeAverage M L m omega) e =
        section6Response M n L omega (triadicCubeShift p.1.1) e := by
      rw [hb]
      rfl
    rw [Section6Covariance.translatePotentialSample_zero]
    rw [← hncast, heq]
    calc
      (3 : ℝ) ^ (-(3 / 2) * (s * ((m - n : ℕ) : ℝ))) *
          section6Response M n L omega (triadicCubeShift p.1.1) e ≤
        (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
          section6Response M n L omega (triadicCubeShift p.1.1) e :=
        mul_le_mul_of_nonneg_right houter hJ0
      _ ≤ cutoffGoodScaleResponseSlot M L s m omega ^ 2 := hrespSq
      _ ≤ aux_obl_ramp_threshold12_fourth_t12sat_positiveBudget M L s m omega := by
        unfold aux_obl_ramp_threshold12_fourth_t12sat_positiveBudget
        have hsquare := sq_nonneg (cutoffGoodScaleResponseSlot M L s m omega)
        have hrest : 0 ≤ 36 * (48 : ℝ) ^ 2 *
            (2 * goodScaleShellSlot s m omega ^ 2 +
              2 * (s⁻¹ * M.delta ^ 2) ^ 2) := by positivity
        linarith


/-! ## The negative-scale branch ending at `L` (threshold 12) -/

private theorem aux_obl_ramp_threshold12_fourth_t12sat_abs_fullShellBlock_cutoff_le_parentSup_add
    {L m : ℕ} (hLm : L ≤ m) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {x : Vec d} (hx : x ∈ cube d m) :
    |fullShellBlock L omega x| ≤
      supNormOn (cube d m) (fullShellBlock m omega) +
        supNormOn (cube d m) (shellBlock m L omega) := by
  rw [fullShellBlock_cutoff_eq_parent_sub_shellBlock hLm]
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · exact abs_apply_le_supNormOn_cube_of_continuous
      (aux_obl_ramp_threshold12_fourth_t12sat_fullShellBlock_continuous m omega) hx
  · exact abs_apply_le_supNormOn_cube_of_continuous
      (aux_obl_ramp_threshold12_fourth_t12sat_shellBlock_continuous m L omega) hx

/-- Threshold-12 envelope for the two parent blocks produced by the clipped
low block `g_L = g_m - g_(m,L)`. -/
theorem aux_obl_ramp_threshold12_fourth_t12sat_exp_parentFull_add_shellSup_le
    {L m : ℕ} (hLm : L ≤ m) {epsilon s : ℝ} (hepsilon : 0 ≤ epsilon)
    (hs0 : 0 ≤ s) (hsUpper : s ≤ 1 / 2)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hfield : GoodFieldOne m 0 epsilon s omega)
    (hprod : aux_obl_ramp_threshold12_fourth_t12sat_ProductTwelve m s omega) :
    Real.exp (supNormOn (cube d m) (fullShellBlock m omega) +
        supNormOn (cube d m) (shellBlock m L omega)) ≤
      144 * (3 : ℝ) ^ ((s * (m : ℝ)) / 4) := by
  have hfull := aux_obl_ramp_threshold12_fourth_t12sat_exp_supNormOn_fullShellBlock_le m hepsilon hsUpper
    omega hfield hprod
  have hshellPoint : ∀ x ∈ cube d m,
      Real.exp |shellBlock m L omega x| ≤
        12 * (3 : ℝ) ^ ((s * ((m - L : ℕ) : ℝ)) / 8) := by
    intro x hx
    exact aux_obl_ramp_threshold12_fourth_t12sat_exp_abs_shellBlock_le hLm le_rfl hepsilon hsUpper omega
      hfield hprod hx
  have hshellSup : Real.exp (supNormOn (cube d m) (shellBlock m L omega)) ≤
      12 * (3 : ℝ) ^ ((s * ((m - L : ℕ) : ℝ)) / 8) := by
    let B := 12 * (3 : ℝ) ^ ((s * ((m - L : ℕ) : ℝ)) / 8)
    have hB0 : 0 < B := by dsimp only [B]; positivity
    have hlog : supNormOn (cube d m) (shellBlock m L omega) ≤ Real.log B := by
      unfold supNormOn
      apply csSup_le
      · exact ⟨|shellBlock m L omega 0|, 0, aux_obl_ramp_threshold12_fourth_t12sat_zero_mem_cube _, rfl⟩
      · rintro _ ⟨x, hx, rfl⟩
        rw [← Real.log_exp |shellBlock m L omega x|]
        exact Real.log_le_log (Real.exp_pos _) (hshellPoint x hx)
    calc
      _ ≤ Real.exp (Real.log B) := Real.exp_le_exp.mpr hlog
      _ = B := Real.exp_log hB0
  rw [Real.exp_add]
  calc
    _ ≤ (12 * (3 : ℝ) ^ ((s * (m : ℝ)) / 8)) *
        (12 * (3 : ℝ) ^ ((s * ((m - L : ℕ) : ℝ)) / 8)) :=
      mul_le_mul hfull hshellSup (Real.exp_pos _).le (by positivity)
    _ ≤ (12 * (3 : ℝ) ^ ((s * (m : ℝ)) / 8)) *
        (12 * (3 : ℝ) ^ ((s * (m : ℝ)) / 8)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hgapReal : ((m - L : ℕ) : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast Nat.sub_le m L
      have := mul_le_mul_of_nonneg_left hgapReal hs0
      linarith
    _ = 144 * ((3 : ℝ) ^ ((s * (m : ℝ)) / 8) *
        (3 : ℝ) ^ ((s * (m : ℝ)) / 8)) := by ring
    _ = 144 * (3 : ℝ) ^ ((s * (m : ℝ)) / 4) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 2
      ring

private theorem aux_obl_ramp_threshold12_fourth_t12sat_exp_abs_subunitLogError_cutoff_le
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ} (hLm : L ≤ m)
    {s : ℝ} (hsLower : 64 * M.delta ^ 2 ≤ s) :
    Real.exp |subunitLogError M L| ≤
      (3 : ℝ) ^ ((s * ((m : ℝ) + 1)) / 16) := by
  have hs0 : 0 ≤ s :=
    (mul_nonneg (by norm_num) (sq_nonneg M.delta)).trans hsLower
  have hlogTwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have htau : _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ 4 * M.delta ^ 2 := by
    calc
      _ ≤ (Real.log 2 / 2) * M.delta ^ 2 := tauSq_le_delta_sq M
      _ ≤ 4 * M.delta ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg M.delta)
  have hL1 : (0 : ℝ) ≤ (L : ℝ) + 1 := by positivity
  have hm1 : (L : ℝ) + 1 ≤ (m : ℝ) + 1 := by
    exact_mod_cast Nat.add_le_add_right hLm 1
  have herr := abs_subunitLogError_le M L
  have hbudget : _root_.SubdiffusiveProcess.Model.tauSq M.P * ((L : ℝ) + 1) ≤
      (s * ((m : ℝ) + 1)) / 16 := by
    have h1 := mul_le_mul_of_nonneg_right htau hL1
    have h2 := mul_le_mul_of_nonneg_right hsLower
      (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1)
    nlinarith [mul_le_mul_of_nonneg_left hm1 M.G4.tauSq_pos.le]
  have harg := herr.trans hbudget
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  apply Real.exp_le_exp.mpr
  have hlog3 : 1 ≤ Real.log 3 := by
    have hexp : Real.exp 1 < (3 : ℝ) :=
      Real.exp_one_lt_d9.trans (by norm_num)
    have hlog := Real.log_lt_log (Real.exp_pos 1) hexp
    simpa only [Real.log_exp] using hlog.le
  exact harg.trans (by
    have hnonneg : 0 ≤ (s * ((m : ℝ) + 1)) / 16 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hlog3 hnonneg])

/-- Threshold-12 pointwise ratio energy for the direct negative-scale
response; every coefficient ratio ends at `L = min m L`, against the
saturated normalizer `ahom M L`. -/
theorem aux_obl_ramp_threshold12_fourth_t12sat_cutoffSubunit_ratioEnergy_le
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ} (hLm : L ≤ m)
    {epsilon s : ℝ} (hepsilon : 0 ≤ epsilon)
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hfield : GoodFieldOne m 0 epsilon s omega)
    (hprod : aux_obl_ramp_threshold12_fourth_t12sat_ProductTwelve m s omega)
    {x : Vec d} (hx : x ∈ cube d m) :
    (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x / ahom M L - 1) ^ 2 +
        (ahom M L / _root_.SubdiffusiveProcess.Model.aCutoff M L omega x - 1) ^ 2 ≤
      (576 * (3 : ℝ) ^ ((s * (m : ℝ)) / 4) *
        (3 : ℝ) ^ ((s * ((m : ℝ) + 1)) / 16) *
        min 1 (supNormOn (cube d m) (fullShellBlock m omega) +
          supNormOn (cube d m) (shellBlock m L omega) +
          _root_.SubdiffusiveProcess.Model.tauSq M.P * ((L : ℝ) + 1))) ^ 2 := by
  let g := fullShellBlock L omega x
  let r := subunitLogError M L
  let G := supNormOn (cube d m) (fullShellBlock m omega) +
    supNormOn (cube d m) (shellBlock m L omega)
  let Rho := |r|
  let Eg := 144 * (3 : ℝ) ^ ((s * (m : ℝ)) / 4)
  let Er := (3 : ℝ) ^ ((s * ((m : ℝ) + 1)) / 16)
  have hs0 : 0 ≤ s :=
    (mul_nonneg (by norm_num) (sq_nonneg M.delta)).trans hsLower
  have hG0 : 0 ≤ G := by
    dsimp only [G]
    exact add_nonneg
      (aux_obl_ramp_threshold12_fourth_t12sat_supNormOn_cube_nonneg m (aux_obl_ramp_threshold12_fourth_t12sat_fullShellBlock_continuous m omega))
      (aux_obl_ramp_threshold12_fourth_t12sat_supNormOn_cube_nonneg m (aux_obl_ramp_threshold12_fourth_t12sat_shellBlock_continuous m L omega))
  have hR0 : 0 ≤ Rho := by dsimp only [Rho]; exact abs_nonneg _
  have hg : |g| ≤ G := by
    dsimp only [g, G]
    exact aux_obl_ramp_threshold12_fourth_t12sat_abs_fullShellBlock_cutoff_le_parentSup_add hLm omega hx
  have hr : |r| ≤ Rho := le_rfl
  have hEg : Real.exp G ≤ Eg := by
    dsimp only [G, Eg]
    exact aux_obl_ramp_threshold12_fourth_t12sat_exp_parentFull_add_shellSup_le hLm hepsilon hs0 hsUpper
      omega hfield hprod
  have hEr : Real.exp Rho ≤ Er := by
    dsimp only [Rho, r, Er]
    exact aux_obl_ramp_threshold12_fourth_t12sat_exp_abs_subunitLogError_cutoff_le M hLm hsLower
  have hdev := combined_ratio_deviation_sum_le_weighted_min
    (A := (1 : ℝ)) (Ainv := (1 : ℝ)) (g := g) (r := r)
    (S := (0 : ℝ)) (G := G) (R := Rho) (C := (0 : ℝ))
    (Eg := Eg) (Er := Er) (by norm_num) (by norm_num) hG0 hR0
    (by norm_num) (by norm_num) hg hr hEg hEr
  have hfactor : 2 * ((0 : ℝ) + 2) * (Eg * Er) =
      576 * (3 : ℝ) ^ ((s * (m : ℝ)) / 4) *
        (3 : ℝ) ^ ((s * ((m : ℝ) + 1)) / 16) := by
    dsimp only [Eg, Er]
    ring
  have hrho : Rho ≤ _root_.SubdiffusiveProcess.Model.tauSq M.P * ((L : ℝ) + 1) := by
    dsimp only [Rho, r]
    exact abs_subunitLogError_le M L
  have hmin : min 1 (0 + G + Rho) ≤ min 1
      (G + _root_.SubdiffusiveProcess.Model.tauSq M.P * ((L : ℝ) + 1)) := by
    apply min_le_min le_rfl
    linarith
  have hcut : _root_.SubdiffusiveProcess.Model.aCutoff M L omega x / ahom M L =
      Real.exp (g + r) := by
    have ha := aCutoff_eq_exp_fullShellBlock M L omega x
    have hinv : (ahom M L)⁻¹ = Real.exp (-Real.log (ahom M L)) := by
      calc
        (ahom M L)⁻¹ = (Real.exp (Real.log (ahom M L)))⁻¹ := by
          rw [Real.exp_log (ahom_pos M L)]
        _ = Real.exp (-Real.log (ahom M L)) := (Real.exp_neg _).symm
    rw [div_eq_mul_inv, ha, hinv, ← Real.exp_add]
    dsimp only [g, r, subunitLogError]
    congr 1
    ring
  have hcutInv : ahom M L / _root_.SubdiffusiveProcess.Model.aCutoff M L omega x =
      Real.exp (-(g + r)) := by
    calc
      _ = (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x / ahom M L)⁻¹ := by
        rw [inv_div]
      _ = (Real.exp (g + r))⁻¹ := by rw [hcut]
      _ = _ := by rw [← Real.exp_neg]
  rw [hcut, hcutInv]
  have hsq : (Real.exp (g + r) - 1) ^ 2 +
      (Real.exp (-(g + r)) - 1) ^ 2 ≤
      (|Real.exp (g + r) - 1| + |Real.exp (-(g + r)) - 1|) ^ 2 := by
    rw [← sq_abs (Real.exp (g + r) - 1),
      ← sq_abs (Real.exp (-(g + r)) - 1)]
    nlinarith [abs_nonneg (Real.exp (g + r) - 1),
      abs_nonneg (Real.exp (-(g + r)) - 1)]
  refine hsq.trans ?_
  rw [hfactor] at hdev
  have hscaled := mul_le_mul_of_nonneg_left hmin (show
    0 ≤ 576 * (3 : ℝ) ^ (s * (m : ℝ) / 4) *
      (3 : ℝ) ^ (s * ((m : ℝ) + 1) / 16) by positivity)
  have hdev' := hdev.trans hscaled
  exact pow_le_pow_left₀ (by positivity)
    (by simpa only [one_mul, mul_one, zero_add] using hdev') 2

private theorem aux_obl_ramp_threshold12_fourth_t12sat_subunit_envelope_weight
    {s : ℝ} (hsUpper : s ≤ 1 / 2) (m : ℕ) :
    (3 : ℝ) ^ (-(3 * s / 2) * (m : ℝ)) *
        (576 * (3 : ℝ) ^ ((s * (m : ℝ)) / 4) *
          (3 : ℝ) ^ ((s * ((m : ℝ) + 1)) / 16)) ^ 2 ≤
      2 * 576 ^ 2 * (3 : ℝ) ^ (-(7 * s / 8) * (m : ℝ)) := by
  have hsFactor : (3 : ℝ) ^ (s / 8) ≤ 2 := by
    have hmono : (3 : ℝ) ^ (s / 8) ≤ (3 : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rw [← Real.sqrt_eq_rpow] at hmono
    have hsqrt3 : Real.sqrt 3 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    exact hmono.trans hsqrt3
  have hexact : (3 : ℝ) ^ (-(3 * s / 2) * (m : ℝ)) *
      (576 * (3 : ℝ) ^ ((s * (m : ℝ)) / 4) *
        (3 : ℝ) ^ ((s * ((m : ℝ) + 1)) / 16)) ^ 2 =
      576 ^ 2 * (3 : ℝ) ^ (-(7 * s / 8) * (m : ℝ)) *
        (3 : ℝ) ^ (s / 8) := by
    have hpow1 : ((3 : ℝ) ^ ((s * (m : ℝ)) / 4)) ^ 2 =
        (3 : ℝ) ^ (2 * ((s * (m : ℝ)) / 4)) := by
      rw [pow_two, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    have hpow2 : ((3 : ℝ) ^ ((s * ((m : ℝ) + 1)) / 16)) ^ 2 =
        (3 : ℝ) ^ (2 * ((s * ((m : ℝ) + 1)) / 16)) := by
      rw [pow_two, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    rw [mul_pow, mul_pow, hpow1, hpow2]
    calc
      _ = 576 ^ 2 * ((3 : ℝ) ^ (-(3 * s / 2) * (m : ℝ)) *
          (3 : ℝ) ^ (2 * (s * (m : ℝ) / 4)) *
          (3 : ℝ) ^ (2 * (s * ((m : ℝ) + 1) / 16))) := by ring
      _ = 576 ^ 2 * (3 : ℝ) ^
          (-(3 * s / 2) * (m : ℝ) + 2 * (s * (m : ℝ) / 4) +
            2 * (s * ((m : ℝ) + 1) / 16)) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      _ = _ := by
        have hexp : -(3 * s / 2) * (m : ℝ) + 2 * (s * (m : ℝ) / 4) +
            2 * (s * ((m : ℝ) + 1) / 16) =
            -(7 * s / 8) * (m : ℝ) + s / 8 := by ring
        rw [hexp, Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        ring
  rw [hexact]
  have hbase0 : 0 ≤ 576 ^ 2 *
      (3 : ℝ) ^ (-(7 * s / 8) * (m : ℝ)) := by positivity
  have := mul_le_mul_of_nonneg_left hsFactor hbase0
  linarith

private theorem aux_obl_ramp_threshold12_fourth_t12sat_subunit_decay_le_fullSlot_sq
    {s : ℝ} (hs0 : 0 ≤ s) (m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    (3 : ℝ) ^ (-(7 * s / 8) * (m : ℝ)) *
        supNormOn (cube d m) (fullShellBlock m omega) ^ 2 ≤
      goodScaleFullSlot s m omega ^ 2 := by
  unfold goodScaleFullSlot
  rw [mul_pow]
  have hpow : ((3 : ℝ) ^ (-(s / 8) * (m : ℝ))) ^ 2 =
      (3 : ℝ) ^ (2 * (-(s / 8) * (m : ℝ))) := by
    rw [pow_two, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  rw [hpow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have := mul_nonneg hs0 (Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))
  nlinarith

private theorem aux_obl_ramp_threshold12_fourth_t12sat_subunit_decay_le_shellSlot_sq
    {L m : ℕ} (hLm : L ≤ m) {s : ℝ} (hs0 : 0 ≤ s)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    (3 : ℝ) ^ (-(7 * s / 8) * (m : ℝ)) *
        supNormOn (cube d m) (shellBlock m L omega) ^ 2 ≤
      goodScaleShellSlot s m omega ^ 2 := by
  let G := supNormOn (cube d m) (shellBlock m L omega)
  let atom := (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (L : ℝ))) * G
  have hG0 : 0 ≤ G :=
    aux_obl_ramp_threshold12_fourth_t12sat_supNormOn_cube_nonneg m (aux_obl_ramp_threshold12_fourth_t12sat_shellBlock_continuous m L omega)
  have hatomMem : atom ∈ {r : ℝ | ∃ j ≤ m,
      r = (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
        supNormOn (cube d m) (shellBlock m j omega)} :=
    ⟨L, hLm, by simp only [atom, G]⟩
  have hatomLe : atom ≤ goodScaleShellSlot s m omega := by
    unfold goodScaleShellSlot
    exact le_csSup (aux_obl_ramp_threshold12_fourth_t12sat_shellSlot_bddAbove s m omega) hatomMem
  have hatom0 : 0 ≤ atom := by dsimp only [atom]; positivity
  have hw : (3 : ℝ) ^ (-(7 * s / 8) * (m : ℝ)) ≤
      ((3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (L : ℝ)))) ^ 2 := by
    rw [pow_two, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hLmReal : (L : ℝ) ≤ (m : ℝ) := by exact_mod_cast hLm
    have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
    have h1 := mul_nonneg hs0 hL0
    have h2 := mul_le_mul_of_nonneg_left hLmReal hs0
    nlinarith
  calc
    _ ≤ ((3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (L : ℝ)))) ^ 2 * G ^ 2 :=
      mul_le_mul_of_nonneg_right hw (sq_nonneg G)
    _ = atom ^ 2 := by simp only [atom]; ring
    _ ≤ goodScaleShellSlot s m omega ^ 2 :=
      pow_le_pow_left₀ hatom0 hatomLe 2

private theorem aux_obl_ramp_threshold12_fourth_t12sat_subunit_decay_drift_le
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ} (hLm : L ≤ m)
    {s : ℝ} (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2) :
    (3 : ℝ) ^ (-(7 * s / 8) * (m : ℝ)) *
        (_root_.SubdiffusiveProcess.Model.tauSq M.P * ((L : ℝ) + 1)) ^ 2 ≤
      16 * (s⁻¹ * M.delta ^ 2) ^ 2 := by
  have hs : 0 < s :=
    (mul_pos (by norm_num) (sq_pos_of_pos M.shellPrefix.delta_pos)).trans_le hsLower
  have hLm1 : (L : ℝ) + 1 ≤ (m : ℝ) + 1 := by
    exact_mod_cast Nat.add_le_add_right hLm 1
  have hrho : (_root_.SubdiffusiveProcess.Model.tauSq M.P * ((L : ℝ) + 1)) ^ 2 ≤
      (_root_.SubdiffusiveProcess.Model.tauSq M.P * ((m : ℝ) + 1)) ^ 2 := by
    apply pow_le_pow_left₀
      (mul_nonneg M.G4.tauSq_pos.le (by positivity : (0 : ℝ) ≤ (L : ℝ) + 1))
    exact mul_le_mul_of_nonneg_left hLm1 M.G4.tauSq_pos.le
  have hdecay : (3 : ℝ) ^ (-(7 * s / 8) * (m : ℝ)) ≤
      2 * (3 : ℝ) ^ (-((s / 2) * ((m : ℝ) + 1))) := by
    have hsplit : -(7 * s / 8) * (m : ℝ) ≤
        s / 2 - (s / 2) * ((m : ℝ) + 1) := by
      have := mul_nonneg hs.le (Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))
      nlinarith
    have hpow := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 3) hsplit
    have hrewrite : (3 : ℝ) ^
        (s / 2 - (s / 2) * ((m : ℝ) + 1)) =
        (3 : ℝ) ^ (s / 2) *
          (3 : ℝ) ^ (-((s / 2) * ((m : ℝ) + 1))) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
    rw [hrewrite] at hpow
    have hsPow : (3 : ℝ) ^ (s / 2) ≤ 2 := by
      have hmono : (3 : ℝ) ^ (s / 2) ≤ (3 : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      rw [← Real.sqrt_eq_rpow] at hmono
      exact hmono.trans (by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3])
    have hp0 : 0 ≤ (3 : ℝ) ^ (-((s / 2) * ((m : ℝ) + 1))) := by positivity
    exact hpow.trans (mul_le_mul_of_nonneg_right hsPow hp0)
  have hcore := three_rpow_neg_mul_drift_sq_le
    (s := s / 2) (t := (m : ℝ) + 1)
    (tau := _root_.SubdiffusiveProcess.Model.tauSq M.P) (by positivity) (by positivity)
  have htau : _root_.SubdiffusiveProcess.Model.tauSq M.P ^ 2 ≤ M.delta ^ 4 := by
    have hlog : Real.log 2 / 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hle := (tauSq_le_delta_sq M).trans
      (mul_le_of_le_one_left (sq_nonneg M.delta) hlog)
    calc
      _root_.SubdiffusiveProcess.Model.tauSq M.P ^ 2 ≤ (M.delta ^ 2) ^ 2 :=
        pow_le_pow_left₀ M.G4.tauSq_pos.le hle 2
      _ = M.delta ^ 4 := by ring
  calc
    _ ≤ (3 : ℝ) ^ (-(7 * s / 8) * (m : ℝ)) *
        (_root_.SubdiffusiveProcess.Model.tauSq M.P * ((m : ℝ) + 1)) ^ 2 :=
      mul_le_mul_of_nonneg_left hrho (Real.rpow_nonneg (by norm_num) _)
    _ ≤ 2 * (3 : ℝ) ^ (-((s / 2) * ((m : ℝ) + 1))) *
        (_root_.SubdiffusiveProcess.Model.tauSq M.P * ((m : ℝ) + 1)) ^ 2 := by
      exact mul_le_mul_of_nonneg_right hdecay (sq_nonneg _)
    _ ≤ 2 * (2 * ((s / 2)⁻¹) ^ 2 *
        _root_.SubdiffusiveProcess.Model.tauSq M.P ^ 2) := by
      nlinarith [hcore]
    _ ≤ 2 * (2 * ((s / 2)⁻¹) ^ 2 * M.delta ^ 4) := by
      gcongr
    _ = 16 * (s⁻¹ * M.delta ^ 2) ^ 2 := by
      field_simp [hs.ne']
      ring

/-- Threshold-12 square budget for all negative annular scales above a
cutoff-saturated parent. -/
def aux_obl_ramp_threshold12_fourth_t12sat_subunitBudget
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (s : ℝ) (m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  6 * 576 ^ 2 * (goodScaleFullSlot s m omega ^ 2 +
    goodScaleShellSlot s m omega ^ 2 +
    16 * (s⁻¹ * M.delta ^ 2) ^ 2)

theorem aux_obl_ramp_threshold12_fourth_t12sat_subunitBudget_nonneg
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (s : ℝ) (m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ aux_obl_ramp_threshold12_fourth_t12sat_subunitBudget M s m omega := by
  unfold aux_obl_ramp_threshold12_fourth_t12sat_subunitBudget
  positivity

/-- Every nonpositive annular atom is controlled by the threshold-12 cutoff
subunit budget; all coefficient ratios end at `L`. -/
theorem aux_obl_ramp_threshold12_fourth_t12sat_subunit_atom_le_budget [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ} (hLm : L ≤ m)
    {epsilon s : ℝ} (hepsilon : 0 ≤ epsilon)
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hfield : GoodFieldOne m 0 epsilon s omega)
    (hprod : aux_obl_ramp_threshold12_fourth_t12sat_ProductTwelve m s omega)
    {R : SubdiffusiveProcess.CoarseGrainingVocab.TriadicCube d} {j : ℤ} (hj : j ≤ (m : ℤ))
    (hscale : R.scale ≤ j - 2)
    (hann : triadicCubeShift R ∈ cube d j \ cube d (j - 1))
    (hneg : R.scale ≤ 0) :
    ENNReal.ofReal ((3 : ℝ) ^ (-(3 * s / 2) *
          ((m : ℝ) - (R.scale : ℝ)))) *
        section6LocalProbeMax M L omega 0
          (tailCoefficientCubeAverage M L m omega) R ≤
      ENNReal.ofReal (aux_obl_ramp_threshold12_fourth_t12sat_subunitBudget M s m omega) := by
  have hs0 : 0 ≤ s :=
    (mul_nonneg (by norm_num) (sq_nonneg M.delta)).trans hsLower
  set F : ℝ := 576 * (3 : ℝ) ^ ((s * (m : ℝ)) / 4) *
    (3 : ℝ) ^ ((s * ((m : ℝ) + 1)) / 16) with hF
  set Gf : ℝ := supNormOn (cube d m) (fullShellBlock m omega) with hGf
  set Gs : ℝ := supNormOn (cube d m) (shellBlock m L omega) with hGs
  set rho : ℝ := _root_.SubdiffusiveProcess.Model.tauSq M.P * ((L : ℝ) + 1) with hrho
  set B : ℝ := min 1 (Gf + Gs + rho) with hB
  set K : ℝ := (F * B) ^ 2 with hK
  set omega' : _root_.SubdiffusiveProcess.Model.PotentialSample d :=
    translatePotentialSample (triadicCubeShift R) omega with homega'
  have hRdesc : R ∈ descendantsAtScale (originCube d (m : ℤ)) R.scale :=
    annularCube_mem_descendantsAtScale hj hscale hann
  have hpoint : ∀ x ∈ ((Ch02.cubeDomain (originCube d R.scale) :
      Ch02.Domain d) : Set (Vec d)),
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega' x / ahom M L - 1) ^ 2 +
        (ahom M L / _root_.SubdiffusiveProcess.Model.aCutoff M L omega' x - 1) ^ 2 ≤ K := by
    intro x hx
    have hxcube : x ∈ cube d R.scale := by
      exact hx
    have hxR : triadicCubeShift R + x ∈ openCubeSet R := by
      rw [openCubeSet_eq_translateSet_originCube_of_triadicCube,
        mem_translateSet_iff_sub_mem]
      simp only [add_sub_cancel_left]
      exact hxcube
    have hxM : triadicCubeShift R + x ∈ cube d (m : ℤ) :=
      openCubeSet_subset_of_mem_descendantsAtScale
        (scale_le_of_mem_descendantsAtScale hRdesc) hRdesc hxR
    have hxM' : x + triadicCubeShift R ∈ cube d (m : ℤ) := by
      rwa [add_comm] at hxM
    rw [homega', Section6Covariance.aCutoff_translatePotentialSample]
    simpa only [K, F, B, Gf, Gs, rho] using
      aux_obl_ramp_threshold12_fourth_t12sat_cutoffSubunit_ratioEnergy_le M hLm hepsilon
        hsLower hsUpper omega hfield hprod hxM'
  have haverage : Ch02.average (Ch02.cubeDomain (originCube d R.scale))
      (fun x ↦
        (_root_.SubdiffusiveProcess.Model.aCutoff M L omega' x / ahom M L - 1) ^ 2 +
        (ahom M L / _root_.SubdiffusiveProcess.Model.aCutoff M L omega' x - 1) ^ 2) ≤ K := by
    set U : Ch02.Domain d := Ch02.cubeDomain (originCube d R.scale) with hU
    have haPos := _root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega'
    have hcontinuous : Continuous (fun x ↦
        (_root_.SubdiffusiveProcess.Model.aCutoff M L omega' x / ahom M L - 1) ^ 2 +
        (ahom M L / _root_.SubdiffusiveProcess.Model.aCutoff M L omega' x - 1) ^ 2) :=
      ((((_root_.SubdiffusiveProcess.Model.continuous_aCutoff M L omega').div_const _).sub
        continuous_const).pow 2).add
        (((continuous_const.div
          (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M L omega')
          (fun x ↦ (haPos x).ne')).sub continuous_const).pow 2)
    exact average_le_of_le_on U
      ((hcontinuous.continuousOn.integrableOn_compact
        U.isDomain.isBoundedDomain.isBounded.isCompact_closure).mono_set
          subset_closure) hpoint
  have hprobeRaw := section6LocalProbeMax_le_ratioEnergy_average M L m omega R
  have hb := tailCoefficientCubeAverage_eq_ahom_of_cutoff_le_scale M hLm omega
  rw [hb] at hprobeRaw
  have hprobe : section6LocalProbeMax M L omega 0
      (tailCoefficientCubeAverage M L m omega) R ≤ ENNReal.ofReal K := by
    rw [hb]
    exact hprobeRaw.trans (ENNReal.ofReal_le_ofReal haverage)
  have hweight : (3 : ℝ) ^ (-(3 * s / 2) *
      ((m : ℝ) - (R.scale : ℝ))) ≤
      (3 : ℝ) ^ (-(3 * s / 2) * (m : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hk : ((R.scale : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hneg
    have := mul_nonneg hs0 (neg_nonneg.mpr hk)
    nlinarith
  have hw0 : 0 ≤ (3 : ℝ) ^ (-(3 * s / 2) *
      ((m : ℝ) - (R.scale : ℝ))) := Real.rpow_nonneg (by norm_num) _
  have henv := aux_obl_ramp_threshold12_fourth_t12sat_subunit_envelope_weight hsUpper m
  have hsplit := min_one_add_three_sq_le_three_sum_sq Gf Gs rho
  have hdecayFull := aux_obl_ramp_threshold12_fourth_t12sat_subunit_decay_le_fullSlot_sq hs0 m omega
  have hdecayShell := aux_obl_ramp_threshold12_fourth_t12sat_subunit_decay_le_shellSlot_sq hLm hs0 omega
  have hdecayDrift := aux_obl_ramp_threshold12_fourth_t12sat_subunit_decay_drift_le M hLm hsLower hsUpper
  have hfinal : (3 : ℝ) ^ (-(3 * s / 2) *
      ((m : ℝ) - (R.scale : ℝ))) * K ≤
      aux_obl_ramp_threshold12_fourth_t12sat_subunitBudget M s m omega := by
    have hB2 : B ^ 2 ≤ 3 * (Gf ^ 2 + Gs ^ 2 + rho ^ 2) := by
      simpa only [B] using hsplit
    have hstep1 : (3 : ℝ) ^ (-(3 * s / 2) *
        ((m : ℝ) - (R.scale : ℝ))) * K ≤
        (2 * 576 ^ 2 * (3 : ℝ) ^ (-(7 * s / 8) * (m : ℝ))) * B ^ 2 := by
      have hFB0 : 0 ≤ B ^ 2 := sq_nonneg _
      have hweightF : (3 : ℝ) ^ (-(3 * s / 2) *
          ((m : ℝ) - (R.scale : ℝ))) * F ^ 2 ≤
          (3 : ℝ) ^ (-(3 * s / 2) * (m : ℝ)) * F ^ 2 :=
        mul_le_mul_of_nonneg_right hweight (sq_nonneg F)
      calc
        (3 : ℝ) ^ (-(3 * s / 2) *
            ((m : ℝ) - (R.scale : ℝ))) * K =
            ((3 : ℝ) ^ (-(3 * s / 2) *
              ((m : ℝ) - (R.scale : ℝ))) * F ^ 2) * B ^ 2 := by
          rw [hK]
          ring
        _ ≤ ((3 : ℝ) ^ (-(3 * s / 2) * (m : ℝ)) * F ^ 2) * B ^ 2 :=
          mul_le_mul_of_nonneg_right hweightF hFB0
        _ = ((3 : ℝ) ^ (-(3 * s / 2) * (m : ℝ)) *
            (576 * (3 : ℝ) ^ (s * (m : ℝ) / 4) *
              (3 : ℝ) ^ (s * ((m : ℝ) + 1) / 16)) ^ 2) * B ^ 2 := by
          rw [hF]
        _ ≤ (2 * 576 ^ 2 *
            (3 : ℝ) ^ (-(7 * s / 8) * (m : ℝ))) * B ^ 2 :=
          mul_le_mul_of_nonneg_right henv hFB0
    refine hstep1.trans ?_
    have hscaleB := mul_le_mul_of_nonneg_left hB2 (show
      0 ≤ 2 * 576 ^ 2 * (3 : ℝ) ^ (-(7 * s / 8) * (m : ℝ)) by
        positivity)
    have hcomponents : (3 : ℝ) ^ (-(7 * s / 8) * (m : ℝ)) *
        (Gf ^ 2 + Gs ^ 2 + rho ^ 2) ≤
        goodScaleFullSlot s m omega ^ 2 + goodScaleShellSlot s m omega ^ 2 +
          16 * (s⁻¹ * M.delta ^ 2) ^ 2 := by
      rw [mul_add, mul_add]
      simpa only [Gf, Gs, rho] using
        add_le_add (add_le_add hdecayFull hdecayShell) hdecayDrift
    unfold aux_obl_ramp_threshold12_fourth_t12sat_subunitBudget
    calc
      _ ≤ (2 * 576 ^ 2 * (3 : ℝ) ^ (-(7 * s / 8) * (m : ℝ))) *
          (3 * (Gf ^ 2 + Gs ^ 2 + rho ^ 2)) := hscaleB
      _ = 6 * 576 ^ 2 * ((3 : ℝ) ^ (-(7 * s / 8) * (m : ℝ)) *
          (Gf ^ 2 + Gs ^ 2 + rho ^ 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcomponents (by positivity)
  calc
    ENNReal.ofReal ((3 : ℝ) ^ (-(3 * s / 2) *
          ((m : ℝ) - (R.scale : ℝ)))) *
        section6LocalProbeMax M L omega 0
          (tailCoefficientCubeAverage M L m omega) R ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-(3 * s / 2) *
          ((m : ℝ) - (R.scale : ℝ)))) * ENNReal.ofReal K := by
        gcongr
    _ = ENNReal.ofReal ((3 : ℝ) ^ (-(3 * s / 2) *
          ((m : ℝ) - (R.scale : ℝ))) * K) :=
      (ENNReal.ofReal_mul hw0).symm
    _ ≤ ENNReal.ofReal (aux_obl_ramp_threshold12_fourth_t12sat_subunitBudget M s m omega) :=
      ENNReal.ofReal_le_ofReal hfinal

/-- Complete refined annular supremum on the threshold-12 event above `L`. -/
theorem aux_obl_ramp_threshold12_fourth_t12sat_annularSupTwo_le_budget [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ} (hLm : L ≤ m)
    {epsilon s : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hfield : GoodFieldOne m 0 epsilon s omega)
    (hprod : aux_obl_ramp_threshold12_fourth_t12sat_ProductTwelve m s omega)
    (hresp : GoodResponse M (some L) m 0 epsilon s omega) :
    annularSupTwo s (m : ℤ)
        (section6LocalProbeMax M L omega 0
          (tailCoefficientCubeAverage M L m omega)) ≤
      ENNReal.ofReal (aux_obl_ramp_threshold12_fourth_t12sat_positiveBudget M L s m omega +
        aux_obl_ramp_threshold12_fourth_t12sat_subunitBudget M s m omega) := by
  refine iSup_le fun p ↦ ?_
  rcases le_or_gt 0 p.1.1.scale with hscale0 | hscaleneg
  · refine (aux_obl_ramp_threshold12_fourth_t12sat_positive_annular_atom_le_budget M hLm hepsilon0 hepsilon1
      hsLower hsUpper omega hfield hprod hresp p hscale0).trans
        (ENNReal.ofReal_le_ofReal ?_)
    have hsub := aux_obl_ramp_threshold12_fourth_t12sat_subunitBudget_nonneg M s m omega
    linarith
  · obtain ⟨hj, hsc, hann⟩ := p.2
    refine (aux_obl_ramp_threshold12_fourth_t12sat_subunit_atom_le_budget M hLm hepsilon0
      hsLower hsUpper omega hfield hprod hj hsc hann hscaleneg.le).trans
        (ENNReal.ofReal_le_ofReal ?_)
    have hpos := aux_obl_ramp_threshold12_fourth_t12sat_positiveBudget_nonneg M L s m omega
    linarith


/-! ## The base display for the `ℝ≥0∞` paper error -/

/-- The square of the threshold-12 cutoff base constant. -/
def aux_obl_ramp_threshold12_fourth_t12sat_squareConstant : ℝ := 192 * (2 + 165888 + 31850496)

theorem aux_obl_ramp_threshold12_fourth_t12sat_squareConstant_pos : 0 < aux_obl_ramp_threshold12_fourth_t12sat_squareConstant := by
  unfold aux_obl_ramp_threshold12_fourth_t12sat_squareConstant
  norm_num

private theorem aux_obl_ramp_threshold12_fourth_t12sat_budget_le_square (A D Bs Bf Bg : ℝ) :
    192 * ((2 * A ^ 2 + 36 * (48 : ℝ) ^ 2 * (2 * Bs ^ 2 + 2 * D ^ 2)) +
        6 * 576 ^ 2 * (Bf ^ 2 + Bs ^ 2 + 16 * D ^ 2)) ≤
      aux_obl_ramp_threshold12_fourth_t12sat_squareConstant * (A ^ 2 + D ^ 2 + Bs ^ 2 + Bf ^ 2 + Bg ^ 2) := by
  have hexp : aux_obl_ramp_threshold12_fourth_t12sat_squareConstant * (A ^ 2 + D ^ 2 + Bs ^ 2 + Bf ^ 2 + Bg ^ 2) -
      192 * ((2 * A ^ 2 + 36 * (48 : ℝ) ^ 2 * (2 * Bs ^ 2 + 2 * D ^ 2)) +
        6 * 576 ^ 2 * (Bf ^ 2 + Bs ^ 2 + 16 * D ^ 2)) =
      192 * (32016384 * A ^ 2 + 2 * D ^ 2 + 29859842 * Bs ^ 2 +
        30025730 * Bf ^ 2 + 32016386 * Bg ^ 2) := by
    unfold aux_obl_ramp_threshold12_fourth_t12sat_squareConstant
    ring
  have h0 : 0 ≤ 192 * (32016384 * A ^ 2 + 2 * D ^ 2 + 29859842 * Bs ^ 2 +
      30025730 * Bf ^ 2 + 32016386 * Bg ^ 2) := by positivity
  linarith

/-- Nonnegativity of the five cutoff display slots. -/
private theorem aux_obl_ramp_threshold12_fourth_t12sat_slots_nonneg
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) {m : ℕ} {s : ℝ} (hs0 : 0 < s)
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ cutoffGoodScaleResponseSlot M L s m eta ∧ 0 ≤ s⁻¹ * M.delta ^ 2 ∧
      0 ≤ goodScaleShellSlot s m eta ∧ 0 ≤ goodScaleFullSlot s m eta ∧
      0 ≤ goodScaleGradientSlot m eta := by
  refine ⟨?_, mul_nonneg (inv_nonneg.2 hs0.le) (sq_nonneg _), ?_, ?_, ?_⟩
  · refine Real.sSup_nonneg ?_
    rintro a ⟨j, n, -, -, z, -, -, rfl⟩
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)
  · refine Real.sSup_nonneg ?_
    rintro a ⟨j, -, rfl⟩
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (aux_obl_ramp_threshold12_fourth_t12sat_supNormOn_nonneg _ _)
  · exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (aux_obl_ramp_threshold12_fourth_t12sat_supNormOn_nonneg _ _)
  · rw [goodScaleGradientSlot_eq_longRatioGradientTail]
    exact longRatioGradientTail_nonneg m eta

private theorem aux_obl_ramp_threshold12_fourth_t12sat_sqrt_budget_le
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) {m : ℕ} {s : ℝ} (hs0 : 0 < s)
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    (192 * (aux_obl_ramp_threshold12_fourth_t12sat_positiveBudget M L s m eta +
        aux_obl_ramp_threshold12_fourth_t12sat_subunitBudget M s m eta)) ^ (1 / 2 : ℝ) ≤
      Real.sqrt aux_obl_ramp_threshold12_fourth_t12sat_squareConstant *
        (cutoffGoodScaleResponseSlot M L s m eta + s⁻¹ * M.delta ^ 2 +
          goodScaleShellSlot s m eta + goodScaleFullSlot s m eta +
          goodScaleGradientSlot m eta) := by
  obtain ⟨hA0, hD0, hBs0, hBf0, hBg0⟩ := aux_obl_ramp_threshold12_fourth_t12sat_slots_nonneg M L (m := m) hs0 eta
  set A : ℝ := cutoffGoodScaleResponseSlot M L s m eta with hAdef
  set D : ℝ := s⁻¹ * M.delta ^ 2 with hDdef
  set Bs : ℝ := goodScaleShellSlot s m eta with hBsdef
  set Bf : ℝ := goodScaleFullSlot s m eta with hBfdef
  set Bg : ℝ := goodScaleGradientSlot m eta with hBgdef
  set Sigma : ℝ := A + D + Bs + Bf + Bg with hSigmadef
  have hSigma0 : 0 ≤ Sigma := by rw [hSigmadef]; linarith
  rw [← Real.sqrt_eq_rpow]
  have hsq : A ^ 2 + D ^ 2 + Bs ^ 2 + Bf ^ 2 + Bg ^ 2 ≤ Sigma ^ 2 := by
    rw [hSigmadef]
    nlinarith [mul_nonneg hA0 hD0, mul_nonneg hA0 hBs0, mul_nonneg hA0 hBf0,
      mul_nonneg hA0 hBg0, mul_nonneg hD0 hBs0, mul_nonneg hD0 hBf0,
      mul_nonneg hD0 hBg0, mul_nonneg hBs0 hBf0, mul_nonneg hBs0 hBg0,
      mul_nonneg hBf0 hBg0]
  have hcoef : 192 * (aux_obl_ramp_threshold12_fourth_t12sat_positiveBudget M L s m eta +
      aux_obl_ramp_threshold12_fourth_t12sat_subunitBudget M s m eta) ≤ aux_obl_ramp_threshold12_fourth_t12sat_squareConstant *
      (A ^ 2 + D ^ 2 + Bs ^ 2 + Bf ^ 2 + Bg ^ 2) := by
    rw [aux_obl_ramp_threshold12_fourth_t12sat_positiveBudget, aux_obl_ramp_threshold12_fourth_t12sat_subunitBudget,
      ← hAdef, ← hDdef, ← hBsdef, ← hBfdef]
    exact aux_obl_ramp_threshold12_fourth_t12sat_budget_le_square A D Bs Bf Bg
  have hT0 : 0 ≤ aux_obl_ramp_threshold12_fourth_t12sat_squareConstant := aux_obl_ramp_threshold12_fourth_t12sat_squareConstant_pos.le
  calc
    Real.sqrt (192 * (aux_obl_ramp_threshold12_fourth_t12sat_positiveBudget M L s m eta +
        aux_obl_ramp_threshold12_fourth_t12sat_subunitBudget M s m eta)) ≤
        Real.sqrt (aux_obl_ramp_threshold12_fourth_t12sat_squareConstant * Sigma ^ 2) :=
      Real.sqrt_le_sqrt (hcoef.trans (mul_le_mul_of_nonneg_left hsq hT0))
    _ = Real.sqrt aux_obl_ramp_threshold12_fourth_t12sat_squareConstant * Sigma := by
      rw [Real.sqrt_mul hT0, Real.sqrt_sq hSigma0]

/-- The threshold-12 base display above the cutoff for the `ℝ≥0∞`-valued
paper error itself (no `toReal`): the weighted descendant series is bounded
through the annular supremum, so the paper error is finite on the event. -/
theorem aux_obl_ramp_threshold12_fourth_t12sat_paperError_le_base [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ} (hLm : L ≤ m)
    {epsilon s : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hfield : GoodFieldOne m 0 epsilon s eta)
    (hprod : aux_obl_ramp_threshold12_fourth_t12sat_ProductTwelve m s eta)
    (hresp : GoodResponse M (some L) m 0 epsilon s eta) :
    paperHomogenizationError (originCube d (m : ℤ)) (m : ℤ) s .infinity (.finite 2)
        (aCutoffFamily M L eta) (tailCoefficientCubeAverage M L m eta) ≤
      ENNReal.ofReal (Real.sqrt aux_obl_ramp_threshold12_fourth_t12sat_squareConstant *
        (cutoffGoodScaleResponseSlot M L s m eta + s⁻¹ * M.delta ^ 2 +
          goodScaleShellSlot s m eta + goodScaleFullSlot s m eta +
          goodScaleGradientSlot m eta)) := by
  have hdim : 2 ≤ d := M.shellPrefix.dimension
  have hd1 : 1 ≤ d := by omega
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hsLower
  set alpha : ℝ := tailCoefficientCubeAverage M L m eta with halpha
  set g : SubdiffusiveProcess.CoarseGrainingVocab.TriadicCube d → ℝ≥0∞ :=
    section6LocalProbeMax M L eta 0 alpha with hg
  set B : ℝ := aux_obl_ramp_threshold12_fourth_t12sat_positiveBudget M L s m eta +
    aux_obl_ramp_threshold12_fourth_t12sat_subunitBudget M s m eta with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    have h1 := aux_obl_ramp_threshold12_fourth_t12sat_positiveBudget_nonneg M L s m eta
    have h2 := aux_obl_ramp_threshold12_fourth_t12sat_subunitBudget_nonneg M s m eta
    linarith
  have hseries := tsum_geometricWeight_descendantSup_le_annularSup hs0 hsUpper hd1 m g
    (fun n _ => section6LocalProbeMax_originCube_le_onion M L eta 0 alpha n)
  have hthree := annularSup_le_three_mul_annularSupTwo (m := (m : ℤ)) hsUpper g
    (section6LocalProbeMax_le_child M L eta 0 alpha)
  have hstep2 : annularSupTwo s (m : ℤ) g ≤ ENNReal.ofReal B :=
    aux_obl_ramp_threshold12_fourth_t12sat_annularSupTwo_le_budget M hLm hepsilon0 hepsilon1 hsLower hsUpper eta
      hfield hprod hresp
  have htotal : ∑' l : ℕ, ENNReal.ofReal (Ch02.geometricWeight s 2 l) *
      (⨆ R : {R : SubdiffusiveProcess.CoarseGrainingVocab.TriadicCube d //
          R ∈ descendantsAtScale (originCube d (m : ℤ)) ((m : ℤ) - (l : ℤ))},
        g R.1) ≤ ENNReal.ofReal (192 * B) := by
    calc
      _ ≤ 64 * annularSup s (m : ℤ) g := hseries
      _ ≤ 64 * (3 * annularSupTwo s (m : ℤ) g) := by gcongr
      _ ≤ 64 * (3 * ENNReal.ofReal B) := by gcongr
      _ = 192 * ENNReal.ofReal B := by ring
      _ = ENNReal.ofReal (192 * B) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 192), ENNReal.ofReal_ofNat]
  have hrw : (∑' l : ℕ, ENNReal.ofReal (Ch02.geometricWeight s 2 l) *
      paperMaxDescendantProbeAtScale (originCube d (m : ℤ)) ((m : ℤ) - (l : ℤ))
        (aCutoffFamily M L eta) alpha) =
      ∑' l : ℕ, ENNReal.ofReal (Ch02.geometricWeight s 2 l) *
      (⨆ R : {R : SubdiffusiveProcess.CoarseGrainingVocab.TriadicCube d //
          R ∈ descendantsAtScale (originCube d (m : ℤ)) ((m : ℤ) - (l : ℤ))},
        g R.1) := by
    refine tsum_congr fun l => ?_
    rw [paperMaxDescendantProbeAtScale_aCutoffFamily_eq_transported]
    congr 1
    refine iSup_congr fun R => ?_
    rw [hg, section6LocalProbeMax, Section6Covariance.translatePotentialSample_zero,
      scale_eq_of_mem_descendantsAtScale R.2]
  rw [paperHomogenizationError_infinity_two_eq_weighted_series, hrw]
  calc
    _ ≤ (ENNReal.ofReal (192 * B)) ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow htotal (by norm_num)
    _ = ENNReal.ofReal ((192 * B) ^ (1 / 2 : ℝ)) :=
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)
    _ ≤ _ := ENNReal.ofReal_le_ofReal (aux_obl_ramp_threshold12_fourth_t12sat_sqrt_budget_le M L hs0 eta)

/-! ## Response truncation on the cutoff carrier (upstream
`cutoffGoodScaleResponseSlot_le_accumulatedError_add_pow_eight`, reading only
the cutoff response clause) -/

private theorem aux_obl_ramp_threshold12_fourth_t12sat_cutoffTruncatedResponseSet_bddAbove
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    {m : ℕ} {s : ℝ} (hs : 0 ≤ s) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    BddAbove {r : ℝ | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧
      ∃ z : Vec d, OnTriadicGrid n (z - 0) ∧
        z - 0 ∈ cube d j \ cube d (j - 1) ∧
        r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
          Real.sqrt (min (sSup {q : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
            q = section6Response M n (min n ((some L).getD n)) omega z e}) 1)} := by
  refine ⟨1, ?_⟩
  rintro r ⟨j, n, hjm, hnj, z, hzgrid, hzann, rfl⟩
  have hnm : n ≤ m := by omega
  have hgap : 0 ≤ (m : ℝ) - (n : ℝ) := by
    exact sub_nonneg.mpr (Nat.cast_le.2 hnm)
  have hw : (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hgap
  have hsqrt : Real.sqrt (min
      (sSup {q : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
        q = section6Response M n (min n ((some L).getD n)) omega z e}) 1) ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (min_le_right _ 1)
  exact (mul_le_mul hw hsqrt (Real.sqrt_nonneg _) (by positivity)).trans_eq
    (mul_one 1)

/-- The cutoff response slot is bounded by the truncated response part of the
literal cutoff `accumulatedError M (some L)`, plus `epsilon^8`. -/
theorem aux_obl_ramp_threshold12_fourth_t12sat_cutoffResponseSlot_le_accumulatedError
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    {m : ℕ} {epsilon s : ℝ} (hepsilon : 0 ≤ epsilon) (hs : 0 ≤ s)
    {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d}
    (hresp : GoodResponse M (some L) m 0 epsilon s omega) :
    cutoffGoodScaleResponseSlot M L s m omega ≤
      accumulatedError M (some L) m 0 s omega + epsilon ^ 8 := by
  unfold cutoffGoodScaleResponseSlot
  let S : Set ℝ := {r : ℝ | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧
    ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d j \ cube d (j - 1) ∧
    r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
      Real.sqrt (sSup {q : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
        q = section6Response M n (min n L) omega z e})}
  change sSup S ≤ _
  by_cases hS : S.Nonempty
  · apply csSup_le hS
    rintro _ ⟨j, n, hjm, hnj, z, hzgrid, hzann, rfl⟩
    let A : Set ℝ := {q : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
      q = section6Response M n (min n L) omega z e}
    have hAne : A.Nonempty := by
      have hd : 2 ≤ d := M.shellPrefix.dimension
      let i : Fin d := ⟨0, by omega⟩
      let e : Vec d := Pi.single i 1
      refine ⟨section6Response M n (min n L) omega z e, e, ?_, rfl⟩
      rw [vecNormSq, vecDot, Finset.sum_eq_single i]
      · simp [e]
      · intro b _ hbi
        simp [e, Pi.single_eq_of_ne hbi]
      · simp
    have hrespA : sSup A ≤ epsilon ^ 2 *
        (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 8) := by
      refine csSup_le hAne ?_
      rintro _ ⟨e, he, rfl⟩
      simpa only [A, sub_zero, Option.getD_some] using
        hresp j n hjm hnj z
          (by simpa only [sub_zero] using hzgrid)
          (by simpa only [sub_zero] using hzann) e he
    have hsqrt : Real.sqrt (sSup A) ≤ epsilon *
        (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 16) := by
      have hright : 0 ≤ epsilon *
          (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 16) := by positivity
      rw [Real.sqrt_le_iff]
      refine ⟨hright, hrespA.trans_eq ?_⟩
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      ring
    let t : ℝ := (3 : ℝ) ^ (-(s * ((m : ℝ) - (n : ℝ))) / 16)
    have ht0 : 0 < t := Real.rpow_pos_of_pos (by norm_num) _
    have htinv : t⁻¹ =
        (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 16) := by
      dsimp only [t]
      rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      ring
    have htrunc := Section6Holder.pow_eight_mul_le_truncated_add_pow_eight ht0 hepsilon
      (Real.sqrt_nonneg _) (by rwa [htinv])
    have hsqrtMin : min (Real.sqrt (sSup A)) 1 =
        Real.sqrt (min (sSup A) 1) := by
      have hmono : Monotone Real.sqrt := fun _ _ h ↦ Real.sqrt_le_sqrt h
      symm
      calc
        Real.sqrt (min (sSup A) 1) =
            min (Real.sqrt (sSup A)) (Real.sqrt 1) := hmono.map_min
        _ = min (Real.sqrt (sSup A)) 1 := by rw [Real.sqrt_one]
    have hweight : t ^ 8 =
        (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) := by
      dsimp only [t]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      ring
    rw [hweight, hsqrtMin] at htrunc
    have htruncated :
        (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
            Real.sqrt (min (sSup A) 1) ≤
          accumulatedError M (some L) m 0 s omega := by
      apply Section6Holder.truncatedResponseAtom_le_accumulatedError M (some L) s m 0 omega
        (aux_obl_ramp_threshold12_fourth_t12sat_cutoffTruncatedResponseSet_bddAbove M L hs omega) hjm hnj
      · simpa only [sub_zero] using hzgrid
      · simpa only [sub_zero] using hzann
    have hadd := add_le_add htruncated (le_refl (epsilon ^ 8))
    simpa only [A, Option.getD_some] using htrunc.trans hadd
  · have hEmpty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    rw [hEmpty, Real.sSup_empty]
    have hE := Section6Holder.accumulatedError_nonneg M (some L) s m 0 omega
    positivity

/-! ## The epsilon cap on the field slots (only `GoodFieldOne` is read) -/

private theorem aux_obl_ramp_threshold12_fourth_t12sat_bddAbove_abs_values_cube_int {k : ℤ} {f : Vec d → ℝ}
    (hf : Continuous f) :
    BddAbove {a : ℝ | ∃ x ∈ cube d k, a = |f x|} := by
  let Q := originCube d k
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (cubeCenter Q) (cubeRadius Q)).exists_bound_of_continuousOn
      ((continuous_abs.comp hf).continuousOn)
  refine ⟨max 0 C, ?_⟩
  rintro a ⟨x, hx, rfl⟩
  have hx' : x ∈ Metric.closedBall (cubeCenter Q) (cubeRadius Q) :=
    cubeSet_subset_closedBall Q (openCubeSet_subset_cubeSet Q hx)
  have h := hC x hx'
  simpa only [Function.comp_apply, Real.norm_eq_abs, abs_abs] using
    h.trans (le_max_right _ _)

private theorem aux_obl_ramp_threshold12_fourth_t12sat_abs_apply_le_supNormOn_cube_int {k : ℤ} {f : Vec d → ℝ}
    (hf : Continuous f) {x : Vec d} (hx : x ∈ cube d k) :
    |f x| ≤ supNormOn (cube d k) f :=
  le_csSup (aux_obl_ramp_threshold12_fourth_t12sat_bddAbove_abs_values_cube_int hf) ⟨x, hx, rfl⟩

private theorem aux_obl_ramp_threshold12_fourth_t12sat_translatedCube_zero (k : ℤ) :
    translatedCube d k 0 = cube d k := by
  unfold translatedCube
  simp

private theorem aux_obl_ramp_threshold12_fourth_t12sat_shellGradient_continuous
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) :
    Continuous (shellGradient g) := by
  unfold shellGradient
  apply continuous_pi
  intro i
  exact (_root_.SubdiffusiveProcess.Model.PotentialField.deriv g).continuous.clm_apply
    continuous_const

private theorem aux_obl_ramp_threshold12_fourth_t12sat_shellControl_continuous
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) (i : ℕ) :
    Continuous (fun x => |g x| + (3 : ℝ) ^ i *
      euclideanNorm (shellGradient g x)) := by
  have hnorm : Continuous (fun x => euclideanNorm (shellGradient g x)) := by
    rw [show (fun x => euclideanNorm (shellGradient g x)) =
        fun x => ‖HilbertVec.ofVec (shellGradient g x)‖ by
      funext x
      rw [euclideanNorm_eq_norm_ofVec]]
    exact continuous_norm.comp
      ((HilbertVec.ofVecL d).continuous.comp (aux_obl_ramp_threshold12_fourth_t12sat_shellGradient_continuous g))
  exact (continuous_abs.comp g.1.1.continuous).add (continuous_const.mul hnorm)

private theorem aux_obl_ramp_threshold12_fourth_t12sat_sum_abs_le_of_goodFieldOne (m q : ℕ) {epsilon s : ℝ}
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hgood : GoodFieldOne m 0 epsilon s omega)
    {T : Finset ℕ} (hT : T ⊆ Finset.Icc (m - q) (m + q))
    {x : Vec d} (hx : x ∈ cube d (m : ℤ)) :
    ∑ i ∈ T, |omega i x| ≤ epsilon * (3 : ℝ) ^ ((s * (q : ℝ)) / 8) := by
  have hevent := hgood q
  rw [aux_obl_ramp_threshold12_fourth_t12sat_translatedCube_zero] at hevent
  have hxlarge : x ∈ cube d ((m : ℤ) + 1 + (q : ℤ)) := by
    refine openCubeSet_originCube_subset_of_scale_le ?_ hx
    omega
  have hterm : ∀ i ∈ Finset.Icc (m - q) (m + q), |omega i x| ≤
      supNormOn (cube d ((m : ℤ) + 1 + (q : ℤ))) (fun y =>
        |omega i y| + (3 : ℝ) ^ i * euclideanNorm (shellGradient (omega i) y)) := by
    intro i _
    have hcontrol := aux_obl_ramp_threshold12_fourth_t12sat_abs_apply_le_supNormOn_cube_int
      (aux_obl_ramp_threshold12_fourth_t12sat_shellControl_continuous (omega i) i) hxlarge
    have hnonneg : 0 ≤ |omega i x| + (3 : ℝ) ^ i *
        euclideanNorm (shellGradient (omega i) x) :=
      add_nonneg (abs_nonneg _)
        (mul_nonneg (by positivity) (euclideanNorm_nonneg _))
    rw [abs_of_nonneg hnonneg] at hcontrol
    refine le_trans ?_ hcontrol
    have : 0 ≤ (3 : ℝ) ^ i * euclideanNorm (shellGradient (omega i) x) :=
      mul_nonneg (by positivity) (euclideanNorm_nonneg _)
    linarith
  calc
    ∑ i ∈ T, |omega i x| ≤ ∑ i ∈ Finset.Icc (m - q) (m + q), |omega i x| :=
      Finset.sum_le_sum_of_subset_of_nonneg hT (fun i _ _ => abs_nonneg _)
    _ ≤ ∑ i ∈ Finset.Icc (m - q) (m + q),
        supNormOn (cube d ((m : ℤ) + 1 + (q : ℤ))) (fun y =>
          |omega i y| + (3 : ℝ) ^ i *
            euclideanNorm (shellGradient (omega i) y)) :=
      Finset.sum_le_sum hterm
    _ ≤ epsilon * (3 : ℝ) ^ ((s * (q : ℝ)) / 8) := hevent

private theorem aux_obl_ramp_threshold12_fourth_t12sat_supNormOn_shellBlock_le_of_goodFieldOne
    (m j : ℕ) (hj : j ≤ m) {epsilon s : ℝ}
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hgood : GoodFieldOne m 0 epsilon s omega) :
    supNormOn (cube d (m : ℤ)) (shellBlock m j omega) ≤
      epsilon * (3 : ℝ) ^ ((s * ((m - j : ℕ) : ℝ)) / 8) := by
  refine csSup_le ?_ ?_
  · exact ⟨|shellBlock m j omega 0|, 0, aux_obl_ramp_threshold12_fourth_t12sat_zero_mem_cube (m : ℤ), rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hsubset : Finset.Icc (j + 1) m ⊆
        Finset.Icc (m - (m - j)) (m + (m - j)) := by
      intro i hi
      simp only [Finset.mem_Icc] at hi ⊢
      omega
    have hsum := aux_obl_ramp_threshold12_fourth_t12sat_sum_abs_le_of_goodFieldOne m (m - j) omega hgood hsubset hx
    refine le_trans ?_ hsum
    exact Finset.abs_sum_le_sum_abs _ _

private theorem aux_obl_ramp_threshold12_fourth_t12sat_supNormOn_fullShellBlock_le_of_goodFieldOne
    (m : ℕ) {epsilon s : ℝ}
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hgood : GoodFieldOne m 0 epsilon s omega) :
    supNormOn (cube d (m : ℤ)) (fullShellBlock m omega) ≤
      epsilon * (3 : ℝ) ^ ((s * (m : ℝ)) / 8) := by
  refine csSup_le ?_ ?_
  · exact ⟨|fullShellBlock m omega 0|, 0, aux_obl_ramp_threshold12_fourth_t12sat_zero_mem_cube (m : ℤ), rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hsubset : Finset.range (m + 1) ⊆ Finset.Icc (m - m) (m + m) := by
      intro i hi
      simp only [Finset.mem_Icc, Finset.mem_range] at hi ⊢
      omega
    have hsum := aux_obl_ramp_threshold12_fourth_t12sat_sum_abs_le_of_goodFieldOne m m omega hgood hsubset hx
    refine le_trans ?_ hsum
    exact Finset.abs_sum_le_sum_abs _ _

theorem aux_obl_ramp_threshold12_fourth_t12sat_goodScaleShellSlot_le (m : ℕ) {epsilon s : ℝ}
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hgood : GoodFieldOne m 0 epsilon s omega) :
    goodScaleShellSlot s m omega ≤ epsilon := by
  refine csSup_le ⟨_, m, le_rfl, rfl⟩ ?_
  rintro _ ⟨j, hj, rfl⟩
  have hgap : (m : ℝ) - (j : ℝ) = ((m - j : ℕ) : ℝ) := by
    rw [Nat.cast_sub hj]
  have hsup := aux_obl_ramp_threshold12_fourth_t12sat_supNormOn_shellBlock_le_of_goodFieldOne m j hj omega hgood
  have hw : (0 : ℝ) ≤ (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  calc
    (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
        supNormOn (cube d (m : ℤ)) (shellBlock m j omega) ≤
        (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
          (epsilon * (3 : ℝ) ^ ((s * ((m - j : ℕ) : ℝ)) / 8)) :=
      mul_le_mul_of_nonneg_left hsup hw
    _ = epsilon := by
      rw [← hgap, ← mul_assoc, mul_comm _ epsilon, mul_assoc,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      rw [show -(s / 8) * ((m : ℝ) - (j : ℝ)) + s * ((m : ℝ) - (j : ℝ)) / 8 = 0 by
        ring]
      rw [Real.rpow_zero, mul_one]

theorem aux_obl_ramp_threshold12_fourth_t12sat_goodScaleFullSlot_le (m : ℕ) {epsilon s : ℝ}
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hgood : GoodFieldOne m 0 epsilon s omega) :
    goodScaleFullSlot s m omega ≤ epsilon := by
  have hsup := aux_obl_ramp_threshold12_fourth_t12sat_supNormOn_fullShellBlock_le_of_goodFieldOne m omega hgood
  have hw : (0 : ℝ) ≤ (3 : ℝ) ^ (-(s / 8) * (m : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  unfold goodScaleFullSlot
  calc
    (3 : ℝ) ^ (-(s / 8) * (m : ℝ)) *
        supNormOn (cube d (m : ℤ)) (fullShellBlock m omega) ≤
        (3 : ℝ) ^ (-(s / 8) * (m : ℝ)) *
          (epsilon * (3 : ℝ) ^ ((s * (m : ℝ)) / 8)) :=
      mul_le_mul_of_nonneg_left hsup hw
    _ = epsilon := by
      rw [← mul_assoc, mul_comm _ epsilon, mul_assoc,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      rw [show -(s / 8) * (m : ℝ) + s * (m : ℝ) / 8 = 0 by ring]
      rw [Real.rpow_zero, mul_one]

/-! ## The `L < m` saturation branch of the fourth conjunct at threshold 12 -/

/-- **Threshold-12 coarse error above the cutoff.**  The fourth conjunct of
`product_threshold_regularities d 12`, restricted to `L < m`: both the
`min epsilon` display and the `C * epsilon` cap, with one numerical constant
chosen before the model.  This is the exact `hsat` premise of
`aux_obl_ramp_threshold12_fourth_fourth_of_saturation`. -/
theorem aux_obl_ramp_threshold12_fourth_saturation_error (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ L : ℕ,
      ∀ s ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ),
        _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ s * Real.log 3 / 16 →
        ∀ epsilon ∈ Set.Icc (s⁻¹ * M.delta ^ 2) 1, ∀ m : ℕ, L < m → ∀ z : Vec d,
          ∀ ω,
            indicatorValue (_root_.SubdiffusiveProcess.Paper.product_threshold_good_scale d M 12 (some L) m z epsilon s)
                (fun ω' => section6HomogenizationError M s L m ω' z) ω ≤
              C * min epsilon
                (s⁻¹ * M.delta ^ 2 + epsilon ^ 8 +
                  accumulatedError M (some L) m z s ω) ∧
            indicatorValue (_root_.SubdiffusiveProcess.Paper.product_threshold_good_scale d M 12 (some L) m z epsilon s)
                (fun ω' => section6HomogenizationError M s L m ω' z) ω ≤ C * epsilon := by
  set K : ℝ := Real.sqrt aux_obl_ramp_threshold12_fourth_t12sat_squareConstant with hKdef
  have hK0 : 0 < K := Real.sqrt_pos.2 aux_obl_ramp_threshold12_fourth_t12sat_squareConstant_pos
  refine ⟨7 * K, by positivity, ?_⟩
  intro M L s hs _htau epsilon hepsilon m hLm z omega
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hD0 : 0 ≤ s⁻¹ * M.delta ^ 2 := mul_nonneg (inv_nonneg.2 hs0.le) (sq_nonneg _)
  have heps0' : 0 ≤ epsilon := hD0.trans hepsilon.1
  have hEsome0 := Section6Holder.accumulatedError_nonneg M (some L) s m z omega
  by_cases homega : omega ∈ _root_.SubdiffusiveProcess.Paper.product_threshold_good_scale d M 12 (some L) m z epsilon s
  · simp only [indicatorValue, ite_eq_left homega]
    have hprod := aux_obl_ramp_threshold12_fourth_t12sat_productTwelve_of_mem M homega
    obtain ⟨_, hspos, _, heps0, heps1, hfield, _, hresp⟩ := homega
    set eta : _root_.SubdiffusiveProcess.Model.PotentialSample d :=
      translatePotentialSample z omega with heta
    have hrespEta : GoodResponse M (some L) m 0 epsilon s eta :=
      (Section6Covariance.goodResponse_translatePotentialSample
        M (some L) m 0 epsilon s z omega).2 (by simpa only [add_zero] using hresp)
    have hfieldEta : GoodFieldOne m 0 epsilon s eta :=
      (Section6Covariance.goodFieldOne_translatePotentialSample m 0 epsilon s z omega).2
        (by simpa only [add_zero] using hfield)
    have hbase := aux_obl_ramp_threshold12_fourth_t12sat_paperError_le_base M hLm.le heps0.le heps1 hs.1 hs.2 eta
      hfieldEta hprod hrespEta
    obtain ⟨hA0, _, hBs0, hBf0, hBg0⟩ := aux_obl_ramp_threshold12_fourth_t12sat_slots_nonneg M L (m := m) hs0 eta
    set Sigma : ℝ := cutoffGoodScaleResponseSlot M L s m eta + s⁻¹ * M.delta ^ 2 +
      goodScaleShellSlot s m eta + goodScaleFullSlot s m eta +
      goodScaleGradientSlot m eta with hSigma
    have hSigma0 : 0 ≤ Sigma := by rw [hSigma]; linarith
    have hreal : section6HomogenizationError M s L m omega z ≤ K * Sigma := by
      unfold section6HomogenizationError
      exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hK0.le hSigma0) hbase
    -- the truncated display, on the literal cutoff carrier
    set E : ℝ := accumulatedError M (some L) m 0 s eta with hEdef
    have hA := aux_obl_ramp_threshold12_fourth_t12sat_cutoffResponseSlot_le_accumulatedError M L heps0.le hspos.le
      hrespEta
    have hBs := goodScaleShellSlot_le_cutoffAccumulatedError M L s m eta
    have hBf := goodScaleFullSlot_le_two_mul_cutoffAccumulatedError M L s m eta
    have hBg := goodScaleGradientSlot_le_cutoffAccumulatedError M L s m eta
    have hsum5 : Sigma ≤ 5 * (s⁻¹ * M.delta ^ 2 + epsilon ^ 8 + E) := by
      rw [← hEdef] at hA hBs hBf hBg
      have heps8 : 0 ≤ epsilon ^ 8 := pow_nonneg heps0.le 8
      rw [hSigma]
      linarith
    -- the epsilon cap
    have hAe := aux_obl_ramp_threshold12_fourth_t12sat_cutoffResponseSlot_le_epsilon M L heps0.le hspos.le hrespEta
    have hBse := aux_obl_ramp_threshold12_fourth_t12sat_goodScaleShellSlot_le m eta hfieldEta
    have hBfe := aux_obl_ramp_threshold12_fourth_t12sat_goodScaleFullSlot_le m eta hfieldEta
    have hBge : goodScaleGradientSlot m eta ≤ 3 * epsilon := by
      rw [goodScaleGradientSlot_eq_longRatioGradientTail]
      exact longRatioGradientTail_le_three_mul_of_goodFieldOne m heps0.le hs.2
        eta hfieldEta
    have hsum7 : Sigma ≤ 7 * epsilon := by
      rw [hSigma]
      linarith [hepsilon.1]
    have hcarrier : E = accumulatedError M (some L) m z s omega := by
      rw [hEdef, heta, Section6Holder.accumulatedError_translatePotentialSample]
    rw [← hcarrier]
    have hE0 : 0 ≤ E := by
      rw [hEdef]
      exact Section6Holder.accumulatedError_nonneg M (some L) s m 0 eta
    have hX0 : 0 ≤ s⁻¹ * M.delta ^ 2 + epsilon ^ 8 + E := by positivity
    have h5 : section6HomogenizationError M s L m omega z ≤
        K * (5 * (s⁻¹ * M.delta ^ 2 + epsilon ^ 8 + E)) :=
      hreal.trans (mul_le_mul_of_nonneg_left hsum5 hK0.le)
    have h7 : section6HomogenizationError M s L m omega z ≤ K * (7 * epsilon) :=
      hreal.trans (mul_le_mul_of_nonneg_left hsum7 hK0.le)
    refine ⟨?_, by linarith⟩
    rcases le_total epsilon (s⁻¹ * M.delta ^ 2 + epsilon ^ 8 + E) with hle | hle
    · rw [min_eq_left hle]
      linarith
    · rw [min_eq_right hle]
      nlinarith
  · simp only [indicatorValue, ite_eq_right homega]
    exact ⟨by positivity, by positivity⟩


/-! ## The whole fourth conjunct -/



theorem aux_obl_ramp_threshold12_fourth_fourth_error (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ L : ℕ,
      ∀ s ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ),
        _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ s * Real.log 3 / 16 →
        ∀ epsilon ∈ Set.Icc (s⁻¹ * M.delta ^ 2) 1, ∀ m : ℕ, ∀ z : Vec d,
          ∀ ω,
            indicatorValue (_root_.SubdiffusiveProcess.Paper.product_threshold_good_scale d M 12 (some L) m z epsilon s)
                (fun ω' => section6HomogenizationError M s L m ω' z) ω ≤
              C * min epsilon
                (s⁻¹ * M.delta ^ 2 + epsilon ^ 8 +
                  accumulatedError M (some L) m z s ω) ∧
            indicatorValue (_root_.SubdiffusiveProcess.Paper.product_threshold_good_scale d M 12 (some L) m z epsilon s)
                (fun ω' => section6HomogenizationError M s L m ω' z) ω ≤ C * epsilon :=
  aux_obl_ramp_threshold12_fourth_fourth_of_saturation d
    (aux_obl_ramp_threshold12_fourth_saturation_error d)

/-- The coarse-error theorem fills the fourth slot of the threshold-12 carrier. -/
example (d : ℕ) [NeZero d] (h : product_threshold_regularities d 12) :
    product_threshold_regularities d 12 :=
  ⟨h.1, h.2.1, h.2.2.1, aux_obl_ramp_threshold12_fourth_fourth_error d⟩

end SubdiffusiveProcess.Paper

namespace SubdiffusiveProcess.Paper

/-- The literal fourth conjunct of `product_threshold_regularities d 12`. -/
theorem obl_ramp_threshold12_fourth (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ L : ℕ,
      ∀ s ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ),
        _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ s * Real.log 3 / 16 →
        ∀ epsilon ∈ Set.Icc (s⁻¹ * M.delta ^ 2) 1, ∀ m : ℕ, ∀ z : Vec d,
          ∀ ω,
            indicatorValue (_root_.SubdiffusiveProcess.Paper.product_threshold_good_scale d M 12 (some L) m z epsilon s)
                (fun ω' => section6HomogenizationError M s L m ω' z) ω ≤
              C * min epsilon
                (s⁻¹ * M.delta ^ 2 + epsilon ^ 8 +
                  accumulatedError M (some L) m z s ω) ∧
            indicatorValue (_root_.SubdiffusiveProcess.Paper.product_threshold_good_scale d M 12 (some L) m z epsilon s)
                (fun ω' => section6HomogenizationError M s L m ω' z) ω ≤ C * epsilon := by
  exact aux_obl_ramp_threshold12_fourth_fourth_error d

end SubdiffusiveProcess.Paper
