import SubdiffusiveProcess.Paper.obl_ramp_site_inputs
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.GoodScaleSaturation
import SubdiffusiveProcess.CoarseGrainingVocab.Section6AnnularResummation
import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.GoodEventCap




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

namespace Paper

variable {d : ℕ}

/-! ## Elementary sup-norm reads -/

private theorem aux_in_deterministic_equal_scale_b12_supNormOn_nonneg (W : Set (Vec d)) (f : Vec d → ℝ) :
    0 ≤ supNormOn W f := by
  refine Real.sSup_nonneg ?_
  rintro a ⟨x, _, rfl⟩
  exact abs_nonneg _

private theorem aux_in_deterministic_equal_scale_b12_abs_le_supNormOn {W : Set (Vec d)} {f : Vec d → ℝ}
    (hB : BddAbove ((fun x => |f x|) '' W)) {x : Vec d} (hx : x ∈ W) :
    |f x| ≤ supNormOn W f := by
  unfold supNormOn
  refine le_csSup (hB.mono ?_) ⟨x, hx, rfl⟩
  rintro r ⟨y, hy, rfl⟩
  exact ⟨y, hy, rfl⟩

private theorem aux_in_deterministic_equal_scale_b12_shellBlock_continuous (m n : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    Continuous (shellBlock m n omega) := by
  unfold shellBlock
  fun_prop

private theorem aux_in_deterministic_equal_scale_b12_bddAbove_abs_values_cube (m : ℕ) {f : Vec d → ℝ}
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

private theorem aux_in_deterministic_equal_scale_b12_zero_mem_cube (k : ℤ) : (0 : Vec d) ∈ cube d k := by
  rw [cube, mem_openCubeSet_originCube_iff]
  intro i
  have hp : 0 < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  constructor <;> simp only [Pi.zero_apply] <;> nlinarith

/-! ## Site (ii): the combined-ratio error from `obl_ramp_site_inputs` -/

/-- The two-squared-`L^∞` sensitivity error on a local cube, read from the
threshold-12 sup-norm bound of `obl_ramp_site_inputs` (clause (ii)). -/
theorem aux_in_deterministic_equal_scale_b12_cutoffRatioError_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m n : ℕ} (hnm : n ≤ m) (hmL : m ≤ L)
    (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z : Vec d) {W : ℝ}
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
  have h1 := aux_in_deterministic_equal_scale_b12_supNormOn_nonneg (cube d n)
    (fun x => combinedCoefficientRatio M L m n eta z x - 1)
  have h2 := aux_in_deterministic_equal_scale_b12_supNormOn_nonneg (cube d n)
    (fun x => combinedCoefficientRatioInv M L m n eta z x - 1)
  have hW0 : 0 ≤ W := by linarith
  have hfwd : ∀ x ∈ (U : Set (Vec d)),
      |combinedCoefficientRatio M L m n eta z x - 1| ≤ W := by
    intro x hx
    have hx' : x ∈ cube d n := by simpa only [hU, Ch02.cubeDomain_coe] using hx
    have h := aux_in_deterministic_equal_scale_b12_abs_le_supNormOn
      (f := fun x => combinedCoefficientRatio M L m n eta z x - 1) hB1 hx'
    linarith
  have hrev : ∀ x ∈ (U : Set (Vec d)),
      |combinedCoefficientRatioInv M L m n eta z x - 1| ≤ W := by
    intro x hx
    have hx' : x ∈ cube d n := by simpa only [hU, Ch02.cubeDomain_coe] using hx
    have h := aux_in_deterministic_equal_scale_b12_abs_le_supNormOn
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
theorem aux_in_deterministic_equal_scale_b12_weighted_probe_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m n j : ℕ}
    (hnm : n ≤ m) {s CB : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s)
    (hj : j ≤ m) (hnj : n + 2 ≤ j)
    (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
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
          SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m - n : ℕ) : ℝ))) ^ 2) :
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
            SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P *
              ((m - n : ℕ) : ℝ))) ^ 2 := by
  let T : ℝ := ((m - n : ℕ) : ℝ)
  let u : ℝ := s * T
  let A : ℝ := (3 : ℝ) ^ ((3 * s * T) / 16)
  let B : ℝ := min 1 (longRatioGradientTail m eta +
    supNormOn (cube d n)
      (shellBlock m n
        (translatePotentialSample (triadicCubeShift R) eta)) +
    SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * T)
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
theorem aux_in_deterministic_equal_scale_b12_weighted_probe_le_split
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m n j : ℕ}
    (hnm : n ≤ m) {s CB : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s)
    (hj : j ≤ m) (hnj : n + 2 ≤ j)
    (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
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
          SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m - n : ℕ) : ℝ))) ^ 2) :
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
  let D : ℝ := SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * T
  let Main : ℝ := 2 * v * section6Response M n n eta (triadicCubeShift R) e
  let Pweighted : ℝ := (3 : ℝ) ^ (-(3 / 2) * (s * T)) *
    paperScalarProbe (originCube d (n : ℤ))
      (aCutoffFamily M L
        (translatePotentialSample (triadicCubeShift R) eta))
      (tailCoefficientCubeAverage M L m eta) e
  have hraw : Pweighted ≤ Main + 12 * CB ^ 2 * v * min 1 (S + G + D) ^ 2 := by
    simpa only [Pweighted, Main, v, S, G, D, T] using
      aux_in_deterministic_equal_scale_b12_weighted_probe_le M hnm hsLower hj hnj eta hR hann he hresp hE
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
theorem aux_in_deterministic_equal_scale_b12_response_atom_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m : ℕ} {epsilon s : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hs0 : 0 ≤ s)
    {omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d}
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

private theorem aux_in_deterministic_equal_scale_b12_responseSlot_bddAbove
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {s : ℝ} {m : ℕ}
    {omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d}
    (hs0 : 0 ≤ s) (hresp : GoodResponse M none m 0 1 s omega) :
    BddAbove {r : ℝ | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧
      ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d j \ cube d (j - 1) ∧
      r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
        Real.sqrt (sSup {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
          t = section6Response M n n omega z e})} := by
  refine ⟨1, ?_⟩
  intro r hr
  exact aux_in_deterministic_equal_scale_b12_response_atom_le M zero_le_one hs0 hresp hr

/-! ## Slot domination (upstream `AnnularAggregation`) -/

private theorem aux_in_deterministic_equal_scale_b12_supNormOn_mono_cube {n m : ℕ}
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {R : SubdiffusiveProcess.CoarseGrainingVocab.TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)) :
    supNormOn (cube d n)
        (shellBlock m n (translatePotentialSample (triadicCubeShift R) omega)) ≤
      supNormOn (cube d m) (shellBlock m n omega) := by
  unfold supNormOn
  apply csSup_le
  · exact ⟨|shellBlock m n (translatePotentialSample (triadicCubeShift R) omega) 0|,
      0, aux_in_deterministic_equal_scale_b12_zero_mem_cube (n : ℤ), rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hscale : R.scale = (n : ℤ) := scale_eq_of_mem_descendantsAtScale hR
    have hxR : triadicCubeShift R + x ∈ openCubeSet R := by
      rw [openCubeSet_eq_translateSet_originCube_of_triadicCube,
        mem_translateSet_iff_sub_mem]
      simpa only [hscale, add_sub_cancel_left] using hx
    have hxM : triadicCubeShift R + x ∈ cube d m :=
      openCubeSet_subset_of_mem_descendantsAtScale
        (scale_le_of_mem_descendantsAtScale hR) hR hxR
    have hle : |shellBlock m n omega (triadicCubeShift R + x)| ≤
        sSup {a : ℝ | ∃ y ∈ cube d m, a = |shellBlock m n omega y|} :=
      le_csSup (aux_in_deterministic_equal_scale_b12_bddAbove_abs_values_cube m
        (aux_in_deterministic_equal_scale_b12_shellBlock_continuous m n omega))
        ⟨triadicCubeShift R + x, hxM, rfl⟩
    simpa only [shellBlock_translatePotentialSample, add_comm] using hle

private theorem aux_in_deterministic_equal_scale_b12_shellSlot_bddAbove
    (s : ℝ) (m : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
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

private theorem aux_in_deterministic_equal_scale_b12_response_weight_le_slot_sq
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m n j : ℕ}
    (hnm : n ≤ m) {s : ℝ} (hs0 : 0 ≤ s)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
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
    exact le_csSup (aux_in_deterministic_equal_scale_b12_responseSlot_bddAbove M hs0 hresp) hatomMem
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

private theorem aux_in_deterministic_equal_scale_b12_shell_weight_le_slot_sq
    {m n : ℕ} (hnm : n ≤ m) {s : ℝ} (hs0 : 0 ≤ s)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) {R : SubdiffusiveProcess.CoarseGrainingVocab.TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)) :
    (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
        supNormOn (cube d n)
          (shellBlock m n (translatePotentialSample (triadicCubeShift R) omega)) ^ 2 ≤
      goodScaleShellSlot s m omega ^ 2 := by
  let G := supNormOn (cube d m) (shellBlock m n omega)
  let atom := (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (n : ℝ))) * G
  have hGlocal := aux_in_deterministic_equal_scale_b12_supNormOn_mono_cube omega hR
  have hG0 : 0 ≤ G := aux_in_deterministic_equal_scale_b12_supNormOn_nonneg _ _
  have hatomMem : atom ∈ {r : ℝ | ∃ j ≤ m,
      r = (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
        supNormOn (cube d m) (shellBlock m j omega)} :=
    ⟨n, hnm, by simp only [atom, G]⟩
  have hatomLe : atom ≤ goodScaleShellSlot s m omega := by
    unfold goodScaleShellSlot
    exact le_csSup (aux_in_deterministic_equal_scale_b12_shellSlot_bddAbove s m omega) hatomMem
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
    aux_in_deterministic_equal_scale_b12_supNormOn_nonneg _ _
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
def aux_in_deterministic_equal_scale_b12_positiveBudget (CB : ℝ) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (s : ℝ) (m : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : ℝ :=
  2 * goodScaleResponseSlot M s m omega ^ 2 +
    36 * CB ^ 2 *
      (goodScaleGradientSlot m omega ^ 2 +
        goodScaleShellSlot s m omega ^ 2 +
        2 * (s⁻¹ * M.delta ^ 2) ^ 2)

theorem aux_in_deterministic_equal_scale_b12_positiveBudget_nonneg (CB : ℝ)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (s : ℝ) (m : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    0 ≤ aux_in_deterministic_equal_scale_b12_positiveBudget CB M s m omega := by
  unfold aux_in_deterministic_equal_scale_b12_positiveBudget
  positivity



def aux_in_deterministic_equal_scale_b12_SiteTwo (CB : ℝ) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ)
    (m : ℕ) (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : Prop :=
  ∀ n : ℕ, n ≤ m → ∀ z : Vec d,
    translatedCube d n z ⊆ cube d m →
    BddAbove ((fun x : Vec d =>
      |combinedCoefficientRatio M m m n eta z x - 1|) '' cube d n) ∧
    BddAbove ((fun x : Vec d =>
      |combinedCoefficientRatioInv M m m n eta z x - 1|) '' cube d n) ∧
    supNormOn (cube d n)
        (fun x => combinedCoefficientRatio M m m n eta z x - 1) +
      supNormOn (cube d n)
        (fun x => combinedCoefficientRatioInv M m m n eta z x - 1) ≤
      CB * (3 : ℝ) ^ (3 * s * ((m : ℝ) - (n : ℝ)) / 16) *
        min 1 (longRatioGradientTail m eta +
          supNormOn (cube d n)
            (shellBlock m n (translatePotentialSample z eta)) +
          SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) - (n : ℝ)))

/-- Every nonnegative-scale annular atom is dominated by the threshold-12
positive budget. -/
theorem aux_in_deterministic_equal_scale_b12_positive_annular_atom_le_budget
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m : ℕ} {s CB : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s)
    (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hresp : GoodResponse M none m 0 1 s eta)
    (hsite : aux_in_deterministic_equal_scale_b12_SiteTwo CB M s m eta)
    (p : AnnularPairTwo d (m : ℤ)) (hscale0 : 0 ≤ p.1.1.scale) :
    ENNReal.ofReal
          ((3 : ℝ) ^ (-(3 * s / 2) *
            ((m : ℝ) - (p.1.1.scale : ℝ)))) *
        section6LocalProbeMax M m eta 0
          (tailCoefficientCubeAverage M m m eta) p.1.1 ≤
      ENNReal.ofReal (aux_in_deterministic_equal_scale_b12_positiveBudget CB M s m eta) := by
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
      simpa only [hRscale, add_sub_cancel_left] using hx
    exact openCubeSet_subset_of_mem_descendantsAtScale
      (scale_le_of_mem_descendantsAtScale hR) hR hxR
  obtain ⟨hB1, hB2, hsum⟩ := hsite n hnm (triadicCubeShift p.1.1) hsub
  have hgapR : (m : ℝ) - (n : ℝ) = ((m - n : ℕ) : ℝ) := by rw [Nat.cast_sub hnm]
  have hE := aux_in_deterministic_equal_scale_b12_cutoffRatioError_le M hnm le_rfl eta
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
  have hraw := aux_in_deterministic_equal_scale_b12_weighted_probe_le_split M hnm hsLower hjm hnj eta hR hann' e.2
    hresp (by simpa only [mul_assoc] using hE)
  have hresp2 := aux_in_deterministic_equal_scale_b12_response_weight_le_slot_sq M hnm hs0 eta hresp hjm hnj
    (onTriadicGrid_triadicCubeShift_of_scale
      (scale_eq_of_mem_descendantsAtScale hR)) hann' e.2
  have hshell := aux_in_deterministic_equal_scale_b12_shell_weight_le_slot_sq hnm hs0 eta hR
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
  simpa only [aux_in_deterministic_equal_scale_b12_positiveBudget, hncast] using hfinal

/-! ## The subunit branch (upstream `SubunitTail`, site (iii)) -/

private theorem aux_in_deterministic_equal_scale_b12_three_rpow_add (a b : ℝ) :
    (3 : ℝ) ^ a * (3 : ℝ) ^ b = (3 : ℝ) ^ (a + b) :=
  (Real.rpow_add (by norm_num) a b).symm

private theorem aux_in_deterministic_equal_scale_b12_three_rpow_sq (a : ℝ) :
    ((3 : ℝ) ^ a) ^ 2 = (3 : ℝ) ^ (2 * a) := by
  rw [pow_two, aux_in_deterministic_equal_scale_b12_three_rpow_add]
  ring_nf

private theorem aux_in_deterministic_equal_scale_b12_subunit_envelope_weight {s : ℝ} (hs0 : 0 ≤ s)
    (hs2 : s ≤ 1 / 2) (m : ℕ) :
    (3 : ℝ) ^ (-(3 * s / 2) * (m : ℝ)) * subunitEnvelope s m ^ 2 ≤
      108 * (3 : ℝ) ^ (-(s * (m : ℝ))) := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have henv : subunitEnvelope s m ^ 2 =
      36 * (3 : ℝ) ^ (2 * ((s * (m : ℝ)) / 8) + 2 * ((s * ((m : ℝ) + 1)) / 16)) := by
    unfold subunitEnvelope
    rw [mul_pow, mul_pow, aux_in_deterministic_equal_scale_b12_three_rpow_sq, aux_in_deterministic_equal_scale_b12_three_rpow_sq, mul_assoc,
      aux_in_deterministic_equal_scale_b12_three_rpow_add]
    norm_num
  rw [henv, ← mul_assoc, mul_comm ((3 : ℝ) ^ (-(3 * s / 2) * (m : ℝ))) 36,
    mul_assoc, aux_in_deterministic_equal_scale_b12_three_rpow_add]
  have hexp : -(3 * s / 2) * (m : ℝ) +
      (2 * ((s * (m : ℝ)) / 8) + 2 * ((s * ((m : ℝ) + 1)) / 16)) =
      -(s * (m : ℝ)) + s * (1 - (m : ℝ)) / 8 := by ring
  rw [hexp, ← aux_in_deterministic_equal_scale_b12_three_rpow_add]
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
def aux_in_deterministic_equal_scale_b12_subunitBudget (CB : ℝ) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (s : ℝ) (m : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : ℝ :=
  324 * (2 * CB) ^ 2 *
    (goodScaleGradientSlot m omega ^ 2 +
      goodScaleFullSlot s m omega ^ 2 +
      6 * (s⁻¹ * M.delta ^ 2) ^ 2)

theorem aux_in_deterministic_equal_scale_b12_subunitBudget_nonneg (CB : ℝ)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (s : ℝ) (m : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    0 ≤ aux_in_deterministic_equal_scale_b12_subunitBudget CB M s m omega := by
  unfold aux_in_deterministic_equal_scale_b12_subunitBudget
  positivity

/-- Every nonpositive-scale annular atom is dominated by the threshold-12
subunit budget.  The pointwise ratio energy is site (iii) of
`obl_ramp_site_inputs`. -/
theorem aux_in_deterministic_equal_scale_b12_subunit_atom_le_budget [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m : ℕ} {s CB : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hsite : ∀ x ∈ cube d (m : ℤ),
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m eta x /
            tailCoefficientCubeAverage M m m eta - 1) ^ 2 +
          (tailCoefficientCubeAverage M m m eta /
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m eta x - 1) ^ 2 ≤
        ((2 * CB) * subunitEnvelope s m * subunitDeviation M m eta) ^ 2)
    {R : SubdiffusiveProcess.CoarseGrainingVocab.TriadicCube d} {j : ℤ} (hj : j ≤ (m : ℤ)) (hscale : R.scale ≤ j - 2)
    (hann : triadicCubeShift R ∈ cube d j \ cube d (j - 1))
    (hneg : R.scale ≤ 0) :
    ENNReal.ofReal ((3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (R.scale : ℝ)))) *
        section6LocalProbeMax M m eta 0
          (tailCoefficientCubeAverage M m m eta) R ≤
      ENNReal.ofReal (aux_in_deterministic_equal_scale_b12_subunitBudget CB M s m eta) := by
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hsLower
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  set K : ℝ := ((2 * CB) * subunitEnvelope s m * subunitDeviation M m eta) ^ 2 with hK
  set omega' : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d :=
    translatePotentialSample (triadicCubeShift R) eta with homega'
  have hRdesc : R ∈ descendantsAtScale (originCube d (m : ℤ)) R.scale :=
    annularCube_mem_descendantsAtScale hj hscale hann
  have hpoint : ∀ x ∈ ((Ch02.cubeDomain (originCube d R.scale) :
      Ch02.Domain d) : Set (Vec d)),
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m omega' x /
            tailCoefficientCubeAverage M m m eta - 1) ^ 2 +
          (tailCoefficientCubeAverage M m m eta /
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m omega' x - 1) ^ 2 ≤ K := by
    intro x hx
    have hxcube : x ∈ cube d R.scale := by
      simpa only [Ch02.cubeDomain_coe] using hx
    have hxR : triadicCubeShift R + x ∈ openCubeSet R := by
      rw [openCubeSet_eq_translateSet_originCube_of_triadicCube,
        mem_translateSet_iff_sub_mem]
      simpa only [add_sub_cancel_left] using hxcube
    have hxM : triadicCubeShift R + x ∈ cube d (m : ℤ) :=
      openCubeSet_subset_of_mem_descendantsAtScale
        (scale_le_of_mem_descendantsAtScale hRdesc) hRdesc hxR
    have hxM' : x + triadicCubeShift R ∈ cube d (m : ℤ) := by
      rwa [add_comm] at hxM
    rw [homega', Section6Covariance.aCutoff_translatePotentialSample]
    exact hsite _ hxM'
  have haverage : Ch02.average (Ch02.cubeDomain (originCube d R.scale))
      (fun x =>
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m omega' x /
          tailCoefficientCubeAverage M m m eta - 1) ^ 2 +
        (tailCoefficientCubeAverage M m m eta /
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m omega' x - 1) ^ 2) ≤ K := by
    set U : Ch02.Domain d := Ch02.cubeDomain (originCube d R.scale) with hU
    have ha_pos : ∀ x, 0 < SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m omega' x :=
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M m omega'
    have hcontinuous : Continuous (fun x =>
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m omega' x /
          tailCoefficientCubeAverage M m m eta - 1) ^ 2 +
          (tailCoefficientCubeAverage M m m eta /
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m omega' x - 1) ^ 2) :=
      ((((SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M m omega').div_const _).sub
        continuous_const).pow 2).add
        (((continuous_const.div
          (SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M m omega')
          (fun x => (ha_pos x).ne')).sub continuous_const).pow 2)
    exact average_le_of_le_on U
      ((hcontinuous.continuousOn.integrableOn_compact
        U.isDomain.isBoundedDomain.isBounded.isCompact_closure).mono_set
          subset_closure) hpoint
  have hprobe : section6LocalProbeMax M m eta 0
      (tailCoefficientCubeAverage M m m eta) R ≤ ENNReal.ofReal K :=
    (section6LocalProbeMax_le_ratioEnergy_average M m m eta R).trans
      (ENNReal.ofReal_le_ofReal haverage)
  have hweight : (3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (R.scale : ℝ))) ≤
      (3 : ℝ) ^ (-(3 * s / 2) * (m : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hkr : ((R.scale : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hneg
    nlinarith
  have hw0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (R.scale : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hfinal : (3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (R.scale : ℝ))) * K ≤
      aux_in_deterministic_equal_scale_b12_subunitBudget CB M s m eta := by
    set S : ℝ := longRatioGradientTail m eta with hS
    set G : ℝ := supNormOn (cube d (m : ℤ)) (fullShellBlock m eta) with hG
    set Rho : ℝ := SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) + 1) with hRho
    have henv := aux_in_deterministic_equal_scale_b12_subunit_envelope_weight (s := s) hs0.le hsUpper m
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
        rw [goodScaleFullSlot, mul_pow, aux_in_deterministic_equal_scale_b12_three_rpow_sq, ← hG]
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
          rw [aux_in_deterministic_equal_scale_b12_three_rpow_add]
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
            (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) + 1)) ^ 2) := by
          rw [hRho]; ring
        _ ≤ 3 * (2 * (s⁻¹) ^ 2 * M.delta ^ 4) :=
          mul_le_mul_of_nonneg_left hcore (by norm_num)
        _ = 6 * (s⁻¹ * M.delta ^ 2) ^ 2 := by ring
    refine hstep1.trans ?_
    unfold aux_in_deterministic_equal_scale_b12_subunitBudget
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
        section6LocalProbeMax M m eta 0
          (tailCoefficientCubeAverage M m m eta) R ≤
        ENNReal.ofReal ((3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (R.scale : ℝ)))) *
          ENNReal.ofReal K := by
      gcongr
    _ = ENNReal.ofReal ((3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (R.scale : ℝ))) * K) :=
      (ENNReal.ofReal_mul hw0).symm
    _ ≤ ENNReal.ofReal (aux_in_deterministic_equal_scale_b12_subunitBudget CB M s m eta) :=
      ENNReal.ofReal_le_ofReal hfinal

/-! ## The complete annular supremum and the base display -/

/-- The site-(iii) hypothesis of `obl_ramp_site_inputs` at `L = m`, written
with the upstream envelope (`12 * ... = 2 * subunitEnvelope`). -/
def aux_in_deterministic_equal_scale_b12_SiteThree (CB : ℝ) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ)
    (m : ℕ) (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : Prop :=
  ∀ x ∈ cube d (m : ℤ),
    (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m eta x /
          tailCoefficientCubeAverage M m m eta - 1) ^ 2 +
        (tailCoefficientCubeAverage M m m eta /
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m eta x - 1) ^ 2 ≤
      ((2 * CB) * subunitEnvelope s m * subunitDeviation M m eta) ^ 2

theorem aux_in_deterministic_equal_scale_b12_annularSupTwo_le_budget [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m : ℕ} {s CB : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hresp : GoodResponse M none m 0 1 s eta)
    (hsiteTwo : aux_in_deterministic_equal_scale_b12_SiteTwo CB M s m eta)
    (hsiteThree : aux_in_deterministic_equal_scale_b12_SiteThree CB M s m eta) :
    annularSupTwo s (m : ℤ)
        (section6LocalProbeMax M m eta 0 (tailCoefficientCubeAverage M m m eta)) ≤
      ENNReal.ofReal (aux_in_deterministic_equal_scale_b12_positiveBudget CB M s m eta +
        aux_in_deterministic_equal_scale_b12_subunitBudget CB M s m eta) := by
  refine iSup_le fun p => ?_
  rcases le_or_gt 0 p.1.1.scale with hscale0 | hscaleneg
  · refine (aux_in_deterministic_equal_scale_b12_positive_annular_atom_le_budget M hsLower eta hresp hsiteTwo
      p hscale0).trans (ENNReal.ofReal_le_ofReal ?_)
    have := aux_in_deterministic_equal_scale_b12_subunitBudget_nonneg CB M s m eta
    linarith
  · obtain ⟨hj, hsc, hann⟩ := p.2
    refine (aux_in_deterministic_equal_scale_b12_subunit_atom_le_budget M hsLower hsUpper eta hsiteThree
      hj hsc hann hscaleneg.le).trans (ENNReal.ofReal_le_ofReal ?_)
    have := aux_in_deterministic_equal_scale_b12_positiveBudget_nonneg CB M s m eta
    linarith

/-- The square of the threshold-12 base constant. -/
def aux_in_deterministic_equal_scale_b12_squareConstant (CB : ℝ) : ℝ := 384 + 1506816 * CB ^ 2

private theorem aux_in_deterministic_equal_scale_b12_budget_le_square (CB A D Bs Bf Bg : ℝ) :
    192 * ((2 * A ^ 2 + 36 * CB ^ 2 * (Bg ^ 2 + Bs ^ 2 + 2 * D ^ 2)) +
        324 * (2 * CB) ^ 2 * (Bg ^ 2 + Bf ^ 2 + 6 * D ^ 2)) ≤
      aux_in_deterministic_equal_scale_b12_squareConstant CB * (A ^ 2 + D ^ 2 + Bs ^ 2 + Bf ^ 2 + Bg ^ 2) := by
  unfold aux_in_deterministic_equal_scale_b12_squareConstant
  have h1 := mul_nonneg (sq_nonneg CB) (sq_nonneg A)
  have h2 := mul_nonneg (sq_nonneg CB) (sq_nonneg Bs)
  have h3 := mul_nonneg (sq_nonneg CB) (sq_nonneg Bf)
  have h4 := mul_nonneg (sq_nonneg CB) (sq_nonneg Bg)
  have h5 := sq_nonneg D
  have h6 := sq_nonneg Bs
  have h7 := sq_nonneg Bf
  have h8 := sq_nonneg Bg
  have hexp : aux_in_deterministic_equal_scale_b12_squareConstant CB * (A ^ 2 + D ^ 2 + Bs ^ 2 + Bf ^ 2 + Bg ^ 2) -
      192 * ((2 * A ^ 2 + 36 * CB ^ 2 * (Bg ^ 2 + Bs ^ 2 + 2 * D ^ 2)) +
        324 * (2 * CB) ^ 2 * (Bg ^ 2 + Bf ^ 2 + 6 * D ^ 2)) =
      1506816 * (CB ^ 2 * A ^ 2) + 384 * D ^ 2 + 384 * Bs ^ 2 + 384 * Bf ^ 2 +
        384 * Bg ^ 2 + 1499904 * (CB ^ 2 * Bs ^ 2) + 1257984 * (CB ^ 2 * Bf ^ 2) +
        1251072 * (CB ^ 2 * Bg ^ 2) := by
    unfold aux_in_deterministic_equal_scale_b12_squareConstant
    ring
  unfold aux_in_deterministic_equal_scale_b12_squareConstant at hexp
  linarith

/-- Nonnegativity of the five display slots. -/
private theorem aux_in_deterministic_equal_scale_b12_slots_nonneg
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m : ℕ} {s : ℝ} (hs0 : 0 < s)
    (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
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
      (aux_in_deterministic_equal_scale_b12_supNormOn_nonneg _ _)
  · exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (aux_in_deterministic_equal_scale_b12_supNormOn_nonneg _ _)
  · rw [goodScaleGradientSlot_eq_longRatioGradientTail]
    exact longRatioGradientTail_nonneg m eta

/-- The square-root arithmetic of the base display. -/
private theorem aux_in_deterministic_equal_scale_b12_sqrt_budget_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m : ℕ} {s CB : ℝ} (hs0 : 0 < s)
    (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    (192 * (aux_in_deterministic_equal_scale_b12_positiveBudget CB M s m eta +
        aux_in_deterministic_equal_scale_b12_subunitBudget CB M s m eta)) ^ (1 / 2 : ℝ) ≤
      Real.sqrt (aux_in_deterministic_equal_scale_b12_squareConstant CB) *
        (goodScaleResponseSlot M s m eta + s⁻¹ * M.delta ^ 2 +
          goodScaleShellSlot s m eta + goodScaleFullSlot s m eta +
          goodScaleGradientSlot m eta) := by
  obtain ⟨hA0, hD0, hBs0, hBf0, hBg0⟩ := aux_in_deterministic_equal_scale_b12_slots_nonneg M (m := m) hs0 eta
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
  have hcoef : 192 * (aux_in_deterministic_equal_scale_b12_positiveBudget CB M s m eta +
      aux_in_deterministic_equal_scale_b12_subunitBudget CB M s m eta) ≤ aux_in_deterministic_equal_scale_b12_squareConstant CB *
      (A ^ 2 + D ^ 2 + Bs ^ 2 + Bf ^ 2 + Bg ^ 2) := by
    rw [aux_in_deterministic_equal_scale_b12_positiveBudget, aux_in_deterministic_equal_scale_b12_subunitBudget,
      ← hAdef, ← hDdef, ← hBsdef, ← hBfdef, ← hBgdef]
    exact aux_in_deterministic_equal_scale_b12_budget_le_square CB A D Bs Bf Bg
  have hT0 : 0 ≤ aux_in_deterministic_equal_scale_b12_squareConstant CB := by
    unfold aux_in_deterministic_equal_scale_b12_squareConstant
    positivity
  calc
    Real.sqrt (192 * (aux_in_deterministic_equal_scale_b12_positiveBudget CB M s m eta +
        aux_in_deterministic_equal_scale_b12_subunitBudget CB M s m eta)) ≤
        Real.sqrt (aux_in_deterministic_equal_scale_b12_squareConstant CB * Sigma ^ 2) :=
      Real.sqrt_le_sqrt (hcoef.trans (mul_le_mul_of_nonneg_left hsq hT0))
    _ = Real.sqrt (aux_in_deterministic_equal_scale_b12_squareConstant CB) * Sigma := by
      rw [Real.sqrt_mul hT0, Real.sqrt_sq hSigma0]

/-- The threshold-12 base display for the `ℝ≥0∞`-valued paper error itself
(no `toReal`): the weighted descendant series is bounded through the annular
supremum, so the paper error is finite on the event. -/
theorem aux_in_deterministic_equal_scale_b12_paperError_le_base [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m : ℕ} {s CB : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hresp : GoodResponse M none m 0 1 s eta)
    (hsiteTwo : aux_in_deterministic_equal_scale_b12_SiteTwo CB M s m eta)
    (hsiteThree : aux_in_deterministic_equal_scale_b12_SiteThree CB M s m eta) :
    paperHomogenizationError (originCube d (m : ℤ)) (m : ℤ) s .infinity (.finite 2)
        (aCutoffFamily M m eta) (tailCoefficientCubeAverage M m m eta) ≤
      ENNReal.ofReal (Real.sqrt (aux_in_deterministic_equal_scale_b12_squareConstant CB) *
        (goodScaleResponseSlot M s m eta + s⁻¹ * M.delta ^ 2 +
          goodScaleShellSlot s m eta + goodScaleFullSlot s m eta +
          goodScaleGradientSlot m eta)) := by
  have hdim : 2 ≤ d := M.shellPrefix.dimension
  have hd1 : 1 ≤ d := by omega
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hsLower
  set alpha : ℝ := tailCoefficientCubeAverage M m m eta with halpha
  set g : SubdiffusiveProcess.CoarseGrainingVocab.TriadicCube d → ℝ≥0∞ :=
    section6LocalProbeMax M m eta 0 alpha with hg
  set B : ℝ := aux_in_deterministic_equal_scale_b12_positiveBudget CB M s m eta +
    aux_in_deterministic_equal_scale_b12_subunitBudget CB M s m eta with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    have h1 := aux_in_deterministic_equal_scale_b12_positiveBudget_nonneg CB M s m eta
    have h2 := aux_in_deterministic_equal_scale_b12_subunitBudget_nonneg CB M s m eta
    linarith
  have hseries := tsum_geometricWeight_descendantSup_le_annularSup hs0 hsUpper hd1 m g
    (fun n _ => section6LocalProbeMax_originCube_le_onion M m eta 0 alpha n)
  have hthree := annularSup_le_three_mul_annularSupTwo (m := (m : ℤ)) hsUpper g
    (section6LocalProbeMax_le_child M m eta 0 alpha)
  have hstep2 : annularSupTwo s (m : ℤ) g ≤ ENNReal.ofReal B :=
    aux_in_deterministic_equal_scale_b12_annularSupTwo_le_budget M hsLower hsUpper eta hresp hsiteTwo hsiteThree
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
        (aCutoffFamily M m eta) alpha) =
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
    _ ≤ _ := ENNReal.ofReal_le_ofReal (aux_in_deterministic_equal_scale_b12_sqrt_budget_le M hs0 eta)


/-! ## Response truncation (upstream `RefinedLocalMathcalE`) -/

private theorem aux_in_deterministic_equal_scale_b12_truncatedResponseSet_bddAbove
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m : ℕ} {s : ℝ}
    (hs : 0 ≤ s) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
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
theorem aux_in_deterministic_equal_scale_b12_responseSlot_le_accumulatedError
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m : ℕ} {epsilon s : ℝ}
    (hepsilon : 0 ≤ epsilon) (hs : 0 ≤ s)
    {omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d}
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
        (aux_in_deterministic_equal_scale_b12_truncatedResponseSet_bddAbove M hs omega) hjm hnj
      · simpa only [sub_zero] using hzgrid
      · simpa only [sub_zero] using hzann
    have hadd := add_le_add htruncated (le_refl (epsilon ^ 8))
    simpa only [A, Option.getD_none, min_self] using htrunc.trans hadd
  · have hEmpty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    rw [hEmpty, Real.sSup_empty]
    exact add_nonneg (Section6Holder.accumulatedError_nonneg M none s m 0 omega)
      (pow_nonneg hepsilon 8)

/-! ## The principal equal-scale threshold-12 estimates -/

/-- **Equal-scale threshold-12 coarse error, `ℝ≥0∞` form.**  A dimension-only
constant, chosen before the model, bounds the paper error itself (the carrier
whose `toReal` is `section6HomogenizationError M s m m omega z`) at the equal
scale `L = m` on the literal threshold-12 event, under exactly the parameter
assumptions of the fourth conjunct of `product_threshold_regularities d 12`.
In particular the paper error is finite on the event. -/
theorem aux_in_deterministic_equal_scale_b12_paper_error (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ),
      SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ s * Real.log 3 / 16 →
      ∀ epsilon ∈ Set.Icc (s⁻¹ * M.delta ^ 2) 1,
      ∀ (m : ℕ) (z : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        omega ∈ Paper.product_threshold_good_scale d M 12 (some m) m z epsilon s →
        paperHomogenizationError (originCube d (m : ℤ)) (m : ℤ) s .infinity (.finite 2)
            (aCutoffFamily M m (translatePotentialSample z omega))
            (tailCoefficientCubeAverage M m m (translatePotentialSample z omega)) ≤
          ENNReal.ofReal (C * (s⁻¹ * M.delta ^ 2 + epsilon ^ 8 +
            accumulatedError M (some m) m z s omega)) := by
  obtain ⟨CB, hCB, hsites⟩ := Paper.obl_ramp_site_inputs d
  have hT0 : 0 < aux_in_deterministic_equal_scale_b12_squareConstant CB := by
    unfold aux_in_deterministic_equal_scale_b12_squareConstant
    positivity
  have hK0 : 0 < Real.sqrt (aux_in_deterministic_equal_scale_b12_squareConstant CB) := Real.sqrt_pos.2 hT0
  refine ⟨5 * Real.sqrt (aux_in_deterministic_equal_scale_b12_squareConstant CB), by positivity, ?_⟩
  intro M s hs htau epsilon hepsilon m z omega homega
  obtain ⟨hBpos, hspos, hs1, heps0, heps1, hfield, hprod, hresp⟩ := homega
  -- the literal threshold-12 event at amplitude one, as consumed by the sites
  have hone : omega ∈ Paper.product_threshold_good_scale d M 12 (some m) m z 1 s :=
    ⟨hBpos, hspos, hs1, one_pos, le_rfl,
      Section6ExcessDecay.goodFieldOne_mono heps1 hfield, hprod,
      Section6ExcessDecay.goodResponse_mono heps0.le heps1 hresp⟩
  have hsite := hsites M s hs htau m m le_rfl z omega hone
  set eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d :=
    translatePotentialSample z omega with heta
  obtain ⟨_, hII, _, _, hIII⟩ := hsite
  have hsiteTwo : aux_in_deterministic_equal_scale_b12_SiteTwo CB M s m eta := by
    intro n hn z' hz'
    obtain ⟨h1, h2, _, _, _, h6⟩ := hII n hn z' hz'
    exact ⟨h1, h2, h6⟩
  have hsiteThree : aux_in_deterministic_equal_scale_b12_SiteThree CB M s m eta := by
    intro x hx
    have h := (hIII x hx).2
    have henv : (CB * (12 * (3 : ℝ) ^ (s * (m : ℝ) / 8) *
            (3 : ℝ) ^ (s * ((m : ℝ) + 1) / 16)) *
          min 1 (longRatioGradientTail m eta +
            supNormOn (cube d m) (fullShellBlock m eta) +
            SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) + 1))) =
        (2 * CB) * subunitEnvelope s m * subunitDeviation M m eta := by
      unfold subunitEnvelope subunitDeviation
      ring_nf
    rw [henv] at h
    exact h
  -- the response clause at the origin of the translated sample, without cutoff
  have hrespEta : GoodResponse M none m 0 epsilon s eta := by
    have h0 : GoodResponse M (some m) m 0 epsilon s eta :=
      (Section6Covariance.goodResponse_translatePotentialSample
        M (some m) m 0 epsilon s z omega).2 (by simpa only [add_zero] using hresp)
    exact (Section6Cutoff.goodResponse_some_iff_none_of_scale_le_cutoff
      M le_rfl 0 epsilon s eta).1 h0
  have hrespOne : GoodResponse M none m 0 1 s eta :=
    Section6ExcessDecay.goodResponse_mono heps0.le heps1 hrespEta
  have hbase := aux_in_deterministic_equal_scale_b12_paperError_le_base M hs.1 hs.2 eta hrespOne hsiteTwo hsiteThree
  -- truncation of the four slots into the accumulated error
  set E : ℝ := accumulatedError M none m 0 s eta with hEdef
  have hA := aux_in_deterministic_equal_scale_b12_responseSlot_le_accumulatedError M heps0.le hspos.le hrespEta
  have hBs := Section6Holder.goodScaleShellSlot_le_accumulatedError M s m eta
  have hBf := Section6Holder.goodScaleFullSlot_le_two_mul_accumulatedError M s m eta
  have hBg := Section6Holder.goodScaleGradientSlot_le_accumulatedError M s m eta
  have hsum : goodScaleResponseSlot M s m eta + s⁻¹ * M.delta ^ 2 +
        goodScaleShellSlot s m eta + goodScaleFullSlot s m eta +
        goodScaleGradientSlot m eta ≤
      5 * (s⁻¹ * M.delta ^ 2 + epsilon ^ 8 + E) := by
    rw [← hEdef] at hA hBs hBf hBg
    have hD0 : 0 ≤ s⁻¹ * M.delta ^ 2 := mul_nonneg (inv_nonneg.2 hspos.le) (sq_nonneg _)
    have heps8 : 0 ≤ epsilon ^ 8 := pow_nonneg heps0.le 8
    linarith
  have hcarrier : E = accumulatedError M (some m) m z s omega := by
    rw [hEdef, ← Section6Cutoff.accumulatedError_some_eq_none_of_scale_le_cutoff
      M le_rfl 0 s eta, heta,
      Section6Holder.accumulatedError_translatePotentialSample]
  refine hbase.trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    Real.sqrt (aux_in_deterministic_equal_scale_b12_squareConstant CB) *
          (goodScaleResponseSlot M s m eta + s⁻¹ * M.delta ^ 2 +
            goodScaleShellSlot s m eta + goodScaleFullSlot s m eta +
            goodScaleGradientSlot m eta) ≤
        Real.sqrt (aux_in_deterministic_equal_scale_b12_squareConstant CB) *
          (5 * (s⁻¹ * M.delta ^ 2 + epsilon ^ 8 + E)) :=
      mul_le_mul_of_nonneg_left hsum hK0.le
    _ = 5 * Real.sqrt (aux_in_deterministic_equal_scale_b12_squareConstant CB) *
          (s⁻¹ * M.delta ^ 2 + epsilon ^ 8 +
            accumulatedError M (some m) m z s omega) := by
      rw [hcarrier]
      ring



theorem in_deterministic_equal_scale_b12 (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ),
      SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ s * Real.log 3 / 16 →
      ∀ epsilon ∈ Set.Icc (s⁻¹ * M.delta ^ 2) 1,
      ∀ (m : ℕ) (z : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        omega ∈ Paper.product_threshold_good_scale d M 12 (some m) m z epsilon s →
        section6HomogenizationError M s m m omega z ≤
          C * (s⁻¹ * M.delta ^ 2 + epsilon ^ 8 +
            accumulatedError M (some m) m z s omega) := by
  obtain ⟨C, hC, hpaper⟩ := aux_in_deterministic_equal_scale_b12_paper_error d
  refine ⟨C, hC, ?_⟩
  intro M s hs htau epsilon hepsilon m z omega homega
  have hp := hpaper M s hs htau epsilon hepsilon m z omega homega
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hD0 : 0 ≤ s⁻¹ * M.delta ^ 2 := mul_nonneg (inv_nonneg.2 hs0.le) (sq_nonneg _)
  have heps0 : 0 ≤ epsilon := hD0.trans hepsilon.1
  have hE0 := Section6Holder.accumulatedError_nonneg M (some m) s m z omega
  have hRHS0 : 0 ≤ C * (s⁻¹ * M.delta ^ 2 + epsilon ^ 8 +
      accumulatedError M (some m) m z s omega) := by positivity
  unfold section6HomogenizationError
  exact ENNReal.toReal_le_of_le_ofReal hRHS0 hp

/-- Indicator form of `in_deterministic_equal_scale_b12`, in the
shape of the fourth conjunct of `product_threshold_regularities d 12` at
`L = m` (without its `min epsilon` improvement and separate `C * epsilon`
clause, which the equal-scale consumer does not need). -/
theorem aux_in_deterministic_equal_scale_b12_error_indicator (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ),
      SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ s * Real.log 3 / 16 →
      ∀ epsilon ∈ Set.Icc (s⁻¹ * M.delta ^ 2) 1,
      ∀ (m : ℕ) (z : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        indicatorValue (Paper.product_threshold_good_scale d M 12 (some m) m z epsilon s)
            (fun omega' => section6HomogenizationError M s m m omega' z) omega ≤
          C * (s⁻¹ * M.delta ^ 2 + epsilon ^ 8 +
            accumulatedError M (some m) m z s omega) := by
  obtain ⟨C, hC, hbound⟩ := in_deterministic_equal_scale_b12 d
  refine ⟨C, hC, ?_⟩
  intro M s hs htau epsilon hepsilon m z omega
  by_cases hmem : omega ∈ Paper.product_threshold_good_scale d M 12 (some m) m z epsilon s
  · simpa only [indicatorValue, if_pos hmem] using
      hbound M s hs htau epsilon hepsilon m z omega hmem
  · have hs0 : 0 < s :=
      (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
    have hD0 : 0 ≤ s⁻¹ * M.delta ^ 2 := mul_nonneg (inv_nonneg.2 hs0.le) (sq_nonneg _)
    have heps0 : 0 ≤ epsilon := hD0.trans hepsilon.1
    have hE0 := Section6Holder.accumulatedError_nonneg M (some m) s m z omega
    simp only [indicatorValue, if_neg hmem]
    positivity

end Paper



