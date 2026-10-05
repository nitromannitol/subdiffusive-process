module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.CoarseMatrixEntryBounds
public import SubdiffusiveProcess.CoarseGrainingVocab.ACutoffP4Bounds
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ResponseRosenthal

@[expose] public section

/-!
# Step 1: unconditional arbitrary-order moments of the coarse response

The `L^p`/Rosenthal route to the annealed-to-quenched upgrade
( §43-§44) needs, at every
order, a moment bound for

    `cutoffResponseOnCube M L p q R omega = J (cubeDomain R) (a_L(omega)) p q`.

The development owned order `1` unconditionally and order `2` only under the
Section-4 induction hypothesis.  This file supplies **every** order `xi`,
unconditionally, at fixed `L`.

The mechanism is entirely elementary once the pieces are in place:

* `cutoffResponseJ_eq_randomMatrixQuadratics` makes `J` an **exact quadratic
  form** in the two coarse matrices;
* `CoarseMatrixEntryBounds` bounds their entries pathwise by the spatial
  averages of `a_L` and `a_L⁻¹` (the trivial-competitor bound);
* those averages are bounded by `exp (aCutoffCubeLogEnvelope …)` because the
  cutoff is squeezed between `exp (-Z)` and `exp Z` on the covering cube;
* `integrable_exp_mul_aCutoffCubeLogEnvelope` gives exponential moments of that
  envelope **at every positive order**.

At fixed `L` the field is a finite product of `L+1` lognormals, so This is the
expected answer: all moments are finite.  No `DRAFT_SORRY` conclusion is used.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

abbrev Sample' (d : ℕ) := _root_.SubdiffusiveProcess.Model.PotentialSample d

variable {d : ℕ}

/-- A pointwise upper bound on a domain passes to the normalized average. -/
theorem average_le_of_le (U : Ch02.Domain d) {f : Vec d → ℝ} {c : ℝ}
    (hint : IntegrableOn f (U : Set (Vec d)))
    (hle : ∀ x ∈ (U : Set (Vec d)), f x ≤ c) :
    Ch02.average U f ≤ c := by
  have hvol : 0 < (volume (U : Set (Vec d))).toReal :=
    Homogenization.Internal.Ch02.BookCh02.domain_volume_pos U
  have hfin : volume (U : Set (Vec d)) ≠ ⊤ :=
    ((measure_mono subset_closure).trans_lt
      U.isBoundedDomain.isBounded.isCompact_closure.measure_lt_top).ne
  have hfinm : IsFiniteMeasure (volume.restrict (U : Set (Vec d))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_ne le_top hfin
  have hconst : IntegrableOn (fun _ : Vec d => c) (U : Set (Vec d)) :=
    integrable_const c
  have hmono : (∫ x in (U : Set (Vec d)), f x) ≤
      ∫ _x in (U : Set (Vec d)), c :=
    setIntegral_mono_on hint hconst U.measurableSet hle
  rw [setIntegral_const] at hmono
  rw [Ch02.average]
  have hle' : (volume (U : Set (Vec d))).toReal⁻¹ *
      (∫ x in (U : Set (Vec d)), f x) ≤
      (volume (U : Set (Vec d))).toReal⁻¹ *
        ((volume (U : Set (Vec d))).toReal * c) := by
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hvol.le)
    simpa only [smul_eq_mul] using! hmono
  refine hle'.trans (le_of_eq ?_)
  field_simp

/-- The spatial average of the cutoff on a triadic cube is bounded by the
exponential of the logarithmic envelope of a covering origin cube. -/
theorem average_aCutoff_le_exp_envelope
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (R : TriadicCube d)
    (omega : Sample' d) :
    Ch02.average (Ch02.cubeDomain R) (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) ≤
      Real.exp (aCutoffCubeLogEnvelope M L
        (aCutoffCubeOriginCoverScale R) omega) := by
  refine average_le_of_le _ ?_ ?_
  · have hcont := _root_.SubdiffusiveProcess.Model.continuous_aCutoff M L omega
    simpa only [Ch02.cubeDomain_coe, Pi.inv_apply] using!
      (hcont.continuousOn.integrableOn_compact
        (Ch02.cubeDomain R).isBoundedDomain.isBounded.isCompact_closure).mono_set
        subset_closure
  · intro x hx
    refine aCutoff_le_exp_aCutoffCubeLogEnvelope M L _ omega ?_
    exact openCubeSet_subset_aCutoffCubeOriginCover R
      (by simpa only [Ch02.cubeDomain_coe, Pi.inv_apply] using! hx)

/-- The spatial average of the reciprocal cutoff obeys the same bound. -/
theorem average_aCutoffInv_le_exp_envelope
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (R : TriadicCube d)
    (omega : Sample' d) :
    Ch02.average (Ch02.cubeDomain R)
        (fun x => (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x)⁻¹) ≤
      Real.exp (aCutoffCubeLogEnvelope M L
        (aCutoffCubeOriginCoverScale R) omega) := by
  refine average_le_of_le _ ?_ ?_
  · have hcont := (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M L omega).inv₀
      (fun x => (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x).ne')
    simpa only [Ch02.cubeDomain_coe, Pi.inv_apply] using!
      (hcont.continuousOn.integrableOn_compact
        (Ch02.cubeDomain R).isBoundedDomain.isBounded.isCompact_closure).mono_set
        subset_closure
  · intro x hx
    have hmem : x ∈ openCubeSet (originCube d (aCutoffCubeOriginCoverScale R)) :=
      openCubeSet_subset_aCutoffCubeOriginCover R
        (by simpa only [Ch02.cubeDomain_coe, Pi.inv_apply] using! hx)
    have hlow := exp_neg_aCutoffCubeLogEnvelope_le_aCutoff M L _ omega hmem
    have hpos := _root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x
    rw [inv_le_comm₀ hpos (Real.exp_pos _)]
    simpa [Real.exp_neg] using! hlow

/-- Sum of absolute coordinates, the crude vector gauge used below. -/
def absCoordSum (p : Vec d) : ℝ := ∑ i, |p i|

theorem absCoordSum_nonneg (p : Vec d) : 0 ≤ absCoordSum p :=
  Finset.sum_nonneg fun _i _ => abs_nonneg _

/-- A uniform entry bound gives a crude bound on the quadratic form. -/
theorem abs_vecDot_matVecMul_le_of_entries {A : Mat d} {c : ℝ}
    (_hc : 0 ≤ c) (hA : ∀ i j, |A i j| ≤ c) (p : Vec d) :
    |vecDot p (matVecMul A p)| ≤ c * absCoordSum p * absCoordSum p := by
  have hrow : ∀ i : Fin d, |∑ j, A i j * p j| ≤ c * absCoordSum p := by
    intro i
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [absCoordSum, Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro j _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hA i j) (abs_nonneg _)
  calc
    |vecDot p (matVecMul A p)| = |∑ i, p i * (∑ j, A i j * p j)| := rfl
    _ ≤ ∑ i, |p i * (∑ j, A i j * p j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |p i| * (c * absCoordSum p) := by
        refine Finset.sum_le_sum ?_
        intro i _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hrow i) (abs_nonneg _)
    _ = c * absCoordSum p * absCoordSum p := by
        rw [← Finset.sum_mul, absCoordSum]; ring

/-- **The pathwise bound on the coarse response.** -/
theorem abs_cutoffResponseOnCube_le_exp_envelope
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (p q : Vec d)
    (R : TriadicCube d) (omega : Sample' d) :
    |cutoffResponseOnCube M L p q R omega| ≤
      ((1 / 2 : ℝ) * absCoordSum p * absCoordSum p +
          (1 / 2 : ℝ) * absCoordSum q * absCoordSum q) *
          Real.exp (aCutoffCubeLogEnvelope M L
            (aCutoffCubeOriginCoverScale R) omega) +
        |vecDot p q| := by
  set U := Ch02.cubeDomain R with hU
  set Z := Real.exp (aCutoffCubeLogEnvelope M L
    (aCutoffCubeOriginCoverScale R) omega) with hZ
  have hZ0 : 0 ≤ Z := (Real.exp_pos _).le
  have hprimal : |vecDot p (matVecMul (randomAMatrix M L U omega) p)| ≤
      Z * absCoordSum p * absCoordSum p := by
    refine abs_vecDot_matVecMul_le_of_entries hZ0 (fun i j => ?_) p
    exact (abs_randomAMatrix_entry_le_average' M L U omega i j).trans
      (average_aCutoff_le_exp_envelope M L R omega)
  have hdual : |vecDot q (matVecMul ((randomAStarMatrix M L U omega)⁻¹) q)| ≤
      Z * absCoordSum q * absCoordSum q := by
    refine abs_vecDot_matVecMul_le_of_entries hZ0 (fun i j => ?_) q
    exact (abs_randomAStarInv_entry_le_inverse_average' M L U omega i j).trans
      (average_aCutoffInv_le_exp_envelope M L R omega)
  have hJ : cutoffResponseOnCube M L p q R omega =
      (1 / 2 : ℝ) * vecDot p (matVecMul (randomAMatrix M L U omega) p) +
        (1 / 2 : ℝ) * vecDot q
          (matVecMul ((randomAStarMatrix M L U omega)⁻¹) q) - vecDot p q := by
    simpa [cutoffResponseOnCube, aCutoffFamily, aCutoffTriadicData, hU] using!
      cutoffResponseJ_eq_randomMatrixQuadratics M L U p q omega
  rw [hJ, abs_le]
  obtain ⟨hX1, hX2⟩ := abs_le.mp hprimal
  obtain ⟨hY1, hY2⟩ := abs_le.mp hdual
  have hc1 := neg_abs_le (vecDot p q)
  have hc2 := le_abs_self (vecDot p q)
  constructor <;> nlinarith [hX1, hX2, hY1, hY2, hc1, hc2]

/-- **Step 1, delivered.**  The coarse response has a finite moment of **every**
order, unconditionally, at fixed `L`. -/
theorem memLp_cutoffResponseOnCube
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (p q : Vec d)
    (R : TriadicCube d) {xi : ℝ} (hxi : 1 ≤ xi) :
    MemLp (cutoffResponseOnCube M L p q R) (ENNReal.ofReal xi)
      M.P.toMeasure := by
  have hd_ne : d ≠ 0 := Nat.ne_of_gt
    (lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension)
  let : NeZero d := ⟨hd_ne⟩
  have hxi0 : 0 < xi := lt_of_lt_of_le zero_lt_one hxi
  set K : ℝ := (1 / 2 : ℝ) * absCoordSum p * absCoordSum p +
    (1 / 2 : ℝ) * absCoordSum q * absCoordSum q with hK
  set Zf : Sample' d → ℝ := fun omega =>
    Real.exp (aCutoffCubeLogEnvelope M L
      (aCutoffCubeOriginCoverScale R) omega) with hZf
  -- the dominating variable has every moment
  have hexp : MemLp Zf (ENNReal.ofReal xi) M.P.toMeasure := by
    have hint := integrable_exp_mul_aCutoffCubeLogEnvelope M L
      (aCutoffCubeOriginCoverScale R) (q := xi) hxi0
    have hmeas : AEStronglyMeasurable Zf M.P.toMeasure :=
      ((measurable_aCutoffCubeLogEnvelope M L
        (aCutoffCubeOriginCoverScale R)).exp).aestronglyMeasurable
    change eLpNorm Zf (ENNReal.ofReal xi) M.P.toMeasure < ⊤
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by simpa using! (ENNReal.ofReal_pos.mpr hxi0).ne') ENNReal.ofReal_ne_top hmeas]
    have hrw : ∀ omega : Sample' d,
        ‖Zf omega‖ₑ ^ (ENNReal.ofReal xi).toReal =
          ENNReal.ofReal (Real.exp (xi * aCutoffCubeLogEnvelope M L
            (aCutoffCubeOriginCoverScale R) omega)) := by
      intro omega
      rw [ENNReal.toReal_ofReal hxi0.le]
      rw [Real.enorm_eq_ofReal (Real.exp_pos _).le]
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hxi0.le]
      congr 1
      rw [← Real.exp_mul, mul_comm]
    simp only [hrw]
    have := hint.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun omega => (Real.exp_pos _).le)] at this
    exact this
  -- domination
  have hdom : ∀ᵐ omega ∂M.P.toMeasure,
      ‖cutoffResponseOnCube M L p q R omega‖ ≤
        ‖K * Zf omega + |vecDot p q|‖ := by
    filter_upwards with omega
    have h := abs_cutoffResponseOnCube_le_exp_envelope M L p q R omega
    have hnn : 0 ≤ K * Zf omega + |vecDot p q| := by
      have hK0 : 0 ≤ K := by
        rw [hK]
        have := absCoordSum_nonneg p
        have := absCoordSum_nonneg q
        positivity
      have : 0 ≤ Zf omega := (Real.exp_pos _).le
      positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn]
    simpa [hK, hZf] using! h
  have hbig : MemLp (fun omega => K * Zf omega + |vecDot p q|)
      (ENNReal.ofReal xi) M.P.toMeasure := by
    exact (hexp.const_mul K).add (memLp_const _)
  have hmeasJ : AEStronglyMeasurable (cutoffResponseOnCube M L p q R)
      M.P.toMeasure :=
    (measurable_cutoffResponseOnCube M L p q R).aestronglyMeasurable
  exact MemLp.of_le hbig hmeasJ hdom

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge
