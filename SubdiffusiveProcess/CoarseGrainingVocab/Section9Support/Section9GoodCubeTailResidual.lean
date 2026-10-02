import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeTail




set_option autoImplicit false

open Homogenization hiding Vec cubeSet
open Set MeasureTheory ProbabilityTheory MarkovProcess
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

variable {d : ℕ}

/-! ## Transport of the layer-zero conclusion to the site -/

theorem sub_centre_mem_nativeBox_one {n : ℕ} {z : Lattice d} {x : Vec d}
    (hx : x ∈ nativeBox n 1 z) :
    x - goodCubeCentre n z ∈ nativeBox n 1 (0 : Lattice d) := by
  rw [nativeBox, goodCubeCentre_zero_lattice]
  refine mem_centeredAxisCube.mpr fun i => ?_
  have h := mem_centeredAxisCube.mp hx i
  have hrw : (x - goodCubeCentre n z) i - (0 : Vec d) i =
      x i - goodCubeCentre n z i := by simp
  rw [hrw]
  exact h

/-- **The good event carries the log-Lipschitz bound at the site.** -/
theorem aCutoff_le_exp_mul_of_not_goodCubeBad (M : GMCModel d) (n : ℕ) (z : Lattice d)
    (omega : PotentialSample d)
    (hom : omega ∉ coefficientLocalBadEvent M n 1 (goodCubeBad M n) z)
    {x y : Vec d} (hx : x ∈ nativeBox n 1 z) (hy : y ∈ nativeBox n 1 z) :
    aCutoff M n omega x ≤
      Real.exp (logLipschitzThreshold M n * ‖x - y‖) * aCutoff M n omega y := by
  have hnb : restrictedCoefficientObservation (fun w : PotentialSample d => aCutoff M n w)
      (nativeBox n 1 (0 : Lattice d))
      (translatePotentialSequence (goodCubeCentre n z) omega) ∉ goodCubeBad M n := hom
  have hlip := not_not.mp hnb
  have hx' := hlip ⟨x - goodCubeCentre n z, sub_centre_mem_nativeBox_one hx⟩
    ⟨y - goodCubeCentre n z, sub_centre_mem_nativeBox_one hy⟩
  have hrwx : aCutoff M n (translatePotentialSequence (goodCubeCentre n z) omega)
      (x - goodCubeCentre n z) = aCutoff M n omega x := by
    rw [SubdiffusiveProcess.CoarseGrainingVocab.aCutoff_translatePotentialSequence, sub_add_cancel]
  have hrwy : aCutoff M n (translatePotentialSequence (goodCubeCentre n z) omega)
      (y - goodCubeCentre n z) = aCutoff M n omega y := by
    rw [SubdiffusiveProcess.CoarseGrainingVocab.aCutoff_translatePotentialSequence, sub_add_cancel]
  have hnorm : ‖(x - goodCubeCentre n z) - (y - goodCubeCentre n z)‖ = ‖x - y‖ := by
    rw [sub_sub_sub_cancel_right]
  change aCutoff M n (translatePotentialSequence (goodCubeCentre n z) omega)
      (x - goodCubeCentre n z) ≤
    Real.exp (logLipschitzThreshold M n *
        ‖(x - goodCubeCentre n z) - (y - goodCubeCentre n z)‖) *
      aCutoff M n (translatePotentialSequence (goodCubeCentre n z) omega)
        (y - goodCubeCentre n z) at hx'
  rw [hrwx, hrwy, hnorm] at hx'
  exact hx'

theorem norm_sub_le_of_mem_nativeBox_one {n : ℕ} {z : Lattice d} {x y : Vec d}
    (hx : x ∈ nativeBox n 1 z) (hy : y ∈ nativeBox n 1 z) :
    ‖x - y‖ ≤ (3 : ℝ) ^ n := by
  have hx' := mem_centeredAxisCube.mp hx
  have hy' := mem_centeredAxisCube.mp hy
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  have h1 := hx' i
  have h2 := hy' i
  rw [Real.norm_eq_abs]
  have hxy : (x - y) i = (x i - goodCubeCentre n z i) - (y i - goodCubeCentre n z i) := by
    simp
  rw [hxy]
  have hb : |(x i - goodCubeCentre n z i) - (y i - goodCubeCentre n z i)| ≤
      |x i - goodCubeCentre n z i| + |y i - goodCubeCentre n z i| :=
    abs_sub _ _
  have hL : (1 : ℝ) * (3 : ℝ) ^ n / 2 + 1 * (3 : ℝ) ^ n / 2 = (3 : ℝ) ^ n := by ring
  linarith



theorem exists_parentEllipticity_scale_of_not_goodCubeBad (M : GMCModel d) (n : ℕ)
    (z : Lattice d) (omega : PotentialSample d)
    (hom : omega ∉ coefficientLocalBadEvent M n 1 (goodCubeBad M n) z) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ y ∈ nativeBox n 1 z,
      lam ≤ aCutoff M n omega y ∧
        aCutoff M n omega y ≤
          Real.exp (2 * (logLipschitzThreshold M n * (3 : ℝ) ^ n)) * lam := by
  set Theta : ℝ := logLipschitzThreshold M n with hTheta
  have hTnn : 0 ≤ Theta := logLipschitzThreshold_nonneg M n
  set x0 : Vec d := goodCubeCentre n z with hx0
  have hx0mem : x0 ∈ nativeBox n 1 z := by
    refine mem_centeredAxisCube.mpr fun i => ?_
    simp only [hx0, sub_self, abs_zero]
    positivity
  have hstep : ∀ y ∈ nativeBox n 1 z,
      aCutoff M n omega y ≤ Real.exp (Theta * (3 : ℝ) ^ n) * aCutoff M n omega x0 ∧
        aCutoff M n omega x0 ≤ Real.exp (Theta * (3 : ℝ) ^ n) * aCutoff M n omega y := by
    intro y hy
    have h1 := aCutoff_le_exp_mul_of_not_goodCubeBad M n z omega hom hy hx0mem
    have h2 := aCutoff_le_exp_mul_of_not_goodCubeBad M n z omega hom hx0mem hy
    have hn1 : ‖y - x0‖ ≤ (3 : ℝ) ^ n := norm_sub_le_of_mem_nativeBox_one hy hx0mem
    have hn2 : ‖x0 - y‖ ≤ (3 : ℝ) ^ n := norm_sub_le_of_mem_nativeBox_one hx0mem hy
    have hpos1 : 0 < aCutoff M n omega x0 := Real.exp_pos _
    have hpos2 : 0 < aCutoff M n omega y := Real.exp_pos _
    have hm1 : Real.exp (Theta * ‖y - x0‖) ≤ Real.exp (Theta * (3 : ℝ) ^ n) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hn1 hTnn)
    have hm2 : Real.exp (Theta * ‖x0 - y‖) ≤ Real.exp (Theta * (3 : ℝ) ^ n) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hn2 hTnn)
    exact ⟨h1.trans (mul_le_mul_of_nonneg_right hm1 hpos1.le),
      h2.trans (mul_le_mul_of_nonneg_right hm2 hpos2.le)⟩
  refine ⟨Real.exp (-(Theta * (3 : ℝ) ^ n)) * aCutoff M n omega x0,
    mul_pos (Real.exp_pos _) (Real.exp_pos _), ?_⟩
  intro y hy
  obtain ⟨hup, hlow⟩ := hstep y hy
  have hE : (0 : ℝ) < Real.exp (Theta * (3 : ℝ) ^ n) := Real.exp_pos _
  have hEinv : Real.exp (-(Theta * (3 : ℝ) ^ n)) = (Real.exp (Theta * (3 : ℝ) ^ n))⁻¹ := by
    rw [Real.exp_neg]
  constructor
  · rw [hEinv, inv_mul_eq_div, div_le_iff₀ hE]
    calc aCutoff M n omega x0 ≤ Real.exp (Theta * (3 : ℝ) ^ n) * aCutoff M n omega y := hlow
      _ = aCutoff M n omega y * Real.exp (Theta * (3 : ℝ) ^ n) := by ring
  · have h2E : Real.exp (2 * (Theta * (3 : ℝ) ^ n)) * Real.exp (-(Theta * (3 : ℝ) ^ n)) =
        Real.exp (Theta * (3 : ℝ) ^ n) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc aCutoff M n omega y ≤ Real.exp (Theta * (3 : ℝ) ^ n) * aCutoff M n omega x0 := hup
      _ = Real.exp (2 * (Theta * (3 : ℝ) ^ n)) *
            (Real.exp (-(Theta * (3 : ℝ) ^ n)) * aCutoff M n omega x0) := by
          rw [← mul_assoc, h2E]



theorem exists_ellipticity_of_small_diameter_of_not_goodCubeBad (M : GMCModel d)
    (n : ℕ) (z : Lattice d) (omega : PotentialSample d)
    (hom : omega ∉ coefficientLocalBadEvent M n 1 (goodCubeBad M n) z)
    {S : Set (Vec d)} (hS : S ⊆ nativeBox n 1 z) {rho : ℝ}
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ rho) :
    ∀ x ∈ S, ∀ y ∈ S,
      aCutoff M n omega x ≤
        Real.exp (logLipschitzThreshold M n * rho) * aCutoff M n omega y := by
  have hTnn : 0 ≤ logLipschitzThreshold M n := logLipschitzThreshold_nonneg M n
  intro x hx y hy
  have h := aCutoff_le_exp_mul_of_not_goodCubeBad M n z omega hom (hS hx) (hS hy)
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  exact Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (hdiam x hx y hy) hTnn)

/-! ## The corrected residual -/

/-- The six displays that remain after the layer-zero tail is proved, with the
box factor `B = 1` and the concrete bad predicate `goodCubeBad`. -/
structure GoodCubeResidualDisplays (d : ℕ) (c C p0 eps1 : ℝ)
    (Pfam0 : Set (Cube d × Cube d)) (Qfam0 Afam0 : Set (Cube d)) : Prop where
  exit_lower : GoodCubeReferenceDisplay d c eps1 1 Pfam0 Qfam0 Afam0 goodCubeBad
    (fun M n z _ law _ _ _ =>
      ∀ x ∈ middleQuarter (goodCubeCentre n z, (3 : ℝ) ^ n),
        ENNReal.ofReal (c * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M)
            ((3 : ℝ) ^ n)) ≤
          meanExit law (cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n)) x)
  exit_upper : GoodCubeReferenceDisplay d c eps1 1 Pfam0 Qfam0 Afam0 goodCubeBad
    (fun M n z _ law _ _ _ =>
      ∀ x ∈ cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n),
        meanExit law (cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n)) x ≤
          ENNReal.ofReal (C * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M)
            ((3 : ℝ) ^ n)))
  descendant : GoodCubeReferenceDisplay d c eps1 1 Pfam0 Qfam0 Afam0 goodCubeBad
    (fun M _ _ _ law _ Qfam _ =>
      ∀ B' ∈ Qfam, ∀ Bq ∈ Qfam, CompactlyInside B' Bq →
        (∀ x ∈ cubeSet B',
          ENNReal.ofReal (c * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M) Bq.2) ≤
            meanExit law (cubeSet Bq) x) ∧
        (∀ x ∈ cubeSet Bq,
          meanExit law (cubeSet Bq) x ≤
            ENNReal.ofReal (C * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M) Bq.2)))
  mass_quarter : GoodCubeReferenceDisplay d c eps1 1 Pfam0 Qfam0 Afam0 goodCubeBad
    (fun M n z omega _ _ _ _ =>
      ENNReal.ofReal c *
          weightedMeasure (aCutoff M n omega)
            (cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n)) ≤
        weightedMeasure (aCutoff M n omega)
          (middleQuarter (goodCubeCentre n z, (3 : ℝ) ^ n)))
  mass_descendant : GoodCubeReferenceDisplay d c eps1 1 Pfam0 Qfam0 Afam0 goodCubeBad
    (fun M n _ omega _ _ Qfam _ =>
      ∀ B' ∈ Qfam, ∀ Bq ∈ Qfam, CompactlyInside B' Bq →
        ENNReal.ofReal c * weightedMeasure (aCutoff M n omega) (cubeSet Bq) ≤
          weightedMeasure (aCutoff M n omega) (cubeSet B'))
  sobolev : GoodCubeReferenceDisplay d c eps1 1 Pfam0 Qfam0 Afam0 goodCubeBad
    (fun M n _ omega _ _ Qfam _ =>
      ∀ Q ∈ Qfam, ∀ f : H10Function (cubeSet Q),
        lpSq (aCutoff M n omega) (cubeSet Q) p0 f.toH1Function.toFun ≤
          ENNReal.ofReal C *
            weightedMeasure (aCutoff M n omega) (cubeSet Q) ^ (-(1 - 2 / p0)) *
            ENNReal.ofReal (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M) Q.2 *
              energy (aCutoff M n omega) (cubeSet Q) f.toH1Function))



def GoodCubeResidualPackage (d : ℕ) : Prop :=
  ∃ (p0 C0 : ℝ) (_hp0 : 2 < p0) (_hC0 : 2 ≤ C0),
    ∀ (j1 j2 : ℕ), 2 ≤ j1 → 1 ≤ j2 →
      ∀ (grid0 : Finset (Vec d)) (Pfam0 : Set (Cube d × Cube d))
        (Qfam0 Afam0 : Set (Cube d)),
        IsLocalCubeGeometry grid0 j1 j2 ((0 : Vec d), (3 : ℝ) ^ (0 : ℕ))
            Pfam0 Qfam0 Afam0 →
        (∀ Q ∈ Qfam0, cubeSet Q ⊆ cubeSet ((0 : Vec d), (3 : ℝ) ^ (0 : ℕ))) →
        (∀ (n : ℕ) (z : Lattice d),
          IsLocalCubeGeometry grid0 j1 j2
            (goodCubeCentre n z, (3 : ℝ) ^ n) (goodCubeReferencePairs Pfam0 n z)
            (goodCubeReferenceFamily Qfam0 n z) (goodCubeReferenceFamily Afam0 n z)) →
        ∃ c0 : ℝ, 0 < c0 ∧ c0 ≤ 1 ∧
          ∀ c C eps1 : ℝ, 0 < c → c ≤ c0 → C0 ≤ C → 0 < eps1 →
            GoodCubeResidualDisplays d c C p0 eps1 Pfam0 Qfam0 Afam0

/-- **The six-display residual implies the seven-display analytic package.**
The `.tail` display is supplied by `goodCubeBad_tail`. -/
theorem goodCubeAnalyticPackage_of_residualPackage {d : ℕ}
    (h : GoodCubeResidualPackage d) : GoodCubeAnalyticPackage d := by
  obtain ⟨p0, C0, hp0, hC0, h⟩ := h
  refine ⟨p0, 1, C0, hp0, one_pos, lt_of_lt_of_le two_pos hC0, goodCubeBad, ?_⟩
  intro j1 j2 hj1 hj2 grid0 Pfam0 Qfam0 Afam0 hg0 hin hg
  obtain ⟨c0, hc0, hc01, hdisp⟩ := h j1 j2 hj1 hj2 grid0 Pfam0 Qfam0 Afam0 hg0 hin hg
  refine ⟨c0, hc0, ?_⟩
  intro c C eps1 hc hcc0 hCC0 heps1
  obtain ⟨hxl, hxu, hdesc, hmq, hmd, hsob⟩ := hdisp c C eps1 hc hcc0 hCC0 heps1
  exact ⟨fun M _ n z => goodCubeBad_tail M hc (hcc0.trans hc01) (hC0.trans hCC0) n z,
    hxl, hxu, hdesc, hmq, hmd, hsob⟩

/-! ## The uniform-in-scale statement the P-363 residual forces -/

/-- The uniform-in-`n` ellipticity tail: for a **fixed** ratio `K`, the
probability that `a_n` fails the two-sided bound with ratio `K` on the whole
native box of side `B·3^n` is bounded by `C₀e^{-c₀²δ^{-2}|log δ|^{-2}}`, with
constants independent of `n`.  This is the falsifiable content of the
`bad ⊇ badEllipticity` clause of `GoodCubeDisplayPackage`. -/
def UniformParentEllipticityTail (d : ℕ) : Prop :=
  ∃ B K C0 c0 : ℝ, 1 ≤ B ∧ 0 < K ∧ 0 < C0 ∧ 0 < c0 ∧
    ∀ M : GMCModel d, M.delta ≤ c0 → ∀ (n : ℕ) (z : Lattice d),
      M.P.toMeasure (coefficientLocalBadEvent M n B (badEllipticity d n B K) z) ≤
        ENNReal.ofReal
          (C0 * Real.exp (-(c0 * (c0 / (M.delta ^ 2 * Real.log M.delta ^ 2)))))

/-- **The P-363 residual forces the uniform-in-scale ellipticity tail.**  Every
witness of `GoodCubeDisplayPackage d` produces one, because its `.tail` display
is uniform in `n` while its `bad` predicate contains `badEllipticity d n B K`
for a ratio `K` fixed before `n`. -/
theorem uniformParentEllipticityTail_of_displayPackage {d : ℕ}
    (h : GoodCubeDisplayPackage d) : UniformParentEllipticityTail d := by
  obtain ⟨p0, B, C0, K, hp0, hB, hC0, hK, bad, hsub, h⟩ := h
  obtain ⟨grid0, Pfam0, Qfam0, Afam0, hg0, hin, hg⟩ :=
    exists_goodCubeReferenceTemplate d (le_refl 2) (le_refl 1)
  obtain ⟨c0, hc0, hdisp⟩ := h 2 1 (le_refl 2) (le_refl 1) grid0 Pfam0 Qfam0 Afam0 hg0 hin hg
  refine ⟨B, K, C0, c0, hB, hK, hC0, hc0, ?_⟩
  intro M hdelta n z
  have htail := (hdisp c0 C0 1 hc0 (le_refl c0) (le_refl C0) one_pos).tail M hdelta n z
  refine le_trans (measure_mono ?_) htail
  exact Set.preimage_mono (Set.preimage_mono (hsub M n))

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
