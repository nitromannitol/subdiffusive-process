import SubdiffusiveProcess.Analysis.DeterministicAnchorTransport
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FlatComparatorForcing
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FlatComparatorTransport




namespace SubdiffusiveProcess.InteriorComparisonEngine

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec TriadicCube Mat
open Homogenization.Book
open Homogenization.Book.Ch03 Homogenization.Book.Ch03.ABK26 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport
open scoped ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

variable {d : ℕ} [NeZero d]




omit [NeZero d] in
/-- Twin of
`SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.isForcedEquation_aCutoff_untranslate`,
generic in an arbitrary `ScalarTriadicCoeffData`. -/
theorem aux_icc_isForcedEquation_scalarData_untranslate
    (Q : TriadicCube d) (y : Vec d)
    {a : Vec d → ℝ} (dataY : ScalarTriadicCoeffData (fun q => a (q + y)))
    {u : H1Function (translateSet y (openCubeSet Q))} {g : Vec d → Vec d}
    (h : IsDivFormWeakSolutionOn a (translateSet y (openCubeSet Q)) u g) :
    Ch03.ABK26.IsForcedEquation Q (dataY.toTriadicCoeffFamily.coeffOn Q)
      (H1Function.untranslate y u) (fun x => g (x + y)) := by
  have htr := isDivFormWeakSolutionOn_untranslate y h
  intro phi
  have hphi := htr phi
  simpa [ScalarTriadicCoeffData.toTriadicCoeffFamily, ScalarCoeffOnData.toCoeffOn,
    scalarCoeffField, matVecMul_scalarMatrix] using hphi

/-! ### Error transport: off-grid stability closes the loop back onto the
translated (`y`-anchored) coefficient data. -/

omit [NeZero d] in
/-- Translating both the domain and the field by the same vector preserves
exact (non-a.e.) ellipticity. -/
theorem aux_icc_isEllipticFieldOn_translateCoeffField_of_isEllipticFieldOn
    {lam Lam : ℝ} {w : Vec d} {S : Set (Vec d)} {b : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (translateSet w S) b) :
    IsEllipticFieldOn lam Lam S (translateCoeffField w b) := by
  classical
  obtain ⟨hmeas, hpt⟩ := hEll
  constructor
  · have hmeas' : Measurable
        (fun x : Vec d => fun i j =>
          if x + w ∈ translateSet w S then b (x + w) i j else 0) :=
      hmeas.comp (measurable_add_const w)
    have heq : (fun x : Vec d => fun i j =>
          if x ∈ S then translateCoeffField w b x i j else 0) =
        fun x : Vec d => fun i j =>
          if x + w ∈ translateSet w S then b (x + w) i j else 0 := by
      funext x i j
      have hfun : (fun i => x i + w i) = x + w := rfl
      by_cases hx : x ∈ S
      · have hxw : x + w ∈ translateSet w S := by
          rw [mem_translateSet_iff_sub_mem]
          simpa using hx
        simp only [translateCoeffField, hfun, if_pos hx, if_pos hxw]
      · have hxw : x + w ∉ translateSet w S := by
          rw [mem_translateSet_iff_sub_mem]
          simpa using hx
        simp only [translateCoeffField, hfun, if_neg hx, if_neg hxw]
    rw [heq]
    exact hmeas'
  · intro x hx
    have hxw : x + w ∈ translateSet w S := by
      rw [mem_translateSet_iff_sub_mem]
      simpa using hx
    have hthis := hpt (x + w) hxw
    have hfun : (fun i => x i + w i) = x + w := rfl
    simpa only [translateCoeffField, hfun] using hthis

omit [NeZero d] in


theorem aux_icc_translatedRep_ae_eq_scalarY
    (n : ℕ) (a : Vec d → ℝ) (z y : Vec d)
    (data : ScalarTriadicCoeffData (fun q => a (q + z)))
    (hcontain : translateSet (y - z) (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
      cubeSet (originCube d ((n : ℤ) + 2))) :
    translateCoeffField (y - z)
        (Internal.Ch02.BookCh02.pointwiseCoeffField
          (Ch02.cubeDomain (originCube d ((n : ℤ) + 2)))
          ((data.onCube (originCube d ((n : ℤ) + 2))).toCoeffOn)) =ᵐ[
        volume.restrict (cubeSet (originCube d ((n : ℤ) - 2)))]
      scalarCoeffField (fun q => a (q + y)) := by
  set K : TriadicCube d := originCube d ((n : ℤ) + 2) with hKdef
  set P : TriadicCube d := originCube d ((n : ℤ) - 2) with hPdef
  have hWeq : translateSet y (cubeSet P) =
      translateSet z (translateSet (y - z) (cubeSet P)) := by
    rw [translateSet_translateSet]
    congr 1
    abel
  have hmono : translateSet (y - z) (cubeSet P) ⊆ cubeSet K → translateSet z
      (translateSet (y - z) (cubeSet P)) ⊆ translateSet z (cubeSet K) := by
    intro h q hq
    rw [mem_translateSet_iff_sub_mem] at hq ⊢
    exact h hq
  have hWsub : translateSet y (cubeSet P) ⊆ translateSet z (cubeSet K) := by
    rw [hWeq]
    exact hmono hcontain
  have hroot := SubdiffusiveProcess.DeterministicAnchorTransport.rootRep_translated_ae
    K z a data (translateSet y (cubeSet P)) hWsub
  have hpull := (measurePreserving_addRight_restrict_translateSet y (cubeSet P)
    (d := d)).quasiMeasurePreserving.ae_eq hroot
  have hfunL : ∀ x : Vec d, (translateCoeffField (-z)
      (Internal.Ch02.BookCh02.pointwiseCoeffField (Ch02.cubeDomain K)
        ((data.onCube K).toCoeffOn))) (x + y) =
      translateCoeffField (y - z)
        (Internal.Ch02.BookCh02.pointwiseCoeffField (Ch02.cubeDomain K)
          ((data.onCube K).toCoeffOn)) x := by
    intro x
    show Internal.Ch02.BookCh02.pointwiseCoeffField (Ch02.cubeDomain K)
        ((data.onCube K).toCoeffOn) (fun i => (x i + y i) + (-z i)) =
      Internal.Ch02.BookCh02.pointwiseCoeffField (Ch02.cubeDomain K)
        ((data.onCube K).toCoeffOn) (fun i => x i + (y i - z i))
    congr 1
    funext i
    ring
  have hfunR : ∀ x : Vec d, scalarCoeffField a (x + y) =
      scalarCoeffField (fun q => a (q + y)) x := by
    intro x
    rfl
  filter_upwards [hpull] with x hx
  rw [← hfunL x, ← hfunR x]
  exact hx

/-- Twin of `offGridShellMax_eq_translate`, with `hg` restricted to the
descendants actually read at this shell (the only place the original proof
uses it). -/
theorem aux_icc_offGridShellMax_eq_translate_desc
    (w : Vec d) (P : TriadicCube d) (k : ℤ) (A : Ch02.TriadicCoeffFamily d)
    (g : CoeffField d)
    (hg : ∀ R ∈ descendantsAtScale P k, (A.coeffOn R).toCoeffField =
      translateCoeffField w g) (a0 : Mat d) :
    offGridShellMax w P k g a0 =
      Ch02.maxDescendantNormalizedBlockResponseAtScale P k A a0 := by
  rw [offGridShellMax, Ch02.maxDescendantNormalizedBlockResponseAtScale]
  refine Ch02.finsetSupReal_congr (descendantsAtScale P k) ?_
  intro R hR
  exact offGridBlockResponseMax_eq_translate w R A g (hg R hR) a0

/-- Twin of `offGridErrorFunctional_eq_homogenizationErrorOnCube_translate`,
with `hg` restricted to descendants of `P` (the only cubes the shell series
ever reads). -/
theorem aux_icc_offGridErrorFunctional_eq_homogenizationErrorOnCube_translate_desc
    (w : Vec d) (P : TriadicCube d) {t : ℝ} (ht : 0 < t)
    (A : Ch02.TriadicCoeffFamily d) (g : CoeffField d)
    (hg : ∀ (k : ℤ) (S : TriadicCube d), S ∈ descendantsAtScale P k →
      (A.coeffOn S).toCoeffField = translateCoeffField w g) (a0 : Mat d) :
    offGridErrorFunctional w P t g a0 =
      Ch02.HomogenizationErrorOnCube P t .infinity (.finite 2) A a0 := by
  have hshell : ∀ l : ℕ, offGridShellMax w P (P.scale - (l : ℤ)) g a0 =
      Ch02.maxDescendantNormalizedBlockResponseAtScale P (P.scale - (l : ℤ)) A a0 :=
    fun l => aux_icc_offGridShellMax_eq_translate_desc w P (P.scale - (l : ℤ)) A g
      (hg (P.scale - (l : ℤ))) a0
  have hsum : (∑' l : ℕ, Ch02.geometricWeight t 2 l *
      offGridShellMax w P (P.scale - (l : ℤ)) g a0) =
      Ch02.HomogenizationErrorOnCube P t .infinity (.finite 2) A a0 ^ 2 := by
    rw [Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum P ht A a0]
    exact tsum_congr fun l => by rw [hshell l]
  rw [offGridErrorFunctional, hsum]
  exact Real.sqrt_sq
    (homogenizationErrorOnCube_infinity_two_nonneg P A a0 ht)

/-- Package a globally measurable, exactly-elliptic-on-`openCubeSet Q'` field
as a public `Ch02.CoeffOn`.  Twin of
`Internal.Ch02.BookCh02.pointwiseCoeffOn`'s field-construction technique,
starting from an already exact (not merely pointwise-good) field. -/
noncomputable def aux_icc_mkCoeffOn (Q' : TriadicCube d) {lamK LamK : ℝ}
    (field : CoeffField d)
    (hlam_pos : 0 < lamK) (hlam_le : lamK ≤ LamK)
    (hEllOn : IsEllipticFieldOn lamK LamK (openCubeSet Q') field) :
    Ch02.CoeffOn (Ch02.cubeDomain Q') where
  toCoeffField := field
  lam := lamK
  Lam := LamK
  lam_pos := hlam_pos
  lam_le_Lam := hlam_le
  aeStronglyMeasurable := by
    intro i j
    have hite : Measurable fun x : Vec d =>
        if x ∈ (Ch02.cubeDomain Q' : Set (Vec d)) then field x i j else 0 := by
      rw [Ch02.cubeDomain_coe]
      exact measurable_pi_iff.1 (measurable_pi_iff.1 hEllOn.1 i) j
    have hentry : Measurable fun x : Vec d =>
        restrictCoeffField (Ch02.cubeDomain Q' : Set (Vec d)) field x i j := by
      have heq : (fun x : Vec d =>
            restrictCoeffField (Ch02.cubeDomain Q' : Set (Vec d)) field x i j) =
          fun x : Vec d =>
            if x ∈ (Ch02.cubeDomain Q' : Set (Vec d)) then field x i j else 0 := by
        funext x
        simp only [restrictCoeffField]
        split_ifs <;> rfl
      rw [heq]
      exact hite
    exact hentry.aestronglyMeasurable
  aeElliptic := by
    filter_upwards [MeasureTheory.ae_restrict_mem (Ch02.cubeDomain Q').measurableSet]
      with x hxU
    exact hEllOn.2 x (by rwa [Ch02.cubeDomain_coe] at hxU)

/-- The dite-patched coefficient family: `bshift` (intended to be
`translateCoeffField (y - z) b`) on cubes contained in the replacement window
`P`, and `dataY`'s own family elsewhere.  Only the values on descendants of
`P` are ever read by `Ch02.HomogenizationErrorOnCube P`, and there the two
branches coincide with `dataY`'s field a.e. (`hbae`). -/
noncomputable def aux_icc_patchedFamily (P : TriadicCube d) {lamK LamK : ℝ}
    (bshift : CoeffField d)
    (hlam_pos : 0 < lamK) (hlam_le : lamK ≤ LamK)
    (hEllP : IsEllipticFieldOn lamK LamK (openCubeSet P) bshift)
    {a : Vec d → ℝ} {y : Vec d} (dataY : ScalarTriadicCoeffData (fun q => a (q + y)))
    (hbae : bshift =ᵐ[volume.restrict (cubeSet P)] scalarCoeffField (fun q => a (q + y))) :
    Ch02.TriadicCoeffFamily d where
  coeffOn Q' :=
    if h : openCubeSet Q' ⊆ openCubeSet P then
      aux_icc_mkCoeffOn Q' bshift hlam_pos hlam_le
        (hEllP.mono (measurableSet_openCubeSet Q') h)
    else
      dataY.toTriadicCoeffFamily.coeffOn Q'
  restrictsTo_of_subset := by
    intro Q R hRQ
    by_cases hQ : openCubeSet Q ⊆ openCubeSet P <;>
      by_cases hR : openCubeSet R ⊆ openCubeSet P
    · simp only [dif_pos hQ, dif_pos hR, Ch02.CoeffOn.RestrictsTo, aux_icc_mkCoeffOn]
      exact Filter.EventuallyEq.rfl
    · exact absurd (hRQ.trans hQ) hR
    · -- hQ false, hR true: cross case, both a.e. equal to `scalarCoeffField (a ∘ (+y))`
      simp only [dif_neg hQ, dif_pos hR, Ch02.CoeffOn.RestrictsTo, aux_icc_mkCoeffOn]
      show bshift =ᵐ[volumeMeasureOn (Ch02.cubeDomain R : Set (Vec d))]
        (dataY.toTriadicCoeffFamily.coeffOn Q).toCoeffField
      have hQeq : (dataY.toTriadicCoeffFamily.coeffOn Q).toCoeffField =
          scalarCoeffField (fun q => a (q + y)) := rfl
      rw [hQeq, Ch02.cubeDomain_coe, volumeMeasureOn]
      exact MeasureTheory.ae_restrict_of_ae_restrict_of_subset
        (hR.trans (openCubeSet_subset_cubeSet P)) hbae
    · simp only [dif_neg hQ, dif_neg hR, Ch02.CoeffOn.RestrictsTo]
      exact Filter.EventuallyEq.rfl

omit [NeZero d] in
/-- The patched family's field on any cube contained in `P` is the true
`bshift` value, on the nose. -/
theorem aux_icc_patchedFamily_coeffOn_of_subset
    (P : TriadicCube d) {lamK LamK : ℝ}
    {bshift : CoeffField d}
    {hlam_pos : 0 < lamK} {hlam_le : lamK ≤ LamK}
    {hEllP : IsEllipticFieldOn lamK LamK (openCubeSet P) bshift}
    {a : Vec d → ℝ} {y : Vec d} {dataY : ScalarTriadicCoeffData (fun q => a (q + y))}
    {hbae : bshift =ᵐ[volume.restrict (cubeSet P)] scalarCoeffField (fun q => a (q + y))}
    {Q' : TriadicCube d} (h : openCubeSet Q' ⊆ openCubeSet P) :
    ((aux_icc_patchedFamily P bshift hlam_pos hlam_le hEllP dataY hbae).coeffOn Q').toCoeffField =
      bshift := by
  simp only [aux_icc_patchedFamily, dif_pos h, aux_icc_mkCoeffOn]

/-- **The error transport.**  The paper's anchored homogenization error
(stated for `data`, anchored at `z`, on the parent cube) controls the ordinary
Chapter 2 error of the translated family `dataY` (anchored at `y`) on the
smaller replacement cube `P = 𝔠_{n-2}`. -/
theorem aux_icc_errorTransport
    (n : ℕ) (s Cerr a0 : ℝ) (a : Vec d → ℝ) (z y : Vec d)
    (data : ScalarTriadicCoeffData (fun q => a (q + z)))
    (dataY : ScalarTriadicCoeffData (fun q => a (q + y)))
    (hs : 0 < s) (hs1 : s ≤ 1) (hCerr : 0 ≤ Cerr) (ha0 : 0 < a0)
    (herr : paperHomogenizationError (originCube d ((n : ℤ) + 2)) ((n : ℤ) + 2) (s / 8)
      Ch02.MultiscaleExponent.infinity (Ch02.MultiscaleExponent.finite 2)
      data.toTriadicCoeffFamily a0 ≤ ENNReal.ofReal Cerr)
    (hcontain : translateSet (y - z) (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
      cubeSet (originCube d ((n : ℤ) + 2))) :
    Ch02.HomogenizationErrorOnCube (originCube d ((n : ℤ) - 2)) (s / 6)
        Ch02.MultiscaleExponent.infinity (Ch02.MultiscaleExponent.finite 2)
        dataY.toTriadicCoeffFamily (scalarMatrix a0) ≤
      Real.sqrt (192 * (d : ℝ)) * ((3 : ℝ) ^ (s / 2) * Cerr) := by
  set K : TriadicCube d := originCube d ((n : ℤ) + 2) with hKdef
  set P : TriadicCube d := originCube d ((n : ℤ) - 2) with hPdef
  set c : Ch02.CoeffOn (Ch02.cubeDomain K) := (data.onCube K).toCoeffOn with hcdef
  set b : CoeffField d :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (Ch02.cubeDomain K) c with hbdef
  have hWmeas : MeasurableSet (translateSet (y - z) (cubeSet P)) := by
    rw [← preimage_subRight_eq_translateSet]
    exact (measurableSet_cubeSet P).preimage (measurable_id.sub measurable_const)
  have hEllb : IsEllipticFieldOn c.lam c.Lam (translateSet (y - z) (cubeSet P)) b :=
    SubdiffusiveProcess.DeterministicAnchorTransport.rootRep_local_elliptic
      K c (translateSet (y - z) (cubeSet P)) hWmeas hcontain
  set R : Ch02.TriadicCoeffFamily d :=
    Ch03.ABK26.rootPointwiseCoeffFamily K (data.toTriadicCoeffFamily.coeffOn K) with hRdef
  have hroot := SubdiffusiveProcess.DeterministicAnchorTransport.anchored_error_bound
    d n s Cerr a0 (fun q => a (q + z)) data hs hCerr ha0 herr
  have hrootEq : Ch02.HomogenizationErrorOnCube K (s / 8) Ch02.MultiscaleExponent.infinity
      (Ch02.MultiscaleExponent.finite 2) R (scalarMatrix a0) =
      Ch02.HomogenizationErrorOnCube K (s / 8) Ch02.MultiscaleExponent.infinity
        (Ch02.MultiscaleExponent.finite 2) data.toTriadicCoeffFamily (scalarMatrix a0) :=
    SubdiffusiveProcess.DeterministicAnchorTransport.root_error_eq K
      data.toTriadicCoeffFamily (s / 8) (scalarMatrix a0)
  have herror : Ch02.HomogenizationErrorOnCube K (s / 8) Ch02.MultiscaleExponent.infinity
      (Ch02.MultiscaleExponent.finite 2) R (scalarMatrix a0) ≤ Cerr := by
    rw [hrootEq]; exact hroot
  have hcap := SubdiffusiveProcess.DeterministicAnchorTransport.offgrid_error_cap
    (P := P) (K := K) s Cerr R (scalarMatrix a0) (y - z) b
    hs hs1 (fun Q => rfl) hEllb hcontain herror
  have hdepth : ((((K.scale - P.scale).toNat : ℕ) : ℝ)) = 4 := by
    simp [K, P, Homogenization.originCube]
  have hbound : offGridErrorFunctional (y - z) P (s / 6) b (scalarMatrix a0) ≤
      Real.sqrt (192 * (d : ℝ)) * ((3 : ℝ) ^ (s / 2) * Cerr) := by
    simpa [hdepth, Real.sqrt_mul, show s / 8 * 4 = s / 2 by ring] using hcap
  have hEllTranslated : IsEllipticFieldOn c.lam c.Lam
      (openCubeSet P) (translateCoeffField (y - z) b) :=
    (aux_icc_isEllipticFieldOn_translateCoeffField_of_isEllipticFieldOn hEllb).mono
      (measurableSet_openCubeSet P) (openCubeSet_subset_cubeSet P)
  have hbae : translateCoeffField (y - z) b =ᵐ[volume.restrict (cubeSet P)]
      scalarCoeffField (fun q => a (q + y)) :=
    aux_icc_translatedRep_ae_eq_scalarY n a z y data hcontain
  set A5 : Ch02.TriadicCoeffFamily d :=
    aux_icc_patchedFamily P (translateCoeffField (y - z) b)
      (data.onCube K).lam_pos (data.onCube K).lam_le_Lam hEllTranslated dataY hbae
    with hA5def
  have hgA5 : ∀ (k : ℤ) (S : TriadicCube d), S ∈ descendantsAtScale P k →
      (A5.coeffOn S).toCoeffField = translateCoeffField (y - z) b := by
    intro k S hS
    have hSsub : openCubeSet S ⊆ openCubeSet P :=
      openCubeSet_subset_of_mem_descendantsAtScale
        (descendant_scale_le_of_mem_descendantsAtScale hS) hS
    rw [hA5def]
    exact aux_icc_patchedFamily_coeffOn_of_subset (P := P) (dataY := dataY) (hbae := hbae) hSsub
  have hbridge := aux_icc_offGridErrorFunctional_eq_homogenizationErrorOnCube_translate_desc
    (y - z) P (show (0 : ℝ) < s / 6 by linarith) A5 b hgA5 (scalarMatrix a0)
  have hAEEq : Ch02.HomogenizationErrorOnCube P (s / 6) Ch02.MultiscaleExponent.infinity
      (Ch02.MultiscaleExponent.finite 2) A5 (scalarMatrix a0) =
      Ch02.HomogenizationErrorOnCube P (s / 6) Ch02.MultiscaleExponent.infinity
        (Ch02.MultiscaleExponent.finite 2) dataY.toTriadicCoeffFamily (scalarMatrix a0) := by
    apply homogenizationErrorOnCube_eq_of_descendantAEEq
    intro k S hS
    have hSsub : openCubeSet S ⊆ openCubeSet P :=
      openCubeSet_subset_of_mem_descendantsAtScale
        (descendant_scale_le_of_mem_descendantsAtScale hS) hS
    show (A5.coeffOn S).toCoeffField =ᵐ[volumeMeasureOn (Ch02.cubeDomain S : Set (Vec d))]
      (dataY.toTriadicCoeffFamily.coeffOn S).toCoeffField
    have hfield := hgA5 k S hS
    have hQeq : (dataY.toTriadicCoeffFamily.coeffOn S).toCoeffField =
        scalarCoeffField (fun q => a (q + y)) := rfl
    rw [show A5.coeffOn S = _ from rfl, hfield, hQeq, Ch02.cubeDomain_coe, volumeMeasureOn]
    exact MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      (hSsub.trans (openCubeSet_subset_cubeSet P)) hbae
  rw [← hAEEq, ← hbridge]
  exact hbound

end

end SubdiffusiveProcess.InteriorComparisonEngine
