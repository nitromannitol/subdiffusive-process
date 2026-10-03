module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeCalibration

@[expose] public section




set_option autoImplicit false

open Homogenization hiding Vec cubeSet
open Set MeasureTheory ProbabilityTheory MarkovProcess
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

variable {d : ℕ}

/-! ## Weighted mass against Lebesgue measure -/

theorem measurableSet_cubeSet (Q : Cube d) : MeasurableSet (cubeSet Q) :=
  measurableSet_axisCube _ _

theorem volume_cubeSet {Q : Cube d} (hQ : 0 ≤ Q.2) :
    volume (cubeSet Q) = ENNReal.ofReal (Q.2 ^ d) := by
  have hne : volume (cubeSet Q) ≠ ⊤ := volume_axisCube_ne_top _ _
  conv_lhs => rw [← ENNReal.ofReal_toReal hne]
  exact congrArg ENNReal.ofReal (SubdiffusiveProcess.Section9.volume_centeredAxisCube_toReal Q.1 hQ)

theorem weightedMeasure_le_of_le (a : Vec d → ℝ) {S : Set (Vec d)} (hS : MeasurableSet S)
    {Lam : ℝ} (h : ∀ x ∈ S, a x ≤ Lam) :
    weightedMeasure a S ≤ ENNReal.ofReal Lam * volume S := by
  rw [weightedMeasure, withDensity_apply _ hS]
  calc ∫⁻ x in S, ENNReal.ofReal (a x)
      ≤ ∫⁻ _x in S, ENNReal.ofReal Lam := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem hS] with x hx
        exact ENNReal.ofReal_le_ofReal (h x hx)
    _ = ENNReal.ofReal Lam * volume S := by rw [setLIntegral_const]

theorem le_weightedMeasure_of_le (a : Vec d → ℝ) {S : Set (Vec d)} (hS : MeasurableSet S)
    {lam : ℝ} (h : ∀ x ∈ S, lam ≤ a x) :
    ENNReal.ofReal lam * volume S ≤ weightedMeasure a S := by
  rw [weightedMeasure, withDensity_apply _ hS]
  calc ENNReal.ofReal lam * volume S
      = ∫⁻ _x in S, ENNReal.ofReal lam := by rw [setLIntegral_const]
    _ ≤ ∫⁻ x in S, ENNReal.ofReal (a x) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem hS] with x hx
        exact ENNReal.ofReal_le_ofReal (h x hx)



theorem mass_ratio_of_ellipticity (a : Vec d → ℝ) {lam Lam : ℝ}
    (hlam : 0 ≤ lam) (hLam : 0 ≤ Lam) {S : Set (Vec d)} {Q R : Cube d}
    (hQ : 0 ≤ Q.2) (hR : 0 ≤ R.2) (hQS : cubeSet Q ⊆ S) (hRS : cubeSet R ⊆ S)
    (hlo : ∀ x ∈ S, lam ≤ a x) (hhi : ∀ x ∈ S, a x ≤ Lam)
    {cc : ℝ} (hcc : 0 ≤ cc) (hgeo : cc * (Lam * R.2 ^ d) ≤ lam * Q.2 ^ d) :
    ENNReal.ofReal cc * weightedMeasure a (cubeSet R) ≤ weightedMeasure a (cubeSet Q) := by
  have hup : weightedMeasure a (cubeSet R) ≤ ENNReal.ofReal (Lam * R.2 ^ d) := by
    have h := weightedMeasure_le_of_le a (measurableSet_cubeSet R)
      (fun x hx => hhi x (hRS hx))
    rw [volume_cubeSet hR, ← ENNReal.ofReal_mul hLam] at h
    exact h
  have hlow : ENNReal.ofReal (lam * Q.2 ^ d) ≤ weightedMeasure a (cubeSet Q) := by
    have h := le_weightedMeasure_of_le a (measurableSet_cubeSet Q)
      (fun x hx => hlo x (hQS hx))
    rw [volume_cubeSet hQ, ← ENNReal.ofReal_mul hlam] at h
    exact h
  calc ENNReal.ofReal cc * weightedMeasure a (cubeSet R)
      ≤ ENNReal.ofReal cc * ENNReal.ofReal (Lam * R.2 ^ d) := by
        gcongr
    _ = ENNReal.ofReal (cc * (Lam * R.2 ^ d)) := (ENNReal.ofReal_mul hcc).symm
    _ ≤ ENNReal.ofReal (lam * Q.2 ^ d) := ENNReal.ofReal_le_ofReal hgeo
    _ ≤ weightedMeasure a (cubeSet Q) := hlow

/-! ## The geometric mass constant of a fixed finite family -/



theorem exists_side_ratio (Qfam0 : Set (Cube d)) (hfin : Qfam0.Finite)
    (hne : Qfam0.Nonempty) (hpos : ∀ Q ∈ Qfam0, 0 < Q.2) :
    ∃ q : ℝ, 0 < q ∧ ∀ Q ∈ Qfam0, ∀ R ∈ Qfam0, q * R.2 ^ d ≤ Q.2 ^ d := by
  obtain ⟨Qm, hQm, hmin⟩ := Set.exists_min_image Qfam0 (fun Q => Q.2) hfin hne
  obtain ⟨QM, hQM, hmax⟩ := Set.exists_max_image Qfam0 (fun Q => Q.2) hfin hne
  have hminpos : 0 < Qm.2 := hpos Qm hQm
  have hmaxpos : 0 < QM.2 := hpos QM hQM
  refine ⟨(Qm.2 / QM.2) ^ d, by positivity, ?_⟩
  intro Q hQ R hR
  have hRle : R.2 ≤ QM.2 := hmax R hR
  have hQge : Qm.2 ≤ Q.2 := hmin Q hQ
  have hstep : (Qm.2 / QM.2) ^ d * R.2 ^ d ≤ (Qm.2 / QM.2) ^ d * QM.2 ^ d := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact pow_le_pow_left₀ (hpos R hR).le hRle d
  have hcancel : (Qm.2 / QM.2) ^ d * QM.2 ^ d = Qm.2 ^ d := by
    rw [← mul_pow, div_mul_cancel₀ _ (ne_of_gt hmaxpos)]
  have hfinal : Qm.2 ^ d ≤ Q.2 ^ d := pow_le_pow_left₀ hminpos.le hQge d
  calc (Qm.2 / QM.2) ^ d * R.2 ^ d ≤ (Qm.2 / QM.2) ^ d * QM.2 ^ d := hstep
    _ = Qm.2 ^ d := hcancel
    _ ≤ Q.2 ^ d := hfinal

/-! ## The ellipticity property of the good event -/



def GoodCubeParentEllipticity (d : ℕ) (c eps1 B K : ℝ)
    (bad : (M : GMCModel d) → (n : ℕ) → Set (nativeBox n B (0 : Lattice d) → ℝ)) : Prop :=
  ∀ M : GMCModel d, M.delta ≤ c → ∀ (n : ℕ) (z : Lattice d),
    ∀ omega ∈ goodCubeEvent
      (goodCubeEventField n B eps1 (coefficientLocalBadEvent M n B (bad M n))) z,
      ∃ lam : ℝ, 0 < lam ∧
        ∀ x ∈ cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n),
          lam ≤ aCutoff M n omega x ∧ aCutoff M n omega x ≤ K * lam

/-- Every cube of the transported family lies in the native cube. -/
theorem cubeSet_transported_subset {Qfam0 : Set (Cube d)}
    (hinside : ∀ Q ∈ Qfam0, cubeSet Q ⊆ cubeSet ((0 : Vec d), (3 : ℝ) ^ (0 : ℕ)))
    (n : ℕ) (z : Lattice d) :
    ∀ Q ∈ goodCubeReferenceFamily Qfam0 n z,
      cubeSet Q ⊆ cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n) := by
  rintro _ ⟨Q0, hQ0, rfl⟩
  have hs : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have h1 : cubeSet (affineCubeTransport (goodCubeCentre n z) ((3 : ℝ) ^ n) Q0) =
      affinePhi (goodCubeCentre n z) ((3 : ℝ) ^ n) '' cubeSet Q0 :=
    cubeSet_affineCubeTransport _ hs Q0
  have h2 : cubeSet (affineCubeTransport (goodCubeCentre n z) ((3 : ℝ) ^ n)
        ((0 : Vec d), (3 : ℝ) ^ (0 : ℕ))) =
      affinePhi (goodCubeCentre n z) ((3 : ℝ) ^ n) ''
        cubeSet ((0 : Vec d), (3 : ℝ) ^ (0 : ℕ)) :=
    cubeSet_affineCubeTransport _ hs _
  rw [show goodCubeReferenceTransport n z Q0
      = affineCubeTransport (goodCubeCentre n z) ((3 : ℝ) ^ n) Q0 from rfl, h1,
    ← affineCubeTransport_unit n z, h2]
  exact Set.image_mono (hinside Q0 hQ0)

/-- Positive sides transport to positive sides. -/
theorem side_pos_transported {Qfam0 : Set (Cube d)}
    (hpos : ∀ Q ∈ Qfam0, 0 < Q.2) (n : ℕ) (z : Lattice d) :
    ∀ Q ∈ goodCubeReferenceFamily Qfam0 n z, 0 < Q.2 := by
  rintro _ ⟨Q0, hQ0, rfl⟩
  exact mul_pos (by positivity) (hpos Q0 hQ0)



theorem exists_mass_constant_of_parentEllipticity
    (c B K : ℝ) (hK : 0 < K) (hc : 0 < c)
    {j1 j2 : ℕ} {grid0 : Finset (Vec d)} {Pfam0 : Set (Cube d × Cube d)}
    {Qfam0 Afam0 : Set (Cube d)}
    (hgeom0 : IsLocalCubeGeometry grid0 j1 j2 ((0 : Vec d), (3 : ℝ) ^ (0 : ℕ))
      Pfam0 Qfam0 Afam0)
    (hinside : ∀ Q ∈ Qfam0, cubeSet Q ⊆ cubeSet ((0 : Vec d), (3 : ℝ) ^ (0 : ℕ)))
    {bad : (M : GMCModel d) → (n : ℕ) → Set (nativeBox n B (0 : Lattice d) → ℝ)}
    (hell : ∀ eps1 : ℝ, 0 < eps1 → GoodCubeParentEllipticity d c eps1 B K bad) :
    ∃ c0 : ℝ, 0 < c0 ∧ c0 ≤ c ∧ ∀ cc eps1 : ℝ, 0 < cc → cc ≤ c0 → 0 < eps1 →
      GoodCubeReferenceDisplay d cc eps1 B Pfam0 Qfam0 Afam0 bad
        (fun M n z omega _ _ _ _ =>
          ENNReal.ofReal cc *
              weightedMeasure (aCutoff M n omega)
                (cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n)) ≤
            weightedMeasure (aCutoff M n omega)
              (middleQuarter (goodCubeCentre n z, (3 : ℝ) ^ n))) ∧
      GoodCubeReferenceDisplay d cc eps1 B Pfam0 Qfam0 Afam0 bad
        (fun M n _ omega _ _ Qfam _ =>
          ∀ B' ∈ Qfam, ∀ Bq ∈ Qfam, CompactlyInside B' Bq →
            ENNReal.ofReal cc * weightedMeasure (aCutoff M n omega) (cubeSet Bq) ≤
              weightedMeasure (aCutoff M n omega) (cubeSet B')) := by
  obtain ⟨q, hq, hratio⟩ := exists_side_ratio Qfam0 hgeom0.finite_Q
    ⟨_, hgeom0.self_mem⟩ hgeom0.side_pos
  refine ⟨min c (min (q / K) ((K * 4 ^ d)⁻¹)), ?_, min_le_left _ _, ?_⟩
  · exact lt_min hc (lt_min (by positivity) (by positivity))
  intro cc eps1 hcc hcc0 heps1
  have hccc : cc ≤ c := hcc0.trans (min_le_left _ _)
  have hccq : cc ≤ q / K := hcc0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcc4 : cc ≤ (K * 4 ^ d)⁻¹ :=
    hcc0.trans ((min_le_right _ _).trans (min_le_right _ _))
  constructor
  · intro M hdelta n z omega hom law _
    obtain ⟨lam, hlam, hbd⟩ := hell eps1 heps1 M (hdelta.trans hccc) n z omega hom
    have hs : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
    have hmq : middleQuarter (goodCubeCentre n z, (3 : ℝ) ^ n) =
        cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n / 4) := rfl
    rw [hmq]
    refine mass_ratio_of_ellipticity (Q := (goodCubeCentre n z, (3 : ℝ) ^ n / 4))
      (R := (goodCubeCentre n z, (3 : ℝ) ^ n))
      (S := cubeSet (goodCubeCentre n z, (3 : ℝ) ^ n)) _ hlam.le (by positivity)
      (by positivity) (by positivity)
      (centeredAxisCube_mono (by linarith)) subset_rfl
      (fun x hx => (hbd x hx).1) (fun x hx => (hbd x hx).2) hcc.le ?_
    have hP : (0 : ℝ) < ((3 : ℝ) ^ n) ^ d := by positivity
    have h4 : (0 : ℝ) < (4 : ℝ) ^ d := by positivity
    have hK4 : cc * (K * 4 ^ d) ≤ 1 := by
      rw [← le_div_iff₀ (by positivity), one_div]
      exact hcc4
    calc cc * (K * lam * ((3 : ℝ) ^ n) ^ d)
        = cc * (K * 4 ^ d) * (lam * ((3 : ℝ) ^ n) ^ d / 4 ^ d) := by
          field_simp
      _ ≤ 1 * (lam * ((3 : ℝ) ^ n) ^ d / 4 ^ d) :=
          mul_le_mul_of_nonneg_right hK4 (by positivity)
      _ = lam * (((3 : ℝ) ^ n) ^ d / 4 ^ d) := by ring
      _ = lam * ((3 : ℝ) ^ n / 4) ^ d := by rw [div_pow]
  · intro M hdelta n z omega hom law _
    obtain ⟨lam, hlam, hbd⟩ := hell eps1 heps1 M (hdelta.trans hccc) n z omega hom
    intro B' hB' Bq hBq _
    have hsub' := cubeSet_transported_subset hinside n z B' hB'
    have hsubq := cubeSet_transported_subset hinside n z Bq hBq
    have hp' := side_pos_transported hgeom0.side_pos n z B' hB'
    have hpq := side_pos_transported hgeom0.side_pos n z Bq hBq
    refine mass_ratio_of_ellipticity _ hlam.le (by positivity) hp'.le hpq.le
      hsub' hsubq (fun x hx => (hbd x hx).1) (fun x hx => (hbd x hx).2) hcc.le ?_
    obtain ⟨R0, hR0, hR0e⟩ := hB'
    obtain ⟨S0, hS0, hS0e⟩ := hBq
    have hside : q * Bq.2 ^ d ≤ B'.2 ^ d := by
      have h := hratio R0 hR0 S0 hS0
      have hB2 : B'.2 = (3 : ℝ) ^ n * R0.2 := by rw [← hR0e]; rfl
      have hq2 : Bq.2 = (3 : ℝ) ^ n * S0.2 := by rw [← hS0e]; rfl
      have hp : (0 : ℝ) ≤ ((3 : ℝ) ^ n) ^ d := by positivity
      calc q * Bq.2 ^ d = ((3 : ℝ) ^ n) ^ d * (q * S0.2 ^ d) := by
            rw [hq2, mul_pow]; ring
        _ ≤ ((3 : ℝ) ^ n) ^ d * R0.2 ^ d := mul_le_mul_of_nonneg_left h hp
        _ = B'.2 ^ d := by rw [hB2, mul_pow]
    have hqK : cc * K ≤ q := by
      rw [← le_div_iff₀ hK]
      exact hccq
    nlinarith [hside, hlam.le, pow_pos hpq d, pow_pos hp' d,
      mul_le_mul_of_nonneg_right hqK (pow_pos hpq d).le]

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
