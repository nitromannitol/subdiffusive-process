module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeMassReduction
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeReferenceGeometry

@[expose] public section

/-!
# Bounded native scales for the good-cube reference family

The finite choices  are made on the
unit reference cube and transported by triadic dilations. In positive
dimension, containment in that cube forces every gridded member to have a
nonpositive integer exponent. Taking the maximum of the resulting finite
nonnegative depths gives a bound chosen before the model and native scale.

The transported exponent is retained as an integer at every native scale.
Above the common depth bound it is a natural scale with bounded deficit.
The same construction supplies the actual ENNReal volume floor used for
mass comparison. It keeps the original family fixed; auxiliary testing
cubes and their separately chosen centers are not adjoined to it.
-/

set_option autoImplicit false
open Set MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.Section9 (centeredAxisCube)
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- A gridded positive-side cube contained in the unit cube has a nonnegative triadic depth. -/
theorem exists_goodCube_reference_depth {d : ℕ} [NeZero d]
    {grid : Finset (Vec d)} (Q : Cube d) (hQ : 0 < Q.2)
    (hgrid : IsGridCube grid Q.1 Q.2)
    (hinside : cubeSet Q ⊆ cubeSet ((0 : Vec d), (1 : ℝ))) :
    Q.2 ≤ 1 ∧ ∃ k : ℕ, Q.2 = (3 : ℝ) ^ (-(k : ℤ)) := by
  obtain ⟨g, hg, m, lattice, hm, hx⟩ := hgrid
  have hmeas : MeasureTheory.volume (cubeSet Q) ≤
      MeasureTheory.volume (cubeSet ((0 : Vec d), (1 : ℝ))) := measure_mono hinside
  rw [volume_cubeSet hQ.le, volume_cubeSet (by norm_num : (0 : ℝ) ≤ 1)] at hmeas
  have h1 : Q.2 ^ d ≤ (1 : ℝ) ^ d :=
    (ENNReal.ofReal_le_ofReal_iff (by norm_num : 0 ≤ (1 : ℝ) ^ d)).mp hmeas
  have h1' : Q.2 ^ d ≤ 1 := by simpa using h1
  have hside : Q.2 ≤ 1 := (pow_le_one_iff_of_nonneg hQ.le (NeZero.ne d)).mp h1'
  have hmle : m ≤ 0 := by
    have h3 : (3 : ℝ) ^ m ≤ 1 := by rw [← hm]; exact hside
    exact (zpow_le_one_iff_right₀ (by norm_num : (1 : ℝ) < 3)).mp h3
  refine ⟨hside, (-m).toNat, ?_⟩
  have hnonneg : 0 ≤ -m := by omega
  rw [hm, Int.toNat_of_nonneg hnonneg]
  simp

/-- Native dilation retains the integer descendant scale at every n and has natural scale above the common depth bound. -/
theorem goodCube_native_depth_scales (n k J : ℕ) (hkJ : k ≤ J) :
    (3 : ℝ) ^ n * (3 : ℝ) ^ (-(k : ℤ)) = (3 : ℝ) ^ ((n : ℤ) - k) ∧
      (J ≤ n → (3 : ℝ) ^ n * (3 : ℝ) ^ (-(k : ℤ)) =
        (3 : ℝ) ^ (n - k) ∧ n - (n - k) ≤ J) := by
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  have hInt : (3 : ℝ) ^ n * (3 : ℝ) ^ (-(k : ℤ)) = (3 : ℝ) ^ ((n : ℤ) - k) := by
    calc (3 : ℝ) ^ n * (3 : ℝ) ^ (-(k : ℤ))
        = (3 : ℝ) ^ ((n : ℤ) + -(k : ℤ)) := by
          rw [zpow_add₀ h3]
          simp only [zpow_natCast]
      _ = (3 : ℝ) ^ ((n : ℤ) - k) := rfl
  refine ⟨hInt, ?_⟩
  intro hJn
  have hk : k ≤ n := le_trans hkJ hJn
  refine ⟨?_, ?_⟩
  · calc (3 : ℝ) ^ n * (3 : ℝ) ^ (-(k : ℤ)) = (3 : ℝ) ^ ((n : ℤ) - k) := hInt
      _ = (3 : ℝ) ^ ((n - k : ℕ) : ℤ) := by
          congr 1
          exact (Int.ofNat_sub hk).symm
      _ = (3 : ℝ) ^ (n - k) := by rw [zpow_natCast]
  · omega

/-- A uniform lower reference side and unit upper side give an actual Lebesgue-volume floor after every positive affine dilation. -/
theorem goodCube_affine_volume_floor {d : ℕ}
    (Q R : Cube d) (y : Vec d) {s ell : ℝ}
    (hs : 0 < s) (hell : 0 < ell) (hQ : ell ≤ Q.2)
    (hR0 : 0 ≤ R.2) (hR1 : R.2 ≤ 1) :
    ENNReal.ofReal (ell ^ d) * volume (cubeSet (affineCubeTransport y s R)) ≤
      volume (cubeSet (affineCubeTransport y s Q)) := by
  have hs0 : 0 ≤ s := le_of_lt hs
  have hRside : 0 ≤ s * R.2 := mul_nonneg hs0 hR0
  have hQside : 0 ≤ s * Q.2 := mul_nonneg hs0 (le_trans (le_of_lt hell) hQ)
  simp only [affineCubeTransport]
  rw [volume_cubeSet hRside, volume_cubeSet hQside]
  rw [← ENNReal.ofReal_mul (pow_nonneg (le_of_lt hell) d)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hRpow : R.2 ^ d ≤ 1 := pow_le_one₀ hR0 hR1
  have h1 : ell ^ d * (s * R.2) ^ d ≤ ell ^ d * s ^ d := by
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (le_of_lt hell) d)
    rw [mul_pow]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hRpow (pow_nonneg (le_of_lt hs) d)
  have h2 : ell ^ d * s ^ d ≤ Q.2 ^ d * s ^ d :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_of_lt hell) hQ d) (pow_nonneg (le_of_lt hs) d)
  calc ell ^ d * (s * R.2) ^ d ≤ ell ^ d * s ^ d := h1
    _ ≤ Q.2 ^ d * s ^ d := h2
    _ = (s * Q.2) ^ d := by rw [mul_pow]; ring

/-- The fixed finite reference family has bounded nonnegative depth labels and a common positive side floor. -/
theorem exists_goodCube_reference_depths {d : ℕ} [NeZero d]
    (grid : Finset (Vec d)) (Qfam : Set (Cube d)) (hfin : Qfam.Finite)
    (hpos : ∀ Q ∈ Qfam, 0 < Q.2)
    (hgrid : ∀ Q ∈ Qfam, IsGridCube grid Q.1 Q.2)
    (hinside : ∀ Q ∈ Qfam, cubeSet Q ⊆ cubeSet ((0 : Vec d), (1 : ℝ))) :
    ∃ (J : ℕ) (k : Qfam → ℕ), ∀ Q : Qfam,
      k Q ≤ J ∧ Q.val.2 = (3 : ℝ) ^ (-(k Q : ℤ)) ∧
      (3 : ℝ) ^ (-(J : ℤ)) ≤ Q.val.2 ∧ Q.val.2 ≤ 1 := by
  classical
  have hdepth : ∀ Q : Qfam, ∃ k : ℕ, Q.val.2 = (3 : ℝ) ^ (-(k : ℤ)) := by
    intro Q
    exact (exists_goodCube_reference_depth Q.val (hpos Q.val Q.property)
      (hgrid Q.val Q.property) (hinside Q.val Q.property)).2
  choose k hk using hdepth
  let : Finite Qfam := hfin.to_subtype
  let : Fintype Qfam := Fintype.ofFinite Qfam
  refine ⟨Finset.univ.sup (fun (Q : Qfam) => k Q), fun Q => k Q, ?_⟩
  intro Q
  refine ⟨Finset.le_sup (f := fun (Q : Qfam) => k Q) (Finset.mem_univ Q), hk Q, ?_,
    (exists_goodCube_reference_depth Q.val (hpos Q.val Q.property)
      (hgrid Q.val Q.property) (hinside Q.val Q.property)).1⟩
  have hkJ : k Q ≤ Finset.univ.sup (fun (Q : Qfam) => k Q) :=
    Finset.le_sup (f := fun (Q : Qfam) => k Q) (Finset.mem_univ Q)
  rw [hk Q]
  apply (zpow_le_zpow_iff_right₀ (by norm_num : (1:ℝ) < 3)).2
  apply neg_le_neg
  exact_mod_cast hkJ

/-- Nonzero affine cube transport preserves the number of members of a finite testing family. -/
theorem goodCube_affine_family_card {d : ℕ} (Qfam : Finset (Cube d))
    (y : Vec d) {s : ℝ} (hs : s ≠ 0) :
    (Qfam.image (affineCubeTransport y s)).card = Qfam.card := by
  apply Finset.card_image_of_injective
  intro Q Q' h
  have h1 : affinePhi y s Q.1 = affinePhi y s Q'.1 := by
    simpa only [affineCubeTransport] using! congrArg Prod.fst h
  have h2 : s * Q.2 = s * Q'.2 := by
    simpa only [affineCubeTransport] using congrArg Prod.snd h
  have hQ1 : Q.1 = Q'.1 := affinePhi_injective y hs h1
  have hQ2 : Q.2 = Q'.2 := mul_left_cancel₀ hs h2
  exact Prod.ext hQ1 hQ2

/-- Construct the reference scale catalog, its exact native scales, and its transported volume floor directly from the finite gridded geometry. -/
theorem exists_goodCube_reference_scale_catalog {d : ℕ} [NeZero d]
    (grid : Finset (Vec d)) (Qfam : Set (Cube d)) (hfin : Qfam.Finite)
    (hpos : ∀ Q ∈ Qfam, 0 < Q.2)
    (hgrid : ∀ Q ∈ Qfam, IsGridCube grid Q.1 Q.2)
    (hinside : ∀ Q ∈ Qfam, cubeSet Q ⊆ cubeSet ((0 : Vec d), (1 : ℝ))) :
    ∃ (J : ℕ) (k : Qfam → ℕ),
      (∀ Q : Qfam, k Q ≤ J ∧ Q.val.2 = (3 : ℝ) ^ (-(k Q : ℤ)) ∧
        (3 : ℝ) ^ (-(J : ℤ)) ≤ Q.val.2 ∧ Q.val.2 ≤ 1) ∧
      (∀ (n : ℕ) (y : Vec d) (Q : Qfam),
        (affineCubeTransport y ((3 : ℝ) ^ n) Q.val).2 =
          (3 : ℝ) ^ ((n : ℤ) - k Q) ∧
        (J ≤ n → (affineCubeTransport y ((3 : ℝ) ^ n) Q.val).2 =
          (3 : ℝ) ^ (n - k Q) ∧ n - (n - k Q) ≤ J)) ∧
      ∀ (n : ℕ) (y : Vec d) (Q R : Qfam),
        ENNReal.ofReal (((3 : ℝ) ^ (-(J : ℤ))) ^ d) *
          volume (cubeSet (affineCubeTransport y ((3 : ℝ) ^ n) R.val)) ≤
          volume (cubeSet (affineCubeTransport y ((3 : ℝ) ^ n) Q.val)) := by
  obtain ⟨J, k, hdata⟩ := exists_goodCube_reference_depths grid Qfam hfin hpos hgrid hinside
  refine ⟨J, k, hdata, ?_, ?_⟩
  · intro n y Q
    simp only [affineCubeTransport]
    rw [(hdata Q).2.1]
    exact goodCube_native_depth_scales n (k Q) J (hdata Q).1
  · intro n y Q R
    exact goodCube_affine_volume_floor Q.val R.val y
      (pow_pos (by norm_num) n) (zpow_pos (by norm_num) _)
      ((hdata Q).2.2.1) (hpos R.val R.property).le ((hdata R).2.2.2)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
