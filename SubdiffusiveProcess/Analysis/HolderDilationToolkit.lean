module

public import SubdiffusiveProcess.Lane4.CubeDilation
public import SubdiffusiveProcess.Lane4.Carriers

@[expose] public section




open MeasureTheory Set TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal Pointwise

noncomputable section

namespace SubdiffusiveProcess

variable {d : ℕ}

/-- Generic dilation transport for `holderRatioSet`, for ARBITRARY sets `S0, S` related by
`cubeDilation z 0 r` (not hardcoded to `frontier`, unlike `lem_extension`'s
`aux_lem_extension_holderRatioSet_dilation`). -/
theorem aux_hDet_holderRatioSet_dilation
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (beta : ℝ) (G : SpatialCoordinates d → ℝ)
    (S0 S : Set (SpatialCoordinates d))
    (hmem : ∀ x : SpatialCoordinates d, x ∈ S0 ↔ cubeDilation z 0 r x ∈ S) :
    holderRatioSet beta S0 (fun x => G (cubeDilation z 0 r x)) =
      (r ^ beta) • holderRatioSet beta S G := by
  have hTinj : Function.Injective (cubeDilation z (0 : SpatialCoordinates d) r) :=
    (cubeDilationEquiv z (0 : SpatialCoordinates d) hr.ne').injective
  have hTsurj : Function.Surjective (cubeDilation z (0 : SpatialCoordinates d) r) :=
    (cubeDilationEquiv z (0 : SpatialCoordinates d) hr.ne').surjective
  ext v
  simp only [holderRatioSet, Set.mem_smul_set, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, y, hy, hxy, rfl⟩
    have hTxy : cubeDilation z 0 r x ≠ cubeDilation z 0 r y := fun h => hxy (hTinj h)
    have hd : Real.sqrt (∑ j, (cubeDilation z 0 r x j - cubeDilation z 0 r y j) ^ 2) =
        r * Real.sqrt (∑ j, (x j - y j) ^ 2) := sqrt_sum_sq_cubeDilation z 0 hr x y
    refine ⟨|G (cubeDilation z 0 r x) - G (cubeDilation z 0 r y)| /
        (Real.sqrt (∑ j, (cubeDilation z 0 r x j - cubeDilation z 0 r y j) ^ 2)) ^ beta,
      ⟨cubeDilation z 0 r x, (hmem x).mp hx, cubeDilation z 0 r y, (hmem y).mp hy, hTxy, rfl⟩, ?_⟩
    rw [hd, smul_eq_mul, Real.mul_rpow hr.le (Real.sqrt_nonneg _)]
    have hden : (0:ℝ) < r ^ beta := Real.rpow_pos_of_pos hr beta
    field_simp
  · rintro ⟨v', ⟨x, hx, y, hy, hxy, rfl⟩, rfl⟩
    obtain ⟨x0, hx0⟩ := hTsurj x
    obtain ⟨y0, hy0⟩ := hTsurj y
    have hx0S0 : x0 ∈ S0 := (hmem x0).mpr (hx0 ▸ hx)
    have hy0S0 : y0 ∈ S0 := (hmem y0).mpr (hy0 ▸ hy)
    have hxy0 : x0 ≠ y0 := fun h => hxy (by rw [← hx0, ← hy0, h])
    have hd : Real.sqrt (∑ j, (x j - y j) ^ 2) = r * Real.sqrt (∑ j, (x0 j - y0 j) ^ 2) := by
      have := sqrt_sum_sq_cubeDilation z 0 hr x0 y0
      rwa [hx0, hy0] at this
    refine ⟨x0, hx0S0, y0, hy0S0, hxy0, ?_⟩
    rw [hx0, hy0, hd, smul_eq_mul, Real.mul_rpow hr.le (Real.sqrt_nonneg _)]
    have hden : (0:ℝ) < r ^ beta := Real.rpow_pos_of_pos hr beta
    field_simp

/-- `holderSeminorm` transport under `cubeDilation`, for arbitrary related sets. -/
theorem aux_hDet_holderSeminorm_dilation
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (beta : ℝ) (G : SpatialCoordinates d → ℝ)
    (S0 S : Set (SpatialCoordinates d))
    (hmem : ∀ x : SpatialCoordinates d, x ∈ S0 ↔ cubeDilation z 0 r x ∈ S) :
    holderSeminorm beta S0 (fun x => G (cubeDilation z 0 r x)) =
      r ^ beta * holderSeminorm beta S G := by
  unfold holderSeminorm
  rw [aux_hDet_holderRatioSet_dilation z r hr beta G S0 S hmem,
    Real.sSup_smul_of_nonneg (Real.rpow_nonneg hr.le _)]
  simp only [smul_eq_mul]

/-- `IsHolderOn` transport under `cubeDilation`, for arbitrary related sets. -/
theorem aux_hDet_isHolderOn_dilation
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (beta : ℝ) (G : SpatialCoordinates d → ℝ)
    (S0 S : Set (SpatialCoordinates d))
    (hmem : ∀ x : SpatialCoordinates d, x ∈ S0 ↔ cubeDilation z 0 r x ∈ S)
    (hG : IsHolderOn beta S G) :
    IsHolderOn beta S0 (fun x => G (cubeDilation z 0 r x)) := by
  unfold IsHolderOn at hG ⊢
  rw [aux_hDet_holderRatioSet_dilation z r hr beta G S0 S hmem]
  exact (bddAbove_smul_iff_of_pos (Real.rpow_pos_of_pos hr beta)).mpr hG

/-- The affine map `cubeDilation z 0 r` sends the closed unit cube onto the closed cube of
side `r` about `z`: the concrete membership-transport fact `hDet`'s `_below`/`_above`
construction needs to instantiate the generic dilation lemmas above at `S0 := unitClosed`,
`S := closedCube z r hr`. -/
theorem aux_hDet_mem_closedCube_dilation
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (x : SpatialCoordinates d) :
    x ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) ↔
      cubeDilation z 0 r x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) := by
  show dist x 0 ≤ 1 / 2 ↔ dist (cubeDilation z 0 r x) z ≤ r / 2
  have hdeq : dist (cubeDilation z 0 r x) z = r * dist x 0 := by
    have heq : cubeDilation z 0 r x - z = r • (x - 0) := by
      funext i
      simp [cubeDilation, smul_eq_mul]
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_pos hr, ← dist_eq_norm]
  rw [hdeq]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith



theorem aux_hDet_cAlphaNorm_le_of_holderSeminorm_zero
    (alpha : ℝ) (hpos : 0 ≤ alpha) (S : Set (SpatialCoordinates d))
    (F : SpatialCoordinates d → ℝ) (x0 : SpatialCoordinates d) (hx0 : x0 ∈ S)
    (hzero : F x0 = 0)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S,
      Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ 1)
    (hHolder : IsHolderOn alpha S F) {K : ℝ} (hK : holderSeminorm alpha S F ≤ K) (hK0 : 0 ≤ K) :
    cAlphaNorm alpha S F ≤ 2 * K := by
  have hpoint : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      |F x - F y| ≤ K * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha := by
    intro x hx y hy hxy
    have hρpos : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
      rcases (Real.sqrt_nonneg (∑ j : Fin d, (x j - y j) ^ 2)).lt_or_eq with h | h
      · exact h
      · exfalso; apply hxy
        have hsq : ∑ j : Fin d, (x j - y j) ^ 2 = 0 := by
          have hh := (Real.sqrt_eq_zero (by positivity)).mp h.symm
          simpa using hh
        have hall : ∀ j ∈ Finset.univ, (x j - y j) ^ 2 = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp hsq
        funext j
        have hj := hall j (Finset.mem_univ j)
        nlinarith [sq_eq_zero_iff.mp hj]
    have hρa_pos : 0 < (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha :=
      Real.rpow_pos_of_pos hρpos alpha
    have hmem : |F x - F y| / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha ∈
        holderRatioSet alpha S F := ⟨x, hx, y, hy, hxy, rfl⟩
    have hle : |F x - F y| / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha ≤ K :=
      (le_csSup hHolder hmem).trans hK
    calc |F x - F y| = (|F x - F y| / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha) *
        (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha := by field_simp
      _ ≤ K * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha :=
        mul_le_mul_of_nonneg_right hle hρa_pos.le
  have hsup : sSup {v : ℝ | ∃ x ∈ S, v = |F x|} ≤ K := by
    apply Real.sSup_le
    · rintro v ⟨x, hx, rfl⟩
      by_cases hxx : x = x0
      · subst hxx; rw [hzero]; simpa using hK0
      · have hfx := hpoint x hx x0 hx0 hxx
        have hfd : (Real.sqrt (∑ j : Fin d, (x j - x0 j) ^ 2)) ^ alpha ≤ 1 :=
          Real.rpow_le_one (by positivity) (hdiam x hx x0 hx0) hpos
        calc |F x| = |F x - F x0| := by rw [hzero]; ring_nf
          _ ≤ K * (Real.sqrt (∑ j : Fin d, (x j - x0 j) ^ 2)) ^ alpha := hfx
          _ ≤ K * 1 := mul_le_mul_of_nonneg_left hfd hK0
          _ = K := mul_one K
    · exact hK0
  unfold cAlphaNorm
  linarith [hsup, hK]

end SubdiffusiveProcess
