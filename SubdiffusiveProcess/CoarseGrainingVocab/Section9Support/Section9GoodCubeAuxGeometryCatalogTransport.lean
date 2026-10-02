import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeAuxGeometryCatalog




set_option autoImplicit false
open Set MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.Section9 (centeredAxisCube)
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The affine image of the reference pair catalogue is exactly the catalogue of transported centers at the integer native scale. -/
theorem goodCube_auxiliary_pairs_affine_image {d : ℕ}
    (X : Finset (Vec d)) (j k n : ℕ) (y : Vec d) :
    (goodCubeAuxiliaryPairs X j (-(k : ℤ))).image
        (affinePairTransport y ((3 : ℝ) ^ n)) =
      goodCubeAuxiliaryPairs (goodCubeAuxiliaryCenters X y n) j ((n : ℤ) - k) := by
  have hscale : ((3 : ℝ) ^ n) * (3 : ℝ) ^ (-(k : ℤ)) = (3 : ℝ) ^ ((n : ℤ) - k) :=
    (goodCube_native_depth_scales n k k le_rfl).1
  have key : ∀ x : Vec d,
      affinePairTransport y ((3 : ℝ) ^ n)
          ((x, (3 : ℝ) ^ (-(j : ℤ)) * (3 : ℝ) ^ (-(k : ℤ))), (x, (3 : ℝ) ^ (-(k : ℤ)))) =
        ((affinePhi y ((3 : ℝ) ^ n) x, (3 : ℝ) ^ (-(j : ℤ)) * (3 : ℝ) ^ ((n : ℤ) - k)),
          (affinePhi y ((3 : ℝ) ^ n) x, (3 : ℝ) ^ ((n : ℤ) - k))) := by
    intro x
    refine Prod.ext ?_ ?_
    · refine Prod.ext ?_ ?_
      · rfl
      · show ((3 : ℝ) ^ n) * ((3 : ℝ) ^ (-(j : ℤ)) * (3 : ℝ) ^ (-(k : ℤ))) =
            (3 : ℝ) ^ (-(j : ℤ)) * (3 : ℝ) ^ ((n : ℤ) - k)
        rw [← hscale]
        ring
    · refine Prod.ext ?_ ?_
      · rfl
      · exact hscale
  simp only [goodCubeAuxiliaryPairs, goodCubeAuxiliaryCenters,
    Finset.image_image]
  refine Finset.image_congr (fun x _hx => key x)

/-- A positive affine image of a reference cube inside the unit cube lies inside the native parent cube. -/
theorem goodCube_affine_cube_subset_native {d : ℕ} (Q : Cube d)
    (hQ : cubeSet Q ⊆ cubeSet ((0 : Vec d), (1 : ℝ)))
    (y : Vec d) {s : ℝ} (hs : 0 < s) :
    cubeSet (affineCubeTransport y s Q) ⊆ cubeSet (y, s) := by
  calc cubeSet (affineCubeTransport y s Q)
      = affinePhi y s '' cubeSet Q := cubeSet_affineCubeTransport y hs Q
    _ ⊆ affinePhi y s '' cubeSet ((0 : Vec d), (1 : ℝ)) := Set.image_mono hQ
    _ = cubeSet (y, s) := by
        rw [← cubeSet_affineCubeTransport y hs]
        simp [affineCubeTransport]

/-- Native auxiliary pairs preserve cardinality, exact scale, middle-half geometry, and containment in the native parent. -/
theorem goodCube_auxiliary_pair_catalog_native {d : ℕ}
    (X : Finset (Vec d)) (j k : ℕ) (hj : 1 ≤ j)
    (hX : ∀ x ∈ X, cubeSet (x, (3 : ℝ) ^ (-(k : ℤ))) ⊆
      cubeSet ((0 : Vec d), (1 : ℝ))) (n : ℕ) (y : Vec d) :
    let P := goodCubeAuxiliaryPairs X j (-(k : ℤ))
    let Pn := P.image (affinePairTransport y ((3 : ℝ) ^ n))
    Pn.card = P.card ∧
      ∀ p ∈ Pn, 0 < p.1.2 ∧
        p.2.2 = (3 : ℝ) ^ ((n : ℤ) - k) ∧
        p.1.2 = (3 : ℝ) ^ (-(j : ℤ)) * p.2.2 ∧
        closure (cubeSet p.1) ⊆ centeredAxisCube p.2.1 (p.2.2 / 2) ∧
        cubeSet p.2 ⊆ cubeSet (y, (3 : ℝ) ^ n) ∧
        (k ≤ n → p.2.2 = (3 : ℝ) ^ (n - k)) := by
  dsimp only
  have h3n : (0 : ℝ) < (3 : ℝ) ^ n := pow_pos (by norm_num) n
  have hinj : Function.Injective (affinePhi y ((3 : ℝ) ^ n)) :=
    affinePhi_injective y h3n.ne'
  obtain ⟨hcardC, hgeoC⟩ := goodCube_auxiliary_pairs_geometry
    (goodCubeAuxiliaryCenters X y n) j ((n : ℤ) - k) hj
  obtain ⟨hcardX, -⟩ := goodCube_auxiliary_pairs_geometry X j (-(k : ℤ)) hj
  have hcent : (goodCubeAuxiliaryCenters X y n).card = X.card := by
    simp only [goodCubeAuxiliaryCenters, Finset.card_image_of_injective _ hinj]
  refine ⟨?_, ?_⟩
  · rw [goodCube_auxiliary_pairs_affine_image, hcardC, hcent]
    exact hcardX.symm
  · rintro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hgeoC p
      (by rw [← goodCube_auxiliary_pairs_affine_image]; exact hp)
    obtain ⟨q, hq, hpq⟩ := Finset.mem_image.1 hp
    simp only [goodCubeAuxiliaryPairs, Finset.mem_image] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    refine ⟨h1, h2, h3, h4, ?_, ?_⟩
    · rw [← hpq]
      simp only [affinePairTransport]
      exact goodCube_affine_cube_subset_native _ (hX x hx) y
        (pow_pos (by norm_num) n)
    · intro hkn
      rw [h2, ← zpow_natCast, ← Int.ofNat_sub hkn]

/-- The reference relative square cap is preserved at every native scale. -/
theorem goodCube_auxiliary_physical_square_cap (n k : ℕ) {eta C L : ℝ}
    (href : ((3 : ℝ) ^ (-(k : ℤ))) ^ 2 ≤ (eta / C) * L ^ 2) :
    ((3 : ℝ) ^ ((n : ℤ) - k)) ^ 2 ≤ (eta / C) * ((3 : ℝ) ^ n * L) ^ 2 := by
  have hscale := (goodCube_native_depth_scales n k k le_rfl).1
  rw [← hscale, mul_pow, mul_pow]
  calc ((3 : ℝ) ^ n) ^ 2 * ((3 : ℝ) ^ (-(k : ℤ))) ^ 2
      ≤ ((3 : ℝ) ^ n) ^ 2 * ((eta / C) * L ^ 2) :=
        mul_le_mul_of_nonneg_left href (sq_nonneg ((3 : ℝ) ^ n))
    _ = (eta / C) * (((3 : ℝ) ^ n) ^ 2 * L ^ 2) := by ring

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
