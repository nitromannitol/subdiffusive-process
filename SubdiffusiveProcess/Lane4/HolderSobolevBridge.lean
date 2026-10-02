

import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Lane4.Bridge
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.WindowSeminorms
import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.InhomogeneousForcingCarrier
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.IntervalGeometry

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace SubdiffusiveProcess.Lane4

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec

/-! ### 1. The dictionary `halfHolderSeminorm = holderSeminormOn (1/2)` -/

/-- The explicit Euclidean magnitude is the square root of the coordinate sum of squares. -/
theorem euclideanNorm_eq_sqrt_sum_sq {d : ℕ} (v : SpatialCoordinates d) :
    euclideanNorm v = Real.sqrt (∑ i : Fin d, (v i) ^ 2) := by
  simp only [euclideanNorm, vecNormSq, vecDot, sq]

/-- A single Hölder-`1/2` quotient, written in MFD's finite-coordinate form, is the GMC
Euclidean quotient. -/
theorem halfHolderQuotient_eq {d : ℕ} (g : SpatialCoordinates d → Fin d → ℝ)
    (x y : SpatialCoordinates d) :
    Real.sqrt (∑ i : Fin d, (g x i - g y i) ^ 2) /
        Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) =
      euclideanNorm (g x - g y) / euclideanNorm (x - y) ^ (1 / 2 : ℝ) := by
  rw [euclideanNorm_eq_sqrt_sum_sq, euclideanNorm_eq_sqrt_sum_sq, ← Real.sqrt_eq_rpow]
  rfl

/-- **Dictionary.** MFD's `[g]_{W^{1/2,∞}(S)}` (`halfHolderSeminorm`, finite coordinates) is
GMC's explicit Euclidean Hölder seminorm `holderSeminormOn S (1/2) g`: both are the `sSup` of the
same set of quotients, including the junk value on unbounded or one-point quotient sets. -/
theorem halfHolderSeminorm_eq_holderSeminormOn {d : ℕ} (S : Set (SpatialCoordinates d))
    (g : SpatialCoordinates d → Fin d → ℝ) :
    halfHolderSeminorm S g = holderSeminormOn S (1 / 2) g := by
  unfold halfHolderSeminorm holderSeminormOn
  congr 1
  ext v
  simp only [Set.mem_setOf_eq, halfHolderQuotient_eq]

/-! ### 2. Translation invariance of the Hölder class and seminorm -/

/-- A Hölder bound on `W` transfers to `g (· + z)` on any `V` with `V + z ⊆ W`. -/
theorem holderSeminormBoundOn_comp_add {d : ℕ} {V W : Set (Vec d)} (z : Vec d)
    (hVW : ∀ y ∈ V, y + z ∈ W) {alpha K : ℝ} {g : Vec d → Vec d}
    (hg : HolderSeminormBoundOn W alpha K g) :
    HolderSeminormBoundOn V alpha K (fun y => g (y + z)) := by
  intro p hp q hq
  have h := hg (p + z) (hVW p hp) (q + z) (hVW q hq)
  simpa only [add_sub_add_right_eq_sub] using h

/-- The Hölder class transfers to `g (· + z)` on any `V` with `V + z ⊆ W`. -/
theorem memHolder_comp_add {d : ℕ} {V W : Set (Vec d)} (z : Vec d)
    (hVW : ∀ y ∈ V, y + z ∈ W) {alpha : ℝ} {g : Vec d → Vec d}
    (hg : MemHolder W alpha g) : MemHolder V alpha (fun y => g (y + z)) := by
  obtain ⟨K, hK, hgK⟩ := hg
  exact ⟨K, hK, holderSeminormBoundOn_comp_add z hVW hgK⟩

/-- The literal Hölder seminorm is translation invariant: when `W` is exactly `V + z`, the
quotient sets of `g (· + z)` on `V` and of `g` on `W` coincide (no Hölder hypothesis needed). -/
theorem holderSeminormOn_comp_add {d : ℕ} {V W : Set (Vec d)} (z : Vec d)
    (hVW : ∀ y, y ∈ V ↔ y + z ∈ W) (alpha : ℝ) (g : Vec d → Vec d) :
    holderSeminormOn V alpha (fun y => g (y + z)) = holderSeminormOn W alpha g := by
  unfold holderSeminormOn
  congr 1
  ext r
  constructor
  · rintro ⟨x, hx, y, hy, hxy, rfl⟩
    refine ⟨x + z, (hVW x).1 hx, y + z, (hVW y).1 hy, fun h => hxy (add_right_cancel h), ?_⟩
    rw [add_sub_add_right_eq_sub]
  · rintro ⟨x, hx, y, hy, hxy, rfl⟩
    refine ⟨x - z, (hVW _).2 (by rwa [sub_add_cancel]), y - z,
      (hVW _).2 (by rwa [sub_add_cancel]), fun h => hxy (sub_left_inj.1 h), ?_⟩
    simp only [sub_add_cancel, sub_sub_sub_cancel_right]

/-! ### 3. The MFD root is the translate `z + □_m` -/

/-- The MFD root `centeredCube z (3^m)` is `z + □_m`, as a set (the shape used by
`aux_prop_folded_iteration_weak_transfer`). -/
theorem centeredCube_eq_translateSet_cube {d : ℕ} (m : ℕ) (z : SpatialCoordinates d)
    (hR : (0 : ℝ) < 3 ^ m) :
    (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) =
      translateSet z (cube d (m : ℤ)) := by
  ext x
  rw [mem_translateSet_iff_sub_mem, cube,
    ← centeredCube_zero_eq_openCubeSet_originCube (d := d) (m : ℤ) (by positivity)]
  change dist x z < (3 : ℝ) ^ m / 2 ↔ dist (x - z) 0 < (3 : ℝ) ^ (m : ℤ) / 2
  rw [dist_eq_norm, dist_eq_norm, sub_zero, zpow_natCast]

/-- `y ∈ □_m ↔ y + z ∈ z + □_m`. -/
theorem mem_cube_iff_add_mem_centeredCube {d : ℕ} (m : ℕ) (z : SpatialCoordinates d)
    (hR : (0 : ℝ) < 3 ^ m) (y : Vec d) :
    y ∈ cube d (m : ℤ) ↔
      y + z ∈ (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) := by
  rw [centeredCube_eq_translateSet_cube m z hR, mem_translateSet_iff_sub_mem, add_sub_cancel_right]






theorem folded_source_memHolder {d : ℕ} (m : ℕ) (z : SpatialCoordinates d)
    (hR : (0 : ℝ) < 3 ^ m) (g : SpatialCoordinates d → Fin d → ℝ)
    (hg : MemHolder (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) (1 / 2) g) :
    MemHolder (cube d (m : ℤ)) (1 / 2) (fun y => g (y + z)) :=
  memHolder_comp_add z (fun y hy => (mem_cube_iff_add_mem_centeredCube m z hR y).1 hy) hg

/-- **B5, seminorm dictionary on the translated chart.** GMC's Hölder seminorm of the
translated source on `□_m` is exactly MFD's `halfHolderSeminorm` of `g` on the root. -/
theorem folded_source_holderSeminormOn_eq {d : ℕ} (m : ℕ) (z : SpatialCoordinates d)
    (hR : (0 : ℝ) < 3 ^ m) (g : SpatialCoordinates d → Fin d → ℝ) :
    holderSeminormOn (cube d (m : ℤ)) (1 / 2) (fun y => g (y + z)) =
      halfHolderSeminorm (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) g := by
  rw [halfHolderSeminorm_eq_holderSeminormOn]
  exact holderSeminormOn_comp_add z (mem_cube_iff_add_mem_centeredCube m z hR) _ g

/-- **B5, fractional carrier.** For every order `s ∈ (0, 1/4]` the translated source lies in
the inhomogeneous carrier `MemCubeEuclideanFullWsp (originCube d m) s two` — the exact
`hgfrac` premise of `aux_prop_folded_iteration_interior_excess_decay` and
`aux_prop_folded_iteration_iteration_core`. -/
theorem folded_source_memCubeEuclideanFullWsp {d : ℕ} (hd : 2 ≤ d) (m : ℕ)
    (z : SpatialCoordinates d) (hR : (0 : ℝ) < 3 ^ m) (g : SpatialCoordinates d → Fin d → ℝ)
    (hg : MemHolder (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) (1 / 2) g) :
    ∀ s : ℝ, 0 < s → s ≤ (1 / 4 : ℝ) →
      ∃ sOrder : FractionalOrder, sOrder.1 = s ∧
        Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
          (originCube d m) sOrder FiniteLpExponent.two (fun y => g (y + z)) := by
  intro s hs0 hs
  exact Section6ExcessDecay.exists_fractionalOrder_memCubeEuclideanFullWsp_of_memHolder
    (by omega) hs0 hs (folded_source_memHolder m z hR g hg)



theorem folded_source_window_le {d : ℕ} (hd : 2 ≤ d) (m : ℕ) (z : SpatialCoordinates d)
    (hR : (0 : ℝ) < 3 ^ m) (g : SpatialCoordinates d → Fin d → ℝ)
    (hg : MemHolder (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) (1 / 2) g) :
    ∀ s : ℝ, 0 < s → s ≤ (1 / 4 : ℝ) →
      ∀ (j : ℤ) (x : Vec d), x ∈ cube d (m : ℤ) →
        (3 : ℝ) ^ (s * (j : ℝ)) *
            (fractionalSeminormOn (truncatedCube d (m : ℤ) j x) s
              (fun y => g (y + z))).toReal ≤
          Section6ExcessDecay.fractionalHolderConst d * Real.sqrt s * (3 : ℝ) ^ ((j : ℝ) / 2) *
            halfHolderSeminorm
              (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) g := by
  haveI : NeZero d := ⟨by omega⟩
  intro s hs0 hs j x hx
  rw [← folded_source_holderSeminormOn_eq m z hR g]
  exact Section6Holder.forcing_fractional_window_le hx hs0 hs
    (folded_source_memHolder m z hR g hg)

/-- **B5, window display at the iteration windows** `U_j = truncatedCube d m j 0`, indexed by
`j : ℕ` with the casts of `aux_prop_folded_iteration_iteration_core`'s defect `defJ`. -/
theorem folded_source_window_le_nat {d : ℕ} (hd : 2 ≤ d) (m : ℕ) (z : SpatialCoordinates d)
    (hR : (0 : ℝ) < 3 ^ m) (g : SpatialCoordinates d → Fin d → ℝ)
    (hg : MemHolder (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) (1 / 2) g) :
    ∀ s : ℝ, 0 < s → s ≤ (1 / 4 : ℝ) → ∀ j : ℕ,
      (3 : ℝ) ^ (s * (j : ℝ)) *
          (fractionalSeminormOn (truncatedCube d m j 0) s (fun y => g (y + z))).toReal ≤
        Section6ExcessDecay.fractionalHolderConst d * Real.sqrt s *
          (3 : ℝ) ^ (-(((m : ℝ) - (j : ℝ)) / 2)) *
          ((3 : ℝ) ^ ((m : ℝ) / 2) *
            halfHolderSeminorm
              (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) g) := by
  intro s hs0 hs j
  have h := folded_source_window_le hd m z hR g hg s hs0 hs (j : ℤ) 0
    (Section6ExcessDecay.zero_mem_cube d m)
  have hsplit := Section6Holder.three_half_scale_decay (m : ℤ) (j : ℤ)
  simp only [Int.cast_natCast] at h hsplit
  rw [hsplit] at h
  calc (3 : ℝ) ^ (s * (j : ℝ)) *
        (fractionalSeminormOn (truncatedCube d m j 0) s (fun y => g (y + z))).toReal
      ≤ _ := h
    _ = _ := by ring

/-- **B5, summed source defect** (paper `e.delta.j.z.sum`). For any family `D` that on each
scale `j ∈ [n, top]` is either `0` (a bad scale) or the iteration core's source defect
`c · (a0 j)⁻¹ · 3^{sj} [g']_{H̲^s(U_j)}`, and any bound `A` on the inverse references over
`[n, top]`, the defects sum to at most `(5/2) c C_H(d) s^{1/2} · A 3^{m/2} [g]_{W^{1/2,∞}(z+□_m)}`.
The geometric sum is GMC's `Section6Holder.sum_Icc_three_parent_half_le`. -/
theorem folded_source_defect_sum_le {d : ℕ} (hd : 2 ≤ d) (m : ℕ) (z : SpatialCoordinates d)
    (hR : (0 : ℝ) < 3 ^ m) (g : SpatialCoordinates d → Fin d → ℝ)
    (hg : MemHolder (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) (1 / 2) g) :
    ∀ s : ℝ, 0 < s → s ≤ (1 / 4 : ℝ) → ∀ c : ℝ, 0 ≤ c →
    ∀ n top : ℕ, n ≤ top → top ≤ m →
    ∀ a0 : ℕ → ℝ, (∀ j, 0 < a0 j) →
    ∀ A : ℝ, (∀ j : ℕ, n ≤ j → j ≤ top → (a0 j)⁻¹ ≤ A) →
    ∀ D : ℤ → ℝ, (∀ j ∈ Finset.Icc (n : ℤ) (top : ℤ), D j = 0 ∨
        D j = c * (a0 j.toNat)⁻¹ * (3 : ℝ) ^ (s * (j.toNat : ℕ)) *
          (fractionalSeminormOn (truncatedCube d m (j.toNat : ℕ) 0) s
            (fun y => g (y + z))).toReal) →
      ∑ j ∈ Finset.Icc (n : ℤ) (top : ℤ), D j ≤
        (5 / 2 : ℝ) * c * Section6ExcessDecay.fractionalHolderConst d * Real.sqrt s *
          (A * (3 : ℝ) ^ ((m : ℝ) / 2) *
            halfHolderSeminorm
              (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) g) := by
  intro s hs0 hs c hc n top hnt htm a0 ha0 A hA D hD
  set G : ℝ := halfHolderSeminorm (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) g
    with hGdef
  have hG0 : 0 ≤ G := by
    rw [hGdef, ← folded_source_holderSeminormOn_eq m z hR g]
    exact Section6ExcessDecay.holderSeminormOn_nonneg (folded_source_memHolder m z hR g hg)
  set CH : ℝ := Section6ExcessDecay.fractionalHolderConst d * Real.sqrt s with hCHdef
  have hCH0 : 0 ≤ CH :=
    mul_nonneg (Section6ExcessDecay.fractionalHolderConst_nonneg d) (Real.sqrt_nonneg s)
  have hA0 : 0 ≤ A := le_trans (inv_nonneg.2 (ha0 n).le) (hA n le_rfl hnt)
  set B : ℝ := A * (3 : ℝ) ^ ((m : ℝ) / 2) * G with hBdef
  have hB0 : 0 ≤ B := mul_nonneg (mul_nonneg hA0 (Real.rpow_nonneg (by norm_num) _)) hG0
  have hterm : ∀ j ∈ Finset.Icc (n : ℤ) (top : ℤ),
      D j ≤ c * CH * B * (3 : ℝ) ^ (-(((m - j : ℤ) : ℝ) / 2)) := by
    intro j hj
    have hw0 : 0 ≤ (3 : ℝ) ^ (-(((m - j : ℤ) : ℝ) / 2)) := Real.rpow_nonneg (by norm_num) _
    have hrhs0 : 0 ≤ c * CH * B * (3 : ℝ) ^ (-(((m - j : ℤ) : ℝ) / 2)) :=
      mul_nonneg (mul_nonneg (mul_nonneg hc hCH0) hB0) hw0
    rcases hD j hj with h0 | hdef
    · rw [h0]
      exact hrhs0
    obtain ⟨hnj, hjtop⟩ := Finset.mem_Icc.1 hj
    obtain ⟨jn, rfl⟩ : ∃ jn : ℕ, j = (jn : ℤ) :=
      ⟨j.toNat, (Int.toNat_of_nonneg (le_trans (by positivity) hnj)).symm⟩
    have hnjn : n ≤ jn := by exact_mod_cast hnj
    have hjntop : jn ≤ top := by exact_mod_cast hjtop
    rw [hdef, Int.toNat_natCast]
    have hwin := folded_source_window_le_nat hd m z hR g hg s hs0 hs jn
    have hinv0 : 0 ≤ (a0 jn)⁻¹ := inv_nonneg.2 (ha0 jn).le
    have hcast : (((m : ℤ) - (jn : ℤ) : ℤ) : ℝ) = (m : ℝ) - (jn : ℝ) := by push_cast; ring
    rw [hcast]
    set w : ℝ := (3 : ℝ) ^ (-(((m : ℝ) - (jn : ℝ)) / 2)) with hwdef
    have hw0' : 0 ≤ w := Real.rpow_nonneg (by norm_num) _
    have hM0 : 0 ≤ (3 : ℝ) ^ ((m : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
    set F : ℝ := (3 : ℝ) ^ (s * (jn : ℝ)) *
      (fractionalSeminormOn (truncatedCube d m jn 0) s (fun y => g (y + z))).toReal with hFdef
    have hstep1 : c * (a0 jn)⁻¹ * F ≤ c * (a0 jn)⁻¹ * (CH * w * ((3 : ℝ) ^ ((m : ℝ) / 2) * G)) :=
      mul_le_mul_of_nonneg_left hwin (mul_nonneg hc hinv0)
    have hstep2 : c * (a0 jn)⁻¹ * (CH * w * ((3 : ℝ) ^ ((m : ℝ) / 2) * G)) ≤
        c * A * (CH * w * ((3 : ℝ) ^ ((m : ℝ) / 2) * G)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hA jn hnjn hjntop) hc)
        (mul_nonneg (mul_nonneg hCH0 hw0') (mul_nonneg hM0 hG0))
    have hassoc : c * (a0 jn)⁻¹ * (3 : ℝ) ^ (s * (jn : ℝ)) *
        (fractionalSeminormOn (truncatedCube d m jn 0) s (fun y => g (y + z))).toReal =
        c * (a0 jn)⁻¹ * F := by
      rw [hFdef]; ring
    have hfinal : c * A * (CH * w * ((3 : ℝ) ^ ((m : ℝ) / 2) * G)) = c * CH * B * w := by
      rw [hBdef]; ring
    rw [hassoc]
    exact le_trans hstep1 (le_trans hstep2 (le_of_eq hfinal))
  have hgeo := Section6Holder.sum_Icc_three_parent_half_le (m := (m : ℤ))
    (show (n : ℤ) ≤ (top : ℤ) by exact_mod_cast hnt)
  have hlast : (3 : ℝ) ^ (-((((m : ℤ) - (top : ℤ) : ℤ) : ℝ) / 2)) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
    have : (0 : ℝ) ≤ (((m : ℤ) - (top : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast (show (0 : ℤ) ≤ (m : ℤ) - (top : ℤ) by omega)
    linarith
  have hK0 : 0 ≤ c * CH * B := mul_nonneg (mul_nonneg hc hCH0) hB0
  calc ∑ j ∈ Finset.Icc (n : ℤ) (top : ℤ), D j
      ≤ ∑ j ∈ Finset.Icc (n : ℤ) (top : ℤ),
          c * CH * B * (3 : ℝ) ^ (-(((m - j : ℤ) : ℝ) / 2)) := Finset.sum_le_sum hterm
    _ = c * CH * B * ∑ j ∈ Finset.Icc (n : ℤ) (top : ℤ),
          (3 : ℝ) ^ (-(((m - j : ℤ) : ℝ) / 2)) := by rw [Finset.mul_sum]
    _ ≤ c * CH * B * ((5 / 2 : ℝ) * 1) :=
        mul_le_mul_of_nonneg_left (le_trans hgeo
          (mul_le_mul_of_nonneg_left hlast (by norm_num))) hK0
    _ = (5 / 2 : ℝ) * c * Section6ExcessDecay.fractionalHolderConst d * Real.sqrt s * B := by
        rw [hCHdef]; ring

end SubdiffusiveProcess.Lane4
