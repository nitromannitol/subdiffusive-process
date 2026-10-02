import SubdiffusiveProcess.Besov.DetachTheta

/-!
# Counting on the overlap centres for the detach inequality

The overlap centres `S ∈ centersAtDepth Q₀ j` (`Q₀ = originCube d 0`) have their `3^d` neighbours
`nbr S δ` among the depth-`j+1` descendants of `Q₀`; the maps `S ↦ nbr S δ` are injective; and there are at
least `3^{d j}` centres.  Consequently the average over the centres of the block quantities
`theta (originCube d (S.scale+1)) (k+1) (f (· + c_S))` is at most `3^d · theta Q₀ (j+1+k) f`.
-/

open MeasureTheory
open Homogenization

namespace SubdiffusiveProcess.Besov.Detach

noncomputable section

theorem nbr_injective {d : ℕ} (δ : Fin d → Fin 3) :
    Function.Injective (fun S : TriadicCube d => nbr S δ) := by
  intro S S' h
  unfold nbr at h
  cases S with
  | mk s idx =>
  cases S' with
  | mk s' idx' =>
  simp only [TriadicCube.mk.injEq] at h ⊢
  refine ⟨h.1, ?_⟩
  funext i
  have := congrFun h.2 i
  omega

theorem mem_descendantsAtDepth_of_cubeSet_subset {d : ℕ} {Q R : TriadicCube d} {n : ℕ}
    (hscale : R.scale = Q.scale - (n : ℤ)) (hsub : cubeSet R ⊆ cubeSet Q) :
    R ∈ descendantsAtDepth Q n := by
  have hxR : cubeCenter R ∈ cubeSet R := by
    rw [Homogenization.cubeSet]
    simp only [Set.mem_setOf_eq]
    intro i
    have hs : 0 < cubeScaleFactor R := by
      rw [Homogenization.cubeScaleFactor]; positivity
    constructor <;> · simp only [cubeCenter]; nlinarith [hs]
  have hxQ : cubeCenter R ∈ cubeSet Q := hsub hxR
  have hxU := cubeSet_subset_iUnion_descendantsAtDepth Q n hxQ
  obtain ⟨P, hP, hxP⟩ := Set.mem_iUnion₂.mp hxU
  have hP' : P ∈ descendantsAtDepth Q n := hP
  have hPscale : P.scale = Q.scale - (n : ℤ) := scale_eq_sub_of_mem_descendantsAtDepth hP'
  have hRP : R = P := by
    by_contra hne
    exact (Set.disjoint_left.mp (disjoint_cubeSet_of_scale_eq_of_ne (by rw [hscale, hPscale]) hne)) hxR hxP
  rw [hRP]
  exact hP'

theorem cubeSet_nbr_subset_overlap {d : ℕ} (S : TriadicCube d) (δ : Fin d → Fin 3) :
    cubeSet (nbr S δ) ⊆ ScalarOverlap.cubeSet S := by
  intro x hx
  simp only [Homogenization.cubeSet, Set.mem_setOf_eq] at hx
  intro i
  obtain ⟨hlo, hhi⟩ := hx i
  have hscale : Homogenization.cubeScaleFactor (nbr S δ) = Homogenization.cubeScaleFactor S := by
    simp [nbr, Homogenization.cubeScaleFactor]
  rw [hscale] at hlo hhi
  simp only [nbr] at hlo hhi
  push_cast at hlo hhi
  have hs : 0 < Homogenization.cubeScaleFactor S := by
    rw [Homogenization.cubeScaleFactor]
    exact zpow_pos (by norm_num) _
  constructor
  · have h1 : (S.index i : ℝ) - 3 / 2 ≤ (S.index i : ℝ) + (δ i : ℝ) - 1 - 1 / 2 := by
      have : (0 : ℝ) ≤ (δ i : ℝ) := by positivity
      linarith
    exact le_trans (mul_le_mul_of_nonneg_right h1 hs.le) hlo
  · have h2 : (S.index i : ℝ) + (δ i : ℝ) - 1 + 1 / 2 ≤ (S.index i : ℝ) + 3 / 2 := by
      have hnat : (δ i : ℕ) ≤ 2 := by
        have := (δ i).isLt
        omega
      have hδ2 : (δ i : ℝ) ≤ 2 := by exact_mod_cast hnat
      linarith
    exact lt_of_lt_of_le hhi (mul_le_mul_of_nonneg_right h2 hs.le)

theorem nbr_mem_descendantsAtDepth {d : ℕ} {j : ℕ} {S : TriadicCube d}
    (hS : S ∈ ScalarOverlap.centersAtDepth (originCube d 0) j) (δ : Fin d → Fin 3) :
    nbr S δ ∈ descendantsAtDepth (originCube d 0) (j + 1) := by
  have hS' := ScalarOverlap.mem_centersAtDepth_iff.mp hS
  have hscale : (nbr S δ).scale = (originCube d 0).scale - ((j + 1 : ℕ) : ℤ) := by
    have := scale_eq_sub_of_mem_descendantsAtDepth hS'.1
    simpa [nbr] using this
  exact mem_descendantsAtDepth_of_cubeSet_subset hscale
    ((cubeSet_nbr_subset_overlap S δ).trans hS'.2)

theorem card_descendantsAtDepth_le_centers {d : ℕ} (j : ℕ) :
    (3 ^ d) ^ j ≤ (ScalarOverlap.centersAtDepth (originCube d 0) j).card := by
  calc (3 ^ d) ^ j = (descendantsAtDepth (originCube d 0) j).card := (descendantsAtDepth_card (originCube d 0) j).symm
    _ ≤ (ScalarOverlap.centersAtDepth (originCube d 0) j).card := ScalarOverlap.descendantsAtDepth_card_le_centersAtDepth_card (originCube d 0) j

theorem centers_scale {d : ℕ} {j : ℕ} {S : TriadicCube d}
    (hS : S ∈ ScalarOverlap.centersAtDepth (originCube d 0) j) :
    S.scale + 1 = -(j : ℤ) := by
  have h := ScalarOverlap.mem_centersAtDepth_iff.mp hS
  have hscale := scale_eq_sub_of_mem_descendantsAtDepth h.1
  simp only [originCube] at hscale
  omega

theorem block_sum_le {d : ℕ} (j : ℕ) (h : TriadicCube d → ℝ)
    (hh : ∀ P, 0 ≤ h P) :
    ∑ S ∈ ScalarOverlap.centersAtDepth (originCube d 0) j, ∑ δ : Fin d → Fin 3, h (nbr S δ) ≤
      (3 : ℝ) ^ d * ∑ P ∈ descendantsAtDepth (originCube d 0) (j + 1), h P := by
  have hcard : Fintype.card (Fin d → Fin 3) = 3 ^ d := by
    rw [Fintype.card_fun]
    simp
  calc
    ∑ S ∈ ScalarOverlap.centersAtDepth (originCube d 0) j, ∑ δ : Fin d → Fin 3, h (nbr S δ)
        = ∑ δ : Fin d → Fin 3, ∑ S ∈ ScalarOverlap.centersAtDepth (originCube d 0) j, h (nbr S δ) :=
          Finset.sum_comm
    _ ≤ ∑ δ : Fin d → Fin 3, ∑ P ∈ descendantsAtDepth (originCube d 0) (j + 1), h P := by
          apply Finset.sum_le_sum
          intro δ _
          have hinj : Set.InjOn (fun S : TriadicCube d => nbr S δ)
              ↑(ScalarOverlap.centersAtDepth (originCube d 0) j) :=
            fun a _ b _ hab => nbr_injective δ hab
          rw [← Finset.sum_image hinj]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro P hP
            rcases Finset.mem_image.mp hP with ⟨S, hS, rfl⟩
            exact nbr_mem_descendantsAtDepth hS δ
          · intro P _ _
            exact hh P
    _ = (Fintype.card (Fin d → Fin 3) : ℕ) •
          (∑ P ∈ descendantsAtDepth (originCube d 0) (j + 1), h P) := Finset.sum_const _
    _ = (3 : ℝ) ^ d * ∑ P ∈ descendantsAtDepth (originCube d 0) (j + 1), h P := by
          rw [hcard, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

theorem avg_theta_block_le {d : ℕ} (j k : ℕ) (f : Vec d → ℝ) :
    ScalarOverlap.centersAverage (originCube d 0) j
        (fun S => theta (originCube d (S.scale + 1)) (k + 1) (fun x => f (x + cubeCenter S))) ≤
      (3 : ℝ) ^ d * theta (originCube d 0) (j + 1 + k) f := by
  classical
  set 𝒮 := ScalarOverlap.centersAtDepth (originCube d 0) j with h𝒮
  have hcardpos : (0 : ℝ) < (𝒮.card : ℝ) := by
    exact_mod_cast ScalarOverlap.centersAtDepth_card_pos (originCube d 0) j
  have hcardge : ((3 : ℝ) ^ d) ^ j ≤ (𝒮.card : ℝ) := by
    have := card_descendantsAtDepth_le_centers (d := d) j
    exact_mod_cast this
  have h3d : (0 : ℝ) < (3 : ℝ) ^ d := by positivity
  have hθ : 0 ≤ theta (originCube d 0) (j + 1 + k) f := theta_nonneg _ _ _
  have h1 : ∑ S ∈ 𝒮, theta (originCube d (S.scale + 1)) (k + 1) (fun x => f (x + cubeCenter S)) =
      ((3 : ℝ) ^ d)⁻¹ * ∑ S ∈ 𝒮, ∑ δ : Fin d → Fin 3, theta (nbr S δ) k f := by
    simp_rw [theta_block]
    rw [← Finset.mul_sum]
  have h2 := block_sum_le j (fun P => theta P k f) (fun P => theta_nonneg P k f)
  have h4 := sum_theta_descendants (originCube d 0) (j + 1) k f
  have h5 : (j + 1 + k) = (j + 1) + k := rfl
  unfold ScalarOverlap.centersAverage
  show ((𝒮.card : ℝ))⁻¹ * ∑ S ∈ 𝒮, _ ≤ _
  rw [h1]
  have h6 : ∑ S ∈ 𝒮, ∑ δ : Fin d → Fin 3, theta (nbr S δ) k f ≤
      (3 : ℝ) ^ d * (((3 ^ d) ^ (j + 1) : ℕ) * theta (originCube d 0) (j + 1 + k) f) := by
    rw [← h4]
    exact h2
  calc ((𝒮.card : ℝ))⁻¹ * (((3 : ℝ) ^ d)⁻¹ * ∑ S ∈ 𝒮, ∑ δ : Fin d → Fin 3, theta (nbr S δ) k f)
      ≤ ((𝒮.card : ℝ))⁻¹ * (((3 : ℝ) ^ d)⁻¹ *
          ((3 : ℝ) ^ d * (((3 ^ d) ^ (j + 1) : ℕ) * theta (originCube d 0) (j + 1 + k) f))) := by
        gcongr
    _ = (((3 : ℝ) ^ d) ^ (j + 1) / (𝒮.card : ℝ)) * theta (originCube d 0) (j + 1 + k) f := by
        push_cast
        field_simp
    _ ≤ (3 : ℝ) ^ d * theta (originCube d 0) (j + 1 + k) f := by
        gcongr
        rw [div_le_iff₀ hcardpos, pow_succ]
        nlinarith [hcardge, h3d]

end

end SubdiffusiveProcess.Besov.Detach
