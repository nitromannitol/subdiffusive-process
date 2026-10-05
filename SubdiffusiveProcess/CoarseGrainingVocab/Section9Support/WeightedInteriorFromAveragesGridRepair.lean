
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

@[expose] public section




set_option autoImplicit false
open Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.Section9 (centeredAxisCube)

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The repaired hypothesis is satisfiable in every dimension: the `64 ^ d`
scaled offsets `j / 64` cover every cube in the middle sixteenth of a grid cube
of comparable size, with Lebesgue number `192`. -/
theorem exists_hasMiddleSixteenthCover (d : ℕ) :
    ∃ grid : Finset (Vec d), HasMiddleSixteenthCover grid 192 := by
  classical
  refine ⟨(Finset.univ : Finset (Fin d → Fin 64)).image
      (fun j => (fun i => ((j i : ℕ) : ℝ) / 64 : Vec d)), by norm_num, ?_⟩
  intro x rho hrho
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow (x := 64 * rho) (y := (3 : ℝ))
    (by positivity) (by norm_num)
  set m : ℤ := n + 1 with hm
  have hpow : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) _
  have hupper : 64 * rho < (3 : ℝ) ^ m := hn2
  have hlower : (3 : ℝ) ^ m ≤ 192 * rho := by
    have h3 : (3 : ℝ) ^ m = 3 * (3 : ℝ) ^ n := by
      rw [hm, zpow_add₀ (by norm_num : (3:ℝ) ≠ 0), zpow_one]; ring
    rw [h3]; linarith
  set t : Fin d → ℤ := fun i => round (64 * x i / (3 : ℝ) ^ m) with ht
  set k : Fin d → ℤ := fun i => t i / 64 with hk
  set jj : Fin d → ℤ := fun i => t i % 64 with hj
  have hj0 : ∀ i, 0 ≤ jj i := fun i => Int.emod_nonneg _ (by norm_num)
  have hj64 : ∀ i, jj i < 64 := fun i => Int.emod_lt_of_pos _ (by norm_num)
  have hsplit : ∀ i, 64 * k i + jj i = t i := fun i => Int.mul_ediv_add_emod (t i) 64
  set g : Vec d := fun i => (((jj i).toNat : ℕ) : ℝ) / 64 with hg
  have hgmem : g ∈ (Finset.univ : Finset (Fin d → Fin 64)).image
      (fun j => (fun i => ((j i : ℕ) : ℝ) / 64 : Vec d)) := by
    refine Finset.mem_image.mpr ⟨fun i => ⟨(jj i).toNat, ?_⟩, Finset.mem_univ _, rfl⟩
    have := hj64 i
    omega
  set y : Vec d := fun i => (3 : ℝ) ^ m * (g i + (k i : ℝ)) with hy
  have hycoord : ∀ i, y i = (3 : ℝ) ^ m * (t i : ℝ) / 64 := by
    intro i
    have hcast : (((jj i).toNat : ℕ) : ℝ) = (jj i : ℝ) := by
      have := hj0 i
      exact_mod_cast Int.toNat_of_nonneg this
    have : ((64 : ℝ) * (k i : ℝ) + (jj i : ℝ)) = (t i : ℝ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (hsplit i)
    rw [hy, hg]
    simp only
    rw [hcast]
    field_simp
    linarith [this]
  have hclose : ∀ i, |x i - y i| ≤ (3 : ℝ) ^ m / 128 := by
    intro i
    have hround : |64 * x i / (3 : ℝ) ^ m - (t i : ℝ)| ≤ 1 / 2 := abs_sub_round _
    have hrw : x i - y i = ((3 : ℝ) ^ m / 64) * (64 * x i / (3 : ℝ) ^ m - (t i : ℝ)) := by
      rw [hycoord i]; field_simp
    rw [hrw, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (3 : ℝ) ^ m / 64)]
    calc (3 : ℝ) ^ m / 64 * |64 * x i / (3 : ℝ) ^ m - (t i : ℝ)|
        ≤ (3 : ℝ) ^ m / 64 * (1 / 2) := by
          exact mul_le_mul_of_nonneg_left hround (by positivity)
      _ = (3 : ℝ) ^ m / 128 := by ring
  refine ⟨y, (3 : ℝ) ^ m, ⟨g, hgmem, m, k, rfl, rfl⟩, by linarith, hlower, ?_⟩
  intro w hw i _
  have hwi := hw i (Set.mem_univ i)
  simp only [Set.mem_Ioo] at hwi ⊢
  have h1 := (abs_le.mp (hclose i)).1
  have h2 := (abs_le.mp (hclose i)).2
  constructor <;> linarith [hwi.1, hwi.2]

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
