module

public import SubdiffusiveProcess.Lane1.TriadicGrid
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic

@[expose] public section

/-! Countable padded roots and their finite buffered-coordinate catalogues.
The existing triadic grid supplies the spatial carrier and cardinality bound.
The catalogues cover specified prefixes; no probabilistic estimate is made.
-/
open scoped BigOperators
noncomputable section
namespace SubdiffusiveProcess

/-- A root records its mesh generation, integer spatial index, and radius index. -/
abbrev PrefixRootIndex (d : ℕ) := ℕ × ((Fin d → ℤ) × ℕ)

/-- The physical centre of a root with fixed padding. -/
def prefixRootCentre {d : ℕ} (J : ℕ) (p : PrefixRootIndex d) : SpatialCoordinates d :=
  gridPoint (p.1 + J) p.2.1

/-- The physical level of a root with fixed padding. -/
def prefixRootLevel {d : ℕ} (J : ℕ) (p : PrefixRootIndex d) : ℤ :=
  (p.2.2 : ℤ) - J

/-- All padded roots in the spatial box at one target generation. -/
def prefixRootCatalogue (d : ℕ) (rho : ℝ) (J n : ℕ) : Finset (PrefixRootIndex d) := by
  classical
  exact ((gridIndices d rho (n + J)) ×ˢ Finset.range (n + J + 1)).image
    (fun ak => (n, ak))

/-- One fixed constant controls the root catalogue at every generation. -/
def prefixRootCountConstant (d : ℕ) (rho : ℝ) (J : ℕ) : ℝ :=
  ((J : ℝ) + 1) * ((2 * rho + 3) * (3 : ℝ) ^ J) ^ d

/-- The root-count constant is nonnegative for a nonnegative spatial radius. -/
theorem prefixRootCountConstant_nonneg (d : ℕ) (rho : ℝ) (J : ℕ) (hrho : 0 ≤ rho) :
    0 ≤ prefixRootCountConstant d rho J := by
  unfold prefixRootCountConstant
  positivity

/-- Membership identifies exactly the generation, spatial index, and permitted radius index. -/
theorem mem_prefixRootCatalogue {d : ℕ} (rho : ℝ) (J n : ℕ) (p : PrefixRootIndex d) :
    p ∈ prefixRootCatalogue d rho J n ↔
      p.1 = n ∧ p.2.1 ∈ gridIndices d rho (n + J) ∧ p.2.2 ≤ n + J := by
  classical
  constructor
  · intro hp
    obtain ⟨ak, hak, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨rfl, (Finset.mem_product.mp hak).1,
      Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hak).2)⟩
  · rintro ⟨hn, ha, hk⟩
    apply Finset.mem_image.mpr
    refine ⟨p.2, Finset.mem_product.mpr ⟨ha, Finset.mem_range.mpr (by omega)⟩, ?_⟩
    exact Prod.ext hn.symm rfl

/-- The root catalogue has a linear polynomial cost times the spatial triadic growth. -/
theorem prefixRootCatalogue_card_le (d : ℕ) (rho : ℝ) (hrho : 0 ≤ rho) (J n : ℕ) :
    ((prefixRootCatalogue d rho J n).card : ℝ) ≤
      prefixRootCountConstant d rho J * ((n : ℝ) + 1) * (3 : ℝ) ^ (d * n) := by
  classical
  have hcard : (prefixRootCatalogue d rho J n).card ≤
      (gridIndices d rho (n + J)).card * (n + J + 1) := by
    unfold prefixRootCatalogue
    exact Finset.card_image_le.trans_eq (by rw [Finset.card_product, Finset.card_range])
  have hcardR : ((prefixRootCatalogue d rho J n).card : ℝ) ≤
      ((gridIndices d rho (n + J)).card : ℝ) * (n + J + 1) := by exact_mod_cast hcard
  have hgrid := card_gridIndices_le (d := d) hrho (n + J)
  rw [zpow_natCast, pow_add, mul_pow, mul_pow, ← pow_mul] at hgrid
  have hpoly : (n : ℝ) + J + 1 ≤ ((J : ℝ) + 1) * ((n : ℝ) + 1) := by
    nlinarith only [mul_nonneg (Nat.cast_nonneg (α := ℝ) J) (Nat.cast_nonneg (α := ℝ) n)]
  have hm := mul_le_mul hgrid hpoly (by positivity) (by positivity)
  refine hcardR.trans (hm.trans_eq ?_)
  unfold prefixRootCountConstant
  rw [mul_pow, ← pow_mul]
  rw [Nat.mul_comm n d, Nat.mul_comm J d]
  ring

/-- The root count in the real-exponent form used by the probability bank. -/
theorem prefixRootCatalogue_card_le_rpow (d : ℕ) (rho : ℝ) (hrho : 0 ≤ rho)
    (J n : ℕ) :
    ((prefixRootCatalogue d rho J n).card : ℝ) ≤
      prefixRootCountConstant d rho J * ((n : ℝ) + 1) ^ 1 *
        (3 : ℝ) ^ ((d : ℝ) * n) := by
  simpa only [pow_one, ← Nat.cast_mul, Real.rpow_natCast] using
    prefixRootCatalogue_card_le d rho hrho J n

/-- All buffered coordinates through a fixed physical depth, for all roots up to that generation. -/
def prefixCoordinateCatalogue (d : ℕ) (rho : ℝ) (J buffer T : ℕ) :
    Finset (PrefixRootIndex d × ℤ) := by
  classical
  exact ((Finset.range (T + 1)).biUnion fun n =>
    (prefixRootCatalogue d rho J n) ×ˢ Finset.Icc (-(buffer : ℤ)) ((T : ℤ) + J)).filter
      (fun p => prefixRootLevel J p.1 + p.2 ≤ T)

/-- Every catalogued coordinate is below the stated physical depth. -/
theorem prefixCoordinateCatalogue_level {d : ℕ} (rho : ℝ) (J buffer T : ℕ)
    (p : PrefixRootIndex d × ℤ) (hp : p ∈ prefixCoordinateCatalogue d rho J buffer T) :
    prefixRootLevel J p.1 + p.2 ≤ T := (Finset.mem_filter.mp hp).2

/-- Every buffered prefix ending below the cutoff belongs to the coordinate catalogue. -/
theorem prefixCoordinateCatalogue_covers {d : ℕ} (rho : ℝ) (J buffer T n len : ℕ)
    (p : PrefixRootIndex d) (hp : p ∈ prefixRootCatalogue d rho J n) (hn : n ≤ T)
    (hend : prefixRootLevel J p + (len : ℤ) + buffer ≤ T)
    (j : ℤ) (hj : j ∈ Finset.Icc (-(buffer : ℤ)) ((len : ℤ) + buffer)) :
    (p, j) ∈ prefixCoordinateCatalogue d rho J buffer T := by
  classical
  apply Finset.mem_filter.mpr
  have hjlo := (Finset.mem_Icc.mp hj).1
  have hjhi := (Finset.mem_Icc.mp hj).2
  have hjT : j ≤ (T : ℤ) + J := by
    unfold prefixRootLevel at hend
    omega
  refine ⟨Finset.mem_biUnion.mpr ⟨n, Finset.mem_range.mpr (by omega),
    Finset.mem_product.mpr ⟨hp, Finset.mem_Icc.mpr ⟨hjlo, hjT⟩⟩⟩, ?_⟩
  change prefixRootLevel J p + j ≤ (T : ℤ)
  omega

/-- The coordinate catalogue has only three polynomial factors beyond the spatial triadic growth. -/
theorem prefixCoordinateCatalogue_card_le (d : ℕ) (rho : ℝ) (hrho : 0 ≤ rho)
    (J buffer T : ℕ) :
    ((prefixCoordinateCatalogue d rho J buffer T).card : ℝ) ≤
      (prefixRootCountConstant d rho J * ((J : ℝ) + buffer + 1)) *
        ((T : ℝ) + 1) ^ 3 * (3 : ℝ) ^ (d * T) := by
  classical
  let S : Finset ℤ := Finset.Icc (-(buffer : ℤ)) ((T : ℤ) + J)
  have hS : S.card = T + J + buffer + 1 := by
    dsimp only [S]
    rw [Int.card_Icc]
    omega
  have hSbound : (S.card : ℝ) ≤ ((J : ℝ) + buffer + 1) * ((T : ℝ) + 1) := by
    rw [hS]
    push_cast
    have hprod := mul_nonneg (show (0 : ℝ) ≤ J + buffer by positivity) (Nat.cast_nonneg (α := ℝ) T)
    nlinarith only [hprod]
  have hroot n (hn : n ∈ Finset.range (T + 1)) :
      ((prefixRootCatalogue d rho J n).card : ℝ) ≤
        prefixRootCountConstant d rho J * ((T : ℝ) + 1) * (3 : ℝ) ^ (d * T) := by
    have hnT : n ≤ T := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    refine (prefixRootCatalogue_card_le d rho hrho J n).trans ?_
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.add_le_add_right hnT 1)
        (prefixRootCountConstant_nonneg d rho J hrho)
    · exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left d hnT)
    · positivity
    · exact mul_nonneg (prefixRootCountConstant_nonneg d rho J hrho) (by positivity)
  have hcard : (prefixCoordinateCatalogue d rho J buffer T).card ≤
      ∑ n ∈ Finset.range (T + 1), (prefixRootCatalogue d rho J n).card * S.card := by
    unfold prefixCoordinateCatalogue
    refine (Finset.card_filter_le _ _).trans ((Finset.card_biUnion_le).trans_eq ?_)
    apply Finset.sum_congr rfl
    intro n _
    exact Finset.card_product _ _
  have hcardR : ((prefixCoordinateCatalogue d rho J buffer T).card : ℝ) ≤
      ∑ n ∈ Finset.range (T + 1),
        ((prefixRootCatalogue d rho J n).card : ℝ) * (S.card : ℝ) := by exact_mod_cast hcard
  have hboundnonneg : 0 ≤
      prefixRootCountConstant d rho J * ((T : ℝ) + 1) * (3 : ℝ) ^ (d * T) :=
    mul_nonneg (mul_nonneg (prefixRootCountConstant_nonneg d rho J hrho)
      (by positivity)) (by positivity)
  have hsum := Finset.sum_le_sum (fun n hn =>
    mul_le_mul (hroot n hn) hSbound (Nat.cast_nonneg _) hboundnonneg)
  refine hcardR.trans (hsum.trans_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  ring

/-- A cutoff catalogue at depth floor(vN) has the stated entropy in vN. -/
theorem prefixCoordinateCatalogue_cutoff_card_le (d : ℕ) (rho : ℝ) (hrho : 0 ≤ rho)
    (J buffer N : ℕ) (v : ℝ) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    ((prefixCoordinateCatalogue d rho J buffer ⌊v * N⌋₊).card : ℝ) ≤
      (prefixRootCountConstant d rho J * ((J : ℝ) + buffer + 1)) *
        ((N : ℝ) + 1) ^ 3 * (3 : ℝ) ^ (((d : ℝ) * v) * N) := by
  have hfloor := Nat.floor_le (mul_nonneg hv (Nat.cast_nonneg (α := ℝ) N))
  have hvN : v * N ≤ (N : ℝ) := mul_le_of_le_one_left (Nat.cast_nonneg _) hv1
  have hpoly : ((⌊v * N⌋₊ : ℝ) + 1) ^ 3 ≤ ((N : ℝ) + 1) ^ 3 :=
    pow_le_pow_left₀ (by positivity) (add_le_add (hfloor.trans hvN) le_rfl) _
  have hpow : (3 : ℝ) ^ (d * ⌊v * N⌋₊) ≤ (3 : ℝ) ^ (((d : ℝ) * v) * N) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    calc (d : ℝ) * ⌊v * N⌋₊ ≤ (d : ℝ) * (v * N) :=
      mul_le_mul_of_nonneg_left hfloor (Nat.cast_nonneg _)
      _ = _ := (mul_assoc _ _ _).symm
  refine (prefixCoordinateCatalogue_card_le d rho hrho J buffer ⌊v * N⌋₊).trans ?_
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left hpoly
      (mul_nonneg (prefixRootCountConstant_nonneg d rho J hrho) (by positivity))
  · exact hpow
  · positivity
  · exact mul_nonneg
      (mul_nonneg (prefixRootCountConstant_nonneg d rho J hrho) (by positivity))
      (by positivity)

/-- Enumerating a finite catalogue by its cardinal preserves membership. -/
def finiteCatalogueEntry {α : Type*} (S : Finset α) (i : Fin S.card) : α :=
  (S.equivFin.symm i).val

/-- Every enumerated entry belongs to its finite catalogue. -/
theorem finiteCatalogueEntry_mem {α : Type*} (S : Finset α) (i : Fin S.card) :
    finiteCatalogueEntry S i ∈ S := (S.equivFin.symm i).property

/-- Every member of a finite catalogue occurs in its enumeration. -/
theorem finiteCatalogueEntry_surjective {α : Type*} (S : Finset α) (x : α)
    (hx : x ∈ S) : ∃ i : Fin S.card, finiteCatalogueEntry S i = x := by
  refine ⟨S.equivFin ⟨x, hx⟩, ?_⟩
  exact congrArg Subtype.val (S.equivFin.symm_apply_apply ⟨x, hx⟩)

end SubdiffusiveProcess
