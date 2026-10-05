module

public import SubdiffusiveProcess.Section10.InitialSimplexEnergyCube
public import SubdiffusiveProcess.Section10.InitialSimplexEnergyPacking

@[expose] public section

/-!
# Uniform initial simplex energy from a geometric packing

All probabilistic and scalar inputs are discharged using the genuine GMCModel
and the proved Section 3/4/5 providers. The sole supplied object is the finite
geometric packing: it contains no energy estimate. Per-depth energy is paid
with the geometric ratio 2/3. The affine remainder is handled separately using
the reciprocal lower bound, including ell=0.
-/

namespace SubdiffusiveProcess.Section10

open Homogenization Homogenization.Book MeasureTheory Set
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec Mat TriadicCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

/-- The source's exponential annealed-ordering loss is at most 2^i under the
standing GMC disorder range. -/
theorem exp_two_tauSq_nat_le (M : GMCModel d) (i : ℕ) :
    Real.exp (2 * tauSq M.P * (i : ℝ)) ≤ (2 : ℝ) ^ i := by
  rw [mul_comm (2 * tauSq M.P), Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos _).le (exp_two_tauSq_le_two M) i

/-- The finite version of the convergent source series, with a uniform bound. -/
theorem sum_two_thirds_pow_le_three (N : ℕ) :
    ∑ i ∈ Finset.range N, (2 / 3 : ℝ) ^ i ≤ 3 := by
  have heq : ∀ N : ℕ,
      (∑ i ∈ Finset.range N, (2 / 3 : ℝ) ^ i) + 3 * (2 / 3 : ℝ) ^ N = 3 := by
    intro N
    induction N with
    | zero => norm_num
    | succ N ih =>
        rw [Finset.sum_range_succ, pow_succ]
        nlinarith
  have hpos : 0 ≤ (2 / 3 : ℝ) ^ N := pow_nonneg (by norm_num) N
  linarith [heq N]

/-- Volume fractions and local growth losses combine into a bounded sum. -/
theorem packing_depth_weight_sum_le {ell : ℕ} {pi : Equiv.Perm (Fin d)}
    {K : ℝ} (hK : 0 ≤ K) (P : InitialSimplexCubePacking ell pi K) :
    (∑ Q ∈ P.cubes, (volume (openCubeSet Q)).toReal /
      (volume (initialSimplex ell pi).openCarrier).toReal * (2 : ℝ) ^ P.depth Q) ≤ 3 * K := by
  classical
  let v : TriadicCube d → ℝ := fun Q => (volume (openCubeSet Q)).toReal /
    (volume (initialSimplex ell pi).openCarrier).toReal
  have hmap : ∀ Q ∈ P.cubes, P.depth Q ∈ Finset.range (ell + 1) :=
    fun Q hQ => Finset.mem_range.mpr (Nat.lt_succ_of_le (P.depth_le Q hQ))
  calc
    _ = ∑ i ∈ Finset.range (ell + 1),
        ∑ Q ∈ P.cubes.filter (fun Q => P.depth Q = i), v Q * (2 : ℝ) ^ P.depth Q :=
      (Finset.sum_fiberwise_of_maps_to hmap (fun Q => v Q * (2 : ℝ) ^ P.depth Q)).symm
    _ = ∑ i ∈ Finset.range (ell + 1),
        (∑ Q ∈ P.cubes.filter (fun Q => P.depth Q = i), v Q) * (2 : ℝ) ^ i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro Q hQ
      rw [(Finset.mem_filter.mp hQ).2]
    _ ≤ ∑ i ∈ Finset.range (ell + 1), K * (2 / 3 : ℝ) ^ i := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ (K * (1 / 3 : ℝ) ^ i) * (2 : ℝ) ^ i :=
          mul_le_mul_of_nonneg_right (P.depth_fraction i) (pow_nonneg (by norm_num) i)
        _ = K * (2 / 3 : ℝ) ^ i := by
          rw [mul_assoc, ← mul_pow]
          congr 2
          norm_num
    _ = K * ∑ i ∈ Finset.range (ell + 1), (2 / 3 : ℝ) ^ i := by rw [Finset.mul_sum]
    _ ≤ K * 3 := mul_le_mul_of_nonneg_left (sum_two_thirds_pow_le_three _) hK
    _ = 3 * K := mul_comm _ _

/-- The reciprocal lower bound pays for the affine remainder with one factor
2, uniformly in ell. This includes ell=0. -/
theorem one_le_two_pow_mul_ahom (M : GMCModel d) (ell : ℕ) :
    1 ≤ (2 : ℝ) ^ (ell + 1) * ahom M ell := by
  have hlow : Real.exp (-(2 * tauSq M.P * ((ell + 1 : ℕ) : ℝ))) ≤ ahom M ell := by
    apply le_trans _ (SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower M ell)
    apply Real.exp_le_exp.mpr
    have htau := M.G4.tauSq_pos.le
    have hell : 0 ≤ (ell : ℝ) := Nat.cast_nonneg ell
    push_cast
    nlinarith
  have h1 := mul_le_mul_of_nonneg_left hlow
    (Real.exp_pos (2 * tauSq M.P * ((ell + 1 : ℕ) : ℝ))).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right (exp_two_tauSq_nat_le M (ell + 1))
    (ahom_pos M ell).le)

/-- The affine competitor has expected normalized energy exactly |p|². -/
theorem expectedAffineDirichletEnergy_le_vecNormSq (M : GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (p : Vec d) :
    expectedAffineDirichletEnergy M L U p ≤ vecNormSq p := by
  have h := expectedAffineDirichletEnergy_le_packing (ι := Unit) M L U ∅
    (fun _ => U) (fun _ => L) (by simp) (by simp) (by simp) p
  simpa only [Finset.sum_empty, zero_add, packingRemainder, Finset.notMem_empty,
    iUnion_of_empty, iUnion_empty, sdiff_empty, div_self (volume_toReal_pos U).ne',
    one_mul] using h

/-- Complete initial simplex bound at ell=0 with the explicit constant 2.
It needs no geometric supplier or caller energy estimate. -/
theorem initialSimplexExpectedEnergy_zero_le (M : GMCModel d)
    (pi : Equiv.Perm (Fin d)) (p : Vec d) :
    initialSimplexExpectedEnergy M 0 pi p ≤ 2 * ahom M 0 * vecNormSq p := by
  have h := one_le_two_pow_mul_ahom M 0
  norm_num only [zero_add, pow_one] at h
  exact (expectedAffineDirichletEnergy_le_vecNormSq M 0
    (kuhnCellDomain (initialSimplex 0 pi)) p).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right h (vecNormSq_nonneg p))

/-- The uncovered volume's affine energy is bounded without omitting ell=0. -/
theorem packing_affine_remainder_le {ell : ℕ} {pi : Equiv.Perm (Fin d)}
    {K : ℝ} (hK : 0 ≤ K) (P : InitialSimplexCubePacking ell pi K)
    (M : GMCModel d) (p : Vec d) :
    (volume (packingRemainder (initialSimplex ell pi).openCarrier P.cubes openCubeSet)).toReal /
      (volume (initialSimplex ell pi).openCarrier).toReal * vecNormSq p ≤
        2 * K * ahom M ell * vecNormSq p := by
  have hgeom : (2 / 3 : ℝ) ^ ell ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h1 := one_le_two_pow_mul_ahom M ell
  have hpow : (1 / 3 : ℝ) ^ ell * (2 : ℝ) ^ (ell + 1) = 2 * (2 / 3 : ℝ) ^ ell := by
    rw [pow_succ]
    calc
      (1 / 3 : ℝ) ^ ell * ((2 : ℝ) ^ ell * 2) =
          2 * ((1 / 3 : ℝ) ^ ell * (2 : ℝ) ^ ell) := by ring
      _ = _ := by rw [← mul_pow]; congr 2; norm_num
  have hscalar : K * (1 / 3 : ℝ) ^ ell ≤ 2 * K * ahom M ell := by
    calc
      _ ≤ (K * (1 / 3 : ℝ) ^ ell) * ((2 : ℝ) ^ (ell + 1) * ahom M ell) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left h1
          (mul_nonneg hK (pow_nonneg (by norm_num) ell))
      _ = (2 * K * ahom M ell) * (2 / 3 : ℝ) ^ ell := by rw [← mul_assoc, mul_assoc K, hpow]; ring
      _ ≤ 2 * K * ahom M ell := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hgeom
          (mul_nonneg (mul_nonneg (by norm_num) hK) (ahom_pos M ell).le)
  exact mul_le_mul_of_nonneg_right (P.remainder_fraction.trans hscalar) (vecNormSq_nonneg p)

/-- Complete probabilistic/scalar supplier for D1. The remaining input is
only the explicit finite geometric packing; all coefficient energy estimates
come from proved source providers for the actual GMCModel. Constants precede
the model, scale, permutation and slope. -/
theorem exists_initialSimplexEnergy_constants_of_packing (d : ℕ) (K : ℝ) (hK : 1 ≤ K) :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 →
      ∀ (ell : ℕ) (pi : Equiv.Perm (Fin d)),
        InitialSimplexCubePacking ell pi K → ∀ p : Vec d,
          initialSimplexExpectedEnergy M ell pi p ≤ C * ahom M ell * vecNormSq p := by
  obtain ⟨delta0, B, hdelta0, hB, hcube⟩ := exists_initialCubeEnergy_constants d
  let C := 3 * K * B + 2 * K
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  have hC : 0 < C := by dsimp only [C]; nlinarith
  refine ⟨delta0, C, hdelta0, hC, ?_⟩
  intro M hM ell pi P p
  let U := kuhnCellDomain (initialSimplex ell pi)
  let v : TriadicCube d → ℝ := fun Q => (volume (openCubeSet Q)).toReal /
    (volume (initialSimplex ell pi).openCarrier).toReal
  have hlocal : ∀ Q ∈ P.cubes,
      expectedAffineDirichletEnergy M (ell - P.depth Q) (Ch02.cubeDomain Q) p ≤
        B * ahom M ell * vecNormSq p * (2 : ℝ) ^ P.depth Q := by
    intro Q hQ
    have he := hcube M hM (ell - P.depth Q) Q (P.scale_eq Q hQ) p
    have ha := ahom_le_exp_mul_of_le M (Nat.sub_le ell (P.depth Q))
    rw [Nat.sub_sub_self (P.depth_le Q hQ)] at ha
    have ha' : ahom M (ell - P.depth Q) ≤ (2 : ℝ) ^ P.depth Q * ahom M ell :=
      ha.trans (mul_le_mul_of_nonneg_right (exp_two_tauSq_nat_le M (P.depth Q))
        (ahom_pos M ell).le)
    calc
      _ ≤ B * ((2 : ℝ) ^ P.depth Q * ahom M ell) * vecNormSq p :=
        he.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha' hB0)
          (vecNormSq_nonneg p))
      _ = _ := by ring
  have hpacking := expectedAffineDirichletEnergy_le_packing M ell U P.cubes
    (fun Q => Ch02.cubeDomain Q) (fun Q => ell - P.depth Q)
    P.subset P.disjoint (fun Q _ => Nat.sub_le ell (P.depth Q)) p
  have hsum : (∑ Q ∈ P.cubes, v Q *
      expectedAffineDirichletEnergy M (ell - P.depth Q) (Ch02.cubeDomain Q) p) ≤
        (3 * K * B) * ahom M ell * vecNormSq p := by
    calc
      _ ≤ ∑ Q ∈ P.cubes, v Q * (B * ahom M ell * vecNormSq p * (2 : ℝ) ^ P.depth Q) :=
        Finset.sum_le_sum (fun Q hQ => mul_le_mul_of_nonneg_left (hlocal Q hQ)
          (div_nonneg ENNReal.toReal_nonneg (volume_toReal_pos U).le))
      _ = (B * ahom M ell * vecNormSq p) *
          (∑ Q ∈ P.cubes, v Q * (2 : ℝ) ^ P.depth Q) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro Q _
        ring
      _ ≤ (B * ahom M ell * vecNormSq p) * (3 * K) :=
        mul_le_mul_of_nonneg_left (packing_depth_weight_sum_le hK0 P)
          (mul_nonneg (mul_nonneg hB0 (ahom_pos M ell).le) (vecNormSq_nonneg p))
      _ = _ := by ring
  calc
    initialSimplexExpectedEnergy M ell pi p ≤
        (∑ Q ∈ P.cubes, v Q *
          expectedAffineDirichletEnergy M (ell - P.depth Q) (Ch02.cubeDomain Q) p) +
        (volume (packingRemainder (initialSimplex ell pi).openCarrier P.cubes openCubeSet)).toReal /
          (volume (initialSimplex ell pi).openCarrier).toReal * vecNormSq p := hpacking
    _ ≤ (3 * K * B) * ahom M ell * vecNormSq p +
          2 * K * ahom M ell * vecNormSq p :=
        add_le_add hsum (packing_affine_remainder_le hK0 P M p)
    _ = C * ahom M ell * vecNormSq p := by dsimp only [C]; ring

end
end SubdiffusiveProcess.Section10
