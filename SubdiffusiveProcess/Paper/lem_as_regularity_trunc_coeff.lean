module

public import SubdiffusiveProcess.Paper.lem_as_regularity_tail_reference
public import SubdiffusiveProcess.Paper.lem_as_regularity_reference_ratio
public import SubdiffusiveProcess.Analysis.SignedPrefix
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.Multiplier
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Observables

@[expose] public section

/-! The physical coefficient with the infrared field truncated at `L'` is a positive constant times
the cutoff field `a_{N+L'}` of the translated native sample; its tail coefficients are the
reference scalars of the physical coefficient, and Dirichlet solutions rescale with the constant. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set SubdiffusiveProcess SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance
open Homogenization hiding Vec
open scoped ENNReal BigOperators Pointwise
noncomputable section
namespace Paper

/-- The constant relating the truncated physical coefficient to the cutoff field. -/
def aux_lem_as_regularity_trunc_coeff_const {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (omega : BilateralField d) (N L' : ℕ) : ℝ :=
  (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
    Real.exp ((L' : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P -
      ∑ n ∈ Finset.range L', omega (Int.ofNat (n + 1)) 0)

theorem aux_lem_as_regularity_trunc_coeff_const_pos {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (omega : BilateralField d) (N L' : ℕ) :
    0 < aux_lem_as_regularity_trunc_coeff_const M omega N L' :=
  mul_pos (inv_pos.2 (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _)

/-- The native sample read at the translated point is the layer of `omega` at the physical point. -/
theorem aux_lem_as_regularity_trunc_coeff_layer {d : ℕ} (omega : BilateralField d) (N : ℕ)
    (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (z0 y : SpatialCoordinates d) (k : ℕ) :
    translatePotentialSample ((3 : ℝ) ^ N • z0) eta k y =
      omega ((k : ℤ) - N) ((3 : ℝ) ^ (-(N : ℤ)) • y + z0) := by
  have hid : (3 : ℝ) ^ (-(N : ℤ)) * (3 : ℝ) ^ N = 1 := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    simp
  rw [translatePotentialSample_apply, hEta, smul_add, smul_smul, hid, one_smul]

/-- The truncated physical coefficient is a constant multiple of the cutoff field. -/
theorem lem_as_regularity_trunc_coeff {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (omega : BilateralField d) (N L' : ℕ)
    (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (z0 y : SpatialCoordinates d) :
    cutoffCoefficient M (fun om => infraredPartialSum om L') omega N
        ((3 : ℝ) ^ (-(N : ℤ)) • y + z0) =
      aux_lem_as_regularity_trunc_coeff_const M omega N L' *
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (N + L')
          (translatePotentialSample ((3 : ℝ) ^ N • z0) eta) y := by
  unfold cutoffCoefficient cutoffPotential SubdiffusiveProcess.Frozen.Assumptions.aCutoff
    aux_lem_as_regularity_trunc_coeff_const infraredPartialSum
  simp only [aux_lem_as_regularity_trunc_coeff_layer omega N eta hEta z0 y]
  set x : SpatialCoordinates d := (3 : ℝ) ^ (-(N : ℤ)) • y + z0 with hx
  have hsplit : ∑ k ∈ Finset.range (N + L' + 1), omega ((k : ℤ) - N) x =
      ∑ j ∈ Finset.range (N + 1), omega (-(Int.ofNat j)) x +
        ∑ n ∈ Finset.range L', omega (Int.ofNat (n + 1)) x := by
    rw [show N + L' + 1 = (N + 1) + L' by ring, Finset.sum_range_add]
    congr 1
    · rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k < N + 1 := Finset.mem_range.1 hk
      have : ((N + 1 - 1 - k : ℕ) : ℤ) - N = -(Int.ofNat k) := by
        simp only [Int.ofNat_eq_natCast]; omega
      rw [this]
    · refine Finset.sum_congr rfl fun n _ => ?_
      have : ((N + 1 + n : ℕ) : ℤ) - N = Int.ofNat (n + 1) := by
        simp only [Int.ofNat_eq_natCast]; push_cast; ring
      rw [this]
  have hH : (∑ n ∈ Finset.range L',
      (omega (Int.ofNat (n + 1)) -
        ContinuousMap.const (SpatialCoordinates d) ((omega (Int.ofNat (n + 1))) 0))) x =
      ∑ n ∈ Finset.range L', ((omega (Int.ofNat (n + 1))) x - (omega (Int.ofNat (n + 1))) 0) := by
    simp [ContinuousMap.sum_apply]
  have hcard : ∑ k ∈ Finset.range (N + L' + 1),
      ((omega ((k : ℤ) - N)) x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) =
      ∑ k ∈ Finset.range (N + L' + 1), (omega ((k : ℤ) - N)) x -
        ((N : ℝ) + L' + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast; ring
  rw [hH, hcard, hsplit, mul_assoc, ← Real.exp_add, Finset.sum_sub_distrib]
  congr 2
  ring

/-- The layers above scale `k` at a point, in signed-prefix form. -/
theorem aux_lem_as_regularity_trunc_coeff_layer_sum {d : ℕ} (omega : BilateralField d)
    (N L' k : ℕ) (hk : k ≤ N + L') (w : SpatialCoordinates d) :
    ∑ i ∈ Finset.Ico (k + 1) (N + L' + 1), (omega ((i : ℤ) - N)) w =
      ∑ n ∈ Finset.range L', (omega (Int.ofNat (n + 1))) w +
        signedPrefix (fun i => (omega (-i)) w) ((N : ℤ) - k) := by
  have h1 : ∑ i ∈ Finset.Ico (k + 1) (N + L' + 1), (omega ((i : ℤ) - N)) w =
      ∑ j ∈ Finset.Ico (-(L' : ℤ)) ((N : ℤ) - k), (omega (-j)) w := by
    refine Finset.sum_nbij' (fun i : ℕ => (N : ℤ) - i) (fun j : ℤ => ((N : ℤ) - j).toNat)
      ?_ ?_ ?_ ?_ ?_
    · intro i hi; simp only [Finset.mem_Ico] at hi ⊢; omega
    · intro j hj; simp only [Finset.mem_Ico] at hj ⊢; omega
    · intro i hi; simp only [Finset.mem_Ico] at hi; beta_reduce; omega
    · intro j hj; simp only [Finset.mem_Ico] at hj; beta_reduce; omega
    · intro i _
      rw [show -((N : ℤ) - i) = (i : ℤ) - N by ring]
  have h2 : ∑ j ∈ Finset.Ico (-(L' : ℤ)) 0, (omega (-j)) w =
      ∑ n ∈ Finset.range L', (omega (Int.ofNat (n + 1))) w := by
    refine Finset.sum_nbij' (fun j : ℤ => (-j - 1).toNat) (fun n : ℕ => -((n : ℤ) + 1))
      ?_ ?_ ?_ ?_ ?_
    · intro j hj; simp only [Finset.mem_Ico, Finset.mem_range] at hj ⊢; omega
    · intro n hn; simp only [Finset.mem_Ico, Finset.mem_range] at hn ⊢; omega
    · intro j hj; simp only [Finset.mem_Ico] at hj; beta_reduce; omega
    · intro n hn; beta_reduce; omega
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      have : (Int.ofNat ((-j - 1).toNat + 1)) = -j := by simp only [Int.ofNat_eq_natCast]; omega
      rw [this]
  have h3 := signedPrefix_sub (fun i => (omega (-i)) w) (-(L' : ℤ)) ((N : ℤ) - k) (by omega)
  have h4 : signedPrefix (fun i => (omega (-i)) w) (-(L' : ℤ)) =
      -∑ j ∈ Finset.Ico (-(L' : ℤ)) 0, (omega (-j)) w := by
    unfold signedPrefix
    split_ifs with h
    · have : (L' : ℤ) = 0 := by omega
      simp [this]
    · rfl
  rw [h1, ← h2]
  linarith

/-- The constant times the tail coefficient of the translated native sample is the physical
reference scalar. -/
theorem aux_lem_as_regularity_trunc_tail {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (omega : BilateralField d) (N L' k : ℕ) (hk : k ≤ N + L')
    (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (z0 w : SpatialCoordinates d) :
    aux_lem_as_regularity_trunc_coeff_const M omega N L' *
        tailCoefficient M (N + L') k (translatePotentialSample ((3 : ℝ) ^ N • z0) eta)
          ((3 : ℝ) ^ N • (w - z0)) =
      aux_in_deterministic_onestep_sref M (fun om => infraredPartialSum om L') omega N
        ((N : ℤ) - k) w := by
  have hid : (3 : ℝ) ^ (-(N : ℤ)) * (3 : ℝ) ^ N = 1 := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    simp
  have hpt : ∀ i : ℕ, translatePotentialSample ((3 : ℝ) ^ N • z0) eta i ((3 : ℝ) ^ N • (w - z0)) =
      (omega ((i : ℤ) - N)) w := by
    intro i
    rw [translatePotentialSample_apply, hEta, ← smul_add, sub_add_cancel, smul_smul, ← zpow_natCast,
      ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    simp
  rw [aux_lem_as_regularity_tail_reference_eq M hk]
  simp only [hpt]
  have hlayer := aux_lem_as_regularity_trunc_coeff_layer_sum omega N L' k hk w
  have hcard : ∑ i ∈ Finset.Ico (k + 1) (N + L' + 1),
      ((omega ((i : ℤ) - N)) w - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) =
      ∑ i ∈ Finset.Ico (k + 1) (N + L' + 1), (omega ((i : ℤ) - N)) w -
        ((N : ℝ) + L' - k) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    have : N + L' + 1 - (k + 1) = N + L' - k := by omega
    rw [this, Nat.cast_sub hk]
    push_cast; ring
  have hH : (fun om => infraredPartialSum om L') omega w =
      ∑ n ∈ Finset.range L', ((omega (Int.ofNat (n + 1))) w - (omega (Int.ofNat (n + 1))) 0) := by
    simp [infraredPartialSum, ContinuousMap.sum_apply]
  have hnat : ((N : ℤ) - ((N : ℤ) - k)).toNat = k := by omega
  unfold aux_in_deterministic_onestep_sref aux_lem_as_regularity_trunc_coeff_const
  dsimp only
  rw [hnat, hcard, hlayer, hH]
  have hpos1 := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M k
  have hpos2 := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
  have hret : (if 0 ≤ (N : ℤ) - k then ∑ j ∈ Finset.Ico (0 : ℤ) ((N : ℤ) - k), (omega (-j)) w
      else -∑ j ∈ Finset.Ico ((N : ℤ) - k) (0 : ℤ), (omega (-j)) w) =
      signedPrefix (fun i => (omega (-i)) w) ((N : ℤ) - k) := rfl
  rw [hret]
  rw [Finset.sum_sub_distrib]
  set τ := SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P with hτ
  set B := ∑ n ∈ Finset.range L', (omega (Int.ofNat (n + 1))) w
  set S0 := ∑ n ∈ Finset.range L', (omega (Int.ofNat (n + 1))) 0
  set P := signedPrefix (fun i => (omega (-i)) w) ((N : ℤ) - k)
  have e1 : Real.exp ((L' : ℝ) * τ - S0) * Real.exp (B + P - ((N : ℝ) + L' - k) * τ) =
      Real.exp (((k : ℝ) + 1) * τ) / Real.exp (((N : ℝ) + 1) * τ) * Real.exp (B - S0 + P) := by
    rw [← Real.exp_add, ← Real.exp_sub, ← Real.exp_add]; congr 1; ring
  calc (ahom M N)⁻¹ * Real.exp ((L' : ℝ) * τ - S0) *
        (ahom M k * Real.exp (B + P - ((N : ℝ) + L' - k) * τ))
      = (ahom M N)⁻¹ * ahom M k *
          (Real.exp ((L' : ℝ) * τ - S0) * Real.exp (B + P - ((N : ℝ) + L' - k) * τ)) := by ring
    _ = (ahom M N)⁻¹ * ahom M k *
          (Real.exp (((k : ℝ) + 1) * τ) / Real.exp (((N : ℝ) + 1) * τ) *
            Real.exp (B - S0 + P)) := by rw [e1]
    _ = _ := by
      have := Real.exp_pos (((N : ℝ) + 1) * τ)
      field_simp

/-- A Holder datum stays Holder after scaling by a nonnegative constant. -/
theorem aux_lem_as_regularity_trunc_coeff_memHolder_smul {d : ℕ} {W : Set (Vec d)} {alpha c : ℝ}
    (hc : 0 ≤ c) {f : Vec d → Vec d} (hf : MemHolder W alpha f) :
    MemHolder W alpha (fun x => c • f x) := by
  obtain ⟨K, hK, hb⟩ := hf
  refine ⟨c * K, mul_nonneg hc hK, fun x hx y hy => ?_⟩
  have h := hb x hx y hy
  have : (fun x => c • f x) x - (fun x => c • f x) y = c • (f x - f y) := by
    simp only [smul_sub]
  rw [this, euclideanNorm_smul, abs_of_nonneg hc, mul_assoc]
  exact mul_le_mul_of_nonneg_left h hc

/-- The Holder seminorm scales with a nonnegative constant. -/
theorem aux_lem_as_regularity_trunc_coeff_holderSeminormOn_smul {d : ℕ} (W : Set (Vec d))
    (alpha : ℝ) {c : ℝ} (hc : 0 ≤ c) (f : Vec d → Vec d) :
    holderSeminormOn W alpha (fun x => c • f x) = c * holderSeminormOn W alpha f := by
  unfold holderSeminormOn
  have hset : {r : ℝ | ∃ x ∈ W, ∃ y ∈ W, x ≠ y ∧
      r = euclideanNorm ((fun x => c • f x) x - (fun x => c • f x) y) /
        euclideanNorm (x - y) ^ alpha} =
      c • {r : ℝ | ∃ x ∈ W, ∃ y ∈ W, x ≠ y ∧
        r = euclideanNorm (f x - f y) / euclideanNorm (x - y) ^ alpha} := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨x, hx, y, hy, hxy, rfl⟩
      refine ⟨euclideanNorm (f x - f y) / euclideanNorm (x - y) ^ alpha,
        ⟨x, hx, y, hy, hxy, rfl⟩, ?_⟩
      simp only [← smul_sub, euclideanNorm_smul, abs_of_nonneg hc]
      ring
    · rintro ⟨s, ⟨x, hx, y, hy, hxy, rfl⟩, rfl⟩
      refine ⟨x, hx, y, hy, hxy, ?_⟩
      simp only [← smul_sub, euclideanNorm_smul, abs_of_nonneg hc]
      ring
  rw [hset, Real.sSup_smul_of_nonneg hc, smul_eq_mul]

/-- Fractional Sobolev membership is preserved by scalar multiples. -/
theorem aux_lem_as_regularity_trunc_coeff_memFullWsp_smul {d : ℕ} {Q : Homogenization.TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent} {g : Vec d → Vec d} (c : ℝ)
    (hg : Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp Q s p g) :
    Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp Q s p (fun x => c • g x) := by
  constructor
  · have h := hg.1.const_smul c
    simpa only [map_smul] using! h
  · unfold Homogenization.MemCubeEuclideanWsp
    have hk : Homogenization.cubeEuclideanWspKernel s p (fun x => c • g x) =
        fun z => c • Homogenization.cubeEuclideanWspKernel s p g z := by
      funext z
      rw [Homogenization.cubeEuclideanWspKernel_apply,
        Homogenization.cubeEuclideanWspKernel_apply, ← smul_sub,
        show HilbertVec.ofVec (c • (g z.1 - g z.2)) = c • HilbertVec.ofVec (g z.1 - g z.2) from
          (HilbertVec.ofVecL d).map_smul c _, smul_comm]
    rw [hk]
    exact hg.2.const_smul c

/-- A Dirichlet solution for a constant multiple of a coefficient is a Dirichlet solution for the
coefficient with the datum divided by the constant. -/
theorem aux_lem_as_regularity_trunc_coeff_dirichlet_scale {d : ℕ} {a : Vec d → ℝ}
    {Q : Homogenization.TriadicCube d} {u h : H1Function (openCubeSet Q)} {g : Vec d → Vec d} {c : ℝ}
    (hc : 0 < c) (hsol : IsDirichletSolutionOn (fun y => c * a y) Q u h g) :
    IsDirichletSolutionOn a Q u h (fun x => c⁻¹ • g x) := by
  refine (Section6HolderLift.isDirichletSolutionOn_const_mul_iff (a := a) (Q := Q) (u := u) (h := h)
    (g := fun x => c⁻¹ • g x) hc.ne').1 ?_
  convert hsol using 2
  funext x
  simp only [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]

end Paper
