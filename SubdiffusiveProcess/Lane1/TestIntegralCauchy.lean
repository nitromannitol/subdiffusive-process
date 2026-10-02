import SubdiffusiveProcess.Lane1.TriadicTiling
import SubdiffusiveProcess.Lane1.StepApproximation

/-!
# The test integral is Cauchy along the cutoffs

Comparing `∫ f dnu` with the step sum over the generation-`j` tiles costs the
oscillation of `f` at scale `3 ^ (-j)` times the mass of a fixed ball -- a
bound UNIFORM in `nu`.  Applied to the cutoff measures, whose masses on a fixed
ball are bounded uniformly in the cutoff by the growth bound, it turns the
convergence of finitely many cube masses into a Cauchy property for the test
integral.
-/

open Filter MeasureTheory

open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess

/-- The tile centre lies in its tile. -/
theorem tileCenter_mem {d : ℕ} (j : ℕ) (k : Fin d → ℤ) :
    tileCenter j k ∈ triadicTile j k := by
  have ht : (0 : ℝ) < (3 : ℝ) ^ (-(j : ℤ)) := zpow_neg_pos j
  rw [mem_triadicTile_iff]
  intro i
  constructor
  · have : (k i : ℝ) * (3 : ℝ) ^ (-(j : ℤ))
        ≤ ((k i : ℝ) + 1 / 2) * (3 : ℝ) ^ (-(j : ℤ)) := by nlinarith
    simpa [tileCenter] using this
  · have : ((k i : ℝ) + 1 / 2) * (3 : ℝ) ^ (-(j : ℤ))
        < ((k i : ℝ) + 1) * (3 : ℝ) ^ (-(j : ℤ)) := by nlinarith
    simpa [tileCenter] using this

/-- The finite index set of generation-`j` tiles meeting a ball of radius `R`. -/
def tileIndices (d : ℕ) (R : ℝ) (j : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ =>
    Finset.Icc (-(⌈R / (3 : ℝ) ^ (-(j : ℤ))⌉₊ + 1 : ℤ))
      ((⌈R / (3 : ℝ) ^ (-(j : ℤ))⌉₊ + 1 : ℤ))

/-- A point of the ball has its tile index in the box. -/
theorem tileIndex_mem_tileIndices {d : ℕ} {R : ℝ} (hR : 0 ≤ R) (j : ℕ)
    {x : SpatialCoordinates d} (hx : dist x (0 : SpatialCoordinates d) ≤ R) :
    tileIndex j x ∈ tileIndices d R j := by
  classical
  have ht : (0 : ℝ) < (3 : ℝ) ^ (-(j : ℤ)) := zpow_neg_pos j
  rw [tileIndices, Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have hxi : |x i| ≤ R := by
    have := (dist_pi_le_iff hR).mp hx i
    have hzero : (0 : SpatialCoordinates d) i = 0 := rfl
    rwa [Real.dist_eq, hzero, sub_zero] at this
  have hdiv : |x i / (3 : ℝ) ^ (-(j : ℤ))| ≤ R / (3 : ℝ) ^ (-(j : ℤ)) := by
    rw [abs_div, abs_of_pos ht]
    gcongr
  have hce : (R / (3 : ℝ) ^ (-(j : ℤ)))
      ≤ (⌈R / (3 : ℝ) ^ (-(j : ℤ))⌉₊ : ℝ) := Nat.le_ceil _
  have hfl : |((⌊x i / (3 : ℝ) ^ (-(j : ℤ))⌋ : ℤ) : ℝ)|
      ≤ (⌈R / (3 : ℝ) ^ (-(j : ℤ))⌉₊ : ℝ) + 1 := by
    have h1 : ((⌊x i / (3 : ℝ) ^ (-(j : ℤ))⌋ : ℤ) : ℝ)
        ≤ x i / (3 : ℝ) ^ (-(j : ℤ)) := Int.floor_le _
    have h2 : x i / (3 : ℝ) ^ (-(j : ℤ)) - 1
        < ((⌊x i / (3 : ℝ) ^ (-(j : ℤ))⌋ : ℤ) : ℝ) := Int.sub_one_lt_floor _
    rw [abs_le] at hdiv ⊢
    constructor <;> linarith [hdiv.1, hdiv.2]
  rw [abs_le] at hfl
  constructor
  · have : (-((⌈R / (3 : ℝ) ^ (-(j : ℤ))⌉₊ : ℝ) + 1))
        ≤ ((⌊x i / (3 : ℝ) ^ (-(j : ℤ))⌋ : ℤ) : ℝ) := hfl.1
    have hcast : ((-(⌈R / (3 : ℝ) ^ (-(j : ℤ))⌉₊ + 1 : ℤ) : ℤ) : ℝ)
        = -((⌈R / (3 : ℝ) ^ (-(j : ℤ))⌉₊ : ℝ) + 1) := by push_cast; ring
    have hres : ((-(⌈R / (3 : ℝ) ^ (-(j : ℤ))⌉₊ + 1 : ℤ) : ℤ) : ℝ)
        ≤ ((tileIndex j x i : ℤ) : ℝ) := by rw [hcast]; simpa [tileIndex] using this
    exact_mod_cast hres
  · have : ((⌊x i / (3 : ℝ) ^ (-(j : ℤ))⌋ : ℤ) : ℝ)
        ≤ (⌈R / (3 : ℝ) ^ (-(j : ℤ))⌉₊ : ℝ) + 1 := hfl.2
    have hcast : (((⌈R / (3 : ℝ) ^ (-(j : ℤ))⌉₊ + 1 : ℤ) : ℤ) : ℝ)
        = (⌈R / (3 : ℝ) ^ (-(j : ℤ))⌉₊ : ℝ) + 1 := by push_cast; ring
    have hres : ((tileIndex j x i : ℤ) : ℝ)
        ≤ (((⌈R / (3 : ℝ) ^ (-(j : ℤ))⌉₊ + 1 : ℤ) : ℤ) : ℝ) := by
      rw [hcast]; simpa [tileIndex] using this
    exact_mod_cast hres

/-- **The step bound.**  Comparing the test integral with the step sum over the
generation-`j` tiles costs the oscillation of `f` at that scale, times the
total mass of the tiles -- and the bound does not depend on `nu`. -/
theorem test_integral_step_bound
    {d : ℕ} (nu : Measure (SpatialCoordinates d)) (hac : nu ≪ volume)
    (f : SpatialCoordinates d → ℝ)
    (R : ℝ) (hR : 0 ≤ R)
    (hsupp : ∀ x, R < dist x (0 : SpatialCoordinates d) → f x = 0)
    (hint : Integrable f nu) (j : ℕ)
    (eta : ℝ) (heta : 0 ≤ eta)
    (hosc : ∀ x y, dist x y ≤ (3 : ℝ) ^ (-(j : ℤ)) → |f x - f y| ≤ eta)
    (hfin : ∀ k ∈ tileIndices d R j, nu (triadicTile j k) ≠ ⊤) :
    |∫ x, f x ∂nu
        - ∑ k ∈ tileIndices d R j, f (tileCenter j k) *
            (nu ((centeredCube (tileCenter j k) ((3 : ℝ) ^ (-(j : ℤ)))
              (zpow_neg_pos j)) : Set (SpatialCoordinates d))).toReal|
      ≤ eta * ∑ k ∈ tileIndices d R j, (nu (triadicTile j k)).toReal := by
  classical
  have hzero : ∀ x, x ∉ (⋃ k ∈ tileIndices d R j, triadicTile j k) → f x = 0 := by
    intro x hx
    by_contra hfx
    refine hx ?_
    have hdx : dist x (0 : SpatialCoordinates d) ≤ R := by
      by_contra hcon
      push_neg at hcon
      exact hfx (hsupp x hcon)
    exact Set.mem_biUnion (tileIndex_mem_tileIndices hR j hdx)
      (mem_triadicTile_tileIndex j x)
  have hstep := integral_sub_step_le nu f (tileIndices d R j)
    (fun k => triadicTile j k) (fun k => tileCenter j k)
    (fun k _ => measurableSet_triadicTile j k)
    (fun k _ l _ hkl => triadicTile_disjoint j hkl)
    hzero hint hfin eta heta
    (fun k _ x hx => hosc x (tileCenter j k)
      (dist_le_of_mem_triadicTile hx (tileCenter_mem j k)))
  have hrw : ∀ k : Fin d → ℤ,
      (nu (triadicTile j k)).toReal
        = (nu ((centeredCube (tileCenter j k) ((3 : ℝ) ^ (-(j : ℤ)))
            (zpow_neg_pos j)) : Set (SpatialCoordinates d))).toReal := by
    intro k
    rw [measure_triadicTile_eq nu hac j k]
  simpa only [hrw] using hstep

/-- **The test integral is Cauchy along the cutoffs**, hence convergent. -/
theorem test_integral_cauchy
    {d : ℕ} (nuN : ℕ → Measure (SpatialCoordinates d))
    (hac : ∀ N, nuN N ≪ volume)
    (f : SpatialCoordinates d → ℝ) (hfc : Continuous f)
    (hcs : HasCompactSupport f)
    (hint : ∀ N, Integrable f (nuN N))
    (R : ℝ) (hR : 0 ≤ R)
    (hsupp : ∀ x, R < dist x (0 : SpatialCoordinates d) → f x = 0)
    (Cmass : ℝ) (hCmass0 : 0 < Cmass)
    (hCmass : ∀ (N j : ℕ),
      ∑ k ∈ tileIndices d R j, (nuN N (triadicTile j k)).toReal ≤ Cmass)
    (hfinN : ∀ (N j : ℕ), ∀ k ∈ tileIndices d R j, nuN N (triadicTile j k) ≠ ⊤)
    (hcube : ∀ (j : ℕ) (k : Fin d → ℤ), ∃ L : ℝ, Tendsto
      (fun N => (nuN N ((centeredCube (tileCenter j k) ((3 : ℝ) ^ (-(j : ℤ)))
        (zpow_neg_pos j)) : Set (SpatialCoordinates d))).toReal) atTop (nhds L)) :
    ∃ L : ℝ, Tendsto (fun N => ∫ x, f x ∂(nuN N)) atTop (nhds L) := by
  classical
  refine cauchySeq_tendsto_of_complete ?_
  rw [Metric.cauchySeq_iff]
  intro eps heps
  set eta : ℝ := eps / (4 * Cmass) with hetadef
  have hetapos : 0 < eta := by rw [hetadef]; positivity
  have huc : UniformContinuous f := hcs.uniformContinuous_of_continuous hfc
  obtain ⟨delta, hdelta, hdel⟩ := Metric.uniformContinuous_iff.mp huc eta hetapos
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (3 : ℝ) ^ (-(j : ℤ)) < delta := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hdelta (by norm_num : (1 : ℝ) / 3 < 1)
    refine ⟨n, ?_⟩
    have hpow : ((1 : ℝ) / 3) ^ n = (3 : ℝ) ^ (-(n : ℤ)) := by
      rw [one_div, inv_pow, zpow_neg, zpow_natCast]
    rwa [hpow] at hn
  have hosc : ∀ x y, dist x y ≤ (3 : ℝ) ^ (-(j : ℤ)) → |f x - f y| ≤ eta := by
    intro x y hxy
    have h := hdel (lt_of_le_of_lt hxy hj)
    rw [Real.dist_eq] at h
    exact h.le
  set step : ℕ → ℝ := fun N => ∑ k ∈ tileIndices d R j,
    f (tileCenter j k) * (nuN N ((centeredCube (tileCenter j k)
      ((3 : ℝ) ^ (-(j : ℤ))) (zpow_neg_pos j)) :
        Set (SpatialCoordinates d))).toReal with hstepdef
  have hstepconv : ∃ L : ℝ, Tendsto step atTop (nhds L) := by
    choose L hL using fun k : Fin d → ℤ => hcube j k
    refine ⟨∑ k ∈ tileIndices d R j, f (tileCenter j k) * L k, ?_⟩
    rw [hstepdef]
    exact tendsto_finset_sum _ (fun k _ => (hL k).const_mul _)
  obtain ⟨Lsum, hLsum⟩ := hstepconv
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.mp hLsum (eps / 4) (by positivity)
  refine ⟨N0, fun N hN M hM => ?_⟩
  have hb : ∀ P : ℕ, |∫ x, f x ∂(nuN P) - step P| ≤ eps / 4 := by
    intro P
    have hbP := test_integral_step_bound (nuN P) (hac P) f R hR hsupp (hint P) j
      eta hetapos.le hosc (hfinN P j)
    refine le_trans hbP ?_
    have hm := hCmass P j
    have hstep1 : eta * ∑ k ∈ tileIndices d R j, (nuN P (triadicTile j k)).toReal
        ≤ eta * Cmass := mul_le_mul_of_nonneg_left hm hetapos.le
    have hEC : eta * Cmass = eps / 4 := by
      rw [hetadef]
      field_simp
    rwa [hEC] at hstep1
  have h1 := hb N
  have h2 := hb M
  have h3 : |step N - Lsum| < eps / 4 := by
    have := hN0 N hN
    rwa [Real.dist_eq] at this
  have h4 : |step M - Lsum| < eps / 4 := by
    have := hN0 M hM
    rwa [Real.dist_eq] at this
  rw [Real.dist_eq]
  have e1 : ∫ x, f x ∂(nuN N) - ∫ x, f x ∂(nuN M)
      = ((∫ x, f x ∂(nuN N) - step N) + (step N - Lsum))
        - ((∫ x, f x ∂(nuN M) - step M) + (step M - Lsum)) := by ring
  rw [e1]
  have hsplit : |((∫ x, f x ∂(nuN N) - step N) + (step N - Lsum))
        - ((∫ x, f x ∂(nuN M) - step M) + (step M - Lsum))|
      ≤ (|∫ x, f x ∂(nuN N) - step N| + |step N - Lsum|)
        + (|∫ x, f x ∂(nuN M) - step M| + |step M - Lsum|) := by
    refine le_trans (abs_sub _ _) ?_
    gcongr <;> exact abs_add_le _ _
  refine lt_of_le_of_lt hsplit ?_
  linarith [h1, h2, h3, h4]

end SubdiffusiveProcess
