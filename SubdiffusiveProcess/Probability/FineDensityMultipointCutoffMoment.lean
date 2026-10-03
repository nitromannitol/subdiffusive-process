module

public import SubdiffusiveProcess.Probability.FineDensityMultipointMoment
public import SubdiffusiveProcess.Probability.SeparatedFineLayerFactorization

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open Homogenization
open scoped CompactlySupported ENNReal NNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess

theorem fineDensity_multiPoint_prod_exp_moment_le_of_separated_cutoff
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (p : ℕ) (hp : 1 ≤ p)
    (N j0 : ℕ) (x : Fin p → SpatialCoordinates d)
    (hpdelta : (p : ℝ) * M.delta ≤ 1)
    (hsep : Pairwise (fun i k : Fin p =>
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ (-(j0 : ℤ)) <
        Homogenization.euclideanNorm (x i - x k))) :
    (∫ omega : BilateralField d, ∏ k : Fin p, fineDensity M N omega (x k)
        ∂(chaosSampleLaw M).toMeasure) ≤
      Real.exp ((min (N + 1) j0 : ℝ) *
        ((Real.log 2 / 2) * (p : ℝ) ^ 2 * M.delta ^ 2 -
          (p : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) := by
  classical
  let ν := chaosRootFieldLaw M
  let laws : ℤ → Measure C(SpatialCoordinates d, ℝ) :=
    fun j => (scaledLayerLaw d ν j).toMeasure
  let P : Measure (BilateralField d) := Measure.infinitePi laws
  let F : C(SpatialCoordinates d, ℝ) → ℝ := fun f =>
    Real.exp (∑ k : Fin p, f (x k) - (p : ℝ) *
      SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
  have hFmeas : Measurable F := by
    dsimp [F]
    apply Measurable.exp
    apply Measurable.sub
    · apply Finset.measurable_sum
      intro k hk
      exact (continuous_eval_const (x k)).measurable
    · exact measurable_const
  have hindep (T : Finset ℕ) : iIndepFun
      (fun i : T => fun omega : BilateralField d => omega (-(i : ℤ))) P := by
    have hfull : iIndepFun
        (fun j : ℤ => fun omega : BilateralField d => omega j) P := by
      dsimp only [P, laws]
      exact iIndepFun_infinitePi (fun _ => measurable_id)
    apply hfull.precomp
    intro i₁ i₂ hi
    apply Subtype.ext
    exact_mod_cast (neg_injective hi)
  have hfactor (T : Finset ℕ) :
      ∫ omega, ∏ i : T, F (omega (-(i : ℤ))) ∂P =
        ∏ i : T, ∫ omega, F (omega (-(i : ℤ))) ∂P := by
    refine (hindep T).integral_fun_prod_comp ?_ (fun i => ?_)
    · intro i
      exact (measurable_pi_apply (-(i : ℤ))).aemeasurable
    · exact hFmeas.aestronglyMeasurable
  let a : ℕ → ℝ := fun i =>
    ∫ omega, F (omega (-(i : ℤ))) ∂P
  have hexp (n : ℕ) (omega : BilateralField d) :
      (∏ k : Fin p, fineDensity M n omega (x k)) =
        ∏ j ∈ Finset.range (n + 1), F (omega (-(j : ℤ))) := by
    simp only [fineDensity, finePotential, F]
    calc
      (∏ k : Fin p, Real.exp
          (∑ j ∈ Finset.range (n + 1), (omega (-Int.ofNat j)) (x k) -
            (n + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) =
          Real.exp (∑ k : Fin p,
            (∑ j ∈ Finset.range (n + 1), (omega (-Int.ofNat j)) (x k) -
              (n + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) :=
        (Real.exp_sum _ _).symm
      _ = Real.exp (∑ j ∈ Finset.range (n + 1),
            (∑ k : Fin p, (omega (-Int.ofNat j)) (x k) -
              (p : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) := by
        congr 1
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          Finset.sum_const, Finset.sum_comm]
        simp only [Finset.card_fin, Finset.card_range, Finset.sum_const]
        ring
      _ = ∏ j ∈ Finset.range (n + 1),
          Real.exp (∑ k : Fin p, (omega (-Int.ofNat j)) (x k) -
            (p : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) :=
        Real.exp_sum _ _
  have hcombine (n : ℕ) :
      (∫ omega, ∏ k : Fin p, fineDensity M n omega (x k) ∂P) =
        ∏ j ∈ Finset.range (n + 1), a j := by
    calc
      (∫ omega, ∏ k : Fin p, fineDensity M n omega (x k) ∂P) =
          ∫ omega, ∏ j : (Finset.range (n + 1) : Finset ℕ),
            F (omega (-(j : ℤ))) ∂P := by
              apply integral_congr_ae
              filter_upwards with omega
              rw [hexp n omega]
              exact (Finset.prod_coe_sort (Finset.range (n + 1))
                (fun j => F (omega (-(j : ℤ))))).symm
      _ = ∏ j : (Finset.range (n + 1) : Finset ℕ),
          ∫ omega, F (omega (-(j : ℤ))) ∂P :=
            hfactor (Finset.range (n + 1))
      _ = ∏ j ∈ Finset.range (n + 1), a j := by
            simpa only [a] using!
              (Finset.prod_coe_sort (Finset.range (n + 1))
                (fun j => ∫ omega : BilateralField d,
                  F (omega (-(j : ℤ))) ∂P))
  have htail (i : ℕ) (hi : j0 ≤ i) : a i = 1 := by
    have hsep_at : Pairwise (fun r k : Fin p =>
        Real.sqrt (d : ℝ) * (3 : ℝ) ^ (-(i : ℤ)) <
          Homogenization.euclideanNorm (x r - x k)) := by
      intro r k hrk
      have hneg : -(i : ℤ) ≤ -(j0 : ℤ) := by
        exact neg_le_neg (by exact_mod_cast hi)
      have hpow : (3 : ℝ) ^ (-(i : ℤ)) ≤
          (3 : ℝ) ^ (-(j0 : ℤ)) :=
        zpow_le_zpow_right₀ (a := (3 : ℝ)) (by norm_num) hneg
      exact (mul_le_mul_of_nonneg_left hpow (Real.sqrt_nonneg _)).trans_lt
        (hsep hrk)
    have hone := chaosSampleLaw_prod_exp_sub_tauSq_eq_one_of_fineLayer_separated
      M p i x hsep_at
    calc
      a i = ∫ omega : BilateralField d,
          ∏ k : Fin p, Real.exp
            ((omega (-(i : ℤ))) (x k) -
              SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ∂P := by
            apply integral_congr_ae
            filter_upwards with omega
            dsimp [a, F]
            rw [← Real.exp_sum]
            congr 1
            rw [Finset.sum_sub_distrib, Finset.sum_const]
            simp only [Finset.card_fin]
            ring
      _ = 1 := by
            simpa only [P, ν, laws, chaosSampleLaw, commonScaleLaw] using! hone
  let j' : ℕ := min (N + 1) j0
  have hmin : j' ≤ N + 1 := by
    exact Nat.min_le_left _ _
  have hcut :
      (∏ i ∈ Finset.range (N + 1), a i) =
        ∏ i ∈ Finset.range j', a i := by
    have htailprod : (∏ i ∈ Finset.Ico j' (N + 1), a i) = 1 := by
      by_cases h : j0 ≤ N + 1
      · have hj' : j' = j0 := by
          dsimp [j']
          exact min_eq_right h
        rw [hj']
        apply Finset.prod_eq_one
        intro i hi
        exact htail i (Finset.mem_Ico.mp hi).1
      · have hj' : j' = N + 1 := by
          dsimp [j']
          exact min_eq_left (Nat.le_of_not_ge h)
        rw [hj']
        simp
    rw [← Finset.prod_range_mul_prod_Ico a hmin, htailprod, mul_one]
  rw [show (chaosSampleLaw M).toMeasure = P by rfl]
  rw [hcombine N, hcut]
  by_cases hj : j' = 0
  · rw [hj]
    have hjNat : min (N + 1) j0 = 0 := by
      simpa [j'] using! hj
    have hjReal : (min (N + 1) j0 : ℝ) = 0 := by
      exact_mod_cast hjNat
    simp [hjReal]
  · have hjpos : 0 < j' := Nat.pos_of_ne_zero hj
    have hbound := (fineDensity_multiPoint_prod_exp_moment_le M p hp
      (j' - 1) x hpdelta).2
    rw [show (chaosSampleLaw M).toMeasure = P by rfl] at hbound
    have hcast : ((j' - 1 : ℕ) : ℝ) + 1 = (j' : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ j')]
      norm_num
    calc
      (∏ i ∈ Finset.range j', a i) =
          ∫ omega, ∏ k : Fin p, fineDensity M (j' - 1) omega (x k) ∂P := by
            rw [hcombine (j' - 1)]
            rw [Nat.sub_add_cancel hjpos]
      _ ≤ Real.exp ((((j' - 1 : ℕ) : ℝ) + 1) *
          ((Real.log 2 / 2) * (p : ℝ) ^ 2 * M.delta ^ 2 -
            (p : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) := by
            exact hbound
      _ = Real.exp ((j' : ℝ) *
          ((Real.log 2 / 2) * (p : ℝ) ^ 2 * M.delta ^ 2 -
            (p : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) := by
            rw [hcast]
      _ = Real.exp ((min (N + 1) j0 : ℝ) *
          ((Real.log 2 / 2) * (p : ℝ) ^ 2 * M.delta ^ 2 -
            (p : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) := by
            simp [j']

end SubdiffusiveProcess
