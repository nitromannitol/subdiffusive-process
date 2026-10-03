module

public import SubdiffusiveProcess.Nash.DomainNash
public import SubdiffusiveProcess.Nash.OrbitEnergy
public import SubdiffusiveProcess.Nash.Decay
public import SubdiffusiveProcess.Nash.DecayConstant

@[expose] public section

open MeasureTheory MarkovProcess MarkovProcess.Semigroup Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubdiffusiveProcess.Nash

/-- The Nash decay estimate for a generator-domain vector with a positive L1 bound. -/
theorem domain_norm_sq_bound {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (P : SubMarkovKernelSemigroup X) (S : StronglyContinuousContractionSemigroup (Lp ℝ 2 mu))
    (hsub : P.IsSubInvariant mu)
    (hcompat : ∀ (t : ℝ≥0) (f : Lp ℝ 2 mu), (S t f : X → ℝ) =ᵐ[mu] kernelIntegral (P t) f)
    (d : ℕ) (hd : 2 ≤ d) (K : ℝ) (hK : 0 < K)
    (hsob : ∀ f : S.generatorDomain,
      eLpNorm (f : X → ℝ) (ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) - 1))) mu ^ (2 : ℕ) ≤
        ENNReal.ofReal K * ENNReal.ofReal (-⟪S.generator f, (f : Lp ℝ 2 mu)⟫))
    (f : S.generatorDomain) (F : ℝ) (hF : 0 < F)
    (hf : eLpNorm (f : X → ℝ) 1 mu ≤ ENNReal.ofReal F) (t : ℝ≥0) (ht : 0 < t) :
    ‖S t (f : Lp ℝ 2 mu)‖ ^ 2 ≤ ((d : ℝ) * K / (2 * (t : ℝ))) ^ d * F ^ 2 := by
  have hdN : 0 < d := lt_of_lt_of_le (by norm_num : 0 < 2) hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdN
  have hfI : Integrable (f : X → ℝ) mu :=
    memLp_one_iff_integrable.mp (hf.trans_lt ENNReal.ofReal_lt_top)
  let u : ℝ → ℝ := fun s => ‖S (Real.toNNReal s) (f : Lp ℝ 2 mu)‖ ^ 2
  let v : ℝ → ℝ := fun s => 2 * ⟪S (Real.toNNReal s) (S.generator f),
    S (Real.toNNReal s) (f : Lp ℝ 2 mu)⟫
  let c : ℝ := 2 / ((d : ℝ) * K * F ^ (2 / (d : ℝ)))
  have hp : 0 < F ^ (2 / (d : ℝ)) := Real.rpow_pos_of_pos hF _
  have hc : 0 < c := by dsimp [c]; positivity
  by_cases hut : u t = 0
  · have hut' : ‖S t (f : Lp ℝ 2 mu)‖ ^ 2 = 0 := by simpa only [u, Real.toNNReal_coe] using hut
    rw [hut']
    positivity
  have hutP : 0 < u t := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hut)
  have huA : Antitone u := by
    intro a b hab
    exact pow_le_pow_left₀ (norm_nonneg _) (orbit_norm_antitone S f (Real.toNNReal_mono hab)) 2
  have hpos (s : ℝ) (hs : s ∈ Icc 0 (t : ℝ)) : 0 < u s := hutP.trans_le (huA hs.2)
  have hineq (s : ℝ) (hs : s ∈ Ioo 0 (t : ℝ)) : v s ≤ -((d : ℝ) * c) * u s ^ (1 + 1 / (d : ℝ)) := by
    let E : ℝ := -⟪S (Real.toNNReal s) (S.generator f), S (Real.toNNReal s) (f : Lp ℝ 2 mu)⟫
    let g : S.generatorDomain := ⟨S (Real.toNNReal s) f, S.operator_mem_generatorDomain f _⟩
    have hgSob := hsob g
    rw [S.generator_operator] at hgSob
    have hgL1 := (semigroup_eLpNorm_one_le mu P S hsub hcompat (Real.toNNReal s) f hfI).trans hf
    have hn := real_nash_of_sobolev mu d hd (S (Real.toNNReal s) f) K E F hK.le
      (orbit_energy_nonneg S f hs.1) hF.le hgL1 hgSob
    have he : u s ^ (1 + 1 / (d : ℝ)) / (K * F ^ (2 / (d : ℝ))) ≤ E := by
      rw [div_le_iff₀ (mul_pos hK hp)]
      simpa only [u, mul_assoc, mul_comm, mul_left_comm] using hn
    calc
      v s = -2 * E := by dsimp [v, E]; ring
      _ ≤ -2 * (u s ^ (1 + 1 / (d : ℝ)) / (K * F ^ (2 / (d : ℝ)))) :=
        mul_le_mul_of_nonpos_left he (by norm_num)
      _ = -((d : ℝ) * c) * u s ^ (1 + 1 / (d : ℝ)) := by
        dsimp [c]
        field_simp
  have hdec := decay_rpow u v d c t hdR hc ht
    (((S.continuous_operator_toNNReal f).norm.pow 2).continuousOn) hpos
    (fun s hs => hasDerivAt_orbit_norm_sq S f hs.1) hineq
  rw [decay_constant d hdN K F t hK hF ht] at hdec
  simpa only [u, Real.toNNReal_coe] using hdec

end SubdiffusiveProcess.Nash
