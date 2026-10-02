import SubdiffusiveProcess.Nash.DomainDecay
import SubdiffusiveProcess.Nash.OrbitAverage

open MeasureTheory MarkovProcess MarkovProcess.Semigroup Filter Set
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace SubdiffusiveProcess.Nash

variable {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (P : SubMarkovKernelSemigroup X) (S : StronglyContinuousContractionSemigroup (Lp ℝ 2 mu))
    (hsub : P.IsSubInvariant mu)
    (hcompat : ∀ (t : ℝ≥0) (f : Lp ℝ 2 mu), (S t f : X → ℝ) =ᵐ[mu] kernelIntegral (P t) f)
    (d : ℕ) (hd : 2 ≤ d) (K : ℝ) (hK : 0 < K)
    (hsob : ∀ f : S.generatorDomain,
      eLpNorm (f : X → ℝ) (ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) - 1))) mu ^ (2 : ℕ) ≤
        ENNReal.ofReal K * ENNReal.ofReal (-⟪S.generator f, (f : Lp ℝ 2 mu)⟫))

include P hsub hcompat hd hK hsob

/-- The generator-domain bound extends through short orbit averages. -/
theorem semigroup_norm_sq_bound (f : Lp ℝ 2 mu) (F : ℝ) (hF : 0 < F)
    (hf : eLpNorm (f : X → ℝ) 1 mu ≤ ENNReal.ofReal F) (t : ℝ≥0) (ht : 0 < t) :
    ‖S t f‖ ^ 2 ≤ ((d : ℝ) * K / (2 * (t : ℝ))) ^ d * F ^ 2 := by
  have hfI : Integrable (f : X → ℝ) mu :=
    memLp_one_iff_integrable.mp ⟨Lp.aestronglyMeasurable _, hf.trans_lt ENNReal.ofReal_lt_top⟩
  have hlim : Tendsto (fun s : ℝ≥0 => ‖S t (orbitAverage S f s : Lp ℝ 2 mu)‖ ^ 2)
      (𝓝[>] 0) (𝓝 (‖S t f‖ ^ 2)) :=
    ((continuous_norm.pow 2).tendsto (S t f)).comp
      (((S t).continuous.tendsto f).comp (tendsto_orbitAverage S f))
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact domain_norm_sq_bound mu P S hsub hcompat d hd K hK hsob (orbitAverage S f s) F hF
    ((orbitAverage_eLpNorm_one_le mu P S hsub hcompat f hfI s hs).trans hf) t ht

/-- The resulting L1-to-L2 operator bound has the sharp Nash coefficient. -/
theorem semigroup_L1_L2_bound (t : ℝ≥0) (ht : 0 < t) (f : Lp ℝ 2 mu)
    (hf : Integrable (f : X → ℝ) mu) :
    ‖S t f‖ ≤ Real.sqrt (((d : ℝ) * K / (2 * (t : ℝ))) ^ d) *
      (eLpNorm (f : X → ℝ) 1 mu).toReal := by
  let F := (eLpNorm (f : X → ℝ) 1 mu).toReal
  have hF : 0 ≤ F := ENNReal.toReal_nonneg
  have hfin := (memLp_one_iff_integrable.mpr hf).2.ne
  have hFrep : ENNReal.ofReal F = eLpNorm (f : X → ℝ) 1 mu := ENNReal.ofReal_toReal hfin
  by_cases hzero : F = 0
  · have hz : eLpNorm (f : X → ℝ) 1 mu = 0 := by rw [← hFrep, hzero]; simp
    have hfzero : f = 0 := by
      apply Lp.ext
      exact ((eLpNorm_eq_zero_iff (Lp.aestronglyMeasurable f) one_ne_zero).mp hz).trans
        (Lp.coeFn_zero _ _ _).symm
    simp only [hfzero, map_zero, norm_zero]
    exact mul_nonneg (Real.sqrt_nonneg _) ENNReal.toReal_nonneg
  have hFp : 0 < F := lt_of_le_of_ne hF (Ne.symm hzero)
  have hn := semigroup_norm_sq_bound mu P S hsub hcompat d hd K hK hsob f F hFp
    (by rw [hFrep]) t ht
  have hR : 0 ≤ ((d : ℝ) * K / (2 * (t : ℝ))) ^ d := by positivity
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hF)).mp
  calc
    ‖S t f‖ ^ 2 ≤ ((d : ℝ) * K / (2 * (t : ℝ))) ^ d * F ^ 2 := hn
    _ = (Real.sqrt (((d : ℝ) * K / (2 * (t : ℝ))) ^ d) * F) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hR]

end SubdiffusiveProcess.Nash
