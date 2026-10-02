import SubdiffusiveProcess.Nash.L1Ball
import SubdiffusiveProcess.Nash.KernelContraction

open MeasureTheory MarkovProcess MarkovProcess.Semigroup Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.Nash

/-- Generator-domain approximants obtained by averaging a short semigroup orbit. -/
def orbitAverage {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (S : StronglyContinuousContractionSemigroup H) (f : H) (t : ℝ≥0) : S.generatorDomain :=
  ⟨(t : ℝ)⁻¹ • S.orbitIntegral f t,
    S.generatorDomain.smul_mem _ (S.orbitIntegral_mem_generatorDomain f t)⟩

theorem tendsto_orbitAverage {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (S : StronglyContinuousContractionSemigroup H) (f : H) :
    Tendsto (fun t : ℝ≥0 => (orbitAverage S f t : H)) (𝓝[>] 0) (𝓝 f) :=
  S.tendsto_inv_smul_orbitIntegral f

/-- L1 contraction passes to the orbit averages in the ambient Hilbert space. -/
theorem orbitAverage_eLpNorm_one_le {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (P : SubMarkovKernelSemigroup X) (S : StronglyContinuousContractionSemigroup (Lp ℝ 2 mu))
    (hsub : P.IsSubInvariant mu)
    (hcompat : ∀ (t : ℝ≥0) (f : Lp ℝ 2 mu), (S t f : X → ℝ) =ᵐ[mu] kernelIntegral (P t) f)
    (f : Lp ℝ 2 mu) (hf : Integrable (f : X → ℝ) mu) (t : ℝ≥0) (ht : 0 < t) :
    eLpNorm ((orbitAverage S f t : Lp ℝ 2 mu) : X → ℝ) 1 mu ≤ eLpNorm (f : X → ℝ) 1 mu := by
  have htR : (0 : ℝ) < t := ht
  have h := (convex_L1Ball mu (eLpNorm (f : X → ℝ) 1 mu)).set_average_mem
    (isClosed_L1Ball mu _) (t := Ioc (0 : ℝ) t) (μ := volume)
    (by simpa [Real.volume_Ioc] using (ENNReal.ofReal_pos.mpr htR).ne')
    (by simp [Real.volume_Ioc])
    (ae_of_all _ fun s => semigroup_eLpNorm_one_le mu P S hsub hcompat (Real.toNNReal s) f hf)
    ((S.continuous_operator_toNNReal f).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  rw [setAverage_eq, measureReal_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal htR.le, ← intervalIntegral.integral_of_le t.coe_nonneg] at h
  exact h

end SubdiffusiveProcess.Nash
