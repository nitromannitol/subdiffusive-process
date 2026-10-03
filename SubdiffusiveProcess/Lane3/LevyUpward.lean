module

public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.Probability.ConditionalExpectation
public import SubdiffusiveProcess.Probability.ProductConditionalExpectation
public import Mathlib.Tactic

@[expose] public section




open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section

namespace SubdiffusiveProcess
namespace Lane3

variable {Om : Type*} {m0 : MeasurableSpace Om} {P : Measure Om}

/-- Lévy upward, constant form: an integrable variable measurable for the
generated `σ`-field whose conditional expectations along the filtration are
all equal to one constant is almost surely that constant. -/
theorem ae_eq_const_of_condExp_eq_const [IsFiniteMeasure P]
    (F : Filtration ℕ m0) (g : Om → ℝ) (c : ℝ)
    (hg : Integrable g P) (hgmeas : StronglyMeasurable[⨆ n, F n] g)
    (hconst : ∀ n, P[g|F n] =ᵐ[P] fun _ => c) :
    g =ᵐ[P] fun _ => c := by
  have hall : ∀ᵐ x ∂P, ∀ n, (P[g|F n]) x = c := by
    exact ae_all_iff.mpr hconst
  filter_upwards [hg.tendsto_ae_condExp hgmeas, hall] with x ht hc
  have hconstlim : Tendsto (fun n => (P[g|F n]) x) atTop (𝓝 c) := by
    simp only [hc]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique ht hconstlim

/-- The zero-one form actually used: if every conditional expectation along
the filtration equals the mean, the variable is almost surely its mean
(paper lines 3256-3259). -/
theorem ae_eq_integral_of_condExp_eq_integral [IsProbabilityMeasure P]
    (F : Filtration ℕ m0) (g : Om → ℝ)
    (hg : Integrable g P) (hgmeas : StronglyMeasurable[⨆ n, F n] g)
    (hconst : ∀ n, P[g|F n] =ᵐ[P] fun _ => ∫ x, g x ∂P) :
    ∃ c : ℝ, g =ᵐ[P] fun _ => c :=
  ⟨∫ x, g x ∂P, ae_eq_const_of_condExp_eq_const F g _ hg hgmeas hconst⟩


/-- Conditioning on a `σ`-field independent of one for which the variable is
already (almost everywhere) measurable returns the mean.  This is the step of
paper lines 3254-3256: `m` is `𝓕_{¬S}`-measurable, `𝓕_{¬S}` is independent of
the band, hence `E[m | band] = E[m]`. -/
theorem condExp_eq_integral_of_ae_condExp_of_indep [IsProbabilityMeasure P]
    (mc mb : MeasurableSpace Om) (hmc : mc ≤ m0) (hmb : mb ≤ m0)
    (hindep : Indep mc mb P)
    (g : Om → ℝ) (hint : Integrable g P)
    (hmeas : g =ᵐ[P] P[g|mc]) :
    P[g|mb] =ᵐ[P] fun _ => ∫ ω, g ω ∂P := by
  haveI : IsFiniteMeasure (P.trim hmb) := isFiniteMeasure_trim hmb
  have h1 : P[g|mb] =ᵐ[P] P[P[g|mc]|mb] := condExp_congr_ae hmeas
  have h2 : P[P[g|mc]|mb] =ᵐ[P] fun _ => ∫ ω, (P[g|mc]) ω ∂P :=
    condExp_indep_eq hmc hmb stronglyMeasurable_condExp hindep
  have h3 : ∫ ω, (P[g|mc]) ω ∂P = ∫ ω, g ω ∂P := integral_condExp hmc
  refine h1.trans (h2.trans ?_)
  rw [h3]


/-- Resampling invariance makes a variable almost everywhere equal to its
conditional expectation given the retained block: the step of paper lines
3237-3249, `Var(m ∣ 𝓕_{¬S}) = 0`.  `e` splits the space into the retained
block `A` and the resampled block `Bt`. -/
theorem ae_eq_condExp_of_resample_invariant
    {A Bt : Type*} [MeasurableSpace A] [MeasurableSpace Bt]
    [IsProbabilityMeasure P]
    (mu : Measure A) [IsProbabilityMeasure mu]
    (nu : Measure Bt) [IsProbabilityMeasure nu]
    (e : Om ≃ᵐ A × Bt) (he : MeasurePreserving e P (mu.prod nu))
    (g : Om → ℝ) (hgm : Measurable g) (hint : Integrable g P)
    (hinv : ∀ᵐ z ∂(P.prod P), g z.1 = g (e.symm ((e z.1).1, (e z.2).2))) :
    g =ᵐ[P] P[g | (inferInstance : MeasurableSpace A).comap (fun x => (e x).1)] := by
  have hcond := condExp_equiv_fst_integral e he hint
  have hfub : ∀ᵐ ω ∂P, ∀ᵐ ω' ∂P, g ω = g (e.symm ((e ω).1, (e ω').2)) :=
    Measure.ae_ae_of_ae_prod hinv
  have hpush : MeasurePreserving (fun ω' => (e ω').2) P nu := by
    have h := (measurePreserving_snd (μ := mu) (ν := nu)).comp he
    simpa [Function.comp_def] using h
  have hkey : g =ᵐ[P] fun ω => ∫ b, g (e.symm ((e ω).1, b)) ∂nu := by
    filter_upwards [hfub] with ω hω
    have hmset : MeasurableSet {b : Bt | g ω = g (e.symm ((e ω).1, b))} := by
      have hmap : Measurable (fun b : Bt => g (e.symm ((e ω).1, b))) :=
        hgm.comp (e.symm.measurable.comp (measurable_const.prodMk measurable_id))
      exact measurableSet_eq_fun measurable_const hmap
    have hae : ∀ᵐ b ∂nu, g ω = g (e.symm ((e ω).1, b)) := by
      rw [← hpush.map_eq, ae_map_iff hpush.measurable.aemeasurable hmset]
      exact hω
    calc g ω = ∫ _b : Bt, g ω ∂nu := by simp
      _ = ∫ b, g (e.symm ((e ω).1, b)) ∂nu := integral_congr_ae hae
  exact hkey.trans hcond.symm

end Lane3
end SubdiffusiveProcess
