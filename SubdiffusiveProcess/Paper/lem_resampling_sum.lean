import SubdiffusiveProcess.Probability.ResamplingSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped ENNReal

noncomputable section
namespace Paper

/-- **Summing resampling bounds** (paper `mfd:lem-resampling-sum`, multifractal-2d83286.tex
L9015-9028), in the canonical product-space form: the independent family is the coordinate
family of `Measure.infinitePi μ`, "replace `ξ_j` by an independent copy" is the update of the
coordinate `j` with the coordinate `j` of an independent second sample, and
`σ(ξ_j : j ∈ J)` is the pull-back of the product σ-field along the restriction to `J`. -/
theorem lem_resampling_sum {I : Type*} [Countable I] [DecidableEq I]
    {E : I → Type*} [∀ i, MeasurableSpace (E i)]
    (μ : (i : I) → Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (X : ((i : I) → E i) → ℝ) (hX : MemLp X p (Measure.infinitePi μ)) (J : Set I) :
    eLpNorm (X - (Measure.infinitePi μ)[X |
        MeasurableSpace.comap (fun (ω : (i : I) → E i) (j : J) => ω j) MeasurableSpace.pi])
        p (Measure.infinitePi μ) ≤
      ∑' j : ↥Jᶜ, eLpNorm (fun q : ((i : I) → E i) × ((i : I) → E i) =>
          X q.1 - X (Function.update q.1 (j : I) (q.2 j))) p
        ((Measure.infinitePi μ).prod (Measure.infinitePi μ)) :=
  SubdiffusiveProcess.Probability.eLpNorm_sub_condExp_le_tsum_resample μ hp hp_top X hX J

end Paper
