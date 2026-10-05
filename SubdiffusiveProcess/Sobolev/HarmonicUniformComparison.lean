module

public import SubdiffusiveProcess.Sobolev.WeightedHarmonicBoundaryMaximum
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.Corrector

@[expose] public section

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum
noncomputable section
namespace SubdiffusiveProcess

/-- Uniformly close native boundary data have uniformly close weak harmonic extensions. -/
theorem ae_abs_sub_le_of_harmonic_datum_bound
    {d : ℕ} [NeZero d] {W : Set (SpatialCoordinates d)}
    (hW : IsOpenBoundedConvexDomain W)
    (A : SpatialCoordinates d → ℝ) (hA : Measurable A)
    (lam Lam : ℝ) (hlam : 0 < lam)
    (hbounds : ∀ x ∈ W, lam ≤ A x ∧ A x ≤ Lam)
    (u v beta gamma : H1Function W)
    (hu : IsWeaklyHarmonicOn A W u) (hv : IsWeaklyHarmonicOn A W v)
    (hut : HasZeroTraceDifferenceOn W u beta)
    (hvt : HasZeroTraceDifferenceOn W v gamma)
    (M : ℝ) (hdatum : ∀ x, |beta.toFun x - gamma.toFun x| ≤ M) :
    ∀ᵐ x ∂volume.restrict W, |u.toFun x - v.toFun x| ≤ M := by
  have hEll := isEllipticFieldOn_scalar hW.isOpen.measurableSet hA hlam hbounds
  have hharm := Section6Dirichlet.isWeaklyHarmonicOn_sub hEll hu hv
  obtain ⟨w, hw, _⟩ :=
    Section6Dirichlet.exists_h10Function_solutionDifference_sub_boundaryDifference hut hvt
  have hdiff : MemH10 W (fun x => (u - v).toFun x - (beta - gamma).toFun x) :=
    ⟨w, by simpa only [H1Function.sub_toFun] using funext hw⟩
  have hupper := hasBoundaryUpperBoundOn_of_datum_le hW hdiff
    (fun x => by simpa only [H1Function.sub_toFun] using (abs_le.mp (hdatum x)).2)
  have hdiffneg : MemH10 W
      (fun x => (-(u - v)).toFun x - (-(beta - gamma)).toFun x) := by
    convert memH10_neg hdiff using 1
    funext x
    simp only [H1Function.neg_toFun]
    ring
  have hlower := hasBoundaryUpperBoundOn_of_datum_le hW hdiffneg
    (fun x => by simpa only [H1Function.neg_toFun, H1Function.sub_toFun] using
      (neg_le.mpr (abs_le.mp (hdatum x)).1))
  have hb : ∀ᵐ x ∂volume.restrict W, lam ≤ A x ∧ A x ≤ Lam := by
    filter_upwards [self_mem_ae_restrict hW.isOpen.measurableSet] with x hx
    exact hbounds x hx
  simpa only [H1Function.sub_toFun] using
    ae_abs_le_of_isWeaklyHarmonicOn hW hlam hA.aestronglyMeasurable hb
    hharm hupper hlower

end SubdiffusiveProcess
