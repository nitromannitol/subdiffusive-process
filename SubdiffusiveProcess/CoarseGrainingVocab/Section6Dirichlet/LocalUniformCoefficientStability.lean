import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.CoefficientPerturbationEnergy

/-!
# Dirichlet stability under locally uniform scalar-coefficient convergence

This module discharges the integrability premises of the scalar coefficient
perturbation identity from the usual matrix ellipticity carrier, then applies
the quantitative estimate directly to a uniform limit on a containing set.
It is deterministic and independent of the cutoff construction.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-- The scalar-coefficient flux paired with a difference of two `H¹`
gradients is integrable whenever the associated scalar matrix field is
elliptic. -/
theorem integrableOn_scalarFlux_gradDifference_of_isEllipticFieldOn
    {W : Set (Vec d)} {a : Vec d → ℝ} {lambda Lambda : ℝ}
    (hEll : IsEllipticFieldOn lambda Lambda W (scalarCoeffField a))
    (q u v : H1Function W) :
    IntegrableOn
      (fun x ↦ vecDot (a x • q.grad x) (u.grad x - v.grad x)) W := by
  have hflux : MemVectorL2 W (fun x ↦ a x • q.grad x) := by
    simpa only [scalarCoeffField, Homogenization.matVecMul_scalarMatrix] using
      (memVectorL2_matVecMul_of_isEllipticFieldOn hEll q.grad_memVectorL2)
  exact integrableOn_vecDot_of_memVectorL2 hflux
    (u.grad_memVectorL2.sub v.grad_memVectorL2)

/-- **Strong-gradient continuity under local uniform coefficient
convergence.**  Let `u n` and `ulim` be scalar-coefficient harmonic functions
with a common trace.  If the coefficients `a n` converge uniformly to `alim`
on a set containing the PDE domain, the approximate coefficients have a
common positive lower ellipticity bound, and both the approximate and limiting
scalar matrix fields are elliptic, then `grad (u n)` converges strongly in
`L²` to `grad ulim`.

Unlike `tendsto_l2NormOn_gradDifference_of_coefficient_close`, this statement
constructs the coefficient tolerance directly from the uniform-convergence
filter and discharges all pairing-integrability premises from ellipticity. -/
theorem tendsto_l2NormOn_gradDifference_of_tendstoUniformlyOn
    {W K : Set (Vec d)} {a : ℕ → Vec d → ℝ} {alim : Vec d → ℝ}
    {u : ℕ → H1Function W} {ulim h : H1Function W}
    {lambda LambdaLim : ℝ} {Lambda : ℕ → ℝ}
    (hWm : MeasurableSet W) (hWK : W ⊆ K) (hlambda : 0 < lambda)
    (halow : ∀ n x, x ∈ W → lambda ≤ a n x)
    (haEll : ∀ n,
      IsEllipticFieldOn lambda (Lambda n) W (scalarCoeffField (a n)))
    (halimEll : IsEllipticFieldOn lambda LambdaLim W (scalarCoeffField alim))
    (haLim : TendstoUniformlyOn a alim Filter.atTop K)
    (huTrace : ∀ n, HasZeroTraceDifferenceOn W (u n) h)
    (hulimTrace : HasZeroTraceDifferenceOn W ulim h)
    (huHarm : ∀ n, IsWeaklyHarmonicOn (a n) W (u n))
    (hulimHarm : IsWeaklyHarmonicOn alim W ulim) :
    Filter.Tendsto
      (fun n ↦ Section5Support.l2NormOn W
        (fun x ↦ (u n).grad x - ulim.grad x))
      Filter.atTop (nhds 0) := by
  let V := Section5Support.l2NormOn W ulim.grad
  have hVnonneg : 0 ≤ V := Section5Support.l2NormOn_nonneg W ulim.grad
  refine Metric.tendsto_atTop.2 fun epsilon hepsilon ↦ ?_
  let eta := epsilon * lambda / (V + 1)
  have hVone : 0 < V + 1 := by positivity
  have heta : 0 < eta := div_pos (mul_pos hepsilon hlambda) hVone
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (Metric.tendstoUniformlyOn_iff.1 haLim eta heta)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hclose : ∀ x ∈ W, |alim x - a n x| ≤ eta := by
    intro x hx
    have hdist := hN n hn x (hWK hx)
    simpa only [Real.dist_eq] using hdist.le
  have hau :=
    integrableOn_scalarFlux_gradDifference_of_isEllipticFieldOn
      (haEll n) (u n) (u n) ulim
  have hav :=
    integrableOn_scalarFlux_gradDifference_of_isEllipticFieldOn
      (haEll n) ulim (u n) ulim
  have hbv :=
    integrableOn_scalarFlux_gradDifference_of_isEllipticFieldOn
      halimEll ulim (u n) ulim
  have hbound := l2NormOn_gradDifference_le_of_coefficient_close
    hWm hlambda heta.le (halow n) hclose (huTrace n) hulimTrace
    (huHarm n) hulimHarm hau hav hbv
  rw [Real.dist_eq, sub_zero, abs_of_nonneg
    (Section5Support.l2NormOn_nonneg W
      (fun x ↦ (u n).grad x - ulim.grad x))]
  refine lt_of_le_of_lt hbound ?_
  dsimp only [eta, V]
  have hratio :
      Section5Support.l2NormOn W ulim.grad /
          (Section5Support.l2NormOn W ulim.grad + 1) < 1 := by
    exact (div_lt_one hVone).2 (by linarith)
  calc
    epsilon * lambda /
          (Section5Support.l2NormOn W ulim.grad + 1) / lambda *
        Section5Support.l2NormOn W ulim.grad =
        epsilon *
          (Section5Support.l2NormOn W ulim.grad /
            (Section5Support.l2NormOn W ulim.grad + 1)) := by
      field_simp
    _ < epsilon * 1 := mul_lt_mul_of_pos_left hratio hepsilon
    _ = epsilon := mul_one _

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
