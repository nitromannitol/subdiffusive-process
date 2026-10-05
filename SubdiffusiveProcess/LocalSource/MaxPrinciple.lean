module

public import SubdiffusiveProcess.LocalSource.Harmonic
public import SubdiffusiveProcess.Sobolev.HarmonicDiffMaxPrinciple
public import SubdiffusiveProcess.Sobolev.NativeH10
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6MeasurableMaxPrinciple
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.Corrector

@[expose] public section

/-!
# The weak maximum principle for the Dirichlet minimizer

A killed-harmonic graph element `h` whose trace class is that of a datum `v` with `|v| ≤ M` a.e.
satisfies `|h| ≤ M` a.e.  The proof transports `h` to a native weakly `a`-harmonic `H¹` function and
applies the measurable-coefficient maximum principle of the Section 6 library: the positive part
`(h − M)₊` has zero trace because `h − v ∈ H¹₀` and `v` is clamped globally at level `M`.
-/

open MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum

namespace SubdiffusiveProcess

variable {d : ℕ}

/-- A positive coefficient is bounded above almost everywhere by its `L^∞` norm. -/
theorem localSource_ae_le_norm {Q : Opens (SpatialCoordinates d)} (a : PositiveCoefficient Q) :
    ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), a.val x ≤ ‖a.val‖ := by
  have h1 := enorm_ae_le_eLpNormEssSup (a.val : SpatialCoordinates d → ℝ)
    (volume.restrict (Q : Set (SpatialCoordinates d)))
  have hfin : eLpNormEssSup (a.val : SpatialCoordinates d → ℝ)
      (volume.restrict (Q : Set (SpatialCoordinates d))) ≠ ⊤ := by
    have := (Lp.memLp a.val).eLpNorm_lt_top
    rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable a.val)] at this
    exact this.ne
  filter_upwards [h1] with x hx
  have hn : ‖a.val x‖ ≤ ‖a.val‖ := by
    rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable a.val)]
    have := ENNReal.toReal_mono hfin hx
    simpa using this
  exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hn)

/-- **Weak maximum principle** for a killed-harmonic graph element with a bounded trace class. -/
theorem localSource_ae_abs_le [NeZero d] {Q : Opens (SpatialCoordinates d)}
    (hQ : Homogenization.IsOpenBoundedConvexDomain (Q : Set (SpatialCoordinates d)))
    (a : PositiveCoefficient Q) (h v : weakSobolevGraph Q)
    (hharm : ∀ psi : killedSobolevGraph Q, sobolevCoefficientForm a h.val psi.val = 0)
    (hdiff : h.val - v.val ∈ killedSobolevGraph Q) {M : ℝ} (hM : 0 ≤ M)
    (hv : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), |v.val.1 x| ≤ M) :
    ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), |h.val.1 x| ≤ M := by
  obtain ⟨hN, hNval, hNharm⟩ := localSource_isWeaklyHarmonicOn a h hharm
  obtain ⟨vN, vNval, -⟩ := exists_nativeH1Function_of_weakSobolevGraph v
  obtain ⟨e, hefun, -⟩ := exists_nativeH10Function_of_killedSobolevGraph
    (⟨h.val - v.val, hdiff⟩ : killedSobolevGraph Q)
  have hdiffN : Homogenization.MemH10 (Q : Set (SpatialCoordinates d))
      (fun y => hN.toFun y - vN.toFun y) := by
    refine memH10_congr (f := e.toH1Function.toFun) ⟨e, rfl⟩ ?_
    filter_upwards [Lp.coeFn_sub h.val.1 v.val.1] with x hx
    have h1 : e.toH1Function.toFun x = (h.val - v.val).1 x := congrFun hefun x
    rw [h1]
    change (h.val.1 - v.val.1 : DomainL2 Q) x = _
    rw [hx]
    simp only [Pi.sub_apply]
    rw [show hN.toFun x = h.val.1 x from congrFun hNval x,
      show vN.toFun x = v.val.1 x from congrFun vNval x]
  obtain ⟨Ψ, hΨup, hΨlow, hΨeq⟩ := exists_h1_clamp hQ vN hM
  have hΨae : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), Ψ.toFun x = vN.toFun x := by
    filter_upwards [hv] with x hx
    apply hΨeq
    rw [show vN.toFun x = v.val.1 x from congrFun vNval x]
    exact hx
  have hdiffΨ : Homogenization.MemH10 (Q : Set (SpatialCoordinates d))
      (fun y => hN.toFun y - Ψ.toFun y) :=
    memH10_congr hdiffN (by
      filter_upwards [hΨae] with x hx
      rw [hx])
  have hup : HasBoundaryUpperBoundOn (Q : Set (SpatialCoordinates d)) hN M :=
    hasBoundaryUpperBoundOn_of_datum_le hQ hdiffΨ hΨup
  have hdiffneg : Homogenization.MemH10 (Q : Set (SpatialCoordinates d))
      (fun y => (-hN).toFun y - (-Ψ).toFun y) := by
    have h' := Homogenization.memH10_neg hdiffΨ
    have hfun : (fun y => -(hN.toFun y - Ψ.toFun y)) =
        fun y => (-hN).toFun y - (-Ψ).toFun y := by
      funext y
      rw [Homogenization.H1Function.neg_toFun, Homogenization.H1Function.neg_toFun]
      ring
    rwa [hfun] at h'
  have hlow : HasBoundaryUpperBoundOn (Q : Set (SpatialCoordinates d)) (-hN) M := by
    refine hasBoundaryUpperBoundOn_of_datum_le hQ hdiffneg fun y => ?_
    rw [Homogenization.H1Function.neg_toFun]
    show -Ψ.toFun y ≤ M
    linarith only [hΨlow y]
  obtain ⟨c, hc, hac⟩ := a.property
  have hbounds : ∀ᵐ y ∂(Homogenization.volumeMeasureOn (Q : Set (SpatialCoordinates d))),
      c ≤ (fun x => a.val x) y ∧ (fun x => a.val x) y ≤ ‖a.val‖ := by
    filter_upwards [hac, localSource_ae_le_norm a] with y h1 h2
    exact ⟨h1, h2⟩
  have hmeas : AEStronglyMeasurable (fun x => a.val x)
      (Homogenization.volumeMeasureOn (Q : Set (SpatialCoordinates d))) :=
    (Lp.memLp a.val).aestronglyMeasurable
  have hfin := ae_abs_le_of_isWeaklyHarmonicOn hQ hc hmeas hbounds hNharm hup hlow
  filter_upwards [hfin] with x hx
  rwa [show hN.toFun x = h.val.1 x from congrFun hNval x] at hx

end SubdiffusiveProcess
