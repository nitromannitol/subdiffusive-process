module

public import SubdiffusiveProcess.Sobolev.HarmonicityTransfer
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Variational.WeightedL2

@[expose] public section

/-!
# Transporting `sobolevCoefficientForm`-harmonicity to `IsWeaklyHarmonicOn`

`HarmonicityTransfer` does this for the coefficient `1`.  Here the coefficient is an arbitrary
`PositiveCoefficient`: a graph element `h` with `E_a(h, ψ) = 0` for every killed `ψ` is
represented by a native `H¹` function weakly `a`-harmonic in the sense of the Section 6 vocabulary.
-/

open MeasureTheory Set TopologicalSpace

namespace SubdiffusiveProcess

variable {d : ℕ}

/-- A killed-harmonic graph element is a weakly `a`-harmonic native `H¹` function. -/
theorem localSource_isWeaklyHarmonicOn {Q : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Q) (h : weakSobolevGraph Q)
    (hharm : ∀ psi : killedSobolevGraph Q,
      sobolevCoefficientForm a h.val psi.val = 0) :
    ∃ h' : Homogenization.H1Function (Q : Set (SpatialCoordinates d)),
      (h' : SpatialCoordinates d → ℝ) = (fun x => h.val.1 x) ∧
      SubdiffusiveProcess.CoarseGrainingVocab.IsWeaklyHarmonicOn (fun x => a.val x)
        (Q : Set (SpatialCoordinates d)) h' := by
  obtain ⟨h', hval, hgrad⟩ := exists_nativeH1Function_of_weakSobolevGraph h
  refine ⟨h', hval, fun φ => ?_⟩
  obtain ⟨u, humem, hu1, hu2⟩ := exists_killedSobolevGraph_of_h10Function φ
  have hz := hharm ⟨u, humem⟩
  rw [sobolevCoefficientForm_apply] at hz
  have hint : ∀ i : Fin d, Integrable (fun x => a.val x * (h.val.2 i x * u.2 i x))
      (volume.restrict (Q : Set (SpatialCoordinates d))) := by
    intro i
    have := integrable_weighted_inner (μ := volume.restrict (Q : Set (SpatialCoordinates d)))
      a.val (h.val.2 i) (u.2 i)
    simpa [RCLike.inner_apply, mul_comm] using this
  have hpt : ∀ x, Homogenization.vecDot (a.val x • h'.grad x) (φ.toH1Function.grad x) =
      ∑ i : Fin d, a.val x * (h.val.2 i x * φ.toH1Function.grad x i) := by
    intro x
    rw [Homogenization.vecDot]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hgrad]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hcongr : ∀ i : Fin d,
      ∫ x in (Q : Set (SpatialCoordinates d)), a.val x * (h.val.2 i x * φ.toH1Function.grad x i) =
        ∫ x in (Q : Set (SpatialCoordinates d)), a.val x * (h.val.2 i x * u.2 i x) := by
    intro i
    refine integral_congr_ae ?_
    filter_upwards [hu2 i] with x hx
    rw [hx]
  show ∫ x in (Q : Set (SpatialCoordinates d)),
      Homogenization.vecDot (a.val x • h'.grad x) (φ.toH1Function.grad x) ∂volume = 0
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have hint' : ∀ i ∈ (Finset.univ : Finset (Fin d)), Integrable
      (fun x => a.val x * (h.val.2 i x * φ.toH1Function.grad x i))
      (volume.restrict (Q : Set (SpatialCoordinates d))) := by
    intro i _
    refine (hint i).congr ?_
    filter_upwards [hu2 i] with x hx
    rw [hx]
  rw [integral_finset_sum _ hint']
  simp only [hcongr]
  exact hz

end SubdiffusiveProcess
