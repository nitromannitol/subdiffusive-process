import SubdiffusiveProcess.Sobolev.NativeH1
import SubdiffusiveProcess.Sobolev.NativeH10Reverse
import SubdiffusiveProcess.Sobolev.GradientRange
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase




open MeasureTheory Set TopologicalSpace

namespace SubdiffusiveProcess

/-- Componentwise, `sobolevGradient` is exactly the coordinate gradient. -/
theorem sobolevGradient_apply {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (z : SobolevData Ω) (i : Fin d) :
    (sobolevGradient z) i = z.2 i := by
  simp [sobolevGradient]

/-- A `weakSobolevGraph`-harmonicity hypothesis (tested against
`killedSobolevGraph` elements) transports, via the native `H1Function`/
`H10Function` bridges, to `Homogenization`'s `IsWeaklyHarmonicOn` (tested
against `H10Function` elements). -/
theorem isWeaklyHarmonicOn_of_weakSobolevGraph_harm {d : ℕ} [NeZero d]
    {Ω : Opens (SpatialCoordinates d)}
    (v : weakSobolevGraph Ω)
    (hharm : ∀ psi : killedSobolevGraph Ω,
      inner ℝ (sobolevGradient v.val) (subspaceGradient (killedSobolevGraph Ω) psi) = 0) :
    ∃ v' : Homogenization.H1Function (Ω : Set (SpatialCoordinates d)),
      (v' : SpatialCoordinates d → ℝ) = (fun x => v.val.1 x) ∧
      SubdiffusiveProcess.CoarseGrainingVocab.IsWeaklyHarmonicOn (fun _ => (1 : ℝ))
        (Ω : Set (SpatialCoordinates d)) v' := by
  obtain ⟨v', hv'val, hv'grad⟩ := exists_nativeH1Function_of_weakSobolevGraph v
  refine ⟨v', hv'val, fun φ => ?_⟩
  obtain ⟨u, humem, hu1, hu2⟩ := exists_killedSobolevGraph_of_h10Function φ
  have hinner := hharm ⟨u, humem⟩
  have hsubgrad : subspaceGradient (killedSobolevGraph Ω) (⟨u, humem⟩ : killedSobolevGraph Ω) =
      sobolevGradient u := rfl
  rw [hsubgrad, PiLp.inner_apply] at hinner
  simp only [sobolevGradient_apply] at hinner
  have hL2 : ∀ i, (inner ℝ (v.val.2 i) (u.2 i) : ℝ) =
      ∫ x in (Ω : Set (SpatialCoordinates d)), v.val.2 i x * u.2 i x ∂volume := by
    intro i
    rw [L2.inner_def]
    simp only [RCLike.inner_apply, conj_trivial, mul_comm]
  have hcongr : ∀ i, (∫ x in (Ω : Set (SpatialCoordinates d)), v.val.2 i x * u.2 i x ∂volume) =
      ∫ x in (Ω : Set (SpatialCoordinates d)), v.val.2 i x * φ.toH1Function.grad x i ∂volume := by
    intro i
    refine integral_congr_ae ?_
    filter_upwards [hu2 i] with x hx
    rw [hx]
  have hint : ∀ i, IntegrableOn
      (fun x => v.val.2 i x * φ.toH1Function.grad x i) (Ω : Set (SpatialCoordinates d)) volume :=
    fun i => (Lp.memLp (v.val.2 i)).integrable_mul (φ.toH1Function.gradMemL2 i)
  have hpt : ∀ x, Homogenization.vecDot (v'.grad x) (φ.toH1Function.grad x) =
      ∑ i, v.val.2 i x * φ.toH1Function.grad x i := by
    intro x
    rw [Homogenization.vecDot]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hv'grad]
  have hsum : (∫ x in (Ω : Set (SpatialCoordinates d)),
      Homogenization.vecDot (v'.grad x) (φ.toH1Function.grad x) ∂volume) =
      ∑ i, ∫ x in (Ω : Set (SpatialCoordinates d)), v.val.2 i x * φ.toH1Function.grad x i ∂volume := by
    rw [← integral_finset_sum Finset.univ (fun i _ => hint i)]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  show ∫ x in (Ω : Set (SpatialCoordinates d)),
      Homogenization.vecDot ((1 : ℝ) • v'.grad x) (φ.toH1Function.grad x) ∂volume = 0
  simp only [one_smul]
  rw [hsum]
  simp only [← hcongr, ← hL2]
  exact hinner

end SubdiffusiveProcess
