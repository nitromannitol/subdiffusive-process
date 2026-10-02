import SubdiffusiveProcess.Lane1.CampanatoCutoff

open Filter MeasureTheory Topology
open SubdiffusiveProcess
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem cutoff_campanato_bound
    {d : ℕ} {z : SpatialCoordinates d} {rQ : ℝ} (hrQ : 0 < rQ)
    {alpha : ℝ} (halpha : 0 < alpha)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (u : SpatialCoordinates d → ℝ) {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hint : LocallyIntegrable u volume)
    (hzero : ∀ x ∉ (centeredCube z rQ hrQ : Set (SpatialCoordinates d)), u x = 0)
    (hcont : ContinuousOn u
      (closure (centeredCube z rQ hrQ : Set (SpatialCoordinates d))))
    (hosc : ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
      (∫ y in Metric.ball x r,
          (u y - (volume.real (Metric.ball x r))⁻¹ *
            ∫ w in Metric.ball x r, u w) ^ 2) ≤
        (K * ‖f‖) ^ 2 * volume.real (Metric.ball x r) * r ^ (2 * alpha))
    (hcamp : ∀ (u' : SpatialCoordinates d → ℝ) (A : ℝ), 0 ≤ A →
        LocallyIntegrable u' volume → LocallyIntegrable (fun x => (u' x) ^ 2) volume →
        (∀ x ∉ (centeredCube z rQ hrQ : Set (SpatialCoordinates d)), u' x = 0) →
        (∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
          (∫ y in Metric.ball x r,
              (u' y - (volume.real (Metric.ball x r))⁻¹ *
                ∫ w in Metric.ball x r, u' w) ^ 2) ≤
            A ^ 2 * volume.real (Metric.ball x r) * r ^ (2 * alpha)) →
        ∃ v : SpatialCoordinates d → ℝ,
          v =ᵐ[volume] u' ∧
          (∀ x y : SpatialCoordinates d, |v x - v y| ≤ C * A * dist x y ^ alpha) ∧
          ∀ x ∉ (centeredCube z rQ hrQ : Set (SpatialCoordinates d)), v x = 0) :
    ∀ x ∈ closure (centeredCube z rQ hrQ : Set (SpatialCoordinates d)),
      ∀ y ∈ closure (centeredCube z rQ hrQ : Set (SpatialCoordinates d)),
        |u x - u y| ≤ C * (K * ‖f‖) * dist x y ^ alpha := by
  let U : Set (SpatialCoordinates d) := centeredCube z rQ hrQ
  have hUopen : IsOpen U := by
    dsimp [U]
    exact (centeredCube z rQ hrQ).isOpen
  have hucomp : ContinuousOn u Uᶜ := by
    apply ContinuousOn.congr continuousOn_const
    intro x hx
    exact hzero x hx
  have huall : Continuous u := by
    have huunion : ContinuousOn u (closure U ∪ Uᶜ) :=
      hcont.union_of_isClosed hucomp isClosed_closure hUopen.isClosed_compl
    have hunion : closure U ∪ Uᶜ = (Set.univ : Set (SpatialCoordinates d)) := by
      apply Set.eq_univ_of_forall
      intro x
      by_cases hx : x ∈ U
      · exact Or.inl (subset_closure hx)
      · exact Or.inr hx
    rw [hunion] at huunion
    exact continuousOn_univ.mp huunion
  have husq : LocallyIntegrable (fun x => (u x) ^ 2) volume := by
    exact (huall.pow 2).locallyIntegrable
  have hA : 0 ≤ K * ‖f‖ := mul_nonneg hK (norm_nonneg f)
  obtain ⟨v, hvae, hvholder, _⟩ :=
    hcamp u (K * ‖f‖) hA hint husq hzero (fun x r hr hr1 => hosc x r hr hr1)
  exact SubdiffusiveProcess.cutoff_campanato_bound hrQ halpha u
    (mul_nonneg hC hA) hcont v hvae hvholder

end Paper
