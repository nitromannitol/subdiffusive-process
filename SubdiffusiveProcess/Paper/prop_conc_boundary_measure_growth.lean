module

public import SubdiffusiveProcess.Paper.prop_boundary
public import SubdiffusiveProcess.Probability.DominatedWeakGrowth

@[expose] public section

/-! Eventual resolved-scale bounds pass to local energy measures dominated by every weak cluster.
The compactness and domination premises are the existing energy-measure convergence interface. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology
namespace SubdiffusiveProcess.Paper
noncomputable section

/-- Compactly supported energy measures pass eventual local bounds to their dominated limit measure. -/
theorem prop_conc_boundary_measure_growth
    {d : ℕ} (K : Set (SpatialCoordinates d)) (hK : IsCompact K)
    (muN : ℕ → Measure (SpatialCoordinates d)) (nu : Measure (SpatialCoordinates d))
    (E0 : ℝ) (hsupp : ∀ n, muN n Kᶜ = 0)
    (hmass : ∀ n, muN n Set.univ ≤ ENNReal.ofReal E0)
    (hdom : ∀ (mu : Measure (SpatialCoordinates d)) (sigma : ℕ → ℕ),
      mu Set.univ < ⊤ → mu Kᶜ = 0 → StrictMono sigma →
      (∀ phi : SpatialCoordinates d → ℝ, ContinuousOn phi K →
        Tendsto (fun n => ∫ x, phi x ∂muN (sigma n)) atTop (𝓝 (∫ x, phi x ∂mu))) →
      ∀ B : Set (SpatialCoordinates d), MeasurableSet B → nu B ≤ mu B)
    {T : Type*} (tests : T → Set (SpatialCoordinates d)) (hopen : ∀ t, IsOpen (tests t))
    (bound : T → ℝ≥0∞) (hb : ∀ t, ∀ᶠ n in atTop, muN n (tests t) ≤ bound t) :
    ∀ t, nu (tests t) ≤ bound t := by
  obtain ⟨mu, sigma, hsig, hfin, hs, hw⟩ :=
    aux_prop_boundary_weak_cluster K hK muN E0 hsupp hmass
  let muf : FiniteMeasure (SpatialCoordinates d) := ⟨mu, ⟨hfin⟩⟩
  let mus : ℕ → FiniteMeasure (SpatialCoordinates d) :=
    fun n => ⟨muN (sigma n), ⟨(hmass (sigma n)).trans_lt ENNReal.ofReal_lt_top⟩⟩
  have hweak : Tendsto mus atTop (𝓝 muf) :=
    FiniteMeasure.tendsto_of_forall_integral_tendsto
      (fun phi => hw phi phi.continuous.continuousOn)
  intro t
  exact measure_le_of_dominated_weak_limit_eventually nu hweak
    (hdom mu sigma hfin hs hsig hw) (hopen t) (bound t)
    (hsig.tendsto_atTop.eventually (hb t))

end
end SubdiffusiveProcess.Paper
