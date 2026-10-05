module

public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.NativeInfraredLimit
public import SubdiffusiveProcess.Probability.InfraredCommonFieldConvergence
public import Mathlib.Topology.Metrizable.ContinuousMap

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess

theorem exists_infraredCharacterization {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    ∃ H : BilateralField d → C(SpatialCoordinates d, ℝ),
      InfraredCharacterization M H := by
  classical
  obtain ⟨Cconst, hCnonneg, hCM⟩ := exists_native_infrared_limit hd
  obtain ⟨Hn, hHnmeas, hHnCont, hHnLimAE, hLpLayer, hLpAll⟩ := hCM M
  have hExists :=
    infraredPartialSum_tendsto_of_native_infrared_limit M Hn
      (hHnLimAE.mono (fun omega h => ⟨h.1, h.2.1⟩))
  have hmeas : ∀ L : ℕ, Measurable (fun beta : BilateralField d =>
      infraredPartialSum beta L) := by
    intro L
    unfold infraredPartialSum
    apply Continuous.measurable
    apply continuous_finsetSum
    intro n hn
    have hcoord : Continuous (fun beta : BilateralField d =>
        beta (Int.ofNat (n + 1))) := continuous_apply (Int.ofNat (n + 1))
    have heval0 : Continuous (fun f : C(SpatialCoordinates d, ℝ) => f 0) :=
      continuous_eval_const 0
    have hc : Continuous (fun beta : BilateralField d =>
        ContinuousMap.const (SpatialCoordinates d) ((beta (Int.ofNat (n + 1))) 0)) := by
      simpa [ContinuousMap.constPi, Function.comp_def] using
        ((ContinuousMap.continuous_const' (X := SpatialCoordinates d) (Y := ℝ)).comp
          (heval0.comp hcoord))
    exact (continuous_apply (Int.ofNat (n + 1))).sub hc
  let good : Set (BilateralField d) :=
    {beta | ∃ y : C(SpatialCoordinates d, ℝ),
      Tendsto (fun L => infraredPartialSum beta L) atTop (nhds y)}
  have hgood_meas : MeasurableSet good := by
    apply MeasureTheory.measurableSet_exists_tendsto
    intro L
    exact hmeas L
  let : TopologicalSpace.MetrizableSpace C(SpatialCoordinates d, ℝ) := inferInstance
  let G : ℕ → BilateralField d → C(SpatialCoordinates d, ℝ) := fun L beta =>
    if hβ : beta ∈ good then infraredPartialSum beta L else 0
  have hG : ∀ L : ℕ, Measurable (G L) := by
    intro L
    dsimp [G]
    exact Measurable.ite hgood_meas (hmeas L) measurable_const
  let H : BilateralField d → C(SpatialCoordinates d, ℝ) := fun beta =>
    if hβ : beta ∈ good then Classical.choose hβ else 0
  have hlim : Tendsto G atTop (nhds H) := by
    rw [tendsto_pi_nhds]
    intro beta
    by_cases hβ : beta ∈ good
    · simpa only [G, H, dite_eq_left hβ] using Classical.choose_spec hβ
    · simp only [G, H, dite_eq_right hβ]
      exact tendsto_const_nhds
  have hHmeas : Measurable H := measurable_of_tendsto_metrizable hG hlim
  refine ⟨H, hHmeas, ?_⟩
  filter_upwards [hExists] with omega hω
  have hmem : omega ∈ good := hω
  simpa only [H, dite_eq_left hmem] using Classical.choose_spec hmem

end SubdiffusiveProcess
