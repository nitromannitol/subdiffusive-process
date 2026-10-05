module

public import SubdiffusiveProcess.Paper.prop_21
public import SubdiffusiveProcess.Paper.prop_response_compact
public import SubdiffusiveProcess.Paper.conv_represented_sequence
public import SubdiffusiveProcess.Paper.prop_killed_inverse
public import SubdiffusiveProcess.Paper.conv_energy_measure_normalization
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.DirichletForm.All
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Topology.ContinuousMap.Compact

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology

namespace SubdiffusiveProcess.Paper



theorem rem_random_weights_catalog_transfer
    {d : ℕ} (_hd : 2 ≤ d) (Q : Opens (SpatialCoordinates d))
    (z : SpatialCoordinates d) (r : ℝ) (_hr : 0 < r)
    (_hQ : (Q : Set (SpatialCoordinates d)) = Metric.ball z (r / 2))
    [CompactSpace ↥(closure (Q : Set (SpatialCoordinates d)))]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ResponseSpace Q) (_hS : S.space = killedSobolevGraph Q)
    (a : ℕ → Ω → PositiveCoefficient Q)
    (potEval : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ) → SpatialCoordinates d → ℝ)
    (_hpotEval : ∀ (v : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ))
      (x : SpatialCoordinates d) (hx : x ∈ closure (Q : Set (SpatialCoordinates d))),
      potEval v x = v ⟨x, hx⟩)
    (aw : ℕ → Ω → C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ) → PositiveCoefficient Q)
    (_haw : ∀ n ω v, ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
      (aw n ω v).val x = Real.exp (potEval v x) * (a n ω).val x)
    (E : Ω → _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : ∀ ω, _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure (E ω))
    (_hGammaQ : ∀ ω u, u ∈ (E ω).domain →
      (Gamma ω).measure u (Q : Set (SpatialCoordinates d))ᶜ = 0)
    (R : C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ) → Ω → DomainL2 Q → ℝ)
    (_hR : ∀ v ω f, IsLUB {t : ℝ | ∃ u : DomainL2 Q, u ∈ (E ω).domain ∧
      t = 2 * inner ℝ f u - ∫ x in (Q : Set (SpatialCoordinates d)),
        Real.exp (potEval v x) ∂((Gamma ω).measure u)} (R v ω f))
    (catalog : ℕ → C(↥(closure (Q : Set (SpatialCoordinates d))), ℝ))
    (_hdense : DenseRange catalog) (_hzero : catalog 0 = 0)
    (hrepresented : ∀ k : ℕ, ∀ f : DomainL2 Q,
      ∃ (resp : ℕ → Ω → ℝ) (respLim : Ω → ℝ) (G : Set Ω),
        conv_represented_sequence P (ι := PUnit)
          (fun _ : PUnit => resp) (fun _ : PUnit => respLim)
          (fun _ _ _ => 0) G ∧
        (∀ n : ℕ, resp n =ᵐ[P]
          (fun ω => inverseResponse S (aw n ω (catalog k))
            ((sobolevVolumeLoad f).comp S.space.subtypeL))) ∧
        (respLim =ᵐ[P] (fun ω => R (catalog k) ω f)) ∧
        (∀ n : ℕ, AEMeasurable (resp n) P) ∧
        AEMeasurable respLim P) :
    (∀ k : ℕ, ∀ f : DomainL2 Q,
      TendstoInMeasure P (fun n ω => inverseResponse S (aw n ω (catalog k))
        ((sobolevVolumeLoad f).comp S.space.subtypeL)) atTop
        (fun ω => R (catalog k) ω f)) ∧
    (∀ (k : ℕ) (n : ℕ) (f : DomainL2 Q),
      AEMeasurable (fun ω => inverseResponse S (aw n ω (catalog k))
        ((sobolevVolumeLoad f).comp S.space.subtypeL)) P) ∧
    (∀ (k : ℕ) (f : DomainL2 Q),
      AEMeasurable (fun ω => R (catalog k) ω f) P) := by
  have htransfer : ∀ (k : ℕ) (f : DomainL2 Q),
      TendstoInMeasure P (fun n ω => inverseResponse S (aw n ω (catalog k))
        ((sobolevVolumeLoad f).comp S.space.subtypeL)) atTop
        (fun ω => R (catalog k) ω f) ∧
      (∀ n : ℕ, AEMeasurable (fun ω => inverseResponse S (aw n ω (catalog k))
        ((sobolevVolumeLoad f).comp S.space.subtypeL)) P) ∧
      AEMeasurable (fun ω => R (catalog k) ω f) P := by
    intro k f
    obtain ⟨resp, respLim, G, hconv, hresp, hlim, hresp_meas, hlim_meas⟩ :=
      hrepresented k f
    rcases hconv with ⟨_, _, hG_null, hpath, _⟩
    have hG : ∀ᵐ ω ∂P, ω ∈ G := by
      rw [ae_iff]
      exact hG_null
    have hresp_all : ∀ᵐ ω ∂P, ∀ n : ℕ,
        resp n ω = inverseResponse S (aw n ω (catalog k))
          ((sobolevVolumeLoad f).comp S.space.subtypeL) :=
      ae_all_iff.mpr hresp
    have hae : ∀ᵐ ω ∂P,
        Tendsto
          (fun n => inverseResponse S (aw n ω (catalog k))
            ((sobolevVolumeLoad f).comp S.space.subtypeL))
          atTop (𝓝 (R (catalog k) ω f)) := by
      filter_upwards [hG, hresp_all, hlim] with ω hω hrespω hlimω
      have hω' := hpath PUnit.unit ω hω
      simpa only [hrespω, hlimω] using hω'
    have hmeas : ∀ n : ℕ, AEMeasurable
        (fun ω => inverseResponse S (aw n ω (catalog k))
          ((sobolevVolumeLoad f).comp S.space.subtypeL)) P := by
      intro n
      exact (aemeasurable_congr (hresp n)).mp (hresp_meas n)
    have hlim_meas' : AEMeasurable (fun ω => R (catalog k) ω f) P :=
      (aemeasurable_congr hlim).mp hlim_meas
    exact ⟨tendstoInMeasure_of_tendsto_ae (fun n => (hmeas n).aestronglyMeasurable)
      hae, hmeas, hlim_meas'⟩
  refine ⟨?_, ?_, ?_⟩
  · intro k f
    exact (htransfer k f).1
  · intro k n f
    exact (htransfer k f).2.1 n
  · intro k f
    exact (htransfer k f).2.2

end SubdiffusiveProcess.Paper
