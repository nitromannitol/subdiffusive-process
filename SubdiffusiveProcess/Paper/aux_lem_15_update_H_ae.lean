import SubdiffusiveProcess.Main.InfraredPartialSum
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.CommonScaleLaw
import SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1
import SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2
import SubdiffusiveProcess.Probability.CopyLayerBlock
import Mathlib.Tactic
import SubdiffusiveProcess.Paper.in_common_scale_coupling
import SubdiffusiveProcess.Paper.lem_infrared

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology

noncomputable section
namespace Paper



theorem aux_lem_15_update_H_ae
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (delta : ℝ) (hdelta : 0 < delta) (hdelta_le : delta ≤ 1)
    (Praw : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d))
    (hG1 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 d Praw)
    (hG2 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2 d delta Praw)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hHmeas : Measurable H)
    (hHconv :
      ∀ᵐ omega ∂((commonScaleLaw d
        ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
          (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
            C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
              C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable)).toMeasure),
        Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega)))
    (j : ℕ) :
    let P : Measure (BilateralField d) :=
      (commonScaleLaw d
        ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
          (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
            C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
              C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable)).toMeasure
    ∀ᵐ pair ∂(P.prod P),
      H pair.1 =
        H (Function.update pair.1 (-(j : ℤ)) (pair.2 (-(j : ℤ))))
    := by
  dsimp only
  let ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ) :=
    (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
      (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
        C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
          C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable
  let P : Measure (BilateralField d) := (commonScaleLaw d ν).toMeasure
  have hHconv' : ∀ᵐ omega ∂P,
      Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega)) := by
    simpa [P, ν] using hHconv
  let k : ℤ := -(j : ℤ)
  have hcopy : MeasurePreserving
      (fun pair : BilateralField d × BilateralField d =>
        fun i : ℤ => if i ∈ ({k} : Set ℤ) then pair.2 i else pair.1 i)
      (P.prod P) P := by
    simpa [P, ν, commonScaleLaw] using
      (SubdiffusiveProcess.measurePreserving_copy_infinitePi_block
        (μ := fun i : ℤ =>
          (scaledLayerLaw d ν i : Measure C(SpatialCoordinates d, ℝ)))
        ({k} : Set ℤ))
  have hfst : MeasurePreserving Prod.fst (P.prod P) P :=
    measurePreserving_fst
  have hconv₁ : ∀ᵐ pair ∂(P.prod P),
      Tendsto (infraredPartialSum pair.1) atTop (𝓝 (H pair.1)) := by
    simpa only [Function.comp_apply] using
      hfst.quasiMeasurePreserving.ae hHconv'
  have hconv₂ : ∀ᵐ pair ∂(P.prod P),
      Tendsto (infraredPartialSum (Function.update pair.1 k (pair.2 k))) atTop
        (𝓝 (H (Function.update pair.1 k (pair.2 k)))) := by
    have h := hcopy.quasiMeasurePreserving.ae hHconv'
    filter_upwards [h] with pair hp
    have hfun : (fun i : ℤ => if i ∈ ({k} : Set ℤ) then pair.2 i else pair.1 i) =
        Function.update pair.1 k (pair.2 k) := by
      funext i
      by_cases hi : i = k
      · subst i
        simp
      · simp [Function.update, hi]
    rw [hfun] at hp
    exact hp
  filter_upwards [hconv₁, hconv₂] with pair hp₁ hp₂
  apply tendsto_nhds_unique hp₁
  apply hp₂.congr'
  filter_upwards [] with L
  have hω (n : ℕ) :
      Function.update pair.1 k (pair.2 k) (Int.ofNat (n + 1)) =
        pair.1 (Int.ofNat (n + 1)) := by
    simp [Function.update, k]
    omega
  simp only [infraredPartialSum]
  simp_rw [hω]

end Paper
