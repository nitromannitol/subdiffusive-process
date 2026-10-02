import MarkovProcess.Continuity.DenseTimeContinuousSupport
import MarkovProcess.Continuity.GlobalDyadicFloorModification

/-! Continuous-path support from unit-interval Kolmogorov bounds. -/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MarkovProcess Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem unitDyadicFloorLimit_congr_on_unit {Omega E : Type*}
    [PseudoMetricSpace E] [CompleteSpace E] (X Y : NNRat → Omega → E) (omega : Omega)
    (h : ∀ r : NNRat, r ≤ 1 → X r omega = Y r omega) :
    unitDyadicFloorLimit X omega = unitDyadicFloorLimit Y omega := by
  funext t
  unfold unitDyadicFloorLimit
  congr 1
  funext n
  apply h
  exact_mod_cast ((unitDyadicFloorValue_le n t).trans t.2.2)

theorem shiftedUnitDyadicFloorLimit_eq_clipped {Omega E : Type*}
    [PseudoMetricSpace E] [CompleteSpace E] (X : NNRat → Omega → E)
    (omega : Omega) (n : ℕ) :
    shiftedUnitDyadicFloorLimit (n : NNRat) X omega =
      unitDyadicFloorLimit (fun t ↦ X ((n : NNRat) + min t 1)) omega := by
  unfold shiftedUnitDyadicFloorLimit
  apply unitDyadicFloorLimit_congr_on_unit
  intro r hr
  simp only [timeShift, min_eq_left hr]

theorem globalDyadicFloorLimit_nat_add {Omega E : Type*}
    [MetricSpace E] [CompleteSpace E] (X : NNRat → Omega → E) (omega : Omega)
    (n : ℕ) (t : NNRat) (ht : t ≤ 1) :
    globalDyadicFloorLimit X omega (↑((n:NNRat)+t):NNReal) =
      shiftedUnitDyadicFloorLimit (n:NNRat) X omega (unitIccOfNNRat t ht) := by
  set x : NNReal := ↑((n:NNRat)+t) with hx_def
  have hx : x ∈ nnrealUnitInterval n := by
    constructor
    · change (n : NNReal) ≤ ↑((n : NNRat) + t)
      exact_mod_cast (le_add_of_nonneg_right t.2 : (n : NNRat) ≤ (n : NNRat) + t)
    · change (↑((n : NNRat) + t) : NNReal) ≤ (n : NNReal) + 1
      have hu : (n : NNRat) + t ≤ (n : NNRat) + 1 := by
        simpa only [add_comm] using add_le_add_left ht (n : NNRat)
      exact_mod_cast hu
  have hcoord : nnrealUnitCoordinate n ⟨x, hx⟩ = unitIccOfNNRat t ht := by
    apply Subtype.ext
    simp only [nnrealUnitCoordinate, unitIccOfNNRat, hx_def]
    push_cast
    ring_nf
    change (((t : NNRat) : NNReal) : ℝ) = (t : ℝ)
    exact_mod_cast rfl
  rw [globalDyadicFloorLimit_coe X omega n ⟨x, hx⟩]
  simp only [globalDyadicFloorPiece, hcoord]

/-- Bounds on each unit interval suffice for continuous-path support; no
uniform-in-time moment constant is required. -/
theorem supportedOnContinuousPaths_of_unitKolmogorov {beta alpha : Type*}
    [MeasurableSpace beta] [MetricSpace alpha] [CompleteSpace alpha]
    [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
    (kappa : Kernel beta (DenseTime → alpha)) [IsMarkovKernel kappa]
    (hlocal : ∀ b (n : ℕ), ∃ M : ℝ≥0, IsKolmogorovProcess
      (fun t : NNRat ↦ fun omega : DenseTime → alpha ↦ omega ((n : NNRat) + min t 1))
      (kappa b) 4 2 M) :
    Kernel.IsSupportedOnContinuousPaths kappa := by
  intro b
  let X : NNRat → (DenseTime → alpha) → alpha := fun r omega ↦ omega r
  have hcont : ∀ᵐ omega ∂kappa b, Continuous (globalDyadicFloorLimit X omega) := by
    have hpieces : ∀ᵐ omega ∂kappa b, ∀ n : ℕ,
        Continuous (shiftedUnitDyadicFloorLimit n X omega) := by
      rw [ae_all_iff]
      intro n
      obtain ⟨M, hM⟩ := hlocal b n
      have h := IsKolmogorovProcess.ae_continuous_unitDyadicFloorLimit
        hM (show (0 : ℝ) < 1 / 8 by norm_num) (show (1 : ℝ) / 8 < (2 - 1) / 4 by norm_num)
      filter_upwards [h] with omega homega
      rw [shiftedUnitDyadicFloorLimit_eq_clipped]
      exact homega
    exact hpieces.mono fun _ h ↦ continuous_globalDyadicFloorLimit_of_forall h
  have hmatch : ∀ q : DenseTime, ∀ᵐ omega ∂kappa b,
      omega q = globalDyadicFloorLimit X omega (q : NNReal) := by
    intro q
    let n := nnratNatFloor q
    let t := nnratUnitRemainder q
    have ht : t ≤ 1 := nnratUnitRemainder_le_one q
    have hnt : (n : NNRat) + t = q := nnratNatFloor_add_unitRemainder q
    obtain ⟨M, hM⟩ := hlocal b n
    have h := IsKolmogorovProcess.ae_eq_unitDyadicFloorLimit hM
      (show (0 : ℝ) < 1 / 8 by norm_num) (show (1 : ℝ) / 8 < (2 - 1) / 4 by norm_num) t ht
    filter_upwards [h] with omega homega
    have hp := congrFun (shiftedUnitDyadicFloorLimit_eq_clipped X omega n) (unitIccOfNNRat t ht)
    rw [min_eq_left ht, hnt] at homega
    have heval := globalDyadicFloorLimit_nat_add X omega n t ht
    rw [hnt] at heval
    exact homega.trans (hp.symm.trans heval.symm)
  have hall : ∀ᵐ omega ∂kappa b, ∀ q : DenseTime,
      omega q = globalDyadicFloorLimit X omega (q : NNReal) := ae_all_iff.2 hmatch
  filter_upwards [hcont, hall] with omega hcontinuous homega
  refine ⟨⟨globalDyadicFloorLimit X omega, hcontinuous⟩, ?_⟩
  funext q
  exact (homega q).symm

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
