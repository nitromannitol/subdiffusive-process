module

public import SubdiffusiveProcess.Section10.PhysicalLocalTransportCoefficients
public import SubdiffusiveProcess.Probability.InfraredCharacterizationExistence

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Homogenization Set
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess
open scoped BigOperators
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalLocalTransport

variable {d : ℕ} [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)]

/-- The existing, constructed infrared field, with its actual bilateral characterization. -/
def infraredField (M : GMCModel d) : BilateralField d → C(Vec d, ℝ) :=
  Classical.choose (exists_infraredCharacterization M.shellPrefix.dimension M)

theorem infraredField_spec (M : GMCModel d) : InfraredCharacterization M (infraredField M) :=
  Classical.choose_spec (exists_infraredCharacterization M.shellPrefix.dimension M)

/-- The top physical density agrees with the existing full infrared cutoff density.
The full event is chosen before the starting point; the equality holds at every point. -/
theorem top_local_identification (M : GMCModel d) (m : ℕ) (z : Vec d) :
    ∀ᵐ eta ∂nativeLaw M, ∀ x : Vec d,
      localSpeed M ⊤ m z (physicalEnvironment M m z eta) x =
        cutoffSpeedDensity M (infraredField M) (bilateralEnvironment eta) m x ∧
      localCoefficient M ⊤ m z (physicalEnvironment M m z eta) x =
        cutoffCoefficient M (infraredField M) (bilateralEnvironment eta) m x := by
  have hH := (bilateralEnvironment_preserving M).quasiMeasurePreserving.ae
    (infraredField_spec M).2
  filter_upwards [physicalEnvironment_local M m z, hH] with eta hlocal hlim
  let omega := physicalEnvironment M m z eta
  let xi := bilateralEnvironment eta
  have hz (k : ℕ) : omega.val k z = xi ((k : ℤ) - m) 0 := by
    simpa only [smul_zero, add_zero] using hlocal k 0
  have hp (y : Vec d) : Tendsto (fun n => anchoredPartialSum omega.val n y)
      atTop (nhds (anchoredLog omega y)) :=
    ((anchoredLog_spec omega).value_tendsto {y} isCompact_singleton).tendsto_at rfl
  intro x
  have hxlocal (k : ℕ) : omega.val k (z + (3 : ℝ) ^ m • x) =
      xi ((k : ℤ) - m) x := hlocal k x
  have hindex (k : ℕ) : (k : ℤ) - m = -(m : ℤ) + k := by omega
  let F : ℝ := ∑ j ∈ Finset.range (m + 1), xi (-(j : ℤ)) x -
    (m + 1 : ℝ) * tauSq M.P
  let B : ℝ := ∑ k ∈ Finset.range (m + 1), (omega.val k z - tauSq M.P)
  have hnat : Tendsto (fun n : ℕ => m + n) atTop atTop :=
    tendsto_atTop_mono (fun n : ℕ => Nat.le_add_left n m) tendsto_id
  have hphys := ((hp (z + (3 : ℝ) ^ m • x)).comp hnat).sub ((hp z).comp hnat)
  have hphys' := hphys.add_const B
  have hbil := ((continuous_eval_const x).tendsto _).comp hlim
  have hbil' := hbil.add_const F
  have hid : (fun n => anchoredPartialSum omega.val (m + n) (z + (3 : ℝ) ^ m • x) -
      anchoredPartialSum omega.val (m + n) z + B) =
      (fun n => infraredPartialSum xi n x + F) := by
    funext n
    have hh := finiteLocalPotential_eq M (l := m + n) (m := m) (by omega) xi x
    simp only [Nat.add_sub_cancel_left] at hh
    have hh' : finiteLocalPotential M (m + n) m xi x =
        infraredPartialSum xi n x + F := by rw [hh]; dsimp [F]; ring
    rw [← hh']
    unfold anchoredPartialSum finiteLocalPotential B
    simp only [min_eq_left (show m ≤ m + n by omega), hxlocal, hz, hindex,
      Finset.sum_sub_distrib]
    ring
  change Tendsto (fun n => anchoredPartialSum omega.val (m + n)
    (z + (3 : ℝ) ^ m • x) - anchoredPartialSum omega.val (m + n) z + B)
    atTop (nhds _) at hphys'
  rw [hid] at hphys'
  have hlog := tendsto_nhds_unique hphys' hbil'
  have hs : localSpeed M ⊤ m z omega x = cutoffSpeedDensity M (infraredField M) xi m x := by
    rw [localSpeed_exp]
    simp only [activeScale, WithTop.untopD_top, min_self]
    rw [physicalPotential_finite_apply]
    change Real.exp (anchoredLog omega (z + (3 : ℝ) ^ m • x) - anchoredLog omega z + B) = _
    rw [hlog]
    unfold cutoffSpeedDensity cutoffPotential F
    simp only [Int.ofNat_eq_natCast]
    congr 1
    ring
  refine ⟨hs, ?_⟩
  simp only [localCoefficient, activeScale, WithTop.untopD_top, min_self,
    cutoffCoefficient]
  change (ahom M m)⁻¹ * localSpeed M ⊤ m z omega x =
    (ahom M m)⁻¹ * cutoffSpeedDensity M (infraredField M) xi m x
  rw [hs]

/-- Finite `m≤l` is the full bilateral density times its actual infrared-tail correction. -/
theorem finite_multiplier_identification (M : GMCModel d) {l m : ℕ} (hml : m ≤ l)
    (xi : BilateralField d) (x : Vec d) :
    finiteLocalSpeed M l m xi x =
      Real.exp (infraredPartialSum xi (l - m) x - infraredField M xi x) *
        cutoffSpeedDensity M (infraredField M) xi m x ∧
    finiteLocalCoefficient M l m xi x =
      Real.exp (infraredPartialSum xi (l - m) x - infraredField M xi x) *
        cutoffCoefficient M (infraredField M) xi m x := by
  have hs : finiteLocalSpeed M l m xi x =
      Real.exp (infraredPartialSum xi (l - m) x - infraredField M xi x) *
        cutoffSpeedDensity M (infraredField M) xi m x := by
    unfold finiteLocalSpeed cutoffSpeedDensity cutoffPotential
    rw [finiteLocalPotential_eq M hml, ← Real.exp_add]
    simp only [Int.ofNat_eq_natCast]
    congr 1
    ring
  exact ⟨hs, by simp only [finiteLocalCoefficient, min_eq_left hml, hs,
    cutoffCoefficient, cutoffSpeedDensity]; ring⟩

end SubdiffusiveProcess.Section10.PhysicalLocalTransport
