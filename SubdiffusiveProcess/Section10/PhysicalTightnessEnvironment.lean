module

public import SubdiffusiveProcess.Section10.PhysicalLocalTransportInfrared

@[expose] public section

/-!
# Actual common-scale/local coefficients at arbitrary physical scale

The existing native coupling is used at base cutoff `N`. For every local scale
`m` and every rescaled centre `y`, the physical centre is `3^N y` and the local
spatial dilation is `3^(m-N)`. The two genuine branches are finite `L=N` with
`Hf=0`, and top with the characterized full infrared field. A common positive
spatial scalar appears in both speed and coefficient and cancels from the
generator. No caller coefficient/law equality is assumed by these exports.
-/

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalTightness
open PhysicalLocalTransport

variable {d : ℕ} [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)]

/-- The actual infrared characterization is unique as a continuous field,
on a full event chosen before the spatial point. -/
theorem infrared_eq_constructed (M : GMCModel d)
    (H : BilateralField d → C(Vec d, ℝ)) (hH : InfraredCharacterization M H) :
    ∀ᵐ xi ∂(chaosSampleLaw M).toMeasure, H xi = infraredField M xi := by
  filter_upwards [hH.2, (infraredField_spec M).2] with xi hxi hcanonical
  exact tendsto_nhds_unique hxi hcanonical

/-- The finite branch at the base cutoff is exactly the stationary common-scale
speed, with no infrared term. -/
theorem finite_base_speed (M : GMCModel d) (N : ℕ) (xi : BilateralField d) (x : Vec d) :
    finiteLocalSpeed M N N xi x = cutoffSpeedDensity M (fun _ => 0) xi N x := by
  unfold finiteLocalSpeed
  rw [finiteLocalPotential_eq M (Nat.le_refl N)]
  simp [infraredPartialSum, cutoffSpeedDensity, cutoffPotential]

omit [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)] in
private theorem physical_spatial_identity {d : ℕ} [_ms : MeasurableSpace C(Vec d, ℝ)] [_borel : BorelSpace C(Vec d, ℝ)]
    (N m : ℕ) (y x : Vec d) :
    (3 : ℝ) ^ N • (y + (3 : ℝ) ^ ((m : ℤ) - (N : ℤ)) • x) =
      (3 : ℝ) ^ N • y + (3 : ℝ) ^ m • x := by
  rw [smul_add, smul_smul]
  congr 1
  rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast, zpow_natCast]
  field_simp

/-- The common positive scalar at the local physical centre. -/
def commonLocalFactor (M : GMCModel d) (L : WithTop ℕ) (N m : ℕ)
    (y : Vec d) (omega : AnchoredC11Sample d) : ℝ :=
  localFactor M L m ((3 : ℝ) ^ N • y) omega / localFactor M L N 0 omega

omit [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)] in
theorem commonLocalFactor_pos {d : ℕ} [_ms : MeasurableSpace C(Vec d, ℝ)] [_borel : BorelSpace C(Vec d, ℝ)]
    (M : GMCModel d) (L : WithTop ℕ) (N m : ℕ)
    (y : Vec d) (omega : AnchoredC11Sample d) : 0 < commonLocalFactor M L N m y omega :=
  div_pos (localFactor_pos M L m _ omega) (localFactor_pos M L N 0 omega)

private theorem local_speed_dilation (M : GMCModel d) (L : WithTop ℕ) (N m : ℕ)
    (y : Vec d) (omega : AnchoredC11Sample d) (x : Vec d) :
    localSpeed M L N 0 omega (y + (3 : ℝ) ^ ((m : ℤ) - (N : ℤ)) • x) =
      commonLocalFactor M L N m y omega *
        localSpeed M L m ((3 : ℝ) ^ N • y) omega x := by
  unfold localSpeed commonLocalFactor
  rw [zero_add, physical_spatial_identity]
  field_simp [(localFactor_pos M L m ((3 : ℝ) ^ N • y) omega).ne',
    (localFactor_pos M L N 0 omega).ne']

private theorem local_coefficient_dilation (M : GMCModel d) (L : WithTop ℕ) (N m : ℕ)
    (y : Vec d) (omega : AnchoredC11Sample d) (hactive : activeScale L N = N)
    (x : Vec d) :
    localCoefficient M L N 0 omega (y + (3 : ℝ) ^ ((m : ℤ) - (N : ℤ)) • x) =
      (commonLocalFactor M L N m y omega * ahom M (activeScale L m) / ahom M N) *
        localCoefficient M L m ((3 : ℝ) ^ N • y) omega x := by
  unfold localCoefficient
  rw [hactive, local_speed_dilation]
  field_simp [(ahom_pos M N).ne', (ahom_pos M (activeScale L m)).ne']

/-- Finite-cutoff coefficients at every local scale, including `m>N` with active
cutoff `N`. The same native sample supplies the literal anchored and bilateral laws. -/
theorem finite_common_local_dilation (M : GMCModel d) (N : ℕ) :
    ∀ᵐ eta ∂nativeLaw M, ∀ (m : ℕ) (y x : Vec d),
      let omega := physicalEnvironment M N 0 eta
      let xi := bilateralEnvironment eta
      let c := commonLocalFactor M (N : WithTop ℕ) N m y omega
      cutoffSpeedDensity M (fun _ => 0) xi N
          (y + (3 : ℝ) ^ ((m : ℤ) - (N : ℤ)) • x) =
        c * localSpeed M (N : WithTop ℕ) m ((3 : ℝ) ^ N • y) omega x ∧
      cutoffCoefficient M (fun _ => 0) xi N
          (y + (3 : ℝ) ^ ((m : ℤ) - (N : ℤ)) • x) =
        (c * ahom M (min m N) / ahom M N) *
          localCoefficient M (N : WithTop ℕ) m ((3 : ℝ) ^ N • y) omega x := by
  filter_upwards [finite_local_identification M N N 0] with eta hglobal
  intro m y x
  dsimp only
  have hs := local_speed_dilation M (N : WithTop ℕ) N m y (physicalEnvironment M N 0 eta) x
  rw [(hglobal _).1, finite_base_speed] at hs
  have hc := local_coefficient_dilation M (N : WithTop ℕ) N m y
    (physicalEnvironment M N 0 eta) (by rw [activeScale_coe, min_self]) x
  rw [(hglobal _).2] at hc
  have hcbase : ∀ q : Vec d, finiteLocalCoefficient M N N (bilateralEnvironment eta) q =
      cutoffCoefficient M (fun _ => 0) (bilateralEnvironment eta) N q := by
    intro q
    simp only [finiteLocalCoefficient, min_self, finite_base_speed]
    rfl
  rw [hcbase, activeScale_coe] at hc
  exact ⟨hs, hc⟩

/-- Top retains the actual full infrared field. Its local active cutoff is `m`
even when `m>N`; no truncation or cutoff-zero replacement is used. -/
theorem top_common_local_dilation (M : GMCModel d)
    (H : BilateralField d → C(Vec d, ℝ)) (hH : InfraredCharacterization M H) (N : ℕ) :
    ∀ᵐ eta ∂nativeLaw M, ∀ (m : ℕ) (y x : Vec d),
      let omega := physicalEnvironment M N 0 eta
      let xi := bilateralEnvironment eta
      let c := commonLocalFactor M ⊤ N m y omega
      cutoffSpeedDensity M H xi N (y + (3 : ℝ) ^ ((m : ℤ) - (N : ℤ)) • x) =
        c * localSpeed M ⊤ m ((3 : ℝ) ^ N • y) omega x ∧
      cutoffCoefficient M H xi N (y + (3 : ℝ) ^ ((m : ℤ) - (N : ℤ)) • x) =
        (c * ahom M m / ahom M N) *
          localCoefficient M ⊤ m ((3 : ℝ) ^ N • y) omega x := by
  have hHeq := (bilateralEnvironment_preserving M).quasiMeasurePreserving.ae
    (infrared_eq_constructed M H hH)
  filter_upwards [top_local_identification M N 0, hHeq] with eta hglobal hHeta
  intro m y x
  dsimp only
  have hs := local_speed_dilation M ⊤ N m y (physicalEnvironment M N 0 eta) x
  rw [(hglobal _).1] at hs
  have hc := local_coefficient_dilation M ⊤ N m y (physicalEnvironment M N 0 eta)
    (by simp [activeScale]) x
  rw [(hglobal _).2] at hc
  simp only [activeScale, WithTop.untopD_top, min_self] at hc
  simpa only [cutoffSpeedDensity, cutoffCoefficient, cutoffPotential, hHeta]
    using And.intro hs hc

end SubdiffusiveProcess.Section10.PhysicalTightness
