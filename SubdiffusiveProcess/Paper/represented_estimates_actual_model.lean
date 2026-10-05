module

public import SubdiffusiveProcess.Paper.conv_represented_thm_c1_family_grids_actual_root
public import SubdiffusiveProcess.Paper.inputs_simultaneous
public import SubdiffusiveProcess.Paper.inputs_responses_witness
public import SubdiffusiveProcess.Paper.inputs_regularity_witness
public import SubdiffusiveProcess.Paper.inputs_iteration_witness
public import SubdiffusiveProcess.Paper.inputs_poincare_witness
public import SubdiffusiveProcess.Paper.inputs_extension_witness
public import SubdiffusiveProcess.Paper.conv_represented_estimates
public import SubdiffusiveProcess.Paper.in_represented_bounds_seq
public import SubdiffusiveProcess.Probability.InfraredCharacterizationExistence

@[expose] public section

open Set Filter MeasureTheory TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped Topology ENNReal NNReal ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Encodable geometric data suffice to construct the entire determining cube catalogue. -/
theorem aux_represented_estimates_actual_model_rooted_catalogue (d : ℕ) :
    ∃ (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i),
      (∀ i, (∀ c : Fin d, ∃ q : ℚ, z i c = (q : ℝ)) ∧
        ∃ k : ℤ, r i = (3 : ℝ) ^ k) ∧
      _root_.SubdiffusiveProcess.Paper.conv_represented_root_family d z r hr := by
  classical
  let Z : ((Fin d → ℚ) × ℤ) → SpatialCoordinates d := fun a c => (a.1 c : ℝ)
  let R : ((Fin d → ℚ) × ℤ) → ℝ := fun a => (3 : ℝ) ^ a.2
  have hR : ∀ a, 0 < R a := fun a => by dsimp [R]; positivity
  let Codes := {a : (Fin d → ℚ) × ℤ //
    (centeredCube (Z a) (R a) (hR a) : Set (SpatialCoordinates d)) ⊆
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))}
  have hzero : Z (0, 0) = 0 := by ext c; simp [Z]
  have hroot : (centeredCube (Z (0, 0)) (R (0, 0)) (hR (0, 0)) :
      Set (SpatialCoordinates d)) ⊆
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) := by
    simpa only [hzero, R, zpow_zero] using (subset_rfl :
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) ⊆ _)
  let root : Codes := ⟨(0, 0), hroot⟩
  have : Nonempty Codes := ⟨root⟩
  obtain ⟨e, he⟩ := exists_surjective_nat Codes
  let z : ℕ → SpatialCoordinates d := fun i => Z (e i).val
  let r : ℕ → ℝ := fun i => R (e i).val
  have hr : ∀ i, 0 < r i := fun i => hR (e i).val
  have hrat : ∀ i, (∀ c : Fin d, ∃ q : ℚ, z i c = (q : ℝ)) ∧
      ∃ k : ℤ, r i = (3 : ℝ) ^ k :=
    fun i => ⟨fun c => ⟨(e i).val.1 c, rfl⟩, (e i).val.2, rfl⟩
  obtain ⟨i0, hi0⟩ := he root
  have hz0 : z i0 = 0 := by simpa only [z, hi0, root] using hzero
  have hside0 : r i0 = 1 := by simp [r, hi0, root, R]
  have hcomplete : ∀ (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0),
      (∀ c : Fin d, ∃ q : ℚ, z0 c = (q : ℝ)) → (∃ k : ℤ, r0 = (3 : ℝ) ^ k) →
      (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) ⊆
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) →
      ∃ i, z i = z0 ∧ r i = r0 := by
    intro z0 r0 hr0 hz hrtri hsub
    choose q hq using hz
    obtain ⟨k, hk⟩ := hrtri
    have hZ : Z (q, k) = z0 := funext fun c => (hq c).symm
    have hR0 : R (q, k) = r0 := hk.symm
    let a : Codes := ⟨(q, k), by simpa only [hZ, hR0] using hsub⟩
    obtain ⟨i, hi⟩ := he a
    exact ⟨i, by simpa only [z, hi, a] using hZ,
      by simpa only [r, hi, a] using hR0⟩
  have hfamily : _root_.SubdiffusiveProcess.Paper.conv_represented_root_family d z r hr := by
    refine ⟨i0, ?_, ?_, ?_⟩
    · simp only [hz0, hside0]; exact subset_rfl
    · intro i
      simpa only [hz0, hside0] using (e i).property
    · intro z0 r0 hr0 hz htri hsub
      apply hcomplete z0 r0 hr0 hz htri
      simpa only [hz0, hside0] using hsub
  exact ⟨z, r, hr, hrat, hfamily⟩

/-- A nonempty class of complete rooted catalogues with genuine killed response spaces. -/
theorem aux_represented_estimates_actual_model_killed_catalogue
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ (Z : ℕ → SpatialCoordinates d) (R : ℕ → ℝ) (hR : ∀ i, 0 < R i)
      (Sspace : ∀ i, ResponseSpace (centeredCube (Z i) (R i) (hR i))),
      (∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (Z i) (R i) (hR i))) ∧
      (∀ i, (∀ c : Fin d, ∃ q : ℚ, Z i c = (q : ℝ)) ∧ ∃ m : ℤ, R i = (3 : ℝ) ^ m) ∧
      conv_represented_root_family d Z R hR := by
  classical
  have : NeZero d := ⟨by omega⟩
  obtain ⟨Z, R, hR, hrat, hroot⟩ :=
    aux_represented_estimates_actual_model_rooted_catalogue d
  have hP : ∀ i, ∃ K : ℝ≥0,
      ∀ u : killedSobolevGraph (centeredCube (Z i) (R i) (hR i)),
        ‖(u : SobolevData (centeredCube (Z i) (R i) (hR i))).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube (Z i) (R i) (hR i))) u‖ :=
    fun i => (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain
      (centeredCube (Z i) (R i) (hR i))
      (lane2_isOpenBoundedConvexDomain_centeredCube (Z i) (hR i))).1
  let Sspace : ∀ i, ResponseSpace (centeredCube (Z i) (R i) (hR i)) :=
    fun i => killedResponseSpace (hP i)
  exact ⟨Z, R, hR, Sspace, (fun _ => rfl), hrat, hroot⟩

/-- Every sufficiently small model supplies the exact represented carriers for any chart,
actual infrared characterization, rooted cube catalogue and increasing cutoff pair.
The geometric and infrared inputs are themselves witnessed in the conclusion. -/
theorem represented_estimates_actual_model
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (alpha eta beta t : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (heta : 0 < eta) (hAeta : 1 + eta < 2 * alpha)
    (hb : 1 / 2 < beta) (hba : beta < alpha) :
    Nonempty (in_J d) ∧
    (∃ (Z : ℕ → SpatialCoordinates d) (R : ℕ → ℝ) (hR : ∀ i, 0 < R i)
      (Sspace : ∀ i, ResponseSpace (centeredCube (Z i) (R i) (hR i))),
      (∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (Z i) (R i) (hR i))) ∧
      (∀ i, (∀ c : Fin d, ∃ q : ℚ, Z i c = (q : ℝ)) ∧ ∃ m : ℤ, R i = (3 : ℝ) ^ m) ∧
      conv_represented_root_family d Z R hR) ∧
    ∀ E : in_J d,
      ∃ δ0 : ℝ, 0 < δ0 ∧
        ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ δ0 →
          (∃ H : BilateralField d → C(SpatialCoordinates d, ℝ),
            InfraredCharacterization M H) ∧
          ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
            InfraredCharacterization M H →
          ∀ (Z : ℕ → SpatialCoordinates d) (R : ℕ → ℝ) (hR : ∀ i, 0 < R i)
            (Sspace : ∀ i, ResponseSpace (centeredCube (Z i) (R i) (hR i))),
            (∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (Z i) (R i) (hR i))) →
            (∀ i, (∀ c : Fin d, ∃ q : ℚ, Z i c = (q : ℝ)) ∧ ∃ m : ℤ, R i = (3 : ℝ) ^ m) →
            conv_represented_root_family d Z R hR →
          ∀ (NE NF : ℕ → ℕ), StrictMono NE → StrictMono NF →
      ∃ seq : ℕ → ℕ, StrictMono seq ∧
        ∃ (Ωh : Type) (_ : MeasurableSpace Ωh) (Ph : Measure Ωh) (_ : IsProbabilityMeasure Ph)
          (field : Ωh → BilateralField d) (env : ℕ → Ωh → BilateralField d)
          (GNE GNF : (i : ℕ) → ℕ → Ωh →
            DomainL2 (centeredCube (Z i) (R i) (hR i)) →L[ℝ]
              DomainL2 (centeredCube (Z i) (R i) (hR i)))
          (GE GF : (i : ℕ) → Ωh →
            DomainL2 (centeredCube (Z i) (R i) (hR i)) →L[ℝ]
              DomainL2 (centeredCube (Z i) (R i) (hR i))),
          conv_represented_joint_grids d hd M H Ωh Ph field env env Z R hR Sspace
            GNE GNF GE GF (fun n => NE (seq n)) (fun n => NF (seq n)) alpha eta E beta t ∧
          aux_conv_represented_env_interface_bounds d hd M H Ωh Ph env env Z R hR Sspace GE GF
            (fun n => NE (seq n)) (fun n => NF (seq n)) := by
  classical
  obtain ⟨E0, _, _, Sob, W, Cp, _, _, _, _, hInterp, _, _, _, _, _, _⟩ :=
    inputs_simultaneous d hd
  refine ⟨⟨E0⟩, aux_represented_estimates_actual_model_killed_catalogue d hd, ?_⟩
  intro E
  let Pin : in_poincare d hd E := Classical.choice (inputs_poincare_witness d hd E)
  let X : in_extension d hd E := Classical.choice (inputs_extension_witness d hd E)
  obtain ⟨δrepresented, hδrepresented, hrepresented⟩ :=
    conv_represented_thm_c1_family_grids_actual_root d hd hInterp E Pin X W Cp Sob
      alpha eta beta t ht htd ha0 ha1 heta hAeta hb hba
  obtain ⟨Cresp, δinput, _, hδinput, hresponses⟩ := inputs_responses_witness d hd 1 le_rfl
  refine ⟨min δinput δrepresented, lt_min hδinput hδrepresented, ?_⟩
  intro M hM
  obtain ⟨Rm, _, _⟩ := hresponses M (hM.trans (min_le_left _ _))
  refine ⟨exists_infraredCharacterization hd M, ?_⟩
  intro H hH Z R hR Sspace hS hrat hroot NE NF hNE hNF
  obtain ⟨seq, hseq, Ωh, mΩh, Ph, hPh, field, env, GNE, GNF, GE, GF,
      hjoint, hbounds, _⟩ :=
    hrepresented M Rm (inputs_regularity_witness d M) (inputs_iteration_witness d hd M E)
      H hH (hM.trans (min_le_right _ _)) Z R hR Sspace hS hrat hroot NE NF hNE hNF
  exact ⟨seq, hseq, Ωh, mΩh, Ph, hPh, field, env, GNE, GNF, GE, GF,
    hjoint, hbounds⟩

end SubdiffusiveProcess.Paper
