module

public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.EllipticRegularity.CubeDilation
public import SubdiffusiveProcess.Analysis.HolderDilationToolkit
public import SubdiffusiveProcess.Paper.aux_coercivity_dilation_killed_pullback
public import SubdiffusiveProcess.Paper.inputs_classical_e4_extension
public import SubdiffusiveProcess.Paper.classical_unit_cube_fractional_zero_extension

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- E4: the zero-trace fractional zero-extension theorem.  Follows from the unit-cube leaf
`classical_unit_cube_fractional_zero_extension` (statement unchanged): zero-extend the killed pull-back to the unit
cube and push the extension forward along the dilation (which preserves the closed cube and does not increase the
global Gagliardo norm for `r ≤ 1`, `d ≥ 2s`). -/
theorem inputs_classical_e4_zero_extension (d : ℕ) (hd : 2 ≤ d)
    (s : Set.Ioo (0 : ℝ) 1) (hs : (1 / 2 : ℝ) < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ v : killedSobolevGraph (centeredCube z r hr),
        ∃ V : SpatialCoordinates d → ℝ,
          (((v : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] V) ∧
          (∀ x, x ∉ (closedCube z r hr : Set (SpatialCoordinates d)) → V x = 0) ∧
          globalFractionalSqNorm s V ≤ ENNReal.ofReal
            (C * cubeFractionalSqNorm hd z r hr s (v : SobolevData (centeredCube z r hr)).1) := by
  obtain ⟨C, hC, hext⟩ := classical_unit_cube_fractional_zero_extension d hd s hs
  refine ⟨C, hC, ?_⟩
  intro z r hr hr1 v
  obtain ⟨w, hwae, -⟩ := aux_coercivity_dilation_killed_pullback d z r hr one_pos v
  obtain ⟨V', hV'ae, hV'zero, hV'⟩ := hext w
  set vv : DomainL2 (centeredCube z r hr) := (v : SobolevData (centeredCube z r hr)).1 with hvv
  set ww : DomainL2 (centeredCube (0 : SpatialCoordinates d) 1 one_pos) :=
    (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1 with hww
  have hpull : ∀ᵐ x ∂(volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))),
      (ww : SpatialCoordinates d → ℝ) x = (vv : SpatialCoordinates d → ℝ) (cubeDilation z (0 : SpatialCoordinates d) r x) :=
    hwae
  have hwp : ww = aux_inputs_classical_e4_interpolation_pull z hr vv :=
    Lp.ext (by
      filter_upwards [hpull, aux_inputs_classical_e4_interpolation_pull_ae z hr vv] with x h1 h2
      rw [h1, h2])
  refine ⟨fun x => V' (cubeDilation (0 : SpatialCoordinates d) z r⁻¹ x), ?_, ?_, ?_⟩
  · -- a.e. equality on the cube of side `r`
    have hkey : ∀ᵐ x' ∂(volume.restrict
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))),
        (vv : SpatialCoordinates d → ℝ) (cubeDilation z (0 : SpatialCoordinates d) r x') = V' x' := by
      filter_upwards [hpull, hV'ae] with x' h1 h2
      rw [← h1, h2]
    have hcoe : ⇑(cubeDilationEquiv z (0 : SpatialCoordinates d) hr.ne') = cubeDilation z 0 r := rfl
    set N : Set (SpatialCoordinates d) := {x | ¬ ((vv : SpatialCoordinates d → ℝ) x =
      V' (cubeDilation (0 : SpatialCoordinates d) z r⁻¹ x))} with hN
    have hnull : (Measure.map (cubeDilation z (0 : SpatialCoordinates d) r) (volume.restrict
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))) N = 0 := by
      rw [← hcoe, MeasurableEquiv.map_apply]
      refine measure_mono_null ?_ (ae_iff.1 hkey)
      intro x' hx'
      simp only [Set.mem_preimage, hN, Set.mem_ofPred_eq] at hx' ⊢
      intro h
      apply hx'
      rw [hcoe]
      have hinv : cubeDilation (0 : SpatialCoordinates d) z r⁻¹ (cubeDilation z (0 : SpatialCoordinates d) r x') = x' := by
        have := MeasurableEquiv.symm_apply_apply (cubeDilationEquiv z (0 : SpatialCoordinates d) hr.ne') x'
        exact this
      rw [hinv]; exact h
    rw [map_cubeDilation_restrict z 0 hr one_pos, Measure.smul_apply, smul_eq_mul, mul_eq_zero] at hnull
    rcases hnull with h0 | h0
    · exfalso
      rw [ENNReal.ofReal_eq_zero] at h0
      have : 0 < |(r ^ d)⁻¹| := abs_pos.2 (inv_ne_zero (pow_ne_zero _ hr.ne'))
      linarith
    · exact ae_iff.2 h0
  · -- vanishing off the closed cube of side `r`
    intro x hx
    apply hV'zero
    intro hmem
    apply hx
    have hinv : cubeDilation z (0 : SpatialCoordinates d) r (cubeDilation (0 : SpatialCoordinates d) z r⁻¹ x) = x := by
      have := MeasurableEquiv.apply_symm_apply (cubeDilationEquiv z (0 : SpatialCoordinates d) hr.ne') x
      exact this
    have := (aux_hDet_mem_closedCube_dilation z r hr (cubeDilation (0 : SpatialCoordinates d) z r⁻¹ x)).1 hmem
    rwa [hinv] at this
  · obtain ⟨hfs, hSs, hAs⟩ := aux_inputs_classical_e4_interpolation_scale hd z hr s vv
    rw [← hwp] at hSs hAs
    calc globalFractionalSqNorm (s : ℝ) (fun x => V' (cubeDilation (0 : SpatialCoordinates d) z r⁻¹ x))
        ≤ globalFractionalSqNorm (s : ℝ) V' :=
          aux_inputs_classical_e4_extension_global_le hd s z hr hr1 V'
      _ ≤ ENNReal.ofReal (C * cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos s ww) := hV'
      _ ≤ ENNReal.ofReal (C * cubeFractionalSqNorm hd z r hr s vv) := by
          apply ENNReal.ofReal_le_ofReal
          apply mul_le_mul_of_nonneg_left _ hC.le
          rw [aux_inputs_classical_e4_extension_sqnorm hd z hr s vv,
            aux_inputs_classical_e4_extension_sqnorm hd (0 : SpatialCoordinates d) one_pos s ww, ← hAs, hSs]
          have hs0 := s.2.1
          have hrs : 1 ≤ r ^ (-(s : ℝ)) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 (by linarith)
          have hb0 : 0 ≤ (cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos s
              (fun _ : Fin 1 => ww)).toReal := ENNReal.toReal_nonneg
          have : (cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos s (fun _ : Fin 1 => ww)).toReal ≤
              r ^ (-(s : ℝ)) * (cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos s
                (fun _ : Fin 1 => ww)).toReal := by nlinarith
          nlinarith [this, sq_nonneg (‖vv‖ / Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))))]

end SubdiffusiveProcess.Paper
