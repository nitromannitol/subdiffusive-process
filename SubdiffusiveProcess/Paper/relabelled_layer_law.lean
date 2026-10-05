module

public import SubdiffusiveProcess.Paper.in_common_scale_coupling
public import SubdiffusiveProcess.Main.CommonScaleLaw
public import SubdiffusiveProcess.Main.BilateralField

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory SubdiffusiveProcess

namespace SubdiffusiveProcess.Paper

private theorem aux_shifted_infinitePi_map
    {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (laws : ℤ → Measure X) [∀ j, IsProbabilityMeasure (laws j)]
    (f : X → Y) (hf : Measurable f) (N : Nat) :
    Measure.map (fun omega : ℤ → X => fun i : Nat =>
      f (omega ((i : ℤ) - (N : ℤ)))) (Measure.infinitePi laws) =
      Measure.infinitePi (fun i : Nat =>
        Measure.map f (laws ((i : ℤ) - (N : ℤ)))) := by
  classical
  let shift : Nat → ℤ := fun i => (i : ℤ) - (N : ℤ)
  let S : Set ℤ := Set.range shift
  let e : Nat ≃ S :=
    Equiv.ofBijective (fun i => ⟨shift i, ⟨i, rfl⟩⟩) (by
      constructor
      · intro i j hij
        have hshift : shift i = shift j := congrArg Subtype.val hij
        dsimp [shift] at hshift
        omega
      · rintro ⟨j, ⟨i, rfl⟩⟩
        exact ⟨i, rfl⟩)
  let R : (ℤ → X) → (j : S) → X := S.domRestrict
  let E : ((j : S) → X) → (Nat → X) := fun z i => z (e i)
  let T : (Nat → X) → (Nat → Y) := fun z i => f (z i)
  have hR : Measurable R := by
    exact measurable_pi_iff.mpr fun j => measurable_pi_apply j.1
  have hE : Measurable E := by
    exact Measurable.of_eval fun i => measurable_pi_apply (e i)
  have hT : Measurable T := by
    exact Measurable.of_eval fun i => hf.comp (measurable_pi_apply i)
  have hrestrict :
      Measure.map R (Measure.infinitePi laws) =
        Measure.infinitePi (fun j : S => laws j) := by
    simpa only [R] using
      (Measure.infinitePi_map_restrict' (μ := laws) (I := S))
  have hreindex :
      Measure.map E (Measure.infinitePi (fun j : S => laws j)) =
        Measure.infinitePi (fun i : Nat => laws (shift i)) := by
    have h := Measure.infinitePi_map_piCongrLeft
      (μ := fun i : Nat => laws (shift i)) e.symm
    have hEfun :
        (MeasurableEquiv.piCongrLeft (fun _ : Nat => X) e.symm :
          (S → X) → (Nat → X)) = E := by
      funext z i
      simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply, E]
    have hlaws : (fun j : S => laws j) =
        (fun j : S => laws (shift (e.symm j))) := by
      funext j
      congr 1
      exact (congrArg Subtype.val (e.apply_symm_apply j)).symm
    rw [← hEfun]
    rw [hlaws]
    exact h
  have hscale :
      Measure.map T (Measure.infinitePi (fun i : Nat => laws (shift i))) =
        Measure.infinitePi (fun i : Nat => Measure.map f (laws (shift i))) := by
    rw [Measure.infinitePi_map_pi
      (μ := fun i : Nat => laws (shift i))
      (f := fun _ : Nat => f) (fun _ => hf)]
  have hcomp :
      (fun omega : ℤ → X => fun i : Nat => f (omega (shift i))) =
        T ∘ E ∘ R := by
    funext omega i
    rfl
  change Measure.map (fun omega : ℤ → X => fun i : Nat =>
      f (omega (shift i))) (Measure.infinitePi laws) = _
  calc
    Measure.map (fun omega : ℤ → X => fun i : Nat => f (omega (shift i)))
        (Measure.infinitePi laws) =
        Measure.map (T ∘ E ∘ R) (Measure.infinitePi laws) := by rw [hcomp]
    _ = Measure.map T (Measure.map E (Measure.map R (Measure.infinitePi laws))) := by
      calc
        Measure.map (T ∘ E ∘ R) (Measure.infinitePi laws) =
            Measure.map (T ∘ E) (Measure.map R (Measure.infinitePi laws)) :=
          (Measure.map_map (hT.comp hE) hR).symm
        _ = Measure.map T (Measure.map E (Measure.map R (Measure.infinitePi laws))) :=
          (Measure.map_map hT hE).symm
    _ = Measure.infinitePi (fun i : Nat => Measure.map f (laws (shift i))) := by
      rw [hrestrict, hreindex, hscale]

/--
- in_common_scale_coupling supplies the independent bilateral product law.
- hg pins each relabelled layer to g_(i-N)(3^(-N) y) from the same original realization.
- The conclusion is equality of the entire nonnegative-index family laws, not merely equality of one-point marginals.
- The relabelling is performed at one fixed N at a time; no cutoff-dependent layer mixing is asserted.
-/
theorem relabelled_layer_law
    (d : Nat)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (nu : ProbabilityMeasure C(SpatialCoordinates d, ℝ))
    (g : Nat → BilateralField d → Nat → C(SpatialCoordinates d, ℝ))
    (hg : ∀ N omega i y,
      g N omega i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y)) :
    ∀ N : Nat,
      Measure.map (g N) (commonScaleLaw d nu).toMeasure =
      Measure.map (fun omega : BilateralField d => fun i : Nat => omega (i : ℤ))
          (commonScaleLaw d nu).toMeasure := by
  intro N
  have hpoint : g N = (fun omega : BilateralField d => fun i : Nat =>
      SubdiffusiveProcess.layerScaling d (N : ℤ)
        (omega ((i : ℤ) - (N : ℤ)))) := by
    funext omega i
    apply ContinuousMap.ext
    intro y
    exact hg N omega i y
  have hmap := aux_shifted_infinitePi_map
    (laws := fun j : ℤ =>
      (SubdiffusiveProcess.scaledLayerLaw d nu j : Measure _))
    (f := SubdiffusiveProcess.layerScaling d (N : ℤ))
    (SubdiffusiveProcess.layerScaling d (N : ℤ)).continuous.measurable N
  have hscaled : ∀ i : Nat,
      Measure.map (SubdiffusiveProcess.layerScaling d (N : ℤ))
          ((SubdiffusiveProcess.scaledLayerLaw d nu
          ((i : ℤ) - (N : ℤ))).toMeasure) =
        (SubdiffusiveProcess.scaledLayerLaw d nu (i : ℤ)).toMeasure := by
    intro i
    have hcomp_scale :
        SubdiffusiveProcess.layerScaling d (N : ℤ) ∘
            SubdiffusiveProcess.layerScaling d ((i : ℤ) - (N : ℤ)) =
          SubdiffusiveProcess.layerScaling d (i : ℤ) := by
      funext f
      apply ContinuousMap.ext
      intro y
      simp only [SubdiffusiveProcess.layerScaling,
        ContinuousMap.compRightContinuousMap_apply, ContinuousMap.comp_apply,
        Function.comp_apply, ContinuousMap.coe_mk]
      rw [smul_smul]
      congr 2
      rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      congr 1
      omega
    change Measure.map (SubdiffusiveProcess.layerScaling d (N : ℤ))
          (Measure.map (SubdiffusiveProcess.layerScaling d
            ((i : ℤ) - (N : ℤ))) nu.toMeasure) =
        Measure.map (SubdiffusiveProcess.layerScaling d (i : ℤ)) nu.toMeasure
    calc
      Measure.map (SubdiffusiveProcess.layerScaling d (N : ℤ))
            (Measure.map (SubdiffusiveProcess.layerScaling d
              ((i : ℤ) - (N : ℤ))) nu.toMeasure) =
          Measure.map
            (SubdiffusiveProcess.layerScaling d (N : ℤ) ∘
              SubdiffusiveProcess.layerScaling d ((i : ℤ) - (N : ℤ)))
            nu.toMeasure :=
        Measure.map_map
          (SubdiffusiveProcess.layerScaling d (N : ℤ)).continuous.measurable
          (SubdiffusiveProcess.layerScaling d ((i : ℤ) - (N : ℤ))).continuous.measurable
      _ = Measure.map (SubdiffusiveProcess.layerScaling d (i : ℤ)) nu.toMeasure := by
        rw [hcomp_scale]
  have hrel :
      Measure.map
          (fun omega : BilateralField d => fun i : Nat =>
            SubdiffusiveProcess.layerScaling d (N : ℤ)
              (omega ((i : ℤ) - (N : ℤ))))
          (commonScaleLaw d nu).toMeasure =
        Measure.infinitePi (fun i : Nat =>
          Measure.map (SubdiffusiveProcess.layerScaling d (N : ℤ))
            (SubdiffusiveProcess.scaledLayerLaw d nu
              ((i : ℤ) - (N : ℤ))).toMeasure) := by
    simpa only [SubdiffusiveProcess.commonScaleLaw] using! hmap
  have hrel' :
      Measure.map
          (fun omega : BilateralField d => fun i : Nat =>
            SubdiffusiveProcess.layerScaling d (N : ℤ)
              (omega ((i : ℤ) - (N : ℤ))))
          (commonScaleLaw d nu).toMeasure =
        Measure.infinitePi (fun i : Nat =>
          (SubdiffusiveProcess.scaledLayerLaw d nu (i : ℤ)).toMeasure) := by
    rw [hrel]
    congr 1
    funext i
    exact hscaled i
  have hpositive :
      Measure.map (fun omega : BilateralField d => fun i : Nat => omega (i : ℤ))
          (commonScaleLaw d nu).toMeasure =
        Measure.infinitePi (fun i : Nat =>
          (SubdiffusiveProcess.scaledLayerLaw d nu (i : ℤ)).toMeasure) := by
    change Measure.map (fun omega : ℤ → C(SpatialCoordinates d, ℝ) =>
        fun i : Nat => omega (i : ℤ))
        (Measure.infinitePi (fun j : ℤ =>
          (SubdiffusiveProcess.scaledLayerLaw d nu j : Measure _))) = _
    simpa only [sub_zero, Measure.map_id'] using!
      (aux_shifted_infinitePi_map
        (laws := fun j : ℤ =>
          (SubdiffusiveProcess.scaledLayerLaw d nu j : Measure _))
        (f := fun x : C(SpatialCoordinates d, ℝ) => x) measurable_id 0)
  calc
    Measure.map (g N) (commonScaleLaw d nu).toMeasure =
        Measure.map
          (fun omega : BilateralField d => fun i : Nat =>
            SubdiffusiveProcess.layerScaling d (N : ℤ)
              (omega ((i : ℤ) - (N : ℤ))))
          (commonScaleLaw d nu).toMeasure := by rw [hpoint]
    _ = Measure.infinitePi (fun i : Nat =>
          (SubdiffusiveProcess.scaledLayerLaw d nu (i : ℤ)).toMeasure) := hrel'
    _ = Measure.map (fun omega : BilateralField d => fun i : Nat => omega (i : ℤ))
          (commonScaleLaw d nu).toMeasure := hpositive.symm

end SubdiffusiveProcess.Paper
