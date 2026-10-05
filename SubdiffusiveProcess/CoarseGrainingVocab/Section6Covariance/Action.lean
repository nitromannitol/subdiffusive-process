module

public import SubdiffusiveProcess.CoarseGrainingVocab.AnnealedProviders
public import SubdiffusiveProcess.CoarseGrainingVocab.Section45Support



@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance

open MeasureTheory Homogenization

noncomputable section

variable {d : ℕ}

/-! ### The action on a single potential layer -/

/-- Translating a potential layer by `0` does nothing. -/
theorem potentialField_translate_zero
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) :
    _root_.SubdiffusiveProcess.Model.PotentialField.translate (0 : Vec d) g = g := by
  refine _root_.SubdiffusiveProcess.Model.PotentialField.ext fun x => ?_
  rw [_root_.SubdiffusiveProcess.Model.PotentialField.translate_apply, add_zero]

/-- Translating a potential layer by `z` and then by `w` translates it by
`z + w`. -/
theorem potentialField_translate_translate (z w : Vec d)
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) :
    _root_.SubdiffusiveProcess.Model.PotentialField.translate w
        (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g) =
      _root_.SubdiffusiveProcess.Model.PotentialField.translate (z + w) g := by
  refine _root_.SubdiffusiveProcess.Model.PotentialField.ext fun x => ?_
  rw [_root_.SubdiffusiveProcess.Model.PotentialField.translate_apply,
    _root_.SubdiffusiveProcess.Model.PotentialField.translate_apply,
    _root_.SubdiffusiveProcess.Model.PotentialField.translate_apply, add_assoc,
    add_comm w z]

/-- The stored derivative of a translated layer is the derivative at the
translated point. -/
theorem potentialField_deriv_translate (z : Vec d)
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) (x : Vec d) :
    _root_.SubdiffusiveProcess.Model.PotentialField.deriv
        (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g) x =
      _root_.SubdiffusiveProcess.Model.PotentialField.deriv g (x + z) :=
  rfl

/-! ### The action on samples -/

/-- `translatePotentialSample` and `translatePotentialSequence` are the same
map; the two names come from the Section 4 and Section 6 arguments. -/
theorem translatePotentialSample_eq_translatePotentialSequence (z : Vec d) :
    translatePotentialSample (d := d) z = translatePotentialSequence z :=
  rfl

@[simp]
theorem translatePotentialSample_apply (z : Vec d)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) (k : ℕ) (x : Vec d) :
    translatePotentialSample z ω k x = ω k (x + z) :=
  rfl

@[simp]
theorem translatePotentialSample_zero
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    translatePotentialSample (0 : Vec d) ω = ω := by
  funext k
  exact potentialField_translate_zero (ω k)

/-- The action law: translating by `z` and then by `w` is translating by
`z + w`. -/
theorem translatePotentialSample_translate (z w : Vec d)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    translatePotentialSample w (translatePotentialSample z ω) =
      translatePotentialSample (z + w) ω := by
  funext k
  exact potentialField_translate_translate z w (ω k)

theorem measurable_translatePotentialSample (z : Vec d) :
    Measurable (translatePotentialSample (d := d) z) :=
  measurable_translatePotentialSequence z

/-- Translation by `z` is a measurable automorphism of the sample space, with
inverse translation by `-z`. -/
def translatePotentialSampleEquiv (z : Vec d) :
    _root_.SubdiffusiveProcess.Model.PotentialSample d ≃ᵐ
      _root_.SubdiffusiveProcess.Model.PotentialSample d where
  toEquiv :=
    { toFun := translatePotentialSample z
      invFun := translatePotentialSample (-z)
      left_inv := fun ω => by
        rw [translatePotentialSample_translate, add_neg_cancel,
          translatePotentialSample_zero]
      right_inv := fun ω => by
        rw [translatePotentialSample_translate, neg_add_cancel,
          translatePotentialSample_zero] }
  measurable_toFun := measurable_translatePotentialSample z
  measurable_invFun := measurable_translatePotentialSample (-z)

@[simp]
theorem coe_translatePotentialSampleEquiv (z : Vec d) :
    ⇑(translatePotentialSampleEquiv (d := d) z) = translatePotentialSample z :=
  rfl

/-! ### Stationarity -/

/-- The layer law is invariant under the translation action.  This is
`potentialSequenceLaw_stationary` read through the Section 6 name. -/
theorem map_translatePotentialSample
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (z : Vec d) :
    Measure.map (translatePotentialSample (d := d) z) M.P.toMeasure =
      M.P.toMeasure :=
  potentialSequenceLaw_stationary M z

theorem measurePreserving_translatePotentialSample
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (z : Vec d) :
    MeasurePreserving (translatePotentialSample (d := d) z)
      M.P.toMeasure M.P.toMeasure :=
  ⟨measurable_translatePotentialSample z, map_translatePotentialSample M z⟩

/-- The law-level transfer, **for an arbitrary set**.  No measurability of `E`
is required, because `translatePotentialSample z` is a measurable equivalence
rather than a bare measurable map. -/
theorem measure_preimage_translatePotentialSample
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (z : Vec d)
    (E : Set (_root_.SubdiffusiveProcess.Model.PotentialSample d)) :
    M.P.toMeasure (translatePotentialSample z ⁻¹' E) = M.P.toMeasure E := by
  have hmap := (translatePotentialSampleEquiv (d := d) z).map_apply
    (μ := M.P.toMeasure) E
  rw [coe_translatePotentialSampleEquiv, map_translatePotentialSample] at hmap
  exact hmap.symm

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance
