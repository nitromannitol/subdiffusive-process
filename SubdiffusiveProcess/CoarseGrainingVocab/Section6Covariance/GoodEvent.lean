module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Observables
public import SubdiffusiveProcess.Frozen.Section6.Defs.GoodEvent



@[expose] public section

/-!
# Translation covariance of the Section 6 good event

The frozen good event `goodEvent M cutoff m y ε s` is the conjunction of the
two field conditions `GoodFieldOne`, `GoodFieldTwo` and the response condition
`GoodResponse`, all read on windows centred at the translate `y`.  This module
proves that each of the three, and therefore the event itself, is *exactly*
translation covariant:

```
ω ∈ goodEvent M cutoff m (z + y) ε s  ↔  translatePotentialSample z ω ∈ goodEvent M cutoff m y ε s
```

and in particular, at `y = 0`,

```
goodEvent M cutoff m z ε s = translatePotentialSample z ⁻¹' goodEvent M cutoff m 0 ε s .
```

The law-level consequence `measure_goodEvent_translate` says the probability of
the good event does not depend on the translate.  It is unconditional: it needs
no measurability of `goodEvent`, because `translatePotentialSample z` is a
measurable *automorphism* (see
`SubdiffusiveProcess/CoarseGrainingVocab/Section6Covariance/Action.lean`).  This matters, since
`goodEvent` is a conjunction of suprema over uncountable windows and of an
infinite product, and its measurability is not available in the tree.

The three component events `goodFieldOneEvent`, `goodFieldTwoEvent`,
`goodResponseEvent` below are the translated versions of the three private
component events of `SubdiffusiveProcess/Providers/Section6/DensityOfGoodScales.lean`, which are
the special case `cutoff = none`, `y = 0`.

## References

* `p.good.scale.mathcal.E` (the translated good event `G_{m,y}`).
* `p.good.scale.mathcal.E` (`p.good.scale.mathcal.E`, stated at
  translate `0`; the consumers read it at a translate).
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance

open MeasureTheory Homogenization
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ### Supremum norms on translated windows -/

/-- Precomposing with a translation moves the window of a supremum norm. -/
theorem supNormOn_comp_add (z : Vec d) (W : Set (Vec d)) (f : Vec d → ℝ) :
    supNormOn W (fun x => f (x + z)) = supNormOn ((fun p => z + p) '' W) f := by
  unfold supNormOn
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x + z, ⟨x, hx, add_comm z x⟩, rfl⟩
  · rintro ⟨q, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by rw [add_comm z x]⟩

/-- Precomposing with a translation moves the centre of a translated-cube
supremum norm. -/
theorem supNormOn_translatedCube_comp_add (z y : Vec d) (k : ℤ)
    (f : Vec d → ℝ) :
    supNormOn (translatedCube d k y) (fun x => f (x + z)) =
      supNormOn (translatedCube d k (z + y)) f := by
  rw [supNormOn_comp_add, image_add_left_translatedCube]

/-- The shell gradient is translation covariant. -/
theorem shellGradient_translate (z : Vec d)
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) (x : Vec d) :
    shellGradient (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g) x =
      shellGradient g (x + z) :=
  rfl

/-! ### The first field condition -/

/-- One summand of `GoodFieldOne`, transported. -/
theorem goodFieldOne_summand_translate (z y : Vec d) (k : ℤ) (i : ℕ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    supNormOn (translatedCube d k y) (fun x =>
        |translatePotentialSample z ω i x| + (3 : ℝ) ^ i *
          Homogenization.euclideanNorm
            (shellGradient (translatePotentialSample z ω i) x)) =
      supNormOn (translatedCube d k (z + y)) (fun x =>
        |ω i x| + (3 : ℝ) ^ i *
          Homogenization.euclideanNorm (shellGradient (ω i) x)) :=
  supNormOn_translatedCube_comp_add z y k (fun p =>
    |ω i p| + (3 : ℝ) ^ i *
      Homogenization.euclideanNorm (shellGradient (ω i) p))

/-- The first field condition is translation covariant. -/
theorem goodFieldOne_translatePotentialSample (m : ℕ) (y : Vec d)
    (epsilon s : ℝ) (z : Vec d)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    GoodFieldOne m y epsilon s (translatePotentialSample z ω) ↔
      GoodFieldOne m (z + y) epsilon s ω := by
  unfold GoodFieldOne
  refine forall_congr' fun j => ?_
  have hsum : (∑ i ∈ Finset.Icc (m - j) (m + j),
        supNormOn (translatedCube d ((m : ℤ) + 1 + (j : ℤ)) y) (fun x =>
          |translatePotentialSample z ω i x| + (3 : ℝ) ^ i *
            Homogenization.euclideanNorm
              (shellGradient (translatePotentialSample z ω i) x))) =
      ∑ i ∈ Finset.Icc (m - j) (m + j),
        supNormOn (translatedCube d ((m : ℤ) + 1 + (j : ℤ)) (z + y)) (fun x =>
          |ω i x| + (3 : ℝ) ^ i *
            Homogenization.euclideanNorm (shellGradient (ω i) x)) :=
    Finset.sum_congr rfl fun i _ =>
      goodFieldOne_summand_translate z y ((m : ℤ) + 1 + (j : ℤ)) i ω
  exact Iff.of_eq
    (congrArg (fun t : ℝ => t ≤ epsilon * (3 : ℝ) ^ ((s * (j : ℝ)) / 8)) hsum)

/-! ### The second field condition -/

/-- The second field condition is translation covariant.  The base point `y`
of the tail product translates with the window. -/
theorem goodFieldTwo_translatePotentialSample (m : ℕ) (y : Vec d) (s : ℝ)
    (z : Vec d) (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    GoodFieldTwo m y s (translatePotentialSample z ω) ↔
      GoodFieldTwo m (z + y) s ω := by
  unfold GoodFieldTwo
  refine forall_congr' fun j => ?_
  set g : Vec d → ℝ := fun p =>
    (∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |ω i p|) +
      ∏' i : ℕ, if m + j ≤ i then Real.exp (4 * |ω i p - ω i (z + y)|) else 1
    with hg
  have hfun : (fun x : Vec d =>
        (∏ i ∈ Finset.Icc (m - j) (m + j),
          Real.exp |translatePotentialSample z ω i x|) +
        ∏' i : ℕ, if m + j ≤ i then
          Real.exp (4 * |translatePotentialSample z ω i x -
            translatePotentialSample z ω i y|) else 1) =
      fun x : Vec d => g (x + z) := by
    funext x
    simp only [hg, translatePotentialSample_apply]
    rw [add_comm y z]
  have hsup : supNormOn (translatedCube d ((m : ℤ) + 1 + (j : ℤ)) y) (fun x =>
        (∏ i ∈ Finset.Icc (m - j) (m + j),
          Real.exp |translatePotentialSample z ω i x|) +
        ∏' i : ℕ, if m + j ≤ i then
          Real.exp (4 * |translatePotentialSample z ω i x -
            translatePotentialSample z ω i y|) else 1) =
      supNormOn (translatedCube d ((m : ℤ) + 1 + (j : ℤ)) (z + y)) g := by
    rw [hfun]
    exact supNormOn_translatedCube_comp_add z y _ g
  exact Iff.of_eq
    (congrArg (fun t : ℝ => t ≤ 6 * (3 : ℝ) ^ ((s * (j : ℝ)) / 8)) hsup)

/-! ### The response condition -/

/-- The response condition is translation covariant.  The annulus constraint
`w - y` is invariant under translating both the observation point and the base
point. -/
theorem goodResponse_translatePotentialSample
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (cutoff : Option ℕ) (m : ℕ)
    (y : Vec d) (epsilon s : ℝ) (z : Vec d)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    GoodResponse M cutoff m y epsilon s (translatePotentialSample z ω) ↔
      GoodResponse M cutoff m (z + y) epsilon s ω := by
  unfold GoodResponse
  constructor
  · intro h j n hjm hnj w hgrid hann e he
    have hsub : w - z - y = w - (z + y) := by rw [sub_sub, add_comm z y]
    have hkey := h j n hjm hnj (w - z) (by rw [hsub]; exact hgrid)
      (by rw [hsub]; exact hann) e he
    rw [section6Response_translatePotentialSample,
      show z + (w - z) = w by rw [add_sub_cancel]] at hkey
    exact hkey
  · intro h j n hjm hnj w hgrid hann e he
    have hsub : z + w - (z + y) = w - y := by
      rw [add_sub_add_left_eq_sub]
    rw [section6Response_translatePotentialSample]
    exact h j n hjm hnj (z + w) (by rw [hsub]; exact hgrid)
      (by rw [hsub]; exact hann) e he

/-! ### The good event -/

/-- The good event is exactly translation covariant. -/
theorem mem_goodEvent_translatePotentialSample
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (cutoff : Option ℕ) (m : ℕ)
    (y : Vec d) (epsilon s : ℝ) (z : Vec d)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    translatePotentialSample z ω ∈ goodEvent M cutoff m y epsilon s ↔
      ω ∈ goodEvent M cutoff m (z + y) epsilon s := by
  show (GoodFieldOne m y epsilon s (translatePotentialSample z ω) ∧
      GoodFieldTwo m y s (translatePotentialSample z ω) ∧
      GoodResponse M cutoff m y epsilon s (translatePotentialSample z ω)) ↔ _
  rw [goodFieldOne_translatePotentialSample, goodFieldTwo_translatePotentialSample,
    goodResponse_translatePotentialSample]
  exact Iff.rfl

/-- The good event at a translate is the preimage of the good event at the
untranslated base point. -/
theorem goodEvent_translatePotentialSample
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (cutoff : Option ℕ) (m : ℕ)
    (y : Vec d) (epsilon s : ℝ) (z : Vec d) :
    goodEvent M cutoff m (z + y) epsilon s =
      translatePotentialSample z ⁻¹' goodEvent M cutoff m y epsilon s := by
  ext ω
  exact (mem_goodEvent_translatePotentialSample M cutoff m y epsilon s z ω).symm

/-- The form the Section 6 consumers need: the good event at translate `z` is
the pullback of the good event at translate `0`. -/
theorem goodEvent_eq_preimage_translate_zero
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (cutoff : Option ℕ) (m : ℕ)
    (epsilon s : ℝ) (z : Vec d) :
    goodEvent M cutoff m z epsilon s =
      translatePotentialSample z ⁻¹' goodEvent M cutoff m 0 epsilon s := by
  have h := goodEvent_translatePotentialSample M cutoff m 0 epsilon s z
  rwa [add_zero] at h

/-- Membership form of `goodEvent_eq_preimage_translate_zero`. -/
theorem mem_goodEvent_iff_translate_zero
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (cutoff : Option ℕ) (m : ℕ)
    (epsilon s : ℝ) (z : Vec d)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    ω ∈ goodEvent M cutoff m z epsilon s ↔
      translatePotentialSample z ω ∈ goodEvent M cutoff m 0 epsilon s := by
  rw [goodEvent_eq_preimage_translate_zero]
  exact Iff.rfl




/-- The first field event at a translate.  At `y = 0` this is the private
`goodFieldOneEvent` of `SubdiffusiveProcess/Providers/Section6/DensityOfGoodScales.lean`. -/
def goodFieldOneEvent (m : ℕ) (y : Vec d) (epsilon s : ℝ) :
    Set (_root_.SubdiffusiveProcess.Model.PotentialSample d) :=
  {ω | GoodFieldOne m y epsilon s ω}

/-- The second field event at a translate. -/
def goodFieldTwoEvent (m : ℕ) (y : Vec d) (s : ℝ) :
    Set (_root_.SubdiffusiveProcess.Model.PotentialSample d) :=
  {ω | GoodFieldTwo m y s ω}

/-- The response event at a translate. -/
def goodResponseEvent (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (cutoff : Option ℕ) (m : ℕ) (y : Vec d) (epsilon s : ℝ) :
    Set (_root_.SubdiffusiveProcess.Model.PotentialSample d) :=
  {ω | GoodResponse M cutoff m y epsilon s ω}

/-- The good event is the intersection of its three component events. -/
theorem goodEvent_eq_inter (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (cutoff : Option ℕ) (m : ℕ) (y : Vec d) (epsilon s : ℝ) :
    goodEvent M cutoff m y epsilon s =
      goodFieldOneEvent m y epsilon s ∩ goodFieldTwoEvent m y s ∩
        goodResponseEvent M cutoff m y epsilon s := by
  ext ω
  exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩

theorem goodFieldOneEvent_translatePotentialSample (m : ℕ) (y : Vec d)
    (epsilon s : ℝ) (z : Vec d) :
    goodFieldOneEvent (d := d) m (z + y) epsilon s =
      translatePotentialSample z ⁻¹' goodFieldOneEvent m y epsilon s := by
  ext ω
  exact (goodFieldOne_translatePotentialSample m y epsilon s z ω).symm

theorem goodFieldTwoEvent_translatePotentialSample (m : ℕ) (y : Vec d) (s : ℝ)
    (z : Vec d) :
    goodFieldTwoEvent (d := d) m (z + y) s =
      translatePotentialSample z ⁻¹' goodFieldTwoEvent m y s := by
  ext ω
  exact (goodFieldTwo_translatePotentialSample m y s z ω).symm

theorem goodResponseEvent_translatePotentialSample
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (cutoff : Option ℕ) (m : ℕ)
    (y : Vec d) (epsilon s : ℝ) (z : Vec d) :
    goodResponseEvent M cutoff m (z + y) epsilon s =
      translatePotentialSample z ⁻¹' goodResponseEvent M cutoff m y epsilon s := by
  ext ω
  exact (goodResponse_translatePotentialSample M cutoff m y epsilon s z ω).symm

/-! ### The law-level equalities -/

/-- The probability of the good event does not depend on the translate.  No
measurability hypothesis is needed. -/
theorem measure_goodEvent_translate
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (cutoff : Option ℕ) (m : ℕ)
    (y : Vec d) (epsilon s : ℝ) (z : Vec d) :
    M.P.toMeasure (goodEvent M cutoff m (z + y) epsilon s) =
      M.P.toMeasure (goodEvent M cutoff m y epsilon s) := by
  rw [goodEvent_translatePotentialSample,
    measure_preimage_translatePotentialSample]

/-- The good event at any translate has the same probability as at the
origin. -/
theorem measure_goodEvent_eq_zero_translate
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (cutoff : Option ℕ) (m : ℕ)
    (epsilon s : ℝ) (z : Vec d) :
    M.P.toMeasure (goodEvent M cutoff m z epsilon s) =
      M.P.toMeasure (goodEvent M cutoff m 0 epsilon s) := by
  have h := measure_goodEvent_translate M cutoff m 0 epsilon s z
  rwa [add_zero] at h

theorem measure_goodFieldOneEvent_eq_zero_translate
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (epsilon s : ℝ)
    (z : Vec d) :
    M.P.toMeasure (goodFieldOneEvent (d := d) m z epsilon s) =
      M.P.toMeasure (goodFieldOneEvent (d := d) m 0 epsilon s) := by
  have h := goodFieldOneEvent_translatePotentialSample (d := d) m 0 epsilon s z
  rw [add_zero] at h
  rw [h, measure_preimage_translatePotentialSample]

theorem measure_goodFieldTwoEvent_eq_zero_translate
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (s : ℝ) (z : Vec d) :
    M.P.toMeasure (goodFieldTwoEvent (d := d) m z s) =
      M.P.toMeasure (goodFieldTwoEvent (d := d) m 0 s) := by
  have h := goodFieldTwoEvent_translatePotentialSample (d := d) m 0 s z
  rw [add_zero] at h
  rw [h, measure_preimage_translatePotentialSample]

theorem measure_goodResponseEvent_eq_zero_translate
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (cutoff : Option ℕ) (m : ℕ)
    (epsilon s : ℝ) (z : Vec d) :
    M.P.toMeasure (goodResponseEvent M cutoff m z epsilon s) =
      M.P.toMeasure (goodResponseEvent M cutoff m 0 epsilon s) := by
  have h := goodResponseEvent_translatePotentialSample M cutoff m 0 epsilon s z
  rw [add_zero] at h
  rw [h, measure_preimage_translatePotentialSample]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance
