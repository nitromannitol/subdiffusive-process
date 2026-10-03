module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeLargeBox
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeClauses
public import SubdiffusiveProcess.CoarseGrainingVocab.AnnealedProviders

@[expose] public section




set_option autoImplicit false

open MeasureTheory ProbabilityTheory Homogenization Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.Section9 (centeredAxisCube)

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open SubdiffusiveProcess.Frozen.Assumptions

variable {d : ℕ}

/-! ## Equivariance of the boxed observables -/

theorem boxDerivNorm_translate (v : Vec d) (g : PotentialField d) (K : Set (Vec d)) :
    boxDerivNorm K (PotentialField.translate v g) =
      boxDerivNorm ((fun y : Vec d => y + v) '' K) g := by
  unfold boxDerivNorm
  refine supWithZero_eq_of_range_eq ?_
  ext t
  constructor
  · rintro ⟨⟨x, hx⟩, rfl⟩
    exact ⟨⟨x + v, ⟨x, hx, rfl⟩⟩, by simp [Section6Anchored.deriv_translate]⟩
  · rintro ⟨⟨y, ⟨x, hx, rfl⟩⟩, rfl⟩
    exact ⟨⟨x, hx⟩, by simp [Section6Anchored.deriv_translate]⟩

theorem boxDerivLipschitzSeminorm_translate (v : Vec d) (g : PotentialField d)
    (K : Set (Vec d)) :
    boxDerivLipschitzSeminorm K (PotentialField.translate v g) =
      boxDerivLipschitzSeminorm ((fun y : Vec d => y + v) '' K) g := by
  unfold boxDerivLipschitzSeminorm
  refine supWithZero_eq_of_range_eq ?_
  ext t
  constructor
  · rintro ⟨⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hne⟩, rfl⟩
    refine ⟨⟨⟨⟨a + v, ⟨a, ha, rfl⟩⟩, ⟨b + v, ⟨b, hb, rfl⟩⟩⟩, ?_⟩, ?_⟩
    · intro h
      exact hne (Subtype.ext (add_right_cancel (congrArg Subtype.val h)))
    · simp only [Section6Anchored.deriv_translate, dist_add_right]
  · rintro ⟨⟨⟨⟨y, ⟨a, ha, rfl⟩⟩, ⟨y', ⟨b, hb, rfl⟩⟩⟩, hne⟩, rfl⟩
    refine ⟨⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, ?_⟩, ?_⟩
    · intro h
      have hab : a = b := congrArg Subtype.val h
      subst hab
      exact hne rfl
    · simp only [Section6Anchored.deriv_translate, dist_add_right]

theorem layerObservable_translate (n : ℕ) (v : Vec d) (K : Set (Vec d))
    (g : PotentialField d) :
    layerObservable n K (PotentialField.translate v g) =
      layerObservable n ((fun y : Vec d => y + v) '' K) g := by
  unfold layerObservable
  rw [boxDerivNorm_translate, boxDerivLipschitzSeminorm_translate]

/-! ## Equivariance of the boxes -/

theorem goodCubeCentre_add (n : ℕ) (z a : Lattice d) :
    goodCubeCentre n (z + a) = goodCubeCentre n z + goodCubeCentre n a := by
  funext i
  simp only [goodCubeCentre, Pi.add_apply, Int.cast_add]
  ring

theorem centeredAxisCube_add (x v : Vec d) (L : ℝ) :
    centeredAxisCube (x + v) L = (fun y : Vec d => y + v) '' centeredAxisCube x L := by
  ext y
  simp only [Set.mem_image]
  constructor
  · intro hy
    refine ⟨y - v, ?_, by abel⟩
    rw [mem_centeredAxisCube] at hy ⊢
    intro i
    have h : (y - v) i - x i = y i - (x + v) i := by
      simp only [Pi.sub_apply, Pi.add_apply]; ring
    rw [h]
    exact hy i
  · rintro ⟨w, hw, rfl⟩
    rw [mem_centeredAxisCube] at hw ⊢
    intro i
    have h : (w + v) i - (x + v) i = w i - x i := by
      simp only [Pi.add_apply]; ring
    rw [h]
    exact hw i

theorem nativeBox_add (n : ℕ) (C : ℝ) (z a : Lattice d) :
    nativeBox n C (z + a) =
      (fun y : Vec d => y + goodCubeCentre n a) '' nativeBox n C z := by
  unfold nativeBox
  rw [goodCubeCentre_add, centeredAxisCube_add]

/-! ## Covariance of the layer events -/

/-- **Clause 7f for the layers.**  The layer event at the translated site is the
`T a`-preimage of the layer event at the original site, for the single diagonal
translation `T a` of all shells by `3^n a`. -/
theorem layerEvent_translate (n j : ℕ) (C eps1 : ℝ) (z a : Lattice d) :
    layerEvent n j C eps1 (z + a) =
      (translatePotentialSequence (goodCubeCentre n a)) ⁻¹' (layerEvent n j C eps1 z) := by
  ext omega
  simp only [layerEvent, Set.mem_preimage, Set.mem_setOf_eq]
  have hfield : (translatePotentialSequence (goodCubeCentre n a) omega) (n + j) =
      PotentialField.translate (goodCubeCentre n a) (omega (n + j)) := rfl
  rw [hfield, layerObservable_translate, ← nativeBox_add]



theorem covariant_of_recentredFunctional (M : GMCModel d) (n : ℕ)
    (Phi : (Vec d → ℝ) → Prop) (z a : Lattice d) :
    {omega : PotentialSample d |
        Phi fun x => aCutoff M n omega (x + goodCubeCentre n (z + a))} =
      (translatePotentialSequence (goodCubeCentre n a)) ⁻¹'
        {omega : PotentialSample d |
          Phi fun x => aCutoff M n omega (x + goodCubeCentre n z)} := by
  ext omega
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  have hfun : (fun x : Vec d =>
      aCutoff M n (translatePotentialSequence (goodCubeCentre n a) omega)
        (x + goodCubeCentre n z)) =
      fun x : Vec d => aCutoff M n omega (x + goodCubeCentre n (z + a)) := by
    funext x
    rw [aCutoff_translatePotentialSequence, goodCubeCentre_add]
    congr 1
    abel
  rw [hfun]

/-! ## Clause 7f -/

theorem measurableSet_of_shellLocalSigma {k : ℕ} {B : Set (Vec d)}
    {s : Set (PotentialSample d)} (h : MeasurableSet[shellLocalSigma k B] s) :
    MeasurableSet s := by
  have hle : shellLocalSigma (d := d) k B ≤
      (inferInstance : MeasurableSpace (PotentialSample d)) :=
    le_trans (MeasurableSpace.comap_mono (potentialFieldLocalSigma_le_borel B))
      (SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate k).comap_le
  exact hle _ h

/-- **Clause 7f of `SubdiffusiveProcess.Frozen.Section9.weighted_good_cube_events`, for the
concrete event field.**  Given the ambient measurability of the layer-zero
event and its covariance under the diagonal translation family — the two
properties any construction of `G(U)` out of the cutoff field on `CU` has, by
`covariant_of_recentredFunctional` — the whole field has a translation
invariant law.  The probabilistic input is `(g1)` stationarity, through
`SubdiffusiveProcess.CoarseGrainingVocab.potentialSequenceLaw_stationary`. -/
theorem translationInvariantEventLaw_goodCubeEventField (M : GMCModel d) (n : ℕ)
    {C eps1 : ℝ} (hC : 0 ≤ C) [NeZero d]
    (E0 : Lattice d → Set (PotentialSample d))
    (hE0meas : ∀ z : Lattice d, MeasurableSet (E0 z))
    (hE0cov : ∀ z a : Lattice d,
      E0 (z + a) = (translatePotentialSequence (goodCubeCentre n a)) ⁻¹' (E0 z)) :
    TranslationInvariantEventLaw M.P.toMeasure (goodCubeEventField n C eps1 E0) := by
  refine translationInvariantEventLaw_of_covariant ?_
    (fun a => translatePotentialSequence (goodCubeCentre n a))
    (fun a => measurable_translatePotentialSequence _)
    (fun a => potentialSequenceLaw_stationary M _) ?_
  · intro j z
    match j with
    | 0 => exact hE0meas z
    | (i + 1) =>
        exact measurableSet_of_shellLocalSigma
          (measurableSet_layerEvent hC n (i + 1) eps1 z)
  · intro j z a
    match j with
    | 0 => exact hE0cov z a
    | (i + 1) => exact layerEvent_translate n (i + 1) C eps1 z a

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
