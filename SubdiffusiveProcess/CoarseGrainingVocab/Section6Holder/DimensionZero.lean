module

public import SubdiffusiveProcess.Frozen.Section6.Defs.HolderRegularityConclusions
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.ScaledInterface
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.Windows

@[expose] public section

/-!
# The degenerate zero-dimensional Hölder conclusion

The analytic ladder is only needed in positive dimension.  On `Vec 0` every
scalar function is constant and every vector field vanishes, so all three
rows of `HolderRegularityConclusions` have zero left-hand side.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab Homogenization

noncomputable section
attribute [local instance] Classical.propDecidable

private theorem vecField_dim_zero (f : Vec 0 → Vec 0) : f = 0 := by
  funext x
  exact Section6Iteration.vec_dim_zero_eq (f x) 0

private theorem holderSeminormOn_dim_zero (W : Set (Vec 0)) (alpha : ℝ)
    (f : Vec 0 → Vec 0) : holderSeminormOn W alpha f = 0 := by
  unfold holderSeminormOn
  have hempty : {r : ℝ | ∃ x ∈ W, ∃ y ∈ W, x ≠ y ∧
      r = euclideanNorm (f x - f y) / euclideanNorm (x - y) ^ alpha} = ∅ := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨x, _hx, y, _hy, hxy, _hr⟩
    exact hxy (Section6Iteration.vec_dim_zero_eq x y)
  rw [hempty, Real.sSup_empty]

private theorem vectorSupNormOn_dim_zero (W : Set (Vec 0)) (hW : W.Nonempty)
    (f : Vec 0 → Vec 0) : vectorSupNormOn W f = 0 := by
  unfold vectorSupNormOn
  have hset : {r : ℝ | ∃ x ∈ W, r = euclideanNorm (f x)} = {0} := by
    ext r
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hzero : f x = 0 := Section6Iteration.vec_dim_zero_eq (f x) 0
      simp only [hzero, euclideanNorm_zero, Set.mem_singleton_iff]
    · intro hr
      rw [Set.mem_singleton_iff] at hr
      obtain ⟨x, hx⟩ := hW
      refine ⟨x, hx, ?_⟩
      rw [hr]
      have hzero : f x = 0 := Section6Iteration.vec_dim_zero_eq (f x) 0
      simp only [hzero, euclideanNorm_zero]
  rw [hset, csSup_singleton]

private theorem vectorNormalizedL2On_dim_zero (W : Set (Vec 0))
    (hW : 0 < (volume W).toReal) (f : Vec 0 → Vec 0) :
    vectorNormalizedL2On W f = 0 := by
  unfold vectorNormalizedL2On
  have hfun : (fun x ↦ euclideanNorm (f x)) = (fun _ : Vec 0 ↦ (0 : ℝ)) := by
    funext x
    have hzero : f x = 0 := Section6Iteration.vec_dim_zero_eq (f x) 0
    simp only [hzero, euclideanNorm_zero]
  rw [hfun, Section6Iteration.normalizedL2On_dim_zero hW _ 0, abs_zero]

/-- `HolderRegularityConclusions` is automatic in dimension zero. -/
theorem holderRegularityConclusions_dim_zero
    (M : _root_.SubdiffusiveProcess.Model.GMCModel 0) (C : ℝ) (hC : 0 ≤ C)
    (L : ℕ) (ω : _root_.SubdiffusiveProcess.Model.PotentialSample 0) (alpha : ℝ)
    (m X : ℕ) (u h : H1Function (openCubeSet (originCube 0 m)))
    (g : Vec 0 → Vec 0) :
    HolderRegularityConclusions M C L ω alpha m X u h g := by
  unfold HolderRegularityConclusions
  have hcube : (cube 0 (m : ℤ)).Nonempty :=
    ⟨0, Section6ExcessDecay.zero_mem_cube 0 (m : ℤ)⟩
  have hglobalOsc : normalizedL2On (cube 0 (m : ℤ))
      (fun z ↦ u.toFun z - averageOn (cube 0 (m : ℤ)) u.toFun) = 0 := by
    apply Section6Iteration.normalizedL2On_sub_average_dim_zero
    rw [cube, volume_openCubeSet_toReal]
    exact cubeVolume_pos (originCube 0 (m : ℤ))
  have hgzero : holderSeminormOn (cube 0 (m : ℤ)) (1 / 2) g = 0 :=
    holderSeminormOn_dim_zero _ _ _
  have hhzero : fractionalInfinityNormOnReal (cube 0 (m : ℤ)) ((3 : ℝ) ^ m)
      (1 / 2) h.grad = 0 := full_norm_dim_zero _ _ _ _ (by positivity)
  have hsupzero : vectorSupNormOn (cube 0 (m : ℤ)) h.grad = 0 :=
    vectorSupNormOn_dim_zero _ hcube _
  have henergyGlobal : vectorNormalizedL2On (cube 0 (m : ℤ))
      (fun z ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L ω z) • u.grad z) = 0 := by
    apply vectorNormalizedL2On_dim_zero
    change 0 < (volume (openCubeSet (originCube 0 (m : ℤ)))).toReal
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos (originCube 0 (m : ℤ))
  constructor
  · intro n hn x hx ell hell y _hygrid hy
    have hvol := Section6ExcessDecay.volume_toReal_truncatedCube_pos
      (m := (m : ℤ)) (j := (ell : ℤ)) y hy.2 (by omega)
    rw [Section6Iteration.normalizedL2On_sub_average_dim_zero hvol,
      hglobalOsc, hgzero, hhzero]
    simp only [mul_zero, add_zero]
    positivity
  constructor
  · intro n hn x hx
    have hvol := Section6ExcessDecay.volume_toReal_truncatedCube_pos
      (m := (m : ℤ)) (j := (n : ℤ)) x hx (by omega)
    rw [vectorNormalizedL2On_dim_zero _ hvol, henergyGlobal, hgzero, hhzero]
    simp only [mul_zero, add_zero]
    positivity
  · intro n _hn _hgap ell _hnell hellm x hx
    have hvolN := Section6ExcessDecay.volume_toReal_truncatedCube_pos
      (m := (m : ℤ)) (j := (n : ℤ)) x hx (by omega)
    have hvolEll := Section6ExcessDecay.volume_toReal_truncatedCube_pos
      (m := (m : ℤ)) (j := (ell : ℤ)) x hx (by omega)
    rw [Section6Iteration.excess_dim_zero hvolN,
      Section6Iteration.excess_dim_zero hvolEll,
      Section6Iteration.normalizedL2On_sub_average_dim_zero hvolEll,
      hgzero, hsupzero, hhzero]
    simp only [mul_zero, add_zero]
    positivity

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
