module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SimplexGapStrict

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-! ## The unit sphere of slopes -/

/-- **The source's `{|p| = 1}`**, in the ambient norm `vecNormSq`. -/
def vecUnitSphere (d : ℕ) : Set (Vec d) := {p : Vec d | vecNormSq p = 1}

theorem mem_vecUnitSphere_iff {p : Vec d} : p ∈ vecUnitSphere d ↔ vecNormSq p = 1 :=
  Iff.rfl

theorem isClosed_vecUnitSphere : IsClosed (vecUnitSphere d) :=
  isClosed_eq continuous_vecNormSq continuous_const

theorem isBounded_vecUnitSphere : Bornology.IsBounded (vecUnitSphere d) := by
  refine Bornology.IsBounded.subset
    (Metric.isBounded_closedBall (x := (0 : Vec d)) (r := 1)) ?_
  intro p hp
  have hp1 : vecNormSq p = 1 := hp
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
  have hsq : p i ^ (2 : ℕ) ≤ 1 := by
    have := sq_apply_le_vecNormSq p i
    rwa [hp1] at this
  rw [Real.norm_eq_abs]
  nlinarith [abs_nonneg (p i), sq_abs (p i)]

theorem isCompact_vecUnitSphere : IsCompact (vecUnitSphere d) := by
  have h := isBounded_vecUnitSphere (d := d) |>.isCompact_closure
  rwa [isClosed_vecUnitSphere.closure_eq] at h

theorem vecUnitSphere_nonempty (hd : 0 < d) : (vecUnitSphere d).Nonempty := by
  refine ⟨Pi.single ⟨0, hd⟩ 1, ?_⟩
  show vecNormSq (Pi.single ⟨0, hd⟩ (1 : ℝ)) = 1
  simp [vecNormSq, vecDot, Pi.single_apply, Finset.sum_ite_eq']

theorem ne_zero_of_mem_vecUnitSphere {p : Vec d} (hp : p ∈ vecUnitSphere d) : p ≠ 0 := by
  intro h
  have h1 : vecNormSq p = 1 := hp
  rw [h] at h1
  simp [vecNormSq, vecDot] at h1

/-! ## The one-cell minimum is a quadratic form in the slope -/

/-- A quadratic form in the slope is continuous. -/
theorem continuous_vecDot_matVecMul (A : Mat d) :
    Continuous fun p : Vec d => vecDot p (matVecMul A p) := by
  unfold vecDot matVecMul
  exact continuous_finset_sum _ fun i _ =>
    (continuous_apply i).mul
      (continuous_finset_sum _ fun j _ => continuous_const.mul (continuous_apply j))



theorem dirichletInfOn_shellFactor_eq_vol_mul (M : GMCModel d) (T : Kuhn.KuhnCell d)
    (omega : PotentialSample d) (p : Vec d) :
    dirichletInfOn (shellFactor M 0 omega) T.openCarrier p =
      (volume T.openCarrier).toReal *
        vecDot p (matVecMul (randomShellMatrix M 0 T omega) p) := by
  have hvol : (0 : ℝ) < (volume T.openCarrier).toReal :=
    volume_toReal_pos (kuhnCellDomain T)
  have h : vecDot p (matVecMul (randomShellMatrix M 0 T omega) p) =
      (volume T.openCarrier).toReal⁻¹ *
        dirichletInfOn (shellFactor M 0 omega) T.openCarrier p :=
    vecDot_aMatrix_eq_dirichletInfOn (shellFactorCoeffOnData M 0 omega _)
      (fun x => (shellFactor_pos M 0 omega x).le) p
  rw [h, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hvol), one_mul]

theorem continuous_dirichletInfOn_shellFactor (M : GMCModel d) (T : Kuhn.KuhnCell d)
    (omega : PotentialSample d) :
    Continuous fun p : Vec d =>
      dirichletInfOn (shellFactor M 0 omega) T.openCarrier p := by
  have hfun : (fun p : Vec d => dirichletInfOn (shellFactor M 0 omega) T.openCarrier p) =
      fun p : Vec d => (volume T.openCarrier).toReal *
        vecDot p (matVecMul (randomShellMatrix M 0 T omega) p) :=
    funext fun p => dirichletInfOn_shellFactor_eq_vol_mul M T omega p
  rw [hfun]
  exact continuous_const.mul (continuous_vecDot_matVecMul _)

/-! ## Continuity of the expectation -/

/-- **The expected one-cell minimum is continuous in the slope.**  Dominated
convergence against P-89's Piece 4: the family is dominated by
`|p|^2 int_spx B_0`, integrable with no moment assumption. -/
theorem continuous_integral_dirichletInfOn_shellFactor (M : GMCModel d)
    (T : Kuhn.KuhnCell d) :
    Continuous fun p : Vec d =>
      ∫ omega, dirichletInfOn (shellFactor M 0 omega) T.openCarrier p
        ∂M.P.toMeasure := by
  have hUmeas : MeasurableSet T.openCarrier := (Kuhn.isOpen_openCarrier T).measurableSet
  rw [continuous_iff_continuousAt]
  intro p₀
  refine continuousAt_of_dominated
    (bound := fun omega : PotentialSample d =>
      (vecNormSq p₀ + 1) * ∫ x in T.openCarrier, shellFactor M 0 omega x)
    (Filter.Eventually.of_forall fun p =>
      (measurable_dirichletInfOn_shellFactor M T p).aestronglyMeasurable) ?_ ?_
    (Filter.Eventually.of_forall fun omega =>
      (continuous_dirichletInfOn_shellFactor M T omega).continuousAt)
  · have hnhds : {p : Vec d | vecNormSq p < vecNormSq p₀ + 1} ∈ nhds p₀ := by
      exact (isOpen_lt continuous_vecNormSq continuous_const).mem_nhds (by simp)
    filter_upwards [hnhds] with p hp
    refine Filter.Eventually.of_forall fun omega => ?_
    have hnn : 0 ≤ ∫ x in T.openCarrier, shellFactor M 0 omega x :=
      setIntegral_nonneg hUmeas fun x _ => (shellFactor_pos M 0 omega x).le
    rw [Real.norm_eq_abs, abs_of_nonneg (dirichletInfOn_nonneg hUmeas
      (fun x => (shellFactor_pos M 0 omega x).le))]
    exact le_trans (dirichletInfOn_shellFactor_le M T p omega)
      (mul_le_mul_of_nonneg_right (le_of_lt hp) hnn)
  · exact (integrable_setIntegral_shellFactor M 0 hUmeas
      (isBounded_openCarrier T)).const_mul _

/-! ## `q_*` at one cell -/

/-- **`E[p . B_0(spx) p]`**, the expectation inside `e.strict.decay.qstar.def`
before the two suprema are taken. -/
def qStarSlope (M : GMCModel d) (T : Kuhn.KuhnCell d) (p : Vec d) : ℝ :=
  ∫ omega, vecDot p (matVecMul (randomShellMatrix M 0 T omega) p) ∂M.P.toMeasure

theorem qStarSlope_eq_inv_mul (M : GMCModel d) (T : Kuhn.KuhnCell d) (p : Vec d) :
    qStarSlope M T p = (volume T.openCarrier).toReal⁻¹ *
      ∫ omega, dirichletInfOn (shellFactor M 0 omega) T.openCarrier p
        ∂M.P.toMeasure := by
  have hpt : ∀ omega : PotentialSample d,
      vecDot p (matVecMul (randomShellMatrix M 0 T omega) p) =
        (volume T.openCarrier).toReal⁻¹ *
          dirichletInfOn (shellFactor M 0 omega) T.openCarrier p := fun omega =>
    vecDot_aMatrix_eq_dirichletInfOn (shellFactorCoeffOnData M 0 omega _)
      (fun x => (shellFactor_pos M 0 omega x).le) p
  rw [qStarSlope]
  simp only [hpt]
  exact integral_const_mul _ _

theorem continuous_qStarSlope (M : GMCModel d) (T : Kuhn.KuhnCell d) :
    Continuous (qStarSlope M T) := by
  have hfun : qStarSlope M T = fun p : Vec d => (volume T.openCarrier).toReal⁻¹ *
      ∫ omega, dirichletInfOn (shellFactor M 0 omega) T.openCarrier p
        ∂M.P.toMeasure :=
    funext (qStarSlope_eq_inv_mul M T)
  rw [hfun]
  exact continuous_const.mul (continuous_integral_dirichletInfOn_shellFactor M T)

/-- P-89's strict gap, restated on `qStarSlope`. -/
theorem qStarSlope_lt (M : GMCModel d) (T : Kuhn.KuhnCell d) {p : Vec d} (hp : p ≠ 0) :
    qStarSlope M T p < vecNormSq p :=
  integral_vecDot_randomShellMatrix_lt M T hp

/-- **`q_*(pi) = sup_{|p| = 1} E[p . B_0(spx_0^pi) p]`**, the inner supremum of
`e.strict.decay.qstar.def` (normalized, as the source's `fint` is). -/
def qStarCell (M : GMCModel d) (T : Kuhn.KuhnCell d) : ℝ :=
  sSup (qStarSlope M T '' vecUnitSphere d)

/-- **The supremum defining `q_*` is attained.**  This is item 1 of P-89's
frontier: without attainment the strict inequality at each slope does not
survive the supremum. -/
theorem exists_isMaxOn_qStarSlope (M : GMCModel d) (T : Kuhn.KuhnCell d) :
    ∃ p ∈ vecUnitSphere d, IsMaxOn (qStarSlope M T) (vecUnitSphere d) p :=
  isCompact_vecUnitSphere.exists_isMaxOn
    (vecUnitSphere_nonempty (lt_of_lt_of_le two_pos M.shellPrefix.dimension))
    (continuous_qStarSlope M T).continuousOn

theorem bddAbove_qStarSlope_image (M : GMCModel d) (T : Kuhn.KuhnCell d) :
    BddAbove (qStarSlope M T '' vecUnitSphere d) := by
  obtain ⟨p, hp, hmax⟩ := exists_isMaxOn_qStarSlope M T
  exact ⟨qStarSlope M T p, by rintro y ⟨q, hq, rfl⟩; exact hmax hq⟩

theorem exists_mem_vecUnitSphere_qStarCell_eq (M : GMCModel d) (T : Kuhn.KuhnCell d) :
    ∃ p ∈ vecUnitSphere d, qStarCell M T = qStarSlope M T p := by
  obtain ⟨p, hp, hmax⟩ := exists_isMaxOn_qStarSlope M T
  refine ⟨p, hp, IsGreatest.csSup_eq ⟨⟨p, hp, rfl⟩, ?_⟩⟩
  rintro y ⟨q, hq, rfl⟩
  exact hmax hq

theorem qStarSlope_le_qStarCell (M : GMCModel d) (T : Kuhn.KuhnCell d) {p : Vec d}
    (hp : p ∈ vecUnitSphere d) : qStarSlope M T p ≤ qStarCell M T :=
  le_csSup (bddAbove_qStarSlope_image M T) ⟨p, hp, rfl⟩



theorem qStarCell_lt_one (M : GMCModel d) (T : Kuhn.KuhnCell d) : qStarCell M T < 1 := by
  obtain ⟨p, hp, hqeq⟩ := exists_mem_vecUnitSphere_qStarCell_eq M T
  have hp1 : vecNormSq p = 1 := hp
  rw [hqeq]
  have := qStarSlope_lt M T (ne_zero_of_mem_vecUnitSphere hp)
  rwa [hp1] at this

/-! ## `q_*` as the maximum over the finite family of orders -/

/-- **`q_* < 1`** in the source's own shape (`e.strict.decay.qstar.gap`): a
single constant below one dominating `E[p . B_0(spx_0^pi) p]` for every order
`pi` in a finite family and every unit slope. -/
theorem exists_qStar_lt_one (M : GMCModel d) (S : Finset (Kuhn.KuhnCell d)) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧
      ∀ T ∈ S, ∀ p ∈ vecUnitSphere d, qStarSlope M T p ≤ q := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hS
  · exact ⟨0, le_rfl, one_pos, by simp⟩
  · refine ⟨max 0 (S.sup' hS (qStarCell M)), le_max_left _ _, ?_, ?_⟩
    · refine max_lt one_pos ((Finset.sup'_lt_iff hS).mpr fun T hT => qStarCell_lt_one M T)
    · intro T hT p hp
      exact le_trans (qStarSlope_le_qStarCell M T hp)
        (le_max_of_le_right (Finset.le_sup' (qStarCell M) hT))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
