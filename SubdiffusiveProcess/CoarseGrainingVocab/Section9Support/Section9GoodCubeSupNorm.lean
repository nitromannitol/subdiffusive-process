module

public import SubdiffusiveProcess.CoarseGrainingVocab.NegativeBesovSupport
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

@[expose] public section




set_option autoImplicit false

open MeasureTheory Homogenization Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-! ## A general supremum lemma -/

/-- The supremum of `f` over `X`, with `0` adjoined so that the value is always
defined and nonnegative.  This is the encoding the frozen `(g2)` observables
`SubdiffusiveProcess.Frozen.Assumptions.PotentialField.unitCubeValueNorm` and its siblings use. -/
def supWithZero {X : Type*} (f : X → ℝ) : ℝ :=
  sSup (Set.range (fun o : Option X => o.elim 0 f))

theorem bddAbove_optionRange {X : Type*} {f : X → ℝ} (h : BddAbove (Set.range f)) :
    BddAbove (Set.range (fun o : Option X => o.elim 0 f)) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨max 0 c, ?_⟩
  rintro r ⟨o, rfl⟩
  cases o with
  | none => exact le_max_left _ _
  | some x => exact (hc ⟨x, rfl⟩).trans (le_max_right _ _)

theorem le_supWithZero {X : Type*} {f : X → ℝ} (h : BddAbove (Set.range f)) (x : X) :
    f x ≤ supWithZero f :=
  le_csSup (bddAbove_optionRange h) ⟨some x, rfl⟩

theorem supWithZero_nonneg {X : Type*} {f : X → ℝ} (h : BddAbove (Set.range f)) :
    0 ≤ supWithZero f :=
  le_csSup (bddAbove_optionRange h) ⟨none, rfl⟩

theorem supWithZero_le {X : Type*} {f : X → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hf : ∀ x, f x ≤ b) : supWithZero f ≤ b := by
  refine csSup_le ⟨0, ⟨none, rfl⟩⟩ ?_
  rintro r ⟨o, rfl⟩
  cases o with
  | none => exact hb
  | some x => exact hf x



theorem measurable_supWithZero_of_separable {Omega X : Type*} [MeasurableSpace Omega]
    [TopologicalSpace X] [TopologicalSpace.SeparableSpace X]
    (F : Omega → X → ℝ) (hcont : ∀ w, Continuous (F w))
    (hbdd : ∀ w, BddAbove (Set.range (F w)))
    (hmeas : ∀ x : X, Measurable (fun w => F w x)) :
    Measurable (fun w => supWithZero (F w)) := by
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense X
  haveI : Countable D := hDcount.to_subtype
  have hbddD : ∀ w : Omega, BddAbove (Set.range (fun p : D => F w p.1)) := by
    intro w
    obtain ⟨c, hc⟩ := hbdd w
    exact ⟨c, by rintro r ⟨p, rfl⟩; exact hc ⟨p.1, rfl⟩⟩
  have hEq : ∀ w : Omega, supWithZero (fun p : D => F w p.1) = supWithZero (F w) := by
    intro w
    refine le_antisymm ?_ ?_
    · exact supWithZero_le (supWithZero_nonneg (hbdd w)) fun p => le_supWithZero (hbdd w) p.1
    · refine supWithZero_le (supWithZero_nonneg (hbddD w)) ?_
      intro x
      have hclosed : IsClosed {y : X | F w y ≤ supWithZero (fun p : D => F w p.1)} :=
        isClosed_le (hcont w) continuous_const
      have hsub : D ⊆ {y : X | F w y ≤ supWithZero (fun p : D => F w p.1)} :=
        fun y hy => le_supWithZero (hbddD w) ⟨y, hy⟩
      have hcl := closure_minimal hsub hclosed
      rw [hDdense.closure_eq] at hcl
      exact hcl (Set.mem_univ x)
  have hmeasD : Measurable (fun w : Omega => supWithZero (fun p : D => F w p.1)) := by
    have h : Measurable (fun w : Omega =>
        ⨆ o : Option D, (o.elim 0 (fun p : D => F w p.1))) := by
      refine Measurable.iSup ?_
      intro o
      cases o with
      | none => exact measurable_const
      | some p => exact hmeas p.1
    simpa only [supWithZero, iSup] using h
  simpa only [hEq] using hmeasD

/-! ## The derivative of a potential is a local observable -/

open SubdiffusiveProcess.Frozen.Assumptions

variable {d : ℕ}

/-- The directional derivative of a potential at an interior point of `U` is
measurable for `PotentialField.localSigma U`: it is the limit of difference
quotients of the value at points of `U`, and each value is local by
`SubdiffusiveProcess.CoarseGrainingVocab.measurable_eval_potentialFieldLocalSigma_of_mem_isOpen`. -/
theorem measurable_deriv_apply_localSigma [NeZero d] {U : Set (Vec d)} (hU : IsOpen U)
    {x : Vec d} (hx : x ∈ U) (v : Vec d) :
    @Measurable (PotentialField d) ℝ
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma U) _
      (fun g => PotentialField.deriv g x v) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
  set c : ℕ → ℝ := fun n => ((n : ℝ) + 1) * (1 + ‖v‖) / r with hc
  have hcpos : ∀ n, 0 < c n := by
    intro n
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < 1 + ‖v‖ := by positivity
    exact div_pos (mul_pos h1 h2) hr
  have hsmall : ∀ n, x + (c n)⁻¹ • v ∈ U := by
    intro n
    apply hball
    have hnorm : ‖(c n)⁻¹ • v‖ < r := by
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (hcpos n)]
      rw [inv_mul_eq_div, div_lt_iff₀ (hcpos n)]
      have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hexp : r * c n = ((n : ℝ) + 1) * (1 + ‖v‖) := by
        simp only [hc]
        field_simp
      rw [hexp]
      nlinarith [norm_nonneg v]
    simpa [Metric.mem_ball, dist_eq_norm] using hnorm
  have hmeas : ∀ n, @Measurable (PotentialField d) ℝ
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma U) _
      (fun g : PotentialField d => c n • (g (x + (c n)⁻¹ • v) - g x)) := by
    intro n
    have h1 := SubdiffusiveProcess.CoarseGrainingVocab.measurable_eval_potentialFieldLocalSigma_of_mem_isOpen
      hU (hsmall n)
    have h2 := SubdiffusiveProcess.CoarseGrainingVocab.measurable_eval_potentialFieldLocalSigma_of_mem_isOpen
      hU hx
    exact (h1.sub h2).const_smul (c n)
  refine @measurable_of_tendsto_metrizable (PotentialField d) ℝ
    (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma U) _ _ _ _
    (fun n g => c n • (g (x + (c n)⁻¹ • v) - g x)) _ hmeas ?_
  rw [tendsto_pi_nhds]
  intro g
  refine (g.hasFDerivAt x).lim v ?_
  have hpos : (0 : ℝ) < (1 + ‖v‖) / r := by positivity
  have hlim : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * ((1 + ‖v‖) / r)) atTop atTop :=
    Filter.Tendsto.atTop_mul_const hpos
      (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have heq : (fun n : ℕ => ‖c n‖) = fun n : ℕ => ((n : ℝ) + 1) * ((1 + ‖v‖) / r) := by
    funext n
    rw [Real.norm_eq_abs, abs_of_pos (hcpos n), hc]
    ring
  rw [heq]
  exact hlim

/-- The `i`th standard basis vector of `Vec d = Fin d → ℝ`. -/
def basisVec (d : ℕ) (i : Fin d) : Vec d := Pi.single i (1 : ℝ)

/-- A real linear functional on `Vec d = Fin d → ℝ` is the sum of its
coordinate values against the coordinate projections. -/
theorem clm_eq_sum_proj (L : Vec d →L[ℝ] ℝ) :
    L = ∑ i : Fin d, (L (basisVec d i)) • ContinuousLinearMap.proj i := by
  ext y
  have hy : y = ∑ i : Fin d, y i • (basisVec d i) := by
    funext j
    simp [basisVec, Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq]
  calc L y = L (∑ i : Fin d, y i • (basisVec d i)) := by rw [← hy]
    _ = ∑ i : Fin d, y i * L (basisVec d i) := by rw [map_sum]; simp
    _ = (∑ i : Fin d, (L (basisVec d i)) •
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i) y := by
        simp [ContinuousLinearMap.sum_apply, mul_comm]

/-- **The stored derivative at an interior point is a local observable.**  This is
the analytic content of obligation O3: `LocalSigmaR` only sees integral entry
tests, but a `C¹` field's derivative is recovered from them through ball averages
and difference quotients. -/
theorem measurable_deriv_localSigma [NeZero d] {U : Set (Vec d)} (hU : IsOpen U)
    {x : Vec d} (hx : x ∈ U) :
    @Measurable (PotentialField d) (Vec d →L[ℝ] ℝ)
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma U) _
      (fun g => PotentialField.deriv g x) := by
  have hexp : (fun g : PotentialField d => PotentialField.deriv g x)
      = fun g : PotentialField d => ∑ i : Fin d,
        (PotentialField.deriv g x (basisVec d i)) • ContinuousLinearMap.proj i := by
    funext g
    exact clm_eq_sum_proj _
  rw [hexp]
  letI : MeasurableSpace (PotentialField d) :=
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma U
  refine Finset.measurable_sum Finset.univ ?_
  intro i _
  have hcont : Continuous
      (fun t : ℝ => t • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i)) :=
    continuous_id.smul continuous_const
  exact hcont.measurable.comp (measurable_deriv_apply_localSigma hU hx _)

/-! ## The boxed `(g2)` observables -/

/-- `‖g‖_{L^∞(K)}` in the `(g2)` convention of
`SubdiffusiveProcess.Frozen.Assumptions.PotentialField.unitCubeValueNorm`. -/
def boxValueNorm (K : Set (Vec d)) (g : PotentialField d) : ℝ :=
  supWithZero (fun x : K => |g x.1|)

/-- `‖∇g‖_{L^∞(K)}` in the `(g2)` convention of
`SubdiffusiveProcess.Frozen.Assumptions.PotentialField.unitCubeDerivNorm`. -/
def boxDerivNorm (K : Set (Vec d)) (g : PotentialField d) : ℝ :=
  supWithZero (fun x : K => ‖PotentialField.deriv g x.1‖)

/-- `‖∇²g‖_{L^∞(K)}` in the `C¹ˑ¹` convention of
`SubdiffusiveProcess.Frozen.Assumptions.PotentialField.unitCubeDerivLipschitzSeminorm`: the
Lipschitz seminorm of the stored derivative on `K`. -/
def boxDerivLipschitzSeminorm (K : Set (Vec d)) (g : PotentialField d) : ℝ :=
  supWithZero (fun p : {p : K × K // p.1 ≠ p.2} =>
    dist (PotentialField.deriv g p.1.1.1) (PotentialField.deriv g p.1.2.1) /
      dist p.1.1.1 p.1.2.1)

/-- The boxed value norm on the unit cube is the frozen `(g2)` value observable. -/
theorem boxValueNorm_eq_unitCubeValueNorm (g : PotentialField d) :
    boxValueNorm (openCubeSet (originCube d 0)) g =
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.unitCubeValueNorm g := by
  have hfun : (fun o : Option {x : Vec d // x ∈ openCubeSet (originCube d 0)} =>
      o.elim (0 : ℝ) (fun x => |g x.1|)) =
      (fun o : Option {x : Vec d // x ∈ openCubeSet (originCube d 0)} =>
        match o with | none => (0 : ℝ) | some x => |g x.1|) := by
    funext o; cases o <;> rfl
  show sSup (Set.range (fun o : Option {x : Vec d // x ∈ openCubeSet (originCube d 0)} =>
      o.elim (0 : ℝ) (fun x => |g x.1|))) = _
  rw [hfun]
  rfl

/-- The boxed gradient norm on the unit cube is the frozen `(g2)` gradient
observable. -/
theorem boxDerivNorm_eq_unitCubeDerivNorm (g : PotentialField d) :
    boxDerivNorm (openCubeSet (originCube d 0)) g =
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.unitCubeDerivNorm g := by
  have hfun : (fun o : Option {x : Vec d // x ∈ openCubeSet (originCube d 0)} =>
      o.elim (0 : ℝ) (fun x => ‖PotentialField.deriv g x.1‖)) =
      (fun o : Option {x : Vec d // x ∈ openCubeSet (originCube d 0)} =>
        match o with | none => (0 : ℝ) | some x => ‖PotentialField.deriv g x.1‖) := by
    funext o; cases o <;> rfl
  show sSup (Set.range (fun o : Option {x : Vec d // x ∈ openCubeSet (originCube d 0)} =>
      o.elim (0 : ℝ) (fun x => ‖PotentialField.deriv g x.1‖))) = _
  rw [hfun]
  rfl

/-- The boxed derivative Lipschitz seminorm on the unit cube is the frozen
`C¹ˑ¹` observable. -/
theorem boxDerivLipschitzSeminorm_eq_unitCubeDerivLipschitzSeminorm
    (g : PotentialField d) :
    boxDerivLipschitzSeminorm (openCubeSet (originCube d 0)) g =
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.unitCubeDerivLipschitzSeminorm g := by
  have hfun : (fun o : Option {p : {x : Vec d // x ∈ openCubeSet (originCube d 0)} ×
        {x : Vec d // x ∈ openCubeSet (originCube d 0)} // p.1 ≠ p.2} =>
      o.elim (0 : ℝ) (fun p => dist (PotentialField.deriv g p.1.1.1)
        (PotentialField.deriv g p.1.2.1) / dist p.1.1.1 p.1.2.1)) =
      (fun o : Option {p : {x : Vec d // x ∈ openCubeSet (originCube d 0)} ×
          {x : Vec d // x ∈ openCubeSet (originCube d 0)} // p.1 ≠ p.2} =>
        match o with
        | none => (0 : ℝ)
        | some p => dist (PotentialField.deriv g p.1.1.1)
            (PotentialField.deriv g p.1.2.1) / dist p.1.1.1 p.1.2.1) := by
    funext o; cases o <;> rfl
  show sSup (Set.range (fun o : Option {p : {x : Vec d // x ∈ openCubeSet (originCube d 0)} ×
        {x : Vec d // x ∈ openCubeSet (originCube d 0)} // p.1 ≠ p.2} =>
      o.elim (0 : ℝ) (fun p => dist (PotentialField.deriv g p.1.1.1)
        (PotentialField.deriv g p.1.2.1) / dist p.1.1.1 p.1.2.1))) = _
  rw [hfun]
  rfl

/-! ### Boundedness of the boxed observables on a bounded box -/

theorem bddAbove_boxDerivNorm_family {K : Set (Vec d)} (hK : Bornology.IsBounded K)
    (g : PotentialField d) :
    BddAbove (Set.range (fun x : K => ‖PotentialField.deriv g x.1‖)) := by
  obtain ⟨C, hC⟩ := hK.isCompact_closure.exists_bound_of_continuousOn
    (continuous_norm.comp (PotentialField.deriv g).continuous).continuousOn
  refine ⟨max 0 C, ?_⟩
  rintro r ⟨x, rfl⟩
  have hx : x.1 ∈ closure K := subset_closure x.2
  have h := hC x.1 hx
  have h' : ‖PotentialField.deriv g x.1‖ ≤ C := by
    simpa only [Function.comp_apply, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)] using h
  exact h'.trans (le_max_right _ _)

theorem bddAbove_boxDerivLipschitzSeminorm_family {K : Set (Vec d)}
    (hK : Bornology.IsBounded K) (g : PotentialField d) :
    BddAbove (Set.range (fun p : {p : K × K // p.1 ≠ p.2} =>
      dist (PotentialField.deriv g p.1.1.1) (PotentialField.deriv g p.1.2.1) /
        dist p.1.1.1 p.1.2.1)) := by
  obtain ⟨C, hC⟩ := g.2.2 (closure K) hK.isCompact_closure
  refine ⟨max 0 C, ?_⟩
  rintro r ⟨p, rfl⟩
  have hne : p.1.1.1 ≠ p.1.2.1 := fun h => p.property (Subtype.ext h)
  have hdist : 0 < dist p.1.1.1 p.1.2.1 := dist_pos.mpr hne
  have hlip := hC.dist_le_mul p.1.1.1 (subset_closure p.1.1.2) p.1.2.1 (subset_closure p.1.2.2)
  exact ((div_le_iff₀ hdist).2 hlip).trans (le_max_right _ _)

/-! ### Obligation O3 for a single layer -/



theorem measurable_boxDerivNorm_localSigma [NeZero d] {U K : Set (Vec d)}
    (hU : IsOpen U) (hKU : K ⊆ U) (hK : Bornology.IsBounded K) :
    @Measurable (PotentialField d) ℝ
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma U) _ (boxDerivNorm K) := by
  letI : MeasurableSpace (PotentialField d) :=
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma U
  refine measurable_supWithZero_of_separable
    (fun g : PotentialField d => fun x : K => ‖PotentialField.deriv g x.1‖)
    (fun g => continuous_norm.comp
      ((PotentialField.deriv g).continuous.comp continuous_subtype_val))
    (fun g => bddAbove_boxDerivNorm_family hK g) ?_
  intro x
  exact continuous_norm.measurable.comp (measurable_deriv_localSigma hU (hKU x.2))



theorem measurable_boxDerivLipschitzSeminorm_localSigma [NeZero d] {U K : Set (Vec d)}
    (hU : IsOpen U) (hKU : K ⊆ U) (hK : Bornology.IsBounded K) :
    @Measurable (PotentialField d) ℝ
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma U) _
      (boxDerivLipschitzSeminorm K) := by
  letI : MeasurableSpace (PotentialField d) :=
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma U
  refine measurable_supWithZero_of_separable
    (fun g : PotentialField d => fun p : {p : K × K // p.1 ≠ p.2} =>
      dist (PotentialField.deriv g p.1.1.1) (PotentialField.deriv g p.1.2.1) /
        dist p.1.1.1 p.1.2.1)
    (fun g => ?_) (fun g => bddAbove_boxDerivLipschitzSeminorm_family hK g) ?_
  · refine Continuous.div ?_ ?_ ?_
    · exact Continuous.dist
        ((PotentialField.deriv g).continuous.comp
          (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)))
        ((PotentialField.deriv g).continuous.comp
          (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)))
    · exact (continuous_subtype_val.comp
        (continuous_fst.comp continuous_subtype_val)).dist
          (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val))
    · intro p
      exact dist_ne_zero.mpr fun h => p.property (Subtype.ext h)
  · intro p
    have h1 := measurable_deriv_localSigma (d := d) hU (hKU p.1.1.2)
    have h2 := measurable_deriv_localSigma (d := d) hU (hKU p.1.2.2)
    exact (h1.dist h2).div_const _

/-! ### Obligation O3 in the shell form clause 7b consumes -/

/-- **Clause 7b, gradient term.**  `‖∇g_k‖_{L^∞(K)}` as a function of the sample is
measurable for `shellLocalSigma k B` whenever `K ⊆ B` is a bounded box inside an
open `B`. -/
theorem measurable_boxDerivNorm_shellLocalSigma [NeZero d] (k : ℕ) {B K : Set (Vec d)}
    (hB : IsOpen B) (hKB : K ⊆ B) (hK : Bornology.IsBounded K) :
    @Measurable (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) ℝ
      (shellLocalSigma k B) _
      (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
        boxDerivNorm K (omega k)) :=
  (measurable_boxDerivNorm_localSigma hB hKB hK).comp
    (Measurable.of_comap_le (le_refl (shellLocalSigma k B)))

/-- **Clause 7b, Hessian term.** -/
theorem measurable_boxDerivLipschitzSeminorm_shellLocalSigma [NeZero d] (k : ℕ)
    {B K : Set (Vec d)} (hB : IsOpen B) (hKB : K ⊆ B) (hK : Bornology.IsBounded K) :
    @Measurable (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) ℝ
      (shellLocalSigma k B) _
      (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
        boxDerivLipschitzSeminorm K (omega k)) :=
  (measurable_boxDerivLipschitzSeminorm_localSigma hB hKB hK).comp
    (Measurable.of_comap_le (le_refl (shellLocalSigma k B)))

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
