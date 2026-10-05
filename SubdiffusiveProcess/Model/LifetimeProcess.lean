module

public import Mathlib
public import MarkovProcess.Main
public import MarkovProcess.Trajectory.StoppingLtTop
public import MarkovProcess.Lifetime.CountablySeparated
public import MarkovProcess.Path.Polish
public import MarkovProcess.Examples.Identity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

@[expose] public section




set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.Model.LifetimeProcess

/-! ### The Borel structure of a sum -/

/-- The disjoint-sum measurable structure of two Borel spaces is the Borel structure of the sum
topology.  Mathlib has no instance for this, and it is what makes
`MarkovProcess.LifetimePath.measurableEmbedding_ofContinuousPath` applicable to the cemetery
extension `Cemetery alpha = alpha ⊕ Unit`. -/
theorem borelSpace_sum {α β : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] [Nonempty α] [Nonempty β] :
    BorelSpace (α ⊕ β) := by
  constructor
  apply le_antisymm
  · intro s hs
    rw [measurableSet_sum_iff] at hs
    obtain ⟨hl, hr⟩ := hs
    classical
    set L : α ⊕ β → α := Sum.elim id (fun _ => (Classical.arbitrary α)) with hL
    set R : α ⊕ β → β := Sum.elim (fun _ => (Classical.arbitrary β)) id with hR
    have hLc : Continuous L := Continuous.sumElim continuous_id continuous_const
    have hRc : Continuous R := Continuous.sumElim continuous_const continuous_id
    have hsplit : s = (L ⁻¹' (Sum.inl ⁻¹' s) ∩ Set.range (Sum.inl : α → α ⊕ β)) ∪
        (R ⁻¹' (Sum.inr ⁻¹' s) ∩ Set.range (Sum.inr : β → α ⊕ β)) := by
      ext x
      cases x with
      | inl a => simp [hL, hR]
      | inr b => simp [hL, hR]
    rw [hsplit]
    refine MeasurableSet.union (MeasurableSet.inter ?_ ?_) (MeasurableSet.inter ?_ ?_)
    · exact (hLc.borel_measurable) (by rwa [← BorelSpace.measurable_eq])
    · exact MeasurableSpace.measurableSet_generateFrom
        (isOpen_range_inl : IsOpen (Set.range (Sum.inl : α → α ⊕ β)))
    · exact (hRc.borel_measurable) (by rwa [← BorelSpace.measurable_eq])
    · exact MeasurableSpace.measurableSet_generateFrom
        (isOpen_range_inr : IsOpen (Set.range (Sum.inr : β → α ⊕ β)))
  · apply MeasurableSpace.generateFrom_le
    intro u hu
    rw [measurableSet_sum_iff]
    exact ⟨(hu.preimage continuous_inl).measurableSet, (hu.preimage continuous_inr).measurableSet⟩

variable {d : ℕ}

/-- The cemetery extension of `Vec d` carries the Borel structure of its sum topology.  Scoped:
it is switched on only inside this namespace, where the standard-Borel hypotheses of the
`LifetimePath` API are needed. -/
scoped instance instBorelSpaceCemetery : BorelSpace (Cemetery (Vec d)) := borelSpace_sum

/-! ### `ofContinuousPath` against the Section 9 vocabulary -/

/-- Shifting commutes with the infinite-lifetime embedding. -/
theorem shift_ofContinuousPath (S : NNReal) (w : ContinuousPath (Vec d)) :
    LifetimePath.shift S (LifetimePath.ofContinuousPath w)
      = LifetimePath.ofContinuousPath (ContinuousPath.shift S w) := by
  refine LifetimePath.ext_coordinate ?_ ?_
  · simp
  · intro t
    simp
    rfl

/-- The Section 9 `position` of an infinite-lifetime path is the value of the continuous path. -/
theorem position_ofContinuousPath (t : NNReal) (w : ContinuousPath (Vec d)) :
    position t (LifetimePath.ofContinuousPath w) = w t := by
  rw [position, LifetimePath.coordinate_ofContinuousPath]
  rfl

/-- The infinite-lifetime embedding is measurable from the continuous-path canonical filtration
to the lifetime-path canonical filtration, at every time. -/
theorem measurable_ofContinuousPath_canonicalFiltration (t : NNReal) :
    Measurable[ContinuousPath.canonicalFiltration (alpha := Vec d) t,
      LifetimePath.canonicalFiltration (alpha := Vec d) t]
      (LifetimePath.ofContinuousPath (α := Vec d)) := by
  apply Measurable.of_comap_le
  rw [LifetimePath.canonicalFiltration, MeasurableSpace.comap_iSup]
  refine iSup_le fun s => ?_
  rw [MeasurableSpace.comap_comp]
  have hfun : LifetimePath.coordinate (α := Vec d) (s : NNReal) ∘ LifetimePath.ofContinuousPath
      = Cemetery.alive ∘ ContinuousPath.coordinateProcess (alpha := Vec d) (s : NNReal) := by
    funext w
    exact LifetimePath.coordinate_ofContinuousPath w (s : NNReal)
  rw [hfun, ← MeasurableSpace.comap_comp]
  refine le_trans (MeasurableSpace.comap_mono (measurable_inl (α := Vec d) (β := Unit)).comap_le) ?_
  exact le_iSup_of_le (⟨(s : NNReal), s.2⟩ : Set.Iic t) le_rfl

/-- A stopping time of the lifetime-path filtration pulls back to a stopping time of the
continuous-path filtration. -/
theorem isStoppingTime_comp_ofContinuousPath {T : Path d → ENNReal}
    (hT : IsStoppingTime LifetimePath.canonicalFiltration T) :
    IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun w => T (LifetimePath.ofContinuousPath w)) :=
  fun t => measurable_ofContinuousPath_canonicalFiltration t (hT t)

/-- Events of the stopped sigma-algebra pull back to events of the stopped sigma-algebra. -/
theorem measurableSet_preimage_stopped {T : Path d → ENNReal}
    (hT : IsStoppingTime LifetimePath.canonicalFiltration T)
    {B : Set (Path d)} (hB : MeasurableSet[hT.measurableSpace] B) :
    MeasurableSet[(isStoppingTime_comp_ofContinuousPath hT).measurableSpace]
      (LifetimePath.ofContinuousPath ⁻¹' B) := by
  have hembSup : Measurable[
      (⨆ t, ContinuousPath.canonicalFiltration (alpha := Vec d) t),
      (⨆ t, LifetimePath.canonicalFiltration (alpha := Vec d) t)]
      (LifetimePath.ofContinuousPath (α := Vec d)) := by
    apply Measurable.of_comap_le
    rw [MeasurableSpace.comap_iSup]
    refine iSup_le fun t => ?_
    exact (measurable_ofContinuousPath_canonicalFiltration t).comap_le.trans (le_iSup _ t)
  refine ⟨hembSup hB.1, fun t => ?_⟩
  exact measurable_ofContinuousPath_canonicalFiltration t (hB.2 t)

/-! ### The lifetime-path process -/

open SubMarkovKernelSemigroup

variable (P : SubMarkovKernelSemigroup (Vec d)) (hP : P.IsConservative)

/-- **The lifetime-path process of a conservative sub-Markov kernel semigroup on `Vec d`**: the
continuous-path process of `MarkovProcess.Main`, pushed forward to the formalization's carrier
`Path d = LifetimePath (Vec d)` by the infinite-lifetime embedding. -/
def lifetimeProcess : Kernel (Vec d) (Path d) :=
  Kernel.map (IsConservative.continuousProcess P hP) LifetimePath.ofContinuousPath

theorem lifetimeProcess_apply (x : Vec d) :
    lifetimeProcess P hP x =
      ((IsConservative.continuousProcess P hP) x).map LifetimePath.ofContinuousPath :=
  Kernel.map_apply _ LifetimePath.measurable_ofContinuousPath x

/-- The first conjunct of `StrongMarkov`: the process is a probability kernel. -/
theorem lifetimeProcess_univ (x : Vec d) : lifetimeProcess P hP x univ = 1 := by
  rw [lifetimeProcess_apply,
    Measure.map_apply LifetimePath.measurable_ofContinuousPath MeasurableSet.univ,
    Set.preimage_univ]
  exact measure_univ

/-- The second conjunct of `StrongMarkov`: the process starts where it is told. -/
theorem lifetimeProcess_start (hK : P.KolmogorovRegular hP) (x : Vec d) :
    ∀ᵐ w ∂(lifetimeProcess P hP x), LifetimePath.coordinate 0 w = Cemetery.alive x := by
  classical
  set mu := IsConservative.continuousProcess P hP x with hmu
  have heval : Measurable (fun w : ContinuousPath (Vec d) => w (0 : NNReal)) :=
    ContinuousPath.measurable_coordinateProcess (alpha := Vec d) 0
  have hmap : mu.map (fun w : ContinuousPath (Vec d) => w (0 : NNReal)) = Measure.dirac x := by
    rw [hmu, ← Kernel.map_apply _ heval,
      IsConservative.continuousProcess_map_eval_zero P hP hK]
    rfl
  rw [ae_iff, lifetimeProcess_apply]
  have hAc : MeasurableSet
      {w : Path d | ¬ LifetimePath.coordinate 0 w = Cemetery.alive x} := by
    have hsing : MeasurableSet ({Cemetery.alive x}ᶜ : Set (Cemetery (Vec d))) :=
      (measurableSet_singleton _).compl
    exact (LifetimePath.measurable_coordinate (α := Vec d) 0) hsing
  rw [Measure.map_apply LifetimePath.measurable_ofContinuousPath hAc]
  have hpre : LifetimePath.ofContinuousPath ⁻¹'
      {w : Path d | ¬ LifetimePath.coordinate 0 w = Cemetery.alive x}
      = (fun w : ContinuousPath (Vec d) => w (0 : NNReal)) ⁻¹' ({x}ᶜ) := by
    ext w
    simp
  rw [hpre, ← Measure.map_apply heval (measurableSet_singleton x).compl, hmap,
    Measure.dirac_apply' x (measurableSet_singleton x).compl]
  simp

/-- Change of variables along the infinite-lifetime embedding, for the whole space. -/
theorem lintegral_lifetimeProcess (y : Vec d) (F : Path d → ENNReal) :
    ∫⁻ v, F v ∂(lifetimeProcess P hP y)
      = ∫⁻ w, F (LifetimePath.ofContinuousPath w) ∂(IsConservative.continuousProcess P hP y) := by
  rw [lifetimeProcess_apply,
    (LifetimePath.measurableEmbedding_ofContinuousPath (α := Vec d)).lintegral_map]

/-- Change of variables along the infinite-lifetime embedding, on a measurable set.  No
measurability of `F` is required: `ofContinuousPath` is a measurable embedding. -/
theorem lintegral_lifetimeProcess_restrict (x : Vec d) {A : Set (Path d)} (hA : MeasurableSet A)
    (F : Path d → ENNReal) :
    ∫⁻ w in A, F w ∂(lifetimeProcess P hP x)
      = ∫⁻ w in LifetimePath.ofContinuousPath ⁻¹' A, F (LifetimePath.ofContinuousPath w)
          ∂(IsConservative.continuousProcess P hP x) := by
  rw [lifetimeProcess_apply, Measure.restrict_map LifetimePath.measurable_ofContinuousPath hA,
    (LifetimePath.measurableEmbedding_ofContinuousPath (α := Vec d)).lintegral_map]

/-- **The third conjunct of `StrongMarkov`** for the lifetime-path process: the map-form strong
Markov identity at an `ENNReal`-valued stopping time of `LifetimePath.canonicalFiltration`,
restricted to the event that the time is strictly before the lifetime. -/
theorem lifetimeProcess_strongMarkov_shift
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (x : Vec d) (T : Path d → ENNReal)
    (hT : IsStoppingTime LifetimePath.canonicalFiltration T)
    (B : Set (Path d)) (hB : MeasurableSet[hT.measurableSpace] B)
    (g : Path d → ENNReal) (hg : Measurable g) :
    (∫⁻ w in B ∩ {w | T w < w.lifetime},
        g (LifetimePath.shift (T w).toNNReal w) ∂(lifetimeProcess P hP x)) =
      ∫⁻ w in B ∩ {w | T w < w.lifetime},
        (∫⁻ v, g v ∂(lifetimeProcess P hP (position (T w).toNNReal w)))
          ∂(lifetimeProcess P hP x) := by
  classical
  set mu := IsConservative.continuousProcess P hP x with hmu
  set tau : ContinuousPath (Vec d) → WithTop NNReal :=
    fun w => T (LifetimePath.ofContinuousPath w) with htaudef
  have htau : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := Vec d)) tau :=
    isStoppingTime_comp_ofContinuousPath hT
  have hBmeas : MeasurableSet[htau.measurableSpace] (LifetimePath.ofContinuousPath ⁻¹' B) :=
    measurableSet_preimage_stopped hT hB
  have hAmeas : MeasurableSet (B ∩ {w : Path d | T w < w.lifetime}) := by
    refine (hT.measurableSpace_le B hB).inter ?_
    have hlifetime : Measurable (fun w : Path d => (w.lifetime : WithTop NNReal)) := by
      simpa only using! LifetimePath.measurable_lifetime (α := Vec d)
    simpa only using! measurableSet_lt hT.measurable' hlifetime
  have hpre : LifetimePath.ofContinuousPath ⁻¹' (B ∩ {w : Path d | T w < w.lifetime})
      = (LifetimePath.ofContinuousPath ⁻¹' B) ∩ {w | tau w < ⊤} := by
    ext w
    change (LifetimePath.ofContinuousPath w ∈ B ∧
      T (LifetimePath.ofContinuousPath w) < (⊤ : ENNReal)) ↔
      (LifetimePath.ofContinuousPath w ∈ B ∧ tau w < (⊤ : WithTop NNReal))
    rfl
  have hgof : Measurable (fun w : ContinuousPath (Vec d) => g (LifetimePath.ofContinuousPath w)) :=
    hg.comp LifetimePath.measurable_ofContinuousPath
  have hL : (∫⁻ w in B ∩ {w | T w < w.lifetime},
        g (LifetimePath.shift (T w).toNNReal w) ∂(lifetimeProcess P hP x))
      = ∫⁻ w in (LifetimePath.ofContinuousPath ⁻¹' B) ∩ {w | tau w < ⊤},
          g (LifetimePath.ofContinuousPath
            (ContinuousPath.shift ((tau w).untopD 0) w)) ∂mu := by
    rw [lintegral_lifetimeProcess_restrict P hP x hAmeas, hpre]
    refine lintegral_congr fun w => ?_
    rw [shift_ofContinuousPath]
    rfl
  have hLmap : (∫⁻ w in (LifetimePath.ofContinuousPath ⁻¹' B) ∩ {w | tau w < ⊤},
          g (LifetimePath.ofContinuousPath
            (ContinuousPath.shift ((tau w).untopD 0) w)) ∂mu)
      = ∫⁻ eta, g (LifetimePath.ofContinuousPath eta)
          ∂((mu.restrict ((LifetimePath.ofContinuousPath ⁻¹' B) ∩ {w | tau w < ⊤})).map
            (fun w => ContinuousPath.shift ((tau w).untopD 0) w)) := by
    rw [lintegral_map hgof (ContinuousPath.measurable_shift_untopD_stoppingTime tau htau)]
  have hSM := hFeller.continuousProcess_restrict_map_shift_stoppingTime_lt_top P hP hK x tau htau
    (LifetimePath.ofContinuousPath ⁻¹' B) hBmeas
  have hbind : (∫⁻ eta, g (LifetimePath.ofContinuousPath eta)
          ∂((mu.restrict ((LifetimePath.ofContinuousPath ⁻¹' B) ∩ {w | tau w < ⊤})).map
            (fun w => ContinuousPath.shift ((tau w).untopD 0) w)))
      = ∫⁻ w in (LifetimePath.ofContinuousPath ⁻¹' B) ∩ {w | tau w < ⊤},
          (∫⁻ eta, g (LifetimePath.ofContinuousPath eta)
            ∂(IsConservative.continuousProcess P hP (w ((tau w).untopD 0)))) ∂mu := by
    rw [hmu, hSM, Measure.lintegral_bind (Kernel.measurable _).aemeasurable hgof.aemeasurable]
    rfl
  have hR : (∫⁻ w in B ∩ {w | T w < w.lifetime},
        (∫⁻ v, g v ∂(lifetimeProcess P hP (position (T w).toNNReal w)))
          ∂(lifetimeProcess P hP x))
      = ∫⁻ w in (LifetimePath.ofContinuousPath ⁻¹' B) ∩ {w | tau w < ⊤},
          (∫⁻ eta, g (LifetimePath.ofContinuousPath eta)
            ∂(IsConservative.continuousProcess P hP (w ((tau w).untopD 0)))) ∂mu := by
    rw [lintegral_lifetimeProcess_restrict P hP x hAmeas, hpre]
    refine lintegral_congr fun w => ?_
    rw [position_ofContinuousPath, lintegral_lifetimeProcess]
    rfl
  rw [hL, hLmap, hbind, hR]

/-- **The lifetime-path process of a conservative Feller Kolmogorov-regular semigroup on `Vec d`
satisfies the formalization's `StrongMarkov` predicate.** -/
theorem strongMarkov_lifetimeProcess
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP) :
    StrongMarkov (lifetimeProcess P hP) :=
  ⟨lifetimeProcess_univ P hP, lifetimeProcess_start P hP hK,
    fun x T hT B hB g hg =>
      lifetimeProcess_strongMarkov_shift P hP hFeller hK x T hT B hB g hg⟩

/-! ### Inhabitedness -/

/-- **`StrongMarkov` is inhabited in every dimension.**  The witness is the lifetime-path process
of `MarkovProcess.idSemigroup`, i.e. the law of the constant path.

This retires the *vacuity* question for the first conjunct of `LocalDiffusion` only.  The
constant process does not satisfy `LocalDiffusion`'s resolvent clause for any elliptic
coefficient: its killed resolvent on `U` is `f` itself, which solves
`s⁻¹ ρ u - ∇·(c∇u) = s⁻¹ ρ f` only when `∫_U c ∇f · ∇φ = 0` for all `φ ∈ H¹₀(U)`, and
`CoefficientOn` forces `c` to be bounded below by a positive constant. -/
theorem exists_strongMarkov (d : ℕ) : ∃ law : Kernel (Vec d) (Path d), StrongMarkov law :=
  ⟨lifetimeProcess idSemigroup isConservative_idSemigroup,
    strongMarkov_lifetimeProcess _ _ isFellerKernelSemigroup_idSemigroup
      kolmogorovRegular_idSemigroup⟩

/-- Every positive constant is a `CoefficientOn` datum on every set: the second conjunct of
`LocalDiffusion` holds for constant coefficients, for every `law`. -/
theorem coefficientOn_const {a : ℝ} (ha : 0 < a) (U : Set (Vec d)) :
    CoefficientOn U (fun _ => a) := by
  refine ⟨aestronglyMeasurable_const, a, a, ha, ?_⟩
  filter_upwards with x
  exact ⟨le_rfl, le_rfl⟩

/-- The constant coefficient `1` is a `CoefficientOn` datum on every set. -/
theorem coefficientOn_one (U : Set (Vec d)) : CoefficientOn U (fun _ => (1 : ℝ)) :=
  coefficientOn_const one_pos U

/-- The first two conjuncts of `LocalDiffusion 1 1` are jointly satisfiable in every dimension.
Only the resolvent clause remains; see the module docstring. -/
theorem exists_strongMarkov_and_coefficientOn (d : ℕ) :
    ∃ law : Kernel (Vec d) (Path d), StrongMarkov law ∧
      ∀ K : Set (Vec d), IsCompact K →
        CoefficientOn K (fun _ => (1 : ℝ)) ∧ CoefficientOn K (fun _ => (1 : ℝ)) := by
  obtain ⟨law, hlaw⟩ := exists_strongMarkov d
  exact ⟨law, hlaw, fun K _ => ⟨coefficientOn_one K, coefficientOn_one K⟩⟩

end SubdiffusiveProcess.Model.LifetimeProcess
