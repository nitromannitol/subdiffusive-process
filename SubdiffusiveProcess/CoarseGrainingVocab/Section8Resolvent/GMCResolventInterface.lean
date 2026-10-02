import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.MassiveContraction
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FellerBridge
import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SmallContrastScalarBridge
import SubdiffusiveProcess.Assumptions.AnchoredCoefficient
import SubdiffusiveProcess.Assumptions.Cutoff




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open MarkovProcess MarkovProcess.Semigroup
open scoped ZeroAtInfty

noncomputable section

variable {d : ℕ}






theorem continuous_coefficientAt (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (L : WithTop ℕ) (ω : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d) :
    Continuous (coefficientAt M L ω) := by
  induction L using WithTop.recTopCoe with
  | top => exact SubdiffusiveProcess.Frozen.Assumptions.continuous_aAnchored M ω
  | coe n => exact SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M n ω.1



theorem coefficientAt_pos (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (L : WithTop ℕ) (ω : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d) (x : Vec d) :
    0 < coefficientAt M L ω x := by
  induction L using WithTop.recTopCoe with
  | top => exact SubdiffusiveProcess.Frozen.Assumptions.aAnchored_pos M ω x
  | coe n => exact SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M n ω.1 x



theorem exists_bounds_coefficientAt_of_isCompact
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : WithTop ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d)
    {K : Set (Vec d)} (hK : IsCompact K) :
    ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ K, lam ≤ coefficientAt M L ω x ∧ coefficientAt M L ω x ≤ Lam := by
  rcases K.eq_empty_or_nonempty with hempty | hne
  · exact ⟨1, 1, one_pos, by simp [hempty]⟩
  · obtain ⟨xmin, hxmin, hmin⟩ :=
      hK.exists_isMinOn hne (continuous_coefficientAt M L ω).continuousOn
    obtain ⟨xmax, hxmax, hmax⟩ :=
      hK.exists_isMaxOn hne (continuous_coefficientAt M L ω).continuousOn
    exact ⟨coefficientAt M L ω xmin, coefficientAt M L ω xmax,
      coefficientAt_pos M L ω xmin, fun x hx ↦ ⟨hmin hx, hmax hx⟩⟩



theorem isEllipticFieldOn_coefficientAt (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (L : WithTop ℕ) (ω : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d)
    {W : Set (Vec d)} (hW : MeasurableSet W) {lam Lam : ℝ} (hlam : 0 < lam)
    (hb : ∀ x ∈ W, lam ≤ coefficientAt M L ω x ∧ coefficientAt M L ω x ≤ Lam) :
    IsEllipticFieldOn lam Lam W (scalarCoeffField (coefficientAt M L ω)) :=
  Section6BoundedMultiplier.isEllipticFieldOn_scalarCoeffField_of_continuousOn
    hW (continuous_coefficientAt M L ω).continuousOn hlam hb






abbrev IsReversibleMassiveSolutionOn (a : Vec d → ℝ) (mu : ℝ) (W : Set (Vec d))
    (u : H1Function W) (f : Vec d → ℝ) : Prop :=
  IsMassiveWeakSolutionOn a a mu W u f



abbrev IsDivergenceMassiveSolutionOn (a : Vec d → ℝ) (mu : ℝ) (W : Set (Vec d))
    (u : H1Function W) (f : Vec d → ℝ) : Prop :=
  IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) mu W u f




/-- **Uniqueness for the reversible local resolvent.**  On a bounded measurable
set, the zero-boundary problem `μ a u - ∇·(a∇u) = a f` has at most one solution
with a given trace. -/
theorem ae_eq_of_isReversibleMassiveDirichletSolutionOn
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : WithTop ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d)
    {W : Set (Vec d)} (hW : MeasurableSet W) (hWb : Bornology.IsBounded W)
    {mu : ℝ} (hmu : 0 < mu)
    {u u' hD : H1Function W} {f : Vec d → ℝ}
    (hu : HasZeroTraceDifferenceOn W u hD ∧
      IsReversibleMassiveSolutionOn (coefficientAt M L ω) mu W u f)
    (hu' : HasZeroTraceDifferenceOn W u' hD ∧
      IsReversibleMassiveSolutionOn (coefficientAt M L ω) mu W u' f) :
    u.toFun =ᵐ[volume.restrict W] u'.toFun ∧
      u.grad =ᵐ[volume.restrict W] u'.grad := by
  obtain ⟨lam, Lam, hlam, hb⟩ :=
    exists_bounds_coefficientAt_of_isCompact M L ω hWb.isCompact_closure
  have hbW : ∀ x ∈ W, lam ≤ coefficientAt M L ω x ∧ coefficientAt M L ω x ≤ Lam :=
    fun x hx ↦ hb x (subset_closure hx)
  have hEll := isEllipticFieldOn_coefficientAt M L ω hW hlam hbW
  refine ae_eq_of_isMassiveDirichletSolutionOn (rhoMax := Lam) hW hmu hlam hEll hlam
    (fun x hx ↦ (hbW x hx).1)
    ((continuous_coefficientAt M L ω).aestronglyMeasurable)
    (fun x hx ↦ (hbW x hx).1) ?_ hu hu'
  filter_upwards [ae_restrict_mem hW] with x hx
  rw [abs_of_pos (coefficientAt_pos M L ω x)]
  exact (hbW x hx).2

/-- **Uniqueness for the divergence-form local resolvent.**  On a bounded
measurable set, the zero-boundary problem `μ u - ∇·(a∇u) = f` has at most one
solution with a given trace. -/
theorem ae_eq_of_isDivergenceMassiveDirichletSolutionOn
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : WithTop ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d)
    {W : Set (Vec d)} (hW : MeasurableSet W) (hWb : Bornology.IsBounded W)
    {mu : ℝ} (hmu : 0 < mu)
    {u u' hD : H1Function W} {f : Vec d → ℝ}
    (hu : HasZeroTraceDifferenceOn W u hD ∧
      IsDivergenceMassiveSolutionOn (coefficientAt M L ω) mu W u f)
    (hu' : HasZeroTraceDifferenceOn W u' hD ∧
      IsDivergenceMassiveSolutionOn (coefficientAt M L ω) mu W u' f) :
    u.toFun =ᵐ[volume.restrict W] u'.toFun ∧
      u.grad =ᵐ[volume.restrict W] u'.grad := by
  obtain ⟨lam, Lam, hlam, hb⟩ :=
    exists_bounds_coefficientAt_of_isCompact M L ω hWb.isCompact_closure
  have hbW : ∀ x ∈ W, lam ≤ coefficientAt M L ω x ∧ coefficientAt M L ω x ≤ Lam :=
    fun x hx ↦ hb x (subset_closure hx)
  have hEll := isEllipticFieldOn_coefficientAt M L ω hW hlam hbW
  refine ae_eq_of_isMassiveDirichletSolutionOn (rhoMax := 1) hW hmu one_pos hEll hlam
    (fun x hx ↦ (hbW x hx).1) aestronglyMeasurable_const (fun _ _ ↦ le_rfl) ?_ hu hu'
  exact Filter.Eventually.of_forall fun _ ↦ by norm_num

/-! ### The weak elliptic resolvent characterization -/



def IsWeakEllipticResolvent (c rho : Vec d → ℝ)
    (D : C0ResolventDatum (Vec d)) : Prop :=
  ∀ (mu : PositiveShift) (f : C₀(Vec d, ℝ)) (W : Set (Vec d)),
    IsOpenBoundedConvexDomain W →
      ∃ u : H1Function W,
        (∀ x ∈ W, u.toFun x = D.solution mu f x) ∧
          IsMassiveWeakSolutionOn c rho (mu : ℝ) W u (fun x ↦ f x)






theorem exists_gmcFellerSemigroup_of_resolvent
    (c rho : Vec d → ℝ) (D : C0ResolventDatum (Vec d))
    (hdense : ∀ mu, DenseRange (D.operator mu))
    (hchar : IsWeakEllipticResolvent c rho D) :
    ∃ P : SubMarkovKernelSemigroup (Vec d),
      P.IsFellerKernelSemigroup ∧
      (∀ (mu : PositiveShift) (f : C₀(Vec d, ℝ)) (x : Vec d),
        D.solution mu f x =
          ∫ t in Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
            kernelIntegral (P (Real.toNNReal t)) f x) ∧
      IsWeakEllipticResolvent c rho D :=
  ⟨D.fellerKernelSemigroup hdense,
    D.isFellerKernelSemigroup_fellerKernelSemigroup hdense,
    D.solution_eq_laplace hdense, hchar⟩



theorem exists_gmcReversibleFellerSemigroup_of_resolvent
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : WithTop ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d)
    (D : C0ResolventDatum (Vec d)) (hdense : ∀ mu, DenseRange (D.operator mu))
    (hchar : IsWeakEllipticResolvent (coefficientAt M L ω) (coefficientAt M L ω) D) :
    ∃ P : SubMarkovKernelSemigroup (Vec d),
      P.IsFellerKernelSemigroup ∧
      (∀ (mu : PositiveShift) (f : C₀(Vec d, ℝ)) (x : Vec d),
        D.solution mu f x =
          ∫ t in Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
            kernelIntegral (P (Real.toNNReal t)) f x) ∧
      IsWeakEllipticResolvent (coefficientAt M L ω) (coefficientAt M L ω) D :=
  exists_gmcFellerSemigroup_of_resolvent _ _ D hdense hchar



theorem exists_gmcDivergenceFellerSemigroup_of_resolvent
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : WithTop ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d)
    (D : C0ResolventDatum (Vec d)) (hdense : ∀ mu, DenseRange (D.operator mu))
    (hchar : IsWeakEllipticResolvent (coefficientAt M L ω) (fun _ ↦ (1 : ℝ)) D) :
    ∃ P : SubMarkovKernelSemigroup (Vec d),
      P.IsFellerKernelSemigroup ∧
      (∀ (mu : PositiveShift) (f : C₀(Vec d, ℝ)) (x : Vec d),
        D.solution mu f x =
          ∫ t in Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
            kernelIntegral (P (Real.toNNReal t)) f x) ∧
      IsWeakEllipticResolvent (coefficientAt M L ω) (fun _ ↦ (1 : ℝ)) D :=
  exists_gmcFellerSemigroup_of_resolvent _ _ D hdense hchar

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
