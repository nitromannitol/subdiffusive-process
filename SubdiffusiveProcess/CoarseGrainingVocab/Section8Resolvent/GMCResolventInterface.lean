module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.MassiveContraction
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FellerBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SmallContrastScalarBridge
public import SubdiffusiveProcess.Assumptions.AnchoredCoefficient
public import SubdiffusiveProcess.Assumptions.Cutoff

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open MarkovProcess MarkovProcess.Semigroup
open scoped ZeroAtInfty

noncomputable section

variable {d : ℕ}

/-! ### Regularity and local ellipticity of the multiscale coefficient -/

/-- The multiscale coefficient is continuous, uniformly in the cutoff index,
including at the uncut field `L = ⊤`. -/
theorem continuous_coefficientAt (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (L : WithTop ℕ) (ω : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d) :
    Continuous (coefficientAt M L ω) := by
  induction L using WithTop.recTopCoe with
  | top => exact _root_.SubdiffusiveProcess.Model.continuous_aAnchored M ω
  | coe n => exact _root_.SubdiffusiveProcess.Model.continuous_aCutoff M n ω.1

/-- The multiscale coefficient is positive, uniformly in the cutoff index,
including at the uncut field `L = ⊤`. -/
theorem coefficientAt_pos (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (L : WithTop ℕ) (ω : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d) (x : Vec d) :
    0 < coefficientAt M L ω x := by
  induction L using WithTop.recTopCoe with
  | top => exact _root_.SubdiffusiveProcess.Model.aAnchored_pos M ω x
  | coe n => exact _root_.SubdiffusiveProcess.Model.aCutoff_pos M n ω.1 x

/-- **Local ellipticity of the multiscale coefficient.**  On every compact set the
coefficient is bounded above and below by positive constants.  No uniformity in
the set is claimed and none is available: `a` is only locally elliptic, which is
why the paper's Section 8 works with the coarse ellipticity ratios of the large-cube ellipticity
moment estimate (`s.fixed.coefficient` and `mfd:sec-speed`) rather than
with a global constant. -/
theorem exists_bounds_coefficientAt_of_isCompact
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : WithTop ℕ)
    (ω : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d)
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

/-- The multiscale coefficient, read as an elliptic matrix field on a measurable
set on which two-sided bounds are known. -/
theorem isEllipticFieldOn_coefficientAt (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (L : WithTop ℕ) (ω : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d)
    {W : Set (Vec d)} (hW : MeasurableSet W) {lam Lam : ℝ} (hlam : 0 < lam)
    (hb : ∀ x ∈ W, lam ≤ coefficientAt M L ω x ∧ coefficientAt M L ω x ≤ Lam) :
    IsEllipticFieldOn lam Lam W (scalarCoeffField (coefficientAt M L ω)) :=
  Section6BoundedMultiplier.isEllipticFieldOn_scalarCoeffField_of_continuousOn
    hW (continuous_coefficientAt M L ω).continuousOn hlam hb

/-! ### The two pairs of `s.fixed.coefficient` and `mfd:sec-speed` -/

/-- The reversible local resolvent equation: the pair `(c, ρ) = (a, a)`, whose
generator is `a⁻¹ ∇·(a∇)` (`s.fixed.coefficient` and `mfd:sec-speed`). -/
abbrev IsReversibleMassiveSolutionOn (a : Vec d → ℝ) (mu : ℝ) (W : Set (Vec d))
    (u : H1Function W) (f : Vec d → ℝ) : Prop :=
  IsMassiveWeakSolutionOn a a mu W u f

/-- The divergence-form local resolvent equation: the pair `(c, ρ) = (a, 1)`,
whose generator is `∇·(a∇)` (`s.fixed.coefficient` and `mfd:sec-speed`). -/
abbrev IsDivergenceMassiveSolutionOn (a : Vec d → ℝ) (mu : ℝ) (W : Set (Vec d))
    (u : H1Function W) (f : Vec d → ℝ) : Prop :=
  IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) mu W u f

/-! ### Uniqueness of the local resolvent for the multiscale coefficient -/

/-- **Uniqueness for the reversible local resolvent.**  On a bounded measurable
set, the zero-boundary problem `μ a u - ∇·(a∇u) = a f` has at most one solution
with a given trace. -/
theorem ae_eq_of_isReversibleMassiveDirichletSolutionOn
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : WithTop ℕ)
    (ω : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d)
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
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : WithTop ℕ)
    (ω : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d)
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

/-- **The Section 8 export required by the Section 7.**  A `C₀` resolvent
datum is a *weak elliptic resolvent* for the pair `(c, ρ)` when, on every
bounded open convex domain, the function `R_μ f` has an `H¹` representative
solving the massive equation `μ ρ u - ∇·(c∇u) = ρ f` weakly.

Locality is intrinsic here, not a weakening: for the GMC coefficient the global
energy `∫_{ℝ^d} c |∇ R_μ f|²` need not be finite, since `c` is only locally
elliptic (`exists_bounds_coefficientAt_of_isCompact`).  The paper's own Section 8
whole-space statements are likewise localized
(`s.fixed.coefficient` and `mfd:sec-speed`). -/
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
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : WithTop ℕ)
    (ω : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d)
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
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : WithTop ℕ)
    (ω : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d)
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
