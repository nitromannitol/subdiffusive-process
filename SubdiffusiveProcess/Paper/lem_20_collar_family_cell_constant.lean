module

public import SubdiffusiveProcess.Paper.mesh_interpolator
public import SubdiffusiveProcess.Paper.cell_boundary_continuity
public import SubdiffusiveProcess.VariationalResponses.CellDirichlet
public import SubdiffusiveProcess.CoarseGrainingVocab.DirichletUniqueness
public import SubdiffusiveProcess.CutoffsCellPlateau

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace Metric
open SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Constant-cell harmonic uniqueness in the collar gluing argument.

Tick list:
- The standing dimension hypothesis `2 ≤ d` is carried from the global
  convention of the manuscript; it supplies the nonzero-dimensional
  setting used by the cell uniqueness argument.
- `W`, `a`, `u`, and the constant datum `theta` are concrete cell-level
  carriers, not abstract conclusion fields.
- `hEll`, `hharm`, and `htrace` are the ellipticity, harmonicity, and
  matching-trace inputs used by the cell Dirichlet uniqueness argument.
- `mesh_interpolator` supplies the cellwise harmonic interpolation and
  `cell_boundary_continuity` supplies its continuous boundary representative.
- CONCLUDED: the cellwise almost-everywhere constant value and vanishing
  weak gradient.
This is a proof-step fine child of `lem_20_collar_family`.
-/
theorem lem_20_collar_family_cell_constant
    (d : ℕ) (hd : 2 ≤ d) (W : Opens (SpatialCoordinates d))
    (hW : IsOpenBoundedConvexDomain (W : Set (SpatialCoordinates d)))
    (hne : (W : Set (SpatialCoordinates d)).Nonempty)
    (a : SpatialCoordinates d → ℝ) (lam Lam : ℝ)
    (hEll : IsEllipticFieldOn lam Lam (W : Set (SpatialCoordinates d))
      (scalarCoeffField a))
    (theta u : H1Function (W : Set (SpatialCoordinates d))) (c : ℝ)
    (hconst : ∀ x ∈ (W : Set (SpatialCoordinates d)), theta.toFun x = c)
    (hharm : IsWeaklyHarmonicOn a (W : Set (SpatialCoordinates d)) u)
    (htrace : HasZeroTraceDifferenceOn (W : Set (SpatialCoordinates d)) u theta) :
    ∀ᵐ x ∂(volume.restrict (W : Set (SpatialCoordinates d))),
      u.toFun x = c ∧ ∀ i : Fin d, u.grad x i = 0 := by
  have : NeZero d := ⟨by omega⟩
  have : IsFiniteMeasure (volumeMeasureOn (W : Set (SpatialCoordinates d))) :=
    hW.isFiniteMeasure_restrict_volume
  let thetaConst : H1Function (W : Set (SpatialCoordinates d)) :=
    H1Function.const c
  have htheta_ae : theta.toFun =ᵐ[volume.restrict (W : Set (SpatialCoordinates d))]
      thetaConst.toFun := by
    filter_upwards [ae_restrict_mem hW.isOpen.measurableSet] with x hx
    exact (hconst x hx).trans (H1Function.const_apply c x).symm
  have htheta_grad : theta.grad =ᵐ[volume.restrict (W : Set (SpatialCoordinates d))]
      (fun _ => (0 : SpatialCoordinates d)) := by
    have hgrad := SubdiffusiveProcess.lane2_grad_ae_eq_of_ae_eq'
      hW.isOpen hW.isBoundedDomain.isBounded theta thetaConst htheta_ae
    simpa [thetaConst] using! hgrad
  have hzero : IsWeaklyHarmonicOn a (W : Set (SpatialCoordinates d))
      (0 : H1Function (W : Set (SpatialCoordinates d))) := by
    intro φ
    simp [Homogenization.vecDot_zero_left]
  have htheta_harm : IsWeaklyHarmonicOn a (W : Set (SpatialCoordinates d)) theta := by
    exact SubdiffusiveProcess.lane2_isWeaklyHarmonicOn_congr_ae
      hW.isOpen.measurableSet htheta_grad.symm hzero
  have htheta_trace : HasZeroTraceDifferenceOn
      (W : Set (SpatialCoordinates d)) theta theta := by
    refine ⟨0, ?_, ?_⟩
    · intro x
      change theta.toFun x = theta.toFun x + 0
      ring
    · intro x
      change theta.grad x = theta.grad x + 0
      simp
  have huniq :=
    SubdiffusiveProcess.CoarseGrainingVocab.ae_eq_of_isWeaklyHarmonicOn_of_hasZeroTraceDifferenceOn
      hW hne hEll hharm htrace htheta_harm htheta_trace
  filter_upwards [huniq.1, huniq.2, htheta_grad,
    ae_restrict_mem hW.isOpen.measurableSet] with x hvalue hgrad hzero' hx
  constructor
  · exact hvalue.trans (hconst x hx)
  · intro i
    rw [hgrad, hzero']
    rfl

/-- The datum has no value strictly between zero and one on the cell closure. -/
def aux_cutoffs_noMiddleOnClosure (d : ℕ) (theta : SpatialCoordinates d → ℝ)
    (W : Set (SpatialCoordinates d)) : Prop :=
  ¬∃ x ∈ closure W, 0 < theta x ∧ theta x < 1

/-- Express the no-middle condition as an empty intersection. -/
theorem aux_cutoffs_noMiddleOnClosure_iff_empty_inter (d : ℕ)
    {θ : SpatialCoordinates d → ℝ} {W : Set (SpatialCoordinates d)} :
    aux_cutoffs_noMiddleOnClosure d θ W ↔
      (closure W ∩ {x | 0 < θ x ∧ θ x < 1}) = ∅ := by
  constructor
  · intro h
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    intro x hx
    rcases hx with ⟨hx_cl, hx_mid⟩
    exact h ⟨x, hx_cl, hx_mid⟩
  · intro h h_ex
    rcases h_ex with ⟨x, hx_cl, hx_mid⟩
    have hx_inter : x ∈ closure W ∩ {x | 0 < θ x ∧ θ x < 1} := ⟨hx_cl, hx_mid⟩
    rw [h] at hx_inter
    exact Set.notMem_empty x hx_inter

/-- A harmonic cell with plateau boundary data has vanishing weak gradient. -/
theorem aux_cutoffs_plateau_gradient_zero
    (d : ℕ) (hd : 2 ≤ d) (W : Opens (SpatialCoordinates d))
    (hW : IsOpenBoundedConvexDomain (W : Set (SpatialCoordinates d)))
    (hne : (W : Set (SpatialCoordinates d)).Nonempty)
    (a : SpatialCoordinates d → ℝ) (lam Lam : ℝ)
    (hEll : IsEllipticFieldOn lam Lam (W : Set (SpatialCoordinates d))
      (scalarCoeffField a))
    (theta u : H1Function (W : Set (SpatialCoordinates d)))
    (htrace : HasZeroTraceDifferenceOn (W : Set (SpatialCoordinates d)) u theta)
    (hharm : IsWeaklyHarmonicOn a (W : Set (SpatialCoordinates d)) u)
    (h_cont : ContinuousOn theta.toFun (closure (W : Set (SpatialCoordinates d))))
    (h_range : ∀ x ∈ closure (W : Set (SpatialCoordinates d)),
      0 ≤ theta.toFun x ∧ theta.toFun x ≤ 1)
    (h_preconn : IsPreconnected (closure (W : Set (SpatialCoordinates d))))
    (h_no_mid : aux_cutoffs_noMiddleOnClosure d theta.toFun
      (W : Set (SpatialCoordinates d))) :
    ∀ i : Fin d, ∀ᵐ x ∂(volume.restrict (W : Set (SpatialCoordinates d))),
      u.grad x i = 0 := by
  have h_no_mid' : ¬∃ x ∈ closure (W : Set (SpatialCoordinates d)),
      0 < theta.toFun x ∧ theta.toFun x < 1 := h_no_mid
  have h_plateau := aux_cutoffs_plateau_constant_on_preconnected
    h_preconn h_cont h_range h_no_mid'
  rcases h_plateau with (h_all_zero | h_all_one)
  · have h_const : ∀ x ∈ (W : Set (SpatialCoordinates d)),
        theta.toFun x = (0 : ℝ) := by
      intro x hx
      exact h_all_zero x (subset_closure hx)
    have h_lemma := lem_20_collar_family_cell_constant
      d hd W hW hne a lam Lam hEll theta u (0 : ℝ) h_const hharm htrace
    intro i
    filter_upwards [h_lemma] with x hx
    exact hx.2 i
  · have h_const : ∀ x ∈ (W : Set (SpatialCoordinates d)),
        theta.toFun x = (1 : ℝ) := by
      intro x hx
      exact h_all_one x (subset_closure hx)
    have h_lemma := lem_20_collar_family_cell_constant
      d hd W hW hne a lam Lam hEll theta u (1 : ℝ) h_const hharm htrace
    intro i
    filter_upwards [h_lemma] with x hx
    exact hx.2 i

/-- The plateau conclusion specialized to odd grid cells. -/
theorem aux_cutoffs_plateau_gradient_zero_oddGridCell
    (d : ℕ) (hd : 2 ≤ d) {z : SpatialCoordinates d} {r : ℝ} (hr : 0 < r)
    (m : ℕ) (k : OddGridIndex d m)
    (a : SpatialCoordinates d → ℝ) (lam Lam : ℝ)
    (hEll : IsEllipticFieldOn lam Lam
      (oddGridCell z r hr m k : Set (SpatialCoordinates d)) (scalarCoeffField a))
    (theta u : H1Function (oddGridCell z r hr m k : Set (SpatialCoordinates d)))
    (htrace : HasZeroTraceDifferenceOn
      (oddGridCell z r hr m k : Set (SpatialCoordinates d)) u theta)
    (hharm : IsWeaklyHarmonicOn a
      (oddGridCell z r hr m k : Set (SpatialCoordinates d)) u)
    (h_cont : ContinuousOn theta.toFun
      (closure (oddGridCell z r hr m k : Set (SpatialCoordinates d))))
    (h_range : ∀ x ∈ closure (oddGridCell z r hr m k : Set (SpatialCoordinates d)),
      0 ≤ theta.toFun x ∧ theta.toFun x ≤ 1)
    (h_no_mid : aux_cutoffs_noMiddleOnClosure d theta.toFun
      (oddGridCell z r hr m k : Set (SpatialCoordinates d))) :
    ∀ i : Fin d, ∀ᵐ x ∂(volume.restrict
      (oddGridCell z r hr m k : Set (SpatialCoordinates d))),
      u.grad x i = 0 := by
  have h_preconn : IsPreconnected
      (closure (oddGridCell z r hr m k : Set (SpatialCoordinates d))) :=
    aux_cutoffs_oddGridCell_closure_isPreconnected hr m k
  have hne : (oddGridCell z r hr m k : Set (SpatialCoordinates d)).Nonempty := by
    refine ⟨oddGridCenter z r m k, ?_⟩
    exact Metric.mem_ball_self (half_pos (div_pos hr (by positivity)))
  have hW : IsOpenBoundedConvexDomain
      (oddGridCell z r hr m k : Set (SpatialCoordinates d)) :=
    lane2_isOpenBoundedConvexDomain_centeredCube (oddGridCenter z r m k)
      (div_pos hr (by positivity))
  exact aux_cutoffs_plateau_gradient_zero
    d hd (oddGridCell z r hr m k) hW hne a lam Lam hEll theta u htrace hharm
    h_cont h_range h_preconn h_no_mid

end SubdiffusiveProcess.Paper
