import SubdiffusiveProcess.CoarseGrainingVocab.DirichletScalarForcing
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.CoefficientSigma

/-!
# Ellipticity and well-posedness for the literal rescaled cutoff coefficient
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

theorem continuous_rescaledCutoffCoefficient
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L N : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    Continuous (rescaledCutoffCoefficient M L N omega) := by
  unfold rescaledCutoffCoefficient
  exact continuous_const.mul
    ((SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M L omega).comp
      (continuous_const_smul ((3 : ℝ) ^ N)))

theorem rescaledCutoffCoefficient_pos
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L N : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (x : Vec d) :
    0 < rescaledCutoffCoefficient M L N omega x := by
  unfold rescaledCutoffCoefficient
  have hahom : 0 < ahom M L := (Real.exp_pos _).trans_le
    (SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower M L)
  exact mul_pos (inv_pos.mpr hahom)
    (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega _)

/-- On the unit cube, the literal rescaled cutoff admits deterministic
samplewise ellipticity constants. -/
theorem exists_isEllipticFieldOn_rescaledCutoffCoefficient
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L N : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    ∃ lam Lam : ℝ, 0 < lam ∧
      IsEllipticFieldOn lam Lam (openCubeSet (originCube d 0))
        (scalarCoeffField (rescaledCutoffCoefficient M L N omega)) := by
  let a0 := rescaledCutoffCoefficient M L N omega
  have ha : Continuous a0 := continuous_rescaledCutoffCoefficient M L N omega
  have hcompact : IsCompact (closure (openCubeSet (originCube d 0))) :=
    (Homogenization.Book.Ch02.cubeDomain (originCube d 0)).isDomain
      |>.isBoundedDomain.isBounded.isCompact_closure
  have hnonempty : (closure (openCubeSet (originCube d 0))).Nonempty :=
    (Homogenization.Book.Ch02.cubeDomain (originCube d 0)).nonempty.closure
  obtain ⟨xmin, hxmin, hmin⟩ :=
    hcompact.exists_isMinOn hnonempty ha.continuousOn
  obtain ⟨xmax, hxmax, hmax⟩ :=
    hcompact.exists_isMaxOn hnonempty ha.continuousOn
  refine ⟨a0 xmin, a0 xmax, rescaledCutoffCoefficient_pos M L N omega xmin, ?_⟩
  constructor
  · have hmatrix : Continuous fun x : Vec d ↦ scalarCoeffField a0 x :=
      ha.smul continuous_const
    refine measurable_pi_iff.2 fun i ↦ measurable_pi_iff.2 fun j ↦ ?_
    have hentry : Measurable fun x : Vec d ↦ scalarCoeffField a0 x i j :=
      (continuous_apply j).comp ((continuous_apply i).comp hmatrix) |>.measurable
    exact Measurable.ite (measurableSet_openCubeSet (originCube d 0))
      hentry measurable_const
  · intro x hx
    have hxc : x ∈ closure (openCubeSet (originCube d 0)) := subset_closure hx
    have hlow : a0 xmin ≤ a0 x := hmin hxc
    have hupp : a0 x ≤ a0 xmax := hmax hxc
    exact (isEllipticMatrix_scalarMatrix
      (rescaledCutoffCoefficient_pos M L N omega x)).mono
        (rescaledCutoffCoefficient_pos M L N omega xmin) hlow hupp

/-- Existence and a.e. uniqueness for both weak problems appearing in the
frozen cutoff Dirichlet conclusion. -/
theorem cutoffDirichlet_wellPosed
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L N : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (f : Vec d → ℝ)
    (hf : MemLp f 2 (volume.restrict (openCubeSet (originCube d 0))))
    (h : H2Datum (originCube d 0)) :
    (∃ u : H1Function (openCubeSet (originCube d 0)),
      IsScalarDirichletSolutionOn
        (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
        (originCube d 0) u h.toH1 f) ∧
    (∀ u u' : H1Function (openCubeSet (originCube d 0)),
      IsScalarDirichletSolutionOn
          (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
          (originCube d 0) u h.toH1 f →
      IsScalarDirichletSolutionOn
          (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
          (originCube d 0) u' h.toH1 f →
      u.toFun =ᵐ[volume.restrict (openCubeSet (originCube d 0))] u'.toFun ∧
        u.grad =ᵐ[volume.restrict (openCubeSet (originCube d 0))] u'.grad) ∧
    (∃ v : H1Function (openCubeSet (originCube d 0)),
      IsScalarDirichletSolutionOn (fun _ ↦ (1 : Mat d))
        (originCube d 0) v h.toH1 f) ∧
    (∀ v v' : H1Function (openCubeSet (originCube d 0)),
      IsScalarDirichletSolutionOn (fun _ ↦ (1 : Mat d))
          (originCube d 0) v h.toH1 f →
      IsScalarDirichletSolutionOn (fun _ ↦ (1 : Mat d))
          (originCube d 0) v' h.toH1 f →
      v.toFun =ᵐ[volume.restrict (openCubeSet (originCube d 0))] v'.toFun ∧
        v.grad =ᵐ[volume.restrict (openCubeSet (originCube d 0))] v'.grad) := by
  obtain ⟨lam, Lam, hlam, hEll⟩ :=
    exists_isEllipticFieldOn_rescaledCutoffCoefficient M L N omega
  refine ⟨exists_isScalarDirichletSolutionOn hEll h.toH1 hf, ?_,
    exists_isScalarDirichletSolutionOn_one h.toH1 hf, ?_⟩
  · intro u u' hu hu'
    exact ae_eq_of_isScalarDirichletSolutionOn hEll hu hu'
  · intro v v' hv hv'
    exact ae_eq_of_isScalarDirichletSolutionOn_one hv hv'

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
