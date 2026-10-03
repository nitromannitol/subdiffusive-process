module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.CompactSupportMonotoneLimit
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.GMCCubeBounds
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.CompactSupportLocalGradientBound
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceDecayFunction
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Set Topology
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped CompactlySupported ENNReal ZeroAtInfty

noncomputable section

variable {d : ℕ}

/-- A uniform finite `L²` seminorm bound passes to an almost-everywhere
pointwise limit, and in particular makes the limit a global `L²` function. -/
theorem memLp_two_and_eLpNorm_le_of_ae_tendsto
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (v : ℕ → X → ℝ) (u : X → ℝ) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hv : ∀ n, AEStronglyMeasurable (v n) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ v n x) atTop (𝓝 (u x)))
    (hbound : ∀ n, eLpNorm (v n) 2 μ ≤ C) :
    MemLp u 2 μ ∧ eLpNorm u 2 μ ≤ C := by
  have humeas := aestronglyMeasurable_of_tendsto_ae atTop hv hlim
  have hnorm : eLpNorm u 2 μ ≤ C :=
    Lp.eLpNorm_le_of_ae_tendsto
      (Filter.Eventually.of_forall hbound) hv humeas hlim
  refine ⟨?_, hnorm⟩
  exact hnorm.trans_lt (lt_top_iff_ne_top.mpr hC)

private theorem eLpNorm_two_le_div_of_integral_sq_le
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {u f : X → ℝ} {mu : ℝ} (hmu : 0 < mu)
    (hu : MemLp u 2 μ) (hf : MemLp f 2 μ)
    (henergy : mu ^ 2 * ∫ x, u x ^ 2 ∂μ ≤ ∫ x, f x ^ 2 ∂μ) :
    eLpNorm u 2 μ ≤ eLpNorm f 2 μ / ENNReal.ofReal mu := by
  have hsq :
      (mu * (eLpNorm u 2 μ).toReal) ^ 2 ≤
        (eLpNorm f 2 μ).toReal ^ 2 := by
    rw [mul_pow, Homogenization.toReal_eLpNorm_two_sq_eq_integral_sq hu,
      Homogenization.toReal_eLpNorm_two_sq_eq_integral_sq hf]
    exact henergy
  have hmul : mu * (eLpNorm u 2 μ).toReal ≤ (eLpNorm f 2 μ).toReal :=
    le_of_sq_le_sq hsq ENNReal.toReal_nonneg
  have hreal :
      (eLpNorm u 2 μ).toReal ≤
        (eLpNorm f 2 μ / ENNReal.ofReal mu).toReal := by
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal hmu.le]
    exact (le_div_iff₀' hmu).2 hmul
  exact (ENNReal.toReal_le_toReal hu.eLpNorm_ne_top
    (ENNReal.div_ne_top hf.eLpNorm_ne_top
      (ENNReal.ofReal_ne_zero_iff.mpr hmu))).1 hreal

private theorem integral_sq_zeroExtension
    {U : Set (Vec d)} (hU : MeasurableSet U) (w : H10Function U) :
    ∫ x, w.zeroExtension x ^ 2 ∂volume =
      ∫ x in U, w.toH1Function.toFun x ^ 2 ∂volume := by
  calc
    ∫ x, w.zeroExtension x ^ 2 ∂volume =
        ∫ x in U, w.zeroExtension x ^ 2 ∂volume := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [w.zeroExtension_apply_of_not_mem hx, zero_pow]
      norm_num
    _ = ∫ x in U, w.toH1Function.toFun x ^ 2 ∂volume := by
      apply integral_congr_ae
      exact (ae_restrict_iff' hU).2 <|
        Filter.Eventually.of_forall fun x hx ↦ by
          change w.zeroExtension x ^ 2 = w.toH1Function.toFun x ^ 2
          rw [w.zeroExtension_apply_of_mem hx]

/-- The pointwise limit of divergence-form massive cube solutions inherits
the global unweighted `L²` contraction, uniformly along the exhaustion.

The only coefficient fact used here is that the mass density is `1`.  Local
ellipticity is already packaged in `IsControlledMassiveCubeSolution`; no
global uniform ellipticity assumption is introduced. -/
theorem memLp_two_and_massive_l2_contraction_of_pointwise_cube_limit
    {c : Vec d → ℝ} {mu : ℝ} (hmu : 0 < mu) (f : C_c(Vec d, ℝ))
    (uCube : ∀ n : ℕ, H10Function (cube d (n : ℤ)))
    (v : ℕ → Vec d → ℝ) (u : Vec d → ℝ)
    (hcontrolled : ∀ n,
      IsControlledMassiveCubeSolution c (fun _ ↦ 1) mu f n (uCube n))
    (hvEq : ∀ n, v n =ᵐ[volume] (uCube n).zeroExtension)
    (hvLim : ∀ x, Tendsto (fun n ↦ v n x) atTop (𝓝 (u x))) :
    MemLp u 2 volume ∧
      mu ^ 2 * ∫ x, u x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume := by
  have hfMem : MemLp (fun x ↦ f x) 2 volume :=
    f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport
  have hcubeMeas : ∀ n : ℕ, MeasurableSet (cube d (n : ℤ)) := fun n ↦
    (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (n : ℤ)).isOpen.measurableSet
  have hzeroMem : ∀ n, MemLp (uCube n).zeroExtension 2 volume := fun n ↦
    (uCube n).memLp_zeroExtension (hcubeMeas n) (uCube n).toH1Function.memL2
  have hvMem : ∀ n, MemLp (v n) 2 volume := fun n ↦
    MemLp.ae_eq (hvEq n).symm (hzeroMem n)
  have henergy : ∀ n,
      mu ^ 2 * ∫ x, (uCube n).zeroExtension x ^ 2 ∂volume ≤
        ∫ x, f x ^ 2 ∂volume := by
    intro n
    calc
      mu ^ 2 * ∫ x, (uCube n).zeroExtension x ^ 2 ∂volume =
          mu ^ 2 * ∫ x in cube d (n : ℤ),
            (uCube n).toH1Function.toFun x ^ 2 ∂volume := by
        rw [integral_sq_zeroExtension (hcubeMeas n)]
      _ ≤ ∫ x in cube d (n : ℤ), f x ^ 2 ∂volume := by
        simpa only [one_mul, pow_two] using! (hcontrolled n).2.1
      _ ≤ ∫ x, f x ^ 2 ∂volume :=
        setIntegral_le_integral hfMem.integrable_sq
          (Filter.Eventually.of_forall fun x ↦ sq_nonneg (f x))
  let C : ℝ≥0∞ := eLpNorm (fun x ↦ f x) 2 volume / ENNReal.ofReal mu
  have hC : C ≠ ∞ :=
    ENNReal.div_ne_top hfMem.eLpNorm_ne_top
      (ENNReal.ofReal_ne_zero_iff.mpr hmu)
  have hvNorm : ∀ n, eLpNorm (v n) 2 volume ≤ C := by
    intro n
    rw [eLpNorm_congr_ae (hvEq n)]
    exact eLpNorm_two_le_div_of_integral_sq_le hmu (hzeroMem n) hfMem (henergy n)
  obtain ⟨huMem, huNorm⟩ := memLp_two_and_eLpNorm_le_of_ae_tendsto
    v u C hC (fun n ↦ (hvMem n).aestronglyMeasurable)
      (Filter.Eventually.of_forall hvLim) hvNorm
  refine ⟨huMem, ?_⟩
  have hreal :
      (eLpNorm u 2 volume).toReal ≤
        (eLpNorm (fun x ↦ f x) 2 volume).toReal / mu := by
    have := (ENNReal.toReal_le_toReal huMem.eLpNorm_ne_top hC).2 huNorm
    simpa only [C, ENNReal.toReal_div, ENNReal.toReal_ofReal hmu.le] using! this
  have hmul :
      mu * (eLpNorm u 2 volume).toReal ≤
        (eLpNorm (fun x ↦ f x) 2 volume).toReal :=
    (le_div_iff₀' hmu).1 hreal
  have hsq :
      (mu * (eLpNorm u 2 volume).toReal) ^ 2 ≤
        (eLpNorm (fun x ↦ f x) 2 volume).toReal ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hmu.le ENNReal.toReal_nonneg)
      ENNReal.toReal_nonneg).2 hmul
  calc
    mu ^ 2 * ∫ x, u x ^ 2 ∂volume =
        (mu * (eLpNorm u 2 volume).toReal) ^ 2 := by
      rw [mul_pow,
        Homogenization.toReal_eLpNorm_two_sq_eq_integral_sq huMem]
    _ ≤ (eLpNorm (fun x ↦ f x) 2 volume).toReal ^ 2 := hsq
    _ = ∫ x, f x ^ 2 ∂volume :=
      Homogenization.toReal_eLpNorm_two_sq_eq_integral_sq hfMem

/-- A fixed pointwise cube limit has compatible `H¹` massive weak-solution
representatives on every centered cube.  The conclusion concerns the same
global function `u` that appears in the pointwise convergence hypothesis.

This packages the local compactness passage needed before applying the
homogeneous-cell estimate in source lines 11687--11695. -/
theorem exists_localMassiveWeakSolutions_of_pointwise_cube_limit [NeZero d]
    {c rho : Vec d → ℝ} (B : MassiveCubeBounds c rho)
    {mu : ℝ} (hmu : 0 < mu) (f : C_c(Vec d, ℝ))
    (uCube : ∀ n : ℕ, H10Function (cube d (n : ℤ)))
    (v : ℕ → Vec d → ℝ) (u : Vec d → ℝ)
    (hcontrolled : ∀ n, IsControlledMassiveCubeSolution c rho mu f n (uCube n))
    (hvEq : ∀ n, v n =ᵐ[volume] (uCube n).zeroExtension)
    (hvLim : ∀ x, Tendsto (fun n ↦ v n x) atTop (𝓝 (u x))) :
    ∀ k : ℕ, ∃ uLocal : H1Function (cube d (k : ℤ)),
      uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
        IsMassiveWeakSolutionOn c rho mu (cube d (k : ℤ)) uLocal f := by
  intro k
  let hcube := Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (k : ℤ)
  letI : IsFiniteMeasure (volumeMeasureOn (cube d (k : ℤ))) :=
    hcube.isBoundedDomain.isFiniteMeasure_restrict_volume
  let hsubset (n : ℕ) : cube d (k : ℤ) ⊆ cube d ((k + n : ℕ) : ℤ) :=
    Section6ExcessDecay.cube_subset_cube_of_le (by omega)
  let w (n : ℕ) : H1Function (cube d (k : ℤ)) :=
    (uCube (k + n)).toH1Function.restrict hcube.isOpen (hsubset n)
  obtain ⟨Cgrad, _hCgrad, hgradient⟩ :=
    exists_uniform_local_gradient_norm_bound B hmu f uCube hcontrolled k
  have hbound : ∀ n, ∀ᵐ x ∂(volumeMeasureOn (cube d (k : ℤ))),
      |(w n).toFun x| ≤ ‖compactSupportToC0 f‖ / mu := by
    intro n
    exact (hcontrolled (k + n)).2.2.2.filter_mono <|
      ae_mono (Measure.restrict_mono (hsubset n) le_rfl)
  have hwEq : ∀ n, (w n).toFun =ᵐ[
      volumeMeasureOn (cube d (k : ℤ))] v (k + n) := by
    intro n
    have hvLocal : v (k + n) =ᵐ[
        volumeMeasureOn (cube d (k : ℤ))] (uCube (k + n)).zeroExtension :=
      (hvEq (k + n)).filter_mono <|
        ae_mono (show volumeMeasureOn (cube d (k : ℤ)) ≤ volume from
          Measure.restrict_le_self)
    filter_upwards [hvLocal,
      ae_restrict_mem hcube.isOpen.measurableSet] with x hx hxCube
    change (uCube (k + n)).toH1Function.toFun x = v (k + n) x
    rw [hx, (uCube (k + n)).zeroExtension_apply_of_mem ((hsubset n) hxCube)]
  have hpoint : ∀ᵐ x ∂(volumeMeasureOn (cube d (k : ℤ))),
      Tendsto (fun n ↦ (w n).toFun x) atTop (𝓝 (u x)) := by
    filter_upwards [ae_all_iff.2 hwEq] with x hx
    have hvSub : Tendsto (fun n ↦ v (k + n) x) atTop (𝓝 (u x)) := by
      simpa only [Function.comp_apply] using!
        (hvLim x).comp (strictMono_id.const_add k).tendsto_atTop
    apply Filter.Tendsto.congr' _ hvSub
    exact Filter.Eventually.of_forall fun n ↦ (hx n).symm
  have hw : ∀ n, IsMassiveWeakSolutionOn c rho mu
      (cube d (k : ℤ)) (w n) f := by
    intro n
    exact IsMassiveWeakSolutionOn.restrict hcube.isOpen
      (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d
        ((k + n : ℕ) : ℤ)).isOpen
      (hsubset n) (hcontrolled (k + n)).1
  have hfLocal : MemL2On (cube d (k : ℤ)) f :=
    (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport).restrict _
  obtain ⟨uLocal, huLocal, hsolution⟩ :=
    exists_isMassiveWeakSolutionOn_of_bounded_pointwise_limit
      (B.ell k) (B.rho_measurable k) (B.rho_bounded k) hfLocal w
      hbound hpoint (by simpa only [w] using! hgradient) hw
  exact ⟨uLocal, huLocal, hsolution⟩

/-- The divergence-form pointwise cube limit satisfies the full deterministic
exterior-decay conclusion once the stopping partition supplies its four raw
graph inputs.  Unlike `massiveWholeSpaceSolution_decay_of_graph_cells`, this
endpoint requires no global uniform ellipticity and no global `H¹` carrier. -/
theorem integral_sq_exterior_le_of_divergence_pointwise_cube_limit_graph_cells
    {c : Vec d → ℝ} {mu : ℝ} (hmu : 0 < mu) (f : C_c(Vec d, ℝ))
    (uCube : ∀ n : ℕ, H10Function (cube d (n : ℤ)))
    (v : ℕ → Vec d → ℝ) (u : Vec d → ℝ)
    (hcontrolled : ∀ n,
      IsControlledMassiveCubeSolution c (fun _ ↦ 1) mu f n (uCube n))
    (hvEq : ∀ n, v n =ᵐ[volume] (uCube n).zeroExtension)
    (hvLim : ∀ x, Tendsto (fun n ↦ v n x) atTop (𝓝 (u x)))
    (count : ℕ → ℕ)
    (cell : (j : ℕ) → Fin (count j) → Set (Vec d))
    (exterior : Set (Vec d)) {A theta : ℝ} (N D : ℕ) {rate : ℝ}
    (hA : 0 ≤ A) (htheta : 0 < theta) (hD : 0 < D)
    (heffective : (D : ℝ) * theta < 1)
    (hsource : ∀ i : Fin (count 0),
      ∫ x in cell 0 i, u x ^ 2 ∂volume ≤ A)
    (hstep : ∀ (j : ℕ) (i : Fin (count j)), 0 < j →
      ∃ p : Σ k : ℕ, Fin (count k),
        j ≤ p.1 + 1 ∧
        ∫ x in cell j i, u x ^ 2 ∂volume ≤
          theta * ∫ x in cell p.1 p.2, u x ^ 2 ∂volume)
    (hcard : ∀ j, count j ≤ N * D ^ j)
    (hcover : exterior ⊆
      ⋃ p : Σ k : ℕ, Fin (count (⌈rate⌉₊ + k)),
        cell (⌈rate⌉₊ + p.1) p.2) :
    ∫ x in exterior, u x ^ 2 ∂volume ≤
      (N : ℝ) * A * (1 - (D : ℝ) * theta)⁻¹ *
        Real.exp (Real.log ((D : ℝ) * theta) * rate) := by
  have hu := (memLp_two_and_massive_l2_contraction_of_pointwise_cube_limit
    hmu f uCube v u hcontrolled hvEq hvLim).1
  exact integral_sq_exterior_le_of_graph_cells u hu count cell exterior N D
    hA htheta hD heffective hsource hstep hcard hcover

/-- The divergence-form GMC cube exhaustion has an everywhere bounded,
nonnegative, monotone pointwise limit which is also a global `L²` function
and obeys the sharp massive `L²` contraction.

This is the first assembly-facing whole-space carrier that uses only the
landed local GMC cube bounds, rather than a false global uniform ellipticity
hypothesis. -/
theorem exists_pointwiseMonotoneDivergenceMassiveCubeLimit_with_l2 [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : WithTop ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d)
    {mu : ℝ} (hmu : 0 < mu) (f : C_c(Vec d, ℝ)) (hf : ∀ x, 0 ≤ f x) :
    ∃ uCube : ∀ n : ℕ, H10Function (cube d (n : ℤ)),
      ∃ v : ℕ → Vec d → ℝ, ∃ u : Vec d → ℝ,
        (∀ n, IsControlledMassiveCubeSolution (coefficientAt M L omega)
          (fun _ ↦ (1 : ℝ)) mu f n (uCube n)) ∧
        (∀ n, v n =ᵐ[volume] (uCube n).zeroExtension) ∧
        (∀ x, Monotone fun n ↦ v n x) ∧
        (∀ n x, 0 ≤ v n x ∧ v n x ≤ ‖compactSupportToC0 f‖ / mu) ∧
        (∀ x, Tendsto (fun n ↦ v n x) atTop (𝓝 (u x))) ∧
        MemLp u 2 volume ∧
        mu ^ 2 * ∫ x, u x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume := by
  obtain ⟨uCube, v, u, hcontrolled, hvEq, hvMono, hvBounds, hvLim⟩ :=
    exists_pointwiseMonotoneDivergenceMassiveCubeLimit M L omega hmu f hf
  have hL2 := memLp_two_and_massive_l2_contraction_of_pointwise_cube_limit
    hmu f uCube v u hcontrolled hvEq hvLim
  exact ⟨uCube, v, u, hcontrolled, hvEq, hvMono, hvBounds, hvLim, hL2.1, hL2.2⟩

/-- The divergence-form GMC exhaustion simultaneously supplies the global
`L²` carrier and compatible local weak-solution representatives.  Thus the
same function can be fed to `integral_sq_exterior_le_of_graph_cells`, while
its local representatives can be used to establish the graph-cell PDE
inequalities. -/
theorem exists_pointwiseMonotoneDivergenceMassiveCubeLimit_with_l2_and_local
    [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : WithTop ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d)
    {mu : ℝ} (hmu : 0 < mu) (f : C_c(Vec d, ℝ)) (hf : ∀ x, 0 ≤ f x) :
    ∃ uCube : ∀ n : ℕ, H10Function (cube d (n : ℤ)),
      ∃ v : ℕ → Vec d → ℝ, ∃ u : Vec d → ℝ,
        (∀ n, IsControlledMassiveCubeSolution (coefficientAt M L omega)
          (fun _ ↦ (1 : ℝ)) mu f n (uCube n)) ∧
        (∀ n, v n =ᵐ[volume] (uCube n).zeroExtension) ∧
        (∀ x, Monotone fun n ↦ v n x) ∧
        (∀ n x, 0 ≤ v n x ∧ v n x ≤ ‖compactSupportToC0 f‖ / mu) ∧
        (∀ x, Tendsto (fun n ↦ v n x) atTop (𝓝 (u x))) ∧
        MemLp u 2 volume ∧
        (mu ^ 2 * ∫ x, u x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume) ∧
        ∀ k : ℕ, ∃ uLocal : H1Function (cube d (k : ℤ)),
          uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
            IsMassiveWeakSolutionOn (coefficientAt M L omega) (fun _ ↦ 1)
              mu (cube d (k : ℤ)) uLocal f := by
  obtain ⟨uCube, v, u, hcontrolled, hvEq, hvMono, hvBounds, hvLim⟩ :=
    exists_pointwiseMonotoneDivergenceMassiveCubeLimit M L omega hmu f hf
  have hL2 := memLp_two_and_massive_l2_contraction_of_pointwise_cube_limit
    hmu f uCube v u hcontrolled hvEq hvLim
  have hlocal := exists_localMassiveWeakSolutions_of_pointwise_cube_limit
    (divergenceMassiveCubeBounds M L omega) hmu f uCube v u
      hcontrolled hvEq hvLim
  exact ⟨uCube, v, u, hcontrolled, hvEq, hvMono, hvBounds, hvLim,
    hL2.1, hL2.2, hlocal⟩

end


end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
