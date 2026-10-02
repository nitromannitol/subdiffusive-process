import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.CompactSupportLocalGradientBound




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Topology
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped CompactlySupported ZeroAtInfty

noncomputable section

variable {d : ℕ}

/-- The nonnegative compact-data cube exhaustion produces one bounded global
pointwise limit with compatible local massive weak-solution representatives. -/
theorem exists_bounded_localMassiveWeakSolution_of_compactSupport [NeZero d]
    {c rho : Vec d → ℝ} (B : MassiveCubeBounds c rho)
    {mu : ℝ} (hmu : 0 < mu) (f : C_c(Vec d, ℝ))
    (hf : ∀ x, 0 ≤ f x) :
    ∃ u : Vec d → ℝ,
      (∀ x, 0 ≤ u x ∧ u x ≤ ‖compactSupportToC0 f‖ / mu) ∧
        ∀ k : ℕ, ∃ uLocal : H1Function (cube d (k : ℤ)),
          uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
            IsMassiveWeakSolutionOn c rho mu (cube d (k : ℤ)) uLocal f := by
  obtain ⟨uCube, v, u, hu, hvEq, _hvMono, hvBounds, hvLim⟩ :=
    exists_pointwiseMonotoneMassiveCubeLimit_of_compactSupport B hmu f hf
  have huBounds : ∀ x, 0 ≤ u x ∧ u x ≤ ‖compactSupportToC0 f‖ / mu := by
    intro x
    exact isClosed_Icc.mem_of_tendsto (hvLim x) <|
      Filter.Eventually.of_forall fun n ↦ hvBounds n x
  refine ⟨u, huBounds, fun k ↦ ?_⟩
  let hcube := Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (k : ℤ)
  letI : IsFiniteMeasure (volumeMeasureOn (cube d (k : ℤ))) :=
    hcube.isBoundedDomain.isFiniteMeasure_restrict_volume
  let hsubset (n : ℕ) : cube d (k : ℤ) ⊆ cube d ((k + n : ℕ) : ℤ) :=
    Section6ExcessDecay.cube_subset_cube_of_le (by omega)
  let w (n : ℕ) : H1Function (cube d (k : ℤ)) :=
    (uCube (k + n)).toH1Function.restrict hcube.isOpen (hsubset n)
  obtain ⟨Cgrad, _hCgrad, hgradient⟩ :=
    exists_uniform_local_gradient_norm_bound B hmu f uCube hu k
  have hbound : ∀ n, ∀ᵐ x ∂(volumeMeasureOn (cube d (k : ℤ))),
      |(w n).toFun x| ≤ ‖compactSupportToC0 f‖ / mu := by
    intro n
    exact (hu (k + n)).2.2.2.filter_mono <|
      ae_mono (Measure.restrict_mono (hsubset n) le_rfl)
  have hwEq : ∀ n, (w n).toFun =ᵐ[
      volumeMeasureOn (cube d (k : ℤ))] v (k + n) := by
    intro n
    have hvLocal : v (k + n) =ᵐ[
        volumeMeasureOn (cube d (k : ℤ))] (uCube (k + n)).zeroExtension :=
      (hvEq (k + n)).filter_mono <|
        ae_mono (show volume.restrict (cube d (k : ℤ)) ≤ volume from
          Measure.restrict_le_self)
    filter_upwards [hvLocal,
      ae_restrict_mem hcube.isOpen.measurableSet] with x hx hxCube
    simp only [w, H1Function.restrict, hx]
    exact ((uCube (k + n)).zeroExtension_apply_of_mem ((hsubset n) hxCube)).symm
  have hpoint : ∀ᵐ x ∂(volumeMeasureOn (cube d (k : ℤ))),
      Tendsto (fun n ↦ (w n).toFun x) atTop (nhds (u x)) := by
    filter_upwards [ae_all_iff.2 hwEq] with x hx
    have hvSub : Tendsto (fun n ↦ v (k + n) x) atTop (nhds (u x)) := by
      simpa only [Function.comp_apply] using
        (hvLim x).comp (strictMono_id.const_add k).tendsto_atTop
    apply Filter.Tendsto.congr' _ hvSub
    exact Filter.Eventually.of_forall fun n ↦ (hx n).symm
  have hw : ∀ n, IsMassiveWeakSolutionOn c rho mu
      (cube d (k : ℤ)) (w n) f := by
    intro n
    exact IsMassiveWeakSolutionOn.restrict hcube.isOpen
      (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d
        ((k + n : ℕ) : ℤ)).isOpen
      (hsubset n) (hu (k + n)).1
  have hfLocal : MemL2On (cube d (k : ℤ)) f :=
    (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport).restrict _
  obtain ⟨uLocal, huLocal, hsolution⟩ :=
    exists_isMassiveWeakSolutionOn_of_bounded_pointwise_limit
      (B.ell k) (B.rho_measurable k) (B.rho_bounded k) hfLocal w
      hbound hpoint (by simpa only [w] using hgradient) hw
  exact ⟨uLocal, huLocal, hsolution⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
