module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut.LimitTransfer
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.InteriorSpecialization

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut

open MeasureTheory Filter Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
open SubdiffusiveProcess.Frozen.Assumptions

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ### Elementary window facts -/

/-- A bounded open convex domain has finite volume. -/
theorem volume_ne_top_of_domain {V : Set (Vec d)}
    (h : IsOpenBoundedConvexDomain V) : volume V ≠ ⊤ := by
  haveI := h.isFiniteMeasure_restrict_volume
  have hlt := measure_lt_top (volume.restrict V) Set.univ
  rw [Measure.restrict_apply_univ] at hlt
  exact hlt.ne

/-- A nonempty bounded open convex domain has strictly positive finite
volume. -/
theorem volume_toReal_pos_of_domain {V : Set (Vec d)}
    (h : IsOpenBoundedConvexDomain V) (hne : V.Nonempty) :
    0 < (volume V).toReal :=
  ENNReal.toReal_pos (h.isOpen.measure_pos volume hne).ne'
    (volume_ne_top_of_domain h)

/-! ### The displays at the uncut coefficient -/

/-- **The two Theorem C displays at `L = ⊤`.**

Hypotheses: the `J`-uniform ellipticity pair on `𝔠_m` and the uniform
convergence of the anchored cutoffs on `closure 𝔠_m` — both supplied by the
PROVED anchor `l.finite.cutoff.coefficient.convergence` — and the *uncut
clause* of the frozen interior Hölder anchor, carried byte-exact and
instantiated at this sample and scale. -/
theorem theoremCDisplays_top_of_uncutAnchor [NeZero d]
    {M : GMCModel d} {C gamma : ℝ} {m X : ℕ} {ω : AnchoredC11Sample d}
    {lam Lam : ℝ} (hlam : 0 < lam)
    (hbA : ∀ x ∈ cube d (m : ℤ),
      lam ≤ aAnchored M ω x ∧ aAnchored M ω x ≤ Lam)
    (hbC : ∀ L : ℕ, ∀ x ∈ cube d (m : ℤ),
      lam ≤ anchoredCutoff M L ω.1 x ∧ anchoredCutoff M L ω.1 x ≤ Lam)
    (hunif : TendstoUniformlyOn (fun (L : ℕ) x ↦ anchoredCutoff M L ω.1 x)
      (aAnchored M ω) atTop (closure (cube d (m : ℤ))))
    (hanchor : ∀ J : ℕ, m ≤ J →
      ∀ (p : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (aCutoff M J ω.1) (cube d (m : ℤ)) p g →
        MemHolder (cube d (m : ℤ)) (1 / 2) g →
        InteriorHolderRegularityConclusions M C J ω.1 gamma m X p g)
    (u : H1Function (openCubeSet (originCube d (m : ℤ))))
    (hu : IsWeaklyHarmonicOn (coefficientAt M (⊤ : WithTop ℕ) ω)
      (cube d (m : ℤ)) u) :
    TheoremCDisplays M C (⊤ : WithTop ℕ) gamma m X ω u := by
  classical
  -- Geometry of the outer window.
  have hWm : MeasurableSet (cube d (m : ℤ)) :=
    measurableSet_openCubeSet (originCube d (m : ℤ))
  have hWdom : IsOpenBoundedConvexDomain (cube d (m : ℤ)) :=
    isOpenBoundedConvexDomain_cube d (m : ℤ)
  have hWne : (cube d (m : ℤ)).Nonempty := nonempty_cube d (m : ℤ)
  have hWfin : volume (cube d (m : ℤ)) ≠ ⊤ := volume_ne_top_of_domain hWdom
  have hWpos : 0 < (volume (cube d (m : ℤ))).toReal :=
    volume_toReal_pos_of_domain hWdom hWne
  -- The uncut coefficient is the anchored limit.
  have huA : IsWeaklyHarmonicOn (aAnchored M ω) (cube d (m : ℤ)) u := hu
  -- Ellipticity carriers, uniform in the cutoff.
  have hEllA : IsEllipticFieldOn lam Lam (cube d (m : ℤ))
      (scalarCoeffField (aAnchored M ω)) := isEllipticFieldOn_aAnchored hlam hbA
  have hEllC : ∀ L : ℕ, IsEllipticFieldOn lam Lam (cube d (m : ℤ))
      (scalarCoeffField (anchoredCutoff M L ω.1)) := fun L ↦
    isEllipticFieldOn_anchoredCutoff L hlam (hbC L)
  have hLamnn : 0 ≤ Lam := by
    obtain ⟨x0, hx0⟩ := hWne
    have := (hbA x0 hx0).2
    have h0 := (hbA x0 hx0).1
    linarith
  -- S4: the comparison solutions.
  have hex : ∀ j : ℕ, ∃ p : H1Function (cube d (m : ℤ)),
      IsWeaklyHarmonicOn (anchoredCutoff M (m + j) ω.1) (cube d (m : ℤ)) p ∧
        HasZeroTraceDifferenceOn (cube d (m : ℤ)) p u := fun j ↦
    exists_comparisonSolution_cube (hEllC (m + j)) u
  choose v hv hvz using hex
  choose w hwf hwg using hvz
  -- The coefficient defect vanishes uniformly on the window.
  have hdefect : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
      ∀ x ∈ cube d (m : ℤ),
        |aAnchored M ω x - anchoredCutoff M (m + j) ω.1 x| ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ :=
      eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 hunif) ε hε)
    refine eventually_atTop.2 ⟨N, fun j hj x hx ↦ ?_⟩
    have hxc : x ∈ closure (cube d (m : ℤ)) := subset_closure hx
    have hdist := hN (m + j) (by omega) x hxc
    rw [Real.dist_eq] at hdist
    exact hdist.le
  -- S5: the gradient energy of the difference vanishes.
  have hE : Tendsto
      (fun j ↦ ∫ x in cube d (m : ℤ),
        vecNormSq ((w j).toH1Function.grad x) ∂volume) atTop (nhds 0) :=
    tendsto_integral_vecNormSq_grad_zero hWm hlam hEllA (fun j ↦ hEllC (m + j))
      (fun j x hx ↦ (hbC (m + j) x hx).1) huA hv hwg hdefect
  -- Poincaré: the `L²` size of the difference vanishes too.
  obtain ⟨Cp, hCp0, hCp⟩ := exists_poincare_integral_const hWdom hWm
  have hL2 : Tendsto
      (fun j ↦ ∫ x in cube d (m : ℤ),
        ((v j).toFun x - u.toFun x) ^ 2 ∂volume) atTop (nhds 0) := by
    have hmaj : Tendsto (fun j ↦ Cp * ∫ x in cube d (m : ℤ),
        vecNormSq ((w j).toH1Function.grad x) ∂volume) atTop (nhds 0) := by
      simpa using hE.const_mul Cp
    refine squeeze_zero (fun j ↦ ?_) (fun j ↦ ?_) hmaj
    · exact setIntegral_nonneg hWm fun x _ ↦ sq_nonneg _
    · have hcongr : ∀ x, ((v j).toFun x - u.toFun x) ^ 2 =
          (w j).toH1Function.toFun x ^ 2 := by
        intro x; rw [hwf j x]; ring
      simp only [hcongr]
      exact hCp (w j)
  -- The weighted composite fields.
  have hmemF : ∀ j : ℕ, MemVectorL2 (cube d (m : ℤ))
      (fun x ↦ Real.sqrt (anchoredCutoff M (m + j) ω.1 x) • (v j).grad x) :=
    fun j ↦ memVectorL2_sqrt_smul_grad hlam
      (continuous_anchoredCutoff M (m + j) ω.1) hWm (hbC (m + j)) (v j)
  have hmemFlim : MemVectorL2 (cube d (m : ℤ))
      (fun x ↦ Real.sqrt (aAnchored M ω x) • u.grad x) :=
    memVectorL2_sqrt_smul_grad hlam (continuous_aAnchored M ω) hWm hbA u
  have hEW : Tendsto (fun j ↦ ∫ x in cube d (m : ℤ),
      vecNormSq (Real.sqrt (anchoredCutoff M (m + j) ω.1 x) • (v j).grad x -
        Real.sqrt (aAnchored M ω x) • u.grad x) ∂volume) atTop (nhds 0) :=
    tendsto_integral_weighted_sub_zero hWm hLamnn
      (fun j x ↦ (anchoredCutoff_pos M (m + j) ω.1 x).le)
      (fun x ↦ (aAnchored_pos M ω x).le)
      (fun j x hx ↦ (hbC (m + j) x hx).2) hwg
      (fun j ↦ integrableOn_vecNormSq_of_memVectorL2
        ((hmemF j).sub hmemFlim)) hE hdefect
  -- The finite-cutoff displays, one for each comparison solution.
  have hdisp : ∀ j : ℕ,
      TheoremCDisplays M C ((m + j : ℕ) : WithTop ℕ) gamma m X ω (v j) := by
    intro j
    have hharm : IsWeaklyHarmonicOn
        (coefficientAt M ((m + j : ℕ) : WithTop ℕ) ω) (cube d (m : ℤ)) (v j) :=
      (isWeaklyHarmonicOn_coefficientAt_iff_anchoredCutoff M (m + j) ω
        (cube d (m : ℤ)) (v j)).2 (hv j)
    have hcut : IsWeaklyHarmonicOn (aCutoff M (m + j) ω.1)
        (cube d (m : ℤ)) (v j) := by
      rwa [coefficientAt_natCast] at hharm
    obtain ⟨hdiv, hg⟩ := interior_hypotheses_of_isWeaklyHarmonicOn hcut
    exact theoremCDisplays_of_interiorConclusions
      (hanchor (m + j) (Nat.le_add_right m j) (v j) _ hdiv hg)
  -- The limit passage, window by window.
  intro n hn z hgrid hsub
  have hVdom : IsOpenBoundedConvexDomain (translatedCube d (n : ℤ) z) :=
    isOpenBoundedConvexDomain_translatedCube (n : ℤ) z
  have hVm : MeasurableSet (translatedCube d (n : ℤ) z) :=
    hVdom.isOpen.measurableSet
  have hVne : (translatedCube d (n : ℤ) z).Nonempty :=
    translatedCube_nonempty (n : ℤ) z
  have hVfin : volume (translatedCube d (n : ℤ) z) ≠ ⊤ :=
    volume_ne_top_of_domain hVdom
  have hVpos : 0 < (volume (translatedCube d (n : ℤ) z)).toReal :=
    volume_toReal_pos_of_domain hVdom hVne
  have hVW : translatedCube d (n : ℤ) z ⊆ cube d (m : ℤ) :=
    hsub.trans (Section6ExcessDecay.cube_subset_cube_of_le (by omega))
  refine ⟨?_, ?_⟩
  · -- Row 1: the oscillation display.
    refine centeredNormalizedL2On_le_mul_of_outer_tendsto hVm hVpos hVfin
      hWm hWpos hWfin hVW (fun j ↦ (v j).memL2) u.memL2 hL2 ?_
    intro j
    exact (hdisp j n hn z hgrid hsub).1
  · -- Row 2: the energy display.
    refine vectorNormalizedL2On_le_mul_of_outer_tendsto hVm hVW hmemF
      hmemFlim hEW ?_
    intro j
    have h := (hdisp j n hn z hgrid hsub).2
    simp only [coefficientAt_natCast_eq_const_mul_anchoredCutoff] at h
    exact (energyEstimate_const_smul_iff
      (aCutoff_origin_pos M (m + j) ω.1) _ _ _ _ _).1 h

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut
