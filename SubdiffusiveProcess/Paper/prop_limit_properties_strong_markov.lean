module

public import SubdiffusiveProcess.Paper.limit_kernel
public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Paper.lem_tightness_deterministic_restart

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_prop_limit_properties_strong_markov_deterministic
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (hP : P.IsConservative)
    (Q : Kernel (SpatialCoordinates d) (DiffusionPath d))
    [IsMarkovKernel Q]
    (hfd : ∀ I : Finset ℝ≥0,
      Q.map (ContinuousPath.finsetEvaluation I) =
        SubMarkovKernelSemigroup.finiteSetKernel P I) :
    ∀ (x : SpatialCoordinates d) (t : ℝ≥0)
      (A : Set (DiffusionPath d)),
      MeasurableSet[ContinuousPath.canonicalFiltration
        (alpha := SpatialCoordinates d) t] A →
      ((Q x).restrict A).map (ContinuousPath.shift t) =
        Kernel.comap Q (fun path : DiffusionPath d => path t)
          (ContinuousPath.measurable_coordinateProcess t) ∘ₘ ((Q x).restrict A) := by
  intro x t A hA
  let past : DiffusionPath d → (Set.Iic t → SpatialCoordinates d) :=
    fun path r => path r.1
  have hpast : Measurable past := by
    rw [measurable_pi_iff]
    intro r
    exact ContinuousPath.measurable_coordinateProcess (r : ℝ≥0)
  let terminal : (Set.Iic t → SpatialCoordinates d) → SpatialCoordinates d :=
    fun history => history ⟨t, by simp⟩
  have hterminal : Measurable terminal := measurable_pi_apply _
  have hTerminalPath : terminal ∘ past = fun path : DiffusionPath d => path t := by
    rfl
  have hJoint :
      (Q x).map (fun path => (past path, ContinuousPath.shift t path)) =
        ((Q x).map past) ⊗ₘ (Q.comap terminal hterminal) := by
    have hcut : ∀ I : Finset (Set.Iic t ⊕ DenseTime),
        (Q.map (fun path => (past path, ContinuousPath.shift t path))).map
          (I.restrict ∘ Kernel.finitePastDenseFuture
            (index := Set.Iic t) (alpha := SpatialCoordinates d)) =
        (((Q.map past).compProd
          ((Q.comap terminal hterminal).comap Prod.snd measurable_snd))).map
          (I.restrict ∘ Kernel.finitePastDenseFuture
            (index := Set.Iic t) (alpha := SpatialCoordinates d)) := by
      intro I
      obtain ⟨Jpast, Jfuture, ht, hPast, hPastExact, hFuture, hFutureExact,
        cutIndex, G, hcutIndex, hG, hGmeas, hfin⟩ :=
        aux_lem_tightness_deterministic_restart_mixedFiniteCut
          P hP Q hfd t I
      apply Kernel.ext
      intro y
      let ppoint : Jpast → Set.Iic t := fun u =>
        ⟨(u : ℝ≥0), by
          rcases hPastExact (u : ℝ≥0) u.property with hu | ⟨r, hr, hu⟩
          · simp [hu]
          · rw [← hu]
            exact r.property⟩
      let pproj : (Set.Iic t → SpatialCoordinates d) →
          (Jpast → SpatialCoordinates d) :=
        fun history u => history (ppoint u)
      let fproj : DiffusionPath d → (Jfuture → SpatialCoordinates d) :=
        fun path u => path (u : ℝ≥0)
      let terminal' : (Jpast → SpatialCoordinates d) → SpatialCoordinates d :=
        fun history => history ⟨t, ht⟩
      let Hproj : ((Set.Iic t → SpatialCoordinates d) × DiffusionPath d) →
          ((Jpast → SpatialCoordinates d) × (Jfuture → SpatialCoordinates d)) :=
        Prod.map pproj fproj
      let Fcut : ((Set.Iic t → SpatialCoordinates d) × DiffusionPath d) →
          (I → SpatialCoordinates d) :=
        I.restrict ∘ Kernel.finitePastDenseFuture
          (index := Set.Iic t) (alpha := SpatialCoordinates d)
      have hpproj : Measurable pproj := by
        rw [measurable_pi_iff]
        intro u
        exact measurable_pi_apply (ppoint u)
      have hfproj : Measurable fproj := by
        rw [measurable_pi_iff]
        intro u
        exact ContinuousPath.measurable_coordinateProcess (u : ℝ≥0)
      have hHproj : Measurable Hproj := hpproj.prodMap hfproj
      have hterminal' : Measurable terminal' := measurable_pi_apply _
      have hcompat : terminal' ∘ pproj = terminal := by
        funext history
        dsimp [terminal', pproj, terminal]
      have hFcut : Measurable Fcut := by
        exact (Finset.measurable_restrict I).comp
          Kernel.measurable_finitePastDenseFuture
      have hpair : Measurable
          (fun path : DiffusionPath d =>
            (past path, ContinuousPath.shift t path)) :=
        hpast.prodMk (ContinuousPath.measurable_shift_fixed t)
      have hGcomp : Measurable (G ∘ Hproj) := hGmeas.comp hHproj
      have hzero : ∀ z : SpatialCoordinates d,
          ∀ᵐ path ∂Q z, path (0 : ℝ≥0) = z := by
        intro z
        have hzeroMap : (Q z).map (fun path : DiffusionPath d => path (0 : ℝ≥0)) =
            Measure.dirac z := by
          have hsingleton :
              (Q.map (ContinuousPath.finsetEvaluation ({(0 : ℝ≥0)} : Finset ℝ≥0))) z =
                (SubMarkovKernelSemigroup.finiteSetKernel P
                  ({(0 : ℝ≥0)} : Finset ℝ≥0)) z := by
            exact congrArg (fun K => K z) (hfd ({(0 : ℝ≥0)} : Finset ℝ≥0))
          have hsingleton' :
              (Q z).map (ContinuousPath.finsetEvaluation ({(0 : ℝ≥0)} : Finset ℝ≥0)) =
                SubMarkovKernelSemigroup.finiteSetKernel P
                  ({(0 : ℝ≥0)} : Finset ℝ≥0) z := by
            simpa only [Kernel.map_apply Q
              (ContinuousPath.measurable_finsetEvaluation ({(0 : ℝ≥0)} : Finset ℝ≥0)) z]
              using hsingleton
          have hzeroMap' :
              (Q z).map (fun path : DiffusionPath d => path (0 : ℝ≥0)) = P.kernel 0 z :=
            SubdiffusiveProcess.map_eval_eq_of_finsetEvaluation
              P (Q z) z (0 : ℝ≥0) hsingleton'
          calc
            (Q z).map (fun path : DiffusionPath d => path (0 : ℝ≥0)) = P.kernel 0 z :=
              hzeroMap'
            _ = Measure.dirac z := by
              rw [P.zero, Kernel.id_apply]
        let : IsProbabilityMeasure (Q z) := IsMarkovKernel.isProbabilityMeasure z
        apply (mem_ae_iff_prob_eq_one
          (ContinuousPath.measurable_coordinateProcess (0 : ℝ≥0)
            (MeasurableSet.singleton z))).mpr
        rw [← Measure.map_apply
          (ContinuousPath.measurable_coordinateProcess (0 : ℝ≥0))
          (MeasurableSet.singleton z)]
        change (Measure.map (fun path : DiffusionPath d => path (0 : ℝ≥0))
          (Q z)) {z} = 1
        rw [hzeroMap]
        simp
      have hfactor_ae : ∀ history : Set.Iic t → SpatialCoordinates d,
          ∀ future : DiffusionPath d, future (0 : ℝ≥0) = terminal' (pproj history) →
            Fcut (history, future) = G (Hproj (history, future)) := by
        intro history future hfuture
        funext i
        rcases i with ⟨i, hi⟩
        rcases i with r | q
        · have hc := hcutIndex ⟨Sum.inl r, hi⟩
          have hc' : cutIndex ⟨Sum.inl r, hi⟩ =
              Sum.inl ⟨r.1, hPast r hi⟩ := by simpa using hc
          rw [hG, hc']
          simp [Fcut, Hproj, pproj, fproj, Kernel.finitePastDenseFuture]
          apply congrArg history
          apply Subtype.ext
          rfl
        · by_cases hq : q = 0
          · subst q
            have hc := hcutIndex ⟨Sum.inr 0, hi⟩
            have hc' : cutIndex ⟨Sum.inr 0, hi⟩ = Sum.inl ⟨t, ht⟩ := by
              simpa using hc
            rw [hG, hc']
            change future (DenseTime.castOrderEmbedding 0) = history (ppoint ⟨t, ht⟩)
            simpa [DenseTime.castOrderEmbedding, NNRat.castOrderEmbedding_apply,
              terminal', pproj, ContinuousPath.densePastRestriction_apply] using hfuture
          · have hc := hcutIndex ⟨Sum.inr q, hi⟩
            have hc' : cutIndex ⟨Sum.inr q, hi⟩ =
                Sum.inr ⟨DenseTime.castOrderEmbedding q, hFuture q hi
                  (bot_lt_iff_ne_bot.mpr hq)⟩ := by
              simpa [hq] using hc
            rw [hG, hc']
            simp [Fcut, Hproj, pproj, fproj, Kernel.finitePastDenseFuture]
      have hEqMeas : MeasurableSet
          {z : (Set.Iic t → SpatialCoordinates d) × DiffusionPath d |
            Fcut z = G (Hproj z)} := measurableSet_eq_fun hFcut hGcomp
      have hEqAe : ∀ᵐ z ∂((Q.map past y) ⊗ₘ (Q.comap terminal hterminal)),
          Fcut z = G (Hproj z) := by
        apply Measure.ae_compProd_of_ae_ae hEqMeas
        refine ae_of_all _ ?_
        intro history
        filter_upwards [hzero (terminal history)] with future hfuture
        apply hfactor_ae history future
        simpa [terminal', pproj, ppoint, terminal] using hfuture
      have hRmeasure :
          ((Q.map past).compProd
            ((Q.comap terminal hterminal).comap Prod.snd measurable_snd)) y =
            (Q.map past y) ⊗ₘ (Q.comap terminal hterminal) := by
        ext S hS
        rw [Kernel.compProd_apply hS, Measure.compProd_apply hS]
        rfl
      have hQpast :
          (Q.map past).map pproj =
            SubMarkovKernelSemigroup.finiteSetKernel P Jpast := by
        have heval : pproj ∘ past = ContinuousPath.finsetEvaluation Jpast := by
          funext path u
          rfl
        calc
          (Q.map past).map pproj = Q.map (pproj ∘ past) :=
            (Kernel.map_comp_right Q hpast hpproj).symm
          _ = Q.map (ContinuousPath.finsetEvaluation Jpast) := by rw [heval]
          _ = SubMarkovKernelSemigroup.finiteSetKernel P Jpast := hfd Jpast
      have hQfuture' :
          (Q.map fproj).comap terminal' hterminal' =
            (SubMarkovKernelSemigroup.finiteSetKernel P Jfuture).comap
              terminal' hterminal' := by
        have hprojEval : fproj = ContinuousPath.finsetEvaluation Jfuture := by
          funext path u
          rfl
        rw [hprojEval, hfd Jfuture]
      have hright :
          (((Q.map past).compProd
            ((Q.comap terminal hterminal).comap Prod.snd measurable_snd)) y).map Fcut =
          ((SubMarkovKernelSemigroup.finiteSetKernel P Jpast) ⊗ₖ
            Kernel.prodMkLeft (SpatialCoordinates d)
          ((SubMarkovKernelSemigroup.finiteSetKernel P Jfuture).comap
                terminal' hterminal')).map G y := by
        have hkernelMap := Kernel.map_compProd_prodMkLeft_comap
          (Q.map past) Q terminal terminal' hterminal' pproj hpproj fproj hfproj hcompat
        calc
          (((Q.map past).compProd
            ((Q.comap terminal hterminal).comap Prod.snd measurable_snd)) y).map Fcut =
              ((Q.map past y) ⊗ₘ (Q.comap terminal hterminal)).map Fcut := by
                rw [hRmeasure]
          _ = ((Q.map past y) ⊗ₘ (Q.comap terminal hterminal)).map
              (G ∘ Hproj) := Measure.map_congr hEqAe
          _ = (((Q.map past y) ⊗ₘ (Q.comap terminal hterminal)).map Hproj).map G := by
                exact (Measure.map_map hGmeas hHproj).symm
          _ = (((Q.map past) ⊗ₖ Kernel.prodMkLeft (SpatialCoordinates d)
              (Q.comap terminal hterminal)).map Hproj y).map G := by
                have hmapH := Kernel.map_apply
                  ((Q.map past).compProd
                    ((Q.comap terminal hterminal).comap Prod.snd measurable_snd))
                  hHproj y
                rw [hRmeasure] at hmapH
                exact congrArg (fun mu => mu.map G) hmapH.symm
          _ = (((Q.map past).map pproj ⊗ₖ Kernel.prodMkLeft (SpatialCoordinates d)
              ((Q.map fproj).comap terminal' hterminal')).map G) y := by
                calc
                  _ = (Measure.map G
                      (((Q.map past).map pproj ⊗ₖ Kernel.prodMkLeft (SpatialCoordinates d)
                        ((Q.map fproj).comap terminal' hterminal')) y)) := by
                          rw [hkernelMap]
                  _ = _ := (Kernel.map_apply _ hGmeas y).symm
          _ = ((SubMarkovKernelSemigroup.finiteSetKernel P Jpast ⊗ₖ
              Kernel.prodMkLeft (SpatialCoordinates d)
                ((SubMarkovKernelSemigroup.finiteSetKernel P Jfuture).comap
                  terminal' hterminal')).map G) y := by
                rw [hQpast, hQfuture']
      have hleft :
          (Q.map (fun path => (past path, ContinuousPath.shift t path))).map Fcut y =
          ((SubMarkovKernelSemigroup.finiteSetKernel P Jpast) ⊗ₖ
            Kernel.prodMkLeft (SpatialCoordinates d)
              ((SubMarkovKernelSemigroup.finiteSetKernel P Jfuture).comap
                terminal' hterminal')).map G y := by
        rw [← Kernel.map_comp_right Q
          (hpast.prodMk (ContinuousPath.measurable_shift_fixed t)) hFcut]
        simpa [Fcut] using congrArg (fun K => K y) hfin
      have hmapR := Kernel.map_apply
        ((Q.map past).compProd
          ((Q.comap terminal hterminal).comap Prod.snd measurable_snd)) hFcut y
      simpa [Fcut] using (hleft.trans hright.symm).trans hmapR.symm
    let default : DiffusionPath d := ContinuousMap.const ℝ≥0 (0 : SpatialCoordinates d)
    have hkernel := aux_lem_tightness_deterministic_restart_jointLaw
      (alpha := SpatialCoordinates d) t default
      (Q.map (fun path => (past path, ContinuousPath.shift t path)))
      ((Q.map past).compProd ((Q.comap terminal hterminal).comap Prod.snd measurable_snd)) hcut
    have hx := congrArg (fun K => K x) hkernel
    calc
      (Q x).map (fun path => (past path, ContinuousPath.shift t path)) =
          (Q.map (fun path => (past path, ContinuousPath.shift t path))) x := by
            rw [Kernel.map_apply Q
              (hpast.prodMk (ContinuousPath.measurable_shift_fixed t)) x]
      _ = ((Q.map past).compProd
          ((Q.comap terminal hterminal).comap Prod.snd measurable_snd)) x := hx
      _ = (Q x).map past ⊗ₘ (Q.comap terminal hterminal) := by
            ext S hS
            rw [Kernel.compProd_apply hS, Measure.compProd_apply hS]
            rw [Kernel.map_apply Q hpast x]
            rfl
  have hRestricted :=
    aux_lem_tightness_deterministic_restart_restrictedMap
      (alpha := SpatialCoordinates d) t (Q x)
      past hpast Q terminal hterminal hJoint
  have hfiltration :
      MeasurableSpace.comap past inferInstance =
        ContinuousPath.canonicalFiltration (alpha := SpatialCoordinates d) t := by
    rw [ContinuousPath.canonicalFiltration]
    change MeasurableSpace.comap
        (fun path : DiffusionPath d =>
          fun r : Set.Iic t => path (r : ℝ≥0))
        (⨆ r : Set.Iic t,
          MeasurableSpace.comap (fun path : Set.Iic t → SpatialCoordinates d => path r)
            inferInstance) =
      ⨆ r : Set.Iic t,
        MeasurableSpace.comap
          (fun path : DiffusionPath d => path (r : ℝ≥0)) inferInstance
    rw [MeasurableSpace.comap_iSup]
    simp only [MeasurableSpace.comap_comp]
    rfl
  have hA' : MeasurableSet[MeasurableSpace.comap past inferInstance] A := by
    rw [hfiltration]
    exact hA
  have hkernel :
      (Q.comap terminal hterminal).comap past hpast =
        Q.comap (fun path : DiffusionPath d => path t)
          (ContinuousPath.measurable_coordinateProcess t) := by
    rw [← Kernel.comap_comp_right Q hpast hterminal]
    congr 1
  rw [hkernel] at hRestricted
  exact hRestricted A hA'

theorem aux_prop_limit_properties_strong_markov_deterministic_integral
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (hP : P.IsConservative)
    (Q : Kernel (SpatialCoordinates d) (DiffusionPath d))
    [IsMarkovKernel Q]
    (hfd : ∀ I : Finset ℝ≥0,
      Q.map (ContinuousPath.finsetEvaluation I) =
        SubMarkovKernelSemigroup.finiteSetKernel P I)
    (x : SpatialCoordinates d) (t : ℝ≥0) (A : Set (DiffusionPath d))
    (hA : MeasurableSet[ContinuousPath.canonicalFiltration
      (alpha := SpatialCoordinates d) t] A)
    (F : DiffusionPath d → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ path in A, F (ContinuousPath.shift t path) ∂(Q x)) =
      ∫⁻ path in A, ∫⁻ future, F future ∂(Q (path t)) ∂(Q x) := by
  let past : DiffusionPath d → (Set.Iic t → SpatialCoordinates d) :=
    fun path r => path r.1
  have hpast : Measurable past := by
    rw [measurable_pi_iff]
    intro r
    exact ContinuousPath.measurable_coordinateProcess (r : ℝ≥0)
  let terminal : (Set.Iic t → SpatialCoordinates d) → SpatialCoordinates d :=
    fun history => history ⟨t, by simp⟩
  have hterminal : Measurable terminal := measurable_pi_apply _
  have hTerminalPath : terminal ∘ past = fun path : DiffusionPath d => path t := by
    rfl
  have hfiltration :
      MeasurableSpace.comap past inferInstance =
        ContinuousPath.canonicalFiltration (alpha := SpatialCoordinates d) t := by
    rw [ContinuousPath.canonicalFiltration]
    change MeasurableSpace.comap
        (fun path : DiffusionPath d => fun r : Set.Iic t => path (r : ℝ≥0))
        (⨆ r : Set.Iic t,
          MeasurableSpace.comap (fun path : Set.Iic t → SpatialCoordinates d => path r)
            inferInstance) =
      ⨆ r : Set.Iic t,
        MeasurableSpace.comap
          (fun path : DiffusionPath d => path (r : ℝ≥0)) inferInstance
    rw [MeasurableSpace.comap_iSup]
    simp only [MeasurableSpace.comap_comp]
    rfl
  have hA' : MeasurableSet[MeasurableSpace.comap past inferInstance] A := by
    rw [hfiltration]
    exact hA
  have hkernel :
      (Q.comap terminal hterminal).comap past hpast =
        Q.comap (fun path : DiffusionPath d => path t)
          (ContinuousPath.measurable_coordinateProcess t) := by
    rw [← Kernel.comap_comp_right Q hpast hterminal]
    congr 1
  have hRestricted : ∀ A : Set (DiffusionPath d),
      MeasurableSet[MeasurableSpace.comap past inferInstance] A →
        ((Q x).restrict A).map (ContinuousPath.shift t) =
          (Q.comap terminal hterminal).comap past hpast ∘ₘ ((Q x).restrict A) := by
    intro A hA'
    have hAc : MeasurableSet[ContinuousPath.canonicalFiltration
        (alpha := SpatialCoordinates d) t] A := by
      rw [← hfiltration]
      exact hA'
    have hR := aux_prop_limit_properties_strong_markov_deterministic
      P hP Q hfd x t A hAc
    rw [← hkernel] at hR
    exact hR
  exact aux_lem_tightness_deterministic_restart_lintegral_identity
    (alpha := SpatialCoordinates d) t (Q x) past hpast Q terminal hterminal
    hTerminalPath hRestricted A hA' F hF

theorem aux_prop_limit_properties_strong_markov_finite_stopping
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (hP : P.IsConservative)
    (Q : Kernel (SpatialCoordinates d) (DiffusionPath d))
    [IsMarkovKernel Q]
    (hQcont : ∀ F : BoundedContinuousFunction (DiffusionPath d) ℝ,
      Continuous (fun x : SpatialCoordinates d => ∫ path, F path ∂(Q x)))
    (hfd : ∀ I : Finset ℝ≥0,
      Q.map (ContinuousPath.finsetEvaluation I) =
        SubMarkovKernelSemigroup.finiteSetKernel P I)
    (hdet : ∀ (x : SpatialCoordinates d) (s : ℝ≥0)
      (A : Set (DiffusionPath d)),
      MeasurableSet[ContinuousPath.canonicalFiltration
        (alpha := SpatialCoordinates d) s] A →
      ((Q x).restrict A).map (ContinuousPath.shift s) =
        Kernel.comap Q (fun path : DiffusionPath d => path s)
          (ContinuousPath.measurable_coordinateProcess s) ∘ₘ ((Q x).restrict A)) :
    ∀ (x : SpatialCoordinates d) (T : DiffusionPath d → ℝ≥0)
      (hT : IsStoppingTime (ContinuousPath.canonicalFiltration
        (alpha := SpatialCoordinates d))
        (fun omega ↦ (T omega : WithTop ℝ≥0)))
      (A : Set (DiffusionPath d)),
        MeasurableSet[hT.measurableSpace] A →
        ((Q x).restrict A).map
            (fun omega ↦ ContinuousPath.shift (T omega) omega) =
          Kernel.comap Q (fun omega ↦ omega (T omega))
              (ContinuousPath.measurable_eval_stoppingTime_borel T hT) ∘ₘ
            ((Q x).restrict A) := by
  intro x T hT A hA
  set mu : Measure (DiffusionPath d) := (Q x).restrict A
  set Tn : ℕ → DiffusionPath d → ℝ≥0 :=
    fun n omega ↦ MarkovProcess.dyadicCeiling n (T omega)
  have hTnStop : ∀ n, IsStoppingTime
      (ContinuousPath.canonicalFiltration (alpha := SpatialCoordinates d))
      (fun omega ↦ ((Tn n omega : ℝ≥0) : WithTop ℝ≥0)) :=
    fun n ↦ MarkovProcess.isStoppingTime_dyadicCeiling hT n
  have hTnMeas : ∀ n, Measurable (Tn n) :=
    fun n ↦ ContinuousPath.measurable_of_isStoppingTime _ (hTnStop n)
  have hATn : ∀ n, MeasurableSet[(hTnStop n).measurableSpace] A := fun n ↦
    IsStoppingTime.measurableSpace_mono hT (hTnStop n)
      (fun omega ↦ WithTop.coe_le_coe.mpr
        (MarkovProcess.le_dyadicCeiling n (T omega))) A hA
  have hstep : ∀ n, mu.map (fun omega ↦
      ContinuousPath.shift (Tn n omega) omega) =
      Kernel.comap Q (fun omega ↦ omega (Tn n omega))
        (ContinuousPath.measurable_eval_stoppingTime_borel _ (hTnStop n)) ∘ₘ mu :=
    fun n ↦ ContinuousPath.restrict_map_shift_stoppingTime_eq_pathKernel_comp_of_restart_on_range
      Q x (Tn n) (hTnStop n) (MarkovProcess.countable_range_dyadicCeiling_comp n T)
      (fun S _ ↦ hdet x S) A (hATn n)
  apply MarkovProcess.Measure.map_denseRestriction_injective
  apply MarkovProcess.Measure.eq_of_map_finiteRestriction_eq
  intro J
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let L : Kernel (SpatialCoordinates d) (J → SpatialCoordinates d) :=
    (SubMarkovKernelSemigroup.finiteSetKernel P
      (SubMarkovKernelSemigroup.denseTimePhysicalSet J)).map
      (DenseTimePath.pullbackPhysicalSet J)
  let evalDense : DiffusionPath d → (J → SpatialCoordinates d) :=
    fun path j ↦ path (DenseTime.castOrderEmbedding j)
  have hevalDense : Continuous evalDense := by
    exact ContinuousPath.continuous_finiteEvaluation
      (fun j : J ↦ DenseTime.castOrderEmbedding j)
  let fBounded : BoundedContinuousFunction (J → SpatialCoordinates d) ℝ :=
    ⟨f.toContinuousMap, ZeroAtInftyContinuousMap.bounded f⟩
  let F : BoundedContinuousFunction (DiffusionPath d) ℝ :=
    fBounded.compContinuous ⟨evalDense, hevalDense⟩
  let g : SpatialCoordinates d → ℝ :=
    fun y ↦ ∫ z, f z ∂L y
  have hQJ :
      (Q.map ContinuousPath.denseRestriction).map J.restrict = L := by
    let evaluatePhysical : DiffusionPath d →
        SubMarkovKernelSemigroup.denseTimePhysicalSet J → SpatialCoordinates d :=
      fun path t ↦ path t
    have hEvaluate : Measurable evaluatePhysical := by
      rw [measurable_pi_iff]
      intro t
      exact ContinuousPath.measurable_coordinateProcess (t : ℝ≥0)
    have hfun :
        J.restrict ∘ ContinuousPath.denseRestriction =
          DenseTimePath.pullbackPhysicalSet J ∘ evaluatePhysical := by
      funext path
      exact (DenseTimePath.pullbackPhysicalSet_evaluation J path).symm
    rw [← Kernel.map_comp_right Q ContinuousPath.measurable_denseRestriction
        (Finset.measurable_restrict J), hfun,
      Kernel.map_comp_right Q hEvaluate
        (DenseTimePath.measurable_pullbackPhysicalSet J)]
    change (Q.map (fun path : DiffusionPath d =>
        fun t : SubMarkovKernelSemigroup.denseTimePhysicalSet J => path t)).map
        (DenseTimePath.pullbackPhysicalSet J) = L
    rw [show (fun path t ↦ path t) =
        ContinuousPath.finsetEvaluation
          (SubMarkovKernelSemigroup.denseTimePhysicalSet J) by rfl,
      hfd (SubMarkovKernelSemigroup.denseTimePhysicalSet J)]
  have hkernelAt : ∀ (e : DiffusionPath d → SpatialCoordinates d)
      (he : Measurable e),
      ((Q.comap e he).map ContinuousPath.denseRestriction).map J.restrict =
        L.comap e he := by
    intro e he
    rw [← Kernel.comap_map_comm Q he ContinuousPath.measurable_denseRestriction,
      ← Kernel.comap_map_comm (Q.map ContinuousPath.denseRestriction) he
        (Finset.measurable_restrict J), hQJ]
  have hmeasureAt : ∀ (e : DiffusionPath d → SpatialCoordinates d)
      (he : Measurable e),
      (((Q.comap e he ∘ₘ mu).map ContinuousPath.denseRestriction).map J.restrict) =
        L.comap e he ∘ₘ mu := by
    intro e he
    rw [Measure.map_comp mu _ ContinuousPath.measurable_denseRestriction,
      Measure.map_comp mu _ (Finset.measurable_restrict J), hkernelAt e he]
  have hg_cont : Continuous g := by
    have hFcont := hQcont F
    have hInt : ∀ y, (∫ path, F path ∂(Q y)) = g y := by
      intro y
      have hi := congrArg (fun K => K y) hQJ
      rw [Kernel.map_apply (Q.map ContinuousPath.denseRestriction)
          (Finset.measurable_restrict J) y,
        Kernel.map_apply Q ContinuousPath.measurable_denseRestriction y] at hi
      have hi' := congrArg (fun nu : Measure (J → SpatialCoordinates d) =>
        ∫ z, f z ∂nu) hi
      change (∫ z, f z ∂Measure.map J.restrict
          (Measure.map ContinuousPath.denseRestriction (Q y))) =
        ∫ z, f z ∂L y at hi'
      rw [ContinuousPath.integral_map_denseRestriction_map_restrict] at hi'
      simpa only [F, BoundedContinuousFunction.compContinuous_apply, fBounded,
        g, L, evalDense, ContinuousPath.denseRestriction_apply ] using! hi'
    exact hFcont.congr hInt
  let C : ℝ := ‖PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f‖
  have hg_bound : ∀ y, ‖g y‖ ≤ C := by
    intro y
    exact hP.norm_integral_map_finiteSetKernel_pullbackPhysicalSet_le J f y
  have hlimT : ∀ omega, Tendsto (fun n ↦ Tn n omega) atTop (nhds (T omega)) :=
    fun omega ↦ MarkovProcess.tendsto_dyadicCeiling (T omega)
  have hright :=
    MarkovProcess.tendsto_integral_continuousPath_eval_randomTime_of_tendsto
      mu Tn T hTnMeas hlimT g hg_cont C hg_bound
  have hleft :=
    MarkovProcess.tendsto_integral_continuousPath_finiteDenseEvaluation_shift_randomTime_of_tendsto
      mu Tn T hTnMeas hlimT J f
  have htest : StronglyMeasurable (fun omega : DiffusionPath d ↦
      f (J.restrict (ContinuousPath.denseRestriction omega))) :=
    (f.continuous.comp (ContinuousPath.continuous_finiteEvaluation
      (fun j : J ↦ DenseTime.castOrderEmbedding j))).stronglyMeasurable
  have heq : ∀ n, (∫ omega, f (fun j : J ↦
        omega (Tn n omega + DenseTime.castOrderEmbedding j)) ∂mu) =
      ∫ omega, g (omega (Tn n omega)) ∂mu := by
    intro n
    have hm := congrArg (fun rho : Measure (DiffusionPath d) ↦
      rho.map ContinuousPath.denseRestriction |>.map J.restrict) (hstep n)
    have hi := congrArg (fun rho : Measure (J → SpatialCoordinates d) ↦
      ∫ z, f z ∂rho) hm
    rw [ContinuousPath.integral_map_denseRestriction_map_restrict] at hi
    have hmeasure := hmeasureAt
      (fun omega : DiffusionPath d ↦ omega (Tn n omega))
      (ContinuousPath.measurable_eval_stoppingTime_borel _ (hTnStop n))
    rw [hmeasure] at hi
    let : IsMarkovKernel L := by
      dsimp only [L]
      let : IsMarkovKernel
          (SubMarkovKernelSemigroup.finiteSetKernel P
            (SubMarkovKernelSemigroup.denseTimePhysicalSet J)) :=
        hP.isMarkovKernel_finiteSetKernel P
          (SubMarkovKernelSemigroup.denseTimePhysicalSet J)
      exact Kernel.IsMarkovKernel.map _
        (DenseTimePath.measurable_pullbackPhysicalSet J)
    let : IsMarkovKernel
        (L.comap (fun omega : DiffusionPath d ↦ omega (Tn n omega))
          (ContinuousPath.measurable_eval_stoppingTime_borel _ (hTnStop n))) :=
      inferInstance
    let : IsFiniteMeasure
        (L.comap (fun omega : DiffusionPath d ↦ omega (Tn n omega))
          (ContinuousPath.measurable_eval_stoppingTime_borel _ (hTnStop n)) ∘ₘ mu) :=
      inferInstance
    have hfint : Integrable f
        (L.comap (fun omega : DiffusionPath d ↦ omega (Tn n omega))
          (ContinuousPath.measurable_eval_stoppingTime_borel _ (hTnStop n)) ∘ₘ mu) :=
      f.integrable
    rw [Measure.comp_eq_comp_const_apply] at hfint
    have hcompIntegral :
        (∫ z, f z ∂(L.comap (fun omega ↦ omega (Tn n omega))
          (ContinuousPath.measurable_eval_stoppingTime_borel _ (hTnStop n)) ∘ₘ mu)) =
          ∫ omega, ∫ z, f z ∂L (omega (Tn n omega)) ∂mu := by
      rw [Measure.comp_eq_comp_const_apply]
      exact Kernel.integral_comp hfint
    rw [hcompIntegral] at hi
    rw [integral_map
      (ContinuousPath.measurable_shift_of_measurable (Tn n) (hTnMeas n)).aemeasurable
      htest.aestronglyMeasurable] at hi
    simpa only [ContinuousPath.denseRestriction_apply, ContinuousPath.shift_apply,
      g, L, evalDense, F] using! hi
  have hlimits :
      (∫ omega, f (fun j : J ↦
        omega (T omega + DenseTime.castOrderEmbedding j)) ∂mu) =
        ∫ omega, g (omega (T omega)) ∂mu :=
    tendsto_nhds_unique hleft (by simpa only [heq] using hright)
  have hmeasure := hmeasureAt
    (fun omega : DiffusionPath d ↦ omega (T omega))
    (ContinuousPath.measurable_eval_stoppingTime_borel T hT)
  rw [ContinuousPath.integral_map_denseRestriction_map_restrict,
    hmeasure]
  rw [integral_map
    (ContinuousPath.measurable_shift_stoppingTime T hT).aemeasurable
    htest.aestronglyMeasurable]
  let : IsMarkovKernel L := by
    dsimp only [L]
    let : IsMarkovKernel
        (SubMarkovKernelSemigroup.finiteSetKernel P
          (SubMarkovKernelSemigroup.denseTimePhysicalSet J)) :=
      hP.isMarkovKernel_finiteSetKernel P
        (SubMarkovKernelSemigroup.denseTimePhysicalSet J)
    exact Kernel.IsMarkovKernel.map _
      (DenseTimePath.measurable_pullbackPhysicalSet J)
  let : IsMarkovKernel
      (L.comap (fun omega : DiffusionPath d ↦ omega (T omega))
        (ContinuousPath.measurable_eval_stoppingTime_borel T hT)) := inferInstance
  let : IsFiniteMeasure
      (L.comap (fun omega : DiffusionPath d ↦ omega (T omega))
        (ContinuousPath.measurable_eval_stoppingTime_borel T hT) ∘ₘ mu) := inferInstance
  have hfint : Integrable f
      (L.comap (fun omega : DiffusionPath d ↦ omega (T omega))
        (ContinuousPath.measurable_eval_stoppingTime_borel T hT) ∘ₘ mu) :=
    f.integrable
  rw [Measure.comp_eq_comp_const_apply] at hfint
  have hcompIntegral :
      (∫ z, f z ∂(L.comap (fun omega ↦ omega (T omega))
        (ContinuousPath.measurable_eval_stoppingTime_borel T hT) ∘ₘ mu)) =
        ∫ omega, ∫ z, f z ∂L (omega (T omega)) ∂mu := by
    rw [Measure.comp_eq_comp_const_apply]
    exact Kernel.integral_comp hfint
  rw [hcompIntegral]
  simpa only [Kernel.const_apply, Kernel.comap_apply,
    ContinuousPath.denseRestriction_apply, ContinuousPath.shift_apply,
    g, L, evalDense, F] using! hlimits

theorem aux_prop_limit_properties_strong_markov_stopping_lt_top
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Q : Kernel (SpatialCoordinates d) (DiffusionPath d))
    [IsMarkovKernel Q]
    (hfinite : ∀ (x : SpatialCoordinates d) (T : DiffusionPath d → ℝ≥0)
      (hT : IsStoppingTime (ContinuousPath.canonicalFiltration
        (alpha := SpatialCoordinates d))
        (fun omega ↦ (T omega : WithTop ℝ≥0)))
      (A : Set (DiffusionPath d)),
        MeasurableSet[hT.measurableSpace] A →
        ((Q x).restrict A).map
            (fun omega ↦ ContinuousPath.shift (T omega) omega) =
          Kernel.comap Q (fun omega ↦ omega (T omega))
              (ContinuousPath.measurable_eval_stoppingTime_borel T hT) ∘ₘ
            ((Q x).restrict A)) :
    ∀ (x : SpatialCoordinates d)
      (tau : DiffusionPath d → WithTop ℝ≥0),
      (htau : IsStoppingTime (ContinuousPath.canonicalFiltration
        (alpha := SpatialCoordinates d)) tau) →
      ∀ (A : Set (DiffusionPath d)),
        MeasurableSet[htau.measurableSpace] A →
        ((Q x).restrict (A ∩ {omega | tau omega < ⊤})).map
            (fun omega ↦ ContinuousPath.shift ((tau omega).untopD 0) omega) =
          Kernel.comap Q (fun omega ↦ omega ((tau omega).untopD 0))
              (ContinuousPath.measurable_eval_untopD_stoppingTime tau htau) ∘ₘ
            ((Q x).restrict (A ∩ {omega | tau omega < ⊤})) := by
  intro x tau htau A hA
  have hslice : ∀ K : ℕ,
      (((Q x).restrict (StoppingTime.stoppingTimeSlice A tau K)).map
          (fun omega ↦ ContinuousPath.shift ((tau omega).untopD 0) omega)) =
        (Kernel.comap Q (fun omega ↦ omega ((tau omega).untopD 0))
            (ContinuousPath.measurable_eval_untopD_stoppingTime tau htau) ∘ₘ
          ((Q x).restrict (StoppingTime.stoppingTimeSlice A tau K))) := by
    intro K
    have hDK : MeasurableSet (StoppingTime.stoppingTimeSlice A tau K) :=
      StoppingTime.measurableSet_stoppingTimeSlice' htau hA K
    have hAK : MeasurableSet[(StoppingTime.isStoppingTime_truncTime htau
        (K : ℝ≥0)).measurableSpace]
        (StoppingTime.stoppingTimeSlice A tau K) := by
      rw [StoppingTime.measurableSpace_truncTime htau (K : ℝ≥0)]
      exact StoppingTime.measurableSet_stoppingTimeSlice htau hA K
    have hmain := hfinite x (StoppingTime.truncTime tau (K : ℝ≥0))
      (StoppingTime.isStoppingTime_truncTime htau (K : ℝ≥0))
      (StoppingTime.stoppingTimeSlice A tau K) hAK
    have hL : (((Q x).restrict (StoppingTime.stoppingTimeSlice A tau K)).map
          (fun omega ↦ ContinuousPath.shift
            (StoppingTime.truncTime tau (K : ℝ≥0) omega) omega)) =
        (((Q x).restrict (StoppingTime.stoppingTimeSlice A tau K)).map
          (fun omega ↦ ContinuousPath.shift ((tau omega).untopD 0) omega)) := by
      refine Measure.map_congr
        ((ae_restrict_iff' hDK).mpr (ae_of_all _ fun omega homega ↦ ?_))
      exact congrArg (fun s ↦ ContinuousPath.shift s omega)
        (StoppingTime.truncTime_eq_untopD_of_mem_stoppingTimeSlice homega)
    have hR : (Kernel.comap Q
            (fun omega ↦ omega (StoppingTime.truncTime tau (K : ℝ≥0) omega))
            (ContinuousPath.measurable_eval_stoppingTime_borel
              (StoppingTime.truncTime tau (K : ℝ≥0))
              (StoppingTime.isStoppingTime_truncTime htau (K : ℝ≥0))) ∘ₘ
          ((Q x).restrict (StoppingTime.stoppingTimeSlice A tau K))) =
        (Kernel.comap Q (fun omega ↦ omega ((tau omega).untopD 0))
            (ContinuousPath.measurable_eval_untopD_stoppingTime tau htau) ∘ₘ
          ((Q x).restrict (StoppingTime.stoppingTimeSlice A tau K))) := by
      refine Measure.comp_congr
        ((ae_restrict_iff' hDK).mpr (ae_of_all _ fun omega homega ↦ ?_))
      simp only [Kernel.comap_apply]
      rw [StoppingTime.truncTime_eq_untopD_of_mem_stoppingTimeSlice homega]
    rw [← hL, hmain, hR]
  rw [← StoppingTime.iUnion_stoppingTimeSlice (tau := tau) A]
  exact StoppingTime.map_restrict_iUnion_eq_comp_of_forall _ _ _
    (ContinuousPath.measurable_shift_untopD_stoppingTime tau htau)
    (StoppingTime.stoppingTimeSlice A tau)
    (fun K ↦ StoppingTime.measurableSet_stoppingTimeSlice' htau hA K)
    (StoppingTime.pairwise_disjoint_stoppingTimeSlice A) hslice

theorem aux_prop_limit_properties_strong_markov_deterministic_map
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Q : Kernel (SpatialCoordinates d) (DiffusionPath d))
    (hQ : IsMarkovKernel Q) (x : SpatialCoordinates d) (t : ℝ≥0)
    (hdet : ∀ A : Set (DiffusionPath d),
      MeasurableSet[ContinuousPath.canonicalFiltration
        (alpha := SpatialCoordinates d) t] A →
      ∀ F : DiffusionPath d → ℝ≥0∞, Measurable F →
        (∫⁻ path in A, F (ContinuousPath.shift t path) ∂(Q x)) =
          (∫⁻ path in A,
            ∫⁻ future, F future ∂(Q (path t)) ∂(Q x))) :
    ∀ A : Set (DiffusionPath d),
      MeasurableSet[ContinuousPath.canonicalFiltration
        (alpha := SpatialCoordinates d) t] A →
      ((Q x).restrict A).map (ContinuousPath.shift t) =
        Kernel.comap Q (ContinuousPath.coordinateProcess (alpha := SpatialCoordinates d) t)
          (ContinuousPath.measurable_coordinateProcess t) ∘ₘ ((Q x).restrict A) := by
  let : IsMarkovKernel Q := hQ
  intro A hA
  have hshift := ContinuousPath.measurable_shift_fixed
    (alpha := SpatialCoordinates d) t
  ext B hB
  rw [Measure.map_apply hshift hB,
    Measure.restrict_apply (hshift hB),
    Measure.bind_apply hB (Kernel.aemeasurable _)]
  have hind : Measurable
      (Set.indicator B (fun _ : DiffusionPath d => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hB
  have hi := hdet A hA
    (Set.indicator B (fun _ : DiffusionPath d => (1 : ℝ≥0∞))) hind
  have hi' :
      (∫⁻ path in A,
        (Set.indicator (ContinuousPath.shift t ⁻¹' B)
          (fun _ : DiffusionPath d => (1 : ℝ≥0∞))) path ∂(Q x)) =
        (∫⁻ path in A,
          ∫⁻ future, (Set.indicator B
            (fun _ : DiffusionPath d => (1 : ℝ≥0∞))) future
              ∂(Q (path t)) ∂(Q x)) := by
    simpa only [Set.indicator_apply, Set.mem_preimage, one_mul] using! hi
  rw [setLIntegral_indicator (hshift hB), setLIntegral_one] at hi'
  simp only [lintegral_indicator hB, setLIntegral_one] at hi'
  change (Q x) (ContinuousPath.shift t ⁻¹' B ∩ A) =
    ∫⁻ path in A, Q (path t) B ∂(Q x)
  exact hi'

theorem aux_prop_limit_properties_strong_markov_future_continuous
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P₀ : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (R : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hR : IsMarkovKernel R) (omega : BilateralField d)
    (hcont : Continuous (fun x : SpatialCoordinates d =>
      jointPathProbabilityMeasure R hR omega x))
    (hfd : ∀ I x, R.map (ContinuousPath.finsetEvaluation I) (omega, x) =
      SubMarkovKernelSemigroup.finiteSetKernel P₀ I x)
    (J : Finset DenseTime) (f : C_c(J → SpatialCoordinates d, ℝ)) :
    Continuous (fun y => ∫ z, f z ∂(
      (SubMarkovKernelSemigroup.finiteSetKernel P₀
        (MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J)).map
        (DenseTimePath.pullbackPhysicalSet J) y)) := by
  let evalJ : DiffusionPath d → (J → SpatialCoordinates d) :=
    fun path j => path (DenseTime.castOrderEmbedding j)
  have hevalJ : Measurable evalJ := by
    rw [measurable_pi_iff]
    intro j
    exact ContinuousPath.measurable_coordinateProcess _
  have hcontEval : Continuous evalJ := by
    exact continuous_pi fun j => continuous_eval_const _
  let F : BoundedContinuousFunction (DiffusionPath d) ℝ :=
    (f : BoundedContinuousFunction (J → SpatialCoordinates d) ℝ).compContinuous
      ⟨evalJ, hcontEval⟩
  have hFcont : Continuous (fun y =>
      ∫ path, F path ∂jointPathProbabilityMeasure R hR omega y) :=
    (ProbabilityMeasure.continuous_iff_forall_continuous_integral.mp hcont) F
  have hEvalLaw : ∀ y,
      (R (omega, y)).map evalJ =
        ((SubMarkovKernelSemigroup.finiteSetKernel P₀
          (MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J)).map
          (DenseTimePath.pullbackPhysicalSet J)) y := by
    intro y
    have hcomp : evalJ = DenseTimePath.pullbackPhysicalSet J ∘
        ContinuousPath.finsetEvaluation
          (MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J) := by
      funext path j
      rfl
    calc
      (R (omega, y)).map evalJ = (R.map evalJ) (omega, y) := by
        rw [Kernel.map_apply R hevalJ]
      _ = (R.map (DenseTimePath.pullbackPhysicalSet J ∘
          ContinuousPath.finsetEvaluation
            (MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J)))
            (omega, y) := by rw [hcomp]
      _ = (((R.map (ContinuousPath.finsetEvaluation
          (MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J))).map
            (DenseTimePath.pullbackPhysicalSet J)) (omega, y)) := by
        rw [Kernel.map_comp_right R
          (ContinuousPath.measurable_finsetEvaluation _)
          (DenseTimePath.measurable_pullbackPhysicalSet J)]
      _ = _ := by
        have hh := congrArg (fun μ => μ.map (DenseTimePath.pullbackPhysicalSet J))
          (hfd (MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J) y)
        rw [Kernel.map_apply (R.map
          (ContinuousPath.finsetEvaluation
            (MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J)))
            (DenseTimePath.measurable_pullbackPhysicalSet J) (omega, y),
          Kernel.map_apply (SubMarkovKernelSemigroup.finiteSetKernel P₀
            (MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J))
            (DenseTimePath.measurable_pullbackPhysicalSet J) y]
        exact hh
  have heq : (fun y => ∫ z, f z ∂(((
      SubMarkovKernelSemigroup.finiteSetKernel P₀
        (MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J)).map
        (DenseTimePath.pullbackPhysicalSet J)) y)) =
      (fun y => ∫ path, F path ∂jointPathProbabilityMeasure R hR omega y) := by
    funext y
    rw [← hEvalLaw y]
    have hfmeas : AEStronglyMeasurable (f : (J → SpatialCoordinates d) → ℝ)
        (Measure.map evalJ (R (omega, y))) :=
      f.continuous.stronglyMeasurable.aestronglyMeasurable
    have hi := integral_map (μ := R (omega, y)) hevalJ.aemeasurable hfmeas
    simpa only [F, BoundedContinuousFunction.compContinuous_apply] using! hi
  rw [heq]
  exact hFcont

theorem aux_prop_limit_properties_strong_markov_conservative
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (R : Kernel (SpatialCoordinates d) (DiffusionPath d))
    (hR : IsMarkovKernel R)
    (hfd : ∀ I x, R.map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel P I x) :
    P.IsConservative := by
  intro t x
  let : IsMarkovKernel R := hR
  have hsingleton :
      (R x).map (ContinuousPath.finsetEvaluation ({t} : Finset ℝ≥0)) =
        SubMarkovKernelSemigroup.finiteSetKernel P ({t} : Finset ℝ≥0) x := by
    simpa only [Kernel.map_apply R
      (ContinuousPath.measurable_finsetEvaluation ({t} : Finset ℝ≥0)) x] using
      hfd ({t} : Finset ℝ≥0) x
  have htime : (R x).map (fun path : DiffusionPath d => path t) = P.kernel t x :=
    SubdiffusiveProcess.map_eval_eq_of_finsetEvaluation P (R x) x t hsingleton
  calc
    P.kernel t x Set.univ = ((R x).map (fun path : DiffusionPath d => path t)) Set.univ := by
      rw [htime]
    _ = (R x) ((fun path : DiffusionPath d => path t) ⁻¹' Set.univ) := by
      rw [Measure.map_apply (continuous_eval_const t).measurable MeasurableSet.univ]
    _ = 1 := by simp only [Set.preimage_univ, measure_univ]

theorem aux_prop_limit_properties_strong_markov_canonical_restart
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (R : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hR : IsMarkovKernel R) (omega : BilateralField d)
    (hP : P.IsConservative)
    (hfd : ∀ I x, R.map (ContinuousPath.finsetEvaluation I) (omega, x) =
      SubMarkovKernelSemigroup.finiteSetKernel P I x) :
    ∀ (x : SpatialCoordinates d) (t : ℝ≥0) (A : Set (DiffusionPath d)),
      MeasurableSet[ContinuousPath.canonicalFiltration
        (alpha := SpatialCoordinates d) t] A →
      ((R (omega, x)).restrict A).map (ContinuousPath.shift t) =
        Kernel.comap R (fun path : DiffusionPath d => (omega, path t))
          (measurable_const.prodMk
            (ContinuousPath.measurable_coordinateProcess t)) ∘ₘ
            ((R (omega, x)).restrict A) := by
  intro x t A hA
  let Q : Kernel (SpatialCoordinates d) (DiffusionPath d) :=
    R.comap (fun y => (omega, y)) (by measurability)
  have hQ : IsMarkovKernel Q := by
    dsimp [Q]
    infer_instance
  let : IsMarkovKernel Q := hQ
  have hfdQ : ∀ I y, Q.map (ContinuousPath.finsetEvaluation I) y =
      SubMarkovKernelSemigroup.finiteSetKernel P I y := by
    intro I y
    rw [Kernel.map_apply Q (ContinuousPath.measurable_finsetEvaluation I) y]
    rw [Kernel.comap_apply]
    have hh := hfd I y
    rw [Kernel.map_apply R (ContinuousPath.measurable_finsetEvaluation I) (omega, y)] at hh
    exact hh
  have hdet : ∀ (A : Set (DiffusionPath d)),
      MeasurableSet[ContinuousPath.canonicalFiltration
        (alpha := SpatialCoordinates d) t] A →
      ∀ F : DiffusionPath d → ℝ≥0∞, Measurable F →
        (∫⁻ path in A, F (ContinuousPath.shift t path) ∂(Q x)) =
          (∫⁻ path in A, ∫⁻ future, F future ∂(Q (path t)) ∂(Q x)) := by
    intro B hB F hF
    have hfdQ' : ∀ I : Finset ℝ≥0,
        Q.map (ContinuousPath.finsetEvaluation I) =
          SubMarkovKernelSemigroup.finiteSetKernel P I := by
      intro I
      ext y S hS
      exact congrArg (fun nu : Measure (I → SpatialCoordinates d) => nu S)
        (hfdQ I y)
    exact aux_prop_limit_properties_strong_markov_deterministic_integral
      P hP Q hfdQ' x t B hB F hF
  have hmap := aux_prop_limit_properties_strong_markov_deterministic_map
    Q hQ x t hdet
  have hcomp :
      Kernel.comap Q (ContinuousPath.coordinateProcess (alpha := SpatialCoordinates d) t)
          (ContinuousPath.measurable_coordinateProcess t) =
        Kernel.comap R (fun path : DiffusionPath d => (omega, path t))
          (measurable_const.prodMk
            (ContinuousPath.measurable_coordinateProcess t)) := by
    ext y S hS
    rfl
  rw [hcomp] at hmap
  exact hmap A hA

theorem aux_prop_limit_properties_strong_markov_null_of_usual
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (mu : Measure (DiffusionPath d)) (t : ℝ≥0) (A : Set (DiffusionPath d))
    (hA : MeasurableSet[usualNaturalAt mu t] A) :
    NullMeasurableSet A mu := by
  have hnull : ∀ S : Set (DiffusionPath d),
      MeasurableSet[MeasurableSpace.generateFrom
        {U : Set (DiffusionPath d) | mu U = 0}] S →
        NullMeasurableSet S mu := by
    have hgen : ∀ (basis : Set (Set (DiffusionPath d))),
        (∀ U ∈ basis, NullMeasurableSet U mu) →
        ∀ S, MeasurableSpace.GenerateMeasurable basis S →
          NullMeasurableSet S mu := by
      intro basis hbasis S hS
      induction hS with
      | basic U hU => exact hbasis U hU
      | empty => exact nullMeasurableSet_empty
      | compl U hU ih => exact ih.compl
      | iUnion f hF ih => exact NullMeasurableSet.iUnion ih
    intro S hS
    apply hgen {U : Set (DiffusionPath d) | mu U = 0}
    · intro U hU
      exact NullMeasurableSet.of_null hU
    · exact hS
  have hsup : ∀ (s : ℝ≥0), ∀ S : Set (DiffusionPath d),
      MeasurableSet[ContinuousPath.canonicalFiltration
          (alpha := SpatialCoordinates d) s ⊔
        MeasurableSpace.generateFrom
          {U : Set (DiffusionPath d) | mu U = 0}] S →
      NullMeasurableSet S mu := by
    intro s S hS
    have hS' := (MeasurableSpace.measurableSet_sup).mp hS
    change MeasurableSpace.GenerateMeasurable
      ({U : Set (DiffusionPath d) |
          MeasurableSet[ContinuousPath.canonicalFiltration
            (alpha := SpatialCoordinates d) s] U} ∪
        {U : Set (DiffusionPath d) |
          MeasurableSet[MeasurableSpace.generateFrom
            {U : Set (DiffusionPath d) | mu U = 0}] U}) S at hS'
    have hgen : ∀ (basis : Set (Set (DiffusionPath d))),
        (∀ U ∈ basis, NullMeasurableSet U mu) →
        ∀ S, MeasurableSpace.GenerateMeasurable basis S →
          NullMeasurableSet S mu := by
      intro basis hbasis U hU
      induction hU with
      | basic V hV => exact hbasis V hV
      | empty => exact nullMeasurableSet_empty
      | compl V hV ih => exact ih.compl
      | iUnion f hF ih => exact NullMeasurableSet.iUnion ih
    apply hgen _ ?_ S hS'
    intro U hU
    rcases hU with hU | hU
    · exact MeasurableSet.nullMeasurableSet (μ := mu)
        ((ContinuousPath.canonicalFiltration
          (alpha := SpatialCoordinates d)).le s U hU)
    · exact hnull U hU
  have hA' : MeasurableSet[⨅ s : {s : ℝ≥0 // t < s},
      ContinuousPath.canonicalFiltration (alpha := SpatialCoordinates d) s.val ⊔
        MeasurableSpace.generateFrom {U : Set (DiffusionPath d) | mu U = 0}] A := by
    simpa only [usualNaturalAt] using! hA
  rw [MeasurableSpace.measurableSet_iInf] at hA'
  exact hsup _ _ (hA' ⟨t + 1, by simp⟩)

theorem aux_prop_limit_properties_strong_markov_canonical_representative
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (mu : Measure (DiffusionPath d)) (t : ℝ≥0) (A : Set (DiffusionPath d))
    (hA : MeasurableSet[
      ContinuousPath.canonicalFiltration (alpha := SpatialCoordinates d) t ⊔
        MeasurableSpace.generateFrom
          {U : Set (DiffusionPath d) | mu U = 0}] A) :
    ∃ B : Set (DiffusionPath d),
      MeasurableSet[ContinuousPath.canonicalFiltration
        (alpha := SpatialCoordinates d) t] B ∧ B =ᵐ[mu] A := by
  have hgen : ∀ (basis : Set (Set (DiffusionPath d))),
      (∀ U ∈ basis, ∃ V : Set (DiffusionPath d),
        MeasurableSet[ContinuousPath.canonicalFiltration
          (alpha := SpatialCoordinates d) t] V ∧ V =ᵐ[mu] U) →
      ∀ S, MeasurableSpace.GenerateMeasurable basis S →
        ∃ V : Set (DiffusionPath d),
          MeasurableSet[ContinuousPath.canonicalFiltration
            (alpha := SpatialCoordinates d) t] V ∧ V =ᵐ[mu] S := by
    intro basis hbasis S hS
    induction hS with
    | basic U hU => exact hbasis U hU
    | empty =>
        exact ⟨∅, @MeasurableSet.empty _
          (ContinuousPath.canonicalFiltration (alpha := SpatialCoordinates d) t),
          EventuallyEq.refl _ _⟩
    | compl U hU ih =>
        rcases ih with ⟨V, hV, hVU⟩
        exact ⟨Vᶜ, hV.compl, hVU.compl⟩
    | iUnion f hF ih =>
        choose V hVmeas hVae using ih
        exact ⟨⋃ i, V i, MeasurableSet.iUnion hVmeas,
          EventuallyEqSet.countable_iUnion hVae⟩
  have hzero : ∀ U : Set (DiffusionPath d),
      MeasurableSet[MeasurableSpace.generateFrom
        {V : Set (DiffusionPath d) | mu V = 0}] U →
      ∃ V : Set (DiffusionPath d),
        MeasurableSet[ContinuousPath.canonicalFiltration
          (alpha := SpatialCoordinates d) t] V ∧ V =ᵐ[mu] U := by
    intro U hU
    change MeasurableSpace.GenerateMeasurable
      {V : Set (DiffusionPath d) | mu V = 0} U at hU
    refine hgen {V : Set (DiffusionPath d) | mu V = 0} ?_ U hU
    intro V hV
    exact ⟨∅, @MeasurableSet.empty _
      (ContinuousPath.canonicalFiltration (alpha := SpatialCoordinates d) t),
      (ae_eq_empty).2 hV |>.symm⟩
  have hS := (MeasurableSpace.measurableSet_sup).mp hA
  change MeasurableSpace.GenerateMeasurable
    ({U : Set (DiffusionPath d) |
        MeasurableSet[ContinuousPath.canonicalFiltration
          (alpha := SpatialCoordinates d) t] U} ∪
      {U : Set (DiffusionPath d) |
        MeasurableSet[MeasurableSpace.generateFrom
          {U : Set (DiffusionPath d) | mu U = 0}] U}) A at hS
  apply hgen _ ?_ A hS
  intro U hU
  rcases hU with hU | hU
  · exact ⟨U, hU, EventuallyEq.refl _ _⟩
  · exact hzero U hU

theorem aux_prop_limit_properties_strong_markov_usual_mono
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (mu : Measure (DiffusionPath d)) {s t : ℝ≥0} (hst : s ≤ t) :
    usualNaturalAt mu s ≤ usualNaturalAt mu t := by
  unfold usualNaturalAt
  refine le_iInf fun u => ?_
  exact iInf_le_of_le ⟨u, lt_of_le_of_lt hst u.property⟩ le_rfl

theorem aux_prop_limit_properties_strong_markov_usual_null_le
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (mu : Measure (DiffusionPath d)) (t : ℝ≥0) :
    MeasurableSpace.generateFrom
        {U : Set (DiffusionPath d) | mu U = 0} ≤ usualNaturalAt mu t := by
  unfold usualNaturalAt
  refine le_iInf fun s => ?_
  exact le_sup_of_le_right le_rfl

theorem aux_prop_limit_properties_strong_markov_usual_le_null
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (mu : Measure (DiffusionPath d)) (t : ℝ≥0) :
    usualNaturalAt mu t ≤
      @NullMeasurableSpace.instMeasurableSpace
        (DiffusionPath d) ContinuousPath.instMeasurableSpace mu := by
  unfold usualNaturalAt
  refine (iInf_le (fun s : {s : ℝ≥0 // t < s} ↦
      ContinuousPath.canonicalFiltration (alpha := SpatialCoordinates d) s.1 ⊔
        MeasurableSpace.generateFrom {U : Set (DiffusionPath d) | mu U = 0})
      ⟨t + 1, by simp⟩).trans ?_
  apply sup_le
  · intro U hU
    exact ((ContinuousPath.canonicalFiltration
      (alpha := SpatialCoordinates d)).le' _ U hU).nullMeasurableSet
  · exact MeasurableSpace.generateFrom_le (fun U hU ↦
      NullMeasurableSet.of_null hU)

theorem aux_prop_limit_properties_strong_markov_stopping_ae_transfer
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (mu : Measure (DiffusionPath d))
    (f : Filtration ℝ≥0
      (@NullMeasurableSpace.instMeasurableSpace
        (DiffusionPath d) ContinuousPath.instMeasurableSpace mu))
    (tau sigma : DiffusionPath d → WithTop ℝ≥0)
    (htau : IsStoppingTime f tau)
    (hae : tau =ᵐ[mu] sigma)
    (hnull : ∀ t : ℝ≥0,
      MeasurableSpace.generateFrom {U : Set (DiffusionPath d) | mu U = 0} ≤ f t) :
    ∃ hsigma : IsStoppingTime f sigma,
      ∀ A : Set (DiffusionPath d), MeasurableSet[htau.measurableSpace] A →
        MeasurableSet[hsigma.measurableSpace] A := by
  let N : Set (DiffusionPath d) := {path | tau path ≠ sigma path}
  have hNzero : mu N = 0 := by
    dsimp [N]
    exact ae_iff.mp hae
  have hNmeas : ∀ t : ℝ≥0, MeasurableSet[f t] N := by
    intro t
    exact hnull t N (MeasurableSpace.measurableSet_generateFrom hNzero)
  have hσ : IsStoppingTime f sigma := by
    intro t
    have hpart : MeasurableSet[f t]
        ({path | sigma path ≤ t} ∩ N) := by
      apply hnull t
      apply MeasurableSpace.measurableSet_generateFrom
      exact measure_mono_null Set.inter_subset_right hNzero
    have hset : {path | sigma path ≤ t} =
        ({path | tau path ≤ t} \ N) ∪
          ({path | sigma path ≤ t} ∩ N) := by
      ext path
      by_cases hp : path ∈ N
      · simp [hp]
      · have heq : tau path = sigma path := by
          simpa only [N, Set.mem_ofPred_eq, not_not] using hp
        simp [hp, heq]
    exact hset.symm ▸ ((htau t).diff (hNmeas t) |>.union hpart)
  refine ⟨hσ, ?_⟩
  intro A hA
  refine ⟨hA.1, ?_⟩
  intro t
  have hpart : MeasurableSet[f t]
      ((A ∩ {path | sigma path ≤ t}) ∩ N) := by
    apply hnull t
    apply MeasurableSpace.measurableSet_generateFrom
    exact measure_mono_null (by
      intro path hp
      exact hp.2) hNzero
  have hset : A ∩ {path | sigma path ≤ t} =
      ((A ∩ {path | tau path ≤ t}) \ N) ∪
        ((A ∩ {path | sigma path ≤ t}) ∩ N) := by
    ext path
    by_cases hp : path ∈ N
    · simp [hp]
    · have heq : tau path = sigma path := by
        simpa only [N, Set.mem_ofPred_eq, not_not] using hp
      simp [hp, heq]
  exact hset.symm ▸ ((hA.2 t).diff (hNmeas t) |>.union hpart)

theorem aux_prop_limit_properties_strong_markov_null_reassembly
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    {beta : Type*} [MeasurableSpace beta]
    (mu : Measure (DiffusionPath d)) (kappa : Kernel (DiffusionPath d) beta)
    (g : DiffusionPath d → beta) (hg : Measurable g)
    (D : ℕ → Set (DiffusionPath d))
    (hD : ∀ n, NullMeasurableSet (D n) mu)
    (hdisj : Pairwise (Function.onFun Disjoint D))
    (h : ∀ n, (mu.restrict (D n)).map g = kappa ∘ₘ (mu.restrict (D n))) :
    (mu.restrict (⋃ n, D n)).map g = kappa ∘ₘ (mu.restrict (⋃ n, D n)) := by
  ext S hS
  calc
    (mu.restrict (⋃ n, D n)).map g S =
        mu (g ⁻¹' S ∩ ⋃ n, D n) := by
      rw [Measure.map_apply hg hS, Measure.restrict_apply (hg hS)]
    _ = mu (⋃ n, g ⁻¹' S ∩ D n) := by
      rw [Set.inter_iUnion]
    _ = ∑' n, mu (g ⁻¹' S ∩ D n) := by
      apply measure_iUnion₀ (μ := mu)
      · intro i j hij
        have hd : Disjoint (g ⁻¹' S ∩ D i) (g ⁻¹' S ∩ D j) :=
          (hdisj hij).mono Set.inter_subset_right Set.inter_subset_right
        exact hd.aedisjoint
      · intro i
        exact (hg hS).nullMeasurableSet.inter (hD i)
    _ = ∑' n, (kappa ∘ₘ (mu.restrict (D n))) S := by
      apply tsum_congr
      intro n
      calc
        mu (g ⁻¹' S ∩ D n) =
            (mu.restrict (D n)) (g ⁻¹' S) := by
              rw [Measure.restrict_apply (hg hS)]
        _ = (Measure.map g (mu.restrict (D n))) S := by
              rw [Measure.map_apply hg hS]
        _ = (kappa ∘ₘ (mu.restrict (D n))) S := by rw [h n]
    _ = (kappa ∘ₘ (mu.restrict (⋃ n, D n))) S := by
      calc
        ∑' n, (kappa ∘ₘ (mu.restrict (D n))) S =
            ∑' n, ∫⁻ a in D n, kappa a S ∂mu := by
              apply tsum_congr
              intro n
              rw [Measure.bind_apply hS kappa.aemeasurable]
        _ = ∫⁻ a in ⋃ n, D n, kappa a S ∂mu := by
              rw [lintegral_iUnion₀ hD
                (fun i j hij ↦ (hdisj hij).aedisjoint)]
        _ = (kappa ∘ₘ (mu.restrict (⋃ n, D n))) S := by
              rw [Measure.bind_apply hS kappa.aemeasurable]

theorem aux_prop_limit_properties_strong_markov_map_dense_restrict_integral
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (nu : Measure (DiffusionPath d)) (J : Finset DenseTime)
    (f : C_c(J → SpatialCoordinates d, ℝ)) :
    ∫ z, f z ∂((nu.map ContinuousPath.denseRestriction).map J.restrict) =
      ∫ omega, f (J.restrict (ContinuousPath.denseRestriction omega)) ∂nu := by
  have hdense := ContinuousPath.measurable_denseRestriction
    (alpha := SpatialCoordinates d)
  have hrestrict := Finset.measurable_restrict (X := fun _ ↦ SpatialCoordinates d) J
  rw [Measure.map_map hrestrict hdense]
  exact integral_map (hrestrict.comp hdense).aemeasurable
    f.continuous.stronglyMeasurable.aestronglyMeasurable

theorem aux_prop_limit_properties_strong_markov_composed_dense_integral
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (Q : Kernel (SpatialCoordinates d) (DiffusionPath d))
    (hP : P.IsConservative) (hfd : ∀ I x,
      Q.map (ContinuousPath.finsetEvaluation I) x =
        SubMarkovKernelSemigroup.finiteSetKernel P I x)
    (mu : Measure (DiffusionPath d)) [IsFiniteMeasure mu] (r : ℝ≥0)
    (J : Finset DenseTime) (f : C_c(J → SpatialCoordinates d, ℝ)) :
    ∫ z, f z ∂(((Kernel.comap Q
          (ContinuousPath.coordinateProcess (alpha := SpatialCoordinates d) r)
          (ContinuousPath.measurable_coordinateProcess r) ∘ₘ mu).map
        ContinuousPath.denseRestriction).map J.restrict) =
      ∫ omega, ∫ z, f z ∂((SubMarkovKernelSemigroup.finiteSetKernel P
          (MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J)).map
            (DenseTimePath.pullbackPhysicalSet J) (omega r)) ∂mu := by
  let KJ : Kernel (SpatialCoordinates d) (J → SpatialCoordinates d) :=
    (SubMarkovKernelSemigroup.finiteSetKernel P
      (MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J)).map
      (DenseTimePath.pullbackPhysicalSet J)
  have heval := ContinuousPath.measurable_coordinateProcess
    (alpha := SpatialCoordinates d) r
  have hdense := ContinuousPath.measurable_denseRestriction
    (alpha := SpatialCoordinates d)
  have hrestrict := Finset.measurable_restrict
    (X := fun _ ↦ SpatialCoordinates d) J
  have hQJ : (Q.map ContinuousPath.denseRestriction).map J.restrict = KJ := by
    calc
      (Q.map ContinuousPath.denseRestriction).map J.restrict =
          Q.map (J.restrict ∘ ContinuousPath.denseRestriction) := by
        rw [Kernel.map_comp_right Q hdense hrestrict]
      _ = (Q.map (ContinuousPath.finsetEvaluation
          (MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J))).map
            (DenseTimePath.pullbackPhysicalSet J) := by
        have hcomp : J.restrict ∘ ContinuousPath.denseRestriction =
            DenseTimePath.pullbackPhysicalSet (alpha := SpatialCoordinates d) J ∘
              ContinuousPath.finsetEvaluation
                (MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J) := by
          funext path j
          rfl
        rw [hcomp]
        rw [Kernel.map_comp_right Q
          (ContinuousPath.measurable_finsetEvaluation
            (alpha := SpatialCoordinates d) _)
          (DenseTimePath.measurable_pullbackPhysicalSet (alpha := SpatialCoordinates d) J)]
      _ = KJ := by
        ext x S hS
        dsimp only [KJ]
        rw [Kernel.map_apply (Q.map (ContinuousPath.finsetEvaluation
          (MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J)))
            (DenseTimePath.measurable_pullbackPhysicalSet J) x,
          Kernel.map_apply
            (SubMarkovKernelSemigroup.finiteSetKernel P
              (MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J))
            (DenseTimePath.measurable_pullbackPhysicalSet J) x]
        have hh := congrArg (fun rho : Measure _ ↦
            rho.map (DenseTimePath.pullbackPhysicalSet J))
          (hfd (MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J) x)
        exact congrArg (fun rho : Measure _ ↦ rho S) hh
  have hkernel :
      ((Kernel.comap Q (ContinuousPath.coordinateProcess
          (alpha := SpatialCoordinates d) r) heval).map
          ContinuousPath.denseRestriction).map J.restrict =
        Kernel.comap KJ (ContinuousPath.coordinateProcess
          (alpha := SpatialCoordinates d) r) heval := by
    rw [← Kernel.comap_map_comm Q heval hdense,
      ← Kernel.comap_map_comm (Q.map ContinuousPath.denseRestriction)
        heval hrestrict, hQJ]
  have hmeasure :
      (((Kernel.comap Q (ContinuousPath.coordinateProcess
          (alpha := SpatialCoordinates d) r) heval ∘ₘ mu).map
          ContinuousPath.denseRestriction).map J.restrict) =
        Kernel.comap KJ (ContinuousPath.coordinateProcess
          (alpha := SpatialCoordinates d) r) heval ∘ₘ mu := by
    rw [Measure.map_comp mu _ hdense, Measure.map_comp mu _ hrestrict, hkernel]
  rw [hmeasure, Measure.comp_eq_comp_const_apply]
  let : IsMarkovKernel KJ := by
    dsimp only [KJ]
    let : IsMarkovKernel (SubMarkovKernelSemigroup.finiteSetKernel P
        (MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J)) :=
      hP.isMarkovKernel_finiteSetKernel P _
    exact Kernel.IsMarkovKernel.map _ (DenseTimePath.measurable_pullbackPhysicalSet J)
  let : IsMarkovKernel (Kernel.comap KJ
      (ContinuousPath.coordinateProcess (alpha := SpatialCoordinates d) r) heval) :=
    inferInstance
  let : IsFiniteMeasure
      (Kernel.comap KJ (ContinuousPath.coordinateProcess
        (alpha := SpatialCoordinates d) r) heval ∘ₘ mu) := inferInstance
  have hfint : Integrable f
      (Kernel.comap KJ (ContinuousPath.coordinateProcess
        (alpha := SpatialCoordinates d) r) heval ∘ₘ mu) := f.integrable
  rw [Measure.comp_eq_comp_const_apply] at hfint
  have hi := Kernel.integral_comp hfint
  simpa only [Kernel.const_apply, Kernel.comap_apply,
    ContinuousPath.coordinateProcess_apply, KJ] using! hi

theorem aux_prop_limit_properties_strong_markov_composed_dense_integral_random
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (Q : Kernel (SpatialCoordinates d) (DiffusionPath d))
    (hP : P.IsConservative) (hfd : ∀ I x,
      Q.map (ContinuousPath.finsetEvaluation I) x =
        SubMarkovKernelSemigroup.finiteSetKernel P I x)
    (mu : Measure (DiffusionPath d)) [IsFiniteMeasure mu]
    (r : DiffusionPath d → ℝ≥0)
    (hr : Measurable r)
    (J : Finset DenseTime) (f : C_c(J → SpatialCoordinates d, ℝ)) :
    ∫ z, f z ∂(((Kernel.comap Q
          (fun path : DiffusionPath d ↦ path (r path))
          (ContinuousPath.measurable_eval_of_measurable r hr) ∘ₘ mu).map
        ContinuousPath.denseRestriction).map J.restrict) =
      ∫ omega, ∫ z, f z ∂((SubMarkovKernelSemigroup.finiteSetKernel P
          (MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J)).map
            (DenseTimePath.pullbackPhysicalSet J) (omega (r omega))) ∂mu := by
  let KJ : Kernel (SpatialCoordinates d) (J → SpatialCoordinates d) :=
    (SubMarkovKernelSemigroup.finiteSetKernel P
      (MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J)).map
      (DenseTimePath.pullbackPhysicalSet J)
  let heval : Measurable (fun path : DiffusionPath d ↦ path (r path)) :=
    ContinuousPath.measurable_eval_of_measurable r hr
  have hdense := ContinuousPath.measurable_denseRestriction
    (alpha := SpatialCoordinates d)
  have hrestrict := Finset.measurable_restrict
    (X := fun _ ↦ SpatialCoordinates d) J
  have hQJ : (Q.map ContinuousPath.denseRestriction).map J.restrict = KJ := by
    calc
      (Q.map ContinuousPath.denseRestriction).map J.restrict =
          Q.map (J.restrict ∘ ContinuousPath.denseRestriction) := by
        rw [Kernel.map_comp_right Q hdense hrestrict]
      _ = (Q.map (ContinuousPath.finsetEvaluation
          (MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J))).map
            (DenseTimePath.pullbackPhysicalSet J) := by
        have hcomp : J.restrict ∘ ContinuousPath.denseRestriction =
            DenseTimePath.pullbackPhysicalSet (alpha := SpatialCoordinates d) J ∘
              ContinuousPath.finsetEvaluation
                (MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J) := by
          funext path j
          rfl
        rw [hcomp]
        rw [Kernel.map_comp_right Q
          (ContinuousPath.measurable_finsetEvaluation
            (alpha := SpatialCoordinates d) _)
          (DenseTimePath.measurable_pullbackPhysicalSet
            (alpha := SpatialCoordinates d) J)]
      _ = KJ := by
        ext x S hS
        dsimp only [KJ]
        rw [Kernel.map_apply (Q.map (ContinuousPath.finsetEvaluation
          (MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J)))
            (DenseTimePath.measurable_pullbackPhysicalSet J) x,
          Kernel.map_apply
            (SubMarkovKernelSemigroup.finiteSetKernel P
              (MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J))
            (DenseTimePath.measurable_pullbackPhysicalSet J) x]
        have hh := congrArg (fun rho : Measure _ ↦
            rho.map (DenseTimePath.pullbackPhysicalSet J))
          (hfd (MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J) x)
        exact congrArg (fun rho : Measure _ ↦ rho S) hh
  have hkernel :
      ((Kernel.comap Q (fun path : DiffusionPath d ↦ path (r path)) heval).map
        ContinuousPath.denseRestriction).map J.restrict =
        Kernel.comap KJ (fun path : DiffusionPath d ↦ path (r path)) heval := by
    rw [← Kernel.comap_map_comm Q heval hdense,
      ← Kernel.comap_map_comm (Q.map ContinuousPath.denseRestriction)
        heval hrestrict, hQJ]
  have hmeasure :
      (((Kernel.comap Q (fun path : DiffusionPath d ↦ path (r path)) heval ∘ₘ mu).map
        ContinuousPath.denseRestriction).map J.restrict) =
        Kernel.comap KJ (fun path : DiffusionPath d ↦ path (r path)) heval ∘ₘ mu := by
    rw [Measure.map_comp mu _ hdense, Measure.map_comp mu _ hrestrict, hkernel]
  rw [hmeasure, Measure.comp_eq_comp_const_apply]
  let : IsMarkovKernel KJ := by
    dsimp only [KJ]
    let : IsMarkovKernel (SubMarkovKernelSemigroup.finiteSetKernel P
        (MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J)) :=
      hP.isMarkovKernel_finiteSetKernel P _
    exact Kernel.IsMarkovKernel.map _
      (DenseTimePath.measurable_pullbackPhysicalSet J)
  let : IsMarkovKernel (Kernel.comap KJ
      (fun path : DiffusionPath d ↦ path (r path)) heval) := inferInstance
  let : IsFiniteMeasure (Kernel.comap KJ
      (fun path : DiffusionPath d ↦ path (r path)) heval ∘ₘ mu) := inferInstance
  have hfint : Integrable f (Kernel.comap KJ
      (fun path : DiffusionPath d ↦ path (r path)) heval ∘ₘ mu) := f.integrable
  rw [Measure.comp_eq_comp_const_apply] at hfint
  have hi := Kernel.integral_comp hfint
  simpa only [Kernel.const_apply, Kernel.comap_apply, KJ] using! hi

theorem aux_prop_limit_properties_strong_markov_countable_restart
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Q : Kernel (SpatialCoordinates d) (DiffusionPath d))
    (x : SpatialCoordinates d)
    (f : Filtration ℝ≥0
      (@NullMeasurableSpace.instMeasurableSpace
        (DiffusionPath d) ContinuousPath.instMeasurableSpace (Q x)))
    (T : DiffusionPath d → ℝ≥0)
    (hT : IsStoppingTime f (fun path ↦ (T path : WithTop ℝ≥0)))
    (hTRange : (Set.range T).Countable)
    (hTmeas : @Measurable (DiffusionPath d) ℝ≥0
      (ContinuousPath.instMeasurableSpace) NNReal.measurableSpace T)
    (A : Set (DiffusionPath d))
    (hA : MeasurableSet[hT.measurableSpace] A)
    (hRestart : ∀ S ∈ Set.range T, ∀ B : Set (DiffusionPath d),
      MeasurableSet[f S] B →
        ((Q x).restrict B).map (ContinuousPath.shift S) =
          Kernel.comap Q (ContinuousPath.coordinateProcess S)
            (ContinuousPath.measurable_coordinateProcess S) ∘ₘ
            ((Q x).restrict B)) :
    ((Q x).restrict A).map (fun path ↦ ContinuousPath.shift (T path) path) =
          Kernel.comap Q (fun path ↦ path (T path))
        (ContinuousPath.measurable_eval_of_measurable T hTmeas) ∘ₘ
        ((Q x).restrict A) := by
  classical
  let : Countable (Set.range T) := hTRange.to_subtype
  have hcoercedRange :
      (Set.range (fun path ↦ (T path : WithTop ℝ≥0))).Countable := by
    refine (hTRange.image (fun t : ℝ≥0 ↦ (t : WithTop ℝ≥0))).mono ?_
    rintro i ⟨path, rfl⟩
    exact ⟨T path, ⟨path, rfl⟩, rfl⟩
  have hshift : @Measurable (DiffusionPath d) (DiffusionPath d)
      ContinuousPath.instMeasurableSpace ContinuousPath.instMeasurableSpace
      (fun path ↦ ContinuousPath.shift (T path) path) :=
    ContinuousPath.measurable_shift_of_measurable T hTmeas
  let lev : Set.range T → Set (DiffusionPath d) :=
    fun S ↦ A ∩ {path | T path = (S : ℝ≥0)}
  have hlevF : ∀ S : Set.range T, MeasurableSet[f (S : ℝ≥0)] (lev S) := by
    intro S
    have h1 := hA.2 (S : ℝ≥0)
    have h2 : MeasurableSet[f (S : ℝ≥0)]
        {path | (T path : WithTop ℝ≥0) = ((S : ℝ≥0) : WithTop ℝ≥0)} :=
      hT.measurableSet_eq_of_countable_range hcoercedRange (S : ℝ≥0)
    have hset : lev S =
        (A ∩ {path | (T path : WithTop ℝ≥0) ≤ ((S : ℝ≥0) : WithTop ℝ≥0)}) ∩
          {path | (T path : WithTop ℝ≥0) = ((S : ℝ≥0) : WithTop ℝ≥0)} := by
      ext path
      simp only [lev, Set.mem_inter_iff, Set.mem_ofPred_eq,
        WithTop.coe_eq_coe, WithTop.coe_le_coe]
      exact ⟨fun h ↦ ⟨⟨h.1, h.2.le⟩, h.2⟩,
        fun h ↦ ⟨h.1.1, h.2⟩⟩
    rw [hset]
    exact h1.inter h2
  have hlevNull : ∀ S : Set.range T,
      NullMeasurableSet (lev S) (Q x) := by
    intro S
    have hm : @MeasurableSet (DiffusionPath d)
        (@NullMeasurableSpace.instMeasurableSpace
          (DiffusionPath d) ContinuousPath.instMeasurableSpace (Q x)) (lev S) :=
      (f.le' (S : ℝ≥0)) _ (hlevF S)
    exact hm
  have hdisj : Pairwise (Function.onFun Disjoint lev) := by
    intro S S' hSS'
    refine Set.disjoint_left.mpr fun path hpath hpath' ↦ hSS' ?_
    simp only [lev, Set.mem_inter_iff, Set.mem_ofPred_eq] at hpath hpath'
    exact Subtype.ext (by rw [← hpath.2, ← hpath'.2])
  have hunion : ⋃ S : Set.range T, lev S = A := by
    ext path
    simp only [lev, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun ⟨_, h, _⟩ ↦ h, fun h ↦
      ⟨⟨T path, ⟨path, rfl⟩⟩, h, rfl⟩⟩
  ext B hB
  rw [Measure.map_apply hshift hB,
    Measure.bind_apply hB (Kernel.aemeasurable _),
    Measure.restrict_apply (hshift hB)]
  have hLHS :
      (fun path : DiffusionPath d ↦ ContinuousPath.shift (T path) path) ⁻¹' B ∩ A =
        ⋃ S : Set.range T, ((ContinuousPath.shift (S : ℝ≥0)) ⁻¹' B ∩ lev S) := by
    rw [← hunion]
    ext path
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_preimage, lev,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hB', S, hA', hS⟩
      exact ⟨S, by rw [← hS]; exact hB', hA', hS⟩
    · rintro ⟨S, hB', hA', hS⟩
      exact ⟨by rw [hS]; exact hB', S, hA', hS⟩
  rw [hLHS,
    measure_iUnion₀ (μ := Q x) (fun S S' hSS' ↦
      (hdisj hSS').mono Set.inter_subset_right Set.inter_subset_right |>.aedisjoint)
      (fun S ↦ (ContinuousPath.measurable_shift_fixed (S : ℝ≥0) hB).nullMeasurableSet.inter
        (hlevNull S))]
  have hRHS :
      ∫⁻ path, (Kernel.comap Q (fun path ↦ path (T path))
          (ContinuousPath.measurable_eval_of_measurable T hTmeas)) path B
        ∂((Q x).restrict A) =
      ∑' S : Set.range T, ∫⁻ path in lev S,
        Q (path (T path)) B ∂(Q x) := by
    simp only [Kernel.comap_apply]
    show ∫⁻ path in A, Q (path (T path)) B ∂(Q x) = _
    rw [← hunion, lintegral_iUnion₀ hlevNull
      (fun S S' hSS' ↦ (hdisj hSS').aedisjoint)]
  rw [hRHS]
  refine tsum_congr fun S ↦ ?_
  have hres := congrArg (fun rho : Measure (DiffusionPath d) ↦ rho B)
    (hRestart (S : ℝ≥0) S.2 (lev S) (hlevF S))
  simp only [Measure.map_apply (ContinuousPath.measurable_shift_fixed (S : ℝ≥0)) hB,
    Measure.restrict_apply (ContinuousPath.measurable_shift_fixed (S : ℝ≥0) hB),
    Measure.bind_apply hB (Kernel.aemeasurable _), Kernel.comap_apply,
    ContinuousPath.coordinateProcess_apply] at hres
  rw [hres]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_mem₀ (hlevNull S)] with path hpath
  simp only [lev, Set.mem_inter_iff, Set.mem_ofPred_eq] at hpath
  rw [hpath.2]

theorem aux_prop_limit_properties_strong_markov_usual_deterministic_restart
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (R : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hR : IsMarkovKernel R) (omega : BilateralField d)
    (hP : P.IsConservative)
    (hcont : Continuous (fun x : SpatialCoordinates d =>
      jointPathProbabilityMeasure R hR omega x))
    (hfd : ∀ I x, R.map (ContinuousPath.finsetEvaluation I) (omega, x) =
      SubMarkovKernelSemigroup.finiteSetKernel P I x)
    (x : SpatialCoordinates d) (t : ℝ≥0) (A : Set (DiffusionPath d))
    (hA : MeasurableSet[usualNaturalAt
      (R (omega, x)) t] A) :
    ((R (omega, x)).restrict A).map (ContinuousPath.shift t) =
      Kernel.comap R (fun path : DiffusionPath d => (omega, path t))
        (measurable_const.prodMk (ContinuousPath.measurable_coordinateProcess t)) ∘ₘ
        ((R (omega, x)).restrict A) := by
  let Q : Kernel (SpatialCoordinates d) (DiffusionPath d) :=
    R.comap (fun y => (omega, y)) (by measurability)
  let : IsMarkovKernel Q := by
    dsimp [Q]
    infer_instance
  have hQfd : ∀ I y, Q.map (ContinuousPath.finsetEvaluation I) y =
      SubMarkovKernelSemigroup.finiteSetKernel P I y := by
    intro I y
    rw [Kernel.map_apply Q (ContinuousPath.measurable_finsetEvaluation I) y,
      Kernel.comap_apply]
    have hh := hfd I y
    rw [Kernel.map_apply R (ContinuousPath.measurable_finsetEvaluation I)
      (omega, y)] at hh
    exact hh
  let nu : Measure (DiffusionPath d) := Q x
  let mu : Measure (DiffusionPath d) := nu.restrict A
  let : IsProbabilityMeasure nu := by
    dsimp [nu]
    infer_instance
  have hAq (n : ℕ) (q : ℕ → DenseTime)
      (hqAbove : ∀ n, t < DenseTime.castOrderEmbedding (q n)) :
      MeasurableSet[ContinuousPath.canonicalFiltration
        (alpha := SpatialCoordinates d)
          (DenseTime.castOrderEmbedding (q n)) ⊔
        MeasurableSpace.generateFrom {U : Set (DiffusionPath d) | nu U = 0}] A := by
    exact (MeasurableSpace.measurableSet_iInf.mp hA)
      ⟨DenseTime.castOrderEmbedding (q n), hqAbove n⟩
  obtain ⟨q, hqAnti, hqAbove, hq⟩ :=
    exists_denseTime_seq_strictAnti_tendsto t
  have hstep : ∀ n, mu.map (ContinuousPath.shift
      (DenseTime.castOrderEmbedding (q n))) =
      Kernel.comap Q (ContinuousPath.coordinateProcess
        (alpha := SpatialCoordinates d) (DenseTime.castOrderEmbedding (q n)))
        (ContinuousPath.measurable_coordinateProcess _) ∘ₘ mu := by
    intro n
    obtain ⟨B, hB, hBae⟩ :=
      aux_prop_limit_properties_strong_markov_canonical_representative nu
        (DenseTime.castOrderEmbedding (q n)) A (hAq n q hqAbove)
    have hres : nu.restrict B = nu.restrict A :=
      Measure.restrict_congr_set hBae
    have hcan := aux_prop_limit_properties_strong_markov_canonical_restart
      P R hR omega hP hfd x (DenseTime.castOrderEmbedding (q n)) B hB
    have hcanQ : ((Q x).restrict B).map (ContinuousPath.shift
        (DenseTime.castOrderEmbedding (q n))) =
        Kernel.comap Q (ContinuousPath.coordinateProcess
          (alpha := SpatialCoordinates d) (DenseTime.castOrderEmbedding (q n)))
          (ContinuousPath.measurable_coordinateProcess _) ∘ₘ ((Q x).restrict B) := by
      simpa only [Q, Kernel.comap_apply] using! hcan
    rw [hres] at hcanQ
    exact hcanQ
  change mu.map (ContinuousPath.shift t) =
    Kernel.comap Q (ContinuousPath.coordinateProcess
      (alpha := SpatialCoordinates d) t)
      (ContinuousPath.measurable_coordinateProcess t) ∘ₘ mu
  apply MarkovProcess.Measure.map_denseRestriction_injective
  apply MarkovProcess.Measure.eq_of_map_finiteRestriction_eq
  intro J
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let L : Kernel (SpatialCoordinates d) (J → SpatialCoordinates d) :=
    (SubMarkovKernelSemigroup.finiteSetKernel P
      (MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J)).map
      (DenseTimePath.pullbackPhysicalSet J)
  let g : SpatialCoordinates d → ℝ := fun y ↦ ∫ z, f z ∂L y
  have hg_cont : Continuous g := by
    exact aux_prop_limit_properties_strong_markov_future_continuous
      P R hR omega hcont hfd J f
  let C := ‖PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f‖
  have hg_bound : ∀ y, ‖g y‖ ≤ C := by
    intro y
    exact hP.norm_integral_map_finiteSetKernel_pullbackPhysicalSet_le J f y
  have hright := tendsto_integral_continuousPath_eval_of_tendsto
    mu t q hq g hg_cont C hg_bound
  have hleft := tendsto_integral_continuousPath_finiteDenseEvaluation_shift
    mu t q hq J f
  have heq (n : ℕ) :
      (∫ path, f (fun j : J ↦ path
          (DenseTime.castOrderEmbedding (q n) + DenseTime.castOrderEmbedding j)) ∂mu) =
        ∫ path, g (path (DenseTime.castOrderEmbedding (q n))) ∂mu := by
    have hm := congrArg (fun rho : Measure (DiffusionPath d) ↦
      (rho.map ContinuousPath.denseRestriction).map J.restrict) (hstep n)
    have hi := congrArg (fun rho : Measure (J → SpatialCoordinates d) ↦
      ∫ z, f z ∂rho) hm
    rw [aux_prop_limit_properties_strong_markov_map_dense_restrict_integral,
      aux_prop_limit_properties_strong_markov_composed_dense_integral
        P Q hP hQfd mu (DenseTime.castOrderEmbedding (q n)) J f] at hi
    have htest : StronglyMeasurable (fun path : DiffusionPath d ↦
        f (J.restrict (ContinuousPath.denseRestriction path))) :=
      (f.continuous.comp (ContinuousPath.continuous_finiteEvaluation
        (fun j : J ↦ DenseTime.castOrderEmbedding j))).stronglyMeasurable
    rw [integral_map
      (ContinuousPath.measurable_shift_fixed
        (DenseTime.castOrderEmbedding (q n))).aemeasurable
      htest.aestronglyMeasurable] at hi
    simpa only [ContinuousPath.denseRestriction_apply,
      ContinuousPath.shift_apply, L, g] using! hi
  have hlimits :
      (∫ path, f (fun j : J ↦ path
          (t + DenseTime.castOrderEmbedding j)) ∂mu) =
        ∫ path, g (path t) ∂mu :=
    tendsto_nhds_unique hleft (by simpa only [heq] using hright)
  rw [aux_prop_limit_properties_strong_markov_map_dense_restrict_integral,
    aux_prop_limit_properties_strong_markov_composed_dense_integral
      P Q hP hQfd mu t J f]
  have htest : StronglyMeasurable (fun path : DiffusionPath d ↦
      f (J.restrict (ContinuousPath.denseRestriction path))) :=
    (f.continuous.comp (ContinuousPath.continuous_finiteEvaluation
      (fun j : J ↦ DenseTime.castOrderEmbedding j))).stronglyMeasurable
  rw [integral_map (ContinuousPath.measurable_shift_fixed t).aemeasurable
    htest.aestronglyMeasurable]
  simpa only [ContinuousPath.denseRestriction_apply,
    ContinuousPath.shift_apply, L, g] using! hlimits

theorem aux_prop_limit_properties_strong_markov_usual_finite_restart
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (R : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hR : IsMarkovKernel R) (omega : BilateralField d)
    (hP : P.IsConservative)
    (hcont : Continuous (fun x : SpatialCoordinates d =>
      jointPathProbabilityMeasure R hR omega x))
    (hfd : ∀ I x, R.map (ContinuousPath.finsetEvaluation I) (omega, x) =
      SubMarkovKernelSemigroup.finiteSetKernel P I x)
    (x : SpatialCoordinates d)
    (f : Filtration ℝ≥0
      (@NullMeasurableSpace.instMeasurableSpace
        (DiffusionPath d) ContinuousPath.instMeasurableSpace (R (omega, x))))
    (T : DiffusionPath d → ℝ≥0)
    (hT : IsStoppingTime f (fun path ↦ (T path : WithTop ℝ≥0)))
    (hTmeas : Measurable T)
    (A : Set (DiffusionPath d))
    (hA : MeasurableSet[hT.measurableSpace] A)
    (hRestart : ∀ S : ℝ≥0, ∀ B : Set (DiffusionPath d),
      MeasurableSet[f S] B →
        ((R (omega, x)).restrict B).map (ContinuousPath.shift S) =
          Kernel.comap R (fun path : DiffusionPath d => (omega, path S))
            (Measurable.prodMk
              (f := fun _ : DiffusionPath d => omega)
              (g := fun path : DiffusionPath d => path S)
              (measurable_const : Measurable (fun _ : DiffusionPath d => omega))
              (ContinuousPath.measurable_coordinateProcess S)) ∘ₘ
            ((R (omega, x)).restrict B)) :
    ((R (omega, x)).restrict A).map
        (fun path ↦ ContinuousPath.shift (T path) path) =
      Kernel.comap R (fun path ↦ (omega, path (T path)))
        (Measurable.prodMk
          (f := fun _ : DiffusionPath d => omega)
          (g := fun path : DiffusionPath d => path (T path))
          (measurable_const : Measurable (fun _ : DiffusionPath d => omega))
          (ContinuousPath.measurable_eval_of_measurable T hTmeas)) ∘ₘ
        ((R (omega, x)).restrict A) := by
  let Q : Kernel (SpatialCoordinates d) (DiffusionPath d) :=
    R.comap (fun y : SpatialCoordinates d ↦ (omega, y))
      ((measurable_const : Measurable (fun _ : SpatialCoordinates d => omega)).prodMk
        (measurable_id : Measurable (fun y : SpatialCoordinates d => y)))
  let : IsMarkovKernel Q := by
    dsimp [Q]
    infer_instance
  have hQfd : ∀ I y, Q.map (ContinuousPath.finsetEvaluation I) y =
      SubMarkovKernelSemigroup.finiteSetKernel P I y := by
    intro I y
    rw [Kernel.map_apply Q (ContinuousPath.measurable_finsetEvaluation I) y,
      Kernel.comap_apply]
    have hh := hfd I y
    rw [Kernel.map_apply R (ContinuousPath.measurable_finsetEvaluation I)
      (omega, y)] at hh
    exact hh
  have hTnMeas : ∀ n : ℕ, Measurable (fun path ↦
      MarkovProcess.dyadicCeiling n (T path)) := by
    intro n
    have hdyn : Measurable (MarkovProcess.dyadicCeiling n) := by
      refine measurable_of_Iic fun i ↦ ?_
      have heq : (MarkovProcess.dyadicCeiling n ⁻¹' Set.Iic i) =
          Set.Iic (MarkovProcess.dyadicFloor n i) := by
        ext s
        simp only [Set.mem_preimage, Set.mem_Iic]
        exact MarkovProcess.dyadicCeiling_le_iff n s i
      rw [heq]
      exact measurableSet_Iic
    exact hdyn.comp hTmeas
  let Tn : ℕ → DiffusionPath d → ℝ≥0 := fun n path ↦
    MarkovProcess.dyadicCeiling n (T path)
  have hTnStop : ∀ n, IsStoppingTime f
      (fun path ↦ (Tn n path : WithTop ℝ≥0)) := by
    intro n
    exact MarkovProcess.isStoppingTime_dyadicCeiling hT n
  have hATn : ∀ n, MeasurableSet[(hTnStop n).measurableSpace] A := by
    intro n
    exact IsStoppingTime.measurableSpace_mono hT (hTnStop n)
      (fun path ↦ WithTop.coe_le_coe.mpr
        (MarkovProcess.le_dyadicCeiling n (T path))) A hA
  have hstep : ∀ n, ((Q x).restrict A).map
        (fun path ↦ ContinuousPath.shift (Tn n path) path) =
      Kernel.comap Q (fun path ↦ path (Tn n path))
        (ContinuousPath.measurable_eval_of_measurable
          (fun path : DiffusionPath d => Tn n path) (hTnMeas n)) ∘ₘ
        ((Q x).restrict A) := by
    intro n
    apply aux_prop_limit_properties_strong_markov_countable_restart
      Q x f (Tn n) (hTnStop n)
      (MarkovProcess.countable_range_dyadicCeiling_comp n T)
      (hTnMeas n) A (hATn n)
    intro S _ B hB
    have hh := hRestart (S : ℝ≥0) B hB
    simpa only [Q, Kernel.comap_apply] using! hh
  have hcomp :
      Kernel.comap Q (fun path : DiffusionPath d => path (T path))
          (ContinuousPath.measurable_eval_of_measurable T hTmeas) =
        Kernel.comap R (fun path : DiffusionPath d => (omega, path (T path)))
          (Measurable.prodMk
            (f := fun _ : DiffusionPath d => omega)
            (g := fun path : DiffusionPath d => path (T path))
            (measurable_const : Measurable (fun _ : DiffusionPath d => omega))
            (ContinuousPath.measurable_eval_of_measurable T hTmeas)) := by
    ext y S hS
    rfl
  rw [← hcomp]
  change ((Q x).restrict A).map
      (fun path ↦ ContinuousPath.shift (T path) path) =
    Kernel.comap Q (fun path ↦ path (T path))
      (ContinuousPath.measurable_eval_of_measurable T hTmeas) ∘ₘ
      ((Q x).restrict A)
  apply MarkovProcess.Measure.map_denseRestriction_injective
  apply MarkovProcess.Measure.eq_of_map_finiteRestriction_eq
  intro J
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro g
  let L : Kernel (SpatialCoordinates d) (J → SpatialCoordinates d) :=
    (SubMarkovKernelSemigroup.finiteSetKernel P
      (MarkovProcess.SubMarkovKernelSemigroup.denseTimePhysicalSet J)).map
      (DenseTimePath.pullbackPhysicalSet J)
  let k : SpatialCoordinates d → ℝ := fun y ↦ ∫ z, g z ∂L y
  have hk_cont : Continuous k :=
    aux_prop_limit_properties_strong_markov_future_continuous
      P R hR omega hcont hfd J g
  let C := ‖PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap g‖
  have hk_bound : ∀ y, ‖k y‖ ≤ C := by
    intro y
    exact hP.norm_integral_map_finiteSetKernel_pullbackPhysicalSet_le J g y
  have hright := tendsto_integral_continuousPath_eval_randomTime_of_tendsto
    ((Q x).restrict A) Tn T hTnMeas
    (fun path ↦ MarkovProcess.tendsto_dyadicCeiling_comp T path) k hk_cont C hk_bound
  have hleft := tendsto_integral_continuousPath_finiteDenseEvaluation_shift_randomTime_of_tendsto
    ((Q x).restrict A) Tn T hTnMeas
    (fun path ↦ MarkovProcess.tendsto_dyadicCeiling_comp T path) J g
  have heq : ∀ n, (∫ path, g (fun j : J ↦
        path (Tn n path + DenseTime.castOrderEmbedding j)) ∂((Q x).restrict A)) =
      ∫ path, k (path (Tn n path)) ∂((Q x).restrict A) := by
    intro n
    have hm := congrArg (fun rho : Measure (DiffusionPath d) ↦
      (rho.map ContinuousPath.denseRestriction).map J.restrict) (hstep n)
    have hi := congrArg (fun rho : Measure (J → SpatialCoordinates d) ↦
      ∫ z, g z ∂rho) hm
    rw [aux_prop_limit_properties_strong_markov_map_dense_restrict_integral,
      aux_prop_limit_properties_strong_markov_composed_dense_integral_random
        P Q hP hQfd ((Q x).restrict A) (Tn n) (hTnMeas n) J g] at hi
    have htest : StronglyMeasurable (fun path : DiffusionPath d ↦
        g (J.restrict (ContinuousPath.denseRestriction path))) :=
      (g.continuous.comp (ContinuousPath.continuous_finiteEvaluation
        (fun j : J ↦ DenseTime.castOrderEmbedding j))).stronglyMeasurable
    rw [integral_map
      (ContinuousPath.measurable_shift_of_measurable (Tn n) (hTnMeas n)).aemeasurable
      htest.aestronglyMeasurable] at hi
    simpa only [ContinuousPath.denseRestriction_apply,
      ContinuousPath.shift_apply, L, k] using! hi
  have hlimits :
      (∫ path, g (fun j : J ↦
        path (T path + DenseTime.castOrderEmbedding j)) ∂((Q x).restrict A)) =
        ∫ path, k (path (T path)) ∂((Q x).restrict A) :=
    tendsto_nhds_unique hleft (by simpa only [heq] using hright)
  rw [aux_prop_limit_properties_strong_markov_map_dense_restrict_integral,
    aux_prop_limit_properties_strong_markov_composed_dense_integral_random
      P Q hP hQfd ((Q x).restrict A) T hTmeas J g]
  have htest : StronglyMeasurable (fun path : DiffusionPath d ↦
      g (J.restrict (ContinuousPath.denseRestriction path))) :=
    (g.continuous.comp (ContinuousPath.continuous_finiteEvaluation
      (fun j : J ↦ DenseTime.castOrderEmbedding j))).stronglyMeasurable
  rw [integral_map (ContinuousPath.measurable_shift_of_measurable T hTmeas).aemeasurable
    htest.aestronglyMeasurable]
  simpa only [ContinuousPath.denseRestriction_apply,
    ContinuousPath.shift_apply, L, k] using! hlimits



theorem prop_limit_properties_strong_markov
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (_hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (P : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K)
    (hKcont : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      Continuous (fun x : SpatialCoordinates d =>
        jointPathProbabilityMeasure K hK omega x))
    (_hin : in_crossing M H PN KN)
    (hlim : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
        SubMarkovKernelSemigroup.finiteSetKernel (P omega) I x)
    (_hconv : ∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ eps : ℝ, 0 < eps →
      Tendsto (fun N ↦ (chaosSampleLaw M).toMeasure
          {omega : BilateralField d | ∃ x ∈ B, eps ≤
            pathLevyProkhorovDist
              (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
              (jointPathProbabilityMeasure K hK omega x)}) atTop (nhds 0)) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      HasStrongMarkovRestart K omega := by
  classical
  filter_upwards [hKcont, hlim] with omega hcont hfd
  intro x tau htau A hA F hF
  let Q : Kernel (SpatialCoordinates d) (DiffusionPath d) :=
    K.comap (fun y : SpatialCoordinates d => (omega, y))
      (Measurable.prodMk
        (f := fun _ : SpatialCoordinates d => omega)
        (g := fun y : SpatialCoordinates d => y)
        (measurable_const : Measurable (fun _ : SpatialCoordinates d => omega))
        (measurable_id : Measurable (fun y : SpatialCoordinates d => y)))
  let : IsMarkovKernel Q := by
    dsimp [Q]
    infer_instance
  have hQfd : ∀ I y, Q.map (ContinuousPath.finsetEvaluation I) y =
      SubMarkovKernelSemigroup.finiteSetKernel (P omega) I y := by
    intro I y
    rw [Kernel.map_apply Q (ContinuousPath.measurable_finsetEvaluation I) y,
      Kernel.comap_apply]
    have hh := hfd I y
    rw [Kernel.map_apply K (ContinuousPath.measurable_finsetEvaluation I)
      (omega, y)] at hh
    exact hh
  have hP : (P omega).IsConservative :=
    aux_prop_limit_properties_strong_markov_conservative
      (P omega) Q inferInstance hQfd
  let mu : Measure (DiffusionPath d) := K (omega, x)
  let f : Filtration ℝ≥0
      (@NullMeasurableSpace.instMeasurableSpace
        (DiffusionPath d) ContinuousPath.instMeasurableSpace mu) :=
    { seq := fun t => usualNaturalAt mu t
      mono' := fun s t hst =>
        aux_prop_limit_properties_strong_markov_usual_mono mu hst
      le' := fun t => aux_prop_limit_properties_strong_markov_usual_le_null mu t }
  have htauF : IsStoppingTime f tau := by
    intro t
    simpa only [f] using! htau t
  rcases hA with ⟨hAnull, hAsections⟩
  obtain ⟨B, hAB, hBmeas, hBAE⟩ :=
    MeasureTheory.NullMeasurableSet.exists_measurable_superset_ae_eq hAnull
  have hBsection : ∀ t : ℝ≥0,
      MeasurableSet[usualNaturalAt mu t]
        (B ∩ {path : DiffusionPath d | tau path ≤ t}) := by
    intro t
    have hdiff0 : mu (B \ A) = 0 := (ae_eq_set.mp hBAE).1
    have hdiffgen : B \ A ∈ {U : Set (DiffusionPath d) | mu U = 0} := hdiff0
    have hdiffmeas : MeasurableSet[
        MeasurableSpace.generateFrom {U : Set (DiffusionPath d) | mu U = 0}]
        (B \ A) := MeasurableSpace.measurableSet_generateFrom hdiffgen
    have hdiff : MeasurableSet[usualNaturalAt mu t] (B \ A) :=
      (aux_prop_limit_properties_strong_markov_usual_null_le mu t)
        (B \ A) hdiffmeas
    have hEt : MeasurableSet[usualNaturalAt mu t]
        {path : DiffusionPath d | tau path ≤ t} := by
      simpa only [mu] using! htau t
    have hBunion : B = A ∪ (B \ A) := by
      ext path
      constructor
      · intro hpath
        by_cases hpathA : path ∈ A
        · exact Or.inl hpathA
        · exact Or.inr ⟨hpath, hpathA⟩
      · intro hpath
        rcases hpath with hpath | ⟨hpath, _⟩
        · exact hAB hpath
        · exact hpath
    rw [hBunion, Set.union_inter_distrib_right]
    exact (hAsections t).union (hdiff.inter hEt)
  let terminalSigma : Unit → MeasurableSpace (DiffusionPath d) := fun _ => by exact ⨆ t, f t
  have hread : @Measurable (DiffusionPath d) (DenseTime → SpatialCoordinates d)
      (terminalSigma ()) inferInstance ContinuousPath.denseRestriction := by
    let : MeasurableSpace (DiffusionPath d) := terminalSigma ()
    rw [measurable_pi_iff]
    intro q
    have hcoord := ContinuousPath.measurable_coordinateProcess_canonicalFiltration
      (alpha := SpatialCoordinates d) (DenseTime.castOrderEmbedding q)
    have hle : ContinuousPath.canonicalFiltration
        (alpha := SpatialCoordinates d) (DenseTime.castOrderEmbedding q) ≤
        f (DenseTime.castOrderEmbedding q) := by
      change _ ≤ usualNaturalAt mu (DenseTime.castOrderEmbedding q)
      unfold usualNaturalAt
      refine le_iInf fun u => ?_
      exact le_sup_of_le_left
        ((ContinuousPath.canonicalFiltration (alpha := SpatialCoordinates d)).mono u.property.le)
    exact hcoord.mono (hle.trans (le_iSup f _)) le_rfl
  have hbase : ContinuousPath.instMeasurableSpace ≤ terminalSigma () := by
    have he := ContinuousPath.measurableEmbedding_denseRestriction
      (alpha := SpatialCoordinates d)
    exact he.comap_eq.symm.le.trans hread.comap_le
  have hterminalNull : terminalSigma () ≤
      @NullMeasurableSpace.instMeasurableSpace
        (DiffusionPath d) ContinuousPath.instMeasurableSpace mu := by
    refine iSup_le fun t => ?_
    simpa only [f] using! aux_prop_limit_properties_strong_markov_usual_le_null mu t
  have hBstop : MeasurableSet[htauF.measurableSpace] B := by
    refine ⟨?_, ?_⟩
    · exact hbase B hBmeas
    · simpa only [f] using! hBsection
  have hRestart : ∀ S : ℝ≥0, ∀ C : Set (DiffusionPath d),
      MeasurableSet[f S] C →
        ((K (omega, x)).restrict C).map (ContinuousPath.shift S) =
          Kernel.comap K (fun path : DiffusionPath d => (omega, path S))
            (Measurable.prodMk
              (f := fun _ : DiffusionPath d => omega)
              (g := fun path : DiffusionPath d => path S)
              (measurable_const : Measurable (fun _ : DiffusionPath d => omega))
              (ContinuousPath.measurable_coordinateProcess S)) ∘ₘ
            ((K (omega, x)).restrict C) := by
    intro S C hC
    apply aux_prop_limit_properties_strong_markov_usual_deterministic_restart
      (P omega) K hK omega hP hcont hfd x S C
    simpa only [f, mu] using! hC
  let D : ℕ → Set (DiffusionPath d) := fun n =>
    MarkovProcess.StoppingTime.stoppingTimeSlice B tau n
  have hDdisj : Pairwise (Function.onFun Disjoint D) := by
    simpa only [D] using
      (MarkovProcess.StoppingTime.pairwise_disjoint_stoppingTimeSlice B)
  let Tn : ℕ → DiffusionPath d → ℝ≥0 := fun n path =>
    MarkovProcess.StoppingTime.truncTime tau (n : ℝ≥0) path
  have hTnStop : ∀ n, IsStoppingTime f
      (fun path => (Tn n path : WithTop ℝ≥0)) := by
    intro n
    exact MarkovProcess.StoppingTime.isStoppingTime_truncTime htauF (n : ℝ≥0)
  have hTnAE : ∀ n, AEMeasurable (Tn n) (K (omega, x)) := by
    intro n
    have hh := (hTnStop n).measurable'.untopD 0
    have hh' : @Measurable (DiffusionPath d) ℝ≥0
        (@NullMeasurableSpace.instMeasurableSpace
          (DiffusionPath d) ContinuousPath.instMeasurableSpace (K (omega, x)))
        NNReal.measurableSpace (Tn n) := by
      simpa only [Tn, WithTop.untopD_coe] using! hh
    have hhN : NullMeasurable (Tn n) (K (omega, x)) := hh'
    exact hhN.aemeasurable
  let TnM : ℕ → DiffusionPath d → ℝ≥0 := fun n =>
    (hTnAE n).mk (Tn n)
  have hTnMmeas : ∀ n, Measurable (TnM n) := by
    intro n
    exact (hTnAE n).measurable_mk
  have hTnMae : ∀ n, Tn n =ᵐ[K (omega, x)] TnM n := by
    intro n
    exact (hTnAE n).ae_eq_mk
  have hTnMStop : ∀ n, IsStoppingTime f
      (fun path => (TnM n path : WithTop ℝ≥0)) := by
    intro n
    have hEq : (fun path => (Tn n path : WithTop ℝ≥0)) =ᵐ[K (omega, x)]
        (fun path => (TnM n path : WithTop ℝ≥0)) := by
      filter_upwards [hTnMae n] with path hpath
      exact congrArg (fun s : ℝ≥0 => (s : WithTop ℝ≥0)) hpath
    exact (aux_prop_limit_properties_strong_markov_stopping_ae_transfer
      mu f (fun path => (Tn n path : WithTop ℝ≥0))
        (fun path => (TnM n path : WithTop ℝ≥0)) (hTnStop n) hEq
        (fun t => by simpa only [f] using
          (aux_prop_limit_properties_strong_markov_usual_null_le mu t))).1
  have hDstop : ∀ n, MeasurableSet[(hTnStop n).measurableSpace] (D n) := by
    intro n
    change MeasurableSet[
      (MarkovProcess.StoppingTime.isStoppingTime_truncTime htauF
        (n : ℝ≥0)).measurableSpace] (D n)
    rw [MarkovProcess.StoppingTime.measurableSpace_truncTime htauF (n : ℝ≥0)]
    exact MarkovProcess.StoppingTime.measurableSet_stoppingTimeSlice
      htauF hBstop n
  have hDnull : ∀ n, NullMeasurableSet (D n) (K (omega, x)) := by
    intro n
    have hh := ((hTnStop n).measurableSet (D n)).mp (hDstop n) |>.1
    exact hterminalNull (D n) hh
  have hDstopM : ∀ n, MeasurableSet[(hTnMStop n).measurableSpace] (D n) := by
    intro n
    exact (aux_prop_limit_properties_strong_markov_stopping_ae_transfer
      mu f (fun path => (Tn n path : WithTop ℝ≥0))
        (fun path => (TnM n path : WithTop ℝ≥0)) (hTnStop n)
        ((hTnMae n).mono fun path hpath =>
          congrArg (fun s : ℝ≥0 => (s : WithTop ℝ≥0)) hpath)
        (fun t => by simpa only [f] using
          (aux_prop_limit_properties_strong_markov_usual_null_le mu t))).2
      (D n) (hDstop n)
  have hfinite : ∀ n, ((K (omega, x)).restrict (D n)).map
        (fun path => ContinuousPath.shift (TnM n path) path) =
      Kernel.comap K (fun path => (omega, path (TnM n path)))
        (Measurable.prodMk
          (f := fun _ : DiffusionPath d => omega)
          (g := fun path => path (TnM n path))
          (measurable_const : Measurable (fun _ : DiffusionPath d => omega))
          (ContinuousPath.measurable_eval_of_measurable (TnM n) (hTnMmeas n))) ∘ₘ
        ((K (omega, x)).restrict (D n)) := by
    intro n
    exact aux_prop_limit_properties_strong_markov_usual_finite_restart
      (P omega) K hK omega hP hcont hfd x f (TnM n) (hTnMStop n)
      (hTnMmeas n) (D n) (hDstopM n) hRestart
  let Tfin : DiffusionPath d → ℝ≥0 := fun path =>
    (tau path).untopD 0
  have hTfinAE : AEMeasurable Tfin (K (omega, x)) := by
    have hh := htauF.measurable'.untopD 0
    have hh' : @Measurable (DiffusionPath d) ℝ≥0
        (@NullMeasurableSpace.instMeasurableSpace
          (DiffusionPath d) ContinuousPath.instMeasurableSpace (K (omega, x)))
        NNReal.measurableSpace Tfin := by
      simpa only [Tfin] using! hh
    have hhN : NullMeasurable Tfin (K (omega, x)) := hh'
    exact hhN.aemeasurable
  let TfinM : DiffusionPath d → ℝ≥0 := hTfinAE.mk Tfin
  have hTfinMmeas : Measurable TfinM := hTfinAE.measurable_mk
  have hTfinMae : Tfin =ᵐ[K (omega, x)] TfinM := hTfinAE.ae_eq_mk
  have hshift : Measurable (fun path : DiffusionPath d =>
      ContinuousPath.shift (TfinM path) path) :=
    ContinuousPath.measurable_shift_of_measurable TfinM hTfinMmeas
  have hevalfin : Measurable (fun path : DiffusionPath d => path (TfinM path)) :=
    ContinuousPath.measurable_eval_of_measurable TfinM hTfinMmeas
  let hpairfin : Measurable (fun path : DiffusionPath d =>
      (omega, path (TfinM path))) :=
    Measurable.prodMk
      (f := fun _ : DiffusionPath d => omega)
      (g := fun path : DiffusionPath d => path (TfinM path))
      (measurable_const : Measurable (fun _ : DiffusionPath d => omega)) hevalfin
  let κ : Kernel (DiffusionPath d) (DiffusionPath d) :=
    Kernel.comap K (fun path : DiffusionPath d => (omega, path (TfinM path))) hpairfin
  have hmap : ∀ n, ((K (omega, x)).restrict (D n)).map
        (fun path => ContinuousPath.shift (TfinM path) path) =
      ((K (omega, x)).restrict (D n)).map
        (fun path => ContinuousPath.shift (TnM n path) path) := by
    intro n
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem₀ (hDnull n),
      ae_restrict_of_ae hTfinMae, ae_restrict_of_ae (hTnMae n)] with
      path hpath hfin hn
    have hh := MarkovProcess.StoppingTime.truncTime_eq_untopD_of_mem_stoppingTimeSlice
      (A := B) (tau := tau) (K := n) hpath
    have htime : TfinM path = TnM n path := by
      rw [← hfin, ← hn]
      simpa only [Tfin, Tn] using hh.symm
    exact congrArg (fun s : ℝ≥0 => ContinuousPath.shift s path) htime
  have hcomp : ∀ n, Kernel.comap K
        (fun path : DiffusionPath d => (omega, path (TnM n path)))
        (Measurable.prodMk
          (f := fun _ : DiffusionPath d => omega)
          (g := fun path => path (TnM n path))
          (measurable_const : Measurable (fun _ : DiffusionPath d => omega))
          (ContinuousPath.measurable_eval_of_measurable (TnM n) (hTnMmeas n))) ∘ₘ
        ((K (omega, x)).restrict (D n)) =
      κ ∘ₘ ((K (omega, x)).restrict (D n)) := by
    intro n
    apply Measure.comp_congr
    filter_upwards [ae_restrict_mem₀ (hDnull n),
      ae_restrict_of_ae hTfinMae, ae_restrict_of_ae (hTnMae n)] with
      path hpath hfin hn
    have hh := MarkovProcess.StoppingTime.truncTime_eq_untopD_of_mem_stoppingTimeSlice
      (A := B) (tau := tau) (K := n) hpath
    ext S hS
    simp only [Kernel.comap_apply, κ]
    have htime : TfinM path = TnM n path := by
      rw [← hfin, ← hn]
      simpa only [Tfin, Tn] using hh.symm
    rw [htime]
  have hDn : ∀ n, ((K (omega, x)).restrict (D n)).map
        (fun path => ContinuousPath.shift (TfinM path) path) =
      κ ∘ₘ ((K (omega, x)).restrict (D n)) := by
    intro n
    calc
      _ = ((K (omega, x)).restrict (D n)).map
          (fun path => ContinuousPath.shift (TnM n path) path) := hmap n
      _ = _ := hfinite n
      _ = _ := hcomp n
  have hassembled :=
    aux_prop_limit_properties_strong_markov_null_reassembly
      (K (omega, x)) κ
      (fun path => ContinuousPath.shift (TfinM path) path)
      hshift D hDnull hDdisj hDn
  have hUnion : (⋃ n, D n) = B ∩ {path : DiffusionPath d | tau path < ⊤} := by
    simpa only [D] using
      (MarkovProcess.StoppingTime.iUnion_stoppingTimeSlice (tau := tau) B)
  rw [hUnion] at hassembled
  have hInt := congrArg (fun nu : Measure (DiffusionPath d) =>
      ∫⁻ path, F path ∂nu) hassembled
  rw [lintegral_map hF hshift] at hInt
  rw [Measure.comp_eq_comp_const_apply,
    Kernel.lintegral_comp _ _ _ hF] at hInt
  have hBformula :
      ∫⁻ path in B ∩ {path : DiffusionPath d | tau path < ⊤},
          F (ContinuousPath.shift (TfinM path) path) ∂(K (omega, x)) =
        ∫⁻ path in B ∩ {path : DiffusionPath d | tau path < ⊤},
          ∫⁻ future, F future ∂(K (omega, path (TfinM path))) ∂(K (omega, x)) := by
    simpa only [κ, Kernel.comap_apply, TfinM] using! hInt
  have hres : (K (omega, x)).restrict
        (A ∩ {path : DiffusionPath d | tau path < ⊤}) =
      (K (omega, x)).restrict
        (B ∩ {path : DiffusionPath d | tau path < ⊤}) := by
    apply Measure.restrict_congr_set
    exact (ae_eq_set_inter hBAE (ae_eq_refl _)).symm
  rw [hres]
  calc
    _ = ∫⁻ path in B ∩ {path : DiffusionPath d | tau path < ⊤},
        F (ContinuousPath.shift (TfinM path) path) ∂(K (omega, x)) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae hTfinMae] with path hpath
      simpa only [Tfin] using
        congrArg (fun s : ℝ≥0 => F (ContinuousPath.shift s path)) hpath
    _ = _ := hBformula
    _ = ∫⁻ path in B ∩ {path : DiffusionPath d | tau path < ⊤},
        ∫⁻ future, F future ∂(K (omega, path (Tfin path))) ∂(K (omega, x)) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae hTfinMae] with path hpath
      exact congrArg (fun s : ℝ≥0 =>
        ∫⁻ future, F future ∂(K (omega, path s))) hpath.symm


end SubdiffusiveProcess.Paper

