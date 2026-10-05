module

public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Paper.aux_lem_tightness_deterministic_restart_mixedFiniteCut
public import SubdiffusiveProcess.Paper.aux_lem_tightness_deterministic_restart_jointLaw
public import SubdiffusiveProcess.Paper.aux_lem_tightness_deterministic_restart_restrictedMap
public import SubdiffusiveProcess.Paper.aux_lem_tightness_deterministic_restart_lintegral_identity
public import SubdiffusiveProcess.Main.DiffusionPath
public import SubdiffusiveProcess.MultiplicativeChaos.TimeMarginal

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper



theorem lem_tightness_deterministic_restart
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (_hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (PN : ℕ → BilateralField d →
      SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d)
      (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hin : in_crossing M H PN KN) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      ∀ x : SpatialCoordinates d, ∀ t : ℝ≥0,
        ∀ A : Set (DiffusionPath d),
          MeasurableSet[
            ContinuousPath.canonicalFiltration
              (alpha := SpatialCoordinates d) t] A →
            ∀ F : DiffusionPath d → ℝ≥0∞, Measurable F →
              (∫⁻ path in A, F (ContinuousPath.shift t path)
                  ∂(KN N (omega, x))) =
                (∫⁻ path in A,
                  ∫⁻ future, F future ∂(KN N (omega, path t))
                    ∂(KN N (omega, x))) := by
  unfold in_crossing at hin
  rcases hin with ⟨hResolvent, hConservative, hFiniteDimensional⟩
  filter_upwards [hFiniteDimensional] with omega hfdOmega
  intro N x t A hA F hF
  have hP : (PN N omega).IsConservative := hConservative N omega
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
  let Q : Kernel (SpatialCoordinates d) (DiffusionPath d) :=
    (KN N).comap (fun y => (omega, y)) (by measurability)
  have : IsMarkovKernel Q := by
    dsimp [Q]
    infer_instance
  have : IsProbabilityMeasure (KN N (omega, x)) := (hKN N).isProbabilityMeasure _
  have hfdQ : ∀ U : Finset ℝ≥0,
      Q.map (ContinuousPath.finsetEvaluation U) =
        SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) U := by
    intro U
    have hEval : Measurable
        (ContinuousPath.finsetEvaluation U : DiffusionPath d → U → SpatialCoordinates d) := by
      exact ContinuousPath.measurable_finsetEvaluation U
    ext y S hS
    rw [Kernel.map_apply Q hEval y, Kernel.comap_apply]
    have hh := congrArg (fun mu : Measure (U → SpatialCoordinates d) => mu S)
      (hfdOmega N U y)
    rw [Kernel.map_apply (KN N) hEval (omega, y)] at hh
    exact hh
  have hJoint :
      (KN N (omega, x)).map (fun path => (past path, ContinuousPath.shift t path)) =
        ((KN N (omega, x)).map past) ⊗ₘ (Q.comap terminal hterminal) := by
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
          (PN N omega) hP Q hfdQ t I
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
              (Q z).map (ContinuousPath.finsetEvaluation ({(0 : ℝ≥0)} : Finset ℝ≥0)) =
                SubMarkovKernelSemigroup.finiteSetKernel (PN N omega)
                  ({(0 : ℝ≥0)} : Finset ℝ≥0) z := by
            have h := congrArg (fun K => K z)
              (hfdQ ({(0 : ℝ≥0)} : Finset ℝ≥0))
            simpa only [Kernel.map_apply Q
              (ContinuousPath.measurable_finsetEvaluation ({(0 : ℝ≥0)} : Finset ℝ≥0)) z]
              using h
          have hzeroMap' :
              (Q z).map (fun path : DiffusionPath d => path (0 : ℝ≥0)) =
                (PN N omega).kernel 0 z :=
            SubdiffusiveProcess.map_eval_eq_of_finsetEvaluation
              (PN N omega) (Q z) z (0 : ℝ≥0) hsingleton
          calc
            (Q z).map (fun path : DiffusionPath d => path (0 : ℝ≥0)) =
                (PN N omega).kernel 0 z := hzeroMap'
            _ = Measure.dirac z := by
              rw [(PN N omega).zero, Kernel.id_apply]
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
              Sum.inl ⟨r.1, hPast r hi⟩ := by
            simpa using hc
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
              terminal', pproj, ContinuousPath.denseRestriction_apply] using hfuture
          · have hc := hcutIndex ⟨Sum.inr q, hi⟩
            have hc' : cutIndex ⟨Sum.inr q, hi⟩ =
                Sum.inr ⟨DenseTime.castOrderEmbedding q, hFuture q hi
                  (bot_lt_iff_ne_bot.mpr hq)⟩ := by
              simpa [hq] using hc
            rw [hG, hc']
            simp [Fcut, Hproj, pproj, fproj, Kernel.finitePastDenseFuture,
              ContinuousPath.denseRestriction_apply]
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
            SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) Jpast := by
        have heval : pproj ∘ past = ContinuousPath.finsetEvaluation Jpast := by
          funext path u
          rfl
        calc
          (Q.map past).map pproj = Q.map (pproj ∘ past) :=
            (Kernel.map_comp_right Q hpast hpproj).symm
          _ = Q.map (ContinuousPath.finsetEvaluation Jpast) := by rw [heval]
          _ = SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) Jpast :=
            hfdQ Jpast
      have hQfuture' :
          (Q.map fproj).comap terminal' hterminal' =
            (SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) Jfuture).comap
              terminal' hterminal' := by
        have hprojEval : fproj = ContinuousPath.finsetEvaluation Jfuture := by
          funext path u
          rfl
        rw [hprojEval, hfdQ Jfuture]
      have hright :
          (((Q.map past).compProd
            ((Q.comap terminal hterminal).comap Prod.snd measurable_snd)) y).map Fcut =
          ((SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) Jpast) ⊗ₖ
            Kernel.prodMkLeft (SpatialCoordinates d)
          ((SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) Jfuture).comap
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
          _ = ((SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) Jpast ⊗ₖ
              Kernel.prodMkLeft (SpatialCoordinates d)
                ((SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) Jfuture).comap
                  terminal' hterminal')).map G) y := by
                rw [hQpast, hQfuture']
      have hleft :
          (Q.map (fun path => (past path, ContinuousPath.shift t path))).map Fcut y =
          ((SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) Jpast) ⊗ₖ
            Kernel.prodMkLeft (SpatialCoordinates d)
              ((SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) Jfuture).comap
                terminal' hterminal')).map G y := by
        rw [← Kernel.map_comp_right Q hpair hFcut]
        simpa [Fcut] using congrArg (fun K => K y) hfin
      have hmapR := Kernel.map_apply
        ((Q.map past).compProd
          ((Q.comap terminal hterminal).comap Prod.snd measurable_snd)) hFcut y
      simpa [Fcut] using
        (hleft.trans hright.symm).trans hmapR.symm
    let default : DiffusionPath d := ContinuousMap.const ℝ≥0 (0 : SpatialCoordinates d)
    have hkernel := aux_lem_tightness_deterministic_restart_jointLaw
      (alpha := SpatialCoordinates d) t default
      (Q.map (fun path => (past path, ContinuousPath.shift t path)))
      ((Q.map past).compProd ((Q.comap terminal hterminal).comap Prod.snd measurable_snd)) hcut
    have hx := congrArg (fun K => K x) hkernel
    calc
      (KN N (omega, x)).map (fun path => (past path, ContinuousPath.shift t path)) =
          (Q.map (fun path => (past path, ContinuousPath.shift t path))) x := by
            rw [Kernel.map_apply Q
              (hpast.prodMk (ContinuousPath.measurable_shift_fixed t)) x]
            rfl
      _ = ((Q.map past).compProd
          ((Q.comap terminal hterminal).comap Prod.snd measurable_snd)) x := hx
      _ = (KN N (omega, x)).map past ⊗ₘ (Q.comap terminal hterminal) := by
            ext S hS
            rw [Kernel.compProd_apply hS, Measure.compProd_apply hS]
            rw [Kernel.map_apply Q hpast x]
            rfl
  have hRestricted :=
    aux_lem_tightness_deterministic_restart_restrictedMap
      (alpha := SpatialCoordinates d) t (KN N (omega, x))
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
  exact aux_lem_tightness_deterministic_restart_lintegral_identity
    (alpha := SpatialCoordinates d) t (KN N (omega, x))
    past hpast Q terminal hterminal hTerminalPath hRestricted A hA' F hF

end SubdiffusiveProcess.Paper
