module

public import SubdiffusiveProcess.Probability.Diffusion.AnalyticInput
public import MarkovProcess.Lifetime.Law
public import MarkovProcess.Lifetime.CountablySeparated
public import MarkovProcess.Lifetime.NonexplosiveTransport
public import MarkovProcess.Trajectory.StoppingLtTop

@[expose] public section

/-! Transport of continuous-path restart to infinite-lifetime paths. -/
open MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.Probability.Diffusion.Input
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.FellerRealization

/-- The measurable sum used for the cemetery extension is its Borel sigma-algebra. -/
theorem cemetery_borelSpace (d : ℕ) : BorelSpace (Cemetery (State d)) := by
  constructor
  apply le_antisymm
  · intro s hs
    have hl : MeasurableSet (Sum.inl ⁻¹' s : Set (State d)) := hs.1
    have hr : MeasurableSet (Sum.inr ⁻¹' s : Set Unit) := hs.2
    letI : MeasurableSpace (Cemetery (State d)) := borel (Cemetery (State d))
    letI : BorelSpace (Cemetery (State d)) := ⟨rfl⟩
    have hemL : MeasurableEmbedding (Sum.inl : State d → Cemetery (State d)) :=
      Topology.IsOpenEmbedding.measurableEmbedding Topology.IsOpenEmbedding.inl
    have hemR : MeasurableEmbedding (Sum.inr : Unit → Cemetery (State d)) :=
      Topology.IsOpenEmbedding.measurableEmbedding Topology.IsOpenEmbedding.inr
    have hsplit : (Sum.inl '' (Sum.inl ⁻¹' s)) ∪ (Sum.inr '' (Sum.inr ⁻¹' s)) = s := by
      apply Set.Subset.antisymm
      · rintro w (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) <;> exact hx
      · intro w hw
        cases w with
        | inl x => exact Or.inl ⟨x, hw, rfl⟩
        | inr x => exact Or.inr ⟨x, hw, rfl⟩
    rw [← hsplit]
    exact (hemL.measurableSet_image.mpr hl).union (hemR.measurableSet_image.mpr hr)
  · apply MeasurableSpace.generateFrom_le
    intro s hs
    exact ⟨(hs.preimage continuous_inl).measurableSet,
      (hs.preimage continuous_inr).measurableSet⟩

/-- The continuous-to-lifetime embedding preserves information available by a given time. -/
theorem measurable_ofContinuousPath_filtration (d : ℕ) (t : NNReal) :
    Measurable[ContinuousPath.canonicalFiltration (alpha := State d) t,
      LifetimePath.canonicalFiltration (alpha := State d) t]
      (LifetimePath.ofContinuousPath : ContinuousPath (State d) → LifetimePath (State d)) := by
  apply Measurable.of_comap_le
  change MeasurableSpace.comap LifetimePath.ofContinuousPath
    (⨆ s : Iic t, MeasurableSpace.comap (LifetimePath.coordinate (α := State d) s)
      inferInstance) ≤ ContinuousPath.canonicalFiltration (alpha := State d) t
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun s ↦ ?_
  rw [MeasurableSpace.comap_comp]
  have hfun : LifetimePath.coordinate (α := State d) s ∘ LifetimePath.ofContinuousPath =
      Cemetery.alive ∘ ContinuousPath.coordinateProcess (alpha := State d) s := by
    funext w
    exact LifetimePath.coordinate_ofContinuousPath w s
  rw [hfun]
  have halive : Measurable (Cemetery.alive : State d → Cemetery (State d)) := measurable_inl
  have hcoord : Measurable[ContinuousPath.canonicalFiltration (alpha := State d) t]
      (ContinuousPath.coordinateProcess (alpha := State d) s) :=
    (ContinuousPath.measurable_coordinateProcess_canonicalFiltration s).mono
      ((ContinuousPath.canonicalFiltration (alpha := State d)).mono s.property) le_rfl
  exact (halive.comp hcoord).comap_le

/-- The infinite-lifetime embedding commutes with every finite shift. -/
theorem ofContinuousPath_shift (d : ℕ) (S : NNReal) (w : ContinuousPath (State d)) :
    LifetimePath.ofContinuousPath (ContinuousPath.shift S w) =
      LifetimePath.shift S (LifetimePath.ofContinuousPath w) := by
  apply LifetimePath.ext_coordinate
  · simp only [LifetimePath.lifetime_ofContinuousPath, LifetimePath.lifetime_shift,
      ENNReal.top_sub_coe]
  · intro t
    rw [LifetimePath.coordinate_ofContinuousPath, LifetimePath.coordinate_shift,
      LifetimePath.coordinate_ofContinuousPath]
    rfl

/-- Event-restricted continuous restart gives the lifetime restart law. -/
theorem restart_map_ofContinuousPath (d : ℕ)
    (K : Kernel (State d) (ContinuousPath (State d))) [IsMarkovKernel K]
    (hzero : ∀ x, ∀ᵐ w ∂K x, w (0 : NNReal) = x)
    (hRestart : ∀ x, ∀ T : ContinuousPath (State d) → WithTop NNReal,
      ∀ hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := State d)) T,
        ∀ B, MeasurableSet[hT.measurableSpace] B →
          ((K x).restrict (B ∩ {w | T w < ⊤})).map
            (fun w ↦ ContinuousPath.shift ((T w).untopD 0) w) =
          Kernel.comap K (fun w ↦ w ((T w).untopD 0))
            (ContinuousPath.measurable_eval_untopD_stoppingTime T hT) ∘ₘ
              ((K x).restrict (B ∩ {w | T w < ⊤}))) :
    Restart (K.map LifetimePath.ofContinuousPath) := by
  classical
  letI : BorelSpace (Cemetery (State d)) := cemetery_borelSpace d
  letI : StandardBorelSpace (Cemetery (State d)) :=
    inferInstance
  letI : MeasurableSpace.CountablySeparated (LifetimePath (State d)) :=
    LifetimePath.instCountablySeparated (alpha := State d)
  let emb : ContinuousPath (State d) → LifetimePath (State d) := LifetimePath.ofContinuousPath
  have hemb : MeasurableEmbedding emb := LifetimePath.measurableEmbedding_ofContinuousPath
  let law := K.map emb
  have hlaw : IsMarkovKernel law := Kernel.IsMarkovKernel.map K hemb.measurable
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact (hlaw.isProbabilityMeasure x).measure_univ
  · intro x
    change ∀ᵐ w ∂law x, LifetimePath.coordinate 0 w = Cemetery.alive x
    rw [show law x = (K x).map emb from Kernel.map_apply K hemb.measurable x]
    apply hemb.ae_map_iff.mpr
    filter_upwards [hzero x] with w hw
    change LifetimePath.coordinate 0 (LifetimePath.ofContinuousPath w) = Cemetery.alive x
    rw [LifetimePath.coordinate_ofContinuousPath, hw]
  · intro x T hT B hB
    let tau : ContinuousPath (State d) → WithTop NNReal := fun w ↦ T (emb w)
    have htau : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := State d)) tau := by
      intro t
      exact measurable_ofContinuousPath_filtration d t (hT t)
    let A : Set (ContinuousPath (State d)) := emb ⁻¹' B
    have hA : MeasurableSet[htau.measurableSpace] A := by
      have hembSup : Measurable[
          (⨆ t, ContinuousPath.canonicalFiltration (alpha := State d) t),
          (⨆ t, LifetimePath.canonicalFiltration (alpha := State d) t)] emb := by
        apply Measurable.of_comap_le
        rw [MeasurableSpace.comap_iSup]
        refine iSup_le fun t ↦ ?_
        exact (measurable_ofContinuousPath_filtration d t).comap_le.trans (le_iSup _ t)
      refine ⟨hembSup hB.1, fun t ↦ ?_⟩
      exact measurable_ofContinuousPath_filtration d t (hB.2 t)
    let C := A ∩ {w | tau w < ⊤}
    let nu := (K x).restrict C
    let shiftC : ContinuousPath (State d) → ContinuousPath (State d) :=
      fun w ↦ ContinuousPath.shift ((tau w).untopD 0) w
    let evalC : ContinuousPath (State d) → State d := fun w ↦ w ((tau w).untopD 0)
    let shiftL : LifetimePath (State d) → LifetimePath (State d) :=
      fun w ↦ LifetimePath.shift (T w).toNNReal w
    let nextL : LifetimePath (State d) → Measure (LifetimePath (State d)) :=
      fun w ↦ law (stateAt (T w).toNNReal w)
    have hshiftC : Measurable shiftC :=
      ContinuousPath.measurable_shift_untopD_stoppingTime tau htau
    have hevalC : Measurable evalC :=
      ContinuousPath.measurable_eval_untopD_stoppingTime tau htau
    have hshift : shiftL ∘ emb = emb ∘ shiftC := by
      funext w
      exact (ofContinuousPath_shift d (T (emb w)).toNNReal w).symm
    have hstate : ∀ w : ContinuousPath (State d),
        stateAt (T (emb w)).toNNReal (emb w) = evalC w := by
      intro w
      change (LifetimePath.coordinate (T (emb w)).toNNReal
        (LifetimePath.ofContinuousPath w)).elim id (fun _ ↦ 0) = _
      rw [LifetimePath.coordinate_ofContinuousPath]
      rfl
    have hnext : nextL ∘ emb = fun w ↦ law (evalC w) := by
      funext w
      exact congrArg law (hstate w)
    have hshiftL : AEMeasurable shiftL (nu.map emb) := by
      apply hemb.aemeasurable_map_iff.mpr
      rw [hshift]
      exact (hemb.measurable.comp hshiftC).aemeasurable
    have hnextL : AEMeasurable nextL (nu.map emb) := by
      apply hemb.aemeasurable_map_iff.mpr
      rw [hnext]
      exact (law.measurable.comp hevalC).aemeasurable
    have hrestrict : (law x).restrict (B ∩ {w | T w < w.lifetime}) = nu.map emb := by
      rw [show law x = (K x).map emb from Kernel.map_apply K hemb.measurable x,
        hemb.restrict_map]
      congr 2
    change ((law x).restrict (B ∩ {w | T w < w.lifetime})).map shiftL =
      ((law x).restrict (B ∩ {w | T w < w.lifetime})).bind nextL
    rw [hrestrict, AEMeasurable.map_map_of_aemeasurable hshiftL hemb.measurable.aemeasurable,
      hshift, ← Measure.map_map hemb.measurable hshiftC]
    have hc := hRestart x tau htau A hA
    change nu.map shiftC = Kernel.comap K evalC hevalC ∘ₘ nu at hc
    rw [hc, Measure.map_comp nu _ hemb.measurable]
    ext S hS
    rw [Measure.bind_apply hS (Kernel.aemeasurable _), Measure.bind_apply hS hnextL,
      hemb.lintegral_map (fun w ↦ nextL w S)]
    apply lintegral_congr
    intro w
    rw [Kernel.map_apply _ hemb.measurable, Kernel.comap_apply]
    change (K (evalC w)).map emb S = law (stateAt (T (emb w)).toNNReal (emb w)) S
    rw [hstate, Kernel.map_apply K hemb.measurable]
end SubdiffusiveProcess.FellerRealization
