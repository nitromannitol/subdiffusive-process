module

public import SubdiffusiveProcess.Section10.LegacyPhysicalTransport
public import SubdiffusiveProcess.Section10.PhysicalLocalTransportInfrared
public import SubdiffusiveProcess.Section10.PhysicalLocalTransportUniqueness
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.Section10.PhysicalLocalTransport SubdiffusiveProcess.Section10.PhysicalAttachment
open SubdiffusiveProcess.Section10.LegacyPhysicalTransport
open scoped ENNReal NNReal ProbabilityTheory
noncomputable section
namespace SubdiffusiveProcess.Section10.LegacyPhysicalAttachment

def IsPhysicalFamily {d : ℕ} (M : GMCModel d)
    (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)) :
    Prop :=
  ∀ᵐ omega ∂(physicalLaw M).toMeasure, ∀ L : WithTop ℕ,
    ∃ D : C0ResolventDatum (SpatialCoordinates d),
    ∃ hdense : ∀ mu, DenseRange (D.operator mu),
      IsWeakEllipticResolvent (coefficientAt M L omega) (coefficientAt M L omega) D ∧
      (D.fellerKernelSemigroup hdense).IsConservative ∧
      ∀ (I : Finset ℝ≥0) (x : SpatialCoordinates d),
        ((X L).map (ContinuousPath.finsetEvaluation I)) (omega, x) =
          SubMarkovKernelSemigroup.finiteSetKernel (D.fellerKernelSemigroup hdense) I x

def rescale {d : ℕ} (M : GMCModel d) (n : ℕ) (w : DiffusionPath d) :
    DiffusionPath d :=
  ⟨fun t => (3 : ℝ) ^ (-(n : ℤ)) •
    w (Real.toNNReal ((3 : ℝ) ^ (2 * n) / ahom M n) * t), by fun_prop⟩

def CutoffAttachment {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d)) :
    Prop :=
  (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
    ∀ N, ∃ D : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum
        (SpatialCoordinates d),
      (∀ mu, DenseRange (D.operator mu)) ∧
      SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent
        (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) D ∧
      ∀ (mu : Semigroup.PositiveShift)
        (f : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ)
        (x : SpatialCoordinates d),
        D.solution mu f x =
          ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
            kernelIntegral (PN N omega (Real.toNNReal t)) f x) ∧
  (∀ N omega, (PN N omega).IsConservative) ∧
  (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
    ∀ N I x, (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
      SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x)

theorem rescale_eq {d : ℕ} (M : GMCModel d) (N : ℕ) :
    rescale M N =
      ContinuousPath.rescale (physicalCoordinates N (0 : SpatialCoordinates d)).symm
        (rawClock M N N) := by
  have hclock : Real.toNNReal ((3 : ℝ)^(2*N) / ahom M N) = rawClock M N N := by
    apply NNReal.eq
    simp only [rawClock, activeScale_coe, min_self]
    exact max_eq_left (div_pos (pow_pos (by norm_num) _) (ahom_pos M N)).le
  funext w
  apply ContinuousMap.ext
  intro t
  simp only [rescale, ContinuousMap.coe_mk,
    ContinuousPath.rescale_apply, physicalCoordinates_symm_apply,
    sub_zero, zpow_neg, zpow_natCast, hclock]

def annealedSequence {d : ℕ}
    (M : GMCModel d)
    (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d))
    (hX : ∀ L, IsMarkovKernel (X L)) (untruncated : Bool) (phi : ℕ → ℕ)
    (xs : ℕ → SpatialCoordinates d) (n : ℕ) : ProbabilityMeasure (DiffusionPath d) := by
  letI := hX ((if untruncated then ⊤ else ((phi n) : WithTop ℕ)))
  let row := ((X ((if untruncated then ⊤ else ((phi n) : WithTop ℕ)))).comap
    (fun omega => (omega,(3 : ℝ)^(phi n) • xs n))
    (measurable_id.prodMk measurable_const)).map
      (rescale M (phi n))
  have hm : Measurable (rescale M (phi n)) := by
    rw [rescale_eq]
    exact ContinuousPath.measurable_rescale _ _
  letI : IsMarkovKernel row := Kernel.IsMarkovKernel.map _ hm
  exact ⟨row ∘ₘ (physicalLaw M).toMeasure, inferInstance⟩

theorem annealedSequence_integral {d : ℕ}
    (M : GMCModel d)
    (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d))
    (hX : ∀ L, IsMarkovKernel (X L)) (untruncated : Bool) (phi : ℕ → ℕ)
    (xs : ℕ → SpatialCoordinates d) (n : ℕ)
    (G : BoundedContinuousFunction (DiffusionPath d) ℝ) :
    (∫ w, G w ∂(annealedSequence M X hX untruncated phi xs n :
      Measure (DiffusionPath d))) =
      ∫ omega, ∫ w, G (rescale M (phi n) w)
        ∂X ((if untruncated then ⊤ else ((phi n) : WithTop ℕ)))
          (omega,(3 : ℝ)^(phi n) • xs n)
        ∂(physicalLaw M).toMeasure := by
  let L := (if untruncated then ⊤ else ((phi n) : WithTop ℕ))
  let := hX L
  have hm : Measurable (rescale M (phi n)) := by
    rw [rescale_eq]
    exact ContinuousPath.measurable_rescale _ _
  change (∫ w, G w ∂(_ ∘ₘ (physicalLaw M).toMeasure)) = _
  rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp (G.integrable _),
    Kernel.const_apply]
  apply integral_congr_ae
  apply ae_of_all
  intro omega
  dsimp only
  rw [Kernel.map_apply _ hm, Kernel.comap_apply,
    integral_map hm.aemeasurable G.continuous.measurable.aestronglyMeasurable]

def annealedRow {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d)
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K) (x : SpatialCoordinates d) :
    ProbabilityMeasure (DiffusionPath d) := by
  letI := hK
  exact ⟨K.comap (fun omega => (omega,x)) (measurable_id.prodMk measurable_const) ∘ₘ
    (chaosSampleLaw M).toMeasure, inferInstance⟩

theorem annealedRow_integral {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d)
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K) (x : SpatialCoordinates d)
    (G : BoundedContinuousFunction (DiffusionPath d) ℝ) :
    (∫ w, G w ∂(annealedRow M K hK x : Measure (DiffusionPath d))) =
      ∫ omega, ∫ w, G w ∂K (omega,x) ∂(chaosSampleLaw M).toMeasure := by
  let := hK
  change (∫ w, G w ∂(_ ∘ₘ (chaosSampleLaw M).toMeasure)) = _
  rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp (G.integrable _),
    Kernel.const_apply]
  rfl

theorem infrared_unique {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, H omega = infraredField M omega := by
  filter_upwards [hH.2, (infraredField_spec M).2] with omega h h'
  exact tendsto_nhds_unique h h'

theorem top_path_attachment {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hscale : MassiveUnscale d) (M : GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N)) (hin : CutoffAttachment M H PN KN)
    (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d))
    (hX : ∀ L, IsMarkovKernel (X L))
    (hphysical : IsPhysicalFamily M X) (N : ℕ) :
    ∀ᵐ eta ∂nativeLaw M, ∀ x : SpatialCoordinates d,
      (X ⊤ (physicalEnvironment M N 0 eta, (3 : ℝ)^N • x)).map
        (rescale M N) = KN N (bilateralEnvironment eta,x) := by
  let := hX ⊤
  let := hKN N
  have hp := (physicalEnvironment_preserving M N 0).quasiMeasurePreserving.ae hphysical
  have hb1 := (bilateralEnvironment_preserving M).quasiMeasurePreserving.ae hin.1
  have hb3 := (bilateralEnvironment_preserving M).quasiMeasurePreserving.ae hin.2.2
  have hH' := (bilateralEnvironment_preserving M).quasiMeasurePreserving.ae
    (infrared_unique M H hH)
  filter_upwards [hp, hb1, hb3, hH', top_local_identification M N 0]
    with eta hphysical' hres hFDD hHeta hid
  let omega := physicalEnvironment M N 0 eta
  let xi := bilateralEnvironment eta
  obtain ⟨D, hdense, hweak, hcons, hfdd⟩ := hphysical' ⊤
  obtain ⟨E, hedense, hEweak, hElaplace⟩ := hres N
  let c := rawClock M ⊤ N
  let e := physicalCoordinates (d := d) N 0
  let D' := transportedDatum D e c (rawClock_pos M ⊤ N)
  let hdense' := transportedDatum_dense D hdense e c (rawClock_pos M ⊤ N)
  let Q := (KN N).comap (Prod.mk xi) measurable_prodMk_left
  let Y := ((X ⊤).comap (fun x => (omega,e x)) (measurable_const.prodMk e.measurable)).map
    (ContinuousPath.rescale e.symm c)
  let : IsMarkovKernel Q := by dsimp [Q]; infer_instance
  let : IsMarkovKernel Y := Kernel.IsMarkovKernel.map _ (ContinuousPath.measurable_rescale _ _)
  have hQF : ∀ I x, Q.map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel (PN N xi) I x := by
    intro I x
    rw [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I), Kernel.comap_apply]
    have h := hFDD N I x
    rw [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)] at h
    exact h
  have hPN := (SubdiffusiveProcess.E7.isFeller_of_realization_and_datum
    (PN N xi) E hedense hElaplace Q hQF).1
  have hDweak : IsWeakEllipticResolvent (localCoefficient M ⊤ N 0 omega)
      (localSpeed M ⊤ N 0 omega) D' :=
    datum_weak hscale M ⊤ N 0 omega D hweak
  have hc : localCoefficient M ⊤ N 0 omega = cutoffCoefficient M H xi N := by
    funext x
    have hh : cutoffCoefficient M H xi N x =
        cutoffCoefficient M (infraredField M) xi N x := by
      unfold cutoffCoefficient cutoffPotential
      rw [show H xi = infraredField M xi from hHeta]
    exact (hid x).2.trans hh.symm
  have hb : localSpeed M ⊤ N 0 omega = cutoffSpeedDensity M H xi N := by
    funext x
    have hh : cutoffSpeedDensity M H xi N x =
        cutoffSpeedDensity M (infraredField M) xi N x := by
      unfold cutoffSpeedDensity cutoffPotential
      rw [show H xi = infraredField M xi from hHeta]
    exact (hid x).1.trans hh.symm
  rw [← hc, ← hb] at hEweak
  have hconj := datum_conjugacy D hdense e c (rawClock_pos M ⊤ N)
  have hYF : ∀ I x, Y.map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel (D'.fellerKernelSemigroup hdense') I x := by
    intro I x
    rw [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)]
    dsimp only [Y]
    rw [Kernel.map_apply _ (ContinuousPath.measurable_rescale _ _), Kernel.comap_apply]
    change ((X ⊤ (omega,e x)).map (ContinuousPath.rescale e.symm c)).map _ = _
    apply rescaled_fdd _ _ hcons
      ((X ⊤).comap (Prod.mk omega) measurable_prodMk_left) inferInstance
      (fun J y => ?_) e.symm c (rawClock_pos M ⊤ N) hconj I x
    have h := hfdd J y
    rw [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation J)] at h
    exact h
  have hEQ : Y = Q := local_law_unique M ⊤ N 0 omega D' E hDweak hEweak
    hdense' hedense Y Q inferInstance hYF (by intro I x; simpa only [hPN] using hQF I x)
  intro x
  have hrow := congrArg (fun Z : Kernel (SpatialCoordinates d) (DiffusionPath d) => Z x) hEQ
  dsimp only [Y, Q] at hrow
  rw [Kernel.map_apply _ (ContinuousPath.measurable_rescale _ _), Kernel.comap_apply,
    Kernel.comap_apply] at hrow
  change (X ⊤ (omega,e x)).map (ContinuousPath.rescale e.symm c) = KN N (xi,x) at hrow
  have hclock : c = rawClock M N N := by
    apply NNReal.eq
    change (3 : ℝ)^(2*N) / ahom M (activeScale ⊤ N) =
      (3 : ℝ)^(2*N) / ahom M (activeScale (N : WithTop ℕ) N)
    have htop : activeScale (⊤ : WithTop ℕ) N = N := by
      simp only [activeScale, WithTop.untopD_top, min_self]
    have hfinite : activeScale (N : WithTop ℕ) N = N :=
      (activeScale_coe N N).trans (min_self N)
    rw [htop, hfinite]
  simpa only [rescale_eq, e, physicalCoordinates_apply,
    zero_add, hclock] using hrow

theorem top_annealed_attachment {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hscale : MassiveUnscale d) (M : GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N)) (hin : CutoffAttachment M H PN KN)
    (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d))
    (hX : ∀ L, IsMarkovKernel (X L))
    (hphysical : IsPhysicalFamily M X) (N : ℕ)
    (x : SpatialCoordinates d) :
    annealedSequence M X hX true id (fun _ => x) N =
      annealedRow M (KN N) (hKN N) x := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext
  intro B hB
  have hm : Measurable (rescale M N) := by
    rw [rescale_eq]
    exact ContinuousPath.measurable_rescale _ _
  let left := ((X ⊤).comap (fun omega => (omega,(3 : ℝ)^N • x))
    (measurable_id.prodMk measurable_const)).map (rescale M N)
  let right := (KN N).comap (fun xi => (xi,x)) (measurable_id.prodMk measurable_const)
  change ((physicalLaw M).toMeasure.bind left) B =
    ((chaosSampleLaw M).toMeasure.bind right) B
  rw [Measure.bind_apply hB left.aemeasurable, Measure.bind_apply hB right.aemeasurable]
  change (∫⁻ omega, left omega B ∂(physicalLaw M).toMeasure) = _
  rw [← (physicalEnvironment_preserving M N 0).lintegral_comp
      (Kernel.measurable_coe left hB),
    ← (bilateralEnvironment_preserving M).lintegral_comp (Kernel.measurable_coe right hB)]
  apply lintegral_congr_ae
  filter_upwards [top_path_attachment hscale M H hH PN KN hKN hin X hX hphysical N]
    with eta h
  dsimp only [left, right]
  rw [Kernel.map_apply _ hm, Kernel.comap_apply, Kernel.comap_apply, h x]


theorem top_annealed_integral {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hscale : MassiveUnscale d) (M : GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N)) (hin : CutoffAttachment M H PN KN)
    (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d))
    (hX : ∀ L, IsMarkovKernel (X L)) (hphysical : IsPhysicalFamily M X)
    (N : ℕ) (x : SpatialCoordinates d) (G : BoundedContinuousFunction (DiffusionPath d) ℝ) :
    (∫ omega, ∫ w, G (rescale M N w) ∂X ⊤ (omega, (3 : ℝ)^N • x)
      ∂(physicalLaw M).toMeasure) =
    ∫ omega, ∫ w, G w ∂KN N (omega, x) ∂(chaosSampleLaw M).toMeasure := by
  have h := congrArg (fun P : ProbabilityMeasure (DiffusionPath d) =>
    ∫ w, G w ∂(P : Measure (DiffusionPath d)))
      (top_annealed_attachment hscale M H hH PN KN hKN hin X hX hphysical N x)
  simpa only [annealedSequence_integral, annealedRow_integral, id_eq, ite_true] using h

/-- Every legacy annealed limit is a physical untruncated annealed limit. -/
theorem exists_annealed_limit {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hscale : MassiveUnscale d) (M : GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N)) (hin : CutoffAttachment M H PN KN)
    (phi : ℕ → ℕ) (xs : ℕ → SpatialCoordinates d) (P : ProbabilityMeasure (DiffusionPath d))
    (hlimit : ∀ G : BoundedContinuousFunction (DiffusionPath d) ℝ,
      Tendsto (fun n => ∫ omega, ∫ w, G w ∂KN (phi n) (omega, xs n)
        ∂(chaosSampleLaw M).toMeasure) atTop (𝓝 (∫ w, G w ∂(P : Measure (DiffusionPath d))))) :
    ∃ X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d),
      (∀ L, IsMarkovKernel (X L)) ∧ IsPhysicalFamily M X ∧
      (∀ G : BoundedContinuousFunction (DiffusionPath d) ℝ,
        Tendsto (fun n => ∫ omega, ∫ w, G (rescale M (phi n) w)
          ∂X ⊤ (omega, (3 : ℝ)^(phi n) • xs n) ∂(physicalLaw M).toMeasure) atTop
            (𝓝 (∫ w, G w ∂(P : Measure (DiffusionPath d))))) := by
  obtain ⟨X, hX, hphysical⟩ := exists_physical_family M
  refine ⟨X, hX, hphysical, ?_⟩
  intro G
  convert hlimit G using 1
  funext n
  exact top_annealed_integral hscale M H hH PN KN hKN hin X hX hphysical (phi n) (xs n) G

end SubdiffusiveProcess.Section10.LegacyPhysicalAttachment
