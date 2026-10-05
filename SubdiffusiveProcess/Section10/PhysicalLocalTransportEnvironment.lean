module

public import SubdiffusiveProcess.Section10.PhysicalAttachmentCoefficients
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Action
public import SubdiffusiveProcess.Probability.NativeCommonScaleLaw
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Homogenization Set
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalLocalTransport

variable {d : ℕ}

/-- A genuine coupling carrier: bilateral independent copies of the native root field. -/
abbrev NativeEnvironment (d : ℕ) := ℤ → PotentialField d

def nativeLaw (M : GMCModel d) : Measure (NativeEnvironment d) :=
  Measure.infinitePi (fun _ : ℤ => (zeroPotentialLaw M.P).toMeasure)

instance (M : GMCModel d) : IsProbabilityMeasure (nativeLaw M) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi _))

/-- Select the natural physical layers from the bilateral independent root copies. -/
def naturalSample (m : ℕ) (eta : NativeEnvironment d) : PotentialSample d :=
  fun k => _root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k (eta ((k : ℤ) - m))

theorem measurable_naturalSample (m : ℕ) : Measurable (naturalSample (d := d) m) :=
  measurable_pi_iff.mpr fun k =>
    (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_triadicScale k).comp (measurable_pi_apply _)

theorem naturalSample_preserving (M : GMCModel d) (m : ℕ) :
    MeasurePreserving (naturalSample m) (nativeLaw M) M.P.toMeasure := by
  have hind : iIndepFun (fun j : ℤ => fun eta : NativeEnvironment d => eta j)
      (nativeLaw M) := iIndepFun_infinitePi (fun _ => measurable_id)
  have hinj : Function.Injective (fun k : ℕ => (k : ℤ) - m) := by
    intro k l h
    change (k : ℤ) - (m : ℤ) = (l : ℤ) - (m : ℤ) at h
    have hh : (k : ℤ) = l := by omega
    exact_mod_cast hh
  have hnat := (hind.precomp hinj).comp (fun k => _root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k)
    (fun k => _root_.SubdiffusiveProcess.Model.PotentialField.measurable_triadicScale k)
  refine ⟨measurable_naturalSample m, ?_⟩
  have hsource := (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun k : ℕ => measurable_pi_apply k)).mp M.shellPrefix.independent
  have htarget := (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun k : ℕ => (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_triadicScale k).comp
      (measurable_pi_apply ((k : ℤ) - m)))).mp hnat
  change Measure.map (naturalSample m) (nativeLaw M) = M.P.toMeasure
  rw [show M.P.toMeasure = Measure.infinitePi
    (fun k : ℕ => M.P.toMeasure.map (fun omega => omega k)) by
      change Measure.map id M.P.toMeasure = _ at hsource
      simpa only [Measure.map_id] using hsource]
  rw [show Measure.map (naturalSample m) (nativeLaw M) = _ from htarget]
  congr 1
  funext k
  change Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k ∘ (fun eta => eta ((k : ℤ) - m)))
      (nativeLaw M) = (potentialMarginalLaw M.P k).toMeasure
  rw [← Measure.map_map (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_triadicScale k)
    (measurable_pi_apply (((k : ℤ) - m)) : Measurable
      (fun eta : NativeEnvironment d => eta ((k : ℤ) - m)))]
  change Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k)
    ((Measure.infinitePi (fun _ : ℤ => (zeroPotentialLaw M.P).toMeasure)).map
      (fun eta => eta ((k : ℤ) - m))) = _
  rw [Measure.infinitePi_map_eval]
  exact congrArg ProbabilityMeasure.toMeasure (M.shellPrefix.marginal_scaling k).symm

/-- Physical samples centered so that their local fields have the canonical bilateral law. -/
def rawSample (m : ℕ) (z : Vec d) : NativeEnvironment d → PotentialSample d :=
  translatePotentialSample (-z) ∘ naturalSample m

theorem rawSample_preserving (M : GMCModel d) (m : ℕ) (z : Vec d) :
    MeasurePreserving (rawSample m z) (nativeLaw M) M.P.toMeasure :=
  (Section6Covariance.measurePreserving_translatePotentialSample M (-z)).comp
    (naturalSample_preserving M m)

theorem ae_good (M : GMCModel d) :
    ∀ᵐ omega ∂M.P.toMeasure, omega ∈ anchoredC11GoodSet d :=
  (mem_ae_iff_prob_eq_one (Section6Anchored.measurableSet_anchoredC11GoodSet d)).mpr
    (Section6Anchored.measure_anchoredC11GoodSet_eq_one M)

def defaultAnchored (M : GMCModel d) : AnchoredC11Sample d :=
  ⟨Classical.choose (ae_good M).exists, Classical.choose_spec (ae_good M).exists⟩

/-- A measurable representative of restriction to the actual full anchored event. -/
def anchor (M : GMCModel d) (omega : PotentialSample d) : AnchoredC11Sample d := by
  classical
  exact ⟨if omega ∈ anchoredC11GoodSet d then omega else (defaultAnchored M).val, by
    split_ifs with h
    · exact h
    · exact (defaultAnchored M).property⟩

theorem measurable_anchor (M : GMCModel d) : Measurable (anchor M) := by
  classical
  exact (Measurable.ite (Section6Anchored.measurableSet_anchoredC11GoodSet d)
    measurable_id measurable_const).subtype_mk

theorem anchor_val (M : GMCModel d) {omega : PotentialSample d}
    (h : omega ∈ anchoredC11GoodSet d) : (anchor M omega).val = omega := by
  simp [anchor, h]

theorem physicalLaw_val_preserving (M : GMCModel d) :
    MeasurePreserving (Subtype.val : AnchoredC11Sample d → PotentialSample d)
      (PhysicalAttachment.physicalLaw M).toMeasure M.P.toMeasure := by
  refine ⟨measurable_subtype_coe, ?_⟩
  change Measure.map Subtype.val (Measure.comap Subtype.val M.P.toMeasure) = _
  rw [map_comap_subtype_coe (Section6Anchored.measurableSet_anchoredC11GoodSet d),
    Measure.restrict_eq_self_of_ae_mem (ae_good M)]

theorem anchor_preserving (M : GMCModel d) :
    MeasurePreserving (anchor M) M.P.toMeasure
      (PhysicalAttachment.physicalLaw M).toMeasure := by
  refine ⟨measurable_anchor M, ?_⟩
  have hmap : Measure.map Subtype.val (Measure.map (anchor M) M.P.toMeasure) =
      M.P.toMeasure := by
    rw [Measure.map_map measurable_subtype_coe (measurable_anchor M)]
    calc
      Measure.map (Subtype.val ∘ anchor M) M.P.toMeasure =
          Measure.map id M.P.toMeasure := Measure.map_congr <| by
        filter_upwards [ae_good M] with omega h
        exact anchor_val M h
      _ = M.P.toMeasure := Measure.map_id
  have hemb := MeasurableEmbedding.subtype_coe
    (Section6Anchored.measurableSet_anchoredC11GoodSet d)
  have hh := congrArg (Measure.comap (Subtype.val : AnchoredC11Sample d → PotentialSample d))
    hmap
  rw [hemb.comap_map] at hh
  exact hh

def physicalEnvironment (M : GMCModel d) (m : ℕ) (z : Vec d) :
    NativeEnvironment d → AnchoredC11Sample d := anchor M ∘ rawSample m z

theorem physicalEnvironment_preserving (M : GMCModel d) (m : ℕ) (z : Vec d) :
    MeasurePreserving (physicalEnvironment M m z) (nativeLaw M)
      (PhysicalAttachment.physicalLaw M).toMeasure :=
  (anchor_preserving M).comp (rawSample_preserving M m z)

variable [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)]

def bilateralEnvironment (eta : NativeEnvironment d) : BilateralField d :=
  fun j => layerScaling d j (eta j).1.1

theorem bilateralEnvironment_preserving (M : GMCModel d) :
    MeasurePreserving bilateralEnvironment (nativeLaw M) (chaosSampleLaw M).toMeasure :=
  measurePreserving_nativeCopies_commonScaleLaw M

omit [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)] in
theorem rawSample_local (m k : ℕ) (z x : Vec d) (eta : NativeEnvironment d) :
    rawSample m z eta k (z + (3 : ℝ) ^ m • x) =
      bilateralEnvironment eta ((k : ℤ) - m) x := by
  change eta ((k : ℤ) - m)
      (((3 : ℝ) ^ k)⁻¹ • (z + (3 : ℝ) ^ m • x + -z)) =
    eta ((k : ℤ) - m) ((3 : ℝ) ^ (-((k : ℤ) - m)) • x)
  rw [add_neg_cancel_comm, smul_smul]
  congr 2
  rw [neg_sub, zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast, zpow_natCast]
  exact mul_comm _ _

omit [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)] in
/-- On one full event, every physical layer agrees with its shifted bilateral local layer. -/
theorem physicalEnvironment_local {d : ℕ} [_ms : MeasurableSpace C(Vec d, ℝ)] [_borel : BorelSpace C(Vec d, ℝ)]
    (M : GMCModel d) (m : ℕ) (z : Vec d) :
    ∀ᵐ eta ∂nativeLaw M, ∀ k : ℕ, ∀ x : Vec d,
      (physicalEnvironment M m z eta).val k (z + (3 : ℝ) ^ m • x) =
        bilateralEnvironment eta ((k : ℤ) - m) x := by
  filter_upwards [(rawSample_preserving M m z).quasiMeasurePreserving.tendsto_ae.eventually (ae_good M)] with eta h
  intro k x
  rw [show (physicalEnvironment M m z eta).val = rawSample m z eta from anchor_val M h]
  exact rawSample_local m k z x eta

/-- The literal finite window on the actual anchored sample space. -/
def physicalWindow (l m : ℕ) (z : Vec d) (omega : AnchoredC11Sample d) :
    Fin (l + 1) → C(Vec d, ℝ) := fun k =>
  (omega.val k).1.1.comp
    ⟨fun x => z + (3 : ℝ) ^ m • x, by fun_prop⟩

def bilateralWindow (l m : ℕ) (xi : BilateralField d) : Fin (l + 1) → C(Vec d, ℝ) :=
  fun k => xi ((k.val : ℤ) - m)

def windowLaw (M : GMCModel d) (l m : ℕ) : Measure (Fin (l + 1) → C(Vec d, ℝ)) :=
  Measure.pi (fun k : Fin (l + 1) =>
    (scaledLayerLaw d (chaosRootFieldLaw M) ((k.val : ℤ) - m)).toMeasure)

theorem measurable_physicalWindow (l m : ℕ) (z : Vec d) :
    Measurable (physicalWindow (d := d) l m z) := by
  let forget : C(PotentialField d, C(Vec d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  apply measurable_pi_iff.mpr
  intro k
  have hcoord : Measurable (fun omega : AnchoredC11Sample d => omega.val k.val) :=
    (measurable_pi_apply k.val).comp measurable_subtype_coe
  exact (ContinuousMap.continuous_precomp _).measurable.comp
    (forget.continuous.measurable.comp hcoord)

theorem bilateralWindow_preserving (M : GMCModel d) (l m : ℕ) :
    MeasurePreserving (bilateralWindow l m) (chaosSampleLaw M).toMeasure (windowLaw M l m) := by
  have hind : iIndepFun (fun j : ℤ => fun xi : BilateralField d => xi j)
      (chaosSampleLaw M).toMeasure := iIndepFun_infinitePi (fun _ => measurable_id)
  have hinj : Function.Injective (fun k : Fin (l + 1) => (k.val : ℤ) - m) := by
    intro k j h
    apply Fin.ext
    change (k.val : ℤ) - (m : ℤ) = (j.val : ℤ) - (m : ℤ) at h
    omega
  refine ⟨measurable_pi_iff.mpr (fun k => measurable_pi_apply _), ?_⟩
  rw [show (chaosSampleLaw M).toMeasure.map (bilateralWindow l m) =
      Measure.pi (fun k : Fin (l + 1) =>
        (chaosSampleLaw M).toMeasure.map (fun xi => xi ((k.val : ℤ) - m))) from
    (iIndepFun_iff_map_fun_eq_pi_map (fun k => (measurable_pi_apply _).aemeasurable)).mp
      (hind.precomp hinj)]
  unfold windowLaw
  congr 1
  funext k
  exact Measure.infinitePi_map_eval _ _

/-- Exact pushforward of the physical law, for every finite cutoff and every scale and center. -/
theorem physicalWindow_preserving (M : GMCModel d) (l m : ℕ) (z : Vec d) :
    MeasurePreserving (physicalWindow l m z) (PhysicalAttachment.physicalLaw M).toMeasure
      (windowLaw M l m) := by
  refine ⟨measurable_physicalWindow l m z, ?_⟩
  rw [← (physicalEnvironment_preserving M m z).map_eq,
    Measure.map_map (measurable_physicalWindow l m z)
      (physicalEnvironment_preserving M m z).measurable]
  calc
    Measure.map (physicalWindow l m z ∘ physicalEnvironment M m z) (nativeLaw M) =
        Measure.map (bilateralWindow l m ∘ bilateralEnvironment) (nativeLaw M) := by
      apply Measure.map_congr
      filter_upwards [physicalEnvironment_local M m z] with eta h
      funext k
      ext x
      change (physicalEnvironment M m z eta).val k.val
        (z + (3 : ℝ) ^ m • x) = bilateralEnvironment eta ((k.val : ℤ) - m) x
      exact h k.val x
    _ = windowLaw M l m :=
      ((bilateralWindow_preserving M l m).comp (bilateralEnvironment_preserving M)).map_eq

end SubdiffusiveProcess.Section10.PhysicalLocalTransport
