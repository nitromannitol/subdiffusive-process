import SubdiffusiveProcess.PartProcess.Data
import Mathlib.Topology.Compactness.SigmaCompact
import SubdiffusiveProcess.Processes.E7.Occupation
import SubdiffusiveProcess.PartProcess.CompactCoverExit

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.PartProcess
open SubdiffusiveProcess.E7

/-- Compact exhaustion of an open region, cofinal among its compact subsets. -/
structure CompactCover {d : ℕ} (U : Set (Fin d → ℝ)) where
  sets : ℕ → Set (Fin d → ℝ)
  compact : ∀ n, IsCompact (sets n)
  monotone : Monotone sets
  subset : ∀ n, sets n ⊆ U
  cofinal : ∀ A, IsCompact A → A ⊆ U → ∃ n, A ⊆ sets n

theorem exists_compactCover {d : ℕ} (U : Set (Fin d → ℝ)) (hU : IsOpen U) :
    Nonempty (CompactCover U) := by
  letI : LocallyCompactSpace U := hU.locallyCompactSpace
  let K := CompactExhaustion.choice U
  refine ⟨⟨fun n => Subtype.val '' K n,
    fun n => (K.isCompact n).image continuous_subtype_val,
    fun _ _ h => image_mono (K.subset h),
    fun n => Subtype.coe_image_subset U (K n), ?_⟩⟩
  intro A hA hAU
  have hpre : IsCompact ((Subtype.val : U → Fin d → ℝ) ⁻¹' A) :=
    (Topology.IsEmbedding.subtypeVal.isCompact_iff).2 (by
      simpa only [Subtype.image_preimage_val, inter_eq_right.2 hAU] using hA)
  obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact hpre
  exact ⟨n, fun x hx => ⟨⟨x, hAU hx⟩, hn hx, rfl⟩⟩

theorem CompactCover.iUnion_survival {d : ℕ} {U : Set (Fin d → ℝ)}
    (C : CompactCover U) (t : ℝ≥0∞) :
    (⋃ n, {w : ContinuousPath (Fin d → ℝ) | t < ContinuousPath.exitTime (C.sets n) w}) =
      {w | t < ContinuousPath.exitTime U w} := by
  ext w
  simp only [mem_iUnion, mem_setOf_eq]
  constructor
  · rintro ⟨n, hn⟩
    exact hn.trans_le (ContinuousPath.exitTime_mono (C.subset n) w)
  · intro ht
    obtain ⟨r, htr, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
    have hK : IsCompact ((w : NNReal → Fin d → ℝ) '' Icc 0 r) :=
      isCompact_Icc.image w.continuous
    have hKU : (w : NNReal → Fin d → ℝ) '' Icc 0 r ⊆ U := by
      rintro _ ⟨s, hs, rfl⟩
      exact ContinuousPath.mem_of_lt_exitTime U w s
        ((ENNReal.coe_le_coe.2 hs.2).trans_lt hr)
    obtain ⟨n, hn⟩ := C.cofinal _ hK hKU
    refine ⟨n, htr.trans_le ?_⟩
    apply (ContinuousPath.le_exitTime_iff _ w _).2
    intro s hs
    have hsr : r < s := by
      by_contra h
      exact hs (hn ⟨s, ⟨zero_le _, le_of_not_gt h⟩, rfl⟩)
    exact (ENNReal.coe_lt_coe.2 hsr).le

theorem killedOcc_compactCover_tendsto {d : ℕ}
    (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ))) (hK : IsMarkovKernel K)
    (U : Set (Fin d → ℝ)) (hU : IsOpen U) (C : CompactCover U)
    (α : ℝ) (f : (Fin d → ℝ) → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (x : Fin d → ℝ) :
    Tendsto (fun n => killedOcc K (C.sets n) α f x) atTop
      (𝓝 (killedOcc K U α f x)) := by
  have hmono : Monotone (fun n => killedOcc K (C.sets n) α f x) :=
    fun _ _ h => killedOcc_mono K (C.monotone h) α f x
  have heq : killedOcc K U α f x = ⨆ n, killedOcc K (C.sets n) α f x := by
    simp_rw [killedOcc_continuousPath]
    have hslice : ∀ t : ℝ,
        (∫⁻ w in {w | ENNReal.ofReal t < ContinuousPath.exitTime U w},
          ENNReal.ofReal (f (w (Real.toNNReal t))) ∂(K x)) =
        ⨆ n, ∫⁻ w in {w | ENNReal.ofReal t < ContinuousPath.exitTime (C.sets n) w},
          ENNReal.ofReal (f (w (Real.toNNReal t))) ∂(K x) := by
      intro t
      rw [← C.iUnion_survival]
      exact setLIntegral_iUnion_of_directed _ (Monotone.directed_le
        (fun _ _ h w hw => hw.trans_le (ContinuousPath.exitTime_mono (C.monotone h) w)))
    simp_rw [hslice, ENNReal.mul_iSup]
    apply lintegral_iSup
    · intro n
      exact (ENNReal.measurable_ofReal.comp
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable).mul
        (killedOcc_slice_measurable K hK _ (measurable_closed_exit _ (C.compact n).isClosed)
          f hf x)
    · intro i j hij t
      apply mul_le_mul_right
      apply lintegral_mono' (Measure.restrict_mono_set _ ?_) le_rfl
      intro w hw
      exact hw.trans_le (ContinuousPath.exitTime_mono (C.monotone hij) w)
  rw [heq]
  exact tendsto_atTop_iSup hmono

end SubdiffusiveProcess.PartProcess
