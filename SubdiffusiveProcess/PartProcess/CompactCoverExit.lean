import SubdiffusiveProcess.PartProcess.Data
import SubdiffusiveProcess.Processes.E7.Occupation
import MarkovProcess.Lifetime.CountablySeparated
import MarkovProcess.Path.Exhaustion

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.PartProcess
open SubdiffusiveProcess.E7

private theorem cemetery_borel {d : ℕ} : BorelSpace (Cemetery (Fin d → ℝ)) := by
  constructor
  apply le_antisymm
  · letI : MeasurableSpace (Cemetery (Fin d → ℝ)) := borel _
    letI : BorelSpace (Cemetery (Fin d → ℝ)) := ⟨rfl⟩
    intro s hs
    obtain ⟨hl, hr⟩ := hs
    change MeasurableSet ((Sum.inl : (Fin d → ℝ) → Cemetery (Fin d → ℝ)) ⁻¹' s) at hl
    change MeasurableSet ((Sum.inr : Unit → Cemetery (Fin d → ℝ)) ⁻¹' s) at hr
    have el : MeasurableEmbedding (Sum.inl : (Fin d → ℝ) → Cemetery (Fin d → ℝ)) :=
      Topology.IsOpenEmbedding.inl.measurableEmbedding
    have er : MeasurableEmbedding (Sum.inr : Unit → Cemetery (Fin d → ℝ)) :=
      Topology.IsOpenEmbedding.inr.measurableEmbedding
    have hli := el.measurableSet_image.2 hl
    have hri := er.measurableSet_image.2 hr
    convert hli.union hri using 1
    ext x
    cases x with
    | inl x => simp
    | inr x =>
      cases x
      simp only [mem_union, mem_image, mem_preimage, Sum.inr.injEq,
        Sum.inl_ne_inr, and_false, exists_false, false_or, exists_eq_right]
      constructor
      · intro h
        exact ⟨(), h, trivial⟩
      · rintro ⟨x, hx⟩
        cases x
        exact hx.1
  · apply MeasurableSpace.generateFrom_le
    intro s hs
    exact ⟨(isOpen_sum_iff.1 hs).1.measurableSet, (isOpen_sum_iff.1 hs).2.measurableSet⟩

theorem closed_exit_lt_iff {d : ℕ} (A : Set (Fin d → ℝ)) (hA : IsClosed A)
    (w : ContinuousPath (Fin d → ℝ)) (a : ℝ≥0∞) :
    ContinuousPath.exitTime A w < a ↔
      ∃ n : ℕ, (DenseTime.castOrderEmbedding (DenseTime.enumeration n) : ℝ≥0∞) < a ∧
        w (DenseTime.castOrderEmbedding (DenseTime.enumeration n)) ∉ A := by
  constructor
  · intro h
    obtain ⟨_, ⟨t, rfl, ht⟩, hta⟩ := sInf_lt_iff.1 h
    let O : Set NNReal := {s | (s : ℝ≥0∞) < a} ∩ (w : NNReal → Fin d → ℝ) ⁻¹' Aᶜ
    have hO : IsOpen O :=
      (isOpen_lt ENNReal.continuous_coe continuous_const).inter
        (hA.isOpen_compl.preimage w.continuous)
    obtain ⟨b, c, hbc, hsub⟩ := hO.exists_Ioo_subset ⟨t, hta, ht⟩
    obtain ⟨q, hbq, hqc⟩ := DenseTime.exists_cast_btwn hbc
    refine ⟨DenseTime.enumeration.symm q, ?_⟩
    simpa only [Equiv.apply_symm_apply] using hsub ⟨hbq, hqc⟩
  · rintro ⟨n, hn, hbad⟩
    exact (ContinuousPath.exitTime_le_of_notMem A w _ hbad).trans_lt hn

theorem measurable_closed_exit {d : ℕ} (A : Set (Fin d → ℝ)) (hA : IsClosed A) :
    Measurable (ContinuousPath.exitTime A) := by
  apply measurable_of_Iio
  intro a
  have heq : ContinuousPath.exitTime A ⁻¹' Iio a =
      ⋃ n : ℕ, if (DenseTime.castOrderEmbedding (DenseTime.enumeration n) : ℝ≥0∞) < a
        then (fun w : ContinuousPath (Fin d → ℝ) =>
          w (DenseTime.castOrderEmbedding (DenseTime.enumeration n))) ⁻¹' Aᶜ else ∅ := by
    ext w
    simp only [mem_preimage, mem_Iio, closed_exit_lt_iff A hA, mem_iUnion]
    apply exists_congr
    intro n
    split_ifs <;> simp_all
  rw [heq]
  apply MeasurableSet.iUnion
  intro n
  split_ifs
  · exact (ContinuousPath.measurable_coordinateProcess _) hA.measurableSet.compl
  · exact MeasurableSet.empty

theorem killedOcc_continuousPath {d : ℕ}
    (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ)))
    (U : Set (Fin d → ℝ)) (α : ℝ) (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    killedOcc K U α f x =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-α * t)) *
        ∫⁻ w in {w | ENNReal.ofReal t < ContinuousPath.exitTime U w},
          ENNReal.ofReal (f (w (Real.toNNReal t))) ∂(K x) := by
  letI : PolishSpace (Cemetery (Fin d → ℝ)) := inferInstance
  letI : BorelSpace (Cemetery (Fin d → ℝ)) := cemetery_borel
  letI : StandardBorelSpace (Cemetery (Fin d → ℝ)) := inferInstance
  letI : MeasurableSpace.CountablySeparated (LifetimePath (Fin d → ℝ)) :=
    LifetimePath.instCountablySeparated
  unfold killedOcc
  apply lintegral_congr
  intro t
  congr 1
  rw [Kernel.map_apply K LifetimePath.measurable_ofContinuousPath x,
    LifetimePath.measurableEmbedding_ofContinuousPath.restrict_map,
    LifetimePath.measurableEmbedding_ofContinuousPath.lintegral_map]
  simp only [preimage_setOf_eq, LifetimePath.exitTime_ofContinuousPath, aux_n8_stateAt_ofCP]

theorem killedOcc_mono {d : ℕ}
    (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ)))
    {U V : Set (Fin d → ℝ)} (hUV : U ⊆ V) (α : ℝ)
    (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    killedOcc K U α f x ≤ killedOcc K V α f x := by
  rw [killedOcc_continuousPath, killedOcc_continuousPath]
  apply lintegral_mono
  intro t
  apply mul_le_mul_right
  apply lintegral_mono' (Measure.restrict_mono_set _ ?_) le_rfl
  intro w hw
  exact hw.trans_le (ContinuousPath.exitTime_mono hUV w)

theorem killedOcc_le_free {d : ℕ}
    (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ)))
    (U : Set (Fin d → ℝ)) (α : ℝ) (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    killedOcc K U α f x ≤ potentialOcc K 0 α f x := by
  rw [killedOcc_continuousPath]
  unfold potentialOcc
  apply lintegral_mono
  intro t
  simp only [SubMarkovKernelSemigroup.feynmanKacAdditiveFunctional,
    Pi.zero_apply, intervalIntegral.integral_zero, neg_zero, Real.exp_zero,
    ENNReal.ofReal_one, one_mul]
  exact mul_le_mul_right (lintegral_mono' Measure.restrict_le_self le_rfl) _

theorem killedOcc_slice_measurable {d : ℕ}
    (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ))) (hK : IsMarkovKernel K)
    (A : Set (Fin d → ℝ)) (hA : Measurable (ContinuousPath.exitTime A))
    (f : (Fin d → ℝ) → ℝ) (hf : Measurable f) (x : Fin d → ℝ) :
    Measurable (fun t : ℝ =>
      ∫⁻ w in {w | ENNReal.ofReal t < ContinuousPath.exitTime A w},
        ENNReal.ofReal (f (w (Real.toNNReal t))) ∂(K x)) := by
  letI := hK
  simp_rw [← lintegral_indicator (measurableSet_lt measurable_const hA)]
  exact ((ENNReal.measurable_ofReal.comp (hf.comp aux_n8_measurable_eval)).indicator
    (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
      (hA.comp measurable_snd))).lintegral_prod_right'

end SubdiffusiveProcess.PartProcess
