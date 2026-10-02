import SubdiffusiveProcess.CoarseGrainingVocab.Section6MeasurableMaxPrinciple

namespace SubdiffusiveProcess

open MeasureTheory Set TopologicalSpace

noncomputable section



theorem abs_le_on_of_ae_restrict_of_continuousOn
    {d : ℕ} {W : Set (Homogenization.Vec d)}
    (hW : IsOpen W) (g : Homogenization.Vec d → ℝ) (M : ℝ)
    (hg : ContinuousOn g W)
    (hae : ∀ᵐ x ∂volume.restrict W, |g x| ≤ M) :
    ∀ x ∈ W, |g x| ≤ M := by
  have hgabs : ContinuousOn (fun x => |g x|) W := continuous_abs.comp_continuousOn hg
  have hS_open : IsOpen (W ∩ {x : Homogenization.Vec d | M < |g x|}) := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨hxW, hxgt⟩
    have hWnhds : W ∈ nhds x := hW.mem_nhds hxW
    have hcont : ContinuousAt (fun y => |g y|) x := hgabs.continuousAt hWnhds
    have htnhds : Set.Ioi M ∈ nhds (|g x|) := isOpen_Ioi.mem_nhds hxgt
    have hpre : (fun y => |g y|) ⁻¹' Set.Ioi M ∈ nhds x := hcont.preimage_mem_nhds htnhds
    exact Filter.inter_mem hWnhds hpre
  have hnull : volume.restrict W {x : Homogenization.Vec d | ¬ |g x| ≤ M} = 0 :=
    MeasureTheory.ae_iff.mp hae
  have hset_eq :
      {x : Homogenization.Vec d | ¬ |g x| ≤ M}
        = {x : Homogenization.Vec d | M < |g x|} := by
    ext x
    exact not_le
  rw [hset_eq] at hnull
  have hrestrict :
      volume.restrict W {x : Homogenization.Vec d | M < |g x|}
        = volume ({x : Homogenization.Vec d | M < |g x|} ∩ W) :=
    MeasureTheory.Measure.restrict_apply' hW.measurableSet
  rw [hrestrict] at hnull
  have hS_measure_zero : volume (W ∩ {x : Homogenization.Vec d | M < |g x|}) = 0 := by
    rw [Set.inter_comm]
    exact hnull
  have hS_empty : W ∩ {x : Homogenization.Vec d | M < |g x|} = ∅ := by
    by_contra hne
    exact hS_open.measure_ne_zero volume (Set.nonempty_iff_ne_empty.mpr hne) hS_measure_zero
  intro x hxW
  by_contra hcon
  have hxmem : x ∈ W ∩ {x : Homogenization.Vec d | M < |g x|} :=
    ⟨hxW, not_le.mp hcon⟩
  rw [hS_empty] at hxmem
  exact Set.notMem_empty x hxmem

end
end SubdiffusiveProcess
