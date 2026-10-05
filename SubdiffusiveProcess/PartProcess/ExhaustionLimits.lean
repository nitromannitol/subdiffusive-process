module

public import SubdiffusiveProcess.PartProcess.CompactCover
public import SubdiffusiveProcess.PartProcess.GraphConvergence

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.PartProcess

/-- An extended-real pointwise limit agrees with the almost-everywhere subsequence
limit supplied by convergence in `L²`. -/
theorem association_of_limits {X : Type*} [MeasurableSpace X] {m : Measure X}
    (r : ℕ → X → ℝ≥0∞) (g : X → ℝ≥0∞)
    (u : ℕ → Lp ℝ 2 m) (v : Lp ℝ 2 m)
    (hfin : ∀ n, ∀ᵐ x ∂m, r n x < ⊤)
    (heq : ∀ n, (fun x => (r n x).toReal) =ᵐ[m] ⇑(u n))
    (hlim : Tendsto u atTop (𝓝 v))
    (hpoint : ∀ x, Tendsto (fun n => r n x) atTop (𝓝 (g x))) :
    (∀ᵐ x ∂m, g x < ⊤) ∧ (fun x => (g x).toReal) =ᵐ[m] ⇑v := by
  obtain ⟨ns, hns, hsub⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have H : ∀ᵐ x ∂m, g x < ⊤ ∧ (g x).toReal = v x := by
    filter_upwards [hsub, ae_all_iff.2 hfin, ae_all_iff.2 heq] with x hx hfx hex
    have hpos : 0 ≤ v x := ge_of_tendsto' hx fun k => by
      rw [← hex (ns k)]
      exact ENNReal.toReal_nonneg
    have ht : Tendsto (fun k => r (ns k) x) atTop (𝓝 (ENNReal.ofReal (v x))) := by
      apply (ENNReal.tendsto_ofReal hx).congr
      intro k
      rw [← hex (ns k), ENNReal.ofReal_toReal (hfx (ns k)).ne]
    have he : g x = ENNReal.ofReal (v x) :=
      tendsto_nhds_unique ((hpoint x).comp hns.tendsto_atTop) ht
    exact ⟨by rw [he]; exact ENNReal.ofReal_lt_top,
      by rw [he, ENNReal.toReal_ofReal hpos]⟩
  exact ⟨H.mono fun _ h => h.1, H.mono fun _ h => h.2⟩

end SubdiffusiveProcess.PartProcess
