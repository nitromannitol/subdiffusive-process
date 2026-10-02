import SubdiffusiveProcess.Lane3.BandFiltration
import SubdiffusiveProcess.Lane3.LevyUpward
import Mathlib.Tactic




open MeasureTheory ProbabilityTheory Filter Set Topology

noncomputable section

namespace SubdiffusiveProcess
namespace Lane3

instance bandSetDecidable (H : ℕ) : DecidablePred (fun j : ℤ => j ∈ bandSet H) :=
  fun j => decidable_of_iff (-(H : ℤ) ≤ j ∧ j ≤ (H : ℤ)) (by simp [bandSet, Set.mem_Icc])

section Split

variable {Y : ℤ → Type} [instY : ∀ j, MeasurableSpace (Y j)]
  (laws : (j : ℤ) → Measure (Y j)) [instP : ∀ j, IsProbabilityMeasure (laws j)]

/-- The split of the layer product at band radius `H`: the retained block is
the complement of the band. -/
def bandSplit (H : ℕ) :
    ((j : ℤ) → Y j) ≃ᵐ (((i : {j : ℤ // j ∉ bandSet H}) → Y i.1) ×
      ((i : {j : ℤ // ¬ (j ∉ bandSet H)}) → Y i.1)) :=
  MeasurableEquiv.piEquivPiSubtypeProd Y (fun j => j ∉ bandSet H)

theorem bandSplit_symm_apply (H : ℕ) (ω ω' : (j : ℤ) → Y j) :
    (bandSplit (Y := Y) H).symm
        (((bandSplit (Y := Y) H) ω).1, ((bandSplit (Y := Y) H) ω').2) =
      fun j => if j ∈ bandSet H then ω' j else ω j := by
  funext j
  show (if _h : j ∉ bandSet H then ω j else ω' j) = _
  by_cases hj : j ∈ bandSet H
  · rw [dif_neg (by simpa using hj), if_pos hj]
  · rw [dif_pos hj, if_neg hj]

theorem measurePreserving_bandSplit (H : ℕ) :
    MeasurePreserving (bandSplit (Y := Y) H) (Measure.infinitePi laws)
      ((Measure.infinitePi fun i : {j : ℤ // j ∉ bandSet H} => laws i.1).prod
        (Measure.infinitePi fun i : {j : ℤ // ¬ (j ∉ bandSet H)} => laws i.1)) :=
  measurePreserving_infinitePi_split laws (fun j => j ∉ bandSet H)


end Split

/-- **Lemma `mfd:lem-endpoints`** (proposed statement L3-C6), paper lines
3223-3272: an optimal endpoint invariant under resampling any finite set of
layers is almost surely constant. -/
theorem deterministic_endpoints
    (Y : ℤ → Type) [instY : ∀ j, MeasurableSpace (Y j)]
    (laws : (j : ℤ) → Measure (Y j)) [instP : ∀ j, IsProbabilityMeasure (laws j)]
    (m : ((j : ℤ) → Y j) → ℝ) (hm : Measurable m)
    (Cb : ℝ) (hbdd : ∀ ω, |m ω| ≤ Cb)
    (hinv : ∀ S : Finset ℤ,
      ∀ᵐ z ∂((Measure.infinitePi laws).prod (Measure.infinitePi laws)),
        m z.1 = m (fun j => if j ∈ S then z.2 j else z.1 j)) :
    ∃ c : ℝ, ∀ᵐ ω ∂(Measure.infinitePi laws), m ω = c := by
  classical
  have hint : Integrable m (Measure.infinitePi laws) := by
    have hmem : MemLp m ⊤ (Measure.infinitePi laws) :=
      memLp_top_of_bound hm.aestronglyMeasurable Cb
        (Filter.Eventually.of_forall fun ω => by
          simpa [Real.norm_eq_abs] using hbdd ω)
    exact hmem.integrable le_top
  have hcond : ∀ H : ℕ,
      (Measure.infinitePi laws)[m | (bandFiltration (Y := Y)) H] =ᵐ[Measure.infinitePi laws]
        fun _ => ∫ ω, m ω ∂(Measure.infinitePi laws) := by
    intro H
    have hinv' : ∀ᵐ z ∂((Measure.infinitePi laws).prod (Measure.infinitePi laws)),
        m z.1 = m ((bandSplit (Y := Y) H).symm
          (((bandSplit (Y := Y) H) z.1).1, ((bandSplit (Y := Y) H) z.2).2)) := by
      filter_upwards [hinv (Finset.Icc (-(H : ℤ)) (H : ℤ))] with z hz
      have hfun : (fun j => if j ∈ Finset.Icc (-(H : ℤ)) (H : ℤ) then z.2 j else z.1 j)
          = fun j => if j ∈ bandSet H then z.2 j else z.1 j := by
        funext j
        by_cases hj : j ∈ bandSet H
        · rw [if_pos hj, if_pos (by simpa [bandSet, Finset.mem_Icc, Set.mem_Icc] using hj)]
        · rw [if_neg hj, if_neg (by simpa [bandSet, Finset.mem_Icc, Set.mem_Icc] using hj)]
      rw [bandSplit_symm_apply, ← hfun]
      exact hz
    have hae := ae_eq_condExp_of_resample_invariant
      (P := Measure.infinitePi laws)
      (mu := Measure.infinitePi fun i : {j : ℤ // j ∉ bandSet H} => laws i.1)
      (nu := Measure.infinitePi fun i : {j : ℤ // ¬ (j ∉ bandSet H)} => laws i.1)
      (bandSplit (Y := Y) H) (measurePreserving_bandSplit laws H) m hm hint hinv'
    have hdisj : Disjoint ((bandSet H)ᶜ) (bandSet H) := disjoint_compl_left
    have hif := indepFun_restrict_infinitePi laws ((bandSet H)ᶜ) (bandSet H) hdisj
    rw [IndepFun_iff_Indep] at hif
    have hmcle : ((inferInstance : MeasurableSpace ((i : {j : ℤ // j ∉ bandSet H}) → Y i.1)).comap
        fun x => ((bandSplit (Y := Y) H) x).1) ≤
        (inferInstance : MeasurableSpace ((j : ℤ) → Y j)) :=
      (((bandSplit (Y := Y) H).measurable).fst).comap_le
    have hindep : Indep ((inferInstance :
        MeasurableSpace ((i : {j : ℤ // j ∉ bandSet H}) → Y i.1)).comap
        fun x => ((bandSplit (Y := Y) H) x).1) (bandSigma Y H)
        (Measure.infinitePi laws) := by
      rw [bandSigma_eq_comap]
      exact hif
    exact condExp_eq_integral_of_ae_condExp_of_indep _ _ hmcle (bandSigma_le H)
      hindep m hint hae
  have hgmeas : StronglyMeasurable[⨆ H : ℕ, (bandFiltration (Y := Y)) H] m := by
    have h1 : (⨆ H : ℕ, (bandFiltration (Y := Y)) H) =
        (inferInstance : MeasurableSpace ((j : ℤ) → Y j)) := iSup_bandFiltration
    rw [h1]
    exact hm.stronglyMeasurable
  exact ae_eq_integral_of_condExp_eq_integral (bandFiltration (Y := Y)) m hint hgmeas hcond

end Lane3
end SubdiffusiveProcess
