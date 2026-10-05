module

public import SubdiffusiveProcess.PartProcess.Carrier
public import SubdiffusiveProcess.PartProcess.CompactCover
public import SubdiffusiveProcess.PartProcess.GraphConvergence
public import Mathlib.Topology.Compactness.SigmaCompact

@[expose] public section

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.PartProcess
open SubdiffusiveProcess.E7

theorem coreClosure_compactCover_dense {d : ℕ} {m : Measure (Fin d → ℝ)}
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m) (U : Set (Fin d → ℝ)) (C : CompactCover U)
    (u : Lp ℝ 2 m) (hu : u ∈ E.killedCoreClosure U) (ε : ℝ) (hε : 0 < ε) :
    ∃ n v, v ∈ supportedDomain E (C.sets n) ∧ E.energyNormSq (u - v) < ε := by
  obtain ⟨v, hv, he⟩ := hu.2 ε hε
  obtain ⟨f, hf, hfK, hfU, hvf⟩ := hv.2
  obtain ⟨n, hn⟩ := C.cofinal (tsupport f) hfK hfU
  refine ⟨n, v, ⟨hv.1, ?_⟩, he⟩
  filter_upwards [hvf] with x hx hxA
  rw [hx]
  exact image_eq_zero_of_notMem_tsupport (fun h => hxA (hn h))

/-- Identification on globally square-integrable data, before restricting to `U`. -/
theorem open_association {d : ℕ} {m : Measure (Fin d → ℝ)}
    (hm : IsLocallyFiniteMeasure m) (hpos : m.IsOpenPosMeasure)
    (D : Data d m) (U : Set (Fin d → ℝ)) (hU : IsOpen U)
    (α : ℝ) (hα : 0 < α)
    (G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m)
    (hG : IsDomainResolvent D.form.toClosedForm
      (D.form.toClosedForm.killedCoreClosure U) α G)
    (f : (Fin d → ℝ) → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfL : MemLp f 2 m) :
    (∀ᵐ x ∂m, killedOcc D.law U α f x < ⊤) ∧
    (fun x => (killedOcc D.law U α f x).toReal) =ᵐ[m] ⇑(G (hfL.toLp f)) := by
  classical
  obtain ⟨V, hV, _, C, hC⟩ := D.regular
  let W := U ∩ V
  have hW : IsOpen W := hU.inter hV
  obtain ⟨cv⟩ := exists_compactCover W hW
  have hclosure : D.form.toClosedForm.killedCoreClosure W =
      D.form.toClosedForm.killedCoreClosure U := coreClosure_inter_carrier D.form V C hC U
  let En := fun n => supportedDomain D.form.toClosedForm (cv.sets n)
  have hEn : ∀ n, GraphClosed D.form.toClosedForm (En n) :=
    fun n => graphClosed_supportedDomain _ _
  choose Gn hGn using fun n => exists_domainResolvent D.form.toClosedForm (En n) (hEn n) α hα
  have hsubset : ∀ n, En n ≤ D.form.toClosedForm.killedCoreClosure W := fun n =>
    compact_supported_mem_coreClosure D.form V C hC (cv.sets n) W (cv.compact n)
      hW (cv.subset n) inter_subset_right
  have hmono : Monotone En := by
    intro i j hij u hu
    refine ⟨hu.1, ?_⟩
    filter_upwards [hu.2] with x hx hxj
    exact hx (fun h => hxj (cv.monotone hij h))
  have hGW : IsDomainResolvent D.form.toClosedForm
      (D.form.toClosedForm.killedCoreClosure W) α G := by
    rw [hclosure]
    exact hG
  have ht := domainResolvent_tendsto D.form.toClosedForm
    (D.form.toClosedForm.killedCoreClosure W) En hsubset
    (fun u hu ε hε => coreClosure_compactCover_dense _ W cv u hu ε hε) hmono
    (graphClosed_killedCoreClosure _ W) α hα G hGW Gn hGn (hfL.toLp f)
  have hassoc := fun n => compact_association hm hpos D (cv.sets n) (cv.compact n)
    α hα (Gn n) (hGn n) f hf hf0 hfL
  obtain ⟨hfinite, heq⟩ := association_of_limits
    (fun n => killedOcc D.law (cv.sets n) α f) (killedOcc D.law W α f)
    (fun n => Gn n (hfL.toLp f)) (G (hfL.toLp f))
    (fun n => (hassoc n).1) (fun n => (hassoc n).2) ht
    (fun x => killedOcc_compactCover_tendsto D.law D.markov W hW cv α f hf hf0 x)
  have hinter := killedOcc_inter_carrier_congr hm hpos D V hV C hC U hU α f hf
  constructor
  · filter_upwards [hfinite, hinter] with x hx he
    rwa [he] at hx
  · filter_upwards [heq, hinter] with x hx he
    rwa [he] at hx

end SubdiffusiveProcess.PartProcess
