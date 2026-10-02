import SubdiffusiveProcess.PartProcess.CompactKilling
import SubdiffusiveProcess.PartProcess.CompactCover
import SubdiffusiveProcess.PartProcess.GraphConvergence
import SubdiffusiveProcess.PartProcess.CoreLocalization
import SubdiffusiveProcess.PartProcess.ExhaustionLimits
import SubdiffusiveProcess.PartProcess.CarrierNoExit

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.PartProcess
open SubdiffusiveProcess.E7
variable {d : ℕ} {m : Measure (Fin d → ℝ)}

/-- Exhausting the regular carrier gives the original form resolvent. -/
theorem carrier_free_association (hm : IsLocallyFiniteMeasure m) (hpos : m.IsOpenPosMeasure)
    (D : Data d m) (V : Set (Fin d → ℝ)) (hV : IsOpen V)
    (C : Set (Lp ℝ 2 m)) (hC : DirichletForm.IsCoreOn D.form.toClosedForm V C)
    (α : ℝ) (hα : 0 < α)
    (G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m)
    (hG : DirichletForm.IsResolvent D.form.toClosedForm α G)
    (f : (Fin d → ℝ) → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfL : MemLp f 2 m) :
    killedOcc D.law V α f =ᵐ[m] potentialOcc D.law 0 α f := by
  classical
  obtain ⟨cv⟩ := exists_compactCover V hV
  let En := fun n => supportedDomain D.form.toClosedForm (cv.sets n)
  have hEn : ∀ n, GraphClosed D.form.toClosedForm (En n) :=
    fun n => graphClosed_supportedDomain _ _
  choose Gn hGn using fun n => exists_domainResolvent D.form.toClosedForm (En n) (hEn n) α hα
  have hdense : ∀ u ∈ D.form.domain, ∀ ε : ℝ, 0 < ε →
      ∃ n v, v ∈ En n ∧ D.form.energyNormSq (u - v) < ε := by
    intro u hu ε hε
    obtain ⟨v, hvC, he⟩ := hC.denseEnergy u hu ε hε
    obtain ⟨g, hg, hgK, hgV, hvg⟩ := (hC.memCoreOn v hvC).2
    obtain ⟨n, hn⟩ := cv.cofinal _ hgK hgV
    refine ⟨n, v, ⟨(hC.memCoreOn v hvC).1, ?_⟩, he⟩
    filter_upwards [hvg] with x hx hxA
    rw [hx]
    exact image_eq_zero_of_notMem_tsupport (fun h => hxA (hn h))
  have hmono : Monotone En := by
    intro i j hij u hu
    refine ⟨hu.1, ?_⟩
    filter_upwards [hu.2] with x hx hxj
    exact hx (fun h => hxj (cv.monotone hij h))
  have hdomain : GraphClosed D.form.toClosedForm D.form.domain :=
    ⟨le_rfl, fun _ _ _ hv _ => hv⟩
  have ht := domainResolvent_tendsto D.form.toClosedForm D.form.domain En
    (fun _ _ hu => hu.1) hdense hmono hdomain α hα G hG Gn hGn (hfL.toLp f)
  have hassoc := fun n => compact_association hm hpos D (cv.sets n) (cv.compact n)
    α hα (Gn n) (hGn n) f hf hf0 hfL
  obtain ⟨hfinite, heq⟩ := association_of_limits
    (fun n => killedOcc D.law (cv.sets n) α f) (killedOcc D.law V α f)
    (fun n => Gn n (hfL.toLp f)) (G (hfL.toLp f))
    (fun n => (hassoc n).1) (fun n => (hassoc n).2) ht
    (fun x => killedOcc_compactCover_tendsto D.law D.markov V hV cv α f hf hf0 x)
  obtain ⟨hfreefin, hfree⟩ := free_association hm hpos D α hα G hG f hf hf0 hfL
  filter_upwards [hfinite, heq, hfreefin, hfree] with x hx hxe hy hye
  exact (ENNReal.toReal_eq_toReal_iff' hx.ne hy.ne).1 (hxe.trans hye.symm)

/-- Conservativity and free association make the carrier boundary invisible almost everywhere. -/
theorem carrier_nonexit (hm : IsLocallyFiniteMeasure m) (hpos : m.IsOpenPosMeasure)
    (D : Data d m) (V : Set (Fin d → ℝ)) (hV : IsOpen V)
    (C : Set (Lp ℝ 2 m)) (hC : DirichletForm.IsCoreOn D.form.toClosedForm V C) :
    ∀ᵐ x ∂m, ∀ᵐ w ∂(D.law x),
      LifetimePath.exitTime V (LifetimePath.ofContinuousPath w) = ⊤ := by
  letI := hm
  obtain ⟨G, hG⟩ := exists_isResolvent D.form.toClosedForm (show (0 : ℝ) < 1 by norm_num)
  let f : ℕ → (Fin d → ℝ) → ℝ := fun n =>
    (Metric.closedBall 0 (n : ℝ)).indicator (fun _ => 1)
  have hf : ∀ n, Measurable (f n) := fun n =>
    measurable_const.indicator Metric.isClosed_closedBall.measurableSet
  have hf0 : ∀ n x, 0 ≤ f n x := fun n x => indicator_nonneg (fun _ _ => zero_le_one) x
  have hfL : ∀ n, MemLp (f n) 2 m := fun n => memLp_indicator_const 2
    Metric.isClosed_closedBall.measurableSet 1 (Or.inr (isCompact_closedBall _ _).measure_lt_top.ne)
  have hcover : ∀ z : Fin d → ℝ, ∃ n, 0 < f n z := by
    intro z
    obtain ⟨n, hn⟩ := exists_nat_gt (dist z 0)
    refine ⟨n, ?_⟩
    dsimp [f]
    rw [indicator_of_mem (show z ∈ Metric.closedBall 0 (n : ℝ) from hn.le)]
    exact zero_lt_one
  have hassoc : ∀ n, killedOcc D.law V 1 (f n) =ᵐ[m] potentialOcc D.law 0 1 (f n) :=
    fun n => carrier_free_association hm hpos D V hV C hC 1 (by norm_num) G hG
      (f n) (hf n) (hf0 n) (hfL n)
  have hfinite : ∀ n, ∀ᵐ x ∂m, potentialOcc D.law 0 1 (f n) x < ⊤ := fun n =>
    (free_association hm hpos D 1 (by norm_num) G hG (f n) (hf n) (hf0 n) (hfL n)).1
  filter_upwards [ae_all_iff.2 hassoc, ae_all_iff.2 hfinite] with x hx hfin
  exact nonexit_of_equal_occupations D.law D.markov V hV 1 f hf hcover x hfin hx

theorem killedOcc_inter_carrier_congr (hm : IsLocallyFiniteMeasure m)
    (hpos : m.IsOpenPosMeasure) (D : Data d m) (V : Set (Fin d → ℝ)) (hV : IsOpen V)
    (C : Set (Lp ℝ 2 m)) (hC : DirichletForm.IsCoreOn D.form.toClosedForm V C)
    (U : Set (Fin d → ℝ)) (hU : IsOpen U) (α : ℝ)
    (f : (Fin d → ℝ) → ℝ) (hf : Measurable f) :
    killedOcc D.law (U ∩ V) α f =ᵐ[m] killedOcc D.law U α f := by
  filter_upwards [carrier_nonexit hm hpos D V hV C hC] with x hx
  rw [killedOcc_continuousPath, killedOcc_continuousPath]
  apply lintegral_congr
  intro t
  congr 1
  rw [← lintegral_indicator
      (measurableSet_lt measurable_const (ContinuousPath.measurable_exitTime (U ∩ V) (hU.inter hV))),
    ← lintegral_indicator
      (measurableSet_lt measurable_const (ContinuousPath.measurable_exitTime U hU))]
  apply lintegral_congr_ae
  filter_upwards [hx] with w hw
  rw [LifetimePath.exitTime_ofContinuousPath] at hw
  have hall := (ContinuousPath.exitTime_eq_top_iff V w).1 hw
  have he : ContinuousPath.exitTime (U ∩ V) w = ContinuousPath.exitTime U w := by
    unfold ContinuousPath.exitTime
    congr 1
    ext s
    simp only [mem_setOf_eq, mem_inter_iff]
    apply exists_congr
    intro r
    simp only [hall r, and_true]
  simp only [Set.indicator, mem_setOf_eq, he]

end SubdiffusiveProcess.PartProcess
