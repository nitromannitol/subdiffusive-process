module

public import SubdiffusiveProcess.PartProcess.FreeResolvent
public import MarkovProcess.Trajectory.FeynmanKacRealResolvent
public import SubdiffusiveProcess.PartProcess.FeynmanKacBounded
public import SubdiffusiveProcess.PartProcess.FeynmanKacApproximation

@[expose] public section

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.PartProcess
variable {d : ℕ} {m : Measure (Fin d → ℝ)}

/-- The stochastic perturbation identity for an arbitrary supplied continuous realization. -/
theorem potentialOcc_duhamel (hm : IsLocallyFiniteMeasure m) (hpos : m.IsOpenPosMeasure)
    (D : Data d m) (q : (Fin d → ℝ) → ℝ) (hq : Measurable q)
    (hq0 : ∀ x, 0 ≤ q x) (B : ℝ) (hB : ∀ x, q x ≤ B)
    (α : ℝ) (hα : 0 < α)
    (G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m)
    (hG : _root_.SubdiffusiveProcess.DirichletForm.IsResolvent D.form.toClosedForm α G)
    (f : (Fin d → ℝ) → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfL : MemLp f 2 m)
    (hu : MemLp (fun x => q x * (potentialOcc D.law q α f x).toReal) 2 m) :
    (fun x => (potentialOcc D.law q α f x).toReal) =ᵐ[m]
      fun x => G (hfL.toLp f) x -
        G (hu.toLp (fun y => q y * (potentialOcc D.law q α f y).toReal)) x := by
  let := D.markov
  let b0 : ℝ := max B 0
  have hb0 : 0 ≤ b0 := le_max_right _ _
  have hqb : ∀ x, |q x| ≤ b0 := fun x => by
    rw [abs_of_nonneg (hq0 x)]
    exact (hB x).trans (le_max_left _ _)
  let Q : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m := multiplication q hq b0 hb0 hqb
  let fs : ℕ → (Fin d → ℝ) → ℝ := fun n x => min (f x) (n : ℝ)
  have hfs (n : ℕ) : Measurable (fs n) := hf.min measurable_const
  have hfs0 (n : ℕ) (x : Fin d → ℝ) : 0 ≤ fs n x :=
    le_min (hf0 x) (Nat.cast_nonneg n)
  have hfsL (n : ℕ) : MemLp (fs n) 2 m := by
    apply hfL.mono' (hfs n).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      simp only [Real.norm_eq_abs, abs_of_nonneg (hfs0 n x)]
      exact min_le_left (f x) (n : ℝ)
  let us : ℕ → (Fin d → ℝ) → ℝ :=
    fun n x => (potentialOcc D.law q α (fs n) x).toReal
  let u : (Fin d → ℝ) → ℝ := fun x => (potentialOcc D.law q α f x).toReal
  have husL (n : ℕ) : MemLp (us n) 2 m :=
    (potentialOcc_memLp hm hpos D q hq hq0 α hα (fs n) (hfs n) (hfs0 n) (hfsL n)).2
  have huL : MemLp u 2 m :=
    (potentialOcc_memLp hm hpos D q hq hq0 α hα f hf hf0 hfL).2
  let v : Lp ℝ 2 m := huL.toLp u
  let vs : ℕ → Lp ℝ 2 m := fun n => (husL n).toLp (us n)
  have hqus (n : ℕ) : ⇑(Q (vs n)) =ᵐ[m] fun x => q x * us n x := by
    filter_upwards [multiplyLp_coe q hq b0 hb0 hqb (vs n), (husL n).coeFn_toLp]
      with x hx hy
    exact hx.trans (congrArg (fun z => q x * z) hy)
  have hqu : ⇑(Q v) =ᵐ[m] fun x => q x * u x := by
    filter_upwards [multiplyLp_coe q hq b0 hb0 hqb v, huL.coeFn_toLp] with x hx hy
    exact hx.trans (congrArg (fun z => q x * z) hy)
  have hqusL (n : ℕ) : MemLp (fun x => q x * us n x) 2 m :=
    (memLp_congr_ae (hqus n)).1 (Lp.memLp (Q (vs n)))
  have hqs_toLp (n : ℕ) : (hqusL n).toLp (fun x => q x * us n x) = Q (vs n) := by
    apply Lp.ext
    exact (hqusL n).coeFn_toLp.trans (hqus n).symm
  have heq (n : ℕ) : vs n = G ((hfsL n).toLp (fs n)) - G (Q (vs n)) := by
    have ha := potentialOcc_duhamel_bounded hm hpos D q hq hq0 B hB α hα G hG
      (fs n) (hfs n) (hfs0 n) (hfsL n) (n : ℝ)
      (fun x => by rw [abs_of_nonneg (hfs0 n x)]; exact min_le_right _ _) (hqusL n)
    rw [hqs_toLp n] at ha
    apply Lp.ext
    exact (husL n).coeFn_toLp.trans
      (ha.trans (Lp.coeFn_sub _ _).symm)
  obtain ⟨hflim, hulim⟩ := potentialOcc_truncation_tendsto hm hpos D hq hq0 hα hf hf0
    hfL hfsL huL husL
  have hv : v = G (hfL.toLp f) - G (Q v) := by
    exact tendsto_nhds_unique hulim
      (((G.continuous.tendsto _).comp hflim).sub
        ((G.continuous.tendsto _).comp ((Q.continuous.tendsto _).comp hulim))
        |>.congr fun n => (heq n).symm)
  have hq_toLp : hu.toLp (fun x => q x * u x) = Q v := by
    apply Lp.ext
    exact hu.coeFn_toLp.trans hqu.symm
  rw [hq_toLp]
  have hav : ⇑v =ᵐ[m] fun x => G (hfL.toLp f) x - G (Q v) x := by
    exact (congrArg (fun z : Lp ℝ 2 m => (z : (Fin d → ℝ) → ℝ)) hv).eventuallyEq.trans
      (Lp.coeFn_sub _ _)
  exact huL.coeFn_toLp.symm.trans hav

/-- Bounded-potential occupation solves the perturbed form equation. -/
theorem potentialOcc_association (hm : IsLocallyFiniteMeasure m) (hpos : m.IsOpenPosMeasure)
    (D : Data d m) (q : (Fin d → ℝ) → ℝ) (hq : Measurable q)
    (hq0 : ∀ x, 0 ≤ q x) (B : ℝ) (hB : ∀ x, q x ≤ B)
    (F : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m) (hFdom : F.domain = D.form.domain)
    (hFform : ∀ u v, F.form u v =
      D.form.form u v + ∫ x, q x * u x * v x ∂m)
    (α : ℝ) (hα : 0 < α)
    (G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (hG : _root_.SubdiffusiveProcess.DirichletForm.IsResolvent F α G)
    (f : (Fin d → ℝ) → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfL : MemLp f 2 m) :
    (∀ᵐ x ∂m, potentialOcc D.law q α f x < ⊤) ∧
    (fun x => (potentialOcc D.law q α f x).toReal) =ᵐ[m] ⇑(G (hfL.toLp f)) := by
  let := D.markov
  obtain ⟨hfin, huL⟩ := potentialOcc_memLp hm hpos D q hq hq0 α hα f hf hf0 hfL
  refine ⟨hfin, ?_⟩
  let u : (Fin d → ℝ) → ℝ := fun x => (potentialOcc D.law q α f x).toReal
  let v : Lp ℝ 2 m := huL.toLp u
  let b0 : ℝ := max B 0
  have hb0 : 0 ≤ b0 := le_max_right _ _
  have hqb : ∀ x, |q x| ≤ b0 := fun x => by
    rw [abs_of_nonneg (hq0 x)]
    exact (hB x).trans (le_max_left _ _)
  let Q : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m := multiplication q hq b0 hb0 hqb
  have hqv : ⇑(Q v) =ᵐ[m] fun x => q x * u x := by
    filter_upwards [multiplyLp_coe q hq b0 hb0 hqb v, huL.coeFn_toLp] with x hx hy
    exact hx.trans (congrArg (fun z => q x * z) hy)
  have hquL : MemLp (fun x => q x * u x) 2 m := (memLp_congr_ae hqv).1 (Lp.memLp (Q v))
  have hq_toLp : hquL.toLp (fun x => q x * u x) = Q v := by
    apply Lp.ext
    exact hquL.coeFn_toLp.trans hqv.symm
  obtain ⟨R, hR⟩ := SubdiffusiveProcess.E7.exists_isResolvent D.form.toClosedForm hα
  have hd := potentialOcc_duhamel hm hpos D q hq hq0 B hB α hα R hR
    f hf hf0 hfL hquL
  rw [hq_toLp] at hd
  have hvR : v = R (hfL.toLp f - Q v) := by
    rw [map_sub]
    apply Lp.ext
    exact huL.coeFn_toLp.trans (hd.trans (Lp.coeFn_sub _ _).symm)
  have hvdom : v ∈ F.domain := by
    rw [hFdom, hvR]
    exact hR.mem_domain _
  have hveq (w : Lp ℝ 2 m) (hw : w ∈ F.domain) :
      α * inner ℝ v w + F.form v w = inner ℝ (hfL.toLp f) w := by
    have hwe : w ∈ D.form.domain := by rwa [hFdom] at hw
    have hre := hR.eq (hfL.toLp f - Q v) hwe
    rw [← hvR, inner_sub_left] at hre
    rw [hFform, ← inner_multiplication q hq b0 hb0 hqb v w]
    change α * inner ℝ v w + (D.form.form v w + inner ℝ (Q v) w) = _
    linarith only [hre]
  have hzdom : v - G (hfL.toLp f) ∈ F.domain :=
    F.domain.sub_mem hvdom (hG.mem_domain _)
  have hz : α * inner ℝ (v - G (hfL.toLp f)) (v - G (hfL.toLp f)) +
      F.form (v - G (hfL.toLp f)) (v - G (hfL.toLp f)) = 0 := by
    rw [inner_sub_left, F.form_sub_left hvdom (hG.mem_domain _) hzdom]
    have hv := hveq _ hzdom
    have hg := hG.eq (hfL.toLp f) hzdom
    linarith only [hv, hg]
  rw [real_inner_self_eq_norm_sq] at hz
  have he := F.form_nonneg _ hzdom
  have hs : ‖v - G (hfL.toLp f)‖ ^ 2 = 0 := by
    exact le_antisymm (le_of_mul_le_mul_left
      (show α * ‖v - G (hfL.toLp f)‖ ^ 2 ≤ α * 0 by
        rw [mul_zero]
        linarith only [hz, he]) hα) (sq_nonneg _)
  have hn : ‖v - G (hfL.toLp f)‖ = 0 := (sq_eq_zero_iff).1 hs
  have hvG : v = G (hfL.toLp f) := sub_eq_zero.1 (norm_eq_zero.1 hn)
  exact huL.coeFn_toLp.symm.trans (by
    change (v : (Fin d → ℝ) → ℝ) =ᵐ[m] ⇑(G (hfL.toLp f))
    rw [hvG])

end SubdiffusiveProcess.PartProcess
