module

public import SubdiffusiveProcess.Paper.cor_14_form_variation
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Sobolev.PotentialPerturbation
public import SubdiffusiveProcess.Sobolev.PotentialResponses
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Lane2.LimitForm
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.SimpleFuncDense
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal
open scoped Topology

namespace Paper

lemma aux_cor_14_form_sharp_energy_simple_cross
    {X : Type*} [MeasurableSpace X]
    (s : SignedMeasure X) (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (B : Set X) (hB : MeasurableSet B) (f : SimpleFunc X ℝ)
    (hcs : ∀ A : Set X, MeasurableSet A →
      |s A| ≤ Real.sqrt (μ A).toReal * Real.sqrt (ν A).toReal) :
    |DirichletForm.signedIntegralOn s B f| ≤
      Real.sqrt (μ B).toReal *
        Real.sqrt (∫ x in B, f x ^ 2 ∂ν) := by
  classical
  have hfp : Integrable (f : X → ℝ) (s.toJordanDecomposition.posPart.restrict B) :=
    SimpleFunc.integrable_of_isFiniteMeasure f
  have hfn : Integrable (f : X → ℝ) (s.toJordanDecomposition.negPart.restrict B) :=
    SimpleFunc.integrable_of_isFiniteMeasure f
  simp only [DirichletForm.signedIntegralOn]
  rw [f.integral_eq_sum hfp, f.integral_eq_sum hfn]
  have hsum :
      (∑ x ∈ f.range, (s.toJordanDecomposition.posPart.restrict B).real (⇑f ⁻¹' {x}) • x -
        ∑ x ∈ f.range, (s.toJordanDecomposition.negPart.restrict B).real (⇑f ⁻¹' {x}) • x) =
        ∑ x ∈ f.range, s (B ∩ (⇑f ⁻¹' {x})) * x := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    have hA : MeasurableSet (B ∩ (⇑f ⁻¹' {x})) :=
      hB.inter (f.measurableSet_preimage {x})
    have hsx : s (B ∩ (⇑f ⁻¹' {x})) =
        (s.toJordanDecomposition.posPart (B ∩ (⇑f ⁻¹' {x}))).toReal -
          (s.toJordanDecomposition.negPart (B ∩ (⇑f ⁻¹' {x}))).toReal := by
      calc
        s (B ∩ (⇑f ⁻¹' {x})) =
            s.toJordanDecomposition.toSignedMeasure (B ∩ (⇑f ⁻¹' {x})) := by
          rw [SignedMeasure.toSignedMeasure_toJordanDecomposition]
        _ = s.toJordanDecomposition.posPart.toSignedMeasure
              (B ∩ (⇑f ⁻¹' {x})) -
            s.toJordanDecomposition.negPart.toSignedMeasure
              (B ∩ (⇑f ⁻¹' {x})) := rfl
        _ = (s.toJordanDecomposition.posPart (B ∩ (⇑f ⁻¹' {x}))).toReal -
              (s.toJordanDecomposition.negPart (B ∩ (⇑f ⁻¹' {x}))).toReal := by
          rw [Measure.toSignedMeasure_apply_measurable hA,
            Measure.toSignedMeasure_apply_measurable hA]
          rfl
    rw [Measure.real, Measure.real,
      Measure.restrict_apply (f.measurableSet_preimage {x}),
      Measure.restrict_apply (f.measurableSet_preimage {x})]
    calc
      (s.toJordanDecomposition.posPart.real (⇑f ⁻¹' {x} ∩ B)) • x -
          (s.toJordanDecomposition.negPart.real (⇑f ⁻¹' {x} ∩ B)) • x =
          ((s.toJordanDecomposition.posPart (B ∩ (⇑f ⁻¹' {x}))).toReal -
            (s.toJordanDecomposition.negPart (B ∩ (⇑f ⁻¹' {x}))).toReal) * x := by
              rw [Measure.real, Measure.real, Set.inter_comm (⇑f ⁻¹' {x}) B]
              · simp only [smul_eq_mul]
                ring
      _ = s (B ∩ (⇑f ⁻¹' {x})) * x := by rw [← hsx]
  rw [hsum]
  have hsumμ :
      (∑ x ∈ f.range, (μ (B ∩ (⇑f ⁻¹' {x}))).toReal) = (μ B).toReal := by
    have h := MeasureTheory.sum_measureReal_preimage_singleton (μ := μ.restrict B)
      f.range (f := (⇑f : X → ℝ)) (fun x hx => f.measurableSet_preimage {x})
    simpa [Measure.real, Measure.restrict_apply, f.measurableSet_preimage,
      Set.inter_comm] using h
  have hsumν :
      (∑ x ∈ f.range, (ν (B ∩ (⇑f ⁻¹' {x}))).toReal) = (ν B).toReal := by
    have h := MeasureTheory.sum_measureReal_preimage_singleton (μ := ν.restrict B)
      f.range (f := (⇑f : X → ℝ)) (fun x hx => f.measurableSet_preimage {x})
    simpa [Measure.real, Measure.restrict_apply, f.measurableSet_preimage,
      Set.inter_comm] using h
  let F : SimpleFunc X ℝ := f.map (fun x => x ^ 2)
  have hFint : Integrable (F : X → ℝ) (ν.restrict B) :=
    SimpleFunc.integrable_of_isFiniteMeasure F
  have hsq :
      (∫ x in B, f x ^ 2 ∂ν) =
        ∑ x ∈ f.range, (ν (B ∩ (⇑f ⁻¹' {x}))).toReal * x ^ 2 := by
    change ∫ x, F x ∂(ν.restrict B) = _
    have hFpos : 0 ≤ᶠ[ae (ν.restrict B)] (F : X → ℝ) :=
      Filter.Eventually.of_forall (fun x => by
        change 0 ≤ (f x) ^ 2
        exact sq_nonneg _)
    rw [← F.integral_eq_integral hFint, F.integral_eq_lintegral hFint hFpos]
    have hlin :
        (∫⁻ x, ENNReal.ofReal (F x) ∂(ν.restrict B)) =
          ∑ x ∈ f.range, ENNReal.ofReal (x ^ 2) *
            (ν.restrict B) (⇑f ⁻¹' {x}) := by
      change (∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂(ν.restrict B)) = _
      let H : SimpleFunc X ℝ≥0∞ :=
        f.map (fun x : ℝ => ENNReal.ofReal (x ^ 2))
      calc
        (∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂(ν.restrict B)) =
            ∫⁻ x, H x ∂(ν.restrict B) := by
              congr 1
        _ = H.lintegral (ν.restrict B) := H.lintegral_eq_lintegral _
        _ = ∑ x ∈ f.range, ENNReal.ofReal (x ^ 2) *
              (ν.restrict B) (⇑f ⁻¹' {x}) := by
              exact SimpleFunc.map_lintegral _ _
    rw [hlin, ENNReal.toReal_sum]
    · simp [Measure.restrict_apply, f.measurableSet_preimage, Set.inter_comm,
        ENNReal.toReal_ofReal, sq_nonneg, mul_comm]
    · intro x hx
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (measure_lt_top (ν.restrict B) _).ne
  have hcs' : ∀ x ∈ f.range,
      |s (B ∩ (⇑f ⁻¹' {x}))| ≤
        Real.sqrt (μ (B ∩ (⇑f ⁻¹' {x}))).toReal *
          Real.sqrt (ν (B ∩ (⇑f ⁻¹' {x}))).toReal := by
    intro x hx
    exact hcs _ (hB.inter (f.measurableSet_preimage {x}))
  calc
    |∑ x ∈ f.range, s (B ∩ (⇑f ⁻¹' {x})) * x| ≤
        ∑ x ∈ f.range, |s (B ∩ (⇑f ⁻¹' {x})) * x| := by
          exact Finset.abs_sum_le_sum_abs
            (fun x : ℝ => s (B ∩ (⇑f ⁻¹' {x})) * x) f.range
    _ = ∑ x ∈ f.range, |x| * |s (B ∩ (⇑f ⁻¹' {x}))| := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [abs_mul, mul_comm]
    _ ≤ ∑ x ∈ f.range, |x| *
          (Real.sqrt (μ (B ∩ (⇑f ⁻¹' {x}))).toReal *
            Real.sqrt (ν (B ∩ (⇑f ⁻¹' {x}))).toReal) := by
          apply Finset.sum_le_sum
          intro x hx
          exact mul_le_mul_of_nonneg_left (hcs' x hx) (abs_nonneg _)
    _ = ∑ x ∈ f.range,
          Real.sqrt (μ (B ∩ (⇑f ⁻¹' {x}))).toReal *
            Real.sqrt (x ^ 2 * (ν (B ∩ (⇑f ⁻¹' {x}))).toReal) := by
          apply Finset.sum_congr rfl
          intro x hx
          have hμ0 : 0 ≤ (μ (B ∩ (⇑f ⁻¹' {x}))).toReal := ENNReal.toReal_nonneg
          have hν0 : 0 ≤ (ν (B ∩ (⇑f ⁻¹' {x}))).toReal := ENNReal.toReal_nonneg
          rw [Real.sqrt_mul (sq_nonneg x)]
          rw [Real.sqrt_sq_eq_abs]
          ring
    _ ≤ Real.sqrt (∑ x ∈ f.range,
          (μ (B ∩ (⇑f ⁻¹' {x}))).toReal) *
          Real.sqrt (∑ x ∈ f.range,
            x ^ 2 * (ν (B ∩ (⇑f ⁻¹' {x}))).toReal) := by
          apply Real.sum_sqrt_mul_sqrt_le
          · intro x
            exact ENNReal.toReal_nonneg
          · intro x
            positivity
    _ = Real.sqrt (μ B).toReal * Real.sqrt (∫ x in B, f x ^ 2 ∂ν) := by
          rw [hsumμ, hsq]
          congr 1
          simp [mul_comm]

lemma aux_cor_14_form_sharp_energy_weighted_cross
    {X : Type*} [MeasurableSpace X]
    (s : SignedMeasure X) (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (B : Set X) (hB : MeasurableSet B) (f : X → ℝ) (hf : Measurable f)
    (K : ℝ) (hK : 0 ≤ K) (hfb : ∀ x, |f x| ≤ K)
    (hcs : ∀ A : Set X, MeasurableSet A →
      |s A| ≤ Real.sqrt (μ A).toReal * Real.sqrt (ν A).toReal) :
    |DirichletForm.signedIntegralOn s B f| ≤
      Real.sqrt (μ B).toReal *
        Real.sqrt (∫ x in B, f x ^ 2 ∂ν) := by
  classical
  let R : Set ℝ := Set.range f ∪ {0}
  let h0 : (0 : ℝ) ∈ R := by simp [R]
  let φ : ℕ → SimpleFunc X ℝ :=
    fun n => SimpleFunc.approxOn f hf R 0 h0 n
  have hφmem : ∀ n x, φ n x ∈ R := by
    intro n x
    exact SimpleFunc.approxOn_mem hf h0 n x
  have hφb : ∀ n x, |φ n x| ≤ K := by
    intro n x
    rcases hφmem n x with hx | hx
    · rcases hx with ⟨y, hy⟩
      rw [← hy]
      exact hfb y
    · have hx0 : φ n x = 0 := by simpa using hx
      simp [hx0, hK]
  have hφlim : ∀ x, Tendsto (fun n => φ n x) atTop (𝓝 (f x)) := by
    intro x
    apply SimpleFunc.tendsto_approxOn hf h0
    exact subset_closure (Set.mem_union_left _ (Set.mem_range_self x))
  have hposlim :
      Tendsto (fun n => ∫ x in B, φ n x ∂s.toJordanDecomposition.posPart)
        atTop (𝓝 (∫ x in B, f x ∂s.toJordanDecomposition.posPart)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : X => K)
    · intro n
      exact (SimpleFunc.measurable (φ n)).aestronglyMeasurable
    · exact integrable_const K
    · intro n
      filter_upwards [] with x
      simpa [Real.norm_eq_abs] using hφb n x
    · filter_upwards [] with x
      exact hφlim x
  have hneglim :
      Tendsto (fun n => ∫ x in B, φ n x ∂s.toJordanDecomposition.negPart)
        atTop (𝓝 (∫ x in B, f x ∂s.toJordanDecomposition.negPart)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : X => K)
    · intro n
      exact (SimpleFunc.measurable (φ n)).aestronglyMeasurable
    · exact integrable_const K
    · intro n
      filter_upwards [] with x
      simpa [Real.norm_eq_abs] using hφb n x
    · filter_upwards [] with x
      exact hφlim x
  have hsignedlim :
      Tendsto (fun n => DirichletForm.signedIntegralOn s B (φ n)) atTop
        (𝓝 (DirichletForm.signedIntegralOn s B f)) := by
    simpa only [DirichletForm.signedIntegralOn] using hposlim.sub hneglim
  have hsq_lim :
      Tendsto (fun n => ∫ x in B, (φ n x) ^ 2 ∂ν) atTop
        (𝓝 (∫ x in B, f x ^ 2 ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : X => K ^ 2)
    · intro n
      have hm : Measurable (fun x => (φ n x) ^ 2) := by fun_prop
      exact hm.aestronglyMeasurable
    · exact integrable_const (K ^ 2)
    · intro n
      filter_upwards [] with x
      simp only [Real.norm_eq_abs, abs_pow]
      nlinarith [abs_nonneg (φ n x), hφb n x]
    · filter_upwards [] with x
      exact (hφlim x).pow 2
  have hrightlim :
      Tendsto (fun n => Real.sqrt (μ B).toReal *
          Real.sqrt (∫ x in B, (φ n x) ^ 2 ∂ν)) atTop
        (𝓝 (Real.sqrt (μ B).toReal *
          Real.sqrt (∫ x in B, f x ^ 2 ∂ν))) := by
    exact (hsq_lim.sqrt).const_mul _
  have hineq : ∀ n,
      |DirichletForm.signedIntegralOn s B (φ n)| ≤
        Real.sqrt (μ B).toReal *
          Real.sqrt (∫ x in B, (φ n x) ^ 2 ∂ν) := by
    intro n
    exact aux_cor_14_form_sharp_energy_simple_cross s μ ν B hB (φ n) hcs
  exact le_of_tendsto_of_tendsto hsignedlim.abs hrightlim
    (Filter.Eventually.of_forall hineq)

lemma aux_cor_14_form_sharp_energy_exp_bound
    {S t : ℝ} (hS : 0 ≤ S) (ht : |t| ≤ S) :
    |Real.exp t - 1| ≤
      (Real.exp (S / 2) - Real.exp (-S / 2)) * Real.exp (t / 2) := by
  have ht_bounds : -S ≤ t ∧ t ≤ S := (abs_le.mp ht)
  have hC : 0 ≤ Real.exp (S / 2) - Real.exp (-S / 2) := by
    apply sub_nonneg.mpr
    apply Real.exp_le_exp.mpr
    linarith
  by_cases htn : 0 ≤ t
  · have hdiff :
        Real.exp (t / 2) - Real.exp (-t / 2) ≤
          Real.exp (S / 2) - Real.exp (-S / 2) := by
      apply sub_le_sub
      · apply Real.exp_le_exp.mpr
        linarith
      · apply Real.exp_le_exp.mpr
        linarith
    have he₁ : Real.exp (t / 2) * Real.exp (t / 2) = Real.exp t := by
      rw [← Real.exp_add]
      congr 1
      ring
    have he₂ : Real.exp (t / 2) * Real.exp (-t / 2) = 1 := by
      rw [← Real.exp_add]
      rw [show t / 2 + -t / 2 = 0 by ring, Real.exp_zero]
    rw [abs_of_nonneg]
    · calc
        Real.exp t - 1 =
            Real.exp (t / 2) *
              (Real.exp (t / 2) - Real.exp (-t / 2)) := by
                rw [← he₁, ← he₂]
                ring
        _ ≤ Real.exp (t / 2) *
              (Real.exp (S / 2) - Real.exp (-S / 2)) :=
                mul_le_mul_of_nonneg_left hdiff (Real.exp_nonneg _)
        _ = (Real.exp (S / 2) - Real.exp (-S / 2)) * Real.exp (t / 2) :=
              by ring
    · apply sub_nonneg.mpr
      simpa using Real.exp_le_exp.mpr htn
  · have ht' : t ≤ 0 := le_of_not_ge htn
    have hdiff :
        Real.exp (-t / 2) - Real.exp (t / 2) ≤
          Real.exp (S / 2) - Real.exp (-S / 2) := by
      apply sub_le_sub
      · apply Real.exp_le_exp.mpr
        linarith
      · apply Real.exp_le_exp.mpr
        linarith
    have he₁ : Real.exp (t / 2) * Real.exp (-t / 2) = 1 := by
      rw [← Real.exp_add]
      rw [show t / 2 + -t / 2 = 0 by ring, Real.exp_zero]
    have he₂ : Real.exp (t / 2) * Real.exp (t / 2) = Real.exp t := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [abs_of_nonpos]
    · calc
        -(Real.exp t - 1) = 1 - Real.exp t := by ring
        _ =
            Real.exp (t / 2) *
              (Real.exp (-t / 2) - Real.exp (t / 2)) := by
                rw [← he₁, ← he₂]
                ring
        _ ≤ Real.exp (t / 2) *
              (Real.exp (S / 2) - Real.exp (-S / 2)) :=
                mul_le_mul_of_nonneg_left hdiff (Real.exp_nonneg _)
        _ = (Real.exp (S / 2) - Real.exp (-S / 2)) * Real.exp (t / 2) :=
              by ring
    · apply sub_nonpos.mpr
      simpa using Real.exp_le_exp.mpr ht'

lemma aux_cor_14_form_sharp_energy_quadratic
    {x k : ℝ} (hx : 0 ≤ x) (hk : 0 ≤ k) (h : x ^ 2 ≤ k * x) : x ≤ k := by
  nlinarith




theorem cor_14_form_sharp_energy :
    (∀ (d : ℕ) (Q : Opens (SpatialCoordinates d))
        (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      let q := centeredCube z r hr;
      (closure (q : Set (SpatialCoordinates d)) ⊆ (Q : Set (SpatialCoordinates d))) →
      (∀ (E Eg : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
          (Gamma : DirichletForm.EnergyMeasure E) (Gammag : DirichletForm.EnergyMeasure Eg),
        Eg.domain = E.domain →
        ∀ (V0 : Submodule ℝ (DomainL2 Q)),
        DirichletForm.IsKilledDomain E (q : Set (SpatialCoordinates d)) V0 →
        ∀ (g : SpatialCoordinates d → ℝ), Measurable g →
        ∀ (B : Set (SpatialCoordinates d)), MeasurableSet B →
        B ⊆ (q : Set (SpatialCoordinates d)) → (∀ x, x ∉ B → g x = 0) →
        ∀ (S : ℝ), IsLUB (Set.range (fun x => |g x|)) S →
        BddAbove (Set.range (fun x => |g x|)) →
        (∀ v ∈ E.domain, ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
          Gammag.measure v A =
            ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(Gamma.measure v)) →
        (∀ (u ug : DomainL2 Q), u ∈ E.domain → ug ∈ Eg.domain →
          ug - u ∈ V0 →
          (∀ v ∈ V0,
            DirichletForm.signedIntegralOn (Gammag.cross (ug - u) v)
                (q : Set (SpatialCoordinates d)) (fun _ => (1 : ℝ)) =
              -DirichletForm.signedIntegralOn (Gamma.cross u v) B
                (fun x => Real.exp (g x) - 1)) →
          Real.sqrt (Gammag.measure (ug - u) q).toReal ≤
              (Real.exp (S / 2) - Real.exp (-S / 2)) *
                Real.sqrt (Gamma.measure u B).toReal ∧
            Real.sqrt (Gammag.measure ug B).toReal ≤
              2 * Real.exp (S / 2) * Real.sqrt (Gamma.measure u B).toReal))) := by
  intro d Q z r hr
  dsimp only
  intro hQ E Eg Gamma Gammag hdom V0 hkill g hg B hB hBq hgzero S hS hBdd hmeasure
  intro u ug hu hug hdiff heq
  let q : Set (SpatialCoordinates d) := (centeredCube z r hr : Set (SpatialCoordinates d))
  have hqopen : IsOpen q := by
    exact (centeredCube z r hr).2
  have hq : MeasurableSet q := hqopen.measurableSet
  have huEg : u ∈ Eg.domain := by
    rw [hdom]
    exact hu
  have hwE : ug - u ∈ E.domain := by
    exact E.domain.sub_mem (hdom ▸ hug) hu
  have hwEg : ug - u ∈ Eg.domain := by
    rw [hdom]
    exact hwE
  have hwV : ug - u ∈ V0 := hdiff
  have hgabs : ∀ x, |g x| ≤ S := by
    intro x
    exact hS.1 ⟨x, rfl⟩
  have hS0 : 0 ≤ S := by
    have hx0 : SpatialCoordinates d := fun _ => 0
    exact le_trans (abs_nonneg (g hx0)) (hgabs hx0)
  have hC0 : 0 ≤ Real.exp (S / 2) - Real.exp (-S / 2) := by
    apply sub_nonneg.mpr
    exact Real.exp_le_exp.mpr (by linarith)
  let K : ℝ := Real.exp S + 1
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hf : Measurable (fun x => Real.exp (g x) - 1) :=
    hg.exp.sub measurable_const
  have hfb : ∀ x, |Real.exp (g x) - 1| ≤ K := by
    intro x
    have hexp : Real.exp (g x) ≤ Real.exp S :=
      Real.exp_le_exp.mpr (le_trans (abs_le.mp (hgabs x)).2 le_rfl)
    calc
      |Real.exp (g x) - 1| ≤ |Real.exp (g x) - 0| + |0 - 1| :=
        abs_sub_le _ _ _
      _ = Real.exp (g x) + 1 := by
        rw [sub_zero, abs_of_nonneg (Real.exp_nonneg _), zero_sub, abs_neg]
        norm_num
      _ ≤ K := by
        dsimp [K]
        nlinarith
  letI : IsFiniteMeasure (Gamma.measure u) :=
    ⟨Gamma.measure_univ_lt_top u hu⟩
  letI : IsFiniteMeasure (Gamma.measure (ug - u)) :=
    ⟨Gamma.measure_univ_lt_top (ug - u) hwE⟩
  letI : IsFiniteMeasure (Gammag.measure (ug - u)) :=
    ⟨Gammag.measure_univ_lt_top (ug - u) hwEg⟩
  letI : IsFiniteMeasure (Gammag.measure u) :=
    ⟨Gammag.measure_univ_lt_top u huEg⟩
  have hweighted :=
    aux_cor_14_form_sharp_energy_weighted_cross
      (Gamma.cross u (ug - u)) (Gamma.measure u) (Gamma.measure (ug - u)) B hB
      (fun x => Real.exp (g x) - 1) hf K hK hfb
      (fun A hA => Gamma.abs_cross_le u hu (ug - u) hwE A hA)
  have hpoint : ∀ x,
      |Real.exp (g x) - 1| ≤
        (Real.exp (S / 2) - Real.exp (-S / 2)) * Real.exp (g x / 2) := by
    intro x
    exact aux_cor_14_form_sharp_energy_exp_bound hS0 (hgabs x)
  have hpoint_sq : ∀ x,
      (Real.exp (g x) - 1) ^ 2 ≤
        (Real.exp (S / 2) - Real.exp (-S / 2)) ^ 2 * Real.exp (g x) := by
    intro x
    have hsqrt :=
      (sq_le_sq₀ (abs_nonneg (Real.exp (g x) - 1))
        (mul_nonneg hC0 (Real.exp_nonneg _))).2 (hpoint x)
    have hexp_half : Real.exp (g x / 2) ^ 2 = Real.exp (g x) := by
      calc
        Real.exp (g x / 2) ^ 2 =
            Real.exp (g x / 2) * Real.exp (g x / 2) := by ring
        _ = Real.exp (g x / 2 + g x / 2) := by rw [Real.exp_add]
        _ = Real.exp (g x) := by congr 1 <;> ring
    rw [mul_pow, hexp_half] at hsqrt
    simpa [abs_sq] using hsqrt
  have hexp_w : Integrable (fun x => Real.exp (g x)) (Gamma.measure (ug - u)) := by
    apply (integrable_const (Real.exp S)).mono hg.exp.aestronglyMeasurable
    filter_upwards [] with x
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _),
      abs_of_nonneg (Real.exp_nonneg S)] using
      Real.exp_le_exp.mpr (le_trans (abs_le.mp (hgabs x)).2 le_rfl)
  have hmeasure_real_w_q :
      (Gammag.measure (ug - u) q).toReal =
        ∫ x in q, Real.exp (g x) ∂Gamma.measure (ug - u) := by
    rw [hmeasure (ug - u) hwE q hq]
    symm
    exact integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun x => Real.exp_nonneg _))
      hg.exp.aestronglyMeasurable
  have hI2 :
      (∫ x in B, (Real.exp (g x) - 1) ^ 2 ∂Gamma.measure (ug - u)) ≤
        (Real.exp (S / 2) - Real.exp (-S / 2)) ^ 2 *
          (Gammag.measure (ug - u) q).toReal := by
    have hf2 : Integrable (fun x => (Real.exp (g x) - 1) ^ 2)
        ((Gamma.measure (ug - u)).restrict B) := by
      apply (integrable_const (K ^ 2)).mono
        (hf.pow_const 2).aestronglyMeasurable
      filter_upwards [] with x
      simp only [Real.norm_eq_abs, abs_pow]
      rw [abs_of_nonneg hK]
      nlinarith [abs_nonneg (Real.exp (g x) - 1), hfb x]
    have hCexp : Integrable
        (fun x => (Real.exp (S / 2) - Real.exp (-S / 2)) ^ 2 * Real.exp (g x))
        ((Gamma.measure (ug - u)).restrict B) :=
      (hexp_w.restrict).const_mul _
    have hfirst := integral_mono_ae hf2 hCexp
      (Filter.Eventually.of_forall (fun x => hpoint_sq x))
    have hsecond :
        (∫ x in B, (Real.exp (S / 2) - Real.exp (-S / 2)) ^ 2 *
          Real.exp (g x) ∂Gamma.measure (ug - u)) ≤
          ∫ x in q, (Real.exp (S / 2) - Real.exp (-S / 2)) ^ 2 *
            Real.exp (g x) ∂Gamma.measure (ug - u) := by
      apply integral_mono_measure
        (μ := (Gamma.measure (ug - u)).restrict B)
        (ν := (Gamma.measure (ug - u)).restrict q)
        (f := fun x =>
          (Real.exp (S / 2) - Real.exp (-S / 2)) ^ 2 * Real.exp (g x))
      · exact Measure.restrict_mono hBq (le_refl (Gamma.measure (ug - u)))
      · exact Filter.Eventually.of_forall (fun x =>
          mul_nonneg
            (sq_nonneg (Real.exp (S / 2) - Real.exp (-S / 2)))
            (Real.exp_nonneg _))
      · exact (hexp_w.restrict (s := q)).const_mul
          ((Real.exp (S / 2) - Real.exp (-S / 2)) ^ 2)
    calc
      (∫ x in B, (Real.exp (g x) - 1) ^ 2 ∂Gamma.measure (ug - u)) ≤
          ∫ x in B, (Real.exp (S / 2) - Real.exp (-S / 2)) ^ 2 *
            Real.exp (g x) ∂Gamma.measure (ug - u) := hfirst
      _ ≤ ∫ x in q, (Real.exp (S / 2) - Real.exp (-S / 2)) ^ 2 *
            Real.exp (g x) ∂Gamma.measure (ug - u) := hsecond
      _ = (Real.exp (S / 2) - Real.exp (-S / 2)) ^ 2 *
            (Gammag.measure (ug - u) q).toReal := by
              rw [integral_const_mul, hmeasure_real_w_q]
  have hsqrtI2 :
      Real.sqrt (∫ x in B, (Real.exp (g x) - 1) ^ 2 ∂Gamma.measure (ug - u)) ≤
        (Real.exp (S / 2) - Real.exp (-S / 2)) *
          Real.sqrt (Gammag.measure (ug - u) q).toReal := by
    calc
      Real.sqrt (∫ x in B, (Real.exp (g x) - 1) ^ 2 ∂Gamma.measure (ug - u)) ≤
          Real.sqrt ((Real.exp (S / 2) - Real.exp (-S / 2)) ^ 2 *
            (Gammag.measure (ug - u) q).toReal) := Real.sqrt_le_sqrt hI2
      _ = (Real.exp (S / 2) - Real.exp (-S / 2)) *
          Real.sqrt (Gammag.measure (ug - u) q).toReal := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
          abs_of_nonneg hC0]
  have hcross_bound :
      |DirichletForm.signedIntegralOn (Gamma.cross u (ug - u)) B
          (fun x => Real.exp (g x) - 1)| ≤
        (Real.exp (S / 2) - Real.exp (-S / 2)) *
          Real.sqrt (Gamma.measure u B).toReal *
            Real.sqrt (Gammag.measure (ug - u) q).toReal := by
    calc
      |DirichletForm.signedIntegralOn (Gamma.cross u (ug - u)) B
          (fun x => Real.exp (g x) - 1)| ≤
          Real.sqrt (Gamma.measure u B).toReal *
            Real.sqrt (∫ x in B, (Real.exp (g x) - 1) ^ 2
              ∂Gamma.measure (ug - u)) := hweighted
      _ ≤ Real.sqrt (Gamma.measure u B).toReal *
          ((Real.exp (S / 2) - Real.exp (-S / 2)) *
            Real.sqrt (Gammag.measure (ug - u) q).toReal) :=
        mul_le_mul_of_nonneg_left hsqrtI2 (Real.sqrt_nonneg _)
      _ = (Real.exp (S / 2) - Real.exp (-S / 2)) *
          Real.sqrt (Gamma.measure u B).toReal *
            Real.sqrt (Gammag.measure (ug - u) q).toReal := by ring
  have heq_w :
      DirichletForm.signedIntegralOn (Gammag.cross (ug - u) (ug - u)) q
          (fun _ => (1 : ℝ)) =
        -DirichletForm.signedIntegralOn (Gamma.cross u (ug - u)) B
          (fun x => Real.exp (g x) - 1) := by
    simpa [q] using heq (ug - u) hwV
  have heq_mass :
      (Gammag.measure (ug - u) q).toReal =
        -DirichletForm.signedIntegralOn (Gamma.cross u (ug - u)) B
          (fun x => Real.exp (g x) - 1) := by
    have hself := Gammag.cross_self (ug - u) hwEg q hq
    have hconst :
        DirichletForm.signedIntegralOn (Gammag.cross (ug - u) (ug - u)) q
            (fun _ => (1 : ℝ)) =
          Gammag.cross (ug - u) (ug - u) q := by
      simp only [DirichletForm.signedIntegralOn, integral_const]
      simp only [smul_eq_mul, mul_one]
      rw [measureReal_restrict_apply_univ, measureReal_restrict_apply_univ]
      calc
        (Gammag.cross (ug - u) (ug - u)).toJordanDecomposition.posPart.real q -
            (Gammag.cross (ug - u) (ug - u)).toJordanDecomposition.negPart.real q =
            (Gammag.cross (ug - u) (ug - u)).toJordanDecomposition.posPart.toSignedMeasure q -
              (Gammag.cross (ug - u) (ug - u)).toJordanDecomposition.negPart.toSignedMeasure q := by
                rw [Measure.toSignedMeasure_apply_measurable hq,
                  Measure.toSignedMeasure_apply_measurable hq]
        _ = (Gammag.cross (ug - u) (ug - u)).toJordanDecomposition.toSignedMeasure q := rfl
        _ = Gammag.cross (ug - u) (ug - u) q := by
          rw [SignedMeasure.toSignedMeasure_toJordanDecomposition]
    rw [hconst, hself] at heq_w
    exact heq_w
  have hmass0 : 0 ≤ (Gammag.measure (ug - u) q).toReal :=
    ENNReal.toReal_nonneg
  have hquad_w :
      (Real.sqrt (Gammag.measure (ug - u) q).toReal) ^ 2 ≤
        ((Real.exp (S / 2) - Real.exp (-S / 2)) *
          Real.sqrt (Gamma.measure u B).toReal) *
            Real.sqrt (Gammag.measure (ug - u) q).toReal := by
    have hsquare := Real.sq_sqrt hmass0
    calc
      (Real.sqrt (Gammag.measure (ug - u) q).toReal) ^ 2 =
          (Gammag.measure (ug - u) q).toReal := hsquare
      _ = -DirichletForm.signedIntegralOn (Gamma.cross u (ug - u)) B
          (fun x => Real.exp (g x) - 1) := heq_mass
      _ ≤ |DirichletForm.signedIntegralOn (Gamma.cross u (ug - u)) B
          (fun x => Real.exp (g x) - 1)| := neg_le_abs _
      _ ≤ ((Real.exp (S / 2) - Real.exp (-S / 2)) *
          Real.sqrt (Gamma.measure u B).toReal) *
            Real.sqrt (Gammag.measure (ug - u) q).toReal := hcross_bound
  have hfirst_q :
      Real.sqrt (Gammag.measure (ug - u) q).toReal ≤
        (Real.exp (S / 2) - Real.exp (-S / 2)) *
          Real.sqrt (Gamma.measure u B).toReal := by
    apply aux_cor_14_form_sharp_energy_quadratic
      (Real.sqrt_nonneg _) (mul_nonneg hC0 (Real.sqrt_nonneg _))
    exact hquad_w
  constructor
  · simpa [q] using hfirst_q
  · have hexp_u : Integrable (fun x => Real.exp (g x)) (Gamma.measure u) := by
      apply (integrable_const (Real.exp S)).mono hg.exp.aestronglyMeasurable
      filter_upwards [] with x
      simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _),
        abs_of_nonneg (Real.exp_nonneg _)] using
        Real.exp_le_exp.mpr (le_trans (abs_le.mp (hgabs x)).2 le_rfl)
    have hmeasure_real_u_B :
        (Gammag.measure u B).toReal =
          ∫ x in B, Real.exp (g x) ∂Gamma.measure u := by
      rw [hmeasure u hu B hB]
      symm
      exact integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall (fun x => Real.exp_nonneg _))
        hg.exp.aestronglyMeasurable
    have hmass_u_bound :
        (Gammag.measure u B).toReal ≤
          Real.exp S * (Gamma.measure u B).toReal := by
      have hmono :
          (∫ x in B, Real.exp (g x) ∂Gamma.measure u) ≤
            ∫ x in B, Real.exp S ∂Gamma.measure u := by
        apply integral_mono_ae (hexp_u.restrict) (integrable_const _)
        exact Filter.Eventually.of_forall (fun x =>
          Real.exp_le_exp.mpr (le_trans (abs_le.mp (hgabs x)).2 le_rfl))
      calc
        (Gammag.measure u B).toReal =
            ∫ x in B, Real.exp (g x) ∂Gamma.measure u := hmeasure_real_u_B
        _ ≤ ∫ x in B, Real.exp S ∂Gamma.measure u := hmono
        _ = Real.exp S * (Gamma.measure u B).toReal := by
          rw [integral_const, measureReal_restrict_apply_univ]
          change (Gamma.measure u B).toReal * Real.exp S =
            Real.exp S * (Gamma.measure u B).toReal
          ring
    have hsqrt_u :
        Real.sqrt (Gammag.measure u B).toReal ≤
          Real.exp (S / 2) * Real.sqrt (Gamma.measure u B).toReal := by
      calc
        Real.sqrt (Gammag.measure u B).toReal ≤
            Real.sqrt (Real.exp S * (Gamma.measure u B).toReal) :=
          Real.sqrt_le_sqrt hmass_u_bound
        _ = Real.exp (S / 2) * Real.sqrt (Gamma.measure u B).toReal := by
          rw [Real.sqrt_mul (Real.exp_nonneg _), ← Real.exp_half]
    have hmass_wB :
        (Gammag.measure (ug - u) B).toReal ≤
          (Gammag.measure (ug - u) q).toReal :=
      Gammag.toReal_measure_mono hwEg hBq
    have hsqrt_wB :
        Real.sqrt (Gammag.measure (ug - u) B).toReal ≤
          (Real.exp (S / 2) - Real.exp (-S / 2)) *
            Real.sqrt (Gamma.measure u B).toReal := by
      calc
        Real.sqrt (Gammag.measure (ug - u) B).toReal ≤
            Real.sqrt (Gammag.measure (ug - u) q).toReal :=
          Real.sqrt_le_sqrt hmass_wB
        _ ≤ (Real.exp (S / 2) - Real.exp (-S / 2)) *
            Real.sqrt (Gamma.measure u B).toReal := hfirst_q
    have hident :
        (Gammag.measure ug B).toReal =
          (Gammag.measure u B).toReal +
            2 * Gammag.cross u (ug - u) B +
              (Gammag.measure (ug - u) B).toReal := by
      have hsum := Gammag.cross_add_self_apply huEg hwEg B
      have hadd : u + (ug - u) = ug := by abel
      rw [hadd, Gammag.cross_self ug hug B hB,
        Gammag.cross_self u huEg B hB,
        Gammag.cross_self (ug - u) hwEg B hB] at hsum
      simpa using hsum
    have hquad_ug :
        (Real.sqrt (Gammag.measure ug B).toReal) ^ 2 ≤
          (Real.sqrt (Gammag.measure u B).toReal +
            Real.sqrt (Gammag.measure (ug - u) B).toReal) ^ 2 := by
      have hu0 : 0 ≤ (Gammag.measure u B).toReal := ENNReal.toReal_nonneg
      have hw0 : 0 ≤ (Gammag.measure (ug - u) B).toReal :=
        ENNReal.toReal_nonneg
      have hug0 : 0 ≤ (Gammag.measure ug B).toReal := ENNReal.toReal_nonneg
      have hsu := Real.sq_sqrt hu0
      have hsw := Real.sq_sqrt hw0
      have hsug := Real.sq_sqrt hug0
      have hcross := Gammag.abs_cross_le u huEg (ug - u) hwEg B hB
      have hcross_upper : Gammag.cross u (ug - u) B ≤
          Real.sqrt (Gammag.measure u B).toReal *
            Real.sqrt (Gammag.measure (ug - u) B).toReal :=
        (le_abs_self _).trans hcross
      nlinarith
    have htri :
        Real.sqrt (Gammag.measure ug B).toReal ≤
          Real.sqrt (Gammag.measure u B).toReal +
            Real.sqrt (Gammag.measure (ug - u) B).toReal := by
      have hnonneg :
          0 ≤ Real.sqrt (Gammag.measure u B).toReal +
            Real.sqrt (Gammag.measure (ug - u) B).toReal :=
        add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      nlinarith [hquad_ug, Real.sqrt_nonneg (Gammag.measure ug B).toReal]
    calc
      Real.sqrt (Gammag.measure ug B).toReal ≤
          Real.sqrt (Gammag.measure u B).toReal +
            Real.sqrt (Gammag.measure (ug - u) B).toReal := htri
      _ ≤ Real.exp (S / 2) * Real.sqrt (Gamma.measure u B).toReal +
          (Real.exp (S / 2) - Real.exp (-S / 2)) *
            Real.sqrt (Gamma.measure u B).toReal :=
        add_le_add hsqrt_u hsqrt_wB
      _ ≤ 2 * Real.exp (S / 2) * Real.sqrt (Gamma.measure u B).toReal := by
        have ha0 : 0 ≤ Real.sqrt (Gamma.measure u B).toReal := Real.sqrt_nonneg _
        have he0 : 0 ≤ Real.exp (-S / 2) := Real.exp_nonneg _
        calc
          Real.exp (S / 2) * Real.sqrt (Gamma.measure u B).toReal +
              (Real.exp (S / 2) - Real.exp (-S / 2)) *
                Real.sqrt (Gamma.measure u B).toReal =
            (2 * Real.exp (S / 2) - Real.exp (-S / 2)) *
              Real.sqrt (Gamma.measure u B).toReal := by ring
          _ ≤ 2 * Real.exp (S / 2) * Real.sqrt (Gamma.measure u B).toReal := by
            exact mul_le_mul_of_nonneg_right (sub_le_self _ he0) ha0

end Paper
