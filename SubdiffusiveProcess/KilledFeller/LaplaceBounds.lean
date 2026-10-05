module

public import MarkovProcess.Semigroup.Resolvent
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

open Filter MeasureTheory Set Topology
noncomputable section
namespace SubdiffusiveProcess.KilledFeller

/-- The positive exponential weight has tail integral `λ⁻¹ exp(-λh)`. -/
theorem integral_exp_neg_mul_Ioi {lam : ℝ} (hlam : 0 < lam) (h : ℝ) :
    (∫ t in Ioi h, Real.exp (-lam * t)) = lam⁻¹ * Real.exp (-lam * h) := by
  rw [integral_exp_mul_Ioi (neg_neg_of_pos hlam)]
  field_simp

/-- A bounded measurable scalar test is integrable against a positive Laplace weight. -/
theorem integrableOn_exp_mul_bounded (a : ℝ → ℝ) (ha : Measurable a)
    {lam B : ℝ} (hlam : 0 < lam)
    (hbound : ∀ t ∈ Ioi (0 : ℝ), |a t| ≤ B) :
    IntegrableOn (fun t => Real.exp (-lam * t) * a t) (Ioi (0 : ℝ)) := by
  apply ((exp_neg_integrableOn_Ioi 0 hlam).mul_const B).mono'
    ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul ha).aestronglyMeasurable
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  change ‖Real.exp (-lam * t) * a t‖ ≤ Real.exp (-lam * t) * B
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (hbound t ht) (Real.exp_pos _).le

/-- Splitting a normalized Laplace transform at h bounds its error by the short-time modulus and exponential tail. -/
theorem normalized_laplace_deviation_bound
    (a : ℝ → ℝ) (ha : Measurable a)
    (lam h c m B : ℝ) (hlam : 0 < lam) (hh : 0 ≤ h) (hm : 0 ≤ m) (_hB : 0 ≤ B)
    (hbound : ∀ t ∈ Ioi (0 : ℝ), |a t - c| ≤ B)
    (hnear : ∀ t ∈ Ioc (0 : ℝ) h, |a t - c| ≤ m) :
    |lam * (∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) * a t) - c| ≤
      m + B * Real.exp (-lam * h) := by
  let e : ℝ → ℝ := fun t => Real.exp (-lam * t)
  have he : IntegrableOn e (Ioi (0 : ℝ)) := exp_neg_integrableOn_Ioi 0 hlam
  have hdiff : IntegrableOn (fun t => e t * (a t - c)) (Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_bounded (fun t => a t - c) (ha.sub measurable_const) hlam hbound
  have hconst : IntegrableOn (fun t => e t * c) (Ioi (0 : ℝ)) := he.mul_const c
  have haint : IntegrableOn (fun t => e t * a t) (Ioi (0 : ℝ)) := by
    change Integrable (fun t => e t * a t) (volume.restrict (Ioi (0 : ℝ)))
    convert (Integrable.add hdiff hconst) using 1
    funext t
    simp only [Pi.add_apply]
    ring
  have hrewrite : lam * (∫ t in Ioi (0 : ℝ), e t * a t) - c =
      lam * (∫ t in Ioi (0 : ℝ), e t * (a t - c)) := by
    rw [show (fun t => e t * (a t - c)) = (fun t => e t * a t) - (fun t => e t * c) by
      funext t; simp only [Pi.sub_apply]; ring]
    change lam * (∫ t in Ioi (0 : ℝ), e t * a t) - c =
      lam * (∫ t in Ioi (0 : ℝ), e t * a t - e t * c)
    rw [integral_sub haint hconst, integral_mul_const]
    dsimp only [e]
    rw [MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.integral_exp_neg_mul_Ioi_zero hlam]
    field_simp
  have htail : IntegrableOn ((Ioi h).indicator (fun t => e t * B)) (Ioi (0 : ℝ)) :=
    (he.mul_const B).indicator measurableSet_Ioi
  have hdom : IntegrableOn (fun t => e t * m + (Ioi h).indicator (fun s => e s * B) t)
      (Ioi (0 : ℝ)) := (he.mul_const m).add htail
  have hcompare : |∫ t in Ioi (0 : ℝ), e t * (a t - c)| ≤
      ∫ t in Ioi (0 : ℝ), e t * m + (Ioi h).indicator (fun s => e s * B) t := by
    rw [← Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le hdom
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    by_cases hth : h < t
    · rw [indicator_of_mem (show t ∈ Ioi h from hth)]
      exact (mul_le_mul_of_nonneg_left (hbound t ht) (Real.exp_pos _).le).trans
        (le_add_of_nonneg_left (mul_nonneg (Real.exp_pos _).le hm))
    · rw [indicator_of_notMem (show t ∉ Ioi h from hth), add_zero]
      exact mul_le_mul_of_nonneg_left (hnear t ⟨ht, le_of_not_gt hth⟩) (Real.exp_pos _).le
  have htailIntegral : (∫ t in Ioi (0 : ℝ), (Ioi h).indicator (fun s => e s * B) t) =
      lam⁻¹ * Real.exp (-lam * h) * B := by
    rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      Set.inter_eq_left.mpr (Ioi_subset_Ioi hh), integral_mul_const]
    exact congrArg (fun z => z * B) (integral_exp_neg_mul_Ioi hlam h)
  rw [hrewrite, abs_mul, abs_of_pos hlam]
  calc
    lam * |∫ t in Ioi (0 : ℝ), e t * (a t - c)| ≤
        lam * (∫ t in Ioi (0 : ℝ), e t * m + (Ioi h).indicator (fun s => e s * B) t) :=
      mul_le_mul_of_nonneg_left hcompare hlam.le
    _ = m + B * Real.exp (-lam * h) := by
      rw [integral_add (he.mul_const m) htail, integral_mul_const, htailIntegral]
      dsimp only [e]
      rw [MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.integral_exp_neg_mul_Ioi_zero hlam]
      field_simp [hlam.ne']

end SubdiffusiveProcess.KilledFeller
