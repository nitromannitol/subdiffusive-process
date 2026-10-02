import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCoerciveCutoff

/-!
# Pointwise prices for the direct boundary coercive densities

These are the three elementary estimates used after the nonzero-datum weak
test.  They are kept independent of the GMC good event so the later layer can
insert either pointwise ellipticity bounds or the multiscale bounds supplied
by `Section6GoodScale`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization MeasureTheory

noncomputable section

variable {d : ℕ}

theorem boundaryCoerciveDatumDensity_le
    {a eta : Vec d → ℝ} {H : Vec d → Vec d} {Lam : ℝ} {x : Vec d}
    (ha0 : 0 ≤ a x) (haLam : a x ≤ Lam)
    (heta0 : 0 ≤ eta x) (heta1 : eta x ≤ 1) :
    boundaryCoerciveDatumDensity a eta H x ≤ Lam * vecNormSq (H x) := by
  have hetaSq : eta x ^ 2 ≤ 1 := by nlinarith
  have hnorm : 0 ≤ vecNormSq (H x) := vecNormSq_nonneg _
  unfold boundaryCoerciveDatumDensity
  have hcoef : a x * eta x ^ 2 ≤ Lam := by
    calc
      a x * eta x ^ 2 ≤ a x * 1 :=
        mul_le_mul_of_nonneg_left hetaSq ha0
      _ ≤ Lam := by simpa using haLam
  exact mul_le_mul_of_nonneg_right hcoef hnorm

theorem boundaryCoerciveCutoffDensity_le
    {a eta w : Vec d → ℝ} {Lam B : ℝ} {x : Vec d}
    (ha0 : 0 ≤ a x) (haLam : a x ≤ Lam)
    (hgrad : euclideanNorm (euclideanGradient eta x) ≤ B) :
    boundaryCoerciveCutoffDensity a eta w x ≤
      Lam * B ^ 2 * w x ^ 2 := by
  have hB0 : 0 ≤ B := (euclideanNorm_nonneg _).trans hgrad
  have hgradSq : vecNormSq (euclideanGradient eta x) ≤ B ^ 2 := by
    rw [← euclideanNorm_sq]
    exact pow_le_pow_left₀ (euclideanNorm_nonneg _) hgrad 2
  have hw : 0 ≤ w x ^ 2 := sq_nonneg _
  unfold boundaryCoerciveCutoffDensity
  calc
    a x * w x ^ 2 * vecNormSq (euclideanGradient eta x) ≤
        a x * w x ^ 2 * B ^ 2 :=
      mul_le_mul_of_nonneg_left hgradSq (mul_nonneg ha0 hw)
    _ ≤ Lam * w x ^ 2 * B ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right haLam hw) (sq_nonneg B)
    _ = Lam * B ^ 2 * w x ^ 2 := by ring



theorem boundaryCoerciveCutoffDensity_le_sq
    {a eta w : Vec d → ℝ} {Lam B2 : ℝ} {x : Vec d}
    (ha0 : 0 ≤ a x) (haLam : a x ≤ Lam)
    (hgrad : vecNormSq (euclideanGradient eta x) ≤ B2) :
    boundaryCoerciveCutoffDensity a eta w x ≤ Lam * B2 * w x ^ 2 := by
  have hB2 : 0 ≤ B2 := (vecNormSq_nonneg _).trans hgrad
  have hw : 0 ≤ w x ^ 2 := sq_nonneg _
  unfold boundaryCoerciveCutoffDensity
  calc
    a x * w x ^ 2 * vecNormSq (euclideanGradient eta x) ≤
        a x * w x ^ 2 * B2 :=
      mul_le_mul_of_nonneg_left hgrad (mul_nonneg ha0 hw)
    _ ≤ Lam * w x ^ 2 * B2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right haLam hw) hB2
    _ = Lam * B2 * w x ^ 2 := by ring

theorem boundaryCoerciveForceDensity_le
    {a eta : Vec d → ℝ} {G : Vec d → Vec d} {lam : ℝ} {x : Vec d}
    (hlam : 0 < lam) (hlama : lam ≤ a x)
    (heta0 : 0 ≤ eta x) (heta1 : eta x ≤ 1) :
    boundaryCoerciveForceDensity a eta G x ≤
      lam⁻¹ * vecNormSq (G x) := by
  have ha : 0 < a x := hlam.trans_le hlama
  have hetaSq : eta x ^ 2 ≤ 1 := by nlinarith
  have hinv : (a x)⁻¹ ≤ lam⁻¹ := by
    exact (inv_le_inv₀ ha hlam).2 hlama
  have hcoef : (a x)⁻¹ * eta x ^ 2 ≤ lam⁻¹ := by
    calc
      (a x)⁻¹ * eta x ^ 2 ≤ (a x)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hetaSq (inv_nonneg.mpr ha.le)
      _ ≤ lam⁻¹ := by simpa using hinv
  unfold boundaryCoerciveForceDensity
  exact mul_le_mul_of_nonneg_right hcoef (vecNormSq_nonneg _)

/-- Integrated datum price on a finite measurable window. -/
theorem volumeAverage_boundaryCoerciveDatumDensity_le
    {V : Set (Vec d)} {a eta : Vec d → ℝ} {H : Vec d → Vec d} {Lam : ℝ}
    [IsFiniteMeasure (volume.restrict V)]
    (hV : MeasurableSet V)
    (hleft : IntegrableOn (boundaryCoerciveDatumDensity a eta H) V)
    (hright : IntegrableOn (fun x => Lam * vecNormSq (H x)) V)
    (ha0 : ∀ x ∈ V, 0 ≤ a x) (haLam : ∀ x ∈ V, a x ≤ Lam)
    (heta0 : ∀ x ∈ V, 0 ≤ eta x) (heta1 : ∀ x ∈ V, eta x ≤ 1) :
    volumeAverage V (boundaryCoerciveDatumDensity a eta H) ≤
      volumeAverage V (fun x => Lam * vecNormSq (H x)) := by
  exact volumeAverage_le_volumeAverage_of_le_on hV hleft hright fun x hx =>
    boundaryCoerciveDatumDensity_le (ha0 x hx) (haLam x hx)
      (heta0 x hx) (heta1 x hx)

/-- Integrated cutoff-gradient price on a finite measurable window. -/
theorem volumeAverage_boundaryCoerciveCutoffDensity_le
    {V : Set (Vec d)} {a eta w : Vec d → ℝ} {Lam B : ℝ}
    [IsFiniteMeasure (volume.restrict V)]
    (hV : MeasurableSet V)
    (hleft : IntegrableOn (boundaryCoerciveCutoffDensity a eta w) V)
    (hright : IntegrableOn (fun x => Lam * B ^ 2 * w x ^ 2) V)
    (ha0 : ∀ x ∈ V, 0 ≤ a x) (haLam : ∀ x ∈ V, a x ≤ Lam)
    (hgrad : ∀ x ∈ V, euclideanNorm (euclideanGradient eta x) ≤ B) :
    volumeAverage V (boundaryCoerciveCutoffDensity a eta w) ≤
      volumeAverage V (fun x => Lam * B ^ 2 * w x ^ 2) := by
  exact volumeAverage_le_volumeAverage_of_le_on hV hleft hright fun x hx =>
    boundaryCoerciveCutoffDensity_le (ha0 x hx) (haLam x hx) (hgrad x hx)

/-- Integrated inverse-coefficient forcing price on a finite measurable
window. -/
theorem volumeAverage_boundaryCoerciveForceDensity_le
    {V : Set (Vec d)} {a eta : Vec d → ℝ} {G : Vec d → Vec d} {lam : ℝ}
    [IsFiniteMeasure (volume.restrict V)]
    (hV : MeasurableSet V)
    (hleft : IntegrableOn (boundaryCoerciveForceDensity a eta G) V)
    (hright : IntegrableOn (fun x => lam⁻¹ * vecNormSq (G x)) V)
    (hlam : 0 < lam) (hlama : ∀ x ∈ V, lam ≤ a x)
    (heta0 : ∀ x ∈ V, 0 ≤ eta x) (heta1 : ∀ x ∈ V, eta x ≤ 1) :
    volumeAverage V (boundaryCoerciveForceDensity a eta G) ≤
      volumeAverage V (fun x => lam⁻¹ * vecNormSq (G x)) := by
  exact volumeAverage_le_volumeAverage_of_le_on hV hleft hright fun x hx =>
    boundaryCoerciveForceDensity_le hlam (hlama x hx)
      (heta0 x hx) (heta1 x hx)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
