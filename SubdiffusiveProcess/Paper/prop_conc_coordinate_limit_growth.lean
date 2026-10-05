module

public import SubdiffusiveProcess.Paper.prop_conc_affine_cutoff_growth
public import SubdiffusiveProcess.Probability.FiniteMeasureGrowth
public import SubdiffusiveProcess.Analysis.MeasureBallGrowth

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper
noncomputable section

/-- Sum of the actual finite coordinate-minimizer energy measures. -/
def aux_prop_conc_coordinate_limit_growth_measure
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Q : Set (SpatialCoordinates d)))]
    (hQ : Bornology.IsBounded (Q : Set (SpatialCoordinates d)))
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Q,
      ‖(u : SobolevData Q).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Q) u‖)
    (a : PositiveCoefficient Q) : FiniteMeasure (SpatialCoordinates d) := by
  let mu := fun i : Fin d =>
    aux_prop_conc_affine_cutoff_growth_measure hQ hP a (Pi.single i 1)
  haveI (i : Fin d) : IsFiniteMeasure (mu i) :=
    (aux_prop_conc_affine_cutoff_growth_finite_mass hQ hP a (Pi.single i 1)).1
  exact ⟨∑ i, mu i, inferInstance⟩

/-- The original growth theorem supplies the moment bound for any weak limit
of the actual coordinate-minimizer measures. No finite growth or reciprocal
moment bound is an extra premise. The constant has exactly the model and
geometry dependence of `prop_growth`, and precedes the cutoff subsequence.
-/
theorem prop_conc_coordinate_limit_growth
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (t p : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < d) (hp : 1 ≤ p) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∃ Cbound : ℝ≥0,
      ∀ (hP : ∃ C : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
          ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
            C * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
        (N : ℕ → ℕ) (mu : BilateralField d → FiniteMeasure (SpatialCoordinates d)),
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
          ∀ phi : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          Tendsto (fun n => ∫ x, phi x ∂(aux_prop_conc_coordinate_limit_growth_measure
            (centeredCube_isBounded z hr) hP (cutoffPositiveCoefficient M H om (N n) z hr)))
            atTop (𝓝 (∫ x, phi x ∂(mu om)))) →
      ∃ K : BilateralField d → ℝ,
        Measurable K ∧ (∀ om, 0 ≤ K om) ∧
        eLpNorm K (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ Cbound ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (x : SpatialCoordinates d) (rho : ℝ), 0 < rho → rho ≤ 1 →
          (mu om : Measure (SpatialCoordinates d))
            (Metric.ball x rho ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) ≤
              ENNReal.ofReal (K om * rho ^ t) := by
  obtain ⟨delta0, hdelta0, hsupplier⟩ :=
    prop_conc_affine_cutoff_growth d hd I Pin X W Cp Sob t p ht htd hp
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr hr1
  obtain ⟨K0, C0, hKm, hKnorm, hKge, hgrowth⟩ :=
    hsupplier M Rm Sreg It H hIR hdelta z r hr hr1
  let ci : Fin d → ℝ := fun i =>
    c2Norm (closedCube z r hr : Set (SpatialCoordinates d))
      (fun y => affineSlope (Pi.single i 1) y + 0)
  let Caff : ℝ := ∑ i : Fin d, (ci i) ^ 2
  have hCaff : 0 ≤ Caff := Finset.sum_nonneg (fun i _ => sq_nonneg (ci i))
  let A : ℝ≥0 := ⟨2 ^ t * Caff, mul_nonneg (Real.rpow_nonneg (by norm_num) t) hCaff⟩
  refine ⟨A * C0, ?_⟩
  intro hP N mu hweak
  let muN := fun n om => aux_prop_conc_coordinate_limit_growth_measure
    (centeredCube_isBounded z hr) hP (cutoffPositiveCoefficient M H om (N n) z hr)
  let f : ℕ → BilateralField d → ℝ := fun n => (A : ℝ) • K0 (N n)
  let q : ℝ≥0 := ⟨p, by linarith⟩
  have hq : q ≠ 0 := by
    intro hz
    have hzR := congrArg (fun a : ℝ≥0 => (a : ℝ)) hz
    change p = 0 at hzR
    linarith
  have hqcoe : (q : ℝ≥0∞) = ENNReal.ofReal p := ENNReal.ofReal_coe_nnreal.symm
  have hf (n : ℕ) : Measurable (f n) := (hKm (N n)).const_mul _
  have hAnorm : ‖(A : ℝ)‖ₑ = (A : ℝ≥0∞) := by
    change (↑‖(A : ℝ)‖₊ : ℝ≥0∞) = (A : ℝ≥0∞)
    exact congrArg (fun a : ℝ≥0 => (a : ℝ≥0∞)) (Real.nnnorm_of_nonneg A.property)
  have hb (n : ℕ) : eLpNorm (f n) q (chaosSampleLaw M).toMeasure ≤ (A * C0 : ℝ≥0) := by
    change eLpNorm ((A : ℝ) • K0 (N n)) q (chaosSampleLaw M).toMeasure ≤ _
    rw [eLpNorm_const_smul, hAnorm, ENNReal.coe_mul, hqcoe]
    exact mul_le_mul_right (hKnorm (N n)) _
  let T := SpatialCoordinates d × {rho : ℝ // 0 < rho ∧ rho ≤ 1}
  let tests : T → Set (SpatialCoordinates d) := fun b =>
    Metric.ball b.1 b.2.val ∩ (centeredCube z r hr : Set (SpatialCoordinates d))
  let scale : T → ℝ≥0 := fun b => ⟨b.2.val ^ t, Real.rpow_nonneg b.2.property.1.le t⟩
  have hopen (b : T) : IsOpen (tests b) :=
    Metric.isOpen_ball.inter (centeredCube z r hr).isOpen
  have hconv : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      Tendsto (fun n => muN n om) atTop (𝓝 (mu om)) :=
    hweak.mono fun om hom => FiniteMeasure.tendsto_of_forall_integral_tendsto hom
  have ht0 : 0 ≤ t := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [ht, hdR]
  have hfiniteGrowth : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ n b,
      (muN n om : Measure (SpatialCoordinates d)) (tests b) ≤
        (scale b : ℝ≥0∞) * ‖f n om‖ₑ := by
    filter_upwards [hgrowth, hKge] with om hom hge n b
    have hK0 : 0 ≤ K0 (N n) om := zero_le_one.trans (hge (N n))
    have hlocal : ∀ x ∈ centeredCube z r hr, ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
        (muN n om : Measure (SpatialCoordinates d))
          (Metric.ball x rho ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) ≤
            ENNReal.ofReal ((K0 (N n) om * Caff) * rho ^ t) := by
      intro x hx rho hrho hrho1
      change (∑ i : Fin d, aux_prop_conc_affine_cutoff_growth_measure
        (centeredCube_isBounded z hr) hP (cutoffPositiveCoefficient M H om (N n) z hr)
        (Pi.single i 1)) _ ≤ _
      rw [Measure.finsetSum_apply]
      calc
        _ ≤ ∑ i : Fin d, ENNReal.ofReal (K0 (N n) om * (ci i) ^ 2 * rho ^ t) :=
          Finset.sum_le_sum (fun i _ => (hom hP (N n) (Pi.single i 1)).2.2 x rho hx hrho hrho1)
        _ = ENNReal.ofReal ((K0 (N n) om * Caff) * rho ^ t) := by
          rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ =>
            mul_nonneg (mul_nonneg hK0 (sq_nonneg _)) (Real.rpow_nonneg hrho.le _))]
          congr 1
          simp only [Caff, Finset.sum_mul, Finset.mul_sum]
    have hz : z ∈ centeredCube z r hr := Metric.mem_ball_self (half_pos hr)
    have hcell : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ Metric.ball z 1 := by
      intro y hy
      change dist y z < r / 2 at hy
      change dist y z < 1
      exact lt_of_lt_of_le hy (by linarith)
    have h := measure_ball_inter_growth_of_centers_mem
      (muN n om) (centeredCube z r hr) z hz hcell (K0 (N n) om * Caff) t
      (mul_nonneg hK0 hCaff) ht0 hlocal b.1 b.2.val b.2.property.1 b.2.property.2
    have hid : (2 ^ t * (K0 (N n) om * Caff)) * b.2.val ^ t =
        b.2.val ^ t * f n om := by change _ = _ * ((2 ^ t * Caff) * K0 (N n) om); ring
    rw [hid, ENNReal.ofReal_mul (Real.rpow_nonneg b.2.property.1.le t)] at h
    rw [show (scale b : ℝ≥0∞) = ENNReal.ofReal (b.2.val ^ t) from
      ENNReal.ofReal_coe_nnreal.symm]
    refine h.trans (mul_le_mul_right ?_ _)
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  obtain ⟨K, hKm', hKpos, hKn, hKg⟩ := exists_measure_growth_of_weak_convergence
    (chaosSampleLaw M).toMeasure muN mu tests hopen scale f q (A * C0) hq hf hb hconv hfiniteGrowth
  refine ⟨K, hKm', hKpos, by simpa only [hqcoe] using hKn, ?_⟩
  filter_upwards [hKg] with om hom x rho hrho hrho1
  have h := hom (x, ⟨rho, hrho, hrho1⟩)
  have hs : ((scale (x, ⟨rho, hrho, hrho1⟩)) : ℝ≥0∞) = ENNReal.ofReal (rho ^ t) :=
    ENNReal.ofReal_coe_nnreal.symm
  rw [hs, ← ENNReal.ofReal_mul (hKpos om)] at h
  exact h

end
end SubdiffusiveProcess.Paper
