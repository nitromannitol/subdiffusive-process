module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.RoughDirichletDatum
public import Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliRHS.EnergySplit

@[expose] public section

/-!
# Boundary Caccioppoli after a rough Dirichlet lift

The local boundary patch only records that `u - v` has zero trace through the
patch.  Subtracting the rough Dirichlet lift removes the boundary datum without
differentiating the coefficient.  This file packages the homogeneous
Caccioppoli estimate, the coefficient-energy triangle inequality, and the
Dirichlet-energy price of the lift.

The energy estimate uses GMC's exponential shell-ratio carrier.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The flux of an `H¹` function is square integrable. -/
theorem memVectorL2_flux (Q : TriadicCube d) (a : CoeffFamily d)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) :
    MemVectorL2 (Ch02.cubeDomain Q : Set (Vec d))
      (fun x => matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x)) := by
  have hB : MemVectorL2 (Ch02.cubeDomain Q : Set (Vec d))
      (fun x => matVecMul (publicCoeffField Q a x) (u.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn
      (publicCoeffField_isEllipticFieldOn Q a) u.grad_memVectorL2
  refine hB.ae_eq ?_
  filter_upwards [publicCoeffField_ae_eq Q a] with x hx
  rw [hx]

private theorem matVecMul_sub_right (A : Mat d) (x y : Vec d) :
    matVecMul A (x - y) = matVecMul A x - matVecMul A y := by
  rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg, sub_eq_add_neg]

theorem integrableOn_flux_pairing (Q : TriadicCube d) (a : CoeffFamily d)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d)))
    (φ : H10Function (Ch02.cubeDomain Q : Set (Vec d))) :
    IntegrableOn
      (fun x => vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x))
        (φ.toH1Function.grad x))
      (Ch02.cubeDomain Q : Set (Vec d)) :=
  integrableOn_vecDot_of_memVectorL2 (memVectorL2_flux Q a u)
    φ.toH1Function.grad_memVectorL2

/-- The difference of two solutions with the same force is homogeneous. -/
theorem isForcedEquation_sub {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d} {u v : H1Function (Ch02.cubeDomain Q : Set (Vec d))}
    (hu : IsForcedEquation Q a u g) (hv : IsForcedEquation Q a v g) :
    IsForcedEquation Q a (u - v) (fun _ => 0) := by
  intro φ
  have hrw : ∀ x,
      vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) ((u - v).grad x))
          (φ.toH1Function.grad x) =
        vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x))
            (φ.toH1Function.grad x) -
          vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (v.grad x))
            (φ.toH1Function.grad x) := by
    intro x
    rw [H1Function.sub_grad]
    show vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x - v.grad x)) _ = _
    rw [matVecMul_sub_right]
    simp only [vecDot, Pi.sub_apply]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hzero : ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
      vecDot ((fun _ : Vec d => (0 : Vec d)) x) (φ.toH1Function.grad x) ∂volume = 0 := by
    simp [vecDot]
  rw [hzero]
  calc
    ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
        vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) ((u - v).grad x))
          (φ.toH1Function.grad x) ∂volume =
      ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
        (vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x))
            (φ.toH1Function.grad x) -
          vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (v.grad x))
            (φ.toH1Function.grad x)) ∂volume :=
        integral_congr_ae (Filter.Eventually.of_forall hrw)
    _ = (∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
          vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x))
            (φ.toH1Function.grad x) ∂volume) -
        ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
          vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (v.grad x))
            (φ.toH1Function.grad x) ∂volume :=
      integral_sub (integrableOn_flux_pairing Q a u φ)
        (integrableOn_flux_pairing Q a v φ)
    _ = 0 := by rw [hu φ, hv φ, sub_self]

theorem forceBesovRegularity_zero (Q : TriadicCube d) (s : ℝ) :
    ForceBesovRegularity Q s (fun _ : Vec d => (0 : Vec d)) where
  memLp := (MemLp.zero : MemLp (0 : Vec d → Vec d) 2 (normalizedCubeMeasure Q))
  partialSeminorms_bddAbove :=
    cubeBesovPositiveVectorPartialSeminormTwo_zero_bddAbove Q s

/-- The homogeneous difference, retaining the localized boundary trace. -/
def boundaryForcedCaccioppoliDatumOfDifference {Q : TriadicCube d}
    {a : CoeffFamily d} (x : Vec d) {g : Vec d → Vec d}
    {u v : H1Function (Ch02.cubeDomain Q : Set (Vec d))}
    (hu : IsForcedEquation Q a u g) (hv : IsForcedEquation Q a v g)
    (hdiff : Ch01.LocalizedZeroTraceFunctionOn
      (Ch02.cubeDomain Q : Set (Vec d)) (openCubeAtScale x (Q.scale - 1))
      (fun y => u.toFun y - v.toFun y)) :
    BoundaryForcedCaccioppoliDatum Q a x (fun _ => 0) where
  toH1 := u - v
  weakSolution := isForcedEquation_sub hu hv
  zeroTraceOnBoundaryPatch := by
    rw [H1Function.sub_toFun]
    exact hdiff

variable [NeZero d]

/-- Caccioppoli for the homogeneous difference of two same-force solutions. -/
theorem exists_boundaryCaccioppoliEnergy_ofDifference (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {s t : ℝ} {x : Vec d}
        {g : Vec d → Vec d}
        (u v : H1Function (Ch02.cubeDomain Q : Set (Vec d))),
        IsForcedEquation Q a u g → IsForcedEquation Q a v g →
        Ch01.LocalizedZeroTraceFunctionOn
          (Ch02.cubeDomain Q : Set (Vec d)) (openCubeAtScale x (Q.scale - 1))
          (fun y => u.toFun y - v.toFun y) →
        0 < s → s < 1 → 0 < t → t < 1 / 2 → s + t < 1 →
        x ∈ openCubeSet Q →
          localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) (u - v) ≤
            caccioppoliWithRHSPrefactor C Q a s t *
              (Ch02.lambdaS Q t a *
                (3 : ℝ) ^ (-(2 * Q.scale)) *
                normalizedL2SqOnSet (openCubeSet Q) (fun y => u.toFun y - v.toFun y)) := by
  obtain ⟨C, hC, hbound⟩ := (coarseCaccioppoliRHSTheory (d := d)).exists_constant
  refine ⟨C, hC, ?_⟩
  intro Q a s t x g u v hu hv hdiff hs hs1 ht ht2 hst hx
  let datum := boundaryForcedCaccioppoliDatumOfDifference x hu hv hdiff
  have h := hbound datum hs hs1 ht ht2 hst hx (forceBesovRegularity_zero Q (2 * t))
  dsimp [datum, boundaryForcedCaccioppoliDatumOfDifference,
    Homogenization.Book.Ch03.boundaryCaccioppoliWithRHSRHS,
    boundaryForcedCaccioppoliCoreEnergy, boundaryForcedCaccioppoliParentL2Sq] at h
  have hzero : (fun _ : Vec d => (0 : Vec d)) = (0 : Vec d → Vec d) := rfl
  rw [hzero] at h
  simp only [Homogenization.Book.Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo,
    cubeBesovPositiveVectorSeminormTwo_zero] at h
  norm_num at h
  have hexp : ((-(2 * Q.scale) : ℤ) : ℝ) = -(2 * ((Q.scale : ℤ) : ℝ)) := by
    push_cast
    ring
  rw [← Real.rpow_intCast]
  rw [hexp]
  have hfun : (u - v).toFun = fun y => u.toFun y - v.toFun y := by
    simpa only using! H1Function.sub_toFun u v
  have h' : localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) (u - v) ≤
      caccioppoliWithRHSPrefactor C Q a s t *
        (Ch02.lambdaS Q t a * 3 ^ (-(2 * (Q.scale : ℝ))) *
          normalizedL2SqOnSet (openCubeSet Q) (u - v).toFun) := h
  rw [hfun] at h'
  exact h'

/-- Coefficient-energy triangle inequality on a local core. -/
theorem localizedCoeffEnergyValue_core_le_two_mul_sub_add
    {Q : TriadicCube d} {a : CoeffFamily d} {x : Vec d}
    (u v : H1Function (Ch02.cubeDomain Q : Set (Vec d))) :
    localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) u ≤
      2 * localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) (u - v) +
        2 * localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) v := by
  set V : Set (Vec d) := caccioppoliCoreSet Q x
  have hVopen : V ⊆ openCubeSet Q := fun _ hy => hy.1
  have hVcube : V ⊆ cubeSet Q := fun y hy => openCubeSet_subset_cubeSet Q (hVopen hy)
  have hmono : volumeMeasureOn V ≤ volumeMeasureOn (openCubeSet Q) :=
    Measure.restrict_mono_set volume hVopen
  have hu := u.grad_memVectorL2.mono_measure hmono
  have hv := v.grad_memVectorL2.mono_measure hmono
  have hw := (u - v).grad_memVectorL2.mono_measure hmono
  have hsplit : u.grad =ᵐ[volumeMeasureOn V] fun y => (u - v).grad y + v.grad y := by
    filter_upwards with y
    rw [H1Function.sub_grad]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have htriangle :=
    volumeAverage_coefficientEnergyDensity_le_two_mul_add_of_ae_eq_add
      (V := V) (A := publicCoeffField Q a)
      (lam := (a.coeffOn Q).lam) (Lam := (a.coeffOn Q).Lam)
      ((publicCoeffField_isEllipticFieldOn_cubeSet Q a).mono
        (measurableSet_caccioppoliCoreSet Q x) hVcube)
      hu hw hv hsplit
  rw [localizedCoeffEnergyValue_eq_volumeAverage_publicCoeffField_of_subset_openCubeSet
      hVopen u,
    localizedCoeffEnergyValue_eq_volumeAverage_publicCoeffField_of_subset_openCubeSet
      hVopen (u - v),
    localizedCoeffEnergyValue_eq_volumeAverage_publicCoeffField_of_subset_openCubeSet
      hVopen v]
  exact htriangle

/-- A local core average is controlled by the parent energy. -/
theorem localizedCoeffEnergyValue_core_le_eighteen_pow_mul_parent
    {Q : TriadicCube d} {a : CoeffFamily d} {x : Vec d} (hx : x ∈ openCubeSet Q)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) :
    localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) u ≤
      (18 : ℝ) ^ d * localizedCoeffEnergyValue (openCubeSet Q) (a.coeffOn Q) u := by
  have hcore : caccioppoliCoreSet Q x ⊆ openCubeSet Q := fun _ hy => hy.1
  have hnonneg : ∀ y ∈ cubeSet Q,
      0 ≤ coefficientEnergyDensity (publicCoeffField Q a) u.grad y :=
    coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
      (publicCoeffField_isEllipticFieldOn_cubeSet Q a) u.grad
  have hgrad : MemVectorL2 (cubeSet Q) u.grad := by
    simpa [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using u.grad_memVectorL2
  have hint := integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn
    (publicCoeffField_isEllipticFieldOn_cubeSet Q a) hgrad
  have havg := normalizedSetAverage_caccioppoliCoreSet_le_eighteen_pow_mul_cubeAverage
    Q hx hnonneg hint
  rw [localizedCoeffEnergyValue_eq_volumeAverage_publicCoeffField_of_subset_openCubeSet
      hcore u,
    ← cubeAverage_coefficientEnergyDensity_publicCoeffField_eq_localizedCoeffEnergyValue Q a u]
  exact havg

omit [NeZero d] in
theorem localizedCoeffEnergyValue_openCubeSet_nonneg (Q : TriadicCube d)
    (a : CoeffFamily d) (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) :
    0 ≤ localizedCoeffEnergyValue (openCubeSet Q) (a.coeffOn Q) u := by
  rw [← cubeAverage_coefficientEnergyDensity_publicCoeffField_eq_localizedCoeffEnergyValue
    Q a u]
  exact cubeAverage_nonneg_of_nonneg_on
    (coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
      (publicCoeffField_isEllipticFieldOn_cubeSet Q a) u.grad)

omit [NeZero d] in
theorem dirichletForcedSolutionEnergyNorm_sq (Q : TriadicCube d) (a : CoeffFamily d)
    {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g) :
    dirichletForcedSolutionEnergyNorm Q a v ^ 2 =
      localizedCoeffEnergyValue (openCubeSet Q) (a.coeffOn Q) v.toH1 := by
  rw [dirichletForcedSolutionEnergyNorm, h1EnergyNormOnCube]
  exact Real.sq_sqrt (localizedCoeffEnergyValue_openCubeSet_nonneg Q a v.toH1)

/-- The parent energy of a Dirichlet solution is bounded by the Chapter-3 RHS. -/
theorem exists_localizedCoeffEnergyValue_openCubeSet_le_dirichletEnergyWithRHSRHS_sq
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {r : ℝ} {g : Vec d → Vec d}
        (v : DirichletForcedCubeSolution Q a g),
        0 < r → r < 1 → ForceBesovRegularity Q r g →
        ForceBesovRegularity Q r (dirichletBoundaryGradientField v) →
          localizedCoeffEnergyValue (openCubeSet Q) (a.coeffOn Q) v.toH1 ≤
            dirichletEnergyWithRHSRHS C Q a r g v ^ 2 := by
  obtain ⟨C, hC, hdir, _⟩ := (energyConsequencesRHSTheory (d := d)).exists_constant
  refine ⟨C, hC, ?_⟩
  intro Q a r g v hr hr1 hg hh
  have hbase := hdir (Q := Q) (a := a) (s := r) (g := g) v hr hr1 hg hh
  have hnn : 0 ≤ dirichletForcedSolutionEnergyNorm Q a v := by
    rw [dirichletForcedSolutionEnergyNorm, h1EnergyNormOnCube]
    exact Real.sqrt_nonneg _
  rw [← dirichletForcedSolutionEnergyNorm_sq Q a v]
  exact pow_le_pow_left₀ hnn hbase 2

/-- Boundary Caccioppoli plus the rough Dirichlet lift's energy. -/
theorem exists_boundaryCaccioppoliEnergy_withBoundaryDatum (d : ℕ) [NeZero d] :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {s t r : ℝ} {x : Vec d}
        {g : Vec d → Vec d} (u : H1Function (Ch02.cubeDomain Q : Set (Vec d)))
        (v : DirichletForcedCubeSolution Q a g),
        IsForcedEquation Q a u g →
        Ch01.LocalizedZeroTraceFunctionOn
          (Ch02.cubeDomain Q : Set (Vec d)) (openCubeAtScale x (Q.scale - 1))
          (fun y => u.toFun y - v.toH1.toFun y) →
        0 < s → s < 1 → 0 < t → t < 1 / 2 → s + t < 1 →
        0 < r → r < 1 → ForceBesovRegularity Q r g →
        ForceBesovRegularity Q r (dirichletBoundaryGradientField v) →
        x ∈ openCubeSet Q →
          localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) u ≤
            2 * (caccioppoliWithRHSPrefactor C₁ Q a s t *
              (Ch02.lambdaS Q t a *
                (3 : ℝ) ^ (-(2 * Q.scale)) *
                normalizedL2SqOnSet (openCubeSet Q)
                  (fun y => u.toFun y - v.toH1.toFun y))) +
              2 * ((18 : ℝ) ^ d * dirichletEnergyWithRHSRHS C₂ Q a r g v ^ 2) := by
  obtain ⟨C₁, hC₁, hcacc⟩ := exists_boundaryCaccioppoliEnergy_ofDifference d
  obtain ⟨C₂, hC₂, henergy⟩ :=
    exists_localizedCoeffEnergyValue_openCubeSet_le_dirichletEnergyWithRHSRHS_sq d
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro Q a s t r x g u v hu hdiff hs hs1 ht ht2 hst hr hr1 hg hh hx
  have hd := hcacc u v.toH1 hu v.weakSolution hdiff hs hs1 ht ht2 hst hx
  have hvcore := localizedCoeffEnergyValue_core_le_eighteen_pow_mul_parent
    (a := a) hx v.toH1
  have hvparent := henergy v hr hr1 hg hh
  have hv : localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) v.toH1 ≤
      (18 : ℝ) ^ d * dirichletEnergyWithRHSRHS C₂ Q a r g v ^ 2 :=
    hvcore.trans (mul_le_mul_of_nonneg_left hvparent (by positivity))
  have hmink := localizedCoeffEnergyValue_core_le_two_mul_sub_add
    (x := x) (a := a) u v.toH1
  linarith only [hmink, hd, hv]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
