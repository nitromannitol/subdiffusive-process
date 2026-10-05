module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section2Support
public import Homogenization.Book.Ch03.Theorems.CoarsePoincare
public import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.CanonicalFields
public import Homogenization.Probability.LocalEllipticitySlices.SymmetricL2

@[expose] public section

namespace SubdiffusiveProcess.Providers.Section2

open MeasureTheory Homogenization Homogenization.Book
open scoped BigOperators ENNReal

noncomputable section


-- the energy-integrability route is generalized here from solutions to arbitrary `H¹` data,
-- while its coefficient-to-a.e.-ellipticity step is reused from CoarseGraining.
private theorem coefficientEnergyIntegrable {d : ℕ} {U : Ch02.Domain d}
    (a : Ch02.CoeffOn U) (u : H1Function (U : Set (Vec d))) :
    IntegrableOn
      (fun x => vecDot (u.grad x) (matVecMul (a.toCoeffField x) (u.grad x)))
      (U : Set (Vec d)) volume := by
  have hflux : MemVectorL2 (U : Set (Vec d))
      (fun x => matVecMul (a.toCoeffField x) (u.grad x)) :=
    (Ch05.Section53.JUpperBoundWeakNorms.ch02_coeffOn_isAEEllipticFieldOn a).memVectorL2_matVecMul
      u.grad_memVectorL2
  exact integrableOn_vecDot_of_memVectorL2 u.grad_memVectorL2 hflux

private theorem inverseCoefficientEnergyIntegrable {d : ℕ} {U : Ch02.Domain d}
    (a : Ch02.CoeffOn U) (hsym : a.IsSymmetric)
    (h : Vec d → Vec d) (hh : MemVectorL2 (U : Set (Vec d)) h) :
    IntegrableOn
      (fun x => vecDot (h x) (matVecMul (a.toCoeffField x)⁻¹ (h x)))
      (U : Set (Vec d)) volume := by
  let b : Ch02.CoeffOn U := Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffOn U a
  have hba : Ch02.CoeffOn.AEEq b a := by
    simpa [b] using Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq U a
  have hEll : IsEllipticFieldOn b.lam b.Lam (U : Set (Vec d)) b.toCoeffField := by
    simpa [b] using
      Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffOn_isEllipticFieldOn U a
  have hinv : MemVectorL2 (U : Set (Vec d))
      (fun x => matVecMul (symmPart (b.toCoeffField x))⁻¹ (h x)) :=
    memVectorL2_matVecMul_symmPartInv_of_isEllipticFieldOn hEll hh
  have hbase : IntegrableOn
      (fun x => vecDot (h x) (matVecMul (symmPart (b.toCoeffField x))⁻¹ (h x)))
      (U : Set (Vec d)) volume :=
    integrableOn_vecDot_of_memVectorL2 hh hinv
  refine hbase.congr ?_
  filter_upwards [hsym, hba] with x hsymm hba_x
  rw [hba_x]
  have hs : symmPart (a.toCoeffField x) = a.toCoeffField x := by
    ext i j
    have hij : a.toCoeffField x j i = a.toCoeffField x i j :=
      (Matrix.IsSymm.ext_iff.mp hsymm) i j
    simp [symmPart, hij]
  rw [hs]

private theorem arbitraryGradientAverageEnergyControl {d : ℕ}
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) (hsym : a.IsSymmetric)
    (u : H1Function (U : Set (Vec d))) :
    vecNormSq (Ch02.h1AverageGradient U u) ≤
      Ch02.matrixNorm (Ch02.sigmaStarInvCoarse U a) *
        Ch02.average U
          (fun x => vecDot (u.grad x) (matVecMul (a.toCoeffField x) (u.grad x))) := by
  let theory := Ch02.responseSymmetricDirichletNeumannTheory U a hsym
  let p : Vec d := Ch02.h1AverageGradient U u
  let q : Vec d := matVecMul (Ch02.sigmaStarCoarse U a) p
  obtain ⟨v, _hvMean, hv⟩ := theory.neumann_meanZero_maximizer_exists q
  have hcandidate := hv u
  have hmaxValue :
      Ch02.symmetricNeumannEnergyValue U a q v =
        (1 / 2 : ℝ) * vecDot q (matVecMul (Ch02.sigmaStarInvCoarse U a) q) := by
    rw [← Homogenization.Internal.Ch02.BookCh02.symmetricNeumannNu_eq_of_maximizer hv,
      theory.neumann_value_by_sigmaStarInv]
  have hdet : IsUnit (Ch02.sigmaStarInvCoarse U a).det :=
    (Matrix.isUnit_iff_isUnit_det (A := Ch02.sigmaStarInvCoarse U a)).mp
      (Ch02.sigmaStarInvCoarse_posDef U a).isUnit
  have hleft : ∀ ξ : Vec d,
      matVecMul (Ch02.sigmaStarInvCoarse U a)
        (matVecMul (Ch02.sigmaStarCoarse U a) ξ) = ξ := by
    intro ξ
    rw [matVecMul_mul, Ch02.sigmaStarInvCoarse_mul_sigmaStarCoarse hdet]
    funext i
    simp [matVecMul, Matrix.one_apply]
  have hq : matVecMul (Ch02.sigmaStarInvCoarse U a) q = p := by
    simpa [q] using hleft p
  have hgradCoord : ∀ i, IntegrableOn (fun x => u.grad x i) (U : Set (Vec d)) := by
    intro i
    exact CorrectionFieldData.integrableOn_coord_of_memVectorL2 u.grad_memVectorL2 i
  have hpair :
      Ch02.average U (fun x => vecDot q (u.grad x)) = vecDot q p := by
    simpa [Ch02.average, Ch02.h1AverageGradient, Ch02.averageVec, p] using!
      volumeAverage_vecDot_left (U := (U : Set (Vec d))) q u.grad hgradCoord
  have henergyInt := coefficientEnergyIntegrable a u
  have hcandidateValue :
      Ch02.symmetricNeumannEnergyValue U a q u =
        vecDot q p - (1 / 2 : ℝ) *
          Ch02.average U
            (fun x => vecDot (u.grad x) (matVecMul (a.toCoeffField x) (u.grad x))) := by
    unfold Ch02.symmetricNeumannEnergyValue
    have hpairInt : IntegrableOn (fun x => vecDot q (u.grad x)) (U : Set (Vec d)) :=
      CorrectionFieldData.integrableOn_vecDot_const_left_of_memVectorL2 q
        u.grad_memVectorL2
    have hpairVol :
        volumeAverage (U : Set (Vec d)) (fun x => vecDot q (u.grad x)) = vecDot q p := by
      simpa [Ch02.average] using! hpair
    change volumeAverage (U : Set (Vec d))
        (fun x => vecDot q (u.grad x) -
          1 / 2 * vecDot (u.grad x) (matVecMul (a.toCoeffField x) (u.grad x))) =
      vecDot q p - 1 / 2 * volumeAverage (U : Set (Vec d))
        (fun x => vecDot (u.grad x) (matVecMul (a.toCoeffField x) (u.grad x)))
    rw [show (fun x => vecDot q (u.grad x) -
          1 / 2 * vecDot (u.grad x) (matVecMul (a.toCoeffField x) (u.grad x))) =
        (fun x => vecDot q (u.grad x)) -
          fun x => 1 / 2 * vecDot (u.grad x)
            (matVecMul (a.toCoeffField x) (u.grad x)) by rfl,
      volumeAverage_sub hpairInt (henergyInt.const_mul (1 / 2 : ℝ)), hpairVol]
    rw [show (fun x => 1 / 2 * vecDot (u.grad x)
          (matVecMul (a.toCoeffField x) (u.grad x))) =
        (1 / 2 : ℝ) • fun x => vecDot (u.grad x)
          (matVecMul (a.toCoeffField x) (u.grad x)) by
        funext x; simp]
    rw [volumeAverage_smul]
  have hquad :
      vecDot p (matVecMul (Ch02.sigmaStarCoarse U a) p) ≤
        Ch02.average U
          (fun x => vecDot (u.grad x) (matVecMul (a.toCoeffField x) (u.grad x))) := by
    rw [hcandidateValue, hmaxValue, hq] at hcandidate
    have hqp : vecDot q p = vecDot p (matVecMul (Ch02.sigmaStarCoarse U a) p) := by
      simp [q, vecDot_comm]
    rw [hqp] at hcandidate
    linarith
  have hnorm :=
    Ch02.vecNormSq_le_matrixNorm_mul_vecDot_matVecMul_of_posSemidef_of_leftInverse
      (A := Ch02.sigmaStarCoarse U a) (B := Ch02.sigmaStarInvCoarse U a)
      (Ch02.sigmaStarInvCoarse_posDef U a).posSemidef hleft p
  exact hnorm.trans
    (mul_le_mul_of_nonneg_left hquad (Ch02.matrixNorm_nonneg _))

private theorem scaleNormalizedNegativeBesovVectorNorm_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (q : Ch02.MultiscaleExponent)
    (F : Vec d → Vec d) :
    0 ≤ Ch03.scaleNormalizedNegativeBesovVectorNorm Q s q F := by
  cases q with
  | finite q =>
      unfold Ch03.scaleNormalizedNegativeBesovVectorNorm
      change 0 ≤ sSup
        (Set.range fun N : ℕ => Ch03.negativeBesovVectorPartialNormFinite Q s q N F)
      by_cases hb : BddAbove
          (Set.range fun N : ℕ => Ch03.negativeBesovVectorPartialNormFinite Q s q N F)
      · exact (Ch03.negativeBesovVectorPartialNormFinite_nonneg Q s q 0 F).trans
          (le_csSup hb ⟨0, rfl⟩)
      · rw [Real.sSup_of_not_bddAbove hb]
  | infinity =>
      unfold Ch03.scaleNormalizedNegativeBesovVectorNorm
      change 0 ≤ sSup
        (Set.range fun j : ℕ => Ch03.negativeBesovVectorDepthSeminorm Q s F j)
      by_cases hb : BddAbove
          (Set.range fun j : ℕ => Ch03.negativeBesovVectorDepthSeminorm Q s F j)
      · exact (Ch03.negativeBesovVectorDepthSeminorm_nonneg Q s F 0).trans
          (le_csSup hb ⟨0, rfl⟩)
      · rw [Real.sSup_of_not_bddAbove hb]

mutual

/-- Arbitrary-triadic-cube form of the coarse Poincare engine.  The frozen
anchor only exports origin cubes, while the Section 5 cell localization uses
translated descendants.  Keeping this theorem public exposes the already
proved translation-covariant engine without duplicating it in the Section 5
support layer. -/
theorem coarsePoincareRaw {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : Ch02.TriadicCoeffFamily d)
    (haSymm : ∀ R, Ch02.CoeffOn.IsSymmetric (a.coeffOn R))
    (s : ℝ) (hs : 0 < s) (q : Ch02.MultiscaleExponent) (hq : q.IsAdmissible)
    (u : H1Function (openCubeSet Q)) (h : Vec d → Vec d)
    (hh : MemVectorL2 (openCubeSet Q) h)
    (hsol : IsSolenoidalOn (openCubeSet Q) h) :
    Ch03.scaleNormalizedNegativeBesovVectorNorm Q s q u.grad ≤
        Ch03.poincareDiscountFactor s q *
          Ch03.poincareLowerEllipticityFactor Q a s q *
            Real.sqrt (∫ x, vecDot (u.grad x)
              (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x))
              ∂normalizedCubeMeasure Q) ∧
      Ch03.scaleNormalizedNegativeBesovVectorNorm Q s q h ≤
        Ch03.poincareDiscountFactor s q *
          Ch03.poincareUpperEllipticityFactor Q a s q *
            Real.sqrt (∫ x, vecDot (h x)
              (matVecMul ((a.coeffOn Q).toCoeffField x)⁻¹ (h x))
              ∂normalizedCubeMeasure Q) := by
  let e0 : Vec d → ℝ := fun x =>
    vecDot (u.grad x) (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x))
  let f0 : Vec d → ℝ := fun x =>
    vecDot (h x) (matVecMul ((a.coeffOn Q).toCoeffField x)⁻¹ (h x))
  let energy : Vec d → ℝ := fun x => max 0 (e0 x)
  let invEnergy : Vec d → ℝ := fun x => max 0 (f0 x)
  have hsymCube :
      ∀ᵐ x ∂volume.restrict (cubeSet Q), (a.coeffOn Q).toCoeffField x |>.IsSymm := by
    simpa [volumeMeasureOn, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
      using! haSymm Q
  have hellCube :
      ∀ᵐ x ∂volume.restrict (cubeSet Q),
        IsEllipticMatrix (a.coeffOn Q).lam (a.coeffOn Q).Lam
          ((a.coeffOn Q).toCoeffField x) := by
    simpa [volumeMeasureOn, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
      using (a.coeffOn Q).aeElliptic
  have he0nonneg : ∀ᵐ x ∂volume.restrict (cubeSet Q), 0 ≤ e0 x := by
    filter_upwards [hsymCube, hellCube] with x hsymm hell
    have hlower := hell.2.2.1 (u.grad x)
    exact (mul_nonneg (a.coeffOn Q).lam_pos.le (vecNormSq_nonneg _)).trans hlower
  have hf0nonneg : ∀ᵐ x ∂volume.restrict (cubeSet Q), 0 ≤ f0 x := by
    filter_upwards [hsymCube, hellCube] with x hsymm hell
    have hinv := symmPart_inv_nonneg_of_isEllipticMatrix hell (h x)
    have hs : symmPart ((a.coeffOn Q).toCoeffField x) =
        (a.coeffOn Q).toCoeffField x := by
      ext i j
      have hij := (Matrix.IsSymm.ext_iff.mp hsymm) i j
      simp [symmPart, hij]
    simpa [f0, hs] using hinv
  have henergyAE : e0 =ᵐ[volume.restrict (cubeSet Q)] energy := by
    filter_upwards [he0nonneg] with x hx
    simp [energy, max_eq_right hx]
  have hinvEnergyAE : f0 =ᵐ[volume.restrict (cubeSet Q)] invEnergy := by
    filter_upwards [hf0nonneg] with x hx
    simp [invEnergy, max_eq_right hx]
  have huCube : MemVectorL2 (cubeSet Q) u.grad := by
    simpa [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using u.grad_memVectorL2
  have hhCube : MemVectorL2 (cubeSet Q) h := by
    simpa [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using hh
  have he0IntOpen := coefficientEnergyIntegrable (a.coeffOn Q) u
  have he0Int : IntegrableOn e0 (cubeSet Q) volume := by
    apply (integrableOn_cubeSet_iff_integrableOn_openCubeSet).2
    simpa [e0, Ch02.cubeDomain_coe] using he0IntOpen
  have hf0IntOpen := inverseCoefficientEnergyIntegrable (a.coeffOn Q) (haSymm Q) h hh
  have hf0Int : IntegrableOn f0 (cubeSet Q) volume := by
    apply (integrableOn_cubeSet_iff_integrableOn_openCubeSet).2
    simpa [f0, Ch02.cubeDomain_coe] using hf0IntOpen
  have henergyInt : IntegrableOn energy (cubeSet Q) volume := he0Int.congr henergyAE
  have hinvEnergyInt : IntegrableOn invEnergy (cubeSet Q) volume :=
    hf0Int.congr hinvEnergyAE
  have henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x := by
    intro x _hx
    exact le_max_left _ _
  have hinvEnergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ invEnergy x := by
    intro x _hx
    exact le_max_left _ _
  have hsolCube : IsSolenoidalOn (cubeSet Q) h :=
    isSolenoidalOn_cubeSet_triadicCube_of_openCubeSet hsol
  have hgradient_local : ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
      vecNormSq (cubeAverageVec R u.grad) ≤
        Ch02.coarseSigmaStarInvMatrixNorm R a * cubeAverage R energy := by
    intro j R hR
    let uR := u.restrictToOpenSubcube hR
    have hraw := arbitraryGradientAverageEnergyControl
      (Ch02.cubeDomain R) (a.coeffOn R) (haSymm R) uR
    have hcoeffOpen :
        (a.coeffOn R).toCoeffField =ᵐ[volumeMeasureOn (openCubeSet R)]
          (a.coeffOn Q).toCoeffField :=
      a.restrictsTo_of_subset (openCubeSet_subset_of_mem_descendantsAtDepth hR)
    have hcoeffCube :
        (a.coeffOn R).toCoeffField =ᵐ[volume.restrict (cubeSet R)]
          (a.coeffOn Q).toCoeffField := by
      simpa [volumeMeasureOn, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet R]
        using hcoeffOpen
    have hlocalEnergyAE :
        (fun x => vecDot (u.grad x)
          (matVecMul ((a.coeffOn R).toCoeffField x) (u.grad x)))
          =ᵐ[volume.restrict (cubeSet R)] energy := by
      have hmono : volume.restrict (cubeSet R) ≤ volume.restrict (cubeSet Q) :=
        Measure.restrict_mono_set volume (cubeSet_subset_of_mem_descendantsAtDepth hR)
      have hcoeffEnergyAE :
          (fun x => vecDot (u.grad x)
            (matVecMul ((a.coeffOn R).toCoeffField x) (u.grad x)))
            =ᵐ[volume.restrict (cubeSet R)] e0 :=
        hcoeffCube.mono fun x hx => by simp only [e0]; rw [hx]
      exact hcoeffEnergyAE.trans (henergyAE.filter_mono (ae_mono hmono))
    have havg :
        Ch02.average (Ch02.cubeDomain R)
            (fun x => vecDot (uR.grad x)
              (matVecMul ((a.coeffOn R).toCoeffField x) (uR.grad x))) =
          cubeAverage R energy := by
      rw [Ch05.Section53.JUpperBoundWeakNorms.ch02_average_cubeDomain_eq_cubeAverage]
      exact cubeAverage_eq_of_ae_eq_on_cubeSet (by simpa [uR] using hlocalEnergyAE)
    have havgVec : Ch02.averageVec (Ch02.cubeDomain R) u.grad =
        cubeAverageVec R u.grad := by
      funext i
      exact Ch05.Section53.JUpperBoundWeakNorms.ch02_average_cubeDomain_eq_cubeAverage
        R (fun x => u.grad x i)
    rw [show Ch02.h1AverageGradient (Ch02.cubeDomain R) uR =
        Ch02.averageVec (Ch02.cubeDomain R) u.grad by rfl, havgVec, havg] at hraw
    simpa [Ch02.coarseSigmaStarInvMatrixNorm] using hraw
  have hflux_local : ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
      vecNormSq (cubeAverageVec R h) ≤
        Ch02.coarseBMatrixNorm R a * cubeAverage R invEnergy := by
    intro j R hR
    have hsubset : cubeSet R ⊆ cubeSet Q := cubeSet_subset_of_mem_descendantsAtDepth hR
    have hhR : MemVectorL2 (cubeSet R) h :=
      hhCube.mono_measure (Measure.restrict_mono_set volume hsubset)
    have hsolR : IsSolenoidalOn (cubeSet R) h :=
      hsolCube.restrict_cubeSet_of_mem_descendantsAtDepth hR hhR
    have hhROpen : MemVectorL2 (openCubeSet R) h := by
      simpa [MemVectorL2, volumeMeasureOn,
        volume_restrict_cubeSet_eq_volume_restrict_openCubeSet R] using hhR
    have hsolROpen : IsSolenoidalOn (openCubeSet R) h :=
      isSolenoidalOn_openCubeSet_triadicCube_of_cubeSet hsolR
    have hraw := arbitrarySolenoidalAverageEnergyControl
      (Ch02.cubeDomain R) (a.coeffOn R) (haSymm R) h hhROpen hsolROpen
    have hcoeffOpen :
        (a.coeffOn R).toCoeffField =ᵐ[volumeMeasureOn (openCubeSet R)]
          (a.coeffOn Q).toCoeffField :=
      a.restrictsTo_of_subset (openCubeSet_subset_of_mem_descendantsAtDepth hR)
    have hcoeffCube :
        (a.coeffOn R).toCoeffField =ᵐ[volume.restrict (cubeSet R)]
          (a.coeffOn Q).toCoeffField := by
      simpa [volumeMeasureOn, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet R]
        using hcoeffOpen
    have hlocalEnergyAE :
        (fun x => vecDot (h x)
          (matVecMul ((a.coeffOn R).toCoeffField x)⁻¹ (h x)))
          =ᵐ[volume.restrict (cubeSet R)] invEnergy := by
      have hmono : volume.restrict (cubeSet R) ≤ volume.restrict (cubeSet Q) :=
        Measure.restrict_mono_set volume hsubset
      have hcoeffEnergyAE :
          (fun x => vecDot (h x)
            (matVecMul ((a.coeffOn R).toCoeffField x)⁻¹ (h x)))
            =ᵐ[volume.restrict (cubeSet R)] f0 :=
        hcoeffCube.mono fun x hx => by simp only [f0]; rw [hx]
      exact hcoeffEnergyAE.trans (hinvEnergyAE.filter_mono (ae_mono hmono))
    have havg :
        Ch02.average (Ch02.cubeDomain R)
            (fun x => vecDot (h x)
              (matVecMul ((a.coeffOn R).toCoeffField x)⁻¹ (h x))) =
          cubeAverage R invEnergy := by
      rw [Ch05.Section53.JUpperBoundWeakNorms.ch02_average_cubeDomain_eq_cubeAverage]
      exact cubeAverage_eq_of_ae_eq_on_cubeSet hlocalEnergyAE
    have havgVec : Ch02.averageVec (Ch02.cubeDomain R) h = cubeAverageVec R h := by
      funext i
      exact Ch05.Section53.JUpperBoundWeakNorms.ch02_average_cubeDomain_eq_cubeAverage
        R (fun x => h x i)
    rw [havgVec, havg] at hraw
    simpa [Ch02.coarseBMatrixNorm] using hraw
  have hgradient_depth : ∀ n : ℕ,
      Ch03.negativeBesovVectorDepthAverage Q u.grad n ≤
        Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a *
          cubeAverage Q energy := fun n =>
    Ch03.negativeBesovVectorDepthAverage_le_publicSigmaStarInvEnergy
      a u.grad energy henergy_nonneg henergyInt hgradient_local n
  have hflux_depth : ∀ n : ℕ,
      Ch03.negativeBesovVectorDepthAverage Q h n ≤
        Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a *
          cubeAverage Q invEnergy := fun n =>
    Ch03.negativeBesovVectorDepthAverage_le_publicBEnergy
      a h invEnergy hinvEnergy_nonneg hinvEnergyInt hflux_local n
  have henergyEq : cubeAverage Q energy = ∫ x, e0 x ∂normalizedCubeMeasure Q := by
    rw [← cubeAverage_eq_integral_normalizedCubeMeasure]
    exact (cubeAverage_eq_of_ae_eq_on_cubeSet henergyAE).symm
  have hinvEnergyEq : cubeAverage Q invEnergy = ∫ x, f0 x ∂normalizedCubeMeasure Q := by
    rw [← cubeAverage_eq_integral_normalizedCubeMeasure]
    exact (cubeAverage_eq_of_ae_eq_on_cubeSet hinvEnergyAE).symm
  constructor
  · cases q with
    | finite q =>
        have hq' : 1 ≤ q := by simpa using hq
        have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq'
        simpa [Ch03.poincareLowerEllipticityFactor, e0, henergyEq] using
          (Ch03.finite_gradient_norm_le_of_cubeAverageEnergyControl
            Q a s q hs hq' u.grad energy henergy_nonneg hgradient_depth
            (Ch03.summable_public_sigmaStar_series Q a hs hqpos)
            (Ch03.tsum_public_sigmaStar_series_eq_lambdaSq Q a hs hqpos))
    | infinity =>
        simpa [Ch03.poincareLowerEllipticityFactor, e0, henergyEq] using
          (Ch03.infinity_gradient_norm_le_of_cubeAverageEnergyControl
            Q a s hs u.grad energy henergy_nonneg hgradient_depth)
  · cases q with
    | finite q =>
        have hq' : 1 ≤ q := by simpa using hq
        have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq'
        simpa [Ch03.poincareUpperEllipticityFactor, f0, hinvEnergyEq] using
          (Ch03.finite_flux_norm_le_of_cubeAverageEnergyControl
            Q a s q hs hq' h invEnergy hinvEnergy_nonneg hflux_depth
            (Ch03.summable_public_B_series Q a hs hqpos)
            (Ch03.tsum_public_B_series_eq_LambdaSq Q a hs hqpos))
    | infinity =>
        simpa [Ch03.poincareUpperEllipticityFactor, f0, hinvEnergyEq] using
          (Ch03.infinity_flux_norm_le_of_cubeAverageEnergyControl
            Q a s hs h invEnergy hinvEnergy_nonneg hflux_depth)

private theorem arbitrarySolenoidalAverageEnergyControl {d : ℕ}
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) (hsym : a.IsSymmetric)
    (h : Vec d → Vec d) (hh : MemVectorL2 (U : Set (Vec d)) h)
    (hsol : IsSolenoidalOn (U : Set (Vec d)) h) :
    vecNormSq (Ch02.averageVec U h) ≤
      Ch02.matrixNorm (Ch02.bCoarse U a) *
        Ch02.average U
          (fun x => vecDot (h x) (matVecMul (a.toCoeffField x)⁻¹ (h x))) := by
  let theory := Ch02.responseSymmetricDirichletNeumannTheory U a hsym
  let avg : Vec d := Ch02.averageVec U h
  let B : Mat d := Ch02.bCoarse U a
  let p : Vec d := matVecMul B⁻¹ avg
  obtain ⟨v, hv⟩ := theory.dirichlet_minimizer_exists p
  have hBdet : IsUnit B.det :=
    (Matrix.isUnit_iff_isUnit_det (A := B)).mp (Ch02.bCoarse_posDef U a).isUnit
  have hBmul : ∀ ξ : Vec d, matVecMul B (matVecMul B⁻¹ ξ) = ξ := by
    intro ξ
    rw [matVecMul_mul, Matrix.mul_nonsing_inv B hBdet]
    funext i
    simp [matVecMul, Matrix.one_apply]
  have hBp : matVecMul B p = avg := by
    simpa [p] using hBmul avg
  have hBsig : B = Ch02.sigmaCoarse U a := by
    exact theory.derived_matrices.2.2
  have hminValue :
      Ch02.symmetricDirichletEnergyValue U a v =
        (1 / 2 : ℝ) * vecDot p (matVecMul B p) := by
    rw [← Homogenization.Internal.Ch02.BookCh02.symmetricDirichletNu_eq_of_minimizer hv,
      theory.dirichlet_value_by_sigma, ← hBsig]
  have henergyInt := coefficientEnergyIntegrable a v
  have hdirichletEnergy :
      Ch02.symmetricDirichletEnergyValue U a v =
        (1 / 2 : ℝ) * Ch02.average U
          (fun x => vecDot (v.grad x) (matVecMul (a.toCoeffField x) (v.grad x))) := by
    unfold Ch02.symmetricDirichletEnergyValue
    change volumeAverage (U : Set (Vec d))
        (fun x => 1 / 2 * vecDot (v.grad x) (matVecMul (a.toCoeffField x) (v.grad x))) =
      1 / 2 * volumeAverage (U : Set (Vec d))
        (fun x => vecDot (v.grad x) (matVecMul (a.toCoeffField x) (v.grad x)))
    rw [show (fun x => 1 / 2 * vecDot (v.grad x)
          (matVecMul (a.toCoeffField x) (v.grad x))) =
        (1 / 2 : ℝ) • fun x => vecDot (v.grad x)
          (matVecMul (a.toCoeffField x) (v.grad x)) by
        funext x; simp,
      volumeAverage_smul]
  have henergyEq :
      Ch02.average U
          (fun x => vecDot (v.grad x) (matVecMul (a.toCoeffField x) (v.grad x))) =
        vecDot avg (matVecMul B⁻¹ avg) := by
    rw [hdirichletEnergy] at hminValue
    have hpquad : vecDot p (matVecMul B p) = vecDot avg (matVecMul B⁻¹ avg) := by
      rw [hBp]
      simp [p, vecDot_comm]
    rw [hpquad] at hminValue
    linarith
  have hpot : IsPotentialZeroTraceOn (U : Set (Vec d)) (fun x => v.grad x - p) :=
    Homogenization.Internal.Ch02.BookCh02.isPotentialZeroTraceOn_of_potentialZeroTraceFieldOn
      hv.1
  
  -- test the solenoidal field against the zero-trace potential difference.
  have hzero : ∫ x in (U : Set (Vec d)), vecDot (h x) (v.grad x - p) = 0 := by
    obtain ⟨φ, hφ⟩ := hpot
    have hz := hsol φ
    rwa [hφ] at hz
  have hhGrad : IntegrableOn (fun x => vecDot (h x) (v.grad x))
      (U : Set (Vec d)) volume :=
    integrableOn_vecDot_of_memVectorL2 hh v.grad_memVectorL2
  have hhConst : IntegrableOn (fun x => vecDot (h x) p)
      (U : Set (Vec d)) volume :=
    (CorrectionFieldData.integrableOn_vecDot_const_left_of_memVectorL2 p hh).congr_fun
      (fun x _hx => vecDot_comm p (h x)) U.measurableSet
  have hpairIntegral :
      (∫ x in (U : Set (Vec d)), vecDot (h x) (v.grad x)) =
        ∫ x in (U : Set (Vec d)), vecDot (h x) p := by
    have hsplit :
        (∫ x in (U : Set (Vec d)), vecDot (h x) (v.grad x - p)) =
          (∫ x in (U : Set (Vec d)), vecDot (h x) (v.grad x)) -
            ∫ x in (U : Set (Vec d)), vecDot (h x) p := by
      rw [← integral_sub hhGrad hhConst]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp only [vecDot, Pi.sub_apply]
        calc
          ∑ i, h x i * (v.grad x i - p i) =
              ∑ i, (h x i * v.grad x i - h x i * p i) := by
                apply Finset.sum_congr rfl
                intro i _hi
                ring
          _ = (∑ i, h x i * v.grad x i) - ∑ i, h x i * p i := by
            rw [Finset.sum_sub_distrib]
    rw [hsplit] at hzero
    linarith
  have hhCoord : ∀ i, IntegrableOn (fun x => h x i) (U : Set (Vec d)) := by
    intro i
    exact CorrectionFieldData.integrableOn_coord_of_memVectorL2 hh i
  have hpair :
      Ch02.average U (fun x => vecDot (h x) (v.grad x)) = vecDot avg p := by
    have hright :
        volumeAverage (U : Set (Vec d)) (fun x => vecDot (h x) p) = vecDot avg p := by
      simpa [Ch02.averageVec, Ch02.average, avg] using!
        volumeAverage_vecDot_right (U := (U : Set (Vec d))) h p hhCoord
    have havgPair :
        volumeAverage (U : Set (Vec d)) (fun x => vecDot (h x) (v.grad x)) =
          volumeAverage (U : Set (Vec d)) (fun x => vecDot (h x) p) := by
      unfold volumeAverage
      rw [hpairIntegral]
    simpa [Ch02.average] using! havgPair.trans hright
  have hinvInt := inverseCoefficientEnergyIntegrable a hsym h hh
  have hyoung :
      ∀ᵐ x ∂volumeMeasureOn (U : Set (Vec d)),
        vecDot (h x) (v.grad x) ≤
          (1 / 2 : ℝ) * vecDot (v.grad x)
              (matVecMul (a.toCoeffField x) (v.grad x)) +
            (1 / 2 : ℝ) * vecDot (h x)
              (matVecMul (a.toCoeffField x)⁻¹ (h x)) := by
    filter_upwards [a.aeElliptic, hsym] with x hxEll hxSymm
    have hy := blockMatrixOfCoeff_half_quadratic_ge_vecDot_of_isEllipticMatrix
      hxEll (v.grad x) (h x)
    rw [blockMatrixOfCoeff_quadratic_eq] at hy
    have hs : symmPart (a.toCoeffField x) = a.toCoeffField x := by
      ext i j
      have hij : a.toCoeffField x j i = a.toCoeffField x i j :=
        (Matrix.IsSymm.ext_iff.mp hxSymm) i j
      simp [symmPart, hij]
    have hk : skewPart (a.toCoeffField x) = 0 := by
      ext i j
      have hij : a.toCoeffField x j i = a.toCoeffField x i j :=
        (Matrix.IsSymm.ext_iff.mp hxSymm) i j
      simp [skewPart, hij]
    rw [hs, hk] at hy
    have hz : matVecMul (0 : Mat d) (v.grad x) = 0 := by
      ext i
      simp [matVecMul]
    rw [hz, sub_zero] at hy
    rw [vecDot_comm (v.grad x) (h x)] at hy
    nlinarith
  have hrhsInt : IntegrableOn
      (fun x =>
        (1 / 2 : ℝ) * vecDot (v.grad x)
            (matVecMul (a.toCoeffField x) (v.grad x)) +
          (1 / 2 : ℝ) * vecDot (h x)
            (matVecMul (a.toCoeffField x)⁻¹ (h x)))
      (U : Set (Vec d)) volume :=
    (henergyInt.const_mul (1 / 2 : ℝ)).add (hinvInt.const_mul (1 / 2 : ℝ))
  have hint :
      (∫ x in (U : Set (Vec d)), vecDot (h x) (v.grad x)) ≤
        ∫ x in (U : Set (Vec d)),
          ((1 / 2 : ℝ) * vecDot (v.grad x)
              (matVecMul (a.toCoeffField x) (v.grad x)) +
            (1 / 2 : ℝ) * vecDot (h x)
              (matVecMul (a.toCoeffField x)⁻¹ (h x))) :=
    integral_mono_ae hhGrad hrhsInt hyoung
  have hvolNonneg : 0 ≤ (volume (U : Set (Vec d))).toReal⁻¹ := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hint hvolNonneg
  have hrhsIntegralEq :
      (∫ x in (U : Set (Vec d)),
          ((1 / 2 : ℝ) * vecDot (v.grad x)
              (matVecMul (a.toCoeffField x) (v.grad x)) +
            (1 / 2 : ℝ) * vecDot (h x)
              (matVecMul (a.toCoeffField x)⁻¹ (h x)))) =
        (1 / 2 : ℝ) * (∫ x in (U : Set (Vec d)),
          vecDot (v.grad x) (matVecMul (a.toCoeffField x) (v.grad x))) +
        (1 / 2 : ℝ) * (∫ x in (U : Set (Vec d)),
          vecDot (h x) (matVecMul (a.toCoeffField x)⁻¹ (h x))) := by
    rw [integral_add (henergyInt.const_mul (1 / 2 : ℝ))
        (hinvInt.const_mul (1 / 2 : ℝ)),
      integral_const_mul, integral_const_mul]
  have havgYoung :
      Ch02.average U (fun x => vecDot (h x) (v.grad x)) ≤
        (1 / 2 : ℝ) * Ch02.average U
            (fun x => vecDot (v.grad x) (matVecMul (a.toCoeffField x) (v.grad x))) +
          (1 / 2 : ℝ) * Ch02.average U
            (fun x => vecDot (h x) (matVecMul (a.toCoeffField x)⁻¹ (h x))) := by
    rw [hrhsIntegralEq] at hscaled
    unfold Ch02.average
    nlinarith
  have hquad :
      vecDot avg (matVecMul B⁻¹ avg) ≤
        Ch02.average U
          (fun x => vecDot (h x) (matVecMul (a.toCoeffField x)⁻¹ (h x))) := by
    rw [hpair, henergyEq] at havgYoung
    have havgp : vecDot avg p = vecDot avg (matVecMul B⁻¹ avg) := by rfl
    rw [havgp] at havgYoung
    linarith
  have hnorm :=
    Ch02.vecNormSq_le_matrixNorm_mul_vecDot_matVecMul_of_posSemidef_of_leftInverse
      (A := B⁻¹) (B := B) (Ch02.bCoarse_posDef U a).posSemidef hBmul avg
  exact hnorm.trans
    (mul_le_mul_of_nonneg_left hquad (Ch02.matrixNorm_nonneg _))

end

/-- Arbitrary translated-cube, finite-depth `q = 1` form of the coarse
Poincare estimate.  Section 5 pairs against finite positive Besov tests, so
it needs the individual partial sums rather than only their supremum. -/
theorem coarsePoincarePartialOneRaw {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : Ch02.TriadicCoeffFamily d)
    (haSymm : ∀ R, Ch02.CoeffOn.IsSymmetric (a.coeffOn R))
    (s : ℝ) (hs : 0 < s)
    (u : H1Function (openCubeSet Q)) (h : Vec d → Vec d)
    (hh : MemVectorL2 (openCubeSet Q) h)
    (hsol : IsSolenoidalOn (openCubeSet Q) h) (N : ℕ) :
    cubeBesovNegativeVectorPartialSeminorm Q s N u.grad ≤
        Ch03.poincareDiscountFactor s (.finite 1) *
          Ch03.poincareLowerEllipticityFactor Q a s (.finite 1) *
            Real.sqrt (∫ x, vecDot (u.grad x)
              (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x))
              ∂normalizedCubeMeasure Q) ∧
      cubeBesovNegativeVectorPartialSeminorm Q s N h ≤
        Ch03.poincareDiscountFactor s (.finite 1) *
          Ch03.poincareUpperEllipticityFactor Q a s (.finite 1) *
            Real.sqrt (∫ x, vecDot (h x)
              (matVecMul ((a.coeffOn Q).toCoeffField x)⁻¹ (h x))
              ∂normalizedCubeMeasure Q) := by
  have hraw := coarsePoincareRaw Q a haSymm s hs (.finite 1) (by simp) u h hh hsol
  have huNorm : MemLp u.grad (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet Q u.grad_memVectorL2
  have hhNorm : MemLp h (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet Q hh
  have huBdd : BddAbove (Set.range fun K : ℕ =>
      Ch03.negativeBesovVectorPartialNormFinite Q s 1 K u.grad) := by
    simpa [Ch03.negativeBesovVectorPartialNormFinite,
      cubeBesovNegativeVectorPartialSeminorm, Real.rpow_one,
      Ch03.negativeBesovVectorDepthSeminorm_eq_old] using!
      cubeBesovNegativeVectorPartialSeminorm_bddAbove_of_memLp Q hs u.grad huNorm
  have hhBdd : BddAbove (Set.range fun K : ℕ =>
      Ch03.negativeBesovVectorPartialNormFinite Q s 1 K h) := by
    simpa [Ch03.negativeBesovVectorPartialNormFinite,
      cubeBesovNegativeVectorPartialSeminorm, Real.rpow_one,
      Ch03.negativeBesovVectorDepthSeminorm_eq_old] using!
      cubeBesovNegativeVectorPartialSeminorm_bddAbove_of_memLp Q hs h hhNorm
  constructor
  · calc
      cubeBesovNegativeVectorPartialSeminorm Q s N u.grad =
          Ch03.negativeBesovVectorPartialNormFinite Q s 1 N u.grad := by
        simp [Ch03.negativeBesovVectorPartialNormFinite,
          cubeBesovNegativeVectorPartialSeminorm, Real.rpow_one,
          Ch03.negativeBesovVectorDepthSeminorm_eq_old]
      _ ≤ Ch03.scaleNormalizedNegativeBesovVectorNorm Q s (.finite 1) u.grad := by
        unfold Ch03.scaleNormalizedNegativeBesovVectorNorm
        exact le_csSup huBdd ⟨N, rfl⟩
      _ ≤ _ := hraw.1
  · calc
      cubeBesovNegativeVectorPartialSeminorm Q s N h =
          Ch03.negativeBesovVectorPartialNormFinite Q s 1 N h := by
        simp [Ch03.negativeBesovVectorPartialNormFinite,
          cubeBesovNegativeVectorPartialSeminorm, Real.rpow_one,
          Ch03.negativeBesovVectorDepthSeminorm_eq_old]
      _ ≤ Ch03.scaleNormalizedNegativeBesovVectorNorm Q s (.finite 1) h := by
        unfold Ch03.scaleNormalizedNegativeBesovVectorNorm
        exact le_csSup hhBdd ⟨N, rfl⟩
      _ ≤ _ := hraw.2

open SubdiffusiveProcess.CoarseGrainingVocab
  (paperScaleNormalizedNegativeBesovVectorNorm paperPoincareGeometricFactor
    lambda coefficientEnergyNorm Lambda inverseCoefficientEnergyNorm)

/-- The source-form coarse-grained Poincare inequalities for arbitrary `H¹` gradients and
solenoidal `L²` fields. -/
theorem coarse_grained_poincare {d : ℕ}
    (hd : 2 ≤ d)
    (a : Ch02.TriadicCoeffFamily d)
    (haSymm : ∀ Q, Ch02.CoeffOn.IsSymmetric (a.coeffOn Q)) :
    ∀ (s : ℝ), 0 < s → s ≤ 1 →
      ∀ q : Ch02.MultiscaleExponent, q.IsAdmissible →
        ∀ m : ℤ,
          ∀ u : Homogenization.H1Function
              (Homogenization.openCubeSet (Homogenization.originCube d m)),
            ∀ h : Vec d → Vec d,
              Homogenization.MemVectorL2
                (Homogenization.openCubeSet (Homogenization.originCube d m)) h →
              Homogenization.IsSolenoidalOn
                (Homogenization.openCubeSet (Homogenization.originCube d m)) h →
              paperScaleNormalizedNegativeBesovVectorNorm
                    (Homogenization.originCube d m) s q u.grad ≤
                  paperPoincareGeometricFactor s q *
                    Real.rpow (lambda (Homogenization.originCube d m) s q a) (-1 / 2) *
                      coefficientEnergyNorm (Homogenization.originCube d m) a u.grad ∧
                paperScaleNormalizedNegativeBesovVectorNorm
                    (Homogenization.originCube d m) s q h ≤
                  paperPoincareGeometricFactor s q *
                    Real.rpow (Lambda (Homogenization.originCube d m) s q a) (1 / 2) *
                      inverseCoefficientEnergyNorm
                        (Homogenization.originCube d m) a h := by
  intro s hs hs1 q hq m u h hh hsol
  have : NeZero d := ⟨by omega⟩
  let Q : TriadicCube d := originCube d m
  have hraw := coarsePoincareRaw Q a haSymm s hs q hq u h hh hsol
  cases q with
  | finite q =>
      have hq' : 1 ≤ q := by simpa using hq
      have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq'
      have hscale : Real.rpow s (1 / q) ≤ 1 :=
        Real.rpow_le_one hs.le hs1 (by positivity)
      have huNonneg := scaleNormalizedNegativeBesovVectorNorm_nonneg
        Q s (.finite q) u.grad
      have hhNonneg := scaleNormalizedNegativeBesovVectorNorm_nonneg
        Q s (.finite q) h
      constructor
      · calc
          SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
              Q s (.finite q) u.grad =
              Real.rpow s (1 / q) *
                Ch03.scaleNormalizedNegativeBesovVectorNorm Q s (.finite q) u.grad := rfl
          _ ≤ Ch03.scaleNormalizedNegativeBesovVectorNorm Q s (.finite q) u.grad := by
            simpa using mul_le_of_le_one_left huNonneg hscale
          _ ≤ Ch03.poincareDiscountFactor s (.finite q) *
                Ch03.poincareLowerEllipticityFactor Q a s (.finite q) *
                  Real.sqrt (∫ x, vecDot (u.grad x)
                    (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x))
                    ∂normalizedCubeMeasure Q) := hraw.1
          _ = SubdiffusiveProcess.CoarseGrainingVocab.paperPoincareGeometricFactor s (.finite q) *
                Real.rpow (SubdiffusiveProcess.CoarseGrainingVocab.lambda Q s (.finite q) a) (-1 / 2) *
                  SubdiffusiveProcess.CoarseGrainingVocab.coefficientEnergyNorm Q a u.grad := by
            have hdiscount : Ch03.poincareDiscountFactor s (.finite q) =
                SubdiffusiveProcess.CoarseGrainingVocab.paperPoincareGeometricFactor s (.finite q) := by
              unfold Ch03.poincareDiscountFactor
                SubdiffusiveProcess.CoarseGrainingVocab.paperPoincareGeometricFactor
              simp [one_div]
            have hlower : Ch03.poincareLowerEllipticityFactor Q a s (.finite q) =
                Real.rpow (SubdiffusiveProcess.CoarseGrainingVocab.lambda Q s (.finite q) a)
                  (-1 / 2) := by
              unfold Ch03.poincareLowerEllipticityFactor
              rw [show (-(1 / 2 : ℝ)) = (-1 / 2 : ℝ) by ring]
            rw [hdiscount, hlower]
            rfl
      · calc
          SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
              Q s (.finite q) h =
              Real.rpow s (1 / q) *
                Ch03.scaleNormalizedNegativeBesovVectorNorm Q s (.finite q) h := rfl
          _ ≤ Ch03.scaleNormalizedNegativeBesovVectorNorm Q s (.finite q) h := by
            simpa using mul_le_of_le_one_left hhNonneg hscale
          _ ≤ Ch03.poincareDiscountFactor s (.finite q) *
                Ch03.poincareUpperEllipticityFactor Q a s (.finite q) *
                  Real.sqrt (∫ x, vecDot (h x)
                    (matVecMul ((a.coeffOn Q).toCoeffField x)⁻¹ (h x))
                    ∂normalizedCubeMeasure Q) := hraw.2
          _ = SubdiffusiveProcess.CoarseGrainingVocab.paperPoincareGeometricFactor s (.finite q) *
                Real.rpow (SubdiffusiveProcess.CoarseGrainingVocab.Lambda Q s (.finite q) a) (1 / 2) *
                  SubdiffusiveProcess.CoarseGrainingVocab.inverseCoefficientEnergyNorm Q a h := by
            simp [SubdiffusiveProcess.CoarseGrainingVocab.paperPoincareGeometricFactor,
              SubdiffusiveProcess.CoarseGrainingVocab.inverseCoefficientEnergyNorm,
              Ch03.poincareDiscountFactor, Ch03.poincareUpperEllipticityFactor]
  | infinity =>
      unfold Ch03.poincareDiscountFactor Ch03.poincareLowerEllipticityFactor
        Ch03.poincareUpperEllipticityFactor at hraw
      rw [show (-(1 / 2 : ℝ)) = (-1 / 2 : ℝ) by ring] at hraw
      simpa [Q, SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm,
        SubdiffusiveProcess.CoarseGrainingVocab.paperPoincareGeometricFactor,
        SubdiffusiveProcess.CoarseGrainingVocab.coefficientEnergyNorm,
        SubdiffusiveProcess.CoarseGrainingVocab.inverseCoefficientEnergyNorm] using hraw

end

end SubdiffusiveProcess.Providers.Section2
