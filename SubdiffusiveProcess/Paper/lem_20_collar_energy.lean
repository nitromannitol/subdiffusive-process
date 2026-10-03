module

public import SubdiffusiveProcess.Paper.lem_20_product
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Sobolev.ResponseSpace
public import SubdiffusiveProcess.Sobolev.GradientEnergyMeasure
public import SubdiffusiveProcess.Paper.lem_cutoffs
public import SubdiffusiveProcess.Paper.lem_20_collar_amplitude

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal

namespace Paper




lemma aux_lem_20_collar_energy_pointwise_all_radii
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z R hR))
    (hS : S.space = killedSobolevGraph (centeredCube z R hR))
    (a : PositiveCoefficient (centeredCube z R hR))
    (u chi prod : S.space) (uc : SpatialCoordinates d → ℝ)
    (hgrad : ∀ i : Fin d, (prod.val.2 i : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
        (fun x => (1 - (chi.val.1 : SpatialCoordinates d → ℝ) x) *
          (u.val.2 i : SpatialCoordinates d → ℝ) x -
            uc x * (chi.val.2 i : SpatialCoordinates d → ℝ) x))
    (hchi : ∀ᵐ x ∂(volume.restrict
        (centeredCube z R hR : Set (SpatialCoordinates d))),
      0 ≤ (chi.val.1 : SpatialCoordinates d → ℝ) x ∧
        (chi.val.1 : SpatialCoordinates d → ℝ) x ≤ 1)
    (hchi_one : ∀ᵐ x ∂(volume.restrict
        (centeredCube z R hR : Set (SpatialCoordinates d))),
      3 * r ≤ Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
        (chi.val.1 : SpatialCoordinates d → ℝ) x = 1)
    (hchi_grad : ∀ i : Fin d, ∀ᵐ x ∂(volume.restrict
        (centeredCube z R hR : Set (SpatialCoordinates d))),
      3 * r < Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
        (chi.val.2 i : SpatialCoordinates d → ℝ) x = 0)
    (M : ℝ) (hM : 0 ≤ M)
    (hcollar : ∀ x : SpatialCoordinates d,
      x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) →
      Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ 3 * r →
      |uc x| ≤ M)
    (i : Fin d) (x : SpatialCoordinates d)
    (hxO : x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hpi : (prod.val.2 i : SpatialCoordinates d → ℝ) x =
      (1 - (chi.val.1 : SpatialCoordinates d → ℝ) x) *
        (u.val.2 i : SpatialCoordinates d → ℝ) x -
          uc x * (chi.val.2 i : SpatialCoordinates d → ℝ) x)
    (hcx : 0 ≤ (chi.val.1 : SpatialCoordinates d → ℝ) x ∧
      (chi.val.1 : SpatialCoordinates d → ℝ) x ≤ 1)
    (hcone : 3 * r ≤ Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
      (chi.val.1 : SpatialCoordinates d → ℝ) x = 1)
    (hcg : 3 * r < Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
      (chi.val.2 i : SpatialCoordinates d → ℝ) x = 0)
    (hax : 0 ≤ a.val x)
    (hxC : x ∈ {x | x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
      Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ 3 * r}) :
    a.val x * ((prod.val.2 i : SpatialCoordinates d → ℝ) x) ^ 2 ≤
      a.val x * (2 * ((u.val.2 i : SpatialCoordinates d → ℝ) x) ^ 2 +
        2 * M ^ 2 * ((chi.val.2 i : SpatialCoordinates d → ℝ) x) ^ 2) := by
  rcases hcx with ⟨hcx0, hcx1⟩
  have hcoef : (1 - (chi.val.1 : SpatialCoordinates d → ℝ) x) ^ 2 ≤ (1 : ℝ) ^ 2 := by
    apply sq_le_sq'
    · linarith
    · linarith
  have hucsq : (uc x) ^ 2 ≤ M ^ 2 := by
    have hbound := hcollar x hxO hxC.2
    apply sq_le_sq'
    · exact (abs_le.mp hbound).1
    · exact (abs_le.mp hbound).2
  have hfirst :
      ((1 - (chi.val.1 : SpatialCoordinates d → ℝ) x) *
          (u.val.2 i : SpatialCoordinates d → ℝ) x) ^ 2 ≤
        ((u.val.2 i : SpatialCoordinates d → ℝ) x) ^ 2 := by
    calc
      _ = (1 - (chi.val.1 : SpatialCoordinates d → ℝ) x) ^ 2 *
          ((u.val.2 i : SpatialCoordinates d → ℝ) x) ^ 2 := by ring
      _ ≤ (1 : ℝ) ^ 2 * ((u.val.2 i : SpatialCoordinates d → ℝ) x) ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
      _ = _ := by ring
  have hsecond :
      (uc x * (chi.val.2 i : SpatialCoordinates d → ℝ) x) ^ 2 ≤
        M ^ 2 * ((chi.val.2 i : SpatialCoordinates d → ℝ) x) ^ 2 := by
    calc
      _ = (uc x) ^ 2 * ((chi.val.2 i : SpatialCoordinates d → ℝ) x) ^ 2 := by ring
      _ ≤ M ^ 2 * ((chi.val.2 i : SpatialCoordinates d → ℝ) x) ^ 2 :=
        mul_le_mul_of_nonneg_right hucsq (sq_nonneg _)
  have hsq :
      ((1 - (chi.val.1 : SpatialCoordinates d → ℝ) x) *
          (u.val.2 i : SpatialCoordinates d → ℝ) x -
        uc x * (chi.val.2 i : SpatialCoordinates d → ℝ) x) ^ 2 ≤
        2 * ((u.val.2 i : SpatialCoordinates d → ℝ) x) ^ 2 +
          2 * M ^ 2 * ((chi.val.2 i : SpatialCoordinates d → ℝ) x) ^ 2 := by
    have h_nonneg_sq : 0 ≤ ((1 - (chi.val.1 : SpatialCoordinates d → ℝ) x) *
        (u.val.2 i : SpatialCoordinates d → ℝ) x +
        uc x * (chi.val.2 i : SpatialCoordinates d → ℝ) x) ^ 2 := sq_nonneg _
    nlinarith
  rw [hpi]
  calc
    a.val x * (((1 - (chi.val.1 : SpatialCoordinates d → ℝ) x) *
        (u.val.2 i : SpatialCoordinates d → ℝ) x -
        uc x * (chi.val.2 i : SpatialCoordinates d → ℝ) x) ^ 2) ≤
        a.val x * (2 * ((u.val.2 i : SpatialCoordinates d → ℝ) x) ^ 2 +
          2 * M ^ 2 * ((chi.val.2 i : SpatialCoordinates d → ℝ) x) ^ 2) :=
      mul_le_mul_of_nonneg_left hsq hax
    _ = a.val x * (2 * ((u.val.2 i : SpatialCoordinates d → ℝ) x) ^ 2 +
        2 * M ^ 2 * ((chi.val.2 i : SpatialCoordinates d → ℝ) x) ^ 2) := rfl

lemma aux_lem_20_collar_energy_pointwise
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (r : ℝ) (hr : 0 < r) (hr_upper : r ≤ 1)
    (S : ResponseSpace (centeredCube z R hR))
    (hS : S.space = killedSobolevGraph (centeredCube z R hR))
    (a : PositiveCoefficient (centeredCube z R hR))
    (u chi prod : S.space) (uc : SpatialCoordinates d → ℝ)
    (hgrad : ∀ i : Fin d, (prod.val.2 i : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
        (fun x => (1 - (chi.val.1 : SpatialCoordinates d → ℝ) x) *
          (u.val.2 i : SpatialCoordinates d → ℝ) x -
            uc x * (chi.val.2 i : SpatialCoordinates d → ℝ) x))
    (hchi : ∀ᵐ x ∂(volume.restrict
        (centeredCube z R hR : Set (SpatialCoordinates d))),
      0 ≤ (chi.val.1 : SpatialCoordinates d → ℝ) x ∧
        (chi.val.1 : SpatialCoordinates d → ℝ) x ≤ 1)
    (hchi_one : ∀ᵐ x ∂(volume.restrict
        (centeredCube z R hR : Set (SpatialCoordinates d))),
      3 * r ≤ Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
        (chi.val.1 : SpatialCoordinates d → ℝ) x = 1)
    (hchi_grad : ∀ i : Fin d, ∀ᵐ x ∂(volume.restrict
        (centeredCube z R hR : Set (SpatialCoordinates d))),
      3 * r < Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
        (chi.val.2 i : SpatialCoordinates d → ℝ) x = 0)
    (M : ℝ) (hM : 0 ≤ M)
    (hcollar : ∀ x : SpatialCoordinates d,
      x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) →
      Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ 3 * r →
      |uc x| ≤ M)
    (i : Fin d) (x : SpatialCoordinates d)
    (hxO : x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hpi : (prod.val.2 i : SpatialCoordinates d → ℝ) x =
      (1 - (chi.val.1 : SpatialCoordinates d → ℝ) x) *
        (u.val.2 i : SpatialCoordinates d → ℝ) x -
          uc x * (chi.val.2 i : SpatialCoordinates d → ℝ) x)
    (hcx : 0 ≤ (chi.val.1 : SpatialCoordinates d → ℝ) x ∧
      (chi.val.1 : SpatialCoordinates d → ℝ) x ≤ 1)
    (hcone : 3 * r ≤ Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
      (chi.val.1 : SpatialCoordinates d → ℝ) x = 1)
    (hcg : 3 * r < Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
      (chi.val.2 i : SpatialCoordinates d → ℝ) x = 0)
    (hax : 0 ≤ a.val x)
    (hxC : x ∈ {x | x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
      Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ 3 * r}) :
    a.val x * ((prod.val.2 i : SpatialCoordinates d → ℝ) x) ^ 2 ≤
      a.val x * (2 * ((u.val.2 i : SpatialCoordinates d → ℝ) x) ^ 2 +
        2 * M ^ 2 * ((chi.val.2 i : SpatialCoordinates d → ℝ) x) ^ 2) := by
  exact aux_lem_20_collar_energy_pointwise_all_radii d hd z R hR r hr S hS a u chi prod uc
    hgrad hchi hchi_one hchi_grad M hM hcollar i x hxO hpi hcx hcone hcg hax hxC

/- The existing argument works for every positive collar radius. -/
theorem aux_lem_20_collar_energy_all_radii
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (hS : S.space = killedSobolevGraph (centeredCube z R hR))
    (a : PositiveCoefficient (centeredCube z R hR))
    (u chi prod : S.space) (uc : SpatialCoordinates d → ℝ)
    (huc : (u.val.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] uc)
    (hprod : (prod.val.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
        (fun x => uc x * (1 - (chi.val.1 : SpatialCoordinates d → ℝ) x)))
    (hgrad : ∀ i : Fin d, (prod.val.2 i : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
        (fun x => (1 - (chi.val.1 : SpatialCoordinates d → ℝ) x) *
          (u.val.2 i : SpatialCoordinates d → ℝ) x -
            uc x * (chi.val.2 i : SpatialCoordinates d → ℝ) x))
    (r : ℝ) (hr : 0 < r)
    (hchi : ∀ᵐ x ∂(volume.restrict
        (centeredCube z R hR : Set (SpatialCoordinates d))),
      0 ≤ (chi.val.1 : SpatialCoordinates d → ℝ) x ∧
        (chi.val.1 : SpatialCoordinates d → ℝ) x ≤ 1)
    (hchi_one : ∀ᵐ x ∂(volume.restrict
        (centeredCube z R hR : Set (SpatialCoordinates d))),
      3 * r ≤ Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
        (chi.val.1 : SpatialCoordinates d → ℝ) x = 1)
    (hchi_grad : ∀ i : Fin d, ∀ᵐ x ∂(volume.restrict
        (centeredCube z R hR : Set (SpatialCoordinates d))),
      3 * r < Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
        (chi.val.2 i : SpatialCoordinates d → ℝ) x = 0)
    (M : ℝ) (hM : 0 ≤ M)
    (hcollar : ∀ x : SpatialCoordinates d,
      x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) →
      Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ 3 * r →
      |uc x| ≤ M) :
    responseForm S a prod prod ≤
      2 * (((volume.restrict
        (centeredCube z R hR : Set (SpatialCoordinates d))).withDensity
          (fun y => ENNReal.ofReal (a.val y *
            ∑ i : Fin d, (u.val.2 i y) ^ 2)))
        {x : SpatialCoordinates d | x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
          Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ 3 * r}).toReal +
      2 * M ^ 2 * responseForm S a chi chi := by
  let C : Set (SpatialCoordinates d) :=
    {x | x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
      Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ 3 * r}
  have hC : MeasurableSet C := by
    dsimp [C]
    exact (centeredCube z R hR).isOpen.measurableSet.inter
      (measurableSet_le measurable_infDist measurable_const)
  have hlocal :
      responseForm S a prod prod ≤
        2 * localGradientEnergy a hC
            (sobolevGradient (u : SobolevData (centeredCube z R hR))) +
          2 * M ^ 2 * responseForm S a chi chi := by
    rw [responseForm_apply S a prod prod,
      localGradientEnergy_eq_integral a hC
        (sobolevGradient (u : SobolevData (centeredCube z R hR))),
      responseForm_apply S a chi chi]
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    have hP : Integrable
        (fun x => a.val x * (prod.val.2 i x) ^ 2)
        (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))) := by
      simpa only [pow_two] using!
        (integrable_weighted_coordinates a.val
          (subspaceGradient S.space prod) (subspaceGradient S.space prod) i)
    have hU : Integrable
        (fun x => a.val x * (u.val.2 i x) ^ 2)
        (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))) := by
      simpa only [pow_two] using!
        (integrable_weighted_coordinates a.val
          (subspaceGradient S.space u) (subspaceGradient S.space u) i)
    have hChi : Integrable
        (fun x => a.val x * (chi.val.2 i x) ^ 2)
        (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))) := by
      simpa only [pow_two] using!
        (integrable_weighted_coordinates a.val
          (subspaceGradient S.space chi) (subspaceGradient S.space chi) i)
    have hpoint :
        (fun x => a.val x * (prod.val.2 i x) ^ 2) ≤ᵐ[
          volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
          (fun x =>
            2 * C.indicator (fun y => a.val y * (u.val.2 i y) ^ 2) x +
              2 * M ^ 2 * (a.val x * (chi.val.2 i x) ^ 2)) := by
      filter_upwards [ae_restrict_mem (centeredCube z R hR).isOpen.measurableSet,
        hgrad i, hchi, hchi_one, hchi_grad i,
        positiveCoefficient_ae_nonneg a] with x hxO hpi hcx hcone hcg hax
      by_cases hxC : x ∈ C
      · rw [Set.indicator_of_mem hxC]
        have h := aux_lem_20_collar_energy_pointwise_all_radii d hd z R hR r hr
          S hS a u chi prod uc hgrad hchi hchi_one hchi_grad M hM hcollar
          i x hxO hpi hcx hcone hcg hax hxC
        have hRHS : a.val x * (2 * ((u.val.2 i : SpatialCoordinates d → ℝ) x) ^ 2 +
            2 * M ^ 2 * ((chi.val.2 i : SpatialCoordinates d → ℝ) x) ^ 2) =
            2 * (a.val x * ((u.val.2 i : SpatialCoordinates d → ℝ) x) ^ 2) +
            2 * M ^ 2 * (a.val x * ((chi.val.2 i : SpatialCoordinates d → ℝ) x) ^ 2) := by ring
        rw [hRHS] at h
        exact h
      · have hdist : 3 * r < Metric.infDist x
            (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ := by
          exact lt_of_not_ge (fun h => hxC ⟨hxO, h⟩)
        have hchi_one_x := hcone (le_of_lt hdist)
        have hchi_grad_x := hcg hdist
        rw [Set.indicator_of_notMem hxC, hpi, hchi_one_x, hchi_grad_x]
        simp
    have hright : Integrable
        (fun x =>
          2 * C.indicator (fun y => a.val y * (u.val.2 i y) ^ 2) x +
            2 * M ^ 2 * (a.val x * (chi.val.2 i x) ^ 2))
        (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))) := by
      exact (hU.indicator hC).const_mul 2 |>.add (hChi.const_mul (2 * M ^ 2))
    have hi := integral_mono_ae hP hright hpoint
    rw [integral_add ((hU.indicator hC).const_mul 2)
      (hChi.const_mul (2 * M ^ 2)), integral_const_mul,
      integral_const_mul, integral_indicator hC] at hi
    simpa only [pow_two] using! hi
  have henergy := gradientEnergy_withDensity_finite_and_real a
    (sobolevGradient (u : SobolevData (centeredCube z R hR)))
  have henergyC := henergy.2 C hC
  have henergyC' :
      (((volume.restrict
          (centeredCube z R hR : Set (SpatialCoordinates d))).withDensity
            (fun y => ENNReal.ofReal (a.val y *
              ∑ i : Fin d, (u.val.2 i y) ^ 2))) C).toReal =
        localGradientEnergy a hC
          (sobolevGradient (u : SobolevData (centeredCube z R hR))) := by
    simpa only [Finset.mul_sum] using! henergyC
  have hlocal' :
      responseForm S a prod prod ≤
        2 * (((volume.restrict
          (centeredCube z R hR : Set (SpatialCoordinates d))).withDensity
            (fun y => ENNReal.ofReal (a.val y *
              ∑ i : Fin d, (u.val.2 i y) ^ 2))) C).toReal +
          2 * M ^ 2 * responseForm S a chi chi := by
    calc
      responseForm S a prod prod ≤
          2 * localGradientEnergy a hC
              (sobolevGradient (u : SobolevData (centeredCube z R hR))) +
            2 * M ^ 2 * responseForm S a chi chi := hlocal
      _ = 2 * (((volume.restrict
          (centeredCube z R hR : Set (SpatialCoordinates d))).withDensity
            (fun y => ENNReal.ofReal (a.val y *
              ∑ i : Fin d, (u.val.2 i y) ^ 2))) C).toReal +
            2 * M ^ 2 * responseForm S a chi chi := by
        exact congrArg
          (fun t : ℝ => 2 * t + 2 * M ^ 2 * responseForm S a chi chi)
          henergyC'.symm
  simpa only [C] using hlocal'

theorem lem_20_collar_energy
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (hS : S.space = killedSobolevGraph (centeredCube z R hR))
    (a : PositiveCoefficient (centeredCube z R hR))
    (u chi prod : S.space) (uc : SpatialCoordinates d → ℝ)
    (huc : (u.val.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] uc)
    (hprod : (prod.val.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
        (fun x => uc x * (1 - (chi.val.1 : SpatialCoordinates d → ℝ) x)))
    (hgrad : ∀ i : Fin d, (prod.val.2 i : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
        (fun x => (1 - (chi.val.1 : SpatialCoordinates d → ℝ) x) *
          (u.val.2 i : SpatialCoordinates d → ℝ) x -
            uc x * (chi.val.2 i : SpatialCoordinates d → ℝ) x))
    (r : ℝ) (hr : 0 < r) (hr_upper : r ≤ 1)
    (hchi : ∀ᵐ x ∂(volume.restrict
        (centeredCube z R hR : Set (SpatialCoordinates d))),
      0 ≤ (chi.val.1 : SpatialCoordinates d → ℝ) x ∧
        (chi.val.1 : SpatialCoordinates d → ℝ) x ≤ 1)
    (hchi_one : ∀ᵐ x ∂(volume.restrict
        (centeredCube z R hR : Set (SpatialCoordinates d))),
      3 * r ≤ Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
        (chi.val.1 : SpatialCoordinates d → ℝ) x = 1)
    (hchi_grad : ∀ i : Fin d, ∀ᵐ x ∂(volume.restrict
        (centeredCube z R hR : Set (SpatialCoordinates d))),
      3 * r < Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
        (chi.val.2 i : SpatialCoordinates d → ℝ) x = 0)
    (M : ℝ) (hM : 0 ≤ M)
    (hcollar : ∀ x : SpatialCoordinates d,
      x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) →
      Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ 3 * r →
      |uc x| ≤ M) :
    responseForm S a prod prod ≤
      2 * (((volume.restrict
        (centeredCube z R hR : Set (SpatialCoordinates d))).withDensity
          (fun y => ENNReal.ofReal (a.val y *
            ∑ i : Fin d, (u.val.2 i y) ^ 2)))
        {x : SpatialCoordinates d | x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
          Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ 3 * r}).toReal +
      2 * M ^ 2 * responseForm S a chi chi := by
  exact aux_lem_20_collar_energy_all_radii d hd z R hR S hS a u chi prod uc huc hprod hgrad
    r hr hchi hchi_one hchi_grad M hM hcollar

end Paper
