import SubdiffusiveProcess.Geometry.Cube
import SubdiffusiveProcess.Sobolev.PotentialPerturbation
import SubdiffusiveProcess.Sobolev.PotentialResponses
import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Lane2.LimitForm
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal

namespace Paper



theorem cor_14_form_comparison :
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
        (∀ (u ug : DomainL2 Q), u ∈ E.domain → ug ∈ Eg.domain → ug - u ∈ V0 →
          (∀ v ∈ E.domain, v - u ∈ V0 →
            (Gamma.measure u q).toReal ≤ (Gamma.measure v q).toReal) →
          (∀ v ∈ Eg.domain, v - u ∈ V0 →
            (Gammag.measure ug q).toReal ≤ (Gammag.measure v q).toReal) →
          Real.exp (-S) * (Gamma.measure u q).toReal ≤
              (Gammag.measure ug q).toReal ∧
            (Gammag.measure ug q).toReal ≤
              Real.exp S * (Gamma.measure u q).toReal) ∧
        (∀ (f : DomainL2 Q) (u ug : DomainL2 Q), u ∈ V0 → ug ∈ V0 →
          (∀ v ∈ V0, DirichletForm.signedIntegralOn (Gamma.cross u v)
              (q : Set (SpatialCoordinates d)) (fun _ => (1 : ℝ)) = inner ℝ f v) →
          (∀ v ∈ V0, DirichletForm.signedIntegralOn (Gammag.cross ug v)
              (q : Set (SpatialCoordinates d)) (fun _ => (1 : ℝ)) = inner ℝ f v) →
            Real.exp (-S) * inner ℝ f u ≤ inner ℝ f ug ∧
            inner ℝ f ug ≤ Real.exp S * inner ℝ f u))) := by
  intro d Q z r hr
  dsimp only
  intro hQ E Eg Gamma Gammag hdom V0 hkill g hg B hB hBq hgB S hS hSbdd hmeasure
  have hqmeas : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen.measurableSet
  have hweight : ∀ (v : DomainL2 Q), v ∈ E.domain →
      Real.exp (-S) * (Gamma.measure v (centeredCube z r hr)).toReal ≤
          (Gammag.measure v (centeredCube z r hr)).toReal ∧
        (Gammag.measure v (centeredCube z r hr)).toReal ≤
          Real.exp S * (Gamma.measure v (centeredCube z r hr)).toReal := by
    intro v hv
    have hvEg : v ∈ Eg.domain := by
      rw [hdom]
      exact hv
    have habs : ∀ x, |g x| ≤ S := by
      intro x
      exact hS.1 ⟨x, rfl⟩
    have hlow : ENNReal.ofReal (Real.exp (-S)) *
          Gamma.measure v (centeredCube z r hr) ≤
          Gammag.measure v (centeredCube z r hr) := by
      rw [hmeasure v hv _ hqmeas]
      calc
        ENNReal.ofReal (Real.exp (-S)) * Gamma.measure v
              (centeredCube z r hr) =
            ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
              ENNReal.ofReal (Real.exp (-S)) ∂(Gamma.measure v) := by
                simp [MeasureTheory.lintegral_const]
        _ ≤ ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
              ENNReal.ofReal (Real.exp (g x)) ∂(Gamma.measure v) := by
                apply MeasureTheory.lintegral_mono
                intro x
                exact ENNReal.ofReal_le_ofReal
                  ((Real.exp_le_exp).2 ((abs_le.mp (habs x)).1))
    have hhigh : Gammag.measure v (centeredCube z r hr) ≤
          ENNReal.ofReal (Real.exp S) *
            Gamma.measure v (centeredCube z r hr) := by
      rw [hmeasure v hv _ hqmeas]
      calc
        ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
              ENNReal.ofReal (Real.exp (g x)) ∂(Gamma.measure v) ≤
            ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
              ENNReal.ofReal (Real.exp S) ∂(Gamma.measure v) := by
                apply MeasureTheory.lintegral_mono
                intro x
                exact ENNReal.ofReal_le_ofReal
                  ((Real.exp_le_exp).2 ((abs_le.mp (habs x)).2))
        _ = ENNReal.ofReal (Real.exp S) *
              Gamma.measure v (centeredCube z r hr) := by
                simp [MeasureTheory.lintegral_const]
    constructor
    · calc
        Real.exp (-S) * (Gamma.measure v (centeredCube z r hr)).toReal =
            (ENNReal.ofReal (Real.exp (-S)) *
              Gamma.measure v (centeredCube z r hr)).toReal := by
                rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _))]
        _ ≤ (Gammag.measure v (centeredCube z r hr)).toReal :=
          ENNReal.toReal_mono (Gammag.measure_ne_top hvEg _) hlow
    · calc
        (Gammag.measure v (centeredCube z r hr)).toReal ≤
            (ENNReal.ofReal (Real.exp S) *
              Gamma.measure v (centeredCube z r hr)).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (Gamma.measure_ne_top hv (centeredCube z r hr))) hhigh
        _ = Real.exp S * (Gamma.measure v (centeredCube z r hr)).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _))]
  have hdiag : ∀ (v : DomainL2 Q), v ∈ E.domain →
      Real.exp (-S) * Gamma.cross v v (centeredCube z r hr) ≤
          Gammag.cross v v (centeredCube z r hr) ∧
        Gammag.cross v v (centeredCube z r hr) ≤
          Real.exp S * Gamma.cross v v (centeredCube z r hr) := by
    intro v hv
    have hvEg : v ∈ Eg.domain := by
      rw [hdom]
      exact hv
    simpa only [Gamma.cross_self v hv _ hqmeas,
      Gammag.cross_self v hvEg _ hqmeas] using hweight v hv
  constructor
  · intro u ug hu hug hdiff hmin hming
    have huEg : u ∈ Eg.domain := by
      rw [hdom]
      exact hu
    have hugE : ug ∈ E.domain := by
      rw [← hdom]
      exact hug
    have hmin' : (Gamma.measure u (centeredCube z r hr)).toReal ≤
        (Gamma.measure ug (centeredCube z r hr)).toReal :=
      hmin ug hugE hdiff
    have hming' : (Gammag.measure ug (centeredCube z r hr)).toReal ≤
        (Gammag.measure u (centeredCube z r hr)).toReal := by
      have := hming u huEg (by simpa using (V0.zero_mem))
      exact this
    constructor
    · calc
        Real.exp (-S) * (Gamma.measure u (centeredCube z r hr)).toReal ≤
            Real.exp (-S) * (Gamma.measure ug (centeredCube z r hr)).toReal :=
          mul_le_mul_of_nonneg_left hmin' (Real.exp_pos _).le
        _ ≤ (Gammag.measure ug (centeredCube z r hr)).toReal :=
          (hweight ug hugE).1
    · calc
        (Gammag.measure ug (centeredCube z r hr)).toReal ≤
            (Gammag.measure u (centeredCube z r hr)).toReal := hming'
        _ ≤ Real.exp S * (Gamma.measure u (centeredCube z r hr)).toReal :=
          (hweight u hu).2
  · intro f u ug huV hugV he he_g
    have huE : u ∈ E.domain := hkill.le_domain huV
    have hugE : ug ∈ E.domain := hkill.le_domain hugV
    have huEg : u ∈ Eg.domain := by
      rw [hdom]
      exact huE
    have hugEg : ug ∈ Eg.domain := by
      rw [hdom]
      exact hugE
    have ha : 0 < Real.exp (-S) := Real.exp_pos _
    have hb : 0 < Real.exp S := Real.exp_pos _
    have hab : Real.exp (-S) * Real.exp S = 1 := by
      rw [← Real.exp_add]
      simp
    have hsigned : ∀ (ν : SignedMeasure (SpatialCoordinates d))
        (A : Set (SpatialCoordinates d)), MeasurableSet A →
        DirichletForm.signedIntegralOn ν A (fun _ => (1 : ℝ)) = ν A := by
      intro ν A hA
      have hnu := congrArg (fun s : SignedMeasure (SpatialCoordinates d) => s A)
        (SignedMeasure.toSignedMeasure_toJordanDecomposition ν)
      have hnu2 : ν.toJordanDecomposition.toSignedMeasure A = ν A := hnu
      simp only [DirichletForm.signedIntegralOn, integral_const, measureReal_def]
      simp only [Measure.restrict_apply_univ]
      rw [← hnu2]
      rw [JordanDecomposition.toSignedMeasure, VectorMeasure.sub_apply,
        Measure.toSignedMeasure_apply_measurable hA,
        Measure.toSignedMeasure_apply_measurable hA]
      simp [measureReal_def]
    have he' : ∀ v ∈ V0,
        Gamma.cross u v (centeredCube z r hr) = inner ℝ f v := by
      intro v hv
      calc
        Gamma.cross u v (centeredCube z r hr) =
            DirichletForm.signedIntegralOn (Gamma.cross u v)
              (centeredCube z r hr) (fun _ => (1 : ℝ)) :=
          (hsigned _ _ hqmeas).symm
        _ = inner ℝ f v := he v hv
    have he_g' : ∀ v ∈ V0,
        Gammag.cross ug v (centeredCube z r hr) = inner ℝ f v := by
      intro v hv
      calc
        Gammag.cross ug v (centeredCube z r hr) =
            DirichletForm.signedIntegralOn (Gammag.cross ug v)
              (centeredCube z r hr) (fun _ => (1 : ℝ)) :=
          (hsigned _ _ hqmeas).symm
        _ = inner ℝ f v := he_g v hv
    have hA : 0 ≤ inner ℝ f u := by
      rw [← he' u huV]
      exact Gamma.cross_self_nonneg huE hqmeas
    have hC : 0 ≤ inner ℝ f ug := by
      rw [← he_g' ug hugV]
      exact Gammag.cross_self_nonneg hugEg hqmeas
    have hEu : 0 ≤ Gamma.cross u u (centeredCube z r hr) :=
      Gamma.cross_self_nonneg huE hqmeas
    have hEug : 0 ≤ Gamma.cross ug ug (centeredCube z r hr) :=
      Gamma.cross_self_nonneg hugE hqmeas
    have hFu : 0 ≤ Gammag.cross u u (centeredCube z r hr) :=
      Gammag.cross_self_nonneg huEg hqmeas
    have hFug : 0 ≤ Gammag.cross ug ug (centeredCube z r hr) :=
      Gammag.cross_self_nonneg hugEg hqmeas
    have hcrossE : |Gamma.cross u ug (centeredCube z r hr)| ≤
        Real.sqrt (Gamma.cross u u (centeredCube z r hr)) *
          Real.sqrt (Gamma.cross ug ug (centeredCube z r hr)) := by
      simpa only [Gamma.cross_self u huE _ hqmeas,
        Gamma.cross_self ug hugE _ hqmeas] using
        Gamma.abs_cross_le u huE ug hugE (centeredCube z r hr) hqmeas
    have hcrossF : |Gammag.cross ug u (centeredCube z r hr)| ≤
        Real.sqrt (Gammag.cross ug ug (centeredCube z r hr)) *
          Real.sqrt (Gammag.cross u u (centeredCube z r hr)) := by
      simpa only [Gammag.cross_self ug hugEg _ hqmeas,
        Gammag.cross_self u huEg _ hqmeas] using
        Gammag.abs_cross_le ug hugEg u huEg (centeredCube z r hr) hqmeas
    have hrespE : Gamma.cross u ug (centeredCube z r hr) = inner ℝ f ug := by
      exact he' ug hugV
    have hrespF : Gammag.cross ug u (centeredCube z r hr) = inner ℝ f u := by
      exact he_g' u huV
    have hcrossE' : (inner ℝ f ug) ^ 2 ≤
        (inner ℝ f u) * Gamma.cross ug ug (centeredCube z r hr) := by
      have hprod : 0 ≤ Real.sqrt (Gamma.cross u u (centeredCube z r hr)) *
          Real.sqrt (Gamma.cross ug ug (centeredCube z r hr)) :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      have hle : inner ℝ f ug ≤
          Real.sqrt (Gamma.cross u u (centeredCube z r hr)) *
            Real.sqrt (Gamma.cross ug ug (centeredCube z r hr)) := by
        calc
          inner ℝ f ug = Gamma.cross u ug (centeredCube z r hr) := hrespE.symm
          _ ≤ |Gamma.cross u ug (centeredCube z r hr)| := le_abs_self _
          _ ≤ _ := hcrossE
      have hs := (sq_le_sq₀ hC hprod).2 hle
      calc
        (inner ℝ f ug) ^ 2 ≤
            (Gamma.cross u u (centeredCube z r hr)) *
              (Gamma.cross ug ug (centeredCube z r hr)) := by
                simpa only [mul_pow, Real.sq_sqrt hEu, Real.sq_sqrt hEug] using hs
        _ = (inner ℝ f u) * Gamma.cross ug ug (centeredCube z r hr) := by
          rw [he' u huV]
    have hcrossF' : (inner ℝ f u) ^ 2 ≤
        (inner ℝ f ug) * Gammag.cross u u (centeredCube z r hr) := by
      have hprod : 0 ≤ Real.sqrt (Gammag.cross ug ug (centeredCube z r hr)) *
          Real.sqrt (Gammag.cross u u (centeredCube z r hr)) :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      have hle : inner ℝ f u ≤
          Real.sqrt (Gammag.cross ug ug (centeredCube z r hr)) *
            Real.sqrt (Gammag.cross u u (centeredCube z r hr)) := by
        calc
          inner ℝ f u = Gammag.cross ug u (centeredCube z r hr) := hrespF.symm
          _ ≤ |Gammag.cross ug u (centeredCube z r hr)| := le_abs_self _
          _ ≤ _ := hcrossF
      have hs := (sq_le_sq₀ hA hprod).2 hle
      calc
        (inner ℝ f u) ^ 2 ≤
            (Gammag.cross ug ug (centeredCube z r hr)) *
              (Gammag.cross u u (centeredCube z r hr)) := by
                simpa only [mul_pow, Real.sq_sqrt hFug, Real.sq_sqrt hFu] using hs
        _ = (inner ℝ f ug) * Gammag.cross u u (centeredCube z r hr) := by
          rw [he_g' ug hugV]
    have hlowerE := (hdiag ug hugE).1
    have hupperF := (hdiag u huE).2
    have hupper_response : inner ℝ f ug ≤
        Real.exp S * inner ℝ f u := by
      by_cases hC0 : inner ℝ f ug = 0
      · rw [hC0]
        exact mul_nonneg (hb.le) hA
      · have hCpos : 0 < inner ℝ f ug := lt_of_le_of_ne hC (Ne.symm hC0)
        have hD : Real.exp (-S) * Gamma.cross ug ug (centeredCube z r hr) ≤
            inner ℝ f ug := by
          exact hlowerE.trans_eq (he_g' ug hugV)
        have h1 := mul_le_mul_of_nonneg_left hcrossE' ha.le
        have h2 := mul_le_mul_of_nonneg_left hD hA
        have hcancel : Real.exp (-S) * inner ℝ f ug ≤ inner ℝ f u := by
          apply le_of_mul_le_mul_right (a := inner ℝ f ug) ?_ hCpos
          calc
            (Real.exp (-S) * inner ℝ f ug) * inner ℝ f ug =
                Real.exp (-S) * (inner ℝ f ug) ^ 2 := by ring
            _ ≤ Real.exp (-S) *
                ((inner ℝ f u) * Gamma.cross ug ug (centeredCube z r hr)) := h1
            _ = (inner ℝ f u) *
                (Real.exp (-S) * Gamma.cross ug ug (centeredCube z r hr)) := by ring
            _ ≤ (inner ℝ f u) * inner ℝ f ug := h2
        have hmul := mul_le_mul_of_nonneg_right hcancel hb.le
        calc
          inner ℝ f ug =
              (Real.exp (-S) * inner ℝ f ug) * Real.exp S := by
                calc
                  inner ℝ f ug = (Real.exp (-S) * Real.exp S) * inner ℝ f ug := by
                    rw [hab, one_mul]
                  _ = (Real.exp (-S) * inner ℝ f ug) * Real.exp S := by ring
          _ ≤ inner ℝ f u * Real.exp S := hmul
          _ = Real.exp S * inner ℝ f u := by ring
    have hlower_response : Real.exp (-S) * inner ℝ f u ≤ inner ℝ f ug := by
      by_cases hA0 : inner ℝ f u = 0
      · simp [hA0, hC]
      · have hApos : 0 < inner ℝ f u := lt_of_le_of_ne hA (Ne.symm hA0)
        have hD : Gammag.cross u u (centeredCube z r hr) ≤
            Real.exp S * Gamma.cross u u (centeredCube z r hr) := hupperF
        have h1 := mul_le_mul_of_nonneg_left hcrossF' hb.le
        have h2 := mul_le_mul_of_nonneg_left hD hC
        have hcancel : inner ℝ f u ≤
            Real.exp S * inner ℝ f ug := by
          apply le_of_mul_le_mul_right (a := inner ℝ f u) ?_ hApos
          calc
            inner ℝ f u * inner ℝ f u = (inner ℝ f u) ^ 2 := by ring
            _ ≤ inner ℝ f ug * Gammag.cross u u (centeredCube z r hr) := hcrossF'
            _ ≤ inner ℝ f ug *
                (Real.exp S * Gamma.cross u u (centeredCube z r hr)) := h2
            _ = (Real.exp S * inner ℝ f ug) * inner ℝ f u := by
              rw [he' u huV]
              ring
        have hmul := mul_le_mul_of_nonneg_left hcancel ha.le
        calc
          Real.exp (-S) * inner ℝ f u ≤
              Real.exp (-S) * (Real.exp S * inner ℝ f ug) := hmul
          _ = inner ℝ f ug := by
            calc
              Real.exp (-S) * (Real.exp S * inner ℝ f ug) =
                  (Real.exp (-S) * Real.exp S) * inner ℝ f ug := by ring
              _ = inner ℝ f ug := by rw [hab, one_mul]
    exact ⟨hlower_response, hupper_response⟩

end Paper
