module

public import SubdiffusiveProcess.Main.PositiveScaledNativeLayer
public import SubdiffusiveProcess.Probability.NativeCommonScaleLaw
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellSummable

@[expose] public section

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace SubdiffusiveProcess

theorem measurable_positiveScaledNativeLayer {d : ℕ} :
    Measurable
      (fun omega : SubdiffusiveProcess.NativeBilateralPotentialSample d =>
        SubdiffusiveProcess.positiveScaledNativeLayer omega) := by
  rw [measurable_pi_iff]
  intro n
  exact (_root_.SubdiffusiveProcess.Model.PotentialField.continuous_spatialScale _).measurable.comp
    (measurable_pi_apply ((n + 1 : ℕ) : ℤ))

theorem ae_positiveScaledNativeLayer_shellC11Summable {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    ∀ᵐ omega ∂MeasureTheory.Measure.infinitePi
        (fun _ : ℤ =>
          (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure),
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellC11Summable
        (SubdiffusiveProcess.positiveScaledNativeLayer omega) := by
  let μ : Measure (_root_.SubdiffusiveProcess.Model.PotentialField d) :=
    (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  let S : Set ℤ := {j | 0 ≤ j}
  let e : ℕ ≃ {j : ℤ // j ∈ S} :=
    { toFun := fun k => ⟨(k : ℤ), by simp [S]⟩
      invFun := fun j => j.1.toNat
      left_inv := by intro k; simp
      right_inv := by
        intro j
        apply Subtype.ext
        simp [S, Int.toNat_of_nonneg j.2] }
  let R : (ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d) →
      ({j : ℤ // j ∈ S} → _root_.SubdiffusiveProcess.Model.PotentialField d) :=
    S.domRestrict
  let E : ({j : ℤ // j ∈ S} → _root_.SubdiffusiveProcess.Model.PotentialField d) →
      (ℕ → _root_.SubdiffusiveProcess.Model.PotentialField d) :=
    fun x k => x (e k)
  let T : (ℕ → _root_.SubdiffusiveProcess.Model.PotentialField d) →
      (ℕ → _root_.SubdiffusiveProcess.Model.PotentialField d) :=
    fun x k => _root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k (x k)
  let F : NativeBilateralPotentialSample d →
      _root_.SubdiffusiveProcess.Model.PotentialSample d :=
    fun omega k =>
      _root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k (omega (k : ℤ))
  have hR : Measurable R := by
    exact measurable_pi_iff.mpr fun j => measurable_pi_apply j.1
  have hE : Measurable E := by
    exact Measurable.of_eval fun k : ℕ => measurable_pi_apply (e k)
  have hT : Measurable T := by
    exact Measurable.of_eval fun k : ℕ =>
      (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_triadicScale k).comp
        (measurable_pi_apply k)
  have hF : Measurable F := by
    exact Measurable.of_eval fun k : ℕ =>
      (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_triadicScale k).comp
        (measurable_pi_apply (k : ℤ))
  have hrestrict :
      Measure.map R (Measure.infinitePi (fun _ : ℤ => μ)) =
        Measure.infinitePi (fun _ : {j : ℤ // j ∈ S} => μ) := by
    simpa only [R, Set.domRestrict] using
      (Measure.infinitePi_map_restrict' (μ := fun _ : ℤ => μ) (I := S))
  have hreindex :
      Measure.map E (Measure.infinitePi (fun _ : {j : ℤ // j ∈ S} => μ)) =
        Measure.infinitePi (fun _ : ℕ => μ) := by
    have h := Measure.infinitePi_map_piCongrLeft
      (μ := fun _ : ℕ => μ) e.symm
    have hEeq :
        ⇑(MeasurableEquiv.piCongrLeft
          (fun _ : ℕ => _root_.SubdiffusiveProcess.Model.PotentialField d) e.symm) = E := by
      funext x k
      simpa only [Equiv.symm_apply_apply, E] using
        (MeasurableEquiv.piCongrLeft_apply_apply
          (β := fun _ : ℕ => _root_.SubdiffusiveProcess.Model.PotentialField d)
          e.symm x (e k))
    simpa only [hEeq] using h
  have hscale :
      Measure.map T (Measure.infinitePi (fun _ : ℕ => μ)) =
        Measure.infinitePi
          (fun k : ℕ =>
            (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure.map
              (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k)) := by
    rw [Measure.infinitePi_map_pi
      (μ := fun _ : ℕ => μ)
      (f := fun k : ℕ =>
        _root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k)
      (fun k => _root_.SubdiffusiveProcess.Model.PotentialField.measurable_triadicScale k)]
  have hmap :
      Measure.map F (Measure.infinitePi (fun _ : ℤ => μ)) = M.P.toMeasure := by
    have hcomp : F = T ∘ E ∘ R := by
      funext omega k
      rfl
    calc
      Measure.map F (Measure.infinitePi (fun _ : ℤ => μ)) =
          Measure.map (T ∘ E ∘ R) (Measure.infinitePi (fun _ : ℤ => μ)) := by
            rw [hcomp]
      _ = Measure.map T (Measure.map E
          (Measure.map R (Measure.infinitePi (fun _ : ℤ => μ)))) := by
            calc
              Measure.map (T ∘ E ∘ R)
                  (Measure.infinitePi (fun _ : ℤ => μ)) =
                  Measure.map (T ∘ E)
                    (Measure.map R (Measure.infinitePi (fun _ : ℤ => μ))) :=
                (Measure.map_map (hT.comp hE) hR).symm
              _ = Measure.map T
                    (Measure.map E (Measure.map R
                      (Measure.infinitePi (fun _ : ℤ => μ)))) :=
                (Measure.map_map hT hE).symm
      _ = M.P.toMeasure := by
        rw [hrestrict, hreindex, hscale]
        have hprod :
            M.P.toMeasure =
              Measure.infinitePi
                (fun k : ℕ =>
                  (_root_.SubdiffusiveProcess.Model.potentialMarginalLaw M.P k).toMeasure) := by
          have hi :=
            (ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
              (P := M.P.toMeasure)
              (X := fun k (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) => omega k)
              (fun k => measurable_pi_apply k)).mp M.shellPrefix.independent
          simpa only [_root_.SubdiffusiveProcess.Model.potentialMarginalLaw,
            ProbabilityMeasure.toMeasure_map, Measure.map_id'] using hi
        calc
          Measure.infinitePi
              (fun k : ℕ =>
                (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure.map
                  (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k)) =
              Measure.infinitePi
                (fun k : ℕ =>
                  (_root_.SubdiffusiveProcess.Model.potentialMarginalLaw M.P k).toMeasure) := by
            congr 1
            funext k
            have hm := congrArg
              (fun Q : ProbabilityMeasure
                (_root_.SubdiffusiveProcess.Model.PotentialField d) => Q.toMeasure)
              (M.shellPrefix.marginal_scaling k)
            calc
              Measure.map
                  (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k)
                  (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure =
                  ((_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).map
                    (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k)).toMeasure := rfl
              _ = (_root_.SubdiffusiveProcess.Model.potentialMarginalLaw M.P k).toMeasure := hm.symm
          _ = M.P.toMeasure := hprod.symm
  have hnative :
      ∀ᵐ omega ∂Measure.infinitePi (fun _ : ℤ => μ),
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellC11Summable (F omega) := by
    have h0 :=
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ae_shellC11Summable M
    rw [← hmap] at h0
    exact ae_of_ae_map hF.aemeasurable h0
  filter_upwards [hnative] with omega hω
  have hpos :
      SubdiffusiveProcess.positiveScaledNativeLayer omega =
        (fun n => F omega (n + 1)) := by
    funext n
    change _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale
        ((3 : ℝ) ^ (-(n + 1 : ℤ))) (omega ((n + 1 : ℕ) : ℤ)) =
      _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale
        (((3 : ℝ) ^ (n + 1))⁻¹) (omega ((n + 1 : ℕ) : ℤ))
    congr 2
  have hshift :
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellC11Summable
        (fun n => F omega (n + 1)) := by
    intro R₀
    obtain ⟨u, v, w, hb⟩ := hω R₀
    refine ⟨fun n => u (n + 1), fun n => v (n + 1), fun n => w (n + 1), ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro n; exact hb.u_nonneg (n + 1)
    · intro n; exact hb.v_nonneg (n + 1)
    · intro n; exact hb.w_nonneg (n + 1)
    · exact (summable_nat_add_iff 1).2 hb.u_summable
    · exact (summable_nat_add_iff 1).2 hb.v_summable
    · exact (summable_nat_add_iff 1).2 hb.w_summable
    · intro n x hx
      exact hb.value_le (n + 1) x hx
    · intro n x hx
      exact hb.deriv_le (n + 1) x hx
    · intro n x hx y hy
      exact hb.deriv_lipschitz (n + 1) x hx y hy
  rw [hpos]
  exact hshift

end SubdiffusiveProcess
