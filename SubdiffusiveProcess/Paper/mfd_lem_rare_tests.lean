module

public import SubdiffusiveProcess.Paper.lem_rare_tests_band_increment_bound
public import SubdiffusiveProcess.Paper.lem_rare_tests_dyadic_condExp_ae_limit
public import SubdiffusiveProcess.Paper.lem_rare_tests_dyadic_cover
public import SubdiffusiveProcess.ResponseMoments.QueueHelpers
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SubdiffusiveProcess MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal BigOperators

namespace SubdiffusiveProcess.Paper

/-- Markov's inequality at a prescribed dyadic start, using only its scalar absorption estimate. -/
lemma aux_mfd_lem_rare_tests_fixed_increment :
    ∀ (d : ℕ) (_hd : 1 ≤ d)
      [MeasurableSpace C(SpatialCoordinates d, ℝ)]
      [BorelSpace C(SpatialCoordinates d, ℝ)]
      (P : Measure (BilateralField d)) [IsProbabilityMeasure P]
      (center : ℤ)
      (X : ℕ → BilateralField d → ℝ)
      (Cstar a p : ℝ) (_hCstar : 0 < Cstar) (_ha : 0 < a) (_hp : 1 ≤ p),
      (let Bsym : ℕ → MeasurableSpace (BilateralField d) := fun H =>
          MeasurableSpace.comap
            ((Set.Icc (center - (H : ℤ)) (center + (H : ℤ))).domRestrict)
            (inferInstance : MeasurableSpace
              ((i : Set.Icc (center - (H : ℤ)) (center + (H : ℤ))) →
                C(SpatialCoordinates d, ℝ)));
      (∀ m H : ℕ,
          eLpNorm (fun ω => X m ω - (P[X m | Bsym H]) ω)
              (ENNReal.ofReal p) P ≤
            ENNReal.ofReal (Cstar * (3 : ℝ) ^ (-(a * (H : ℝ))))) →
        ∀ (H0 : ℕ) (B : ℝ),
          (∀ ell : ℕ, 1 ≤ ell →
            (((2 : ℝ) ^ (-(ell : ℤ) - 3 : ℤ))⁻¹ ^ p) *
              (2 * Cstar * (3 : ℝ) ^
                (-(a * ((2 ^ (ell - 1) * H0 : ℕ) : ℝ)))) ^ p ≤
              Real.exp (-(B * ((2 ^ ell * H0 : ℕ) : ℝ)))) →
          ∀ (m ell : ℕ), 1 ≤ ell →
            P {ω |
                2 ^ (-(ell : ℤ) - 3 : ℤ) ≤
                  (P[X m | Bsym (2 ^ ell * H0)]) ω -
                    (P[X m | Bsym (2 ^ (ell - 1) * H0)]) ω} ≤
              ENNReal.ofReal
                (Real.exp (-(B * ((2 ^ ell * H0 : ℕ) : ℝ))))) := by
  intro d hd _ _ P _ center X Cstar a p hCstar ha hp Bsym hband H0 B habs m ell hell
  dsimp only [Bsym] at hband ⊢
  let Hsmall : ℕ := 2 ^ (ell - 1) * H0
  let Hlarge : ℕ := 2 ^ ell * H0
  let ε : ℝ := (2 : ℝ) ^ (-(ell : ℤ) - 3 : ℤ)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hlevels : Hsmall ≤ Hlarge := by
    dsimp [Hsmall, Hlarge]
    exact Nat.mul_le_mul_right H0
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hlevel_real : (Hsmall : ℝ) ≤ Hlarge := by exact_mod_cast hlevels
  have hdecay :
      Cstar * (3 : ℝ) ^ (-(a * (Hlarge : ℝ))) ≤
        Cstar * (3 : ℝ) ^ (-(a * (Hsmall : ℝ))) := by
    apply mul_le_mul_of_nonneg_left ?_ hCstar.le
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith
  by_cases hXm : Integrable (X m) P
  · have hf : AEStronglyMeasurable
        (fun ω => X m ω -
          (P[X m |
            MeasurableSpace.comap
              ((Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))).domRestrict)
              (inferInstance : MeasurableSpace
                ((i : Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))) →
                  C(SpatialCoordinates d, ℝ)))]) ω) P := by
      apply hXm.aestronglyMeasurable.sub
      exact (integrable_condExp (m :=
        MeasurableSpace.comap
          ((Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))).domRestrict)
          (inferInstance : MeasurableSpace
            ((i : Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))) →
              C(SpatialCoordinates d, ℝ)))) (μ := P) (f := X m)).aestronglyMeasurable
    have hg : AEStronglyMeasurable
        (fun ω => X m ω -
          (P[X m |
            MeasurableSpace.comap
              ((Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))).domRestrict)
              (inferInstance : MeasurableSpace
                ((i : Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))) →
                  C(SpatialCoordinates d, ℝ)))]) ω) P := by
      apply hXm.aestronglyMeasurable.sub
      exact (integrable_condExp (m :=
        MeasurableSpace.comap
          ((Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))).domRestrict)
          (inferInstance : MeasurableSpace
            ((i : Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))) →
              C(SpatialCoordinates d, ℝ)))) (μ := P) (f := X m)).aestronglyMeasurable
    have hmark := aux_lem_rare_tests_band_increment_bound_markov p hp
      (fun ω => X m ω -
        (P[X m |
          MeasurableSpace.comap
            ((Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))).domRestrict)
            (inferInstance : MeasurableSpace
              ((i : Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))) →
                C(SpatialCoordinates d, ℝ)))]) ω)
      (fun ω => X m ω -
        (P[X m |
          MeasurableSpace.comap
            ((Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))).domRestrict)
            (inferInstance : MeasurableSpace
              ((i : Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))) →
                C(SpatialCoordinates d, ℝ)))]) ω)
      hf hg ε hε
    have hevent :
        {ω : BilateralField d | ε ≤
            (X m ω -
              (P[X m |
                MeasurableSpace.comap
                  ((Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))).domRestrict)
                  (inferInstance : MeasurableSpace
                    ((i : Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))) →
                      C(SpatialCoordinates d, ℝ)))]) ω) -
            (X m ω -
              (P[X m |
                MeasurableSpace.comap
                  ((Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))).domRestrict)
                  (inferInstance : MeasurableSpace
                    ((i : Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))) →
                      C(SpatialCoordinates d, ℝ)))]) ω)} =
          {ω : BilateralField d |
            ε ≤
              (P[X m |
                MeasurableSpace.comap
                  ((Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))).domRestrict)
                  (inferInstance : MeasurableSpace
                    ((i : Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))) →
                      C(SpatialCoordinates d, ℝ)))]) ω -
              (P[X m |
                MeasurableSpace.comap
                  ((Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))).domRestrict)
                  (inferInstance : MeasurableSpace
                    ((i : Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))) →
                      C(SpatialCoordinates d, ℝ)))]) ω} := by
      ext ω
      simp only [mem_ofPred_eq]
      have heq : ∀ u v w : ℝ, (u - v) - (u - w) = w - v := by
        intro u v w
        ring
      rw [heq]
    rw [hevent] at hmark
    let U : ℝ := 2 * Cstar * (3 : ℝ) ^ (-(a * (Hsmall : ℝ)))
    have hU : 0 < U := by
      dsimp [U]
      positivity
    have hnorm :
        eLpNorm (fun ω => X m ω -
            (P[X m |
              MeasurableSpace.comap
                ((Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))).domRestrict)
                (inferInstance : MeasurableSpace
                  ((i : Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))) →
                    C(SpatialCoordinates d, ℝ)))]) ω)
            (ENNReal.ofReal p) P +
          eLpNorm (fun ω => X m ω -
            (P[X m |
              MeasurableSpace.comap
                ((Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))).domRestrict)
                (inferInstance : MeasurableSpace
                  ((i : Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))) →
                    C(SpatialCoordinates d, ℝ)))]) ω)
            (ENNReal.ofReal p) P ≤ ENNReal.ofReal U := by
      calc
        _ ≤ ENNReal.ofReal
              (Cstar * (3 : ℝ) ^ (-(a * (Hsmall : ℝ)))) +
            ENNReal.ofReal
              (Cstar * (3 : ℝ) ^ (-(a * (Hlarge : ℝ)))) :=
          add_le_add (hband m Hsmall) (hband m Hlarge)
        _ ≤ ENNReal.ofReal
              (Cstar * (3 : ℝ) ^ (-(a * (Hsmall : ℝ)))) +
            ENNReal.ofReal
              (Cstar * (3 : ℝ) ^ (-(a * (Hsmall : ℝ)))) := by
          gcongr
        _ = ENNReal.ofReal U := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          dsimp [U]
          ring
    have hmark_bound :
        P {ω : BilateralField d |
            ε ≤
              (P[X m |
                MeasurableSpace.comap
                  ((Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))).domRestrict)
                  (inferInstance : MeasurableSpace
                    ((i : Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))) →
                      C(SpatialCoordinates d, ℝ)))]) ω -
              (P[X m |
                MeasurableSpace.comap
                  ((Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))).domRestrict)
                  (inferInstance : MeasurableSpace
                    ((i : Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))) →
                      C(SpatialCoordinates d, ℝ)))]) ω} ≤
          (ENNReal.ofReal ε)⁻¹ ^ p * (ENNReal.ofReal U) ^ p := by
      calc
        _ ≤ (ENNReal.ofReal ε)⁻¹ ^ p *
            (eLpNorm (fun ω => X m ω -
              (P[X m |
                MeasurableSpace.comap
                  ((Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))).domRestrict)
                  (inferInstance : MeasurableSpace
                    ((i : Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))) →
                      C(SpatialCoordinates d, ℝ)))]) ω)
              (ENNReal.ofReal p) P +
              eLpNorm (fun ω => X m ω -
              (P[X m |
                MeasurableSpace.comap
                  ((Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))).domRestrict)
                  (inferInstance : MeasurableSpace
                    ((i : Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))) →
                      C(SpatialCoordinates d, ℝ)))]) ω)
              (ENNReal.ofReal p) P) ^ p := hmark
        _ ≤ _ := by gcongr
    have hmark_real :
        P {ω : BilateralField d |
            ε ≤
              (P[X m |
                MeasurableSpace.comap
                  ((Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))).domRestrict)
                  (inferInstance : MeasurableSpace
                    ((i : Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))) →
                      C(SpatialCoordinates d, ℝ)))]) ω -
              (P[X m |
                MeasurableSpace.comap
                  ((Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))).domRestrict)
                  (inferInstance : MeasurableSpace
                    ((i : Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))) →
                      C(SpatialCoordinates d, ℝ)))]) ω} ≤
          ENNReal.ofReal ((ε⁻¹ * U) ^ p) := by
      calc
        _ ≤ (ENNReal.ofReal ε)⁻¹ ^ p * (ENNReal.ofReal U) ^ p := hmark_bound
        _ = _ :=
          aux_lem_rare_tests_band_increment_bound_ennreal_product ε U p hε hU
            (by linarith)
    have habs_real : ε⁻¹ ^ p * U ^ p ≤
        Real.exp (-(B * ((2 ^ ell * H0 : ℕ) : ℝ))) := by
      simpa [ε, U, Hsmall, Hlarge] using! habs ell hell
    have hreal : (ε⁻¹ * U) ^ p ≤
        Real.exp (-(B * ((2 ^ ell * H0 : ℕ) : ℝ))) := by
      calc
        _ = ε⁻¹ ^ p * U ^ p :=
          Real.mul_rpow (by positivity) (by positivity)
        _ ≤ _ := habs_real
    have hfinal :
        P {ω : BilateralField d |
            ε ≤
              (P[X m |
                MeasurableSpace.comap
                  ((Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))).domRestrict)
                  (inferInstance : MeasurableSpace
                    ((i : Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))) →
                      C(SpatialCoordinates d, ℝ)))]) ω -
              (P[X m |
                MeasurableSpace.comap
                  ((Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))).domRestrict)
                  (inferInstance : MeasurableSpace
                    ((i : Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))) →
                      C(SpatialCoordinates d, ℝ)))]) ω} ≤
          ENNReal.ofReal
            (Real.exp (-(B * ((2 ^ ell * H0 : ℕ) : ℝ)))) := by
      exact hmark_real.trans (ENNReal.ofReal_le_ofReal hreal)
    simpa [ε, Hsmall, Hlarge] using! hfinal
  · have hsmall_zero : (P[X m | Bsym Hsmall]) = 0 :=
      condExp_of_not_integrable hXm
    have hlarge_zero : (P[X m | Bsym Hlarge]) = 0 :=
      condExp_of_not_integrable hXm
    change P {ω : BilateralField d | ε ≤
      (P[X m | Bsym Hlarge]) ω - (P[X m | Bsym Hsmall]) ω} ≤ _
    rw [hlarge_zero, hsmall_zero]
    simp only [Pi.zero_apply, sub_self]
    have hempty : {ω : BilateralField d | ε ≤ (0 : ℝ)} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, not_le, mem_empty_iff_false, iff_false]
      exact hε
    rw [hempty, measure_empty]
    exact zero_le

/-- Summable error probabilities give AE convergence at every prescribed positive start. -/
lemma aux_mfd_lem_rare_tests_ae_limit :
    ∀ (d : ℕ) (_hd : 1 ≤ d)
      [MeasurableSpace C(SpatialCoordinates d, ℝ)]
      [BorelSpace C(SpatialCoordinates d, ℝ)]
      (P : Measure (BilateralField d)) [IsProbabilityMeasure P]
      (center : ℤ)
      (X : ℕ → BilateralField d → ℝ)
      (_hmeas : ∀ m, Measurable (X m))
      (Cstar a p : ℝ) (_hCstar : 0 < Cstar) (_ha : 0 < a) (_hp : 1 ≤ p),
      (let Bsym : ℕ → MeasurableSpace (BilateralField d) := fun H =>
          MeasurableSpace.comap
            ((Set.Icc (center - (H : ℤ)) (center + (H : ℤ))).domRestrict)
            (inferInstance : MeasurableSpace
              ((i : Set.Icc (center - (H : ℤ)) (center + (H : ℤ))) →
                C(SpatialCoordinates d, ℝ)));
      (∀ m H : ℕ,
          eLpNorm (fun ω => X m ω - (P[X m | Bsym H]) ω)
              (ENNReal.ofReal p) P ≤
            ENNReal.ofReal (Cstar * (3 : ℝ) ^ (-(a * (H : ℝ))))) →
        ∀ (m H0 : ℕ), 0 < H0 → ∀ᵐ ω ∂P,
          Tendsto (fun ell => (P[X m | Bsym (2 ^ ell * H0)]) ω)
            atTop (𝓝 (X m ω))) := by
  intro d hd _ _ P _ center X hmeas Cstar a p hCstar ha hp
  dsimp only
  intro hCE
  let Bsym : ℕ → MeasurableSpace (BilateralField d) := fun H =>
    MeasurableSpace.comap
      ((Set.Icc (center - (H : ℤ)) (center + (H : ℤ))).domRestrict)
      (inferInstance : MeasurableSpace
        ((i : Set.Icc (center - (H : ℤ)) (center + (H : ℤ))) →
          C(SpatialCoordinates d, ℝ)))
  have hBsym_le : ∀ H : ℕ, Bsym H ≤
      (inferInstance : MeasurableSpace (BilateralField d)) := by
    intro H
    exact (measurable_restrict (Set.Icc (center - (H : ℤ)) (center + (H : ℤ)))).comap_le
  have hmeas_err : ∀ (m H : ℕ),
      AEStronglyMeasurable
        (fun ω => X m ω - (P[X m | Bsym H]) ω) P := by
    intro m H
    exact (hmeas m).aestronglyMeasurable.sub
      ((stronglyMeasurable_condExp (m := Bsym H)).mono (hBsym_le H)).aestronglyMeasurable
  have hmarkov : ∀ (m H : ℕ) (ε : ℝ), 0 < ε →
      P {ω | ENNReal.ofReal ε ≤
          ‖X m ω - (P[X m | Bsym H]) ω‖ₑ} ≤
        (ENNReal.ofReal ε)⁻¹ ^ (ENNReal.ofReal p).toReal *
          eLpNorm (fun ω => X m ω - (P[X m | Bsym H]) ω)
            (ENNReal.ofReal p) P ^ (ENNReal.ofReal p).toReal := by
    intro m H ε hε
    exact meas_ge_le_mul_pow_eLpNorm_enorm P
      (ENNReal.ofReal_ne_zero_iff.mpr (lt_of_lt_of_le zero_lt_one hp))
      ENNReal.ofReal_ne_top (ENNReal.ofReal_ne_zero_iff.mpr hε)
      (by simp)
  have hsum : ∀ (m H0 : ℕ), 0 < H0 → ∀ ε : ℝ, 0 < ε →
      (∑' ell : ℕ, P {ω | ENNReal.ofReal ε ≤
        ‖X m ω - (P[X m | Bsym (2 ^ ell * H0)]) ω‖ₑ}) ≠ ∞ := by
    intro m H0 hH0 ε hε
    have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
    have hp_toReal : (ENNReal.ofReal p).toReal = p :=
      ENNReal.toReal_ofReal hp0.le
    have hterm : ∀ ell : ℕ,
        P {ω | ENNReal.ofReal ε ≤
            ‖X m ω - (P[X m | Bsym (2 ^ ell * H0)]) ω‖ₑ} ≤
          ENNReal.ofReal ((ε⁻¹) ^ p *
            (Cstar * (3 : ℝ) ^ (-(a * ((2 ^ ell * H0 : ℕ) : ℝ)))) ^ p) := by
      intro ell
      calc
        P {ω | ENNReal.ofReal ε ≤
            ‖X m ω - (P[X m | Bsym (2 ^ ell * H0)]) ω‖ₑ} ≤
            (ENNReal.ofReal ε)⁻¹ ^ (ENNReal.ofReal p).toReal *
              eLpNorm (fun ω => X m ω -
                (P[X m | Bsym (2 ^ ell * H0)]) ω) (ENNReal.ofReal p) P ^
                (ENNReal.ofReal p).toReal := hmarkov m (2 ^ ell * H0) ε hε
        _ ≤ (ENNReal.ofReal ε)⁻¹ ^ p *
              (ENNReal.ofReal (Cstar * (3 : ℝ) ^
                (-(a * ((2 ^ ell * H0 : ℕ) : ℝ))))) ^ p := by
          rw [hp_toReal]
          gcongr
          exact hCE m (2 ^ ell * H0)
        _ = ENNReal.ofReal ((ε⁻¹) ^ p *
            (Cstar * (3 : ℝ) ^ (-(a * ((2 ^ ell * H0 : ℕ) : ℝ)))) ^ p) := by
          rw [← ENNReal.ofReal_inv_of_pos hε,
            ENNReal.ofReal_rpow_of_pos (inv_pos.mpr hε),
            ENNReal.ofReal_rpow_of_pos (mul_pos hCstar
              (Real.rpow_pos_of_pos (by norm_num) _)),
            ← ENNReal.ofReal_mul (by positivity)]
    have hpow : ∀ ell : ℕ, ell ≤ 2 ^ ell := by
      intro ell
      induction ell with
      | zero => norm_num
      | succ ell ih =>
          have hA : 1 ≤ 2 ^ ell := Nat.one_le_pow ell 2 (by norm_num)
          have hsum : ell + 1 ≤ 2 ^ ell + 2 ^ ell := Nat.add_le_add ih hA
          simpa [pow_succ, Nat.mul_comm, two_mul] using! hsum
    let K : ℝ := (ε⁻¹) ^ p * Cstar ^ p
    let c : ℝ := a * p * (H0 : ℝ)
    have hK : 0 < K := by
      dsimp [K]
      positivity
    have hc : 0 < c := by
      dsimp [c]
      positivity
    have hgeom :
        (∑' ell : ℕ, ENNReal.ofReal
          (K * (3 : ℝ) ^ (-(c * (ell : ℝ))))) ≠ ∞ :=
      _root_.SubdiffusiveProcess.ResponseMoments.tsum_ofReal_geom_ne_top hK hc
    apply ne_top_of_le_ne_top hgeom
    refine ENNReal.tsum_le_tsum (fun ell => (hterm ell).trans ?_)
    dsimp [K, c]
    apply ENNReal.ofReal_le_ofReal
    have hle : (H0 : ℝ) * (ell : ℝ) ≤
        ((2 ^ ell * H0 : ℕ) : ℝ) := by
      calc
        (H0 : ℝ) * (ell : ℝ) ≤ (H0 : ℝ) * (2 ^ ell : ℝ) := by
          gcongr
          exact_mod_cast hpow ell
        _ = ((2 ^ ell * H0 : ℕ) : ℝ) := by
          push_cast
          ring
    have hexp : -(a * ((2 ^ ell * H0 : ℕ) : ℝ)) ≤
        -((a * (H0 : ℝ)) * (ell : ℝ)) := by
      nlinarith [hle, ha]
    have hrpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp
    have hbase : Cstar * (3 : ℝ) ^ (-(a * ((2 ^ ell * H0 : ℕ) : ℝ))) ≤
        Cstar * (3 : ℝ) ^ (-((a * (H0 : ℝ)) * (ell : ℝ))) := by
      gcongr
    have hpbase₀ := Real.rpow_le_rpow (by positivity) hbase
      (le_trans zero_lt_one.le hp)
    have hpbase :
        (Cstar * (3 : ℝ) ^ (-(a * ((2 ^ ell * H0 : ℕ) : ℝ)))) ^ p ≤
          Cstar ^ p * ((3 : ℝ) ^ (-((a * (H0 : ℝ)) * (ell : ℝ)))) ^ p := by
      calc
        (Cstar * (3 : ℝ) ^ (-(a * ((2 ^ ell * H0 : ℕ) : ℝ)))) ^ p ≤
            (Cstar * (3 : ℝ) ^ (-((a * (H0 : ℝ)) * (ell : ℝ)))) ^ p := hpbase₀
        _ = Cstar ^ p * ((3 : ℝ) ^ (-((a * (H0 : ℝ)) * (ell : ℝ)))) ^ p := by
          rw [Real.mul_rpow (by positivity) (by positivity)]
    have hreal :
        (ε⁻¹) ^ p *
            (Cstar * (3 : ℝ) ^ (-(a * ((2 ^ ell * H0 : ℕ) : ℝ)))) ^ p ≤
          (ε⁻¹) ^ p * Cstar ^ p *
            (3 : ℝ) ^ (-(a * p * (H0 : ℝ) * (ell : ℝ))) := by
      calc
        _ ≤ (ε⁻¹) ^ p * (Cstar ^ p *
            ((3 : ℝ) ^ (-((a * (H0 : ℝ)) * (ell : ℝ)))) ^ p) := by
              exact mul_le_mul_of_nonneg_left hpbase (by positivity)
        _ = (ε⁻¹) ^ p * Cstar ^ p *
            (3 : ℝ) ^ (-(a * p * (H0 : ℝ) * (ell : ℝ))) := by
              rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
              have he : -((a * (H0 : ℝ)) * (ell : ℝ)) * p =
                  -(a * p * (H0 : ℝ) * (ell : ℝ)) := by ring_nf
              rw [he]
              ring
    exact hreal
  have hAE : ∀ (m H0 : ℕ), 0 < H0 → ∀ᵐ ω ∂P,
      Tendsto (fun ell => (P[X m | Bsym (2 ^ ell * H0)]) ω)
        atTop (𝓝 (X m ω)) :=
    lem_rare_tests_dyadic_condExp_ae_limit d hd P center X hsum
  exact hAE

/-- Assemble the interval cover at a fixed positive start; only the eventual cutoff depends on X. -/
lemma aux_mfd_lem_rare_tests_fixed_cover :
    ∀ (d : ℕ)
      [MeasurableSpace C(SpatialCoordinates d, ℝ)]
      [BorelSpace C(SpatialCoordinates d, ℝ)]
      (P : Measure (BilateralField d)) [IsProbabilityMeasure P]
      (center : ℤ) (X : ℕ → BilateralField d → ℝ)
      (_hX01 : ∀ m ω, X m ω ∈ Set.Icc (0 : ℝ) 1)
      (_hmeas : ∀ m, Measurable (X m))
      (_hprob : TendstoInMeasure P X atTop (fun _ => (0 : ℝ)))
      (H0 : ℕ) (_hH00 : 0 < H0) (B : ℝ) (_hB : 0 < B),
      (let Bsym : ℕ → MeasurableSpace (BilateralField d) := fun H =>
          MeasurableSpace.comap
            ((Set.Icc (center - (H : ℤ)) (center + (H : ℤ))).domRestrict)
            (inferInstance : MeasurableSpace
              ((i : Set.Icc (center - (H : ℤ)) (center + (H : ℤ))) →
                C(SpatialCoordinates d, ℝ)));
        (∀ m : ℕ, ∀ᵐ ω ∂P, Tendsto
          (fun ell : ℕ => (P[X m | Bsym (2 ^ ell * H0)]) ω)
          atTop (𝓝 (X m ω))) →
        (∀ (m ell : ℕ), 1 ≤ ell →
          P {ω | 2 ^ (-(ell : ℤ) - 3 : ℤ) ≤
            (P[X m | Bsym (2 ^ ell * H0)]) ω -
              (P[X m | Bsym (2 ^ (ell - 1) * H0)]) ω} ≤
            ENNReal.ofReal (Real.exp (-(B * ((2 ^ ell * H0 : ℕ) : ℝ))))) →
              ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m →
                ∃ W : ℕ+ → Set (BilateralField d),
                  (∀ h : ℕ+,
                    MeasurableSet[
                      MeasurableSpace.comap
                        ((Set.Icc (center - 2 * (h : ℤ)) (center + (h : ℤ))).domRestrict)
                        (inferInstance : MeasurableSpace
                          ((i : Set.Icc (center - 2 * (h : ℤ)) (center + (h : ℤ))) →
                            C(SpatialCoordinates d, ℝ)))] (W h)) ∧
                  (∀ h : ℕ+, P (W h) ≤ ENNReal.ofReal (Real.exp (-(B * (h : ℝ))))) ∧
                  (∀ h : ℕ+, (h : ℕ) < H0 → W h = ∅) ∧
                  (∀ᵐ ω ∂P, 1 / 2 < X m ω → ω ∈ ⋃ h : ℕ+, W h)) := by
  intro d _ _ P _ center X hX01 hmeas hprob H0 hH00 B hB Bsym hD hHinc
  obtain ⟨m0, hm0⟩ := aux_rare_m0 d P X hX01 hmeas hprob B hB H0 hH00
  refine ⟨m0, fun m hm => ?_⟩
  let Bsym0 : ℕ → MeasurableSpace (BilateralField d) := fun H =>
    MeasurableSpace.comap ((Set.Icc (center - (H : ℤ)) (center + (H : ℤ))).domRestrict)
      (inferInstance : MeasurableSpace ((i : Set.Icc (center - (H : ℤ)) (center + (H : ℤ))) → C(SpatialCoordinates d, ℝ)))
  have hBsym0 : ∀ H : ℕ, Bsym0 H = MeasurableSpace.comap ((Set.Icc (center - (H : ℤ)) (center + (H : ℤ))).domRestrict)
      (inferInstance : MeasurableSpace ((i : Set.Icc (center - (H : ℤ)) (center + (H : ℤ))) → C(SpatialCoordinates d, ℝ))) := fun H => rfl
  have hlevel := aux_rare_h0_level_prob d P center X hmeas hX01 Bsym0 H0 m B (hm0 m hm)
  let W : ℕ+ → Set (BilateralField d) := fun h => (if (h : ℕ) = H0 then {ω : BilateralField d | (3 / 8 : ℝ) ≤ (P[X m | Bsym0 H0]) ω} else ∅) ∪ ⋃ (l : { l : ℕ // 1 ≤ l ∧ 2 ^ l * H0 = (h : ℕ) }), {ω : BilateralField d | (2 : ℝ) ^ (-(((l : ℕ) : ℤ)) - 3) ≤ (P[X m | Bsym0 (2 ^ (l : ℕ) * H0)]) ω - (P[X m | Bsym0 (2 ^ ((l : ℕ) - 1) * H0)]) ω}
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · exact aux_rare_clause_meas3 d P center X Bsym0 hBsym0 H0 m W rfl
  · intro h
    by_cases hh : (h : ℕ) = H0
    · have hWeq : W h = {ω : BilateralField d | (3 / 8 : ℝ) ≤ (P[X m | Bsym0 H0]) ω} := by
        dsimp only [W]
        rw [ite_eq_left hh]
        have : IsEmpty { l : ℕ // 1 ≤ l ∧ 2 ^ l * H0 = (h : ℕ) } :=
          ⟨fun l => by
            have h2l : 2 ≤ 2 ^ (l : ℕ) := by
              calc 2 = 2 ^ (1 : ℕ) := by norm_num
                _ ≤ 2 ^ (l : ℕ) := Nat.pow_le_pow_right (by norm_num) l.2.1
            have hmul : 2 * H0 ≤ 2 ^ (l : ℕ) * H0 := Nat.mul_le_mul_right H0 h2l
            rw [l.2.2, hh] at hmul
            omega⟩
        rw [iUnion_of_empty, Set.union_empty]
      rw [hWeq]
      refine le_trans hlevel (le_of_eq ?_)
      rw [show (h : ℝ) = (H0 : ℝ) from by rw [hh]]
    · by_cases hex : ∃ l : ℕ, 1 ≤ l ∧ 2 ^ l * H0 = (h : ℕ)
      · obtain ⟨l, hl1, hl2⟩ := hex
        have hsub : W h ⊆ {ω : BilateralField d | (2 : ℝ) ^ (-(((l : ℕ) : ℤ)) - 3) ≤ (P[X m | Bsym0 (2 ^ (l : ℕ) * H0)]) ω - (P[X m | Bsym0 (2 ^ ((l : ℕ) - 1) * H0)]) ω} := by
          intro ω hω
          dsimp only [W] at hω
          rw [ite_eq_right hh, Set.empty_union] at hω
          simp only [Set.mem_iUnion, mem_ofPred_eq] at hω
          obtain ⟨l', hl'mem⟩ := hω
          have hl'eq : (l' : ℕ) = l := by
            have h2 : 2 ^ l = 2 ^ (l' : ℕ) := Nat.eq_of_mul_eq_mul_right hH00 (hl2.trans l'.2.2.symm)
            exact (Nat.pow_right_injective (by norm_num) h2).symm
          rw [hl'eq] at hl'mem
          exact hl'mem
        refine le_trans (measure_mono hsub) ?_
        have hcast : ((2 ^ l * H0 : ℕ) : ℝ) = ((h : ℕ) : ℝ) := by exact_mod_cast hl2
        have hmono := hHinc m l hl1
        rw [hcast] at hmono
        exact hmono
      · have hWeq : W h = ∅ := by
          dsimp only [W]
          rw [ite_eq_right hh, Set.empty_union]
          have : IsEmpty { l : ℕ // 1 ≤ l ∧ 2 ^ l * H0 = (h : ℕ) } := ⟨fun l => hex ⟨l, l.2.1, l.2.2⟩⟩
          rw [iUnion_of_empty]
        rw [hWeq, measure_empty]
        exact zero_le
  · exact aux_rare_clause_empty3 d P center X Bsym0 hBsym0 H0 m hH00 W rfl
  · filter_upwards [hD m] with ω hlim
    intro hlt
    by_cases h0 : (P[X m | Bsym0 H0]) ω < 3 / 8
    · have hfail : ¬ (∀ l : ℕ, 1 ≤ l → (P[X m | Bsym0 (2 ^ l * H0)]) ω - (P[X m | Bsym0 (2 ^ (l - 1) * H0)]) ω < (2 : ℝ) ^ (-(l : ℤ) - 3)) := by
        intro hΔ
        exact absurd (aux_rare_cover_telescope d P center X Bsym0 H0 hH00 m ω hlim h0 hΔ) (not_le.mpr hlt)
      push Not at hfail
      obtain ⟨l, hl1, hl2⟩ := hfail
      refine Set.mem_iUnion.mpr ⟨⟨2 ^ l * H0, Nat.mul_pos (Nat.pow_pos (by norm_num)) hH00⟩, ?_⟩
      dsimp only [W]
      exact Or.inr (Set.mem_iUnion.mpr ⟨⟨l, hl1, rfl⟩, hl2⟩)
    · push Not at h0
      refine Set.mem_iUnion.mpr ⟨⟨H0, hH00⟩, ?_⟩
      dsimp only [W]
      split_ifs with hc
      · exact Or.inl h0
      · exfalso; exact absurd rfl hc

/-- Rare tests admit a constant-only positive dyadic start, before the field law and observables.
Source: live paper mfd:lem-rare-tests.
The eventual cutoff and cover may depend on the observable family; the start does not. -/
theorem mfd_lem_rare_tests :
    ∃ Cgeom : ℝ, 4 ≤ Cgeom ∧
      ∀ (Cstar a p : ℝ) (_hCstar : 0 < Cstar) (_ha : 0 < a) (_hp : 1 ≤ p)
        (B : ℝ) (_hB : 0 < B) (_hmargin : Cgeom * B < a * p * Real.log 3),
        ∃ H0 : ℕ, 0 < H0 ∧
          ∀ (d : ℕ) (_hd : 1 ≤ d)
            [MeasurableSpace C(SpatialCoordinates d, ℝ)]
            [BorelSpace C(SpatialCoordinates d, ℝ)]
            (P : Measure (BilateralField d)) [IsProbabilityMeasure P]
            (center : ℤ)
            (X : ℕ → BilateralField d → ℝ)
            (_hX01 : ∀ m ω, X m ω ∈ Set.Icc (0 : ℝ) 1)
            (_hmeas : ∀ m, Measurable (X m))
            (_hprob : TendstoInMeasure P X atTop (fun _ => (0 : ℝ))),
            (let Bsym : ℕ → MeasurableSpace (BilateralField d) := fun H =>
                MeasurableSpace.comap
                  ((Set.Icc (center - (H : ℤ)) (center + (H : ℤ))).domRestrict)
                  (inferInstance : MeasurableSpace
                    ((i : Set.Icc (center - (H : ℤ)) (center + (H : ℤ))) →
                      C(SpatialCoordinates d, ℝ)));
              (∀ m H : ℕ,
                eLpNorm (fun ω => X m ω - (P[X m | Bsym H]) ω) (ENNReal.ofReal p) P ≤
                  ENNReal.ofReal (Cstar * (3 : ℝ) ^ (-(a * (H : ℝ))))) →
              ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m →
                ∃ W : ℕ+ → Set (BilateralField d),
                  (∀ h : ℕ+,
                    MeasurableSet[
                      MeasurableSpace.comap
                        ((Set.Icc (center - 2 * (h : ℤ)) (center + (h : ℤ))).domRestrict)
                        (inferInstance : MeasurableSpace
                          ((i : Set.Icc (center - 2 * (h : ℤ)) (center + (h : ℤ))) →
                            C(SpatialCoordinates d, ℝ)))] (W h)) ∧
                  (∀ h : ℕ+, P (W h) ≤ ENNReal.ofReal (Real.exp (-(B * (h : ℝ))))) ∧
                  (∀ h : ℕ+, (h : ℕ) < H0 → W h = ∅) ∧
                  (∀ᵐ ω ∂P, 1 / 2 < X m ω → ω ∈ ⋃ h : ℕ+, W h)) := by
  refine ⟨4, by norm_num, ?_⟩
  intro Cstar a p hCstar ha hp B hB hmargin
  obtain ⟨H0, hH00, hAbs⟩ :=
    aux_lem_rare_tests_band_increment_bound_absorption Cstar a p 4 B
      hCstar ha hp (by norm_num) hB hmargin
  refine ⟨H0, hH00, ?_⟩
  intro d hd _ _ P _ center X hX01 hmeas hprob
  dsimp only
  intro hCE
  have hInc := aux_mfd_lem_rare_tests_fixed_increment d hd P center X
    Cstar a p hCstar ha hp hCE H0 B (hAbs H0 le_rfl)
  have hAE := aux_mfd_lem_rare_tests_ae_limit d hd P center X hmeas
    Cstar a p hCstar ha hp hCE
  exact aux_mfd_lem_rare_tests_fixed_cover d P center X hX01 hmeas hprob
    H0 hH00 B hB (fun m => hAE m H0 hH00) hInc

end SubdiffusiveProcess.Paper
