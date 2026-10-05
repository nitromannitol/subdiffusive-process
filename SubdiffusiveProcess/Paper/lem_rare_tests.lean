module

public import SubdiffusiveProcess.Paper.lem_branch
public import SubdiffusiveProcess.Paper.lem_rare_tests_dyadic_error_summable
public import SubdiffusiveProcess.Paper.lem_rare_tests_dyadic_condExp_ae_limit
public import SubdiffusiveProcess.Paper.lem_rare_tests_band_increment_bound
public import SubdiffusiveProcess.Paper.lem_rare_tests_dyadic_cover
public import SubdiffusiveProcess.ResponseMoments.BandFiltration
public import SubdiffusiveProcess.ResponseMoments.QueueHelpers
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SubdiffusiveProcess MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal BigOperators

namespace SubdiffusiveProcess.Paper



theorem lem_rare_tests :
    ∃ Cgeom : ℝ, 4 ≤ Cgeom ∧
      ∀ (d : ℕ) (_hd : 1 ≤ d)
        [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (P : Measure (BilateralField d)) [IsProbabilityMeasure P]
        (center : ℤ)
        (X : ℕ → BilateralField d → ℝ)
        (_hX01 : ∀ m ω, X m ω ∈ Set.Icc (0 : ℝ) 1)
        (_hmeas : ∀ m, Measurable (X m))
        (_hprob : TendstoInMeasure P X atTop (fun _ => (0 : ℝ)))
        (Cstar a p : ℝ) (_hCstar : 0 < Cstar) (_ha : 0 < a) (_hp : 1 ≤ p),
        (let Bsym : ℕ → MeasurableSpace (BilateralField d) := fun H =>
            MeasurableSpace.comap
              ((Set.Icc (center - (H : ℤ)) (center + (H : ℤ))).domRestrict)
              (inferInstance : MeasurableSpace
                ((i : Set.Icc (center - (H : ℤ)) (center + (H : ℤ))) →
                  C(SpatialCoordinates d, ℝ)));
          (∀ m H : ℕ,
            eLpNorm (fun ω => X m ω - (P[X m | Bsym H]) ω) (ENNReal.ofReal p) P ≤
              ENNReal.ofReal (Cstar * (3 : ℝ) ^ (-(a * (H : ℝ))))) →
          ∀ B : ℝ, 0 < B → Cgeom * B < a * p * Real.log 3 →
            ∃ H0 m0 : ℕ, 0 < H0 ∧
              ∀ m : ℕ, m0 ≤ m →
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
  intro d hd hMs hBs P hP center X hX01 hmeas hprob Cstar a p hCstar ha hp
  dsimp only
  intro hCE B hB hmargin
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
  have hInc : ∀ B' : ℝ, 0 < B' → 4 * B' < a * p * Real.log 3 →
      ∃ Hinc : ℕ, 0 < Hinc ∧
        ∀ H0 : ℕ, Hinc ≤ H0 →
          ∀ (m ell : ℕ), 1 ≤ ell →
            P {ω |
                2 ^ (-(ell : ℤ) - 3 : ℤ) ≤
                  (P[X m | Bsym (2 ^ ell * H0)]) ω -
                    (P[X m | Bsym (2 ^ (ell - 1) * H0)]) ω} ≤
              ENNReal.ofReal
                (Real.exp (-(B' * ((2 ^ ell * H0 : ℕ) : ℝ)))) := by
    intro B' hB' hmargin'
    exact lem_rare_tests_band_increment_bound d hd P center X Cstar a p
      hCstar ha hp hCE 4 B' (by norm_num) hB' hmargin'
  have hcover := lem_rare_tests_dyadic_cover 4 (by norm_num) d hd P center X hX01
    hmeas hprob Cstar a p hCstar ha hp
  exact hcover hCE hAE hInc B hB hmargin
