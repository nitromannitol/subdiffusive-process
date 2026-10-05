module

public import SubdiffusiveProcess.Paper.lem_as_regularity_dirichlet_energy
public import SubdiffusiveProcess.Paper.lem_as_regularity_dirichlet_holder
public import SubdiffusiveProcess.Paper.lem_as_regularity_neumann_energy
public import SubdiffusiveProcess.Paper.lem_as_regularity_neumann_holder
public import SubdiffusiveProcess.Paper.lem_as_regularity_unit_sup
public import SubdiffusiveProcess.Paper.prop_growth
public import SubdiffusiveProcess.Paper.deterministic_good_scale_input
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import SubdiffusiveProcess.Paper.sum_errors_baseline_input
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Metric
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section
namespace SubdiffusiveProcess.Paper

/-! Small-radius half of `lem_as_regularity_unit` : for radii `r ≤ r_N = 3^{-θN}` the stronger finite-cutoff constants
`K_N` with `K_N ≤ B·3^{ξN}` are absorbed by the strict exponent margins
`t0 - t` and `alpha0 - alpha`. -/

/-- Scalar absorption `K_N r^e ≤ B` for `r ≤ 3^{-θN}` and `ξ ≤ θ e`. -/
theorem aux_lem_as_regularity_unit_rpow_absorb
    (K B xi theta e r : ℝ) (N : ℕ)
    (hB : 0 < B)
    (hKB : K ≤ B * (3 : ℝ) ^ (xi * (N : ℝ)))
    (he : 0 ≤ e) (hxi : xi ≤ theta * e)
    (hr : 0 < r) (hrN : r ≤ (3 : ℝ) ^ (-(theta * (N : ℝ)))) :
    K * r ^ e ≤ B := by
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have h3ge1 : (1 : ℝ) ≤ 3 := by norm_num
  have hB3 : (0 : ℝ) ≤ B * (3 : ℝ) ^ (xi * (N : ℝ)) :=
    mul_nonneg hB.le (Real.rpow_pos_of_pos h3pos _).le
  have h2 : r ^ e ≤ (3 : ℝ) ^ ((-(theta * (N : ℝ))) * e) := by
    calc r ^ e ≤ ((3 : ℝ) ^ (-(theta * (N : ℝ)))) ^ e :=
          Real.rpow_le_rpow hr.le hrN he
      _ = (3 : ℝ) ^ ((-(theta * (N : ℝ))) * e) :=
          (Real.rpow_mul (le_of_lt h3pos) _ e).symm
  have h3 : (B * (3 : ℝ) ^ (xi * (N : ℝ))) * r ^ e ≤
            (B * (3 : ℝ) ^ (xi * (N : ℝ))) * (3 : ℝ) ^ ((-(theta * (N : ℝ))) * e) :=
    mul_le_mul_of_nonneg_left h2 hB3
  have h4 : (B * (3 : ℝ) ^ (xi * (N : ℝ))) * (3 : ℝ) ^ ((-(theta * (N : ℝ))) * e) =
            B * (3 : ℝ) ^ ((xi - theta * e) * (N : ℝ)) := by
    rw [mul_assoc]
    congr 1
    rw [← Real.rpow_add h3pos]
    congr 1
    ring
  have h5 : (3 : ℝ) ^ ((xi - theta * e) * (N : ℝ)) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos h3ge1
    have hle : xi - theta * e ≤ 0 := by linarith
    exact mul_nonpos_of_nonpos_of_nonneg hle (Nat.cast_nonneg N)
  have h6 : B * (3 : ℝ) ^ ((xi - theta * e) * (N : ℝ)) ≤ B * 1 :=
    mul_le_mul_of_nonneg_left h5 hB.le
  calc K * r ^ e
      ≤ (B * (3 : ℝ) ^ (xi * (N : ℝ))) * r ^ e :=
        mul_le_mul_of_nonneg_right hKB (Real.rpow_nonneg hr.le e)
    _ ≤ (B * (3 : ℝ) ^ (xi * (N : ℝ))) * (3 : ℝ) ^ ((-(theta * (N : ℝ))) * e) := h3
    _ = B * (3 : ℝ) ^ ((xi - theta * e) * (N : ℝ)) := h4
    _ ≤ B * 1 := h6
    _ = B := by ring

/-- Energy absorption: an `r^{t0}` bound with constant `K_N` becomes an `r^t` bound
with constant `B` below the radius `3^{-θN}`. -/
theorem aux_lem_as_regularity_unit_energy_absorb
    (En K B c xi theta t t0 r : ℝ) (N : ℕ)
    (hB : 0 < B)
    (hKB : K ≤ B * (3 : ℝ) ^ (xi * (N : ℝ)))
    (ht : t < t0) (hxi : xi ≤ theta * (t0 - t))
    (hr : 0 < r) (hrN : r ≤ (3 : ℝ) ^ (-(theta * (N : ℝ))))
    (hEn : En ≤ K * c ^ 2 * r ^ t0) :
    En ≤ B * c ^ 2 * r ^ t := by
  have he : 0 < t0 - t := sub_pos.mpr ht
  have hre : 0 < r ^ (t0 - t) := Real.rpow_pos_of_pos hr _
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have h3one : (1 : ℝ) ≤ 3 := by norm_num
  have key : K * r ^ (t0 - t) ≤ B := by
    by_cases hK : K ≤ 0
    · have h1 : K * r ^ (t0 - t) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hK (le_of_lt hre)
      linarith
    · push Not at hK
      have h3xi_nonneg : 0 ≤ (3 : ℝ) ^ (xi * (N : ℝ)) :=
        Real.rpow_nonneg (le_of_lt h3pos) _
      have step1 : K * r ^ (t0 - t) ≤ (B * (3 : ℝ) ^ (xi * (N : ℝ))) * r ^ (t0 - t) :=
        mul_le_mul_of_nonneg_right hKB (le_of_lt hre)
      have hrle : r ^ (t0 - t) ≤ ((3 : ℝ) ^ (-(theta * (N : ℝ)))) ^ (t0 - t) :=
        Real.rpow_le_rpow (le_of_lt hr) hrN (le_of_lt he)
      have step2 : (B * (3 : ℝ) ^ (xi * (N : ℝ))) * r ^ (t0 - t)
          ≤ (B * (3 : ℝ) ^ (xi * (N : ℝ))) * ((3 : ℝ) ^ (-(theta * (N : ℝ)))) ^ (t0 - t) :=
        mul_le_mul_of_nonneg_left hrle (mul_nonneg (le_of_lt hB) h3xi_nonneg)
      have hpow : ((3 : ℝ) ^ (-(theta * (N : ℝ)))) ^ (t0 - t)
          = (3 : ℝ) ^ (-(theta * (N : ℝ)) * (t0 - t)) :=
        (Real.rpow_mul (le_of_lt h3pos) (-(theta * (N : ℝ))) (t0 - t)).symm
      rw [hpow] at step2
      have hexp_le : xi * (N : ℝ) + (-(theta * (N : ℝ)) * (t0 - t)) ≤ 0 := by
        have hsub : xi - theta * (t0 - t) ≤ 0 := by linarith [hxi]
        have hfac : xi * (N : ℝ) + (-(theta * (N : ℝ)) * (t0 - t))
            = (N : ℝ) * (xi - theta * (t0 - t)) := by ring
        rw [hfac]
        exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg N) hsub
      have step3 : (B * (3 : ℝ) ^ (xi * (N : ℝ))) * (3 : ℝ) ^ (-(theta * (N : ℝ)) * (t0 - t)) ≤ B := by
        have hprod : (3 : ℝ) ^ (xi * (N : ℝ)) * (3 : ℝ) ^ (-(theta * (N : ℝ)) * (t0 - t))
            = (3 : ℝ) ^ (xi * (N : ℝ) + (-(theta * (N : ℝ)) * (t0 - t))) :=
          (Real.rpow_add h3pos _ _).symm
        have hle1 : (3 : ℝ) ^ (xi * (N : ℝ) + (-(theta * (N : ℝ)) * (t0 - t))) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos h3one hexp_le
        have hassoc : (B * (3 : ℝ) ^ (xi * (N : ℝ))) * (3 : ℝ) ^ (-(theta * (N : ℝ)) * (t0 - t))
            = B * ((3 : ℝ) ^ (xi * (N : ℝ)) * (3 : ℝ) ^ (-(theta * (N : ℝ)) * (t0 - t))) := by ring
        rw [hassoc, hprod]
        calc B * (3 : ℝ) ^ (xi * (N : ℝ) + (-(theta * (N : ℝ)) * (t0 - t))) ≤ B * 1 :=
              mul_le_mul_of_nonneg_left hle1 (le_of_lt hB)
          _ = B := by ring
      linarith [step1, step2, step3]
  have hrt0 : r ^ t0 = r ^ (t0 - t) * r ^ t := by
    have h := Real.rpow_add hr (t0 - t) t
    rw [show t0 - t + t = t0 from by ring] at h
    exact h
  have hnonneg : 0 ≤ c ^ 2 * r ^ t :=
    mul_nonneg (sq_nonneg c) (Real.rpow_nonneg (le_of_lt hr) _)
  have hmid : K * c ^ 2 * r ^ t0 ≤ B * c ^ 2 * r ^ t := by
    have heq : K * c ^ 2 * r ^ t0 = (K * r ^ (t0 - t)) * (c ^ 2 * r ^ t) := by
      rw [hrt0]; ring
    rw [heq]
    calc (K * r ^ (t0 - t)) * (c ^ 2 * r ^ t) ≤ B * (c ^ 2 * r ^ t) :=
          mul_le_mul_of_nonneg_right key hnonneg
      _ = B * c ^ 2 * r ^ t := by ring
  linarith [hEn, hmid]

/-- Oscillation absorption: a `ρ^{a0}` bound with constant `K_N·c` becomes a `ρ^a`
bound with constant `B·c` for `0 ≤ ρ ≤ 3^{-θN}`. -/
theorem aux_lem_as_regularity_unit_holder_absorb
    (D K B c xi theta a a0 rho : ℝ) (N : ℕ)
    (hB : 0 < B) (hc : 0 ≤ c)
    (hKB : K ≤ B * (3 : ℝ) ^ (xi * (N : ℝ)))
    (ha : 0 < a) (ha0 : a < a0) (hxi : xi ≤ theta * (a0 - a))
    (hrho : 0 ≤ rho) (hrhoN : rho ≤ (3 : ℝ) ^ (-(theta * (N : ℝ))))
    (hD : D ≤ K * c * rho ^ a0) :
    D ≤ B * c * rho ^ a := by
    by_cases hrho0 : rho = 0
    · rw [hrho0] at hD ⊢
      have hz0 : (0:ℝ) ^ a0 = 0 := Real.zero_rpow (ne_of_gt (lt_trans ha ha0))
      have hza : (0:ℝ) ^ a = 0 := Real.zero_rpow (ne_of_gt ha)
      simp only [hz0, hza, mul_zero] at hD ⊢
      exact hD
    · have hrho_pos : 0 < rho := lt_of_le_of_ne hrho (Ne.symm hrho0)
      have he : 0 ≤ a0 - a := le_of_lt (sub_pos.mpr ha0)
      have hca : 0 ≤ c * rho ^ a := mul_nonneg hc (Real.rpow_nonneg hrho a)
      have hKabs : K * rho ^ (a0 - a) ≤ B := by
        rcases le_or_gt K 0 with hK | hK
        · calc K * rho ^ (a0 - a) ≤ 0 * rho ^ (a0 - a) :=
              mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hrho (a0 - a))
          _ = 0 := by rw [zero_mul]
          _ ≤ B := le_of_lt hB
        · have h3pos : (0:ℝ) < 3 := by norm_num
          have h3nn : (0:ℝ) ≤ 3 := by norm_num
          have hB3 : 0 ≤ B * (3:ℝ) ^ (xi * (N:ℝ)) :=
            mul_nonneg (le_of_lt hB) (Real.rpow_nonneg h3nn (xi * (N:ℝ)))
          have hle1 : (3:ℝ) ^ (xi * (N:ℝ)) * ((3:ℝ) ^ (-(theta * (N:ℝ)))) ^ (a0 - a) ≤ 1 := by
            rw [← Real.rpow_mul (x := (3:ℝ)) h3nn (-(theta * (N:ℝ))) (a0 - a)]
            rw [← Real.rpow_add (x := (3:ℝ)) h3pos (xi * (N:ℝ)) (-(theta * (N:ℝ)) * (a0 - a))]
            rw [show xi * (N:ℝ) + (-(theta * (N:ℝ))) * (a0 - a)
                  = (xi - theta * (a0 - a)) * (N:ℝ) from by ring]
            exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1:ℝ) ≤ 3)
              (mul_nonpos_of_nonpos_of_nonneg (by linarith [hxi]) (Nat.cast_nonneg N))
          calc K * rho ^ (a0 - a)
              ≤ (B * (3:ℝ) ^ (xi * (N:ℝ))) * rho ^ (a0 - a) :=
                mul_le_mul_of_nonneg_right hKB (Real.rpow_nonneg hrho (a0 - a))
            _ ≤ (B * (3:ℝ) ^ (xi * (N:ℝ))) * ((3:ℝ) ^ (-(theta * (N:ℝ)))) ^ (a0 - a) :=
                mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hrho hrhoN he) hB3
            _ = B * ((3:ℝ) ^ (xi * (N:ℝ)) * ((3:ℝ) ^ (-(theta * (N:ℝ)))) ^ (a0 - a)) := by ring
            _ ≤ B * 1 := mul_le_mul_of_nonneg_left hle1 (le_of_lt hB)
            _ = B := by rw [mul_one]
      have h1 : rho ^ a0 = rho ^ (a0 - a) * rho ^ a := by
        have h2 := Real.rpow_add hrho_pos (a0 - a) a
        rw [show a0 - a + a = a0 from by ring] at h2
        exact h2
      have hstep : K * c * rho ^ a0 = (K * rho ^ (a0 - a)) * (c * rho ^ a) := by
        rw [h1]; ring
      calc D ≤ K * c * rho ^ a0 := hD
        _ = (K * rho ^ (a0 - a)) * (c * rho ^ a) := hstep
        _ ≤ B * (c * rho ^ a) := mul_le_mul_of_nonneg_right hKabs hca
        _ = B * c * rho ^ a := by ring

/-- A `C^a` norm bound gives the pointwise oscillation bound for every pair of points,
with the Euclidean distance used by `holderRatioSet`. -/
theorem aux_lem_as_regularity_unit_holder_pair {d : ℕ}
    (a A : ℝ) (ha : 0 < a) (S : Set (SpatialCoordinates d))
    (U : SpatialCoordinates d → ℝ)
    (hH : IsHolderOn a S U) (hA : cAlphaNorm a S U ≤ A)
    (x y : SpatialCoordinates d) (hx : x ∈ S) (hy : y ∈ S) :
    |U x - U y| ≤ A * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ a := by
  by_cases hxy : x = y
  · subst hxy
    simp [Real.zero_rpow ha.ne']
  · have hne_coord : ∃ j : Fin d, x j ≠ y j := by
      by_contra h
      push Not at h
      exact hxy (funext h)
    obtain ⟨j, hj⟩ := hne_coord
    have hsum_pos : 0 < ∑ k : Fin d, (x k - y k) ^ 2 := by
      apply Finset.sum_pos'
      · intro k _
        positivity
      · exact ⟨j, Finset.mem_univ j, sq_pos_of_ne_zero (sub_ne_zero.mpr hj)⟩
    set ρ := Real.sqrt (∑ k : Fin d, (x k - y k) ^ 2) with hρdef
    have hρpos : 0 < ρ := by
      rw [hρdef]
      exact Real.sqrt_pos.mpr hsum_pos
    have hρa_pos : 0 < ρ ^ a := Real.rpow_pos_of_pos hρpos a
    have hmem : |U x - U y| / ρ ^ a ∈ holderRatioSet a S U := by
      refine ⟨x, hx, y, hy, hxy, ?_⟩
      rw [hρdef]
    have hle1 : |U x - U y| / ρ ^ a ≤ holderSeminorm a S U := le_csSup hH hmem
    have hfirst_nonneg : 0 ≤ sSup {v : ℝ | ∃ x ∈ S, v = |U x|} := by
      apply Real.sSup_nonneg
      intro v hv
      rcases hv with ⟨w, _, rfl⟩
      exact abs_nonneg (U w)
    have hle2 : holderSeminorm a S U ≤ cAlphaNorm a S U := by
      unfold cAlphaNorm holderSeminorm
      linarith
    have hle3 : |U x - U y| / ρ ^ a ≤ A := le_trans hle1 (le_trans hle2 hA)
    rw [div_le_iff₀ hρa_pos] at hle3
    rw [hρdef] at hle3
    exact hle3

/-- A sup bound and a pairwise Euclidean-Hölder bound assemble into the full
`IsHolderOn`/`cAlphaNorm` class. -/
theorem aux_lem_as_regularity_unit_cAlphaNorm_of_pairs {d : ℕ}
    (alpha A Sup : ℝ) (hA : 0 ≤ A) (hSup : 0 ≤ Sup)
    (S : Set (SpatialCoordinates d)) (U : SpatialCoordinates d → ℝ)
    (hsup : ∀ x ∈ S, |U x| ≤ Sup)
    (hpair : ∀ x ∈ S, ∀ y ∈ S,
      |U x - U y| ≤ A * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha) :
    IsHolderOn alpha S U ∧ cAlphaNorm alpha S U ≤ Sup + A := by
  have key : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      |U x - U y| / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha ≤ A := by
    intro x hxS y hyS hxy
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hxy
    have hj2 : 0 < (x j - y j) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hj)
    have hle := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => sq_nonneg (x i - y i))
      (Finset.mem_univ j)
    have hsum_pos : 0 < ∑ j : Fin d, (x j - y j) ^ 2 := lt_of_lt_of_le hj2 hle
    have hpos : 0 < (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha :=
      Real.rpow_pos_of_pos (Real.sqrt_pos.mpr hsum_pos) alpha
    rw [div_le_iff₀ hpos]
    exact hpair x hxS y hyS
  constructor
  · unfold IsHolderOn
    refine ⟨A, ?_⟩
    intro v hv
    unfold holderRatioSet at hv
    obtain ⟨x, hxS, y, hyS, hxy, rfl⟩ := hv
    exact key x hxS y hyS hxy
  · unfold cAlphaNorm holderSeminorm holderRatioSet
    apply add_le_add
    · apply Real.sSup_le
      · intro v hv
        simp only [mem_ofPred_eq] at hv
        obtain ⟨x, hxS, rfl⟩ := hv
        exact hsup x hxS
      · exact hSup
    · apply Real.sSup_le
      · intro v hv
        simp only [mem_ofPred_eq] at hv
        obtain ⟨x, hxS, y, hyS, hxy, rfl⟩ := hv
        exact key x hxS y hyS hxy
      · exact hA

/-- Dirichlet small-radius half: from `prop_growth` at the stronger exponents
`t0, alpha0` and the carried cutoff envelope, one random constant `B` controls the
energy at every radius `rad ≤ 3^{-θN}` and every oscillation over distances
`≤ 3^{-θN}`, uniformly in `N` and in the bounded data. -/
theorem aux_lem_as_regularity_unit_dirichlet_small_radius
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d)
    (Pc : in_poincare d hd E)
    (Xc : in_extension d hd E)
    (W : SmallPerturbationInput d)
    (Cp : CampanatoInput d)
    (Sf : SobolevFoundationalInput d hd)
    (alpha alpha0 t t0 : ℝ)
    (hal : 0 < alpha)
    (hal0 : alpha < alpha0)
    (hal1 : alpha0 < 1)
    (ht1 : (d : ℝ) - 1 < t)
    (ht0 : t < t0)
    (ht2 : t0 < (d : ℝ)) :
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (_Rm : in_responses d M)
      (Sreg : in_6_16 d M)
      (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H →
      M.delta ≤ delta0 →
      (hcutoffEnvelope :
        ∀ (p C : ℝ),
          1 ≤ p →
          0 ≤ C →
          ∀ (Kcut : ℕ → BilateralField d → ℝ),
            (∀ N : ℕ,
              MemLp (Kcut N) (ENNReal.ofReal p)
                (chaosSampleLaw M).toMeasure) →
            (∀ N : ℕ,
              eLpNorm (Kcut N) (ENNReal.ofReal p)
                (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal C) →
            ∀ (xi : ℝ),
              0 < xi →
              ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                ∃ B : ℝ, 0 < B ∧
                  ∀ N : ℕ,
                    |Kcut N omega| ≤ B * (3 : ℝ) ^ (xi * (N : ℝ))) →
      ∀ theta : ℝ, 0 < theta →
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ B : ℝ, 0 < B ∧
        ∀ N : ℕ,
          ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
            0 ≤ Kf →
            AEMeasurable F
              (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
            (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
              |F x| ≤ Kf) →
            ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
              ContDiff ℝ 2 phi →
              c2Norm
                  (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                    Set (SpatialCoordinates d)) phi ≤ Cphi →
              ∀ (b u : weakSobolevGraph (unitNeumannCube d)),
                ((b : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
                  =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))]
                    phi →
                SolvesDirichlet
                    (cutoffPositiveCoefficient M H omega N
                      (fun _ => (1 / 2 : ℝ)) one_pos) F b u →
                (∀ (x : SpatialCoordinates d) (rad : ℝ),
                  x ∈ unitNeumannCube d → 0 < rad → rad ≤ 1 →
                  rad ≤ (3 : ℝ) ^ (-(theta * (N : ℝ))) →
                  localGradientEnergy
                    (cutoffPositiveCoefficient M H omega N
                      (fun _ => (1 / 2 : ℝ)) one_pos)
                    (s := Metric.ball x rad ∩
                      (unitNeumannCube d : Set (SpatialCoordinates d)))
                    (isOpen_ball.measurableSet.inter
                      (unitNeumannCube d).isOpen.measurableSet)
                    (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤
                      B * (Kf + Cphi) ^ 2 * rad ^ t) ∧
                (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
                  ((u : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
                    =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] U ∧
                  ∀ x ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                      Set (SpatialCoordinates d)),
                  ∀ y ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                      Set (SpatialCoordinates d)),
                    Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤
                      (3 : ℝ) ^ (-(theta * (N : ℝ))) →
                    |U x - U y| ≤
                      B * (Kf + Cphi) * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha) := by
  obtain ⟨delta1, hdelta1pos, hdelta1⟩ :=
    prop_growth d hd E Pc Xc W Cp Sf t0 alpha0 1 (fun _ => (2 : ℝ))
      (by linarith) ht2 (by linarith) hal1 (fun _ => by norm_num)
  refine ⟨delta1, hdelta1pos, ?_⟩
  intro M Rm Sreg It H hIR hdelta hcut theta htheta
  obtain ⟨K, Cb, hKmem, hKnorm, hKge, hKest⟩ :=
    hdelta1 M Rm Sreg It H hIR hdelta (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos le_rfl
  have hxi : 0 < theta * min (t0 - t) (alpha0 - alpha) :=
    mul_pos htheta (lt_min (by linarith) (by linarith))
  have henv := hcut 2 (max (Cb 0) 0) (by norm_num) (le_max_right _ _) K
    (fun N => hKmem 0 N)
    (fun N => (hKnorm 0 N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
    (theta * min (t0 - t) (alpha0 - alpha)) hxi
  filter_upwards [henv, hKest] with om hen hest
  obtain ⟨B, hB, hBN⟩ := hen
  refine ⟨B, hB, fun N => ?_⟩
  have hKB : K N om ≤ B * (3 : ℝ) ^ (theta * min (t0 - t) (alpha0 - alpha) * (N : ℝ)) :=
    (le_abs_self _).trans (hBN N)
  intro F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol
  obtain ⟨hen2, hhol⟩ := hest N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol
  have hc0 : 0 ≤ Kf + Cphi :=
    add_nonneg hKf ((aux_prop_growth_c2Norm_nonneg _ phi).trans hCphi)
  constructor
  · intro x rad hx hr hr1 hrN
    exact aux_lem_as_regularity_unit_energy_absorb _ (K N om) B (Kf + Cphi)
      (theta * min (t0 - t) (alpha0 - alpha)) theta t t0 rad N hB hKB ht0
      (mul_le_mul_of_nonneg_left (min_le_left _ _) htheta.le) hr hrN
      (hen2 x rad hx hr hr1)
  · obtain ⟨U, hUc, hUae, hUh, hUn⟩ := hhol
    refine ⟨U, hUc, hUae, fun x hx y hy hxy => ?_⟩
    have hpair := aux_lem_as_regularity_unit_holder_pair alpha0 (K N om * (Kf + Cphi))
      (by linarith) _ U hUh hUn x y hx hy
    exact aux_lem_as_regularity_unit_holder_absorb _ (K N om) B (Kf + Cphi)
      (theta * min (t0 - t) (alpha0 - alpha)) theta alpha alpha0 _ N hB hc0 hKB hal hal0
      (mul_le_mul_of_nonneg_left (min_le_right _ _) htheta.le) (Real.sqrt_nonneg _) hxy
      hpair

/-- Neumann small-radius half, stated for any finite-cutoff witness with the exact
shape of the `cor_neumann_source` conclusion at the stronger exponents `t0, alpha0`
(so it is consumed whichever carried inputs feed `cor_neumann_source`). -/
theorem aux_lem_as_regularity_unit_neumann_small_radius
    (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (alpha alpha0 t t0 : ℝ)
    (hal : 0 < alpha)
    (hal0 : alpha < alpha0)
    (ht0 : t < t0)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hcutoffEnvelope :
        ∀ (p C : ℝ),
          1 ≤ p →
          0 ≤ C →
          ∀ (Kcut : ℕ → BilateralField d → ℝ),
            (∀ N : ℕ,
              MemLp (Kcut N) (ENNReal.ofReal p)
                (chaosSampleLaw M).toMeasure) →
            (∀ N : ℕ,
              eLpNorm (Kcut N) (ENNReal.ofReal p)
                (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal C) →
            ∀ (xi : ℝ),
              0 < xi →
              ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                ∃ B : ℝ, 0 < B ∧
                  ∀ N : ℕ,
                    |Kcut N omega| ≤ B * (3 : ℝ) ^ (xi * (N : ℝ)))
    (K : ℕ → BilateralField d → ℝ) (p Cb : ℝ) (hp : 1 ≤ p)
    (hKmem : ∀ N : ℕ, MemLp (K N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure)
    (hKnorm : ∀ N : ℕ,
      eLpNorm (K N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cb)
    (hKest : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ)
          (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
          (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x) = 0 →
        ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
          SolvesNeumann
              (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos) F v →
          (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
            IsHolderOn alpha0
                (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                  Set (SpatialCoordinates d)) U ∧
            ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] U ∧
            cAlphaNorm alpha0
                (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                  Set (SpatialCoordinates d)) U ≤ K N om * Kf) ∧
          (∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ unitNeumannCube d →
            0 < rad → rad ≤ 1 →
            localGradientEnergy
                (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
                (s := Metric.ball x rad ∩
                  (unitNeumannCube d : Set (SpatialCoordinates d)))
                (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
                (sobolevGradient (v : SobolevData (unitNeumannCube d))) ≤
              K N om * Kf ^ 2 * rad ^ t0))
    (theta : ℝ) (htheta : 0 < theta) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ B : ℝ, 0 < B ∧
      ∀ N : ℕ,
        ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
          (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x) = 0 →
          ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
            SolvesNeumann
                (cutoffPositiveCoefficient M H omega N
                  (fun _ => (1 / 2 : ℝ)) one_pos) F v →
            (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
              ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] U ∧
              ∀ x ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                  Set (SpatialCoordinates d)),
              ∀ y ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                  Set (SpatialCoordinates d)),
                Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤
                  (3 : ℝ) ^ (-(theta * (N : ℝ))) →
                |U x - U y| ≤
                  B * Kf * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha) ∧
            (∀ (x : SpatialCoordinates d) (rad : ℝ),
              x ∈ unitNeumannCube d → 0 < rad → rad ≤ 1 →
              rad ≤ (3 : ℝ) ^ (-(theta * (N : ℝ))) →
              localGradientEnergy
                (cutoffPositiveCoefficient M H omega N
                  (fun _ => (1 / 2 : ℝ)) one_pos)
                (s := Metric.ball x rad ∩
                  (unitNeumannCube d : Set (SpatialCoordinates d)))
                (isOpen_ball.measurableSet.inter
                  (unitNeumannCube d).isOpen.measurableSet)
                (sobolevGradient (v : SobolevData (unitNeumannCube d))) ≤
                  B * Kf ^ 2 * rad ^ t) := by
  have hxi : 0 < theta * min (t0 - t) (alpha0 - alpha) :=
    mul_pos htheta (lt_min (by linarith) (by linarith))
  have henv := hcutoffEnvelope p (max Cb 0) hp (le_max_right _ _) K hKmem
    (fun N => (hKnorm N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
    (theta * min (t0 - t) (alpha0 - alpha)) hxi
  filter_upwards [henv, hKest] with om hen hest
  obtain ⟨B, hB, hBN⟩ := hen
  refine ⟨B, hB, fun N => ?_⟩
  have hKB : K N om ≤ B * (3 : ℝ) ^ (theta * min (t0 - t) (alpha0 - alpha) * (N : ℝ)) :=
    (le_abs_self _).trans (hBN N)
  intro F Kf hKf hFm hFb hint v hsol
  obtain ⟨hhol, hen2⟩ := hest N F Kf hKf hFm hFb hint v hsol
  constructor
  · obtain ⟨U, hUc, hUh, hUae, hUn⟩ := hhol
    refine ⟨U, hUc, hUae, fun x hx y hy hxy => ?_⟩
    have hpair := aux_lem_as_regularity_unit_holder_pair alpha0 (K N om * Kf)
      (by linarith) _ U hUh hUn x y hx hy
    exact aux_lem_as_regularity_unit_holder_absorb _ (K N om) B Kf
      (theta * min (t0 - t) (alpha0 - alpha)) theta alpha alpha0 _ N hB hKf hKB hal hal0
      (mul_le_mul_of_nonneg_left (min_le_right _ _) htheta.le) (Real.sqrt_nonneg _) hxy
      hpair
  · intro x rad hx hr hr1 hrN
    exact aux_lem_as_regularity_unit_energy_absorb _ (K N om) B Kf
      (theta * min (t0 - t) (alpha0 - alpha)) theta t t0 rad N hB hKB ht0
      (mul_le_mul_of_nonneg_left (min_le_left _ _) htheta.le) hr hrN
      (hen2 x rad hx hr hr1)

/-! ## Large-radius estimates and final assembly

The small-radius estimates and the large-radius estimates
`r ≥ r_N := 3^{-θN}` give a single random constant for the required oscillation
and energy bounds at all radii `r ≥ r_N := 3^{-θN}`. The five
`aux_lem_as_regularity_unit_lr_*` clauses are proved by the Dirichlet/Neumann
suppliers named below, and the connectors assemble them with the small-radius
estimates into `lem_as_regularity_unit`.

A plain supremum bound does not give a uniform large-radius oscillation
constant: the inequality
`2·Sup/rN^alpha · dist^alpha ≥ 2·Sup ≥ |U x - U y|` for `dist ≥ rN`
uses the constant `2·Sup/rN^alpha`, which diverges as
`rN = 3^{-θN} → 0`. The deterministic iteration controls this constant.
The large-radius oscillation estimate therefore uses `dist ≥ rN` directly,
in place of the small-radius condition `dist ≤ rN`. The separate point-value
estimate, recovered by averaging at radius `r_N`, supplies the supremum term
of `cAlphaNorm`.

The reusable `aux_lem_as_regularity_unit_neumann_small_radius` estimate is
generic in its moment bank (`K, Cb, hKmem, hKnorm, hKest`). The corresponding
supplier `cor_neumann_source` carries
`D : deterministic_good_scale_input d ⟨..⟩`, whereas this principal
statement does not carry `D`. Accordingly, that reusable estimate is not the
route used by the principal proof. The clauses `lr_neumann_holder` and
`lr_neumann_energy` instead give the full per-cutoff Neumann conclusions,
covering both small and large radii.
-/

/-- Combine a near-pair Hölder oscillation bound (distance `≤ rN`, from the
small-radius half) with a far-pair bound (distance `≥ rN`, from a large-radius
estimate below) into one bound valid for every pair, with constant `max Anear
Afar`. Pure case split on `le_total dist rN`, no new analytic content. -/
theorem aux_lem_as_regularity_unit_combine_near_far {d : ℕ}
    (alpha rN Anear Afar : ℝ)
    (U : SpatialCoordinates d → ℝ) (x y : SpatialCoordinates d)
    (hnear : Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ rN →
      |U x - U y| ≤ Anear * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha)
    (hfar : rN ≤ Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) →
      |U x - U y| ≤ Afar * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha) :
    |U x - U y| ≤ max Anear Afar * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha := by
  have hnn : (0:ℝ) ≤ (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha :=
    Real.rpow_nonneg (Real.sqrt_nonneg _) _
  rcases le_total (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) rN with h | h
  · exact (hnear h).trans (mul_le_mul_of_nonneg_right (le_max_left Anear Afar) hnn)
  · exact (hfar h).trans (mul_le_mul_of_nonneg_right (le_max_right Anear Afar) hnn)

/-- Combine a near-radius energy bound (`rad ≤ rN`, from the small-radius half)
with a far-radius bound (`rad ≥ rN`, from a large-radius estimate below) into one
bound valid for every radius, with constant `max Bnear Bfar`. Pure case split
on `le_total rad rN`. -/
theorem aux_lem_as_regularity_unit_combine_energy
    (t rN rad c Bnear Bfar En : ℝ) (hrad0 : 0 ≤ rad)
    (hnear : rad ≤ rN → En ≤ Bnear * c ^ 2 * rad ^ t)
    (hfar : rN ≤ rad → En ≤ Bfar * c ^ 2 * rad ^ t) :
    En ≤ max Bnear Bfar * c ^ 2 * rad ^ t := by
  have hcr : (0:ℝ) ≤ c ^ 2 * rad ^ t := mul_nonneg (sq_nonneg c) (Real.rpow_nonneg hrad0 t)
  rcases le_total rad rN with h | h
  · have h1 := hnear h
    have h2 : Bnear * c ^ 2 * rad ^ t ≤ max Bnear Bfar * c ^ 2 * rad ^ t := by
      calc Bnear * c ^ 2 * rad ^ t = Bnear * (c ^ 2 * rad ^ t) := by ring
        _ ≤ max Bnear Bfar * (c ^ 2 * rad ^ t) :=
              mul_le_mul_of_nonneg_right (le_max_left Bnear Bfar) hcr
        _ = max Bnear Bfar * c ^ 2 * rad ^ t := by ring
    linarith
  · have h1 := hfar h
    have h2 : Bfar * c ^ 2 * rad ^ t ≤ max Bnear Bfar * c ^ 2 * rad ^ t := by
      calc Bfar * c ^ 2 * rad ^ t = Bfar * (c ^ 2 * rad ^ t) := by ring
        _ ≤ max Bnear Bfar * (c ^ 2 * rad ^ t) :=
              mul_le_mul_of_nonneg_right (le_max_right Bnear Bfar) hcr
        _ = max Bnear Bfar * c ^ 2 * rad ^ t := by ring
    linarith

/-- Upgrade a bound with constant `B` to any larger constant `K`, linear case
(`K*c`, `c ≥ 0`). Pure monotonicity, no new analytic content. -/
theorem aux_lem_as_regularity_unit_upgrade_lin
    (B K c v : ℝ) (hBK : B ≤ K) (hc : 0 ≤ c) (hv : v ≤ B * c) : v ≤ K * c :=
  hv.trans (mul_le_mul_of_nonneg_right hBK hc)

/-- Upgrade a bound with constant `B` to any larger constant `K`, three-factor
case (`K*c*e`, `c,e ≥ 0`); reused for both the energy bounds (`c = data^2`,
`e = rad^t`) and the oscillation bounds (`c = data`, `e = dist^alpha`). Pure
monotonicity, no new analytic content. -/
theorem aux_lem_as_regularity_unit_upgrade_osc
    (B K c e v : ℝ) (hBK : B ≤ K) (hc : 0 ≤ c) (he : 0 ≤ e)
    (hv : v ≤ B * c * e) : v ≤ K * c * e := by
  have hce : (0:ℝ) ≤ c * e := mul_nonneg hc he
  calc v ≤ B * c * e := hv
    _ = B * (c * e) := by ring
    _ ≤ K * (c * e) := mul_le_mul_of_nonneg_right hBK hce
    _ = K * c * e := by ring




/-- Dirichlet representatives have a common sup bound on the closed unit cube. -/
theorem aux_lem_as_regularity_unit_lr_dirichlet_sup
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pc : in_poincare d hd E) (Xc : in_extension d hd E)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sf : SobolevFoundationalInput d hd)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd) :
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M)
      (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ B : ℝ, 0 < B ∧
        ∀ N : ℕ,
          ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
            AEMeasurable F
              (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
            (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
              |F x| ≤ Kf) →
            ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
              ContDiff ℝ 2 phi →
              c2Norm
                  (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                    Set (SpatialCoordinates d)) phi ≤ Cphi →
              ∀ (b u : weakSobolevGraph (unitNeumannCube d)),
                ((b : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
                  =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))]
                    phi →
                SolvesDirichlet
                    (cutoffPositiveCoefficient M H omega N
                      (fun _ => (1 / 2 : ℝ)) one_pos) F b u →
                ∀ U : SpatialCoordinates d → ℝ, Continuous U →
                  ((u : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
                    =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] U →
                  ∀ x ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                      Set (SpatialCoordinates d)),
                    |U x| ≤ B * (Kf + Cphi) := by
  exact lem_as_regularity_unit_sup d hd E Pc Xc W Cp Sf D Step Dbase Interp

/-! ### A cutoff-uniform Neumann moment bound

The two conclusions use the same almost-sure random constant to control
both the Hölder seminorm and the local gradient energy of the mean-zero
Neumann solution for every cutoff. The macro-scale growth, coarse bounds
and envelope estimates supply the uniformity through deterministic
iteration. A local ellipticity estimate at a single cutoff does not alone
supply a constant uniform in the cutoff. -/
/-- One almost-sure constant controls both Neumann regularity estimates at every cutoff. -/
theorem aux_lem_as_regularity_unit_uniform_bank
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pc : in_poincare d hd E) (Xc : in_extension d hd E)
    (W : SmallPerturbationInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Cp : CampanatoInput d)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (Sf : SobolevFoundationalInput d hd) (t alpha : ℝ)
    (ht1 : (d : ℝ) - 1 < t) (ht2 : t < (d : ℝ))
    (hal : 0 < alpha) (hal1 : alpha < 1) :
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M)
      (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ B : ℝ, 0 < B ∧
        ∀ N : ℕ,
          ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
            AEMeasurable F
              (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
            (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
              |F x| ≤ Kf) →
            (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x) = 0 →
            ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
              SolvesNeumann
                  (cutoffPositiveCoefficient M H omega N
                    (fun _ => (1 / 2 : ℝ)) one_pos) F v →
              (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
                IsHolderOn alpha
                    (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                      Set (SpatialCoordinates d)) U ∧
                ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
                    =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] U ∧
                cAlphaNorm alpha
                    (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                      Set (SpatialCoordinates d)) U ≤ B * Kf) ∧
              (∀ (x : SpatialCoordinates d) (rad : ℝ),
                x ∈ unitNeumannCube d → 0 < rad → rad ≤ 1 →
                localGradientEnergy
                    (cutoffPositiveCoefficient M H omega N
                      (fun _ => (1 / 2 : ℝ)) one_pos)
                    (s := Metric.ball x rad ∩
                      (unitNeumannCube d : Set (SpatialCoordinates d)))
                    (isOpen_ball.measurableSet.inter
                      (unitNeumannCube d).isOpen.measurableSet)
                    (sobolevGradient (v : SobolevData (unitNeumannCube d))) ≤
                  B * Kf ^ 2 * rad ^ t) := by
  obtain ⟨de, hde, henergy⟩ := lem_as_regularity_neumann_energy d hd E Pc Xc W Cp Sf
    D Step Dbase Interp t ht1 ht2
  obtain ⟨dh, hdh, hholder⟩ := lem_as_regularity_neumann_holder d hd E Pc Xc W Cp Sf
    D Step Dbase Interp alpha hal hal1
  refine ⟨min de dh, lt_min hde hdh, ?_⟩
  intro M Rm Sreg It H hIR hdelta
  filter_upwards [henergy M Rm Sreg It H hIR (hdelta.trans (min_le_left _ _)),
    hholder M Rm Sreg It H hIR (hdelta.trans (min_le_right _ _))] with omega he hh
  obtain ⟨Ke, hKe, he⟩ := he
  obtain ⟨Kh, hKh, hh⟩ := hh
  refine ⟨Ke + Kh, add_pos hKe hKh, ?_⟩
  intro N F Kf hKf hF hFb hF0 v hv
  constructor
  · obtain ⟨U, hUc, hUh, hUae, hUn⟩ := hh N F Kf hKf hF hFb hF0 v hv
    refine ⟨U, hUc, hUh, hUae, hUn.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hKe.le) hKf
  · intro x rad hx hrad hrad1
    exact (he N F Kf hKf hF hFb hF0 v hv x hx rad hrad hrad1).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hKh.le) (sq_nonneg Kf))
        (Real.rpow_nonneg hrad.le t))

/-- The uniform Neumann bank supplies the Holder bound. -/
theorem aux_lem_as_regularity_unit_lr_neumann_holder_D
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pc : in_poincare d hd E) (Xc : in_extension d hd E)
    (W : SmallPerturbationInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Cp : CampanatoInput d)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (Sf : SobolevFoundationalInput d hd) (alpha : ℝ) (hal : 0 < alpha) (hal1 : alpha < 1) :
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M)
      (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ B : ℝ, 0 < B ∧
        ∀ N : ℕ,
          ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
            AEMeasurable F
              (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
            (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
              |F x| ≤ Kf) →
            (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x) = 0 →
            ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
              SolvesNeumann
                  (cutoffPositiveCoefficient M H omega N
                    (fun _ => (1 / 2 : ℝ)) one_pos) F v →
              ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
                IsHolderOn alpha
                    (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                      Set (SpatialCoordinates d)) U ∧
                ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
                    =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] U ∧
                cAlphaNorm alpha
                    (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                      Set (SpatialCoordinates d)) U ≤ B * Kf := by
  obtain ⟨delta0, hdelta0, hbank⟩ :=
    aux_lem_as_regularity_unit_uniform_bank d hd E Pc Xc W D Cp Step Dbase Interp Sf
      ((d : ℝ) - 1 / 2) alpha (by linarith) (by linarith) hal hal1
  refine ⟨delta0, hdelta0, fun M Rm Sreg It H hH hdelta => ?_⟩
  filter_upwards [hbank M Rm Sreg It H hH hdelta] with omega hB
  obtain ⟨B, hBpos, hall⟩ := hB
  exact ⟨B, hBpos, fun N F Kf hKf hFm hFb hint v hsol =>
    (hall N F Kf hKf hFm hFb hint v hsol).1⟩

/-- The uniform Neumann bank supplies local energy decay. -/
theorem aux_lem_as_regularity_unit_lr_neumann_energy_D
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pc : in_poincare d hd E) (Xc : in_extension d hd E)
    (W : SmallPerturbationInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Cp : CampanatoInput d)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (Sf : SobolevFoundationalInput d hd) (t : ℝ)
    (ht1 : (d : ℝ) - 1 < t) (ht2 : t < (d : ℝ)) :
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M)
      (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ B : ℝ, 0 < B ∧
        ∀ N : ℕ,
          ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
            AEMeasurable F
              (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
            (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
              |F x| ≤ Kf) →
            (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x) = 0 →
            ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
              SolvesNeumann
                  (cutoffPositiveCoefficient M H omega N
                    (fun _ => (1 / 2 : ℝ)) one_pos) F v →
              ∀ (x : SpatialCoordinates d) (rad : ℝ),
                x ∈ unitNeumannCube d → 0 < rad → rad ≤ 1 →
                localGradientEnergy
                    (cutoffPositiveCoefficient M H omega N
                      (fun _ => (1 / 2 : ℝ)) one_pos)
                    (s := Metric.ball x rad ∩
                      (unitNeumannCube d : Set (SpatialCoordinates d)))
                    (isOpen_ball.measurableSet.inter
                      (unitNeumannCube d).isOpen.measurableSet)
                    (sobolevGradient (v : SobolevData (unitNeumannCube d))) ≤
                  B * Kf ^ 2 * rad ^ t := by
  obtain ⟨delta0, hdelta0, hbank⟩ :=
    aux_lem_as_regularity_unit_uniform_bank d hd E Pc Xc W D Cp Step Dbase Interp Sf
      t (1 / 2) ht1 ht2 (by norm_num) (by norm_num)
  refine ⟨delta0, hdelta0, fun M Rm Sreg It H hH hdelta => ?_⟩
  filter_upwards [hbank M Rm Sreg It H hH hdelta] with omega hB
  obtain ⟨B, hBpos, hall⟩ := hB
  exact ⟨B, hBpos, fun N F Kf hKf hFm hFb hint v hsol x rad hx hrad hrad1 =>
    (hall N F Kf hKf hFm hFb hint v hsol).2 x rad hx hrad hrad1⟩

/-- The all-radius Dirichlet energy estimate supplies the large-radius clause. -/
theorem aux_lem_as_regularity_unit_lr_dirichlet_energy
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pc : in_poincare d hd E) (Xc : in_extension d hd E)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sf : SobolevFoundationalInput d hd)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd) (t : ℝ)
    (ht1 : (d : ℝ) - 1 < t) (ht2 : t < (d : ℝ)) :
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M)
      (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ theta : ℝ, 0 < theta →
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ B : ℝ, 0 < B ∧
        ∀ N : ℕ,
          ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
            AEMeasurable F
              (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
            (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
              |F x| ≤ Kf) →
            ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
              ContDiff ℝ 2 phi →
              c2Norm
                  (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                    Set (SpatialCoordinates d)) phi ≤ Cphi →
              ∀ (b u : weakSobolevGraph (unitNeumannCube d)),
                ((b : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
                  =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))]
                    phi →
                SolvesDirichlet
                    (cutoffPositiveCoefficient M H omega N
                      (fun _ => (1 / 2 : ℝ)) one_pos) F b u →
                ∀ (x : SpatialCoordinates d) (rad : ℝ),
                  x ∈ unitNeumannCube d → 0 < rad → rad ≤ 1 →
                  (3 : ℝ) ^ (-(theta * (N : ℝ))) ≤ rad →
                  localGradientEnergy
                      (cutoffPositiveCoefficient M H omega N
                        (fun _ => (1 / 2 : ℝ)) one_pos)
                      (s := Metric.ball x rad ∩
                        (unitNeumannCube d : Set (SpatialCoordinates d)))
                      (isOpen_ball.measurableSet.inter
                        (unitNeumannCube d).isOpen.measurableSet)
                      (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤
                    B * (Kf + Cphi) ^ 2 * rad ^ t := by
  obtain ⟨delta0,hdelta0,henergy⟩ := lem_as_regularity_dirichlet_energy
    d hd E Pc Xc W Cp Sf D Step Dbase Interp t ht1 ht2
  refine ⟨delta0,hdelta0,?_⟩
  intro M Rm Sreg It H hIR hdelta theta htheta
  filter_upwards [henergy M Rm Sreg It H hIR hdelta] with omega ho
  obtain ⟨B,hB,ho⟩ := ho
  refine ⟨B,hB,?_⟩
  intro N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol x rad hx hrad hrad1 hlarge
  exact ho N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol x hx rad hrad

/-- The uniform Dirichlet Holder estimate supplies the large-distance clause. -/
theorem aux_lem_as_regularity_unit_lr_dirichlet_oscillation
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pc : in_poincare d hd E) (Xc : in_extension d hd E)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sf : SobolevFoundationalInput d hd)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (alpha : ℝ) (hal : 0 < alpha) (hal1 : alpha < 1) :
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M)
      (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ theta : ℝ, 0 < theta →
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ B : ℝ, 0 < B ∧
        ∀ N : ℕ,
          ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
            AEMeasurable F
              (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
            (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
              |F x| ≤ Kf) →
            ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
              ContDiff ℝ 2 phi →
              c2Norm
                  (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                    Set (SpatialCoordinates d)) phi ≤ Cphi →
              ∀ (b u : weakSobolevGraph (unitNeumannCube d)),
                ((b : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
                  =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))]
                    phi →
                SolvesDirichlet
                    (cutoffPositiveCoefficient M H omega N
                      (fun _ => (1 / 2 : ℝ)) one_pos) F b u →
                ∀ U : SpatialCoordinates d → ℝ, Continuous U →
                  ((u : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
                    =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] U →
                  ∀ x ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                      Set (SpatialCoordinates d)),
                  ∀ y ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                      Set (SpatialCoordinates d)),
                    (3 : ℝ) ^ (-(theta * (N : ℝ))) ≤
                        Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) →
                    |U x - U y| ≤
                      B * (Kf + Cphi) *
                        (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha := by
  obtain ⟨delta0,hd0,hh⟩ := lem_as_regularity_dirichlet_holder d hd E Pc Xc W Cp Sf D Step Dbase Interp alpha hal hal1
  refine ⟨delta0,hd0,?_⟩
  intro M Rm Sreg It H hIR hdelta theta htheta
  filter_upwards [hh M Rm Sreg It H hIR hdelta] with omega h
  obtain ⟨B,hB,h⟩ := h
  refine ⟨B,hB,?_⟩
  intro N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol U hU hrep x hx y hy hdist
  exact h N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol U hU hrep x hx y hy

/-! ### Assembling the two per-cutoff clauses for one common constant `K`

Pure combination lemmas: fix `M, H, omega, N` (and, for Dirichlet, `theta`),
take the small-radius closed result together with the relevant large-radius
results each already specialised to `(M, H, omega, N)`, and produce the full
per-cutoff clause of the statement for one constant `K` dominating
every piece. No new analytic content — `le_total` case splits, the two
`upgrade_*` monotonicity lemmas, and `cAlphaNorm_of_pairs`. -/

/-- Assemble the Dirichlet clause. `K` must dominate `Ben, Bsr` outright
(energy: no sum) and `Bsup, Bsr, Bosc` at half strength (Hölder: `cAlphaNorm`
sums a sup term and a seminorm term, `K/2 + K/2 = K`). -/
theorem aux_lem_as_regularity_unit_dirichlet_clause
    (d : ℕ) (_hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ)
    (alpha t theta K Bsr Bsup Bosc Ben : ℝ)
    (hK : 0 < K)
    (hBsrK : Bsr ≤ K / 2) (hBsupK : Bsup ≤ K / 2) (hBoscK : Bosc ≤ K / 2)
    (hBenK : Ben ≤ K / 2)
    (hsr : ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
        AEMeasurable F (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
              Set (SpatialCoordinates d)) phi ≤ Cphi →
          ∀ (b u : weakSobolevGraph (unitNeumannCube d)),
            ((b : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] phi →
            SolvesDirichlet (cutoffPositiveCoefficient M H omega N
                (fun _ => (1 / 2 : ℝ)) one_pos) F b u →
            (∀ (x : SpatialCoordinates d) (rad : ℝ),
              x ∈ unitNeumannCube d → 0 < rad → rad ≤ 1 →
              rad ≤ (3 : ℝ) ^ (-(theta * (N : ℝ))) →
              localGradientEnergy (cutoffPositiveCoefficient M H omega N
                  (fun _ => (1 / 2 : ℝ)) one_pos)
                (s := Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
                (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
                (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤
                  Bsr * (Kf + Cphi) ^ 2 * rad ^ t) ∧
            (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
              ((u : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] U ∧
              ∀ x ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                  Set (SpatialCoordinates d)),
              ∀ y ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                  Set (SpatialCoordinates d)),
                Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ (3 : ℝ) ^ (-(theta * (N : ℝ))) →
                |U x - U y| ≤
                  Bsr * (Kf + Cphi) * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha))
    (hsup : ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
        AEMeasurable F (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
              Set (SpatialCoordinates d)) phi ≤ Cphi →
          ∀ (b u : weakSobolevGraph (unitNeumannCube d)),
            ((b : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] phi →
            SolvesDirichlet (cutoffPositiveCoefficient M H omega N
                (fun _ => (1 / 2 : ℝ)) one_pos) F b u →
            ∀ U : SpatialCoordinates d → ℝ, Continuous U →
              ((u : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] U →
              ∀ x ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                  Set (SpatialCoordinates d)),
                |U x| ≤ Bsup * (Kf + Cphi))
    (hosc : ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
        AEMeasurable F (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
              Set (SpatialCoordinates d)) phi ≤ Cphi →
          ∀ (b u : weakSobolevGraph (unitNeumannCube d)),
            ((b : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] phi →
            SolvesDirichlet (cutoffPositiveCoefficient M H omega N
                (fun _ => (1 / 2 : ℝ)) one_pos) F b u →
            ∀ U : SpatialCoordinates d → ℝ, Continuous U →
              ((u : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] U →
              ∀ x ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                  Set (SpatialCoordinates d)),
              ∀ y ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                  Set (SpatialCoordinates d)),
                (3 : ℝ) ^ (-(theta * (N : ℝ))) ≤ Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) →
                |U x - U y| ≤
                  Bosc * (Kf + Cphi) * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha)
    (hen : ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
        AEMeasurable F (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
              Set (SpatialCoordinates d)) phi ≤ Cphi →
          ∀ (b u : weakSobolevGraph (unitNeumannCube d)),
            ((b : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] phi →
            SolvesDirichlet (cutoffPositiveCoefficient M H omega N
                (fun _ => (1 / 2 : ℝ)) one_pos) F b u →
            ∀ (x : SpatialCoordinates d) (rad : ℝ),
              x ∈ unitNeumannCube d → 0 < rad → rad ≤ 1 →
              (3 : ℝ) ^ (-(theta * (N : ℝ))) ≤ rad →
              localGradientEnergy (cutoffPositiveCoefficient M H omega N
                  (fun _ => (1 / 2 : ℝ)) one_pos)
                (s := Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
                (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
                (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤
                  Ben * (Kf + Cphi) ^ 2 * rad ^ t) :
    ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
      AEMeasurable F (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
      (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
      ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
        ContDiff ℝ 2 phi →
        c2Norm (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
            Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (unitNeumannCube d)),
          ((b : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M H omega N
              (fun _ => (1 / 2 : ℝ)) one_pos) F b u →
          (∀ (x : SpatialCoordinates d) (rad : ℝ),
            x ∈ unitNeumannCube d → 0 < rad → rad ≤ 1 →
            localGradientEnergy (cutoffPositiveCoefficient M H omega N
                (fun _ => (1 / 2 : ℝ)) one_pos)
              (s := Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
              (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
              (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤
                K * (Kf + Cphi) ^ 2 * rad ^ t) ∧
          (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
            ((u : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] U ∧
            IsHolderOn alpha (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                Set (SpatialCoordinates d)) U ∧
            cAlphaNorm alpha (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                Set (SpatialCoordinates d)) U ≤ K * (Kf + Cphi)) := by
  intro F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol
  obtain ⟨hEnear, U, hUc, hUae, hUnear⟩ := hsr F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol
  have hc0 : 0 ≤ Kf + Cphi :=
    add_nonneg hKf ((aux_prop_growth_c2Norm_nonneg _ phi).trans hCphi)
  have hSup := hsup F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol U hUc hUae
  have hFarOsc := hosc F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol U hUc hUae
  refine ⟨?_, U, hUc, hUae, ?_⟩
  · intro x rad hx hr hr1
    have hcomb := aux_lem_as_regularity_unit_combine_energy t
      ((3 : ℝ) ^ (-(theta * (N : ℝ)))) rad (Kf + Cphi) Bsr Ben
      (localGradientEnergy (cutoffPositiveCoefficient M H omega N
          (fun _ => (1 / 2 : ℝ)) one_pos)
        (s := Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
        (sobolevGradient (u : SobolevData (unitNeumannCube d))))
      hr.le
      (fun hle => hEnear x rad hx hr hr1 hle)
      (fun hge => hen F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol x rad hx hr hr1 hge)
    exact aux_lem_as_regularity_unit_upgrade_osc (max Bsr Ben) K ((Kf + Cphi) ^ 2) (rad ^ t) _
      (max_le (hBsrK.trans (by linarith)) (hBenK.trans (by linarith)))
      (sq_nonneg _) (Real.rpow_nonneg hr.le t) hcomb
  · have hpair : ∀ x ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
        Set (SpatialCoordinates d)),
      ∀ y ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)),
        |U x - U y| ≤ (K / 2) * (Kf + Cphi) *
          (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha := by
      intro x hx y hy
      have he : (0 : ℝ) ≤ (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha :=
        Real.rpow_nonneg (Real.sqrt_nonneg _) alpha
      rcases le_total (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))
          ((3 : ℝ) ^ (-(theta * (N : ℝ)))) with h | h
      · exact aux_lem_as_regularity_unit_upgrade_osc Bsr (K / 2) (Kf + Cphi) _ _
          hBsrK hc0 he (hUnear x hx y hy h)
      · exact aux_lem_as_regularity_unit_upgrade_osc Bosc (K / 2) (Kf + Cphi) _ _
          hBoscK hc0 he (hFarOsc x hx y hy h)
    have hsupK : ∀ x ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
        Set (SpatialCoordinates d)), |U x| ≤ (K / 2) * (Kf + Cphi) :=
      fun x hx => aux_lem_as_regularity_unit_upgrade_lin Bsup (K / 2) (Kf + Cphi) |U x|
        hBsupK hc0 (hSup x hx)
    have hcAP := aux_lem_as_regularity_unit_cAlphaNorm_of_pairs (d := d) alpha
      ((K / 2) * (Kf + Cphi)) ((K / 2) * (Kf + Cphi))
      (mul_nonneg (by linarith) hc0) (mul_nonneg (by linarith) hc0)
      (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)) U
      hsupK hpair
    refine ⟨hcAP.1, ?_⟩
    have heq : (K / 2) * (Kf + Cphi) + (K / 2) * (Kf + Cphi) = K * (Kf + Cphi) := by ring
    exact heq ▸ hcAP.2

/-- Assemble the Neumann clause. Both large-radius results (`lr_neumann_holder`,
`lr_neumann_energy`) already give the full per-cutoff conclusion directly (no
near/far split, no sum in the Hölder bound since `cAlphaNorm` is bundled as
one clause by `cor_neumann_source`'s own shape), so this is a plain two-piece
`K`-upgrade, no `cAlphaNorm_of_pairs` needed. -/
theorem aux_lem_as_regularity_unit_neumann_clause
    (d : ℕ) (_hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ)
    (alpha t K Bnhol Bnen : ℝ) (_hK : 0 < K) (hBnholK : Bnhol ≤ K) (hBnenK : Bnen ≤ K)
    (hnhol : ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
        AEMeasurable F (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
        (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x) = 0 →
        ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
          SolvesNeumann (cutoffPositiveCoefficient M H omega N
              (fun _ => (1 / 2 : ℝ)) one_pos) F v →
          ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
            IsHolderOn alpha (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                Set (SpatialCoordinates d)) U ∧
            ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] U ∧
            cAlphaNorm alpha (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                Set (SpatialCoordinates d)) U ≤ Bnhol * Kf)
    (hnen : ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
        AEMeasurable F (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
        (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x) = 0 →
        ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
          SolvesNeumann (cutoffPositiveCoefficient M H omega N
              (fun _ => (1 / 2 : ℝ)) one_pos) F v →
          ∀ (x : SpatialCoordinates d) (rad : ℝ),
            x ∈ unitNeumannCube d → 0 < rad → rad ≤ 1 →
            localGradientEnergy (cutoffPositiveCoefficient M H omega N
                (fun _ => (1 / 2 : ℝ)) one_pos)
              (s := Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
              (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
              (sobolevGradient (v : SobolevData (unitNeumannCube d))) ≤
                Bnen * Kf ^ 2 * rad ^ t) :
    ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
      AEMeasurable F (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
      (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
      (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x) = 0 →
      ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
        SolvesNeumann (cutoffPositiveCoefficient M H omega N
            (fun _ => (1 / 2 : ℝ)) one_pos) F v →
        (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
          IsHolderOn alpha (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
              Set (SpatialCoordinates d)) U ∧
          ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] U ∧
          cAlphaNorm alpha (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
              Set (SpatialCoordinates d)) U ≤ K * Kf) ∧
        (∀ (x : SpatialCoordinates d) (rad : ℝ),
          x ∈ unitNeumannCube d → 0 < rad → rad ≤ 1 →
          localGradientEnergy (cutoffPositiveCoefficient M H omega N
              (fun _ => (1 / 2 : ℝ)) one_pos)
            (s := Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
            (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
            (sobolevGradient (v : SobolevData (unitNeumannCube d))) ≤
              K * Kf ^ 2 * rad ^ t) := by
  intro F Kf hKf hFm hFb hint v hsol
  obtain ⟨U, hUc, hUh, hUae, hUn⟩ := hnhol F Kf hKf hFm hFb hint v hsol
  refine ⟨⟨U, hUc, hUh, hUae,
      aux_lem_as_regularity_unit_upgrade_lin Bnhol K Kf
        (cAlphaNorm alpha (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
          Set (SpatialCoordinates d)) U) hBnholK hKf hUn⟩, ?_⟩
  intro x rad hx hr hr1
  exact aux_lem_as_regularity_unit_upgrade_osc Bnen K (Kf ^ 2) (rad ^ t) _
    hBnenK (sq_nonneg _) (Real.rpow_nonneg hr.le t)
    (hnen F Kf hKf hFm hFb hint v hsol x rad hx hr hr1)

/-! ### Principal: `lem_as_regularity_unit`

Statement byte-identical to `lem_as_regularity_unit`
(fine refinement of `lem_as_regularity`). Fixes one
concrete `theta := 1` (all six suppliers below are universally quantified
over `theta` resp. hold outright, so any positive `theta` works — matching
how `aux_lem_as_regularity_unit_dirichlet_small_radius` is itself stated),
combines the six suppliers' `delta0`s by `min`, and for `K` uses
`2 * (1 + Bsr + Bsup + Bosc + Ben + Bnen + Bnhol)`: large enough that every
individual supplier constant is `≤ K` and, for the two Dirichlet Hölder
pieces (`Bsup`, and `max Bsr Bosc`) that get summed by `cAlphaNorm`, that
their sum is `≤ K` (via the `K/2 + K/2 = K` split in `dirichlet_clause`). -/
theorem lem_as_regularity_unit
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d)
    (Pc : in_poincare d hd E)
    (Xc : in_extension d hd E)
    (W : SmallPerturbationInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Cp : CampanatoInput d)
    (Sf : SobolevFoundationalInput d hd)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (alpha alpha0 t t0 : ℝ)
    (hal : 0 < alpha)
    (hal0 : alpha < alpha0)
    (hal1 : alpha0 < 1)
    (ht1 : (d : ℝ) - 1 < t)
    (ht0 : t < t0)
    (ht2 : t0 < (d : ℝ)) :
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (Rm : in_responses d M)
      (Sreg : in_6_16 d M)
      (It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H →
      M.delta ≤ min 1 delta0 →
      (hcutoffEnvelope :
        ∀ (p C : ℝ),
          1 ≤ p →
          0 ≤ C →
          ∀ (Kcut : ℕ → BilateralField d → ℝ),
            (∀ N : ℕ,
              MemLp (Kcut N) (ENNReal.ofReal p)
                (chaosSampleLaw M).toMeasure) →
            (∀ N : ℕ,
              eLpNorm (Kcut N) (ENNReal.ofReal p)
                (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal C) →
            ∀ (xi : ℝ),
              0 < xi →
              ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                ∃ B : ℝ, 0 < B ∧
                  ∀ N : ℕ,
                    |Kcut N omega| ≤ B * (3 : ℝ) ^ (xi * (N : ℝ))) →
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧
        ∀ N : ℕ,
          ((∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
              0 ≤ Kf →
              AEMeasurable F
                (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
              (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
                |F x| ≤ Kf) →
              ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
                ContDiff ℝ 2 phi →
                c2Norm
                    (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                      Set (SpatialCoordinates d)) phi ≤ Cphi →
                ∀ (b u : weakSobolevGraph (unitNeumannCube d)),
                  ((b : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
                    =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))]
                      phi →
                  SolvesDirichlet
                      (cutoffPositiveCoefficient M H omega N
                        (fun _ => (1 / 2 : ℝ)) one_pos) F b u →
                  (∀ (x : SpatialCoordinates d) (rad : ℝ),
                    x ∈ unitNeumannCube d → 0 < rad → rad ≤ 1 →
                    localGradientEnergy
                      (cutoffPositiveCoefficient M H omega N
                        (fun _ => (1 / 2 : ℝ)) one_pos)
                      (s := Metric.ball x rad ∩
                        (unitNeumannCube d : Set (SpatialCoordinates d)))
                      (isOpen_ball.measurableSet.inter
                        (unitNeumannCube d).isOpen.measurableSet)
                      (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤
                        K * (Kf + Cphi) ^ 2 * rad ^ t) ∧
                  (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
                    ((u : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
                      =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] U ∧
                    IsHolderOn alpha
                      (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                        Set (SpatialCoordinates d)) U ∧
                    cAlphaNorm alpha
                      (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                        Set (SpatialCoordinates d)) U ≤ K * (Kf + Cphi))) ∧
            (∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
              0 ≤ Kf →
              AEMeasurable F
                (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
              (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
                |F x| ≤ Kf) →
              (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x) = 0 →
              ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
                SolvesNeumann
                    (cutoffPositiveCoefficient M H omega N
                      (fun _ => (1 / 2 : ℝ)) one_pos) F v →
                (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
                  IsHolderOn alpha
                    (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                      Set (SpatialCoordinates d)) U ∧
                  ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
                    =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] U ∧
                  cAlphaNorm alpha
                    (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                      Set (SpatialCoordinates d)) U ≤ K * Kf) ∧
                (∀ (x : SpatialCoordinates d) (rad : ℝ),
                  x ∈ unitNeumannCube d → 0 < rad → rad ≤ 1 →
                  localGradientEnergy
                    (cutoffPositiveCoefficient M H omega N
                      (fun _ => (1 / 2 : ℝ)) one_pos)
                    (s := Metric.ball x rad ∩
                      (unitNeumannCube d : Set (SpatialCoordinates d)))
                    (isOpen_ball.measurableSet.inter
                      (unitNeumannCube d).isOpen.measurableSet)
                    (sobolevGradient (v : SobolevData (unitNeumannCube d))) ≤
                      K * Kf ^ 2 * rad ^ t))) := by
  obtain ⟨d1, hd1pos, hDsr⟩ :=
    aux_lem_as_regularity_unit_dirichlet_small_radius d hd E Pc Xc W Cp Sf alpha alpha0 t t0
      hal hal0 hal1 ht1 ht0 ht2
  obtain ⟨d2, hd2pos, hDsup⟩ := aux_lem_as_regularity_unit_lr_dirichlet_sup d hd E Pc Xc W Cp Sf D Step Dbase Interp
  have halt1 : alpha < 1 := hal0.trans hal1
  obtain ⟨d3, hd3pos, hDosc⟩ :=
    aux_lem_as_regularity_unit_lr_dirichlet_oscillation d hd E Pc Xc W Cp Sf D Step Dbase Interp alpha hal halt1
  have htlt : t < (d : ℝ) := ht0.trans ht2
  obtain ⟨d4, hd4pos, hDen⟩ :=
    aux_lem_as_regularity_unit_lr_dirichlet_energy d hd E Pc Xc W Cp Sf D Step Dbase Interp t ht1 htlt
  obtain ⟨d5, hd5pos, hNen⟩ :=
    aux_lem_as_regularity_unit_lr_neumann_energy_D d hd E Pc Xc W D Cp Step Dbase Interp Sf t ht1 htlt
  obtain ⟨d6, hd6pos, hNhol⟩ :=
    aux_lem_as_regularity_unit_lr_neumann_holder_D d hd E Pc Xc W D Cp Step Dbase Interp Sf alpha hal halt1
  refine ⟨min d1 (min d2 (min d3 (min d4 (min d5 d6)))),
    lt_min hd1pos (lt_min hd2pos (lt_min hd3pos (lt_min hd4pos (lt_min hd5pos hd6pos)))), ?_⟩
  intro M Rm Sreg It H hIR hdelta hcut
  set delta0 := min d1 (min d2 (min d3 (min d4 (min d5 d6)))) with hdelta0def
  have hd0 : M.delta ≤ delta0 := hdelta.trans (min_le_right 1 delta0)
  have hM1 : M.delta ≤ d1 := hd0.trans (min_le_left _ _)
  have hM2 : M.delta ≤ d2 := hd0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hM3 : M.delta ≤ d3 :=
    hd0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hM4 : M.delta ≤ d4 :=
    hd0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hM5 : M.delta ≤ d5 :=
    hd0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hM6 : M.delta ≤ d6 :=
    hd0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  have hDsr' := hDsr M Rm Sreg It H hIR hM1 hcut (1 : ℝ) zero_lt_one
  have hDsup' := hDsup M Rm Sreg It H hIR hM2
  have hDosc' := hDosc M Rm Sreg It H hIR hM3 (1 : ℝ) zero_lt_one
  have hDen' := hDen M Rm Sreg It H hIR hM4 (1 : ℝ) zero_lt_one
  have hNen' := hNen M Rm Sreg It H hIR hM5
  have hNhol' := hNhol M Rm Sreg It H hIR hM6
  filter_upwards [hDsr', hDsup', hDosc', hDen', hNen', hNhol']
    with omega hoDsr hoDsup hoDosc hoDen hoNen hoNhol
  obtain ⟨Bsr, hBsrpos, hoDsr'⟩ := hoDsr
  obtain ⟨Bsup, hBsuppos, hoDsup'⟩ := hoDsup
  obtain ⟨Bosc, hBoscpos, hoDosc'⟩ := hoDosc
  obtain ⟨Ben, hBenpos, hoDen'⟩ := hoDen
  obtain ⟨Bnen, hBnenpos, hoNen'⟩ := hoNen
  obtain ⟨Bnhol, hBnholpos, hoNhol'⟩ := hoNhol
  refine ⟨2 * (1 + Bsr + Bsup + Bosc + Ben + Bnen + Bnhol), by linarith, fun N => ?_⟩
  refine ⟨aux_lem_as_regularity_unit_dirichlet_clause d hd M H omega N alpha t (1 : ℝ)
      (2 * (1 + Bsr + Bsup + Bosc + Ben + Bnen + Bnhol)) Bsr Bsup Bosc Ben
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
      (hoDsr' N) (hoDsup' N) (hoDosc' N) (hoDen' N),
    aux_lem_as_regularity_unit_neumann_clause d hd M H omega N alpha t
      (2 * (1 + Bsr + Bsup + Bosc + Ben + Bnen + Bnhol)) Bnhol Bnen
      (by linarith) (by linarith) (by linarith)
      (hoNhol' N) (hoNen' N)⟩

end SubdiffusiveProcess.Paper
