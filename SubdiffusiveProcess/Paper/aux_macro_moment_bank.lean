import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Sobolev.BoundaryEnergy
import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Paper.coefficient_physical_identity
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.lem_coercivity
import SubdiffusiveProcess.Paper.lem_extension
import SubdiffusiveProcess.Paper.lem_infrared
import SubdiffusiveProcess.Paper.quadratic_inverse_response
import SubdiffusiveProcess.Lane2.CellDirichlet
import SubdiffusiveProcess.Paper.Foundations.Bank.Wave20
import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- **Non-vacuity check for the repaired conclusion (1/2).**  The `hKreference`
clause of `aux_macro_moment_bank` forces `1 ≤ Kmac N om` almost surely, for every
cutoff index `N`: the working cube contains its own centre, `3 ^ (t1 * Lmac) ≥ 1`
because `t1 > d - 1 ≥ 1 > 0`, and `exp |H om x| ≥ 1`.  The old conclusion had no
such consequence. -/
theorem aux_macro_moment_bank_one_le_of_reference
    {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (t1 : ℝ) (ht1 : 0 ≤ t1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (Lmac : ℕ → BilateralField d → ℕ) (Kmac : ℕ → BilateralField d → ℝ)
    (href : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ N x, x ∈ closedCube z r hr →
        (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)) * Real.exp (|H om x|) ≤ Kmac N om) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N, (1 : ℝ) ≤ Kmac N om := by
  filter_upwards [href] with om hom N
  have hz : z ∈ closedCube z r hr := Metric.mem_closedBall_self (by positivity)
  have hpow : (1 : ℝ) ≤ (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hexp : (1 : ℝ) ≤ Real.exp (|H om z|) := Real.one_le_exp (abs_nonneg _)
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)) * Real.exp (|H om z|) :=
        mul_le_mul hpow hexp (by norm_num) (by linarith)
    _ ≤ Kmac N om := hom N z hz



theorem aux_macro_moment_bank_zero_witness_fails
    {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (t1 : ℝ) (ht1 : 0 ≤ t1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (Lmac : ℕ → BilateralField d → ℕ) :
    ¬ (∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ N x, x ∈ closedCube z r hr →
          (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)) * Real.exp (|H om x|) ≤
            (fun (_ : ℕ) (_ : BilateralField d) => (0 : ℝ)) N om) := by
  intro href
  have hone :=
    aux_macro_moment_bank_one_le_of_reference M H t1 ht1 z r hr Lmac
      (fun (_ : ℕ) (_ : BilateralField d) => (0 : ℝ)) href
  obtain ⟨om, hom⟩ := hone.exists
  exact absurd (hom 0) (by norm_num)



theorem aux_aux_macro_moment_bank_one_le_Lmac_of_prefix
    {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M)
    (t1 : ℝ) (z : SpatialCoordinates d)
    (Lmac : ℕ → BilateralField d → ℕ)
    (hprefix : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N L0 : ℕ,
      ∃ L' : ℕ, L0 ≤ L' ∧
        Sreg.prefixLen (N + L') (1 - ((d : ℝ) - t1) / 4) N
          ((3 : ℝ) ^ N • z)
          (fun j => ContinuousMap.compRightContinuousMap ℝ
            (⟨fun x : SpatialCoordinates d => (3 : ℝ) ^ (-(N : ℤ)) • x,
              continuous_const.smul continuous_id⟩ :
              C(SpatialCoordinates d, SpatialCoordinates d))
            (om (j - (N : ℤ)))) ≤ Lmac N om) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N, 1 ≤ Lmac N om := by
  filter_upwards [hprefix] with om hom N
  obtain ⟨L', _, hle⟩ := hom N 0
  exact le_trans (Sreg.prefix_pos _ _ _ _ _) hle

/-- **Non-vacuity check for the `hprefix` clause (2/2).**  The zero prefix bound
`Lmac := fun _ _ => 0` does not satisfy the `hprefix` clause. -/
theorem aux_aux_macro_moment_bank_zero_Lmac_fails
    {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M)
    (t1 : ℝ) (z : SpatialCoordinates d) :
    ¬ (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N L0 : ℕ,
      ∃ L' : ℕ, L0 ≤ L' ∧
        Sreg.prefixLen (N + L') (1 - ((d : ℝ) - t1) / 4) N
          ((3 : ℝ) ^ N • z)
          (fun j => ContinuousMap.compRightContinuousMap ℝ
            (⟨fun x : SpatialCoordinates d => (3 : ℝ) ^ (-(N : ℤ)) • x,
              continuous_const.smul continuous_id⟩ :
              C(SpatialCoordinates d, SpatialCoordinates d))
            (om (j - (N : ℤ)))) ≤
          (fun (_ : ℕ) (_ : BilateralField d) => (0 : ℕ)) N om) := by
  intro hprefix
  have hone := aux_aux_macro_moment_bank_one_le_Lmac_of_prefix M Sreg t1 z
    (fun (_ : ℕ) (_ : BilateralField d) => (0 : ℕ)) hprefix
  obtain ⟨om, hom⟩ := hone.exists
  exact absurd (hom 0) (by norm_num)

theorem aux_aux_macro_moment_bank_form_sub_left {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) (x y z : SobolevData Ω) :
    sobolevCoefficientForm a (x - y) z =
      sobolevCoefficientForm a x z - sobolevCoefficientForm a y z := by
  rw [map_sub]
  rfl

/-- Energy splitting of a Dirichlet solution: `E(u,u) = Λ(b) + E(w,w)` with `w = u - h` the
killed part (`h` the canonical harmonic extension of `b`), and `E(w,w) = ∫ F w`. -/
theorem aux_aux_macro_moment_bank_energy_split {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Ω,
      ‖(u : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) u‖)
    (a : PositiveCoefficient Ω) (F : SpatialCoordinates d → ℝ) (b u : weakSobolevGraph Ω)
    (hsol : SolvesDirichlet a F b u) :
    ∃ w : SobolevData Ω, w ∈ killedSobolevGraph Ω ∧
      sobolevCoefficientForm a (u : SobolevData Ω) (u : SobolevData Ω) =
        dirichletResponse (killedResponseSpace hP) a b + sobolevCoefficientForm a w w ∧
      sobolevCoefficientForm a w w =
        ∫ x in (Ω : Set (SpatialCoordinates d)), F x * w.1 x := by
  obtain ⟨h, hhdef⟩ : ∃ h : weakSobolevGraph Ω,
      h = dirichletMinimizer (killedResponseSpace hP) a b := ⟨_, rfl⟩
  have hub : (u : SobolevData Ω) - (b : SobolevData Ω) ∈ killedSobolevGraph Ω := hsol.1
  have hhb : (h : SobolevData Ω) - (b : SobolevData Ω) ∈ killedSobolevGraph Ω := by
    rw [hhdef]
    exact dirichletMinimizer_mem_affine (killedResponseSpace hP) a b
  obtain ⟨U, hU⟩ : ∃ U : SobolevData Ω, U = (u : SobolevData Ω) := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : SobolevData Ω, V = (h : SobolevData Ω) := ⟨_, rfl⟩
  have hw : U - V ∈ killedSobolevGraph Ω := by
    have := Submodule.sub_mem _ hub hhb
    rw [sub_sub_sub_cancel_right] at this
    rw [hU, hV]
    exact this
  have heul : sobolevCoefficientForm a V (U - V) = 0 := by
    have := dirichletMinimizer_euler (killedResponseSpace hP) a b ⟨U - V, hw⟩
    rw [← hhdef] at this
    change sobolevCoefficientForm a (h : SobolevData Ω) (U - V) = 0 at this
    rw [← hV] at this
    exact this
  have hsrc : sobolevCoefficientForm a U (U - V) =
      ∫ x in (Ω : Set (SpatialCoordinates d)), F x * (U - V).1 x := by
    have := hsol.2 ⟨U - V, hw⟩
    change sobolevCoefficientForm a (u : SobolevData Ω) (U - V) =
      ∫ x in (Ω : Set (SpatialCoordinates d)), F x * (U - V).1 x at this
    rw [← hU] at this
    exact this
  have hresp : dirichletResponse (killedResponseSpace hP) a b = sobolevCoefficientForm a V V := by
    rw [hV, hhdef]
    rfl
  have f1 := aux_aux_macro_moment_bank_form_sub_left a U V (U - V)
  have f2 := map_sub (sobolevCoefficientForm a U) U V
  have f3 := map_sub (sobolevCoefficientForm a V) U V
  have f4 := sobolevCoefficientForm_symm a U V
  refine ⟨U - V, hw, ?_, ?_⟩
  · rw [hresp, ← hU, f1, f2, f3]
    rw [f3] at heul
    linarith
  · rw [f1, heul, sub_zero]
    exact hsrc

/-- Cauchy–Schwarz for the bounded source load. -/
theorem aux_aux_macro_moment_bank_source_pairing_le {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hF : AEMeasurable F (volume.restrict (Ω : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂(volume.restrict (Ω : Set (SpatialCoordinates d))), |F x| ≤ Kf)
    (v : DomainL2 Ω) :
    ∫ x in (Ω : Set (SpatialCoordinates d)), F x * v x ≤
      ((measureUnivNNReal (volume.restrict (Ω : Set (SpatialCoordinates d))) : ℝ) ^
        ((2 : ℝ≥0∞).toReal⁻¹) * Kf) * ‖v‖ := by
  have hmem : MemLp F 2 (volume.restrict (Ω : Set (SpatialCoordinates d))) :=
    MemLp.of_bound hF.aestronglyMeasurable Kf (by
      filter_upwards [hFb] with x hx
      simpa [Real.norm_eq_abs] using hx)
  set fL : DomainL2 Ω := hmem.toLp F with hfL
  have hint : ∫ x in (Ω : Set (SpatialCoordinates d)), F x * v x = inner ℝ fL v := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hmem.coeFn_toLp] with x hx
    rw [hfL, hx]
    simp [mul_comm]
  have hnorm : ‖fL‖ ≤
      (measureUnivNNReal (volume.restrict (Ω : Set (SpatialCoordinates d))) : ℝ) ^
        ((2 : ℝ≥0∞).toReal⁻¹) * Kf := by
    refine Lp.norm_le_of_ae_bound hKf ?_
    filter_upwards [hmem.coeFn_toLp, hFb] with x hx hxb
    rw [hfL, hx, Real.norm_eq_abs]
    exact hxb
  rw [hint]
  exact (real_inner_le_norm fL v).trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))

/-- The `L²` part of the coarse coercivity estimate of `lem_coercivity`. -/
theorem aux_aux_macro_moment_bank_l2_le_of_coercive {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr)) (Kc : ℝ)
    (v : SobolevData (centeredCube z r hr))
    (hco : cubeFractionalSqNorm hd z r hr threeQuarterOrder v.1 ≤
      Kc * sobolevCoefficientForm a v v) :
    ‖v.1‖ ^ 2 ≤ volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
      (|Kc| * sobolevCoefficientForm a v v) := by
  have hvol := centeredCube_volume_pos z hr
  have hsemi : 0 ≤ cubeFractionalVecSeminormSq (k := 1) hd z r hr threeQuarterOrder
      (fun _ => v.1) := by
    unfold cubeFractionalVecSeminormSq
    positivity
  have hE := sobolevCoefficientForm_nonneg a v
  have hsq : cubeFractionalSqNorm hd z r hr threeQuarterOrder v.1 =
      cubeFractionalVecSeminormSq (k := 1) hd z r hr threeQuarterOrder (fun _ => v.1) +
        ‖v.1‖ ^ 2 / volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    simp [cubeFractionalSqNorm, cubeFractionalVecSqNorm]
  rw [hsq] at hco
  have h1 : ‖v.1‖ ^ 2 / volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
      |Kc| * sobolevCoefficientForm a v v := by
    have := mul_le_mul_of_nonneg_right (le_abs_self Kc) hE
    linarith
  rw [div_le_iff₀ hvol] at h1
  linarith

/-- The killed part of the energy is controlled by the source alone. -/
theorem aux_aux_macro_moment_bank_killed_energy_le (e n c V : ℝ) (he : 0 ≤ e)
    (hV : 0 ≤ V) (hen : e ≤ c * n) (hnV : n ^ 2 ≤ V * e) : e ≤ c ^ 2 * V := by
  by_cases h0 : e = 0
  · rw [h0]
    positivity
  · have hpos : 0 < e := lt_of_le_of_ne he (Ne.symm h0)
    have h1 : e ^ 2 ≤ (c * n) ^ 2 := pow_le_pow_left₀ he hen 2
    have h2 : e * e ≤ (c ^ 2 * V) * e := by
      calc e * e = e ^ 2 := by ring
        _ ≤ (c * n) ^ 2 := h1
        _ = c ^ 2 * n ^ 2 := by ring
        _ ≤ c ^ 2 * (V * e) := mul_le_mul_of_nonneg_left hnV (by positivity)
        _ = (c ^ 2 * V) * e := by ring
    exact le_of_mul_le_mul_right h2 hpos

/-- A `C²` boundary datum is `β`-Hölder on the frontier of the working cube, with seminorm
at most its `C²` norm times a dimensional factor. -/
theorem aux_aux_macro_moment_bank_boundary_holder {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (hr1 : r ≤ 1) (beta : ℝ) (hb1 : beta < 1)
    (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ 2 phi) (Cphi : ℝ)
    (hC : c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi) :
    0 ≤ Cphi ∧
      ContinuousOn phi (closedCube z r hr : Set (SpatialCoordinates d)) ∧
      IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) phi ∧
      0 ≤ holderSeminorm beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) phi ∧
      holderSeminorm beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) phi ≤
        Cphi * Real.sqrt (d : ℝ) ^ (1 - beta) := by
  set K : Set (SpatialCoordinates d) := (closedCube z r hr : Set (SpatialCoordinates d)) with hK
  have hKeq : K = Metric.closedBall z (r / 2) := rfl
  have hKc : IsCompact K := (closedCube z r hr).isCompact
  have hDcont : Continuous (fun x => ‖fderiv ℝ phi x‖) :=
    (hphi.continuous_fderiv (by norm_num)).norm
  set B : Set ℝ := {v : ℝ | ∃ x ∈ K, v = ‖fderiv ℝ phi x‖} with hB
  have hBbdd : BddAbove B := by
    refine (hKc.bddAbove_image hDcont.continuousOn).mono ?_
    rintro v ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  set Lφ : ℝ := sSup B with hL
  have hLx : ∀ x ∈ K, ‖fderiv ℝ phi x‖ ≤ Lφ := fun x hx => le_csSup hBbdd ⟨x, hx, rfl⟩
  have hL0 : 0 ≤ Lφ := Real.sSup_nonneg (by
    rintro v ⟨x, _, rfl⟩
    exact norm_nonneg (fderiv ℝ phi x))
  have hA0 : 0 ≤ sSup {v : ℝ | ∃ x ∈ K, v = |phi x|} :=
    Real.sSup_nonneg (by rintro v ⟨x, _, rfl⟩; exact abs_nonneg _)
  have hC0 : 0 ≤ sSup {v : ℝ | ∃ x ∈ K, v = ‖fderiv ℝ (fderiv ℝ phi) x‖} :=
    Real.sSup_nonneg (by
      rintro v ⟨x, _, rfl⟩
      exact norm_nonneg (fderiv ℝ (fderiv ℝ phi) x))
  have hLC : Lφ ≤ Cphi := by
    have : c2Norm K phi = sSup {v : ℝ | ∃ x ∈ K, v = |phi x|} + Lφ +
        sSup {v : ℝ | ∃ x ∈ K, v = ‖fderiv ℝ (fderiv ℝ phi) x‖} := rfl
    linarith
  have hmv : ∀ x ∈ K, ∀ y ∈ K, ‖phi y - phi x‖ ≤ Lφ * ‖y - x‖ := by
    intro x hx y hy
    refine Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun w _ => (hphi.differentiable (by norm_num)) w) hLx ?_ hx hy
    rw [hKeq]
    exact convex_closedBall z (r / 2)
  have hfront : frontier (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ K := by
    rw [hKeq]
    exact frontier_subset_closure.trans Metric.closure_ball_subset_closedBall
  set D : ℝ := Real.sqrt (d : ℝ) ^ (1 - beta) with hD
  have hbound : ∀ v ∈ holderRatioSet beta
      (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) phi, v ≤ Lφ * D := by
    rintro v ⟨x, hx, y, hy, hxy, rfl⟩
    have hxK := hfront hx
    have hyK := hfront hy
    set e : ℝ := Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) with he
    have hcoord : ∀ j : Fin d, |x j - y j| ≤ e := by
      intro j
      refine Real.abs_le_sqrt ?_
      exact Finset.single_le_sum (f := fun i => (x i - y i) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    have hepos : 0 < e := by
      obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
        by_contra hcon
        push_neg at hcon
        exact hxy (funext hcon)
      have : 0 < |x j - y j| := abs_pos.2 (sub_ne_zero.2 hj)
      exact this.trans_le (hcoord j)
    have hnorm : ‖x - y‖ ≤ e := by
      refine (pi_norm_le_iff_of_nonneg hepos.le).2 fun j => ?_
      simpa [Real.norm_eq_abs] using hcoord j
    have hed : e ≤ Real.sqrt (d : ℝ) := by
      refine Real.sqrt_le_sqrt ?_
      have hj : ∀ j : Fin d, (x j - y j) ^ 2 ≤ 1 := by
        intro j
        have hx' : dist x z ≤ r / 2 := by rw [hKeq] at hxK; exact hxK
        have hy' : dist y z ≤ r / 2 := by rw [hKeq] at hyK; exact hyK
        have h1 : |x j - z j| ≤ r / 2 := by
          have := norm_le_pi_norm (x - z) j
          rw [dist_eq_norm] at hx'
          simpa [Real.norm_eq_abs] using this.trans hx'
        have h2 : |y j - z j| ≤ r / 2 := by
          have := norm_le_pi_norm (y - z) j
          rw [dist_eq_norm] at hy'
          simpa [Real.norm_eq_abs] using this.trans hy'
        have h3 : |x j - y j| ≤ 1 := by
          have := abs_sub_le (x j) (z j) (y j)
          rw [abs_sub_comm (z j) (y j)] at this
          linarith
        have := sq_abs (x j - y j) ▸ pow_le_pow_left₀ (abs_nonneg _) h3 2
        simpa using this
      calc (∑ j : Fin d, (x j - y j) ^ 2) ≤ ∑ _j : Fin d, (1 : ℝ) :=
            Finset.sum_le_sum fun j _ => hj j
        _ = (d : ℝ) := by simp
    have hphixy : |phi x - phi y| ≤ Lφ * e := by
      have := hmv y hyK x hxK
      rw [Real.norm_eq_abs] at this
      exact this.trans (mul_le_mul_of_nonneg_left hnorm hL0)
    have hpow : e / e ^ beta = e ^ (1 - beta) := by
      rw [Real.rpow_sub hepos, Real.rpow_one]
    calc |phi x - phi y| / e ^ beta ≤ Lφ * e / e ^ beta :=
          div_le_div_of_nonneg_right hphixy (Real.rpow_nonneg hepos.le _)
      _ = Lφ * (e / e ^ beta) := by ring
      _ = Lφ * e ^ (1 - beta) := by rw [hpow]
      _ ≤ Lφ * D := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hepos.le hed (by linarith)) hL0
  have hD0 : 0 ≤ D := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  refine ⟨hL0.trans hLC, hphi.continuous.continuousOn, ⟨Lφ * D, hbound⟩, ?_, ?_⟩
  · refine Real.sSup_nonneg ?_
    rintro v ⟨x, _, y, _, _, rfl⟩
    exact div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  · exact (Real.sSup_le hbound (mul_nonneg hL0 hD0)).trans
      (mul_le_mul_of_nonneg_right hLC hD0)


/-- **Deterministic energy majorant** (the `hKsource` inequality before moments): for a
Dirichlet solution with bounded source and `C²` datum, the boundary-extension bound of
`lem_extension` (`eq:mfd-2`) and the coercivity of `lem_coercivity` (`eq:mfd-1`) give
`E(u,u) ≤ (c₁ Λ + c₂ |K|) (K_f + C_φ)²` with deterministic `c₁, c₂`. -/
theorem aux_aux_macro_moment_bank_energy_le {d : ℕ} (hd : 2 ≤ d) (E : in_J d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (beta Cext : ℝ) (hb1 : beta < 1) (hCext : 0 < Cext)
    (hext : ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
        ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
      (a : PositiveCoefficient (centeredCube z r hr))
      (G : SpatialCoordinates d → ℝ) (b : weakSobolevGraph (centeredCube z r hr)),
      ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)) →
      IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G →
      ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G →
      dirichletResponse (killedResponseSpace hP) a b ≤
        Cext * E.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 * r ^ ((d : ℝ) - 2) *
          (r ^ beta *
            holderSeminorm beta
              (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
        ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (a : PositiveCoefficient (centeredCube z r hr)) (Kc : ℝ)
    (hcoer : ∀ v : killedSobolevGraph (centeredCube z r hr),
      cubeFractionalSqNorm hd z r hr threeQuarterOrder
          (v : SobolevData (centeredCube z r hr)).1 ≤
        Kc * sobolevCoefficientForm a (v : SobolevData (centeredCube z r hr))
          (v : SobolevData (centeredCube z r hr)))
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hF : AEMeasurable F
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂(volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf)
    (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ) (hphi : ContDiff ℝ 2 phi)
    (hC : c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi)
    (b u : weakSobolevGraph (centeredCube z r hr))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi)
    (hsol : SolvesDirichlet a F b u) :
    sobolevCoefficientForm a (u : SobolevData (centeredCube z r hr))
        (u : SobolevData (centeredCube z r hr)) ≤
      (Cext * r ^ ((d : ℝ) - 2) * (r ^ beta * Real.sqrt (d : ℝ) ^ (1 - beta)) ^ 2 *
          E.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 +
        ((measureUnivNNReal (volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))) : ℝ) ^
            ((2 : ℝ≥0∞).toReal⁻¹)) ^ 2 *
          volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) * |Kc|) *
        (Kf + Cphi) ^ 2 := by
  obtain ⟨hCphi, hcont, hhold, hs0, hsle⟩ :=
    aux_aux_macro_moment_bank_boundary_holder z r hr hr1 beta hb1 phi hphi Cphi hC
  obtain ⟨w, hwk, hsplit, hww⟩ := aux_aux_macro_moment_bank_energy_split hP a F b u hsol
  have hm0 : 0 ≤ (measureUnivNNReal (volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))) : ℝ) ^ ((2 : ℝ≥0∞).toReal⁻¹) :=
    Real.rpow_nonneg (NNReal.coe_nonneg _) _
  have hvol0 : 0 ≤ volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube_volume_pos z hr).le
  have hLam0 : 0 ≤ E.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 :=
    (E.Lam_pos _ _ _ _ _ _ _ _).le
  have hD0 : 0 ≤ Real.sqrt (d : ℝ) ^ (1 - beta) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hrd : 0 ≤ r ^ ((d : ℝ) - 2) := Real.rpow_nonneg hr.le _
  have hrb : 0 ≤ r ^ beta := Real.rpow_nonneg hr.le _
  have he0 : 0 ≤ sobolevCoefficientForm a w w := sobolevCoefficientForm_nonneg a w
  have hpair := aux_aux_macro_moment_bank_source_pairing_le F Kf hKf hF hFb w.1
  have hl2 := aux_aux_macro_moment_bank_l2_le_of_coercive hd z r hr a Kc w (hcoer ⟨w, hwk⟩)
  have hresp := hext hP a phi b hcont hhold hb
  generalize (measureUnivNNReal (volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))) : ℝ) ^ ((2 : ℝ≥0∞).toReal⁻¹) = m
    at hm0 hpair ⊢
  generalize volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) = vol
    at hvol0 hl2 ⊢
  generalize Real.sqrt (d : ℝ) ^ (1 - beta) = D at hD0 hsle ⊢
  generalize E.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 = Lam at hLam0 hresp ⊢
  generalize holderSeminorm beta
    (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) phi = hs at hs0 hsle hresp
  generalize dirichletResponse (killedResponseSpace hP) a b = Dr at hresp hsplit
  generalize sobolevCoefficientForm a w w = e at he0 hww hsplit hl2
  rw [← hww] at hpair
  have hn0 : 0 ≤ ‖w.1‖ := norm_nonneg _
  generalize ‖w.1‖ = n at hpair hl2 hn0
  rw [hsplit]
  -- boundary part
  have hbd : Dr ≤ Cext * r ^ ((d : ℝ) - 2) * (r ^ beta * D) ^ 2 * Lam * Cphi ^ 2 := by
    have hsq : (r ^ beta * hs) ^ 2 ≤ (r ^ beta * (Cphi * D)) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hrb hs0) (mul_le_mul_of_nonneg_left hsle hrb) 2
    have := mul_le_mul_of_nonneg_left hsq
      (mul_nonneg (mul_nonneg hCext.le hLam0) hrd)
    nlinarith
  -- killed part
  have hkill : e ≤ (m * Kf) ^ 2 * (vol * |Kc|) :=
    aux_aux_macro_moment_bank_killed_energy_le e n (m * Kf) (vol * |Kc|) he0
      (mul_nonneg hvol0 (abs_nonneg _)) hpair
      (by rw [mul_assoc]; exact hl2)
  -- assemble
  have hKf2 : Kf ^ 2 ≤ (Kf + Cphi) ^ 2 := pow_le_pow_left₀ hKf (by linarith) 2
  have hC2 : Cphi ^ 2 ≤ (Kf + Cphi) ^ 2 := pow_le_pow_left₀ hCphi (by linarith) 2
  have h1 : Cext * r ^ ((d : ℝ) - 2) * (r ^ beta * D) ^ 2 * Lam * Cphi ^ 2 ≤
      Cext * r ^ ((d : ℝ) - 2) * (r ^ beta * D) ^ 2 * Lam * (Kf + Cphi) ^ 2 :=
    mul_le_mul_of_nonneg_left hC2 (by positivity)
  have h2 : (m * Kf) ^ 2 * (vol * |Kc|) ≤ m ^ 2 * vol * |Kc| * (Kf + Cphi) ^ 2 := by
    have : (m * Kf) ^ 2 * (vol * |Kc|) = m ^ 2 * vol * |Kc| * Kf ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hKf2 (by positivity)
  have : (Cext * r ^ ((d : ℝ) - 2) * (r ^ beta * D) ^ 2 * Lam + m ^ 2 * vol * |Kc|) *
      (Kf + Cphi) ^ 2 = Cext * r ^ ((d : ℝ) - 2) * (r ^ beta * D) ^ 2 * Lam * (Kf + Cphi) ^ 2 +
        m ^ 2 * vol * |Kc| * (Kf + Cphi) ^ 2 := by ring
  rw [this]
  linarith

/-- The reference majorant `exp ‖H|_Q̄‖`: measurable, dominating `exp |H(x)|` on the closed
cube, and with every finite moment (`lem_infrared`, through the compact exponential moments
of an infrared characterization). -/
theorem aux_aux_macro_moment_bank_reference {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (K : Compacts (SpatialCoordinates d)) (Q : ℝ) (hQ : 1 ≤ Q) :
    Measurable (fun om => Real.exp ‖(H om).restrict (K : Set (SpatialCoordinates d))‖) ∧
      (∀ om, ∀ x ∈ (K : Set (SpatialCoordinates d)),
        Real.exp (|H om x|) ≤ Real.exp ‖(H om).restrict (K : Set (SpatialCoordinates d))‖) ∧
      MemLp (fun om => Real.exp ‖(H om).restrict (K : Set (SpatialCoordinates d))‖)
        (ENNReal.ofReal Q) (chaosSampleLaw M).toMeasure := by
  have hmeas : Measurable
      (fun om => Real.exp ‖(H om).restrict (K : Set (SpatialCoordinates d))‖) := by
    have hc : Continuous (fun f : C(SpatialCoordinates d, ℝ) =>
        Real.exp ‖f.restrict (K : Set (SpatialCoordinates d))‖) :=
      Real.continuous_exp.comp (continuous_norm.comp
        (ContinuousMap.continuous_restrict (K : Set (SpatialCoordinates d))))
    exact hc.measurable.comp hH.1
  refine ⟨hmeas, ?_, ?_⟩
  · intro om x hx
    refine Real.exp_le_exp.2 ?_
    have h := ContinuousMap.norm_coe_le_norm
      ((H om).restrict (K : Set (SpatialCoordinates d))) ⟨x, hx⟩
    have heq : ‖((H om).restrict (K : Set (SpatialCoordinates d))) ⟨x, hx⟩‖ = |H om x| :=
      Real.norm_eq_abs _
    rw [heq] at h
    exact h
  · obtain ⟨C, _, hexp⟩ := exists_uniform_compactExponentialMoment_of_infraredCharacterization
      (d := d) hd
    have hint := (hexp M H hH K Q (by linarith)).1
    have hQ0 : ENNReal.ofReal Q ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      linarith
    refine (integrable_norm_rpow_iff hmeas.aestronglyMeasurable hQ0
      ENNReal.ofReal_ne_top).1 ?_
    refine hint.congr (Filter.Eventually.of_forall fun om => ?_)
    simp only [ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ Q)]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_mul, mul_comm]

/-- The Hölder triple `(2P, 2P, P)`. -/
theorem aux_aux_macro_moment_bank_holderTriple (P : ℝ) :
    ENNReal.HolderTriple (ENNReal.ofReal (2 * P)) (ENNReal.ofReal (2 * P))
      (ENNReal.ofReal P) := by
  refine ⟨?_⟩
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
    ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), ← add_mul,
    ENNReal.inv_two_add_inv_two, one_mul]

/-- Hölder aggregation of two factors. -/
theorem aux_aux_macro_moment_bank_product_moment {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (P : ℝ) (X Y : α → ℝ)
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) :
    eLpNorm (fun om => X om * Y om) (ENNReal.ofReal P) μ ≤
      eLpNorm X (ENNReal.ofReal (2 * P)) μ * eLpNorm Y (ENNReal.ofReal (2 * P)) μ := by
  haveI := aux_aux_macro_moment_bank_holderTriple P
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm (p := ENNReal.ofReal (2 * P))
    (q := ENNReal.ofReal (2 * P)) (r := ENNReal.ofReal P) hX hY (fun x y : ℝ => x * y) 1
    (Filter.Eventually.of_forall fun om => by simp [norm_mul])
  simpa using h

/-- The killed Poincaré inequality on a centred cube. -/
theorem aux_aux_macro_moment_bank_killed_poincare {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖ := by
  haveI : NeZero d := ⟨by omega⟩
  have hdom : Homogenization.IsOpenBoundedConvexDomain
      (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    refine ⟨(centeredCube z r hr).isOpen, ?_, ?_⟩
    · refine Homogenization.Bornology.IsBounded.isBoundedDomain ?_
      show Bornology.IsBounded (Metric.ball z (r / 2))
      exact Metric.isBounded_ball
    · show Convex ℝ (Metric.ball z (r / 2))
      exact convex_ball z (r / 2)
  exact (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain _ hdom).1

/-- The disorder threshold: below it the Hölder exponent lies in the admissible range and the
prefix tail rate beats the required exponential moment. -/
theorem aux_aux_macro_moment_bank_delta_facts (Cd a lam δ : ℝ) (hCd : 1 ≤ Cd) (ha0 : 0 < a)
    (ha1 : a < 1 / 4) (hlam : 0 ≤ lam) (hδ0 : 0 < δ)
    (hδ : δ ≤ min (min (1 / 2) Cd⁻¹) (min ((a / Cd) ^ 2) (a ^ 2 / (2 * Cd * (lam + 1))))) :
    δ ≤ Cd⁻¹ ∧ 1 - a ∈ Set.Icc (1 / 2 : ℝ) (1 - Cd * δ * Real.sqrt |Real.log δ|) ∧
      lam < (1 - (1 - a)) ^ 2 / (Cd * δ ^ 2 * |Real.log δ|) := by
  have hδ12 : δ ≤ 1 / 2 := hδ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδC : δ ≤ Cd⁻¹ := hδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδa : δ ≤ (a / Cd) ^ 2 := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδl : δ ≤ a ^ 2 / (2 * Cd * (lam + 1)) :=
    hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hCd0 : 0 < Cd := by linarith
  have hlog : Real.log δ < 0 := Real.log_neg hδ0 (by linarith)
  set Lg : ℝ := |Real.log δ| with hLg
  have hLg0 : 0 < Lg := by rw [hLg]; exact abs_pos.2 hlog.ne
  have hLgδ : δ * Lg ≤ 1 := by
    have h1 : Real.log δ⁻¹ ≤ δ⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.2 hδ0)
    rw [Real.log_inv] at h1
    have h2 : Lg = -Real.log δ := by rw [hLg, abs_of_neg hlog]
    rw [h2]
    have h3 : δ * (-Real.log δ) ≤ δ * (δ⁻¹ - 1) := mul_le_mul_of_nonneg_left h1 hδ0.le
    rw [mul_sub, mul_inv_cancel₀ hδ0.ne', mul_one] at h3
    linarith
  have hsq : δ ^ 2 * Lg ≤ δ := by nlinarith
  refine ⟨hδC, ⟨by linarith, ?_⟩, ?_⟩
  · -- `Cd δ √Lg ≤ a`
    have h1 : (δ * Real.sqrt Lg) ^ 2 ≤ (a / Cd) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hLg0.le]
      linarith
    have h2 : δ * Real.sqrt Lg ≤ a / Cd :=
      (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h1
    have h3 : Cd * (δ * Real.sqrt Lg) ≤ a := by
      rw [le_div_iff₀ hCd0] at h2
      linarith
    nlinarith
  · have hden : 0 < Cd * δ ^ 2 * Lg := by positivity
    have hsimp : (1 - (1 - a)) ^ 2 = a ^ 2 := by ring
    rw [hsimp, lt_div_iff₀ hden]
    have h1 : 2 * Cd * (lam + 1) * δ ≤ a ^ 2 := by
      rw [le_div_iff₀ (by positivity)] at hδl
      linarith
    have h2 : Cd * δ ^ 2 * Lg ≤ Cd * δ := by
      have := mul_le_mul_of_nonneg_left hsq hCd0.le
      linarith
    nlinarith


/-- `L^Q` bound on the bracket `exp‖H‖ + c₁ Λ + c₂ |K|`. -/
theorem aux_aux_macro_moment_bank_bracket_moment {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (Q : ℝ) (hQ : 1 ≤ Q) (R Lam K : α → ℝ) (c1 c2 CL CK : ℝ)
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hR : AEStronglyMeasurable R μ) (hLam : AEStronglyMeasurable Lam μ)
    (hK : AEStronglyMeasurable K μ)
    (hLamb : eLpNorm Lam (ENNReal.ofReal Q) μ ≤ ENNReal.ofReal CL)
    (hKb : eLpNorm K (ENNReal.ofReal Q) μ ≤ ENNReal.ofReal CK) :
    eLpNorm (fun om => R om + (c1 * |Lam om| + c2 * |K om|)) (ENNReal.ofReal Q) μ ≤
      eLpNorm R (ENNReal.ofReal Q) μ +
        (ENNReal.ofReal c1 * ENNReal.ofReal CL + ENNReal.ofReal c2 * ENNReal.ofReal CK) := by
  have hQ' : 1 ≤ ENNReal.ofReal Q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hQ
  have hL' : AEStronglyMeasurable (fun om => c1 * |Lam om|) μ := hLam.norm.const_mul c1
  have hK' : AEStronglyMeasurable (fun om => c2 * |K om|) μ := hK.norm.const_mul c2
  refine (eLpNorm_add_le hR (hL'.add hK') hQ').trans (add_le_add le_rfl ?_)
  refine (eLpNorm_add_le hL' hK' hQ').trans (add_le_add ?_ ?_)
  · have h := eLpNorm_const_smul_le (c := c1) (f := fun om => ‖Lam om‖) (p := ENNReal.ofReal Q)
      (μ := μ)
    have he : ‖c1‖ₑ = ENNReal.ofReal c1 := Real.enorm_of_nonneg hc1
    rw [he, eLpNorm_norm] at h
    have hfun : (c1 • fun om => ‖Lam om‖) = fun om => c1 * |Lam om| := by
      funext om
      simp [Real.norm_eq_abs]
    rw [hfun] at h
    exact h.trans (mul_le_mul_right hLamb _)
  · have h := eLpNorm_const_smul_le (c := c2) (f := fun om => ‖K om‖) (p := ENNReal.ofReal Q)
      (μ := μ)
    have he : ‖c2‖ₑ = ENNReal.ofReal c2 := Real.enorm_of_nonneg hc2
    rw [he, eLpNorm_norm] at h
    have hfun : (c2 • fun om => ‖K om‖) = fun om => c2 * |K om| := by
      funext om
      simp [Real.norm_eq_abs]
    rw [hfun] at h
    exact h.trans (mul_le_mul_right hKb _)

/-- **Fixed-model assembly.**  Given the prefix bound with its moments, the reference
majorant, the coercivity factor and the boundary-extension factor with their moments at the
doubled exponent `2P`, the common prefactor
`Kmac = 3^{t₁ Lmac} (exp ‖H|_Q̄‖ + c₁ Λ + c₂ |K|)` satisfies every clause of the bank. -/
theorem aux_aux_macro_moment_bank_assemble {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (t1 : ℝ) (k : ℕ) (ps : Fin k → ℝ) (Pexp : ℝ)
    (hP1 : 1 ≤ Pexp) (hpsP : ∀ i, ps i ≤ Pexp)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (beta Cext : ℝ) (hb1 : beta < 1) (hCext : 0 < Cext)
    (hext : ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
        ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
      (a : PositiveCoefficient (centeredCube z r hr))
      (G : SpatialCoordinates d → ℝ) (b : weakSobolevGraph (centeredCube z r hr)),
      ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)) →
      IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G →
      ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G →
      dirichletResponse (killedResponseSpace hP) a b ≤
        Cext * E.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 * r ^ ((d : ℝ) - 2) *
          (r ^ beta *
            holderSeminorm beta
              (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2)
    (Lmac : ℕ → BilateralField d → ℕ) (hLmeas : ∀ N, Measurable (Lmac N))
    (BX : ℝ≥0∞) (hBX : BX ≠ ⊤)
    (hX : ∀ N, eLpNorm (fun om => (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)))
      (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure ≤ BX)
    (hprefix : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N L0 : ℕ,
      ∃ L' : ℕ, L0 ≤ L' ∧
        Sreg.prefixLen (N + L') (1 - ((d : ℝ) - t1) / 4) N ((3 : ℝ) ^ N • z)
          (fun j => ContinuousMap.compRightContinuousMap ℝ
            (⟨fun x : SpatialCoordinates d => (3 : ℝ) ^ (-(N : ℤ)) • x,
              continuous_const.smul continuous_id⟩ :
              C(SpatialCoordinates d, SpatialCoordinates d))
            (om (j - (N : ℤ)))) ≤ Lmac N om)
    (hRmeas : Measurable
      (fun om => Real.exp ‖(H om).restrict (closedCube z r hr : Set (SpatialCoordinates d))‖))
    (hRdom : ∀ om, ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      Real.exp (|H om x|) ≤
        Real.exp ‖(H om).restrict (closedCube z r hr : Set (SpatialCoordinates d))‖)
    (hRmem : MemLp
      (fun om => Real.exp ‖(H om).restrict (closedCube z r hr : Set (SpatialCoordinates d))‖)
      (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure)
    (Kco : ℕ → BilateralField d → ℝ)
    (hKco : ∀ N om, ∀ v : killedSobolevGraph (centeredCube z r hr),
      cubeFractionalSqNorm hd z r hr threeQuarterOrder
          (v : SobolevData (centeredCube z r hr)).1 ≤
        Kco N om * sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr)
          (v : SobolevData (centeredCube z r hr)) (v : SobolevData (centeredCube z r hr)))
    (CK : ℝ)
    (hKmem : ∀ N, MemLp (Kco N) (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure)
    (hKbd : ∀ N, eLpNorm (Kco N) (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal CK)
    (Kext : ℕ → BilateralField d → ℝ) (CL : ℝ)
    (hKextmem : ∀ N, MemLp (Kext N) (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure)
    (hKextbd : ∀ N, eLpNorm (Kext N) (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal CL)
    (hdom : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N,
      E.Lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r ((beta - 1 / 2) / 4) 2 ≤
        Kext N om) :
    ∃ (Lmac : ℕ → BilateralField d → ℕ) (Kmac : ℕ → BilateralField d → ℝ)
      (Cbound : Fin k → ℝ),
      (∀ N om, 0 ≤ Kmac N om) ∧
      (∀ i N, MemLp (Kmac N) (ENNReal.ofReal (ps i))
        (chaosSampleLaw M).toMeasure) ∧
      (∀ i N, eLpNorm (Kmac N) (ENNReal.ofReal (ps i))
          (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cbound i)) ∧
      (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N L0 : ℕ,
        ∃ L' : ℕ, L0 ≤ L' ∧
          Sreg.prefixLen (N + L') (1 - ((d : ℝ) - t1) / 4) N
            ((3 : ℝ) ^ N • z)
            (fun j => ContinuousMap.compRightContinuousMap ℝ
              (⟨fun x : SpatialCoordinates d => (3 : ℝ) ^ (-(N : ℤ)) • x,
                continuous_const.smul continuous_id⟩ :
                C(SpatialCoordinates d, SpatialCoordinates d))
              (om (j - (N : ℤ)))) ≤ Lmac N om) ∧
      (∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
          ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
            ContDiff ℝ 2 phi →
            c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
          ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
            ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
            SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
            (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)) *
              sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr)
                (u : SobolevData (centeredCube z r hr))
                (u : SobolevData (centeredCube z r hr)) ≤
                Kmac N om * (Kf + Cphi) ^ 2) ∧
      (∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ N x, x ∈ closedCube z r hr →
          (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)) * Real.exp (|H om x|) ≤ Kmac N om) := by
  have hPc := aux_aux_macro_moment_bank_killed_poincare hd z r hr
  -- the deterministic constants of the energy majorant
  obtain ⟨c1, hc1⟩ : ∃ c1 : ℝ,
      c1 = Cext * r ^ ((d : ℝ) - 2) * (r ^ beta * Real.sqrt (d : ℝ) ^ (1 - beta)) ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c2 : ℝ,
      c2 = ((measureUnivNNReal (volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))) : ℝ) ^
            ((2 : ℝ≥0∞).toReal⁻¹)) ^ 2 *
          volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) := ⟨_, rfl⟩
  have hc10 : 0 ≤ c1 := by
    rw [hc1]
    have := Real.rpow_nonneg hr.le ((d : ℝ) - 2)
    positivity
  have hc20 : 0 ≤ c2 := by
    rw [hc2]
    have := (centeredCube_volume_pos z hr).le
    positivity
  -- the bracket and the prefactor
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℕ → BilateralField d → ℝ, Y = fun N om =>
      Real.exp ‖(H om).restrict (closedCube z r hr : Set (SpatialCoordinates d))‖ +
        (c1 * |Kext N om| + c2 * |Kco N om|) := ⟨_, rfl⟩
  obtain ⟨Kmac, hKmac⟩ : ∃ Kmac : ℕ → BilateralField d → ℝ,
      Kmac = fun N om => (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)) * Y N om := ⟨_, rfl⟩
  have hbr0 : ∀ N om, 0 ≤ c1 * |Kext N om| + c2 * |Kco N om| := by
    intro N om
    positivity
  have hY0 : ∀ N om, Real.exp ‖(H om).restrict (closedCube z r hr : Set (SpatialCoordinates d))‖ +
      (c1 * |Kext N om| + c2 * |Kco N om|) ≤ Y N om := by
    intro N om
    rw [hYdef]
  have hYnn : ∀ N om, 0 ≤ Y N om := by
    intro N om
    refine le_trans ?_ (hY0 N om)
    have := hbr0 N om
    have := Real.exp_pos ‖(H om).restrict (closedCube z r hr : Set (SpatialCoordinates d))‖
    linarith
  have hK0 : ∀ N om, 0 ≤ Kmac N om := by
    intro N om
    rw [hKmac]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hYnn N om)
  -- moments
  have hXmeas : ∀ N, AEStronglyMeasurable (fun om => (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)))
      (chaosSampleLaw M).toMeasure := fun N =>
    ((measurable_from_nat (f := fun n : ℕ => (3 : ℝ) ^ (t1 * (n : ℝ)))).comp
      (hLmeas N)).aestronglyMeasurable
  have hYmeas : ∀ N, AEStronglyMeasurable (Y N) (chaosSampleLaw M).toMeasure := by
    intro N
    rw [hYdef]
    exact hRmeas.aestronglyMeasurable.add
      (((hKextmem N).1.norm.const_mul c1).add ((hKmem N).1.norm.const_mul c2))
  have hYbd : ∀ N, eLpNorm (Y N) (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure ≤
      eLpNorm (fun om => Real.exp ‖(H om).restrict
          (closedCube z r hr : Set (SpatialCoordinates d))‖)
        (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure +
      (ENNReal.ofReal c1 * ENNReal.ofReal CL + ENNReal.ofReal c2 * ENNReal.ofReal CK) := by
    intro N
    rw [hYdef]
    exact aux_aux_macro_moment_bank_bracket_moment (chaosSampleLaw M).toMeasure (2 * Pexp)
      (by linarith) _ _ (Kco N) c1 c2 CL CK hc10 hc20 hRmeas.aestronglyMeasurable
      (hKextmem N).1 (hKmem N).1 (hKextbd N) (hKbd N)
  obtain ⟨BY, hBYdef⟩ : ∃ BY : ℝ≥0∞, BY =
      eLpNorm (fun om => Real.exp ‖(H om).restrict
          (closedCube z r hr : Set (SpatialCoordinates d))‖)
        (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure +
      (ENNReal.ofReal c1 * ENNReal.ofReal CL + ENNReal.ofReal c2 * ENNReal.ofReal CK) :=
    ⟨_, rfl⟩
  rw [← hBYdef] at hYbd
  have hBYtop : BY ≠ ⊤ := by
    rw [hBYdef]
    exact ENNReal.add_ne_top.2 ⟨hRmem.2.ne, ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩⟩
  have hKmeas : ∀ N, AEStronglyMeasurable (Kmac N) (chaosSampleLaw M).toMeasure := by
    intro N
    rw [hKmac]
    exact (hXmeas N).mul (hYmeas N)
  have hKP : ∀ N, eLpNorm (Kmac N) (ENNReal.ofReal Pexp) (chaosSampleLaw M).toMeasure ≤
      BX * BY := by
    intro N
    rw [hKmac]
    exact (aux_aux_macro_moment_bank_product_moment (chaosSampleLaw M).toMeasure Pexp
      _ _ (hXmeas N) (hYmeas N)).trans (mul_le_mul' (hX N) (hYbd N))
  have hBtop : BX * BY ≠ ⊤ := ENNReal.mul_ne_top hBX hBYtop
  have hKi : ∀ i N, eLpNorm (Kmac N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (BX * BY).toReal := by
    intro i N
    rw [ENNReal.ofReal_toReal hBtop]
    exact (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (hpsP i))
      (hKmeas N)).trans (hKP N)
  refine ⟨Lmac, Kmac, fun _ => (BX * BY).toReal, hK0, ?_, hKi, hprefix, ?_, ?_⟩
  · intro i N
    exact ⟨hKmeas N, (hKi i N).trans_lt ENNReal.ofReal_lt_top⟩
  · filter_upwards [hdom] with om hdom
    intro N F Kf hKf hF hFb phi Cphi hphi hC b u hb hsol
    have hen := aux_aux_macro_moment_bank_energy_le hd E z r hr hr1 beta Cext hb1 hCext hext
      hPc (cutoffPositiveCoefficient M H om N z hr) (Kco N om) (hKco N om) F Kf hKf hF hFb
      phi Cphi hphi hC b u hb hsol
    rw [← hc1, ← hc2] at hen
    have h3 : 0 ≤ (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)) := Real.rpow_nonneg (by norm_num) _
    have hsq : 0 ≤ (Kf + Cphi) ^ 2 := sq_nonneg _
    have hYge := hY0 N om
    have hexp0 := Real.exp_pos ‖(H om).restrict (closedCube z r hr : Set (SpatialCoordinates d))‖
    have hKe : Kmac N om = (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)) * Y N om := by rw [hKmac]
    have hLK : c1 * E.Lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r
        ((beta - 1 / 2) / 4) 2 ≤ c1 * |Kext N om| :=
      mul_le_mul_of_nonneg_left ((hdom N).trans (le_abs_self _)) hc10
    rw [hKe, mul_assoc]
    refine mul_le_mul_of_nonneg_left (hen.trans ?_) h3
    exact mul_le_mul_of_nonneg_right (by linarith) hsq
  · refine Filter.Eventually.of_forall fun om => ?_
    intro N x hx
    have h3 : 0 ≤ (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)) := Real.rpow_nonneg (by norm_num) _
    have hKe : Kmac N om = (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)) * Y N om := by rw [hKmac]
    rw [hKe]
    refine mul_le_mul_of_nonneg_left ?_ h3
    have := hRdom om x hx
    have := hbr0 N om
    have := hY0 N om
    linarith

/-- The rescale-and-shift relabelling of the bilateral field at cutoff index `N`. -/
def aux_aux_macro_moment_bank_relabel {d : ℕ} (N : ℕ) (om : BilateralField d) :
    BilateralField d :=
  fun j => ContinuousMap.compRightContinuousMap ℝ
    (⟨fun x : SpatialCoordinates d => (3 : ℝ) ^ (-(N : ℤ)) • x,
      continuous_const.smul continuous_id⟩ :
      C(SpatialCoordinates d, SpatialCoordinates d))
    (om (j - (N : ℤ)))

theorem aux_aux_macro_moment_bank_relabel_measurePreserving {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) :
    MeasurePreserving (aux_aux_macro_moment_bank_relabel (d := d) N)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure := by
  set ν := chaosRootFieldLaw M with hν
  set S : C(C(SpatialCoordinates d, ℝ), C(SpatialCoordinates d, ℝ)) :=
    ContinuousMap.compRightContinuousMap ℝ
      (⟨fun x : SpatialCoordinates d => (3 : ℝ) ^ (-(N : ℤ)) • x,
        continuous_const.smul continuous_id⟩ :
        C(SpatialCoordinates d, SpatialCoordinates d)) with hS
  set law : ℤ → Measure C(SpatialCoordinates d, ℝ) :=
    fun j => (scaledLayerLaw d ν j : Measure C(SpatialCoordinates d, ℝ)) with hlaw
  have hsample : (chaosSampleLaw M).toMeasure = Measure.infinitePi law := rfl
  have hshift_meas : Measurable (fun w : BilateralField d => fun j : ℤ => w (j - (N : ℤ))) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply (j - (N : ℤ)))
  have hS_meas : Measurable (fun w : BilateralField d => fun j : ℤ => S (w j)) :=
    measurable_pi_lambda _ (fun j => S.continuous.measurable.comp (measurable_pi_apply j))
  have hcomp : aux_aux_macro_moment_bank_relabel (d := d) N =
      (fun w : BilateralField d => fun j : ℤ => S (w j)) ∘
        (fun w : BilateralField d => fun j : ℤ => w (j - (N : ℤ))) := rfl
  refine ⟨hcomp ▸ hS_meas.comp hshift_meas, ?_⟩
  -- step 1: the shift
  have h1 : Measure.map (fun w : BilateralField d => fun j : ℤ => w (j - (N : ℤ)))
      (Measure.infinitePi law) = Measure.infinitePi (fun j => law (j - (N : ℤ))) := by
    have h := Measure.infinitePi_map_piCongrLeft (fun j => law (j - (N : ℤ)))
      (Equiv.addRight (N : ℤ))
    have he : (MeasurableEquiv.piCongrLeft
        (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) (Equiv.addRight (N : ℤ)) :
          (ℤ → C(SpatialCoordinates d, ℝ)) → (ℤ → C(SpatialCoordinates d, ℝ))) =
        (fun w j => w (j - (N : ℤ))) := by
      funext w j
      simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply, sub_eq_add_neg]
    have hl : (fun a : ℤ => law (Equiv.addRight (N : ℤ) a - (N : ℤ))) = law := by
      funext a
      simp
    rw [he, hl] at h
    exact h
  -- step 2: the coordinatewise rescaling
  have h2 : Measure.map (fun w : BilateralField d => fun j : ℤ => S (w j))
      (Measure.infinitePi (fun j => law (j - (N : ℤ)))) =
      Measure.infinitePi (fun j => Measure.map S (law (j - (N : ℤ)))) :=
    Measure.infinitePi_map_pi (fun j => law (j - (N : ℤ)))
      (fun _ => S.continuous.measurable)
  -- step 3: each layer law is carried to the next
  have h3 : ∀ j : ℤ, Measure.map S (law (j - (N : ℤ))) = law j := by
    intro j
    simp only [hlaw, scaledLayerLaw, ProbabilityMeasure.toMeasure_map]
    rw [Measure.map_map S.continuous.measurable
      (layerScaling d (j - (N : ℤ))).continuous.measurable]
    congr 1
    funext g
    ext x
    simp only [Function.comp_apply, layerScaling, hS,
      ContinuousMap.compRightContinuousMap_apply, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk]
    congr 1
    rw [smul_smul, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 2
    ring
  rw [hsample, hcomp, ← Measure.map_map hS_meas hshift_meas, h1, h2]
  congr 1
  funext j
  exact h3 j

/-- The smallest level visited infinitely often by a sequence of natural numbers (zero when
there is none): the random prefix bound `Lmac` is this bound for the prefix lengths along the
infrared cutoffs. -/
def aux_aux_macro_moment_bank_ioBound {α : Type*} (f : ℕ → α → ℕ) (om : α) : ℕ :=
  sInf {k : ℕ | ∀ L0 : ℕ, ∃ L' : ℕ, L0 ≤ L' ∧ f L' om ≤ k}

theorem aux_aux_macro_moment_bank_ioBound_upward {α : Type*} (f : ℕ → α → ℕ) (om : α)
    {j k : ℕ} (hjk : j ≤ k)
    (hj : ∀ L0 : ℕ, ∃ L' : ℕ, L0 ≤ L' ∧ f L' om ≤ j) :
    ∀ L0 : ℕ, ∃ L' : ℕ, L0 ≤ L' ∧ f L' om ≤ k := by
  intro L0
  obtain ⟨L', hL', hf⟩ := hj L0
  exact ⟨L', hL', hf.trans hjk⟩

theorem aux_aux_macro_moment_bank_measurableSet_good {α : Type*} [MeasurableSpace α]
    (f : ℕ → α → ℕ) (hf : ∀ L, Measurable (f L)) (k : ℕ) :
    MeasurableSet {om : α | ∀ L0 : ℕ, ∃ L' : ℕ, L0 ≤ L' ∧ f L' om ≤ k} := by
  have hset : {om : α | ∀ L0 : ℕ, ∃ L' : ℕ, L0 ≤ L' ∧ f L' om ≤ k} =
      ⋂ L0 : ℕ, ⋃ L' : ℕ, {om : α | L0 ≤ L' ∧ f L' om ≤ k} := by
    ext om
    simp
  rw [hset]
  refine MeasurableSet.iInter fun L0 => MeasurableSet.iUnion fun L' => ?_
  by_cases h : L0 ≤ L'
  · simp only [h, true_and]
    exact measurableSet_le (hf L') measurable_const
  · simp [h]

theorem aux_aux_macro_moment_bank_ioBound_le_iff {α : Type*} (f : ℕ → α → ℕ) (om : α)
    (k : ℕ) :
    aux_aux_macro_moment_bank_ioBound f om ≤ k ↔
      (∀ L0 : ℕ, ∃ L' : ℕ, L0 ≤ L' ∧ f L' om ≤ k) ∨
        ∀ j : ℕ, ¬ ∀ L0 : ℕ, ∃ L' : ℕ, L0 ≤ L' ∧ f L' om ≤ j := by
  unfold aux_aux_macro_moment_bank_ioBound
  constructor
  · intro h
    by_cases hne : ∃ j : ℕ, ∀ L0 : ℕ, ∃ L' : ℕ, L0 ≤ L' ∧ f L' om ≤ j
    · left
      have hmem := Nat.sInf_mem hne
      exact aux_aux_macro_moment_bank_ioBound_upward f om h hmem
    · right
      push_neg at hne ⊢
      exact hne
  · rintro (h | h)
    · exact Nat.sInf_le h
    · have hempty : {k : ℕ | ∀ L0 : ℕ, ∃ L' : ℕ, L0 ≤ L' ∧ f L' om ≤ k} = ∅ := by
        ext j
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact h j
      rw [hempty, Nat.sInf_empty]
      exact Nat.zero_le _

theorem aux_aux_macro_moment_bank_ioBound_measurable {α : Type*} [MeasurableSpace α]
    (f : ℕ → α → ℕ) (hf : ∀ L, Measurable (f L)) :
    Measurable (aux_aux_macro_moment_bank_ioBound f) := by
  have hle : ∀ k : ℕ, MeasurableSet {om : α | aux_aux_macro_moment_bank_ioBound f om ≤ k} := by
    intro k
    have hset : {om : α | aux_aux_macro_moment_bank_ioBound f om ≤ k} =
        {om : α | ∀ L0 : ℕ, ∃ L' : ℕ, L0 ≤ L' ∧ f L' om ≤ k} ∪
          ⋂ j : ℕ, {om : α | ∀ L0 : ℕ, ∃ L' : ℕ, L0 ≤ L' ∧ f L' om ≤ j}ᶜ := by
      ext om
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_iInter, Set.mem_compl_iff]
      exact aux_aux_macro_moment_bank_ioBound_le_iff f om k
    rw [hset]
    exact (aux_aux_macro_moment_bank_measurableSet_good f hf k).union
      (MeasurableSet.iInter fun j => (aux_aux_macro_moment_bank_measurableSet_good f hf j).compl)
  refine measurable_to_countable' fun k => ?_
  cases k with
  | zero =>
    have : aux_aux_macro_moment_bank_ioBound f ⁻¹' {0} =
        {om : α | aux_aux_macro_moment_bank_ioBound f om ≤ 0} := by
      ext om
      simp
    rw [this]
    exact hle 0
  | succ k =>
    have : aux_aux_macro_moment_bank_ioBound f ⁻¹' {k + 1} =
        {om : α | aux_aux_macro_moment_bank_ioBound f om ≤ k + 1} \
          {om : α | aux_aux_macro_moment_bank_ioBound f om ≤ k} := by
      ext om
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_diff, Set.mem_setOf_eq]
      omega
    rw [this]
    exact (hle (k + 1)).diff (hle k)

/-- The event that level `k` is not visited infinitely often has measure at most the uniform
tail of the sequence at `k`. -/
theorem aux_aux_macro_moment_bank_measure_not_good_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : ℕ → α → ℕ) (k : ℕ) (T : ℝ≥0∞)
    (hT : ∀ L : ℕ, μ {om : α | k < f L om} ≤ T) :
    μ {om : α | ¬ ∀ L0 : ℕ, ∃ L' : ℕ, L0 ≤ L' ∧ f L' om ≤ k} ≤ T := by
  set A : ℕ → Set α := fun L0 => {om : α | ∀ L' : ℕ, L0 ≤ L' → k < f L' om} with hA
  have hmono : Monotone A := by
    intro a b hab om hom L' hL'
    exact hom L' (hab.trans hL')
  have hset : {om : α | ¬ ∀ L0 : ℕ, ∃ L' : ℕ, L0 ≤ L' ∧ f L' om ≤ k} = ⋃ L0, A L0 := by
    ext om
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, hA]
    push_neg
    rfl
  rw [hset, hmono.measure_iUnion]
  refine iSup_le fun L0 => ?_
  refine (measure_mono ?_).trans (hT L0)
  intro om hom
  exact hom L0 le_rfl

theorem aux_aux_macro_moment_bank_measure_lt_ioBound_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : ℕ → α → ℕ) (k : ℕ) (T : ℝ≥0∞)
    (hT : ∀ L : ℕ, μ {om : α | k < f L om} ≤ T) :
    μ {om : α | k < aux_aux_macro_moment_bank_ioBound f om} ≤ T := by
  refine (measure_mono ?_).trans (aux_aux_macro_moment_bank_measure_not_good_le μ f k T hT)
  intro om hom hgood
  have := (aux_aux_macro_moment_bank_ioBound_le_iff f om k).2 (Or.inl hgood)
  exact absurd hom (not_lt.2 this)

/-- Almost surely the bound is attained infinitely often, once the uniform tails vanish. -/
theorem aux_aux_macro_moment_bank_ae_ioBound_attained {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : ℕ → α → ℕ) (T : ℕ → ℝ≥0∞)
    (hT : ∀ k L : ℕ, μ {om : α | k < f L om} ≤ T k)
    (hT0 : Filter.Tendsto T Filter.atTop (nhds 0)) :
    ∀ᵐ om ∂μ, ∀ L0 : ℕ, ∃ L' : ℕ, L0 ≤ L' ∧
      f L' om ≤ aux_aux_macro_moment_bank_ioBound f om := by
  have hnull : μ {om : α | ∀ j : ℕ, ¬ ∀ L0 : ℕ, ∃ L' : ℕ, L0 ≤ L' ∧ f L' om ≤ j} = 0 := by
    apply le_antisymm _ (zero_le _)
    refine ge_of_tendsto' hT0 fun k => ?_
    refine (measure_mono ?_).trans (aux_aux_macro_moment_bank_measure_not_good_le μ f k (T k)
      (hT k))
    intro om hom
    exact hom k
  rw [ae_iff]
  refine measure_mono_null ?_ hnull
  intro om hom
  simp only [Set.mem_setOf_eq] at hom ⊢
  intro j hj
  apply hom
  have hne : ∃ j : ℕ, ∀ L0 : ℕ, ∃ L' : ℕ, L0 ≤ L' ∧ f L' om ≤ j := ⟨j, hj⟩
  exact Nat.sInf_mem hne

/-- Exponential moments of an `ℕ`-valued variable with a geometric tail. -/
theorem aux_aux_macro_moment_bank_lintegral_exp_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (L : α → ℕ) (hL : Measurable L)
    (A κ lam : ℝ) (hA : 1 ≤ A) (hlam : 0 ≤ lam) (hκ : lam < κ)
    (htail : ∀ k : ℕ, μ {om : α | k < L om} ≤ ENNReal.ofReal (A * Real.exp (-κ * k))) :
    ∫⁻ om, ENNReal.ofReal (Real.exp (lam * (L om : ℝ))) ∂μ ≤
      ENNReal.ofReal (A * Real.exp κ * (1 - Real.exp (-(κ - lam)))⁻¹) := by
  have hκ0 : 0 ≤ κ := hlam.trans hκ.le
  set ρ : ℝ := Real.exp (-(κ - lam)) with hρ
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hρ1 : ρ < 1 := by
    rw [hρ, Real.exp_lt_one_iff]
    linarith
  -- pointwise mass bound
  have hmass : ∀ n : ℕ, μ (L ⁻¹' {n}) ≤
      ENNReal.ofReal (A * Real.exp κ * Real.exp (-κ * n)) := by
    intro n
    cases n with
    | zero =>
      refine prob_le_one.trans ?_
      rw [ENNReal.one_le_ofReal]
      have h1 : (1 : ℝ) ≤ Real.exp κ := Real.one_le_exp hκ0
      simp only [Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
      nlinarith
    | succ n =>
      refine (measure_mono (s := L ⁻¹' {n + 1}) (t := {om : α | n < L om}) ?_).trans
        ((htail n).trans (ENNReal.ofReal_le_ofReal ?_))
      · intro om hom
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hom
        simp only [Set.mem_setOf_eq, hom]
        omega
      · have : Real.exp (-κ * n) = Real.exp κ * Real.exp (-κ * ((n + 1 : ℕ) : ℝ)) := by
          rw [← Real.exp_add]
          congr 1
          push_cast
          ring
        rw [this, mul_assoc]
  have hlint : ∫⁻ om, ENNReal.ofReal (Real.exp (lam * (L om : ℝ))) ∂μ =
      ∑' n : ℕ, ENNReal.ofReal (Real.exp (lam * n)) * μ (L ⁻¹' {n}) := by
    have hg : Measurable (fun n : ℕ => ENNReal.ofReal (Real.exp (lam * n))) :=
      measurable_from_nat
    rw [← lintegral_map hg hL, lintegral_countable']
    congr 1
    funext n
    rw [Measure.map_apply hL (measurableSet_singleton n)]
  rw [hlint]
  have hterm : ∀ n : ℕ, ENNReal.ofReal (Real.exp (lam * n)) * μ (L ⁻¹' {n}) ≤
      ENNReal.ofReal (A * Real.exp κ * ρ ^ n) := by
    intro n
    refine (mul_le_mul_right (hmass n) _).trans ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [hρ, ← Real.exp_nat_mul]
    have : Real.exp (lam * n) * (A * Real.exp κ * Real.exp (-κ * n)) =
        A * Real.exp κ * (Real.exp (lam * n) * Real.exp (-κ * n)) := by ring
    rw [this, ← Real.exp_add]
    congr 2
    ring
  refine (ENNReal.tsum_le_tsum hterm).trans (le_of_eq ?_)
  have hsum : Summable (fun n : ℕ => A * Real.exp κ * ρ ^ n) :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left _
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum, tsum_mul_left,
    tsum_geometric_of_lt_one hρ0 hρ1]

/-- `L^q` norm of `3 ^ (t * L)` from an exponential moment of `L`. -/
theorem aux_aux_macro_moment_bank_eLpNorm_rpow_three_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (L : α → ℕ) (t q : ℝ) (hq : 0 < q) (B : ℝ)
    (hB : ∫⁻ om, ENNReal.ofReal (Real.exp (q * t * Real.log 3 * (L om : ℝ))) ∂μ ≤
      ENNReal.ofReal B) :
    eLpNorm (fun om => (3 : ℝ) ^ (t * (L om : ℝ))) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal B ^ (1 / q) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (by simpa using hq) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq.le]
  refine ENNReal.rpow_le_rpow (le_trans (le_of_eq ?_) hB) (by positivity)
  congr 1
  funext om
  rw [Real.enorm_of_nonneg (by positivity), ENNReal.ofReal_rpow_of_nonneg (by positivity) hq.le,
    ← Real.rpow_mul (by norm_num), Real.rpow_def_of_pos (by norm_num)]
  congr 2
  ring


/-- The one-prefix tail of `in_6_16`, in geometric form. -/
theorem aux_aux_macro_moment_bank_tail_geometric {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M) (alpha κ : ℝ)
    (hδC : M.delta ≤ Sreg.C⁻¹) (hα : alpha ∈ Sreg.alphaRange)
    (hκ : κ = (1 - alpha) ^ 2 / (Sreg.C * M.delta ^ 2 * |Real.log M.delta|))
    (hκ0 : 0 ≤ κ) (L m : ℕ) (y : SpatialCoordinates d) (k : ℕ) :
    (chaosSampleLaw M).toMeasure {om | k < Sreg.prefixLen L alpha m y om} ≤
      ENNReal.ofReal (Sreg.C * Real.exp (κ * Sreg.C) * Real.exp (-κ * k)) := by
  refine (Sreg.tail L alpha hδC hα m y k).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [show Sreg.C * Real.exp (κ * Sreg.C) * Real.exp (-κ * k) =
    Sreg.C * (Real.exp (κ * Sreg.C) * Real.exp (-κ * k)) by ring]
  refine mul_le_mul_of_nonneg_left ?_ Sreg.C_pos.le
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h1 : (1 - alpha) ^ 2 * max ((k : ℝ) - Sreg.C) 0 /
      (Sreg.C * M.delta ^ 2 * |Real.log M.delta|) = κ * max ((k : ℝ) - Sreg.C) 0 := by
    rw [hκ]
    ring
  rw [h1]
  have h2 : (k : ℝ) - Sreg.C ≤ max ((k : ℝ) - Sreg.C) 0 := le_max_left _ _
  nlinarith

/-- **The prefix bound `Lmac`** (clause `hprefix`): the least level visited infinitely often
by the one-prefix lengths of `in_6_16` at the rescaled centre and the relabelled field, along
the infrared cutoffs `N + L'`.  It is measurable, almost surely attained infinitely often, and
inherits the geometric tail of `in_6_16` uniformly in `N`, because the relabelling preserves
the law of the field. -/
theorem aux_aux_macro_moment_bank_prefix {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M) (alpha κ : ℝ)
    (hδC : M.delta ≤ Sreg.C⁻¹) (hα : alpha ∈ Sreg.alphaRange)
    (hκ : κ = (1 - alpha) ^ 2 / (Sreg.C * M.delta ^ 2 * |Real.log M.delta|))
    (hκ0 : 0 < κ) (z : SpatialCoordinates d) :
    ∃ Lmac : ℕ → BilateralField d → ℕ,
      (∀ N, Measurable (Lmac N)) ∧
      (∀ N k : ℕ, (chaosSampleLaw M).toMeasure {om | k < Lmac N om} ≤
        ENNReal.ofReal (Sreg.C * Real.exp (κ * Sreg.C) * Real.exp (-κ * k))) ∧
      (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N L0 : ℕ,
        ∃ L' : ℕ, L0 ≤ L' ∧
          Sreg.prefixLen (N + L') alpha N ((3 : ℝ) ^ N • z)
            (aux_aux_macro_moment_bank_relabel N om) ≤ Lmac N om) := by
  set μ := (chaosSampleLaw M).toMeasure with hμ
  set f : ℕ → ℕ → BilateralField d → ℕ := fun N L' om =>
    Sreg.prefixLen (N + L') alpha N ((3 : ℝ) ^ N • z)
      (aux_aux_macro_moment_bank_relabel N om) with hf
  have hfmeas : ∀ N L', Measurable (f N L') := fun N L' =>
    (Sreg.prefix_measurable _ _ _ _).comp
      (aux_aux_macro_moment_bank_relabel_measurePreserving M N).measurable
  set T : ℕ → ℝ≥0∞ := fun k =>
    ENNReal.ofReal (Sreg.C * Real.exp (κ * Sreg.C) * Real.exp (-κ * k)) with hT
  have hftail : ∀ N k L', μ {om | k < f N L' om} ≤ T k := by
    intro N k L'
    have hpres := aux_aux_macro_moment_bank_relabel_measurePreserving M N
    have hset : {om | k < f N L' om} = aux_aux_macro_moment_bank_relabel N ⁻¹'
        {om | k < Sreg.prefixLen (N + L') alpha N ((3 : ℝ) ^ N • z) om} := rfl
    rw [hset, hpres.measure_preimage
      (measurableSet_lt measurable_const (Sreg.prefix_measurable _ _ _ _)).nullMeasurableSet]
    exact aux_aux_macro_moment_bank_tail_geometric M Sreg alpha κ hδC hα hκ hκ0.le _ _ _ k
  have hT0 : Filter.Tendsto T Filter.atTop (nhds 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    have : Filter.Tendsto (fun k : ℕ => Real.exp (-κ * k)) Filter.atTop (nhds 0) := by
      have h := tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-κ)).le
        (Real.exp_lt_one_iff.2 (by linarith))
      refine h.congr fun k => ?_
      rw [← Real.exp_nat_mul]
      ring_nf
    simpa using this.const_mul (Sreg.C * Real.exp (κ * Sreg.C))
  refine ⟨fun N => aux_aux_macro_moment_bank_ioBound (f N), fun N =>
    aux_aux_macro_moment_bank_ioBound_measurable (f N) (hfmeas N), ?_, ?_⟩
  · intro N k
    exact aux_aux_macro_moment_bank_measure_lt_ioBound_le μ (f N) k (T k) (hftail N k)
  · rw [ae_all_iff]
    intro N
    exact aux_aux_macro_moment_bank_ae_ioBound_attained μ (f N) T (fun k L => hftail N k L) hT0


/-- The disorder threshold of the prefix clause, chosen from the dimension, `t₁` and the
aggregation exponent before the model: below it `in_6_16`'s tail applies at the Hölder
exponent `1 - (d - t₁)/4` and its rate beats the exponential moment of order `2P t₁ log 3`. -/
theorem aux_aux_macro_moment_bank_threshold {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (t1 Pexp : ℝ) (ht1 : (d : ℝ) - 1 < t1) (ht1' : t1 < d) (ht10 : 0 ≤ t1) (hP1 : 1 ≤ Pexp) :
    ∃ dA : ℝ, 0 < dA ∧ ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M),
      M.delta ≤ dA →
      M.delta ≤ Sreg.C⁻¹ ∧ 1 - ((d : ℝ) - t1) / 4 ∈ Sreg.alphaRange ∧
        2 * Pexp * t1 * Real.log 3 <
          (1 - (1 - ((d : ℝ) - t1) / 4)) ^ 2 / (Sreg.C * M.delta ^ 2 * |Real.log M.delta|) := by
  obtain ⟨Cd, hCd⟩ : ∃ Cd : ℝ, Cd = ((d : ℝ) + 1) ^ 2 *
      max 1 (Classical.choose (SubdiffusiveProcess.Frozen.Section6.cutoff_holder_regularity d)) := ⟨_, rfl⟩
  have hCd1 : 1 ≤ Cd := by
    rw [hCd]
    have h1 : (1 : ℝ) ≤ ((d : ℝ) + 1) ^ 2 := by
      have : (1 : ℝ) ≤ (d : ℝ) + 1 := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
      nlinarith
    have h2 : (1 : ℝ) ≤
        max 1 (Classical.choose (SubdiffusiveProcess.Frozen.Section6.cutoff_holder_regularity d)) :=
      le_max_left _ _
    nlinarith
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = ((d : ℝ) - t1) / 4 := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; linarith
  have ha1 : a < 1 / 4 := by rw [ha]; linarith
  obtain ⟨lam, hlamdef⟩ : ∃ lam : ℝ, lam = 2 * Pexp * t1 * Real.log 3 := ⟨_, rfl⟩
  have hlam : 0 ≤ lam := by
    rw [hlamdef]
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
    have : (0 : ℝ) ≤ Pexp := by linarith
    positivity
  have hCd0 : 0 < Cd := by linarith
  refine ⟨min (min (1 / 2) Cd⁻¹) (min ((a / Cd) ^ 2) (a ^ 2 / (2 * Cd * (lam + 1)))), ?_, ?_⟩
  · refine lt_min (lt_min (by norm_num) (inv_pos.2 hCd0)) (lt_min (by positivity) ?_)
    have : 0 < 2 * Cd * (lam + 1) := by positivity
    positivity
  intro M Sreg hδA
  have hδ0 : 0 < M.delta := M.shellPrefix.delta_pos
  have hCeq : Sreg.C = Cd := by rw [Sreg.C_eq_dimensional, hCd]
  obtain ⟨hδC, hα, hκlam⟩ :=
    aux_aux_macro_moment_bank_delta_facts Cd a lam M.delta hCd1 ha0 ha1 hlam hδ0 hδA
  rw [← hCeq] at hδC hα hκlam
  rw [← Sreg.alphaRange_eq, ha] at hα
  rw [ha, hlamdef] at hκlam
  exact ⟨hδC, hα, hκlam⟩

/-- **Per-model step**: from the threshold facts and the moment inputs, build the bank. -/
theorem aux_aux_macro_moment_bank_per_model {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (t1 : ℝ) (ht10 : 0 ≤ t1) (k : ℕ) (ps : Fin k → ℝ) (Pexp : ℝ)
    (hP1 : 1 ≤ Pexp) (hpsP : ∀ i, ps i ≤ Pexp)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hδC : M.delta ≤ Sreg.C⁻¹) (hα : 1 - ((d : ℝ) - t1) / 4 ∈ Sreg.alphaRange)
    (hκlam : 2 * Pexp * t1 * Real.log 3 <
      (1 - (1 - ((d : ℝ) - t1) / 4)) ^ 2 / (Sreg.C * M.delta ^ 2 * |Real.log M.delta|))
    (beta Cext : ℝ) (hb1 : beta < 1) (hCext : 0 < Cext)
    (hext : ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
        ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
      (a : PositiveCoefficient (centeredCube z r hr))
      (G : SpatialCoordinates d → ℝ) (b : weakSobolevGraph (centeredCube z r hr)),
      ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)) →
      IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G →
      ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G →
      dirichletResponse (killedResponseSpace hP) a b ≤
        Cext * E.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 * r ^ ((d : ℝ) - 2) *
          (r ^ beta *
            holderSeminorm beta
              (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2)
    (Kco : ℕ → BilateralField d → ℝ)
    (hKco : ∀ N om, ∀ v : killedSobolevGraph (centeredCube z r hr),
      cubeFractionalSqNorm hd z r hr threeQuarterOrder
          (v : SobolevData (centeredCube z r hr)).1 ≤
        Kco N om * sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr)
          (v : SobolevData (centeredCube z r hr)) (v : SobolevData (centeredCube z r hr)))
    (CK : ℝ)
    (hKmem : ∀ N, MemLp (Kco N) (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure)
    (hKbd : ∀ N, eLpNorm (Kco N) (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal CK)
    (Kext : ℕ → BilateralField d → ℝ) (CL : ℝ)
    (hKextmem : ∀ N, MemLp (Kext N) (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure)
    (hKextbd : ∀ N, eLpNorm (Kext N) (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal CL)
    (hdom : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N,
      E.Lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r ((beta - 1 / 2) / 4) 2 ≤
        Kext N om) :
    ∃ (Lmac : ℕ → BilateralField d → ℕ) (Kmac : ℕ → BilateralField d → ℝ)
      (Cbound : Fin k → ℝ),
      (∀ N om, 0 ≤ Kmac N om) ∧
      (∀ i N, MemLp (Kmac N) (ENNReal.ofReal (ps i))
        (chaosSampleLaw M).toMeasure) ∧
      (∀ i N, eLpNorm (Kmac N) (ENNReal.ofReal (ps i))
          (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cbound i)) ∧
      (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N L0 : ℕ,
        ∃ L' : ℕ, L0 ≤ L' ∧
          Sreg.prefixLen (N + L') (1 - ((d : ℝ) - t1) / 4) N
            ((3 : ℝ) ^ N • z)
            (fun j => ContinuousMap.compRightContinuousMap ℝ
              (⟨fun x : SpatialCoordinates d => (3 : ℝ) ^ (-(N : ℤ)) • x,
                continuous_const.smul continuous_id⟩ :
                C(SpatialCoordinates d, SpatialCoordinates d))
              (om (j - (N : ℤ)))) ≤ Lmac N om) ∧
      (∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
          ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
            ContDiff ℝ 2 phi →
            c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
          ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
            ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
            SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
            (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)) *
              sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr)
                (u : SobolevData (centeredCube z r hr))
                (u : SobolevData (centeredCube z r hr)) ≤
                Kmac N om * (Kf + Cphi) ^ 2) ∧
      (∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ N x, x ∈ closedCube z r hr →
          (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)) * Real.exp (|H om x|) ≤ Kmac N om) := by
  have hQ1 : 1 ≤ 2 * Pexp := by linarith
  have hlam : 0 ≤ 2 * Pexp * t1 * Real.log 3 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
    have : (0 : ℝ) ≤ Pexp := by linarith
    positivity
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = (1 - (1 - ((d : ℝ) - t1) / 4)) ^ 2 /
      (Sreg.C * M.delta ^ 2 * |Real.log M.delta|) := ⟨_, rfl⟩
  rw [← hκ] at hκlam
  have hκ0 : 0 < κ := lt_of_le_of_lt hlam hκlam
  obtain ⟨Lmac, hLmeas, hLtail, hLpre⟩ :=
    aux_aux_macro_moment_bank_prefix M Sreg (1 - ((d : ℝ) - t1) / 4) κ hδC hα hκ hκ0 z
  have hA1 : 1 ≤ Sreg.C * Real.exp (κ * Sreg.C) := by
    have h1 := Sreg.C_ge_one
    have h2 : 1 ≤ Real.exp (κ * Sreg.C) := Real.one_le_exp (by positivity)
    nlinarith
  have hX : ∀ N, eLpNorm (fun om => (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)))
      (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Sreg.C * Real.exp (κ * Sreg.C) * Real.exp κ *
        (1 - Real.exp (-(κ - 2 * Pexp * t1 * Real.log 3)))⁻¹) ^ (1 / (2 * Pexp)) := by
    intro N
    exact aux_aux_macro_moment_bank_eLpNorm_rpow_three_le _ (Lmac N) t1 (2 * Pexp)
      (by linarith) _ (aux_aux_macro_moment_bank_lintegral_exp_le (chaosSampleLaw M).toMeasure
        (Lmac N) (hLmeas N) (Sreg.C * Real.exp (κ * Sreg.C)) κ _ hA1 hlam hκlam (hLtail N))
  obtain ⟨hRmeas, hRdom, hRmem⟩ :=
    aux_aux_macro_moment_bank_reference hd M H hH (closedCube z r hr) (2 * Pexp) hQ1
  exact aux_aux_macro_moment_bank_assemble hd E t1 k ps Pexp hP1 hpsP M Sreg H z r hr hr1
    beta Cext hb1 hCext hext Lmac hLmeas _
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top) hX hLpre
    hRmeas hRdom hRmem Kco hKco CK hKmem hKbd Kext CL hKextmem hKextbd hdom

/-- **Conditional form of the bank**, for the working cubes whose side lies in a set `S`.
The exact conclusion of `aux_macro_moment_bank` is derived from the imported interfaces
(`in_6_16`, `lem_infrared` via the infrared characterization, `lem_coercivity`,
`lem_extension` clause `eq:mfd-2`) together with **one additional input**: an almost-sure
majorant, with uniform-in-`N` moments, of the boundary-extension multiplier
`U_N(Q) = Λ_{σ/2,2}(Q; A_N)` of `eq:mfd-2` on the working cube `Q` itself — the fixed-cube
form of `eq:mfd-3`.  `lem_extension` states `eq:mfd-3` only on grid cubes of side `3^{-k}`,
`k ≤ N`; it supplies this input for `S = {1}`
(`aux_aux_macro_moment_bank_unit_cube_Lam_input`) but not for sides `r < 1`. -/
theorem aux_aux_macro_moment_bank_conditional (S : Set ℝ) :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E)
    (_S : SobolevFoundationalInput d hd) (t1 : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t1 → t1 < d → (∀ i, 1 ≤ ps i) →
    (∃ beta : ℝ, beta ∈ Set.Ioo (1 / 2 : ℝ) 1 ∧
      ∀ p : ℝ, 1 ≤ p → ∃ delta1 : ℝ, 0 < delta1 ∧
        ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
          (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
          InfraredCharacterization M H → M.delta ≤ delta1 →
          ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 → r ∈ S →
          ∃ (Kext : ℕ → BilateralField d → ℝ) (CLam : ℝ),
            (∀ N, MemLp (Kext N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) ∧
            (∀ N, eLpNorm (Kext N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
              ENNReal.ofReal CLam) ∧
            ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N,
              E.Lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r
                ((beta - 1 / 2) / 4) 2 ≤ Kext N om) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 → r ∈ S →
      ∃ (Lmac : ℕ → BilateralField d → ℕ) (Kmac : ℕ → BilateralField d → ℝ)
        (Cbound : Fin k → ℝ),
        (∀ N om, 0 ≤ Kmac N om) ∧
        (∀ i N, MemLp (Kmac N) (ENNReal.ofReal (ps i))
          (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (Kmac N) (ENNReal.ofReal (ps i))
            (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cbound i)) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N L0 : ℕ,
          ∃ L' : ℕ, L0 ≤ L' ∧
            Sreg.prefixLen (N + L') (1 - ((d : ℝ) - t1) / 4) N
              ((3 : ℝ) ^ N • z)
              (fun j => ContinuousMap.compRightContinuousMap ℝ
                (⟨fun x : SpatialCoordinates d => (3 : ℝ) ^ (-(N : ℤ)) • x,
                  continuous_const.smul continuous_id⟩ :
                  C(SpatialCoordinates d, SpatialCoordinates d))
                (om (j - (N : ℤ)))) ≤ Lmac N om) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
          ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
            0 ≤ Kf →
            AEMeasurable F
              (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
            (∀ᵐ x ∂(volume.restrict
              (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
            ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
              ContDiff ℝ 2 phi →
              c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
            ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
              ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
                  =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
              SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
              (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)) *
                sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr)
                  (u : SobolevData (centeredCube z r hr))
                  (u : SobolevData (centeredCube z r hr)) ≤
                  Kmac N om * (Kf + Cphi) ^ 2) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
          ∀ N x, x ∈ closedCube z r hr →
            (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)) * Real.exp (|H om x|) ≤ Kmac N om) := by
  intro d hd _ _ E P X Ssob t1 k ps ht1 ht1' hps hLamIn
  obtain ⟨beta, hbeta, hLamM⟩ := hLamIn
  -- one exponent for all listed orders, doubled for Hölder aggregation
  obtain ⟨Pexp, hPdef⟩ : ∃ Pexp : ℝ, Pexp = 1 + ∑ i, ps i := ⟨_, rfl⟩
  have hsum0 : 0 ≤ ∑ i, ps i := Finset.sum_nonneg fun i _ => by linarith [hps i]
  have hP1 : 1 ≤ Pexp := by rw [hPdef]; linarith
  have hpsP : ∀ i, ps i ≤ Pexp := by
    intro i
    rw [hPdef]
    have := Finset.single_le_sum (f := ps) (fun j _ => by linarith [hps j]) (Finset.mem_univ i)
    linarith
  have hQ1 : 1 ≤ 2 * Pexp := by linarith
  have ht10 : 0 ≤ t1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨Cext, hCext, hext⟩ := (lem_extension d hd E X Ssob).1 beta hbeta
  obtain ⟨dc, hdc, hcoer⟩ := aux_lem_coercivity_compat d hd E P Ssob
  obtain ⟨dL, hdL, hLamQ⟩ := hLamM (2 * Pexp) hQ1
  obtain ⟨dA, hdA0, hthr⟩ := aux_aux_macro_moment_bank_threshold (d := d) t1 Pexp ht1 ht1' ht10 hP1
  refine ⟨min dA (min (dc (2 * Pexp)) dL), lt_min hdA0 (lt_min (hdc _ hQ1) hdL), ?_⟩
  intro M Rm Sreg It H hH hδ z r hr hr1 hrS
  obtain ⟨hδC, hα, hκlam⟩ := hthr M Sreg (hδ.trans (min_le_left _ _))
  obtain ⟨Kco, hKco, hKmom⟩ := hcoer M Rm H hH z r hr hr1
  obtain ⟨CK, hKmem, hKbd⟩ := hKmom (2 * Pexp) hQ1
    (hδ.trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨Kext, CL, hKextmem, hKextbd, hdom⟩ :=
    hLamQ M Rm H hH (hδ.trans ((min_le_right _ _).trans (min_le_right _ _))) z r hr hr1 hrS
  exact aux_aux_macro_moment_bank_per_model hd E t1 ht10 k ps Pexp hP1 hpsP M Sreg H hH
    z r hr hr1 hδC hα hκlam beta Cext hbeta.2 hCext (hext z r hr hr1) Kco
    (fun N om v => ((hKco N om).1 v).2) CK hKmem hKbd Kext CL hKextmem hKextbd hdom

/-- **The missing input holds on unit working cubes.**  For a working cube of side `1`,
`lem_extension`'s grid bound `eq:mfd-3` at depth `k = 0` (the root cube itself, which is the
only grid cube of side `1` in it) dominates `Λ_{σ/2,2}(Q; A_N)` for every `N`, with
uniform moments.  So the only working cubes for which the bank's energy clause lacks an input
are those of side `r < 1`. -/
theorem aux_aux_macro_moment_bank_unit_cube_Lam_input :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_X : in_extension d hd E)
    (_S : SobolevFoundationalInput d hd),
    (∃ beta : ℝ, beta ∈ Set.Ioo (1 / 2 : ℝ) 1 ∧
      ∀ p : ℝ, 1 ≤ p → ∃ delta1 : ℝ, 0 < delta1 ∧
        ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
          (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
          InfraredCharacterization M H → M.delta ≤ delta1 →
          ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 → r ∈ ({1} : Set ℝ) →
          ∃ (Kext : ℕ → BilateralField d → ℝ) (CLam : ℝ),
            (∀ N, MemLp (Kext N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) ∧
            (∀ N, eLpNorm (Kext N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
              ENNReal.ofReal CLam) ∧
            ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N,
              E.Lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r
                ((beta - 1 / 2) / 4) 2 ≤ Kext N om) := by
  intro d hd _ _ E X Ssob
  refine ⟨3 / 4, ⟨by norm_num, by norm_num⟩, ?_⟩
  intro p hp
  obtain ⟨delta0, hdelta0, hgrid⟩ := (lem_extension d hd E X Ssob).2 1 p one_pos hp
    (3 / 4) ⟨by norm_num, by norm_num⟩
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm H hH hδ z r hr _ hr1
  rw [Set.mem_singleton_iff] at hr1
  subst hr1
  obtain ⟨K, Cb, hKmem, hKbd, hae⟩ := hgrid M Rm H hH hδ
    z 1 hr 1 (fun _ => z)
  refine ⟨K, Cb, hKmem, hKbd, ?_⟩
  filter_upwards [hae] with om hom N
  have hw : (fun i => (fun _ : Fin 1 => z) 0 i + (3 : ℝ) ^ (-((0 : ℕ) : ℤ)) *
      (((0 : Fin d → ℤ) i : ℤ) : ℝ)) = z := by
    funext i
    simp
  have hs : (3 : ℝ) ^ (-((0 : ℕ) : ℤ)) = 1 := by simp
  have hsub : centeredCube (fun i => (fun _ : Fin 1 => z) 0 i + (3 : ℝ) ^ (-((0 : ℕ) : ℤ)) *
      (((0 : Fin d → ℤ) i : ℤ) : ℝ)) ((3 : ℝ) ^ (-((0 : ℕ) : ℤ))) (by positivity) ≤
      centeredCube z 1 hr := by
    intro x hx
    change x ∈ Metric.ball _ (_ / 2) at hx
    change x ∈ Metric.ball z (1 / 2)
    rw [hw, hs] at hx
    exact hx
  have h := hom N 0 0 0 (Nat.zero_le N) hsub
  rw [hw, hs] at h
  have hlam := E.lam_pos z 1 hr (cutoffPositiveCoefficient M H om N z hr) z 1
    ((3 / 4 - 1 / 2) / 4) 2
  have hinv : 0 < (E.lam z 1 hr (cutoffPositiveCoefficient M H om N z hr) z 1
    ((3 / 4 - 1 / 2) / 4) 2)⁻¹ := inv_pos.2 hlam
  simp only [Real.one_rpow, mul_one] at h
  linarith

/-- **The bank on unit working cubes**, from the imported interfaces alone. -/
theorem aux_aux_macro_moment_bank_unit_cube :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E)
    (_S : SobolevFoundationalInput d hd) (t1 : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t1 → t1 < d → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 → r ∈ ({1} : Set ℝ) →
      ∃ (Lmac : ℕ → BilateralField d → ℕ) (Kmac : ℕ → BilateralField d → ℝ)
        (Cbound : Fin k → ℝ),
        (∀ N om, 0 ≤ Kmac N om) ∧
        (∀ i N, MemLp (Kmac N) (ENNReal.ofReal (ps i))
          (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (Kmac N) (ENNReal.ofReal (ps i))
            (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cbound i)) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N L0 : ℕ,
          ∃ L' : ℕ, L0 ≤ L' ∧
            Sreg.prefixLen (N + L') (1 - ((d : ℝ) - t1) / 4) N
              ((3 : ℝ) ^ N • z)
              (fun j => ContinuousMap.compRightContinuousMap ℝ
                (⟨fun x : SpatialCoordinates d => (3 : ℝ) ^ (-(N : ℤ)) • x,
                  continuous_const.smul continuous_id⟩ :
                  C(SpatialCoordinates d, SpatialCoordinates d))
                (om (j - (N : ℤ)))) ≤ Lmac N om) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
          ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
            0 ≤ Kf →
            AEMeasurable F
              (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
            (∀ᵐ x ∂(volume.restrict
              (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
            ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
              ContDiff ℝ 2 phi →
              c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
            ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
              ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
                  =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
              SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
              (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)) *
                sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr)
                  (u : SobolevData (centeredCube z r hr))
                  (u : SobolevData (centeredCube z r hr)) ≤
                  Kmac N om * (Kf + Cphi) ^ 2) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
          ∀ N x, x ∈ closedCube z r hr →
            (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)) * Real.exp (|H om x|) ≤ Kmac N om) := by
  intro d hd _ _ E P X Ssob t1 k ps ht1 ht1' hps
  exact aux_aux_macro_moment_bank_conditional {1} d hd E P X Ssob t1 k ps ht1 ht1' hps
    (aux_aux_macro_moment_bank_unit_cube_Lam_input d hd E X Ssob)




section RouteW
open Homogenization Homogenization.Book.Ch02

/-- rpow bookkeeping for the ancestor discount. -/
theorem aux_aux_macro_moment_bank_rpow_split (s s' : ℝ) (j n : ℕ) :
    Real.rpow (3 : ℝ) (-s * 2 * (n : ℝ)) * Real.rpow (3 : ℝ) (2 * s' * ((j + n : ℕ) : ℝ)) =
      Real.rpow (3 : ℝ) (2 * s' * (j : ℝ)) *
        (Real.rpow (3 : ℝ) (-2 * (s - s'))) ^ n := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  change (3 : ℝ) ^ (-s * 2 * (n : ℝ)) * (3 : ℝ) ^ (2 * s' * ((j + n : ℕ) : ℝ)) =
      (3 : ℝ) ^ (2 * s' * (j : ℝ)) * ((3 : ℝ) ^ (-2 * (s - s'))) ^ n
  rw [← Real.rpow_natCast ((3 : ℝ) ^ (-2 * (s - s'))) n, ← Real.rpow_mul h3.le,
    ← Real.rpow_add h3, ← Real.rpow_add h3]
  congr 1
  push_cast
  ring

/-- **Ancestor discount, analytic core.**  If every depth-`n` descendant of the root
`Q` carries, for the family `F`, the same `|b|` as some depth-`(j+n)` descendant of `Q`
for the family `G`, then `Λ_{s,2}(Q;F) ≤ C(s,s') 3^{2 s' j} Λ_{s',2}(Q;G)` for
`0 < s' < s`. -/
theorem aux_aux_macro_moment_bank_LambdaSqFinite_ancestor {d : ℕ} (Q : TriadicCube d) (F G : TriadicCoeffFamily d)
    (s s' : ℝ) (hs' : 0 < s') (hss : s' < s) (j : ℕ)
    (hmap : ∀ (n : ℕ) (R : TriadicCube d),
      R ∈ descendantsAtScale Q (Q.scale - (n : ℤ)) →
        ∃ R' ∈ descendantsAtScale Q (Q.scale - ((j + n : ℕ) : ℤ)),
          coarseBMatrixNorm R F = coarseBMatrixNorm R' G)
    (hsumG : Summable (fun n : ℕ => Book.Ch02.geometricWeight s' 2 n *
      (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) G) ^ ((2 : ℝ) / 2))) :
    LambdaSqFinite Q s 2 F ≤
      Book.Ch02.geometricDiscount s 2 / Book.Ch02.geometricDiscount s' 2 *
        (1 - Real.rpow (3 : ℝ) (-2 * (s - s')))⁻¹ *
        Real.rpow (3 : ℝ) (2 * s' * (j : ℝ)) * LambdaSqFinite Q s' 2 G := by
  classical
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hs : 0 < s := hs'.trans hss
  set A : ℕ → ℝ := fun n => maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) F with hA
  set B : ℕ → ℝ := fun n => maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) G with hB
  have hA0 : ∀ n, 0 ≤ A n := fun n => w19_maxDescendantBMatrixNormAtScale_nonneg _ _ _
  have hB0 : ∀ n, 0 ≤ B n := fun n => w19_maxDescendantBMatrixNormAtScale_nonneg _ _ _
  have h22 : ((2 : ℝ) / 2) = 1 := by norm_num
  -- the two series, with the exponents `2/2 = 1` removed
  have hLF : LambdaSqFinite Q s 2 F = ∑' n : ℕ, Book.Ch02.geometricWeight s 2 n * A n := by
    show (∑' n : ℕ, Book.Ch02.geometricWeight s 2 n * (A n) ^ ((2 : ℝ) / 2)) ^ ((2 : ℝ) / 2) = _
    rw [h22]
    simp only [Real.rpow_one]
  have hLG : LambdaSqFinite Q s' 2 G = ∑' n : ℕ, Book.Ch02.geometricWeight s' 2 n * B n := by
    show (∑' n : ℕ, Book.Ch02.geometricWeight s' 2 n * (B n) ^ ((2 : ℝ) / 2)) ^ ((2 : ℝ) / 2) = _
    rw [h22]
    simp only [Real.rpow_one]
  have hsumG' : Summable (fun n : ℕ => Book.Ch02.geometricWeight s' 2 n * B n) := by
    simpa only [h22, Real.rpow_one] using hsumG
  -- step 1: `A n ≤ B (j+n)`
  have hAB : ∀ n, A n ≤ B (j + n) := by
    intro n
    change finsetSupReal _ _ ≤ finsetSupReal _ _
    unfold finsetSupReal
    set S := descendantsAtScale Q (Q.scale - (n : ℤ))
    rcases S.eq_empty_or_nonempty with hS | hS
    · rw [hS]
      simp only [Finset.coe_empty, Set.image_empty, Real.sSup_empty]
      exact hB0 (j + n)
    · refine csSup_le (hS.to_set.image _) ?_
      rintro y ⟨R, hR, rfl⟩
      obtain ⟨R', hR', heq⟩ := hmap n R hR
      show coarseBMatrixNorm R F ≤ _
      rw [heq]
      exact le_csSup ((Finset.finite_toSet _).image _).bddAbove ⟨R', hR', rfl⟩
  -- step 2: a single weighted term of the `G` series is at most `Λ_{s'}`
  have hc' : 0 < Book.Ch02.geometricDiscount s' 2 := w19_geometricDiscount_pos s' 2 hs' two_pos
  have hc : 0 < Book.Ch02.geometricDiscount s 2 := w19_geometricDiscount_pos s 2 hs two_pos
  have hterm : ∀ m, Book.Ch02.geometricWeight s' 2 m * B m ≤ LambdaSqFinite Q s' 2 G := by
    intro m
    rw [hLG]
    exact hsumG'.le_tsum m (fun i _ => mul_nonneg
      (mul_nonneg hc'.le (Real.rpow_nonneg h3.le _)) (hB0 i))
  have hLG0 : 0 ≤ LambdaSqFinite Q s' 2 G := (mul_nonneg
      (mul_nonneg hc'.le (Real.rpow_nonneg h3.le _)) (hB0 0)).trans (hterm 0)
  set L := LambdaSqFinite Q s' 2 G with hL
  -- step 3: `B (j+n) ≤ L c'⁻¹ 3^{2 s'(j+n)}`
  have hBle : ∀ m : ℕ, B m ≤ L * (Book.Ch02.geometricDiscount s' 2)⁻¹ *
      Real.rpow (3 : ℝ) (2 * s' * (m : ℝ)) := by
    intro m
    have hw : Book.Ch02.geometricWeight s' 2 m = Book.Ch02.geometricDiscount s' 2 *
        Real.rpow (3 : ℝ) (-s' * 2 * (m : ℝ)) := rfl
    have hpos : 0 < Real.rpow (3 : ℝ) (-s' * 2 * (m : ℝ)) := Real.rpow_pos_of_pos h3 _
    have hinv : Real.rpow (3 : ℝ) (2 * s' * (m : ℝ)) =
        (Real.rpow (3 : ℝ) (-s' * 2 * (m : ℝ)))⁻¹ := by
      change (3 : ℝ) ^ (2 * s' * (m : ℝ)) = ((3 : ℝ) ^ (-s' * 2 * (m : ℝ)))⁻¹
      rw [← Real.rpow_neg h3.le]
      congr 1
      ring
    have h := hterm m
    rw [hw] at h
    rw [hinv, mul_assoc, ← mul_inv, le_mul_inv_iff₀ (mul_pos hc' hpos)]
    linarith [h]
  -- step 4: termwise domination and the geometric sum
  set ρ : ℝ := Real.rpow (3 : ℝ) (-2 * (s - s')) with hρ
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg h3.le _
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set K : ℝ := Book.Ch02.geometricDiscount s 2 / Book.Ch02.geometricDiscount s' 2 * L *
      Real.rpow (3 : ℝ) (2 * s' * (j : ℝ)) with hK
  have hdom : ∀ n : ℕ, Book.Ch02.geometricWeight s 2 n * A n ≤ K * ρ ^ n := by
    intro n
    have hw : Book.Ch02.geometricWeight s 2 n = Book.Ch02.geometricDiscount s 2 *
        Real.rpow (3 : ℝ) (-s * 2 * (n : ℝ)) := rfl
    have hwpos : 0 ≤ Book.Ch02.geometricWeight s 2 n := by
      rw [hw]; exact mul_nonneg hc.le (Real.rpow_nonneg h3.le _)
    calc Book.Ch02.geometricWeight s 2 n * A n
        ≤ Book.Ch02.geometricWeight s 2 n * (L * (Book.Ch02.geometricDiscount s' 2)⁻¹ *
            Real.rpow (3 : ℝ) (2 * s' * ((j + n : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left ((hAB n).trans (hBle (j + n))) hwpos
      _ = Book.Ch02.geometricDiscount s 2 / Book.Ch02.geometricDiscount s' 2 * L *
            (Real.rpow (3 : ℝ) (-s * 2 * (n : ℝ)) *
              Real.rpow (3 : ℝ) (2 * s' * ((j + n : ℕ) : ℝ))) := by
          rw [hw]; ring
      _ = K * ρ ^ n := by
          rw [aux_aux_macro_moment_bank_rpow_split s s' j n, hK, hρ]; ring
  have hsumR : Summable (fun n : ℕ => K * ρ ^ n) :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left K
  have hnonneg : ∀ n : ℕ, 0 ≤ Book.Ch02.geometricWeight s 2 n * A n := fun n =>
    mul_nonneg (mul_nonneg hc.le (Real.rpow_nonneg h3.le _)) (hA0 n)
  have hsumA : Summable (fun n : ℕ => Book.Ch02.geometricWeight s 2 n * A n) :=
    Summable.of_nonneg_of_le hnonneg hdom hsumR
  rw [hLF]
  calc (∑' n : ℕ, Book.Ch02.geometricWeight s 2 n * A n)
      ≤ ∑' n : ℕ, K * ρ ^ n := hsumA.tsum_le_tsum hdom hsumR
    _ = K * (1 - ρ)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1]
    _ = _ := by rw [hK]; ring



/-- Translation `x ↦ x + z` is measure preserving from `U` onto its translate. -/
theorem aux_aux_macro_moment_bank_translate_mp {d : ℕ} (z : Vec d) (U : Set (Vec d)) (hU : MeasurableSet U) :
    MeasurePreserving (fun x : Vec d => x + z) (volume.restrict U)
      (volume.restrict (translateSet z U)) := by
  have hmeas : MeasurableSet (translateSet z U) := by
    rw [← preimage_subRight_eq_translateSet z U]
    exact (measurable_sub_const z) hU
  have h := (measurePreserving_add_right (volume : Measure (Vec d)) z).restrict_preimage hmeas
  rwa [preimage_addRight_translateSet_eq] at h

/-- A coefficient object on `U' = U + z`, pulled back to `U`: `c(x) = b(x + z)`. -/
def aux_aux_macro_moment_bank_coeffGen {d : ℕ} (U U' : Domain d) (z : Vec d)
    (h : (U' : Set (Vec d)) = translateSet z (U : Set (Vec d))) (b : CoeffOn U') :
    CoeffOn U where
  toCoeffField := translateCoeffField z b.toCoeffField
  lam := b.lam
  Lam := b.Lam
  lam_pos := b.lam_pos
  lam_le_Lam := b.lam_le_Lam
  aeStronglyMeasurable := by
    intro i j
    have hmp := aux_aux_macro_moment_bank_translate_mp z (U : Set (Vec d)) U.measurableSet
    have hb := b.aeStronglyMeasurable i j
    rw [h] at hb
    have hcomp := hb.comp_measurePreserving hmp
    refine hcomp.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Function.comp_apply]
    by_cases hx : x ∈ (U : Set (Vec d))
    · have hx' : x + z ∈ translateSet z (U : Set (Vec d)) := ⟨x, hx, rfl⟩
      rw [restrictCoeffField_apply_of_mem hx', restrictCoeffField_apply_of_mem hx]
      rfl
    · have hx' : x + z ∉ translateSet z (U : Set (Vec d)) := by
        rw [mem_translateSet_iff_sub_mem]
        simpa using hx
      rw [restrictCoeffField_apply_of_not_mem hx', restrictCoeffField_apply_of_not_mem hx]
  aeElliptic := by
    have hmp := aux_aux_macro_moment_bank_translate_mp z (U : Set (Vec d)) U.measurableSet
    have hb := b.aeElliptic
    rw [h] at hb
    exact hmp.quasiMeasurePreserving.ae hb

/-- **Translation invariance of the public `b` matrix** on arbitrary public domains. -/
theorem aux_aux_macro_moment_bank_bCoarse_translate {d : ℕ} (U U' : Domain d) (z : Vec d)
    (h : (U' : Set (Vec d)) = translateSet z (U : Set (Vec d))) (b : CoeffOn U') :
    Book.Ch02.bCoarse U' b = Book.Ch02.bCoarse U (aux_aux_macro_moment_bank_coeffGen U U' z h b) := by
  have hσ : Book.Ch02.sigmaCoarse U' b =
      Book.Ch02.sigmaCoarse U (aux_aux_macro_moment_bank_coeffGen U U' z h b) := by
    rw [Internal.Ch02.book_sigmaCoarse_eq_sigmaCoarse,
      Internal.Ch02.book_sigmaCoarse_eq_sigmaCoarse]
    rw [show U'.carrier = translateSet z U.carrier from h,
      sigmaCoarse_translateSet_eq_translateCoeffField]
    rfl
  have hσs : Book.Ch02.sigmaStarInvCoarse U' b =
      Book.Ch02.sigmaStarInvCoarse U (aux_aux_macro_moment_bank_coeffGen U U' z h b) := by
    rw [Internal.Ch02.book_sigmaStarInvCoarse_eq_sigmaStarInvCoarse,
      Internal.Ch02.book_sigmaStarInvCoarse_eq_sigmaStarInvCoarse]
    rw [show U'.carrier = translateSet z U.carrier from h,
      sigmaStarInvCoarse_translateSet_eq_translateCoeffField]
    rfl
  have hκ : Book.Ch02.kappaCoarse U' b =
      Book.Ch02.kappaCoarse U (aux_aux_macro_moment_bank_coeffGen U U' z h b) := by
    rw [Internal.Ch02.book_kappaCoarse_eq_kappaCoarse,
      Internal.Ch02.book_kappaCoarse_eq_kappaCoarse]
    rw [show U'.carrier = translateSet z U.carrier from h,
      kappaCoarse_translateSet_eq_translateCoeffField]
    rfl
  unfold Book.Ch02.bCoarse
  simp only [coarseMatrices, hσ, hσs, hκ]

theorem aux_aux_macro_moment_bank_qmp_affine {d : ℕ} (t : ℝ) (ht : t ≠ 0) (v : Vec d) :
    Measure.QuasiMeasurePreserving (fun y : Vec d => t • y + v) volume volume := by
  have h1 : Measure.QuasiMeasurePreserving (fun y : Vec d => t • y) volume volume :=
    Measure.quasiMeasurePreserving_smul volume ht
  have h2 : Measure.QuasiMeasurePreserving (fun y : Vec d => y + v) volume volume :=
    (measurePreserving_add_right volume v).quasiMeasurePreserving
  exact h2.comp h1

theorem aux_aux_macro_moment_bank_ae_restrict_comp {d : ℕ} {f : Vec d → Vec d}
    (hf : Measure.QuasiMeasurePreserving f volume volume) {S S' : Set (Vec d)}
    (hS : MeasurableSet S) (hS' : MeasurableSet S') (hmaps : ∀ y ∈ S', f y ∈ S)
    {P : Vec d → Prop} (h : ∀ᵐ x ∂volume.restrict S, P x) :
    ∀ᵐ y ∂volume.restrict S', P (f y) := by
  rw [ae_restrict_iff' hS] at h
  rw [ae_restrict_iff' hS']
  filter_upwards [hf.ae h] with y hy hyS'
  exact hy (hmaps y hyS')

/-- The shift of `translateCube (3^n • c) R` for a depth-`n` descendant `R` of the unit root
is exactly `c`. -/
theorem aux_aux_macro_moment_bank_chart_shift {d : ℕ} (n : ℕ) (c : Fin d → ℤ) (R : TriadicCube d)
    (hR : R.scale = -(n : ℤ)) (i : Fin d) :
    ((descendantTranslationShift n c i : ℤ) : ℝ) * cubeScaleFactor R = (c i : ℝ) := by
  simp only [descendantTranslationShift, cubeScaleFactor, hR]
  push_cast
  rw [zpow_neg, zpow_natCast]
  field_simp

theorem aux_aux_macro_moment_bank_openCubeSet_origin {d : ℕ} (x : Vec d) :
    x ∈ openCubeSet (originCube d 0) ↔ ∀ i, -(1 / 2 : ℝ) < x i ∧ x i < 1 / 2 := by
  simp [openCubeSet, originCube, cubeScaleFactor]

/-- **Per-cube chart similarity.**  A depth-`n` descendant `R` of the unit root in the chart
of the sub-cube `V`, and its image `R̃` (a depth-`(j+n)` descendant) in the chart of the
ancestor `P ⊇ V`, carry the same `|b|` when the two root coefficients agree a.e. on `V`. -/
theorem aux_aux_macro_moment_bank_coarseBMatrixNorm {d : ℕ} (E : in_J d)
    (z₁ : SpatialCoordinates d) (r₁ : ℝ) (hr₁ : 0 < r₁)
    (a₁ : PositiveCoefficient (centeredCube z₁ r₁ hr₁))
    (z₂ : SpatialCoordinates d) (r₂ : ℝ) (hr₂ : 0 < r₂)
    (a₂ : PositiveCoefficient (centeredCube z₂ r₂ hr₂))
    (wV : SpatialCoordinates d) (ρV : ℝ) (hρV : 0 < ρV)
    (wP : SpatialCoordinates d) (ρP : ℝ) (hρP : 0 < ρP)
    (hV : (centeredCube wV ρV hρV : Set (SpatialCoordinates d)) ⊆ centeredCube z₁ r₁ hr₁)
    (hP : (centeredCube wP ρP hρP : Set (SpatialCoordinates d)) ⊆ centeredCube z₂ r₂ hr₂)
    (j : ℕ) (c : Fin d → ℤ)
    (hρ : ρP = (3 : ℝ) ^ j * ρV)
    (hw : ∀ i, wV i = wP i + ρV * (c i : ℝ))
    (hVdesc : dilateCube (-(j : ℤ)) (translateCube c (originCube d 0)) ∈
      descendantsAtScale (originCube d 0) ((originCube d 0).scale - (j : ℤ)))
    (ha : ∀ᵐ x ∂volume.restrict (centeredCube wV ρV hρV : Set (SpatialCoordinates d)),
      a₁.val x = a₂.val x)
    (n : ℕ) (R : TriadicCube d)
    (hR : R ∈ descendantsAtScale (originCube d 0) ((originCube d 0).scale - (n : ℤ))) :
    dilateCube (-(j : ℤ)) (translateCube (descendantTranslationShift n c) R) ∈
        descendantsAtScale (originCube d 0) ((originCube d 0).scale - ((j + n : ℕ) : ℤ)) ∧
      coarseBMatrixNorm R (E.chart z₁ r₁ hr₁ a₁ wV ρV) =
        coarseBMatrixNorm (dilateCube (-(j : ℤ)) (translateCube (descendantTranslationShift n c) R))
          (E.chart z₂ r₂ hr₂ a₂ wP ρP) := by
  classical
  set O : TriadicCube d := originCube d 0 with hO
  have hOs : O.scale = 0 := by simp [hO, originCube]
  set m : Fin d → ℤ := descendantTranslationShift n c with hm
  set TR : TriadicCube d := translateCube m R with hTR
  set Rt : TriadicCube d := dilateCube (-(j : ℤ)) TR with hRt
  have hRscale : R.scale = -(n : ℤ) := by
    have := descendant_scale_eq_of_mem_descendantsAtScale hR
    rw [this, hOs]; ring
  -- descendant bookkeeping
  have h1 : TR ∈ descendantsAtScale (translateCube c O) (O.scale - (n : ℤ)) := by
    rw [descendantsAtScale_translateCube c O (by omega)]
    refine Finset.mem_image.mpr ⟨R, hR, ?_⟩
    simp [hTR, hm]
  have h2 : Rt ∈ descendantsAtScale (dilateCube (-(j : ℤ)) (translateCube c O))
      ((O.scale - (n : ℤ)) + (-(j : ℤ))) := by
    rw [descendantsAtScale_dilateCube]
    exact Finset.mem_image.mpr ⟨TR, h1, rfl⟩
  have h3 := mem_descendantsAtScale_trans hVdesc h2
  have hmem : Rt ∈ descendantsAtScale O (O.scale - ((j + n : ℕ) : ℤ)) := by
    have he : (O.scale - (n : ℤ)) + (-(j : ℤ)) = O.scale - ((j + n : ℕ) : ℤ) := by
      push_cast; ring
    rwa [he] at h3
  refine ⟨hmem, ?_⟩
  have hRO : openCubeSet R ⊆ openCubeSet O :=
    openCubeSet_subset_of_mem_descendantsAtScale (by omega) hR
  have hRtO : openCubeSet Rt ⊆ openCubeSet O :=
    openCubeSet_subset_of_mem_descendantsAtScale (by push_cast; omega) hmem
  -- the physical shift is `c`
  set sh : Vec d := fun i => (m i : ℝ) * cubeScaleFactor R with hsh
  have hshc : ∀ i, sh i = (c i : ℝ) := fun i => aux_aux_macro_moment_bank_chart_shift n c R hRscale i
  have hTRset : openCubeSet TR = translateSet sh (openCubeSet R) := by
    ext x
    rw [hTR, mem_openCubeSet_translateCube_iff, mem_translateSet_iff_sub_mem]
  have hRset : ((cubeDomain R : Domain d) : Set (Vec d)) =
      translateSet (-sh) ((cubeDomain TR : Domain d) : Set (Vec d)) := by
    simp only [cubeDomain_coe]
    ext x
    rw [mem_translateSet_iff_sub_mem, hTRset, mem_translateSet_iff_sub_mem]
    simp
  -- the three coefficient objects
  set F := E.chart z₁ r₁ hr₁ a₁ wV ρV with hF
  set G := E.chart z₂ r₂ hr₂ a₂ wP ρP with hG
  set fwd : CoeffOn (cubeDomain TR) :=
    aux_aux_macro_moment_bank_coeffGen (cubeDomain TR) (cubeDomain R) (-sh) hRset (F.coeffOn R) with hfwd
  have hA : Book.Ch02.bCoarse (cubeDomain R) (F.coeffOn R) =
      Book.Ch02.bCoarse (cubeDomain TR) fwd :=
    aux_aux_macro_moment_bank_bCoarse_translate (cubeDomain TR) (cubeDomain R) (-sh) hRset (F.coeffOn R)
  set D : CoeffOn (cubeDomain Rt) := CoeffOn.dilate (-(j : ℤ)) fwd with hD
  have hdil := CoeffOn.dilate_isCubeDilation (-(j : ℤ)) fwd
  have hB : Book.Ch02.bCoarse (cubeDomain Rt) D = Book.Ch02.bCoarse (cubeDomain TR) fwd :=
    bCoarse_dilate hdil
  -- the a.e. identification
  have h3j : (3 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
  set f : Vec d → Vec d := fun y => (3 : ℝ) ^ j • y + (-sh) with hf
  have hfq := aux_aux_macro_moment_bank_qmp_affine ((3 : ℝ) ^ j) h3j (-sh)
  have hund : ∀ y : Vec d, undilateVec (-(j : ℤ)) y = (3 : ℝ) ^ j • y := by
    intro y
    simp [undilateVec, triadicDilationFactor]
  have hfmaps : ∀ y ∈ openCubeSet Rt, f y ∈ openCubeSet R := by
    intro y hy
    rw [hRt, openCubeSet_dilateCube, Set.mem_smul_set] at hy
    obtain ⟨x', hx', rfl⟩ := hy
    have hx'' : x' - sh ∈ openCubeSet R := by
      rw [hTRset, mem_translateSet_iff_sub_mem] at hx'
      exact hx'
    have : f (triadicDilationFactor (-(j : ℤ)) • x') = x' - sh := by
      simp only [hf, triadicDilationFactor]
      rw [smul_smul, zpow_neg, zpow_natCast, mul_inv_cancel₀ h3j, one_smul, sub_eq_add_neg]
    rw [this]
    exact hx''
  have hRmeas : MeasurableSet (openCubeSet R) := (cubeDomain R).measurableSet
  have hRtmeas : MeasurableSet (openCubeSet Rt) := (cubeDomain Rt).measurableSet
  have hFR := E.chart_eq z₁ r₁ hr₁ a₁ wV ρV hρV hV R hRO
  have hFR' := aux_aux_macro_moment_bank_ae_restrict_comp hfq hRmeas hRtmeas hfmaps hFR
  have hGR := E.chart_eq z₂ r₂ hr₂ a₂ wP ρP hρP hP Rt hRtO
  set g : Vec d → Vec d := fun y => ρP • y + wP with hg
  have hgq := aux_aux_macro_moment_bank_qmp_affine ρP hρP.ne' wP
  have hgf : ∀ y : Vec d, (fun i => wV i + ρV * f y i) = g y := by
    intro y
    funext i
    simp only [hf, hg, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hshc, hw, hρ]
    ring
  have hVmeas : MeasurableSet (centeredCube wV ρV hρV : Set (SpatialCoordinates d)) :=
    (centeredCube wV ρV hρV).isOpen.measurableSet
  have hgmaps : ∀ y ∈ openCubeSet Rt, g y ∈ (centeredCube wV ρV hρV : Set (SpatialCoordinates d)) := by
    intro y hy
    have hfy := (aux_aux_macro_moment_bank_openCubeSet_origin (f y)).mp (hRO (hfmaps y hy))
    rw [← hgf y, centeredCube_eq_pi]
    intro i _
    obtain ⟨hlo, hhi⟩ := hfy i
    constructor <;> nlinarith
  have hag := aux_aux_macro_moment_bank_ae_restrict_comp hgq hVmeas hRtmeas hgmaps ha
  have hC : CoeffOn.AEEq D (G.coeffOn Rt) := by
    unfold CoeffOn.AEEq
    have hDae := hdil.coeff_ae_eq
    simp only [cubeDomain_coe] at hDae ⊢
    filter_upwards [hDae, hFR', hGR, hag] with y hy1 hy2 hy3 hy4
    have e1 : (fun i => wV i + ρV * ((3 : ℝ) ^ j • y + -sh) i) = ρP • y + wP := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hshc, hw, hρ]
      ring
    have e2 : (fun i => wP i + ρP * y i) = ρP • y + wP := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    calc D.toCoeffField y = dilateCoeffField (-(j : ℤ)) fwd.toCoeffField y := hy1
      _ = (F.coeffOn R).toCoeffField ((3 : ℝ) ^ j • y + -sh) := by
          rw [dilateCoeffField_apply, hund y]
          rfl
      _ = scalarMatrix (a₁.val (fun i => wV i + ρV * ((3 : ℝ) ^ j • y + -sh) i)) := hy2
      _ = scalarMatrix (a₁.val (ρP • y + wP)) := by rw [e1]
      _ = scalarMatrix (a₂.val (ρP • y + wP)) := by rw [hy4]
      _ = (G.coeffOn Rt).toCoeffField y := by rw [hy3, e2]
  unfold coarseBMatrixNorm
  rw [hA, ← hB, bCoarse_eq_ofAEEq hC]


/-- **Ancestor discount at the `in_J` interface.**  If the sub-cube `V` (root 1) is a
depth-`j` triadic descendant of the sub-cube `P` (root 2) and the two root coefficients agree
a.e. on `V`, then for `0 < s' < s ≤ 1`,
`Λ_{s,2}(V) ≤ c_{s,2}/c_{s',2} · (1 - 3^{-2(s-s')})⁻¹ · 3^{2 s' j} · Λ_{s',2}(P)`. -/
theorem aux_aux_macro_moment_bank_Lam_ancestor {d : ℕ} (E : in_J d)
    (z₁ : SpatialCoordinates d) (r₁ : ℝ) (hr₁ : 0 < r₁)
    (a₁ : PositiveCoefficient (centeredCube z₁ r₁ hr₁))
    (z₂ : SpatialCoordinates d) (r₂ : ℝ) (hr₂ : 0 < r₂)
    (a₂ : PositiveCoefficient (centeredCube z₂ r₂ hr₂))
    (wV : SpatialCoordinates d) (ρV : ℝ) (hρV : 0 < ρV)
    (wP : SpatialCoordinates d) (ρP : ℝ) (hρP : 0 < ρP)
    (hV : (centeredCube wV ρV hρV : Set (SpatialCoordinates d)) ⊆ centeredCube z₁ r₁ hr₁)
    (hP : (centeredCube wP ρP hρP : Set (SpatialCoordinates d)) ⊆ centeredCube z₂ r₂ hr₂)
    (j : ℕ) (c : Fin d → ℤ)
    (hρ : ρP = (3 : ℝ) ^ j * ρV)
    (hw : ∀ i, wV i = wP i + ρV * (c i : ℝ))
    (hVdesc : dilateCube (-(j : ℤ)) (translateCube c (originCube d 0)) ∈
      descendantsAtScale (originCube d 0) ((originCube d 0).scale - (j : ℤ)))
    (ha : ∀ᵐ x ∂volume.restrict (centeredCube wV ρV hρV : Set (SpatialCoordinates d)),
      a₁.val x = a₂.val x)
    (s s' : ℝ) (hs' : 0 < s') (hss : s' < s) (hs1 : s ≤ 1) :
    E.Lam z₁ r₁ hr₁ a₁ wV ρV s 2 ≤
      Book.Ch02.geometricDiscount s 2 / Book.Ch02.geometricDiscount s' 2 *
        (1 - Real.rpow (3 : ℝ) (-2 * (s - s')))⁻¹ *
        Real.rpow (3 : ℝ) (2 * s' * (j : ℝ)) * E.Lam z₂ r₂ hr₂ a₂ wP ρP s' 2 := by
  have hs : 0 < s := hs'.trans hss
  have h2 : ((2 : ℝ≥0∞)).toReal = (2 : ℝ) := by simp
  rw [w20_Lam_eq_finite E z₁ r₁ hr₁ a₁ wV ρV hρV hV s ⟨hs, hs1⟩ 2 one_le_two (by simp),
    w20_Lam_eq_finite E z₂ r₂ hr₂ a₂ wP ρP hρP hP s' ⟨hs', hss.le.trans hs1⟩ 2 one_le_two
      (by simp), h2]
  refine aux_aux_macro_moment_bank_LambdaSqFinite_ancestor (originCube d 0) _ _ s s' hs' hss j ?_ ?_
  · intro n R hR
    obtain ⟨hmem, heq⟩ := aux_aux_macro_moment_bank_coarseBMatrixNorm E z₁ r₁ hr₁ a₁ z₂ r₂ hr₂ a₂ wV ρV hρV
      wP ρP hρP hV hP j c hρ hw hVdesc ha n R hR
    exact ⟨_, hmem, heq⟩
  · exact w20_summable_Lam E z₂ r₂ hr₂ a₂ wP ρP hρP hP s' ⟨hs', hss.le.trans hs1⟩

end RouteW

/-- **Glued harmonic-replacement competitor.**  For finitely many pairwise disjoint open
cells inside `Q`, the Dirichlet response of `b` on `Q` is at most the sum of the cell
responses of the restrictions of `b` plus the energy of `b` on the uncovered part of `Q`. -/
theorem aux_aux_macro_moment_bank_glue_le {d : ℕ} {Q : Opens (SpatialCoordinates d)} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (cell : ι → Opens (SpatialCoordinates d)) (hle : ∀ k, cell k ≤ Q)
    (hdisj : Pairwise (fun k l => Disjoint (cell k : Set (SpatialCoordinates d))
      (cell l : Set (SpatialCoordinates d))))
    (hPQ : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Q,
      ‖(u : SobolevData Q).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Q) u‖)
    (hPc : ∀ k, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (cell k),
      ‖(u : SobolevData (cell k)).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph (cell k)) u‖)
    (a : PositiveCoefficient Q) (ac : ∀ k, PositiveCoefficient (cell k))
    (hac : ∀ k, ∀ᵐ x ∂volume.restrict (cell k : Set (SpatialCoordinates d)),
      (ac k).val x = a.val x)
    (b : weakSobolevGraph Q) :
    dirichletResponse (killedResponseSpace hPQ) a b ≤
      ∑ k, dirichletResponse (killedResponseSpace (hPc k)) (ac k)
          ⟨sobolevDataRestrict (hle k) (b : SobolevData Q),
            sobolevDataRestrict_mem_weak (hle k) b.property⟩ +
        ∑ i : Fin d, ∫ x in (Q : Set (SpatialCoordinates d)) \
            ⋃ k, (cell k : Set (SpatialCoordinates d)),
          a.val x * ((b : SobolevData Q).2 i x * (b : SobolevData Q).2 i x) := by
  classical
  obtain ⟨bk, hbk⟩ : ∃ bk : ∀ k, weakSobolevGraph (cell k), bk = fun k =>
      ⟨sobolevDataRestrict (hle k) (b : SobolevData Q),
        sobolevDataRestrict_mem_weak (hle k) b.property⟩ := ⟨_, rfl⟩
  have hgoalb : ∀ k, (⟨sobolevDataRestrict (hle k) (b : SobolevData Q),
        sobolevDataRestrict_mem_weak (hle k) b.property⟩ : weakSobolevGraph (cell k)) = bk k := by
    intro k; rw [hbk]
  simp only [hgoalb]
  obtain ⟨uk, huk⟩ : ∃ uk : ∀ k, weakSobolevGraph (cell k), uk = fun k =>
      dirichletMinimizer (killedResponseSpace (hPc k)) (ac k) (bk k) := ⟨_, rfl⟩
  obtain ⟨wk, hwk⟩ : ∃ wk : ∀ k, SobolevData (cell k), wk = fun k =>
      (uk k : SobolevData (cell k)) - (bk k : SobolevData (cell k)) := ⟨_, rfl⟩
  have hwkK : ∀ k, wk k ∈ killedSobolevGraph (cell k) := by
    intro k
    rw [hwk, huk]
    exact dirichletMinimizer_mem_affine (killedResponseSpace (hPc k)) (ac k) (bk k)
  obtain ⟨Wc, hWc⟩ : ∃ Wc : SobolevData Q,
      Wc = ∑ k, zeroExtensionSobolevData (hle k) (wk k) := ⟨_, rfl⟩
  have hWcK : Wc ∈ killedSobolevGraph Q := by
    rw [hWc]
    exact Submodule.sum_mem _ (fun k _ =>
      lane2_zeroExtensionSobolevData_mem_killed (hle k) (hwkK k))
  have hle1 : dirichletResponse (killedResponseSpace hPQ) a b ≤
      sobolevCoefficientForm a ((b : SobolevData Q) + Wc) ((b : SobolevData Q) + Wc) :=
    (dirichletResponse_isLeast (killedResponseSpace hPQ) a b).2 ⟨⟨Wc, hWcK⟩, rfl⟩
  refine hle1.trans (le_of_eq ?_)
  obtain ⟨X, hX⟩ : ∃ X : Fin d → DomainL2 Q, X = fun i => ((b : SobolevData Q) + Wc).2 i :=
    ⟨_, rfl⟩
  -- the gradient of the glued competitor, coordinatewise and a.e.
  have hXsum : ∀ i, X i = (b : SobolevData Q).2 i +
      ∑ k, zeroExtensionLp (hle k) ((wk k).2 i) := by
    intro i
    have h1 : Wc.2 i = ∑ k, zeroExtensionLp (hle k) ((wk k).2 i) := by
      rw [hWc, Prod.snd_sum, Finset.sum_apply]
      rfl
    simp only [hX, Prod.snd_add, Pi.add_apply, h1]
  have hXae : ∀ i, ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      X i x = (b : SobolevData Q).2 i x +
        ∑ k, (cell k : Set (SpatialCoordinates d)).indicator ((wk k).2 i) x := by
    intro i
    have hall : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
        ∀ k, (zeroExtensionLp (hle k) ((wk k).2 i) : SpatialCoordinates d → ℝ) x =
          (cell k : Set (SpatialCoordinates d)).indicator ((wk k).2 i) x :=
      ae_all_iff.2 (fun k => zeroExtensionLp_coeFn (hle k) ((wk k).2 i))
    filter_upwards [hall, Lp.coeFn_add ((b : SobolevData Q).2 i)
      (∑ k, zeroExtensionLp (hle k) ((wk k).2 i)),
      lane2_Lp_coeFn_sum (fun k => zeroExtensionLp (hle k) ((wk k).2 i)) Finset.univ]
      with x h1 h2 h3
    rw [hXsum i, h2, Pi.add_apply, h3]
    congr 1
    exact Finset.sum_congr rfl (fun k _ => h1 k)
  -- on a cell the competitor is the cell minimizer
  have hXcell : ∀ i k, ∀ᵐ x ∂volume.restrict (cell k : Set (SpatialCoordinates d)),
      X i x = (uk k : SobolevData (cell k)).2 i x := by
    intro i k
    have h1 := ae_restrict_of_ae_restrict_of_subset
      (μ := (volume : Measure (SpatialCoordinates d))) (hle k) (hXae i)
    have hbk2 : (bk k : SobolevData (cell k)).2 i =
        domainLpRestrict (hle k) ((b : SobolevData Q).2 i) := by rw [hbk]; rfl
    have h2 : ((bk k : SobolevData (cell k)).2 i : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (cell k : Set (SpatialCoordinates d))]
          ((b : SobolevData Q).2 i) := by
      rw [hbk2]
      exact domainLpRestrict_coeFn (hle k) _
    have h3 := Lp.coeFn_sub ((uk k : SobolevData (cell k)).2 i)
      ((bk k : SobolevData (cell k)).2 i)
    filter_upwards [h1, h2, h3, ae_restrict_mem (cell k).isOpen.measurableSet]
      with x hx1 hx2 hx3 hxk
    rw [hx1]
    rw [Finset.sum_eq_single k]
    · rw [Set.indicator_of_mem hxk]
      have hw2 : (wk k).2 i = (uk k : SobolevData (cell k)).2 i -
          (bk k : SobolevData (cell k)).2 i := by rw [hwk]; rfl
      rw [hw2, hx3, Pi.sub_apply, hx2]
      ring
    · intro l _ hlk
      rw [Set.indicator_of_notMem]
      exact fun hxl => (Set.disjoint_left.mp (hdisj hlk) hxl) hxk
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  -- off the cells the competitor is `b`
  obtain ⟨S, hS⟩ : ∃ S : Set (SpatialCoordinates d), S = (Q : Set (SpatialCoordinates d)) \
      ⋃ k, (cell k : Set (SpatialCoordinates d)) := ⟨_, rfl⟩
  have hSmeas : MeasurableSet S := by
    rw [hS]
    exact Q.isOpen.measurableSet.diff
      (MeasurableSet.iUnion fun k => (cell k).isOpen.measurableSet)
  have hXoff : ∀ i, ∀ᵐ x ∂volume.restrict S, X i x = (b : SobolevData Q).2 i x := by
    intro i
    have h1 := ae_restrict_of_ae_restrict_of_subset
      (μ := (volume : Measure (SpatialCoordinates d)))
      (show S ⊆ (Q : Set (SpatialCoordinates d)) by rw [hS]; exact Set.diff_subset) (hXae i)
    filter_upwards [h1, ae_restrict_mem hSmeas] with x hx hxS
    rw [hS] at hxS
    rw [hx]
    have : ∀ k, (cell k : Set (SpatialCoordinates d)).indicator ((wk k).2 i) x = 0 := by
      intro k
      exact Set.indicator_of_notMem (fun hxk => hxS.2 (Set.mem_iUnion.2 ⟨k, hxk⟩)) _
    simp [this]
  -- integrability on `Q`
  obtain ⟨Ca, hCa⟩ := lane2_coeff_ae_bound a
  have hint : ∀ i, IntegrableOn (fun x => a.val x * (X i x * X i x))
      (Q : Set (SpatialCoordinates d)) volume := fun i =>
    lane2_integrableOn_coeff_mul (Lp.aestronglyMeasurable _) hCa (Lp.memLp _) (Lp.memLp _)
  -- split each coordinate integral
  have hsplit : ∀ i, (∫ x in (Q : Set (SpatialCoordinates d)), a.val x * (X i x * X i x)) =
      (∑ k, ∫ x in (cell k : Set (SpatialCoordinates d)), a.val x * (X i x * X i x)) +
        ∫ x in S, a.val x * (X i x * X i x) := by
    intro i
    have hU : (Q : Set (SpatialCoordinates d)) =
        (⋃ k, (cell k : Set (SpatialCoordinates d))) ∪ S := by
      rw [hS, Set.union_diff_self, Set.union_eq_right.mpr (Set.iUnion_subset fun k => hle k)]
    have hdj : Disjoint (⋃ k, (cell k : Set (SpatialCoordinates d))) S := by
      rw [hS]
      exact Set.disjoint_sdiff_right
    have hsubU : (⋃ k, (cell k : Set (SpatialCoordinates d))) ⊆ (Q : Set (SpatialCoordinates d)) :=
      Set.iUnion_subset fun k => hle k
    have hsubS : S ⊆ (Q : Set (SpatialCoordinates d)) := by rw [hS]; exact Set.diff_subset
    have h := setIntegral_union hdj hSmeas ((hint i).mono_set hsubU) ((hint i).mono_set hsubS)
    rw [← hU] at h
    rw [h, integral_iUnion_fintype (fun k => (cell k).isOpen.measurableSet) hdisj
        (fun k => (hint i).mono_set (hle k))]
  -- identify the pieces
  have hcellform : ∀ k, (∑ i : Fin d, ∫ x in (cell k : Set (SpatialCoordinates d)),
      a.val x * (X i x * X i x)) =
      dirichletResponse (killedResponseSpace (hPc k)) (ac k) (bk k) := by
    intro k
    have hdr : dirichletResponse (killedResponseSpace (hPc k)) (ac k) (bk k) =
        sobolevCoefficientForm (ac k) (uk k : SobolevData (cell k))
          (uk k : SobolevData (cell k)) := by rw [huk]; rfl
    rw [hdr]
    rw [sobolevCoefficientForm_apply]
    refine Finset.sum_congr rfl (fun i _ => integral_congr_ae ?_)
    filter_upwards [hXcell i k, hac k] with x hx1 hx2
    rw [hx1, hx2]
  have hoff : ∀ i, (∫ x in S, a.val x * (X i x * X i x)) =
      ∫ x in S, a.val x * ((b : SobolevData Q).2 i x * (b : SobolevData Q).2 i x) := by
    intro i
    refine integral_congr_ae ?_
    filter_upwards [hXoff i] with x hx
    rw [hx]
  rw [sobolevCoefficientForm_apply]
  have hXe : ∀ i, ((b : SobolevData Q) + Wc).2 i = X i := by intro i; rw [hX]
  simp only [hXe, hsplit, Finset.sum_add_distrib, hoff, ← hS]
  rw [Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl (fun k _ => hcellform k)

section RouteWGeo
open Homogenization Homogenization.Book.Ch02

/-! ### Whitney family of grid cubes inside the working cube (route W) -/

/-- Arithmetic containment test: the triadic cube `T`, read relative to the centre of the
working cube, lies in the working cube of side `r`. -/
def aux_aux_macro_moment_bank_inside {d : ℕ} (r : ℝ) (T : TriadicCube d) : Prop :=
  ∀ i, (|(T.index i : ℝ)| + 1 / 2) * cubeScaleFactor T ≤ r / 2

/-- Maximality of the depth-`k` cube `T` of the unit root: no strict ancestor passes the
containment test. -/
def aux_aux_macro_moment_bank_maximal {d : ℕ} (r : ℝ) (k : ℕ) (T : TriadicCube d) : Prop :=
  ∀ m < k, ∀ A ∈ descendantsAtDepth (originCube d 0) m,
    T ∈ descendantsAtDepth A (k - m) → ¬ aux_aux_macro_moment_bank_inside r A

/-- The Whitney family of levels `0, …, M`: the maximal grid cubes inside the working cube,
indexed by their depth in the unit root. -/
def aux_aux_macro_moment_bank_whitney {d : ℕ} (r : ℝ) (M : ℕ) :
    Finset (Σ _ : ℕ, TriadicCube d) := by
  classical
  exact (Finset.range (M + 1)).sigma fun k =>
    (descendantsAtDepth (originCube d 0) k).filter fun T =>
      aux_aux_macro_moment_bank_inside r T ∧ aux_aux_macro_moment_bank_maximal r k T

theorem aux_aux_macro_moment_bank_mem_whitney {d : ℕ} (r : ℝ) (M : ℕ)
    (p : Σ _ : ℕ, TriadicCube d) :
    p ∈ aux_aux_macro_moment_bank_whitney r M ↔
      p.1 ≤ M ∧ p.2 ∈ descendantsAtDepth (originCube d 0) p.1 ∧
        aux_aux_macro_moment_bank_inside r p.2 ∧ aux_aux_macro_moment_bank_maximal r p.1 p.2 := by
  classical
  unfold aux_aux_macro_moment_bank_whitney
  simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, Nat.lt_add_one_iff]

/-- The physical grid cube of level `k` and index `n` about the centre `z`. -/
abbrev aux_aux_macro_moment_bank_cell {d : ℕ} (z : SpatialCoordinates d) (k : ℕ)
    (n : Fin d → ℤ) : Opens (SpatialCoordinates d) :=
  centeredCube (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (n i : ℝ)) ((3 : ℝ) ^ (-(k : ℤ)))
    (by positivity)

theorem aux_aux_macro_moment_bank_scaleFactor {d : ℕ} (k : ℕ) (T : TriadicCube d)
    (hT : T.scale = -(k : ℤ)) : cubeScaleFactor T = (3 : ℝ) ^ (-(k : ℤ)) := by
  simp [cubeScaleFactor, hT]

theorem aux_aux_macro_moment_bank_scale_of_mem {d : ℕ} (k : ℕ) (T : TriadicCube d)
    (hT : T ∈ descendantsAtDepth (originCube d 0) k) : T.scale = -(k : ℤ) := by
  rw [scale_eq_sub_of_mem_descendantsAtDepth hT]
  simp [originCube]

/-- **Dictionary**: the physical cell is the translate by `z` of the open triadic cube. -/
theorem aux_aux_macro_moment_bank_mem_cell_iff {d : ℕ} (z : SpatialCoordinates d) (k : ℕ)
    (T : TriadicCube d) (hT : T.scale = -(k : ℤ)) (x : SpatialCoordinates d) :
    x ∈ (aux_aux_macro_moment_bank_cell z k T.index : Set (SpatialCoordinates d)) ↔
      x - z ∈ openCubeSet T := by
  rw [centeredCube_eq_pi, Set.mem_univ_pi]
  have hs := aux_aux_macro_moment_bank_scaleFactor k T hT
  simp only [openCubeSet, Set.mem_setOf_eq, Set.mem_Ioo, Pi.sub_apply, hs]
  constructor
  · intro h i
    obtain ⟨h1, h2⟩ := h i
    constructor <;> linarith
  · intro h i
    obtain ⟨h1, h2⟩ := h i
    constructor <;> linarith

/-- A cube passing the containment test lies in the working cube. -/
theorem aux_aux_macro_moment_bank_cell_le {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (k : ℕ) (T : TriadicCube d) (hT : T.scale = -(k : ℤ))
    (hin : aux_aux_macro_moment_bank_inside r T) :
    aux_aux_macro_moment_bank_cell z k T.index ≤ centeredCube z r hr := by
  intro x hx
  have hs0 : 0 < cubeScaleFactor T := by
    rw [aux_aux_macro_moment_bank_scaleFactor k T hT]; positivity
  have hx' := (aux_aux_macro_moment_bank_mem_cell_iff z k T hT x).1 hx
  show x ∈ (centeredCube z r hr : Set (SpatialCoordinates d))
  rw [centeredCube_eq_pi, Set.mem_univ_pi]
  intro i
  obtain ⟨h1, h2⟩ := hx' i
  have hi := hin i
  have ha1 : (T.index i : ℝ) * cubeScaleFactor T ≤ |(T.index i : ℝ)| * cubeScaleFactor T :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hs0.le
  have ha2 : -(T.index i : ℝ) * cubeScaleFactor T ≤ |(T.index i : ℝ)| * cubeScaleFactor T :=
    mul_le_mul_of_nonneg_right (neg_le_abs _) hs0.le
  simp only [Pi.sub_apply] at h1 h2
  constructor <;> linarith

/-- `2 |n| + 1 ≤ 3^m` for the index of a depth-`m` cube of the unit root. -/
theorem aux_aux_macro_moment_bank_two_abs_index_le {d : ℕ} (m : ℕ) (T : TriadicCube d)
    (hT : T ∈ descendantsAtDepth (originCube d 0) m) (i : Fin d) :
    2 * |(T.index i : ℝ)| + 1 ≤ (3 : ℝ) ^ m := by
  have hr := Gagliardo.index_range_of_mem_descendantsAtDepth hT i
  have hh := Gagliardo.two_mul_halfRange m
  simp only [originCube, Pi.zero_apply, mul_zero, zero_sub, zero_add] at hr
  have habs : |T.index i| ≤ Gagliardo.halfRange m := abs_le.2 hr
  have hz : 2 * |T.index i| + 1 ≤ 3 ^ m := by linarith
  have hz' : ((2 * |T.index i| + 1 : ℤ) : ℝ) ≤ ((3 ^ m : ℤ) : ℝ) := by exact_mod_cast hz
  push_cast at hz'
  exact hz'

/-- Every cube of the unit root passes the containment test for the unit working cube. -/
theorem aux_aux_macro_moment_bank_inside_one {d : ℕ} (m : ℕ) (T : TriadicCube d)
    (hT : T ∈ descendantsAtDepth (originCube d 0) m) :
    aux_aux_macro_moment_bank_inside 1 T := by
  intro i
  have h2 := aux_aux_macro_moment_bank_two_abs_index_le m T hT i
  rw [aux_aux_macro_moment_bank_scaleFactor m T
    (aux_aux_macro_moment_bank_scale_of_mem m T hT), zpow_neg, zpow_natCast]
  have h3 : (0 : ℝ) < 3 ^ m := by positivity
  rw [← div_eq_mul_inv, div_le_iff₀ h3]
  linarith

/-- Conversely, a cube at scale `-k` passing the test for `r ≤ 1` is a depth-`k` cube of the
unit root. -/
theorem aux_aux_macro_moment_bank_mem_of_inside {d : ℕ} (r : ℝ) (hr1 : r ≤ 1) (k : ℕ)
    (T : TriadicCube d) (hT : T.scale = -(k : ℤ))
    (hin : aux_aux_macro_moment_bank_inside r T) :
    T ∈ descendantsAtDepth (originCube d 0) k := by
  refine Gagliardo.mem_descendantsAtDepth_of_index_range (by simp [originCube, hT]) ?_
  intro i
  have hi := hin i
  rw [aux_aux_macro_moment_bank_scaleFactor k T hT, zpow_neg, zpow_natCast] at hi
  have h3 : (0 : ℝ) < 3 ^ k := by positivity
  rw [← div_eq_mul_inv, div_le_iff₀ h3] at hi
  have hreal : 2 * |(T.index i : ℝ)| + 1 ≤ (3 : ℝ) ^ k := by
    have := mul_le_mul_of_nonneg_right hr1 h3.le
    linarith
  have hint : 2 * |T.index i| + 1 ≤ 3 ^ k := by
    have : ((2 * |T.index i| + 1 : ℤ) : ℝ) ≤ ((3 ^ k : ℤ) : ℝ) := by push_cast; exact hreal
    exact_mod_cast this
  have hh := Gagliardo.two_mul_halfRange k
  have habs : |T.index i| ≤ Gagliardo.halfRange k := by linarith
  simp only [originCube, Pi.zero_apply, mul_zero, zero_sub, zero_add]
  exact abs_le.1 habs

theorem aux_aux_macro_moment_bank_openCubeSet_subset_cubeSet {d : ℕ} (T : TriadicCube d) :
    openCubeSet T ⊆ cubeSet T := fun _ hy i => ⟨(hy i).1.le, (hy i).2⟩

/-- **(W1) Disjointness**, one-sided form. -/
theorem aux_aux_macro_moment_bank_whitney_disjoint_of_le {d : ℕ} (z : SpatialCoordinates d)
    (r : ℝ) (M : ℕ) (p q : Σ _ : ℕ, TriadicCube d)
    (hp : p ∈ aux_aux_macro_moment_bank_whitney r M)
    (hq : q ∈ aux_aux_macro_moment_bank_whitney r M) (hpq : p ≠ q) (hle : p.1 ≤ q.1) :
    Disjoint (aux_aux_macro_moment_bank_cell z p.1 p.2.index : Set (SpatialCoordinates d))
      (aux_aux_macro_moment_bank_cell z q.1 q.2.index : Set (SpatialCoordinates d)) := by
  obtain ⟨-, hpD, hpin, -⟩ := (aux_aux_macro_moment_bank_mem_whitney r M p).1 hp
  obtain ⟨-, hqD, -, hqmax⟩ := (aux_aux_macro_moment_bank_mem_whitney r M q).1 hq
  rw [Set.disjoint_left]
  intro x hxp hxq
  have hxp' := (aux_aux_macro_moment_bank_mem_cell_iff z p.1 p.2
    (aux_aux_macro_moment_bank_scale_of_mem p.1 p.2 hpD) x).1 hxp
  have hxq' := (aux_aux_macro_moment_bank_mem_cell_iff z q.1 q.2
    (aux_aux_macro_moment_bank_scale_of_mem q.1 q.2 hqD) x).1 hxq
  have hqD' : q.2 ∈ descendantsAtDepth (originCube d 0) (p.1 + (q.1 - p.1)) := by
    rwa [Nat.add_sub_cancel' hle]
  obtain ⟨A, hA, hqA⟩ := exists_descendant_ancestor_at_depth p.1 (q.1 - p.1) hqD'
  have hAeq : A = p.2 := by
    by_contra hne
    have hdis := pairwiseDisjoint_descendantsAtDepth (originCube d 0) p.1 hA hpD hne
    have hxA : x - z ∈ openCubeSet A := openCubeSet_subset_of_mem_descendantsAtDepth hqA hxq'
    exact Set.disjoint_left.1 hdis
      (aux_aux_macro_moment_bank_openCubeSet_subset_cubeSet A hxA)
      (aux_aux_macro_moment_bank_openCubeSet_subset_cubeSet p.2 hxp')
  subst hAeq
  rcases Nat.lt_or_ge p.1 q.1 with hlt | hge
  · exact hqmax p.1 hlt p.2 hA hqA hpin
  · have heq : p.1 = q.1 := le_antisymm hle hge
    have h0 : q.1 - p.1 = 0 := by omega
    rw [h0, descendantsAtDepth_zero, Finset.mem_singleton] at hqA
    apply hpq
    obtain ⟨p1, p2⟩ := p
    obtain ⟨q1, q2⟩ := q
    simp only at heq hqA
    subst heq
    subst hqA
    rfl

/-- **(W1) Disjointness** of distinct Whitney cells. -/
theorem aux_aux_macro_moment_bank_whitney_disjoint {d : ℕ} (z : SpatialCoordinates d)
    (r : ℝ) (M : ℕ) (p q : Σ _ : ℕ, TriadicCube d)
    (hp : p ∈ aux_aux_macro_moment_bank_whitney r M)
    (hq : q ∈ aux_aux_macro_moment_bank_whitney r M) (hpq : p ≠ q) :
    Disjoint (aux_aux_macro_moment_bank_cell z p.1 p.2.index : Set (SpatialCoordinates d))
      (aux_aux_macro_moment_bank_cell z q.1 q.2.index : Set (SpatialCoordinates d)) := by
  rcases le_total p.1 q.1 with h | h
  · exact aux_aux_macro_moment_bank_whitney_disjoint_of_le z r M p q hp hq hpq h
  · exact (aux_aux_macro_moment_bank_whitney_disjoint_of_le z r M q p hq hp
      (Ne.symm hpq) h).symm

/-- **(W2) boundary coordinate.**  A Whitney cube of depth `k + 1` has a coordinate whose
index takes one of four values fixed by `r` and `k`: its parent fails the containment test. -/
theorem aux_aux_macro_moment_bank_boundary_coord {d : ℕ} (r : ℝ) (k : ℕ) (T : TriadicCube d)
    (hT : T ∈ descendantsAtDepth (originCube d 0) (k + 1))
    (hin : aux_aux_macro_moment_bank_inside r T)
    (hmax : aux_aux_macro_moment_bank_maximal r (k + 1) T) :
    ∃ i, T.index i ∈ ({⌊r / 2 * (3 : ℝ) ^ (k + 1) - 1 / 2⌋ - 1, ⌊r / 2 * (3 : ℝ) ^ (k + 1) - 1 / 2⌋,
      1 - ⌊r / 2 * (3 : ℝ) ^ (k + 1) - 1 / 2⌋, -⌊r / 2 * (3 : ℝ) ^ (k + 1) - 1 / 2⌋} : Finset ℤ) := by
  obtain ⟨A, hA, hTA⟩ := exists_descendant_ancestor_at_depth k 1 hT
  have hnot := hmax k (Nat.lt_succ_self k) A hA (by rwa [Nat.add_sub_cancel_left])
  unfold aux_aux_macro_moment_bank_inside at hnot
  push_neg at hnot
  obtain ⟨i, hi⟩ := hnot
  refine ⟨i, ?_⟩
  have hTi := hin i
  rw [aux_aux_macro_moment_bank_scaleFactor k A (aux_aux_macro_moment_bank_scale_of_mem k A hA),
    zpow_neg, zpow_natCast] at hi
  rw [aux_aux_macro_moment_bank_scaleFactor (k + 1) T
    (aux_aux_macro_moment_bank_scale_of_mem (k + 1) T hT), zpow_neg, zpow_natCast] at hTi
  have h3k : (0 : ℝ) < 3 ^ k := by positivity
  have h3k1 : (0 : ℝ) < 3 ^ (k + 1) := by positivity
  rw [← div_eq_mul_inv, div_le_iff₀ h3k1] at hTi
  rw [← div_eq_mul_inv, lt_div_iff₀ h3k] at hi
  -- the parent relation `|n - 3 p| ≤ 1`
  have hrange := Gagliardo.index_range_of_mem_descendantsAtDepth hTA i
  have hh1 : Gagliardo.halfRange 1 = 1 := rfl
  rw [hh1, pow_one] at hrange
  have hpar : 3 * |A.index i| ≤ |T.index i| + 1 := by
    rcases abs_cases (A.index i) with ⟨ha, _⟩ | ⟨ha, _⟩ <;>
      rcases abs_cases (T.index i) with ⟨hb, _⟩ | ⟨hb, _⟩ <;> omega
  have hparR : 3 * |(A.index i : ℝ)| ≤ |(T.index i : ℝ)| + 1 := by
    have : ((3 * |A.index i| : ℤ) : ℝ) ≤ ((|T.index i| + 1 : ℤ) : ℝ) := by exact_mod_cast hpar
    push_cast at this
    exact this
  have hpow : (3 : ℝ) ^ (k + 1) = 3 * 3 ^ k := by ring
  set R : ℝ := r / 2 * (3 : ℝ) ^ (k + 1) with hR
  have hup : |(T.index i : ℝ)| ≤ R - 1 / 2 := by rw [hR]; linarith
  have hlow : R - 5 / 2 < |(T.index i : ℝ)| := by
    have : R = 3 * (r / 2 * 3 ^ k) := by rw [hR, hpow]; ring
    linarith
  set a : ℤ := ⌊R - 1 / 2⌋ with ha
  have h1 : |T.index i| ≤ a := by
    rw [ha, Int.le_floor]
    push_cast
    exact hup
  have h2 : a - 1 ≤ |T.index i| := by
    have hfl : (a : ℝ) ≤ R - 1 / 2 := Int.floor_le _
    have : (a : ℝ) < ((|T.index i| + 2 : ℤ) : ℝ) := by push_cast; linarith
    have : a < |T.index i| + 2 := by exact_mod_cast this
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases abs_cases (T.index i) with ⟨hb, _⟩ | ⟨hb, _⟩ <;> omega

theorem aux_aux_macro_moment_bank_card_piFinset_le {d : ℕ} (i : Fin d) (B : Finset ℤ)
    (hB : B.card ≤ 4) (h : ℤ) (k : ℕ) (hh : 2 * h = 3 ^ k - 1) :
    (Fintype.piFinset (fun j : Fin d => if j = i then B else Finset.Icc (-h) h)).card ≤
      4 * (3 ^ k) ^ (d - 1) := by
  classical
  rw [Fintype.card_piFinset, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  have hIcc : (Finset.Icc (-h) h).card = 3 ^ k := by
    rw [Int.card_Icc]
    have : h + 1 - -h = ((3 ^ k : ℕ) : ℤ) := by push_cast; linear_combination hh
    rw [this, Int.toNat_natCast]
  have hrest : ∏ j ∈ Finset.univ.erase i,
      (if j = i then B else Finset.Icc (-h) h).card = (3 ^ k) ^ (d - 1) := by
    rw [Finset.prod_congr rfl (fun j hj => by rw [if_neg (Finset.ne_of_mem_erase hj), hIcc]),
      Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
  rw [hrest, if_pos rfl]
  exact Nat.mul_le_mul_right _ hB

/-- **(W2) level count**: at most `4 d 3^{k(d-1)}` Whitney cubes of depth `k`. -/
theorem aux_aux_macro_moment_bank_whitney_card_level {d : ℕ} (hd : 1 ≤ d) (r : ℝ)
    (M k : ℕ) :
    ((aux_aux_macro_moment_bank_whitney (d := d) r M).filter (fun p => p.1 = k)).card ≤
      4 * d * (3 ^ k) ^ (d - 1) := by
  classical
  have hinj : Set.InjOn (fun p : Σ _ : ℕ, TriadicCube d => p.2.index)
      ((aux_aux_macro_moment_bank_whitney (d := d) r M).filter (fun p => p.1 = k) :
        Set (Σ _ : ℕ, TriadicCube d)) := by
    intro p hp q hq hpq
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp hq
    obtain ⟨hpW, hp1⟩ := hp
    obtain ⟨hqW, hq1⟩ := hq
    have hpD := ((aux_aux_macro_moment_bank_mem_whitney r M p).1 hpW).2.1
    have hqD := ((aux_aux_macro_moment_bank_mem_whitney r M q).1 hqW).2.1
    have hps := aux_aux_macro_moment_bank_scale_of_mem _ _ hpD
    have hqs := aux_aux_macro_moment_bank_scale_of_mem _ _ hqD
    obtain ⟨p1, ⟨ps, pi⟩⟩ := p
    obtain ⟨q1, ⟨qs, qi⟩⟩ := q
    simp only at hp1 hq1 hps hqs hpq
    subst hp1 hq1 hps hqs hpq
    rfl
  rcases k with _ | k
  · -- depth `0`: only the root
    refine (Finset.card_le_card_of_injOn (fun p => p.2.index) (t := {0}) ?_ hinj).trans ?_
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp
      obtain ⟨hpW, hp1⟩ := hp
      have hpD := ((aux_aux_macro_moment_bank_mem_whitney r M p).1 hpW).2.1
      rw [hp1, descendantsAtDepth_zero, Finset.mem_singleton] at hpD
      simp [hpD, originCube]
    · simp only [Finset.card_singleton, pow_zero, one_pow, mul_one]
      omega
  · set a : ℤ := ⌊r / 2 * (3 : ℝ) ^ (k + 1) - 1 / 2⌋ with ha
    set B : Finset ℤ := {a - 1, a, 1 - a, -a} with hB
    set h : ℤ := Gagliardo.halfRange (k + 1) with hh
    refine (Finset.card_le_card_of_injOn (fun p => p.2.index)
      (t := Finset.univ.biUnion fun i : Fin d =>
        Fintype.piFinset (fun j : Fin d => if j = i then B else Finset.Icc (-h) h)) ?_ hinj).trans ?_
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp
      obtain ⟨hpW, hp1⟩ := hp
      obtain ⟨-, hpD, hpin, hpmax⟩ := (aux_aux_macro_moment_bank_mem_whitney r M p).1 hpW
      rw [hp1] at hpD hpmax
      obtain ⟨i, hi⟩ := aux_aux_macro_moment_bank_boundary_coord r k p.2 hpD hpin hpmax
      simp only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true,
        Set.mem_iUnion, Finset.mem_coe, Fintype.mem_piFinset]
      refine ⟨i, fun j => ?_⟩
      by_cases hj : j = i
      · subst hj
        rw [if_pos rfl]
        exact hi
      · rw [if_neg hj, Finset.mem_Icc]
        have hr := Gagliardo.index_range_of_mem_descendantsAtDepth hpD j
        simp only [originCube, Pi.zero_apply, mul_zero, zero_sub, zero_add] at hr
        exact hr
    · refine Finset.card_biUnion_le.trans ?_
      have hB4 : B.card ≤ 4 := Finset.card_le_four
      have hh2 : 2 * h = 3 ^ (k + 1) - 1 := Gagliardo.two_mul_halfRange (k + 1)
      calc ∑ i : Fin d, (Fintype.piFinset
            (fun j : Fin d => if j = i then B else Finset.Icc (-h) h)).card
          ≤ ∑ _i : Fin d, 4 * (3 ^ (k + 1)) ^ (d - 1) :=
            Finset.sum_le_sum fun i _ =>
              aux_aux_macro_moment_bank_card_piFinset_le i B hB4 h (k + 1) hh2
        _ = 4 * d * (3 ^ (k + 1)) ^ (d - 1) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
            ring

/-- **Summation over the Whitney family**, uniformly in its depth `M`. -/
theorem aux_aux_macro_moment_bank_whitney_sum {d : ℕ} (hd : 1 ≤ d) (r : ℝ) (M : ℕ)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∑ p ∈ aux_aux_macro_moment_bank_whitney (d := d) r M,
        ((((3 : ℝ) ^ p.1) ^ (d - 1))⁻¹ * ρ ^ p.1) ≤ 4 * d * (1 - ρ)⁻¹ := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := aux_aux_macro_moment_bank_whitney (d := d) r M)
    (t := Finset.range (M + 1)) (g := fun p => p.1)
    (fun p hp => Finset.mem_range.2
      (Nat.lt_succ_of_le ((aux_aux_macro_moment_bank_mem_whitney r M p).1 hp).1))]
  have hfib : ∀ k ∈ Finset.range (M + 1),
      ∑ p ∈ (aux_aux_macro_moment_bank_whitney (d := d) r M).filter (fun p => p.1 = k),
        ((((3 : ℝ) ^ p.1) ^ (d - 1))⁻¹ * ρ ^ p.1) ≤ 4 * d * ρ ^ k := by
    intro k _
    rw [Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.1 hp).2]),
      Finset.sum_const, nsmul_eq_mul]
    have hc := aux_aux_macro_moment_bank_whitney_card_level hd r M k
    have hc' : (((aux_aux_macro_moment_bank_whitney (d := d) r M).filter
        (fun p => p.1 = k)).card : ℝ) ≤ 4 * d * ((3 : ℝ) ^ k) ^ (d - 1) := by
      exact_mod_cast hc
    have hpos : (0 : ℝ) < ((3 : ℝ) ^ k) ^ (d - 1) := by positivity
    calc (((aux_aux_macro_moment_bank_whitney (d := d) r M).filter
          (fun p => p.1 = k)).card : ℝ) * ((((3 : ℝ) ^ k) ^ (d - 1))⁻¹ * ρ ^ k)
        ≤ (4 * d * ((3 : ℝ) ^ k) ^ (d - 1)) * ((((3 : ℝ) ^ k) ^ (d - 1))⁻¹ * ρ ^ k) :=
          mul_le_mul_of_nonneg_right hc' (by positivity)
      _ = 4 * d * ρ ^ k := by field_simp
  refine (Finset.sum_le_sum hfib).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← tsum_geometric_of_lt_one hρ0 hρ1]
  exact (summable_geometric_of_lt_one hρ0 hρ1).sum_le_tsum _ (fun i _ => pow_nonneg hρ0 i)

/-- **(W3) coverage**: a point of the working cube off every grid face lies in a Whitney cell
of some depth. -/
theorem aux_aux_macro_moment_bank_whitney_cover {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (hr1 : r ≤ 1) (x : SpatialCoordinates d)
    (hx : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hface : ∀ (i : Fin d) (k : ℕ) (q : ℤ),
      x i ≠ z i + ((q : ℝ) + 1 / 2) * (3 : ℝ) ^ (-(k : ℤ))) :
    ∃ Mw : ℕ, ∃ p ∈ aux_aux_macro_moment_bank_whitney (d := d) r Mw,
      x ∈ (aux_aux_macro_moment_bank_cell z p.1 p.2.index : Set (SpatialCoordinates d)) := by
  classical
  have hdist : dist x z < r / 2 := hx
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = r / 2 - dist x z := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ0 (by norm_num : (1 / 3 : ℝ) < 1)
  have h3k : (0 : ℝ) < 3 ^ k := by positivity
  have hsk : (3 : ℝ) ^ (-(k : ℤ)) = ((3 : ℝ) ^ k)⁻¹ := by rw [zpow_neg, zpow_natCast]
  have hk' : ((3 : ℝ) ^ k)⁻¹ < δ := by rwa [one_div, inv_pow] at hk
  obtain ⟨n, hn⟩ : ∃ n : Fin d → ℤ, n = fun i => ⌊(3 : ℝ) ^ k * (x i - z i) + 1 / 2⌋ :=
    ⟨_, rfl⟩
  obtain ⟨T0, hT0⟩ : ∃ T0 : TriadicCube d, T0 = ⟨-(k : ℤ), n⟩ := ⟨_, rfl⟩
  have hT0s : T0.scale = -(k : ℤ) := by rw [hT0]
  have hT0i : T0.index = n := by rw [hT0]
  -- the rounding error is strictly below `1/2`
  have hloc : ∀ i, (n i : ℝ) - 1 / 2 < (3 : ℝ) ^ k * (x i - z i) ∧
      (3 : ℝ) ^ k * (x i - z i) < (n i : ℝ) + 1 / 2 := by
    intro i
    have hfl : (n i : ℝ) ≤ (3 : ℝ) ^ k * (x i - z i) + 1 / 2 := by
      rw [hn]; exact Int.floor_le _
    have hlt : (3 : ℝ) ^ k * (x i - z i) + 1 / 2 < (n i : ℝ) + 1 := by
      rw [hn]; exact Int.lt_floor_add_one _
    have hne : (n i : ℝ) ≠ (3 : ℝ) ^ k * (x i - z i) + 1 / 2 := by
      intro h
      apply hface i k (n i - 1)
      rw [hsk]
      push_cast
      field_simp
      linarith
    exact ⟨by rcases lt_or_eq_of_le hfl with h | h
              · linarith
              · exact absurd h hne, by linarith⟩
  have hxT0 : x - z ∈ openCubeSet T0 := by
    intro i
    rw [aux_aux_macro_moment_bank_scaleFactor k T0 hT0s, hsk, hT0i]
    obtain ⟨h1, h2⟩ := hloc i
    simp only [Pi.sub_apply]
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_lt_iff₀ h3k, lt_div_iff₀ h3k]
    constructor <;> linarith
  have hin0 : aux_aux_macro_moment_bank_inside r T0 := by
    intro i
    rw [aux_aux_macro_moment_bank_scaleFactor k T0 hT0s, hsk, hT0i]
    obtain ⟨h1, h2⟩ := hloc i
    have hyi : |x i - z i| ≤ dist x z := by
      rw [dist_eq_norm]
      have := norm_le_pi_norm (x - z) i
      simpa [Real.norm_eq_abs] using this
    have habs : |(n i : ℝ)| ≤ (3 : ℝ) ^ k * |x i - z i| + 1 / 2 := by
      have ht : |(3 : ℝ) ^ k * (x i - z i)| = (3 : ℝ) ^ k * |x i - z i| := by
        rw [abs_mul, abs_of_pos h3k]
      have hd : |(n i : ℝ) - (3 : ℝ) ^ k * (x i - z i)| ≤ 1 / 2 :=
        abs_le.2 ⟨by linarith, by linarith⟩
      have := abs_sub_abs_le_abs_sub (n i : ℝ) ((3 : ℝ) ^ k * (x i - z i))
      linarith
    have hmul : (|(n i : ℝ)| + 1 / 2) * ((3 : ℝ) ^ k)⁻¹ ≤ |x i - z i| + ((3 : ℝ) ^ k)⁻¹ := by
      rw [← div_eq_mul_inv, div_le_iff₀ h3k, add_mul, inv_mul_cancel₀ h3k.ne']
      linarith
    linarith
  have hT0D := aux_aux_macro_moment_bank_mem_of_inside r hr1 k T0 hT0s hin0
  -- the largest ancestor of `T0` inside the working cube
  have hex : ∃ m, m ≤ k ∧ ∃ A ∈ descendantsAtDepth (originCube d 0) m,
      T0 ∈ descendantsAtDepth A (k - m) ∧ aux_aux_macro_moment_bank_inside r A :=
    ⟨k, le_rfl, T0, hT0D, by simp, hin0⟩
  obtain ⟨m0, hm0⟩ : ∃ m0, m0 = Nat.find hex := ⟨_, rfl⟩
  have hspec := Nat.find_spec hex
  rw [← hm0] at hspec
  obtain ⟨hm0k, A0, hA0, hT0A0, hinA0⟩ := hspec
  have hmin : ∀ m < m0, ¬ (m ≤ k ∧ ∃ A ∈ descendantsAtDepth (originCube d 0) m,
      T0 ∈ descendantsAtDepth A (k - m) ∧ aux_aux_macro_moment_bank_inside r A) := by
    intro m hm
    rw [hm0] at hm
    exact Nat.find_min hex hm
  refine ⟨m0, ⟨m0, A0⟩, ?_, ?_⟩
  · rw [aux_aux_macro_moment_bank_mem_whitney]
    refine ⟨le_rfl, hA0, hinA0, ?_⟩
    intro m hm A hA hA0A hinA
    simp only at hm
    have htrans : T0 ∈ descendantsAtDepth A (k - m) := by
      have := mem_descendantsAtDepth_add_local hA0A hT0A0
      rwa [show m0 - m + (k - m0) = k - m by omega] at this
    exact hmin m hm ⟨by omega, A, hA, htrans, hinA⟩
  · show x ∈ (aux_aux_macro_moment_bank_cell z m0 A0.index : Set (SpatialCoordinates d))
    rw [aux_aux_macro_moment_bank_mem_cell_iff z m0 A0
      (aux_aux_macro_moment_bank_scale_of_mem _ A0 hA0)]
    exact openCubeSet_subset_of_mem_descendantsAtDepth hT0A0 hxT0

/-- The grid faces form a Lebesgue-null set. -/
theorem aux_aux_macro_moment_bank_faces_null {d : ℕ} (z : SpatialCoordinates d) :
    volume {x : SpatialCoordinates d | ∃ (i : Fin d) (k : ℕ) (q : ℤ),
      x i = z i + ((q : ℝ) + 1 / 2) * (3 : ℝ) ^ (-(k : ℤ))} = 0 := by
  have hset : {x : SpatialCoordinates d | ∃ (i : Fin d) (k : ℕ) (q : ℤ),
      x i = z i + ((q : ℝ) + 1 / 2) * (3 : ℝ) ^ (-(k : ℤ))} =
      ⋃ i : Fin d, ⋃ k : ℕ, ⋃ q : ℤ, {x : SpatialCoordinates d |
        x i = z i + ((q : ℝ) + 1 / 2) * (3 : ℝ) ^ (-(k : ℤ))} := by
    ext x
    simp
  rw [hset]
  refine measure_iUnion_null fun i => measure_iUnion_null fun k => measure_iUnion_null fun q => ?_
  rw [volume_pi]
  exact Measure.pi_hyperplane _ i _

/-- **The coefficient identity** (normaliser `1`): on a sub-cube, the cutoff coefficients of
the sub-cube and of any containing cube agree almost everywhere. -/
theorem aux_aux_macro_moment_bank_cutoff_ae_eq {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (w : SpatialCoordinates d) (ρ : ℝ) (hρ : 0 < ρ) (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r)
    (hsub : (centeredCube w ρ hρ : Set (SpatialCoordinates d)) ⊆ centeredCube z r hr) :
    ∀ᵐ x ∂volume.restrict (centeredCube w ρ hρ : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M H om N w hρ).val x =
        (cutoffPositiveCoefficient M H om N z hr).val x := by
  have h1 := @normalizedContinuousPositiveCoefficient_coeFn d (centeredCube w ρ hρ)
    (closedCube w ρ hρ) ⟨centeredCube_subset_closedCube w hρ⟩
    (cutoffCoefficientCM M H om N w hρ) (cutoffCoefficientCM_pos M H om N w hρ) 1 one_pos
  have h2 := @normalizedContinuousPositiveCoefficient_coeFn d (centeredCube z r hr)
    (closedCube z r hr) ⟨centeredCube_subset_closedCube z hr⟩
    (cutoffCoefficientCM M H om N z hr) (cutoffCoefficientCM_pos M H om N z hr) 1 one_pos
  have h2' := ae_restrict_of_ae_restrict_of_subset hsub h2
  filter_upwards [h1, h2', ae_restrict_mem (centeredCube w ρ hρ).isOpen.measurableSet]
    with x hx1 hx2 hxm
  unfold cutoffPositiveCoefficient
  rw [hx1 hxm, hx2 (hsub hxm)]
  rfl

/-- The closed cube of an inner open cube lies in the closed cube of the outer one. -/
theorem aux_aux_macro_moment_bank_closedCube_subset {d : ℕ} (w : SpatialCoordinates d)
    (ρ : ℝ) (hρ : 0 < ρ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hsub : (centeredCube w ρ hρ : Set (SpatialCoordinates d)) ⊆ centeredCube z r hr) :
    (closedCube w ρ hρ : Set (SpatialCoordinates d)) ⊆ closedCube z r hr := by
  have e1 : (closedCube w ρ hρ : Set (SpatialCoordinates d)) =
      closure (centeredCube w ρ hρ : Set (SpatialCoordinates d)) := by
    change Metric.closedBall w (ρ / 2) = closure (Metric.ball w (ρ / 2))
    rw [closure_ball w (by positivity : ρ / 2 ≠ 0)]
  rw [e1]
  exact closure_minimal (hsub.trans (centeredCube_subset_closedCube z hr))
    (closedCube z r hr).isCompact.isClosed

/-- **(M1)** The `C²` norm is monotone along nonempty subsets of a compact set. -/
theorem aux_aux_macro_moment_bank_c2Norm_mono {d : ℕ} (S S' : Set (SpatialCoordinates d))
    (hS : IsCompact S) (hS' : S'.Nonempty) (hsub : S' ⊆ S)
    (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ 2 phi) :
    c2Norm S' phi ≤ c2Norm S phi := by
  have key : ∀ g : SpatialCoordinates d → ℝ, Continuous g →
      sSup {v : ℝ | ∃ x ∈ S', v = g x} ≤ sSup {v : ℝ | ∃ x ∈ S, v = g x} := by
    intro g hg
    refine csSup_le_csSup ?_ ?_ ?_
    · exact (hS.bddAbove_image hg.continuousOn).mono (by
        rintro v ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩)
    · obtain ⟨x, hx⟩ := hS'
      exact ⟨g x, x, hx, rfl⟩
    · rintro v ⟨x, hx, rfl⟩
      exact ⟨x, hsub hx, rfl⟩
  have h1 := key (fun x => |phi x|) hphi.continuous.abs
  have h2 := key (fun x => ‖fderiv ℝ phi x‖) (hphi.continuous_fderiv (by norm_num)).norm
  have h3 := key (fun x => ‖fderiv ℝ (fderiv ℝ phi) x‖)
    ((hphi.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).norm
  unfold c2Norm
  exact add_le_add (add_le_add h1 h2) h3

/-! ### Per-cell bound and working-cube boundary response (route W) -/

/-- The ancestor-discount constant `c_s / c_{s'} · (1 - 3^{-2(s-s')})⁻¹` at the orders
`s = (3/4 - 1/2)/4` of `eq:mfd-2` and `s' = (5/8 - 1/2)/4` of `eq:mfd-3`. -/
def aux_aux_macro_moment_bank_Cs : ℝ :=
  Book.Ch02.geometricDiscount ((3 / 4 - 1 / 2) / 4) 2 /
      Book.Ch02.geometricDiscount ((5 / 8 - 1 / 2) / 4) 2 *
    (1 - Real.rpow (3 : ℝ) (-2 * ((3 / 4 - 1 / 2) / 4 - (5 / 8 - 1 / 2) / 4)))⁻¹

theorem aux_aux_macro_moment_bank_Cs_nonneg : 0 ≤ aux_aux_macro_moment_bank_Cs := by
  unfold aux_aux_macro_moment_bank_Cs
  have h1 := w19_geometricDiscount_pos ((3 / 4 - 1 / 2) / 4) 2 (by norm_num) two_pos
  have h2 := w19_geometricDiscount_pos ((5 / 8 - 1 / 2) / 4) 2 (by norm_num) two_pos
  have h3 : Real.rpow (3 : ℝ) (-2 * ((3 / 4 - 1 / 2) / 4 - (5 / 8 - 1 / 2) / 4)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have h4 : 0 < 1 - Real.rpow (3 : ℝ) (-2 * ((3 / 4 - 1 / 2) / 4 - (5 / 8 - 1 / 2) / 4)) := by
    linarith
  positivity

/-- **(M4) Ancestor discount at a Whitney cell.**  A depth-`k` cube of the unit root is
compared, in its own chart, with its depth-`min k N` ancestor on the `eq:mfd-3` root
`(z, 1)`; the grid bound there gives `Λ_s(V) ≤ C_{ss'} K 3^{3k/16}`. -/
theorem aux_aux_macro_moment_bank_cell_Lam_le {d : ℕ} (E : in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (K : ℝ)
    (hK : ∀ (k : ℕ) (nidx : Fin d → ℤ), k ≤ N →
      aux_aux_macro_moment_bank_cell z k nidx ≤ centeredCube z 1 one_pos →
      E.Lam z 1 one_pos (cutoffPositiveCoefficient M H om N z one_pos)
          (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ)) ((3 : ℝ) ^ (-(k : ℤ)))
          ((5 / 8 - 1 / 2) / 4) 2 +
        (E.lam z 1 one_pos (cutoffPositiveCoefficient M H om N z one_pos)
          (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ)) ((3 : ℝ) ^ (-(k : ℤ)))
          ((5 / 8 - 1 / 2) / 4) 2)⁻¹ ≤
        K * ((3 : ℝ) ^ (-(k : ℤ))) ^ (-(1 / 8 : ℝ)))
    (k : ℕ) (T : TriadicCube d) (hT : T ∈ descendantsAtDepth (originCube d 0) k) :
    0 < K ∧
      E.Lam (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (T.index i : ℝ)) ((3 : ℝ) ^ (-(k : ℤ)))
          (by positivity)
          (cutoffPositiveCoefficient M H om N
            (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (T.index i : ℝ))
            (by positivity : (0 : ℝ) < (3 : ℝ) ^ (-(k : ℤ))))
          (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (T.index i : ℝ)) ((3 : ℝ) ^ (-(k : ℤ)))
          ((3 / 4 - 1 / 2) / 4) 2 ≤
        aux_aux_macro_moment_bank_Cs * K * (3 : ℝ) ^ ((3 / 16 : ℝ) * k) := by
  obtain ⟨kP, hkP⟩ : ∃ kP, kP = min k N := ⟨_, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j, j = k - kP := ⟨_, rfl⟩
  have hkPk : kP ≤ k := hkP ▸ min_le_left _ _
  have hkPN : kP ≤ N := hkP ▸ min_le_right _ _
  have hk : k = kP + j := by omega
  have hT' : T ∈ descendantsAtDepth (originCube d 0) (kP + j) := hk ▸ hT
  obtain ⟨P, hPD, hTP⟩ := exists_descendant_ancestor_at_depth kP j hT'
  obtain ⟨c, hc⟩ : ∃ c : Fin d → ℤ, c = fun i => T.index i - 3 ^ j * P.index i := ⟨_, rfl⟩
  have hV1 := aux_aux_macro_moment_bank_cell_le z 1 one_pos k T
    (aux_aux_macro_moment_bank_scale_of_mem k T hT) (aux_aux_macro_moment_bank_inside_one k T hT)
  have hP1 := aux_aux_macro_moment_bank_cell_le z 1 one_pos kP P
    (aux_aux_macro_moment_bank_scale_of_mem kP P hPD)
    (aux_aux_macro_moment_bank_inside_one kP P hPD)
  have hρ : (3 : ℝ) ^ (-(kP : ℤ)) = (3 : ℝ) ^ j * (3 : ℝ) ^ (-(k : ℤ)) := by
    rw [hk, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, pow_add]
    field_simp
  have hw : ∀ i, (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (T.index i : ℝ)) i =
      (fun i => z i + (3 : ℝ) ^ (-(kP : ℤ)) * (P.index i : ℝ)) i +
        (3 : ℝ) ^ (-(k : ℤ)) * (c i : ℝ) := by
    intro i
    simp only [hc]
    push_cast
    rw [hρ]
    ring
  have hVdesc : dilateCube (-(j : ℤ)) (translateCube c (originCube d 0)) ∈
      descendantsAtScale (originCube d 0) ((originCube d 0).scale - (j : ℤ)) := by
    rw [descendantsAtScale_eq_descendantsAtDepth _ (by simp [originCube])]
    have hj0 : Int.toNat ((originCube d 0).scale - ((originCube d 0).scale - (j : ℤ))) = j := by
      simp
    rw [hj0]
    refine Gagliardo.mem_descendantsAtDepth_of_index_range
      (by simp [originCube, translateCube, dilateCube]) ?_
    intro i
    have hr := Gagliardo.index_range_of_mem_descendantsAtDepth hTP i
    simp only [dilateCube_index, translateCube, originCube, Pi.zero_apply, mul_zero, zero_add,
      zero_sub, hc]
    constructor <;> linarith [hr.1, hr.2]
  have ha := aux_aux_macro_moment_bank_cutoff_ae_eq M H om N
    (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (T.index i : ℝ)) ((3 : ℝ) ^ (-(k : ℤ)))
    (by positivity) z 1 one_pos (fun x hx => hV1 hx)
  have hLam := aux_aux_macro_moment_bank_Lam_ancestor E
    (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (T.index i : ℝ)) ((3 : ℝ) ^ (-(k : ℤ)))
    (by positivity)
    (cutoffPositiveCoefficient M H om N
      (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (T.index i : ℝ))
      (by positivity : (0 : ℝ) < (3 : ℝ) ^ (-(k : ℤ))))
    z 1 one_pos (cutoffPositiveCoefficient M H om N z one_pos)
    (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (T.index i : ℝ)) ((3 : ℝ) ^ (-(k : ℤ)))
    (by positivity)
    (fun i => z i + (3 : ℝ) ^ (-(kP : ℤ)) * (P.index i : ℝ)) ((3 : ℝ) ^ (-(kP : ℤ)))
    (by positivity) subset_rfl (fun x hx => hP1 hx) j c hρ hw hVdesc ha
    ((3 / 4 - 1 / 2) / 4) ((5 / 8 - 1 / 2) / 4) (by norm_num) (by norm_num) (by norm_num)
  have hKP := hK kP P.index hkPN hP1
  have hLam'pos := E.Lam_pos z 1 one_pos (cutoffPositiveCoefficient M H om N z one_pos)
    (fun i => z i + (3 : ℝ) ^ (-(kP : ℤ)) * (P.index i : ℝ)) ((3 : ℝ) ^ (-(kP : ℤ)))
    ((5 / 8 - 1 / 2) / 4) 2
  have hlampos := inv_pos.2 (E.lam_pos z 1 one_pos (cutoffPositiveCoefficient M H om N z one_pos)
    (fun i => z i + (3 : ℝ) ^ (-(kP : ℤ)) * (P.index i : ℝ)) ((3 : ℝ) ^ (-(kP : ℤ)))
    ((5 / 8 - 1 / 2) / 4) 2)
  have hT2pos : 0 < ((3 : ℝ) ^ (-(kP : ℤ))) ^ (-(1 / 8 : ℝ)) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hKpos : 0 < K := by
    by_contra hneg
    push_neg at hneg
    have := mul_nonpos_of_nonpos_of_nonneg hneg hT2pos.le
    linarith
  refine ⟨hKpos, ?_⟩
  have hexp : Real.rpow (3 : ℝ) (2 * ((5 / 8 - 1 / 2) / 4) * (j : ℝ)) *
      ((3 : ℝ) ^ (-(kP : ℤ))) ^ (-(1 / 8 : ℝ)) ≤ (3 : ℝ) ^ ((3 / 16 : ℝ) * k) := by
    have e2 : ((3 : ℝ) ^ (-(kP : ℤ))) ^ (-(1 / 8 : ℝ)) = (3 : ℝ) ^ ((kP : ℝ) / 8) := by
      rw [← Real.rpow_intCast, ← Real.rpow_mul (by norm_num)]
      congr 1
      push_cast
      ring
    rw [e2]
    change (3 : ℝ) ^ (2 * ((5 / 8 - 1 / 2) / 4) * (j : ℝ)) * (3 : ℝ) ^ ((kP : ℝ) / 8) ≤ _
    rw [← Real.rpow_add (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    rw [hk]
    push_cast
    have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
    have := (Nat.cast_nonneg kP : (0 : ℝ) ≤ kP)
    linarith
  have hT1 : 0 ≤ Real.rpow (3 : ℝ) (2 * ((5 / 8 - 1 / 2) / 4) * (j : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hCs := aux_aux_macro_moment_bank_Cs_nonneg
  unfold aux_aux_macro_moment_bank_Cs at hCs ⊢
  calc _ ≤ _ := hLam
    _ ≤ Book.Ch02.geometricDiscount ((3 / 4 - 1 / 2) / 4) 2 /
          Book.Ch02.geometricDiscount ((5 / 8 - 1 / 2) / 4) 2 *
        (1 - Real.rpow (3 : ℝ) (-2 * ((3 / 4 - 1 / 2) / 4 - (5 / 8 - 1 / 2) / 4)))⁻¹ *
        Real.rpow (3 : ℝ) (2 * ((5 / 8 - 1 / 2) / 4) * (j : ℝ)) *
          (K * ((3 : ℝ) ^ (-(kP : ℤ))) ^ (-(1 / 8 : ℝ))) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hCs hT1)
    _ = Book.Ch02.geometricDiscount ((3 / 4 - 1 / 2) / 4) 2 /
          Book.Ch02.geometricDiscount ((5 / 8 - 1 / 2) / 4) 2 *
        (1 - Real.rpow (3 : ℝ) (-2 * ((3 / 4 - 1 / 2) / 4 - (5 / 8 - 1 / 2) / 4)))⁻¹ * K *
        (Real.rpow (3 : ℝ) (2 * ((5 / 8 - 1 / 2) / 4) * (j : ℝ)) *
          ((3 : ℝ) ^ (-(kP : ℤ))) ^ (-(1 / 8 : ℝ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp (mul_nonneg hCs hKpos.le)

/-- Exponent bookkeeping for a cell of side `3^{-k}`:
`ρ^{d-2} (ρ^{3/4})² 3^{3k/16} = 3^{-k(d-1)} (3^{-5/16})^k`. -/
theorem aux_aux_macro_moment_bank_cell_exponent {d : ℕ} (hd : 1 ≤ d) (k : ℕ) :
    ((3 : ℝ) ^ (-(k : ℤ))) ^ ((d : ℝ) - 2) * (((3 : ℝ) ^ (-(k : ℤ))) ^ (3 / 4 : ℝ)) ^ 2 *
        (3 : ℝ) ^ ((3 / 16 : ℝ) * k) =
      (((3 : ℝ) ^ k) ^ (d - 1))⁻¹ * ((3 : ℝ) ^ (-(5 / 16 : ℝ))) ^ k := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have e0 : (3 : ℝ) ^ (-(k : ℤ)) = (3 : ℝ) ^ (-(k : ℝ)) := by
    rw [← Real.rpow_intCast]
    push_cast
    rfl
  rw [e0, ← Real.rpow_mul h3.le, ← Real.rpow_mul h3.le,
    ← Real.rpow_natCast ((3 : ℝ) ^ (-(k : ℝ) * (3 / 4))) 2, ← Real.rpow_mul h3.le,
    ← pow_mul, ← Real.rpow_natCast (3 : ℝ) (k * (d - 1)), ← Real.rpow_neg h3.le,
    ← Real.rpow_natCast ((3 : ℝ) ^ (-(5 / 16 : ℝ))) k, ← Real.rpow_mul h3.le,
    ← Real.rpow_add h3, ← Real.rpow_add h3, ← Real.rpow_add h3]
  congr 1
  push_cast [Nat.cast_sub hd]
  ring

/-- Real arithmetic of the per-cell bound. -/
theorem aux_aux_macro_moment_bank_cell_arith (Dr Cext Lam Cs K rd rb hs Cphi D T3 : ℝ)
    (hCext : 0 ≤ Cext) (hrd : 0 ≤ rd) (hrb : 0 ≤ rb) (hs0 : 0 ≤ hs) (hsle : hs ≤ Cphi * D)
    (hCs : 0 ≤ Cs) (hK : 0 ≤ K) (hT3 : 0 ≤ T3)
    (h1 : Dr ≤ Cext * Lam * rd * (rb * hs) ^ 2) (h2 : Lam ≤ Cs * K * T3) :
    Dr ≤ Cext * Cs * D ^ 2 * K * Cphi ^ 2 * (rd * rb ^ 2 * T3) := by
  have hsq : (rb * hs) ^ 2 ≤ (rb * (Cphi * D)) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hrb hs0) (mul_le_mul_of_nonneg_left hsle hrb) 2
  have hL2 : 0 ≤ Cs * K * T3 := mul_nonneg (mul_nonneg hCs hK) hT3
  calc Dr ≤ Cext * Lam * rd * (rb * hs) ^ 2 := h1
    _ ≤ Cext * (Cs * K * T3) * rd * (rb * (Cphi * D)) ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hCext) hrd) hsq
          (sq_nonneg _) (mul_nonneg (mul_nonneg hCext hL2) hrd)
    _ = Cext * Cs * D ^ 2 * K * Cphi ^ 2 * (rd * rb ^ 2 * T3) := by ring

/-- **(M5) Per-cell bound.**  On a depth-`k` cube of the unit root, `eq:mfd-2` on the cell
itself (below the cutoff as well) and the ancestor discount give the cell response bound
`Cext C_{ss'} d^{1/4} K Cφ² 3^{-k(d-1)} 3^{-5k/16}`. -/
theorem aux_aux_macro_moment_bank_cell_response {d : ℕ} (hd : 2 ≤ d) (E : in_J d)
    (Cext : ℝ) (hCext : 0 < Cext)
    (hext : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
          ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
            K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
        (a : PositiveCoefficient (centeredCube z r hr))
        (G : SpatialCoordinates d → ℝ) (b : weakSobolevGraph (centeredCube z r hr)),
        ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)) →
        IsHolderOn (3 / 4) (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G →
        ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G →
        dirichletResponse (killedResponseSpace hP) a b ≤
          Cext * E.Lam z r hr a z r ((3 / 4 - 1 / 2) / 4) 2 * r ^ ((d : ℝ) - 2) *
            (r ^ (3 / 4 : ℝ) *
              holderSeminorm (3 / 4)
                (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (K : ℝ)
    (hK : ∀ (k : ℕ) (nidx : Fin d → ℤ), k ≤ N →
      aux_aux_macro_moment_bank_cell z k nidx ≤ centeredCube z 1 one_pos →
      E.Lam z 1 one_pos (cutoffPositiveCoefficient M H om N z one_pos)
          (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ)) ((3 : ℝ) ^ (-(k : ℤ)))
          ((5 / 8 - 1 / 2) / 4) 2 +
        (E.lam z 1 one_pos (cutoffPositiveCoefficient M H om N z one_pos)
          (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ)) ((3 : ℝ) ^ (-(k : ℤ)))
          ((5 / 8 - 1 / 2) / 4) 2)⁻¹ ≤
        K * ((3 : ℝ) ^ (-(k : ℤ))) ^ (-(1 / 8 : ℝ)))
    (k : ℕ) (T : TriadicCube d) (hT : T ∈ descendantsAtDepth (originCube d 0) k)
    (w : SpatialCoordinates d) (hw : w = fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (T.index i : ℝ))
    (ρ : ℝ) (hρdef : ρ = (3 : ℝ) ^ (-(k : ℤ))) (hρ : 0 < ρ)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube w ρ hρ),
      ‖(u : SobolevData (centeredCube w ρ hρ)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube w ρ hρ)) u‖)
    (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ) (hphi : ContDiff ℝ 2 phi)
    (hC : c2Norm (closedCube w ρ hρ : Set (SpatialCoordinates d)) phi ≤ Cphi)
    (b : weakSobolevGraph (centeredCube w ρ hρ))
    (hb : ((b : SobolevData (centeredCube w ρ hρ)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube w ρ hρ : Set (SpatialCoordinates d))] phi) :
    dirichletResponse (killedResponseSpace hP) (cutoffPositiveCoefficient M H om N w hρ) b ≤
      Cext * aux_aux_macro_moment_bank_Cs * (Real.sqrt (d : ℝ) ^ (1 - 3 / 4 : ℝ)) ^ 2 * K *
        Cphi ^ 2 * ((((3 : ℝ) ^ k) ^ (d - 1))⁻¹ * ((3 : ℝ) ^ (-(5 / 16 : ℝ))) ^ k) := by
  subst hw hρdef
  have hρ1 : (3 : ℝ) ^ (-(k : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  obtain ⟨-, hcont, hhold, hs0, hsle⟩ := aux_aux_macro_moment_bank_boundary_holder
    (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (T.index i : ℝ)) ((3 : ℝ) ^ (-(k : ℤ)))
    hρ hρ1 (3 / 4) (by norm_num) phi hphi Cphi hC
  have hresp := hext (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (T.index i : ℝ))
    ((3 : ℝ) ^ (-(k : ℤ))) hρ hρ1 hP (cutoffPositiveCoefficient M H om N
      (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (T.index i : ℝ)) hρ) phi b hcont hhold hb
  obtain ⟨hKpos, hLam⟩ := aux_aux_macro_moment_bank_cell_Lam_le E M H om N z K hK k T hT
  rw [← aux_aux_macro_moment_bank_cell_exponent (by omega) k]
  exact aux_aux_macro_moment_bank_cell_arith _ Cext _ _ K _ _ _ Cphi _ _ hCext.le
    (Real.rpow_nonneg hρ.le _) (Real.rpow_nonneg hρ.le _) hs0 hsle
    aux_aux_macro_moment_bank_Cs_nonneg hKpos.le (Real.rpow_nonneg (by norm_num) _) hresp hLam

/-- The restriction of a boundary datum to a sub-cube keeps its a.e. identification. -/
theorem aux_aux_macro_moment_bank_restrict_datum_ae {d : ℕ} {U V : Opens (SpatialCoordinates d)}
    (hle : V ≤ U) (b : weakSobolevGraph U) (phi : SpatialCoordinates d → ℝ)
    (hb : ((b : SobolevData U).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (U : Set (SpatialCoordinates d))] phi) :
    (((⟨sobolevDataRestrict hle (b : SobolevData U),
        sobolevDataRestrict_mem_weak hle b.property⟩ : weakSobolevGraph V) :
          SobolevData V).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (V : Set (SpatialCoordinates d))] phi :=
  (domainLpRestrict_coeFn hle (b : SobolevData U).1).trans
    (ae_restrict_of_ae_restrict_of_subset hle hb)

/-- The constant of the working-cube boundary response. -/
def aux_aux_macro_moment_bank_Cstar (d : ℕ) (Cext : ℝ) : ℝ :=
  Cext * aux_aux_macro_moment_bank_Cs * (Real.sqrt (d : ℝ) ^ (1 - 3 / 4 : ℝ)) ^ 2 *
    (4 * d * (1 - (3 : ℝ) ^ (-(5 / 16 : ℝ)))⁻¹)

theorem aux_aux_macro_moment_bank_rho_facts :
    0 ≤ (3 : ℝ) ^ (-(5 / 16 : ℝ)) ∧ (3 : ℝ) ^ (-(5 / 16 : ℝ)) < 1 :=
  ⟨Real.rpow_nonneg (by norm_num) _,
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)⟩

theorem aux_aux_macro_moment_bank_Cstar_nonneg (d : ℕ) (Cext : ℝ) (hCext : 0 ≤ Cext) :
    0 ≤ aux_aux_macro_moment_bank_Cstar d Cext := by
  unfold aux_aux_macro_moment_bank_Cstar
  have h1 := aux_aux_macro_moment_bank_rho_facts.2
  have h2 : 0 < 1 - (3 : ℝ) ^ (-(5 / 16 : ℝ)) := by linarith
  have h3 := aux_aux_macro_moment_bank_Cs_nonneg
  have h4 : 0 ≤ Real.sqrt (d : ℝ) ^ (1 - 3 / 4 : ℝ) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  positivity

/-- **(M7, fixed depth)** Gluing the cell minimizers over the Whitney family of depth `Mw`:
the working-cube response is at most `C_* K Cφ²` plus the energy of the datum on the part of
the cube the family does not cover. -/
theorem aux_aux_macro_moment_bank_whitney_glue {d : ℕ} (hd : 2 ≤ d) (E : in_J d)
    (Cext : ℝ) (hCext : 0 < Cext)
    (hext : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
          ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
            K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
        (a : PositiveCoefficient (centeredCube z r hr))
        (G : SpatialCoordinates d → ℝ) (b : weakSobolevGraph (centeredCube z r hr)),
        ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)) →
        IsHolderOn (3 / 4) (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G →
        ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G →
        dirichletResponse (killedResponseSpace hP) a b ≤
          Cext * E.Lam z r hr a z r ((3 / 4 - 1 / 2) / 4) 2 * r ^ ((d : ℝ) - 2) *
            (r ^ (3 / 4 : ℝ) *
              holderSeminorm (3 / 4)
                (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (K : ℝ)
    (hK : ∀ (k : ℕ) (nidx : Fin d → ℤ), k ≤ N →
      aux_aux_macro_moment_bank_cell z k nidx ≤ centeredCube z 1 one_pos →
      E.Lam z 1 one_pos (cutoffPositiveCoefficient M H om N z one_pos)
          (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ)) ((3 : ℝ) ^ (-(k : ℤ)))
          ((5 / 8 - 1 / 2) / 4) 2 +
        (E.lam z 1 one_pos (cutoffPositiveCoefficient M H om N z one_pos)
          (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ)) ((3 : ℝ) ^ (-(k : ℤ)))
          ((5 / 8 - 1 / 2) / 4) 2)⁻¹ ≤
        K * ((3 : ℝ) ^ (-(k : ℤ))) ^ (-(1 / 8 : ℝ)))
    (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ) (hphi : ContDiff ℝ 2 phi)
    (hC : c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi)
    (b : weakSobolevGraph (centeredCube z r hr))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi)
    (Mw : ℕ) :
    dirichletResponse (killedResponseSpace hP) (cutoffPositiveCoefficient M H om N z hr) b ≤
      aux_aux_macro_moment_bank_Cstar d Cext * K * Cphi ^ 2 +
        ∑ i : Fin d, ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)) \
            ⋃ q : ↥(aux_aux_macro_moment_bank_whitney (d := d) r Mw),
              (centeredCube (fun i => z i + (3 : ℝ) ^ (-(q.1.1 : ℤ)) * (q.1.2.index i : ℝ))
                ((3 : ℝ) ^ (-(q.1.1 : ℤ))) (by positivity) : Set (SpatialCoordinates d)),
          (cutoffPositiveCoefficient M H om N z hr).val x *
            ((b : SobolevData (centeredCube z r hr)).2 i x *
              (b : SobolevData (centeredCube z r hr)).2 i x) := by
  classical
  have hle : ∀ q : ↥(aux_aux_macro_moment_bank_whitney (d := d) r Mw),
      centeredCube (fun i => z i + (3 : ℝ) ^ (-(q.1.1 : ℤ)) * (q.1.2.index i : ℝ))
        ((3 : ℝ) ^ (-(q.1.1 : ℤ))) (by positivity) ≤ centeredCube z r hr := by
    intro q
    have hmem := (aux_aux_macro_moment_bank_mem_whitney r Mw q.1).1 q.2
    exact aux_aux_macro_moment_bank_cell_le z r hr q.1.1 q.1.2
      (aux_aux_macro_moment_bank_scale_of_mem _ _ hmem.2.1) hmem.2.2.1
  have hdisj : Pairwise (fun q q' : ↥(aux_aux_macro_moment_bank_whitney (d := d) r Mw) =>
      Disjoint (centeredCube (fun i => z i + (3 : ℝ) ^ (-(q.1.1 : ℤ)) * (q.1.2.index i : ℝ))
          ((3 : ℝ) ^ (-(q.1.1 : ℤ))) (by positivity) : Set (SpatialCoordinates d))
        (centeredCube (fun i => z i + (3 : ℝ) ^ (-(q'.1.1 : ℤ)) * (q'.1.2.index i : ℝ))
          ((3 : ℝ) ^ (-(q'.1.1 : ℤ))) (by positivity) : Set (SpatialCoordinates d))) := by
    intro q q' hne
    exact aux_aux_macro_moment_bank_whitney_disjoint z r Mw q.1 q'.1 q.2 q'.2
      (fun h => hne (Subtype.ext h))
  have hPc : ∀ q : ↥(aux_aux_macro_moment_bank_whitney (d := d) r Mw),
      ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube
        (fun i => z i + (3 : ℝ) ^ (-(q.1.1 : ℤ)) * (q.1.2.index i : ℝ))
        ((3 : ℝ) ^ (-(q.1.1 : ℤ))) (by positivity)),
      ‖(u : SobolevData (centeredCube
        (fun i => z i + (3 : ℝ) ^ (-(q.1.1 : ℤ)) * (q.1.2.index i : ℝ))
        ((3 : ℝ) ^ (-(q.1.1 : ℤ))) (by positivity))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube
          (fun i => z i + (3 : ℝ) ^ (-(q.1.1 : ℤ)) * (q.1.2.index i : ℝ))
          ((3 : ℝ) ^ (-(q.1.1 : ℤ))) (by positivity))) u‖ := fun q =>
    aux_aux_macro_moment_bank_killed_poincare hd _ _ _
  have hac : ∀ q : ↥(aux_aux_macro_moment_bank_whitney (d := d) r Mw),
      ∀ᵐ x ∂volume.restrict (centeredCube
        (fun i => z i + (3 : ℝ) ^ (-(q.1.1 : ℤ)) * (q.1.2.index i : ℝ))
        ((3 : ℝ) ^ (-(q.1.1 : ℤ))) (by positivity) : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M H om N
          (fun i => z i + (3 : ℝ) ^ (-(q.1.1 : ℤ)) * (q.1.2.index i : ℝ))
          (by positivity : (0 : ℝ) < (3 : ℝ) ^ (-(q.1.1 : ℤ)))).val x =
        (cutoffPositiveCoefficient M H om N z hr).val x := fun q =>
    aux_aux_macro_moment_bank_cutoff_ae_eq M H om N _ _ _ z r hr (fun x hx => hle q hx)
  have hg := aux_aux_macro_moment_bank_glue_le
    (fun q : ↥(aux_aux_macro_moment_bank_whitney (d := d) r Mw) =>
      centeredCube (fun i => z i + (3 : ℝ) ^ (-(q.1.1 : ℤ)) * (q.1.2.index i : ℝ))
        ((3 : ℝ) ^ (-(q.1.1 : ℤ))) (by positivity)) hle hdisj hP hPc
    (cutoffPositiveCoefficient M H om N z hr)
    (fun q => cutoffPositiveCoefficient M H om N
      (fun i => z i + (3 : ℝ) ^ (-(q.1.1 : ℤ)) * (q.1.2.index i : ℝ))
      (by positivity : (0 : ℝ) < (3 : ℝ) ^ (-(q.1.1 : ℤ)))) hac b
  refine hg.trans (add_le_add ?_ le_rfl)
  have hCphi : 0 ≤ Cphi := by
    have h0 : 0 ≤ c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi := by
      unfold c2Norm
      have hA : 0 ≤ sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
          v = |phi x|} := Real.sSup_nonneg (by rintro v ⟨x, _, rfl⟩; exact abs_nonneg _)
      have hB : 0 ≤ sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
          v = ‖fderiv ℝ phi x‖} :=
        Real.sSup_nonneg (by rintro v ⟨x, _, rfl⟩; exact norm_nonneg (fderiv ℝ phi x))
      have hC' : 0 ≤ sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
          v = ‖fderiv ℝ (fderiv ℝ phi) x‖} :=
        Real.sSup_nonneg (by rintro v ⟨x, _, rfl⟩; exact norm_nonneg (fderiv ℝ (fderiv ℝ phi) x))
      linarith
    linarith
  have hKpos : 0 < K := (aux_aux_macro_moment_bank_cell_Lam_le E M H om N z K hK 0
    (originCube d 0) (by rw [descendantsAtDepth_zero]; exact Finset.mem_singleton_self _)).1
  have hcell : ∀ q : ↥(aux_aux_macro_moment_bank_whitney (d := d) r Mw),
      dirichletResponse (killedResponseSpace (hPc q))
          (cutoffPositiveCoefficient M H om N
            (fun i => z i + (3 : ℝ) ^ (-(q.1.1 : ℤ)) * (q.1.2.index i : ℝ))
            (by positivity : (0 : ℝ) < (3 : ℝ) ^ (-(q.1.1 : ℤ))))
          ⟨sobolevDataRestrict (hle q) (b : SobolevData (centeredCube z r hr)),
            sobolevDataRestrict_mem_weak (hle q) b.property⟩ ≤
        Cext * aux_aux_macro_moment_bank_Cs * (Real.sqrt (d : ℝ) ^ (1 - 3 / 4 : ℝ)) ^ 2 * K *
          Cphi ^ 2 * ((((3 : ℝ) ^ q.1.1) ^ (d - 1))⁻¹ * ((3 : ℝ) ^ (-(5 / 16 : ℝ))) ^ q.1.1) := by
    intro q
    have hmem := (aux_aux_macro_moment_bank_mem_whitney r Mw q.1).1 q.2
    have hsub : (centeredCube (fun i => z i + (3 : ℝ) ^ (-(q.1.1 : ℤ)) * (q.1.2.index i : ℝ))
        ((3 : ℝ) ^ (-(q.1.1 : ℤ))) (by positivity) : Set (SpatialCoordinates d)) ⊆
        centeredCube z r hr := fun x hx => hle q hx
    have hCq : c2Norm (closedCube (fun i => z i + (3 : ℝ) ^ (-(q.1.1 : ℤ)) * (q.1.2.index i : ℝ))
        ((3 : ℝ) ^ (-(q.1.1 : ℤ))) (by positivity) : Set (SpatialCoordinates d)) phi ≤ Cphi :=
      (aux_aux_macro_moment_bank_c2Norm_mono _ _ (closedCube z r hr).isCompact
        ⟨_, Metric.mem_closedBall_self (by positivity)⟩
        (aux_aux_macro_moment_bank_closedCube_subset _ _ _ z r hr hsub) phi hphi).trans hC
    exact aux_aux_macro_moment_bank_cell_response hd E Cext hCext hext M H om N z K hK q.1.1
      q.1.2 hmem.2.1 _ rfl _ rfl _ (hPc q) phi Cphi hphi hCq _
      (aux_aux_macro_moment_bank_restrict_datum_ae (hle q) b phi hb)
  have hsum := aux_aux_macro_moment_bank_whitney_sum (d := d) (by omega) r Mw
    ((3 : ℝ) ^ (-(5 / 16 : ℝ))) aux_aux_macro_moment_bank_rho_facts.1
    aux_aux_macro_moment_bank_rho_facts.2
  have hC0 : 0 ≤ Cext * aux_aux_macro_moment_bank_Cs *
      (Real.sqrt (d : ℝ) ^ (1 - 3 / 4 : ℝ)) ^ 2 * K * Cphi ^ 2 := by
    have := aux_aux_macro_moment_bank_Cs_nonneg
    have := hCext.le
    positivity
  calc _ ≤ ∑ q : ↥(aux_aux_macro_moment_bank_whitney (d := d) r Mw),
        Cext * aux_aux_macro_moment_bank_Cs * (Real.sqrt (d : ℝ) ^ (1 - 3 / 4 : ℝ)) ^ 2 * K *
          Cphi ^ 2 * ((((3 : ℝ) ^ q.1.1) ^ (d - 1))⁻¹ * ((3 : ℝ) ^ (-(5 / 16 : ℝ))) ^ q.1.1) :=
        Finset.sum_le_sum fun q _ => hcell q
    _ = Cext * aux_aux_macro_moment_bank_Cs * (Real.sqrt (d : ℝ) ^ (1 - 3 / 4 : ℝ)) ^ 2 * K *
          Cphi ^ 2 * ∑ p ∈ aux_aux_macro_moment_bank_whitney (d := d) r Mw,
            ((((3 : ℝ) ^ p.1) ^ (d - 1))⁻¹ * ((3 : ℝ) ^ (-(5 / 16 : ℝ))) ^ p.1) := by
        rw [← Finset.mul_sum]
        congr 1
        exact Finset.sum_coe_sort (aux_aux_macro_moment_bank_whitney (d := d) r Mw)
          (fun p => (((3 : ℝ) ^ p.1) ^ (d - 1))⁻¹ * ((3 : ℝ) ^ (-(5 / 16 : ℝ))) ^ p.1)
    _ ≤ Cext * aux_aux_macro_moment_bank_Cs * (Real.sqrt (d : ℝ) ^ (1 - 3 / 4 : ℝ)) ^ 2 * K *
          Cphi ^ 2 * (4 * d * (1 - (3 : ℝ) ^ (-(5 / 16 : ℝ)))⁻¹) :=
        mul_le_mul_of_nonneg_left hsum hC0
    _ = aux_aux_macro_moment_bank_Cstar d Cext * K * Cphi ^ 2 := by
        unfold aux_aux_macro_moment_bank_Cstar
        ring

/-- **(W3, qualitative)** The energy of an integrable density on the part of the working
cube left uncovered by the Whitney family of depth `Mw` vanishes as `Mw → ∞`. -/
theorem aux_aux_macro_moment_bank_uncovered_tendsto {d : ℕ} (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (f : SpatialCoordinates d → ℝ)
    (hf : IntegrableOn f (centeredCube z r hr : Set (SpatialCoordinates d)) volume) :
    Filter.Tendsto (fun Mw : ℕ => ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)) \
        ⋃ q : ↥(aux_aux_macro_moment_bank_whitney (d := d) r Mw),
          (centeredCube (fun i => z i + (3 : ℝ) ^ (-(q.1.1 : ℤ)) * (q.1.2.index i : ℝ))
            ((3 : ℝ) ^ (-(q.1.1 : ℤ))) (by positivity) : Set (SpatialCoordinates d)), f x)
      Filter.atTop (nhds 0) := by
  obtain ⟨s, hs⟩ : ∃ s : ℕ → Set (SpatialCoordinates d), s = fun Mw =>
      (centeredCube z r hr : Set (SpatialCoordinates d)) \
        ⋃ q : ↥(aux_aux_macro_moment_bank_whitney (d := d) r Mw),
          (centeredCube (fun i => z i + (3 : ℝ) ^ (-(q.1.1 : ℤ)) * (q.1.2.index i : ℝ))
            ((3 : ℝ) ^ (-(q.1.1 : ℤ))) (by positivity) : Set (SpatialCoordinates d)) :=
    ⟨_, rfl⟩
  have hsm : ∀ Mw, MeasurableSet (s Mw) := by
    intro Mw
    rw [hs]
    exact (centeredCube z r hr).isOpen.measurableSet.diff
      (isOpen_iUnion fun q => (centeredCube _ _ _).isOpen).measurableSet
  have hanti : Antitone s := by
    intro M1 M2 h12 x hx
    rw [hs] at hx ⊢
    refine ⟨hx.1, fun hx1 => hx.2 ?_⟩
    obtain ⟨q, hq⟩ := Set.mem_iUnion.1 hx1
    have hmem := (aux_aux_macro_moment_bank_mem_whitney r M1 q.1).1 q.2
    exact Set.mem_iUnion.2 ⟨⟨q.1, (aux_aux_macro_moment_bank_mem_whitney r M2 q.1).2
      ⟨hmem.1.trans h12, hmem.2⟩⟩, hq⟩
  have hnull : volume (⋂ Mw, s Mw) = 0 := by
    refine measure_mono_null ?_ (aux_aux_macro_moment_bank_faces_null z)
    intro x hx
    rw [Set.mem_iInter] at hx
    by_contra hnot
    simp only [Set.mem_setOf_eq, not_exists] at hnot
    have hx0 := hx 0
    rw [hs] at hx0
    obtain ⟨Mw, p, hp, hxp⟩ := aux_aux_macro_moment_bank_whitney_cover z r hr hr1 x hx0.1
      (fun i k q => hnot i k q)
    have hxM := hx Mw
    rw [hs] at hxM
    exact hxM.2 (Set.mem_iUnion.2 ⟨⟨p, hp⟩, hxp⟩)
  have h := tendsto_setIntegral_of_antitone hsm hanti
    ⟨0, hf.mono_set (by rw [hs]; exact Set.diff_subset)⟩
  rw [setIntegral_measure_zero _ hnull] at h
  rw [hs] at h
  exact h

/-- **(M7) The working-cube boundary response.**  On the `eq:mfd-3` event of the root
`(z, 1)` at the cutoff `N`, the Dirichlet response of every `C²` datum on the working cube
is at most `C_* K Cφ²`, for every side `r ≤ 1` and every cutoff. -/
theorem aux_aux_macro_moment_bank_boundary_response {d : ℕ} (hd : 2 ≤ d) (E : in_J d)
    (Cext : ℝ) (hCext : 0 < Cext)
    (hext : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
          ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
            K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
        (a : PositiveCoefficient (centeredCube z r hr))
        (G : SpatialCoordinates d → ℝ) (b : weakSobolevGraph (centeredCube z r hr)),
        ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)) →
        IsHolderOn (3 / 4) (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G →
        ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G →
        dirichletResponse (killedResponseSpace hP) a b ≤
          Cext * E.Lam z r hr a z r ((3 / 4 - 1 / 2) / 4) 2 * r ^ ((d : ℝ) - 2) *
            (r ^ (3 / 4 : ℝ) *
              holderSeminorm (3 / 4)
                (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (K : ℝ)
    (hK : ∀ (k : ℕ) (nidx : Fin d → ℤ), k ≤ N →
      aux_aux_macro_moment_bank_cell z k nidx ≤ centeredCube z 1 one_pos →
      E.Lam z 1 one_pos (cutoffPositiveCoefficient M H om N z one_pos)
          (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ)) ((3 : ℝ) ^ (-(k : ℤ)))
          ((5 / 8 - 1 / 2) / 4) 2 +
        (E.lam z 1 one_pos (cutoffPositiveCoefficient M H om N z one_pos)
          (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ)) ((3 : ℝ) ^ (-(k : ℤ)))
          ((5 / 8 - 1 / 2) / 4) 2)⁻¹ ≤
        K * ((3 : ℝ) ^ (-(k : ℤ))) ^ (-(1 / 8 : ℝ)))
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ) (hphi : ContDiff ℝ 2 phi)
    (hC : c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi)
    (b : weakSobolevGraph (centeredCube z r hr))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi) :
    dirichletResponse (killedResponseSpace hP) (cutoffPositiveCoefficient M H om N z hr) b ≤
      aux_aux_macro_moment_bank_Cstar d Cext * K * Cphi ^ 2 := by
  obtain ⟨Ca, hCa⟩ := lane2_coeff_ae_bound (cutoffPositiveCoefficient M H om N z hr)
  have hint : ∀ i : Fin d, IntegrableOn (fun x =>
      (cutoffPositiveCoefficient M H om N z hr).val x *
        ((b : SobolevData (centeredCube z r hr)).2 i x *
          (b : SobolevData (centeredCube z r hr)).2 i x))
      (centeredCube z r hr : Set (SpatialCoordinates d)) volume := fun i =>
    lane2_integrableOn_coeff_mul (Lp.aestronglyMeasurable _) hCa (Lp.memLp _) (Lp.memLp _)
  have hε := tendsto_finset_sum (Finset.univ : Finset (Fin d)) (fun i _ =>
    aux_aux_macro_moment_bank_uncovered_tendsto z r hr hr1 _ (hint i))
  simp only [Finset.sum_const_zero] at hε
  have hlim := hε.const_add (aux_aux_macro_moment_bank_Cstar d Cext * K * Cphi ^ 2)
  rw [add_zero] at hlim
  exact ge_of_tendsto' hlim (fun Mw => aux_aux_macro_moment_bank_whitney_glue hd E Cext hCext
    hext M H om N z K hK r hr hP phi Cphi hphi hC b hb Mw)

end RouteWGeo

/-- **Deterministic energy majorant, boundary-response form** (the `hKsource` inequality
before moments): if the Dirichlet response of the datum is at most `K_b C_φ²`, then
`E(u,u) ≤ (|K_b| + c₂ |K_c|) (K_f + C_φ)²`, with the coercivity factor `K_c` of
`lem_coercivity` (`eq:mfd-1`) and a deterministic `c₂`. -/
theorem aux_aux_macro_moment_bank_energy_le_bd {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
        ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (a : PositiveCoefficient (centeredCube z r hr)) (Kc : ℝ)
    (hcoer : ∀ v : killedSobolevGraph (centeredCube z r hr),
      cubeFractionalSqNorm hd z r hr threeQuarterOrder
          (v : SobolevData (centeredCube z r hr)).1 ≤
        Kc * sobolevCoefficientForm a (v : SobolevData (centeredCube z r hr))
          (v : SobolevData (centeredCube z r hr)))
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hF : AEMeasurable F
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂(volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf)
    (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ) (hphi : ContDiff ℝ 2 phi)
    (hC : c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi)
    (b u : weakSobolevGraph (centeredCube z r hr))
    (hsol : SolvesDirichlet a F b u) (Kb : ℝ)
    (hbd : dirichletResponse (killedResponseSpace hP) a b ≤ Kb * Cphi ^ 2) :
    sobolevCoefficientForm a (u : SobolevData (centeredCube z r hr))
        (u : SobolevData (centeredCube z r hr)) ≤
      (|Kb| +
        ((measureUnivNNReal (volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))) : ℝ) ^
            ((2 : ℝ≥0∞).toReal⁻¹)) ^ 2 *
          volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) * |Kc|) *
        (Kf + Cphi) ^ 2 := by
  have hCphi := (aux_aux_macro_moment_bank_boundary_holder z r hr hr1 (3 / 4) (by norm_num)
    phi hphi Cphi hC).1
  obtain ⟨w, hwk, hsplit, hww⟩ := aux_aux_macro_moment_bank_energy_split hP a F b u hsol
  have hm0 : 0 ≤ (measureUnivNNReal (volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))) : ℝ) ^ ((2 : ℝ≥0∞).toReal⁻¹) :=
    Real.rpow_nonneg (NNReal.coe_nonneg _) _
  have hvol0 : 0 ≤ volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube_volume_pos z hr).le
  have he0 : 0 ≤ sobolevCoefficientForm a w w := sobolevCoefficientForm_nonneg a w
  have hpair := aux_aux_macro_moment_bank_source_pairing_le F Kf hKf hF hFb w.1
  have hl2 := aux_aux_macro_moment_bank_l2_le_of_coercive hd z r hr a Kc w (hcoer ⟨w, hwk⟩)
  generalize (measureUnivNNReal (volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))) : ℝ) ^ ((2 : ℝ≥0∞).toReal⁻¹) = m
    at hm0 hpair ⊢
  generalize volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) = vol
    at hvol0 hl2 ⊢
  generalize dirichletResponse (killedResponseSpace hP) a b = Dr at hbd hsplit
  generalize sobolevCoefficientForm a w w = e at he0 hww hsplit hl2
  rw [← hww] at hpair
  have hn0 : 0 ≤ ‖w.1‖ := norm_nonneg _
  generalize ‖w.1‖ = n at hpair hl2 hn0
  rw [hsplit]
  have hkill : e ≤ (m * Kf) ^ 2 * (vol * |Kc|) :=
    aux_aux_macro_moment_bank_killed_energy_le e n (m * Kf) (vol * |Kc|) he0
      (mul_nonneg hvol0 (abs_nonneg _)) hpair
      (by rw [mul_assoc]; exact hl2)
  have hKf2 : Kf ^ 2 ≤ (Kf + Cphi) ^ 2 := pow_le_pow_left₀ hKf (by linarith) 2
  have hC2 : Cphi ^ 2 ≤ (Kf + Cphi) ^ 2 := pow_le_pow_left₀ hCphi (by linarith) 2
  have h1 : Kb * Cphi ^ 2 ≤ |Kb| * (Kf + Cphi) ^ 2 :=
    (mul_le_mul_of_nonneg_right (le_abs_self Kb) (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hC2 (abs_nonneg _))
  have h2 : (m * Kf) ^ 2 * (vol * |Kc|) ≤ m ^ 2 * vol * |Kc| * (Kf + Cphi) ^ 2 := by
    have : (m * Kf) ^ 2 * (vol * |Kc|) = m ^ 2 * vol * |Kc| * Kf ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hKf2 (by positivity)
  have : (|Kb| + m ^ 2 * vol * |Kc|) * (Kf + Cphi) ^ 2 =
      |Kb| * (Kf + Cphi) ^ 2 + m ^ 2 * vol * |Kc| * (Kf + Cphi) ^ 2 := by ring
  rw [this]
  linarith

/-- **Fixed-model assembly, boundary-response form.**  Given the prefix bound with its
moments, the reference majorant, the coercivity factor, and an almost-sure bound
`Λ_{N,Q}(b) ≤ K_ext C_φ²` on the working-cube Dirichlet response with moments at the doubled
exponent `2P`, the common prefactor `Kmac = 3^{t₁ Lmac} (exp ‖H|_Q̄‖ + |K_ext| + c₂ |K|)`
satisfies every clause of the bank. -/
theorem aux_aux_macro_moment_bank_assemble_bd {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (t1 : ℝ) (k : ℕ) (ps : Fin k → ℝ) (Pexp : ℝ)
    (hP1 : 1 ≤ Pexp) (hpsP : ∀ i, ps i ≤ Pexp)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (Lmac : ℕ → BilateralField d → ℕ) (hLmeas : ∀ N, Measurable (Lmac N))
    (BX : ℝ≥0∞) (hBX : BX ≠ ⊤)
    (hX : ∀ N, eLpNorm (fun om => (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)))
      (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure ≤ BX)
    (hprefix : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N L0 : ℕ,
      ∃ L' : ℕ, L0 ≤ L' ∧
        Sreg.prefixLen (N + L') (1 - ((d : ℝ) - t1) / 4) N ((3 : ℝ) ^ N • z)
          (fun j => ContinuousMap.compRightContinuousMap ℝ
            (⟨fun x : SpatialCoordinates d => (3 : ℝ) ^ (-(N : ℤ)) • x,
              continuous_const.smul continuous_id⟩ :
              C(SpatialCoordinates d, SpatialCoordinates d))
            (om (j - (N : ℤ)))) ≤ Lmac N om)
    (hRmeas : Measurable
      (fun om => Real.exp ‖(H om).restrict (closedCube z r hr : Set (SpatialCoordinates d))‖))
    (hRdom : ∀ om, ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      Real.exp (|H om x|) ≤
        Real.exp ‖(H om).restrict (closedCube z r hr : Set (SpatialCoordinates d))‖)
    (hRmem : MemLp
      (fun om => Real.exp ‖(H om).restrict (closedCube z r hr : Set (SpatialCoordinates d))‖)
      (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure)
    (Kco : ℕ → BilateralField d → ℝ)
    (hKco : ∀ N om, ∀ v : killedSobolevGraph (centeredCube z r hr),
      cubeFractionalSqNorm hd z r hr threeQuarterOrder
          (v : SobolevData (centeredCube z r hr)).1 ≤
        Kco N om * sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr)
          (v : SobolevData (centeredCube z r hr)) (v : SobolevData (centeredCube z r hr)))
    (CK : ℝ)
    (hKmem : ∀ N, MemLp (Kco N) (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure)
    (hKbd : ∀ N, eLpNorm (Kco N) (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal CK)
    (Kext : ℕ → BilateralField d → ℝ) (CL : ℝ)
    (hKextmem : ∀ N, MemLp (Kext N) (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure)
    (hKextbd : ∀ N, eLpNorm (Kext N) (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal CL)
    (hBd : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ (N : ℕ)
      (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
        ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
      (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
      ContDiff ℝ 2 phi →
      c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
      ∀ b : weakSobolevGraph (centeredCube z r hr),
      ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
      dirichletResponse (killedResponseSpace hP) (cutoffPositiveCoefficient M H om N z hr) b ≤
        Kext N om * Cphi ^ 2) :
    ∃ (Lmac : ℕ → BilateralField d → ℕ) (Kmac : ℕ → BilateralField d → ℝ)
      (Cbound : Fin k → ℝ),
      (∀ N om, 0 ≤ Kmac N om) ∧
      (∀ i N, MemLp (Kmac N) (ENNReal.ofReal (ps i))
        (chaosSampleLaw M).toMeasure) ∧
      (∀ i N, eLpNorm (Kmac N) (ENNReal.ofReal (ps i))
          (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cbound i)) ∧
      (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N L0 : ℕ,
        ∃ L' : ℕ, L0 ≤ L' ∧
          Sreg.prefixLen (N + L') (1 - ((d : ℝ) - t1) / 4) N
            ((3 : ℝ) ^ N • z)
            (fun j => ContinuousMap.compRightContinuousMap ℝ
              (⟨fun x : SpatialCoordinates d => (3 : ℝ) ^ (-(N : ℤ)) • x,
                continuous_const.smul continuous_id⟩ :
                C(SpatialCoordinates d, SpatialCoordinates d))
              (om (j - (N : ℤ)))) ≤ Lmac N om) ∧
      (∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
          ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
            ContDiff ℝ 2 phi →
            c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
          ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
            ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
            SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
            (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)) *
              sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr)
                (u : SobolevData (centeredCube z r hr))
                (u : SobolevData (centeredCube z r hr)) ≤
                Kmac N om * (Kf + Cphi) ^ 2) ∧
      (∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ N x, x ∈ closedCube z r hr →
          (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)) * Real.exp (|H om x|) ≤ Kmac N om) := by
  have hPc := aux_aux_macro_moment_bank_killed_poincare hd z r hr
  -- the deterministic constants of the energy majorant
  obtain ⟨c1, hc1⟩ : ∃ c1 : ℝ, c1 = 1 := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c2 : ℝ,
      c2 = ((measureUnivNNReal (volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))) : ℝ) ^
            ((2 : ℝ≥0∞).toReal⁻¹)) ^ 2 *
          volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) := ⟨_, rfl⟩
  have hc10 : 0 ≤ c1 := by rw [hc1]; norm_num
  have hc20 : 0 ≤ c2 := by
    rw [hc2]
    have := (centeredCube_volume_pos z hr).le
    positivity
  -- the bracket and the prefactor
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℕ → BilateralField d → ℝ, Y = fun N om =>
      Real.exp ‖(H om).restrict (closedCube z r hr : Set (SpatialCoordinates d))‖ +
        (c1 * |Kext N om| + c2 * |Kco N om|) := ⟨_, rfl⟩
  obtain ⟨Kmac, hKmac⟩ : ∃ Kmac : ℕ → BilateralField d → ℝ,
      Kmac = fun N om => (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)) * Y N om := ⟨_, rfl⟩
  have hbr0 : ∀ N om, 0 ≤ c1 * |Kext N om| + c2 * |Kco N om| := by
    intro N om
    positivity
  have hY0 : ∀ N om, Real.exp ‖(H om).restrict (closedCube z r hr : Set (SpatialCoordinates d))‖ +
      (c1 * |Kext N om| + c2 * |Kco N om|) ≤ Y N om := by
    intro N om
    rw [hYdef]
  have hYnn : ∀ N om, 0 ≤ Y N om := by
    intro N om
    refine le_trans ?_ (hY0 N om)
    have := hbr0 N om
    have := Real.exp_pos ‖(H om).restrict (closedCube z r hr : Set (SpatialCoordinates d))‖
    linarith
  have hK0 : ∀ N om, 0 ≤ Kmac N om := by
    intro N om
    rw [hKmac]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hYnn N om)
  -- moments
  have hXmeas : ∀ N, AEStronglyMeasurable (fun om => (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)))
      (chaosSampleLaw M).toMeasure := fun N =>
    ((measurable_from_nat (f := fun n : ℕ => (3 : ℝ) ^ (t1 * (n : ℝ)))).comp
      (hLmeas N)).aestronglyMeasurable
  have hYmeas : ∀ N, AEStronglyMeasurable (Y N) (chaosSampleLaw M).toMeasure := by
    intro N
    rw [hYdef]
    exact hRmeas.aestronglyMeasurable.add
      (((hKextmem N).1.norm.const_mul c1).add ((hKmem N).1.norm.const_mul c2))
  have hYbd : ∀ N, eLpNorm (Y N) (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure ≤
      eLpNorm (fun om => Real.exp ‖(H om).restrict
          (closedCube z r hr : Set (SpatialCoordinates d))‖)
        (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure +
      (ENNReal.ofReal c1 * ENNReal.ofReal CL + ENNReal.ofReal c2 * ENNReal.ofReal CK) := by
    intro N
    rw [hYdef]
    exact aux_aux_macro_moment_bank_bracket_moment (chaosSampleLaw M).toMeasure (2 * Pexp)
      (by linarith) _ _ (Kco N) c1 c2 CL CK hc10 hc20 hRmeas.aestronglyMeasurable
      (hKextmem N).1 (hKmem N).1 (hKextbd N) (hKbd N)
  obtain ⟨BY, hBYdef⟩ : ∃ BY : ℝ≥0∞, BY =
      eLpNorm (fun om => Real.exp ‖(H om).restrict
          (closedCube z r hr : Set (SpatialCoordinates d))‖)
        (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure +
      (ENNReal.ofReal c1 * ENNReal.ofReal CL + ENNReal.ofReal c2 * ENNReal.ofReal CK) :=
    ⟨_, rfl⟩
  rw [← hBYdef] at hYbd
  have hBYtop : BY ≠ ⊤ := by
    rw [hBYdef]
    exact ENNReal.add_ne_top.2 ⟨hRmem.2.ne, ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩⟩
  have hKmeas : ∀ N, AEStronglyMeasurable (Kmac N) (chaosSampleLaw M).toMeasure := by
    intro N
    rw [hKmac]
    exact (hXmeas N).mul (hYmeas N)
  have hKP : ∀ N, eLpNorm (Kmac N) (ENNReal.ofReal Pexp) (chaosSampleLaw M).toMeasure ≤
      BX * BY := by
    intro N
    rw [hKmac]
    exact (aux_aux_macro_moment_bank_product_moment (chaosSampleLaw M).toMeasure Pexp
      _ _ (hXmeas N) (hYmeas N)).trans (mul_le_mul' (hX N) (hYbd N))
  have hBtop : BX * BY ≠ ⊤ := ENNReal.mul_ne_top hBX hBYtop
  have hKi : ∀ i N, eLpNorm (Kmac N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (BX * BY).toReal := by
    intro i N
    rw [ENNReal.ofReal_toReal hBtop]
    exact (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (hpsP i))
      (hKmeas N)).trans (hKP N)
  refine ⟨Lmac, Kmac, fun _ => (BX * BY).toReal, hK0, ?_, hKi, hprefix, ?_, ?_⟩
  · intro i N
    exact ⟨hKmeas N, (hKi i N).trans_lt ENNReal.ofReal_lt_top⟩
  · filter_upwards [hBd] with om hBd
    intro N F Kf hKf hF hFb phi Cphi hphi hC b u hb hsol
    have hen := aux_aux_macro_moment_bank_energy_le_bd hd z r hr hr1 hPc
      (cutoffPositiveCoefficient M H om N z hr) (Kco N om) (hKco N om) F Kf hKf hF hFb
      phi Cphi hphi hC b u hsol (Kext N om) (hBd N hPc phi Cphi hphi hC b hb)
    rw [← hc2] at hen
    have h3 : 0 ≤ (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)) := Real.rpow_nonneg (by norm_num) _
    have hsq : 0 ≤ (Kf + Cphi) ^ 2 := sq_nonneg _
    have hYge := hY0 N om
    have hexp0 := Real.exp_pos ‖(H om).restrict (closedCube z r hr : Set (SpatialCoordinates d))‖
    have hKe : Kmac N om = (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)) * Y N om := by rw [hKmac]
    have hc1' : c1 * |Kext N om| = |Kext N om| := by rw [hc1, one_mul]
    rw [hKe, mul_assoc]
    refine mul_le_mul_of_nonneg_left (hen.trans ?_) h3
    exact mul_le_mul_of_nonneg_right (by linarith) hsq
  · refine Filter.Eventually.of_forall fun om => ?_
    intro N x hx
    have h3 : 0 ≤ (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)) := Real.rpow_nonneg (by norm_num) _
    have hKe : Kmac N om = (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)) * Y N om := by rw [hKmac]
    rw [hKe]
    refine mul_le_mul_of_nonneg_left ?_ h3
    have := hRdom om x hx
    have := hbr0 N om
    have := hY0 N om
    linarith

/-- **Per-model step, boundary-response form**: from the threshold facts, the moment inputs
and the working-cube response bound, build the bank. -/
theorem aux_aux_macro_moment_bank_per_model_bd {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (t1 : ℝ) (ht10 : 0 ≤ t1) (k : ℕ) (ps : Fin k → ℝ) (Pexp : ℝ)
    (hP1 : 1 ≤ Pexp) (hpsP : ∀ i, ps i ≤ Pexp)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hδC : M.delta ≤ Sreg.C⁻¹) (hα : 1 - ((d : ℝ) - t1) / 4 ∈ Sreg.alphaRange)
    (hκlam : 2 * Pexp * t1 * Real.log 3 <
      (1 - (1 - ((d : ℝ) - t1) / 4)) ^ 2 / (Sreg.C * M.delta ^ 2 * |Real.log M.delta|))
    (Kco : ℕ → BilateralField d → ℝ)
    (hKco : ∀ N om, ∀ v : killedSobolevGraph (centeredCube z r hr),
      cubeFractionalSqNorm hd z r hr threeQuarterOrder
          (v : SobolevData (centeredCube z r hr)).1 ≤
        Kco N om * sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr)
          (v : SobolevData (centeredCube z r hr)) (v : SobolevData (centeredCube z r hr)))
    (CK : ℝ)
    (hKmem : ∀ N, MemLp (Kco N) (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure)
    (hKbd : ∀ N, eLpNorm (Kco N) (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal CK)
    (Kext : ℕ → BilateralField d → ℝ) (CL : ℝ)
    (hKextmem : ∀ N, MemLp (Kext N) (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure)
    (hKextbd : ∀ N, eLpNorm (Kext N) (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal CL)
    (hBd : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ (N : ℕ)
      (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
        ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
      (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
      ContDiff ℝ 2 phi →
      c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
      ∀ b : weakSobolevGraph (centeredCube z r hr),
      ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
      dirichletResponse (killedResponseSpace hP) (cutoffPositiveCoefficient M H om N z hr) b ≤
        Kext N om * Cphi ^ 2) :
    ∃ (Lmac : ℕ → BilateralField d → ℕ) (Kmac : ℕ → BilateralField d → ℝ)
      (Cbound : Fin k → ℝ),
      (∀ N om, 0 ≤ Kmac N om) ∧
      (∀ i N, MemLp (Kmac N) (ENNReal.ofReal (ps i))
        (chaosSampleLaw M).toMeasure) ∧
      (∀ i N, eLpNorm (Kmac N) (ENNReal.ofReal (ps i))
          (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cbound i)) ∧
      (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N L0 : ℕ,
        ∃ L' : ℕ, L0 ≤ L' ∧
          Sreg.prefixLen (N + L') (1 - ((d : ℝ) - t1) / 4) N
            ((3 : ℝ) ^ N • z)
            (fun j => ContinuousMap.compRightContinuousMap ℝ
              (⟨fun x : SpatialCoordinates d => (3 : ℝ) ^ (-(N : ℤ)) • x,
                continuous_const.smul continuous_id⟩ :
                C(SpatialCoordinates d, SpatialCoordinates d))
              (om (j - (N : ℤ)))) ≤ Lmac N om) ∧
      (∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
          ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
            ContDiff ℝ 2 phi →
            c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
          ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
            ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
            SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
            (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)) *
              sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr)
                (u : SobolevData (centeredCube z r hr))
                (u : SobolevData (centeredCube z r hr)) ≤
                Kmac N om * (Kf + Cphi) ^ 2) ∧
      (∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ N x, x ∈ closedCube z r hr →
          (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)) * Real.exp (|H om x|) ≤ Kmac N om) := by
  have hQ1 : 1 ≤ 2 * Pexp := by linarith
  have hlam : 0 ≤ 2 * Pexp * t1 * Real.log 3 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
    have : (0 : ℝ) ≤ Pexp := by linarith
    positivity
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = (1 - (1 - ((d : ℝ) - t1) / 4)) ^ 2 /
      (Sreg.C * M.delta ^ 2 * |Real.log M.delta|) := ⟨_, rfl⟩
  rw [← hκ] at hκlam
  have hκ0 : 0 < κ := lt_of_le_of_lt hlam hκlam
  obtain ⟨Lmac, hLmeas, hLtail, hLpre⟩ :=
    aux_aux_macro_moment_bank_prefix M Sreg (1 - ((d : ℝ) - t1) / 4) κ hδC hα hκ hκ0 z
  have hA1 : 1 ≤ Sreg.C * Real.exp (κ * Sreg.C) := by
    have h1 := Sreg.C_ge_one
    have h2 : 1 ≤ Real.exp (κ * Sreg.C) := Real.one_le_exp (by positivity)
    nlinarith
  have hX : ∀ N, eLpNorm (fun om => (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)))
      (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Sreg.C * Real.exp (κ * Sreg.C) * Real.exp κ *
        (1 - Real.exp (-(κ - 2 * Pexp * t1 * Real.log 3)))⁻¹) ^ (1 / (2 * Pexp)) := by
    intro N
    exact aux_aux_macro_moment_bank_eLpNorm_rpow_three_le _ (Lmac N) t1 (2 * Pexp)
      (by linarith) _ (aux_aux_macro_moment_bank_lintegral_exp_le (chaosSampleLaw M).toMeasure
        (Lmac N) (hLmeas N) (Sreg.C * Real.exp (κ * Sreg.C)) κ _ hA1 hlam hκlam (hLtail N))
  obtain ⟨hRmeas, hRdom, hRmem⟩ :=
    aux_aux_macro_moment_bank_reference hd M H hH (closedCube z r hr) (2 * Pexp) hQ1
  exact aux_aux_macro_moment_bank_assemble_bd hd t1 k ps Pexp hP1 hpsP M Sreg H z r hr hr1
    Lmac hLmeas _
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top) hX hLpre
    hRmeas hRdom hRmem Kco hKco CK hKmem hKbd Kext CL hKextmem hKextbd hBd

/-- Moments of a nonnegative constant multiple. -/
theorem aux_aux_macro_moment_bank_const_mul_moment {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (p : ℝ≥0∞) (c : ℝ) (hc : 0 ≤ c) (f : α → ℝ) (B : ℝ)
    (hf : MemLp f p μ) (hB : eLpNorm f p μ ≤ ENNReal.ofReal B) :
    MemLp (fun x => c * f x) p μ ∧ eLpNorm (fun x => c * f x) p μ ≤ ENNReal.ofReal (c * B) := by
  refine ⟨hf.const_mul c, ?_⟩
  have h := eLpNorm_const_smul_le (c := c) (f := f) (p := p) (μ := μ)
  rw [Real.enorm_of_nonneg hc] at h
  have hfun : (c • f) = fun x => c * f x := by
    funext x
    rfl
  rw [hfun] at h
  refine h.trans ?_
  rw [ENNReal.ofReal_mul hc]
  exact mul_le_mul_right hB _

/-- **The working-cube response bound, almost surely** (input `hBd` of the assembly).  On the
single event of `lem_extension`'s `eq:mfd-3` for the root `(z, 1)` (one grid, origin `z`,
`β' = 5/8`, `η = 1/8`), the Dirichlet response of every `C²` datum on the working cube is at
most `C_* K_N Cφ²`, for every cutoff `N` and every side `r ≤ 1`. -/
theorem aux_aux_macro_moment_bank_hBd {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Cext : ℝ) (hCext : 0 < Cext)
    (hext : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
          ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
            K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
        (a : PositiveCoefficient (centeredCube z r hr))
        (G : SpatialCoordinates d → ℝ) (b : weakSobolevGraph (centeredCube z r hr)),
        ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)) →
        IsHolderOn (3 / 4) (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G →
        ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G →
        dirichletResponse (killedResponseSpace hP) a b ≤
          Cext * E.Lam z r hr a z r ((3 / 4 - 1 / 2) / 4) 2 * r ^ ((d : ℝ) - 2) *
            (r ^ (3 / 4 : ℝ) *
              holderSeminorm (3 / 4)
                (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (K : ℕ → BilateralField d → ℝ)
    (hae : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ (N k : ℕ) (index : Fin 1) (nidx : Fin d → ℤ), k ≤ N →
        (centeredCube (fun i => (fun _ : Fin 1 => z) index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
            ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤ centeredCube z 1 one_pos) →
        E.Lam z 1 one_pos (cutoffPositiveCoefficient M H om N z one_pos)
            (fun i => (fun _ : Fin 1 => z) index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
            ((3 : ℝ) ^ (-(k : ℤ))) ((5 / 8 - 1 / 2) / 4) 2 +
          (E.lam z 1 one_pos (cutoffPositiveCoefficient M H om N z one_pos)
            (fun i => (fun _ : Fin 1 => z) index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
            ((3 : ℝ) ^ (-(k : ℤ))) ((5 / 8 - 1 / 2) / 4) 2)⁻¹ ≤
          K N om * ((3 : ℝ) ^ (-(k : ℤ))) ^ (-(1 / 8 : ℝ))) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ (N : ℕ)
      (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
        ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
      (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
      ContDiff ℝ 2 phi →
      c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
      ∀ b : weakSobolevGraph (centeredCube z r hr),
      ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
      dirichletResponse (killedResponseSpace hP) (cutoffPositiveCoefficient M H om N z hr) b ≤
        aux_aux_macro_moment_bank_Cstar d Cext * K N om * Cphi ^ 2 := by
  filter_upwards [hae] with om hom
  intro N hP phi Cphi hphi hC b hb
  exact aux_aux_macro_moment_bank_boundary_response hd E Cext hCext hext M H om N z (K N om)
    (fun k nidx hkN hsub => hom N k 0 nidx hkN hsub) r hr hr1 hP phi Cphi hphi hC b hb



theorem aux_macro_moment_bank :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E)
    (_S : SobolevFoundationalInput d hd) (t1 : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t1 → t1 < d → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∃ (Lmac : ℕ → BilateralField d → ℕ) (Kmac : ℕ → BilateralField d → ℝ)
        (Cbound : Fin k → ℝ),
        (∀ N om, 0 ≤ Kmac N om) ∧
        (∀ i N, MemLp (Kmac N) (ENNReal.ofReal (ps i))
          (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (Kmac N) (ENNReal.ofReal (ps i))
            (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cbound i)) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N L0 : ℕ,
          ∃ L' : ℕ, L0 ≤ L' ∧
            Sreg.prefixLen (N + L') (1 - ((d : ℝ) - t1) / 4) N
              ((3 : ℝ) ^ N • z)
              (fun j => ContinuousMap.compRightContinuousMap ℝ
                (⟨fun x : SpatialCoordinates d => (3 : ℝ) ^ (-(N : ℤ)) • x,
                  continuous_const.smul continuous_id⟩ :
                  C(SpatialCoordinates d, SpatialCoordinates d))
                (om (j - (N : ℤ)))) ≤ Lmac N om) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
          ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
            0 ≤ Kf →
            AEMeasurable F
              (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
            (∀ᵐ x ∂(volume.restrict
              (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
            ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
              ContDiff ℝ 2 phi →
              c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
            ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
              ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
                  =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
              SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
              (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)) *
                sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr)
                  (u : SobolevData (centeredCube z r hr))
                  (u : SobolevData (centeredCube z r hr)) ≤
                  Kmac N om * (Kf + Cphi) ^ 2) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
          ∀ N x, x ∈ closedCube z r hr →
            (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)) * Real.exp (|H om x|) ≤ Kmac N om) := by
  intro d hd _ _ E P X S t1 k ps ht1 ht1' hps
  -- one exponent for all listed orders, doubled for Hölder aggregation
  obtain ⟨Pexp, hPdef⟩ : ∃ Pexp : ℝ, Pexp = 1 + ∑ i, ps i := ⟨_, rfl⟩
  have hsum0 : 0 ≤ ∑ i, ps i := Finset.sum_nonneg fun i _ => by linarith [hps i]
  have hP1 : 1 ≤ Pexp := by rw [hPdef]; linarith
  have hpsP : ∀ i, ps i ≤ Pexp := by
    intro i
    rw [hPdef]
    have := Finset.single_le_sum (f := ps) (fun j _ => by linarith [hps j]) (Finset.mem_univ i)
    linarith
  have hQ1 : 1 ≤ 2 * Pexp := by linarith
  have ht10 : 0 ≤ t1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  -- `eq:mfd-2` at `β = 3/4`, on every cube of side at most `1` (grid cells included)
  obtain ⟨Cext, hCext, hext⟩ := (lem_extension d hd E X S).1 (3 / 4) ⟨by norm_num, by norm_num⟩
  -- `eq:mfd-3` at `η = 1/8` and the doubled exponent, threshold fixed before the model
  obtain ⟨dE, hdE, hgrid⟩ := (lem_extension d hd E X S).2 (1 / 8) (2 * Pexp) (by norm_num) hQ1
    (5 / 8) ⟨by norm_num, by norm_num⟩
  obtain ⟨dc, hdc, hcoer⟩ := aux_lem_coercivity_compat d hd E P S
  obtain ⟨dA, hdA0, hthr⟩ := aux_aux_macro_moment_bank_threshold (d := d) t1 Pexp ht1 ht1' ht10 hP1
  refine ⟨min dA (min (dc (2 * Pexp)) dE), lt_min hdA0 (lt_min (hdc _ hQ1) hdE), ?_⟩
  intro M Rm Sreg It H hH hδ z r hr hr1
  obtain ⟨hδC, hα, hκlam⟩ := hthr M Sreg (hδ.trans (min_le_left _ _))
  obtain ⟨Kco, hKco, hKmom⟩ := hcoer M Rm H hH z r hr hr1
  obtain ⟨CK, hKmem, hKbd⟩ := hKmom (2 * Pexp) hQ1
    (hδ.trans ((min_le_right _ _).trans (min_le_left _ _)))
  -- the grid bound on the root `(z, 1)` at `β' = 5/8`: one grid, origin `z`
  obtain ⟨K, Cb, hKm, hKb, hae⟩ := hgrid M Rm H hH
    (hδ.trans ((min_le_right _ _).trans (min_le_right _ _))) z 1 one_pos 1 (fun _ => z)
  have hC0 := aux_aux_macro_moment_bank_Cstar_nonneg d Cext hCext.le
  have hmom := fun N => aux_aux_macro_moment_bank_const_mul_moment (chaosSampleLaw M).toMeasure
    (ENNReal.ofReal (2 * Pexp)) _ hC0 (K N) Cb (hKm N) (hKb N)
  exact aux_aux_macro_moment_bank_per_model_bd hd t1 ht10 k ps Pexp hP1 hpsP M Sreg H hH
    z r hr hr1 hδC hα hκlam Kco (fun N om v => ((hKco N om).1 v).2) CK hKmem hKbd
    (fun N om => aux_aux_macro_moment_bank_Cstar d Cext * K N om)
    (aux_aux_macro_moment_bank_Cstar d Cext * Cb) (fun N => (hmom N).1) (fun N => (hmom N).2)
    (aux_aux_macro_moment_bank_hBd hd E Cext hCext hext M H z r hr hr1 K hae)

end Paper
