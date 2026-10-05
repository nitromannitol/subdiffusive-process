module

public import SubdiffusiveProcess.Paper.Foundations.AuditExports.InfraredFamilyEnvelope
public import SubdiffusiveProcess.Probability.UniformProductMoments
public import SubdiffusiveProcess.Paper.cor_neumann_source

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric Filter
open SubdiffusiveProcess SubdiffusiveProcess.Paper SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff Topology

noncomputable section
namespace SubdiffusiveProcess.AuditExports

/-- `none` is the characterized limit; `some L` is the positive-layer
partial sum, with `some 0` giving zero infrared. -/
def infraredFamily {d : ℕ}
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (j : Option ℕ) : BilateralField d → C(SpatialCoordinates d, ℝ) :=
  j.elim H (fun L om => infraredPartialSum om L)

theorem infraredFamily_admissible {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : SubdiffusiveProcess.Model.GMCModel d}
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)}
    (hH : InfraredCharacterization M H) (j : Option ℕ) :
    InfraredAdmissible M (infraredFamily H j) := by
  cases j with
  | none => exact InfraredAdmissible.of_char hH
  | some L => exact InfraredAdmissible.of_trunc M L

/-- Linear exponential integrability converts to every finite positive
moment of the exponential. -/
theorem exponential_memLp
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : Ω → ℝ) (hS : Measurable S) (p : ℝ) (hp : 0 < p)
    (hI : Integrable (fun om => Real.exp (p * S om)) μ) :
    MemLp (fun om => Real.exp (S om)) (ENNReal.ofReal p) μ := by
  have heq : ∀ om, ‖Real.exp (S om)‖ ^ (ENNReal.ofReal p).toReal =
      Real.exp (p * S om) := by
    intro om
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ENNReal.toReal_ofReal hp.le,
      Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  exact (integrable_norm_rpow_iff hS.exp.aestronglyMeasurable
    ((ENNReal.ofReal_eq_zero.not).2 (not_le.mpr hp)) ENNReal.ofReal_ne_top).mp
      (by simpa only [heq] using hI)

/-- Comparing two root averages only uses the value envelope. This is
not a comparison of PDE regularity: the two-mesh argument is rerun below. -/
theorem exponential_average_compare
    {d : ℕ} (F G : C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (_hr : 0 < r)
    (A c S : ℝ) (hA : 0 ≤ A)
    (hS : ∀ x ∈ Metric.ball z r, |F x| ≤ S) :
    let b : ℝ := (volume.real (Metric.ball z r))⁻¹ *
      ∫ x in Metric.ball z r, A * Real.exp (F x + G x - c)
    let b0 : ℝ := (volume.real (Metric.ball z r))⁻¹ *
      ∫ x in Metric.ball z r, A * Real.exp (G x - c)
    Real.exp (-S) * b0 ≤ b ∧ b ≤ Real.exp S * b0 := by
  intro b b0
  have hfc : Continuous (fun x => A * Real.exp (F x + G x - c)) := by fun_prop
  have hgc : Continuous (fun x => A * Real.exp (G x - c)) := by fun_prop
  have hfI : IntegrableOn (fun x => A * Real.exp (F x + G x - c))
      (Metric.ball z r) volume :=
    (hfc.continuousOn.integrableOn_compact (isCompact_closedBall z r)).mono_set
      Metric.ball_subset_closedBall
  have hgI : IntegrableOn (fun x => A * Real.exp (G x - c))
      (Metric.ball z r) volume :=
    (hgc.continuousOn.integrableOn_compact (isCompact_closedBall z r)).mono_set
      Metric.ball_subset_closedBall
  have hcmp : ∀ x ∈ Metric.ball z r,
      Real.exp (-S) * (A * Real.exp (G x - c)) ≤
          A * Real.exp (F x + G x - c) ∧
      A * Real.exp (F x + G x - c) ≤
          Real.exp S * (A * Real.exp (G x - c)) := by
    intro x hx
    exact aux_reference_mesh_statistic_exp_compare A (F x + G x) (G x) c S hA
      (by simpa only [add_sub_cancel_right] using hS x hx)
  have hvol : 0 ≤ (volume.real (Metric.ball z r))⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
  constructor
  · have hi := setIntegral_mono_on (hgI.const_mul (Real.exp (-S))) hfI
      measurableSet_ball (fun x hx => (hcmp x hx).1)
    have hi' := mul_le_mul_of_nonneg_left hi hvol
    rw [integral_const_mul] at hi'
    simpa only [b, b0, integral_const_mul, mul_assoc, mul_left_comm, mul_comm] using hi'
  · have hi := setIntegral_mono_on hfI (hgI.const_mul (Real.exp S))
      measurableSet_ball (fun x hx => (hcmp x hx).2)
    have hi' := mul_le_mul_of_nonneg_left hi hvol
    rw [integral_const_mul] at hi'
    simpa only [b, b0, integral_const_mul, mul_assoc, mul_left_comm, mul_comm] using hi'

/-- The root averages and their inverses have one common multiplicative
bound across the infrared family. -/
theorem family_reference_compare
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Model.GMCModel d) (F : C(SpatialCoordinates d, ℝ))
    (om : BilateralField d) (N k : ℕ) (z : SpatialCoordinates d)
    (S : ℝ) (hF : ∀ x ∈ Metric.ball z ((3 : ℝ) ^ (-(k : ℤ)) / 2), |F x| ≤ S) :
    aux_rem_resolved_meshes_bref M (fun _ => F) om N k z +
        (aux_rem_resolved_meshes_bref M (fun _ => F) om N k z)⁻¹ ≤
      Real.exp S * (aux_rem_resolved_meshes_bref M 0 om N k z +
        (aux_rem_resolved_meshes_bref M 0 om N k z)⁻¹) := by
  let G : C(SpatialCoordinates d, ℝ) := ∑ j ∈ Finset.range k, om (-(j : ℤ))
  have hA : 0 ≤ SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M N :=
    div_nonneg (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M _).le
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M _).le
  have hc := exponential_average_compare F G z _ (by positivity)
    (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)
    ((k : ℝ) * SubdiffusiveProcess.Model.tauSq M.P) S hA hF
  have hG : ∀ x, G x = ∑ j ∈ Finset.range k, om (-(j : ℤ)) x := by
    intro x
    simp only [G, ContinuousMap.sum_apply]
  have hc' : Real.exp (-S) * aux_rem_resolved_meshes_bref M 0 om N k z ≤
      aux_rem_resolved_meshes_bref M (fun _ => F) om N k z ∧
      aux_rem_resolved_meshes_bref M (fun _ => F) om N k z ≤
        Real.exp S * aux_rem_resolved_meshes_bref M 0 om N k z := by
    simpa only [aux_rem_resolved_meshes_bref, hG, Pi.zero_apply,
      ContinuousMap.zero_apply, zero_add] using hc
  have hb : 0 < aux_rem_resolved_meshes_bref M (fun _ => F) om N k z :=
    aux_two_mesh_energy_bound_bpos M (fun _ => F) om N k z
  have hb0 : 0 < aux_rem_resolved_meshes_bref M 0 om N k z :=
    aux_two_mesh_energy_bound_bpos M 0 om N k z
  have hi := (inv_le_inv₀ hb (mul_pos (Real.exp_pos _) hb0)).2 hc'.1
  rw [mul_inv_rev, ← Real.exp_neg, neg_neg] at hi
  calc
    _ ≤ Real.exp S * aux_rem_resolved_meshes_bref M 0 om N k z +
        (aux_rem_resolved_meshes_bref M 0 om N k z)⁻¹ * Real.exp S :=
      add_le_add hc'.2 hi
    _ = _ := by ring


/-- A common two-mesh bank for all positive truncations, zero and the
characterized limit. Both random statistics precede the family index. -/
theorem infrared_family_macro
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Lstar Rstar t0 eta etas p q : ℝ)
    (hLstar : 10 ≤ Lstar) (hRstar_pos : 0 < Rstar)
    (hRstar_lt : Rstar < 1 / (100 * Lstar))
    (hRstar_mem : Rstar ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2))
    (ht0_low : (d : ℝ) - 1 < t0) (ht0_high : t0 < (d : ℝ))
    (heta_pos : 0 < eta) (heta_lt : eta < t0 - ((d : ℝ) - 1))
    (hetas_pos : 0 < etas) (hetas_lt : etas < (d : ℝ) + 2 - t0)
    (hp : 1 ≤ p) (hpq : p ≤ q) (hdq_eta : (d : ℝ) < q * eta) :
    ∃ delta0 Cm : ℝ, 0 < delta0 ∧ 0 < Cm ∧
      ∀ (M : SubdiffusiveProcess.Model.GMCModel d) (E : in_J d)
        (Poinc : in_poincare d hd E) (Ext : in_extension d hd E)
        (Rm : in_responses d M) (Sreg : in_6_16 d M)
        (It : in_iteration d M E Sreg)
        (hdet : @deterministic_good_scale_input d
          ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
        let Q : Opens (SpatialCoordinates d) := unitNeumannCube d
        ∃ (U V : ℕ → BilateralField d → ℝ) (Cp : ℝ), 0 ≤ Cp ∧
          (∀ N, Measurable (U N)) ∧ (∀ N, Measurable (V N)) ∧
          (∀ N om, 0 ≤ U N om) ∧ (∀ N om, 0 ≤ V N om) ∧
          (∀ N, MemLp (U N) (ENNReal.ofReal p) P) ∧
          (∀ N, MemLp (V N) (ENNReal.ofReal p) P) ∧
          (∀ N, eLpNorm (U N) (ENNReal.ofReal p) P ≤ ENNReal.ofReal Cp) ∧
          (∀ N, eLpNorm (V N) (ENNReal.ofReal p) P ≤ ENNReal.ofReal Cp) ∧
          ∀ᵐ om ∂P, ∀ j : Option ℕ, ∀ N : ℕ,
            let a : PositiveCoefficient Q := cutoffPositiveCoefficient M
              (infraredFamily H j) om N (fun _ => (1 / 2 : ℝ)) one_pos
            ∀ f : SpatialCoordinates d → ℝ,
              AEMeasurable f (volume.restrict (Q : Set (SpatialCoordinates d))) →
              ∀ Kf : ℝ, 0 ≤ Kf →
                (∀ᵐ y ∂volume.restrict (Q : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
                (∫ y in (Q : Set (SpatialCoordinates d)), f y) = 0 →
              ∀ u : meanZeroSobolevGraph Q, SolvesNeumann a f u →
              ∀ x ∈ (Q : Set (SpatialCoordinates d)), ∀ r : ℝ,
                (3 : ℝ) ^ (-(N : ℤ)) ≤ r →
                aux_rem_resolved_meshes_energy a u
                  {y | ∀ i : Fin d, |y i - x i| < r / 2} ≤
                  Cm * U N om * r ^ (t0 - eta) *
                    (aux_rem_resolved_meshes_energy a u (Q : Set (SpatialCoordinates d)) +
                      V N om * Kf ^ 2) := by
  classical
  have ht0 : 0 < t0 := by
    have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hres := aux_rem_resolved_meshes_onestep_exists d hd Lstar Rstar t0 hLstar hRstar_lt ht0
    (aux_rem_resolved_meshes_finite_onestep_holds d hd Lstar Rstar t0 hLstar ht0_low ht0_high)
  obtain ⟨Kt, Cstep, c, delta1, hKt, hCstep, hc, hdelta1, hone, hone_t⟩ := hres
  have hq1 : 1 ≤ q := hp.trans hpq
  have href0 := aux_reference_mesh_statistic_adm d 1 hd le_rfl (2 * p) q etas (by linarith) hq1 hetas_pos
  obtain ⟨qref, hpqref, hqqref, hgapref, dref, Cmom, Crate, Cosc, CV, hdref, hCmom, hCrate,
    hCosc, hCV, hdref1, hbudget, href⟩ := href0
  obtain ⟨cC, c1, c2, hcC1, -, -, hconst⟩ := aux_prop_folded_iteration_carrier_constants d hd
  have hreg := regularity_mesh_statistic d 1 le_rfl
  obtain ⟨Ccount, Cd, hCcount, hCd, hcard, -⟩ := hreg
  have hKt1 : 1 ≤ Kt := by
    have h3 : (1 : ℝ) < (3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) :=
      Real.one_lt_rpow (by norm_num) (by norm_num)
    have : 0 ≤ 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1) :=
      div_nonneg (by positivity) (by linarith)
    linarith
  have hα1 : 0 < 1 - (t0 + 2 - (d : ℝ)) / 2 := by linarith
  have haT : 1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt < 1 := by
    have : 0 < (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt := div_pos hα1 (by linarith)
    linarith
  have haThalf : 1 / 2 ≤ 1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt := by
    have h1 : (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt ≤ 1 - (t0 + 2 - (d : ℝ)) / 2 :=
      div_le_self hα1.le hKt1
    linarith
  have hr1 : 1 ≤ ((d : ℝ) + 1) * q := by
    have : (1 : ℝ) ≤ (d : ℝ) + 1 := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    nlinarith
  have hr0 : 0 < ((d : ℝ) + 1) * q := by linarith
  have hδfacts := aux_rem_resolved_meshes_delta_facts cC
    (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) (((d : ℝ) + 1) * q) c hcC1 haT hr0 hc
  rcases hδfacts with ⟨hδm, hδall⟩
  have hK1 : 1 ≤ Real.exp (c * (((1 : ℕ) : ℝ) + 26)) *
      (Real.exp (c * (cC + 1)) * (1 + cC)) := by
    have h1 : 1 ≤ Real.exp (c * (((1 : ℕ) : ℝ) + 26)) := Real.one_le_exp (by positivity)
    have h2 : 1 ≤ Real.exp (c * (cC + 1)) := Real.one_le_exp (by positivity)
    have h3 : 1 ≤ Real.exp (c * (cC + 1)) * (1 + cC) :=
      one_le_mul_of_one_le_of_one_le h2 (by linarith)
    exact one_le_mul_of_one_le_of_one_le h1 h3

  refine ⟨min dref (min delta1 (min (1 / 2) (min (1 / cC)
      (min (((1 - (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt)) / cC) ^ 2)
        ((1 - (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt)) ^ 2 /
          (2 * (((d : ℝ) + 1) * q) * c * cC)))))),
    2 ^ d + (36 * (3 * (1 + 100 * Lstar)) ^ d) ^ t0 * 3 ^ eta * 2 ^ t0 *
      (Rstar ^ (-t0) + (d : ℝ) + 1), lt_min hdref (lt_min hdelta1 hδm),
    aux_two_mesh_energy_bound_Cpos d Lstar Rstar t0 eta hLstar hRstar_pos, ?_⟩
  intro M E Poinc Ext Rm Sreg It hdet H hH hδ P Q
  let J : ℕ := 1
  let alpha : ℝ := (t0 + 2 - (d : ℝ)) / 2
  let K : Set (SpatialCoordinates d) := closure (Q : Set (SpatialCoordinates d))
  let R : ℕ → ℝ := fun k => (3 : ℝ) ^ (-(k : ℤ)) / 2
  let relabel : ℕ → BilateralField d → BilateralField d :=
    fun N omega j =>
      ContinuousMap.compRightContinuousMap ℝ
        (⟨fun x : SpatialCoordinates d => (3 : ℝ) ^ (-(N : ℤ)) • x,
          (by fun_prop)⟩ :
          C(SpatialCoordinates d, SpatialCoordinates d))
        (omega (j - (N : ℤ)))
  let Grid : ℕ → Type :=
    fun n => Fin d → Fin (3 ^ (n + J) + 1)
  let Cat : ℕ → Type :=
    fun n =>
      (Fin d → Fin (3 ^ (n + J) + 1)) ×
        ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))
  let ygrid : (n : ℕ) → Grid n → SpatialCoordinates d :=
    fun n a i => (a i : ℝ) * (3 : ℝ) ^ (-(((n + J : ℕ) : ℤ)))
  let active : (n : ℕ) → Cat n → Fin (d + 1) → Set (Fin d) :=
    fun n pi i => {a : Fin d | (pi.2.2.symm a).val < i.val}
  let center : SpatialCoordinates d → Set (Fin d) → SpatialCoordinates d :=
    fun y I a => if a ∈ I then (if y a ≤ 1 / 2 then 0 else 1) else y a
  let k : (n : ℕ) → Cat n → Fin (d + 1) → ℕ :=
    fun n pi i => (pi.2.1 i).val
  let allowance : (N n : ℕ) → Cat n → Fin (d + 1) → BilateralField d → ℝ :=
    fun N n pi i omega =>
      if k n pi i ≤ N then
        (It.prefixLen
            ((3 : ℝ) ^ (N : ℤ) • center (ygrid n pi.1) (active n pi i))
            (1 - (1 - alpha) / Kt) (N - k n pi i + J) (relabel N omega) : ℝ) +
          (J : ℝ) + (It.k : ℝ) + 5
      else 0
  let Z : (N n : ℕ) → Cat n → BilateralField d → ℝ :=
    fun N n pi omega =>
      Cstep ^ (d + 1) *
        Real.exp (c * ∑ i : Fin (d + 1), allowance N n pi i omega)
  have hδref : M.delta ≤ dref := hδ.trans (min_le_left _ _)
  have hδ1 : M.delta ≤ delta1 := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδm' := hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hδf := hδall M.delta hδpos hδm'
  rcases hδf with ⟨hdC, haTr, hrate⟩
  have hCeq : It.C = cC := (hconst E M Sreg It).1
  have hαT : (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) ∈ It.alphaRange := by
    rw [It.alphaRange_eq, hCeq]
    exact ⟨haThalf, haTr⟩
  have hδIt : M.delta ≤ It.C⁻¹ := by rw [hCeq]; exact hdC
  have hR := href M Rm 0 (InfraredAdmissible.zero M) hδref
  rcases hR with ⟨-, -, hmesh, hmom, -, V0, hV0m, hV00, hV0mem, hV0norm, hV0ae⟩
  have hKsub : K ⊆ {x : SpatialCoordinates d | ∀ i, 0 ≤ x i ∧ x i ≤ 1} :=
    aux_rem_resolved_meshes_closure_subset d
  have hBmom : ∀ (N n : ℕ) (pi : Cat n) (i : Fin (d + 1)),
      MemLp (fun om => Real.exp (c * allowance N n pi i om))
        (ENNReal.ofReal (((d : ℝ) + 1) * q)) P ∧
      eLpNorm (fun om => Real.exp (c * allowance N n pi i om))
        (ENNReal.ofReal (((d : ℝ) + 1) * q)) P ≤
        ENNReal.ofReal (Real.exp (c * (((1 : ℕ) : ℝ) + 26)) *
          (Real.exp (c * (cC + 1)) * (1 + cC))) :=
    fun N n pi i => aux_rem_resolved_meshes_allowance_moment It cC hCeq hcC1 _ hαT hδIt c
      (((d : ℝ) + 1) * q) hc hr1 hrate 1
      ((3 : ℝ) ^ (N : ℤ) • center (ygrid n pi.1) (active n pi i)) N (k n pi i)
  have hB0 : ∀ (N n : ℕ) (pi : Cat n) (i : Fin (d + 1)) (om : BilateralField d),
      0 ≤ allowance N n pi i om := by
    intro N n pi i om
    simp only [allowance]
    split_ifs <;> positivity
  have hU := aux_rem_resolved_meshes_regularity d 1 P p q eta hp hpq heta_pos hdq_eta Cstep c
    (Real.exp (c * (((1 : ℕ) : ℝ) + 26)) * (Real.exp (c * (cC + 1)) * (1 + cC)))
    hCstep hc.le hK1 (fun N n pi i om => allowance N n pi i om) hB0
    (fun N n pi i => (hBmom N n pi i).1) (fun N n pi i => (hBmom N n pi i).2)
  rcases hU with ⟨U, hUm, hU0, hUmem, hUnorm, hUae, hRb⟩

  let zenv : SpatialCoordinates d := fun _ => (1 / 2 : ℝ)
  let Kenv : Compacts (SpatialCoordinates d) := closedCube zenv 4 (by norm_num)
  obtain ⟨A, -, henv⟩ := infrared_family_envelope hd zenv 4 (by norm_num)
  obtain ⟨S, hSm, hS0, hSae, -, hSexp⟩ := henv M H hH
  have hExp : MemLp (fun om => Real.exp (S om)) (ENNReal.ofReal (2 * p)) P :=
    exponential_memLp P S hSm (2 * p) (by linarith) (hSexp (2 * p) (by linarith)).1
  let V : ℕ → BilateralField d → ℝ := fun N om => Real.exp (S om) * V0 N om
  let CE : ℝ := (eLpNorm (fun om => Real.exp (S om)) (ENNReal.ofReal (2 * p)) P).toReal
  have hCE : eLpNorm (fun om => Real.exp (S om)) (ENNReal.ofReal (2 * p)) P =
      ENNReal.ofReal CE := (ENNReal.ofReal_toReal hExp.eLpNorm_ne_top).symm
  have hVmem : ∀ N, MemLp (V N) (ENNReal.ofReal p) P := by
    intro N
    have hb := aux_rem_resolved_microscopic_product_lq_bound P p (2 * p) (by linarith) le_rfl
      (fun om => Real.exp (S om)) (V0 N) hExp (hV0mem N)
    exact lt_of_le_of_lt (hb.trans (mul_le_mul' hCE.le (hV0norm N)))
        (by simp only [ENNReal.mul_lt_top, ENNReal.ofReal_lt_top])
  have hVnorm : ∀ N, eLpNorm (V N) (ENNReal.ofReal p) P ≤ ENNReal.ofReal (CE * CV) := by
    intro N
    calc
      _ ≤ eLpNorm (fun om => Real.exp (S om)) (ENNReal.ofReal (2 * p)) P *
          eLpNorm (V0 N) (ENNReal.ofReal (2 * p)) P :=
        aux_rem_resolved_microscopic_product_lq_bound P p (2 * p) (by linarith) le_rfl
          (fun om => Real.exp (S om)) (V0 N) hExp (hV0mem N)
      _ ≤ ENNReal.ofReal CE * ENNReal.ofReal CV := mul_le_mul' hCE.le (hV0norm N)
      _ = _ := (ENNReal.ofReal_mul ENNReal.toReal_nonneg).symm
  let Cp : ℝ := max 0 (max
    (aux_rem_resolved_meshes_Rbound d 1 eta q Cstep
      (Real.exp (c * (((1 : ℕ) : ℝ) + 26)) * (Real.exp (c * (cC + 1)) * (1 + cC)))).toReal
    (CE * CV))
  refine ⟨U, V, Cp, le_max_left _ _, hUm, (fun N => hSm.exp.mul (hV0m N)), hU0,
    (fun N om => mul_nonneg (Real.exp_pos _).le (hV00 N om)), hUmem, hVmem, ?_, ?_, ?_⟩
  · intro N
    exact (hUnorm N).trans ((le_of_eq (ENNReal.ofReal_toReal hRb).symm).trans (ENNReal.ofReal_le_ofReal
      ((le_max_left _ _).trans (le_max_right _ _))))
  · intro N
    exact (hVnorm N).trans (ENNReal.ofReal_le_ofReal
      ((le_max_right _ _).trans (le_max_right _ _)))
  · filter_upwards [hUae, hV0ae, hSae,
      aux_rem_resolved_meshes_physical_cutoff_bridge_unitNeumannCube d M Sreg H hH,
      hH.2] with om hUlub hVlub hSω hphys hlim
    intro j N a f hf Kf hKf hfb hf0 u hu x hx r hr
    have hFnorm : ‖restrictC Kenv (infraredFamily H j om)‖ ≤ S om := by
      cases j with
      | none => exact hSω.1.1
      | some L => exact (hSω.2 L).1
    have hVcore : ∀ k' : ℕ, k' ≤ N → ∀ z : SpatialCoordinates d,
        (∀ i, 0 ≤ z i ∧ z i ≤ 1) →
        aux_rem_resolved_meshes_bref M (infraredFamily H j) om N k' z +
          (aux_rem_resolved_meshes_bref M (infraredFamily H j) om N k' z)⁻¹ ≤
          V N om * ((3 : ℝ) ^ (-(k' : ℤ)) / 2) ^ (-etas) := by
      intro k' hk' z hz
      have hc := family_reference_compare M (infraredFamily H j om) om N k' z (S om) ?_
      · exact hc.trans (by
          have hv := mul_le_mul_of_nonneg_left ((hVlub N).2 k' hk' z hz)
            (Real.exp_pos (S om)).le
          simpa only [V, aux_rem_resolved_meshes_bref, mul_assoc] using hv)
      · intro y hy
        have hzc : dist z zenv ≤ 1 / 2 := by
          rw [dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          intro i
          rw [Real.dist_eq, abs_le]
          dsimp [zenv]
          constructor <;> linarith [(hz i).1, (hz i).2]
        have hry : (3 : ℝ) ^ (-(k' : ℤ)) / 2 ≤ 1 / 2 := by
          linarith [SubdiffusiveProcess.three_zpow_neg_le_one k']
        have hyK : y ∈ (Kenv : Set (SpatialCoordinates d)) := by
          change dist y zenv ≤ 4 / 2
          have ht := dist_triangle y z zenv
          have hyz := Metric.mem_ball.mp hy
          linarith
        have hv := ContinuousMap.norm_coe_le_norm (restrictC Kenv (infraredFamily H j om)) ⟨y, hyK⟩
        change ‖infraredFamily H j om y‖ ≤ ‖restrictC Kenv (infraredFamily H j om)‖ at hv
        rw [Real.norm_eq_abs] at hv
        exact hv.trans hFnorm
    have hsum : ∀ (n : ℕ) (g : Fin d → Fin (3 ^ (n + 1) + 1))
        (dep : Fin (d + 1) → Fin (n + 1 + 1)) (σ : Equiv.Perm (Fin d)),
        (∑ j : Fin (d + 1), aux_rem_resolved_meshes_B
          (fun z m => It.prefixLen z (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) m
            (aux_rem_resolved_meshes_relabel N om)) N 1 It.k
          (fun i => ((g i : ℕ) : ℝ) * (3 : ℝ) ^ (-(((n + 1 : ℕ) : ℤ))))
          (Finset.univ.filter (fun i : Fin d => (σ.symm i).val < j.val)) (dep j).val) =
        ∑ j : Fin (d + 1), allowance N n (g, (dep, σ)) j om := by
      intro n g dep σ
      apply Finset.sum_congr rfl
      intro j _
      simp only [aux_rem_resolved_meshes_B, allowance, k, center, ygrid, active, relabel, alpha,
        aux_rem_resolved_meshes_center_filter]
      rfl
    have hUcore : ∀ (n : ℕ) (g : Fin d → Fin (3 ^ (n + 1) + 1))
        (dep : Fin (d + 1) → Fin (n + 1 + 1)) (σ : Equiv.Perm (Fin d)),
        (3 : ℝ) ^ (-eta * (n : ℝ)) * (Cstep ^ (d + 1) * Real.exp (c * ∑ j : Fin (d + 1),
          aux_rem_resolved_meshes_B
            (fun z m => It.prefixLen z (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) m
              (aux_rem_resolved_meshes_relabel N om)) N 1 It.k
            (fun i => ((g i : ℕ) : ℝ) * (3 : ℝ) ^ (-(((n + 1 : ℕ) : ℤ))))
            (Finset.univ.filter (fun i : Fin d => (σ.symm i).val < j.val)) (dep j).val)) ≤
          U N om := by
      intro n g dep σ
      rw [hsum n g dep σ]
      exact (hUlub N).1 ⟨n, (g, (dep, σ)), rfl⟩
    refine aux_rem_resolved_meshes_energy_app d hd Lstar Rstar t0 eta etas hLstar hRstar_pos
      hRstar_lt hRstar_mem ht0_low ht0_high heta_pos heta_lt hetas_pos hetas_lt 1 le_rfl Cstep c
      hCstep hc.le M (infraredFamily H j) om N a u Kf
      (fun z m => It.prefixLen z (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) m
        (aux_rem_resolved_meshes_relabel N om)) It.k ?_
      (U N om) hUcore (V N om) hVcore x hx r hr
    cases j with
    | none =>
      exact hone M E Poinc Ext Sreg It hdet H hδ1 om hlim N (hphys N)
        f hf Kf hKf hfb hf0 u hu
    | some L =>
      exact hone_t M E Poinc Ext Sreg It hdet L hδ1 om N
        f hf Kf hKf hfb hf0 u hu

/-- Separating the common ultraviolet coefficient from its infrared factor. -/
theorem cutoff_infrared_factor {d : ℕ}
    (M : SubdiffusiveProcess.Model.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d) (N : ℕ) (x : SpatialCoordinates d) :
    cutoffCoefficient M H om N x =
      Real.exp (H om x) * cutoffCoefficient M 0 om N x := by
  simp only [cutoffCoefficient, cutoffPotential, Pi.zero_apply, ContinuousMap.zero_apply,
    zero_add]
  rw [show H om x + (∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x) -
      (N + 1 : ℝ) * SubdiffusiveProcess.Model.tauSq M.P = H om x +
        ((∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x) -
          (N + 1 : ℝ) * SubdiffusiveProcess.Model.tauSq M.P) by ring, Real.exp_add]
  ring

theorem cutoff_infrared_log {d : ℕ}
    (M : SubdiffusiveProcess.Model.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d) (N : ℕ) (x : SpatialCoordinates d) :
    Real.log (cutoffCoefficient M H om N x) =
      H om x + Real.log (cutoffCoefficient M 0 om N x) := by
  have hc : 0 < cutoffCoefficient M 0 om N x := by
    unfold cutoffCoefficient
    exact mul_pos (inv_pos.mpr (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _)
  rw [cutoff_infrared_factor, Real.log_mul (Real.exp_pos _).ne' hc.ne', Real.log_exp]

/-- A common microscopic coefficient bank. The growth rate is selected
before the model, and the bank and all moment bounds before the family index. -/
theorem infrared_family_extremes
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ Cd cd : ℝ, 0 < Cd ∧ 0 < cd ∧
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (p : ℝ), 1 ≤ p →
        ∃ Cp : ℝ, 0 < Cp ∧
          ∀ (M : SubdiffusiveProcess.Model.GMCModel d)
            (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
            InfraredCharacterization M H → M.delta ≤ cd / (2 * p) →
            ∃ (D mlow mhigh : ℕ → BilateralField d → ℝ) (C : ℝ),
              0 ≤ C ∧ (∀ N om, 0 ≤ D N om) ∧
              (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ j : Option ℕ, ∀ N,
                (∀ x y, x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
                  y ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
                  |Real.log (cutoffCoefficient M (infraredFamily H j) om N x) -
                    Real.log (cutoffCoefficient M (infraredFamily H j) om N y)| ≤
                    D N om * (3 : ℝ) ^ N * dist x y) ∧
                (0 < mlow N om ∧ ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
                  mlow N om ≤ cutoffCoefficient M (infraredFamily H j) om N x ∧
                    cutoffCoefficient M (infraredFamily H j) om N x ≤ mhigh N om)) ∧
              (∀ N, MemLp (D N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) ∧
              (∀ N, MemLp (fun om => mhigh N om + (mlow N om)⁻¹)
                (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) ∧
              (∀ N, eLpNorm (D N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
                ENNReal.ofReal (C * Real.sqrt (1 + (N : ℝ)))) ∧
              (∀ N, eLpNorm (fun om => mhigh N om + (mlow N om)⁻¹)
                (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
                ENNReal.ofReal (C * Real.exp ((Cd * M.delta + Cp * M.delta ^ 2) * N))) := by
  classical
  obtain ⟨Cd, cd, hCd, hcd, hX⟩ := aux_lem_extremes_upper d hd
  refine ⟨Cd, cd, hCd, hcd, ?_⟩
  intro z r hr p hp
  obtain ⟨Cp, hCp, hXM⟩ := hX z r hr (2 * p) (by linarith)
  refine ⟨Cp, hCp, ?_⟩
  intro M H hH hδ
  let μ : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  obtain ⟨D0, m0, M0, hD00, hXae, hD0mem, hM0mem, hD0norm, hM0norm⟩ :=
    hXM M 0 (InfraredAdmissible.zero M) hδ
  obtain ⟨A, -, henv⟩ := infrared_family_envelope hd z r hr
  obtain ⟨S, hSm, hS0, hSae, -, hSE⟩ := henv M H hH
  have hE2 : MemLp (fun om => Real.exp (S om)) (ENNReal.ofReal (2 * p)) μ :=
    exponential_memLp μ S hSm (2 * p) (by linarith) (hSE (2 * p) (by linarith)).1
  have hEp : MemLp (fun om => Real.exp (S om)) (ENNReal.ofReal p) μ :=
    hE2.mono_exponent (ENNReal.ofReal_le_ofReal (by linarith))
  have hSp : MemLp S (ENNReal.ofReal p) μ :=
    hEp.mono' hSm.aestronglyMeasurable (Filter.Eventually.of_forall fun om => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hS0 om)]
      linarith [Real.add_one_le_exp (S om)])
  let CE : ℝ := (eLpNorm (fun om => Real.exp (S om)) (ENNReal.ofReal (2 * p)) μ).toReal
  let CS : ℝ := (eLpNorm S (ENNReal.ofReal p) μ).toReal
  have hCE : eLpNorm (fun om => Real.exp (S om)) (ENNReal.ofReal (2 * p)) μ =
      ENNReal.ofReal CE := (ENNReal.ofReal_toReal hE2.eLpNorm_ne_top).symm
  have hCS : eLpNorm S (ENNReal.ofReal p) μ = ENNReal.ofReal CS :=
    (ENNReal.ofReal_toReal hSp.eLpNorm_ne_top).symm
  let D : ℕ → BilateralField d → ℝ := fun N om => D0 N om + S om
  let mlow : ℕ → BilateralField d → ℝ := fun N om => Real.exp (-S om) * m0 N om
  let mhigh : ℕ → BilateralField d → ℝ := fun N om => Real.exp (S om) * M0 N om
  have hmenv : ∀ N, (fun om => mhigh N om + (mlow N om)⁻¹) =
      fun om => Real.exp (S om) * (M0 N om + (m0 N om)⁻¹) := by
    intro N
    funext om
    simp only [mhigh, mlow, mul_inv_rev, Real.exp_neg, inv_inv]
    ring
  have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  have hDp : ∀ N, MemLp (D N) (ENNReal.ofReal p) μ := fun N =>
    (hD0mem N).mono_exponent (ENNReal.ofReal_le_ofReal (by linarith)) |>.add hSp
  have hDb : ∀ N, eLpNorm (D N) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal ((Cp + CS) * Real.sqrt (1 + (N : ℝ))) := by
    intro N
    have hsqrt : 1 ≤ Real.sqrt (1 + (N : ℝ)) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      norm_num
    calc
      _ ≤ eLpNorm (D0 N) (ENNReal.ofReal p) μ + eLpNorm S (ENNReal.ofReal p) μ :=
        eLpNorm_add_le hpE
      _ ≤ ENNReal.ofReal (Cp * Real.sqrt (1 + (N : ℝ))) + ENNReal.ofReal CS :=
        add_le_add ((eLpNorm_le_eLpNorm_of_exponent_le
          (ENNReal.ofReal_le_ofReal (show p ≤ 2 * p by linarith))).trans (hD0norm N)) hCS.le
      _ = ENNReal.ofReal (Cp * Real.sqrt (1 + (N : ℝ)) + CS) :=
        (ENNReal.ofReal_add (by positivity) ENNReal.toReal_nonneg).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by
        nlinarith [show 0 ≤ CS from ENNReal.toReal_nonneg])
  have hMb : ∀ N, eLpNorm (fun om => mhigh N om + (mlow N om)⁻¹)
      (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (CE * Cp * Real.exp ((Cd * M.delta + Cp * M.delta ^ 2) * N)) := by
    intro N
    rw [hmenv N]
    calc
      _ ≤ eLpNorm (fun om => Real.exp (S om)) (ENNReal.ofReal (2 * p)) μ *
          eLpNorm (fun om => M0 N om + (m0 N om)⁻¹) (ENNReal.ofReal (2 * p)) μ :=
        aux_rem_resolved_microscopic_product_lq_bound μ p (2 * p) (by linarith) le_rfl
          (fun om => Real.exp (S om)) (fun om => M0 N om + (m0 N om)⁻¹) hE2 (hM0mem N)
      _ ≤ ENNReal.ofReal CE *
          ENNReal.ofReal (Cp * Real.exp ((Cd * M.delta + Cp * M.delta ^ 2) * N)) :=
        mul_le_mul' hCE.le (hM0norm N)
      _ = _ := by rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg]; congr 1; ring
  let C : ℝ := max (Cp + CS) (CE * Cp)
  refine ⟨D, mlow, mhigh, C, (by dsimp [C, CS]; positivity),
    (fun N om => add_nonneg (hD00 N om) (hS0 om)), ?_, hDp,
    (fun N => lt_of_le_of_lt (hMb N) ENNReal.ofReal_lt_top), ?_, ?_⟩
  · filter_upwards [hXae, hSae] with om hXω hSω
    intro j N
    have hFnorm : ‖restrictC (closedCube z r hr) (infraredFamily H j om)‖ ≤ S om := by
      cases j with
      | none => exact hSω.1.1
      | some L => exact (hSω.2 L).1
    have hFLip : ∀ x y : closedCube z r hr,
        |infraredFamily H j om x - infraredFamily H j om y| ≤ S om * dist x y := by
      cases j with
      | none => exact hSω.1.2
      | some L => exact (hSω.2 L).2
    have hFval : ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
        |infraredFamily H j om x| ≤ S om := by
      intro x hx
      have hv := ContinuousMap.norm_coe_le_norm
        (restrictC (closedCube z r hr) (infraredFamily H j om)) ⟨x, hx⟩
      change ‖infraredFamily H j om x‖ ≤ _ at hv
      rw [Real.norm_eq_abs] at hv
      exact hv.trans hFnorm
    refine ⟨?_, mul_pos (Real.exp_pos _) (hXω N).2.1, ?_⟩
    · intro x y hx hy
      rw [cutoff_infrared_log M (infraredFamily H j) om N x,
        cutoff_infrared_log M (infraredFamily H j) om N y]
      calc
        _ = |(infraredFamily H j om x - infraredFamily H j om y) +
              (Real.log (cutoffCoefficient M 0 om N x) -
                Real.log (cutoffCoefficient M 0 om N y))| := by congr 1; ring
        _ ≤ |infraredFamily H j om x - infraredFamily H j om y| +
            |Real.log (cutoffCoefficient M 0 om N x) -
              Real.log (cutoffCoefficient M 0 om N y)| := abs_add_le _ _
        _ ≤ S om * dist x y + D0 N om * (3 : ℝ) ^ N * dist x y :=
          add_le_add (hFLip ⟨x, hx⟩ ⟨y, hy⟩) ((hXω N).1 x y hx hy)
        _ ≤ _ := by
          have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ N := one_le_pow₀ (by norm_num)
          dsimp [D]
          calc
            _ ≤ S om * (3 : ℝ) ^ N * dist x y + D0 N om * (3 : ℝ) ^ N * dist x y := by
              have hm := mul_le_mul_of_nonneg_right h3 (mul_nonneg (hS0 om) (dist_nonneg (x := x) (y := y)))
              nlinarith
            _ = _ := by ring
    · intro x hx
      have hcp : 0 ≤ cutoffCoefficient M 0 om N x := by
        unfold cutoffCoefficient
        exact mul_nonneg (inv_nonneg.mpr (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N).le)
          (Real.exp_pos _).le
      rw [cutoff_infrared_factor]
      constructor
      · calc
          mlow N om ≤ Real.exp (-S om) * cutoffCoefficient M 0 om N x :=
            mul_le_mul_of_nonneg_left ((hXω N).2.2 x hx).1 (Real.exp_pos _).le
          _ ≤ Real.exp (infraredFamily H j om x) * cutoffCoefficient M 0 om N x := by
            gcongr
            exact (abs_le.mp (hFval x hx)).1
      · calc
          _ ≤ Real.exp (S om) * cutoffCoefficient M 0 om N x := by
            gcongr
            exact (abs_le.mp (hFval x hx)).2
          _ ≤ mhigh N om :=
            mul_le_mul_of_nonneg_left ((hXω N).2.2 x hx).2 (Real.exp_pos _).le
  · intro N
    exact (hDb N).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (le_max_left _ _) (Real.sqrt_nonneg _)))
  · intro N
    exact (hMb N).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (le_max_right _ _) (Real.exp_pos _).le))

/-- The matched microscopic and macroscopic estimates assembled into one
common energy bank at every radius and every infrared convention. -/
theorem infrared_family_resolved :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (t : ℝ) (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t → t < (d : ℝ) →
    (∀ i : Fin k, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (_Rm : in_responses d M) (Sreg : in_6_16 d M)
      (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
    let Q : Opens (SpatialCoordinates d) := unitNeumannCube d
    let a : Option ℕ → ℕ → BilateralField d → PositiveCoefficient Q :=
      fun j N omega => cutoffPositiveCoefficient M (infraredFamily H j) omega N
        (fun _ : Fin d => (1 / 2 : ℝ)) one_pos
    ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
      (∀ N omega, 0 ≤ K N omega) ∧
      (∀ i N,
        MemLp (K N) (ENNReal.ofReal (ps i))
          (chaosSampleLaw M).toMeasure) ∧
      (∀ i N,
        eLpNorm (K N) (ENNReal.ofReal (ps i))
          (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cbound i)) ∧
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ j : Option ℕ, ∀ N : ℕ,
          ∀ f : SpatialCoordinates d → ℝ,
            AEMeasurable f (volume.restrict (Q : Set (SpatialCoordinates d))) →
          ∀ Kf : ℝ, 0 ≤ Kf →
            (∀ᵐ y ∂volume.restrict (Q : Set (SpatialCoordinates d)),
              |f y| ≤ Kf) →
            (∫ y in (Q : Set (SpatialCoordinates d)), f y) = 0 →
          ∀ u : meanZeroSobolevGraph Q,
            SolvesNeumann (a j N omega) f u →
          ∀ x : SpatialCoordinates d, x ∈ (Q : Set (SpatialCoordinates d)) →
          ∀ r : ℝ, 0 < r → r ≤ 1 →
            localGradientEnergy (a j N omega)
              (s := Metric.ball x r ∩ (Q : Set (SpatialCoordinates d)))
              (isOpen_ball.measurableSet.inter Q.isOpen.measurableSet)
              (sobolevGradient (u : SobolevData Q)) ≤
                K N omega *
                  (sobolevCoefficientForm (a j N omega)
                    (u : SobolevData Q) (u : SobolevData Q) + Kf ^ 2) * r ^ t := by
  intro d hd _ _ E _P _X _W D t k ps ht_low ht_high hps
  have hdt : 0 < (d : ℝ) - t := sub_pos.mpr ht_high
  obtain ⟨t1, t0, pmax, ht_nn, htt1, ht1d, ht0_low, ht0_high, heta_pos, heta_lt,
    hetas_pos, hetas_lt, hpmax, hps_le, hq1, hpq, hqmesh_p, hqmesh_q, hqmesh_eta⟩ :=
    aux_rem_resolved_parameters d hd t k ps ht_low ht_high
  -- geometric root radius
  have hRpos : (0 : ℝ) < (3 : ℝ) ^ (-7 : ℤ) / 2 := by positivity
  have hRlt : (3 : ℝ) ^ (-7 : ℤ) / 2 < 1 / (100 * 10) := by norm_num
  have hRmem : (3 : ℝ) ^ (-7 : ℤ) / 2 ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2) := ⟨-7, rfl⟩
  -- the large-scale common package
  have hM := infrared_family_macro d hd 10 ((3 : ℝ) ^ (-7 : ℤ) / 2) t0 (t0 - t1)
    (((d : ℝ) + 2 - t0) / 2) (2 * (2 * pmax * max 1 t))
    (max (2 * (2 * pmax * max 1 t)) (((d : ℝ) + 1) / (t0 - t1))) (by norm_num) hRpos hRlt hRmem
    ht0_low ht0_high heta_pos heta_lt hetas_pos hetas_lt hqmesh_p hqmesh_q hqmesh_eta
  rcases hM with ⟨delta0m, Cm, hdelta0m, hCm, hmesh⟩
  -- the microscopic matched range
  have hp1 : (2 : ℝ) ≤ 2 + 4 * (d : ℝ) / ((d : ℝ) - t) := by
    have : 0 ≤ 4 * (d : ℝ) / ((d : ℝ) - t) := by positivity
    linarith
  have htp : t < (d : ℝ) - 2 * (d : ℝ) / (2 + 4 * (d : ℝ) / ((d : ℝ) - t)) := by
    have hp1pos : 0 < 2 + 4 * (d : ℝ) / ((d : ℝ) - t) := by linarith
    have hkey : 2 * (d : ℝ) / (2 + 4 * (d : ℝ) / ((d : ℝ) - t)) < ((d : ℝ) - t) / 2 := by
      rw [div_lt_iff₀ hp1pos]
      have h4 : ((d : ℝ) - t) * (4 * (d : ℝ) / ((d : ℝ) - t)) = 4 * (d : ℝ) := by
        field_simp
      nlinarith
    linarith
  have hml := aux_rem_resolved_micro_local d hd _W (2 + 4 * (d : ℝ) / ((d : ℝ) - t)) t t1 hp1
    ht_low htt1 ht1d htp
  rcases hml with ⟨Cmic, hCmic, hmicL⟩
  have hms := rem_resolved_microscopic d hd _W (2 + 4 * (d : ℝ) / ((d : ℝ) - t)) t t1 hp1
    ht_low htt1 ht1d htp
  rcases hms with ⟨_, _, _, _, _, _, hstat⟩
  -- extremes of the actual cutoff coefficient on the closed unit cube
  have hXall := infrared_family_extremes d hd
  rcases hXall with ⟨Cde, cde, hCde, hcde, hXz⟩
  have hX := hXz (fun _ => (1 / 2 : ℝ)) 1 one_pos (2 * pmax * max 1 t) hq1
  rcases hX with ⟨Cpr, hCpr, hextM⟩
  -- rate budget
  have hexr : ∃ rmax : ℝ,
      rmax = min (t1 - t) (min ((d : ℝ) + 2 - t) ((d : ℝ) - t)) * Real.log 3 := ⟨_, rfl⟩
  obtain ⟨rmax, hrmax_def⟩ := hexr
  have hrmax : 0 < rmax := by
    rw [hrmax_def]
    refine mul_pos (lt_min (by linarith) (lt_min (by linarith) hdt)) ?_
    exact Real.log_pos (by norm_num)
  have hqpos : 0 < 2 * pmax * max 1 t := by linarith
  refine ⟨min (min delta0m (cde / (2 * (2 * pmax * max 1 t))))
    (min 1 (rmax / (2 * (Cde + Cpr)))), ?_, ?_⟩
  · refine lt_min (lt_min hdelta0m (div_pos hcde (mul_pos (by norm_num) hqpos))) (lt_min one_pos ?_)
    exact div_pos hrmax (by positivity)
  intro M _Rm Sreg _It H hIR hδ Q a
  have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hδm : M.delta ≤ delta0m := hδ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδe : M.delta ≤ cde / (2 * (2 * pmax * max 1 t)) :=
    hδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδ1 : M.delta ≤ 1 := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδr : M.delta ≤ rmax / (2 * (Cde + Cpr)) :=
    hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hrate := aux_rem_resolved_rate Cde Cpr rmax M.delta hCde hCpr hrmax hδpos hδ1 hδr
  rw [hrmax_def] at hrate
  -- instantiate the large-scale package and the extremes on the same sample law
  have hmM := hmesh M E _P _X _Rm Sreg _It D H hIR hδm
  rcases hmM with ⟨U, V, Cp, hCp, _, _, hU0, hV0, hULp, hVLp, hUb, hVb, hae⟩
  have heM := hextM M H hIR hδe
  rcases heM with ⟨De, mlow, mhigh, Cpe, hCpe, hDe0, heae, hDeLp, hmLp, hDeb, hmb⟩
  have hW : ∀ N : ℕ,
      MemLp (fun om => U N om * (1 + V N om)) (ENNReal.ofReal (2 * pmax * max 1 t))
        (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om => U N om * (1 + V N om)) (ENNReal.ofReal (2 * pmax * max 1 t))
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cp * (1 + Cp)) := fun N =>
    aux_rem_resolved_UV_moment (chaosSampleLaw M).toMeasure (2 * pmax * max 1 t) Cp hq1 hCp
      (U N) (V N) (hULp N) (hVLp N) (hUb N) (hVb N)
  have hSb : ∀ N : ℕ,
      eLpNorm (fun om => ‖mhigh N om + (mlow N om)⁻¹‖ + ‖mhigh N om + (mlow N om)⁻¹‖)
        (ENNReal.ofReal (2 * pmax * max 1 t)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * Cpe *
        Real.exp ((Cde * M.delta + Cpr * M.delta ^ 2) * (N : ℝ))) := by
    intro N
    have h2 : (fun om => ‖mhigh N om + (mlow N om)⁻¹‖ + ‖mhigh N om + (mlow N om)⁻¹‖) =
        fun om => 2 * ‖mhigh N om + (mlow N om)⁻¹‖ := by
      funext om; ring
    have hm := hmb N
    calc _ = ENNReal.ofReal 2 * eLpNorm (fun om => mhigh N om + (mlow N om)⁻¹)
            (ENNReal.ofReal (2 * pmax * max 1 t)) (chaosSampleLaw M).toMeasure := by
          rw [h2, aux_rem_resolved_microscopic_nonneg_scalar_eLpNorm _ _ 2 (by norm_num),
            eLpNorm_norm _ (hmLp N).aestronglyMeasurable]
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal
            (Cpe * Real.exp ((Cde * M.delta + Cpr * M.delta ^ 2) * (N : ℝ))) := by
          gcongr
      _ = _ := by rw [← ENNReal.ofReal_mul (by norm_num), mul_assoc]
  have hstatM := hstat (BilateralField d) (chaosSampleLaw M).toMeasure pmax hpmax De
    (fun N om => ‖mhigh N om + (mlow N om)⁻¹‖) (fun N om => ‖mhigh N om + (mlow N om)⁻¹‖)
    (fun N om => U N om * (1 + V N om)) Cpe (2 * Cpe) (Cp * (1 + Cp))
    (Cde * M.delta + Cpr * M.delta ^ 2) hCpe (by positivity) (by positivity) hrate.1 hrate.2
    (fun N om => ⟨hDe0 N om, norm_nonneg _, norm_nonneg _,
      mul_nonneg (hU0 N om) (by linarith [hV0 N om])⟩)
    (fun N => ⟨hDeLp N, (hmLp N).norm, (hmLp N).norm, (hW N).1⟩)
    hDeb hSb (fun N => (hW N).2)
  rcases hstatM with ⟨B, hB0, hBN⟩
  have hA1 : 0 ≤ Cm * 2 ^ t1 := mul_nonneg hCm.le (Real.rpow_pos_of_pos (by norm_num) _).le
  have hA3 : 0 ≤ Cmic * 2 ^ t := mul_nonneg hCmic.le (Real.rpow_pos_of_pos (by norm_num) _).le
  have hA2 : 0 ≤ Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1) :=
    mul_nonneg hA3 (mul_nonneg hCm.le
      (Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (le_max_right _ _)) _).le)
  have hmom : ∀ (i : Fin k) (N : ℕ),
      MemLp (fun om => (Cm * 2 ^ t1) * (U N om * (1 + V N om)) +
        (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) *
          ((1 + De N om) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * (U N om * (1 + V N om))) +
        (Cmic * 2 ^ t) *
          (‖mhigh N om + (mlow N om)⁻¹‖ * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t)))
        (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om => (Cm * 2 ^ t1) * (U N om * (1 + V N om)) +
        (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) *
          ((1 + De N om) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * (U N om * (1 + V N om))) +
        (Cmic * 2 ^ t) *
          (‖mhigh N om + (mlow N om)⁻¹‖ * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t)))
        (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((Cm * 2 ^ t1) * (Cp * (1 + Cp)) +
        (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) * B + (Cmic * 2 ^ t) * B) := by
    intro i N
    have hBNN := hBN N
    beta_reduce at hBNN
    have hWm := (hW N).1.aestronglyMeasurable
    have hDt := (aux_rem_resolved_microscopic_one_add_power_memLp (chaosSampleLaw M).toMeasure
      pmax t hpmax ht_nn (De N) (hDe0 N) (hDeLp N)).aestronglyMeasurable
    have hT1m : AEStronglyMeasurable (fun om =>
        (1 + De N om) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * (U N om * (1 + V N om)))
        (chaosSampleLaw M).toMeasure :=
      (hDt.mul aestronglyMeasurable_const).mul hWm
    have hT2m : AEStronglyMeasurable (fun om =>
        ‖mhigh N om + (mlow N om)⁻¹‖ * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t))
        (chaosSampleLaw M).toMeasure :=
      (hmLp N).norm.aestronglyMeasurable.mul aestronglyMeasurable_const
    have hWb : eLpNorm (fun om => U N om * (1 + V N om)) (ENNReal.ofReal pmax)
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cp * (1 + Cp)) :=
      (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpq)).trans (hW N).2
    exact aux_rem_resolved_three_term_moment (chaosSampleLaw M).toMeasure pmax _ _ _
      (Cp * (1 + Cp)) B hpmax hA1 hA2 hA3 (by positivity) hB0 _ _ _ hWm hT1m hT2m hWb
      hBNN.1 hBNN.2.1 (ps i) (hps_le i)
  refine ⟨fun N om => (Cm * 2 ^ t1) * (U N om * (1 + V N om)) +
        (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) *
          ((1 + De N om) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * (U N om * (1 + V N om))) +
        (Cmic * 2 ^ t) *
          (‖mhigh N om + (mlow N om)⁻¹‖ * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t)),
    fun _ => (Cm * 2 ^ t1) * (Cp * (1 + Cp)) +
        (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) * B + (Cmic * 2 ^ t) * B, ?_,
    fun i N => (hmom i N).1, fun i N => (hmom i N).2, ?_⟩
  · intro N om
    have h1 : 0 ≤ U N om * (1 + V N om) := mul_nonneg (hU0 N om) (by linarith [hV0 N om])
    have h2 : 0 ≤ (1 + De N om) ^ t := (Real.rpow_pos_of_pos (by linarith [hDe0 N om]) _).le
    have h3 : 0 ≤ ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) :=
      (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _) _).le
    have h4 : 0 ≤ ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t) :=
      (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _) _).le
    have h5 := norm_nonneg (mhigh N om + (mlow N om)⁻¹)
    exact add_nonneg (add_nonneg (mul_nonneg hA1 h1) (mul_nonneg hA2 (mul_nonneg (mul_nonneg h2 h3) h1)))
      (mul_nonneg hA3 (mul_nonneg h5 h4))
  · filter_upwards [hae, heae] with om hω1 hω2
    intro j
    have hfirst := fun N : ℕ => aux_rem_resolved_sample d M (infraredFamily H j) om N t t1 t0 Cm Cmic
      (U N om) (V N om) (De N om) (mlow N om) (mhigh N om) (le_of_lt htt1) hCm.le hCmic
      (hU0 N om) (hV0 N om) (hDe0 N om) (hω2 j N).2.1 (hω2 j N).2.2 (hω2 j N).1
      (hmicL ((3 : ℝ) ^ (-(N : ℝ))) (Real.rpow_pos_of_pos (by norm_num) _)
        (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by simp)))
      (hω1 j N)
    exact hfirst

/-- Global coercivity is compared using the zero-infrared Poincaré estimate. -/
theorem neumann_global_energy_compare {d : ℕ} (hd : 2 ≤ d) (E : in_J d)
    (P : in_poincare d hd E)
    (a : PositiveCoefficient (unitNeumannCube d))
    (a0 : PositiveCoefficient (unitNeumannCube d)) (c : ℝ) (hc : 0 ≤ c)
    (hab : ∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      a0.val x ≤ c * a.val x)
    (F : SpatialCoordinates d → ℝ)
    (hF : AEMeasurable F (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))))
    (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hFb : ∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))), |F x| ≤ Kf)
    (v : meanZeroSobolevGraph (unitNeumannCube d)) (hsol : SolvesNeumann a F v) :
    sobolevCoefficientForm a (v : SobolevData (unitNeumannCube d))
        (v : SobolevData (unitNeumannCube d)) ≤
      Kf ^ 2 * P.C ^ 2 * c *
        (E.lam (fun _ => (1 / 2 : ℝ)) 1 one_pos a0 (fun _ => (1 / 2 : ℝ)) 1 1 1)⁻¹ := by
  set lam : ℝ := E.lam (fun _ => (1 / 2 : ℝ)) 1 one_pos a0 (fun _ => (1 / 2 : ℝ)) 1 1 1
    with hlamdef
  have hlam : 0 < lam := E.lam_pos _ _ _ _ _ _ _ _
  set En : ℝ := sobolevCoefficientForm a (v : SobolevData (unitNeumannCube d))
    (v : SobolevData (unitNeumannCube d)) with hEn
  have hEn0 : 0 ≤ En := sobolevCoefficientForm_nonneg a _
  have hvw : (v : SobolevData (unitNeumannCube d)) ∈ weakSobolevGraph (unitNeumannCube d) :=
    (inf_le_left : meanZeroSobolevGraph (unitNeumannCube d) ≤
      weakSobolevGraph (unitNeumannCube d)) v.property
  have hid : En = ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
      F x * (v : SobolevData (unitNeumannCube d)).1 x :=
    hsol ⟨(v : SobolevData (unitNeumannCube d)), hvw⟩
  have hpair := aux_cor_neumann_source_pairing_ae F Kf hKf hF hFb
    (v : SobolevData (unitNeumannCube d)).1
  have hvol : volume.real (unitNeumannCube d : Set (SpatialCoordinates d)) = 1 :=
    centeredCube_one_volume_real (fun _ => (1 / 2 : ℝ)) one_pos
  have hpoin := P.poincare_meanZero (fun _ => (1 / 2 : ℝ)) one_pos a0 v
  have hcompare := localGradientEnergy_le_mul a0 a c hab
    (unitNeumannCube d).isOpen.measurableSet (sobolevGradient (v : SobolevData (unitNeumannCube d)))
  rw [localGradientEnergy_domain_eq_sobolevCoefficientForm a0,
    localGradientEnergy_domain_eq_sobolevCoefficientForm a] at hcompare
  have hnorm : normalizedEnergyNorm a0 (unitNeumannCube d).isOpen.measurableSet
      (sobolevGradient (v : SobolevData (unitNeumannCube d))) = Real.sqrt (sobolevCoefficientForm a0 v v) := by
    unfold normalizedEnergyNorm
    rw [hvol, div_one]
    congr 1
    exact localGradientEnergy_domain_eq_sobolevCoefficientForm a0 (v : SobolevData (unitNeumannCube d))
  rw [centeredCube_one_volume_real, Real.sqrt_one, div_one] at hpoin
  have hpoin' : ‖(v : SobolevData (unitNeumannCube d)).1‖ ≤
      P.C * lam ^ (-(1 / 2) : ℝ) * Real.sqrt c * Real.sqrt En := by
    calc
      _ ≤ P.C * lam ^ (-(1 / 2) : ℝ) * Real.sqrt (sobolevCoefficientForm a0 v v) :=
        by rw [← hnorm]; exact hpoin
      _ ≤ P.C * lam ^ (-(1 / 2) : ℝ) * Real.sqrt (c * En) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcompare)
          (mul_nonneg P.C_pos.le (Real.rpow_nonneg hlam.le _))
      _ = _ := by rw [Real.sqrt_mul hc]; ring
  have hmain : En ≤ Kf * (P.C * lam ^ (-(1 / 2) : ℝ) * Real.sqrt c) * Real.sqrt En := by
    calc En ≤ Kf * ‖(v : SobolevData (unitNeumannCube d)).1‖ := by rw [hid]; exact hpair
      _ ≤ Kf * (P.C * lam ^ (-(1 / 2) : ℝ) * Real.sqrt c * Real.sqrt En) :=
          mul_le_mul_of_nonneg_left hpoin' hKf
      _ = Kf * (P.C * lam ^ (-(1 / 2) : ℝ) * Real.sqrt c) * Real.sqrt En := by ring
  have habs := aux_prop_neumann_growth_absorb En _ hEn0 hmain
  have hsq : (lam ^ (-(1 / 2) : ℝ)) ^ 2 = lam⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlam.le]
    norm_num
    exact Real.rpow_neg_one lam
  calc En ≤ (Kf * (P.C * lam ^ (-(1 / 2) : ℝ) * Real.sqrt c)) ^ 2 := habs
    _ = Kf ^ 2 * P.C ^ 2 * c * (lam ^ (-(1 / 2) : ℝ)) ^ 2 := by
      rw [show (Kf * (P.C * lam ^ (-(1 / 2) : ℝ) * Real.sqrt c)) ^ 2 =
        Kf ^ 2 * P.C ^ 2 * (Real.sqrt c) ^ 2 * (lam ^ (-(1 / 2) : ℝ)) ^ 2 by ring,
        Real.sq_sqrt hc]
    _ = Kf ^ 2 * P.C ^ 2 * c * lam⁻¹ := by rw [hsq]


/-- Coefficient comparison used only for coercivity and cell Poincaré. -/
theorem cutoff_zero_le_family
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Model.GMCModel d) (F : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d) (N : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ℝ) (hF : ‖restrictC (closedCube z r hr) (F om)‖ ≤ S) :
    ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M 0 om N z hr).val x ≤
        Real.exp S * (cutoffPositiveCoefficient M F om N z hr).val x := by
  filter_upwards [aux_prop_growth_holder_micro_campanato_coeff_ae M 0 om N z hr,
    aux_prop_growth_holder_micro_campanato_coeff_ae M F om N z hr,
    ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx0 hxF hx
  rw [hx0, hxF, cutoff_infrared_factor M F om N x]
  have hxK : x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) := by
    change dist x z ≤ r / 2
    rw [centeredCube_coe_eq_ball] at hx
    exact (Metric.mem_ball.mp hx).le
  have hv := ContinuousMap.norm_coe_le_norm (restrictC (closedCube z r hr) (F om)) ⟨x, hxK⟩
  change ‖F om x‖ ≤ _ at hv
  rw [Real.norm_eq_abs] at hv
  have hf := (abs_le.mp (hv.trans hF)).1
  have hc0 : 0 ≤ cutoffCoefficient M 0 om N x := by
    unfold cutoffCoefficient
    exact mul_nonneg (inv_nonneg.mpr (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N).le) (Real.exp_pos _).le
  calc
    _ = 1 * cutoffCoefficient M 0 om N x := by rw [one_mul]
    _ ≤ Real.exp (S + F om x) * cutoffCoefficient M 0 om N x :=
      mul_le_mul_of_nonneg_right (Real.one_le_exp (by linarith)) hc0
    _ = _ := by rw [Real.exp_add]; ring

/-- One source-independent energy bank for the whole infrared family. -/
theorem infrared_family_energy :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩) (t : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t → t < d → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ N om, 0 ≤ K N om) ∧
        (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ idx : Option ℕ, ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
          (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x) = 0 →
        ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
          SolvesNeumann
              (cutoffPositiveCoefficient M (infraredFamily H idx) om N (fun _ => (1 / 2 : ℝ)) one_pos) F v →
          ∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ unitNeumannCube d →
            0 < rad → rad ≤ 1 →
            localGradientEnergy
                (cutoffPositiveCoefficient M (infraredFamily H idx) om N (fun _ => (1 / 2 : ℝ)) one_pos)
                (s := Metric.ball x rad ∩
                  (unitNeumannCube d : Set (SpatialCoordinates d)))
                (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
                (sobolevGradient (v : SobolevData (unitNeumannCube d))) ≤
              K N om * Kf ^ 2 * rad ^ t := by
  intro d hd _ _ E P X W D t k ps htlo hthi hps
  have hps2 : ∀ i : Fin k, 1 ≤ 2 * ps i := fun i => by linarith [hps i]
  obtain ⟨δres, hδres, hres⟩ :=
    infrared_family_resolved d hd E P X W D t k (fun i => 2 * ps i) htlo hthi hps2
  obtain ⟨δlam, hδlam, hlam⟩ :=
    aux_lambda_inv_moments_adm d hd E (1 / 8 : ℝ) ⟨by norm_num, by norm_num⟩
  have hδi : ∀ i : Fin k, 0 < δlam (4 * ps i) := fun i => hδlam _ (by linarith [hps i])
  refine ⟨min δres (1 / (1 + ∑ j : Fin k, 1 / δlam (4 * ps j))),
    lt_min hδres (aux_prop_neumann_growth_delta_pos _ hδi), ?_⟩
  intro M Rm Sreg It H HI hδ
  have hδM : M.delta ≤ δres := hδ.trans (min_le_left _ _)
  have hδMi : ∀ i : Fin k, M.delta ≤ δlam (4 * ps i) := fun i =>
    (hδ.trans (min_le_right _ _)).trans (aux_prop_neumann_growth_delta_min _ hδi i)
  obtain ⟨Kres, Cres, hKres0, hKresMem, hKresBd, hae⟩ := hres M Rm Sreg It H HI hδM
  have hlamI := fun i : Fin k =>
    hlam M Rm 0 (InfraredAdmissible.zero M) (fun _ => (1 / 2 : ℝ)) 1 one_pos le_rfl (4 * ps i) (by linarith [hps i]) (hδMi i)
  choose Clam hLam0Mem hLam0Bd using hlamI
  obtain ⟨Lam0, hLam0def⟩ : ∃ Lam0 : ℕ → BilateralField d → ℝ, Lam0 = fun N om =>
      (E.lam (fun _ => (1 / 2 : ℝ)) 1 one_pos
        (cutoffPositiveCoefficient M 0 om N (fun _ => (1 / 2 : ℝ)) one_pos)
        (fun _ => (1 / 2 : ℝ)) 1 (1 / 8 : ℝ) 1)⁻¹ := ⟨_, rfl⟩
  have hLam00 : ∀ N om, 0 ≤ Lam0 N om := by
    intro N om; rw [hLam0def]
    exact (inv_pos.mpr (E.lam_pos _ _ _ _ _ _ _ _)).le
  obtain ⟨Aenv, -, henv⟩ := infrared_family_envelope hd (fun _ => (1 / 2 : ℝ)) 1 one_pos
  obtain ⟨S, hSm, -, hSae, -, hSE⟩ := henv M H HI
  have hE : ∀ i : Fin k, MemLp (fun om => Real.exp (S om))
      (ENNReal.ofReal (4 * ps i)) (chaosSampleLaw M).toMeasure := fun i =>
    exponential_memLp _ S hSm _ (by linarith [hps i]) (hSE _ (by linarith [hps i])).1
  let CE : Fin k → ℝ := fun i => (eLpNorm (fun om => Real.exp (S om))
    (ENNReal.ofReal (4 * ps i)) (chaosSampleLaw M).toMeasure).toReal
  have hCE : ∀ i, eLpNorm (fun om => Real.exp (S om)) (ENNReal.ofReal (4 * ps i))
      (chaosSampleLaw M).toMeasure = ENNReal.ofReal (CE i) := fun i =>
    (ENNReal.ofReal_toReal (hE i).eLpNorm_ne_top).symm
  let Lam : ℕ → BilateralField d → ℝ := fun N om => Real.exp (S om) * Lam0 N om
  have hLamLp : ∀ i N, MemLp (Lam N) (ENNReal.ofReal (2 * ps i)) (chaosSampleLaw M).toMeasure := by
    intro i N
    have hb := aux_rem_resolved_microscopic_product_lq_bound (chaosSampleLaw M).toMeasure
      (2 * ps i) (4 * ps i) (by linarith [hps i]) (by linarith) (fun om => Real.exp (S om))
      (Lam0 N) (hE i) (by rw [hLam0def]; exact hLam0Mem i N)
    have hb0 : eLpNorm (Lam0 N) (ENNReal.ofReal (4 * ps i))
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Clam i) := by
      rw [hLam0def]
      exact hLam0Bd i N
    exact lt_of_le_of_lt (hb.trans (mul_le_mul' (hCE i).le hb0)) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hLamBd : ∀ i N, eLpNorm (Lam N) (ENNReal.ofReal (2 * ps i)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (CE i * Clam i) := by
    intro i N
    calc
      _ ≤ eLpNorm (fun om => Real.exp (S om)) (ENNReal.ofReal (4 * ps i)) (chaosSampleLaw M).toMeasure *
          eLpNorm (Lam0 N) (ENNReal.ofReal (4 * ps i)) (chaosSampleLaw M).toMeasure :=
        aux_rem_resolved_microscopic_product_lq_bound _ (2 * ps i) (4 * ps i)
          (by linarith [hps i]) (by linarith) _ _ (hE i) (by rw [hLam0def]; exact hLam0Mem i N)
      _ ≤ ENNReal.ofReal (CE i) * ENNReal.ofReal (Clam i) :=
        mul_le_mul' (hCE i).le (by rw [hLam0def]; exact hLam0Bd i N)
      _ = _ := (ENNReal.ofReal_mul ENNReal.toReal_nonneg).symm
  have hLam0 : ∀ N om, 0 ≤ Lam N om := fun N om =>
    mul_nonneg (Real.exp_pos _).le (hLam00 N om)
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ → BilateralField d → ℝ, K = fun N om =>
      Kres N om * (1 + P.C ^ 2 * Lam N om) := ⟨_, rfl⟩
  have hK0 : ∀ N om, 0 ≤ K N om := by
    intro N om; rw [hKdef]
    exact mul_nonneg (hKres0 N om) (by have := hLam0 N om; positivity)
  have hmom := fun (i : Fin k) (N : ℕ) =>
    aux_cor_neumann_source_K_moment (chaosSampleLaw M).toMeasure (ps i) (P.C ^ 2)
      (Cres i) (CE i * Clam i) (hps i) (by positivity) (Kres N) (Lam N)
      (hKresMem i N) (hLamLp i N) (hKresBd i N) (hLamBd i N)
  refine ⟨K, fun i => max (max (Cres i) (P.C ^ 2 * (CE i * Clam i))) 0 *
      (1 + max (max (Cres i) (P.C ^ 2 * (CE i * Clam i))) 0), hK0,
    fun i N => by rw [hKdef]; exact (hmom i N).1,
    fun i N => by rw [hKdef]; exact (hmom i N).2, ?_⟩
  filter_upwards [hae, hSae] with om hom hSω
  intro idx N F Kf hKf hFm hFb hmean v hsol x rad hx hrad hrad1
  have hFnorm : ‖restrictC (closedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos)
      (infraredFamily H idx om)‖ ≤ S om := by
    cases idx with
    | none => exact hSω.1.1
    | some L => exact (hSω.2 L).1
  have hloc := hom idx N F hFm Kf hKf hFb hmean v hsol x hx rad hrad hrad1
  have hEn := neumann_global_energy_compare hd E P
    (cutoffPositiveCoefficient M (infraredFamily H idx) om N (fun _ => (1 / 2 : ℝ)) one_pos)
    (cutoffPositiveCoefficient M 0 om N (fun _ => (1 / 2 : ℝ)) one_pos)
    (Real.exp (S om)) (Real.exp_pos _).le
    (cutoff_zero_le_family M (infraredFamily H idx) om N _ 1 one_pos (S om) hFnorm)
    F hFm Kf hKf hFb v hsol
  have hlampos := E.lam_pos (fun _ => (1 / 2 : ℝ)) 1 one_pos
    (cutoffPositiveCoefficient M 0 om N (fun _ => (1 / 2 : ℝ)) one_pos)
    (fun _ => (1 / 2 : ℝ)) 1 (1 / 8 : ℝ) 1
  have hmono := E.lam_mono (fun _ => (1 / 2 : ℝ)) 1 one_pos
    (cutoffPositiveCoefficient M 0 om N (fun _ => (1 / 2 : ℝ)) one_pos)
    (fun _ => (1 / 2 : ℝ)) 1 1 (1 / 8 : ℝ) 1 (by norm_num)
  have hinv : (E.lam (fun _ => (1 / 2 : ℝ)) 1 one_pos
      (cutoffPositiveCoefficient M 0 om N (fun _ => (1 / 2 : ℝ)) one_pos)
      (fun _ => (1 / 2 : ℝ)) 1 1 1)⁻¹ ≤ Lam0 N om := by
    rw [hLam0def]
    exact inv_anti₀ hlampos hmono
  have hEn' : sobolevCoefficientForm
      (cutoffPositiveCoefficient M (infraredFamily H idx) om N (fun _ => (1 / 2 : ℝ)) one_pos) (v : SobolevData (unitNeumannCube d)) (v : SobolevData (unitNeumannCube d)) ≤
      Kf ^ 2 * P.C ^ 2 * Lam N om := by
    calc
      _ ≤ Kf ^ 2 * P.C ^ 2 * Real.exp (S om) *
          (E.lam (fun _ => (1 / 2 : ℝ)) 1 one_pos
            (cutoffPositiveCoefficient M 0 om N (fun _ => (1 / 2 : ℝ)) one_pos)
            (fun _ => (1 / 2 : ℝ)) 1 1 1)⁻¹ := hEn
      _ ≤ Kf ^ 2 * P.C ^ 2 * Real.exp (S om) * Lam0 N om := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := by dsimp [Lam]; ring
  calc
    _ ≤ Kres N om * (sobolevCoefficientForm
        (cutoffPositiveCoefficient M (infraredFamily H idx) om N (fun _ => (1 / 2 : ℝ)) one_pos) (v : SobolevData (unitNeumannCube d)) (v : SobolevData (unitNeumannCube d)) +
        Kf ^ 2) * rad ^ t := hloc
    _ ≤ Kres N om * (Kf ^ 2 * P.C ^ 2 * Lam N om + Kf ^ 2) * rad ^ t :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add hEn' le_rfl) (hKres0 N om))
        (Real.rpow_nonneg hrad.le _)
    _ = K N om * Kf ^ 2 * rad ^ t := by rw [hKdef]; ring


/-- Common Campanato decay below the wavelength, using a common coefficient floor. -/
theorem infrared_family_micro_campanato :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩) (alpha : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    0 < alpha → alpha < 1 → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∃ (Kosc : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ N om, 0 ≤ Kosc N om) ∧
        (∀ i N, MemLp (Kosc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (Kosc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ idx : Option ℕ, ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
          (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x) = 0 →
        ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
          SolvesNeumann
              (cutoffPositiveCoefficient M (infraredFamily H idx) om N (fun _ => (1 / 2 : ℝ)) one_pos) F v →
          ∀ x ∈ unitNeumannCube d, ∀ rad : ℝ, 0 < rad →
            rad ≤ (3 : ℝ) ^ (-(N : ℤ)) → rad ≤ 1 →
            ∫ y in Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
                ((v : SobolevData (unitNeumannCube d)).1 y - setAverage
                  (Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
                  (v : SobolevData (unitNeumannCube d)).1) ^ 2
                ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)) ≤
              (Kosc N om * Kf) ^ 2 * rad ^ (2 * alpha) *
                volume.real (Metric.ball x rad ∩
                  (unitNeumannCube d : Set (SpatialCoordinates d))) := by
  intro d hd _ _ E P X W D alpha k ps ha0 ha1 hps
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = (max ((d : ℝ) - 1) ((d : ℝ) - 2 + 2 * alpha) + d) / 2 :=
    ⟨_, rfl⟩
  obtain ⟨ht1, htd, he0⟩ := aux_cor_neumann_source_t1_exponent d alpha ha1
  rw [← htdef] at ht1 htd he0
  obtain ⟨e, hedef⟩ : ∃ e : ℝ, e = 2 + t - 2 * alpha - d := ⟨_, rfl⟩
  have he : 0 < e := by rw [hedef]; exact he0
  have hexp : 2 + t = 2 * alpha + d + e := by rw [hedef]; ring
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = 1 + ∑ i, ps i := ⟨_, rfl⟩
  have hsum0 : 0 ≤ ∑ i, ps i := Finset.sum_nonneg fun i _ => le_trans zero_le_one (hps i)
  have hq : 1 ≤ q := by rw [hqdef]; linarith
  have hpq : ∀ i, ps i ≤ q := by
    intro i
    have := Finset.single_le_sum (fun j _ => le_trans zero_le_one (hps j)) (Finset.mem_univ i)
    rw [hqdef]; linarith
  have hq0 : 0 < 2 * q := by linarith
  obtain ⟨deltaE, hdeltaE, hEA⟩ :=
    infrared_family_energy d hd E P X W D t k ps ht1 htd hps
  obtain ⟨Cpe, Cd, cd, hCpe, hCd, hcd, hroot⟩ :=
    aux_prop_growth_energy_assembly_root_extremes d hd (2 * q) (by linarith)
  obtain ⟨CP, hCP0, hPoinc⟩ :=
    aux_prop_growth_holder_micro_campanato_scaled_poincare d (by omega)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  obtain ⟨dabs, hdabs⟩ : ∃ s : ℝ, s = min 1 ((e / 2) * Real.log 3 / (Cd + Cpe)) := ⟨_, rfl⟩
  have hdabs0 : 0 < dabs := by
    rw [hdabs]
    exact lt_min one_pos (div_pos (mul_pos (half_pos he) hlog3) (add_pos hCd hCpe))
  refine ⟨min deltaE (min (cd / (4 * q)) dabs),
    lt_min hdeltaE (lt_min (div_pos hcd (by linarith : 0 < 4 * q)) hdabs0), ?_⟩
  intro M Rm Sreg It H hH hdelta
  have hdE : M.delta ≤ deltaE := hdelta.trans (min_le_left _ _)
  have hdc : M.delta ≤ cd / (4 * q) :=
    hdelta.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hda : M.delta ≤ dabs := hdelta.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hdpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hrate : Cd * M.delta + Cpe * M.delta ^ 2 ≤ (e / 2) * Real.log 3 :=
    aux_prop_growth_holder_micro_campanato_rate Cd Cpe e M.delta hCd hCpe hdpos
      (hda.trans_eq hdabs)
  obtain ⟨K, CbK, -, hKL, hKB, hen⟩ := hEA M Rm Sreg It H hH hdE
  obtain ⟨Dx, Mx0, CE0, hCE0, hDMx00, hext0, hmem0, -, hMxmom0⟩ :=
    hroot M 0 (InfraredAdmissible.zero M) (by simpa only [show 2 * (2 * q) = 4 * q by ring] using hdc) (fun _ => (1 / 2 : ℝ)) 1 one_pos le_rfl
  obtain ⟨Aenv, -, henv⟩ := infrared_family_envelope hd (fun _ => (1 / 2 : ℝ)) 1 one_pos
  obtain ⟨S, hSm, -, hSae, -, hSE⟩ := henv M H hH
  have hE : MemLp (fun om => Real.exp (S om)) (ENNReal.ofReal (2 * q)) (chaosSampleLaw M).toMeasure :=
    exponential_memLp _ S hSm _ (by linarith) (hSE _ (by linarith)).1
  let CS : ℝ := (eLpNorm (fun om => Real.exp (S om)) (ENNReal.ofReal (2 * q))
    (chaosSampleLaw M).toMeasure).toReal
  have hCS : eLpNorm (fun om => Real.exp (S om)) (ENNReal.ofReal (2 * q))
      (chaosSampleLaw M).toMeasure = ENNReal.ofReal CS :=
    (ENNReal.ofReal_toReal hE.eLpNorm_ne_top).symm
  have hmem02 : ∀ N, MemLp (Mx0 N) (ENNReal.ofReal (2 * q))
      (chaosSampleLaw M).toMeasure := by
    intro N
    exact (hmem0 N).2
  have hMxmom02 : ∀ N, eLpNorm (Mx0 N) (ENNReal.ofReal (2 * q))
      (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (CE0 * Real.exp ((Cd * M.delta + Cpe * M.delta ^ 2) * N)) := by
    intro N
    exact hMxmom0 N
  let Mx : ℕ → BilateralField d → ℝ := fun N om => Real.exp (S om) * Mx0 N om
  let CE : ℝ := CS * CE0
  have hCE : 0 ≤ CE := mul_nonneg ENNReal.toReal_nonneg hCE0
  have hMxmom : ∀ N, eLpNorm (Mx N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (CE * Real.exp ((Cd * M.delta + Cpe * M.delta ^ 2) * N)) := by
    intro N
    calc
      _ ≤ eLpNorm (fun om => Real.exp (S om)) (ENNReal.ofReal (2 * q)) (chaosSampleLaw M).toMeasure *
          eLpNorm (Mx0 N) (ENNReal.ofReal (2 * q)) (chaosSampleLaw M).toMeasure :=
        aux_rem_resolved_microscopic_product_lq_bound _ q (2 * q) (by linarith) (by linarith)
          _ _ hE (hmem02 N)
      _ ≤ ENNReal.ofReal CS * ENNReal.ofReal (CE0 * Real.exp ((Cd * M.delta + Cpe * M.delta ^ 2) * N)) :=
        mul_le_mul' hCS.le (hMxmom02 N)
      _ = _ := by rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg]; congr 1; dsimp [CE]; ring
  have hmem : ∀ N, MemLp (Mx N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure :=
    fun N => lt_of_le_of_lt (hMxmom N) ENNReal.ofReal_lt_top
  have hMx0 : ∀ N om, 0 ≤ Mx N om := fun N om =>
    mul_nonneg (Real.exp_pos _).le (hDMx00 N om).2
  have hfac := aux_prop_growth_holder_micro_campanato_fac e _ he hrate
  have hCP1 : 0 ≤ 1 + CP := add_nonneg zero_le_one hCP0
  refine ⟨fun N om => (1 + CP) * (Mx N om + |K N om|) * ((3 : ℝ) ^ (-(N : ℤ))) ^ (e / 2),
    fun i => (1 + CP) * (CE + max (CbK i) 0), ?_, ?_, ?_, ?_⟩
  · intro N om
    have := hMx0 N om
    have := (hfac N).1
    positivity
  · intro i N
    exact (aux_prop_growth_holder_micro_campanato_moment (chaosSampleLaw M).toMeasure (ps i) q
      (hps i) (hpq i) (Mx N) (K N) (1 + CP) _ ((Cd * M.delta + Cpe * M.delta ^ 2) * N) CE
      (CbK i) hCP1 (hfac N).1 (hfac N).2.1 (hfac N).2.2 hCE (hmem N) (hMxmom N)
      (hKL i N) (hKB i N)).1
  · intro i N
    exact (aux_prop_growth_holder_micro_campanato_moment (chaosSampleLaw M).toMeasure (ps i) q
      (hps i) (hpq i) (Mx N) (K N) (1 + CP) _ ((Cd * M.delta + Cpe * M.delta ^ 2) * N) CE
      (CbK i) hCP1 (hfac N).1 (hfac N).2.1 (hfac N).2.2 hCE (hmem N) (hMxmom N)
      (hKL i N) (hKB i N)).2
  · filter_upwards [hen, hext0, hSae] with om hom hext' hSω
    intro idx N F Kf hKf hFm hFb hmean v hsol x hx rad hrad hradN hrad1
    obtain ⟨hMxpos, hbounds, -⟩ := hext' N
    have hFnorm : ‖restrictC (closedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos)
        (infraredFamily H idx om)‖ ≤ S om := by
      cases idx with
      | none => exact hSω.1.1
      | some L => exact (hSω.2 L).1
    have hlow0 := aux_cor_neumann_source_micro_floor M 0 om N (Mx0 N om) hMxpos
      (fun y hy => (hbounds y hy).1)
    have hcompare := cutoff_zero_le_family M (infraredFamily H idx) om N _ 1 one_pos (S om) hFnorm
    have hlow : ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
        1 ≤ Mx N om *
          (cutoffPositiveCoefficient M (infraredFamily H idx) om N (fun _ => (1 / 2 : ℝ)) one_pos).val y := by
      filter_upwards [hlow0, hcompare] with y hy0 hyc
      calc
        1 ≤ Mx0 N om * (cutoffPositiveCoefficient M 0 om N (fun _ => (1 / 2 : ℝ)) one_pos).val y := hy0
        _ ≤ Mx0 N om * (Real.exp (S om) *
              (cutoffPositiveCoefficient M (infraredFamily H idx) om N (fun _ => (1 / 2 : ℝ)) one_pos).val y) :=
          mul_le_mul_of_nonneg_left hyc hMxpos.le
        _ = _ := by dsimp [Mx]; ring
    exact aux_cor_neumann_source_micro_pathwise CP hCP0 hPoinc
      (cutoffPositiveCoefficient M (infraredFamily H idx) om N (fun _ => (1 / 2 : ℝ)) one_pos) (Mx N om)
      (hMx0 N om) hlow v (K N om) Kf t alpha e ((3 : ℝ) ^ (-(N : ℤ))) rad hrad hradN hrad1
      he.le hexp
      (fun c hc => hom idx N F Kf hKf hFm hFb hmean v hsol c rad hc hrad hrad1) x hx



/-- Common coarse-cell Campanato constants from the zero-infrared ellipticity series. -/
theorem infrared_family_macro_cells :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩) (alpha : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    0 < alpha → alpha < 1 → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∃ (Xc : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ N om, 0 ≤ Xc N om) ∧
        (∀ i N, MemLp (Xc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (Xc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ idx : Option ℕ, ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
          (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x) = 0 →
        ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
          SolvesNeumann
              (cutoffPositiveCoefficient M (infraredFamily H idx) om N (fun _ => (1 / 2 : ℝ)) one_pos) F v →
          ∀ j : ℕ, j ≤ N → ∀ kk : Fin d → ℤ, aux_prop_growth_holder_macro_campanato_Adm j kk →
            aux_prop_growth_holder_macro_campanato_var
                (aux_prop_growth_holder_macro_campanato_cell (fun _ => (1 / 2 : ℝ)) j kk)
                ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ) ≤
              (aux_prop_growth_holder_macro_campanato_side j ^ alpha * (Xc N om * Kf)) ^ 2 *
                volume.real
                  (aux_prop_growth_holder_macro_campanato_cell (fun _ => (1 / 2 : ℝ)) j kk) := by
  intro d hd _ _ E P X W D alpha k ps ha0 ha1 hps
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = (max ((d : ℝ) - 1) ((d : ℝ) - 2 + 2 * alpha) + d) / 2 :=
    ⟨_, rfl⟩
  obtain ⟨ht1, htd, he0⟩ := aux_cor_neumann_source_t1_exponent d alpha ha1
  rw [← htdef] at ht1 htd he0
  obtain ⟨e, hedef⟩ : ∃ e : ℝ, e = 2 + t - 2 * alpha - d := ⟨_, rfl⟩
  have he : 0 < e := by rw [hedef]; exact he0
  have hexp : 2 + t = e + 2 * alpha + d := by rw [hedef]; ring
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have ht0 : 0 ≤ t := by linarith
  obtain ⟨e', he'def⟩ : ∃ e' : ℝ, e' = min e 1 := ⟨_, rfl⟩
  have he' : 0 < e' := by rw [he'def]; exact lt_min he one_pos
  have he'e : e' ≤ e := by rw [he'def]; exact min_le_left _ _
  have he'1 : e' ≤ 1 := by rw [he'def]; exact min_le_right _ _
  have hsum0 : 0 ≤ ∑ i, ps i := Finset.sum_nonneg fun i _ => le_trans zero_le_one (hps i)
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = 2 * (d : ℝ) / e' + ∑ i, ps i + 1 := ⟨_, rfl⟩
  have hdq0 : 0 ≤ 2 * (d : ℝ) / e' := div_nonneg (by positivity) he'.le
  have hQ1 : 1 ≤ Q := by rw [hQdef]; linarith
  have hDQ : 2 * (d : ℝ) ≤ e' * Q := by
    rw [hQdef, mul_add, mul_add, mul_div_cancel₀ _ he'.ne']
    have : 0 ≤ e' * ∑ i, ps i := mul_nonneg he'.le hsum0
    linarith
  have hpQ : ∀ i, ps i ≤ Q := by
    intro i
    have := Finset.single_le_sum (fun j _ => le_trans zero_le_one (hps j)) (Finset.mem_univ i)
    rw [hQdef]; linarith
  obtain ⟨deltaE, hdeltaE, hEA⟩ :=
    infrared_family_energy d hd E P X W D t k ps ht1 htd hps
  obtain ⟨deltaZ, hdeltaZ, hZ⟩ := aux_cor_neumann_source_Z_moments d hd E e' (2 * Q) he' (by linarith) (by nlinarith)
  refine ⟨min deltaE deltaZ, lt_min hdeltaE hdeltaZ, ?_⟩
  intro M Rm Sreg It H hH hdelta
  obtain ⟨K, CK, hK0, hKL, hKB, hen⟩ := hEA M Rm Sreg It H hH (hdelta.trans (min_le_left _ _))
  obtain ⟨CZ, hZN⟩ := hZ M Rm 0 (InfraredAdmissible.zero M) (hdelta.trans (min_le_right _ _))
  obtain ⟨Z0, hZ0def⟩ : ∃ Z0 : ℕ → BilateralField d → ℝ, Z0 = fun N om =>
      ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight e' 1 n *
        Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
          (Homogenization.originCube d 0) (-(n : ℤ))
          (E.chart (fun _ => (1 / 2 : ℝ)) 1 one_pos
            (cutoffPositiveCoefficient M 0 om N (fun _ => (1 / 2 : ℝ)) one_pos)
            (fun _ => (1 / 2 : ℝ)) 1) := ⟨_, rfl⟩
  have hZ00 : ∀ N om, 0 ≤ Z0 N om := by
    intro N om; rw [hZ0def]
    exact tsum_nonneg fun n => mul_nonneg ((aux_lambda_inv_moments_weight_sum e' he').2.2 n)
      (aux_lambda_inv_moments_Y_nonneg _ _)
  obtain ⟨Aenv, -, henv⟩ := infrared_family_envelope hd (fun _ => (1 / 2 : ℝ)) 1 one_pos
  obtain ⟨S, hSm, -, hSae, -, hSE⟩ := henv M H hH
  have hE : MemLp (fun om => Real.exp (S om)) (ENNReal.ofReal (2 * Q)) (chaosSampleLaw M).toMeasure :=
    exponential_memLp _ S hSm _ (by linarith) (hSE _ (by linarith)).1
  let CE : ℝ := (eLpNorm (fun om => Real.exp (S om)) (ENNReal.ofReal (2 * Q))
    (chaosSampleLaw M).toMeasure).toReal
  have hCE : eLpNorm (fun om => Real.exp (S om)) (ENNReal.ofReal (2 * Q))
      (chaosSampleLaw M).toMeasure = ENNReal.ofReal CE :=
    (ENNReal.ofReal_toReal hE.eLpNorm_ne_top).symm
  let Z : ℕ → BilateralField d → ℝ := fun N om => Real.exp (S om) * Z0 N om
  have hZ0 : ∀ N om, 0 ≤ Z N om := fun N om => mul_nonneg (Real.exp_pos _).le (hZ00 N om)
  have hZLpQ : ∀ N, MemLp (Z N) (ENNReal.ofReal Q) (chaosSampleLaw M).toMeasure := by
    intro N
    have hb := aux_rem_resolved_microscopic_product_lq_bound (chaosSampleLaw M).toMeasure
      Q (2 * Q) (by linarith) le_rfl (fun om => Real.exp (S om)) (Z0 N) hE
      (by rw [hZ0def]; exact (hZN N).1)
    have hb0 : eLpNorm (Z0 N) (ENNReal.ofReal (2 * Q)) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal CZ := by rw [hZ0def]; exact (hZN N).2.1
    exact lt_of_le_of_lt (hb.trans (mul_le_mul' hCE.le hb0)) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hZBdQ : ∀ N, eLpNorm (Z N) (ENNReal.ofReal Q) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (CE * CZ) := by
    intro N
    have hb0 : eLpNorm (Z0 N) (ENNReal.ofReal (2 * Q)) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal CZ := by rw [hZ0def]; exact (hZN N).2.1
    calc
      _ ≤ eLpNorm (fun om => Real.exp (S om)) (ENNReal.ofReal (2 * Q)) (chaosSampleLaw M).toMeasure *
          eLpNorm (Z0 N) (ENNReal.ofReal (2 * Q)) (chaosSampleLaw M).toMeasure :=
        aux_rem_resolved_microscopic_product_lq_bound _ Q (2 * Q) (by linarith) le_rfl _ _ hE
          (by rw [hZ0def]; exact (hZN N).1)
      _ ≤ ENNReal.ofReal CE * ENNReal.ofReal CZ := mul_le_mul' hCE.le hb0
      _ = _ := (ENNReal.ofReal_mul ENNReal.toReal_nonneg).symm
  obtain ⟨Cg, hCgdef⟩ : ∃ Cg : ℝ, Cg = (1 - (3 : ℝ) ^ (-(1 : ℝ))) / (1 - (3 : ℝ) ^ (-e')) :=
    ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = max 1 (P.C ^ 2 * Cg) := ⟨_, rfl⟩
  have hA1 : 1 ≤ A := by rw [hAdef]; exact le_max_left _ _
  have hAC : P.C ^ 2 * Cg ≤ A := by rw [hAdef]; exact le_max_right _ _
  have hA0 : 0 ≤ A := by linarith
  have hZL : ∀ i N, MemLp (Z N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure :=
    fun i N => (hZLpQ N).mono_exponent (ENNReal.ofReal_le_ofReal (hpQ i))
  have hZB : ∀ i N, eLpNorm (Z N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (CE * CZ) := fun i N =>
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (hpQ i))).trans (hZBdQ N)
  refine ⟨fun N om => 1 + A * (K N om + Z N om),
    fun i => 1 + A * (max (CK i) 0 + max (CE * CZ) 0), ?_, ?_, ?_, ?_⟩
  · intro N om
    have := mul_nonneg hA0 (add_nonneg (hK0 N om) (hZ0 N om))
    linarith
  · intro i N
    exact (aux_prop_growth_holder_assembly_moment _ (hps i) (K N) (Z N) hA0
      (hKL i N) (hZL i N) (hKB i N) (hZB i N)).1
  · intro i N
    exact (aux_prop_growth_holder_assembly_moment _ (hps i) (K N) (Z N) hA0
      (hKL i N) (hZL i N) (hKB i N) (hZB i N)).2
  · have hsummAE := ae_all_iff.2 fun N => (hZN N).2.2
    filter_upwards [hen, hsummAE, hSae] with om hom hsumm hSω
    intro idx N F Kf hKf hFm hFb hmean v hsol j _hj kk hkk
    set c := aux_prop_growth_holder_macro_campanato_center (fun _ => (1 / 2 : ℝ)) j kk with hc
    set s := aux_prop_growth_holder_macro_campanato_side j with hsdef
    have hs0 : 0 < s := aux_prop_growth_holder_macro_campanato_side_pos j
    have hs1 : s ≤ 1 := aux_prop_growth_holder_macro_campanato_side_le_one j
    have hcellT : aux_prop_growth_holder_macro_campanato_cell (fun _ => (1 / 2 : ℝ)) j kk =
        (centeredCube c s hs0 : Set (SpatialCoordinates d)) :=
      (centeredCube_coe_eq_ball c s hs0).symm
    have hQball : (unitNeumannCube d : Set (SpatialCoordinates d)) =
        ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2) := by
      rw [unitNeumannCube, centeredCube_coe_eq_ball]
    have hTQ : (centeredCube c s hs0 : Set (SpatialCoordinates d)) ⊆
        (unitNeumannCube d : Set (SpatialCoordinates d)) := by
      rw [← hcellT, hQball]
      exact aux_prop_growth_holder_macro_campanato_cell_subset _ hkk
    have hle : centeredCube c s hs0 ≤ unitNeumannCube d := hTQ
    have hcQ : c ∈ unitNeumannCube d := by
      apply hTQ
      rw [centeredCube_coe_eq_ball]
      exact mem_ball_self (half_pos hs0)
    have hcoef : ∀ᵐ y ∂volume.restrict (centeredCube c s hs0 : Set (SpatialCoordinates d)),
        (cutoffPositiveCoefficient M 0 om N c hs0).val y =
          (cutoffPositiveCoefficient M 0 om N (fun _ => (1 / 2 : ℝ)) one_pos).val y := by
      filter_upwards [aux_prop_growth_holder_micro_campanato_coeff_ae M 0 om N c hs0,
        ae_restrict_of_ae_restrict_of_subset hTQ
          (aux_prop_growth_holder_micro_campanato_coeff_ae M 0 om N (fun _ => (1 / 2 : ℝ))
            one_pos)] with y h1 h2
      rw [h1, h2]
    have hPc0 := aux_cor_neumann_source_cell_poincare hd E P c s hs0 hle
      (cutoffPositiveCoefficient M 0 om N (fun _ => (1 / 2 : ℝ)) one_pos)
      (cutoffPositiveCoefficient M 0 om N c hs0) hcoef
      ⟨(v : SobolevData (unitNeumannCube d)),
        (inf_le_left : meanZeroSobolevGraph (unitNeumannCube d) ≤
          weakSobolevGraph (unitNeumannCube d)) v.property⟩
    have hFnorm : ‖restrictC (closedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos)
        (infraredFamily H idx om)‖ ≤ S om := by
      cases idx with
      | none => exact hSω.1.1
      | some L => exact (hSω.2 L).1
    have hcomp := localGradientEnergy_le_mul
      (cutoffPositiveCoefficient M 0 om N (fun _ => (1 / 2 : ℝ)) one_pos)
      (cutoffPositiveCoefficient M (infraredFamily H idx) om N (fun _ => (1 / 2 : ℝ)) one_pos)
      (Real.exp (S om))
      (cutoff_zero_le_family M (infraredFamily H idx) om N _ 1 one_pos (S om) hFnorm)
      (centeredCube c s hs0).isOpen.measurableSet (sobolevGradient (v : SobolevData (unitNeumannCube d)))
    have hPc : aux_prop_growth_holder_macro_campanato_var (centeredCube c s hs0 : Set (SpatialCoordinates d))
        ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ) ≤
      P.C ^ 2 * s ^ 2 * (Real.exp (S om) *
        (E.lam c s hs0 (cutoffPositiveCoefficient M 0 om N c hs0) c s 1 1)⁻¹) *
        localGradientEnergy
          (cutoffPositiveCoefficient M (infraredFamily H idx) om N (fun _ => (1 / 2 : ℝ)) one_pos)
          (centeredCube c s hs0).isOpen.measurableSet (sobolevGradient (v : SobolevData (unitNeumannCube d))) := by
      calc
        _ ≤ P.C ^ 2 * s ^ 2 * (E.lam c s hs0 (cutoffPositiveCoefficient M 0 om N c hs0) c s 1 1)⁻¹ *
            localGradientEnergy (cutoffPositiveCoefficient M 0 om N (fun _ => (1 / 2 : ℝ)) one_pos)
              (centeredCube c s hs0).isOpen.measurableSet (sobolevGradient (v : SobolevData (unitNeumannCube d))) := hPc0
        _ ≤ P.C ^ 2 * s ^ 2 * (E.lam c s hs0 (cutoffPositiveCoefficient M 0 om N c hs0) c s 1 1)⁻¹ *
            (Real.exp (S om) * localGradientEnergy
              (cutoffPositiveCoefficient M (infraredFamily H idx) om N (fun _ => (1 / 2 : ℝ)) one_pos)
              (centeredCube c s hs0).isOpen.measurableSet (sobolevGradient (v : SobolevData (unitNeumannCube d)))) :=
          mul_le_mul_of_nonneg_left hcomp
            (mul_nonneg (mul_nonneg (sq_nonneg P.C) (sq_nonneg s))
              (inv_pos.mpr (E.lam_pos _ _ _ _ _ _ _ _)).le)
        _ = _ := by ring
    have hE1 := hom idx N F Kf hKf hFm hFb hmean v hsol c (s / 2) hcQ (half_pos hs0) (by linarith)
    have hset : Metric.ball c (s / 2) ∩ (unitNeumannCube d : Set (SpatialCoordinates d)) =
        (centeredCube c s hs0 : Set (SpatialCoordinates d)) := by
      rw [← centeredCube_coe_eq_ball c s hs0]; exact Set.inter_eq_left.2 hTQ
    have hE2 : localGradientEnergy
        (cutoffPositiveCoefficient M (infraredFamily H idx) om N (fun _ => (1 / 2 : ℝ)) one_pos)
        (s := (centeredCube c s hs0 : Set (SpatialCoordinates d)))
        (centeredCube c s hs0).isOpen.measurableSet
        (sobolevGradient (v : SobolevData (unitNeumannCube d))) ≤ K N om * Kf ^ 2 * (s / 2) ^ t := by
      rw [← aux_cor_neumann_source_energy_congr _ hset
        (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)]
      exact hE1
    have hlam := aux_cor_neumann_source_lam_cell E M 0 om N j kk hkk e e' he' he'e he'1 (hsumm N)
    have hV := aux_prop_growth_holder_macro_campanato_cell_volume (fun _ : Fin d => (1 / 2 : ℝ)) j kk
    rw [hV, hcellT]
    have hfin := aux_cor_neumann_source_cell_alg d _ P.C s _ _ (K N om) Kf t e alpha (Z N om) Cg A
      hs0 (mul_nonneg (Real.exp_pos _).le (inv_nonneg.2 (E.lam_pos _ _ _ _ _ _ _ _).le)) (hK0 N om) (hZ0 N om) ht0 hA1 hAC hexp
      hPc hE2 (by
        have hh := mul_le_mul_of_nonneg_left hlam (Real.exp_pos (S om)).le
        rw [← hCgdef] at hh
        simpa only [Z, hZ0def, mul_left_comm] using hh)
    exact hfin


theorem infrared_family_macro_campanato :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩) (alpha : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    0 < alpha → alpha < 1 → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∃ (Kmac : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ N om, 0 ≤ Kmac N om) ∧
        (∀ i N, MemLp (Kmac N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (Kmac N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ idx : Option ℕ, ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
          (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x) = 0 →
        ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
          SolvesNeumann
              (cutoffPositiveCoefficient M (infraredFamily H idx) om N (fun _ => (1 / 2 : ℝ)) one_pos) F v →
          ∀ x ∈ unitNeumannCube d, ∀ rad : ℝ,
            (3 : ℝ) ^ (-(N : ℤ)) ≤ rad → rad ≤ 1 →
            ∫ y in Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
                ((v : SobolevData (unitNeumannCube d)).1 y - setAverage
                  (Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
                  (v : SobolevData (unitNeumannCube d)).1) ^ 2
                ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)) ≤
              (Kmac N om * Kf) ^ 2 * rad ^ (2 * alpha) *
                volume.real (Metric.ball x rad ∩
                  (unitNeumannCube d : Set (SpatialCoordinates d))) := by
  intro d hd _ _ E P X W D alpha k ps ha0 ha1 hps
  obtain ⟨Kd, hKd1, hunit⟩ := aux_prop_growth_holder_macro_campanato_unit (d := d) alpha ha0 ha1.le
  obtain ⟨delta1, hdelta1, hcell⟩ :=
    infrared_family_macro_cells d hd E P X W D alpha k ps ha0 ha1 hps
  obtain ⟨delta2, hdelta2, hmic⟩ :=
    infrared_family_micro_campanato d hd E P X W D alpha k ps ha0 ha1 hps
  refine ⟨min delta1 delta2, lt_min hdelta1 hdelta2, ?_⟩
  intro M Rm Sreg It H hH hdelta
  obtain ⟨Xc, CX, hXc0, hXcL, hXcB, hcellE⟩ :=
    hcell M Rm Sreg It H hH (hdelta.trans (min_le_left _ _))
  obtain ⟨Kmic, Cmic, hKmic0, hKmicL, hKmicB, hmicE⟩ :=
    hmic M Rm Sreg It H hH (hdelta.trans (min_le_right _ _))
  have hKd0 : 0 ≤ Kd := by linarith
  have hY0 : 0 ≤ ((2 : ℝ) * 3 ^ (0 : ℕ)) ^ (alpha + (d : ℝ) / 2) :=
    Real.rpow_nonneg (by norm_num) _
  have hc0 : 0 ≤ Kd * (1 + ((2 : ℝ) * 3 ^ (0 : ℕ)) ^ (alpha + (d : ℝ) / 2)) :=
    mul_nonneg hKd0 (by linarith)
  refine ⟨fun N om => 1 + Kd * (1 + ((2 : ℝ) * 3 ^ (0 : ℕ)) ^ (alpha + (d : ℝ) / 2)) *
      (Xc N om + Kmic N om),
    fun i => 1 + Kd * (1 + ((2 : ℝ) * 3 ^ (0 : ℕ)) ^ (alpha + (d : ℝ) / 2)) *
      (max (CX i) 0 + max (Cmic i) 0), ?_, ?_, ?_, ?_⟩
  · intro N om
    have := mul_nonneg hc0 (add_nonneg (hXc0 N om) (hKmic0 N om))
    linarith
  · intro i N
    exact (aux_prop_growth_holder_assembly_moment _ (hps i) (Xc N) (Kmic N) hc0
      (hXcL i N) (hKmicL i N) (hXcB i N) (hKmicB i N)).1
  · intro i N
    exact (aux_prop_growth_holder_assembly_moment _ (hps i) (Xc N) (Kmic N) hc0
      (hXcL i N) (hKmicL i N) (hXcB i N) (hKmicB i N)).2
  · filter_upwards [hcellE, hmicE] with om hC hM
    intro idx N F Kf hKf hFm hFb hmean v hsol x hx rad hradN hrad1
    have hside : aux_prop_growth_holder_macro_campanato_side N = (3 : ℝ) ^ (-(N : ℤ)) := by
      unfold aux_prop_growth_holder_macro_campanato_side
      rw [zpow_neg, zpow_natCast]
    have hsidepos := aux_prop_growth_holder_macro_campanato_side_pos N
    have hrad0 : 0 < rad := hsidepos.trans_le (hside.trans_le hradN)
    have hA : 0 ≤ Xc N om * Kf := mul_nonneg (hXc0 N om) hKf
    have hB : 0 ≤ Kmic N om * Kf := mul_nonneg (hKmic0 N om) hKf
    have hu : MemLp ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ) 2
        (volume.restrict (ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2))) := Lp.memLp _
    have H1 : ∀ j : ℕ, 0 ≤ j → j ≤ N → ∀ kk : Fin d → ℤ,
        aux_prop_growth_holder_macro_campanato_Adm j kk →
        aux_prop_growth_holder_macro_campanato_var
            (aux_prop_growth_holder_macro_campanato_cell (fun _ => (1 / 2 : ℝ)) j kk)
            ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ) ≤
          (1 * aux_prop_growth_holder_macro_campanato_side j ^ alpha * (Xc N om * Kf)) ^ 2 *
            volume.real
              (aux_prop_growth_holder_macro_campanato_cell (fun _ => (1 / 2 : ℝ)) j kk) := by
      intro j _ hj kk hkk
      rw [one_mul]
      exact hC idx N F Kf hKf hFm hFb hmean v hsol j hj kk hkk
    have H2 : ∀ p ∈ ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2), ∀ ρ : ℝ,
        aux_prop_growth_holder_macro_campanato_side N ≤ ρ →
        ρ ≤ aux_prop_growth_holder_macro_campanato_side N →
        aux_prop_growth_holder_macro_campanato_var
            (ball p ρ ∩ ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2))
            ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ) ≤
          (Kmic N om * Kf) ^ 2 * ρ ^ (2 * alpha) *
            volume.real (ball p ρ ∩ ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2)) := by
      intro p hp ρ hρ1 hρ2
      have hρ0 : 0 < ρ := hsidepos.trans_le hρ1
      have hρN : ρ ≤ (3 : ℝ) ^ (-(N : ℤ)) := hρ2.trans_eq hside
      have hρ1' : ρ ≤ 1 := hρ2.trans (aux_prop_growth_holder_macro_campanato_side_le_one N)
      have h := hM idx N F Kf hKf hFm hFb hmean v hsol p hp ρ hρ0 hρN hρ1'
      rw [aux_prop_growth_holder_macro_campanato_target_eq
        (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
        Set.inter_subset_right] at h
      exact h
    have H3 : aux_prop_growth_holder_macro_campanato_var
        (ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2))
        ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ) ≤
          (Xc N om * Kf) ^ 2 := by
      have h0 := hC idx N F Kf hKf hFm hFb hmean v hsol 0 (Nat.zero_le N) (fun _ => 0)
        (by intro i; simp)
      have hcenter0 : aux_prop_growth_holder_macro_campanato_center
          (fun _ : Fin d => (1 / 2 : ℝ)) 0 (fun _ => 0) =
          (fun _ : Fin d => (1 / 2 : ℝ)) := by
        funext i
        simp [aux_prop_growth_holder_macro_campanato_center,
          aux_prop_growth_holder_macro_campanato_side]
      have hcell0 : aux_prop_growth_holder_macro_campanato_cell
          (fun _ : Fin d => (1 / 2 : ℝ)) 0 (fun _ => 0) =
          ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2) := by
        unfold aux_prop_growth_holder_macro_campanato_cell
        rw [hcenter0]
        norm_num [aux_prop_growth_holder_macro_campanato_side]
      have hvol : volume.real (ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2)) = 1 :=
        centeredCube_one_volume_real (fun _ => (1 / 2 : ℝ)) one_pos
      rw [hcell0, hvol, mul_one] at h0
      simpa [aux_prop_growth_holder_macro_campanato_side] using h0
    have hmain := hunit (fun _ => (1 / 2 : ℝ)) _ hu N 0 1 (Xc N om * Kf) (Kmic N om * Kf)
      (Xc N om * Kf) (aux_prop_growth_holder_macro_campanato_side N) zero_le_one hA hB hA
      hsidepos le_rfl H1 H2 H3 x hx rad (hside.trans_le hradN) hrad1
    rw [aux_prop_growth_holder_macro_campanato_target_eq
      (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
      Set.inter_subset_right]
    have harith := aux_cor_neumann_source_macro_arith Kd
      (((2 : ℝ) * 3 ^ (0 : ℕ)) ^ (alpha + (d : ℝ) / 2)) (Xc N om) (Kmic N om) Kf hKd0 hY0
      (hXc0 N om) (hKmic0 N om) hKf
    have hL0 : 0 ≤ Kd * (1 * (Xc N om * Kf) + Kmic N om * Kf +
        ((2 : ℝ) * 3 ^ (0 : ℕ)) ^ (alpha + (d : ℝ) / 2) * (Xc N om * Kf)) :=
      mul_nonneg hKd0 (add_nonneg (add_nonneg (by linarith) hB) (mul_nonneg hY0 hA))
    exact hmain.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hL0 harith 2) (Real.rpow_nonneg hrad0.le _)) measureReal_nonneg)


theorem infrared_family_campanato :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩) (alpha : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    0 < alpha → alpha < 1 → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∃ (Kc : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ N om, 0 ≤ Kc N om) ∧
        (∀ i N, MemLp (Kc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (Kc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ idx : Option ℕ, ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
          (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x) = 0 →
        ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
          SolvesNeumann
              (cutoffPositiveCoefficient M (infraredFamily H idx) om N (fun _ => (1 / 2 : ℝ)) one_pos) F v →
          ∀ x ∈ unitNeumannCube d, ∀ rad : ℝ, 0 < rad → rad ≤ 1 →
            ∫ y in Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
                ((v : SobolevData (unitNeumannCube d)).1 y - setAverage
                  (Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
                  (v : SobolevData (unitNeumannCube d)).1) ^ 2
                ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)) ≤
              (Kc N om * Kf) ^ 2 * rad ^ (2 * alpha) *
                volume.real (Metric.ball x rad ∩
                  (unitNeumannCube d : Set (SpatialCoordinates d))) := by
  intro d hd _ _ E P X W D alpha k ps ha0 ha1 hps
  obtain ⟨delta1, hdelta1, hmac⟩ :=
    infrared_family_macro_campanato d hd E P X W D alpha k ps ha0 ha1 hps
  obtain ⟨delta2, hdelta2, hmic⟩ :=
    infrared_family_micro_campanato d hd E P X W D alpha k ps ha0 ha1 hps
  refine ⟨min delta1 delta2, lt_min hdelta1 hdelta2, ?_⟩
  intro M Rm Sreg It H hH hdelta
  obtain ⟨Kmac, Cmac, hKmac0, hKmacL, hKmacB, hmacE⟩ :=
    hmac M Rm Sreg It H hH (hdelta.trans (min_le_left _ _))
  obtain ⟨Kmic, Cmic, hKmic0, hKmicL, hKmicB, hmicE⟩ :=
    hmic M Rm Sreg It H hH (hdelta.trans (min_le_right _ _))
  refine ⟨fun N om => Kmic N om + Kmac N om, fun i => max (Cmic i) 0 + max (Cmac i) 0,
    fun N om => add_nonneg (hKmic0 N om) (hKmac0 N om), ?_, ?_, ?_⟩
  · intro i N
    exact (hKmicL i N).add (hKmacL i N)
  · intro i N
    have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (ps i) := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (hps i)
    calc eLpNorm (fun om => Kmic N om + Kmac N om) (ENNReal.ofReal (ps i))
          (chaosSampleLaw M).toMeasure
        ≤ eLpNorm (Kmic N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure +
            eLpNorm (Kmac N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure :=
          eLpNorm_add_le hp1
      _ ≤ ENNReal.ofReal (max (Cmic i) 0) + ENNReal.ofReal (max (Cmac i) 0) :=
          add_le_add ((hKmicB i N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
            ((hKmacB i N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
      _ = ENNReal.ofReal (max (Cmic i) 0 + max (Cmac i) 0) :=
          (ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)).symm
  · filter_upwards [hmacE, hmicE] with om hom1 hom2
    intro idx N F Kf hKf hFm hFb hmean v hsol x hx rad hrad hrad1
    exact aux_cor_neumann_source_campanato_split _ (Kmic N om) (Kmac N om) Kf
      (rad ^ (2 * alpha)) _ ((3 : ℝ) ^ (-(N : ℤ))) rad (hKmic0 N om) (hKmac0 N om) hKf
      (Real.rpow_nonneg hrad.le _) measureReal_nonneg
      (fun h => hom2 idx N F Kf hKf hFm hFb hmean v hsol x hx rad hrad h hrad1)
      (fun h => hom1 idx N F Kf hKf hFm hFb hmean v hsol x hx rad h hrad1)


theorem infrared_family_neumann_source :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (_Cp : CampanatoInput d) (t alpha : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t → t < d → 0 < alpha → alpha < 1 → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ N om, 0 ≤ K N om) ∧
        (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ idx : Option ℕ, ∀ (N : ℕ)
          (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
          (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x) = 0 →
        ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
          SolvesNeumann
              (cutoffPositiveCoefficient M (infraredFamily H idx) om N (fun _ => (1 / 2 : ℝ)) one_pos) F v →
          (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
            IsHolderOn alpha
                (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                  Set (SpatialCoordinates d)) U ∧
            ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] U ∧
            cAlphaNorm alpha
                (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                  Set (SpatialCoordinates d)) U ≤ K N om * Kf) ∧
          (∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ unitNeumannCube d →
            0 < rad → rad ≤ 1 →
            localGradientEnergy
                (cutoffPositiveCoefficient M (infraredFamily H idx) om N (fun _ => (1 / 2 : ℝ)) one_pos)
                (s := Metric.ball x rad ∩
                  (unitNeumannCube d : Set (SpatialCoordinates d)))
                (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
                (sobolevGradient (v : SobolevData (unitNeumannCube d))) ≤
              K N om * Kf ^ 2 * rad ^ t) := by
  intro d hd _ _ E P X W D Cp t alpha k ps ht1 htd ha0 ha1 hps
  obtain ⟨deltaE, hdeltaE, hEn⟩ :=
    infrared_family_energy d hd E P X W D t k ps ht1 htd hps
  obtain ⟨deltaC, hdeltaC, hCa⟩ :=
    infrared_family_campanato d hd E P X W D alpha k ps ha0 ha1 hps
  refine ⟨min deltaE deltaC, lt_min hdeltaE hdeltaC, ?_⟩
  intro M Rm Sreg It H hH hdelta
  obtain ⟨KE, CE, hKE0, hKEL, hKEB, hEae⟩ :=
    hEn M Rm Sreg It H hH (hdelta.trans (min_le_left _ _))
  obtain ⟨Kc, Cc, hKc0, hKcL, hKcB, hCae⟩ :=
    hCa M Rm Sreg It H hH (hdelta.trans (min_le_right _ _))
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = max 1 ((2 + Real.sqrt d) * Cp.C alpha) := ⟨_, rfl⟩
  have hc1 : 1 ≤ c := hcdef ▸ le_max_left _ _
  have hc0 : 0 ≤ c := by linarith
  have hcC : (2 + Real.sqrt d) * Cp.C alpha ≤ c := hcdef ▸ le_max_right _ _
  refine ⟨fun N om => 1 + c * (KE N om + Kc N om),
    fun i => 1 + c * (max (CE i) 0 + max (Cc i) 0),
    fun N om => add_nonneg zero_le_one
      (mul_nonneg hc0 (add_nonneg (hKE0 N om) (hKc0 N om))), ?_, ?_, ?_⟩
  · intro i N
    exact (aux_prop_growth_holder_assembly_moment _ (hps i) (KE N) (Kc N) hc0
      (hKEL i N) (hKcL i N) (hKEB i N) (hKcB i N)).1
  · intro i N
    exact (aux_prop_growth_holder_assembly_moment _ (hps i) (KE N) (Kc N) hc0
      (hKEL i N) (hKcL i N) (hKEB i N) (hKcB i N)).2
  · filter_upwards [hEae, hCae] with om hE hC
    intro idx N F Kf hKf hFm hFb hmean v hsol
    have hKE := hKE0 N om
    have hKc := hKc0 N om
    obtain ⟨U, hUc, hUH, hUae, hUn⟩ := aux_cor_neumann_source_holder_of_campanato Cp ha0 ha1 v
      hKc hKf (hC idx N F Kf hKf hFm hFb hmean v hsol)
    refine ⟨⟨U, hUc, hUH, hUae, hUn.trans ?_⟩, ?_⟩
    · have h1 : (2 + Real.sqrt d) * Cp.C alpha * Kc N om ≤ c * Kc N om :=
        mul_le_mul_of_nonneg_right hcC hKc
      have h2 : c * Kc N om ≤ c * (KE N om + Kc N om) :=
        mul_le_mul_of_nonneg_left (by linarith) hc0
      have h3 : (2 + Real.sqrt d) * Cp.C alpha * Kc N om ≤ 1 + c * (KE N om + Kc N om) := by
        linarith
      exact mul_le_mul_of_nonneg_right h3 hKf
    · intro x rad hx hrad hrad1
      have h := hE idx N F Kf hKf hFm hFb hmean v hsol x rad hx hrad hrad1
      have h1 : KE N om ≤ c * KE N om := le_mul_of_one_le_left hKE hc1
      have h2 : c * KE N om ≤ c * (KE N om + Kc N om) :=
        mul_le_mul_of_nonneg_left (by linarith) hc0
      have hKle : KE N om ≤ 1 + c * (KE N om + Kc N om) := by linarith
      calc _ ≤ KE N om * Kf ^ 2 * rad ^ t := h
        _ ≤ (1 + c * (KE N om + Kc N om)) * Kf ^ 2 * rad ^ t :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKle (sq_nonneg _))
            (Real.rpow_nonneg hrad.le _)


end SubdiffusiveProcess.AuditExports
