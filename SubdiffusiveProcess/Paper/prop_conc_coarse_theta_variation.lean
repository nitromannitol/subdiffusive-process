module

public import SubdiffusiveProcess.Paper.prop_conc_deletion_cost
public import SubdiffusiveProcess.Paper.prop_conc_masked_delta_bounds
public import SubdiffusiveProcess.Paper.prop_conc_pair_mask

@[expose] public section

/-! Coarse-layer variation of the relative response of a pair of limiting forms.

A weight `exp g` that is within `S` of a constant on the observation cell `q` changes the relative
response `θ` by at most `C S e^{CS} (M - m)`: the constant is invisible (the relative response is
homogeneous of degree zero in a common scalar), only cell values of `g` enter, and the remaining
bounded weight is a deletion supported in `q`, controlled by `prop_conc_deletion_cost` together
with the total masses `ν(q) ≤ C`, `ζ(q) ≤ C (M - m)^2` of `prop_conc_masked_delta_bounds`.
The endpoint gap `Δ = M - m` is retained. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Pointwise
namespace Paper
noncomputable section

section shift
variable {d : ℕ} {Q : Opens (SpatialCoordinates d)} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
  {C0 m M : ℝ}

/-- Adding a constant to the weight multiplies the weighted energy by the exponential of the constant. -/
theorem aux_prop_conc_coarse_theta_variation_wenergy_add
    {E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d)))}
    (Gamma : DirichletForm.EnergyMeasure E) (q : Set (SpatialCoordinates d))
    (g : SpatialCoordinates d → ℝ) (κ : ℝ) (v : DomainL2 Q) :
    aux_prop_conc_pair_data_wenergy Gamma q (fun x => g x + κ) v =
      Real.exp κ * aux_prop_conc_pair_data_wenergy Gamma q g v := by
  unfold aux_prop_conc_pair_data_wenergy
  have hpt : ∀ x, ENNReal.ofReal (Real.exp (g x + κ)) =
      ENNReal.ofReal (Real.exp κ) * ENNReal.ofReal (Real.exp (g x)) := by
    intro x
    rw [Real.exp_add, mul_comm, ENNReal.ofReal_mul (Real.exp_pos _).le]
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]

/-- The weighted energy only sees the weight on the observation set. -/
theorem aux_prop_conc_coarse_theta_variation_wenergy_congr
    {E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d)))}
    (Gamma : DirichletForm.EnergyMeasure E) {q : Set (SpatialCoordinates d)} (hq : MeasurableSet q)
    {g g' : SpatialCoordinates d → ℝ} (h : ∀ x ∈ q, g x = g' x) (v : DomainL2 Q) :
    aux_prop_conc_pair_data_wenergy Gamma q g v = aux_prop_conc_pair_data_wenergy Gamma q g' v := by
  unfold aux_prop_conc_pair_data_wenergy
  congr 1
  exact setLIntegral_congr_fun hq (fun x hx => by rw [h x hx])

theorem aux_prop_conc_coarse_theta_variation_wInfE_add
    (X : prop_conc_pair_data Q z r hr C0 m M) (g : SpatialCoordinates d → ℝ) (κ : ℝ)
    (p : Fin d → ℝ) :
    aux_prop_conc_pair_data_wInfE X (fun x => g x + κ) p =
      Real.exp κ * aux_prop_conc_pair_data_wInfE X g p := by
  unfold aux_prop_conc_pair_data_wInfE
  have hset : {e : ℝ | ∃ v ∈ X.E.domain, v - (X.P.boundary p : DomainL2 Q) ∈ X.D ∧
      e = aux_prop_conc_pair_data_wenergy X.GammaE
        (centeredCube z r hr : Set (SpatialCoordinates d)) (fun x => g x + κ) v} =
      Real.exp κ • {e : ℝ | ∃ v ∈ X.E.domain, v - (X.P.boundary p : DomainL2 Q) ∈ X.D ∧
        e = aux_prop_conc_pair_data_wenergy X.GammaE
          (centeredCube z r hr : Set (SpatialCoordinates d)) g v} := by
    ext e
    simp only [Set.mem_smul_set, Set.mem_setOf_eq, smul_eq_mul]
    constructor
    · rintro ⟨v, hv, hvD, rfl⟩
      exact ⟨_, ⟨v, hv, hvD, rfl⟩, by rw [aux_prop_conc_coarse_theta_variation_wenergy_add]⟩
    · rintro ⟨_, ⟨v, hv, hvD, rfl⟩, rfl⟩
      exact ⟨v, hv, hvD, by rw [aux_prop_conc_coarse_theta_variation_wenergy_add]⟩
  rw [hset, Real.sInf_smul_of_nonneg (Real.exp_pos κ).le, smul_eq_mul]

theorem aux_prop_conc_coarse_theta_variation_wInfF_add
    (X : prop_conc_pair_data Q z r hr C0 m M) (g : SpatialCoordinates d → ℝ) (κ : ℝ)
    (p : Fin d → ℝ) :
    aux_prop_conc_pair_data_wInfF X (fun x => g x + κ) p =
      Real.exp κ * aux_prop_conc_pair_data_wInfF X g p := by
  unfold aux_prop_conc_pair_data_wInfF
  have hset : {e : ℝ | ∃ v ∈ X.F.domain, v - (X.P.boundary p : DomainL2 Q) ∈ X.D ∧
      e = aux_prop_conc_pair_data_wenergy X.GammaF
        (centeredCube z r hr : Set (SpatialCoordinates d)) (fun x => g x + κ) v} =
      Real.exp κ • {e : ℝ | ∃ v ∈ X.F.domain, v - (X.P.boundary p : DomainL2 Q) ∈ X.D ∧
        e = aux_prop_conc_pair_data_wenergy X.GammaF
          (centeredCube z r hr : Set (SpatialCoordinates d)) g v} := by
    ext e
    simp only [Set.mem_smul_set, Set.mem_setOf_eq, smul_eq_mul]
    constructor
    · rintro ⟨v, hv, hvD, rfl⟩
      exact ⟨_, ⟨v, hv, hvD, rfl⟩, by rw [aux_prop_conc_coarse_theta_variation_wenergy_add]⟩
    · rintro ⟨_, ⟨v, hv, hvD, rfl⟩, rfl⟩
      exact ⟨v, hv, hvD, by rw [aux_prop_conc_coarse_theta_variation_wenergy_add]⟩
  rw [hset, Real.sInf_smul_of_nonneg (Real.exp_pos κ).le, smul_eq_mul]

/-- The relative response is homogeneous of degree zero in a common scalar of the weight. -/
theorem aux_prop_conc_coarse_theta_variation_theta_add
    (X : prop_conc_pair_data Q z r hr C0 m M) (c : ℝ) (p : Fin d → ℝ)
    (g : SpatialCoordinates d → ℝ) (κ : ℝ) :
    aux_prop_conc_pair_data_theta X c p (fun x => g x + κ) =
      aux_prop_conc_pair_data_theta X c p g := by
  unfold aux_prop_conc_pair_data_theta
  simp only [aux_prop_conc_coarse_theta_variation_wInfE_add,
    aux_prop_conc_coarse_theta_variation_wInfF_add]
  rw [← Finset.mul_sum]
  rw [show Real.exp κ * aux_prop_conc_pair_data_wInfF X g p -
        c * (Real.exp κ * aux_prop_conc_pair_data_wInfE X g p) =
      Real.exp κ * (aux_prop_conc_pair_data_wInfF X g p -
        c * aux_prop_conc_pair_data_wInfE X g p) by ring]
  exact mul_div_mul_left _ _ (Real.exp_pos κ).ne'

/-- The relative response only depends on the weight on the observation cell. -/
theorem aux_prop_conc_coarse_theta_variation_theta_congr
    (X : prop_conc_pair_data Q z r hr C0 m M) (c : ℝ) (p : Fin d → ℝ)
    {g g' : SpatialCoordinates d → ℝ}
    (h : ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), g x = g' x) :
    aux_prop_conc_pair_data_theta X c p g = aux_prop_conc_pair_data_theta X c p g' := by
  have hq : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen.measurableSet
  have hE : ∀ p' : Fin d → ℝ, aux_prop_conc_pair_data_wInfE X g p' =
      aux_prop_conc_pair_data_wInfE X g' p' := by
    intro p'
    unfold aux_prop_conc_pair_data_wInfE
    congr 1
    ext e
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨v, hv, hvD, rfl⟩
      exact ⟨v, hv, hvD, aux_prop_conc_coarse_theta_variation_wenergy_congr X.GammaE hq h v⟩
    · rintro ⟨v, hv, hvD, rfl⟩
      exact ⟨v, hv, hvD, (aux_prop_conc_coarse_theta_variation_wenergy_congr X.GammaE hq h v).symm⟩
  have hF : ∀ p' : Fin d → ℝ, aux_prop_conc_pair_data_wInfF X g p' =
      aux_prop_conc_pair_data_wInfF X g' p' := by
    intro p'
    unfold aux_prop_conc_pair_data_wInfF
    congr 1
    ext e
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨v, hv, hvD, rfl⟩
      exact ⟨v, hv, hvD, aux_prop_conc_coarse_theta_variation_wenergy_congr X.GammaF hq h v⟩
    · rintro ⟨v, hv, hvD, rfl⟩
      exact ⟨v, hv, hvD, (aux_prop_conc_coarse_theta_variation_wenergy_congr X.GammaF hq h v).symm⟩
  unfold aux_prop_conc_pair_data_theta
  simp only [hE, hF]

end shift

/-- Coarse variation of the relative response: a weight within `S` of a constant on the observation
cell moves `θ` by at most `C S e^{C S} (M - m)`, uniformly in the pair, the slope and `c ∈ [m, M]`. -/
theorem prop_conc_coarse_theta_variation (C0 : ℝ) (hC0 : 1 ≤ C0) (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {Q : Opens (SpatialCoordinates d)} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
      {m M : ℝ} (X : prop_conc_pair_data Q z r hr C0 m M) (c : ℝ), c ∈ Icc m M →
      ∀ p ∈ aux_prop_conc_pair_data_slopes d,
      ∀ (g : SpatialCoordinates d → ℝ), Measurable g → ∀ (κ S : ℝ), 0 ≤ S →
        (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), |g x - κ| ≤ S) →
        |aux_prop_conc_pair_data_theta X c p g -
            aux_prop_conc_pair_data_theta X c p (fun _ => 0)| ≤
          C * S * Real.exp (C * S) * (M - m) := by
  obtain ⟨C1, hC1, h1⟩ := prop_conc_deletion_cost C0 hC0
  obtain ⟨C2, hC2, h2⟩ := prop_conc_masked_delta_bounds C0 hC0 d
  refine ⟨2 * C1 * C2 + C1, by positivity, ?_⟩
  intro Q z r hr m M X c hc p hp g hg κ S hS hgS
  have hq : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen.measurableSet
  -- the truncated centered weight
  let g1 : SpatialCoordinates d → ℝ :=
    (centeredCube z r hr : Set (SpatialCoordinates d)).indicator (fun x => g x - κ)
  have hg1m : Measurable g1 := (hg.sub measurable_const).indicator hq
  have hg1supp : ∀ x, x ∉ (centeredCube z r hr : Set (SpatialCoordinates d)) → g1 x = 0 := by
    intro x hx
    simp only [g1, Set.indicator_of_notMem hx]
  have hg1bd : ∀ x, |g1 x| ≤ S := by
    intro x
    by_cases hx : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d))
    · simp only [g1, Set.indicator_of_mem hx]
      exact hgS x hx
    · simp only [g1, Set.indicator_of_notMem hx, abs_zero]; exact hS
  have hθ : aux_prop_conc_pair_data_theta X c p g = aux_prop_conc_pair_data_theta X c p g1 := by
    have h3 := aux_prop_conc_coarse_theta_variation_theta_add X c p (fun x => g x - κ) κ
    have h4 : (fun x => (g x - κ) + κ) = g := by funext x; ring
    rw [h4] at h3
    rw [h3]
    exact aux_prop_conc_coarse_theta_variation_theta_congr X c p
      (fun x hx => by simp only [g1, Set.indicator_of_mem hx])
  rw [hθ]
  obtain ⟨hb, -⟩ := h1 X c hc p hp g1 hg1m _ hq subset_rfl hg1supp S hS hg1bd
  obtain ⟨hmass, -⟩ := h2 X
  obtain ⟨hnu, hze⟩ := hmass X
  have hgap : 0 ≤ M - m := sub_nonneg.mpr X.hmM
  set nu := (aux_prop_conc_pair_data_nu X (aux_prop_conc_pair_data_slopes d)
    (centeredCube z r hr : Set (SpatialCoordinates d))).toReal with hnu_def
  set ze := (aux_prop_conc_pair_data_zeta X (aux_prop_conc_pair_data_slopes d)
    (centeredCube z r hr : Set (SpatialCoordinates d))).toReal with hze_def
  have hnu0 : 0 ≤ nu := ENNReal.toReal_nonneg
  have hze0 : 0 ≤ ze := ENNReal.toReal_nonneg
  have hsq : Real.sqrt (nu * ze) ≤ C2 * (M - m) := by
    calc Real.sqrt (nu * ze) ≤ Real.sqrt (C2 * (C2 * (M - m) ^ 2)) :=
          Real.sqrt_le_sqrt (mul_le_mul hnu hze hze0 hC2.le)
      _ = Real.sqrt ((C2 * (M - m)) ^ 2) := by congr 1; ring
      _ = C2 * (M - m) := Real.sqrt_sq (mul_nonneg hC2.le hgap)
  have hbr : (M - m) * nu + Real.sqrt (nu * ze) ≤ 2 * C2 * (M - m) := by
    nlinarith [mul_le_mul_of_nonneg_left hnu hgap]
  have hC1S : 0 ≤ C1 * S * Real.exp (C1 * S) := by positivity
  calc |aux_prop_conc_pair_data_theta X c p g1 - aux_prop_conc_pair_data_theta X c p (fun _ => 0)|
      ≤ C1 * S * Real.exp (C1 * S) * ((M - m) * nu + Real.sqrt (nu * ze)) := hb
    _ ≤ C1 * S * Real.exp (C1 * S) * (2 * C2 * (M - m)) :=
        mul_le_mul_of_nonneg_left hbr hC1S
    _ = (2 * C1 * C2) * S * Real.exp (C1 * S) * (M - m) := by ring
    _ ≤ (2 * C1 * C2 + C1) * S * Real.exp ((2 * C1 * C2 + C1) * S) * (M - m) := by
        have hexp : Real.exp (C1 * S) ≤ Real.exp ((2 * C1 * C2 + C1) * S) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by nlinarith [mul_pos hC1 hC2]) hS)
        have hcoef : 2 * C1 * C2 ≤ 2 * C1 * C2 + C1 := by linarith
        have h0 : 0 ≤ (2 * C1 * C2) * S := by positivity
        calc (2 * C1 * C2) * S * Real.exp (C1 * S) * (M - m)
            ≤ (2 * C1 * C2 + C1) * S * Real.exp ((2 * C1 * C2 + C1) * S) * (M - m) := by
              apply mul_le_mul_of_nonneg_right _ hgap
              exact mul_le_mul (mul_le_mul_of_nonneg_right hcoef hS) hexp (Real.exp_pos _).le
                (by positivity)

end
end Paper
