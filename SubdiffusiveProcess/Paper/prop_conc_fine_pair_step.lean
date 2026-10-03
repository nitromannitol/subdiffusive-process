module

public import SubdiffusiveProcess.Paper.prop_conc_deletion_cost
public import SubdiffusiveProcess.Paper.prop_conc_masked_delta_bounds
public import SubdiffusiveProcess.Paper.relative_response_variation

@[expose] public section



set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators
namespace Paper
noncomputable section

section helpers
variable {d : ℕ} {Q : Opens (SpatialCoordinates d)} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
  {C0 m M : ℝ}

/-- Only the values of the weight on the cell matter. -/
theorem aux_prop_conc_fine_pair_step_theta_congr (X : prop_conc_pair_data Q z r hr C0 m M) (c : ℝ)
    (p : Fin d → ℝ) (g h : SpatialCoordinates d → ℝ)
    (hgh : ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), g x = h x) :
    aux_prop_conc_pair_data_theta X c p g = aux_prop_conc_pair_data_theta X c p h := by
  have hq : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen.measurableSet
  have hw : ∀ {E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d)))}
      (Gamma : DirichletForm.EnergyMeasure E) (v : DomainL2 Q),
      aux_prop_conc_pair_data_wenergy Gamma (centeredCube z r hr : Set (SpatialCoordinates d)) g v =
        aux_prop_conc_pair_data_wenergy Gamma (centeredCube z r hr : Set (SpatialCoordinates d)) h v := by
    intro E Gamma v
    unfold aux_prop_conc_pair_data_wenergy
    congr 1
    exact setLIntegral_congr_fun hq (fun x hx => by rw [hgh x hx])
  unfold aux_prop_conc_pair_data_theta aux_prop_conc_pair_data_wInfE aux_prop_conc_pair_data_wInfF
  simp only [hw]

/-- Composition law for the canonical masked pair: the relative response of `mask X g` for the weight `h`
is that of `X` for the weight `g + h`. -/
theorem aux_prop_conc_fine_pair_step_theta_mask (X : prop_conc_pair_data Q z r hr C0 m M)
    (g : SpatialCoordinates d → ℝ) (hg : Measurable g) (K : ℝ) (hK : ∀ x, |g x| ≤ K)
    (c : ℝ) (p : Fin d → ℝ) (h : SpatialCoordinates d → ℝ) (hh : Measurable h) :
    aux_prop_conc_pair_data_theta (aux_prop_conc_pair_mask_pair X g hg K hK) c p h =
      aux_prop_conc_pair_data_theta X c p (g + h) := by
  let W := Classical.choice (aux_prop_conc_pair_mask_exists X g hg K hK)
  have hq : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen.measurableSet
  have hdE : (aux_prop_conc_pair_mask_of X hg hK W).E.domain = X.E.domain := W.Edata.domain_eq
  have hdF : (aux_prop_conc_pair_mask_of X hg hK W).F.domain = X.F.domain := W.Fdata.domain_eq
  have hcls : ∀ (p : Fin d → ℝ) (v : DomainL2 Q),
      v - ((aux_prop_conc_pair_mask_of X hg hK W).P.boundary p : DomainL2 Q) ∈ X.D ↔
        v - (X.P.boundary p : DomainL2 Q) ∈ X.D := by
    intro p v
    have hd : (((aux_prop_conc_pair_mask_of X hg hK W).P.boundary p : DomainL2 Q) -
        (X.P.boundary p : DomainL2 Q)) ∈ X.D := W.traceEg p
    constructor
    · intro h
      have := X.D.add_mem h hd
      simpa only [sub_add_sub_cancel] using this
    · intro h
      have := X.D.sub_mem h hd
      simpa only [sub_sub_sub_cancel_right] using this
  show aux_prop_conc_pair_data_theta (aux_prop_conc_pair_mask_of X hg hK W) c p h = _
  have hE : ∀ p', aux_prop_conc_pair_data_wInfE (aux_prop_conc_pair_mask_of X hg hK W) h p' =
      aux_prop_conc_pair_data_wInfE X (g + h) p' := by
    intro p'
    unfold aux_prop_conc_pair_data_wInfE
    congr 1
    ext e
    constructor
    · rintro ⟨v, hv, hvD, rfl⟩
      have hvX : v ∈ X.E.domain := hdE ▸ hv
      refine ⟨v, hvX, (hcls p' v).1 hvD, ?_⟩
      exact aux_prop_conc_pair_mask_wenergy X.GammaE W.Edata.Gamma _ hq g h hg hh v
        (W.Edata.weight v hvX)
    · rintro ⟨v, hvX, hvD, rfl⟩
      refine ⟨v, hdE ▸ hvX, (hcls p' v).2 hvD, ?_⟩
      exact (aux_prop_conc_pair_mask_wenergy X.GammaE W.Edata.Gamma _ hq g h hg hh v
        (W.Edata.weight v hvX)).symm
  have hF : ∀ p', aux_prop_conc_pair_data_wInfF (aux_prop_conc_pair_mask_of X hg hK W) h p' =
      aux_prop_conc_pair_data_wInfF X (g + h) p' := by
    intro p'
    unfold aux_prop_conc_pair_data_wInfF
    congr 1
    ext e
    constructor
    · rintro ⟨v, hv, hvD, rfl⟩
      have hvX : v ∈ X.F.domain := hdF ▸ hv
      refine ⟨v, hvX, (hcls p' v).1 hvD, ?_⟩
      exact aux_prop_conc_pair_mask_wenergy X.GammaF W.Fdata.Gamma _ hq g h hg hh v
        (W.Fdata.weight v hvX)
    · rintro ⟨v, hvX, hvD, rfl⟩
      refine ⟨v, hdF ▸ hvX, (hcls p' v).2 hvD, ?_⟩
      exact (aux_prop_conc_pair_mask_wenergy X.GammaF W.Fdata.Gamma _ hq g h hg hh v
        (W.Fdata.weight v hvX)).symm
  unfold aux_prop_conc_pair_data_theta
  simp only [hE, hF]

/-- The common form order passes to the local responses. -/
theorem aux_prop_conc_fine_pair_step_response_order (X : prop_conc_pair_data Q z r hr C0 m M)
    (p : Fin d → ℝ) : m * X.P.QE p ≤ X.P.QF p ∧ X.P.QF p ≤ M * X.P.QE p := by
  have hm0 : 0 < m := aux_prop_conc_pair_mask_mpos X
  have hord := energy_order_of_form_order Q X.E X.F X.hEc X.hEl X.hFc X.hFl X.P.domain_eq
    X.GammaE X.GammaF m M hm0 X.horder
  have hq : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen.measurableSet
  have huFE : (X.P.uF p : DomainL2 Q) ∈ X.E.domain := X.P.domain_eq ▸ X.P.memF p
  have hbF : (X.P.boundary p : DomainL2 Q) ∈ X.F.domain := X.P.domain_eq ▸ (X.P.boundary p).property
  constructor
  · calc m * X.P.QE p ≤ m * (X.GammaE.measure (X.P.uF p) (centeredCube z r hr : Set _)).toReal := by
          rw [X.P.responseE p]
          exact mul_le_mul_of_nonneg_left (X.P.minE p (X.P.uF p) huFE (X.P.traceF p)) hm0.le
      _ ≤ (X.GammaF.measure (X.P.uF p) (centeredCube z r hr : Set _)).toReal :=
          (hord _ huFE _ hq).1
      _ = X.P.QF p := (X.P.responseF p).symm
  · calc X.P.QF p = (X.GammaF.measure (X.P.uF p) (centeredCube z r hr : Set _)).toReal :=
          X.P.responseF p
      _ ≤ (X.GammaF.measure (X.P.boundary p) (centeredCube z r hr : Set _)).toReal :=
          X.P.minF p _ hbF (by simpa only [sub_self] using X.D.zero_mem)
      _ ≤ M * (X.GammaE.measure (X.P.boundary p) (centeredCube z r hr : Set _)).toReal :=
          (hord _ (X.P.boundary p).property _ hq).2
      _ = M * X.P.QE p := by rw [X.P.responseE p]

theorem aux_prop_conc_fine_pair_step_QE_nonneg (X : prop_conc_pair_data Q z r hr C0 m M)
    (p : Fin d → ℝ) : 0 ≤ X.P.QE p := by
  rw [X.P.responseE p]; exact ENNReal.toReal_nonneg

/-- The relative response for the trivial weight is at most the endpoint gap times a dimensional
constant. -/
theorem aux_prop_conc_fine_pair_step_theta_zero_abs (X : prop_conc_pair_data Q z r hr C0 m M)
    (c : ℝ) (hc : c ∈ Set.Icc m M) (p : Fin d → ℝ) :
    |aux_prop_conc_pair_data_theta X c p (fun _ => 0)| ≤
      (2 ^ d * ∑ i : Fin d, (p i) ^ 2) * (M - m) := by
  rw [aux_prop_conc_pair_mask_theta_zero]
  have hD := X.hDpos
  have hQ0 := aux_prop_conc_fine_pair_step_QE_nonneg X
  obtain ⟨h1, h2⟩ := aux_prop_conc_fine_pair_step_response_order X p
  have hq := aux_relative_response_variation_quad_bound d X.P.QE hQ0
    (∑ i : Fin d, X.P.QE (Pi.single i 1)) rfl p
  have hE := hQ0 p
  have habs : |X.P.QF p - c * X.P.QE p| ≤ (M - m) * X.P.QE p := by
    rw [abs_le]
    constructor <;> nlinarith [hc.1, hc.2]
  rw [abs_div, abs_of_pos hD, div_le_iff₀ hD]
  calc |X.P.QF p - c * X.P.QE p| ≤ (M - m) * X.P.QE p := habs
    _ ≤ (M - m) * (2 ^ d * (∑ i : Fin d, (p i) ^ 2) * ∑ i : Fin d, X.P.QE (Pi.single i 1)) :=
        mul_le_mul_of_nonneg_left hq (by linarith [hc.1, hc.2])
    _ = (2 ^ d * ∑ i : Fin d, (p i) ^ 2) * (M - m) * ∑ i : Fin d, X.P.QE (Pi.single i 1) := by ring

/-- Every weighted relative response is bounded by the same constant times the endpoint gap. -/
theorem aux_prop_conc_fine_pair_step_theta_abs (X : prop_conc_pair_data Q z r hr C0 m M)
    (c : ℝ) (hc : c ∈ Set.Icc m M) (p : Fin d → ℝ) (g : SpatialCoordinates d → ℝ)
    (hg : Measurable g) (K : ℝ) (hK : ∀ x, |g x| ≤ K) :
    |aux_prop_conc_pair_data_theta X c p g| ≤ (2 ^ d * ∑ i : Fin d, (p i) ^ 2) * (M - m) := by
  have h := aux_prop_conc_fine_pair_step_theta_mask X g hg K hK c p (fun _ => 0) measurable_const
  have e : g + (fun _ => (0 : ℝ)) = g := by funext x; simp
  rw [e] at h
  rw [← h]
  exact aux_prop_conc_fine_pair_step_theta_zero_abs _ c hc p

/-- The normalized mass `ν(B)` of a pair. -/
def aux_prop_conc_fine_pair_step_nu {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r} {C0 m M : ℝ}
    (X : prop_conc_pair_data Q z r hr C0 m M) (B : Set (SpatialCoordinates d)) : ℝ :=
  (aux_prop_conc_pair_data_nu X (aux_prop_conc_pair_data_slopes d) B).toReal

/-- The normalized difference mass `ζ(B)` of a pair. -/
def aux_prop_conc_fine_pair_step_zeta {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r} {C0 m M : ℝ}
    (X : prop_conc_pair_data Q z r hr C0 m M) (B : Set (SpatialCoordinates d)) : ℝ :=
  (aux_prop_conc_pair_data_zeta X (aux_prop_conc_pair_data_slopes d) B).toReal

/-- Piece variation: a weight `h` supported in `B ⊆ q` changes `θ_X(w+u)` by the relative-variation bound in
the masses of the doubly masked pair `Z' = mask (mask X w) u`. -/
def aux_prop_conc_fine_pair_step_Piece (C0 : ℝ) (_hC0 : 1 ≤ C0) (d : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ {Q : Opens (SpatialCoordinates d)} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r} {m M : ℝ}
      (X : prop_conc_pair_data Q z r hr C0 m M) (c : ℝ), c ∈ Set.Icc m M →
      ∀ p ∈ aux_prop_conc_pair_data_slopes d,
      ∀ (w u h : SpatialCoordinates d → ℝ) (hw : Measurable w) (Kw : ℝ) (hKw : ∀ x, |w x| ≤ Kw)
        (hu : Measurable u) (Ku : ℝ) (hKu : ∀ x, |u x| ≤ Ku), Measurable h →
        ∀ (B : Set (SpatialCoordinates d)), MeasurableSet B →
        B ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) → (∀ x, x ∉ B → h x = 0) →
        ∀ G : ℝ, 0 ≤ G → (∀ x, |h x| ≤ G) →
        |aux_prop_conc_pair_data_theta X c p (w + u + h) - aux_prop_conc_pair_data_theta X c p (w + u)| ≤
          C * G * Real.exp (C * G) *
            ((M - m) * aux_prop_conc_fine_pair_step_nu
                (aux_prop_conc_pair_mask_pair (aux_prop_conc_pair_mask_pair X w hw Kw hKw) u hu Ku hKu) B +
              Real.sqrt (aux_prop_conc_fine_pair_step_nu
                  (aux_prop_conc_pair_mask_pair (aux_prop_conc_pair_mask_pair X w hw Kw hKw) u hu Ku hKu) B *
                aux_prop_conc_fine_pair_step_zeta
                  (aux_prop_conc_pair_mask_pair (aux_prop_conc_pair_mask_pair X w hw Kw hKw) u hu Ku hKu) B))

theorem aux_prop_conc_fine_pair_step_piece (C0 : ℝ) (hC0 : 1 ≤ C0) (d : ℕ) :
    aux_prop_conc_fine_pair_step_Piece C0 hC0 d := by
  obtain ⟨C, hC, hdc⟩ := prop_conc_deletion_cost C0 hC0
  refine ⟨C, hC, ?_⟩
  intro Q z r hr m M X c hc p hp w u h hw Kw hKw hu Ku hKu hh B hB hBq hsupp G hG0 hG
  have h1 := (hdc (aux_prop_conc_pair_mask_pair (aux_prop_conc_pair_mask_pair X w hw Kw hKw) u hu Ku hKu)
    c hc p hp h hh B hB hBq hsupp G hG0 hG).1
  rw [aux_prop_conc_fine_pair_step_theta_mask _ u hu Ku hKu c p h hh,
    aux_prop_conc_fine_pair_step_theta_mask _ u hu Ku hKu c p (fun _ => 0) measurable_const,
    aux_prop_conc_fine_pair_step_theta_mask X w hw Kw hKw c p (u + h) (hu.add hh),
    aux_prop_conc_fine_pair_step_theta_mask X w hw Kw hKw c p (u + fun _ => 0)
      (hu.add measurable_const)] at h1
  have e1 : w + (u + h) = w + u + h := (add_assoc _ _ _).symm
  have e2 : u + (fun _ : SpatialCoordinates d => (0 : ℝ)) = u := by funext x; simp
  rw [e1, e2] at h1
  exact h1

/-- Every weighted relative response is at most `C (M - m)`. -/
def aux_prop_conc_fine_pair_step_Bounded (C0 : ℝ) (d : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ {Q : Opens (SpatialCoordinates d)} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r} {m M : ℝ}
      (X : prop_conc_pair_data Q z r hr C0 m M) (c : ℝ), c ∈ Set.Icc m M →
      ∀ p ∈ aux_prop_conc_pair_data_slopes d,
      ∀ (g : SpatialCoordinates d → ℝ), Measurable g → ∀ K : ℝ, (∀ x, |g x| ≤ K) →
        |aux_prop_conc_pair_data_theta X c p g| ≤ C * (M - m)

theorem aux_prop_conc_fine_pair_step_bounded (C0 : ℝ) (d : ℕ) :
    aux_prop_conc_fine_pair_step_Bounded C0 d := by
  let A : ℝ := 2 ^ d * ∑ v ∈ aux_prop_conc_pair_data_slopes d, ∑ i : Fin d, (v i) ^ 2
  have hA : 0 ≤ A := by positivity
  refine ⟨A + 1, by linarith, ?_⟩
  intro Q z r hr m M X c hc p hp g hg K hK
  have h := aux_prop_conc_fine_pair_step_theta_abs X c hc p g hg K hK
  refine h.trans ?_
  have hgap : 0 ≤ M - m := sub_nonneg.mpr X.hmM
  have hsl : 2 ^ d * ∑ i : Fin d, (p i) ^ 2 ≤ A := by
    have : ∑ i : Fin d, (p i) ^ 2 ≤ ∑ v ∈ aux_prop_conc_pair_data_slopes d, ∑ i : Fin d, (v i) ^ 2 :=
      Finset.single_le_sum (f := fun v : Fin d → ℝ => ∑ i : Fin d, (v i) ^ 2)
        (fun v _ => Finset.sum_nonneg fun i _ => sq_nonneg _) hp
    exact mul_le_mul_of_nonneg_left this (by positivity)
  exact mul_le_mul_of_nonneg_right (by linarith) hgap

/-- Lipschitz continuity in the sup norm on the cell. -/
def aux_prop_conc_fine_pair_step_Lip (C0 : ℝ) (_hC0 : 1 ≤ C0) (d : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ {Q : Opens (SpatialCoordinates d)} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r} {m M : ℝ}
      (X : prop_conc_pair_data Q z r hr C0 m M) (c : ℝ), c ∈ Set.Icc m M →
      ∀ p ∈ aux_prop_conc_pair_data_slopes d,
      ∀ (g₁ g₂ : SpatialCoordinates d → ℝ), Measurable g₁ → Measurable g₂ →
        ∀ K : ℝ, (∀ x, |g₁ x| ≤ K) → (∀ x, |g₂ x| ≤ K) →
        ∀ G : ℝ, 0 ≤ G → (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), |g₁ x - g₂ x| ≤ G) →
          |aux_prop_conc_pair_data_theta X c p g₁ - aux_prop_conc_pair_data_theta X c p g₂| ≤
            C * G * Real.exp (C * G) * (M - m)

theorem aux_prop_conc_fine_pair_step_lip (C0 : ℝ) (hC0 : 1 ≤ C0) (d : ℕ) :
    aux_prop_conc_fine_pair_step_Lip C0 hC0 d := by
  obtain ⟨C1, hC1, hdc⟩ := prop_conc_deletion_cost C0 hC0
  obtain ⟨C2, hC2, hmb⟩ := prop_conc_masked_delta_bounds C0 hC0 d
  refine ⟨max (2 * C1 * C2) C1, lt_max_of_lt_right hC1, ?_⟩
  intro Q z r hr m M X c hc p hp g₁ g₂ hg₁ hg₂ K hK₁ hK₂ G hG0 hG
  have hq : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen.measurableSet
  set q : Set (SpatialCoordinates d) := (centeredCube z r hr : Set (SpatialCoordinates d)) with hqdef
  set h : SpatialCoordinates d → ℝ := q.indicator (fun x => g₁ x - g₂ x) with hh
  have hhm : Measurable h := (hg₁.sub hg₂).indicator hq
  have hsupp : ∀ x, x ∉ q → h x = 0 := fun x hx => Set.indicator_of_notMem hx _
  have hbd : ∀ x, |h x| ≤ G := by
    intro x
    by_cases hx : x ∈ q
    · simp only [hh]; rw [Set.indicator_of_mem hx]; exact hG x hx
    · rw [hsupp x hx]; simpa using hG0
  have hY := (hdc (aux_prop_conc_pair_mask_pair X g₂ hg₂ K hK₂) c hc p hp h hhm q hq subset_rfl hsupp
    G hG0 hbd).1
  have hθ1 : aux_prop_conc_pair_data_theta X c p g₁ = aux_prop_conc_pair_data_theta X c p (g₂ + h) := by
    refine aux_prop_conc_fine_pair_step_theta_congr X c p _ _ (fun x hx => ?_)
    simp only [hh, Pi.add_apply]
    rw [Set.indicator_of_mem (show x ∈ q from hx)]
    ring
  have hθ2 : aux_prop_conc_pair_data_theta X c p g₂ =
      aux_prop_conc_pair_data_theta X c p (g₂ + fun _ => 0) := by
    congr 1; funext x; simp
  rw [hθ1, hθ2, ← aux_prop_conc_fine_pair_step_theta_mask X g₂ hg₂ K hK₂ c p h hhm,
    ← aux_prop_conc_fine_pair_step_theta_mask X g₂ hg₂ K hK₂ c p (fun _ => 0) measurable_const]
  refine hY.trans ?_
  -- the masses of the masked pair
  obtain ⟨hmass, -⟩ := hmb X
  obtain ⟨hnu, hze⟩ := hmass (aux_prop_conc_pair_mask_pair X g₂ hg₂ K hK₂)
  have hgap : 0 ≤ M - m := sub_nonneg.mpr X.hmM
  have hnu0 : 0 ≤ (aux_prop_conc_pair_data_nu (aux_prop_conc_pair_mask_pair X g₂ hg₂ K hK₂)
      (aux_prop_conc_pair_data_slopes d) q).toReal := ENNReal.toReal_nonneg
  have hze0 : 0 ≤ (aux_prop_conc_pair_data_zeta (aux_prop_conc_pair_mask_pair X g₂ hg₂ K hK₂)
      (aux_prop_conc_pair_data_slopes d) q).toReal := ENNReal.toReal_nonneg
  have hsq : Real.sqrt ((aux_prop_conc_pair_data_nu (aux_prop_conc_pair_mask_pair X g₂ hg₂ K hK₂)
      (aux_prop_conc_pair_data_slopes d) q).toReal *
      (aux_prop_conc_pair_data_zeta (aux_prop_conc_pair_mask_pair X g₂ hg₂ K hK₂)
        (aux_prop_conc_pair_data_slopes d) q).toReal) ≤ C2 * (M - m) := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    calc _ ≤ C2 * (C2 * (M - m) ^ 2) := mul_le_mul hnu hze hze0 hC2.le
      _ = (C2 * (M - m)) ^ 2 := by ring
  have hbr : (M - m) * (aux_prop_conc_pair_data_nu (aux_prop_conc_pair_mask_pair X g₂ hg₂ K hK₂)
      (aux_prop_conc_pair_data_slopes d) q).toReal +
      Real.sqrt ((aux_prop_conc_pair_data_nu (aux_prop_conc_pair_mask_pair X g₂ hg₂ K hK₂)
      (aux_prop_conc_pair_data_slopes d) q).toReal *
      (aux_prop_conc_pair_data_zeta (aux_prop_conc_pair_mask_pair X g₂ hg₂ K hK₂)
        (aux_prop_conc_pair_data_slopes d) q).toReal) ≤ 2 * C2 * (M - m) := by
    nlinarith [mul_le_mul_of_nonneg_left hnu hgap]
  have hbr0 : 0 ≤ (M - m) * (aux_prop_conc_pair_data_nu (aux_prop_conc_pair_mask_pair X g₂ hg₂ K hK₂)
      (aux_prop_conc_pair_data_slopes d) q).toReal +
      Real.sqrt ((aux_prop_conc_pair_data_nu (aux_prop_conc_pair_mask_pair X g₂ hg₂ K hK₂)
      (aux_prop_conc_pair_data_slopes d) q).toReal *
      (aux_prop_conc_pair_data_zeta (aux_prop_conc_pair_mask_pair X g₂ hg₂ K hK₂)
        (aux_prop_conc_pair_data_slopes d) q).toReal) := by positivity
  have hCm : max (2 * C1 * C2) C1 ≥ C1 := le_max_right _ _
  have hC12 : (2 * C1 * C2) ≤ max (2 * C1 * C2) C1 := le_max_left _ _
  calc C1 * G * Real.exp (C1 * G) * _ ≤ C1 * G * Real.exp (C1 * G) * (2 * C2 * (M - m)) :=
        mul_le_mul_of_nonneg_left hbr (by positivity)
    _ = (2 * C1 * C2) * G * Real.exp (C1 * G) * (M - m) := by ring
    _ ≤ max (2 * C1 * C2) C1 * G * Real.exp (max (2 * C1 * C2) C1 * G) * (M - m) := by
        have h1 : Real.exp (C1 * G) ≤ Real.exp (max (2 * C1 * C2) C1 * G) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hCm hG0)
        have h2 : 2 * C1 * C2 * G ≤ max (2 * C1 * C2) C1 * G := mul_le_mul_of_nonneg_right hC12 hG0
        have h3 : 0 ≤ 2 * C1 * C2 * G := by positivity
        exact mul_le_mul_of_nonneg_right (mul_le_mul h2 h1 (Real.exp_pos _).le
          (h3.trans h2)) hgap

/-- Deletion step: a weight `u` supported in a small set `B` with `ν_{mask X w}(B) ≤ Ks a` changes `θ_X(w)` by
`C G e^{CG} Δ (Ks a + √(C0² A_d) √Ks √a)`. -/
def aux_prop_conc_fine_pair_step_Delete (C0 : ℝ) (_hC0 : 1 ≤ C0) (d : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ {Q : Opens (SpatialCoordinates d)} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r} {m M : ℝ}
      (X : prop_conc_pair_data Q z r hr C0 m M) (c : ℝ), c ∈ Set.Icc m M →
      ∀ p ∈ aux_prop_conc_pair_data_slopes d,
      ∀ (w u : SpatialCoordinates d → ℝ) (hw : Measurable w) (Kw : ℝ) (hKw : ∀ x, |w x| ≤ Kw),
        Measurable u →
        ∀ (B : Set (SpatialCoordinates d)), MeasurableSet B →
        B ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) → (∀ x, x ∉ B → u x = 0) →
        ∀ G : ℝ, 0 ≤ G → (∀ x, |u x| ≤ G) →
        ∀ Ks a : ℝ, 0 ≤ Ks → 0 ≤ a →
          aux_prop_conc_fine_pair_step_nu (aux_prop_conc_pair_mask_pair X w hw Kw hKw) B ≤ Ks * a →
          |aux_prop_conc_pair_data_theta X c p (w + u) - aux_prop_conc_pair_data_theta X c p w| ≤
            C * G * Real.exp (C * G) * (M - m) *
              (Ks * a + Real.sqrt (C0 ^ 2 * ((2 : ℝ) ^ d *
                ∑ v ∈ aux_prop_conc_pair_data_slopes d, ∑ i : Fin d, (v i) ^ 2)) *
                Real.sqrt Ks * Real.sqrt a)

theorem aux_prop_conc_fine_pair_step_delete (C0 : ℝ) (hC0 : 1 ≤ C0) (d : ℕ) :
    aux_prop_conc_fine_pair_step_Delete C0 hC0 d := by
  obtain ⟨C, hC, hdc⟩ := prop_conc_deletion_cost C0 hC0
  refine ⟨C, hC, ?_⟩
  intro Q z r hr m M X c hc p hp w u hw Kw hKw hu B hB hBq hsupp G hG0 hG Ks a hKs ha hnu
  have h2 := (hdc (aux_prop_conc_pair_mask_pair X w hw Kw hKw) c hc p hp u hu B hB hBq hsupp G hG0 hG).2
    Ks a hKs ha hnu
  rw [aux_prop_conc_fine_pair_step_theta_mask X w hw Kw hKw c p u hu,
    aux_prop_conc_fine_pair_step_theta_mask X w hw Kw hKw c p (fun _ => 0) measurable_const] at h2
  have e2 : w + (fun _ : SpatialCoordinates d => (0 : ℝ)) = w := by funext x; simp
  rw [e2] at h2
  exact h2

/-- **Deterministic estimates for the fine-layer step.**  Boundedness, sup-norm Lipschitz continuity, the
deletion step and the piece variation of the weighted relative response `θ_X`. -/
theorem prop_conc_fine_pair_step (C0 : ℝ) (hC0 : 1 ≤ C0) (d : ℕ) :
    aux_prop_conc_fine_pair_step_Bounded C0 d ∧ aux_prop_conc_fine_pair_step_Lip C0 hC0 d ∧
      aux_prop_conc_fine_pair_step_Delete C0 hC0 d ∧ aux_prop_conc_fine_pair_step_Piece C0 hC0 d :=
  ⟨aux_prop_conc_fine_pair_step_bounded C0 d, aux_prop_conc_fine_pair_step_lip C0 hC0 d,
    aux_prop_conc_fine_pair_step_delete C0 hC0 d, aux_prop_conc_fine_pair_step_piece C0 hC0 d⟩

end helpers

end
end Paper
