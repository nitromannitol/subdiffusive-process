import SubdiffusiveProcess.Paper.thm_prop_base

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

section Part0
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

section Ess

variable {d : ℕ} (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
  {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (GE GF : (i : ℕ) → Ω →
    DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ] DomainL2 (centeredCube (z i) (r i) (hr i)))

/-- The constants that are almost surely admissible lower comparison constants. -/
def aux_thm_prop_env_lowerAE : Set ℝ :=
  {a : ℝ | ∀ᵐ omega ∂P, a ∈ aux_thm_prop_lowerSet z r hr GE GF omega}

/-- The constants that are almost surely admissible upper comparison constants. -/
def aux_thm_prop_env_upperAE : Set ℝ :=
  {a : ℝ | ∀ᵐ omega ∂P, a ∈ aux_thm_prop_upperSet z r hr GE GF omega}

theorem aux_thm_prop_env_lowerSet_closed (omega : Ω) :
    IsClosed (aux_thm_prop_lowerSet z r hr GE GF omega) := by
  have : aux_thm_prop_lowerSet z r hr GE GF omega =
      ⋂ i : ℕ, ⋂ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
        {a : ℝ | u ∈ limitFormDomain (GE i omega) →
          a * (limitFormEnergy (GE i omega) u).toReal ≤ (limitFormEnergy (GF i omega) u).toReal} := by
    ext a; simp [aux_thm_prop_lowerSet]
  rw [this]
  refine isClosed_iInter fun i => isClosed_iInter fun u => ?_
  by_cases hu : u ∈ limitFormDomain (GE i omega)
  · simp only [hu, forall_true_left]
    exact isClosed_le (continuous_id.mul continuous_const) continuous_const
  · simp [hu]

theorem aux_thm_prop_env_upperSet_closed (omega : Ω) :
    IsClosed (aux_thm_prop_upperSet z r hr GE GF omega) := by
  have : aux_thm_prop_upperSet z r hr GE GF omega =
      ⋂ i : ℕ, ⋂ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
        {a : ℝ | u ∈ limitFormDomain (GE i omega) →
          (limitFormEnergy (GF i omega) u).toReal ≤ a * (limitFormEnergy (GE i omega) u).toReal} := by
    ext a; simp [aux_thm_prop_upperSet]
  rw [this]
  refine isClosed_iInter fun i => isClosed_iInter fun u => ?_
  by_cases hu : u ∈ limitFormDomain (GE i omega)
  · simp only [hu, forall_true_left]
    exact isClosed_le continuous_const (continuous_id.mul continuous_const)
  · simp [hu]


theorem aux_thm_prop_env_lowerAE_mem (C0 : ℝ)
    (hcomp : ∀ᵐ omega ∂P, aux_thm_prop_compare z r hr GE GF C0 omega) :
    C0⁻¹ ∈ aux_thm_prop_env_lowerAE z r hr P GE GF := by
  filter_upwards [hcomp] with omega h i u hu
  exact ((h i).2 u hu).1

theorem aux_thm_prop_env_upperAE_mem (C0 : ℝ)
    (hcomp : ∀ᵐ omega ∂P, aux_thm_prop_compare z r hr GE GF C0 omega) :
    C0 ∈ aux_thm_prop_env_upperAE z r hr P GE GF := by
  filter_upwards [hcomp] with omega h i u hu
  exact ((h i).2 u hu).2

/-- A common energy value witnessing a positive quadratic form. -/
theorem aux_thm_prop_env_lowerAE_le (C0 : ℝ)
    (hcomp : ∀ᵐ omega ∂P, aux_thm_prop_compare z r hr GE GF C0 omega)
    (hnz : ∀ᵐ omega ∂P, aux_thm_prop_nonzero z r hr GE omega)
    {a : ℝ} (ha : a ∈ aux_thm_prop_env_lowerAE z r hr P GE GF) : a ≤ C0 := by
  haveI : (ae P).NeBot := IsProbabilityMeasure.ae_neBot
  have ha' : ∀ᵐ omega ∂P, a ∈ aux_thm_prop_lowerSet z r hr GE GF omega := ha
  obtain ⟨omega, h1, h2, i, u, hu, hpos⟩ := (ha'.and (hcomp.and hnz)).exists
  have h3 := h1 i u hu
  have h4 := ((h2 i).2 u hu).2
  by_contra hlt
  push_neg at hlt
  nlinarith

theorem aux_thm_prop_env_upperAE_ge (C0 : ℝ)
    (hcomp : ∀ᵐ omega ∂P, aux_thm_prop_compare z r hr GE GF C0 omega)
    (hnz : ∀ᵐ omega ∂P, aux_thm_prop_nonzero z r hr GE omega)
    {a : ℝ} (ha : a ∈ aux_thm_prop_env_upperAE z r hr P GE GF) : C0⁻¹ ≤ a := by
  haveI : (ae P).NeBot := IsProbabilityMeasure.ae_neBot
  have ha' : ∀ᵐ omega ∂P, a ∈ aux_thm_prop_upperSet z r hr GE GF omega := ha
  obtain ⟨omega, h1, h2, i, u, hu, hpos⟩ := (ha'.and (hcomp.and hnz)).exists
  have h3 := h1 i u hu
  have h4 := ((h2 i).2 u hu).1
  by_contra hlt
  push_neg at hlt
  nlinarith

/-- The essential lower endpoint of the two limit forms. -/
def aux_thm_prop_env_essLower : ℝ := sSup (aux_thm_prop_env_lowerAE z r hr P GE GF)

/-- The essential upper endpoint of the two limit forms. -/
def aux_thm_prop_env_essUpper : ℝ := sInf (aux_thm_prop_env_upperAE z r hr P GE GF)

theorem aux_thm_prop_env_essLower_mem (C0 : ℝ)
    (hcomp : ∀ᵐ omega ∂P, aux_thm_prop_compare z r hr GE GF C0 omega)
    (hnz : ∀ᵐ omega ∂P, aux_thm_prop_nonzero z r hr GE omega) :
    ∀ᵐ omega ∂P, aux_thm_prop_env_essLower z r hr P GE GF ∈
      aux_thm_prop_lowerSet z r hr GE GF omega := by
  obtain ⟨u, hmono, hlim, hmem⟩ := exists_seq_tendsto_sSup
    ⟨_, aux_thm_prop_env_lowerAE_mem z r hr P GE GF C0 hcomp⟩
    ⟨C0, fun a ha => aux_thm_prop_env_lowerAE_le z r hr P GE GF C0 hcomp hnz ha⟩
  have hall : ∀ᵐ omega ∂P, ∀ n, u n ∈ aux_thm_prop_lowerSet z r hr GE GF omega :=
    ae_all_iff.2 fun n => hmem n
  filter_upwards [hall] with omega h
  exact (aux_thm_prop_env_lowerSet_closed z r hr GE GF omega).mem_of_tendsto hlim
    (Eventually.of_forall h)

theorem aux_thm_prop_env_essUpper_mem (C0 : ℝ)
    (hcomp : ∀ᵐ omega ∂P, aux_thm_prop_compare z r hr GE GF C0 omega)
    (hnz : ∀ᵐ omega ∂P, aux_thm_prop_nonzero z r hr GE omega) :
    ∀ᵐ omega ∂P, aux_thm_prop_env_essUpper z r hr P GE GF ∈
      aux_thm_prop_upperSet z r hr GE GF omega := by
  obtain ⟨u, hmono, hlim, hmem⟩ := exists_seq_tendsto_sInf
    ⟨_, aux_thm_prop_env_upperAE_mem z r hr P GE GF C0 hcomp⟩
    ⟨C0⁻¹, fun a ha => aux_thm_prop_env_upperAE_ge z r hr P GE GF C0 hcomp hnz ha⟩
  have hall : ∀ᵐ omega ∂P, ∀ n, u n ∈ aux_thm_prop_upperSet z r hr GE GF omega :=
    ae_all_iff.2 fun n => hmem n
  filter_upwards [hall] with omega h
  exact (aux_thm_prop_env_upperSet_closed z r hr GE GF omega).mem_of_tendsto hlim
    (Eventually.of_forall h)

/-- Maximality of the essential lower endpoint. -/
theorem aux_thm_prop_env_essLower_max (C0 : ℝ)
    (hcomp : ∀ᵐ omega ∂P, aux_thm_prop_compare z r hr GE GF C0 omega)
    (hnz : ∀ᵐ omega ∂P, aux_thm_prop_nonzero z r hr GE omega)
    {eps : ℝ} (heps : 0 < eps)
    (h : ∀ᵐ omega ∂P, aux_thm_prop_env_essLower z r hr P GE GF + eps ∈
      aux_thm_prop_lowerSet z r hr GE GF omega) : False := by
  have hmem : aux_thm_prop_env_essLower z r hr P GE GF + eps ∈
      aux_thm_prop_env_lowerAE z r hr P GE GF := h
  have := le_csSup ⟨C0, fun a ha => aux_thm_prop_env_lowerAE_le z r hr P GE GF C0 hcomp hnz ha⟩ hmem
  unfold aux_thm_prop_env_essLower at this
  linarith

theorem aux_thm_prop_env_essUpper_max (C0 : ℝ)
    (hcomp : ∀ᵐ omega ∂P, aux_thm_prop_compare z r hr GE GF C0 omega)
    (hnz : ∀ᵐ omega ∂P, aux_thm_prop_nonzero z r hr GE omega)
    {eps : ℝ} (heps : 0 < eps)
    (h : ∀ᵐ omega ∂P, aux_thm_prop_env_essUpper z r hr P GE GF - eps ∈
      aux_thm_prop_upperSet z r hr GE GF omega) : False := by
  have hmem : aux_thm_prop_env_essUpper z r hr P GE GF - eps ∈
      aux_thm_prop_env_upperAE z r hr P GE GF := h
  have := csInf_le ⟨C0⁻¹, fun a ha => aux_thm_prop_env_upperAE_ge z r hr P GE GF C0 hcomp hnz ha⟩ hmem
  unfold aux_thm_prop_env_essUpper at this
  linarith

theorem aux_thm_prop_env_essLower_ge (C0 : ℝ)
    (hcomp : ∀ᵐ omega ∂P, aux_thm_prop_compare z r hr GE GF C0 omega)
    (hnz : ∀ᵐ omega ∂P, aux_thm_prop_nonzero z r hr GE omega) :
    C0⁻¹ ≤ aux_thm_prop_env_essLower z r hr P GE GF :=
  le_csSup ⟨C0, fun a ha => aux_thm_prop_env_lowerAE_le z r hr P GE GF C0 hcomp hnz ha⟩
    (aux_thm_prop_env_lowerAE_mem z r hr P GE GF C0 hcomp)

theorem aux_thm_prop_env_essUpper_le (C0 : ℝ)
    (hcomp : ∀ᵐ omega ∂P, aux_thm_prop_compare z r hr GE GF C0 omega)
    (hnz : ∀ᵐ omega ∂P, aux_thm_prop_nonzero z r hr GE omega) :
    aux_thm_prop_env_essUpper z r hr P GE GF ≤ C0 :=
  csInf_le ⟨C0⁻¹, fun a ha => aux_thm_prop_env_upperAE_ge z r hr P GE GF C0 hcomp hnz ha⟩
    (aux_thm_prop_env_upperAE_mem z r hr P GE GF C0 hcomp)

theorem aux_thm_prop_env_essLower_le_essUpper (C0 : ℝ)
    (hcomp : ∀ᵐ omega ∂P, aux_thm_prop_compare z r hr GE GF C0 omega)
    (hnz : ∀ᵐ omega ∂P, aux_thm_prop_nonzero z r hr GE omega) :
    aux_thm_prop_env_essLower z r hr P GE GF ≤ aux_thm_prop_env_essUpper z r hr P GE GF := by
  haveI : (ae P).NeBot := IsProbabilityMeasure.ae_neBot
  obtain ⟨omega, h1, h2, i, u, hu, hpos⟩ :=
    ((aux_thm_prop_env_essLower_mem z r hr P GE GF C0 hcomp hnz).and
      ((aux_thm_prop_env_essUpper_mem z r hr P GE GF C0 hcomp hnz).and hnz)).exists
  have h3 := h1 i u hu
  have h4 := h2 i u hu
  by_contra hlt
  push_neg at hlt
  nlinarith

/-- **Essential-endpoint assembly (route differs from the paper's `lem-endpoints`, same conclusion).**
The comparison, the nonvanishing and an improvement statement for deterministic constants
`m < M` that are almost sure endpoints give `F = cE` with `c` deterministic. -/
theorem thm_prop_env_endpoints (C0 : ℝ) (hC0 : 1 ≤ C0)
    (hcomp : ∀ᵐ omega ∂P, aux_thm_prop_compare z r hr GE GF C0 omega)
    (hnz : ∀ᵐ omega ∂P, aux_thm_prop_nonzero z r hr GE omega)
    (himp : ∀ m M : ℝ, C0⁻¹ ≤ m → m < M → M ≤ C0 →
      (∀ᵐ omega ∂P, m ∈ aux_thm_prop_lowerSet z r hr GE GF omega) →
      (∀ᵐ omega ∂P, M ∈ aux_thm_prop_upperSet z r hr GE GF omega) →
      (∀ eps : ℝ, 0 < eps → ¬ ∀ᵐ omega ∂P, m + eps ∈ aux_thm_prop_lowerSet z r hr GE GF omega) →
      (∀ eps : ℝ, 0 < eps → ¬ ∀ᵐ omega ∂P, M - eps ∈ aux_thm_prop_upperSet z r hr GE GF omega) →
      False) :
    ∃ c : ℝ, C0⁻¹ ≤ c ∧ c ≤ C0 ∧ ∀ᵐ omega ∂P, ∀ i : ℕ,
      limitFormDomain (GE i omega) = limitFormDomain (GF i omega) ∧
      ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
        u ∈ limitFormDomain (GE i omega) →
          (limitFormEnergy (GF i omega) u).toReal =
            c * (limitFormEnergy (GE i omega) u).toReal := by
  have hmM := aux_thm_prop_env_essLower_le_essUpper z r hr P GE GF C0 hcomp hnz
  have hmC := aux_thm_prop_env_essLower_ge z r hr P GE GF C0 hcomp hnz
  have hMC := aux_thm_prop_env_essUpper_le z r hr P GE GF C0 hcomp hnz
  have hmmem := aux_thm_prop_env_essLower_mem z r hr P GE GF C0 hcomp hnz
  have hMmem := aux_thm_prop_env_essUpper_mem z r hr P GE GF C0 hcomp hnz
  have hmax1 := fun eps (heps : 0 < eps) =>
    aux_thm_prop_env_essLower_max z r hr P GE GF C0 hcomp hnz heps
  have hmax2 := fun eps (heps : 0 < eps) =>
    aux_thm_prop_env_essUpper_max z r hr P GE GF C0 hcomp hnz heps
  generalize aux_thm_prop_env_essLower z r hr P GE GF = m at *
  generalize aux_thm_prop_env_essUpper z r hr P GE GF = M at *
  have heq : m = M := by
    by_contra hne
    exact himp m M hmC (lt_of_le_of_ne hmM hne) hMC hmmem hMmem hmax1 hmax2
  subst heq
  refine ⟨m, hmC, hMC, ?_⟩
  filter_upwards [hmmem, hMmem, hcomp] with omega h1 h2 h3 i
  exact ⟨(h3 i).1, fun u hu => le_antisymm (h2 i u hu) (h1 i u hu)⟩

end Ess

end Part0

section Part1
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

section Improve

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {z : ℕ → SpatialCoordinates d} {r : ℕ → ℝ} {hr : ∀ j, 0 < r j}
  {GE GF : (i : ℕ) → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
    DomainL2 (centeredCube (z i) (r i) (hr i))}

/-- **Improvement of the endpoint pair from the two local dichotomy branches.**  For deterministic
constants `0 < m < M`, either branch of the local saving statement improves one endpoint by the
factor `3/256` of the gap (the reciprocal branch after the algebra of the swapped pair). -/
theorem aux_thm_prop_env_improve_of_dichotomy (C0 : ℝ) (hC0 : 1 ≤ C0)
    (hsn : ∀ᵐ omega ∂P, ∀ i : ℕ,
      ((∀ x y : DomainL2 (centeredCube (z i) (r i) (hr i)),
          inner ℝ (GE i omega x) y = inner ℝ x (GE i omega y)) ∧
        (∀ x : DomainL2 (centeredCube (z i) (r i) (hr i)),
          0 ≤ inner ℝ x (GE i omega x))) ∧
      ((∀ x y : DomainL2 (centeredCube (z i) (r i) (hr i)),
          inner ℝ (GF i omega x) y = inner ℝ x (GF i omega y)) ∧
        (∀ x : DomainL2 (centeredCube (z i) (r i) (hr i)),
          0 ≤ inner ℝ x (GF i omega x))))
    (hcomp : ∀ᵐ omega ∂P, aux_thm_prop_compare z r hr GE GF C0 omega)
    (m M : ℝ) (hm : C0⁻¹ ≤ m) (hlt : m < M)
    (hdich :
      (∀ᵐ omega ∂P, ∀ i : ℕ,
        ∀ f ∈ aux_thm_prop_smoothSources (centeredCube (z i) (r i) (hr i)),
        ∀ c : ℝ, 0 < c → ∀ ε : ℝ, 0 < ε →
          aux_thm_prop_localSaving M (M - m)
            (limitFormEnergy (GE i omega) (GE i omega f)).toReal
            (limitFormEnergy (GF i omega) (GE i omega f)).toReal
            (volume (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))).toReal
            c ε) ∨
      (∀ᵐ omega ∂P, ∀ i : ℕ,
        ∀ f ∈ aux_thm_prop_smoothSources (centeredCube (z i) (r i) (hr i)),
        ∀ c : ℝ, 0 < c → ∀ ε : ℝ, 0 < ε →
          aux_thm_prop_localSaving m⁻¹ (m⁻¹ - M⁻¹)
            (limitFormEnergy (GF i omega) (GF i omega f)).toReal
            (limitFormEnergy (GE i omega) (GF i omega f)).toReal
            (volume (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))).toReal
            c ε)) :
    ∃ k1 : ℝ, 0 < k1 ∧
      ((∀ᵐ omega ∂P, M - k1 * (M - m) ∈ aux_thm_prop_upperSet z r hr GE GF omega) ∨
        (∀ᵐ omega ∂P, m + k1 * (M - m) ∈ aux_thm_prop_lowerSet z r hr GE GF omega)) := by
  have hcL0 : 0 < m := lt_of_lt_of_le (inv_pos.mpr (by linarith)) hm
  have hΔ : 0 ≤ M - m := sub_nonneg.mpr hlt.le
  have hk1 : (0 : ℝ) < 3 / 256 := by norm_num
  have hk11 : (3 / 256 : ℝ) ≤ 1 := by norm_num
  rcases hdich with hU | hV
  · refine ⟨3 / 256, hk1, Or.inl ?_⟩
    have hK : 0 ≤ M - 3 / 256 * (M - m) := by nlinarith only [hcL0, hlt, hk11]
    have hU' : ∀ᵐ omega ∂P, ∀ i : ℕ,
        ∀ f ∈ aux_thm_prop_smoothSources (centeredCube (z i) (r i) (hr i)),
          limitFormEnergy (GF i omega) (GE i omega f) ≤
            (((M - 3 / 256 * (M - m)) * inner ℝ f (GE i omega f) : ℝ) : EReal) := by
      filter_upwards [hU, hsn, hcomp] with omega homega hsn hc i f hf
      have hEr := aux_thm_prop_energy_range (GE i omega) (hsn i).1.1 (hsn i).1.2 f
      have hdomE : GE i omega f ∈ limitFormDomain (GE i omega) := by
        show limitFormEnergy (GE i omega) (GE i omega f) < ⊤
        rw [hEr]; exact EReal.coe_lt_top _
      have hdomF : GE i omega f ∈ limitFormDomain (GF i omega) := (hc i).1 ▸ hdomE
      have hvol : 0 ≤ (volume (centeredCube (z i) (r i) (hr i) :
          Set (SpatialCoordinates d))).toReal := ENNReal.toReal_nonneg
      have hmain := aux_thm_prop_local_to_improve M (M - m) _ _ _ hΔ
        (EReal.toReal_nonneg (limitFormEnergy_nonneg _ _)) hvol (homega i f hf)
      rw [aux_thm_prop_energy_coe _ _ hdomF]
      rw [hEr, EReal.toReal_coe] at hmain
      exact EReal.coe_le_coe_iff.mpr hmain
    filter_upwards [hU', hsn] with omega homega hsn i u hu
    exact aux_thm_prop_toReal_le (limitFormEnergy_nonneg _ _)
      (aux_thm_prop_core_closure (GE i omega) (GF i omega) (hsn i).1.1 _
        (aux_thm_prop_smoothSources_dense _
          (centeredCube_isBounded (z i) (hr i)).measure_lt_top.ne) _ hK (homega i) u hu)
  · obtain ⟨hK'pos, hprod⟩ := aux_thm_prop_swap_algebra m M (3 / 256) hcL0 hlt hk1 hk11
    refine ⟨3 / 256 * m / M, by have := hcL0.trans hlt; positivity, Or.inr ?_⟩
    have hV' : ∀ᵐ omega ∂P, ∀ i : ℕ,
        ∀ f ∈ aux_thm_prop_smoothSources (centeredCube (z i) (r i) (hr i)),
          limitFormEnergy (GE i omega) (GF i omega f) ≤
            (((m⁻¹ - 3 / 256 * (m⁻¹ - M⁻¹)) * inner ℝ f (GF i omega f) : ℝ) : EReal) := by
      filter_upwards [hV, hsn, hcomp] with omega homega hsn hc i f hf
      have hFr := aux_thm_prop_energy_range (GF i omega) (hsn i).2.1 (hsn i).2.2 f
      have hdomF : GF i omega f ∈ limitFormDomain (GF i omega) := by
        show limitFormEnergy (GF i omega) (GF i omega f) < ⊤
        rw [hFr]; exact EReal.coe_lt_top _
      have hdomE : GF i omega f ∈ limitFormDomain (GE i omega) := (hc i).1.symm ▸ hdomF
      have hvol : 0 ≤ (volume (centeredCube (z i) (r i) (hr i) :
          Set (SpatialCoordinates d))).toReal := ENNReal.toReal_nonneg
      have hcL : M⁻¹ ≤ m⁻¹ := inv_anti₀ hcL0 hlt.le
      have hΔ' : 0 ≤ m⁻¹ - M⁻¹ := sub_nonneg.mpr hcL
      have hmain := aux_thm_prop_local_to_improve m⁻¹ (m⁻¹ - M⁻¹) _ _ _ hΔ'
        (EReal.toReal_nonneg (limitFormEnergy_nonneg _ _)) hvol (homega i f hf)
      rw [aux_thm_prop_energy_coe _ _ hdomE]
      rw [hFr, EReal.toReal_coe] at hmain
      exact EReal.coe_le_coe_iff.mpr hmain
    filter_upwards [hV', hsn, hcomp] with omega homega hsn hc i u hu
    have hu' : u ∈ limitFormDomain (GF i omega) := (hc i).1 ▸ hu
    have hEF := aux_thm_prop_toReal_le (limitFormEnergy_nonneg _ _)
      (aux_thm_prop_core_closure (GF i omega) (GE i omega) (hsn i).2.1 _
        (aux_thm_prop_smoothSources_dense _
          (centeredCube_isBounded (z i) (hr i)).measure_lt_top.ne) _ hK'pos.le (homega i) u hu')
    have hF0 : 0 ≤ (limitFormEnergy (GF i omega) u).toReal :=
      EReal.toReal_nonneg (limitFormEnergy_nonneg _ _)
    exact aux_thm_prop_reciprocal_endpoint_bound m M (3 / 256)
      (limitFormEnergy (GE i omega) u).toReal (limitFormEnergy (GF i omega) u).toReal
      hcL0 (hcL0.trans hlt) hlt.le hk1.le hF0 hEF hprod

end Improve

end Part1

end Paper
end
