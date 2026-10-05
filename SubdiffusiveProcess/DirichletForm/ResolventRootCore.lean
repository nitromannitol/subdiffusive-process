module

public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.DirichletForm.All
public import Mathlib.Tactic
public import SubdiffusiveProcess.Geometry.Cube

@[expose] public section

/-! Extracted local form data for the relative concentration proof.
This module proves the stated deterministic implications; it does not construct random bounds. -/

open MeasureTheory Filter Set Topology TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology ContDiff BigOperators

noncomputable section
namespace SubdiffusiveProcess.LimitFormCore
variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

/-- A symmetric injective operator has dense range. -/
theorem dense_range_of_symm
    (R : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hRsymm : ∀ x y : DomainL2 Q, inner ℝ (R x) y = inner ℝ x (R y))
    (hRinj : Function.Injective R) :
    Dense (Set.range R) := by
  have hK : (LinearMap.range (R : DomainL2 Q →ₗ[ℝ] DomainL2 Q))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro p hp
    rw [Submodule.mem_orthogonal] at hp
    have h0 : R p = 0 := by
      have hself : inner ℝ (R p) (R p) = (0 : ℝ) := by
        have := hp (R (R p)) ⟨R p, rfl⟩
        rw [hRsymm] at this
        rw [real_inner_comm]
        simpa only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_real_eq_id, id_eq, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, norm_eq_zero] using this
      exact inner_self_eq_zero.mp hself
    exact hRinj (by rw [h0, map_zero])
  have htop := (Submodule.topologicalClosure_eq_top_iff
    (K := LinearMap.range (R : DomainL2 Q →ₗ[ℝ] DomainL2 Q))).mpr hK
  rw [← Submodule.dense_iff_topologicalClosure_eq_top] at htop
  simpa only using! htop

/-- The pointwise identity behind the dual energy of `G = R ∘ R`. -/
theorem dual_term_eq
    (R : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hRsymm : ∀ x y : DomainL2 Q, inner ℝ (R x) y = inner ℝ x (R y))
    (f g : DomainL2 Q) :
    2 * inner ℝ f (R g) - inner ℝ f (R (R f)) = ‖g‖ ^ 2 - ‖g - R f‖ ^ 2 := by
  have h1 : inner ℝ f (R g) = inner ℝ (R f) g := (hRsymm f g).symm
  have h2 : inner ℝ f (R (R f)) = inner ℝ (R f) (R f) := (hRsymm f (R f)).symm
  rw [h1, h2, @norm_sub_sq_real, real_inner_self_eq_norm_sq, real_inner_comm g (R f)]
  ring

/-- `E(R g) = ‖g‖²` for the dual energy of `G = R ∘ R`, `R` symmetric and injective. -/
theorem limitFormEnergy_root
    (G R : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hRsymm : ∀ x y : DomainL2 Q, inner ℝ (R x) y = inner ℝ x (R y))
    (hRinj : Function.Injective R) (hRR : R.comp R = G) (g : DomainL2 Q) :
    limitFormEnergy G (R g) = ((‖g‖ ^ 2 : ℝ) : EReal) := by
  have hG : ∀ f, G f = R (R f) := fun f => by rw [← hRR]; rfl
  unfold limitFormEnergy
  apply le_antisymm
  · refine iSup_le fun f => ?_
    rw [hG, SubdiffusiveProcess.LimitFormCore.dual_term_eq R hRsymm f g]
    exact EReal.coe_le_coe_iff.mpr (by nlinarith only [sq_nonneg ‖g - R f‖])
  · have hdense := SubdiffusiveProcess.LimitFormCore.dense_range_of_symm R hRsymm hRinj
    refine le_of_forall_lt fun c0 hc0 => ?_
    obtain ⟨c, hc0c, hc⟩ := EReal.lt_iff_exists_real_btwn.mp hc0
    refine lt_of_lt_of_le hc0c ?_
    -- choose `f` with `‖g - R f‖² < ‖g‖² - c`
    have hpos : (0 : ℝ) < ‖g‖ ^ 2 - c := by
      have := EReal.coe_lt_coe_iff.mp hc
      linarith only [this]
    obtain ⟨y, hy, f, rfl⟩ := (Metric.dense_iff.mp hdense) g (Real.sqrt (‖g‖ ^ 2 - c))
      (Real.sqrt_pos.mpr hpos)
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have hsq : ‖R f - g‖ ^ 2 < ‖g‖ ^ 2 - c := by
      have h0 : 0 ≤ ‖R f - g‖ := norm_nonneg _
      calc ‖R f - g‖ ^ 2 < (Real.sqrt (‖g‖ ^ 2 - c)) ^ 2 := by gcongr
        _ = ‖g‖ ^ 2 - c := Real.sq_sqrt hpos.le
    refine le_trans ?_ (le_iSup _ f)
    rw [hG, SubdiffusiveProcess.LimitFormCore.dual_term_eq R hRsymm f g, norm_sub_rev]
    exact EReal.coe_le_coe_iff.mpr (by linarith only [hsq])

/-- The closed form of the dual energy on the range of the square root. -/
theorem form_root
    (F : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (G R : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hE : ∀ u : DomainL2 Q, F.energy u = limitFormEnergy G u)
    (hRsymm : ∀ x y : DomainL2 Q, inner ℝ (R x) y = inner ℝ x (R y))
    (hRinj : Function.Injective R) (hRR : R.comp R = G) (g : DomainL2 Q) :
    R g ∈ F.domain ∧ F.form (R g) (R g) = ‖g‖ ^ 2 := by
  have hEg := hE (R g)
  rw [SubdiffusiveProcess.LimitFormCore.limitFormEnergy_root G R hRsymm hRinj hRR g] at hEg
  have hmem : R g ∈ F.domain := by
    refine (F.energy_lt_top_iff (R g)).mp ?_
    rw [hEg]
    exact EReal.coe_lt_top _
  refine ⟨hmem, ?_⟩
  rw [F.energy_of_mem hmem] at hEg
  exact EReal.coe_injective hEg

/-- The domain of the closed form is the range of the square root. -/
theorem domain_eq_range
    (F : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (G R : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hE : ∀ u : DomainL2 Q, F.energy u = limitFormEnergy G u)
    (hdomR : limitFormDomain G = Set.range R) (u : DomainL2 Q) :
    u ∈ F.domain ↔ u ∈ Set.range R := by
  rw [← hdomR, ← F.energy_lt_top_iff, hE]
  rfl

/-- **Core density criterion.**  If every element of an energy-dense subset `S` of the
domain is an `L²` limit of elements of a subspace `C` with bounded energies, then `C`
is energy-dense.  Proof: transport by the square root `R` (an isometry from `L²` onto
the domain with the energy norm), where the weak-closure argument is an orthogonal
complement computation. -/
theorem core_dense
    (F : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (G R : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hE : ∀ u : DomainL2 Q, F.energy u = limitFormEnergy G u)
    (hRsymm : ∀ x y : DomainL2 Q, inner ℝ (R x) y = inner ℝ x (R y))
    (hRinj : Function.Injective R) (hRR : R.comp R = G)
    (hdomR : limitFormDomain G = Set.range R)
    (C : Submodule ℝ (DomainL2 Q)) (hC : ∀ x ∈ C, x ∈ F.domain)
    (S : Set (DomainL2 Q))
    (hSdense : ∀ u ∈ F.domain, ∀ ε : ℝ, 0 < ε → ∃ v ∈ S, v ∈ F.domain ∧
      F.energyNormSq (u - v) < ε)
    (happrox : ∀ v ∈ S, ∃ B : ℝ, ∀ ε : ℝ, 0 < ε → ∃ x ∈ C, F.form x x ≤ B ∧ ‖x - v‖ < ε) :
    ∀ u ∈ F.domain, ∀ ε : ℝ, 0 < ε → ∃ w ∈ C, F.energyNormSq (u - w) < ε := by
  have hform := SubdiffusiveProcess.LimitFormCore.form_root F G R hE hRsymm hRinj hRR
  have hdom := SubdiffusiveProcess.LimitFormCore.domain_eq_range F G R hE hdomR
  -- the energy norm of `R g` dominates and is dominated by `‖g‖²`
  have hnormR : ∀ g : DomainL2 Q, F.energyNormSq (R g) = ‖g‖ ^ 2 + ‖R g‖ ^ 2 := by
    intro g
    rw [_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energyNormSq, (hform g).2]
  let Cg : Submodule ℝ (DomainL2 Q) := C.comap (R : DomainL2 Q →ₗ[ℝ] DomainL2 Q)
  have hdenseR := SubdiffusiveProcess.LimitFormCore.dense_range_of_symm R hRsymm hRinj
  -- the preimage of `S` is dense
  have hSg : ∀ g : DomainL2 Q, ∀ η : ℝ, 0 < η → ∃ g' : DomainL2 Q, R g' ∈ S ∧ ‖g - g'‖ < η := by
    intro g η hη
    obtain ⟨v, hvS, hvD, hv⟩ := hSdense (R g) (hform g).1 (η ^ 2) (by positivity)
    obtain ⟨g', rfl⟩ := (hdom v).mp hvD
    refine ⟨g', hvS, ?_⟩
    have h1 : R g - R g' = R (g - g') := (map_sub R g g').symm
    rw [h1, hnormR] at hv
    have h2 : ‖g - g'‖ ^ 2 < η ^ 2 := by nlinarith only [hv, sq_nonneg ‖R (g - g')‖]
    exact lt_of_pow_lt_pow_left₀ 2 hη.le h2
  -- orthogonal complement of the transported core is trivial
  have horth : Cgᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro p hp
    rw [Submodule.mem_orthogonal] at hp
    -- `p` is orthogonal to every `g_v`, `v ∈ S`
    have hS0 : ∀ g' : DomainL2 Q, R g' ∈ S → inner ℝ g' p = (0 : ℝ) := by
      intro g' hg'S
      obtain ⟨B, hB⟩ := happrox (R g') hg'S
      have hB0 : ∀ η : ℝ, 0 < η → |inner ℝ g' p| ≤ η := by
        intro η hη
        set A : ℝ := ‖g'‖ + Real.sqrt (max B 0) + 1 with hA
        have hApos : 0 < A := by positivity
        obtain ⟨y, hy, q, rfl⟩ := (Metric.dense_iff.mp hdenseR) p (η / (2 * A))
          (by positivity)
        rw [Metric.mem_ball, dist_eq_norm] at hy
        obtain ⟨x, hxC, hxB, hx⟩ := hB (η / (2 * (‖q‖ + 1))) (by positivity)
        obtain ⟨gx, rfl⟩ := (hdom x).mp (hC x hxC)
        have hgxC : gx ∈ Cg := hxC
        have hgx0 : inner ℝ gx p = (0 : ℝ) := hp gx hgxC
        have hgxB : ‖gx‖ ≤ Real.sqrt (max B 0) := by
          rw [← Real.sqrt_sq (norm_nonneg gx), ← (hform gx).2]
          exact Real.sqrt_le_sqrt (hxB.trans (le_max_left _ _))
        have hsplit : inner ℝ g' p = inner ℝ (g' - gx) (p - R q) + inner ℝ (R g' - R gx) q := by
          have e1 : inner ℝ (R g' - R gx) q = inner ℝ (g' - gx) (R q) := by
            rw [← map_sub, hRsymm]
          rw [e1, ← inner_add_right, sub_add_cancel, inner_sub_left, hgx0, sub_zero]
        rw [hsplit]
        have hn1 : ‖g' - gx‖ ≤ A := by
          calc ‖g' - gx‖ ≤ ‖g'‖ + ‖gx‖ := norm_sub_le _ _
            _ ≤ A := by rw [hA]; linarith only [hgxB]
        have t1 : |inner ℝ (g' - gx) (p - R q)| ≤ η / 2 := by
          refine (abs_real_inner_le_norm _ _).trans ?_
          have hy' : ‖p - R q‖ ≤ η / (2 * A) := by rw [norm_sub_rev]; exact hy.le
          calc ‖g' - gx‖ * ‖p - R q‖ ≤ A * (η / (2 * A)) :=
                mul_le_mul hn1 hy' (norm_nonneg _) hApos.le
            _ = η / 2 := by field_simp
        have t2 : |inner ℝ (R g' - R gx) q| ≤ η / 2 := by
          refine (abs_real_inner_le_norm _ _).trans ?_
          have hx' : ‖R g' - R gx‖ ≤ η / (2 * (‖q‖ + 1)) := by rw [norm_sub_rev]; exact hx.le
          calc ‖R g' - R gx‖ * ‖q‖ ≤ η / (2 * (‖q‖ + 1)) * (‖q‖ + 1) :=
                mul_le_mul hx' (le_add_of_nonneg_right zero_le_one) (norm_nonneg _) (by positivity)
            _ = η / 2 := by field_simp
        calc |inner ℝ (g' - gx) (p - R q) + inner ℝ (R g' - R gx) q|
            ≤ |inner ℝ (g' - gx) (p - R q)| + |inner ℝ (R g' - R gx) q| := abs_add_le _ _
          _ ≤ η / 2 + η / 2 := add_le_add t1 t2
          _ = η := by ring
      exact abs_nonpos_iff.mp (le_of_forall_pos_le_add fun η hη => by
        rw [zero_add]; exact hB0 η hη)
    -- hence `p = 0`
    have hpp : ∀ η : ℝ, 0 < η → ‖p‖ ^ 2 ≤ η * ‖p‖ := by
      intro η hη
      obtain ⟨g', hg'S, hg'⟩ := hSg p η hη
      have h0 := hS0 g' hg'S
      have : ‖p‖ ^ 2 = inner ℝ (p - g') p := by
        rw [inner_sub_left, h0, sub_zero, real_inner_self_eq_norm_sq]
      rw [this]
      exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hg'.le (norm_nonneg _))
    have hp0 : ‖p‖ = 0 := by
      by_contra hne
      have hpos : 0 < ‖p‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      have := hpp (‖p‖ / 2) (by positivity)
      nlinarith only [hpos, this]
    exact norm_eq_zero.mp hp0
  have hCgdense : Dense (Cg : Set (DomainL2 Q)) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact (Submodule.topologicalClosure_eq_top_iff).mpr horth
  -- conclude
  intro u hu ε hε
  obtain ⟨gu, rfl⟩ := (hdom u).mp hu
  set L : ℝ := 1 + ‖R‖ ^ 2 with hL
  have hLpos : 0 < L := by positivity
  obtain ⟨g, hg, hgC⟩ := (Metric.dense_iff.mp hCgdense) gu (Real.sqrt (ε / L))
    (Real.sqrt_pos.mpr (by positivity))
  rw [Metric.mem_ball, dist_eq_norm] at hg
  refine ⟨R g, hgC, ?_⟩
  have h1 : R gu - R g = R (gu - g) := (map_sub R gu g).symm
  rw [h1, hnormR]
  have hRle : ‖R (gu - g)‖ ≤ ‖R‖ * ‖gu - g‖ := R.le_opNorm _
  have hsq : ‖gu - g‖ ^ 2 < ε / L := by
    have h0 : 0 ≤ ‖gu - g‖ := norm_nonneg _
    have hg' : ‖gu - g‖ < Real.sqrt (ε / L) := by rw [norm_sub_rev]; exact hg
    calc ‖gu - g‖ ^ 2 < (Real.sqrt (ε / L)) ^ 2 := by gcongr
      _ = ε / L := Real.sq_sqrt (by positivity)
  have hR2 : ‖R (gu - g)‖ ^ 2 ≤ ‖R‖ ^ 2 * ‖gu - g‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hRle 2
  calc ‖gu - g‖ ^ 2 + ‖R (gu - g)‖ ^ 2 ≤ L * ‖gu - g‖ ^ 2 := by rw [hL]; nlinarith only [hR2]
    _ < L * (ε / L) := by gcongr
    _ = ε := by field_simp

end SubdiffusiveProcess.LimitFormCore
