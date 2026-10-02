import SubdiffusiveProcess.Static.HarmonicCutoffEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false

section
open MeasureTheory Metric Filter Topology
open scoped ENNReal

set_option autoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Static
open Homogenization

variable {d : ℕ}

lemma aux_hcut_cell_sub_ball {R1 R2 h : ℝ} (hh : 0 < h) {k : Fin d → ℤ} (hk : aux_hcut_IsTrans h R1 R2 k) :
    aux_hcut_cell h k ⊆ ball (0 : Fin d → ℝ) R2 :=
  ball_subset_closedBall.trans (aux_hcut_trans_cell_subset hh hk)

/-- The zero-extended aux_hcut_cell correctors. -/
def aux_hcut_extE {R1 R2 h : ℝ} (hh : 0 < h)
    (e : ∀ k : Fin d → ℤ, aux_hcut_IsTrans h R1 R2 k → H10Function (aux_hcut_cell h k)) (k : Fin d → ℤ) :
    H10Function (ball (0 : Fin d → ℝ) R2) := by
  classical
  exact if hk : aux_hcut_IsTrans h R1 R2 k then
    (e k hk).extendByZeroToOpenSuperset (aux_hcut_measurableSet_cell h k) isOpen_ball (aux_hcut_cell_sub_ball hh hk)
  else 0

lemma aux_hcut_extE_toFun_of_mem {R1 R2 h : ℝ} (hh : 0 < h)
    (e : ∀ k : Fin d → ℤ, aux_hcut_IsTrans h R1 R2 k → H10Function (aux_hcut_cell h k)) {k : Fin d → ℤ}
    (hk : aux_hcut_IsTrans h R1 R2 k) {z : Fin d → ℝ} (hz : z ∈ aux_hcut_cell h k) :
    (aux_hcut_extE hh e k).toH1Function.toFun z = (e k hk).toH1Function.toFun z := by
  classical
  simp only [aux_hcut_extE, dif_pos hk, H10Function.extendByZeroToOpenSuperset_toFun,
    H10Function.zeroExtension_apply_of_mem _ hz]

lemma aux_hcut_extE_toFun_of_not_mem {R1 R2 h : ℝ} (hh : 0 < h)
    (e : ∀ k : Fin d → ℤ, aux_hcut_IsTrans h R1 R2 k → H10Function (aux_hcut_cell h k)) {k : Fin d → ℤ}
    (hk : aux_hcut_IsTrans h R1 R2 k) {z : Fin d → ℝ} (hz : z ∉ aux_hcut_cell h k) :
    (aux_hcut_extE hh e k).toH1Function.toFun z = 0 := by
  classical
  simp only [aux_hcut_extE, dif_pos hk, H10Function.extendByZeroToOpenSuperset_toFun,
    H10Function.zeroExtension_apply_of_not_mem _ hz]

lemma aux_hcut_extE_grad_of_mem {R1 R2 h : ℝ} (hh : 0 < h)
    (e : ∀ k : Fin d → ℤ, aux_hcut_IsTrans h R1 R2 k → H10Function (aux_hcut_cell h k)) {k : Fin d → ℤ}
    (hk : aux_hcut_IsTrans h R1 R2 k) {z : Fin d → ℝ} (hz : z ∈ aux_hcut_cell h k) :
    (aux_hcut_extE hh e k).toH1Function.grad z = (e k hk).toH1Function.grad z := by
  classical
  simp only [aux_hcut_extE, dif_pos hk, H10Function.extendByZeroToOpenSuperset_grad,
    H10Function.zeroExtensionGrad_apply_of_mem _ hz]

lemma aux_hcut_extE_grad_of_not_mem {R1 R2 h : ℝ} (hh : 0 < h)
    (e : ∀ k : Fin d → ℤ, aux_hcut_IsTrans h R1 R2 k → H10Function (aux_hcut_cell h k)) {k : Fin d → ℤ}
    (hk : aux_hcut_IsTrans h R1 R2 k) {z : Fin d → ℝ} (hz : z ∉ aux_hcut_cell h k) :
    (aux_hcut_extE hh e k).toH1Function.grad z = 0 := by
  classical
  simp only [aux_hcut_extE, dif_pos hk, H10Function.extendByZeroToOpenSuperset_grad,
    H10Function.zeroExtensionGrad_apply_of_not_mem _ hz]

end SubdiffusiveProcess.Static
end
end


section
open MeasureTheory Metric Filter Topology
open scoped ENNReal

set_option autoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Static
open Homogenization

variable {d : ℕ}

lemma aux_hcut_mem_T {R1 R2 h : ℝ} (hh : 0 < h) {k : Fin d → ℤ} :
    k ∈ (aux_hcut_trans_finite (d := d) (R1 := R1) (R2 := R2) hh).toFinset ↔ aux_hcut_IsTrans h R1 R2 k :=
  Set.Finite.mem_toFinset _

section Formulas
variable {R1 R2 h : ℝ} (hh : 0 < h) (F : H10Function (ball (0 : Fin d → ℝ) R2))
  (e : ∀ k : Fin d → ℤ, aux_hcut_IsTrans h R1 R2 k → H10Function (aux_hcut_cell h k))

lemma aux_hcut_X_toFun_on_cell {k0 : Fin d → ℤ} (hk0 : aux_hcut_IsTrans h R1 R2 k0) {z : Fin d → ℝ}
    (hz : z ∈ aux_hcut_cell h k0) :
    (aux_hcut_rawChi F (aux_hcut_trans_finite (R1 := R1) (R2 := R2) hh).toFinset (aux_hcut_extE hh e)).toH1Function.toFun z =
      F.toH1Function.toFun z + (e k0 hk0).toH1Function.toFun z := by
  rw [aux_hcut_rawChi_toFun, aux_hcut_sum_single_cell hh _ (fun k z => (aux_hcut_extE hh e k).toH1Function.toFun z)
    (fun k hk z hz => aux_hcut_extE_toFun_of_not_mem hh e ((aux_hcut_mem_T hh).1 hk) hz)
    ((aux_hcut_mem_T hh).2 hk0) hz, aux_hcut_extE_toFun_of_mem hh e hk0 hz]

lemma aux_hcut_X_grad_on_cell {k0 : Fin d → ℤ} (hk0 : aux_hcut_IsTrans h R1 R2 k0) {z : Fin d → ℝ}
    (hz : z ∈ aux_hcut_cell h k0) :
    (aux_hcut_rawChi F (aux_hcut_trans_finite (R1 := R1) (R2 := R2) hh).toFinset (aux_hcut_extE hh e)).toH1Function.grad z =
      F.toH1Function.grad z + (e k0 hk0).toH1Function.grad z := by
  rw [aux_hcut_rawChi_grad, aux_hcut_sum_single_cell hh _ (fun k z => (aux_hcut_extE hh e k).toH1Function.grad z)
    (fun k hk z hz => aux_hcut_extE_grad_of_not_mem hh e ((aux_hcut_mem_T hh).1 hk) hz)
    ((aux_hcut_mem_T hh).2 hk0) hz, aux_hcut_extE_grad_of_mem hh e hk0 hz]

lemma aux_hcut_X_toFun_off {z : Fin d → ℝ} (hz : ∀ k, aux_hcut_IsTrans h R1 R2 k → z ∉ aux_hcut_cell h k) :
    (aux_hcut_rawChi F (aux_hcut_trans_finite (R1 := R1) (R2 := R2) hh).toFinset (aux_hcut_extE hh e)).toH1Function.toFun z =
      F.toH1Function.toFun z := by
  rw [aux_hcut_rawChi_toFun, aux_hcut_sum_no_cell _ (fun k z => (aux_hcut_extE hh e k).toH1Function.toFun z)
    (fun k hk z hz => aux_hcut_extE_toFun_of_not_mem hh e ((aux_hcut_mem_T hh).1 hk) hz)
    (fun k hk => hz k ((aux_hcut_mem_T hh).1 hk)), add_zero]

lemma aux_hcut_X_grad_off {z : Fin d → ℝ} (hz : ∀ k, aux_hcut_IsTrans h R1 R2 k → z ∉ aux_hcut_cell h k) :
    (aux_hcut_rawChi F (aux_hcut_trans_finite (R1 := R1) (R2 := R2) hh).toFinset (aux_hcut_extE hh e)).toH1Function.grad z =
      F.toH1Function.grad z := by
  rw [aux_hcut_rawChi_grad, aux_hcut_sum_no_cell _ (fun k z => (aux_hcut_extE hh e k).toH1Function.grad z)
    (fun k hk z hz => aux_hcut_extE_grad_of_not_mem hh e ((aux_hcut_mem_T hh).1 hk) hz)
    (fun k hk => hz k ((aux_hcut_mem_T hh).1 hk)), add_zero]

end Formulas

lemma aux_hcut_not_trans_cells_of_mem {R1 R2 h : ℝ} (hh : 0 < h) {k : Fin d → ℤ} {z : Fin d → ℝ}
    (hz : z ∈ aux_hcut_cell h k) (hk : ¬ aux_hcut_IsTrans h R1 R2 k) : ∀ k', aux_hcut_IsTrans h R1 R2 k' → z ∉ aux_hcut_cell h k' := by
  intro k' hk' hz'
  by_cases hkk : k = k'
  · exact hk (hkk ▸ hk')
  · exact Set.disjoint_left.1 (aux_hcut_cell_disjoint hh hkk) hz hz'

lemma aux_hcut_not_mem_Ann_of_not_trans {R1 R2 h : ℝ} {k : Fin d → ℤ} {z : Fin d → ℝ}
    (hz : z ∈ aux_hcut_cell h k) (hk : ¬ aux_hcut_IsTrans h R1 R2 k) : z ∉ aux_hcut_Ann R1 R2 h :=
  fun hzA => hk ⟨z, ball_subset_closedBall hz, hzA⟩

end SubdiffusiveProcess.Static
end
end


section
open MeasureTheory Metric Filter Topology
open scoped ENNReal

set_option autoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Static
open Homogenization

variable {d : ℕ}

lemma aux_hcut_f_compact {R2 h : ℝ} {f : (Fin d → ℝ) → ℝ} (hf0 : ∀ x, R2 - 2 * h ≤ ‖x‖ → f x = 0) :
    HasCompactSupport f :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Fin d → ℝ) (R2 - 2 * h)) fun x hx => by
    apply hf0; rw [mem_closedBall_zero_iff, not_le] at hx; exact hx.le

lemma aux_hcut_f_tsupport {R2 h : ℝ} (hh : 0 < h) {f : (Fin d → ℝ) → ℝ}
    (hf0 : ∀ x, R2 - 2 * h ≤ ‖x‖ → f x = 0) :
    tsupport f ⊆ closedBall (0 : Fin d → ℝ) (R2 - 2 * h) := by
  refine closure_minimal (fun x hx => ?_) isClosed_closedBall
  rw [mem_closedBall_zero_iff]
  by_contra hcon
  exact hx (hf0 x (le_of_lt (not_le.1 hcon)))

/-- The a.e. `[0,1]` bounds of the raw interpolant. -/
lemma aux_hcut_raw_bounds {R1 R2 h : ℝ} (hh : 0 < h) (F : H10Function (ball (0 : Fin d → ℝ) R2))
    (f : (Fin d → ℝ) → ℝ) (hFf : F.toH1Function.toFun = f) (hf01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (e : ∀ k : Fin d → ℤ, aux_hcut_IsTrans h R1 R2 k → H10Function (aux_hcut_cell h k))
    (he : ∀ k (hk : aux_hcut_IsTrans h R1 R2 k), ∀ᵐ x ∂(volume.restrict (aux_hcut_cell h k)),
      0 ≤ f x + (e k hk).toH1Function.toFun x ∧ f x + (e k hk).toH1Function.toFun x ≤ 1) :
    ∀ᵐ z ∂(volume : Measure (Fin d → ℝ)),
      0 ≤ (aux_hcut_rawChi F (aux_hcut_trans_finite (R1 := R1) (R2 := R2) hh).toFinset (aux_hcut_extE hh e)).toH1Function.toFun z ∧
      (aux_hcut_rawChi F (aux_hcut_trans_finite (R1 := R1) (R2 := R2) hh).toFinset (aux_hcut_extE hh e)).toH1Function.toFun z ≤ 1 := by
  set T := (aux_hcut_trans_finite (d := d) (R1 := R1) (R2 := R2) hh).toFinset
  have hall : ∀ᵐ z ∂(volume : Measure (Fin d → ℝ)), ∀ k ∈ T, ∀ hk : aux_hcut_IsTrans h R1 R2 k,
      z ∈ aux_hcut_cell h k → 0 ≤ f z + (e k hk).toH1Function.toFun z ∧
        f z + (e k hk).toH1Function.toFun z ≤ 1 := by
    rw [Filter.eventually_all_finset]
    intro k hk
    have hk' := (aux_hcut_mem_T hh).1 hk
    filter_upwards [(ae_restrict_iff' (aux_hcut_measurableSet_cell h k)).1 (he k hk')] with z hz _ hz'
    exact hz hz'
  filter_upwards [hall, aux_hcut_ae_mem_cell (d := d) hh] with z hz ⟨k, hk⟩
  by_cases hkT : aux_hcut_IsTrans h R1 R2 k
  · rw [aux_hcut_X_toFun_on_cell hh F e hkT hk, hFf]
    exact hz k ((aux_hcut_mem_T hh).2 hkT) hkT hk
  · rw [aux_hcut_X_toFun_off hh F e (aux_hcut_not_trans_cells_of_mem hh hk hkT), hFf]
    exact hf01 z

end SubdiffusiveProcess.Static
end
end


section
open MeasureTheory Metric Filter Topology
open scoped ENNReal

set_option autoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Static
open Homogenization

variable {d : ℕ}

/-- **hCut deterministic core.** Given smooth `f` (`1` on `‖x‖ ≤ R1+h`, `0` on `‖x‖ ≥ R2-2h`) and, on
every transition aux_hcut_cell of the side-`h` grid, a corrector `e ∈ H¹₀(aux_hcut_cell)` with `0 ≤ f+e ≤ 1` and the
local energy growth `Kc ρ^{d-1/2}`, the cellwise interpolant is an admissible cutoff between
`ball 0 R1` and `ball 0 R2` with ball energy `≤ 8^d Kc h^{-1/2} r^{d-1/2}`. -/
theorem aux_hcut_hcut_core (hd : 1 ≤ d) (A : (Fin d → ℝ) → ℝ) (hApos : ∀ x, 0 < A x)
    (R1 R2 h Kc : ℝ) (hh : 0 < h) (hh1 : h ≤ 1 / 2) (hKc : 0 ≤ Kc)
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hf1 : ∀ x, ‖x‖ ≤ R1 + h → f x = 1) (hf0 : ∀ x, R2 - 2 * h ≤ ‖x‖ → f x = 0)
    (hcell : ∀ k : Fin d → ℤ, aux_hcut_IsTrans h R1 R2 k → ∃ e : H10Function (aux_hcut_cell h k),
      (∀ᵐ x ∂(volume.restrict (aux_hcut_cell h k)),
        0 ≤ f x + e.toH1Function.toFun x ∧ f x + e.toH1Function.toFun x ≤ 1) ∧
      ∀ y ∈ aux_hcut_cell h k, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
        ∫⁻ z in ball y ρ ∩ aux_hcut_cell h k, ENNReal.ofReal (A z *
          vecDot (aux_hcut_gradVec f z + e.toH1Function.grad z) (aux_hcut_gradVec f z + e.toH1Function.grad z)) ≤
        ENNReal.ofReal (Kc * ρ ^ ((d : ℝ) - 1 / 2))) :
    ∃ chi : H10Function (ball (0 : Fin d → ℝ) R2),
      (∀ x, 0 ≤ chi.toH1Function.toFun x ∧ chi.toH1Function.toFun x ≤ 1) ∧
      (∀ x ∈ ball (0 : Fin d → ℝ) R1, chi.toH1Function.toFun x = 1) ∧
      tsupport chi.toH1Function.toFun ⊆ ball (0 : Fin d → ℝ) R2 ∧
      ∀ (x : Fin d → ℝ) (r : ℝ), 0 < r → r ≤ 1 →
        ∫⁻ z in ball x r ∩ ball (0 : Fin d → ℝ) R2, ENNReal.ofReal (A z *
            vecDot (chi.toH1Function.grad z) (chi.toH1Function.grad z)) ≤
          ENNReal.ofReal (8 ^ d * Kc * h ^ (-(1 / 2 : ℝ)) * r ^ ((d : ℝ) - 1 / 2)) := by
  classical
  choose e he using hcell
  have hfsub : tsupport f ⊆ ball (0 : Fin d → ℝ) R2 :=
    (aux_hcut_f_tsupport hh hf0).trans (closedBall_subset_ball (by linarith))
  set F := aux_hcut_h10OfSmooth isOpen_ball hf (aux_hcut_f_compact hf0) hfsub with hF
  set X := aux_hcut_rawChi F (aux_hcut_trans_finite (d := d) (R1 := R1) (R2 := R2) hh).toFinset (aux_hcut_extE hh e) with hX
  have hbd : ∀ᵐ z ∂(volume : Measure (Fin d → ℝ)),
      0 ≤ X.toH1Function.toFun z ∧ X.toH1Function.toFun z ≤ 1 :=
    aux_hcut_raw_bounds hh F f rfl hf01 e (fun k hk => (he k hk).1)
  set clamp : (Fin d → ℝ) → ℝ := fun z => max 0 (min 1 (X.toH1Function.toFun z)) with hclamp
  have hcl : clamp =ᵐ[volume.restrict (ball (0 : Fin d → ℝ) R2)] X.toH1Function.toFun := by
    refine ae_restrict_of_ae ?_
    filter_upwards [hbd] with z hz
    simp only [hclamp, min_eq_right hz.2, max_eq_right hz.1]
  refine ⟨aux_hcut_h10CongrAe X clamp hcl, ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [aux_hcut_h10CongrAe_toFun, hclamp]
    exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  · intro x hx
    simp only [aux_hcut_h10CongrAe_toFun, hclamp]
    have hoff : ∀ k, aux_hcut_IsTrans h R1 R2 k → x ∉ aux_hcut_cell h k := fun k hk hxk =>
      aux_hcut_trans_cell_disjoint_inner hk hx (ball_subset_closedBall hxk)
    rw [hX, aux_hcut_X_toFun_off hh F e hoff, hF, aux_hcut_h10OfSmooth_toFun,
      hf1 x (by rw [mem_ball_zero_iff] at hx; linarith)]
    norm_num
  · -- support
    set K0 : Set (Fin d → ℝ) := closedBall 0 (R2 - 2 * h) ∪
      ⋃ k ∈ (aux_hcut_trans_finite (d := d) (R1 := R1) (R2 := R2) hh).toFinset, closedBall (aux_hcut_cc h k) (h / 2)
    have hK0closed : IsClosed K0 :=
      isClosed_closedBall.union (isClosed_biUnion_finset fun k _ => isClosed_closedBall)
    have hK0sub : K0 ⊆ ball (0 : Fin d → ℝ) R2 := by
      refine Set.union_subset (closedBall_subset_ball (by linarith)) (Set.iUnion₂_subset fun k hk => ?_)
      exact aux_hcut_trans_cell_subset hh ((aux_hcut_mem_T hh).1 hk)
    refine (closure_minimal (fun x hx => ?_) hK0closed).trans hK0sub
    simp only [aux_hcut_h10CongrAe_toFun, Function.mem_support, hclamp] at hx
    by_cases hin : ∃ k, aux_hcut_IsTrans h R1 R2 k ∧ x ∈ aux_hcut_cell h k
    · obtain ⟨k, hk, hxk⟩ := hin
      exact Or.inr (Set.mem_biUnion ((aux_hcut_mem_T hh).2 hk) (ball_subset_closedBall hxk))
    · push_neg at hin
      rw [hX, aux_hcut_X_toFun_off hh F e hin, hF, aux_hcut_h10OfSmooth_toFun] at hx
      left
      rw [mem_closedBall_zero_iff]
      by_contra hcon
      apply hx
      rw [hf0 x (le_of_lt (not_le.1 hcon))]
      norm_num
  · -- energy
    intro x r hr hr1
    refine (lintegral_mono_set Set.inter_subset_left).trans ?_
    simp only [aux_hcut_h10CongrAe_grad]
    refine aux_hcut_energy_bound hd hh hh1 hKc (aux_hcut_trans_finite (d := d) (R1 := R1) (R2 := R2) hh).toFinset
      (fun z => ENNReal.ofReal (A z * vecDot (X.toH1Function.grad z) (X.toH1Function.grad z)))
      (fun k z => if hk : aux_hcut_IsTrans h R1 R2 k then ENNReal.ofReal (A z *
          vecDot (aux_hcut_gradVec f z + (e k hk).toH1Function.grad z)
            (aux_hcut_gradVec f z + (e k hk).toH1Function.grad z)) else 0)
      ?_ ?_ ?_ x hr hr1
    · intro k hk z hz
      have hk' := (aux_hcut_mem_T hh).1 hk
      beta_reduce
      simp only [dif_pos hk']
      rw [hX, aux_hcut_X_grad_on_cell hh F e hk' hz, hF, aux_hcut_h10OfSmooth_grad]
      rfl
    · intro k hk z hz
      have hk' : ¬ aux_hcut_IsTrans h R1 R2 k := fun h' => hk ((aux_hcut_mem_T hh).2 h')
      beta_reduce
      rw [hX, aux_hcut_X_grad_off hh F e (aux_hcut_not_trans_cells_of_mem hh hz hk'), hF, aux_hcut_h10OfSmooth_grad]
      have h0 : aux_hcut_gradVec f z = 0 := aux_hcut_gradVec_eq_zero_off_Ann hf1 hf0 (aux_hcut_not_mem_Ann_of_not_trans hz hk')
      have h0' : (fun x i => (fderiv ℝ f x) (basisVec i)) z = 0 := h0
      rw [h0']
      simp [vecDot]
    · intro k hk y hy ρ hρ hρ1
      have hk' := (aux_hcut_mem_T hh).1 hk
      beta_reduce
      simp only [dif_pos hk']
      exact (he k hk').2 y hy ρ hρ hρ1

end SubdiffusiveProcess.Static
end
end

