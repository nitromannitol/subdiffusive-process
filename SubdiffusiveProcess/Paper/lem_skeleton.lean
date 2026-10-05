module

public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.VariationalResponses.BoundaryPackaging
public import SubdiffusiveProcess.VariationalResponses.NativeBridge
public import SubdiffusiveProcess.VariationalResponses.ResponseMarkov
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.VariationalResponses.MeshError
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.Main.MeasureTrace
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import SubdiffusiveProcess.Paper.lem_skeleton_smooth_approx
public import SubdiffusiveProcess.Paper.lem_skeleton_finite_cutoff_glue
public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Paper.prop_boundary
public import SubdiffusiveProcess.Paper.prop_killed_inverse
public import SubdiffusiveProcess.Paper.prop_gluing
public import SubdiffusiveProcess.VariationalResponses.CellDirichlet
public import SubdiffusiveProcess.Analysis.ContinuousAEBound
public import SubdiffusiveProcess.CoarseGrainingVocab.Section11.SubunitEstimates
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import SubdiffusiveProcess.Paper.lane4_coercivity_dilation
public import SubdiffusiveProcess.Paper.aux_lane4_coercivity_dilation_cube_geometry
public import SubdiffusiveProcess.EllipticRegularity.CubeDilation

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}




/-- Negation preserves weak harmonicity. -/
theorem aux_lem_skeleton_harmonic_neg
    {d : ℕ} {W : Set (SpatialCoordinates d)} {a : SpatialCoordinates d → ℝ}
    {h : H1Function W} (hharm : IsWeaklyHarmonicOn a W h) :
    IsWeaklyHarmonicOn a W (-h) := by
  intro ψ
  calc
    ∫ x in W, vecDot (a x • (-h).grad x) (ψ.toH1Function.grad x) ∂volume
        = ∫ x in W, vecDot (a x • (-h.grad x)) (ψ.toH1Function.grad x) ∂volume := by
      simp [H1Function.neg_grad]
    _ = ∫ x in W, vecDot (-(a x • h.grad x)) (ψ.toH1Function.grad x) ∂volume := by
      refine integral_congr_ae ?_
      filter_upwards with x
      simp [smul_neg]
    _ = ∫ x in W, (-vecDot (a x • h.grad x) (ψ.toH1Function.grad x)) ∂volume := by
      refine integral_congr_ae ?_
      filter_upwards with x
      simp [vecDot_neg_left]
    _ = -∫ x in W, vecDot (a x • h.grad x) (ψ.toH1Function.grad x) ∂volume := by
      rw [integral_neg]
    _ = -0 := by rw [hharm ψ]
    _ = 0 := by simp

/-- Negation preserves the zero-trace-difference relation. -/
theorem aux_lem_skeleton_trace_neg
    {d : ℕ} {W : Set (SpatialCoordinates d)} {h g : H1Function W}
    (htr : HasZeroTraceDifferenceOn W h g) :
    HasZeroTraceDifferenceOn W (-h) (-g) := by
  obtain ⟨w, hwf, hwg⟩ := htr
  refine ⟨-w, ?_, ?_⟩
  · intro x
    calc
      (-h).toFun x = -(h.toFun x) := by simp
      _ = -(g.toFun x + w.toH1Function.toFun x) := by rw [hwf x]
      _ = -(g.toFun x) + (-(w.toH1Function.toFun x)) := by ring
      _ = (-g).toFun x + (-w).toH1Function.toFun x := by
        have h1 : (-g).toFun x = -(g.toFun x) := by
          simp
        have h2 : (-w).toH1Function.toFun x = -(w.toH1Function.toFun x) := by
          show ((-1 : ℝ) • w.toH1Function).toFun x = -(w.toH1Function.toFun x)
          simp
        rw [h1, h2]
  · intro x
    calc
      (-h).grad x = -(h.grad x) := by simp
      _ = -(g.grad x + w.toH1Function.grad x) := by rw [hwg x]
      _ = -(g.grad x) + (-(w.toH1Function.grad x)) := by ring
      _ = (-g).grad x + (-w).toH1Function.grad x := by
        have h1 : (-g).grad x = -(g.grad x) := by
          simp
        have h2 : (-w).toH1Function.grad x = -(w.toH1Function.grad x) := by
          show ((-1 : ℝ) • w.toH1Function).grad x = -(w.toH1Function.grad x)
          simp
        rw [h1, h2]



theorem aux_lem_skeleton_harmonic_sub
    {d : ℕ} {W : Opens (SpatialCoordinates d)} {a : SpatialCoordinates d → ℝ} {C : ℝ}
    (hameas : AEStronglyMeasurable a (volume.restrict (W : Set (SpatialCoordinates d))))
    (habd : ∀ᵐ x ∂(volume.restrict (W : Set (SpatialCoordinates d))), ‖a x‖ ≤ C)
    {u v : H1Function (W : Set (SpatialCoordinates d))}
    (hu : IsWeaklyHarmonicOn a (W : Set (SpatialCoordinates d)) u)
    (hv : IsWeaklyHarmonicOn a (W : Set (SpatialCoordinates d)) v) :
    IsWeaklyHarmonicOn a (W : Set (SpatialCoordinates d)) (u - v) := by
  intro ψ
  have hiu := lane2_integrableOn_coeff_vecDot hameas habd u.gradMemL2
    ψ.toH1Function.gradMemL2
  have hiv := lane2_integrableOn_coeff_vecDot hameas habd v.gradMemL2
    ψ.toH1Function.gradMemL2
  have hsm : ∀ (w : H1Function (W : Set (SpatialCoordinates d))),
      (fun x => vecDot (a x • w.grad x) (ψ.toH1Function.grad x)) =
        fun x => a x * vecDot (w.grad x) (ψ.toH1Function.grad x) := by
    intro w
    funext x
    simp only [vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have heq : (fun x => vecDot (a x • (u - v).grad x) (ψ.toH1Function.grad x)) =
      fun x => a x * vecDot (u.grad x) (ψ.toH1Function.grad x) -
        a x * vecDot (v.grad x) (ψ.toH1Function.grad x) := by
    funext x
    rw [H1Function.sub_grad]
    simp only [vecDot, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have h1 := hu ψ
  have h2 := hv ψ
  rw [hsm] at h1 h2
  rw [heq, integral_sub hiu hiv, h1, h2, sub_zero]

/-- Differences of zero-trace differences are zero-trace differences (same proof as `aux_lem_finite_source_comparison_trial_trace_sub`, reproduced directly to avoid
the same import cycle). -/
theorem aux_lem_skeleton_trace_sub
    {d : ℕ} {W : Set (SpatialCoordinates d)} {u φ v ψ : H1Function W}
    (hu : HasZeroTraceDifferenceOn W u φ) (hv : HasZeroTraceDifferenceOn W v ψ) :
    HasZeroTraceDifferenceOn W (u - v) (φ - ψ) := by
  obtain ⟨w₁, hw₁f, hw₁g⟩ := hu
  obtain ⟨w₂, hw₂f, hw₂g⟩ := hv
  refine ⟨w₁ - w₂, fun x => ?_, fun x => ?_⟩
  · change (u - v).toFun x = (φ - ψ).toFun x +
      (w₁.toH1Function + (-1 : ℝ) • w₂.toH1Function).toFun x
    rw [H1Function.sub_toFun, H1Function.sub_toFun, H1Function.add_toFun,
      H1Function.smul_toFun]
    simp only
    rw [hw₁f x, hw₂f x]
    ring
  · change (u - v).grad x = (φ - ψ).grad x +
      (w₁.toH1Function + (-1 : ℝ) • w₂.toH1Function).grad x
    rw [H1Function.sub_grad, H1Function.sub_grad, H1Function.add_grad,
      H1Function.smul_grad]
    simp only
    rw [hw₁g x, hw₂g x]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- The oscillation set of a function continuous on a compact superset of `q`
is bounded above. -/
theorem aux_lem_skeleton_osc_bddAbove {d : ℕ} {q K : Set (SpatialCoordinates d)}
    (hK : IsCompact K) (hqK : q ⊆ K) {b : SpatialCoordinates d → ℝ}
    (hb : ContinuousOn b K) :
    BddAbove {s : ℝ | ∃ y ∈ q, ∃ w ∈ q, s = |b y - b w|} := by
  set K' := b '' K with hK'
  have hK'_compact : IsCompact K' := hK.image_of_continuousOn hb
  have hK'_bddAbove : BddAbove K' := hK'_compact.bddAbove
  have hK'_bddBelow : BddBelow K' := hK'_compact.bddBelow
  refine ⟨sSup K' - sInf K', ?_⟩
  rintro s ⟨y, hy, w, hw, rfl⟩
  have hyK : y ∈ K := hqK hy
  have hwK : w ∈ K := hqK hw
  have byK' : b y ∈ K' := Set.mem_image_of_mem b hyK
  have bwK' : b w ∈ K' := Set.mem_image_of_mem b hwK
  have hlow : sInf K' ≤ b y := csInf_le hK'_bddBelow byK'
  have hhigh : b y ≤ sSup K' := le_csSup hK'_bddAbove byK'
  have hlow' : sInf K' ≤ b w := csInf_le hK'_bddBelow bwK'
  have hhigh' : b w ≤ sSup K' := le_csSup hK'_bddAbove bwK'
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- A closure point `z` of `q` obeys the open-cell oscillation bound against
any fixed `x ∈ q`. -/
theorem aux_lem_skeleton_closure_le_osc {d : ℕ} {q K : Set (SpatialCoordinates d)}
    (hK : IsCompact K) (hqK : closure q ⊆ K) {b : SpatialCoordinates d → ℝ}
    (hb : ContinuousOn b K) {x : SpatialCoordinates d} (hx : x ∈ q)
    {z : SpatialCoordinates d} (hz : z ∈ closure q) :
    |b z - b x| ≤ sSup {s : ℝ | ∃ y ∈ q, ∃ w ∈ q, s = |b y - b w|} := by
  have hq_sub_K : q ⊆ K := subset_closure.trans hqK
  have hBdd : BddAbove {s : ℝ | ∃ y ∈ q, ∃ w ∈ q, s = |b y - b w|} :=
    aux_lem_skeleton_osc_bddAbove hK hq_sub_K hb
  have hzK : z ∈ K := hqK hz
  have hcwa : ContinuousWithinAt b q z :=
    (hb.continuousWithinAt hzK).mono hq_sub_K
  have hcwa_sub : ContinuousWithinAt (fun y => b y - b x) q z :=
    ContinuousWithinAt.sub hcwa continuousWithinAt_const
  have h_tendsto_sub : Tendsto (fun y => b y - b x) (𝓝[q] z) (𝓝 (b z - b x)) :=
    hcwa_sub.tendsto
  have h_tendsto_abs : Tendsto (fun y => |b y - b x|) (𝓝[q] z) (𝓝 (|b z - b x|)) := by
    simpa using! (continuous_abs.tendsto (b z - b x)).comp h_tendsto_sub
  have hneBot : NeBot (𝓝[q] z) := (mem_closure_iff_nhdsWithin_neBot.mp hz)
  have h_event : ∀ᶠ y in 𝓝[q] z, |b y - b x| ≤ sSup {s : ℝ | ∃ y ∈ q, ∃ w ∈ q, s = |b y - b w|} :=
    Filter.eventually_of_mem self_mem_nhdsWithin fun y hy => le_csSup hBdd ⟨y, hy, x, hx, rfl⟩
  exact le_of_tendsto h_tendsto_abs h_event

/-- Boundary weak maximum principle: only the frontier values of a datum
continuous up to the boundary matter. -/
theorem aux_lem_skeleton_ae_le_of_frontier_le
    {d : ℕ} [NeZero d] {W : Set (SpatialCoordinates d)}
    (hW : IsOpenBoundedConvexDomain W)
    {a : SpatialCoordinates d → ℝ} {lam Lam : ℝ} (hlam : 0 < lam)
    (hameas : AEStronglyMeasurable a (volume.restrict W))
    (hbounds : ∀ᵐ y ∂(volume.restrict W), lam ≤ a y ∧ a y ≤ Lam)
    {h g : H1Function W} (hharm : IsWeaklyHarmonicOn a W h)
    (htr : HasZeroTraceDifferenceOn W h g)
    (hgc : ContinuousOn g.toFun (closure W)) {M : ℝ}
    (hg : ∀ x ∈ frontier W, g.toFun x ≤ M) :
    ∀ᵐ x ∂(volume.restrict W), h.toFun x ≤ M := by
  classical
  have : IsFiniteMeasure (volumeMeasureOn W) := hW.isFiniteMeasure_restrict_volume
  have hmatch : MemH10 W (fun x => h.toFun x - g.toFun x) := by
    obtain ⟨w0, hwf, _⟩ := htr
    refine ⟨w0, ?_⟩
    funext x
    rw [hwf x]
    ring
  have hlim : Tendsto (fun n : ℕ => M + 1 / (n + 1 : ℝ)) atTop (nhds M) := by
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => M) atTop (nhds M)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have key : ∀ n : ℕ, ∀ᵐ x ∂(volume.restrict W), h.toFun x ≤ M + 1 / (n + 1 : ℝ) := by
    intro n
    set c : ℝ := M + 1 / (n + 1 : ℝ) with hcdef
    have hcM : M < c := by
      rw [hcdef]
      have : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
      linarith
    have hv : MemH10 W (fun x => max (g.toFun x - c) 0) := by
      obtain ⟨p, hpf, _⟩ := Homogenization.exists_h1_max_sub_const hW g c
      let ψ : SpatialCoordinates d → ℝ :=
        fun x => if x ∈ closure W then max (g.toFun x - c) 0 else 0
      have hψeq : ψ =ᵐ[volume.restrict W] p.toFun := by
        filter_upwards [ae_restrict_mem hW.isOpen.measurableSet] with x hx
        simp only [ψ, ite_eq_left (subset_closure hx)]
        rw [hpf]
      let p1 : H1Function W := lane2_H1ofAEEq p ψ hψeq
      have hp1 : p1.toFun = ψ := rfl
      let K : Set (SpatialCoordinates d) := closure W ∩ g.toFun ⁻¹' Set.Ici c
      have hKclosed : IsClosed K :=
        hgc.preimage_isClosed_of_isClosed isClosed_closure isClosed_Ici
      have hKW : K ⊆ W := by
        intro x hx
        by_contra hxW
        have hxf : x ∈ frontier W := by
          refine ⟨hx.1, ?_⟩
          rw [hW.isOpen.interior_eq]
          exact hxW
        have hle := hg x hxf
        have hge : c ≤ g.toFun x := hx.2
        linarith
      have hKcompact : IsCompact K :=
        Metric.isCompact_of_isClosed_isBounded hKclosed (hW.isBoundedDomain.isBounded.subset hKW)
      have hzero : ∀ x ∉ K, p1.toFun x = 0 := by
        intro x hx
        rw [hp1]
        by_cases hxc : x ∈ closure W
        · simp only [ψ, ite_eq_left hxc]
          have hlt : g.toFun x < c := by
            by_contra hge
            exact hx ⟨hxc, le_of_not_gt hge⟩
          rw [max_eq_right (by linarith : g.toFun x - c ≤ 0)]
        · simp only [ψ, ite_eq_right hxc]
      obtain ⟨v0, hv0⟩ :=
        Homogenization.memH10_of_compactSupport hW p1 hKcompact hKW hzero
      have hgoal_eq : (fun x => max (g.toFun x - c) 0) =ᵐ[volume.restrict W]
          v0.toH1Function.toFun := by
        filter_upwards [ae_restrict_mem hW.isOpen.measurableSet] with x hx
        have hvc : v0.toH1Function.toFun x = max (g.toFun x - c) 0 := by
          rw [hv0, hp1]
          simp only [ψ, ite_eq_left (subset_closure hx)]
        exact hvc.symm
      exact ⟨lane2_H10ofAEEq v0 (fun x => max (g.toFun x - c) 0) hgoal_eq, rfl⟩
    let u : H1Function W := h - H1Function.const c
    have hu_toFun : u.toFun = fun x => h.toFun x - c := by
      rw [show u.toFun = fun x => h.toFun x - (H1Function.const c).toFun x from
        H1Function.sub_toFun h (H1Function.const c)]
      funext x
      simp only [H1Function.const]
    have hu_grad : u.grad = h.grad := by
      rw [show u.grad = fun x => h.grad x - (H1Function.const c).grad x from
        H1Function.sub_grad h (H1Function.const c)]
      funext x
      simp only [H1Function.const, sub_zero]
    have hsub : SubdiffusiveProcess.CoarseGrainingVocab.Section11.IsWeakSubSolutionOn a W u := by
      intro ψ' _
      have heq : (fun x => vecDot (a x • u.grad x) (ψ'.toH1Function.grad x)) =
          fun x => vecDot (a x • h.grad x) (ψ'.toH1Function.grad x) := by
        funext x
        rw [hu_grad]
      rw [heq]
      exact le_of_eq (hharm ψ')
    have hmem : MemH10 W (fun x => max (u.toFun x) 0) := by
      simp only [hu_toFun]
      have h1 := Homogenization.memH10_max_sub_matched hW h g hmatch c
      have h2 := Homogenization.memH10_add h1 hv
      simpa only [sub_add_cancel] using h2
    have hnp := SubdiffusiveProcess.CoarseGrainingVocab.Section11.ae_nonpos_of_isWeakSubSolutionOn
      hW hlam hameas hbounds hsub hmem
    filter_upwards [hnp] with x hx
    simp only [hu_toFun] at hx
    rw [hcdef] at hx ⊢
    linarith
  have hall : ∀ᵐ x ∂(volume.restrict W), ∀ n : ℕ, h.toFun x ≤ M + 1 / (n + 1 : ℝ) :=
    ae_all_iff.mpr key
  filter_upwards [hall] with x hx
  exact le_of_tendsto_of_tendsto
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => h.toFun x) atTop (nhds (h.toFun x)))
    hlim (Eventually.of_forall hx)

/-- Ellipticity bookkeeping: the whole-`Q` bound `hell` restricted to one cell
`cell ⊆ Q`, both as `AEStronglyMeasurable`/an a.e. bound and as a pointwise
bound. -/
theorem aux_lem_skeleton_ell_package
    (cell : Set (SpatialCoordinates d)) (hcell_open : IsOpen cell)
    (hsub : cell ⊆ (Q : Set (SpatialCoordinates d)))
    (a : SpatialCoordinates d → ℝ)
    (ha : ContinuousOn a (closure (Q : Set (SpatialCoordinates d))))
    (hell : ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ (Q : Set (SpatialCoordinates d)), lam ≤ a x ∧ a x ≤ Lam) :
    ∃ lam Lam : ℝ, 0 < lam ∧
      AEStronglyMeasurable a (volumeMeasureOn cell) ∧
      (∀ᵐ y ∂(volumeMeasureOn cell), lam ≤ a y ∧ a y ≤ Lam) ∧
      (∀ y ∈ cell, lam ≤ a y ∧ a y ≤ Lam) := by
  obtain ⟨lam, Lam, hlam_pos, hbound⟩ := hell
  have ha' := ha.mono (hsub.trans subset_closure)
  refine ⟨lam, Lam, hlam_pos, ha'.aestronglyMeasurable hcell_open.measurableSet, ?_, ?_⟩
  · filter_upwards [ae_restrict_mem hcell_open.measurableSet] with y hy
    exact hbound y (hsub hy)
  · intro y hy
    exact hbound y (hsub hy)

/-! ### Generic combinators toward `h_domain` / `h_energy_bound`, used by the
`aux_lem_skeleton_gap_from_weak_seq` consumer below. -/

theorem aux_lem_skeleton_sum_tendsto
    (m : ℕ) (f : Fin m → ℕ → ℝ) (Lam : Fin m → ℝ)
    (h : ∀ i : Fin m, Tendsto (f i) atTop (𝓝 (Lam i))) :
    Tendsto (fun n => ∑ i : Fin m, f i n) atTop (𝓝 (∑ i : Fin m, Lam i)) :=
  tendsto_finsetSum Finset.univ (fun i _ => h i)

theorem aux_lem_skeleton_energy_le_of_weak_tendsto
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (S : ResponseSpace Q)
    (aC : ℕ → PositiveCoefficient Q)
    (hliminf : ∀ (uN : ℕ → S.space) (u : DomainL2 Q),
      (∀ f : DomainL2 Q, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop
        (𝓝 (inner ℝ f u))) →
      E.energy u ≤ liminf
        (fun n => ((responseForm S (aC n) (uN n) (uN n) : ℝ) : EReal)) atTop)
    (uN : ℕ → S.space) (v : DomainL2 Q)
    (hweak : ∀ f : DomainL2 Q, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop
      (𝓝 (inner ℝ f v)))
    (L : ℝ)
    (hLtendsto : Tendsto (fun n => (responseForm S (aC n) (uN n) (uN n) : ℝ))
      atTop (𝓝 L)) :
    E.energy v ≤ (L : EReal) := by
  have h1 := hliminf uN v hweak
  have hwenergy : liminf (fun n => ((responseForm S (aC n) (uN n) (uN n) : ℝ) : EReal)) atTop = (L : EReal) :=
    (EReal.tendsto_coe.mpr hLtendsto).liminf_eq
  exact h1.trans_eq hwenergy

theorem aux_lem_skeleton_mem_domain_of_energy_le_coe
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (v : DomainL2 Q) (L : ℝ) (h : E.energy v ≤ (L : EReal)) :
    v ∈ E.domain :=
  E.mem_domain_of_energy_lt_top (lt_of_le_of_lt h (EReal.coe_lt_top L))

theorem aux_lem_skeleton_energy_toReal_le_of_energy_le_coe
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (v : DomainL2 Q) (L : ℝ) (hv : v ∈ E.domain) (h : E.energy v ≤ (L : EReal)) :
    (E.energy v).toReal ≤ L := by
  rw [E.energy_of_mem hv] at h ⊢
  rw [EReal.toReal_coe]
  exact EReal.coe_le_coe_iff.mp h

/-- CONSUMER: chains the Mosco lower bound into the exact pair of facts
`lem_skeleton` needs for `h_domain` and `h_energy_bound`, given a weak-limit
witness `uN → v` whose energies tend to a real `L`. -/
theorem aux_lem_skeleton_domain_and_energy_bound_of_weak_tendsto
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (S : ResponseSpace Q)
    (aC : ℕ → PositiveCoefficient Q)
    (hliminf : ∀ (uN : ℕ → S.space) (u : DomainL2 Q),
      (∀ f : DomainL2 Q, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop
        (𝓝 (inner ℝ f u))) →
      E.energy u ≤ liminf
        (fun n => ((responseForm S (aC n) (uN n) (uN n) : ℝ) : EReal)) atTop)
    (uN : ℕ → S.space) (v : DomainL2 Q)
    (hweak : ∀ f : DomainL2 Q, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop
      (𝓝 (inner ℝ f v)))
    (L : ℝ)
    (hLtendsto : Tendsto (fun n => (responseForm S (aC n) (uN n) (uN n) : ℝ))
      atTop (𝓝 L)) :
    v ∈ E.domain ∧ (E.energy v).toReal ≤ L := by
  have hle := aux_lem_skeleton_energy_le_of_weak_tendsto E S aC hliminf uN v hweak L hLtendsto
  have hmem := aux_lem_skeleton_mem_domain_of_energy_le_coe E v L hle
  exact ⟨hmem, aux_lem_skeleton_energy_toReal_le_of_energy_le_coe E v L hmem hle⟩

theorem aux_lem_skeleton_weak_of_tendsto
    (uN : ℕ → DomainL2 Q) (v : DomainL2 Q)
    (hstrong : Tendsto uN atTop (𝓝 v)) :
    ∀ f : DomainL2 Q, Tendsto (fun n => inner ℝ f (uN n)) atTop (𝓝 (inner ℝ f v)) := by
  intro f
  exact ((innerSL ℝ f : DomainL2 Q →L[ℝ] ℝ).continuous.tendsto v).comp hstrong

theorem aux_lem_skeleton_mem_Sspace_of_H10
    (S : ResponseSpace Q) (hS : S.space = killedSobolevGraph Q)
    (v : Homogenization.H10Function (Q : Set (SpatialCoordinates d))) :
    ∃ s : S.space, ((s : SobolevData Q).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
        (v : SpatialCoordinates d → ℝ) := by
  have h := sobolevDataOfH1_mem_killed v
  rw [← hS] at h
  refine ⟨⟨sobolevDataOfH1 v.toH1Function, h⟩, ?_⟩
  exact sobolevDataOfH1_fst_coeFn v.toH1Function

/-- Stronger form of `aux_lem_skeleton_mem_Sspace_of_H10`: the `S.space`
element also matches `v`'s gradient componentwise a.e. (needed to
identify `responseForm` — which reads off the `S.space` element's gradient
components — with the concrete `energy` of the glued `H10Function`, e.g. for
`aux_lem_skeleton_h_diagonal` below). -/
theorem aux_lem_skeleton_mem_Sspace_of_H10_with_grad
    (S : ResponseSpace Q) (hS : S.space = killedSobolevGraph Q)
    (v : Homogenization.H10Function (Q : Set (SpatialCoordinates d))) :
    ∃ s : S.space, ((s : SobolevData Q).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
        (v : SpatialCoordinates d → ℝ) ∧
      ∀ i : Fin d, ((s : SobolevData Q).2 i : DomainL2 Q)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
          fun x => v.toH1Function.grad x i := by
  have hmem := sobolevDataOfH1_mem_killed v
  rw [← hS] at hmem
  refine ⟨⟨sobolevDataOfH1 v.toH1Function, hmem⟩, ?_, ?_⟩
  · exact sobolevDataOfH1_fst_coeFn v.toH1Function
  · intro i
    exact sobolevDataOfH1_snd_coeFn v.toH1Function i




theorem aux_lem_skeleton_isHolderOn_of_dist_bound
    {beta : ℝ} {S : Set (SpatialCoordinates d)} {f : SpatialCoordinates d → ℝ} {C : ℝ}
    (_hC : 0 ≤ C) (h : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      |f x - f y| ≤ C * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta) :
    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S f := by
  refine ⟨C, ?_⟩
  rintro v ⟨x, hx, y, hy, hxy, rfl⟩
  set E : ℝ := Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) with hEdef
  have hEpos : 0 < E := by
    apply Real.sqrt_pos.mpr
    have hne : ∃ i : Fin d, x i - y i ≠ 0 := by
      by_contra hn
      apply hxy
      funext i
      have hi : x i - y i = 0 := by by_contra hi; exact hn ⟨i, hi⟩
      linarith
    obtain ⟨i, hi⟩ := hne
    exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
  have hbpos : 0 < E ^ beta := Real.rpow_pos_of_pos hEpos beta
  exact (div_le_iff₀ hbpos).mpr (h x hx y hy hxy)

theorem aux_lem_skeleton_holderOn_dest
    {beta : ℝ} {S : Set (SpatialCoordinates d)} {f : SpatialCoordinates d → ℝ}
    (hf : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      |f x - f y| ≤ C * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx y hy hxy
  set E : ℝ := Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) with hEdef
  have hEpos : 0 < E := by
    apply Real.sqrt_pos.mpr
    have hne : ∃ i : Fin d, x i - y i ≠ 0 := by
      by_contra hn
      apply hxy
      funext i
      have hi : x i - y i = 0 := by by_contra hi; exact hn ⟨i, hi⟩
      linarith
    obtain ⟨i, hi⟩ := hne
    exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
  have hbpos : 0 < E ^ beta := Real.rpow_pos_of_pos hEpos beta
  have h' : |f x - f y| ≤ C * E ^ beta := (div_le_iff₀ hbpos).mp (hC ⟨x, hx, y, hy, hxy, rfl⟩)
  calc |f x - f y| ≤ C * E ^ beta := h'
    _ ≤ max C 0 * E ^ beta := mul_le_mul_of_nonneg_right (le_max_left C 0) hbpos.le

/-- A genuinely `beta`-Hölder function on a set of Euclidean diameter `≤ D` is bounded: split
against a fixed base point `z0 ∈ S` via `aux_lem_skeleton_holderOn_dest`. Pulled out as its own
declaration (used twice, for `bseq k - b` and for `b` themselves, inside
`aux_lem_skeleton_gap_weak_seq`) to keep that assembly's own elaboration within budget. -/
theorem aux_lem_skeleton_bounded_of_holderOn_diam
    {beta : ℝ} (hbeta0 : 0 ≤ beta)
    {S : Set (SpatialCoordinates d)} {f : SpatialCoordinates d → ℝ}
    (hf : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S f)
    (z0 : SpatialCoordinates d) (hz0 : z0 ∈ S)
    (D : ℝ) (hD : 0 ≤ D)
    (hSD : ∀ x ∈ S, ∀ y ∈ S, Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ D) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ x ∈ S, |f x| ≤ E := by
  obtain ⟨C, hC0, hC⟩ := aux_lem_skeleton_holderOn_dest hf
  refine ⟨|f z0| + C * D ^ beta, by positivity, ?_⟩
  intro x hx
  by_cases hxz : x = z0
  · rw [hxz]
    have : (0:ℝ) ≤ C * D ^ beta := mul_nonneg hC0 (Real.rpow_nonneg hD beta)
    linarith
  · have hbound : |f x - f z0| ≤ C * (Real.sqrt (∑ j : Fin d, (x j - z0 j) ^ 2)) ^ beta :=
      hC x hx z0 hz0 hxz
    have hdle : Real.sqrt (∑ j : Fin d, (x j - z0 j) ^ 2) ≤ D := hSD x hx z0 hz0
    have hpow : (Real.sqrt (∑ j : Fin d, (x j - z0 j) ^ 2)) ^ beta ≤ D ^ beta :=
      Real.rpow_le_rpow (Real.sqrt_nonneg _) hdle hbeta0
    have hpow' : C * (Real.sqrt (∑ j : Fin d, (x j - z0 j) ^ 2)) ^ beta ≤ C * D ^ beta :=
      mul_le_mul_of_nonneg_left hpow hC0
    calc |f x| = |(f x - f z0) + f z0| := by ring_nf
      _ ≤ |f x - f z0| + |f z0| := abs_add_le _ _
      _ ≤ C * (Real.sqrt (∑ j : Fin d, (x j - z0 j) ^ 2)) ^ beta + |f z0| := by linarith
      _ ≤ C * D ^ beta + |f z0| := by linarith
      _ = |f z0| + C * D ^ beta := by ring

theorem aux_lem_skeleton_isHolderOn_mono
    {beta : ℝ} {S T : Set (SpatialCoordinates d)} {f : SpatialCoordinates d → ℝ}
    (hTS : T ⊆ S) (hf : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S f) : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta T f := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨C, ?_⟩
  rintro v ⟨x, hx, y, hy, hxy, rfl⟩
  exact hC ⟨x, hTS hx, y, hTS hy, hxy, rfl⟩

theorem aux_lem_skeleton_isHolderOn_congr
    {beta : ℝ} {S : Set (SpatialCoordinates d)} {f1 f2 : SpatialCoordinates d → ℝ}
    (heq : ∀ x ∈ S, f1 x = f2 x) (hf1 : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S f1) :
    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S f2 := by
  obtain ⟨C, hC⟩ := hf1
  refine ⟨C, ?_⟩
  rintro v ⟨x, hx, y, hy, hxy, rfl⟩
  rw [← heq x hx, ← heq y hy]
  exact hC ⟨x, hx, y, hy, hxy, rfl⟩

theorem aux_lem_skeleton_isHolderOn_neg
    {beta : ℝ} {S : Set (SpatialCoordinates d)} {f : SpatialCoordinates d → ℝ}
    (hf : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S f) : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S (fun x => -f x) := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨C, ?_⟩
  rintro v ⟨x, hx, y, hy, hxy, rfl⟩
  show |(-f x) - (-f y)| / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta ≤ C
  rw [show (-f x) - (-f y) = -(f x - f y) by ring, abs_neg]
  exact hC ⟨x, hx, y, hy, hxy, rfl⟩

theorem aux_lem_skeleton_isHolderOn_sub
    {beta : ℝ} {S : Set (SpatialCoordinates d)} {f g : SpatialCoordinates d → ℝ}
    (hf : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S f) (hg : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S g) :
    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S (fun x => f x - g x) := by
  obtain ⟨Cf, hCf0, hCf⟩ := aux_lem_skeleton_holderOn_dest hf
  obtain ⟨Cg, hCg0, hCg⟩ := aux_lem_skeleton_holderOn_dest hg
  apply aux_lem_skeleton_isHolderOn_of_dist_bound (C := Cf + Cg) (add_nonneg hCf0 hCg0)
  intro x hx y hy hxy
  have h1 : |f x - f y| ≤ Cf * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta :=
    hCf x hx y hy hxy
  have h2 : |g x - g y| ≤ Cg * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta :=
    hCg x hx y hy hxy
  have habs : |(f x - g x) - (f y - g y)| ≤ |f x - f y| + |g x - g y| := by
    have heq : (f x - g x) - (f y - g y) = (f x - f y) + (-(g x - g y)) := by ring
    calc |(f x - g x) - (f y - g y)| = |(f x - f y) + (-(g x - g y))| := by rw [heq]
      _ ≤ |f x - f y| + |(-(g x - g y))| := abs_add_le _ _
      _ = |f x - f y| + |g x - g y| := by rw [abs_neg]
  calc |(f x - g x) - (f y - g y)| ≤ |f x - f y| + |g x - g y| := habs
    _ ≤ Cf * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta +
          Cg * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta := add_le_add h1 h2
    _ = (Cf + Cg) * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta := by ring

theorem aux_lem_skeleton_holderSeminorm_nonneg
    (beta : ℝ) (S : Set (SpatialCoordinates d)) (f : SpatialCoordinates d → ℝ) :
    0 ≤ _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta S f := by
  unfold _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm
  apply Real.sSup_nonneg
  rintro v ⟨x, hx, y, hy, hxy, rfl⟩
  exact div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)

theorem aux_lem_skeleton_holderSeminorm_mono
    {beta : ℝ} {S T : Set (SpatialCoordinates d)} {f : SpatialCoordinates d → ℝ}
    (hTS : T ⊆ S) (hf : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S f) :
    _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta T f ≤ _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta S f := by
  unfold _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm
  apply Real.sSup_le _ (aux_lem_skeleton_holderSeminorm_nonneg beta S f)
  rintro v ⟨x, hx, y, hy, hxy, rfl⟩
  exact le_csSup hf ⟨x, hTS hx, y, hTS hy, hxy, rfl⟩

theorem aux_lem_skeleton_cAlphaNorm_ge_holderSeminorm
    (beta : ℝ) (S : Set (SpatialCoordinates d)) (f : SpatialCoordinates d → ℝ) :
    _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta S f ≤ _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta S f := by
  unfold _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm
  have h0 : 0 ≤ sSup {v : ℝ | ∃ x ∈ S, v = |f x|} := by
    apply Real.sSup_nonneg
    rintro v ⟨x, hx, rfl⟩
    exact abs_nonneg _
  linarith

/-- Global Lipschitz bound (from `lane2_exists_fderiv_bound`, sup-norm based, matching
`SpatialCoordinates d`'s ambient metric) turned into a genuine `beta`-Hölder bound (against the
Euclidean quotient `SubdiffusiveProcess.EllipticRegularity.holderRatioSet` actually uses) on any set of sup-norm diameter `≤ D`,
for a globally smooth compactly supported function. The sup-norm/Euclidean-norm conversion is
`Homogenization.norm_le_euclideanNorm` / `Homogenization.euclideanNorm_le_dimension_mul_norm`,
exactly as used by `aux_lem_skeleton_smooth_approx_pi_holder` / `_cAlpha_bound`
(`lem_skeleton_smooth_approx`). -/
theorem aux_lem_skeleton_isHolderOn_of_contDiff_bounded
    {beta : ℝ} (_hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1)
    {f : SpatialCoordinates d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfsupp : HasCompactSupport f)
    {S : Set (SpatialCoordinates d)} {D : ℝ} (hD : 0 ≤ D)
    (hSD : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ D) :
    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S f := by
  obtain ⟨L, hL0, hL⟩ := lane2_exists_fderiv_bound hf hfsupp
  apply aux_lem_skeleton_isHolderOn_of_dist_bound (C := L * ((d : ℝ) * D) ^ (1 - beta)) (by positivity)
  intro x hx y hy hxy
  have hdiff : ∀ z ∈ (Set.univ : Set (SpatialCoordinates d)), DifferentiableAt ℝ f z :=
    fun z _ => (hf.differentiable (by norm_num)).differentiableAt
  have hbound : ∀ z ∈ (Set.univ : Set (SpatialCoordinates d)), ‖fderiv ℝ f z‖ ≤ L :=
    fun z _ => hL z
  have hlip : ‖f y - f x‖ ≤ L * ‖y - x‖ :=
    convex_univ.norm_image_sub_le_of_norm_fderiv_le hdiff hbound (Set.mem_univ x) (Set.mem_univ y)
  rw [Real.norm_eq_abs] at hlip
  have hnormeq : ‖y - x‖ = dist x y := by rw [← dist_eq_norm, dist_comm]
  rw [hnormeq, abs_sub_comm] at hlip
  set E : ℝ := Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) with hEdef
  have hEpos : 0 < E := by
    apply Real.sqrt_pos.mpr
    have hne : ∃ i : Fin d, x i - y i ≠ 0 := by
      by_contra hn
      apply hxy
      funext i
      have hi : x i - y i = 0 := by by_contra hi; exact hn ⟨i, hi⟩
      linarith
    obtain ⟨i, hi⟩ := hne
    exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
  have hdistE : dist x y ≤ E := by
    simpa [hEdef, Homogenization.euclideanNorm, Homogenization.vecNormSq,
      Homogenization.vecDot, dist_eq_norm, Pi.sub_apply, pow_two] using
      (Homogenization.norm_le_euclideanNorm (x - y))
  have hEdim : E ≤ (d : ℝ) * dist x y := by
    simpa [hEdef, Homogenization.euclideanNorm, Homogenization.vecNormSq,
      Homogenization.vecDot, dist_eq_norm, Pi.sub_apply, pow_two] using
      (Homogenization.euclideanNorm_le_dimension_mul_norm (x - y))
  have hdxy_le : dist x y ≤ D := hSD x hx y hy
  have hEdD : E ≤ (d : ℝ) * D := hEdim.trans (by
    apply mul_le_mul_of_nonneg_left hdxy_le (by positivity))
  have hexp : E = E ^ (1 - beta) * E ^ beta := by
    rw [← Real.rpow_add hEpos]; norm_num
  have hmono : E ^ (1 - beta) ≤ ((d : ℝ) * D) ^ (1 - beta) :=
    Real.rpow_le_rpow (Real.sqrt_nonneg _) hEdD (by linarith)
  calc |f x - f y| ≤ L * dist x y := hlip
    _ ≤ L * E := mul_le_mul_of_nonneg_left hdistE hL0
    _ = L * (E ^ (1 - beta) * E ^ beta) := by rw [← hexp]
    _ = (L * E ^ (1 - beta)) * E ^ beta := by ring
    _ ≤ (L * ((d : ℝ) * D) ^ (1 - beta)) * E ^ beta := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Real.sqrt_nonneg _) beta)
        exact mul_le_mul_of_nonneg_left hmono hL0




theorem aux_lem_skeleton_ae_of_cellwise
    (m : ℕ) (cell : Fin m → Set (SpatialCoordinates d))
    (hcover : (⋃ i : Fin m, cell i) =ᵐ[(volume : Measure (SpatialCoordinates d))]
      (Q : Set (SpatialCoordinates d)))
    (P : SpatialCoordinates d → Prop)
    (hP : ∀ i, ∀ᵐ x ∂(volume.restrict (cell i)), P x) :
    ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))), P x := by
  rw [← Measure.restrict_congr_set hcover, ae_restrict_iUnion_iff]
  exact hP

/-- A sequence uniformly bounded in norm on a measure space is `UnifIntegrable` at exponent `2`:
for any bound `C > M`, the truncation set `{C ≤ ‖f n x‖₊}` is a.e. empty, so the truncated
`eLpNorm` is genuinely `0`. -/
theorem aux_lem_skeleton_unifIntegrable_of_bounded
    {mu : Measure (SpatialCoordinates d)} {f : ℕ → SpatialCoordinates d → ℝ} {M : ℝ} (hM0 : 0 ≤ M)
    (hfmeas : ∀ n, AEStronglyMeasurable (f n) mu)
    (hbound : ∀ n, ∀ᵐ x ∂mu, |f n x| ≤ M) :
    MeasureTheory.UnifIntegrable f 2 mu := by
  apply MeasureTheory.unifIntegrable_of (by norm_num) (by norm_num) hfmeas
  intro ε hε
  have hM1 : (0 : ℝ) ≤ M + 1 := by linarith
  refine ⟨⟨M + 1, hM1⟩, fun n => ?_⟩
  have hae : {x | (⟨M + 1, hM1⟩ : ℝ≥0) ≤ ‖f n x‖₊}.indicator (f n)
      =ᵐ[mu] (0 : SpatialCoordinates d → ℝ) := by
    filter_upwards [hbound n] with x hx
    by_cases hxs : x ∈ {x | (⟨M + 1, hM1⟩ : ℝ≥0) ≤ ‖f n x‖₊}
    · exfalso
      have h1 : (M + 1 : ℝ) ≤ ‖f n x‖ := by
        have h1' : (⟨M + 1, hM1⟩ : ℝ≥0) ≤ ‖f n x‖₊ := hxs
        exact_mod_cast h1'
      rw [Real.norm_eq_abs] at h1
      linarith
    · exact Set.indicator_of_notMem hxs (f n)
  simpa only [MeasureTheory.eLpNorm_zero] using!
    (MeasureTheory.eLpNorm_congr_ae (p := 2) hae).trans_le (by simpa only [MeasureTheory.eLpNorm_zero] using (show 0 ≤ ε from zero_le))

/-- Continuity on the closure plus a bound on the open interior extends the bound to the whole
closure (via `mem_closure_iff_nhdsWithin_neBot`, exactly the style of `aux_lem_skeleton_closure_le_osc`
above). -/
theorem aux_lem_skeleton_le_closure_of_le_open
    {W : Set (SpatialCoordinates d)} {f : SpatialCoordinates d → ℝ} {M : ℝ}
    (hf : ContinuousOn f (closure W)) (hle : ∀ x ∈ W, f x ≤ M) :
    ∀ x ∈ closure W, f x ≤ M := by
  intro x hx
  have hcwa : ContinuousWithinAt f W x := (hf.continuousWithinAt hx).mono subset_closure
  have hneBot : (𝓝[W] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hx
  have hev : ∀ᶠ y in 𝓝[W] x, f y ≤ M :=
    Filter.eventually_of_mem self_mem_nhdsWithin fun y hy => hle y hy
  exact le_of_tendsto hcwa.tendsto hev

/-- A sequence within `o(1)` of a convergent sequence converges to the same limit. -/
theorem aux_lem_skeleton_tendsto_of_bounded_diff
    (F G : ℕ → ℝ) (L : ℝ) (hG : Tendsto G atTop (𝓝 L))
    (hbound : ∀ n : ℕ, |F n - G n| ≤ 1 / (n + 1 : ℝ)) :
    Tendsto F atTop (𝓝 L) := by
  have hb : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have habs : Tendsto (fun n => |F n - G n|) atTop (𝓝 0) :=
    squeeze_zero (fun n => abs_nonneg _) hbound hb
  have hdiff : Tendsto (fun n => F n - G n) atTop (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero (fun n => F n - G n)).mpr habs
  have hsum : Tendsto (fun n => (F n - G n) + G n) atTop (𝓝 (0 + L)) := hdiff.add hG
  simpa using hsum



theorem aux_lem_skeleton_S2
    (F : ℕ → ℕ → ℝ) (L : ℕ → ℝ) (hF : ∀ n, Tendsto (F n) atTop (𝓝 (L n)))
    (G : ℕ → ℝ) (hG : Tendsto G atTop (𝓝 0)) :
    ∃ kf : ℕ → ℕ, ∀ n : ℕ, |F n (kf n) - L n| ≤ 1 / (n + 1 : ℝ) ∧ |G (kf n)| ≤ 1 / (n + 1 : ℝ) := by
  have hex : ∀ n : ℕ, ∃ k : ℕ, |F n k - L n| ≤ 1 / (n + 1 : ℝ) ∧ |G k| ≤ 1 / (n + 1 : ℝ) := by
    intro n
    have hn : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    have h1 : ∀ᶠ k in atTop, dist (F n k) (L n) < 1 / (n + 1 : ℝ) := by
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (hF n)) _ hn
      exact eventually_atTop.mpr ⟨N, hN⟩
    have h2 : ∀ᶠ k in atTop, dist (G k) 0 < 1 / (n + 1 : ℝ) := by
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hG) _ hn
      exact eventually_atTop.mpr ⟨N, hN⟩
    obtain ⟨k, hk1, hk2⟩ := (h1.and h2).exists
    refine ⟨k, ?_, ?_⟩
    · rw [Real.dist_eq] at hk1; exact hk1.le
    · rw [Real.dist_eq, sub_zero] at hk2; exact hk2.le
  choose kf hkf using hex
  exact ⟨kf, hkf⟩

section
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped Pointwise




/-- `sobolevDataOfH1` is additive, mirroring the already-proved subtraction fact
`aux_prop_gluing_sobolevDataOfH1_sub` (`prop_gluing`). -/
theorem aux_lem_skeleton_sobolevDataOfH1_add {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (u v : H1Function (Ω : Set (SpatialCoordinates d))) :
    sobolevDataOfH1 (u + v) = sobolevDataOfH1 u + sobolevDataOfH1 v := by
  unfold sobolevDataOfH1
  ext1
  · simp only [Prod.fst_add]
    rw [← MemLp.toLp_add]
    apply (MemLp.toLp_eq_toLp_iff _ _).mpr
    exact Filter.Eventually.of_forall (fun x => by simp)
  · funext i
    simp only [Prod.snd_add, Pi.add_apply]
    rw [← MemLp.toLp_add]
    apply (MemLp.toLp_eq_toLp_iff _ _).mpr
    exact Filter.Eventually.of_forall (fun x => by simp)

/-- The abstract coefficient form evaluated at the `sobolevDataOfH1` image of a native `H1`
function is exactly the native `energy`. This is `aux_prop_gluing_responseForm_eq_energy`
without the extraneous `S.space` membership (`sobolevCoefficientForm` needs no such
membership, unlike `responseForm`). -/
theorem aux_lem_skeleton_sobolevCoefficientForm_eq_energy {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (aC : PositiveCoefficient Ω) (a : SpatialCoordinates d → ℝ)
    (haC : ((aC.val : SpatialCoordinates d → ℝ))
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] a)
    (Lam : ℝ) (ha0 : ∀ x ∈ (Ω : Set (SpatialCoordinates d)), 0 ≤ a x)
    (haLam : ∀ x ∈ (Ω : Set (SpatialCoordinates d)), a x ≤ Lam)
    (hameas : AEStronglyMeasurable a (volume.restrict (Ω : Set (SpatialCoordinates d))))
    (D : H1Function (Ω : Set (SpatialCoordinates d))) :
    sobolevCoefficientForm aC (sobolevDataOfH1 D) (sobolevDataOfH1 D) =
      energy a (Ω : Set (SpatialCoordinates d)) D := by
  rw [sobolevCoefficientForm_apply]
  unfold energy
  have hi : ∀ i : Fin d, ∫ y in (Ω : Set (SpatialCoordinates d)),
      aC.val y * ((sobolevDataOfH1 D).2 i y * (sobolevDataOfH1 D).2 i y) =
      ∫ y in (Ω : Set (SpatialCoordinates d)), a y * (D.grad y i * D.grad y i) := by
    intro i
    apply integral_congr_ae
    filter_upwards [haC, sobolevDataOfH1_snd_coeFn D i] with y h1 h2
    rw [h1, h2]
  simp_rw [hi]
  rw [← integral_finsetSum]
  · congr 1
    funext y
    simp only [vecDot, Finset.mul_sum]
  · intro i _
    have hint : Integrable (fun y => D.grad y i * D.grad y i)
        (volume.restrict (Ω : Set (SpatialCoordinates d))) :=
      (D.gradMemL2 i).integrable_mul (D.gradMemL2 i)
    refine Integrable.bdd_mul (c := Lam) hint hameas ?_
    filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (ha0 y hy)]
    exact haLam y hy



theorem aux_lem_skeleton_cellDirichletInfimum_le_dirichletResponse {d : ℕ} [NeZero d]
    {Ω : Opens (SpatialCoordinates d)}
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Ω,
      ‖(u : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) u‖)
    (aC : PositiveCoefficient Ω) (a : SpatialCoordinates d → ℝ)
    (haC : ((aC.val : SpatialCoordinates d → ℝ))
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] a)
    (Lam : ℝ)
    (ha0 : ∀ x ∈ (Ω : Set (SpatialCoordinates d)), 0 ≤ a x)
    (haLam : ∀ x ∈ (Ω : Set (SpatialCoordinates d)), a x ≤ Lam)
    (hameas : AEStronglyMeasurable a (volume.restrict (Ω : Set (SpatialCoordinates d))))
    (e : H1Function (Ω : Set (SpatialCoordinates d))) :
    cellDirichletInfimum a (Ω : Set (SpatialCoordinates d)) e ≤
      dirichletResponse (killedResponseSpace hP) aC
        (⟨sobolevDataOfH1 e, sobolevDataOfH1_mem_weak e⟩ : weakSobolevGraph Ω) := by
  let b : weakSobolevGraph Ω := ⟨sobolevDataOfH1 e, sobolevDataOfH1_mem_weak e⟩
  have hkmem : (dirichletMinimizer (killedResponseSpace hP) aC b : SobolevData Ω) -
      (b : SobolevData Ω) ∈ killedSobolevGraph Ω :=
    dirichletMinimizer_mem_affine (killedResponseSpace hP) aC b
  let kw : killedSobolevGraph Ω :=
    ⟨(dirichletMinimizer (killedResponseSpace hP) aC b : SobolevData Ω) - (b : SobolevData Ω),
      hkmem⟩
  obtain ⟨v, hvval, hvgrad⟩ := exists_nativeH10Function_of_killedSobolevGraph kw
  have hZT : HasZeroTraceDifferenceOn (Ω : Set (SpatialCoordinates d)) (e + v.toH1Function) e :=
    ⟨v, fun _ => rfl, fun _ => rfl⟩
  have hsob_v : sobolevDataOfH1 v.toH1Function = (kw : SobolevData Ω) := by
    refine Prod.ext ?_ ?_
    · exact Lp.ext ((MemLp.coeFn_toLp v.toH1Function.memL2).trans
        (Filter.EventuallyEq.of_eq hvval))
    · funext i
      have hgrad_i : (fun x => v.toH1Function.grad x i) = fun x => (kw : SobolevData Ω).2 i x := by
        funext x; rw [hvgrad]
      exact Lp.ext ((MemLp.coeFn_toLp (v.toH1Function.gradMemL2 i)).trans
        (Filter.EventuallyEq.of_eq hgrad_i))
  have hsob_u : sobolevDataOfH1 (e + v.toH1Function) =
      (dirichletMinimizer (killedResponseSpace hP) aC b : SobolevData Ω) := by
    rw [aux_lem_skeleton_sobolevDataOfH1_add e v.toH1Function, hsob_v]
    show (b : SobolevData Ω) +
        ((dirichletMinimizer (killedResponseSpace hP) aC b : SobolevData Ω) - (b : SobolevData Ω))
      = (dirichletMinimizer (killedResponseSpace hP) aC b : SobolevData Ω)
    abel
  have hEnergy : energy a (Ω : Set (SpatialCoordinates d)) (e + v.toH1Function) =
      dirichletResponse (killedResponseSpace hP) aC b := by
    rw [← aux_lem_skeleton_sobolevCoefficientForm_eq_energy aC a haC Lam ha0 haLam hameas
      (e + v.toH1Function), hsob_u]
    rfl
  have hWmeas : MeasurableSet (Ω : Set (SpatialCoordinates d)) := Ω.isOpen.measurableSet
  have hbdd := (aux_prop_gluing_infimum_set_bdd (Ω : Set (SpatialCoordinates d)) hWmeas a ha0 e).1
  calc cellDirichletInfimum a (Ω : Set (SpatialCoordinates d)) e
      ≤ energy a (Ω : Set (SpatialCoordinates d)) (e + v.toH1Function) :=
        csInf_le hbdd ⟨e + v.toH1Function, hZT, rfl⟩
    _ = dirichletResponse (killedResponseSpace hP) aC b := hEnergy




theorem aux_lem_skeleton_ext_extension_small
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (beta : ℝ) (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
        ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
        (a : PositiveCoefficient (centeredCube z r hr))
        (G : SpatialCoordinates d → ℝ)
        (b : weakSobolevGraph (centeredCube z r hr)),
        ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)) →
        IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G →
        ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G →
        dirichletResponse (killedResponseSpace hP) a b ≤
          C * Jc.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 * r ^ ((d : ℝ) - 2) *
            (r ^ beta * holderSeminorm beta
              (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2 := by
  exact (lem_extension d hd Jc Xc Sf).1 beta hbeta

theorem aux_lem_skeleton_ext_dilation_dist
    (d : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (x y : SpatialCoordinates d) :
    dist (cubeDilation z (0 : SpatialCoordinates d) r x)
        (cubeDilation z (0 : SpatialCoordinates d) r y) =
      r * dist x y := by
  rw [dist_eq_norm, dist_eq_norm]
  have hxy : cubeDilation z (0 : SpatialCoordinates d) r x -
      cubeDilation z (0 : SpatialCoordinates d) r y = r • (x - y) := by
    funext i
    simp [cubeDilation, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hxy, norm_smul, Real.norm_eq_abs, abs_of_pos hr]

theorem aux_lem_skeleton_ext_dilation_frontier
    (d : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (x : SpatialCoordinates d)
    (hx : x ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d))) :
    cubeDilation z (0 : SpatialCoordinates d) r x ∈
      frontier (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  change x ∈ frontier (Metric.ball (0 : SpatialCoordinates d) (1 / 2)) at hx
  change cubeDilation z (0 : SpatialCoordinates d) r x ∈
    frontier (Metric.ball z (r / 2))
  rw [frontier_ball _ (by positivity)] at hx ⊢
  have hx' : dist x (0 : SpatialCoordinates d) = 1 / 2 := by
    simpa [Metric.mem_sphere] using hx
  have hzero : cubeDilation z (0 : SpatialCoordinates d) r
      (0 : SpatialCoordinates d) = z := by
    funext i
    simp [cubeDilation]
  have hd := aux_lem_skeleton_ext_dilation_dist d z r hr x (0 : SpatialCoordinates d)
  rw [hzero] at hd
  simpa [Metric.mem_sphere, hx'] using! hd

theorem aux_lem_skeleton_ext_dilation_holder
    (d : ℕ) (hd : 2 ≤ d) (beta : ℝ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (G : SpatialCoordinates d → ℝ)
    (hG : IsHolderOn beta
      (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) :
    IsHolderOn beta
      (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)))
      (fun x => G (cubeDilation z (0 : SpatialCoordinates d) r x)) ∧
    holderSeminorm beta
        (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
          Set (SpatialCoordinates d)))
        (fun x => G (cubeDilation z (0 : SpatialCoordinates d) r x)) ≤
      r ^ beta * holderSeminorm beta
        (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G ∧
    0 ≤ holderSeminorm beta
      (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)))
      (fun x => G (cubeDilation z (0 : SpatialCoordinates d) r x)) := by
  have hd0 : 0 < d := by omega
  let : NeZero d := ⟨Nat.ne_of_gt hd0⟩
  have hunit : IsHolderOn beta
      (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)))
      (fun x => G (cubeDilation z (0 : SpatialCoordinates d) r x)) := by
    rcases hG with ⟨C, hC⟩
    refine ⟨r ^ beta * C, ?_⟩
    rintro q ⟨x, hx, y, hy, hxy, rfl⟩
    have hTx := aux_lem_skeleton_ext_dilation_frontier d z r hr x hx
    have hTy := aux_lem_skeleton_ext_dilation_frontier d z r hr y hy
    have hTxy : cubeDilation z (0 : SpatialCoordinates d) r x ≠
        cubeDilation z (0 : SpatialCoordinates d) r y := by
      intro h
      apply hxy
      exact (cubeDilationEquiv z (0 : SpatialCoordinates d) hr.ne').injective
        (by simpa using h)
    have hq := hC ⟨cubeDilation z (0 : SpatialCoordinates d) r x, hTx,
      cubeDilation z (0 : SpatialCoordinates d) r y, hTy, hTxy, rfl⟩
    have hd := sqrt_sum_sq_cubeDilation z (0 : SpatialCoordinates d) hr x y
    rw [hd] at hq
    obtain ⟨j, hj⟩ : ∃ j : Fin d, x j ≠ y j := by
      by_contra h
      push Not at h
      exact hxy (funext h)
    have hsum : 0 < ∑ j : Fin d, (x j - y j) ^ 2 := by
      apply (Finset.sum_pos_iff_of_nonneg
        (fun j _ => sq_nonneg (x j - y j))).2
      exact ⟨j, Finset.mem_univ _, sq_pos_of_ne_zero (sub_ne_zero.mpr hj)⟩
    have hden : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) :=
      Real.sqrt_pos.mpr hsum
    have hden0 : Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≠ 0 := hden.ne'
    change |G (cubeDilation z (0 : SpatialCoordinates d) r x) -
        G (cubeDilation z (0 : SpatialCoordinates d) r y)| /
          (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta ≤
        r ^ beta * C
    calc
      |G (cubeDilation z (0 : SpatialCoordinates d) r x) -
          G (cubeDilation z (0 : SpatialCoordinates d) r y)| /
          (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta =
        r ^ beta *
          (|G (cubeDilation z (0 : SpatialCoordinates d) r x) -
            G (cubeDilation z (0 : SpatialCoordinates d) r y)| /
            (r * Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta) := by
              rw [Real.mul_rpow (le_of_lt hr) hden.le]
              field_simp [hden0]
      _ ≤ r ^ beta * C := by
        exact mul_le_mul_of_nonneg_left hq (Real.rpow_nonneg (le_of_lt hr) _)
  have hGbdd : BddAbove (holderRatioSet beta
      (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) := hG
  rcases hunit with ⟨C, hC⟩
  have hunitbdd : BddAbove (holderRatioSet beta
      (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)))
      (fun x => G (cubeDilation z (0 : SpatialCoordinates d) r x))) := ⟨C, hC⟩
  have hratio_nonempty :
      (holderRatioSet beta
        (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
          Set (SpatialCoordinates d)))
        (fun x => G (cubeDilation z (0 : SpatialCoordinates d) r x))).Nonempty := by
    change (holderRatioSet beta
      (frontier (Metric.ball (0 : SpatialCoordinates d) (1 / 2)))
      (fun x => G (cubeDilation z (0 : SpatialCoordinates d) r x))).Nonempty
    rw [frontier_ball _ (by norm_num)]
    rcases (NormedSpace.sphere_nonempty (E := SpatialCoordinates d)).mpr
      (by norm_num : (0 : ℝ) ≤ 1 / 2) with ⟨x, hx⟩
    have hxfront : x ∈ Metric.sphere (0 : SpatialCoordinates d) (1 / 2) := hx
    have hyfront : -x ∈ Metric.sphere (0 : SpatialCoordinates d) (1 / 2) := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hx
    have hxnorm : ‖x‖ = (1 / 2 : ℝ) := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hx
    have hxy : x ≠ -x := by
      intro heq
      have hsum : x + x = 0 := eq_neg_iff_add_eq_zero.mp heq
      have hsmul : (2 : ℝ) • x = 0 := by simpa [two_smul] using hsum
      have hxzero : x = 0 := (smul_eq_zero.mp hsmul).resolve_left (by norm_num)
      rw [hxzero] at hxnorm
      norm_num at hxnorm
    refine ⟨|G (cubeDilation z (0 : SpatialCoordinates d) r x) -
        G (cubeDilation z (0 : SpatialCoordinates d) r (-x))| /
        (Real.sqrt (∑ j : Fin d, (x j - (-x) j) ^ 2)) ^ beta, ?_⟩
    exact ⟨x, hxfront, -x, hyfront, hxy, rfl⟩
  have hseminorm_nonneg : 0 ≤ holderSeminorm beta
      (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)))
      (fun x => G (cubeDilation z (0 : SpatialCoordinates d) r x)) := by
    unfold holderSeminorm
    have hratio' := hratio_nonempty
    rcases hratio' with ⟨q, hq⟩
    have hsup := le_csSup hunitbdd hq
    have hq0 : 0 ≤ q := by
      obtain ⟨x, hx, y, hy, hxy, rfl⟩ := hq
      positivity
    exact hq0.trans hsup
  refine ⟨⟨C, hC⟩, ?_, hseminorm_nonneg⟩
  unfold holderSeminorm
  apply csSup_le hratio_nonempty
  rintro q ⟨x, hx, y, hy, hxy, rfl⟩
  have hTx := aux_lem_skeleton_ext_dilation_frontier d z r hr x hx
  have hTy := aux_lem_skeleton_ext_dilation_frontier d z r hr y hy
  have hTxy : cubeDilation z (0 : SpatialCoordinates d) r x ≠
      cubeDilation z (0 : SpatialCoordinates d) r y := by
    intro h
    apply hxy
    exact (cubeDilationEquiv z (0 : SpatialCoordinates d) hr.ne').injective
      (by simpa using h)
  have hd := sqrt_sum_sq_cubeDilation z (0 : SpatialCoordinates d) hr x y
  obtain ⟨j, hj⟩ : ∃ j : Fin d, x j ≠ y j := by
    by_contra h
    push Not at h
    exact hxy (funext h)
  have hsum : 0 < ∑ j : Fin d, (x j - y j) ^ 2 := by
    apply (Finset.sum_pos_iff_of_nonneg
      (fun j _ => sq_nonneg (x j - y j))).2
    exact ⟨j, Finset.mem_univ _, sq_pos_of_ne_zero (sub_ne_zero.mpr hj)⟩
  have hden : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) :=
    Real.sqrt_pos.mpr hsum
  have hqmem :
      |G (cubeDilation z (0 : SpatialCoordinates d) r x) -
          G (cubeDilation z (0 : SpatialCoordinates d) r y)| /
        (Real.sqrt (∑ j : Fin d,
          (cubeDilation z (0 : SpatialCoordinates d) r x j -
            cubeDilation z (0 : SpatialCoordinates d) r y j) ^ 2)) ^ beta ∈
      holderRatioSet beta
        (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G := by
    exact ⟨cubeDilation z (0 : SpatialCoordinates d) r x, hTx,
      cubeDilation z (0 : SpatialCoordinates d) r y, hTy, hTxy, rfl⟩
  have hq := le_csSup hGbdd hqmem
  have heq :
      |G (cubeDilation z (0 : SpatialCoordinates d) r x) -
          G (cubeDilation z (0 : SpatialCoordinates d) r y)| /
        (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta =
      r ^ beta *
        (|G (cubeDilation z (0 : SpatialCoordinates d) r x) -
          G (cubeDilation z (0 : SpatialCoordinates d) r y)| /
        (Real.sqrt (∑ j : Fin d,
          (cubeDilation z (0 : SpatialCoordinates d) r x j -
            cubeDilation z (0 : SpatialCoordinates d) r y j) ^ 2)) ^ beta) := by
    rw [hd]
    rw [Real.mul_rpow (le_of_lt hr) hden.le]
    field_simp [hden.ne']
  calc
    _ = r ^ beta *
        (|G (cubeDilation z (0 : SpatialCoordinates d) r x) -
          G (cubeDilation z (0 : SpatialCoordinates d) r y)| /
        (Real.sqrt (∑ j : Fin d,
          (cubeDilation z (0 : SpatialCoordinates d) r x j -
            cubeDilation z (0 : SpatialCoordinates d) r y j) ^ 2)) ^ beta) := heq
    _ ≤ r ^ beta * sSup (holderRatioSet beta
        (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) :=
      mul_le_mul_of_nonneg_left hq (Real.rpow_nonneg (le_of_lt hr) _)

theorem aux_lem_skeleton_ext_dilation_killed_pushforward
    (d : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (h1 : (0 : ℝ) < 1)
    (v : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 h1)) :
    ∃ w : killedSobolevGraph (centeredCube z r hr),
      (∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
        (w : SobolevData (centeredCube z r hr)).1 x =
          (v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1
            (cubeDilation (0 : SpatialCoordinates d) z r⁻¹ x)) ∧
      (∀ i : Fin d, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
        ((w : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ) x =
          r⁻¹ * ((v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i)
            (cubeDilation (0 : SpatialCoordinates d) z r⁻¹ x)) := by
  obtain ⟨u, hu_val, hu_grad⟩ :=
    SubdiffusiveProcess.exists_nativeH10Function_of_killedSobolevGraph v
  have hgeom := aux_lane4_coercivity_dilation_cube_geometry d z r hr h1
  have htranslate : (centeredCube z r hr : Set (SpatialCoordinates d)) =
      Homogenization.translateSet z
        (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)) :=
    hgeom.1
  have hscale : (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)) =
      r • (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)) :=
    hgeom.2
  let U1 : Set (SpatialCoordinates d) :=
    (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))
  let U0 : Set (SpatialCoordinates d) :=
    (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d))
  have hinv : (r⁻¹ : ℝ) • (r • U1) = U1 := by
    ext x
    constructor
    · intro hx
      have hx' : r • x ∈ r • U1 :=
        by simpa only [inv_inv] using
          (Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hr.ne')
            (r • U1) x).mp hx
      have hx'' : r⁻¹ • (r • x) ∈ U1 :=
        (Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne' U1 (r • x)).mp hx'
      simpa [smul_smul, hr.ne'] using hx''
    · intro hx
      have hx' : r • x ∈ r • U1 := by
        apply (Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne' U1 (r • x)).mpr
        simpa [smul_smul, hr.ne'] using hx
      exact (Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hr.ne')
        (r • U1) x).mpr (by simpa only [inv_inv] using hx')
  let ucast : Homogenization.H10Function ((r⁻¹ : ℝ) • (r • U1)) := hinv.symm ▸ u
  have hucast_val : ucast.toFun = u.toFun := by
    simpa [ucast] using
      (_root_.SubdiffusiveProcess.Paper.aux_lane4_coercivity_dilation_h10_cast_toFun hinv.symm u)
  have hucast_grad : ucast.grad = u.grad := by
    simpa [ucast] using
      (_root_.SubdiffusiveProcess.Paper.aux_lane4_coercivity_dilation_h10_cast_grad hinv.symm u)
  let uS : Homogenization.H10Function (r • U1) :=
    Homogenization.H10Function.unscale (inv_pos.mpr hr) ucast
  have hscale' : U0 = r • U1 := by simpa [U0, U1] using hscale
  let u0 : Homogenization.H10Function U0 := hscale'.symm ▸ uS
  let htranslate' : (centeredCube z r hr : Set (SpatialCoordinates d)) =
      Homogenization.translateSet z U0 := by simpa [U0] using htranslate
  let uT : Homogenization.H10Function (Homogenization.translateSet z U0) :=
    Homogenization.H10Function.translate u0 z
  let wNative : Homogenization.H10Function
      (centeredCube z r hr : Set (SpatialCoordinates d)) := htranslate'.symm ▸ uT
  obtain ⟨w, hw_val, hw_grad⟩ :=
    _root_.SubdiffusiveProcess.EllipticRegularity.exists_killedSobolevGraph_of_nativeH10 wNative
  have hwNative_val : wNative.toH1Function.toFun = uT.toH1Function.toFun := by
    simpa [wNative] using
      (_root_.SubdiffusiveProcess.Paper.aux_lane4_coercivity_dilation_h10_cast_toFun htranslate'.symm uT)
  have hwNative_grad : wNative.toH1Function.grad = uT.toH1Function.grad := by
    simpa [wNative] using
      (_root_.SubdiffusiveProcess.Paper.aux_lane4_coercivity_dilation_h10_cast_grad htranslate'.symm uT)
  have hu0_val : u0.toH1Function.toFun = uS.toH1Function.toFun := by
    simpa [u0] using
      (_root_.SubdiffusiveProcess.Paper.aux_lane4_coercivity_dilation_h10_cast_toFun hscale'.symm uS)
  have hu0_grad : u0.toH1Function.grad = uS.toH1Function.grad := by
    simpa [u0] using
      (_root_.SubdiffusiveProcess.Paper.aux_lane4_coercivity_dilation_h10_cast_grad hscale'.symm uS)
  refine ⟨w, ?_, ?_⟩
  · filter_upwards [hw_val] with x hx
    rw [hx]
    rw [hwNative_val,
      Homogenization.H10Function.translate_toH1Function,
      Homogenization.H1Function.translate_toFun]
    change u0.toH1Function.toFun (x - z) = _
    rw [hu0_val]
    change (Homogenization.H10Function.unscale (inv_pos.mpr hr) ucast).toH1Function.toFun
      (x - z) = _
    rw [Homogenization.H10Function.unscale_toH1Function,
      Homogenization.H1Function.unscale_toFun]
    change ucast.toH1Function.toFun (r⁻¹ • (x - z)) = _
    rw [hucast_val]
    rw [hu_val]
    congr 1 ; funext i ; simp [cubeDilation, Pi.smul_apply, smul_eq_mul]
  · intro i
    filter_upwards [hw_grad i] with x hx
    rw [hx]
    rw [hwNative_grad,
      Homogenization.H10Function.translate_toH1Function,
      Homogenization.H1Function.translate_grad]
    rw [hu0_grad]
    change (Homogenization.H10Function.unscale (inv_pos.mpr hr) ucast).toH1Function.grad
      (x - z) i = _
    rw [Homogenization.H10Function.unscale_toH1Function,
      Homogenization.H1Function.unscale_grad]
    change (r⁻¹ • ucast.toH1Function.grad (r⁻¹ • (x - z))) i = _
    rw [hucast_grad]
    rw [hu_grad]
    simp only [Pi.smul_apply, smul_eq_mul]
    congr 2 ; funext j ;
      simp [cubeDilation, Pi.smul_apply, smul_eq_mul]

theorem aux_lem_skeleton_ext_large_extension
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d)
    (_Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (_Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (beta : ℝ) (_hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (CE : ℝ) (hCE : 0 < CE)
    (hEsmall : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
        ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
        (a : PositiveCoefficient (centeredCube z r hr))
        (G : SpatialCoordinates d → ℝ)
        (b : weakSobolevGraph (centeredCube z r hr)),
        ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)) →
        IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G →
        ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G →
        dirichletResponse (killedResponseSpace hP) a b ≤
          CE * Jc.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 * r ^ ((d : ℝ) - 2) *
            (r ^ beta * holderSeminorm beta
              (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (_hr1 : 1 < r)
    (hP : ∃ C : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        C * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (a : PositiveCoefficient (centeredCube z r hr))
    (G : SpatialCoordinates d → ℝ)
    (b : weakSobolevGraph (centeredCube z r hr))
    (hG : ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)))
    (hHolder : IsHolderOn beta
      (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G)
    (hEq : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G) :
    dirichletResponse (killedResponseSpace hP) a b ≤
        CE * Jc.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 *
          r ^ ((d : ℝ) - 2) *
          (r ^ beta * holderSeminorm beta
            (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2 := by
  let h1 : (0 : ℝ) < 1 := one_pos
  have hd0 : 0 < d := by omega
  let : NeZero d := ⟨Nat.ne_of_gt hd0⟩
  have hgeom : Homogenization.IsOpenBoundedConvexDomain
      (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)) :=
    SubdiffusiveProcess.lane2_isOpenBoundedConvexDomain_centeredCube
      (0 : SpatialCoordinates d) h1
  obtain ⟨hPunit, _⟩ :=
    exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain
      (centeredCube (0 : SpatialCoordinates d) 1 h1) hgeom
  obtain ⟨a', ha'⟩ :=
    _root_.SubdiffusiveProcess.Paper.lane4_dilation_coefficient_transport d z 0 r hr h1 a
  let T : SpatialCoordinates d → SpatialCoordinates d :=
    cubeDilation z (0 : SpatialCoordinates d) r
  let G' : SpatialCoordinates d → ℝ := fun x => G (T x)
  have hclosed : ∀ x ∈ (closedCube (0 : SpatialCoordinates d) 1 h1 :
      Set (SpatialCoordinates d)), T x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) := by
    intro x hx
    change x ∈ Metric.closedBall (0 : SpatialCoordinates d) (1 / 2) at hx
    change T x ∈ Metric.closedBall z (r / 2)
    have hzero : cubeDilation z (0 : SpatialCoordinates d) r
        (0 : SpatialCoordinates d) = z := by
      funext i
      simp [cubeDilation]
    have hdT := aux_lem_skeleton_ext_dilation_dist d z r hr x
      (0 : SpatialCoordinates d)
    rw [hzero] at hdT
    change cubeDilation z (0 : SpatialCoordinates d) r x ∈
      Metric.closedBall z (r / 2)
    rw [Metric.mem_closedBall, hdT]
    have hmul := mul_le_mul_of_nonneg_left hx hr.le
    convert hmul using 1 ; ring
  have hG' : ContinuousOn G'
      (closedCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)) := by
    dsimp [G']
    exact hG.comp (continuous_cubeDilation z 0 r).continuousOn hclosed
  obtain ⟨hHolder', hHolderSeminorm, hHolderNonneg⟩ :=
    aux_lem_skeleton_ext_dilation_holder d hd beta z r hr G hHolder
  obtain ⟨b0, hb0val, hb0grad⟩ :=
    aux_lane4_coercivity_dilation_weak_pullback d z r hr h1 b
  have hqmp : Measure.QuasiMeasurePreserving T
      (volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)))
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    refine ⟨(continuous_cubeDilation z 0 r).measurable, ?_⟩
    rw [show Measure.map T
        (volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))) =
          Measure.map (cubeDilation z 0 r)
            (volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))) by rfl]
    rw [map_cubeDilation_restrict z 0 hr h1]
    exact Measure.AbsolutelyContinuous.rfl.smul_left _
  have hcomp := hqmp.ae_eq_comp hEq
  have hEq' : ((b0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 :
      SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))] G' := by
    filter_upwards [hb0val, hcomp] with x hxb hxc
    exact hxb.trans (by simpa [T, Function.comp_def] using hxc)
  have he := hEsmall (0 : SpatialCoordinates d) 1 h1 (by norm_num) hPunit a' G' b0
    hG' hHolder' hEq'
  have hLam : Jc.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 =
      Jc.Lam (0 : SpatialCoordinates d) 1 h1 a' (0 : SpatialCoordinates d) 1
        ((beta - 1 / 2) / 4) 2 := by
    apply Jc.Lam_dilation z r hr a 0 h1 a'
    filter_upwards [ha'] with x hx
    simpa only [cubeDilation_apply, sub_zero] using! hx
  let v0 : weakSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 h1) :=
    dirichletMinimizer (killedResponseSpace hPunit) a' b0
  have hq0mem : (v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)) -
      (b0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)) ∈
      killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 h1) := by
    exact dirichletMinimizer_mem_affine (killedResponseSpace hPunit) a' b0
  let q0 : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 h1) :=
    ⟨(v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)) -
      (b0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)), hq0mem⟩
  obtain ⟨q, hqval, hqgrad⟩ :=
    aux_lem_skeleton_ext_dilation_killed_pushforward d z r hr h1 q0
  have hinvcomp : ∀ x : SpatialCoordinates d,
      cubeDilation (0 : SpatialCoordinates d) z r⁻¹
          (cubeDilation z (0 : SpatialCoordinates d) r x) = x := by
    intro x
    funext i
    simp [cubeDilation]
    field_simp [ne_of_gt hr]
  have hqcomp := hqmp.ae_eq_comp hqval
  have hqcomp' : ∀ᵐ x ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)),
      ((q : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
          (T x) =
        ((q0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 :
          SpatialCoordinates d → ℝ) x := by
    filter_upwards [hqcomp] with x hx
    simpa [T, Function.comp_def, hinvcomp x] using hx
  have hqgradcomp : ∀ i : Fin d, ∀ᵐ x ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)),
      ((q : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ)
          (T x) = r⁻¹ *
        ((q0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i :
          SpatialCoordinates d → ℝ) x := by
    intro i
    have h := hqmp.ae_eq_comp (hqgrad i)
    filter_upwards [h] with x hx
    simpa [T, Function.comp_def, hinvcomp x] using hx
  have hval :
      ((v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 :
        SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))]
        fun x => ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
            (T x) + ((q : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
            (T x) := by
    have hsub := Lp.coeFn_sub
      ((v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1)
      ((b0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1)
    filter_upwards [hb0val, hqcomp', hsub] with x hxb hxq hy
    rw [← hxb, hxq]
    change (v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 x =
      (b0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 x +
        ((v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 -
          (b0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1) x
    calc
      _ = ((b0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 :
          SpatialCoordinates d → ℝ) x +
          (((v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 :
            SpatialCoordinates d → ℝ) x -
            ((b0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 :
              SpatialCoordinates d → ℝ) x) := by ring
      _ = _ := by
        exact congrArg (fun t : ℝ =>
          ((b0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 :
            SpatialCoordinates d → ℝ) x + t) hy.symm
  have hgrad : ∀ i : Fin d,
      ((v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i :
        SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))]
        fun x => r * (((b : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ)
            (T x) + ((q : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ)
            (T x)) := by
    intro i
    have hsub := Lp.coeFn_sub
      ((v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i)
      ((b0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i)
    filter_upwards [hb0grad i, hqgradcomp i, hsub] with x hxb hxg hy
    rw [hxg]
    rw [mul_add, ← hxb]
    change (v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i x =
      (b0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i x +
        r * (r⁻¹ * (((v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i -
          (b0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i) x))
    rw [hy]
    field_simp [ne_of_gt hr]
    have hpoint :
        ((v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i :
          SpatialCoordinates d → ℝ) x =
          ((b0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i :
            SpatialCoordinates d → ℝ) x +
            (((v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i :
              SpatialCoordinates d → ℝ) x -
              ((b0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i :
                SpatialCoordinates d → ℝ) x) := by
      abel
    simpa only [Pi.sub_apply] using hpoint
  have hvalE :
      ((v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 :
        SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))]
        fun x => (((b : SobolevData (centeredCube z r hr)) +
          (q : SobolevData (centeredCube z r hr))).1 : SpatialCoordinates d → ℝ)
            (T x) := by
    have hadd := Lp.coeFn_add
      ((b : SobolevData (centeredCube z r hr)).1)
      ((q : SobolevData (centeredCube z r hr)).1)
    have hadd' := hqmp.ae_eq_comp hadd
    filter_upwards [hval, hadd'] with x hxv hxa
    exact hxv.trans hxa.symm
  have hgradE : ∀ i : Fin d,
      ((v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i :
        SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))]
        fun x => r * ((((b : SobolevData (centeredCube z r hr)) +
          (q : SobolevData (centeredCube z r hr))).2 i : SpatialCoordinates d → ℝ)
            (T x)) := by
    intro i
    have hadd := Lp.coeFn_add
      ((b : SobolevData (centeredCube z r hr)).2 i)
      ((q : SobolevData (centeredCube z r hr)).2 i)
    have hadd' := hqmp.ae_eq_comp hadd
    filter_upwards [hgrad i, hadd'] with x hxv hxa
    have hcompadd :
        ((b : SobolevData (centeredCube z r hr)) +
          (q : SobolevData (centeredCube z r hr))).2 i =
          (b : SobolevData (centeredCube z r hr)).2 i +
            (q : SobolevData (centeredCube z r hr)).2 i := by
      rfl
    rw [hcompadd]
    have hxa2 :
        ((((b : SobolevData (centeredCube z r hr)).2 i) +
          ((q : SobolevData (centeredCube z r hr)).2 i)) :
            DomainL2 (centeredCube z r hr)) (T x) =
          ((b : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ)
            (T x) + ((q : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ)
            (T x) := by
      simpa [Function.comp_def] using hxa
    calc
      _ = r * (((b : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ)
          (T x) + ((q : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ)
          (T x)) := hxv
      _ = _ := by rw [hxa2.symm]
  have henergy := aux_lane4_coercivity_dilation_energy_scaling d z r hr h1 a a'
    ((b : SobolevData (centeredCube z r hr)) + (q : SobolevData (centeredCube z r hr)))
    (v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)) ha' hvalE hgradE
  have hleast := (dirichletResponse_isLeast (killedResponseSpace hP) a b).2
    ⟨q, rfl⟩
  have hresp : dirichletResponse (killedResponseSpace hP) a b ≤
      r ^ ((d : ℝ) - 2) * dirichletResponse
        (killedResponseSpace hPunit) a' b0 := by
    calc
      _ ≤ sobolevCoefficientForm a
          ((b : SobolevData (centeredCube z r hr)) +
            (q : SobolevData (centeredCube z r hr)))
          ((b : SobolevData (centeredCube z r hr)) +
            (q : SobolevData (centeredCube z r hr))) := hleast
      _ = r ^ ((d : ℝ) - 2) * sobolevCoefficientForm a'
          (v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1))
          (v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)) := henergy
      _ = _ := by simp [v0, dirichletResponse]
  refine ?_
  have he' : dirichletResponse (killedResponseSpace hPunit) a' b0 ≤
      CE * Jc.Lam (0 : SpatialCoordinates d) 1 h1 a' (0 : SpatialCoordinates d) 1
        ((beta - 1 / 2) / 4) 2 *
        (holderSeminorm beta
          (frontier (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))) G') ^ 2 := by
    simpa [G'] using he
  have he'' : dirichletResponse (killedResponseSpace hPunit) a' b0 ≤
      CE * Jc.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 *
        (holderSeminorm beta
          (frontier (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))) G') ^ 2 := by
    rw [hLam]
    exact he'
  have hsq :
      (holderSeminorm beta
          (frontier (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))) G') ^ 2 ≤
        (r ^ beta * holderSeminorm beta
          (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2 := by
    have hnonneg : 0 ≤ holderSeminorm beta
        (frontier (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))) G' := by
      simpa [G'] using hHolderNonneg
    have hright : 0 ≤ r ^ beta * holderSeminorm beta
        (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G :=
      hnonneg.trans hHolderSeminorm
    nlinarith
  have hcoef : 0 ≤ CE * Jc.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 *
      r ^ ((d : ℝ) - 2) := by
    have hLamPos : 0 < Jc.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 :=
      Jc.Lam_pos z r hr a z r ((beta - 1 / 2) / 4) 2
    exact mul_nonneg
      (mul_nonneg (le_of_lt hCE) (le_of_lt hLamPos))
      (le_of_lt (Real.rpow_pos_of_pos hr _))
  calc
    dirichletResponse (killedResponseSpace hP) a b ≤
        r ^ ((d : ℝ) - 2) *
          dirichletResponse (killedResponseSpace hPunit) a' b0 := hresp
    _ ≤ r ^ ((d : ℝ) - 2) *
        (CE * Jc.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 *
          (holderSeminorm beta
            (frontier (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))) G') ^ 2) := by
      exact mul_le_mul_of_nonneg_left he''
        (le_of_lt (Real.rpow_pos_of_pos hr _))
    _ ≤ CE * Jc.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 *
        r ^ ((d : ℝ) - 2) *
          (r ^ beta * holderSeminorm beta
            (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hsq hcoef
      calc
        _ = (CE * Jc.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 *
            r ^ ((d : ℝ) - 2)) *
              (holderSeminorm beta
                (frontier (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))) G') ^ 2 := by ring
        _ ≤ (CE * Jc.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 *
            r ^ ((d : ℝ) - 2)) *
              (r ^ beta * holderSeminorm beta
                (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2 := hmul
        _ = _ := by ring
    _ = _ := by ring



theorem aux_lem_skeleton_cell_ext_bound {d : ℕ} (hd : 2 ≤ d)
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (beta : ℝ) (hbeta : 1 / 2 < beta) (hbeta1 : beta < 1)
    (c : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : SpatialCoordinates d → ℝ) (lam Lam : ℝ) (hlam : 0 < lam)
    (ha : ContinuousOn a (closure (centeredCube c r hr : Set (SpatialCoordinates d))))
    (hab : ∀ x ∈ (centeredCube c r hr : Set (SpatialCoordinates d)), lam ≤ a x ∧ a x ≤ Lam) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ e : H1Function (centeredCube c r hr : Set (SpatialCoordinates d)),
      ContinuousOn e.toFun (closure (centeredCube c r hr : Set (SpatialCoordinates d))) →
      _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta (frontier (centeredCube c r hr : Set (SpatialCoordinates d))) e.toFun →
      cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) e ≤
        K * (_root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (frontier (centeredCube c r hr : Set (SpatialCoordinates d))) e.toFun) ^ 2 := by
  have hd0 : d ≠ 0 := by omega
  let : NeZero d := ⟨hd0⟩
  let : MeasurableSpace C(SpatialCoordinates d, ℝ) := borel _
  have : BorelSpace C(SpatialCoordinates d, ℝ) := ⟨rfl⟩
  -- Step 1: a global continuous extension of `a`, hence an actual `PositiveCoefficient`.
  obtain ⟨a1, ha1cont, ha1eq⟩ :=
    aux_prop_gluing_coeff_extension
      (closure (centeredCube c r hr : Set (SpatialCoordinates d))) isClosed_closure a ha
  have hab1 : ∀ x ∈ (centeredCube c r hr : Set (SpatialCoordinates d)), lam ≤ a1 x ∧ a1 x ≤ Lam :=
    fun x hx => (ha1eq x (subset_closure hx)) ▸ hab x hx
  obtain ⟨aC, haC1⟩ :=
    lane2_exists_positiveCoefficient (U := centeredCube c r hr) ha1cont hlam hab1
  have haeAA1 : a1 =ᵐ[volume.restrict (centeredCube c r hr : Set (SpatialCoordinates d))] a := by
    filter_upwards [ae_restrict_mem (centeredCube c r hr).isOpen.measurableSet] with x hx
    exact ha1eq x (subset_closure hx)
  have haC : (aC.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube c r hr : Set (SpatialCoordinates d))] a :=
    haC1.trans haeAA1
  have hameas : AEStronglyMeasurable a
      (volume.restrict (centeredCube c r hr : Set (SpatialCoordinates d))) :=
    ha1cont.aestronglyMeasurable.congr haeAA1
  have ha0 : ∀ x ∈ (centeredCube c r hr : Set (SpatialCoordinates d)), 0 ≤ a x :=
    fun x hx => hlam.le.trans (hab x hx).1
  have haLam : ∀ x ∈ (centeredCube c r hr : Set (SpatialCoordinates d)), a x ≤ Lam :=
    fun x hx => (hab x hx).2
  -- Step 2: a Poincare witness for the killed variation space on this cube.
  have hgeom := lane2_isOpenBoundedConvexDomain_centeredCube c hr
  obtain ⟨hP, -⟩ := exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain
    (centeredCube c r hr) hgeom
  -- Step 3: the small-cube extension bound (always available; feeds both branches).
  obtain ⟨C0, hC0pos, hSmall⟩ :=
    aux_lem_skeleton_ext_extension_small d hd Jc Xc Sf beta ⟨hbeta, hbeta1⟩
  -- Step 4: closure of the open cube is the closed cube.
  have hCubeClosure : closure (centeredCube c r hr : Set (SpatialCoordinates d)) =
      (closedCube c r hr : Set (SpatialCoordinates d)) :=
    closure_ball c (half_pos hr).ne'
  -- Step 5: the constant, uniform across the `r ≤ 1` / `r > 1` split.
  have hLampos := (Jc.Lam_pos c r hr aC c r ((beta - 1 / 2) / 4) 2).le
  have hrpow1 : 0 ≤ r ^ ((d : ℝ) - 2) := Real.rpow_nonneg hr.le _
  have hrpow2 : 0 ≤ r ^ (2 * beta) := Real.rpow_nonneg hr.le _
  have hKnonneg : 0 ≤ C0 * Jc.Lam c r hr aC c r ((beta - 1 / 2) / 4) 2 *
      r ^ ((d : ℝ) - 2) * r ^ (2 * beta) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC0pos.le hLampos) hrpow1) hrpow2
  have hrb : (r : ℝ) ^ (2 * beta) = r ^ beta * r ^ beta := by
    rw [two_mul, Real.rpow_add hr]
  refine ⟨C0 * Jc.Lam c r hr aC c r ((beta - 1 / 2) / 4) 2 * r ^ ((d : ℝ) - 2) * r ^ (2 * beta),
    hKnonneg, ?_⟩
  intro e hecont heholder
  have hbridge := aux_lem_skeleton_cellDirichletInfimum_le_dirichletResponse
    hP aC a haC Lam ha0 haLam hameas e
  have hexp : (r ^ beta *
      _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta
        (frontier (centeredCube c r hr : Set (SpatialCoordinates d))) e.toFun) ^ 2 =
      r ^ (2 * beta) *
        (_root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta
          (frontier (centeredCube c r hr : Set (SpatialCoordinates d))) e.toFun) ^ 2 := by
    rw [hrb]; ring
  rcases le_or_gt r 1 with hr1 | hr1
  · have hSmallBound := hSmall c r hr hr1 hP aC e.toFun
      (⟨sobolevDataOfH1 e, sobolevDataOfH1_mem_weak e⟩ : weakSobolevGraph (centeredCube c r hr))
      (hCubeClosure ▸ hecont) heholder (sobolevDataOfH1_fst_coeFn e)
    calc cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) e
        ≤ C0 * Jc.Lam c r hr aC c r ((beta - 1 / 2) / 4) 2 * r ^ ((d : ℝ) - 2) *
            (r ^ beta * _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta
              (frontier (centeredCube c r hr : Set (SpatialCoordinates d))) e.toFun) ^ 2 :=
          hbridge.trans hSmallBound
      _ = C0 * Jc.Lam c r hr aC c r ((beta - 1 / 2) / 4) 2 * r ^ ((d : ℝ) - 2) * r ^ (2 * beta) *
            (_root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta
              (frontier (centeredCube c r hr : Set (SpatialCoordinates d))) e.toFun) ^ 2 := by
          rw [hexp]; ring
  · have hLargeBound := aux_lem_skeleton_ext_large_extension d hd Jc Xc Sf beta ⟨hbeta, hbeta1⟩
      C0 hC0pos hSmall c r hr hr1 hP aC e.toFun
      (⟨sobolevDataOfH1 e, sobolevDataOfH1_mem_weak e⟩ : weakSobolevGraph (centeredCube c r hr))
      (hCubeClosure ▸ hecont) heholder (sobolevDataOfH1_fst_coeFn e)
    calc cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) e
        ≤ C0 * Jc.Lam c r hr aC c r ((beta - 1 / 2) / 4) 2 * r ^ ((d : ℝ) - 2) *
            (r ^ beta * _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta
              (frontier (centeredCube c r hr : Set (SpatialCoordinates d))) e.toFun) ^ 2 :=
          hbridge.trans hLargeBound
      _ = C0 * Jc.Lam c r hr aC c r ((beta - 1 / 2) / 4) 2 * r ^ ((d : ℝ) - 2) * r ^ (2 * beta) *
            (_root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta
              (frontier (centeredCube c r hr : Set (SpatialCoordinates d))) e.toFun) ^ 2 := by
          rw [hexp]; ring

end



theorem aux_lem_skeleton_S1
    (hd : 2 ≤ d) (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (beta : ℝ) (hbeta1 : 1 / 2 < beta) (hbeta2 : beta < 1)
    (c : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hsub : (centeredCube c r hr : Set (SpatialCoordinates d)) ⊆ (Q : Set (SpatialCoordinates d)))
    (a : SpatialCoordinates d → ℝ) (lam Lam : ℝ) (hlam : 0 < lam)
    (ha : ContinuousOn a (closure (centeredCube c r hr : Set (SpatialCoordinates d))))
    (hab : ∀ x ∈ (centeredCube c r hr : Set (SpatialCoordinates d)), lam ≤ a x ∧ a x ≤ Lam)
    (b : SpatialCoordinates d → ℝ)
    (ext : H1Function (centeredCube c r hr : Set (SpatialCoordinates d)))
    (hextcont : ContinuousOn ext.toFun (closure (centeredCube c r hr : Set (SpatialCoordinates d))))
    (hextb : ∀ x ∈ frontier (centeredCube c r hr : Set (SpatialCoordinates d)), ext.toFun x = b x)
    (g : ℕ → H1Function (centeredCube c r hr : Set (SpatialCoordinates d)))
    (bseq : ℕ → SpatialCoordinates d → ℝ)
    (hgcont : ∀ k, ContinuousOn (g k).toFun (closure (centeredCube c r hr : Set (SpatialCoordinates d))))
    (hgb : ∀ k, ∀ x ∈ closure (centeredCube c r hr : Set (SpatialCoordinates d)), (g k).toFun x = bseq k x)
    (hHolderQ : ∀ k, _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta (closure (Q : Set (SpatialCoordinates d)))
      (fun x => bseq k x - b x))
    (hsemQ : Tendsto (fun k => _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (closure (Q : Set (SpatialCoordinates d)))
      (fun x => bseq k x - b x)) atTop (𝓝 0)) :
    Tendsto (fun k => cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) (g k))
      atTop (𝓝 (cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) ext)) := by
  have hWmeas : MeasurableSet (centeredCube c r hr : Set (SpatialCoordinates d)) := (centeredCube c r hr).isOpen.measurableSet
  have ha0 : ∀ x ∈ (centeredCube c r hr : Set (SpatialCoordinates d)), 0 ≤ a x := fun x hx => hlam.le.trans (hab x hx).1
  have haLam : ∀ x ∈ (centeredCube c r hr : Set (SpatialCoordinates d)), a x ≤ Lam := fun x hx => (hab x hx).2
  have hameas : AEStronglyMeasurable a (volume.restrict (centeredCube c r hr : Set (SpatialCoordinates d))) :=
    (ha.mono subset_closure).aestronglyMeasurable (centeredCube c r hr).isOpen.measurableSet
  have hfrontQ : frontier (centeredCube c r hr : Set (SpatialCoordinates d)) ⊆ closure (Q : Set (SpatialCoordinates d)) :=
    frontier_subset_closure.trans (closure_mono hsub)
  obtain ⟨K, hK0, hK⟩ := aux_lem_skeleton_cell_ext_bound hd Jc Xc Sf beta hbeta1 hbeta2 c r hr a lam Lam hlam ha hab
  have hHolderFr : ∀ k, _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta (frontier (centeredCube c r hr : Set (SpatialCoordinates d))) (fun x => bseq k x - b x) :=
    fun k => aux_lem_skeleton_isHolderOn_mono hfrontQ (hHolderQ k)
  have hsemFr : Tendsto (fun k => _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (frontier (centeredCube c r hr : Set (SpatialCoordinates d)))
      (fun x => bseq k x - b x)) atTop (𝓝 0) := by
    have hbound : ∀ k, _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (frontier (centeredCube c r hr : Set (SpatialCoordinates d))) (fun x => bseq k x - b x) ≤
        _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (closure (Q : Set (SpatialCoordinates d))) (fun x => bseq k x - b x) :=
      fun k => aux_lem_skeleton_holderSeminorm_mono hfrontQ (hHolderQ k)
    have hnn : ∀ k, 0 ≤ _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (frontier (centeredCube c r hr : Set (SpatialCoordinates d))) (fun x => bseq k x - b x) :=
      fun k => aux_lem_skeleton_holderSeminorm_nonneg beta (frontier (centeredCube c r hr : Set (SpatialCoordinates d))) (fun x => bseq k x - b x)
    exact squeeze_zero hnn hbound hsemQ
  have heq1 : ∀ k, ∀ x ∈ frontier (centeredCube c r hr : Set (SpatialCoordinates d)), (g k - ext).toFun x = bseq k x - b x := by
    intro k x hx
    have hsub : (g k - ext).toFun x = (g k).toFun x - ext.toFun x :=
      congrFun (H1Function.sub_toFun (g k) ext) x
    rw [hsub, hgb k x (frontier_subset_closure hx), hextb x hx]
  have heq2 : ∀ k, ∀ x ∈ frontier (centeredCube c r hr : Set (SpatialCoordinates d)), (ext - g k).toFun x = -(bseq k x - b x) := by
    intro k x hx
    have hsub : (ext - g k).toFun x = ext.toFun x - (g k).toFun x :=
      congrFun (H1Function.sub_toFun ext (g k)) x
    rw [hsub, hgb k x (frontier_subset_closure hx), hextb x hx]; ring
  have hHolder1 : ∀ k, _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta (frontier (centeredCube c r hr : Set (SpatialCoordinates d))) (g k - ext).toFun :=
    fun k => aux_lem_skeleton_isHolderOn_congr (fun x hx => (heq1 k x hx).symm) (hHolderFr k)
  have hHolder2 : ∀ k, _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta (frontier (centeredCube c r hr : Set (SpatialCoordinates d))) (ext - g k).toFun := fun k =>
    aux_lem_skeleton_isHolderOn_congr (fun x hx => (heq2 k x hx).symm)
      (aux_lem_skeleton_isHolderOn_neg (hHolderFr k))
  have hsem1 : ∀ k, _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (frontier (centeredCube c r hr : Set (SpatialCoordinates d))) (g k - ext).toFun =
      _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (frontier (centeredCube c r hr : Set (SpatialCoordinates d))) (fun x => bseq k x - b x) := by
    intro k
    unfold _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm
    congr 1
    unfold _root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet
    ext v
    constructor
    · rintro ⟨x, hx, y, hy, hxy, rfl⟩; exact ⟨x, hx, y, hy, hxy, by rw [heq1 k x hx, heq1 k y hy]⟩
    · rintro ⟨x, hx, y, hy, hxy, rfl⟩; exact ⟨x, hx, y, hy, hxy, by rw [heq1 k x hx, heq1 k y hy]⟩
  have hsem2 : ∀ k, _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (frontier (centeredCube c r hr : Set (SpatialCoordinates d))) (ext - g k).toFun =
      _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (frontier (centeredCube c r hr : Set (SpatialCoordinates d))) (fun x => bseq k x - b x) := by
    intro k
    have hstep : _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (frontier (centeredCube c r hr : Set (SpatialCoordinates d))) (ext - g k).toFun =
        _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (frontier (centeredCube c r hr : Set (SpatialCoordinates d))) (fun x => -(bseq k x - b x)) := by
      unfold _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm
      congr 1
      unfold _root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet
      ext v
      constructor
      · rintro ⟨x, hx, y, hy, hxy, rfl⟩; exact ⟨x, hx, y, hy, hxy, by rw [heq2 k x hx, heq2 k y hy]⟩
      · rintro ⟨x, hx, y, hy, hxy, rfl⟩; exact ⟨x, hx, y, hy, hxy, by rw [heq2 k x hx, heq2 k y hy]⟩
    rw [hstep]
    have hneg : _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (frontier (centeredCube c r hr : Set (SpatialCoordinates d))) (fun x => -(bseq k x - b x)) =
        _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (frontier (centeredCube c r hr : Set (SpatialCoordinates d))) (fun x => bseq k x - b x) := by
      unfold _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm
      congr 1
      unfold _root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet
      ext v
      constructor
      · rintro ⟨x, hx, y, hy, hxy, rfl⟩
        exact ⟨x, hx, y, hy, hxy, by
          rw [show (-(bseq k x - b x)) - (-(bseq k y - b y)) = -((bseq k x - b x) - (bseq k y - b y)) by ring,
            abs_neg]⟩
      · rintro ⟨x, hx, y, hy, hxy, rfl⟩
        exact ⟨x, hx, y, hy, hxy, by
          rw [show (-(bseq k x - b x)) - (-(bseq k y - b y)) = -((bseq k x - b x) - (bseq k y - b y)) by ring,
            abs_neg]⟩
    exact hneg
  have hInf1 : ∀ k, cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) (g k - ext) ≤
      K * (_root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (frontier (centeredCube c r hr : Set (SpatialCoordinates d))) (fun x => bseq k x - b x)) ^ 2 := by
    intro k
    have hcont : ContinuousOn (g k - ext).toFun (closure (centeredCube c r hr : Set (SpatialCoordinates d))) := by
      rw [H1Function.sub_toFun]; exact (hgcont k).sub hextcont
    have := hK (g k - ext) hcont (hHolder1 k)
    rwa [hsem1 k] at this
  have hInf2 : ∀ k, cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) (ext - g k) ≤
      K * (_root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (frontier (centeredCube c r hr : Set (SpatialCoordinates d))) (fun x => bseq k x - b x)) ^ 2 := by
    intro k
    have hcont : ContinuousOn (ext - g k).toFun (closure (centeredCube c r hr : Set (SpatialCoordinates d))) := by
      rw [H1Function.sub_toFun]; exact hextcont.sub (hgcont k)
    have := hK (ext - g k) hcont (hHolder2 k)
    rwa [hsem2 k] at this
  have hInfTendsto : Tendsto (fun k => K * (_root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (frontier (centeredCube c r hr : Set (SpatialCoordinates d)))
      (fun x => bseq k x - b x)) ^ 2) atTop (𝓝 0) := by
    have : Tendsto (fun k => (_root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (frontier (centeredCube c r hr : Set (SpatialCoordinates d)))
        (fun x => bseq k x - b x)) ^ 2) atTop (𝓝 0) := by
      have := hsemFr.pow 2
      simpa using this
    simpa using this.const_mul K
  have hInf1' : Tendsto (fun k => cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) (g k - ext)) atTop (𝓝 0) := by
    have hnn : ∀ k, 0 ≤ cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) (g k - ext) :=
      fun k => aux_prop_gluing_infimum_nonneg (centeredCube c r hr : Set (SpatialCoordinates d)) hWmeas a ha0 (g k - ext)
    exact squeeze_zero hnn hInf1 hInfTendsto
  have hInf2' : Tendsto (fun k => cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) (ext - g k)) atTop (𝓝 0) := by
    have hnn : ∀ k, 0 ≤ cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) (ext - g k) :=
      fun k => aux_prop_gluing_infimum_nonneg (centeredCube c r hr : Set (SpatialCoordinates d)) hWmeas a ha0 (ext - g k)
    exact squeeze_zero hnn hInf2 hInfTendsto
  have htri1 : ∀ k, Real.sqrt (cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) (g k)) ≤
      Real.sqrt (cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) ext) + Real.sqrt (cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) (g k - ext)) :=
    fun k => aux_prop_gluing_sqrt_infimum_sub_le (centeredCube c r hr : Set (SpatialCoordinates d)) hWmeas a Lam ha0 haLam hameas (g k) ext
  have htri2 : ∀ k, Real.sqrt (cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) ext) ≤
      Real.sqrt (cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) (g k)) + Real.sqrt (cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) (ext - g k)) :=
    fun k => aux_prop_gluing_sqrt_infimum_sub_le (centeredCube c r hr : Set (SpatialCoordinates d)) hWmeas a Lam ha0 haLam hameas ext (g k)
  have hsqrt1 : Tendsto (fun k => Real.sqrt (cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) (g k - ext))) atTop (𝓝 0) := by
    have := hInf1'.sqrt; simpa using this
  have hsqrt2 : Tendsto (fun k => Real.sqrt (cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) (ext - g k))) atTop (𝓝 0) := by
    have := hInf2'.sqrt; simpa using this
  have hsqrtTendsto : Tendsto (fun k => Real.sqrt (cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) (g k))) atTop
      (𝓝 (Real.sqrt (cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) ext))) := by
    have hbound : ∀ k, |Real.sqrt (cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) (g k)) -
        Real.sqrt (cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) ext)| ≤
        Real.sqrt (cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) (g k - ext)) +
          Real.sqrt (cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) (ext - g k)) := by
      intro k
      rw [abs_le]
      constructor
      · nlinarith [htri2 k, Real.sqrt_nonneg (cellDirichletInfimum a
          (centeredCube c r hr : Set (SpatialCoordinates d)) (g k - ext))]
      · nlinarith [htri1 k, Real.sqrt_nonneg (cellDirichletInfimum a
          (centeredCube c r hr : Set (SpatialCoordinates d)) (ext - g k))]
    have hcomb : Tendsto (fun k => Real.sqrt (cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) (g k - ext)) +
        Real.sqrt (cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) (ext - g k))) atTop (𝓝 0) := by
      have := hsqrt1.add hsqrt2; simpa using this
    have hnn : ∀ k, 0 ≤ |Real.sqrt (cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) (g k)) -
        Real.sqrt (cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) ext)| := fun k => abs_nonneg _
    have hzero : Tendsto (fun k => Real.sqrt (cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) (g k)) -
        Real.sqrt (cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) ext)) atTop (𝓝 0) := by
      have habs0 : Tendsto (fun k => |Real.sqrt (cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) (g k)) -
          Real.sqrt (cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) ext)|) atTop (𝓝 0) := squeeze_zero hnn hbound hcomb
      exact (tendsto_zero_iff_abs_tendsto_zero _).mpr habs0
    have := hzero.add (tendsto_const_nhds (x := Real.sqrt (cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) ext)))
    simpa using this
  have hnn1 : ∀ k, 0 ≤ cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) (g k) :=
    fun k => aux_prop_gluing_infimum_nonneg (centeredCube c r hr : Set (SpatialCoordinates d)) hWmeas a ha0 (g k)
  have hnnext : 0 ≤ cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) ext := aux_prop_gluing_infimum_nonneg (centeredCube c r hr : Set (SpatialCoordinates d)) hWmeas a ha0 ext
  have hcont_sq : Continuous (fun t : ℝ => t ^ 2) := continuous_pow 2
  have hsqrtsqrt : Tendsto (fun k => (Real.sqrt (cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) (g k))) ^ 2) atTop
      (𝓝 ((Real.sqrt (cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) ext)) ^ 2)) := (hcont_sq.tendsto _).comp hsqrtTendsto
  have hfin1 : ∀ k, (Real.sqrt (cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) (g k))) ^ 2 = cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) (g k) :=
    fun k => Real.sq_sqrt (hnn1 k)
  have hfin2 : (Real.sqrt (cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) ext)) ^ 2 = cellDirichletInfimum a (centeredCube c r hr : Set (SpatialCoordinates d)) ext :=
    Real.sq_sqrt hnnext
  simp_rw [hfin1] at hsqrtsqrt
  rwa [hfin2] at hsqrtsqrt



theorem aux_lem_skeleton_S3
    (hd : 2 ≤ d) (c : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : SpatialCoordinates d → ℝ) (lam Lam : ℝ) (hlam : 0 < lam)
    (ha : ContinuousOn a (closure (centeredCube c r hr : Set (SpatialCoordinates d))))
    (hab : ∀ x ∈ (centeredCube c r hr : Set (SpatialCoordinates d)), lam ≤ a x ∧ a x ≤ Lam)
    (u1 u2 e1 e2 : H1Function (centeredCube c r hr : Set (SpatialCoordinates d)))
    (hharm1 : IsWeaklyHarmonicOn a (centeredCube c r hr : Set (SpatialCoordinates d)) u1)
    (htr1 : HasZeroTraceDifferenceOn (centeredCube c r hr : Set (SpatialCoordinates d)) u1 e1)
    (hharm2 : IsWeaklyHarmonicOn a (centeredCube c r hr : Set (SpatialCoordinates d)) u2)
    (htr2 : HasZeroTraceDifferenceOn (centeredCube c r hr : Set (SpatialCoordinates d)) u2 e2)
    (hc1 : ContinuousOn u1.toFun (closure (centeredCube c r hr : Set (SpatialCoordinates d))))
    (hc2 : ContinuousOn u2.toFun (closure (centeredCube c r hr : Set (SpatialCoordinates d))))
    (hec1 : ContinuousOn e1.toFun (closure (centeredCube c r hr : Set (SpatialCoordinates d))))
    (hec2 : ContinuousOn e2.toFun (closure (centeredCube c r hr : Set (SpatialCoordinates d))))
    (M : ℝ) (hM : ∀ x ∈ frontier (centeredCube c r hr : Set (SpatialCoordinates d)),
      |e1.toFun x - e2.toFun x| ≤ M) :
    ∀ x ∈ closure (centeredCube c r hr : Set (SpatialCoordinates d)),
      |u1.toFun x - u2.toFun x| ≤ M := by
  have : NeZero d := ⟨by omega⟩
  have hdom : IsOpenBoundedConvexDomain (centeredCube c r hr : Set (SpatialCoordinates d)) := lane2_isOpenBoundedConvexDomain_centeredCube c hr
  have hopen : IsOpen (centeredCube c r hr : Set (SpatialCoordinates d)) := hdom.isOpen
  have ha0 : ∀ x ∈ (centeredCube c r hr : Set (SpatialCoordinates d)), 0 ≤ a x := fun x hx => hlam.le.trans (hab x hx).1
  have haLam : ∀ x ∈ (centeredCube c r hr : Set (SpatialCoordinates d)), a x ≤ Lam := fun x hx => (hab x hx).2
  have hameas : AEStronglyMeasurable a (volume.restrict (centeredCube c r hr : Set (SpatialCoordinates d))) := (ha.mono subset_closure).aestronglyMeasurable hopen.measurableSet
  have habd : ∀ᵐ x ∂(volume.restrict (centeredCube c r hr : Set (SpatialCoordinates d))), ‖a x‖ ≤ Lam := by
    filter_upwards [ae_restrict_mem hopen.measurableSet] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (ha0 x hx)]; exact haLam x hx
  have hbounds : ∀ᵐ y ∂(volume.restrict (centeredCube c r hr : Set (SpatialCoordinates d))), lam ≤ a y ∧ a y ≤ Lam := by
    filter_upwards [ae_restrict_mem hopen.measurableSet] with y hy; exact hab y hy
  have hharmDiff : IsWeaklyHarmonicOn a (centeredCube c r hr : Set (SpatialCoordinates d)) (u1 - u2) :=
    aux_lem_skeleton_harmonic_sub (a := a) (C := Lam) hameas habd hharm1 hharm2
  have htrDiff : HasZeroTraceDifferenceOn (centeredCube c r hr : Set (SpatialCoordinates d)) (u1 - u2) (e1 - e2) :=
    aux_lem_skeleton_trace_sub htr1 htr2
  have hecDiff : ContinuousOn (e1 - e2).toFun (closure (centeredCube c r hr : Set (SpatialCoordinates d))) := by
    rw [H1Function.sub_toFun]; exact hec1.sub hec2
  have hfrontier_upper : ∀ x ∈ frontier (centeredCube c r hr : Set (SpatialCoordinates d)), (e1 - e2).toFun x ≤ M := by
    intro x hx
    rw [show (e1 - e2).toFun x = e1.toFun x - e2.toFun x from congrFun (H1Function.sub_toFun e1 e2) x]
    exact (abs_le.mp (hM x hx)).2
  have hae_upper : ∀ᵐ x ∂(volume.restrict (centeredCube c r hr : Set (SpatialCoordinates d))), (u1 - u2).toFun x ≤ M :=
    aux_lem_skeleton_ae_le_of_frontier_le hdom hlam hameas hbounds hharmDiff htrDiff hecDiff hfrontier_upper
  have hcDiff : ContinuousOn (u1 - u2).toFun (closure (centeredCube c r hr : Set (SpatialCoordinates d))) := by
    rw [H1Function.sub_toFun]; exact hc1.sub hc2
  have hopen_upper : ∀ x ∈ (centeredCube c r hr : Set (SpatialCoordinates d)), (u1 - u2).toFun x ≤ M :=
    lane2_le_of_ae_le_of_continuousOn hopen (hcDiff.mono subset_closure) hae_upper
  have hclosure_upper : ∀ x ∈ closure (centeredCube c r hr : Set (SpatialCoordinates d)), (u1 - u2).toFun x ≤ M :=
    aux_lem_skeleton_le_closure_of_le_open hcDiff hopen_upper
  have hharmNeg1 : IsWeaklyHarmonicOn a (centeredCube c r hr : Set (SpatialCoordinates d)) (-u1) := aux_lem_skeleton_harmonic_neg hharm1
  have hharmNeg2 : IsWeaklyHarmonicOn a (centeredCube c r hr : Set (SpatialCoordinates d)) (-u2) := aux_lem_skeleton_harmonic_neg hharm2
  have htrNeg1 : HasZeroTraceDifferenceOn (centeredCube c r hr : Set (SpatialCoordinates d)) (-u1) (-e1) := aux_lem_skeleton_trace_neg htr1
  have htrNeg2 : HasZeroTraceDifferenceOn (centeredCube c r hr : Set (SpatialCoordinates d)) (-u2) (-e2) := aux_lem_skeleton_trace_neg htr2
  have hharmDiffNeg : IsWeaklyHarmonicOn a (centeredCube c r hr : Set (SpatialCoordinates d)) ((-u1) - (-u2)) :=
    aux_lem_skeleton_harmonic_sub (a := a) (C := Lam) hameas habd hharmNeg1 hharmNeg2
  have htrDiffNeg : HasZeroTraceDifferenceOn (centeredCube c r hr : Set (SpatialCoordinates d)) ((-u1) - (-u2)) ((-e1) - (-e2)) :=
    aux_lem_skeleton_trace_sub htrNeg1 htrNeg2
  have hecDiffNeg : ContinuousOn ((-e1) - (-e2)).toFun (closure (centeredCube c r hr : Set (SpatialCoordinates d))) := by
    rw [H1Function.sub_toFun]
    rw [show (-e1).toFun = fun x => -e1.toFun x from H1Function.neg_toFun e1,
        show (-e2).toFun = fun x => -e2.toFun x from H1Function.neg_toFun e2]
    exact hec1.neg.sub hec2.neg
  have hfrontier_upper' : ∀ x ∈ frontier (centeredCube c r hr : Set (SpatialCoordinates d)), ((-e1) - (-e2)).toFun x ≤ M := by
    intro x hx
    have heq : ((-e1) - (-e2)).toFun x = (-e1).toFun x - (-e2).toFun x :=
      congrFun (H1Function.sub_toFun (-e1) (-e2)) x
    rw [heq, show (-e1).toFun x = -e1.toFun x from congrFun (H1Function.neg_toFun e1) x,
      show (-e2).toFun x = -e2.toFun x from congrFun (H1Function.neg_toFun e2) x]
    have := (abs_le.mp (hM x hx)).1
    linarith
  have hae_upper' : ∀ᵐ x ∂(volume.restrict (centeredCube c r hr : Set (SpatialCoordinates d))), ((-u1) - (-u2)).toFun x ≤ M :=
    aux_lem_skeleton_ae_le_of_frontier_le hdom hlam hameas hbounds hharmDiffNeg htrDiffNeg hecDiffNeg
      hfrontier_upper'
  have hcDiffNeg : ContinuousOn ((-u1) - (-u2)).toFun (closure (centeredCube c r hr : Set (SpatialCoordinates d))) := by
    rw [H1Function.sub_toFun]
    rw [show (-u1).toFun = fun x => -u1.toFun x from H1Function.neg_toFun u1,
        show (-u2).toFun = fun x => -u2.toFun x from H1Function.neg_toFun u2]
    exact hc1.neg.sub hc2.neg
  have hopen_upper' : ∀ x ∈ (centeredCube c r hr : Set (SpatialCoordinates d)), ((-u1) - (-u2)).toFun x ≤ M :=
    lane2_le_of_ae_le_of_continuousOn hopen (hcDiffNeg.mono subset_closure) hae_upper'
  have hclosure_upper' : ∀ x ∈ closure (centeredCube c r hr : Set (SpatialCoordinates d)), ((-u1) - (-u2)).toFun x ≤ M :=
    aux_lem_skeleton_le_closure_of_le_open hcDiffNeg hopen_upper'
  intro x hx
  have h1 := hclosure_upper x hx
  have h2 := hclosure_upper' x hx
  have heq1 : (u1 - u2).toFun x = u1.toFun x - u2.toFun x := congrFun (H1Function.sub_toFun u1 u2) x
  have heq2 : ((-u1) - (-u2)).toFun x = (-u1).toFun x - (-u2).toFun x :=
    congrFun (H1Function.sub_toFun (-u1) (-u2)) x
  have heq3 : (-u1).toFun x = -u1.toFun x := congrFun (H1Function.neg_toFun u1) x
  have heq4 : (-u2).toFun x = -u2.toFun x := congrFun (H1Function.neg_toFun u2) x
  rw [heq1] at h1
  rw [heq2, heq3, heq4] at h2
  rw [abs_le]
  exact ⟨by linarith, h1⟩



theorem aux_lem_skeleton_S4
    (hd : 2 ≤ d) (c : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : SpatialCoordinates d → ℝ) (lam Lam : ℝ) (hlam : 0 < lam)
    (ha : ContinuousOn a (closure (centeredCube c r hr : Set (SpatialCoordinates d))))
    (hab : ∀ x ∈ (centeredCube c r hr : Set (SpatialCoordinates d)), lam ≤ a x ∧ a x ≤ Lam)
    (u1 e1 : H1Function (centeredCube c r hr : Set (SpatialCoordinates d)))
    (hharm1 : IsWeaklyHarmonicOn a (centeredCube c r hr : Set (SpatialCoordinates d)) u1)
    (htr1 : HasZeroTraceDifferenceOn (centeredCube c r hr : Set (SpatialCoordinates d)) u1 e1)
    (hc1 : ContinuousOn u1.toFun (closure (centeredCube c r hr : Set (SpatialCoordinates d))))
    (hec1 : ContinuousOn e1.toFun (closure (centeredCube c r hr : Set (SpatialCoordinates d))))
    (B : ℝ) (hB1 : ∀ x ∈ frontier (centeredCube c r hr : Set (SpatialCoordinates d)), |e1.toFun x| ≤ B) :
    ∀ x ∈ closure (centeredCube c r hr : Set (SpatialCoordinates d)), |u1.toFun x| ≤ B := by
  have : NeZero d := ⟨by omega⟩
  have hdom : IsOpenBoundedConvexDomain (centeredCube c r hr : Set (SpatialCoordinates d)) := lane2_isOpenBoundedConvexDomain_centeredCube c hr
  have hopen : IsOpen (centeredCube c r hr : Set (SpatialCoordinates d)) := hdom.isOpen
  have hameas : AEStronglyMeasurable a (volume.restrict (centeredCube c r hr : Set (SpatialCoordinates d))) := (ha.mono subset_closure).aestronglyMeasurable hopen.measurableSet
  have hbounds : ∀ᵐ y ∂(volume.restrict (centeredCube c r hr : Set (SpatialCoordinates d))), lam ≤ a y ∧ a y ≤ Lam := by
    filter_upwards [ae_restrict_mem hopen.measurableSet] with y hy; exact hab y hy
  have hfrontier_upper : ∀ x ∈ frontier (centeredCube c r hr : Set (SpatialCoordinates d)), e1.toFun x ≤ B := fun x hx => (abs_le.mp (hB1 x hx)).2
  have hae_upper : ∀ᵐ x ∂(volume.restrict (centeredCube c r hr : Set (SpatialCoordinates d))), u1.toFun x ≤ B :=
    aux_lem_skeleton_ae_le_of_frontier_le hdom hlam hameas hbounds hharm1 htr1 hec1 hfrontier_upper
  have hopen_upper : ∀ x ∈ (centeredCube c r hr : Set (SpatialCoordinates d)), u1.toFun x ≤ B :=
    lane2_le_of_ae_le_of_continuousOn hopen (hc1.mono subset_closure) hae_upper
  have hclosure_upper : ∀ x ∈ closure (centeredCube c r hr : Set (SpatialCoordinates d)), u1.toFun x ≤ B :=
    aux_lem_skeleton_le_closure_of_le_open hc1 hopen_upper
  have hharmNeg : IsWeaklyHarmonicOn a (centeredCube c r hr : Set (SpatialCoordinates d)) (-u1) := aux_lem_skeleton_harmonic_neg hharm1
  have htrNeg : HasZeroTraceDifferenceOn (centeredCube c r hr : Set (SpatialCoordinates d)) (-u1) (-e1) := aux_lem_skeleton_trace_neg htr1
  have hecNeg : ContinuousOn (-e1).toFun (closure (centeredCube c r hr : Set (SpatialCoordinates d))) := by
    rw [show (-e1).toFun = fun x => -e1.toFun x from H1Function.neg_toFun e1]; exact hec1.neg
  have hfrontier_upper' : ∀ x ∈ frontier (centeredCube c r hr : Set (SpatialCoordinates d)), (-e1).toFun x ≤ B := by
    intro x hx
    have heq : (-e1).toFun x = -e1.toFun x := congrFun (H1Function.neg_toFun e1) x
    rw [heq]; linarith [(abs_le.mp (hB1 x hx)).1]
  have hcNeg : ContinuousOn (-u1).toFun (closure (centeredCube c r hr : Set (SpatialCoordinates d))) := by
    rw [show (-u1).toFun = fun x => -u1.toFun x from H1Function.neg_toFun u1]; exact hc1.neg
  have hae_upper' : ∀ᵐ x ∂(volume.restrict (centeredCube c r hr : Set (SpatialCoordinates d))), (-u1).toFun x ≤ B :=
    aux_lem_skeleton_ae_le_of_frontier_le hdom hlam hameas hbounds hharmNeg htrNeg hecNeg hfrontier_upper'
  have hopen_upper' : ∀ x ∈ (centeredCube c r hr : Set (SpatialCoordinates d)), (-u1).toFun x ≤ B :=
    lane2_le_of_ae_le_of_continuousOn hopen (hcNeg.mono subset_closure) hae_upper'
  have hclosure_upper' : ∀ x ∈ closure (centeredCube c r hr : Set (SpatialCoordinates d)), (-u1).toFun x ≤ B :=
    aux_lem_skeleton_le_closure_of_le_open hcNeg hopen_upper'
  intro x hx
  have h1 := hclosure_upper x hx
  have h2 := hclosure_upper' x hx
  have heq2 : (-u1).toFun x = -u1.toFun x := congrFun (H1Function.neg_toFun u1) x
  rw [heq2] at h2
  rw [abs_le]
  exact ⟨by linarith, h1⟩



theorem aux_lem_skeleton_S5_S6
    (_hd : 2 ≤ d)
    (hQcube : ∃ (z : SpatialCoordinates d) (R : ℝ), 0 < R ∧
      (Q : Set (SpatialCoordinates d)) = Metric.ball z (R / 2))
    (S : ResponseSpace Q) (hS : S.space = killedSobolevGraph Q)
    (a : ℕ → SpatialCoordinates d → ℝ) (aC : ℕ → PositiveCoefficient Q)
    (haC : ∀ n : ℕ, ((aC n).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] a n)
    (ha : ∀ n : ℕ, ContinuousOn (a n) (closure (Q : Set (SpatialCoordinates d))))
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ (Q : Set (SpatialCoordinates d)), lam ≤ a n x ∧ a n x ≤ Lam)
    (m : ℕ) (cent : Fin m → SpatialCoordinates d) (rad : Fin m → ℝ) (hrad : ∀ i : Fin m, 0 < rad i)
    (hcover : (⋃ i : Fin m, (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)))
      =ᵐ[(volume : Measure (SpatialCoordinates d))] (Q : Set (SpatialCoordinates d)))
    (Wd : ℕ → H10Function (Q : Set (SpatialCoordinates d)))
    (u' : ℕ → ∀ i : Fin m, H1Function (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)))
    (u : ∀ i : Fin m, ℕ → H1Function (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)))
    (hD : ∀ (n : ℕ) (i : Fin m), ∀ᵐ x ∂(volume.restrict (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d))), (Wd n).toH1Function.toFun x = (u' n i).toFun x)
    (hclose : ∀ (n : ℕ) (i : Fin m), ∀ x ∈ closure (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)), |(u' n i).toFun x - (u i n).toFun x| ≤ 1 / (n + 1 : ℝ))
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ (i : Fin m) (n : ℕ), ∀ x ∈ closure (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)), |(u i n).toFun x| ≤ B)
    (v : DomainL2 Q) (vc : SpatialCoordinates d → ℝ)
    (hvrep : (v : SpatialCoordinates d → ℝ) =ᵐ[(volume.restrict (Q : Set (SpatialCoordinates d)))] vc)
    (hvcell : ∀ i : Fin m, ∀ x ∈ (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)),
      Tendsto (fun n : ℕ => (u i n).toFun x) atTop (𝓝 (vc x)))
    (g : ℕ → ∀ i : Fin m, H1Function (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)))
    (hE : ∀ n, energy (a n) (Q : Set (SpatialCoordinates d)) (Wd n).toH1Function =
      ∑ i : Fin m, cellDirichletInfimum (a n) (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)) (g n i))
    (Lam : Fin m → ℝ)
    (hLamSum : Tendsto (fun n => ∑ i : Fin m, cellDirichletInfimum (a n)
      (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) (g n i))
      atTop (𝓝 (∑ i : Fin m, Lam i))) :
    ∃ (uN : ℕ → S.space) (L : ℝ), L ≤ ∑ i : Fin m, Lam i ∧
      (∀ f : DomainL2 Q, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f v))) ∧
      Tendsto (fun n => (responseForm S (aC n) (uN n) (uN n) : ℝ)) atTop (𝓝 L) := by
  have : NeZero d := ⟨by omega⟩
  have hQmeas : MeasurableSet (Q : Set (SpatialCoordinates d)) := Q.isOpen.measurableSet
  obtain ⟨z0, R, hR, hQeq⟩ := hQcube
  have : IsFiniteMeasure (volume.restrict (Q : Set (SpatialCoordinates d))) := by
    have hQdom : IsOpenBoundedConvexDomain (Q : Set (SpatialCoordinates d)) := by
      rw [hQeq]; exact isOpenBoundedConvexDomain_ball z0 (half_pos hR)
    exact hQdom.isFiniteMeasure_restrict_volume
  have hcell_tendsto : ∀ (i : Fin m), ∀ x ∈ (centeredCube (cent i) (rad i) (hrad i) :
      Set (SpatialCoordinates d)), Tendsto (fun n => (u' n i).toFun x) atTop (𝓝 (vc x)) := by
    intro i x hx
    exact aux_lem_skeleton_tendsto_of_bounded_diff (fun n => (u' n i).toFun x) (fun n => (u i n).toFun x)
      (vc x) (hvcell i x hx) (fun n => hclose n i x (subset_closure hx))
  have hcell_ae : ∀ i : Fin m, ∀ᵐ x ∂(volume.restrict (centeredCube (cent i) (rad i) (hrad i) :
      Set (SpatialCoordinates d))), Tendsto (fun n => (Wd n).toH1Function.toFun x) atTop (𝓝 (vc x)) := by
    intro i
    have hDall : ∀ᵐ x ∂(volume.restrict (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d))), ∀ n, (Wd n).toH1Function.toFun x = (u' n i).toFun x :=
      ae_all_iff.mpr (fun n => hD n i)
    filter_upwards [hDall, ae_restrict_mem (centeredCube (cent i) (rad i) (hrad i)).isOpen.measurableSet]
      with x hx hxmem
    exact (tendsto_congr (fun n => (hx n).symm)).mp (hcell_tendsto i x hxmem)
  have hglobal_ae_tendsto : ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
      Tendsto (fun n => (Wd n).toH1Function.toFun x) atTop (𝓝 (vc x)) :=
    aux_lem_skeleton_ae_of_cellwise m (fun i => (centeredCube (cent i) (rad i) (hrad i) :
      Set (SpatialCoordinates d))) hcover _ hcell_ae
  have hcell_bound_ae : ∀ (i : Fin m) (n : ℕ), ∀ᵐ x ∂(volume.restrict (centeredCube (cent i) (rad i)
      (hrad i) : Set (SpatialCoordinates d))), |(Wd n).toH1Function.toFun x| ≤ B + 1 := by
    intro i n
    filter_upwards [hD n i, ae_restrict_mem (centeredCube (cent i) (rad i) (hrad i)).isOpen.measurableSet]
      with x hx hxmem
    rw [hx]
    have h1 : |(u' n i).toFun x - (u i n).toFun x| ≤ 1 / (n + 1 : ℝ) := hclose n i x (subset_closure hxmem)
    have h2 : |(u i n).toFun x| ≤ B := hB i n x (subset_closure hxmem)
    have h3 : (1 : ℝ) / (n + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    calc |(u' n i).toFun x| = |(u i n).toFun x + ((u' n i).toFun x - (u i n).toFun x)| := by ring_nf
      _ ≤ |(u i n).toFun x| + |(u' n i).toFun x - (u i n).toFun x| := abs_add_le _ _
      _ ≤ B + 1 := by linarith
  have hglobal_bound_ae : ∀ n : ℕ, ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
      |(Wd n).toH1Function.toFun x| ≤ B + 1 := fun n =>
    aux_lem_skeleton_ae_of_cellwise m (fun i => (centeredCube (cent i) (rad i) (hrad i) :
      Set (SpatialCoordinates d))) hcover _ (fun i => hcell_bound_ae i n)
  let uN : ℕ → S.space := fun n =>
    ⟨sobolevDataOfH1 (Wd n).toH1Function, by
      have hmem := sobolevDataOfH1_mem_killed (Wd n)
      rwa [← hS] at hmem⟩
  have hfmeas : ∀ n, AEStronglyMeasurable (Wd n).toH1Function.toFun
      (volume.restrict (Q : Set (SpatialCoordinates d))) :=
    fun n => (Wd n).toH1Function.memL2.aestronglyMeasurable
  have hvc_memLp : MemLp vc 2 (volume.restrict (Q : Set (SpatialCoordinates d))) :=
    (Lp.memLp v).ae_eq hvrep
  have hunif : UnifIntegrable (fun n => (Wd n).toH1Function.toFun) 2
      (volume.restrict (Q : Set (SpatialCoordinates d))) :=
    aux_lem_skeleton_unifIntegrable_of_bounded (by linarith : (0:ℝ) ≤ B + 1) hfmeas hglobal_bound_ae
  have htendLp : Tendsto (fun n => eLpNorm ((Wd n).toH1Function.toFun - vc) 2
      (volume.restrict (Q : Set (SpatialCoordinates d)))) atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num) hfmeas hvc_memLp hunif hglobal_ae_tendsto
  have htendLp2 : Tendsto (fun n => eLpNorm
      (((Wd n).toH1Function.memL2.toLp (Wd n).toH1Function.toFun : SpatialCoordinates d → ℝ) - vc) 2
      (volume.restrict (Q : Set (SpatialCoordinates d)))) atTop (𝓝 0) := by
    have heq : ∀ n, eLpNorm (((Wd n).toH1Function.memL2.toLp (Wd n).toH1Function.toFun :
        SpatialCoordinates d → ℝ) - vc) 2 (volume.restrict (Q : Set (SpatialCoordinates d))) =
        eLpNorm ((Wd n).toH1Function.toFun - vc) 2 (volume.restrict (Q : Set (SpatialCoordinates d))) := by
      intro n
      apply eLpNorm_congr_ae
      exact (MemLp.coeFn_toLp (Wd n).toH1Function.memL2).sub (Filter.EventuallyEq.rfl)
    simp_rw [heq]
    exact htendLp
  have hstrong0' : Tendsto (fun n => (Wd n).toH1Function.memL2.toLp (Wd n).toH1Function.toFun) atTop
      (𝓝 (hvc_memLp.toLp vc)) :=
    Lp.tendsto_Lp_of_tendsto_eLpNorm vc hvc_memLp htendLp2
  have heqfun : (fun n => (uN n).val.1) =
      (fun n => (Wd n).toH1Function.memL2.toLp (Wd n).toH1Function.toFun) := by
    funext n
    apply Lp.ext
    exact (sobolevDataOfH1_fst_coeFn (Wd n).toH1Function).trans
      (MemLp.coeFn_toLp (Wd n).toH1Function.memL2).symm
  have hstrong0 : Tendsto (fun n => (uN n).val.1) atTop (𝓝 (hvc_memLp.toLp vc)) := by
    rw [heqfun]; exact hstrong0'
  have hveq : hvc_memLp.toLp vc = v := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp hvc_memLp).trans hvrep.symm
  have hstrong : Tendsto (fun n => (uN n).val.1) atTop (𝓝 v) := hveq ▸ hstrong0
  have hweak : ∀ f : DomainL2 Q, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f v)) :=
    aux_lem_skeleton_weak_of_tendsto (fun n => (uN n).val.1) v hstrong
  have hresp : ∀ n, (responseForm S (aC n) (uN n) (uN n) : ℝ) =
      energy (a n) (Q : Set (SpatialCoordinates d)) (Wd n).toH1Function := by
    intro n
    obtain ⟨lam, Lamc, hlam, hab⟩ := hell n
    have ha0 : ∀ x ∈ (Q : Set (SpatialCoordinates d)), 0 ≤ a n x := fun x hx => hlam.le.trans (hab x hx).1
    have haLam : ∀ x ∈ (Q : Set (SpatialCoordinates d)), a n x ≤ Lamc := fun x hx => (hab x hx).2
    have hameas : AEStronglyMeasurable (a n) (volume.restrict (Q : Set (SpatialCoordinates d))) :=
      ((ha n).mono subset_closure).aestronglyMeasurable hQmeas
    exact aux_prop_gluing_responseForm_eq_energy S (aC n) (a n) (haC n) Lamc ha0 haLam hameas
      (uN n) (Wd n).toH1Function rfl
  have hLtendsto : Tendsto (fun n => (responseForm S (aC n) (uN n) (uN n) : ℝ)) atTop
      (𝓝 (∑ i : Fin m, Lam i)) := by
    have heq : (fun n => (responseForm S (aC n) (uN n) (uN n) : ℝ)) =
        fun n => ∑ i : Fin m, cellDirichletInfimum (a n)
          (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) (g n i) := by
      funext n; rw [hresp n, hE n]
    rw [heq]; exact hLamSum
  exact ⟨uN, ∑ i : Fin m, Lam i, le_refl _, hweak, hLtendsto⟩



theorem aux_lem_skeleton_gap_diagonal
    (hd : 2 ≤ d) (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (hQcube : ∃ (z : SpatialCoordinates d) (R : ℝ), 0 < R ∧
      (Q : Set (SpatialCoordinates d)) = Metric.ball z (R / 2))
    (a : ℕ → SpatialCoordinates d → ℝ)
    (ha : ∀ n : ℕ, ContinuousOn (a n) (closure (Q : Set (SpatialCoordinates d))))
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ (Q : Set (SpatialCoordinates d)), lam ≤ a n x ∧ a n x ≤ Lam)
    (alpha : ℝ) (halpha : 1 / 2 < alpha)
    (b : SpatialCoordinates d → ℝ) (hbcont : ContinuousOn b (closure (Q : Set (SpatialCoordinates d))))
    (hbh : ∀ theta : ℝ, 1 / 2 < theta → theta < min alpha 1 →
      _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn theta (closure (Q : Set (SpatialCoordinates d))) b)
    (hbvanish : ∀ x ∈ frontier (Q : Set (SpatialCoordinates d)), b x = 0)
    (m : ℕ) (cent : Fin m → SpatialCoordinates d) (rad : Fin m → ℝ)
    (hrad : ∀ i : Fin m, 0 < rad i)
    (hpart : ∀ i : Fin m,
      (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) ⊆
        (Q : Set (SpatialCoordinates d)))
    (hdisj : Pairwise fun i j : Fin m =>
      Disjoint (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d))
        (centeredCube (cent j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (hcover : (⋃ i : Fin m, (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)))
      =ᵐ[(volume : Measure (SpatialCoordinates d))]
        (Q : Set (SpatialCoordinates d)))
    (ext : ∀ i : Fin m, ℕ →
      H1Function (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)))
    (hextb : ∀ (i : Fin m) (n : ℕ),
      ContinuousOn (ext i n).toFun
          (closure (centeredCube (cent i) (rad i) (hrad i) :
            Set (SpatialCoordinates d))) ∧
        ∀ x ∈ frontier (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d)), (ext i n).toFun x = b x)
    (u : ∀ i : Fin m, ℕ →
      H1Function (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)))
    (huharm : ∀ (i : Fin m) (n : ℕ),
      IsWeaklyHarmonicOn (a n)
        (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))
        (u i n))
    (hutrace : ∀ (i : Fin m) (n : ℕ),
      HasZeroTraceDifferenceOn
        (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))
        (u i n) (ext i n))
    (hucont : ∀ (i : Fin m) (n : ℕ), ContinuousOn (u i n).toFun
      (closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))))
    (Lam : Fin m → ℝ)
    (hLam : ∀ i : Fin m,
      Tendsto (fun n => cellDirichletInfimum (a n)
        (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))
        (ext i n)) atTop (𝓝 (Lam i))) :
    ∃ (kf : ℕ → ℕ) (W : ℕ → ℕ → H10Function (Q : Set (SpatialCoordinates d)))
      (g u' : ℕ → ℕ → ∀ i : Fin m, H1Function (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d))) (Bsup : ℝ),
      (∀ (n : ℕ) (i : Fin m), ∀ᵐ x ∂(volume.restrict (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d))),
        (W (kf n) n).toH1Function.toFun x = (u' (kf n) n i).toFun x) ∧
      (∀ n, energy (a n) (Q : Set (SpatialCoordinates d)) (W (kf n) n).toH1Function =
        ∑ i : Fin m, cellDirichletInfimum (a n) (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d)) (g (kf n) n i)) ∧
      (∀ (n : ℕ) (i : Fin m), ∀ x ∈ closure (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d)), |(u' (kf n) n i).toFun x - (u i n).toFun x| ≤ 1 / (n + 1 : ℝ)) ∧
      0 ≤ Bsup ∧
      (∀ (i : Fin m) (n : ℕ), ∀ x ∈ closure (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d)), |(u i n).toFun x| ≤ Bsup) ∧
      Tendsto (fun n => ∑ i : Fin m, cellDirichletInfimum (a n)
        (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) (g (kf n) n i))
        atTop (𝓝 (∑ i : Fin m, Lam i)) := by
  have hbeta_lt : (1 : ℝ) / 2 < min alpha 1 := lt_min halpha (by norm_num)
  obtain ⟨beta, hbeta1, hbeta2⟩ := exists_between hbeta_lt
  have hbeta2' : beta < 1 := lt_of_lt_of_le hbeta2 (min_le_right alpha 1)
  obtain ⟨bseq, hbseqC, hbseqsupp, hbseqQ, hbseqconv⟩ :=
    lem_skeleton_smooth_approx hd hQcube alpha halpha b hbcont hbh hbvanish beta hbeta1 hbeta2
  obtain ⟨W, hW⟩ :=
    lem_skeleton_finite_cutoff_glue hd hQcube a ha hell m cent rad hrad hpart hdisj hcover
      bseq hbseqC hbseqsupp hbseqQ
  choose g u' hA hB hC hD hE using fun (k n : ℕ) => (hW k n).2
  obtain ⟨z0, R, hR, hQeq⟩ := hQcube
  have hz0 : z0 ∈ closure (Q : Set (SpatialCoordinates d)) := by
    rw [hQeq]; exact subset_closure (Metric.mem_ball_self (half_pos hR))
  have hQdiam : ∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
      ∀ y ∈ closure (Q : Set (SpatialCoordinates d)), dist x y ≤ R := by
    intro x hx y hy
    have hsub : closure (Metric.ball z0 (R / 2)) ⊆ Metric.closedBall z0 (R / 2) :=
      closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall
    rw [hQeq] at hx hy
    have hx' : dist x z0 ≤ R / 2 := Metric.mem_closedBall.mp (hsub hx)
    have hy' : dist y z0 ≤ R / 2 := Metric.mem_closedBall.mp (hsub hy)
    calc dist x y ≤ dist x z0 + dist z0 y := dist_triangle x z0 y
      _ = dist x z0 + dist y z0 := by rw [dist_comm z0 y]
      _ ≤ R / 2 + R / 2 := add_le_add hx' hy'
      _ = R := by ring
  have hQdiamE : ∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
      ∀ y ∈ closure (Q : Set (SpatialCoordinates d)),
      Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ (d : ℝ) * R := by
    intro x hx y hy
    have hEdim : Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ (d : ℝ) * dist x y := by
      simpa [Homogenization.euclideanNorm, Homogenization.vecNormSq,
        Homogenization.vecDot, dist_eq_norm, Pi.sub_apply, pow_two] using
        (Homogenization.euclideanNorm_le_dimension_mul_norm (x - y))
    exact hEdim.trans (mul_le_mul_of_nonneg_left (hQdiam x hx y hy) (by positivity))
  have hb_holder : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta (closure (Q : Set (SpatialCoordinates d))) b :=
    hbh beta hbeta1 hbeta2
  have hHolderQ : ∀ k, _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta (closure (Q : Set (SpatialCoordinates d)))
      (fun x => bseq k x - b x) := by
    intro k
    have hbseq_holder : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta (closure (Q : Set (SpatialCoordinates d))) (bseq k) :=
      aux_lem_skeleton_isHolderOn_of_contDiff_bounded (by linarith : (0:ℝ) < beta) hbeta2'.le
        (hbseqC k) (hbseqsupp k) hR.le hQdiam
    exact aux_lem_skeleton_isHolderOn_sub hbseq_holder hb_holder
  have hsemQ : Tendsto (fun k => _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (closure (Q : Set (SpatialCoordinates d)))
      (fun x => bseq k x - b x)) atTop (𝓝 0) := by
    have hnn : ∀ k, 0 ≤ _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (closure (Q : Set (SpatialCoordinates d)))
        (fun x => bseq k x - b x) := fun k => aux_lem_skeleton_holderSeminorm_nonneg _ _ _
    have hub : ∀ k, _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (closure (Q : Set (SpatialCoordinates d)))
        (fun x => bseq k x - b x) ≤
        _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta (closure (Q : Set (SpatialCoordinates d))) (fun x => bseq k x - b x) :=
      fun k => aux_lem_skeleton_cAlphaNorm_ge_holderSeminorm _ _ _
    exact squeeze_zero hnn hub hbseqconv
  have hE_bound : ∀ k, ∃ E : ℝ, 0 ≤ E ∧
      ∀ x ∈ closure (Q : Set (SpatialCoordinates d)), |bseq k x - b x| ≤ E := by
    intro k
    exact aux_lem_skeleton_bounded_of_holderOn_diam (by linarith : (0:ℝ) ≤ beta) (hHolderQ k)
      z0 hz0 ((d : ℝ) * R) (by positivity) hQdiamE
  have hSupPart_nonneg : ∀ k, 0 ≤ sSup {v : ℝ | ∃ x ∈ closure (Q : Set (SpatialCoordinates d)),
      v = |bseq k x - b x|} := by
    intro k; apply Real.sSup_nonneg; rintro v ⟨x, hx, rfl⟩; exact abs_nonneg _
  have hSupPart_le : ∀ k, ∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
      |bseq k x - b x| ≤ sSup {v : ℝ | ∃ x ∈ closure (Q : Set (SpatialCoordinates d)),
        v = |bseq k x - b x|} := by
    intro k x hx
    obtain ⟨E, hE0, hE⟩ := hE_bound k
    exact le_csSup ⟨E, by rintro v ⟨y, hy, rfl⟩; exact hE y hy⟩ ⟨x, hx, rfl⟩
  have hSupPart_le_cA : ∀ k, sSup {v : ℝ | ∃ x ∈ closure (Q : Set (SpatialCoordinates d)),
      v = |bseq k x - b x|} ≤
      _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta (closure (Q : Set (SpatialCoordinates d))) (fun x => bseq k x - b x) := by
    intro k
    have hnn : 0 ≤ _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (closure (Q : Set (SpatialCoordinates d)))
        (fun x => bseq k x - b x) := aux_lem_skeleton_holderSeminorm_nonneg _ _ _
    show sSup {v : ℝ | ∃ x ∈ closure (Q : Set (SpatialCoordinates d)), v = |bseq k x - b x|} ≤
        sSup {v : ℝ | ∃ x ∈ closure (Q : Set (SpatialCoordinates d)), v = |bseq k x - b x|} +
          _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (closure (Q : Set (SpatialCoordinates d))) (fun x => bseq k x - b x)
    linarith
  have hSupPart_tendsto : Tendsto (fun k => sSup {v : ℝ | ∃ x ∈ closure (Q : Set (SpatialCoordinates d)),
      v = |bseq k x - b x|}) atTop (𝓝 0) :=
    squeeze_zero hSupPart_nonneg hSupPart_le_cA hbseqconv
  have hS1 : ∀ (n : ℕ) (i : Fin m), Tendsto (fun k => cellDirichletInfimum (a n)
      (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) (g k n i)) atTop
      (𝓝 (cellDirichletInfimum (a n) (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)) (ext i n))) := by
    intro n i
    obtain ⟨lam, Lamc, hlam, hab⟩ := hell n
    exact aux_lem_skeleton_S1 hd Jc Xc Sf beta hbeta1 hbeta2' (cent i) (rad i) (hrad i) (hpart i)
      (a n) lam Lamc hlam ((ha n).mono (closure_mono (hpart i))) (fun x hx => hab x (hpart i hx))
      b (ext i n) (hextb i n).1 (hextb i n).2 (fun k => g k n i) bseq
      (fun k => (hA k n i).1) (fun k => (hA k n i).2) hHolderQ hsemQ
  have hSumTendsto : ∀ n, Tendsto (fun k => ∑ i : Fin m, cellDirichletInfimum (a n)
      (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) (g k n i)) atTop
      (𝓝 (∑ i : Fin m, cellDirichletInfimum (a n)
        (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) (ext i n))) := fun n =>
    aux_lem_skeleton_sum_tendsto m
      (fun i k => cellDirichletInfimum (a n) (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)) (g k n i))
      (fun i => cellDirichletInfimum (a n) (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)) (ext i n))
      (fun i => hS1 n i)
  obtain ⟨kf, hkf⟩ := aux_lem_skeleton_S2
    (fun n k => ∑ i : Fin m, cellDirichletInfimum (a n)
      (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) (g k n i))
    (fun n => ∑ i : Fin m, cellDirichletInfimum (a n)
      (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) (ext i n))
    hSumTendsto
    (fun k => sSup {v : ℝ | ∃ x ∈ closure (Q : Set (SpatialCoordinates d)), v = |bseq k x - b x|})
    hSupPart_tendsto
  have hLamSum : Tendsto (fun n => ∑ i : Fin m, cellDirichletInfimum (a n)
      (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) (g (kf n) n i)) atTop
      (𝓝 (∑ i : Fin m, Lam i)) :=
    aux_lem_skeleton_tendsto_of_bounded_diff
      (fun n => ∑ i : Fin m, cellDirichletInfimum (a n)
        (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) (g (kf n) n i))
      (fun n => ∑ i : Fin m, cellDirichletInfimum (a n)
        (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) (ext i n))
      (∑ i : Fin m, Lam i)
      (aux_lem_skeleton_sum_tendsto m
        (fun i n => cellDirichletInfimum (a n) (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d)) (ext i n)) Lam hLam)
      (fun n => (hkf n).1)
  have hBsup : ∃ Bsup : ℝ, 0 ≤ Bsup ∧ ∀ x ∈ closure (Q : Set (SpatialCoordinates d)), |b x| ≤ Bsup :=
    aux_lem_skeleton_bounded_of_holderOn_diam (by linarith : (0:ℝ) ≤ beta) hb_holder
      z0 hz0 ((d : ℝ) * R) (by positivity) hQdiamE
  obtain ⟨Bsup, hBsup0, hBsup⟩ := hBsup
  have hclose : ∀ (n : ℕ) (i : Fin m), ∀ x ∈ closure (centeredCube (cent i) (rad i) (hrad i) :
      Set (SpatialCoordinates d)), |(u' (kf n) n i).toFun x - (u i n).toFun x| ≤ 1 / (n + 1 : ℝ) := by
    intro n i
    obtain ⟨lam_n, Lam_n, hlam_n, hab_n⟩ := hell n
    have hM : ∀ x ∈ frontier (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)),
        |(g (kf n) n i).toFun x - (ext i n).toFun x| ≤ 1 / (n + 1 : ℝ) := by
      intro x hx
      have hxQ : x ∈ closure (Q : Set (SpatialCoordinates d)) :=
        (frontier_subset_closure.trans (closure_mono (hpart i))) hx
      have heq : (g (kf n) n i).toFun x - (ext i n).toFun x = bseq (kf n) x - b x := by
        rw [(hA (kf n) n i).2 x (frontier_subset_closure hx), (hextb i n).2 x hx]
      rw [heq]
      have h2' : sSup {v : ℝ | ∃ x ∈ closure (Q : Set (SpatialCoordinates d)), v = |bseq (kf n) x - b x|}
          ≤ 1 / (n + 1 : ℝ) := by
        rw [← abs_of_nonneg (hSupPart_nonneg (kf n))]
        exact (hkf n).2
      exact (hSupPart_le (kf n) x hxQ).trans h2'
    exact aux_lem_skeleton_S3 hd (cent i) (rad i) (hrad i) (a n) lam_n Lam_n hlam_n
      ((ha n).mono (closure_mono (hpart i))) (fun x hx => hab_n x (hpart i hx))
      (u' (kf n) n i) (u i n) (g (kf n) n i) (ext i n)
      (hB (kf n) n i).1 (hB (kf n) n i).2.1 (huharm i n) (hutrace i n)
      (hB (kf n) n i).2.2.1 (hucont i n) (hA (kf n) n i).1 (hextb i n).1
      (1 / (n + 1 : ℝ)) hM
  have hB4 : ∀ (i : Fin m) (n : ℕ), ∀ x ∈ closure (centeredCube (cent i) (rad i) (hrad i) :
      Set (SpatialCoordinates d)), |(u i n).toFun x| ≤ Bsup := by
    intro i n
    obtain ⟨lam_n, Lam_n, hlam_n, hab_n⟩ := hell n
    have hM : ∀ x ∈ frontier (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)),
        |(ext i n).toFun x| ≤ Bsup := by
      intro x hx
      rw [(hextb i n).2 x hx]
      exact hBsup x ((frontier_subset_closure.trans (closure_mono (hpart i))) hx)
    exact aux_lem_skeleton_S4 hd (cent i) (rad i) (hrad i) (a n) lam_n Lam_n hlam_n
      ((ha n).mono (closure_mono (hpart i))) (fun x hx => hab_n x (hpart i hx))
      (u i n) (ext i n) (huharm i n) (hutrace i n) (hucont i n) (hextb i n).1 Bsup hM
  exact ⟨kf, W, g, u', Bsup, (fun n i => hC (kf n) n i), (fun n => hE (kf n) n), hclose,
    hBsup0, hB4, hLamSum⟩



theorem aux_lem_skeleton_gap_weak_seq
    (hd : 2 ≤ d) (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (hQcube : ∃ (z : SpatialCoordinates d) (R : ℝ), 0 < R ∧
      (Q : Set (SpatialCoordinates d)) = Metric.ball z (R / 2))
    (a : ℕ → SpatialCoordinates d → ℝ)
    (aC : ℕ → PositiveCoefficient Q)
    (haC : ∀ n : ℕ, ((aC n).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] a n)
    (ha : ∀ n : ℕ, ContinuousOn (a n) (closure (Q : Set (SpatialCoordinates d))))
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ (Q : Set (SpatialCoordinates d)), lam ≤ a n x ∧ a n x ≤ Lam)
    (alpha : ℝ) (halpha : 1 / 2 < alpha)
    (b : SpatialCoordinates d → ℝ) (hbcont : ContinuousOn b (closure (Q : Set (SpatialCoordinates d))))
    (hbh : ∀ theta : ℝ, 1 / 2 < theta → theta < min alpha 1 →
      _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn theta (closure (Q : Set (SpatialCoordinates d))) b)
    (hbvanish : ∀ x ∈ frontier (Q : Set (SpatialCoordinates d)), b x = 0)
    (m : ℕ) (cent : Fin m → SpatialCoordinates d) (rad : Fin m → ℝ)
    (hrad : ∀ i : Fin m, 0 < rad i)
    (hpart : ∀ i : Fin m,
      (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) ⊆
        (Q : Set (SpatialCoordinates d)))
    (hdisj : Pairwise fun i j : Fin m =>
      Disjoint (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d))
        (centeredCube (cent j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (hcover : (⋃ i : Fin m, (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)))
      =ᵐ[(volume : Measure (SpatialCoordinates d))]
        (Q : Set (SpatialCoordinates d)))
    (ext : ∀ i : Fin m, ℕ →
      H1Function (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)))
    (hextb : ∀ (i : Fin m) (n : ℕ),
      ContinuousOn (ext i n).toFun
          (closure (centeredCube (cent i) (rad i) (hrad i) :
            Set (SpatialCoordinates d))) ∧
        ∀ x ∈ frontier (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d)), (ext i n).toFun x = b x)
    (u : ∀ i : Fin m, ℕ →
      H1Function (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)))
    (huharm : ∀ (i : Fin m) (n : ℕ),
      IsWeaklyHarmonicOn (a n)
        (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))
        (u i n))
    (hutrace : ∀ (i : Fin m) (n : ℕ),
      HasZeroTraceDifferenceOn
        (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))
        (u i n) (ext i n))
    (hucont : ∀ (i : Fin m) (n : ℕ), ContinuousOn (u i n).toFun
      (closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))))
    (_hubdry : ∀ (i : Fin m) (n : ℕ),
      ∀ x ∈ frontier (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)), (u i n).toFun x = b x)
    (Lam : Fin m → ℝ)
    (hLam : ∀ i : Fin m,
      Tendsto (fun n => cellDirichletInfimum (a n)
        (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))
        (ext i n)) atTop (𝓝 (Lam i)))
    (S : ResponseSpace Q) (hS : S.space = killedSobolevGraph Q)
    (v : DomainL2 Q)
    (vc : SpatialCoordinates d → ℝ)
    (hvrep : (v : SpatialCoordinates d → ℝ) =ᵐ[(volume.restrict (Q : Set (SpatialCoordinates d)))] vc)
    (hvcell : ∀ i : Fin m,
      ∀ x ∈ (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)),
        Tendsto (fun n : ℕ => (u i n).toFun x) atTop (𝓝 (vc x)))
    (_hvcCell : ∀ i : Fin m, ContinuousOn vc
      (closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))))
    (_hvcBdry : ∀ i : Fin m,
      ∀ x ∈ frontier (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)), vc x = b x) :
    ∃ (uN : ℕ → S.space) (L : ℝ), L ≤ ∑ i : Fin m, Lam i ∧
      (∀ f : DomainL2 Q, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop
        (𝓝 (inner ℝ f v))) ∧
      Tendsto (fun n => (responseForm S (aC n) (uN n) (uN n) : ℝ)) atTop (𝓝 L) := by
  obtain ⟨kf, W, g, u', Bsup, hDfact, hEfact, hclose, hBsup0, hB4, hLamSum⟩ :=
    aux_lem_skeleton_gap_diagonal hd Jc Xc Sf hQcube a ha hell alpha halpha b hbcont hbh hbvanish
      m cent rad hrad hpart hdisj hcover ext hextb u huharm hutrace hucont Lam hLam
  exact aux_lem_skeleton_S5_S6 hd hQcube S hS a aC haC ha hell m cent rad hrad hcover
    (fun n => W (kf n) n) (fun n i => u' (kf n) n i) u
    hDfact hclose Bsup hBsup0 hB4
    v vc hvrep hvcell (fun n i => g (kf n) n i) hEfact Lam hLamSum

/-- CONSUMER: once `aux_lem_skeleton_gap_weak_seq`
supplies the weakly convergent global sequence `uN → v` with energies bounded
by `Σ Lam i`, this chains the already-proved
`aux_lem_skeleton_domain_and_energy_bound_of_weak_tendsto` with monotonicity
of `≤` to give exactly `lem_skeleton`'s `h_domain`/`h_energy_bound` pair. -/
theorem aux_lem_skeleton_gap_from_weak_seq
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (S : ResponseSpace Q)
    (aC : ℕ → PositiveCoefficient Q)
    (hliminf : ∀ (uN : ℕ → S.space) (u : DomainL2 Q),
      (∀ f : DomainL2 Q, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop
        (𝓝 (inner ℝ f u))) →
      E.energy u ≤ liminf
        (fun n => ((responseForm S (aC n) (uN n) (uN n) : ℝ) : EReal)) atTop)
    (v : DomainL2 Q) (m : ℕ) (Lam : Fin m → ℝ)
    (uN : ℕ → S.space) (L : ℝ) (hL_le : L ≤ ∑ i : Fin m, Lam i)
    (hweak : ∀ f : DomainL2 Q, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop
      (𝓝 (inner ℝ f v)))
    (hLtendsto : Tendsto (fun n => (responseForm S (aC n) (uN n) (uN n) : ℝ))
      atTop (𝓝 L)) :
    v ∈ E.domain ∧ (E.energy v).toReal ≤ ∑ i : Fin m, Lam i := by
  obtain ⟨hv, hle⟩ :=
    aux_lem_skeleton_domain_and_energy_bound_of_weak_tendsto E S aC hliminf uN v hweak L hLtendsto
  exact ⟨hv, hle.trans hL_le⟩



theorem lem_skeleton
    (hd : 2 ≤ d) (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (hQcube : ∃ (z : SpatialCoordinates d) (R : ℝ), 0 < R ∧
      (Q : Set (SpatialCoordinates d)) = Metric.ball z (R / 2))
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (S : ResponseSpace Q) (hS : S.space = killedSobolevGraph Q)
    (a : ℕ → SpatialCoordinates d → ℝ)
    (aC : ℕ → PositiveCoefficient Q)
    (haC : ∀ n : ℕ, ((aC n).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] a n)
    (ha : ∀ n : ℕ, ContinuousOn (a n) (closure (Q : Set (SpatialCoordinates d))))
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ (Q : Set (SpatialCoordinates d)), lam ≤ a n x ∧ a n x ≤ Lam)
    (hliminf : ∀ (uN : ℕ → S.space) (u : DomainL2 Q),
      (∀ f : DomainL2 Q, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop
        (𝓝 (inner ℝ f u))) →
      E.energy u ≤ liminf
        (fun n => ((responseForm S (aC n) (uN n) (uN n) : ℝ) : EReal)) atTop)
    (_hrecovery : ∀ u ∈ E.domain, ∃ w : ℕ → S.space,
      Tendsto (fun n => ((w n).val.1,
        ((responseForm S (aC n) (w n) (w n) : ℝ) : EReal))) atTop
        (𝓝 (u, E.energy u)))
    (alpha : ℝ) (halpha : 1 / 2 < alpha)
    (b : SpatialCoordinates d → ℝ) (hbcont : ContinuousOn b (closure (Q : Set (SpatialCoordinates d))))
    (hbh : ∀ theta : ℝ, 1 / 2 < theta → theta < min alpha 1 →
      _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn theta (closure (Q : Set (SpatialCoordinates d))) b)
    (hbvanish : ∀ x ∈ frontier (Q : Set (SpatialCoordinates d)), b x = 0)
    (m : ℕ) (cent : Fin m → SpatialCoordinates d) (rad : Fin m → ℝ)
    (hrad : ∀ i : Fin m, 0 < rad i)
    (hpart : ∀ i : Fin m,
      (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) ⊆
        (Q : Set (SpatialCoordinates d)))
    (hdisj : Pairwise fun i j : Fin m =>
      Disjoint (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d))
        (centeredCube (cent j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (hcover : (⋃ i : Fin m, (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)))
      =ᵐ[(volume : Measure (SpatialCoordinates d))]
        (Q : Set (SpatialCoordinates d)))
    (ext : ∀ i : Fin m, ℕ →
      H1Function (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)))
    (hextb : ∀ (i : Fin m) (n : ℕ),
      ContinuousOn (ext i n).toFun
          (closure (centeredCube (cent i) (rad i) (hrad i) :
            Set (SpatialCoordinates d))) ∧
        ∀ x ∈ frontier (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d)), (ext i n).toFun x = b x)
    (u : ∀ i : Fin m, ℕ →
      H1Function (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)))
    (huharm : ∀ (i : Fin m) (n : ℕ),
      IsWeaklyHarmonicOn (a n)
        (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))
        (u i n))
    (hutrace : ∀ (i : Fin m) (n : ℕ),
      HasZeroTraceDifferenceOn
        (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))
        (u i n) (ext i n))
    (hucont : ∀ (i : Fin m) (n : ℕ), ContinuousOn (u i n).toFun
      (closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))))
    (hubdry : ∀ (i : Fin m) (n : ℕ),
      ∀ x ∈ frontier (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)), (u i n).toFun x = b x)
    (Lam : Fin m → ℝ)
    (hLam : ∀ i : Fin m,
      Tendsto (fun n => cellDirichletInfimum (a n)
        (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))
        (ext i n)) atTop (𝓝 (Lam i)))
    (v : DomainL2 Q)
    (vc : SpatialCoordinates d → ℝ)
    (hvrep : (v : SpatialCoordinates d → ℝ) =ᵐ[(volume.restrict (Q : Set (SpatialCoordinates d)))] vc)
    (hvcell : ∀ i : Fin m,
      ∀ x ∈ (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)),
        Tendsto (fun n : ℕ => (u i n).toFun x) atTop (𝓝 (vc x)))
    (hvcCell : ∀ i : Fin m, ContinuousOn vc
      (closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))))
    (hvcBdry : ∀ i : Fin m,
      ∀ x ∈ frontier (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)), vc x = b x) :
    v ∈ E.domain ∧
    ContinuousOn vc (closure (Q : Set (SpatialCoordinates d))) ∧
    (E.energy v).toReal ≤ ∑ i : Fin m, Lam i ∧
      (∀ i : Fin m, ∀ x ∈ (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)),
        |vc x - b x| ≤
          sSup {s : ℝ | ∃ y ∈ (centeredCube (cent i) (rad i) (hrad i) :
            Set (SpatialCoordinates d)),
            ∃ w ∈ (centeredCube (cent i) (rad i) (hrad i) :
              Set (SpatialCoordinates d)), s = |b y - b w|}) ∧
      ∀ x ∈ closure (Q : Set (SpatialCoordinates d)), |vc x - b x| ≤
        sSup (Set.range (fun i : Fin m =>
          sSup {s : ℝ | ∃ y ∈ (centeredCube (cent i) (rad i) (hrad i) :
            Set (SpatialCoordinates d)),
            ∃ w ∈ (centeredCube (cent i) (rad i) (hrad i) :
              Set (SpatialCoordinates d)), s = |b y - b w|})) := by
  have hdNeZero : NeZero d := ⟨by omega⟩
  -- Helper: a centered cube is an open bounded convex domain
  have h_cell_domain (i : Fin m) : IsOpenBoundedConvexDomain
      (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) := by
    have : (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) =
        Metric.ball (cent i) (rad i / 2) := rfl
    rw [this]
    exact isOpenBoundedConvexDomain_ball (cent i) (half_pos (hrad i))
  have h_cell_open (i : Fin m) : IsOpen (centeredCube (cent i) (rad i) (hrad i) :
      Set (SpatialCoordinates d)) := (h_cell_domain i).isOpen

  -- Maximum principle: the datum-continuity + boundary weak maximum principle
  
  have aux_lem_skeleton_max_principle (i : Fin m) (n : ℕ) (y : SpatialCoordinates d)
      (hy : y ∈ (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))) :
      |(u i n).toFun y - b y| ≤
        sSup {s : ℝ | ∃ y' ∈ (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d)),
          ∃ w' ∈ (centeredCube (cent i) (rad i) (hrad i) :
            Set (SpatialCoordinates d)), s = |b y' - b w'|} := by
    set M : ℝ := sSup {s : ℝ | ∃ y' ∈ (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)),
        ∃ w' ∈ (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d)), s = |b y' - b w'|} with hMdef
    have hdom := h_cell_domain i
    have hopen := h_cell_open i
    obtain ⟨lam', Lam', hlam'_pos, hameas, hbounds, _hpointwise⟩ :=
      aux_lem_skeleton_ell_package
        (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))
        hopen (hpart i) (a n) (ha n) (hell n)
    have hclQ : closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))
        ⊆ closure (Q : Set (SpatialCoordinates d)) := closure_mono (hpart i)
    have hKcompact : IsCompact (closure (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d))) :=
      Metric.isCompact_of_isClosed_isBounded isClosed_closure hdom.isBoundedDomain.isBounded.closure
    have hosc_bound : ∀ x ∈ frontier (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)), |b x - b y| ≤ M :=
      fun x hx => aux_lem_skeleton_closure_le_osc hKcompact (le_refl _)
        (hbcont.mono hclQ) hy (frontier_subset_closure hx)
    -- Upper bound: (u i n) ≤ b y + M a.e. on the cell, via the frontier max principle
    -- applied to the trace datum `ext i n` (whose frontier values equal `b`).
    have hfrontier_upper : ∀ x ∈ frontier (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)), (ext i n).toFun x ≤ b y + M := by
      intro x hx
      rw [(hextb i n).2 x hx]
      linarith [(abs_le.mp (hosc_bound x hx)).2]
    have hae_upper : ∀ᵐ x ∂(volume.restrict (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d))), (u i n).toFun x ≤ b y + M :=
      aux_lem_skeleton_ae_le_of_frontier_le hdom hlam'_pos hameas hbounds
        (huharm i n) (hutrace i n) (hextb i n).1 hfrontier_upper
    have hupper : ∀ x ∈ (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)),
        (u i n).toFun x ≤ b y + M :=
      lane2_le_of_ae_le_of_continuousOn hopen ((hucont i n).mono subset_closure) hae_upper
    -- Lower bound: negate both `u i n` and `ext i n` and repeat.
    have hgc_neg : ContinuousOn (-(ext i n)).toFun
        (closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))) := by
      have heq : (-(ext i n)).toFun = fun x => -(ext i n).toFun x := by
        funext x; simp
      rw [heq]
      exact ((hextb i n).1).neg
    have hfrontier_lower : ∀ x ∈ frontier (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)), (-(ext i n)).toFun x ≤ -(b y) + M := by
      intro x hx
      have heq : (-(ext i n)).toFun x = -(ext i n).toFun x := by
        simp
      rw [heq, (hextb i n).2 x hx]
      linarith [(abs_le.mp (hosc_bound x hx)).1]
    have hae_lower : ∀ᵐ x ∂(volume.restrict (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d))), (-(u i n)).toFun x ≤ -(b y) + M :=
      aux_lem_skeleton_ae_le_of_frontier_le hdom hlam'_pos hameas hbounds
        (aux_lem_skeleton_harmonic_neg (huharm i n)) (aux_lem_skeleton_trace_neg (hutrace i n))
        hgc_neg hfrontier_lower
    have hcont_neg : ContinuousOn (-(u i n)).toFun
        (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) := by
      have heq : (-(u i n)).toFun = fun x => -(u i n).toFun x := by
        funext x; simp
      rw [heq]
      exact ((hucont i n).mono subset_closure).neg
    have hlower : ∀ x ∈ (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)),
        (-(u i n)).toFun x ≤ -(b y) + M :=
      lane2_le_of_ae_le_of_continuousOn hopen hcont_neg hae_lower
    have hlower' : (u i n).toFun y ≥ b y - M := by
      have h1 := hlower y hy
      have h2 : (-(u i n)).toFun y = -(u i n).toFun y := by
        simp
      rw [h2] at h1
      linarith
    have hupper' : (u i n).toFun y ≤ b y + M := hupper y hy
    exact abs_le.mpr ⟨by linarith, by linarith⟩

  -- Oscillation bound for u i n on each cell
  have h_osc_bound : ∀ (i : Fin m) (n : ℕ) (x : SpatialCoordinates d),
      x ∈ (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) →
      |(u i n).toFun x - b x| ≤
        sSup {s : ℝ | ∃ y ∈ (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d)),
          ∃ w ∈ (centeredCube (cent i) (rad i) (hrad i) :
            Set (SpatialCoordinates d)), s = |b y - b w|} :=
    aux_lem_skeleton_max_principle

  -- Cellwise oscillation bound for vc
  have h_cell_osc : ∀ (i : Fin m) (x : SpatialCoordinates d),
      x ∈ (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) →
      |vc x - b x| ≤
        sSup {s : ℝ | ∃ y ∈ (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d)),
          ∃ w ∈ (centeredCube (cent i) (rad i) (hrad i) :
            Set (SpatialCoordinates d)), s = |b y - b w|} := by
    intro i x hx
    have h_tendsto : Tendsto (fun n : ℕ => (u i n).toFun x) atTop (𝓝 (vc x)) := hvcell i x hx
    have h_tendsto_abs : Tendsto (fun n : ℕ => |(u i n).toFun x - b x|) atTop
        (𝓝 |vc x - b x|) := by
      have h_cont_abs : Continuous (fun (t : ℝ) => |t - b x|) := by
        refine Continuous.abs ?_
        exact Continuous.sub continuous_id continuous_const
      exact h_cont_abs.tendsto _ |>.comp h_tendsto
    have h_bound_eventually : ∀ᶠ n in atTop,
        |(u i n).toFun x - b x| ≤
          sSup {s : ℝ | ∃ y ∈ (centeredCube (cent i) (rad i) (hrad i) :
            Set (SpatialCoordinates d)),
            ∃ w ∈ (centeredCube (cent i) (rad i) (hrad i) :
              Set (SpatialCoordinates d)), s = |b y - b w|} :=
      Filter.Eventually.of_forall (fun n => h_osc_bound i n x hx)
    exact le_of_tendsto h_tendsto_abs h_bound_eventually

  have h_cell_osc' : ∀ i : Fin m, ∀ x ∈ (centeredCube (cent i) (rad i) (hrad i) :
      Set (SpatialCoordinates d)),
      |vc x - b x| ≤
        sSup {s : ℝ | ∃ y ∈ (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d)),
          ∃ w ∈ (centeredCube (cent i) (rad i) (hrad i) :
            Set (SpatialCoordinates d)), s = |b y - b w|} :=
    fun i => h_cell_osc i

  -- Global oscillation bound
  have h_global_osc : ∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
      |vc x - b x| ≤
        sSup (Set.range (fun i : Fin m =>
          sSup {s : ℝ | ∃ y ∈ (centeredCube (cent i) (rad i) (hrad i) :
            Set (SpatialCoordinates d)),
            ∃ w ∈ (centeredCube (cent i) (rad i) (hrad i) :
              Set (SpatialCoordinates d)), s = |b y - b w|})) := by
    intro x hx
    have h_closure_cover : closure (Q : Set (SpatialCoordinates d)) ⊆
        ⋃ i : Fin m, closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) :=
      aux_lem_skeleton_finite_cutoff_glue_closure_cover
        (fun i => centeredCube (cent i) (rad i) (hrad i)) hcover
    have hrange_bddAbove : BddAbove (Set.range (fun i : Fin m =>
        sSup {s : ℝ | ∃ y ∈ (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d)),
          ∃ w ∈ (centeredCube (cent i) (rad i) (hrad i) :
            Set (SpatialCoordinates d)), s = |b y - b w|})) :=
      (Set.finite_range _).bddAbove
    obtain ⟨z0, R0, hR0, hQeq⟩ := hQcube
    have hQbounded : Bornology.IsBounded (Q : Set (SpatialCoordinates d)) := by
      rw [hQeq]; exact Metric.isBounded_ball
    have hKQcompact : IsCompact (closure (Q : Set (SpatialCoordinates d))) :=
      Metric.isCompact_of_isClosed_isBounded isClosed_closure hQbounded.closure
    have hx_mem_union : x ∈ ⋃ i : Fin m, closure (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)) := h_closure_cover hx
    rcases Set.mem_iUnion.mp hx_mem_union with ⟨i, hi⟩
    by_cases hx_cell : x ∈ (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))
    · have h_bound := h_cell_osc i x hx_cell
      exact le_trans h_bound (le_csSup hrange_bddAbove (Set.mem_range_self i))
    · have h_open : IsOpen (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) :=
        h_cell_open i
      have hx_frontier : x ∈ frontier (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) := by
        have h_interior_eq : interior (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) =
            (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) :=
          h_open.interior_eq
        have hx_not_interior : x ∉ interior (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) := by
          rw [h_interior_eq]
          exact hx_cell
        exact ⟨hi, hx_not_interior⟩
      have hvc_eq_b : vc x = b x := hvcBdry i x hx_frontier
      rw [hvc_eq_b, sub_self, abs_zero]
      have hosc_i_bddAbove : BddAbove {s : ℝ | ∃ y ∈ (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d)),
          ∃ w ∈ (centeredCube (cent i) (rad i) (hrad i) :
            Set (SpatialCoordinates d)), s = |b y - b w|} :=
        aux_lem_skeleton_osc_bddAbove hKQcompact
          ((hpart i).trans subset_closure) hbcont
      have h0_mem : (0 : ℝ) ∈ {s : ℝ | ∃ y ∈ (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d)),
          ∃ w ∈ (centeredCube (cent i) (rad i) (hrad i) :
            Set (SpatialCoordinates d)), s = |b y - b w|} := by
        rcases hi with hi'
        obtain ⟨p, hp⟩ : (centeredCube (cent i) (rad i) (hrad i) :
            Set (SpatialCoordinates d)).Nonempty := ⟨cent i, by
          have : (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) =
              Metric.ball (cent i) (rad i / 2) := rfl
          rw [this]; exact Metric.mem_ball_self (half_pos (hrad i))⟩
        exact ⟨p, hp, p, hp, by simp⟩
      have h0_le : (0 : ℝ) ≤ sSup {s : ℝ | ∃ y ∈ (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d)),
          ∃ w ∈ (centeredCube (cent i) (rad i) (hrad i) :
            Set (SpatialCoordinates d)), s = |b y - b w|} :=
        le_csSup hosc_i_bddAbove h0_mem
      exact le_trans h0_le (le_csSup hrange_bddAbove (Set.mem_range_self i))

  -- Continuity: cellwise closures cover closure Q; a finite union of closed
  -- pieces on which vc is continuous is continuous.
  have h_continuous : ContinuousOn vc (closure (Q : Set (SpatialCoordinates d))) := by
    have h_cells_cover_closure : closure (Q : Set (SpatialCoordinates d)) =
        ⋃ i : Fin m, closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) := by
      apply Set.Subset.antisymm
      · exact aux_lem_skeleton_finite_cutoff_glue_closure_cover
          (fun i => centeredCube (cent i) (rad i) (hrad i)) hcover
      · refine iUnion_subset (fun i => closure_mono (hpart i))
    rw [h_cells_cover_closure]
    let C (i : Fin m) : Set (SpatialCoordinates d) :=
      closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))
    have hC_closed (i : Fin m) : IsClosed (C i) := isClosed_closure
    have hC_cont (i : Fin m) : ContinuousOn vc (C i) := hvcCell i
    have h_gen : ∀ s : Finset (Fin m), ContinuousOn vc (⋃ j ∈ s, C j) := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · simp
      · intro j s' hjs' ih
        simp only [Finset.set_biUnion_insert]
        exact ContinuousOn.union_of_isClosed (hC_cont j) ih (hC_closed j)
          (isClosed_biUnion_finset (fun k _ => hC_closed k))
    have h_cont_union : ContinuousOn vc (⋃ i : Fin m, C i) := by
      have h := h_gen Finset.univ
      simpa using h
    exact h_cont_union

  -- Domain membership and the energy bound: assembled from the genuine gap
  -- `aux_lem_skeleton_gap_weak_seq` (the global approximating sequence,
  -- built via lem_skeleton_smooth_approx + lem_skeleton_finite_cutoff_glue +
  
  -- through the already-proved consumer `aux_lem_skeleton_domain_and_energy_bound_of_weak_tendsto`.
  obtain ⟨uN, L, hL_le, hweak, hLtendsto⟩ :=
    aux_lem_skeleton_gap_weak_seq hd Jc Xc Sf hQcube a aC haC ha hell alpha halpha b hbcont hbh hbvanish
      m cent rad hrad hpart hdisj hcover ext hextb u huharm hutrace hucont hubdry Lam hLam
      S hS v vc hvrep hvcell hvcCell hvcBdry
  obtain ⟨h_domain, h_energy_bound⟩ :=
    aux_lem_skeleton_gap_from_weak_seq E S aC hliminf v m Lam uN L hL_le hweak hLtendsto

  exact ⟨h_domain, h_continuous, h_energy_bound, h_cell_osc', h_global_osc⟩

end SubdiffusiveProcess.Paper
