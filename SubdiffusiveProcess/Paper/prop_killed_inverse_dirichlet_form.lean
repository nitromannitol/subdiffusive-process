module

public import SubdiffusiveProcess.Paper.killed_inverse_mosco
public import SubdiffusiveProcess.Paper.prop_killed_inverse_injectivity
public import SubdiffusiveProcess.Paper.prop_killed_inverse_spectral_square_root
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Variational.DualEnergy

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_prop_killed_inverse_dirichlet_form_root_injective
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (G R : H →L[ℝ] H) (hcomp : R.comp R = G)
    (hinj : Function.Injective G) : Function.Injective R := by
  intro x y hxy
  apply hinj
  rw [← hcomp]
  simpa only [ContinuousLinearMap.comp_apply] using congrArg R hxy

theorem aux_prop_killed_inverse_dirichlet_form_root_dense
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (R : H →L[ℝ] H)
    (hsym : ∀ x y : H, inner ℝ (R x) y = inner ℝ x (R y))
    (hinj : Function.Injective R) :
    Dense (LinearMap.range (R : H →ₗ[ℝ] H) : Set H) := by
  have hRsym : (R : H →ₗ[ℝ] H).IsSymmetric := hsym
  have hadj : ContinuousLinearMap.adjoint R = R := hRsym.clm_adjoint_eq
  have hker : LinearMap.ker (R : H →ₗ[ℝ] H) = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinj
  have horth := R.orthogonal_ker
  rw [hadj, hker, Submodule.bot_orthogonal_eq_top] at horth
  exact (Submodule.dense_iff_topologicalClosure_eq_top).2 horth.symm


theorem aux_prop_killed_inverse_dirichlet_form_dual_energy_root_range
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (G R : H →L[ℝ] H)
    (_hsym : ∀ x y : H, inner ℝ (G x) y = inner ℝ x (G y))
    (hRsym : ∀ x y : H, inner ℝ (R x) y = inner ℝ x (R y))
    (hcomp : R.comp R = G)
    (hRinj : Function.Injective R)
    (u : H) :
    (⨆ f : H, ((2 * inner ℝ f (R u) - inner ℝ f (G f) : ℝ) : EReal)) =
      ((inner ℝ u u : ℝ) : EReal) := by
  have hdense : Dense (LinearMap.range (R : H →ₗ[ℝ] H) : Set H) :=
    aux_prop_killed_inverse_dirichlet_form_root_dense R hRsym hRinj
  let F : H → ℝ := fun y => 2 * inner ℝ y u - inner ℝ y y
  have hcross (f : H) : inner ℝ f (R u) = inner ℝ (R f) u := by
    exact (hRsym f u).symm
  have hcross' (f : H) : inner ℝ u (R f) = inner ℝ (R f) u := by
    exact real_inner_comm _ _
  have hquad (f : H) : inner ℝ f (G f) = inner ℝ (R f) (R f) := by
    rw [← hcomp]
    rw [ContinuousLinearMap.comp_apply]
    exact (hRsym f (R f)).symm
  have hupper (f : H) :
      2 * inner ℝ f (R u) - inner ℝ f (G f) ≤ inner ℝ u u := by
    have hsquare : 0 ≤ inner ℝ (R f - u) (R f - u) := real_inner_self_nonneg
    rw [inner_sub_left, inner_sub_right, inner_sub_right] at hsquare
    rw [hcross f, hquad f]
    nlinarith [hcross' f]
  apply le_antisymm
  · refine iSup_le fun f => ?_
    rw [EReal.coe_le_coe_iff]
    exact hupper f
  · let E : EReal :=
      ⨆ f : H, ((2 * inner ℝ f (R u) - inner ℝ f (G f) : ℝ) : EReal)
    have hE_nonneg : (0 : EReal) ≤ E := by
      exact le_iSup_of_le (0 : H) (by simp)
    by_contra hnot
    have hElt : E < ((inner ℝ u u : ℝ) : EReal) := by
      exact lt_of_not_ge (by simpa [E] using hnot)
    have hEtop : E ≠ ⊤ := by
      intro htop
      rw [htop] at hElt
      exact (not_lt_of_ge le_top) hElt
    have hEbot : E ≠ ⊥ := by
      intro hbot
      rw [hbot] at hE_nonneg
      exact (not_le_of_gt EReal.bot_lt_zero) hE_nonneg
    let c : ℝ := E.toReal
    have hEeq : E = (c : EReal) :=
      (EReal.coe_toReal hEtop hEbot).symm
    have hbound : ∀ y ∈ (LinearMap.range (R : H →ₗ[ℝ] H) : Set H), F y ≤ c := by
      rintro y ⟨f, rfl⟩
      have hle := le_iSup (fun f : H =>
        ((2 * inner ℝ f (R u) - inner ℝ f (G f) : ℝ) : EReal)) f
      rw [show (⨆ f : H, ((2 * inner ℝ f (R u) - inner ℝ f (G f) : ℝ) : EReal)) = E by rfl,
        hEeq] at hle
      rw [EReal.coe_le_coe_iff] at hle
      dsimp [F]
      rw [hcross f, hquad f] at hle
      exact hle
    have hcont : Continuous F := by
      fun_prop
    have hclosed : IsClosed {y : H | F y ≤ c} := by
      exact isClosed_le hcont continuous_const
    have hu_closure : u ∈ closure (LinearMap.range (R : H →ₗ[ℝ] H) : Set H) := by
      rw [dense_iff_closure_eq.mp hdense]
      exact mem_univ u
    have hu_mem : u ∈ {y : H | F y ≤ c} := by
      apply hclosed.closure_subset
      exact closure_mono hbound hu_closure
    have hu_bound : inner ℝ u u ≤ c := by
      dsimp [F] at hu_mem
      linarith
    have hElt' : c < inner ℝ u u := by
      rw [hEeq] at hElt
      exact EReal.coe_lt_coe_iff.mp hElt
    exact (not_lt_of_ge hu_bound) hElt'



theorem prop_killed_inverse_dirichlet_form
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q)
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hsym : ∀ x y : DomainL2 Q,
      inner ℝ (G x) y = inner ℝ x (G y))
    (_hpos : ∀ x : DomainL2 Q, 0 ≤ inner ℝ x (G x))
    (hinj : Function.Injective G)
    (hroot : ∃ Rroot : DomainL2 Q →L[ℝ] DomainL2 Q,
      (∀ x y : DomainL2 Q,
        inner ℝ (Rroot x) y = inner ℝ x (Rroot y)) ∧
      (∀ x : DomainL2 Q, 0 ≤ inner ℝ x (Rroot x)) ∧
      Rroot.comp Rroot = G ∧ limitFormDomain G = Set.range Rroot)
    (hmosco :
      ((∀ (uN : ℕ → S.space) (u : DomainL2 Q),
          (∀ f : DomainL2 Q,
            Tendsto (fun n => inner ℝ f (uN n).val.1) atTop
              (𝓝 (inner ℝ f u))) →
          limitFormEnergy G u ≤
            liminf (fun n => ((responseForm S (a n) (uN n) (uN n) : ℝ) : EReal))
              atTop) ∧
        (∀ u ∈ limitFormDomain G, ∃ w : ℕ → S.space,
          Tendsto (fun n => ((w n).val.1,
            ((responseForm S (a n) (w n) (w n) : ℝ) : EReal))) atTop
            (𝓝 (u, limitFormEnergy G u)))))
    (hcontract :
      ∀ (n : ℕ) (T : ℝ → ℝ),
        _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T →
        ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
            (fun x => T (u.val.1 x))) ∧
          responseForm S (a n) v v ≤ responseForm S (a n) u u) :
    ∃ EForm : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (Q : Set (SpatialCoordinates d))),
      (∀ w : DomainL2 Q,
        EForm.toClosedForm.energy w = limitFormEnergy G w) ∧
      _root_.SubdiffusiveProcess.DirichletForm.HasNormalContractions EForm := by
  classical
  obtain ⟨R, hRsym, hRpos, hcomp, hdomain⟩ := hroot
  have hRinj : Function.Injective R :=
    aux_prop_killed_inverse_dirichlet_form_root_injective G R hcomp hinj
  let D : Submodule ℝ (DomainL2 Q) := LinearMap.range (R : DomainL2 Q →ₗ[ℝ] DomainL2 Q)
  have hDset : (D : Set (DomainL2 Q)) = Set.range R := by
    ext u
    constructor
    · intro hu
      exact (LinearMap.mem_range.mp hu)
    · rintro ⟨u, rfl⟩
      exact LinearMap.mem_range_self R.toLinearMap u
  have hD_mem_iff (u : DomainL2 Q) : u ∈ D ↔ u ∈ Set.range R := by
    change u ∈ (D : Set (DomainL2 Q)) ↔ u ∈ Set.range R
    rw [hDset]
  let e : DomainL2 Q ≃ₗ[ℝ] D :=
    LinearEquiv.ofInjective (R : DomainL2 Q →ₗ[ℝ] DomainL2 Q) hRinj
  let rootInv : DomainL2 Q → DomainL2 Q := fun u =>
    if hu : u ∈ D then e.symm ⟨u, hu⟩ else 0
  have hrootInv_apply (u : DomainL2 Q) : rootInv (R u) = u := by
    dsimp [rootInv]
    rw [dite_eq_left (show R u ∈ D by exact LinearMap.mem_range_self R.toLinearMap u)]
    have heq :
        (⟨R u, (show R u ∈ D by exact LinearMap.mem_range_self R.toLinearMap u)⟩ : D) = e u := by
      apply Subtype.ext
      exact (LinearEquiv.ofInjective_apply
        (R : DomainL2 Q →ₗ[ℝ] DomainL2 Q) u).symm
    rw [heq, e.symm_apply_apply]
  have hR_rootInv (u : DomainL2 Q) (hu : u ∈ D) : R (rootInv u) = u := by
    change (e (rootInv u) : DomainL2 Q) = u
    have he : (e (rootInv u) : DomainL2 Q) = u := by
      dsimp [rootInv]
      rw [dite_eq_left hu]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨u, hu⟩)
    exact he
  have hrootInv_add {u v : DomainL2 Q} (hu : u ∈ D) (hv : v ∈ D) :
      rootInv (u + v) = rootInv u + rootInv v := by
    apply hRinj
    calc
      R (rootInv (u + v)) = u + v := hR_rootInv (u + v) (D.add_mem hu hv)
      _ = R (rootInv u) + R (rootInv v) := by rw [hR_rootInv u hu, hR_rootInv v hv]
      _ = R (rootInv u + rootInv v) := by rw [R.map_add]
  have hrootInv_smul (c : ℝ) {u : DomainL2 Q} (hu : u ∈ D) :
      rootInv (c • u) = c • rootInv u := by
    apply hRinj
    calc
      R (rootInv (c • u)) = c • u := hR_rootInv (c • u) (D.smul_mem c hu)
      _ = c • R (rootInv u) := by rw [hR_rootInv u hu]
      _ = R (c • rootInv u) := by rw [R.map_smul]
  have henergy_root (u : DomainL2 Q) :
      (⨆ f : DomainL2 Q,
        ((2 * inner ℝ f (R u) - inner ℝ f (G f) : ℝ) : EReal)) =
        ((inner ℝ u u : ℝ) : EReal) :=
    aux_prop_killed_inverse_dirichlet_form_dual_energy_root_range G R hsym hRsym hcomp hRinj u
  have hrootInv_neg {u : DomainL2 Q} (hu : u ∈ D) :
      rootInv (-u) = -rootInv u := by
    simpa using hrootInv_smul (-1) hu
  have hrootInv_sub {u v : DomainL2 Q} (hu : u ∈ D) (hv : v ∈ D) :
      rootInv (u - v) = rootInv u - rootInv v := by
    rw [sub_eq_add_neg, hrootInv_add hu (D.neg_mem hv), hrootInv_neg hv]
    simp only [sub_eq_add_neg]
  let form : DomainL2 Q → DomainL2 Q → ℝ := fun u v =>
    inner ℝ (rootInv u) (rootInv v)
  have hform_symm : ∀ u ∈ D, ∀ v ∈ D, form u v = form v u := by
    intro u hu v hv
    exact real_inner_comm _ _
  have hform_add_left : ∀ u ∈ D, ∀ v ∈ D, ∀ w ∈ D,
      form (u + v) w = form u w + form v w := by
    intro u hu v hv w hw
    dsimp [form]
    rw [hrootInv_add hu hv, inner_add_left]
  have hform_smul_left : ∀ c : ℝ, ∀ u ∈ D, ∀ v ∈ D,
      form (c • u) v = c * form u v := by
    intro c u hu v hv
    dsimp [form]
    rw [hrootInv_smul c hu, real_inner_smul_left]
  have hform_nonneg : ∀ u ∈ D, 0 ≤ form u u := by
    intro u hu
    exact real_inner_self_nonneg
  have hDdense : Dense (D : Set (DomainL2 Q)) := by
    dsimp [D]
    exact aux_prop_killed_inverse_dirichlet_form_root_dense R hRsym hRinj
  have hform_eq_limit {u : DomainL2 Q} (hu : u ∈ D) :
      ((form u u : ℝ) : EReal) = limitFormEnergy G u := by
    have huR : u = R (rootInv u) := (hR_rootInv u hu).symm
    rw [huR]
    dsimp [form]
    rw [hrootInv_apply]
    simpa [limitFormEnergy] using (henergy_root (rootInv u)).symm
  let EClosed : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (Q : Set (SpatialCoordinates d))) :=
    { domain := D
      form := form
      denseDomain := hDdense
      form_symm := hform_symm
      form_add_left := hform_add_left
      form_smul_left := hform_smul_left
      form_nonneg := hform_nonneg
      complete := by
        intro u hu hc
        let f : ℕ → DomainL2 Q := fun n => rootInv (u n)
        have hfC : CauchySeq f := by
          rw [Metric.cauchySeq_iff]
          intro ε hε
          obtain ⟨N, hN⟩ := hc (ε ^ 2) (sq_pos_of_pos hε)
          refine ⟨N, fun p hp q hq => ?_⟩
          have hdiff : u p - u q ∈ D := D.sub_mem (hu p) (hu q)
          have hformdiff : form (u p - u q) (u p - u q) =
              ‖f p - f q‖ ^ 2 := by
            dsimp [form, f]
            rw [hrootInv_sub (hu p) (hu q), real_inner_self_eq_norm_sq]
          have hsmall := hN p hp q hq
          rw [hformdiff] at hsmall
          rw [dist_eq_norm]
          nlinarith [norm_nonneg (f p - f q)]
        obtain ⟨f_lim, hf_lim⟩ := cauchySeq_tendsto_of_complete hfC
        let z : DomainL2 Q := R f_lim
        have hz : z ∈ D := by
          dsimp [z, D]
          exact LinearMap.mem_range_self R.toLinearMap f_lim
        refine ⟨z, hz, ?_⟩
        have hfdiff : Tendsto (fun n => f n - f_lim) atTop (𝓝 0) := by
          simpa using hf_lim.sub
            (tendsto_const_nhds : Tendsto (fun _ : ℕ => f_lim) atTop (𝓝 f_lim))
        have hnorm_f : Tendsto (fun n => ‖f n - f_lim‖ ^ 2) atTop (𝓝 0) := by
          have h := (tendsto_norm.comp hfdiff).pow 2
          simpa using h
        have hnorm_R : Tendsto
            (fun n => ‖R (f n - f_lim)‖ ^ 2) atTop (𝓝 0) := by
          have hRzero : Tendsto (fun n => R (f n - f_lim)) atTop (𝓝 0) := by
            simpa only [Function.comp_apply, map_zero] using!
              R.continuous.continuousAt.tendsto.comp hfdiff
          have h := (tendsto_norm.comp hRzero).pow 2
          simpa using h
        have hsum : Tendsto
            (fun n => ‖f n - f_lim‖ ^ 2 + ‖R (f n - f_lim)‖ ^ 2)
            atTop (𝓝 0) := by simpa only [add_zero] using hnorm_f.add hnorm_R
        apply hsum.congr'
        filter_upwards [] with n
        have hdiff : u n - z = R (f n - f_lim) := by
          dsimp [f, z]
          calc
            u n - R f_lim = R (rootInv (u n)) - R f_lim := by
              exact congrArg (fun x => x - R f_lim) (hR_rootInv (u n) (hu n)).symm
            _ = R (rootInv (u n) - f_lim) := (R.map_sub _ _).symm
            _ = R (rootInv (u n) - f_lim) := rfl
        rw [hdiff]
        dsimp [form]
        rw [hrootInv_apply, real_inner_self_eq_norm_sq]
      }
  have henergy_off {u : DomainL2 Q} (hu : u ∉ D) :
      limitFormEnergy G u = (⊤ : EReal) := by
    have hu_not : u ∉ limitFormDomain G := by
      intro huG
      apply hu
      apply (hD_mem_iff u).2
      rw [← hdomain]
      exact huG
    have hnotlt : ¬ limitFormEnergy G u < (⊤ : EReal) := by
      simpa only [limitFormDomain, mem_ofPred_eq] using hu_not
    exact le_antisymm le_top (not_lt.mp hnotlt)
  have henergy_all (u : DomainL2 Q) :
      EClosed.energy u = limitFormEnergy G u := by
    by_cases hu : u ∈ D
    · rw [_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energy_of_mem EClosed hu, hform_eq_limit hu]
    · rw [_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energy_of_notMem EClosed hu, henergy_off hu]
  have hoperates : ∀ T : ℝ → ℝ, _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T →
      EClosed.OperatesOn T := by
    intro T hT u hu v hv
    let TLp : DomainL2 Q → DomainL2 Q :=
      hT.lipschitzWith.compLp hT.map_zero
    have hTLp_ae (x : DomainL2 Q) :
        (TLp x : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
          (fun y => T (x y)) := by
      exact hT.lipschitzWith.coeFn_compLp hT.map_zero x
    have hv_eq : v = TLp u := by
      apply Lp.ext
      exact hv.trans (hTLp_ae u).symm
    have hu_lim : u ∈ limitFormDomain G := by
      rw [hdomain]
      exact (hD_mem_iff u).1 hu
    obtain ⟨w, hw⟩ := hmosco.2 u hu_lim
    have hwstrong : Tendsto (fun n => (w n).val.1) atTop (𝓝 u) :=
      (continuous_fst.tendsto (u, limitFormEnergy G u)).comp hw
    have hTLp_cont : Continuous TLp :=
      hT.lipschitzWith.continuous_compLp hT.map_zero
    have hcomp : Tendsto (fun n => TLp ((w n).val.1)) atTop (𝓝 (TLp u)) :=
      hTLp_cont.continuousAt.tendsto.comp hwstrong
    choose v' hv'_ae hv'_le using fun n => hcontract n T hT (w n)
    have hv'_eq (n : ℕ) : (v' n).val.1 = TLp ((w n).val.1) := by
      apply Lp.ext
      exact (hv'_ae n).trans (hTLp_ae ((w n).val.1)).symm
    have hv'strong : Tendsto (fun n => (v' n).val.1) atTop (𝓝 (TLp u)) := by
      rw [show (fun n => (v' n).val.1) = (fun n => TLp ((w n).val.1)) by
        funext n; exact hv'_eq n]
      exact hcomp
    have hv'weak : ∀ f : DomainL2 Q,
        Tendsto (fun n => inner ℝ f (v' n).val.1) atTop
          (𝓝 (inner ℝ f (TLp u))) := by
      intro f
      exact tendsto_const_nhds.inner hv'strong
    have hlow := hmosco.1 (fun n => v' n) (TLp u) hv'weak
    have hwenergy : Tendsto
        (fun n => ((responseForm S (a n) (w n) (w n) : ℝ) : EReal)) atTop
          (𝓝 (limitFormEnergy G u)) :=
      (continuous_snd.tendsto (u, limitFormEnergy G u)).comp hw
    have hliminf_le :
        liminf (fun n => ((responseForm S (a n) (v' n) (v' n) : ℝ) : EReal)) atTop ≤
          liminf (fun n => ((responseForm S (a n) (w n) (w n) : ℝ) : EReal)) atTop := by
      refine Filter.liminf_le_liminf
        (h := ?_)
        (Filter.isBoundedUnder_of_eventually_ge (a := (0 : EReal)) <| by
          filter_upwards [] with n
          exact (EReal.coe_nonneg).mpr (responseForm_nonneg S (a n) (v' n)))
        hwenergy.isCoboundedUnder_ge
      filter_upwards [] with n
      exact_mod_cast hv'_le n
    have hfinite_le : limitFormEnergy G (TLp u) ≤ limitFormEnergy G u := by
      exact hlow.trans (hliminf_le.trans_eq hwenergy.liminf_eq)
    have hTLp_lim : TLp u ∈ limitFormDomain G := by
      rw [limitFormDomain]
      exact lt_of_le_of_lt hfinite_le hu_lim
    have hTLp_D : TLp u ∈ D := by
      apply (hD_mem_iff (TLp u)).2
      rw [← hdomain]
      exact hTLp_lim
    have hform_le : form (TLp u) (TLp u) ≤ form u u := by
      apply EReal.coe_le_coe_iff.mp
      rw [hform_eq_limit hTLp_D, hform_eq_limit hu]
      exact hfinite_le
    refine ⟨hv_eq ▸ hTLp_D, ?_⟩
    rw [hv_eq]
    exact hform_le
  let EForm : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (Q : Set (SpatialCoordinates d))) :=
    { toClosedForm := EClosed
      markov := by
        intro u hu v hv
        exact hoperates _root_.SubdiffusiveProcess.DirichletForm.unitTruncation
          _root_.SubdiffusiveProcess.DirichletForm.isIsNormalContraction_unitTruncation u hu v hv }
  refine ⟨EForm, ?_, ?_⟩
  · intro w
    exact henergy_all w
  · exact ⟨hoperates⟩

end SubdiffusiveProcess.Paper
