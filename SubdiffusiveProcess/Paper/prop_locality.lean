module

public import SubdiffusiveProcess.Paper.catalog_cutoff_existence
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.VariationalResponses.BoundaryPackaging
public import SubdiffusiveProcess.VariationalResponses.NativeBridge
public import SubdiffusiveProcess.VariationalResponses.ResponseMarkov
public import SubdiffusiveProcess.Main.MeasureTrace
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.Variational.DualEnergyQuadratic
public import SubdiffusiveProcess.Paper.prop_locality_recovery

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

lemma aux_prop_locality_eq_of_le_and_add_eq {a b M : EReal}
    (ha : a ≤ M) (hb : b ≤ M) (h : a + b = M + M) (hMtop : M ≠ ⊤) : a = M := by
  by_cases hMbot : M = ⊥
  · rw [hMbot] at ha ⊢
    exact le_bot_iff.mp ha
  · have ha_ne_top : a ≠ ⊤ := by
      intro ha'
      rw [ha'] at ha
      exact hMtop (top_le_iff.mp ha)
    have hb_ne_top : b ≠ ⊤ := by
      intro hb'
      rw [hb'] at hb
      exact hMtop (top_le_iff.mp hb)
    have ha_ne_bot : a ≠ ⊥ := by
      intro ha'
      rw [ha', EReal.bot_add] at h
      have hm : M = ⊥ := by
        cases M with
        | bot => rfl
        | top => exact (hMtop rfl).elim
        | coe m =>
          rw [← EReal.coe_add] at h
          exact (EReal.coe_ne_bot (m + m) h.symm).elim
      exact hMbot hm
    have hb_ne_bot : b ≠ ⊥ := by
      intro hb'
      rw [hb', EReal.add_bot] at h
      have hm : M = ⊥ := by
        cases M with
        | bot => rfl
        | top => exact (hMtop rfl).elim
        | coe m =>
          rw [← EReal.coe_add] at h
          exact (EReal.coe_ne_bot (m + m) h.symm).elim
      exact hMbot hm
    have hAc : (a.toReal : EReal) = a := EReal.coe_toReal ha_ne_top ha_ne_bot
    have hBc : (b.toReal : EReal) = b := EReal.coe_toReal hb_ne_top hb_ne_bot
    have hMc : (M.toReal : EReal) = M := EReal.coe_toReal hMtop hMbot
    have haR : a.toReal ≤ M.toReal := by
      have h1 : a ≤ (M.toReal : EReal) := by rw [hMc]; exact ha
      rw [← hAc] at h1
      exact EReal.coe_le_coe_iff.mp h1
    have hbR : b.toReal ≤ M.toReal := by
      have h1 : b ≤ (M.toReal : EReal) := by rw [hMc]; exact hb
      rw [← hBc] at h1
      exact EReal.coe_le_coe_iff.mp h1
    have hR : a.toReal + b.toReal = M.toReal + M.toReal := by
      have hh := h
      rw [← hAc, ← hBc, ← hMc] at hh
      rw [← EReal.coe_add, ← EReal.coe_add] at hh
      exact EReal.coe_eq_coe_iff.mp hh
    have heq : a.toReal = M.toReal := by linarith
    rw [← hAc, ← hMc, heq]

lemma aux_prop_locality_two_mul_EReal (x : EReal) : (2 : EReal) * x = x + x := by
  cases x with
  | bot => exact EReal.mul_bot_of_pos (by norm_num)
  | top => exact EReal.mul_top_of_pos (by norm_num)
  | coe x =>
    calc
      (2 : EReal) * (x : EReal) = (((2 : ℝ) * x : ℝ) : EReal) :=
        (EReal.coe_mul 2 x).symm
      _ = (((x + x : ℝ)) : EReal) := by congr 1 ; ring
      _ = (x : EReal) + (x : EReal) := EReal.coe_add x x

lemma aux_prop_locality_add_ne_top {a b : EReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    a + b ≠ ⊤ := by
  intro h
  cases a <;> cases b <;> simp_all

lemma aux_prop_locality_response_add
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hsym : ∀ x y, B x y = B y x) (u v : V) :
    B (u + v) (u + v) = B u u + B v v + 2 * B u v := by
  rw [B.map_add, add_apply, (B u).map_add, (B v).map_add,
    hsym v u]
  ring

lemma aux_prop_locality_response_sub
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hsym : ∀ x y, B x y = B y x) (u v : V) :
    B (u - v) (u - v) = B u u - 2 * B u v + B v v := by
  rw [B.map_sub, sub_apply, (B u).map_sub, (B v).map_sub,
    hsym v u]
  ring

lemma aux_prop_locality_response_add_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hsym : ∀ x y, B x y = B y x)
    {u v : V} (hcross : B u v = 0) :
    B (u + v) (u + v) = B u u + B v v := by
  calc
    B (u + v) (u + v) = B u u + B v v + 2 * B u v :=
      aux_prop_locality_response_add B hsym u v
    _ = B u u + B v v := by rw [hcross, mul_zero, add_zero]

lemma aux_prop_locality_response_sub_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hsym : ∀ x y, B x y = B y x)
    {u v : V} (hcross : B u v = 0) :
    B (u - v) (u - v) = B u u + B v v := by
  calc
    B (u - v) (u - v) = B u u - 2 * B u v + B v v :=
      aux_prop_locality_response_sub B hsym u v
    _ = B u u + B v v := by rw [hcross, mul_zero, sub_zero]

lemma aux_prop_locality_response_zero (d : ℕ) (Q : Opens (SpatialCoordinates d))
    (S : ResponseSpace Q) (a : PositiveCoefficient Q) :
    responseForm S a (0 : S.space) (0 : S.space) = 0 := by
  simp only [map_zero]

lemma aux_prop_locality_energy_parallelogram (d : ℕ) (Q : Opens (SpatialCoordinates d))
    (G : DomainL2 Q →L[ℝ] DomainL2 Q) (u v : DomainL2 Q)
    (hsymm : ∀ x y : DomainL2 Q, inner ℝ (G x) y = inner ℝ x (G y))
    (hpos : ∀ x : DomainL2 Q, 0 ≤ inner ℝ x (G x)) :
    limitFormEnergy G (u + v) + limitFormEnergy G (u - v) =
      (limitFormEnergy G u + limitFormEnergy G v) +
        (limitFormEnergy G u + limitFormEnergy G v) := by
  have hpara := quadraticDual_parallelogram G hsymm hpos u v
  simp only [limitFormEnergy] at hpara ⊢
  rw [hpara, aux_prop_locality_two_mul_EReal _, aux_prop_locality_two_mul_EReal _]
  abel

lemma aux_prop_locality_polarization (d : ℕ) (Q : Opens (SpatialCoordinates d))
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q)
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hGsymm : ∀ f g : DomainL2 Q,
      (inner ℝ f (G g) : ℝ) = (inner ℝ g (G f) : ℝ))
    (hLower : ∀ (wN : ℕ → S.space) (w : DomainL2 Q),
      (∀ f : DomainL2 Q, Tendsto (fun n => inner ℝ f (wN n).val.1) atTop
        (𝓝 (inner ℝ f w))) →
      limitFormEnergy G w ≤
        liminf (fun n => ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal)) atTop)
    (u v : DomainL2 Q)
    (hu : u ∈ limitFormDomain G) (hv : v ∈ limitFormDomain G)
    (uN vN : ℕ → S.space)
    (huN : Tendsto (fun n => ((uN n).val.1,
        ((responseForm S (a n) (uN n) (uN n) : ℝ) : EReal))) atTop
        (𝓝 (u, limitFormEnergy G u)))
    (hvN : Tendsto (fun n => ((vN n).val.1,
        ((responseForm S (a n) (vN n) (vN n) : ℝ) : EReal))) atTop
        (𝓝 (v, limitFormEnergy G v)))
    (hcross : ∀ n : ℕ, responseForm S (a n) (uN n) (vN n) = 0) :
    limitFormBilinear G u v = 0 := by
  have huN1 : Tendsto (fun n => (uN n).val.1) atTop (𝓝 u) :=
    (continuous_fst.tendsto (u, limitFormEnergy G u)).comp huN
  have hvN1 : Tendsto (fun n => (vN n).val.1) atTop (𝓝 v) :=
    (continuous_fst.tendsto (v, limitFormEnergy G v)).comp hvN
  have huNe : Tendsto
      (fun n => (((responseForm S (a n) (uN n) (uN n) : ℝ)) : EReal)) atTop
      (𝓝 (limitFormEnergy G u)) :=
    (continuous_snd.tendsto (u, limitFormEnergy G u)).comp huN
  have hvNe : Tendsto
      (fun n => (((responseForm S (a n) (vN n) (vN n) : ℝ)) : EReal)) atTop
      (𝓝 (limitFormEnergy G v)) :=
    (continuous_snd.tendsto (v, limitFormEnergy G v)).comp hvN
  have hwP1 : Tendsto (fun n => (uN n + vN n : S.space).val.1) atTop
      (𝓝 (u + v)) := huN1.add hvN1
  have hwM1 : Tendsto (fun n => (uN n - vN n : S.space).val.1) atTop
      (𝓝 (u - v)) := huN1.sub hvN1
  have hwP_weak : ∀ f : DomainL2 Q,
      Tendsto (fun n => inner ℝ f (uN n + vN n : S.space).val.1) atTop
        (𝓝 (inner ℝ f (u + v))) := by
    intro f
    exact ((continuous_const.inner continuous_id).tendsto (u + v)).comp hwP1
  have hwM_weak : ∀ f : DomainL2 Q,
      Tendsto (fun n => inner ℝ f (uN n - vN n : S.space).val.1) atTop
        (𝓝 (inner ℝ f (u - v))) := by
    intro f
    exact ((continuous_const.inner continuous_id).tendsto (u - v)).comp hwM1
  have hP_le : limitFormEnergy G (u + v) ≤
      liminf (fun n => ((responseForm S (a n) (uN n + vN n : S.space)
        (uN n + vN n : S.space) : ℝ) : EReal)) atTop :=
    hLower (fun n => uN n + vN n) (u + v) hwP_weak
  have hM_le : limitFormEnergy G (u - v) ≤
      liminf (fun n => ((responseForm S (a n) (uN n - vN n : S.space)
        (uN n - vN n : S.space) : ℝ) : EReal)) atTop :=
    hLower (fun n => uN n - vN n) (u - v) hwM_weak
  have hresponseP :
      (fun n => ((responseForm S (a n) (uN n + vN n : S.space)
        (uN n + vN n : S.space) : ℝ) : EReal)) =
      fun n => (((responseForm S (a n) (uN n) (uN n) : ℝ) : EReal)
        + ((responseForm S (a n) (vN n) (vN n) : ℝ) : EReal)) := by
    funext n
    have h1 : responseForm S (a n) (uN n + vN n) (uN n + vN n) =
        responseForm S (a n) (uN n) (uN n) + responseForm S (a n) (vN n) (vN n) := by
      exact aux_prop_locality_response_add_zero (responseForm S (a n))
        (fun x y => responseForm_symm S (a n) x y) (hcross n)
    simpa only [EReal.coe_add] using congrArg (fun x : ℝ => (x : EReal)) h1
  have hresponseM :
      (fun n => ((responseForm S (a n) (uN n - vN n : S.space)
        (uN n - vN n : S.space) : ℝ) : EReal)) =
      fun n => (((responseForm S (a n) (uN n) (uN n) : ℝ) : EReal)
        + ((responseForm S (a n) (vN n) (vN n) : ℝ) : EReal)) := by
    funext n
    have h1 : responseForm S (a n) (uN n - vN n) (uN n - vN n) =
        responseForm S (a n) (uN n) (uN n) + responseForm S (a n) (vN n) (vN n) := by
      exact aux_prop_locality_response_sub_zero (responseForm S (a n))
        (fun x y => responseForm_symm S (a n) x y) (hcross n)
    simpa only [EReal.coe_add] using congrArg (fun x : ℝ => (x : EReal)) h1
  have hlimP : liminf (fun n => (((responseForm S (a n) (uN n) (uN n) : ℝ) : EReal)
      + ((responseForm S (a n) (vN n) (vN n) : ℝ) : EReal))) atTop
      = limitFormEnergy G u + limitFormEnergy G v := by
    have hu_bot : limitFormEnergy G u ≠ (⊥ : EReal) := by
      intro h
      have hnonneg := limitFormEnergy_nonneg G u
      rw [h] at hnonneg
      simp at hnonneg
    have hsum : Tendsto
        (fun n => (((responseForm S (a n) (uN n) (uN n) : ℝ) : EReal)
          + ((responseForm S (a n) (vN n) (vN n) : ℝ) : EReal))) atTop
        (𝓝 (limitFormEnergy G u + limitFormEnergy G v)) := by
      have hcont := EReal.continuousAt_add
        (p := (limitFormEnergy G u, limitFormEnergy G v))
        (Or.inl (ne_of_lt hu)) (Or.inl hu_bot)
      have hp : Tendsto
          (fun n => (((responseForm S (a n) (uN n) (uN n) : ℝ) : EReal),
            ((responseForm S (a n) (vN n) (vN n) : ℝ) : EReal))) atTop
          (𝓝 (limitFormEnergy G u, limitFormEnergy G v)) := by
        rw [nhds_prod_eq]
        exact huNe.prodMk hvNe
      exact hcont.tendsto.comp hp
    exact hsum.liminf_eq
  have hP_le' : limitFormEnergy G (u + v) ≤ limitFormEnergy G u + limitFormEnergy G v := by
    rw [hresponseP, hlimP] at hP_le
    exact hP_le
  have hM_le' : limitFormEnergy G (u - v) ≤ limitFormEnergy G u + limitFormEnergy G v := by
    rw [hresponseM, hlimP] at hM_le
    exact hM_le
  have hE0 : limitFormEnergy G (0 : DomainL2 Q) = 0 := by
    refine le_antisymm ?_ (limitFormEnergy_nonneg G 0)
    have hh := hLower (fun _ : ℕ => (0 : S.space)) (0 : DomainL2 Q) (by
      intro f
      have hconst : (fun _ : ℕ => inner ℝ f ((0 : S.space)).val.1) =
          fun _ : ℕ => (0 : ℝ) := by
        funext n
        change inner ℝ f (0 : DomainL2 Q) = 0
        exact inner_zero_right f
      rw [hconst, inner_zero_right f]
      exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (0 : ℝ))))
    simp only [aux_prop_locality_response_zero, liminf_const] at hh
    exact hh
  have hpos : ∀ x : DomainL2 Q, 0 ≤ inner ℝ x (G x) := by
    intro x
    have hle : ((-(inner ℝ x (G x)) : ℝ) : EReal) ≤
        limitFormEnergy G (0 : DomainL2 Q) := by
      rw [limitFormEnergy]
      have h1 := le_iSup
        (fun f : DomainL2 Q => ((2 * inner ℝ f (0 : DomainL2 Q) -
          inner ℝ f (G f) : ℝ) : EReal)) x
      have hx : (2 * inner ℝ x (0 : DomainL2 Q) - inner ℝ x (G x) : ℝ) =
          -inner ℝ x (G x) := by
        have hz : inner ℝ x (0 : DomainL2 Q) = 0 := inner_zero_right x
        rw [hz]
        ring
      rw [hx] at h1
      exact h1
    rw [hE0] at hle
    have hr : (-(inner ℝ x (G x)) : ℝ) ≤ 0 := by
      exact EReal.coe_le_coe_iff.mp hle
    linarith
  have hsymm' : ∀ x y : DomainL2 Q, inner ℝ (G x) y = inner ℝ x (G y) := by
    intro x y
    rw [real_inner_comm, hGsymm]
  have hpara2 := aux_prop_locality_energy_parallelogram d Q G u v hsymm' hpos
  have hMtop : limitFormEnergy G u + limitFormEnergy G v ≠ ⊤ := by
    intro hcon
    have hu_top : limitFormEnergy G u ≠ ⊤ := ne_of_lt hu
    have hv_top : limitFormEnergy G v ≠ ⊤ := ne_of_lt hv
    exact aux_prop_locality_add_ne_top hu_top hv_top hcon
  have haM : limitFormEnergy G (u + v) = limitFormEnergy G u + limitFormEnergy G v :=
    aux_prop_locality_eq_of_le_and_add_eq hP_le' hM_le' hpara2 hMtop
  have hbM : limitFormEnergy G (u - v) = limitFormEnergy G u + limitFormEnergy G v :=
    aux_prop_locality_eq_of_le_and_add_eq hM_le' hP_le' (by rw [add_comm]; exact hpara2) hMtop
  have huv : limitFormEnergy G (u + v) = limitFormEnergy G (u - v) := haM.trans hbM.symm
  have hMbot : limitFormEnergy G u + limitFormEnergy G v ≠ (⊥ : EReal) := by
    intro h
    have hh : (0 : EReal) ≤ limitFormEnergy G u + limitFormEnergy G v :=
      add_nonneg (limitFormEnergy_nonneg G u) (limitFormEnergy_nonneg G v)
    rw [h] at hh
    simp at hh
  show (limitFormEnergy G (u + v) - limitFormEnergy G (u - v)) / (4 : EReal) = 0
  rw [huv, hbM, EReal.sub_self hMtop hMbot, EReal.zero_div]

/-- Strong locality on the core.
- The cube and killed Sobolev space are concrete.
- Symmetry and both Mosco clauses come from prop_killed_inverse.
- Fractional coercivity and bounded represented constants come from
  lem_coercivity and conv_represented_sequence.
- lem_19 records the deferred published CubeFractionalInterpolationInput.
- catalog_cutoff_existence supplies the common cutoff bounds.
- Core representatives have compact support inside the cube.
- prop_locality_recovery concludes the modified recovery sequences and exact
  zero cross energy; the principal conclusion is strong locality. The historical proof is retained in runtime;
the proof below supplies this corrected statement. -/
theorem prop_locality
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    let Q := centeredCube z r hr
    let H := DomainL2 Q
    ∀ (S : ResponseSpace Q) (_hS : S.space = killedSobolevGraph Q)
    (a : ℕ → PositiveCoefficient Q)
    (G : H →L[ℝ] H)
    (_hGsymm : ∀ f g : H, (inner ℝ f (G g) : ℝ) = (inner ℝ g (G f) : ℝ))
    (_hLower : ∀ (wN : ℕ → S.space) (w : H),
      (∀ f : H, Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) →
      limitFormEnergy G w ≤
        liminf (fun n => ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal)) atTop)
    (_hRecovery : ∀ w ∈ limitFormDomain G, ∃ wN : ℕ → S.space,
      Tendsto (fun n => ((wN n).val.1,
        ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal))) atTop
        (𝓝 (w, limitFormEnergy G w)))
    (KN : ℕ → ℝ) (_hKN : ∀ n, 0 ≤ KN n)
    (Kstar : ℝ) (_hKstar : ∀ n, KN n ≤ Kstar)
    (_hfrac : ∀ w : S.space,
      cubeFractionalL2Seminorm hd z r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => w.val.1) < ⊤)
    (_hcoercive : ∀ n (w : S.space),
      ‖w.val.1‖ ^ 2 + volume.real (Q : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd z r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
          (fun _ : Fin 1 => w.val.1)).toReal) ^ 2 ≤ KN n * responseForm S (a n) w w)
    (_hInterp : CubeFractionalInterpolationInput d hd)
    (t : ℝ) (_ht : (d : ℝ) - 1 < t) (_htd : t < (d : ℝ))
    (_hcutoffs : ∀ (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O → closure O ⊆ (Q : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → S.space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n) (closure (Q : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] chic n ∧
          (∀ x ∈ (Q : Set (SpatialCoordinates d)), 0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (Q : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
          responseForm S (a n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((a n).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)))
    (u v : H) (_hu : MemFormCore G u) (_hv : MemFormCore G v)
    (uc vc : SpatialCoordinates d → ℝ)
    (_huc : (u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] uc)
    (_hvc : (v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] vc)
    (_hucont : Continuous uc) (_hvcont : Continuous vc)
    (_hvsupp : HasCompactSupport vc)
    (_husuppQ : tsupport uc ⊆ (Q : Set (SpatialCoordinates d)))
    (_hvsuppQ : tsupport vc ⊆ (Q : Set (SpatialCoordinates d)))
    (_husupp : HasCompactSupport uc)
    (c : ℝ) (W : Set (SpatialCoordinates d)) (_hW : IsOpen W)
    (_hsupp : tsupport vc ⊆ W) (_hconst : ∀ x ∈ W, uc x = c),
    limitFormBilinear G u v = 0 := by
  intro Q H S hS a G hGsymm hLower hRecovery KN hKN Kstar hKstar hfrac hcoercive hInterp
    t ht htd hcutoffs u v hu hv uc vc huc hvc hucont hvcont hvsupp husuppQ hvsuppQ husupp
    c W hW hsupp hconst
  obtain ⟨uN, vN, huN, hvN, hcross⟩ :=
    prop_locality_recovery d hd z r hr S hS a G hLower hRecovery KN hKN Kstar hKstar hfrac
      hcoercive hInterp t ht htd hcutoffs u v hu hv uc vc huc hvc hucont hvcont hvsupp
      husuppQ hvsuppQ husupp c W hW hsupp hconst
  exact aux_prop_locality_polarization d Q S a G hGsymm hLower u v hu.1 hv.1
    uN vN huN hvN hcross

end SubdiffusiveProcess.Paper
/- lemma aux_prop_locality_polarization (d : ℕ) (Q : Opens (SpatialCoordinates d))
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q)
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hGsymm : ∀ f g : DomainL2 Q,
      (inner ℝ f (G g) : ℝ) = (inner ℝ g (G f) : ℝ))
    (hLower : ∀ (wN : ℕ → S.space) (w : DomainL2 Q),
      (∀ f : DomainL2 Q, Tendsto (fun n => inner ℝ f (wN n).val.1) atTop
        (𝓝 (inner ℝ f w))) →
      limitFormEnergy G w ≤
        liminf (fun n => ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal)) atTop)
    (u v : DomainL2 Q)
    (hu : u ∈ limitFormDomain G) (hv : v ∈ limitFormDomain G)
    (uN vN : ℕ → S.space)
    (huN : Tendsto (fun n => ((uN n).val.1,
        ((responseForm S (a n) (uN n) (uN n) : ℝ) : EReal))) atTop
        (𝓝 (u, limitFormEnergy G u)))
    (hvN : Tendsto (fun n => ((vN n).val.1,
        ((responseForm S (a n) (vN n) (vN n) : ℝ) : EReal))) atTop
        (𝓝 (v, limitFormEnergy G v)))
    (hcross : ∀ n : ℕ, responseForm S (a n) (uN n) (vN n) = 0) :
    limitFormBilinear G u v = 0 := by
  have huN1 : Tendsto (fun n => (uN n).val.1) atTop (𝓝 u) :=
    (continuous_fst.tendsto (u, limitFormEnergy G u)).comp huN
  have hvN1 : Tendsto (fun n => (vN n).val.1) atTop (𝓝 v) :=
    (continuous_fst.tendsto (v, limitFormEnergy G v)).comp hvN
  have huNe : Tendsto
      (fun n => (((responseForm S (a n) (uN n) (uN n) : ℝ)) : EReal)) atTop
      (𝓝 (limitFormEnergy G u)) :=
    (continuous_snd.tendsto (u, limitFormEnergy G u)).comp huN
  have hvNe : Tendsto
      (fun n => (((responseForm S (a n) (vN n) (vN n) : ℝ)) : EReal)) atTop
      (𝓝 (limitFormEnergy G v)) :=
    (continuous_snd.tendsto (v, limitFormEnergy G v)).comp hvN
  have hwP1 : Tendsto (fun n => (uN n + vN n : S.space).val.1) atTop
      (𝓝 (u + v)) := huN1.add hvN1
  have hwM1 : Tendsto (fun n => (uN n - vN n : S.space).val.1) atTop
      (𝓝 (u - v)) := huN1.sub hvN1
  have hwP_weak : ∀ f : DomainL2 Q,
      Tendsto (fun n => inner ℝ f (uN n + vN n : S.space).val.1) atTop
        (𝓝 (inner ℝ f (u + v))) := by
    intro f
    exact ((continuous_const.inner continuous_id).tendsto (u + v)).comp hwP1
  have hwM_weak : ∀ f : DomainL2 Q,
      Tendsto (fun n => inner ℝ f (uN n - vN n : S.space).val.1) atTop
        (𝓝 (inner ℝ f (u - v))) := by
    intro f
    exact ((continuous_const.inner continuous_id).tendsto (u - v)).comp hwM1
  have hP_le : limitFormEnergy G (u + v) ≤
      liminf (fun n => ((responseForm S (a n) (uN n + vN n : S.space)
        (uN n + vN n : S.space) : ℝ) : EReal)) atTop :=
    hLower (fun n => uN n + vN n) (u + v) hwP_weak
  have hM_le : limitFormEnergy G (u - v) ≤
      liminf (fun n => ((responseForm S (a n) (uN n - vN n : S.space)
        (uN n - vN n : S.space) : ℝ) : EReal)) atTop :=
    hLower (fun n => uN n - vN n) (u - v) hwM_weak
  have hresponseP :
      (fun n => ((responseForm S (a n) (uN n + vN n : S.space)
        (uN n + vN n : S.space) : ℝ) : EReal)) =
      fun n => (((responseForm S (a n) (uN n) (uN n) : ℝ) : EReal)
        + ((responseForm S (a n) (vN n) (vN n) : ℝ) : EReal)) := by
    funext n
    have h1 : responseForm S (a n) (uN n + vN n) (uN n + vN n) =
        responseForm S (a n) (uN n) (uN n) + responseForm S (a n) (vN n) (vN n) := by
      exact aux_prop_locality_response_add_zero (responseForm S (a n))
        (fun x y => responseForm_symm S (a n) x y) (hcross n)
    simpa only [EReal.coe_add] using congrArg (fun x : ℝ => (x : EReal)) h1
  have hresponseM :
      (fun n => ((responseForm S (a n) (uN n - vN n : S.space)
        (uN n - vN n : S.space) : ℝ) : EReal)) =
      fun n => (((responseForm S (a n) (uN n) (uN n) : ℝ) : EReal)
        + ((responseForm S (a n) (vN n) (vN n) : ℝ) : EReal)) := by
    funext n
    have h1 : responseForm S (a n) (uN n - vN n) (uN n - vN n) =
        responseForm S (a n) (uN n) (uN n) + responseForm S (a n) (vN n) (vN n) := by
      exact aux_prop_locality_response_sub_zero (responseForm S (a n))
        (fun x y => responseForm_symm S (a n) x y) (hcross n)
    simpa only [EReal.coe_add] using congrArg (fun x : ℝ => (x : EReal)) h1
  have hlimP : liminf (fun n => (((responseForm S (a n) (uN n) (uN n) : ℝ) : EReal)
      + ((responseForm S (a n) (vN n) (vN n) : ℝ) : EReal))) atTop
      = limitFormEnergy G u + limitFormEnergy G v := by
    have hu_bot : limitFormEnergy G u ≠ (⊥ : EReal) := by
      intro h
      have hnonneg := limitFormEnergy_nonneg G u
      rw [h] at hnonneg
      simp at hnonneg
    have hsum : Tendsto
        (fun n => (((responseForm S (a n) (uN n) (uN n) : ℝ) : EReal)
          + ((responseForm S (a n) (vN n) (vN n) : ℝ) : EReal))) atTop
        (𝓝 (limitFormEnergy G u + limitFormEnergy G v)) := by
      have hcont := EReal.continuousAt_add
        (p := (limitFormEnergy G u, limitFormEnergy G v))
        (Or.inl (ne_of_lt hu.1)) (Or.inl hu_bot)
      have hp : Tendsto
          (fun n => (((responseForm S (a n) (uN n) (uN n) : ℝ) : EReal),
            ((responseForm S (a n) (vN n) (vN n) : ℝ) : EReal))) atTop
          (𝓝 (limitFormEnergy G u, limitFormEnergy G v)) := by
        rw [nhds_prod_eq]
        exact huNe.prodMk hvNe
      exact hcont.tendsto.comp hp
    exact hsum.liminf_eq
  have hP_le' : limitFormEnergy G (u + v) ≤ limitFormEnergy G u + limitFormEnergy G v := by
    rw [hresponseP, hlimP] at hP_le
    exact hP_le
  have hM_le' : limitFormEnergy G (u - v) ≤ limitFormEnergy G u + limitFormEnergy G v := by
    rw [hresponseM, hlimP] at hM_le
    exact hM_le
  have hE0 : limitFormEnergy G (0 : DomainL2 Q) = 0 := by
    refine le_antisymm ?_ (limitFormEnergy_nonneg G 0)
    have hh := hLower (fun _ : ℕ => (0 : S.space)) (0 : DomainL2 Q) (by
      intro f
      have hconst : (fun _ : ℕ => inner ℝ f ((0 : S.space)).val.1) =
          fun _ : ℕ => (0 : ℝ) := by
        funext n
        change inner ℝ f (0 : DomainL2 Q) = 0
        exact inner_zero_right f
      rw [hconst, inner_zero_right f]
      exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (0 : ℝ))))
    simp only [aux_prop_locality_response_zero, liminf_const] at hh
    exact hh
  have hpos : ∀ x : DomainL2 Q, 0 ≤ inner ℝ x (G x) := by
    intro x
    have hle : ((-(inner ℝ x (G x)) : ℝ) : EReal) ≤
        limitFormEnergy G (0 : DomainL2 Q) := by
      rw [limitFormEnergy]
      have h1 := le_iSup
        (fun f : DomainL2 Q => ((2 * inner ℝ f (0 : DomainL2 Q) -
          inner ℝ f (G f) : ℝ) : EReal)) x
      have hx : (2 * inner ℝ x (0 : DomainL2 Q) - inner ℝ x (G x) : ℝ) =
          -inner ℝ x (G x) := by
        have hz : inner ℝ x (0 : DomainL2 Q) = 0 := inner_zero_right x
        rw [hz]
        ring
      rw [hx] at h1
      exact h1
    rw [hE0] at hle
    have hr : (-(inner ℝ x (G x)) : ℝ) ≤ 0 := by
      exact EReal.coe_le_coe_iff.mp hle
    linarith
  have hsymm' : ∀ x y : DomainL2 Q, inner ℝ (G x) y = inner ℝ x (G y) := by
    intro x y
    rw [real_inner_comm, hGsymm]
  have hpara2 := aux_prop_locality_energy_parallelogram d Q G u v hsymm' hpos
  have hMtop : limitFormEnergy G u + limitFormEnergy G v ≠ ⊤ := by
    intro hcon
    have hu_top : limitFormEnergy G u ≠ ⊤ := ne_of_lt hu.1
    have hv_top : limitFormEnergy G v ≠ ⊤ := ne_of_lt hv.1
    exact aux_prop_locality_add_ne_top hu_top hv_top hcon
  have haM : limitFormEnergy G (u + v) = limitFormEnergy G u + limitFormEnergy G v :=
    aux_prop_locality_eq_of_le_and_add_eq hP_le' hM_le' hpara2 hMtop
  have hbM : limitFormEnergy G (u - v) = limitFormEnergy G u + limitFormEnergy G v :=
    aux_prop_locality_eq_of_le_and_add_eq hM_le' hP_le' (by rw [add_comm]; exact hpara2) hMtop
  have huv : limitFormEnergy G (u + v) = limitFormEnergy G (u - v) := haM.trans hbM.symm
  have hMbot : limitFormEnergy G u + limitFormEnergy G v ≠ (⊥ : EReal) := by
    intro h
    have hh : (0 : EReal) ≤ limitFormEnergy G u + limitFormEnergy G v :=
      add_nonneg (limitFormEnergy_nonneg G u) (limitFormEnergy_nonneg G v)
    rw [h] at hh
    simp at hh
  show (limitFormEnergy G (u + v) - limitFormEnergy G (u - v)) / (4 : EReal) = 0
  rw [huv, hbM, EReal.sub_self hMtop hMbot, EReal.zero_div] -/
