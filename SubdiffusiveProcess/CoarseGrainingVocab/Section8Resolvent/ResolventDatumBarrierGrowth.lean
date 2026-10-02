import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumBarrierLimit
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumSolvability
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.AnchoredClauses
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.Convergence
import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.PositiveRescaling
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellSummable




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Topology
open Homogenization
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
open scoped ZeroAtInfty CompactlySupported

noncomputable section

variable {d : ℕ}

/-! ### Elementary facts -/

theorem continuous_vecNormSq_vec : Continuous (vecNormSq : Vec d → ℝ) := by
  have h : Continuous (fun x : Vec d ↦ ∑ i : Fin d, x i * x i) :=
    continuous_finset_sum _ fun i _ ↦ (continuous_apply i).mul (continuous_apply i)
  exact h

theorem continuous_euclideanNorm : Continuous (euclideanNorm : Vec d → ℝ) :=
  Real.continuous_sqrt.comp continuous_vecNormSq_vec

/-- The logarithmic envelope is dominated by a linear one. -/
theorem one_add_sqrt_log_le (t : ℝ) (ht : 0 ≤ t) :
    1 + Real.sqrt (Real.log (2 + t)) ≤ 5 / 2 * (1 + t) := by
  have h2 : (0 : ℝ) < 2 + t := by linarith
  have hlog : Real.log (2 + t) ≤ 1 + t := by
    have := Real.log_le_sub_one_of_pos h2
    linarith
  have hlog0 : 0 ≤ Real.log (2 + t) := Real.log_nonneg (by linarith)
  have hsqrt : Real.sqrt (Real.log (2 + t)) ≤ (Real.log (2 + t) + 1) / 2 := by
    have hs := Real.sq_sqrt hlog0
    nlinarith [Real.sqrt_nonneg (Real.log (2 + t)),
      sq_nonneg (Real.sqrt (Real.log (2 + t)) - 1)]
  linarith

/-- The Euclidean gradient of `exp ∘ g` for a potential field. -/
theorem euclideanGradient_exp_potentialField (g : PotentialField d) (x : Vec d) :
    euclideanGradient (fun y ↦ Real.exp (g y)) x = Real.exp (g x) • shellGradient g x := by
  funext i
  have hg : HasFDerivAt (fun y : Vec d ↦ (g : Vec d → ℝ) y)
      (PotentialField.deriv g x) x := g.hasFDerivAt x
  have hexp : HasFDerivAt (fun y : Vec d ↦ Real.exp (g y))
      (Real.exp (g x) • PotentialField.deriv g x) x :=
    (Real.hasDerivAt_exp (g x)).comp_hasFDerivAt x hg
  show euclideanCoordDeriv i (fun y : Vec d ↦ Real.exp (g y)) x = _
  rw [euclideanCoordDeriv, hexp.fderiv]
  rfl

/-- The Euclidean gradient of a constant multiple. -/
theorem euclideanGradient_const_mul {g : Vec d → ℝ} (hg : Differentiable ℝ g)
    (C : ℝ) (x : Vec d) :
    euclideanGradient (fun y ↦ C * g y) x = C • euclideanGradient g x := by
  funext i
  show euclideanCoordDeriv i (fun y : Vec d ↦ C * g y) x = _
  rw [euclideanCoordDeriv, fderiv_const_mul (hg x)]
  rfl

/-- The logarithmic envelope passes to the anchored limit. -/
theorem euclideanNorm_shellGradient_anchoredLog_le
    (omega : AnchoredC11Sample d) (x : Vec d) {Bnd : ℝ}
    (h : ∀ L : ℕ, euclideanNorm (shellGradient (anchoredPartialSumField omega.1 L) x) ≤ Bnd) :
    euclideanNorm (shellGradient (anchoredLog omega) x) ≤ Bnd := by
  have huni := tendstoUniformlyOn_shellGradient omega (isCompact_singleton (x := x))
  have hpt : Tendsto (fun L ↦ shellGradient (anchoredPartialSumField omega.1 L) x)
      atTop (nhds (shellGradient (anchoredLog omega) x)) :=
    huni.tendsto_at (Set.mem_singleton x)
  have hcont : Tendsto
      (fun L ↦ euclideanNorm (shellGradient (anchoredPartialSumField omega.1 L) x))
      atTop (nhds (euclideanNorm (shellGradient (anchoredLog omega) x))) :=
    (continuous_euclideanNorm.tendsto _).comp hpt
  exact le_of_tendsto hcont (Filter.Eventually.of_forall h)

/-! ### The two growth hypotheses for a coefficient `C₀ · exp ∘ g` -/

/-- **The barrier growth hypotheses from the anchored clauses.**  The reversible
pair uses only the logarithmic envelope of `∇ log c`; the divergence pair uses
the polynomial envelope of `c` and `∇c`, whose exponent `anchoredKappa = 3/4`
lies below `1`. -/
theorem linearGrowth_of_expPotential {C0 : ℝ} (hC0 : 0 < C0) (g : PotentialField d)
    {c : Vec d → ℝ} (hc : c = fun y ↦ C0 * Real.exp (g y))
    {Cw : ℝ} (hCw : 0 ≤ Cw)
    (hpoly : ∀ x : Vec d, Real.exp (g x) +
      euclideanNorm (Real.exp (g x) • shellGradient g x) ≤
        Cw * (1 + ‖x‖) ^ anchoredKappa)
    (hlog : ∀ x : Vec d, euclideanNorm (shellGradient g x) ≤
      Cw * (1 + Real.sqrt (Real.log (2 + ‖x‖)))) :
    (∀ x, euclideanNorm (euclideanGradient c x) + c x ≤
        (5 * Cw / 2 + 1) * c x * (1 + ‖x‖)) ∧
      (∀ x, euclideanNorm (euclideanGradient c x) + c x ≤
        C0 * Cw * (1 : ℝ) * (1 + ‖x‖)) := by
  have hgdiff : Differentiable ℝ (fun y : Vec d ↦ Real.exp (g y)) := by
    intro y
    exact ((Real.hasDerivAt_exp (g y)).comp_hasFDerivAt y (g.hasFDerivAt y)).differentiableAt
  have hgrad : ∀ x, euclideanGradient c x =
      C0 • (Real.exp (g x) • shellGradient g x) := by
    intro x
    rw [hc, euclideanGradient_const_mul hgdiff C0 x,
      euclideanGradient_exp_potentialField g x]
  have hnorm : ∀ x, euclideanNorm (euclideanGradient c x) =
      C0 * (Real.exp (g x) * euclideanNorm (shellGradient g x)) := by
    intro x
    rw [hgrad x, euclideanNorm_smul, euclideanNorm_smul, abs_of_pos hC0,
      abs_of_pos (Real.exp_pos _)]
  have hcx : ∀ x, c x = C0 * Real.exp (g x) := by
    intro x; rw [hc]
  constructor
  · intro x
    have hr0 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
    have hsg := hlog x
    have hlin : euclideanNorm (shellGradient g x) + 1 ≤
        (5 * Cw / 2 + 1) * (1 + ‖x‖) := by
      have hbase := one_add_sqrt_log_le ‖x‖ hr0
      have hmul : Cw * (1 + Real.sqrt (Real.log (2 + ‖x‖))) ≤
          Cw * (5 / 2 * (1 + ‖x‖)) := mul_le_mul_of_nonneg_left hbase hCw
      nlinarith [hsg, hmul, hr0]
    have hexp : 0 < Real.exp (g x) := Real.exp_pos _
    have hfac : 0 < C0 * Real.exp (g x) := mul_pos hC0 hexp
    rw [hnorm x, hcx x]
    nlinarith [hlin, hfac]
  · intro x
    have hr0 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
    have hkappa : (1 + ‖x‖) ^ anchoredKappa ≤ 1 + ‖x‖ := by
      have hone : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith
      have hle : anchoredKappa ≤ (1 : ℝ) := anchoredKappa_mem.2.le
      have := Real.rpow_le_rpow_of_exponent_le hone hle
      rwa [Real.rpow_one] at this
    have hp := hpoly x
    have hnn : euclideanNorm (Real.exp (g x) • shellGradient g x) =
        Real.exp (g x) * euclideanNorm (shellGradient g x) := by
      rw [euclideanNorm_smul, abs_of_pos (Real.exp_pos _)]
    rw [hnorm x, hcx x]
    rw [hnn] at hp
    have hstep : Real.exp (g x) * euclideanNorm (shellGradient g x) + Real.exp (g x) ≤
        Cw * (1 + ‖x‖) := by
      have : Cw * (1 + ‖x‖) ^ anchoredKappa ≤ Cw * (1 + ‖x‖) :=
        mul_le_mul_of_nonneg_left hkappa hCw
      linarith
    nlinarith [hstep, hC0]




/-- **Both growth hypotheses for `coefficientAt M L ω`, at every cutoff level,**
from the two anchored clauses of one sample. -/
theorem exists_linearGrowth_of_clauses (M : GMCModel d) (L : WithTop ℕ)
    (omega : AnchoredC11Sample d) {Cw : ℝ} (hCw : 0 ≤ Cw)
    (hpoly : ∀ x : Vec d,
      (aAnchored M omega x + (aAnchored M omega x)⁻¹ +
          euclideanNorm (aAnchored M omega x • shellGradient (anchoredLog omega) x) ≤
        Cw * (1 + ‖x‖) ^ anchoredKappa) ∧
      ∀ L' : ℕ,
        anchoredCutoff M L' omega.1 x + (anchoredCutoff M L' omega.1 x)⁻¹ +
            euclideanNorm (anchoredCutoff M L' omega.1 x •
              shellGradient (anchoredPartialSumField omega.1 L') x) ≤
          Cw * (1 + ‖x‖) ^ anchoredKappa)
    (hlog : ∀ x : Vec d, ∀ L' : ℕ,
      euclideanNorm (shellGradient (anchoredPartialSumField omega.1 L') x) +
          PotentialField.unitCubeDerivLipschitzSeminorm
            (PotentialField.translate x (anchoredPartialSumField omega.1 L')) ≤
        Cw * (1 + Real.sqrt (Real.log (2 + ‖x‖)))) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ x, euclideanNorm (euclideanGradient (coefficientAt M L omega) x) +
          coefficientAt M L omega x ≤
        K * coefficientAt M L omega x * (1 + ‖x‖)) ∧
      (∀ x, euclideanNorm (euclideanGradient (coefficientAt M L omega) x) +
          coefficientAt M L omega x ≤ K * (1 : ℝ) * (1 + ‖x‖)) := by
  have hlog' : ∀ (x : Vec d) (L' : ℕ),
      euclideanNorm (shellGradient (anchoredPartialSumField omega.1 L') x) ≤
        Cw * (1 + Real.sqrt (Real.log (2 + ‖x‖))) := by
    intro x L'
    have hnn := PotentialField.unitCubeDerivLipschitzSeminorm_nonneg
      (PotentialField.translate x (anchoredPartialSumField omega.1 L'))
    linarith [hlog x L']
  induction L using WithTop.recTopCoe with
  | top =>
      have hcfun : coefficientAt M (⊤ : WithTop ℕ) omega =
          fun y ↦ (1 : ℝ) * Real.exp (anchoredLog omega y) := by
        funext y
        show aAnchored M omega y = _
        rw [aAnchored, one_mul]
      have hpoly' : ∀ x : Vec d, Real.exp (anchoredLog omega x) +
          euclideanNorm (Real.exp (anchoredLog omega x) •
            shellGradient (anchoredLog omega) x) ≤
          Cw * (1 + ‖x‖) ^ anchoredKappa := by
        intro x
        have h := (hpoly x).1
        have hinv : 0 < (aAnchored M omega x)⁻¹ := by
          rw [aAnchored]
          exact inv_pos.2 (Real.exp_pos _)
        have hval : aAnchored M omega x = Real.exp (anchoredLog omega x) := rfl
        rw [hval] at h hinv
        linarith
      have hlogLim : ∀ x : Vec d,
          euclideanNorm (shellGradient (anchoredLog omega) x) ≤
            Cw * (1 + Real.sqrt (Real.log (2 + ‖x‖))) := by
        intro x
        exact euclideanNorm_shellGradient_anchoredLog_le omega x (fun L' ↦ hlog' x L')
      obtain ⟨h1, h2⟩ := linearGrowth_of_expPotential (C0 := 1) one_pos
        (anchoredLog omega) hcfun hCw hpoly' hlogLim
      refine ⟨max (5 * Cw / 2 + 1) (1 * Cw), le_trans (by linarith) (le_max_left _ _),
        fun x ↦ ?_, fun x ↦ ?_⟩
      · have hcpos : 0 < coefficientAt M (⊤ : WithTop ℕ) omega x :=
          coefficientAt_pos M (⊤ : WithTop ℕ) omega x
        have hmono : (5 * Cw / 2 + 1) * coefficientAt M (⊤ : WithTop ℕ) omega x * (1 + ‖x‖) ≤
            max (5 * Cw / 2 + 1) (1 * Cw) * coefficientAt M (⊤ : WithTop ℕ) omega x *
              (1 + ‖x‖) := by
          have hfac : 0 ≤ coefficientAt M (⊤ : WithTop ℕ) omega x * (1 + ‖x‖) :=
            mul_nonneg hcpos.le (by linarith [norm_nonneg x])
          nlinarith [le_max_left (5 * Cw / 2 + 1) (1 * Cw), hfac]
        exact le_trans (h1 x) hmono
      · have hmono : 1 * Cw * (1 : ℝ) * (1 + ‖x‖) ≤
            max (5 * Cw / 2 + 1) (1 * Cw) * (1 : ℝ) * (1 + ‖x‖) := by
          have hfac : (0 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
          nlinarith [le_max_right (5 * Cw / 2 + 1) (1 * Cw), hfac]
        exact le_trans (h2 x) hmono
  | coe n =>
      set C0 : ℝ := aCutoff M n omega.1 0 with hC0def
      have hC0 : 0 < C0 := aCutoff_pos M n omega.1 0
      have hcfun : coefficientAt M (n : WithTop ℕ) omega =
          fun y ↦ C0 * Real.exp (anchoredPartialSumField omega.1 n y) := by
        rw [Section6TheoremC.coefficientAt_natCast_eq_const_mul_anchoredCutoff]
        funext y
        rw [anchoredCutoff_eq_exp_field]
      have hpoly' : ∀ x : Vec d, Real.exp (anchoredPartialSumField omega.1 n x) +
          euclideanNorm (Real.exp (anchoredPartialSumField omega.1 n x) •
            shellGradient (anchoredPartialSumField omega.1 n) x) ≤
          Cw * (1 + ‖x‖) ^ anchoredKappa := by
        intro x
        have h := (hpoly x).2 n
        have hval : anchoredCutoff M n omega.1 x =
            Real.exp (anchoredPartialSumField omega.1 n x) :=
          anchoredCutoff_eq_exp_field M n omega.1 x
        have hinv : 0 < (anchoredCutoff M n omega.1 x)⁻¹ :=
          inv_pos.2 (Section6TheoremC.anchoredCutoff_pos M n omega.1 x)
        rw [hval] at h hinv
        linarith
      obtain ⟨h1, h2⟩ := linearGrowth_of_expPotential hC0
        (anchoredPartialSumField omega.1 n) hcfun hCw hpoly' (fun x ↦ hlog' x n)
      refine ⟨max (5 * Cw / 2 + 1) (C0 * Cw), le_trans (by linarith) (le_max_left _ _),
        fun x ↦ ?_, fun x ↦ ?_⟩
      · have hcpos : 0 < coefficientAt M (n : WithTop ℕ) omega x :=
          coefficientAt_pos M (n : WithTop ℕ) omega x
        have hmono : (5 * Cw / 2 + 1) * coefficientAt M (n : WithTop ℕ) omega x * (1 + ‖x‖) ≤
            max (5 * Cw / 2 + 1) (C0 * Cw) * coefficientAt M (n : WithTop ℕ) omega x *
              (1 + ‖x‖) := by
          have hfac : 0 ≤ coefficientAt M (n : WithTop ℕ) omega x * (1 + ‖x‖) :=
            mul_nonneg hcpos.le (by linarith [norm_nonneg x])
          nlinarith [le_max_left (5 * Cw / 2 + 1) (C0 * Cw), hfac]
        exact le_trans (h1 x) hmono
      · have hmono : C0 * Cw * (1 : ℝ) * (1 + ‖x‖) ≤
            max (5 * Cw / 2 + 1) (C0 * Cw) * (1 : ℝ) * (1 + ‖x‖) := by
          have hfac : (0 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
          nlinarith [le_max_right (5 * Cw / 2 + 1) (C0 * Cw), hfac]
        exact le_trans (h2 x) hmono

/-! ### The frozen datum on a full-measure set -/

/-- A measurable full-measure subset carrying an almost-sure property. -/
theorem exists_measurable_full_of_ae {alpha : Type*} [MeasurableSpace alpha]
    (mu : Measure alpha) [IsProbabilityMeasure mu] {p : alpha → Prop}
    (h : ∀ᵐ x ∂mu, p x) :
    ∃ s : Set alpha, MeasurableSet s ∧ mu s = 1 ∧ ∀ x ∈ s, p x := by
  have h0 : mu {x | ¬ p x} = 0 := h
  obtain ⟨N, hsub, hNmeas, hN0⟩ := exists_measurable_superset_of_null h0
  refine ⟨Nᶜ, hNmeas.compl, ?_, ?_⟩
  · rw [measure_compl hNmeas (measure_ne_top mu N), hN0, measure_univ, tsub_zero]
  · intro x hx
    by_contra hp
    exact hx (hsub hp)

/-- The zero resolvent datum, used off the full-measure set. -/
def zeroC0ResolventDatum (E : Type*) [TopologicalSpace E] : C0ResolventDatum E where
  solution := fun _ _ ↦ 0
  solution_add := by intro _ _ _; simp
  solution_smul := by intro _ _ _; simp
  solution_nonneg := by intro _ _ _ _; simp
  norm_solution_le := by
    intro mu f
    have hmu : (0 : ℝ) < (mu : ℝ) := mu.2
    have : (0 : ℝ) ≤ ((mu : ℝ))⁻¹ * ‖f‖ :=
      mul_nonneg (inv_nonneg.2 hmu.le) (norm_nonneg _)
    simpa using this
  solution_sub_solution := by intro _ _ _; simp

/-- **The frozen conclusion of `l.gmc.resolvent.datum`, on a prescribed set.**
The resolvent data are supplied by the landed gate on `full` and are the zero
datum elsewhere. -/
theorem exists_gmc_resolvent_data_of_solvability_on [NeZero d]
    (M : GMCModel d) (L : WithTop ℕ) (full : Set (AnchoredC11Sample d))
    (hX : ∀ omega ∈ full, HasC0MassiveSolutionsOnCompactData (coefficientAt M L omega)
      (coefficientAt M L omega))
    (hY : ∀ omega ∈ full, HasC0MassiveSolutionsOnCompactData (coefficientAt M L omega)
      (fun _ ↦ (1 : ℝ))) :
    ∃ DX DY : AnchoredC11Sample d → C0ResolventDatum (Vec d),
      ∀ omega ∈ full,
        (∀ mu, DenseRange ((DX omega).operator mu)) ∧
        IsWeakEllipticResolvent (coefficientAt M L omega)
          (coefficientAt M L omega) (DX omega) ∧
        (∀ mu, DenseRange ((DY omega).operator mu)) ∧
        IsWeakEllipticResolvent (coefficientAt M L omega)
          (fun _ ↦ (1 : ℝ)) (DY omega) := by
  classical
  have key : ∀ omega : AnchoredC11Sample d,
      ∃ DXo DYo : C0ResolventDatum (Vec d), omega ∈ full →
        ((∀ mu, DenseRange (DXo.operator mu)) ∧
          IsWeakEllipticResolvent (coefficientAt M L omega)
            (coefficientAt M L omega) DXo ∧
          (∀ mu, DenseRange (DYo.operator mu)) ∧
          IsWeakEllipticResolvent (coefficientAt M L omega)
            (fun _ ↦ (1 : ℝ)) DYo) := by
    intro omega
    by_cases h : omega ∈ full
    · have RX := MassiveC0Resolvent.ofHasC0MassiveSolutions
        (hasC0MassiveSolutions_reversible_of_solvability M L omega (hX omega h))
      have RY := MassiveC0Resolvent.ofHasC0MassiveSolutions
        (hasC0MassiveSolutions_divergence_of_solvability M L omega (hY omega h))
      obtain ⟨DXo, hDX1, hDX2⟩ := exists_c0ResolventDatum_of_massiveC0Resolvent
        (reversibleMassiveCubeBounds M L omega) RX
        (hasStrongMassiveResolventLimit_of_hasDenseMassiveResolventRange
          (reversibleMassiveCubeBounds M L omega)
          (hasDenseMassiveResolventRange_reversible M L omega) RX)
      obtain ⟨DYo, hDY1, hDY2⟩ := exists_c0ResolventDatum_of_massiveC0Resolvent
        (divergenceMassiveCubeBounds M L omega) RY
        (hasStrongMassiveResolventLimit_of_hasDenseMassiveResolventRange
          (divergenceMassiveCubeBounds M L omega)
          (hasDenseMassiveResolventRange_divergence M L omega) RY)
      exact ⟨DXo, DYo, fun _ ↦ ⟨hDX1, hDX2, hDY1, hDY2⟩⟩
    · exact ⟨zeroC0ResolventDatum (Vec d), zeroC0ResolventDatum (Vec d),
        fun h' ↦ absurd h' h⟩
  choose DX DY hD using key
  exact ⟨DX, DY, fun omega homega ↦ hD omega homega⟩

/-- **The Section 8 resolvent datum for models in the small-`δ` regime.**  The
almost-sure anchored growth clauses supply the barrier hypotheses for both
paper pairs, whence whole-space solvability on compactly supported data and the
frozen conclusion of `l.gmc.resolvent.datum` on a measurable full-measure set of
anchored samples. -/
theorem exists_gmc_resolvent_data_of_delta_le [NeZero d]
    (M : GMCModel d) (hdelta : M.delta ≤ anchoredDelta0 d) (L : WithTop ℕ) :
    ∃ hmeas : MeasurableSet (anchoredC11GoodSet d),
    ∃ hfull : M.P.toMeasure (anchoredC11GoodSet d) = 1,
    ∃ full : Set (AnchoredC11Sample d),
      MeasurableSet full ∧
      (anchoredC11SampleLaw M hmeas hfull).toMeasure full = 1 ∧
    ∃ DX DY : AnchoredC11Sample d → C0ResolventDatum (Vec d),
      ∀ omega ∈ full,
        (∀ mu, DenseRange ((DX omega).operator mu)) ∧
        IsWeakEllipticResolvent (coefficientAt M L omega)
          (coefficientAt M L omega) (DX omega) ∧
        (∀ mu, DenseRange ((DY omega).operator mu)) ∧
        IsWeakEllipticResolvent (coefficientAt M L omega)
          (fun _ ↦ (1 : ℝ)) (DY omega) := by
  classical
  refine ⟨measurableSet_anchoredC11GoodSet d, measure_anchoredC11GoodSet_eq_one M, ?_⟩
  obtain ⟨full, hfullMeas, hfullOne, hfullProp⟩ :=
    exists_measurable_full_of_ae _
      (ae_anchored_growth_clauses M hdelta (measurableSet_anchoredC11GoodSet d)
        (measure_anchoredC11GoodSet_eq_one M))
  have hgrowth : ∀ omega ∈ full, ∃ K : ℝ, 0 ≤ K ∧
      (∀ x, euclideanNorm (euclideanGradient (coefficientAt M L omega) x) +
          coefficientAt M L omega x ≤
        K * coefficientAt M L omega x * (1 + ‖x‖)) ∧
      (∀ x, euclideanNorm (euclideanGradient (coefficientAt M L omega) x) +
          coefficientAt M L omega x ≤ K * (1 : ℝ) * (1 + ‖x‖)) := by
    intro omega homega
    obtain ⟨hCw, hpoly, hlog⟩ := hfullProp omega homega
    exact exists_linearGrowth_of_clauses M L omega hCw hpoly hlog
  refine ⟨full, hfullMeas, hfullOne, ?_⟩
  refine exists_gmc_resolvent_data_of_solvability_on M L full ?_ ?_
  · intro omega homega
    obtain ⟨K, hK, hrev, _⟩ := hgrowth omega homega
    exact hasC0MassiveSolutionsOnCompactData_of_linearGrowth M L omega
      (reversibleMassiveCubeBounds M L omega)
      (fun x ↦ coefficientAt_pos M L omega x) hK hrev
  · intro omega homega
    obtain ⟨K, hK, _, hdiv⟩ := hgrowth omega homega
    exact hasC0MassiveSolutionsOnCompactData_of_linearGrowth M L omega
      (divergenceMassiveCubeBounds M L omega) (fun _ ↦ one_pos) hK hdiv

/-- **The proposed repaired shape of `l.gmc.resolvent.datum`.**  This is the v2
frozen conclusion with the smallness guard `M.delta ≤ δ₀(d)` that the two
anchored growth clauses require, in the exact idiom already used by
`l.large.scale.Holder.multifractal` (`SubdiffusiveProcess/Providers/Section6/
LargeScaleHolderMultifractal.lean`).  See the report for the author item. -/
theorem exists_delta0_gmc_resolvent_data (d : ℕ) [NeZero d] :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 → ∀ L : WithTop ℕ,
      ∃ hmeas : MeasurableSet (anchoredC11GoodSet d),
      ∃ hfull : M.P.toMeasure (anchoredC11GoodSet d) = 1,
      ∃ full : Set (AnchoredC11Sample d),
        MeasurableSet full ∧
        (anchoredC11SampleLaw M hmeas hfull).toMeasure full = 1 ∧
      ∃ DX DY : AnchoredC11Sample d → C0ResolventDatum (Vec d),
        ∀ omega ∈ full,
          (∀ mu, DenseRange ((DX omega).operator mu)) ∧
          IsWeakEllipticResolvent (coefficientAt M L omega)
            (coefficientAt M L omega) (DX omega) ∧
          (∀ mu, DenseRange ((DY omega).operator mu)) ∧
          IsWeakEllipticResolvent (coefficientAt M L omega)
            (fun _ ↦ (1 : ℝ)) (DY omega) :=
  ⟨anchoredDelta0 d, anchoredDelta0_pos d,
    fun M hdelta L ↦ exists_gmc_resolvent_data_of_delta_le M hdelta L⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
