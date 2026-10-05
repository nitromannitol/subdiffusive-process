module

public import SubdiffusiveProcess.CoarseGrainingVocab.AnnealedMatrixVariational
public import SubdiffusiveProcess.CoarseGrainingVocab.ShellSensitivity

@[expose] public section

/-!
# Measurability and integrability of finite-cutoff spatial ratio suprema

The uncountable supremum in `cutoffRatioSup` is replaced by a supremum over a
countable dense subset of the domain.  This follows the proof organization of
`Algsuperdiff/Section3/Provider/BadEvents/SupMeasurability.lean`.  Integrability
then reuses the common finite-cover majorant constructed for
`e.aman.Linfty.moments` in `ShellSensitivity.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open scoped ENNReal

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

private theorem exists_countable_dense_domain {d : ℕ} (U : Ch02.Domain d) :
    ∃ D : Set (Vec d), D.Countable ∧ D ⊆ (U : Set (Vec d)) ∧
      (U : Set (Vec d)) ⊆ closure D := by
  obtain ⟨s, hs, hsdense⟩ := TopologicalSpace.exists_countable_dense (Vec d)
  refine ⟨s ∩ (U : Set (Vec d)), hs.mono Set.inter_subset_left,
    Set.inter_subset_right, ?_⟩
  intro y hy
  rw [Metric.mem_closure_iff]
  intro eps heps
  have hopen : IsOpen (Metric.ball y eps ∩ (U : Set (Vec d))) :=
    Metric.isOpen_ball.inter U.isOpen
  have hnonempty : (Metric.ball y eps ∩ (U : Set (Vec d))).Nonempty :=
    ⟨y, Metric.mem_ball_self heps, hy⟩
  obtain ⟨w, hws, hw⟩ := hsdense.exists_mem_open hopen hnonempty
  exact ⟨w, ⟨hws, hw.2⟩, by rw [dist_comm]; exact hw.1⟩

private theorem eq_iSup_of_dense_domain {d : ℕ} {U : Ch02.Domain d}
    {D : Set (Vec d)} (hDsub : D ⊆ (U : Set (Vec d)))
    (hDdense : (U : Set (Vec d)) ⊆ closure D)
    {g : Vec d → ℝ} (hg : Continuous g) (hgnn : ∀ y, 0 ≤ g y) {S : ℝ}
    (hpt : ∀ y ∈ (U : Set (Vec d)), g y ≤ S)
    (hleast : ∀ C : ℝ, 0 ≤ C →
      (∀ y ∈ (U : Set (Vec d)), g y ≤ C) → S ≤ C) :
    S = ⨆ w : D, g w.1 := by
  obtain ⟨y₀, hy₀⟩ := U.nonempty
  have hDne : D.Nonempty := by
    obtain ⟨w, hw, -⟩ := Metric.mem_closure_iff.1 (hDdense hy₀) 1 one_pos
    exact ⟨w, hw⟩
  have : Nonempty D := hDne.to_subtype
  have hbdd : BddAbove (Set.range fun w : D => g w.1) := by
    refine ⟨S, ?_⟩
    rintro t ⟨w, rfl⟩
    exact hpt w.1 (hDsub w.2)
  have hupper : ⨆ w : D, g w.1 ≤ S := ciSup_le fun w => hpt w.1 (hDsub w.2)
  have hnn : 0 ≤ ⨆ w : D, g w.1 := by
    obtain ⟨w, hw⟩ := hDne
    exact le_trans (hgnn w) (le_ciSup hbdd (⟨w, hw⟩ : D))
  refine le_antisymm (hleast _ hnn fun y hy => ?_) hupper
  by_contra hcon
  push Not at hcon
  set eps : ℝ := g y - ⨆ w : D, g w.1 with hepsdef
  have heps : 0 < eps := by rw [hepsdef]; linarith
  obtain ⟨delta, hdelta, hball⟩ := Metric.continuousAt_iff.1 hg.continuousAt eps heps
  obtain ⟨w, hwD, hwd⟩ := Metric.mem_closure_iff.1 (hDdense hy) delta hdelta
  have hgw : |g w - g y| < eps := by
    have := hball (show dist w y < delta by rw [dist_comm]; exact hwd)
    rwa [Real.dist_eq] at this
  have hlow : ⨆ v : D, g v.1 < g w := by
    have := (abs_lt.1 hgw).1
    rw [hepsdef] at this
    linarith
  exact absurd (le_ciSup hbdd (⟨w, hwD⟩ : D)) (not_le.2 hlow)

private theorem bddAbove_cutoffRatio_range {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (numerator denominator : ℕ)
    (U : Ch02.Domain d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    BddAbove {r : ℝ | ∃ x : Vec d, x ∈ (U : Set (Vec d)) ∧
      r = _root_.SubdiffusiveProcess.Model.aCutoff M numerator omega x /
        _root_.SubdiffusiveProcess.Model.aCutoff M denominator omega x} := by
  let g : Vec d → ℝ := fun x =>
    _root_.SubdiffusiveProcess.Model.aCutoff M numerator omega x /
      _root_.SubdiffusiveProcess.Model.aCutoff M denominator omega x
  have hg : Continuous g :=
    (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M numerator omega).div
      (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M denominator omega)
      (fun x => (_root_.SubdiffusiveProcess.Model.aCutoff_pos M denominator omega x).ne')
  have hcompact : IsCompact (closure (U : Set (Vec d))) :=
    U.isBoundedDomain.isBounded.isCompact_closure
  have himage : BddAbove (g '' closure (U : Set (Vec d))) :=
    hcompact.bddAbove_image hg.continuousOn
  refine himage.mono ?_
  rintro r ⟨x, hx, rfl⟩
  exact ⟨x, subset_closure hx, rfl⟩

private theorem cutoffRatioSup_eq_iSup_dense {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (numerator denominator : ℕ)
    (U : Ch02.Domain d) {D : Set (Vec d)}
    (hDsub : D ⊆ (U : Set (Vec d)))
    (hDdense : (U : Set (Vec d)) ⊆ closure D) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    cutoffRatioSup M numerator denominator U omega =
      ⨆ w : D, _root_.SubdiffusiveProcess.Model.aCutoff M numerator omega w.1 /
        _root_.SubdiffusiveProcess.Model.aCutoff M denominator omega w.1 := by
  let g : Vec d → ℝ := fun x =>
    _root_.SubdiffusiveProcess.Model.aCutoff M numerator omega x /
      _root_.SubdiffusiveProcess.Model.aCutoff M denominator omega x
  have hg : Continuous g :=
    (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M numerator omega).div
      (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M denominator omega)
      (fun x => (_root_.SubdiffusiveProcess.Model.aCutoff_pos M denominator omega x).ne')
  have hbdd := bddAbove_cutoffRatio_range M numerator denominator U omega
  obtain ⟨y₀, hy₀⟩ := U.nonempty
  apply eq_iSup_of_dense_domain hDsub hDdense hg
    (fun x => (div_pos
      (_root_.SubdiffusiveProcess.Model.aCutoff_pos M numerator omega x)
      (_root_.SubdiffusiveProcess.Model.aCutoff_pos M denominator omega x)).le)
  · intro y hy
    exact le_csSup hbdd ⟨y, hy, rfl⟩
  · intro C _hC hC
    unfold cutoffRatioSup
    apply csSup_le
    · exact ⟨g y₀, y₀, hy₀, rfl⟩
    · rintro r ⟨y, hy, rfl⟩
      exact hC y hy

/-- Every pointwise cutoff ratio is bounded by its spatial supremum. -/
theorem cutoffRatio_le_cutoffRatioSup {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (numerator denominator : ℕ)
    (U : Ch02.Domain d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) {x : Vec d}
    (hx : x ∈ (U : Set (Vec d))) :
    _root_.SubdiffusiveProcess.Model.aCutoff M numerator omega x /
        _root_.SubdiffusiveProcess.Model.aCutoff M denominator omega x ≤
      cutoffRatioSup M numerator denominator U omega := by
  exact le_csSup (bddAbove_cutoffRatio_range M numerator denominator U omega)
    ⟨x, hx, rfl⟩

/-- A cutoff ratio supremum is strictly positive on every nonempty domain. -/
theorem cutoffRatioSup_pos {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (numerator denominator : ℕ)
    (U : Ch02.Domain d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 < cutoffRatioSup M numerator denominator U omega := by
  obtain ⟨x, hx⟩ := U.nonempty
  exact (div_pos
    (_root_.SubdiffusiveProcess.Model.aCutoff_pos M numerator omega x)
    (_root_.SubdiffusiveProcess.Model.aCutoff_pos M denominator omega x)).trans_le
      (cutoffRatio_le_cutoffRatioSup M numerator denominator U omega hx)

/-- A finite-cutoff spatial ratio supremum is measurable. -/
theorem measurable_cutoffRatioSup {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (numerator denominator : ℕ)
    (U : Ch02.Domain d) :
    Measurable (cutoffRatioSup M numerator denominator U) := by
  obtain ⟨D, hDc, hDsub, hDdense⟩ := exists_countable_dense_domain U
  let : Countable D := hDc.to_subtype
  have heq : cutoffRatioSup M numerator denominator U = fun omega =>
      ⨆ w : D, _root_.SubdiffusiveProcess.Model.aCutoff M numerator omega w.1 /
        _root_.SubdiffusiveProcess.Model.aCutoff M denominator omega w.1 := by
    funext omega
    exact cutoffRatioSup_eq_iSup_dense M numerator denominator U
      hDsub hDdense omega
  rw [heq]
  exact Measurable.iSup fun w =>
    (_root_.SubdiffusiveProcess.Model.measurable_aCutoff M numerator w.1).div
      (_root_.SubdiffusiveProcess.Model.measurable_aCutoff M denominator w.1)

theorem aux_dedup_d261_potentialShellIndexSigma_mono {d : ℕ} {I J : Set ℕ}
    (hIJ : I ⊆ J) :
    potentialShellIndexSigma (d := d) I ≤ potentialShellIndexSigma J := by
  unfold potentialShellIndexSigma
  refine iSup_le fun k => iSup_le fun hk => ?_
  exact le_iSup_of_le k (le_iSup_of_le (hIJ hk) le_rfl)

private theorem potentialShellIndexSigma_mono {d : ℕ} {I J : Set ℕ}
    (hIJ : I ⊆ J) :
    potentialShellIndexSigma (d := d) I ≤ potentialShellIndexSigma J := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d261_potentialShellIndexSigma_mono (d := d) (I := I) (J := J) (hIJ := hIJ)

/-- Both orientations of a finite cutoff ratio supremum read only the strict
suffix above the lower cutoff. -/
theorem measurable_cutoffRatioSup_potentialShellIndexSigma_Ioi {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {n m : ℕ} (hnm : n < m)
    (U : Ch02.Domain d) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ (potentialShellIndexSigma (Set.Ioi n)) inferInstance
        (cutoffRatioSup M m n U) ∧
      @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ (potentialShellIndexSigma (Set.Ioi n)) inferInstance
        (cutoffRatioSup M n m U) := by
  obtain ⟨D, hDc, hDsub, hDdense⟩ := exists_countable_dense_domain U
  let : Countable D := hDc.to_subtype
  have hindices : (↑(cutoffShellIndices m (n : ℤ)) : Set ℕ) ⊆ Set.Ioi n := by
    intro k hk
    have hk' : k ∈ cutoffShellIndices m (n : ℤ) := hk
    exact (Finset.mem_Icc.mp hk').1
  have hsigma : potentialShellIndexSigma (d := d)
      (↑(cutoffShellIndices m (n : ℤ)) : Set ℕ) ≤
      potentialShellIndexSigma (Set.Ioi n) :=
    potentialShellIndexSigma_mono hindices
  have hfield := measurable_cutoffRatioMinusOne_shellIndexSigma M m (n : ℤ)
    (by omega) (by exact_mod_cast hnm)
  have hforwardPoint : ∀ w : D,
      @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ (potentialShellIndexSigma (Set.Ioi n)) inferInstance
        (fun omega => _root_.SubdiffusiveProcess.Model.aCutoff M m omega w.1 /
          _root_.SubdiffusiveProcess.Model.aCutoff M n omega w.1) := by
    intro w
    have hminus := ((measurable_pi_apply w.1).comp hfield).mono hsigma le_rfl
    have hadd := hminus.add_const 1
    convert hadd using 1
    funext omega
    simp [cutoffRatioMinusOne, aCutoffAtInt,
      show ¬ (n : ℤ) < 0 by omega]
  have hforward : @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
      (potentialShellIndexSigma (Set.Ioi n)) inferInstance
      (fun omega => ⨆ w : D, _root_.SubdiffusiveProcess.Model.aCutoff M m omega w.1 /
        _root_.SubdiffusiveProcess.Model.aCutoff M n omega w.1) :=
    Measurable.iSup hforwardPoint
  have hforwardEq : cutoffRatioSup M m n U = fun omega =>
      ⨆ w : D, _root_.SubdiffusiveProcess.Model.aCutoff M m omega w.1 /
        _root_.SubdiffusiveProcess.Model.aCutoff M n omega w.1 := by
    funext omega
    exact cutoffRatioSup_eq_iSup_dense M m n U hDsub hDdense omega
  have hforwardSup : @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
      (potentialShellIndexSigma (Set.Ioi n)) inferInstance
      (cutoffRatioSup M m n U) := by rwa [hforwardEq]
  have hinversePoint : ∀ w : D,
      @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ (potentialShellIndexSigma (Set.Ioi n)) inferInstance
        (fun omega => _root_.SubdiffusiveProcess.Model.aCutoff M n omega w.1 /
          _root_.SubdiffusiveProcess.Model.aCutoff M m omega w.1) := by
    intro w
    have hinv := (hforwardPoint w).inv
    convert hinv using 1
    funext omega
    have hm := (_root_.SubdiffusiveProcess.Model.aCutoff_pos M m omega w.1).ne'
    have hn := (_root_.SubdiffusiveProcess.Model.aCutoff_pos M n omega w.1).ne'
    simp only [Pi.inv_apply]
    field_simp
  have hinverse : @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
      (potentialShellIndexSigma (Set.Ioi n)) inferInstance
      (fun omega => ⨆ w : D, _root_.SubdiffusiveProcess.Model.aCutoff M n omega w.1 /
        _root_.SubdiffusiveProcess.Model.aCutoff M m omega w.1) :=
    Measurable.iSup hinversePoint
  have hinverseEq : cutoffRatioSup M n m U = fun omega =>
      ⨆ w : D, _root_.SubdiffusiveProcess.Model.aCutoff M n omega w.1 /
        _root_.SubdiffusiveProcess.Model.aCutoff M m omega w.1 := by
    funext omega
    exact cutoffRatioSup_eq_iSup_dense M n m U hDsub hDdense omega
  refine ⟨hforwardSup, ?_⟩
  rwa [hinverseEq]

private theorem exists_domain_subset_originCube {d : ℕ} (U : Ch02.Domain d) :
    ∃ k : ℤ, (U : Set (Vec d)) ⊆ openCubeSet (originCube d k) := by
  obtain ⟨R, hR⟩ := U.isBoundedDomain.isBounded.subset_closedBall 0
  obtain ⟨N, hN⟩ := exists_nat_gt R
  refine ⟨(N : ℤ), ?_⟩
  intro x hx
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hxR : dist x 0 ≤ R := by
    simpa only [Metric.mem_closedBall] using hR hx
  have hxi : |x i| ≤ R := by
    have hi := dist_le_pi_dist x 0 i
    rw [Real.dist_eq] at hi
    simp only [Pi.zero_apply, sub_zero] at hi
    exact hi.trans hxR
  have hNpow : (N : ℝ) ≤ (3 : ℝ) ^ N / (3 - 1) :=
    Nat.cast_le_pow_div_sub (by norm_num) N
  have hhalf : R < (1 / 2 : ℝ) * (3 : ℝ) ^ (N : ℤ) := by
    rw [zpow_natCast]
    norm_num at hNpow ⊢
    linarith
  constructor <;> linarith [le_abs_self (x i), neg_le_of_abs_le hxi]

/-- A common measurable majorant for both orientations of a cutoff-ratio
supremum on a domain contained in one origin cube.  This is public because
the Section 5 source-cell replacement needs the quantitative moment bound
carried by the same `W`, not merely `MemLp` membership. -/
theorem cutoffRatioSup_le_commonMajorant {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {n m : ℕ} (hnm : n < m)
    (U : Ch02.Domain d) {k : ℤ}
    (hUk : (U : Set (Vec d)) ⊆ openCubeSet (originCube d k))
    {W : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ} (hW0 : ∀ omega, 0 ≤ W omega)
    (hWfwd : ∀ omega,
      cutoffRatioLinfty M m n k omega ≤ ENNReal.ofReal (W omega))
    (hWinv : ∀ omega,
      inverseCutoffRatioLinfty M m n k omega ≤ ENNReal.ofReal (W omega)) :
    (∀ omega, cutoffRatioSup M m n U omega ≤ W omega + 1) ∧
      ∀ omega, cutoffRatioSup M n m U omega ≤ W omega + 1 := by
  have hfwd : ∀ omega, cutoffRatioSup M m n U omega ≤ W omega + 1 := by
    intro omega
    unfold cutoffRatioSup
    apply csSup_le
    · obtain ⟨x, hx⟩ := U.nonempty
      exact ⟨_root_.SubdiffusiveProcess.Model.aCutoff M m omega x /
        _root_.SubdiffusiveProcess.Model.aCutoff M n omega x, x, hx, rfl⟩
    · rintro r ⟨x, hx, rfl⟩
      let xk : {y : Vec d // y ∈ openCubeSet (originCube d k)} := ⟨x, hUk hx⟩
      have hpoint := (le_iSup
        (fun y : {z : Vec d // z ∈ openCubeSet (originCube d k)} => ENNReal.ofReal
          |Real.exp (cutoffShellSum m (n : ℤ) y.1 omega -
            ((m - n : ℕ) : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1|) xk).trans
        (hWfwd omega)
      have habs :
          |Real.exp (cutoffShellSum m (n : ℤ) x omega -
            ((m - n : ℕ) : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1| ≤ W omega :=
        (ENNReal.ofReal_le_ofReal_iff (hW0 omega)).mp hpoint
      have heq := cutoffRatioMinusOne_eq_exp_shell M m (n : ℤ) omega x
        (by omega) (by exact_mod_cast hnm)
      unfold cutoffRatioMinusOne aCutoffAtInt at heq
      have hcast : ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ)) = ((m - n : ℕ) : ℝ) := by
        exact_mod_cast (Int.ofNat_sub hnm.le).symm
      rw [hcast] at heq
      simp only [ite_eq_right (show ¬ (n : ℤ) < 0 by omega), Int.toNat_natCast] at heq
      rw [show _root_.SubdiffusiveProcess.Model.aCutoff M m omega x /
          _root_.SubdiffusiveProcess.Model.aCutoff M n omega x =
          (_root_.SubdiffusiveProcess.Model.aCutoff M m omega x /
            _root_.SubdiffusiveProcess.Model.aCutoff M n omega x - 1) + 1 by ring,
        heq]
      simpa only [add_comm] using add_le_add_right (abs_le.mp habs).2 1
  refine ⟨hfwd, ?_⟩
  intro omega
  unfold cutoffRatioSup
  apply csSup_le
  · obtain ⟨x, hx⟩ := U.nonempty
    exact ⟨_root_.SubdiffusiveProcess.Model.aCutoff M n omega x /
      _root_.SubdiffusiveProcess.Model.aCutoff M m omega x, x, hx, rfl⟩
  · rintro r ⟨x, hx, rfl⟩
    let xk : {y : Vec d // y ∈ openCubeSet (originCube d k)} := ⟨x, hUk hx⟩
    have hpoint := (le_iSup
      (fun y : {z : Vec d // z ∈ openCubeSet (originCube d k)} => ENNReal.ofReal
        |Real.exp (-cutoffShellSum m (n : ℤ) y.1 omega +
          ((m - n : ℕ) : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1|) xk).trans
      (hWinv omega)
    have habs :
        |Real.exp (-cutoffShellSum m (n : ℤ) x omega +
          ((m - n : ℕ) : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1| ≤ W omega :=
      (ENNReal.ofReal_le_ofReal_iff (hW0 omega)).mp hpoint
    have heq := inverseCutoffRatioMinusOne_eq_exp_shell M m (n : ℤ) omega x
      (by omega) (by exact_mod_cast hnm)
    unfold inverseCutoffRatioMinusOne aCutoffAtInt at heq
    have hcast : ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ)) = ((m - n : ℕ) : ℝ) := by
      exact_mod_cast (Int.ofNat_sub hnm.le).symm
    rw [hcast] at heq
    simp only [ite_eq_right (show ¬ (n : ℤ) < 0 by omega), Int.toNat_natCast] at heq
    rw [show _root_.SubdiffusiveProcess.Model.aCutoff M n omega x /
        _root_.SubdiffusiveProcess.Model.aCutoff M m omega x =
        (_root_.SubdiffusiveProcess.Model.aCutoff M n omega x /
          _root_.SubdiffusiveProcess.Model.aCutoff M m omega x - 1) + 1 by ring,
      heq]
    simpa only [add_comm] using add_le_add_right (abs_le.mp habs).2 1

/-- The higher-to-lower cutoff spatial ratio supremum is integrable. -/
theorem integrable_cutoffRatioSup_forward {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {n m : ℕ} (hnm : n < m)
    (U : Ch02.Domain d) :
    Integrable (cutoffRatioSup M m n U) M.P.toMeasure := by
  obtain ⟨k, hUk⟩ := exists_domain_subset_originCube U
  obtain ⟨W, hWm, hW0, hWint, _hWbound, hWfwd, hWinv⟩ :=
    aman_Linfty_moments M m n k hnm 1 le_rfl
  have hWint' : Integrable W M.P.toMeasure := by
    simpa only [Real.rpow_one] using hWint
  have hdom := (cutoffRatioSup_le_commonMajorant M hnm U hUk hW0 hWfwd hWinv).1
  apply (hWint'.add (integrable_const 1)).mono'
    (measurable_cutoffRatioSup M m n U).aestronglyMeasurable
  filter_upwards with omega
  rw [Real.norm_eq_abs, abs_of_pos]
  · exact hdom omega
  · obtain ⟨x, hx⟩ := U.nonempty
    exact lt_of_lt_of_le (div_pos
      (_root_.SubdiffusiveProcess.Model.aCutoff_pos M m omega x)
      (_root_.SubdiffusiveProcess.Model.aCutoff_pos M n omega x))
      (le_csSup (bddAbove_cutoffRatio_range M m n U omega) ⟨x, hx, rfl⟩)

/-- The lower-to-higher cutoff spatial ratio supremum is integrable. -/
theorem integrable_cutoffRatioSup_inverse {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {n m : ℕ} (hnm : n < m)
    (U : Ch02.Domain d) :
    Integrable (cutoffRatioSup M n m U) M.P.toMeasure := by
  obtain ⟨k, hUk⟩ := exists_domain_subset_originCube U
  obtain ⟨W, hWm, hW0, hWint, _hWbound, hWfwd, hWinv⟩ :=
    aman_Linfty_moments M m n k hnm 1 le_rfl
  have hWint' : Integrable W M.P.toMeasure := by
    simpa only [Real.rpow_one] using hWint
  have hdom := (cutoffRatioSup_le_commonMajorant M hnm U hUk hW0 hWfwd hWinv).2
  apply (hWint'.add (integrable_const 1)).mono'
    (measurable_cutoffRatioSup M n m U).aestronglyMeasurable
  filter_upwards with omega
  rw [Real.norm_eq_abs, abs_of_pos]
  · exact hdom omega
  · obtain ⟨x, hx⟩ := U.nonempty
    exact lt_of_lt_of_le (div_pos
      (_root_.SubdiffusiveProcess.Model.aCutoff_pos M n omega x)
      (_root_.SubdiffusiveProcess.Model.aCutoff_pos M m omega x))
      (le_csSup (bddAbove_cutoffRatio_range M n m U omega) ⟨x, hx, rfl⟩)

/-- The higher-to-lower cutoff spatial ratio supremum is square-integrable.

This is the `xi = 2` strengthening of `integrable_cutoffRatioSup_forward`.
It is useful when a spatially continuous cutoff observable is viewed as an
`L²` stationary random variable. -/
theorem memLp_two_cutoffRatioSup_forward {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {n m : ℕ} (hnm : n < m)
    (U : Ch02.Domain d) :
    MemLp (cutoffRatioSup M m n U) 2 M.P.toMeasure := by
  obtain ⟨k, hUk⟩ := exists_domain_subset_originCube U
  obtain ⟨W, _hWm, hW0, hWsq, _hWbound, hWfwd, hWinv⟩ :=
    aman_Linfty_moments M m n k hnm 2 (by norm_num)
  have hdom :=
    (cutoffRatioSup_le_commonMajorant M hnm U hUk hW0 hWfwd hWinv).1
  apply (memLp_two_iff_integrable_sq
    (measurable_cutoffRatioSup M m n U).aestronglyMeasurable).2
  have hmajorant : Integrable (fun omega => 2 * W omega ^ 2 + 2)
      M.P.toMeasure := by
    convert (hWsq.const_mul 2 |>.add (integrable_const 2)) using 1
    ext omega
    simp
  apply hmajorant.mono'
    ((measurable_cutoffRatioSup M m n U).pow_const 2).aestronglyMeasurable
  filter_upwards with omega
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hR0 := (cutoffRatioSup_pos M m n U omega).le
  have hR := hdom omega
  nlinarith [sq_nonneg (W omega - 1)]

/-- The lower-to-higher cutoff spatial ratio supremum is square-integrable. -/
theorem memLp_two_cutoffRatioSup_inverse {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {n m : ℕ} (hnm : n < m)
    (U : Ch02.Domain d) :
    MemLp (cutoffRatioSup M n m U) 2 M.P.toMeasure := by
  obtain ⟨k, hUk⟩ := exists_domain_subset_originCube U
  obtain ⟨W, _hWm, hW0, hWsq, _hWbound, hWfwd, hWinv⟩ :=
    aman_Linfty_moments M m n k hnm 2 (by norm_num)
  have hdom :=
    (cutoffRatioSup_le_commonMajorant M hnm U hUk hW0 hWfwd hWinv).2
  apply (memLp_two_iff_integrable_sq
    (measurable_cutoffRatioSup M n m U).aestronglyMeasurable).2
  have hmajorant : Integrable (fun omega => 2 * W omega ^ 2 + 2)
      M.P.toMeasure := by
    convert (hWsq.const_mul 2 |>.add (integrable_const 2)) using 1
    ext omega
    simp
  apply hmajorant.mono'
    ((measurable_cutoffRatioSup M n m U).pow_const 2).aestronglyMeasurable
  filter_upwards with omega
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hR0 := (cutoffRatioSup_pos M n m U omega).le
  have hR := hdom omega
  nlinarith [sq_nonneg (W omega - 1)]

/-- The higher-to-lower cutoff spatial ratio supremum has the fourth moment
needed by the Section 5 weighted cell-energy factorization. -/
theorem memLp_four_cutoffRatioSup_forward {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {n m : ℕ} (hnm : n < m)
    (U : Ch02.Domain d) :
    MemLp (cutoffRatioSup M m n U) 4 M.P.toMeasure := by
  obtain ⟨k, hUk⟩ := exists_domain_subset_originCube U
  obtain ⟨W, _hWm, hW0, hWfour, _hWbound, hWfwd, hWinv⟩ :=
    aman_Linfty_moments M m n k hnm 4 (by norm_num)
  have hWfour' : Integrable (fun omega ↦ W omega ^ (4 : ℕ))
      M.P.toMeasure := by
    convert hWfour using 1
    funext omega
    exact (Real.rpow_natCast (W omega) 4).symm
  have hmajor : Integrable (fun omega ↦ 8 * (W omega ^ (4 : ℕ) + 1))
      M.P.toMeasure :=
    (hWfour'.add (integrable_const 1)).const_mul 8
  have hdom :=
    (cutoffRatioSup_le_commonMajorant M hnm U hUk hW0 hWfwd hWinv).1
  rw [← integrable_norm_rpow_iff
    (measurable_cutoffRatioSup M m n U).aestronglyMeasurable
    (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ∞)]
  norm_num only [ENNReal.toReal_ofNat]
  apply hmajor.mono'
    ((measurable_cutoffRatioSup M m n U).norm.pow_const 4
      |>.aestronglyMeasurable)
  filter_upwards with omega
  simp only [Real.norm_eq_abs,
    abs_of_pos (cutoffRatioSup_pos M m n U omega)]
  calc
    |cutoffRatioSup M m n U omega ^ (4 : ℝ)| =
        |cutoffRatioSup M m n U omega ^ (4 : ℕ)| := by
      exact congrArg abs (Real.rpow_natCast _ 4)
    _ =
        cutoffRatioSup M m n U omega ^ (4 : ℕ) :=
      abs_of_nonneg (pow_nonneg (cutoffRatioSup_pos M m n U omega).le 4)
    _ ≤ (W omega + 1) ^ (4 : ℕ) :=
      pow_le_pow_left₀ (cutoffRatioSup_pos M m n U omega).le
        (hdom omega) 4
    _ ≤ 8 * (W omega ^ (4 : ℕ) + 1) := by
      have hadd := add_pow_le (hW0 omega) zero_le_one 4
      norm_num at hadd ⊢
      exact hadd

/-- The reciprocal cutoff spatial ratio supremum has the same fourth-moment
integrability. -/
theorem memLp_four_cutoffRatioSup_inverse {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {n m : ℕ} (hnm : n < m)
    (U : Ch02.Domain d) :
    MemLp (cutoffRatioSup M n m U) 4 M.P.toMeasure := by
  obtain ⟨k, hUk⟩ := exists_domain_subset_originCube U
  obtain ⟨W, _hWm, hW0, hWfour, _hWbound, hWfwd, hWinv⟩ :=
    aman_Linfty_moments M m n k hnm 4 (by norm_num)
  have hWfour' : Integrable (fun omega ↦ W omega ^ (4 : ℕ))
      M.P.toMeasure := by
    convert hWfour using 1
    funext omega
    exact (Real.rpow_natCast (W omega) 4).symm
  have hmajor : Integrable (fun omega ↦ 8 * (W omega ^ (4 : ℕ) + 1))
      M.P.toMeasure :=
    (hWfour'.add (integrable_const 1)).const_mul 8
  have hdom :=
    (cutoffRatioSup_le_commonMajorant M hnm U hUk hW0 hWfwd hWinv).2
  rw [← integrable_norm_rpow_iff
    (measurable_cutoffRatioSup M n m U).aestronglyMeasurable
    (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ∞)]
  norm_num only [ENNReal.toReal_ofNat]
  apply hmajor.mono'
    ((measurable_cutoffRatioSup M n m U).norm.pow_const 4
      |>.aestronglyMeasurable)
  filter_upwards with omega
  simp only [Real.norm_eq_abs,
    abs_of_pos (cutoffRatioSup_pos M n m U omega)]
  calc
    |cutoffRatioSup M n m U omega ^ (4 : ℝ)| =
        |cutoffRatioSup M n m U omega ^ (4 : ℕ)| := by
      exact congrArg abs (Real.rpow_natCast _ 4)
    _ =
        cutoffRatioSup M n m U omega ^ (4 : ℕ) :=
      abs_of_nonneg (pow_nonneg (cutoffRatioSup_pos M n m U omega).le 4)
    _ ≤ (W omega + 1) ^ (4 : ℕ) :=
      pow_le_pow_left₀ (cutoffRatioSup_pos M n m U omega).le
        (hdom omega) 4
    _ ≤ 8 * (W omega ^ (4 : ℕ) + 1) := by
      have hadd := add_pow_le (hW0 omega) zero_le_one 4
      norm_num at hadd ⊢
      exact hadd

private theorem inv_cutoffRatioSup_le_reverse {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (numerator denominator : ℕ)
    (U : Ch02.Domain d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    (cutoffRatioSup M numerator denominator U omega)⁻¹ ≤
      cutoffRatioSup M denominator numerator U omega := by
  obtain ⟨x, hx⟩ := U.nonempty
  have hpoint := cutoffRatio_le_cutoffRatioSup M numerator denominator U omega hx
  have hpointPos := div_pos
    (_root_.SubdiffusiveProcess.Model.aCutoff_pos M numerator omega x)
    (_root_.SubdiffusiveProcess.Model.aCutoff_pos M denominator omega x)
  have hsupPos := cutoffRatioSup_pos M numerator denominator U omega
  have hinv : (cutoffRatioSup M numerator denominator U omega)⁻¹ ≤
      (_root_.SubdiffusiveProcess.Model.aCutoff M numerator omega x /
        _root_.SubdiffusiveProcess.Model.aCutoff M denominator omega x)⁻¹ :=
    (inv_le_inv₀ hsupPos hpointPos).2 hpoint
  rw [inv_div] at hinv
  exact hinv.trans (cutoffRatio_le_cutoffRatioSup M denominator numerator U omega hx)

/-- The reciprocal of the higher-to-lower ratio supremum is integrable. -/
theorem integrable_inv_cutoffRatioSup_forward {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {n m : ℕ} (hnm : n < m)
    (U : Ch02.Domain d) :
    Integrable (fun omega => (cutoffRatioSup M m n U omega)⁻¹) M.P.toMeasure := by
  apply (integrable_cutoffRatioSup_inverse M hnm U).mono'
    ((measurable_cutoffRatioSup M m n U).inv.aestronglyMeasurable)
  filter_upwards with omega
  rw [Pi.inv_apply, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (cutoffRatioSup_pos M m n U omega))]
  exact inv_cutoffRatioSup_le_reverse M m n U omega

/-- The reciprocal of the lower-to-higher ratio supremum is integrable. -/
theorem integrable_inv_cutoffRatioSup_inverse {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {n m : ℕ} (hnm : n < m)
    (U : Ch02.Domain d) :
    Integrable (fun omega => (cutoffRatioSup M n m U omega)⁻¹) M.P.toMeasure := by
  apply (integrable_cutoffRatioSup_forward M hnm U).mono'
    ((measurable_cutoffRatioSup M n m U).inv.aestronglyMeasurable)
  filter_upwards with omega
  rw [Pi.inv_apply, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (cutoffRatioSup_pos M n m U omega))]
  exact inv_cutoffRatioSup_le_reverse M n m U omega

end

end SubdiffusiveProcess.CoarseGrainingVocab
