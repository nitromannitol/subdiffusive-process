module

public import SubdiffusiveProcess.Paper.lem_as_regularity_dirichlet_budget_twelve
public import SubdiffusiveProcess.Paper.lem_as_regularity_score_bridge
public import SubdiffusiveProcess.Paper.lem_as_regularity_translate_twelve
public import SubdiffusiveProcess.Paper.lem_as_regularity_trunc_coeff
public import SubdiffusiveProcess.Paper.lem_as_regularity_native_reference
public import SubdiffusiveProcess.Analysis.NativeScoreAllowance

@[expose] public section

/-! Native score budgets give the Dirichlet oscillation estimate for the physical coefficient with
the infrared field truncated at any level `L'`, with constants independent of `L'`.  The genuine
infrared field is reached by the limit `L' → ∞` in `lem_as_regularity_actual_dirichlet`. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set SubdiffusiveProcess SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance
open Homogenization hiding Vec
open Homogenization.Book
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The parameters of the truncated estimate. -/
theorem aux_lem_as_regularity_actual_dirichlet_trunc_params (lam tau : ℝ)
    (hlam : 0 < lam) (htau : 0 < tau) :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 / 64 ∧ eps ≤ tau ∧ ∀ delta : ℝ, 0 ≤ delta → delta ≤ eps →
      64 * delta ^ 2 + eps ^ 8 ≤ min (2 * lam) tau ∧ 32 * delta ^ 2 ≤ tau := by
  refine ⟨min (1 / 64) (min (lam / 40) (tau / 40)),
    lt_min (by norm_num) (lt_min (by positivity) (by positivity)), min_le_left _ _,
    ((min_le_right _ _).trans (min_le_right _ _)).trans (by linarith), ?_⟩
  intro delta hd hde
  set eps := min (1 / 64 : ℝ) (min (lam / 40) (tau / 40)) with heps
  have heps0 : 0 < eps := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have h64 : eps ≤ 1 / 64 := min_le_left _ _
  have hl : eps ≤ lam / 40 := (min_le_right _ _).trans (min_le_left _ _)
  have ht : eps ≤ tau / 40 := (min_le_right _ _).trans (min_le_right _ _)
  have he8 : eps ^ 8 ≤ eps := pow_le_of_le_one heps0.le (by linarith) (by norm_num)
  have hd2 : delta ^ 2 ≤ eps ^ 2 := pow_le_pow_left₀ hd hde 2
  have he2 : eps ^ 2 ≤ eps / 64 := by nlinarith
  have hq : 64 * delta ^ 2 ≤ eps := by nlinarith
  refine ⟨le_min ?_ ?_, by nlinarith⟩
  · nlinarith
  · nlinarith

/-- Native score budgets give the Dirichlet oscillation estimate for the physical coefficient with
the infrared field truncated at `L'`, uniformly in `L'`. -/
theorem lem_as_regularity_actual_dirichlet_trunc (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d,ℝ)] [BorelSpace C(SpatialCoordinates d,ℝ)]
    (_D : lane4_deterministic_good_scale_input d) (rho : ℝ) (hrho : 0 < rho) :
    ∃ eps rate C : ℝ, eps ∈ Ioo (0:ℝ) 1 ∧ 0 < rate ∧ 0 < C ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M), M.delta ≤ eps →
    ∀ (omega : BilateralField d) (N : ℕ) (etaN : _root_.SubdiffusiveProcess.Model.PotentialSample d)
      (Fs Ps Rs Ds : ℕ → Vec d → ℝ≥0∞) (Zs : ℕ → Vec d → ℝ) (goods : ℕ → Vec d → Prop),
      (∀ (i : ℕ) (y : SpatialCoordinates d),
        etaN i y = omega ((i:ℤ)-(N:ℤ)) ((3:ℝ)^(-(N:ℤ)) • y)) →
      primitive_scores d M (1/32) eps etaN Fs Ps Rs Ds Zs goods →
    ∀ L' m n : ℕ, n ≤ m → m ≤ N + L' → ∀ w z0 : SpatialCoordinates d,
      (3:ℝ)^N • (w-z0) ∈ cube d m →
      nativeScoreAllowance (fun j => Zs j ((3:ℝ)^N • w)) (fun j => Ds j ((3:ℝ)^N • w)) m rate
        ≤ m-n →
    ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
      IsDirichletSolutionOn (fun y => cutoffCoefficient M (fun om => infraredPartialSum om L')
        omega N ((3:ℝ)^(-(N:ℤ)) • y+z0)) (originCube d m) u h g →
      (∃ sOrder : FractionalOrder,sOrder.1 = (1/4:ℝ) ∧
        Ch03.ABK26.MemCubeEuclideanFullWsp (originCube d m) sOrder FiniteLpExponent.two g) →
      MemHolder (cube d m) (1/2) g → MemHolder (cube d m) (1/2) h.grad →
      (3:ℝ)^(-((n+2:ℕ):ℤ))*normalizedL2On (truncatedCube d m (n+2:ℕ) ((3:ℝ)^N • (w-z0)))
        (fun x => u.toFun x-averageOn (truncatedCube d m (n+2:ℕ) ((3:ℝ)^N • (w-z0))) u.toFun) ≤
      C*(3:ℝ)^(rho*((m:ℝ)-n))*
        ((3:ℝ)^(-((m-5:ℕ):ℤ))*normalizedL2On (truncatedCube d m (m-5:ℕ) ((3:ℝ)^N • (w-z0)))
          (fun x => u.toFun x-averageOn (truncatedCube d m (m-5:ℕ) ((3:ℝ)^N • (w-z0))) u.toFun) +
          vectorSupNormOn (cube d m) h.grad +
          (aux_in_deterministic_onestep_sref M (fun om => infraredPartialSum om L') omega N
            ((N:ℤ)-m) w)⁻¹ *
            (3:ℝ)^((m:ℝ)/2)*holderSeminormOn (cube d m) (1/2) g +
          (3:ℝ)^((m:ℝ)/2)*holderSeminormOn (cube d m) (1/2) h.grad) := by
  obtain ⟨Cg, hCg, hbridge⟩ := lem_as_regularity_score_bridge d
  obtain ⟨lam, tau, C, hlam, htau, htau1, hC, hiter⟩ :=
    lem_as_regularity_dirichlet_budget_twelve d hd Cg ((12:ℝ)^(-(1/4:ℝ))) rho hCg
      (by positivity) hrho
  obtain ⟨eps, heps0, heps64, hepstau, hpar⟩ :=
    aux_lem_as_regularity_actual_dirichlet_trunc_params lam tau hlam htau
  refine ⟨eps, lam * tau / 2, C, ⟨heps0, by linarith⟩, by positivity, hC, ?_⟩
  intro M Rm hδ omega N etaN Fs Ps Rs Ds Zs goods hEta hPS L' m n hnm hmN w z0 hw hallow u h g
    hsol hg hgh hhh
  have hδ0 : 0 ≤ M.delta := M.shellPrefix.delta_pos.le
  obtain ⟨hbase, h32⟩ := hpar M.delta hδ0 hδ
  have hδ64 : M.delta ≤ 1 / 64 := hδ.trans heps64
  have hδsq : M.delta ^ 2 ≤ 1 / 4096 := by nlinarith
  have hδs : M.delta ≤ Real.sqrt (1 / 32) / 8 := by
    have h1 : (1 / 8 : ℝ) ≤ Real.sqrt (1 / 32) :=
      Real.le_sqrt_of_sq_le (by norm_num)
    linarith
  have htauSq : _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ ((1 / 4 : ℝ) / 8) * Real.log 3 / 16 := by
    have hlog2 : Real.log 2 ≤ 1 :=
      (Real.log_le_sub_one_of_pos (by norm_num)).trans_eq (by norm_num)
    have hh := mul_le_mul_of_nonneg_right hlog2 (sq_nonneg M.delta)
    have h1 : _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ M.delta ^ 2 := by
      linarith only [tauSq_le_delta_sq M, hh, sq_nonneg M.delta]
    have hlog3 : (2 / 3 : ℝ) ≤ Real.log 3 := by
      have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 3 by norm_num)
      linarith
    nlinarith
  obtain ⟨hgap, hfin, hZsum, hDsum⟩ := nativeScoreAllowance_window
    (fun j => Zs j ((3:ℝ)^N • w)) (fun j => Ds j ((3:ℝ)^N • w)) m n (lam * tau / 2) hnm hallow
  set L : ℕ := N + L' with hL
  set z : SpatialCoordinates d := (3:ℝ)^N • (w - z0) with hz
  set ωh : _root_.SubdiffusiveProcess.Model.PotentialSample d :=
    translatePotentialSample ((3:ℝ)^N • z0) etaN with hωh
  set c : ℝ := aux_lem_as_regularity_trunc_coeff_const M omega N L' with hc
  have hcpos : 0 < c := aux_lem_as_regularity_trunc_coeff_const_pos M omega N L'
  have hzc : (3:ℝ)^N • z0 + z = (3:ℝ)^N • w := by
    rw [hz, ← smul_add, add_sub_cancel]
  -- the rescaled Dirichlet problem for the cutoff field
  have hcoef : (fun y => cutoffCoefficient M (fun om => infraredPartialSum om L') omega N
      ((3:ℝ)^(-(N:ℤ)) • y + z0)) = fun y => c * _root_.SubdiffusiveProcess.Model.aCutoff M L ωh y :=
    funext fun y => lem_as_regularity_trunc_coeff M omega N L' etaN hEta z0 y
  rw [hcoef] at hsol
  have hsol' := aux_lem_as_regularity_trunc_coeff_dirichlet_scale hcpos hsol
  have hg' : ∃ sOrder : FractionalOrder, sOrder.1 = (1/4:ℝ) ∧
      Ch03.ABK26.MemCubeEuclideanFullWsp (originCube d m) sOrder FiniteLpExponent.two
        (fun x => c⁻¹ • g x) := by
    obtain ⟨sO, hsO, hfw⟩ := hg
    exact ⟨sO, hsO, aux_lem_as_regularity_trunc_coeff_memFullWsp_smul c⁻¹ hfw⟩
  have hgh' : MemHolder (cube d m) (1/2) (fun x => c⁻¹ • g x) :=
    aux_lem_as_regularity_trunc_coeff_memHolder_smul (inv_nonneg.2 hcpos.le) hgh
  have hgs : holderSeminormOn (cube d m) (1/2) (fun x => c⁻¹ • g x) =
      c⁻¹ * holderSeminormOn (cube d m) (1/2) g :=
    aux_lem_as_regularity_trunc_coeff_holderSeminormOn_smul _ _ (inv_nonneg.2 hcpos.le) g
  have heps1 : eps < 1 := by linarith
  -- good events and errors of the translated native sample
  have hev : ∀ e : ℝ, tau ≤ e → e ≤ 1 → ∀ j : ℕ, j + 2 ≤ m → Zs (j + 2) ((3:ℝ)^N • w) < 1 →
      ωh ∈ _root_.SubdiffusiveProcess.Paper.product_threshold_good_scale d M 12 (some L) (j + 2) z e (1 / 32) := by
    intro e he1 he2 j hj hZ
    have hb := (hbridge M (1 / 32) eps (by norm_num) le_rfl hδs heps1 etaN Fs Ps Rs Ds Zs goods
      hPS L (j + 2) (by omega) ((3:ℝ)^N • w) hZ (hfin _ (by omega))).1 e
      (by linarith) he2
    rw [hωh, lem_as_regularity_translate_twelve, hzc]
    exact hb
  have herr : ∀ j : ℕ, j + 2 ≤ m → Zs (j + 2) ((3:ℝ)^N • w) < 1 →
      section6HomogenizationError M (1 / 32) L (j + 2) ωh z ≤
        Cg * (64 * M.delta ^ 2 + eps ^ 8 + (Ds (j + 2) ((3:ℝ)^N • w)).toReal) := by
    intro j hj hZ
    have hb := (hbridge M (1 / 32) eps (by norm_num) le_rfl hδs heps1 etaN Fs Ps Rs Ds Zs goods
      hPS L (j + 2) (by omega) ((3:ℝ)^N • w) hZ (hfin _ (by omega))).2
    rw [hωh, section6HomogenizationError_translatePotentialSample, hzc]
    have e : 2 * ((1 / 32 : ℝ)⁻¹ * M.delta ^ 2) = 64 * M.delta ^ 2 := by ring
    rw [e] at hb
    exact hb
  have hpos1 : ∀ k : ℕ, 0 < ahom M (min k L) := fun k => ahom_pos M _
  have href : ∀ j : ℕ, 0 < tailCoefficient M L (j + 2) ωh z := fun j =>
    tailCoefficient_pos_of_ahom_pos M L (j + 2) ωh (hpos1 _) z
  have htail : ∀ j : ℕ, j + 2 ≤ m → Zs (j + 2) ((3:ℝ)^N • w) < 1 →
      (12:ℝ)^(-(1/4:ℝ)) * tailCoefficient M L (j + 2) ωh z ≤
        tailAverage M L (j + 2) ωh (translatedCube d ((j : ℤ) + 2) z) := by
    intro j hj hZ
    have h12 := hev tau le_rfl htau1 j hj hZ
    have := lem_as_regularity_tail_reference M (L := L) (m := j + 2) (by omega) ωh z
      (some L) tau (1 / 32) h12
    simpa only [Nat.cast_add, Nat.cast_ofNat] using this
  have htailsref : ∀ k : ℕ, k ≤ L → tailCoefficient M L k ωh z =
      aux_in_deterministic_onestep_sref M (fun om => infraredPartialSum om L') omega N
        ((N:ℤ) - k) w / c := by
    intro k hk
    rw [eq_div_iff hcpos.ne', mul_comm]
    exact aux_lem_as_regularity_trunc_tail M omega N L' k hk etaN hEta z0 w
  have hlen : 0 ≤ (m:ℝ) - n := sub_nonneg.mpr (by exact_mod_cast hnm)
  have hsum : (∑ j ∈ Finset.Icc n m, (Ds j ((3:ℝ)^N • w)).toReal) ≤ lam * ((m:ℝ) - n) := by
    have hh := mul_le_mul_of_nonneg_left htau1 hlam.le
    have hrate : lam * tau / 2 ≤ lam := by nlinarith only [hh, hlam]
    exact hDsum.trans (mul_le_mul_of_nonneg_right hrate hlen)
  have hdl : M.delta ^ 2 ≤ 2 * lam := by
    have := hbase.trans (min_le_left _ _)
    nlinarith [pow_nonneg heps0.le 8, sq_nonneg M.delta]
  have hrat : ∀ j : ℕ, n ≤ j → j + 5 ≤ m →
      tailCoefficient M L (m - 2 + 2) ωh z / tailCoefficient M L (j + 2) ωh z ≤
        Real.exp (4 * (lam * ((m:ℝ) - n))) := by
    intro j hjn hjm
    have hh := lem_as_regularity_native_reference M Rm (fun om => infraredPartialSum om L') omega N
      m n j hjn hjm etaN hEta (1 / 32) eps ⟨by norm_num, by norm_num⟩ Fs Ps Rs Ds Zs goods hPS w
      lam hlam.le hdl hfin hsum
    have hrev := aux_lem_as_regularity_native_reference_reverse _ _ _
      (aux_in_deterministic_onestep_sref_pos M (fun om => infraredPartialSum om L') omega N _ w)
      (aux_in_deterministic_onestep_sref_pos M (fun om => infraredPartialSum om L') omega N _ w) hh
    rw [htailsref (m - 2 + 2) (by omega), htailsref (j + 2) (by omega),
      show m - 2 + 2 = m by omega, div_div_div_cancel_right₀ hcpos.ne']
    exact hrev.2
  have hout := hiter (64 * M.delta ^ 2 + eps ^ 8) (by positivity) hbase M (by nlinarith) h32 htauSq
    L m n hgap z hw ωh (fun j => tailCoefficient M L (j + 2) ωh z)
    (fun j => Zs j ((3:ℝ)^N • w)) (fun j => (Ds j ((3:ℝ)^N • w)).toReal) href
    (fun j => aux_in_deterministic_onestep_Z_nonneg M (1 / 32) eps etaN Fs Ps Rs Ds Zs goods hPS
      j _) (fun j => ENNReal.toReal_nonneg) hZsum hDsum hev herr htail hrat u h
    (fun x => c⁻¹ • g x) hsol' hg' hgh' hhh
  have hrefm : tailCoefficient M L (m - 2 + 2) ωh z =
      aux_in_deterministic_onestep_sref M (fun om => infraredPartialSum om L') omega N
        ((N:ℤ) - m) w / c := by
    rw [show m - 2 + 2 = m by omega]
    exact htailsref m (by omega)
  have hsp := aux_in_deterministic_onestep_sref_pos M (fun om => infraredPartialSum om L') omega N
    ((N:ℤ) - m) w
  have key : (tailCoefficient M L (m - 2 + 2) ωh z)⁻¹ * (3:ℝ)^((m:ℝ)/2) *
      holderSeminormOn (cube d m) (1/2) (fun x => c⁻¹ • g x) =
      (aux_in_deterministic_onestep_sref M (fun om => infraredPartialSum om L') omega N
        ((N:ℤ) - m) w)⁻¹ * (3:ℝ)^((m:ℝ)/2) * holderSeminormOn (cube d m) (1/2) g := by
    rw [hgs, hrefm]
    field_simp
  beta_reduce at hout
  rw [key] at hout
  exact hout

end SubdiffusiveProcess.Paper
