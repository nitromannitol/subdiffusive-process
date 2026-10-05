module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.StoppedRatio
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ScaleSaturation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.StoppingSaturation

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable


variable {d : ℕ}

/-- **The mixed-regime pointwise `b`-ratio.**  For `q ≤ L` the numerator tail
coefficient is `a_q · (a_L / a_q)` and the saturated denominator is the
deterministic `a_L`, so the quotient is the exponential of the shell block over
the layers `q+1, …, L` together with the annealed-normalizer error.  Only these
layers occur: this is the manuscript's *"only the terms with `j+3 ≤ i ≤ L`
appear"*. -/
theorem tailCoefficient_div_ahom_eq_exp_shellBlock
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L q : ℕ} (hqL : q ≤ L)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Vec d) :
    tailCoefficient M L q omega x / ahom M L =
      Real.exp (shellBlock L q omega x + normalizerLogError M L q) := by
  have hq : (0 : ℝ) < ahom M q := ahom_pos M q
  have hL : (0 : ℝ) < ahom M L := ahom_pos M L
  have hcut := aCutoff_div_eq_exp_shellBlock M hqL omega x
  have hnorm := ahom_ratio_eq_exp_normalizerLogError M L q
  unfold tailCoefficient
  rw [min_eq_left hqL]
  calc
    ahom M q * (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x /
          _root_.SubdiffusiveProcess.Model.aCutoff M q omega x) / ahom M L
        = (ahom M q / ahom M L) *
            (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x /
              _root_.SubdiffusiveProcess.Model.aCutoff M q omega x) := by ring
    _ = Real.exp (_root_.SubdiffusiveProcess.Model.tauSq M.P * ((L - q : ℕ) : ℝ) +
            normalizerLogError M L q) *
          Real.exp (shellBlock L q omega x -
            _root_.SubdiffusiveProcess.Model.tauSq M.P * ((L - q : ℕ) : ℝ)) := by
          rw [hnorm, hcut]
    _ = Real.exp (shellBlock L q omega x + normalizerLogError M L q) := by
          rw [← Real.exp_add]
          congr 1
          ring

/-- **The mixed regime of `e.cutoff.Holder.b.ratio`.**  With the denominator
saturated, the two-sided ratio bound follows from the shell budget and the
annealed-normalizer budget alone; no good event and no parent-suffix comparison
is used. -/
theorem tailAverage_ratio_bounds_of_saturated_budgets
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L q m : ℕ} (hqL : q ≤ L)
    (hLm : L ≤ m) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (z : Vec d) {B R : ℝ}
    (hshell : ∀ x ∈ cube d (q : ℤ),
      |shellBlock L q (translatePotentialSample z omega) x| ≤ B)
    (hrho : |normalizerLogError M L q| ≤ R) :
    tailAverage M L q omega (translatedCube d (q : ℤ) z) /
        tailCoefficientCubeAverage M L m omega ≤ Real.exp (B + R) ∧
      tailCoefficientCubeAverage M L m omega /
        tailAverage M L q omega (translatedCube d (q : ℤ) z) ≤
          Real.exp (B + R) := by
  rw [Section6Cutoff.tailCoefficientCubeAverage_eq_ahom_of_cutoff_le_scale M hLm
    omega]
  let f : Vec d → ℝ := tailCoefficient M L q (translatePotentialSample z omega)
  have hf : Continuous f := continuous_tailCoefficient M L q _
  have hfpos : ∀ x, 0 < f x := fun x =>
    tailCoefficient_pos_of_ahom_pos M L q _ (ahom_pos M (min q L)) x
  have hbound : ∀ x ∈ cube d (q : ℤ),
      shellBlock L q (translatePotentialSample z omega) x +
        normalizerLogError M L q ≤ B + R := by
    intro x hx
    have h1 : shellBlock L q (translatePotentialSample z omega) x ≤ B :=
      (le_abs_self _).trans (hshell x hx)
    have h2 : normalizerLogError M L q ≤ R :=
      (le_abs_self _).trans hrho
    linarith
  have hboundNeg : ∀ x ∈ cube d (q : ℤ),
      -(shellBlock L q (translatePotentialSample z omega) x +
        normalizerLogError M L q) ≤ B + R := by
    intro x hx
    have h1 : -shellBlock L q (translatePotentialSample z omega) x ≤ B :=
      (neg_le_abs _).trans (hshell x hx)
    have h2 : -normalizerLogError M L q ≤ R :=
      (neg_le_abs _).trans hrho
    linarith
  have hpointForward : ∀ x ∈ cube d (q : ℤ), f x / ahom M L ≤ Real.exp (B + R) := by
    intro x hx
    rw [show f x = tailCoefficient M L q (translatePotentialSample z omega) x from rfl,
      tailCoefficient_div_ahom_eq_exp_shellBlock M hqL _ x]
    exact Real.exp_le_exp.mpr (hbound x hx)
  have hpointReverse : ∀ x ∈ cube d (q : ℤ), ahom M L / f x ≤ Real.exp (B + R) := by
    intro x hx
    have hfx : 0 < f x := hfpos x
    have hforward := tailCoefficient_div_ahom_eq_exp_shellBlock M hqL
      (translatePotentialSample z omega) x
    have hinv : ahom M L / f x =
        Real.exp (-(shellBlock L q (translatePotentialSample z omega) x +
          normalizerLogError M L q)) := by
      rw [Real.exp_neg, ← hforward]
      show ahom M L / f x = (f x / ahom M L)⁻¹
      rw [inv_div]
    rw [hinv]
    exact Real.exp_le_exp.mpr (hboundNeg x hx)
  have h := cubeAverage_ratio_bounds_of_pointwise
    (Ch02.cubeDomain (originCube d (q : ℤ)))
    f hf hfpos (tailCoefficientCubeAverage_pos M L q _) hpointForward hpointReverse
  change tailCoefficientCubeAverage M L q (translatePotentialSample z omega) /
      ahom M L ≤ Real.exp (B + R) ∧
    ahom M L /
      tailCoefficientCubeAverage M L q (translatePotentialSample z omega) ≤
        Real.exp (B + R) at h
  rw [Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample] at h
  exact h

/-- **`e.cutoff.Holder.b.ratio`** (`e.cutoff.Holder.b.ratio`): the
stopped coefficient-ratio display at the cutoff good event, with **no relation
between `m` and `L`**.  Both directions are bounded by the manuscript's linear
exponential rate `exp(C lambda (m - n))`, `C = 4d + 3^{s/8} + 1`. -/
theorem stopped_tailAverage_ratio_bounds_exp_cutoff
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L n q m : ℕ}
    (hnm : n < m) (hnq : n ≤ q) (hqm : q ≤ m)
    (epsilon s lambda : ℝ) (hepsilon : 0 ≤ epsilon) (hs : s ≤ 1 / 2)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    (hdelta : M.delta ^ 2 ≤ lambda) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (z : Vec d)
    (hz : z ∈ cube d m)
    (hsumZ : (∑ i ∈ Finset.Icc n m,
      accumulatedError M (some L) i z s omega) ≤
        lambda * ((m : ℝ) - (n : ℝ)))
    (hsum0 : (∑ i ∈ Finset.Icc n m,
      accumulatedError M (some L) i 0 s omega) ≤
        lambda * ((m : ℝ) - (n : ℝ)))
    (hbadZ : (∑ i ∈ Finset.Icc n m,
        (1 - if omega ∈ goodEvent M (some L) i z epsilon s then (1 : ℝ) else 0)) <
      1 + lambda * ((m : ℝ) - (n : ℝ)))
    (hbad0 : (∑ i ∈ Finset.Icc n m,
        (1 - if omega ∈ goodEvent M (some L) i 0 epsilon s then (1 : ℝ) else 0)) <
      1 + lambda * ((m : ℝ) - (n : ℝ))) :
    let C := 4 * (d : ℝ) + ((3 : ℝ) ^ (-(s / 8)))⁻¹ + 1
    tailAverage M L q omega (translatedCube d (q : ℤ) z) /
        tailCoefficientCubeAverage M L m omega ≤
          Real.exp (C * lambda * ((m : ℝ) - (n : ℝ))) ∧
      tailCoefficientCubeAverage M L m omega /
        tailAverage M L q omega (translatedCube d (q : ℤ) z) ≤
          Real.exp (C * lambda * ((m : ℝ) - (n : ℝ))) := by
  dsimp only
  have hgap0 : 0 ≤ (m : ℝ) - (n : ℝ) := by
    have hnmR : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.2 (le_of_lt hnm)
    linarith
  have hE0 : 0 ≤ lambda * ((m : ℝ) - (n : ℝ)) := mul_nonneg hlambda0 hgap0
  rcases le_total L q with hLq | hqL
  · -- Saturated regime: both factors are the deterministic `a_L`.
    have hLm : L ≤ m := hLq.trans hqm
    have hrate : (0 : ℝ) ≤
        (4 * (d : ℝ) + ((3 : ℝ) ^ (-(s / 8)))⁻¹ + 1) * lambda *
          ((m : ℝ) - (n : ℝ)) := by
      have hC : (0 : ℝ) ≤ 4 * (d : ℝ) + ((3 : ℝ) ^ (-(s / 8)))⁻¹ + 1 := by
        have : (0 : ℝ) < (3 : ℝ) ^ (-(s / 8)) := Real.rpow_pos_of_pos (by norm_num) _
        positivity
      rw [mul_assoc]
      exact mul_nonneg hC hE0
    have hone : (1 : ℝ) ≤ Real.exp ((4 * (d : ℝ) + ((3 : ℝ) ^ (-(s / 8)))⁻¹ + 1) *
        lambda * ((m : ℝ) - (n : ℝ))) := Real.one_le_exp hrate
    rw [Section6Cutoff.tailAverage_translatedCube_eq_ahom_of_cutoff_le_scale M hLq
        omega z,
      Section6Cutoff.tailCoefficientCubeAverage_eq_ahom_of_cutoff_le_scale M hLm
        omega,
      div_self (ahom_pos M L).ne']
    exact ⟨hone, hone⟩
  · rcases le_total m L with hmL | hLm
    · -- Below the cutoff: the two stopping carriers agree, so the uncut
      -- estimate applies verbatim.
      have htransport : ∀ y : Vec d,
          (∑ i ∈ Finset.Icc n m, accumulatedError M none i y s omega) =
            ∑ i ∈ Finset.Icc n m, accumulatedError M (some L) i y s omega :=
        fun y => (accumulatedError_sum_some_eq_none_of_le_cutoff M hmL n y s omega).symm
      have hbadTransport : ∀ y : Vec d,
          (∑ i ∈ Finset.Icc n m,
              (1 - if omega ∈ goodEvent M none i y epsilon s then (1 : ℝ) else 0)) =
            ∑ i ∈ Finset.Icc n m,
              (1 - if omega ∈ goodEvent M (some L) i y epsilon s then
                (1 : ℝ) else 0) := by
        intro y
        have hcount := goodEventCount_sum_some_eq_none_of_le_cutoff M hmL n y
          epsilon s omega
        simp only [Finset.sum_sub_distrib, hcount]
      have hraw := Section6Holder.stopped_tailAverage_ratio_bounds_exp M hnm hnq hqm
        hmL epsilon s lambda hepsilon hs hlambda0 hlambda1 hdelta omega z hz
        (by rw [htransport z]; exact hsumZ) (by rw [htransport 0]; exact hsum0)
        (by rw [hbadTransport z]; exact hbadZ) (by rw [hbadTransport 0]; exact hbad0)
      dsimp only at hraw
      exact hraw
    · -- Mixed regime `q ≤ L ≤ m`: only the layers `q+1, …, L` occur.
      have hshellSum : (∑ i ∈ Finset.Icc (q + 1) L,
          accumulatedError M (some L) i z s omega) ≤
            lambda * ((m : ℝ) - (n : ℝ)) := by
        refine le_trans ?_ hsumZ
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          simp only [Finset.mem_Icc] at hi ⊢
          omega
        · intro i _hi _hout
          exact accumulatedError_nonneg M (some L) s i z omega
      have hshell : ∀ x ∈ cube d (q : ℤ),
          |shellBlock L q (translatePotentialSample z omega) x| ≤
            lambda * ((m : ℝ) - (n : ℝ)) / (3 : ℝ) ^ (-(s / 8)) := by
        intro x hx
        have hxtrans : z + x ∈ translatedCube d (q : ℤ) z := ⟨x, hx, rfl⟩
        rw [shellBlock_translatePotentialSample, add_comm]
        exact (abs_shellBlock_le_accumulatedError_sum M (some L) s z omega hxtrans).trans
          (div_le_div_of_nonneg_right hshellSum (by positivity))
      have hlog : Real.log 2 / 2 ≤ 1 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
      have htau : _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ lambda :=
        (tauSq_le_delta_sq M).trans <|
          (mul_le_of_le_one_left (sq_nonneg M.delta) hlog).trans hdelta
      have hgapQ : ((L - q : ℕ) : ℝ) ≤ (m : ℝ) - (n : ℝ) := by
        rw [Nat.cast_sub hqL]
        have hnqR : (n : ℝ) ≤ (q : ℝ) := Nat.cast_le.2 hnq
        have hLmR : (L : ℝ) ≤ (m : ℝ) := Nat.cast_le.2 hLm
        linarith
      have hR : _root_.SubdiffusiveProcess.Model.tauSq M.P * ((L - q : ℕ) : ℝ) ≤
          lambda * ((m : ℝ) - (n : ℝ)) :=
        mul_le_mul htau hgapQ (Nat.cast_nonneg _) hlambda0
      have hrho : |normalizerLogError M L q| ≤
          _root_.SubdiffusiveProcess.Model.tauSq M.P * ((L - q : ℕ) : ℝ) :=
        abs_normalizerLogError_le_of_le M hqL
      have hmixed := tailAverage_ratio_bounds_of_saturated_budgets M hqL hLm omega z
        hshell hrho
      have hP1 : (1 : ℝ) ≤ (1 + (d : ℝ) * (lambda * ((m : ℝ) - (n : ℝ))) *
          Real.exp ((d : ℝ) * (lambda * ((m : ℝ) - (n : ℝ))))) ^ 2 := by
        have hnn : (0 : ℝ) ≤ (d : ℝ) * (lambda * ((m : ℝ) - (n : ℝ))) *
            Real.exp ((d : ℝ) * (lambda * ((m : ℝ) - (n : ℝ)))) :=
          mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hE0) (Real.exp_pos _).le
        nlinarith
      have hcollapse := Section6Holder.stopped_ratio_budget_le_exp (d := d) (s := s)
        (E := lambda * ((m : ℝ) - (n : ℝ)))
        (R := _root_.SubdiffusiveProcess.Model.tauSq M.P * ((L - q : ℕ) : ℝ)) hE0 hR
      have hexpLe : Real.exp (lambda * ((m : ℝ) - (n : ℝ)) / (3 : ℝ) ^ (-(s / 8)) +
            _root_.SubdiffusiveProcess.Model.tauSq M.P * ((L - q : ℕ) : ℝ)) ≤
          Real.exp ((4 * (d : ℝ) + ((3 : ℝ) ^ (-(s / 8)))⁻¹ + 1) * lambda *
            ((m : ℝ) - (n : ℝ))) := by
        refine le_trans ?_ (hcollapse.trans_eq ?_)
        · exact le_mul_of_one_le_left (Real.exp_pos _).le hP1
        · rw [mul_assoc]
      exact ⟨hmixed.1.trans hexpLe, hmixed.2.trans hexpLe⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff
