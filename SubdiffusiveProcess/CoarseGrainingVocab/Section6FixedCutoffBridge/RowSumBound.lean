module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.RowMomentBound

@[expose] public section

/-!
# Step 2 of the `L^p` plan: summing the rows

`RowMomentBound.lean` bounds the `L^{2 xi}` moment of one row
`paperScaleResponseAtScale` of the fixed-cutoff response.  Here the rows are
summed against the `geometricWeight` series of `paperHomogenizationErrorFinite`.

The passage from the row bound to the whole series avoids Minkowski's
inequality (whose `tsum` form is not available) by the elementary substitute

    `T l ≤ 3^{s l / 2} * Y`,  `Y := (∑' l, (3^{-s l / 2} T l)^p)^{1/p}`,

which loses only a constant and turns the `1/r`-th root of the series into a
plain product.  The `L^p` size of `Y` is then a *single* `lintegral` of a
`tsum`, evaluated term by term by monotone convergence — never a norm of a
sum.

The surviving `N`-rate is `rho * xi`, with `rho` the dimension-only rate of
`AllScaleProbeMoment.lean`.  The `3^{d l}` cardinality of the descendant family
is beaten by the `xi`-th root of the union bound together with the weight
`3^{-s l xi}`, which is why the auxiliary order `xi` must be large compared
with `d`; that is the standing hypothesis `hgamma`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators ENNReal

noncomputable section

private abbrev S7 (d : ℕ) := _root_.SubdiffusiveProcess.Model.PotentialSample d

variable {d : ℕ}

/-! ## Arithmetic of `Real.rpow` at base three -/

theorem rpow3_nonneg (a : ℝ) : 0 ≤ Real.rpow (3 : ℝ) a :=
  Real.rpow_nonneg (by norm_num) a

theorem rpow3_add (a b : ℝ) :
    Real.rpow (3 : ℝ) a * Real.rpow (3 : ℝ) b = Real.rpow (3 : ℝ) (a + b) :=
  (Real.rpow_add (by norm_num : (0 : ℝ) < 3) a b).symm

theorem rpow3_rpow (a b : ℝ) :
    Real.rpow (Real.rpow (3 : ℝ) a) b = Real.rpow (3 : ℝ) (a * b) :=
  (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) a b).symm

theorem rpow3_npow (a : ℝ) (n : ℕ) :
    (Real.rpow (3 : ℝ) a) ^ n = Real.rpow (3 : ℝ) (a * (n : ℝ)) :=
  (Real.rpow_natCast (Real.rpow (3 : ℝ) a) n).symm.trans (rpow3_rpow a (n : ℝ))

theorem ofReal_rpow3_rpow (a p : ℝ) (hp : 0 ≤ p) :
    (ENNReal.ofReal (Real.rpow (3 : ℝ) a)) ^ p =
      ENNReal.ofReal (Real.rpow (3 : ℝ) (a * p)) :=
  (ENNReal.ofReal_rpow_of_nonneg (rpow3_nonneg a) hp).trans
    (congrArg ENNReal.ofReal (rpow3_rpow a p))

theorem ofReal_rpow3_npow (a : ℝ) (n : ℕ) :
    (ENNReal.ofReal (Real.rpow (3 : ℝ) a)) ^ n =
      ENNReal.ofReal (Real.rpow (3 : ℝ) (a * (n : ℝ))) :=
  (ENNReal.ofReal_pow (rpow3_nonneg a) n).symm.trans
    (congrArg ENNReal.ofReal (rpow3_npow a n))

/-! ## Geometric series in `ℝ≥0∞` -/

theorem ofReal_rpow3_neg_lt_one {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (Real.rpow (3 : ℝ) (-t)) < 1 := by
  have hlt : Real.rpow (3 : ℝ) (-t) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  calc ENNReal.ofReal (Real.rpow (3 : ℝ) (-t))
      < ENNReal.ofReal 1 := (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 hlt
    _ = 1 := by simp

theorem tsum_ofReal_rpow3_geometric (t : ℝ) :
    (∑' l : ℕ, ENNReal.ofReal (Real.rpow (3 : ℝ) (-t * (l : ℝ)))) =
      (1 - ENNReal.ofReal (Real.rpow (3 : ℝ) (-t)))⁻¹ := by
  have hpow : ∀ l : ℕ, ENNReal.ofReal (Real.rpow (3 : ℝ) (-t * (l : ℝ))) =
      (ENNReal.ofReal (Real.rpow (3 : ℝ) (-t))) ^ l := fun l =>
    (ofReal_rpow3_npow (-t) l).symm
  simp only [hpow]
  exact ENNReal.tsum_geometric _

theorem tsum_ofReal_rpow3_geometric_ne_top {t : ℝ} (ht : 0 < t) :
    (∑' l : ℕ, ENNReal.ofReal (Real.rpow (3 : ℝ) (-t * (l : ℝ)))) ≠ ⊤ := by
  rw [tsum_ofReal_rpow3_geometric]
  exact ENNReal.inv_ne_top.2 (tsub_pos_of_lt (ofReal_rpow3_neg_lt_one ht)).ne'

/-! ## The cardinality of a descendant family of the centred cube -/

theorem card_descendantsAtScale_originCube (N l : ℕ) :
    (descendantsAtScale (originCube d ((N : ℤ))) ((N : ℤ) - (l : ℤ))).card =
      (3 ^ d) ^ l := by
  have hscale : (originCube d ((N : ℤ))).scale = (N : ℤ) := rfl
  have hle : ((N : ℤ) - (l : ℤ)) ≤ (originCube d ((N : ℤ))).scale := by
    rw [hscale]; omega
  rw [descendantsAtScale, dite_eq_left hle, hscale]
  have hdepth : ((N : ℤ) - ((N : ℤ) - (l : ℤ))).toNat = l := by omega
  rw [hdepth, descendantsAtDepth_card]

/-! ## The row sum -/

/-- **The `L^{2 xi}` bound for the whole fixed-cutoff response error.**

`rho` is the per-cube decay rate and `Cst` the per-cube constant of
`AllScaleProbeMoment.lean`; the standing inequality `hgamma` is exactly
`s * xi > d + rho * xi`. -/
theorem exists_lintegral_paperHomogenizationError_rpow_le [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) {s r xi rho Cst : ℝ}
    (hs : 0 < s) (hr : 0 < r) (hxi : 1 ≤ xi) (hCst : 0 ≤ Cst)
    (hmom : ∀ R : TriadicCube d,
      lpMoment M.P.toMeasure xi
          (fun omega => finiteProbeSum M L (ahom M L) R omega) ≤
        Cst * Real.rpow (3 : ℝ) (-rho * ((R.scale : ℤ) : ℝ)))
    (hgamma : 0 < s * xi - (d : ℝ) - rho * xi) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ N : ℕ,
      (∫⁻ omega, (paperHomogenizationError (originCube d ((N : ℤ))) ((N : ℤ))
          s .infinity (.finite r) (aCutoffFamily M L omega) (ahom M L)) ^ (2 * xi)
          ∂M.P.toMeasure) ≤
        c * ENNReal.ofReal (Real.rpow (3 : ℝ) (-(rho * xi) * (N : ℝ))) := by
  classical
  have halpha : 0 < ahom M L :=
    (Real.exp_pos _).trans_le
      (_root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M L)
  have hxi0 : (0 : ℝ) < xi := lt_of_lt_of_le zero_lt_one hxi
  have hp0 : (0 : ℝ) < 2 * xi := by linarith
  -- the weight sum `K`
  set K : ℝ≥0∞ := ∑' l : ℕ,
    ENNReal.ofReal (Ch02.geometricWeight s r l *
      Real.rpow (3 : ℝ) (s * r * (l : ℝ) / 2)) with hK
  have hdisc0 : 0 ≤ Ch02.geometricDiscount s r := by
    rw [Ch02.geometricDiscount, sub_nonneg]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by nlinarith)
  have hgw : ∀ l : ℕ, Ch02.geometricWeight s r l *
      Real.rpow (3 : ℝ) (s * r * (l : ℝ) / 2) =
      Ch02.geometricDiscount s r *
        Real.rpow (3 : ℝ) (-(s * r / 2) * (l : ℝ)) := by
    intro l
    have hstep : Real.rpow (3 : ℝ) (-s * r * (l : ℝ)) *
        Real.rpow (3 : ℝ) (s * r * (l : ℝ) / 2) =
        Real.rpow (3 : ℝ) (-(s * r / 2) * (l : ℝ)) := by
      rw [rpow3_add]
      congr 1
      ring_nf
    rw [Ch02.geometricWeight, mul_assoc, hstep]
  have hKtop : K ≠ ⊤ := by
    have hrw : K = ENNReal.ofReal (Ch02.geometricDiscount s r) *
        ∑' l : ℕ, ENNReal.ofReal (Real.rpow (3 : ℝ) (-(s * r / 2) * (l : ℝ))) := by
      rw [hK]
      simp only [hgw]
      rw [← ENNReal.tsum_mul_left]
      exact tsum_congr fun l => ENNReal.ofReal_mul hdisc0
    rw [hrw]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (tsum_ofReal_rpow3_geometric_ne_top (by positivity))
  -- the geometric factor from the `l` sum
  set gamma : ℝ := s * xi - (d : ℝ) - rho * xi with hgammadef
  set Gsum : ℝ≥0∞ :=
    ∑' l : ℕ, ENNReal.ofReal (Real.rpow (3 : ℝ) (-gamma * (l : ℝ))) with hGsum
  have hGtop : Gsum ≠ ⊤ := tsum_ofReal_rpow3_geometric_ne_top hgamma
  refine ⟨K ^ (2 * xi / r) * ENNReal.ofReal (Cst ^ xi) * Gsum, ?_, ?_⟩
  · refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top) hGtop
    exact ENNReal.rpow_ne_top_of_nonneg (by positivity) hKtop
  intro N
  set T : ℕ → S7 d → ℝ≥0∞ := fun l omega =>
    paperScaleResponseAtScale (originCube d ((N : ℤ))) ((N : ℤ) - (l : ℤ))
      .infinity (aCutoffFamily M L omega) (ahom M L) with hT
  set A : ℕ → S7 d → ℝ≥0∞ := fun l omega =>
    ENNReal.ofReal (Real.rpow (3 : ℝ) (-(s / 2) * (l : ℝ))) * T l omega with hA
  set Y : S7 d → ℝ≥0∞ := fun omega =>
    (∑' l : ℕ, (A l omega) ^ (2 * xi)) ^ (2 * xi)⁻¹ with hY
  -- pointwise: every row is dominated by `Y`
  have hrow : ∀ (l : ℕ) (omega : S7 d),
      T l omega ≤
        ENNReal.ofReal (Real.rpow (3 : ℝ) ((s / 2) * (l : ℝ))) * Y omega := by
    intro l omega
    have hterm : (A l omega) ^ (2 * xi) ≤ ∑' j : ℕ, (A j omega) ^ (2 * xi) :=
      ENNReal.le_tsum (f := fun j : ℕ => (A j omega) ^ (2 * xi)) l
    have hAle : A l omega ≤ Y omega := by
      have hstep := ENNReal.rpow_le_rpow hterm (le_of_lt (inv_pos.2 hp0))
      rwa [← ENNReal.rpow_mul, mul_inv_cancel₀ hp0.ne', ENNReal.rpow_one] at hstep
    have hmul := mul_le_mul_right
      hAle (ENNReal.ofReal (Real.rpow (3 : ℝ) ((s / 2) * (l : ℝ))))
    refine le_trans (le_of_eq ?_) hmul
    have hcoef : ENNReal.ofReal (Real.rpow (3 : ℝ) ((s / 2) * (l : ℝ))) *
        ENNReal.ofReal (Real.rpow (3 : ℝ) (-(s / 2) * (l : ℝ))) = 1 := by
      rw [← ENNReal.ofReal_mul (rpow3_nonneg _), rpow3_add]
      have hzero : (s / 2) * (l : ℝ) + -(s / 2) * (l : ℝ) = 0 := by ring
      have h30 : Real.rpow (3 : ℝ) 0 = 1 := Real.rpow_zero 3
      rw [hzero, h30, ENNReal.ofReal_one]
    rw [hA]
    calc T l omega = 1 * T l omega := (one_mul _).symm
      _ = (ENNReal.ofReal (Real.rpow (3 : ℝ) ((s / 2) * (l : ℝ))) *
            ENNReal.ofReal (Real.rpow (3 : ℝ) (-(s / 2) * (l : ℝ)))) *
              T l omega := by rw [hcoef]
      _ = _ := by rw [mul_assoc]
  -- pointwise: the whole series is dominated by `K * Y^r`
  have hbody : ∀ omega : S7 d,
      (∑' l : ℕ, ENNReal.ofReal (Ch02.geometricWeight s r l) *
        (T l omega) ^ r) ≤ K * (Y omega) ^ r := by
    intro omega
    have hstep : ∀ l : ℕ,
        ENNReal.ofReal (Ch02.geometricWeight s r l) * (T l omega) ^ r ≤
          ENNReal.ofReal (Ch02.geometricWeight s r l *
            Real.rpow (3 : ℝ) (s * r * (l : ℝ) / 2)) * (Y omega) ^ r := by
      intro l
      have hpow := ENNReal.rpow_le_rpow (hrow l omega) hr.le
      rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le] at hpow
      have hcoef :
          (ENNReal.ofReal (Real.rpow (3 : ℝ) ((s / 2) * (l : ℝ)))) ^ r =
            ENNReal.ofReal (Real.rpow (3 : ℝ) (s * r * (l : ℝ) / 2)) := by
        rw [ofReal_rpow3_rpow _ _ hr.le]
        congr 1
        ring_nf
      rw [hcoef] at hpow
      calc ENNReal.ofReal (Ch02.geometricWeight s r l) * (T l omega) ^ r
          ≤ ENNReal.ofReal (Ch02.geometricWeight s r l) *
              (ENNReal.ofReal (Real.rpow (3 : ℝ) (s * r * (l : ℝ) / 2)) *
                (Y omega) ^ r) := mul_le_mul_right hpow _
        _ = ENNReal.ofReal (Ch02.geometricWeight s r l *
              Real.rpow (3 : ℝ) (s * r * (l : ℝ) / 2)) * (Y omega) ^ r := by
              rw [ENNReal.ofReal_mul
                (geometricWeight_nonneg_of_nonneg hs.le hr.le l)]
              ring_nf
    refine le_trans (ENNReal.tsum_le_tsum hstep) ?_
    rw [hK, ENNReal.tsum_mul_right]
  -- raise to the power `2 xi`
  have hpointwise : ∀ omega : S7 d,
      (paperHomogenizationError (originCube d ((N : ℤ))) ((N : ℤ))
          s .infinity (.finite r) (aCutoffFamily M L omega) (ahom M L)) ^ (2 * xi) ≤
        K ^ (2 * xi / r) * (∑' l : ℕ, (A l omega) ^ (2 * xi)) := by
    intro omega
    have hdef : paperHomogenizationError (originCube d ((N : ℤ))) ((N : ℤ))
        s .infinity (.finite r) (aCutoffFamily M L omega) (ahom M L) =
        (∑' l : ℕ, ENNReal.ofReal (Ch02.geometricWeight s r l) *
          (T l omega) ^ r) ^ (1 / r) := rfl
    rw [hdef, ← ENNReal.rpow_mul]
    have hexp : (1 / r) * (2 * xi) = 2 * xi / r := by field_simp
    rw [hexp]
    refine le_trans (ENNReal.rpow_le_rpow (hbody omega) (by positivity)) ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 2 * xi / r)]
    refine mul_le_mul_right (le_of_eq ?_) _
    rw [← ENNReal.rpow_mul]
    have hexp2 : r * (2 * xi / r) = 2 * xi := by field_simp
    rw [hexp2, hY, ← ENNReal.rpow_mul, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
  -- integrate
  have hmeasA : ∀ l : ℕ, Measurable fun omega : S7 d => (A l omega) ^ (2 * xi) :=
    fun l => ((measurable_paperScaleResponseAtScale_ambient M L
      (originCube d ((N : ℤ))) ((N : ℤ) - (l : ℤ))).const_mul _).pow_const _
  have hint1 : (∫⁻ omega,
      (paperHomogenizationError (originCube d ((N : ℤ))) ((N : ℤ))
        s .infinity (.finite r) (aCutoffFamily M L omega) (ahom M L)) ^ (2 * xi)
        ∂M.P.toMeasure) ≤
      K ^ (2 * xi / r) * ∑' l : ℕ,
        ∫⁻ omega, (A l omega) ^ (2 * xi) ∂M.P.toMeasure := by
    refine le_trans (lintegral_mono hpointwise) ?_
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg
      (by positivity) hKtop)]
    exact mul_le_mul_right (le_of_eq
      (lintegral_tsum fun l => (hmeasA l).aemeasurable)) _
  refine le_trans hint1 ?_
  -- the per-row estimate
  have hrowint : ∀ l : ℕ,
      (∫⁻ omega, (A l omega) ^ (2 * xi) ∂M.P.toMeasure) ≤
        (ENNReal.ofReal (Cst ^ xi) *
            ENNReal.ofReal (Real.rpow (3 : ℝ) (-(rho * xi) * (N : ℝ)))) *
          ENNReal.ofReal (Real.rpow (3 : ℝ) (-gamma * (l : ℝ))) := by
    intro l
    have hsplit : ∀ omega : S7 d, (A l omega) ^ (2 * xi) =
        ENNReal.ofReal (Real.rpow (3 : ℝ) (-(s * xi) * (l : ℝ))) *
          (T l omega) ^ (2 * xi) := by
      intro omega
      rw [hA, ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ofReal_rpow3_rpow _ _ hp0.le]
      congr 2
      ring_nf
    simp only [hsplit]
    rw [lintegral_const_mul _ ((measurable_paperScaleResponseAtScale_ambient M L
      (originCube d ((N : ℤ))) ((N : ℤ) - (l : ℤ))).pow_const _)]
    have hcard := card_descendantsAtScale_originCube (d := d) N l
    have hAbound : ∀ R ∈ descendantsAtScale (originCube d ((N : ℤ)))
        ((N : ℤ) - (l : ℤ)),
        lpMoment M.P.toMeasure xi
            (fun omega => finiteProbeSum M L (ahom M L) R omega) ≤
          Cst * Real.rpow (3 : ℝ) (-rho * ((N : ℝ) - (l : ℝ))) := by
      intro R hR
      have hscale : R.scale = (N : ℤ) - (l : ℤ) :=
        scale_eq_of_mem_descendantsAtScale hR
      have hbase := hmom R
      rw [hscale] at hbase
      have hcast : ((((N : ℤ) - (l : ℤ)) : ℤ) : ℝ) = (N : ℝ) - (l : ℝ) := by
        push_cast; ring
      rwa [hcast] at hbase
    have hstep := lintegral_paperScaleResponseAtScale_rpow_le M L halpha
      (originCube d ((N : ℤ))) ((N : ℤ) - (l : ℤ)) hxi
      (Cst * Real.rpow (3 : ℝ) (-rho * ((N : ℝ) - (l : ℝ)))) hAbound
    rw [hcard] at hstep
    refine le_trans (mul_le_mul_right hstep _) (le_of_eq ?_)
    have hnat : (((3 ^ d) ^ l : ℕ) : ℝ≥0∞) =
        ENNReal.ofReal (Real.rpow (3 : ℝ) ((d : ℝ) * (l : ℝ))) := by
      have hcast : (((3 ^ d) ^ l : ℕ) : ℝ) =
          Real.rpow (3 : ℝ) ((d : ℝ) * (l : ℝ)) := by
        have h1 : ((3 ^ d : ℕ) : ℝ) = Real.rpow (3 : ℝ) (d : ℝ) := by
          have hc : ((3 ^ d : ℕ) : ℝ) = (3 : ℝ) ^ d := by push_cast; ring
          rw [hc]
          exact (Real.rpow_natCast (3 : ℝ) d).symm
        calc (((3 ^ d) ^ l : ℕ) : ℝ) = ((3 ^ d : ℕ) : ℝ) ^ l := by push_cast; ring
          _ = (Real.rpow (3 : ℝ) (d : ℝ)) ^ l := by rw [h1]
          _ = Real.rpow (3 : ℝ) ((d : ℝ) * (l : ℝ)) := rpow3_npow _ _
      rw [← ENNReal.ofReal_natCast, hcast]
    have hnn2 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((d : ℝ) * (l : ℝ)) := rpow3_nonneg _
    have hnn3 : (0 : ℝ) ≤ Cst ^ xi := Real.rpow_nonneg hCst _
    have hexpsum : Real.rpow (3 : ℝ) (-(s * xi) * (l : ℝ)) *
        Real.rpow (3 : ℝ) ((d : ℝ) * (l : ℝ)) *
        Real.rpow (3 : ℝ) (-rho * ((N : ℝ) - (l : ℝ)) * xi) =
        Real.rpow (3 : ℝ) (-(rho * xi) * (N : ℝ)) *
          Real.rpow (3 : ℝ) (-gamma * (l : ℝ)) := by
      rw [rpow3_add, rpow3_add, rpow3_add]
      congr 1
      rw [hgammadef]
      ring_nf
    have hmulrpow : (Cst * Real.rpow (3 : ℝ) (-rho * ((N : ℝ) - (l : ℝ)))) ^ xi =
        Cst ^ xi * Real.rpow (3 : ℝ) (-rho * ((N : ℝ) - (l : ℝ)) * xi) := by
      rw [Real.mul_rpow hCst (rpow3_nonneg _)]
      exact congrArg (fun t : ℝ => Cst ^ xi * t) (rpow3_rpow _ _)
    have hreal : Real.rpow (3 : ℝ) (-(s * xi) * (l : ℝ)) *
        (Real.rpow (3 : ℝ) ((d : ℝ) * (l : ℝ)) *
          (Cst * Real.rpow (3 : ℝ) (-rho * ((N : ℝ) - (l : ℝ)))) ^ xi) =
        Cst ^ xi * Real.rpow (3 : ℝ) (-(rho * xi) * (N : ℝ)) *
          Real.rpow (3 : ℝ) (-gamma * (l : ℝ)) := by
      rw [hmulrpow]
      calc Real.rpow (3 : ℝ) (-(s * xi) * (l : ℝ)) *
            (Real.rpow (3 : ℝ) ((d : ℝ) * (l : ℝ)) *
              (Cst ^ xi *
                Real.rpow (3 : ℝ) (-rho * ((N : ℝ) - (l : ℝ)) * xi)))
          = Cst ^ xi * (Real.rpow (3 : ℝ) (-(s * xi) * (l : ℝ)) *
              Real.rpow (3 : ℝ) ((d : ℝ) * (l : ℝ)) *
              Real.rpow (3 : ℝ) (-rho * ((N : ℝ) - (l : ℝ)) * xi)) := by ring
        _ = Cst ^ xi * (Real.rpow (3 : ℝ) (-(rho * xi) * (N : ℝ)) *
              Real.rpow (3 : ℝ) (-gamma * (l : ℝ))) := by rw [hexpsum]
        _ = _ := by ring
    rw [hnat, ← ENNReal.ofReal_mul hnn2, ← ENNReal.ofReal_mul (rpow3_nonneg _),
      hreal, ENNReal.ofReal_mul (mul_nonneg hnn3 (rpow3_nonneg _)),
      ENNReal.ofReal_mul hnn3]
  refine le_trans (mul_le_mul_right (ENNReal.tsum_le_tsum hrowint) _) ?_
  rw [ENNReal.tsum_mul_left, ← hGsum]
  exact le_of_eq (by ring)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge
