module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SharpSuffixRepresentative
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SubunitResponse

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory Homogenization Homogenization.Book Homogenization.IndependentSums
open scoped ENNReal

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

variable {d : ℕ}

/-! ## The literal subunit ratio observable -/

/-- Literal ratio-energy carrier of the subunit moment bound for `J`: the
supremum over cutoffs `L ≥ m` and points of the open cube `cu_m` of the
forward-plus-reciprocal deviation of `a_L` from its tail-coefficient cube
average. -/
noncomputable def subunitTailRatioObservable
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ≥0∞ :=
  ⨆ L : {L : ℕ // m ≤ L},
    ⨆ x : {x : Vec d // x ∈ openCubeSet (originCube d (m : ℤ))},
      ENNReal.ofReal
        |_root_.SubdiffusiveProcess.Model.aCutoff M L omega x /
              tailCoefficientCubeAverage M L m omega +
            tailCoefficientCubeAverage M L m omega /
              _root_.SubdiffusiveProcess.Model.aCutoff M L omega x - 2|

/-! ## The absolute cutoff as a shell exponential -/

private theorem cutoffShellIndices_neg_one (m : ℕ) :
    cutoffShellIndices m (-1) = Finset.range (m + 1) := by
  unfold cutoffShellIndices
  ext j
  simp only [Finset.mem_Icc, Finset.mem_range]
  norm_num

/-- The mean-one cutoff is the exponential of its full shell sum minus the
deterministic drift `(m+1) tauSq`. -/
theorem aCutoff_eq_exp_absoluteShellSum
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (x : Vec d) :
    _root_.SubdiffusiveProcess.Model.aCutoff M m omega x =
      Real.exp (cutoffShellSum m (-1) x omega -
        ((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) := by
  unfold _root_.SubdiffusiveProcess.Model.aCutoff cutoffShellSum
  rw [cutoffShellIndices_neg_one]
  congr 1
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
  ring

/-! ## The deterministic normalizer -/

/-- The deterministic drift absorbing the mean-one normalization and the
two-sided bound on the homogenized coefficient. -/
def subunitDrift (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) : ℝ :=
  ((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P

theorem subunitDrift_nonneg (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) :
    0 ≤ subunitDrift M m :=
  mul_nonneg (by positivity) M.G4.tauSq_pos.le

theorem ahom_pos (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) :
    0 < ahom M m :=
  (Real.exp_pos _).trans_le
    (SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower M m)

/-- `e^{-(m+1) tauSq} ≤ ahom_m ≤ 1` bounds the logarithm of the deterministic
normalizer by the drift. -/
theorem abs_ahomShift_le_subunitDrift
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) :
    |((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
        Real.log (ahom M m)| ≤ subunitDrift M m := by
  have hpos := ahom_pos M m
  have hupper : Real.log (ahom M m) ≤ 0 :=
    Real.log_nonpos hpos.le (ahom_le_one M m)
  have hlower : -(((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) ≤
      Real.log (ahom M m) := by
    have hexp := SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower M m
    have := Real.log_le_log (Real.exp_pos _) hexp
    rw [Real.log_exp] at this
    linarith
  rw [abs_le]
  constructor
  · have := subunitDrift_nonneg M m
    unfold subunitDrift
    linarith
  · unfold subunitDrift
    linarith

/-! ## The unit-cube grid covering `cu_m` -/

/-- The measurable envelope of the full shell sum on one unit cube of the
grid covering `cu_m`. -/
def subunitCellEnvelope (m : ℕ) (p : Fin d → ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  smallCubeBlockEnvelope 0 m (0 : ℤ) (physicalShellCoverCenter 0 p) omega

theorem subunitCellEnvelope_nonneg (m : ℕ) (p : Fin d → ℤ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : 0 ≤ subunitCellEnvelope m p omega :=
  smallCubeBlockEnvelope_nonneg _ _ _ _ _

theorem measurable_subunitCellEnvelope (m : ℕ) (p : Fin d → ℤ) :
    Measurable (subunitCellEnvelope (d := d) m p) :=
  measurable_smallCubeBlockEnvelope _ _ _ _

/-- Maximum of the unit-cube envelopes over the grid covering `cu_m`.  The
grid has `O(3^(d m))` cells. -/
def subunitGridEnvelope (m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  (shellCoverShifts d (m : ℤ)).sup' (shellCoverShifts_nonempty d (m : ℤ))
    (fun p => subunitCellEnvelope m p omega)

theorem subunitGridEnvelope_nonneg (m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ subunitGridEnvelope m omega := by
  obtain ⟨p, hp⟩ := shellCoverShifts_nonempty d (m : ℤ)
  exact (subunitCellEnvelope_nonneg m p omega).trans
    (Finset.le_sup' (fun q => subunitCellEnvelope m q omega) hp)

theorem measurable_subunitGridEnvelope (m : ℕ) :
    Measurable (subunitGridEnvelope (d := d) m) := by
  let Y : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ :=
    (shellCoverShifts d (m : ℤ)).sup' (shellCoverShifts_nonempty d (m : ℤ))
      fun p => subunitCellEnvelope m p
  have hY : Measurable Y := Finset.measurable_sup'
    (shellCoverShifts_nonempty d (m : ℤ))
    (fun p _ => measurable_subunitCellEnvelope (d := d) m p)
  have heq : Y = subunitGridEnvelope m := by
    funext omega
    exact Finset.sup'_apply (shellCoverShifts_nonempty d (m : ℤ))
      (fun p => subunitCellEnvelope m p) omega
  rwa [← heq]

/-- Every point of `cu_m` lies in a grid cell, so the grid maximum controls
the full shell sum uniformly on `cu_m`. -/
theorem abs_absoluteShellSum_le_subunitGridEnvelope
    (m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (m : ℤ))) :
    |cutoffShellSum m (-1) x omega| ≤ subunitGridEnvelope m omega := by
  obtain ⟨p, hpFin, hp⟩ :=
    exists_physicalShellCoverCenter_mem (d := d) 0 (m : ℤ) hx
  simp only [Nat.cast_zero, sub_zero] at hpFin hp
  have hlocal := abs_cutoffShellSum_le_smallCubeBlockEnvelope
    (d := d) 0 m (0 : ℤ) (physicalShellCoverCenter 0 p) (by norm_num) omega hp
  simp only [Nat.cast_zero, zero_sub] at hlocal
  exact hlocal.trans
    (Finset.le_sup' (fun q => subunitCellEnvelope m q omega) hpFin)

/-! ## The two-factor exponential majorant -/



def subunitCellMajorant (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ)
    (p : Fin d → ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  Real.exp (subunitCellEnvelope m p omega +
      suffixSensitivityRealRepresentative m (m : ℤ) omega +
      subunitDrift M m) - 1

/-- The grid majorant: the same object with the unit-cube maximum in place of
one cell. -/
def subunitMajorant (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  Real.exp (subunitGridEnvelope m omega +
      suffixSensitivityRealRepresentative m (m : ℤ) omega +
      subunitDrift M m) - 1

private theorem suffixSensitivityRealRepresentative_nonneg (n : ℕ) (k : ℤ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ suffixSensitivityRealRepresentative n k omega :=
  ENNReal.toReal_nonneg

private theorem subunitCellMajorant_nonneg
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (p : Fin d → ℤ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : 0 ≤ subunitCellMajorant M m p omega := by
  unfold subunitCellMajorant
  refine sub_nonneg.mpr (Real.one_le_exp (add_nonneg (add_nonneg ?_ ?_) ?_))
  · exact subunitCellEnvelope_nonneg m p omega
  · exact suffixSensitivityRealRepresentative_nonneg _ _ _
  · exact subunitDrift_nonneg M m

theorem subunitMajorant_nonneg (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : 0 ≤ subunitMajorant M m omega := by
  unfold subunitMajorant
  refine sub_nonneg.mpr (Real.one_le_exp (add_nonneg (add_nonneg ?_ ?_) ?_))
  · exact subunitGridEnvelope_nonneg m omega
  · exact suffixSensitivityRealRepresentative_nonneg _ _ _
  · exact subunitDrift_nonneg M m

theorem measurable_subunitMajorant
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) :
    Measurable (subunitMajorant M m) := by
  unfold subunitMajorant
  have hgrid := measurable_subunitGridEnvelope (d := d) m
  have hsuffix : Measurable (suffixSensitivityRealRepresentative (d := d) m (m : ℤ)) :=
    (measurable_suffixSensitivityRealRepresentative (d := d) m (m : ℤ)).mono
      (potentialShellIndexSigma_le_borel (d := d) (Set.Ioi m)) le_rfl
  exact (((hgrid.add hsuffix).add_const _).exp).sub_const 1

/-- The grid majorant is attained at one cell, so its `q`-th power is below
the sum of the cell powers.  This union bound is where the finite-maximum cost
`exp (d log 3 m / xi)` is paid. -/
theorem subunitMajorant_rpow_le_sum
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (q : ℝ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    subunitMajorant M m omega ^ q ≤
      ∑ p ∈ shellCoverShifts d (m : ℤ), subunitCellMajorant M m p omega ^ q := by
  obtain ⟨p0, hp0mem, hp0⟩ := Finset.exists_mem_eq_sup'
    (shellCoverShifts_nonempty d (m : ℤ))
    (fun p => subunitCellEnvelope m p omega)
  have heq : subunitMajorant M m omega = subunitCellMajorant M m p0 omega := by
    unfold subunitMajorant subunitCellMajorant subunitGridEnvelope
    rw [hp0]
  rw [heq]
  exact Finset.single_le_sum
    (f := fun p => subunitCellMajorant M m p omega ^ q)
    (fun p _ => Real.rpow_nonneg (subunitCellMajorant_nonneg M m p omega) q)
    hp0mem

/-! ## Pathwise domination of the literal observable -/

private theorem abs_ratio_energy_le_of_exp_bounds {R T : ℝ} (hT : 0 ≤ T)
    (hlow : Real.exp (-T) ≤ R) (hup : R ≤ Real.exp T) :
    |R + R⁻¹ - 2| ≤ 2 * (Real.exp T - 1) ^ 2 := by
  have hu1 : (1 : ℝ) ≤ Real.exp T := Real.one_le_exp hT
  have hu0 : (0 : ℝ) < Real.exp T := Real.exp_pos T
  have hlow' : (Real.exp T)⁻¹ ≤ R := by rwa [Real.exp_neg] at hlow
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hlow'
  have huR : 1 ≤ Real.exp T * R := by
    have h := mul_le_mul_of_nonneg_left hlow' hu0.le
    rwa [mul_inv_cancel₀ hu0.ne'] at h
  have hnonneg : 0 ≤ R + R⁻¹ - 2 := by
    have hid : R + R⁻¹ - 2 = (R - 1) ^ 2 / R := by
      field_simp
      ring
    rw [hid]
    positivity
  have hkey : 0 ≤ (Real.exp T - R) * (Real.exp T * R - 1) :=
    mul_nonneg (sub_nonneg.mpr hup) (sub_nonneg.mpr huR)
  have hid2 : Real.exp T + (Real.exp T)⁻¹ - (R + R⁻¹) =
      (Real.exp T - R) * (Real.exp T * R - 1) / (Real.exp T * R) := by
    field_simp
    ring
  have hdiff : 0 ≤ Real.exp T + (Real.exp T)⁻¹ - (R + R⁻¹) := by
    rw [hid2]
    exact div_nonneg hkey (mul_pos hu0 hR0).le
  have hend : Real.exp T + (Real.exp T)⁻¹ - 2 ≤ 2 * (Real.exp T - 1) ^ 2 := by
    have hid : Real.exp T + (Real.exp T)⁻¹ - 2 =
        (Real.exp T - 1) ^ 2 / Real.exp T := by
      field_simp
      ring
    rw [hid, div_le_iff₀ hu0]
    nlinarith [sq_nonneg (Real.exp T - 1)]
  rw [abs_of_nonneg hnonneg]
  linarith



theorem abs_subunitTailRatio_le_subunitMajorant
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hpair : ∀ L : ℕ, m ≤ L → ∀ x y : Vec d,
      x ∈ openCubeSet (originCube d (m : ℤ)) →
      y ∈ openCubeSet (originCube d (m : ℤ)) →
      |(_root_.SubdiffusiveProcess.Model.aCutoff M L omega x /
            _root_.SubdiffusiveProcess.Model.aCutoff M m omega x) /
          (_root_.SubdiffusiveProcess.Model.aCutoff M L omega y /
            _root_.SubdiffusiveProcess.Model.aCutoff M m omega y) - 1| ≤
        cutoffChangeSuffixRepresentative m (m : ℤ) omega)
    {L : ℕ} (hmL : m ≤ L) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (m : ℤ))) :
    |_root_.SubdiffusiveProcess.Model.aCutoff M L omega x /
          tailCoefficientCubeAverage M L m omega +
        tailCoefficientCubeAverage M L m omega /
          _root_.SubdiffusiveProcess.Model.aCutoff M L omega x - 2| ≤
      2 * subunitMajorant M m omega ^ 2 := by
  have hYexp : 1 + cutoffChangeSuffixRepresentative m (m : ℤ) omega =
      Real.exp (suffixSensitivityRealRepresentative m (m : ℤ) omega) := by
    unfold cutoffChangeSuffixRepresentative
    ring
  set U : Ch02.Domain d := Ch02.cubeDomain (originCube d (m : ℤ)) with hU
  set t : Vec d → ℝ := fun y =>
    _root_.SubdiffusiveProcess.Model.aCutoff M L omega y /
      _root_.SubdiffusiveProcess.Model.aCutoff M m omega y with ht
  have hcarrier : (U : Set (Vec d)) = openCubeSet (originCube d (m : ℤ)) :=
    Ch02.cubeDomain_coe _
  have htpos : ∀ y, 0 < t y := fun y =>
    div_pos (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega y)
      (_root_.SubdiffusiveProcess.Model.aCutoff_pos M m omega y)
  have htcont : Continuous t :=
    (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M L omega).div
      (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M m omega)
      (fun y => (_root_.SubdiffusiveProcess.Model.aCutoff_pos M m omega y).ne')
  have hfun : tailCoefficient M L m omega = ahom M m • t := by
    funext y
    unfold tailCoefficient
    rw [min_eq_left hmL]
    simp [ht]
  have havgfactor : tailCoefficientCubeAverage M L m omega =
      ahom M m * Ch02.average U t := by
    unfold tailCoefficientCubeAverage
    rw [hfun]
    change volumeAverage (U : Set (Vec d)) (ahom M m • t) = _
    rw [volumeAverage_smul]
    rfl
  have hahom := ahom_pos M m
  have havgpos : 0 < Ch02.average U t := by
    have hpos := tailCoefficientCubeAverage_pos M L m omega
    rw [havgfactor] at hpos
    nlinarith
  have hpairU : ∀ y ∈ (U : Set (Vec d)), ∀ z ∈ (U : Set (Vec d)),
      |t y / t z - 1| ≤ cutoffChangeSuffixRepresentative m (m : ℤ) omega := by
    intro y hy z hz
    rw [hcarrier] at hy hz
    exact hpair L hmL y z hy hz
  have hxU : x ∈ (U : Set (Vec d)) := by rw [hcarrier]; exact hx
  obtain ⟨hVinv, hV⟩ :=
    tailAverage_ratio_bounds U t htcont htpos hpairU havgpos hxU
  have hVpos : 0 < t x / Ch02.average U t := div_pos (htpos x) havgpos
  have hVupper : t x / Ch02.average U t ≤
      Real.exp (suffixSensitivityRealRepresentative m (m : ℤ) omega) := by
    have := (abs_le.mp hV).2
    rw [← hYexp]
    linarith
  have hVlower :
      Real.exp (-suffixSensitivityRealRepresentative m (m : ℤ) omega) ≤
        t x / Ch02.average U t := by
    have hb2 := (abs_le.mp hVinv).2
    have hle : Ch02.average U t / t x ≤
        Real.exp (suffixSensitivityRealRepresentative m (m : ℤ) omega) := by
      rw [← hYexp]
      linarith
    rw [div_le_iff₀ (htpos x)] at hle
    rw [le_div_iff₀ havgpos]
    have hmul := mul_le_mul_of_nonneg_left hle
      (Real.exp_pos (-suffixSensitivityRealRepresentative m (m : ℤ) omega)).le
    rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      one_mul] at hmul
    linarith
  have hSG : |cutoffShellSum m (-1) x omega| ≤ subunitGridEnvelope m omega :=
    abs_absoluteShellSum_le_subunitGridEnvelope m omega hx
  have hcb := abs_ahomShift_le_subunitDrift M m
  have hUfactor : _root_.SubdiffusiveProcess.Model.aCutoff M m omega x / ahom M m =
      Real.exp (cutoffShellSum m (-1) x omega -
        (((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
          Real.log (ahom M m))) := by
    rw [aCutoff_eq_exp_absoluteShellSum M m omega x,
      show (cutoffShellSum m (-1) x omega -
          (((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
            Real.log (ahom M m))) =
        (cutoffShellSum m (-1) x omega -
          ((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) -
          Real.log (ahom M m) by ring,
      ]
    rw [Real.exp_sub (cutoffShellSum m (-1) x omega -
      ((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) (Real.log (ahom M m)),
      Real.exp_log hahom]
  have hZV0 : (0 : ℝ) ≤ suffixSensitivityRealRepresentative m (m : ℤ) omega :=
    suffixSensitivityRealRepresentative_nonneg _ _ _
  have hG0 : 0 ≤ subunitGridEnvelope m omega := subunitGridEnvelope_nonneg m omega
  have hb0 : 0 ≤ subunitDrift M m := subunitDrift_nonneg M m
  have hT0 : (0 : ℝ) ≤ subunitGridEnvelope m omega +
      suffixSensitivityRealRepresentative m (m : ℤ) omega +
      subunitDrift M m := by linarith
  have hRfactor : _root_.SubdiffusiveProcess.Model.aCutoff M L omega x /
        tailCoefficientCubeAverage M L m omega =
      (_root_.SubdiffusiveProcess.Model.aCutoff M m omega x / ahom M m) *
        (t x / Ch02.average U t) := by
    rw [havgfactor, ht]
    have h1 := (_root_.SubdiffusiveProcess.Model.aCutoff_pos M m omega x).ne'
    have h2 := havgpos.ne'
    have h3 := hahom.ne'
    field_simp
  have hRupper : _root_.SubdiffusiveProcess.Model.aCutoff M L omega x /
        tailCoefficientCubeAverage M L m omega ≤
      Real.exp (subunitGridEnvelope m omega +
        suffixSensitivityRealRepresentative m (m : ℤ) omega +
        subunitDrift M m) := by
    rw [hRfactor, hUfactor]
    have h1 : Real.exp (cutoffShellSum m (-1) x omega -
        (((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
          Real.log (ahom M m))) ≤
        Real.exp (subunitGridEnvelope m omega + subunitDrift M m) := by
      apply Real.exp_le_exp.mpr
      linarith [(abs_le.mp hSG).2, (abs_le.mp hcb).1]
    calc
      _ ≤ Real.exp (subunitGridEnvelope m omega + subunitDrift M m) *
            Real.exp (suffixSensitivityRealRepresentative m (m : ℤ) omega) :=
        mul_le_mul h1 hVupper hVpos.le (Real.exp_pos _).le
      _ = _ := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hRlower : Real.exp (-(subunitGridEnvelope m omega +
        suffixSensitivityRealRepresentative m (m : ℤ) omega +
        subunitDrift M m)) ≤
      _root_.SubdiffusiveProcess.Model.aCutoff M L omega x /
        tailCoefficientCubeAverage M L m omega := by
    rw [hRfactor, hUfactor]
    have h1 : Real.exp (-(subunitGridEnvelope m omega + subunitDrift M m)) ≤
        Real.exp (cutoffShellSum m (-1) x omega -
          (((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
            Real.log (ahom M m))) := by
      apply Real.exp_le_exp.mpr
      linarith [(abs_le.mp hSG).1, (abs_le.mp hcb).2]
    calc
      Real.exp (-(subunitGridEnvelope m omega +
            suffixSensitivityRealRepresentative m (m : ℤ) omega +
            subunitDrift M m)) =
          Real.exp (-(subunitGridEnvelope m omega + subunitDrift M m)) *
            Real.exp (-suffixSensitivityRealRepresentative m (m : ℤ) omega) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := mul_le_mul h1 hVlower (Real.exp_pos _).le (Real.exp_pos _).le
  have hinvform : tailCoefficientCubeAverage M L m omega /
      _root_.SubdiffusiveProcess.Model.aCutoff M L omega x =
        (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x /
          tailCoefficientCubeAverage M L m omega)⁻¹ := by
    rw [inv_div]
  rw [hinvform]
  have hfinal := abs_ratio_energy_le_of_exp_bounds hT0 hRlower hRupper
  have hmaj : subunitMajorant M m omega =
      Real.exp (subunitGridEnvelope m omega +
        suffixSensitivityRealRepresentative m (m : ℤ) omega +
        subunitDrift M m) - 1 := rfl
  rw [hmaj]
  exact hfinal

/-- Almost sure `ENNReal` form of the pathwise domination. -/
theorem ae_subunitTailRatioObservable_le
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) :
    ∀ᵐ omega ∂M.P.toMeasure,
      subunitTailRatioObservable M m omega ≤
        ENNReal.ofReal (2 * subunitMajorant M m omega ^ 2) := by
  filter_upwards
    [ae_tailCutoff_pair_ratio_le_cutoffChangeSuffixRepresentative M m]
    with omega hpair
  refine iSup_le fun L => iSup_le fun x => ENNReal.ofReal_le_ofReal ?_
  exact abs_subunitTailRatio_le_subunitMajorant M m omega hpair L.2 x.2

/-! ## The weak tail of the two-factor envelope -/

/-- Dimension-free constant in the unit-cube block scale. -/
def subunitBlockConst : ℝ := 3 * smallCubeBlockConst

theorem subunitBlockConst_pos : 0 < subunitBlockConst :=
  mul_pos (by norm_num) smallCubeBlockConst_pos

theorem smallCubeBlockScale_pos (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {lower upper : ℕ} (hlu : lower ≤ upper) (r : ℤ) :
    0 < smallCubeBlockScale M lower upper r := by
  unfold smallCubeBlockScale
  refine mul_pos gammaTriangleConst_pos (add_pos ?_ ?_)
  · exact mul_pos (mul_pos cutoffGammaConst_pos
      (Real.sqrt_pos.mpr (by positivity))) M.shellPrefix.delta_pos
  · exact mul_pos gammaTriangleConst_pos
      (Finset.sum_pos (fun j _ => translatedSmallShellScale_pos M j r)
        (Finset.nonempty_Icc.mpr hlu))

/-- On the unit-cube grid the own-scale block estimate loses only the factor
`3` relative to the scale-`-1` version proved in `ShellSensitivity`. -/
theorem smallCubeBlockScale_unit_le (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (m : ℕ) :
    smallCubeBlockScale M 0 m (0 : ℤ) ≤
      subunitBlockConst * Real.sqrt ((m : ℝ) + 1) * M.delta := by
  have hshift : ∀ j : ℕ, translatedSmallShellScale M j (0 : ℤ) =
      3 * translatedSmallShellScale M j (((0 : ℕ) : ℤ) - 1) := by
    intro j
    unfold translatedSmallShellScale
    rw [show ((0 : ℤ) - (j : ℤ)) = 1 + ((((0 : ℕ) : ℤ) - 1) - (j : ℤ)) by
      push_cast; ring, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
    ring
  have hsum : ∑ j ∈ Finset.Icc 0 m, translatedSmallShellScale M j (0 : ℤ) =
      3 * ∑ j ∈ Finset.Icc 0 m,
        translatedSmallShellScale M j (((0 : ℕ) : ℤ) - 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => hshift j
  have hown := smallCubeBlockScale_ownScale_le M 0 m
  have hP : 0 ≤ cutoffGammaConst * Real.sqrt ((m - 0 + 1 : ℕ) : ℝ) * M.delta :=
    mul_nonneg (mul_nonneg cutoffGammaConst_pos.le (Real.sqrt_nonneg _))
      M.shellPrefix.delta_pos.le
  have hS : 0 ≤ ∑ j ∈ Finset.Icc 0 m,
      translatedSmallShellScale M j (((0 : ℕ) : ℤ) - 1) :=
    Finset.sum_nonneg fun j _ => (translatedSmallShellScale_pos M j _).le
  have hgamma : (0 : ℝ) ≤ gammaTriangleConst 2 := gammaTriangleConst_pos.le
  have hstep : smallCubeBlockScale M 0 m (0 : ℤ) ≤
      3 * smallCubeBlockScale M 0 m (((0 : ℕ) : ℤ) - 1) := by
    unfold smallCubeBlockScale
    rw [hsum]
    nlinarith [mul_nonneg hgamma hP]
  have hcast : ((m - 0 + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by
    rw [Nat.sub_zero]
    push_cast
    ring
  rw [hcast] at hown
  calc
    smallCubeBlockScale M 0 m (0 : ℤ) ≤
        3 * smallCubeBlockScale M 0 m (((0 : ℕ) : ℤ) - 1) := hstep
    _ ≤ 3 * (smallCubeBlockConst * Real.sqrt ((m : ℝ) + 1) * M.delta) := by
      linarith
    _ = subunitBlockConst * Real.sqrt ((m : ℝ) + 1) * M.delta := by
      unfold subunitBlockConst
      ring

/-- Dimensional constant in the joint weak tail of the two envelopes. -/
def subunitScaleConst (d : ℕ) : ℝ :=
  gammaTriangleConst 2 * (subunitBlockConst + shellSensitivityConst d)

theorem subunitScaleConst_pos (d : ℕ) : 0 < subunitScaleConst d :=
  mul_pos gammaTriangleConst_pos
    (add_pos subunitBlockConst_pos (shellSensitivityConst_pos d))



def subunitScale (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) : ℝ :=
  subunitScaleConst d * M.delta * Real.sqrt ((m : ℝ) + 1)

theorem subunitScale_pos (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) :
    0 < subunitScale M m :=
  mul_pos (mul_pos (subunitScaleConst_pos d) M.shellPrefix.delta_pos)
    (Real.sqrt_pos.mpr (by positivity))

private theorem one_le_sqrt_succ (m : ℕ) : (1 : ℝ) ≤ Real.sqrt ((m : ℝ) + 1) := by
  have h0 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  nlinarith [Real.sq_sqrt h0, Real.sqrt_nonneg ((m : ℝ) + 1)]

theorem isBigOWith_gammaTwo_subunitCellSum
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (p : Fin d → ℤ) :
    IsBigOWith M.P.toMeasure (gammaSigma 2)
      (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => subunitCellEnvelope m p omega +
        suffixSensitivityRealRepresentative m (m : ℤ) omega)
      (subunitScale M m) := by
  have hblock : IsBigOWith M.P.toMeasure (gammaSigma 2)
      (subunitCellEnvelope (d := d) m p) (smallCubeBlockScale M 0 m (0 : ℤ)) :=
    isBigOWith_gammaTwo_smallCubeBlockEnvelope M 0 m (0 : ℤ)
      (physicalShellCoverCenter 0 p) (Nat.zero_le m)
  have hfield : IsBigOWith M.P.toMeasure (gammaSigma 2)
      (sensitivityFieldRepresentative (d := d) m (m : ℤ))
      (shellSensitivityConst d * M.delta) := by
    have h := isBigOWith_gammaTwo_sensitivityFieldRepresentative M m (m : ℤ)
    simpa using h
  have hsuffix : IsBigOWith M.P.toMeasure (gammaSigma 2)
      (suffixSensitivityRealRepresentative (d := d) m (m : ℤ))
      (shellSensitivityConst d * M.delta) :=
    Ch04.isBigOWith_of_ae_le hfield
      ((ae_suffixSensitivityRealRepresentative_eq_sensitivityFieldRepresentative
        M m (m : ℤ)).le)
  have hmeasSuffix : Measurable
      (suffixSensitivityRealRepresentative (d := d) m (m : ℤ)) :=
    (measurable_suffixSensitivityRealRepresentative (d := d) m (m : ℤ)).mono
      (potentialShellIndexSigma_le_borel (d := d) (Set.Ioi m)) le_rfl
  have hA1 : 0 < smallCubeBlockScale M 0 m (0 : ℤ) :=
    smallCubeBlockScale_pos M (Nat.zero_le m) (0 : ℤ)
  have hA2 : 0 < shellSensitivityConst d * M.delta :=
    mul_pos (shellSensitivityConst_pos d) M.shellPrefix.delta_pos
  have hsum := isBigOWith_gammaTwo_add_nonneg M
    (measurable_subunitCellEnvelope (d := d) m p) hmeasSuffix
    (subunitCellEnvelope_nonneg m p)
    (suffixSensitivityRealRepresentative_nonneg (d := d) m (m : ℤ))
    hA1 hA2 hblock hsuffix
  refine hsum.mono_scale ?_
  have hblockle := smallCubeBlockScale_unit_le M m
  have hsqrt := one_le_sqrt_succ m
  have hdelta := M.shellPrefix.delta_pos.le
  have hsens := (shellSensitivityConst_pos d).le
  have hgamma : (0 : ℝ) ≤ gammaTriangleConst 2 := gammaTriangleConst_pos.le
  have h1 : shellSensitivityConst d * M.delta ≤
      shellSensitivityConst d * M.delta * Real.sqrt ((m : ℝ) + 1) :=
    le_mul_of_one_le_right (mul_nonneg hsens hdelta) hsqrt
  unfold subunitScale subunitScaleConst
  calc
    gammaTriangleConst 2 *
        (smallCubeBlockScale M 0 m (0 : ℤ) + shellSensitivityConst d * M.delta) ≤
        gammaTriangleConst 2 *
          (subunitBlockConst * Real.sqrt ((m : ℝ) + 1) * M.delta +
            shellSensitivityConst d * M.delta * Real.sqrt ((m : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left (add_le_add hblockle h1) hgamma
    _ = gammaTriangleConst 2 * (subunitBlockConst + shellSensitivityConst d) *
        M.delta * Real.sqrt ((m : ℝ) + 1) := by ring

/-! ## The per-cell lognormal moment -/

theorem subunitCellMajorant_moment
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (p : Fin d → ℤ)
    {q : ℝ} (hq : 1 ≤ q) :
    Integrable (fun omega => subunitCellMajorant M m p omega ^ q)
        M.P.toMeasure ∧
      (∫ omega, subunitCellMajorant M m p omega ^ q ∂M.P.toMeasure) ^ q⁻¹ ≤
        2 * gammaMomentConst 2 * Real.sqrt (2 * q) *
          (subunitScale M m + subunitDrift M m) *
          Real.exp (q * subunitScale M m ^ 2 + subunitDrift M m) := by
  have hX0 : ∀ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, 0 ≤ subunitCellEnvelope m p omega +
      suffixSensitivityRealRepresentative m (m : ℤ) omega := fun omega =>
    add_nonneg (subunitCellEnvelope_nonneg m p omega)
      (suffixSensitivityRealRepresentative_nonneg _ _ _)
  have hXm : Measurable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      subunitCellEnvelope m p omega +
        suffixSensitivityRealRepresentative m (m : ℤ) omega) :=
    (measurable_subunitCellEnvelope (d := d) m p).add
      ((measurable_suffixSensitivityRealRepresentative (d := d) m (m : ℤ)).mono
        (potentialShellIndexSigma_le_borel (d := d) (Set.Ioi m)) le_rfl)
  have hbig : IsBigO M.P.toMeasure (gammaSigma 2)
      (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => subunitCellEnvelope m p omega +
        suffixSensitivityRealRepresentative m (m : ℤ) omega)
      (subunitScale M m) := by
    simpa [IsBigO, abs_of_nonneg (hX0 _)] using
      isBigOWith_gammaTwo_subunitCellSum M m p
  have htransfer := integral_abs_exp_sub_const_sub_one_rpow_root_le
    (mu := M.P.toMeasure)
    (X := fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => subunitCellEnvelope m p omega +
      suffixSensitivityRealRepresentative m (m : ℤ) omega)
    (A := subunitScale M m) (p := q) (b := -subunitDrift M m)
    (subunitScale_pos M m) hq hXm.aemeasurable hbig
  have hnn : ∀ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, 0 ≤ Real.exp (subunitCellEnvelope m p omega +
      suffixSensitivityRealRepresentative m (m : ℤ) omega +
      subunitDrift M m) - 1 := fun omega =>
    sub_nonneg.mpr (Real.one_le_exp
      (add_nonneg (hX0 omega) (subunitDrift_nonneg M m)))
  have hfun : (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => subunitCellMajorant M m p omega ^ q) =
      fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => |Real.exp ((subunitCellEnvelope m p omega +
        suffixSensitivityRealRepresentative m (m : ℤ) omega) -
          -subunitDrift M m) - 1| ^ q := by
    funext omega
    rw [sub_neg_eq_add, abs_of_nonneg (hnn omega)]
    rfl
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact htransfer.1
  · rw [hfun]
    simpa only [abs_neg, abs_of_nonneg (subunitDrift_nonneg M m)] using
      htransfer.2

/-! ## The grid cardinality -/

theorem card_shellCoverShifts_subunit_le (d m : ℕ) :
    (((shellCoverShifts d (m : ℤ)).card : ℕ) : ℝ) ≤ (3 : ℝ) ^ ((m + 2) * d) := by
  have hrad : shellCoverRadius (m : ℤ) = 3 ^ (m + 1) := by
    unfold shellCoverRadius
    congr 1
  have hbase : 2 * 3 ^ (m + 1) + 1 ≤ 3 ^ (m + 2) := by
    have h3 : (1 : ℕ) ≤ 3 ^ m := Nat.one_le_pow _ _ (by norm_num)
    have e1 : 3 ^ (m + 1) = 3 ^ m * 3 := pow_succ 3 m
    have e2 : (3 : ℕ) ^ (m + 2) = 3 ^ m * 9 := by
      rw [pow_add]
      norm_num
    omega
  have hnat : (shellCoverShifts d (m : ℤ)).card ≤ 3 ^ ((m + 2) * d) := by
    rw [card_shellCoverShifts, hrad, pow_mul]
    exact Nat.pow_le_pow_left hbase d
  exact_mod_cast hnat

/-! ## The grid maximum moment -/

theorem subunitMajorant_moment
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) {q : ℝ} (hq : 1 ≤ q) :
    Integrable (fun omega => subunitMajorant M m omega ^ q) M.P.toMeasure ∧
      (∫ omega, subunitMajorant M m omega ^ q ∂M.P.toMeasure) ^ q⁻¹ ≤
        ((3 : ℝ) ^ ((m + 2) * d)) ^ q⁻¹ *
          (2 * gammaMomentConst 2 * Real.sqrt (2 * q) *
            (subunitScale M m + subunitDrift M m) *
            Real.exp (q * subunitScale M m ^ 2 + subunitDrift M m)) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  set B : ℝ := 2 * gammaMomentConst 2 * Real.sqrt (2 * q) *
    (subunitScale M m + subunitDrift M m) *
    Real.exp (q * subunitScale M m ^ 2 + subunitDrift M m) with hBdef
  have hB0 : 0 ≤ B := by
    have h1 : 0 < gammaMomentConst 2 := gammaMomentConst_pos (by norm_num)
    have h2 : 0 ≤ subunitScale M m + subunitDrift M m :=
      add_nonneg (subunitScale_pos M m).le (subunitDrift_nonneg M m)
    have h3 : (0 : ℝ) ≤ Real.sqrt (2 * q) := Real.sqrt_nonneg _
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (by norm_num) h1.le) h3) h2) (Real.exp_pos _).le
  have hcell : ∀ p : Fin d → ℤ,
      Integrable (fun omega => subunitCellMajorant M m p omega ^ q)
          M.P.toMeasure ∧
        (∫ omega, subunitCellMajorant M m p omega ^ q ∂M.P.toMeasure) ≤
          B ^ q := by
    intro p
    obtain ⟨hint, hbd⟩ := subunitCellMajorant_moment M m p hq
    refine ⟨hint, ?_⟩
    have hI0 : 0 ≤ ∫ omega, subunitCellMajorant M m p omega ^ q ∂M.P.toMeasure :=
      integral_nonneg fun omega =>
        Real.rpow_nonneg (subunitCellMajorant_nonneg M m p omega) q
    calc
      ∫ omega, subunitCellMajorant M m p omega ^ q ∂M.P.toMeasure =
          ((∫ omega, subunitCellMajorant M m p omega ^ q ∂M.P.toMeasure) ^ q⁻¹)
            ^ q := by
        rw [← Real.rpow_mul hI0, inv_mul_cancel₀ hq0.ne', Real.rpow_one]
      _ ≤ B ^ q := Real.rpow_le_rpow (Real.rpow_nonneg hI0 _) hbd hq0.le
  have hsumint : Integrable (fun omega => ∑ p ∈ shellCoverShifts d (m : ℤ),
      subunitCellMajorant M m p omega ^ q) M.P.toMeasure :=
    integrable_finsetSum _ fun p _ => (hcell p).1
  have hmeas : AEStronglyMeasurable
      (fun omega => subunitMajorant M m omega ^ q) M.P.toMeasure :=
    (((Real.continuous_rpow_const hq0.le).measurable).comp
      (measurable_subunitMajorant M m)).aestronglyMeasurable
  have hGint : Integrable (fun omega => subunitMajorant M m omega ^ q)
      M.P.toMeasure := by
    refine Integrable.mono' hsumint hmeas ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (subunitMajorant_nonneg M m omega) q)]
    exact subunitMajorant_rpow_le_sum M m q omega
  have hI0 : 0 ≤ ∫ omega, subunitMajorant M m omega ^ q ∂M.P.toMeasure :=
    integral_nonneg fun omega =>
      Real.rpow_nonneg (subunitMajorant_nonneg M m omega) q
  have hIle : (∫ omega, subunitMajorant M m omega ^ q ∂M.P.toMeasure) ≤
      (3 : ℝ) ^ ((m + 2) * d) * B ^ q := by
    have hstep1 : (∫ omega, subunitMajorant M m omega ^ q ∂M.P.toMeasure) ≤
        ∫ omega, (∑ p ∈ shellCoverShifts d (m : ℤ),
          subunitCellMajorant M m p omega ^ q) ∂M.P.toMeasure :=
      integral_mono hGint hsumint fun omega =>
        subunitMajorant_rpow_le_sum M m q omega
    have hstep2 : (∫ omega, (∑ p ∈ shellCoverShifts d (m : ℤ),
        subunitCellMajorant M m p omega ^ q) ∂M.P.toMeasure) =
        ∑ p ∈ shellCoverShifts d (m : ℤ),
          ∫ omega, subunitCellMajorant M m p omega ^ q ∂M.P.toMeasure :=
      integral_finsetSum _ fun p _ => (hcell p).1
    have hstep3 : (∑ p ∈ shellCoverShifts d (m : ℤ),
        ∫ omega, subunitCellMajorant M m p omega ^ q ∂M.P.toMeasure) ≤
        ((shellCoverShifts d (m : ℤ)).card : ℝ) * B ^ q := by
      calc
        _ ≤ ∑ _p ∈ shellCoverShifts d (m : ℤ), B ^ q :=
          Finset.sum_le_sum fun p _ => (hcell p).2
        _ = ((shellCoverShifts d (m : ℤ)).card : ℝ) * B ^ q := by
          rw [Finset.sum_const, nsmul_eq_mul]
    have hcard := card_shellCoverShifts_subunit_le d m
    have hBq : 0 ≤ B ^ q := Real.rpow_nonneg hB0 q
    calc
      _ ≤ _ := hstep1
      _ = _ := hstep2
      _ ≤ ((shellCoverShifts d (m : ℤ)).card : ℝ) * B ^ q := hstep3
      _ ≤ (3 : ℝ) ^ ((m + 2) * d) * B ^ q := by
        exact mul_le_mul_of_nonneg_right hcard hBq
  refine ⟨hGint, ?_⟩
  have hpow0 : (0 : ℝ) ≤ (3 : ℝ) ^ ((m + 2) * d) := by positivity
  calc
    (∫ omega, subunitMajorant M m omega ^ q ∂M.P.toMeasure) ^ q⁻¹ ≤
        ((3 : ℝ) ^ ((m + 2) * d) * B ^ q) ^ q⁻¹ :=
      Real.rpow_le_rpow hI0 hIle (by positivity)
    _ = ((3 : ℝ) ^ ((m + 2) * d)) ^ q⁻¹ * B := by
      rw [Real.mul_rpow hpow0 (Real.rpow_nonneg hB0 q), ← Real.rpow_mul hB0,
        mul_inv_cancel₀ hq0.ne', Real.rpow_one]

/-! ## The subunit tail-ratio moment -/

private theorem paperENNRealLpNorm_le_of_ae_le
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {p : ℝ} (hp : 0 < p) {X : Omega → ℝ≥0∞} {W : Omega → ℝ}
    (hW0 : ∀ omega, 0 ≤ W omega)
    (hWint : Integrable (fun omega => W omega ^ p) mu)
    (hXW : ∀ᵐ omega ∂mu, X omega ≤ ENNReal.ofReal (W omega)) :
    paperENNRealLpNorm mu p X ≤
      ENNReal.ofReal ((∫ omega, W omega ^ p ∂mu) ^ p⁻¹) := by
  have hp0 : 0 ≤ p := hp.le
  have hinv0 : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0
  have hpow : ∀ᵐ omega ∂mu, X omega ^ p ≤ ENNReal.ofReal (W omega ^ p) := by
    filter_upwards [hXW] with omega homega
    calc
      X omega ^ p ≤ (ENNReal.ofReal (W omega)) ^ p :=
        ENNReal.rpow_le_rpow homega hp0
      _ = ENNReal.ofReal (W omega ^ p) :=
        ENNReal.ofReal_rpow_of_nonneg (hW0 omega) hp0
  unfold paperENNRealLpNorm
  calc
    (∫⁻ omega, X omega ^ p ∂mu) ^ p⁻¹ ≤
        (∫⁻ omega, ENNReal.ofReal (W omega ^ p) ∂mu) ^ p⁻¹ :=
      ENNReal.rpow_le_rpow (lintegral_mono_ae hpow) hinv0
    _ = (ENNReal.ofReal (∫ omega, W omega ^ p ∂mu)) ^ p⁻¹ := by
      rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hWint
        (Filter.Eventually.of_forall fun omega =>
          Real.rpow_nonneg (hW0 omega) p)]
    _ = ENNReal.ofReal ((∫ omega, W omega ^ p ∂mu) ^ p⁻¹) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun omega =>
        Real.rpow_nonneg (hW0 omega) p) hinv0]

/-- Dimensional smallness threshold used by the subunit grid maximum; it is the
`c(d)` of `e.gammazeta.cond` for this display. -/
def subunitSmallnessConst (d : ℕ) : ℝ :=
  min 1 (Real.log 3 / (4 * (4 * subunitScaleConst d ^ 2 + 1)))

/-- Dimensional prefactor in the subunit moment bound for `J`. -/
def subunitMomentConst (d : ℕ) : ℝ :=
  max 1 (96 * gammaMomentConst 2 ^ 2 * (3 : ℝ) ^ ((4 : ℝ)⁻¹) *
    (8 * subunitScaleConst d ^ 2 / Real.log 3 + 8 / Real.log 3 ^ 2))

private theorem log_three_pos : 0 < Real.log 3 :=
  Real.log_pos (by norm_num)

theorem subunitSmallnessConst_pos (d : ℕ) : 0 < subunitSmallnessConst d := by
  unfold subunitSmallnessConst
  refine lt_min (by norm_num) (div_pos log_three_pos ?_)
  positivity

theorem subunitSmallnessConst_le_one (d : ℕ) : subunitSmallnessConst d ≤ 1 :=
  min_le_left _ _

theorem one_le_subunitMomentConst (d : ℕ) : 1 ≤ subunitMomentConst d :=
  le_max_left _ _

private theorem subunitMomentConst_ge (d : ℕ) :
    96 * gammaMomentConst 2 ^ 2 * (3 : ℝ) ^ ((4 : ℝ)⁻¹) *
        subunitSmallnessConst d *
        (8 * subunitScaleConst d ^ 2 / Real.log 3 + 8 / Real.log 3 ^ 2) ≤
      subunitMomentConst d := by
  have hgamma0 : 0 < gammaMomentConst 2 := gammaMomentConst_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := log_three_pos
  have hc1 : subunitSmallnessConst d ≤ 1 := subunitSmallnessConst_le_one d
  have hpos : (0 : ℝ) ≤ 96 * gammaMomentConst 2 ^ 2 * (3 : ℝ) ^ ((4 : ℝ)⁻¹) *
      (8 * subunitScaleConst d ^ 2 / Real.log 3 + 8 / Real.log 3 ^ 2) := by
    positivity
  have hrw : 96 * gammaMomentConst 2 ^ 2 * (3 : ℝ) ^ ((4 : ℝ)⁻¹) *
      subunitSmallnessConst d *
      (8 * subunitScaleConst d ^ 2 / Real.log 3 + 8 / Real.log 3 ^ 2) =
      (96 * gammaMomentConst 2 ^ 2 * (3 : ℝ) ^ ((4 : ℝ)⁻¹) *
        (8 * subunitScaleConst d ^ 2 / Real.log 3 + 8 / Real.log 3 ^ 2)) *
        subunitSmallnessConst d := by ring
  rw [hrw]
  refine le_trans ?_ (le_max_right _ _)
  calc
    (96 * gammaMomentConst 2 ^ 2 * (3 : ℝ) ^ ((4 : ℝ)⁻¹) *
        (8 * subunitScaleConst d ^ 2 / Real.log 3 + 8 / Real.log 3 ^ 2)) *
          subunitSmallnessConst d ≤
        (96 * gammaMomentConst 2 ^ 2 * (3 : ℝ) ^ ((4 : ℝ)⁻¹) *
          (8 * subunitScaleConst d ^ 2 / Real.log 3 + 8 / Real.log 3 ^ 2)) * 1 :=
      mul_le_mul_of_nonneg_left hc1 hpos
    _ = _ := by ring

/-! ### The two parameter absorptions of `e.gammazeta.cond`

These are pure real inequalities, isolated from the probabilistic context so
that the linear arithmetic stays cheap. -/

private theorem subunit_real_absorption
    {c K xi delta delta1 s Q u A b : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hcthresh : c ≤ Real.log 3 / (4 * (4 * K ^ 2 + 1)))
    (hxi0 : 0 < xi) (hE0 : 0 < delta)
    (hdelta1 : delta1 < 1) (hdelta1pos : 0 < delta1)
    (hs : 0 < s) (hs1 : s ≤ 1)
    (hxiE : xi * delta ≤ c * s * delta1)
    (hEs : delta ≤ c / 4 * s ^ 2 * delta1)
    (hQ1 : 1 ≤ Q) (huQ : u = s * Q) (hb0 : 0 ≤ b)
    (hAsq : A ^ 2 = K ^ 2 * delta * Q) (hbQ : b ≤ Q * delta) :
    xi * (A + b) ^ 2 ≤ c * delta1 * (2 * K ^ 2 * u + u ^ 2 / 2) ∧
      4 * xi * A ^ 2 + 2 * b ≤ Real.log 3 / 4 * u := by
  have hQ0 : (0 : ℝ) ≤ Q := by linarith
  have hu0 : 0 ≤ u := by
    rw [huQ]
    exact mul_nonneg hs.le hQ0
  have hxiA : xi * A ^ 2 ≤ K ^ 2 * (c * s * delta1) * Q := by
    rw [hAsq]
    have h1 : xi * (K ^ 2 * delta * Q) = K ^ 2 * (xi * delta) * Q := by ring
    rw [h1]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hxiE (sq_nonneg K)) hQ0
  have hxiAu : xi * A ^ 2 ≤ K ^ 2 * c * delta1 * u := by
    have h2 : K ^ 2 * (c * s * delta1) * Q = K ^ 2 * c * delta1 * u := by
      rw [huQ]; ring
    rw [h2] at hxiA
    exact hxiA
  have hcs : c * s ≤ 1 := by
    have h1 : c * s ≤ 1 * 1 := mul_le_mul hc1 hs1 hs.le zero_le_one
    linarith
  have hcsd : c * s * delta1 ≤ 1 := by
    have h2 : c * s * delta1 ≤ 1 * 1 :=
      mul_le_mul hcs hdelta1.le hdelta1pos.le zero_le_one
    linarith
  have hxib : xi * b ^ 2 ≤ c / 4 * delta1 * u ^ 2 := by
    have hbsq : b ^ 2 ≤ (Q * delta) ^ 2 := pow_le_pow_left₀ hb0 hbQ 2
    have hstep1 : xi * b ^ 2 ≤ xi * (Q * delta) ^ 2 :=
      mul_le_mul_of_nonneg_left hbsq hxi0.le
    have hstep2 : xi * (Q * delta) ^ 2 = (xi * delta) * (delta * Q ^ 2) := by
      ring
    have hQ2 : (0 : ℝ) ≤ Q ^ 2 := sq_nonneg Q
    have hstep3 : (xi * delta) * (delta * Q ^ 2) ≤
        (c * s * delta1) * (c / 4 * s ^ 2 * delta1 * Q ^ 2) := by
      refine mul_le_mul hxiE ?_ (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right hEs hQ2
    have hstep4 : (c * s * delta1) * (c / 4 * s ^ 2 * delta1 * Q ^ 2) =
        ((c * s * delta1) * delta1) * (c / 4 * u ^ 2) := by
      rw [huQ]; ring
    have hstep5 : ((c * s * delta1) * delta1) * (c / 4 * u ^ 2) ≤
        delta1 * (c / 4 * u ^ 2) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have h := mul_le_mul_of_nonneg_right hcsd hdelta1pos.le
      linarith
    have hstep6 : delta1 * (c / 4 * u ^ 2) = c / 4 * delta1 * u ^ 2 := by ring
    linarith
  refine ⟨?_, ?_⟩
  · have hexpand : (A + b) ^ 2 ≤ 2 * A ^ 2 + 2 * b ^ 2 := by
      linarith [sq_nonneg (A - b)]
    have h1 : xi * (A + b) ^ 2 ≤ 2 * (xi * A ^ 2) + 2 * (xi * b ^ 2) := by
      linarith [mul_le_mul_of_nonneg_left hexpand hxi0.le]
    linarith
  · have h1' : 4 * (K ^ 2 * c * delta1 * u) ≤ 4 * K ^ 2 * c * u := by
      have hKu : (0 : ℝ) ≤ K ^ 2 * c * u :=
        mul_nonneg (mul_nonneg (sq_nonneg K) hc0.le) hu0
      have h := mul_le_mul_of_nonneg_left hdelta1.le hKu
      linarith
    have h3 : 2 * b ≤ c / 2 * u := by
      have hbb : b ≤ Q * (c / 4 * s ^ 2 * delta1) := by
        have := mul_le_mul_of_nonneg_left hEs hQ0
        linarith
      have hfin : Q * (c / 4 * s ^ 2 * delta1) ≤ c / 4 * u := by
        rw [huQ]
        have hcsQ : (0 : ℝ) ≤ c / 4 * s * Q :=
          mul_nonneg (mul_nonneg (by positivity) hs.le) hQ0
        have hsd : s * delta1 ≤ 1 := by
          have h := mul_le_mul hs1 hdelta1.le hdelta1pos.le zero_le_one
          linarith
        have h := mul_le_mul_of_nonneg_left hsd hcsQ
        linarith
      linarith
    have h4 : c * (4 * K ^ 2 + 1) ≤ Real.log 3 / 4 := by
      have hden : (0 : ℝ) < 4 * (4 * K ^ 2 + 1) := by positivity
      have h5 := (le_div_iff₀ hden).mp hcthresh
      linarith
    have hcu : (0 : ℝ) ≤ c * u := mul_nonneg hc0.le hu0
    linarith [mul_le_mul_of_nonneg_right h4 hu0]

private theorem subunit_geometric {K u : ℝ} (hu0 : 0 ≤ u) :
    (1 : ℝ) ≤ (3 : ℝ) ^ (u / 4) ∧
      ((3 : ℝ) ^ (u / 4)) ^ 4 = (3 : ℝ) ^ u ∧
      (3 : ℝ) ^ (u / 4) = Real.exp (Real.log 3 * (u / 4)) ∧
      2 * K ^ 2 * u + u ^ 2 / 2 ≤
        (8 * K ^ 2 / Real.log 3 + 8 / Real.log 3 ^ 2) *
          ((3 : ℝ) ^ (u / 4)) ^ 2 := by
  have hlog3 : 0 < Real.log 3 := log_three_pos
  have hR1 : (1 : ℝ) ≤ (3 : ℝ) ^ (u / 4) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hR0 : (0 : ℝ) < (3 : ℝ) ^ (u / 4) := lt_of_lt_of_le zero_lt_one hR1
  have hRe : (3 : ℝ) ^ (u / 4) = Real.exp (Real.log 3 * (u / 4)) :=
    Real.rpow_def_of_pos (by norm_num) _
  have hR4 : ((3 : ℝ) ^ (u / 4)) ^ 4 = (3 : ℝ) ^ u := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (u / 4)) 4,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have huR : u ≤ 4 / Real.log 3 * (3 : ℝ) ^ (u / 4) := by
    have hle : Real.log 3 * (u / 4) ≤ Real.exp (Real.log 3 * (u / 4)) := by
      have h := Real.add_one_le_exp (Real.log 3 * (u / 4))
      linarith
    have hcoef : (0 : ℝ) ≤ 4 / Real.log 3 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hle hcoef
    rw [hRe]
    calc
      u = 4 / Real.log 3 * (Real.log 3 * (u / 4)) := by field_simp
      _ ≤ 4 / Real.log 3 * Real.exp (Real.log 3 * (u / 4)) := hmul
  refine ⟨hR1, hR4, hRe, ?_⟩
  have hR2 : (3 : ℝ) ^ (u / 4) ≤ ((3 : ℝ) ^ (u / 4)) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hR1 hR0.le
    linarith
  have hu2 : u ^ 2 ≤ 2 * (8 / Real.log 3 ^ 2) * ((3 : ℝ) ^ (u / 4)) ^ 2 := by
    have hmul := mul_le_mul huR huR hu0 (by positivity)
    calc
      u ^ 2 = u * u := sq u
      _ ≤ (4 / Real.log 3 * (3 : ℝ) ^ (u / 4)) *
            (4 / Real.log 3 * (3 : ℝ) ^ (u / 4)) := hmul
      _ = 2 * (8 / Real.log 3 ^ 2) * ((3 : ℝ) ^ (u / 4)) ^ 2 := by
        field_simp
        ring
  have hlin : 2 * K ^ 2 * u ≤
      8 * K ^ 2 / Real.log 3 * ((3 : ℝ) ^ (u / 4)) ^ 2 := by
    have h1 : 2 * K ^ 2 * u ≤ 2 * K ^ 2 * (4 / Real.log 3 * (3 : ℝ) ^ (u / 4)) :=
      mul_le_mul_of_nonneg_left huR (by positivity)
    have hK2 : (0 : ℝ) ≤ 8 * K ^ 2 / Real.log 3 := by positivity
    have heq : 2 * K ^ 2 * (4 / Real.log 3 * (3 : ℝ) ^ (u / 4)) =
        8 * K ^ 2 / Real.log 3 * (3 : ℝ) ^ (u / 4) := by
      field_simp
      ring
    rw [heq] at h1
    have h2 := mul_le_mul_of_nonneg_left hR2 hK2
    linarith
  have hexpand : (8 * K ^ 2 / Real.log 3 + 8 / Real.log 3 ^ 2) *
      ((3 : ℝ) ^ (u / 4)) ^ 2 =
      8 * K ^ 2 / Real.log 3 * ((3 : ℝ) ^ (u / 4)) ^ 2 +
        8 / Real.log 3 ^ 2 * ((3 : ℝ) ^ (u / 4)) ^ 2 := by ring
  rw [hexpand]
  linarith

/-- The subunit moment bound for `J`: the `L^xi` moment of the subunit
absolute-cutoff grid maximum. -/
theorem subunit_tail_ratio_moment :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1 ∧ 1 ≤ C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (xi delta1 s : ℝ) (m : ℕ),
        1 ≤ xi → M.delta ^ 2 ≤ delta1 → delta1 < 1 →
        0 < s → s ≤ 1 →
        4 * (d : ℝ) * s⁻¹ ≤ xi →
        xi ≤ c * s * (M.delta ^ 2)⁻¹ * delta1 →
        paperENNRealLpNorm M.P.toMeasure xi
            (subunitTailRatioObservable M m) ≤
          ENNReal.ofReal (C * delta1 * (3 : ℝ) ^ (s * (m : ℝ))) := by
  refine ⟨subunitSmallnessConst d, subunitMomentConst d,
    subunitSmallnessConst_pos d, subunitSmallnessConst_le_one d,
    one_le_subunitMomentConst d, ?_⟩
  intro M xi delta1 s m hxi hdelta hdelta1 hs hs1 hxid hxic
  have hc0 : 0 < subunitSmallnessConst d := subunitSmallnessConst_pos d
  have hc1 : subunitSmallnessConst d ≤ 1 := subunitSmallnessConst_le_one d
  have hcthresh : subunitSmallnessConst d ≤
      Real.log 3 / (4 * (4 * subunitScaleConst d ^ 2 + 1)) := min_le_right _ _
  have hlog3 : 0 < Real.log 3 := log_three_pos
  have hgamma0 : 0 < gammaMomentConst 2 := gammaMomentConst_pos (by norm_num)
  have hxi0 : 0 < xi := lt_of_lt_of_le zero_lt_one hxi
  have hdeltapos : 0 < M.delta := M.shellPrefix.delta_pos
  have hE0 : 0 < M.delta ^ 2 := by positivity
  have hdelta1pos : 0 < delta1 := lt_of_lt_of_le hE0 hdelta
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
    have := M.shellPrefix.dimension
    exact_mod_cast le_trans (by norm_num) this
  have hxiE : xi * M.delta ^ 2 ≤ subunitSmallnessConst d * s * delta1 := by
    have h := mul_le_mul_of_nonneg_right hxic hE0.le
    calc
      xi * M.delta ^ 2 ≤
          subunitSmallnessConst d * s * (M.delta ^ 2)⁻¹ * delta1 *
            M.delta ^ 2 := h
      _ = subunitSmallnessConst d * s * delta1 := by field_simp
  have hEs : M.delta ^ 2 ≤ subunitSmallnessConst d / 4 * s ^ 2 * delta1 := by
    have h1 : 4 * (d : ℝ) * s⁻¹ * M.delta ^ 2 ≤ xi * M.delta ^ 2 :=
      mul_le_mul_of_nonneg_right hxid hE0.le
    have h2 : 4 * (d : ℝ) * s⁻¹ * M.delta ^ 2 ≤
        subunitSmallnessConst d * s * delta1 := h1.trans hxiE
    have h3 : 4 * (d : ℝ) * M.delta ^ 2 ≤
        subunitSmallnessConst d * s ^ 2 * delta1 := by
      have h4 := mul_le_mul_of_nonneg_right h2 hs.le
      calc
        4 * (d : ℝ) * M.delta ^ 2 = 4 * (d : ℝ) * s⁻¹ * M.delta ^ 2 * s := by
          field_simp
        _ ≤ subunitSmallnessConst d * s * delta1 * s := h4
        _ = subunitSmallnessConst d * s ^ 2 * delta1 := by ring
    nlinarith [mul_nonneg (mul_nonneg hc0.le (sq_nonneg s)) hdelta1pos.le]
  -- deterministic scale facts
  have hQ1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (m : ℝ) := by positivity
    linarith
  have hu0 : (0 : ℝ) ≤ s * ((m : ℝ) + 1) := mul_nonneg hs.le (by linarith)
  have hb0 : 0 ≤ subunitDrift M m := subunitDrift_nonneg M m
  have hAsq : subunitScale M m ^ 2 =
      subunitScaleConst d ^ 2 * M.delta ^ 2 * ((m : ℝ) + 1) := by
    unfold subunitScale
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  have hbQ : subunitDrift M m ≤ ((m : ℝ) + 1) * M.delta ^ 2 := by
    unfold subunitDrift
    have htau := tauSq_le_delta_sq M
    have hlog2 : Real.log 2 / 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hQ0 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
    have hstep : ((m : ℝ) + 1) * (Real.log 2 / 2 * M.delta ^ 2) ≤
        ((m : ℝ) + 1) * M.delta ^ 2 := by
      refine mul_le_mul_of_nonneg_left ?_ hQ0
      nlinarith [sq_nonneg M.delta]
    linarith [mul_le_mul_of_nonneg_left htau hQ0]
  obtain ⟨habs, hexpbound⟩ := subunit_real_absorption
    (c := subunitSmallnessConst d) (K := subunitScaleConst d)
    (xi := xi) (delta := M.delta ^ 2) (delta1 := delta1) (s := s)
    (Q := (m : ℝ) + 1) (u := s * ((m : ℝ) + 1)) (A := subunitScale M m)
    (b := subunitDrift M m) hc0 hc1 hcthresh hxi0 hE0 hdelta1 hdelta1pos
    hs hs1 hxiE hEs hQ1 rfl hb0 hAsq hbQ
  obtain ⟨hR1, hR4, hRe, hpoly⟩ :=
    subunit_geometric (K := subunitScaleConst d) (u := s * ((m : ℝ) + 1)) hu0
  set R : ℝ := (3 : ℝ) ^ (s * ((m : ℝ) + 1) / 4) with hRdef
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR1
  have hexpR : Real.exp (4 * xi * subunitScale M m ^ 2 +
      2 * subunitDrift M m) ≤ R := by
    rw [hRe]
    refine Real.exp_le_exp.mpr ?_
    calc
      4 * xi * subunitScale M m ^ 2 + 2 * subunitDrift M m ≤
          Real.log 3 / 4 * (s * ((m : ℝ) + 1)) := hexpbound
      _ = Real.log 3 * (s * ((m : ℝ) + 1) / 4) := by ring
  have h3u : (3 : ℝ) ^ (s * ((m : ℝ) + 1)) ≤ 3 * (3 : ℝ) ^ (s * (m : ℝ)) := by
    have hsplit : s * ((m : ℝ) + 1) = s * (m : ℝ) + s := by ring
    rw [hsplit, Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    have hle : (3 : ℝ) ^ s ≤ (3 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1
    rw [Real.rpow_one] at hle
    have hX : (0 : ℝ) ≤ (3 : ℝ) ^ (s * (m : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have h := mul_le_mul_of_nonneg_left hle hX
    linarith
  -- the grid cost
  have hds : (d : ℝ) * (2 * xi)⁻¹ ≤ s / 8 := by
    have hxinv : (0 : ℝ) < 2 * xi := by linarith
    have h1 : 4 * (d : ℝ) ≤ xi * s := by
      have h := mul_le_mul_of_nonneg_right hxid hs.le
      have heq : 4 * (d : ℝ) * s⁻¹ * s = 4 * (d : ℝ) := by field_simp
      rw [heq] at h
      linarith
    rw [← div_eq_mul_inv, div_le_iff₀ hxinv]
    linarith
  have hNpow : ((3 : ℝ) ^ ((m + 2) * d)) ^ (2 * xi)⁻¹ ≤
      (3 : ℝ) ^ (s * ((m : ℝ) + 2) / 8) := by
    rw [← Real.rpow_natCast (3 : ℝ) ((m + 2) * d),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hcast : (((m + 2) * d : ℕ) : ℝ) = ((m : ℝ) + 2) * (d : ℝ) := by
      push_cast
      ring
    rw [hcast, mul_assoc]
    have hm2 : (0 : ℝ) ≤ (m : ℝ) + 2 := by positivity
    calc
      ((m : ℝ) + 2) * ((d : ℝ) * (2 * xi)⁻¹) ≤ ((m : ℝ) + 2) * (s / 8) :=
        mul_le_mul_of_nonneg_left hds hm2
      _ = s * ((m : ℝ) + 2) / 8 := by ring
  have hNsq : (((3 : ℝ) ^ ((m + 2) * d)) ^ (2 * xi)⁻¹) ^ 2 ≤
      (3 : ℝ) ^ ((4 : ℝ)⁻¹) * R := by
    have hbase : (0 : ℝ) ≤ ((3 : ℝ) ^ ((m + 2) * d)) ^ (2 * xi)⁻¹ :=
      Real.rpow_nonneg (by positivity) _
    refine (pow_le_pow_left₀ hbase hNpow 2).trans ?_
    have h2 : ((3 : ℝ) ^ (s * ((m : ℝ) + 2) / 8)) ^ 2 =
        (3 : ℝ) ^ (s * ((m : ℝ) + 2) / 8 * 2) := by
      rw [← Real.rpow_natCast ((3 : ℝ) ^ (s * ((m : ℝ) + 2) / 8)) 2,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    rw [h2, hRdef, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    linarith
  -- assemble the moment
  have hq2 : (1 : ℝ) ≤ 2 * xi := by linarith
  obtain ⟨hGint, hGbd⟩ := subunitMajorant_moment M m hq2
  have hGnn : ∀ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, 0 ≤ subunitMajorant M m omega :=
    subunitMajorant_nonneg M m
  have hI0 : 0 ≤ ∫ omega, subunitMajorant M m omega ^ (2 * xi) ∂M.P.toMeasure :=
    integral_nonneg fun omega => Real.rpow_nonneg (hGnn omega) _
  have hJ0 : (0 : ℝ) ≤
      (∫ omega, subunitMajorant M m omega ^ (2 * xi) ∂M.P.toMeasure) ^
        (2 * xi)⁻¹ := Real.rpow_nonneg hI0 _
  have hBsq : (2 * gammaMomentConst 2 * Real.sqrt (2 * (2 * xi)) *
        (subunitScale M m + subunitDrift M m) *
        Real.exp (2 * xi * subunitScale M m ^ 2 + subunitDrift M m)) ^ 2 =
      16 * gammaMomentConst 2 ^ 2 *
        (xi * (subunitScale M m + subunitDrift M m) ^ 2) *
        Real.exp (4 * xi * subunitScale M m ^ 2 + 2 * subunitDrift M m) := by
    have hsq : Real.sqrt (2 * (2 * xi)) ^ 2 = 4 * xi := by
      rw [Real.sq_sqrt (by linarith)]
      ring
    have hexpsq : Real.exp (2 * xi * subunitScale M m ^ 2 +
        subunitDrift M m) ^ 2 =
        Real.exp (4 * xi * subunitScale M m ^ 2 + 2 * subunitDrift M m) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    have hring : (2 * gammaMomentConst 2 * Real.sqrt (2 * (2 * xi)) *
        (subunitScale M m + subunitDrift M m) *
        Real.exp (2 * xi * subunitScale M m ^ 2 + subunitDrift M m)) ^ 2 =
        4 * gammaMomentConst 2 ^ 2 * (Real.sqrt (2 * (2 * xi)) ^ 2) *
          (subunitScale M m + subunitDrift M m) ^ 2 *
          (Real.exp (2 * xi * subunitScale M m ^ 2 + subunitDrift M m) ^ 2) := by
      ring
    rw [hring, hsq, hexpsq]
    ring
  have hCbig : (0 : ℝ) ≤ 8 * subunitScaleConst d ^ 2 / Real.log 3 +
      8 / Real.log 3 ^ 2 := by positivity
  have hkey : xi * (subunitScale M m + subunitDrift M m) ^ 2 ≤
      subunitSmallnessConst d * delta1 *
        ((8 * subunitScaleConst d ^ 2 / Real.log 3 + 8 / Real.log 3 ^ 2) *
          R ^ 2) := by
    refine habs.trans ?_
    exact mul_le_mul_of_nonneg_left hpoly (by positivity)
  have hchain : (2 * gammaMomentConst 2 * Real.sqrt (2 * (2 * xi)) *
        (subunitScale M m + subunitDrift M m) *
        Real.exp (2 * xi * subunitScale M m ^ 2 + subunitDrift M m)) ^ 2 ≤
      16 * gammaMomentConst 2 ^ 2 *
        (subunitSmallnessConst d * delta1 *
          ((8 * subunitScaleConst d ^ 2 / Real.log 3 + 8 / Real.log 3 ^ 2) *
            R ^ 2)) * R := by
    rw [hBsq]
    refine mul_le_mul ?_ hexpR (Real.exp_pos _).le (by positivity)
    exact mul_le_mul_of_nonneg_left hkey (by positivity)
  have hCfinal := subunitMomentConst_ge d
  have hfinalreal : 2 * ((∫ omega, subunitMajorant M m omega ^ (2 * xi)
        ∂M.P.toMeasure) ^ (2 * xi)⁻¹) ^ 2 ≤
      subunitMomentConst d * delta1 * (3 : ℝ) ^ (s * (m : ℝ)) := by
    have hsquare := pow_le_pow_left₀ hJ0 hGbd 2
    rw [mul_pow] at hsquare
    have hstep : (((3 : ℝ) ^ ((m + 2) * d)) ^ (2 * xi)⁻¹) ^ 2 *
          (2 * gammaMomentConst 2 * Real.sqrt (2 * (2 * xi)) *
            (subunitScale M m + subunitDrift M m) *
            Real.exp (2 * xi * subunitScale M m ^ 2 + subunitDrift M m)) ^ 2 ≤
        ((3 : ℝ) ^ ((4 : ℝ)⁻¹) * R) *
          (16 * gammaMomentConst 2 ^ 2 *
            (subunitSmallnessConst d * delta1 *
              ((8 * subunitScaleConst d ^ 2 / Real.log 3 +
                8 / Real.log 3 ^ 2) * R ^ 2)) * R) :=
      mul_le_mul hNsq hchain (by positivity) (by positivity)
    have hcollect : ((3 : ℝ) ^ ((4 : ℝ)⁻¹) * R) *
        (16 * gammaMomentConst 2 ^ 2 *
          (subunitSmallnessConst d * delta1 *
            ((8 * subunitScaleConst d ^ 2 / Real.log 3 +
              8 / Real.log 3 ^ 2) * R ^ 2)) * R) =
        (16 * gammaMomentConst 2 ^ 2 * (3 : ℝ) ^ ((4 : ℝ)⁻¹) *
          subunitSmallnessConst d *
          (8 * subunitScaleConst d ^ 2 / Real.log 3 + 8 / Real.log 3 ^ 2)) *
            delta1 * R ^ 4 := by ring
    have hcoef0 : (0 : ℝ) ≤ 16 * gammaMomentConst 2 ^ 2 *
        (3 : ℝ) ^ ((4 : ℝ)⁻¹) * subunitSmallnessConst d *
          (8 * subunitScaleConst d ^ 2 / Real.log 3 + 8 / Real.log 3 ^ 2) := by
      positivity
    have hR4le : R ^ 4 ≤ 3 * (3 : ℝ) ^ (s * (m : ℝ)) := by
      rw [hRdef, hR4]
      exact h3u
    have hlast : (16 * gammaMomentConst 2 ^ 2 * (3 : ℝ) ^ ((4 : ℝ)⁻¹) *
          subunitSmallnessConst d *
          (8 * subunitScaleConst d ^ 2 / Real.log 3 + 8 / Real.log 3 ^ 2)) *
            delta1 * R ^ 4 ≤
        (16 * gammaMomentConst 2 ^ 2 * (3 : ℝ) ^ ((4 : ℝ)⁻¹) *
          subunitSmallnessConst d *
          (8 * subunitScaleConst d ^ 2 / Real.log 3 + 8 / Real.log 3 ^ 2)) *
            delta1 * (3 * (3 : ℝ) ^ (s * (m : ℝ))) :=
      mul_le_mul_of_nonneg_left hR4le (mul_nonneg hcoef0 hdelta1pos.le)
    have hCle : 2 * ((16 * gammaMomentConst 2 ^ 2 * (3 : ℝ) ^ ((4 : ℝ)⁻¹) *
          subunitSmallnessConst d *
          (8 * subunitScaleConst d ^ 2 / Real.log 3 + 8 / Real.log 3 ^ 2)) *
            delta1 * (3 * (3 : ℝ) ^ (s * (m : ℝ)))) ≤
        subunitMomentConst d * delta1 * (3 : ℝ) ^ (s * (m : ℝ)) := by
      have hrw : 2 * ((16 * gammaMomentConst 2 ^ 2 * (3 : ℝ) ^ ((4 : ℝ)⁻¹) *
            subunitSmallnessConst d *
            (8 * subunitScaleConst d ^ 2 / Real.log 3 + 8 / Real.log 3 ^ 2)) *
              delta1 * (3 * (3 : ℝ) ^ (s * (m : ℝ)))) =
          (96 * gammaMomentConst 2 ^ 2 * (3 : ℝ) ^ ((4 : ℝ)⁻¹) *
            subunitSmallnessConst d *
            (8 * subunitScaleConst d ^ 2 / Real.log 3 + 8 / Real.log 3 ^ 2)) *
              (delta1 * (3 : ℝ) ^ (s * (m : ℝ))) := by ring
      rw [hrw]
      have hnn : (0 : ℝ) ≤ delta1 * (3 : ℝ) ^ (s * (m : ℝ)) :=
        mul_nonneg hdelta1pos.le (Real.rpow_nonneg (by norm_num) _)
      calc
        _ ≤ subunitMomentConst d * (delta1 * (3 : ℝ) ^ (s * (m : ℝ))) :=
          mul_le_mul_of_nonneg_right hCfinal hnn
        _ = subunitMomentConst d * delta1 * (3 : ℝ) ^ (s * (m : ℝ)) := by ring
    have hall := hsquare.trans (hstep.trans (hcollect.le.trans hlast))
    calc
      2 * ((∫ omega, subunitMajorant M m omega ^ (2 * xi)
            ∂M.P.toMeasure) ^ (2 * xi)⁻¹) ^ 2 ≤
          2 * ((16 * gammaMomentConst 2 ^ 2 * (3 : ℝ) ^ ((4 : ℝ)⁻¹) *
            subunitSmallnessConst d *
            (8 * subunitScaleConst d ^ 2 / Real.log 3 + 8 / Real.log 3 ^ 2)) *
              delta1 * (3 * (3 : ℝ) ^ (s * (m : ℝ)))) := by
        linarith only [hall]
      _ ≤ _ := hCle
  -- transfer to the paper's carrier
  have hW0 : ∀ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, 0 ≤ 2 * subunitMajorant M m omega ^ 2 :=
    fun omega => by positivity
  have hWfun : (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      (2 * subunitMajorant M m omega ^ 2) ^ xi) =
      fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        2 ^ xi * subunitMajorant M m omega ^ (2 * xi) := by
    funext omega
    have hG0 := hGnn omega
    have hsq : subunitMajorant M m omega ^ 2 =
        subunitMajorant M m omega ^ (2 : ℝ) := by
      rw [← Real.rpow_natCast (subunitMajorant M m omega) 2]
      norm_num
    rw [hsq, Real.mul_rpow (by norm_num) (Real.rpow_nonneg hG0 2),
      ← Real.rpow_mul hG0]
  have hWint : Integrable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      (2 * subunitMajorant M m omega ^ 2) ^ xi) M.P.toMeasure := by
    rw [hWfun]
    exact hGint.const_mul _
  have hWval : (∫ omega, (2 * subunitMajorant M m omega ^ 2) ^ xi
        ∂M.P.toMeasure) ^ xi⁻¹ =
      2 * ((∫ omega, subunitMajorant M m omega ^ (2 * xi)
        ∂M.P.toMeasure) ^ (2 * xi)⁻¹) ^ 2 := by
    rw [hWfun, integral_const_mul,
      Real.mul_rpow (Real.rpow_nonneg (by norm_num) xi) hI0,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_inv_cancel₀ hxi0.ne',
      Real.rpow_one]
    congr 1
    have hxine : xi ≠ 0 := hxi0.ne'
    have hexp : xi⁻¹ = (2 * xi)⁻¹ * ((2 : ℕ) : ℝ) := by
      push_cast
      field_simp
    rw [hexp, Real.rpow_mul hI0, Real.rpow_natCast]
  refine (paperENNRealLpNorm_le_of_ae_le hxi0 hW0 hWint
    (ae_subunitTailRatioObservable_le M m)).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hWval]
  exact hfinalreal

end

end SubdiffusiveProcess.CoarseGrainingVocab
