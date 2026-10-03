module

public import SubdiffusiveProcess.CoarseGrainingVocab.CutoffRatioSup
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.AnnealedOrdering
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SuffixMoment

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory Homogenization Homogenization.Book Homogenization.IndependentSums

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

theorem potentialShellIndexSigma_mono {d : ℕ} {I J : Set ℕ}
    (hIJ : I ⊆ J) :
    potentialShellIndexSigma (d := d) I ≤ potentialShellIndexSigma J := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d261_potentialShellIndexSigma_mono (d := d) (I := I) (J := J) (hIJ := hIJ)

/-! ## Strict-suffix measurability of the own-scale block -/

private theorem measurable_cutoffShellSum_potentialShellIndexSigma_Ioi
    {d : ℕ} (m k : ℕ) (x : Vec d) :
    @Measurable (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) ℝ (potentialShellIndexSigma (Set.Ioi k))
      inferInstance (cutoffShellSum m (k : ℤ) x) := by
  unfold cutoffShellSum
  apply Finset.measurable_sum
  intro j hj
  have hjk : k < j := by
    have hj' := (Finset.mem_Icc.mp hj).1
    simpa only [Int.toNat_natCast, Nat.lt_succ_iff] using! hj'
  exact (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval x).comp
    (measurable_potentialCoordinate_shellIndexSigma
      (show j ∈ Set.Ioi k from hjk))

private theorem measurable_translatedSmallShellEnvelope_potentialShellIndexSigma_Ioi
    {d : ℕ} (k j : ℕ) (hj : k < j) (r : ℤ) (z : Vec d) :
    @Measurable (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) ℝ (potentialShellIndexSigma (Set.Ioi k))
      inferInstance (translatedSmallShellEnvelope j r z) := by
  unfold translatedSmallShellEnvelope
  exact measurable_const.mul
    (measurable_translatedShellG2_potentialShellIndexSigma
      (show j ∈ Set.Ioi k from hj) _)

/-- The canonical own-scale envelope for the finite shell block `(k,m]` on
the physical translate `z + cube_k` reads only shells strictly above `k`. -/
theorem measurable_smallCubeBlockEnvelope_potentialShellIndexSigma_Ioi
    {d : ℕ} (m k : ℕ) (z : Vec d) :
    @Measurable (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) ℝ (potentialShellIndexSigma (Set.Ioi k))
      inferInstance
      (smallCubeBlockEnvelope (k + 1) m (k : ℤ) z) := by
  letI : MeasurableSpace (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) := potentialShellIndexSigma (Set.Ioi k)
  change Measurable (smallCubeBlockEnvelope (k + 1) m (k : ℤ) z)
  unfold smallCubeBlockEnvelope
  have hpoint :=
    measurable_cutoffShellSum_potentialShellIndexSigma_Ioi
      (d := d) m k z
  have hsum : @Measurable (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) ℝ
      (potentialShellIndexSigma (Set.Ioi k)) inferInstance
      (fun omega => ∑ j ∈ Finset.Icc (k + 1) m,
        translatedSmallShellEnvelope j (k : ℤ) z omega) := by
    apply Finset.measurable_sum
    intro j hj
    have hj' : k + 1 ≤ j := (Finset.mem_Icc.mp hj).1
    exact measurable_translatedSmallShellEnvelope_potentialShellIndexSigma_Ioi
      k j (by omega) (k : ℤ) z
  simpa only [Real.norm_eq_abs, show (((k + 1 : ℕ) : ℤ) - 1) = (k : ℤ) by omega] using!
    hpoint.norm.add hsum

/-! ## The finite-block lognormal representative -/

/-- Selected simultaneous representative for the forward and inverse cutoff
ratios of the finite shell block `(k,m]` on `z + cube_k`. -/
noncomputable def finiteBlockRatioRepresentative {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m k : ℕ) (z : Vec d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : ℝ :=
  Real.exp
      (smallCubeBlockEnvelope (k + 1) m (k : ℤ) z omega +
        ((m - k : ℕ) : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) - 1

theorem finiteBlockRatioRepresentative_nonneg {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m k : ℕ) (z : Vec d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    0 ≤ finiteBlockRatioRepresentative M m k z omega := by
  unfold finiteBlockRatioRepresentative
  apply sub_nonneg.mpr
  apply Real.one_le_exp
  exact add_nonneg (smallCubeBlockEnvelope_nonneg _ _ _ _ _)
    (mul_nonneg (by positivity) M.G4.tauSq_pos.le)

/-- The finite-block representative is measurable for the strict suffix above
`k`, exactly as required by the prefix/suffix factorization. -/
theorem measurable_finiteBlockRatioRepresentative {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m k : ℕ) (z : Vec d) :
    @Measurable (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) ℝ (potentialShellIndexSigma (Set.Ioi k))
      inferInstance (finiteBlockRatioRepresentative M m k z) := by
  unfold finiteBlockRatioRepresentative
  exact ((measurable_smallCubeBlockEnvelope_potentialShellIndexSigma_Ioi
    (d := d) m k z).add_const _).exp.sub_const 1

private theorem abs_exp_sub_one_le_exp_abs_sub_one (t : ℝ) :
    |Real.exp t - 1| ≤ Real.exp |t| - 1 := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht, abs_of_nonneg
      (sub_nonneg.mpr (Real.one_le_exp ht))]
  · have ht0 : t ≤ 0 := le_of_not_ge ht
    rw [abs_of_nonpos ht0, abs_of_nonpos
      (sub_nonpos.mpr (Real.exp_le_one_iff.mpr ht0))]
    have hpos := Real.add_one_le_exp t
    have hneg := Real.add_one_le_exp (-t)
    nlinarith

/-- On the translated scale-`k` cube, the selected representative dominates
the forward finite cutoff ratio. -/
theorem abs_cutoffRatioMinusOne_le_finiteBlockRatioRepresentative {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m k : ℕ} (hkm : k < m)
    (z : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) {x : Vec d}
    (hx : x - z ∈ openCubeSet (originCube d (k : ℤ))) :
    |cutoffRatioMinusOne M m (k : ℤ) omega x| ≤
      finiteBlockRatioRepresentative M m k z omega := by
  let Z := smallCubeBlockEnvelope (k + 1) m (k : ℤ) z omega
  let b := ((m - k : ℕ) : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P
  have hZ0 : 0 ≤ Z := smallCubeBlockEnvelope_nonneg _ _ _ _ _
  have hb0 : 0 ≤ b := mul_nonneg (by positivity) M.G4.tauSq_pos.le
  have hshell : |cutoffShellSum m (k : ℤ) x omega| ≤ Z := by
    simpa [Z, show (((k + 1 : ℕ) : ℤ) - 1) = (k : ℤ) by omega] using
      abs_cutoffShellSum_le_smallCubeBlockEnvelope
        (d := d) (k + 1) m (k : ℤ) z (by norm_num) omega hx
  rw [cutoffRatioMinusOne_eq_exp_shell M m (k : ℤ) omega x
    (by omega) (by omega)]
  have hcast : ((((m : ℤ) - (k : ℤ) : ℤ) : ℝ)) = ((m - k : ℕ) : ℝ) := by
    exact_mod_cast (show (m : ℤ) - k = (m - k : ℕ) by omega)
  rw [hcast]
  calc
    |Real.exp (cutoffShellSum m (k : ℤ) x omega - b) - 1| ≤
        Real.exp |cutoffShellSum m (k : ℤ) x omega - b| - 1 :=
      abs_exp_sub_one_le_exp_abs_sub_one _
    _ ≤ Real.exp (Z + b) - 1 := by
      gcongr
      calc
        |cutoffShellSum m (k : ℤ) x omega - b| ≤
            |cutoffShellSum m (k : ℤ) x omega| + |b| := abs_sub _ _
        _ = |cutoffShellSum m (k : ℤ) x omega| + b := by rw [abs_of_nonneg hb0]
        _ ≤ Z + b := add_le_add hshell le_rfl
    _ = finiteBlockRatioRepresentative M m k z omega := by
      simp only [finiteBlockRatioRepresentative, Z, b]

/-- On the translated scale-`k` cube, the same selected representative also
dominates the inverse finite cutoff ratio. -/
theorem abs_inverseCutoffRatioMinusOne_le_finiteBlockRatioRepresentative {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m k : ℕ} (hkm : k < m)
    (z : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) {x : Vec d}
    (hx : x - z ∈ openCubeSet (originCube d (k : ℤ))) :
    |inverseCutoffRatioMinusOne M m (k : ℤ) omega x| ≤
      finiteBlockRatioRepresentative M m k z omega := by
  let Z := smallCubeBlockEnvelope (k + 1) m (k : ℤ) z omega
  let b := ((m - k : ℕ) : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P
  have hZ0 : 0 ≤ Z := smallCubeBlockEnvelope_nonneg _ _ _ _ _
  have hb0 : 0 ≤ b := mul_nonneg (by positivity) M.G4.tauSq_pos.le
  have hshell : |cutoffShellSum m (k : ℤ) x omega| ≤ Z := by
    simpa [Z, show (((k + 1 : ℕ) : ℤ) - 1) = (k : ℤ) by omega] using
      abs_cutoffShellSum_le_smallCubeBlockEnvelope
        (d := d) (k + 1) m (k : ℤ) z (by norm_num) omega hx
  rw [inverseCutoffRatioMinusOne_eq_exp_shell M m (k : ℤ) omega x
    (by omega) (by omega)]
  have hcast : ((((m : ℤ) - (k : ℤ) : ℤ) : ℝ)) = ((m - k : ℕ) : ℝ) := by
    exact_mod_cast (show (m : ℤ) - k = (m - k : ℕ) by omega)
  rw [hcast]
  calc
    |Real.exp (-cutoffShellSum m (k : ℤ) x omega + b) - 1| ≤
        Real.exp |-cutoffShellSum m (k : ℤ) x omega + b| - 1 :=
      abs_exp_sub_one_le_exp_abs_sub_one _
    _ ≤ Real.exp (Z + b) - 1 := by
      gcongr
      calc
        |-cutoffShellSum m (k : ℤ) x omega + b| =
            |cutoffShellSum m (k : ℤ) x omega - b| := by
          rw [show -cutoffShellSum m (k : ℤ) x omega + b =
            -(cutoffShellSum m (k : ℤ) x omega - b) by ring, abs_neg]
        _ ≤ |cutoffShellSum m (k : ℤ) x omega| + |b| := abs_sub _ _
        _ = |cutoffShellSum m (k : ℤ) x omega| + b := by rw [abs_of_nonneg hb0]
        _ ≤ Z + b := add_le_add hshell le_rfl
    _ = finiteBlockRatioRepresentative M m k z omega := by
      simp only [finiteBlockRatioRepresentative, Z, b]

/-! ## Raw sharp moment -/

/-- The exact lognormal-transfer output for the canonical finite-block
representative.  The public own-scale estimate
`smallCubeBlockScale_ownScale_le` turns `A` into
`C * delta * sqrt (m-k)` at its consumers. -/
theorem finiteBlockRatioRepresentative_moment_raw {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m k : ℕ} (hkm : k < m)
    (z : Vec d) (p : ℝ) (hp : 1 ≤ p) :
    let A := smallCubeBlockScale M (k + 1) m (k : ℤ)
    let b := ((m - k : ℕ) : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P
    Integrable (fun omega =>
      finiteBlockRatioRepresentative M m k z omega ^ p) M.P.toMeasure ∧
    (∫ omega, finiteBlockRatioRepresentative M m k z omega ^ p
        ∂M.P.toMeasure) ^ p⁻¹ ≤
      2 * gammaMomentConst 2 * Real.sqrt (2 * p) * (A + b) *
        Real.exp (p * A ^ 2 + b) := by
  dsimp only
  let A := smallCubeBlockScale M (k + 1) m (k : ℤ)
  let b := ((m - k : ℕ) : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P
  let Z : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := smallCubeBlockEnvelope (k + 1) m (k : ℤ) z
  have hA : 0 < A := by
    unfold A smallCubeBlockScale
    apply mul_pos gammaTriangleConst_pos
    apply add_pos
    · exact mul_pos (mul_pos cutoffGammaConst_pos
        (Real.sqrt_pos.mpr (by positivity))) M.shellPrefix.delta_pos
    · exact mul_pos gammaTriangleConst_pos
        (Finset.sum_pos
          (fun j _ => translatedSmallShellScale_pos M j (k : ℤ))
          (Finset.nonempty_Icc.mpr (by omega)))
  have hb0 : 0 ≤ b := mul_nonneg (by positivity) M.G4.tauSq_pos.le
  have hZtail : IsBigO M.P.toMeasure (gammaSigma 2) Z A := by
    simpa [Z, A, IsBigO,
      abs_of_nonneg (smallCubeBlockEnvelope_nonneg (d := d) (k + 1) m
        (k : ℤ) z _)] using
      isBigOWith_gammaTwo_smallCubeBlockEnvelope M (k + 1) m (k : ℤ) z
        (by omega)
  have htransfer := integral_abs_exp_sub_const_sub_one_rpow_root_le
    (mu := M.P.toMeasure) (X := Z) (A := A) (p := p) (b := -b)
    hA hp (measurable_smallCubeBlockEnvelope _ _ _ _).aemeasurable hZtail
  have hfun : (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
      finiteBlockRatioRepresentative M m k z omega ^ p) =
      fun omega => |Real.exp (Z omega - -b) - 1| ^ p := by
    funext omega
    rw [sub_neg_eq_add, abs_of_nonneg]
    · rfl
    · exact finiteBlockRatioRepresentative_nonneg M m k z omega
  constructor
  · rw [hfun]
    exact htransfer.1
  · rw [hfun]
    simpa only [abs_neg, abs_of_nonneg hb0] using htransfer.2

/-- The own-scale weak-tail parameter has the sharp square-root gap. -/
theorem finiteBlockRatioRepresentative_scale_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m k : ℕ} (hkm : k < m) :
    smallCubeBlockScale M (k + 1) m (k : ℤ) ≤
      smallCubeBlockConst * Real.sqrt ((m - k : ℕ) : ℝ) * M.delta := by
  have h := smallCubeBlockScale_ownScale_le M (k + 1) m
  have hgap : m - (k + 1) + 1 = m - k := by omega
  simpa only [show (((k + 1 : ℕ) : ℤ) - 1) = (k : ℤ) by omega, hgap] using h

/-! ## The manuscript's two-block product envelope -/

/-- Sum of the forward and reciprocal deterministic annealed-ratio defects. -/
noncomputable def annealedRatioDefect {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m k : ℕ) : ℝ :=
  |ahom M m * (ahom M k)⁻¹ - 1| +
    |(ahom M m)⁻¹ * ahom M k - 1|

theorem annealedRatioDefect_nonneg {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m k : ℕ) :
    0 ≤ annealedRatioDefect M m k :=
  add_nonneg (abs_nonneg _) (abs_nonneg _)



noncomputable def sharpTwoBlockSuffixRepresentative {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m k : ℕ) (z : Vec d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : ℝ :=
  2 *
    ((1 + annealedRatioDefect M m k) *
        (1 + cutoffChangeSuffixRepresentative m (m : ℤ) omega) *
        (1 + finiteBlockRatioRepresentative M m k z omega) - 1)

theorem sharpTwoBlockSuffixRepresentative_nonneg {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m k : ℕ) (z : Vec d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    0 ≤ sharpTwoBlockSuffixRepresentative M m k z omega := by
  have hD := annealedRatioDefect_nonneg M m k
  have hY := cutoffChangeSuffixRepresentative_nonneg (d := d) m (m : ℤ) omega
  have hZ := finiteBlockRatioRepresentative_nonneg M m k z omega
  unfold sharpTwoBlockSuffixRepresentative
  have hfirst : 1 ≤
      (1 + annealedRatioDefect M m k) *
        (1 + cutoffChangeSuffixRepresentative m (m : ℤ) omega) := by
    nlinarith [mul_nonneg hD hY]
  have hfull : 1 ≤
      (1 + annealedRatioDefect M m k) *
        (1 + cutoffChangeSuffixRepresentative m (m : ℤ) omega) *
          (1 + finiteBlockRatioRepresentative M m k z omega) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hfirst) hZ]
  nlinarith



theorem measurable_sharpTwoBlockSuffixRepresentative {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m k : ℕ} (hkm : k ≤ m)
    (z : Vec d) :
    @Measurable (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) ℝ (potentialShellIndexSigma (Set.Ioi k))
      inferInstance (sharpTwoBlockSuffixRepresentative M m k z) := by
  letI : MeasurableSpace (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) := potentialShellIndexSigma (Set.Ioi k)
  have hlarge0 := measurable_cutoffChangeSuffixRepresentative (d := d) m (m : ℤ)
  have hset : Set.Ioi m ⊆ Set.Ioi k := by
    intro j hj
    exact lt_of_le_of_lt hkm hj
  have hlarge : Measurable (cutoffChangeSuffixRepresentative (d := d) m (m : ℤ)) :=
    hlarge0.mono (potentialShellIndexSigma_mono (d := d) hset) le_rfl
  have hfinite : Measurable (finiteBlockRatioRepresentative M m k z) :=
    measurable_finiteBlockRatioRepresentative M m k z
  unfold sharpTwoBlockSuffixRepresentative
  fun_prop

/-- Product-expansion arithmetic used for both orientations of the
manuscript's `X_(m,k)(z)`. -/
theorem abs_mul_three_sub_one_le_product_envelope
    {X Y Z DX DY DZ : ℝ}
    (hDX : 0 ≤ DX) (hDY : 0 ≤ DY)
    (hX : |X - 1| ≤ DX) (hY : |Y - 1| ≤ DY) (hZ : |Z - 1| ≤ DZ) :
    |X * Y * Z - 1| ≤ (1 + DX) * (1 + DY) * (1 + DZ) - 1 := by
  have hraw : |X * Y * Z - 1| ≤
      |X - 1| + |Y - 1| + |Z - 1| +
        |X - 1| * |Y - 1| + |X - 1| * |Z - 1| +
        |Y - 1| * |Z - 1| + |X - 1| * |Y - 1| * |Z - 1| := by
    have hid : X * Y * Z - 1 =
        (X - 1) + (Y - 1) + (Z - 1) +
          (X - 1) * (Y - 1) + (X - 1) * (Z - 1) +
          (Y - 1) * (Z - 1) + (X - 1) * (Y - 1) * (Z - 1) := by ring
    rw [hid]
    let a := X - 1
    let b := Y - 1
    let c := Z - 1
    let e := (X - 1) * (Y - 1)
    let f := (X - 1) * (Z - 1)
    let g := (Y - 1) * (Z - 1)
    let h := (X - 1) * (Y - 1) * (Z - 1)
    have h1 := abs_add_le a b
    have h2 := abs_add_le (a + b) c
    have h3 := abs_add_le (a + b + c) e
    have h4 := abs_add_le (a + b + c + e) f
    have h5 := abs_add_le (a + b + c + e + f) g
    have h6 := abs_add_le (a + b + c + e + f + g) h
    calc
      |_ + _ + _ + _ + _ + _ + _| ≤
          |X - 1| + |Y - 1| + |Z - 1| +
            |(X - 1) * (Y - 1)| + |(X - 1) * (Z - 1)| +
            |(Y - 1) * (Z - 1)| + |(X - 1) * (Y - 1) * (Z - 1)| := by
        dsimp only [a, b, c, e, f, g, h] at h1 h2 h3 h4 h5 h6
        linarith
      _ = _ := by simp only [abs_mul]
  calc
    |X * Y * Z - 1| ≤ _ := hraw
    _ ≤ DX + DY + DZ + DX * DY + DX * DZ + DY * DZ + DX * DY * DZ := by
      gcongr
    _ = (1 + DX) * (1 + DY) * (1 + DZ) - 1 := by ring




private theorem continuous_cutoffShellSum_in_space
    {d : ℕ} (L m : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    Continuous (fun x : Vec d => cutoffShellSum L (m : ℤ) x omega) := by
  unfold cutoffShellSum
  fun_prop



theorem tailCutoff_pair_ratio_le_cutoffRatioOscillationSup {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m : ℕ} (hmL : m ≤ L)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) {x y : Vec d}
    (hx : x ∈ openCubeSet (originCube d (m : ℤ)))
    (hy : y ∈ openCubeSet (originCube d (m : ℤ))) :
    ENNReal.ofReal
        |(SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x /
              SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m omega x) /
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y /
              SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m omega y) - 1| ≤
      cutoffRatioOscillationSup m (m : ℤ) omega := by
  by_cases hLm : L = m
  · subst L
    have hx0 := (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M m omega x).ne'
    have hy0 := (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M m omega y).ne'
    simp [hx0, hy0]
  have hmL' : m < L := lt_of_le_of_ne hmL (Ne.symm hLm)
  let S : Vec d → ℝ := fun u => cutoffShellSum L (m : ℤ) u omega
  let b : ℝ := (((L : ℤ) - (m : ℤ) : ℤ) : ℝ) *
    SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P
  have hxratio := cutoffRatioMinusOne_eq_exp_shell
    M L (m : ℤ) omega x (by omega) (by omega)
  have hyratio := cutoffRatioMinusOne_eq_exp_shell
    M L (m : ℤ) omega y (by omega) (by omega)
  have hxexp : SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x /
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m omega x = Real.exp (S x - b) := by
    rw [cutoffRatioMinusOne] at hxratio
    simp only [aCutoffAtInt, show ¬(m : ℤ) < 0 by omega, if_false,
      Int.toNat_natCast] at hxratio
    change _ - 1 = Real.exp (S x - b) - 1 at hxratio
    linarith
  have hyexp : SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y /
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m omega y = Real.exp (S y - b) := by
    rw [cutoffRatioMinusOne] at hyratio
    simp only [aCutoffAtInt, show ¬(m : ℤ) < 0 by omega, if_false,
      Int.toNat_natCast] at hyratio
    change _ - 1 = Real.exp (S y - b) - 1 at hyratio
    linarith
  have hratio :
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x /
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m omega x) /
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y /
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m omega y) =
        Real.exp (S x - S y) := by
    rw [hxexp, hyexp, div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  have hdiff : |S x - S y| ≤ cubeOscillation (m : ℤ) S := by
    rw [abs_le]
    constructor
    · have h := sub_le_cubeOscillation_of_continuous (m : ℤ)
        (continuous_cutoffShellSum_in_space L m omega) hy hx
      dsimp only [S] at h ⊢
      linarith
    · exact sub_le_cubeOscillation_of_continuous (m : ℤ)
        (continuous_cutoffShellSum_in_space L m omega) hx hy
  have hreal : |Real.exp (S x - S y) - 1| ≤
      Real.exp (cubeOscillation (m : ℤ) S) - 1 := by
    exact (abs_exp_sub_one_le_exp_abs_sub_one _).trans
      (sub_le_sub_right (Real.exp_le_exp.mpr hdiff) 1)
  rw [hratio]
  unfold cutoffRatioOscillationSup
  refine (ENNReal.ofReal_le_ofReal hreal).trans ?_
  exact le_iSup_of_le L (le_iSup_of_le hmL le_rfl)



theorem ae_tailCutoff_pair_ratio_le_cutoffChangeSuffixRepresentative {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) :
    ∀ᵐ omega ∂M.P.toMeasure,
      ∀ (L : ℕ), m ≤ L → ∀ x y : Vec d,
        x ∈ openCubeSet (originCube d (m : ℤ)) →
        y ∈ openCubeSet (originCube d (m : ℤ)) →
        |(SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x /
              SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m omega x) /
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y /
              SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m omega y) - 1| ≤
          cutoffChangeSuffixRepresentative m (m : ℤ) omega := by
  filter_upwards
    [ae_cutoffRatioOscillationSup_le_cutoffChangeSuffixRepresentative
      M m (m : ℤ)] with omega hselected
  intro L hmL x y hx hy
  have hpoint :=
    (tailCutoff_pair_ratio_le_cutoffRatioOscillationSup M hmL omega hx hy).trans
      hselected
  exact (ENNReal.ofReal_le_ofReal_iff
    (cutoffChangeSuffixRepresentative_nonneg m (m : ℤ) omega)).mp hpoint




/-- If all pair ratios of a positive continuous field are within `Y` of one,
then both normalizations by its spatial average are within `Y` of one.  This
is the deterministic average-between-extrema step used twice in
`e.localize.J.from.L.to.m`. -/
theorem tailAverage_ratio_bounds {d : ℕ} (U : Ch02.Domain d)
    (t : Vec d → ℝ) (ht : Continuous t) (htpos : ∀ x, 0 < t x)
    {Y : ℝ}
    (hpair : ∀ x ∈ (U : Set (Vec d)), ∀ y ∈ (U : Set (Vec d)),
      |t x / t y - 1| ≤ Y)
    (havg : 0 < Ch02.average U t) {y : Vec d} (hy : y ∈ (U : Set (Vec d))) :
    |Ch02.average U t / t y - 1| ≤ Y ∧
      |t y / Ch02.average U t - 1| ≤ Y := by
  let A : ℝ := Ch02.average U t
  have htInt : IntegrableOn t (U : Set (Vec d)) :=
    (ht.continuousOn.integrableOn_compact
      U.isDomain.isBoundedDomain.isBounded.isCompact_closure).mono_set
        subset_closure
  have hvolpos : 0 < (volume (U : Set (Vec d))).toReal := by
    have hpos : 0 < volume (U : Set (Vec d)) :=
      U.isOpen.measure_pos volume U.nonempty
    have htop : volume (U : Set (Vec d)) ≠ ⊤ :=
      ne_of_lt U.isDomain.volume_lt_top
    exact ENNReal.toReal_pos hpos.ne' htop
  have hvol : (volume (U : Set (Vec d))).toReal ≠ 0 := hvolpos.ne'
  have hty : 0 < t y := htpos y
  let f : Vec d → ℝ := fun x => t x / t y - 1
  have hfcont : Continuous f := (ht.div_const _).sub continuous_const
  have hfInt : IntegrableOn f (U : Set (Vec d)) :=
    (hfcont.continuousOn.integrableOn_compact
      U.isDomain.isBoundedDomain.isBounded.isCompact_closure).mono_set
        subset_closure
  have hfavg : Ch02.average U f = A / t y - 1 := by
    change volumeAverage (U : Set (Vec d)) f = _
    have hscaled : IntegrableOn (fun x => t x / t y) (U : Set (Vec d)) := by
      simpa [div_eq_mul_inv, mul_comm] using! htInt.const_mul (t y)⁻¹
    have honeInt : IntegrableOn (fun _ : Vec d => (1 : ℝ))
        (U : Set (Vec d)) := integrable_const 1
    rw [show f = (fun x => t x / t y) - (fun _ => 1) by rfl,
      volumeAverage_sub hscaled honeInt,
      volumeAverage_const hvol]
    rw [show (fun x => t x / t y) = (t y)⁻¹ • t by
      funext x; simp [smul_eq_mul, div_eq_mul_inv, mul_comm],
      volumeAverage_smul]
    dsimp [A, Ch02.average, volumeAverage]
    ring
  have hfupper : Ch02.average U f ≤ Y := by
    change volumeAverage (U : Set (Vec d)) f ≤ Y
    exact volumeAverage_le_of_le_on U.measurableSet hfInt hvol
      (fun x hx => (le_abs_self (f x)).trans (hpair x hx y hy))
  have hfnegInt : IntegrableOn (fun x => -f x) (U : Set (Vec d)) :=
    hfInt.neg
  have hfnegupper : Ch02.average U (fun x => -f x) ≤ Y := by
    change volumeAverage (U : Set (Vec d)) (fun x => -f x) ≤ Y
    exact volumeAverage_le_of_le_on U.measurableSet hfnegInt hvol
      (fun x hx => (neg_le_abs (f x)).trans (hpair x hx y hy))
  have hfnegavg : Ch02.average U (fun x => -f x) = -Ch02.average U f := by
    change volumeAverage (U : Set (Vec d)) (fun x => -f x) =
      -volumeAverage (U : Set (Vec d)) f
    rw [show (fun x => -f x) = (-1 : ℝ) • f by
      funext x; simp, volumeAverage_smul]
    simp
  have hfirst : |A / t y - 1| ≤ Y := by
    rw [← hfavg]
    rw [abs_le]
    constructor
    · rw [hfnegavg] at hfnegupper
      linarith
    · exact hfupper
  have hlowerPoint : ∀ x ∈ (U : Set (Vec d)),
      (1 - Y) * t x ≤ t y := by
    intro x hx
    have h := hpair y hy x hx
    have htX := htpos x
    have hlow : -Y ≤ t y / t x - 1 := (abs_le.mp h).1
    have hlow' : 1 - Y ≤ t y / t x := by linarith
    exact (le_div_iff₀ htX).mp hlow'
  have hupperPoint : ∀ x ∈ (U : Set (Vec d)),
      t y ≤ (1 + Y) * t x := by
    intro x hx
    have h := hpair y hy x hx
    have htX := htpos x
    have hupp : t y / t x - 1 ≤ Y := (abs_le.mp h).2
    have hupp' : t y / t x ≤ 1 + Y := by linarith
    exact (div_le_iff₀ htX).mp hupp'
  have hlowerInt : IntegrableOn (fun x => (1 - Y) * t x)
      (U : Set (Vec d)) := htInt.const_mul (1 - Y)
  have hlowerAvg : (1 - Y) * A ≤ t y := by
    have h := volumeAverage_le_of_le_on U.measurableSet hlowerInt hvol
      hlowerPoint
    change volumeAverage (U : Set (Vec d)) (fun x => (1 - Y) * t x) ≤ t y at h
    rw [show (fun x => (1 - Y) * t x) = (1 - Y) • t by
      funext x; simp [smul_eq_mul], volumeAverage_smul] at h
    exact h
  have hupperDiffInt : IntegrableOn (fun x => t y - (1 + Y) * t x)
      (U : Set (Vec d)) :=
    (integrable_const (μ := volume.restrict (U : Set (Vec d))) (t y)).sub
      (htInt.const_mul (1 + Y))
  have hupperAvg0 : Ch02.average U (fun x => t y - (1 + Y) * t x) ≤ 0 := by
    change volumeAverage (U : Set (Vec d)) (fun x => t y - (1 + Y) * t x) ≤ 0
    exact volumeAverage_le_of_le_on U.measurableSet hupperDiffInt hvol
      (fun x hx => sub_nonpos.mpr (hupperPoint x hx))
  have hupperAvg : t y ≤ (1 + Y) * A := by
    have hconstInt : IntegrableOn (fun _ : Vec d => t y)
        (U : Set (Vec d)) :=
      integrable_const (μ := volume.restrict (U : Set (Vec d))) (t y)
    have hscaledInt : IntegrableOn ((1 + Y) • t) (U : Set (Vec d)) := by
      simpa [smul_eq_mul] using! htInt.const_mul (1 + Y)
    have heqfun : (fun x => t y - (1 + Y) * t x) =
        (fun _ => t y) - (1 + Y) • t := by
      funext x
      simp [smul_eq_mul]
    rw [heqfun] at hupperAvg0
    change volumeAverage (U : Set (Vec d))
      ((fun _ => t y) - (1 + Y) • t) ≤ 0 at hupperAvg0
    rw [volumeAverage_sub hconstInt hscaledInt,
      volumeAverage_const hvol, volumeAverage_smul] at hupperAvg0
    dsimp [A, Ch02.average, volumeAverage] at hupperAvg0 ⊢
    linarith
  have hsecond : |t y / A - 1| ≤ Y := by
    rw [abs_le]
    constructor
    · have hratioLower : 1 - Y ≤ t y / A :=
        (le_div_iff₀ havg).2 hlowerAvg
      nlinarith
    · have hratioUpper : t y / A ≤ 1 + Y :=
        (div_le_iff₀ havg).2 hupperAvg
      nlinarith
  exact ⟨hfirst, hsecond⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab
