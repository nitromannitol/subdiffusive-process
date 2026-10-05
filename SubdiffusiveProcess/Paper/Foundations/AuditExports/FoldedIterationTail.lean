module

public import SubdiffusiveProcess.Paper.prop_folded_iteration
public import SubdiffusiveProcess.Paper.inputs_J_witness
public import SubdiffusiveProcess.Paper.inputs_poincare_witness
public import SubdiffusiveProcess.Paper.inputs_extension_witness
public import SubdiffusiveProcess.Paper.inputs_deterministic_witness
public import SubdiffusiveProcess.Paper.inputs_iteration_witness

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open SubdiffusiveProcess _root_.SubdiffusiveProcess.Paper _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section
namespace SubdiffusiveProcess.AuditExports

/-- The original iteration prefix, evaluated at the folded exponent, has the
paper's tail for every real threshold. Enlarging the dimensional constant by
one absorbs the passage from the integer threshold to its floor. -/
theorem folded_iteration_prefix_tail
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (E : in_J d)
    (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
    (C K gamma : ℝ) (hC : It.C + 1 ≤ C) (hK : 1 ≤ K)
    (hdelta : M.delta ≤ C⁻¹) (hgamma : gamma ∈ Ico (1 / 2 : ℝ) 1)
    (hgap : C * K * M.delta * Real.sqrt |Real.log M.delta| ≤ 1 - gamma) :
    ∀ (m : ℕ) (z : SpatialCoordinates d) (h : ℝ), 0 ≤ h →
      (chaosSampleLaw M).toMeasure
          {om | h < (It.prefixLen z (1 - (1 - gamma) / K) m om : ℝ)} ≤
        ENNReal.ofReal (C * Real.exp (-((1 - gamma) ^ 2 * max (h - C) 0 /
          (C * K ^ 2 * M.delta ^ 2 * |Real.log M.delta|)))) := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hdeltaPos : 0 < M.delta := M.shellPrefix.delta_pos
  have hCc : It.C ≤ C := by linarith
  have hCpos : 0 < C := It.C_pos.trans_le hCc
  have hdeltaIt : M.delta ≤ It.C⁻¹ :=
    hdelta.trans (inv_anti₀ It.C_pos hCc)
  have hdeltaLt : M.delta < 1 := by
    have hCtwo : 2 ≤ C := by linarith [It.C_ge_one]
    exact lt_of_le_of_lt
      (hdelta.trans (inv_anti₀ (by norm_num : (0 : ℝ) < 2) hCtwo)) (by norm_num)
  have hlogPos : 0 < |Real.log M.delta| :=
    abs_pos.mpr (ne_of_lt (Real.log_neg hdeltaPos hdeltaLt))
  have h1gamma : 0 ≤ 1 - gamma := sub_nonneg.mpr hgamma.2.le
  have hstar : 1 - (1 - gamma) / K ∈ It.alphaRange := by
    rw [It.alphaRange_eq]
    constructor
    · have hdiv := div_le_self h1gamma hK
      linarith [hgamma.1]
    · have hrate : 0 ≤ M.delta * Real.sqrt |Real.log M.delta| := by positivity
      have hscaled : It.C * M.delta * Real.sqrt |Real.log M.delta| * K ≤ 1 - gamma := by
        calc
          It.C * M.delta * Real.sqrt |Real.log M.delta| * K
              = It.C * (K * (M.delta * Real.sqrt |Real.log M.delta|)) := by ring
          _ ≤ C * (K * (M.delta * Real.sqrt |Real.log M.delta|)) :=
            mul_le_mul_of_nonneg_right hCc (mul_nonneg hKpos.le hrate)
          _ = C * K * M.delta * Real.sqrt |Real.log M.delta| := by ring
          _ ≤ 1 - gamma := hgap
      have hdiv := (le_div_iff₀ hKpos).mpr hscaled
      linarith
  intro m z h hh
  have htail := It.prefix_tail z (1 - (1 - gamma) / K) hstar hdeltaIt m ⌊h⌋₊
  have hset : {om | h < (It.prefixLen z (1 - (1 - gamma) / K) m om : ℝ)} ⊆
      {om | ⌊h⌋₊ < It.prefixLen z (1 - (1 - gamma) / K) m om} := by
    intro om hom
    exact (Nat.floor_lt hh).mpr hom
  have hfloor := Nat.lt_floor_add_one h
  have hmax : max (h - C) 0 ≤ max ((⌊h⌋₊ : ℝ) - It.C) 0 := by
    apply max_le_max_right
    linarith
  have hnum : 0 ≤ (1 - gamma) ^ 2 * max (h - C) 0 := by positivity
  have hden : 0 < It.C * K ^ 2 * M.delta ^ 2 * |Real.log M.delta| :=
    mul_pos (mul_pos (mul_pos It.C_pos (sq_pos_of_pos hKpos))
      (sq_pos_of_pos hdeltaPos)) hlogPos
  have hdenle : It.C * K ^ 2 * M.delta ^ 2 * |Real.log M.delta| ≤
      C * K ^ 2 * M.delta ^ 2 * |Real.log M.delta| := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCc (sq_nonneg K))
        (sq_nonneg M.delta)) (abs_nonneg _)
  have hquot : (1 - gamma) ^ 2 * max (h - C) 0 /
        (C * K ^ 2 * M.delta ^ 2 * |Real.log M.delta|) ≤
      (1 - gamma) ^ 2 * max ((⌊h⌋₊ : ℝ) - It.C) 0 /
        (It.C * K ^ 2 * M.delta ^ 2 * |Real.log M.delta|) := by
    calc
      _ ≤ (1 - gamma) ^ 2 * max (h - C) 0 /
          (It.C * K ^ 2 * M.delta ^ 2 * |Real.log M.delta|) :=
        div_le_div_of_nonneg_left hnum hden hdenle
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmax (sq_nonneg (1 - gamma))) hden.le
  have hid : (1 - (1 - (1 - gamma) / K)) ^ 2 *
        max ((⌊h⌋₊ : ℝ) - It.C) 0 /
        (It.C * M.delta ^ 2 * |Real.log M.delta|) =
      (1 - gamma) ^ 2 * max ((⌊h⌋₊ : ℝ) - It.C) 0 /
        (It.C * K ^ 2 * M.delta ^ 2 * |Real.log M.delta|) := by
    rw [show 1 - (1 - (1 - gamma) / K) = (1 - gamma) / K by ring, div_pow]
    rw [div_mul_eq_mul_div, div_div]
    congr 1
    ring
  rw [hid] at htail
  refine (measure_mono hset).trans (htail.trans (ENNReal.ofReal_le_ofReal ?_))
  exact mul_le_mul hCc (Real.exp_le_exp.mpr (neg_le_neg hquot))
    (Real.exp_pos _).le hCpos.le

/-- Energy decay for a nonempty coordinate fold, together with the stopping-scale
tail under the same dimensional constants. The J chart, deterministic
inputs and original-field regularity/iteration packages are constructed from
existing nodes. The prefix has no cutoff parameter, so the tail is uniform in
`L`, `m` and the deterministic translate `z`. -/
theorem folded_iteration_energy_and_tail
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ C K : ℝ, 0 < C ∧ 1 ≤ K ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ C⁻¹ →
      ∀ gamma : ℝ, gamma ∈ Ico (1 / 2 : ℝ) 1 →
        C * K * M.delta * Real.sqrt |Real.log M.delta| ≤ 1 - gamma →
        let E := Classical.choice (inputs_J_witness d hd)
        let Sreg := inputs_regularity_witness d M
        let It := inputs_iteration_witness d hd M E
        let gammaStar := 1 - (1 - gamma) / K
        ∀ (L m : ℕ) (z : SpatialCoordinates d), m ≤ L →
          ((∀ h : ℝ, 0 ≤ h →
            (chaosSampleLaw M).toMeasure {om | h < (It.prefixLen z gammaStar m om : ℝ)} ≤
              ENNReal.ofReal (C * Real.exp (-((1 - gamma) ^ 2 * max (h - C) 0 /
                (C * K ^ 2 * M.delta ^ 2 * |Real.log M.delta|))))) ∧
          ∀ (n : ℕ) (hR : (0 : ℝ) < 3 ^ m) (om : BilateralField d)
            (I P : Finset (Fin d)), I.Nonempty → n ≤ m →
            (n : ℤ) ≤ (m : ℤ) - It.prefixLen z gammaStar m om →
            ∀ foldedCoef : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ m) hR),
              ((foldedCoef.val : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))]
                fun x => (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR).val
                  (coordinateFold z I P x)) →
            ∀ (g : SpatialCoordinates d → Fin d → ℝ)
              (hgrad : HilbertGradient (centeredCube z ((3 : ℝ) ^ m) hR))
              (u : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hR)),
              SubdiffusiveProcess.CoarseGrainingVocab.MemHolder
                (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) (1 / 2) g →
              (∀ i : Fin d, (hgrad i : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))]
                fun x => g x i) →
              (∀ φ : killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hR),
                sobolevCoefficientForm foldedCoef
                  (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR))
                  (φ : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR)) =
                -inner ℝ hgrad
                  (subspaceGradient (killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hR)) φ)) →
              normalizedEnergyNorm foldedCoef
                (centeredCube z ((3 : ℝ) ^ n) (by positivity)).isOpen.measurableSet
                (sobolevGradient (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR))) ≤
              C * (3 : ℝ) ^ ((1 - gamma) * ((m : ℝ) - n)) *
                (normalizedEnergyNorm foldedCoef
                  (centeredCube z ((3 : ℝ) ^ m) hR).isOpen.measurableSet
                  (sobolevGradient (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR))) +
                Real.sqrt (It.ref L (m - 2) z om)⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2) *
                  halfHolderSeminorm (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) g)) := by
  classical
  let E := Classical.choice (inputs_J_witness d hd)
  let Pc := Classical.choice (inputs_poincare_witness d hd E)
  let Xc := Classical.choice (inputs_extension_witness d hd E)
  have : NeZero d := ⟨by omega⟩
  obtain ⟨Cenergy, K, hCenergy, hKfold, henergy⟩ :=
    prop_folded_iteration d hd E Pc Xc (inputs_deterministic_witness d hd)
  have hden : 0 < (3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1 := by
    have hp := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 3)
      (by norm_num : (0 : ℝ) < 1 - 2 * (1 / 32 : ℝ))
    linarith
  have hK : 1 ≤ K := by
    have hfrac : 0 ≤ 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1) :=
      div_nonneg (by positivity) hden.le
    linarith
  obtain ⟨cC, _c1, _c2, _hcC, _, _, hconst⟩ :=
    aux_prop_folded_iteration_carrier_constants d hd
  let C := max Cenergy (cC + 1)
  have hCE : Cenergy ≤ C := le_max_left _ _
  have hCpos : 0 < C := hCenergy.trans_le hCE
  refine ⟨C, K, hCpos, hK, ?_⟩
  intro M hdelta gamma hgamma hgap E' Sreg It gammaStar L m z hmL
  have hdeltaPos : 0 < M.delta := M.shellPrefix.delta_pos
  have hItC : It.C + 1 ≤ C := by
    rw [(hconst E' M Sreg It).1]
    exact le_max_right _ _
  refine ⟨folded_iteration_prefix_tail M E' Sreg It C K gamma hItC hK hdelta hgamma hgap m z,
    ?_⟩
  have hdeltaE : M.delta ≤ Cenergy⁻¹ :=
    hdelta.trans (inv_anti₀ hCenergy hCE)
  have hgammaE : gamma ∈ Icc (1 / 2 : ℝ)
      (1 - Cenergy * M.delta * Real.sqrt |Real.log M.delta|) := by
    refine ⟨hgamma.1, ?_⟩
    have hCK : Cenergy ≤ C * K := hCE.trans (le_mul_of_one_le_right hCpos.le hK)
    have hscaled := mul_le_mul_of_nonneg_right hCK
      (show 0 ≤ M.delta * Real.sqrt |Real.log M.delta| by positivity)
    have hbound : Cenergy * M.delta * Real.sqrt |Real.log M.delta| ≤ 1 - gamma := by
      calc
        _ = Cenergy * (M.delta * Real.sqrt |Real.log M.delta|) := by ring
        _ ≤ (C * K) * (M.delta * Real.sqrt |Real.log M.delta|) := hscaled
        _ = C * K * M.delta * Real.sqrt |Real.log M.delta| := by ring
        _ ≤ 1 - gamma := hgap
    linarith
  intro n hR om I P hI hnm hprefix foldedCoef hfold g hgrad u hg hggrad hweak
  have hest := henergy M Sreg It hdeltaE gamma hgammaE L m n z hR om I P hI hmL hnm
    hprefix foldedCoef hfold g hgrad u hg hggrad hweak
  refine hest.trans ?_
  apply mul_le_mul_of_nonneg_right
  · exact mul_le_mul_of_nonneg_right hCE (Real.rpow_nonneg (by norm_num) _)
  · exact add_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (by norm_num) _))
    (aux_prop_folded_iteration_halfHolder_nonneg _ _))

/-- The added tail clause of `mfd:prop-folded-iteration`. Its constants are
chosen together with the folded energy constants, before the model, exponent,
cutoff, cube and translate. The scale is the constructed original iteration
prefix at `gammaStar`, with no `L` dependence and no PDE or folding premise. -/
theorem folded_iteration_minimal_scale_tail
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ C K : ℝ, 0 < C ∧ 1 ≤ K ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ C⁻¹ →
      ∀ gamma : ℝ, gamma ∈ Ico (1 / 2 : ℝ) 1 →
        C * K * M.delta * Real.sqrt |Real.log M.delta| ≤ 1 - gamma →
        let E := Classical.choice (inputs_J_witness d hd)
        let It := inputs_iteration_witness d hd M E
        let gammaStar := 1 - (1 - gamma) / K
        ∀ (L m : ℕ) (z : SpatialCoordinates d), m ≤ L →
          ∀ h : ℝ, 0 ≤ h →
            (chaosSampleLaw M).toMeasure {om | h < (It.prefixLen z gammaStar m om : ℝ)} ≤
              ENNReal.ofReal (C * Real.exp (-((1 - gamma) ^ 2 * max (h - C) 0 /
                (C * K ^ 2 * M.delta ^ 2 * |Real.log M.delta|)))) := by
  obtain ⟨C, K, hC, hK, hboth⟩ := folded_iteration_energy_and_tail d hd
  refine ⟨C, K, hC, hK, ?_⟩
  intro M hdelta gamma hgamma hgap E It gammaStar L m z hmL
  exact (hboth M hdelta gamma hgamma hgap L m z hmL).1

end SubdiffusiveProcess.AuditExports
