module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalComponentScale
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalCrossingProvider
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalProvider

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section

/-! ## The residual, with the box constant recorded -/



def UniformChemicalDistanceBoundBox (d Cdep : ℕ) (Cprob cprob : ℝ) : Prop :=
  ∃ q0 Cbox : ℕ, ∃ c Cfail Clen : ℝ,
    1 ≤ Cbox ∧ 0 < c ∧ 0 < Cfail ∧ 0 ≤ Clen ∧
    ∀ {Omega : Type} [MeasurableSpace Omega] (mu : Measure Omega)
      [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Omega) (q : ℝ),
      (q0 : ℝ) ≤ q →
      (∀ j z, mu (E j z) ≤
        ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2)))) →
      IndependentEventScales mu E →
      MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E →
      TranslationInvariantEventLaw mu E →
      ∀ (z : Lattice d) (L : ℕ), 1 ≤ L →
        mu (chemicalDistanceFailureEvent E Cbox Clen z L) ≤
          ENNReal.ofReal (Cfail * Real.exp (-c * q * Real.log L ^ 2))

/-- The box-recorded bound is the printed one. -/
theorem uniformChemicalDistanceBound_of_box {d Cdep : ℕ} {Cprob cprob : ℝ}
    (h : UniformChemicalDistanceBoundBox d Cdep Cprob cprob) :
    UniformChemicalDistanceBound d Cdep Cprob cprob := by
  obtain ⟨q0, Cbox, c, Cfail, Clen, _, hc, hCfail, hClen, hb⟩ := h
  exact ⟨q0, Cbox, c, Cfail, Clen, hc, hCfail, hClen, hb⟩

/-- **`DRSLevelData` still feeds the box-recorded bound.**  Same route as
`uniformChemicalDistanceBound_of_drsLevelData`; the box constant of that lemma is
already positive by hypothesis, so nothing is lost. -/
theorem uniformChemicalDistanceBoundBox_of_drsLevelData
    (d Cdep q0 Cbox : ℕ) (Cprob cprob c Cfail Clen Centropy : ℝ)
    (hCbox : 1 ≤ Cbox) (hc : 0 < c) (hCprob : 0 ≤ Cprob)
    (hclen : 4 ≤ Clen) (hCfail1 : 1 ≤ Cfail) (hCentropy : 1 ≤ Centropy)
    (hccprob : c ≤ cprob) (hq0pos : 0 < q0)
    (hCfail : ((5 : ℝ) ^ d) * (2 * (Cprob * (((3 * Cbox) ^ d : ℕ) : ℝ))) ≤ Cfail)
    (hq0 : ∀ q : ℝ, (q0 : ℝ) ≤ q →
      2 * (Real.log Centropy + Real.log 2) + 2 * Real.sqrt 2 * d ≤ 4 * c * q)
    (hq0seed : ∀ q : ℝ, (q0 : ℝ) ≤ q →
      Real.log ((3 : ℝ) ^ d) + Real.log 2 ≤ cprob * q)
    (hdata : DRSLevelData d Cdep q0 Cbox Cprob cprob c Clen Centropy) :
    UniformChemicalDistanceBoundBox d Cdep Cprob cprob := by
  have hClen0 : (0 : ℝ) ≤ Clen := by linarith
  refine ⟨q0, Cbox, c, Cfail, Clen, hCbox, hc, by linarith, hClen0, ?_⟩
  intro Omega _ mu _ E q hq hprob hscales hrange hlaw z L hL
  obtain ⟨Cross, Rk, Sk, hseed, hindep, hcross, hcard, hroute⟩ :=
    hdata mu E q hq hprob hscales hrange hlaw
  have hqpos : 0 < q := lt_of_lt_of_le (by exact_mod_cast hq0pos) hq
  have hcp : 0 ≤ cprob * q := by
    have : 0 < cprob := lt_of_lt_of_le hc hccprob
    positivity
  exact measure_chemicalDistanceFailureEvent_le (dim := d) (Centropy := Centropy)
    hqpos hc hCfail1 hCentropy (hq0 q hq) hseed hindep hcross hcard
    (fun k x => clusteredBadForcing_badLevelEvent (hroute k x))
    (levelToRadiusTransfer_badLevelEvent E Cbox Clen)
    (smallRadiusBound_of_multiscaleEventProbability hCbox hclen hCprob hqpos.le
      hc.le hccprob hcp (hq0seed q hq) hprob hCfail) z L hL

/-! ## Clause (iii) of the anchor -/

/-- The amplitude constant of the `H₂` tail: `C(d) / q` with
`C(d) = 4 (1 + log (max 1 (2 Cfail))) / (c (log 2) ^ 2)`. -/
def chemicalHeightAmplitude (c Cfail : ℝ) : ℝ :=
  4 * (1 + Real.log (max 1 (2 * max 1 Cfail))) / (c * Real.log 2 ^ 2)

theorem chemicalHeightAmplitude_pos {c Cfail : ℝ} (hc : 0 < c) :
    0 < chemicalHeightAmplitude c Cfail := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnum : 0 ≤ Real.log (max 1 (2 * max 1 Cfail)) :=
    Real.log_nonneg (le_max_left _ _)
  have hden : 0 < c * Real.log 2 ^ 2 := by positivity
  exact div_pos (by linarith) hden

/-- **The residual of P-374, from the manuscript's printed missing lemma.**

`DRSChemicalInput` — clause (iii) of `[ASD, Lemma B.1]` with the `O_{Γ₁}(C/q)`
tail of the dyadic height, centred at exactly `1` — for the concrete field, from
`UniformChemicalDistanceBoundBox`. -/
theorem exists_drsChemicalInput_of_uniformChemicalDistanceBoundBox
    {d Cdep : ℕ} {Cprob cprob : ℝ}
    (h : UniformChemicalDistanceBoundBox d Cdep Cprob cprob) :
    ∃ q0 Cbox : ℕ, ∃ Cr Clen : ℝ,
      1 ≤ Cbox ∧ 0 < Cr ∧ 0 ≤ Clen ∧
      DRSChemicalInput d Cdep q0 Cbox Cprob cprob Cr Clen := by
  classical
  obtain ⟨q0, Cbox, c, Cfail, Clen, hCbox, hc, hCfailpos, hClen, hb⟩ := h
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcl : 0 < c * Real.log 2 ^ 2 := by positivity
  set Cf : ℝ := max 1 Cfail with hCf
  have hCf1 : 1 ≤ Cf := le_max_left _ _
  have hCf0 : (0 : ℝ) ≤ Cf := by linarith
  have hCfle : Cfail ≤ Cf := le_max_right _ _
  set T : ℝ := 1 / (c * Real.log 2 ^ 2) with hT
  have hTpos : 0 < T := by positivity
  refine ⟨max q0 ⌈T⌉₊, Cbox, chemicalHeightAmplitude c Cfail, Clen, hCbox,
    chemicalHeightAmplitude_pos hc, hClen, ?_⟩
  intro Omega _ mu _ E q hq hprob hsc hr hlaw
  have hq0le : (q0 : ℝ) ≤ q :=
    le_trans (by exact_mod_cast Nat.le_max_left q0 ⌈T⌉₊) hq
  have hTq : T ≤ q :=
    le_trans (le_trans (Nat.le_ceil T) (by exact_mod_cast Nat.le_max_right q0 ⌈T⌉₊)) hq
  have hqpos : 0 < q := lt_of_lt_of_le hTpos hTq
  set rate : ℝ := chemicalTailRate c q with hrate
  have hratepos : 0 < rate := chemicalTailRate_pos hc hqpos
  have hrate1 : 1 ≤ rate := by
    rw [hrate, chemicalTailRate]
    rw [hT, div_le_iff₀ hcl] at hTq
    nlinarith
  have hE : ∀ j z, MeasurableSet (E j z) := hlaw.1
  have hD : ∀ (z : Lattice d) (n : ℕ),
      MeasurableSet (chemicalDistanceFailureEvent E Cbox Clen z (2 ^ n)) :=
    fun z n => measurableSet_chemicalDistanceFailureEvent hE Cbox Clen z (2 ^ n)
  have hbound : ∀ (z : Lattice d) (n : ℕ), 1 ≤ n →
      mu (chemicalDistanceFailureEvent E Cbox Clen z (2 ^ n)) ≤
        ENNReal.ofReal (Cf * Real.exp (-(rate * (n : ℝ) ^ 2))) := by
    intro z n _
    refine le_trans (hb mu E q hq0le hprob hsc hr hlaw z (2 ^ n) Nat.one_le_two_pow) ?_
    refine ENNReal.ofReal_le_ofReal ?_
    rw [chemicalDyadic_bound_rewrite (c := c) (q := q) (Cfail := Cfail) n, ← hrate]
    exact mul_le_mul_of_nonneg_right hCfle (Real.exp_pos _).le
  refine ⟨fun z ω => chemicalComponentScale E Cbox Clen z ω,
    fun z ω => one_le_chemicalComponentScale E Cbox Clen z ω, ?_, ?_, ?_⟩
  · intro z
    have hbase := ogammaLE_chemicalComponentScale mu (hD z) hCf0 hratepos (hbound z)
    refine ogammaLE_mono_scale_one' ?_ ?_ hbase
    · have hnum : 0 ≤ Real.log (chemicalTailPrefactor Cf rate) :=
        Real.log_nonneg (one_le_chemicalTailPrefactor _ _)
      positivity
    · have hpre : chemicalTailPrefactor Cf rate ≤ max 1 (2 * Cf) :=
        chemicalTailPrefactor_le hCf0 hrate1
      have hlogle : Real.log (chemicalTailPrefactor Cf rate) ≤
          Real.log (max 1 (2 * Cf)) :=
        Real.log_le_log (lt_of_lt_of_le zero_lt_one (one_le_chemicalTailPrefactor _ _))
          hpre
      have hamp : chemicalHeightAmplitude c Cfail / q =
          4 * ((1 + Real.log (max 1 (2 * Cf))) / rate) := by
        rw [chemicalHeightAmplitude, hCf, hrate, chemicalTailRate]
        field_simp
      rw [hamp]
      have h4 : (0 : ℝ) < 4 := by norm_num
      refine mul_le_mul_of_nonneg_left ?_ h4.le
      gcongr
  · have hae : ∀ᵐ ω ∂mu, ∀ z : Lattice d,
        (chemicalDistanceHeightSet E Cbox Clen z ω).Nonempty := by
      refine ae_all_iff.2 fun z => ?_
      exact ae_nonempty_chemicalDistanceHeightSet mu hCf0 hratepos (hbound z)
    filter_upwards [hae] with ω hω
    intro z n hn
    exact not_mem_chemicalDistanceFailureEvent_of_chemicalComponentScale_le (hω z) hn
  · exact fun z => measurable_chemicalComponentScale (hD z)

/-! ## The frozen block -/



theorem weightedMultiscalePercolation_of_uniformChemicalDistanceBoundBox
    (d Cdep : ℕ) (Cprob cprob : ℝ) (hd : 2 ≤ d)
    (hCprob : 0 < Cprob) (hcprob : 0 < cprob)
    (hres : UniformChemicalDistanceBoundBox d Cdep Cprob cprob) :
    ∃ q0 L0 Cbox : ℕ, ∃ c C : ℝ,
      0 < c ∧ 0 < C ∧ 1 ≤ L0 ∧
      ∀ {Omega : Type} [MeasurableSpace Omega] (mu : Measure Omega)
        [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Omega) (q : ℝ),
        (q0 : ℝ) ≤ q →
        (∀ j z, mu (E j z) ≤
          ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2)))) →
        IndependentEventScales mu E →
        MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E →
        TranslationInvariantEventLaw mu E →
        ∃ crossing component : Lattice d → Omega → ℕ,
          (∀ z omega, 1 ≤ crossing z omega) ∧
          (∀ z omega, 1 ≤ component z omega) ∧
          (∀ z, SubdiffusiveProcess.OGammaLE mu 1 (C / q) (fun omega => (crossing z omega : ℝ) - L0)) ∧
          (∀ z, SubdiffusiveProcess.OGammaLE mu 1 (C / q) (fun omega => (component z omega : ℝ) - 1)) ∧
          AEFiniteRangePercolationGeometry mu E Cbox
            (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.section9CrossingSteps d)
            c C q crossing component := by
  obtain ⟨q0r, Cbox, Cr, Clen, hCbox, hCr, hClen, hinput⟩ :=
    exists_drsChemicalInput_of_uniformChemicalDistanceBoundBox hres
  exact weightedMultiscalePercolation_of_chemical d Cdep q0r Cbox Cprob cprob Cr Clen
    hd hCbox hCprob hcprob hCr hClen hinput

/-- **The frozen block plus the two measurability facts, from the uniform chemical-distance
bound alone.**

`weightedMultiscalePercolation_of_uniformChemicalDistanceBoundBox` is untouched and keeps its
exact declared type; this companion routes through
`weightedMultiscalePercolationMeasurable_of_chemical` instead. -/
theorem weightedMultiscalePercolationMeasurable_of_uniformChemicalDistanceBoundBox
    (d Cdep : ℕ) (Cprob cprob : ℝ) (hd : 2 ≤ d)
    (hCprob : 0 < Cprob) (hcprob : 0 < cprob)
    (hres : UniformChemicalDistanceBoundBox d Cdep Cprob cprob) :
    ∃ q0 L0 Cbox : ℕ, ∃ c C : ℝ,
      0 < c ∧ 0 < C ∧ 1 ≤ L0 ∧
      ∀ {Omega : Type} [MeasurableSpace Omega] (mu : Measure Omega)
        [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Omega) (q : ℝ),
        (q0 : ℝ) ≤ q →
        (∀ j z, mu (E j z) ≤
          ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2)))) →
        IndependentEventScales mu E →
        MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E →
        TranslationInvariantEventLaw mu E →
        ∃ crossing component : Lattice d → Omega → ℕ,
          (∀ z omega, 1 ≤ crossing z omega) ∧
          (∀ z omega, 1 ≤ component z omega) ∧
          (∀ z, SubdiffusiveProcess.OGammaLE mu 1 (C / q) (fun omega => (crossing z omega : ℝ) - L0)) ∧
          (∀ z, SubdiffusiveProcess.OGammaLE mu 1 (C / q) (fun omega => (component z omega : ℝ) - 1)) ∧
          AEFiniteRangePercolationGeometry mu E Cbox
            (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.section9CrossingSteps d)
            c C q crossing component ∧
          (∀ z, Measurable (crossing z)) ∧
          (∀ z, Measurable (component z)) := by
  obtain ⟨q0r, Cbox, Cr, Clen, hCbox, hCr, hClen, hinput⟩ :=
    exists_drsChemicalInput_of_uniformChemicalDistanceBoundBox hres
  exact weightedMultiscalePercolationMeasurable_of_chemical d Cdep q0r Cbox Cprob cprob Cr Clen
    hd hCbox hCprob hcprob hCr hClen hinput

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
