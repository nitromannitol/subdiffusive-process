module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalLevelCarrier
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalSmallRadius
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalDRSConditions
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalRefutation

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section

/-! ## The external level datum of `[DRS, Theorem 1.3]` -/

/-- **The level package of the `√2` renormalization, for the level carrier.**

For every field satisfying the three multiscale-percolation hypotheses, this
datum supplies the long-crossing events `Cross`, the level dependence radii `Rk`,
the level sub-box centres `Sk`, and the five estimates the induction of
`Section9ChemicalAssembly.measure_le_sqrtTwoLevelBound` consumes, with the level
carrier `badLevelEvent` fixed:

* the **seed** `mu (Bad 0 x) ≤ exp (-4 c q)` — `[DRS, Lemmas 4.2, 4.4]`, whose
  probabilistic half is `Section9ChemicalSeed.measure_seedFailure_le` and whose
  combinatorial half needs S1/S2;
* the **exact finite-range independence** of the chosen level events, which is
  stronger than approximate P3 for the full good-site field;
* the **long-crossing bound** at rate `L_k ^ (3/2)` — `[DRS]` P1/P3;
* the **entropy count**, proved in
  `Section9ChemicalDRSConditions.card_separatedPairs_latticeBall_le_exp_sqrtTwoScheduleEntropy`
  once `Sk` is the lattice ball of sub-box centres;
* the **routing waypoints** of `[DRS, Theorem 3.1]`, in the reduced geometric
  form `ClusterAvoidingWaypoints` of `Section9ChemicalLevelCarrier`.

This uses, `[DRS, Theorems 1.3, 3.1]`. -/
def DRSLevelData (dim Cdep q0 Cbox : ℕ) (Cprob cprob c Clen Centropy : ℝ) : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsProbabilityMeasure mu] (E : ℕ → Lattice dim → Set Omega) (q : ℝ),
    (q0 : ℝ) ≤ q →
    (∀ j z, mu (E j z) ≤
      ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2)))) →
    IndependentEventScales mu E →
    MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E →
    TranslationInvariantEventLaw mu E →
    ∃ (Cross : ℕ → Lattice dim → Set Omega) (Rk : ℕ → ℕ)
      (Sk : ℕ → Lattice dim → Finset (Lattice dim)),
      (∀ x, mu (badLevelEvent E Cbox Clen 0 x) ≤
        ENNReal.ofReal (Real.exp (-(4 * c * q)))) ∧
      (∀ k, FiniteRangeIndependentEvents mu (Rk k) (badLevelEvent E Cbox Clen k)) ∧
      (∀ k x, mu (Cross k x) ≤
        ENNReal.ofReal (Real.exp (-(4 * c * q * Real.exp (3 / 2 * Real.sqrt 2 ^ k))))) ∧
      (∀ k x, (((separatedPairs (Rk k) (Sk k x)).card : ℕ) : ℝ) ≤
        Real.exp (sqrtTwoScheduleEntropy Centropy dim k)) ∧
      (∀ (k : ℕ) (x : Lattice dim) (L : ℕ), sqrtTwoScale (k + 1) ≤ (L : ℝ) →
        ∃ steps : ℕ, ∃ link : ℝ, 0 ≤ link ∧ (steps : ℝ) * link ≤ Clen * L ∧
          ClusterAvoidingWaypoints E Cbox Clen (badLevelEvent E Cbox Clen k)
            (sqrtTwoScale k) (Rk k) (Sk k x) (Cross k x) steps link x L)

/-! ## The chemical-distance bound, assembled -/

/-- **`uniform_chemical_distance_of_finite_range`, proved from `DRSLevelData`.**

Everything else the `√2` renormalization needs is proved: the level carrier
discharges `LevelToRadiusTransfer`, the routing waypoints discharge
`ClusteredBadForcing`, and the seed union bound discharges `SmallRadiusBound`. -/
theorem uniformChemicalDistanceBound_of_drsLevelData
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
    UniformChemicalDistanceBound d Cdep Cprob cprob := by
  have hClen0 : (0 : ℝ) ≤ Clen := by linarith
  refine uniformChemicalDistanceBound_of_levelData d Cdep q0 Cbox Cprob cprob c Cfail
    Clen Centropy hc (by linarith) hClen0 hCfail1 hCentropy hq0pos hq0 ?_
  intro Omega _ mu _ E q hq hprob hscales hrange hlaw
  obtain ⟨Cross, Rk, Sk, hseed, hindep, hcross, hcard, hroute⟩ :=
    hdata mu E q hq hprob hscales hrange hlaw
  have hqpos : 0 < q := lt_of_lt_of_le (by exact_mod_cast hq0pos) hq
  have hcp : 0 ≤ cprob * q := by
    have : 0 < cprob := lt_of_lt_of_le hc hccprob
    positivity
  refine ⟨badLevelEvent E Cbox Clen, Cross, Rk, Sk, hseed, hindep, hcross, hcard,
    fun k x => clusteredBadForcing_badLevelEvent (hroute k x),
    levelToRadiusTransfer_badLevelEvent E Cbox Clen, ?_⟩
  exact smallRadiusBound_of_multiscaleEventProbability hCbox hclen hCprob hqpos.le
    hc.le hccprob hcp (hq0seed q hq) hprob hCfail


/-! ## The windowed level datum, and the sharper assembly -/

/-- **A conditional level package for the windowed carrier.** The radii are
restricted to a schedule window, and the routing waypoints keep their link
radii in that window. This restriction does not localize the underlying
good-site or component events, so the exact independence field below is still
an assumption. `Section9ChemicalLocalCarrier` provides genuinely local
truncated and recursive events; their transfer to chemical failures remains
separate work. -/
def DRSWindowLevelData (dim Cdep q0 Cbox : ℕ) (Cprob cprob c Clen Centropy : ℝ) : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsProbabilityMeasure mu] (E : ℕ → Lattice dim → Set Omega) (q : ℝ),
    (q0 : ℝ) ≤ q →
    (∀ j z, mu (E j z) ≤
      ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2)))) →
    IndependentEventScales mu E →
    MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E →
    TranslationInvariantEventLaw mu E →
    ∃ (Cross : ℕ → Lattice dim → Set Omega) (Rk : ℕ → ℕ)
      (Sk : ℕ → Lattice dim → Finset (Lattice dim)),
      (∀ x, mu (badWindowEvent E Cbox Clen 0 x) ≤
        ENNReal.ofReal (Real.exp (-(4 * c * q)))) ∧
      (∀ k, FiniteRangeIndependentEvents mu (Rk k) (badWindowEvent E Cbox Clen k)) ∧
      (∀ k x, mu (Cross k x) ≤
        ENNReal.ofReal (Real.exp (-(4 * c * q * Real.exp (3 / 2 * Real.sqrt 2 ^ k))))) ∧
      (∀ k x, (((separatedPairs (Rk k) (Sk k x)).card : ℕ) : ℝ) ≤
        Real.exp (sqrtTwoScheduleEntropy Centropy dim k)) ∧
      (∀ (k : ℕ) (x : Lattice dim) (L : ℕ), sqrtTwoScale (k + 1) ≤ (L : ℝ) →
        (L : ℝ) < sqrtTwoScale (k + 2) →
        ∃ steps : ℕ, ∃ link : ℝ, 0 ≤ link ∧ (steps : ℝ) * link ≤ Clen * L ∧
          ClusterAvoidingWindowWaypoints E Cbox Clen (badWindowEvent E Cbox Clen k)
            (sqrtTwoScale k) (sqrtTwoScale (k + 1)) (Rk k) (Sk k x) (Cross k x)
            steps link x L)

/-- **`uniform_chemical_distance_of_finite_range` from the windowed level datum.** -/
theorem uniformChemicalDistanceBound_of_drsWindowLevelData
    (d Cdep q0 Cbox : ℕ) (Cprob cprob c Cfail Clen Centropy : ℝ)
    (hCbox : 1 ≤ Cbox) (hc : 0 < c) (hCprob : 0 ≤ Cprob)
    (hclen : 4 ≤ Clen) (hCfail1 : 1 ≤ Cfail) (hCentropy : 1 ≤ Centropy)
    (hccprob : c ≤ cprob) (hq0pos : 0 < q0)
    (hCfail : ((5 : ℝ) ^ d) * (2 * (Cprob * (((3 * Cbox) ^ d : ℕ) : ℝ))) ≤ Cfail)
    (hq0 : ∀ q : ℝ, (q0 : ℝ) ≤ q →
      2 * (Real.log Centropy + Real.log 2) + 2 * Real.sqrt 2 * d ≤ 4 * c * q)
    (hq0seed : ∀ q : ℝ, (q0 : ℝ) ≤ q →
      Real.log ((3 : ℝ) ^ d) + Real.log 2 ≤ cprob * q)
    (hdata : DRSWindowLevelData d Cdep q0 Cbox Cprob cprob c Clen Centropy) :
    UniformChemicalDistanceBound d Cdep Cprob cprob := by
  refine ⟨q0, Cbox, c, Cfail, Clen, hc, by linarith, by linarith, ?_⟩
  intro Omega _ mu _ E q hq hprob hscales hrange hlaw z L hL
  obtain ⟨Cross, Rk, Sk, hseed, hindep, hcross, hcard, hroute⟩ :=
    hdata mu E q hq hprob hscales hrange hlaw
  have hqpos : 0 < q := lt_of_lt_of_le (by exact_mod_cast hq0pos) hq
  have hcp : 0 ≤ cprob * q := by
    have : 0 < cprob := lt_of_lt_of_le hc hccprob
    positivity
  exact measure_chemicalDistanceFailureEvent_le_window (dim := d) (Centropy := Centropy)
    (Cross := Cross) (Rk := Rk) (Sk := Sk)
    hqpos hc hCfail1 hCentropy (hq0 q hq) hseed hindep hcross hcard
    (fun k x => clusteredBadForcing_badWindowEvent (hroute k x))
    (levelToRadiusWindowTransfer_badWindowEvent E Cbox Clen)
    (smallRadiusBound_of_multiscaleEventProbability hCbox hclen hCprob hqpos.le
      hc.le hccprob hcp (hq0seed q hq) hprob hCfail) z L hL

/-! ## The external inputs of the statement -/

/-- **The external imports of the multiscale percolation lemma.**

* `asdGeometry` — `[ASD, Lemma B.1(2),(3)]` with its two `O_Γ₁` tails and the
  dyadic chemical thresholds, in the *everywhere* form the statement asks
  for.  This is the field that carries the a.e.-versus-everywhere overreach
  discussed in the module docstring.
* `drsLevelData` — `[DRS, Theorem 1.3]`'s level package for the level carrier,
  resting on `DRSConditionP1`'s ergodicity, `DRSConditionP3`'s truncation
  construction, `TimarBoundaryInput` and `DRSConditionS2`'s ergodic step, and on
  `[DRS, Theorem 3.1]`'s routing. -/
structure PercolationExternalInputs (dim Cdep q0 L0 Cbox : ℕ)
    (Cprob cprob c C Clen Centropy : ℝ) : Prop where
  asdGeometry : ASDGeometryInput dim Cdep q0 L0 Cbox
    (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.section9CrossingSteps dim)
    Cprob cprob c C Clen
  drsLevelData : DRSLevelData dim Cdep q0 Cbox Cprob cprob c Clen Centropy

/-- **The provider theorem.**  The conclusion is the statement of
`SubdiffusiveProcess.Section9.weighted_multiscale_percolation`, verbatim. -/
theorem weighted_multiscale_percolation_of_external (d Cdep : ℕ)
    (Cprob cprob : ℝ) (_hCprob : 0 < Cprob) (_hcprob : 0 < cprob)
    {q0 L0 Cbox : ℕ} {c C Clen Centropy : ℝ}
    (hc : 0 < c) (hCpos : 0 < C) (hL0 : 1 ≤ L0) (hClen : 0 ≤ Clen)
    (hC1 : Real.log 2 ≤ C) (hC2 : 2 * Clen ≤ C)
    (h : PercolationExternalInputs d Cdep q0 L0 Cbox Cprob cprob c C Clen Centropy) :
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
          FiniteRangePercolationGeometry E Cbox
            (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.section9CrossingSteps d)
            c C q crossing component :=
  weightedMultiscalePercolation_of_inputs d Cdep q0 L0 Cbox Cprob cprob c C Clen
    hc hCpos hL0 hClen hC1 hC2 h.asdGeometry

/-- **Which external input is refuted.**  With `1 ≤ section9CrossingSteps d` and
`d ≥ 1`, `PercolationExternalInputs` is false — the `asdGeometry` field asks for
`[ASD, Lemma B.1]` at *every* sample, which the Dirac counterexample of
`Section9ChemicalRefutation` defeats. -/
theorem not_percolationExternalInputs_of_one_le_section9CrossingSteps
    {d Cdep q0 L0 Cbox : ℕ} (hd : 0 < d) {Cprob cprob c C Clen Centropy : ℝ}
    (hCprob : 0 < Cprob) (hcprob : 0 < cprob)
    (hc : 0 < c) (hCpos : 0 < C) (hL0 : 1 ≤ L0) (hClen : 0 ≤ Clen)
    (hC1 : Real.log 2 ≤ C) (hC2 : 2 * Clen ≤ C)
    (hstep : 1 ≤ SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.section9CrossingSteps d) :
    ¬ PercolationExternalInputs d Cdep q0 L0 Cbox Cprob cprob c C Clen Centropy := by
  intro h
  exact not_weightedMultiscalePercolation_of_one_le_section9CrossingSteps
    (Cdep := Cdep) hd Cprob cprob hstep
    (weighted_multiscale_percolation_of_external d Cdep Cprob cprob hCprob hcprob
      hc hCpos hL0 hClen hC1 hC2 h)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
