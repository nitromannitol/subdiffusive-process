module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalDRSConditions
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalWaypointChain
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalHeightTail
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section

variable {d : ℕ} {Ω : Type*}

/-! ## The level bound of the `√2` schedule -/



def sqrtTwoLevelBound (a Centropy : ℝ) (dim : ℕ) : ℕ → ℝ
  | 0 => Real.exp (-a)
  | k + 1 => Real.exp (sqrtTwoScheduleEntropy Centropy dim k) *
      (sqrtTwoLevelBound a Centropy dim k ^ 2 +
        Real.exp (-(a * Real.exp (3 / 2 * Real.sqrt 2 ^ k))))

theorem sqrtTwoLevelBound_nonneg (a Centropy : ℝ) (dim : ℕ) :
    ∀ k, 0 ≤ sqrtTwoLevelBound a Centropy dim k := by
  intro k
  induction k with
  | zero => exact (Real.exp_pos _).le
  | succ k ih =>
    rw [sqrtTwoLevelBound]
    have : 0 ≤ sqrtTwoLevelBound a Centropy dim k ^ 2 +
        Real.exp (-(a * Real.exp (3 / 2 * Real.sqrt 2 ^ k))) := by positivity
    positivity

/-- **The level induction.**  The forcing inclusion, the entropy count, the
finite-range independence of the level events and the crossing bound propagate
the seed bound along the `√2` schedule. -/
theorem measure_le_sqrtTwoLevelBound [MeasurableSpace Ω] {mu : Measure Ω}
    [IsProbabilityMeasure mu] {Bad Cross : ℕ → Lattice d → Set Ω} {Rk : ℕ → ℕ}
    {Sk : ℕ → Lattice d → Finset (Lattice d)} {a Centropy : ℝ} {dim : ℕ}
    (hCentropy : 1 ≤ Centropy)
    (hseed : ∀ x, mu (Bad 0 x) ≤ ENNReal.ofReal (Real.exp (-a)))
    (hindep : ∀ k, FiniteRangeIndependentEvents mu (Rk k) (Bad k))
    (hcross : ∀ k x, mu (Cross k x) ≤
      ENNReal.ofReal (Real.exp (-(a * Real.exp (3 / 2 * Real.sqrt 2 ^ k)))))
    (hcard : ∀ k x, (((separatedPairs (Rk k) (Sk k x)).card : ℕ) : ℝ) ≤
      Real.exp (sqrtTwoScheduleEntropy Centropy dim k))
    (hforce : ∀ k x,
      ClusteredBadForcing (Bad k) (Bad (k + 1) x) (Cross k x) (Rk k) (Sk k x)) :
    ∀ k x, mu (Bad k x) ≤ ENNReal.ofReal (sqrtTwoLevelBound a Centropy dim k) := by
  intro k
  induction k with
  | zero => exact hseed
  | succ k ih =>
    intro x
    have hstep := measure_le_ofReal_twoSeedStep_of_clusteredBadForcing
      (μ := mu) (Bad := Bad k) (Next := Bad (k + 1) x) (Cross := Cross k x)
      (R := Rk k) (S := Sk k x)
      (sqrtTwoLevelBound_nonneg a Centropy dim k)
      (sqrtTwoScheduleEntropy_nonneg hCentropy dim k)
      (Real.exp_nonneg _) (hindep k) ih (hcross k x) (hcard k x) (hforce k x)
    simpa [sqrtTwoLevelBound] using hstep

/-- The `q`-uniform rate of the level bound.  The threshold on `a = c q` is the
closed-form `q₀(d)` of `Section9ChemicalRenormalizationStep`. -/
theorem sqrtTwoLevelBound_le_exp_neg_half {a Centropy : ℝ} {dim : ℕ}
    (ha : 0 < a) (hC : 1 ≤ Centropy)
    (hq0 : 2 * (Real.log Centropy + Real.log 2) + 2 * Real.sqrt 2 * dim ≤ a) :
    ∀ k, sqrtTwoLevelBound a Centropy dim k ≤ Real.exp (-(a / 2 * 2 ^ k)) :=
  le_exp_neg_half_of_sqrtTwo_renormalization ha hC hq0
    (sqrtTwoLevelBound_nonneg a Centropy dim) le_rfl
    (fun k => le_of_eq (by rw [sqrtTwoLevelBound]))
    (fun k => two_mul_two_pow_le_exp_three_halves k)

/-- **The printed bound at an intermediate scale.**  At every `L ≥ e` there is a
schedule level below `L` whose unfavourable events are already smaller than
`exp (-(a/4) (log L) ^ 2)`. -/
theorem exists_level_measure_le_exp_neg_log_sq [MeasurableSpace Ω] {mu : Measure Ω}
    [IsProbabilityMeasure mu] {Bad Cross : ℕ → Lattice d → Set Ω} {Rk : ℕ → ℕ}
    {Sk : ℕ → Lattice d → Finset (Lattice d)} {a Centropy : ℝ} {dim : ℕ}
    (ha : 0 < a) (hCentropy : 1 ≤ Centropy)
    (hq0 : 2 * (Real.log Centropy + Real.log 2) + 2 * Real.sqrt 2 * dim ≤ a)
    (hseed : ∀ x, mu (Bad 0 x) ≤ ENNReal.ofReal (Real.exp (-a)))
    (hindep : ∀ k, FiniteRangeIndependentEvents mu (Rk k) (Bad k))
    (hcross : ∀ k x, mu (Cross k x) ≤
      ENNReal.ofReal (Real.exp (-(a * Real.exp (3 / 2 * Real.sqrt 2 ^ k)))))
    (hcard : ∀ k x, (((separatedPairs (Rk k) (Sk k x)).card : ℕ) : ℝ) ≤
      Real.exp (sqrtTwoScheduleEntropy Centropy dim k))
    (hforce : ∀ k x,
      ClusteredBadForcing (Bad k) (Bad (k + 1) x) (Cross k x) (Rk k) (Sk k x))
    {L : ℝ} (hL : Real.exp 1 ≤ L) :
    ∃ k : ℕ, sqrtTwoScale k ≤ L ∧
      ∀ x, mu (Bad k x) ≤
        ENNReal.ofReal (Real.exp (-(a / 4 * Real.log L ^ 2))) := by
  obtain ⟨k, hlevel, hbound⟩ :=
    exp_neg_log_sq_of_sqrtTwo_renormalization (p := sqrtTwoLevelBound a Centropy dim)
      ha hCentropy hq0 (sqrtTwoLevelBound_nonneg a Centropy dim) le_rfl
      (fun k => le_of_eq (by rw [sqrtTwoLevelBound])) hL
  refine ⟨k, hlevel, fun x => ?_⟩
  exact (measure_le_sqrtTwoLevelBound hCentropy hseed hindep hcross hcard hforce k x).trans
    (ENNReal.ofReal_le_ofReal hbound)

/-! ## The two remaining hypotheses, stated exactly -/

/-- **The level-to-radius transfer.**  The level-`k` unfavourable event dominates
the chemical-distance failure event at every radius above the level scale.

`[DRS, Theorem 1.3]` builds its level events so that this holds by construction;
taking `Bad k z = ⋃_{L : L_k ≤ L} D_L(z)` does the same here. -/
def LevelToRadiusTransfer (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (Clen : ℝ)
    (Bad : ℕ → Lattice d → Set Ω) : Prop :=
  ∀ (z : Lattice d) (L : ℕ) (k : ℕ), 1 ≤ L → sqrtTwoScale k ≤ (L : ℝ) →
    chemicalDistanceFailureEvent E Cbox Clen z L ⊆ Bad k z

/-- **The small-radius range.**  Below `e` the exponent `(log L) ^ 2` is at most
`1` and the level induction is silent; the estimate there comes from the
bad-site bound. -/
def SmallRadiusBound [MeasurableSpace Ω] (mu : Measure Ω)
    (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (Clen c Cfail q : ℝ) : Prop :=
  ∀ (z : Lattice d) (L : ℕ), 1 ≤ L → (L : ℝ) < Real.exp 1 →
    mu (chemicalDistanceFailureEvent E Cbox Clen z L) ≤
      ENNReal.ofReal (Cfail * Real.exp (-c * q * Real.log L ^ 2))

/-- **The chemical-distance estimate for one field.**  The level induction plus
the two hypotheses above give the printed bound at every radius `L ≥ 1`. -/
theorem measure_chemicalDistanceFailureEvent_le [MeasurableSpace Ω] {mu : Measure Ω}
    [IsProbabilityMeasure mu] {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ}
    {Bad Cross : ℕ → Lattice d → Set Ω} {Rk : ℕ → ℕ}
    {Sk : ℕ → Lattice d → Finset (Lattice d)} {Clen c Cfail q Centropy : ℝ}
    {dim : ℕ}
    (hq : 0 < q) (hc : 0 < c) (hCfail : 1 ≤ Cfail) (hCentropy : 1 ≤ Centropy)
    (hq0 : 2 * (Real.log Centropy + Real.log 2) + 2 * Real.sqrt 2 * dim ≤ 4 * c * q)
    (hseed : ∀ x, mu (Bad 0 x) ≤ ENNReal.ofReal (Real.exp (-(4 * c * q))))
    (hindep : ∀ k, FiniteRangeIndependentEvents mu (Rk k) (Bad k))
    (hcross : ∀ k x, mu (Cross k x) ≤
      ENNReal.ofReal (Real.exp (-(4 * c * q * Real.exp (3 / 2 * Real.sqrt 2 ^ k)))))
    (hcard : ∀ k x, (((separatedPairs (Rk k) (Sk k x)).card : ℕ) : ℝ) ≤
      Real.exp (sqrtTwoScheduleEntropy Centropy dim k))
    (hforce : ∀ k x,
      ClusteredBadForcing (Bad k) (Bad (k + 1) x) (Cross k x) (Rk k) (Sk k x))
    (htransfer : LevelToRadiusTransfer E Cbox Clen Bad)
    (hsmall : SmallRadiusBound mu E Cbox Clen c Cfail q)
    (z : Lattice d) (L : ℕ) (hL : 1 ≤ L) :
    mu (chemicalDistanceFailureEvent E Cbox Clen z L) ≤
      ENNReal.ofReal (Cfail * Real.exp (-c * q * Real.log L ^ 2)) := by
  rcases lt_or_ge (L : ℝ) (Real.exp 1) with hsmallL | hbigL
  · exact hsmall z L hL hsmallL
  · have ha : 0 < 4 * c * q := by positivity
    obtain ⟨k, hlevel, hbound⟩ :=
      exists_level_measure_le_exp_neg_log_sq (Bad := Bad) (Cross := Cross)
        (Rk := Rk) (Sk := Sk) (dim := dim) ha hCentropy hq0 hseed hindep hcross
        hcard hforce hbigL
    refine (measure_mono (htransfer z L k hL hlevel)).trans ((hbound z).trans ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    have heq : 4 * c * q / 4 * Real.log L ^ 2 = c * q * Real.log L ^ 2 := by ring
    have hCf : Real.exp (-(c * q * Real.log L ^ 2)) ≤
        Cfail * Real.exp (-c * q * Real.log L ^ 2) := by
      have h1 : Real.exp (-(c * q * Real.log L ^ 2)) =
          Real.exp (-c * q * Real.log L ^ 2) := by ring_nf
      rw [h1]
      nlinarith [Real.exp_pos (-c * q * Real.log L ^ 2)]
    rw [heq]
    exact hCf

/-! ## The chemical-distance input of the multiscale percolation lemma -/

/-- **`uniform_chemical_distance_of_finite_range`, assembled.**

`UniformChemicalDistanceBound` (`Section9ChemicalDistance`) is the `∃`-packaged,
field-uniform version of `measure_chemicalDistanceFailureEvent_le`.  This lemma
performs the packaging: it takes the constants and, for **every** field
satisfying the multiscale-percolation hypotheses, the level data and the two
remaining hypotheses, and returns the bound. -/
theorem uniformChemicalDistanceBound_of_levelData
    (d Cdep q0 Cbox : ℕ) (Cprob cprob c Cfail Clen Centropy : ℝ)
    (hc : 0 < c) (hCfail : 0 < Cfail) (hClen : 0 ≤ Clen) (hCfail1 : 1 ≤ Cfail)
    (hCentropy : 1 ≤ Centropy)
    (hq0pos : 0 < q0)
    (hq0 : ∀ q : ℝ, (q0 : ℝ) ≤ q →
      2 * (Real.log Centropy + Real.log 2) + 2 * Real.sqrt 2 * d ≤ 4 * c * q)
    (hdata : ∀ {Omega : Type} [MeasurableSpace Omega] (mu : Measure Omega)
      [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Omega) (q : ℝ),
      (q0 : ℝ) ≤ q →
      (∀ j z, mu (E j z) ≤
        ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2)))) →
      IndependentEventScales mu E →
      MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E →
      TranslationInvariantEventLaw mu E →
      ∃ (Bad Cross : ℕ → Lattice d → Set Omega) (Rk : ℕ → ℕ)
        (Sk : ℕ → Lattice d → Finset (Lattice d)),
        (∀ x, mu (Bad 0 x) ≤ ENNReal.ofReal (Real.exp (-(4 * c * q)))) ∧
        (∀ k, FiniteRangeIndependentEvents mu (Rk k) (Bad k)) ∧
        (∀ k x, mu (Cross k x) ≤
          ENNReal.ofReal (Real.exp (-(4 * c * q * Real.exp (3 / 2 * Real.sqrt 2 ^ k))))) ∧
        (∀ k x, (((separatedPairs (Rk k) (Sk k x)).card : ℕ) : ℝ) ≤
          Real.exp (sqrtTwoScheduleEntropy Centropy d k)) ∧
        (∀ k x, ClusteredBadForcing (Bad k) (Bad (k + 1) x) (Cross k x) (Rk k) (Sk k x)) ∧
        LevelToRadiusTransfer E Cbox Clen Bad ∧
        SmallRadiusBound mu E Cbox Clen c Cfail q) :
    UniformChemicalDistanceBound d Cdep Cprob cprob := by
  refine ⟨q0, Cbox, c, Cfail, Clen, hc, hCfail, hClen, ?_⟩
  intro Omega _ mu _ E q hq hprob hscales hrange hlaw z L hL
  obtain ⟨Bad, Cross, Rk, Sk, hseed, hindep, hcross, hcard, hforce, htransfer, hsmall⟩ :=
    hdata mu E q hq hprob hscales hrange hlaw
  have hqpos : 0 < q := lt_of_lt_of_le (by exact_mod_cast hq0pos) hq
  exact measure_chemicalDistanceFailureEvent_le (dim := d) (Centropy := Centropy)
    hqpos hc hCfail1 hCentropy (hq0 q hq) hseed hindep hcross hcard hforce
    htransfer hsmall z L hL






def ASDGeometryInput (dim Cdep q0 L0 Cbox J : ℕ) (Cprob cprob c C Clen : ℝ) : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsProbabilityMeasure mu] (E : ℕ → Lattice dim → Set Omega) (q : ℝ),
    (q0 : ℝ) ≤ q →
    (∀ j z, mu (E j z) ≤
      ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2)))) →
    IndependentEventScales mu E →
    MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E →
    TranslationInvariantEventLaw mu E →
    ∃ crossing component : Lattice dim → Omega → ℕ,
      (∀ z omega, 1 ≤ crossing z omega) ∧
      (∀ z omega, 1 ≤ component z omega) ∧
      (∀ z, SubdiffusiveProcess.OGammaLE mu 1 (C / q) (fun omega => (crossing z omega : ℝ) - L0)) ∧
      (∀ z, SubdiffusiveProcess.OGammaLE mu 1 (C / q) (fun omega => (component z omega : ℝ) - 1)) ∧
      (∀ (omega : Omega) (z : Lattice dim), ∀ l : ℕ, crossing z omega ≤ l →
        ∀ path : List (Lattice dim), IsJStepListPath J path →
        (∃ v ∈ path, InLatticeBallReal z v (l / 3 : ℝ)) →
        (∃ v ∈ path, ¬ InLatticeBallReal z v (2 * l / 3 : ℝ)) →
        ∃ chosen : List (Lattice dim),
          chosen.Sublist path ∧ c * l ≤ chosen.length ∧
            (∀ v ∈ chosen,
              IsPercolationGoodSite E Cbox omega v ∧
                latticeBallSet v Cbox ⊆
                  latticeBallSet z (3 * l / 4 : ℝ) \ latticeBallSet z (l / 4 : ℝ)) ∧
            chosen.Pairwise fun v w ↦
              Disjoint (latticeBallSet v Cbox) (latticeBallSet w Cbox)) ∧
      (∀ (omega : Omega) (z : Lattice dim), ∀ s : ℝ, 0 ≤ s → ∀ v : Lattice dim,
        InLatticeBallReal z v s → ¬ IsPercolationGoodSite E Cbox omega v →
        HasLatticeDiameterAtMost
          (jStepComponent J {u | ¬ IsPercolationGoodSite E Cbox omega u} v)
          (C * (1 + component z omega + q⁻¹ * Real.log (2 + s)) ^ 2)) ∧
      (∀ (omega : Omega) (z : Lattice dim) (n : ℕ), component z omega ≤ n →
        omega ∉ chemicalDistanceFailureEvent E Cbox Clen z (2 ^ n))



theorem weightedMultiscalePercolation_of_inputs
    (dim Cdep q0 L0 Cbox : ℕ) (Cprob cprob c C Clen : ℝ)
    (hc : 0 < c) (hCpos : 0 < C) (hL0 : 1 ≤ L0) (hClen : 0 ≤ Clen)
    (hC1 : Real.log 2 ≤ C) (hC2 : 2 * Clen ≤ C)
    (hinput : ASDGeometryInput dim Cdep q0 L0 Cbox
      (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.section9CrossingSteps dim)
      Cprob cprob c C Clen) :
    ∃ q0' L0' Cbox' : ℕ, ∃ c' C' : ℝ,
      0 < c' ∧ 0 < C' ∧ 1 ≤ L0' ∧
      ∀ {Omega : Type} [MeasurableSpace Omega] (mu : Measure Omega)
        [IsProbabilityMeasure mu] (E : ℕ → Lattice dim → Set Omega) (q : ℝ),
        (q0' : ℝ) ≤ q →
        (∀ j z, mu (E j z) ≤
          ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2)))) →
        IndependentEventScales mu E →
        MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E →
        TranslationInvariantEventLaw mu E →
        ∃ crossing component : Lattice dim → Omega → ℕ,
          (∀ z omega, 1 ≤ crossing z omega) ∧
          (∀ z omega, 1 ≤ component z omega) ∧
          (∀ z, SubdiffusiveProcess.OGammaLE mu 1 (C' / q) (fun omega => (crossing z omega : ℝ) - L0')) ∧
          (∀ z, SubdiffusiveProcess.OGammaLE mu 1 (C' / q) (fun omega => (component z omega : ℝ) - 1)) ∧
          FiniteRangePercolationGeometry E Cbox'
            (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.section9CrossingSteps dim)
            c' C' q crossing component := by
  refine ⟨q0, L0, Cbox, c, C, hc, hCpos, hL0, ?_⟩
  intro Omega _ mu _ E q hq hprob hscales hrange hlaw
  obtain ⟨crossing, component, hcr1, hco1, hcrTail, hcoTail, hcross, hbad, hheight⟩ :=
    hinput mu E q hq hprob hscales hrange hlaw
  exact ⟨crossing, component, hcr1, hco1, hcrTail, hcoTail,
    finiteRangePercolationGeometry_of_chemicalDistanceThresholds
      hc hClen hC1 hC2 hcross hbad hheight⟩


end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
