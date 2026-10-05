module

public import SubdiffusiveProcess.Paper.prop_response_compact
public import SubdiffusiveProcess.Lnorm.KilledResponsePotential

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess.Paper

local instance aux_response_l1_compact_of_band_fact : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 1) :=
  ⟨by norm_num⟩

/-- Arbitrary-cube `L¹` compactness for a countable family of positive responses. The moment
and band inputs have the forms supplied by `rem_bank_response_moments` and `prop_16`. -/
theorem response_l1_compact_of_band
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (Idx : Type) [Countable Idx]
    (R : Idx → Response (centeredCube z r hr))
    (Cmom Cband : Idx → ℝ) (aD : ℝ)
    (hCmom : ∀ i, 0 ≤ Cmom i) (hCband : ∀ i, 0 ≤ Cband i) (haD : 0 < aD)
    (hmem6 : ∀ i N,
      MemLp (SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr (R i) M H N)
        (ENNReal.ofReal 6) (chaosSampleLaw M).toMeasure)
    (hmom6 : ∀ i N,
      eLpNorm (SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr (R i) M H N)
        (ENNReal.ofReal 6) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cmom i))
    (hband2 : ∀ i h N,
      eLpNorm
        (fun omega =>
          SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr (R i) M H N omega -
            (((chaosSampleLaw M).toMeasure)[
              SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr (R i) M H N |
              bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]) omega)
        (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (Cband i * M.delta * (3 : ℝ) ^ (-aD * (h : ℝ)))) :
    (∀ i N,
      MemLp (SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr (R i) M H N)
        1 (chaosSampleLaw M).toMeasure) ∧
    (∀ i, IsCompact (closure (Set.range (fun N =>
      ((hmem6 i N).mono_exponent (by norm_num : ENNReal.ofReal 1 ≤ ENNReal.ofReal 6)).toLp
        (SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr (R i) M H N))))) := by
  classical
  let q : ℝ≥0∞ := ENNReal.ofReal 6
  let p : ℝ≥0∞ := ENNReal.ofReal 1
  let laws := SubdiffusiveProcess.Lnorm.regroup_laws M
  let Rf : Idx → ℕ → ((j : ℤ) → SubdiffusiveProcess.Lnorm.regroup_Y d j) → ℝ :=
    fun i N => SubdiffusiveProcess.Lnorm.potentialResponseProxy z r hr (R i) M N
  let Pm : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  let Gpol : Empty → ℕ → ((j : ℤ) → SubdiffusiveProcess.Lnorm.regroup_Y d j) → ℝ :=
    fun e _ _ => Empty.elim e
  have : Fact (1 ≤ p) := ⟨by norm_num [p]⟩
  have hpq : p < q := by norm_num [p, q]
  have hqtop : q ≠ ⊤ := by norm_num [q]
  have hdisorder : 0 < M.delta := M.shellPrefix.delta_pos
  have hproxyMom : ∀ i N,
      MemLp (Rf i N) q (Measure.infinitePi laws) ∧
      eLpNorm (Rf i N) q (Measure.infinitePi laws) ≤ ENNReal.ofReal (Cmom i) := by
    intro i N
    simpa [Rf, q, laws, Pm] using
      (SubdiffusiveProcess.Lnorm.responseProxy_moments z r hr (R i) M H hH
        (ENNReal.ofReal 6) N (Cmom i) (hCmom i) (hmem6 i N) (hmom6 i N))
  have hproxyBand : ∀ i h N,
      eLpNorm
        (fun y => Rf i N y -
          ((Measure.infinitePi laws)[Rf i N | bandSigma (SubdiffusiveProcess.Lnorm.regroup_Y d) h]) y)
        p (Measure.infinitePi laws) ≤
        ENNReal.ofReal (Cband i * M.delta * (3 : ℝ) ^ (-aD * (h : ℝ))) := by
    intro i h N
    have hband := SubdiffusiveProcess.Lnorm.responseProxy_band z r hr (R i) M H hH
      (Cband i) aD (Cmom i) (fun n => hmem6 i n)
      (fun Hband n => hband2 i Hband n) h N
    have hmeas : AEStronglyMeasurable
        (fun y => Rf i N y -
          ((Measure.infinitePi laws)[Rf i N | bandSigma (SubdiffusiveProcess.Lnorm.regroup_Y d) h]) y)
        (Measure.infinitePi laws) :=
      (hproxyMom i N).1.aestronglyMeasurable.sub
        (stronglyMeasurable_condExp.aestronglyMeasurable.mono (bandSigma_le h))
    have hlow : p ≤ ENNReal.ofReal 2 := by norm_num [p]
    have hcontract := eLpNorm_le_eLpNorm_of_exponent_le (μ := Measure.infinitePi laws) (f := fun y => Rf i N y - ((Measure.infinitePi laws)[Rf i N | bandSigma (SubdiffusiveProcess.Lnorm.regroup_Y d) h]) y) hlow
    simpa [Rf, p, laws] using hcontract.trans hband
  have hproxySplit : ∀ i Hband,
      ∃ (X : Type) (_ : MetricSpace X) (_ : TopologicalSpace.SeparableSpace X)
        (_ : MeasurableSpace X) (_ : BorelSpace X) (Q : Opens (SpatialCoordinates d))
        (R' : Response Q)
        (V : ((j : bandSet Hband) → SubdiffusiveProcess.Lnorm.regroup_Y d j.1) → X)
        (psi : X → Potential Q)
        (tail : ℕ → ((j : {j : ℤ // j ∉ bandSet Hband}) →
          SubdiffusiveProcess.Lnorm.regroup_Y d j.1) → Potential Q),
        Measurable V ∧ LipschitzWith 1 psi ∧
        (∀ N, Hband ≤ N → Measurable (fun w : X ×
          ((j : {j : ℤ // j ∉ bandSet Hband}) → SubdiffusiveProcess.Lnorm.regroup_Y d j.1) =>
            R'.eval (psi w.1 + tail N w.2))) ∧
      (∀ N, Hband ≤ N → ∀ omg : (j : ℤ) → SubdiffusiveProcess.Lnorm.regroup_Y d j,
          Rf i N omg = R'.eval (psi (V (fun j => omg j.1)) + tail N (fun j => omg j.1))) := by
    intro i Hband
    change ∃ (X : Type) (_ : MetricSpace X) (_ : TopologicalSpace.SeparableSpace X)
      (_ : MeasurableSpace X) (_ : BorelSpace X) (Q : Opens (SpatialCoordinates d))
      (R' : Response Q)
      (V : ((j : bandSet Hband) → SubdiffusiveProcess.Lnorm.regroup_Y d j.1) → X)
      (psi : X → Potential Q)
      (tail : ℕ → ((j : {j : ℤ // j ∉ bandSet Hband}) →
        SubdiffusiveProcess.Lnorm.regroup_Y d j.1) → Potential Q),
      Measurable V ∧ LipschitzWith 1 psi ∧
      (∀ N, Hband ≤ N → Measurable (fun w : X ×
        ((j : {j : ℤ // j ∉ bandSet Hband}) → SubdiffusiveProcess.Lnorm.regroup_Y d j.1) =>
          R'.eval (psi w.1 + tail N w.2))) ∧
      (∀ N, Hband ≤ N → ∀ omg : (j : ℤ) → SubdiffusiveProcess.Lnorm.regroup_Y d j,
        Rf i N omg = R'.eval (psi (V (fun j => omg j.1)) + tail N (fun j => omg j.1)))
    exact SubdiffusiveProcess.Lnorm.responseProxy_hsplit z r hr (R i) M Hband
  have hcompactAll := _root_.SubdiffusiveProcess.Paper.prop_response_compact d
    (SubdiffusiveProcess.Lnorm.regroup_Y d) laws Idx Empty Rf Gpol p q hpq hqtop
    aD M.delta haD hdisorder Cband hCband
    (fun i => ENNReal.ofReal (Cmom i)) (fun _ => ENNReal.ofReal_ne_top)
    (fun i N => (hproxyMom i N).1) (fun i N => (hproxyMom i N).2)
    (fun i Hband N _ => by simpa only [neg_mul] using hproxyBand i Hband N)
    hproxySplit (fun e => Empty.elim e) (fun e => Empty.elim e)
    (fun e _ _ => Empty.elim e)
  have hRDmem1 : ∀ i N,
      MemLp (SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr (R i) M H N)
        p Pm := by
    intro i N
    exact (hmem6 i N).mono_exponent (by norm_num [p, q])
  have hRfmem1 : ∀ i N, MemLp (Rf i N) p (Measure.infinitePi laws) := by
    intro i N
    exact (hproxyMom i N).1.mono_exponent (by norm_num [p, q])
  have htransported : ∀ i,
      IsCompact (closure (Set.range (fun N => (hRDmem1 i N).toLp
        (SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr (R i) M H N)))) := by
    intro i
    exact SubdiffusiveProcess.Lnorm.responseProxy_compact_transport z r hr (R i) M H hH
      (p := p) (fun N => hRDmem1 i N) (fun N => hRfmem1 i N) (hcompactAll.1 i)
  constructor
  · intro i N
    simpa [p, Pm] using hRDmem1 i N
  · intro i
    have hEq : (fun N => (hRDmem1 i N).toLp
        (SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr (R i) M H N)) =
        (fun N => ((hmem6 i N).mono_exponent (by norm_num [p, q] : p ≤ q)).toLp
          (SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr (R i) M H N)) := by
      funext N
      apply Lp.ext
      filter_upwards [(hRDmem1 i N).coeFn_toLp,
        ((hmem6 i N).mono_exponent (by norm_num [p, q] : p ≤ q)).coeFn_toLp] with omega hleft hright
      calc
        _ = SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr (R i) M H N omega := hleft
        _ = _ := hright.symm
    rw [← hEq]
    simpa [p] using htransported i

end SubdiffusiveProcess.Paper
