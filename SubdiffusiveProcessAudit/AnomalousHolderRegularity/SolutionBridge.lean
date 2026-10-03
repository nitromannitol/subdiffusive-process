module
public import SubdiffusiveProcess.Paper.t_C
public import SubdiffusiveProcessAudit.AnomalousHolderRegularity.SolutionBasic
@[expose] public section
noncomputable section
namespace SubdiffusiveProcessAudit.AnomalousHolderRegularity
open MeasureTheory Filter Topology
open _root_.SubdiffusiveProcessAudit.AnomalousHolderRegularity.SubdiffusiveProcess.Frozen.Assumptions

theorem localSigma_eq {d : ℕ} (U : Set (Homogenization.Vec d)) :
    PotentialField.localSigma U = _root_.SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma U := by
  unfold PotentialField.localSigma _root_.SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma
    Homogenization.LocalSigmaR _root_.Homogenization.LocalSigmaR
  rw [MeasurableSpace.comap_generateFrom, MeasurableSpace.comap_generateFrom]
  congr 1
  ext s
  constructor
  · rintro ⟨t, ⟨i, j, phi, hphi, hsupp, r, hr, rfl⟩, rfl⟩
    exact ⟨_root_.Homogenization.entryTestR i j phi ⁻¹' r,
      ⟨i, j, phi, ⟨hphi.measurable, hphi.bounded, hphi.hasCompactSupport⟩, hsupp, r, hr, rfl⟩, rfl⟩
  · rintro ⟨t, ⟨i, j, phi, hphi, hsupp, r, hr, rfl⟩, rfl⟩
    exact ⟨Homogenization.entryTestR i j phi ⁻¹' r,
      ⟨i, j, phi, ⟨hphi.measurable, hphi.bounded, hphi.hasCompactSupport⟩, hsupp, r, hr, rfl⟩, rfl⟩

theorem partialSumField_eq {d : ℕ} (omega : PotentialSample d) (L : ℕ) :
    anchoredPartialSumField omega L = _root_.SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField omega L := by
  induction L with
  | zero => rfl
  | succ L ih =>
      simp only [anchoredPartialSumField,
        _root_.SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField, ih]
      rfl

abbrev OriginalModel (d : ℕ) := _root_.SubdiffusiveProcess.Frozen.Assumptions.GMCModel d

def toModel {d : ℕ} (M : GMCModel d) : OriginalModel d where
  delta := M.delta
  P := M.P
  shellPrefix := ⟨M.shellPrefix.dimension, M.shellPrefix.delta_pos,
    M.shellPrefix.delta_le_half, M.shellPrefix.independent, M.shellPrefix.marginal_scaling⟩
  G1 := ⟨M.G1.integrable, M.G1.mean_zero, M.G1.stationary, by
    intro U V hU hV hUV
    rw [← localSigma_eq U, ← localSigma_eq V]
    exact M.G1.range_dependence U V hU hV hUV⟩
  G2 := ⟨M.G2.regularity_expectation⟩
  G3 := ⟨M.G3.signed_coordinate_permutations, M.G3.negation⟩
  G4 := ⟨M.G4.exponential_integrable, M.G4.tauSq_pos⟩

theorem toLimit {d : ℕ} {omega : PotentialSample d} {g : PotentialField d}
    (h : IsAnchoredC11Limit omega g) :
    _root_.SubdiffusiveProcess.Frozen.Assumptions.IsAnchoredC11Limit omega g :=
  ⟨h.value_tendsto, by simpa only [partialSumField_eq, PotentialField.deriv, _root_.SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv] using! h.deriv_tendsto,
    by simpa only [partialSumField_eq, PotentialField.deriv, _root_.SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv, LipschitzSeminormCauchyOn, _root_.SubdiffusiveProcess.Frozen.Assumptions.LipschitzSeminormCauchyOn] using! h.deriv_lipschitz_cauchy, h.anchored⟩

theorem fromLimit {d : ℕ} {omega : PotentialSample d} {g : PotentialField d}
    (h : _root_.SubdiffusiveProcess.Frozen.Assumptions.IsAnchoredC11Limit omega g) :
    IsAnchoredC11Limit omega g :=
  ⟨h.value_tendsto, by simpa only [partialSumField_eq, PotentialField.deriv, _root_.SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv] using! h.deriv_tendsto,
    by simpa only [partialSumField_eq, PotentialField.deriv, _root_.SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv, LipschitzSeminormCauchyOn, _root_.SubdiffusiveProcess.Frozen.Assumptions.LipschitzSeminormCauchyOn] using! h.deriv_lipschitz_cauchy, h.anchored⟩

theorem goodSet_eq (d : ℕ) :
    anchoredC11GoodSet d = _root_.SubdiffusiveProcess.Frozen.Assumptions.anchoredC11GoodSet d := by
  ext omega
  constructor
  · rintro ⟨g, hg, huniq⟩
    exact ⟨g, toLimit hg, fun g' hg' => huniq g' (fromLimit hg')⟩
  · rintro ⟨g, hg, huniq⟩
    exact ⟨g, fromLimit hg, fun g' hg' => huniq g' (toLimit hg')⟩


abbrev RootSample (d : ℕ) := _root_.SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d

def subtypeEquiv {α : Type*} [MeasurableSpace α] (s t : Set α) (h : s = t) : s ≃ᵐ t where
  toFun omega := ⟨omega.1, by rw [← h]; exact omega.2⟩
  invFun omega := ⟨omega.1, by rw [h]; exact omega.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := measurable_subtype_coe.subtype_mk
  measurable_invFun := measurable_subtype_coe.subtype_mk

theorem subtypeEquiv_map_comap {α : Type*} [MeasurableSpace α]
    (s t : Set α) (h : s = t) (μ : Measure α) :
    Measure.map (subtypeEquiv s t h) (Measure.comap (Subtype.val : s → α) μ) =
    Measure.comap (Subtype.val : t → α) μ := by
  subst t
  exact Measure.map_id

def sampleEquiv (d : ℕ) : AnchoredC11Sample d ≃ᵐ RootSample d :=
  subtypeEquiv _ _ (goodSet_eq d)

theorem sampleLaw_map (d : ℕ) (μ : Measure (PotentialSample d)) :
    Measure.map (sampleEquiv d) (Measure.comap (Subtype.val : AnchoredC11Sample d → PotentialSample d) μ) =
    Measure.comap (Subtype.val : RootSample d → PotentialSample d) μ :=
  subtypeEquiv_map_comap _ _ (goodSet_eq d) μ

theorem anchoredLog_eq {d : ℕ} (omega : AnchoredC11Sample d) :
    anchoredLog omega = _root_.SubdiffusiveProcess.Frozen.Assumptions.anchoredLog (sampleEquiv d omega) := by
  apply omega.property.unique
  · exact Classical.choose_spec omega.property.exists
  · exact fromLimit (Classical.choose_spec (sampleEquiv d omega).property.exists)

theorem coefficientAt_eq {d : ℕ} (M : GMCModel d) (L : WithTop ℕ) (omega : AnchoredC11Sample d) :
    SubdiffusiveProcess.CoarseGrainingVocab.coefficientAt M L omega =
    _root_.SubdiffusiveProcess.CoarseGrainingVocab.coefficientAt (toModel M) L (sampleEquiv d omega) := by
  cases L with
  | top =>
    funext x
    exact congrArg (fun g : PotentialField d => Real.exp (g x)) (anchoredLog_eq omega)
  | coe n => rfl

def toH1 {d : ℕ} {U : Set (Homogenization.Vec d)} (u : Homogenization.H1Function U) :
    _root_.Homogenization.H1Function U :=
  ⟨u.toFun, u.grad, u.memL2, u.gradMemL2, u.hasWeakGradient⟩

def fromH1 {d : ℕ} {U : Set (Homogenization.Vec d)} (u : _root_.Homogenization.H1Function U) :
    Homogenization.H1Function U :=
  ⟨u.toFun, u.grad, u.memL2, u.gradMemL2, u.hasWeakGradient⟩

def toH10 {d : ℕ} {U : Set (Homogenization.Vec d)} (u : Homogenization.H10Function U) :
    _root_.Homogenization.H10Function U :=
  ⟨toH1 u.toH1Function, u.approx, u.approx_smooth, u.approx_hasCompactSupport,
    u.approx_support_subset, u.tendsto_approx, u.tendsto_approx_grad⟩

def fromH10 {d : ℕ} {U : Set (Homogenization.Vec d)} (u : _root_.Homogenization.H10Function U) :
    Homogenization.H10Function U :=
  ⟨fromH1 u.toH1Function, u.approx, u.approx_smooth, u.approx_hasCompactSupport,
    u.approx_support_subset, u.tendsto_approx, u.tendsto_approx_grad⟩

theorem harmonic_eq {d : ℕ} (a : Homogenization.Vec d → ℝ) (U : Set (Homogenization.Vec d))
    (u : Homogenization.H1Function U) :
    SubdiffusiveProcess.CoarseGrainingVocab.IsWeaklyHarmonicOn a U u ↔
    _root_.SubdiffusiveProcess.CoarseGrainingVocab.IsWeaklyHarmonicOn a U (toH1 u) := by
  constructor
  · intro h phi
    exact h (fromH10 phi)
  · intro h phi
    exact h (toH10 phi)

end SubdiffusiveProcessAudit.AnomalousHolderRegularity

namespace SubdiffusiveProcessAuditOriginalAnomalousHolderRegularity
open Filter SubdiffusiveProcess SubdiffusiveProcess.Frozen.Assumptions MeasureTheory ProbabilityTheory
open Homogenization
open Set
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology

def RootConclusion (d : ℕ) : Prop :=
  ∃ delta0 C0 C : ℝ, 0 < delta0 ∧ 0 < C0 ∧ 0 < C ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 →
        let mu := Measure.comap (Subtype.val : AnchoredC11Sample d → PotentialSample d) M.P.toMeasure
        gammaReg C0 M.delta ∈ Set.Ioo (1 / 2 : ℝ) 1 ∧
        ∀ gamma ∈ Set.Icc (1 / 2 : ℝ) (gammaReg C0 M.delta),
          ∃ Lscale : WithTop ℕ → ℕ → AnchoredC11Sample d → ℕ,
            (∀ (L : WithTop ℕ) (m : ℕ), Measurable (Lscale L m)) ∧
            (∀ (L : WithTop ℕ) (m k : ℕ), 0 < k →
              mu {omega | k < Lscale L m omega} ≤
                ENNReal.ofReal (C * Real.exp (
                  -((1 - gamma) ^ 2 * max ((k : ℝ) - C) 0) /
                    (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
            ∀ᵐ omega ∂mu,
              (∀ (L : WithTop ℕ) (m : ℕ), 0 < m →
                ∀ u : H1Function (openCubeSet (originCube d m)),
                  IsWeaklyHarmonicOn (coefficientAt M L omega) (cube d m) u →
                  ∀ n : ℕ, (n : ℤ) ≤ (m : ℤ) - (Lscale L m omega : ℤ) →
                    ∀ z : Homogenization.Vec d, OnTriadicGrid n z →
                    translatedCube d n z ⊆ cube d (m - 1) →
                      normalizedL2On (translatedCube d n z)
                          (fun x => u.toFun x - averageOn (translatedCube d n z) u.toFun) ≤
                        C * (3 : ℝ) ^ (-gamma * ((m : ℝ) - (n : ℝ))) *
                          normalizedL2On (cube d m)
                            (fun x => u.toFun x - averageOn (cube d m) u.toFun) ∧
                      vectorNormalizedL2On (translatedCube d n z)
                          (fun x => Real.sqrt (coefficientAt M L omega x) • u.grad x) ≤
                        C * (3 : ℝ) ^ ((1 - gamma) * ((m : ℝ) - (n : ℝ))) *
                          vectorNormalizedL2On (cube d m)
                            (fun x => Real.sqrt (coefficientAt M L omega x) • u.grad x)) ∧
              (∀ (L : WithTop ℕ) (u : Homogenization.Vec d → ℝ),
                (∀ m : ℤ, ∃ um : H1Function (openCubeSet (originCube d m)),
                  (∀ x, um.toFun x = u x) ∧
                    IsWeaklyHarmonicOn (coefficientAt M L omega) (cube d m) um) →
                (∀ eps > 0, ∃ᶠ R : ℝ in atTop, R ^ (-gammaReg C0 M.delta) *
                    sInf {r : ℝ | ∃ c : ℝ,
                      r = normalizedL2On (Metric.ball (0 : Homogenization.Vec d) R) (fun x => u x - c)} < eps) →
                ∃ uRep : Homogenization.Vec d → ℝ,
                  Continuous uRep ∧ uRep =ᵐ[volume] u ∧
                  (∀ m : ℤ, ∀ um : H1Function (openCubeSet (originCube d m)),
                    (∀ x, um.toFun x = u x) →
                    IsWeaklyHarmonicOn (coefficientAt M L omega) (cube d m) um →
                    uRep =ᵐ[volume.restrict (openCubeSet (originCube d m))] um.toFun) ∧
                  ∃ c : ℝ, ∀ x, uRep x = c)

end SubdiffusiveProcessAuditOriginalAnomalousHolderRegularity
namespace SubdiffusiveProcessAudit.AnomalousHolderRegularity
open Filter _root_.SubdiffusiveProcessAudit.AnomalousHolderRegularity.SubdiffusiveProcess
open _root_.SubdiffusiveProcessAudit.AnomalousHolderRegularity.SubdiffusiveProcess.Frozen.Assumptions MeasureTheory ProbabilityTheory
open _root_.SubdiffusiveProcessAudit.AnomalousHolderRegularity.Homogenization
open Set
open _root_.SubdiffusiveProcessAudit.AnomalousHolderRegularity.SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology

theorem transferC (d : ℕ) (h : SubdiffusiveProcessAuditOriginalAnomalousHolderRegularity.RootConclusion d) :
  ∃ delta0 C0 C : ℝ, 0 < delta0 ∧ 0 < C0 ∧ 0 < C ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 →
        let mu := Measure.comap (Subtype.val : AnchoredC11Sample d → PotentialSample d) M.P.toMeasure
        gammaReg C0 M.delta ∈ Set.Ioo (1 / 2 : ℝ) 1 ∧
        ∀ gamma ∈ Set.Icc (1 / 2 : ℝ) (gammaReg C0 M.delta),
          ∃ Lscale : WithTop ℕ → ℕ → AnchoredC11Sample d → ℕ,
            (∀ (L : WithTop ℕ) (m : ℕ), Measurable (Lscale L m)) ∧
            (∀ (L : WithTop ℕ) (m k : ℕ), 0 < k →
              mu {omega | k < Lscale L m omega} ≤
                ENNReal.ofReal (C * Real.exp (
                  -((1 - gamma) ^ 2 * max ((k : ℝ) - C) 0) /
                    (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
            ∀ᵐ omega ∂mu,
              (∀ (L : WithTop ℕ) (m : ℕ), 0 < m →
                ∀ u : H1Function (openCubeSet (originCube d m)),
                  IsWeaklyHarmonicOn (coefficientAt M L omega) (cube d m) u →
                  ∀ n : ℕ, (n : ℤ) ≤ (m : ℤ) - (Lscale L m omega : ℤ) →
                    ∀ z : Homogenization.Vec d, OnTriadicGrid n z →
                    translatedCube d n z ⊆ cube d (m - 1) →
                      normalizedL2On (translatedCube d n z)
                          (fun x => u.toFun x - averageOn (translatedCube d n z) u.toFun) ≤
                        C * (3 : ℝ) ^ (-gamma * ((m : ℝ) - (n : ℝ))) *
                          normalizedL2On (cube d m)
                            (fun x => u.toFun x - averageOn (cube d m) u.toFun) ∧
                      vectorNormalizedL2On (translatedCube d n z)
                          (fun x => Real.sqrt (coefficientAt M L omega x) • u.grad x) ≤
                        C * (3 : ℝ) ^ ((1 - gamma) * ((m : ℝ) - (n : ℝ))) *
                          vectorNormalizedL2On (cube d m)
                            (fun x => Real.sqrt (coefficientAt M L omega x) • u.grad x)) ∧
              (∀ (L : WithTop ℕ) (u : Homogenization.Vec d → ℝ),
                (∀ m : ℤ, ∃ um : H1Function (openCubeSet (originCube d m)),
                  (∀ x, um.toFun x = u x) ∧
                    IsWeaklyHarmonicOn (coefficientAt M L omega) (cube d m) um) →
                (∀ eps > 0, ∃ᶠ R : ℝ in atTop, R ^ (-gammaReg C0 M.delta) *
                    sInf {r : ℝ | ∃ c : ℝ,
                      r = normalizedL2On (Metric.ball (0 : Homogenization.Vec d) R) (fun x => u x - c)} < eps) →
                ∃ uRep : Homogenization.Vec d → ℝ,
                  Continuous uRep ∧ uRep =ᵐ[volume] u ∧
                  (∀ m : ℤ, ∀ um : H1Function (openCubeSet (originCube d m)),
                    (∀ x, um.toFun x = u x) →
                    IsWeaklyHarmonicOn (coefficientAt M L omega) (cube d m) um →
                    uRep =ᵐ[volume.restrict (openCubeSet (originCube d m))] um.toFun) ∧
                  ∃ c : ℝ, ∀ x, uRep x = c) := by
  rcases h with ⟨delta0, C0, C, hd0, hC0, hC, hmain⟩
  refine ⟨delta0, C0, C, hd0, hC0, hC, ?_⟩
  intro M hM
  rcases hmain (toModel M) hM with ⟨hgamma, hscales⟩
  refine ⟨hgamma, ?_⟩
  intro gamma hgamma
  rcases hscales gamma hgamma with ⟨l, hlmeas, hltail, hreg⟩
  refine ⟨fun L m omega => l L m (sampleEquiv d omega),
    fun L m => (hlmeas L m).comp (sampleEquiv d).measurable, ?_, ?_⟩
  · intro L m k hk
    have ht := hltail L m k hk
    erw [← sampleLaw_map d M.P.toMeasure, (sampleEquiv d).map_apply] at ht
    exact ht
  · erw [← sampleLaw_map d M.P.toMeasure, ← (sampleEquiv d).map_ae] at hreg
    change ∀ᵐ omega ∂Measure.comap (Subtype.val : AnchoredC11Sample d → PotentialSample d) M.P.toMeasure, _ at hreg
    filter_upwards [hreg] with omega hgood
    constructor
    · intro L m hm u hu n hn z hz hsub
      have hu' : _root_.SubdiffusiveProcess.CoarseGrainingVocab.IsWeaklyHarmonicOn
          (_root_.SubdiffusiveProcess.CoarseGrainingVocab.coefficientAt (toModel M) L (sampleEquiv d omega))
          (cube d m) (toH1 u) := by
        erw [← coefficientAt_eq]
        exact (harmonic_eq _ _ u).mp hu
      have hg := hgood.1 L m hm (toH1 u) hu' n hn z hz hsub
      simpa only [toH1, coefficientAt_eq] using! hg
    · intro L u hulocal hugrowth
      have hulocal' : ∀ m : ℤ, ∃ um : _root_.Homogenization.H1Function (openCubeSet (originCube d m)),
          (∀ x, um.toFun x = u x) ∧
          _root_.SubdiffusiveProcess.CoarseGrainingVocab.IsWeaklyHarmonicOn
            (_root_.SubdiffusiveProcess.CoarseGrainingVocab.coefficientAt (toModel M) L (sampleEquiv d omega))
            (cube d m) um := by
        intro m
        rcases hulocal m with ⟨um, hum, hhm⟩
        refine ⟨toH1 um, hum, ?_⟩
        erw [← coefficientAt_eq]
        exact (harmonic_eq _ _ um).mp hhm
      rcases hgood.2 L u hulocal' hugrowth with ⟨uRep, hc, hae, hlocal, hconst⟩
      refine ⟨uRep, hc, hae, ?_, hconst⟩
      intro m um hum hhm
      apply hlocal m (toH1 um) hum
      erw [← coefficientAt_eq]
      exact (harmonic_eq _ _ um).mp hhm

end SubdiffusiveProcessAudit.AnomalousHolderRegularity
