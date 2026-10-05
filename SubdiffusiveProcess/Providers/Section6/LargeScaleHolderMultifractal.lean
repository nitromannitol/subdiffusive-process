module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.PerScaleData
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.LiouvilleAssembly
public import SubdiffusiveProcess.Section6.Defs.GammaReg
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.GammaRegRange
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.GoodSetMeasurable
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellSummable
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut.PerScaleDataTop
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut.LiouvilleFromHolder
public import SubdiffusiveProcess.Section6.CutoffHolderRegularityInterior

@[expose] public section

/-!
# Large-scale Hölder and Liouville assembly

`large_scale_holder_multifractal_of_halves` is a conditional assembly: its
explicit interior estimate supplies the finite-cutoff and uncut branches.
The final theorem `large_scale_holder_multifractal` discharges that premise
with `SubdiffusiveProcess.Section6.cutoff_holder_regularity_interior`.

`Section6TheoremCUncut.perScaleData_all_of_interiorAnchor` combines the two
branches; the uncut branch uses the anchored coefficient-convergence theorem.
The Liouville conclusion follows from the regularity clause at `gammaReg`
through `liouvilleClause_of_holderClause`. The returned disorder threshold
also supplies the exponent-range condition. These are different proof steps;
finite-cutoff estimates alone do not supply the uncut conclusion.
-/

namespace SubdiffusiveProcess.Providers.Section6

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
open _root_.SubdiffusiveProcess.Model
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}



theorem large_scale_holder_multifractal_of_halves
    (delta0 C0 C : ℝ) (hdelta0 : 0 < delta0) (hC0 : 0 < C0) (hC : 0 < C)
    (hinterior : ∀ (M : GMCModel d) (_hd : M.delta ≤ delta0),
      ∀ gamma ∈ Set.Icc (1 / 2 : ℝ)
          (1 - C0 * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)),
        ∀ L m : ℕ,
          (∃ X : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ,
            Measurable X ∧ (∀ ω, 0 < X ω) ∧
            (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < X ω} ≤ ENNReal.ofReal
              (C * Real.exp (-((1 - gamma) ^ 2 * max ((k : ℝ) - C) 0) /
                (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
            ∀ ω, ∀ (u : H1Function (openCubeSet (originCube d m)))
                (g : Vec d → Vec d),
              IsDivFormWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L ω)
                  (cube d m) u g →
              MemHolder (cube d m) (1 / 2) g →
              InteriorHolderRegularityConclusions M C L ω gamma m (X ω) u g) ∧
          (m ≤ L → ∃ Xuncut : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ,
            Measurable Xuncut ∧ (∀ ω, 0 < Xuncut ω) ∧
            (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < Xuncut ω} ≤ ENNReal.ofReal
              (C * Real.exp (-((1 - gamma) ^ 2 * max ((k : ℝ) - C) 0) /
                (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
            ∀ J : ℕ, m ≤ J → ∀ ω,
              ∀ (u : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d),
                IsDivFormWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M J ω)
                    (cube d m) u g →
                MemHolder (cube d m) (1 / 2) g →
                InteriorHolderRegularityConclusions M C J ω gamma m (Xuncut ω) u g)) :
    ∃ delta0' C0' C' : ℝ, 0 < delta0' ∧ 0 < C0' ∧ 0 < C' ∧
      ∀ M : GMCModel d, (M.delta ≤ delta0' →
      ∃ hmeas : MeasurableSet (anchoredC11GoodSet d),
      ∃ hfull : M.P.toMeasure (anchoredC11GoodSet d) = 1,
      gammaReg C0' M.delta ∈ Set.Ioo (1 / 2 : ℝ) 1 ∧
      (∀ gamma ∈ Set.Icc (1 / 2 : ℝ) (gammaReg C0' M.delta),
        ∃ full : Set (AnchoredC11Sample d),
          MeasurableSet full ∧
          (anchoredC11SampleLaw M hmeas hfull).toMeasure full = 1 ∧
          ∀ L : WithTop ℕ, ∀ m : ℕ, 0 < m →
            ∃ X : AnchoredC11Sample d → ℕ,
              Measurable X ∧ (∀ ω, 0 < X ω) ∧
              (∀ k : ℕ, 0 < k →
                (anchoredC11SampleLaw M hmeas hfull).toMeasure
                    {ω' | k < X ω'} ≤ ENNReal.ofReal
                (C' * Real.exp (-((1 - gamma) ^ 2 * max ((k : ℝ) - C') 0) /
                  (C' * M.delta ^ 2 * |Real.log M.delta|)))) ∧
              ∀ ω ∈ full, TheoremCInner M C' L gamma m X ω) ∧
      (∃ full : Set (AnchoredC11Sample d),
        MeasurableSet full ∧
        (anchoredC11SampleLaw M hmeas hfull).toMeasure full = 1 ∧
        ∀ ω ∈ full, ∀ L : WithTop ℕ, ∀ u : Vec d → ℝ,
          (∀ m : ℤ, ∃ um : H1Function (openCubeSet (originCube d m)),
            (∀ x, um.toFun x = u x) ∧
              IsWeaklyHarmonicOn (coefficientAt M L ω) (cube d m) um) →
          (∀ ε > 0, ∃ᶠ R : ℝ in atTop, R ^ (-gammaReg C0' M.delta) *
              sInf {r : ℝ | ∃ c : ℝ,
                r = normalizedL2On (Metric.ball (0 : Vec d) R)
                  (fun x => u x - c)} < ε) →
          ∃ uRep : Vec d → ℝ,
            Continuous uRep ∧
            uRep =ᵐ[volume] u ∧
            (∀ m : ℤ, ∀ um : H1Function (openCubeSet (originCube d m)),
              (∀ x, um.toFun x = u x) →
              IsWeaklyHarmonicOn (coefficientAt M L ω) (cube d m) um →
              uRep =ᵐ[volume.restrict (openCubeSet (originCube d m))] um.toFun) ∧
            ∃ c : ℝ, ∀ x, uRep x = c)) := by
  obtain ⟨delta0conv, hdelta0conv, hall⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut.perScaleData_all_of_interiorAnchor d
  have hsmallpos : (0 : ℝ) < 1 / (8 * C0 ^ 2) := by positivity
  refine ⟨min (min delta0 delta0conv) (1 / (8 * C0 ^ 2)), C0, C,
    lt_min (lt_min hdelta0 hdelta0conv) hsmallpos, hC0, hC, fun M hd ↦ ?_⟩
  have hd1 : M.delta ≤ delta0 :=
    hd.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hd2 : M.delta ≤ delta0conv :=
    hd.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hd3 : M.delta < 1 / (4 * C0 ^ 2) := by
    have hle : M.delta ≤ 1 / (8 * C0 ^ 2) := hd.trans (min_le_right _ _)
    have hlt : 1 / (8 * C0 ^ 2) < 1 / (4 * C0 ^ 2) := by
      apply one_div_lt_one_div_of_lt <;> nlinarith [sq_nonneg C0, hC0]
    exact lt_of_le_of_lt hle hlt
  have hrange : gammaReg C0 M.delta ∈ Set.Ioo (1 / 2 : ℝ) 1 :=
    gammaReg_mem_Ioo_of_model M hC0 hd3
  -- The `C^{0,γ}` clause, at every admissible exponent.
  have hholder : ∀ gamma ∈ Set.Icc (1 / 2 : ℝ) (gammaReg C0 M.delta),
      ∃ full : Set (AnchoredC11Sample d),
        MeasurableSet full ∧
        (anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
          (measure_anchoredC11GoodSet_eq_one M)).toMeasure full = 1 ∧
        ∀ L : WithTop ℕ, ∀ m : ℕ, 0 < m →
          ∃ X : AnchoredC11Sample d → ℕ,
            Measurable X ∧ (∀ ω, 0 < X ω) ∧
            (∀ k : ℕ, 0 < k →
              (anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
                  (measure_anchoredC11GoodSet_eq_one M)).toMeasure
                  {ω' | k < X ω'} ≤ ENNReal.ofReal
              (C * Real.exp (-((1 - gamma) ^ 2 * max ((k : ℝ) - C) 0) /
                (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
            ∀ ω ∈ full, TheoremCInner M C L gamma m X ω := by
    intro gamma hgamma
    have hgamma' : gamma ∈ Set.Icc (1 / 2 : ℝ)
        (1 - C0 * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)) := hgamma
    exact holder_clause_finite_of_interiorAnchor M C gamma
      (measurableSet_anchoredC11GoodSet d) (measure_anchoredC11GoodSet_eq_one M)
      (hall M hd2 C gamma
        (fun L' m' ↦ (hinterior M hd1 gamma hgamma' L' m').1)
        (fun L' m' ↦ (hinterior M hd1 gamma hgamma' L' m').2))
  exact ⟨measurableSet_anchoredC11GoodSet d, measure_anchoredC11GoodSet_eq_one M,
    hrange, hholder,
    SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut.liouvilleClause_of_holderClause
      M hC (measurableSet_anchoredC11GoodSet d)
      (measure_anchoredC11GoodSet_eq_one M) hrange
      (hholder (gammaReg C0 M.delta) ⟨hrange.1.le, le_rfl⟩)⟩






theorem large_scale_holder_multifractal
    (d : ℕ) :
    ∃ delta0 C0 C : ℝ, 0 < delta0 ∧ 0 < C0 ∧ 0 < C ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, (M.delta ≤ delta0 →
      ∃ hmeas : MeasurableSet (_root_.SubdiffusiveProcess.Model.anchoredC11GoodSet d),
      ∃ hfull : M.P.toMeasure (_root_.SubdiffusiveProcess.Model.anchoredC11GoodSet d) = 1,
      gammaReg C0 M.delta ∈ Set.Ioo (1 / 2 : ℝ) 1 ∧
      (∀ gamma ∈ Set.Icc (1 / 2 : ℝ) (gammaReg C0 M.delta),
        ∃ full : Set (_root_.SubdiffusiveProcess.Model.AnchoredC11Sample d),
          MeasurableSet full ∧
          (_root_.SubdiffusiveProcess.Model.anchoredC11SampleLaw M hmeas hfull).toMeasure full = 1 ∧
          ∀ L : WithTop ℕ, ∀ m : ℕ, 0 < m →
            ∃ X : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d → ℕ,
              Measurable X ∧ (∀ ω, 0 < X ω) ∧
              (∀ k : ℕ, 0 < k →
                (_root_.SubdiffusiveProcess.Model.anchoredC11SampleLaw M hmeas hfull).toMeasure
                    {ω' | k < X ω'} ≤ ENNReal.ofReal
                (C * Real.exp (-((1 - gamma) ^ 2 * max ((k : ℝ) - C) 0) /
                  (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
              ∀ ω ∈ full,
              ∀ u : H1Function (openCubeSet (originCube d m)),
                IsWeaklyHarmonicOn (coefficientAt M L ω) (cube d m) u →
                ∀ n : ℕ, (n : ℤ) ≤ (m : ℤ) - (X ω : ℤ) →
                  ∀ z : Vec d, OnTriadicGrid n z →
                  translatedCube d n z ⊆ cube d (m - 1) →
                  normalizedL2On (translatedCube d n z)
                      (fun x => u.toFun x - averageOn (translatedCube d n z) u.toFun) ≤
                    C * (3 : ℝ) ^ (-gamma * ((m : ℝ) - (n : ℝ))) *
                      normalizedL2On (cube d m)
                        (fun x => u.toFun x - averageOn (cube d m) u.toFun) ∧
                  vectorNormalizedL2On (translatedCube d n z)
                      (fun x => Real.sqrt (coefficientAt M L ω x) • u.grad x) ≤
                    C * (3 : ℝ) ^ ((1 - gamma) * ((m : ℝ) - (n : ℝ))) *
                      vectorNormalizedL2On (cube d m)
                        (fun x => Real.sqrt (coefficientAt M L ω x) • u.grad x)) ∧
      (∃ full : Set (_root_.SubdiffusiveProcess.Model.AnchoredC11Sample d),
        MeasurableSet full ∧
        (_root_.SubdiffusiveProcess.Model.anchoredC11SampleLaw M hmeas hfull).toMeasure full = 1 ∧
        ∀ ω ∈ full, ∀ L : WithTop ℕ, ∀ u : Vec d → ℝ,
          (∀ m : ℤ, ∃ um : H1Function (openCubeSet (originCube d m)),
            (∀ x, um.toFun x = u x) ∧
              IsWeaklyHarmonicOn (coefficientAt M L ω) (cube d m) um) →
          (∀ ε > 0, ∃ᶠ R : ℝ in atTop, R ^ (-gammaReg C0 M.delta) *
              sInf {r : ℝ | ∃ c : ℝ,
                r = normalizedL2On (Metric.ball (0 : Vec d) R) (fun x => u x - c)} < ε) →
          ∃ uRep : Vec d → ℝ,
            Continuous uRep ∧
            uRep =ᵐ[volume] u ∧
            (∀ m : ℤ, ∀ um : H1Function (openCubeSet (originCube d m)),
              (∀ x, um.toFun x = u x) →
              IsWeaklyHarmonicOn (coefficientAt M L ω) (cube d m) um →
              uRep =ᵐ[volume.restrict (openCubeSet (originCube d m))] um.toFun) ∧
            ∃ c : ℝ, ∀ x, uRep x = c)) := by
  obtain ⟨C, hC, hM⟩ := _root_.SubdiffusiveProcess.Section6.cutoff_holder_regularity_interior d
  exact large_scale_holder_multifractal_of_halves C⁻¹ C C (inv_pos.2 hC) hC hC
    (fun M hd gamma hgamma L m =>
      ⟨(hM M hd gamma hgamma L m).1, (hM M hd gamma hgamma L m).2.1⟩)


end

end SubdiffusiveProcess.Providers.Section6
