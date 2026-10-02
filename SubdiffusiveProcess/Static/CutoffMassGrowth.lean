import SubdiffusiveProcess.Static.CubeMassEnvelope
import SubdiffusiveProcess.Static.CubeMassReadout
import SubdiffusiveProcess.Static.MassWindow
import SubdiffusiveProcess.Static.LocalMassComparison
import SubdiffusiveProcess.Static.AnchoredTailMoments
import SubdiffusiveProcess.Frozen.Section6.Defs.CoefficientAt
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.GoodSetMeasurable
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellSummable
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
import SubdiffusiveProcess.Frozen.Vocab.Ahom

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.Static
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Static

/-- Uniform positive and negative mass growth on every ball in the fixed
reference cube, in the physical anchored local normalization. -/
theorem exists_uniform_local_mass (d : ℕ) (y0 : Vec d) (ρ0 : ℝ) (hρ0 : 0 < ρ0) :
    ∀ q : ℝ, 1 ≤ q →
      ∃ delta0 : ℝ, 0 < delta0 ∧
        ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta ≤ delta0 →
          ∃ C : ℝ, 0 < C ∧
            ∀ (L : WithTop ℕ) (m : ℕ) (z : Vec d),
              ∃ K : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d → ℝ, Measurable K ∧
                (∀ ω, 1 ≤ K ω) ∧
                (∫⁻ ω, ENNReal.ofReal (K ω ^ q)
                  ∂(SubdiffusiveProcess.Frozen.Assumptions.anchoredC11SampleLaw M
                    (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measurableSet_anchoredC11GoodSet d)
                    (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measure_anchoredC11GoodSet_eq_one M)).toMeasure) ≤
                  ENNReal.ofReal C ∧
                ∀ᵐ ω ∂(SubdiffusiveProcess.Frozen.Assumptions.anchoredC11SampleLaw M
                    (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measurableSet_anchoredC11GoodSet d)
                    (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measure_anchoredC11GoodSet_eq_one M)).toMeasure,
                  let j : ℕ := match L with
                    | ⊤ => m
                    | (n : ℕ) => min m n
                  let cz : ℝ := coefficientAt M L ω z /
                    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M j ω.1 z
                  let b : Vec d → ℝ := fun x => cz⁻¹ * coefficientAt M L ω (z + (3 : ℝ) ^ m • x)
                  localMassEstimates b y0 ρ0 (K ω) := by
  intro q hq
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have h2q : 1 ≤ 2 * q := by linarith
  obtain ⟨J, hwindow⟩ := exists_mass_window y0 ρ0
  let R := max 1 ρ0
  have hR : 1 ≤ R := le_max_left _ _
  have hρR : ρ0 ≤ R := le_max_right _ _
  have hR0 : 0 ≤ R := hρ0.le.trans hρR
  obtain ⟨δ0, A, hδ0, hA, hbank⟩ :=
    exists_uniform_cube_mass_envelope d y0 R (2 * q) hR0 h2q
  obtain ⟨B, hB, htail⟩ := exists_uniform_local_tail_comparison d J (2 * q) h2q
  refine ⟨min δ0 1, lt_min hδ0 zero_lt_one, ?_⟩
  intro M hM
  have hMδ : M.delta ≤ δ0 := hM.trans (min_le_left _ _)
  have hM1 : M.delta ≤ 1 := hM.trans (min_le_right _ _)
  let G := massGrowthConstant d
  have hG : 0 < G := massGrowthConstant_pos d
  let C := B ^ (1 / 2 : ℝ) * (G ^ (2 * q) * A) ^ (1 / 2 : ℝ)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro L m z
  let j := localIndex L m
  have hjm : j ≤ m := by
    cases L using WithTop.recTopCoe
    · exact le_rfl
    · exact min_le_left _ _
  obtain ⟨W, hW, hWone, hWmom, hWdom⟩ := hbank M hMδ j m hjm z
  obtain ⟨F, hF, hFone, hFmom, hFdom⟩ := htail M hM1 m z
  let U : AnchoredC11Sample d → ℝ := fun ω => G * W ω.1
  have hU : Measurable U := measurable_const.mul (hW.comp measurable_subtype_coe)
  have hUone : ∀ ω, 1 ≤ U ω := fun ω =>
    one_le_mul_of_one_le_of_one_le (one_le_massGrowthConstant d) (hWone ω.1)
  have hU0 : ∀ ω, 0 ≤ U ω := fun ω => zero_le_one.trans (hUone ω)
  have hF0 : ∀ ω, 0 ≤ F ω := fun ω => zero_le_one.trans (hFone ω)
  have hUmom : (∫⁻ ω, ENNReal.ofReal (U ω ^ (2 * q)) ∂localAnchoredLaw M) ≤
      ENNReal.ofReal (G ^ (2 * q) * A) := by
    have heq : (fun ω : AnchoredC11Sample d => ENNReal.ofReal (U ω ^ (2 * q))) =
        fun ω => ENNReal.ofReal (G ^ (2 * q)) * ENNReal.ofReal (W ω.1 ^ (2 * q)) := by
      funext ω
      dsimp only [U]
      rw [Real.mul_rpow hG.le (zero_le_one.trans (hWone ω.1)),
        ENNReal.ofReal_mul (Real.rpow_nonneg hG.le _)]
    rw [heq, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      anchored_moment_eq M W hW (2 * q)]
    exact (mul_le_mul' le_rfl hWmom).trans_eq
      (ENNReal.ofReal_mul (Real.rpow_nonneg hG.le _)).symm
  refine ⟨fun ω => F ω * U ω, hF.mul hU,
    fun ω => one_le_mul_of_one_le_of_one_le (hFone ω) (hUone ω), ?_, ?_⟩
  · change (∫⁻ ω, ENNReal.ofReal ((F ω * U ω) ^ q) ∂localAnchoredLaw M) ≤ ENNReal.ofReal C
    calc
      _ ≤ (∫⁻ ω, ENNReal.ofReal (F ω ^ (2 * q)) ∂localAnchoredLaw M) ^ (1 / 2 : ℝ) *
          (∫⁻ ω, ENNReal.ofReal (U ω ^ (2 * q)) ∂localAnchoredLaw M) ^ (1 / 2 : ℝ) :=
        product_moment_le _ hF hU hF0 hU0 q
      _ ≤ ENNReal.ofReal B ^ (1 / 2 : ℝ) *
          ENNReal.ofReal (G ^ (2 * q) * A) ^ (1 / 2 : ℝ) :=
        mul_le_mul' (ENNReal.rpow_le_rpow hFmom (by norm_num))
          (ENNReal.rpow_le_rpow hUmom (by norm_num))
      _ = ENNReal.ofReal C := by
        rw [ENNReal.ofReal_rpow_of_nonneg hB.le (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
          ← ENNReal.ofReal_mul (by positivity)]
  · have hWa := (measurePreserving_anchoredVal M).quasiMeasurePreserving.ae hWdom
    filter_upwards [hWa, hFdom] with ω hω hFω
    have hprefix : localMassEstimates (fun x => aCutoff M j ω.1 (z + (3 : ℝ) ^ m • x))
        y0 ρ0 (U ω) :=
      localMassEstimates_of_cube_envelope M j m z y0 hR hρR (hWone ω.1) ω.1 hω
    have hcomp : ∀ x ∈ Metric.ball y0 (ρ0 / 2),
        (F ω)⁻¹ * aCutoff M j ω.1 (z + (3 : ℝ) ^ m • x) ≤ localDensity M L m z ω x ∧
        localDensity M L m z ω x ≤ F ω * aCutoff M j ω.1 (z + (3 : ℝ) ^ m • x) := by
      intro x hx
      cases L using WithTop.recTopCoe
      · exact hFω ⊤ le_top x (hwindow m x hx)
      · rename_i L
        by_cases hmL : m ≤ L
        · have hh := hFω (L : WithTop ℕ) (WithTop.coe_le_coe.mpr hmL) x (hwindow m x hx)
          change (F ω)⁻¹ * aCutoff M (min m L) ω.1 _ ≤ localDensity M (L : WithTop ℕ) m z ω x ∧
            localDensity M (L : WithTop ℕ) m z ω x ≤ F ω * aCutoff M (min m L) ω.1 _
          simpa only [min_eq_left hmL] using hh
        · have hLm : L ≤ m := le_of_lt (lt_of_not_ge hmL)
          change (F ω)⁻¹ * aCutoff M (min m L) ω.1 _ ≤ localDensity M (L : WithTop ℕ) m z ω x ∧
            localDensity M (L : WithTop ℕ) m z ω x ≤ F ω * aCutoff M (min m L) ω.1 _
          rw [min_eq_right hLm, localDensity_finite_of_le M hLm z ω x]
          have ha := (aCutoff_pos M L ω.1 (z + (3 : ℝ) ^ m • x)).le
          refine ⟨?_, le_mul_of_one_le_left ha (hFone ω)⟩
          exact mul_le_of_le_one_left ha (inv_le_one_of_one_le₀ (hFone ω))
    have hresult := localMassEstimates_of_comparison (hFone ω)
      (fun x hx => (hcomp x hx).1) (fun x hx => (hcomp x hx).2) hprefix
    exact hresult

end SubdiffusiveProcess.Static
