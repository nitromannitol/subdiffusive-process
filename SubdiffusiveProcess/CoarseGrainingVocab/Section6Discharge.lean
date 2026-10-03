module

public import SubdiffusiveProcess.Assumptions.Observables
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
public import Homogenization.Internal.Ch02.BlockCoarseMatrix
public import Homogenization.Sobolev.Fractional.ContinuousInterpolation.UnitCubeGeometry

@[expose] public section

/-!
# Section 6 junk-branch discharge lemmas

These lemmas isolate the boundedness and positivity facts needed to show that
the totalized definitions on the frozen section 6 surface take their intended
values.  They do not provide any theorem-level section 6 anchor.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book Homogenization.Book.Ch02
open scoped BigOperators ENNReal Topology

noncomputable section

/-! ## Hölder quotient boundedness (audit F-01) -/

/-- Audit F-01: a supplied Hölder seminorm bound is an upper bound for every
quotient occurring in `fractionalInfinitySeminormOn`. -/
theorem bddAbove_holderQuotients_of_holderSeminormBoundOn {d : ℕ}
    {W : Set (Vec d)} {s K : ℝ} {f : Vec d → Vec d}
    (_hK : 0 ≤ K) (hf : HolderSeminormBoundOn W s K f) :
    BddAbove {r : ℝ | ∃ x ∈ W, ∃ y ∈ W, x ≠ y ∧
      r = euclideanNorm (f x - f y) / euclideanNorm (x - y) ^ s} := by
  refine ⟨K, ?_⟩
  rintro r ⟨x, hx, y, hy, hxy, rfl⟩
  have hxy0 : euclideanNorm (x - y) ≠ 0 := by
    intro hzero
    exact hxy (sub_eq_zero.mp (euclideanNorm_eq_zero_iff.mp hzero))
  have hden : 0 < euclideanNorm (x - y) ^ s :=
    Real.rpow_pos_of_pos (lt_of_le_of_ne (euclideanNorm_nonneg _) (Ne.symm hxy0)) s
  exact (div_le_iff₀ hden).2 (hf x hx y hy)

/-- Audit F-01: membership in the paper's Hölder class supplies boundedness of
the quotient set used by `fractionalInfinitySeminormOn`. -/
theorem bddAbove_holderQuotients_of_memHolder {d : ℕ}
    {W : Set (Vec d)} {s : ℝ} {f : Vec d → Vec d}
    (hf : MemHolder W s f) :
    BddAbove {r : ℝ | ∃ x ∈ W, ∃ y ∈ W, x ≠ y ∧
      r = euclideanNorm (f x - f y) / euclideanNorm (x - y) ^ s} := by
  obtain ⟨K, hK, hfK⟩ := hf
  exact bddAbove_holderQuotients_of_holderSeminormBoundOn hK hfK

/-! ## Response-sphere boundedness (audit F-02) -/

/-- The section 6 response is continuous in its probe.  This follows from the
quadratic block-matrix representation, not from the variational `sSup`
definition. -/
theorem continuous_section6Response_probe {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (cubeScale cutoff : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z : Vec d) :
    Continuous (section6Response M cubeScale cutoff ω z) := by
  unfold section6Response paperScalarProbe
  simp_rw [Homogenization.Internal.Ch02.BookCh02.responseJ_eq_block_quadratic]
  simp only [blockVecDot, blockMatVecMul, vecDot]
  unfold Homogenization.matVecMul
  fun_prop

/-- Audit F-02: the response values over the Euclidean unit sphere are bounded
above, so the inner `sSup` in `accumulatedError` does not take a junk value. -/
theorem bddAbove_section6Response_unitSphere {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (cubeScale cutoff : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z : Vec d) :
    BddAbove {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
      t = section6Response M cubeScale cutoff ω z e} := by
  let S : Set (Vec d) := {e | vecNormSq e = 1}
  have hSclosed : IsClosed S := by
    apply isClosed_eq
    · change Continuous (fun e : Vec d => ∑ i, e i * e i)
      fun_prop
    · exact continuous_const
  have hSsubset : S ⊆ Metric.closedBall 0 1 := by
    intro e he
    change vecNormSq e = 1 at he
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    have hi : (e i) ^ 2 ≤ 1 := by
      simpa [he] using sq_apply_le_vecNormSq e i
    rw [Real.norm_eq_abs]
    have habs : |e i| ^ 2 ≤ 1 := by simpa [sq_abs] using hi
    nlinarith [abs_nonneg (e i)]
  have hScompact : IsCompact S :=
    (isCompact_closedBall (0 : Vec d) 1).of_isClosed_subset hSclosed hSsubset
  have himage := hScompact.bddAbove_image
    (continuous_section6Response_probe M cubeScale cutoff ω z).continuousOn
  refine himage.mono ?_
  rintro t ⟨e, he, rfl⟩
  exact ⟨e, he, rfl⟩

/-! ## Tail-average positivity (audit F-05) -/

/-- The tail coefficient is continuous in space. -/
theorem continuous_tailCoefficient {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    Continuous (tailCoefficient M L m ω) := by
  unfold tailCoefficient
  exact continuous_const.mul
    ((SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M L ω).div
      (SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M (min m L) ω)
      (fun x => (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M (min m L) ω x).ne'))

/-- Audit F-05: once the corresponding `ahom` is positive, the tail
coefficient is pointwise strictly positive. -/
theorem tailCoefficient_pos_of_ahom_pos {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hhom : 0 < ahom M (min m L)) (x : Vec d) :
    0 < tailCoefficient M L m ω x := by
  exact mul_pos hhom (div_pos
    (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L ω x)
    (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M (min m L) ω x))

private theorem volumeAverage_pos_of_pos_on {d : ℕ}
    {W : Set (Vec d)} {f : Vec d → ℝ}
    (hW : MeasurableSet W) (hvol : 0 < (volume W).toReal)
    (hint : IntegrableOn f W) (hf : ∀ x ∈ W, 0 < f x) :
    0 < volumeAverage W f := by
  have hvolE : 0 < volume W := (ENNReal.toReal_pos_iff.mp hvol).1
  have hnonneg : 0 ≤ᵐ[volume.restrict W] f := by
    filter_upwards [ae_restrict_mem hW] with x hx
    exact (hf x hx).le
  have hsupp : 0 < (volume.restrict W) (Function.support f) := by
    have hsub : W ⊆ Function.support f := by
      intro x hx
      exact (hf x hx).ne'
    calc
      0 < volume W := hvolE
      _ = (volume.restrict W) W := by simp [hW]
      _ ≤ (volume.restrict W) (Function.support f) := measure_mono hsub
  have hintpos : 0 < ∫ x in W, f x ∂volume :=
    (integral_pos_iff_support_of_nonneg_ae hnonneg hint).2 hsupp
  exact mul_pos (inv_pos.mpr hvol) hintpos

/-- Audit F-05: on every centered paper cube, the average tail coefficient is
strictly positive, conditional only on the still-separate `ahom` positivity
input. -/
theorem tailAverage_cube_pos_of_ahom_pos {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (k : ℤ)
    (hhom : 0 < ahom M (min m L)) :
    0 < tailAverage M L m ω (cube d k) := by
  let Q := originCube d k
  have hint : IntegrableOn (tailCoefficient M L m ω) (openCubeSet Q) := by
    have hclosed : IntegrableOn (tailCoefficient M L m ω)
        (Metric.closedBall (cubeCenter Q) (cubeRadius Q)) :=
      (continuous_tailCoefficient M L m ω).continuousOn.integrableOn_compact
        (ProperSpace.isCompact_closedBall (cubeCenter Q) (cubeRadius Q))
    exact hclosed.mono_set ((openCubeSet_subset_cubeSet Q).trans (cubeSet_subset_closedBall Q))
  unfold tailAverage cube
  apply volumeAverage_pos_of_pos_on (measurableSet_openCubeSet Q)
  · rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  · exact hint
  · intro x _hx
    exact tailCoefficient_pos_of_ahom_pos M L m ω hhom x




private theorem nonneg_le_exp_sq (x : ℝ) (hx : 0 ≤ x) :
    x ≤ Real.exp (x ^ 2) := by
  by_cases hx1 : x ≤ 1
  · exact hx1.trans (Real.one_le_exp (sq_nonneg x))
  · have hxx : x ≤ x ^ 2 := by nlinarith
    have hexp : x ^ 2 + 1 ≤ Real.exp (x ^ 2) := Real.add_one_le_exp _
    linarith

-- PROVENANCE: this is the first-moment extraction used before Tonelli in
-- `Algsuperdiff/Section3/Provider/Orlicz/AESummability.lean`, specialized to
-- GMC's expectation-form `OGammaLE` and its `g2Observable`.
/-- Audits F-03/F-04: G2 gives an integrable unit-cube regularity observable
with the coarse first-moment bound needed by the weighted Tonelli argument. -/
theorem g2Observable_integrable_and_integral_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    Integrable SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure ∧
      ∫ g, SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable g
          ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure ≤ 2 * M.delta := by
  let X : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ :=
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
  let E : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ := fun g =>
    Real.exp ((M.delta⁻¹ * max (X g) 0) ^ (2 : ℕ))
  have hG2 := M.G2.regularity_expectation
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hXnonneg : ∀ g, 0 ≤ X g :=
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable_nonneg
  have hpoint : ∀ g, X g ≤ M.delta * E g := by
    intro g
    let y := M.delta⁻¹ * X g
    have hy : 0 ≤ y := mul_nonneg (inv_nonneg.mpr hdelta.le) (hXnonneg g)
    have hxy : X g = M.delta * y := by
      dsimp [y]
      field_simp
    have hyexp := nonneg_le_exp_sq y hy
    rw [hxy]
    apply mul_le_mul_of_nonneg_left _ hdelta.le
    simpa [E, y, max_eq_left (hXnonneg g)] using hyexp
  have hEint : Integrable E
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := by
    simpa [E, X, SubdiffusiveProcess.OGammaLE] using hG2.1
  have hXint : Integrable X
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := by
    apply (hEint.const_mul M.delta).mono'
    · exact SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable_measurable.aestronglyMeasurable
    · filter_upwards with g
      rw [Real.norm_of_nonneg (hXnonneg g)]
      exact hpoint g
  refine ⟨hXint, ?_⟩
  calc
    ∫ g, X g ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure ≤
        ∫ g, M.delta * E g ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure :=
      integral_mono_ae hXint (hEint.const_mul M.delta)
        (Filter.Eventually.of_forall hpoint)
    _ = M.delta * ∫ g, E g
          ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure :=
      integral_const_mul M.delta E
    _ ≤ M.delta * 2 := mul_le_mul_of_nonneg_left (by
      simpa [E, X, SubdiffusiveProcess.OGammaLE] using hG2.2) hdelta.le
    _ = 2 * M.delta := by ring

-- PROVENANCE: adapts the Tonelli step of
-- `Algsuperdiff/Section3/Provider/Orlicz/AESummability.lean` and the local
-- version in `Algsuperdiff/Section3/Cutoff/Summability.lean`.
/-- Audits F-03/F-04, analytic half: summable first moments of nonnegative
measurable layers imply samplewise summability almost surely. -/
theorem ae_summable_of_summable_integrals_nonneg
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (F : ℕ → Ω → ℝ)
    (hFmeas : ∀ n, Measurable (F n)) (hFnonneg : ∀ n ω, 0 ≤ F n ω)
    (hFint : ∀ n, Integrable (F n) μ)
    (hFsum : Summable (fun n => ∫ ω, F n ω ∂μ)) :
    ∀ᵐ ω ∂μ, Summable (fun n => F n ω) := by
  have hlin : ∑' n, ∫⁻ ω, ENNReal.ofReal (F n ω) ∂μ ≠ ⊤ := by
    calc
      ∑' n, ∫⁻ ω, ENNReal.ofReal (F n ω) ∂μ =
          ∑' n, ENNReal.ofReal (∫ ω, F n ω ∂μ) := by
        congr with n
        exact (ofReal_integral_eq_lintegral_ofReal (hFint n)
          (Filter.Eventually.of_forall fun ω => hFnonneg n ω)).symm
      _ = ENNReal.ofReal (∑' n, ∫ ω, F n ω ∂μ) := by
        exact (ENNReal.ofReal_tsum_of_nonneg
          (fun n => integral_nonneg fun ω => hFnonneg n ω) hFsum).symm
      _ ≠ ⊤ := ENNReal.ofReal_ne_top
  have htotal : ∫⁻ ω, ∑' n, ENNReal.ofReal (F n ω) ∂μ ≠ ⊤ := by
    rw [lintegral_tsum fun n => (hFmeas n).aemeasurable.ennreal_ofReal]
    exact hlin
  have hfinite : ∀ᵐ ω ∂μ, ∑' n, ENNReal.ofReal (F n ω) < ⊤ :=
    ae_lt_top' (AEMeasurable.ennreal_tsum fun n =>
      (hFmeas n).aemeasurable.ennreal_ofReal) htotal
  filter_upwards [hfinite] with ω hω
  have hs : Summable (fun n => ((F n ω).toNNReal : ℝ)) := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
    simpa [ENNReal.ofReal, Real.toNNReal_of_nonneg (hFnonneg _ ω)] using hω.ne
  simpa [Real.toNNReal_of_nonneg (hFnonneg _ ω)] using hs

/-- Audit F-03, deterministic half: summability of the logarithmic tail makes
the exact infinite product in `GoodFieldTwo` multipliable. -/
theorem multipliable_goodFieldTwo_tail_of_summable {d : ℕ}
    (m j : ℕ) (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (x y : Vec d)
    (hsum : Summable (fun i : ℕ => if m + j ≤ i then 4 * |ω i x - ω i y| else 0)) :
    Multipliable (fun i : ℕ =>
      if m + j ≤ i then Real.exp (4 * |ω i x - ω i y|) else 1) := by
  have hprod := hsum.hasSum.rexp
  exact hprod.multipliable.congr (fun i => by
    by_cases hi : m + j ≤ i <;> simp [hi])

private abbrev Sample (d : ℕ) := SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d
private abbrev Field (d : ℕ) := SubdiffusiveProcess.Frozen.Assumptions.PotentialField d


public def section6UnscalePotential {d : ℕ} (j : ℕ) (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale ((3 : ℝ) ^ j) g

private theorem measurable_section6UnscalePotential {d : ℕ} (j : ℕ) :
    Measurable (section6UnscalePotential (d := d) j) :=
  (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.continuous_spatialScale _).measurable

private theorem section6UnscalePotential_triadicScale {d : ℕ}
    (j : ℕ) (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :
    section6UnscalePotential j
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale j g) = g := by
  apply SubdiffusiveProcess.Frozen.Assumptions.PotentialField.ext
  intro x
  simp only [section6UnscalePotential,
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale_apply,
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale_apply, smul_smul]
  rw [inv_mul_cancel₀ (by positivity : (3 : ℝ) ^ j ≠ 0), one_smul]

private theorem map_section6UnscalePotential_coordinate_eq_zero {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j : ℕ) :
    Measure.map (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => section6UnscalePotential j (omega j))
        M.P.toMeasure =
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := by
  let mu0 := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure
  have hcoord := SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate (d := d) j
  have hunscale := measurable_section6UnscalePotential (d := d) j
  calc
    Measure.map (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => section6UnscalePotential j (omega j))
        M.P.toMeasure =
      Measure.map (section6UnscalePotential j)
        (SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw M.P j).toMeasure := by
      rw [SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw,
        ProbabilityMeasure.toMeasure_map, Measure.map_map hunscale hcoord]
      rfl
    _ = Measure.map (section6UnscalePotential j)
        (Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale j) mu0) := by
      rw [M.shellPrefix.marginal_scaling j, ProbabilityMeasure.toMeasure_map]
    _ = Measure.map
        (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d => section6UnscalePotential j
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale j g)) mu0 := by
      rw [Measure.map_map hunscale
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_triadicScale j)]
      rfl
    _ = Measure.map id mu0 := by
      congr 1
      funext g
      exact section6UnscalePotential_triadicScale j g
    _ = mu0 := Measure.map_id

private theorem map_translate_section6UnscalePotential_coordinate_eq_zero {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j : ℕ) (z : Vec d) :
    Measure.map
        (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
          SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z
            (section6UnscalePotential j (omega j))) M.P.toMeasure =
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := by
  let T := SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate (d := d) z
  have hT := SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_translate z
  have hU : Measurable (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
      section6UnscalePotential j (omega j)) :=
    (measurable_section6UnscalePotential j).comp
      (SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate j)
  calc
    Measure.map (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => T (section6UnscalePotential j (omega j)))
        M.P.toMeasure =
      Measure.map T
        (Measure.map (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => section6UnscalePotential j (omega j))
          M.P.toMeasure) := by
        rw [Measure.map_map hT hU]
        rfl
    _ = Measure.map T
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := by
      rw [map_section6UnscalePotential_coordinate_eq_zero M j]
    _ = (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := by
      simpa [T] using M.G1.stationary z

def section6TranslatedShellG2 {d : ℕ} (j : ℕ) (z : Vec d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : ℝ :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
    (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z
      (section6UnscalePotential j (omega j)))

private theorem measurable_section6TranslatedShellG2 {d : ℕ}
    (j : ℕ) (z : Vec d) :
    Measurable (section6TranslatedShellG2 (d := d) j z) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable_measurable.comp
    ((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_translate z).comp
      ((measurable_section6UnscalePotential j).comp
        (SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate j)))

private theorem section6TranslatedShellG2_nonneg {d : ℕ}
    (j : ℕ) (z : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    0 ≤ section6TranslatedShellG2 j z omega :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable_nonneg _

def section6SmallShellEnvelope {d : ℕ} (j r : ℕ) (z : Vec d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : ℝ :=
  (3 : ℝ) ^ ((r : ℤ) - (j : ℤ)) *
    section6TranslatedShellG2 j ((((3 : ℝ) ^ j)⁻¹) • z) omega

private theorem section6SmallShellEnvelope_nonneg {d : ℕ}
    (j r : ℕ) (z : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    0 ≤ section6SmallShellEnvelope j r z omega :=
  mul_nonneg (zpow_nonneg (by norm_num) _)
    (section6TranslatedShellG2_nonneg _ _ _)

private theorem measurable_section6SmallShellEnvelope {d : ℕ}
    (j r : ℕ) (z : Vec d) :
    Measurable (section6SmallShellEnvelope (d := d) j r z) :=
  (measurable_section6TranslatedShellG2 j _).const_mul _

private theorem mem_translatedCube_iff_sub_mem {d : ℕ} {r : ℤ} {z x : Vec d} :
    x ∈ translatedCube d r z ↔ x - z ∈ cube d r := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hu
  · intro hx
    refine ⟨x - z, hx, ?_⟩
    ext i
    simp

private theorem integrable_translatedShellG2_and_integral_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j : ℕ) (z : Vec d) :
    Integrable (section6TranslatedShellG2 j z) M.P.toMeasure ∧
      ∫ omega, section6TranslatedShellG2 j z omega ∂M.P.toMeasure ≤ 2 * M.delta := by
  let G : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ := SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
  let T : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → SubdiffusiveProcess.Frozen.Assumptions.PotentialField d := fun omega =>
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z
      (section6UnscalePotential j (omega j))
  have hGmeas : Measurable G :=
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable_measurable
  have hTmeas : Measurable T :=
    (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_translate z).comp
      ((measurable_section6UnscalePotential j).comp
        (SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate j))
  have hbase := g2Observable_integrable_and_integral_le M
  have hmap := map_translate_section6UnscalePotential_coordinate_eq_zero M j z
  have hmapInt : Integrable G (Measure.map T M.P.toMeasure) := by
    rw [hmap]
    exact hbase.1
  have hcomp : Integrable (G ∘ T) M.P.toMeasure :=
    (integrable_map_measure hGmeas.aestronglyMeasurable hTmeas.aemeasurable).mp hmapInt
  have hintEq : (∫ omega, G (T omega) ∂M.P.toMeasure) =
      ∫ g, G g ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := by
    calc
      (∫ omega, G (T omega) ∂M.P.toMeasure) =
          ∫ g, G g ∂Measure.map T M.P.toMeasure := by
        exact (integral_map hTmeas.aemeasurable
          hGmeas.aestronglyMeasurable).symm
      _ = ∫ g, G g ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := by
        rw [hmap]
  refine ⟨?_, ?_⟩
  · simpa [section6TranslatedShellG2, G, T, Function.comp_def] using! hcomp
  · simpa [section6TranslatedShellG2, G, T] using hintEq.trans_le hbase.2

private theorem integrable_section6SmallShellEnvelope_and_integral_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j r : ℕ) (z : Vec d) :
    Integrable (section6SmallShellEnvelope j r z) M.P.toMeasure ∧
      ∫ omega, section6SmallShellEnvelope j r z omega ∂M.P.toMeasure ≤
        (3 : ℝ) ^ ((r : ℤ) - (j : ℤ)) * (2 * M.delta) := by
  let w : Vec d := (((3 : ℝ) ^ j)⁻¹) • z
  have hG := integrable_translatedShellG2_and_integral_le M j w
  have hscale : 0 ≤ (3 : ℝ) ^ ((r : ℤ) - (j : ℤ)) := zpow_nonneg (by norm_num) _
  refine ⟨?_, ?_⟩
  · simpa [section6SmallShellEnvelope, w] using!
      hG.1.const_mul ((3 : ℝ) ^ ((r : ℤ) - (j : ℤ)))
  · have h := mul_le_mul_of_nonneg_left hG.2 hscale
    simpa [section6SmallShellEnvelope, w, integral_const_mul] using h

private theorem section6SmallShellEnvelope_diagonal_eq {d : ℕ}
    (r q : ℕ) (z : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    section6SmallShellEnvelope (r + q) r z omega =
      (1 / 3 : ℝ) ^ q *
        section6TranslatedShellG2 (r + q)
          ((((3 : ℝ) ^ (r + q))⁻¹) • z) omega := by
  rw [section6SmallShellEnvelope]
  congr 1
  rw [show (r : ℤ) - ((r + q : ℕ) : ℤ) = -((q : ℕ) : ℤ) by omega,
    zpow_neg, zpow_natCast]
  rw [← inv_pow]
  norm_num

private theorem ae_summable_section6SmallShellEnvelope_diagonal {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (r : ℕ) (z : Vec d) :
    ∀ᵐ omega ∂M.P.toMeasure,
      Summable (fun q : ℕ => section6SmallShellEnvelope (r + q) r z omega) := by
  let F : ℕ → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := fun q omega =>
    section6SmallShellEnvelope (r + q) r z omega
  have hFint : ∀ q, Integrable (F q) M.P.toMeasure := fun q =>
    (integrable_section6SmallShellEnvelope_and_integral_le
      M (r + q) r z).1
  have hFbound : ∀ q, (∫ omega, F q omega ∂M.P.toMeasure) ≤
      2 * M.delta * (1 / 3 : ℝ) ^ q := by
    intro q
    have h := (integrable_section6SmallShellEnvelope_and_integral_le
      M (r + q) r z).2
    rw [show (r : ℤ) - ((r + q : ℕ) : ℤ) = -((q : ℕ) : ℤ) by omega,
      zpow_neg, zpow_natCast] at h
    have hpow : ((3 : ℝ) ^ q)⁻¹ = (1 / 3 : ℝ) ^ q := by
      rw [← inv_pow]
      norm_num
    rw [hpow] at h
    change (∫ omega, F q omega ∂M.P.toMeasure) ≤
      (1 / 3 : ℝ) ^ q * (2 * M.delta) at h
    simpa only [mul_comm] using h
  have hgeom : Summable (fun q : ℕ => 2 * M.delta * (1 / 3 : ℝ) ^ q) :=
    (summable_geometric_of_norm_lt_one
      (show ‖(1 / 3 : ℝ)‖ < 1 by norm_num)).mul_left (2 * M.delta)
  have hFsum : Summable (fun q => ∫ omega, F q omega ∂M.P.toMeasure) :=
    Summable.of_nonneg_of_le
      (fun q => integral_nonneg fun omega => section6SmallShellEnvelope_nonneg _ _ _ _)
      hFbound hgeom
  exact ae_summable_of_summable_integrals_nonneg M.P.toMeasure F
    (fun q => measurable_section6SmallShellEnvelope _ _ _)
    (fun q omega => section6SmallShellEnvelope_nonneg _ _ _ _)
    hFint hFsum

private theorem deriv_norm_le_g2Observable {d : ℕ} (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d 0)) :
    ‖SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g x‖ ≤
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable g := by
  have hderiv : ‖SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g x‖ ≤
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.unitCubeDerivNorm g := by
    unfold SubdiffusiveProcess.Frozen.Assumptions.PotentialField.unitCubeDerivNorm
    apply le_csSup
    · obtain ⟨C, hC⟩ :=
        (isCompact_closedBall (cubeCenter (originCube d 0))
          (cubeRadius (originCube d 0))).exists_bound_of_continuousOn
            ((continuous_norm.comp
              (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g).continuous).continuousOn)
      refine ⟨max 0 C, ?_⟩
      rintro r ⟨o, rfl⟩
      cases o with
      | none => exact le_max_left _ _
      | some y =>
        have hy : y.1 ∈ Metric.closedBall (cubeCenter (originCube d 0))
            (cubeRadius (originCube d 0)) := by
          apply Metric.ball_subset_closedBall
          rw [ball_cubeCenter_eq_openCubeSet]
          exact y.2
        have hr := hC y.1 hy
        simpa only [Function.comp_apply, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg _)] using hr.trans (le_max_right _ _)
    · exact ⟨some ⟨x, hx⟩, rfl⟩
  calc
    ‖SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g x‖ ≤
        SubdiffusiveProcess.Frozen.Assumptions.PotentialField.unitCubeDerivNorm g := hderiv
    _ ≤ SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable g := by
      unfold SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
      have hv := SubdiffusiveProcess.Frozen.Assumptions.PotentialField.unitCubeValueNorm_nonneg g
      have hl :=
        SubdiffusiveProcess.Frozen.Assumptions.PotentialField.unitCubeDerivLipschitzSeminorm_nonneg g
      linarith

private theorem euclideanNorm_shellGradient_le {d : ℕ} (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) (x : Vec d) :
    euclideanNorm (shellGradient g x) ≤
      (d : ℝ) * ‖SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g x‖ := by
  have hpi : ‖shellGradient g x‖ ≤
      ‖SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g x‖ := by
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro i
    rw [Real.norm_eq_abs]
    calc
      |shellGradient g x i| =
          ‖SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g x
            (Pi.single i (1 : ℝ) : Vec d)‖ := by
        rw [Real.norm_eq_abs]
        rfl
      _ ≤ ‖SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g x‖ *
          ‖(Pi.single i (1 : ℝ) : Vec d)‖ :=
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g x).le_opNorm _
      _ = ‖SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g x‖ := by
        rw [Pi.norm_single]
        norm_num
  calc
    euclideanNorm (shellGradient g x) ≤ (d : ℝ) * ‖shellGradient g x‖ :=
      euclideanNorm_le_dimension_mul_norm _
    _ ≤ (d : ℝ) * ‖SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g x‖ :=
      mul_le_mul_of_nonneg_left hpi (Nat.cast_nonneg d)

private theorem inv_scale_mem_unitCube {d : ℕ} {j r : ℕ} (hrj : r ≤ j)
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d (r : ℤ))) :
    (((3 : ℝ) ^ j)⁻¹) • x ∈ openCubeSet (originCube d 0) := by
  rw [mem_openCubeSet_originCube_iff] at hx ⊢
  intro i
  have h3j : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  have hscale : (3 : ℝ) ^ r ≤ (3 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) hrj
  have hxi := hx i
  simp only [Pi.smul_apply, smul_eq_mul, zpow_zero, mul_one]
  constructor
  · rw [← div_eq_inv_mul, lt_div_iff₀ h3j]
    calc
      -(1 / 2 : ℝ) * (3 : ℝ) ^ j ≤ -(1 / 2 : ℝ) * (3 : ℝ) ^ r := by
        exact mul_le_mul_of_nonpos_left hscale (by norm_num)
      _ < x i := by simpa only [zpow_natCast] using hxi.1
  · rw [← div_eq_inv_mul, div_lt_iff₀ h3j]
    calc
      x i < (1 / 2 : ℝ) * (3 : ℝ) ^ r := by
        simpa only [zpow_natCast] using hxi.2
      _ ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ j :=
        mul_le_mul_of_nonneg_left hscale (by norm_num)

private theorem shellGradient_le_section6SmallShellEnvelope {d : ℕ}
    (j r : ℕ) (hrj : r ≤ j) (z : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) {x : Vec d}
    (hx : x ∈ translatedCube d (r : ℤ) z) :
    euclideanNorm (shellGradient (omega j) x) ≤
      (d : ℝ) * ((3 : ℝ) ^ j)⁻¹ *
        section6TranslatedShellG2 j ((((3 : ℝ) ^ j)⁻¹) • z) omega := by
  let z' : Vec d := (((3 : ℝ) ^ j)⁻¹) • z
  let u : Vec d := (((3 : ℝ) ^ j)⁻¹) • (x - z)
  let g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d := SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z'
    (section6UnscalePotential j (omega j))
  have hu : u ∈ openCubeSet (originCube d 0) :=
    inv_scale_mem_unitCube hrj (mem_translatedCube_iff_sub_mem.mp hx)
  have hderiv : SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g u =
      (3 : ℝ) ^ j • SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (omega j) x := by
    change (3 : ℝ) ^ j •
        SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (omega j)
          ((3 : ℝ) ^ j • (u + z')) =
      (3 : ℝ) ^ j • SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (omega j) x
    congr 1
    congr 1
    dsimp [u, z']
    rw [← smul_add, sub_add_cancel, smul_smul]
    rw [mul_inv_cancel₀ (by positivity : (3 : ℝ) ^ j ≠ 0), one_smul]
  have hG := deriv_norm_le_g2Observable g hu
  rw [hderiv, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (3 : ℝ) ^ j)] at hG
  have h3j : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  have hnorm : ‖SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (omega j) x‖ ≤
      ((3 : ℝ) ^ j)⁻¹ * section6TranslatedShellG2 j z' omega := by
    rw [le_inv_mul_iff₀ h3j]
    simpa only [g, section6TranslatedShellG2] using hG
  calc
    euclideanNorm (shellGradient (omega j) x) ≤
        (d : ℝ) * ‖SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (omega j) x‖ :=
      euclideanNorm_shellGradient_le _ _
    _ ≤ (d : ℝ) * (((3 : ℝ) ^ j)⁻¹ *
        section6TranslatedShellG2 j z' omega) :=
      mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg d)
    _ = (d : ℝ) * ((3 : ℝ) ^ j)⁻¹ *
        section6TranslatedShellG2 j ((((3 : ℝ) ^ j)⁻¹) • z) omega := by
      simp only [z', mul_assoc]

private theorem vectorSupNormOn_shellGradient_le_section6SmallShellEnvelope {d : ℕ}
    (j r : ℕ) (hrj : r ≤ j) (z : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    vectorSupNormOn (translatedCube d (r : ℤ) z) (shellGradient (omega j)) ≤
      (d : ℝ) * ((3 : ℝ) ^ j)⁻¹ *
        section6TranslatedShellG2 j ((((3 : ℝ) ^ j)⁻¹) • z) omega := by
  unfold vectorSupNormOn
  apply csSup_le
  · have hzero : (0 : Vec d) ∈ cube d (r : ℤ) := by
      rw [cube, mem_openCubeSet_originCube_iff]
      intro i
      have hp : 0 < (3 : ℝ) ^ (r : ℤ) := zpow_pos (by norm_num) _
      constructor <;> simp only [Pi.zero_apply] <;> nlinarith
    exact ⟨euclideanNorm (shellGradient (omega j) z), z,
      mem_translatedCube_iff_sub_mem.mpr (by simpa using hzero), rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact shellGradient_le_section6SmallShellEnvelope j r hrj z omega hx

theorem scaled_vectorSupNormOn_shellGradient_le_envelope {d : ℕ}
    (j r : ℕ) (hrj : r ≤ j) (z : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    (3 : ℝ) ^ r *
        vectorSupNormOn (translatedCube d (r : ℤ) z) (shellGradient (omega j)) ≤
      (d : ℝ) * section6SmallShellEnvelope j r z omega := by
  have h := vectorSupNormOn_shellGradient_le_section6SmallShellEnvelope
    j r hrj z omega
  have hpow : (3 : ℝ) ^ r * ((3 : ℝ) ^ j)⁻¹ =
      (3 : ℝ) ^ ((r : ℤ) - (j : ℤ)) := by
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast, zpow_natCast]
    exact (div_eq_mul_inv _ _).symm
  calc
    (3 : ℝ) ^ r *
        vectorSupNormOn (translatedCube d (r : ℤ) z) (shellGradient (omega j)) ≤
      (3 : ℝ) ^ r * ((d : ℝ) * ((3 : ℝ) ^ j)⁻¹ *
        section6TranslatedShellG2 j ((((3 : ℝ) ^ j)⁻¹) • z) omega) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = (d : ℝ) * section6SmallShellEnvelope j r z omega := by
      rw [section6SmallShellEnvelope]
      rw [← hpow]
      ring

theorem vectorSupNormOn_shellGradient_nonneg {d : ℕ}
    (j r : ℕ) (hrj : r ≤ j) (z : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    0 ≤ vectorSupNormOn (translatedCube d (r : ℤ) z) (shellGradient (omega j)) := by
  let C : ℝ := (d : ℝ) * ((3 : ℝ) ^ j)⁻¹ *
    section6TranslatedShellG2 j ((((3 : ℝ) ^ j)⁻¹) • z) omega
  have hBdd : BddAbove {a : ℝ | ∃ x ∈ translatedCube d (r : ℤ) z,
      a = euclideanNorm (shellGradient (omega j) x)} := by
    refine ⟨C, ?_⟩
    rintro a ⟨x, hx, rfl⟩
    exact shellGradient_le_section6SmallShellEnvelope j r hrj z omega hx
  have hzero : (0 : Vec d) ∈ cube d (r : ℤ) := by
    rw [cube, mem_openCubeSet_originCube_iff]
    intro i
    have hp : 0 < (3 : ℝ) ^ (r : ℤ) := zpow_pos (by norm_num) _
    constructor <;> simp only [Pi.zero_apply] <;> nlinarith
  unfold vectorSupNormOn
  exact (euclideanNorm_nonneg (shellGradient (omega j) z)).trans
    (le_csSup hBdd ⟨z, mem_translatedCube_iff_sub_mem.mpr (by simpa using hzero), rfl⟩)

-- PROVENANCE: mirrors the translated local-control moment -> geometric
-- summation route in `Algsuperdiff/Section3/Cutoff/LocalControlMoment.lean`.
/-- Audit F-04: on every deterministic translated cube, the literal gradient
tail in `accumulatedError` is summable almost surely. -/
theorem ae_summable_translatedCube_gradient_tail {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k : ℕ) (z : Vec d) :
    ∀ᵐ omega ∂M.P.toMeasure, Summable (fun j : ℕ =>
      if k ≤ j then
        (3 : ℝ) ^ k *
          vectorSupNormOn (translatedCube d (k : ℤ) z) (shellGradient (omega j))
      else 0) := by
  filter_upwards [ae_summable_section6SmallShellEnvelope_diagonal M k z] with omega hsum
  let F : ℕ → ℝ := fun j => if k ≤ j then
    (3 : ℝ) ^ k *
      vectorSupNormOn (translatedCube d (k : ℤ) z) (shellGradient (omega j))
    else 0
  have hshift : Summable (fun q : ℕ => F (q + k)) := by
    have hdom : ∀ q : ℕ, F (q + k) ≤
        (d : ℝ) * section6SmallShellEnvelope (k + q) k z omega := by
      intro q
      dsimp [F]
      rw [if_pos (by omega : k ≤ q + k)]
      simpa only [Nat.add_comm] using
        scaled_vectorSupNormOn_shellGradient_le_envelope
          (j := k + q) (r := k) (by omega) z omega
    have hnonneg : ∀ q : ℕ, 0 ≤ F (q + k) := by
      intro q
      dsimp [F]
      rw [if_pos (by omega : k ≤ q + k)]
      exact mul_nonneg (by positivity)
        (vectorSupNormOn_shellGradient_nonneg (j := q + k) (r := k)
          (by omega) z omega)
    exact Summable.of_nonneg_of_le hnonneg hdom (hsum.mul_left (d : ℝ))
  exact (summable_nat_add_iff k).mp hshift

private theorem norm_inv_scale_le_shell_ratio {d : ℕ} {j r : ℕ}
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d (r : ℤ))) :
    ‖(((3 : ℝ) ^ j)⁻¹) • x‖ ≤
      (3 : ℝ) ^ ((r : ℤ) - (j : ℤ)) := by
  have h3j : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  have hrhs : 0 ≤ (3 : ℝ) ^ ((r : ℤ) - (j : ℤ)) :=
    zpow_nonneg (by norm_num) _
  rw [pi_norm_le_iff_of_nonneg hrhs]
  intro i
  have hxi := (mem_openCubeSet_originCube_iff.mp hx) i
  simp only [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
  rw [abs_le]
  have hpow : (3 : ℝ) ^ ((r : ℤ) - (j : ℤ)) =
      ((3 : ℝ) ^ j)⁻¹ * (3 : ℝ) ^ r := by
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast, zpow_natCast]
    rw [div_eq_mul_inv, mul_comm]
  rw [hpow]
  have habs : |x i| ≤ (3 : ℝ) ^ r := by
    rw [abs_le]
    constructor
    · have hlo : -(1 / 2 : ℝ) * (3 : ℝ) ^ r < x i := by
        simpa only [zpow_natCast] using hxi.1
      nlinarith [show (0 : ℝ) ≤ (3 : ℝ) ^ r by positivity]
    · have hhi : x i < (1 / 2 : ℝ) * (3 : ℝ) ^ r := by
        simpa only [zpow_natCast] using hxi.2
      nlinarith [show (0 : ℝ) ≤ (3 : ℝ) ^ r by positivity]
  rw [← abs_le, abs_mul, abs_of_pos (inv_pos.mpr h3j)]
  exact mul_le_mul_of_nonneg_left habs (inv_nonneg.mpr h3j.le)

private theorem abs_shell_sub_le_section6SmallShellEnvelope {d : ℕ}
    (j r : ℕ) (hrj : r ≤ j) (z : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) {x : Vec d}
    (hx : x ∈ translatedCube d (r : ℤ) z) :
    |omega j x - omega j z| ≤ section6SmallShellEnvelope j r z omega := by
  let z' : Vec d := (((3 : ℝ) ^ j)⁻¹) • z
  let g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d := SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z'
    (section6UnscalePotential j (omega j))
  let u : Vec d := (((3 : ℝ) ^ j)⁻¹) • (x - z)
  have hxdiff := mem_translatedCube_iff_sub_mem.mp hx
  have hu : u ∈ openCubeSet (originCube d 0) :=
    inv_scale_mem_unitCube hrj hxdiff
  have hzero : (0 : Vec d) ∈ openCubeSet (originCube d 0) := by
    rw [mem_openCubeSet_originCube_iff]
    intro i
    norm_num
  have hmean := (convex_openCubeSet (originCube d 0)).norm_image_sub_le_of_norm_fderiv_le
    (f := fun v : Vec d => g v)
    (fun v _ => (g.hasFDerivAt v).differentiableAt)
    (fun v hv => by
      rw [(g.hasFDerivAt v).fderiv]
      exact deriv_norm_le_g2Observable g hv)
    hu hzero
  have hdist : ‖(0 : Vec d) - u‖ ≤
      (3 : ℝ) ^ ((r : ℤ) - (j : ℤ)) := by
    have h := norm_inv_scale_le_shell_ratio (j := j) hxdiff
    simpa only [u, zero_sub, norm_neg] using h
  have hvalx : g u = omega j x := by
    simp only [g, u, z', SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate_apply,
      section6UnscalePotential,
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale_apply]
    rw [← smul_add, sub_add_cancel, smul_smul]
    rw [mul_inv_cancel₀ (by positivity : (3 : ℝ) ^ j ≠ 0), one_smul]
  have hvalz : g 0 = omega j z := by
    simp only [g, z', SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate_apply,
      zero_add, section6UnscalePotential,
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale_apply, smul_smul]
    rw [mul_inv_cancel₀ (by positivity : (3 : ℝ) ^ j ≠ 0), one_smul]
  change ‖g 0 - g u‖ ≤ _ at hmean
  rw [hvalz, hvalx, Real.norm_eq_abs, abs_sub_comm] at hmean
  have hG : 0 ≤ section6TranslatedShellG2 j z' omega :=
    section6TranslatedShellG2_nonneg _ _ _
  calc
    |omega j x - omega j z| ≤
        section6TranslatedShellG2 j z' omega * ‖(0 : Vec d) - u‖ := hmean
    _ ≤ section6TranslatedShellG2 j z' omega *
        (3 : ℝ) ^ ((r : ℤ) - (j : ℤ)) :=
      mul_le_mul_of_nonneg_left hdist hG
    _ = section6SmallShellEnvelope j r z omega := by
      rw [section6SmallShellEnvelope]
      exact mul_comm _ _

private theorem supNormOn_shell_sub_le_section6SmallShellEnvelope {d : ℕ}
    (j r : ℕ) (hrj : r ≤ j) (z : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    supNormOn (translatedCube d (r : ℤ) z) (fun x => omega j x - omega j z) ≤
      section6SmallShellEnvelope j r z omega := by
  unfold supNormOn
  apply csSup_le
  · have hzero : (0 : Vec d) ∈ cube d (r : ℤ) := by
      rw [cube, mem_openCubeSet_originCube_iff]
      intro i
      have hp : 0 < (3 : ℝ) ^ (r : ℤ) := zpow_pos (by norm_num) _
      constructor <;> simp only [Pi.zero_apply] <;> nlinarith
    exact ⟨|omega j z - omega j z|, z,
      mem_translatedCube_iff_sub_mem.mpr (by simpa using hzero), rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact abs_shell_sub_le_section6SmallShellEnvelope j r hrj z omega hx

private theorem supNormOn_shell_sub_nonneg {d : ℕ}
    (j r : ℕ) (hrj : r ≤ j) (z : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    0 ≤ supNormOn (translatedCube d (r : ℤ) z) (fun x => omega j x - omega j z) := by
  have hBdd : BddAbove {a : ℝ | ∃ x ∈ translatedCube d (r : ℤ) z,
      a = |omega j x - omega j z|} := by
    refine ⟨section6SmallShellEnvelope j r z omega, ?_⟩
    rintro a ⟨x, hx, rfl⟩
    exact abs_shell_sub_le_section6SmallShellEnvelope j r hrj z omega hx
  have hzero : (0 : Vec d) ∈ cube d (r : ℤ) := by
    rw [cube, mem_openCubeSet_originCube_iff]
    intro i
    have hp : 0 < (3 : ℝ) ^ (r : ℤ) := zpow_pos (by norm_num) _
    constructor <;> simp only [Pi.zero_apply] <;> nlinarith
  unfold supNormOn
  simpa using (le_csSup hBdd ⟨z,
    mem_translatedCube_iff_sub_mem.mpr (by simpa using hzero), rfl⟩)

-- PROVENANCE: mirrors `CubeControlTransport.lean` and
-- `LocalControlMoment.lean`: translated marginal control, a measurable
-- finite local envelope, then a geometrically weighted Tonelli sum.
/-- Audit F-03, uniform logarithmic form: on every deterministic translated
cube, the exact shell-increment suprema defining the infinite field product
are summable almost surely. -/
theorem ae_summable_goodFieldTwo_tail_supNorm {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m j : ℕ) (y : Vec d) :
    ∀ᵐ omega ∂M.P.toMeasure, Summable (fun i : ℕ =>
      if m + j ≤ i then
        4 * supNormOn (translatedCube d ((m + 1 + j : ℕ) : ℤ) y)
          (fun x => omega i x - omega i y)
      else 0) := by
  let t := m + j
  let r := m + 1 + j
  filter_upwards [ae_summable_section6SmallShellEnvelope_diagonal M r y] with omega hsum
  let F : ℕ → ℝ := fun i => if t ≤ i then
    4 * supNormOn (translatedCube d (r : ℤ) y) (fun x => omega i x - omega i y)
    else 0
  have htail : Summable (fun q : ℕ => F (q + 1 + t)) := by
    have hdom : ∀ q : ℕ, F (q + 1 + t) ≤
        4 * section6SmallShellEnvelope (r + q) r y omega := by
      intro q
      dsimp [F]
      rw [if_pos (by omega : t ≤ q + 1 + t)]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      have hindex : q + 1 + t = r + q := by omega
      rw [hindex]
      exact supNormOn_shell_sub_le_section6SmallShellEnvelope
        (j := r + q) (r := r) (by omega) y omega
    have hnonneg : ∀ q : ℕ, 0 ≤ F (q + 1 + t) := by
      intro q
      dsimp [F]
      rw [if_pos (by omega : t ≤ q + 1 + t)]
      exact mul_nonneg (by norm_num)
        (supNormOn_shell_sub_nonneg (j := q + 1 + t) (r := r)
          (by omega) y omega)
    exact Summable.of_nonneg_of_le hnonneg hdom (hsum.mul_left 4)
  have hshift : Summable (fun q : ℕ => F (q + t)) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.add_assoc, Nat.add_comm 1] using htail
  have hF : Summable F := (summable_nat_add_iff t).mp hshift
  simpa [F, t, r, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hF

private theorem translatedCube_subset_closedBall {d : ℕ} (r : ℤ) (z : Vec d) :
    translatedCube d r z ⊆ Metric.closedBall z (cubeRadius (originCube d r)) := by
  rintro x ⟨u, hu, rfl⟩
  have huball : u ∈ Metric.ball (cubeCenter (originCube d r))
      (cubeRadius (originCube d r)) := by
    rw [ball_cubeCenter_eq_openCubeSet]
    exact hu
  apply Metric.ball_subset_closedBall
  rw [Metric.mem_ball] at huball ⊢
  have hcenter : cubeCenter (originCube d r) = (0 : Vec d) := by
    ext i
    simp [cubeCenter, originCube]
  simpa [dist_eq_norm, hcenter] using huball

theorem aux_dedup_d228_bddAbove_abs_values_translatedCube {d : ℕ}
    (r : ℤ) (z : Vec d) {f : Vec d → ℝ} (hf : Continuous f) :
    BddAbove {a : ℝ | ∃ x ∈ translatedCube d r z, a = |f x|} := by
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall z (cubeRadius (originCube d r))).exists_bound_of_continuousOn
      ((continuous_abs.comp hf).continuousOn)
  refine ⟨max 0 C, ?_⟩
  rintro a ⟨x, hx, rfl⟩
  have h := hC x (translatedCube_subset_closedBall r z hx)
  simpa only [Function.comp_apply, Real.norm_eq_abs, abs_abs] using
    h.trans (le_max_right _ _)

private theorem bddAbove_abs_values_translatedCube {d : ℕ}
    (r : ℤ) (z : Vec d) {f : Vec d → ℝ} (hf : Continuous f) :
    BddAbove {a : ℝ | ∃ x ∈ translatedCube d r z, a = |f x|} := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d228_bddAbove_abs_values_translatedCube (d := d) (r := r) (z := z) (f := f) (hf := hf)

private theorem abs_apply_le_supNormOn_translatedCube {d : ℕ}
    (r : ℤ) (z : Vec d) {f : Vec d → ℝ} (hf : Continuous f)
    {x : Vec d} (hx : x ∈ translatedCube d r z) :
    |f x| ≤ supNormOn (translatedCube d r z) f := by
  unfold supNormOn
  exact le_csSup (bddAbove_abs_values_translatedCube r z hf) ⟨x, hx, rfl⟩

private theorem summable_goodFieldTwo_point_tail_of_sup {d : ℕ}
    (m j : ℕ) (y : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hsum : Summable (fun i : ℕ => if m + j ≤ i then
      4 * supNormOn (translatedCube d ((m + 1 + j : ℕ) : ℤ) y)
        (fun x => omega i x - omega i y) else 0))
    {x : Vec d} (hx : x ∈ translatedCube d ((m + 1 + j : ℕ) : ℤ) y) :
    Summable (fun i : ℕ => if m + j ≤ i then
      4 * |omega i x - omega i y| else 0) := by
  refine Summable.of_nonneg_of_le
    (f := fun i : ℕ => if m + j ≤ i then
      4 * supNormOn (translatedCube d ((m + 1 + j : ℕ) : ℤ) y)
        (fun x => omega i x - omega i y) else 0) ?_ ?_ hsum
  · intro i
    split <;> positivity
  · intro i
    by_cases hi : m + j ≤ i
    · simp only [hi, if_true]
      exact mul_le_mul_of_nonneg_left
        (abs_apply_le_supNormOn_translatedCube _ _
          ((omega i).1.1.continuous.sub
            (continuous_const : Continuous (fun _ : Vec d => omega i y))) hx) (by norm_num)
    · simp only [hi, if_false]
      exact le_rfl

/-- Audit F-03, exact product form: on every deterministic translated cube,
the infinite product occurring in `GoodFieldTwo` is multipliable at every
point, on one event of full probability. -/
theorem ae_multipliable_goodFieldTwo_tail_on_translatedCube {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m j : ℕ) (y : Vec d) :
    ∀ᵐ omega ∂M.P.toMeasure, ∀ x ∈ translatedCube d ((m + 1 + j : ℕ) : ℤ) y,
      Multipliable (fun i : ℕ => if m + j ≤ i then
        Real.exp (4 * |omega i x - omega i y|) else 1) := by
  filter_upwards [ae_summable_goodFieldTwo_tail_supNorm M m j y] with omega hsum
  intro x hx
  exact multipliable_goodFieldTwo_tail_of_summable m j omega x y
    (summable_goodFieldTwo_point_tail_of_sup m j y omega hsum hx)

/-- Audit F-03, exact outer-supremum guard: almost surely the full expression
inside `GoodFieldTwo` is bounded on its translated cube, so `supNormOn` does
not take its unbounded-set junk value. -/
theorem ae_bddAbove_goodFieldTwo_values_on_translatedCube {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m j : ℕ) (y : Vec d) :
    ∀ᵐ omega ∂M.P.toMeasure,
      BddAbove {a : ℝ | ∃ x ∈ translatedCube d ((m + 1 + j : ℕ) : ℤ) y,
        a = |(∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |omega i x|) +
          ∏' i : ℕ, if m + j ≤ i then
            Real.exp (4 * |omega i x - omega i y|) else 1|} := by
  filter_upwards [ae_summable_goodFieldTwo_tail_supNorm M m j y] with omega hsum
  let W := translatedCube d ((m + 1 + j : ℕ) : ℤ) y
  let finitePart : Vec d → ℝ := fun x =>
    ∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |omega i x|
  have hfiniteContinuous : Continuous finitePart := by
    dsimp [finitePart]
    fun_prop
  obtain ⟨C, hC⟩ := bddAbove_abs_values_translatedCube
    ((m + 1 + j : ℕ) : ℤ) y hfiniteContinuous
  let S : ℝ := ∑' i : ℕ, if m + j ≤ i then
    4 * supNormOn W (fun x => omega i x - omega i y) else 0
  refine ⟨C + Real.exp S, ?_⟩
  rintro a ⟨x, hx, rfl⟩
  have hpoint := summable_goodFieldTwo_point_tail_of_sup m j y omega hsum hx
  let pointTerm : ℕ → ℝ := fun i => if m + j ≤ i then
    4 * |omega i x - omega i y| else 0
  have hpoint_nonneg : ∀ i, 0 ≤ pointTerm i := by
    intro i
    dsimp [pointTerm]
    split <;> positivity
  have hsup_nonneg : ∀ i, 0 ≤ (if m + j ≤ i then
      4 * supNormOn W (fun x => omega i x - omega i y) else 0) := by
    intro i
    by_cases hi : m + j ≤ i
    · simp only [hi, if_true]
      have hsup : 0 ≤ supNormOn W (fun x => omega i x - omega i y) := by
        have hbdd := bddAbove_abs_values_translatedCube
          ((m + 1 + j : ℕ) : ℤ) y
            ((omega i).1.1.continuous.sub
              (continuous_const : Continuous (fun _ : Vec d => omega i y)))
        have hzero : y ∈ W := by
          apply mem_translatedCube_iff_sub_mem.mpr
          rw [cube, mem_openCubeSet_originCube_iff]
          intro k
          have hp : 0 < (3 : ℝ) ^ ((m + 1 + j : ℕ) : ℤ) :=
            zpow_pos (by norm_num) _
          constructor <;> simp only [Pi.zero_apply, sub_self] <;> nlinarith
        unfold supNormOn
        simpa [W, Pi.sub_def] using! (le_csSup hbdd ⟨y, hzero, rfl⟩)
      positivity
    · simp only [hi, if_false]
      exact le_rfl
  have hterm_le : ∀ i, pointTerm i ≤ (if m + j ≤ i then
      4 * supNormOn W (fun x => omega i x - omega i y) else 0) := by
    intro i
    by_cases hi : m + j ≤ i
    · simp only [pointTerm, hi, if_true]
      exact mul_le_mul_of_nonneg_left
        (abs_apply_le_supNormOn_translatedCube _ _
          ((omega i).1.1.continuous.sub
            (continuous_const : Continuous (fun _ : Vec d => omega i y))) hx) (by norm_num)
    · simp only [pointTerm, hi, if_false]
      exact le_rfl
  have htsum : (∑' i, pointTerm i) ≤ S := by
    exact Summable.tsum_le_tsum hterm_le hpoint hsum
  have htprod : (∏' i : ℕ, if m + j ≤ i then
      Real.exp (4 * |omega i x - omega i y|) else 1) =
      Real.exp (∑' i, pointTerm i) := by
    have heq : (fun i : ℕ => if m + j ≤ i then
        Real.exp (4 * |omega i x - omega i y|) else 1) =
        fun i => Real.exp (pointTerm i) := by
      funext i
      by_cases hi : m + j ≤ i <;> simp [pointTerm, hi]
    rw [heq]
    exact hpoint.hasSum.rexp.tprod_eq
  have hfinite : |finitePart x| ≤ C := hC ⟨x, hx, rfl⟩
  have htail : Real.exp (∑' i, pointTerm i) ≤ Real.exp S := Real.exp_le_exp.mpr htsum
  rw [htprod]
  have hfinite_nonneg : 0 ≤ finitePart x := by
    dsimp [finitePart]
    positivity
  have htail_nonneg : 0 ≤ Real.exp (∑' i, pointTerm i) := Real.exp_nonneg _
  rw [abs_of_nonneg (add_nonneg hfinite_nonneg htail_nonneg)]
  exact add_le_add ((le_abs_self (finitePart x)).trans hfinite) htail


/-! ## G4's guarded integral (audit F-08) -/

/-- Audit F-08: G4 supplies the integrability side condition that makes the
integral inside `tauSq` genuine. -/
theorem integrable_exp_zeroPotential_at_zero {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    Integrable (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d => Real.exp (g 0))
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure :=
  M.G4.exponential_integrable

/-- Audit F-08: the G4 integral is strictly positive, hence in particular is
not the zero junk input of `Real.log`. -/
theorem integral_exp_zeroPotential_at_zero_pos {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    0 < ∫ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
      Real.exp (g 0) ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := by
  exact integral_exp_pos (integrable_exp_zeroPotential_at_zero M)

/-- Audit F-08: the second G4 guard is the strict positivity of the derived
disorder strength. -/
theorem tauSq_pos_of_G4 {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    0 < SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P :=
  M.G4.tauSq_pos

end

end SubdiffusiveProcess.CoarseGrainingVocab
