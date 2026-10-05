module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StationaryHorizontalOrbit
public import Homogenization.Geometry.BoundaryLayer
public import Homogenization.Geometry.OriginCubeBoundaryPush
public import Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.QuantitativeCutoff.Basic
public import Homogenization.Sobolev.Foundations.QuantitativeCutoff
public import Homogenization.Sobolev.PotentialSolenoidal

@[expose] public section

/-!
# Boundary cutoff for realized stationary potentials

This supplies the deterministic localization step used in the finite-volume
Dirichlet exhaustion in `l.one.step.upper`: multiply a smooth spatial
primitive by a canonical cutoff supported strictly inside a triadic cube.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- Squared norm of an `L²` class as the energy of its representative. -/
theorem norm_sq_vectorL2_eq_integral_normSq
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {mu : Measure Omega} (F : Lp E 2 mu) :
    ‖F‖ ^ 2 = ∫ omega, ‖F omega‖ ^ 2 ∂mu := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def (𝕜 := ℝ)]
  exact integral_congr_ae
    (Filter.Eventually.of_forall fun omega =>
      real_inner_self_eq_norm_sq (F omega))

/-- Energy of a square-integrable representative equals the squared norm of
its `L²` class. -/
theorem integral_normSq_eq_norm_sq_toLp
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {mu : Measure Omega} {X : Omega → E} (hX : MemLp X 2 mu) :
    ∫ omega, ‖X omega‖ ^ 2 ∂mu = ‖hX.toLp X‖ ^ 2 := by
  rw [norm_sq_vectorL2_eq_integral_normSq]
  refine integral_congr_ae ?_
  filter_upwards [hX.coeFn_toLp] with omega hXt
  rw [hXt]

/-- Energy of a difference of representatives equals the squared distance of
their `L²` classes. -/
theorem integral_normSq_sub_eq_norm_sq_toLp
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {mu : Measure Omega} {X Y : Omega → E}
    (hX : MemLp X 2 mu) (hY : MemLp Y 2 mu) :
    ∫ omega, ‖X omega - Y omega‖ ^ 2 ∂mu =
      ‖hX.toLp X - hY.toLp Y‖ ^ 2 := by
  rw [norm_sq_vectorL2_eq_integral_normSq]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (hX.toLp X) (hY.toLp Y),
    hX.coeFn_toLp, hY.coeFn_toLp] with omega hsub hXt hYt
  rw [hsub]
  simp only [Pi.sub_apply, hXt, hYt]

/-- Canonical strongly measurable representative of a stationary scalar
`L²` class. -/
def stationaryScalarRepresentative {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (phi : Stationary.ScalarL2 M.P.toMeasure) : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ :=
  (Lp.aestronglyMeasurable phi).mk phi

theorem stronglyMeasurable_stationaryScalarRepresentative {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (phi : Stationary.ScalarL2 M.P.toMeasure) :
    StronglyMeasurable (stationaryScalarRepresentative M phi) :=
  (Lp.aestronglyMeasurable phi).stronglyMeasurable_mk

theorem memLp_two_stationaryScalarRepresentative {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (phi : Stationary.ScalarL2 M.P.toMeasure) :
    MemLp (stationaryScalarRepresentative M phi) 2 M.P.toMeasure :=
  (Lp.memLp phi).ae_eq (Lp.aestronglyMeasurable phi).ae_eq_mk

theorem toLp_stationaryScalarRepresentative {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (phi : Stationary.ScalarL2 M.P.toMeasure) :
    (memLp_two_stationaryScalarRepresentative M phi).toLp
        (stationaryScalarRepresentative M phi) = phi := by
  rw [MemLp.toLp_congr (memLp_two_stationaryScalarRepresentative M phi)
    (Lp.memLp phi) (Lp.aestronglyMeasurable phi).ae_eq_mk.symm,
    Lp.toLp_coeFn]

/-- A stationary vector field has a strongly continuous orbit as soon as
each scalar coordinate does. -/
theorem continuous_koopmanOrbit_of_continuous_vectorL2Coord {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (F : Stationary.VectorL2 d M.P.toMeasure)
    (hcoord : letI := potentialSequenceVAddInvariant M
      ∀ i : Fin d, Continuous (fun z : Vec d =>
        Stationary.koopman (mu := M.P.toMeasure) z
          (Stationary.vectorL2Coord (mu := M.P.toMeasure) i F))) :
    letI := potentialSequenceVAddInvariant M
    Continuous (fun z : Vec d =>
      Stationary.koopman (mu := M.P.toMeasure) z F) := by
  let := potentialSequenceVAddInvariant M
  classical
  let E : Fin d → Stationary.VectorL2 d M.P.toMeasure := fun i =>
    scalarToVectorL2 M.P.toMeasure (Pi.single i 1)
      (Stationary.vectorL2Coord (mu := M.P.toMeasure) i F)
  have hterm : ∀ i : Fin d, Continuous (fun z : Vec d =>
      Stationary.koopman (mu := M.P.toMeasure) z (E i)) := by
    intro i
    have hc := (scalarToVectorL2 M.P.toMeasure
      (Pi.single i 1)).continuous.comp (hcoord i)
    convert hc using 1
    funext z
    exact koopman_scalarToVectorL2 M z (Pi.single i 1)
      (Stationary.vectorL2Coord (mu := M.P.toMeasure) i F)
  have hsum : Continuous (fun z : Vec d => ∑ i : Fin d,
      Stationary.koopman (mu := M.P.toMeasure) z (E i)) :=
    continuous_finsetSum Finset.univ fun i _ => hterm i
  convert hsum using 1
  funext z
  rw [← map_sum]
  have hEF : ∑ i : Fin d, E i = F := by
    change assembleScalarCoordinates M (fun i =>
      Stationary.vectorL2Coord (mu := M.P.toMeasure) i F) = F
    exact assembleScalarCoordinates_vectorL2Coord M F
  rw [hEF]

/-- Coordinate identification between the honest samplewise gradient
representative and the Hilbert-space kernel derivative. -/
theorem vectorL2Coord_toLp_representativeMollifyGrad_eq {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa)
    {phi : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ} (hphim : StronglyMeasurable phi)
    (hphi : MemLp phi 2 M.P.toMeasure)
    {F : Stationary.VectorL2 d M.P.toMeasure}
    (hgrad : letI := potentialSequenceVAddInvariant M
      Stationary.HasHorizontalGradient (mu := M.P.toMeasure)
        (hphi.toLp phi) F)
    (i : Fin d) :
    letI := potentialSequenceVAddInvariant M
    Stationary.vectorL2Coord (mu := M.P.toMeasure) i
        ((memLp_two_representativeMollifyGrad M hcompact hkappa hphim hphi).toLp
          (representativeMollifyGrad kappa phi)) =
      Stationary.mollifyL2 (mu := M.P.toMeasure)
        (Stationary.kernelDeriv kappa i) (hphi.toLp phi) := by
  let := potentialSequenceVAddInvariant M
  let G := representativeMollifyGrad kappa phi
  let hGm := stronglyMeasurable_representativeMollifyGrad hkappa hphim
  let hG := memLp_two_representativeMollifyGrad M hcompact hkappa hphim hphi
  rw [vectorL2Coord_toLp_representative M hGm hG i]
  change (memLp_representativeCoord M hGm hG i).toLp
      (representativeMollify (Stationary.kernelDeriv kappa i) phi) = _
  have hrep := toLp_representativeMollify_eq_mollifyL2 M
    (Stationary.continuous_kernelDeriv hkappa i)
    (Stationary.hasCompactSupport_kernelDeriv hcompact i) hphim hphi
    hgrad.continuous_koopmanOrbit
  simpa only using hrep



theorem toLp_representativeMollifyGrad_eq_mollifiedGradientL2 {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa)
    {phi : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ} (hphim : StronglyMeasurable phi)
    (hphi : MemLp phi 2 M.P.toMeasure)
    {F : Stationary.VectorL2 d M.P.toMeasure}
    (hgrad : letI := potentialSequenceVAddInvariant M
      Stationary.HasHorizontalGradient (mu := M.P.toMeasure)
        (hphi.toLp phi) F) :
    letI := potentialSequenceVAddInvariant M
    (memLp_two_representativeMollifyGrad M hcompact hkappa hphim hphi).toLp
        (representativeMollifyGrad kappa phi) =
      mollifiedGradientL2 M kappa (hphi.toLp phi) := by
  let := potentialSequenceVAddInvariant M
  apply Stationary.vectorL2_eq_of_coord_eq
  intro i
  rw [mollifiedGradientL2, vectorL2Coord_assembleScalarCoordinates]
  exact vectorL2Coord_toLp_representativeMollifyGrad_eq
    M hcompact hkappa hphim hphi hgrad i

/-- Exact topology-free gradient identification in the assembled vector
carrier.  This is the GMC analogue of Superdiffusion's
`mollifyGrad_ae_eq_mollify`. -/
theorem toLp_representativeMollifyGrad_eq_assemble_mollifiedGradient
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa)
    {phi : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ} (hphim : StronglyMeasurable phi)
    (hphi : MemLp phi 2 M.P.toMeasure)
    {F : Stationary.VectorL2 d M.P.toMeasure}
    (hgrad : letI := potentialSequenceVAddInvariant M
      Stationary.HasHorizontalGradient (mu := M.P.toMeasure)
        (hphi.toLp phi) F) :
    letI := potentialSequenceVAddInvariant M
    (memLp_two_representativeMollifyGrad M hcompact hkappa hphim hphi).toLp
        (representativeMollifyGrad kappa phi) =
      assembleScalarCoordinates M fun i =>
        Stationary.mollifyL2 (mu := M.P.toMeasure) kappa
          (Stationary.vectorL2Coord (mu := M.P.toMeasure) i F) := by
  let := potentialSequenceVAddInvariant M
  rw [toLp_representativeMollifyGrad_eq_mollifiedGradientL2
    M hcompact hkappa hphim hphi hgrad]
  apply Stationary.vectorL2_eq_of_coord_eq
  intro i
  rw [mollifiedGradientL2, vectorL2Coord_assembleScalarCoordinates,
    vectorL2Coord_assembleScalarCoordinates]
  exact hgrad.mollifyL2_kernelDeriv_eq_coord hcompact hkappa i



theorem toLp_representativeMollifyGrad_eq_mollifyL2 {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa)
    {phi : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ} (hphim : StronglyMeasurable phi)
    (hphi : MemLp phi 2 M.P.toMeasure)
    {F : Stationary.VectorL2 d M.P.toMeasure}
    (hgrad : letI := potentialSequenceVAddInvariant M
      Stationary.HasHorizontalGradient (mu := M.P.toMeasure)
        (hphi.toLp phi) F) :
    letI := potentialSequenceVAddInvariant M
    (memLp_two_representativeMollifyGrad M hcompact hkappa hphim hphi).toLp
        (representativeMollifyGrad kappa phi) =
      Stationary.mollifyL2 (mu := M.P.toMeasure) kappa F := by
  let := potentialSequenceVAddInvariant M
  rw [toLp_representativeMollifyGrad_eq_assemble_mollifiedGradient
    M hcompact hkappa hphim hphi hgrad]
  have hFcont : Continuous (fun z : Vec d =>
      Stationary.koopman (mu := M.P.toMeasure) z F) :=
    continuous_koopmanOrbit_of_continuous_vectorL2Coord M F
      hgrad.continuous_koopmanOrbit_coord
  apply Stationary.vectorL2_eq_of_coord_eq
  intro i
  rw [vectorL2Coord_assembleScalarCoordinates,
    Stationary.vectorL2Coord_mollifyL2_of_continuous
      (mu := M.P.toMeasure) hkappa.continuous hcompact F hFcont i]

/-- Smooth, honestly represented horizontal gradients are dense in the
closed stationary-potential subspace.  The representative and mollifier are
returned explicitly so that the boundary-cutoff construction can consume
them without a measurable-selection gap. -/
theorem exists_mollifiedRepresentativeGradient_norm_sub_lt {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {F : Stationary.VectorL2 d M.P.toMeasure}
    (hF : letI := potentialSequenceVAddInvariant M
      F ∈ Stationary.stationaryPotentialSubspace
        (mu := M.P.toMeasure) (d := d))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ rho : Stationary.L2Mollifier d,
      ∃ phi : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ,
        ∃ hphim : StronglyMeasurable phi,
          ∃ hphi : MemLp phi 2 M.P.toMeasure,
            ‖(memLp_two_representativeMollifyGrad M rho.compactSupport
                rho.smooth hphim hphi).toLp
                  (representativeMollifyGrad rho.toFun phi) - F‖ < epsilon := by
  let := potentialSequenceVAddInvariant M
  let eta : ℝ := epsilon / 2
  have heta : 0 < eta := div_pos hepsilon (by norm_num)
  obtain ⟨psi, G, hpsi, hFG⟩ :=
    Stationary.exists_hasHorizontalGradient_norm_sub_lt hF heta
  have hGcont : Continuous (fun z : Vec d =>
      Stationary.koopman (mu := M.P.toMeasure) z G) :=
    continuous_koopmanOrbit_of_continuous_vectorL2Coord M G
      hpsi.continuous_koopmanOrbit_coord
  obtain ⟨rho, hrho⟩ :=
    Stationary.exists_mollifier_norm_mollifyL2_sub_lt_of_continuousAt
      (mu := M.P.toMeasure) G hGcont.continuousAt heta
  let phi := stationaryScalarRepresentative M psi
  let hphim : StronglyMeasurable phi :=
    stronglyMeasurable_stationaryScalarRepresentative M psi
  let hphi : MemLp phi 2 M.P.toMeasure :=
    memLp_two_stationaryScalarRepresentative M psi
  have hphiClass : hphi.toLp phi = psi := by
    exact toLp_stationaryScalarRepresentative M psi
  have hgradRep : Stationary.HasHorizontalGradient (mu := M.P.toMeasure)
      (hphi.toLp phi) G := by
    simpa only [hphiClass] using hpsi
  refine ⟨rho, phi, hphim, hphi, ?_⟩
  rw [toLp_representativeMollifyGrad_eq_mollifyL2 M
    rho.compactSupport rho.smooth hphim hphi hgradRep]
  calc
    ‖Stationary.mollifyL2 (mu := M.P.toMeasure) rho.toFun G - F‖ ≤
        ‖Stationary.mollifyL2 (mu := M.P.toMeasure) rho.toFun G - G‖ +
          ‖G - F‖ := by
      simpa only [dist_eq_norm] using
        dist_triangle
          (Stationary.mollifyL2 (mu := M.P.toMeasure) rho.toFun G) G F
    _ < eta + eta := add_lt_add hrho (by simpa only [norm_sub_rev] using hFG)
    _ = epsilon := by dsimp only [eta]; ring

/-- Inner ratio of the stationary-potential cutoff at boundary scale `L`. -/
def stationaryCutoffInnerRatio (L : ℕ) : ℝ :=
  1 - (3 : ℝ) ^ (-(L : ℤ)) / 2

/-- Outer ratio of the stationary-potential cutoff at boundary scale `L`. -/
def stationaryCutoffOuterRatio (L : ℕ) : ℝ :=
  1 - (3 : ℝ) ^ (-(L : ℤ)) / 4

theorem three_zpow_neg_pos (L : ℕ) : 0 < (3 : ℝ) ^ (-(L : ℤ)) :=
  zpow_pos (by norm_num) _

theorem three_zpow_neg_le_one (L : ℕ) : (3 : ℝ) ^ (-(L : ℤ)) ≤ 1 := by
  apply zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 3)
  simp

theorem stationaryCutoffInnerRatio_pos (L : ℕ) :
    0 < stationaryCutoffInnerRatio L := by
  have := three_zpow_neg_le_one L
  unfold stationaryCutoffInnerRatio
  linarith

theorem stationaryCutoffInnerRatio_nonneg (L : ℕ) :
    0 ≤ stationaryCutoffInnerRatio L :=
  (stationaryCutoffInnerRatio_pos L).le

theorem stationaryCutoffInnerRatio_le_one (L : ℕ) :
    stationaryCutoffInnerRatio L ≤ 1 := by
  have hpos := three_zpow_neg_pos L
  unfold stationaryCutoffInnerRatio
  linarith

private theorem one_sub_pow_le_mul_one_sub (n : ℕ) {ρ : ℝ}
    (h0 : 0 ≤ ρ) :
    1 - ρ ^ n ≤ (n : ℝ) * (1 - ρ) := by
  have hbase : (-2 : ℝ) ≤ ρ - 1 := by linarith
  have hpow : 1 + (n : ℝ) * (ρ - 1) ≤ (1 + (ρ - 1)) ^ n :=
    one_add_mul_le_pow hbase n
  have hsimp : (1 : ℝ) + (ρ - 1) = ρ := by ring
  rw [hsimp] at hpow
  nlinarith [hpow]

theorem one_sub_stationaryCutoffInnerRatio_pow_le (d L : ℕ) :
    1 - stationaryCutoffInnerRatio L ^ d ≤
      (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) / 2 := by
  have hbern := one_sub_pow_le_mul_one_sub d
    (stationaryCutoffInnerRatio_nonneg L)
  have hrw : (1 : ℝ) - stationaryCutoffInnerRatio L =
      (3 : ℝ) ^ (-(L : ℤ)) / 2 := by
    unfold stationaryCutoffInnerRatio
    ring
  rw [hrw] at hbern
  linarith

theorem stationaryCutoffInnerRatio_lt_outer (L : ℕ) :
    stationaryCutoffInnerRatio L < stationaryCutoffOuterRatio L := by
  have := three_zpow_neg_pos L
  unfold stationaryCutoffInnerRatio stationaryCutoffOuterRatio
  linarith

theorem stationaryCutoffOuterRatio_lt_one (L : ℕ) :
    stationaryCutoffOuterRatio L < 1 := by
  have := three_zpow_neg_pos L
  unfold stationaryCutoffOuterRatio
  linarith

theorem stationaryCutoffOuter_sub_inner (L : ℕ) :
    stationaryCutoffOuterRatio L - stationaryCutoffInnerRatio L =
      (3 : ℝ) ^ (-(L : ℤ)) / 4 := by
  unfold stationaryCutoffInnerRatio stationaryCutoffOuterRatio
  ring

/-- The canonical cutoff used to localize a stationary primitive to `Q`. -/
def stationaryPotentialCutoff {d : ℕ} (Q : TriadicCube d) (L : ℕ) :
    QuantitativeCubeCutoff Q (stationaryCutoffInnerRatio L)
      (stationaryCutoffOuterRatio L) :=
  QuantitativeCubeCutoff.canonical Q _ _ (stationaryCutoffInnerRatio_pos L)
    (stationaryCutoffInnerRatio_lt_outer L)

theorem stationaryPotentialCutoff_tsupport_subset {d : ℕ}
    (Q : TriadicCube d) (L : ℕ) :
    tsupport (stationaryPotentialCutoff Q L).toFun ⊆ openCubeSet Q := by
  exact (stationaryPotentialCutoff Q L).tsupport_subset_openCubeSet_of_lt_one
    (by
      have := three_zpow_neg_le_one L
      unfold stationaryCutoffOuterRatio
      linarith)
    (stationaryCutoffOuterRatio_lt_one L)

/-- Uniform gradient bound for the canonical cutoff. -/
def stationaryPotentialCutoffGradBound {d : ℕ}
    (Q : TriadicCube d) (L : ℕ) : ℝ :=
  (d : ℝ) * (quantitativeCubeCutoffGradientConst d /
    ((stationaryCutoffOuterRatio L - stationaryCutoffInnerRatio L) *
      cubeRadius Q))

/-- Hilbert-vector form of the cutoff gradient. -/
def stationaryPotentialCutoffHilbertGrad {d : ℕ}
    (Q : TriadicCube d) (L : ℕ) (x : Vec d) : HilbertVec d :=
  HilbertVec.ofVec fun i =>
    fderiv ℝ (stationaryPotentialCutoff Q L).toFun x (basisVec i)

private theorem norm_basisVec_le_one {d : ℕ} (i : Fin d) :
    ‖(basisVec i : Vec d)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
  by_cases h : j = i
  · subst h
    simp [basisVec]
  · simp [basisVec, h]

theorem norm_stationaryPotentialCutoffHilbertGrad_le {d : ℕ}
    (Q : TriadicCube d) (L : ℕ) (x : Vec d) :
    ‖stationaryPotentialCutoffHilbertGrad Q L x‖ ≤
      stationaryPotentialCutoffGradBound Q L := by
  have hcoord : ‖(fun i => fderiv ℝ
      (stationaryPotentialCutoff Q L).toFun x (basisVec i) : Vec d)‖ ≤
      ‖fderiv ℝ (stationaryPotentialCutoff Q L).toFun x‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    calc
      ‖fderiv ℝ (stationaryPotentialCutoff Q L).toFun x
          (basisVec i)‖ ≤
          ‖fderiv ℝ (stationaryPotentialCutoff Q L).toFun x‖ *
            ‖(basisVec i : Vec d)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ (stationaryPotentialCutoff Q L).toFun x‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_basisVec_le_one i) (norm_nonneg _)
      _ = _ := mul_one _
  calc
    ‖stationaryPotentialCutoffHilbertGrad Q L x‖ ≤
        (d : ℝ) * ‖(fun i => fderiv ℝ
          (stationaryPotentialCutoff Q L).toFun x (basisVec i) : Vec d)‖ :=
      HilbertVec.norm_ofVec_le_mul_norm _
    _ ≤ (d : ℝ) *
        ‖fderiv ℝ (stationaryPotentialCutoff Q L).toFun x‖ :=
      mul_le_mul_of_nonneg_left hcoord (Nat.cast_nonneg d)
    _ ≤ stationaryPotentialCutoffGradBound Q L :=
      mul_le_mul_of_nonneg_left
        ((stationaryPotentialCutoff Q L).gradient_bound x)
        (Nat.cast_nonneg d)

theorem stationaryPotentialCutoffGradBound_nonneg {d : ℕ}
    (Q : TriadicCube d) (L : ℕ) :
    0 ≤ stationaryPotentialCutoffGradBound Q L :=
  (norm_nonneg _).trans
    (norm_stationaryPotentialCutoffHilbertGrad_le Q L 0)

/-- Explicit decay of the cutoff gradient on an expanding origin cube. -/
theorem stationaryPotentialCutoffGradBound_originCube
    (d K L : ℕ) :
    stationaryPotentialCutoffGradBound (originCube d (K : ℤ)) L =
      ((d : ℝ) * quantitativeCubeCutoffGradientConst d * 8 *
        (3 : ℝ) ^ L) * ((3 : ℝ) ^ K)⁻¹ := by
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (-(L : ℤ)) :=
    three_zpow_neg_pos L
  have hK : (0 : ℝ) < (3 : ℝ) ^ K := by positivity
  have hrad : cubeRadius (originCube d (K : ℤ)) =
      (1 / 2 : ℝ) * (3 : ℝ) ^ K := by
    simp [cubeRadius, cubeScaleFactor, originCube, zpow_natCast]
  have hL : (3 : ℝ) ^ (-(L : ℤ)) = ((3 : ℝ) ^ L)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  have hLpos : (0 : ℝ) < (3 : ℝ) ^ L := by positivity
  rw [stationaryPotentialCutoffGradBound,
    stationaryCutoffOuter_sub_inner, hrad, hL]
  field_simp
  ring

/-- At a fixed boundary-strip depth, the canonical cutoff gradient vanishes
on expanding origin cubes.  This is the large-volume limit needed before the
strip depth is sent to infinity in the Dirichlet comparison. -/
theorem tendsto_stationaryPotentialCutoffGradBound_originCube
    (d L : ℕ) :
    Filter.Tendsto
      (fun K : ℕ =>
        stationaryPotentialCutoffGradBound (originCube d (K : ℤ)) L)
      Filter.atTop (nhds 0) := by
  have hpow : Filter.Tendsto (fun K : ℕ => ((3 : ℝ)⁻¹) ^ K)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
  have hscaled := hpow.const_mul
    ((d : ℝ) * quantitativeCubeCutoffGradientConst d * 8 * (3 : ℝ) ^ L)
  convert hscaled using 1
  · funext K
    rw [stationaryPotentialCutoffGradBound_originCube, inv_pow]
  · simp

/-- Consequently the primitive-error term in the normalized cutoff estimate
vanishes on expanding origin cubes. -/
theorem tendsto_stationaryPotentialCutoffPrimitivePrice_originCube
    (d L : ℕ) (Iphi : ℝ) :
    Filter.Tendsto
      (fun K : ℕ =>
        2 * stationaryPotentialCutoffGradBound
              (originCube d (K : ℤ)) L ^ 2 * Iphi)
      Filter.atTop (nhds 0) := by
  have hgrad := tendsto_stationaryPotentialCutoffGradBound_originCube d L
  convert ((hgrad.pow 2).const_mul (2 * Iphi)) using 1
  · funext K
    ring
  · simp

/-- Boundary strip on which the canonical cutoff may differ from one. -/
def stationaryPotentialBoundaryStrip {d : ℕ}
    (Q : TriadicCube d) (L : ℕ) : Set (Vec d) :=
  cubeSet Q \
    scaledClosedCubeSet Q (stationaryCutoffInnerRatio L)

theorem stationaryPotentialBoundaryStrip_subset_cubeSet {d : ℕ}
    (Q : TriadicCube d) (L : ℕ) :
    stationaryPotentialBoundaryStrip Q L ⊆ cubeSet Q := Set.sdiff_subset

theorem measurableSet_stationaryPotentialBoundaryStrip {d : ℕ}
    (Q : TriadicCube d) (L : ℕ) :
    MeasurableSet (stationaryPotentialBoundaryStrip Q L) :=
  (measurableSet_cubeSet Q).diff
    (isClosed_scaledClosedCubeSet Q _).measurableSet

theorem volume_stationaryPotentialBoundaryStrip_ne_top {d : ℕ}
    (Q : TriadicCube d) (L : ℕ) :
    volume (stationaryPotentialBoundaryStrip Q L) ≠ ⊤ :=
  measure_ne_top_of_subset Set.sdiff_subset (volume_cubeSet_lt_top Q).ne

private theorem cubeShrunkSet_subset_scaledClosedCubeSet {d : ℕ}
    (Q : TriadicCube d) (ρ : ℝ) :
    cubeShrunkSet Q ((1 - ρ) / 2) ⊆ scaledClosedCubeSet Q ρ := by
  intro x hx i
  have hxi := hx i
  have hs : (0 : ℝ) < cubeScaleFactor Q :=
    zpow_pos (by norm_num : (0 : ℝ) < 3) Q.scale
  rw [abs_le]
  constructor
  · have := hxi.1
    have hrad : cubeRadius Q = (1 / 2 : ℝ) * cubeScaleFactor Q := rfl
    have hc : cubeCenter Q i = (Q.index i : ℝ) * cubeScaleFactor Q := rfl
    rw [hrad, hc]
    nlinarith [this]
  · have := hxi.2
    have hrad : cubeRadius Q = (1 / 2 : ℝ) * cubeScaleFactor Q := rfl
    have hc : cubeCenter Q i = (Q.index i : ℝ) * cubeScaleFactor Q := rfl
    rw [hrad, hc]
    nlinarith [this]

private theorem cubeSet_diff_scaledClosedCubeSet_subset {d : ℕ}
    (Q : TriadicCube d) (ρ : ℝ) :
    cubeSet Q \ scaledClosedCubeSet Q ρ ⊆
      cubeBoundaryLayer Q ((1 - ρ) / 2) :=
  fun _ hx => ⟨hx.1, fun hmem =>
    hx.2 (cubeShrunkSet_subset_scaledClosedCubeSet Q ρ hmem)⟩

private theorem volume_cubeSet_diff_scaledClosedCubeSet_toReal_le {d : ℕ}
    (Q : TriadicCube d) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (volume (cubeSet Q \ scaledClosedCubeSet Q ρ)).toReal ≤
      (1 - ρ ^ d) * cubeVolume Q := by
  have ht0 : (0 : ℝ) ≤ (1 - ρ) / 2 := by linarith
  have hthalf : (1 - ρ) / 2 ≤ (1 / 2 : ℝ) := by linarith
  have hlayer := volume_cubeBoundaryLayer_toReal_of_nonneg_le_half Q ht0 hthalf
  have hsub : volume (cubeSet Q \ scaledClosedCubeSet Q ρ) ≤
      volume (cubeBoundaryLayer Q ((1 - ρ) / 2)) :=
    measure_mono (cubeSet_diff_scaledClosedCubeSet_subset Q ρ)
  have hfin : volume (cubeBoundaryLayer Q ((1 - ρ) / 2)) ≠ ⊤ :=
    measure_ne_top_of_subset (cubeBoundaryLayer_subset_cubeSet Q _)
      (volume_cubeSet_lt_top Q).ne
  have hmono := ENNReal.toReal_mono hfin hsub
  refine hmono.trans ?_
  rw [hlayer]
  have hrw : 1 - 2 * ((1 - ρ) / 2) = ρ := by ring
  rw [hrw]
  have hvol : cubeVolume Q = cubeScaleFactor Q ^ d := rfl
  rw [hvol, mul_pow]
  ring_nf
  exact le_rfl

/-- Explicit boundary-strip volume fraction. -/
theorem volume_stationaryPotentialBoundaryStrip_toReal_le {d : ℕ}
    (Q : TriadicCube d) (L : ℕ) :
    (volume (stationaryPotentialBoundaryStrip Q L)).toReal ≤
      (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) / 2 * cubeVolume Q := by
  refine (volume_cubeSet_diff_scaledClosedCubeSet_toReal_le Q
    (stationaryCutoffInnerRatio_nonneg L)
    (stationaryCutoffInnerRatio_le_one L)).trans ?_
  exact mul_le_mul_of_nonneg_right
    (one_sub_stationaryCutoffInnerRatio_pow_le d L)
    (cubeVolume_nonneg Q)

/-- Euclidean gradient of the canonical boundary cutoff. -/
def stationaryPotentialCutoffGrad {d : ℕ}
    (Q : TriadicCube d) (L : ℕ) (x : Vec d) : Vec d :=
  fun i => fderiv ℝ (stationaryPotentialCutoff Q L).toFun x (basisVec i)

/-- Gradient formula for the localized scalar primitive `eta * phi`. -/
def stationaryPotentialLocalGrad {d : ℕ}
    (Q : TriadicCube d) (L : ℕ) (phi : Vec d → ℝ) : Vec d → Vec d :=
  fun x i =>
    (stationaryPotentialCutoff Q L).toFun x *
        fderiv ℝ phi x (basisVec i) +
      phi x * stationaryPotentialCutoffGrad Q L x i

/-- Localized gradient written directly from stationary representatives. -/
def stationaryRepresentativeLocalGrad {d : ℕ}
    (Q : TriadicCube d) (L : ℕ)
    (phi : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ) (P : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : Vec d → Vec d :=
  fun x i =>
    (stationaryPotentialCutoff Q L).toFun x * (realize P omega x).toVec i +
      realize phi omega x * fderiv ℝ
        (stationaryPotentialCutoff Q L).toFun x (basisVec i)

/-- Exact product-rule decomposition of the localized representative. -/
theorem ofVec_stationaryRepresentativeLocalGrad_sub_realize {d : ℕ}
    (Q : TriadicCube d) (L : ℕ)
    (phi : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ) (P : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Vec d) :
    HilbertVec.ofVec (stationaryRepresentativeLocalGrad Q L phi P omega x) -
        realize P omega x =
      ((stationaryPotentialCutoff Q L).toFun x - 1) • realize P omega x +
        realize phi omega x • stationaryPotentialCutoffHilbertGrad Q L x := by
  ext i
  simp [stationaryRepresentativeLocalGrad,
    stationaryPotentialCutoffHilbertGrad, HilbertVec.toVec]
  ring

/-- The displayed local gradient is exactly the derivative of the cutoff
product. -/
theorem fderiv_cutoff_mul_apply {d : ℕ}
    (Q : TriadicCube d) (L : ℕ) {phi : Vec d → ℝ}
    (hphi : ContDiff ℝ (⊤ : ℕ∞) phi) (x : Vec d) (i : Fin d) :
    fderiv ℝ (fun y => (stationaryPotentialCutoff Q L).toFun y * phi y) x
        (basisVec i) = stationaryPotentialLocalGrad Q L phi x i := by
  have heta : HasFDerivAt (stationaryPotentialCutoff Q L).toFun
      (fderiv ℝ (stationaryPotentialCutoff Q L).toFun x) x :=
    ((stationaryPotentialCutoff Q L).smooth.differentiable (by simp) x).hasFDerivAt
  have hphi' : HasFDerivAt phi (fderiv ℝ phi x) x :=
    (hphi.differentiable (by simp) x).hasFDerivAt
  change fderiv ℝ ((stationaryPotentialCutoff Q L).toFun * phi) x
      (basisVec i) = _
  rw [(heta.mul hphi').fderiv]
  rfl

/-- Multiplying a smooth primitive by the canonical cutoff gives an honest
zero-trace potential competitor on the cube. -/
theorem isPotentialZeroTraceOn_stationaryPotentialLocalGrad {d : ℕ}
    (Q : TriadicCube d) (L : ℕ) {phi : Vec d → ℝ}
    (hphi : ContDiff ℝ (⊤ : ℕ∞) phi) :
    IsPotentialZeroTraceOn (openCubeSet Q)
      (stationaryPotentialLocalGrad Q L phi) := by
  have heta := (stationaryPotentialCutoff Q L).smooth
  have hprod : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : Vec d => (stationaryPotentialCutoff Q L).toFun y * phi y) :=
    heta.mul hphi
  have hsupp : HasCompactSupport
      (fun y : Vec d => (stationaryPotentialCutoff Q L).toFun y * phi y) :=
    (stationaryPotentialCutoff Q L).hasCompactSupport.mul_right
  have hsub : tsupport
      (fun y : Vec d => (stationaryPotentialCutoff Q L).toFun y * phi y) ⊆
      openCubeSet Q :=
    subset_trans (closure_mono (Function.support_mul_subset_left _ _))
      (stationaryPotentialCutoff_tsupport_subset Q L)
  have hbase := isPotentialZeroTraceOn_of_contDiff
    (isOpen_openCubeSet Q) hprod hsupp hsub
  refine (show (fun (x : Vec d) i =>
      fderiv ℝ
        (fun y : Vec d => (stationaryPotentialCutoff Q L).toFun y * phi y)
        x (basisVec i)) = stationaryPotentialLocalGrad Q L phi from ?_) ▸ hbase
  funext x i
  exact fderiv_cutoff_mul_apply Q L hphi x i

/-- Representative form of the zero-trace membership theorem. -/
theorem isPotentialZeroTraceOn_stationaryRepresentativeLocalGrad {d : ℕ}
    (Q : TriadicCube d) (L : ℕ)
    {phi : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ} {P : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d}
    {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d}
    (hsmooth : ContDiff ℝ (⊤ : ℕ∞) (realize phi omega))
    (hgrad : ∀ (x : Vec d) (i : Fin d),
      fderiv ℝ (realize phi omega) x (basisVec i) =
        (realize P omega x).toVec i) :
    IsPotentialZeroTraceOn (openCubeSet Q)
      (stationaryRepresentativeLocalGrad Q L phi P omega) := by
  have heq : stationaryRepresentativeLocalGrad Q L phi P omega =
      stationaryPotentialLocalGrad Q L (realize phi omega) := by
    funext x i
    simp only [stationaryRepresentativeLocalGrad,
      stationaryPotentialLocalGrad, stationaryPotentialCutoffGrad,
      hgrad x i]
  rw [heq]
  exact isPotentialZeroTraceOn_stationaryPotentialLocalGrad Q L hsmooth

/-- Pointwise quadratic cutoff error.  The first term is confined to the
boundary strip and the second is the controlled primitive/cutoff-gradient
term. -/
theorem norm_sq_stationaryRepresentativeLocalGrad_sub_le {d : ℕ}
    (Q : TriadicCube d) (L : ℕ)
    (phi : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ) (P : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) {x : Vec d} (hx : x ∈ cubeSet Q) :
    ‖HilbertVec.ofVec (stationaryRepresentativeLocalGrad Q L phi P omega x) -
        realize P omega x‖ ^ 2 ≤
      2 * (cubeSet Q \
          scaledClosedCubeSet Q (stationaryCutoffInnerRatio L)).indicator
            (fun y => ‖realize P omega y‖ ^ 2) x +
        2 * stationaryPotentialCutoffGradBound Q L ^ 2 *
          ‖realize phi omega x‖ ^ 2 := by
  have hdec := ofVec_stationaryRepresentativeLocalGrad_sub_realize
    Q L phi P omega x
  have hgb := norm_stationaryPotentialCutoffHilbertGrad_le Q L x
  have hgb0 := stationaryPotentialCutoffGradBound_nonneg Q L
  have hsecond :
      ‖realize phi omega x • stationaryPotentialCutoffHilbertGrad Q L x‖ ≤
        ‖realize phi omega x‖ * stationaryPotentialCutoffGradBound Q L := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left hgb (norm_nonneg _)
  by_cases hmem : x ∈
      scaledClosedCubeSet Q (stationaryCutoffInnerRatio L)
  · have hone : (stationaryPotentialCutoff Q L).toFun x = 1 :=
      (stationaryPotentialCutoff Q L).eq_one_on_inner x hmem
    have hind : (cubeSet Q \
        scaledClosedCubeSet Q (stationaryCutoffInnerRatio L)).indicator
          (fun y => ‖realize P omega y‖ ^ 2) x = 0 :=
      Set.indicator_of_notMem (fun h => h.2 hmem) _
    have hle :
        ‖HilbertVec.ofVec
            (stationaryRepresentativeLocalGrad Q L phi P omega x) -
          realize P omega x‖ ≤
            ‖realize phi omega x‖ *
              stationaryPotentialCutoffGradBound Q L := by
      rw [hdec, hone]
      simpa using hsecond
    rw [hind]
    nlinarith [norm_nonneg
      (HilbertVec.ofVec (stationaryRepresentativeLocalGrad Q L phi P omega x) -
        realize P omega x),
      mul_nonneg (norm_nonneg (realize phi omega x)) hgb0]
  · have hxmem : x ∈ cubeSet Q \
        scaledClosedCubeSet Q (stationaryCutoffInnerRatio L) :=
      Set.mem_sdiff_of_mem hx hmem
    have hind : (cubeSet Q \
        scaledClosedCubeSet Q (stationaryCutoffInnerRatio L)).indicator
          (fun y => ‖realize P omega y‖ ^ 2) x =
            ‖realize P omega x‖ ^ 2 :=
      Set.indicator_of_mem hxmem _
    have hcut : ‖(stationaryPotentialCutoff Q L).toFun x - 1‖ ≤ 1 := by
      have h0 := (stationaryPotentialCutoff Q L).nonneg x
      have h1 := (stationaryPotentialCutoff Q L).le_one x
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have hfirst :
        ‖((stationaryPotentialCutoff Q L).toFun x - 1) •
          realize P omega x‖ ≤ ‖realize P omega x‖ := by
      rw [norm_smul]
      calc
        ‖(stationaryPotentialCutoff Q L).toFun x - 1‖ *
            ‖realize P omega x‖ ≤ 1 * ‖realize P omega x‖ :=
          mul_le_mul_of_nonneg_right hcut (norm_nonneg _)
        _ = ‖realize P omega x‖ := one_mul _
    have hle :
        ‖HilbertVec.ofVec
            (stationaryRepresentativeLocalGrad Q L phi P omega x) -
          realize P omega x‖ ≤
        ‖realize P omega x‖ +
          ‖realize phi omega x‖ *
            stationaryPotentialCutoffGradBound Q L := by
      rw [hdec]
      exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)
    rw [hind]
    nlinarith [norm_nonneg
      (HilbertVec.ofVec (stationaryRepresentativeLocalGrad Q L phi P omega x) -
        realize P omega x),
      mul_nonneg (norm_nonneg (realize phi omega x)) hgb0,
      norm_nonneg (realize P omega x),
      sq_nonneg (‖realize P omega x‖ -
        ‖realize phi omega x‖ * stationaryPotentialCutoffGradBound Q L)]

/-- Expected unnormalized cutoff error on a fixed cube. -/
theorem integral_setIntegral_normSq_stationaryRepresentativeLocalGrad_sub_le
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Q : TriadicCube d) (L : ℕ)
    {phi : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ} {P : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d}
    (hphim : StronglyMeasurable phi) (hphi : MemLp phi 2 M.P.toMeasure)
    (hPm : StronglyMeasurable P) (hP : MemLp P 2 M.P.toMeasure) :
    ∫ omega, (∫ x in cubeSet Q,
        ‖HilbertVec.ofVec
            (stationaryRepresentativeLocalGrad Q L phi P omega x) -
          realize P omega x‖ ^ 2) ∂M.P.toMeasure ≤
      2 * ((volume (stationaryPotentialBoundaryStrip Q L)).toReal *
          ∫ omega, ‖P omega‖ ^ 2 ∂M.P.toMeasure) +
        2 * stationaryPotentialCutoffGradBound Q L ^ 2 *
          (cubeVolume Q * ∫ omega, ‖phi omega‖ ^ 2 ∂M.P.toMeasure) := by
  have hQfin : volume (cubeSet Q) ≠ ⊤ := (volume_cubeSet_lt_top Q).ne
  have hSfin := volume_stationaryPotentialBoundaryStrip_ne_top Q L
  have hSmeas := measurableSet_stationaryPotentialBoundaryStrip Q L
  let G := stationaryPotentialCutoffGradBound Q L
  have hdomint : Integrable (fun omega =>
      2 * (∫ x in stationaryPotentialBoundaryStrip Q L,
        ‖realize P omega x‖ ^ 2) +
      2 * G ^ 2 * ∫ x in cubeSet Q, ‖realize phi omega x‖ ^ 2)
      M.P.toMeasure :=
    ((integrable_setIntegral_normSq_realize M hSfin hPm hP).const_mul 2).add
      ((integrable_setIntegral_normSq_realize M hQfin hphim hphi).const_mul
        (2 * G ^ 2))
  have hmono :
      ∫ omega, (∫ x in cubeSet Q,
          ‖HilbertVec.ofVec
              (stationaryRepresentativeLocalGrad Q L phi P omega x) -
            realize P omega x‖ ^ 2) ∂M.P.toMeasure ≤
        ∫ omega, (2 *
            (∫ x in stationaryPotentialBoundaryStrip Q L,
              ‖realize P omega x‖ ^ 2) +
          2 * G ^ 2 * ∫ x in cubeSet Q,
            ‖realize phi omega x‖ ^ 2) ∂M.P.toMeasure := by
    refine integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun _ => integral_nonneg fun _ => by positivity)
      hdomint ?_
    filter_upwards [ae_memLp_two_realize M hSfin hPm hP,
      ae_memLp_two_realize M hQfin hphim hphi,
      ae_memLp_two_realize M hQfin hPm hP] with omega hPS hphiQ hPQ
    have hPSint : Integrable (fun x => ‖realize P omega x‖ ^ 2)
        (volume.restrict (stationaryPotentialBoundaryStrip Q L)) :=
      (memLp_two_iff_integrable_sq_norm
        (stronglyMeasurable_realize hPm omega).aestronglyMeasurable).1 hPS
    have hphiQint : Integrable (fun x => ‖realize phi omega x‖ ^ 2)
        (volume.restrict (cubeSet Q)) :=
      (memLp_two_iff_integrable_sq_norm
        (stronglyMeasurable_realize hphim omega).aestronglyMeasurable).1 hphiQ
    have hindvol : Integrable
        ((stationaryPotentialBoundaryStrip Q L).indicator
          fun y => ‖realize P omega y‖ ^ 2) volume :=
      MeasureTheory.IntegrableOn.integrable_indicator hPSint hSmeas
    have hindint : Integrable
        ((stationaryPotentialBoundaryStrip Q L).indicator
          fun y => ‖realize P omega y‖ ^ 2)
        (volume.restrict (cubeSet Q)) :=
      hindvol.mono_measure Measure.restrict_le_self
    have hbound : Integrable (fun x =>
        2 * (stationaryPotentialBoundaryStrip Q L).indicator
              (fun y => ‖realize P omega y‖ ^ 2) x +
          2 * G ^ 2 * ‖realize phi omega x‖ ^ 2)
        (volume.restrict (cubeSet Q)) :=
      (hindint.const_mul 2).add (hphiQint.const_mul (2 * G ^ 2))
    have hinner :
        (∫ x in cubeSet Q,
          ‖HilbertVec.ofVec
              (stationaryRepresentativeLocalGrad Q L phi P omega x) -
            realize P omega x‖ ^ 2) ≤
        ∫ x in cubeSet Q,
          (2 * (stationaryPotentialBoundaryStrip Q L).indicator
                (fun y => ‖realize P omega y‖ ^ 2) x +
            2 * G ^ 2 * ‖realize phi omega x‖ ^ 2) := by
      refine integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _ => by positivity) hbound ?_
      refine (ae_restrict_iff' (measurableSet_cubeSet Q)).2 ?_
      filter_upwards with x hx
      simpa only [stationaryPotentialBoundaryStrip, G] using
        norm_sq_stationaryRepresentativeLocalGrad_sub_le
          Q L phi P omega hx
    refine hinner.trans (le_of_eq ?_)
    rw [integral_add (hindint.const_mul 2)
        (hphiQint.const_mul (2 * G ^ 2)),
      integral_const_mul, integral_const_mul,
      setIntegral_indicator hSmeas,
      Set.inter_eq_self_of_subset_right
        (stationaryPotentialBoundaryStrip_subset_cubeSet Q L)]
  refine hmono.trans (le_of_eq ?_)
  rw [integral_add
      ((integrable_setIntegral_normSq_realize M hSfin hPm hP).const_mul 2)
      ((integrable_setIntegral_normSq_realize M hQfin hphim hphi).const_mul
        (2 * G ^ 2)),
    integral_const_mul, integral_const_mul,
    integral_setIntegral_normSq_realize M hSfin hPm hP,
    integral_setIntegral_normSq_realize M hQfin hphim hphi,
    volume_cubeSet_toReal]

/-- Normalized expected cutoff error.  The boundary price is exactly
`d * 3^(-L)` and the primitive price is the squared cutoff-gradient bound. -/
theorem normalized_integral_setIntegral_normSq_stationaryRepresentativeLocalGrad_sub_le
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Q : TriadicCube d) (L : ℕ)
    {phi : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ} {P : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d}
    (hphim : StronglyMeasurable phi) (hphi : MemLp phi 2 M.P.toMeasure)
    (hPm : StronglyMeasurable P) (hP : MemLp P 2 M.P.toMeasure) :
    (cubeVolume Q)⁻¹ *
        (∫ omega, (∫ x in cubeSet Q,
          ‖HilbertVec.ofVec
              (stationaryRepresentativeLocalGrad Q L phi P omega x) -
            realize P omega x‖ ^ 2) ∂M.P.toMeasure) ≤
      (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) *
          (∫ omega, ‖P omega‖ ^ 2 ∂M.P.toMeasure) +
        2 * stationaryPotentialCutoffGradBound Q L ^ 2 *
          (∫ omega, ‖phi omega‖ ^ 2 ∂M.P.toMeasure) := by
  let V := cubeVolume Q
  let S := (volume (stationaryPotentialBoundaryStrip Q L)).toReal
  let D := (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ))
  let IP := ∫ omega, ‖P omega‖ ^ 2 ∂M.P.toMeasure
  let Iphi := ∫ omega, ‖phi omega‖ ^ 2 ∂M.P.toMeasure
  let G := stationaryPotentialCutoffGradBound Q L
  let A := ∫ omega, (∫ x in cubeSet Q,
    ‖HilbertVec.ofVec
        (stationaryRepresentativeLocalGrad Q L phi P omega x) -
      realize P omega x‖ ^ 2) ∂M.P.toMeasure
  have hV : 0 < V := cubeVolume_pos Q
  have hIP : 0 ≤ IP := integral_nonneg fun _ => by positivity
  have hraw : A ≤ 2 * (S * IP) + 2 * G ^ 2 * (V * Iphi) := by
    exact integral_setIntegral_normSq_stationaryRepresentativeLocalGrad_sub_le
      M Q L hphim hphi hPm hP
  have hscaled := mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hV.le)
  have hstrip : S ≤ D / 2 * V := by
    simpa only [S, D, div_mul_eq_mul_div, mul_assoc] using
      volume_stationaryPotentialBoundaryStrip_toReal_le Q L
  have hstripScaled : 2 * V⁻¹ * S ≤ D := by
    calc
      2 * V⁻¹ * S ≤ 2 * V⁻¹ * (D / 2 * V) :=
        mul_le_mul_of_nonneg_left hstrip
          (mul_nonneg (by norm_num) (inv_nonneg.mpr hV.le))
      _ = D := by
        field_simp
  have hstripMoment : (2 * V⁻¹ * S) * IP ≤ D * IP :=
    mul_le_mul_of_nonneg_right hstripScaled hIP
  change V⁻¹ * A ≤ D * IP + 2 * G ^ 2 * Iphi
  calc
    V⁻¹ * A ≤ V⁻¹ *
        (2 * (S * IP) + 2 * G ^ 2 * (V * Iphi)) := hscaled
    _ = (2 * V⁻¹ * S) * IP + 2 * G ^ 2 * Iphi := by
      field_simp
    _ ≤ D * IP + 2 * G ^ 2 * Iphi := add_le_add hstripMoment le_rfl

/-- The localized potential error has a genuine sample-space integral.  This
is the measurability field needed when the cutoff family is inserted into the
finite-volume Dirichlet variational problem. -/
theorem integrable_setIntegral_normSq_stationaryRepresentativeLocalGrad_sub_target
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Q : TriadicCube d) (L : ℕ)
    {phi : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ} {q p : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d}
    (hphim : StronglyMeasurable phi) (hphi : MemLp phi 2 M.P.toMeasure)
    (hqm : StronglyMeasurable q) (hq : MemLp q 2 M.P.toMeasure)
    (hpm : StronglyMeasurable p) (hp : MemLp p 2 M.P.toMeasure) :
    Integrable (fun omega => ∫ x in cubeSet Q,
      ‖HilbertVec.ofVec
          (stationaryRepresentativeLocalGrad Q L phi q omega x) -
        realize p omega x‖ ^ 2) M.P.toMeasure := by
  let Z : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d := fun omega => q omega - p omega
  let G : ℝ := stationaryPotentialCutoffGradBound Q L
  have hZm : StronglyMeasurable Z := hqm.sub hpm
  have hZ : MemLp Z 2 M.P.toMeasure := hq.sub hp
  have hQfin : volume (cubeSet Q) ≠ ⊤ := (volume_cubeSet_lt_top Q).ne
  have hmajor : Integrable (fun omega =>
      3 * (∫ x in cubeSet Q, ‖realize q omega x‖ ^ 2) +
      3 * G ^ 2 * (∫ x in cubeSet Q, ‖realize phi omega x‖ ^ 2) +
      3 * (∫ x in cubeSet Q, ‖realize Z omega x‖ ^ 2)) M.P.toMeasure :=
    (((integrable_setIntegral_normSq_realize M hQfin hqm hq).const_mul 3).add
      ((integrable_setIntegral_normSq_realize M hQfin hphim hphi).const_mul
        (3 * G ^ 2))).add
      ((integrable_setIntegral_normSq_realize M hQfin hZm hZ).const_mul 3)
  have hcut : Continuous (stationaryPotentialCutoff Q L).toFun :=
    (stationaryPotentialCutoff Q L).smooth.continuous
  have hcutGrad : Continuous (stationaryPotentialCutoffHilbertGrad Q L) := by
    apply (HilbertVec.continuousLinearEquivVec d).symm.continuous.comp
    apply continuous_pi
    intro i
    exact ((stationaryPotentialCutoff Q L).smooth.continuous_fderiv (by simp)).clm_apply
      continuous_const
  have hcoef : StronglyMeasurable (fun z : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d =>
      (stationaryPotentialCutoff Q L).toFun z.2 - 1) :=
    ((hcut.comp continuous_snd).stronglyMeasurable).sub stronglyMeasurable_const
  have hjoint : StronglyMeasurable (fun z : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d =>
      HilbertVec.ofVec
          (stationaryRepresentativeLocalGrad Q L phi q z.1 z.2) -
        realize p z.1 z.2) := by
    have hright : StronglyMeasurable (fun z : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d =>
        ((stationaryPotentialCutoff Q L).toFun z.2 - 1) • realize q z.1 z.2 +
          realize phi z.1 z.2 • stationaryPotentialCutoffHilbertGrad Q L z.2 +
          realize Z z.1 z.2) :=
      ((hcoef.smul (stronglyMeasurable_uncurry_realize hqm)).add
        ((stronglyMeasurable_uncurry_realize hphim).smul
          ((hcutGrad.comp continuous_snd).stronglyMeasurable))).add
        (stronglyMeasurable_uncurry_realize hZm)
    convert hright using 1
    funext z
    rw [show realize Z z.1 z.2 = realize q z.1 z.2 - realize p z.1 z.2 by rfl]
    rw [← ofVec_stationaryRepresentativeLocalGrad_sub_realize
      Q L phi q z.1 z.2]
    abel
  have htargetMeas : StronglyMeasurable (fun omega => ∫ x in cubeSet Q,
      ‖HilbertVec.ofVec
          (stationaryRepresentativeLocalGrad Q L phi q omega x) -
        realize p omega x‖ ^ 2) := by
    simpa only [Measure.restrict_apply_univ] using!
      (hjoint.norm.pow 2).integral_prod_right'
        (ν := volume.restrict (cubeSet Q))
  apply hmajor.mono' htargetMeas.aestronglyMeasurable
  filter_upwards [ae_memLp_two_realize M hQfin hqm hq,
    ae_memLp_two_realize M hQfin hphim hphi,
    ae_memLp_two_realize M hQfin hZm hZ] with omega hqomega hphiomega hZomega
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => by positivity)]
  have hinner : ∀ x : Vec d,
      ‖HilbertVec.ofVec
          (stationaryRepresentativeLocalGrad Q L phi q omega x) -
        realize p omega x‖ ^ 2 ≤
      3 * ‖realize q omega x‖ ^ 2 +
        3 * G ^ 2 * ‖realize phi omega x‖ ^ 2 +
        3 * ‖realize Z omega x‖ ^ 2 := by
    intro x
    have hcut0 := (stationaryPotentialCutoff Q L).nonneg x
    have hcut1 := (stationaryPotentialCutoff Q L).le_one x
    have hcoefLe : ‖(stationaryPotentialCutoff Q L).toFun x - 1‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      linarith
    have hgradLe := norm_stationaryPotentialCutoffHilbertGrad_le Q L x
    have hG0 : 0 ≤ G := stationaryPotentialCutoffGradBound_nonneg Q L
    have hdecomp := ofVec_stationaryRepresentativeLocalGrad_sub_realize
      Q L phi q omega x
    have htri : ‖HilbertVec.ofVec
          (stationaryRepresentativeLocalGrad Q L phi q omega x) -
        realize p omega x‖ ≤
        ‖realize q omega x‖ + G * ‖realize phi omega x‖ +
          ‖realize Z omega x‖ := by
      have heq : HilbertVec.ofVec
            (stationaryRepresentativeLocalGrad Q L phi q omega x) -
          realize p omega x =
          (((stationaryPotentialCutoff Q L).toFun x - 1) • realize q omega x +
            realize phi omega x • stationaryPotentialCutoffHilbertGrad Q L x) +
            realize Z omega x := by
        rw [show realize Z omega x = realize q omega x - realize p omega x by rfl,
          ← hdecomp]
        abel
      rw [heq]
      have hfirst :
          ‖((stationaryPotentialCutoff Q L).toFun x - 1) • realize q omega x‖ ≤
            ‖realize q omega x‖ := by
        rw [norm_smul]
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hcoefLe (norm_nonneg _)
      have hsecond :
          ‖realize phi omega x • stationaryPotentialCutoffHilbertGrad Q L x‖ ≤
            G * ‖realize phi omega x‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        calc
          |realize phi omega x| * ‖stationaryPotentialCutoffHilbertGrad Q L x‖ ≤
              |realize phi omega x| * G :=
            mul_le_mul_of_nonneg_left hgradLe (abs_nonneg _)
          _ = G * ‖realize phi omega x‖ := by
            rw [Real.norm_eq_abs]
            ring
      calc
        _ ≤ ‖((stationaryPotentialCutoff Q L).toFun x - 1) • realize q omega x‖ +
            ‖realize phi omega x • stationaryPotentialCutoffHilbertGrad Q L x‖ +
            ‖realize Z omega x‖ := by
          exact (norm_add_le _ _).trans
            (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ ‖realize q omega x‖ + G * ‖realize phi omega x‖ +
            ‖realize Z omega x‖ :=
          add_le_add (add_le_add hfirst hsecond) le_rfl
    let a : ℝ := ‖realize q omega x‖
    let b : ℝ := G * ‖realize phi omega x‖
    let c : ℝ := ‖realize Z omega x‖
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) htri 2
    have hthree : (a + b + c) ^ 2 ≤
        3 * a ^ 2 + 3 * b ^ 2 + 3 * c ^ 2 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
    calc
      _ ≤ (‖realize q omega x‖ + G * ‖realize phi omega x‖ +
          ‖realize Z omega x‖) ^ 2 := hsquare
      _ ≤ _ := by
        dsimp only [a, b, c] at hthree
        ring_nf at hthree ⊢
        exact hthree
  have hqint : Integrable (fun x => ‖realize q omega x‖ ^ 2)
      (volume.restrict (cubeSet Q)) :=
    (memLp_two_iff_integrable_sq_norm
      (stronglyMeasurable_realize hqm omega).aestronglyMeasurable).1 hqomega
  have hphiint : Integrable (fun x => ‖realize phi omega x‖ ^ 2)
      (volume.restrict (cubeSet Q)) :=
    (memLp_two_iff_integrable_sq_norm
      (stronglyMeasurable_realize hphim omega).aestronglyMeasurable).1 hphiomega
  have hZint : Integrable (fun x => ‖realize Z omega x‖ ^ 2)
      (volume.restrict (cubeSet Q)) :=
    (memLp_two_iff_integrable_sq_norm
      (stronglyMeasurable_realize hZm omega).aestronglyMeasurable).1 hZomega
  calc
    (∫ x in cubeSet Q, ‖HilbertVec.ofVec
        (stationaryRepresentativeLocalGrad Q L phi q omega x) -
      realize p omega x‖ ^ 2) ≤
      ∫ x in cubeSet Q,
        (3 * ‖realize q omega x‖ ^ 2 +
          3 * G ^ 2 * ‖realize phi omega x‖ ^ 2 +
          3 * ‖realize Z omega x‖ ^ 2) := by
      exact integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _ => by positivity)
        (((hqint.const_mul 3).add (hphiint.const_mul (3 * G ^ 2))).add
          (hZint.const_mul 3)) (Filter.Eventually.of_forall hinner)
    _ = _ := by
      let fq : Vec d → ℝ := fun x => 3 * ‖realize q omega x‖ ^ 2
      let fphi : Vec d → ℝ := fun x =>
        3 * G ^ 2 * ‖realize phi omega x‖ ^ 2
      let fZ : Vec d → ℝ := fun x => 3 * ‖realize Z omega x‖ ^ 2
      have hfq : Integrable fq (volume.restrict (cubeSet Q)) := hqint.const_mul 3
      have hfphi : Integrable fphi (volume.restrict (cubeSet Q)) :=
        hphiint.const_mul (3 * G ^ 2)
      have hfZ : Integrable fZ (volume.restrict (cubeSet Q)) := hZint.const_mul 3
      have hout := integral_add (hfq.add hfphi) hfZ
      have hin := integral_add hfq hfphi
      calc
        (∫ x in cubeSet Q,
            3 * ‖realize q omega x‖ ^ 2 +
              3 * G ^ 2 * ‖realize phi omega x‖ ^ 2 +
              3 * ‖realize Z omega x‖ ^ 2) =
            (∫ x in cubeSet Q, fq x + fphi x) +
              ∫ x in cubeSet Q, fZ x := by
          simpa only [fq, fphi, fZ, Pi.add_apply] using hout
        _ = ((∫ x in cubeSet Q, fq x) +
              ∫ x in cubeSet Q, fphi x) +
              ∫ x in cubeSet Q, fZ x := by rw [hin]
        _ = _ := by
          dsimp only [fq, fphi, fZ]
          rw [integral_const_mul, integral_const_mul, integral_const_mul]

theorem aux_dedup_d200_normSq_add_le_young {E : Type*} [NormedAddCommGroup E]
    {delta : ℝ} (hdelta : 0 < delta) (a b : E) :
    ‖a + b‖ ^ 2 ≤
      (1 + delta) * ‖a‖ ^ 2 + (1 + delta⁻¹) * ‖b‖ ^ 2 := by
  have htri : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have hinv : delta⁻¹ * delta = 1 := inv_mul_cancel₀ hdelta.ne'
  have hcross : 2 * (‖a‖ * ‖b‖) ≤
      delta * ‖a‖ ^ 2 + delta⁻¹ * ‖b‖ ^ 2 := by
    have hsq : 0 ≤ delta⁻¹ * (delta * ‖a‖ - ‖b‖) ^ 2 := by positivity
    have hrewrite : delta⁻¹ * (delta * ‖a‖ - ‖b‖) ^ 2 =
        delta * ‖a‖ ^ 2 + delta⁻¹ * ‖b‖ ^ 2 -
          2 * (‖a‖ * ‖b‖) := by
      field_simp
      ring
    linarith
  have hsq : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htri 2
  nlinarith

private theorem normSq_add_le_young {E : Type*} [NormedAddCommGroup E]
    {delta : ℝ} (hdelta : 0 < delta) (a b : E) :
    ‖a + b‖ ^ 2 ≤
      (1 + delta) * ‖a‖ ^ 2 + (1 + delta⁻¹) * ‖b‖ ^ 2 := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.aux_dedup_d200_normSq_add_le_young (E := E) (delta := delta) (hdelta := hdelta) (a := a) (b := b)

private theorem stationaryPotential_young_density_arith
    {M P s delta eta D A e : ℝ}
    (hM0 : 0 ≤ M) (hMD : M ≤ D) (hP0 : 0 ≤ P)
    (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hsbound : s * (D * (2 * P + 1) + 1) ≤ eta / 3)
    (hdeltabound : delta * (D * (P + 1) ^ 2 + 1) ≤ eta / 3)
    (hsdelta : s ≤ delta * eta / 6)
    (hA : A ≤ (P + s) ^ 2) (he : e ≤ s ^ 2) :
    (1 + delta) * (M * A) + (1 + delta⁻¹) * e ≤
      M * P ^ 2 + eta := by
  have hD0 : 0 ≤ D := hM0.trans hMD
  have hinv : delta⁻¹ * delta = 1 := inv_mul_cancel₀ hdelta0.ne'
  have hinvpos : 0 < delta⁻¹ := inv_pos.mpr hdelta0
  have hdeltaInvOne : (1 : ℝ) ≤ delta⁻¹ := by
    have hstep := mul_le_mul_of_nonneg_left hdelta1 hinvpos.le
    linarith
  have hssq : s ^ 2 ≤ s := by nlinarith
  have hmain : (1 + delta) * (M * A) ≤
      M * (P + s) ^ 2 + delta * (M * (P + s) ^ 2) := by
    have hMA := mul_le_mul_of_nonneg_left hA hM0
    nlinarith
  have hexpand : M * (P + s) ^ 2 ≤
      M * P ^ 2 + s * (D * (2 * P + 1)) := by
    have hsmall : 2 * P * s + s ^ 2 ≤ s * (2 * P + 1) := by
      nlinarith
    have hnonneg : 0 ≤ s * (2 * P + 1) := by positivity
    have hstep := mul_le_mul hMD hsmall (by nlinarith) hD0
    nlinarith
  have hdeltaTerm : delta * (M * (P + s) ^ 2) ≤
      delta * (D * (P + 1) ^ 2) := by
    have hps : (P + s) ^ 2 ≤ (P + 1) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul hMD hps (sq_nonneg _) hD0) hdelta0.le
  have herror : (1 + delta⁻¹) * e ≤ eta / 3 := by
    have hcoef : 1 + delta⁻¹ ≤ 2 * delta⁻¹ := by linarith
    have hstep : (1 + delta⁻¹) * e ≤ 2 * delta⁻¹ * s ^ 2 := by
      calc
        (1 + delta⁻¹) * e ≤ (1 + delta⁻¹) * s ^ 2 :=
          mul_le_mul_of_nonneg_left he (by positivity)
        _ ≤ 2 * delta⁻¹ * s ^ 2 := by
          exact mul_le_mul_of_nonneg_right hcoef (sq_nonneg s)
    have hs2 : s ^ 2 ≤ delta * eta / 6 := hssq.trans hsdelta
    calc
      (1 + delta⁻¹) * e ≤ 2 * delta⁻¹ * s ^ 2 := hstep
      _ ≤ 2 * delta⁻¹ * (delta * eta / 6) :=
        mul_le_mul_of_nonneg_left hs2 (by positivity)
      _ = eta / 3 := by
        field_simp
        ring
  have hsCost : s * (D * (2 * P + 1)) ≤ eta / 3 := by
    nlinarith [hsbound]
  have hdeltaCost : delta * (D * (P + 1) ^ 2) ≤ eta / 3 := by
    nlinarith [hdeltabound]
  nlinarith

/-- Young transfer from a smooth stationary representative to an arbitrary
stationary target.  This is the quantitative density interface needed to use
the cutoff competitors against the genuine stationary projection rather than
only against its mollification. -/
theorem normalized_integral_setIntegral_normSq_stationaryRepresentativeLocalGrad_sub_target_le
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Q : TriadicCube d) (L : ℕ) {delta : ℝ} (hdelta : 0 < delta)
    {phi : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ} {q p : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d}
    (hphim : StronglyMeasurable phi) (hphi : MemLp phi 2 M.P.toMeasure)
    (hqm : StronglyMeasurable q) (hq : MemLp q 2 M.P.toMeasure)
    (hpm : StronglyMeasurable p) (hp : MemLp p 2 M.P.toMeasure) :
    (cubeVolume Q)⁻¹ *
        (∫ omega, (∫ x in cubeSet Q,
          ‖HilbertVec.ofVec
              (stationaryRepresentativeLocalGrad Q L phi q omega x) -
            realize p omega x‖ ^ 2) ∂M.P.toMeasure) ≤
      (1 + delta) *
          ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) *
              (∫ omega, ‖q omega‖ ^ 2 ∂M.P.toMeasure) +
            2 * stationaryPotentialCutoffGradBound Q L ^ 2 *
              (∫ omega, ‖phi omega‖ ^ 2 ∂M.P.toMeasure)) +
        (1 + delta⁻¹) *
          (∫ omega, ‖q omega - p omega‖ ^ 2 ∂M.P.toMeasure) := by
  let V := cubeVolume Q
  let S := stationaryPotentialBoundaryStrip Q L
  let G := stationaryPotentialCutoffGradBound Q L
  let Z : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d := fun omega => q omega - p omega
  have hV : 0 < V := cubeVolume_pos Q
  have hSfin := volume_stationaryPotentialBoundaryStrip_ne_top Q L
  have hSmeas := measurableSet_stationaryPotentialBoundaryStrip Q L
  have hQfin : volume (cubeSet Q) ≠ ⊤ := (volume_cubeSet_lt_top Q).ne
  have hZm : StronglyMeasurable Z := hqm.sub hpm
  have hZ : MemLp Z 2 M.P.toMeasure := hq.sub hp
  have hqS := integrable_setIntegral_normSq_realize M hSfin hqm hq
  have hphiQ := integrable_setIntegral_normSq_realize M hQfin hphim hphi
  have hZQ := integrable_setIntegral_normSq_realize M hQfin hZm hZ
  have hdeltaOne : 0 ≤ 1 + delta := by linarith
  have hdeltaInvOne : 0 ≤ 1 + delta⁻¹ := by positivity
  have hupperInt : Integrable (fun omega =>
      (1 + delta) *
          (2 * (∫ x in S, ‖realize q omega x‖ ^ 2) +
            2 * G ^ 2 * (∫ x in cubeSet Q,
              ‖realize phi omega x‖ ^ 2)) +
        (1 + delta⁻¹) * (∫ x in cubeSet Q,
          ‖realize Z omega x‖ ^ 2)) M.P.toMeasure :=
    (((hqS.const_mul 2).add (hphiQ.const_mul (2 * G ^ 2))).const_mul
      (1 + delta)).add (hZQ.const_mul (1 + delta⁻¹))
  have houter :
      (∫ omega, (∫ x in cubeSet Q,
          ‖HilbertVec.ofVec
              (stationaryRepresentativeLocalGrad Q L phi q omega x) -
            realize p omega x‖ ^ 2) ∂M.P.toMeasure) ≤
        ∫ omega,
          ((1 + delta) *
              (2 * (∫ x in S, ‖realize q omega x‖ ^ 2) +
                2 * G ^ 2 * (∫ x in cubeSet Q,
                  ‖realize phi omega x‖ ^ 2)) +
            (1 + delta⁻¹) * (∫ x in cubeSet Q,
              ‖realize Z omega x‖ ^ 2)) ∂M.P.toMeasure := by
    refine integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun _ => integral_nonneg fun _ => by positivity)
      hupperInt ?_
    filter_upwards [ae_memLp_two_realize M hSfin hqm hq,
      ae_memLp_two_realize M hQfin hphim hphi,
      ae_memLp_two_realize M hQfin hZm hZ] with omega hqomega hphiomega hZomega
    have hqSInt : Integrable (fun x => ‖realize q omega x‖ ^ 2)
        (volume.restrict S) :=
      (memLp_two_iff_integrable_sq_norm
        (stronglyMeasurable_realize hqm omega).aestronglyMeasurable).1 hqomega
    have hphiQInt : Integrable (fun x => ‖realize phi omega x‖ ^ 2)
        (volume.restrict (cubeSet Q)) :=
      (memLp_two_iff_integrable_sq_norm
        (stronglyMeasurable_realize hphim omega).aestronglyMeasurable).1 hphiomega
    have hZQInt : Integrable (fun x => ‖realize Z omega x‖ ^ 2)
        (volume.restrict (cubeSet Q)) :=
      (memLp_two_iff_integrable_sq_norm
        (stronglyMeasurable_realize hZm omega).aestronglyMeasurable).1 hZomega
    let upper : Vec d → ℝ := fun x =>
      (1 + delta) *
          (2 * S.indicator (fun y => ‖realize q omega y‖ ^ 2) x +
            2 * G ^ 2 * ‖realize phi omega x‖ ^ 2) +
        (1 + delta⁻¹) * ‖realize Z omega x‖ ^ 2
    have hupperSpatial : Integrable upper (volume.restrict (cubeSet Q)) := by
      have hqInd : Integrable
          (S.indicator fun y => ‖realize q omega y‖ ^ 2) volume :=
        MeasureTheory.IntegrableOn.integrable_indicator hqSInt hSmeas
      have hqIndQ : Integrable
          (S.indicator fun y => ‖realize q omega y‖ ^ 2)
          (volume.restrict (cubeSet Q)) := hqInd.mono_measure Measure.restrict_le_self
      exact (((hqIndQ.const_mul 2).add
        (hphiQInt.const_mul (2 * G ^ 2))).const_mul (1 + delta)).add
          (hZQInt.const_mul (1 + delta⁻¹))
    have hinner :
        (∫ x in cubeSet Q,
          ‖HilbertVec.ofVec
              (stationaryRepresentativeLocalGrad Q L phi q omega x) -
            realize p omega x‖ ^ 2) ≤ ∫ x in cubeSet Q, upper x := by
      refine integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _ => by positivity) hupperSpatial ?_
      refine (ae_restrict_iff' (measurableSet_cubeSet Q)).2 ?_
      filter_upwards with x hx
      let a := HilbertVec.ofVec
          (stationaryRepresentativeLocalGrad Q L phi q omega x) -
        realize q omega x
      let b := realize Z omega x
      have hsplit : HilbertVec.ofVec
            (stationaryRepresentativeLocalGrad Q L phi q omega x) -
          realize p omega x = a + b := by
        simp only [a, b, Z, realize_apply]
        abel
      have hlocal := norm_sq_stationaryRepresentativeLocalGrad_sub_le
        Q L phi q omega hx
      have hyoung := normSq_add_le_young hdelta a b
      rw [hsplit]
      exact hyoung.trans (add_le_add
        (mul_le_mul_of_nonneg_left hlocal hdeltaOne) le_rfl)
    refine hinner.trans (le_of_eq ?_)
    dsimp only [upper]
    have hqIndQ : Integrable
        (S.indicator fun y => ‖realize q omega y‖ ^ 2)
        (volume.restrict (cubeSet Q)) :=
      (MeasureTheory.IntegrableOn.integrable_indicator hqSInt hSmeas)
        |>.mono_measure Measure.restrict_le_self
    have hbaseInt := (hqIndQ.const_mul 2).add
      (hphiQInt.const_mul (2 * G ^ 2))
    have hleftInt := hbaseInt.const_mul (1 + delta)
    have hrightInt := hZQInt.const_mul (1 + delta⁻¹)
    calc
      _ = (1 + delta) * (∫ x in cubeSet Q,
              (2 * S.indicator (fun y => ‖realize q omega y‖ ^ 2) x +
                2 * G ^ 2 * ‖realize phi omega x‖ ^ 2)) +
            (1 + delta⁻¹) * (∫ x in cubeSet Q,
              ‖realize Z omega x‖ ^ 2) := by
        have hadd := integral_add hleftInt hrightInt
        rw [integral_const_mul, integral_const_mul] at hadd
        simpa only [Pi.add_apply] using hadd
      _ = (1 + delta) *
              (2 * (∫ x in cubeSet Q,
                  S.indicator (fun y => ‖realize q omega y‖ ^ 2) x) +
                2 * G ^ 2 * (∫ x in cubeSet Q,
                  ‖realize phi omega x‖ ^ 2)) +
            (1 + delta⁻¹) * (∫ x in cubeSet Q,
              ‖realize Z omega x‖ ^ 2) := by
        rw [integral_add (hqIndQ.const_mul 2)
          (hphiQInt.const_mul (2 * G ^ 2)),
          integral_const_mul, integral_const_mul]
      _ = _ := by
        rw [setIntegral_indicator hSmeas,
          Set.inter_eq_self_of_subset_right
            (stationaryPotentialBoundaryStrip_subset_cubeSet Q L)]
  have houterEval :
      ∫ omega,
          ((1 + delta) *
              (2 * (∫ x in S, ‖realize q omega x‖ ^ 2) +
                2 * G ^ 2 * (∫ x in cubeSet Q,
                  ‖realize phi omega x‖ ^ 2)) +
            (1 + delta⁻¹) * (∫ x in cubeSet Q,
              ‖realize Z omega x‖ ^ 2)) ∂M.P.toMeasure =
        (1 + delta) *
            (2 * (volume S).toReal *
                (∫ omega, ‖q omega‖ ^ 2 ∂M.P.toMeasure) +
              2 * G ^ 2 * V *
                (∫ omega, ‖phi omega‖ ^ 2 ∂M.P.toMeasure)) +
          (1 + delta⁻¹) * V *
            (∫ omega, ‖Z omega‖ ^ 2 ∂M.P.toMeasure) := by
    have hbaseInt := (hqS.const_mul 2).add
      (hphiQ.const_mul (2 * G ^ 2))
    have hleftInt := hbaseInt.const_mul (1 + delta)
    have hrightInt := hZQ.const_mul (1 + delta⁻¹)
    calc
      _ = (1 + delta) *
              (∫ omega,
                (2 * (∫ x in S, ‖realize q omega x‖ ^ 2) +
                  2 * G ^ 2 * (∫ x in cubeSet Q,
                    ‖realize phi omega x‖ ^ 2)) ∂M.P.toMeasure) +
            (1 + delta⁻¹) *
              (∫ omega, (∫ x in cubeSet Q,
                ‖realize Z omega x‖ ^ 2) ∂M.P.toMeasure) := by
        have hadd := integral_add hleftInt hrightInt
        rw [integral_const_mul, integral_const_mul] at hadd
        simpa only [Pi.add_apply] using hadd
      _ = (1 + delta) *
              (2 * (∫ omega, (∫ x in S,
                    ‖realize q omega x‖ ^ 2) ∂M.P.toMeasure) +
                2 * G ^ 2 * (∫ omega, (∫ x in cubeSet Q,
                    ‖realize phi omega x‖ ^ 2) ∂M.P.toMeasure)) +
            (1 + delta⁻¹) *
              (∫ omega, (∫ x in cubeSet Q,
                ‖realize Z omega x‖ ^ 2) ∂M.P.toMeasure) := by
        rw [integral_add (hqS.const_mul 2)
          (hphiQ.const_mul (2 * G ^ 2)),
          integral_const_mul, integral_const_mul]
      _ = _ := by
        rw [integral_setIntegral_normSq_realize M hSfin hqm hq,
          integral_setIntegral_normSq_realize M hQfin hphim hphi,
          integral_setIntegral_normSq_realize M hQfin hZm hZ,
          volume_cubeSet_toReal]
        dsimp only [S, V]
        ring
  have hscaled := mul_le_mul_of_nonneg_left houter (inv_nonneg.mpr hV.le)
  rw [houterEval] at hscaled
  have hqMoment : 0 ≤ ∫ omega, ‖q omega‖ ^ 2 ∂M.P.toMeasure :=
    integral_nonneg fun _ => by positivity
  have hstrip := volume_stationaryPotentialBoundaryStrip_toReal_le Q L
  have hstripScaled : 2 * V⁻¹ * (volume S).toReal ≤
      (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) := by
    have hmul : 2 * V⁻¹ *
          (volume (stationaryPotentialBoundaryStrip Q L)).toReal ≤
        2 * V⁻¹ *
          ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) / 2 * cubeVolume Q) :=
      mul_le_mul_of_nonneg_left hstrip
        (mul_nonneg (by norm_num) (inv_nonneg.mpr hV.le))
    dsimp only [S, V] at hmul ⊢
    calc
      2 * (cubeVolume Q)⁻¹ *
          (volume (stationaryPotentialBoundaryStrip Q L)).toReal ≤
        2 * (cubeVolume Q)⁻¹ *
          ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) / 2 * cubeVolume Q) := hmul
      _ = (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) := by
        field_simp [ne_of_gt (cubeVolume_pos Q)]
  have hstripMoment := mul_le_mul_of_nonneg_right hstripScaled hqMoment
  change V⁻¹ * _ ≤ _
  calc
    V⁻¹ * _ ≤ V⁻¹ *
        ((1 + delta) *
            (2 * (volume S).toReal *
                (∫ omega, ‖q omega‖ ^ 2 ∂M.P.toMeasure) +
              2 * G ^ 2 * V *
                (∫ omega, ‖phi omega‖ ^ 2 ∂M.P.toMeasure)) +
          (1 + delta⁻¹) * V *
            (∫ omega, ‖Z omega‖ ^ 2 ∂M.P.toMeasure)) := hscaled
    _ = (1 + delta) *
          ((2 * V⁻¹ * (volume S).toReal) *
              (∫ omega, ‖q omega‖ ^ 2 ∂M.P.toMeasure) +
            2 * G ^ 2 *
              (∫ omega, ‖phi omega‖ ^ 2 ∂M.P.toMeasure)) +
        (1 + delta⁻¹) *
          (∫ omega, ‖Z omega‖ ^ 2 ∂M.P.toMeasure) := by field_simp
    _ ≤ (1 + delta) *
          ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) *
              (∫ omega, ‖q omega‖ ^ 2 ∂M.P.toMeasure) +
            2 * G ^ 2 *
              (∫ omega, ‖phi omega‖ ^ 2 ∂M.P.toMeasure)) +
        (1 + delta⁻¹) *
          (∫ omega, ‖Z omega‖ ^ 2 ∂M.P.toMeasure) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (add_le_add hstripMoment le_rfl)
          hdeltaOne) le_rfl
    _ = _ := rfl

/-- At fixed strip depth and fixed stationary mollification, the only
large-cube contribution in the target-transfer bound is the primitive cutoff
term, and it vanishes as the origin cube expands. -/
theorem tendsto_stationaryPotentialCutoffTargetBound_originCube
    (d L : ℕ) (delta Iq Iphi Idiff : ℝ) :
    Filter.Tendsto
      (fun K : ℕ =>
        (1 + delta) *
            ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * Iq +
              2 * stationaryPotentialCutoffGradBound
                  (originCube d (K : ℤ)) L ^ 2 * Iphi) +
          (1 + delta⁻¹) * Idiff)
      Filter.atTop
      (nhds ((1 + delta) *
          ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * Iq) +
        (1 + delta⁻¹) * Idiff)) := by
  have hprimitive :=
    tendsto_stationaryPotentialCutoffPrimitivePrice_originCube d L Iphi
  have hsum : Filter.Tendsto
      (fun K : ℕ =>
        (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * Iq +
          2 * stationaryPotentialCutoffGradBound
              (originCube d (K : ℤ)) L ^ 2 * Iphi)
      Filter.atTop
      (nhds ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * Iq + 0)) :=
    tendsto_const_nhds.add hprimitive
  have hscaled := hsum.const_mul (1 + delta)
  have htotal := hscaled.add
    (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ℕ => (1 + delta⁻¹) * Idiff) Filter.atTop
      (nhds ((1 + delta⁻¹) * Idiff)))
  simpa only [add_zero] using htotal

/-- The quantitatively controlled mollified representative produces an
honest zero-trace competitor almost surely. -/
theorem ae_isPotentialZeroTraceOn_mollifiedRepresentativeLocalGrad
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa)
    {phi : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ} (hphim : StronglyMeasurable phi)
    (hphi : MemLp phi 2 M.P.toMeasure)
    (Q : TriadicCube d) (L : ℕ) :
    ∀ᵐ omega ∂M.P.toMeasure,
      IsPotentialZeroTraceOn (openCubeSet Q)
        (stationaryRepresentativeLocalGrad Q L
          (representativeMollify kappa phi)
          (representativeMollifyGrad kappa phi) omega) := by
  filter_upwards [ae_smooth_primitive_representativeMollify
    M hcompact hkappa hphim hphi] with omega homega
  exact isPotentialZeroTraceOn_stationaryRepresentativeLocalGrad Q L
    homega.1 homega.2

/-- Complete potential-side localization package: every closed stationary
potential field has a quantitatively nearby smooth stationary representative,
and every canonical cube cutoff of that representative is an admissible
zero-trace competitor almost surely. -/
theorem exists_mollifiedRepresentativeGradient_zeroTrace_norm_sub_lt
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {F : Stationary.VectorL2 d M.P.toMeasure}
    (hF : letI := potentialSequenceVAddInvariant M
      F ∈ Stationary.stationaryPotentialSubspace
        (mu := M.P.toMeasure) (d := d))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ rho : Stationary.L2Mollifier d,
      ∃ phi : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ,
        ∃ hphim : StronglyMeasurable phi,
          ∃ hphi : MemLp phi 2 M.P.toMeasure,
            ‖(memLp_two_representativeMollifyGrad M rho.compactSupport
                rho.smooth hphim hphi).toLp
                  (representativeMollifyGrad rho.toFun phi) - F‖ < epsilon ∧
            ∀ (Q : TriadicCube d) (L : ℕ),
              ∀ᵐ omega ∂M.P.toMeasure,
                IsPotentialZeroTraceOn (openCubeSet Q)
                  (stationaryRepresentativeLocalGrad Q L
                    (representativeMollify rho.toFun phi)
                    (representativeMollifyGrad rho.toFun phi) omega) := by
  obtain ⟨rho, phi, hphim, hphi, hclose⟩ :=
    exists_mollifiedRepresentativeGradient_norm_sub_lt M hF hepsilon
  exact ⟨rho, phi, hphim, hphi, hclose, fun Q L =>
    ae_isPotentialZeroTraceOn_mollifiedRepresentativeLocalGrad
      M rho.compactSupport rho.smooth hphim hphi Q L⟩

/-- Potential half of the stationary local-approximation theorem.  Every
stationary potential `L²` field admits zero-trace competitors on all expanding
origin cubes whose expected normalized error is the boundary-strip price,
up to an arbitrary tolerance and a nonnegative term tending to zero. -/
theorem exists_stationaryPotentialZeroTrace_family_bound
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (L : ℕ) {eta : ℝ} (heta : 0 < eta)
    {F : Stationary.VectorL2 d M.P.toMeasure}
    (hF : letI := potentialSequenceVAddInvariant M
      F ∈ Stationary.stationaryPotentialSubspace
        (mu := M.P.toMeasure) (d := d)) :
    ∃ (V : ℕ → _root_.SubdiffusiveProcess.Model.PotentialSample d → Vec d → Vec d) (g : ℕ → ℝ),
      (∀ K, 0 ≤ g K) ∧
      Filter.Tendsto g Filter.atTop (nhds 0) ∧
      (∀ K : ℕ, ∀ᵐ omega ∂M.P.toMeasure,
        IsPotentialZeroTraceOn
          (openCubeSet (originCube d (K : ℤ))) (V K omega)) ∧
      (∀ K : ℕ, Integrable (fun omega =>
        ∫ x in cubeSet (originCube d (K : ℤ)),
          ‖HilbertVec.ofVec (V K omega x) -
            realize (stationaryVectorRepresentative M F) omega x‖ ^ 2)
        M.P.toMeasure) ∧
      ∀ K : ℕ,
        (cubeVolume (originCube d (K : ℤ)))⁻¹ *
            (∫ omega, (∫ x in cubeSet (originCube d (K : ℤ)),
              ‖HilbertVec.ofVec (V K omega x) -
                realize (stationaryVectorRepresentative M F) omega x‖ ^ 2)
              ∂M.P.toMeasure) ≤
          (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * ‖F‖ ^ 2 + eta + g K := by
  let P : ℝ := ‖F‖
  have hP0 : 0 ≤ P := norm_nonneg _
  have hXdelta : 0 < 3 * ((d : ℝ) * (P + 1) ^ 2 + 1) := by positivity
  have hXs : 0 < 3 * ((d : ℝ) * (2 * P + 1) + 1) := by positivity
  let delta : ℝ := min 1 (eta / (3 * ((d : ℝ) * (P + 1) ^ 2 + 1)))
  have hdelta0 : 0 < delta := lt_min one_pos (by positivity)
  have hdelta1 : delta ≤ 1 := min_le_left _ _
  have hdeltabound :
      delta * ((d : ℝ) * (P + 1) ^ 2 + 1) ≤ eta / 3 := by
    have hle : delta ≤ eta / (3 * ((d : ℝ) * (P + 1) ^ 2 + 1)) :=
      min_le_right _ _
    have hne : (d : ℝ) * (P + 1) ^ 2 + 1 ≠ 0 := by positivity
    calc
      delta * ((d : ℝ) * (P + 1) ^ 2 + 1) ≤
          (eta / (3 * ((d : ℝ) * (P + 1) ^ 2 + 1))) *
            ((d : ℝ) * (P + 1) ^ 2 + 1) :=
        mul_le_mul_of_nonneg_right hle (by positivity)
      _ = eta / 3 := by field_simp
  let s : ℝ := min 1
    (min (eta / (3 * ((d : ℝ) * (2 * P + 1) + 1)))
      (delta * eta / 6))
  have hs0 : 0 < s := lt_min one_pos (lt_min (by positivity) (by positivity))
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsbound :
      s * ((d : ℝ) * (2 * P + 1) + 1) ≤ eta / 3 := by
    have hle : s ≤ eta / (3 * ((d : ℝ) * (2 * P + 1) + 1)) :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hne : (d : ℝ) * (2 * P + 1) + 1 ≠ 0 := by positivity
    calc
      s * ((d : ℝ) * (2 * P + 1) + 1) ≤
          (eta / (3 * ((d : ℝ) * (2 * P + 1) + 1))) *
            ((d : ℝ) * (2 * P + 1) + 1) :=
        mul_le_mul_of_nonneg_right hle (by positivity)
      _ = eta / 3 := by field_simp
  have hsdelta : s ≤ delta * eta / 6 :=
    (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨rho, phi, hphim, hphi, hclose, hzeroTrace⟩ :=
    exists_mollifiedRepresentativeGradient_zeroTrace_norm_sub_lt
      M hF hs0
  let psi : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := representativeMollify rho.toFun phi
  let q : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d := representativeMollifyGrad rho.toFun phi
  let p : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d := stationaryVectorRepresentative M F
  let hpsim : StronglyMeasurable psi :=
    stronglyMeasurable_representativeMollify rho.continuous hphim
  let hpsi : MemLp psi 2 M.P.toMeasure :=
    memLp_two_representativeMollify M rho.continuous rho.integrable hphim hphi
  let hqm : StronglyMeasurable q :=
    stronglyMeasurable_representativeMollifyGrad rho.smooth hphim
  let hq : MemLp q 2 M.P.toMeasure :=
    memLp_two_representativeMollifyGrad M rho.compactSupport rho.smooth hphim hphi
  let hpm : StronglyMeasurable p := stronglyMeasurable_stationaryVectorRepresentative M F
  let hp : MemLp p 2 M.P.toMeasure := memLp_two_stationaryVectorRepresentative M F
  have hpClass : hp.toLp p = F := toLp_stationaryVectorRepresentative M F
  have hqClose : ‖hq.toLp q - F‖ < s := by
    simpa only [q, hq] using hclose
  let A : ℝ := ∫ omega, ‖q omega‖ ^ 2 ∂M.P.toMeasure
  let e : ℝ := ∫ omega, ‖q omega - p omega‖ ^ 2 ∂M.P.toMeasure
  have heEq : e = ‖hq.toLp q - F‖ ^ 2 := by
    dsimp only [e]
    rw [integral_normSq_sub_eq_norm_sq_toLp hq hp, hpClass]
  have he : e ≤ s ^ 2 := by
    rw [heEq]
    have hq0 : 0 ≤ ‖hq.toLp q - F‖ := norm_nonneg _
    nlinarith
  have hqNorm : ‖hq.toLp q‖ ≤ P + s := by
    calc
      ‖hq.toLp q‖ = ‖(hq.toLp q - F) + F‖ := by congr 1; abel
      _ ≤ ‖hq.toLp q - F‖ + ‖F‖ := norm_add_le _ _
      _ ≤ P + s := by dsimp only [P]; linarith
  have hA : A ≤ (P + s) ^ 2 := by
    rw [show A = ‖hq.toLp q‖ ^ 2 by
      exact integral_normSq_eq_norm_sq_toLp hq]
    exact pow_le_pow_left₀ (norm_nonneg _) hqNorm 2
  let Ipsi : ℝ := ∫ omega, ‖psi omega‖ ^ 2 ∂M.P.toMeasure
  let V : ℕ → _root_.SubdiffusiveProcess.Model.PotentialSample d → Vec d → Vec d := fun K omega =>
    stationaryRepresentativeLocalGrad (originCube d (K : ℤ)) L
      psi q omega
  let g : ℕ → ℝ := fun K =>
    (1 + delta) *
      (2 * stationaryPotentialCutoffGradBound
          (originCube d (K : ℤ)) L ^ 2 * Ipsi)
  refine ⟨V, g, ?_, ?_, ?_, ?_, ?_⟩
  · intro K
    dsimp only [g, Ipsi]
    positivity
  · have hbase :=
      tendsto_stationaryPotentialCutoffPrimitivePrice_originCube d L Ipsi
    simpa only [g, mul_zero] using hbase.const_mul (1 + delta)
  · intro K
    simpa only [V, psi, q] using
      hzeroTrace (originCube d (K : ℤ)) L
  · intro K
    simpa only [V, psi, q, p] using
      integrable_setIntegral_normSq_stationaryRepresentativeLocalGrad_sub_target
        M (originCube d (K : ℤ)) L hpsim hpsi hqm hq hpm hp
  · intro K
    have hkey :=
      normalized_integral_setIntegral_normSq_stationaryRepresentativeLocalGrad_sub_target_le
        M (originCube d (K : ℤ)) L hdelta0 hpsim hpsi hqm hq hpm hp
    have hscale0 : 0 ≤ (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) := by positivity
    have hscaleD : (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) ≤ (d : ℝ) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (three_zpow_neg_le_one L) (Nat.cast_nonneg d)
    have harith := stationaryPotential_young_density_arith
      (M := (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)))
      (P := P) (s := s) (delta := delta) (eta := eta) (D := (d : ℝ))
      (A := A) (e := e) hscale0 hscaleD hP0 hs0 hs1 hdelta0 hdelta1
      hsbound hdeltabound hsdelta hA he
    change _ ≤ (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * ‖F‖ ^ 2 + eta + g K
    calc
      _ ≤ (1 + delta) *
            ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * A +
              2 * stationaryPotentialCutoffGradBound
                  (originCube d (K : ℤ)) L ^ 2 * Ipsi) +
          (1 + delta⁻¹) * e := by
        simpa only [V, psi, q, p, A, e, Ipsi] using hkey
      _ = ((1 + delta) *
              ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * A) +
            (1 + delta⁻¹) * e) + g K := by
        dsimp only [g]
        ring
      _ ≤ ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * P ^ 2 + eta) + g K :=
        by
          linarith only [harith]
      _ = _ := by rfl

/-- The preceding thermodynamic potential approximation specialized to the
projected suffix forcing in the one-step argument. -/
theorem exists_oneStepPotentialProjection_zeroTrace_family_bound
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (p : Vec d) (hh : 0 < h)
    (L : ℕ) {eta : ℝ} (heta : 0 < eta) :
    ∃ (V : ℕ → _root_.SubdiffusiveProcess.Model.PotentialSample d → Vec d → Vec d) (g : ℕ → ℝ),
      (∀ K, 0 ≤ g K) ∧
      Filter.Tendsto g Filter.atTop (nhds 0) ∧
      (∀ K : ℕ, ∀ᵐ omega ∂M.P.toMeasure,
        IsPotentialZeroTraceOn
          (openCubeSet (originCube d (K : ℤ))) (V K omega)) ∧
      (∀ K : ℕ, Integrable (fun omega =>
        ∫ x in cubeSet (originCube d (K : ℤ)),
          ‖HilbertVec.ofVec (V K omega x) -
            realize (stationaryVectorRepresentative M
              (oneStepPotentialProjection M n h p hh)) omega x‖ ^ 2)
        M.P.toMeasure) ∧
      ∀ K : ℕ,
        (cubeVolume (originCube d (K : ℤ)))⁻¹ *
            (∫ omega, (∫ x in cubeSet (originCube d (K : ℤ)),
              ‖HilbertVec.ofVec (V K omega x) -
                realize (stationaryVectorRepresentative M
                  (oneStepPotentialProjection M n h p hh)) omega x‖ ^ 2)
              ∂M.P.toMeasure) ≤
          (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) *
              ‖oneStepPotentialProjection M n h p hh‖ ^ 2 + eta + g K := by
  exact exists_stationaryPotentialZeroTrace_family_bound M L heta
    (oneStepPotentialProjection_mem_stationaryPotentialSubspace M n h p hh)

/-- The projected one-step forcing admits, after stationary mollification, a
genuine zero-trace competitor on every fixed triadic cube.  This is the
samplewise membership endpoint of the Dirichlet exhaustion. -/
theorem ae_exists_zeroTrace_cutoff_oneStepPotentialProjection
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (p : Vec d) (hh : 0 < h)
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa)
    (Q : TriadicCube d) (L : ℕ) :
    ∀ᵐ omega ∂M.P.toMeasure,
      ∃ phi : Vec d → ℝ,
        (∀ (x : Vec d) (i : Fin d),
          fderiv ℝ phi x (basisVec i) =
            stationaryMollifiedRealization M kappa
              (oneStepPotentialProjection M n h p hh) omega x i) ∧
        IsPotentialZeroTraceOn (openCubeSet Q)
          (stationaryPotentialLocalGrad Q L phi) := by
  filter_upwards [ae_exists_contDiff_primitive_oneStepPotentialProjection
    M n h p hh hcompact hkappa] with omega homega
  obtain ⟨phi, hphismooth, hphi⟩ := homega
  exact ⟨phi, hphi,
    isPotentialZeroTraceOn_stationaryPotentialLocalGrad Q L hphismooth⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
