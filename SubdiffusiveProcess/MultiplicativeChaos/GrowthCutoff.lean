module

public import SubdiffusiveProcess.MultiplicativeChaos.TriadicGrid
public import SubdiffusiveProcess.MultiplicativeChaos.CubeSupMoment
public import SubdiffusiveProcess.MultiplicativeChaos.GrowthSeries
public import SubdiffusiveProcess.MultiplicativeChaos.ChaosPositiveMoments

@[expose] public section

/-!
# Uniform growth of the cutoff measures

`eq:mfd-39` of Proposition `mfd:prop-chaos-growth` (`eq:mfd-39` and `mfd:prop-chaos-growth`): one
random constant, in `L^p` of the sample law, bounding `mu_N(B(x,r))` by
`Kmu * r ^ (d - epsilon)` for EVERY cutoff `N`, every centre in a bounded
region and every radius `r <= 1`.

The route is the paper's.  The cube masses are nonnegative martingales with
`p`-th moments bounded uniformly in the cutoff
(`chaos_positive_moments_and_martingales`); `lintegral_iSup_pow_le_of_martingale`
turns that into a bound on the supremum over the cutoff; the triadic grid of
`TriadicGrid` converts an arbitrary ball into one grid cube; and the resulting
series over the layers is geometric with ratio `3 ^ (-theta)`,
`theta = p epsilon - d - Cexponent delta ^ 2`, which is positive exactly when
the disorder is below the threshold `delta0` produced here.

Two points of the formalization are worth recording.  The layer sum is taken
over generations `j + 2`, because the moment bound applies only to cubes of
side at most one and a generation-`j` cube has side `4 * 3 ^ (-j)`; the radii
above `3 ^ (-2)` that this leaves out are handled separately, by covering the
unit ball with the finitely many generation-two cubes and absorbing their
number into a deterministic constant.  And the supremum over the cutoff is
taken of the `p`-th powers rather than of the masses, which avoids commuting
`(sup .) ^ p` with the supremum.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped CompactlySupported ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess

/-- The layer weight of the growth bound: `3 ^ ((j + 3) (d - epsilon))`, the
reciprocal of the radius scale of the generation-`(j+2)` layer. -/
def growthWeight (d : ℕ) (epsilon : ℝ) (j : ℕ) : ℝ :=
  (3 : ℝ) ^ (((j : ℝ) + 3) * ((d : ℝ) - epsilon))

theorem growthWeight_pos (d : ℕ) (epsilon : ℝ) (j : ℕ) :
    0 < growthWeight d epsilon j :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- The random series controlling the growth of the cutoff measures on a
bounded region: over the triadic layers `j` (generation `j + 2`, so that the
cube side `4 * 3 ^ (-(j+2))` is at most one) and over the finitely many grid
indices meeting the region. -/
def growthSum {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (epsilon rho : ℝ) (p : ℕ) (omega : BilateralField d) : ℝ≥0∞ :=
  ∑' j : ℕ, ∑ k ∈ gridIndices d (rho + 2) (j + 2),
    ENNReal.ofReal (growthWeight d epsilon j ^ p) *
      ⨆ N : ℕ, ENNReal.ofReal
        (((weightedChaosCutoff M H N omega) (gridCube (j + 2) k)).toReal ^ p)

/-- The random constant of the growth bound. -/
def growthConstant {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (epsilon rho : ℝ) (p : ℕ) (omega : BilateralField d) : ℝ :=
  (growthSum M H epsilon rho p omega).toReal ^ ((p : ℝ)⁻¹)

/-- The exponent of the triadic series: positive exactly when the disorder is
small enough, which is what `delta0` encodes. -/
def growthTheta (d : ℕ) (epsilon : ℝ) (p : ℕ) (Cexponent delta : ℝ) : ℝ :=
  (p : ℝ) * epsilon - (d : ℝ) - Cexponent * delta ^ 2

/-- **Uniform growth of the cutoff measures** (`eq:mfd-39`, `eq:mfd-39`). -/
theorem chaos_growth_cutoff
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (epsilon : ℝ) (hepsilon : epsilon ∈ Set.Ioo 0 1)
    (p : ℕ) (hp : (d : ℝ) < p * epsilon) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        ∀ (R : Set (SpatialCoordinates d)), Bornology.IsBounded R →
          ∃ Kmu : BilateralField d → ℝ,
            MemLp Kmu p (chaosSampleLaw M).toMeasure ∧
            ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              0 ≤ Kmu omega ∧
              ∀ N x, x ∈ R → ∀ r, 0 < r → r ≤ 1 →
                weightedChaosCutoff M H N omega (Metric.ball x r) ≤
                  ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - epsilon)) := by
  classical
  obtain ⟨hep0, hep1⟩ := hepsilon
  -- `p` is at least three: `p epsilon > d ≥ 2` and `epsilon < 1`.
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hppos : (0 : ℝ) < (p : ℝ) := by nlinarith
  have hp2 : 2 ≤ p := by
    by_contra hcon
    push Not at hcon
    have hple : (p : ℝ) ≤ 1 := by
      have : p ≤ 1 := Nat.lt_succ_iff.mp hcon
      exact_mod_cast this
    nlinarith [hp, hdR, hep0, hep1, hple]
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp2
  obtain ⟨Cexponent, cSmall, hCe, hcS, hA⟩ :=
    chaos_positive_moments_and_martingales hd p hp1
  refine ⟨min cSmall (Real.sqrt (((p : ℝ) * epsilon - d) / (2 * Cexponent))), ?_, ?_⟩
  · refine lt_min hcS ?_
    refine Real.sqrt_pos.mpr ?_
    have : (0 : ℝ) < (p : ℝ) * epsilon - d := by linarith
    positivity
  · intro M H hH hdelta R hR
    have hdelta0 : 0 < M.delta := M.shellPrefix.delta_pos
    have hdeltacS : M.delta ≤ cSmall := le_trans hdelta (min_le_left _ _)
    -- the disorder is small enough to make the triadic exponent positive
    have hdeltasq : Cexponent * M.delta ^ 2 ≤ ((p : ℝ) * epsilon - d) / 2 := by
      have hle : M.delta ≤ Real.sqrt (((p : ℝ) * epsilon - d) / (2 * Cexponent)) :=
        le_trans hdelta (min_le_right _ _)
      have hnn : (0 : ℝ) ≤ ((p : ℝ) * epsilon - d) / (2 * Cexponent) := by
        have h1 : (0 : ℝ) < (p : ℝ) * epsilon - d := by linarith
        positivity
      have hsq : M.delta ^ 2 ≤ ((p : ℝ) * epsilon - d) / (2 * Cexponent) := by
        have := Real.sq_sqrt hnn
        nlinarith [hle, hdelta0.le, Real.sqrt_nonneg
          (((p : ℝ) * epsilon - d) / (2 * Cexponent))]
      have := mul_le_mul_of_nonneg_left hsq hCe.le
      calc Cexponent * M.delta ^ 2
          ≤ Cexponent * (((p : ℝ) * epsilon - d) / (2 * Cexponent)) := this
        _ = ((p : ℝ) * epsilon - d) / 2 := by field_simp
    have htheta : 0 < growthTheta d epsilon p Cexponent M.delta := by
      rw [growthTheta]
      linarith
    -- the region, enlarged so that every grid cube used lies inside it
    obtain ⟨rho0, hrho0⟩ := hR.subset_closedBall (0 : SpatialCoordinates d)
    set rho : ℝ := max rho0 1 with hrhodef
    have hrho1 : (1 : ℝ) ≤ rho := le_max_right _ _
    have hrhonn : (0 : ℝ) ≤ rho := by linarith
    have hRsub : R ⊆ Metric.closedBall (0 : SpatialCoordinates d) rho :=
      hrho0.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
    set Rbig : Set (SpatialCoordinates d) :=
      Metric.ball (0 : SpatialCoordinates d) (rho + 6) with hRbigdef
    have hRbig : Bornology.IsBounded Rbig := Metric.isBounded_ball
    obtain ⟨Cmass, hCm, hA'⟩ := hA Rbig hRbig
    obtain ⟨hmom, hlf1, hlf2, hmart1, hmart2⟩ := hA' M H hH hdeltacS
    -- the side of a generation-`(j+2)` cube
    set sside : ℕ → ℝ := fun j => 4 * (3 : ℝ) ^ (-((j + 2 : ℕ) : ℤ)) with hsside
    have hsspos : ∀ j, 0 < sside j := by
      intro j
      have h := zpow_neg_pos (j + 2)
      rw [hsside]
      linarith
    have hsszle : ∀ j : ℕ, (3 : ℝ) ^ (-((j + 2 : ℕ) : ℤ)) ≤ 1 :=
      fun j => three_zpow_neg_le_one (j + 2)
    have hssle1 : ∀ j, sside j ≤ 1 := by
      intro j
      have h2 : (3 : ℝ) ^ (-((j + 2 : ℕ) : ℤ)) ≤ (3 : ℝ) ^ (-((2 : ℕ) : ℤ)) :=
        three_zpow_neg_le_of_le (by omega)
      have h3 : (3 : ℝ) ^ (-((2 : ℕ) : ℤ)) = 1 / 9 := by norm_num
      rw [hsside]
      rw [h3] at h2
      linarith
    -- the cubes sit inside the enlarged region
    have hcubesub : ∀ (j : ℕ) (k : Fin d → ℤ),
        k ∈ gridIndices d (rho + 2) (j + 2) → gridCube (j + 2) k ⊆ Rbig := by
      intro j k hk
      have hgp := dist_gridPoint_le_of_mem (by linarith : (0 : ℝ) ≤ rho + 2) hk
      rw [gridCube_eq]
      intro y hy
      have h1 : dist y (gridPoint (j + 2) k) < 2 * (3 : ℝ) ^ (-((j + 2 : ℕ) : ℤ)) :=
        Metric.mem_ball.mp hy
      have h2 := hsszle j
      have h3 : dist y (0 : SpatialCoordinates d)
          ≤ dist y (gridPoint (j + 2) k)
            + dist (gridPoint (j + 2) k) (0 : SpatialCoordinates d) :=
        dist_triangle _ _ _
      rw [hRbigdef]
      refine Metric.mem_ball.mpr ?_
      linarith
    -- Doob on each cube
    have hcube : ∀ (j : ℕ) (k : Fin d → ℤ),
        k ∈ gridIndices d (rho + 2) (j + 2) →
        ∫⁻ omega, ⨆ N : ℕ, ENNReal.ofReal
            (((weightedChaosCutoff M H N omega) (gridCube (j + 2) k)).toReal ^ p)
            ∂(chaosSampleLaw M).toMeasure
          ≤ ENNReal.ofReal ((2 : ℝ) ^ p * ((p : ℝ) / ((p : ℝ) - 1))) *
            ENNReal.ofReal (Cmass * sside j ^
              ((d : ℝ) * p - Cexponent * M.delta ^ 2)) := by
      intro j k hk
      have hsub := hcubesub j k hk
      have hm := fun N => hmom N (gridPoint (j + 2) k) (sside j) (hsspos j)
        (hssle1 j) hsub
      have hmt := hmart2 (gridPoint (j + 2) k) (sside j) (hsspos j)
      have hgc : gridCube (j + 2) k
          = ((centeredCube (gridPoint (j + 2) k) (sside j) (hsspos j)) :
              Set (SpatialCoordinates d)) := rfl
      rw [hgc]
      exact lintegral_iSup_pow_le_of_martingale hmt.1 (fun N omega => hmt.2 N omega)
        p hp2 _ (fun N => (hm N).2.1) (fun N => (hm N).2.2)
    -- measurability of each layer term
    have hGmble : ∀ (j : ℕ) (k : Fin d → ℤ),
        k ∈ gridIndices d (rho + 2) (j + 2) →
        Measurable (fun omega => ⨆ N : ℕ, ENNReal.ofReal
          (((weightedChaosCutoff M H N omega) (gridCube (j + 2) k)).toReal ^ p)) := by
      intro j k hk
      refine Measurable.iSup ?_
      intro N
      have hm := hmom N (gridPoint (j + 2) k) (sside j) (hsspos j) (hssle1 j)
        (hcubesub j k hk)
      exact (hm.1).ennreal_ofReal
    -- the integral of the series is the series of the integrals
    have hWeq : ∫⁻ omega, growthSum M H epsilon rho p omega
          ∂(chaosSampleLaw M).toMeasure
        = ∑' j : ℕ, ∑ k ∈ gridIndices d (rho + 2) (j + 2),
            ENNReal.ofReal (growthWeight d epsilon j ^ p) *
              ∫⁻ omega, (⨆ N : ℕ, ENNReal.ofReal
                (((weightedChaosCutoff M H N omega)
                  (gridCube (j + 2) k)).toReal ^ p))
                ∂(chaosSampleLaw M).toMeasure := by
      simp only [growthSum]
      rw [lintegral_tsum]
      · refine tsum_congr fun j => ?_
        rw [lintegral_finsetSum]
        · refine Finset.sum_congr rfl fun k hk => ?_
          exact lintegral_const_mul _ (hGmble j k hk)
        · intro k hk
          exact (measurable_const.mul (hGmble j k hk))
      · intro j
        have hfun : (fun omega => ∑ k ∈ gridIndices d (rho + 2) (j + 2),
              ENNReal.ofReal (growthWeight d epsilon j ^ p) *
                ⨆ N : ℕ, ENNReal.ofReal
                  (((weightedChaosCutoff M H N omega)
                    (gridCube (j + 2) k)).toReal ^ p))
            = ∑ k ∈ gridIndices d (rho + 2) (j + 2),
              (fun omega => ENNReal.ofReal (growthWeight d epsilon j ^ p) *
                ⨆ N : ℕ, ENNReal.ofReal
                  (((weightedChaosCutoff M H N omega)
                    (gridCube (j + 2) k)).toReal ^ p)) := by
          funext omega
          simp [Finset.sum_apply]
        rw [hfun]
        exact Finset.aemeasurable_sum _
          (fun k hk => (measurable_const.mul (hGmble j k hk)).aemeasurable)
    -- the arithmetic of the layers
    set aexp : ℝ := (d : ℝ) * p - Cexponent * M.delta ^ 2 with haexp
    set theta : ℝ := growthTheta d epsilon p Cexponent M.delta with hth
    have hkey : (d : ℝ) + ((d : ℝ) - epsilon) * (p : ℝ) - aexp = -theta := by
      rw [haexp, hth, growthTheta]; ring
    set Cp : ℝ := (2 : ℝ) ^ p * ((p : ℝ) / ((p : ℝ) - 1)) with hCp
    have hppos1 : (1 : ℝ) < (p : ℝ) := by
      have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
      linarith
    have hCppos : 0 < Cp := by
      rw [hCp]
      have : (0 : ℝ) < (p : ℝ) / ((p : ℝ) - 1) := by
        apply div_pos hppos
        linarith
      positivity
    have harith : ∀ j : ℕ,
        ((gridIndices d (rho + 2) (j + 2)).card : ℝ) *
            (growthWeight d epsilon j ^ p * (Cp * (Cmass * sside j ^ aexp)))
          ≤ ((2 * (rho + 2) + 3) * 9) ^ d * Cp * Cmass * (4 : ℝ) ^ aexp *
              (3 : ℝ) ^ ((3 : ℝ) * (((d : ℝ) - epsilon) * (p : ℝ))) *
              (3 : ℝ) ^ ((-2 : ℝ) * aexp) *
            (3 : ℝ) ^ (-(j : ℝ) * theta) := by
      intro j
      have h3 : (0 : ℝ) < 3 := by norm_num
      have h3' : (0 : ℝ) ≤ 3 := by norm_num
      set B0 : ℝ := 2 * (rho + 2) + 3 with hB0def
      have hB0 : 0 ≤ B0 := by rw [hB0def]; linarith
      set A : ℝ := ((d : ℝ) - epsilon) * (p : ℝ) with hAdef
      have hc1 : ((gridIndices d (rho + 2) (j + 2)).card : ℝ)
          ≤ (B0 * 9) ^ d * (3 : ℝ) ^ ((j : ℝ) * (d : ℝ)) := by
        refine le_trans (card_gridIndices_le (by linarith) (j + 2)) (le_of_eq ?_)
        have hz : (3 : ℝ) ^ (((j + 2 : ℕ)) : ℤ) = 9 * (3 : ℝ) ^ ((j : ℝ)) := by
          rw [zpow_natCast, pow_add, ← Real.rpow_natCast (3 : ℝ) j]
          norm_num
          ring
        rw [hz, ← mul_assoc, mul_pow, ← Real.rpow_natCast ((3 : ℝ) ^ ((j : ℝ))) d,
          ← Real.rpow_mul h3']
      have hw : growthWeight d epsilon j ^ p
          = (3 : ℝ) ^ ((3 : ℝ) * A) * (3 : ℝ) ^ ((j : ℝ) * A) := by
        rw [growthWeight, ← Real.rpow_natCast _ p, ← Real.rpow_mul h3',
          ← Real.rpow_add h3, hAdef]
        congr 1
        ring
      have hs : sside j ^ aexp
          = (4 : ℝ) ^ aexp *
            ((3 : ℝ) ^ ((-2 : ℝ) * aexp) * (3 : ℝ) ^ (-(j : ℝ) * aexp)) := by
        rw [hsside]
        rw [Real.mul_rpow (by norm_num) (le_of_lt (zpow_neg_pos (j + 2)))]
        congr 1
        rw [← Real.rpow_intCast (3 : ℝ) (-((j + 2 : ℕ) : ℤ)), ← Real.rpow_mul h3',
          ← Real.rpow_add h3]
        congr 1
        push_cast
        ring
      have hmerge : (3 : ℝ) ^ ((j : ℝ) * (d : ℝ)) * (3 : ℝ) ^ ((j : ℝ) * A) *
            (3 : ℝ) ^ (-(j : ℝ) * aexp)
          = (3 : ℝ) ^ (-(j : ℝ) * theta) := by
        rw [← Real.rpow_add h3, ← Real.rpow_add h3]
        congr 1
        have hk : (d : ℝ) + A - aexp = -theta := by rw [hAdef]; exact hkey
        linear_combination (j : ℝ) * hk
      have hrest : 0 ≤ growthWeight d epsilon j ^ p *
          (Cp * (Cmass * sside j ^ aexp)) := by
        have h1 : 0 < growthWeight d epsilon j := growthWeight_pos d epsilon j
        have h2 : 0 < sside j := hsspos j
        have h3s : (0 : ℝ) < sside j ^ aexp := Real.rpow_pos_of_pos h2 _
        have h4 : 0 ≤ Cmass := hCm.le
        positivity
      calc ((gridIndices d (rho + 2) (j + 2)).card : ℝ) *
            (growthWeight d epsilon j ^ p * (Cp * (Cmass * sside j ^ aexp)))
          ≤ ((B0 * 9) ^ d * (3 : ℝ) ^ ((j : ℝ) * (d : ℝ))) *
            (growthWeight d epsilon j ^ p * (Cp * (Cmass * sside j ^ aexp))) := by
            exact mul_le_mul_of_nonneg_right hc1 hrest
        _ = (B0 * 9) ^ d * Cp * Cmass * (4 : ℝ) ^ aexp *
              (3 : ℝ) ^ ((3 : ℝ) * A) * (3 : ℝ) ^ ((-2 : ℝ) * aexp) *
              (3 : ℝ) ^ (-(j : ℝ) * theta) := by
            rw [hw, hs, ← hmerge]
            ring
    set Cbig : ℝ := ((2 * (rho + 2) + 3) * 9) ^ d * Cp * Cmass * (4 : ℝ) ^ aexp *
        (3 : ℝ) ^ ((3 : ℝ) * (((d : ℝ) - epsilon) * (p : ℝ))) *
        (3 : ℝ) ^ ((-2 : ℝ) * aexp) with hCbig
    have hCbignn : 0 ≤ Cbig := by
      rw [hCbig]
      have h1 : (0 : ℝ) ≤ 2 * (rho + 2) + 3 := by linarith
      have h2 : (0 : ℝ) < (4 : ℝ) ^ aexp := Real.rpow_pos_of_pos (by norm_num) _
      have h3 : (0 : ℝ) < (3 : ℝ) ^ ((3 : ℝ) * (((d : ℝ) - epsilon) * (p : ℝ))) :=
        Real.rpow_pos_of_pos (by norm_num) _
      have h4 : (0 : ℝ) < (3 : ℝ) ^ ((-2 : ℝ) * aexp) :=
        Real.rpow_pos_of_pos (by norm_num) _
      have h5 : (0 : ℝ) ≤ Cmass := hCm.le
      positivity
    -- (A) the series is finite
    have hWlt : ∫⁻ omega, growthSum M H epsilon rho p omega
        ∂(chaosSampleLaw M).toMeasure < ⊤ := by
      rw [hWeq]
      refine lt_of_le_of_lt ?_ (tsum_ofReal_three_rpow_lt_top htheta hCbignn)
      refine ENNReal.tsum_le_tsum fun j => ?_
      have hstep1 : ∑ k ∈ gridIndices d (rho + 2) (j + 2),
            ENNReal.ofReal (growthWeight d epsilon j ^ p) *
              ∫⁻ omega, (⨆ N : ℕ, ENNReal.ofReal
                (((weightedChaosCutoff M H N omega)
                  (gridCube (j + 2) k)).toReal ^ p))
                ∂(chaosSampleLaw M).toMeasure
          ≤ ∑ _k ∈ gridIndices d (rho + 2) (j + 2),
              ENNReal.ofReal (growthWeight d epsilon j ^ p) *
                (ENNReal.ofReal Cp * ENNReal.ofReal (Cmass * sside j ^ aexp)) := by
        refine Finset.sum_le_sum fun k hk => ?_
        exact mul_le_mul_right (hcube j k hk) _
      refine le_trans hstep1 ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      have hwnn : 0 ≤ growthWeight d epsilon j ^ p :=
        pow_nonneg (growthWeight_pos d epsilon j).le p
      have hsnn : 0 ≤ Cmass * sside j ^ aexp := by
        have := Real.rpow_pos_of_pos (hsspos j) aexp
        have h5 : (0 : ℝ) ≤ Cmass := hCm.le
        positivity
      have hprod : ENNReal.ofReal (growthWeight d epsilon j ^ p) *
            (ENNReal.ofReal Cp * ENNReal.ofReal (Cmass * sside j ^ aexp))
          = ENNReal.ofReal (growthWeight d epsilon j ^ p *
              (Cp * (Cmass * sside j ^ aexp))) := by
        rw [ENNReal.ofReal_mul hwnn, ENNReal.ofReal_mul hCppos.le]
      rw [hprod]
      have hcardcast : ((gridIndices d (rho + 2) (j + 2)).card : ℝ≥0∞)
          = ENNReal.ofReal (((gridIndices d (rho + 2) (j + 2)).card : ℝ)) := by
        simp
      rw [hcardcast, ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (harith j)
    -- measurability of the series
    have hWmble : Measurable (fun omega => growthSum M H epsilon rho p omega) := by
      simp only [growthSum]
      refine Measurable.tsum ?_
      intro j
      exact Finset.measurable_sum _
        (fun k hk => measurable_const.mul (hGmble j k hk))
    -- (B) the constant is nonnegative, measurable and in `L^p`
    have hKnn : ∀ omega, 0 ≤ growthConstant M H epsilon rho p omega := by
      intro omega
      rw [growthConstant]
      positivity
    have hKmble : Measurable (growthConstant M H epsilon rho p) := by
      show Measurable (fun omega =>
        (growthSum M H epsilon rho p omega).toReal ^ ((p : ℝ)⁻¹))
      exact (hWmble.ennreal_toReal).pow measurable_const
    have hWne : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        growthSum M H epsilon rho p omega ≠ ⊤ :=
      ae_lt_top hWmble hWlt.ne |>.mono fun omega h => h.ne
    have hpow : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ‖growthConstant M H epsilon rho p omega‖ₑ ^ ((p : ℕ) : ℝ)
          = growthSum M H epsilon rho p omega := by
      filter_upwards [hWne] with omega hne
      have hnn := hKnn omega
      have hpne : ((p : ℝ)) ≠ 0 := by positivity
      rw [Real.enorm_eq_ofReal hnn]
      show (ENNReal.ofReal
          ((growthSum M H epsilon rho p omega).toReal ^ ((p : ℝ)⁻¹))) ^ ((p : ℕ) : ℝ)
        = growthSum M H epsilon rho p omega
      rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by positivity),
        ← ENNReal.rpow_mul, inv_mul_cancel₀ hpne, ENNReal.rpow_one,
        ENNReal.ofReal_toReal hne]
    have hMemLp : MemLp (growthConstant M H epsilon rho p) p
        (chaosSampleLaw M).toMeasure := by
      have hpz : ((p : ℕ) : ℝ≥0∞) ≠ 0 := by
        simp only [ne_eq, Nat.cast_eq_zero]
        omega
      have hpt : ((p : ℕ) : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top p
      rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hpz hpt hKmble.aestronglyMeasurable]
      have htoReal : ((p : ℕ) : ℝ≥0∞).toReal = ((p : ℕ) : ℝ) := by simp
      rw [htoReal]
      have hcongr : ∫⁻ omega, ‖growthConstant M H epsilon rho p omega‖ₑ ^ ((p : ℕ) : ℝ)
            ∂(chaosSampleLaw M).toMeasure
          = ∫⁻ omega, growthSum M H epsilon rho p omega
            ∂(chaosSampleLaw M).toMeasure :=
        lintegral_congr_ae hpow
      rw [hcongr]
      exact hWlt
    -- (C) the pointwise bound on each grid cube
    have hcubebd : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ (j N : ℕ) (k : Fin d → ℤ), k ∈ gridIndices d (rho + 2) (j + 2) →
          ((weightedChaosCutoff M H N omega) (gridCube (j + 2) k)).toReal *
              growthWeight d epsilon j
            ≤ growthConstant M H epsilon rho p omega := by
      filter_upwards [hWne] with omega hne
      intro j N k hk
      set x : ℝ := ((weightedChaosCutoff M H N omega)
        (gridCube (j + 2) k)).toReal with hxdef
      have hx0 : 0 ≤ x := ENNReal.toReal_nonneg
      have hw0 : 0 < growthWeight d epsilon j := growthWeight_pos d epsilon j
      have hterm : ENNReal.ofReal ((growthWeight d epsilon j * x) ^ p)
          ≤ growthSum M H epsilon rho p omega := by
        have h1 : ENNReal.ofReal (growthWeight d epsilon j ^ p) *
              ENNReal.ofReal (x ^ p)
            ≤ ENNReal.ofReal (growthWeight d epsilon j ^ p) *
              ⨆ N' : ℕ, ENNReal.ofReal
                (((weightedChaosCutoff M H N' omega)
                  (gridCube (j + 2) k)).toReal ^ p) :=
          mul_le_mul_right (le_iSup (fun N' : ℕ => ENNReal.ofReal
            (((weightedChaosCutoff M H N' omega)
              (gridCube (j + 2) k)).toReal ^ p)) N) _
        have h2 : ENNReal.ofReal (growthWeight d epsilon j ^ p) *
              (⨆ N' : ℕ, ENNReal.ofReal
                (((weightedChaosCutoff M H N' omega)
                  (gridCube (j + 2) k)).toReal ^ p))
            ≤ ∑ k' ∈ gridIndices d (rho + 2) (j + 2),
              ENNReal.ofReal (growthWeight d epsilon j ^ p) *
                ⨆ N' : ℕ, ENNReal.ofReal
                  (((weightedChaosCutoff M H N' omega)
                    (gridCube (j + 2) k')).toReal ^ p) :=
          Finset.single_le_sum (f := fun k' => ENNReal.ofReal
            (growthWeight d epsilon j ^ p) * ⨆ N' : ℕ, ENNReal.ofReal
              (((weightedChaosCutoff M H N' omega)
                (gridCube (j + 2) k')).toReal ^ p))
            (fun i _ => bot_le) hk
        have h3 : (∑ k' ∈ gridIndices d (rho + 2) (j + 2),
              ENNReal.ofReal (growthWeight d epsilon j ^ p) *
                ⨆ N' : ℕ, ENNReal.ofReal
                  (((weightedChaosCutoff M H N' omega)
                    (gridCube (j + 2) k')).toReal ^ p))
            ≤ growthSum M H epsilon rho p omega := by
          rw [growthSum]
          exact ENNReal.le_tsum (f := fun j' : ℕ =>
            ∑ k' ∈ gridIndices d (rho + 2) (j' + 2),
              ENNReal.ofReal (growthWeight d epsilon j' ^ p) *
                ⨆ N' : ℕ, ENNReal.ofReal
                  (((weightedChaosCutoff M H N' omega)
                    (gridCube (j' + 2) k')).toReal ^ p)) j
        have hmulsplit : ENNReal.ofReal ((growthWeight d epsilon j * x) ^ p)
            = ENNReal.ofReal (growthWeight d epsilon j ^ p) *
              ENNReal.ofReal (x ^ p) := by
          rw [mul_pow, ENNReal.ofReal_mul (by positivity)]
        rw [hmulsplit]
        exact le_trans h1 (le_trans h2 h3)
      have hle : (growthWeight d epsilon j * x) ^ p
          ≤ (growthSum M H epsilon rho p omega).toReal :=
        (ENNReal.ofReal_le_iff_le_toReal hne).mp hterm
      have hpne : (p : ℕ) ≠ 0 := by omega
      calc x * growthWeight d epsilon j
          = growthWeight d epsilon j * x := by ring
        _ = ((growthWeight d epsilon j * x) ^ p) ^ ((p : ℝ)⁻¹) :=
            (Real.pow_rpow_inv_natCast (by positivity) hpne).symm
        _ ≤ ((growthSum M H epsilon rho p omega).toReal) ^ ((p : ℝ)⁻¹) := by
            refine Real.rpow_le_rpow (by positivity) hle (by positivity)
        _ = growthConstant M H epsilon rho p omega := rfl
    -- the deterministic constant absorbing the large-radius regime
    set C0 : ℝ := max 1 (((gridIndices d (rho + 2) 2).card : ℝ) *
      (3 : ℝ) ^ (-((d : ℝ) - epsilon))) with hC0
    have hC0pos : 0 < C0 := lt_of_lt_of_le one_pos (le_max_left _ _)
    have hC01 : (1 : ℝ) ≤ C0 := le_max_left _ _
    have hdeps : 0 < (d : ℝ) - epsilon := by linarith
    refine ⟨fun omega => C0 * growthConstant M H epsilon rho p omega, ?_, ?_⟩
    · exact hMemLp.const_mul C0
    · filter_upwards [hcubebd] with omega hb
      refine ⟨mul_nonneg hC0pos.le (hKnn omega), ?_⟩
      intro N x hx r hr hr1
      have hxdist : dist x (0 : SpatialCoordinates d) ≤ rho :=
        Metric.mem_closedBall.mp (hRsub hx)
      have hKnn0 : 0 ≤ growthConstant M H epsilon rho p omega := hKnn omega
      by_cases hsmall : r ≤ (3 : ℝ) ^ (-(2 : ℤ))
      · -- the generic regime: one grid cube contains the ball
        obtain ⟨J, hJ1, hJ2⟩ := exists_triadic_scale hr hr1
        have hJ2' : 2 ≤ J := by
          by_contra hcon
          push Not at hcon
          have h1 : (3 : ℝ) ^ (-(2 : ℤ)) ≤ (3 : ℝ) ^ (-((J : ℤ) + 1)) := by
            have : ((J : ℤ) + 1) ≤ 2 := by omega
            have h2 : (3 : ℝ) ^ (-(2 : ℤ)) ≤ (3 : ℝ) ^ (-((J : ℤ) + 1)) := by
              rw [zpow_neg, zpow_neg]
              refine inv_anti₀ (by positivity) ?_
              exact zpow_le_zpow_right₀ (by norm_num) this
            exact h2
          linarith
        obtain ⟨j, hj⟩ : ∃ j : ℕ, J = j + 2 := ⟨J - 2, by omega⟩
        subst hj
        have hrj : r ≤ (3 : ℝ) ^ (-((j + 2 : ℕ) : ℤ)) := by
          have : ((j + 2 : ℕ) : ℤ) = ((j : ℤ) + 2) := by push_cast; ring
          rw [this]
          have h2 : ((j : ℤ) + 2) = (((j + 2 : ℕ)) : ℤ) := by push_cast; ring
          simpa using hJ2
        obtain ⟨k, hk, hsub⟩ := exists_grid_cube (rho := rho + 1) (j + 2)
          (by linarith : dist x (0 : SpatialCoordinates d) ≤ rho + 1) hr hrj
        have hkbox : k ∈ gridIndices d (rho + 2) (j + 2) := by
          have : rho + 1 + 1 = rho + 2 := by ring
          rwa [this] at hk
        have := hlf2 N omega
        have hfin : (weightedChaosCutoff M H N omega) (gridCube (j + 2) k) ≠ ⊤ := by
          rw [gridCube_eq]
          exact (measure_ball_lt_top).ne
        have hmono := measure_mono (μ := weightedChaosCutoff M H N omega) hsub
        refine le_trans hmono ?_
        have hpt := hb j N k hkbox
        have hwpos : 0 < growthWeight d epsilon j := growthWeight_pos d epsilon j
        have htoreal : ((weightedChaosCutoff M H N omega)
            (gridCube (j + 2) k)).toReal
              ≤ growthConstant M H epsilon rho p omega / growthWeight d epsilon j := by
          rw [le_div_iff₀ hwpos]
          exact hpt
        have hweight : growthConstant M H epsilon rho p omega /
              growthWeight d epsilon j
            ≤ C0 * growthConstant M H epsilon rho p omega * r ^ ((d : ℝ) - epsilon) := by
          have hrge : (3 : ℝ) ^ (-((j : ℝ) + 3)) ≤ r := by
            have hz : (3 : ℝ) ^ (-((j : ℤ) + 3)) < r := by
              have : ((j : ℤ) + 2 + 1) = ((j : ℤ) + 3) := by ring
              rw [← this]
              simpa using hJ1
            have hcast : (3 : ℝ) ^ (-((j : ℝ) + 3))
                = (3 : ℝ) ^ (-((j : ℤ) + 3)) := by
              rw [← Real.rpow_intCast (3 : ℝ) (-((j : ℤ) + 3))]
              congr 1
              push_cast
              ring
            rw [hcast]
            exact hz.le
          have hrpow : (growthWeight d epsilon j)⁻¹ ≤ r ^ ((d : ℝ) - epsilon) := by
            rw [growthWeight, ← Real.rpow_neg (by norm_num)]
            have hexp : -(((j : ℝ) + 3) * ((d : ℝ) - epsilon))
                = (-((j : ℝ) + 3)) * ((d : ℝ) - epsilon) := by ring
            rw [hexp, Real.rpow_mul (by norm_num)]
            exact Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hrge hdeps.le
          have hdiv : growthConstant M H epsilon rho p omega /
                growthWeight d epsilon j
              = growthConstant M H epsilon rho p omega * (growthWeight d epsilon j)⁻¹ := by
            ring
          rw [hdiv]
          calc growthConstant M H epsilon rho p omega * (growthWeight d epsilon j)⁻¹
              ≤ growthConstant M H epsilon rho p omega * r ^ ((d : ℝ) - epsilon) := by
                exact mul_le_mul_of_nonneg_left hrpow hKnn0
            _ ≤ C0 * growthConstant M H epsilon rho p omega *
                r ^ ((d : ℝ) - epsilon) := by
                have hrp : 0 ≤ r ^ ((d : ℝ) - epsilon) := Real.rpow_nonneg hr.le _
                have hKr : 0 ≤ growthConstant M H epsilon rho p omega *
                    r ^ ((d : ℝ) - epsilon) := mul_nonneg hKnn0 hrp
                calc growthConstant M H epsilon rho p omega * r ^ ((d : ℝ) - epsilon)
                    = 1 * (growthConstant M H epsilon rho p omega *
                        r ^ ((d : ℝ) - epsilon)) := (one_mul _).symm
                  _ ≤ C0 * (growthConstant M H epsilon rho p omega *
                        r ^ ((d : ℝ) - epsilon)) :=
                      mul_le_mul_of_nonneg_right hC01 hKr
                  _ = C0 * growthConstant M H epsilon rho p omega *
                        r ^ ((d : ℝ) - epsilon) := (mul_assoc _ _ _).symm
        have hfinal : ((weightedChaosCutoff M H N omega)
            (gridCube (j + 2) k)).toReal
              ≤ C0 * growthConstant M H epsilon rho p omega *
                r ^ ((d : ℝ) - epsilon) := le_trans htoreal hweight
        calc (weightedChaosCutoff M H N omega) (gridCube (j + 2) k)
            = ENNReal.ofReal (((weightedChaosCutoff M H N omega)
                (gridCube (j + 2) k)).toReal) := (ENNReal.ofReal_toReal hfin).symm
          _ ≤ ENNReal.ofReal (C0 * growthConstant M H epsilon rho p omega *
              r ^ ((d : ℝ) - epsilon)) := ENNReal.ofReal_le_ofReal hfinal
      · -- the large-radius regime: cover by generation-two cubes
        push Not at hsmall
        have hz2 : (0 : ℝ) < (3 : ℝ) ^ (-((2 : ℕ) : ℤ)) := zpow_neg_pos 2
        have hz2le : (3 : ℝ) ^ (-((2 : ℕ) : ℤ)) ≤ 1 := three_zpow_neg_le_one 2
        have hcover : Metric.ball x r ⊆
            ⋃ k ∈ gridIndices d (rho + 2) 2, gridCube 2 k := by
          intro y hy
          obtain ⟨k, hk⟩ := exists_gridPoint_close 2 y
          have hyk : y ∈ gridCube 2 k := by
            rw [gridCube_eq]
            refine Metric.mem_ball.mpr ?_
            calc dist y (gridPoint 2 k) ≤ (3 : ℝ) ^ (-((2 : ℕ) : ℤ)) := hk
              _ < 2 * (3 : ℝ) ^ (-((2 : ℕ) : ℤ)) := by linarith
          have hkbox : k ∈ gridIndices d (rho + 2) 2 := by
            refine mem_gridIndices ?_
            have h1 : dist (gridPoint 2 k) (0 : SpatialCoordinates d)
                ≤ dist (gridPoint 2 k) y + dist y (0 : SpatialCoordinates d) :=
              dist_triangle _ _ _
            have h2 : dist (gridPoint 2 k) y = dist y (gridPoint 2 k) := dist_comm _ _
            have h3 : dist y (0 : SpatialCoordinates d)
                ≤ dist y x + dist x (0 : SpatialCoordinates d) := dist_triangle _ _ _
            have h4 : dist y x < r := Metric.mem_ball.mp hy
            rw [h2] at h1
            linarith
          exact Set.mem_biUnion hkbox hyk
        have hsumle := measure_biUnion_finset_le
          (μ := weightedChaosCutoff M H N omega) (gridIndices d (rho + 2) 2)
          (fun k => gridCube 2 k)
        have hw0 : 0 < growthWeight d epsilon 0 := growthWeight_pos d epsilon 0
        have hbound : ∀ k ∈ gridIndices d (rho + 2) 2,
            (weightedChaosCutoff M H N omega) (gridCube 2 k)
              ≤ ENNReal.ofReal (growthConstant M H epsilon rho p omega /
                  growthWeight d epsilon 0) := by
          intro k hk
          have := hlf2 N omega
          have hfin : (weightedChaosCutoff M H N omega) (gridCube 2 k) ≠ ⊤ := by
            rw [gridCube_eq]
            exact (measure_ball_lt_top).ne
          have hpt := hb 0 N k hk
          rw [← ENNReal.ofReal_toReal hfin]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [le_div_iff₀ hw0]
          exact hpt
        -- the deterministic comparison of the two scales
        have hrpow2 : (3 : ℝ) ^ ((-2 : ℝ) * ((d : ℝ) - epsilon))
            ≤ r ^ ((d : ℝ) - epsilon) := by
          have hcast : (3 : ℝ) ^ (-((2 : ℕ) : ℤ)) = (3 : ℝ) ^ ((-2 : ℝ)) := by
            rw [← Real.rpow_intCast (3 : ℝ) (-((2 : ℕ) : ℤ))]
            congr 1
            push_cast
            ring
          rw [Real.rpow_mul (by norm_num), ← hcast]
          exact Real.rpow_le_rpow hz2.le hsmall.le hdeps.le
        have harith2 : ((gridIndices d (rho + 2) 2).card : ℝ) *
              (growthConstant M H epsilon rho p omega / growthWeight d epsilon 0)
            ≤ C0 * growthConstant M H epsilon rho p omega *
              r ^ ((d : ℝ) - epsilon) := by
          have hw0eq : growthWeight d epsilon 0
              = (3 : ℝ) ^ ((3 : ℝ) * ((d : ℝ) - epsilon)) := by
            rw [growthWeight]
            congr 1
            push_cast
            ring
          have hdiv : growthConstant M H epsilon rho p omega /
                growthWeight d epsilon 0
              = growthConstant M H epsilon rho p omega *
                (3 : ℝ) ^ ((-3 : ℝ) * ((d : ℝ) - epsilon)) := by
            rw [hw0eq, div_eq_mul_inv, ← Real.rpow_neg (by norm_num)]
            congr 2
            ring
          have hsplit : (3 : ℝ) ^ ((-3 : ℝ) * ((d : ℝ) - epsilon))
              = (3 : ℝ) ^ (-((d : ℝ) - epsilon)) *
                (3 : ℝ) ^ ((-2 : ℝ) * ((d : ℝ) - epsilon)) := by
            rw [← Real.rpow_add (by norm_num)]
            congr 1
            ring
          rw [hdiv, hsplit]
          have hc2nn : (0 : ℝ) ≤ ((gridIndices d (rho + 2) 2).card : ℝ) :=
            Nat.cast_nonneg _
          have hA1 : (0 : ℝ) ≤ (3 : ℝ) ^ (-((d : ℝ) - epsilon)) :=
            Real.rpow_nonneg (by norm_num) _
          have hstep1 : ((gridIndices d (rho + 2) 2).card : ℝ) *
                (growthConstant M H epsilon rho p omega *
                  ((3 : ℝ) ^ (-((d : ℝ) - epsilon)) *
                    (3 : ℝ) ^ ((-2 : ℝ) * ((d : ℝ) - epsilon))))
              ≤ ((gridIndices d (rho + 2) 2).card : ℝ) *
                (growthConstant M H epsilon rho p omega *
                  ((3 : ℝ) ^ (-((d : ℝ) - epsilon)) * r ^ ((d : ℝ) - epsilon))) := by
            have hin : (3 : ℝ) ^ (-((d : ℝ) - epsilon)) *
                  (3 : ℝ) ^ ((-2 : ℝ) * ((d : ℝ) - epsilon))
                ≤ (3 : ℝ) ^ (-((d : ℝ) - epsilon)) * r ^ ((d : ℝ) - epsilon) :=
              mul_le_mul_of_nonneg_left hrpow2 hA1
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hin hKnn0) hc2nn
          refine le_trans hstep1 ?_
          have hC0ge : ((gridIndices d (rho + 2) 2).card : ℝ) *
              (3 : ℝ) ^ (-((d : ℝ) - epsilon)) ≤ C0 := le_max_right _ _
          have hrp : 0 ≤ r ^ ((d : ℝ) - epsilon) := Real.rpow_nonneg hr.le _
          have hKr : 0 ≤ growthConstant M H epsilon rho p omega *
              r ^ ((d : ℝ) - epsilon) := mul_nonneg hKnn0 hrp
          calc ((gridIndices d (rho + 2) 2).card : ℝ) *
                (growthConstant M H epsilon rho p omega *
                  ((3 : ℝ) ^ (-((d : ℝ) - epsilon)) * r ^ ((d : ℝ) - epsilon)))
              = (((gridIndices d (rho + 2) 2).card : ℝ) *
                  (3 : ℝ) ^ (-((d : ℝ) - epsilon))) *
                (growthConstant M H epsilon rho p omega *
                  r ^ ((d : ℝ) - epsilon)) := by ring
            _ ≤ C0 * (growthConstant M H epsilon rho p omega *
                  r ^ ((d : ℝ) - epsilon)) :=
                mul_le_mul_of_nonneg_right hC0ge hKr
            _ = C0 * growthConstant M H epsilon rho p omega *
                  r ^ ((d : ℝ) - epsilon) := (mul_assoc _ _ _).symm
        refine le_trans (le_trans (measure_mono hcover) hsumle) ?_
        calc ∑ k ∈ gridIndices d (rho + 2) 2,
              (weightedChaosCutoff M H N omega) (gridCube 2 k)
            ≤ ∑ _k ∈ gridIndices d (rho + 2) 2,
              ENNReal.ofReal (growthConstant M H epsilon rho p omega /
                growthWeight d epsilon 0) := Finset.sum_le_sum hbound
          _ = ((gridIndices d (rho + 2) 2).card : ℝ≥0∞) *
              ENNReal.ofReal (growthConstant M H epsilon rho p omega /
                growthWeight d epsilon 0) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ = ENNReal.ofReal (((gridIndices d (rho + 2) 2).card : ℝ) *
              (growthConstant M H epsilon rho p omega /
                growthWeight d epsilon 0)) := by
              rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
              congr 1
              simp
          _ ≤ ENNReal.ofReal (C0 * growthConstant M H epsilon rho p omega *
              r ^ ((d : ℝ) - epsilon)) := ENNReal.ofReal_le_ofReal harith2

end SubdiffusiveProcess

