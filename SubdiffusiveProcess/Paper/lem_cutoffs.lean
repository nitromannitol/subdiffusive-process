
-- paper label `mfd:lem-cutoffs` records the damped-extrema/Borel--Cantelli
-- derivation of the microscopic majorant from the existing inputs.
module

public import SubdiffusiveProcess.Paper.conv_represented_sequence
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.VariationalResponses.NativeBridge
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.Main.CubeFractionalL2Norm
public import SubdiffusiveProcess.Paper.conv_represented_estimates
public import SubdiffusiveProcess.Paper.cell_boundary_continuity
public import SubdiffusiveProcess.Paper.mesh_interpolator
public import SubdiffusiveProcess.Paper.lem_cutoffs_below_wavelength_scale
public import SubdiffusiveProcess.Paper.lem_cutoffs_transition_cover
public import SubdiffusiveProcess.Paper.lem_cutoffs_collar_transition_sum
public import SubdiffusiveProcess.VariationalResponses.MeshGluing
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Paper.lem_extremes
public import SubdiffusiveProcess.Paper.prop_growth
public import SubdiffusiveProcess.Paper.in_killed_inverse
public import SubdiffusiveProcess.Paper.conv_energy_measure_normalization
public import SubdiffusiveProcess.Paper.lem_20_collar_family_cell_constant
public import SubdiffusiveProcess.CutoffsOddCatalogue
public import SubdiffusiveProcess.CutoffsCommonMajorant
public import SubdiffusiveProcess.CutoffsUniformCollarSum
public import SubdiffusiveProcess.CutoffsBoundaryNorm
public import SubdiffusiveProcess.CutoffsPhysicalDepth
public import SubdiffusiveProcess.CutoffsUniformGeometry
public import SubdiffusiveProcess.Geometry.ClosedOddGridCover
public import SubdiffusiveProcess.Geometry.OddGridPartition
public import SubdiffusiveProcess.Sobolev.OddGridEnergy
public import SubdiffusiveProcess.Sobolev.HarmonicCellMinimum
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6MeasurableMaxPrinciple
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.Corrector
public import SubdiffusiveProcess.CoarseGrainingVocab.DirichletUniqueness
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace Metric
open SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_cutoffs_odd_cell_catalogue_of_represented
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
    (J : Type) [Countable J] [DecidableEq J] (j0 : J)
    (z : J → SpatialCoordinates d) (rad : J → ℝ) (hrad : ∀ j, 0 < rad j)
    (S : ∀ j, ResponseSpace (centeredCube (z j) (rad j) (hrad j)))
    (D : ∀ j, Submodule ℚ (DomainL2 (centeredCube (z j) (rad j) (hrad j))))
    [hDc : ∀ j, Countable (D j)]
    (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
    (T : J → Type) [hTc : ∀ j, Countable (T j)]
    (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
    (thetaH1 : ∀ j, T j → Homogenization.H1Function
      (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (usrc : ∀ j, (D j) → ℕ → Ω → (S j).space)
    (srcRep : ∀ j, (D j) → ℕ → Ω → SpatialCoordinates d → ℝ)
    (ucell : ∀ j, T j → ℕ → Ω → Homogenization.H1Function
      (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (Cext beta alpha eta t : ℝ) (orders : Finset ℝ) (E : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Index : Type) [Countable Index]
    (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
    (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
    (coercivityKey extensionKey lambdaKey : J → Index)
    (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ j, (D j) → Index)
    (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
    (Grid : Type) [Countable Grid]
    (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J)
    (gridKey : Grid → Index)
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (hz0 : z j0 = z0) (hrad0 : rad j0 = R)
    (hrepresented :
      _root_.SubdiffusiveProcess.Paper.conv_represented_estimates d hd M H Ω P cutoff env J j0 z rad hrad
        S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E
        Index resp respLim constants G coercivityKey extensionKey lambdaKey
        sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey
        cellGrowthKey cellHolderKey Grid origin gridRoot gridKey)
    (Jr : ℕ) (k : OddGridIndex d (triadicHalf Jr)) :
    ∃ j_cell : J,
      z j_cell = oddGridCenter z0 R (triadicHalf Jr) k ∧
      rad j_cell = R / (3 : ℝ) ^ Jr := by
  rcases hrepresented with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hcenter, hscale, hcomplete, _⟩
  exact aux_cutoffs_odd_cell_catalogue_of_geometry j0 z rad hrad z0 R hR
    hz0 hrad0 hcenter hscale hcomplete Jr k


/-- The damped finite-cutoff coefficient extrema of `lem_extremes` on the fixed
root cube. The moment order `q ≥ 1` and the threshold are fixed before the
model; below the threshold `Cd δ + Cp δ² ≤ η log 3 / 2`, so the damped extrema
`3^(-η N) (mhigh_N + mlow_N⁻¹)` have `L^q` norms decaying like
`exp(-η log 3 / 2)^N`. -/
theorem aux_lem_cutoffs_damped_extrema
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (eta : ℝ) (heta : 0 < eta) (q : ℝ) (hq : 1 ≤ q) :
    ∃ delta0 A : ℝ, 0 < delta0 ∧ 0 ≤ A ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        ∃ mlow mhigh : ℕ → BilateralField d → ℝ,
          (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
            0 < mlow N om ∧
              ∀ x ∈ (closedCube z0 R hR : Set (SpatialCoordinates d)),
                mlow N om ≤ cutoffCoefficient M H om N x ∧
                  cutoffCoefficient M H om N x ≤ mhigh N om) ∧
          (∀ N : ℕ, MemLp (fun om => (3 : ℝ) ^ (-((N : ℝ) * eta)) *
              (mhigh N om + (mlow N om)⁻¹)) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure) ∧
          (∀ N : ℕ, eLpNorm (fun om => (3 : ℝ) ^ (-((N : ℝ) * eta)) *
              (mhigh N om + (mlow N om)⁻¹)) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (A * Real.exp (-(eta * Real.log 3 / 2)) ^ N)) := by
  obtain ⟨Cp, Cd, cd, hCp, hCd, hcd, hext⟩ := _root_.SubdiffusiveProcess.Paper.aux_lem_extremes_compat d hd z0 R hR q hq
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hq0 : 0 < q := by linarith
  have hCDp : 0 < Cd + Cp := by linarith
  refine ⟨min (cd / q) (min 1 (eta * Real.log 3 / (2 * (Cd + Cp)))), Cp,
    lt_min (div_pos hcd hq0) (lt_min one_pos (div_pos (mul_pos heta hlog3) (by positivity))),
    hCp.le, ?_⟩
  intro M H hIR hδ
  have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hδcd : M.delta ≤ cd / q := hδ.trans (min_le_left _ _)
  have hδ1 : M.delta ≤ 1 := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδe : M.delta ≤ eta * Real.log 3 / (2 * (Cd + Cp)) :=
    hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨D, mlow, mhigh, -, hae, -, hmem, -, hnorm⟩ := hext M H hIR hδcd
  have hrate : Cd * M.delta + Cp * M.delta ^ 2 ≤ eta * Real.log 3 / 2 := by
    have h2 : M.delta ^ 2 ≤ M.delta := by
      rw [sq]
      exact mul_le_of_le_one_right hδpos.le hδ1
    have h3 : Cp * M.delta ^ 2 ≤ Cp * M.delta := mul_le_mul_of_nonneg_left h2 hCp.le
    calc Cd * M.delta + Cp * M.delta ^ 2 ≤ Cd * M.delta + Cp * M.delta := by linarith
      _ = (Cd + Cp) * M.delta := by ring
      _ ≤ (Cd + Cp) * (eta * Real.log 3 / (2 * (Cd + Cp))) :=
          mul_le_mul_of_nonneg_left hδe hCDp.le
      _ = eta * Real.log 3 / 2 := by
          field_simp
  refine ⟨mlow, mhigh, ?_, fun N => (hmem N).const_mul _, fun N => ?_⟩
  · filter_upwards [hae] with om hom N
    exact (hom N).2
  · set c : ℝ := (3 : ℝ) ^ (-((N : ℝ) * eta)) with hc
    have hc0 : 0 ≤ c := Real.rpow_nonneg (by norm_num) _
    have hsmul := eLpNorm_const_smul c (fun om => mhigh N om + (mlow N om)⁻¹)
      (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure
    have hkey : c * (Cp * Real.exp ((Cd * M.delta + Cp * M.delta ^ 2) * (N : ℝ))) ≤
        Cp * Real.exp (-(eta * Real.log 3 / 2)) ^ N := by
      have hexp : Real.log 3 * (-((N : ℝ) * eta)) +
          (Cd * M.delta + Cp * M.delta ^ 2) * (N : ℝ) ≤
          (N : ℝ) * (-(eta * Real.log 3 / 2)) := by
        have h := mul_le_mul_of_nonneg_right hrate (Nat.cast_nonneg N)
        have e1 : Real.log 3 * (-((N : ℝ) * eta)) = -(2 * ((eta * Real.log 3 / 2) * N)) := by
          ring
        have e2 : (N : ℝ) * (-(eta * Real.log 3 / 2)) = -((eta * Real.log 3 / 2) * N) := by
          ring
        rw [e1, e2]
        linarith
      rw [hc, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), ← Real.exp_nat_mul]
      calc Real.exp (Real.log 3 * (-((N : ℝ) * eta))) *
            (Cp * Real.exp ((Cd * M.delta + Cp * M.delta ^ 2) * (N : ℝ)))
          = Cp * Real.exp (Real.log 3 * (-((N : ℝ) * eta)) +
              (Cd * M.delta + Cp * M.delta ^ 2) * (N : ℝ)) := by
            rw [Real.exp_add]; ring
        _ ≤ Cp * Real.exp ((N : ℝ) * (-(eta * Real.log 3 / 2))) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hexp) hCp.le
    calc eLpNorm (fun om => c * (mhigh N om + (mlow N om)⁻¹)) (ENNReal.ofReal q)
          (chaosSampleLaw M).toMeasure
        = ‖c‖ₑ * eLpNorm (fun om => mhigh N om + (mlow N om)⁻¹) (ENNReal.ofReal q)
          (chaosSampleLaw M).toMeasure := hsmul
      _ ≤ ENNReal.ofReal c *
            ENNReal.ofReal (Cp * Real.exp ((Cd * M.delta + Cp * M.delta ^ 2) * (N : ℝ))) := by
          rw [Real.enorm_of_nonneg hc0]
          exact mul_le_mul_of_nonneg_left (hnorm N) zero_le
      _ = ENNReal.ofReal
            (c * (Cp * Real.exp ((Cd * M.delta + Cp * M.delta ^ 2) * (N : ℝ)))) :=
          (ENNReal.ofReal_mul hc0).symm
      _ ≤ ENNReal.ofReal (Cp * Real.exp (-(eta * Real.log 3 / 2)) ^ N) :=
          ENNReal.ofReal_le_ofReal hkey

/-- Common cutoff majorant for `lem_cutoffs` from the actual `lem_extremes`
and `conv_represented_estimates` inputs. The threshold `delta0` is fixed from the
root, `eta` and `orders` alone, before the model. For any finite selection `F`
of represented constants (for instance the root grid key and the finitely many
superunit-cell extension keys), `KN` is measurable, at least one, has uniform
moments of every requested order, dominates `F` and the damped coefficient
extrema at `N = cutoff n` on the represented environment, and is pathwise
bounded on one measurable full-measure subevent of `G`. -/
theorem aux_lem_cutoffs_common_majorant
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (eta : ℝ) (heta : 0 < eta)
    (orders : Finset ℝ) (horders : ∀ p ∈ orders, 0 < p) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        M.delta ≤ delta0 →
      ∀ (beta alpha t Cext : ℝ)
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P]
        (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
        (J : Type) [Countable J] [DecidableEq J] (j0 : J)
        (z : J → SpatialCoordinates d) (rad : J → ℝ)
        (hrad : ∀ j, 0 < rad j)
        (S : ∀ j, ResponseSpace (centeredCube (z j) (rad j) (hrad j)))
        (D : ∀ j, Submodule ℚ
          (DomainL2 (centeredCube (z j) (rad j) (hrad j))))
        [∀ j, Countable (D j)]
        (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
        (T : J → Type) [∀ j, Countable (T j)]
        (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
        (thetaH1 : ∀ j, T j →
          Homogenization.H1Function
            (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
        (usrc : ∀ j, (D j) → ℕ → Ω → (S j).space)
        (srcRep : ∀ j, (D j) → ℕ → Ω → SpatialCoordinates d → ℝ)
        (ucell : ∀ j, T j → ℕ → Ω →
          Homogenization.H1Function
            (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
        (E : _root_.SubdiffusiveProcess.Paper.in_J d)
        (Index : Type) [Countable Index]
        (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
        (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
        (coercivityKey extensionKey lambdaKey : J → Index)
        (sourceResponseKey sourceGrowthKey sourceHolderKey :
          ∀ j, (D j) → Index)
        (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
        (Grid : Type) [Countable Grid]
        (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J)
        (gridKey : Grid → Index)
        (_hz0 : z j0 = z0) (_hrad0 : rad j0 = R)
        (_hrepresented :
          _root_.SubdiffusiveProcess.Paper.conv_represented_estimates d hd M H Ω P cutoff env J j0 z rad hrad
            S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E
            Index resp respLim constants G coercivityKey extensionKey lambdaKey
            sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey
            cellGrowthKey cellHolderKey Grid origin gridRoot gridKey)
        (F : Finset Index),
        ∃ KN : ℕ → Ω → ℝ, ∃ Ggood : Set Ω, ∃ mlow mhigh : ℕ → BilateralField d → ℝ,
          MeasurableSet Ggood ∧ Ggood ⊆ G ∧ P (Ggoodᶜ) = 0 ∧
          (∀ n : ℕ, Measurable (KN n)) ∧
          (∀ n : ℕ, ∀ omega : Ω, 1 ≤ KN n omega) ∧
          (∀ p ∈ orders, ∃ Cp : ℝ, 0 ≤ Cp ∧
            ∀ n : ℕ,
              MemLp (KN n) (ENNReal.ofReal p) P ∧
                eLpNorm (KN n) (ENNReal.ofReal p) P ≤ ENNReal.ofReal Cp) ∧
          (∀ omega ∈ Ggood,
            BddAbove (Set.range (fun n : ℕ => KN n omega))) ∧
          (∀ omega ∈ Ggood, ∀ n : ℕ, ∀ i ∈ F, constants i n omega ≤ KN n omega) ∧
          (∀ omega ∈ Ggood, ∀ n : ℕ,
            0 < mlow (cutoff n) (env n omega) ∧
            (∀ x ∈ closure
                (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
              mlow (cutoff n) (env n omega) ≤
                  cutoffCoefficient M H (env n omega) (cutoff n) x ∧
                cutoffCoefficient M H (env n omega) (cutoff n) x ≤
                  mhigh (cutoff n) (env n omega)) ∧
            mhigh (cutoff n) (env n omega) ≤
              KN n omega * (3 : ℝ) ^ (((cutoff n : ℕ) : ℝ) * eta) ∧
            (mlow (cutoff n) (env n omega))⁻¹ ≤
              KN n omega * (3 : ℝ) ^ (((cutoff n : ℕ) : ℝ) * eta)) := by
  classical
  have hsum0 : 0 ≤ ∑ p ∈ orders, p := Finset.sum_nonneg (fun p hp => (horders p hp).le)
  have hq1 : (1 : ℝ) ≤ 1 + ∑ p ∈ orders, p := by linarith
  have hqord : ∀ p ∈ orders, p ≤ 1 + ∑ p ∈ orders, p := by
    intro p hp
    have := Finset.single_le_sum (f := fun p : ℝ => p) (fun p hp => (horders p hp).le) hp
    linarith
  obtain ⟨delta0, A, hdelta0, hA, hext⟩ :=
    aux_lem_cutoffs_damped_extrema d hd z0 R hR eta heta (1 + ∑ p ∈ orders, p) hq1
  refine ⟨delta0, hdelta0, ?_⟩
  intro M H hM beta alpha t Cext Ω _ P _ cutoff env J _ _ j0 z rad hrad S D _ f T _ theta
    thetaH1 usrc srcRep ucell E Index _ resp respLim constants G coercivityKey extensionKey
    lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey
    cellHolderKey Grid _ origin gridRoot gridKey hz0 hrad0 hrepresented F
  obtain ⟨-, -, -, -, -, hcut, hIR, henv, hlaw, hseq, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, hcm, hmom, -⟩ := hrepresented
  obtain ⟨-, -, hG, -, hbdd⟩ := hseq
  obtain ⟨mlow, mhigh, hae, hXmem, hXbd⟩ := hext M H hIR hM
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  obtain ⟨KN, Ggood, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    aux_cutoffs_common_majorant_core P (chaosSampleLaw M).toMeasure cutoff hcut env henv
      hlaw constants G hG hcm orders hmom hbdd F _ hae _ (1 + ∑ p ∈ orders, p) hq1 hqord A
      (Real.exp (-(eta * Real.log 3 / 2))) hA (Real.exp_pos _).le
      ((Real.exp_lt_exp.2 (by have := mul_pos heta hlog3; linarith)).trans_eq Real.exp_zero)
      hXmem hXbd
  refine ⟨KN, Ggood, mlow, mhigh, h1, h2, h3, h4, h5, h6, h7, h8, ?_⟩
  intro om hom n
  obtain ⟨hgd, hX⟩ := h9 om hom n
  obtain ⟨hlow, hcube⟩ := hgd (cutoff n)
  have hQ : ∀ x ∈ closure
      (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
      x ∈ (closedCube z0 R hR : Set (SpatialCoordinates d)) := by
    intro x hx
    have hx' : x ∈ closure (Metric.ball (z j0) (rad j0 / 2)) := hx
    have hball := Metric.closure_ball_subset_closedBall hx'
    change x ∈ Metric.closedBall z0 (R / 2)
    rw [← hz0, ← hrad0]
    exact hball
  have hz0mem : z0 ∈ (closedCube z0 R hR : Set (SpatialCoordinates d)) := by
    change z0 ∈ Metric.closedBall z0 (R / 2)
    exact Metric.mem_closedBall_self (by positivity)
  have hhigh_nonneg : 0 ≤ mhigh (cutoff n) (env n om) :=
    (hlow.trans_le ((hcube z0 hz0mem).1.trans (hcube z0 hz0mem).2)).le
  have hinv_pos : 0 < (mlow (cutoff n) (env n om))⁻¹ := inv_pos.2 hlow
  have hpos : 0 < (3 : ℝ) ^ (((cutoff n : ℕ) : ℝ) * eta) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hS : mhigh (cutoff n) (env n om) + (mlow (cutoff n) (env n om))⁻¹ ≤
      KN n om * (3 : ℝ) ^ (((cutoff n : ℕ) : ℝ) * eta) := by
    have hX' : ((3 : ℝ) ^ (((cutoff n : ℕ) : ℝ) * eta))⁻¹ *
        (mhigh (cutoff n) (env n om) + (mlow (cutoff n) (env n om))⁻¹) ≤ KN n om := by
      rw [← Real.rpow_neg (by norm_num)]
      exact hX
    rw [inv_mul_le_iff₀ hpos] at hX'
    rw [mul_comm]
    exact hX'
  refine ⟨hlow, fun x hx => hcube x (hQ x hx), ?_, ?_⟩
  · linarith
  · linarith

/-- Reduction of `lem_cutoffs` to its pathwise mesh and collar step. The
hypothesis `hMC` is exactly the remaining proof obligation: for an abstract
majorant `KN` that is at least one, pathwise bounded on `Ggood ⊆ G`, dominates a
finite selection `F` of represented constants (chosen after the representation)
and dominates the damped coefficient extrema at `N = cutoff n`, the harmonic
plateau and collar conclusions hold on `Ggood`. The measurable majorant, its
moments and the common event are supplied by
`aux_lem_cutoffs_common_majorant`. -/
theorem aux_lem_cutoffs_of_mesh_collar
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (beta alpha eta t : ℝ)
    (_hbeta : 1 / 2 < beta) (_hbetaalpha : beta < alpha)
    (_halpha : alpha < 1) (heta : 0 < eta)
    (_htlow : (d : ℝ) - 1 < t) (_htupper : t < (d : ℝ))
    (_hetaalpha : 1 + eta < 2 * alpha)
    (orders : Finset ℝ) (horders : ∀ p ∈ orders, 0 < p)
    (Cext Cgrad : ℝ) (_hCext : 0 < Cext) (_hCgrad : 0 < Cgrad)
    (hMC : ∃ delta1 Ccollar : ℝ, 0 < delta1 ∧ 0 < Ccollar ∧
        ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
          (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
          M.delta ≤ delta1 →
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
          [IsProbabilityMeasure P]
          (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
          (J : Type) [Countable J] [DecidableEq J] (j0 : J)
          (z : J → SpatialCoordinates d) (rad : J → ℝ)
          (hrad : ∀ j, 0 < rad j)
          (S : ∀ j, ResponseSpace (centeredCube (z j) (rad j) (hrad j)))
          (D : ∀ j, Submodule ℚ
            (DomainL2 (centeredCube (z j) (rad j) (hrad j))))
          [_hDc : ∀ j, Countable (D j)]
          (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
          (T : J → Type) [_hTc : ∀ j, Countable (T j)]
          (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
          (thetaH1 : ∀ j, T j →
            Homogenization.H1Function
              (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
          (usrc : ∀ j, (D j) → ℕ → Ω → (S j).space)
          (srcRep : ∀ j, (D j) → ℕ → Ω → SpatialCoordinates d → ℝ)
          (ucell : ∀ j, T j → ℕ → Ω →
            Homogenization.H1Function
              (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
          (E : _root_.SubdiffusiveProcess.Paper.in_J d)
          (Index : Type) [Countable Index]
          (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
          (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
          (coercivityKey extensionKey lambdaKey : J → Index)
          (sourceResponseKey sourceGrowthKey sourceHolderKey :
            ∀ j, (D j) → Index)
          (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
          (Grid : Type) [Countable Grid]
          (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J)
          (gridKey : Grid → Index)
          (_hz0 : z j0 = z0) (_hrad0 : rad j0 = R)
          (_hrepresented :
            _root_.SubdiffusiveProcess.Paper.conv_represented_estimates d hd M H Ω P cutoff env J j0 z rad hrad
              S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E
              Index resp respLim constants G coercivityKey extensionKey lambdaKey
              sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey
              cellGrowthKey cellHolderKey Grid origin gridRoot gridKey),
          let Q := centeredCube (z j0) (rad j0) (hrad j0)
          let S0 := S j0
          let aN := fun (omega : Ω) (n : ℕ) =>
            _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n omega) (cutoff n)
              (z j0) (hrad j0)
          let rawAN := fun (omega : Ω) (n : ℕ) =>
            cutoffCoefficient M H (env n omega) (cutoff n)
          ∃ F : Finset Index,
            ∀ (KN : ℕ → Ω → ℝ) (Ggood : Set Ω) (mlow mhigh : ℕ → BilateralField d → ℝ),
              Ggood ⊆ G →
              (∀ n : ℕ, ∀ omega : Ω, 1 ≤ KN n omega) →
              (∀ omega ∈ Ggood, BddAbove (Set.range (fun n : ℕ => KN n omega))) →
              (∀ omega ∈ Ggood, ∀ n : ℕ, ∀ i ∈ F, constants i n omega ≤ KN n omega) →
              (∀ omega ∈ Ggood, ∀ n : ℕ,
                0 < mlow (cutoff n) (env n omega) ∧
                (∀ x ∈ closure
                    (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
                  mlow (cutoff n) (env n omega) ≤
                      cutoffCoefficient M H (env n omega) (cutoff n) x ∧
                    cutoffCoefficient M H (env n omega) (cutoff n) x ≤
                      mhigh (cutoff n) (env n omega)) ∧
                mhigh (cutoff n) (env n omega) ≤
                  KN n omega * (3 : ℝ) ^ (((cutoff n : ℕ) : ℝ) * eta) ∧
                (mlow (cutoff n) (env n omega))⁻¹ ≤
                  KN n omega * (3 : ℝ) ^ (((cutoff n : ℕ) : ℝ) * eta)) →
              ∀ omega ∈ Ggood,
                (∀ b : T j0, ∀ K O W : Set (SpatialCoordinates d), ∀ Jmesh : ℕ,
                  IsCompact K → IsOpen O →
                  closure O ⊆ (Q : Set (SpatialCoordinates d)) →
                  IsOpen W → K ⊆ W → W ⊆ O →
                  (∀ x : SpatialCoordinates d,
                    0 ≤ theta j0 b x ∧ theta j0 b x ≤ 1) →
                  (∀ x ∈ W, theta j0 b x = 1) →
                  tsupport (theta j0 b) ⊆ O →
                  (∀ k : OddGridIndex d (triadicHalf Jmesh),
                    (closure
                        (oddGridCell (z j0) (rad j0) (hrad j0)
                          (triadicHalf Jmesh) k : Set (SpatialCoordinates d)) ∩
                        {x : SpatialCoordinates d |
                          0 < theta j0 b x ∧ theta j0 b x < 1}).Nonempty →
                      closure
                          (oddGridCell (z j0) (rad j0) (hrad j0)
                            (triadicHalf Jmesh) k : Set (SpatialCoordinates d)) ⊆
                        O \ K) →
                  ∃ chiH : ℕ → Homogenization.H1Function
                      (Q : Set (SpatialCoordinates d)),
                    ∃ chiS : ℕ → S0.space,
                      ∃ chic : ℕ → SpatialCoordinates d → ℝ,
                        ∃ V : Set (SpatialCoordinates d),
                          ∃ Benergy Ball Bholder : ℝ,
                            IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧
                            0 ≤ Benergy ∧ 0 ≤ Ball ∧ 0 ≤ Bholder ∧
                            (∀ n : ℕ,
                              (chiS n).val = sobolevDataOfH1 (chiH n) ∧
                              ContinuousOn (chic n)
                                (closure (Q : Set (SpatialCoordinates d))) ∧
                              (chiS n).val.1 =ᵐ[
                                volume.restrict (Q : Set (SpatialCoordinates d))]
                                chic n ∧
                              (∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
                                0 ≤ chic n x ∧ chic n x ≤ 1) ∧
                              (∀ x ∈ V, chic n x = 1) ∧
                              (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                                x ∉ O → chic n x = 0) ∧
                              (∀ k : OddGridIndex d (triadicHalf Jmesh),
                                IsWeaklyHarmonicOn (rawAN omega n)
                                  (oddGridCell (z j0) (rad j0) (hrad j0)
                                    (triadicHalf Jmesh) k : Set (SpatialCoordinates d))
                                  ((chiH n).restrict
                                    (oddGridCell (z j0) (rad j0) (hrad j0)
                                      (triadicHalf Jmesh) k).isOpen
                                    (oddGridCell_subset (z j0) (hrad j0)
                                      (triadicHalf Jmesh) k)) ∧
                                HasZeroTraceDifferenceOn
                                  (oddGridCell (z j0) (rad j0) (hrad j0)
                                    (triadicHalf Jmesh) k : Set (SpatialCoordinates d))
                                  ((chiH n).restrict
                                    (oddGridCell (z j0) (rad j0) (hrad j0)
                                      (triadicHalf Jmesh) k).isOpen
                                    (oddGridCell_subset (z j0) (hrad j0)
                                      (triadicHalf Jmesh) k))
                                  ((thetaH1 j0 b).restrict
                                    (oddGridCell (z j0) (rad j0) (hrad j0)
                                      (triadicHalf Jmesh) k).isOpen
                                    (oddGridCell_subset (z j0) (hrad j0)
                                      (triadicHalf Jmesh) k))) ∧
                              (∀ k : OddGridIndex d (triadicHalf Jmesh),
                                (∃ c : ℝ, ∀ x ∈ closure
                                    (oddGridCell (z j0) (rad j0) (hrad j0)
                                      (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                                  theta j0 b x = c) →
                                  ∀ i : Fin d, ∀ᵐ x ∂volume.restrict
                                    (oddGridCell (z j0) (rad j0) (hrad j0)
                                      (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                                    (chiS n).val.2 i x = 0) ∧
                              responseForm S0 (aN omega n) (chiS n) (chiS n) ≤ Benergy ∧
                              (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), ∀ s : ℝ,
                                0 < s → s ≤ 1 →
                                ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
                                  (fun y => ENNReal.ofReal
                                    ((aN omega n).val y *
                                      ∑ i : Fin d, ((chiS n).val.2 i y) ^ 2)))
                                  (Metric.ball x s) ≤ ENNReal.ofReal (Ball * s ^ t)) ∧
                              _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
                                (closure (Q : Set (SpatialCoordinates d))) (chic n) ∧
                              _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
                                (closure (Q : Set (SpatialCoordinates d))) (chic n) ≤
                                Bholder) ∧
                            (∃ sigma : ℕ → ℕ, ∃ chiLim : SpatialCoordinates d → ℝ,
                              StrictMono sigma ∧
                              ContinuousOn chiLim
                                (closure (Q : Set (SpatialCoordinates d))) ∧
                              TendstoUniformlyOn (fun n => chic (sigma n)) chiLim atTop
                                (closure (Q : Set (SpatialCoordinates d))) ∧
                              (∀ k : OddGridIndex d (triadicHalf Jmesh),
                                (∃ c : ℝ, ∀ x ∈ closure
                                    (oddGridCell (z j0) (rad j0) (hrad j0)
                                      (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                                  theta j0 b x = c) →
                                  ∀ x ∈ closure
                                    (oddGridCell (z j0) (rad j0) (hrad j0)
                                      (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                                    chiLim x = theta j0 b x))) ∧
                (∀ Jr : ℕ,
                  let rho := rad j0 / (3 : ℝ) ^ Jr
                    ∀ thetaR : SpatialCoordinates d → ℝ,
                      ContDiff ℝ ∞ thetaR →
                      (∀ x : SpatialCoordinates d,
                        0 ≤ thetaR x ∧ thetaR x ≤ 1) →
                      (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                        Metric.infDist x (frontier (Q : Set (SpatialCoordinates d))) ≤ rho →
                          thetaR x = 0) →
                      (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                        3 * rho ≤ Metric.infDist x (frontier (Q : Set (SpatialCoordinates d))) →
                          thetaR x = 1) →
                      (∀ x : SpatialCoordinates d,
                        norm (fderiv ℝ thetaR x) ≤ Cgrad / rho) →
                      ∀ thetaRH1 : Homogenization.H1Function
                        (Q : Set (SpatialCoordinates d)),
                        thetaRH1.toFun = thetaR →
                        ∃ collarH : ℕ → Homogenization.H1Function
                            (Q : Set (SpatialCoordinates d)),
                          ∃ collarS : ℕ → S0.space,
                            ∃ collarC : ℕ → SpatialCoordinates d → ℝ,
                              ∀ n : ℕ,
                                (collarS n).val = sobolevDataOfH1 (collarH n) ∧
                                ContinuousOn (collarC n)
                                  (closure (Q : Set (SpatialCoordinates d))) ∧
                                (collarS n).val.1 =ᵐ[
                                  volume.restrict (Q : Set (SpatialCoordinates d))]
                                  collarC n ∧
                                (∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
                                  0 ≤ collarC n x ∧ collarC n x ≤ 1) ∧
                                (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                                  Metric.infDist x
                                      (frontier (Q : Set (SpatialCoordinates d))) ≤ rho →
                                    collarC n x = 0) ∧
                                (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                                  3 * rho ≤ Metric.infDist x
                                      (frontier (Q : Set (SpatialCoordinates d))) →
                                    collarC n x = 1) ∧
                                (∀ i : Fin d, ∀ᵐ x ∂volume.restrict
                                  (Q : Set (SpatialCoordinates d)),
                                  3 * rho < Metric.infDist x
                                      (frontier (Q : Set (SpatialCoordinates d))) →
                                    (collarS n).val.2 i x = 0) ∧
                                (∀ k : OddGridIndex d (triadicHalf Jr),
                                  IsWeaklyHarmonicOn (rawAN omega n)
                                    (oddGridCell (z j0) (rad j0) (hrad j0)
                                      (triadicHalf Jr) k : Set (SpatialCoordinates d))
                                    ((collarH n).restrict
                                      (oddGridCell (z j0) (rad j0) (hrad j0)
                                        (triadicHalf Jr) k).isOpen
                                      (oddGridCell_subset (z j0) (hrad j0)
                                        (triadicHalf Jr) k)) ∧
                                  HasZeroTraceDifferenceOn
                                    (oddGridCell (z j0) (rad j0) (hrad j0)
                                      (triadicHalf Jr) k : Set (SpatialCoordinates d))
                                    ((collarH n).restrict
                                      (oddGridCell (z j0) (rad j0) (hrad j0)
                                        (triadicHalf Jr) k).isOpen
                                      (oddGridCell_subset (z j0) (hrad j0)
                                        (triadicHalf Jr) k))
                                    (thetaRH1.restrict
                                      (oddGridCell (z j0) (rad j0) (hrad j0)
                                        (triadicHalf Jr) k).isOpen
                                      (oddGridCell_subset (z j0) (hrad j0)
                                        (triadicHalf Jr) k))) ∧
                                responseForm S0 (aN omega n) (collarS n) (collarS n) ≤
                                  Ccollar * KN n omega * rho ^ (-1 - eta))) :
    ∃ delta0 Ccollar : ℝ, 0 < delta0 ∧ 0 < Ccollar ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        M.delta ≤ delta0 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P]
        (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
        (J : Type) [Countable J] [DecidableEq J] (j0 : J)
        (z : J → SpatialCoordinates d) (rad : J → ℝ)
        (hrad : ∀ j, 0 < rad j)
        (S : ∀ j, ResponseSpace (centeredCube (z j) (rad j) (hrad j)))
        (D : ∀ j, Submodule ℚ
          (DomainL2 (centeredCube (z j) (rad j) (hrad j))))
        [_hDc : ∀ j, Countable (D j)]
        (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
        (T : J → Type) [_hTc : ∀ j, Countable (T j)]
        (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
        (thetaH1 : ∀ j, T j →
          Homogenization.H1Function
            (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
        (usrc : ∀ j, (D j) → ℕ → Ω → (S j).space)
        (srcRep : ∀ j, (D j) → ℕ → Ω → SpatialCoordinates d → ℝ)
        (ucell : ∀ j, T j → ℕ → Ω →
          Homogenization.H1Function
            (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
        (E : _root_.SubdiffusiveProcess.Paper.in_J d)
        (Index : Type) [Countable Index]
        (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
        (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
        (coercivityKey extensionKey lambdaKey : J → Index)
        (sourceResponseKey sourceGrowthKey sourceHolderKey :
          ∀ j, (D j) → Index)
        (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
        (Grid : Type) [Countable Grid]
        (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J)
        (gridKey : Grid → Index)
        (_hz0 : z j0 = z0) (_hrad0 : rad j0 = R)
        (_hrepresented :
          _root_.SubdiffusiveProcess.Paper.conv_represented_estimates d hd M H Ω P cutoff env J j0 z rad hrad
            S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E
            Index resp respLim constants G coercivityKey extensionKey lambdaKey
            sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey
            cellGrowthKey cellHolderKey Grid origin gridRoot gridKey),
        let Q := centeredCube (z j0) (rad j0) (hrad j0)
        let S0 := S j0
        let aN := fun (omega : Ω) (n : ℕ) =>
          _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n omega) (cutoff n)
            (z j0) (hrad j0)
        let rawAN := fun (omega : Ω) (n : ℕ) =>
          cutoffCoefficient M H (env n omega) (cutoff n)
        ∃ KN : ℕ → Ω → ℝ, ∃ Ggood : Set Ω,
          MeasurableSet Ggood ∧ Ggood ⊆ G ∧ P (Ggoodᶜ) = 0 ∧
          (∀ n : ℕ, Measurable (KN n)) ∧
          (∀ n : ℕ, ∀ omega : Ω, 1 ≤ KN n omega) ∧
          (∀ p ∈ orders, ∃ Cp : ℝ, 0 ≤ Cp ∧
            ∀ n : ℕ,
              MemLp (KN n) (ENNReal.ofReal p) P ∧
                eLpNorm (KN n) (ENNReal.ofReal p) P ≤ ENNReal.ofReal Cp) ∧
          (∀ omega ∈ Ggood,
            BddAbove (Set.range (fun n : ℕ => KN n omega))) ∧
          ∀ omega ∈ Ggood,
            (∀ b : T j0, ∀ K O W : Set (SpatialCoordinates d), ∀ Jmesh : ℕ,
              IsCompact K → IsOpen O →
              closure O ⊆ (Q : Set (SpatialCoordinates d)) →
              IsOpen W → K ⊆ W → W ⊆ O →
              (∀ x : SpatialCoordinates d,
                0 ≤ theta j0 b x ∧ theta j0 b x ≤ 1) →
              (∀ x ∈ W, theta j0 b x = 1) →
              tsupport (theta j0 b) ⊆ O →
              (∀ k : OddGridIndex d (triadicHalf Jmesh),
                (closure
                    (oddGridCell (z j0) (rad j0) (hrad j0)
                      (triadicHalf Jmesh) k : Set (SpatialCoordinates d)) ∩
                    {x : SpatialCoordinates d |
                      0 < theta j0 b x ∧ theta j0 b x < 1}).Nonempty →
                  closure
                      (oddGridCell (z j0) (rad j0) (hrad j0)
                        (triadicHalf Jmesh) k : Set (SpatialCoordinates d)) ⊆
                    O \ K) →
              ∃ chiH : ℕ → Homogenization.H1Function
                  (Q : Set (SpatialCoordinates d)),
                ∃ chiS : ℕ → S0.space,
                  ∃ chic : ℕ → SpatialCoordinates d → ℝ,
                    ∃ V : Set (SpatialCoordinates d),
                      ∃ Benergy Ball Bholder : ℝ,
                        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧
                        0 ≤ Benergy ∧ 0 ≤ Ball ∧ 0 ≤ Bholder ∧
                        (∀ n : ℕ,
                          (chiS n).val = sobolevDataOfH1 (chiH n) ∧
                          ContinuousOn (chic n)
                            (closure (Q : Set (SpatialCoordinates d))) ∧
                          (chiS n).val.1 =ᵐ[
                            volume.restrict (Q : Set (SpatialCoordinates d))]
                            chic n ∧
                          (∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
                            0 ≤ chic n x ∧ chic n x ≤ 1) ∧
                          (∀ x ∈ V, chic n x = 1) ∧
                          (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                            x ∉ O → chic n x = 0) ∧
                          (∀ k : OddGridIndex d (triadicHalf Jmesh),
                            IsWeaklyHarmonicOn (rawAN omega n)
                              (oddGridCell (z j0) (rad j0) (hrad j0)
                                (triadicHalf Jmesh) k : Set (SpatialCoordinates d))
                              ((chiH n).restrict
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k).isOpen
                                (oddGridCell_subset (z j0) (hrad j0)
                                  (triadicHalf Jmesh) k)) ∧
                            HasZeroTraceDifferenceOn
                              (oddGridCell (z j0) (rad j0) (hrad j0)
                                (triadicHalf Jmesh) k : Set (SpatialCoordinates d))
                              ((chiH n).restrict
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k).isOpen
                                (oddGridCell_subset (z j0) (hrad j0)
                                  (triadicHalf Jmesh) k))
                              ((thetaH1 j0 b).restrict
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k).isOpen
                                (oddGridCell_subset (z j0) (hrad j0)
                                  (triadicHalf Jmesh) k))) ∧
                          (∀ k : OddGridIndex d (triadicHalf Jmesh),
                            (∃ c : ℝ, ∀ x ∈ closure
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                              theta j0 b x = c) →
                              ∀ i : Fin d, ∀ᵐ x ∂volume.restrict
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                                (chiS n).val.2 i x = 0) ∧
                          responseForm S0 (aN omega n) (chiS n) (chiS n) ≤ Benergy ∧
                          (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), ∀ s : ℝ,
                            0 < s → s ≤ 1 →
                            ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
                              (fun y => ENNReal.ofReal
                                ((aN omega n).val y *
                                  ∑ i : Fin d, ((chiS n).val.2 i y) ^ 2)))
                              (Metric.ball x s) ≤ ENNReal.ofReal (Ball * s ^ t)) ∧
                          _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
                            (closure (Q : Set (SpatialCoordinates d))) (chic n) ∧
                          _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
                            (closure (Q : Set (SpatialCoordinates d))) (chic n) ≤
                            Bholder) ∧
                        (∃ sigma : ℕ → ℕ, ∃ chiLim : SpatialCoordinates d → ℝ,
                          StrictMono sigma ∧
                          ContinuousOn chiLim
                            (closure (Q : Set (SpatialCoordinates d))) ∧
                          TendstoUniformlyOn (fun n => chic (sigma n)) chiLim atTop
                            (closure (Q : Set (SpatialCoordinates d))) ∧
                          (∀ k : OddGridIndex d (triadicHalf Jmesh),
                            (∃ c : ℝ, ∀ x ∈ closure
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                              theta j0 b x = c) →
                              ∀ x ∈ closure
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                                chiLim x = theta j0 b x))) ∧
            (∀ Jr : ℕ,
              let rho := rad j0 / (3 : ℝ) ^ Jr
                ∀ thetaR : SpatialCoordinates d → ℝ,
                  ContDiff ℝ ∞ thetaR →
                  (∀ x : SpatialCoordinates d,
                    0 ≤ thetaR x ∧ thetaR x ≤ 1) →
                  (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                    Metric.infDist x (frontier (Q : Set (SpatialCoordinates d))) ≤ rho →
                      thetaR x = 0) →
                  (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                    3 * rho ≤ Metric.infDist x (frontier (Q : Set (SpatialCoordinates d))) →
                      thetaR x = 1) →
                  (∀ x : SpatialCoordinates d,
                    norm (fderiv ℝ thetaR x) ≤ Cgrad / rho) →
                  ∀ thetaRH1 : Homogenization.H1Function
                    (Q : Set (SpatialCoordinates d)),
                    thetaRH1.toFun = thetaR →
                    ∃ collarH : ℕ → Homogenization.H1Function
                        (Q : Set (SpatialCoordinates d)),
                      ∃ collarS : ℕ → S0.space,
                        ∃ collarC : ℕ → SpatialCoordinates d → ℝ,
                          ∀ n : ℕ,
                            (collarS n).val = sobolevDataOfH1 (collarH n) ∧
                            ContinuousOn (collarC n)
                              (closure (Q : Set (SpatialCoordinates d))) ∧
                            (collarS n).val.1 =ᵐ[
                              volume.restrict (Q : Set (SpatialCoordinates d))]
                              collarC n ∧
                            (∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
                              0 ≤ collarC n x ∧ collarC n x ≤ 1) ∧
                            (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                              Metric.infDist x
                                  (frontier (Q : Set (SpatialCoordinates d))) ≤ rho →
                                collarC n x = 0) ∧
                            (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                              3 * rho ≤ Metric.infDist x
                                  (frontier (Q : Set (SpatialCoordinates d))) →
                                collarC n x = 1) ∧
                            (∀ i : Fin d, ∀ᵐ x ∂volume.restrict
                              (Q : Set (SpatialCoordinates d)),
                              3 * rho < Metric.infDist x
                                  (frontier (Q : Set (SpatialCoordinates d))) →
                                (collarS n).val.2 i x = 0) ∧
                            (∀ k : OddGridIndex d (triadicHalf Jr),
                              IsWeaklyHarmonicOn (rawAN omega n)
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jr) k : Set (SpatialCoordinates d))
                                ((collarH n).restrict
                                  (oddGridCell (z j0) (rad j0) (hrad j0)
                                    (triadicHalf Jr) k).isOpen
                                  (oddGridCell_subset (z j0) (hrad j0)
                                    (triadicHalf Jr) k)) ∧
                              HasZeroTraceDifferenceOn
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jr) k : Set (SpatialCoordinates d))
                                ((collarH n).restrict
                                  (oddGridCell (z j0) (rad j0) (hrad j0)
                                    (triadicHalf Jr) k).isOpen
                                  (oddGridCell_subset (z j0) (hrad j0)
                                    (triadicHalf Jr) k))
                                (thetaRH1.restrict
                                  (oddGridCell (z j0) (rad j0) (hrad j0)
                                    (triadicHalf Jr) k).isOpen
                                  (oddGridCell_subset (z j0) (hrad j0)
                                    (triadicHalf Jr) k))) ∧
                            responseForm S0 (aN omega n) (collarS n) (collarS n) ≤
                              Ccollar * KN n omega * rho ^ (-1 - eta)) := by
  classical
  obtain ⟨delta1, Ccollar, hdelta1, hCcollar, hmc⟩ := hMC
  obtain ⟨delta0, hdelta0, hmaj⟩ :=
    aux_lem_cutoffs_common_majorant d hd z0 R hR eta heta orders horders
  refine ⟨min delta0 delta1, Ccollar, lt_min hdelta0 hdelta1, hCcollar, ?_⟩
  intro M H hM Ω _ P _ cutoff env J _ _ j0 z rad hrad S D _ f T _ theta thetaH1 usrc srcRep
    ucell E Index _ resp respLim constants G coercivityKey extensionKey lambdaKey
    sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey
    cellHolderKey Grid _ origin gridRoot gridKey hz0 hrad0 hrepresented
  have hmcF := hmc M H (hM.trans (min_le_right _ _)) Ω P cutoff env J j0 z rad hrad S D
    f T theta thetaH1 usrc srcRep ucell E Index resp respLim constants G coercivityKey
    extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey
    cellGrowthKey cellHolderKey Grid origin gridRoot gridKey hz0 hrad0 hrepresented
  rcases hmcF with ⟨F, hF⟩
  have hmajF :=
    hmaj M H (hM.trans (min_le_left _ _)) beta alpha t Cext Ω P cutoff env J j0 z rad hrad
      S D f T theta thetaH1 usrc srcRep ucell E Index resp respLim constants G coercivityKey
      extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey hz0 hrad0
      hrepresented F
  rcases hmajF with ⟨KN, Ggood, mlow, mhigh, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact ⟨KN, Ggood, h1, h2, h3, h4, h5, h6, h7, hF KN Ggood mlow mhigh h2 h5 h7 h8 h9⟩

/-! ### Holder helpers of the mesh/collar step -/

/-- A coordinate difference is at most the Euclidean distance. -/
theorem aux_lem_cutoffs_holder_coord_le_edist {d : ℕ} (x y : SpatialCoordinates d)
    (i : Fin d) : |x i - y i| ≤ Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j => (x j - y j) ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i))

/-- Distinct points have positive Euclidean distance. -/
theorem aux_lem_cutoffs_holder_edist_pos {d : ℕ} {x y : SpatialCoordinates d} (hxy : x ≠ y) :
    0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
    by_contra h
    push Not at h
    exact hxy (funext h)
  exact lt_of_lt_of_le (abs_pos.mpr (sub_ne_zero.mpr hi))
    (aux_lem_cutoffs_holder_coord_le_edist x y i)

/-- The Euclidean distance is at most `√d` times the sup distance. -/
theorem aux_lem_cutoffs_holder_edist_le_dist {d : ℕ} (x y : SpatialCoordinates d) :
    Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt d * dist x y := by
  have hsum : ∑ j : Fin d, (x j - y j) ^ 2 ≤ (d : ℝ) * dist x y ^ 2 := by
    calc ∑ j : Fin d, (x j - y j) ^ 2 ≤ ∑ _j : Fin d, dist x y ^ 2 := by
          apply Finset.sum_le_sum
          intro j _
          rw [← sq_abs]
          have h := dist_le_pi_dist x y j
          rw [Real.dist_eq] at h
          exact pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = (d : ℝ) * dist x y ^ 2 := by simp
  calc Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt ((d : ℝ) * dist x y ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt d * dist x y := by
        rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq dist_nonneg]

/-- Points differing in one coordinate: the Euclidean distance is that coordinate gap. -/
theorem aux_lem_cutoffs_holder_edist_single {d : ℕ} (p q : SpatialCoordinates d) (i : Fin d)
    (h : ∀ j, j ≠ i → p j = q j) :
    Real.sqrt (∑ j : Fin d, (p j - q j) ^ 2) = |p i - q i| := by
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [h j hj])
    (fun hi => absurd (Finset.mem_univ i) hi), Real.sqrt_sq_eq_abs]

/-- The closed centered cube is the closed coordinate box. -/
theorem aux_lem_cutoffs_holder_mem_closure_cube {d : ℕ} (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (x : SpatialCoordinates d) :
    x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)) ↔
      ∀ i, |x i - z i| ≤ r / 2 := by
  change x ∈ closure (Metric.ball z (r / 2)) ↔ _
  rw [closure_ball z (by positivity : r / 2 ≠ 0), Metric.mem_closedBall,
    dist_pi_le_iff (by positivity)]
  simp only [Real.dist_eq]

/-- The closed odd-grid cell is the closed coordinate box around its center. -/
theorem aux_lem_cutoffs_holder_mem_closure_cell {d : ℕ} (z : SpatialCoordinates d) {R : ℝ}
    (hR : 0 < R) (m : ℕ) (k : OddGridIndex d m) (x : SpatialCoordinates d) :
    x ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)) ↔
      ∀ i, |x i - oddGridCenter z R m k i| ≤ R / (2 * (m : ℝ) + 1) / 2 :=
  aux_lem_cutoffs_holder_mem_closure_cube _ _ x

/-- Every point of the closed cube lies in some closed cell. -/
theorem aux_lem_cutoffs_holder_exists_cell {d : ℕ} (z : SpatialCoordinates d) {R : ℝ}
    (hR : 0 < R) (m : ℕ) {p : SpatialCoordinates d}
    (hp : p ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d))) :
    ∃ k : OddGridIndex d m, p ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)) := by
  rw [← oddGridCell_closure_iUnion_eq_closure_centeredCube z hR m] at hp
  exact mem_iUnion.mp hp

/-- Changing one coordinate of a closed-cell point keeps it in a closed cell with the
same labels off that coordinate, provided the new coordinate fits. -/
theorem aux_lem_cutoffs_holder_update_mem_cell {d : ℕ} (z : SpatialCoordinates d) {R : ℝ}
    (hR : 0 < R) (m : ℕ) {k k' : OddGridIndex d m} {p : SpatialCoordinates d}
    (hp : p ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d))) (i : Fin d)
    (hk : ∀ j, j ≠ i → k' j = k j) {s : ℝ}
    (hs : |s - oddGridCenter z R m k' i| ≤ R / (2 * (m : ℝ) + 1) / 2) :
    Function.update p i s ∈ closure (oddGridCell z R hR m k' : Set (SpatialCoordinates d)) := by
  rw [aux_lem_cutoffs_holder_mem_closure_cell] at hp ⊢
  intro j
  by_cases hj : j = i
  · subst hj
    simpa using hs
  · rw [Function.update_of_ne hj]
    have h := hp j
    simpa only [oddGridCenter, hk j hj] using h

/-- One-coordinate step below the mesh width, in increasing direction. -/
theorem aux_lem_cutoffs_holder_step_le {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (m : ℕ) {alpha : ℝ} (halpha : 0 < alpha) {H : ℝ} (hH : 0 ≤ H)
    (f : SpatialCoordinates d → ℝ)
    (hcell : ∀ k : OddGridIndex d m,
      ∀ x ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)),
      ∀ y ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)),
        |f x - f y| ≤ H * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha)
    (p : SpatialCoordinates d)
    (hp : p ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)))
    (i : Fin d) (t : ℝ) (hpt : p i ≤ t) (hlt : t - p i < R / (2 * (m : ℝ) + 1))
    (hq : Function.update p i t ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d))) :
    |f p - f (Function.update p i t)| ≤ 2 * H * (t - p i) ^ alpha := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ, R / (2 * (m : ℝ) + 1) = ρ := ⟨_, rfl⟩
  have hρpos : 0 < ρ := hρ ▸ by positivity
  have hRρ : R = (2 * (m : ℝ) + 1) * ρ := by
    rw [← hρ, mul_div_cancel₀ R (by positivity : (2 * (m : ℝ) + 1) ≠ 0)]
  rw [hρ] at hlt
  obtain ⟨k, hk⟩ := aux_lem_cutoffs_holder_exists_cell z hR m hp
  have hkc := (aux_lem_cutoffs_holder_mem_closure_cell z hR m k p).mp hk
  rw [hρ] at hkc
  have hpi := abs_le.mp (hkc i)
  have hδ : 0 ≤ t - p i := sub_nonneg.mpr hpt
  have hpair : ∀ (k' : OddGridIndex d m) (a b : SpatialCoordinates d),
      a ∈ closure (oddGridCell z R hR m k' : Set (SpatialCoordinates d)) →
      b ∈ closure (oddGridCell z R hR m k' : Set (SpatialCoordinates d)) →
      (∀ j, j ≠ i → a j = b j) → |a i - b i| ≤ t - p i →
      |f a - f b| ≤ H * (t - p i) ^ alpha := by
    intro k' a b ha hb hab hle
    refine (hcell k' a ha b hb).trans ?_
    rw [aux_lem_cutoffs_holder_edist_single a b i hab]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hle halpha.le) hH
  have hHδ : 0 ≤ H * (t - p i) ^ alpha := mul_nonneg hH (Real.rpow_nonneg hδ _)
  by_cases hin : t ≤ oddGridCenter z R m k i + ρ / 2
  · have hq' : Function.update p i t ∈
        closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)) := by
      apply aux_lem_cutoffs_holder_update_mem_cell z hR m hk i (fun j _ => rfl)
      rw [hρ, abs_le]; constructor <;> linarith
    have h := hpair k p _ hk hq' (fun j hj => (Function.update_of_ne hj _ _).symm)
      (by rw [Function.update_self, abs_le]; constructor <;> linarith)
    linarith
  · push Not at hin
    have hqi := abs_le.mp ((aux_lem_cutoffs_holder_mem_closure_cube z hR _).mp hq i)
    rw [Function.update_self] at hqi
    have hki : (k i).val < 2 * m := by
      have h1 : ((k i).val : ℝ) * ρ < (2 * (m : ℝ)) * ρ := by
        simp only [oddGridCenter, hρ] at hin
        linarith
      exact_mod_cast lt_of_mul_lt_mul_right h1 hρpos.le
    obtain ⟨k', hk'i, hk'j⟩ : ∃ k' : OddGridIndex d m, (k' i).val = (k i).val + 1 ∧
        ∀ j, j ≠ i → k' j = k j :=
      ⟨Function.update k i ⟨(k i).val + 1, by omega⟩, by simp,
        fun j hj => Function.update_of_ne hj _ _⟩
    have hcen : oddGridCenter z R m k' i = oddGridCenter z R m k i + ρ := by
      simp only [oddGridCenter, hk'i, hρ]; push_cast; ring
    have hμk : Function.update p i (oddGridCenter z R m k i + ρ / 2) ∈
        closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)) := by
      apply aux_lem_cutoffs_holder_update_mem_cell z hR m hk i (fun j _ => rfl)
      rw [hρ, abs_le]; constructor <;> linarith
    have hμk' : Function.update p i (oddGridCenter z R m k i + ρ / 2) ∈
        closure (oddGridCell z R hR m k' : Set (SpatialCoordinates d)) := by
      apply aux_lem_cutoffs_holder_update_mem_cell z hR m hk i hk'j
      rw [hρ, hcen, abs_le]; constructor <;> linarith
    have hqk' : Function.update p i t ∈
        closure (oddGridCell z R hR m k' : Set (SpatialCoordinates d)) := by
      apply aux_lem_cutoffs_holder_update_mem_cell z hR m hk i hk'j
      rw [hρ, hcen, abs_le]; constructor <;> linarith
    have h1 := hpair k p _ hk hμk (fun j hj => (Function.update_of_ne hj _ _).symm)
      (by rw [Function.update_self, abs_le]; constructor <;> linarith)
    have h2 := hpair k' _ _ hμk' hqk'
      (fun j hj => by rw [Function.update_of_ne hj, Function.update_of_ne hj])
      (by rw [Function.update_self, Function.update_self, abs_le]; constructor <;> linarith)
    calc |f p - f (Function.update p i t)|
        ≤ |f p - f (Function.update p i (oddGridCenter z R m k i + ρ / 2))| +
          |f (Function.update p i (oddGridCenter z R m k i + ρ / 2)) -
            f (Function.update p i t)| := abs_sub_le _ _ _
      _ ≤ 2 * H * (t - p i) ^ alpha := by linarith

/-- One-coordinate step in the closed cube, at any distance. -/
theorem aux_lem_cutoffs_holder_step {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (m : ℕ) {alpha : ℝ} (halpha : 0 < alpha) {B H : ℝ} (hB : 0 ≤ B) (hH : 0 ≤ H)
    (f : SpatialCoordinates d → ℝ)
    (hval : ∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)), |f x| ≤ B)
    (hcell : ∀ k : OddGridIndex d m,
      ∀ x ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)),
      ∀ y ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)),
        |f x - f y| ≤ H * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha)
    (p : SpatialCoordinates d)
    (hp : p ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)))
    (i : Fin d) (t : ℝ)
    (hq : Function.update p i t ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d))) :
    |f p - f (Function.update p i t)| ≤
      (2 * H + 2 * B * (R / (2 * (m : ℝ) + 1)) ^ (-alpha)) * |p i - t| ^ alpha := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ, R / (2 * (m : ℝ) + 1) = ρ := ⟨_, rfl⟩
  have hρpos : 0 < ρ := hρ ▸ by positivity
  rw [hρ]
  have hδ := abs_nonneg (p i - t)
  have hρα : 0 ≤ ρ ^ (-alpha) := Real.rpow_nonneg hρpos.le _
  have hδα : 0 ≤ |p i - t| ^ alpha := Real.rpow_nonneg hδ _
  have hHδ : 0 ≤ 2 * H * |p i - t| ^ alpha := by positivity
  have hBδ : 0 ≤ 2 * B * ρ ^ (-alpha) * |p i - t| ^ alpha := by positivity
  by_cases hbig : ρ ≤ |p i - t|
  · have h2B : |f p - f (Function.update p i t)| ≤ 2 * B := by
      have h1 := abs_le.mp (hval p hp)
      have h2 := abs_le.mp (hval _ hq)
      rw [abs_le]; constructor <;> linarith
    have hone : 1 ≤ ρ ^ (-alpha) * |p i - t| ^ alpha := by
      rw [Real.rpow_neg hρpos.le, inv_mul_eq_div,
        one_le_div (Real.rpow_pos_of_pos hρpos _)]
      exact Real.rpow_le_rpow hρpos.le hbig halpha.le
    have h3 := mul_le_mul_of_nonneg_left hone (by linarith : 0 ≤ 2 * B)
    linarith
  · push Not at hbig
    rcases le_total (p i) t with hpt | htp
    · have hδeq : |p i - t| = t - p i := by
        rw [abs_sub_comm]; exact abs_of_nonneg (sub_nonneg.mpr hpt)
      rw [hδeq] at hbig hHδ hBδ ⊢
      have h := aux_lem_cutoffs_holder_step_le z R hR m halpha hH f hcell p hp i t hpt
        (by rw [hρ]; exact hbig) hq
      linarith
    · have hδeq : |p i - t| = p i - t := abs_of_nonneg (sub_nonneg.mpr htp)
      rw [hδeq] at hbig hHδ hBδ ⊢
      have hp' : Function.update (Function.update p i t) i (p i) = p := by
        rw [Function.update_idem, Function.update_eq_self]
      have h := aux_lem_cutoffs_holder_step_le z R hR m halpha hH f hcell
        (Function.update p i t) hq i (p i) (by rw [Function.update_self]; exact htp)
        (by rw [Function.update_self, hρ]; exact hbig) (by rw [hp']; exact hp)
      rw [hp', Function.update_self, abs_sub_comm] at h
      linarith



theorem aux_lem_cutoffs_pair_bound_of_holder {d : ℕ} {alpha A : ℝ} (halpha : 0 < alpha)
    {S : Set (SpatialCoordinates d)} {f : SpatialCoordinates d → ℝ}
    (hH : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha S f) (hA : _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha S f ≤ A) :
    ∀ x ∈ S, ∀ y ∈ S,
      |f x - f y| ≤ A * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha := by
  intro x hx y hy
  by_cases hxy : x = y
  · subst hxy
    simp [Real.zero_rpow halpha.ne']
  · have hpos := aux_lem_cutoffs_holder_edist_pos hxy
    have hsup : 0 ≤ sSup {v : ℝ | ∃ x ∈ S, v = |f x|} := by
      apply Real.sSup_nonneg
      rintro v ⟨w, -, rfl⟩
      exact abs_nonneg _
    have hsemi : _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm alpha S f ≤ A := by
      unfold _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm at hA
      linarith
    have hratio : |f x - f y| / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha ≤ A :=
      (le_csSup hH ⟨x, hx, y, hy, hxy, rfl⟩).trans hsemi
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hpos alpha)).mp hratio



theorem aux_lem_cutoffs_holder_of_pair_bound {d : ℕ} {alpha B C : ℝ} (_halpha : 0 < alpha)
    (hB : 0 ≤ B) (hC : 0 ≤ C) {S : Set (SpatialCoordinates d)}
    {f : SpatialCoordinates d → ℝ}
    (hval : ∀ x ∈ S, |f x| ≤ B)
    (hpair : ∀ x ∈ S, ∀ y ∈ S,
      |f x - f y| ≤ C * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha) :
    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha S f ∧ _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha S f ≤ B + C := by
  have hratio : ∀ v ∈ _root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet alpha S f, v ≤ C := by
    rintro v ⟨x, hx, y, hy, hxy, rfl⟩
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (aux_lem_cutoffs_holder_edist_pos hxy) alpha)).mpr
      (hpair x hx y hy)
  refine ⟨⟨C, fun v hv => hratio v hv⟩, ?_⟩
  unfold _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm
  apply add_le_add
  · apply Real.sSup_le
    · rintro v ⟨x, hx, rfl⟩
      exact hval x hx
    · exact hB
  · exact Real.sSup_le hratio hC

/-- Gluing cellwise Hölder estimates on a centered odd grid of mesh `ρ` into a
global Hölder estimate on the closed cube. The global constant depends only on
the dimension, the cell constant, the sup bound and the mesh width. -/
theorem aux_lem_cutoffs_holder_glue {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (m : ℕ) {alpha : ℝ} (halpha : 0 < alpha) {B H : ℝ} (hB : 0 ≤ B) (hH : 0 ≤ H)
    (f : SpatialCoordinates d → ℝ)
    (hval : ∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)), |f x| ≤ B)
    (hcell : ∀ k : OddGridIndex d m,
      ∀ x ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)),
      ∀ y ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)),
        |f x - f y| ≤ H * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha) :
    ∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
      ∀ y ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
        |f x - f y| ≤ (d : ℝ) * (2 * H + 2 * B * (R / (2 * (m : ℝ) + 1)) ^ (-alpha)) *
          (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha := by
  intro x hx y hy
  have hstep := aux_lem_cutoffs_holder_step z R hR m halpha hB hH f hval hcell
  obtain ⟨K, hK⟩ : ∃ K, 2 * H + 2 * B * (R / (2 * (m : ℝ) + 1)) ^ (-alpha) = K := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [← hK]; positivity
  simp only [hK] at hstep
  rw [hK]
  let P : ℕ → SpatialCoordinates d := fun n l => if l.val < n then y l else x l
  have hP0 : P 0 = x := by funext l; simp [P]
  have hPd : P d = y := by funext l; simp [P, l.isLt]
  have hPs : ∀ n (hn : n < d), P (n + 1) = Function.update (P n) ⟨n, hn⟩ (y ⟨n, hn⟩) := by
    intro n hn
    funext l
    by_cases hl : l = ⟨n, hn⟩
    · subst hl; simp [P]
    · rw [Function.update_of_ne hl]
      have hl' : l.val ≠ n := fun h => hl (Fin.ext h)
      simp only [P]
      by_cases h1 : l.val < n
      · rw [ite_eq_left h1, ite_eq_left (by omega)]
      · rw [ite_eq_right h1, ite_eq_right (by omega)]
  have hPn : ∀ n (hn : n < d), P n ⟨n, hn⟩ = x ⟨n, hn⟩ := by
    intro n hn; simp [P]
  have hPmem : ∀ n, P n ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)) := by
    intro n
    rw [aux_lem_cutoffs_holder_mem_closure_cube] at hx hy ⊢
    intro l
    simp only [P]
    split_ifs
    · exact hy l
    · exact hx l
  have htel : f x - f y = ∑ n ∈ Finset.range d, (f (P n) - f (P (n + 1))) := by
    have h := Finset.sum_range_sub' (fun n => f (P n)) d
    simp only [hP0, hPd] at h
    exact h.symm
  calc |f x - f y| ≤ ∑ n ∈ Finset.range d, |f (P n) - f (P (n + 1))| := by
        rw [htel]; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.range d, K * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha := by
        apply Finset.sum_le_sum
        intro n hn
        have hn' : n < d := Finset.mem_range.mp hn
        rw [hPs n hn']
        refine (hstep (P n) (hPmem n) ⟨n, hn'⟩ (y ⟨n, hn'⟩) ?_).trans ?_
        · rw [← hPs n hn']; exact hPmem (n + 1)
        · rw [hPn n hn']
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _)
            (aux_lem_cutoffs_holder_coord_le_edist x y _) halpha.le) hK0
    _ = (d : ℝ) * K * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc]

/-- Arzelà–Ascoli: a uniformly bounded, uniformly Hölder sequence on a compact
set has a uniformly convergent subsequence with a continuous limit. -/
theorem aux_lem_cutoffs_subseq_uniform {d : ℕ} (K : Set (SpatialCoordinates d))
    (hK : IsCompact K) (u : ℕ → SpatialCoordinates d → ℝ)
    (hcont : ∀ n, ContinuousOn (u n) K) {B C alpha : ℝ} (halpha : 0 < alpha) (hC : 0 ≤ C)
    (hbdd : ∀ n, ∀ x ∈ K, |u n x| ≤ B)
    (hHol : ∀ n, ∀ x ∈ K, ∀ y ∈ K,
      |u n x - u n y| ≤ C * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ g : SpatialCoordinates d → ℝ, ContinuousOn g K ∧
      TendstoUniformlyOn (fun n => u (σ n)) g atTop K := by
  classical
  have : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  let F : ℕ → BoundedContinuousFunction ↥K ℝ := fun n =>
    BoundedContinuousFunction.mkOfCompact
      (ContinuousMap.mk (K.domRestrict (u n)) (ContinuousOn.domRestrict (hcont n)))
  let A : Set (BoundedContinuousFunction ↥K ℝ) := Set.range F
  have hA : ∀ (g : BoundedContinuousFunction ↥K ℝ) (x : ↥K), g ∈ A →
      g x ∈ Set.Icc (-B) B := by
    rintro g x ⟨n, rfl⟩
    change u n ↑x ∈ Set.Icc (-B) B
    exact abs_le.mp (hbdd n ↑x x.property)
  have heq : Equicontinuous ((↑) : A → ↥K → ℝ) := by
    refine Metric.equicontinuous_of_continuity_modulus
      (fun t : ℝ => C * (Real.sqrt d * t) ^ alpha) ?_ _ ?_
    · have hlin : Tendsto (fun t : ℝ => Real.sqrt d * t) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_const.mul continuous_id).tendsto (0 : ℝ)
          (f := fun t : ℝ => Real.sqrt d * t)
      have hpow := (Real.continuousAt_rpow_const 0 alpha (Or.inr halpha.le)).tendsto
      rw [Real.zero_rpow halpha.ne'] at hpow
      simpa using (hpow.comp hlin).const_mul C
    · intro x y i
      obtain ⟨n, hn⟩ := i.property
      rw [← hn]
      change dist (u n ↑x) (u n ↑y) ≤ C * (Real.sqrt d * dist x y) ^ alpha
      rw [Real.dist_eq]
      refine (hHol n ↑x x.property ↑y y.property).trans ?_
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Real.sqrt_nonneg _)
        (aux_lem_cutoffs_holder_edist_le_dist (x : SpatialCoordinates d) y) halpha.le) hC
  have hcomp : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli (Set.Icc (-B) B) isCompact_Icc A hA heq
  obtain ⟨a, -, τ, hτ, htend⟩ :=
    hcomp.tendsto_subseq (x := F) (fun n => subset_closure ⟨n, rfl⟩)
  let g : SpatialCoordinates d → ℝ := fun x => if hx : x ∈ K then a ⟨x, hx⟩ else 0
  refine ⟨τ, hτ, g, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have hgr : K.domRestrict g = ⇑a := by
      funext x
      change (if hx : (x : SpatialCoordinates d) ∈ K then a ⟨x, hx⟩ else 0) = a x
      exact dite_eq_left x.property
    change Continuous (K.domRestrict g)
    rw [hgr]
    exact a.continuous
  · rw [Metric.tendstoUniformlyOn_iff]
    intro eps heps
    obtain ⟨k0, hk0⟩ := Metric.tendsto_atTop.mp htend eps heps
    refine Filter.eventually_atTop.mpr ⟨k0, fun k hk x hx => ?_⟩
    have hpt : dist (F (τ k) ⟨x, hx⟩) (a ⟨x, hx⟩) ≤ dist (F (τ k)) a :=
      BoundedContinuousFunction.dist_coe_le_dist _
    have hgx : g x = a ⟨x, hx⟩ := dite_eq_left hx
    have hFx : F (τ k) ⟨x, hx⟩ = u (τ k) x := rfl
    rw [hFx] at hpt
    rw [hgx, dist_comm]
    exact lt_of_le_of_lt hpt (hk0 k hk)


/-! ### Geom helpers of the mesh/collar step -/

/-- The frontier of the sup-cube is the sup-sphere. -/
theorem aux_lem_cutoffs_geom_frontier_eq {d : ℕ} (z : SpatialCoordinates d) (R : ℝ)
    (hR : 0 < R) :
    frontier (centeredCube z R hR : Set (SpatialCoordinates d)) = Metric.sphere z (R / 2) := by
  change frontier (Metric.ball z (R / 2)) = _
  exact frontier_ball z (half_pos hR).ne'

/-- The closure of the sup-cube is the closed sup-ball. -/
theorem aux_lem_cutoffs_geom_closure_eq {d : ℕ} (z : SpatialCoordinates d) (R : ℝ)
    (hR : 0 < R) :
    closure (centeredCube z R hR : Set (SpatialCoordinates d)) =
      Metric.closedBall z (R / 2) := by
  change closure (Metric.ball z (R / 2)) = _
  exact closure_ball z (half_pos hR).ne'

/-- Coordinate description of the closure of an odd-grid cell. -/
theorem aux_lem_cutoffs_geom_mem_closure_cell {d : ℕ} (z : SpatialCoordinates d)
    (R : ℝ) (hR : 0 < R) (m : ℕ) (k : OddGridIndex d m) (x : SpatialCoordinates d) :
    x ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)) ↔
      ∀ i, |x i - (z i + ((k i).val - (m : ℝ)) * (R / (2 * (m : ℝ) + 1)))| ≤
        (R / (2 * (m : ℝ) + 1)) / 2 := by
  have hρ : 0 < R / (2 * (m : ℝ) + 1) / 2 := by positivity
  change x ∈ closure (Metric.ball (oddGridCenter z R m k) (R / (2 * (m : ℝ) + 1) / 2)) ↔ _
  rw [closure_ball _ hρ.ne', Metric.mem_closedBall, dist_pi_le_iff hρ.le]
  simp only [Real.dist_eq, oddGridCenter]

/-- Distance to the frontier is at most the distance to any coordinate face. -/
theorem aux_lem_cutoffs_infDist_le_face {d : ℕ} (z : SpatialCoordinates d) (R : ℝ)
    (hR : 0 < R) (x : SpatialCoordinates d)
    (hx : x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d))) (i : Fin d) :
    Metric.infDist x (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) ≤
      R / 2 - |x i - z i| := by
  have hR2 : 0 < R / 2 := half_pos hR
  rw [aux_lem_cutoffs_geom_closure_eq] at hx
  have hxj : ∀ j, |x j - z j| ≤ R / 2 := by
    intro j
    have := (dist_pi_le_iff hR2.le).mp (Metric.mem_closedBall.mp hx) j
    rwa [Real.dist_eq] at this
  obtain ⟨s, hsabs, hgap⟩ : ∃ s : ℝ, |s| = R / 2 ∧ |x i - (z i + s)| = R / 2 - |x i - z i| := by
    have hxi := abs_le.mp (hxj i)
    rcases le_total 0 (x i - z i) with h | h
    · refine ⟨R / 2, abs_of_pos hR2, ?_⟩
      rw [abs_of_nonneg h, abs_of_nonpos (by linarith)]
      ring
    · refine ⟨-(R / 2), by rw [abs_neg, abs_of_pos hR2], ?_⟩
      rw [abs_of_nonpos h, abs_of_nonneg (by linarith)]
      ring
  let y : SpatialCoordinates d := Function.update x i (z i + s)
  have hyF : y ∈ frontier (centeredCube z R hR : Set (SpatialCoordinates d)) := by
    rw [aux_lem_cutoffs_geom_frontier_eq, Metric.mem_sphere]
    apply le_antisymm
    · refine (dist_pi_le_iff hR2.le).mpr fun j => ?_
      rw [Real.dist_eq]
      by_cases hj : j = i
      · rw [hj]
        simp [y, hsabs]
      · simp only [y, Function.update_of_ne hj]
        exact hxj j
    · have := dist_le_pi_dist y z i
      simpa [y, Real.dist_eq, hsabs] using this
  have hgap0 : 0 ≤ R / 2 - |x i - z i| := by
    rw [← hgap]
    exact abs_nonneg _
  calc Metric.infDist x (frontier (centeredCube z R hR : Set (SpatialCoordinates d)))
      ≤ dist x y := Metric.infDist_le_dist_of_mem hyF
    _ ≤ R / 2 - |x i - z i| := by
      refine (dist_pi_le_iff hgap0).mpr fun j => ?_
      rw [Real.dist_eq]
      by_cases hj : j = i
      · rw [hj]
        simp [y, hgap]
      · simp only [y, Function.update_of_ne hj, sub_self, abs_zero]
        exact hgap0

/-- Distance to the frontier is at least the gap to the sup-sphere. -/
theorem aux_lem_cutoffs_le_infDist {d : ℕ} (hd : 1 ≤ d) (z : SpatialCoordinates d) (R : ℝ)
    (hR : 0 < R) (x : SpatialCoordinates d) :
    R / 2 - dist x z ≤
      Metric.infDist x (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) := by
  have hne := aux_cutoffs_cube_frontier_nonempty d hd z R hR
  refine (Metric.le_infDist hne).mpr fun p hp => ?_
  rw [aux_lem_cutoffs_geom_frontier_eq, Metric.mem_sphere] at hp
  have := dist_triangle p x z
  rw [dist_comm p x] at this
  linarith

/-- A real offset of at most `(m - 5/2)` mesh widths is within half a mesh width
of an interior label with at least three labels to spare on each side. -/
theorem aux_lem_cutoffs_geom_label (m : ℕ) (ρ t : ℝ) (hρ : 0 < ρ)
    (ht : |t| ≤ ((m : ℝ) - 5 / 2) * ρ) :
    ∃ n : ℕ, 3 ≤ n ∧ n + 3 ≤ 2 * m ∧ |t - ((n : ℝ) - m) * ρ| ≤ ρ / 2 := by
  have hm : (5 / 2 : ℝ) ≤ m := by
    by_contra h
    push Not at h
    have : ((m : ℝ) - 5 / 2) * ρ < 0 := mul_neg_of_neg_of_pos (by linarith) hρ
    linarith [abs_nonneg t]
  have hm3 : 3 ≤ m := by
    by_contra h
    push Not at h
    have : (m : ℝ) ≤ 2 := by exact_mod_cast (by omega : m ≤ 2)
    linarith
  set v : ℝ := t / ρ with hv
  have htv : t = v * ρ := by rw [hv]; field_simp
  have hvabs : |v| ≤ (m : ℝ) - 5 / 2 := by
    rw [hv, abs_div, abs_of_pos hρ, div_le_iff₀ hρ]
    exact ht
  have hvl := (abs_le.mp hvabs).1
  have hvu := (abs_le.mp hvabs).2
  have key : ∀ n : ℕ, |v - ((n : ℝ) - m)| ≤ 1 / 2 → |t - ((n : ℝ) - m) * ρ| ≤ ρ / 2 := by
    intro n hn
    rw [htv, ← sub_mul, abs_mul, abs_of_pos hρ]
    calc |v - ((n : ℝ) - m)| * ρ ≤ 1 / 2 * ρ := mul_le_mul_of_nonneg_right hn hρ.le
      _ = ρ / 2 := by ring
  have hnn : 0 ≤ v + m + 1 / 2 := by linarith
  have hfl := Nat.floor_le hnn
  have hfu := Nat.lt_floor_add_one (v + m + 1 / 2)
  set n₀ : ℕ := ⌊v + m + 1 / 2⌋₊ with hn₀
  have hn₀3 : 3 ≤ n₀ := by
    have : (2 : ℝ) < n₀ := by linarith
    have : 2 < n₀ := by exact_mod_cast this
    omega
  by_cases hcase : n₀ + 3 ≤ 2 * m
  · refine ⟨n₀, hn₀3, hcase, key n₀ ?_⟩
    rw [abs_le]
    constructor <;> linarith
  · refine ⟨2 * m - 3, by omega, by omega, key _ ?_⟩
    have hcast : ((2 * m - 3 : ℕ) : ℝ) = 2 * (m : ℝ) - 3 := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    have hge : (2 * m - 2 : ℕ) ≤ n₀ := by omega
    have hge' : 2 * (m : ℝ) - 2 ≤ n₀ := by
      have := (Nat.cast_le (α := ℝ)).mpr hge
      rw [Nat.cast_sub (by omega)] at this
      push_cast at this
      linarith
    rw [hcast, abs_le]
    constructor <;> linarith

/-- A cell whose labels all stay three steps away from both ends has its whole
closure inside the cube at distance at least three mesh widths from the frontier. -/
theorem aux_lem_cutoffs_geom_good_closure {d : ℕ} (hd : 1 ≤ d) (z : SpatialCoordinates d)
    (R : ℝ) (hR : 0 < R) (m : ℕ) (k : OddGridIndex d m)
    (hk : ∀ i, 3 ≤ (k i).val ∧ (k i).val + 3 ≤ 2 * m) :
    ∀ y' ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)),
      y' ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
      3 * (R / (2 * (m : ℝ) + 1)) ≤
        Metric.infDist y' (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) := by
  intro y hy
  have hc := aux_cutoffs_closed_cell_coordinate z R hR m k y hy
  have h2 := aux_lem_cutoffs_le_infDist hd z R hR y
  have hm1 : (0 : ℝ) < 2 * m + 1 := by positivity
  have hRρ : R = (2 * (m : ℝ) + 1) * (R / (2 * (m : ℝ) + 1)) := by field_simp
  have hρ : 0 < R / (2 * (m : ℝ) + 1) := div_pos hR hm1
  generalize R / (2 * (m : ℝ) + 1) = ρ at hc hRρ hρ ⊢
  have hm3 : (3 : ℝ) ≤ m := by
    have := hk ⟨0, hd⟩
    exact_mod_cast (by omega : 3 ≤ m)
  have hyi : ∀ i, |y i - z i| ≤ ((m : ℝ) - 5 / 2) * ρ := by
    intro i
    have h3 : (3 : ℝ) ≤ (k i).val := by exact_mod_cast (hk i).1
    have h3' : ((k i).val : ℝ) + 3 ≤ 2 * m := by exact_mod_cast (hk i).2
    have hci := abs_le.mp (hc i)
    have p1 : 0 ≤ (((k i).val : ℝ) - 3) * ρ := mul_nonneg (by linarith) hρ.le
    have p2 : 0 ≤ (2 * (m : ℝ) - (k i).val - 3) * ρ := mul_nonneg (by linarith) hρ.le
    rw [abs_le]
    constructor <;> linarith
  have hdist : dist y z ≤ ((m : ℝ) - 5 / 2) * ρ :=
    (dist_pi_le_iff (mul_nonneg (by linarith) hρ.le)).mpr fun i => by
      rw [Real.dist_eq]
      exact hyi i
  refine ⟨?_, by linarith⟩
  change y ∈ Metric.ball z (R / 2)
  rw [Metric.mem_ball]
  linarith

/-- A point within one mesh width of the frontier lies in the closure of a
boundary-layer cell, all of whose points are within one mesh width. -/
theorem aux_lem_cutoffs_zero_layer_cell {d : ℕ} (hd : 1 ≤ d) (z : SpatialCoordinates d)
    (R : ℝ) (hR : 0 < R) (m : ℕ) (x : SpatialCoordinates d)
    (hx : x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hdist : Metric.infDist x (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) ≤
      R / (2 * (m : ℝ) + 1)) :
    ∃ k : OddGridIndex d m,
      x ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)) ∧
      ∀ y ∈ (oddGridCell z R hR m k : Set (SpatialCoordinates d)),
        Metric.infDist y (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) ≤
          R / (2 * (m : ℝ) + 1) := by
  have hxcl : x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)) := subset_closure hx
  have h2 := aux_lem_cutoffs_le_infDist hd z R hR x
  have hxQ : ∀ j, |x j - z j| < R / 2 := by
    intro j
    have hb : dist x z < R / 2 := hx
    have := (dist_pi_lt_iff (half_pos hR)).mp hb j
    rwa [Real.dist_eq] at this
  obtain ⟨i, hi⟩ : ∃ i, R / 2 - R / (2 * (m : ℝ) + 1) ≤ |x i - z i| := by
    by_contra hcon
    push Not at hcon
    have hpos : 0 < R / 2 - R / (2 * (m : ℝ) + 1) :=
      lt_of_le_of_lt (abs_nonneg _) (hcon ⟨0, hd⟩)
    have : dist x z < R / 2 - R / (2 * (m : ℝ) + 1) :=
      (dist_pi_lt_iff hpos).mpr fun j => by rw [Real.dist_eq]; exact hcon j
    linarith
  obtain ⟨e, he1, he2⟩ : ∃ e : Fin (2 * m + 1),
      |x i - (z i + ((e.val : ℝ) - m) * (R / (2 * (m : ℝ) + 1)))| ≤
        (R / (2 * (m : ℝ) + 1)) / 2 ∧
      ∀ t : ℝ, z i + ((e.val : ℝ) - m) * (R / (2 * (m : ℝ) + 1)) -
          (R / (2 * (m : ℝ) + 1)) / 2 < t →
        t < z i + ((e.val : ℝ) - m) * (R / (2 * (m : ℝ) + 1)) +
          (R / (2 * (m : ℝ) + 1)) / 2 →
        R / 2 - R / (2 * (m : ℝ) + 1) < |t - z i| := by
    have hm1 : (0 : ℝ) < 2 * m + 1 := by positivity
    have hRρ : R = (2 * (m : ℝ) + 1) * (R / (2 * (m : ℝ) + 1)) := by field_simp
    have hxi := hxQ i
    generalize R / (2 * (m : ℝ) + 1) = ρ at hi hRρ ⊢
    rcases le_total 0 (x i - z i) with h | h
    · rw [abs_of_nonneg h] at hi hxi
      refine ⟨⟨2 * m, by omega⟩, ?_, ?_⟩
      · simp only [Nat.cast_mul, Nat.cast_ofNat]
        rw [abs_le]
        constructor <;> linarith
      · intro t ht1 _
        simp only [Nat.cast_mul, Nat.cast_ofNat] at ht1
        exact lt_of_lt_of_le (by linarith) (le_abs_self (t - z i))
    · rw [abs_of_nonpos h] at hi hxi
      refine ⟨⟨0, by omega⟩, ?_, ?_⟩
      · simp only [Nat.cast_zero]
        rw [abs_le]
        constructor <;> linarith
      · intro t _ ht2
        simp only [Nat.cast_zero] at ht2
        exact lt_of_lt_of_le (by linarith) (neg_le_abs (t - z i))
  have hxcov := hxcl
  rw [← oddGridCell_closure_iUnion_eq_closure_centeredCube z hR m, Set.mem_iUnion] at hxcov
  obtain ⟨k, hk⟩ := hxcov
  refine ⟨Function.update k i e, ?_, ?_⟩
  · rw [aux_lem_cutoffs_geom_mem_closure_cell]
    intro j
    by_cases hj : j = i
    · rw [hj, Function.update_self]
      exact he1
    · rw [Function.update_of_ne hj]
      exact (aux_lem_cutoffs_geom_mem_closure_cell z R hR m k x).mp hk j
  · intro y hy
    have hyQ := oddGridCell_subset z hR m _ hy
    have h1 := aux_lem_cutoffs_infDist_le_face z R hR y (subset_closure hyQ) i
    have hyc := (mem_oddGridCell z hR m _ y).mp hy i
    rw [Function.update_self] at hyc
    have := he2 (y i) hyc.1 hyc.2
    linarith

/-- A point at distance at least three mesh widths from the frontier lies in
the closure of a cell whose closure stays inside the cube at distance at least
three mesh widths. -/
theorem aux_lem_cutoffs_one_region_cell {d : ℕ} (hd : 1 ≤ d) (z : SpatialCoordinates d)
    (R : ℝ) (hR : 0 < R) (m : ℕ) (x : SpatialCoordinates d)
    (hx : x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hdist : 3 * (R / (2 * (m : ℝ) + 1)) ≤
      Metric.infDist x (frontier (centeredCube z R hR : Set (SpatialCoordinates d)))) :
    ∃ k : OddGridIndex d m,
      x ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)) ∧
      ∀ y ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)),
        y ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
        3 * (R / (2 * (m : ℝ) + 1)) ≤
          Metric.infDist y (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) := by
  have hxcl : x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)) := subset_closure hx
  have hm1 : (0 : ℝ) < 2 * m + 1 := by positivity
  have hρ : 0 < R / (2 * (m : ℝ) + 1) := div_pos hR hm1
  have hRρ : R = (2 * (m : ℝ) + 1) * (R / (2 * (m : ℝ) + 1)) := by field_simp
  have hxi : ∀ i, |x i - z i| ≤ ((m : ℝ) - 5 / 2) * (R / (2 * (m : ℝ) + 1)) := by
    intro i
    have := aux_lem_cutoffs_infDist_le_face z R hR x hxcl i
    linarith
  choose n hn3 hn3' hnx using fun i => aux_lem_cutoffs_geom_label m _ (x i - z i) hρ (hxi i)
  let k : OddGridIndex d m := fun i => ⟨n i, by have := hn3' i; omega⟩
  refine ⟨k, ?_, aux_lem_cutoffs_geom_good_closure hd z R hR m k fun i => ⟨hn3 i, hn3' i⟩⟩
  rw [aux_lem_cutoffs_geom_mem_closure_cell]
  intro i
  show |x i - (z i + (((n i : ℕ) : ℝ) - m) * (R / (2 * (m : ℝ) + 1)))| ≤ _
  rw [show x i - (z i + (((n i : ℕ) : ℝ) - m) * (R / (2 * (m : ℝ) + 1))) =
    x i - z i - (((n i : ℕ) : ℝ) - m) * (R / (2 * (m : ℝ) + 1)) by ring]
  exact hnx i

/-- An open cell containing a point strictly deeper than three mesh widths has
its whole closure inside the cube at distance at least three mesh widths. -/
theorem aux_lem_cutoffs_deep_cell {d : ℕ} (hd : 1 ≤ d) (z : SpatialCoordinates d)
    (R : ℝ) (hR : 0 < R) (m : ℕ) (k : OddGridIndex d m) (y : SpatialCoordinates d)
    (hy : y ∈ (oddGridCell z R hR m k : Set (SpatialCoordinates d)))
    (hdist : 3 * (R / (2 * (m : ℝ) + 1)) <
      Metric.infDist y (frontier (centeredCube z R hR : Set (SpatialCoordinates d)))) :
    ∀ y' ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)),
      y' ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
      3 * (R / (2 * (m : ℝ) + 1)) ≤
        Metric.infDist y' (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) := by
  refine aux_lem_cutoffs_geom_good_closure hd z R hR m k fun i => ?_
  have hyQ := oddGridCell_subset z hR m k hy
  have h1 := aux_lem_cutoffs_infDist_le_face z R hR y (subset_closure hyQ) i
  have hc := (mem_oddGridCell z hR m k y).mp hy i
  have hm1 : (0 : ℝ) < 2 * m + 1 := by positivity
  have hρ : 0 < R / (2 * (m : ℝ) + 1) := div_pos hR hm1
  have hRρ : R = (2 * (m : ℝ) + 1) * (R / (2 * (m : ℝ) + 1)) := by field_simp
  generalize R / (2 * (m : ℝ) + 1) = ρ at hc hρ hRρ hdist
  have hlt1 : ((k i).val : ℝ) * ρ < (2 * m - 2) * ρ := by
    have := le_abs_self (y i - z i)
    linarith [hc.1]
  have hlt2 : 2 * ρ < ((k i).val : ℝ) * ρ := by
    have := neg_abs_le (y i - z i)
    linarith [hc.2]
  have hk1 : ((k i).val : ℝ) + 2 < 2 * m := by
    have := lt_of_mul_lt_mul_right hlt1 hρ.le
    linarith
  have hk2 : (2 : ℝ) < (k i).val := lt_of_mul_lt_mul_right hlt2 hρ.le
  have hk1' : (k i).val + 2 < 2 * m := by exact_mod_cast hk1
  have hk2' : 2 < (k i).val := by exact_mod_cast hk2
  omega

/-- A smooth collar datum vanishing within `ρ` of the frontier inside the cube
becomes a smooth compactly supported function after zero extension off the cube. -/
theorem aux_lem_cutoffs_collar_indicator_smooth {d : ℕ} (z : SpatialCoordinates d)
    (R : ℝ) (hR : 0 < R) (rho : ℝ) (hrho : 0 < rho)
    (thetaR : SpatialCoordinates d → ℝ) (hs : ContDiff ℝ ∞ thetaR)
    (hzero : ∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
      Metric.infDist x (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) ≤ rho →
        thetaR x = 0) :
    ContDiff ℝ ∞ ((centeredCube z R hR : Set (SpatialCoordinates d)).indicator thetaR) ∧
      HasCompactSupport ((centeredCube z R hR : Set (SpatialCoordinates d)).indicator thetaR) ∧
      tsupport ((centeredCube z R hR : Set (SpatialCoordinates d)).indicator thetaR) ⊆
        (centeredCube z R hR : Set (SpatialCoordinates d)) := by
  set Q : Set (SpatialCoordinates d) := (centeredCube z R hR : Set (SpatialCoordinates d))
    with hQ
  have hQopen : IsOpen Q := (centeredCube z R hR).isOpen
  have hsupp : tsupport (Q.indicator thetaR) ⊆ Q := by
    have hK : IsClosed (closure Q ∩ {y | rho ≤ Metric.infDist y (frontier Q)}) :=
      isClosed_closure.inter (isClosed_le continuous_const (Metric.continuous_infDist_pt _))
    have h1 : Function.support (Q.indicator thetaR) ⊆
        closure Q ∩ {y | rho ≤ Metric.infDist y (frontier Q)} := by
      intro y hy
      rw [Function.mem_support] at hy
      have hyQ : y ∈ Q := by
        by_contra h
        exact hy (Set.indicator_of_notMem h _)
      rw [Set.indicator_of_mem hyQ] at hy
      refine ⟨subset_closure hyQ, ?_⟩
      by_contra h
      exact hy (hzero y hyQ (le_of_lt (not_le.mp h)))
    have h2 : closure Q ∩ {y | rho ≤ Metric.infDist y (frontier Q)} ⊆ Q := by
      rintro y ⟨hyc, hyd⟩
      by_contra hyQ
      have hyF : y ∈ frontier Q := ⟨hyc, by rwa [hQopen.interior_eq]⟩
      rw [mem_ofPred_eq, Metric.infDist_zero_of_mem hyF] at hyd
      linarith
    exact (closure_minimal h1 hK).trans h2
  refine ⟨?_, ?_, hsupp⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ Q
    · have hev : Q.indicator thetaR =ᶠ[𝓝 x] thetaR :=
        Filter.eventually_of_mem (hQopen.mem_nhds hx) fun y hy => Set.indicator_of_mem hy _
      exact hs.contDiffAt.congr_of_eventuallyEq hev
    · have hev : Q.indicator thetaR =ᶠ[𝓝 x] fun _ => 0 :=
        notMem_tsupport_iff_eventuallyEq.mp fun h => hx (hsupp h)
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hcpt : IsCompact (closure Q) := by
      rw [hQ]
      change IsCompact (closure (Metric.ball z (R / 2)))
      exact Metric.isBounded_ball.isCompact_closure
    exact hcpt.of_isClosed_subset (isClosed_tsupport _) (hsupp.trans subset_closure)


/-! ### Mesh helpers of the mesh/collar step -/

/-- A zero-trace difference transfers to a datum with the same values on the
cell and almost everywhere the same weak gradient there. -/
theorem aux_lem_cutoffs_traceDiff_congr {d : ℕ} {W : Set (SpatialCoordinates d)}
    (hW : IsOpen W) {u h h' : H1Function W}
    (htr : HasZeroTraceDifferenceOn W u h)
    (hfun : ∀ x ∈ W, h.toFun x = h'.toFun x)
    (hgrad : h.grad =ᵐ[volume.restrict W] h'.grad) :
    HasZeroTraceDifferenceOn W u h' := by
  obtain ⟨w, hwv, hwg⟩ := htr
  have hmW : ∀ᵐ x ∂(volume.restrict W), x ∈ W := ae_restrict_mem hW.measurableSet
  have hvae : (fun x => u.toFun x - h'.toFun x) =ᵐ[volume.restrict W]
      w.toH1Function.toFun := by
    filter_upwards [hmW] with x hx
    rw [hwv x, ← hfun x hx]
    ring
  have hgae : (fun x => u.grad x - h'.grad x) =ᵐ[volume.restrict W]
      w.toH1Function.grad := by
    filter_upwards [hgrad] with x hx
    rw [hwg x, hx]
    abel
  have hgae_i : ∀ i : Fin d, (fun x => (u.grad x - h'.grad x) i) =ᵐ[volume.restrict W]
      (fun x => w.toH1Function.grad x i) := by
    intro i
    filter_upwards [hgae] with x hx
    rw [hx]
  let w' : H10Function W :=
    { toFun := fun x => u.toFun x - h'.toFun x
      grad := fun x => u.grad x - h'.grad x
      memL2 := (w.toH1Function.memL2).ae_eq hvae.symm
      gradMemL2 := fun i => (w.toH1Function.gradMemL2 i).ae_eq (hgae_i i).symm
      hasWeakGradient := by
        intro i φ hφ hφc hφs
        have h1 := w.toH1Function.hasWeakGradient i φ hφ hφc hφs
        have e1 : ∫ x in W, (u.toFun x - h'.toFun x) * (fderiv ℝ φ x) (basisVec i) =
            ∫ x in W, w.toH1Function.toFun x * (fderiv ℝ φ x) (basisVec i) := by
          apply integral_congr_ae
          filter_upwards [hvae] with x hx
          rw [hx]
        have e2 : ∫ x in W, (u.grad x - h'.grad x) i * φ x =
            ∫ x in W, w.toH1Function.grad x i * φ x := by
          apply integral_congr_ae
          filter_upwards [hgae_i i] with x hx
          rw [hx]
        rw [e1, e2]
        exact h1
      approx := w.approx
      approx_smooth := w.approx_smooth
      approx_hasCompactSupport := w.approx_hasCompactSupport
      approx_support_subset := w.approx_support_subset
      tendsto_approx := by
        refine (w.tendsto_approx).congr (fun n => ?_)
        apply eLpNorm_congr_ae
        filter_upwards [hvae] with x hx
        rw [hx]
      tendsto_approx_grad := by
        intro i
        refine (w.tendsto_approx_grad i).congr (fun n => ?_)
        apply eLpNorm_congr_ae
        filter_upwards [hgae_i i] with x hx
        rw [hx] }
  refine ⟨w', fun x => ?_, fun x => ?_⟩
  · change u.toFun x = h'.toFun x + (u.toFun x - h'.toFun x)
    ring
  · change u.grad x = h'.grad x + (u.grad x - h'.grad x)
    abel

/-- A continuous positive function has positive bounds on a compact set. -/
theorem aux_lem_cutoffs_pos_bounds {d : ℕ} (a : SpatialCoordinates d → ℝ)
    (ha : Continuous a) (hpos : ∀ x, 0 < a x) (K : Set (SpatialCoordinates d))
    (hK : IsCompact K) :
    ∃ lam Lam : ℝ, 0 < lam ∧ ∀ x ∈ K, lam ≤ a x ∧ a x ≤ Lam := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨1, 1, one_pos, fun x hx => by rw [hKe] at hx; exact absurd hx (notMem_empty x)⟩
  · obtain ⟨xm, hxm, hmin⟩ := hK.exists_isMinOn hKne ha.continuousOn
    obtain ⟨xM, hxM, hmax⟩ := hK.exists_isMaxOn hKne ha.continuousOn
    exact ⟨a xm, a xM, hpos xm, fun x hx => ⟨hmin hx, hmax hx⟩⟩

/-- The finite-cutoff coefficient is continuous and positive. -/
theorem aux_lem_cutoffs_cutoffCoefficient_cont_pos {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ) :
    Continuous (cutoffCoefficient M H om N) ∧ ∀ x, 0 < cutoffCoefficient M H om N x := by
  refine ⟨?_, fun x => ?_⟩
  · refine continuous_const.mul (Real.continuous_exp.comp ?_)
    exact Continuous.sub
      (Continuous.add (H om).continuous
        (continuous_finsetSum _ fun j _ => (om (-(Int.ofNat j))).continuous))
      continuous_const
  · exact mul_pos (inv_pos.2 (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _)

/-- The normalized positive coefficient equals the raw cutoff coefficient a.e. -/
theorem aux_lem_cutoffs_positiveCoefficient_ae {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ((_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H om N z hr).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        cutoffCoefficient M H om N := by
  have h1 := @normalizedContinuousPositiveCoefficient_coeFn d (centeredCube z r hr)
    (closedCube z r hr) ⟨centeredCube_subset_closedCube z hr⟩
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM M H om N z hr) (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM_pos M H om N z hr)
    1 one_pos
  filter_upwards [h1, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx hxm
  unfold _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient
  rw [hx hxm, div_one]
  rfl

theorem aux_lem_cutoffs_cc_harmonic_ae_abs
    {d : ℕ} [NeZero d] (W : Set (SpatialCoordinates d))
    (a : SpatialCoordinates d → ℝ) (lam Lam : ℝ)
    (hWdom : IsOpenBoundedConvexDomain W) (hlam : 0 < lam)
    (ha : Continuous a)
    (habounds : ∀ x ∈ W, lam ≤ a x ∧ a x ≤ Lam)
    (φ u : H1Function W)
    (hφupper : ∀ y, φ.toFun y ≤ 1)
    (hφlower : ∀ y, -φ.toFun y ≤ 0)
    (hu : IsWeaklyHarmonicOn a W u)
    (htrace : HasZeroTraceDifferenceOn W u φ) :
    ∀ᵐ y ∂(volume.restrict W), 0 ≤ u.toFun y ∧ u.toFun y ≤ 1 := by
  have hWopen : IsOpen W := hWdom.1
  have hameas : AEStronglyMeasurable a (volumeMeasureOn W) :=
    ha.aestronglyMeasurable.restrict
  have hbounds : ∀ᵐ y ∂(volumeMeasureOn W), lam ≤ a y ∧ a y ≤ Lam := by
    filter_upwards [ae_restrict_mem hWopen.measurableSet] with y hy
    exact habounds y hy
  obtain ⟨w, hwval, hwgrad⟩ := htrace
  have hdiff : MemH10 W (fun y => u.toFun y - φ.toFun y) := by
    refine ⟨w, ?_⟩
    funext y
    rw [hwval y]
    ring
  have hdiffneg : MemH10 W (fun y => (-u).toFun y - (-φ).toFun y) := by
    rcases Homogenization.memH10_neg hdiff with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    funext y
    have hvy := congrFun hv y
    calc
      v.toFun y = -(u.toFun y - φ.toFun y) := by
        simpa only [Homogenization.H1Function.neg_toFun] using hvy
      _ = (-u).toFun y - (-φ).toFun y := by
        simp only [Homogenization.H1Function.neg_toFun]
        ring
  have hφlower' : ∀ y, (-φ).toFun y ≤ 0 := by
    intro y
    simpa only [Homogenization.H1Function.neg_toFun] using hφlower y
  have hupper :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.hasBoundaryUpperBoundOn_of_datum_le
      hWdom hdiff hφupper
  have hlower :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.hasBoundaryUpperBoundOn_of_datum_le
      hWdom hdiffneg hφlower'
  have haeupper :=
    SubdiffusiveProcess.CoarseGrainingVocab.ae_le_of_isWeaklyHarmonicOn
      hWdom hlam hameas hbounds hu hupper
  have haelower :=
    SubdiffusiveProcess.CoarseGrainingVocab.ae_le_of_isWeaklyHarmonicOn
      hWdom hlam hameas hbounds (SubdiffusiveProcess.CoarseGrainingVocab.isWeaklyHarmonicOn_neg hu) hlower
  filter_upwards [haeupper, haelower] with y hyupper hylower
  have hylower' : -u.toFun y ≤ 0 := by
    simpa only [Homogenization.H1Function.neg_toFun] using hylower
  exact ⟨by linarith, hyupper⟩

theorem aux_lem_cutoffs_cc_harmonic_range
    {d : ℕ} [NeZero d] (W : Set (SpatialCoordinates d))
    (a : SpatialCoordinates d → ℝ) (lam Lam : ℝ)
    (hWdom : IsOpenBoundedConvexDomain W) (hlam : 0 < lam)
    (ha : Continuous a)
    (habounds : ∀ x ∈ W, lam ≤ a x ∧ a x ≤ Lam)
    (φ u : H1Function W)
    (hφupper : ∀ y, φ.toFun y ≤ 1)
    (hφlower : ∀ y, -φ.toFun y ≤ 0)
    (hu : IsWeaklyHarmonicOn a W u)
    (htrace : HasZeroTraceDifferenceOn W u φ)
    (hcont : ContinuousOn u.toFun (closure W)) :
    ∀ x ∈ closure W, 0 ≤ u.toFun x ∧ u.toFun x ≤ 1 := by
  have hWopen : IsOpen W := hWdom.1
  have hae := aux_lem_cutoffs_cc_harmonic_ae_abs W a lam Lam hWdom hlam ha
    habounds φ u hφupper hφlower hu htrace
  have haeupper : ∀ᵐ y ∂(volume.restrict W), u.toFun y ≤ 1 := by
    filter_upwards [hae] with y hy
    exact hy.2
  have haelower : ∀ᵐ y ∂(volume.restrict W), -u.toFun y ≤ 0 := by
    filter_upwards [hae] with y hy
    linarith [hy.1]
  have hupperW : ∀ x ∈ W, u.toFun x ≤ 1 :=
    lane2_le_of_ae_le_of_continuousOn hWopen
      (hcont.mono subset_closure) haeupper
  have hlowerW : ∀ x ∈ W, -u.toFun x ≤ 0 :=
    lane2_le_of_ae_le_of_continuousOn hWopen
      (hcont.neg.mono subset_closure) haelower
  intro x hx
  have hupperC : u.toFun x ≤ 1 :=
    ContinuousWithinAt.closure_le hx ((hcont x hx).mono subset_closure)
      continuousWithinAt_const hupperW
  have hlowerC : -u.toFun x ≤ 0 :=
    ContinuousWithinAt.closure_le hx
      ((hcont.neg x hx).mono subset_closure) continuousWithinAt_const hlowerW
  constructor <;> linarith

theorem aux_lem_cutoffs_cc_constant_cell
    {d : ℕ} [NeZero d] (W : Set (SpatialCoordinates d))
    (a : SpatialCoordinates d → ℝ) (lam Lam : ℝ)
    (hWdom : IsOpenBoundedConvexDomain W) (hlam : 0 < lam)
    (ha : Continuous a)
    (habounds : ∀ x ∈ W, lam ≤ a x ∧ a x ≤ Lam)
    (φ u : H1Function W) (cval : ℝ) (hφone : ∀ x ∈ W, φ.toFun x = cval)
    (hu : IsWeaklyHarmonicOn a W u)
    (htrace : HasZeroTraceDifferenceOn W u φ)
    (hcont : ContinuousOn u.toFun (closure W)) :
    ∀ x ∈ closure W, u.toFun x = cval := by
  let := hWdom.isFiniteMeasure_restrict_volume
  have hWopen : IsOpen W := hWdom.1
  obtain ⟨w, hwval, hwgrad⟩ := htrace
  let c : H1Function W := H1Function.const cval
  have hdiff : MemH10 W (u - c).toFun := by
    have hae : (u - c).toFun =ᵐ[volume.restrict W] w.toH1Function.toFun := by
      filter_upwards [ae_restrict_mem hWopen.measurableSet] with x hx
      have hw := hwval x
      have hp := hφone x hx
      dsimp [c]
      simp only [Homogenization.H1Function.sub_toFun, H1Function.const_apply]
      rw [hw, hp]
      ring_nf
    exact Homogenization.memH10_of_ae_eq_h10 hWdom (u - c) w hae
  let cn : H1Function W := H1Function.const (-cval)
  have hdiffneg : MemH10 W ((-u) - cn).toFun := by
    have hae : ((-u) - cn).toFun =ᵐ[volume.restrict W]
        (-w).toH1Function.toFun := by
      filter_upwards [ae_restrict_mem hWopen.measurableSet] with x hx
      have hw := hwval x
      have hp := hφone x hx
      dsimp [cn]
      simp only [Homogenization.H1Function.sub_toFun,
        Homogenization.H1Function.neg_toFun, H1Function.const_apply]
      rw [hw, hp]
      ring_nf
      rw [show (-w).toH1Function = -w.toH1Function by rfl]
      simp only [Homogenization.H1Function.neg_toFun]
    exact Homogenization.memH10_of_ae_eq_h10 hWdom ((-u) - cn) (-w) hae
  have hameas : AEStronglyMeasurable a (volumeMeasureOn W) :=
    ha.aestronglyMeasurable.restrict
  have hbounds : ∀ᵐ y ∂(volumeMeasureOn W), lam ≤ a y ∧ a y ≤ Lam := by
    filter_upwards [ae_restrict_mem hWopen.measurableSet] with y hy
    exact habounds y hy
  have hupper :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.hasBoundaryUpperBoundOn_of_datum_le
      (M := cval) hWdom (by simpa only [Homogenization.H1Function.sub_toFun] using hdiff)
        (by intro y; simp [c])
  have hlower :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.hasBoundaryUpperBoundOn_of_datum_le
      (M := -cval) hWdom (by simpa only [Homogenization.H1Function.sub_toFun] using hdiffneg)
        (by intro y; simp [cn])
  have haeupper :=
    SubdiffusiveProcess.CoarseGrainingVocab.ae_le_of_isWeaklyHarmonicOn
      hWdom hlam hameas hbounds hu hupper
  have haelower :=
    SubdiffusiveProcess.CoarseGrainingVocab.ae_le_of_isWeaklyHarmonicOn
      hWdom hlam hameas hbounds (SubdiffusiveProcess.CoarseGrainingVocab.isWeaklyHarmonicOn_neg hu) hlower
  have hae : u.toFun =ᵐ[volume.restrict W] (fun _ => cval) := by
    filter_upwards [haeupper, haelower] with y hyupper hylower
    have hylower' : -u.toFun y ≤ -cval := by
      simpa only [Homogenization.H1Function.neg_toFun] using hylower
    linarith
  have heqW : ∀ x ∈ W, u.toFun x = cval :=
    lane2_eqOn_of_ae_eq_of_continuousOn hWopen
      (hcont.mono subset_closure) continuousOn_const hae
  intro x hx
  apply le_antisymm
  · exact ContinuousWithinAt.closure_le hx
      ((hcont x hx).mono subset_closure) continuousWithinAt_const
      (fun y hy => (heqW y hy).le)
  · exact ContinuousWithinAt.closure_le hx
      (continuousWithinAt_const) ((hcont x hx).mono subset_closure)
      (fun y hy => (heqW y hy).ge)


/-- Odd-grid cells are open bounded convex domains. -/
theorem aux_lem_cutoffs_cell_dom {d : ℕ} (z : SpatialCoordinates d) {R : ℝ} (hR : 0 < R)
    (m : ℕ) (k : OddGridIndex d m) :
    IsOpenBoundedConvexDomain (oddGridCell z R hR m k : Set (SpatialCoordinates d)) := by
  dsimp [oddGridCell]
  apply lane2_isOpenBoundedConvexDomain_centeredCube

/-- Odd-grid cells are nonempty. -/
theorem aux_lem_cutoffs_cell_nonempty {d : ℕ} (z : SpatialCoordinates d) {R : ℝ} (hR : 0 < R)
    (m : ℕ) (k : OddGridIndex d m) :
    (oddGridCell z R hR m k : Set (SpatialCoordinates d)).Nonempty := by
  refine ⟨oddGridCenter z R m k, ?_⟩
  exact Metric.mem_ball_self (half_pos (div_pos hR (by positivity)))

/-- The closure of a cell lies in the closure of its parent. -/
theorem aux_lem_cutoffs_cell_closure_sub {d : ℕ} (z : SpatialCoordinates d) {R : ℝ}
    (hR : 0 < R) (m : ℕ) (k : OddGridIndex d m) :
    closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)) ⊆
      closure (centeredCube z R hR : Set (SpatialCoordinates d)) :=
  closure_mono (oddGridCell_subset z hR m k)

/-- The harmonic triadic mesh interpolant of a smooth `[0,1]`-valued compactly
supported datum, with the range, constant-cell, minimality and partition
properties used by both cutoff constructions. -/
theorem aux_lem_cutoffs_mesh_package {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (J : ℕ)
    (a : SpatialCoordinates d → ℝ) (ha : Continuous a) (hapos : ∀ x, 0 < a x)
    (φ : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hφs : ContDiff ℝ ∞ φ.toFun) (hφc : HasCompactSupport φ.toFun)
    (hφQ : tsupport φ.toFun ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hφr : ∀ x, 0 ≤ φ.toFun x ∧ φ.toFun x ≤ 1) :
    ∃ w : H10Function (centeredCube z R hR : Set (SpatialCoordinates d)),
      ContinuousOn w.toH1Function.toFun
        (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
      (∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
        0 ≤ w.toH1Function.toFun x ∧ w.toH1Function.toFun x ≤ 1) ∧
      (∀ k : OddGridIndex d (triadicHalf J),
        IsWeaklyHarmonicOn a
          (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
          (w.toH1Function.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
            (oddGridCell_subset z hR (triadicHalf J) k)) ∧
        HasZeroTraceDifferenceOn
          (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
          (w.toH1Function.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
            (oddGridCell_subset z hR (triadicHalf J) k))
          (φ.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
            (oddGridCell_subset z hR (triadicHalf J) k))) ∧
      (∀ k : OddGridIndex d (triadicHalf J),
        energy a (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
            (w.toH1Function.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
              (oddGridCell_subset z hR (triadicHalf J) k)) =
          cellDirichletInfimum a
            (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
            (φ.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
              (oddGridCell_subset z hR (triadicHalf J) k))) ∧
      (∀ (k : OddGridIndex d (triadicHalf J)) (c : ℝ),
        (∀ x ∈ (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)),
          φ.toFun x = c) →
        (∀ x ∈ closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)),
          w.toH1Function.toFun x = c) ∧
        ∀ᵐ x ∂(volume.restrict
          (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))),
          ∀ i : Fin d, w.toH1Function.grad x i = 0) ∧
      energy a (centeredCube z R hR : Set (SpatialCoordinates d)) w.toH1Function =
        ∑ k : OddGridIndex d (triadicHalf J),
          energy a (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
            (w.toH1Function.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
              (oddGridCell_subset z hR (triadicHalf J) k)) := by
  obtain ⟨lam, Lam, hlam, hbounds⟩ := aux_lem_cutoffs_pos_bounds a ha hapos
    (closure (centeredCube z R hR : Set (SpatialCoordinates d)))
    (lane2_isCompact_closure_centeredCube z hR)
  have hboundsQ : ∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
      lam ≤ a x ∧ a x ≤ Lam := fun x hx => hbounds x (subset_closure hx)
  obtain ⟨Cmesh, -, hmesh⟩ := mesh_interpolator (d := d) hd
  obtain ⟨w, hwcont, hwcell, hwenergy, -⟩ :=
    hmesh z R hR J a lam Lam hlam ha hboundsQ φ hφs hφc hφQ
  have hcellQ : ∀ k : OddGridIndex d (triadicHalf J),
      ∀ x ∈ (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)),
        lam ≤ a x ∧ a x ≤ Lam := fun k x hx =>
    hboundsQ x (oddGridCell_subset z hR (triadicHalf J) k hx)
  have hharm : ∀ k : OddGridIndex d (triadicHalf J),
      IsWeaklyHarmonicOn a
          (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
          (w.toH1Function.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
            (oddGridCell_subset z hR (triadicHalf J) k)) ∧
        HasZeroTraceDifferenceOn
          (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
          (w.toH1Function.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
            (oddGridCell_subset z hR (triadicHalf J) k))
          (φ.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
            (oddGridCell_subset z hR (triadicHalf J) k)) := fun k =>
    ⟨(hwcell k).1, (hwcell k).2.1⟩
  have hcont_cell : ∀ k : OddGridIndex d (triadicHalf J),
      ContinuousOn
        (w.toH1Function.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
          (oddGridCell_subset z hR (triadicHalf J) k)).toFun
        (closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))) :=
    fun k => hwcont.mono (aux_lem_cutoffs_cell_closure_sub z hR (triadicHalf J) k)
  refine ⟨w, hwcont, ?_, hharm, ?_, ?_, ?_⟩
  · intro x hx
    rw [← oddGridCell_closure_iUnion_eq_closure_centeredCube z hR (triadicHalf J)] at hx
    rcases mem_iUnion.mp hx with ⟨k, hxk⟩
    exact aux_lem_cutoffs_cc_harmonic_range
      (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
      a lam Lam (aux_lem_cutoffs_cell_dom z hR _ k) hlam ha (hcellQ k)
      (φ.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
        (oddGridCell_subset z hR (triadicHalf J) k))
      (w.toH1Function.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
        (oddGridCell_subset z hR (triadicHalf J) k))
      (fun y => (hφr y).2) (fun y => neg_nonpos.mpr (hφr y).1)
      (hharm k).1 (hharm k).2 (hcont_cell k) x hxk
  · intro k
    exact (hwcell k).2.2
  · intro k c hc
    have hconst := aux_lem_cutoffs_cc_constant_cell
      (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
      a lam Lam (aux_lem_cutoffs_cell_dom z hR _ k) hlam ha (hcellQ k)
      (φ.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
        (oddGridCell_subset z hR (triadicHalf J) k))
      (w.toH1Function.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
        (oddGridCell_subset z hR (triadicHalf J) k)) c hc
      (hharm k).1 (hharm k).2 (hcont_cell k)
    refine ⟨hconst, ?_⟩
    have hEll : IsEllipticFieldOn lam Lam
        (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
        (scalarCoeffField a) :=
      lane2_isEllipticFieldOn_scalar
        (oddGridCell z R hR (triadicHalf J) k).isOpen.measurableSet ha.measurable hlam
        (hcellQ k)
    have hcc := lem_20_collar_family_cell_constant d hd
      (oddGridCell z R hR (triadicHalf J) k) (aux_lem_cutoffs_cell_dom z hR _ k)
      (aux_lem_cutoffs_cell_nonempty z hR _ k) a lam Lam hEll
      (φ.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
        (oddGridCell_subset z hR (triadicHalf J) k))
      (w.toH1Function.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
        (oddGridCell_subset z hR (triadicHalf J) k)) c hc (hharm k).1 (hharm k).2
    filter_upwards [hcc] with x hx
    exact hx.2
  · have hameas : AEStronglyMeasurable a
        (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))) :=
      ha.aestronglyMeasurable
    have habd : ∀ᵐ x ∂(volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))),
        ‖a x‖ ≤ Lam := by
      filter_upwards [ae_restrict_mem (centeredCube z R hR).isOpen.measurableSet] with x hx
      rw [Real.norm_eq_abs]
      have hh := hboundsQ x hx
      exact abs_le.mpr (by constructor <;> linarith)
    have hcoord : ∀ i : Fin d, IntegrableOn
        (fun x => a x * (w.toH1Function.grad x i * w.toH1Function.grad x i))
        (centeredCube z R hR : Set (SpatialCoordinates d)) volume := by
      intro i
      exact lane2_integrableOn_coeff_mul hameas habd
        (w.toH1Function.gradMemL2 i) (w.toH1Function.gradMemL2 i)
    have hint : IntegrableOn
        (fun x => a x * Homogenization.vecDot (w.toH1Function.grad x) (w.toH1Function.grad x))
        (centeredCube z R hR : Set (SpatialCoordinates d)) volume := by
      have hsum : Integrable
          (fun x => ∑ i : Fin d, a x *
            (w.toH1Function.grad x i * w.toH1Function.grad x i))
          (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))) :=
        integrable_finsetSum Finset.univ (fun i _ => hcoord i)
      simp only [← Finset.mul_sum] at hsum
      exact hsum
    exact energy_eq_sum_oddGridCell_restrict z hR (triadicHalf J) a w.toH1Function hint

/-- The response form of the Sobolev data of an `H¹` function is its energy for
any coefficient agreeing a.e. with the response coefficient. -/
theorem aux_lem_cutoffs_resp_energy {d : ℕ} (z : SpatialCoordinates d) {R : ℝ} (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (aC : PositiveCoefficient (centeredCube z R hR)) (a : SpatialCoordinates d → ℝ)
    (hAC : (aC.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] a)
    (u : H1Function (centeredCube z R hR : Set (SpatialCoordinates d))) (χ : S.space)
    (hχ : (χ : SobolevData (centeredCube z R hR)) = sobolevDataOfH1 u) :
    responseForm S aC χ χ = energy a (centeredCube z R hR : Set (SpatialCoordinates d)) u := by
  obtain ⟨Cₐ, hCₐ⟩ := lane2_coeff_ae_bound aC
  have hint : ∀ i : Fin d, IntegrableOn
      (fun x => aC.val x *
        (((sobolevDataOfH1 u).2 i : DomainL2 (centeredCube z R hR)) x *
          ((sobolevDataOfH1 u).2 i : DomainL2 (centeredCube z R hR)) x))
      (centeredCube z R hR : Set (SpatialCoordinates d)) volume := by
    intro i
    exact lane2_integrableOn_coeff_mul (Lp.aestronglyMeasurable aC.val) hCₐ
      (Lp.memLp ((sobolevDataOfH1 u).2 i))
      (Lp.memLp ((sobolevDataOfH1 u).2 i))
  have hall : ∀ᵐ x ∂(volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))),
      ∀ i : Fin d,
        (((sobolevDataOfH1 u).2 i : DomainL2 (centeredCube z R hR)) x) = u.grad x i := by
    apply ae_all_iff.mpr
    intro i
    exact sobolevDataOfH1_snd_coeFn u i
  rw [responseForm_apply, hχ]
  calc
    ∑ i : Fin d, ∫ x in (centeredCube z R hR : Set (SpatialCoordinates d)),
          aC.val x *
            (((sobolevDataOfH1 u).2 i : DomainL2 (centeredCube z R hR)) x *
              ((sobolevDataOfH1 u).2 i : DomainL2 (centeredCube z R hR)) x)
        = ∫ x in (centeredCube z R hR : Set (SpatialCoordinates d)),
          ∑ i : Fin d, aC.val x *
            (((sobolevDataOfH1 u).2 i : DomainL2 (centeredCube z R hR)) x *
              ((sobolevDataOfH1 u).2 i : DomainL2 (centeredCube z R hR)) x) := by
      symm
      simpa only [Finset.sum_apply] using
        (integral_finsetSum Finset.univ (fun i _ => hint i))
    _ = energy a (centeredCube z R hR : Set (SpatialCoordinates d)) u := by
      apply integral_congr_ae
      filter_upwards [hAC, hall] with x hx hxi
      simp only [Homogenization.vecDot]
      rw [hx, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hxi i]

/-- The energy of a smooth datum on a bounded open convex domain is bounded by
the coefficient bound, the dimension, the squared gradient bound and the volume. -/
theorem aux_lem_cutoffs_datum_energy_le {d : ℕ} (W : Set (SpatialCoordinates d))
    (hW : IsOpenBoundedConvexDomain W) (a : SpatialCoordinates d → ℝ) (A G : ℝ)
    (hA : ∀ x ∈ W, 0 ≤ a x ∧ a x ≤ A) (hG : 0 ≤ G)
    (φ : H1Function W) (hφs : ContDiff ℝ 1 φ.toFun)
    (hgrad : ∀ x ∈ W, ‖fderiv ℝ φ.toFun x‖ ≤ G) :
    energy a W φ ≤ A * ((d : ℝ) * G ^ 2) * volume.real W := by
  have : IsFiniteMeasure (volume.restrict W) := hW.isFiniteMeasure_restrict_volume
  let ψ : H1Function W := H1Function.ofContDiffOnIsOpenBoundedConvexDomain hW hφs
  have hgae : φ.grad =ᵐ[volume.restrict W] ψ.grad :=
    lane2_grad_ae_eq_of_ae_eq' hW.isOpen hW.isBoundedDomain.isBounded φ ψ
      (Filter.Eventually.of_forall fun x => rfl)
  have hψ : ∀ x i, ψ.grad x i = (fderiv ℝ φ.toFun x) (basisVec i) := fun x i => rfl
  have hWm : ∀ᵐ x ∂(volume.restrict W), x ∈ W := ae_restrict_mem hW.isOpen.measurableSet
  have hbasis : ∀ i : Fin d, ‖(basisVec i : SpatialCoordinates d)‖ ≤ 1 := by
    intro i
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    rw [basisVec_apply]
    split_ifs <;> simp
  have hpt : ∀ᵐ x ∂(volume.restrict W),
      a x * Homogenization.vecDot (φ.grad x) (φ.grad x) ≤ A * ((d : ℝ) * G ^ 2) := by
    filter_upwards [hgae, hWm] with x hx hxW
    have hsq : ∀ i : Fin d, φ.grad x i * φ.grad x i ≤ G ^ 2 := by
      intro i
      rw [hx, hψ]
      have h1 : |(fderiv ℝ φ.toFun x) (basisVec i)| ≤ G := by
        calc |(fderiv ℝ φ.toFun x) (basisVec i)| = ‖(fderiv ℝ φ.toFun x) (basisVec i)‖ :=
              (Real.norm_eq_abs _).symm
          _ ≤ ‖fderiv ℝ φ.toFun x‖ * ‖(basisVec i : SpatialCoordinates d)‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ G * 1 := mul_le_mul (hgrad x hxW) (hbasis i) (norm_nonneg _) hG
          _ = G := mul_one G
      have := mul_self_le_mul_self (abs_nonneg _) h1
      rw [abs_mul_abs_self] at this
      simpa [sq] using this
    have hdot : Homogenization.vecDot (φ.grad x) (φ.grad x) ≤ (d : ℝ) * G ^ 2 := by
      unfold Homogenization.vecDot
      calc ∑ i : Fin d, φ.grad x i * φ.grad x i ≤ ∑ _i : Fin d, G ^ 2 :=
            Finset.sum_le_sum fun i _ => hsq i
        _ = (d : ℝ) * G ^ 2 := by simp
    have hdot0 : 0 ≤ Homogenization.vecDot (φ.grad x) (φ.grad x) := by
      unfold Homogenization.vecDot
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    calc a x * Homogenization.vecDot (φ.grad x) (φ.grad x)
        ≤ A * Homogenization.vecDot (φ.grad x) (φ.grad x) :=
          mul_le_mul_of_nonneg_right (hA x hxW).2 hdot0
      _ ≤ A * ((d : ℝ) * G ^ 2) :=
          mul_le_mul_of_nonneg_left hdot ((hA x hxW).1.trans (hA x hxW).2)
  have hnn : 0 ≤ᵐ[volume.restrict W] fun x => a x * Homogenization.vecDot (φ.grad x) (φ.grad x) := by
    filter_upwards [hWm] with x hxW
    apply mul_nonneg (hA x hxW).1
    unfold Homogenization.vecDot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  calc energy a W φ = ∫ x in W, a x * Homogenization.vecDot (φ.grad x) (φ.grad x) := rfl
    _ ≤ ∫ _x in W, A * ((d : ℝ) * G ^ 2) :=
        integral_mono_of_nonneg hnn (integrable_const _) hpt
    _ = A * ((d : ℝ) * G ^ 2) * volume.real W := by
        rw [setIntegral_const, smul_eq_mul, mul_comm]

theorem aux_lem_cutoffs_cc_partition_measure
    {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (m : ℕ)
    (g : SpatialCoordinates d → ENNReal) (x : SpatialCoordinates d) (rho : ℝ) :
    ((volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))).withDensity g)
        (Metric.ball x rho) =
      ∑ k : OddGridIndex d m,
        ((volume.restrict (oddGridCell z R hR m k : Set (SpatialCoordinates d))).withDensity g)
          (Metric.ball x rho) := by
  let μ : Measure (SpatialCoordinates d) := volume.withDensity g
  let U : Set (SpatialCoordinates d) :=
    ⋃ k : OddGridIndex d m, (oddGridCell z R hR m k : Set (SpatialCoordinates d))
  have hμae : U =ᵐ[μ] (centeredCube z R hR : Set (SpatialCoordinates d)) := by
    exact (withDensity_absolutelyContinuous (volume : Measure (SpatialCoordinates d)) g).ae_eq
      (oddGrid_union_ae_eq z hR m)
  have hrestrict : μ.restrict (centeredCube z R hR : Set (SpatialCoordinates d)) =
      μ.restrict U := Measure.restrict_congr_set hμae.symm
  have hunion : μ.restrict U =
      Measure.sum (fun k : OddGridIndex d m =>
        μ.restrict (oddGridCell z R hR m k : Set (SpatialCoordinates d))) := by
    exact Measure.restrict_iUnion
      (oddGridCell_pairwiseDisjoint z hR m)
      (fun k => (oddGridCell z R hR m k).isOpen.measurableSet)
  have hQ : μ.restrict (centeredCube z R hR : Set (SpatialCoordinates d)) =
      (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))).withDensity g := by
    exact restrict_withDensity (centeredCube z R hR).isOpen.measurableSet g
  have hcell : ∀ k : OddGridIndex d m,
      μ.restrict (oddGridCell z R hR m k : Set (SpatialCoordinates d)) =
        (volume.restrict (oddGridCell z R hR m k : Set (SpatialCoordinates d))).withDensity g := by
    intro k
    exact restrict_withDensity (oddGridCell z R hR m k).isOpen.measurableSet g
  rw [← hQ, hrestrict, hunion, Measure.sum_apply _ Metric.isOpen_ball.measurableSet]
  simp_rw [hcell]
  rw [tsum_fintype]

theorem aux_lem_cutoffs_cc_cell_measure_mono
    {d : ℕ} (cell : Set (SpatialCoordinates d)) (hcell : IsOpen cell)
    (g : SpatialCoordinates d → ENNReal) (s t : Set (SpatialCoordinates d))
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hsub : s ∩ cell ⊆ t ∩ cell) :
    ((volume.restrict cell).withDensity g) s ≤
      ((volume.restrict cell).withDensity g) t := by
  let μ : Measure (SpatialCoordinates d) := volume.withDensity g
  let ν : Measure (SpatialCoordinates d) := (volume.restrict cell).withDensity g
  have hν : ν = μ.restrict cell := by
    dsimp [ν, μ]
    exact (restrict_withDensity hcell.measurableSet g).symm
  have hsupp : ν.restrict cell = ν := by
    rw [hν, Measure.restrict_restrict hcell.measurableSet]
    simp only [inter_self]
  calc
    ((volume.restrict cell).withDensity g) s = (ν.restrict cell) s := by rw [hsupp]
    _ = ν (s ∩ cell) := Measure.restrict_apply hs
    _ ≤ ν (t ∩ cell) := measure_mono hsub
    _ = (ν.restrict cell) t := (Measure.restrict_apply ht).symm
    _ = ((volume.restrict cell).withDensity g) t := by rw [hsupp]

theorem aux_lem_cutoffs_cc_sum_power
    {ι : Type*} [Fintype ι] (c : ι → ℝ) (t rho : ℝ)
    (hc : ∀ i, 0 ≤ c i) (_ht : 0 ≤ t) (hrho : 0 ≤ rho) :
    (∑ i : ι, ENNReal.ofReal (c i * (2 * rho) ^ t)) =
      ENNReal.ofReal ((2 : ℝ) ^ t * (∑ i : ι, c i) * rho ^ t) := by
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · rw [← Finset.sum_mul]
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hrho]
    congr 1
    ring
  · intro i _
    exact mul_nonneg (hc i) (Real.rpow_nonneg (by positivity) t)

theorem aux_lem_cutoffs_cc_density_congr
    {d : ℕ} {μ : Measure (SpatialCoordinates d)}
    (f g : SpatialCoordinates d → ℝ)
    (p q : SpatialCoordinates d → Fin d → ℝ)
    (hf : f =ᵐ[μ] g)
    (hp : ∀ i : Fin d, (fun x => p x i) =ᵐ[μ] (fun x => q x i)) :
    (fun x => ENNReal.ofReal (f x * ∑ i : Fin d, (p x i) ^ 2)) =ᵐ[μ]
      (fun x => ENNReal.ofReal (g x * ∑ i : Fin d, (q x i) ^ 2)) := by
  filter_upwards [hf, ae_all_iff.mpr hp] with x hfx hxp
  rw [hfx]
  congr 1
  simp_rw [hxp]


/-- Cellwise all-radii bound with the total cell energy absorbing radii above
one half; no bound on the cell diameter is needed. -/
theorem aux_lem_cutoffs_cell_growth_total {d : ℕ} (cell : Set (SpatialCoordinates d))
    (hcell : IsOpen cell) (g : SpatialCoordinates d → ENNReal) (Gr E t : ℝ)
    (ht : 0 ≤ t) (hGr : 0 ≤ Gr) (hE : 0 ≤ E)
    (hbound : ∀ y ∈ closure cell, ∀ r : ℝ, 0 < r → r ≤ 1 →
      ((volume.restrict cell).withDensity g) (Metric.ball y r) ≤ ENNReal.ofReal (Gr * r ^ t))
    (htotal : ((volume.restrict cell).withDensity g) Set.univ ≤ ENNReal.ofReal E)
    (x : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ((volume.restrict cell).withDensity g) (Metric.ball x r) ≤
      ENNReal.ofReal ((Gr + E) * (2 * r) ^ t) := by
  have hmono : ENNReal.ofReal (Gr * (2 * r) ^ t) ≤ ENNReal.ofReal ((Gr + E) * (2 * r) ^ t) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg (by positivity) t))
  by_cases hsmall : 2 * r ≤ 1
  · by_cases hne : (Metric.ball x r ∩ cell).Nonempty
    · obtain ⟨y, hyball, hycell⟩ := hne
      have hycl : y ∈ closure cell := subset_closure hycell
      have hsubset : Metric.ball x r ∩ cell ⊆ Metric.ball y (2 * r) ∩ cell := by
        intro q hq
        refine ⟨?_, hq.2⟩
        apply Metric.mem_ball'.mpr
        calc
          dist y q ≤ dist y x + dist x q := dist_triangle _ _ _
          _ < r + r := add_lt_add
            (Metric.mem_ball.mp hyball)
            (by simpa [dist_comm] using (Metric.mem_ball.mp hq.1))
          _ = 2 * r := by ring
      calc
        ((volume.restrict cell).withDensity g) (Metric.ball x r) ≤
            ((volume.restrict cell).withDensity g) (Metric.ball y (2 * r)) :=
          aux_lem_cutoffs_cc_cell_measure_mono cell hcell g
            (Metric.ball x r) (Metric.ball y (2 * r))
            Metric.isOpen_ball.measurableSet Metric.isOpen_ball.measurableSet hsubset
        _ ≤ ENNReal.ofReal (Gr * (2 * r) ^ t) := hbound y hycl (2 * r) (by positivity) hsmall
        _ ≤ _ := hmono
    · have hempty : Metric.ball x r ∩ cell = ∅ := not_nonempty_iff_eq_empty.mp hne
      calc
        ((volume.restrict cell).withDensity g) (Metric.ball x r) ≤
            ((volume.restrict cell).withDensity g) (∅ : Set (SpatialCoordinates d)) :=
          aux_lem_cutoffs_cc_cell_measure_mono cell hcell g
            (Metric.ball x r) ∅ Metric.isOpen_ball.measurableSet MeasurableSet.empty
            (by simp [hempty])
        _ = 0 := by simp
        _ ≤ _ := bot_le
  · have hpow : 1 ≤ (2 * r) ^ t := Real.one_le_rpow (by linarith) ht
    calc
      ((volume.restrict cell).withDensity g) (Metric.ball x r) ≤
          ((volume.restrict cell).withDensity g) Set.univ := measure_mono (subset_univ _)
      _ ≤ ENNReal.ofReal E := htotal
      _ ≤ ENNReal.ofReal ((Gr + E) * (2 * r) ^ t) := by
        apply ENNReal.ofReal_le_ofReal
        calc E = E * 1 := (mul_one E).symm
          _ ≤ (Gr + E) * (2 * r) ^ t :=
            mul_le_mul (by linarith) hpow zero_le_one (by linarith)

/-- The total mass of a cell energy measure is the cell energy. -/
theorem aux_lem_cutoffs_energy_measure_univ {d : ℕ} (W : TopologicalSpace.Opens (SpatialCoordinates d))
    (a : SpatialCoordinates d → ℝ) (Lam : ℝ) (ha : Continuous a)
    (hbd : ∀ x ∈ (W : Set (SpatialCoordinates d)), 0 ≤ a x ∧ a x ≤ Lam)
    (u : H1Function (W : Set (SpatialCoordinates d))) :
    ((volume.restrict (W : Set (SpatialCoordinates d))).withDensity
        (fun y => ENNReal.ofReal (a y * ∑ i : Fin d, (u.grad y i) ^ 2))) Set.univ =
      ENNReal.ofReal (energy a (W : Set (SpatialCoordinates d)) u) := by
  have hameas : AEStronglyMeasurable a (volume.restrict (W : Set (SpatialCoordinates d))) :=
    ha.aestronglyMeasurable
  have habd : ∀ᵐ x ∂(volume.restrict (W : Set (SpatialCoordinates d))), ‖a x‖ ≤ Lam := by
    filter_upwards [ae_restrict_mem W.isOpen.measurableSet] with x hx
    rw [Real.norm_eq_abs]
    have hh := hbd x hx
    exact abs_le.mpr (by constructor <;> linarith)
  have hcoord : ∀ i : Fin d, IntegrableOn
      (fun x => a x * (u.grad x i * u.grad x i)) (W : Set (SpatialCoordinates d)) volume :=
    fun i => lane2_integrableOn_coeff_mul hameas habd (u.gradMemL2 i) (u.gradMemL2 i)
  have hint : Integrable (fun y => a y * ∑ i : Fin d, (u.grad y i) ^ 2)
      (volume.restrict (W : Set (SpatialCoordinates d))) := by
    have hsum := integrable_finsetSum Finset.univ (fun i _ => hcoord i)
    refine hsum.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [← Finset.mul_sum, sq]
  have hnn : 0 ≤ᵐ[volume.restrict (W : Set (SpatialCoordinates d))]
      fun y => a y * ∑ i : Fin d, (u.grad y i) ^ 2 := by
    filter_upwards [ae_restrict_mem W.isOpen.measurableSet] with y hy
    exact mul_nonneg (hbd y hy).1 (Finset.sum_nonneg fun i _ => sq_nonneg _)
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  unfold energy
  apply integral_congr_ae
  filter_upwards with y
  simp only [Homogenization.vecDot, sq]


/-! ### Plateau helpers of the mesh/collar step -/

theorem aux_lem_cutoffs_cc_global_measure_bound
    {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (m : ℕ)
    (g h : SpatialCoordinates d → ENNReal)
    (heq : g =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] h)
    (b : OddGridIndex d m → ℝ) (hb : ∀ k, 0 ≤ b k) (t : ℝ) (ht : 0 ≤ t)
    (hcell : ∀ k : OddGridIndex d m, ∀ x : SpatialCoordinates d,
      ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
      ((volume.restrict (oddGridCell z R hR m k : Set (SpatialCoordinates d))).withDensity h)
        (Metric.ball x rho) ≤ ENNReal.ofReal (b k * (2 * rho) ^ t))
    (x : SpatialCoordinates d) (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    ((volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))).withDensity g)
        (Metric.ball x rho) ≤
      ENNReal.ofReal (((2 : ℝ) ^ t * ∑ k : OddGridIndex d m, b k) * rho ^ t) := by
  rw [withDensity_congr_ae heq]
  rw [aux_lem_cutoffs_cc_partition_measure z R hR m h x rho]
  calc
    (∑ k : OddGridIndex d m,
        ((volume.restrict (oddGridCell z R hR m k : Set (SpatialCoordinates d))).withDensity h)
          (Metric.ball x rho)) ≤
        ∑ k : OddGridIndex d m, ENNReal.ofReal (b k * (2 * rho) ^ t) := by
      exact Finset.sum_le_sum (fun k _ => hcell k x rho hrho hrho1)
    _ = ENNReal.ofReal (((2 : ℝ) ^ t * ∑ k : OddGridIndex d m, b k) * rho ^ t) :=
      aux_lem_cutoffs_cc_sum_power b t rho hb ht hrho.le

/-- On a mesh cell that is not a transition cell, a continuous `[0,1]`-valued
plateau datum is identically `0` or identically `1` on the closed cell. -/
theorem aux_lem_cutoffs_nontransition_const {d : ℕ} (z : SpatialCoordinates d) {R : ℝ}
    (hR : 0 < R) (m : ℕ) (k : OddGridIndex d m) (θ : SpatialCoordinates d → ℝ)
    (hθc : Continuous θ) (hθr : ∀ x, 0 ≤ θ x ∧ θ x ≤ 1)
    (hnot : ¬(closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)) ∩
      {x | 0 < θ x ∧ θ x < 1}).Nonempty) :
    (∀ x ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)), θ x = 0) ∨
      (∀ x ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)), θ x = 1) :=
  aux_cutoffs_plateau_constant_on_preconnected
    (aux_cutoffs_oddGridCell_closure_isPreconnected hR m k) hθc.continuousOn
    (fun x _ => hθr x) (fun ⟨x, hx, hmid⟩ => hnot ⟨x, hx, hmid⟩)

/-- The plateau neighbourhood `V`: the cube minus the closed cells missing `K`. -/
theorem aux_lem_cutoffs_plateau_V {d : ℕ} (z : SpatialCoordinates d) {R : ℝ} (hR : 0 < R)
    (m : ℕ) (θ : SpatialCoordinates d → ℝ) (hθc : Continuous θ)
    (hθr : ∀ x, 0 ≤ θ x ∧ θ x ≤ 1)
    (K O W : Set (SpatialCoordinates d)) (hKW : K ⊆ W) (hWO : W ⊆ O)
    (hOQ : closure O ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hθW : ∀ x ∈ W, θ x = 1) (hθO : tsupport θ ⊆ O)
    (htrans : ∀ k : OddGridIndex d m,
      (closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)) ∩
        {x | 0 < θ x ∧ θ x < 1}).Nonempty →
      closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)) ⊆ O \ K) :
    ∃ V : Set (SpatialCoordinates d), IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧
      ∀ x ∈ V, ∃ k : OddGridIndex d m,
        x ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)) ∧
        ∀ y ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)), θ y = 1 := by
  classical
  let F : Finset (OddGridIndex d m) := Finset.univ.filter
    (fun k => Disjoint (closure (oddGridCell z R hR m k : Set (SpatialCoordinates d))) K)
  let V : Set (SpatialCoordinates d) := (centeredCube z R hR : Set (SpatialCoordinates d)) \
    ⋃ k ∈ F, closure (oddGridCell z R hR m k : Set (SpatialCoordinates d))
  have hKQ : K ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) :=
    fun x hx => hOQ (subset_closure (hWO (hKW hx)))
  -- every point of `V` lies in a closed cell meeting `K`, on which `θ ≡ 1`
  have hcellone : ∀ x ∈ V, ∃ k : OddGridIndex d m,
      x ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)) ∧
      ∀ y ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)), θ y = 1 := by
    intro x hx
    have hxcl : x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)) :=
      subset_closure hx.1
    rw [← oddGridCell_closure_iUnion_eq_closure_centeredCube z hR m] at hxcl
    rcases mem_iUnion.mp hxcl with ⟨k, hxk⟩
    refine ⟨k, hxk, ?_⟩
    have hkF : k ∉ F := by
      intro hkF
      exact hx.2 (mem_iUnion₂.mpr ⟨k, hkF, hxk⟩)
    have hnd : ¬Disjoint (closure (oddGridCell z R hR m k : Set (SpatialCoordinates d))) K := by
      intro hdis
      exact hkF (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hdis⟩)
    obtain ⟨y, hyk, hyK⟩ := Set.not_disjoint_iff.mp hnd
    have hnot : ¬(closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)) ∩
        {x | 0 < θ x ∧ θ x < 1}).Nonempty := by
      intro htr
      exact (htrans k htr hyk).2 hyK
    rcases aux_lem_cutoffs_nontransition_const z hR m k θ hθc hθr hnot with h0 | h1
    · have := h0 y hyk
      rw [hθW y (hKW hyK)] at this
      norm_num at this
    · exact h1
  refine ⟨V, ?_, ?_, ?_, hcellone⟩
  · apply (centeredCube z R hR).isOpen.sdiff
    exact Set.Finite.isClosed_biUnion F.finite_toSet (fun k _ => isClosed_closure)
  · intro x hxK
    refine ⟨hKQ hxK, ?_⟩
    intro hx
    rcases mem_iUnion₂.mp hx with ⟨k, hkF, hxk⟩
    have hdis := (Finset.mem_filter.mp hkF).2
    exact Set.disjoint_left.mp hdis hxk hxK
  · intro x hx
    obtain ⟨k, hxk, hone⟩ := hcellone x hx
    apply hθO
    apply subset_tsupport
    rw [Function.mem_support, hone x hxk]
    exact one_ne_zero

/-- A cube point outside `O` lies in a closed cell on which `θ ≡ 0`. -/
theorem aux_lem_cutoffs_plateau_zero {d : ℕ} (z : SpatialCoordinates d) {R : ℝ} (hR : 0 < R)
    (m : ℕ) (θ : SpatialCoordinates d → ℝ) (hθc : Continuous θ)
    (hθr : ∀ x, 0 ≤ θ x ∧ θ x ≤ 1) (K O : Set (SpatialCoordinates d))
    (hθO : tsupport θ ⊆ O)
    (htrans : ∀ k : OddGridIndex d m,
      (closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)) ∩
        {x | 0 < θ x ∧ θ x < 1}).Nonempty →
      closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)) ⊆ O \ K)
    (x : SpatialCoordinates d) (hxQ : x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hxO : x ∉ O) :
    ∃ k : OddGridIndex d m,
      x ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)) ∧
      ∀ y ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)), θ y = 0 := by
  have hxcl : x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)) :=
    subset_closure hxQ
  rw [← oddGridCell_closure_iUnion_eq_closure_centeredCube z hR m] at hxcl
  rcases mem_iUnion.mp hxcl with ⟨k, hxk⟩
  refine ⟨k, hxk, ?_⟩
  have hnot : ¬(closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)) ∩
      {y | 0 < θ y ∧ θ y < 1}).Nonempty := fun htr => hxO (htrans k htr hxk).1
  have hθx : θ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hxO (hθO h))
  rcases aux_lem_cutoffs_nontransition_const z hR m k θ hθc hθr hnot with h0 | h1
  · exact h0
  · have := h1 x hxk
    rw [hθx] at this
    norm_num at this


/-- Hölder gluing and Arzelà–Ascoli for the plateau mesh interpolants. -/
theorem aux_lem_cutoffs_holder_limit {d : ℕ} (z : SpatialCoordinates d) {R : ℝ} (hR : 0 < R)
    (m : ℕ) {alpha : ℝ} (halpha : 0 < alpha) (θ : SpatialCoordinates d → ℝ)
    (chic : ℕ → SpatialCoordinates d → ℝ)
    (hcont : ∀ n, ContinuousOn (chic n) (closure (centeredCube z R hR : Set (SpatialCoordinates d))))
    (hrange : ∀ n, ∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
      0 ≤ chic n x ∧ chic n x ≤ 1)
    (Ho : OddGridIndex d m → ℝ) (hHo : ∀ k, 0 ≤ Ho k)
    (hpair : ∀ n (k : OddGridIndex d m),
      ∀ x ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)),
      ∀ y ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)),
        |chic n x - chic n y| ≤ Ho k * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha)
    (hconst : ∀ n (k : OddGridIndex d m),
      (∃ c : ℝ, ∀ x ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)), θ x = c) →
        ∀ x ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)), chic n x = θ x) :
    ∃ Bholder : ℝ, 0 ≤ Bholder ∧
      (∀ n, _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
          (closure (centeredCube z R hR : Set (SpatialCoordinates d))) (chic n) ∧
        _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
          (closure (centeredCube z R hR : Set (SpatialCoordinates d))) (chic n) ≤ Bholder) ∧
      ∃ sigma : ℕ → ℕ, ∃ chiLim : SpatialCoordinates d → ℝ,
        StrictMono sigma ∧
        ContinuousOn chiLim (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
        TendstoUniformlyOn (fun n => chic (sigma n)) chiLim atTop
          (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
        ∀ k : OddGridIndex d m,
          (∃ c : ℝ, ∀ x ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)),
            θ x = c) →
          ∀ x ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)),
            chiLim x = θ x := by
  classical
  set Hs : ℝ := ∑ k : OddGridIndex d m, Ho k with hHs
  have hHs0 : 0 ≤ Hs := Finset.sum_nonneg fun k _ => hHo k
  have hHok : ∀ k, Ho k ≤ Hs := fun k =>
    Finset.single_le_sum (f := Ho) (fun k _ => hHo k) (Finset.mem_univ k)
  set Hg : ℝ := (d : ℝ) * (2 * Hs + 2 * 1 * (R / (2 * (m : ℝ) + 1)) ^ (-alpha)) with hHg
  have hHg0 : 0 ≤ Hg := by
    have : 0 ≤ (R / (2 * (m : ℝ) + 1)) ^ (-alpha) :=
      Real.rpow_nonneg (div_nonneg hR.le (by positivity)) _
    positivity
  have hval : ∀ n, ∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
      |chic n x| ≤ 1 := fun n x hx =>
    abs_le.mpr ⟨by linarith [(hrange n x hx).1], (hrange n x hx).2⟩
  have hglob : ∀ n, ∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
      ∀ y ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
        |chic n x - chic n y| ≤ Hg * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha := by
    intro n
    exact aux_lem_cutoffs_holder_glue z R hR m halpha zero_le_one hHs0 (chic n) (hval n)
      (fun k x hx y hy => (hpair n k x hx y hy).trans
        (mul_le_mul_of_nonneg_right (hHok k)
          (Real.rpow_nonneg (Real.sqrt_nonneg _) _)))
  refine ⟨1 + Hg, by linarith, fun n =>
    aux_lem_cutoffs_holder_of_pair_bound halpha zero_le_one hHg0 (hval n) (hglob n), ?_⟩
  obtain ⟨σ, hσ, g, hg, hconv⟩ := aux_lem_cutoffs_subseq_uniform
    (closure (centeredCube z R hR : Set (SpatialCoordinates d)))
    (lane2_isCompact_closure_centeredCube z hR) chic hcont halpha hHg0 hval hglob
  refine ⟨σ, g, hσ, hg, hconv, ?_⟩
  intro k hk x hx
  have hxQ : x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)) :=
    closure_mono (oddGridCell_subset z hR m k) hx
  have hlim := hconv.tendsto_at hxQ
  have hconstseq : (fun n => chic (σ n) x) = fun _ => θ x := by
    funext n
    exact hconst (σ n) k hk x hx
  rw [hconstseq] at hlim
  exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm

/-- The deterministic plateau cutoff: the harmonic mesh interpolants of a
catalog plateau on a mesh finer than its transition region, given uniform
cellwise energy, all-radii and Hölder bounds for every cell solution. -/
theorem aux_lem_cutoffs_plateau_generic {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (hS : S.space = killedSobolevGraph (centeredCube z R hR))
    (a : ℕ → SpatialCoordinates d → ℝ) (ha : ∀ n, Continuous (a n))
    (hapos : ∀ n x, 0 < a n x)
    (aC : ℕ → PositiveCoefficient (centeredCube z R hR))
    (hAC : ∀ n, ((aC n).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] a n)
    (t alpha : ℝ) (ht : 0 ≤ t) (halpha : 0 < alpha)
    (θ : SpatialCoordinates d → ℝ)
    (θH : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hθH : θH.toFun = θ) (hθs : ContDiff ℝ ∞ θ)
    (K O W : Set (SpatialCoordinates d)) (Jmesh : ℕ)
    (_hO : IsOpen O)
    (hOQ : closure O ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hKW : K ⊆ W) (hWO : W ⊆ O)
    (hθr : ∀ x, 0 ≤ θ x ∧ θ x ≤ 1) (hθW : ∀ x ∈ W, θ x = 1) (hθO : tsupport θ ⊆ O)
    (htrans : ∀ k : OddGridIndex d (triadicHalf Jmesh),
      (closure (oddGridCell z R hR (triadicHalf Jmesh) k : Set (SpatialCoordinates d)) ∩
        {x | 0 < θ x ∧ θ x < 1}).Nonempty →
      closure (oddGridCell z R hR (triadicHalf Jmesh) k : Set (SpatialCoordinates d)) ⊆ O \ K)
    (hcell : ∀ k : OddGridIndex d (triadicHalf Jmesh), ∃ E Gr Ho : ℝ,
      0 ≤ E ∧ 0 ≤ Gr ∧ 0 ≤ Ho ∧
      ∀ (n : ℕ) (w : H1Function
          (oddGridCell z R hR (triadicHalf Jmesh) k : Set (SpatialCoordinates d))),
        IsWeaklyHarmonicOn (a n)
          (oddGridCell z R hR (triadicHalf Jmesh) k : Set (SpatialCoordinates d)) w →
        HasZeroTraceDifferenceOn
          (oddGridCell z R hR (triadicHalf Jmesh) k : Set (SpatialCoordinates d)) w
          (θH.restrict (oddGridCell z R hR (triadicHalf Jmesh) k).isOpen
            (oddGridCell_subset z hR (triadicHalf Jmesh) k)) →
        ContinuousOn w.toFun
          (closure (oddGridCell z R hR (triadicHalf Jmesh) k : Set (SpatialCoordinates d))) →
        energy (a n)
            (oddGridCell z R hR (triadicHalf Jmesh) k : Set (SpatialCoordinates d)) w ≤ E ∧
        (∀ x ∈ closure (oddGridCell z R hR (triadicHalf Jmesh) k :
            Set (SpatialCoordinates d)), ∀ r : ℝ, 0 < r → r ≤ 1 →
          ((volume.restrict (oddGridCell z R hR (triadicHalf Jmesh) k :
              Set (SpatialCoordinates d))).withDensity
            (fun y => ENNReal.ofReal (a n y * ∑ i : Fin d, (w.grad y i) ^ 2)))
            (Metric.ball x r) ≤ ENNReal.ofReal (Gr * r ^ t)) ∧
        (∀ x ∈ closure (oddGridCell z R hR (triadicHalf Jmesh) k :
            Set (SpatialCoordinates d)),
          ∀ y ∈ closure (oddGridCell z R hR (triadicHalf Jmesh) k :
            Set (SpatialCoordinates d)),
          |w.toFun x - w.toFun y| ≤
            Ho * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha)) :
    ∃ chiH : ℕ → H1Function (centeredCube z R hR : Set (SpatialCoordinates d)),
      ∃ chiS : ℕ → S.space,
        ∃ chic : ℕ → SpatialCoordinates d → ℝ,
          ∃ V : Set (SpatialCoordinates d),
            ∃ Benergy Ball Bholder : ℝ,
              IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧
              0 ≤ Benergy ∧ 0 ≤ Ball ∧ 0 ≤ Bholder ∧
              (∀ n : ℕ,
                (chiS n).val = sobolevDataOfH1 (chiH n) ∧
                ContinuousOn (chic n)
                  (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
                (chiS n).val.1 =ᵐ[
                  volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
                  chic n ∧
                (∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
                  0 ≤ chic n x ∧ chic n x ≤ 1) ∧
                (∀ x ∈ V, chic n x = 1) ∧
                (∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
                  x ∉ O → chic n x = 0) ∧
                (∀ k : OddGridIndex d (triadicHalf Jmesh),
                  IsWeaklyHarmonicOn (a n)
                    (oddGridCell z R hR (triadicHalf Jmesh) k : Set (SpatialCoordinates d))
                    ((chiH n).restrict
                      (oddGridCell z R hR (triadicHalf Jmesh) k).isOpen
                      (oddGridCell_subset z hR (triadicHalf Jmesh) k)) ∧
                  HasZeroTraceDifferenceOn
                    (oddGridCell z R hR (triadicHalf Jmesh) k : Set (SpatialCoordinates d))
                    ((chiH n).restrict
                      (oddGridCell z R hR (triadicHalf Jmesh) k).isOpen
                      (oddGridCell_subset z hR (triadicHalf Jmesh) k))
                    (θH.restrict
                      (oddGridCell z R hR (triadicHalf Jmesh) k).isOpen
                      (oddGridCell_subset z hR (triadicHalf Jmesh) k))) ∧
                (∀ k : OddGridIndex d (triadicHalf Jmesh),
                  (∃ c : ℝ, ∀ x ∈ closure
                      (oddGridCell z R hR (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                    θ x = c) →
                    ∀ i : Fin d, ∀ᵐ x ∂volume.restrict
                      (oddGridCell z R hR (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                      (chiS n).val.2 i x = 0) ∧
                responseForm S (aC n) (chiS n) (chiS n) ≤ Benergy ∧
                (∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)), ∀ s : ℝ,
                  0 < s → s ≤ 1 →
                  ((volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))).withDensity
                    (fun y => ENNReal.ofReal
                      ((aC n).val y *
                        ∑ i : Fin d, ((chiS n).val.2 i y) ^ 2)))
                    (Metric.ball x s) ≤ ENNReal.ofReal (Ball * s ^ t)) ∧
                _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
                  (closure (centeredCube z R hR : Set (SpatialCoordinates d))) (chic n) ∧
                _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
                  (closure (centeredCube z R hR : Set (SpatialCoordinates d))) (chic n) ≤
                  Bholder) ∧
              (∃ sigma : ℕ → ℕ, ∃ chiLim : SpatialCoordinates d → ℝ,
                StrictMono sigma ∧
                ContinuousOn chiLim
                  (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
                TendstoUniformlyOn (fun n => chic (sigma n)) chiLim atTop
                  (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
                (∀ k : OddGridIndex d (triadicHalf Jmesh),
                  (∃ c : ℝ, ∀ x ∈ closure
                      (oddGridCell z R hR (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                    θ x = c) →
                    ∀ x ∈ closure
                      (oddGridCell z R hR (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                      chiLim x = θ x)) := by
  classical
  have hθc : Continuous θ := hθs.continuous
  have htsQ : tsupport θ ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) :=
    hθO.trans (subset_closure.trans hOQ)
  have hφs : ContDiff ℝ ∞ θH.toFun := by rw [hθH]; exact hθs
  have hφc : HasCompactSupport θH.toFun := by
    rw [hθH]
    exact IsCompact.of_isClosed_subset (lane2_isCompact_closure_centeredCube z hR)
      (isClosed_tsupport _) (htsQ.trans subset_closure)
  have hφQ : tsupport θH.toFun ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) := by
    rw [hθH]; exact htsQ
  have hφr : ∀ x, 0 ≤ θH.toFun x ∧ θH.toFun x ≤ 1 := by rw [hθH]; exact hθr
  have hmesh := fun n => aux_lem_cutoffs_mesh_package hd z R hR Jmesh (a n) (ha n) (hapos n)
    θH hφs hφc hφQ hφr
  choose w hwcont hwrange hwharm hwen hwconst hwpart using hmesh
  choose E Gr Ho hE hGr hHo hcb using hcell
  let chiH : ℕ → H1Function (centeredCube z R hR : Set (SpatialCoordinates d)) :=
    fun n => (w n).toH1Function
  have hmem : ∀ n : ℕ, sobolevDataOfH1 (chiH n) ∈ S.space := by
    intro n
    rw [hS]
    exact sobolevDataOfH1_mem_killed (w n)
  let chiS : ℕ → S.space := fun n => ⟨sobolevDataOfH1 (chiH n), hmem n⟩
  let chic : ℕ → SpatialCoordinates d → ℝ := fun n => (chiH n).toFun
  -- constant cells: the interpolant equals the datum on the closed cell
  have hconstcell : ∀ n (k : OddGridIndex d (triadicHalf Jmesh)),
      (∃ c : ℝ, ∀ x ∈ closure
          (oddGridCell z R hR (triadicHalf Jmesh) k : Set (SpatialCoordinates d)), θ x = c) →
        (∀ x ∈ closure
          (oddGridCell z R hR (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
            chic n x = θ x) ∧
        ∀ᵐ x ∂(volume.restrict
          (oddGridCell z R hR (triadicHalf Jmesh) k : Set (SpatialCoordinates d))),
          ∀ i : Fin d, (chiH n).grad x i = 0 := by
    intro n k ⟨c, hc⟩
    have hc' : ∀ x ∈ (oddGridCell z R hR (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
        θH.toFun x = c := by
      intro x hx
      rw [hθH]
      exact hc x (subset_closure hx)
    obtain ⟨hv, hg⟩ := hwconst n k c hc'
    exact ⟨fun x hx => (hv x hx).trans (hc x hx).symm, hg⟩
  -- the plateau neighbourhood
  obtain ⟨V, hVopen, hKV, hVO, hVone⟩ := aux_lem_cutoffs_plateau_V z hR (triadicHalf Jmesh)
    θ hθc hθr K O W hKW hWO hOQ hθW hθO htrans
  -- Hölder bounds and the uniform limit
  have hpair : ∀ n (k : OddGridIndex d (triadicHalf Jmesh)),
      ∀ x ∈ closure (oddGridCell z R hR (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
      ∀ y ∈ closure (oddGridCell z R hR (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
        |chic n x - chic n y| ≤ Ho k * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha :=
    fun n k => (hcb k n _ (hwharm n k).1 (hwharm n k).2
      ((hwcont n).mono (aux_lem_cutoffs_cell_closure_sub z hR _ k))).2.2
  obtain ⟨Bholder, hBholder, hHol, hlim⟩ := aux_lem_cutoffs_holder_limit z hR (triadicHalf Jmesh)
    halpha θ chic hwcont hwrange Ho hHo hpair (fun n k hk => (hconstcell n k hk).1)
  -- energy
  let Benergy : ℝ := ∑ k : OddGridIndex d (triadicHalf Jmesh), E k
  have hBenergy : 0 ≤ Benergy := Finset.sum_nonneg fun k _ => hE k
  have hresp : ∀ n, responseForm S (aC n) (chiS n) (chiS n) ≤ Benergy := by
    intro n
    rw [aux_lem_cutoffs_resp_energy z hR S (aC n) (a n) (hAC n) (chiH n) (chiS n) rfl]
    rw [hwpart n]
    exact Finset.sum_le_sum fun k _ => (hcb k n _ (hwharm n k).1 (hwharm n k).2
      ((hwcont n).mono (aux_lem_cutoffs_cell_closure_sub z hR _ k))).1
  -- all-radii bound
  let Ball : ℝ := (2 : ℝ) ^ t * ∑ k : OddGridIndex d (triadicHalf Jmesh), (Gr k + E k)
  have hBall : 0 ≤ Ball :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) t)
      (Finset.sum_nonneg fun k _ => add_nonneg (hGr k) (hE k))
  have hgrowth : ∀ n, ∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
      ∀ s : ℝ, 0 < s → s ≤ 1 →
      ((volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))).withDensity
        (fun y => ENNReal.ofReal
          ((aC n).val y * ∑ i : Fin d, ((chiS n).val.2 i y) ^ 2)))
        (Metric.ball x s) ≤ ENNReal.ofReal (Ball * s ^ t) := by
    intro n x _ s hs hs1
    obtain ⟨lam, Lam, hlam, hbd⟩ := aux_lem_cutoffs_pos_bounds (a n) (ha n) (hapos n)
      (closure (centeredCube z R hR : Set (SpatialCoordinates d)))
      (lane2_isCompact_closure_centeredCube z hR)
    have hden := aux_lem_cutoffs_cc_density_congr
      ((aC n).val : SpatialCoordinates d → ℝ) (a n)
      (fun y i => ((chiS n).val.2 i : DomainL2 (centeredCube z R hR)) y)
      (fun y i => (chiH n).grad y i) (hAC n)
      (fun i => sobolevDataOfH1_snd_coeFn (chiH n) i)
    have hcellg : ∀ k : OddGridIndex d (triadicHalf Jmesh), ∀ y : SpatialCoordinates d,
        ∀ r : ℝ, 0 < r → r ≤ 1 →
        ((volume.restrict (oddGridCell z R hR (triadicHalf Jmesh) k :
            Set (SpatialCoordinates d))).withDensity
          (fun x => ENNReal.ofReal (a n x * ∑ i : Fin d, ((chiH n).grad x i) ^ 2)))
          (Metric.ball y r) ≤ ENNReal.ofReal ((Gr k + E k) * (2 * r) ^ t) := by
      intro k y r hr _
      have hcbk := hcb k n _ (hwharm n k).1 (hwharm n k).2
        ((hwcont n).mono (aux_lem_cutoffs_cell_closure_sub z hR _ k))
      have htot := aux_lem_cutoffs_energy_measure_univ
        (oddGridCell z R hR (triadicHalf Jmesh) k) (a n) Lam (ha n)
        (fun x hx => ⟨(hapos n x).le, (hbd x (aux_lem_cutoffs_cell_closure_sub z hR _ k
          (subset_closure hx))).2⟩)
        ((chiH n).restrict (oddGridCell z R hR (triadicHalf Jmesh) k).isOpen
          (oddGridCell_subset z hR (triadicHalf Jmesh) k))
      exact aux_lem_cutoffs_cell_growth_total _
        (oddGridCell z R hR (triadicHalf Jmesh) k).isOpen _ (Gr k) (E k) t ht (hGr k) (hE k)
        hcbk.2.1 (by rw [htot]; exact ENNReal.ofReal_le_ofReal hcbk.1) y r hr
    exact aux_lem_cutoffs_cc_global_measure_bound z R hR (triadicHalf Jmesh)
      (fun y => ENNReal.ofReal
        ((aC n).val y * ∑ i : Fin d, ((chiS n).val.2 i) y ^ 2))
      (fun y => ENNReal.ofReal (a n y * ∑ i : Fin d, ((chiH n).grad y i) ^ 2))
      hden (fun k => Gr k + E k) (fun k => add_nonneg (hGr k) (hE k)) t ht hcellg x s hs hs1
  refine ⟨chiH, chiS, chic, V, Benergy, Ball, Bholder, hVopen, hKV, hVO, hBenergy, hBall,
    hBholder, fun n => ?_, hlim⟩
  refine ⟨rfl, hwcont n, sobolevDataOfH1_fst_coeFn (chiH n), hwrange n, ?_, ?_,
    hwharm n, ?_, hresp n, hgrowth n, hHol n⟩
  · intro x hx
    obtain ⟨k, hxk, hone⟩ := hVone x hx
    exact ((hconstcell n k ⟨1, hone⟩).1 x hxk).trans (hone x hxk)
  · intro x hxQ hxO
    obtain ⟨k, hxk, hzero⟩ := aux_lem_cutoffs_plateau_zero z hR (triadicHalf Jmesh) θ hθc hθr
      K O hθO htrans x hxQ hxO
    exact ((hconstcell n k ⟨0, hzero⟩).1 x hxk).trans (hzero x hxk)
  · intro k hk i
    have hg := (hconstcell n k hk).2
    have hsd : (fun x => ((chiS n).val.2 i : DomainL2 (centeredCube z R hR)) x)
        =ᵐ[volume.restrict (oddGridCell z R hR (triadicHalf Jmesh) k :
          Set (SpatialCoordinates d))] fun x => (chiH n).grad x i :=
      ae_restrict_of_ae_restrict_of_subset (oddGridCell_subset z hR (triadicHalf Jmesh) k)
        (sobolevDataOfH1_snd_coeFn (chiH n) i)
    filter_upwards [hg, hsd] with x hx hx'
    rw [hx', hx i]


/-! ### Collar helpers of the mesh/collar step -/

/-- The zero extension of a collar datum off the cube, as an `H¹` datum with
the same weak gradient on the cube. -/
def aux_lem_cutoffs_collar_datum {d : ℕ} (z : SpatialCoordinates d) {R : ℝ} (hR : 0 < R)
    (thetaRH1 : H1Function (centeredCube z R hR : Set (SpatialCoordinates d))) :
    H1Function (centeredCube z R hR : Set (SpatialCoordinates d)) where
  toFun := (centeredCube z R hR : Set (SpatialCoordinates d)).indicator thetaRH1.toFun
  grad := thetaRH1.grad
  memL2 := by
    refine thetaRH1.memL2.ae_eq ?_
    filter_upwards [ae_restrict_mem (centeredCube z R hR).isOpen.measurableSet] with x hx
    rw [Set.indicator_of_mem hx]
  gradMemL2 := thetaRH1.gradMemL2
  hasWeakGradient := by
    intro i φ hφ hφc hφs
    rw [← thetaRH1.hasWeakGradient i φ hφ hφc hφs]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (centeredCube z R hR).isOpen.measurableSet] with x hx
    rw [Set.indicator_of_mem hx]

/-- The energy of an `H¹` function whose weak gradient vanishes a.e. is zero. -/
theorem aux_lem_cutoffs_energy_zero {d : ℕ} (W : Set (SpatialCoordinates d))
    (a : SpatialCoordinates d → ℝ) (u : H1Function W)
    (hg : ∀ᵐ x ∂(volume.restrict W), ∀ i : Fin d, u.grad x i = 0) :
    energy a W u = 0 := by
  unfold energy
  rw [← integral_zero (SpatialCoordinates d) ℝ]
  apply integral_congr_ae
  filter_upwards [hg] with x hx
  simp [Homogenization.vecDot, hx]

/-- The Dirichlet infimum only depends on the values of the datum on the cell
and on its weak gradient there. -/
theorem aux_lem_cutoffs_cellInf_congr {d : ℕ} (W : Set (SpatialCoordinates d)) (hW : IsOpen W)
    (a : SpatialCoordinates d → ℝ) (h h' : H1Function W)
    (hfun : ∀ x ∈ W, h.toFun x = h'.toFun x) (hgrad : h.grad = h'.grad) :
    cellDirichletInfimum a W h = cellDirichletInfimum a W h' := by
  unfold cellDirichletInfimum
  congr 1
  ext e
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, aux_lem_cutoffs_traceDiff_congr hW hu hfun (by rw [hgrad]), rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, aux_lem_cutoffs_traceDiff_congr hW hu (fun x hx => (hfun x hx).symm)
      (by rw [hgrad]), rfl⟩

/-- The deterministic collar cutoff: the harmonic mesh interpolants of a smooth
collar datum at mesh width `ρ = R / 3^Jr`. The energy is bounded by the sum of
the cell Dirichlet infima over the transition cells. -/
theorem aux_lem_cutoffs_collar_generic {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (hS : S.space = killedSobolevGraph (centeredCube z R hR))
    (a : ℕ → SpatialCoordinates d → ℝ) (ha : ∀ n, Continuous (a n))
    (hapos : ∀ n x, 0 < a n x)
    (aC : ℕ → PositiveCoefficient (centeredCube z R hR))
    (hAC : ∀ n, ((aC n).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] a n)
    (Jr : ℕ) (thetaR : SpatialCoordinates d → ℝ) (hsmooth : ContDiff ℝ ∞ thetaR)
    (hrange : ∀ x, 0 ≤ thetaR x ∧ thetaR x ≤ 1)
    (hzero : ∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
      Metric.infDist x (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) ≤
        R / (3 : ℝ) ^ Jr → thetaR x = 0)
    (hone : ∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
      3 * (R / (3 : ℝ) ^ Jr) ≤
        Metric.infDist x (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) →
          thetaR x = 1)
    (thetaRH1 : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hH1 : thetaRH1.toFun = thetaR)
    (I : Finset (OddGridIndex d (triadicHalf Jr)))
    (hI : ∀ k, k ∈ I ↔
      (closure (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d)) ∩
        {x : SpatialCoordinates d | 0 < thetaR x ∧ thetaR x < 1}).Nonempty) :
    ∃ collarH : ℕ → H1Function (centeredCube z R hR : Set (SpatialCoordinates d)),
      ∃ collarS : ℕ → S.space,
        ∃ collarC : ℕ → SpatialCoordinates d → ℝ,
          ∀ n : ℕ,
            (collarS n).val = sobolevDataOfH1 (collarH n) ∧
            ContinuousOn (collarC n)
              (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
            (collarS n).val.1 =ᵐ[
              volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
              collarC n ∧
            (∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
              0 ≤ collarC n x ∧ collarC n x ≤ 1) ∧
            (∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
              Metric.infDist x
                  (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) ≤
                  R / (3 : ℝ) ^ Jr →
                collarC n x = 0) ∧
            (∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
              3 * (R / (3 : ℝ) ^ Jr) ≤ Metric.infDist x
                  (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) →
                collarC n x = 1) ∧
            (∀ i : Fin d, ∀ᵐ x ∂volume.restrict
              (centeredCube z R hR : Set (SpatialCoordinates d)),
              3 * (R / (3 : ℝ) ^ Jr) < Metric.infDist x
                  (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) →
                (collarS n).val.2 i x = 0) ∧
            (∀ k : OddGridIndex d (triadicHalf Jr),
              IsWeaklyHarmonicOn (a n)
                (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d))
                ((collarH n).restrict
                  (oddGridCell z R hR (triadicHalf Jr) k).isOpen
                  (oddGridCell_subset z hR (triadicHalf Jr) k)) ∧
              HasZeroTraceDifferenceOn
                (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d))
                ((collarH n).restrict
                  (oddGridCell z R hR (triadicHalf Jr) k).isOpen
                  (oddGridCell_subset z hR (triadicHalf Jr) k))
                (thetaRH1.restrict
                  (oddGridCell z R hR (triadicHalf Jr) k).isOpen
                  (oddGridCell_subset z hR (triadicHalf Jr) k))) ∧
            responseForm S (aC n) (collarS n) (collarS n) ≤
              ∑ k ∈ I, cellDirichletInfimum (a n)
                  (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d))
                  (thetaRH1.restrict
                    (oddGridCell z R hR (triadicHalf Jr) k).isOpen
                    (oddGridCell_subset z hR (triadicHalf Jr) k)) := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hρ : R / (2 * (triadicHalf Jr : ℝ) + 1) = R / (3 : ℝ) ^ Jr := by
    rw [triadic_denominator]
  have hρpos : 0 < R / (3 : ℝ) ^ Jr := by positivity
  let φ := aux_lem_cutoffs_collar_datum z hR thetaRH1
  have hφfun : φ.toFun = (centeredCube z R hR : Set (SpatialCoordinates d)).indicator thetaR := by
    change (centeredCube z R hR : Set (SpatialCoordinates d)).indicator thetaRH1.toFun = _
    rw [hH1]
  obtain ⟨hφs', hφc', hφQ'⟩ := aux_lem_cutoffs_collar_indicator_smooth z R hR
    (R / (3 : ℝ) ^ Jr) hρpos thetaR hsmooth hzero
  have hφs : ContDiff ℝ ∞ φ.toFun := by rw [hφfun]; exact hφs'
  have hφc : HasCompactSupport φ.toFun := by rw [hφfun]; exact hφc'
  have hφQ : tsupport φ.toFun ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) := by
    rw [hφfun]; exact hφQ'
  have hφr : ∀ x, 0 ≤ φ.toFun x ∧ φ.toFun x ≤ 1 := by
    intro x
    rw [hφfun]
    by_cases hx : x ∈ (centeredCube z R hR : Set (SpatialCoordinates d))
    · rw [Set.indicator_of_mem hx]; exact hrange x
    · rw [Set.indicator_of_notMem hx]; exact ⟨le_refl 0, zero_le_one⟩
  have hφon : ∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
      φ.toFun x = thetaR x := by
    intro x hx
    rw [hφfun, Set.indicator_of_mem hx]
  have hmesh := fun n => aux_lem_cutoffs_mesh_package hd z R hR Jr (a n) (ha n) (hapos n)
    φ hφs hφc hφQ hφr
  choose w hwcont hwrange hwharm hwen hwconst hwpart using hmesh
  have hmem : ∀ n : ℕ, sobolevDataOfH1 (w n).toH1Function ∈ S.space := by
    intro n
    rw [hS]
    exact sobolevDataOfH1_mem_killed (w n)
  have hcellQ : ∀ k : OddGridIndex d (triadicHalf Jr),
      (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d)) ⊆
        (centeredCube z R hR : Set (SpatialCoordinates d)) :=
    fun k => oddGridCell_subset z hR (triadicHalf Jr) k
  have hfunk : ∀ k : OddGridIndex d (triadicHalf Jr),
      ∀ x ∈ (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d)),
        (φ.restrict (oddGridCell z R hR (triadicHalf Jr) k).isOpen
            (oddGridCell_subset z hR (triadicHalf Jr) k)).toFun x =
          (thetaRH1.restrict (oddGridCell z R hR (triadicHalf Jr) k).isOpen
            (oddGridCell_subset z hR (triadicHalf Jr) k)).toFun x := by
    intro k x hx
    change φ.toFun x = thetaRH1.toFun x
    rw [hφon x (hcellQ k hx), hH1]
  have hgradk : ∀ k : OddGridIndex d (triadicHalf Jr),
      (φ.restrict (oddGridCell z R hR (triadicHalf Jr) k).isOpen
          (oddGridCell_subset z hR (triadicHalf Jr) k)).grad =
        (thetaRH1.restrict (oddGridCell z R hR (triadicHalf Jr) k).isOpen
          (oddGridCell_subset z hR (triadicHalf Jr) k)).grad := fun k => rfl
  -- vanishing in the inner collar
  have hC0 : ∀ n, ∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
      Metric.infDist x (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) ≤
        R / (3 : ℝ) ^ Jr → (w n).toH1Function.toFun x = 0 := by
    intro n x hx hdist
    rw [← hρ] at hdist
    obtain ⟨k, hxk, hy⟩ := aux_lem_cutoffs_zero_layer_cell hd1 z R hR (triadicHalf Jr) x hx hdist
    have hc : ∀ y ∈ (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d)),
        φ.toFun y = 0 := by
      intro y hyk
      rw [hφon y (hcellQ k hyk)]
      exact hzero y (hcellQ k hyk) (by rw [← hρ]; exact hy y hyk)
    exact (hwconst n k 0 hc).1 x hxk
  -- equal to one deep inside
  have hC1 : ∀ n, ∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
      3 * (R / (3 : ℝ) ^ Jr) ≤
        Metric.infDist x (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) →
      (w n).toH1Function.toFun x = 1 := by
    intro n x hx hdist
    rw [← hρ] at hdist
    obtain ⟨k, hxk, hy⟩ := aux_lem_cutoffs_one_region_cell hd1 z R hR (triadicHalf Jr) x hx hdist
    have hc : ∀ y ∈ (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d)),
        φ.toFun y = 1 := by
      intro y hyk
      obtain ⟨hyQ, hyd⟩ := hy y (subset_closure hyk)
      rw [hφon y hyQ]
      exact hone y hyQ (by rw [← hρ]; exact hyd)
    exact (hwconst n k 1 hc).1 x hxk
  -- the gradient vanishes deep inside
  have hCg : ∀ n, ∀ i : Fin d, ∀ᵐ x ∂volume.restrict
      (centeredCube z R hR : Set (SpatialCoordinates d)),
      3 * (R / (3 : ℝ) ^ Jr) < Metric.infDist x
          (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) →
        ((sobolevDataOfH1 (w n).toH1Function).2 i : DomainL2 (centeredCube z R hR)) x = 0 := by
    intro n i
    have hsd := sobolevDataOfH1_snd_coeFn (w n).toH1Function i
    have hcover : ∀ᵐ x ∂(volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))),
        x ∈ ⋃ k : OddGridIndex d (triadicHalf Jr),
          (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d)) := by
      have h1 := (oddGrid_union_ae_eq z hR (triadicHalf Jr)).mem_iff
      have h2 : ∀ᵐ x ∂(volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))),
          x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) :=
        ae_restrict_mem (centeredCube z R hR).isOpen.measurableSet
      filter_upwards [ae_restrict_of_ae h1, h2] with x hx hxQ
      exact hx.mpr hxQ
    have hcell : ∀ k : OddGridIndex d (triadicHalf Jr),
        ∀ᵐ x ∂(volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))),
          x ∈ (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d)) →
          3 * (R / (3 : ℝ) ^ Jr) < Metric.infDist x
              (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) →
            (w n).toH1Function.grad x i = 0 := by
      intro k
      by_cases hdeep : ∃ y ∈ (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d)),
          3 * (R / (3 : ℝ) ^ Jr) < Metric.infDist y
            (frontier (centeredCube z R hR : Set (SpatialCoordinates d)))
      · obtain ⟨y, hyk, hyd⟩ := hdeep
        rw [← hρ] at hyd
        have hgood := aux_lem_cutoffs_deep_cell hd1 z R hR (triadicHalf Jr) k y hyk hyd
        have hc : ∀ y ∈ (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d)),
            φ.toFun y = 1 := by
          intro y' hy'k
          obtain ⟨hyQ, hyd'⟩ := hgood y' (subset_closure hy'k)
          rw [hφon y' hyQ]
          exact hone y' hyQ (by rw [← hρ]; exact hyd')
        have hg := (hwconst n k 1 hc).2
        have hg' := (ae_restrict_iff' (oddGridCell z R hR (triadicHalf Jr) k).isOpen.measurableSet).mp hg
        filter_upwards [ae_restrict_of_ae hg'] with x hx hxk _
        exact hx hxk i
      · push Not at hdeep
        filter_upwards with x hxk hxd
        exact absurd hxd (not_lt.mpr (hdeep x hxk))
    have hall := ae_all_iff.mpr hcell
    filter_upwards [hsd, hall, hcover] with x hx hxall hxcov hxd
    rcases mem_iUnion.mp hxcov with ⟨k, hxk⟩
    rw [hx]
    exact hxall k hxk hxd
  -- the energy is carried by the transition cells
  have hCE : ∀ n, energy (a n) (centeredCube z R hR : Set (SpatialCoordinates d))
      (w n).toH1Function ≤
      ∑ k ∈ I, cellDirichletInfimum (a n)
          (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d))
          (thetaRH1.restrict (oddGridCell z R hR (triadicHalf Jr) k).isOpen
            (oddGridCell_subset z hR (triadicHalf Jr) k)) := by
    intro n
    rw [hwpart n]
    have hcellEq : ∀ k : OddGridIndex d (triadicHalf Jr),
        energy (a n) (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d))
            ((w n).toH1Function.restrict (oddGridCell z R hR (triadicHalf Jr) k).isOpen
              (oddGridCell_subset z hR (triadicHalf Jr) k)) =
          cellDirichletInfimum (a n)
            (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d))
            (thetaRH1.restrict (oddGridCell z R hR (triadicHalf Jr) k).isOpen
              (oddGridCell_subset z hR (triadicHalf Jr) k)) := by
      intro k
      rw [hwen n k]
      exact aux_lem_cutoffs_cellInf_congr _ (oddGridCell z R hR (triadicHalf Jr) k).isOpen
        (a n) _ _ (hfunk k) (hgradk k)
    have hzeroE : ∀ k ∈ (Finset.univ : Finset (OddGridIndex d (triadicHalf Jr))), k ∉ I →
        energy (a n) (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d))
            ((w n).toH1Function.restrict (oddGridCell z R hR (triadicHalf Jr) k).isOpen
              (oddGridCell_subset z hR (triadicHalf Jr) k)) = 0 := by
      intro k _ hkI
      have hnot := fun h => hkI ((hI k).mpr h)
      rcases aux_lem_cutoffs_nontransition_const z hR (triadicHalf Jr) k thetaR
        hsmooth.continuous hrange hnot with h0 | h1
      · refine aux_lem_cutoffs_energy_zero _ (a n) _ (hwconst n k 0 ?_).2
        intro y hy
        rw [hφon y (hcellQ k hy)]
        exact h0 y (subset_closure hy)
      · refine aux_lem_cutoffs_energy_zero _ (a n) _ (hwconst n k 1 ?_).2
        intro y hy
        rw [hφon y (hcellQ k hy)]
        exact h1 y (subset_closure hy)
    rw [← Finset.sum_subset (Finset.subset_univ I) hzeroE]
    exact le_of_eq (Finset.sum_congr rfl fun k _ => hcellEq k)
  have hCT : ∀ n (k : OddGridIndex d (triadicHalf Jr)),
      HasZeroTraceDifferenceOn
        (oddGridCell z R hR (triadicHalf Jr) k : Set (SpatialCoordinates d))
        ((w n).toH1Function.restrict (oddGridCell z R hR (triadicHalf Jr) k).isOpen
          (oddGridCell_subset z hR (triadicHalf Jr) k))
        (thetaRH1.restrict (oddGridCell z R hR (triadicHalf Jr) k).isOpen
          (oddGridCell_subset z hR (triadicHalf Jr) k)) := fun n k =>
    aux_lem_cutoffs_traceDiff_congr (oddGridCell z R hR (triadicHalf Jr) k).isOpen
      (hwharm n k).2 (hfunk k) (by rw [hgradk k])
  refine ⟨fun n => (w n).toH1Function, fun n => ⟨sobolevDataOfH1 (w n).toH1Function, hmem n⟩,
    fun n => (w n).toH1Function.toFun, fun n => ?_⟩
  refine ⟨rfl, hwcont n, sobolevDataOfH1_fst_coeFn (w n).toH1Function, hwrange n,
    hC0 n, hC1 n, hCg n, fun k => ⟨(hwharm n k).1, hCT n k⟩, ?_⟩
  rw [aux_lem_cutoffs_resp_energy z hR S (aC n) (a n) (hAC n) (w n).toH1Function _ rfl]
  exact hCE n


/-! ### Rep helpers of the mesh/collar step -/

/-- The Dirichlet infimum depends only on the datum's values on the cell and
its weak gradient there up to null sets. -/
theorem aux_lem_cutoffs_cellInf_congr_ae {d : ℕ} (W : Set (SpatialCoordinates d))
    (hW : IsOpen W) (a : SpatialCoordinates d → ℝ) (h h' : H1Function W)
    (hfun : ∀ x ∈ W, h.toFun x = h'.toFun x)
    (hgrad : h.grad =ᵐ[volume.restrict W] h'.grad) :
    cellDirichletInfimum a W h = cellDirichletInfimum a W h' := by
  unfold cellDirichletInfimum
  congr 1
  ext e
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, aux_lem_cutoffs_traceDiff_congr hW hu hfun hgrad, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, aux_lem_cutoffs_traceDiff_congr hW hu (fun x hx => (hfun x hx).symm)
      hgrad.symm, rfl⟩

/-- Identification of a cell solution with a catalogue solution on the same
cube (possibly presented as a different set expression). -/
theorem aux_lem_cutoffs_cell_transfer {d : ℕ} [NeZero d] {W W' : Set (SpatialCoordinates d)}
    (hWW : W' = W) (hWdom : IsOpenBoundedConvexDomain W) (hne : W.Nonempty)
    (a : SpatialCoordinates d → ℝ) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField a))
    (θ0 : H1Function W) (θ1 : H1Function W') (hθ : ∀ x, θ0.toFun x = θ1.toFun x)
    (u : H1Function W') (hu : IsWeaklyHarmonicOn a W' u)
    (hut : HasZeroTraceDifferenceOn W' u θ1)
    (w : H1Function W) (hw : IsWeaklyHarmonicOn a W w)
    (hwt : HasZeroTraceDifferenceOn W w θ0) :
    w.toFun =ᵐ[volume.restrict W] u.toFun ∧ w.grad =ᵐ[volume.restrict W] u.grad ∧
      energy a W w = cellDirichletInfimum a W' θ1 := by
  subst hWW
  have hg : θ0.grad =ᵐ[volume.restrict W'] θ1.grad :=
    lane2_grad_ae_eq_of_ae_eq' hWdom.isOpen hWdom.isBoundedDomain.isBounded θ0 θ1
      (Filter.Eventually.of_forall hθ)
  have hut' : HasZeroTraceDifferenceOn W' u θ0 :=
    aux_lem_cutoffs_traceDiff_congr hWdom.isOpen hut (fun x _ => (hθ x).symm) hg.symm
  obtain ⟨h1, h2⟩ := SubdiffusiveProcess.CoarseGrainingVocab.ae_eq_of_isWeaklyHarmonicOn_of_hasZeroTraceDifferenceOn
    hWdom hne hEll hw hwt hu hut'
  refine ⟨h1, h2, ?_⟩
  rw [energy_eq_sInf_sameTrace_of_isWeaklyHarmonicOn hWdom hne hEll hw hwt]
  exact aux_lem_cutoffs_cellInf_congr_ae W' hWdom.isOpen a θ0 θ1 (fun x _ => hθ x) hg

/-- Energy measures on equal sets with a.e. equal densities coincide. -/
theorem aux_lem_cutoffs_density_transfer {d : ℕ} {W W' : Set (SpatialCoordinates d)}
    (hWW : W' = W) (g g' : SpatialCoordinates d → ENNReal)
    (hg : g' =ᵐ[volume.restrict W'] g) (s : Set (SpatialCoordinates d)) :
    ((volume.restrict W).withDensity g) s = ((volume.restrict W').withDensity g') s := by
  subst hWW
  rw [withDensity_congr_ae hg]

/-- Two functions continuous on the closure of an open set and a.e. equal on
it agree on the closure. -/
theorem aux_lem_cutoffs_eqOn_closure {d : ℕ} (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (f g : SpatialCoordinates d → ℝ) (hf : ContinuousOn f (closure U))
    (hg : ContinuousOn g (closure U)) (hae : f =ᵐ[volume.restrict U] g) :
    ∀ x ∈ closure U, f x = g x := by
  have hfgU : EqOn f g U := fun x hx =>
    lane2_eqOn_of_ae_eq_of_continuousOn hU (hf.mono subset_closure) (hg.mono subset_closure)
      hae x hx
  exact fun x hx => EqOn.of_subset_closure hfgU hf hg subset_closure subset_rfl hx

/-- Uniform cellwise bounds for the plateau mesh, from the represented cell
solutions of the catalogue cube equal to the mesh cell. -/
theorem aux_lem_cutoffs_rep_plateau_cell
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Cext beta alpha eta t : ℝ) (orders : Finset ℝ)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
    (J : Type) [Countable J] [DecidableEq J] (j0 : J)
    (z : J → SpatialCoordinates d) (rad : J → ℝ)
    (hrad : ∀ j, 0 < rad j)
    (S : ∀ j, ResponseSpace (centeredCube (z j) (rad j) (hrad j)))
    (D : ∀ j, Submodule ℚ
      (DomainL2 (centeredCube (z j) (rad j) (hrad j))))
    [hDc : ∀ j, Countable (D j)]
    (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
    (T : J → Type) [hTc : ∀ j, Countable (T j)]
    (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
    (thetaH1 : ∀ j, T j →
      Homogenization.H1Function
        (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (usrc : ∀ j, (D j) → ℕ → Ω → (S j).space)
    (srcRep : ∀ j, (D j) → ℕ → Ω → SpatialCoordinates d → ℝ)
    (ucell : ∀ j, T j → ℕ → Ω →
      Homogenization.H1Function
        (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (E : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Index : Type) [Countable Index]
    (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
    (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
    (coercivityKey extensionKey lambdaKey : J → Index)
    (sourceResponseKey sourceGrowthKey sourceHolderKey :
      ∀ j, (D j) → Index)
    (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
    (Grid : Type) [Countable Grid]
    (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J)
    (gridKey : Grid → Index)
    (hrepresented :
      _root_.SubdiffusiveProcess.Paper.conv_represented_estimates d hd M H Ω P cutoff env J j0 z rad hrad
        S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E
        Index resp respLim constants G coercivityKey extensionKey lambdaKey
        sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey
        cellGrowthKey cellHolderKey Grid origin gridRoot gridKey)
    (omega : Ω) (homega : omega ∈ G) (b : T j0) (Jmesh : ℕ)
    (k : OddGridIndex d (triadicHalf Jmesh)) :
    ∃ E Gr Ho : ℝ, 0 ≤ E ∧ 0 ≤ Gr ∧ 0 ≤ Ho ∧
      ∀ (n : ℕ) (w : H1Function
          (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jmesh) k :
            Set (SpatialCoordinates d))),
        IsWeaklyHarmonicOn (cutoffCoefficient M H (env n omega) (cutoff n))
          (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jmesh) k :
            Set (SpatialCoordinates d)) w →
        HasZeroTraceDifferenceOn
          (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jmesh) k :
            Set (SpatialCoordinates d)) w
          ((thetaH1 j0 b).restrict
            (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jmesh) k).isOpen
            (oddGridCell_subset (z j0) (hrad j0) (triadicHalf Jmesh) k)) →
        ContinuousOn w.toFun
          (closure (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jmesh) k :
            Set (SpatialCoordinates d))) →
        energy (cutoffCoefficient M H (env n omega) (cutoff n))
            (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jmesh) k :
              Set (SpatialCoordinates d)) w ≤ E ∧
        (∀ x ∈ closure (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jmesh) k :
            Set (SpatialCoordinates d)), ∀ r : ℝ, 0 < r → r ≤ 1 →
          ((volume.restrict (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jmesh) k :
              Set (SpatialCoordinates d))).withDensity
            (fun y => ENNReal.ofReal (cutoffCoefficient M H (env n omega) (cutoff n) y *
              ∑ i : Fin d, (w.grad y i) ^ 2)))
            (Metric.ball x r) ≤ ENNReal.ofReal (Gr * r ^ t)) ∧
        (∀ x ∈ closure (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jmesh) k :
            Set (SpatialCoordinates d)),
          ∀ y ∈ closure (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jmesh) k :
            Set (SpatialCoordinates d)),
          |w.toFun x - w.toFun y| ≤
            Ho * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha) := by
  classical
  have : NeZero d := ⟨by omega⟩
  obtain ⟨-, -, hA3, -, -, -, -, -, -, hseq, hsub, hcenter, hscale, hcomplete, -, -, -, -, -, -,
    htheta, -, htransfer, -, -, -, -, -, hF, -, -, -, -, -, hL⟩ := hrepresented
  have halpha : 0 < alpha := by linarith [hA3.1, hA3.2]
  obtain ⟨j, hjz, hjr⟩ := aux_cutoffs_odd_cell_catalogue_of_geometry j0 z rad hrad (z j0) (rad j0)
    (hrad j0) rfl rfl hcenter hscale hcomplete Jmesh k
  have hWW : (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)) =
      (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jmesh) k : Set (SpatialCoordinates d)) := by
    change Metric.ball (z j) (rad j / 2) =
      Metric.ball (oddGridCenter (z j0) (rad j0) (triadicHalf Jmesh) k)
        (rad j0 / (2 * (triadicHalf Jmesh : ℝ) + 1) / 2)
    rw [hjz, hjr, triadic_denominator]
  obtain ⟨h', hh'⟩ := htransfer j0 j (hsub j) b
  obtain ⟨-, -, -, hconv, hbdd⟩ := hseq
  obtain ⟨Mr, hMr⟩ := (hconv (cellResponseKey j h') omega homega).bddAbove_range
  obtain ⟨Mg, hMg⟩ := hbdd (cellGrowthKey j h') omega homega
  obtain ⟨Mh, hMh⟩ := hbdd (cellHolderKey j h') omega homega
  have hMg0 : 0 ≤ Mg := (abs_nonneg _).trans (hMg 0)
  have hMh0 : 0 ≤ Mh := (abs_nonneg _).trans (hMh 0)
  set c2 : ℝ := _root_.SubdiffusiveProcess.EllipticRegularity.c2Norm
    (closure (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d))) (theta j h')
    with hc2def
  have hc2 : 0 ≤ c2 := by
    rw [hc2def]
    unfold _root_.SubdiffusiveProcess.EllipticRegularity.c2Norm
    refine add_nonneg (add_nonneg ?_ ?_) ?_ <;> apply Real.sSup_nonneg <;>
      rintro v ⟨x, -, rfl⟩ <;> positivity
  refine ⟨max Mr 0, Mg * c2 ^ 2, Mh * c2, le_max_right _ _, by positivity, by positivity, ?_⟩
  intro n w hw hwt hwc
  obtain ⟨-, hU⟩ := hF j n omega homega
  obtain ⟨huh, hut, huc, -, hur⟩ := hU h'
  obtain ⟨hcont, hpos⟩ := aux_lem_cutoffs_cutoffCoefficient_cont_pos M H (env n omega) (cutoff n)
  obtain ⟨lam, Lam, hlam, hbd⟩ := aux_lem_cutoffs_pos_bounds _ hcont hpos
    (closure (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jmesh) k :
      Set (SpatialCoordinates d)))
    (lane2_isCompact_closure_centeredCube _ _)
  have hEll : IsEllipticFieldOn lam Lam
      (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jmesh) k : Set (SpatialCoordinates d))
      (scalarCoeffField (cutoffCoefficient M H (env n omega) (cutoff n))) :=
    lane2_isEllipticFieldOn_scalar
      (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jmesh) k).isOpen.measurableSet
      hcont.measurable hlam (fun x hx => hbd x (subset_closure hx))
  have hθ : ∀ x, ((thetaH1 j0 b).restrict
      (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jmesh) k).isOpen
      (oddGridCell_subset (z j0) (hrad j0) (triadicHalf Jmesh) k)).toFun x =
        (thetaH1 j h').toFun x := by
    intro x
    change (thetaH1 j0 b).toFun x = (thetaH1 j h').toFun x
    rw [(htheta j0 b).2, (htheta j h').2, hh']
  have htr := aux_lem_cutoffs_cell_transfer hWW (aux_lem_cutoffs_cell_dom _ _ _ k)
    (aux_lem_cutoffs_cell_nonempty _ _ _ k) _ hEll _ (thetaH1 j h') hθ
    (ucell j h' n omega) huh hut w hw hwt
  obtain ⟨hfun, hgrad, hen⟩ := htr
  have hrestr : volume.restrict
      (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jmesh) k : Set (SpatialCoordinates d)) =
      volume.restrict (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)) := by
    rw [hWW]
  have hclos : closure (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jmesh) k :
      Set (SpatialCoordinates d)) =
      closure (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)) := by
    rw [hWW]
  refine ⟨?_, ?_, ?_⟩
  · rw [hen, ← hur]
    exact (hMr ⟨n, rfl⟩).trans (le_max_left _ _)
  · intro x hx r hr hr1
    have hgrad' := hgrad
    rw [hrestr] at hgrad'
    have hden : (fun y => ENNReal.ofReal
        ((_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n omega) (cutoff n) (z j) (hrad j)).val y *
          ∑ i : Fin d, (((sobolevDataOfH1 (ucell j h' n omega)).2 i) y) ^ 2))
        =ᵐ[volume.restrict (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d))]
        (fun y => ENNReal.ofReal (cutoffCoefficient M H (env n omega) (cutoff n) y *
          ∑ i : Fin d, (w.grad y i) ^ 2)) := by
      have hsd := ae_all_iff.mpr fun i => sobolevDataOfH1_snd_coeFn (ucell j h' n omega) i
      filter_upwards [aux_lem_cutoffs_positiveCoefficient_ae M H (env n omega) (cutoff n)
        (z j) (hrad j), hsd, hgrad'] with y hy1 hy2 hy3
      rw [hy1]
      congr 2
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hy2 i, hy3]
    rw [aux_lem_cutoffs_density_transfer hWW _ _ hden]
    refine ((hL j h' n omega homega).1 x (hclos ▸ hx) r hr hr1).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have hc := (le_abs_self _).trans (hMg n)
    have hpow : 0 ≤ c2 ^ 2 * r ^ t := mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hr.le _)
    calc constants (cellGrowthKey j h') n omega * c2 ^ 2 * r ^ t
        = constants (cellGrowthKey j h') n omega * (c2 ^ 2 * r ^ t) := by ring
      _ ≤ Mg * (c2 ^ 2 * r ^ t) := mul_le_mul_of_nonneg_right hc hpow
      _ = Mg * c2 ^ 2 * r ^ t := by ring
  · have hucl : ContinuousOn (ucell j h' n omega).toFun
        (closure (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jmesh) k :
          Set (SpatialCoordinates d))) := hclos ▸ huc
    have heq := aux_lem_cutoffs_eqOn_closure _
      (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jmesh) k).isOpen _ _ hwc hucl hfun
    have hpairU := aux_lem_cutoffs_pair_bound_of_holder halpha
      (hL j h' n omega homega).2.1
      ((hL j h' n omega homega).2.2.trans
        (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hMh n)) hc2))
    intro x hx y hy
    rw [heq x hx, heq y hy]
    exact hpairU x (hclos ▸ hx) y (hclos ▸ hy)

/-- The represented plateau clause of `lem_cutoffs` at a represented point. -/
theorem aux_lem_cutoffs_rep_plateau
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Cext beta alpha eta t : ℝ) (orders : Finset ℝ)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
    (J : Type) [Countable J] [DecidableEq J] (j0 : J)
    (z : J → SpatialCoordinates d) (rad : J → ℝ)
    (hrad : ∀ j, 0 < rad j)
    (S : ∀ j, ResponseSpace (centeredCube (z j) (rad j) (hrad j)))
    (D : ∀ j, Submodule ℚ
      (DomainL2 (centeredCube (z j) (rad j) (hrad j))))
    [hDc : ∀ j, Countable (D j)]
    (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
    (T : J → Type) [hTc : ∀ j, Countable (T j)]
    (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
    (thetaH1 : ∀ j, T j →
      Homogenization.H1Function
        (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (usrc : ∀ j, (D j) → ℕ → Ω → (S j).space)
    (srcRep : ∀ j, (D j) → ℕ → Ω → SpatialCoordinates d → ℝ)
    (ucell : ∀ j, T j → ℕ → Ω →
      Homogenization.H1Function
        (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (E : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Index : Type) [Countable Index]
    (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
    (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
    (coercivityKey extensionKey lambdaKey : J → Index)
    (sourceResponseKey sourceGrowthKey sourceHolderKey :
      ∀ j, (D j) → Index)
    (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
    (Grid : Type) [Countable Grid]
    (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J)
    (gridKey : Grid → Index)
    (hrepresented :
      _root_.SubdiffusiveProcess.Paper.conv_represented_estimates d hd M H Ω P cutoff env J j0 z rad hrad
        S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E
        Index resp respLim constants G coercivityKey extensionKey lambdaKey
        sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey
        cellGrowthKey cellHolderKey Grid origin gridRoot gridKey)
    (omega : Ω) (homega : omega ∈ G) :
    let Q := centeredCube (z j0) (rad j0) (hrad j0)
    let S0 := S j0
    let aN := fun (omega : Ω) (n : ℕ) =>
      _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n omega) (cutoff n)
        (z j0) (hrad j0)
    let rawAN := fun (omega : Ω) (n : ℕ) =>
      cutoffCoefficient M H (env n omega) (cutoff n)
    (∀ b : T j0, ∀ K O W : Set (SpatialCoordinates d), ∀ Jmesh : ℕ,
              IsCompact K → IsOpen O →
              closure O ⊆ (Q : Set (SpatialCoordinates d)) →
              IsOpen W → K ⊆ W → W ⊆ O →
              (∀ x : SpatialCoordinates d,
                0 ≤ theta j0 b x ∧ theta j0 b x ≤ 1) →
              (∀ x ∈ W, theta j0 b x = 1) →
              tsupport (theta j0 b) ⊆ O →
              (∀ k : OddGridIndex d (triadicHalf Jmesh),
                (closure
                    (oddGridCell (z j0) (rad j0) (hrad j0)
                      (triadicHalf Jmesh) k : Set (SpatialCoordinates d)) ∩
                    {x : SpatialCoordinates d |
                      0 < theta j0 b x ∧ theta j0 b x < 1}).Nonempty →
                  closure
                      (oddGridCell (z j0) (rad j0) (hrad j0)
                        (triadicHalf Jmesh) k : Set (SpatialCoordinates d)) ⊆
                    O \ K) →
              ∃ chiH : ℕ → Homogenization.H1Function
                  (Q : Set (SpatialCoordinates d)),
                ∃ chiS : ℕ → S0.space,
                  ∃ chic : ℕ → SpatialCoordinates d → ℝ,
                    ∃ V : Set (SpatialCoordinates d),
                      ∃ Benergy Ball Bholder : ℝ,
                        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧
                        0 ≤ Benergy ∧ 0 ≤ Ball ∧ 0 ≤ Bholder ∧
                        (∀ n : ℕ,
                          (chiS n).val = sobolevDataOfH1 (chiH n) ∧
                          ContinuousOn (chic n)
                            (closure (Q : Set (SpatialCoordinates d))) ∧
                          (chiS n).val.1 =ᵐ[
                            volume.restrict (Q : Set (SpatialCoordinates d))]
                            chic n ∧
                          (∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
                            0 ≤ chic n x ∧ chic n x ≤ 1) ∧
                          (∀ x ∈ V, chic n x = 1) ∧
                          (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                            x ∉ O → chic n x = 0) ∧
                          (∀ k : OddGridIndex d (triadicHalf Jmesh),
                            IsWeaklyHarmonicOn (rawAN omega n)
                              (oddGridCell (z j0) (rad j0) (hrad j0)
                                (triadicHalf Jmesh) k : Set (SpatialCoordinates d))
                              ((chiH n).restrict
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k).isOpen
                                (oddGridCell_subset (z j0) (hrad j0)
                                  (triadicHalf Jmesh) k)) ∧
                            HasZeroTraceDifferenceOn
                              (oddGridCell (z j0) (rad j0) (hrad j0)
                                (triadicHalf Jmesh) k : Set (SpatialCoordinates d))
                              ((chiH n).restrict
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k).isOpen
                                (oddGridCell_subset (z j0) (hrad j0)
                                  (triadicHalf Jmesh) k))
                              ((thetaH1 j0 b).restrict
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k).isOpen
                                (oddGridCell_subset (z j0) (hrad j0)
                                  (triadicHalf Jmesh) k))) ∧
                          (∀ k : OddGridIndex d (triadicHalf Jmesh),
                            (∃ c : ℝ, ∀ x ∈ closure
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                              theta j0 b x = c) →
                              ∀ i : Fin d, ∀ᵐ x ∂volume.restrict
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                                (chiS n).val.2 i x = 0) ∧
                          responseForm S0 (aN omega n) (chiS n) (chiS n) ≤ Benergy ∧
                          (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), ∀ s : ℝ,
                            0 < s → s ≤ 1 →
                            ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
                              (fun y => ENNReal.ofReal
                                ((aN omega n).val y *
                                  ∑ i : Fin d, ((chiS n).val.2 i y) ^ 2)))
                              (Metric.ball x s) ≤ ENNReal.ofReal (Ball * s ^ t)) ∧
                          _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
                            (closure (Q : Set (SpatialCoordinates d))) (chic n) ∧
                          _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
                            (closure (Q : Set (SpatialCoordinates d))) (chic n) ≤
                            Bholder) ∧
                        (∃ sigma : ℕ → ℕ, ∃ chiLim : SpatialCoordinates d → ℝ,
                          StrictMono sigma ∧
                          ContinuousOn chiLim
                            (closure (Q : Set (SpatialCoordinates d))) ∧
                          TendstoUniformlyOn (fun n => chic (sigma n)) chiLim atTop
                            (closure (Q : Set (SpatialCoordinates d))) ∧
                          (∀ k : OddGridIndex d (triadicHalf Jmesh),
                            (∃ c : ℝ, ∀ x ∈ closure
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                              theta j0 b x = c) →
                              ∀ x ∈ closure
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                                chiLim x = theta j0 b x))) := by
  intro Q S0 aN rawAN b K O W Jmesh _hK hO hOQ _hW hKW hWO hθr hθW hθO htrans
  have : NeZero d := ⟨by omega⟩
  have hrep := hrepresented
  obtain ⟨⟨htlow, -⟩, hA2, hA3, -, -, -, -, -, -, -, -, -, -, -, -, -, hSk, -, -, -,
    htheta, -⟩ := hrep
  have ht : 0 ≤ t := by
    have : (1 : ℝ) ≤ (d : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith
    linarith
  have halpha : 0 < alpha := by linarith [hA3.1, hA3.2]
  exact aux_lem_cutoffs_plateau_generic hd (z j0) (rad j0) (hrad j0) (S j0) (hSk j0)
    (fun n => cutoffCoefficient M H (env n omega) (cutoff n))
    (fun n => (aux_lem_cutoffs_cutoffCoefficient_cont_pos M H (env n omega) (cutoff n)).1)
    (fun n => (aux_lem_cutoffs_cutoffCoefficient_cont_pos M H (env n omega) (cutoff n)).2)
    (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n omega) (cutoff n) (z j0) (hrad j0))
    (fun n => aux_lem_cutoffs_positiveCoefficient_ae M H (env n omega) (cutoff n) (z j0)
      (hrad j0))
    t alpha ht halpha (theta j0 b) (thetaH1 j0 b) (htheta j0 b).2 (htheta j0 b).1
    K O W Jmesh hO hOQ hKW hWO hθr hθW hθO htrans
    (fun k => aux_lem_cutoffs_rep_plateau_cell d hd M H Cext beta alpha eta t orders Ω P cutoff
      env J j0 z rad hrad S D f T theta thetaH1 usrc srcRep ucell E Index resp respLim constants
      G coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey hrepresented omega
      homega b Jmesh k)


/-! ### RepCollar helpers of the mesh/collar step -/

/-- Restricting one datum to equal open sets gives the same Dirichlet infimum. -/
theorem aux_lem_cutoffs_cellInf_restrict_eq {d : ℕ} {W W' U : Set (SpatialCoordinates d)}
    (hWW : W' = W) (hW : IsOpen W) (hW' : IsOpen W') (hWU : W ⊆ U) (hW'U : W' ⊆ U)
    (a : SpatialCoordinates d → ℝ) (θ : H1Function U) :
    cellDirichletInfimum a W (θ.restrict hW hWU) =
      cellDirichletInfimum a W' (θ.restrict hW' hW'U) := by
  subst hWW
  rfl

/-- The Dirichlet infimum is at most the energy of the datum itself. -/
theorem aux_lem_cutoffs_cellInf_le_datum {d : ℕ} (W : Set (SpatialCoordinates d))
    (a : SpatialCoordinates d → ℝ) (ha : ∀ x ∈ W, 0 ≤ a x) (hW : MeasurableSet W)
    (θ : H1Function W) :
    cellDirichletInfimum a W θ ≤ energy a W θ := by
  unfold cellDirichletInfimum
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro e ⟨u, -, rfl⟩
    unfold energy
    apply setIntegral_nonneg hW
    intro x hx
    exact mul_nonneg (ha x hx) (by
      unfold Homogenization.vecDot
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _)
  · refine ⟨θ, ⟨0, fun x => ?_, fun x => ?_⟩, rfl⟩
    · change θ.toFun x = θ.toFun x + (0 : H1Function W).toFun x
      simp
    · change θ.grad x = θ.grad x + (0 : H1Function W).grad x
      simp




theorem aux_lem_cutoffs_cAlphaNorm_nonneg {d : ℕ} (b : ℝ) (S : Set (SpatialCoordinates d))
    (f : SpatialCoordinates d → ℝ) : 0 ≤ _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm b S f := by
  unfold _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm _root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet
  apply add_nonneg
  · apply Real.sSup_nonneg
    rintro v ⟨x, -, rfl⟩
    exact abs_nonneg _
  · apply Real.sSup_nonneg
    rintro v ⟨x, -, y, -, -, rfl⟩
    exact div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)

/-- Cell boundary quotient norms are nonnegative. -/
theorem aux_lem_cutoffs_quotientNorm_nonneg {d : ℕ} (beta : ℝ) (z : SpatialCoordinates d)
    (r : ℝ) (g : SpatialCoordinates d → ℝ) : 0 ≤ cellBoundaryQuotientNorm beta z r g := by
  unfold cellBoundaryQuotientNorm quotientCBetaNorm
  apply Real.sInf_nonneg
  rintro v ⟨c, rfl⟩
  exact aux_lem_cutoffs_cAlphaNorm_nonneg _ _ _

/-- Transition-cell cost of the collar datum in the three regimes: coarse
superunit cells (extension key in the finite selection), represented grid scales
above the ultraviolet cutoff (grid key), and cells below the ultraviolet cutoff
(direct coefficient maximum). -/
theorem aux_lem_cutoffs_rep_collar_cell
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Cext beta alpha eta t : ℝ) (orders : Finset ℝ)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
    (J : Type) [Countable J] [DecidableEq J] (j0 : J)
    (z : J → SpatialCoordinates d) (rad : J → ℝ)
    (hrad : ∀ j, 0 < rad j)
    (S : ∀ j, ResponseSpace (centeredCube (z j) (rad j) (hrad j)))
    (D : ∀ j, Submodule ℚ
      (DomainL2 (centeredCube (z j) (rad j) (hrad j))))
    [hDc : ∀ j, Countable (D j)]
    (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
    (T : J → Type) [hTc : ∀ j, Countable (T j)]
    (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
    (thetaH1 : ∀ j, T j →
      Homogenization.H1Function
        (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (usrc : ∀ j, (D j) → ℕ → Ω → (S j).space)
    (srcRep : ∀ j, (D j) → ℕ → Ω → SpatialCoordinates d → ℝ)
    (ucell : ∀ j, T j → ℕ → Ω →
      Homogenization.H1Function
        (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (E : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Index : Type) [Countable Index]
    (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
    (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
    (coercivityKey extensionKey lambdaKey : J → Index)
    (sourceResponseKey sourceGrowthKey sourceHolderKey :
      ∀ j, (D j) → Index)
    (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
    (Grid : Type) [Countable Grid]
    (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J)
    (gridKey : Grid → Index)
    (hrepresented :
      _root_.SubdiffusiveProcess.Paper.conv_represented_estimates d hd M H Ω P cutoff env J j0 z rad hrad
        S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E
        Index resp respLim constants G coercivityKey extensionKey lambdaKey
        sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey
        cellGrowthKey cellHolderKey Grid origin gridRoot gridKey)
    (Cgrad : ℝ) (hCgrad : 0 < Cgrad) (κ : ℤ) (hκ : rad j0 = (3 : ℝ) ^ κ)
    (g0 : Grid) (hg0 : gridRoot g0 = j0 ∧ origin g0 = z j0)
    (omega : Ω) (homega : omega ∈ G) (n : ℕ) (Kn : ℝ) (hKn : 0 ≤ Kn)
    (hgrid : constants (gridKey g0) n omega ≤ Kn)
    (Mhi : ℝ)
    (hMhi : ∀ x ∈ closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
      cutoffCoefficient M H (env n omega) (cutoff n) x ≤ Mhi)
    (hMK : Mhi ≤ Kn * (3 : ℝ) ^ (((cutoff n : ℕ) : ℝ) * eta))
    (Jr : ℕ) (k : OddGridIndex d (triadicHalf Jr)) (j_cell : J)
    (hjz : z j_cell = oddGridCenter (z j0) (rad j0) (triadicHalf Jr) k)
    (hjr : rad j_cell = rad j0 / (3 : ℝ) ^ Jr)
    (hcoarse : (Jr : ℤ) < κ → constants (extensionKey j_cell) n omega ≤ Kn)
    (thetaR : SpatialCoordinates d → ℝ) (hsmooth : ContDiff ℝ ∞ thetaR)
    (hrange : ∀ x, 0 ≤ thetaR x ∧ thetaR x ≤ 1)
    (hgradR : ∀ x, ‖fderiv ℝ thetaR x‖ ≤ Cgrad / (rad j0 / (3 : ℝ) ^ Jr))
    (thetaRH1 : H1Function (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)))
    (hH1 : thetaRH1.toFun = thetaR) :
    cellDirichletInfimum (cutoffCoefficient M H (env n omega) (cutoff n))
        (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jr) k : Set (SpatialCoordinates d))
        (thetaRH1.restrict (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jr) k).isOpen
          (oddGridCell_subset (z j0) (hrad j0) (triadicHalf Jr) k)) ≤
      (Cext * (1 + Cgrad) ^ 2 * (1 + rad j0 ^ eta) + (d : ℝ) * Cgrad ^ 2) * Kn *
        (rad j0 / (3 : ℝ) ^ Jr) ^ ((d : ℝ) - 2 - eta) := by
  classical
  obtain ⟨-, hA2, hA3, hCext0', -, -, -, -, -, -, hsub, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, hnonneg, -, -, -, hI, hJ, -, -⟩ := hrepresented
  have heta : 0 < eta := hA2.2.1
  have hbeta0 : 0 < beta := by linarith [hA3.1]
  have hbeta1 : beta ≤ 1 := by linarith [hA3.2, hA2.1]
  have hCext0 : 0 ≤ Cext := hCext0'.le
  set ρ : ℝ := rad j0 / (3 : ℝ) ^ Jr with hρdef
  have hρpos : 0 < ρ := div_pos (hrad j0) (by positivity)
  have hρR : ρ ≤ rad j0 := div_le_self (hrad j0).le (one_le_pow₀ (by norm_num))
  have hR0 : 0 < rad j0 := hrad j0
  have hRη : 0 ≤ rad j0 ^ eta := Real.rpow_nonneg hR0.le _
  have hKρ : 0 ≤ Kn * ρ ^ ((d : ℝ) - 2 - eta) := mul_nonneg hKn (Real.rpow_nonneg hρpos.le _)
  set a : SpatialCoordinates d → ℝ := cutoffCoefficient M H (env n omega) (cutoff n) with hadef
  obtain ⟨hacont, hapos⟩ := aux_lem_cutoffs_cutoffCoefficient_cont_pos M H (env n omega) (cutoff n)
  have hWW : (centeredCube (z j_cell) (rad j_cell) (hrad j_cell) : Set (SpatialCoordinates d)) =
      (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jr) k : Set (SpatialCoordinates d)) := by
    change Metric.ball (z j_cell) (rad j_cell / 2) =
      Metric.ball (oddGridCenter (z j0) (rad j0) (triadicHalf Jr) k)
        (rad j0 / (2 * (triadicHalf Jr : ℝ) + 1) / 2)
    rw [hjz, hjr, triadic_denominator]
  have hinf_eq := aux_lem_cutoffs_cellInf_restrict_eq hWW
    (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jr) k).isOpen
    (centeredCube (z j_cell) (rad j_cell) (hrad j_cell)).isOpen
    (oddGridCell_subset (z j0) (hrad j0) (triadicHalf Jr) k) (hsub j_cell) a thetaRH1
  have hgradc : ∀ x, ‖fderiv ℝ thetaR x‖ ≤ Cgrad / rad j_cell := by
    rw [hjr]; exact hgradR
  obtain ⟨hbc, hqn⟩ := aux_cutoffs_boundary_class_and_norm (z j_cell) (rad j_cell) Cgrad beta
    (hrad j_cell) hCgrad.le hbeta0 hbeta1 thetaR hsmooth hrange hgradc
  have hqn0 := aux_lem_cutoffs_quotientNorm_nonneg beta (z j_cell) (rad j_cell) thetaR
  have hqn2 : (cellBoundaryQuotientNorm beta (z j_cell) (rad j_cell) thetaR) ^ 2 ≤
      (1 + Cgrad) ^ 2 := pow_le_pow_left₀ hqn0 hqn 2
  have hIc := hI j_cell n omega homega
    (thetaRH1.restrict (centeredCube (z j_cell) (rad j_cell) (hrad j_cell)).isOpen (hsub j_cell))
    (by
      change ContinuousOn thetaRH1.toFun _
      rw [hH1]; exact hsmooth.continuous.continuousOn)
    (by change IsCellBoundaryClass beta (z j_cell) (rad j_cell) thetaRH1.toFun; rw [hH1]; exact hbc)
  have hext0 : 0 ≤ constants (extensionKey j_cell) n omega := hnonneg _ omega homega n
  have hpowsplit : ρ ^ ((d : ℝ) - 2) = ρ ^ ((d : ℝ) - 2 - eta) * ρ ^ eta := by
    rw [← Real.rpow_add hρpos]; congr 1; ring
  have hCcell1 : Cext * (1 + Cgrad) ^ 2 * (1 + rad j0 ^ eta) ≤
      Cext * (1 + Cgrad) ^ 2 * (1 + rad j0 ^ eta) + (d : ℝ) * Cgrad ^ 2 :=
    le_add_of_nonneg_right (by positivity)
  have hbase : cellDirichletInfimum a
      (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jr) k : Set (SpatialCoordinates d))
      (thetaRH1.restrict (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jr) k).isOpen
        (oddGridCell_subset (z j0) (hrad j0) (triadicHalf Jr) k)) ≤
      Cext * constants (extensionKey j_cell) n omega * ρ ^ ((d : ℝ) - 2) * (1 + Cgrad) ^ 2 := by
    rw [hinf_eq]
    refine hIc.trans ?_
    have hr : rad j_cell ^ ((d : ℝ) - 2) = ρ ^ ((d : ℝ) - 2) := by rw [hjr]
    change Cext * constants (extensionKey j_cell) n omega * rad j_cell ^ ((d : ℝ) - 2) *
      cellBoundaryQuotientNorm beta (z j_cell) (rad j_cell) thetaRH1.toFun ^ 2 ≤ _
    rw [hr, hH1]
    exact mul_le_mul_of_nonneg_left hqn2
      (mul_nonneg (mul_nonneg hCext0 hext0) (Real.rpow_nonneg hρpos.le _))
  by_cases hc : (Jr : ℤ) < κ
  · -- coarse superunit cell: finite extension key
    have hext := hcoarse hc
    have hρη : ρ ^ eta ≤ rad j0 ^ eta := Real.rpow_le_rpow hρpos.le hρR heta.le
    refine hbase.trans ?_
    rw [hpowsplit]
    calc Cext * constants (extensionKey j_cell) n omega *
          (ρ ^ ((d : ℝ) - 2 - eta) * ρ ^ eta) * (1 + Cgrad) ^ 2
        ≤ Cext * Kn * (ρ ^ ((d : ℝ) - 2 - eta) * rad j0 ^ eta) * (1 + Cgrad) ^ 2 := by
          gcongr
      _ = (Cext * (1 + Cgrad) ^ 2 * rad j0 ^ eta) * (Kn * ρ ^ ((d : ℝ) - 2 - eta)) := by ring
      _ ≤ (Cext * (1 + Cgrad) ^ 2 * (1 + rad j0 ^ eta) + (d : ℝ) * Cgrad ^ 2) *
            (Kn * ρ ^ ((d : ℝ) - 2 - eta)) := by
          apply mul_le_mul_of_nonneg_right _ hKρ
          refine le_trans ?_ hCcell1
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  · push Not at hc
    obtain ⟨kp, hkp⟩ : ∃ kp : ℕ, (kp : ℤ) = (Jr : ℤ) - κ := ⟨((Jr : ℤ) - κ).toNat,
      Int.toNat_of_nonneg (by linarith)⟩
    have hρz : ρ = (3 : ℝ) ^ (-(kp : ℤ)) := by
      rw [aux_cutoffs_physical_side κ Jr (rad j0) ρ hκ rfl, hkp]
      congr 1; ring
    by_cases hN : kp ≤ cutoff n
    · -- represented grid scale above the ultraviolet cutoff
      have hidx : ∃ idx : Fin d → ℤ,
          z j_cell = (fun i => origin g0 i + (3 : ℝ) ^ (-(kp : ℤ)) * (idx i : ℝ)) := by
        refine ⟨fun i => ((k i).val : ℤ) - (triadicHalf Jr : ℤ), ?_⟩
        rw [hjz, hg0.2, ← hρz, hρdef, ← triadic_denominator]
        funext i
        simp only [oddGridCenter]
        push_cast
        ring
      have hsub' : (centeredCube (z j_cell) (rad j_cell) (hrad j_cell) :
          Set (SpatialCoordinates d)) ⊆
          (centeredCube (z (gridRoot g0)) (rad (gridRoot g0)) (hrad (gridRoot g0)) :
            Set (SpatialCoordinates d)) := by
        rw [hg0.1]; exact hsub j_cell
      have hJc := hJ g0 n kp j_cell omega homega hN (by rw [hjr]; exact hρz) hidx hsub'
      have hlam0 : 0 ≤ constants (lambdaKey j_cell) n omega := hnonneg _ omega homega n
      rw [hjr] at hJc
      have hext : constants (extensionKey j_cell) n omega ≤ Kn * ρ ^ (-eta) :=
        (by linarith : constants (extensionKey j_cell) n omega ≤
          constants (gridKey g0) n omega * ρ ^ (-eta)).trans
          (mul_le_mul_of_nonneg_right hgrid (Real.rpow_nonneg hρpos.le _))
      have hpow2 : ρ ^ (-eta) * ρ ^ ((d : ℝ) - 2) = ρ ^ ((d : ℝ) - 2 - eta) := by
        rw [← Real.rpow_add hρpos]; congr 1; ring
      refine hbase.trans ?_
      calc Cext * constants (extensionKey j_cell) n omega * ρ ^ ((d : ℝ) - 2) * (1 + Cgrad) ^ 2
          ≤ Cext * (Kn * ρ ^ (-eta)) * ρ ^ ((d : ℝ) - 2) * (1 + Cgrad) ^ 2 := by gcongr
        _ = (Cext * (1 + Cgrad) ^ 2) * (Kn * (ρ ^ (-eta) * ρ ^ ((d : ℝ) - 2))) := by ring
        _ = (Cext * (1 + Cgrad) ^ 2) * (Kn * ρ ^ ((d : ℝ) - 2 - eta)) := by rw [hpow2]
        _ ≤ (Cext * (1 + Cgrad) ^ 2 * (1 + rad j0 ^ eta) + (d : ℝ) * Cgrad ^ 2) *
              (Kn * ρ ^ ((d : ℝ) - 2 - eta)) := by
            apply mul_le_mul_of_nonneg_right _ hKρ
            refine le_trans ?_ hCcell1
            have : (1 : ℝ) ≤ 1 + rad j0 ^ eta := by linarith
            exact le_mul_of_one_le_right (by positivity) this
        _ = _ := by ring
    · -- below the ultraviolet cutoff: direct coefficient maximum
      push Not at hN
      have hρr : ρ = (3 : ℝ) ^ (-(kp : ℝ)) := by
        rw [hρz, ← Real.rpow_intCast]; push_cast; rfl
      have hcellset : (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jr) k :
          Set (SpatialCoordinates d)) ⊆
          closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)) :=
        (oddGridCell_subset (z j0) (hrad j0) (triadicHalf Jr) k).trans subset_closure
      have hG0 : 0 ≤ Cgrad / ρ := div_nonneg hCgrad.le hρpos.le
      have hen := aux_lem_cutoffs_datum_energy_le
        (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jr) k : Set (SpatialCoordinates d))
        (aux_lem_cutoffs_cell_dom _ _ _ k) a Mhi (Cgrad / ρ)
        (fun x hx => ⟨(hapos x).le, hMhi x (hcellset hx)⟩) hG0
        (thetaRH1.restrict (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jr) k).isOpen
          (oddGridCell_subset (z j0) (hrad j0) (triadicHalf Jr) k))
        (by change ContDiff ℝ 1 thetaRH1.toFun; rw [hH1]; exact hsmooth.of_le (by simp))
        (by intro x _; change ‖fderiv ℝ thetaRH1.toFun x‖ ≤ _; rw [hH1]; exact hgradR x)
      have hvol : volume.real (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jr) k :
          Set (SpatialCoordinates d)) = ρ ^ d := by
        have hv := centeredCube_volume_real (oddGridCenter (z j0) (rad j0) (triadicHalf Jr) k)
          (div_pos (hrad j0) (by positivity : (0 : ℝ) < 2 * (triadicHalf Jr : ℝ) + 1))
        refine hv.trans ?_
        rw [triadic_denominator]
      rw [hvol] at hen
      have hle := aux_lem_cutoffs_cellInf_le_datum _ a (fun x _ => (hapos x).le)
        (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jr) k).isOpen.measurableSet
        (thetaRH1.restrict (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jr) k).isOpen
          (oddGridCell_subset (z j0) (hrad j0) (triadicHalf Jr) k))
      have hscale : Mhi * ((d : ℝ) * (Cgrad / ρ) ^ 2) * ρ ^ d =
          ((d : ℝ) * Cgrad ^ 2 * Mhi) * ρ ^ ((d : ℝ) - 2) := by
        rw [Real.rpow_sub hρpos, Real.rpow_natCast, Real.rpow_two]
        field_simp
      have hMK' : (d : ℝ) * Cgrad ^ 2 * Mhi ≤
          ((d : ℝ) * Cgrad ^ 2 * Kn) * (3 : ℝ) ^ (((cutoff n : ℕ) : ℝ) * eta) := by
        rw [mul_assoc ((d : ℝ) * Cgrad ^ 2)]
        exact mul_le_mul_of_nonneg_left hMK (by positivity)
      have hbelow := aux_cutoffs_physical_below_energy d (cutoff n) kp ρ eta
        ((d : ℝ) * Cgrad ^ 2 * Kn) ((d : ℝ) * Cgrad ^ 2 * Mhi) hρr heta.le (by positivity) hN hMK'
      calc cellDirichletInfimum a _ _ ≤ _ := hle
        _ ≤ Mhi * ((d : ℝ) * (Cgrad / ρ) ^ 2) * ρ ^ d := hen
        _ = ((d : ℝ) * Cgrad ^ 2 * Mhi) * ρ ^ ((d : ℝ) - 2) := hscale
        _ ≤ ((d : ℝ) * Cgrad ^ 2 * Kn) * ρ ^ ((d : ℝ) - 2 - eta) := hbelow
        _ = ((d : ℝ) * Cgrad ^ 2) * (Kn * ρ ^ ((d : ℝ) - 2 - eta)) := by ring
        _ ≤ (Cext * (1 + Cgrad) ^ 2 * (1 + rad j0 ^ eta) + (d : ℝ) * Cgrad ^ 2) *
              (Kn * ρ ^ ((d : ℝ) - 2 - eta)) :=
            mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) hKρ
        _ = _ := by ring


/-! ### Final helpers of the mesh/collar step -/

/-- The represented collar clause of `lem_cutoffs` at a represented point, for
any majorant dominating the root grid key, the coarse extension keys and the
damped coefficient maximum. -/
theorem aux_lem_cutoffs_rep_collar
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Cext beta alpha eta t : ℝ) (orders : Finset ℝ)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
    (J : Type) [Countable J] [DecidableEq J] (j0 : J)
    (z : J → SpatialCoordinates d) (rad : J → ℝ)
    (hrad : ∀ j, 0 < rad j)
    (S : ∀ j, ResponseSpace (centeredCube (z j) (rad j) (hrad j)))
    (D : ∀ j, Submodule ℚ
      (DomainL2 (centeredCube (z j) (rad j) (hrad j))))
    [hDc : ∀ j, Countable (D j)]
    (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
    (T : J → Type) [hTc : ∀ j, Countable (T j)]
    (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
    (thetaH1 : ∀ j, T j →
      Homogenization.H1Function
        (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (usrc : ∀ j, (D j) → ℕ → Ω → (S j).space)
    (srcRep : ∀ j, (D j) → ℕ → Ω → SpatialCoordinates d → ℝ)
    (ucell : ∀ j, T j → ℕ → Ω →
      Homogenization.H1Function
        (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (E : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Index : Type) [Countable Index]
    (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
    (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
    (coercivityKey extensionKey lambdaKey : J → Index)
    (sourceResponseKey sourceGrowthKey sourceHolderKey :
      ∀ j, (D j) → Index)
    (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
    (Grid : Type) [Countable Grid]
    (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J)
    (gridKey : Grid → Index)
    (hrepresented :
      _root_.SubdiffusiveProcess.Paper.conv_represented_estimates d hd M H Ω P cutoff env J j0 z rad hrad
        S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E
        Index resp respLim constants G coercivityKey extensionKey lambdaKey
        sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey
        cellGrowthKey cellHolderKey Grid origin gridRoot gridKey)
    (Cgrad : ℝ) (hCgrad : 0 < Cgrad) (Ccollar : ℝ)
    (hCsum : ∀ (Jr : ℕ) (rho : ℝ) (thetaR : SpatialCoordinates d → ℝ),
      (∀ x ∈ (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
        3 * rho ≤ Metric.infDist x
          (frontier (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d))) →
          thetaR x = 1) →
      rho = rad j0 / (3 : ℝ) ^ Jr →
      ∃ I : Finset (OddGridIndex d (triadicHalf Jr)),
        (∀ k, k ∈ I ↔
          (closure (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jr) k :
            Set (SpatialCoordinates d)) ∩
            {x : SpatialCoordinates d | 0 < thetaR x ∧ thetaR x < 1}).Nonempty) ∧
        ∀ (K : ℕ → ℝ) (e : OddGridIndex d (triadicHalf Jr) → ℕ → ℝ),
          (∀ n, 0 ≤ K n) →
          (∀ n k, k ∈ I →
            e k n ≤ (Cext * (1 + Cgrad) ^ 2 * (1 + rad j0 ^ eta) + (d : ℝ) * Cgrad ^ 2) *
              K n * rho ^ ((d : ℝ) - 2 - eta)) →
          ∀ n, (∑ k ∈ I, e k n) ≤ Ccollar * K n * rho ^ (-1 - eta))
    (κ : ℤ) (hκ : rad j0 = (3 : ℝ) ^ κ)
    (g0 : Grid) (hg0 : gridRoot g0 = j0 ∧ origin g0 = z j0)
    (jc : ∀ Jr : ℕ, OddGridIndex d (triadicHalf Jr) → J)
    (hjc : ∀ Jr k, z (jc Jr k) = oddGridCenter (z j0) (rad j0) (triadicHalf Jr) k ∧
      rad (jc Jr k) = rad j0 / (3 : ℝ) ^ Jr)
    (omega : Ω) (homega : omega ∈ G) (KN : ℕ → Ω → ℝ) (hKN : ∀ n, 1 ≤ KN n omega)
    (hgrid : ∀ n, constants (gridKey g0) n omega ≤ KN n omega)
    (hcoarse : ∀ n (Jr : ℕ) (k : OddGridIndex d (triadicHalf Jr)), (Jr : ℤ) < κ →
      constants (extensionKey (jc Jr k)) n omega ≤ KN n omega)
    (Mhi : ℕ → ℝ)
    (hMhi : ∀ n, ∀ x ∈ closure
        (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
      cutoffCoefficient M H (env n omega) (cutoff n) x ≤ Mhi n)
    (hMK : ∀ n, Mhi n ≤ KN n omega * (3 : ℝ) ^ (((cutoff n : ℕ) : ℝ) * eta)) :
    let Q := centeredCube (z j0) (rad j0) (hrad j0)
    let S0 := S j0
    let aN := fun (omega : Ω) (n : ℕ) =>
      _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n omega) (cutoff n)
        (z j0) (hrad j0)
    let rawAN := fun (omega : Ω) (n : ℕ) =>
      cutoffCoefficient M H (env n omega) (cutoff n)
    (∀ Jr : ℕ,
              let rho := rad j0 / (3 : ℝ) ^ Jr
                ∀ thetaR : SpatialCoordinates d → ℝ,
                  ContDiff ℝ ∞ thetaR →
                  (∀ x : SpatialCoordinates d,
                    0 ≤ thetaR x ∧ thetaR x ≤ 1) →
                  (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                    Metric.infDist x (frontier (Q : Set (SpatialCoordinates d))) ≤ rho →
                      thetaR x = 0) →
                  (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                    3 * rho ≤ Metric.infDist x (frontier (Q : Set (SpatialCoordinates d))) →
                      thetaR x = 1) →
                  (∀ x : SpatialCoordinates d,
                    norm (fderiv ℝ thetaR x) ≤ Cgrad / rho) →
                  ∀ thetaRH1 : Homogenization.H1Function
                    (Q : Set (SpatialCoordinates d)),
                    thetaRH1.toFun = thetaR →
                    ∃ collarH : ℕ → Homogenization.H1Function
                        (Q : Set (SpatialCoordinates d)),
                      ∃ collarS : ℕ → S0.space,
                        ∃ collarC : ℕ → SpatialCoordinates d → ℝ,
                          ∀ n : ℕ,
                            (collarS n).val = sobolevDataOfH1 (collarH n) ∧
                            ContinuousOn (collarC n)
                              (closure (Q : Set (SpatialCoordinates d))) ∧
                            (collarS n).val.1 =ᵐ[
                              volume.restrict (Q : Set (SpatialCoordinates d))]
                              collarC n ∧
                            (∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
                              0 ≤ collarC n x ∧ collarC n x ≤ 1) ∧
                            (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                              Metric.infDist x
                                  (frontier (Q : Set (SpatialCoordinates d))) ≤ rho →
                                collarC n x = 0) ∧
                            (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                              3 * rho ≤ Metric.infDist x
                                  (frontier (Q : Set (SpatialCoordinates d))) →
                                collarC n x = 1) ∧
                            (∀ i : Fin d, ∀ᵐ x ∂volume.restrict
                              (Q : Set (SpatialCoordinates d)),
                              3 * rho < Metric.infDist x
                                  (frontier (Q : Set (SpatialCoordinates d))) →
                                (collarS n).val.2 i x = 0) ∧
                            (∀ k : OddGridIndex d (triadicHalf Jr),
                              IsWeaklyHarmonicOn (rawAN omega n)
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jr) k : Set (SpatialCoordinates d))
                                ((collarH n).restrict
                                  (oddGridCell (z j0) (rad j0) (hrad j0)
                                    (triadicHalf Jr) k).isOpen
                                  (oddGridCell_subset (z j0) (hrad j0)
                                    (triadicHalf Jr) k)) ∧
                              HasZeroTraceDifferenceOn
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jr) k : Set (SpatialCoordinates d))
                                ((collarH n).restrict
                                  (oddGridCell (z j0) (rad j0) (hrad j0)
                                    (triadicHalf Jr) k).isOpen
                                  (oddGridCell_subset (z j0) (hrad j0)
                                    (triadicHalf Jr) k))
                                (thetaRH1.restrict
                                  (oddGridCell (z j0) (rad j0) (hrad j0)
                                    (triadicHalf Jr) k).isOpen
                                  (oddGridCell_subset (z j0) (hrad j0)
                                    (triadicHalf Jr) k))) ∧
                            responseForm S0 (aN omega n) (collarS n) (collarS n) ≤
                              Ccollar * KN n omega * rho ^ (-1 - eta)) := by
  intro Q S0 aN rawAN Jr rho thetaR hsmooth hrange hzero hone hgradR thetaRH1 hH1
  have : NeZero d := ⟨by omega⟩
  have hrep := hrepresented
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hSk, -⟩ := hrep
  obtain ⟨I, hI, hsum⟩ := hCsum Jr rho thetaR hone rfl
  obtain ⟨collarH, collarS, collarC, hcol⟩ := aux_lem_cutoffs_collar_generic hd (z j0) (rad j0)
    (hrad j0) (S j0) (hSk j0) (fun n => cutoffCoefficient M H (env n omega) (cutoff n))
    (fun n => (aux_lem_cutoffs_cutoffCoefficient_cont_pos M H (env n omega) (cutoff n)).1)
    (fun n => (aux_lem_cutoffs_cutoffCoefficient_cont_pos M H (env n omega) (cutoff n)).2)
    (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n omega) (cutoff n) (z j0) (hrad j0))
    (fun n => aux_lem_cutoffs_positiveCoefficient_ae M H (env n omega) (cutoff n) (z j0)
      (hrad j0))
    Jr thetaR hsmooth hrange hzero hone thetaRH1 hH1 I hI
  refine ⟨collarH, collarS, collarC, fun n => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hcol n
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9.trans ?_⟩
  exact hsum (fun n => KN n omega)
    (fun k n => cellDirichletInfimum (cutoffCoefficient M H (env n omega) (cutoff n))
      (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jr) k : Set (SpatialCoordinates d))
      (thetaRH1.restrict (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jr) k).isOpen
        (oddGridCell_subset (z j0) (hrad j0) (triadicHalf Jr) k)))
    (fun n => zero_le_one.trans (hKN n))
    (fun n k _ => aux_lem_cutoffs_rep_collar_cell d hd M H Cext beta alpha eta t orders Ω P
      cutoff env J j0 z rad hrad S D f T theta thetaH1 usrc srcRep ucell E Index resp respLim
      constants G coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey
      sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey
      hrepresented Cgrad hCgrad κ hκ g0 hg0 omega homega n (KN n omega)
      (zero_le_one.trans (hKN n)) (hgrid n) (Mhi n) (hMhi n) (hMK n) Jr k (jc Jr k)
      (hjc Jr k).1 (hjc Jr k).2 (hcoarse n Jr k) thetaR hsmooth hrange hgradR thetaRH1 hH1) n

/-- The pathwise mesh and collar step of `lem_cutoffs`: the premise `hMC` of
`aux_lem_cutoffs_of_mesh_collar`, proved from the represented catalogue. The
finite selection `F` is the root grid key together with the extension keys of
the finitely many superunit collar cells. -/
theorem aux_lem_cutoffs_mesh_collar
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (beta alpha eta t : ℝ)
    (_hbeta : 1 / 2 < beta) (_hbetaalpha : beta < alpha)
    (_halpha : alpha < 1) (_heta : 0 < eta)
    (_htlow : (d : ℝ) - 1 < t) (_htupper : t < (d : ℝ))
    (_hetaalpha : 1 + eta < 2 * alpha)
    (orders : Finset ℝ) (_horders : ∀ p ∈ orders, 0 < p)
    (Cext Cgrad : ℝ) (hCext : 0 < Cext) (hCgrad : 0 < Cgrad) :
    ∃ delta1 Ccollar : ℝ, 0 < delta1 ∧ 0 < Ccollar ∧
        ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
          (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
          M.delta ≤ delta1 →
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
          [IsProbabilityMeasure P]
          (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
          (J : Type) [Countable J] [DecidableEq J] (j0 : J)
          (z : J → SpatialCoordinates d) (rad : J → ℝ)
          (hrad : ∀ j, 0 < rad j)
          (S : ∀ j, ResponseSpace (centeredCube (z j) (rad j) (hrad j)))
          (D : ∀ j, Submodule ℚ
            (DomainL2 (centeredCube (z j) (rad j) (hrad j))))
          [_hDc : ∀ j, Countable (D j)]
          (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
          (T : J → Type) [_hTc : ∀ j, Countable (T j)]
          (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
          (thetaH1 : ∀ j, T j →
            Homogenization.H1Function
              (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
          (usrc : ∀ j, (D j) → ℕ → Ω → (S j).space)
          (srcRep : ∀ j, (D j) → ℕ → Ω → SpatialCoordinates d → ℝ)
          (ucell : ∀ j, T j → ℕ → Ω →
            Homogenization.H1Function
              (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
          (E : _root_.SubdiffusiveProcess.Paper.in_J d)
          (Index : Type) [Countable Index]
          (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
          (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
          (coercivityKey extensionKey lambdaKey : J → Index)
          (sourceResponseKey sourceGrowthKey sourceHolderKey :
            ∀ j, (D j) → Index)
          (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
          (Grid : Type) [Countable Grid]
          (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J)
          (gridKey : Grid → Index)
          (_hz0 : z j0 = z0) (_hrad0 : rad j0 = R)
          (_hrepresented :
            _root_.SubdiffusiveProcess.Paper.conv_represented_estimates d hd M H Ω P cutoff env J j0 z rad hrad
              S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E
              Index resp respLim constants G coercivityKey extensionKey lambdaKey
              sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey
              cellGrowthKey cellHolderKey Grid origin gridRoot gridKey),
          let Q := centeredCube (z j0) (rad j0) (hrad j0)
          let S0 := S j0
          let aN := fun (omega : Ω) (n : ℕ) =>
            _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n omega) (cutoff n)
              (z j0) (hrad j0)
          let rawAN := fun (omega : Ω) (n : ℕ) =>
            cutoffCoefficient M H (env n omega) (cutoff n)
          ∃ F : Finset Index,
            ∀ (KN : ℕ → Ω → ℝ) (Ggood : Set Ω) (mlow mhigh : ℕ → BilateralField d → ℝ),
              Ggood ⊆ G →
              (∀ n : ℕ, ∀ omega : Ω, 1 ≤ KN n omega) →
              (∀ omega ∈ Ggood, BddAbove (Set.range (fun n : ℕ => KN n omega))) →
              (∀ omega ∈ Ggood, ∀ n : ℕ, ∀ i ∈ F, constants i n omega ≤ KN n omega) →
              (∀ omega ∈ Ggood, ∀ n : ℕ,
                0 < mlow (cutoff n) (env n omega) ∧
                (∀ x ∈ closure
                    (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
                  mlow (cutoff n) (env n omega) ≤
                      cutoffCoefficient M H (env n omega) (cutoff n) x ∧
                    cutoffCoefficient M H (env n omega) (cutoff n) x ≤
                      mhigh (cutoff n) (env n omega)) ∧
                mhigh (cutoff n) (env n omega) ≤
                  KN n omega * (3 : ℝ) ^ (((cutoff n : ℕ) : ℝ) * eta) ∧
                (mlow (cutoff n) (env n omega))⁻¹ ≤
                  KN n omega * (3 : ℝ) ^ (((cutoff n : ℕ) : ℝ) * eta)) →
              ∀ omega ∈ Ggood,
                (∀ b : T j0, ∀ K O W : Set (SpatialCoordinates d), ∀ Jmesh : ℕ,
                  IsCompact K → IsOpen O →
                  closure O ⊆ (Q : Set (SpatialCoordinates d)) →
                  IsOpen W → K ⊆ W → W ⊆ O →
                  (∀ x : SpatialCoordinates d,
                    0 ≤ theta j0 b x ∧ theta j0 b x ≤ 1) →
                  (∀ x ∈ W, theta j0 b x = 1) →
                  tsupport (theta j0 b) ⊆ O →
                  (∀ k : OddGridIndex d (triadicHalf Jmesh),
                    (closure
                        (oddGridCell (z j0) (rad j0) (hrad j0)
                          (triadicHalf Jmesh) k : Set (SpatialCoordinates d)) ∩
                        {x : SpatialCoordinates d |
                          0 < theta j0 b x ∧ theta j0 b x < 1}).Nonempty →
                      closure
                          (oddGridCell (z j0) (rad j0) (hrad j0)
                            (triadicHalf Jmesh) k : Set (SpatialCoordinates d)) ⊆
                        O \ K) →
                  ∃ chiH : ℕ → Homogenization.H1Function
                      (Q : Set (SpatialCoordinates d)),
                    ∃ chiS : ℕ → S0.space,
                      ∃ chic : ℕ → SpatialCoordinates d → ℝ,
                        ∃ V : Set (SpatialCoordinates d),
                          ∃ Benergy Ball Bholder : ℝ,
                            IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧
                            0 ≤ Benergy ∧ 0 ≤ Ball ∧ 0 ≤ Bholder ∧
                            (∀ n : ℕ,
                              (chiS n).val = sobolevDataOfH1 (chiH n) ∧
                              ContinuousOn (chic n)
                                (closure (Q : Set (SpatialCoordinates d))) ∧
                              (chiS n).val.1 =ᵐ[
                                volume.restrict (Q : Set (SpatialCoordinates d))]
                                chic n ∧
                              (∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
                                0 ≤ chic n x ∧ chic n x ≤ 1) ∧
                              (∀ x ∈ V, chic n x = 1) ∧
                              (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                                x ∉ O → chic n x = 0) ∧
                              (∀ k : OddGridIndex d (triadicHalf Jmesh),
                                IsWeaklyHarmonicOn (rawAN omega n)
                                  (oddGridCell (z j0) (rad j0) (hrad j0)
                                    (triadicHalf Jmesh) k : Set (SpatialCoordinates d))
                                  ((chiH n).restrict
                                    (oddGridCell (z j0) (rad j0) (hrad j0)
                                      (triadicHalf Jmesh) k).isOpen
                                    (oddGridCell_subset (z j0) (hrad j0)
                                      (triadicHalf Jmesh) k)) ∧
                                HasZeroTraceDifferenceOn
                                  (oddGridCell (z j0) (rad j0) (hrad j0)
                                    (triadicHalf Jmesh) k : Set (SpatialCoordinates d))
                                  ((chiH n).restrict
                                    (oddGridCell (z j0) (rad j0) (hrad j0)
                                      (triadicHalf Jmesh) k).isOpen
                                    (oddGridCell_subset (z j0) (hrad j0)
                                      (triadicHalf Jmesh) k))
                                  ((thetaH1 j0 b).restrict
                                    (oddGridCell (z j0) (rad j0) (hrad j0)
                                      (triadicHalf Jmesh) k).isOpen
                                    (oddGridCell_subset (z j0) (hrad j0)
                                      (triadicHalf Jmesh) k))) ∧
                              (∀ k : OddGridIndex d (triadicHalf Jmesh),
                                (∃ c : ℝ, ∀ x ∈ closure
                                    (oddGridCell (z j0) (rad j0) (hrad j0)
                                      (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                                  theta j0 b x = c) →
                                  ∀ i : Fin d, ∀ᵐ x ∂volume.restrict
                                    (oddGridCell (z j0) (rad j0) (hrad j0)
                                      (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                                    (chiS n).val.2 i x = 0) ∧
                              responseForm S0 (aN omega n) (chiS n) (chiS n) ≤ Benergy ∧
                              (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), ∀ s : ℝ,
                                0 < s → s ≤ 1 →
                                ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
                                  (fun y => ENNReal.ofReal
                                    ((aN omega n).val y *
                                      ∑ i : Fin d, ((chiS n).val.2 i y) ^ 2)))
                                  (Metric.ball x s) ≤ ENNReal.ofReal (Ball * s ^ t)) ∧
                              _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
                                (closure (Q : Set (SpatialCoordinates d))) (chic n) ∧
                              _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
                                (closure (Q : Set (SpatialCoordinates d))) (chic n) ≤
                                Bholder) ∧
                            (∃ sigma : ℕ → ℕ, ∃ chiLim : SpatialCoordinates d → ℝ,
                              StrictMono sigma ∧
                              ContinuousOn chiLim
                                (closure (Q : Set (SpatialCoordinates d))) ∧
                              TendstoUniformlyOn (fun n => chic (sigma n)) chiLim atTop
                                (closure (Q : Set (SpatialCoordinates d))) ∧
                              (∀ k : OddGridIndex d (triadicHalf Jmesh),
                                (∃ c : ℝ, ∀ x ∈ closure
                                    (oddGridCell (z j0) (rad j0) (hrad j0)
                                      (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                                  theta j0 b x = c) →
                                  ∀ x ∈ closure
                                    (oddGridCell (z j0) (rad j0) (hrad j0)
                                      (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                                    chiLim x = theta j0 b x))) ∧
                (∀ Jr : ℕ,
                  let rho := rad j0 / (3 : ℝ) ^ Jr
                    ∀ thetaR : SpatialCoordinates d → ℝ,
                      ContDiff ℝ ∞ thetaR →
                      (∀ x : SpatialCoordinates d,
                        0 ≤ thetaR x ∧ thetaR x ≤ 1) →
                      (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                        Metric.infDist x (frontier (Q : Set (SpatialCoordinates d))) ≤ rho →
                          thetaR x = 0) →
                      (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                        3 * rho ≤ Metric.infDist x (frontier (Q : Set (SpatialCoordinates d))) →
                          thetaR x = 1) →
                      (∀ x : SpatialCoordinates d,
                        norm (fderiv ℝ thetaR x) ≤ Cgrad / rho) →
                      ∀ thetaRH1 : Homogenization.H1Function
                        (Q : Set (SpatialCoordinates d)),
                        thetaRH1.toFun = thetaR →
                        ∃ collarH : ℕ → Homogenization.H1Function
                            (Q : Set (SpatialCoordinates d)),
                          ∃ collarS : ℕ → S0.space,
                            ∃ collarC : ℕ → SpatialCoordinates d → ℝ,
                              ∀ n : ℕ,
                                (collarS n).val = sobolevDataOfH1 (collarH n) ∧
                                ContinuousOn (collarC n)
                                  (closure (Q : Set (SpatialCoordinates d))) ∧
                                (collarS n).val.1 =ᵐ[
                                  volume.restrict (Q : Set (SpatialCoordinates d))]
                                  collarC n ∧
                                (∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
                                  0 ≤ collarC n x ∧ collarC n x ≤ 1) ∧
                                (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                                  Metric.infDist x
                                      (frontier (Q : Set (SpatialCoordinates d))) ≤ rho →
                                    collarC n x = 0) ∧
                                (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                                  3 * rho ≤ Metric.infDist x
                                      (frontier (Q : Set (SpatialCoordinates d))) →
                                    collarC n x = 1) ∧
                                (∀ i : Fin d, ∀ᵐ x ∂volume.restrict
                                  (Q : Set (SpatialCoordinates d)),
                                  3 * rho < Metric.infDist x
                                      (frontier (Q : Set (SpatialCoordinates d))) →
                                    (collarS n).val.2 i x = 0) ∧
                                (∀ k : OddGridIndex d (triadicHalf Jr),
                                  IsWeaklyHarmonicOn (rawAN omega n)
                                    (oddGridCell (z j0) (rad j0) (hrad j0)
                                      (triadicHalf Jr) k : Set (SpatialCoordinates d))
                                    ((collarH n).restrict
                                      (oddGridCell (z j0) (rad j0) (hrad j0)
                                        (triadicHalf Jr) k).isOpen
                                      (oddGridCell_subset (z j0) (hrad j0)
                                        (triadicHalf Jr) k)) ∧
                                  HasZeroTraceDifferenceOn
                                    (oddGridCell (z j0) (rad j0) (hrad j0)
                                      (triadicHalf Jr) k : Set (SpatialCoordinates d))
                                    ((collarH n).restrict
                                      (oddGridCell (z j0) (rad j0) (hrad j0)
                                        (triadicHalf Jr) k).isOpen
                                      (oddGridCell_subset (z j0) (hrad j0)
                                        (triadicHalf Jr) k))
                                    (thetaRH1.restrict
                                      (oddGridCell (z j0) (rad j0) (hrad j0)
                                        (triadicHalf Jr) k).isOpen
                                      (oddGridCell_subset (z j0) (hrad j0)
                                        (triadicHalf Jr) k))) ∧
                                responseForm S0 (aN omega n) (collarS n) (collarS n) ≤
                                  Ccollar * KN n omega * rho ^ (-1 - eta)) := by
  classical
  obtain ⟨Csum, hCsum0, hCsum⟩ := aux_cutoffs_uniform_collar_sum d hd z0 R hR eta
    (Cext * (1 + Cgrad) ^ 2 * (1 + R ^ eta) + (d : ℝ) * Cgrad ^ 2)
    (by have := Real.rpow_nonneg hR.le eta; positivity)
  refine ⟨1, Csum, one_pos, hCsum0, ?_⟩
  intro M H _hM Ω _ P _ cutoff env J _ _ j0 z rad hrad S D _ f T _ theta thetaH1 usrc srcRep
    ucell E Index _ resp respLim constants G coercivityKey extensionKey lambdaKey
    sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey
    cellHolderKey Grid _ origin gridRoot gridKey hz0 hrad0 hrepresented Q S0 aN rawAN
  subst hz0 hrad0
  have hrep := hrepresented
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hcenter, hscale, hcomplete, -, hgridroot, -⟩ := hrep
  have hκ := Classical.choose_spec (hscale j0)
  have hg0 := Classical.choose_spec (hgridroot j0)
  choose jc hjc using fun (Jr : ℕ) (k : OddGridIndex d (triadicHalf Jr)) =>
    aux_cutoffs_odd_cell_catalogue_of_geometry j0 z rad hrad (z j0) (rad j0) (hrad j0) rfl rfl
      hcenter hscale hcomplete Jr k
  refine ⟨insert (gridKey (Classical.choose (hgridroot j0)))
    ((Finset.range (Classical.choose (hscale j0)).toNat).biUnion fun Jr =>
    Finset.univ.image fun k : OddGridIndex d (triadicHalf Jr) => extensionKey (jc Jr k)), ?_⟩
  intro KN Ggood mlow mhigh hGG hKN1 _hbdd hFdom hext omega homega
  refine ⟨aux_lem_cutoffs_rep_plateau d hd M H Cext beta alpha eta t orders Ω P cutoff env J j0 z
    rad hrad S D f T theta thetaH1 usrc srcRep ucell E Index resp respLim constants G
    coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
    cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey hrepresented omega
    (hGG homega), ?_⟩
  exact aux_lem_cutoffs_rep_collar d hd M H Cext beta alpha eta t orders Ω P cutoff env J j0 z
    rad hrad S D f T theta thetaH1 usrc srcRep ucell E Index resp respLim constants G
    coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
    cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey hrepresented
    Cgrad hCgrad Csum hCsum _ hκ _ hg0 jc hjc omega (hGG homega) KN (fun n => hKN1 n omega)
    (fun n => hFdom omega homega n _ (Finset.mem_insert_self _ _))
    (fun n Jr k hc => hFdom omega homega n _ (Finset.mem_insert_of_mem
      (Finset.mem_biUnion.mpr ⟨Jr, Finset.mem_range.mpr (by omega),
        Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩)))
    (fun n => mhigh (cutoff n) (env n omega))
    (fun n x hx => ((hext omega homega n).2.1 x hx).2)
    (fun n => (hext omega homega n).2.2.1)



/-- Corrected cutoffs, paper label `mfd:lem-cutoffs`.

Carried-input and supplier checklist:
* `conv_represented_estimates`: the actual coefficient, killed spaces, trace
  catalogue, finite moment bank, per-cell estimates and represented event.
* `conv_represented_sequence`: simultaneous convergence and objectwise boundedness
  on the represented probability space; no bound for the original full sequence.
* `in_J` and `lem_extension`: the concrete coefficient functionals and estimates
  (2)–(3) in the range stated at paper label `mfd:lem-cutoffs`.
* `lem_extremes`: the finite-cutoff coefficient maximum used for the direct
  below-ultraviolet branch; its scale absorption is the fine proof step
  `lem_cutoffs_below_wavelength_scale`, not a carried extra hypothesis.
* `prop_growth`: all-radii growth at exponent `t` and regularity at exponent
  `alpha`, including centres on the closed-cube boundary.
* `mesh_interpolator` and `cell_boundary_continuity`: the harmonic mesh
  construction and continuous representatives with the prescribed traces.
* `lem_cutoffs_transition_cover` and `lem_cutoffs_collar_transition_sum`:
  the finite transition-cell cover and the energy summation, split out as fine proof steps.
* `in_killed_inverse` and `conv_energy_measure_normalization`: the finite form
  and energy measure use the same actual coefficient as the cell equation.

The root, exponents, finite moment orders and datum-gradient bound precede the
small-disorder threshold. `KN` is an indexed measurable family; the common
represented event precedes every plateau, mesh and collar choice. The two output
clauses are separate conjuncts, so the collar does not depend on the existence
of an unrelated catalog plateau. Full Sobolev data identify values and gradients;
pointwise statements concern continuous representatives, gradient statements are
a.e. The growth exponent is `t`, not `alpha`.

The carrier is corrected here. The paper's collar display is retained as written, while its range question remains separate.
No additional microscopic estimate is assumed as a premise. The below-
ultraviolet direct bound is a proof obligation, not an interface hypothesis.
The mesh, interpolation, and collar estimates are assembled below.
-/
theorem lem_cutoffs
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (beta alpha eta t : ℝ)
    (hbeta : 1 / 2 < beta) (hbetaalpha : beta < alpha)
    (halpha : alpha < 1) (heta : 0 < eta)
    (htlow : (d : ℝ) - 1 < t) (htupper : t < (d : ℝ))
    (hetaalpha : 1 + eta < 2 * alpha)
    (orders : Finset ℝ) (horders : ∀ p ∈ orders, 0 < p)
    (Cext Cgrad : ℝ) (hCext : 0 < Cext) (hCgrad : 0 < Cgrad) :
    ∃ delta0 Ccollar : ℝ, 0 < delta0 ∧ 0 < Ccollar ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        M.delta ≤ delta0 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P]
        (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
        (J : Type) [Countable J] [DecidableEq J] (j0 : J)
        (z : J → SpatialCoordinates d) (rad : J → ℝ)
        (hrad : ∀ j, 0 < rad j)
        (S : ∀ j, ResponseSpace (centeredCube (z j) (rad j) (hrad j)))
        (D : ∀ j, Submodule ℚ
          (DomainL2 (centeredCube (z j) (rad j) (hrad j))))
        [_hDc : ∀ j, Countable (D j)]
        (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
        (T : J → Type) [_hTc : ∀ j, Countable (T j)]
        (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
        (thetaH1 : ∀ j, T j →
          Homogenization.H1Function
            (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
        (usrc : ∀ j, (D j) → ℕ → Ω → (S j).space)
        (srcRep : ∀ j, (D j) → ℕ → Ω → SpatialCoordinates d → ℝ)
        (ucell : ∀ j, T j → ℕ → Ω →
          Homogenization.H1Function
            (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
        (E : _root_.SubdiffusiveProcess.Paper.in_J d)
        (Index : Type) [Countable Index]
        (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
        (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
        (coercivityKey extensionKey lambdaKey : J → Index)
        (sourceResponseKey sourceGrowthKey sourceHolderKey :
          ∀ j, (D j) → Index)
        (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
        (Grid : Type) [Countable Grid]
        (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J)
        (gridKey : Grid → Index)
        (_hz0 : z j0 = z0) (_hrad0 : rad j0 = R)
        (_hrepresented :
          _root_.SubdiffusiveProcess.Paper.conv_represented_estimates d hd M H Ω P cutoff env J j0 z rad hrad
            S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E
            Index resp respLim constants G coercivityKey extensionKey lambdaKey
            sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey
            cellGrowthKey cellHolderKey Grid origin gridRoot gridKey),
        let Q := centeredCube (z j0) (rad j0) (hrad j0)
        let S0 := S j0
        let aN := fun (omega : Ω) (n : ℕ) =>
          _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n omega) (cutoff n)
            (z j0) (hrad j0)
        let rawAN := fun (omega : Ω) (n : ℕ) =>
          cutoffCoefficient M H (env n omega) (cutoff n)
        ∃ KN : ℕ → Ω → ℝ, ∃ Ggood : Set Ω,
          MeasurableSet Ggood ∧ Ggood ⊆ G ∧ P (Ggoodᶜ) = 0 ∧
          (∀ n : ℕ, Measurable (KN n)) ∧
          (∀ n : ℕ, ∀ omega : Ω, 1 ≤ KN n omega) ∧
          (∀ p ∈ orders, ∃ Cp : ℝ, 0 ≤ Cp ∧
            ∀ n : ℕ,
              MemLp (KN n) (ENNReal.ofReal p) P ∧
                eLpNorm (KN n) (ENNReal.ofReal p) P ≤ ENNReal.ofReal Cp) ∧
          (∀ omega ∈ Ggood,
            BddAbove (Set.range (fun n : ℕ => KN n omega))) ∧
          ∀ omega ∈ Ggood,
            (∀ b : T j0, ∀ K O W : Set (SpatialCoordinates d), ∀ Jmesh : ℕ,
              IsCompact K → IsOpen O →
              closure O ⊆ (Q : Set (SpatialCoordinates d)) →
              IsOpen W → K ⊆ W → W ⊆ O →
              (∀ x : SpatialCoordinates d,
                0 ≤ theta j0 b x ∧ theta j0 b x ≤ 1) →
              (∀ x ∈ W, theta j0 b x = 1) →
              tsupport (theta j0 b) ⊆ O →
              (∀ k : OddGridIndex d (triadicHalf Jmesh),
                (closure
                    (oddGridCell (z j0) (rad j0) (hrad j0)
                      (triadicHalf Jmesh) k : Set (SpatialCoordinates d)) ∩
                    {x : SpatialCoordinates d |
                      0 < theta j0 b x ∧ theta j0 b x < 1}).Nonempty →
                  closure
                      (oddGridCell (z j0) (rad j0) (hrad j0)
                        (triadicHalf Jmesh) k : Set (SpatialCoordinates d)) ⊆
                    O \ K) →
              ∃ chiH : ℕ → Homogenization.H1Function
                  (Q : Set (SpatialCoordinates d)),
                ∃ chiS : ℕ → S0.space,
                  ∃ chic : ℕ → SpatialCoordinates d → ℝ,
                    ∃ V : Set (SpatialCoordinates d),
                      ∃ Benergy Ball Bholder : ℝ,
                        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧
                        0 ≤ Benergy ∧ 0 ≤ Ball ∧ 0 ≤ Bholder ∧
                        (∀ n : ℕ,
                          (chiS n).val = sobolevDataOfH1 (chiH n) ∧
                          ContinuousOn (chic n)
                            (closure (Q : Set (SpatialCoordinates d))) ∧
                          (chiS n).val.1 =ᵐ[
                            volume.restrict (Q : Set (SpatialCoordinates d))]
                            chic n ∧
                          (∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
                            0 ≤ chic n x ∧ chic n x ≤ 1) ∧
                          (∀ x ∈ V, chic n x = 1) ∧
                          (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                            x ∉ O → chic n x = 0) ∧
                          (∀ k : OddGridIndex d (triadicHalf Jmesh),
                            IsWeaklyHarmonicOn (rawAN omega n)
                              (oddGridCell (z j0) (rad j0) (hrad j0)
                                (triadicHalf Jmesh) k : Set (SpatialCoordinates d))
                              ((chiH n).restrict
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k).isOpen
                                (oddGridCell_subset (z j0) (hrad j0)
                                  (triadicHalf Jmesh) k)) ∧
                            HasZeroTraceDifferenceOn
                              (oddGridCell (z j0) (rad j0) (hrad j0)
                                (triadicHalf Jmesh) k : Set (SpatialCoordinates d))
                              ((chiH n).restrict
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k).isOpen
                                (oddGridCell_subset (z j0) (hrad j0)
                                  (triadicHalf Jmesh) k))
                              ((thetaH1 j0 b).restrict
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k).isOpen
                                (oddGridCell_subset (z j0) (hrad j0)
                                  (triadicHalf Jmesh) k))) ∧
                          (∀ k : OddGridIndex d (triadicHalf Jmesh),
                            (∃ c : ℝ, ∀ x ∈ closure
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                              theta j0 b x = c) →
                              ∀ i : Fin d, ∀ᵐ x ∂volume.restrict
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                                (chiS n).val.2 i x = 0) ∧
                          responseForm S0 (aN omega n) (chiS n) (chiS n) ≤ Benergy ∧
                          (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), ∀ s : ℝ,
                            0 < s → s ≤ 1 →
                            ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
                              (fun y => ENNReal.ofReal
                                ((aN omega n).val y *
                                  ∑ i : Fin d, ((chiS n).val.2 i y) ^ 2)))
                              (Metric.ball x s) ≤ ENNReal.ofReal (Ball * s ^ t)) ∧
                          _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
                            (closure (Q : Set (SpatialCoordinates d))) (chic n) ∧
                          _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
                            (closure (Q : Set (SpatialCoordinates d))) (chic n) ≤
                            Bholder) ∧
                        (∃ sigma : ℕ → ℕ, ∃ chiLim : SpatialCoordinates d → ℝ,
                          StrictMono sigma ∧
                          ContinuousOn chiLim
                            (closure (Q : Set (SpatialCoordinates d))) ∧
                          TendstoUniformlyOn (fun n => chic (sigma n)) chiLim atTop
                            (closure (Q : Set (SpatialCoordinates d))) ∧
                          (∀ k : OddGridIndex d (triadicHalf Jmesh),
                            (∃ c : ℝ, ∀ x ∈ closure
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                              theta j0 b x = c) →
                              ∀ x ∈ closure
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                                chiLim x = theta j0 b x))) ∧
            (∀ Jr : ℕ,
              let rho := rad j0 / (3 : ℝ) ^ Jr
                ∀ thetaR : SpatialCoordinates d → ℝ,
                  ContDiff ℝ ∞ thetaR →
                  (∀ x : SpatialCoordinates d,
                    0 ≤ thetaR x ∧ thetaR x ≤ 1) →
                  (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                    Metric.infDist x (frontier (Q : Set (SpatialCoordinates d))) ≤ rho →
                      thetaR x = 0) →
                  (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                    3 * rho ≤ Metric.infDist x (frontier (Q : Set (SpatialCoordinates d))) →
                      thetaR x = 1) →
                  (∀ x : SpatialCoordinates d,
                    norm (fderiv ℝ thetaR x) ≤ Cgrad / rho) →
                  ∀ thetaRH1 : Homogenization.H1Function
                    (Q : Set (SpatialCoordinates d)),
                    thetaRH1.toFun = thetaR →
                    ∃ collarH : ℕ → Homogenization.H1Function
                        (Q : Set (SpatialCoordinates d)),
                      ∃ collarS : ℕ → S0.space,
                        ∃ collarC : ℕ → SpatialCoordinates d → ℝ,
                          ∀ n : ℕ,
                            (collarS n).val = sobolevDataOfH1 (collarH n) ∧
                            ContinuousOn (collarC n)
                              (closure (Q : Set (SpatialCoordinates d))) ∧
                            (collarS n).val.1 =ᵐ[
                              volume.restrict (Q : Set (SpatialCoordinates d))]
                              collarC n ∧
                            (∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
                              0 ≤ collarC n x ∧ collarC n x ≤ 1) ∧
                            (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                              Metric.infDist x
                                  (frontier (Q : Set (SpatialCoordinates d))) ≤ rho →
                                collarC n x = 0) ∧
                            (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                              3 * rho ≤ Metric.infDist x
                                  (frontier (Q : Set (SpatialCoordinates d))) →
                                collarC n x = 1) ∧
                            (∀ i : Fin d, ∀ᵐ x ∂volume.restrict
                              (Q : Set (SpatialCoordinates d)),
                              3 * rho < Metric.infDist x
                                  (frontier (Q : Set (SpatialCoordinates d))) →
                                (collarS n).val.2 i x = 0) ∧
                            (∀ k : OddGridIndex d (triadicHalf Jr),
                              IsWeaklyHarmonicOn (rawAN omega n)
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jr) k : Set (SpatialCoordinates d))
                                ((collarH n).restrict
                                  (oddGridCell (z j0) (rad j0) (hrad j0)
                                    (triadicHalf Jr) k).isOpen
                                  (oddGridCell_subset (z j0) (hrad j0)
                                    (triadicHalf Jr) k)) ∧
                              HasZeroTraceDifferenceOn
                                (oddGridCell (z j0) (rad j0) (hrad j0)
                                  (triadicHalf Jr) k : Set (SpatialCoordinates d))
                                ((collarH n).restrict
                                  (oddGridCell (z j0) (rad j0) (hrad j0)
                                    (triadicHalf Jr) k).isOpen
                                  (oddGridCell_subset (z j0) (hrad j0)
                                    (triadicHalf Jr) k))
                                (thetaRH1.restrict
                                  (oddGridCell (z j0) (rad j0) (hrad j0)
                                    (triadicHalf Jr) k).isOpen
                                  (oddGridCell_subset (z j0) (hrad j0)
                                    (triadicHalf Jr) k))) ∧
                            responseForm S0 (aN omega n) (collarS n) (collarS n) ≤
                              Ccollar * KN n omega * rho ^ (-1 - eta)) := by
  exact aux_lem_cutoffs_of_mesh_collar d hd z0 R hR beta alpha eta t hbeta hbetaalpha halpha
    heta htlow htupper hetaalpha orders horders Cext Cgrad hCext hCgrad
    (aux_lem_cutoffs_mesh_collar d hd z0 R hR beta alpha eta t hbeta hbetaalpha halpha heta
      htlow htupper hetaalpha orders horders Cext Cgrad hCext hCgrad)

end SubdiffusiveProcess.Paper
