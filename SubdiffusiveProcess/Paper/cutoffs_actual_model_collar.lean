import SubdiffusiveProcess.Paper.lem_cutoffs

open Filter MeasureTheory Set TopologicalSpace Metric
open SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal BigOperators Topology ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-! The existing collar construction with a direct grid envelope. The full
represented record is used for geometry and the actual cell PDE. The direct
grid bound permits a minimum of two independently proved envelopes. -/
theorem aux_lem_cutoffs_actual_model_collar_cell
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
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
    (E : Paper.in_J d)
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
      Paper.conv_represented_estimates d hd M H Ω P cutoff env J j0 z rad hrad
        S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E
        Index resp respLim constants G coercivityKey extensionKey lambdaKey
        sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey
        cellGrowthKey cellHolderKey Grid origin gridRoot gridKey)
    (Cgrad : ℝ) (hCgrad : 0 < Cgrad) (κ : ℤ) (hκ : rad j0 = (3 : ℝ) ^ κ)
    (g0 : Grid) (hg0 : gridRoot g0 = j0 ∧ origin g0 = z j0)
    (omega : Ω) (homega : omega ∈ G) (n : ℕ) (Kn : ℝ) (hKn : 0 ≤ Kn)
    (hgrid : ∀ (kp : ℕ) (j : J), kp ≤ cutoff n →
      rad j = (3 : ℝ) ^ (-(kp : ℤ)) →
      (∃ idx : Fin d → ℤ, z j =
        (fun i => origin g0 i + (3 : ℝ) ^ (-(kp : ℤ)) * (idx i : ℝ))) →
      (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)) ⊆
        (centeredCube (z (gridRoot g0)) (rad (gridRoot g0)) (hrad (gridRoot g0)) :
          Set (SpatialCoordinates d)) →
      constants (extensionKey j) n omega ≤ Kn * (rad j) ^ (-eta))
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
    -, -, hnonneg, -, -, -, hI, _, -, -⟩ := hrepresented
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
  · push_neg at hc
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
      have hext : constants (extensionKey j_cell) n omega ≤ Kn * ρ ^ (-eta) := by
        have he := hgrid kp j_cell hN (by rw [hjr]; exact hρz) hidx hsub'
        simpa only [hjr, ← hρdef] using he
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
      push_neg at hN
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


theorem cutoffs_actual_model_collar
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
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
    (E : Paper.in_J d)
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
      Paper.conv_represented_estimates d hd M H Ω P cutoff env J j0 z rad hrad
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
    (hgrid : ∀ n (kp : ℕ) (j : J), kp ≤ cutoff n →
      rad j = (3 : ℝ) ^ (-(kp : ℤ)) →
      (∃ idx : Fin d → ℤ, z j =
        (fun i => origin g0 i + (3 : ℝ) ^ (-(kp : ℤ)) * (idx i : ℝ))) →
      (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)) ⊆
        (centeredCube (z (gridRoot g0)) (rad (gridRoot g0)) (hrad (gridRoot g0)) :
          Set (SpatialCoordinates d)) →
      constants (extensionKey j) n omega ≤ KN n omega * (rad j) ^ (-eta))
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
      Lane4.cutoffPositiveCoefficient M H (env n omega) (cutoff n)
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
  haveI : NeZero d := ⟨by omega⟩
  have hrep := hrepresented
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hSk, -⟩ := hrep
  obtain ⟨I, hI, hsum⟩ := hCsum Jr rho thetaR hone rfl
  obtain ⟨collarH, collarS, collarC, hcol⟩ := aux_lem_cutoffs_collar_generic hd (z j0) (rad j0)
    (hrad j0) (S j0) (hSk j0) (fun n => cutoffCoefficient M H (env n omega) (cutoff n))
    (fun n => (aux_lem_cutoffs_cutoffCoefficient_cont_pos M H (env n omega) (cutoff n)).1)
    (fun n => (aux_lem_cutoffs_cutoffCoefficient_cont_pos M H (env n omega) (cutoff n)).2)
    (fun n => Lane4.cutoffPositiveCoefficient M H (env n omega) (cutoff n) (z j0) (hrad j0))
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
    (fun n k _ => aux_lem_cutoffs_actual_model_collar_cell d hd M H Cext beta alpha eta t orders Ω P
      cutoff env J j0 z rad hrad S D f T theta thetaH1 usrc srcRep ucell E Index resp respLim
      constants G coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey
      sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey
      hrepresented Cgrad hCgrad κ hκ g0 hg0 omega homega n (KN n omega)
      (zero_le_one.trans (hKN n)) (hgrid n) (Mhi n) (hMhi n) (hMK n) Jr k (jc Jr k)
      (hjc Jr k).1 (hjc Jr k).2 (hcoarse n Jr k) thetaR hsmooth hrange hgradR thetaRH1 hH1) n


end Paper
