module

public import SubdiffusiveProcess.Paper.Support.B7cFiniteCellIdentification
public import SubdiffusiveProcess.Paper.in_represented_catalogue
public import SubdiffusiveProcess.Paper.conv_represented_estimates

@[expose] public section





set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff BigOperators
noncomputable section
namespace Paper

/-- The actual represented catalogue supplies the cell estimates for the
finite interpolants in the repaired boundary statement. -/
theorem aux_mfd_prop_boundary_catalogue_bounds
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
    (J : Type) [Countable J] [DecidableEq J] (j0 : J)
    (z : J → SpatialCoordinates d) (rad : J → ℝ) (hr : ∀ j, 0 < rad j)
    (S : ∀ j, ResponseSpace (centeredCube (z j) (rad j) (hr j)))
    (D : ∀ j, Submodule ℚ (DomainL2 (centeredCube (z j) (rad j) (hr j))))
    [hDc : ∀ j, Countable (D j)]
    (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
    (T : J → Type) [hTc : ∀ j, Countable (T j)]
    (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
    (thetaH1 : ∀ j, T j →
      Homogenization.H1Function
        (centeredCube (z j) (rad j) (hr j) : Set (SpatialCoordinates d)))
    (usrc : ∀ j, (D j) → ℕ → Ω → (S j).space)
    (srcRep : ∀ j, (D j) → ℕ → Ω → SpatialCoordinates d → ℝ)
    (ucell : ∀ j, T j → ℕ → Ω →
      Homogenization.H1Function
        (centeredCube (z j) (rad j) (hr j) : Set (SpatialCoordinates d)))
    (Cext : ℝ) (beta alpha eta t : ℝ) (orders : Finset ℝ)
    (E : Paper.in_J d)
    (Index : Type) [Countable Index]
    (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
    (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
    (coercivityKey extensionKey lambdaKey : J → Index)
    (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ j, (D j) → Index)
    (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
    (Grid : Type) [Countable Grid]
    (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J) (gridKey : Grid → Index)
    (hrepresented : conv_represented_estimates d hd M H Ω P cutoff env J j0 z rad hr
      S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E
      Index resp respLim constants G coercivityKey extensionKey lambdaKey
      sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey
      cellGrowthKey cellHolderKey Grid origin gridRoot gridKey)
    (omega : Ω) (hmem : omega ∈ G) (iQ : J)
    (zq : SpatialCoordinates d) (rq : ℝ) (hrq : 0 < rq) (h3rq : 0 < 3 * rq)
    (hz : z iQ = zq) (hrad : rad iQ = 3 * rq)
    (g : D iQ)
    (betaQ : H1Function (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d)))
    (hBeta : betaQ.toFun = f iQ g)
    (UN : ℕ → H1Function (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d)))
    (hFinite : ∀ k : OddGridIndex d (triadicHalf 1),
      let qk := oddGridCell zq (3 * rq) h3rq (triadicHalf 1) k
      let hsub := oddGridCell_subset zq h3rq (triadicHalf 1) k
      ∀ n,
        IsWeaklyHarmonicOn (cutoffCoefficient M H (env n omega) (cutoff n))
          (qk : Set (SpatialCoordinates d)) ((UN n).restrict qk.isOpen hsub) ∧
        HasZeroTraceDifferenceOn (qk : Set (SpatialCoordinates d))
          ((UN n).restrict qk.isOpen hsub) (betaQ.restrict qk.isOpen hsub) ∧
        ContinuousOn (UN n).toFun (closure (qk : Set (SpatialCoordinates d)))) :
    ∃ Bcell Hcell : OddGridIndex d (triadicHalf 1) → ℝ,
      (∀ k, 0 ≤ Bcell k ∧ 0 ≤ Hcell k) ∧
      ∀ k : OddGridIndex d (triadicHalf 1), ∀ n,
        energy (cutoffCoefficient M H (env n omega) (cutoff n))
          (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) k : Set (SpatialCoordinates d))
          ((UN n).restrict (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) k).isOpen
            (oddGridCell_subset zq h3rq (triadicHalf 1) k)) ≤ Bcell k ∧
        (∀ x ∈ closure (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) k : Set (SpatialCoordinates d)),
          ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) k : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal (cutoffCoefficient M H (env n omega) (cutoff n) y *
                ∑ i : Fin d, ((UN n).grad y i) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (Bcell k * rr ^ t)) ∧
        (∀ x ∈ closure (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) k : Set (SpatialCoordinates d)),
          ∀ y ∈ closure (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) k : Set (SpatialCoordinates d)),
            |(UN n).toFun x - (UN n).toFun y| ≤ Hcell k * dist x y ^ alpha) ∧
        (∀ x ∈ closure (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) k : Set (SpatialCoordinates d)),
          |(UN n).toFun x| ≤ Hcell k) := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  rcases hrepresented with
    ⟨ht, ha, hb, hC, hord, hcut, hIR, hmeas, hlaw, hseq, hroot, hrat, htri,
      hcomplete, horigin, hgrid, hS, hdense, hsource, hsdense, htrace,
      hsourceTrace, hrestrict, happrox, hplateau, hcmeas, hmoment, hnonneg,
      hresponse, hcoarse, hcoercive, habsolute, hgridbound, hsourcebound, hcellbound⟩
  have halpha : 0 < alpha := by linarith only [hb.1, hb.2]
  let Q := centeredCube zq (3 * rq) h3rq
  have hQeq : centeredCube (z iQ) (rad iQ) (hr iQ) = Q := by
    apply SetLike.coe_injective
    change Metric.ball (z iQ) (rad iQ / 2) = Metric.ball zq (3 * rq / 2)
    rw [hz, hrad]
  obtain ⟨ell, hell⟩ := htri iQ
  have hRq : rq = (3 : ℝ) ^ (ell - 1) := by
    calc rq = rad iQ / 3 := by rw [hrad]; ring
      _ = (3 : ℝ) ^ ell / 3 := by rw [hell]
      _ = (3 : ℝ) ^ (ell - 1) := by
        rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
  have hRootRat : ∀ i : Fin d, ∃ q : ℚ, zq i = (q : ℝ) := by
    simpa only [hz] using hrat iQ
  have hSideRat : ∃ q : ℚ, 3 * rq = (q : ℝ) := by
    refine ⟨(3 : ℚ) ^ ell, ?_⟩
    rw [← hrad, hell]
    simp only [Rat.cast_zpow, Rat.cast_ofNat]
  obtain ⟨hParent, hThetaParent⟩ := hsourceTrace iQ g
  have hex : ∀ k : OddGridIndex d (triadicHalf 1),
      ∃ B HH : ℝ, 0 ≤ B ∧ 0 ≤ HH ∧ ∀ n,
        energy (cutoffCoefficient M H (env n omega) (cutoff n))
          (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) k : Set (SpatialCoordinates d))
          ((UN n).restrict (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) k).isOpen
            (oddGridCell_subset zq h3rq (triadicHalf 1) k)) ≤ B ∧
        (∀ x ∈ closure (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) k : Set (SpatialCoordinates d)),
          ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) k : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal (cutoffCoefficient M H (env n omega) (cutoff n) y *
                ∑ i : Fin d, ((UN n).grad y i) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)) ∧
        (∀ x ∈ closure (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) k : Set (SpatialCoordinates d)),
          ∀ y ∈ closure (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) k : Set (SpatialCoordinates d)),
            |(UN n).toFun x - (UN n).toFun y| ≤ HH * dist x y ^ alpha) ∧
        (∀ x ∈ closure (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) k : Set (SpatialCoordinates d)),
          |(UN n).toFun x| ≤ HH) := by
    intro k
    let qk := oddGridCell zq (3 * rq) h3rq (triadicHalf 1) k
    have hsub := oddGridCell_subset zq h3rq (triadicHalf 1) k
    have hratK := aux_in_represented_catalogue_ratCoord_oddGridCenter d (triadicHalf 1)
      zq (3 * rq) k hRootRat hSideRat
    have hInRoot : (centeredCube (oddGridCenter zq (3 * rq) (triadicHalf 1) k) rq hrq :
        Set (SpatialCoordinates d)) ⊆
        (centeredCube (z j0) (rad j0) (hr j0) : Set (SpatialCoordinates d)) := by
      rw [← aux_prop_gluing_cell_eq zq rq hrq h3rq k]
      exact hsub.trans (by simpa only [hQeq] using hroot iQ)
    obtain ⟨jc, hjz, hjr⟩ := hcomplete _ rq hrq hratK ⟨ell - 1, hRq⟩ hInRoot
    have hQchild : centeredCube (z jc) (rad jc) (hr jc) = qk := by
      apply SetLike.coe_injective
      change Metric.ball (z jc) (rad jc / 2) = (qk : Set (SpatialCoordinates d))
      rw [hjz, hjr]
      exact (aux_prop_gluing_cell_eq zq rq hrq h3rq k).symm
    have hChildParent : (centeredCube (z jc) (rad jc) (hr jc) : Set (SpatialCoordinates d)) ⊆
        (centeredCube (z iQ) (rad iQ) (hr iQ) : Set (SpatialCoordinates d)) := by
      rw [hQchild, hQeq]
      exact hsub
    obtain ⟨hc, hThetaChild⟩ := hrestrict iQ jc hChildParent hParent
    have hTheta : theta jc hc = f iQ g := hThetaChild.trans hThetaParent
    obtain ⟨MR, hMR⟩ := (hseq.2.2.2.1 (cellResponseKey jc hc) omega hmem).bddAbove_range
    obtain ⟨MG, hMG⟩ := hseq.2.2.2.2 (cellGrowthKey jc hc) omega hmem
    obtain ⟨MH, hMH⟩ := hseq.2.2.2.2 (cellHolderKey jc hc) omega hmem
    let C2 := Lane4.c2Norm (closure (centeredCube (z jc) (rad jc) (hr jc) : Set (SpatialCoordinates d)))
      (theta jc hc)
    let CG := max 0 MG * C2 ^ 2
    let CH := max 0 MH * max 0 C2
    have hNative : ∃ (psi : H1Function (qk : Set (SpatialCoordinates d)))
        (v : ℕ → H1Function (qk : Set (SpatialCoordinates d))),
        psi.toFun = f iQ g ∧
        (∀ n, IsWeaklyHarmonicOn (cutoffCoefficient M H (env n omega) (cutoff n))
          (qk : Set (SpatialCoordinates d)) (v n)) ∧
        (∀ n, HasZeroTraceDifferenceOn (qk : Set (SpatialCoordinates d)) (v n) psi) ∧
        (∀ n, ContinuousOn (v n).toFun (closure (qk : Set (SpatialCoordinates d)))) ∧
        (∀ n, energy (cutoffCoefficient M H (env n omega) (cutoff n))
          (qk : Set (SpatialCoordinates d)) (v n) ≤ MR) ∧
        (∀ n, ∀ x ∈ closure (qk : Set (SpatialCoordinates d)),
          ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict (qk : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal (cutoffCoefficient M H (env n omega) (cutoff n) y *
                ∑ i : Fin d, ((v n).grad y i) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (CG * rr ^ t)) ∧
        (∀ n, Lane4.IsHolderOn alpha (closure (qk : Set (SpatialCoordinates d))) (v n).toFun) ∧
        (∀ n, Lane4.cAlphaNorm alpha (closure (qk : Set (SpatialCoordinates d))) (v n).toFun ≤ CH) := by
      rw [← hQchild]
      refine ⟨thetaH1 jc hc, (fun n => ucell jc hc n omega),
        (htrace jc hc).2.trans hTheta,
        (fun n => ((hresponse jc n omega hmem).2 hc).1),
        (fun n => ((hresponse jc n omega hmem).2 hc).2.1),
        (fun n => ((hresponse jc n omega hmem).2 hc).2.2.1), ?_, ?_,
        (fun n => (hcellbound jc hc n omega hmem).2.1), ?_⟩
      · intro n
        rw [native_harmonic_energy_eq_infimum
          (Lane4.cutoffPositiveCoefficient M H (env n omega) (cutoff n) (z jc) (hr jc))
          _ (FiniteStopping.cutoffCoefficient_ae M H (env n omega) (cutoff n) (z jc) (hr jc))
          (thetaH1 jc hc) (ucell jc hc n omega)
          (((hresponse jc n omega hmem).2 hc).2.1) (((hresponse jc n omega hmem).2 hc).1)]
        rw [← ((hresponse jc n omega hmem).2 hc).2.2.2.2]
        exact hMR (Set.mem_range_self n)
      · intro n x hx rr hrr hrr1
        have hAe := FiniteStopping.cutoffCoefficient_ae M H (env n omega) (cutoff n) (z jc) (hr jc)
        have hDensity : (fun y => ENNReal.ofReal (
            (Lane4.cutoffPositiveCoefficient M H (env n omega) (cutoff n) (z jc) (hr jc)).val y *
            ∑ i : Fin d, ((sobolevDataOfH1 (ucell jc hc n omega)).2 i y) ^ 2))
            =ᵐ[volume.restrict (centeredCube (z jc) (rad jc) (hr jc) : Set (SpatialCoordinates d))]
            (fun y => ENNReal.ofReal (cutoffCoefficient M H (env n omega) (cutoff n) y *
              ∑ i : Fin d, ((ucell jc hc n omega).grad y i) ^ 2)) := by
          have hg := ae_all_iff.mpr (fun i : Fin d =>
            sobolevDataOfH1_snd_coeFn (ucell jc hc n omega) i)
          filter_upwards [hAe, hg] with y hy hgy
          simp only [hy, hgy]
        rw [← withDensity_congr_ae hDensity]
        exact ((hcellbound jc hc n omega hmem).1 x hx rr hrr hrr1).trans
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (((le_abs_self _).trans (hMG n)).trans (le_max_right _ _)) (sq_nonneg C2))
            (Real.rpow_nonneg hrr.le t)))
      · intro n
        exact ((hcellbound jc hc n omega hmem).2.2).trans
          ((mul_le_mul_of_nonneg_left (le_max_right 0 C2)
            (hnonneg (cellHolderKey jc hc) omega hmem n)).trans
            (mul_le_mul_of_nonneg_right
              (((le_abs_self _).trans (hMH n)).trans (le_max_right 0 MH))
              (le_max_left 0 C2)))
    obtain ⟨psi, v, hpsi, hv, hvt, hvc, henergy, hgrowth, hholder, hnorm⟩ := hNative
    obtain ⟨B, HH, hB, hHH, hbound⟩ := aux_mfd_prop_boundary_catalogue_cell_bounds
      (oddGridCenter zq (3 * rq) (triadicHalf 1) k)
      (3 * rq / (2 * (triadicHalf 1 : ℝ) + 1)) (div_pos h3rq (by positivity))
      (fun n => cutoffCoefficient M H (env n omega) (cutoff n))
      (fun n => aux_mfd_prop_boundary_cutoff_continuous M H (env n omega) (cutoff n))
      (fun n => aux_mfd_prop_boundary_cutoff_elliptic_closure M H (env n omega) (cutoff n) _ _ _)
      (betaQ.restrict qk.isOpen hsub) psi (hBeta.trans hpsi.symm) v hv hvt hvc
      alpha t halpha MR CG CH henergy hgrowth hholder hnorm
    exact ⟨B, HH, hB, hHH, fun n => hbound n ((UN n).restrict qk.isOpen hsub)
      (hFinite k n).1 (hFinite k n).2.1 (hFinite k n).2.2⟩
  choose B H hB hH hBounds using hex
  exact ⟨B, H, fun k => ⟨hB k, hH k⟩, hBounds⟩

end Paper
