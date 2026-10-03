module

public import SubdiffusiveProcess.CoarseGrainingVocab.AnnealedProviders
public import SubdiffusiveProcess.CoarseGrainingVocab.PrefixSuffixMeasurability

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory Homogenization Homogenization.Book
open scoped ENNReal

noncomputable section

-- REUSE-CANDIDATE: Algsuperdiff/Section3/Provider/Annealed/RealStationaryTransfer.lean
-- PROVENANCE: the response-covariance step uses CoarseGraining's
-- `ResponseJ_translateSet_eq_translateCoeffField`; the measure transfer mirrors
-- Algsuperdiff's real-stationarity consumer named above.
theorem paperScalarProbeMaxOn_cube_eq_origin_translated {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (Q : TriadicCube d)
    (alpha : ℝ) :
    paperScalarProbeMaxOn (Ch02.cubeDomain Q)
        (aCutoffCoeffOnData M L omega (Ch02.cubeDomain Q)).toCoeffOn alpha =
      paperScalarProbeMaxOn
        (Ch02.cubeDomain (Homogenization.originCube d Q.scale))
        (aCutoffCoeffOnData M L
          (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSequence
            (Homogenization.triadicCubeShift Q) omega)
          (Ch02.cubeDomain (Homogenization.originCube d Q.scale))).toCoeffOn alpha := by
  unfold paperScalarProbeMaxOn
  apply iSup_congr
  intro e
  congr 1
  simp only [J]
  rw [Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ]
  rw [Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ]
  rw [Ch02.cubeDomain_coe,
    Homogenization.openCubeSet_eq_translateSet_originCube_of_triadicCube Q]
  rw [Homogenization.ResponseJ_translateSet_eq_translateCoeffField]
  apply congrArg (Homogenization.ResponseJ
    (Homogenization.openCubeSet (Homogenization.originCube d Q.scale))
    ((Real.sqrt alpha)⁻¹ • (e : Vec d)) (Real.sqrt alpha • (e : Vec d)))
  funext x
  change Homogenization.scalarMatrix
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega
        (x + Homogenization.triadicCubeShift Q)) =
    Homogenization.scalarMatrix
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L
        (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSequence
          (Homogenization.triadicCubeShift Q) omega) x)
  exact congrArg Homogenization.scalarMatrix
    (aCutoff_translatePotentialSequence M L
      (Homogenization.triadicCubeShift Q) omega x).symm

theorem normalizedDefect_cube_eq_origin_translated {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (Q : TriadicCube d) :
    normalizedDefect M L (Ch02.cubeDomain Q) omega =
      normalizedDefect M L
        (Ch02.cubeDomain (Homogenization.originCube d Q.scale))
        (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSequence
          (Homogenization.triadicCubeShift Q) omega) := by
  unfold normalizedDefect
  exact paperScalarProbeMaxOn_cube_eq_origin_translated M L omega Q (ahom M L)

theorem paperENNRealLpNorm_normalizedDefect_cube_eq_origin {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (xi : ℝ)
    (Q : TriadicCube d) :
    paperENNRealLpNorm M.P.toMeasure xi
        (normalizedDefect M L (Ch02.cubeDomain Q)) =
      paperENNRealLpNorm M.P.toMeasure xi
        (normalizedDefect M L
          (Ch02.cubeDomain (Homogenization.originCube d Q.scale))) := by
  rw [show normalizedDefect M L (Ch02.cubeDomain Q) =
      fun omega => normalizedDefect M L
        (Ch02.cubeDomain (Homogenization.originCube d Q.scale))
        (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSequence
          (Homogenization.triadicCubeShift Q) omega) by
    funext omega
    exact normalizedDefect_cube_eq_origin_translated M L omega Q]
  unfold paperENNRealLpNorm
  let F := fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
    normalizedDefect M L
      (Ch02.cubeDomain (Homogenization.originCube d Q.scale)) omega ^ xi
  have hbase : Measurable (normalizedDefect M L
      (Ch02.cubeDomain (Homogenization.originCube d Q.scale))) :=
    (measurable_normalizedDefect_potentialShellIndexSigma_Iic M L
      (Ch02.cubeDomain (Homogenization.originCube d Q.scale))).mono
        (potentialShellIndexSigma_le_borel (d := d) (Set.Iic L)) le_rfl
  have hF : Measurable F := ENNReal.continuous_rpow_const.measurable.comp hbase
  have hT := measurable_translatePotentialSequence
    (Homogenization.triadicCubeShift Q)
  have hmap := potentialSequenceLaw_stationary M
    (Homogenization.triadicCubeShift Q)
  change (∫⁻ omega, F
      (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSequence
        (Homogenization.triadicCubeShift Q) omega) ∂M.P.toMeasure) ^ xi⁻¹ =
    (∫⁻ omega, F omega ∂M.P.toMeasure) ^ xi⁻¹
  rw [← MeasureTheory.lintegral_map hF hT, hmap]

theorem inductionHypothesis_normalizedDefect_cube {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m0 k : ℕ} {xi delta1 : ℝ}
    (hS : inductionHypothesis M m0 xi delta1) (hk : k ≤ m0)
    (Q : TriadicCube d) (hQ : Q.scale = (k : ℤ)) :
    paperENNRealLpNorm M.P.toMeasure xi
        (normalizedDefect M k (Ch02.cubeDomain Q)) ≤ ENNReal.ofReal delta1 := by
  rw [paperENNRealLpNorm_normalizedDefect_cube_eq_origin M k xi Q, hQ]
  let kfin : Fin (m0 + 1) := ⟨k, Nat.lt_succ_iff.mpr hk⟩
  exact (le_iSup (fun m : Fin (m0 + 1) => paperENNRealLpNorm M.P.toMeasure xi
    (normalizedDefect M m
      (Ch02.cubeDomain (Homogenization.originCube d (m : ℤ))))) kfin).trans hS.2.2.2

end

end SubdiffusiveProcess.CoarseGrainingVocab
