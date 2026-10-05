module

public import SubdiffusiveProcess.Paper.candidate_good_estimates_trace_support
public import SubdiffusiveProcess.Sobolev.GoodextHolderLimit

@[expose] public section

/-! A bounded bank of actual source responses has a uniform continuous subsequential limit.
The probabilistic extraction of the bound and the finite regularity estimate are inputs.
-/

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped Topology ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Uniformly bounded continuous Hölder source responses converge along a subsequence to the actual operator-limit representative. -/
theorem candidate_source_compact_bank
    {d : ℕ} [NeZero d]
    (Qc : SpatialCoordinates d) (Qr : ℝ) (hQr : 0 < Qr)
    (beta : ℝ) (hbeta : beta ∈ Ioo (1 / 2 : ℝ) 1)
    (S : ResponseSpace (centeredCube Qc Qr hQr))
    (hS : S.space = killedSobolevGraph (centeredCube Qc Qr hQr))
    (aN : ℕ → PositiveCoefficient (centeredCube Qc Qr hQr))
    (GN : ℕ → DomainL2 (centeredCube Qc Qr hQr) →L[ℝ]
      DomainL2 (centeredCube Qc Qr hQr))
    (hGN : ∀ n fL2, GN n fL2 =
      (responseSolution S (aN n) ((sobolevVolumeLoad fL2).comp S.space.subtypeL)).val.1)
    (G : DomainL2 (centeredCube Qc Qr hQr) →L[ℝ] DomainL2 (centeredCube Qc Qr hQr))
    (hG : Tendsto GN atTop (𝓝 G))
    (f : SpatialCoordinates d → ℝ) (fL2 : DomainL2 (centeredCube Qc Qr hQr))
    (hfL2 : (fL2 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube Qc Qr hQr : Set (SpatialCoordinates d))] f)
    (K : ℝ) (hK : 0 ≤ K)
    (hSource : ∀ n, ∀ u : killedSobolevGraph (centeredCube Qc Qr hQr),
      (∀ psi : killedSobolevGraph (centeredCube Qc Qr hQr),
        sobolevCoefficientForm (aN n) u.val psi.val =
          ∫ x in (centeredCube Qc Qr hQr : Set (SpatialCoordinates d)), f x * psi.val.1 x) →
      ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
        (u.val.1 : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube Qc Qr hQr : Set (SpatialCoordinates d))] U ∧
        (∀ x ∈ frontier (centeredCube Qc Qr hQr : Set (SpatialCoordinates d)), U x = 0) ∧
        IsHolderOn beta (closedCube Qc Qr hQr : Set (SpatialCoordinates d)) U ∧
        cAlphaNorm beta (closedCube Qc Qr hQr : Set (SpatialCoordinates d)) U ≤ K) :
    ∃ (U : SpatialCoordinates d → ℝ) (ns : ℕ → ℕ)
      (UN : ℕ → SpatialCoordinates d → ℝ), StrictMono ns ∧
      ContinuousOn U (closure (centeredCube Qc Qr hQr : Set (SpatialCoordinates d))) ∧
      (G fL2 : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube Qc Qr hQr : Set (SpatialCoordinates d))] U ∧
      (∀ x ∈ frontier (centeredCube Qc Qr hQr : Set (SpatialCoordinates d)), U x = 0) ∧
      IsHolderOn beta (closure (centeredCube Qc Qr hQr : Set (SpatialCoordinates d))) U ∧
      TendstoUniformlyOn UN U atTop
        (closure (centeredCube Qc Qr hQr : Set (SpatialCoordinates d))) ∧
      ∀ n, Continuous (UN n) ∧
        (GN (ns n) fL2 : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube Qc Qr hQr : Set (SpatialCoordinates d))] UN n := by
  classical
  let Q := centeredCube Qc Qr hQr
  have hclosed : closure (Q : Set (SpatialCoordinates d)) =
      (closedCube Qc Qr hQr : Set (SpatialCoordinates d)) := by
    exact closure_ball Qc (ne_of_gt (half_pos hQr))
  have hbpos : 0 < beta := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hbeta.1
  have hBank : ∀ n, ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
      (GN n fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U ∧
      (∀ x ∈ frontier (Q : Set (SpatialCoordinates d)), U x = 0) ∧
      IsHolderOn beta (closure (Q : Set (SpatialCoordinates d))) U ∧
      cAlphaNorm beta (closure (Q : Set (SpatialCoordinates d))) U ≤ K := by
    intro n
    obtain ⟨u, hu, hsolve⟩ := aux_candidate_good_estimates_trace_support_response_killed Q S hS
      (aN n) f fL2 hfL2
    obtain ⟨U, hUc, hUr, hUb, hUh, hUn⟩ := hSource n u hsolve
    refine ⟨U, hUc, ?_, hUb, ?_, ?_⟩
    · rw [hGN n fL2, ← hu]
      exact hUr
    · simpa only [hclosed] using hUh
    · simpa only [hclosed] using hUn
  choose BN hBN using hBank
  have hpointwise (n : ℕ) := aux_lem_goodext_pointwise_of_cAlpha beta K hbpos
    (closure (Q : Set (SpatialCoordinates d))) (centeredCube_isBounded Qc hQr).isCompact_closure
    (BN n) (hBN n).1.continuousOn (hBN n).2.2.2.1 (hBN n).2.2.2.2
  have hEqui : ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      ∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
      ∀ y ∈ closure (Q : Set (SpatialCoordinates d)),
        |BN n x - BN n y| ≤ C * dist x y ^ beta := by
    refine ⟨K * (Real.sqrt d) ^ beta, mul_nonneg hK
      (Real.rpow_nonneg (Real.sqrt_nonneg _) _), ?_⟩
    intro n x hx y hy
    calc
      |BN n x - BN n y| ≤ K * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta :=
        (hpointwise n).2.2 x hx y hy
      _ ≤ K * (Real.sqrt d * dist x y) ^ beta :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Real.sqrt_nonneg _) (aux_lem_goodext_euclid_le x y) hbpos.le) hK
      _ = (K * (Real.sqrt d) ^ beta) * dist x y ^ beta := by
        rw [Real.mul_rpow (Real.sqrt_nonneg _) dist_nonneg, mul_assoc]
  have hPoint : ∃ x ∈ closure (Q : Set (SpatialCoordinates d)),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n, |BN n x| ≤ C := by
    have hc : Qc ∈ closure (Q : Set (SpatialCoordinates d)) :=
      subset_closure (Metric.mem_ball_self (half_pos hQr))
    exact ⟨Qc, hc, K, hK, fun n => (hpointwise n).2.1 Qc hc⟩
  have hrec : Tendsto (fun n => GN n fL2) atTop (𝓝 (G fL2)) :=
    ((continuous_id.clm_apply continuous_const).tendsto G).comp hG
  obtain ⟨U, ns, hns, hUc, hUr, hUb, hUp, hUni⟩ :=
    aux_candidate_good_estimates_trace_support_compact_rep Qc Qr hQr beta hbeta
      (fun n => GN n fL2) BN (fun n => (hBN n).2.1)
      (fun n => (hBN n).2.2.1) hEqui hPoint (G fL2) hrec
  have hUh : IsHolderOn beta (closure (Q : Set (SpatialCoordinates d))) U := by
    refine ⟨K, ?_⟩
    rintro v ⟨x, hx, y, hy, hxy, rfl⟩
    apply le_of_tendsto (((hUp x hx).sub (hUp y hy)).abs.div_const _)
    apply Eventually.of_forall
    intro n
    have hSup : 0 ≤ sSup {v : ℝ | ∃ x ∈ closure (Q : Set (SpatialCoordinates d)), v = |BN (ns n) x|} :=
      Real.sSup_nonneg (by rintro v ⟨x, hx, rfl⟩; exact abs_nonneg _)
    exact (le_csSup (hBN (ns n)).2.2.2.1 ⟨x, hx, y, hy, hxy, rfl⟩).trans
      ((le_add_of_nonneg_left hSup).trans (hBN (ns n)).2.2.2.2)
  exact ⟨U, ns, fun n => BN (ns n), hns, hUc, hUr, hUb, hUh, hUni,
    fun n => ⟨(hBN (ns n)).1, (hBN (ns n)).2.1⟩⟩

end SubdiffusiveProcess.Paper
