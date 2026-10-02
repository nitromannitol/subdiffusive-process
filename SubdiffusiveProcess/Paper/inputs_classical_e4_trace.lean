import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Lane2.ExternalInputs
import SubdiffusiveProcess.Analysis.HolderExtension
import SubdiffusiveProcess.CubeTrace.Extension
import SubdiffusiveProcess.CubeTrace.Sobolev
import SubdiffusiveProcess.CubeTrace.SobolevAssembly
import SubdiffusiveProcess.CubeTrace.Glue

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

theorem inputs_classical_e4_trace (d : ℕ) (hd : 2 ≤ d) :
    ∀ (beta : ℝ) (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1),
    ∃ C : ℝ, 0 < C ∧ ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r = 1 →
    ∀ (G : SpatialCoordinates d → ℝ),
      IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G →
      ∃ b : weakSobolevGraph (centeredCube z r hr),
        ∃ U : SpatialCoordinates d → ℝ,
          Continuous U ∧
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
          (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), U x = G x) ∧
          (∀ i : Fin d,
            cubeFractionalL2Seminorm hd z r hr
              ⟨(beta - 1 / 2) / 2, by
                have h1 := hbeta.1
                have h2 := hbeta.2
                constructor <;> simp only [Set.mem_Ioo] at * <;> linarith⟩
              (fun _ : Fin 1 => ((b : SobolevData (centeredCube z r hr)).2 i)) < ⊤) ∧
          ∑ i : Fin d,
              cubeFractionalSqNorm hd z r hr
                ⟨(beta - 1 / 2) / 2, by
                  have h1 := hbeta.1
                  have h2 := hbeta.2
                  constructor <;> simp only [Set.mem_Ioo] at * <;> linarith⟩
                ((b : SobolevData (centeredCube z r hr)).2 i) ≤
            C * (r ^ beta *
              holderSeminorm beta
                (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2 := by
  classical
  intro beta hbeta
  haveI : NeZero d := ⟨by omega⟩
  have hb0 : 0 < beta := by linarith [hbeta.1]
  have hb1 : beta ≤ 1 := hbeta.2.le
  obtain ⟨Cb, hCb0, hCb⟩ := SubdiffusiveProcess.CubeTrace.ct_extension_bounds (d := d)
    (β := beta) ⟨hb0, hbeta.2⟩
  obtain ⟨Cs, hCs0, hCs⟩ := SubdiffusiveProcess.CubeTrace.ct_sobolev_of_reg (d := d) hd hbeta
  refine ⟨Cs * Cb ^ 2 * (d : ℝ) ^ beta + 1, by positivity, ?_⟩
  intro z r hr hr1 G hG
  subst hr1
  obtain ⟨hHnn, -⟩ := SubdiffusiveProcess.CubeTrace.holder_pointwise hb0 hG
  set H : ℝ := holderSeminorm beta
    (frontier (centeredCube z 1 hr : Set (SpatialCoordinates d))) G with hH
  set K : ℝ := H * (d : ℝ) ^ (beta / 2) with hK
  have hK0 : 0 ≤ K := by positivity
  have hsup := SubdiffusiveProcess.CubeTrace.holder_sup_norm hb0 hG
  obtain ⟨Gh, hGh_eq, hGh⟩ := exists_holder_extension
    (frontier (centeredCube z 1 hr : Set (SpatialCoordinates d))) G K beta hK0 hb0 hb1 hsup
  have hGh' : ∀ x y, |Gh x - Gh y| ≤ K * ‖x - y‖ ^ beta := fun x y => by
    simpa [dist_eq_norm] using hGh x y
  have hGhc : Continuous Gh := SubdiffusiveProcess.CubeTrace.holder_continuous hb0 hGh'
  obtain ⟨hclose, hgrad, hhess⟩ := hCb z Gh K hK0 hGh'
  obtain ⟨B0, hB0⟩ := SubdiffusiveProcess.CubeTrace.holder_bounded_on_ctQ hK0 hb0 hGh' z
  have hreg : SubdiffusiveProcess.CubeTrace.CTReg z beta (Cb * K)
      (SubdiffusiveProcess.CubeTrace.ctB z Gh) :=
    ⟨SubdiffusiveProcess.CubeTrace.ctB_contDiffOn z hGhc, hgrad, hhess, B0 + Cb * K, by
      intro x hx
      have h1 := hclose x hx
      have h2 : SubdiffusiveProcess.CubeTrace.ctM z x ^ beta ≤ 1 :=
        Real.rpow_le_one (SubdiffusiveProcess.CubeTrace.ctM_pos hx).le
          (by linarith [SubdiffusiveProcess.CubeTrace.ctM_le_quarter z x]) hb0.le
      have h3 : Cb * K * SubdiffusiveProcess.CubeTrace.ctM z x ^ beta ≤ Cb * K := by
        have := mul_le_mul_of_nonneg_left h2 (mul_nonneg hCb0 hK0)
        linarith
      calc |SubdiffusiveProcess.CubeTrace.ctB z Gh x|
          = |Gh x + (SubdiffusiveProcess.CubeTrace.ctB z Gh x - Gh x)| := by ring_nf
        _ ≤ |Gh x| + |SubdiffusiveProcess.CubeTrace.ctB z Gh x - Gh x| := abs_add_le _ _
        _ ≤ B0 + Cb * K := add_le_add (hB0 x hx) (h1.trans h3)⟩
  obtain ⟨bg, hbg1, hbg2, hbg3⟩ := hCs z (Cb * K) (SubdiffusiveProcess.CubeTrace.ctB z Gh)
    (mul_nonneg hCb0 hK0) hreg
  refine ⟨bg, fun x => if x ∈ SubdiffusiveProcess.CubeTrace.ctQ z then
    SubdiffusiveProcess.CubeTrace.ctB z Gh x else Gh x, ?_, ?_, ?_, ?_, ?_⟩
  · exact SubdiffusiveProcess.CubeTrace.glue_continuous (mul_nonneg hCb0 hK0) hb0
      hreg.contDiffOn.continuousOn hGhc hclose
  · refine hbg1.trans ?_
    refine (ae_restrict_iff' Metric.isOpen_ball.measurableSet).2 (Eventually.of_forall fun x hx => ?_)
    exact (if_pos hx).symm
  · intro x hx
    have hxn := SubdiffusiveProcess.CubeTrace.frontier_ctQ_disjoint z x hx
    show (if x ∈ SubdiffusiveProcess.CubeTrace.ctQ z then _ else _) = _
    rw [if_neg hxn]
    exact hGh_eq hx
  · intro i
    exact hbg2 i
  · have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hK2 : K ^ 2 = H ^ 2 * (d : ℝ) ^ beta := by
      rw [hK, mul_pow, ← Real.rpow_natCast ((d : ℝ) ^ (beta / 2)) 2,
        ← Real.rpow_mul hdpos.le]
      congr 2
      push_cast
      ring
    refine hbg3.trans ?_
    rw [Real.one_rpow, one_mul]
    calc Cs * (Cb * K) ^ 2 = Cs * Cb ^ 2 * (d : ℝ) ^ beta * H ^ 2 := by
          rw [mul_pow, hK2]; ring
      _ ≤ (Cs * Cb ^ 2 * (d : ℝ) ^ beta + 1) * H ^ 2 := by
          nlinarith [sq_nonneg H]

end Paper
