module

public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.Paper.inputs_classical_e4_rellich

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem inputs_Interp_compact (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (threeQuarters : Set.Ioo (0 : ℝ) 1) (hs : (threeQuarters : ℝ) = 3 / 4)
    (w : ℕ → CubeFractionalL2 (k := 1) hd z r hr threeQuarters) (M : ℝ)
    (hbound : ∀ n, cubeFractionalL2Norm hd z r hr threeQuarters (w n) ≤ M) :
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      ∃ wlim : DomainL2 (centeredCube z r hr),
        Tendsto (fun n => ‖(w (sigma n)).val 0 - wlim‖) atTop (nhds 0) := by
  let v : ℕ → DomainL2 (centeredCube z r hr) := fun n => (w n).val 0
  let vol : ℝ := volume.real (centeredCube z r hr : Set (SpatialCoordinates d))
  let c : ℝ := r ^ (-(threeQuarters : ℝ))
  let a : ℕ → ℝ := fun n =>
    (cubeFractionalL2Seminorm hd z r hr threeQuarters (w n).val).toReal
  let t : ℕ → ℝ := fun n =>
    Real.sqrt (∑ i : Fin 1, ‖(w n).val i‖ ^ 2) / Real.sqrt vol
  let q : ℕ → ℝ := fun n => ‖v n‖ ^ 2 / vol
  let B : ℝ := M ^ 2 + M ^ 2 / c ^ 2

  have hvol : 0 < vol := by
    dsimp [vol]
    exact centeredCube_volume_pos z hr
  have hc : 0 < c := by
    dsimp [c]
    rw [hs]
    exact Real.rpow_pos_of_pos hr _

  have hcoord (n : ℕ) : (fun _ : Fin 1 => v n) = (w n).val := by
    funext i
    change (w n).val 0 = (w n).val i
    exact congrArg (w n).val (Subsingleton.elim 0 i)

  have hfinite : ∀ n,
      cubeFractionalL2Seminorm hd z r hr threeQuarters (fun _ : Fin 1 => v n) < ⊤ := by
    intro n
    simpa only [hcoord n] using (w n).property

  have hnBound (n : ℕ) : a n + c * t n ≤ M := by
    simpa only [a, c, t, vol, cubeFractionalL2Norm] using hbound n

  have hsqFormula (n : ℕ) :
      cubeFractionalSqNorm hd z r hr threeQuarters (v n) = a n ^ 2 + q n := by
    simp [cubeFractionalSqNorm, cubeFractionalVecSqNorm,
      cubeFractionalVecSeminormSq, a, q, vol, v, hcoord n]

  have htSq (n : ℕ) : t n ^ 2 = q n := by
    dsimp [t, q, vol]
    have hsum :
        (∑ i : Fin 1, ‖(w n).val i‖ ^ 2) = ‖v n‖ ^ 2 := by
      simp [v]
    rw [hsum, div_pow, Real.sq_sqrt (sq_nonneg ‖v n‖),
      Real.sq_sqrt hvol.le]

  have hsqBound : ∀ n, cubeFractionalSqNorm hd z r hr threeQuarters (v n) ≤ B := by
    intro n
    have ha : 0 ≤ a n := by
      dsimp [a]
      exact ENNReal.toReal_nonneg
    have ht : 0 ≤ t n := by
      dsimp [t]
      exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hb : 0 ≤ c * t n := mul_nonneg hc.le ht
    have hM : 0 ≤ M := le_trans (add_nonneg ha hb) (hnBound n)
    have haM : a n ≤ M := by linarith [hnBound n, hb]
    have hbM : c * t n ≤ M := by linarith [hnBound n, ha]
    have haSq : a n ^ 2 ≤ M ^ 2 := by nlinarith
    have hbSq : (c * t n) ^ 2 ≤ M ^ 2 := by nlinarith
    have hcSq : 0 < c ^ 2 := sq_pos_of_pos hc
    have hrel : q n * c ^ 2 = (c * t n) ^ 2 := by
      rw [mul_pow, htSq n]
      ring
    have hqScaled : q n ≤ (c * t n) ^ 2 / c ^ 2 :=
      (le_div_iff₀ hcSq).2 hrel.le
    have hqM : q n ≤ M ^ 2 / c ^ 2 :=
      le_trans hqScaled (div_le_div_of_nonneg_right hbSq hcSq.le)
    rw [hsqFormula n]
    dsimp [B]
    exact add_le_add haSq hqM

  obtain ⟨sigma, wlim, hmono, hconv⟩ :=
    inputs_classical_e4_rellich d hd threeQuarters z r hr v B hfinite hsqBound
  refine ⟨sigma, hmono, wlim, ?_⟩
  exact (tendsto_iff_norm_sub_tendsto_zero).1 hconv

end SubdiffusiveProcess.Paper
