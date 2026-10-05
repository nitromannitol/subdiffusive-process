module

public import SubdiffusiveProcess.FiniteStopping.SourcedStageComparison

@[expose] public section

/-! The sourced comparison at a stage of the observation tree (source-carrying analogue of
`comparison_at_stage`). -/

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.FiniteStopping

variable {d : ℕ}

/-- Sourced comparison at the stage-`(s+1)` cell of the two-stage tree of the root `Q(z, 3^j)`, for any weak
solution `u` of the sourced equation (test identity `hsol` against the killed space of the root). -/
theorem comparison_at_stage_src
    [NeZero d]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (alpha eta Cfin pad : ℝ) (heta : 0 < eta) (hCfin : 0 < Cfin) (hpad : 1 < pad)
    (hpad3 : pad ≤ 3) (H1 N target source : ℕ) (hH1 : 0 < H1)
    (z : SpatialCoordinates d) (j : ℤ) (hr : (0 : ℝ) < (3 : ℝ) ^ j)
    (hj0 : 0 ≤ ((H1 * SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℕ) : ℤ) + j)
    (u : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ j) hr))
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hFm : Measurable F) (hKf : 0 ≤ Kf)
    (hFb : ∀ x ∈ centeredCube z ((3 : ℝ) ^ j) hr, |F x| ≤ Kf)
    (hsol : ∀ psi : killedSobolevGraph (centeredCube z ((3 : ℝ) ^ j) hr),
      sobolevCoefficientForm (cutoffPositiveCoefficient model H omega source z hr)
          (u : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr))
          (psi : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr)) =
        ∫ x in (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)),
          F x * (psi : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr)).1 x)
    (w0 : Fin (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) → OddGridIndex d 1)
    (s : ℕ) (w : Fin (s + 1) → OddGridIndex d (subdivisionHalfWidth H1))
    (hPad : SubdiffusiveProcess.FiniteStopping.padLabel 2 (w (Fin.last s)))
    (hReg : SubdiffusiveProcess.FiniteStopping.Reg model H alpha H1 pad Cfin hpad source
      (H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + (s + 1)))
      (descendantCenter (subdivisionHalfWidth H1)
        (descendantCenter 1 z ((3 : ℝ) ^ j) (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) w0)
        (descendantSide 1 (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) ((3 : ℝ) ^ j))
        (s + 1) w) omega)
    (hTrace : SubdiffusiveProcess.FiniteStopping.trace_close model H alpha eta target source
      (H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + (s + 1)))
      (descendantCenter (subdivisionHalfWidth H1)
        (descendantCenter 1 z ((3 : ℝ) ^ j) (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) w0)
        (descendantSide 1 (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) ((3 : ℝ) ^ j))
        (s + 1) w) omega) :
    let t0 := SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j
    let mg := subdivisionHalfWidth H1
    let aT := cutoffPositiveCoefficient model H omega target z hr
    let aS := cutoffPositiveCoefficient model H omega source z hr
    SubdiffusiveProcess.FiniteStopping.respOn aT u
        (SubdiffusiveProcess.FiniteStopping.cell2_le_root z hr t0 mg w0 (s + 1) w)
        (SubdiffusiveProcess.FiniteStopping.cell2_killedPoincare z hr t0 mg w0 (s + 1) w) ≤
      SubdiffusiveProcess.FiniteStopping.kappaRatio model H1 target source
          (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + (s + 1)) *
        SubdiffusiveProcess.FiniteStopping.respOn aS u
          (SubdiffusiveProcess.FiniteStopping.cell2_le_root z hr t0 mg w0 (s + 1) w)
          (SubdiffusiveProcess.FiniteStopping.cell2_killedPoincare z hr t0 mg w0 (s + 1) w) +
      2 * Cfin ^ 2 * eta * SubdiffusiveProcess.FiniteStopping.kappaRatio model H1 target source
          (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + (s + 1)) *
        (SubdiffusiveProcess.FiniteStopping.energyOn aS u.val
            (SubdiffusiveProcess.FiniteStopping.cell2 z hr t0 mg w0 s (fun i => w i.castSucc)) +
          (descendantSide mg (s + 1) (descendantSide 1 t0 ((3 : ℝ) ^ j))) ^ ((d : ℝ) + 2) *
            (SubdiffusiveProcess.FiniteStopping.reference model H omega source
              (H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + (s + 1)))
              (descendantCenter mg
                (descendantCenter 1 z ((3 : ℝ) ^ j) t0 w0)
                (descendantSide 1 t0 ((3 : ℝ) ^ j)) (s + 1) w))⁻¹ * Kf ^ 2) := by
  let t0 := SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j
  let mg := subdivisionHalfWidth H1
  let R := descendantSide 1 t0 ((3 : ℝ) ^ j)
  let z0 := descendantCenter 1 z ((3 : ℝ) ^ j) t0 w0
  let zQ := descendantCenter mg z0 R (s + 1) w
  let zP := descendantCenter mg z0 R s (fun i => w i.castSucc)
  let rQ := descendantSide mg (s + 1) R
  let rP := descendantSide mg s R
  have hrQ : 0 < rQ := descendantSide_pos mg (s + 1) (descendantSide_pos 1 t0 hr)
  have hrP : 0 < rP := descendantSide_pos mg s (descendantSide_pos 1 t0 hr)
  have hdepth : rQ = (3 : ℝ) ^
      (-((H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + (s + 1)) : ℕ) : ℤ)) :=
    SubdiffusiveProcess.FiniteStopping.cell2_radius_eq H1 N hH1 j hj0 (s + 1)
  have hsize : rP = (3 : ℝ) ^ H1 * rQ :=
    SubdiffusiveProcess.FiniteStopping.cell2_parent_side_eq H1 R s
  have hcenter : zQ = oddGridCenter zP rP mg (w (Fin.last s)) :=
    SubdiffusiveProcess.FiniteStopping.cell2_succ_eq_oddGridCenter z hr t0 mg w0 s w
  have hcontained : (closedCube zQ (pad * rQ)
      (mul_pos (lt_trans zero_lt_one hpad) hrQ) : Set (SpatialCoordinates d)) ⊆
      centeredCube zP rP hrP := by
    have hc := (SubdiffusiveProcess.FiniteStopping.Reg_premises_at_stage H1 N hH1 z j hj0
      w0 s w pad hpad hpad3 hPad).2
    simpa only [hsize, hdepth] using hc
  have hQroot : centeredCube zQ rQ hrQ ≤ centeredCube z ((3 : ℝ) ^ j) hr := by
    change centeredCube
      (descendantCenter mg (descendantCenter 1 z ((3 : ℝ) ^ j) t0 w0)
        (descendantSide 1 t0 ((3 : ℝ) ^ j)) (s + 1) w)
      (descendantSide mg (s + 1) (descendantSide 1 t0 ((3 : ℝ) ^ j)))
      (descendantSide_pos mg (s + 1)
        (descendantSide_pos 1 t0 (zpow_pos (by norm_num) j))) ≤
        centeredCube z ((3 : ℝ) ^ j) hr
    rw [← SubdiffusiveProcess.FiniteStopping.cell2_eq_centeredCube z hr t0 mg w0
      (s + 1) w]
    exact SubdiffusiveProcess.FiniteStopping.cell2_le_root z hr t0 mg w0 (s + 1) w
  have hProot : centeredCube zP rP hrP ≤ centeredCube z ((3 : ℝ) ^ j) hr := by
    change centeredCube
      (descendantCenter mg (descendantCenter 1 z ((3 : ℝ) ^ j) t0 w0)
        (descendantSide 1 t0 ((3 : ℝ) ^ j)) s (fun i => w i.castSucc))
      (descendantSide mg s (descendantSide 1 t0 ((3 : ℝ) ^ j)))
      (descendantSide_pos mg s
        (descendantSide_pos 1 t0 (zpow_pos (by norm_num) j))) ≤
        centeredCube z ((3 : ℝ) ^ j) hr
    rw [← SubdiffusiveProcess.FiniteStopping.cell2_eq_centeredCube z hr t0 mg w0
      s (fun i => w i.castSucc)]
    exact SubdiffusiveProcess.FiniteStopping.cell2_le_root z hr t0 mg w0 s
      (fun i => w i.castSucc)
  have hQP : centeredCube zQ rQ hrQ ≤ centeredCube zP rP hrP := by
    change centeredCube
      (descendantCenter mg (descendantCenter 1 z ((3 : ℝ) ^ j) t0 w0)
        (descendantSide 1 t0 ((3 : ℝ) ^ j)) (s + 1) w)
      (descendantSide mg (s + 1) (descendantSide 1 t0 ((3 : ℝ) ^ j)))
      (descendantSide_pos mg (s + 1)
        (descendantSide_pos 1 t0 (zpow_pos (by norm_num) j))) ≤
      centeredCube
        (descendantCenter mg (descendantCenter 1 z ((3 : ℝ) ^ j) t0 w0)
          (descendantSide 1 t0 ((3 : ℝ) ^ j)) s (fun i => w i.castSucc))
        (descendantSide mg s (descendantSide 1 t0 ((3 : ℝ) ^ j)))
        (descendantSide_pos mg s
          (descendantSide_pos 1 t0 (zpow_pos (by norm_num) j)))
    rw [← SubdiffusiveProcess.FiniteStopping.cell2_eq_centeredCube z hr t0 mg w0
      (s + 1) w,
      ← SubdiffusiveProcess.FiniteStopping.cell2_eq_centeredCube z hr t0 mg w0
        s (fun i => w i.castSucc)]
    exact SubdiffusiveProcess.FiniteStopping.cell2_succ_le_parent z hr t0 mg w0 s w
  have hCubeQ : SubdiffusiveProcess.FiniteStopping.cell2 z hr t0 mg w0 (s + 1) w =
      centeredCube zQ rQ hrQ := by
    rw [SubdiffusiveProcess.FiniteStopping.cell2_eq_centeredCube]
  have hPQ : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube zQ rQ hrQ),
      ‖(v : SobolevData (centeredCube zQ rQ hrQ)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube zQ rQ hrQ)) v‖ := by
    simpa only [hCubeQ] using!
      SubdiffusiveProcess.FiniteStopping.cell2_killedPoincare z hr t0 mg w0 (s + 1) w
  have hQrootCell :=
    SubdiffusiveProcess.FiniteStopping.cell2_le_root z hr t0 mg w0 (s + 1) w
  have hPQCell :=
    SubdiffusiveProcess.FiniteStopping.cell2_killedPoincare z hr t0 mg w0 (s + 1) w
  have hCubeP : SubdiffusiveProcess.FiniteStopping.cell2 z hr t0 mg w0 s
      (fun i => w i.castSucc) = centeredCube zP rP hrP := by
    rw [SubdiffusiveProcess.FiniteStopping.cell2_eq_centeredCube]
  have hCmp := SubdiffusiveProcess.FiniteStopping.comparison_of_reg_trace_src model H omega
    alpha eta Cfin pad heta hCfin hpad H1
    (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + (s + 1)) target source z hr u F Kf hFm hKf
    hFb hsol zQ zP rQ rP hrQ hrP hdepth hsize hQroot hProot hQP
    (w (Fin.last s)) hcenter hcontained hReg hTrace hPQ
  have hrespT := SubdiffusiveProcess.FiniteStopping.respOn_eq_of_domain_eq
    (cutoffPositiveCoefficient model H omega target z hr) u
    hCubeQ.symm hQroot hQrootCell hPQ hPQCell
  have hrespS := SubdiffusiveProcess.FiniteStopping.respOn_eq_of_domain_eq
    (cutoffPositiveCoefficient model H omega source z hr) u
    hCubeQ.symm hQroot hQrootCell hPQ hPQCell
  have henergy := SubdiffusiveProcess.FiniteStopping.energyOn_eq_of_domain_eq
    (cutoffPositiveCoefficient model H omega source z hr) u.val hCubeP.symm
  dsimp only at hCmp ⊢
  rw [hrespT, hrespS, henergy] at hCmp
  exact hCmp

end SubdiffusiveProcess.FiniteStopping
