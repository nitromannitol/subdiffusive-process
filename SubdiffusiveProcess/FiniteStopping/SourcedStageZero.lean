module

public import SubdiffusiveProcess.FiniteStopping.SourcedStageZeroAlg

@[expose] public section

/-! Sourced per-cell comparison for the infrared-free coefficient, and its stage-level form (see
`SourcedStageZeroAlg` for the docstring of the weight transfer). -/

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.FiniteStopping

variable {d : ℕ}

theorem aux_zero_div_bound (Y Y0 wz e : ℝ) (hwz : 0 < wz) (he : 0 < e)
    (h : e⁻¹ * (wz * Y) ≤ Y0) : Y ≤ (e / wz) * Y0 := by
  have h1 : wz * Y ≤ e * Y0 := by
    have := mul_le_mul_of_nonneg_left h he.le
    rwa [← mul_assoc, mul_inv_cancel₀ he.ne', one_mul] at this
  rw [div_mul_eq_mul_div, le_div_iff₀ hwz]
  linarith

/-- The sourced comparison at one padded child `q` (centre `zQ`, side `3^{-H1 n}`) of a parent `p`
(centre `zP`, side `3^{H1}` times that): the paper's local estimate with the extra source term. `u` is ANY
weak solution of the sourced equation on the root (Dirichlet or Neumann), given through the Dirichlet-type
test identity `hsol`. -/
theorem comparison_of_reg_trace_src_zero
    [NeZero d]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (alpha eta Cfin pad : ℝ) (heta : 0 < eta) (hCfin : 0 < Cfin) (hpad : 1 < pad)
    (H1 n target source : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (u : weakSobolevGraph (centeredCube z r hr))
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hFm : Measurable F) (hKf : 0 ≤ Kf)
    (hFb : ∀ x ∈ centeredCube z r hr, |F x| ≤ Kf)
    (hsol : ∀ psi : killedSobolevGraph (centeredCube z r hr),
      sobolevCoefficientForm (cutoffPositiveCoefficient model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega source z hr)
          (u : SobolevData (centeredCube z r hr)) (psi : SobolevData (centeredCube z r hr)) =
        ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          F x * (psi : SobolevData (centeredCube z r hr)).1 x)
    (zQ zP : SpatialCoordinates d) (rQ rP : ℝ) (hrQ : 0 < rQ) (hrP : 0 < rP)
    (hdepth : rQ = (3 : ℝ) ^ (-((H1 * n : ℕ) : ℤ)))
    (hsize : rP = (3 : ℝ) ^ H1 * rQ)
    (hQroot : centeredCube zQ rQ hrQ ≤ centeredCube z r hr)
    (hProot : centeredCube zP rP hrP ≤ centeredCube z r hr)
    (hQP : centeredCube zQ rQ hrQ ≤ centeredCube zP rP hrP)
    (idx : OddGridIndex d (subdivisionHalfWidth H1))
    (hcenter : zQ = oddGridCenter zP rP (subdivisionHalfWidth H1) idx)
    (hcontained : (closedCube zQ (pad * rQ) (mul_pos (lt_trans zero_lt_one hpad) hrQ) :
        Set (SpatialCoordinates d)) ⊆ centeredCube zP rP hrP)
    (hReg : SubdiffusiveProcess.FiniteStopping.Reg model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) alpha H1 pad Cfin hpad
      source (H1 * n) zQ omega)
    (hTrace : SubdiffusiveProcess.FiniteStopping.trace_close model H alpha eta
      target source (H1 * n) zQ omega)
    (hPQ : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube zQ rQ hrQ),
      ‖(v : SobolevData (centeredCube zQ rQ hrQ)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube zQ rQ hrQ)) v‖)
    (c : ℝ) (hc : 0 ≤ c)
    (hosc : ∀ x ∈ centeredCube zQ rQ hrQ, |H omega x - H omega zQ| ≤ c) :
    let aT := cutoffPositiveCoefficient model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega target z hr
    let aS := cutoffPositiveCoefficient model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega source z hr
    SubdiffusiveProcess.FiniteStopping.respOn aT u hQroot hPQ ≤
      Real.exp c ^ 2 * SubdiffusiveProcess.FiniteStopping.kappaRatio model H1 target source n *
        SubdiffusiveProcess.FiniteStopping.respOn aS u hQroot hPQ +
      2 * Cfin ^ 2 * eta * Real.exp c *
        SubdiffusiveProcess.FiniteStopping.kappaRatio model H1 target source n *
        (SubdiffusiveProcess.FiniteStopping.energyOn aS u.val (centeredCube zP rP hrP) +
          rQ ^ ((d : ℝ) + 2) *
            (SubdiffusiveProcess.FiniteStopping.reference model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega source (H1 * n) zQ)⁻¹ *
              Kf ^ 2) := by
  subst rP
  subst rQ
  let uP : weakSobolevGraph _ :=
    ⟨sobolevDataRestrict hProot u.val, sobolevDataRestrict_mem_weak hProot u.property⟩
  let uQ : weakSobolevGraph _ :=
    ⟨sobolevDataRestrict hQroot u.val, sobolevDataRestrict_mem_weak hQroot u.property⟩
  have hweakP : ∀ psi : killedSobolevGraph (centeredCube zP ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-((H1 * n : ℕ) : ℤ))) hrP),
      sobolevCoefficientForm (cutoffPositiveCoefficient model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega source zP hrP)
          (uP : SobolevData (centeredCube zP ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-((H1 * n : ℕ) : ℤ))) hrP))
          (psi : SobolevData (centeredCube zP ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-((H1 * n : ℕ) : ℤ))) hrP)) =
        ∫ x in (centeredCube zP ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-((H1 * n : ℕ) : ℤ))) hrP :
            Set (SpatialCoordinates d)),
          F x * (psi : SobolevData (centeredCube zP ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-((H1 * n : ℕ) : ℤ))) hrP)).1 x := by
    have hab : ((cutoffPositiveCoefficient model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega source z hr).val :
        SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube zP ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-((H1 * n : ℕ) : ℤ))) hrP :
          Set (SpatialCoordinates d))]
        (cutoffPositiveCoefficient model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega source zP hrP).val := by
      have h1 := positiveCoefficientRestrict_coeFn hProot
        (cutoffPositiveCoefficient model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega source z hr)
      rw [SubdiffusiveProcess.FiniteStopping.positiveCoefficientRestrict_cutoff model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega
        source z hr zP hrP hProot] at h1
      exact h1.symm
    exact SubdiffusiveProcess.weakEquation_restrict hProot _ _ hab
      (u : SobolevData (centeredCube z r hr)) F hsol
  obtain ⟨U, cc, hcont, hae, hholder, hnorm⟩ := hReg zP idx hcenter hcontained
    F Kf hFm hKf (fun x hx => hFb x (hProot hx)) uP hweakP
  have hclass := SubdiffusiveProcess.FiniteStopping.reg_to_boundary_class zQ _ hrQ alpha
    U cc hcont hholder
  have hnorm' := SubdiffusiveProcess.FiniteStopping.cellBoundaryQuotientNorm_le zQ _ hrQ
    alpha U cc _ hcont hholder hnorm
  have haeQ : (fun x => uQ.val.1 x) =ᵐ[
      volume.restrict (centeredCube zQ _ hrQ : Set (SpatialCoordinates d))] U :=
    SubdiffusiveProcess.FiniteStopping.domainLpRestrict_ae_trans hQP hProot u.val.1 U hae
  have ht := hTrace hPQ uQ U hcont hclass haeQ
  have hsS := SubdiffusiveProcess.FiniteStopping.reference_pos model H omega source (H1 * n) zQ
  have hsT := SubdiffusiveProcess.FiniteStopping.reference_pos model H omega target (H1 * n) zQ
  set wz : ℝ := Real.exp (-(H omega zQ)) with hwz
  have hwzpos : 0 < wz := Real.exp_pos _
  have hs0 : SubdiffusiveProcess.FiniteStopping.reference model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega source (H1 * n) zQ =
      SubdiffusiveProcess.FiniteStopping.reference model H omega source (H1 * n) zQ * wz :=
    SubdiffusiveProcess.FiniteStopping.reference_zero_eq model H omega source (H1 * n) zQ
  have hnorm2 : cellBoundaryQuotientNorm alpha zQ ((3 : ℝ) ^ (-((H1 * n : ℕ) : ℤ))) U ≤
      Cfin * ((3 : ℝ) ^ (-((H1 * n : ℕ) : ℤ))) ^ (((2 : ℝ) - (d : ℝ)) / 2) *
        (SubdiffusiveProcess.FiniteStopping.reference model H omega source (H1 * n) zQ * wz) ^
          (-(1 : ℝ) / 2) *
        Real.sqrt (sobolevCoefficientForm
          (cutoffPositiveCoefficient model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega source zP hrP) uP.val uP.val) +
      Cfin * ((3 : ℝ) ^ (-((H1 * n : ℕ) : ℤ))) ^ (2 : ℝ) *
        (SubdiffusiveProcess.FiniteStopping.reference model H omega source (H1 * n) zQ * wz)⁻¹ * Kf := by
    rw [← hs0]
    exact hnorm'
  -- weight comparisons on the cell
  have hbT := SubdiffusiveProcess.FiniteStopping.respOn_zero_bounds model H omega target zQ hrQ c hosc
    (killedResponseSpace hPQ) uQ
  have hbS := SubdiffusiveProcess.FiniteStopping.respOn_zero_bounds model H omega source zQ hrQ c hosc
    (killedResponseSpace hPQ) uQ
  have hX0 : dirichletResponse (killedResponseSpace hPQ)
      (cutoffPositiveCoefficient model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega target zQ hrQ) uQ ≤
      Real.exp c * (wz * dirichletResponse (killedResponseSpace hPQ)
        (cutoffPositiveCoefficient model H omega target zQ hrQ) uQ) := hbT.2
  have hY : dirichletResponse (killedResponseSpace hPQ)
      (cutoffPositiveCoefficient model H omega source zQ hrQ) uQ ≤
      (Real.exp c / wz) * dirichletResponse (killedResponseSpace hPQ)
        (cutoffPositiveCoefficient model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega source zQ hrQ) uQ := by
    have h := hbS.1
    rw [Real.exp_neg] at h
    exact aux_zero_div_bound _ _ wz _ hwzpos (Real.exp_pos c) h
  have hY0 : 0 ≤ dirichletResponse (killedResponseSpace hPQ)
      (cutoffPositiveCoefficient model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega source zQ hrQ) uQ :=
    dirichletResponse_nonneg _ _ _
  have hresult := SubdiffusiveProcess.FiniteStopping.conjunct2_core_src_zero _ _ _ wz (Real.exp c) Cfin eta
    (cellBoundaryQuotientNorm alpha zQ _ U) _ Kf _ _ _ _ (d : ℝ) hrQ hsT hsS hwzpos
    (Real.one_le_exp hc) hCfin heta (SubdiffusiveProcess.FiniteStopping.boundary_norm_nonneg _ _ _ _)
    (sobolevCoefficientForm_nonneg _ uP.val) hKf hnorm2 ht hX0 hY hY0
  have henergy : sobolevCoefficientForm
      (cutoffPositiveCoefficient model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega source zP hrP) uP.val uP.val =
      SubdiffusiveProcess.FiniteStopping.energyOn
        (cutoffPositiveCoefficient model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega source z hr) u.val (centeredCube zP _ hrP) := by
    rw [SubdiffusiveProcess.FiniteStopping.sobolevCoefficientForm_eq_energyOn,
      ← SubdiffusiveProcess.FiniteStopping.positiveCoefficientRestrict_cutoff
        model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega source z hr zP hrP hProot]
    exact SubdiffusiveProcess.FiniteStopping.energyOn_restrict_eq hProot
      (cutoffPositiveCoefficient model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega source z hr) u.val
  have hratio : SubdiffusiveProcess.FiniteStopping.reference model H omega target (H1 * n) zQ /
      SubdiffusiveProcess.FiniteStopping.reference model H omega source (H1 * n) zQ =
      SubdiffusiveProcess.FiniteStopping.kappaRatio model H1 target source n :=
    (SubdiffusiveProcess.FiniteStopping.kappaRatio_eq_sRatio model H H1 target source n
      zQ omega).symm
  rw [henergy, hratio, ← hs0] at hresult
  dsimp only
  unfold SubdiffusiveProcess.FiniteStopping.respOn
  rw [SubdiffusiveProcess.FiniteStopping.positiveCoefficientRestrict_cutoff
      model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega target z hr zQ hrQ hQroot,
    SubdiffusiveProcess.FiniteStopping.positiveCoefficientRestrict_cutoff
      model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega source z hr zQ hrQ hQroot]
  exact hresult


theorem energyOn_restrict_nonneg {U Ω : Opens (SpatialCoordinates d)} (hU : U ≤ Ω)
    (a : PositiveCoefficient Ω) (u : SobolevData Ω) :
    0 ≤ SubdiffusiveProcess.FiniteStopping.energyOn a u (U : Set (SpatialCoordinates d)) := by
  rw [← SubdiffusiveProcess.FiniteStopping.energyOn_restrict_eq hU a u,
    ← SubdiffusiveProcess.FiniteStopping.sobolevCoefficientForm_eq_energyOn]
  exact sobolevCoefficientForm_nonneg _ _

theorem kappaRatio_nonneg' (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (H1 target source n : ℕ) :
    0 ≤ kappaRatio model H1 target source n := by
  unfold kappaRatio kappaSeq
  have hk : ∀ J : ℕ, 0 < Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
      SubdiffusiveProcess.CoarseGrainingVocab.ahom model J := fun J =>
    mul_pos (Real.exp_pos _) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model J)
  exact (div_pos (div_pos (hk _) (hk _)) (div_pos (hk _) (hk _))).le

theorem zero_finish (RT RS κ E Src Cg e wt : ℝ) (hκ : 0 ≤ κ) (hRS : 0 ≤ RS) (hE : 0 ≤ E)
    (hSrc : 0 ≤ Src) (hCg : 0 ≤ Cg) (he : 1 ≤ e) (hwt : e ^ 2 ≤ wt)
    (h : RT ≤ e ^ 2 * κ * RS + Cg * e * κ * (E + Src)) :
    RT ≤ wt * κ * RS + Cg * (wt * κ) * (E + Src) := by
  have hX : 0 ≤ E + Src := add_nonneg hE hSrc
  have hew : e ≤ wt := le_trans (by nlinarith) hwt
  have h1 : e ^ 2 * κ * RS ≤ wt * κ * RS :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hwt hκ) hRS
  have h2 : Cg * e * κ * (E + Src) ≤ Cg * (wt * κ) * (E + Src) := by
    have : Cg * e * κ = Cg * (e * κ) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hew hκ) hCg) hX
  linarith only [h, h1, h2]

/-- Sourced comparison at the stage-`(s+1)` cell of the two-stage tree of the root `Q(z, 3^j)`, for any weak
solution `u` of the sourced equation (test identity `hsol` against the killed space of the root). -/
theorem comparison_at_stage_src_zero
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
      sobolevCoefficientForm (cutoffPositiveCoefficient model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega source z hr)
          (u : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr))
          (psi : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr)) =
        ∫ x in (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)),
          F x * (psi : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr)).1 x)
    (w0 : Fin (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) → OddGridIndex d 1)
    (s : ℕ) (w : Fin (s + 1) → OddGridIndex d (subdivisionHalfWidth H1))
    (hPad : SubdiffusiveProcess.FiniteStopping.padLabel 2 (w (Fin.last s)))
    (LH : ℝ) (hLH : 0 ≤ LH)
    (hLip : ∀ x ∈ closedCube z ((3 : ℝ) ^ j) hr, ∀ y ∈ closedCube z ((3 : ℝ) ^ j) hr,
      |H omega x - H omega y| ≤ LH * dist x y)
    (wt : ℝ)
    (hwt : Real.exp (LH * descendantSide (subdivisionHalfWidth H1) (s + 1)
      (descendantSide 1 (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) ((3 : ℝ) ^ j))) ≤ wt)
    (hReg : SubdiffusiveProcess.FiniteStopping.Reg model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) alpha H1 pad Cfin hpad source
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
    let aT := cutoffPositiveCoefficient model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega target z hr
    let aS := cutoffPositiveCoefficient model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega source z hr
    SubdiffusiveProcess.FiniteStopping.respOn aT u
        (SubdiffusiveProcess.FiniteStopping.cell2_le_root z hr t0 mg w0 (s + 1) w)
        (SubdiffusiveProcess.FiniteStopping.cell2_killedPoincare z hr t0 mg w0 (s + 1) w) ≤
      wt * SubdiffusiveProcess.FiniteStopping.kappaRatio model H1 target source
          (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + (s + 1)) *
        SubdiffusiveProcess.FiniteStopping.respOn aS u
          (SubdiffusiveProcess.FiniteStopping.cell2_le_root z hr t0 mg w0 (s + 1) w)
          (SubdiffusiveProcess.FiniteStopping.cell2_killedPoincare z hr t0 mg w0 (s + 1) w) +
      2 * Cfin ^ 2 * eta * (wt * SubdiffusiveProcess.FiniteStopping.kappaRatio model H1 target source
          (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + (s + 1))) *
        (SubdiffusiveProcess.FiniteStopping.energyOn aS u.val
            (SubdiffusiveProcess.FiniteStopping.cell2 z hr t0 mg w0 s (fun i => w i.castSucc)) +
          (descendantSide mg (s + 1) (descendantSide 1 t0 ((3 : ℝ) ^ j))) ^ ((d : ℝ) + 2) *
            (SubdiffusiveProcess.FiniteStopping.reference model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega source
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
  have hLRQ : 0 ≤ LH * rQ / 2 := by positivity
  have hosc : ∀ x ∈ centeredCube zQ rQ hrQ, |H omega x - H omega zQ| ≤ LH * rQ / 2 := by
    intro x hx
    have hxr : x ∈ closedCube z ((3 : ℝ) ^ j) hr := by
      have h1 : x ∈ (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) := hQroot hx
      exact centeredCube_subset_closedCube z hr h1
    have hzr : zQ ∈ closedCube z ((3 : ℝ) ^ j) hr := by
      have h1 : zQ ∈ (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) :=
        hQroot (Metric.mem_ball_self (by positivity))
      exact centeredCube_subset_closedCube z hr h1
    have hd : dist x zQ ≤ rQ / 2 := by
      have : dist x zQ < rQ / 2 := hx
      exact this.le
    calc |H omega x - H omega zQ| ≤ LH * dist x zQ := hLip x hxr zQ hzr
      _ ≤ LH * (rQ / 2) := mul_le_mul_of_nonneg_left hd hLH
      _ = LH * rQ / 2 := by ring
  have hCmp := SubdiffusiveProcess.FiniteStopping.comparison_of_reg_trace_src_zero model H omega
    alpha eta Cfin pad heta hCfin hpad H1
    (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + (s + 1)) target source z hr u F Kf hFm hKf
    hFb hsol zQ zP rQ rP hrQ hrP hdepth hsize hQroot hProot hQP
    (w (Fin.last s)) hcenter hcontained hReg hTrace hPQ (LH * rQ / 2) hLRQ hosc
  have hrespT := SubdiffusiveProcess.FiniteStopping.respOn_eq_of_domain_eq
    (cutoffPositiveCoefficient model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega target z hr) u
    hCubeQ.symm hQroot hQrootCell hPQ hPQCell
  have hrespS := SubdiffusiveProcess.FiniteStopping.respOn_eq_of_domain_eq
    (cutoffPositiveCoefficient model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega source z hr) u
    hCubeQ.symm hQroot hQrootCell hPQ hPQCell
  have henergy := SubdiffusiveProcess.FiniteStopping.energyOn_eq_of_domain_eq
    (cutoffPositiveCoefficient model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega source z hr) u.val hCubeP.symm
  dsimp only at hCmp ⊢
  rw [hrespT, hrespS, henergy] at hCmp
  have hE0 : 0 ≤ SubdiffusiveProcess.FiniteStopping.energyOn
      (cutoffPositiveCoefficient model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega source z hr) u.val
      (centeredCube zP rP hrP : Set (SpatialCoordinates d)) :=
    SubdiffusiveProcess.FiniteStopping.energyOn_restrict_nonneg hProot _ _
  have hSrc0 : 0 ≤ rQ ^ ((d : ℝ) + 2) *
      (SubdiffusiveProcess.FiniteStopping.reference model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega source
        (H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + (s + 1))) zQ)⁻¹ * Kf ^ 2 := by
    have hpos : 0 < SubdiffusiveProcess.FiniteStopping.reference model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega source
        (H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + (s + 1))) zQ :=
      SubdiffusiveProcess.FiniteStopping.reference_pos _ _ _ _ _ _
    positivity
  have hRS0 := dirichletResponse_nonneg (killedResponseSpace hPQ)
    (positiveCoefficientRestrict hQroot (cutoffPositiveCoefficient model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega source z hr))
    ⟨sobolevDataRestrict hQroot u.val, sobolevDataRestrict_mem_weak hQroot u.property⟩
  have hκ := SubdiffusiveProcess.FiniteStopping.kappaRatio_nonneg' model H1 target source
    (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + (s + 1))
  have hexp2 : Real.exp (LH * rQ / 2) ^ 2 ≤ wt := by
    rw [← Real.exp_nat_mul]
    calc Real.exp (((2 : ℕ) : ℝ) * (LH * rQ / 2)) = Real.exp (LH * rQ) := by
          congr 1; push_cast; ring
      _ ≤ wt := hwt
  exact SubdiffusiveProcess.FiniteStopping.zero_finish _ _ _ _ _ _ _ _ hκ hRS0 hE0 hSrc0
    (by positivity) (Real.one_le_exp hLRQ) hexp2 hCmp



end SubdiffusiveProcess.FiniteStopping
