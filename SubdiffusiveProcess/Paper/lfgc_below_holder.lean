module

public import SubdiffusiveProcess.Paper.lfgc_wavelength_coefficient
public import SubdiffusiveProcess.Analysis.SmallOscillationHolderEnergy
public import SubdiffusiveProcess.Lane4.CutoffCoefficientRepresentative

@[expose] public section




open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4 SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal BigOperators Topology
noncomputable section
namespace Paper

/-- A wavelength prefix and the small-oscillation inputs give the parent-energy Holder estimate. -/
theorem lfgc_below_holder {d : ℕ} [NeZero d]
    (W : SmallPerturbationInput d) (p alpha : ℝ) (hp : 2 ≤ p)
    (halpha : 0 < alpha) (halpha1 : alpha < 1) (halphap : alpha < 1 - (d : ℝ) / p)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (hIR : Tendsto (infraredPartialSum omega) atTop (nhds (H omega)) ∨ H = 0)
    (sigma eps : ℝ) (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal)
    (Zsc : ℕ → Vec d → ℝ) (goodEvt : ℕ → Vec d → Prop)
    (hPS : primitive_scores d M sigma eps eta Fsc Psc Rsc Dsc Zsc goodEvt)
    (r : ℝ) (hr : 0 < r) (hrN : r = (3 : ℝ) ^ (-(N : ℤ)))
    (z : SpatialCoordinates d) (lam : ℝ) (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hlamSmall : (d : ℝ) * lam ≤ W.osc p) (hdelta1 : M.delta ≤ 1)
    (hpad : ∀ w : Fin 1 → OddGridIndex d 1,
      Dsc 0 (((3 : ℝ) ^ N) • descendantCenter 1 z (3 * r) 1 w) ≠ ⊤ ∧
      (Dsc 0 (((3 : ℝ) ^ N) • descendantCenter 1 z (3 * r) 1 w)).toReal ≤ lam)
    (zP : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (hsub : Metric.closedBall z (3 * r / 2) ⊆
      (centeredCube zP R hR : Set (SpatialCoordinates d)))
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hF : Measurable F) (hKf : 0 ≤ Kf)
    (hbound : ∀ x ∈ (centeredCube zP R hR : Set (SpatialCoordinates d)), |F x| ≤ Kf)
    (u : weakSobolevGraph (centeredCube zP R hR))
    (heq : ∀ psi : killedSobolevGraph (centeredCube zP R hR),
      sobolevCoefficientForm (cutoffPositiveCoefficient M H omega N zP hR) u.val psi.val =
        ∫ x in (centeredCube zP R hR : Set (SpatialCoordinates d)), F x * psi.val.1 x) :
    let s := aux_in_deterministic_onestep_sref M H omega N N z
    let C := (((d : ℝ) + 1) ^ alpha + 1) * W.CMorrey p alpha * W.C p * Real.exp ((d : ℝ) + 2)
    ∃ (U : SpatialCoordinates d → ℝ) (c : ℝ),
      ContinuousOn U (closedCube z r hr : Set (SpatialCoordinates d)) ∧
      ((u.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube z r hr : Set (SpatialCoordinates d))] U) ∧
      IsHolderOn alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
        (fun x => U (z + r • x) - c) ∧
      cAlphaNorm alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
        (fun x => U (z + r • x) - c) ≤
          C * r ^ ((2 - (d : ℝ)) / 2) * s ^ (-(1 : ℝ) / 2) *
            Real.sqrt (sobolevCoefficientForm (cutoffPositiveCoefficient M H omega N zP hR) u.val u.val) +
          C * r ^ (2 : ℝ) * s⁻¹ * Kf := by
  let s := aux_in_deterministic_onestep_sref M H omega N N z
  let B := Real.exp ((d : ℝ) + 2)
  have hs : 0 < s := aux_in_deterministic_onestep_sref_pos M H omega N N z
  have hB : 0 < B := Real.exp_pos _
  have hB1 : 1 ≤ B := Real.one_le_exp_iff.mpr (by positivity)
  have hl : 0 < 4 * (r / 2) := by positivity
  let V := centeredCube z (4 * (r / 2)) hl
  let a := cutoffPositiveCoefficient M H omega N z hl
  have hVball : (V : Set (SpatialCoordinates d)) ⊆ Metric.closedBall z r := by
    intro x hx
    change dist x z < 4 * (r / 2) / 2 at hx
    change dist x z ≤ r
    linarith only [hx]
  have hVsub : V ≤ centeredCube zP R hR :=
    hVball.trans ((Metric.closedBall_subset_closedBall (by linarith only [hr])).trans hsub)
  have hfield := lfgc_wavelength_coefficient M H omega N eta hEta hIR sigma eps Fsc Psc Rsc Dsc
    Zsc goodEvt hPS r hr hrN z lam hlam hlam1 hdelta1 hpad
  have hbase := hfield z (Metric.mem_closedBall_self hr.le)
  have ha0 := cutoffCoefficient_pos M H omega N z
  have ha := (cutoffPositiveCoefficient_representative M H omega N z hl).2.2.2
  have haP := (cutoffPositiveCoefficient_representative M H omega N zP hR).2.2.2
  have hab : ((cutoffPositiveCoefficient M H omega N zP hR).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (V : Set (SpatialCoordinates d))] a.val := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hVsub haP, ha] with x hx hy
    exact hx.trans hy.symm
  have hosc : ∀ᵐ x ∂volume.restrict (V : Set (SpatialCoordinates d)),
      |Real.log (a.val x) - Real.log (cutoffCoefficient M H omega N z)| ≤ W.osc p := by
    filter_upwards [ha, ae_restrict_mem V.isOpen.measurableSet] with x hx hxV
    rw [hx]
    exact (hfield x (hVball hxV)).1.trans hlamSmall
  have hlow : ∀ᵐ x ∂volume.restrict (V : Set (SpatialCoordinates d)), s / B ≤ a.val x := by
    filter_upwards [ha, ae_restrict_mem V.isOpen.measurableSet] with x hx hxV
    rw [hx]
    apply (div_le_iff₀ hB).mpr
    simpa only [mul_comm] using (hfield x (hVball hxV)).2
  have hcompB : s ≤ B * (s / B) := by rw [mul_div_cancel₀ s hB.ne']
  obtain ⟨U, hU, htie, hHolder, hnorm⟩ := smallOscillation_holder_parent_energy W p alpha hp
    halpha halpha1 halphap z (r / 2) hl (centeredCube zP R hR) hVsub
    (cutoffPositiveCoefficient M H omega N zP hR) a hab
    (cutoffCoefficient M H omega N z) (s / B) s B ha0 (div_pos hs hB) hs hB1 hbase.2 hcompB
    hosc hlow F Kf hF hKf hbound u heq
  rw [show 2 * (r / 2) = r by ring] at hHolder hnorm
  exact ⟨U, U z, hU.continuousOn, htie, hHolder, hnorm⟩

end Paper
