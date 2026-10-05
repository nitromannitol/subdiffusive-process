module

public import SubdiffusiveProcess.Probability.WeightedChaosMass
public import SubdiffusiveProcess.Main.ConditionalFineFiltration
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped CompactlySupported ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess

theorem weightedChaosCutoff_centeredCube_adapted
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : Measurable H)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    Adapted (conditionalFineFiltration H hH)
      (fun N omega ↦ ((weightedChaosCutoff M H N omega)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal) := by
  intro N
  let Φ : BilateralField d → (j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ) :=
    fun omega j ↦ omega (-(Int.ofNat j))
  let Y : Type := C(SpatialCoordinates d, ℝ) × ((j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ))
  let Ψ : BilateralField d → Y := fun omega ↦ (H omega, Φ omega)
  let g : Y × SpatialCoordinates d → ℝ :=
    fun p ↦ Real.exp (p.1.1 p.2) * Real.exp ((∑ j : Fin (N + 1), p.1.2 j p.2) -
      (N + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)
  have hA : Measurable (fun p :
      (C(SpatialCoordinates d, ℝ) × ((j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ))) ×
        SpatialCoordinates d ↦ p.1.1 p.2) := by fun_prop
  have hB : Measurable (fun p :
      (C(SpatialCoordinates d, ℝ) × ((j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ))) ×
        SpatialCoordinates d ↦
      (∑ j : Fin (N + 1), p.1.2 j p.2) - (N + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) := by
    fun_prop
  have hg : StronglyMeasurable g := by
    have hgm : Measurable g := by
      unfold g
      exact (hA.exp).mul (hB.exp)
    exact hgm.stronglyMeasurable
  have hgmass : StronglyMeasurable
      (fun y : Y ↦ ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), g (y, x)) :=
    hg.integral_prod_right'
  have hΦmeas : Measurable[(conditionalFineFiltration H hH) N] Φ := by
    have heq : (MeasurableSpace.comap Φ
        (inferInstance : MeasurableSpace ((j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ)))) =
        ⨆ j : Fin (N + 1), MeasurableSpace.comap
          (fun omega : BilateralField d ↦ omega (-(Int.ofNat j))) inferInstance := by
      simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
        MeasurableSpace.comap_comp]
      rfl
    have hle : MeasurableSpace.comap Φ inferInstance ≤ (conditionalFineFiltration H hH) N := by
      change MeasurableSpace.comap Φ inferInstance ≤
        MeasurableSpace.comap H inferInstance ⊔
          ⨆ j : Fin (N + 1), MeasurableSpace.comap
            (fun omega : BilateralField d ↦ omega (-(Int.ofNat j))) inferInstance
      rw [heq]
      exact le_sup_right
    exact (comap_measurable Φ).mono hle le_rfl
  have hHmeas : Measurable[(conditionalFineFiltration H hH) N] H := by
    have hle : MeasurableSpace.comap H inferInstance ≤ (conditionalFineFiltration H hH) N := by
      change MeasurableSpace.comap H inferInstance ≤
        MeasurableSpace.comap H inferInstance ⊔
          ⨆ j : Fin (N + 1), MeasurableSpace.comap
            (fun omega : BilateralField d ↦ omega (-(Int.ofNat j))) inferInstance
      exact le_sup_left
    exact (comap_measurable H).mono hle le_rfl
  have hΨmeas : Measurable[(conditionalFineFiltration H hH) N] Ψ :=
    hHmeas.prodMk hΦmeas
  have hsum : ∀ (omega : BilateralField d) (x : SpatialCoordinates d),
      (∑ j ∈ Finset.range (N + 1), (omega (-(Int.ofNat j))) x) =
        ∑ j : Fin (N + 1), (omega (-(Int.ofNat j))) x := by
    intro omega x
    refine Finset.sum_bij (s := Finset.range (N + 1))
      (t := (Finset.univ : Finset (Fin (N + 1))))
      (fun n hn ↦ ⟨n, by simpa using hn⟩) ?_ ?_ ?_ ?_
    · intro n hn
      simp
    · intro a ha b hb hab
      exact congrArg Fin.val hab
    · intro b hb
      exact ⟨b.1, by simpa using b.2, by simp⟩
    · intro n hn
      rfl
  have hfun : (fun omega : BilateralField d ↦
      ((weightedChaosCutoff M H N omega)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal) =
      (fun omega ↦ ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), g (Ψ omega, x)) := by
    funext omega
    rw [weightedChaosCutoff_centeredCube_toReal_eq_integral M H N omega z r hr]
    apply integral_congr_ae
    filter_upwards with x
    simp only [g, Ψ, Φ, fineDensity, finePotential]
    rw [hsum omega x]
  change Measurable[(conditionalFineFiltration H hH) N]
    (fun omega : BilateralField d ↦ ((weightedChaosCutoff M H N omega)
      (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
  rw [hfun]
  exact (hgmass.comp_measurable hΨmeas).measurable

end SubdiffusiveProcess
