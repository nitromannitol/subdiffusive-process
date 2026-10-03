module

public import SubdiffusiveProcess.Paper.prop_conc_mesh_cutoff_family
public import SubdiffusiveProcess.Paper.prop_conc_harmonic_cell_trace
public import SubdiffusiveProcess.Geometry.EuclideanHolderMetric

@[expose] public section

/-! Smooth harmonic meshes with the precise trace, energy and growth data used
by the local boundary theorem. All coefficient and cell estimates remain explicit. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff BigOperators
namespace Paper
noncomputable section

/-- The native harmonic mesh and its estimates in the ambient killed response space. -/
structure aux_prop_conc_boundary_mesh_Data
    {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (a : ℕ → SpatialCoordinates d → ℝ)
    (aC : ℕ → PositiveCoefficient (centeredCube z R hR))
    (beta : SpatialCoordinates d → ℝ)
    (betaH : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (J : ℕ) (t alpha : ℝ) where
  u : ℕ → H1Function (centeredCube z R hR : Set (SpatialCoordinates d))
  uS : ℕ → S.space
  rep : ∀ n, (uS n : SobolevData (centeredCube z R hR)) = sobolevDataOfH1 (u n)
  continuous : ∀ n, ContinuousOn (u n).toFun (closure (centeredCube z R hR : Set (SpatialCoordinates d)))
  harmonic : ∀ n k, IsWeaklyHarmonicOn (a n)
    (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
    ((u n).restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
      (oddGridCell_subset z hR (triadicHalf J) k))
  trace : ∀ n k, HasZeroTraceDifferenceOn
    (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
    ((u n).restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
      (oddGridCell_subset z hR (triadicHalf J) k))
    (betaH.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
      (oddGridCell_subset z hR (triadicHalf J) k))
  boundary : ∀ n k, ∀ x ∈ frontier (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)),
    (u n).toFun x = beta x
  E : OddGridIndex d (triadicHalf J) → ℝ
  H : OddGridIndex d (triadicHalf J) → ℝ
  E_nonneg : ∀ k, 0 ≤ E k
  H_nonneg : ∀ k, 0 ≤ H k
  energy : ∀ n k, SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.energy (a n)
    (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
    ((u n).restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
      (oddGridCell_subset z hR (triadicHalf J) k)) ≤ E k
  growth : ∀ n k, ∀ x ∈ closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)),
    ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
      ((volume.restrict (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))).withDensity
        (fun y => ENNReal.ofReal ((aC n).val y * ∑ i : Fin d, ((uS n).val.2 i y) ^ 2)))
        (Metric.ball x rr) ≤ ENNReal.ofReal (E k * rr ^ t)
  holder : ∀ n k,
    (∀ x ∈ closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)),
      ∀ y ∈ closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)),
      |(u n).toFun x - (u n).toFun y| ≤ H k * dist x y ^ alpha) ∧
    (∀ x ∈ closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)),
      |(u n).toFun x| ≤ H k)

/-- Smooth cell bounds construct the full harmonic-mesh input for boundary identification. -/
theorem prop_conc_boundary_mesh
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (hS : S.space = killedSobolevGraph (centeredCube z R hR))
    (a : ℕ → SpatialCoordinates d → ℝ) (ha : ∀ n, Continuous (a n))
    (hpos : ∀ n x, 0 < a n x)
    (aC : ℕ → PositiveCoefficient (centeredCube z R hR))
    (hAC : ∀ n, (aC n).val =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] a n)
    (beta : SpatialCoordinates d → ℝ) (hbeta : ContDiff ℝ ∞ beta)
    (hcomp : HasCompactSupport beta)
    (hsupp : tsupport beta ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)))
    (betaH : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hbetaH : betaH.toFun = beta)
    (J : ℕ) (t alpha : ℝ) (halpha : 0 ≤ alpha)
    (hcell : aux_prop_conc_mesh_cutoff_family_CellBounds z R hR a t alpha J betaH) :
    Nonempty (aux_prop_conc_boundary_mesh_Data z R hR S a aC beta betaH J t alpha) := by
  classical
  haveI dimensionNonzero : NeZero d := ⟨by omega⟩
  obtain ⟨Cmesh, _hCmesh, hmesh⟩ := mesh_interpolator (d := d) hd
  choose lam Lam hlam hboundsQ using fun n => aux_lem_cutoffs_pos_bounds (a n) (ha n) (hpos n)
    (closure (centeredCube z R hR : Set (SpatialCoordinates d)))
    (lane2_isCompact_closure_centeredCube z hR)
  have hex n := hmesh z R hR J (a n) (lam n) (Lam n) (hlam n) (ha n)
    (fun x hx => hboundsQ n x (subset_closure hx)) betaH
    (by simpa only [hbetaH] using hbeta) (by simpa only [hbetaH] using hcomp)
    (by simpa only [hbetaH] using hsupp)
  choose w hwcont hwcell hwsum hwerr using hex
  let us : ℕ → S.space := fun n =>
    ⟨sobolevDataOfH1 (w n).toH1Function, hS.symm ▸ sobolevDataOfH1_mem_killed (w n)⟩
  choose E Gr Ho hE hGr hHo hb using hcell
  have hlocalcont n k : ContinuousOn (w n).toH1Function.toFun
      (closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))) :=
    (hwcont n).mono (closure_mono (oddGridCell_subset z hR (triadicHalf J) k))
  have hlocal n k := hb k n _ (hwcell n k).1 (hwcell n k).2.1 (hlocalcont n k)
  obtain ⟨Cb, hCb⟩ := ((lane2_isCompact_closure_centeredCube z hR).image_of_continuousOn
    hbeta.continuous.abs.continuousOn).bddAbove
  let Err : ℝ := Cmesh * (R / (3 : ℝ) ^ J) *
    sSup ((fun y => ‖fderiv ℝ beta y‖) '' closure (centeredCube z R hR : Set (SpatialCoordinates d)))
  have herr n : ∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
      |(w n).toH1Function.toFun x - beta x| ≤ Err := by
    intro x hx
    apply ContinuousWithinAt.closure_le hx
      ((((hwcont n).sub hbeta.continuous.continuousOn).abs x hx).mono subset_closure)
      continuousWithinAt_const
    simpa only [hbetaH] using! hwerr n
  have habs n : ∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
      |(w n).toH1Function.toFun x| ≤ |Err| + |Cb| := by
    intro x hx
    have hbc := hCb ⟨x, hx, rfl⟩
    have htri := abs_add_le ((w n).toH1Function.toFun x - beta x) (beta x)
    rw [sub_add_cancel] at htri
    exact htri.trans (add_le_add ((herr n x hx).trans (le_abs_self _))
      (hbc.trans (le_abs_self _)))
  refine ⟨{
    u := fun n => (w n).toH1Function
    uS := us
    rep := fun _ => rfl
    continuous := hwcont
    harmonic := fun n k => (hwcell n k).1
    trace := fun n k => (hwcell n k).2.1
    boundary := ?_
    E := fun k => max (E k) (Gr k)
    H := fun k => max (Ho k * (d : ℝ) ^ alpha) (|Err| + |Cb|)
    E_nonneg := fun k => (hE k).trans (le_max_left _ _)
    H_nonneg := fun k => (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans (le_max_right _ _)
    energy := fun n k => (hlocal n k).1.trans (le_max_left _ _)
    growth := ?_
    holder := ?_ }⟩
  · intro n k x hx
    have hsmooth : ContDiff ℝ ∞
        (betaH.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
          (oddGridCell_subset z hR (triadicHalf J) k)).toFun := by
      change ContDiff ℝ ∞ betaH.toFun
      rw [hbetaH]
      exact hbeta
    have ht := prop_conc_harmonic_cell_trace hd
      (oddGridCenter z R (triadicHalf J) k) _ (div_pos hR (by positivity))
      (a n) (ha n) (hpos n) _ _ hsmooth (hwcell n k).1 (hwcell n k).2.1
      (hlocalcont n k) x hx
    exact ht.trans (congrFun hbetaH x)
  · intro n k x hx rr hrr hrr1
    have hcoeff := ae_restrict_of_ae_restrict_of_subset
      (oddGridCell_subset z hR (triadicHalf J) k) (hAC n)
    have hgrad : ∀ i : Fin d, (us n).val.2 i =ᵐ[volume.restrict
        (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))]
        fun y => (w n).toH1Function.grad y i := fun i =>
      ae_restrict_of_ae_restrict_of_subset (oddGridCell_subset z hR (triadicHalf J) k)
        (sobolevDataOfH1_snd_coeFn (w n).toH1Function i)
    have hdensity : (fun y => ENNReal.ofReal ((aC n).val y * ∑ i : Fin d, ((us n).val.2 i y) ^ 2))
        =ᵐ[volume.restrict (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))]
        (fun y => ENNReal.ofReal (a n y * ∑ i : Fin d, ((w n).toH1Function.grad y i) ^ 2)) := by
      filter_upwards [hcoeff, ae_all_iff.mpr hgrad] with y hy hgy
      rw [hy]
      congr 2
      exact Finset.sum_congr rfl (fun i _ => congrArg (fun v : ℝ => v ^ 2) (hgy i))
    rw [withDensity_congr_ae hdensity]
    exact ((hlocal n k).2.1 x hx rr hrr hrr1).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hrr.le _)))
  · intro n k
    constructor
    · intro x hx y hy
      exact (euclidean_holder_le_metric x y halpha (hHo k) ((hlocal n k).2.2 x hx y hy)).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _))
    · intro x hx
      exact (habs n x (closure_mono (oddGridCell_subset z hR (triadicHalf J) k) hx)).trans
        (le_max_right _ _)

end
end Paper
