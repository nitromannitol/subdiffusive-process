module

public import SubdiffusiveProcess.Paper.lem_cutoffs
public import SubdiffusiveProcess.Paper.catalog_cutoff_existence
public import SubdiffusiveProcess.Geometry.SmoothPlateau

@[expose] public section

/-! Deterministic cutoff families assembled from actual harmonic-cell estimates.
The supplied estimates are retained as explicit inputs; this module asserts no random bounds. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Filter Set TopologicalSpace SubdiffusiveProcess Homogenization
open _root_.SubdiffusiveProcess.EllipticRegularity SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff BigOperators
namespace SubdiffusiveProcess.Paper
noncomputable section

/-- Bounds for all harmonic solutions on the cells of one smooth-data mesh. -/
def aux_prop_conc_mesh_cutoff_family_CellBounds
    {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (a : ℕ → SpatialCoordinates d → ℝ) (t alpha : ℝ)
    (Jmesh : ℕ) (θH : H1Function (centeredCube z R hR : Set (SpatialCoordinates d))) : Prop :=
∀ k : OddGridIndex d (triadicHalf Jmesh), ∃ E Gr Ho : ℝ,
      0 ≤ E ∧ 0 ≤ Gr ∧ 0 ≤ Ho ∧
      ∀ (n : ℕ) (w : H1Function
          (oddGridCell z R hR (triadicHalf Jmesh) k : Set (SpatialCoordinates d))),
        IsWeaklyHarmonicOn (a n)
          (oddGridCell z R hR (triadicHalf Jmesh) k : Set (SpatialCoordinates d)) w →
        HasZeroTraceDifferenceOn
          (oddGridCell z R hR (triadicHalf Jmesh) k : Set (SpatialCoordinates d)) w
          (θH.restrict (oddGridCell z R hR (triadicHalf Jmesh) k).isOpen
            (oddGridCell_subset z hR (triadicHalf Jmesh) k)) →
        ContinuousOn w.toFun
          (closure (oddGridCell z R hR (triadicHalf Jmesh) k : Set (SpatialCoordinates d))) →
        energy (a n)
            (oddGridCell z R hR (triadicHalf Jmesh) k : Set (SpatialCoordinates d)) w ≤ E ∧
        (∀ x ∈ closure (oddGridCell z R hR (triadicHalf Jmesh) k :
            Set (SpatialCoordinates d)), ∀ r : ℝ, 0 < r → r ≤ 1 →
          ((volume.restrict (oddGridCell z R hR (triadicHalf Jmesh) k :
              Set (SpatialCoordinates d))).withDensity
            (fun y => ENNReal.ofReal (a n y * ∑ i : Fin d, (w.grad y i) ^ 2)))
            (Metric.ball x r) ≤ ENNReal.ofReal (Gr * r ^ t)) ∧
        (∀ x ∈ closure (oddGridCell z R hR (triadicHalf Jmesh) k :
            Set (SpatialCoordinates d)),
          ∀ y ∈ closure (oddGridCell z R hR (triadicHalf Jmesh) k :
            Set (SpatialCoordinates d)),
          |w.toFun x - w.toFun y| ≤
            Ho * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha)

/-- Uniform bounds on every admissible harmonic mesh, with a separate constant for each datum and cell. -/
def aux_prop_conc_mesh_cutoff_family_AllCellBounds
    {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (a : ℕ → SpatialCoordinates d → ℝ) (t alpha : ℝ) : Prop :=
  ∀ J : ℕ, R / (3 : ℝ) ^ J ≤ 1 →
    ∀ theta : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ theta →
    ∀ thetaH : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)),
      thetaH.toFun = theta →
      aux_prop_conc_mesh_cutoff_family_CellBounds z R hR a t alpha J thetaH

/-- Cutoffs with a common energy and ball-growth bound for each compactly contained pair. -/
def aux_prop_conc_mesh_cutoff_family_Cutoffs
    {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (aC : ℕ → PositiveCoefficient (centeredCube z R hR)) (t : ℝ) : Prop :=
    ∀ K O : Set (SpatialCoordinates d), IsCompact K → IsOpen O → K ⊆ O →
      closure O ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → S.space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n) (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] chic n ∧
          (∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
            0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
          responseForm S (aC n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)), ∀ rr : ℝ,
            0 < rr → rr ≤ 1 →
            ((volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((aC n).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t))

/-- A fixed harmonic mesh gives cutoffs with one common energy and growth bound. -/
theorem aux_prop_conc_mesh_cutoff_family_of_mesh
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (hS : S.space = killedSobolevGraph (centeredCube z R hR))
    (a : ℕ → SpatialCoordinates d → ℝ) (ha : ∀ n, Continuous (a n))
    (hapos : ∀ n x, 0 < a n x)
    (aC : ℕ → PositiveCoefficient (centeredCube z R hR))
    (hAC : ∀ n, ((aC n).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] a n)
    (t alpha : ℝ) (ht : 0 ≤ t) (halpha : 0 < alpha)
    (theta : SpatialCoordinates d → ℝ)
    (thetaH : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hthetaH : thetaH.toFun = theta) (htheta : ContDiff ℝ ∞ theta)
    (K O V0 : Set (SpatialCoordinates d)) (J : ℕ)
    (hO : IsOpen O) (hOQ : closure O ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hKV0 : K ⊆ V0) (hV0O : V0 ⊆ O)
    (hrange : ∀ x, 0 ≤ theta x ∧ theta x ≤ 1)
    (hone : ∀ x ∈ V0, theta x = 1) (hsupp : tsupport theta ⊆ O)
    (htrans : ∀ k : OddGridIndex d (triadicHalf J),
      (closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) ∩
        {x | 0 < theta x ∧ theta x < 1}).Nonempty →
      closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) ⊆ O \ K)
    (hcell : aux_prop_conc_mesh_cutoff_family_CellBounds z R hR a t alpha J thetaH) :
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → S.space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n) (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] chic n ∧
          (∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
            0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
          responseForm S (aC n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)), ∀ rr : ℝ,
            0 < rr → rr ≤ 1 →
            ((volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((aC n).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)) := by
  have dimensionNonzero : NeZero d := ⟨by omega⟩
  obtain ⟨_chiH, chiS, chic, V, BE, BG, BH, hV, hKV, hVO, hBE, _hBG, _hBH, hchi, _⟩ :=
    aux_lem_cutoffs_plateau_generic hd z R hR S hS a ha hapos aC hAC
      t alpha ht halpha theta thetaH hthetaH htheta K O V0 J hO hOQ hKV0 hV0O
      hrange hone hsupp htrans hcell
  refine ⟨V, chiS, chic, max BE BG, hV, hKV, hVO, hBE.trans (le_max_left _ _), ?_⟩
  intro n
  obtain ⟨_hrep, hc, hae, hrange, h1, h0, _hharm, _hconst, he, hg, _hhol, _hnorm⟩ := hchi n
  refine ⟨hc, hae, (fun x hx => hrange x (subset_closure hx)), h1, h0,
    he.trans (le_max_left _ _), ?_⟩
  intro x hx rad hrad hrad1
  exact (hg x hx rad hrad hrad1).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hrad.le _)))


/-- Uniform harmonic-cell estimates construct continuous cutoffs with uniformly bounded energy and ball growth. -/
theorem prop_conc_mesh_cutoff_family
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (hS : S.space = killedSobolevGraph (centeredCube z R hR))
    (a : ℕ → SpatialCoordinates d → ℝ) (ha : ∀ n, Continuous (a n))
    (hapos : ∀ n x, 0 < a n x)
    (aC : ℕ → PositiveCoefficient (centeredCube z R hR))
    (hAC : ∀ n, ((aC n).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] a n)
    (t alpha : ℝ) (ht : 0 ≤ t) (halpha : 0 < alpha)
    (hcell : ∀ J : ℕ, R / (3 : ℝ) ^ J ≤ 1 →
      ∀ theta : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ theta →
      ∀ thetaH : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)),
        thetaH.toFun = theta →
        aux_prop_conc_mesh_cutoff_family_CellBounds z R hR a t alpha J thetaH) :
    ∀ K O : Set (SpatialCoordinates d), IsCompact K → IsOpen O → K ⊆ O →
      closure O ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → S.space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n) (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] chic n ∧
          (∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
            0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
          responseForm S (aC n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)), ∀ rr : ℝ,
            0 < rr → rr ≤ 1 →
            ((volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((aC n).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)) := by
  have dimensionNonzero : NeZero d := ⟨by omega⟩
  intro K O hK hO hKO hOQ
  obtain ⟨theta, V0, htheta, hcompact, hsupp, hV0, hKV0, hV0O, hrange, hone⟩ :=
    exists_smooth_compact_plateau K O hK hO hKO
  obtain ⟨J, V1, _hV1, _hKV1, _hV1O, _hone1, _hnear, htrans, hside⟩ :=
    aux_catalog_cutoff_existence_mesh_geometry z R hR theta hcompact
      K O V0 hK hO hKO hV0 hKV0 hV0O hone hsupp
  let thetaH : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)) :=
    H1Function.ofContDiff (centeredCube z R hR).isOpen (htheta.of_le (by norm_num)) hcompact
  exact aux_prop_conc_mesh_cutoff_family_of_mesh d hd z R hR S hS a ha hapos aC hAC
    t alpha ht halpha theta thetaH rfl htheta K O V0 J hO hOQ hKV0 hV0O hrange hone hsupp
    htrans (hcell J hside.le theta htheta thetaH rfl)

end
end SubdiffusiveProcess.Paper
