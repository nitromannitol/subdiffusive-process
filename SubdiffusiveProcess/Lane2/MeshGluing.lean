import SubdiffusiveProcess.Lane2.CellAssembly
import SubdiffusiveProcess.Lane2.CellDirichlet
import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Lane2.BoundaryPackaging
import SubdiffusiveProcess.Lane2.NativeBridge
import SubdiffusiveProcess.Lane2.ResponseMarkov
import SubdiffusiveProcess.Lane2.BoundaryResponse
import SubdiffusiveProcess.Lane2.MeshError
import SubdiffusiveProcess.Geometry.ClosedOddGridCover
import SubdiffusiveProcess.Lane2.ExternalInputs
import SubdiffusiveProcess.Main.MeasureTrace
import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff Distributions
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput




noncomputable section
namespace SubdiffusiveProcess

variable {d : ℕ}



theorem lane2_meshGluing [NeZero d] (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (J : ℕ)
    (a : SpatialCoordinates d → ℝ) (ha : Continuous a)
    (lam Lam : ℝ) (hlam : 0 < lam)
    (habounds : ∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
      lam ≤ a x ∧ a x ≤ Lam)
    (φ : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ.toFun)
    (hφsupp : HasCompactSupport φ.toFun)
    (hφQ : tsupport φ.toFun ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)))
    (uc : ∀ k : OddGridIndex d (triadicHalf J),
      H1Function (oddGridCell z R hR (triadicHalf J) k :
        Set (SpatialCoordinates d)))
    (hharm : ∀ k : OddGridIndex d (triadicHalf J),
      IsWeaklyHarmonicOn a
        (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
        (uc k))
    (htrace : ∀ k : OddGridIndex d (triadicHalf J),
      HasZeroTraceDifferenceOn
        (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
        (uc k)
        (φ.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
          (oddGridCell_subset z hR (triadicHalf J) k))) :
    ∃ w : H10Function (centeredCube z R hR : Set (SpatialCoordinates d)),
      (∀ k : OddGridIndex d (triadicHalf J),
        ∀ᵐ x ∂(volume.restrict (oddGridCell z R hR (triadicHalf J) k :
          Set (SpatialCoordinates d))),
          w.toH1Function.toFun x = (uc k).toFun x) ∧
      ContinuousOn w.toH1Function.toFun
        (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
      (∀ k : OddGridIndex d (triadicHalf J),
        ∀ x ∈ frontier (oddGridCell z R hR (triadicHalf J) k :
          Set (SpatialCoordinates d)),
          w.toH1Function.toFun x = φ.toFun x) ∧
      energy a (centeredCube z R hR : Set (SpatialCoordinates d))
          w.toH1Function =
        (∑ k : OddGridIndex d (triadicHalf J),
          energy a (oddGridCell z R hR (triadicHalf J) k :
            Set (SpatialCoordinates d)) (uc k)) ∧
      (∀ k : OddGridIndex d (triadicHalf J),
        energy a (oddGridCell z R hR (triadicHalf J) k :
          Set (SpatialCoordinates d)) (uc k)
          = sInf {e : ℝ | ∃ v : H1Function
              (oddGridCell z R hR (triadicHalf J) k :
                Set (SpatialCoordinates d)),
            HasZeroTraceDifferenceOn
              (oddGridCell z R hR (triadicHalf J) k :
                Set (SpatialCoordinates d)) v
              (φ.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
                (oddGridCell_subset z hR (triadicHalf J) k)) ∧
            e = energy a (oddGridCell z R hR (triadicHalf J) k :
              Set (SpatialCoordinates d)) v}) := by
  classical
  have hQb : Bornology.IsBounded
      (centeredCube z R hR : Set (SpatialCoordinates d)) :=
    (lane2_isOpenBoundedConvexDomain_centeredCube z hR).2.1.isBounded
  have hφk : sobolevDataOfH1 φ ∈ killedSobolevGraph (centeredCube z R hR) :=
    lane2_sobolevDataOfH1_mem_killed_of_test hQb φ hφ hφsupp hφQ
  have htr := htrace
  choose wk hwk1 hwk2 using htrace
  choose wkS hwkS1 hwkS2 using fun k => Lane4.exists_killedSobolevGraph_of_nativeH10 (wk k)
  obtain ⟨W, hWk, hWcell⟩ := lane2_exists_glued_killed
    (Q := centeredCube z R hR)
    (cell := fun k : OddGridIndex d (triadicHalf J) =>
      oddGridCell z R hR (triadicHalf J) k)
    (fun k => oddGridCell_subset z hR (triadicHalf J) k)
    (oddGridCell_pairwiseDisjoint z hR (triadicHalf J))
    (sobolevDataOfH1 φ) hφk
    (fun k => ((wkS k : killedSobolevGraph (oddGridCell z R hR (triadicHalf J) k)) :
      SobolevData (oddGridCell z R hR (triadicHalf J) k)))
    (fun k => (wkS k).property)
  obtain ⟨w0, hw0f, hw0g⟩ :=
    exists_nativeH10Function_of_killedSobolevGraph
      (Ω := centeredCube z R hR) ⟨W, hWk⟩
  have hcellae : ∀ k : OddGridIndex d (triadicHalf J),
      w0.toH1Function.toFun
        =ᵐ[volume.restrict (oddGridCell z R hR (triadicHalf J) k :
          Set (SpatialCoordinates d))] (uc k).toFun := by
    intro k
    have e1 := hWcell k
    have e2 := ae_restrict_of_ae_restrict_of_subset
      (μ := (volume : Measure (SpatialCoordinates d)))
      (oddGridCell_subset z hR (triadicHalf J) k)
      (sobolevDataOfH1_fst_coeFn φ)
    have e3 := hwkS1 k
    have hw0 : w0.toH1Function.toFun
        = fun x => ((W.1 : DomainL2 (centeredCube z R hR)) :
          SpatialCoordinates d → ℝ) x := hw0f
    rw [hw0]
    filter_upwards [e1, e2, e3] with x h1 h2 h3
    rw [h1, h2, h3, hwk1 k x]
    rfl
  have hcellb : ∀ k : OddGridIndex d (triadicHalf J),
      ∃ v : SpatialCoordinates d → ℝ,
        ContinuousOn v (closure (oddGridCell z R hR (triadicHalf J) k :
          Set (SpatialCoordinates d))) ∧
        v =ᵐ[volume.restrict (oddGridCell z R hR (triadicHalf J) k :
          Set (SpatialCoordinates d))] (uc k).toFun ∧
        ∀ x ∈ frontier (oddGridCell z R hR (triadicHalf J) k :
          Set (SpatialCoordinates d)), v x = φ.toFun x := by
    intro k
    have hb : ∀ x ∈ (oddGridCell z R hR (triadicHalf J) k :
        Set (SpatialCoordinates d)), lam ≤ a x ∧ a x ≤ Lam := fun x hx =>
      habounds x (oddGridCell_subset z hR (triadicHalf J) k hx)
    exact (lane2_cellDirichletBoundaryContinuity hd).continuous_up_to_boundary
      (oddGridCenter z R (triadicHalf J) k)
      (R / (2 * ((triadicHalf J : ℕ) : ℝ) + 1)) (div_pos hR (by positivity))
      a lam Lam hlam ha hb
      (φ.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
        (oddGridCell_subset z hR (triadicHalf J) k))
      (uc k) hφ (hharm k) (htr k)
  choose v hvcont hvae hvb using hcellb
  obtain ⟨F, hFcont, hFcell, hFout⟩ := lane2_exists_continuous_glue
    (fun k : OddGridIndex d (triadicHalf J) =>
      oddGridCell z R hR (triadicHalf J) k)
    (oddGridCell_pairwiseDisjoint z hR (triadicHalf J))
    φ.toFun v hvcont hvb
  have hFae : F =ᵐ[volume.restrict
      (centeredCube z R hR : Set (SpatialCoordinates d))]
      w0.toH1Function.toFun := by
    have hcover := oddGrid_union_ae_eq z hR (triadicHalf J)
    rw [← Measure.restrict_congr_set hcover]
    rw [Filter.EventuallyEq, ae_restrict_iUnion_iff]
    intro k
    filter_upwards [hvae k, hcellae k,
      ae_restrict_mem (oddGridCell z R hR (triadicHalf J) k).isOpen.measurableSet]
      with x h1 h2 hx
    rw [hFcell k x hx, h1, ← h2]
  have hnocell : ∀ (k : OddGridIndex d (triadicHalf J)) (x : SpatialCoordinates d),
      x ∈ frontier (oddGridCell z R hR (triadicHalf J) k :
        Set (SpatialCoordinates d)) →
      ∀ j : OddGridIndex d (triadicHalf J),
        x ∉ (oddGridCell z R hR (triadicHalf J) j :
          Set (SpatialCoordinates d)) := by
    intro k x hx j hj
    have hxk : x ∉ (oddGridCell z R hR (triadicHalf J) k :
        Set (SpatialCoordinates d)) := by
      have := hx.2
      rwa [(oddGridCell z R hR (triadicHalf J) k).isOpen.interior_eq] at this
    have hjk : j = k := by
      by_contra hne
      obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.mp hx.1 _
        (oddGridCell z R hR (triadicHalf J) j).isOpen hj
      exact (Set.disjoint_left.mp
        (oddGridCell_pairwiseDisjoint z hR (triadicHalf J) hne) hy1) hy2
    exact hxk (hjk ▸ hj)
  have habd : ∀ᵐ x ∂(volume.restrict
      (centeredCube z R hR : Set (SpatialCoordinates d))),
      ‖a x‖ ≤ max |lam| |Lam| := by
    filter_upwards [ae_restrict_mem (centeredCube z R hR).isOpen.measurableSet]
      with x hx
    obtain ⟨h1, h2⟩ := habounds x hx
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have hl : -|lam| ≤ lam := neg_abs_le lam
      have : -(max |lam| |Lam|) ≤ -|lam| := by simpa using le_max_left |lam| |Lam|
      linarith
    · have : Lam ≤ |Lam| := le_abs_self Lam
      have h4 : |Lam| ≤ max |lam| |Lam| := le_max_right _ _
      linarith
  have hanneg : ∀ᵐ x ∂(volume.restrict
      (centeredCube z R hR : Set (SpatialCoordinates d))), 0 ≤ a x := by
    filter_upwards [ae_restrict_mem (centeredCube z R hR).isOpen.measurableSet]
      with x hx
    exact le_trans hlam.le (habounds x hx).1
  refine ⟨lane2_H10ofAEEq w0 F hFae, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    filter_upwards [hvae k,
      ae_restrict_mem (oddGridCell z R hR (triadicHalf J) k).isOpen.measurableSet]
      with x h1 hx
    show F x = (uc k).toFun x
    rw [hFcell k x hx, h1]
  · show ContinuousOn F
      (closure (centeredCube z R hR : Set (SpatialCoordinates d)))
    rw [← oddGridCell_closure_iUnion_eq_closure_centeredCube z hR (triadicHalf J)]
    exact hFcont
  · intro k x hx
    show F x = φ.toFun x
    exact hFout x (hnocell k x hx)
  · refine lane2_energy_sum_cells (Q := centeredCube z R hR)
      (fun k : OddGridIndex d (triadicHalf J) =>
        oddGridCell z R hR (triadicHalf J) k)
      (fun k => oddGridCell_subset z hR (triadicHalf J) k)
      (oddGridCell_pairwiseDisjoint z hR (triadicHalf J))
      (oddGrid_union_ae_eq z hR (triadicHalf J))
      ha.aestronglyMeasurable habd _ uc (fun k i => ?_)
    refine lane2_grad_ae_eq_of_ae_eq
      (oddGridCell z R hR (triadicHalf J) k).isOpen
      ((lane2_isOpenBoundedConvexDomain_centeredCube
        (oddGridCenter z R (triadicHalf J) k)
        (div_pos hR (by positivity))).2.1.isBounded)
      ((lane2_H10ofAEEq w0 F hFae).toH1Function.restrict
        (oddGridCell z R hR (triadicHalf J) k).isOpen
        (oddGridCell_subset z hR (triadicHalf J) k))
      (uc k) ?_ i
    filter_upwards [hvae k,
      ae_restrict_mem (oddGridCell z R hR (triadicHalf J) k).isOpen.measurableSet]
      with x h1 hx
    show F x = (uc k).toFun x
    rw [hFcell k x hx, h1]
  · intro k
    refine lane2_energy_isLeast (W := oddGridCell z R hR (triadicHalf J) k)
      ha.aestronglyMeasurable
      (ae_restrict_of_ae_restrict_of_subset
        (μ := (volume : Measure (SpatialCoordinates d)))
        (oddGridCell_subset z hR (triadicHalf J) k) habd)
      (ae_restrict_of_ae_restrict_of_subset
        (μ := (volume : Measure (SpatialCoordinates d)))
        (oddGridCell_subset z hR (triadicHalf J) k) hanneg)
      (hharm k) (htr k)





theorem lane2_meshInterpolator
    {d : ℕ} [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (J : ℕ)
        (a : SpatialCoordinates d → ℝ) (lam Lam : ℝ),
        0 < lam →
        Continuous a →
        (∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
          lam ≤ a x ∧ a x ≤ Lam) →
        ∀ φ : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)),
          ContDiff ℝ ∞ φ.toFun →
          HasCompactSupport φ.toFun →
          tsupport φ.toFun ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) →
          ∃ w : H10Function (centeredCube z R hR : Set (SpatialCoordinates d)),
            ContinuousOn w.toH1Function.toFun
              (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
            (∀ k : OddGridIndex d (triadicHalf J),
              let W := oddGridCell z R hR (triadicHalf J) k
              let hW : (W : Set (SpatialCoordinates d)) ⊆
                  (centeredCube z R hR : Set (SpatialCoordinates d)) :=
                oddGridCell_subset z hR (triadicHalf J) k
              let wk : H1Function (W : Set (SpatialCoordinates d)) :=
                w.toH1Function.restrict W.isOpen hW
              let φk : H1Function (W : Set (SpatialCoordinates d)) :=
                φ.restrict W.isOpen hW
              IsWeaklyHarmonicOn a (W : Set (SpatialCoordinates d)) wk ∧
              HasZeroTraceDifferenceOn (W : Set (SpatialCoordinates d)) wk φk ∧
              energy a (W : Set (SpatialCoordinates d)) wk =
                sInf {e : ℝ | ∃ u : H1Function (W : Set (SpatialCoordinates d)),
                  HasZeroTraceDifferenceOn (W : Set (SpatialCoordinates d)) u φk ∧
                  e = energy a (W : Set (SpatialCoordinates d)) u}) ∧
            energy a (centeredCube z R hR : Set (SpatialCoordinates d))
                w.toH1Function =
              (∑ k : OddGridIndex d (triadicHalf J),
                let W := oddGridCell z R hR (triadicHalf J) k
                let hW : (W : Set (SpatialCoordinates d)) ⊆
                    (centeredCube z R hR : Set (SpatialCoordinates d)) :=
                  oddGridCell_subset z hR (triadicHalf J) k
                let φk : H1Function (W : Set (SpatialCoordinates d)) :=
                  φ.restrict W.isOpen hW
                sInf {e : ℝ | ∃ u : H1Function (W : Set (SpatialCoordinates d)),
                  HasZeroTraceDifferenceOn (W : Set (SpatialCoordinates d)) u φk ∧
                  e = energy a (W : Set (SpatialCoordinates d)) u}) ∧
            (∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
              |w.toH1Function.toFun x - φ.toFun x| ≤
                C * (R / (3 : ℝ) ^ J) *
                  sSup ((fun y => ‖fderiv ℝ φ.toFun y‖) ''
                    closure (centeredCube z R hR : Set (SpatialCoordinates d)))) := by
  classical
  refine ⟨2 * Real.sqrt d, by positivity, ?_⟩
  intro z R hR J a lam Lam hlam ha habounds φ hφ hφsupp hφQ
  set m := triadicHalf J with hm
  set cell : OddGridIndex d m → Opens (SpatialCoordinates d) :=
    fun k => oddGridCell z R hR m k with hcell
  have hsub : ∀ k, (cell k : Set (SpatialCoordinates d)) ⊆
      (centeredCube z R hR : Set (SpatialCoordinates d)) :=
    fun k => oddGridCell_subset z hR m k
  have hcellgeom : ∀ k, IsOpenBoundedConvexDomain
      (cell k : Set (SpatialCoordinates d)) := fun k =>
    lane2_isOpenBoundedConvexDomain_centeredCube (oddGridCenter z R m k)
      (div_pos hR (by positivity))
  have hcellsol : ∀ k : OddGridIndex d m,
      ∃ u : H1Function (cell k : Set (SpatialCoordinates d)),
        HasZeroTraceDifferenceOn (cell k : Set (SpatialCoordinates d)) u
          (φ.restrict (cell k).isOpen (hsub k)) ∧
        IsWeaklyHarmonicOn a (cell k : Set (SpatialCoordinates d)) u := by
    intro k
    refine lane2_exists_weaklyHarmonic_of_zeroTrace (hcellgeom k)
      ⟨oddGridCenter z R m k, Metric.mem_ball_self (by positivity)⟩
      (lane2_isEllipticFieldOn_scalar (W := (cell k : Set (SpatialCoordinates d)))
        (cell k).isOpen.measurableSet ha.measurable hlam
        (fun x hx => habounds x (hsub k hx))) _
  choose uc htrace hharm using hcellsol
  obtain ⟨w, hae, hcont, -, hE, hmin⟩ :=
    lane2_meshGluing hd z R hR J a ha lam Lam hlam habounds φ hφ hφsupp hφQ
      uc hharm htrace
  -- the glued datum has the cellwise gradient almost everywhere
  have hgradae : ∀ k : OddGridIndex d m,
      (w.toH1Function.restrict (cell k).isOpen (hsub k)).grad
        =ᵐ[volume.restrict (cell k : Set (SpatialCoordinates d))] (uc k).grad := by
    intro k
    exact lane2_grad_ae_eq_of_ae_eq' (cell k).isOpen (hcellgeom k).2.1.isBounded _ _
      (hae k)
  -- the three cellwise clauses
  have hcellclauses : ∀ k : OddGridIndex d m,
      IsWeaklyHarmonicOn a (cell k : Set (SpatialCoordinates d))
        (w.toH1Function.restrict (cell k).isOpen (hsub k)) ∧
      HasZeroTraceDifferenceOn (cell k : Set (SpatialCoordinates d))
        (w.toH1Function.restrict (cell k).isOpen (hsub k))
        (φ.restrict (cell k).isOpen (hsub k)) ∧
      energy a (cell k : Set (SpatialCoordinates d))
          (w.toH1Function.restrict (cell k).isOpen (hsub k))
        = sInf {e : ℝ | ∃ u : H1Function (cell k : Set (SpatialCoordinates d)),
            HasZeroTraceDifferenceOn (cell k : Set (SpatialCoordinates d)) u
              (φ.restrict (cell k).isOpen (hsub k)) ∧
            e = energy a (cell k : Set (SpatialCoordinates d)) u} := by
    intro k
    refine ⟨lane2_isWeaklyHarmonicOn_congr_ae (cell k).isOpen.measurableSet
      ((hgradae k).symm) (hharm k), ?_, ?_⟩
    · obtain ⟨h, hval, hgrad⟩ := htrace k
      have hresv : (φ.restrict (cell k).isOpen (hsub k)).toFun = φ.toFun := rfl
      have hresg : (φ.restrict (cell k).isOpen (hsub k)).grad = φ.grad := rfl
      simp only [hresv, hresg] at hval hgrad
      refine ⟨lane2_H10ofAEEq2 h (fun x => w.toH1Function.toFun x - φ.toFun x)
        (fun x => w.toH1Function.grad x - φ.grad x) ?_ ?_, ?_, ?_⟩
      · filter_upwards [hae k] with x hx
        show w.toH1Function.toFun x - φ.toFun x = h.toH1Function.toFun x
        rw [hx, hval x]
        ring
      · intro i
        filter_upwards [hgradae k] with x hx
        show w.toH1Function.grad x i - φ.grad x i = h.toH1Function.grad x i
        have hx' : w.toH1Function.grad x i = (uc k).grad x i := congrFun hx i
        rw [hx', congrFun (hgrad x) i]
        simp only [Pi.add_apply]
        ring
      · intro x
        show w.toH1Function.toFun x = φ.toFun x + (w.toH1Function.toFun x - φ.toFun x)
        ring
      · intro x
        show w.toH1Function.grad x = φ.grad x + (w.toH1Function.grad x - φ.grad x)
        funext i
        show w.toH1Function.grad x i = φ.grad x i + (w.toH1Function.grad x i - φ.grad x i)
        ring
    · rw [lane2_energy_congr_ae (cell k).isOpen.measurableSet (hgradae k)]
      exact hmin k
  refine ⟨w, hcont, fun k => hcellclauses k, ?_, ?_⟩
  · rw [hE]
    exact Finset.sum_congr rfl (fun k _ => (hcellclauses k).2.2 ▸
      lane2_energy_congr_ae (cell k).isOpen.measurableSet (hgradae k) ▸ rfl)
  · -- the pointwise clause, cell by cell and then by continuity
    have hbound : ∀ k : OddGridIndex d m,
        ∀ x ∈ (cell k : Set (SpatialCoordinates d)),
          |w.toH1Function.toFun x - φ.toFun x| ≤
            2 * Real.sqrt d * (R / (3 : ℝ) ^ J) *
              sSup ((fun y => ‖fderiv ℝ φ.toFun y‖) ''
                closure (centeredCube z R hR : Set (SpatialCoordinates d))) := by
      intro k
      exact lane2_mesh_cell_error z hR J a lam Lam hlam ha habounds k
        (w.toH1Function.restrict (cell k).isOpen (hsub k))
        (φ.restrict (cell k).isOpen (hsub k))
        (hcellclauses k).1 (hcellclauses k).2.1
        (hcont.mono ((hsub k).trans subset_closure)) hφ
    intro x hx
    -- every point of the cube is a limit of points of the open cells
    have hxcl : x ∈ closure (⋃ k : OddGridIndex d m,
        (cell k : Set (SpatialCoordinates d))) := by
      have hfin : closure (⋃ k : OddGridIndex d m,
          (cell k : Set (SpatialCoordinates d)))
          = ⋃ k : OddGridIndex d m,
            closure (cell k : Set (SpatialCoordinates d)) := by
        refine le_antisymm ?_ ?_
        · exact closure_minimal (Set.iUnion_mono (fun k => subset_closure))
            (isClosed_iUnion_of_finite (fun k => isClosed_closure))
        · exact Set.iUnion_subset (fun k => closure_mono (Set.subset_iUnion (fun k => (cell k : Set (SpatialCoordinates d))) k))
      rw [hfin, oddGridCell_closure_iUnion_eq_closure_centeredCube z hR m]
      exact subset_closure hx
    have hcontdiff : ContinuousOn
        (fun y => |w.toH1Function.toFun y - φ.toFun y|)
        (closure (centeredCube z R hR : Set (SpatialCoordinates d))) :=
      (hcont.sub (hφ.continuous.continuousOn)).abs
    haveI : (nhdsWithin x (⋃ k : OddGridIndex d m,
        (cell k : Set (SpatialCoordinates d)))).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp hxcl
    refine le_of_tendsto
      ((hcontdiff x (subset_closure hx)).mono_left
        (nhdsWithin_mono x (Set.iUnion_subset (fun k =>
          (hsub k).trans subset_closure)))) ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hy
    exact hbound k y hk

end SubdiffusiveProcess
