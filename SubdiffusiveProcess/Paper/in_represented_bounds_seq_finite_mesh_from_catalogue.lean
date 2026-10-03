module

public import SubdiffusiveProcess.Paper.in_represented_bounds_seq_finite_mesh
public import SubdiffusiveProcess.Paper.lem_cutoffs
public import SubdiffusiveProcess.Lane2.NativeBridge

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- The native H¹ representative selected for a catalogue source agrees with
the smooth trace selected by the represented catalogue, both in value on the
closed root and in weak gradient almost everywhere. -/
theorem aux_in_represented_finite_mesh_catalogue_trace_alignment
    {d : ℕ} [NeZero d]
    {Q : Opens (SpatialCoordinates d)}
    (D : Submodule ℚ (DomainL2 Q))
    (phi : D → H1Function (Q : Set (SpatialCoordinates d)))
    (hPhi : ∀ g : D,
      ContDiff ℝ ∞ (phi g).toFun ∧
      HasCompactSupport (phi g).toFun ∧
      tsupport (phi g).toFun ⊆ (Q : Set (SpatialCoordinates d)) ∧
      (sobolevDataOfH1 (phi g)).1 = g.val)
    (g : D) (b : H1Function (Q : Set (SpatialCoordinates d)))
    (hsource : g.val =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] b.toFun)
    (hbCont : Continuous b.toFun) :
    (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), (phi g).toFun x = b.toFun x) ∧
      (phi g).grad =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] b.grad := by
  have hPhiAE : (phi g).toFun =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] b.toFun := by
    have hdata : (sobolevDataOfH1 (phi g)).1 = g.val := (hPhi g).2.2.2
    have hdataAE :
        ((sobolevDataOfH1 (phi g)).1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
          (g.val : SpatialCoordinates d → ℝ) := by
      rw [hdata]
    exact (sobolevDataOfH1_fst_coeFn (phi g)).symm.trans (hdataAE.trans hsource)
  have hvalClosed := aux_lem_cutoffs_eqOn_closure (Q : Set (SpatialCoordinates d)) Q.isOpen
    (phi g).toFun b.toFun
    ((hPhi g).1.continuous.continuousOn.mono (Set.subset_univ _))
    (hbCont.continuousOn.mono (Set.subset_univ _)) hPhiAE
  have hfirstAE :
      ((sobolevDataOfH1 (phi g)).1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
        ((sobolevDataOfH1 b).1 : SpatialCoordinates d → ℝ) :=
    (sobolevDataOfH1_fst_coeFn (phi g)).trans
      (hPhiAE.trans (sobolevDataOfH1_fst_coeFn b).symm)
  have hfirst : (sobolevDataOfH1 (phi g)).1 = (sobolevDataOfH1 b).1 :=
    Lp.ext hfirstAE
  have hweakPhi :
      ((sobolevDataOfH1 (phi g)).1, (sobolevDataOfH1 (phi g)).2) ∈
        weakSobolevGraph Q := by
    change sobolevDataOfH1 (phi g) ∈ weakSobolevGraph Q
    exact sobolevDataOfH1_mem_weak (phi g)
  have hweakB :
      ((sobolevDataOfH1 (phi g)).1, (sobolevDataOfH1 b).2) ∈
        weakSobolevGraph Q := by
    have hbWeak :
        ((sobolevDataOfH1 b).1, (sobolevDataOfH1 b).2) ∈
          weakSobolevGraph Q := by
      change sobolevDataOfH1 b ∈ weakSobolevGraph Q
      exact sobolevDataOfH1_mem_weak b
    rw [← hfirst] at hbWeak
    exact hbWeak
  have hgradData := weakSobolevGraph_gradient_unique hweakPhi hweakB
  have hgrad : (sobolevDataOfH1 (phi g)).2 = (sobolevDataOfH1 b).2 := hgradData
  have hgradAE : (phi g).grad =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] b.grad := by
    have hcoords : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
        ∀ i, (phi g).grad x i = b.grad x i := by
      apply ae_all_iff.mpr
      intro i
      exact (sobolevDataOfH1_snd_coeFn (phi g) i).symm.trans
        ((show (((sobolevDataOfH1 (phi g)).2 i : DomainL2 Q) :
            SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
              (((sobolevDataOfH1 b).2 i : DomainL2 Q) :
                SpatialCoordinates d → ℝ) from by
            rw [congrFun hgrad i]
            ).trans
          (sobolevDataOfH1_snd_coeFn b i))
    filter_upwards [hcoords] with x hx
    exact funext hx
  exact ⟨hvalClosed, hgradAE⟩

/-- Actual `_hFiniteMesh` supplier from the source and trace clauses of
`conv_represented_estimates`.  The root trace is selected separately for each
catalogue source; cell restrictions are aligned using the native H¹ data before
the existing plateau-cell and harmonic mesh suppliers are applied. -/
theorem in_represented_bounds_seq_finite_mesh_from_catalogue
    {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
    (J : Type) [Countable J] [DecidableEq J] (j0 : J)
    (z : J → SpatialCoordinates d) (rad : J → ℝ) (hrad : ∀ j, 0 < rad j)
    (S : ∀ j, ResponseSpace (centeredCube (z j) (rad j) (hrad j)))
    (Dsrc : ∀ j, Submodule ℚ (DomainL2 (centeredCube (z j) (rad j) (hrad j))))
    [hDc : ∀ j, Countable (Dsrc j)]
    (fSrc : ∀ j, Dsrc j → SpatialCoordinates d → ℝ)
    (T : J → Type) [hTc : ∀ j, Countable (T j)]
    (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
    (thetaH1 : ∀ j, T j → H1Function
      (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (usrc : ∀ j, Dsrc j → ℕ → Ω → (S j).space)
    (srcRep : ∀ j, Dsrc j → ℕ → Ω → SpatialCoordinates d → ℝ)
    (ucell : ∀ j, T j → ℕ → Ω → H1Function
      (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (Cext beta alpha eta t : ℝ) (orders : Finset ℝ) (E : Paper.in_J d)
    (Index : Type) [Countable Index]
    (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
    (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
    (coercivityKey extensionKey lambdaKey : J → Index)
    (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ j, Dsrc j → Index)
    (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
    (Grid : Type) [Countable Grid]
    (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J)
    (gridKey : Grid → Index)
    (hrepresented : conv_represented_estimates d hd M H Ω P cutoff env J j0 z rad hrad
      S Dsrc fSrc T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E
      Index resp respLim constants G coercivityKey extensionKey lambdaKey
      sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey
      cellGrowthKey cellHolderKey Grid origin gridRoot gridKey)
    (omega : Ω) (homega : omega ∈ G)
    (phi : Dsrc j0 → H1Function
      (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)))
    (hPhi : ∀ g : Dsrc j0,
      ContDiff ℝ ∞ (phi g).toFun ∧
      HasCompactSupport (phi g).toFun ∧
      tsupport (phi g).toFun ⊆
        (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)) ∧
      (sobolevDataOfH1 (phi g)).1 = g.val)
    (halpha : 0 < alpha) :
    ∀ g : Dsrc j0, ∃ Cphi : ℝ, 0 ≤ Cphi ∧ ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∃ vN : ℕ → (S j0).space, ∃ vcN : ℕ → SpatialCoordinates d → ℝ,
      ∃ Kset : Set (SpatialCoordinates d),
        IsCompact Kset ∧
        Kset ⊆ (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)) ∧
        ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ,
          (vN n).val.1 =ᵐ[volume.restrict
            (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d))] vcN n ∧
          ContinuousOn (vcN n)
            (closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d))) ∧
          (∀ x ∈ (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)) \ Kset,
            vcN n x = 0) ∧
          Lane4.IsHolderOn alpha
            (closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)))
            (vcN n) ∧
          Lane4.cAlphaNorm alpha
            (closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)))
            (vcN n) ≤ B ∧
          responseForm (S j0)
            (Lane4.cutoffPositiveCoefficient M H (env n omega) (cutoff n) (z j0) (hrad j0))
            (vN n) (vN n) ≤ B ∧
          ∀ x ∈ closure
              (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
            |vcN n x - (phi g).toFun x| ≤ Cphi * (rad j0 / (3 : ℝ) ^ k) := by
  classical
  have hroot := hrepresented
  rcases hroot with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hS, _, hsource, htail⟩
  rcases htail with ⟨_, htail⟩
  rcases htail with ⟨htheta, htail⟩
  rcases htail with ⟨hsourceTrace, _⟩
  let Q : Set (SpatialCoordinates d) := centeredCube (z j0) (rad j0) (hrad j0)
  let raw : ℕ → SpatialCoordinates d → ℝ := fun n =>
    cutoffCoefficient M H (env n omega) (cutoff n)
  let a : ℕ → PositiveCoefficient (centeredCube (z j0) (rad j0) (hrad j0)) := fun n =>
    Lane4.cutoffPositiveCoefficient M H (env n omega) (cutoff n) (z j0) (hrad j0)
  have hrawCont : ∀ n, Continuous (raw n) := by
    intro n
    exact (aux_lem_cutoffs_cutoffCoefficient_cont_pos M H (env n omega) (cutoff n)).1
  have hrawBounds : ∀ n, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ Q, lam ≤ raw n x ∧ raw n x ≤ Lam := by
    intro n
    obtain ⟨lam, Lam, hlam, hbd⟩ :=
      aux_lem_cutoffs_pos_bounds _
        (aux_lem_cutoffs_cutoffCoefficient_cont_pos M H (env n omega) (cutoff n)).1
        (aux_lem_cutoffs_cutoffCoefficient_cont_pos M H (env n omega) (cutoff n)).2
        (closure Q) (lane2_isCompact_closure_centeredCube (z j0) (hrad j0))
    refine ⟨lam, Lam, hlam, ?_⟩
    intro x hx
    exact hbd x (subset_closure hx)
  have hAC : ∀ n, (a n).val =ᵐ[volume.restrict Q] raw n := by
    intro n
    exact aux_lem_cutoffs_positiveCoefficient_ae M H (env n omega) (cutoff n)
      (z j0) (hrad j0)
  have hCell : ∀ (g : Dsrc j0) (Jmesh : ℕ)
      (κ : OddGridIndex d (triadicHalf Jmesh)),
      ∃ Ec Hc : ℝ, 0 ≤ Ec ∧ 0 ≤ Hc ∧
        ∀ (n : ℕ) (w : H1Function
          (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jmesh) κ :
            Set (SpatialCoordinates d))),
          IsWeaklyHarmonicOn (raw n)
            (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jmesh) κ :
              Set (SpatialCoordinates d)) w →
          HasZeroTraceDifferenceOn
            (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jmesh) κ :
              Set (SpatialCoordinates d)) w
            ((phi g).restrict
              (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jmesh) κ).isOpen
              (oddGridCell_subset (z j0) (hrad j0) (triadicHalf Jmesh) κ)) →
          ContinuousOn w.toFun
            (closure (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jmesh) κ :
              Set (SpatialCoordinates d))) →
          energy (raw n)
              (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jmesh) κ :
                Set (SpatialCoordinates d)) w ≤ Ec ∧
          ∀ x ∈ closure (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jmesh) κ :
              Set (SpatialCoordinates d)),
            ∀ y ∈ closure (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jmesh) κ :
              Set (SpatialCoordinates d)),
              |w.toFun x - w.toFun y| ≤
                Hc * (Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2)) ^ alpha := by
    intro g Jmesh κ
    obtain ⟨b, hb⟩ := hsourceTrace j0 g
    obtain ⟨Ec, Gr, Ho, hEc, hGr, hHo, hcell⟩ :=
      aux_lem_cutoffs_rep_plateau_cell d hd M H Cext beta alpha eta t orders Ω P cutoff
        env J j0 z rad hrad S Dsrc fSrc T theta thetaH1 usrc srcRep ucell E Index resp
        respLim constants G coercivityKey extensionKey lambdaKey sourceResponseKey
        sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey
        Grid origin gridRoot gridKey hrepresented omega homega b Jmesh κ
    let h1 : H1Function Q := phi g
    let h2 : H1Function Q := thetaH1 j0 b
    have halign := aux_in_represented_finite_mesh_catalogue_trace_alignment
      (Q := centeredCube (z j0) (rad j0) (hrad j0)) (Dsrc j0) phi hPhi g h2
      (by
        have hs : g.val =ᵐ[volume.restrict Q] fSrc j0 g :=
          (hsource j0 g).2.2.2
        have hbAE : fSrc j0 g =ᵐ[volume.restrict Q] h2.toFun := by
          filter_upwards [] with x
          change fSrc j0 g x = (thetaH1 j0 b).toFun x
          rw [(congrFun (htheta j0 b).2 x)]
          exact (congrFun hb x).symm
        exact hs.trans hbAE)
      (by
        have hh := htheta j0 b
        change Continuous (thetaH1 j0 b).toFun
        rw [hh.2]
        exact hh.1.continuous)
    refine ⟨Ec, Ho, hEc, hHo, ?_⟩
    intro n w hw htr hwc
    have htrace' : HasZeroTraceDifferenceOn
        (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jmesh) κ :
          Set (SpatialCoordinates d)) w
        ((h2).restrict
          (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jmesh) κ).isOpen
          (oddGridCell_subset (z j0) (hrad j0) (triadicHalf Jmesh) κ)) := by
      apply aux_lem_cutoffs_traceDiff_congr
        (W := (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jmesh) κ :
          Set (SpatialCoordinates d)))
        (u := w)
        (h := (h1).restrict
          (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jmesh) κ).isOpen
          (oddGridCell_subset (z j0) (hrad j0) (triadicHalf Jmesh) κ))
        (h' := (h2).restrict
          (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jmesh) κ).isOpen
          (oddGridCell_subset (z j0) (hrad j0) (triadicHalf Jmesh) κ))
        (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf Jmesh) κ).isOpen htr
      · intro x hx
        simpa only [H1Function.restrict] using!
          halign.1 x (subset_closure (oddGridCell_subset
            (z j0) (hrad j0) (triadicHalf Jmesh) κ hx))
      · simpa only [H1Function.restrict] using!
          (ae_restrict_of_ae_restrict_of_subset
            (oddGridCell_subset (z j0) (hrad j0) (triadicHalf Jmesh) κ) halign.2)
    have hbound := hcell n w hw (by simpa [h2] using htrace') hwc
    exact ⟨hbound.1, hbound.2.2⟩
  exact in_represented_bounds_seq_finite_mesh hd (z j0) (rad j0) (hrad j0)
    (S j0) (hS j0) a raw hrawCont hrawBounds hAC (Dsrc j0) phi hPhi alpha halpha hCell



end Paper
