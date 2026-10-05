module

public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.VariationalResponses.CellDirichlet
public import SubdiffusiveProcess.VariationalResponses.MeshGluing
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Paper.lem_skeleton_smooth_approx
public import Mathlib.Topology.TietzeExtension
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

lemma aux_lem_skeleton_finite_cutoff_glue_continuous_extension
    (f : SpatialCoordinates d → ℝ)
    (hf : ContinuousOn f (closure (Q : Set (SpatialCoordinates d)))) :
    ∃ F : SpatialCoordinates d → ℝ, Continuous F ∧
      ∀ x ∈ closure (Q : Set (SpatialCoordinates d)), F x = f x := by
  classical
  let s : Set (SpatialCoordinates d) := closure (Q : Set (SpatialCoordinates d))
  let fs : C(s, ℝ) := ⟨s.domRestrict f, hf.domRestrict⟩
  obtain ⟨F, hF⟩ := ContinuousMap.exists_restrict_eq isClosed_closure fs
  refine ⟨F, F.continuous, ?_⟩
  intro x hx
  have hFx := DFunLike.congr_fun hF ⟨x, hx⟩
  exact hFx

lemma aux_lem_skeleton_finite_cutoff_glue_closure_cover
    {m : ℕ}
    (cell : Fin m → Opens (SpatialCoordinates d))
    (hcover : (⋃ i : Fin m, (cell i : Set (SpatialCoordinates d)))
      =ᵐ[(volume : Measure (SpatialCoordinates d))]
        (Q : Set (SpatialCoordinates d))) :
    closure (Q : Set (SpatialCoordinates d)) ⊆
      ⋃ i : Fin m, closure (cell i : Set (SpatialCoordinates d)) := by
  have hdense : Dense ((⋃ i : Fin m, (cell i : Set (SpatialCoordinates d))) ∪
      (Q : Set (SpatialCoordinates d))ᶜ) := by
    apply Measure.dense_of_ae (μ := (volume : Measure (SpatialCoordinates d)))
    filter_upwards [hcover] with x hx
    by_cases hQx : x ∈ (Q : Set (SpatialCoordinates d))
    · exact Or.inl (hx.mpr hQx)
    · exact Or.inr hQx
  have hQsub : (Q : Set (SpatialCoordinates d)) ⊆
      closure (⋃ i : Fin m, (cell i : Set (SpatialCoordinates d))) := by
    intro x hx
    have h := hdense.open_subset_closure_inter Q.isOpen hx
    apply (closure_mono ?_) h
    intro y hy
    rcases hy.2 with hyS | hyQ
    · exact hyS
    · exact (hyQ hy.1).elim
  have hSsub : (⋃ i : Fin m, (cell i : Set (SpatialCoordinates d))) ⊆
      ⋃ i : Fin m, closure (cell i : Set (SpatialCoordinates d)) := by
    intro x hx
    rcases mem_iUnion.mp hx with ⟨i, hxi⟩
    exact mem_iUnion.mpr ⟨i, subset_closure hxi⟩
  have hclosed : IsClosed (⋃ i : Fin m,
      closure (cell i : Set (SpatialCoordinates d))) :=
    isClosed_iUnion_of_finite (fun i => isClosed_closure)
  have hSc : closure (⋃ i : Fin m, (cell i : Set (SpatialCoordinates d))) ⊆
      ⋃ i : Fin m, closure (cell i : Set (SpatialCoordinates d)) :=
    closure_minimal hSsub hclosed
  refine closure_minimal (hQsub.trans hSc) hclosed



theorem lem_skeleton_finite_cutoff_glue
    (hd : 2 ≤ d)
    (hQcube : ∃ (z : SpatialCoordinates d) (R : ℝ), 0 < R ∧
      (Q : Set (SpatialCoordinates d)) = Metric.ball z (R / 2))
    (a : ℕ → SpatialCoordinates d → ℝ)
    (ha : ∀ n : ℕ, ContinuousOn (a n) (closure (Q : Set (SpatialCoordinates d))))
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ (Q : Set (SpatialCoordinates d)), lam ≤ a n x ∧ a n x ≤ Lam)
    (m : ℕ) (cent : Fin m → SpatialCoordinates d) (rad : Fin m → ℝ)
    (hrad : ∀ i : Fin m, 0 < rad i)
    (hpart : ∀ i : Fin m,
      (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) ⊆
        (Q : Set (SpatialCoordinates d)))
    (hdisj : Pairwise fun i j : Fin m =>
      Disjoint (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d))
        (centeredCube (cent j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (hcover : (⋃ i : Fin m, (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)))
      =ᵐ[(volume : Measure (SpatialCoordinates d))]
        (Q : Set (SpatialCoordinates d)))
    (bseq : ℕ → SpatialCoordinates d → ℝ)
    (hbseqC : ∀ k : ℕ, ContDiff ℝ ∞ (bseq k))
    (hbseqsupp : ∀ k : ℕ, HasCompactSupport (bseq k))
    (hbseqQ : ∀ k : ℕ,
      tsupport (bseq k) ⊆ (Q : Set (SpatialCoordinates d))) :
    ∃ W : ℕ → ℕ → H10Function (Q : Set (SpatialCoordinates d)),
      ∀ k n : ℕ,
        ContinuousOn (W k n).toH1Function.toFun
          (closure (Q : Set (SpatialCoordinates d))) ∧
        ∃ g : (∀ i : Fin m, H1Function (centeredCube (cent i) (rad i) (hrad i) :
            Set (SpatialCoordinates d))),
          ∃ u : (∀ i : Fin m, H1Function (centeredCube (cent i) (rad i) (hrad i) :
            Set (SpatialCoordinates d))),
            (∀ i : Fin m, ContinuousOn (g i).toFun
                (closure (centeredCube (cent i) (rad i) (hrad i) :
                  Set (SpatialCoordinates d))) ∧
              ∀ x ∈ closure (centeredCube (cent i) (rad i) (hrad i) :
                Set (SpatialCoordinates d)), (g i).toFun x = bseq k x) ∧
            (∀ i : Fin m,
              IsWeaklyHarmonicOn (a n)
                (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))
                (u i) ∧
              HasZeroTraceDifferenceOn
                (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))
                (u i) (g i) ∧
              ContinuousOn (u i).toFun
                (closure (centeredCube (cent i) (rad i) (hrad i) :
                  Set (SpatialCoordinates d))) ∧
              ∀ x ∈ frontier (centeredCube (cent i) (rad i) (hrad i) :
                Set (SpatialCoordinates d)), (u i).toFun x = bseq k x ∧
              energy (a n)
                (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))
                (u i) =
                cellDirichletInfimum (a n)
                  (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))
                  (g i)) ∧
            (∀ i : Fin m, ∀ᵐ x ∂(volume.restrict
              (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))),
              (W k n).toH1Function.toFun x = (u i).toFun x) ∧
            (∀ i : Fin m, ∀ x ∈ frontier (centeredCube (cent i) (rad i) (hrad i) :
              Set (SpatialCoordinates d)), (W k n).toH1Function.toFun x = bseq k x) ∧
            energy (a n) (Q : Set (SpatialCoordinates d))
                (W k n).toH1Function =
              (∑ i : Fin m,
                cellDirichletInfimum (a n)
                  (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))
                  (g i)) := by
  classical
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  let : NeZero d := ⟨Nat.ne_of_gt hdpos⟩
  obtain ⟨z, R, hR, hQball⟩ := hQcube
  let cell : Fin m → Opens (SpatialCoordinates d) :=
    fun i => centeredCube (cent i) (rad i) (hrad i)
  have hQset : (Q : Set (SpatialCoordinates d)) =
      (centeredCube z R hR : Set (SpatialCoordinates d)) := by
    rw [hQball]
    rfl
  have hcellQ : ∀ i : Fin m,
      (cell i : Set (SpatialCoordinates d)) ⊆ (Q : Set (SpatialCoordinates d)) := by
    intro i
    simpa [cell] using! hpart i
  have hcellle : ∀ i : Fin m, cell i ≤ Q := by
    intro i
    exact hcellQ i
  have hQb : Bornology.IsBounded (Q : Set (SpatialCoordinates d)) := by
    rw [hQset]
    exact (isOpenBoundedConvexDomain_centeredCube z hR).2.1.isBounded
  have haext : ∀ n : ℕ, ∃ A : SpatialCoordinates d → ℝ,
      Continuous A ∧
        ∀ x ∈ closure (Q : Set (SpatialCoordinates d)), A x = a n x := by
    intro n
    exact aux_lem_skeleton_finite_cutoff_glue_continuous_extension
      (a n) (ha n)
  choose A hAcont hAeq using haext
  choose lam Lam hlam hbounds using hell
  have hcoverCell : (⋃ i : Fin m, (cell i : Set (SpatialCoordinates d)))
      =ᵐ[(volume : Measure (SpatialCoordinates d))] (Q : Set (SpatialCoordinates d)) := by
    simpa [cell] using! hcover
  have hclosureCell : closure (Q : Set (SpatialCoordinates d)) ⊆
      ⋃ i : Fin m, closure (cell i : Set (SpatialCoordinates d)) :=
    aux_lem_skeleton_finite_cutoff_glue_closure_cover cell hcoverCell
  have hcellgeom : ∀ i : Fin m,
      IsOpenBoundedConvexDomain (cell i : Set (SpatialCoordinates d)) := by
    intro i
    simpa [cell] using!
      (isOpenBoundedConvexDomain_centeredCube (cent i) (hrad i))
  have hAbounds : ∀ n i x, x ∈ (cell i : Set (SpatialCoordinates d)) →
      lam n ≤ A n x ∧ A n x ≤ Lam n := by
    intro n i x hx
    have hxa : x ∈ (Q : Set (SpatialCoordinates d)) := hcellQ i hx
    have hxeq : A n x = a n x := hAeq n x (subset_closure hxa)
    rw [hxeq]
    exact hbounds n x hxa
  let hphi : ∀ (k : ℕ) (i : Fin m),
      H1Function (cell i : Set (SpatialCoordinates d)) := by
    intro k i
    exact H1Function.ofContDiff (cell i).isOpen
      ((hbseqC k).of_le (by simp)) (hbseqsupp k)
  let hphiQ : ∀ k : ℕ, H1Function (Q : Set (SpatialCoordinates d)) := by
    intro k
    exact H1Function.ofContDiff Q.isOpen
      ((hbseqC k).of_le (by simp)) (hbseqsupp k)
  have hper : ∀ k n : ℕ, ∃ W : H10Function (Q : Set (SpatialCoordinates d)),
      ContinuousOn W.toH1Function.toFun (closure (Q : Set (SpatialCoordinates d))) ∧
      ∃ g : ∀ i : Fin m, H1Function (cell i : Set (SpatialCoordinates d)),
      ∃ u : ∀ i : Fin m, H1Function (cell i : Set (SpatialCoordinates d)),
        (∀ i, ContinuousOn (g i).toFun (closure (cell i : Set (SpatialCoordinates d))) ∧
          ∀ x ∈ closure (cell i : Set (SpatialCoordinates d)),
            (g i).toFun x = bseq k x) ∧
        (∀ i,
          IsWeaklyHarmonicOn (a n) (cell i : Set (SpatialCoordinates d)) (u i) ∧
          HasZeroTraceDifferenceOn (cell i : Set (SpatialCoordinates d)) (u i) (g i) ∧
          ContinuousOn (u i).toFun (closure (cell i : Set (SpatialCoordinates d))) ∧
          ∀ x ∈ frontier (cell i : Set (SpatialCoordinates d)),
            (u i).toFun x = bseq k x ∧
          energy (a n) (cell i : Set (SpatialCoordinates d)) (u i) =
            cellDirichletInfimum (a n) (cell i : Set (SpatialCoordinates d)) (g i)) ∧
        (∀ i, ∀ᵐ x ∂(volume.restrict (cell i : Set (SpatialCoordinates d))),
          W.toH1Function.toFun x = (u i).toFun x) ∧
        (∀ i, ∀ x ∈ frontier (cell i : Set (SpatialCoordinates d)),
          W.toH1Function.toFun x = bseq k x) ∧
        energy (a n) (Q : Set (SpatialCoordinates d)) W.toH1Function =
          ∑ i : Fin m, cellDirichletInfimum (a n)
            (cell i : Set (SpatialCoordinates d)) (g i) := by
    intro k n
    let g : ∀ i : Fin m, H1Function (cell i : Set (SpatialCoordinates d)) :=
      fun i => hphi k i
    have hcellsol : ∀ i : Fin m, ∃ u : H1Function (cell i : Set (SpatialCoordinates d)),
        HasZeroTraceDifferenceOn (cell i : Set (SpatialCoordinates d)) u (g i) ∧
          IsWeaklyHarmonicOn (A n) (cell i : Set (SpatialCoordinates d)) u ∧
          IsWeaklyHarmonicOn (a n) (cell i : Set (SpatialCoordinates d)) u := by
      intro i
      have hEll := isEllipticFieldOn_scalar
        (W := (cell i : Set (SpatialCoordinates d)))
        (cell i).isOpen.measurableSet (hAcont n).measurable (hlam n)
        (hAbounds n i)
      obtain ⟨ui, htr, hh⟩ := exists_weaklyHarmonic_of_zeroTrace
        (hcellgeom i)
        ⟨cent i, by
          change cent i ∈ Metric.ball (cent i) (rad i / 2)
          exact Metric.mem_ball_self (half_pos (hrad i))⟩
        hEll (g i)
      have hhraw : IsWeaklyHarmonicOn (a n)
          (cell i : Set (SpatialCoordinates d)) ui := by
        intro ψ
        calc
          (∫ x in (cell i : Set (SpatialCoordinates d)),
              vecDot (a n x • ui.grad x) (ψ.toH1Function.grad x) ∂volume) =
              ∫ x in (cell i : Set (SpatialCoordinates d)),
                vecDot (A n x • ui.grad x) (ψ.toH1Function.grad x) ∂volume := by
            refine setIntegral_congr_ae (cell i).isOpen.measurableSet
              (Filter.Eventually.of_forall ?_)
            intro x hx
            rw [hAeq n x (subset_closure (hcellQ i hx))]
          _ = 0 := hh ψ
      exact ⟨ui, htr, hh, hhraw⟩
    choose u0 htrace hharmA hharm using hcellsol
    have hcellrep : ∀ i : Fin m, ∃ v : SpatialCoordinates d → ℝ,
        ContinuousOn v (closure (cell i : Set (SpatialCoordinates d))) ∧
        v =ᵐ[volume.restrict (cell i : Set (SpatialCoordinates d))] (u0 i).toFun ∧
        ∀ x ∈ frontier (cell i : Set (SpatialCoordinates d)), v x = bseq k x := by
      intro i
      simpa [cell, g] using!
        (cellDirichletBoundaryContinuity (d := d) hd).continuous_up_to_boundary
          (cent i) (rad i) (hrad i) (A n) (lam n) (Lam n) (hlam n) (hAcont n)
          (hAbounds n i) (g i) (u0 i)
          (by simpa [g, hphi] using! (hbseqC k))
          (hharmA i) (htrace i)
    choose v hvcont hvae hvb using hcellrep
    let u : ∀ i : Fin m, H1Function (cell i : Set (SpatialCoordinates d)) :=
      fun i => H1ofAEEq (u0 i) (v i) (hvae i)
    have hharm' : ∀ i : Fin m,
        IsWeaklyHarmonicOn (a n) (cell i : Set (SpatialCoordinates d)) (u i) := by
      intro i
      exact isWeaklyHarmonicOn_congr_ae
        (cell i).isOpen.measurableSet (Filter.EventuallyEq.rfl) (hharm i)
    have htrace' : ∀ i : Fin m,
        HasZeroTraceDifferenceOn (cell i : Set (SpatialCoordinates d)) (u i) (g i) := by
      intro i
      obtain ⟨w, hwval, hwgrad⟩ := htrace i
      have hwae : (fun x => v i x - (g i).toFun x) =ᵐ[
          volume.restrict (cell i : Set (SpatialCoordinates d))]
          w.toH1Function.toFun := by
        filter_upwards [hvae i] with x hx
        rw [hx, hwval x]
        ring
      refine ⟨H10ofAEEq2 w
        (fun x => v i x - (g i).toFun x) w.toH1Function.grad hwae
        (fun j => Filter.EventuallyEq.rfl), ?_, ?_⟩
      · intro x
        change v i x = (g i).toFun x + (v i x - (g i).toFun x)
        ring
      · intro x
        exact hwgrad x
    have hmin : ∀ i : Fin m,
        energy (a n) (cell i : Set (SpatialCoordinates d)) (u i) =
          cellDirichletInfimum (a n) (cell i : Set (SpatialCoordinates d)) (g i) := by
      intro i
      have hameasQ : AEStronglyMeasurable (a n)
          (volume.restrict (Q : Set (SpatialCoordinates d))) :=
        ((ha n).mono subset_closure).aestronglyMeasurable Q.isOpen.measurableSet
      have hameas : AEStronglyMeasurable (a n)
          (volume.restrict (cell i : Set (SpatialCoordinates d))) :=
        hameasQ.mono_measure (Measure.restrict_mono (hcellQ i) le_rfl)
      have habd : ∀ᵐ x ∂(volume.restrict (cell i : Set (SpatialCoordinates d))),
          ‖a n x‖ ≤ max |lam n| |Lam n| := by
        filter_upwards [ae_restrict_mem (cell i).isOpen.measurableSet] with x hx
        obtain ⟨hl, hu⟩ := hbounds n x (hcellQ i hx)
        rw [Real.norm_eq_abs, abs_le]
        constructor
        · have h1 : -|lam n| ≤ lam n := neg_abs_le _
          have h2 : -(max |lam n| |Lam n|) ≤ -|lam n| := by
            exact neg_le_neg (le_max_left |lam n| |Lam n|)
          linarith
        · exact le_trans hu (le_trans (le_abs_self _) (le_max_right _ _))
      have hanneg : ∀ᵐ x ∂(volume.restrict (cell i : Set (SpatialCoordinates d))),
          0 ≤ a n x := by
        filter_upwards [ae_restrict_mem (cell i).isOpen.measurableSet] with x hx
        exact le_trans (hlam n).le (hbounds n x (hcellQ i hx)).1
      simpa [cellDirichletInfimum] using!
        (energy_isLeast (W := cell i) hameas habd hanneg
          (hharm' i) (htrace' i))
    have hphiKilled : sobolevDataOfH1 (hphiQ k) ∈ killedSobolevGraph Q :=
      sobolevDataOfH1_mem_killed_of_test hQb (hphiQ k)
        (by simpa [hphiQ] using! (hbseqC k))
        (by simpa [hphiQ] using! (hbseqsupp k))
        (by simpa [hphiQ] using! (hbseqQ k))
    have htraceFinal := htrace'
    choose wtr hwtrval hwtrgrad using htrace'
    choose wkS hwkS1 hwkS2 using
      fun i => _root_.SubdiffusiveProcess.EllipticRegularity.exists_killedSobolevGraph_of_nativeH10 (wtr i)
    obtain ⟨Wdata, hWkill, hWcell⟩ := exists_glued_killed
      (Q := Q) cell hcellle hdisj (sobolevDataOfH1 (hphiQ k)) hphiKilled
      (fun i => ((wkS i : killedSobolevGraph (cell i)) : SobolevData (cell i)))
      (fun i => (wkS i).property)
    obtain ⟨w0, hw0f, hw0g⟩ :=
      exists_nativeH10Function_of_killedSobolevGraph (Ω := Q) ⟨Wdata, hWkill⟩
    have hcellae : ∀ i : Fin m,
        w0.toH1Function.toFun =ᵐ[volume.restrict (cell i : Set (SpatialCoordinates d))]
          (u i).toFun := by
      intro i
      have e1 := hWcell i
      have e2 := ae_restrict_of_ae_restrict_of_subset
        (μ := (volume : Measure (SpatialCoordinates d))) (hcellQ i)
        (sobolevDataOfH1_fst_coeFn (hphiQ k))
      have e3 := hwkS1 i
      have hw0 : w0.toH1Function.toFun =
          fun x => ((Wdata.1 : DomainL2 Q) : SpatialCoordinates d → ℝ) x := hw0f
      rw [hw0]
      filter_upwards [e1, e2, e3] with x h1 h2 h3
      rw [h1, h2, h3, hwtrval i x]
      have heq : (hphiQ k).toFun x = (g i).toFun x := by
        change bseq k x = bseq k x
        rfl
      rw [heq]
    obtain ⟨F, hFcont, hFcell, hFout⟩ := exists_continuous_glue
      cell hdisj (bseq k) v hvcont hvb
    have hFae : F =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
        w0.toH1Function.toFun := by
      rw [← Measure.restrict_congr_set hcoverCell]
      rw [Filter.EventuallyEq, ae_restrict_iUnion_iff]
      intro i
      filter_upwards [hcellae i,
        ae_restrict_mem (cell i).isOpen.measurableSet] with x hu hx
      rw [hFcell i x hx, hu]
      rfl
    have hFcontQ : ContinuousOn F (closure (Q : Set (SpatialCoordinates d))) :=
      hFcont.mono hclosureCell
    let W : H10Function (Q : Set (SpatialCoordinates d)) :=
      H10ofAEEq w0 F hFae
    have hWcell : ∀ i : Fin m,
        W.toH1Function.toFun =ᵐ[volume.restrict (cell i : Set (SpatialCoordinates d))]
          (u i).toFun := by
      intro i
      filter_upwards [ae_restrict_mem (cell i).isOpen.measurableSet] with x hxi
      change F x = (u i).toFun x
      rw [hFcell i x hxi]
      rfl
    have hnocell : ∀ (i : Fin m) (x : SpatialCoordinates d),
        x ∈ frontier (cell i : Set (SpatialCoordinates d)) →
        ∀ j : Fin m, x ∉ (cell j : Set (SpatialCoordinates d)) := by
      intro i x hxi j hxj
      have hxi' : x ∉ (cell i : Set (SpatialCoordinates d)) := by
        have := hxi.2
        rwa [(cell i).isOpen.interior_eq] at this
      have hij : j = i := by
        by_contra hne
        obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.mp hxi.1 _ (cell j).isOpen hxj
        exact (Set.disjoint_left.mp (hdisj hne) hy1) hy2
      exact hxi' (hij ▸ hxj)
    have hgradae : ∀ i : Fin m,
        (W.toH1Function.restrict (cell i).isOpen (hcellle i)).grad =ᵐ[
          volume.restrict (cell i : Set (SpatialCoordinates d))] (u i).grad := by
      intro i
      exact grad_ae_eq_of_ae_eq' (cell i).isOpen
        (hcellgeom i).2.1.isBounded (W.toH1Function.restrict (cell i).isOpen
          (hcellle i)) (u i) (hWcell i)
    have henergy : energy (a n) (Q : Set (SpatialCoordinates d)) W.toH1Function =
        ∑ i : Fin m, cellDirichletInfimum (a n)
          (cell i : Set (SpatialCoordinates d)) (g i) := by
      rw [show energy (a n) (Q : Set (SpatialCoordinates d)) W.toH1Function =
          energy (a n) (Q : Set (SpatialCoordinates d)) W.toH1Function from rfl]
      have hameasQ : AEStronglyMeasurable (a n)
          (volume.restrict (Q : Set (SpatialCoordinates d))) :=
        ((ha n).mono subset_closure).aestronglyMeasurable Q.isOpen.measurableSet
      have habdQ : ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
          ‖a n x‖ ≤ max |lam n| |Lam n| := by
        filter_upwards [ae_restrict_mem Q.isOpen.measurableSet] with x hx
        obtain ⟨hl, hu⟩ := hbounds n x hx
        rw [Real.norm_eq_abs, abs_le]
        constructor
        · have h1 : -|lam n| ≤ lam n := neg_abs_le _
          have h2 : -(max |lam n| |Lam n|) ≤ -|lam n| := by
            exact neg_le_neg (le_max_left |lam n| |Lam n|)
          linarith
        · exact le_trans hu (le_trans (le_abs_self _) (le_max_right _ _))
      calc
        energy (a n) (Q : Set (SpatialCoordinates d)) W.toH1Function =
            ∑ i : Fin m, energy (a n) (cell i : Set (SpatialCoordinates d)) (u i) := by
          apply (energy_sum_cells (Q := Q) cell hcellle hdisj hcoverCell
            hameasQ habdQ W.toH1Function (fun i => u i) ?_)
          intro i j
          filter_upwards [hgradae i] with x hx
          exact congrFun hx j
        _ = ∑ i : Fin m, cellDirichletInfimum (a n)
            (cell i : Set (SpatialCoordinates d)) (g i) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hmin i
    refine ⟨W, hFcontQ, g, u, ?_, ?_, hWcell, ?_, henergy⟩
    · intro i
      constructor
      · simpa [g, hphi] using!
          ((hbseqC k).continuous.continuousOn :
            ContinuousOn (bseq k) (closure (cell i : Set (SpatialCoordinates d))))
      · intro x hx
        rfl
    · intro i
      refine ⟨hharm' i, htraceFinal i, hvcont i, ?_⟩
      intro x hx
      exact ⟨by simpa [u] using! hvb i x hx, hmin i⟩
    · intro i x hx
      change F x = bseq k x
      exact hFout x (hnocell i x hx)
  choose W hW using hper
  refine ⟨W, ?_⟩
  intro k n
  have hk := hW k n
  simpa [cell] using! hk

end SubdiffusiveProcess.Paper
