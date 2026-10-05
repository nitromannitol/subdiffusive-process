module

public import SubdiffusiveProcess.Paper.conv_represented_sequence
public import SubdiffusiveProcess.Paper.conv_represented_estimates
public import SubdiffusiveProcess.Paper.mesh_interpolator
public import SubdiffusiveProcess.Paper.cell_boundary_continuity
public import SubdiffusiveProcess.Paper.prop_growth
public import SubdiffusiveProcess.Paper.lane4_deterministic_coefficient_class
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.MultiplicativeChaos.CampanatoCutoff
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import Mathlib.Topology.TietzeExtension

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper



theorem prop_gluing_smooth_mesh
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (hcellsub : ∀ k : OddGridIndex d (triadicHalf 1),
      ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
          Set (SpatialCoordinates d)) ⊆
        (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (alpha t : ℝ) (_ht : (d : ℝ) - 1 < t) (_htd : t < (d : ℝ))
    (S : ResponseSpace (centeredCube z (3 * r) h3r))
    (hS : S.space = killedSobolevGraph (centeredCube z (3 * r) h3r))
    (A : ℕ → SpatialCoordinates d → ℝ)
    (hAcont : ∀ n : ℕ, ContinuousOn (A n)
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
        lam ≤ A n x ∧ A n x ≤ Lam)
    (Catalog : Set (SpatialCoordinates d → ℝ))
    (hCatalog : ∀ Phi ∈ Catalog,
      ContDiff ℝ ∞ Phi ∧ HasCompactSupport Phi ∧
        tsupport Phi ⊆ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hCatalogBounds : ∀ Phi, Phi ∈ Catalog →
      ∀ PhiH : H1Function
          (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
        PhiH.toFun = Phi →
        ∃ Bcell Hcell : OddGridIndex d (triadicHalf 1) → ℝ,
          (∀ k : OddGridIndex d (triadicHalf 1),
            0 ≤ Bcell k ∧ 0 ≤ Hcell k) ∧
          ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1))
            (w : H1Function
              ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))),
            IsWeaklyHarmonicOn (A n)
              ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) w →
            HasZeroTraceDifferenceOn
              ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) w
              (PhiH.restrict
                (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
                (hcellsub k)) →
            energy (A n)
                ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                  Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) w ≤
              Bcell k ∧
            (∀ x ∈ closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
              ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
                ((volume.restrict
                  ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                    Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))).withDensity
                  (fun y => ENNReal.ofReal ((A n) y *
                    ∑ i : Fin d, (w.grad y i) ^ 2)))
                  (Metric.ball x rr) ≤ ENNReal.ofReal (Bcell k * rr ^ t)) ∧
            ∃ wc : SpatialCoordinates d → ℝ,
              ContinuousOn wc
                (closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                  Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))) ∧
              w.toFun =ᵐ[volume.restrict
                ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                  Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))] wc ∧
              (∀ x ∈ closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                  Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
                ∀ y ∈ closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                  Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
                  |wc x - wc y| ≤ Hcell k * dist x y ^ alpha) ∧
              (∀ x ∈ closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                  Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
                |wc x| ≤ Hcell k)) :
    ∀ Phi ∈ Catalog,
      ∃ (PhiH : H1Function
          (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
        (Phiq : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)))
        (UN : ℕ → H1Function
          (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
        (UNS : ℕ → S.space)
        (Bcell Hcell : OddGridIndex d (triadicHalf 1) → ℝ),
        PhiH.toFun = Phi ∧
        Phiq.toFun = Phi ∧
        (∀ k : OddGridIndex d (triadicHalf 1),
          0 ≤ Bcell k ∧ 0 ≤ Hcell k) ∧
        (∀ n : ℕ,
          (UNS n : SobolevData (centeredCube z (3 * r) h3r)) =
            sobolevDataOfH1 (UN n) ∧
          ContinuousOn (UN n).toFun
            (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
          (∀ x ∈ frontier (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
            (UN n).toFun x = 0) ∧
          ∀ k : OddGridIndex d (triadicHalf 1),
            IsWeaklyHarmonicOn (A n)
              ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))
              ((UN n).restrict
                (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
                (hcellsub k)) ∧
            HasZeroTraceDifferenceOn
              ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))
              ((UN n).restrict
                (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
                (hcellsub k))
              (PhiH.restrict
                (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
                (hcellsub k)) ∧
            ContinuousOn (UN n).toFun
              (closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))) ∧
            (∀ x ∈ frontier ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
              (UN n).toFun x = Phi x)) ∧
        (∀ n : ℕ, ∀ k : OddGridIndex d (triadicHalf 1),
          energy (A n)
              ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))
              ((UN n).restrict
                (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
                (hcellsub k)) ≤ Bcell k) ∧
        (∀ n : ℕ, ∀ k : OddGridIndex d (triadicHalf 1),
          ∀ x ∈ closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
            Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
          ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict
              ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((A n) y *
                ∑ i : Fin d, ((UNS n : SobolevData
                  (centeredCube z (3 * r) h3r)).2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (Bcell k * rr ^ t)) ∧
        (∀ n : ℕ, ∀ k : OddGridIndex d (triadicHalf 1),
          (∀ x ∈ closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
              Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
            ∀ y ∈ closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
              Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
              |(UN n).toFun x - (UN n).toFun y| ≤
                Hcell k * dist x y ^ alpha) ∧
          (∀ x ∈ closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
              Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
            |(UN n).toFun x| ≤ Hcell k)) := by
  classical
  let : NeZero d := ⟨by omega⟩
  intro Phi hPhiMem
  have hPhiData := hCatalog Phi hPhiMem
  have hPhiSmooth1 : ContDiff ℝ 1 Phi := by
    exact hPhiData.1.of_le (by simp)
  let Q : Set (SpatialCoordinates d) :=
    (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))
  let PhiH : H1Function Q :=
    H1Function.ofContDiff (centeredCube z (3 * r) h3r).isOpen
      hPhiSmooth1 hPhiData.2.1
  have hPhiH : PhiH.toFun = Phi := by
    rfl
  let Phiq : H1Function
      (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    H1Function.ofContDiff (centeredCube z r hr).isOpen
      hPhiSmooth1 hPhiData.2.1
  have hPhiq : Phiq.toFun = Phi := by
    rfl
  have hAext : ∀ n : ℕ, ∃ a : SpatialCoordinates d → ℝ,
      Continuous a ∧
        ∀ x ∈ closure Q, a x = A n x := by
    intro n
    let f : C(closure Q, ℝ) :=
      ⟨fun x : closure Q => A n x,
        (continuousOn_iff_continuous_domRestrict.mp (hAcont n))⟩
    obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq isClosed_closure f
    refine ⟨g, g.continuous, ?_⟩
    intro x hx
    have hxg := congrArg (fun h : C(closure Q, ℝ) => h ⟨x, hx⟩) hg
    simpa [f] using! hxg
  choose aext haext hAeq using hAext
  have hmesh : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : SpatialCoordinates d → ℝ) (lam Lam : ℝ),
        0 < lam → Continuous a →
        (∀ x ∈ Q, lam ≤ a x ∧ a x ≤ Lam) →
        ∃ w : H10Function Q,
          ContinuousOn w.toH1Function.toFun (closure Q) ∧
          (∀ k : OddGridIndex d (triadicHalf 1),
            IsWeaklyHarmonicOn a
              (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                Set (SpatialCoordinates d))
              (w.toH1Function.restrict
                (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
                (hcellsub k)) ∧
            HasZeroTraceDifferenceOn
              (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                Set (SpatialCoordinates d))
              (w.toH1Function.restrict
                (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
                (hcellsub k))
              (PhiH.restrict
                (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
                (hcellsub k))
            ) := by
    obtain ⟨C, hC, h⟩ := mesh_interpolator (d := d) hd
    refine ⟨C, hC, ?_⟩
    intro a lam Lam hlam ha hab
    have hPhiSmooth : ContDiff ℝ ∞ PhiH.toFun := by
      simpa [hPhiH] using hPhiData.1
    have hPhiCompact : HasCompactSupport PhiH.toFun := by
      simpa [hPhiH] using hPhiData.2.1
    have hPhiSupport : tsupport PhiH.toFun ⊆ Q := by
      simpa [hPhiH, Q] using hPhiData.2.2
    obtain ⟨w, hwcont, hwcell, hwenergy, hwerror⟩ :=
      h z (3 * r) h3r 1 a lam Lam hlam ha (by simpa [Q] using hab)
        PhiH hPhiSmooth hPhiCompact hPhiSupport
    refine ⟨w, ?_, ?_⟩
    · simpa [Q] using hwcont
    · intro k
      have hk := hwcell k
      dsimp at hk
      exact ⟨hk.1, hk.2.1⟩
  obtain ⟨Bcell, Hcell, hBH, hBounds⟩ :=
    hCatalogBounds Phi hPhiMem PhiH hPhiH
  obtain ⟨meshC, hmeshC, hmesh⟩ := hmesh
  choose lam Lam hlam hab using hell
  have hw_exists : ∀ n : ℕ, ∃ w : H10Function Q,
      ContinuousOn w.toH1Function.toFun (closure Q) ∧
      ∀ k : OddGridIndex d (triadicHalf 1),
        IsWeaklyHarmonicOn (A n)
          (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
            Set (SpatialCoordinates d))
          (w.toH1Function.restrict
            (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
            (hcellsub k)) ∧
        HasZeroTraceDifferenceOn
          (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
            Set (SpatialCoordinates d))
          (w.toH1Function.restrict
            (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
            (hcellsub k))
          (PhiH.restrict
            (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
            (hcellsub k)) := by
    intro n
    obtain ⟨w, hwcont, hwcell⟩ :=
      hmesh (aext n) (lam n) (Lam n) (hlam n) (haext n) (by
        intro x hx
        have hx' : x ∈ closure Q := subset_closure hx
        rw [hAeq n x hx']
        exact hab n x hx')
    refine ⟨w, hwcont, ?_⟩
    intro k
    have hk := hwcell k
    have hWsub :
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Set (SpatialCoordinates d)) ⊆ Q := by
      simpa [Q] using hcellsub k
    have heqA : ∀ x ∈
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Set (SpatialCoordinates d)),
        aext n x = A n x := by
      intro x hx
      exact hAeq n x (subset_closure (hWsub hx))
    have hhA : IsWeaklyHarmonicOn (A n)
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Set (SpatialCoordinates d))
        (w.toH1Function.restrict
          (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k)) := by
      intro φ
      change (∫ x in
          (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
            Set (SpatialCoordinates d)),
          vecDot ((A n x) •
            (w.toH1Function.restrict
              (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
              (hcellsub k)).grad x) (φ.grad x)) = 0
      calc
        (∫ x in
            (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
              Set (SpatialCoordinates d)),
            vecDot ((A n x) •
              (w.toH1Function.restrict
                (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
                (hcellsub k)).grad x) (φ.grad x)) =
            ∫ x in
              (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                Set (SpatialCoordinates d)),
              vecDot ((aext n x) •
                (w.toH1Function.restrict
                  (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
                  (hcellsub k)).grad x) (φ.grad x) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem
            (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen.measurableSet]
            with x hx
          rw [heqA x hx]
        _ = 0 := hk.1 φ
    exact ⟨hhA, hk.2⟩
  choose w hwcont hwcell using hw_exists
  let UN : ℕ → H1Function Q := fun n => (w n).toH1Function
  have hUNmem : ∀ n : ℕ, sobolevDataOfH1 (UN n) ∈ S.space := by
    intro n
    rw [hS]
    exact sobolevDataOfH1_mem_killed (w n)
  let UNS : ℕ → S.space := fun n => ⟨sobolevDataOfH1 (UN n), hUNmem n⟩
  have hCellData : ∀ n : ℕ, ∀ k : OddGridIndex d (triadicHalf 1),
      ContinuousOn (UN n).toFun
        (closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))) ∧
      (∀ x ∈ frontier ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
        (UN n).toFun x = Phi x) ∧
      energy (A n)
          ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
            Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))
          ((UN n).restrict
            (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
            (hcellsub k)) ≤ Bcell k ∧
      (∀ x ∈ closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
        ∀ y ∈ closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
          |(UN n).toFun x - (UN n).toFun y| ≤
            Hcell k * dist x y ^ alpha) ∧
      (∀ x ∈ closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
        |(UN n).toFun x| ≤ Hcell k) := by
    intro n k
    let W : Set (SpatialCoordinates d) :=
      (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
        Set (SpatialCoordinates d))
    let u : H1Function W :=
      (UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
        (hcellsub k)
    have hWsub : W ⊆ Q := by
      simpa [W, Q] using hcellsub k
    have hWclosureQ : closure W ⊆ closure Q :=
      closure_mono hWsub
    have hucont : ContinuousOn u.toFun (closure W) := by
      simpa [u] using! (hwcont n).mono hWclosureQ
    have hucell : IsWeaklyHarmonicOn (A n) W u := by
      simpa [u, W] using (hwcell n k).1
    have hutrace : HasZeroTraceDifferenceOn W u
        (PhiH.restrict
          (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k)) := by
      simpa [u, W] using (hwcell n k).2
    have hcell := hBounds n k u hucell hutrace
    obtain ⟨wc, hwccont, hwae, hwholder, hwbound⟩ := hcell.2.2
    have heqOpen : Set.EqOn u.toFun wc W := by
      intro x hx
      exact lane2_eqOn_of_ae_eq_of_continuousOn
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
        (hucont.mono subset_closure) (hwccont.mono subset_closure) hwae x hx
    have heqClosure : Set.EqOn u.toFun wc (closure W) :=
      heqOpen.of_subset_closure hucont hwccont subset_closure (subset_refl _)
    have hWgeom : IsOpenBoundedConvexDomain W := by
      simpa [W, oddGridCell] using
        (lane2_isOpenBoundedConvexDomain_centeredCube
          (oddGridCenter z (3 * r) (triadicHalf 1) k)
          (div_pos h3r (by positivity)))
    have hAcontW : ContinuousOn (A n) (closure W) :=
      (hAcont n).mono hWclosureQ
    have hAboundsW : ∀ x ∈ W, ∃ lam' Lam' : ℝ, 0 < lam' ∧
        lam' ≤ A n x ∧ A n x ≤ Lam' := by
      intro x hx
      exact ⟨lam n, Lam n, hlam n,
        (hab n x (subset_closure (hWsub hx))).1,
        (hab n x (subset_closure (hWsub hx))).2⟩
    have hAboundsW' : ∀ x ∈ W,
        lam n ≤ A n x ∧ A n x ≤ Lam n := by
      intro x hx
      exact hab n x (subset_closure (hWsub hx))
    have hPhiCellSmooth : ContDiff ℝ ∞
        (PhiH.restrict
          (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k)).toFun := by
      simpa [H1Function.restrict, hPhiH] using hPhiData.1
    obtain ⟨v, hvcont, hvae, hvface⟩ :=
      cell_boundary_continuity (d := d) hd
        (oddGridCenter z (3 * r) (triadicHalf 1) k)
        (3 * r / (2 * ((triadicHalf 1 : ℕ) : ℝ) + 1))
        (div_pos h3r (by positivity)) (A n) (lam n)
        (Lam n) (hlam n) hAcontW hAboundsW'
        (PhiH.restrict
          (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k)) u hPhiCellSmooth hucell hutrace
    have hvcont' : ContinuousOn v (closure W) := by
      simpa [W, oddGridCell] using hvcont
    have hvae' : v =ᵐ[volume.restrict W] u.toFun := by
      simpa [W, oddGridCell] using hvae
    have hvface' : ∀ x ∈ frontier W,
        v x = (PhiH.restrict
          (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k)).toFun x := by
      simpa [W, oddGridCell] using hvface
    have heqUvOpen : Set.EqOn u.toFun v W := by
      intro x hx
      exact lane2_eqOn_of_ae_eq_of_continuousOn
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
        (hucont.mono subset_closure) (hvcont'.mono subset_closure)
        hvae'.symm x hx
    have heqUvClosure : Set.EqOn u.toFun v (closure W) :=
      heqUvOpen.of_subset_closure hucont hvcont' subset_closure (subset_refl _)
    have hface : ∀ x ∈ frontier W, (UN n).toFun x = Phi x := by
      intro x hx
      have hux : u.toFun x = v x :=
        heqUvClosure (frontier_subset_closure hx)
      calc
        (UN n).toFun x = u.toFun x := by rfl
        _ = v x := hux
        _ = (PhiH.restrict
            (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
            (hcellsub k)).toFun x := hvface' x hx
        _ = Phi x := by simp [H1Function.restrict, hPhiH]
    refine ⟨hucont, hface, hcell.1, ?_, ?_⟩
    · intro x hx y hy
      have hx' : x ∈ closure W := by simpa [W] using hx
      have hy' : y ∈ closure W := by simpa [W] using hy
      calc
        |(UN n).toFun x - (UN n).toFun y| =
            |u.toFun x - u.toFun y| := by rfl
        _ = |wc x - wc y| := by rw [heqClosure hx', heqClosure hy']
        _ ≤ Hcell k * dist x y ^ alpha := hwholder x hx y hy
    · intro x hx
      have hx' : x ∈ closure W := by simpa [W] using hx
      calc
        |(UN n).toFun x| = |u.toFun x| := by rfl
        _ = |wc x| := by rw [heqClosure hx']
        _ ≤ Hcell k := hwbound x hx
  refine ⟨PhiH, Phiq, UN, UNS, Bcell, Hcell, hPhiH, hPhiq, hBH, ?_, ?_, ?_, ?_⟩
  · intro n
    refine ⟨rfl, ?_, ?_, ?_⟩
    · simpa [UN, Q] using hwcont n
    · intro x hx
      have hxQcl : x ∈ closure Q := by
        simpa [Q] using (frontier_subset_closure hx)
      have hxQcl' : x ∈ closure (centeredCube z (3 * r) h3r :
          Set (SpatialCoordinates d)) := by
        simpa [Q] using hxQcl
      rw [← oddGridCell_closure_iUnion_eq_closure_centeredCube z h3r
        (triadicHalf 1)] at hxQcl'
      obtain ⟨k, hxk⟩ := mem_iUnion.mp hxQcl'
      have hxnotQ : x ∉ Q := by
        intro hx'
        have hxint : x ∈ interior
            (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) := by
          rw [(centeredCube z (3 * r) h3r).isOpen.interior_eq]
          simpa [Q] using hx'
        exact hx.2 hxint
      have hxnotW : x ∉
          (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
            Set (SpatialCoordinates d)) := by
        intro hxW
        exact hxnotQ (hcellsub k hxW)
      have hxfrontW : x ∈ frontier
          (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
            Set (SpatialCoordinates d)) := by
        rw [frontier]
        exact ⟨hxk, fun hxi => hxnotW (interior_subset hxi)⟩
      have hpx : Phi x = 0 := image_eq_zero_of_notMem_tsupport (by
        intro hxt
        exact hxnotQ (hPhiData.2.2 hxt))
      exact (hCellData n k).2.1 x hxfrontW |>.trans hpx
    · intro k
      have hcellk := hCellData n k
      refine ⟨?_, ?_, hcellk.1, hcellk.2.1⟩
      · simpa [UN] using (hwcell n k).1
      · simpa [UN] using (hwcell n k).2
  · intro n k
    exact (hCellData n k).2.2.1
  · intro n k x hx rr hrr hrr1
    have hcell := hBounds n k
      ((UN n).restrict
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
        (hcellsub k))
      (by simpa [UN] using (hwcell n k).1)
      (by simpa [UN] using (hwcell n k).2)
    let W : Set (SpatialCoordinates d) :=
      (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
        Set (SpatialCoordinates d))
    have hgrad : ∀ i : Fin d,
        (((UNS n : SobolevData (centeredCube z (3 * r) h3r)).2 i :
          DomainL2 (centeredCube z (3 * r) h3r)) :
          SpatialCoordinates d → ℝ) =ᵐ[volume.restrict W]
          fun y => ((UN n).restrict
            (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
            (hcellsub k)).grad y i := by
      intro i
      have h0 := sobolevDataOfH1_snd_coeFn (UN n) i
      have hsub : W ⊆ Q := by
        simpa [W, Q] using hcellsub k
      have h1 := ae_restrict_of_ae_restrict_of_subset hsub h0
      simpa [UNS, W] using! h1
    have hden :
        (fun y => ENNReal.ofReal ((A n) y *
          ∑ i : Fin d,
            ((UNS n : SobolevData (centeredCube z (3 * r) h3r)).2 i y) ^ 2)) =ᵐ[
            volume.restrict W]
          (fun y => ENNReal.ofReal ((A n) y *
            ∑ i : Fin d,
              (((UN n).restrict
                (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
                (hcellsub k)).grad y i) ^ 2)) := by
      filter_upwards [ae_all_iff.mpr hgrad] with y hy
      congr 1
      simp_rw [hy]
    rw [withDensity_congr_ae hden]
    simpa [W] using hcell.2.1 x hx rr hrr hrr1
  · intro n k
    refine ⟨?_, ?_⟩
    · exact (hCellData n k).2.2.2.1
    · exact (hCellData n k).2.2.2.2

end SubdiffusiveProcess.Paper

