module

public import SubdiffusiveProcess.Paper.mesh_interpolator
public import SubdiffusiveProcess.Paper.lem_cutoffs
public import SubdiffusiveProcess.VariationalResponses.NativeBridge
public import Mathlib.Topology.MetricSpace.Thickening

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- A mesh interpolant vanishes on any cell separated from the source support.
This is the cutoff-independent part of the compact-support argument. -/
theorem aux_in_represented_finite_mesh_cell_zero
    {d : ℕ} [NeZero d]
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (J : ℕ)
    (δ : ℝ) (hside : R / (3 : ℝ) ^ J < δ)
    (φ : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (raw : SpatialCoordinates d → ℝ) (hrawCont : Continuous raw)
    (lam Lam : ℝ) (hlam : 0 < lam)
    (hrawBounds : ∀ y ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
      lam ≤ raw y ∧ raw y ≤ Lam)
    (w : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hwcont : ContinuousOn w.toFun
      (closure (centeredCube z R hR : Set (SpatialCoordinates d))))
    (κ : OddGridIndex d (triadicHalf J))
    (hwcell : IsWeaklyHarmonicOn raw
      (oddGridCell z R hR (triadicHalf J) κ : Set (SpatialCoordinates d))
      (w.restrict (oddGridCell z R hR (triadicHalf J) κ).isOpen
        (oddGridCell_subset z hR (triadicHalf J) κ)))
    (htrace : HasZeroTraceDifferenceOn
      (oddGridCell z R hR (triadicHalf J) κ : Set (SpatialCoordinates d))
      (w.restrict (oddGridCell z R hR (triadicHalf J) κ).isOpen
        (oddGridCell_subset z hR (triadicHalf J) κ))
      (φ.restrict (oddGridCell z R hR (triadicHalf J) κ).isOpen
        (oddGridCell_subset z hR (triadicHalf J) κ)))
    (x : SpatialCoordinates d)
    (_hx : x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hxCell : x ∈ closure
      (oddGridCell z R hR (triadicHalf J) κ : Set (SpatialCoordinates d)))
    (hxK : x ∉ Metric.cthickening δ (tsupport φ.toFun)) :
    w.toFun x = 0 := by
  classical
  let W : Set (SpatialCoordinates d) :=
    (oddGridCell z R hR (triadicHalf J) κ : Set (SpatialCoordinates d))
  let c : SpatialCoordinates d := oddGridCenter z R (triadicHalf J) κ
  let ρ : ℝ := R / (2 * (triadicHalf J : ℝ) + 1) / 2
  have hWball : W = Metric.ball c ρ := rfl
  have hxcl : x ∈ closure W := by simpa [W] using hxCell
  have hdisj : Disjoint (closure W) (tsupport φ.toFun) := by
    apply Set.disjoint_left.mpr
    intro y hyW hyK
    have hyW' : y ∈ closure (Metric.ball c ρ) := by
      rw [← hWball]
      exact hyW
    have hyclosed := Metric.closure_ball_subset_closedBall hyW'
    have hyball : dist y c ≤ ρ := Metric.mem_closedBall.mp hyclosed
    have hxW' : x ∈ closure (Metric.ball c ρ) := by
      rw [← hWball]
      exact hxcl
    have hxclosed := Metric.closure_ball_subset_closedBall hxW'
    have hxball : dist x c ≤ ρ := Metric.mem_closedBall.mp hxclosed
    have hdist : dist x y ≤ R / (3 : ℝ) ^ J := by
      calc
        dist x y ≤ dist x c + dist c y := dist_triangle _ _ _
        _ ≤ ρ + ρ := add_le_add hxball (by simpa [dist_comm] using hyball)
        _ = R / (3 : ℝ) ^ J := by
          dsimp [ρ]
          rw [triadic_denominator]
          ring
    have hxK' : x ∈ Metric.cthickening δ (tsupport φ.toFun) :=
      Metric.mem_cthickening_of_dist_le x y δ (tsupport φ.toFun) hyK
        (hdist.trans (le_of_lt hside))
    exact hxK hxK'
  have hWdom : IsOpenBoundedConvexDomain W := by
    change IsOpenBoundedConvexDomain
      (oddGridCell z R hR (triadicHalf J) κ : Set (SpatialCoordinates d))
    exact aux_lem_cutoffs_cell_dom z hR (triadicHalf J) κ
  let wk : H1Function W :=
    w.restrict (oddGridCell z R hR (triadicHalf J) κ).isOpen
      (oddGridCell_subset z hR (triadicHalf J) κ)
  let φk : H1Function W :=
    φ.restrict (oddGridCell z R hR (triadicHalf J) κ).isOpen
      (oddGridCell_subset z hR (triadicHalf J) κ)
  have hφzero : ∀ y ∈ W, φk.toFun y = 0 := by
    intro y hy
    have hyK : y ∉ tsupport φ.toFun := by
      intro hyK
      exact (Set.disjoint_left.mp hdisj) (subset_closure hy) hyK
    exact image_eq_zero_of_notMem_tsupport hyK
  have hwkcont : ContinuousOn wk.toFun (closure W) := by
    change ContinuousOn w.toFun (closure W)
    exact hwcont.mono (closure_mono (oddGridCell_subset z hR (triadicHalf J) κ))
  have hzero := aux_lem_cutoffs_cc_constant_cell W raw lam Lam hWdom hlam
    hrawCont (fun y hy => hrawBounds y (oddGridCell_subset z hR (triadicHalf J) κ hy))
    φk wk 0 hφzero (by simpa [wk, W] using hwcell)
    (by simpa [wk, φk, W] using htrace) hwkcont
  exact hzero x (by simpa [W] using hxcl)

/-- Algebraic sup-bound step used after the mesh interpolation estimate. -/
theorem aux_in_represented_finite_mesh_sup_bound
    (u ψ Bphi Cphi side : ℝ)
    (herr : |u - ψ| ≤ Cphi * side) (hψ : |ψ| ≤ Bphi) :
    |u| ≤ Bphi + Cphi * side := by
  calc
    |u| = |(u - ψ) + ψ| := by congr 1; ring
    _ ≤ |u - ψ| + |ψ| := abs_add_le _ _
    _ ≤ Cphi * side + Bphi := add_le_add herr hψ
    _ = Bphi + Cphi * side := add_comm _ _

/-- Cellwise Hölder control and a sup bound give the mesh-wide Holder supplier. -/
theorem aux_in_represented_finite_mesh_global_holder
    {d : ℕ} [NeZero d]
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (m : ℕ)
    (alpha : ℝ) (halpha : 0 < alpha) (B H : ℝ)
    (hB : 0 ≤ B) (hH : 0 ≤ H)
    (f : SpatialCoordinates d → ℝ)
    (hsup : ∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
      |f x| ≤ B)
    (hcell : ∀ κ : OddGridIndex d m,
      ∀ x ∈ closure (oddGridCell z R hR m κ : Set (SpatialCoordinates d)),
      ∀ y ∈ closure (oddGridCell z R hR m κ : Set (SpatialCoordinates d)),
        |f x - f y| ≤ H *
          (Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2)) ^ alpha) :
    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (closure (centeredCube z R hR : Set (SpatialCoordinates d))) f ∧
      _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha (closure (centeredCube z R hR : Set (SpatialCoordinates d))) f ≤
        B + (d : ℝ) * (2 * H + 2 * B * (R / (2 * (m : ℝ) + 1)) ^ (-alpha)) := by
  let Hglobal : ℝ := (d : ℝ) *
    (2 * H + 2 * B * (R / (2 * (m : ℝ) + 1)) ^ (-alpha))
  have hHglobal : 0 ≤ Hglobal := by
    dsimp [Hglobal]
    have hmeshpos : 0 < R / (2 * (m : ℝ) + 1) := by positivity
    positivity
  have hpair : ∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
      ∀ y ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
        |f x - f y| ≤ Hglobal *
          (Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2)) ^ alpha := by
    intro x hx y hy
    have hglue := aux_lem_cutoffs_holder_glue z R hR m halpha hB hH f hsup hcell
    change |f x - f y| ≤
      (d : ℝ) * (2 * H + 2 * B * (R / (2 * (m : ℝ) + 1)) ^ (-alpha)) *
        (Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2)) ^ alpha
    exact hglue x hx y hy
  have hholder := aux_lem_cutoffs_holder_of_pair_bound halpha hB hHglobal hsup hpair
  refine ⟨hholder.1, ?_⟩
  simpa [Hglobal, add_comm, add_left_comm, add_assoc] using hholder.2

/-- Finite-grid energy is bounded by summing the represented cell estimates. -/
theorem aux_in_represented_finite_mesh_energy_bound
    {d : ℕ} [NeZero d]
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (J : ℕ)
    (raw : SpatialCoordinates d → ℝ)
    (φ : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (w : H10Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (Ecell : OddGridIndex d (triadicHalf J) → ℝ)
    (hCellBound : ∀ (κ : OddGridIndex d (triadicHalf J))
      (u : H1Function (oddGridCell z R hR (triadicHalf J) κ : Set (SpatialCoordinates d))),
      IsWeaklyHarmonicOn (raw)
        (oddGridCell z R hR (triadicHalf J) κ : Set (SpatialCoordinates d)) u →
      HasZeroTraceDifferenceOn
        (oddGridCell z R hR (triadicHalf J) κ : Set (SpatialCoordinates d)) u
        (φ.restrict (oddGridCell z R hR (triadicHalf J) κ).isOpen
          (oddGridCell_subset z hR (triadicHalf J) κ)) →
      ContinuousOn u.toFun
        (closure (oddGridCell z R hR (triadicHalf J) κ : Set (SpatialCoordinates d))) →
      energy raw
        (oddGridCell z R hR (triadicHalf J) κ : Set (SpatialCoordinates d)) u ≤ Ecell κ)
    (hwcont : ContinuousOn w.toH1Function.toFun
      (closure (centeredCube z R hR : Set (SpatialCoordinates d))))
    (hwcell : ∀ κ : OddGridIndex d (triadicHalf J),
      let W := oddGridCell z R hR (triadicHalf J) κ
      let hW : (W : Set (SpatialCoordinates d)) ⊆
        (centeredCube z R hR : Set (SpatialCoordinates d)) :=
          oddGridCell_subset z hR (triadicHalf J) κ
      let wk : H1Function (W : Set (SpatialCoordinates d)) :=
        w.toH1Function.restrict W.isOpen hW
      let φk : H1Function (W : Set (SpatialCoordinates d)) := φ.restrict W.isOpen hW
      IsWeaklyHarmonicOn raw (W : Set (SpatialCoordinates d)) wk ∧
      HasZeroTraceDifferenceOn (W : Set (SpatialCoordinates d)) wk φk ∧
      energy raw (W : Set (SpatialCoordinates d)) wk =
        sInf {e : ℝ | ∃ u : H1Function (W : Set (SpatialCoordinates d)),
          HasZeroTraceDifferenceOn (W : Set (SpatialCoordinates d)) u φk ∧
          e = energy raw (W : Set (SpatialCoordinates d)) u})
    (hsum : energy raw (centeredCube z R hR : Set (SpatialCoordinates d))
        w.toH1Function =
      ∑ κ : OddGridIndex d (triadicHalf J),
        let W := oddGridCell z R hR (triadicHalf J) κ
        let hW : (W : Set (SpatialCoordinates d)) ⊆
          (centeredCube z R hR : Set (SpatialCoordinates d)) :=
            oddGridCell_subset z hR (triadicHalf J) κ
        let φk : H1Function (W : Set (SpatialCoordinates d)) := φ.restrict W.isOpen hW
        sInf {e : ℝ | ∃ u : H1Function (W : Set (SpatialCoordinates d)),
          HasZeroTraceDifferenceOn (W : Set (SpatialCoordinates d)) u φk ∧
          e = energy raw (W : Set (SpatialCoordinates d)) u}) :
    energy raw (centeredCube z R hR : Set (SpatialCoordinates d)) w.toH1Function ≤
      ∑ κ : OddGridIndex d (triadicHalf J), Ecell κ := by
  rw [hsum]
  apply Finset.sum_le_sum
  intro κ hκ
  let W : Set (SpatialCoordinates d) :=
    (oddGridCell z R hR (triadicHalf J) κ : Set (SpatialCoordinates d))
  let wk : H1Function W := w.toH1Function.restrict
    (oddGridCell z R hR (triadicHalf J) κ).isOpen
    (oddGridCell_subset z hR (triadicHalf J) κ)
  have hmin := (hwcell κ).2.2
  have hbound := hCellBound κ wk
    (by simpa [wk, W] using (hwcell κ).1)
    (by simpa [wk, W] using (hwcell κ).2.1)
    (by simpa [wk, W] using!
      (hwcont.mono (closure_mono (oddGridCell_subset z hR (triadicHalf J) κ))))
  calc
    sInf {e : ℝ | ∃ u : H1Function W,
        HasZeroTraceDifferenceOn W u (φ.restrict
          (oddGridCell z R hR (triadicHalf J) κ).isOpen
          (oddGridCell_subset z hR (triadicHalf J) κ)) ∧
        e = energy raw W u} = energy raw W wk := by
          simpa [W, wk] using hmin.symm
    _ ≤ Ecell κ := hbound

/-- Build the smooth-data interpolants and their common-support/error properties.
This stage is independent of the represented cell energy and Holder constants. -/
theorem aux_in_represented_bounds_seq_finite_mesh_preprocess
    {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (raw : ℕ → SpatialCoordinates d → ℝ)
    (hrawCont : ∀ n, Continuous (raw n))
    (hrawBounds : ∀ n, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
        lam ≤ raw n x ∧ raw n x ≤ Lam)
    (φ : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hφsmooth : ContDiff ℝ ∞ φ.toFun)
    (hφcompact : HasCompactSupport φ.toFun)
    (hφsupport : tsupport φ.toFun ⊆
      (centeredCube z R hR : Set (SpatialCoordinates d))) :
    ∃ Cphi : ℝ, 0 ≤ Cphi ∧ ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∃ w : ℕ → H10Function (centeredCube z R hR : Set (SpatialCoordinates d)),
      ∃ vcN : ℕ → SpatialCoordinates d → ℝ,
      ∃ Kset : Set (SpatialCoordinates d),
        IsCompact Kset ∧
        Kset ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
        (∀ n : ℕ, vcN n = (w n).toH1Function.toFun) ∧
        ∀ n : ℕ,
          ContinuousOn (vcN n)
            (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
          (∀ κ : OddGridIndex d (triadicHalf k),
            let W := oddGridCell z R hR (triadicHalf k) κ
            let hW : (W : Set (SpatialCoordinates d)) ⊆
              (centeredCube z R hR : Set (SpatialCoordinates d)) :=
                oddGridCell_subset z hR (triadicHalf k) κ
            let wk : H1Function (W : Set (SpatialCoordinates d)) :=
              (w n).toH1Function.restrict W.isOpen hW
            let φk : H1Function (W : Set (SpatialCoordinates d)) :=
              φ.restrict W.isOpen hW
            IsWeaklyHarmonicOn (raw n) (W : Set (SpatialCoordinates d)) wk ∧
            HasZeroTraceDifferenceOn (W : Set (SpatialCoordinates d)) wk φk ∧
            energy (raw n) (W : Set (SpatialCoordinates d)) wk =
              sInf {e : ℝ | ∃ u : H1Function (W : Set (SpatialCoordinates d)),
                HasZeroTraceDifferenceOn (W : Set (SpatialCoordinates d)) u φk ∧
                e = energy (raw n) (W : Set (SpatialCoordinates d)) u}) ∧
          (energy (raw n) (centeredCube z R hR : Set (SpatialCoordinates d))
              (w n).toH1Function =
            ∑ κ : OddGridIndex d (triadicHalf k),
              let W := oddGridCell z R hR (triadicHalf k) κ
              let hW : (W : Set (SpatialCoordinates d)) ⊆
                (centeredCube z R hR : Set (SpatialCoordinates d)) :=
                  oddGridCell_subset z hR (triadicHalf k) κ
              let φk : H1Function (W : Set (SpatialCoordinates d)) :=
                φ.restrict W.isOpen hW
              sInf {e : ℝ | ∃ u : H1Function (W : Set (SpatialCoordinates d)),
                HasZeroTraceDifferenceOn (W : Set (SpatialCoordinates d)) u φk ∧
                e = energy (raw n) (W : Set (SpatialCoordinates d)) u}) ∧
          (∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) \ Kset,
            vcN n x = 0) ∧
          ∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
            |vcN n x - φ.toFun x| ≤ Cphi * (R / (3 : ℝ) ^ k) := by
  classical
  have hQopen : IsOpen (centeredCube z R hR : Set (SpatialCoordinates d)) :=
    (centeredCube z R hR).isOpen
  have hQcompact : IsCompact
      (closure (centeredCube z R hR : Set (SpatialCoordinates d))) :=
    isCompact_closure_centeredCube z hR
  have hKcompact : IsCompact (tsupport φ.toFun) :=
    hQcompact.of_isClosed_subset (isClosed_tsupport φ.toFun)
      (hφsupport.trans subset_closure)
  obtain ⟨δ, hδ, hδQ⟩ := hKcompact.exists_cthickening_subset_open hQopen hφsupport
  let Kset : Set (SpatialCoordinates d) := Metric.cthickening δ (tsupport φ.toFun)
  have hKsetCompact : IsCompact Kset := by
    dsimp [Kset]
    exact hKcompact.cthickening
  have hKsetSub : Kset ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) := by
    dsimp [Kset]
    exact hδQ
  have hside_tendsto : Tendsto (fun k : ℕ => R * (1 / 3 : ℝ) ^ k)
      atTop (𝓝 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 : ℝ) / 3 < 1)
    simpa using hp.const_mul R
  have hside_eventually : ∀ᶠ k : ℕ in atTop, R * (1 / 3 : ℝ) ^ k < δ :=
    hside_tendsto.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.1 hside_eventually
  obtain ⟨Cmesh, hCmesh, hmesh⟩ := mesh_interpolator (d := d) hd
  let gradSup : ℝ := sSup ((fun x => ‖fderiv ℝ φ.toFun x‖) ''
    closure (centeredCube z R hR : Set (SpatialCoordinates d)))
  have hgradSup : 0 ≤ gradSup := by
    dsimp [gradSup]
    apply Real.sSup_nonneg
    rintro y ⟨x, hx, rfl⟩
    exact norm_nonneg _
  let Cphi : ℝ := Cmesh * gradSup
  have hCphi : 0 ≤ Cphi := mul_nonneg hCmesh hgradSup
  refine ⟨Cphi, hCphi, k0, ?_⟩
  intro k hkk
  have hside : R / (3 : ℝ) ^ k < δ := by
    have hlt := hk0 k hkk
    have hpow : (1 / 3 : ℝ) ^ k = 1 / (3 : ℝ) ^ k := by
      simp [one_div, inv_pow]
    rw [hpow] at hlt
    simpa [div_eq_mul_inv, mul_comm] using hlt
  let m : ℕ := triadicHalf k
  have hbounds : ∀ n : ℕ, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
        lam ≤ raw n x ∧ raw n x ≤ Lam := hrawBounds
  choose lam Lam hlam hab using hbounds
  have hwExists : ∀ n : ℕ, ∃ w : H10Function
      (centeredCube z R hR : Set (SpatialCoordinates d)),
      ContinuousOn w.toH1Function.toFun
        (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
      (∀ κ : OddGridIndex d m,
        let W := oddGridCell z R hR m κ
        let hW : (W : Set (SpatialCoordinates d)) ⊆
          (centeredCube z R hR : Set (SpatialCoordinates d)) := oddGridCell_subset z hR m κ
        let wk : H1Function (W : Set (SpatialCoordinates d)) :=
          w.toH1Function.restrict W.isOpen hW
        let φk : H1Function (W : Set (SpatialCoordinates d)) := φ.restrict W.isOpen hW
        IsWeaklyHarmonicOn (raw n) (W : Set (SpatialCoordinates d)) wk ∧
        HasZeroTraceDifferenceOn (W : Set (SpatialCoordinates d)) wk φk ∧
        energy (raw n) (W : Set (SpatialCoordinates d)) wk =
          sInf {e : ℝ | ∃ u : H1Function (W : Set (SpatialCoordinates d)),
            HasZeroTraceDifferenceOn (W : Set (SpatialCoordinates d)) u φk ∧
            e = energy (raw n) (W : Set (SpatialCoordinates d)) u}) ∧
      (energy (raw n) (centeredCube z R hR : Set (SpatialCoordinates d))
          w.toH1Function =
        ∑ κ : OddGridIndex d m,
          let W := oddGridCell z R hR m κ
          let hW : (W : Set (SpatialCoordinates d)) ⊆
            (centeredCube z R hR : Set (SpatialCoordinates d)) := oddGridCell_subset z hR m κ
          let φk : H1Function (W : Set (SpatialCoordinates d)) := φ.restrict W.isOpen hW
          sInf {e : ℝ | ∃ u : H1Function (W : Set (SpatialCoordinates d)),
            HasZeroTraceDifferenceOn (W : Set (SpatialCoordinates d)) u φk ∧
            e = energy (raw n) (W : Set (SpatialCoordinates d)) u}) ∧
      ∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
        |w.toH1Function.toFun x - φ.toFun x| ≤ Cmesh *
          (R / (3 : ℝ) ^ k) * gradSup := by
    intro n
    obtain ⟨w, hwcont, hwcell, hwenergy, hwerr⟩ := hmesh z R hR k (raw n)
      (lam n) (Lam n) (hlam n) (hrawCont n) (hab n) φ hφsmooth hφcompact hφsupport
    exact ⟨w, by simpa using hwcont, by simpa [m] using hwcell,
      by simpa [m] using hwenergy, by simpa [gradSup] using hwerr⟩
  choose w hwcont hwcell hwenergy hwerr using hwExists
  let vcN : ℕ → SpatialCoordinates d → ℝ := fun n => (w n).toH1Function.toFun
  have herrorClosure : ∀ n x, x ∈ closure
      (centeredCube z R hR : Set (SpatialCoordinates d)) →
      |vcN n x - φ.toFun x| ≤ Cphi * (R / (3 : ℝ) ^ k) := by
    intro n x hx
    have hcontErr : ContinuousOn
        (fun y => |(w n).toH1Function.toFun y - φ.toFun y|)
        (closure (centeredCube z R hR : Set (SpatialCoordinates d))) :=
      ((hwcont n).sub (hφsmooth.continuous.continuousOn.mono subset_closure)).abs
    have hle := ContinuousWithinAt.closure_le hx
      ((hcontErr x hx).mono subset_closure) continuousWithinAt_const
      (fun y hy => by
        simpa [vcN, Cphi, gradSup, mul_assoc, mul_left_comm, mul_comm] using
          (hwerr n y hy))
    calc
      |vcN n x - φ.toFun x| ≤ Cmesh * (R / (3 : ℝ) ^ k) * gradSup := by
        simpa [vcN, gradSup, mul_assoc] using hle
      _ = Cphi * (R / (3 : ℝ) ^ k) := by
        dsimp [Cphi]
        ring
  have hzero : ∀ n, ∀ x ∈
      (centeredCube z R hR : Set (SpatialCoordinates d)) \ Kset, vcN n x = 0 := by
    intro n x hx
    have hxcl : x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)) :=
      subset_closure hx.1
    rw [← oddGridCell_closure_iUnion_eq_closure_centeredCube z hR m] at hxcl
    obtain ⟨κ, hxκ⟩ := mem_iUnion.mp hxcl
    have hz : (w n).toH1Function.toFun x = 0 :=
      aux_in_represented_finite_mesh_cell_zero z R hR k δ hside φ (raw n)
        (hrawCont n) (lam n) (Lam n) (hlam n) (hab n)
        (w n).toH1Function (hwcont n) κ (hwcell n κ).1 (hwcell n κ).2.1
        x hx.1 hxκ (by simpa [Kset] using hx.2)
    rw [show vcN n = (w n).toH1Function.toFun by rfl]
    exact hz
  refine ⟨w, vcN, Kset, hKsetCompact, hKsetSub,
    (fun n => by funext x; rfl), ?_⟩
  intro n
  refine ⟨by simpa [vcN] using hwcont n, hwcell n, hwenergy n, hzero n, ?_⟩
  intro x hx
  exact herrorClosure n x hx

/-- Construct the finite-mesh field used in `in_represented_bounds_seq` from
the *cellwise represented estimates*.  `hCell` is exactly the energy and
Hölder output of `aux_lem_cutoffs_rep_plateau_cell`, with its irrelevant growth
clause projected away.  In particular it contains no interpolant, no global
Holder bound, no compact-support conclusion, and no approximation estimate.
The latter four conclusions are constructed here from the frozen harmonic
mesh interpolator, the maximum principle on constant cells, and the finite
mesh Holder-gluing lemma. -/
theorem aux_in_represented_bounds_seq_finite_mesh_from_cell_bounds
    {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (hS : S.space = killedSobolevGraph (centeredCube z R hR))
    (a : ℕ → PositiveCoefficient (centeredCube z R hR))
    (raw : ℕ → SpatialCoordinates d → ℝ)
    (hrawCont : ∀ n, Continuous (raw n))
    (hrawBounds : ∀ n, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
        lam ≤ raw n x ∧ raw n x ≤ Lam)
    (hAC : ∀ n, (a n).val =ᵐ[volume.restrict
      (centeredCube z R hR : Set (SpatialCoordinates d))] raw n)
    (φ : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hφsmooth : ContDiff ℝ ∞ φ.toFun)
    (hφcompact : HasCompactSupport φ.toFun)
    (hφsupport : tsupport φ.toFun ⊆
      (centeredCube z R hR : Set (SpatialCoordinates d)))
    (alpha : ℝ) (halpha : 0 < alpha)
    (hCell : ∀ (J : ℕ) (κ : OddGridIndex d (triadicHalf J)),
      ∃ E H : ℝ, 0 ≤ E ∧ 0 ≤ H ∧
        ∀ (n : ℕ) (w : H1Function
          (oddGridCell z R hR (triadicHalf J) κ : Set (SpatialCoordinates d))),
          IsWeaklyHarmonicOn (raw n)
            (oddGridCell z R hR (triadicHalf J) κ : Set (SpatialCoordinates d)) w →
          HasZeroTraceDifferenceOn
            (oddGridCell z R hR (triadicHalf J) κ : Set (SpatialCoordinates d)) w
            (φ.restrict (oddGridCell z R hR (triadicHalf J) κ).isOpen
              (oddGridCell_subset z hR (triadicHalf J) κ)) →
          ContinuousOn w.toFun
            (closure (oddGridCell z R hR (triadicHalf J) κ : Set (SpatialCoordinates d))) →
          energy (raw n)
              (oddGridCell z R hR (triadicHalf J) κ : Set (SpatialCoordinates d)) w ≤ E ∧
          ∀ x ∈ closure (oddGridCell z R hR (triadicHalf J) κ : Set (SpatialCoordinates d)),
            ∀ y ∈ closure (oddGridCell z R hR (triadicHalf J) κ : Set (SpatialCoordinates d)),
              |w.toFun x - w.toFun y| ≤
                H * (Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2)) ^ alpha) :
    ∃ Cphi : ℝ, 0 ≤ Cphi ∧ ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∃ vN : ℕ → S.space, ∃ vcN : ℕ → SpatialCoordinates d → ℝ,
      ∃ Kset : Set (SpatialCoordinates d),
        IsCompact Kset ∧
        Kset ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
        ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ,
          (vN n).val.1 =ᵐ[volume.restrict
            (centeredCube z R hR : Set (SpatialCoordinates d))] vcN n ∧
          ContinuousOn (vcN n)
            (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
          (∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) \ Kset,
            vcN n x = 0) ∧
          _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
            (closure (centeredCube z R hR : Set (SpatialCoordinates d))) (vcN n) ∧
          _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
            (closure (centeredCube z R hR : Set (SpatialCoordinates d))) (vcN n) ≤ M ∧
          responseForm S (a n) (vN n) (vN n) ≤ M ∧
          ∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
            |vcN n x - φ.toFun x| ≤ Cphi * (R / (3 : ℝ) ^ k) := by
  classical
  obtain ⟨Cphi, hCphi, k0, hpre⟩ :=
    aux_in_represented_bounds_seq_finite_mesh_preprocess hd z R hR raw
      hrawCont hrawBounds φ hφsmooth hφcompact hφsupport
  refine ⟨Cphi, hCphi, k0, ?_⟩
  intro k hk
  obtain ⟨w, vcN, Kset, hKcompact, hKsubset, hvc, hmeshData⟩ := hpre k hk
  let Q : Set (SpatialCoordinates d) :=
    (centeredCube z R hR : Set (SpatialCoordinates d))
  let m : ℕ := triadicHalf k
  choose Ecell Hcell hEcell hHcell hCellBound using
    (fun κ : OddGridIndex d (triadicHalf k) => hCell k κ)
  let vN : ℕ → S.space := fun n =>
    ⟨sobolevDataOfH1 (w n).toH1Function, by
      rw [hS]
      exact sobolevDataOfH1_mem_killed (w n)⟩
  have hQcompact : IsCompact (closure Q) := by
    dsimp [Q]
    exact isCompact_closure_centeredCube z hR
  have hphiBounded : BddAbove {v : ℝ | ∃ x ∈ closure Q, v = |φ.toFun x|} := by
    have himage : {v : ℝ | ∃ x ∈ closure Q, v = |φ.toFun x|} =
        (fun x => |φ.toFun x|) '' closure Q := by
      ext v
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
    rw [himage]
    exact hQcompact.bddAbove_image
      ((hφsmooth.continuous).abs.continuousOn)
  let Bphi : ℝ := sSup {v : ℝ | ∃ x ∈ closure Q, v = |φ.toFun x|}
  have hBphi : 0 ≤ Bphi := by
    dsimp [Bphi]
    apply Real.sSup_nonneg
    rintro y ⟨x, hx, rfl⟩
    exact abs_nonneg _
  have hphiAbs : ∀ x ∈ closure Q, |φ.toFun x| ≤ Bphi := by
    intro x hx
    apply le_csSup hphiBounded
    exact ⟨x, hx, rfl⟩
  refine ⟨vN, vcN, Kset, hKcompact, hKsubset, ?_⟩
  let side : ℝ := R / (3 : ℝ) ^ k
  let Bglobal : ℝ := Bphi + Cphi * side
  let Htotal : ℝ := ∑ κ : OddGridIndex d m, Hcell κ
  let Hglobal : ℝ := (d : ℝ) *
    (2 * Htotal + 2 * Bglobal * (R / (2 * (m : ℝ) + 1)) ^ (-alpha))
  let Eglobal : ℝ := ∑ κ : OddGridIndex d m, Ecell κ
  have hBglobal : 0 ≤ Bglobal := by
    dsimp [Bglobal]
    positivity
  have hHtotal : 0 ≤ Htotal := by
    dsimp [Htotal]
    exact Finset.sum_nonneg fun κ hκ => hHcell κ
  have hHglobal : 0 ≤ Hglobal := by
    dsimp [Hglobal]
    have hmeshpos : 0 < R / (2 * (m : ℝ) + 1) := by positivity
    positivity
  have hEglobal : 0 ≤ Eglobal := by
    dsimp [Eglobal]
    exact Finset.sum_nonneg fun κ hκ => hEcell κ
  have hM : 0 ≤ max Eglobal (Bglobal + Hglobal) :=
    (add_nonneg hBglobal hHglobal).trans (le_max_right _ _)
  refine ⟨max Eglobal (Bglobal + Hglobal), hM, ?_⟩
  intro n
  obtain ⟨hwcont, hwcell, hwenergy, hzero, herr⟩ := hmeshData n
  have hwcontFun : ContinuousOn (w n).toH1Function.toFun
      (closure (centeredCube z R hR : Set (SpatialCoordinates d))) := by
    rw [← hvc n]
    exact hwcont
  have hlocalPair : ∀ κ : OddGridIndex d m,
      ∀ x ∈ closure (oddGridCell z R hR m κ : Set (SpatialCoordinates d)),
      ∀ y ∈ closure (oddGridCell z R hR m κ : Set (SpatialCoordinates d)),
        |vcN n x - vcN n y| ≤ Htotal *
          (Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2)) ^ alpha := by
    intro κ x hx y hy
    have hloc := (hCellBound κ n
      ((w n).toH1Function.restrict (oddGridCell z R hR m κ).isOpen
        (oddGridCell_subset z hR m κ))
      ((hwcell κ).1)
      ((hwcell κ).2.1)
      (hwcontFun.mono (closure_mono (oddGridCell_subset z hR m κ)))).2 x hx y hy
    have hHle : Hcell κ ≤ Htotal := by
      dsimp [Htotal]
      exact Finset.single_le_sum (fun κ' hκ' => hHcell κ') (Finset.mem_univ κ)
    rw [hvc n]
    exact hloc.trans (mul_le_mul_of_nonneg_right hHle
      (Real.rpow_nonneg (Real.sqrt_nonneg _) _))
  have hsup : ∀ x ∈ closure Q, |vcN n x| ≤ Bglobal := by
    intro x hx
    have hphi := hphiAbs x hx
    have herrnx := herr x hx
    change |vcN n x - φ.toFun x| ≤ Cphi * side at herrnx
    have hs := aux_in_represented_finite_mesh_sup_bound
      (vcN n x) (φ.toFun x) Bphi Cphi side herrnx hphi
    change |vcN n x| ≤ Bphi + Cphi * side
    exact hs
  have hholder := aux_in_represented_finite_mesh_global_holder
    z R hR m alpha halpha Bglobal Htotal hBglobal hHtotal (vcN n) hsup hlocalPair
  have hMholder : _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha (closure Q) (vcN n) ≤ Bglobal + Hglobal :=
    hholder.2
  have henergyRaw := aux_in_represented_finite_mesh_energy_bound z R hR k
    (raw n) φ (w n) Ecell
    (fun κ u hu htrace hcont =>
      (hCellBound κ n u hu htrace hcont).1)
    hwcontFun hwcell hwenergy
  have henergy : responseForm S (a n) (vN n) (vN n) ≤ Eglobal := by
    rw [aux_lem_cutoffs_resp_energy z hR S (a n) (raw n) (hAC n)
      (w n).toH1Function (vN n) rfl]
    change energy (raw n) Q (w n).toH1Function ≤
      ∑ κ : OddGridIndex d m, Ecell κ
    exact henergyRaw
  refine ⟨?_, hwcont, hzero, hholder.1, hMholder.trans (le_max_right _ _),
    henergy.trans (le_max_left _ _), herr⟩
  rw [hvc n]
  exact sobolevDataOfH1_fst_coeFn (w n).toH1Function

/-- Exact catalogue-shaped `_hFiniteMesh` supplier. The explicit `hCell` input
is the projection of `aux_lem_cutoffs_rep_plateau_cell` for the represented
smooth trace; it contains only the represented energy and local Holder bounds. -/
theorem in_represented_bounds_seq_finite_mesh
    {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (hS : S.space = killedSobolevGraph (centeredCube z R hR))
    (a : ℕ → PositiveCoefficient (centeredCube z R hR))
    (raw : ℕ → SpatialCoordinates d → ℝ)
    (hrawCont : ∀ n, Continuous (raw n))
    (hrawBounds : ∀ n, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
        lam ≤ raw n x ∧ raw n x ≤ Lam)
    (hAC : ∀ n, (a n).val =ᵐ[volume.restrict
      (centeredCube z R hR : Set (SpatialCoordinates d))] raw n)
    (D : Submodule ℚ (DomainL2 (centeredCube z R hR)))
    (phi : D → H1Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hPhi : ∀ f : D,
      ContDiff ℝ ∞ (phi f).toFun ∧
      HasCompactSupport (phi f).toFun ∧
      tsupport (phi f).toFun ⊆
        (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
      (sobolevDataOfH1 (phi f)).1 = f.val)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hCell : ∀ (f : D) (J : ℕ) (κ : OddGridIndex d (triadicHalf J)),
      ∃ E H : ℝ, 0 ≤ E ∧ 0 ≤ H ∧
        ∀ (n : ℕ) (w : H1Function
          (oddGridCell z R hR (triadicHalf J) κ : Set (SpatialCoordinates d))),
          IsWeaklyHarmonicOn (raw n)
            (oddGridCell z R hR (triadicHalf J) κ : Set (SpatialCoordinates d)) w →
          HasZeroTraceDifferenceOn
            (oddGridCell z R hR (triadicHalf J) κ : Set (SpatialCoordinates d)) w
            ((phi f).restrict (oddGridCell z R hR (triadicHalf J) κ).isOpen
              (oddGridCell_subset z hR (triadicHalf J) κ)) →
          ContinuousOn w.toFun
            (closure (oddGridCell z R hR (triadicHalf J) κ : Set (SpatialCoordinates d))) →
          energy (raw n)
              (oddGridCell z R hR (triadicHalf J) κ : Set (SpatialCoordinates d)) w ≤ E ∧
          ∀ x ∈ closure (oddGridCell z R hR (triadicHalf J) κ : Set (SpatialCoordinates d)),
            ∀ y ∈ closure (oddGridCell z R hR (triadicHalf J) κ : Set (SpatialCoordinates d)),
              |w.toFun x - w.toFun y| ≤
                H * (Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2)) ^ alpha) :
    ∀ f : D, ∃ Cphi : ℝ, 0 ≤ Cphi ∧ ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∃ vN : ℕ → S.space, ∃ vcN : ℕ → SpatialCoordinates d → ℝ,
      ∃ Kset : Set (SpatialCoordinates d),
        IsCompact Kset ∧
        Kset ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
        ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ,
          (vN n).val.1 =ᵐ[volume.restrict
            (centeredCube z R hR : Set (SpatialCoordinates d))] vcN n ∧
          ContinuousOn (vcN n)
            (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
          (∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) \ Kset,
            vcN n x = 0) ∧
          _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
            (closure (centeredCube z R hR : Set (SpatialCoordinates d))) (vcN n) ∧
          _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
            (closure (centeredCube z R hR : Set (SpatialCoordinates d))) (vcN n) ≤ M ∧
          responseForm S (a n) (vN n) (vN n) ≤ M ∧
          ∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
            |vcN n x - (phi f).toFun x| ≤ Cphi * (R / (3 : ℝ) ^ k) := by
  intro f
  obtain ⟨hφsmooth, hφcompact, hφsupport, _hφdata⟩ := hPhi f
  exact aux_in_represented_bounds_seq_finite_mesh_from_cell_bounds
    hd z R hR S hS a raw hrawCont hrawBounds hAC (phi f)
    hφsmooth hφcompact hφsupport alpha halpha (hCell f)

end SubdiffusiveProcess.Paper




end
