module

public import SubdiffusiveProcess.Paper.conv_represented_estimates
public import SubdiffusiveProcess.Paper.conv_represented_sequence
public import SubdiffusiveProcess.Paper.conv_catalog_cutoffs
public import SubdiffusiveProcess.Paper.mesh_interpolator
public import SubdiffusiveProcess.Paper.mesh_gluing
public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Paper.prop_growth
public import SubdiffusiveProcess.VariationalResponses.MeshGluing
public import SubdiffusiveProcess.VariationalResponses.NativeBridge
public import SubdiffusiveProcess.VariationalResponses.ResponseMarkov
public import SubdiffusiveProcess.Main.CubeFractionalL2Norm
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6MeasurableMaxPrinciple
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.Corrector
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.MetricSpace.Thickening
public import SubdiffusiveProcess.MultiplicativeChaos.TriadicGrid
public import SubdiffusiveProcess.Geometry.OddGridPartition
public import SubdiffusiveProcess.Sobolev.HarmonicTriadicMeshH10

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_catalog_cutoff_existence_basis
    {d : ℕ} [NeZero d] (_hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    {C : Type*} [Countable C] [DecidableEq C]
    (centers : C → SpatialCoordinates d) (radii : C → ℝ)
    (hradii : ∀ c : C, 0 < radii c)
    (_hRational : ∀ c : C, ∀ i : Fin d, ∃ q : ℚ,
      centers c i = (q : ℝ))
    (_hTriadic : ∀ c : C, ∃ k : ℤ, radii c = (3 : ℝ) ^ k)
    (hContained : ∀ c : C,
      closure (centeredCube (centers c) (radii c) (hradii c) : Set
        (SpatialCoordinates d)) ⊆ (centeredCube z R hR : Set
          (SpatialCoordinates d)))
    (hComplete : ∀ (z' : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r'),
      (∀ i : Fin d, ∃ q : ℚ, z' i = (q : ℝ)) →
      (∃ k : ℤ, r' = (3 : ℝ) ^ k) →
      closure (centeredCube z' r' hr' : Set (SpatialCoordinates d)) ⊆
        (centeredCube z R hR : Set (SpatialCoordinates d)) →
      ∃ c : C, centers c = z' ∧ radii c = r')
    (O : Set (SpatialCoordinates d)) (hO : IsOpen O)
    (hOQ : closure O ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)))
    (L : Set (SpatialCoordinates d)) (hL : IsCompact L) (hLO : L ⊆ O) :
    ∃ s : Finset C,
      L ⊆ (⋃ c ∈ s, (centeredCube (centers c) (radii c) (hradii c) :
        Set (SpatialCoordinates d))) ∧
      closure (⋃ c ∈ s, (centeredCube (centers c) (radii c) (hradii c) :
        Set (SpatialCoordinates d))) ⊆
        O ∧
      closure (⋃ c ∈ s, (centeredCube (centers c) (radii c) (hradii c) :
        Set (SpatialCoordinates d))) ⊆
        (centeredCube z R hR : Set (SpatialCoordinates d)) := by
  let U : C → Set (SpatialCoordinates d) := fun c =>
    (centeredCube (centers c) (radii c) (hradii c) : Set (SpatialCoordinates d))
  have hlocal : ∀ x ∈ L, ∃ c : C, x ∈ U c ∧ closure (U c) ⊆ O := by
    intro x hx
    obtain ⟨ε, hε, hεO⟩ := (Metric.isOpen_iff.mp hO) x (hLO hx)
    let δ : ℝ := min (ε / 20) 1
    have hδ : 0 < δ := by
      dsimp [δ]
      exact lt_min (by linarith) zero_lt_one
    have hδε : δ ≤ ε / 20 := min_le_left _ _
    have hδ1 : δ ≤ 1 := min_le_right _ _
    have hδ5 : δ / 5 ≤ 1 := by linarith
    choose q hqlo hqhi using fun i : Fin d =>
      (exists_rat_btwn (by linarith : x i - δ / 20 < x i + δ / 20))
    let z' : SpatialCoordinates d := fun i => (q i : ℝ)
    have hz'rat : ∀ i : Fin d, ∃ q' : ℚ, z' i = (q' : ℝ) := by
      intro i
      exact ⟨q i, rfl⟩
    have hcoord : ∀ i : Fin d, dist (z' i) (x i) < δ / 20 := by
      intro i
      rw [Real.dist_eq]
      rw [abs_lt]
      constructor <;> linarith [hqlo i, hqhi i]
    have hz'x : dist z' x ≤ δ / 20 := by
      apply (dist_pi_le_iff (by positivity)).2
      intro i
      exact (hcoord i).le
    have hz'x' : dist z' x < δ / 10 := by linarith
    obtain ⟨J, hJlo, hJhi⟩ :=
      SubdiffusiveProcess.exists_triadic_scale (by positivity : 0 < δ / 5) hδ5
    let r' : ℝ := (3 : ℝ) ^ (-(J : ℤ))
    have hr' : 0 < r' := by
      dsimp [r']
      positivity
    have hJlo' : r' / 3 < δ / 5 := by
      have he : (3 : ℝ) ^ (-((J : ℤ) + 1)) = r' / 3 := by
        dsimp [r']
        rw [show -((J : ℤ) + 1) = -(J : ℤ) - 1 by ring]
        rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
        norm_num
      rw [← he]
      exact hJlo
    have hJhi' : δ / 5 ≤ r' := by
      exact hJhi
    have hxr' : dist x z' < r' / 2 := by
      rw [dist_comm]
      have : δ / 10 ≤ r' / 2 := by linarith
      exact hz'x'.trans_le this
    have hcl : closure (centeredCube z' r' hr' : Set (SpatialCoordinates d)) ⊆
        Metric.ball x ε := by
      have hclosure : closure (centeredCube z' r' hr' : Set (SpatialCoordinates d)) =
          Metric.closedBall z' (r' / 2) := by
        change closure (Metric.ball z' (r' / 2)) = _
        rw [closure_ball z']
        positivity
      rw [hclosure]
      intro y hy
      rw [Metric.mem_closedBall] at hy
      rw [Metric.mem_ball]
      have hr'lt : r' < 3 * (δ / 5) := by linarith [hJlo']
      have hyx : dist y x ≤ r' / 2 + dist z' x := by
        calc
          dist y x ≤ dist y z' + dist z' x := dist_triangle _ _ _
          _ ≤ r' / 2 + dist z' x := add_le_add hy (le_refl _)
      have hsum : r' / 2 + dist z' x < ε := by
        have : r' / 2 + dist z' x < 2 * δ / 5 := by
          linarith [hr'lt, hz'x']
        have : 2 * δ / 5 ≤ ε := by
          have := hδε
          linarith
        linarith
      exact hyx.trans_lt hsum
    have hclO : closure (centeredCube z' r' hr' : Set (SpatialCoordinates d)) ⊆ O :=
      hcl.trans hεO
    obtain ⟨c, hc, hradius⟩ := hComplete z' r' hr' hz'rat
      ⟨-(J : ℤ), rfl⟩ (hclO.trans (subset_closure.trans hOQ))
    refine ⟨c, ?_, ?_⟩
    · simpa [U, hc, hradius] using! hxr'
    · simpa [U, hc, hradius] using hclO
  let D := {c : C // closure (U c) ⊆ O}
  have hcover : L ⊆ ⋃ c : D, U c.1 := by
    intro x hx
    obtain ⟨c, hxc, hcO⟩ := hlocal x hx
    exact mem_iUnion.mpr ⟨⟨c, hcO⟩, hxc⟩
  obtain ⟨s', hs'⟩ := hL.elim_finite_subcover (fun c : D => U c.1)
    (fun c => (centeredCube (centers c.1) (radii c.1) (hradii c.1)).isOpen) hcover
  let s : Finset C := s'.image Subtype.val
  refine ⟨s, ?_, ?_, ?_⟩
  · intro x hx
    rcases mem_iUnion₂.mp (hs' hx) with ⟨c, hc, hxc⟩
    exact mem_iUnion₂.mpr ⟨c.1, Finset.mem_image.mpr ⟨c, hc, rfl⟩, hxc⟩
  · rw [s.closure_biUnion]
    intro x hx
    simp only [mem_iUnion] at hx
    obtain ⟨c, hc, hxc⟩ := hx
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hc
    exact c'.property hxc
  · rw [s.closure_biUnion]
    intro x hx
    simp only [mem_iUnion] at hx
    obtain ⟨c, hc, hxc⟩ := hx
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hc
    exact (hContained c'.1) hxc

theorem aux_catalog_cutoff_existence_cell_dist
    {d : ℕ} (z : SpatialCoordinates d) {R : ℝ} (hR : 0 < R)
    (m : ℕ) (k : OddGridIndex d m)
    {x y : SpatialCoordinates d}
    (hx : x ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)))
    (hy : y ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d))) :
    dist x y ≤ R / (2 * (m : ℝ) + 1) := by
  have hside : 0 < R / (2 * (m : ℝ) + 1) := by positivity
  have hclosure : closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)) =
      Metric.closedBall (oddGridCenter z R m k)
        ((R / (2 * (m : ℝ) + 1)) / 2) := by
    change closure (Metric.ball (oddGridCenter z R m k)
      ((R / (2 * (m : ℝ) + 1)) / 2)) = _
    rw [closure_ball]
    positivity
  rw [hclosure] at hx hy
  rw [Metric.mem_closedBall] at hx hy
  calc
    dist x y ≤ dist x (oddGridCenter z R m k) +
        dist (oddGridCenter z R m k) y := dist_triangle _ _ _
    _ ≤ (R / (2 * (m : ℝ) + 1)) / 2 +
        (R / (2 * (m : ℝ) + 1)) / 2 :=
      add_le_add hx (by simpa [dist_comm] using hy)
    _ = R / (2 * (m : ℝ) + 1) := by ring

theorem aux_catalog_cutoff_existence_transition_cells_apply
    {d : ℕ} [NeZero d] (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (f : SpatialCoordinates d → ℝ) (K V O : Set (SpatialCoordinates d))
    (hfone : ∀ x ∈ V, f x = 1)
    (δO δV : ℝ) (hthO : Metric.thickening δO (tsupport f) ⊆ O)
    (hthV : Metric.thickening δV K ⊆ V)
    (J : ℕ) (hmesh : R / (3 : ℝ) ^ J < min δO δV) :
    ∀ k : OddGridIndex d (triadicHalf J),
      (closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) ∩
          {x | 0 < f x ∧ f x < 1}).Nonempty →
      closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) ⊆ O \ K := by
  intro k hk x hx
  obtain ⟨y, hycell, hytrans⟩ := hk
  have hyts : y ∈ tsupport f :=
    subset_tsupport f (by exact (ne_of_gt hytrans.1))
  have hxy : dist x y < min δO δV := by
    exact (aux_catalog_cutoff_existence_cell_dist z hR (triadicHalf J) k hx hycell).trans_lt
      (by simpa [triadic_denominator J] using hmesh)
  have hxO : x ∈ O := by
    apply hthO
    exact (Metric.mem_thickening_iff (δ := δO) (E := tsupport f) (x := x)).mpr
      ⟨y, hyts, lt_of_lt_of_le hxy (min_le_left δO δV)⟩
  have hxK : x ∉ K := by
    intro hxK
    have hyV : y ∈ V := by
      apply hthV
      exact (Metric.mem_thickening_iff (δ := δV) (E := K) (x := y)).mpr
        ⟨x, hxK, lt_of_lt_of_le (by simpa [dist_comm] using hxy)
          (min_le_right δO δV)⟩
    exact (ne_of_gt hytrans.2) (hfone y hyV).symm
  exact ⟨hxO, hxK⟩

theorem aux_catalog_cutoff_existence_mesh_identity
    (R : ℝ) (J : ℕ) :
    R / (3 : ℝ) ^ J = R * (1 / 3 : ℝ) ^ J := by
  rw [div_pow]
  field_simp
  simp

theorem aux_catalog_cutoff_existence_mesh_bound
    {R δ q : ℝ} (hR : 0 < R) (hq : 0 ≤ q)
    (hpow : q < δ / (2 * R)) :
    R * q < δ := by
  have hmul : q * (2 * R) < δ :=
    (lt_div_iff₀ (by positivity : 0 < 2 * R)).mp hpow
  have hRle : R ≤ 2 * R := by linarith
  have hbound : R * q ≤ q * (2 * R) := by
    calc
      R * q ≤ (2 * R) * q := mul_le_mul_of_nonneg_right hRle hq
      _ = q * (2 * R) := by ring
  exact hbound.trans_lt hmul

theorem aux_catalog_cutoff_existence_mesh_power
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    ∃ J : ℕ, (1 / 3 : ℝ) ^ J < δ / (2 * R) := by
  exact exists_pow_lt_of_lt_one
    (x := δ / (2 * R)) (by positivity : 0 < δ / (2 * R))
    (by norm_num : (1 / 3 : ℝ) < 1)

theorem aux_catalog_cutoff_existence_mesh_scale
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    ∃ J : ℕ, R / (3 : ℝ) ^ J < δ := by
  obtain ⟨J, hJpow⟩ := aux_catalog_cutoff_existence_mesh_power hR hδ
  refine ⟨J, ?_⟩
  calc
    R / (3 : ℝ) ^ J = R * (1 / 3 : ℝ) ^ J :=
      aux_catalog_cutoff_existence_mesh_identity R J
    _ < δ := aux_catalog_cutoff_existence_mesh_bound hR (by positivity) hJpow

theorem aux_catalog_cutoff_existence_harmonic_ae_abs
    {d : ℕ} [NeZero d] (W : Set (SpatialCoordinates d))
    (a : SpatialCoordinates d → ℝ) (lam Lam : ℝ)
    (hWdom : IsOpenBoundedConvexDomain W) (hlam : 0 < lam)
    (ha : Continuous a)
    (habounds : ∀ x ∈ W, lam ≤ a x ∧ a x ≤ Lam)
    (φ u : H1Function W)
    (hφupper : ∀ y, φ.toFun y ≤ 1)
    (hφlower : ∀ y, -φ.toFun y ≤ 0)
    (hu : IsWeaklyHarmonicOn a W u)
    (htrace : HasZeroTraceDifferenceOn W u φ) :
    ∀ᵐ y ∂(volume.restrict W), 0 ≤ u.toFun y ∧ u.toFun y ≤ 1 := by
  have hWopen : IsOpen W := hWdom.1
  have hameas : AEStronglyMeasurable a (volumeMeasureOn W) :=
    ha.aestronglyMeasurable.restrict
  have hbounds : ∀ᵐ y ∂(volumeMeasureOn W), lam ≤ a y ∧ a y ≤ Lam := by
    filter_upwards [ae_restrict_mem hWopen.measurableSet] with y hy
    exact habounds y hy
  obtain ⟨w, hwval, hwgrad⟩ := htrace
  have hdiff : MemH10 W (fun y => u.toFun y - φ.toFun y) := by
    refine ⟨w, ?_⟩
    funext y
    rw [hwval y]
    ring
  have hdiffneg : MemH10 W (fun y => (-u).toFun y - (-φ).toFun y) := by
    rcases Homogenization.memH10_neg hdiff with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    funext y
    have hvy := congrFun hv y
    calc
      v.toFun y = -(u.toFun y - φ.toFun y) := by
        simpa only [Homogenization.H1Function.neg_toFun] using hvy
      _ = (-u).toFun y - (-φ).toFun y := by
        simp only [Homogenization.H1Function.neg_toFun]
        ring
  have hφlower' : ∀ y, (-φ).toFun y ≤ 0 := by
    intro y
    simpa only [Homogenization.H1Function.neg_toFun] using hφlower y
  have hupper :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.hasBoundaryUpperBoundOn_of_datum_le
      hWdom hdiff hφupper
  have hlower :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.hasBoundaryUpperBoundOn_of_datum_le
      hWdom hdiffneg hφlower'
  have haeupper :=
    SubdiffusiveProcess.CoarseGrainingVocab.ae_le_of_isWeaklyHarmonicOn
      hWdom hlam hameas hbounds hu hupper
  have haelower :=
    SubdiffusiveProcess.CoarseGrainingVocab.ae_le_of_isWeaklyHarmonicOn
      hWdom hlam hameas hbounds (SubdiffusiveProcess.CoarseGrainingVocab.isWeaklyHarmonicOn_neg hu) hlower
  filter_upwards [haeupper, haelower] with y hyupper hylower
  have hylower' : -u.toFun y ≤ 0 := by
    simpa only [Homogenization.H1Function.neg_toFun] using hylower
  exact ⟨by linarith, hyupper⟩

theorem aux_catalog_cutoff_existence_harmonic_range
    {d : ℕ} [NeZero d] (W : Set (SpatialCoordinates d))
    (a : SpatialCoordinates d → ℝ) (lam Lam : ℝ)
    (hWdom : IsOpenBoundedConvexDomain W) (hlam : 0 < lam)
    (ha : Continuous a)
    (habounds : ∀ x ∈ W, lam ≤ a x ∧ a x ≤ Lam)
    (φ u : H1Function W)
    (hφupper : ∀ y, φ.toFun y ≤ 1)
    (hφlower : ∀ y, -φ.toFun y ≤ 0)
    (hu : IsWeaklyHarmonicOn a W u)
    (htrace : HasZeroTraceDifferenceOn W u φ)
    (hcont : ContinuousOn u.toFun (closure W)) :
    ∀ x ∈ closure W, 0 ≤ u.toFun x ∧ u.toFun x ≤ 1 := by
  have hWopen : IsOpen W := hWdom.1
  have hae := aux_catalog_cutoff_existence_harmonic_ae_abs W a lam Lam hWdom hlam ha
    habounds φ u hφupper hφlower hu htrace
  have haeupper : ∀ᵐ y ∂(volume.restrict W), u.toFun y ≤ 1 := by
    filter_upwards [hae] with y hy
    exact hy.2
  have haelower : ∀ᵐ y ∂(volume.restrict W), -u.toFun y ≤ 0 := by
    filter_upwards [hae] with y hy
    linarith [hy.1]
  have hupperW : ∀ x ∈ W, u.toFun x ≤ 1 :=
    lane2_le_of_ae_le_of_continuousOn hWopen
      (hcont.mono subset_closure) haeupper
  have hlowerW : ∀ x ∈ W, -u.toFun x ≤ 0 :=
    lane2_le_of_ae_le_of_continuousOn hWopen
      (hcont.neg.mono subset_closure) haelower
  intro x hx
  have hupperC : u.toFun x ≤ 1 :=
    ContinuousWithinAt.closure_le hx ((hcont x hx).mono subset_closure)
      continuousWithinAt_const hupperW
  have hlowerC : -u.toFun x ≤ 0 :=
    ContinuousWithinAt.closure_le hx
      ((hcont.neg x hx).mono subset_closure) continuousWithinAt_const hlowerW
  constructor <;> linarith

theorem aux_catalog_cutoff_existence_constant_cell
    {d : ℕ} [NeZero d] (W : Set (SpatialCoordinates d))
    (a : SpatialCoordinates d → ℝ) (lam Lam : ℝ)
    (hWdom : IsOpenBoundedConvexDomain W) (hlam : 0 < lam)
    (ha : Continuous a)
    (habounds : ∀ x ∈ W, lam ≤ a x ∧ a x ≤ Lam)
    (φ u : H1Function W) (cval : ℝ) (hφone : ∀ x ∈ W, φ.toFun x = cval)
    (hu : IsWeaklyHarmonicOn a W u)
    (htrace : HasZeroTraceDifferenceOn W u φ)
    (hcont : ContinuousOn u.toFun (closure W)) :
    ∀ x ∈ closure W, u.toFun x = cval := by
  let := hWdom.isFiniteMeasure_restrict_volume
  have hWopen : IsOpen W := hWdom.1
  obtain ⟨w, hwval, hwgrad⟩ := htrace
  let c : H1Function W := H1Function.const cval
  have hdiff : MemH10 W (u - c).toFun := by
    have hae : (u - c).toFun =ᵐ[volume.restrict W] w.toH1Function.toFun := by
      filter_upwards [ae_restrict_mem hWopen.measurableSet] with x hx
      have hw := hwval x
      have hp := hφone x hx
      dsimp [c]
      simp only [Homogenization.H1Function.sub_toFun, H1Function.const_apply]
      rw [hw, hp]
      ring_nf
    exact Homogenization.memH10_of_ae_eq_h10 hWdom (u - c) w hae
  let cn : H1Function W := H1Function.const (-cval)
  have hdiffneg : MemH10 W ((-u) - cn).toFun := by
    have hae : ((-u) - cn).toFun =ᵐ[volume.restrict W]
        (-w).toH1Function.toFun := by
      filter_upwards [ae_restrict_mem hWopen.measurableSet] with x hx
      have hw := hwval x
      have hp := hφone x hx
      dsimp [cn]
      simp only [Homogenization.H1Function.sub_toFun,
        Homogenization.H1Function.neg_toFun, H1Function.const_apply]
      rw [hw, hp]
      ring_nf
      rw [show (-w).toH1Function = -w.toH1Function by rfl]
      simp only [Homogenization.H1Function.neg_toFun]
    exact Homogenization.memH10_of_ae_eq_h10 hWdom ((-u) - cn) (-w) hae
  have hameas : AEStronglyMeasurable a (volumeMeasureOn W) :=
    ha.aestronglyMeasurable.restrict
  have hbounds : ∀ᵐ y ∂(volumeMeasureOn W), lam ≤ a y ∧ a y ≤ Lam := by
    filter_upwards [ae_restrict_mem hWopen.measurableSet] with y hy
    exact habounds y hy
  have hupper :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.hasBoundaryUpperBoundOn_of_datum_le
      (M := cval) hWdom (by simpa only [Homogenization.H1Function.sub_toFun] using hdiff)
        (by intro y; simp [c])
  have hlower :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.hasBoundaryUpperBoundOn_of_datum_le
      (M := -cval) hWdom (by simpa only [Homogenization.H1Function.sub_toFun] using hdiffneg)
        (by intro y; simp [cn])
  have haeupper :=
    SubdiffusiveProcess.CoarseGrainingVocab.ae_le_of_isWeaklyHarmonicOn
      hWdom hlam hameas hbounds hu hupper
  have haelower :=
    SubdiffusiveProcess.CoarseGrainingVocab.ae_le_of_isWeaklyHarmonicOn
      hWdom hlam hameas hbounds (SubdiffusiveProcess.CoarseGrainingVocab.isWeaklyHarmonicOn_neg hu) hlower
  have hae : u.toFun =ᵐ[volume.restrict W] (fun _ => cval) := by
    filter_upwards [haeupper, haelower] with y hyupper hylower
    have hylower' : -u.toFun y ≤ -cval := by
      simpa only [Homogenization.H1Function.neg_toFun] using hylower
    linarith
  have heqW : ∀ x ∈ W, u.toFun x = cval :=
    lane2_eqOn_of_ae_eq_of_continuousOn hWopen
      (hcont.mono subset_closure) continuousOn_const hae
  intro x hx
  apply le_antisymm
  · exact ContinuousWithinAt.closure_le hx
      ((hcont x hx).mono subset_closure) continuousWithinAt_const
      (fun y hy => (heqW y hy).le)
  · exact ContinuousWithinAt.closure_le hx
      (continuousWithinAt_const) ((hcont x hx).mono subset_closure)
      (fun y hy => (heqW y hy).ge)

theorem aux_catalog_cutoff_existence_mesh_interpolant
    {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (J : ℕ)
    (a : SpatialCoordinates d → ℝ) (lam Lam : ℝ)
    (hlam : 0 < lam) (ha : Continuous a)
    (habounds : ∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
      lam ≤ a x ∧ a x ≤ Lam)
    (φ : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hφsmooth : ContDiff ℝ (⊤ : ℕ∞) φ.toFun)
    (hφsupp : HasCompactSupport φ.toFun)
    (hφQ : tsupport φ.toFun ⊆ (centeredCube z R hR : Set (SpatialCoordinates d))) :
    ∃ w : H10Function (centeredCube z R hR : Set (SpatialCoordinates d)),
      ContinuousOn w.toH1Function.toFun
        (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
      (∀ k : OddGridIndex d (triadicHalf J),
        IsWeaklyHarmonicOn a
          (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
          (w.toH1Function.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
            (oddGridCell_subset z hR (triadicHalf J) k)) ∧
        HasZeroTraceDifferenceOn
          (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
          (w.toH1Function.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
            (oddGridCell_subset z hR (triadicHalf J) k))
          (φ.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
            (oddGridCell_subset z hR (triadicHalf J) k)) ∧
        energy a
            (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
            (w.toH1Function.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
              (oddGridCell_subset z hR (triadicHalf J) k)) =
          sInf {e : ℝ | ∃ u : H1Function
            (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)),
            HasZeroTraceDifferenceOn
              (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) u
              (φ.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
                (oddGridCell_subset z hR (triadicHalf J) k)) ∧
            e = energy a
              (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) u}) ∧
      energy a (centeredCube z R hR : Set (SpatialCoordinates d)) w.toH1Function =
        ∑ k : OddGridIndex d (triadicHalf J),
          sInf {e : ℝ | ∃ u : H1Function
            (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)),
            HasZeroTraceDifferenceOn
              (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) u
              (φ.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
                (oddGridCell_subset z hR (triadicHalf J) k)) ∧
            e = energy a
              (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) u} := by
  obtain ⟨Cmesh, hCmesh, hmesh⟩ := mesh_interpolator hd
  obtain ⟨w, hwcont, hwcell, hwenergy, hwapprox⟩ :=
    hmesh z R hR J a lam Lam hlam ha habounds φ hφsmooth hφsupp hφQ
  refine ⟨w, hwcont, ?_, hwenergy⟩
  intro k
  simpa only using hwcell k

theorem aux_catalog_cutoff_existence_plateau_selection
    {d : ℕ} [NeZero d] (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ)
    (hR : 0 < R)
    (C : Type*) [Countable C] [DecidableEq C]
    (centers : C → SpatialCoordinates d) (radii : C → ℝ)
    (hradii : ∀ c : C, 0 < radii c)
    (hRational : ∀ c : C, ∀ i : Fin d, ∃ q : ℚ,
      centers c i = (q : ℝ))
    (hTriadic : ∀ c : C, ∃ k : ℤ, radii c = (3 : ℝ) ^ k)
    (hContained : ∀ c : C,
      closure (centeredCube (centers c) (radii c) (hradii c) : Set
        (SpatialCoordinates d)) ⊆
        (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hComplete : ∀ (z' : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r'),
      (∀ i : Fin d, ∃ q : ℚ, z' i = (q : ℝ)) →
      (∃ k : ℤ, r' = (3 : ℝ) ^ k) →
      closure (centeredCube z' r' hr' : Set (SpatialCoordinates d)) ⊆
        (centeredCube z R hR : Set (SpatialCoordinates d)) →
      ∃ c : C, centers c = z' ∧ radii c = r')
    (T : Type*) [Countable T]
    (theta : T → H1Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hTheta : ∀ b : T,
      ContDiff ℝ (⊤ : ℕ∞) (theta b).toFun ∧
      HasCompactSupport (theta b).toFun ∧
      tsupport (theta b).toFun ⊆
        (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
      ∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
        0 ≤ (theta b).toFun x ∧ (theta b).toFun x ≤ 1)
    (hPlateaus : ∀ (s o : Finset C),
      (⋃ c ∈ s, closure (centeredCube (centers c) (radii c) (hradii c) :
        Set (SpatialCoordinates d))) ⊆
        (⋃ c ∈ o, (centeredCube (centers c) (radii c) (hradii c) :
          Set (SpatialCoordinates d))) →
      closure (⋃ c ∈ o, (centeredCube (centers c) (radii c) (hradii c) :
        Set (SpatialCoordinates d))) ⊆
        (centeredCube z R hR : Set (SpatialCoordinates d)) →
      ∃ b : T, ∃ V : Set (SpatialCoordinates d),
        IsOpen V ∧
        (⋃ c ∈ s, closure (centeredCube (centers c) (radii c) (hradii c) :
          Set (SpatialCoordinates d))) ⊆ V ∧
        V ⊆ (⋃ c ∈ o, (centeredCube (centers c) (radii c) (hradii c) :
          Set (SpatialCoordinates d))) ∧
        (∀ x ∈ V, (theta b).toFun x = 1) ∧
        tsupport (theta b).toFun ⊆
          (⋃ c ∈ o, (centeredCube (centers c) (radii c) (hradii c) :
            Set (SpatialCoordinates d))))
    (K O : Set (SpatialCoordinates d))
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (hOQ : closure O ⊆ (centeredCube z R hR : Set (SpatialCoordinates d))) :
    ∃ (b : T) (V₀ : Set (SpatialCoordinates d)),
      IsOpen V₀ ∧ K ⊆ V₀ ∧ V₀ ⊆ O ∧
      (∀ x ∈ V₀, (theta b).toFun x = 1) ∧
      tsupport (theta b).toFun ⊆ O ∧
      ContDiff ℝ (⊤ : ℕ∞) (theta b).toFun ∧
      HasCompactSupport (theta b).toFun ∧
      tsupport (theta b).toFun ⊆
        (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
      (∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
        0 ≤ (theta b).toFun x ∧ (theta b).toFun x ≤ 1) := by
  obtain ⟨s, hsK, hsO, hsQ⟩ :=
    aux_catalog_cutoff_existence_basis hd z R hR centers radii hradii hRational
      hTriadic hContained hComplete O hO hOQ K hK hKO
  let L : Set (SpatialCoordinates d) :=
    ⋃ c ∈ s, closure (centeredCube (centers c) (radii c) (hradii c) :
      Set (SpatialCoordinates d))
  have hLcompact : IsCompact L := by
    dsimp [L]
    exact s.isCompact_biUnion (fun c hc =>
      lane2_isCompact_closure_centeredCube (centers c) (hradii c))
  have hLO : L ⊆ O := by
    simpa [L, s.closure_biUnion] using hsO
  obtain ⟨o, hLo, hoQO, hoQ⟩ :=
    aux_catalog_cutoff_existence_basis hd z R hR centers radii hradii hRational
      hTriadic hContained hComplete O hO hOQ L hLcompact hLO
  obtain ⟨b, V₀, hV₀open, hL_V₀, hV₀o, hthetaV₀, hsuppo⟩ :=
    hPlateaus s o hLo hoQ
  have hVL : (⋃ c ∈ s, (centeredCube (centers c) (radii c) (hradii c) :
      Set (SpatialCoordinates d))) ⊆ L := by
    intro x hx
    rcases mem_iUnion₂.mp hx with ⟨c, hc, hxc⟩
    exact mem_iUnion₂.mpr ⟨c, hc, subset_closure hxc⟩
  have hKV₀ : K ⊆ V₀ := by
    exact hsK.trans (hVL.trans hL_V₀)
  have hV₀O : V₀ ⊆ O := hV₀o.trans (by
    intro x hx
    exact hoQO (subset_closure hx))
  have hbsuppO : tsupport (theta b).toFun ⊆ O :=
    hsuppo.trans (by
      intro x hx
      exact hoQO (subset_closure hx))
  obtain ⟨hbcont, hbcomp, hbsupp, hbrange⟩ := hTheta b
  refine ⟨b, V₀, hV₀open, hKV₀, hV₀O, hthetaV₀, hbsuppO, hbcont, hbcomp,
    hbsupp, hbrange⟩

theorem aux_catalog_cutoff_existence_mesh_selection
    {d : ℕ} [NeZero d] (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (f : SpatialCoordinates d → ℝ) (hfcomp : HasCompactSupport f)
    (K V O : Set (SpatialCoordinates d)) (hK : IsCompact K)
    (hVopen : IsOpen V) (hKV : K ⊆ V)
    (hfone : ∀ x ∈ V, f x = 1) (hO : IsOpen O)
    (hfsupp : tsupport f ⊆ O) :
    ∃ J : ℕ,
      ∀ k : OddGridIndex d (triadicHalf J),
        (closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) ∩
            {x | 0 < f x ∧ f x < 1}).Nonempty →
        closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) ⊆ O \ K := by
  obtain ⟨δO, hδO, hthO⟩ := hfcomp.exists_thickening_subset_open hO hfsupp
  obtain ⟨δV, hδV, hthV⟩ := hK.exists_thickening_subset_open hVopen hKV
  let δ : ℝ := min δO δV
  have hδ : 0 < δ := lt_min hδO hδV
  obtain ⟨J, hmesh⟩ := aux_catalog_cutoff_existence_mesh_scale hR hδ
  refine ⟨J, ?_⟩
  exact aux_catalog_cutoff_existence_transition_cells_apply z R hR f K V O hfone δO δV
    hthO hthV J (by simpa [δ] using hmesh)

theorem aux_catalog_cutoff_existence_mesh_geometry
    {d : ℕ} [NeZero d] (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (f : SpatialCoordinates d → ℝ) (hfcomp : HasCompactSupport f)
    (K O V₀ : Set (SpatialCoordinates d)) (hK : IsCompact K)
    (hO : IsOpen O) (hKO : K ⊆ O) (hV₀open : IsOpen V₀)
    (hKV₀ : K ⊆ V₀) (_hV₀O : V₀ ⊆ O)
    (hfone₀ : ∀ x ∈ V₀, f x = 1) (hfsupp : tsupport f ⊆ O) :
    ∃ (J : ℕ) (V : Set (SpatialCoordinates d)),
      IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧
      (∀ x ∈ V, f x = 1) ∧
      (∀ k : OddGridIndex d (triadicHalf J),
        (closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) ∩ V).Nonempty →
        closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) ⊆ V₀) ∧
      (∀ k : OddGridIndex d (triadicHalf J),
        (closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) ∩
            {x | 0 < f x ∧ f x < 1}).Nonempty →
        closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) ⊆ O \ K) ∧
      R / (3 : ℝ) ^ J < 1 := by
  obtain ⟨δ₀, hδ₀, hth₀⟩ :=
    hK.exists_thickening_subset_open hV₀open hKV₀
  obtain ⟨δs, hδs, hthS⟩ :=
    hfcomp.exists_thickening_subset_open hO hfsupp
  obtain ⟨δk, hδk, hthK⟩ :=
    hK.exists_thickening_subset_open hO hKO
  let δO : ℝ := min δs δk
  have hδO : 0 < δO := lt_min hδs hδk
  have hthO : Metric.thickening δO (tsupport f) ⊆ O := by
    exact (Metric.thickening_mono (min_le_left δs δk) _).trans hthS
  have hthK' : Metric.thickening δO K ⊆ O := by
    exact (Metric.thickening_mono (min_le_right δs δk) _).trans hthK
  let ε : ℝ := min (min δ₀ δO) 1 / 3
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hε₀ : ε ≤ δ₀ := by
    dsimp [ε]
    nlinarith [min_le_left (min δ₀ δO) 1, min_le_left δ₀ δO]
  have hεO : ε ≤ δO := by
    dsimp [ε]
    nlinarith [min_le_left (min δ₀ δO) 1, min_le_right δ₀ δO]
  have h2ε₀ : 2 * ε < δ₀ := by
    dsimp [ε]
    nlinarith [hδ₀, min_le_left (min δ₀ δO) 1, min_le_left δ₀ δO]
  obtain ⟨J, hmesh⟩ := aux_catalog_cutoff_existence_mesh_scale hR hε
  let V : Set (SpatialCoordinates d) := Metric.thickening ε K
  have hVopen : IsOpen V := by
    dsimp [V]
    exact Metric.isOpen_thickening
  have hKV : K ⊆ V := by
    dsimp [V]
    exact Metric.self_subset_thickening hε K
  have hVO : V ⊆ O := by
    intro x hx
    apply hthK'
    exact Metric.thickening_mono hεO K hx
  have hV₀ : V ⊆ V₀ := by
    intro x hx
    apply hth₀
    exact Metric.thickening_mono hε₀ K hx
  have hfone : ∀ x ∈ V, f x = 1 := by
    intro x hx
    exact hfone₀ x (hV₀ hx)
  have hcellV₀ :
      ∀ k : OddGridIndex d (triadicHalf J),
        (closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) ∩ V).Nonempty →
        closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) ⊆ V₀ := by
    intro k hk y hy
    obtain ⟨x, hxcell, hxV⟩ := hk
    obtain ⟨x₀, hx₀, hxx₀⟩ :=
      (Metric.mem_thickening_iff (δ := ε) (E := K) (x := x)).mp hxV
    apply hth₀
    have hdistle : dist y x₀ ≤
        R / (3 : ℝ) ^ J + dist x x₀ := by
      calc
        dist y x₀ ≤ dist y x + dist x x₀ := dist_triangle _ _ _
        _ ≤ R / (3 : ℝ) ^ J + dist x x₀ :=
          add_le_add
            (by simpa [dist_comm, triadic_denominator J] using
              (aux_catalog_cutoff_existence_cell_dist z hR (triadicHalf J) k hy hxcell))
            (le_refl _)
    exact (Metric.mem_thickening_iff (δ := δ₀) (E := K) (x := y)).mpr
      ⟨x₀, hx₀, lt_of_le_of_lt hdistle (by nlinarith [hmesh, hxx₀, h2ε₀])⟩
  have htransition :
      ∀ k : OddGridIndex d (triadicHalf J),
        (closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) ∩
            {x | 0 < f x ∧ f x < 1}).Nonempty →
        closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) ⊆ O \ K := by
    have hthV : Metric.thickening ε K ⊆ V := by
      intro x hx
      exact hx
    apply aux_catalog_cutoff_existence_transition_cells_apply z R hR f K V O hfone
      δO ε hthO hthV J
    have hmine : min δO ε = ε := min_eq_right hεO
    simpa [hmine] using hmesh
  refine ⟨J, V, hVopen, hKV, hVO, hfone, hcellV₀, htransition, ?_⟩
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    nlinarith [min_le_right (min δ₀ δO) 1]
  exact hmesh.trans_le hε1

theorem aux_catalog_cutoff_existence_cell_zero
    {d : ℕ} [NeZero d] (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (J : ℕ) (k : OddGridIndex d (triadicHalf J))
    (f : SpatialCoordinates d → ℝ)
    (hfcont : ContinuousOn f
      (closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))))
    (hfrange : ∀ y ∈ closure (oddGridCell z R hR (triadicHalf J) k :
        Set (SpatialCoordinates d)), 0 ≤ f y ∧ f y ≤ 1)
    (x : SpatialCoordinates d)
    (hx : x ∈ closure (oddGridCell z R hR (triadicHalf J) k :
      Set (SpatialCoordinates d))) (hfx : f x = 0)
    (hnot :
      ¬(closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) ∩
        {y | 0 < f y ∧ f y < 1}).Nonempty) :
    ∀ y ∈ closure (oddGridCell z R hR (triadicHalf J) k :
      Set (SpatialCoordinates d)), f y = 0 := by
  have hcl :
      closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) =
        Metric.closedBall (oddGridCenter z R (triadicHalf J) k)
          ((R / (2 * (triadicHalf J : ℝ) + 1)) / 2) := by
    change closure (Metric.ball _ _) = _
    rw [closure_ball]
    positivity
  have hconv : Convex ℝ
      (closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))) := by
    rw [hcl]
    exact convex_closedBall _ _
  have hpre := hconv.isPreconnected
  intro y hy
  by_contra hyzero
  have hypos : 0 < f y := lt_of_le_of_ne (hfrange y hy).1 (Ne.symm hyzero)
  have hyone : f y = 1 := by
    by_contra hyone
    have hylt : f y < 1 := lt_of_le_of_ne (hfrange y hy).2 hyone
    exact hnot ⟨y, hy, ⟨hypos, hylt⟩⟩
  have hmid : (1 / 2 : ℝ) ∈ Icc (f x) (f y) := by
    rw [hfx, hyone]
    norm_num
  obtain ⟨q, hq, hqval⟩ :=
    hpre.intermediate_value hx hy hfcont hmid
  exact hnot ⟨q, hq, by
    change 0 < f q ∧ f q < 1
    rw [hqval]
    norm_num⟩

theorem aux_catalog_cutoff_existence_partition_measure
    {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (m : ℕ)
    (g : SpatialCoordinates d → ENNReal) (x : SpatialCoordinates d) (rho : ℝ) :
    ((volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))).withDensity g)
        (Metric.ball x rho) =
      ∑ k : OddGridIndex d m,
        ((volume.restrict (oddGridCell z R hR m k : Set (SpatialCoordinates d))).withDensity g)
          (Metric.ball x rho) := by
  let μ : Measure (SpatialCoordinates d) := volume.withDensity g
  let U : Set (SpatialCoordinates d) :=
    ⋃ k : OddGridIndex d m, (oddGridCell z R hR m k : Set (SpatialCoordinates d))
  have hμae : U =ᵐ[μ] (centeredCube z R hR : Set (SpatialCoordinates d)) := by
    exact (withDensity_absolutelyContinuous (volume : Measure (SpatialCoordinates d)) g).ae_eq
      (oddGrid_union_ae_eq z hR m)
  have hrestrict : μ.restrict (centeredCube z R hR : Set (SpatialCoordinates d)) =
      μ.restrict U := Measure.restrict_congr_set hμae.symm
  have hunion : μ.restrict U =
      Measure.sum (fun k : OddGridIndex d m =>
        μ.restrict (oddGridCell z R hR m k : Set (SpatialCoordinates d))) := by
    exact Measure.restrict_iUnion
      (oddGridCell_pairwiseDisjoint z hR m)
      (fun k => (oddGridCell z R hR m k).isOpen.measurableSet)
  have hQ : μ.restrict (centeredCube z R hR : Set (SpatialCoordinates d)) =
      (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))).withDensity g := by
    exact restrict_withDensity (centeredCube z R hR).isOpen.measurableSet g
  have hcell : ∀ k : OddGridIndex d m,
      μ.restrict (oddGridCell z R hR m k : Set (SpatialCoordinates d)) =
        (volume.restrict (oddGridCell z R hR m k : Set (SpatialCoordinates d))).withDensity g := by
    intro k
    exact restrict_withDensity (oddGridCell z R hR m k).isOpen.measurableSet g
  rw [← hQ, hrestrict, hunion, Measure.sum_apply _ Metric.isOpen_ball.measurableSet]
  simp_rw [hcell]
  rw [tsum_fintype]

theorem aux_catalog_cutoff_existence_cell_measure_mono
    {d : ℕ} (cell : Set (SpatialCoordinates d)) (hcell : IsOpen cell)
    (g : SpatialCoordinates d → ENNReal) (s t : Set (SpatialCoordinates d))
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hsub : s ∩ cell ⊆ t ∩ cell) :
    ((volume.restrict cell).withDensity g) s ≤
      ((volume.restrict cell).withDensity g) t := by
  let μ : Measure (SpatialCoordinates d) := volume.withDensity g
  let ν : Measure (SpatialCoordinates d) := (volume.restrict cell).withDensity g
  have hν : ν = μ.restrict cell := by
    dsimp [ν, μ]
    exact (restrict_withDensity hcell.measurableSet g).symm
  have hsupp : ν.restrict cell = ν := by
    rw [hν, Measure.restrict_restrict hcell.measurableSet]
    simp only [inter_self]
  calc
    ((volume.restrict cell).withDensity g) s = (ν.restrict cell) s := by rw [hsupp]
    _ = ν (s ∩ cell) := Measure.restrict_apply hs
    _ ≤ ν (t ∩ cell) := measure_mono hsub
    _ = (ν.restrict cell) t := (Measure.restrict_apply ht).symm
    _ = ((volume.restrict cell).withDensity g) t := by rw [hsupp]

theorem aux_catalog_cutoff_existence_sum_power
    {ι : Type*} [Fintype ι] (c : ι → ℝ) (t rho : ℝ)
    (hc : ∀ i, 0 ≤ c i) (_ht : 0 ≤ t) (hrho : 0 ≤ rho) :
    (∑ i : ι, ENNReal.ofReal (c i * (2 * rho) ^ t)) =
      ENNReal.ofReal ((2 : ℝ) ^ t * (∑ i : ι, c i) * rho ^ t) := by
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · rw [← Finset.sum_mul]
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hrho]
    ring
  · intro i hi
    exact mul_nonneg (hc i) (Real.rpow_nonneg (by positivity) t)

theorem aux_catalog_cutoff_existence_cell_growth
    {d : ℕ} (cell : Set (SpatialCoordinates d)) (hcell : IsOpen cell)
    (g : SpatialCoordinates d → ENNReal) (C t : ℝ)
    (hdiam : ∀ (u v : SpatialCoordinates d), u ∈ closure cell → v ∈ closure cell →
      dist u v ≤ C) (hC : C < 1) (ht : 0 ≤ t)
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ y ∈ closure cell, ∀ r : ℝ, 0 < r → r ≤ 1 →
      ((volume.restrict cell).withDensity g) (Metric.ball y r) ≤
        ENNReal.ofReal (K * r ^ t))
    (x : SpatialCoordinates d) (rho : ℝ) (hrho : 0 < rho) (_hrho1 : rho ≤ 1) :
    ((volume.restrict cell).withDensity g) (Metric.ball x rho) ≤
      ENNReal.ofReal (K * (2 * rho) ^ t) := by
  by_cases hsmall : 2 * rho ≤ 1
  · by_cases hne : (Metric.ball x rho ∩ cell).Nonempty
    · obtain ⟨y, hyball, hycell⟩ := hne
      have hycl : y ∈ closure cell := subset_closure hycell
      have hsubset : Metric.ball x rho ∩ cell ⊆ Metric.ball y (2 * rho) ∩ cell := by
        intro q hq
        refine ⟨?_, hq.2⟩
        apply Metric.mem_ball'.mpr
        calc
          dist y q ≤ dist y x + dist x q := dist_triangle _ _ _
          _ < rho + rho := add_lt_add
            (Metric.mem_ball.mp hyball)
            (by simpa [dist_comm] using (Metric.mem_ball.mp hq.1))
          _ = 2 * rho := by ring
      calc
        ((volume.restrict cell).withDensity g) (Metric.ball x rho) ≤
            ((volume.restrict cell).withDensity g) (Metric.ball y (2 * rho)) :=
          aux_catalog_cutoff_existence_cell_measure_mono cell hcell g
            (Metric.ball x rho) (Metric.ball y (2 * rho))
            Metric.isOpen_ball.measurableSet Metric.isOpen_ball.measurableSet hsubset
        _ ≤ ENNReal.ofReal (K * (2 * rho) ^ t) := hbound y hycl (2 * rho)
          (by positivity) hsmall
    · have hempty : Metric.ball x rho ∩ cell = ∅ := not_nonempty_iff_eq_empty.mp hne
      calc
        ((volume.restrict cell).withDensity g) (Metric.ball x rho) ≤
            ((volume.restrict cell).withDensity g) (∅ : Set (SpatialCoordinates d)) :=
          aux_catalog_cutoff_existence_cell_measure_mono cell hcell g
            (Metric.ball x rho) ∅ Metric.isOpen_ball.measurableSet MeasurableSet.empty
            (by simp [hempty])
        _ = 0 := by simp
        _ ≤ ENNReal.ofReal (K * (2 * rho) ^ t) := bot_le
  · have hrhohalf : 1 / 2 < rho := by linarith
    by_cases hne : (Metric.ball x rho ∩ cell).Nonempty
    · obtain ⟨y, hyball, hycell⟩ := hne
      have hycl : y ∈ closure cell := subset_closure hycell
      have hsubset : Metric.ball x rho ∩ cell ⊆ Metric.ball y 1 ∩ cell := by
        intro q hq
        refine ⟨?_, hq.2⟩
        apply Metric.mem_ball'.mpr
        have hdist := hdiam q y (subset_closure hq.2) hycl
        exact lt_of_le_of_lt (by simpa [dist_comm] using hdist) hC
      calc
        ((volume.restrict cell).withDensity g) (Metric.ball x rho) ≤
            ((volume.restrict cell).withDensity g) (Metric.ball y 1) :=
          aux_catalog_cutoff_existence_cell_measure_mono cell hcell g
            (Metric.ball x rho) (Metric.ball y 1)
            Metric.isOpen_ball.measurableSet Metric.isOpen_ball.measurableSet hsubset
        _ ≤ ENNReal.ofReal (K * (1 : ℝ) ^ t) := hbound y hycl 1
          (by positivity) (by norm_num)
        _ ≤ ENNReal.ofReal (K * (2 * rho) ^ t) := by
          apply ENNReal.ofReal_le_ofReal
          have hpow : 1 ≤ (2 * rho) ^ t := by
            apply Real.one_le_rpow
            linarith
            exact ht
          simpa only [Real.one_rpow, mul_one] using
            (mul_le_mul_of_nonneg_left hpow hK)
    · have hempty : Metric.ball x rho ∩ cell = ∅ := not_nonempty_iff_eq_empty.mp hne
      calc
        ((volume.restrict cell).withDensity g) (Metric.ball x rho) ≤
            ((volume.restrict cell).withDensity g) (∅ : Set (SpatialCoordinates d)) :=
          aux_catalog_cutoff_existence_cell_measure_mono cell hcell g
            (Metric.ball x rho) ∅ Metric.isOpen_ball.measurableSet MeasurableSet.empty
            (by simp [hempty])
        _ = 0 := by simp
        _ ≤ ENNReal.ofReal (K * (2 * rho) ^ t) := bot_le

theorem aux_catalog_cutoff_existence_global_measure_bound
    {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (m : ℕ)
    (g h : SpatialCoordinates d → ENNReal)
    (heq : g =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] h)
    (b : OddGridIndex d m → ℝ) (hb : ∀ k, 0 ≤ b k) (t : ℝ) (ht : 0 ≤ t)
    (hcell : ∀ k : OddGridIndex d m, ∀ x : SpatialCoordinates d,
      ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
      ((volume.restrict (oddGridCell z R hR m k : Set (SpatialCoordinates d))).withDensity h)
        (Metric.ball x rho) ≤ ENNReal.ofReal (b k * (2 * rho) ^ t))
    (x : SpatialCoordinates d) (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    ((volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))).withDensity g)
        (Metric.ball x rho) ≤
      ENNReal.ofReal (((2 : ℝ) ^ t * ∑ k : OddGridIndex d m, b k) * rho ^ t) := by
  rw [withDensity_congr_ae heq]
  rw [aux_catalog_cutoff_existence_partition_measure z R hR m h x rho]
  calc
    (∑ k : OddGridIndex d m,
        ((volume.restrict (oddGridCell z R hR m k : Set (SpatialCoordinates d))).withDensity h)
          (Metric.ball x rho)) ≤
        ∑ k : OddGridIndex d m, ENNReal.ofReal (b k * (2 * rho) ^ t) := by
      exact Finset.sum_le_sum (fun k _ => hcell k x rho hrho hrho1)
    _ = ENNReal.ofReal (((2 : ℝ) ^ t * ∑ k : OddGridIndex d m, b k) * rho ^ t) :=
      aux_catalog_cutoff_existence_sum_power b t rho hb ht hrho.le

theorem aux_catalog_cutoff_existence_density_congr
    {d : ℕ} {μ : Measure (SpatialCoordinates d)}
    (f g : SpatialCoordinates d → ℝ)
    (p q : SpatialCoordinates d → Fin d → ℝ)
    (hf : f =ᵐ[μ] g)
    (hp : ∀ i : Fin d, (fun x => p x i) =ᵐ[μ] (fun x => q x i)) :
    (fun x => ENNReal.ofReal (f x * ∑ i : Fin d, (p x i) ^ 2)) =ᵐ[μ]
      (fun x => ENNReal.ofReal (g x * ∑ i : Fin d, (q x i) ^ 2)) := by
  filter_upwards [hf, ae_all_iff.mpr hp] with x hfx hxp
  rw [hfx]
  congr 1
  simp_rw [hxp]



theorem catalog_cutoff_existence
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ)
    (hR : 0 < R) :
    let Q := centeredCube z R hR
    ∀ (S : ResponseSpace Q)
    (_hS : S.space = killedSobolevGraph Q)
    (a : ℕ → SpatialCoordinates d → ℝ)
    (aC : ℕ → PositiveCoefficient Q)
    (_hAC : ∀ n : ℕ,
      ((aC n).val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] a n)
    (_hAcont : ∀ n : ℕ, Continuous (a n))
    (_hell : ∀ n : ℕ, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ (Q : Set (SpatialCoordinates d)),
        lam ≤ a n x ∧ a n x ≤ Lam)
    (t alpha : ℝ) (_ht : (d : ℝ) - 1 < t) (_htd : t < (d : ℝ))
    (_halpha : 0 < alpha) (_halpha1 : alpha < 1)
    (C : Type*) [Countable C] [DecidableEq C]
    (centers : C → SpatialCoordinates d) (radii : C → ℝ)
    (hradii : ∀ c : C, 0 < radii c)
    (_hRational : ∀ c : C, ∀ i : Fin d, ∃ q : ℚ,
      centers c i = (q : ℝ))
    (_hTriadic : ∀ c : C, ∃ k : ℤ, radii c = (3 : ℝ) ^ k)
    (_hContained : ∀ c : C,
      closure (centeredCube (centers c) (radii c) (hradii c) : Set
        (SpatialCoordinates d)) ⊆ (Q : Set (SpatialCoordinates d)))
    (_hComplete : ∀ (z' : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r'),
      (∀ i : Fin d, ∃ q : ℚ, z' i = (q : ℝ)) →
      (∃ k : ℤ, r' = (3 : ℝ) ^ k) →
      closure (centeredCube z' r' hr' : Set (SpatialCoordinates d)) ⊆
        (Q : Set (SpatialCoordinates d)) →
      ∃ c : C, centers c = z' ∧ radii c = r')
    (T : Type*) [Countable T]
    (theta : T → H1Function (Q : Set (SpatialCoordinates d)))
    (_hTheta : ∀ b : T,
      ContDiff ℝ (⊤ : ℕ∞) (theta b).toFun ∧
      HasCompactSupport (theta b).toFun ∧
      tsupport (theta b).toFun ⊆ (Q : Set (SpatialCoordinates d)) ∧
      ∀ x ∈ (Q : Set (SpatialCoordinates d)),
        0 ≤ (theta b).toFun x ∧ (theta b).toFun x ≤ 1)
    (_hPlateaus : ∀ (s o : Finset C),
      (⋃ c ∈ s, closure (centeredCube (centers c) (radii c) (hradii c) :
        Set (SpatialCoordinates d))) ⊆
        (⋃ c ∈ o, (centeredCube (centers c) (radii c) (hradii c) :
          Set (SpatialCoordinates d))) →
      closure (⋃ c ∈ o, (centeredCube (centers c) (radii c) (hradii c) :
        Set (SpatialCoordinates d))) ⊆ (Q : Set (SpatialCoordinates d)) →
      ∃ b : T, ∃ V : Set (SpatialCoordinates d),
        IsOpen V ∧
        (⋃ c ∈ s, closure (centeredCube (centers c) (radii c) (hradii c) :
          Set (SpatialCoordinates d))) ⊆ V ∧
        V ⊆ (⋃ c ∈ o, (centeredCube (centers c) (radii c) (hradii c) :
          Set (SpatialCoordinates d))) ∧
        (∀ x ∈ V, (theta b).toFun x = 1) ∧
        tsupport (theta b).toFun ⊆
          (⋃ c ∈ o, (centeredCube (centers c) (radii c) (hradii c) :
            Set (SpatialCoordinates d))))
    (B : T → (J : ℕ) → OddGridIndex d (triadicHalf J) → ℝ)
    (_hBnonneg : ∀ (b : T) (J : ℕ) (k : OddGridIndex d (triadicHalf J)),
      0 ≤ B b J k)
    (_hCellBounds : ∀ (b : T) (J n : ℕ)
        (k : OddGridIndex d (triadicHalf J))
        (w : H1Function
          (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))),
      IsWeaklyHarmonicOn (a n)
        (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) w →
      HasZeroTraceDifferenceOn
        (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) w
        ((theta b).restrict
          (oddGridCell z R hR (triadicHalf J) k).isOpen
          (oddGridCell_subset z hR (triadicHalf J) k)) →
      energy (a n)
          (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) w ≤
        B b J k ∧
      ∀ x ∈ closure (oddGridCell z R hR (triadicHalf J) k :
          Set (SpatialCoordinates d)),
        ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
          (((volume.restrict
            (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal
                ((a n) y * ∑ i : Fin d, (w.grad y i) ^ 2)))
            (Metric.ball x rho)) ≤
            ENNReal.ofReal (B b J k * rho ^ t))
    (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O →
      closure O ⊆ (Q : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → S.space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ)
        (b : T) (J : ℕ)
        (chiH : ℕ → H1Function (Q : Set (SpatialCoordinates d))),
        (∀ x ∈ V, (theta b).toFun x = 1) ∧
        tsupport (theta b).toFun ⊆ O ∧
        (∀ k : OddGridIndex d (triadicHalf J),
          (closure (oddGridCell z R hR (triadicHalf J) k :
            Set (SpatialCoordinates d)) ∩
              {x | 0 < (theta b).toFun x ∧ (theta b).toFun x < 1}).Nonempty →
            closure (oddGridCell z R hR (triadicHalf J) k :
              Set (SpatialCoordinates d)) ⊆ O \ K) ∧
        (∀ n : ℕ, (chi n).val = sobolevDataOfH1 (chiH n)) ∧
        (∀ n : ℕ, ∀ k : OddGridIndex d (triadicHalf J),
          IsWeaklyHarmonicOn (a n)
            (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
            ((chiH n).restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
              (oddGridCell_subset z hR (triadicHalf J) k)) ∧
          HasZeroTraceDifferenceOn
            (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
            ((chiH n).restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
              (oddGridCell_subset z hR (triadicHalf J) k))
            ((theta b).restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
              (oddGridCell_subset z hR (triadicHalf J) k))) ∧
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n) (closure (Q : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] chic n ∧
          (∀ x ∈ (Q : Set (SpatialCoordinates d)),
            0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (Q : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
          responseForm S (aC n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), ∀ rho : ℝ,
            0 < rho → rho ≤ 1 →
            ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal
                ((aC n).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rho) ≤ ENNReal.ofReal (B * rho ^ t)) := by
  simp only
  intro S hS a aC hAC hAcont hell t alpha ht htd halpha halpha1 C hCcount hCdec centers radii hradii hRational hTriadic hContained hComplete T hTcount theta hTheta hPlateaus B hBnonneg hCellBounds K O hK hO hKO hOQ
  let Q : Opens (SpatialCoordinates d) := centeredCube z R hR
  obtain ⟨b, V₀, hV₀open, hKV₀, hV₀O, hthetaV₀, hbsuppO, hbcont, hbcomp, hbsupp,
      hbrange⟩ :=
    aux_catalog_cutoff_existence_plateau_selection hd z R hR C centers radii hradii
      hRational hTriadic hContained hComplete T theta hTheta
      hPlateaus K O hK hO hKO hOQ
  obtain ⟨J, V, hVopen, hKV, hVO, hthetaV, hcellV₀, htransition_cells, hcellsize⟩ :=
    aux_catalog_cutoff_existence_mesh_geometry z R hR (theta b).toFun hbcomp K O V₀ hK
      hO hKO hV₀open hKV₀ hV₀O hthetaV₀ hbsuppO
  have htheta_bounds : ∀ y : SpatialCoordinates d,
      0 ≤ (theta b).toFun y ∧ (theta b).toFun y ≤ 1 := by
    intro y
    by_cases hyQ : y ∈ (centeredCube z R hR : Set (SpatialCoordinates d))
    · exact hbrange y hyQ
    · have hyts : y ∉ tsupport (theta b).toFun := by
        intro hy
        exact hyQ (hbsupp hy)
      have hyzero : (theta b).toFun y = 0 :=
        image_eq_zero_of_notMem_tsupport hyts
      simp [hyzero]
  have hw_exists : ∀ n : ℕ,
      ∃ w : H10Function (centeredCube z R hR : Set (SpatialCoordinates d)),
        ContinuousOn w.toH1Function.toFun
            (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
        (∀ k : OddGridIndex d (triadicHalf J),
          IsWeaklyHarmonicOn (a n)
            (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
            (w.toH1Function.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
              (oddGridCell_subset z hR (triadicHalf J) k)) ∧
          HasZeroTraceDifferenceOn
            (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
            (w.toH1Function.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
              (oddGridCell_subset z hR (triadicHalf J) k))
            ((theta b).restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
              (oddGridCell_subset z hR (triadicHalf J) k)) ∧
          energy (a n)
              (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
              (w.toH1Function.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
                (oddGridCell_subset z hR (triadicHalf J) k)) =
            sInf {e : ℝ | ∃ u : H1Function
              (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)),
              HasZeroTraceDifferenceOn
                (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) u
                ((theta b).restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
                  (oddGridCell_subset z hR (triadicHalf J) k)) ∧
              e = energy (a n)
                (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) u}) ∧
        energy (a n) (centeredCube z R hR : Set (SpatialCoordinates d))
            w.toH1Function =
          ∑ k : OddGridIndex d (triadicHalf J),
            sInf {e : ℝ | ∃ u : H1Function
              (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)),
              HasZeroTraceDifferenceOn
                (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) u
                ((theta b).restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
                  (oddGridCell_subset z hR (triadicHalf J) k)) ∧
              e = energy (a n)
                (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) u} := by
    intro n
    obtain ⟨lam, Lam, hlam, habounds⟩ := hell n
    simpa only using
      (aux_catalog_cutoff_existence_mesh_interpolant hd z R hR J (a n) lam Lam hlam
        (hAcont n) habounds (theta b) hbcont hbcomp hbsupp)
  choose w hwcont hwcell hwenergy using hw_exists
  let chiH : ℕ → H1Function (centeredCube z R hR : Set (SpatialCoordinates d)) :=
    fun n => (w n).toH1Function
  have hmem : ∀ n : ℕ, sobolevDataOfH1 (chiH n) ∈ S.space := by
    intro n
    rw [hS]
    exact sobolevDataOfH1_mem_killed (w n)
  let chi : ℕ → S.space := fun n => ⟨sobolevDataOfH1 (chiH n), hmem n⟩
  let chic : ℕ → SpatialCoordinates d → ℝ := fun n => (chiH n).toFun
  have hcell_dom : ∀ k : OddGridIndex d (triadicHalf J),
      IsOpenBoundedConvexDomain
        (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) := by
    intro k
    dsimp [oddGridCell]
    apply lane2_isOpenBoundedConvexDomain_centeredCube
  have hcell_closureQ : ∀ k : OddGridIndex d (triadicHalf J),
      closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) ⊆
        closure (centeredCube z R hR : Set (SpatialCoordinates d)) := by
    intro k
    exact closure_minimal
      ((oddGridCell_subset z hR (triadicHalf J) k).trans subset_closure)
      isClosed_closure
  have hphi_upper : ∀ k : OddGridIndex d (triadicHalf J), ∀ y,
      ((theta b).restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
        (oddGridCell_subset z hR (triadicHalf J) k)).toFun y ≤ 1 := by
    intro k y
    change (theta b).toFun y ≤ 1
    exact (htheta_bounds y).2
  have hphi_lower : ∀ k : OddGridIndex d (triadicHalf J), ∀ y,
      -((theta b).restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
        (oddGridCell_subset z hR (triadicHalf J) k)).toFun y ≤ 0 := by
    intro k y
    change -(theta b).toFun y ≤ 0
    exact neg_nonpos.mpr (htheta_bounds y).1
  have hcell_range : ∀ n : ℕ, ∀ k : OddGridIndex d (triadicHalf J),
      ∀ x ∈ closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)),
        0 ≤ (chiH n).toFun x ∧ (chiH n).toFun x ≤ 1 := by
    intro n k
    obtain ⟨lam, Lam, hlam, habounds⟩ := hell n
    intro x hx
    exact (aux_catalog_cutoff_existence_harmonic_range
      (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
      (a n) lam Lam (hcell_dom k) hlam (hAcont n)
      (fun y hy => habounds y (oddGridCell_subset z hR (triadicHalf J) k hy))
      ((theta b).restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
        (oddGridCell_subset z hR (triadicHalf J) k))
      ((chiH n).restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
        (oddGridCell_subset z hR (triadicHalf J) k))
      (hphi_upper k) (hphi_lower k) (hwcell n k |>.1)
      (hwcell n k |>.2.1)
      ((hwcont n).mono (hcell_closureQ k))) x hx
  have hchi_range : ∀ n : ℕ, ∀ x ∈ (Q : Set (SpatialCoordinates d)),
      0 ≤ chic n x ∧ chic n x ≤ 1 := by
    intro n x hx
    have hxcl : x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)) :=
      subset_closure hx
    rw [← oddGridCell_closure_iUnion_eq_closure_centeredCube z hR (triadicHalf J)] at hxcl
    rcases mem_iUnion.mp hxcl with ⟨k, hxk⟩
    exact hcell_range n k x hxk
  have hchi_plateau : ∀ n : ℕ, ∀ x ∈ V, chic n x = 1 := by
    intro n x hxV
    have hxQ : x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) :=
      hOQ (subset_closure (hVO hxV))
    have hxcl : x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)) :=
      subset_closure hxQ
    rw [← oddGridCell_closure_iUnion_eq_closure_centeredCube z hR (triadicHalf J)] at hxcl
    rcases mem_iUnion.mp hxcl with ⟨k, hxk⟩
    have hkV₀ := hcellV₀ k ⟨x, ⟨hxk, hxV⟩⟩
    have hphione : ∀ y ∈ (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)),
        ((theta b).restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
          (oddGridCell_subset z hR (triadicHalf J) k)).toFun y = 1 := by
      intro y hy
      change (theta b).toFun y = 1
      exact hthetaV₀ y (hkV₀ (subset_closure hy))
    obtain ⟨lam, Lam, hlam, habounds⟩ := hell n
    exact aux_catalog_cutoff_existence_constant_cell
      (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
      (a n) lam Lam (hcell_dom k) hlam (hAcont n)
      (fun y hy => habounds y (oddGridCell_subset z hR (triadicHalf J) k hy))
      ((theta b).restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
        (oddGridCell_subset z hR (triadicHalf J) k))
      ((chiH n).restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
        (oddGridCell_subset z hR (triadicHalf J) k)) 1 hphione
      (hwcell n k |>.1) (hwcell n k |>.2.1)
      ((hwcont n).mono (hcell_closureQ k)) x hxk
  have hchi_zero_out : ∀ n : ℕ, ∀ x ∈ (Q : Set (SpatialCoordinates d)),
      x ∉ O → chic n x = 0 := by
    intro n x hxQ hxO
    have hxcl : x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)) :=
      subset_closure hxQ
    rw [← oddGridCell_closure_iUnion_eq_closure_centeredCube z hR (triadicHalf J)] at hxcl
    rcases mem_iUnion.mp hxcl with ⟨k, hxk⟩
    have hnot : ¬(closure (oddGridCell z R hR (triadicHalf J) k :
        Set (SpatialCoordinates d)) ∩
        {y | 0 < (theta b).toFun y ∧ (theta b).toFun y < 1}).Nonempty := by
      intro htr
      exact hxO (htransition_cells k htr hxk).1
    have hfx : (theta b).toFun x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hxt
      exact hxO (hbsuppO hxt)
    have htszero := aux_catalog_cutoff_existence_cell_zero
      z R hR J k (theta b).toFun hbcont.continuous.continuousOn
      (fun y hy => htheta_bounds y) x hxk hfx hnot
    have htszero : ∀ y ∈ closure (oddGridCell z R hR (triadicHalf J) k :
        Set (SpatialCoordinates d)), (theta b).toFun y = 0 := htszero
    have hzeroW : ∀ y ∈ (oddGridCell z R hR (triadicHalf J) k :
        Set (SpatialCoordinates d)), (theta b).toFun y = 0 := by
      intro y hy
      exact htszero y (subset_closure hy)
    obtain ⟨lam, Lam, hlam, habounds⟩ := hell n
    have hz := aux_catalog_cutoff_existence_constant_cell
      (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
      (a n) lam Lam (hcell_dom k) hlam (hAcont n)
      (fun y hy => habounds y (oddGridCell_subset z hR (triadicHalf J) k hy))
      ((theta b).restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
        (oddGridCell_subset z hR (triadicHalf J) k))
      ((chiH n).restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
        (oddGridCell_subset z hR (triadicHalf J) k)) 0
      (by intro y hy; exact hzeroW y hy)
      (hwcell n k |>.1) (hwcell n k |>.2.1)
      ((hwcont n).mono (hcell_closureQ k)) x hxk
    exact hz
  have hresp_energy : ∀ n : ℕ,
      responseForm S (aC n) (chi n) (chi n) = energy (a n)
        (centeredCube z R hR : Set (SpatialCoordinates d)) (chiH n) := by
    intro n
    obtain ⟨Cₐ, hCₐ⟩ := lane2_coeff_ae_bound (aC n)
    have hint : ∀ i : Fin d, IntegrableOn
        (fun x => (aC n).val x *
          (((sobolevDataOfH1 (chiH n)).2 i : DomainL2 (centeredCube z R hR)) x *
            ((sobolevDataOfH1 (chiH n)).2 i : DomainL2 (centeredCube z R hR)) x))
        (centeredCube z R hR : Set (SpatialCoordinates d)) volume := by
      intro i
      exact lane2_integrableOn_coeff_mul (Lp.aestronglyMeasurable (aC n).val) hCₐ
        (Lp.memLp ((sobolevDataOfH1 (chiH n)).2 i))
        (Lp.memLp ((sobolevDataOfH1 (chiH n)).2 i))
    have hall : ∀ᵐ x ∂(volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))),
        ∀ i : Fin d,
          (((sobolevDataOfH1 (chiH n)).2 i : DomainL2 (centeredCube z R hR)) x) =
            (chiH n).grad x i := by
      apply ae_all_iff.mpr
      intro i
      exact sobolevDataOfH1_snd_coeFn (chiH n) i
    calc
      responseForm S (aC n) (chi n) (chi n) =
          ∑ i : Fin d, ∫ x in (centeredCube z R hR : Set (SpatialCoordinates d)),
            (aC n).val x *
              (((sobolevDataOfH1 (chiH n)).2 i : DomainL2 (centeredCube z R hR)) x *
                ((sobolevDataOfH1 (chiH n)).2 i : DomainL2 (centeredCube z R hR)) x) := by
        rw [responseForm_apply]
      _ = ∫ x in (centeredCube z R hR : Set (SpatialCoordinates d)),
          ∑ i : Fin d, (aC n).val x *
            (((sobolevDataOfH1 (chiH n)).2 i : DomainL2 (centeredCube z R hR)) x *
              ((sobolevDataOfH1 (chiH n)).2 i : DomainL2 (centeredCube z R hR)) x) := by
        symm
        simpa only [Finset.sum_apply] using
          (integral_finsetSum Finset.univ (fun i _ => hint i))
      _ = energy (a n) (centeredCube z R hR : Set (SpatialCoordinates d)) (chiH n) := by
        apply integral_congr_ae
        filter_upwards [hAC n, hall] with x hx hxi
        simp only [Homogenization.vecDot]
        rw [hx]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hxi i]
  let Bsum : ℝ := ∑ k : OddGridIndex d (triadicHalf J), B b J k
  let Bglobal : ℝ := (2 : ℝ) ^ t * Bsum
  have htpos : 0 < t := by
    have hd1 : (1 : ℝ) < (d : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hd)
    exact (sub_pos.mpr hd1).trans ht
  have hBglobal : 0 ≤ Bglobal := by
    dsimp [Bglobal]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) t) (by
      dsimp [Bsum]
      exact Finset.sum_nonneg (fun k _ => hBnonneg b J k))
  have hglobal_energy : ∀ n : ℕ,
      energy (a n) (centeredCube z R hR : Set (SpatialCoordinates d)) (chiH n) ≤ Bglobal := by
    intro n
    obtain ⟨lam, Lam, hlam, habounds⟩ := hell n
    have hameas : AEStronglyMeasurable (a n)
        (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))) :=
      (hAcont n).aestronglyMeasurable
    have habd : ∀ᵐ x ∂(volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))),
        ‖a n x‖ ≤ Lam := by
      filter_upwards [ae_restrict_mem (centeredCube z R hR).isOpen.measurableSet] with x hx
      rw [Real.norm_eq_abs]
      have hh := habounds x hx
      exact abs_le.mpr (by constructor <;> linarith)
    have hcoord : ∀ i : Fin d, IntegrableOn
        (fun x => a n x * ((chiH n).grad x i * (chiH n).grad x i))
        (centeredCube z R hR : Set (SpatialCoordinates d)) volume := by
      intro i
      exact lane2_integrableOn_coeff_mul hameas habd
        ((chiH n).gradMemL2 i) ((chiH n).gradMemL2 i)
    have hint : IntegrableOn
        (fun x => a n x * Homogenization.vecDot ((chiH n).grad x) ((chiH n).grad x))
        (centeredCube z R hR : Set (SpatialCoordinates d)) volume := by
      have hsum : Integrable
          (fun x => ∑ i : Fin d, a n x *
            ((chiH n).grad x i * (chiH n).grad x i))
          (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))) :=
        integrable_finsetSum Finset.univ (fun i _ => hcoord i)
      simpa only [Homogenization.vecDot, ← Finset.mul_sum] using! hsum
    have hpart := energy_eq_sum_oddGridCell_restrict z hR (triadicHalf J) (a n)
      (chiH n) hint
    calc
      energy (a n) (centeredCube z R hR : Set (SpatialCoordinates d)) (chiH n) =
          ∑ k : OddGridIndex d (triadicHalf J),
            energy (a n) (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
              ((chiH n).restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
                (oddGridCell_subset z hR (triadicHalf J) k)) := hpart
      _ ≤ ∑ k : OddGridIndex d (triadicHalf J), B b J k := by
        apply Finset.sum_le_sum
        intro k hk
        exact (hCellBounds b J n k
          ((chiH n).restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
            (oddGridCell_subset z hR (triadicHalf J) k))
          (hwcell n k |>.1) (hwcell n k |>.2.1)).1
      _ = Bsum := rfl
      _ ≤ Bglobal := by
        dsimp [Bglobal]
        have hpow : 1 ≤ (2 : ℝ) ^ t := Real.one_le_rpow (by norm_num) (by linarith [ht])
        have hsum : 0 ≤ Bsum := by
          dsimp [Bsum]
          exact Finset.sum_nonneg (fun k _ => hBnonneg b J k)
        nlinarith
  have hcell_growth : ∀ n : ℕ, ∀ k : OddGridIndex d (triadicHalf J),
      ∀ x : SpatialCoordinates d,
      ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
      ((volume.restrict (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))).withDensity
        (fun y => ENNReal.ofReal
          (a n y * ∑ i : Fin d,
            (((chiH n).restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
              (oddGridCell_subset z hR (triadicHalf J) k)).grad y i) ^ 2)))
        (Metric.ball x rho) ≤ ENNReal.ofReal (B b J k * (2 * rho) ^ t) := by
    intro n k x rho hrho hrho1
    let cell : Set (SpatialCoordinates d) :=
      (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
    let wk : H1Function cell :=
      (chiH n).restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
        (oddGridCell_subset z hR (triadicHalf J) k)
    let density : SpatialCoordinates d → ENNReal := fun y => ENNReal.ofReal
      (a n y * ∑ i : Fin d, (wk.grad y i) ^ 2)
    have hbound := (hCellBounds b J n k wk
      (by simpa [wk] using (hwcell n k).1)
      (by simpa [wk] using (hwcell n k).2.1)).2
    have hdiam : ∀ (u v : SpatialCoordinates d), u ∈ closure cell → v ∈ closure cell →
        dist u v ≤ R / (2 * (triadicHalf J : ℝ) + 1) := by
      intro u v hu hv
      exact aux_catalog_cutoff_existence_cell_dist z hR (triadicHalf J) k hu hv
    have hside : R / (2 * (triadicHalf J : ℝ) + 1) < 1 := by
      simpa [triadic_denominator J] using hcellsize
    have hgrowth := aux_catalog_cutoff_existence_cell_growth cell
      (by simpa [cell] using (oddGridCell z R hR (triadicHalf J) k).isOpen)
      density (R / (2 * (triadicHalf J : ℝ) + 1)) t hdiam hside htpos.le (B b J k)
      (hBnonneg b J k) (by simpa [density] using hbound) x rho hrho hrho1
    simpa [cell, wk, density] using hgrowth
  have hresp_le : ∀ n : ℕ, responseForm S (aC n) (chi n) (chi n) ≤ Bglobal := by
    intro n
    rw [hresp_energy n]
    exact hglobal_energy n
  have hmeasure_bound : ∀ n : ℕ, ∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
      ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
      ((volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))).withDensity
        (fun y => ENNReal.ofReal
          ((aC n).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
        (Metric.ball x rho) ≤ ENNReal.ofReal (Bglobal * rho ^ t) := by
    intro n x hx rho hrho hrho1
    have hden := aux_catalog_cutoff_existence_density_congr
      ((aC n).val : SpatialCoordinates d → ℝ) (a n)
      (fun y i => ((chi n).val.2 i : DomainL2 (centeredCube z R hR)) y)
      (fun y i => (chiH n).grad y i) (hAC n)
      (fun i => sobolevDataOfH1_snd_coeFn (chiH n) i)
    have hcell : ∀ k : OddGridIndex d (triadicHalf J), ∀ y : SpatialCoordinates d,
        ∀ r : ℝ, 0 < r → r ≤ 1 →
        ((volume.restrict (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))).withDensity
          (fun x => ENNReal.ofReal (a n x * ∑ i : Fin d, ((chiH n).grad x i) ^ 2)))
          (Metric.ball y r) ≤ ENNReal.ofReal (B b J k * (2 * r) ^ t) := by
      intro k y r hr hr1
      simpa only using! hcell_growth n k y r hr hr1
    dsimp [Bglobal, Bsum]
    exact aux_catalog_cutoff_existence_global_measure_bound z R hR (triadicHalf J)
        (fun y => ENNReal.ofReal
          ((aC n).val y * ∑ i : Fin d, ((chi n).val.2 i) y ^ 2))
        (fun y => ENNReal.ofReal (a n y * ∑ i : Fin d, ((chiH n).grad y i) ^ 2))
        hden (fun k : OddGridIndex d (triadicHalf J) => B b J k)
        (fun k => hBnonneg b J k) t htpos.le hcell x rho hrho hrho1
  have hchi_eq : ∀ n : ℕ, (chi n).val = sobolevDataOfH1 (chiH n) := by
    intro n
    rfl
  have hcell_clauses : ∀ n : ℕ, ∀ k : OddGridIndex d (triadicHalf J),
      IsWeaklyHarmonicOn (a n)
          (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
          ((chiH n).restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
            (oddGridCell_subset z hR (triadicHalf J) k)) ∧
      HasZeroTraceDifferenceOn
          (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))
          ((chiH n).restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
            (oddGridCell_subset z hR (triadicHalf J) k))
          ((theta b).restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
            (oddGridCell_subset z hR (triadicHalf J) k)) := by
    intro n k
    exact ⟨(hwcell n k).1, (hwcell n k).2.1⟩
  refine ⟨V, chi, chic, Bglobal, b, J, chiH, ?_⟩
  refine ⟨hthetaV, hbsuppO, htransition_cells, hchi_eq, hcell_clauses, ?_⟩
  refine ⟨hVopen, hKV, hVO, hBglobal, ?_⟩
  intro n
  refine ⟨?_, ?_, hchi_range n, hchi_plateau n, hchi_zero_out n,
    hresp_le n, ?_⟩
  · simpa [chic] using (hwcont n)
  · dsimp [chi, chic]
    exact sobolevDataOfH1_fst_coeFn (chiH n)
  · intro x hx rho hrho hrho1
    exact hmeasure_bound n x hx rho hrho hrho1

end SubdiffusiveProcess.Paper

