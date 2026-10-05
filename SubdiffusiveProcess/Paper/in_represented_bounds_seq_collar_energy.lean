module

public import SubdiffusiveProcess.Paper.in_represented_bounds_seq_collar_profile
public import SubdiffusiveProcess.Paper.Foundations.CollarBufferedProfile

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace Metric
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal BigOperators Topology ContDiff

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The surface cell count times the cell cost has the collar-energy exponent. -/
theorem aux_in_represented_bounds_seq_collar_energy_scale
    (d : ℕ) (hd : 1 ≤ d) (R h : ℝ) (hR : 0 < R) (hh : 0 < h) (eta : ℝ) :
    (R / h) ^ (d - 1) * h ^ ((d : ℝ) - 2 - eta) =
      R ^ (d - 1) * h ^ (-1 - eta) := by
  have hn : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub hd, Nat.cast_one]
  rw [← Real.rpow_natCast, Real.div_rpow hR.le hh.le, div_eq_mul_inv,
    ← Real.rpow_neg hh.le, mul_assoc, ← Real.rpow_add hh]
  have he : -((d - 1 : ℕ) : ℝ) + ((d : ℝ) - 2 - eta) = -1 - eta := by
    rw [hn]
    ring
  rw [he, Real.rpow_natCast]

/-- Finite sum with an explicit constant independent of mesh and cutoff. -/
theorem aux_in_represented_bounds_seq_collar_energy_sum
    {ι : Type*} (I : Finset ι) (e : ι → ℝ)
    (d : ℕ) (hd : 1 ≤ d) (R h r q eta C B K : ℝ)
    (hR : 0 < R) (hh : 0 < h) (hr : 0 < r) (hq : 0 < q)
    (hscale : h = q * r) (hC : 0 ≤ C) (_hB : 0 ≤ B) (hK : 0 ≤ K)
    (hcount : (I.card : ℝ) ≤ B * (R / h) ^ (d - 1))
    (hcell : ∀ i ∈ I, e i ≤ C * K * h ^ ((d : ℝ) - 2 - eta)) :
    ∑ i ∈ I, e i ≤
      (B * C * R ^ (d - 1) * q ^ (-1 - eta)) * K * r ^ (-1 - eta) := by
  have hcost : 0 ≤ C * K * h ^ ((d : ℝ) - 2 - eta) := by positivity
  calc
    ∑ i ∈ I, e i ≤ ∑ _i ∈ I, C * K * h ^ ((d : ℝ) - 2 - eta) :=
      Finset.sum_le_sum hcell
    _ = (I.card : ℝ) * (C * K * h ^ ((d : ℝ) - 2 - eta)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (B * (R / h) ^ (d - 1)) * (C * K * h ^ ((d : ℝ) - 2 - eta)) :=
      mul_le_mul_of_nonneg_right hcount hcost
    _ = (B * C * R ^ (d - 1) * q ^ (-1 - eta)) * K * r ^ (-1 - eta) := by
      calc
        _ = B * C * K * ((R / h) ^ (d - 1) * h ^ ((d : ℝ) - 2 - eta)) := by ring
        _ = B * C * K * (R ^ (d - 1) * h ^ (-1 - eta)) := by
          rw [aux_in_represented_bounds_seq_collar_energy_scale d hd R h hR hh eta]
        _ = _ := by
          rw [hscale, Real.mul_rpow hq.le hr.le]
          ring

/-- Exact paper radii can use the grid five levels below the source mesh. -/
theorem aux_in_represented_bounds_seq_collar_energy_mesh
    (R : ℝ) (hR : 0 < R) (k : ℕ) :
    R / (3 : ℝ) ^ (k + 5) = (10 / 243 : ℝ) * (R / (10 * (3 : ℝ) ^ k)) ∧
    R / (3 : ℝ) ^ (k + 5) ≤ (R / (10 * (3 : ℝ) ^ k)) / 2 ∧
    3 * (R / (10 * (3 : ℝ) ^ k)) ≤ 73 * (R / (3 : ℝ) ^ (k + 5)) := by
  have hp : 0 < (3 : ℝ) ^ k := by positivity
  rw [pow_add]
  norm_num
  constructor
  · ring
  constructor <;> field_simp <;> nlinarith

/-- The SAME harmonic interpolant has the exact collar profile and the required
energy rate at every paper radius. The displayed cell-cost hypothesis is the
conclusion of `aux_lem_cutoffs_rep_collar_cell`. -/
theorem in_represented_bounds_seq_collar_energy
    {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (r : ℝ) (hr : r = R / (10 * (3 : ℝ) ^ k))
    (a : SpatialCoordinates d → ℝ) (ha : Continuous a) (hapos : ∀ x, 0 < a x)
    (phi : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hsmooth : ContDiff ℝ ∞ phi.toFun) (hcompact : HasCompactSupport phi.toFun)
    (hsupport : tsupport phi.toFun ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hrange : ∀ x, 0 ≤ phi.toFun x ∧ phi.toFun x ≤ 1)
    (hzero : ∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
      Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ 3 * r / 2 →
        phi.toFun x = 0)
    (hone : ∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
      5 * r / 2 ≤ Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
        phi.toFun x = 1)
    (eta C K : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hcell : ∀ q : OddGridIndex d (triadicHalf (k + 5)),
      cellDirichletInfimum a
        (oddGridCell z R hR (triadicHalf (k + 5)) q : Set (SpatialCoordinates d))
        (phi.restrict (oddGridCell z R hR (triadicHalf (k + 5)) q).isOpen
          (oddGridCell_subset z hR (triadicHalf (k + 5)) q)) ≤
        C * K * (R / (3 : ℝ) ^ (k + 5)) ^ ((d : ℝ) - 2 - eta)) :
    ∃ w : H10Function (centeredCube z R hR : Set (SpatialCoordinates d)),
      ContinuousOn w.toH1Function.toFun
        (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
      (∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
        0 ≤ w.toH1Function.toFun x ∧ w.toH1Function.toFun x ≤ 1) ∧
      (∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
        Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ r →
          w.toH1Function.toFun x = 0) ∧
      (∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
        3 * r ≤ Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
          w.toH1Function.toFun x = 1) ∧
      (∀ q : OddGridIndex d (triadicHalf (k + 5)),
        IsWeaklyHarmonicOn a
          (oddGridCell z R hR (triadicHalf (k + 5)) q : Set (SpatialCoordinates d))
          (w.toH1Function.restrict (oddGridCell z R hR (triadicHalf (k + 5)) q).isOpen
            (oddGridCell_subset z hR (triadicHalf (k + 5)) q)) ∧
        HasZeroTraceDifferenceOn
          (oddGridCell z R hR (triadicHalf (k + 5)) q : Set (SpatialCoordinates d))
          (w.toH1Function.restrict (oddGridCell z R hR (triadicHalf (k + 5)) q).isOpen
            (oddGridCell_subset z hR (triadicHalf (k + 5)) q))
          (phi.restrict (oddGridCell z R hR (triadicHalf (k + 5)) q).isOpen
            (oddGridCell_subset z hR (triadicHalf (k + 5)) q))) ∧
      energy a (centeredCube z R hR : Set (SpatialCoordinates d)) w.toH1Function ≤
        ((d : ℝ) * 148 * C * R ^ (d - 1) * (10 / 243 : ℝ) ^ (-1 - eta)) *
          K * r ^ (-1 - eta) := by
  have hrpos : 0 < r := by rw [hr]; positivity
  have hm := aux_in_represented_bounds_seq_collar_energy_mesh R hR k
  rw [← hr] at hm
  obtain ⟨w, hwc, hw01, hw0, hw1, hwharm, hwen⟩ :=
    in_represented_bounds_seq_collar_profile hd z R hR (k + 5) r hrpos hm.2.1
      a ha hapos phi hsmooth hcompact hsupport hrange hzero hone
  refine ⟨w, hwc, hw01, hw0, hw1, hwharm, hwen.trans ?_⟩
  let I := aux_in_represented_bounds_seq_collar_count_indices z R hR
    (triadicHalf (k + 5)) phi.toFun
  have hzout : ∀ x, x ∉ (centeredCube z R hR : Set (SpatialCoordinates d)) →
      phi.toFun x = 0 := by
    intro x hx
    by_contra hn
    exact hx (hsupport (subset_tsupport phi.toFun hn))
  have honeF : ∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
      3 * r ≤ Metric.infDist x (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) →
        phi.toFun x = 1 := by
    intro x hx hdist
    rw [aux_lem_20_collar_family_smooth_collar_infDist_frontier_eq d hd z R hR x hx] at hdist
    exact hone x (subset_closure hx) (by linarith)
  have hcount := in_represented_bounds_seq_collar_count hd z R hR
    (triadicHalf (k + 5)) (R / (3 : ℝ) ^ (k + 5)) (by positivity)
    (by rw [triadic_denominator]; field_simp) r hrpos 73 hm.2.2 phi.toFun hzout honeF
  have hden : 2 * (triadicHalf (k + 5) : ℝ) + 1 = R / (R / (3 : ℝ) ^ (k + 5)) := by
    rw [triadic_denominator]
    field_simp
  have hcount' : (I.card : ℝ) ≤ (d : ℝ) * 148 *
      (R / (R / (3 : ℝ) ^ (k + 5))) ^ (d - 1) := by
    convert hcount using 1 ; norm_num [I, hden]
  exact aux_in_represented_bounds_seq_collar_energy_sum I _ d (by omega)
    R (R / (3 : ℝ) ^ (k + 5)) r (10 / 243) eta C ((d : ℝ) * 148) K
    hR (by positivity) hrpos (by norm_num) hm.1 hC (by positivity) hK hcount'
    (fun q _ => hcell q)

end SubdiffusiveProcess.Paper
