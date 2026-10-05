module

public import SubdiffusiveProcess.MultiplicativeChaos.ChaosBasic
public import Mathlib.MeasureTheory.Integral.Average

@[expose] public section

/-!
# The per-cutoff Campanato bound

Campanato's criterion produces a Hölder representative of a function from a
bound on its mean oscillation.  At finite cutoff the killed resolvent is
already continuous up to the boundary of the cube, so the representative IS
the function there, and the criterion becomes a pointwise Hölder bound for the
resolvent itself.
-/

open MeasureTheory Set
open scoped ENNReal NNReal Topology

noncomputable section
namespace SubdiffusiveProcess

variable {d : ℕ}

/-- Two functions that agree almost everywhere and are continuous on the
closure of an open set agree on that closure. -/
theorem eqOn_closure_of_ae_eq {U : Set (SpatialCoordinates d)} (hU : IsOpen U)
    (u v : SpatialCoordinates d → ℝ)
    (hu : ContinuousOn u (closure U)) (hv : ContinuousOn v (closure U))
    (hae : u =ᵐ[volume] v) : Set.EqOn u v (closure U) := by
  have hUeq : Set.EqOn u v U := by
    intro x hx
    by_contra hne
    set c : ℝ := |u x - v x| / 2 with hcdef
    have hc : 0 < c := by
      have : 0 < |u x - v x| := abs_pos.mpr (sub_ne_zero.mpr hne)
      rw [hcdef]; linarith
    have hcontabs : ContinuousOn (fun w => |u w - v w|) U :=
      ((hu.mono subset_closure).sub (hv.mono subset_closure)).abs
    have hW : IsOpen (U ∩ (fun w => |u w - v w|) ⁻¹' (Set.Ioi c)) :=
      hcontabs.isOpen_inter_preimage hU isOpen_Ioi
    have hxW : x ∈ U ∩ (fun w => |u w - v w|) ⁻¹' (Set.Ioi c) := by
      refine ⟨hx, ?_⟩
      simp only [Set.mem_preimage, Set.mem_Ioi, hcdef]
      have : 0 < |u x - v x| := abs_pos.mpr (sub_ne_zero.mpr hne)
      linarith
    have hWpos : 0 < volume (U ∩ (fun w => |u w - v w|) ⁻¹' (Set.Ioi c)) :=
      hW.measure_pos volume ⟨x, hxW⟩
    have hWnull : volume (U ∩ (fun w => |u w - v w|) ⁻¹' (Set.Ioi c)) = 0 := by
      refine measure_mono_null (fun w hw => ?_) (ae_iff.mp hae)
      have hwc : c < |u w - v w| := hw.2
      simp only [mem_ofPred_eq]
      intro heq
      rw [heq] at hwc
      simp at hwc
      linarith
    exact absurd hWnull (ne_of_gt hWpos)
  exact hUeq.of_subset_closure hu hv subset_closure (subset_refl _)

/-- A Hölder bound makes a function continuous. -/
theorem continuous_of_holder (v : SpatialCoordinates d → ℝ) {K alpha : ℝ}
    (hK : 0 ≤ K) (halpha : 0 < alpha)
    (hbound : ∀ x y : SpatialCoordinates d, |v x - v y| ≤ K * dist x y ^ alpha) :
    Continuous v := by
  refine Metric.continuous_iff.mpr fun x eps heps => ?_
  rcases eq_or_lt_of_le hK with hK0 | hK0
  · refine ⟨1, one_pos, fun y _ => ?_⟩
    have hb := hbound y x
    rw [← hK0, zero_mul] at hb
    have : |v y - v x| = 0 := le_antisymm hb (abs_nonneg _)
    rw [Real.dist_eq]
    rw [this] at *
    linarith [heps]
  · refine ⟨(eps / K) ^ (1 / alpha), by positivity, fun y hy => ?_⟩
    have hdnn : (0 : ℝ) ≤ dist y x := dist_nonneg
    have hlt : dist y x ^ alpha < eps / K := by
      have hmono := Real.rpow_lt_rpow hdnn hy halpha
      rwa [← Real.rpow_mul (by positivity), one_div,
        inv_mul_cancel₀ (ne_of_gt halpha), Real.rpow_one] at hmono
    calc dist (v y) (v x) = |v y - v x| := Real.dist_eq _ _
      _ ≤ K * dist y x ^ alpha := hbound y x
      _ < K * (eps / K) := by
          exact mul_lt_mul_of_pos_left hlt hK0
      _ = eps := by field_simp

/-- The per-cutoff Campanato bound: a Hölder representative transfers its
bound to a function that is continuous on the closed cube. -/
theorem cutoff_campanato_bound
    {z : SpatialCoordinates d} {rQ : ℝ} (hrQ : 0 < rQ)
    {alpha : ℝ} (halpha : 0 < alpha)
    (u : SpatialCoordinates d → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hcont : ContinuousOn u
      (closure (centeredCube z rQ hrQ : Set (SpatialCoordinates d))))
    (v : SpatialCoordinates d → ℝ) (hvae : v =ᵐ[volume] u)
    (hvholder : ∀ x y : SpatialCoordinates d,
      |v x - v y| ≤ K * dist x y ^ alpha) :
    ∀ x ∈ closure (centeredCube z rQ hrQ : Set (SpatialCoordinates d)),
      ∀ y ∈ closure (centeredCube z rQ hrQ : Set (SpatialCoordinates d)),
        |u x - u y| ≤ K * dist x y ^ alpha := by
  have hopen : IsOpen (centeredCube z rQ hrQ : Set (SpatialCoordinates d)) := by
    rw [centeredCube_coe_eq_ball]
    exact Metric.isOpen_ball
  have hvcont : Continuous v := continuous_of_holder v hK halpha hvholder
  have heq : Set.EqOn u v
      (closure (centeredCube z rQ hrQ : Set (SpatialCoordinates d))) :=
    eqOn_closure_of_ae_eq hopen u v hcont hvcont.continuousOn hvae.symm
  intro x hx y hy
  rw [heq hx, heq hy]
  exact hvholder x y

end SubdiffusiveProcess
