module

public import SubdiffusiveProcess.Paper.lfgc_obad_bound

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# Parts of the single-point assembly: base tail, endpoint closeness, bad-event bound
-/

open MeasureTheory Filter Topology SubdiffusiveProcess
open scoped ENNReal

namespace SubdiffusiveProcess.Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
/-- Large root statistic forces a large selected coordinate. -/
theorem aux_lfgc_single_parts_rootX_gt_subset [_instPreserved0 : MeasurableSpace C(SpatialCoordinates d, ℝ)] [_instPreserved1 : BorelSpace C(SpatialCoordinates d, ℝ)] [NeZero d] (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (sigma : ℝ) (T : ℕ) (offset : Fin T → ℤ) (shift : Fin T → SpatialCoordinates d) (N : ℕ)
    (n : ℤ) (z : SpatialCoordinates d) {θ₀ t : ℝ} (hθ₀ : 0 < θ₀) (ht : 0 ≤ t)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) :
    {omega | t < aux_lfgc_root_impl_rootX I M sigma T offset shift N n z (2 / θ₀) H omega} ⊆
      ⋃ q : Fin T × aux_lfgc_root_stat_SelIdx d,
        {omega | t * θ₀ / 2 < |aux_lfgc_root_stat_selOf (aux_lfgc_root_stat_bandCoords I M H sigma sigma T offset shift N n z omega) q|} := by
  intro omega homega
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion] at homega ⊢
  by_contra hno
  push Not at hno
  have hle : ‖aux_lfgc_root_stat_selOf (aux_lfgc_root_stat_bandCoords I M H sigma sigma T offset shift N n z omega)‖ ≤ t * θ₀ / 2 := by
    exact (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun q => by
      rw [Real.norm_eq_abs]; exact hno q
  have := aux_lfgc_root_stat_phiStat_le_of_norm_le (show (0 : ℝ) ≤ 2 / θ₀ by positivity) hle
  unfold aux_lfgc_root_impl_rootX at homega
  have e : 2 / θ₀ * (t * θ₀ / 2) = t := by field_simp
  linarith

end SubdiffusiveProcess.Paper
namespace SubdiffusiveProcess.Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- Base tail of the root statistic from the coordinate tails. -/
theorem aux_lfgc_single_parts_rootX_base_tail [NeZero d] (P : Measure (BilateralField d)) (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (sigma : ℝ) (T : ℕ) (offset : Fin T → ℤ)
    (shift : Fin T → SpatialCoordinates d) (N : ℕ) (n : ℤ) (z : SpatialCoordinates d)
    {θ₀ t p B : ℝ} (hθ₀ : 0 < θ₀) (ht : 0 < t) (hs1 : t * θ₀ / 2 ≤ 1)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hq : ∀ q : Fin T × aux_lfgc_root_stat_SelIdx d, ∀ s : ℝ, 0 < s → s ≤ 1 →
      P {omega | s < |aux_lfgc_root_stat_selOf (aux_lfgc_root_stat_bandCoords I M H sigma sigma T offset shift N n z omega) q|} ≤
        (ENNReal.ofReal B / ENNReal.ofReal (s ^ 2)) ^ p) :
    P {omega | t < aux_lfgc_root_impl_rootX I M sigma T offset shift N n z (2 / θ₀) H omega} ≤
      (Fintype.card (Fin T × aux_lfgc_root_stat_SelIdx d) : ℝ≥0∞) *
        (ENNReal.ofReal B / ENNReal.ofReal ((t * θ₀ / 2) ^ 2)) ^ p := by
  refine (measure_mono (aux_lfgc_single_parts_rootX_gt_subset I M sigma T offset shift N n z hθ₀ ht.le H)).trans
    ((measure_iUnion_fintype_le _ _).trans ?_)
  calc ∑ q : Fin T × aux_lfgc_root_stat_SelIdx d, P {omega | t * θ₀ / 2 <
        |aux_lfgc_root_stat_selOf (aux_lfgc_root_stat_bandCoords I M H sigma sigma T offset shift N n z omega) q|}
      ≤ ∑ _q : Fin T × aux_lfgc_root_stat_SelIdx d, (ENNReal.ofReal B / ENNReal.ofReal ((t * θ₀ / 2) ^ 2)) ^ p :=
        Finset.sum_le_sum fun q _ => hq q _ (by positivity) hs1
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The endpoint is close to the statistic when the infrared tail oscillates little. -/
theorem lfgc_single_parts [NeZero d] (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (sigma : ℝ) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) (T : ℕ) (offset : Fin T → ℤ)
    (shift : Fin T → SpatialCoordinates d) (N : ℕ) (n : ℤ) (z : SpatialCoordinates d)
    {θ₀ ε : ℝ} (hθ₀ : 0 < θ₀) (hθ₀2 : θ₀ ≤ 2) (hε : 0 ≤ ε)
    (hslack : 2 / θ₀ * aux_lfgc_root_impl_tolSlack ε ≤ 1 / 32)
    (H H' : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (hosc : aux_lfgc_root_impl_allOscLe T offset shift n z H H' ε omega) :
    |aux_lfgc_root_impl_rootX I M sigma T offset shift N n z (2 / θ₀) H' omega -
      aux_lfgc_root_impl_rootX I M sigma T offset shift N n z (2 / θ₀) H omega| ≤ 1 / 32 := by
  have h1 := lfgc_root_impl hsigma hθ₀ hθ₀2 hε H H' omega hosc (I := I) (M := M) (N := N)
  have h2 := lfgc_root_impl hsigma hθ₀ hθ₀2 hε H' H omega hosc.symm (I := I) (M := M) (N := N)
  rw [abs_le]; constructor <;> linarith

end SubdiffusiveProcess.Paper
