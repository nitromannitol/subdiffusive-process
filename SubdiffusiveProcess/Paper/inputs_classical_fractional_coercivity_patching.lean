import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Sobolev.DomainPoincare
import SubdiffusiveProcess.Lane2.OddExtension
import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
import SubdiffusiveProcess.Sobolev.MeanZeroRestrict
import SubdiffusiveProcess.Sobolev.AffineResponses
import SubdiffusiveProcess.Paper.inputs_classical_e4_h1_finite




set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace Paper
namespace FCP

variable {d : ℕ}

/-- Lattice centres `z + n / 2`. -/
def aux_fcp_center (z : SpatialCoordinates d) (n : Fin d → ℤ) : SpatialCoordinates d :=
  fun j => z j + (n j : ℝ) / 2

/-- The index aux_fcp_box `|n_j| ≤ N`. -/
def aux_fcp_box (d N : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) N

/-- The finite set of unit-cube centres. -/
def aux_fcp_centers (z : SpatialCoordinates d) (N : ℕ) : Finset (SpatialCoordinates d) :=
  (aux_fcp_box d N).image (aux_fcp_center z)

/-- The scalar Gagliardo integrand of `cubeFractionalL2Seminorm` (one component). -/
def aux_fcp_gq (s : ℝ) (g : SpatialCoordinates d → ℝ) (x y : SpatialCoordinates d) : ℝ≥0∞ :=
  ENNReal.ofReal ((g x - g y) ^ 2) /
    (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^ ((d : ℝ) + 2 * s)

/-- Unit cube around a centre. -/
abbrev aux_fcp_ucube (p : SpatialCoordinates d) : Set (SpatialCoordinates d) :=
  (centeredCube p 1 one_pos : Set (SpatialCoordinates d))

/-- Mean of `g` over the unit cube (volume one). -/
def aux_fcp_umean (g : SpatialCoordinates d → ℝ) (p : SpatialCoordinates d) : ℝ :=
  ∫ x in aux_fcp_ucube p, g x

/-! ### Geometry of the lattice cover -/

/-- Every point of `Q` has a centre within sup-distance `1/4`, and then every `y` within
sup-distance `1/4` of `x` lies in the same unit cube. -/
theorem aux_fcp_cover_near (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (N : ℕ) (hN : r + 1 ≤ N)
    (x : SpatialCoordinates d) (hx : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (y : SpatialCoordinates d) (hxy : ∀ j, |x j - y j| < 1 / 4) :
    ∃ p ∈ aux_fcp_centers z N, x ∈ aux_fcp_ucube p ∧ y ∈ aux_fcp_ucube p := by
  have hxball : x ∈ Metric.ball z (r / 2) := hx
  have hxcoord : ∀ j, |x j - z j| < r / 2 := by
    rw [Metric.mem_ball, dist_pi_lt_iff (half_pos hr)] at hxball
    intro j
    have h := hxball j
    rwa [Real.dist_eq] at h
  let n : Fin d → ℤ := fun j => round (2 * (x j - z j))
  let p : SpatialCoordinates d := aux_fcp_center z n
  have hround : ∀ j, |2 * (x j - z j) - (n j : ℝ)| ≤ 1 / 2 := fun j => by
    simpa [n] using abs_sub_round (2 * (x j - z j))
  have hnbound : ∀ j, |((n j : ℤ) : ℝ)| < (N : ℝ) := by
    intro j
    have h1 : |((n j : ℤ) : ℝ)| ≤ |2 * (x j - z j)| + 1 / 2 := by
      have habs : |((n j : ℤ) : ℝ)| = |2 * (x j - z j) + (((n j : ℤ) : ℝ) - 2 * (x j - z j))| := by ring_nf
      rw [habs]
      calc |2 * (x j - z j) + (((n j : ℤ) : ℝ) - 2 * (x j - z j))|
          ≤ |2 * (x j - z j)| + |((n j : ℤ) : ℝ) - 2 * (x j - z j)| := abs_add_le _ _
        _ = |2 * (x j - z j)| + |2 * (x j - z j) - ((n j : ℤ) : ℝ)| := by rw [abs_sub_comm]
        _ ≤ |2 * (x j - z j)| + 1 / 2 := by linarith [hround j]
    have h2 : |2 * (x j - z j)| < r + 1 / 2 := by
      rw [abs_mul, abs_of_pos (show (0:ℝ) < 2 by norm_num)]
      linarith [hxcoord j]
    linarith [h1, h2, hN]
  have hp : p ∈ aux_fcp_centers z N := by
    show p ∈ (aux_fcp_box d N).image (aux_fcp_center z)
    refine Finset.mem_image.mpr ⟨n, ?_, rfl⟩
    show n ∈ Fintype.piFinset (fun _ => Finset.Icc (-(N : ℤ)) N)
    rw [Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_Icc]
    have hlt := abs_lt.mp (hnbound j)
    constructor
    · have h2 : ((-(N : ℤ) : ℤ) : ℝ) ≤ (n j : ℝ) := by push_cast; linarith [hlt.1]
      exact_mod_cast h2
    · have h1 : (n j : ℝ) ≤ (N : ℝ) := le_of_lt hlt.2
      exact_mod_cast h1
  have hxpj : ∀ j, |x j - p j| ≤ 1 / 4 := by
    intro j
    have heq : x j - p j = (2 * (x j - z j) - (n j : ℝ)) / 2 := by
      show x j - (z j + (n j : ℝ) / 2) = _
      ring
    rw [heq, abs_div, abs_of_pos (show (0:ℝ) < 2 by norm_num)]
    have := div_le_div_of_nonneg_right (hround j) (show (0:ℝ) ≤ 2 by norm_num)
    linarith
  have hxp : x ∈ aux_fcp_ucube p := by
    show x ∈ Metric.ball p (1 / 2)
    rw [Metric.mem_ball, dist_pi_lt_iff (show (0:ℝ) < 1/2 by norm_num)]
    intro j
    rw [Real.dist_eq]
    linarith [hxpj j]
  have hyp : y ∈ aux_fcp_ucube p := by
    show y ∈ Metric.ball p (1 / 2)
    rw [Metric.mem_ball, dist_pi_lt_iff (show (0:ℝ) < 1/2 by norm_num)]
    intro j
    rw [Real.dist_eq]
    have htri : |y j - p j| ≤ |x j - p j| + |x j - y j| := by
      have h1 : y j - p j = (x j - p j) + (y j - x j) := by ring
      rw [h1]
      calc |(x j - p j) + (y j - x j)| ≤ |x j - p j| + |y j - x j| := abs_add_le _ _
        _ = |x j - p j| + |x j - y j| := by rw [abs_sub_comm (y j) (x j)]
    linarith [htri, hxpj j, hxy j]
  exact ⟨p, hp, hxp, hyp⟩

/-- Unit cubes with `n 0 = N` miss `Q`. -/
theorem aux_fcp_outer_disjoint (hd : 2 ≤ d) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (N : ℕ)
    (hN : r + 1 ≤ N) (n : Fin d → ℤ) (hn : n ⟨0, by omega⟩ = N) :
    Disjoint (aux_fcp_ucube (aux_fcp_center z n)) (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  rw [Set.disjoint_left]
  intro x hxu hxq
  have huc : dist x (aux_fcp_center z n) < (1 : ℝ) / 2 := Metric.mem_ball.mp hxu
  have hqc : dist x z < r / 2 := Metric.mem_ball.mp hxq
  have h1 := (dist_pi_lt_iff (by norm_num : (0 : ℝ) < 1 / 2)).mp huc ⟨0, by omega⟩
  have h2 := (dist_pi_lt_iff (half_pos hr)).mp hqc ⟨0, by omega⟩
  rw [Real.dist_eq] at h1 h2
  have h1a : aux_fcp_center z n ⟨0, by omega⟩ - 1 / 2 < x ⟨0, by omega⟩ := by
    linarith [(abs_lt.mp h1).1]
  have h2a : x ⟨0, by omega⟩ < z ⟨0, by omega⟩ + r / 2 := by
    linarith [(abs_lt.mp h2).2]
  have hc : aux_fcp_center z n ⟨0, by omega⟩ = z ⟨0, by omega⟩ + (N : ℝ) / 2 := by
    unfold aux_fcp_center
    rw [hn]
    push_cast
    ring
  have hN' : r / 2 + 1 / 2 ≤ (N : ℝ) / 2 := by linarith
  linarith [h1a, h2a, hc, hN']

/-- Consecutive centres along `e_0` overlap in a set of volume `1/2`. -/
theorem aux_fcp_step_overlap_volume (hd : 2 ≤ d) (z : SpatialCoordinates d) (n : Fin d → ℤ) :
    volume.real (aux_fcp_ucube (aux_fcp_center z n) ∩ aux_fcp_ucube (aux_fcp_center z (n + Pi.single ⟨0, by omega⟩ 1))) = 1 / 2 := by
  have hi0lt : (0 : ℕ) < d := by omega
  have h1 : aux_fcp_ucube (aux_fcp_center z n) = Set.pi Set.univ
      (fun i : Fin d => Set.Ioo ((aux_fcp_center z n) i - 1 / 2) ((aux_fcp_center z n) i + 1 / 2)) :=
    centeredCube_eq_pi _ one_pos
  have h2 : aux_fcp_ucube (aux_fcp_center z (n + Pi.single ⟨0, hi0lt⟩ (1 : ℤ))) = Set.pi Set.univ
      (fun i : Fin d => Set.Ioo ((aux_fcp_center z (n + Pi.single ⟨0, hi0lt⟩ (1 : ℤ))) i - 1 / 2)
        ((aux_fcp_center z (n + Pi.single ⟨0, hi0lt⟩ (1 : ℤ))) i + 1 / 2)) :=
    centeredCube_eq_pi _ one_pos
  have hc2 : ∀ i : Fin d, aux_fcp_center z (n + Pi.single ⟨0, hi0lt⟩ (1 : ℤ)) i =
      aux_fcp_center z n i + (if i = ⟨0, hi0lt⟩ then (1 / 2 : ℝ) else 0) := by
    intro i
    simp only [aux_fcp_center, Pi.add_apply]
    by_cases h : i = ⟨0, hi0lt⟩
    · subst h
      rw [Pi.single_eq_same, if_pos rfl]
      push_cast
      ring
    · rw [Pi.single_eq_of_ne h, if_neg h]
      push_cast
      ring
  have hcnn : ∀ i : Fin d, (0 : ℝ) ≤ (if i = ⟨0, hi0lt⟩ then (1 / 2 : ℝ) else 0) := by
    intro i
    split_ifs <;> norm_num
  have hset : (Set.pi Set.univ (fun i : Fin d => Set.Ioo ((aux_fcp_center z n) i - 1 / 2) ((aux_fcp_center z n) i + 1 / 2) ∩
      Set.Ioo ((aux_fcp_center z (n + Pi.single ⟨0, hi0lt⟩ (1 : ℤ))) i - 1 / 2)
        ((aux_fcp_center z (n + Pi.single ⟨0, hi0lt⟩ (1 : ℤ))) i + 1 / 2))) =
      Set.pi Set.univ (fun i : Fin d =>
        Set.Ioo ((aux_fcp_center z n) i + (if i = ⟨0, hi0lt⟩ then (1 / 2 : ℝ) else 0) - 1 / 2)
          ((aux_fcp_center z n) i + 1 / 2)) := by
    apply Set.pi_congr rfl
    intro i _
    rw [hc2 i]
    apply Set.ext
    intro x
    simp only [Set.mem_inter_iff, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨ha, hb⟩, hc, hd'⟩
      exact ⟨hc, hb⟩
    · rintro ⟨ha, hb⟩
      exact ⟨⟨by linarith [hcnn i], hb⟩, ha, by linarith [hcnn i]⟩
  have hvol : volume (Set.pi Set.univ (fun i : Fin d =>
      Set.Ioo ((aux_fcp_center z n) i + (if i = ⟨0, hi0lt⟩ then (1 / 2 : ℝ) else 0) - 1 / 2)
        ((aux_fcp_center z n) i + 1 / 2))) = ENNReal.ofReal (1 / 2) := by
    rw [Real.volume_pi_Ioo]
    refine (Finset.prod_eq_single ⟨0, hi0lt⟩ ?_ ?_).trans ?_
    · intro b _ hb
      rw [if_neg hb,
        show ((aux_fcp_center z n) b + 1 / 2) - ((aux_fcp_center z n) b + 0 - 1 / 2) = 1 by ring,
        ENNReal.ofReal_one]
    · intro h
      exact absurd (Finset.mem_univ _) h
    · rw [if_pos rfl,
        show ((aux_fcp_center z n) ⟨0, hi0lt⟩ + 1 / 2) -
          ((aux_fcp_center z n) ⟨0, hi0lt⟩ + 1 / 2 - 1 / 2) = 1 / 2 by ring]
  rw [h1, h2, ← Set.pi_inter_distrib, hset, Measure.real, hvol, ENNReal.toReal_ofReal (by norm_num)]

/-- Two means that both approximate `g` in L2 on a common set of volume `1/2` are close:
`(m - m')^2 ≤ 4 (A + A')` where `A, A'` bound the squared L2 deviations on the two cubes. -/
theorem aux_fcp_mean_step (g : SpatialCoordinates d → ℝ) (S T : Set (SpatialCoordinates d))
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hST : volume.real (S ∩ T) = 1 / 2)
    (hSf : volume S < ⊤) (hTf : volume T < ⊤)
    (hg : IntegrableOn (fun x => g x ^ 2) (S ∪ T))
    (hgi : IntegrableOn g (S ∪ T))
    (m m' A A' : ℝ) (hA : ∫ x in S, (g x - m) ^ 2 ≤ A) (hA' : ∫ x in T, (g x - m') ^ 2 ≤ A') :
    (m - m') ^ 2 ≤ 4 * (A + A') := by
  have hSg2 : IntegrableOn (fun x => g x ^ 2) S := hg.mono_set (Set.subset_union_left)
  have hTg2 : IntegrableOn (fun x => g x ^ 2) T := hg.mono_set (Set.subset_union_right)
  have hSg : IntegrableOn g S := hgi.mono_set (Set.subset_union_left)
  have hTg : IntegrableOn g T := hgi.mono_set (Set.subset_union_right)
  have hSm : IntegrableOn (fun _ : SpatialCoordinates d => m) S :=
    IntegrableOn.of_bound hSf aestronglyMeasurable_const ‖m‖
      (Filter.Eventually.of_forall fun x => le_refl ‖m‖)
  have hTm' : IntegrableOn (fun _ : SpatialCoordinates d => m') T :=
    IntegrableOn.of_bound hTf aestronglyMeasurable_const ‖m'‖
      (Filter.Eventually.of_forall fun x => le_refl ‖m'‖)
  have hS1 : IntegrableOn (fun x => (g x - m) ^ 2) S := by
    have h : (fun x : SpatialCoordinates d => (g x - m) ^ 2)
        = fun x => g x ^ 2 - (2 * m) * g x + m * m := by funext x; ring
    rw [h]
    exact (hSg2.sub (hSg.const_mul (2 * m))).add (hSm.const_mul m)
  have hT1 : IntegrableOn (fun x => (g x - m') ^ 2) T := by
    have h : (fun x : SpatialCoordinates d => (g x - m') ^ 2)
        = fun x => g x ^ 2 - (2 * m') * g x + m' * m' := by funext x; ring
    rw [h]
    exact (hTg2.sub (hTg.const_mul (2 * m'))).add (hTm'.const_mul m')
  have hSTsub : (S ∩ T) ⊆ S := Set.inter_subset_left
  have hSTsub' : (S ∩ T) ⊆ T := Set.inter_subset_right
  have hSTfin : volume (S ∩ T) < ⊤ := lt_of_le_of_lt (measure_mono Set.inter_subset_left) hSf
  have hSTc : IntegrableOn (fun _ : SpatialCoordinates d => (m - m') ^ 2) (S ∩ T) :=
    IntegrableOn.of_bound hSTfin aestronglyMeasurable_const ‖(m - m') ^ 2‖
      (Filter.Eventually.of_forall fun x => le_refl ‖(m - m') ^ 2‖)
  have hST2 : IntegrableOn (fun x => 2 * (g x - m) ^ 2 + 2 * (g x - m') ^ 2) (S ∩ T) :=
    ((hS1.mono_set hSTsub).const_mul 2).add ((hT1.mono_set hSTsub').const_mul 2)
  have hstepB : ∫ x in S ∩ T, (m - m') ^ 2 ≤
      ∫ x in S ∩ T, (2 * (g x - m) ^ 2 + 2 * (g x - m') ^ 2) := by
    apply integral_mono hSTc hST2
    intro x
    have e : m - m' = (g x - m') - (g x - m) := by ring
    rw [e]
    nlinarith [sq_nonneg ((g x - m') - (g x - m)), sq_nonneg ((g x - m') + (g x - m))]
  have hB' : ∫ x in S ∩ T, (2 * (g x - m) ^ 2 + 2 * (g x - m') ^ 2)
      = 2 * (∫ x in S ∩ T, (g x - m) ^ 2) + 2 * (∫ x in S ∩ T, (g x - m') ^ 2) := by
    rw [integral_add ((hS1.mono_set hSTsub).const_mul 2) ((hT1.mono_set hSTsub').const_mul 2),
        integral_const_mul, integral_const_mul]
  have hmono1 : ∫ x in S ∩ T, (g x - m) ^ 2 ≤ ∫ x in S, (g x - m) ^ 2 :=
    setIntegral_mono_set hS1 (ae_of_all _ fun x => sq_nonneg _)
      (Filter.Eventually.of_forall fun x hx => hx.1)
  have hmono2 : ∫ x in S ∩ T, (g x - m') ^ 2 ≤ ∫ x in T, (g x - m') ^ 2 :=
    setIntegral_mono_set hT1 (ae_of_all _ fun x => sq_nonneg _)
      (Filter.Eventually.of_forall fun x hx => hx.2)
  have hconst : ∫ x in S ∩ T, (m - m') ^ 2 = volume.real (S ∩ T) * (m - m') ^ 2 := by
    rw [setIntegral_const, smul_eq_mul]
  have hfin : volume.real (S ∩ T) * (m - m') ^ 2 ≤ 2 * A + 2 * A' := by
    calc volume.real (S ∩ T) * (m - m') ^ 2
        = ∫ x in S ∩ T, (m - m') ^ 2 := hconst.symm
      _ ≤ ∫ x in S ∩ T, (2 * (g x - m) ^ 2 + 2 * (g x - m') ^ 2) := hstepB
      _ = 2 * (∫ x in S ∩ T, (g x - m) ^ 2) + 2 * (∫ x in S ∩ T, (g x - m') ^ 2) := hB'
      _ ≤ 2 * A + 2 * A' := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left (le_trans hmono1 hA) (by norm_num)
          · exact mul_le_mul_of_nonneg_left (le_trans hmono2 hA') (by norm_num)
  rw [hST] at hfin
  nlinarith [hfin]

/-! ### Sub-lemmas for the L2 chain and the near/far split -/

/-- Every point of `Q` lies in some unit cube of the cover. -/
theorem aux_fcp_cover_Q (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (N : ℕ) (hN : r + 1 ≤ N) :
    (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ ⋃ p ∈ aux_fcp_centers z N, aux_fcp_ucube p := by
  intro x hx
  obtain ⟨p, hp, hxp, -⟩ := aux_fcp_cover_near z hr N hN x hx x (fun j => by simp)
  exact Set.mem_biUnion hp hxp

/-- The L2 mass on `Q` is at most the sum of the masses on the covering cubes. -/
theorem aux_fcp_l2_le_sum_cubes (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (N : ℕ) (hN : r + 1 ≤ N)
    (g : SpatialCoordinates d → ℝ)
    (hg2 : Integrable (fun x => g x ^ 2)) :
    ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), g x ^ 2 ≤
      ∑ p ∈ aux_fcp_centers z N, ∫ x in aux_fcp_ucube p, g x ^ 2 := by
  have hQmeas : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen.measurableSet
  have hFint : ∀ p ∈ aux_fcp_centers z N, Integrable ((aux_fcp_ucube p).indicator (fun x => g x ^ 2)) :=
    fun p _ => hg2.indicator (centeredCube p 1 one_pos).isOpen.measurableSet
  have hsumint : Integrable (fun x => ∑ p ∈ aux_fcp_centers z N, (aux_fcp_ucube p).indicator (fun x => g x ^ 2) x) :=
    integrable_finset_sum _ hFint
  have hpt : ∀ x, (centeredCube z r hr : Set (SpatialCoordinates d)).indicator (fun x => g x ^ 2) x ≤
      ∑ p ∈ aux_fcp_centers z N, (aux_fcp_ucube p).indicator (fun x => g x ^ 2) x := by
    intro x
    by_cases hx : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d))
    · rw [Set.indicator_of_mem hx]
      obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp (aux_fcp_cover_Q z hr N hN hx)
      refine le_trans (le_of_eq ?_) (Finset.single_le_sum (fun q _ => ?_) hp)
      · rw [Set.indicator_of_mem hxp]
      · by_cases h : x ∈ aux_fcp_ucube q
        · rw [Set.indicator_of_mem h]; exact sq_nonneg _
        · rw [Set.indicator_of_notMem h]
    · rw [Set.indicator_of_notMem hx]
      exact Finset.sum_nonneg fun q _ => by
        by_cases h : x ∈ aux_fcp_ucube q
        · rw [Set.indicator_of_mem h]; exact sq_nonneg _
        · rw [Set.indicator_of_notMem h]
  calc ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), g x ^ 2
      = ∫ x, (centeredCube z r hr : Set (SpatialCoordinates d)).indicator (fun x => g x ^ 2) x :=
          (integral_indicator hQmeas).symm
    _ ≤ ∫ x, ∑ p ∈ aux_fcp_centers z N, (aux_fcp_ucube p).indicator (fun x => g x ^ 2) x :=
          integral_mono (hg2.indicator hQmeas) hsumint hpt
    _ = ∑ p ∈ aux_fcp_centers z N, ∫ x, (aux_fcp_ucube p).indicator (fun x => g x ^ 2) x :=
          integral_finset_sum _ hFint
    _ = ∑ p ∈ aux_fcp_centers z N, ∫ x in aux_fcp_ucube p, g x ^ 2 := by
          refine Finset.sum_congr rfl fun p hp => ?_
          exact integral_indicator (centeredCube p 1 one_pos).isOpen.measurableSet

/-- On a unit cube, the mass is bounded by the mean deviation and the mean. -/
theorem aux_fcp_cube_mass_le (p : SpatialCoordinates d) (g : SpatialCoordinates d → ℝ)
    (hg2 : IntegrableOn (fun x => g x ^ 2) (aux_fcp_ucube p)) (hg : IntegrableOn g (aux_fcp_ucube p)) :
    ∫ x in aux_fcp_ucube p, g x ^ 2 ≤ 2 * (∫ x in aux_fcp_ucube p, (g x - aux_fcp_umean g p) ^ 2) + 2 * aux_fcp_umean g p ^ 2 := by
  have hvol : volume.real (aux_fcp_ucube p) = 1 := by
    rw [Measure.real_def, centeredCube_volume p one_pos, one_pow]
    exact ENNReal.toReal_ofReal (by norm_num)
  have hvolne : volume (aux_fcp_ucube p) ≠ ⊤ := by
    rw [centeredCube_volume p one_pos]
    exact ENNReal.ofReal_ne_top
  have hg2' : Integrable (fun x => g x ^ 2) (volume.restrict (aux_fcp_ucube p)) := hg2
  have hg' : Integrable g (volume.restrict (aux_fcp_ucube p)) := hg
  have hc : Integrable (fun _ : SpatialCoordinates d => aux_fcp_umean g p ^ 2) (volume.restrict (aux_fcp_ucube p)) :=
    integrableOn_const hvolne
  have hint2 : Integrable (fun _ : SpatialCoordinates d => 2 * aux_fcp_umean g p ^ 2) (volume.restrict (aux_fcp_ucube p)) :=
    hc.const_mul 2
  have hpoly : Integrable (fun x => g x ^ 2 - (2 * aux_fcp_umean g p) * g x + aux_fcp_umean g p ^ 2)
      (volume.restrict (aux_fcp_ucube p)) :=
    (hg2'.sub (hg'.const_mul (2 * aux_fcp_umean g p))).add hc
  have hm2 : Integrable (fun x => (g x - aux_fcp_umean g p) ^ 2) (volume.restrict (aux_fcp_ucube p)) :=
    hpoly.congr (Filter.Eventually.of_forall (fun x => by ring))
  have hint1 : Integrable (fun x => 2 * (g x - aux_fcp_umean g p) ^ 2) (volume.restrict (aux_fcp_ucube p)) :=
    hm2.const_mul 2
  have hRHS : Integrable (fun x => 2 * (g x - aux_fcp_umean g p) ^ 2 + 2 * aux_fcp_umean g p ^ 2)
      (volume.restrict (aux_fcp_ucube p)) := hint1.add hint2
  have hpt : ∀ x : SpatialCoordinates d, g x ^ 2 ≤ 2 * (g x - aux_fcp_umean g p) ^ 2 + 2 * aux_fcp_umean g p ^ 2 := by
    intro x
    nlinarith [sq_nonneg (g x - 2 * aux_fcp_umean g p)]
  have hInt : ∫ x in aux_fcp_ucube p, (2 * (g x - aux_fcp_umean g p) ^ 2 + 2 * aux_fcp_umean g p ^ 2)
      = 2 * (∫ x in aux_fcp_ucube p, (g x - aux_fcp_umean g p) ^ 2) + 2 * aux_fcp_umean g p ^ 2 := by
    rw [integral_add hint1 hint2, integral_const_mul, setIntegral_const, hvol, one_smul]
  calc ∫ x in aux_fcp_ucube p, g x ^ 2
      ≤ ∫ x in aux_fcp_ucube p, (2 * (g x - aux_fcp_umean g p) ^ 2 + 2 * aux_fcp_umean g p ^ 2) :=
        setIntegral_mono hg2 hRHS hpt
    _ = 2 * (∫ x in aux_fcp_ucube p, (g x - aux_fcp_umean g p) ^ 2) + 2 * aux_fcp_umean g p ^ 2 := hInt

/-- Chain of means along `e_0`: every cube mean is controlled by the local deviations. -/
theorem aux_fcp_chain_mean_bound (hd : 2 ≤ d) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (N : ℕ)
    (hN : r + 1 ≤ N) (g : SpatialCoordinates d → ℝ)
    (hg0 : ∀ x, x ∉ (centeredCube z r hr : Set (SpatialCoordinates d)) → g x = 0)
    (hg2 : Integrable (fun x => g x ^ 2))
    (hgi : Integrable g)
    (B : ℝ) (hA : ∀ p ∈ aux_fcp_centers z N, ∫ x in aux_fcp_ucube p, (g x - aux_fcp_umean g p) ^ 2 ≤ B) :
    ∀ p ∈ aux_fcp_centers z N, aux_fcp_umean g p ^ 2 ≤ 8 * (2 * N + 1) ^ 2 * B := by
  classical
  have i0lt : 0 < d := by omega
  set i0 : Fin d := ⟨0, i0lt⟩ with hi0
  -- membership of lattice centres
  have hmem : ∀ n ∈ aux_fcp_box d N, aux_fcp_center z n ∈ aux_fcp_centers z N := fun n hn => Finset.mem_image.mpr ⟨n, hn, rfl⟩
  have hB0 : 0 ≤ B := by
    obtain ⟨p0, hp0⟩ : (aux_fcp_centers z N).Nonempty := ⟨aux_fcp_center z 0, hmem 0 (by simp [aux_fcp_box, Fintype.mem_piFinset])⟩
    exact (setIntegral_nonneg (centeredCube p0 1 one_pos).isOpen.measurableSet
      (fun x _ => sq_nonneg _)).trans (hA p0 hp0)
  -- one step along e_0
  have hstep : ∀ n ∈ aux_fcp_box d N, n i0 < N →
      |aux_fcp_umean g (aux_fcp_center z n) - aux_fcp_umean g (aux_fcp_center z (n + Pi.single i0 1))| ≤ Real.sqrt (8 * B) := by
    intro n hn hlt
    have hn' : n + Pi.single i0 1 ∈ aux_fcp_box d N := by
      simp only [aux_fcp_box, Fintype.mem_piFinset, Finset.mem_Icc] at hn ⊢
      intro j
      by_cases hj : j = i0
      · subst hj; simp only [Pi.add_apply, Pi.single_eq_same]; constructor <;> linarith [(hn i0).1]
      · simp only [Pi.add_apply, Pi.single_eq_of_ne hj, add_zero]; exact hn j
    have hsq := aux_fcp_mean_step g (aux_fcp_ucube (aux_fcp_center z n)) (aux_fcp_ucube (aux_fcp_center z (n + Pi.single i0 1)))
      (centeredCube _ 1 one_pos).isOpen.measurableSet (centeredCube _ 1 one_pos).isOpen.measurableSet
      (aux_fcp_step_overlap_volume hd z n)
      (by rw [centeredCube_volume]; exact ENNReal.ofReal_lt_top)
      (by rw [centeredCube_volume]; exact ENNReal.ofReal_lt_top)
      hg2.integrableOn hgi.integrableOn _ _ B B (hA _ (hmem n hn)) (hA _ (hmem _ hn'))
    rw [show 4 * (B + B) = 8 * B by ring] at hsq
    exact Real.abs_le_sqrt hsq
  -- induction on the distance to the outer layer
  have hind : ∀ k : ℕ, ∀ n ∈ aux_fcp_box d N, ((N : ℤ) - n i0).toNat = k →
      |aux_fcp_umean g (aux_fcp_center z n)| ≤ k * Real.sqrt (8 * B) := by
    intro k
    induction k with
    | zero =>
      intro n hn hk
      have hle : n i0 ≤ N := by
        simp only [aux_fcp_box, Fintype.mem_piFinset, Finset.mem_Icc] at hn; exact (hn i0).2
      have heq : n i0 = N := by omega
      have hdisj := aux_fcp_outer_disjoint hd z hr N hN n heq
      have h0 : aux_fcp_umean g (aux_fcp_center z n) = 0 := by
        unfold aux_fcp_umean
        apply setIntegral_eq_zero_of_forall_eq_zero
        intro x hx
        exact hg0 x (Set.disjoint_left.mp hdisj hx)
      simp [h0]
    | succ k ih =>
      intro n hn hk
      have hlt : n i0 < N := by omega
      have hn' : n + Pi.single i0 1 ∈ aux_fcp_box d N := by
        simp only [aux_fcp_box, Fintype.mem_piFinset, Finset.mem_Icc] at hn ⊢
        intro j
        by_cases hj : j = i0
        · subst hj; simp only [Pi.add_apply, Pi.single_eq_same]; constructor <;> linarith [(hn i0).1]
        · simp only [Pi.add_apply, Pi.single_eq_of_ne hj, add_zero]; exact hn j
      have hk' : ((N : ℤ) - ((n + Pi.single i0 (1 : ℤ) : Fin d → ℤ) i0)).toNat = k := by
        simp only [Pi.add_apply, Pi.single_eq_same]; omega
      have h1 := hstep n hn hlt
      have h2 := ih _ hn' hk'
      calc |aux_fcp_umean g (aux_fcp_center z n)|
          ≤ |aux_fcp_umean g (aux_fcp_center z n) - aux_fcp_umean g (aux_fcp_center z (n + Pi.single i0 1))| +
            |aux_fcp_umean g (aux_fcp_center z (n + Pi.single i0 1))| := by
              have := abs_sub_abs_le_abs_sub (aux_fcp_umean g (aux_fcp_center z n)) (aux_fcp_umean g (aux_fcp_center z (n + Pi.single i0 1)))
              linarith [abs_nonneg (aux_fcp_umean g (aux_fcp_center z (n + Pi.single i0 1)))]
        _ ≤ Real.sqrt (8 * B) + k * Real.sqrt (8 * B) := add_le_add h1 h2
        _ = ((k + 1 : ℕ) : ℝ) * Real.sqrt (8 * B) := by push_cast; ring
  -- conclude
  intro p hp
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hp
  have hK := hind _ n hn rfl
  have hKle : (((N : ℤ) - n i0).toNat : ℝ) ≤ 2 * N + 1 := by
    have hlo : -(N : ℤ) ≤ n i0 := by
      simp only [aux_fcp_box, Fintype.mem_piFinset, Finset.mem_Icc] at hn; exact (hn i0).1
    have : ((N : ℤ) - n i0).toNat ≤ 2 * N + 1 := by omega
    exact_mod_cast this
  have hs0 : 0 ≤ Real.sqrt (8 * B) := Real.sqrt_nonneg _
  have habs : |aux_fcp_umean g (aux_fcp_center z n)| ≤ (2 * N + 1) * Real.sqrt (8 * B) :=
    hK.trans (mul_le_mul_of_nonneg_right hKle hs0)
  have hsq : aux_fcp_umean g (aux_fcp_center z n) ^ 2 ≤ ((2 * N + 1) * Real.sqrt (8 * B)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  calc aux_fcp_umean g (aux_fcp_center z n) ^ 2 ≤ ((2 * N + 1) * Real.sqrt (8 * B)) ^ 2 := hsq
    _ = 8 * (2 * N + 1) ^ 2 * B := by
        rw [mul_pow, Real.sq_sqrt (by linarith)]; ring

/-- Pointwise near/far bound: near pairs of `Q` are counted by some covering cube; far pairs
(some coordinate gap `≥ 1/4`) have kernel at most `4^{d+2s}`. -/
theorem aux_fcp_gq_pointwise (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (N : ℕ) (hN : r + 1 ≤ N)
    (s : ℝ) (hs0 : 0 < s) (g : SpatialCoordinates d → ℝ)
    (x : SpatialCoordinates d) (hx : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (y : SpatialCoordinates d) :
    aux_fcp_gq s g x y ≤ (∑ p ∈ aux_fcp_centers z N, (aux_fcp_ucube p).indicator (fun x' => (aux_fcp_ucube p).indicator (aux_fcp_gq s g x') y) x) +
      ENNReal.ofReal (4 ^ ((d : ℝ) + 2 * s) * (g x - g y) ^ 2) := by
  by_cases hnear : ∀ j, |x j - y j| < 1 / 4
  · obtain ⟨p, hp, hxp, hyp⟩ := aux_fcp_cover_near z hr N hN x hx y hnear
    have hterm : (aux_fcp_ucube p).indicator (fun x' => (aux_fcp_ucube p).indicator (aux_fcp_gq s g x') y) x = aux_fcp_gq s g x y := by
      rw [Set.indicator_of_mem hxp, Set.indicator_of_mem hyp]
    have hnonneg : ∀ q ∈ aux_fcp_centers z N,
        0 ≤ (aux_fcp_ucube q).indicator (fun x' => (aux_fcp_ucube q).indicator (aux_fcp_gq s g x') y) x :=
      fun q _ => zero_le _
    calc aux_fcp_gq s g x y
        = (aux_fcp_ucube p).indicator (fun x' => (aux_fcp_ucube p).indicator (aux_fcp_gq s g x') y) x := hterm.symm
      _ ≤ ∑ q ∈ aux_fcp_centers z N, (aux_fcp_ucube q).indicator (fun x' => (aux_fcp_ucube q).indicator (aux_fcp_gq s g x') y) x :=
          Finset.single_le_sum hnonneg hp
      _ ≤ _ := le_add_of_nonneg_right (zero_le _)
  · push_neg at hnear
    obtain ⟨j, hj⟩ := hnear
    have hsum_nonneg : 0 ≤ ∑ j : Fin d, (x j - y j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    have hle : (1 / 4 : ℝ) ^ 2 ≤ ∑ j : Fin d, (x j - y j) ^ 2 := by
      calc (1 / 4 : ℝ) ^ 2 ≤ (x j - y j) ^ 2 := by
            rw [sq_le_sq, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
            exact hj
        _ ≤ ∑ i : Fin d, (x i - y i) ^ 2 :=
            Finset.single_le_sum (f := fun i => (x i - y i) ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    have hD0 : 0 ≤ Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := Real.sqrt_nonneg _
    have hsqrt : (1 / 4 : ℝ) ≤ Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
      rw [Real.le_sqrt (by norm_num) hsum_nonneg]
      exact hle
    have hDpos : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) hsqrt
    have hexp : 0 ≤ (d : ℝ) + 2 * s := by positivity
    have hone : (1 : ℝ) ≤ 4 ^ ((d : ℝ) + 2 * s) *
        (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ ((d : ℝ) + 2 * s) := by
      rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hD0]
      calc (1 : ℝ) = 1 ^ ((d : ℝ) + 2 * s) := (Real.one_rpow _).symm
        _ ≤ (4 * Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ ((d : ℝ) + 2 * s) :=
            Real.rpow_le_rpow (by norm_num) (by linarith) hexp
    have hpowpos : 0 < (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ ((d : ℝ) + 2 * s) :=
      Real.rpow_pos_of_pos hDpos _
    have hgq : aux_fcp_gq s g x y ≤ ENNReal.ofReal (4 ^ ((d : ℝ) + 2 * s) * (g x - g y) ^ 2) := by
      unfold aux_fcp_gq
      rw [ENNReal.ofReal_rpow_of_nonneg hD0 hexp, ← ENNReal.ofReal_div_of_pos hpowpos]
      apply ENNReal.ofReal_le_ofReal
      rw [div_le_iff₀ hpowpos]
      calc (g x - g y) ^ 2 = (g x - g y) ^ 2 * 1 := (mul_one _).symm
        _ ≤ (g x - g y) ^ 2 * (4 ^ ((d : ℝ) + 2 * s) *
              (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ ((d : ℝ) + 2 * s)) :=
            mul_le_mul_of_nonneg_left hone (sq_nonneg _)
        _ = 4 ^ ((d : ℝ) + 2 * s) * (g x - g y) ^ 2 *
              (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ ((d : ℝ) + 2 * s) := by ring
    exact hgq.trans (le_add_of_nonneg_left (zero_le _))

/-- The far part integrates to at most `4 |Q| ∫_Q g^2` times the kernel constant. -/
theorem aux_fcp_far_integral (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (s : ℝ)
    (g : SpatialCoordinates d → ℝ)
    (hg2 : IntegrableOn (fun x => g x ^ 2) (centeredCube z r hr)) :
    ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ENNReal.ofReal (4 ^ ((d : ℝ) + 2 * s) * (g x - g y) ^ 2) ≤
      ENNReal.ofReal (4 ^ ((d : ℝ) + 2 * s) * 4 * r ^ d *
        ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), g x ^ 2) := by
  set Q : Set (SpatialCoordinates d) := (centeredCube z r hr : Set (SpatialCoordinates d)) with hQ
  set C : ℝ := 4 ^ ((d : ℝ) + 2 * s) with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have hvt : volume Q ≠ ⊤ := by rw [hQ, centeredCube_volume z hr]; exact ENNReal.ofReal_ne_top
  set I : ℝ := ∫ x in Q, g x ^ 2 with hI
  have hIval : 0 ≤ I := by rw [hI]; exact integral_nonneg (fun x => sq_nonneg (g x))
  have hB : ∫⁻ y in Q, ENNReal.ofReal (2 * C * (g y) ^ 2) = ENNReal.ofReal (2 * C * I) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hg2.const_mul (2 * C))
          (Filter.Eventually.of_forall (fun y => by positivity)), integral_const_mul, ← hI]
  have hpt : ∀ x, ∫⁻ y in Q, ENNReal.ofReal (C * (g x - g y) ^ 2) ≤
      ENNReal.ofReal (2 * C * (g x) ^ 2) * volume Q + ENNReal.ofReal (2 * C * I) := by
    intro x
    have hle : ∀ y : SpatialCoordinates d,
        ENNReal.ofReal (C * (g x - g y) ^ 2) ≤
          ENNReal.ofReal (2 * C * (g x) ^ 2) + ENNReal.ofReal (2 * C * (g y) ^ 2) := by
      intro y
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      calc C * (g x - g y) ^ 2 ≤ C * (2 * (g x) ^ 2 + 2 * (g y) ^ 2) :=
            mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (g x + g y)]) hC0
        _ = 2 * C * (g x) ^ 2 + 2 * C * (g y) ^ 2 := by ring
    calc ∫⁻ y in Q, ENNReal.ofReal (C * (g x - g y) ^ 2)
        ≤ ∫⁻ y in Q, (ENNReal.ofReal (2 * C * (g x) ^ 2) + ENNReal.ofReal (2 * C * (g y) ^ 2)) :=
          lintegral_mono hle
      _ = ENNReal.ofReal (2 * C * (g x) ^ 2) * volume Q + ENNReal.ofReal (2 * C * I) := by
          rw [lintegral_add_left (f := fun _ : SpatialCoordinates d => ENNReal.ofReal (2 * C * (g x) ^ 2))
                measurable_const]
          rw [lintegral_const, Measure.restrict_apply_univ, hB]
  calc ∫⁻ x in Q, ∫⁻ y in Q, ENNReal.ofReal (C * (g x - g y) ^ 2)
      ≤ ∫⁻ x in Q, (ENNReal.ofReal (2 * C * (g x) ^ 2) * volume Q + ENNReal.ofReal (2 * C * I)) :=
        lintegral_mono hpt
    _ = (∫⁻ x in Q, ENNReal.ofReal (2 * C * (g x) ^ 2) * volume Q) + ∫⁻ x in Q, ENNReal.ofReal (2 * C * I) := by
        rw [lintegral_add_right (f := fun x => ENNReal.ofReal (2 * C * (g x) ^ 2) * volume Q) measurable_const]
    _ = ENNReal.ofReal (2 * C * I) * volume Q + ENNReal.ofReal (2 * C * I) * volume Q := by
        rw [lintegral_mul_const' (volume Q) (fun x => ENNReal.ofReal (2 * C * (g x) ^ 2)) hvt, hB,
            lintegral_const, Measure.restrict_apply_univ]
    _ = ENNReal.ofReal (C * 4 * r ^ d * I) := by
        rw [hQ, centeredCube_volume z hr]
        have ha : (0 : ℝ) ≤ 2 * C * I := by positivity
        have hv : (0 : ℝ) ≤ r ^ d := pow_nonneg hr.le d
        rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_add (mul_nonneg ha hv) (mul_nonneg ha hv)]
        congr 1
        ring

/-- The near part: restricting to the covering cubes. -/
theorem aux_fcp_near_integral (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (N : ℕ) (s : ℝ)
    (g : SpatialCoordinates d → ℝ) (hgm : Measurable g) :
    ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
          (∑ p ∈ aux_fcp_centers z N, (aux_fcp_ucube p).indicator (fun x' => (aux_fcp_ucube p).indicator (aux_fcp_gq s g x') y) x) ≤
      ∑ p ∈ aux_fcp_centers z N, ∫⁻ x in aux_fcp_ucube p, ∫⁻ y in aux_fcp_ucube p, aux_fcp_gq s g x y := by
  set Q : Set (SpatialCoordinates d) := (centeredCube z r hr : Set (SpatialCoordinates d)) with hQ
  have hgq : Measurable (Function.uncurry (aux_fcp_gq s g)) := by
    unfold aux_fcp_gq Function.uncurry; fun_prop
  have hF : ∀ p, Measurable (Function.uncurry fun x y =>
      (aux_fcp_ucube p).indicator (fun x' => (aux_fcp_ucube p).indicator (aux_fcp_gq s g x') y) x) := by
    intro p
    have hU : MeasurableSet (aux_fcp_ucube p) := (centeredCube p 1 one_pos).isOpen.measurableSet
    have : (Function.uncurry fun x y =>
        (aux_fcp_ucube p).indicator (fun x' => (aux_fcp_ucube p).indicator (aux_fcp_gq s g x') y) x) =
        (aux_fcp_ucube p ×ˢ aux_fcp_ucube p).indicator (Function.uncurry (aux_fcp_gq s g)) := by
      funext q
      obtain ⟨x, y⟩ := q
      by_cases hx : x ∈ aux_fcp_ucube p <;> by_cases hy : y ∈ aux_fcp_ucube p <;>
        simp [Function.uncurry, Set.indicator, hx, hy, Set.mem_prod]
    rw [this]
    exact hgq.indicator (hU.prod hU)
  calc ∫⁻ x in Q, ∫⁻ y in Q, (∑ p ∈ aux_fcp_centers z N,
          (aux_fcp_ucube p).indicator (fun x' => (aux_fcp_ucube p).indicator (aux_fcp_gq s g x') y) x)
      = ∫⁻ x in Q, ∑ p ∈ aux_fcp_centers z N, ∫⁻ y in Q,
          (aux_fcp_ucube p).indicator (fun x' => (aux_fcp_ucube p).indicator (aux_fcp_gq s g x') y) x := by
        refine lintegral_congr fun x => ?_
        exact lintegral_finset_sum _ fun p _ => (hF p).of_uncurry_left
    _ = ∑ p ∈ aux_fcp_centers z N, ∫⁻ x in Q, ∫⁻ y in Q,
          (aux_fcp_ucube p).indicator (fun x' => (aux_fcp_ucube p).indicator (aux_fcp_gq s g x') y) x :=
        lintegral_finset_sum _ fun p _ => (hF p).lintegral_prod_right
    _ ≤ ∑ p ∈ aux_fcp_centers z N, ∫⁻ x in aux_fcp_ucube p, ∫⁻ y in aux_fcp_ucube p, aux_fcp_gq s g x y := by
        refine Finset.sum_le_sum fun p _ => ?_
        have hU : MeasurableSet (aux_fcp_ucube p) := (centeredCube p 1 one_pos).isOpen.measurableSet
        calc ∫⁻ x in Q, ∫⁻ y in Q,
              (aux_fcp_ucube p).indicator (fun x' => (aux_fcp_ucube p).indicator (aux_fcp_gq s g x') y) x
            = ∫⁻ x in Q, (aux_fcp_ucube p).indicator (fun x' => ∫⁻ y in Q, (aux_fcp_ucube p).indicator (aux_fcp_gq s g x') y) x := by
              refine lintegral_congr fun x => ?_
              by_cases hx : x ∈ aux_fcp_ucube p <;> simp [Set.indicator, hx]
          _ = ∫⁻ x in Q ∩ aux_fcp_ucube p, ∫⁻ y in Q, (aux_fcp_ucube p).indicator (aux_fcp_gq s g x) y := by
              rw [lintegral_indicator hU, Measure.restrict_restrict hU, Set.inter_comm]
          _ = ∫⁻ x in Q ∩ aux_fcp_ucube p, ∫⁻ y in Q ∩ aux_fcp_ucube p, aux_fcp_gq s g x y := by
              refine lintegral_congr fun x => ?_
              rw [lintegral_indicator hU, Measure.restrict_restrict hU, Set.inter_comm]
          _ ≤ ∫⁻ x in aux_fcp_ucube p, ∫⁻ y in aux_fcp_ucube p, aux_fcp_gq s g x y := by
              refine (lintegral_mono_set Set.inter_subset_right).trans ?_
              exact lintegral_mono fun x => lintegral_mono_set Set.inter_subset_right

/-! ### Main estimates for the zero extension `g` -/

/-- The L2 bound from the local mean-deviation bounds, by chaining means along `e_0`. -/
theorem aux_fcp_l2_bound (hd : 2 ≤ d) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (N : ℕ)
    (hN : r + 1 ≤ N) (g : SpatialCoordinates d → ℝ)
    (hg0 : ∀ x, x ∉ (centeredCube z r hr : Set (SpatialCoordinates d)) → g x = 0)
    (hg2 : Integrable (fun x => g x ^ 2))
    (hgi : Integrable g)
    (B : ℝ) (hA : ∀ p ∈ aux_fcp_centers z N, ∫ x in aux_fcp_ucube p, (g x - aux_fcp_umean g p) ^ 2 ≤ B) :
    ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), g x ^ 2 ≤
      ((aux_fcp_centers z N).card : ℝ) * (2 + 16 * (2 * N + 1) ^ 2) * B := by
  have hmean := aux_fcp_chain_mean_bound hd z hr N hN g hg0 hg2 hgi B hA
  calc ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), g x ^ 2
      ≤ ∑ p ∈ aux_fcp_centers z N, ∫ x in aux_fcp_ucube p, g x ^ 2 := aux_fcp_l2_le_sum_cubes z hr N hN g hg2
    _ ≤ ∑ _p ∈ aux_fcp_centers z N, (2 * B + 2 * (8 * (2 * N + 1) ^ 2 * B)) := by
        apply Finset.sum_le_sum
        intro p hp
        calc ∫ x in aux_fcp_ucube p, g x ^ 2
            ≤ 2 * (∫ x in aux_fcp_ucube p, (g x - aux_fcp_umean g p) ^ 2) + 2 * aux_fcp_umean g p ^ 2 :=
              aux_fcp_cube_mass_le p g hg2.integrableOn hgi.integrableOn
          _ ≤ 2 * B + 2 * (8 * (2 * N + 1) ^ 2 * B) :=
              add_le_add (mul_le_mul_of_nonneg_left (hA p hp) (by norm_num : (0:ℝ) ≤ 2))
                (mul_le_mul_of_nonneg_left (hmean p hp) (by norm_num : (0:ℝ) ≤ 2))
    _ = ((aux_fcp_centers z N).card : ℝ) * (2 + 16 * (2 * N + 1) ^ 2) * B := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- Near/far splitting of the Gagliardo double integral on `Q`. -/
theorem aux_fcp_near_far (hd : 2 ≤ d) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (N : ℕ)
    (hN : r + 1 ≤ N) (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (g : SpatialCoordinates d → ℝ)
    (hg2 : IntegrableOn (fun x => g x ^ 2) (centeredCube z r hr)) (hgm : Measurable g) :
    ENNReal.ofReal s * ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)), aux_fcp_gq s g x y ≤
      (∑ p ∈ aux_fcp_centers z N, ENNReal.ofReal s * ∫⁻ x in aux_fcp_ucube p, ∫⁻ y in aux_fcp_ucube p, aux_fcp_gq s g x y) +
      ENNReal.ofReal (s * 4 ^ ((d : ℝ) + 2 * s) * 4 * r ^ d *
        ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), g x ^ 2) := by
  set Q : Set (SpatialCoordinates d) := (centeredCube z r hr : Set (SpatialCoordinates d)) with hQ
  have hfarm : ∀ x, Measurable fun y => ENNReal.ofReal (4 ^ ((d : ℝ) + 2 * s) * (g x - g y) ^ 2) := by
    intro x; fun_prop
  have hstep : ∫⁻ x in Q, ∫⁻ y in Q, aux_fcp_gq s g x y ≤
      (∫⁻ x in Q, ∫⁻ y in Q, (∑ p ∈ aux_fcp_centers z N,
          (aux_fcp_ucube p).indicator (fun x' => (aux_fcp_ucube p).indicator (aux_fcp_gq s g x') y) x)) +
      ∫⁻ x in Q, ∫⁻ y in Q, ENNReal.ofReal (4 ^ ((d : ℝ) + 2 * s) * (g x - g y) ^ 2) := by
    calc ∫⁻ x in Q, ∫⁻ y in Q, aux_fcp_gq s g x y
        ≤ ∫⁻ x in Q, ((∫⁻ y in Q, (∑ p ∈ aux_fcp_centers z N,
            (aux_fcp_ucube p).indicator (fun x' => (aux_fcp_ucube p).indicator (aux_fcp_gq s g x') y) x)) +
            ∫⁻ y in Q, ENNReal.ofReal (4 ^ ((d : ℝ) + 2 * s) * (g x - g y) ^ 2)) := by
          refine setLIntegral_mono' (centeredCube z r hr).isOpen.measurableSet fun x hx => ?_
          rw [← lintegral_add_right _ (hfarm x)]
          exact lintegral_mono fun y => aux_fcp_gq_pointwise z hr N hN s hs0 g x hx y
      _ = _ := by
          have hFm : Measurable fun x => ∫⁻ y in Q,
              ENNReal.ofReal (4 ^ ((d : ℝ) + 2 * s) * (g x - g y) ^ 2) := by
            have hu : Measurable (Function.uncurry fun x y : SpatialCoordinates d =>
                ENNReal.ofReal (4 ^ ((d : ℝ) + 2 * s) * (g x - g y) ^ 2)) := by
              unfold Function.uncurry; fun_prop
            exact hu.lintegral_prod_right
          exact lintegral_add_right _ hFm
  have hnear := aux_fcp_near_integral z hr N s g hgm
  have hfar := aux_fcp_far_integral z hr s g hg2
  calc ENNReal.ofReal s * ∫⁻ x in Q, ∫⁻ y in Q, aux_fcp_gq s g x y
      ≤ ENNReal.ofReal s * ((∑ p ∈ aux_fcp_centers z N, ∫⁻ x in aux_fcp_ucube p, ∫⁻ y in aux_fcp_ucube p, aux_fcp_gq s g x y) +
          ENNReal.ofReal (4 ^ ((d : ℝ) + 2 * s) * 4 * r ^ d * ∫ x in Q, g x ^ 2)) := by
        gcongr
        exact hstep.trans (add_le_add hnear hfar)
    _ = (∑ p ∈ aux_fcp_centers z N, ENNReal.ofReal s * ∫⁻ x in aux_fcp_ucube p, ∫⁻ y in aux_fcp_ucube p, aux_fcp_gq s g x y) +
          ENNReal.ofReal (s * 4 ^ ((d : ℝ) + 2 * s) * 4 * r ^ d * ∫ x in Q, g x ^ 2) := by
        rw [mul_add, Finset.mul_sum, ← ENNReal.ofReal_mul hs0.le]
        congr 2
        ring

/-! ### Conversions between the Lean carriers and the function `g` -/

/-- The squared L2 norm on `Q` as an integral of an a.e.-equal representative. -/
theorem aux_fcp_norm_sq_eq (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (f : DomainL2 (centeredCube z r hr)) (g : SpatialCoordinates d → ℝ)
    (hfg : (f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] g) :
    ‖f‖ ^ 2 = ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), g x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq f, L2.inner_def]
  refine integral_congr_ae (hfg.mono fun x hx => ?_)
  simp only [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- The volume-normalized seminorm, squared and multiplied by the volume, is the (toReal of the)
Gagliardo double integral of any a.e.-equal representative. -/
theorem aux_fcp_seminorm_sq_eq (hd : 2 ≤ d) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (s : Set.Ioo (0 : ℝ) 1) (f : DomainL2 (centeredCube z r hr)) (g : SpatialCoordinates d → ℝ)
    (hfg : (f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] g) :
    volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
        (cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => f)).toReal ^ 2 =
      (ENNReal.ofReal (s : ℝ) * ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)), aux_fcp_gq (s : ℝ) g x y).toReal := by
  simp only [cubeFractionalL2Seminorm, Fin.sum_univ_one]
  set Q : Set (SpatialCoordinates d) := (centeredCube z r hr : Set (SpatialCoordinates d)) with hQ
  set J : ℝ≥0∞ := ∫⁻ x in Q, ∫⁻ y in Q, aux_fcp_gq (s : ℝ) g x y with hJ
  have hfgQ : (f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict Q] g := hfg
  have hJeq : (∫⁻ x in Q, ∫⁻ y in Q,
        ENNReal.ofReal ((f x - f y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^ ((d : ℝ) + 2 * (s : ℝ)))
      = J := by
    rw [hJ]
    simp only [aux_fcp_gq]
    apply lintegral_congr_ae
    filter_upwards [hfgQ] with x hx
    rw [hx]
    apply lintegral_congr_ae
    filter_upwards [hfgQ] with y hy
    rw [hy]
  rw [hJeq]
  have hpow : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)).toReal ^ 2 = x.toReal := by
    intro x
    have h2 : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
      have h : (1 / 2 : ℝ) = ((2 : ℕ) : ℝ)⁻¹ := by norm_num
      rw [h]
      exact ENNReal.rpow_inv_natCast_pow (n := 2) (by norm_num) x
    calc (x ^ (1 / 2 : ℝ)).toReal ^ 2 = ((x ^ (1 / 2 : ℝ)) ^ 2).toReal := by rw [ENNReal.toReal_pow]
      _ = x.toReal := by rw [h2]
  rw [hpow]
  have hVol : volume Q = ENNReal.ofReal (r ^ d) := by rw [hQ]; exact centeredCube_volume z hr
  have hVolreal : (volume Q).toReal = r ^ d := by
    rw [hVol, ENNReal.toReal_ofReal (pow_nonneg hr.le d)]
  have hrd : (r : ℝ) ^ d ≠ 0 := (pow_pos hr d).ne'
  have hs0 : 0 ≤ (s : ℝ) := s.2.1.le
  have hreal : volume.real Q = (volume Q).toReal := by simp only [Measure.real]
  rw [hreal, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofReal hs0, hVolreal,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hs0]
  field_simp

/-! ### The per-cube facts (Sobolev glue) -/

/-- Restricting the zero extension (to the whole space) to a unit cube gives the indicator
representative a.e. on that cube. -/
theorem aux_fcp_restrictZeroExt_coeFn (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (p : SpatialCoordinates d)
    (f : DomainL2 (centeredCube z r hr)) :
    (domainLpRestrict (le_top : centeredCube p 1 one_pos ≤ ⊤)
        (zeroExtensionLp (le_top : centeredCube z r hr ≤ ⊤) f) : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (aux_fcp_ucube p)] (centeredCube z r hr : Set (SpatialCoordinates d)).indicator f := by
  have h1 := domainLpRestrict_coeFn (le_top : centeredCube p 1 one_pos ≤ ⊤)
    (zeroExtensionLp (le_top : centeredCube z r hr ≤ ⊤) f)
  have h2 := zeroExtensionLp_coeFn (le_top : centeredCube z r hr ≤ ⊤) f
  exact h1.trans (ae_restrict_of_ae_restrict_of_subset (Set.subset_univ _) h2)

/-- Energy comparison: the energy on a unit cube of the zero extension of `v` is at most the
energy of `v` on `Q`, when both coefficients agree a.e. with the same positive `c`. -/
theorem aux_fcp_energy_restrict_le (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (p : SpatialCoordinates d)
    (c : SpatialCoordinates d → ℝ) (hcpos : ∀ x, 0 < c x)
    (aQ : PositiveCoefficient (centeredCube z r hr))
    (haQ : (aQ.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] c)
    (ap : PositiveCoefficient (centeredCube p 1 one_pos))
    (hap : (ap.val : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (aux_fcp_ucube p)] c)
    (v : SobolevData (centeredCube z r hr)) :
    sobolevCoefficientForm ap
        (sobolevDataRestrict (le_top : centeredCube p 1 one_pos ≤ ⊤)
          (zeroExtensionSobolevData (le_top : centeredCube z r hr ≤ ⊤) v))
        (sobolevDataRestrict (le_top : centeredCube p 1 one_pos ≤ ⊤)
          (zeroExtensionSobolevData (le_top : centeredCube z r hr ≤ ⊤) v)) ≤
      sobolevCoefficientForm aQ v v := by
  rw [sobolevCoefficientForm_apply, sobolevCoefficientForm_apply]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [sobolevDataRestrict, zeroExtensionSobolevData]
  set Q : Set (SpatialCoordinates d) := (centeredCube z r hr : Set (SpatialCoordinates d)) with hQdef
  set U : Set (SpatialCoordinates d) := (aux_fcp_ucube p : Set (SpatialCoordinates d)) with hUdef
  set gr : SpatialCoordinates d → ℝ := (domainLpRestrict (le_top : centeredCube p 1 one_pos ≤ ⊤)
      (zeroExtensionLp (le_top : centeredCube z r hr ≤ ⊤) (v.2 i)) : SpatialCoordinates d → ℝ) with hgrdef
  set g : SpatialCoordinates d → ℝ := Q.indicator (v.2 i : SpatialCoordinates d → ℝ) with hgdef
  have hQmeas : MeasurableSet Q := (centeredCube z r hr).isOpen.measurableSet
  have hgr : gr =ᵐ[volume.restrict U] g := by
    simpa [hgrdef, hgdef, hUdef] using aux_fcp_restrictZeroExt_coeFn z hr p (v.2 i)
  have hcv : Integrable (fun x => aQ.val x * (v.2 i x * v.2 i x)) (volume.restrict Q) := by
    have h := integrable_weighted_inner (E := ℝ) aQ.val (v.2 i) (v.2 i)
    refine h.congr ?_
    filter_upwards with x
    simp only [RCLike.inner_apply, conj_trivial]
  have hc_int : IntegrableOn (fun x => c x * (v.2 i x * v.2 i x)) Q := by
    refine hcv.congr ?_
    filter_upwards [haQ] with x hx
    rw [hx]
  have hpoint : ∀ x, c x * (Q.indicator (fun x' => v.2 i x' * v.2 i x') x)
      = Q.indicator (fun x' => c x' * (v.2 i x' * v.2 i x')) x := by
    intro x
    by_cases hx : x ∈ Q
    · simp only [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx, mul_zero]
  calc ∫ x in U, ap.val x * (gr x * gr x)
      = ∫ x in U, c x * (g x * g x) := by
        apply integral_congr_ae
        filter_upwards [hap, hgr] with x h1 h2
        rw [h1, h2]
    _ = ∫ x in U, c x * (Q.indicator (fun x' => v.2 i x' * v.2 i x') x) := by
        apply integral_congr_ae
        filter_upwards with x
        by_cases hx : x ∈ Q
        · simp only [hgdef, Set.indicator_of_mem hx]
        · simp only [hgdef, Set.indicator_of_notMem hx, mul_zero]
    _ = ∫ x in U, Q.indicator (fun x' => c x' * (v.2 i x' * v.2 i x')) x := by
        apply integral_congr_ae; filter_upwards with x; exact hpoint x
    _ = ∫ x in U ∩ Q, c x * (v.2 i x * v.2 i x) := setIntegral_indicator hQmeas
    _ ≤ ∫ x in Q, c x * (v.2 i x * v.2 i x) :=
        setIntegral_mono_set hc_int
          (ae_of_all _ (fun x => mul_nonneg (hcpos x).le (mul_self_nonneg _)))
          (ae_of_all _ (fun x hx => hx.2))
    _ = ∫ x in Q, aQ.val x * (v.2 i x * v.2 i x) := by
        apply integral_congr_ae
        filter_upwards [haQ] with x hx
        rw [hx]

/-- On a unit cube the inhomogeneous norm is the squared seminorm plus the squared L2 norm. -/
theorem aux_fcp_sqNorm_eq (hd : 2 ≤ d) (p : SpatialCoordinates d) (s : Set.Ioo (0 : ℝ) 1)
    (f : DomainL2 (centeredCube p 1 one_pos)) :
    cubeFractionalSqNorm hd p 1 one_pos s f =
      (cubeFractionalL2Seminorm hd p 1 one_pos s (fun _ : Fin 1 => f)).toReal ^ 2 + ‖f‖ ^ 2 := by
  unfold cubeFractionalSqNorm cubeFractionalVecSqNorm cubeFractionalVecSeminormSq
  rw [Fin.sum_univ_one]
  have hvol : volume.real (centeredCube p 1 one_pos : Set (SpatialCoordinates d)) = 1 := by
    rw [measureReal_def, centeredCube_volume]; simp
  rw [hvol, div_one]

/-- A finite seminorm on a unit cube means a finite Gagliardo double integral of any a.e.
representative. -/
theorem aux_fcp_semi_lt_top_imp (hd : 2 ≤ d) (p : SpatialCoordinates d) (s : Set.Ioo (0 : ℝ) 1)
    (f : DomainL2 (centeredCube p 1 one_pos)) (g : SpatialCoordinates d → ℝ)
    (hfg : (f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (aux_fcp_ucube p)] g)
    (hfin : cubeFractionalL2Seminorm hd p 1 one_pos s (fun _ : Fin 1 => f) < ⊤) :
    ENNReal.ofReal (s : ℝ) * ∫⁻ x in aux_fcp_ucube p, ∫⁻ y in aux_fcp_ucube p, aux_fcp_gq (s : ℝ) g x y < ⊤ := by
  classical
  have hvol : volume (aux_fcp_ucube p : Set (SpatialCoordinates d)) = 1 := by
    rw [centeredCube_volume, one_pow, ENNReal.ofReal_one]
  unfold cubeFractionalL2Seminorm at hfin
  rw [hvol, div_one] at hfin
  set J : ℝ≥0∞ := ∫⁻ x in aux_fcp_ucube p, ∫⁻ y in aux_fcp_ucube p,
      ENNReal.ofReal (∑ i : Fin 1, ((fun _ : Fin 1 => f) i x - (fun _ : Fin 1 => f) i y) ^ 2) /
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^ ((d : ℝ) + 2 * (s : ℝ)) with hJ
  have hprod : ENNReal.ofReal (s : ℝ) * J < ⊤ := by
    by_contra h
    have heq : ENNReal.ofReal (s : ℝ) * J = ⊤ := top_unique (le_of_not_gt h)
    exact (ne_of_lt hfin) (by rw [heq, ENNReal.top_rpow_of_pos (by norm_num)])
  have hIeq : J = ∫⁻ x in aux_fcp_ucube p, ∫⁻ y in aux_fcp_ucube p, aux_fcp_gq (s : ℝ) g x y := by
    rw [hJ]
    apply lintegral_congr_ae
    filter_upwards [hfg] with x hx
    apply lintegral_congr_ae
    filter_upwards [hfg] with y hy
    simp only [aux_fcp_gq, Fin.sum_univ_one]
    rw [hx, hy]
  rw [hIeq] at hprod
  exact hprod

/-- The unit cube has volume one. -/
theorem aux_fcp_ucube_volume_real (p : SpatialCoordinates d) : volume.real (aux_fcp_ucube p) = 1 := by
  rw [measureReal_def, centeredCube_volume]; simp

/-- Shifting by a constant does not change the Gagliardo integrand. -/
theorem aux_fcp_gq_sub_const (s : ℝ) (g : SpatialCoordinates d → ℝ) (m : ℝ) :
    aux_fcp_gq s (fun x => g x - m) = aux_fcp_gq s g := by
  funext x y; simp only [aux_fcp_gq]; congr 2; ring

/-- Per unit cube: (A) mean deviation and (B) local Gagliardo integral, both `≤ K E(v)`. -/
theorem aux_fcp_cube_facts (hd : 2 ≤ d) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (N : ℕ)
    (c : SpatialCoordinates d → ℝ) (hcpos : ∀ x, 0 < c x)
    (aQ : PositiveCoefficient (centeredCube z r hr))
    (haQ : (aQ.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] c)
    (a : (i : aux_fcp_centers z N) → PositiveCoefficient (centeredCube i.val 1 one_pos))
    (ha : ∀ i : aux_fcp_centers z N, ((a i).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube i.val 1 one_pos : Set (SpatialCoordinates d))] c)
    (K : ℝ) (hK : 0 ≤ K)
    (hloc : ∀ (i : aux_fcp_centers z N) (w : meanZeroSobolevGraph (centeredCube i.val 1 one_pos)),
      cubeFractionalSqNorm hd i.val 1 one_pos threeQuarterOrder w.val.1 ≤
        K * sobolevCoefficientForm (a i) w.val w.val)
    (v : killedSobolevGraph (centeredCube z r hr)) (g : SpatialCoordinates d → ℝ)
    (hg : g = (centeredCube z r hr : Set (SpatialCoordinates d)).indicator (v.val.1 : SpatialCoordinates d → ℝ))
    (p : SpatialCoordinates d) (hp : p ∈ aux_fcp_centers z N) :
    (∫ x in aux_fcp_ucube p, (g x - aux_fcp_umean g p) ^ 2 ≤ K * sobolevCoefficientForm aQ v.val v.val) ∧
    (ENNReal.ofReal (3 / 4) * ∫⁻ x in aux_fcp_ucube p, ∫⁻ y in aux_fcp_ucube p, aux_fcp_gq (3 / 4) g x y ≤
        ENNReal.ofReal (K * sobolevCoefficientForm aQ v.val v.val)) := by
  have hve := lane2_zeroExtensionSobolevData_mem_weak_of_killed
    (le_top : centeredCube z r hr ≤ ⊤) v.property
  have hvol : volume.real (aux_fcp_ucube p) = 1 := aux_fcp_ucube_volume_real p
  obtain ⟨w, hw1, hwgrad⟩ := exists_meanZero_restrict_of_weakSobolevGraph
    (le_top : centeredCube p 1 one_pos ≤ ⊤) (centeredCube_isBounded p one_pos)
    (by rw [hvol]; norm_num) _ hve
  have hl := hloc ⟨p, hp⟩ w
  -- energy comparison
  have hE : sobolevCoefficientForm (a ⟨p, hp⟩) w.val w.val ≤ sobolevCoefficientForm aQ v.val v.val := by
    have heq : sobolevCoefficientForm (a ⟨p, hp⟩) w.val w.val =
        sobolevCoefficientForm (a ⟨p, hp⟩)
          (sobolevDataRestrict (le_top : centeredCube p 1 one_pos ≤ ⊤)
            (zeroExtensionSobolevData (le_top : centeredCube z r hr ≤ ⊤) v.val))
          (sobolevDataRestrict (le_top : centeredCube p 1 one_pos ≤ ⊤)
            (zeroExtensionSobolevData (le_top : centeredCube z r hr ≤ ⊤) v.val)) := by
      simp only [sobolevCoefficientForm, ContinuousLinearMap.bilinearComp_apply, hwgrad]
    rw [heq]
    exact aux_fcp_energy_restrict_le z hr p c hcpos aQ haQ (a ⟨p, hp⟩) (ha ⟨p, hp⟩) v.val
  -- the representative of w
  have hvr := aux_fcp_restrictZeroExt_coeFn z hr p v.val.1
  rw [← hg] at hvr
  have hint : (∫ y in aux_fcp_ucube p, (sobolevDataRestrict (le_top : centeredCube p 1 one_pos ≤ ⊤)
      (zeroExtensionSobolevData (le_top : centeredCube z r hr ≤ ⊤) v.val)).1 y) = aux_fcp_umean g p :=
    integral_congr_ae hvr
  have hw' : ((w : SobolevData (centeredCube p 1 one_pos)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (aux_fcp_ucube p)] fun x => g x - aux_fcp_umean g p := by
    filter_upwards [hw1, hvr] with x h1 h2
    rw [h1]
    change (sobolevDataRestrict (le_top : centeredCube p 1 one_pos ≤ ⊤)
        (zeroExtensionSobolevData (le_top : centeredCube z r hr ≤ ⊤) v.val)).1 x - _ = _
    rw [hvol, hint, inv_one, one_mul]
    exact congrArg (· - aux_fcp_umean g p) h2
  have hsq := aux_fcp_sqNorm_eq hd p threeQuarterOrder w.val.1
  have hEw : 0 ≤ sobolevCoefficientForm (a ⟨p, hp⟩) w.val w.val := sobolevCoefficientForm_nonneg _ _
  have hKE : K * sobolevCoefficientForm (a ⟨p, hp⟩) w.val w.val ≤
      K * sobolevCoefficientForm aQ v.val v.val := mul_le_mul_of_nonneg_left hE hK
  constructor
  · -- (A): ∫ (g - m)^2 = ‖w‖^2 ≤ ‖w‖^2 + seminorm^2 = sqNorm ≤ K E(w) ≤ K E(v)
    rw [← aux_fcp_norm_sq_eq p one_pos w.val.1 _ hw']
    have : (0 : ℝ) ≤ (cubeFractionalL2Seminorm hd p 1 one_pos threeQuarterOrder
        (fun _ : Fin 1 => w.val.1)).toReal ^ 2 := sq_nonneg _
    linarith
  · -- (B): the local Gagliardo integral, finite by `inputs_classical_e4_h1_finite`
    have hwweak : w.val ∈ weakSobolevGraph (centeredCube p 1 one_pos) :=
      ((mem_meanZeroSobolevGraph_iff _).mp w.property).1
    have hfin := inputs_classical_e4_h1_finite d hd threeQuarterOrder p 1 one_pos ⟨w.val, hwweak⟩
    have hlt := aux_fcp_semi_lt_top_imp hd p threeQuarterOrder w.val.1 _ hw' hfin
    have heq := aux_fcp_seminorm_sq_eq hd p one_pos threeQuarterOrder w.val.1 _ hw'
    rw [hvol, one_mul, aux_fcp_gq_sub_const] at heq
    rw [aux_fcp_gq_sub_const] at hlt
    have hsq3 : ((threeQuarterOrder : Set.Ioo (0 : ℝ) 1) : ℝ) = 3 / 4 := rfl
    rw [hsq3] at heq hlt
    rw [ENNReal.le_ofReal_iff_toReal_le hlt.ne (mul_nonneg hK (sobolevCoefficientForm_nonneg aQ v.val)), ← heq]
    have : 0 ≤ ‖w.val.1‖ ^ 2 := sq_nonneg _
    linarith

/-- For the zero extension `g` of a killed `v`: on every unit cube of the cover, (A) the mean
deviation and (B) the local Gagliardo integral are bounded by `K E(v)`. -/
theorem aux_fcp_local_facts (hd : 2 ≤ d) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (N : ℕ)
    (hN : r + 1 ≤ N) (c : SpatialCoordinates d → ℝ) (hcpos : ∀ x, 0 < c x)
    (aQ : PositiveCoefficient (centeredCube z r hr))
    (haQ : (aQ.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] c)
    (a : (i : aux_fcp_centers z N) → PositiveCoefficient (centeredCube i.val 1 one_pos))
    (ha : ∀ i : aux_fcp_centers z N, ((a i).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube i.val 1 one_pos : Set (SpatialCoordinates d))] c)
    (K : ℝ) (hK : 0 ≤ K)
    (hloc : ∀ (i : aux_fcp_centers z N) (w : meanZeroSobolevGraph (centeredCube i.val 1 one_pos)),
      cubeFractionalSqNorm hd i.val 1 one_pos threeQuarterOrder w.val.1 ≤
        K * sobolevCoefficientForm (a i) w.val w.val)
    (v : killedSobolevGraph (centeredCube z r hr)) :
    (∀ p ∈ aux_fcp_centers z N, ∫ x in aux_fcp_ucube p,
        ((centeredCube z r hr : Set (SpatialCoordinates d)).indicator (v.val.1 : SpatialCoordinates d → ℝ) x -
          aux_fcp_umean ((centeredCube z r hr : Set (SpatialCoordinates d)).indicator (v.val.1 : SpatialCoordinates d → ℝ)) p) ^ 2 ≤
        K * sobolevCoefficientForm aQ v.val v.val) ∧
    (∀ p ∈ aux_fcp_centers z N, ENNReal.ofReal (3 / 4) * ∫⁻ x in aux_fcp_ucube p, ∫⁻ y in aux_fcp_ucube p,
        aux_fcp_gq (3 / 4) ((centeredCube z r hr : Set (SpatialCoordinates d)).indicator (v.val.1 : SpatialCoordinates d → ℝ)) x y ≤
        ENNReal.ofReal (K * sobolevCoefficientForm aQ v.val v.val)) :=
  ⟨fun p hp => (aux_fcp_cube_facts hd z hr N c hcpos aQ haQ a ha K hK hloc v _ rfl p hp).1,
   fun p hp => (aux_fcp_cube_facts hd z hr N c hcpos aQ haQ a ha K hK hloc v _ rfl p hp).2⟩

/-- Measurability of the zero extension. -/
theorem aux_fcp_zeroExt_measurable (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (f : DomainL2 (centeredCube z r hr)) :
    Measurable ((centeredCube z r hr : Set (SpatialCoordinates d)).indicator (f : SpatialCoordinates d → ℝ)) := by
  have hf : Measurable (f : SpatialCoordinates d → ℝ) := (Lp.stronglyMeasurable f).measurable
  exact hf.indicator (centeredCube z r hr).isOpen.measurableSet

/-- Integrability of the zero extension and of its square on any set. -/
theorem aux_fcp_zeroExt_integrable (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (f : DomainL2 (centeredCube z r hr)) (S : Set (SpatialCoordinates d)) :
    IntegrableOn ((centeredCube z r hr : Set (SpatialCoordinates d)).indicator (f : SpatialCoordinates d → ℝ)) S ∧
    IntegrableOn (fun x => ((centeredCube z r hr : Set (SpatialCoordinates d)).indicator (f : SpatialCoordinates d → ℝ) x) ^ 2) S := by
  classical
  set Q : Set (SpatialCoordinates d) := (centeredCube z r hr : Set (SpatialCoordinates d)) with hQ
  have hQmeas : MeasurableSet Q := (centeredCube z r hr).isOpen.measurableSet
  haveI hfin : IsFiniteMeasure (volume.restrict Q) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, hQ, centeredCube_volume z hr]
    exact ENNReal.ofReal_lt_top
  have hmem : MemLp (f : SpatialCoordinates d → ℝ) 2 (volume.restrict Q) := Lp.memLp f
  have hfint : IntegrableOn (f : SpatialCoordinates d → ℝ) Q := hmem.integrable (by norm_num)
  have hsqint : IntegrableOn (fun x => (f : SpatialCoordinates d → ℝ) x ^ 2) Q :=
    hmem.integrable_sq
  have h1 : Integrable (Q.indicator (f : SpatialCoordinates d → ℝ)) volume :=
    hfint.integrable_indicator hQmeas
  have h2 : Integrable (Q.indicator (fun x => (f : SpatialCoordinates d → ℝ) x ^ 2)) volume :=
    hsqint.integrable_indicator hQmeas
  refine ⟨h1.integrableOn, ?_⟩
  have hsqeq : (fun x => (Q.indicator (f : SpatialCoordinates d → ℝ) x) ^ 2)
      = Q.indicator (fun x => (f : SpatialCoordinates d → ℝ) x ^ 2) := by
    funext x
    by_cases hx : x ∈ Q <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  rw [hsqeq]
  exact h2.integrableOn


/-! ### Small algebra helpers (kept separate to keep elaboration cheap) -/

theorem aux_fcp_sum_const_ofReal {α : Type*} (S : Finset α) (b : ℝ) (_hb : 0 ≤ b) :
    ∑ _p ∈ S, ENNReal.ofReal b = ENNReal.ofReal (S.card * b) := by
  rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- The seminorm part: from the per-cube bounds and the near/far split. -/
theorem aux_fcp_semi_bound {ι : Type*} (S : Finset ι) (loc : ι → ℝ≥0∞) (I : ℝ≥0∞) (far B C2 L2 : ℝ)
    (hB0 : 0 ≤ B) (hC2 : 0 ≤ C2) (hL2 : 0 ≤ L2)
    (hNF : I ≤ (∑ p ∈ S, loc p) + ENNReal.ofReal far) (hfar : far ≤ C2 * L2)
    (hloc : ∀ p ∈ S, loc p ≤ ENNReal.ofReal B) :
    I.toReal ≤ S.card * B + C2 * L2 := by
  apply ENNReal.toReal_le_of_le_ofReal (by positivity)
  calc I ≤ (∑ p ∈ S, loc p) + ENNReal.ofReal far := hNF
    _ ≤ (∑ _p ∈ S, ENNReal.ofReal B) + ENNReal.ofReal (C2 * L2) := by
        gcongr with p hp
        · exact hloc p hp
    _ = ENNReal.ofReal (S.card * B) + ENNReal.ofReal (C2 * L2) := by rw [aux_fcp_sum_const_ofReal S B hB0]
    _ = ENNReal.ofReal (S.card * B + C2 * L2) := (ENNReal.ofReal_add (by positivity) (by positivity)).symm

theorem aux_fcp_final_arith (M C1 C2 B L2 S : ℝ) (_hM : 0 ≤ M) (_hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (_hB : 0 ≤ B)
    (hL2 : L2 ≤ C1 * B) (hS : S ≤ M * B + C2 * L2) :
    L2 + S ≤ (C1 + M + C2 * C1) * B := by
  have : C2 * L2 ≤ C2 * (C1 * B) := mul_le_mul_of_nonneg_left hL2 hC2
  nlinarith

theorem aux_fcp_centers_card_pos (z : SpatialCoordinates d) (N : ℕ) : 0 < (aux_fcp_centers z N).card := by
  refine Finset.card_pos.mpr ⟨aux_fcp_center z 0, Finset.mem_image.mpr ⟨0, ?_, rfl⟩⟩
  simp [aux_fcp_box, Fintype.mem_piFinset]

end FCP

open FCP in
theorem inputs_classical_fractional_coercivity_patching
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ (centers : Finset (SpatialCoordinates d)) (C : ℝ), 0 < C ∧
      ∀ (c : SpatialCoordinates d → ℝ), Continuous c → (∀ x, 0 < c x) →
      ∀ (aQ : PositiveCoefficient (centeredCube z r hr)),
        ((aQ.val : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] c) →
      ∀ (a : (i : centers) → PositiveCoefficient (centeredCube i.val 1 one_pos)),
        (∀ i : centers, ((a i).val : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube i.val 1 one_pos : Set (SpatialCoordinates d))] c) →
      ∀ K : ℝ, 0 ≤ K →
        (∀ (i : centers) (w : meanZeroSobolevGraph (centeredCube i.val 1 one_pos)),
          cubeFractionalSqNorm hd i.val 1 one_pos threeQuarterOrder w.val.1 ≤
            K * sobolevCoefficientForm (a i) w.val w.val) →
        ∀ v : killedSobolevGraph (centeredCube z r hr),
          ‖v.val.1‖ ^ 2 + volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
              (cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
                (fun _ : Fin 1 => v.val.1)).toReal ^ 2 ≤
            C * K * sobolevCoefficientForm aQ v.val v.val := by
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ⌈r⌉₊ + 2 := ⟨_, rfl⟩
  have hN : r + 1 ≤ (N : ℝ) := by
    have := Nat.le_ceil r
    rw [hNdef]; push_cast; linarith
  have hMpos : (0 : ℝ) < (FCP.aux_fcp_centers z N).card := by exact_mod_cast aux_fcp_centers_card_pos z N
  have hC1pos : (0 : ℝ) < (FCP.aux_fcp_centers z N).card * (2 + 16 * (2 * N + 1) ^ 2) := by positivity
  have hC2nn : (0 : ℝ) ≤ (3 / 4 : ℝ) * 4 ^ ((d : ℝ) + 2 * (3 / 4 : ℝ)) * 4 * r ^ d := by positivity
  refine ⟨FCP.aux_fcp_centers z N, (FCP.aux_fcp_centers z N).card * (2 + 16 * (2 * N + 1) ^ 2) +
    (FCP.aux_fcp_centers z N).card + ((3 / 4 : ℝ) * 4 ^ ((d : ℝ) + 2 * (3 / 4 : ℝ)) * 4 * r ^ d) *
      ((FCP.aux_fcp_centers z N).card * (2 + 16 * (2 * N + 1) ^ 2)), by positivity, ?_⟩
  intro c _hc hcpos aQ haQ a ha K hK hloc v
  have hE0 : 0 ≤ sobolevCoefficientForm aQ v.val v.val := sobolevCoefficientForm_nonneg aQ v.val
  have hfacts := aux_fcp_local_facts hd z hr N hN c hcpos aQ haQ a ha K hK hloc v
  obtain ⟨g, hg⟩ : ∃ g : SpatialCoordinates d → ℝ,
      g = (centeredCube z r hr : Set (SpatialCoordinates d)).indicator (v.val.1 : SpatialCoordinates d → ℝ) :=
    ⟨_, rfl⟩
  rw [← hg] at hfacts
  have hfg : (v.val.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] g := by
    filter_upwards [ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx
    rw [hg, Set.indicator_of_mem hx]
  have hint := aux_fcp_zeroExt_integrable z hr v.val.1
  rw [← hg] at hint
  have hL2 := aux_fcp_l2_bound hd z hr N hN g
    (fun x hx => by rw [hg, Set.indicator_of_notMem hx]) (integrableOn_univ.mp (hint univ).2)
    (integrableOn_univ.mp (hint univ).1) _ hfacts.1
  have hgm : Measurable g := by rw [hg]; exact aux_fcp_zeroExt_measurable z hr v.val.1
  have hNF := aux_fcp_near_far hd z hr N hN (3 / 4) (by norm_num) (by norm_num) g (hint _).2 hgm
  have hS := aux_fcp_semi_bound (FCP.aux_fcp_centers z N) (fun p => ENNReal.ofReal (3 / 4) *
      ∫⁻ x in aux_fcp_ucube p, ∫⁻ y in aux_fcp_ucube p, aux_fcp_gq (3 / 4) g x y) _ _ _ _ _
    (mul_nonneg hK hE0) hC2nn (integral_nonneg fun x => sq_nonneg (g x)) hNF le_rfl hfacts.2
  have hsq : ((threeQuarterOrder : Set.Ioo (0 : ℝ) 1) : ℝ) = 3 / 4 := rfl
  rw [aux_fcp_norm_sq_eq z hr v.val.1 g hfg, aux_fcp_seminorm_sq_eq hd z hr threeQuarterOrder v.val.1 g hfg, hsq]
  have := aux_fcp_final_arith _ _ _ _ _ _ hMpos.le hC1pos.le hC2nn (mul_nonneg hK hE0) hL2 hS
  calc _ ≤ _ := this
    _ = _ := by ring

end Paper
