module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeLayerEvents

@[expose] public section




set_option autoImplicit false

open MeasureTheory ProbabilityTheory Homogenization Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.Section9 (centeredAxisCube)

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open SubdiffusiveProcess.Frozen.Assumptions

variable {d : ℕ}

/-! ## `supWithZero` depends only on the range -/

theorem range_option_elim {X : Type*} (f : X → ℝ) :
    Set.range (fun o : Option X => o.elim 0 f) = insert 0 (Set.range f) := by
  ext r
  constructor
  · rintro ⟨o, rfl⟩
    cases o with
    | none => exact Set.mem_insert 0 _
    | some x => exact Set.mem_insert_of_mem _ ⟨x, rfl⟩
  · rintro (rfl | ⟨x, rfl⟩)
    · exact ⟨none, rfl⟩
    · exact ⟨some x, rfl⟩

/-- The boxed observables are supremum-of-a-range constructions, so any
reindexing with the same value set leaves them unchanged. -/
theorem supWithZero_eq_of_range_eq {X Y : Type*} {f : X → ℝ} {g : Y → ℝ}
    (h : Set.range f = Set.range g) : supWithZero f = supWithZero g := by
  unfold supWithZero
  rw [range_option_elim, range_option_elim, h]

/-! ## Geometry of the rescaled box -/

/-- The rescaled displacement of a point of a ball of radius `R` from the ball's
centre lies in the triadic cube of side `3^r`, once `2R < 3^k·3^r`.  This is the
depth-`r` form of `scaled_shift_mem_unitCube`. -/
theorem scaled_shift_mem_originCube {k : ℕ} {r : ℤ} {R : ℝ}
    (hk : 2 * R < (3 : ℝ) ^ k * (3 : ℝ) ^ r) {x w : Vec d}
    (hw : w ∈ Metric.closedBall x R) :
    ((3 : ℝ) ^ k)⁻¹ • w - ((3 : ℝ) ^ k)⁻¹ • x ∈ openCubeSet (originCube d r) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  rw [Metric.mem_closedBall, dist_eq_norm] at hw
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hcoord : |(w - x) i| ≤ ‖w - x‖ := norm_le_pi_norm (w - x) i
  have h1 : |(w - x) i| ≤ R := hcoord.trans hw
  have h2 : ((3 : ℝ) ^ k)⁻¹ * |(w - x) i| ≤ ((3 : ℝ) ^ k)⁻¹ * R :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h4 : (1 : ℝ) / 2 * ((3 : ℝ) ^ k * (3 : ℝ) ^ r)
      = (1 / 2 : ℝ) * (3 : ℝ) ^ r * (3 : ℝ) ^ k := by ring
  have h5 : ((3 : ℝ) ^ k)⁻¹ * R < (1 / 2 : ℝ) * (3 : ℝ) ^ r := by
    rw [inv_mul_eq_div, div_lt_iff₀ h3, ← h4]
    linarith
  have hkey : ((3 : ℝ) ^ k)⁻¹ * |(w - x) i| < (1 / 2 : ℝ) * (3 : ℝ) ^ r := h2.trans_lt h5
  have hpos : (0 : ℝ) ≤ ((3 : ℝ) ^ k)⁻¹ * |(w - x) i| :=
    mul_nonneg (by positivity) (abs_nonneg _)
  rw [← smul_sub, Pi.smul_apply, smul_eq_mul]
  have habs : |((3 : ℝ) ^ k)⁻¹ * (w - x) i| < (1 / 2 : ℝ) * (3 : ℝ) ^ r := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ((3 : ℝ) ^ k)⁻¹)]
    exact hkey
  exact ⟨by linarith [(abs_lt.mp habs).1], (abs_lt.mp habs).2⟩

/-- Membership of a translated triadic cube from a sup-norm ball. -/
theorem sub_mem_originCube_of_mem_closedBall {r : ℤ} {rho : ℝ}
    (h : rho < (1 / 2 : ℝ) * (3 : ℝ) ^ r) {y x : Vec d}
    (hx : x ∈ Metric.closedBall y rho) :
    x - y ∈ openCubeSet (originCube d r) := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hx
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hle : |(x - y) i| ≤ ‖x - y‖ := norm_le_pi_norm (x - y) i
  have habs : |(x - y) i| < (1 / 2 : ℝ) * (3 : ℝ) ^ r := by linarith
  exact ⟨by linarith [(abs_lt.mp habs).1], (abs_lt.mp habs).2⟩

/-! ## The translated cover readouts -/

/-- **The translated pointwise readout.**  A uniform bound `G` on the `(g2)`
gauges of the cubes of the cover of `y + cu_r` bounds the gradient at every
point of that cube. -/
theorem norm_deriv_le_of_forall_g2_le (g : PotentialField d) (y : Vec d)
    {r : ℤ} {G : ℝ}
    (hG : ∀ p ∈ shellCoverShifts d r,
      PotentialField.g2Observable (PotentialField.translate (y + shellCoverCenter p) g) ≤ G)
    {w : Vec d} (hw : w - y ∈ openCubeSet (originCube d r)) :
    ‖PotentialField.deriv g w‖ ≤ G := by
  obtain ⟨p, hp, hwp⟩ := exists_shellCoverShift_mem hw
  rw [mem_translateSet_iff_sub_mem] at hwp
  have h := PotentialField.norm_deriv_le_g2Observable
    (PotentialField.translate (y + shellCoverCenter p) g) hwp
  rw [Section6Anchored.deriv_translate] at h
  have hc : w - y - shellCoverCenter p + (y + shellCoverCenter p) = w := by abel
  rw [hc] at h
  exact h.trans (hG p hp)

/-- **The translated variant of
`SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.norm_deriv_unscalePotential_sub_le_of_forall_le`**
(the lemma P-341 named as the next step for obligation O10).  A uniform bound
`G` on the gauges of every cube of the cover of the *translated* triadic cube
`y + cu_r` gives the Lipschitz seminorm bound `G` on any convex subset, with no
loss.  The proof is segment chaining plus the two-point cover lemma, run in the
coordinates recentred at `y`. -/
theorem norm_deriv_sub_le_of_forall_g2_le (g : PotentialField d) (y : Vec d)
    {r : ℤ} {G : ℝ}
    (hG : ∀ p ∈ shellCoverShifts d r,
      PotentialField.g2Observable (PotentialField.translate (y + shellCoverCenter p) g) ≤ G)
    {S : Set (Vec d)} (hS : Convex ℝ S)
    (hSsub : ∀ x ∈ S, x - y ∈ openCubeSet (originCube d r))
    {w w' : Vec d} (hw : w ∈ S) (hw' : w' ∈ S) :
    ‖PotentialField.deriv g w - PotentialField.deriv g w'‖ ≤ G * ‖w - w'‖ := by
  refine Section6Anchored.norm_sub_le_mul_of_forall_norm_sub_le hS
    (by norm_num : (0 : ℝ) < (6 : ℝ)⁻¹) ?_ hw hw'
  intro a ha b hb hab
  have hau : a - y ∈ openCubeSet (originCube d r) := hSsub a ha
  have hdiff : ‖(a - y) - (b - y)‖ ≤ (6 : ℝ)⁻¹ := by
    have hrw : (a - y) - (b - y) = a - b := by abel
    rw [hrw]; exact hab
  obtain ⟨p, hp, hap, hbp⟩ := Section6Anchored.exists_shellCoverShift_mem_pair hau hdiff
  rw [mem_translateSet_iff_sub_mem] at hap hbp
  have hbound := PotentialField.norm_deriv_sub_deriv_le_g2Observable_mul
    (PotentialField.translate (y + shellCoverCenter p) g) hap hbp
  rw [Section6Anchored.deriv_translate, Section6Anchored.deriv_translate] at hbound
  have hc1 : a - y - shellCoverCenter p + (y + shellCoverCenter p) = a := by abel
  have hc2 : b - y - shellCoverCenter p + (y + shellCoverCenter p) = b := by abel
  have hc3 : a - y - shellCoverCenter p - (b - y - shellCoverCenter p) = a - b := by abel
  rw [hc1, hc2, hc3] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_right (hG p hp) (norm_nonneg _))

/-! ## The covering gauge -/

/-- The maximum of the own-scale `(g2)` gauges of shell `k` over the cubes of
the `1/3`-mesh cover of the translated triadic cube `y + cu_r`.  This is
`SubdiffusiveProcess.CoarseGrainingVocab.largeCubeShellG2` recentred at `y`. -/
def coverShellG2 (k : ℕ) (y : Vec d) (r : ℤ) (omega : PotentialSample d) : ℝ :=
  (shellCoverShifts d r).sup' (shellCoverShifts_nonempty d r) fun p =>
    translatedShellG2 k (y + shellCoverCenter p) omega

theorem le_coverShellG2 (k : ℕ) (y : Vec d) {r : ℤ} (omega : PotentialSample d)
    {p : Fin d → ℤ} (hp : p ∈ shellCoverShifts d r) :
    translatedShellG2 k (y + shellCoverCenter p) omega ≤ coverShellG2 k y r omega :=
  Finset.le_sup' (fun q => translatedShellG2 k (y + shellCoverCenter q) omega) hp

theorem coverShellG2_nonneg (k : ℕ) (y : Vec d) (r : ℤ) (omega : PotentialSample d) :
    0 ≤ coverShellG2 k y r omega := by
  obtain ⟨p, hp⟩ := shellCoverShifts_nonempty d r
  exact (translatedShellG2_nonneg _ _ _).trans (le_coverShellG2 k y omega hp)

/-- The hypothesis form the two readouts consume. -/
theorem forall_g2_le_coverShellG2 (k : ℕ) (y : Vec d) (r : ℤ)
    (omega : PotentialSample d) :
    ∀ p ∈ shellCoverShifts d r,
      PotentialField.g2Observable
          (PotentialField.translate (y + shellCoverCenter p)
            (unscalePotential k (omega k))) ≤ coverShellG2 k y r omega :=
  fun _ hp => le_coverShellG2 k y omega hp

/-! ## The boxed observables on a box of several wavelengths -/

/-- **The gradient sup-norm on a wide box.**  No hypothesis relating the box to
one wavelength: the cover absorbs the excess into the prefactor. -/
theorem boxDerivNorm_le_coverShellG2 {k : ℕ} {r : ℤ} {R : ℝ}
    (hk : 2 * R < (3 : ℝ) ^ k * (3 : ℝ) ^ r) (omega : PotentialSample d) (x : Vec d)
    {K : Set (Vec d)} (hK : K ⊆ Metric.closedBall x R) :
    boxDerivNorm K (omega k) ≤
      ((3 : ℝ) ^ k)⁻¹ * coverShellG2 k (((3 : ℝ) ^ k)⁻¹ • x) r omega := by
  have hnonneg : 0 ≤ ((3 : ℝ) ^ k)⁻¹ * coverShellG2 k (((3 : ℝ) ^ k)⁻¹ • x) r omega :=
    mul_nonneg (by positivity) (coverShellG2_nonneg _ _ _ _)
  refine supWithZero_le hnonneg ?_
  intro w
  have hmem := scaled_shift_mem_originCube hk (hK w.2)
  have hg := norm_deriv_le_of_forall_g2_le (unscalePotential k (omega k))
    (((3 : ℝ) ^ k)⁻¹ • x) (forall_g2_le_coverShellG2 k _ r omega) hmem
  rw [Section6Anchored.deriv_eq_smul_deriv_unscalePotential k (omega k) w.1, norm_smul,
    Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < ((3 : ℝ) ^ k)⁻¹)]
  exact mul_le_mul_of_nonneg_left hg (by positivity)

/-- **The gradient Lipschitz seminorm on a wide box.**  This is where the
translated segment-chaining lemma is used: two points of the box need not lie in
a common cube of the cover. -/
theorem boxDerivLipschitzSeminorm_le_coverShellG2 {k : ℕ} {r : ℤ} {R : ℝ}
    (hk : 2 * R < (3 : ℝ) ^ k * (3 : ℝ) ^ r) (omega : PotentialSample d) (x : Vec d)
    {K : Set (Vec d)} (hK : K ⊆ Metric.closedBall x R) :
    boxDerivLipschitzSeminorm K (omega k) ≤
      ((3 : ℝ) ^ k)⁻¹ * (((3 : ℝ) ^ k)⁻¹ * coverShellG2 k (((3 : ℝ) ^ k)⁻¹ • x) r omega) := by
  have h3 : (0 : ℝ) < ((3 : ℝ) ^ k)⁻¹ := by positivity
  have h3' : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  set y : Vec d := ((3 : ℝ) ^ k)⁻¹ • x with hy
  set G : ℝ := coverShellG2 k y r omega with hGdef
  have hnonneg : 0 ≤ ((3 : ℝ) ^ k)⁻¹ * (((3 : ℝ) ^ k)⁻¹ * G) :=
    mul_nonneg h3.le (mul_nonneg h3.le (coverShellG2_nonneg _ _ _ _))
  -- the rescaled box, as a convex subset of the translated triadic cube
  set S : Set (Vec d) := Metric.closedBall y (((3 : ℝ) ^ k)⁻¹ * R) with hS
  have hSconv : Convex ℝ S := convex_closedBall _ _
  have hrho : ((3 : ℝ) ^ k)⁻¹ * R < (1 / 2 : ℝ) * (3 : ℝ) ^ r := by
    rw [inv_mul_eq_div, div_lt_iff₀ h3']
    nlinarith
  have hSsub : ∀ u ∈ S, u - y ∈ openCubeSet (originCube d r) := fun u hu =>
    sub_mem_originCube_of_mem_closedBall hrho hu
  have hmemS : ∀ w ∈ K, ((3 : ℝ) ^ k)⁻¹ • w ∈ S := by
    intro w hw
    have hd := hK hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hd ⊢
    rw [hy, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos h3]
    exact mul_le_mul_of_nonneg_left hd h3.le
  refine supWithZero_le hnonneg ?_
  intro p
  have hne : p.1.1.1 ≠ p.1.2.1 := fun h => p.property (Subtype.ext h)
  have hdpos : 0 < dist p.1.1.1 p.1.2.1 := dist_pos.mpr hne
  have hchain := norm_deriv_sub_le_of_forall_g2_le (unscalePotential k (omega k)) y
    (forall_g2_le_coverShellG2 k y r omega) hSconv hSsub
    (hmemS _ p.1.1.2) (hmemS _ p.1.2.2)
  have hscaled : ‖((3 : ℝ) ^ k)⁻¹ • p.1.1.1 - ((3 : ℝ) ^ k)⁻¹ • p.1.2.1‖ =
      ((3 : ℝ) ^ k)⁻¹ * ‖p.1.1.1 - p.1.2.1‖ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos h3]
  rw [hscaled] at hchain
  have hkey : PotentialField.deriv (omega k) p.1.1.1 - PotentialField.deriv (omega k) p.1.2.1 =
      ((3 : ℝ) ^ k)⁻¹ •
        (PotentialField.deriv (unscalePotential k (omega k)) (((3 : ℝ) ^ k)⁻¹ • p.1.1.1) -
          PotentialField.deriv (unscalePotential k (omega k)) (((3 : ℝ) ^ k)⁻¹ • p.1.2.1)) := by
    rw [smul_sub, ← Section6Anchored.deriv_eq_smul_deriv_unscalePotential k (omega k) p.1.1.1,
      ← Section6Anchored.deriv_eq_smul_deriv_unscalePotential k (omega k) p.1.2.1]
  rw [div_le_iff₀ hdpos, dist_eq_norm, hkey, norm_smul, Real.norm_eq_abs,
    abs_of_pos h3, dist_eq_norm]
  have hstep := mul_le_mul_of_nonneg_left hchain h3.le
  calc ((3 : ℝ) ^ k)⁻¹ *
        ‖PotentialField.deriv (unscalePotential k (omega k)) (((3 : ℝ) ^ k)⁻¹ • p.1.1.1) -
          PotentialField.deriv (unscalePotential k (omega k)) (((3 : ℝ) ^ k)⁻¹ • p.1.2.1)‖
      ≤ ((3 : ℝ) ^ k)⁻¹ * (G * (((3 : ℝ) ^ k)⁻¹ * ‖p.1.1.1 - p.1.2.1‖)) := hstep
    _ = ((3 : ℝ) ^ k)⁻¹ * (((3 : ℝ) ^ k)⁻¹ * G) * ‖p.1.1.1 - p.1.2.1‖ := by ring



theorem layerObservable_le_coverShellG2 (n j : ℕ) {C : ℝ} {r : ℤ}
    (hC : 0 ≤ C) (hCr : C < (3 : ℝ) ^ r) (z : Lattice d) (omega : PotentialSample d) :
    layerObservable n (nativeBox n C z) (omega (n + j)) ≤
      2 * ((3 : ℝ) ^ j)⁻¹ *
        coverShellG2 (n + j) (((3 : ℝ) ^ (n + j))⁻¹ • goodCubeCentre n z) r omega := by
  have han : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hbj : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  have hb1 : (1 : ℝ) ≤ (3 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hsplit : (3 : ℝ) ^ (n + j) = (3 : ℝ) ^ n * (3 : ℝ) ^ j := pow_add _ _ _
  have hR : nativeBox n C z ⊆
      Metric.closedBall (goodCubeCentre n z) (C * (3 : ℝ) ^ n / 2) :=
    centeredAxisCube_subset_closedBall _ (by positivity)
  have hk : 2 * (C * (3 : ℝ) ^ n / 2) < (3 : ℝ) ^ (n + j) * (3 : ℝ) ^ r := by
    rw [hsplit]
    have h1 : C * (3 : ℝ) ^ n < (3 : ℝ) ^ r * (3 : ℝ) ^ n :=
      mul_lt_mul_of_pos_right hCr han
    have h2 : (3 : ℝ) ^ r * (3 : ℝ) ^ n ≤ (3 : ℝ) ^ n * (3 : ℝ) ^ j * (3 : ℝ) ^ r := by
      have : (3 : ℝ) ^ r * (3 : ℝ) ^ n * 1 ≤ (3 : ℝ) ^ r * (3 : ℝ) ^ n * (3 : ℝ) ^ j :=
        mul_le_mul_of_nonneg_left hb1 (by positivity)
      nlinarith [this]
    linarith
  set T := coverShellG2 (n + j) (((3 : ℝ) ^ (n + j))⁻¹ • goodCubeCentre n z) r omega with hT
  have hTnonneg : 0 ≤ T := coverShellG2_nonneg _ _ _ _
  have hgrad := boxDerivNorm_le_coverShellG2 hk omega (goodCubeCentre n z) hR
  have hhess := boxDerivLipschitzSeminorm_le_coverShellG2 hk omega (goodCubeCentre n z) hR
  have hinv : ((3 : ℝ) ^ (n + j))⁻¹ = ((3 : ℝ) ^ n)⁻¹ * ((3 : ℝ) ^ j)⁻¹ := by
    rw [hsplit, mul_inv]
  have hstep1 : (3 : ℝ) ^ n * boxDerivNorm (nativeBox n C z) (omega (n + j))
      ≤ ((3 : ℝ) ^ j)⁻¹ * T := by
    have hmul := mul_le_mul_of_nonneg_left hgrad han.le
    calc (3 : ℝ) ^ n * boxDerivNorm (nativeBox n C z) (omega (n + j))
        ≤ (3 : ℝ) ^ n * (((3 : ℝ) ^ (n + j))⁻¹ * T) := hmul
      _ = ((3 : ℝ) ^ j)⁻¹ * T := by rw [hinv]; field_simp
  have hstep2 : ((3 : ℝ) ^ n) ^ 2 *
      boxDerivLipschitzSeminorm (nativeBox n C z) (omega (n + j))
      ≤ (((3 : ℝ) ^ j)⁻¹) ^ 2 * T := by
    have h2 := mul_le_mul_of_nonneg_left hhess (by positivity : (0 : ℝ) ≤ ((3 : ℝ) ^ n) ^ 2)
    calc ((3 : ℝ) ^ n) ^ 2 *
          boxDerivLipschitzSeminorm (nativeBox n C z) (omega (n + j))
        ≤ ((3 : ℝ) ^ n) ^ 2 * (((3 : ℝ) ^ (n + j))⁻¹ * (((3 : ℝ) ^ (n + j))⁻¹ * T)) := h2
      _ = (((3 : ℝ) ^ j)⁻¹) ^ 2 * T := by rw [hinv]; field_simp
  have hsq : (((3 : ℝ) ^ j)⁻¹) ^ 2 * T ≤ ((3 : ℝ) ^ j)⁻¹ * T := by
    have hle : (((3 : ℝ) ^ j)⁻¹) ^ 2 ≤ ((3 : ℝ) ^ j)⁻¹ := by
      have hinv1 : ((3 : ℝ) ^ j)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hb1
      nlinarith [inv_pos.mpr hbj]
    exact mul_le_mul_of_nonneg_right hle hTnonneg
  unfold layerObservable
  have hsum := add_le_add hstep1 (hstep2.trans hsq)
  linarith

/-! ## The union bound and the tail -/

theorem measure_biUnion_finset_le_card_ofReal {Omega iota : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (s : Finset iota) (A : iota → Set Omega) {e : ℝ}
    (hs : ∀ p ∈ s, mu (A p) ≤ ENNReal.ofReal e) :
    mu (⋃ p ∈ s, A p) ≤ ENNReal.ofReal ((s.card : ℝ) * e) := by
  refine (measure_biUnion_finset_le s A).trans ?_
  refine (Finset.sum_le_sum hs).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul,
    ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (s.card : ℝ)), ENNReal.ofReal_natCast]

/-- The per-cube weak-Orlicz tail, at the level the layer event needs. -/
theorem measureReal_upperTail_translatedShellG2_le (M : GMCModel d) (k : ℕ) (y : Vec d)
    {eps1 : ℝ} (jr : ℝ) (hjr : 0 ≤ jr)
    (hdelta : 2 * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) ≤ eps1) :
    M.P.toMeasure.real (Homogenization.IndependentSums.upperTailEvent
        (translatedShellG2 k y) (eps1 * (3 : ℝ) ^ (3 * jr / 4) / 2)) ≤
      Real.exp (-(layerTailConstant * (eps1 ^ 2 / M.delta ^ 2) * (3 : ℝ) ^ (3 * jr / 2))) := by
  have hlog : (0 : ℝ) < 1 + Real.log 2 := by positivity
  have hdpos : 0 < M.delta := M.shellPrefix.delta_pos
  set A : ℝ := (1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta with hA
  have hApos : 0 < A := mul_pos (Real.rpow_pos_of_pos hlog _) hdpos
  set theta : ℝ := eps1 * (3 : ℝ) ^ (3 * jr / 4) / 2 with htheta
  set t : ℝ := theta / A with ht
  have hone : (1 : ℝ) ≤ (3 : ℝ) ^ (3 * jr / 4) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have ht1 : 1 ≤ t := by
    rw [ht, le_div_iff₀ hApos, one_mul, htheta]
    have h1 : A * 2 ≤ eps1 := by rw [hA]; linarith
    nlinarith
  have hAt : A * t = theta := by rw [ht]; field_simp
  have htail := SubdiffusiveProcess.CoarseGrainingVocab.isBigOWith_gammaTwo_translatedShellG2 M k y ht1
  rw [hAt] at htail
  have hAsq : A ^ 2 = (1 + Real.log 2) * M.delta ^ 2 := by
    rw [hA, mul_pow]
    congr 1
    rw [← Real.rpow_natCast ((1 + Real.log 2) ^ (2 : ℝ)⁻¹) 2, ← Real.rpow_mul hlog.le]
    norm_num
  have hsq34 : ((3 : ℝ) ^ (3 * jr / 4)) ^ (2 : ℕ) = (3 : ℝ) ^ (3 * jr / 2) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (3 * jr / 4)) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    push_cast
    ring
  have hthetasq : theta ^ 2 = eps1 ^ 2 * (3 : ℝ) ^ (3 * jr / 2) / 4 := by
    rw [htheta, div_pow, mul_pow, hsq34]
    ring
  have htsq : t ^ 2 =
      layerTailConstant * (eps1 ^ 2 / M.delta ^ 2) * (3 : ℝ) ^ (3 * jr / 2) := by
    rw [ht, div_pow, hthetasq, hAsq, layerTailConstant]
    have h1 : (1 : ℝ) + Real.log 2 ≠ 0 := ne_of_gt hlog
    have h2 : M.delta ≠ 0 := ne_of_gt hdpos
    field_simp
  have hgamma : (Homogenization.IndependentSums.gammaSigma 2 t)⁻¹ =
      Real.exp (-(layerTailConstant * (eps1 ^ 2 / M.delta ^ 2) * (3 : ℝ) ^ (3 * jr / 2))) := by
    rw [Homogenization.IndependentSums.gammaSigma_apply, ← Real.exp_neg]
    congr 1
    rw [← htsq, ← Real.rpow_natCast t 2]
    norm_num
  rw [hgamma] at htail
  exact htail



theorem measure_layerEvent_le_cover (M : GMCModel d) (n j : ℕ) {C eps1 : ℝ} {r : ℤ}
    (hC : 0 ≤ C) (hCr : C < (3 : ℝ) ^ r)
    (hdelta : 2 * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) ≤ eps1)
    (z : Lattice d) :
    M.P.toMeasure (layerEvent n j C eps1 z) ≤
      ENNReal.ofReal (((shellCoverShifts d r).card : ℝ) *
        Real.exp (-(layerTailConstant * (eps1 ^ 2 / M.delta ^ 2) *
          (3 : ℝ) ^ (3 * (j : ℝ) / 2)))) := by
  classical
  set y : Vec d := ((3 : ℝ) ^ (n + j))⁻¹ • goodCubeCentre n z with hy
  set theta : ℝ := eps1 * (3 : ℝ) ^ (3 * (j : ℝ) / 4) / 2 with htheta
  have hpowj : (3 : ℝ) ^ (j : ℝ) = (3 : ℝ) ^ j := by rw [Real.rpow_natCast]
  have hprod : (3 : ℝ) ^ (-(j : ℝ) / 4) * (3 : ℝ) ^ j = (3 : ℝ) ^ (3 * (j : ℝ) / 4) := by
    rw [← hpowj, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
      show (-(j : ℝ) / 4 + (j : ℝ)) = 3 * (j : ℝ) / 4 by ring]
  -- the pathwise inclusion into a union over the cover
  have hincl : layerEvent n j C eps1 z ⊆
      ⋃ p ∈ shellCoverShifts d r,
        Homogenization.IndependentSums.upperTailEvent
          (translatedShellG2 (n + j) (y + shellCoverCenter p)) theta := by
    intro omega homega
    have hdom := layerObservable_le_coverShellG2 n j hC hCr z omega
    have hlt : eps1 * (3 : ℝ) ^ (-(j : ℝ) / 4) <
        2 * ((3 : ℝ) ^ j)⁻¹ * coverShellG2 (n + j) y r omega :=
      lt_of_lt_of_le homega hdom
    have hbj : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
    have hmul := mul_lt_mul_of_pos_right hlt (by positivity : (0 : ℝ) < (3 : ℝ) ^ j / 2)
    have hrw : 2 * ((3 : ℝ) ^ j)⁻¹ * coverShellG2 (n + j) y r omega * ((3 : ℝ) ^ j / 2)
        = coverShellG2 (n + j) y r omega := by field_simp
    rw [hrw] at hmul
    have hleft : eps1 * (3 : ℝ) ^ (-(j : ℝ) / 4) * ((3 : ℝ) ^ j / 2)
        = eps1 * (3 : ℝ) ^ (3 * (j : ℝ) / 4) / 2 := by
      rw [show eps1 * (3 : ℝ) ^ (-(j : ℝ) / 4) * ((3 : ℝ) ^ j / 2)
          = eps1 * ((3 : ℝ) ^ (-(j : ℝ) / 4) * (3 : ℝ) ^ j) / 2 by ring, hprod]
    rw [hleft] at hmul
    unfold coverShellG2 at hmul
    rw [Finset.lt_sup'_iff] at hmul
    obtain ⟨p, hp, hlt'⟩ := hmul
    exact Set.mem_iUnion₂.mpr ⟨p, hp, hlt'⟩
  refine (measure_mono hincl).trans ?_
  refine measure_biUnion_finset_le_card_ofReal _ _ _ ?_
  intro p _
  have hne : M.P.toMeasure (Homogenization.IndependentSums.upperTailEvent
      (translatedShellG2 (n + j) (y + shellCoverCenter p)) theta) ≠ ⊤ := measure_ne_top _ _
  rw [← ENNReal.ofReal_toReal hne]
  refine ENNReal.ofReal_le_ofReal ?_
  exact measureReal_upperTail_translatedShellG2_le M (n + j) _ (j : ℝ)
    (by positivity) hdelta

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
