module

public import SubdiffusiveProcess.MultiplicativeChaos.ChaosBasic
public import SubdiffusiveProcess.MultiplicativeChaos.WeightedIndep
public import Mathlib.MeasureTheory.Integral.Marginal

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped CompactlySupported ENNReal NNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess

/-- The cube mass at cutoff `N` is a measurable function of the fine prefix
`(omega (-j))_{j ≤ N}` alone.  This is the factorization behind the
adaptedness in `chaosCutoff_centeredCube_martingale_nonnegative`, made
explicit so that it can be combined with the independence of `H` from the
fine layers (paper D:39–40). -/
theorem exists_prefix_factorization_chaosCutoff_pow
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (p : ℕ) :
    ∃ psi : ((j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ)) → ℝ,
      Measurable psi ∧
      ∀ omega : BilateralField d,
        ((chaosCutoff M N omega)
          (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p =
          psi (fun j => omega (-(Int.ofNat j))) := by
  classical
  let g : ((j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ)) × SpatialCoordinates d → ℝ :=
    fun q => Real.exp (∑ j : Fin (N + 1), q.1 j q.2 -
      (N + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)
  have hg : StronglyMeasurable g := by
    unfold g
    fun_prop
  refine ⟨fun y => (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
    g (y, x)) ^ p, ?_, ?_⟩
  · exact (hg.integral_prod_right'.measurable).pow_const p
  · intro omega
    rw [chaosCutoff_centeredCube_toReal_eq_integral M N omega z r hr]
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    show fineDensity M N omega x = g (_, x)
    unfold g fineDensity finePotential
    congr 2
    exact (Fin.sum_univ_eq_sum_range
      (fun j : ℕ => (omega (-(Int.ofNat j))) x) (N + 1)).symm

/-- Paper D:39–40: `H` is independent of the fine layers `j ≥ 0`, so any
measurable function of `H` is independent of the cube mass at every cutoff. -/
theorem indepFun_comp_H_chaosCutoff_pow
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (p : ℕ)
    (Phi : C(SpatialCoordinates d, ℝ) → ℝ) (hPhi : Measurable Phi) :
    IndepFun (fun omega : BilateralField d => Phi (H omega))
      (fun omega : BilateralField d =>
        ((chaosCutoff M N omega)
          (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p)
      (chaosSampleLaw M).toMeasure := by
  obtain ⟨psi, hpsi, hpsieq⟩ :=
    exists_prefix_factorization_chaosCutoff_pow M N z r hr p
  have hindep := infraredCharacterization_indepFun_H_finePrefix M H N hH
  refine (hindep.comp hPhi hpsi).congr ?_ ?_
  · filter_upwards with omega
    rfl
  · filter_upwards with omega
    exact (hpsieq omega).symm

/-- Paper D:40–44, the exact factorization: the weight factor and the
unweighted cube moment separate. -/
theorem integral_comp_H_mul_chaosCutoff_pow
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (p : ℕ)
    (Phi : C(SpatialCoordinates d, ℝ) → ℝ) (hPhi : Measurable Phi)
    (hint1 : Integrable (fun omega : BilateralField d => Phi (H omega))
      (chaosSampleLaw M).toMeasure)
    (hint2 : Integrable (fun omega : BilateralField d =>
        ((chaosCutoff M N omega)
          (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p)
      (chaosSampleLaw M).toMeasure) :
    (∫ omega, Phi (H omega) *
        ((chaosCutoff M N omega)
          (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p
      ∂(chaosSampleLaw M).toMeasure) =
      (∫ omega, Phi (H omega) ∂(chaosSampleLaw M).toMeasure) *
        ∫ omega, ((chaosCutoff M N omega)
          (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p
          ∂(chaosSampleLaw M).toMeasure :=
  (indepFun_comp_H_chaosCutoff_pow M H hH N z r hr p Phi hPhi).integral_fun_mul_eq_mul_integral
    hint1.aestronglyMeasurable hint2.aestronglyMeasurable


/-- Paper D:49–57: at a layer index `j` for which every pair of the `p` points
is separated beyond the dependence range `√d·3^{-j}`, the `p`-point moment is
at most `exp (j · c)` with `c = (log 2 / 2) p² δ²`.  Separation is stated in
the ambient sup distance, which is stronger than the Euclidean separation the
frozen multipoint estimate requires. -/
theorem integral_prod_fineDensity_le_of_dist_separated
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (p : ℕ) (hp : 1 ≤ p) (N j : ℕ)
    (y : Fin p → SpatialCoordinates d)
    (hpdelta : (p : ℝ) * M.delta ≤ 1)
    (hsep : Pairwise (fun i k : Fin p =>
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ (-(j : ℤ)) < dist (y i) (y k))) :
    (∫ omega, ∏ k, fineDensity M N omega (y k) ∂(chaosSampleLaw M).toMeasure) ≤
      Real.exp ((j : ℝ) * (Real.log 2 / 2 * (p : ℝ) ^ 2 * M.delta ^ 2)) := by
  have hsep' : Pairwise (fun i k : Fin p =>
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ (-(j : ℤ)) <
        Homogenization.euclideanNorm (y i - y k)) := by
    intro i k hik
    refine lt_of_lt_of_le (hsep hik) ?_
    have h := Homogenization.norm_le_euclideanNorm (y i - y k)
    simpa [dist_eq_norm] using h
  refine (fineDensity_multiPoint_prod_exp_moment_le_of_separated_cutoff
    M p hp N j y hpdelta hsep').trans (Real.exp_le_exp.mpr ?_)
  set c : ℝ := Real.log 2 / 2 * (p : ℝ) ^ 2 * M.delta ^ 2 with hcdef
  have hc : 0 ≤ c := by
    rw [hcdef]; positivity
  have htau : 0 < _root_.SubdiffusiveProcess.Model.tauSq M.P := M.G4.tauSq_pos
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := by positivity
  have hmin : min ((N : ℝ) + 1) (j : ℝ) ≤ (j : ℝ) := min_le_right _ _
  have hmin0 : (0 : ℝ) ≤ min ((N : ℝ) + 1) (j : ℝ) :=
    le_min (by positivity) hj0
  have hptau : 0 ≤ (p : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P := by positivity
  rcases le_or_gt 0 (c - (p : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) with hpos | hneg
  · calc min ((N : ℝ) + 1) (j : ℝ) * (c - (p : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)
        ≤ (j : ℝ) * (c - (p : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) :=
          mul_le_mul_of_nonneg_right hmin hpos
      _ ≤ (j : ℝ) * c := by
          apply mul_le_mul_of_nonneg_left _ hj0
          linarith
  · calc min ((N : ℝ) + 1) (j : ℝ) * (c - (p : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)
        ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hmin0 hneg.le
      _ ≤ (j : ℝ) * c := mul_nonneg hj0 hc


/-- Paper D:55–57, the elementary half: the dependence range `D·3^{-j}` drops
below any positive separation `m`. -/
theorem exists_three_zpow_mul_lt (D m : ℝ) (hD : 0 < D) (hm : 0 < m) :
    ∃ j : ℕ, D * (3 : ℝ) ^ (-(j : ℤ)) < m := by
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (D / m) (by norm_num : (1 : ℝ) < 3)
  refine ⟨j, ?_⟩
  have h3 : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  have hzp : (3 : ℝ) ^ (-(j : ℤ)) = ((3 : ℝ) ^ j)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  rw [hzp, mul_inv_lt_iff₀ h3]
  have hstep : D < (3 : ℝ) ^ j * m := by
    calc D = (D / m) * m := by field_simp
      _ < (3 : ℝ) ^ j * m := mul_lt_mul_of_pos_right hj hm
  linarith [mul_comm ((3 : ℝ) ^ j) m]

/-- Paper D:55–57: for `p` points that are pairwise distinct there is a layer
index beyond which every pair is separated by more than the dependence range.
Vacuous, hence trivially true, when `p ≤ 1`. -/
theorem exists_dist_separation_index
    {d p : ℕ} (y : Fin p → SpatialCoordinates d)
    (hne : Pairwise (fun i k : Fin p => y i ≠ y k)) :
    ∃ j : ℕ, Pairwise (fun i k : Fin p =>
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ (-(j : ℤ)) < dist (y i) (y k)) := by
  classical
  by_cases hd0 : (0 : ℝ) < Real.sqrt (d : ℝ)
  · classical
    set T : Finset (Fin p × Fin p) :=
      Finset.univ.filter (fun q : Fin p × Fin p => q.1 ≠ q.2) with hT
    have hmemT : ∀ q : Fin p × Fin p, q ∈ T ↔ q.1 ≠ q.2 := by
      intro q
      simp [hT]
    by_cases hTne : T.Nonempty
    · set m : ℝ := T.inf' hTne (fun q => dist (y q.1) (y q.2)) with hm
      have hmpos : 0 < m := by
        rw [hm, Finset.lt_inf'_iff]
        intro q hq
        exact dist_pos.mpr (hne ((hmemT q).mp hq))
      obtain ⟨j, hj⟩ := exists_three_zpow_mul_lt _ m hd0 hmpos
      refine ⟨j, ?_⟩
      intro i k hik
      refine lt_of_lt_of_le hj ?_
      rw [hm]
      exact Finset.inf'_le (fun q : Fin p × Fin p => dist (y q.1) (y q.2))
        ((hmemT (i, k)).mpr hik)
    · refine ⟨0, ?_⟩
      intro i k hik
      exact absurd ⟨(i, k), (hmemT (i, k)).mpr hik⟩ hTne
  · refine ⟨0, ?_⟩
    intro i k hik
    have hzero : Real.sqrt (d : ℝ) = 0 :=
      le_antisymm (le_of_not_gt hd0) (Real.sqrt_nonneg _)
    rw [hzero, zero_mul]
    exact dist_pos.mpr (hne hik)

/-- The finite geometric identity behind the layer decomposition of paper
D:55–57: `e^{m c} = 1 + (e^c - 1) Σ_{j < m} e^{j c}`.  It is what removes the
`1/(e^c - 1)` that a naive geometric sum would leave behind, so that the
constant in eq. (38) stays bounded as the disorder tends to zero. -/
theorem exp_nat_mul_eq_one_add_geom (c : ℝ) (m : ℕ) :
    Real.exp ((m : ℝ) * c) =
      1 + (Real.exp c - 1) * ∑ j ∈ Finset.range m, Real.exp ((j : ℝ) * c) := by
  have hgeom := geom_sum_mul (Real.exp c) m
  have hrw : ∀ j : ℕ, Real.exp ((j : ℝ) * c) = Real.exp c ^ j :=
    fun j => Real.exp_nat_mul c j
  simp only [hrw]
  rw [mul_comm (Real.exp c - 1), hgeom]
  ring


/-- Integrating a constant over a finite block of coordinates multiplies it by
the product of the total masses.  Mathlib has `lmarginal` but not this. -/
theorem lmarginal_const
    {D : Type*} [DecidableEq D] {X : D → Type*}
    [∀ i, MeasurableSpace (X i)]
    (mu : ∀ i, Measure (X i)) [∀ i, SigmaFinite (mu i)]
    (s : Finset D) (c : ℝ≥0∞) :
    lmarginal mu s (fun _ => c) = fun _ => c * ∏ i ∈ s, mu i Set.univ := by
  classical
  induction s using Finset.induction_on generalizing c with
  | empty => simp [lmarginal_empty]
  | @insert i t hi ih =>
      rw [lmarginal_insert' _ measurable_const hi]
      funext x
      simp only [lintegral_const]
      rw [ih (c * mu i Set.univ), Finset.prod_insert hi]
      ring

/-- Bounding a function by a constant on a block of coordinates. -/
theorem lmarginal_le_const
    {D : Type*} [DecidableEq D] {X : D → Type*}
    [∀ i, MeasurableSpace (X i)]
    (mu : ∀ i, Measure (X i)) [∀ i, SigmaFinite (mu i)]
    (s : Finset D) (c : ℝ≥0∞) (f : ((i : D) → X i) → ℝ≥0∞)
    (hf : ∀ x, f x ≤ c) (x : (i : D) → X i) :
    lmarginal mu s f x ≤ c * ∏ i ∈ s, mu i Set.univ := by
  have hmono : lmarginal mu s f ≤ lmarginal mu s (fun _ => c) :=
    lmarginal_mono (fun y => hf y)
  have := hmono x
  rwa [lmarginal_const mu s c] at this


/-- Paper D:57–60, the product-measure step: the integral over the `p`-fold
product of a function of two distinct coordinates is controlled by a uniform
bound on the single inner integral, times the total mass of the remaining
`p - 1` coordinates.  Proved with `lmarginal`, so no product-measure
equivalence is needed. -/
theorem lintegral_pi_two_coords_le
    {X : Type*} [MeasurableSpace X] [Inhabited X] (nu : Measure X)
    [SigmaFinite nu] (p : ℕ) (i k : Fin p) (hik : i ≠ k)
    (W : X → X → ℝ≥0∞) (hW : Measurable (fun q : X × X => W q.1 q.2))
    (C : ℝ≥0∞) (hC : ∀ u, (∫⁻ v, W u v ∂nu) ≤ C) :
    (∫⁻ y : Fin p → X, W (y i) (y k) ∂(Measure.pi fun _ : Fin p => nu)) ≤
      C * (nu Set.univ) ^ (p - 1) := by
  classical
  set mu : Fin p → Measure X := fun _ => nu with hmu
  set f : (Fin p → X) → ℝ≥0∞ := fun y => W (y i) (y k) with hfdef
  have hfmeas : Measurable f := by
    simp only [hfdef]
    have hpair : Measurable (fun y : Fin p → X => (y i, y k)) :=
      (measurable_pi_apply i).prodMk (measurable_pi_apply k)
    have hcomp := hW.comp hpair
    simpa [Function.comp_def] using hcomp
  have hkey : lmarginal mu Finset.univ f =
      lmarginal mu (Finset.univ.erase k)
        (fun x => ∫⁻ t, f (Function.update x k t) ∂mu k) :=
    lmarginal_erase' f hfmeas (Finset.mem_univ k)
  have hbody : ∀ x : Fin p → X,
      (∫⁻ t, f (Function.update x k t) ∂mu k) ≤ C := by
    intro x
    have hpt : ∀ t : X, f (Function.update x k t) = W (x i) t := by
      intro t
      simp only [hfdef, Function.update_self, Function.update_of_ne hik]
    simp_rw [hpt]
    exact hC (x i)
  have hle := lmarginal_le_const mu (Finset.univ.erase k) C
    (fun x => ∫⁻ t, f (Function.update x k t) ∂mu k) hbody
    (default : Fin p → X)
  have hcard : ((Finset.univ : Finset (Fin p)).erase k).card = p - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ,
      Fintype.card_fin]
  have hprod : ∏ _j ∈ (Finset.univ : Finset (Fin p)).erase k, nu Set.univ =
      (nu Set.univ) ^ (p - 1) := by
    rw [Finset.prod_const, hcard]
  have hstart : (∫⁻ y : Fin p → X, f y ∂(Measure.pi mu)) =
      lmarginal mu Finset.univ f (default : Fin p → X) := by
    rw [lmarginal_univ]
  rw [hstart, hkey]
  refine le_trans hle ?_
  rw [hmu, hprod]


/-- `m` is below the weighted geometric mean of any two of its upper bounds.
This is what replaces the paper's case split at the scale `3^{-j} ~ r`
(paper D:57-60): one geometric series instead of two. -/
theorem le_rpow_mul_rpow_of_le_of_le
    (m A B theta : ℝ) (hm : 0 ≤ m) (hA : m ≤ A) (hB : m ≤ B)
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    m ≤ A ^ (1 - theta) * B ^ theta := by
  rcases eq_or_lt_of_le hm with hm0 | hmpos
  · rw [← hm0]
    exact mul_nonneg (Real.rpow_nonneg (hm.trans hA) _)
      (Real.rpow_nonneg (hm.trans hB) _)
  · have he : (1 - theta) + theta = 1 := by ring
    have hsplit : m ^ (1 - theta) * m ^ theta = m := by
      rw [← Real.rpow_add hmpos, he, Real.rpow_one]
    rw [← hsplit]
    exact mul_le_mul (Real.rpow_le_rpow hm hA (by linarith))
      (Real.rpow_le_rpow hm hB h0) (Real.rpow_nonneg hm _)
      (Real.rpow_nonneg (hm.trans hA) _)

/-- `x e^{-x} ≤ 1 - e^{-x}`: the elementary fact that keeps the constant
`(e^c - 1) / (1 - 3^{-a/2})` bounded as the disorder tends to zero. -/
theorem mul_exp_neg_le_one_sub_exp_neg (x : ℝ) :
    x * Real.exp (-x) ≤ 1 - Real.exp (-x) := by
  have h := Real.add_one_le_exp x
  have hpos : 0 < Real.exp (-x) := Real.exp_pos _
  have hmul : (x + 1) * Real.exp (-x) ≤ Real.exp x * Real.exp (-x) :=
    mul_le_mul_of_nonneg_right h hpos.le
  have hone : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hone] at hmul
  nlinarith [hmul]

/-- The restricted volume of a ball, bounded by the ball's own volume. -/
theorem restrict_measure_ball_le
    {d : ℕ} (S : Set (SpatialCoordinates d)) (u : SpatialCoordinates d)
    {s : ℝ} (hs : 0 < s) :
    (volume.restrict S) {v : SpatialCoordinates d | dist u v < s} ≤
      ENNReal.ofReal ((2 * s) ^ d) := by
  have hset : {v : SpatialCoordinates d | dist u v < s} = Metric.ball u s := by
    ext v
    simp [Metric.mem_ball, dist_comm]
  rw [hset]
  refine le_trans (Measure.restrict_apply_le _ _) ?_
  rw [volume_ball_spatial u hs]

/-- The restricted volume of any set, bounded by the total mass. -/
theorem restrict_measure_le_total
    {d : ℕ} (S A : Set (SpatialCoordinates d)) :
    (volume.restrict S) A ≤ volume S := by
  refine le_trans (measure_mono (Set.subset_univ A)) ?_
  rw [Measure.restrict_apply_univ]


/-- The layer weight of a pair of points: `∑_j e^{jc}` over the layers `j` at
which the two points are NOT separated beyond the dependence range
`√d·3^{-j}`.  Paper D:55-57 counts exactly these layers.  If the two points
coincide the sum is over all `j` and the value is `∞`, which is why no
null-set argument about the diagonal is needed anywhere below. -/
def layerWeight (d : ℕ) (c : ℝ) (u v : SpatialCoordinates d) : ℝ≥0∞ :=
  ∑' j : ℕ, if dist u v ≤ Real.sqrt (d : ℝ) * (3 : ℝ) ^ (-(j : ℤ))
    then ENNReal.ofReal (Real.exp ((j : ℝ) * c)) else 0

theorem measurable_layerWeight_uncurry (d : ℕ) (c : ℝ) :
    Measurable (fun q : SpatialCoordinates d × SpatialCoordinates d =>
      layerWeight d c q.1 q.2) := by
  unfold layerWeight
  refine Measurable.tsum ?_
  intro j
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_le (by fun_prop) measurable_const


/-- Paper D:55-57, the counting step: the layers below the least separation
index all carry a close pair, so the partial geometric sum is dominated by the
sum of the pair layer weights. -/
theorem sum_range_exp_le_sum_layerWeight
    {d p : ℕ} (c : ℝ) (y : Fin p → SpatialCoordinates d) (m : ℕ)
    (hwit : ∀ j < m, ∃ q ∈ (Finset.univ.filter
        (fun q : Fin p × Fin p => q.1 ≠ q.2)),
      dist (y q.1) (y q.2) ≤ Real.sqrt (d : ℝ) * (3 : ℝ) ^ (-(j : ℤ))) :
    (∑ j ∈ Finset.range m, ENNReal.ofReal (Real.exp ((j : ℝ) * c))) ≤
      ∑ q ∈ (Finset.univ.filter (fun q : Fin p × Fin p => q.1 ≠ q.2)),
        layerWeight d c (y q.1) (y q.2) := by
  classical
  set T : Finset (Fin p × Fin p) :=
    Finset.univ.filter (fun q : Fin p × Fin p => q.1 ≠ q.2) with hT
  have hstep : ∀ j ∈ Finset.range m,
      ENNReal.ofReal (Real.exp ((j : ℝ) * c)) ≤
        ∑ q ∈ T, (if dist (y q.1) (y q.2) ≤
            Real.sqrt (d : ℝ) * (3 : ℝ) ^ (-(j : ℤ))
          then ENNReal.ofReal (Real.exp ((j : ℝ) * c)) else 0) := by
    intro j hj
    obtain ⟨q, hqT, hq⟩ := hwit j (Finset.mem_range.mp hj)
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun q : Fin p × Fin p => if dist (y q.1) (y q.2) ≤
          Real.sqrt (d : ℝ) * (3 : ℝ) ^ (-(j : ℤ))
        then ENNReal.ofReal (Real.exp ((j : ℝ) * c)) else 0)
      (fun _ _ => bot_le) hqT)
    show _ ≤ if dist (y q.1) (y q.2) ≤
        Real.sqrt (d : ℝ) * (3 : ℝ) ^ (-(j : ℤ))
      then ENNReal.ofReal (Real.exp ((j : ℝ) * c)) else 0
    rw [ite_eq_left hq]
  calc (∑ j ∈ Finset.range m, ENNReal.ofReal (Real.exp ((j : ℝ) * c)))
      ≤ ∑ j ∈ Finset.range m, ∑ q ∈ T,
          (if dist (y q.1) (y q.2) ≤
              Real.sqrt (d : ℝ) * (3 : ℝ) ^ (-(j : ℤ))
            then ENNReal.ofReal (Real.exp ((j : ℝ) * c)) else 0) :=
        Finset.sum_le_sum hstep
    _ = ∑ q ∈ T, ∑ j ∈ Finset.range m,
          (if dist (y q.1) (y q.2) ≤
              Real.sqrt (d : ℝ) * (3 : ℝ) ^ (-(j : ℤ))
            then ENNReal.ofReal (Real.exp ((j : ℝ) * c)) else 0) := Finset.sum_comm
    _ ≤ ∑ q ∈ T, layerWeight d c (y q.1) (y q.2) := by
        refine Finset.sum_le_sum ?_
        intro q _
        exact ENNReal.sum_le_tsum _


/-- The per-layer rate `c = (log 2 / 2) p² δ²` of paper D:53-54. -/
def chaosLayerRate {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (p : ℕ) : ℝ :=
  Real.log 2 / 2 * (p : ℝ) ^ 2 * M.delta ^ 2

theorem chaosLayerRate_pos {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (p : ℕ) (hp : 1 ≤ p) : 0 < chaosLayerRate M p := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  unfold chaosLayerRate
  positivity

/-- Paper D:36-60, pointwise in the configuration: the `p`-point moment is
bounded by `1 + (e^c - 1)` times the sum of the pair layer weights.  Holds for
EVERY configuration: when two points coincide the right-hand side is `∞`. -/
theorem ofReal_integral_prod_le_layerWeight
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (p : ℕ) (hp : 1 ≤ p) (N : ℕ)
    (hpdelta : (p : ℝ) * M.delta ≤ 1)
    (y : Fin p → SpatialCoordinates d) :
    ENNReal.ofReal (∫ omega, ∏ k, fineDensity M N omega (y k)
        ∂(chaosSampleLaw M).toMeasure) ≤
      1 + ENNReal.ofReal (Real.exp (chaosLayerRate M p) - 1) *
        ∑ q ∈ (Finset.univ.filter (fun q : Fin p × Fin p => q.1 ≠ q.2)),
          layerWeight d (chaosLayerRate M p) (y q.1) (y q.2) := by
  classical
  set c : ℝ := chaosLayerRate M p with hcdef
  have hcpos : 0 < c := chaosLayerRate_pos M p hp
  set T : Finset (Fin p × Fin p) :=
    Finset.univ.filter (fun q : Fin p × Fin p => q.1 ≠ q.2) with hT
  by_cases hdist : Pairwise (fun i k : Fin p => y i ≠ y k)
  · obtain ⟨j0, hj0⟩ := exists_dist_separation_index y hdist
    have hex : ∃ j : ℕ, Pairwise (fun i k : Fin p =>
        Real.sqrt (d : ℝ) * (3 : ℝ) ^ (-(j : ℤ)) < dist (y i) (y k)) := ⟨j0, hj0⟩
    have hm : Pairwise (fun i k : Fin p =>
        Real.sqrt (d : ℝ) * (3 : ℝ) ^ (-((Nat.find hex : ℕ) : ℤ)) <
          dist (y i) (y k)) := Nat.find_spec hex
    have hwit : ∀ j < Nat.find hex, ∃ q ∈ T,
        dist (y q.1) (y q.2) ≤ Real.sqrt (d : ℝ) * (3 : ℝ) ^ (-(j : ℤ)) := by
      intro j hj
      have hnot := Nat.find_min hex hj
      rw [Pairwise] at hnot
      push Not at hnot
      obtain ⟨i, k, hik, hle⟩ := hnot
      exact ⟨(i, k), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hik⟩, hle⟩
    have hP1 := sum_range_exp_le_sum_layerWeight c y (Nat.find hex) hwit
    have hint := integral_prod_fineDensity_le_of_dist_separated
      M p hp N (Nat.find hex) y hpdelta hm
    have hid := exp_nat_mul_eq_one_add_geom c (Nat.find hex)
    have hnn : ∀ j ∈ Finset.range (Nat.find hex), (0 : ℝ) ≤ Real.exp ((j : ℝ) * c) :=
      fun j _ => (Real.exp_pos _).le
    have hsumnn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (Nat.find hex), Real.exp ((j : ℝ) * c) :=
      Finset.sum_nonneg hnn
    have hexpnn : (0 : ℝ) ≤ Real.exp c - 1 := by
      have := Real.one_le_exp hcpos.le
      linarith
    calc ENNReal.ofReal (∫ omega, ∏ k, fineDensity M N omega (y k)
            ∂(chaosSampleLaw M).toMeasure)
        ≤ ENNReal.ofReal (Real.exp ((Nat.find hex : ℝ) * c)) :=
          ENNReal.ofReal_le_ofReal hint
      _ = ENNReal.ofReal (1 + (Real.exp c - 1) *
            ∑ j ∈ Finset.range (Nat.find hex), Real.exp ((j : ℝ) * c)) := by rw [hid]
      _ = 1 + ENNReal.ofReal (Real.exp c - 1) *
            ENNReal.ofReal (∑ j ∈ Finset.range (Nat.find hex),
              Real.exp ((j : ℝ) * c)) := by
          rw [ENNReal.ofReal_add (by norm_num) (mul_nonneg hexpnn hsumnn),
            ENNReal.ofReal_mul hexpnn, ENNReal.ofReal_one]
      _ ≤ 1 + ENNReal.ofReal (Real.exp c - 1) *
            ∑ q ∈ T, layerWeight d c (y q.1) (y q.2) := by
          gcongr
          rw [ENNReal.ofReal_sum_of_nonneg hnn]
          exact hP1
  · rw [Pairwise] at hdist
    push Not at hdist
    obtain ⟨i, k, hik, heq⟩ := hdist
    have hinf : layerWeight d c (y i) (y k) = ⊤ := by
      unfold layerWeight
      have hterm : ∀ j : ℕ, (if dist (y i) (y k) ≤
          Real.sqrt (d : ℝ) * (3 : ℝ) ^ (-(j : ℤ))
        then ENNReal.ofReal (Real.exp ((j : ℝ) * c)) else 0) =
          ENNReal.ofReal (Real.exp ((j : ℝ) * c)) := by
        intro j
        rw [ite_eq_left]
        rw [heq, dist_self]
        positivity
      simp_rw [hterm]
      refine top_le_iff.mp ?_
      calc (⊤ : ℝ≥0∞) = ∑' _ : ℕ, (1 : ℝ≥0∞) :=
            (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
        _ ≤ ∑' j : ℕ, ENNReal.ofReal (Real.exp ((j : ℝ) * c)) := by
            refine ENNReal.tsum_le_tsum fun j => ?_
            rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
            exact ENNReal.ofReal_le_ofReal
              (Real.one_le_exp (by positivity))
    have hmem : ((i, k) : Fin p × Fin p) ∈ T :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hik⟩
    have hsumtop : (∑ q ∈ T, layerWeight d c (y q.1) (y q.2)) = ⊤ := by
      refine top_le_iff.mp ?_
      calc (⊤ : ℝ≥0∞) = layerWeight d c (y i) (y k) := hinf.symm
        _ ≤ ∑ q ∈ T, layerWeight d c (y q.1) (y q.2) :=
            Finset.single_le_sum (f := fun q : Fin p × Fin p =>
              layerWeight d c (y q.1) (y q.2)) (fun _ _ => bot_le) hmem
    rw [hsumtop]
    have hne : ENNReal.ofReal (Real.exp c - 1) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      have := Real.add_one_le_exp c
      nlinarith [Real.exp_pos c]
    rw [ENNReal.mul_top hne]
    simp


/-- The `ℝ≥0∞` form of the geometric-mean bound. -/
theorem enn_le_rpow_mul_rpow (m A B : ℝ≥0∞) (theta : ℝ)
    (hmtop : m ≠ ⊤) (hA : m ≤ A) (hB : m ≤ B)
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    m ≤ A ^ (1 - theta) * B ^ theta := by
  rcases eq_or_ne m 0 with hm0 | hm0
  · rw [hm0]; exact bot_le
  · have he : (1 - theta) + theta = 1 := by ring
    have hsplit : m ^ (1 - theta) * m ^ theta = m := by
      rw [← ENNReal.rpow_add _ _ hm0 hmtop, he, ENNReal.rpow_one]
    rw [← hsplit]
    exact mul_le_mul' (ENNReal.rpow_le_rpow hA (by linarith))
      (ENNReal.rpow_le_rpow hB h0)

/-- The restricted volume of a closed ball, via the open ball of twice the
radius. -/
theorem restrict_measure_closedBall_le
    {d : ℕ} (S : Set (SpatialCoordinates d)) (u : SpatialCoordinates d)
    {s : ℝ} (hs : 0 < s) :
    (volume.restrict S) {v : SpatialCoordinates d | dist u v ≤ s} ≤
      ENNReal.ofReal ((4 * s) ^ d) := by
  have hsub : {v : SpatialCoordinates d | dist u v ≤ s} ⊆
      {v : SpatialCoordinates d | dist u v < 2 * s} := by
    intro v hv
    have : dist u v ≤ s := hv
    simp only [Set.mem_ofPred_eq]
    linarith
  refine le_trans (measure_mono hsub) ?_
  have h2s : (0 : ℝ) < 2 * s := by linarith
  have := restrict_measure_ball_le S u h2s
  calc (volume.restrict S) {v : SpatialCoordinates d | dist u v < 2 * s}
      ≤ ENNReal.ofReal ((2 * (2 * s)) ^ d) := this
    _ = ENNReal.ofReal ((4 * s) ^ d) := by ring_nf

/-- Paper D:57-60: the inner integral of the layer weight, bounded term by term
by the geometric mean of the two available bounds on the restricted volume of a
ball.  This is the step that replaces the paper's case split at the scale
`3^{-j} ≈ r` by a single geometric series. -/
theorem lintegral_layerWeight_le
    {d : ℕ} (hd : 0 < d) (S : Set (SpatialCoordinates d)) (c : ℝ)
    (r : ℝ) (_hr : 0 < r) (hS : volume S ≤ ENNReal.ofReal (r ^ d))
    (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (u : SpatialCoordinates d) :
    (∫⁻ v, layerWeight d c u v ∂(volume.restrict S)) ≤
      ∑' j : ℕ, ENNReal.ofReal (Real.exp ((j : ℝ) * c)) *
        (ENNReal.ofReal (r ^ d) ^ (1 - theta) *
          ENNReal.ofReal ((4 * (Real.sqrt (d : ℝ) * (3 : ℝ) ^ (-(j : ℤ)))) ^ d) ^ theta) := by
  classical
  have hsqrt : (0 : ℝ) < Real.sqrt (d : ℝ) := by
    refine Real.sqrt_pos.mpr ?_
    exact_mod_cast hd
  unfold layerWeight
  rw [lintegral_tsum]
  · refine ENNReal.tsum_le_tsum fun j => ?_
    have hthree : (0 : ℝ) < (3 : ℝ) ^ (-(j : ℤ)) := by positivity
    have hsj : (0 : ℝ) < Real.sqrt (d : ℝ) * (3 : ℝ) ^ (-(j : ℤ)) :=
      mul_pos hsqrt hthree
    have hmeasset : MeasurableSet {v : SpatialCoordinates d |
        dist u v ≤ Real.sqrt (d : ℝ) * (3 : ℝ) ^ (-(j : ℤ))} :=
      measurableSet_le (by fun_prop) measurable_const
    have hind : (∫⁻ v, (if dist u v ≤
          Real.sqrt (d : ℝ) * (3 : ℝ) ^ (-(j : ℤ))
        then ENNReal.ofReal (Real.exp ((j : ℝ) * c)) else 0) ∂(volume.restrict S)) =
        ENNReal.ofReal (Real.exp ((j : ℝ) * c)) *
          (volume.restrict S) {v : SpatialCoordinates d |
            dist u v ≤ Real.sqrt (d : ℝ) * (3 : ℝ) ^ (-(j : ℤ))} := by
      rw [← lintegral_indicator_const hmeasset]
      congr 1
    rw [hind]
    refine mul_le_mul_right ?_ _
    refine enn_le_rpow_mul_rpow _ _ _ theta ?_ ?_ ?_ h0 h1
    · exact ne_of_lt (lt_of_le_of_lt (restrict_measure_le_total S _)
        (lt_of_le_of_lt hS ENNReal.ofReal_lt_top))
    · exact le_trans (restrict_measure_le_total S _) hS
    · exact restrict_measure_closedBall_le S u hsj
  · intro j
    refine (Measurable.ite ?_ measurable_const measurable_const).aemeasurable
    exact measurableSet_le (by fun_prop) measurable_const


/-- The geometric sum of a constant multiple, in `ℝ≥0∞`: no side condition is
needed because `ENNReal.tsum_geometric` has none. -/
theorem tsum_const_mul_geom (Kc rho : ℝ≥0∞) :
    (∑' j : ℕ, Kc * rho ^ j) = Kc * (1 - rho)⁻¹ := by
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

/-- Paper D:57-60, the per-layer factorization: the `j`-th term of the bound
produced by `lintegral_layerWeight_le` is a constant times the `j`-th power of
the ratio `e^c · 3^{-d·theta}`. -/
theorem layer_term_factor (d : ℕ) (r c theta : ℝ) (h0 : 0 ≤ theta) (j : ℕ) :
    ENNReal.ofReal (Real.exp ((j : ℝ) * c)) *
        (ENNReal.ofReal (r ^ d) ^ (1 - theta) *
          ENNReal.ofReal ((4 * (Real.sqrt (d : ℝ) * (3 : ℝ) ^ (-(j : ℤ)))) ^ d) ^ theta) =
      (ENNReal.ofReal (r ^ d) ^ (1 - theta) *
          ENNReal.ofReal ((4 * Real.sqrt (d : ℝ)) ^ d) ^ theta) *
        (ENNReal.ofReal (Real.exp c) *
          ENNReal.ofReal (((3 : ℝ) ^ (-(d : ℤ))) ^ theta)) ^ j := by
  have hzp : (0 : ℝ) < (3 : ℝ) ^ (-(d : ℤ)) := by positivity
  have hbase : (4 * (Real.sqrt (d : ℝ) * (3 : ℝ) ^ (-(j : ℤ)))) ^ d =
      (4 * Real.sqrt (d : ℝ)) ^ d * (((3 : ℝ) ^ (-(d : ℤ))) ^ j) := by
    rw [← mul_assoc, mul_pow]
    congr 1
    rw [← zpow_natCast ((3 : ℝ) ^ (-(j : ℤ))) d,
      ← zpow_natCast ((3 : ℝ) ^ (-(d : ℤ))) j, ← zpow_mul, ← zpow_mul]
    ring_nf
  have hnn1 : (0 : ℝ) ≤ (4 * Real.sqrt (d : ℝ)) ^ d := by positivity
  have e1 : ENNReal.ofReal (Real.exp ((j : ℝ) * c)) =
      ENNReal.ofReal (Real.exp c) ^ j := by
    rw [Real.exp_nat_mul, ENNReal.ofReal_pow (Real.exp_pos c).le]
  have e2 : ENNReal.ofReal (((3 : ℝ) ^ (-(d : ℤ))) ^ j) ^ theta =
      ENNReal.ofReal (((3 : ℝ) ^ (-(d : ℤ))) ^ theta) ^ j := by
    rw [ENNReal.ofReal_pow hzp.le, ← ENNReal.ofReal_rpow_of_pos hzp,
      ← ENNReal.rpow_natCast (ENNReal.ofReal ((3 : ℝ) ^ (-(d : ℤ)))) j,
      ← ENNReal.rpow_natCast
        ((ENNReal.ofReal ((3 : ℝ) ^ (-(d : ℤ)))) ^ theta) j,
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_comm]
  rw [hbase, ENNReal.ofReal_mul hnn1, ENNReal.mul_rpow_of_nonneg _ _ h0, e1, e2,
    mul_pow]
  ring

/-- Paper D:57-60, the constant: `(e^{a log 3} - 1)/(1 - 3^{-a/2})` stays
bounded as the disorder tends to zero.  This is what makes `Cmass` in eq. (38)
independent of the model. -/
theorem exp_sub_one_div_one_sub_le (a : ℝ) (ha : 0 < a) :
    (Real.exp (a * Real.log 3) - 1) *
        (1 - Real.exp (-(a / 2 * Real.log 3)))⁻¹ ≤
      2 * Real.exp (3 * a / 2 * Real.log 3) := by
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set x : ℝ := a / 2 * Real.log 3 with hx
  have hxpos : 0 < x := by rw [hx]; positivity
  have hnum : Real.exp (2 * x) - 1 ≤ 2 * x * Real.exp (2 * x) := by
    have h := Real.add_one_le_exp (-(2 * x))
    have hpos : 0 < Real.exp (2 * x) := Real.exp_pos _
    have hmul : (-(2 * x) + 1) * Real.exp (2 * x) ≤
        Real.exp (-(2 * x)) * Real.exp (2 * x) :=
      mul_le_mul_of_nonneg_right h hpos.le
    have hone : Real.exp (-(2 * x)) * Real.exp (2 * x) = 1 := by
      rw [← Real.exp_add]; simp
    rw [hone] at hmul; nlinarith [hmul]
  have hden : x * Real.exp (-x) ≤ 1 - Real.exp (-x) :=
    mul_exp_neg_le_one_sub_exp_neg x
  have hdenpos : 0 < 1 - Real.exp (-x) :=
    lt_of_lt_of_le (by positivity) hden
  have h2x : a * Real.log 3 = 2 * x := by rw [hx]; ring
  have h3x : 3 * a / 2 * Real.log 3 = 3 * x := by rw [hx]; ring
  rw [h2x, h3x]
  rw [inv_eq_one_div, mul_one_div, div_le_iff₀ hdenpos]
  have hexp3 : Real.exp (3 * x) = Real.exp (2 * x) * Real.exp x := by
    rw [← Real.exp_add]; ring_nf
  have hinv : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [hnum, hden, Real.exp_pos (2 * x), Real.exp_pos x, Real.exp_pos (-x),
    mul_le_mul_of_nonneg_left hden (le_of_lt (Real.exp_pos (2 * x)))]


/-- Paper D:57-60 in closed form: the inner integral of the layer weight is
bounded by one geometric series, whose ratio is `e^c · 3^{-d·theta}`.  The
bound does not depend on the base point `u`, which is what
`lintegral_pi_two_coords_le` consumes. -/
theorem lintegral_layerWeight_le_geom
    {d : ℕ} (hd : 0 < d) (S : Set (SpatialCoordinates d)) (c : ℝ)
    (r : ℝ) (hr : 0 < r) (hS : volume S ≤ ENNReal.ofReal (r ^ d))
    (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (u : SpatialCoordinates d) :
    (∫⁻ v, layerWeight d c u v ∂(volume.restrict S)) ≤
      (ENNReal.ofReal (r ^ d) ^ (1 - theta) *
          ENNReal.ofReal ((4 * Real.sqrt (d : ℝ)) ^ d) ^ theta) *
        (1 - ENNReal.ofReal (Real.exp c) *
          ENNReal.ofReal (((3 : ℝ) ^ (-(d : ℤ))) ^ theta))⁻¹ := by
  refine (lintegral_layerWeight_le hd S c r hr hS theta h0 h1 u).trans ?_
  refine le_of_eq ?_
  rw [tsum_congr (fun j : ℕ => layer_term_factor d r c theta h0 j),
    tsum_const_mul_geom]

/-- Paper D:57-60: the pair contribution over the `p`-fold cube.  Combines the
product-measure step with the closed-form inner bound. -/
theorem lintegral_pi_layerWeight_le
    {d : ℕ} (hd : 0 < d) (S : Set (SpatialCoordinates d)) (c : ℝ)
    (r : ℝ) (hr : 0 < r) (hS : volume S ≤ ENNReal.ofReal (r ^ d))
    (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (p : ℕ) (i k : Fin p) (hik : i ≠ k) :
    (∫⁻ y : Fin p → SpatialCoordinates d, layerWeight d c (y i) (y k)
        ∂(Measure.pi fun _ : Fin p => volume.restrict S)) ≤
      ((ENNReal.ofReal (r ^ d) ^ (1 - theta) *
          ENNReal.ofReal ((4 * Real.sqrt (d : ℝ)) ^ d) ^ theta) *
        (1 - ENNReal.ofReal (Real.exp c) *
          ENNReal.ofReal (((3 : ℝ) ^ (-(d : ℤ))) ^ theta))⁻¹) *
      (volume S) ^ (p - 1) := by
  have hfin : IsFiniteMeasure (volume.restrict S) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_lt hS ENNReal.ofReal_lt_top
  have huniv : (volume.restrict S) Set.univ = volume S := Measure.restrict_apply_univ S
  have := lintegral_pi_two_coords_le (volume.restrict S) p i k hik
    (layerWeight d c) (measurable_layerWeight_uncurry d c) _
    (fun u => lintegral_layerWeight_le_geom hd S c r hr hS theta h0 h1 u)
  rwa [huniv] at this


/-- Measurability of a pair layer weight as a function of the configuration. -/
theorem measurable_layerWeight_coords {d : ℕ} (c : ℝ) (p : ℕ) (i k : Fin p) :
    Measurable (fun y : Fin p → SpatialCoordinates d =>
      layerWeight d c (y i) (y k)) := by
  have hpair : Measurable (fun y : Fin p → SpatialCoordinates d => (y i, y k)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply k)
  have hcomp := (measurable_layerWeight_uncurry d c).comp hpair
  simpa [Function.comp_def] using hcomp

/-- Paper D:55-60: the sum over pairs, integrated over the `p`-fold cube. -/
theorem lintegral_pi_sum_layerWeight_le
    {d : ℕ} (hd : 0 < d) (S : Set (SpatialCoordinates d)) (c : ℝ)
    (r : ℝ) (hr : 0 < r) (hS : volume S ≤ ENNReal.ofReal (r ^ d))
    (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (p : ℕ) :
    (∫⁻ y : Fin p → SpatialCoordinates d,
        ∑ q ∈ (Finset.univ.filter (fun q : Fin p × Fin p => q.1 ≠ q.2)),
          layerWeight d c (y q.1) (y q.2)
        ∂(Measure.pi fun _ : Fin p => volume.restrict S)) ≤
      (p * p : ℕ) •
        (((ENNReal.ofReal (r ^ d) ^ (1 - theta) *
            ENNReal.ofReal ((4 * Real.sqrt (d : ℝ)) ^ d) ^ theta) *
          (1 - ENNReal.ofReal (Real.exp c) *
            ENNReal.ofReal (((3 : ℝ) ^ (-(d : ℤ))) ^ theta))⁻¹) *
          (volume S) ^ (p - 1)) := by
  classical
  set T : Finset (Fin p × Fin p) :=
    Finset.univ.filter (fun q : Fin p × Fin p => q.1 ≠ q.2) with hT
  set B : ℝ≥0∞ :=
    ((ENNReal.ofReal (r ^ d) ^ (1 - theta) *
        ENNReal.ofReal ((4 * Real.sqrt (d : ℝ)) ^ d) ^ theta) *
      (1 - ENNReal.ofReal (Real.exp c) *
        ENNReal.ofReal (((3 : ℝ) ^ (-(d : ℤ))) ^ theta))⁻¹) *
      (volume S) ^ (p - 1) with hB
  rw [lintegral_finsetSum' T
    (fun q _ => (measurable_layerWeight_coords c p q.1 q.2).aemeasurable)]
  have hterm : ∀ q ∈ T,
      (∫⁻ y : Fin p → SpatialCoordinates d, layerWeight d c (y q.1) (y q.2)
        ∂(Measure.pi fun _ : Fin p => volume.restrict S)) ≤ B := by
    intro q hq
    have hne : q.1 ≠ q.2 := by
      have := Finset.mem_filter.mp hq
      simpa [hT] using this.2
    exact lintegral_pi_layerWeight_le hd S c r hr hS theta h0 h1 p q.1 q.2 hne
  refine (Finset.sum_le_card_nsmul T _ B hterm).trans ?_
  refine nsmul_le_nsmul_left (bot_le) ?_
  calc T.card ≤ (Finset.univ : Finset (Fin p × Fin p)).card :=
        Finset.card_filter_le _ _
    _ = p * p := by simp


/-- The `ℝ≥0∞`-valued form of the `p`-point reduction: any `ℝ≥0∞` bound on the
`p`-point moment integrates to a bound on the `omega`-integral of the `p`-th
power of the cube mass. -/
theorem lintegral_ofReal_chaosCutoff_pow_le'
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (p : ℕ) (hp : 1 ≤ p) (N : ℕ)
    (hpdelta : (p : ℝ) * M.delta ≤ 1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (bound : (Fin p → SpatialCoordinates d) → ℝ≥0∞)
    (hb : ∀ y : Fin p → SpatialCoordinates d,
      ENNReal.ofReal (∫ omega, ∏ k, fineDensity M N omega (y k)
        ∂(chaosSampleLaw M).toMeasure) ≤ bound y) :
    (∫⁻ omega, ENNReal.ofReal (((chaosCutoff M N omega)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p)
      ∂(chaosSampleLaw M).toMeasure) ≤
      ∫⁻ y : Fin p → SpatialCoordinates d, bound y
        ∂(Measure.pi fun _ : Fin p ↦
          volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  have hstep : (∫⁻ omega, ENNReal.ofReal (((chaosCutoff M N omega)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p)
      ∂(chaosSampleLaw M).toMeasure) =
      ∫⁻ y : Fin p → SpatialCoordinates d, ∫⁻ omega,
        ENNReal.ofReal (∏ i, fineDensity M N omega (y i))
        ∂(chaosSampleLaw M).toMeasure
      ∂(Measure.pi fun _ : Fin p ↦
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    rw [← lintegral_lintegral_swap_prod_fineDensity M N z r hr p]
    apply lintegral_congr
    intro omega
    exact ofReal_chaosCutoff_pow_eq_pi_lintegral M N omega z r hr p
  rw [hstep]
  refine lintegral_mono fun y => ?_
  exact le_trans
    (le_of_eq (lintegral_ofReal_prod_fineDensity_eq_ofReal_integral M p hp N y hpdelta))
    (hb y)

/-- Paper D:36-60 assembled in `ℝ≥0∞`: the unweighted chaos moment.  The two
summands are the trivial contribution `|q|^p` and the pair contribution, whose
constant is the closed-form geometric series. -/
theorem lintegral_chaosCutoff_pow_core
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 0 < d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (p : ℕ) (hp : 1 ≤ p) (N : ℕ)
    (hpdelta : (p : ℝ) * M.delta ≤ 1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    (∫⁻ omega, ENNReal.ofReal (((chaosCutoff M N omega)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p)
      ∂(chaosSampleLaw M).toMeasure) ≤
      ENNReal.ofReal (r ^ d) ^ p +
        ENNReal.ofReal (Real.exp (chaosLayerRate M p) - 1) *
          ((p * p : ℕ) •
            (((ENNReal.ofReal (r ^ d) ^ (1 - theta) *
                ENNReal.ofReal ((4 * Real.sqrt (d : ℝ)) ^ d) ^ theta) *
              (1 - ENNReal.ofReal (Real.exp (chaosLayerRate M p)) *
                ENNReal.ofReal (((3 : ℝ) ^ (-(d : ℤ))) ^ theta))⁻¹) *
              ENNReal.ofReal (r ^ d) ^ (p - 1))) := by
  classical
  set Q : Set (SpatialCoordinates d) := (centeredCube z r hr : Set (SpatialCoordinates d))
    with hQdef
  have hvol : volume Q = ENNReal.ofReal (r ^ d) := by
    rw [hQdef, centeredCube_volume]
  have hS : volume Q ≤ ENNReal.ofReal (r ^ d) := le_of_eq hvol
  set c : ℝ := chaosLayerRate M p with hc
  set T : Finset (Fin p × Fin p) :=
    Finset.univ.filter (fun q : Fin p × Fin p => q.1 ≠ q.2) with hT
  refine (lintegral_ofReal_chaosCutoff_pow_le' M p hp N hpdelta z r hr
    (fun y => 1 + ENNReal.ofReal (Real.exp c - 1) *
      ∑ q ∈ T, layerWeight d c (y q.1) (y q.2))
    (fun y => ofReal_integral_prod_le_layerWeight M p hp N hpdelta y)).trans ?_
  rw [lintegral_add_left measurable_const]
  have hone : (∫⁻ _y : Fin p → SpatialCoordinates d, (1 : ℝ≥0∞)
      ∂(Measure.pi fun _ : Fin p => volume.restrict Q)) =
      ENNReal.ofReal (r ^ d) ^ p := by
    rw [lintegral_one, Measure.pi_univ]
    simp [hvol]
  have hmul : (∫⁻ y : Fin p → SpatialCoordinates d,
      ENNReal.ofReal (Real.exp c - 1) * ∑ q ∈ T, layerWeight d c (y q.1) (y q.2)
      ∂(Measure.pi fun _ : Fin p => volume.restrict Q)) =
      ENNReal.ofReal (Real.exp c - 1) *
        ∫⁻ y : Fin p → SpatialCoordinates d,
          ∑ q ∈ T, layerWeight d c (y q.1) (y q.2)
          ∂(Measure.pi fun _ : Fin p => volume.restrict Q) :=
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  rw [hone, hmul]
  have hsum := lintegral_pi_sum_layerWeight_le hd Q c r hr hS theta h0 h1 p
  rw [hvol] at hsum
  gcongr


/-- `r ^ s` decreases in the exponent when `0 < r ≤ 1`. -/
theorem ofReal_rpow_le_of_le_one (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    {s t : ℝ} (hst : t ≤ s) :
    ENNReal.ofReal (r ^ s) ≤ ENNReal.ofReal (r ^ t) :=
  ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hr hr1 hst)

/-- `ofReal (r ^ (n : ℕ))` as an `rpow`. -/
theorem ofReal_pow_eq_rpow (r : ℝ) (_hr : 0 < r) (n : ℕ) :
    ENNReal.ofReal (r ^ n) = ENNReal.ofReal (r ^ (n : ℝ)) := by
  rw [Real.rpow_natCast]

/-- Paper D:60-63: the core bound in the frozen shape `Cmass · r^(d p - 2a)`,
for the UNWEIGHTED chaos.  The exponent loss is `2a` with
`a = chaosLayerRate M p / log 3`, i.e. `Cexponent = (log 2 / log 3) p²`; the
constant depends only on `d` and `p`. -/
theorem lintegral_chaosCutoff_pow_le_rpow
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 0 < d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (p : ℕ) (hp : 1 ≤ p) (N : ℕ)
    (hpdelta : (p : ℝ) * M.delta ≤ 1)
    (ha : chaosLayerRate M p / Real.log 3 ≤ (d : ℝ) / 4)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    (∫⁻ omega, ENNReal.ofReal (((chaosCutoff M N omega)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p)
      ∂(chaosSampleLaw M).toMeasure) ≤
      ENNReal.ofReal
        ((1 + (p : ℝ) ^ 2 * (4 * Real.sqrt (d : ℝ)) ^ d * (2 * (3 : ℝ) ^ d)) *
          r ^ ((d : ℝ) * p -
            2 * (chaosLayerRate M p / Real.log 3))) := by
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  set c : ℝ := chaosLayerRate M p with hc
  have hcpos : 0 < c := chaosLayerRate_pos M p hp
  set a : ℝ := c / Real.log 3 with hadef
  have hapos : 0 < a := by rw [hadef]; positivity
  have hca : c = a * Real.log 3 := by
    rw [hadef]; field_simp
  set theta : ℝ := 3 * a / (2 * (d : ℝ)) with hth
  have h0 : 0 ≤ theta := by rw [hth]; positivity
  have hdtheta : (d : ℝ) * theta = 3 * a / 2 := by
    rw [hth]; field_simp
  have h1 : theta ≤ 1 := by
    rw [hth, div_le_one (by positivity)]
    nlinarith [ha, hdR]
  have h32 : 3 * a / 2 ≤ (d : ℝ) := by nlinarith [ha, hdR]
  have hcore := lintegral_chaosCutoff_pow_core hd M p hp N hpdelta z r hr theta h0 h1
  refine hcore.trans ?_
  -- the geometric factor
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have hzr : ((3 : ℝ) ^ (-(d : ℤ))) = (3 : ℝ) ^ (-(d : ℝ)) := by
    rw [← Real.rpow_intCast]
    norm_num
  have hexpc : Real.exp c = (3 : ℝ) ^ a := by
    rw [Real.rpow_def_of_pos h3pos, hca, mul_comm]
  have hx : ENNReal.ofReal (Real.exp c) *
      ENNReal.ofReal (((3 : ℝ) ^ (-(d : ℤ))) ^ theta) =
      ENNReal.ofReal ((3 : ℝ) ^ (-(a / 2))) := by
    rw [hzr, ← Real.rpow_mul h3pos.le, hexpc,
      ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add h3pos]
    have hexp : a + -(d : ℝ) * theta = -(a / 2) := by
      rw [neg_mul, hdtheta]; ring
    rw [hexp]
  have hEpos : (0 : ℝ) < (3 : ℝ) ^ (-(a / 2)) := by positivity
  have hElt : (3 : ℝ) ^ (-(a / 2)) < 1 := by
    have h0' : (3 : ℝ) ^ (0 : ℝ) = 1 := by simp
    rw [← h0']
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have hone_sub : (1 : ℝ≥0∞) - ENNReal.ofReal ((3 : ℝ) ^ (-(a / 2))) =
      ENNReal.ofReal (1 - (3 : ℝ) ^ (-(a / 2))) := by
    rw [ENNReal.ofReal_sub _ hEpos.le, ENNReal.ofReal_one]
  have hEexp : (3 : ℝ) ^ (-(a / 2)) = Real.exp (-(a / 2 * Real.log 3)) := by
    rw [Real.rpow_def_of_pos h3pos]
    congr 1
    ring
  have hgeom : ENNReal.ofReal (Real.exp c - 1) *
      ((1 : ℝ≥0∞) - ENNReal.ofReal ((3 : ℝ) ^ (-(a / 2))))⁻¹ ≤
      ENNReal.ofReal (2 * (3 : ℝ) ^ d) := by
    have hcnn : 0 ≤ Real.exp c - 1 := by
      have := Real.one_le_exp hcpos.le; linarith
    rw [hone_sub, ← ENNReal.ofReal_inv_of_pos (by linarith),
      ← ENNReal.ofReal_mul hcnn]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := exp_sub_one_div_one_sub_le a hapos
    rw [← hca, ← hEexp] at h
    refine h.trans ?_
    have h32' : Real.exp (3 * a / 2 * Real.log 3) = (3 : ℝ) ^ (3 * a / 2) := by
      rw [Real.rpow_def_of_pos h3pos]; congr 1; ring
    rw [h32']
    have hmono : (3 : ℝ) ^ (3 * a / 2) ≤ (3 : ℝ) ^ ((d : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) h32
    have hnat : (3 : ℝ) ^ ((d : ℝ)) = (3 : ℝ) ^ d := by
      rw [Real.rpow_natCast]
    rw [hnat] at hmono
    nlinarith [hmono]
  have hBth : ENNReal.ofReal ((4 * Real.sqrt (d : ℝ)) ^ d) ^ theta ≤
      ENNReal.ofReal ((4 * Real.sqrt (d : ℝ)) ^ d) := by
    have hge : (1 : ℝ) ≤ (4 * Real.sqrt (d : ℝ)) ^ d := by
      refine one_le_pow₀ ?_
      have : (1 : ℝ) ≤ Real.sqrt (d : ℝ) := by
        rw [show (1:ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hd)
      linarith
    have h1' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((4 * Real.sqrt (d : ℝ)) ^ d) := by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
      exact ENNReal.ofReal_le_ofReal hge
    calc ENNReal.ofReal ((4 * Real.sqrt (d : ℝ)) ^ d) ^ theta
        ≤ ENNReal.ofReal ((4 * Real.sqrt (d : ℝ)) ^ d) ^ (1 : ℝ) :=
          ENNReal.rpow_le_rpow_of_exponent_le h1' h1
      _ = ENNReal.ofReal ((4 * Real.sqrt (d : ℝ)) ^ d) := by
          rw [ENNReal.rpow_one]
  have hrd : (0 : ℝ) < r ^ d := by positivity
  have hArpow : ∀ t : ℝ, ENNReal.ofReal (r ^ d) ^ t =
      ENNReal.ofReal (r ^ ((d : ℝ) * t)) := by
    intro t
    rw [ENNReal.ofReal_rpow_of_pos hrd, ← Real.rpow_natCast r d,
      ← Real.rpow_mul hr.le]
  have e_p : (r ^ d) ^ p = r ^ ((d : ℝ) * (p : ℝ)) := by
    rw [← pow_mul, ← Real.rpow_natCast r (d * p)]
    push_cast
    ring_nf
  have e_pm1 : (r ^ d) ^ (p - 1) = r ^ ((d : ℝ) * ((p : ℝ) - 1)) := by
    rw [← pow_mul, ← Real.rpow_natCast r (d * (p - 1))]
    push_cast [Nat.cast_sub hp]
    ring_nf
  have hppow : ENNReal.ofReal (r ^ d) ^ p =
      ENNReal.ofReal (r ^ ((d : ℝ) * (p : ℝ))) := by
    rw [← ENNReal.ofReal_pow hrd.le, e_p]
  have hpm1 : ENNReal.ofReal (r ^ d) ^ (p - 1) =
      ENNReal.ofReal (r ^ ((d : ℝ) * ((p : ℝ) - 1))) := by
    rw [← ENNReal.ofReal_pow hrd.le, e_pm1]
  set E : ℝ := (d : ℝ) * (p : ℝ) - 2 * a with hE
  have hterm1 : ENNReal.ofReal (r ^ d) ^ p ≤ ENNReal.ofReal (r ^ E) := by
    rw [hppow]
    exact ofReal_rpow_le_of_le_one r hr hr1 (by rw [hE]; linarith)
  have hprod : ENNReal.ofReal (r ^ ((d : ℝ) * (1 - theta))) *
      ENNReal.ofReal (r ^ ((d : ℝ) * ((p : ℝ) - 1))) ≤ ENNReal.ofReal (r ^ E) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hr]
    refine ofReal_rpow_le_of_le_one r hr hr1 ?_
    have : (d : ℝ) * (1 - theta) + (d : ℝ) * ((p : ℝ) - 1) =
        (d : ℝ) * (p : ℝ) - 3 * a / 2 := by
      have := hdtheta; nlinarith [hdtheta]
    rw [this, hE]
    linarith
  have hcard : ((p * p : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((p : ℝ) ^ 2) := by
    rw [← ENNReal.ofReal_natCast]
    congr 1
    push_cast
    ring
  rw [← hc, hx, nsmul_eq_mul, hcard, hArpow (1 - theta), hpm1]
  calc ENNReal.ofReal (r ^ d) ^ p +
        ENNReal.ofReal (Real.exp c - 1) *
          (ENNReal.ofReal ((p : ℝ) ^ 2) *
            (ENNReal.ofReal (r ^ ((d : ℝ) * (1 - theta))) *
                ENNReal.ofReal ((4 * Real.sqrt (d : ℝ)) ^ d) ^ theta *
                (1 - ENNReal.ofReal ((3 : ℝ) ^ (-(a / 2))))⁻¹ *
              ENNReal.ofReal (r ^ ((d : ℝ) * ((p : ℝ) - 1)))))
      ≤ ENNReal.ofReal (r ^ E) +
        ENNReal.ofReal ((p : ℝ) ^ 2) * ENNReal.ofReal ((4 * Real.sqrt (d : ℝ)) ^ d) *
          ENNReal.ofReal (2 * (3 : ℝ) ^ d) * ENNReal.ofReal (r ^ E) := by
        refine add_le_add hterm1 ?_
        calc ENNReal.ofReal (Real.exp c - 1) *
              (ENNReal.ofReal ((p : ℝ) ^ 2) *
                (ENNReal.ofReal (r ^ ((d : ℝ) * (1 - theta))) *
                    ENNReal.ofReal ((4 * Real.sqrt (d : ℝ)) ^ d) ^ theta *
                    (1 - ENNReal.ofReal ((3 : ℝ) ^ (-(a / 2))))⁻¹ *
                  ENNReal.ofReal (r ^ ((d : ℝ) * ((p : ℝ) - 1)))))
            = ENNReal.ofReal ((p : ℝ) ^ 2) *
                (ENNReal.ofReal ((4 * Real.sqrt (d : ℝ)) ^ d) ^ theta *
                  (ENNReal.ofReal (Real.exp c - 1) *
                    (1 - ENNReal.ofReal ((3 : ℝ) ^ (-(a / 2))))⁻¹) *
                  (ENNReal.ofReal (r ^ ((d : ℝ) * (1 - theta))) *
                    ENNReal.ofReal (r ^ ((d : ℝ) * ((p : ℝ) - 1))))) := by ring
          _ ≤ ENNReal.ofReal ((p : ℝ) ^ 2) *
                (ENNReal.ofReal ((4 * Real.sqrt (d : ℝ)) ^ d) *
                  ENNReal.ofReal (2 * (3 : ℝ) ^ d) * ENNReal.ofReal (r ^ E)) := by
              gcongr
          _ = ENNReal.ofReal ((p : ℝ) ^ 2) *
                ENNReal.ofReal ((4 * Real.sqrt (d : ℝ)) ^ d) *
                ENNReal.ofReal (2 * (3 : ℝ) ^ d) * ENNReal.ofReal (r ^ E) := by ring
    _ = ENNReal.ofReal ((1 + (p : ℝ) ^ 2 * (4 * Real.sqrt (d : ℝ)) ^ d *
            (2 * (3 : ℝ) ^ d)) * r ^ E) := by
        rw [add_mul, one_mul, ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (p : ℝ) ^ 2),
          ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ (2:ℝ))]


/-- `g ↦ exp (lambda ‖g|_K‖)` is measurable on `C(R^d, R)`: restriction to a set
is continuous for the compact-open topology, and so are the norm and `exp`. -/
theorem measurable_exp_norm_restrict {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (K : TopologicalSpace.Compacts (SpatialCoordinates d)) (lambda : ℝ) :
    Measurable (fun g : C(SpatialCoordinates d, ℝ) =>
      Real.exp (lambda * ‖g.restrict (K : Set (SpatialCoordinates d))‖)) := by
  refine (Real.continuous_exp.comp ?_).measurable
  exact continuous_const.mul
    (continuous_norm.comp (ContinuousMap.continuous_restrict _))

/-- Measurability of the cube masses at a fixed cutoff. -/
theorem measurable_chaosCutoff_pow
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (p : ℕ) :
    Measurable (fun omega : BilateralField d =>
      ((chaosCutoff M N omega)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p) := by
  have hadp := (chaosCutoff_centeredCube_martingale_nonnegative M z r hr).1.1 N
  exact ((hadp.mono
    ((conditionalFineFiltration (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
      measurable_const).le N)).measurable).pow_const p

theorem measurable_weightedChaosCutoff_pow
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (N : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (p : ℕ) :
    Measurable (fun omega : BilateralField d =>
      ((weightedChaosCutoff M H N omega)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p) := by
  have hadp := weightedChaosCutoff_centeredCube_adapted M H hH z r hr N
  exact (hadp.mono ((conditionalFineFiltration H hH).le N) le_rfl).pow_const p


/-- Paper D:36-64, eq. (38) for one cube: the weighted chaos moment, with the
weight removed by the exact independence factorization. -/
theorem weighted_moment_bound
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd2 : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (p : ℕ) (hp : 1 ≤ p) (N : ℕ) (hpdelta : (p : ℝ) * M.delta ≤ 1)
    (ha : chaosLayerRate M p / Real.log 3 ≤ (d : ℝ) / 4)
    (K : TopologicalSpace.Compacts (SpatialCoordinates d))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hQK : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      (K : Set (SpatialCoordinates d))) :
    Measurable (fun omega : BilateralField d =>
      ((weightedChaosCutoff M H N omega)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p) ∧
    Integrable (fun omega : BilateralField d =>
      ((weightedChaosCutoff M H N omega)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p)
      (chaosSampleLaw M).toMeasure ∧
    (∫ omega, ((weightedChaosCutoff M H N omega)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p
      ∂(chaosSampleLaw M).toMeasure) ≤
      (∫ omega, Real.exp ((p : ℝ) *
          ‖(H omega).restrict (K : Set (SpatialCoordinates d))‖)
        ∂(chaosSampleLaw M).toMeasure) *
        ((1 + (p : ℝ) ^ 2 * (4 * Real.sqrt (d : ℝ)) ^ d * (2 * (3 : ℝ) ^ d)) *
          r ^ ((d : ℝ) * p -
            2 * (chaosLayerRate M p / Real.log 3))) := by
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd2
  set Cm : ℝ :=
    1 + (p : ℝ) ^ 2 * (4 * Real.sqrt (d : ℝ)) ^ d * (2 * (3 : ℝ) ^ d) with hCm
  set E : ℝ := (d : ℝ) * p - 2 * (chaosLayerRate M p / Real.log 3) with hE
  set Phi : C(SpatialCoordinates d, ℝ) → ℝ :=
    fun g => Real.exp ((p : ℝ) * ‖g.restrict (K : Set (SpatialCoordinates d))‖)
    with hPhidef
  have hPhimeasC : Measurable Phi := measurable_exp_norm_restrict K (p : ℝ)
  have hlin := lintegral_chaosCutoff_pow_le_rpow hd0 M p hp N hpdelta ha z r hr hr1
  have hCmr : 0 ≤ Cm * r ^ E := by
    rw [hCm]; positivity
  obtain ⟨hMint, hMbound⟩ :=
    integrable_and_integral_le_of_lintegral_ofReal_le (chaosSampleLaw M).toMeasure
      (fun omega => ((chaosCutoff M N omega)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p)
      (measurable_chaosCutoff_pow M N z r hr p)
      (fun w => by positivity) (Cm * r ^ E) hCmr hlin
  have hPhiInt : Integrable (fun omega : BilateralField d => Phi (H omega))
      (chaosSampleLaw M).toMeasure :=
    exists_compactExponentialMoment_of_infraredCharacterization hd2 M H hH K
      (p : ℝ) (by positivity)
  have hWmeas := measurable_weightedChaosCutoff_pow M H hH.1 N z r hr p
  have hprod : Integrable (fun omega : BilateralField d => Phi (H omega) *
      ((chaosCutoff M N omega)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p)
      (chaosSampleLaw M).toMeasure :=
    (indepFun_comp_H_chaosCutoff_pow M H hH N z r hr p Phi hPhimeasC).integrable_mul
      hPhiInt hMint
  have hpt : ∀ omega : BilateralField d,
      ((weightedChaosCutoff M H N omega)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p ≤
      Phi (H omega) * ((chaosCutoff M N omega)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p := fun omega =>
    weightedChaosCutoff_pow_le_exp_mul_chaosCutoff_pow M H N omega K z r hr p hQK
  have hWint : Integrable (fun omega : BilateralField d =>
      ((weightedChaosCutoff M H N omega)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p)
      (chaosSampleLaw M).toMeasure := by
    refine hprod.mono' hWmeas.aestronglyMeasurable (ae_of_all _ fun omega => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact hpt omega
  refine ⟨hWmeas, hWint, ?_⟩
  have hPhinn : 0 ≤ ∫ omega, Phi (H omega) ∂(chaosSampleLaw M).toMeasure :=
    integral_nonneg (fun omega => (Real.exp_pos _).le)
  calc (∫ omega, ((weightedChaosCutoff M H N omega)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p
      ∂(chaosSampleLaw M).toMeasure)
      ≤ ∫ omega, Phi (H omega) * ((chaosCutoff M N omega)
          (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p
        ∂(chaosSampleLaw M).toMeasure := integral_mono hWint hprod hpt
    _ = (∫ omega, Phi (H omega) ∂(chaosSampleLaw M).toMeasure) *
        ∫ omega, ((chaosCutoff M N omega)
          (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p
          ∂(chaosSampleLaw M).toMeasure :=
        integral_comp_H_mul_chaosCutoff_pow M H hH N z r hr p Phi hPhimeasC
          hPhiInt hMint
    _ ≤ (∫ omega, Phi (H omega) ∂(chaosSampleLaw M).toMeasure) * (Cm * r ^ E) :=
        mul_le_mul_of_nonneg_left hMbound hPhinn


/-- Block (A) of the frozen `chaos_positive_moments_and_martingales`: paper
`mfd:lem-chaos-moments`, eq. (38).  `Cexponent = (log 2 / log 3) p²` and
`cSmall = min (1/p) (sqrt (d log 3 / (2 log 2 p²)))` are fixed before the
bounded region and before the model, and `Cmass` before the model, exactly as
the frozen binder order demands. -/
theorem chaos_moment_block
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) (p : ℕ) (hp : 1 ≤ p) :
    ∃ Cexponent cSmall : ℝ, 0 < Cexponent ∧ 0 < cSmall ∧
      ∀ (R : Set (SpatialCoordinates d)), Bornology.IsBounded R →
        ∃ Cmass : ℝ, 0 < Cmass ∧
          ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
            (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
            InfraredCharacterization M H → M.delta ≤ cSmall →
            ∀ (N : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
              r ≤ 1 → (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ R →
              Measurable (fun omega ↦
                ((weightedChaosCutoff M H N omega)
                  (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p) ∧
              Integrable (fun omega ↦
                ((weightedChaosCutoff M H N omega)
                  (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p)
                (chaosSampleLaw M).toMeasure ∧
              ∫ omega, ((weightedChaosCutoff M H N omega)
                  (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p
                ∂(chaosSampleLaw M).toMeasure ≤
                Cmass * r ^ ((d : ℝ) * p - Cexponent * M.delta ^ 2) := by
  classical
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  obtain ⟨CK, hCKnn, hCKspec⟩ :=
    exists_uniform_compactExponentialMoment_of_infraredCharacterization
      (d := d) hd
  set Cexponent : ℝ := Real.log 2 / Real.log 3 * (p : ℝ) ^ 2 with hCe
  set cSmall : ℝ :=
    min (1 / (p : ℝ))
      (Real.sqrt ((d : ℝ) * Real.log 3 / (2 * Real.log 2 * (p : ℝ) ^ 2)))
    with hcS
  have hCepos : 0 < Cexponent := by rw [hCe]; positivity
  have hcSpos : 0 < cSmall := by
    rw [hcS]
    refine lt_min (by positivity) ?_
    exact Real.sqrt_pos.mpr (by positivity)
  refine ⟨Cexponent, cSmall, hCepos, hcSpos, ?_⟩
  intro R hR
  obtain ⟨s, hs⟩ := hR.subset_closedBall (0 : SpatialCoordinates d)
  set K : TopologicalSpace.Compacts (SpatialCoordinates d) :=
    ⟨Metric.closedBall (0 : SpatialCoordinates d) s, isCompact_closedBall _ _⟩ with hK
  set Cm : ℝ :=
    1 + (p : ℝ) ^ 2 * (4 * Real.sqrt (d : ℝ)) ^ d * (2 * (3 : ℝ) ^ d) with hCm
  have hCmpos : 0 < Cm := by rw [hCm]; positivity
  refine ⟨2 * Real.exp (CK K * (p : ℝ) ^ 2 * cSmall ^ 2) * Cm, by positivity, ?_⟩
  intro M H hH hdelta N z r hr hr1 hsub
  have hdpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hpdelta : (p : ℝ) * M.delta ≤ 1 := by
    have h1 : M.delta ≤ 1 / (p : ℝ) :=
      le_trans hdelta (by rw [hcS]; exact min_le_left _ _)
    rw [le_div_iff₀ hpR] at h1
    nlinarith [h1]
  have hasq : M.delta ^ 2 ≤
      (d : ℝ) * Real.log 3 / (2 * Real.log 2 * (p : ℝ) ^ 2) := by
    have h2 : M.delta ≤
        Real.sqrt ((d : ℝ) * Real.log 3 / (2 * Real.log 2 * (p : ℝ) ^ 2)) :=
      le_trans hdelta (by rw [hcS]; exact min_le_right _ _)
    have := Real.sq_sqrt
      (show (0:ℝ) ≤ (d : ℝ) * Real.log 3 / (2 * Real.log 2 * (p : ℝ) ^ 2) by positivity)
    nlinarith [hdpos.le, Real.sqrt_nonneg
      ((d : ℝ) * Real.log 3 / (2 * Real.log 2 * (p : ℝ) ^ 2))]
  have hatwo : 2 * (chaosLayerRate M p / Real.log 3) = Cexponent * M.delta ^ 2 := by
    rw [hCe, chaosLayerRate]
    field_simp
  have ha : chaosLayerRate M p / Real.log 3 ≤ (d : ℝ) / 4 := by
    rw [chaosLayerRate, div_le_iff₀ hlog3]
    have h := hasq
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * Real.log 2 * (p : ℝ) ^ 2)] at h
    have hrw : M.delta ^ 2 * (2 * Real.log 2 * (p : ℝ) ^ 2)
        = 4 * (Real.log 2 / 2 * (p : ℝ) ^ 2 * M.delta ^ 2) := by ring
    rw [hrw] at h
    linarith
  have hQK : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      (K : Set (SpatialCoordinates d)) := hsub.trans hs
  obtain ⟨hmeas, hint, hbnd⟩ :=
    weighted_moment_bound hd M H hH p hp N hpdelta ha K z r hr hr1 hQK
  refine ⟨hmeas, hint, hbnd.trans ?_⟩
  rw [hatwo]
  have hPhi := (hCKspec M H hH K (p : ℝ) (by positivity)).2
  have hexpmono : Real.exp (CK K * (p : ℝ) ^ 2 * M.delta ^ 2) ≤
      Real.exp (CK K * (p : ℝ) ^ 2 * cSmall ^ 2) := by
    refine Real.exp_le_exp.mpr ?_
    have hsq : M.delta ^ 2 ≤ cSmall ^ 2 := by nlinarith [hdpos.le, hcSpos.le, hdelta]
    calc CK K * (p : ℝ) ^ 2 * M.delta ^ 2
        = (CK K * (p : ℝ) ^ 2) * M.delta ^ 2 := by ring
      _ ≤ (CK K * (p : ℝ) ^ 2) * cSmall ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (mul_nonneg (hCKnn K) (by positivity))
      _ = CK K * (p : ℝ) ^ 2 * cSmall ^ 2 := by ring
  have hrpow : 0 ≤ r ^ ((d : ℝ) * p - Cexponent * M.delta ^ 2) := by positivity
  have hstep : (∫ omega, Real.exp ((p : ℝ) *
      ‖(H omega).restrict (K : Set (SpatialCoordinates d))‖)
      ∂(chaosSampleLaw M).toMeasure) ≤
      2 * Real.exp (CK K * (p : ℝ) ^ 2 * cSmall ^ 2) :=
    hPhi.trans (by nlinarith [hexpmono, Real.exp_pos (CK K * (p : ℝ) ^ 2 * M.delta ^ 2)])
  calc (∫ omega, Real.exp ((p : ℝ) *
        ‖(H omega).restrict (K : Set (SpatialCoordinates d))‖)
        ∂(chaosSampleLaw M).toMeasure) *
        (Cm * r ^ ((d : ℝ) * p - Cexponent * M.delta ^ 2))
      ≤ (2 * Real.exp (CK K * (p : ℝ) ^ 2 * cSmall ^ 2)) *
        (Cm * r ^ ((d : ℝ) * p - Cexponent * M.delta ^ 2)) := by
        refine mul_le_mul_of_nonneg_right hstep ?_
        positivity
    _ = 2 * Real.exp (CK K * (p : ℝ) ^ 2 * cSmall ^ 2) * Cm *
        r ^ ((d : ℝ) * p - Cexponent * M.delta ^ 2) := by ring

end SubdiffusiveProcess
