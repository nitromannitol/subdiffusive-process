import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeSupNorm
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeEvents
import SubdiffusiveProcess.CoarseGrainingVocab.ACutoffRange
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.GrowingBallDerivative




set_option autoImplicit false

open MeasureTheory ProbabilityTheory Homogenization Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.Section9 (centeredAxisCube)

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open SubdiffusiveProcess.Frozen.Assumptions

variable {d : ℕ}

/-! ## Obligation O6: range dependence at shell `k` -/

theorem euclideanNorm_eq_vecNorm (x : Vec d) :
    Homogenization.euclideanNorm x = Homogenization.Book.Ch02.vecNorm x := by
  rw [← sq_eq_sq₀ (Homogenization.euclideanNorm_nonneg x)
    (Homogenization.Book.Ch02.vecNorm_nonneg x),
    Homogenization.euclideanNorm_sq,
    Homogenization.Book.Ch02.vecNorm_sq_eq_vecNormSq]

/-- **Obligation O6.**  The `(g1)` range-one dependence of the unit-scale layer,
transported to shell `k`: two boxes separated by `√d·3^k` carry independent
shell-`k` local σ-fields.  The transport is the `marginal_scaling` change of
variables of `SubdiffusiveProcess.Frozen.Assumptions.ShellLawPrefix`, already carried out in
`SubdiffusiveProcess.CoarseGrainingVocab.indep_potentialShellLocal_of_cutoff_separation`. -/
theorem indep_shellLocalSigma_of_separation (M : GMCModel d) (k : ℕ)
    (U V : Set (Vec d)) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hsep : ∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V →
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ k ≤ Homogenization.euclideanNorm (x - y)) :
    Indep (shellLocalSigma k U) (shellLocalSigma k V) M.P.toMeasure := by
  have hsep' : ∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V →
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ k ≤ Homogenization.Book.Ch02.vecNorm (x - y) := by
    intro x y hx hy
    simpa only [euclideanNorm_eq_vecNorm] using hsep hx hy
  have h := SubdiffusiveProcess.CoarseGrainingVocab.indep_potentialShellLocal_of_cutoff_separation
    M k ⟨k, Nat.lt_succ_self k⟩ U V hU hV hsep'
  simpa only [shellLocalSigma] using h

/-! ## The boxes of the layer events -/



def nativeBox (n : ℕ) (C : ℝ) (z : Lattice d) : Set (Vec d) :=
  centeredAxisCube (goodCubeCentre n z) (C * (3 : ℝ) ^ n)

/-- The dependence box of the layer-`j` event, of side `C·3^{n+j}`, as printed in
clause 7b of `SubdiffusiveProcess.Frozen.Section9.weighted_good_cube_events`. -/
def layerBox (n j : ℕ) (C : ℝ) (z : Lattice d) : Set (Vec d) :=
  centeredAxisCube (goodCubeCentre n z) (C * (3 : ℝ) ^ (n + j))

theorem nativeBox_subset_layerBox {C : ℝ} (hC : 0 ≤ C) (n j : ℕ) (z : Lattice d) :
    nativeBox n C z ⊆ layerBox n j C z := by
  refine centeredAxisCube_mono ?_
  have h : (3 : ℝ) ^ n ≤ (3 : ℝ) ^ (n + j) :=
    pow_le_pow_right₀ (by norm_num) (Nat.le_add_right n j)
  exact mul_le_mul_of_nonneg_left h hC

theorem isOpen_centeredAxisCube (x : Vec d) (L : ℝ) : IsOpen (centeredAxisCube x L) :=
  isOpen_axisCube _ _

theorem isBounded_centeredAxisCube (x : Vec d) (L : ℝ) :
    Bornology.IsBounded (centeredAxisCube x L) := by
  refine Bornology.IsBounded.pi fun _ => Metric.isBounded_Ioo _ _

theorem isOpen_layerBox (n j : ℕ) (C : ℝ) (z : Lattice d) :
    IsOpen (layerBox n j C z) := isOpen_centeredAxisCube _ _

theorem isBounded_nativeBox (n : ℕ) (C : ℝ) (z : Lattice d) :
    Bornology.IsBounded (nativeBox n C z) := isBounded_centeredAxisCube _ _

/-! ## The layer events -/



def layerObservable (n : ℕ) (K : Set (Vec d)) (g : PotentialField d) : ℝ :=
  (3 : ℝ) ^ n * boxDerivNorm K g +
    ((3 : ℝ) ^ n) ^ 2 * boxDerivLipschitzSeminorm K g



def layerEvent (n j : ℕ) (C eps1 : ℝ) (z : Lattice d) :
    Set (PotentialSample d) :=
  {omega : PotentialSample d |
    eps1 * (3 : ℝ) ^ (-(j : ℝ) / 4) <
      layerObservable n (nativeBox n C z) (omega (n + j))}



theorem measurableSet_layerEvent [NeZero d] {C : ℝ} (hC : 0 ≤ C) (n j : ℕ)
    (eps1 : ℝ) (z : Lattice d) :
    MeasurableSet[shellLocalSigma (n + j) (layerBox n j C z)]
      (layerEvent n j C eps1 z) := by
  have hgrad := measurable_boxDerivNorm_shellLocalSigma (d := d) (n + j)
    (isOpen_layerBox n j C z) (nativeBox_subset_layerBox hC n j z)
    (isBounded_nativeBox n C z)
  have hhess := measurable_boxDerivLipschitzSeminorm_shellLocalSigma (d := d) (n + j)
    (isOpen_layerBox n j C z) (nativeBox_subset_layerBox hC n j z)
    (isBounded_nativeBox n C z)
  have hobs : @Measurable (PotentialSample d) ℝ
      (shellLocalSigma (n + j) (layerBox n j C z)) _
      (fun omega : PotentialSample d =>
        layerObservable n (nativeBox n C z) (omega (n + j))) :=
    (hgrad.const_mul _).add (hhess.const_mul _)
  exact hobs measurableSet_Ioi

/-! ## Clause 7e: the finite-range clause for one layer -/

/-- **Clause 7e for the layer `j`, with the exact constant relation.**  If
`C + √d ≤ Cdep` then two site sets at lattice distance more than `Cdep·3^j`
carry layer-`j` event fields with independent σ-algebras.  The deterministic
input is `euclidean_separation_of_latticeDist`; the probabilistic input is
obligation O6 at shell `n + j`. -/
theorem finiteRangeIndependentEvents_layer [NeZero d] (M : GMCModel d)
    {C : ℝ} {Cdep : ℕ} (hCdep : C + Real.sqrt (d : ℝ) ≤ (Cdep : ℝ))
    (n j : ℕ) (E : Lattice d → Set (PotentialSample d))
    (hE : ∀ z, MeasurableSet[shellLocalSigma (n + j) (layerBox n j C z)] (E z)) :
    FiniteRangeIndependentEvents M.P.toMeasure (Cdep * 3 ^ j) E := by
  intro S T hsep
  have hmeasU : MeasurableSet (⋃ z ∈ S, layerBox n j C z) := by
    refine MeasurableSet.biUnion S.to_countable fun z _ => ?_
    exact (isOpen_layerBox n j C z).measurableSet
  have hmeasV : MeasurableSet (⋃ z ∈ T, layerBox n j C z) := by
    refine MeasurableSet.biUnion T.to_countable fun z _ => ?_
    exact (isOpen_layerBox n j C z).measurableSet
  have hsepbox : ∀ ⦃p q : Vec d⦄, p ∈ (⋃ z ∈ S, layerBox n j C z) →
      q ∈ (⋃ z ∈ T, layerBox n j C z) →
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ (n + j) ≤ Homogenization.euclideanNorm (p - q) := by
    intro p q hp hq
    obtain ⟨z, hz, hpz⟩ := Set.mem_iUnion₂.mp hp
    obtain ⟨z', hz', hqz⟩ := Set.mem_iUnion₂.mp hq
    exact euclidean_separation_of_latticeDist hCdep (hsep z hz z' hz') hpz hqz
  have hindep := indep_shellLocalSigma_of_separation M (n + j)
    (⋃ z ∈ S, layerBox n j C z) (⋃ z ∈ T, layerBox n j C z) hmeasU hmeasV hsepbox
  exact indep_of_indep_of_le_right
    (indep_of_indep_of_le_left hindep (eventFieldSigma_le_shellLocalSigma hE S))
    (eventFieldSigma_le_shellLocalSigma hE T)

/-! ## Clause 7d: the layer blocks -/

/-- The dependence blocks of the event field of the anchor: the layer-zero event
sees the shells `0, …, n` (it is built from `a_n`), and the layer-`j` event sees
only the shell `n + j`. -/
def goodCubeBlock (n : ℕ) : ℕ → Set ℕ
  | 0 => Set.Iic n
  | (j + 1) => {n + (j + 1)}

theorem pairwise_disjoint_goodCubeBlock (n : ℕ) :
    Pairwise (Function.onFun Disjoint (goodCubeBlock n)) := by
  intro i j hij
  simp only [Function.onFun]
  match i, j with
  | 0, 0 => exact absurd rfl hij
  | 0, (b + 1) =>
      rw [Set.disjoint_left]
      intro k hk hk'
      simp only [goodCubeBlock, Set.mem_Iic, Set.mem_singleton_iff] at hk hk'
      omega
  | (a + 1), 0 =>
      rw [Set.disjoint_left]
      intro k hk hk'
      simp only [goodCubeBlock, Set.mem_Iic, Set.mem_singleton_iff] at hk hk'
      omega
  | (a + 1), (b + 1) =>
      rw [Set.disjoint_left]
      intro k hk hk'
      simp only [goodCubeBlock, Set.mem_singleton_iff] at hk hk'
      omega




theorem centeredAxisCube_subset_closedBall (x : Vec d) {L : ℝ} (hL : 0 ≤ L) :
    centeredAxisCube x L ⊆ Metric.closedBall x (L / 2) := by
  intro y hy
  rw [mem_centeredAxisCube] at hy
  rw [Metric.mem_closedBall, dist_pi_le_iff (by linarith)]
  intro i
  exact le_of_lt (by simpa [Real.dist_eq] using hy i)

/-- The rescaled displacement of a point of a ball of radius `R` from the ball's
centre lies in the unit cube, once `2R < 3^k`. -/
theorem scaled_shift_mem_unitCube {k : ℕ} {R : ℝ} (hk : 2 * R < (3 : ℝ) ^ k)
    {x w : Vec d} (hw : w ∈ Metric.closedBall x R) :
    ((3 : ℝ) ^ k)⁻¹ • w - ((3 : ℝ) ^ k)⁻¹ • x ∈ openCubeSet (originCube d 0) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  rw [Metric.mem_closedBall, dist_eq_norm] at hw
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hcoord : |(w - x) i| ≤ ‖w - x‖ := norm_le_pi_norm (w - x) i
  have habs : |(((3 : ℝ) ^ k)⁻¹ • w - ((3 : ℝ) ^ k)⁻¹ • x) i| < 1 / 2 := by
    rw [← smul_sub, Pi.smul_apply, smul_eq_mul, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < ((3 : ℝ) ^ k)⁻¹)]
    have hle : |(w - x) i| ≤ R := hcoord.trans hw
    have : ((3 : ℝ) ^ k)⁻¹ * |(w - x) i| ≤ ((3 : ℝ) ^ k)⁻¹ * R :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    have hR : ((3 : ℝ) ^ k)⁻¹ * R < 1 / 2 := by
      rw [inv_mul_eq_div, div_lt_iff₀ h3]
      linarith
    exact lt_of_le_of_lt this hR
  simpa only [zpow_zero, mul_one] using (abs_lt.mp habs)

variable {omega : PotentialSample d}

/-- **Pathwise gradient bound.**  On a box inside the ball of radius `R` around
`x`, with `2R < 3^k`, the boxed gradient norm of shell `k` is at most `3^{-k}`
times the own-scale `(g2)` gauge at the rescaled centre. -/
theorem boxDerivNorm_le_translatedShellG2 {k : ℕ} {R : ℝ} (hk : 2 * R < (3 : ℝ) ^ k)
    (omega : PotentialSample d) (x : Vec d) {K : Set (Vec d)}
    (hK : K ⊆ Metric.closedBall x R) :
    boxDerivNorm K (omega k) ≤
      ((3 : ℝ) ^ k)⁻¹ * translatedShellG2 k (((3 : ℝ) ^ k)⁻¹ • x) omega := by
  have hnonneg : 0 ≤ ((3 : ℝ) ^ k)⁻¹ * translatedShellG2 k (((3 : ℝ) ^ k)⁻¹ • x) omega :=
    mul_nonneg (by positivity) (translatedShellG2_nonneg _ _ _)
  refine supWithZero_le hnonneg ?_
  intro w
  have hmem := scaled_shift_mem_unitCube hk (hK w.2)
  have hg := SubdiffusiveProcess.Frozen.Assumptions.PotentialField.norm_deriv_le_g2Observable
    (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate (((3 : ℝ) ^ k)⁻¹ • x)
      (unscalePotential k (omega k))) hmem
  rw [Section6Anchored.deriv_translate] at hg
  have hcancel : ((3 : ℝ) ^ k)⁻¹ • w.1 - ((3 : ℝ) ^ k)⁻¹ • x + ((3 : ℝ) ^ k)⁻¹ • x
      = ((3 : ℝ) ^ k)⁻¹ • w.1 := by abel
  rw [hcancel] at hg
  rw [Section6Anchored.deriv_eq_smul_deriv_unscalePotential k (omega k) w.1, norm_smul,
    Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < ((3 : ℝ) ^ k)⁻¹)]
  exact mul_le_mul_of_nonneg_left hg (by positivity)

/-- **Pathwise Hessian bound.**  Under the same geometry the boxed derivative
Lipschitz seminorm of shell `k` is at most `3^{-2k}` times the own-scale gauge. -/
theorem boxDerivLipschitzSeminorm_le_translatedShellG2 {k : ℕ} {R : ℝ}
    (hk : 2 * R < (3 : ℝ) ^ k) (omega : PotentialSample d) (x : Vec d)
    {K : Set (Vec d)} (hK : K ⊆ Metric.closedBall x R) :
    boxDerivLipschitzSeminorm K (omega k) ≤
      ((3 : ℝ) ^ k)⁻¹ * (((3 : ℝ) ^ k)⁻¹ *
        translatedShellG2 k (((3 : ℝ) ^ k)⁻¹ • x) omega) := by
  have h3 : (0 : ℝ) < ((3 : ℝ) ^ k)⁻¹ := by positivity
  have hnonneg : 0 ≤ ((3 : ℝ) ^ k)⁻¹ * (((3 : ℝ) ^ k)⁻¹ *
      translatedShellG2 k (((3 : ℝ) ^ k)⁻¹ • x) omega) :=
    mul_nonneg h3.le (mul_nonneg h3.le (translatedShellG2_nonneg _ _ _))
  refine supWithZero_le hnonneg ?_
  intro p
  set y : Vec d := ((3 : ℝ) ^ k)⁻¹ • x with hy
  have hmx := scaled_shift_mem_unitCube hk (hK p.1.1.2)
  have hmy := scaled_shift_mem_unitCube hk (hK p.1.2.2)
  have hbound := SubdiffusiveProcess.Frozen.Assumptions.PotentialField.norm_deriv_sub_deriv_le_g2Observable_mul
    (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate y (unscalePotential k (omega k)))
    hmx hmy
  rw [Section6Anchored.deriv_translate, Section6Anchored.deriv_translate] at hbound
  have hc1 : ((3 : ℝ) ^ k)⁻¹ • p.1.1.1 - y + y = ((3 : ℝ) ^ k)⁻¹ • p.1.1.1 := by abel
  have hc2 : ((3 : ℝ) ^ k)⁻¹ • p.1.2.1 - y + y = ((3 : ℝ) ^ k)⁻¹ • p.1.2.1 := by abel
  have hc3 : ((3 : ℝ) ^ k)⁻¹ • p.1.1.1 - y - (((3 : ℝ) ^ k)⁻¹ • p.1.2.1 - y)
      = ((3 : ℝ) ^ k)⁻¹ • p.1.1.1 - ((3 : ℝ) ^ k)⁻¹ • p.1.2.1 := by abel
  rw [hc1, hc2, hc3] at hbound
  have hscaled : ‖((3 : ℝ) ^ k)⁻¹ • p.1.1.1 - ((3 : ℝ) ^ k)⁻¹ • p.1.2.1‖ =
      ((3 : ℝ) ^ k)⁻¹ * ‖p.1.1.1 - p.1.2.1‖ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos h3]
  rw [hscaled] at hbound
  have hkey : SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (omega k) p.1.1.1 -
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (omega k) p.1.2.1 =
      ((3 : ℝ) ^ k)⁻¹ •
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (unscalePotential k (omega k))
            (((3 : ℝ) ^ k)⁻¹ • p.1.1.1) -
          SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (unscalePotential k (omega k))
            (((3 : ℝ) ^ k)⁻¹ • p.1.2.1)) := by
    rw [smul_sub, ← Section6Anchored.deriv_eq_smul_deriv_unscalePotential k (omega k) p.1.1.1,
      ← Section6Anchored.deriv_eq_smul_deriv_unscalePotential k (omega k) p.1.2.1]
  have hne : p.1.1.1 ≠ p.1.2.1 := fun h => p.property (Subtype.ext h)
  have hdpos : 0 < dist p.1.1.1 p.1.2.1 := dist_pos.mpr hne
  rw [div_le_iff₀ hdpos]
  have hdist : dist (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (omega k) p.1.1.1)
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (omega k) p.1.2.1)
      = ‖SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (omega k) p.1.1.1 -
        SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (omega k) p.1.2.1‖ := dist_eq_norm _ _
  rw [hdist, hkey, norm_smul, Real.norm_eq_abs, abs_of_pos h3]
  have hstep : ((3 : ℝ) ^ k)⁻¹ *
      ‖SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (unscalePotential k (omega k))
          (((3 : ℝ) ^ k)⁻¹ • p.1.1.1) -
        SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (unscalePotential k (omega k))
          (((3 : ℝ) ^ k)⁻¹ • p.1.2.1)‖ ≤
      ((3 : ℝ) ^ k)⁻¹ *
        (translatedShellG2 k y omega * (((3 : ℝ) ^ k)⁻¹ * ‖p.1.1.1 - p.1.2.1‖)) :=
    mul_le_mul_of_nonneg_left hbound h3.le
  have hdn : dist p.1.1.1 p.1.2.1 = ‖p.1.1.1 - p.1.2.1‖ := dist_eq_norm _ _
  rw [hdn]
  calc ((3 : ℝ) ^ k)⁻¹ *
        ‖SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (unscalePotential k (omega k))
            (((3 : ℝ) ^ k)⁻¹ • p.1.1.1) -
          SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (unscalePotential k (omega k))
            (((3 : ℝ) ^ k)⁻¹ • p.1.2.1)‖
      ≤ ((3 : ℝ) ^ k)⁻¹ *
        (translatedShellG2 k y omega * (((3 : ℝ) ^ k)⁻¹ * ‖p.1.1.1 - p.1.2.1‖)) := hstep
    _ = ((3 : ℝ) ^ k)⁻¹ * (((3 : ℝ) ^ k)⁻¹ * translatedShellG2 k y omega) *
        ‖p.1.1.1 - p.1.2.1‖ := by ring

/-! ### The combined pathwise bound and the geometric tail -/



theorem layerObservable_le_translatedShellG2 (n j : ℕ) (_hj : 1 ≤ j) {C : ℝ}
    (hC : 0 ≤ C) (hCj : C < (3 : ℝ) ^ j) (z : Lattice d)
    (omega : PotentialSample d) :
    layerObservable n (nativeBox n C z) (omega (n + j)) ≤
      2 * ((3 : ℝ) ^ j)⁻¹ *
        translatedShellG2 (n + j) (((3 : ℝ) ^ (n + j))⁻¹ • goodCubeCentre n z) omega := by
  have han : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hbj : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  have hb1 : (1 : ℝ) ≤ (3 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hsplit : (3 : ℝ) ^ (n + j) = (3 : ℝ) ^ n * (3 : ℝ) ^ j := pow_add _ _ _
  have hR : nativeBox n C z ⊆
      Metric.closedBall (goodCubeCentre n z) (C * (3 : ℝ) ^ n / 2) :=
    centeredAxisCube_subset_closedBall _ (by positivity)
  have hk : 2 * (C * (3 : ℝ) ^ n / 2) < (3 : ℝ) ^ (n + j) := by
    rw [hsplit]
    have : C * (3 : ℝ) ^ n < (3 : ℝ) ^ j * (3 : ℝ) ^ n :=
      mul_lt_mul_of_pos_right hCj han
    linarith
  set T := translatedShellG2 (n + j) (((3 : ℝ) ^ (n + j))⁻¹ • goodCubeCentre n z) omega
    with hT
  have hTnonneg : 0 ≤ T := translatedShellG2_nonneg _ _ _
  have hgrad := boxDerivNorm_le_translatedShellG2 hk omega (goodCubeCentre n z) hR
  have hhess := boxDerivLipschitzSeminorm_le_translatedShellG2 hk omega
    (goodCubeCentre n z) hR
  have hinv : ((3 : ℝ) ^ (n + j))⁻¹ = ((3 : ℝ) ^ n)⁻¹ * ((3 : ℝ) ^ j)⁻¹ := by
    rw [hsplit, mul_inv]
  have hstep1 : (3 : ℝ) ^ n * boxDerivNorm (nativeBox n C z) (omega (n + j))
      ≤ ((3 : ℝ) ^ j)⁻¹ * T := by
    have := mul_le_mul_of_nonneg_left hgrad han.le
    calc (3 : ℝ) ^ n * boxDerivNorm (nativeBox n C z) (omega (n + j))
        ≤ (3 : ℝ) ^ n * (((3 : ℝ) ^ (n + j))⁻¹ * T) := this
      _ = ((3 : ℝ) ^ j)⁻¹ * T := by
          rw [hinv]
          field_simp
  have hstep2 : ((3 : ℝ) ^ n) ^ 2 *
      boxDerivLipschitzSeminorm (nativeBox n C z) (omega (n + j))
      ≤ (((3 : ℝ) ^ j)⁻¹) ^ 2 * T := by
    have h2 := mul_le_mul_of_nonneg_left hhess (by positivity : (0 : ℝ) ≤ ((3 : ℝ) ^ n) ^ 2)
    calc ((3 : ℝ) ^ n) ^ 2 *
          boxDerivLipschitzSeminorm (nativeBox n C z) (omega (n + j))
        ≤ ((3 : ℝ) ^ n) ^ 2 * (((3 : ℝ) ^ (n + j))⁻¹ * (((3 : ℝ) ^ (n + j))⁻¹ * T)) := h2
      _ = (((3 : ℝ) ^ j)⁻¹) ^ 2 * T := by
          rw [hinv]
          field_simp
  have hsq : (((3 : ℝ) ^ j)⁻¹) ^ 2 * T ≤ ((3 : ℝ) ^ j)⁻¹ * T := by
    have hle : (((3 : ℝ) ^ j)⁻¹) ^ 2 ≤ ((3 : ℝ) ^ j)⁻¹ := by
      have hinv1 : ((3 : ℝ) ^ j)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hb1
      nlinarith [inv_pos.mpr hbj]
    exact mul_le_mul_of_nonneg_right hle hTnonneg
  unfold layerObservable
  have := add_le_add hstep1 (hstep2.trans hsq)
  linarith

/-- The tail constant of the layer events: `(4(1+log 2))⁻¹`, the value produced by
`SubdiffusiveProcess.CoarseGrainingVocab.isBigOWith_gammaTwo_translatedShellG2`. -/
def layerTailConstant : ℝ := (4 * (1 + Real.log 2))⁻¹

theorem layerTailConstant_pos : 0 < layerTailConstant := by
  unfold layerTailConstant
  have : (0 : ℝ) < 1 + Real.log 2 := by positivity
  positivity



theorem measure_layerEvent_le (M : GMCModel d) (n j : ℕ) (hj : 1 ≤ j)
    {C eps1 : ℝ} (hC : 0 ≤ C) (hCj : C < (3 : ℝ) ^ j) (heps1 : 0 < eps1)
    (hdelta : 2 * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) ≤ eps1)
    (z : Lattice d) :
    M.P.toMeasure (layerEvent n j C eps1 z) ≤
      ENNReal.ofReal (Real.exp
        (-(layerTailConstant * (eps1 ^ 2 / M.delta ^ 2) * (3 : ℝ) ^ (3 * (j : ℝ) / 2)))) := by
  classical
  have hlog : (0 : ℝ) < 1 + Real.log 2 := by positivity
  have hdpos : 0 < M.delta := M.shellPrefix.delta_pos
  set y : Vec d := ((3 : ℝ) ^ (n + j))⁻¹ • goodCubeCentre n z with hy
  set A : ℝ := (1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta with hA
  have hApos : 0 < A := mul_pos (Real.rpow_pos_of_pos hlog _) hdpos
  set theta : ℝ := eps1 * (3 : ℝ) ^ (3 * (j : ℝ) / 4) / 2 with htheta
  -- the pathwise inclusion
  have hpowj : (3 : ℝ) ^ (j : ℝ) = (3 : ℝ) ^ j := by
    rw [Real.rpow_natCast]
  have hprod : (3 : ℝ) ^ (-(j : ℝ) / 4) * (3 : ℝ) ^ j = (3 : ℝ) ^ (3 * (j : ℝ) / 4) := by
    rw [← hpowj, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
      show (-(j : ℝ) / 4 + (j : ℝ)) = 3 * (j : ℝ) / 4 by ring]
  have hincl : layerEvent n j C eps1 z ⊆
      Homogenization.IndependentSums.upperTailEvent (translatedShellG2 (n + j) y) theta := by
    intro omega homega
    have hdom := layerObservable_le_translatedShellG2 n j hj hC hCj z omega
    have hlt : eps1 * (3 : ℝ) ^ (-(j : ℝ) / 4) <
        2 * ((3 : ℝ) ^ j)⁻¹ * translatedShellG2 (n + j) y omega :=
      lt_of_lt_of_le homega hdom
    have hbj : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
    have hmul := mul_lt_mul_of_pos_right hlt (by positivity : (0 : ℝ) < (3 : ℝ) ^ j / 2)
    show theta < translatedShellG2 (n + j) y omega
    rw [htheta]
    have hrw : 2 * ((3 : ℝ) ^ j)⁻¹ * translatedShellG2 (n + j) y omega *
        ((3 : ℝ) ^ j / 2) = translatedShellG2 (n + j) y omega := by
      field_simp
    rw [hrw] at hmul
    have hleft : eps1 * (3 : ℝ) ^ (-(j : ℝ) / 4) * ((3 : ℝ) ^ j / 2)
        = eps1 * (3 : ℝ) ^ (3 * (j : ℝ) / 4) / 2 := by
      rw [show eps1 * (3 : ℝ) ^ (-(j : ℝ) / 4) * ((3 : ℝ) ^ j / 2)
          = eps1 * ((3 : ℝ) ^ (-(j : ℝ) / 4) * (3 : ℝ) ^ j) / 2 by ring, hprod]
    rw [hleft] at hmul
    exact hmul
  -- the weak-Orlicz tail at level `theta`
  set t : ℝ := theta / A with ht
  have hthetapos : 0 < theta := by
    rw [htheta]
    have : (0 : ℝ) < (3 : ℝ) ^ (3 * (j : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  have hone : (1 : ℝ) ≤ (3 : ℝ) ^ (3 * (j : ℝ) / 4) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have ht1 : 1 ≤ t := by
    rw [ht, le_div_iff₀ hApos, one_mul, htheta]
    have h1 : A * 2 ≤ eps1 := by rw [hA]; linarith
    nlinarith
  have hAt : A * t = theta := by
    rw [ht]
    field_simp
  have htail := SubdiffusiveProcess.CoarseGrainingVocab.isBigOWith_gammaTwo_translatedShellG2 M (n + j) y ht1
  rw [hAt] at htail
  -- convert the exponent
  have hAsq : A ^ 2 = (1 + Real.log 2) * M.delta ^ 2 := by
    rw [hA, mul_pow]
    congr 1
    rw [← Real.rpow_natCast ((1 + Real.log 2) ^ (2 : ℝ)⁻¹) 2, ← Real.rpow_mul hlog.le]
    norm_num
  have hsq34 : ((3 : ℝ) ^ (3 * (j : ℝ) / 4)) ^ (2 : ℕ) = (3 : ℝ) ^ (3 * (j : ℝ) / 2) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (3 * (j : ℝ) / 4)) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    push_cast
    ring
  have hthetasq : theta ^ 2 = eps1 ^ 2 * (3 : ℝ) ^ (3 * (j : ℝ) / 2) / 4 := by
    rw [htheta, div_pow, mul_pow, hsq34]
    ring
  have htsq : t ^ 2 =
      layerTailConstant * (eps1 ^ 2 / M.delta ^ 2) * (3 : ℝ) ^ (3 * (j : ℝ) / 2) := by
    rw [ht, div_pow, hthetasq, hAsq, layerTailConstant]
    have h1 : (1 : ℝ) + Real.log 2 ≠ 0 := ne_of_gt hlog
    have h2 : M.delta ≠ 0 := ne_of_gt hdpos
    field_simp
  have hgamma : (Homogenization.IndependentSums.gammaSigma 2 t)⁻¹ =
      Real.exp (-(layerTailConstant * (eps1 ^ 2 / M.delta ^ 2) *
        (3 : ℝ) ^ (3 * (j : ℝ) / 2))) := by
    rw [Homogenization.IndependentSums.gammaSigma_apply, ← Real.exp_neg]
    congr 1
    rw [← htsq, ← Real.rpow_natCast t 2]
    norm_num
  rw [hgamma] at htail
  -- back to the measure
  have hmono : M.P.toMeasure (layerEvent n j C eps1 z) ≤
      M.P.toMeasure (Homogenization.IndependentSums.upperTailEvent
        (translatedShellG2 (n + j) y) theta) := measure_mono hincl
  refine hmono.trans ?_
  have hne : M.P.toMeasure (Homogenization.IndependentSums.upperTailEvent
      (translatedShellG2 (n + j) y) theta) ≠ ⊤ := measure_ne_top _ _
  rw [← ENNReal.ofReal_toReal hne]
  exact ENNReal.ofReal_le_ofReal htail

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
