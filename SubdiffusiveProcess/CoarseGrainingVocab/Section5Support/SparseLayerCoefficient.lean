import SubdiffusiveProcess.CoarseGrainingVocab.AnnealedProviders
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SimplexGapRigidity




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open MeasureTheory ProbabilityTheory Homogenization
open SubdiffusiveProcess.Frozen.Assumptions
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## Definitions -/



noncomputable def shellFactor (M : GMCModel d) (k : ℕ)
    (omega : PotentialSample d) (x : Vec d) : ℝ :=
  Real.exp (omega k x - tauSq M.P)

/-- The product of the shell factors over an arbitrary finite set of layers.
This is the common shape of `a_m`, `A_N^{(R)}`, and `C_m^{(R)}`. -/
noncomputable def layerCoefficient (M : GMCModel d) (S : Finset ℕ)
    (omega : PotentialSample d) (x : Vec d) : ℝ :=
  ∏ k ∈ S, shellFactor M k omega x



noncomputable def sparseLayerCoefficient (M : GMCModel d) (R N : ℕ)
    (omega : PotentialSample d) (x : Vec d) : ℝ :=
  ∏ j ∈ Finset.range (N + 1), shellFactor M (j * R) omega x



noncomputable def complementLayerCoefficient (M : GMCModel d) (R m : ℕ)
    (omega : PotentialSample d) (x : Vec d) : ℝ :=
  ∏ k ∈ (Finset.range (m + 1)).filter (fun k => ¬ R ∣ k),
    shellFactor M k omega x

/-- The layer indices carried by `A_N^{(R)}`. -/
def sparseLayerIndices (R N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).image (fun j => j * R)

/-- The layer indices carried by `C_m^{(R)}`. -/
def complementLayerIndices (R m : ℕ) : Finset ℕ :=
  (Finset.range (m + 1)).filter (fun k => ¬ R ∣ k)

/-! ## Characterizations -/

/-- Exponential-sum form of the layer product. -/
theorem layerCoefficient_eq_exp_sum (M : GMCModel d) (S : Finset ℕ)
    (omega : PotentialSample d) (x : Vec d) :
    layerCoefficient M S omega x =
      Real.exp (∑ k ∈ S, (omega k x - tauSq M.P)) := by
  rw [layerCoefficient, Real.exp_sum]
  rfl

/-- The paper's finite cutoff `a_m` is the layer product over
`Finset.range (m + 1)`. -/
theorem aCutoff_eq_layerCoefficient (M : GMCModel d) (m : ℕ)
    (omega : PotentialSample d) (x : Vec d) :
    aCutoff M m omega x = layerCoefficient M (Finset.range (m + 1)) omega x := by
  rw [layerCoefficient_eq_exp_sum]
  rfl

/-- `A_N^{(R)}` is the layer product over `sparseLayerIndices R N`, for every
positive spacing `R`. -/
theorem sparseLayerCoefficient_eq_layerCoefficient (M : GMCModel d) {R : ℕ}
    (hR : 0 < R) (N : ℕ) (omega : PotentialSample d) (x : Vec d) :
    sparseLayerCoefficient M R N omega x =
      layerCoefficient M (sparseLayerIndices R N) omega x := by
  rw [layerCoefficient, sparseLayerIndices,
    Finset.prod_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_right hR hab)]
  rfl

/-- `C_m^{(R)}` is the layer product over `complementLayerIndices R m`. -/
theorem complementLayerCoefficient_eq_layerCoefficient (M : GMCModel d)
    (R m : ℕ) (omega : PotentialSample d) (x : Vec d) :
    complementLayerCoefficient M R m omega x =
      layerCoefficient M (complementLayerIndices R m) omega x :=
  rfl

/-- Every layer product is positive. -/
theorem layerCoefficient_pos (M : GMCModel d) (S : Finset ℕ)
    (omega : PotentialSample d) (x : Vec d) :
    0 < layerCoefficient M S omega x :=
  Finset.prod_pos fun _ _ => Real.exp_pos _

/-! ## The factorization display -/

/-- The multiples of `R` inside `Finset.range (m + 1)` are exactly the sparse
indices up to `floor (m / R)`. -/
theorem filter_dvd_range_eq_sparseLayerIndices {R : ℕ} (hR : 0 < R) (m : ℕ) :
    (Finset.range (m + 1)).filter (fun k => R ∣ k) =
      sparseLayerIndices R (m / R) := by
  ext k
  simp only [sparseLayerIndices, Finset.mem_filter, Finset.mem_range,
    Finset.mem_image, Nat.lt_succ_iff]
  constructor
  · rintro ⟨hkm, j, rfl⟩
    refine ⟨j, ?_, Nat.mul_comm j R⟩
    exact (Nat.le_div_iff_mul_le hR).2 (by rw [Nat.mul_comm]; exact hkm)
  · rintro ⟨j, hj, rfl⟩
    refine ⟨?_, ⟨j, by ring⟩⟩
    exact le_trans (Nat.mul_le_mul_right R hj) (Nat.div_mul_le_self m R)
/-- The sparse and complementary index sets are disjoint. -/
theorem disjoint_sparse_complement {R : ℕ} (hR : 0 < R) (m : ℕ) :
    Disjoint (sparseLayerIndices R (m / R)) (complementLayerIndices R m) := by
  rw [← filter_dvd_range_eq_sparseLayerIndices hR m, complementLayerIndices]
  exact Finset.disjoint_filter_filter_neg _ _ _

/-- The sparse and complementary index sets partition `Finset.range (m + 1)`. -/
theorem sparse_union_complement {R : ℕ} (hR : 0 < R) (m : ℕ) :
    sparseLayerIndices R (m / R) ∪ complementLayerIndices R m =
      Finset.range (m + 1) := by
  rw [← filter_dvd_range_eq_sparseLayerIndices hR m, complementLayerIndices,
    Finset.filter_union_filter_neg_eq]

/-- Layer products multiply over disjoint index sets. -/
theorem layerCoefficient_union (M : GMCModel d) {S T : Finset ℕ}
    (hST : Disjoint S T) (omega : PotentialSample d) (x : Vec d) :
    layerCoefficient M (S ∪ T) omega x =
      layerCoefficient M S omega x * layerCoefficient M T omega x :=
  Finset.prod_union hST



theorem aCutoff_eq_sparse_mul_complement (M : GMCModel d) {R : ℕ} (hR : 0 < R)
    (m : ℕ) (omega : PotentialSample d) (x : Vec d) :
    aCutoff M m omega x =
      sparseLayerCoefficient M R (m / R) omega x *
        complementLayerCoefficient M R m omega x := by
  rw [aCutoff_eq_layerCoefficient, ← sparse_union_complement hR m,
    layerCoefficient_union M (disjoint_sparse_complement hR m),
    sparseLayerCoefficient_eq_layerCoefficient M hR,
    complementLayerCoefficient_eq_layerCoefficient]

/-- **The factorization at the sparse index.**  At `m = N * R` — the index at
which the sparse-layer premise `HighDimensionalSparseLayerConclusion` speaks,
and hence the coefficient underlying `ahom M (N * R)` — the display reads
`a_{NR} = A_N^{(R)} C_{NR}^{(R)}`. -/
theorem aCutoff_sparse_index_eq_sparse_mul_complement (M : GMCModel d) {R : ℕ}
    (hR : 0 < R) (N : ℕ) (omega : PotentialSample d) :
    aCutoff M (N * R) omega =
      fun x => sparseLayerCoefficient M R N omega x *
        complementLayerCoefficient M R (N * R) omega x := by
  funext x
  rw [aCutoff_eq_sparse_mul_complement M hR (N * R) omega x,
    Nat.mul_div_cancel _ hR]

/-! ## Normalization -/

/-- The exponential moment defining `tauSq` is positive. -/
private theorem integral_exp_zero_pos (M : GMCModel d) :
    0 < ∫ g : PotentialField d, Real.exp (g 0)
      ∂(zeroPotentialLaw M.P).toMeasure := by
  have hnonneg : 0 ≤ ∫ g : PotentialField d, Real.exp (g 0)
      ∂(zeroPotentialLaw M.P).toMeasure :=
    integral_nonneg fun _ => (Real.exp_pos _).le
  have hlog : 0 < Real.log (∫ g : PotentialField d, Real.exp (g 0)
      ∂(zeroPotentialLaw M.P).toMeasure) := M.G4.tauSq_pos
  exact zero_lt_one.trans ((Real.log_pos_iff hnonneg).mp hlog)

/-- The normalization identity `exp (tau^2) = E[exp (g_0(0))]`. -/
private theorem exp_tauSq_eq (M : GMCModel d) :
    Real.exp (tauSq M.P) =
      ∫ g : PotentialField d, Real.exp (g 0)
        ∂(zeroPotentialLaw M.P).toMeasure :=
  Real.exp_log (integral_exp_zero_pos M)



theorem mgf_shell_eval_sub_tauSq (M : GMCModel d) (k : ℕ) (x : Vec d) :
    mgf (fun omega : PotentialSample d => omega k x - tauSq M.P)
      M.P.toMeasure 1 = 1 := by
  rw [mgf]
  calc
    ∫ omega : PotentialSample d,
        Real.exp (1 * (omega k x - tauSq M.P)) ∂M.P.toMeasure =
        Real.exp (-tauSq M.P) *
          ∫ omega : PotentialSample d, Real.exp (omega k x) ∂M.P.toMeasure := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
      simp only [one_mul, Real.exp_sub, Real.exp_neg]
      ring
    _ = Real.exp (-tauSq M.P) *
          ∫ g : PotentialField d, Real.exp (g 0)
            ∂(zeroPotentialLaw M.P).toMeasure := by
      rw [integral_exp_shell_eval M k x]
    _ = 1 := by
      rw [← exp_tauSq_eq M, Real.exp_neg]
      field_simp



theorem integral_layerCoefficient_apply (M : GMCModel d) (S : Finset ℕ)
    (x : Vec d) :
    ∫ omega : PotentialSample d, layerCoefficient M S omega x
      ∂M.P.toMeasure = 1 := by
  classical
  set X : ℕ → PotentialSample d → ℝ :=
    fun k omega => omega k x - tauSq M.P with hX
  have hIndep : iIndepFun X M.P.toMeasure := by
    simpa [hX, Function.comp_def] using M.shellPrefix.independent.comp
      (fun _ g => g x - tauSq M.P)
      (fun _ => (PotentialField.measurable_eval x).sub measurable_const)
  have hMeas : ∀ k, Measurable (X k) := fun k =>
    (measurable_shell_eval k x).sub measurable_const
  calc
    ∫ omega : PotentialSample d, layerCoefficient M S omega x ∂M.P.toMeasure =
        mgf (∑ k ∈ S, X k) M.P.toMeasure 1 := by
      simp [mgf, layerCoefficient_eq_exp_sum, hX, Finset.sum_apply]
    _ = ∏ k ∈ S, mgf (X k) M.P.toMeasure 1 := hIndep.mgf_sum hMeas _
    _ = 1 := by
      simp [hX, mgf_shell_eval_sub_tauSq M _ x]



theorem integral_shellFactor_apply (M : GMCModel d) (k : ℕ) (x : Vec d) :
    ∫ omega : PotentialSample d, shellFactor M k omega x ∂M.P.toMeasure = 1 := by
  have h := integral_layerCoefficient_apply M {k} x
  simpa [layerCoefficient] using h

/-- `E[A_N^{(R)}(x)] = 1`. -/
theorem integral_sparseLayerCoefficient_apply (M : GMCModel d) {R : ℕ}
    (hR : 0 < R) (N : ℕ) (x : Vec d) :
    ∫ omega : PotentialSample d, sparseLayerCoefficient M R N omega x
      ∂M.P.toMeasure = 1 := by
  simp only [sparseLayerCoefficient_eq_layerCoefficient M hR]
  exact integral_layerCoefficient_apply M _ x



theorem integral_complementLayerCoefficient_apply (M : GMCModel d) (R m : ℕ)
    (x : Vec d) :
    ∫ omega : PotentialSample d, complementLayerCoefficient M R m omega x
      ∂M.P.toMeasure = 1 :=
  integral_layerCoefficient_apply M _ x

/-! ## Independence of complementary layer blocks -/

/-- The layer product as a measurable function of the layers it uses. -/
private noncomputable def layerProductOfTuple (M : GMCModel d) (S : Finset ℕ)
    (v : (i : S) → PotentialField d) (x : Vec d) : ℝ :=
  ∏ i : S, Real.exp (v i x - tauSq M.P)

private theorem measurable_layerProductOfTuple (M : GMCModel d) (S : Finset ℕ) :
    Measurable (layerProductOfTuple M S) := by
  refine measurable_pi_lambda _ fun x => ?_
  refine Finset.measurable_prod _ fun i _ => ?_
  exact (((PotentialField.measurable_eval x).comp
    (measurable_pi_apply i)).sub measurable_const).exp

private theorem layerProductOfTuple_apply (M : GMCModel d) (S : Finset ℕ)
    (omega : PotentialSample d) :
    layerProductOfTuple M S (fun i : S => omega i) =
      layerCoefficient M S omega := by
  funext x
  rw [layerProductOfTuple, layerCoefficient]
  exact Finset.prod_coe_sort S (fun k => Real.exp (omega k x - tauSq M.P))

/-- **Disjoint layer blocks are independent.**  This is the mutual layer
independence of the standing model (`ShellLawPrefix.independent`) pushed
through the two layer products, as whole random fields. -/
theorem indepFun_layerCoefficient_of_disjoint (M : GMCModel d) {S T : Finset ℕ}
    (hST : Disjoint S T) :
    IndepFun (fun omega : PotentialSample d => layerCoefficient M S omega)
      (fun omega : PotentialSample d => layerCoefficient M T omega)
      M.P.toMeasure := by
  have hbase :=
    M.shellPrefix.independent.indepFun_finset S T hST
      (fun k => measurable_potentialCoordinate k)
  have hcomp := hbase.comp (measurable_layerProductOfTuple M S)
    (measurable_layerProductOfTuple M T)
  simpa [Function.comp_def, layerProductOfTuple_apply M S,
    layerProductOfTuple_apply M T] using hcomp



theorem indepFun_sparseLayerCoefficient_complementLayerCoefficient
    (M : GMCModel d) {R : ℕ} (hR : 0 < R) (m : ℕ) :
    IndepFun
      (fun omega : PotentialSample d =>
        sparseLayerCoefficient M R (m / R) omega)
      (fun omega : PotentialSample d => complementLayerCoefficient M R m omega)
      M.P.toMeasure := by
  have h := indepFun_layerCoefficient_of_disjoint M
    (disjoint_sparse_complement hR m)
  have hsparse : (fun omega : PotentialSample d =>
      sparseLayerCoefficient M R (m / R) omega) =
      fun omega : PotentialSample d =>
        layerCoefficient M (sparseLayerIndices R (m / R)) omega := by
    funext omega x
    exact sparseLayerCoefficient_eq_layerCoefficient M hR _ omega x
  rw [hsparse]
  exact h

/-- Every layer product is a measurable observable at each point. -/
theorem measurable_layerCoefficient_apply (M : GMCModel d) (S : Finset ℕ)
    (x : Vec d) :
    Measurable (fun omega : PotentialSample d => layerCoefficient M S omega x) :=
  Finset.measurable_prod _ fun k _ =>
    ((measurable_shell_eval k x).sub measurable_const).exp

/-- Measurability of `C_m^{(R)}` at a point. -/
theorem measurable_complementLayerCoefficient_apply (M : GMCModel d) (R m : ℕ)
    (x : Vec d) :
    Measurable (fun omega : PotentialSample d =>
      complementLayerCoefficient M R m omega x) :=
  measurable_layerCoefficient_apply M _ x



theorem integral_mul_complementLayerCoefficient_apply (M : GMCModel d)
    (R m : ℕ) (x : Vec d) {F : PotentialSample d → ℝ}
    (hF : AEStronglyMeasurable F M.P.toMeasure)
    (hindep : IndepFun F
      (fun omega : PotentialSample d => complementLayerCoefficient M R m omega x)
      M.P.toMeasure) :
    ∫ omega : PotentialSample d,
        F omega * complementLayerCoefficient M R m omega x ∂M.P.toMeasure =
      ∫ omega : PotentialSample d, F omega ∂M.P.toMeasure := by
  rw [hindep.integral_fun_mul_eq_mul_integral hF
      (measurable_complementLayerCoefficient_apply M R m x).aestronglyMeasurable,
    integral_complementLayerCoefficient_apply M R m x, mul_one]

/-- Pointwise form of the same independence, at any spatial point. -/
theorem indepFun_sparse_complement_apply (M : GMCModel d) {R : ℕ} (hR : 0 < R)
    (m : ℕ) (x : Vec d) :
    IndepFun
      (fun omega : PotentialSample d =>
        sparseLayerCoefficient M R (m / R) omega x)
      (fun omega : PotentialSample d =>
        complementLayerCoefficient M R m omega x) M.P.toMeasure :=
  (indepFun_sparseLayerCoefficient_complementLayerCoefficient M hR m).comp
    (measurable_pi_apply x) (measurable_pi_apply x)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
