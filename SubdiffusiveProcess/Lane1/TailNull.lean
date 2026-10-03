module

public import SubdiffusiveProcess.Lane1.TailFunctional
public import SubdiffusiveProcess.Lane1.TestFunctionMartingale
public import SubdiffusiveProcess.Main.MeasuresConvergeLocally
public import SubdiffusiveProcess.Lane1.OpenExhaustion

@[expose] public section

/-!
# A cube is null for the limit exactly when the tail functional vanishes

The limiting chaos depends on every layer, so the event that it gives a cube no
mass is not visibly a tail event.  It is one all the same: the first `k+1`
layers enter the cutoff densities only through a continuous strictly positive
factor, which on the compact support of a test function is bounded between two
positive constants and therefore cannot turn a vanishing limit into a
non-vanishing one.  What is left after that factor is removed is the tail
functional of `TailFunctional.lean`, which reads only the layers beyond `k`.
-/

open Filter MeasureTheory
open scoped CompactlySupported ENNReal NNReal Topology

noncomputable section
namespace SubdiffusiveProcess

variable {d : ℕ}

section Split

variable [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The test integral of the cutoff chaos, with the first `k+1` layers split
off as a weight. -/
theorem integral_weightedChaosCutoff_split
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (k m : ℕ) (omega : BilateralField d) (f : SpatialCoordinates d → ℝ) :
    ∫ x, f x ∂(weightedChaosCutoff M H (k + 1 + m) omega)
      = ∫ x, (f x * (Real.exp (H omega x) * fineDensity M k omega x))
          * fineDensity M m (layerShift (k + 1) omega) x ∂volume := by
  rw [integral_weightedChaosCutoff_eq]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show Real.exp (H omega x) * fineDensity M (k + 1 + m) omega x * f x
    = f x * (Real.exp (H omega x) * fineDensity M k omega x)
      * fineDensity M m (layerShift (k + 1) omega) x
  rw [fineDensity_split M k m omega x]
  ring

end Split

/-- Multiplying a compactly supported test function by a continuous function. -/
def mulContinuous (f : C_c(SpatialCoordinates d, ℝ))
    (w : C(SpatialCoordinates d, ℝ)) : C_c(SpatialCoordinates d, ℝ) :=
  ⟨⟨fun x => f x * w x, (map_continuous f).mul (map_continuous w)⟩,
    f.hasCompactSupport.mul_right⟩

@[simp] theorem mulContinuous_apply (f : C_c(SpatialCoordinates d, ℝ))
    (w : C(SpatialCoordinates d, ℝ)) (x : SpatialCoordinates d) :
    mulContinuous f w x = f x * w x := rfl

/-- A continuous function with compact support is integrable against any
measure finite on compacts. -/
theorem integrable_cc (f : C_c(SpatialCoordinates d, ℝ))
    (nu : Measure (SpatialCoordinates d)) [IsFiniteMeasureOnCompacts nu] :
    Integrable (fun x => f x) nu :=
  (map_continuous f).integrable_of_hasCompactSupport f.hasCompactSupport

section Urysohn

/-- The Urysohn functions of the exhaustion of an open set. -/
def urysohnSeq {U : Set (SpatialCoordinates d)} (hU : IsOpen U) (n : ℕ) :
    C_c(SpatialCoordinates d, ℝ) :=
  Classical.choose (exists_urysohn_openPiece hU n)

theorem urysohnSeq_spec {U : Set (SpatialCoordinates d)} (hU : IsOpen U) (n : ℕ) :
    (∀ x, 0 ≤ urysohnSeq hU n x ∧ urysohnSeq hU n x ≤ 1) ∧
      (∀ x ∈ openPiece U n, urysohnSeq hU n x = 1) ∧
      tsupport ((urysohnSeq hU n : SpatialCoordinates d → ℝ)) ⊆ U :=
  Classical.choose_spec (exists_urysohn_openPiece hU n)

theorem urysohnSeq_nonneg {U : Set (SpatialCoordinates d)} (hU : IsOpen U)
    (n : ℕ) (x : SpatialCoordinates d) : 0 ≤ urysohnSeq hU n x :=
  ((urysohnSeq_spec hU n).1 x).1

/-- An open set is null exactly when every Urysohn function of its exhaustion
integrates to zero. -/
theorem measure_eq_zero_iff_integral_urysohn
    (nu : Measure (SpatialCoordinates d)) [IsFiniteMeasureOnCompacts nu]
    {U : Set (SpatialCoordinates d)} (hU : IsOpen U) :
    nu U = 0 ↔ ∀ n, ∫ x, urysohnSeq hU n x ∂nu = 0 := by
  constructor
  · intro hzero n
    have hsub : {x | urysohnSeq hU n x ≠ 0} ⊆ U := by
      intro x hx
      exact (urysohnSeq_spec hU n).2.2 (subset_tsupport _ hx)
    have hnull : nu {x | urysohnSeq hU n x ≠ 0} = 0 :=
      measure_mono_null hsub hzero
    refine integral_eq_zero_of_ae ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx
    simpa using not_not.mp hx
  · intro hzero
    have hpiece : ∀ n, nu (openPiece U n) = 0 := by
      intro n
      have hae : (fun x => urysohnSeq hU n x) =ᵐ[nu] 0 :=
        (integral_eq_zero_iff_of_nonneg (urysohnSeq_nonneg hU n)
          (integrable_cc _ nu)).mp (hzero n)
      have hsub : openPiece U n ⊆ {x | urysohnSeq hU n x ≠ 0} := by
        intro x hx
        simp only [Set.mem_setOf_eq, (urysohnSeq_spec hU n).2.1 x hx]
        exact one_ne_zero
      refine measure_mono_null hsub ?_
      have : nu {x | ¬ urysohnSeq hU n x = 0} = 0 := by
        have := hae
        rw [Filter.EventuallyEq, ae_iff] at this
        simpa using this
      simpa using this
    rw [← iUnion_openPiece hU]
    exact measure_iUnion_null hpiece

end Urysohn

section Sandwich

variable [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The factor through which the first `k+1` layers enter the cutoff chaos. -/
def blockWeight (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (k : ℕ)
    (omega : BilateralField d) : C(SpatialCoordinates d, ℝ) :=
  ⟨fun x => Real.exp (H omega x) * fineDensity M k omega x,
    (Real.continuous_exp.comp (H omega).continuous).mul
      (continuous_fineDensity M k omega)⟩

theorem blockWeight_pos (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (k : ℕ)
    (omega : BilateralField d) (x : SpatialCoordinates d) :
    0 < blockWeight M H k omega x :=
  mul_pos (Real.exp_pos _) (fineDensity_pos M k omega x)

/-- The mass a test function receives in the limit vanishes exactly when the
tail functional does.  The first `k+1` layers are bounded between two positive
constants on the support of the test function, so they cannot decide the
question. -/
theorem integral_eq_zero_iff_tailTestLimsup
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (k : ℕ)
    (omega : BilateralField d) (nu : Measure (SpatialCoordinates d))
    (f : C_c(SpatialCoordinates d, ℝ)) (hf : ∀ x, 0 ≤ f x)
    (hconv : Tendsto (fun N => ∫ x, f x ∂(weightedChaosCutoff M H N omega)) atTop
      (nhds (∫ x, f x ∂nu))) :
    ∫ x, f x ∂nu = 0 ↔ tailTestLimsup M f (k + 1) omega = 0 := by
  classical
  set w : C(SpatialCoordinates d, ℝ) := blockWeight M H k omega with hw
  set F : ℕ → SpatialCoordinates d → ℝ :=
    fun m x => fineDensity M m (layerShift (k + 1) omega) x with hF
  set a : ℕ → ℝ := fun m => ∫ x, f x * F m x ∂volume with ha
  set b : ℕ → ℝ := fun m => ∫ x, f x ∂(weightedChaosCutoff M H (k + 1 + m) omega)
    with hbdef
  have hFpos : ∀ m x, 0 < F m x := fun m x => fineDensity_pos M m _ x
  have hb : ∀ m, b m = ∫ x, (f x * w x) * F m x ∂volume := by
    intro m
    exact integral_weightedChaosCutoff_split M H k m omega _
  have hanonneg : ∀ m, 0 ≤ a m := fun m =>
    integral_nonneg fun x => mul_nonneg (hf x) (hFpos m x).le
  have hbnonneg : ∀ m, 0 ≤ b m := fun m => integral_nonneg fun x => hf x
  have hbconv : Tendsto b atTop (nhds (∫ x, f x ∂nu)) :=
    hconv.comp (tendsto_atTop_mono (fun m => Nat.le_add_left m (k + 1)) tendsto_id)
  have htail : tailTestLimsup M f (k + 1) omega
      = limsup (fun m => ENNReal.ofReal (a m)) atTop := rfl
  by_cases hK : (tsupport (f : SpatialCoordinates d → ℝ)).Nonempty
  · obtain ⟨xc, hxc, hmin⟩ := f.hasCompactSupport.exists_isMinOn hK
      (map_continuous w).continuousOn
    obtain ⟨xC, hxC, hmax⟩ := f.hasCompactSupport.exists_isMaxOn hK
      (map_continuous w).continuousOn
    set cv : ℝ := w xc with hcv
    set Cv : ℝ := w xC with hCv
    have hcvpos : 0 < cv := blockWeight_pos M H k omega xc
    have hzero : ∀ x, x ∉ tsupport (f : SpatialCoordinates d → ℝ) → f x = 0 := by
      intro x hx
      by_contra hne
      exact hx (subset_tsupport _ hne)
    have hintF : ∀ m, Integrable (fun x => f x * F m x) volume := by
      intro m
      exact ((map_continuous f).mul
        (continuous_fineDensity M m (layerShift (k + 1) omega))).integrable_of_hasCompactSupport
          (f.hasCompactSupport.mul_right)
    have hintFw : ∀ m, Integrable (fun x => (f x * w x) * F m x) volume := by
      intro m
      exact (((map_continuous f).mul (map_continuous w)).mul
        (continuous_fineDensity M m (layerShift (k + 1) omega))).integrable_of_hasCompactSupport
          ((f.hasCompactSupport.mul_right).mul_right)
    have hlow : ∀ m, cv * a m ≤ b m := by
      intro m
      rw [hb m, ← integral_const_mul]
      refine integral_mono ((hintF m).const_mul cv) (hintFw m) fun x => ?_
      by_cases hx : x ∈ tsupport (f : SpatialCoordinates d → ℝ)
      · have hle : cv ≤ w x := hmin hx
        have hnn : 0 ≤ f x * F m x := mul_nonneg (hf x) (hFpos m x).le
        calc cv * (f x * F m x) ≤ w x * (f x * F m x) :=
              mul_le_mul_of_nonneg_right hle hnn
          _ = f x * w x * F m x := by ring
      · rw [hzero x hx]
        simp
    have hhigh : ∀ m, b m ≤ Cv * a m := by
      intro m
      rw [hb m, ← integral_const_mul]
      refine integral_mono (hintFw m) ((hintF m).const_mul Cv) fun x => ?_
      by_cases hx : x ∈ tsupport (f : SpatialCoordinates d → ℝ)
      · have hle : w x ≤ Cv := hmax hx
        have hnn : 0 ≤ f x * F m x := mul_nonneg (hf x) (hFpos m x).le
        calc f x * w x * F m x = w x * (f x * F m x) := by ring
          _ ≤ Cv * (f x * F m x) := mul_le_mul_of_nonneg_right hle hnn
      · rw [hzero x hx]
        simp
    constructor
    · intro hnu
      have hb0 : Tendsto b atTop (nhds 0) := by rw [← hnu]; exact hbconv
      have ha0 : Tendsto a atTop (nhds 0) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le
          tendsto_const_nhds (by simpa using hb0.div_const cv) (fun m => hanonneg m)
          fun m => ?_
        rw [le_div_iff₀ hcvpos, mul_comm]
        exact hlow m
      rw [htail]
      exact (ENNReal.tendsto_ofReal ha0).limsup_eq.trans (by simp)
    · intro hlim
      rw [htail] at hlim
      have hlimsup : limsup (fun m => ENNReal.ofReal (a m)) atTop = 0 := hlim
      have hliminf : liminf (fun m => ENNReal.ofReal (a m)) atTop = 0 :=
        le_antisymm (le_trans (liminf_le_limsup) (le_of_eq hlimsup)) (zero_le)
      have htend : Tendsto (fun m => ENNReal.ofReal (a m)) atTop (nhds 0) :=
        tendsto_of_liminf_eq_limsup hliminf hlimsup
      have ha0 : Tendsto a atTop (nhds 0) := by
        have := (ENNReal.tendsto_toReal (by simp)).comp htend
        simp only [Function.comp_def, ENNReal.toReal_zero] at this
        refine this.congr fun m => ?_
        exact ENNReal.toReal_ofReal (hanonneg m)
      have hb0 : Tendsto b atTop (nhds 0) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le
          tendsto_const_nhds (by simpa using ha0.const_mul Cv) (fun m => hbnonneg m)
          fun m => hhigh m
      have := tendsto_nhds_unique hbconv hb0
      exact this
  · have hfzero : ∀ x, f x = 0 := by
      intro x
      by_contra hne
      exact hK ⟨x, subset_tsupport _ hne⟩
    have h1 : ∫ x, f x ∂nu = 0 := by simp [hfzero]
    have h2 : tailTestLimsup M f (k + 1) omega = 0 := by
      rw [htail]
      have : ∀ m, a m = 0 := by
        intro m
        simp [ha, hfzero]
      simp [this]
    simp [h1, h2]

/-- An open set is null for the limit exactly when the tail functional of
every Urysohn function of its exhaustion vanishes.  The right-hand side reads
only the layers beyond `k`. -/
theorem measure_eq_zero_iff_tail
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (k : ℕ)
    (omega : BilateralField d) (nu : Measure (SpatialCoordinates d))
    [IsFiniteMeasureOnCompacts nu]
    (hconv : MeasuresConvergeLocally
      (fun N => weightedChaosCutoff M H N omega) nu)
    {U : Set (SpatialCoordinates d)} (hU : IsOpen U) :
    nu U = 0 ↔ ∀ n, tailTestLimsup M (urysohnSeq hU n) (k + 1) omega = 0 := by
  rw [measure_eq_zero_iff_integral_urysohn nu hU]
  exact forall_congr' fun n =>
    integral_eq_zero_iff_tailTestLimsup M H k omega nu (urysohnSeq hU n)
      (urysohnSeq_nonneg hU n) (hconv _)

end Sandwich

end SubdiffusiveProcess
