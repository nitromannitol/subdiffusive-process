import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Probability.LayerProductBlocks
import Mathlib.Probability.Independence.Basic
import Mathlib.Topology.Metrizable.ContinuousMap

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess

theorem infraredCharacterization_indepFun_negCoord_finePrefix
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ)
    (hH : InfraredCharacterization M H) :
    IndepFun
      (fun omega : BilateralField d => omega (-(Int.ofNat (N + 1))))
      (fun omega : BilateralField d =>
        (H omega, fun j : Fin (N + 1) => omega (-(Int.ofNat j))))
      (chaosSampleLaw M).toMeasure := by
  classical
  let laws : (j : ℤ) → Measure C(SpatialCoordinates d, ℝ) :=
    fun j => (scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure
  have hmeasure : (chaosSampleLaw M).toMeasure = Measure.infinitePi laws := by
    rfl
  let idx : ℤ := -(Int.ofNat (N + 1))
  let S : Set ℤ := {idx}
  let T : Set ℤ := Sᶜ
  have hST : Disjoint S T := by
    exact disjoint_compl_right
  have hpartial : ∀ L : ℕ, Measurable (fun omega : BilateralField d =>
      infraredPartialSum omega L) := by
    intro L
    unfold infraredPartialSum
    apply Continuous.measurable
    apply continuous_finset_sum
    intro n hn
    have hcoord : Continuous (fun beta : BilateralField d =>
        beta (Int.ofNat (n + 1))) := continuous_apply (Int.ofNat (n + 1))
    have heval0 : Continuous (fun f : C(SpatialCoordinates d, ℝ) => f 0) :=
      continuous_eval_const 0
    have hc : Continuous (fun beta : BilateralField d =>
        ContinuousMap.const (SpatialCoordinates d) ((beta (Int.ofNat (n + 1))) 0)) := by
      simpa [ContinuousMap.constPi, Function.comp_def] using
        ((ContinuousMap.continuous_const' (X := SpatialCoordinates d) (Y := ℝ)).comp
          (heval0.comp hcoord))
    exact (continuous_apply (Int.ofNat (n + 1))).sub hc
  let good : Set (BilateralField d) :=
    {beta | ∃ y : C(SpatialCoordinates d, ℝ),
      Tendsto (fun L => infraredPartialSum beta L) atTop (nhds y)}
  have hgood : MeasurableSet good := by
    apply MeasureTheory.measurableSet_exists_tendsto
    intro L
    exact hpartial L
  letI : TopologicalSpace.MetrizableSpace C(SpatialCoordinates d, ℝ) := inferInstance
  let Gseq : ℕ → BilateralField d → C(SpatialCoordinates d, ℝ) := fun L beta =>
    if hbeta : beta ∈ good then infraredPartialSum beta L else 0
  have hGseq : ∀ L : ℕ, Measurable (Gseq L) := by
    intro L
    dsimp [Gseq]
    exact Measurable.ite hgood (hpartial L) measurable_const
  let G : BilateralField d → C(SpatialCoordinates d, ℝ) := fun beta =>
    if hbeta : beta ∈ good then Classical.choose hbeta else 0
  have hGlim : Tendsto Gseq atTop (nhds G) := by
    rw [tendsto_pi_nhds]
    intro beta
    by_cases hbeta : beta ∈ good
    · simpa only [Gseq, G, dif_pos hbeta] using Classical.choose_spec hbeta
    · simp only [Gseq, G, dif_neg hbeta]
      exact tendsto_const_nhds
  have hG : Measurable G := by
    exact measurable_of_tendsto_metrizable hGseq hGlim
  let κ : ((j : T) → C(SpatialCoordinates d, ℝ)) → BilateralField d :=
    fun y i => if hi : i ∈ T then y ⟨i, hi⟩ else 0
  have hκ : Measurable κ := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : i ∈ T
    · have heval : Measurable (fun y : (j : T) → C(SpatialCoordinates d, ℝ) =>
          y ⟨i, hi⟩) := measurable_pi_apply _
      simpa only [κ, dif_pos hi] using heval
    · simp only [κ, dif_neg hi]
      exact measurable_const
  have hκpos (omega : BilateralField d) (i : ℤ) (hi : 0 < i) :
      κ (T.restrict omega) i = omega i := by
    have hiT : i ∈ T := by
      simp only [T, S, Set.mem_compl_iff, Set.mem_singleton_iff]
      change i ≠ -(Int.ofNat (N + 1))
      intro heq
      have hnonneg : (0 : ℤ) ≤ Int.ofNat (N + 1) := Int.natCast_nonneg _
      have hnonpos : -(Int.ofNat (N + 1)) ≤ 0 := neg_nonpos.mpr hnonneg
      linarith
    simp only [κ, dif_pos hiT, Set.restrict_apply]
  have hsum_eq (omega : BilateralField d) (L : ℕ) :
      infraredPartialSum (κ (T.restrict omega)) L = infraredPartialSum omega L := by
    unfold infraredPartialSum
    apply Finset.sum_congr rfl
    intro n hn
    have hnpos : 0 < Int.ofNat (n + 1) := by
      have hn' : 0 < n + 1 := Nat.zero_lt_succ n
      exact Int.natCast_pos.mpr hn'
    simp only [hκpos omega (Int.ofNat (n + 1)) hnpos]
  have hprefixT (j : Fin (N + 1)) : -(Int.ofNat j) ∈ T := by
    simp only [T, S, Set.mem_compl_iff, Set.mem_singleton_iff]
    change -(Int.ofNat (j : ℕ)) ≠ -(Int.ofNat (N + 1))
    intro heq
    apply (Nat.ne_of_lt j.isLt)
    exact Int.ofNat_inj.mp (neg_injective heq)
  let φ : ((i : S) → C(SpatialCoordinates d, ℝ)) → C(SpatialCoordinates d, ℝ) :=
    fun y => y ⟨idx, by simp [S]⟩
  let ψ : ((i : T) → C(SpatialCoordinates d, ℝ)) →
      C(SpatialCoordinates d, ℝ) × ((j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ)) :=
    fun y => (G (κ y), fun j => y ⟨-(Int.ofNat j), hprefixT j⟩)
  have hφ : Measurable φ := by
    dsimp [φ]
    exact measurable_pi_apply _
  have hpref : Measurable (fun y : (i : T) → C(SpatialCoordinates d, ℝ) =>
      fun j : Fin (N + 1) => y ⟨-(Int.ofNat j), hprefixT j⟩) := by
    apply measurable_pi_lambda
    intro j
    exact measurable_pi_apply _
  have hψ : Measurable ψ := by
    dsimp [ψ]
    exact (hG.comp hκ).prodMk hpref
  have hbase : IndepFun S.restrict T.restrict (Measure.infinitePi laws) :=
    indepFun_restrict_infinitePi laws S T hST
  have hcomp : IndepFun (φ ∘ S.restrict) (ψ ∘ T.restrict)
      (Measure.infinitePi laws) := hbase.comp hφ hψ
  rw [← hmeasure] at hcomp
  have hleft : (φ ∘ S.restrict) =ᵐ[(chaosSampleLaw M).toMeasure]
      (fun omega : BilateralField d => omega idx) := by
    filter_upwards [] with omega
    rfl
  have hright : (ψ ∘ T.restrict) =ᵐ[(chaosSampleLaw M).toMeasure]
      (fun omega : BilateralField d =>
        (H omega, fun j : Fin (N + 1) => omega (-(Int.ofNat j)))) := by
    filter_upwards [hH.2] with omega homega
    have hlim : Tendsto (fun L => infraredPartialSum (κ (T.restrict omega)) L)
        atTop (nhds (H omega)) := by
      have heq : (fun L => infraredPartialSum (κ (T.restrict omega)) L) =
          (fun L => infraredPartialSum omega L) := by
        funext L
        exact hsum_eq omega L
      rw [heq]
      exact homega
    have hgoodκ : κ (T.restrict omega) ∈ good := ⟨H omega, hlim⟩
    have hGeq : G (κ (T.restrict omega)) = H omega := by
      dsimp [G]
      rw [dif_pos hgoodκ]
      exact tendsto_nhds_unique (Classical.choose_spec hgoodκ) hlim
    change (G (κ (T.restrict omega)),
      fun j : Fin (N + 1) => (T.restrict omega) ⟨-(Int.ofNat j), hprefixT j⟩) =
      (H omega, fun j : Fin (N + 1) => omega (-(Int.ofNat j)))
    rw [hGeq]
    rfl
  exact hcomp.congr hleft hright

end SubdiffusiveProcess
