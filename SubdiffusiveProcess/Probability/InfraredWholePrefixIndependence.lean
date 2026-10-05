module

public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Probability.LayerProductBlocks
public import SubdiffusiveProcess.Probability.InfraredFineIndependence
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Topology.Metrizable.ContinuousMap

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess

theorem infraredCharacterization_indepFun_H_finePrefix
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ)
    (hH : InfraredCharacterization M H) :
    IndepFun H
      (fun omega : BilateralField d => fun j : Fin (N + 1) => omega (-(Int.ofNat j)))
      (chaosSampleLaw M).toMeasure := by
  classical
  let laws : (j : ℤ) → Measure C(SpatialCoordinates d, ℝ) :=
    fun j => (scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure
  have hmeasure : (chaosSampleLaw M).toMeasure = Measure.infinitePi laws := by
    rfl
  let S : Set ℤ := {i : ℤ | i ≤ 0}
  let T : Set ℤ := Sᶜ
  have hST : Disjoint S T := by
    exact disjoint_compl_right
  have hpartial : ∀ L : ℕ, Measurable (fun omega : BilateralField d =>
      infraredPartialSum omega L) := by
    intro L
    unfold infraredPartialSum
    apply Continuous.measurable
    apply continuous_finsetSum
    intro n hn
    have hcoord : Continuous (fun beta : BilateralField d =>
        beta (Int.ofNat (n + 1))) := continuous_apply (Int.ofNat (n + 1))
    have heval0 : Continuous (fun f : C(SpatialCoordinates d, ℝ) => f 0) :=
      continuous_eval_const 0
    have hc : Continuous (fun beta : BilateralField d =>
        ContinuousMap.const (SpatialCoordinates d) ((beta (Int.ofNat (n + 1))) 0)) := by
      simpa [ContinuousMap.constPi, Function.comp_def] using!
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
  let : TopologicalSpace.MetrizableSpace C(SpatialCoordinates d, ℝ) := inferInstance
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
    · simpa only [Gseq, G, dite_eq_left hbeta] using! Classical.choose_spec hbeta
    · simp only [Gseq, G, dite_eq_right hbeta]
      exact tendsto_const_nhds
  have hG : Measurable G := by
    exact measurable_of_tendsto_metrizable hGseq hGlim
  let κ : ((j : T) → C(SpatialCoordinates d, ℝ)) → BilateralField d :=
    fun y i => if hi : i ∈ T then y ⟨i, hi⟩ else 0
  have hκ : Measurable κ := by
    apply Measurable.of_eval
    intro i
    by_cases hi : i ∈ T
    · have heval : Measurable (fun y : (j : T) → C(SpatialCoordinates d, ℝ) =>
          y ⟨i, hi⟩) := measurable_pi_apply _
      simpa only [κ, dite_eq_left hi] using! heval
    · simp only [κ, dite_eq_right hi]
      exact measurable_const
  have hκpos (omega : BilateralField d) (i : ℤ) (hi : 0 < i) :
      κ (T.domRestrict omega) i = omega i := by
    have hiT : i ∈ T := by
      simp only [T, S, Set.mem_compl_iff]
      exact not_le.mpr hi
    simp only [κ, dite_eq_left hiT]
    rfl
  have hsum_eq (omega : BilateralField d) (L : ℕ) :
      infraredPartialSum (κ (T.domRestrict omega)) L = infraredPartialSum omega L := by
    unfold infraredPartialSum
    apply Finset.sum_congr rfl
    intro n hn
    have hnpos : 0 < Int.ofNat (n + 1) := by
      have hn' : 0 < n + 1 := Nat.zero_lt_succ n
      exact Int.natCast_pos.mpr hn'
    simp only [hκpos omega (Int.ofNat (n + 1)) hnpos]
  have hprefixS (j : Fin (N + 1)) : -(Int.ofNat j) ∈ S := by
    simp only [S]
    exact neg_nonpos.mpr (Int.natCast_nonneg _)
  let φ : ((i : S) → C(SpatialCoordinates d, ℝ)) →
      (j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ) :=
    fun y j => y ⟨-(Int.ofNat j), hprefixS j⟩
  let ψ : ((i : T) → C(SpatialCoordinates d, ℝ)) →
      C(SpatialCoordinates d, ℝ) := fun y => G (κ y)
  have hφ : Measurable φ := by
    apply Measurable.of_eval
    intro j
    exact measurable_pi_apply _
  have hψ : Measurable ψ := by
    dsimp [ψ]
    exact hG.comp hκ
  have hbase : IndepFun S.domRestrict T.domRestrict (Measure.infinitePi laws) :=
    indepFun_restrict_infinitePi laws S T hST
  have hcomp : IndepFun (ψ ∘ T.domRestrict) (φ ∘ S.domRestrict)
      (Measure.infinitePi laws) := hbase.symm.comp hψ hφ
  rw [← hmeasure] at hcomp
  have hleft : (φ ∘ S.domRestrict) =ᵐ[(chaosSampleLaw M).toMeasure]
      (fun omega : BilateralField d => fun j : Fin (N + 1) =>
        omega (-(Int.ofNat j))) := by
    filter_upwards [] with omega
    funext j
    rfl
  have hright : (ψ ∘ T.domRestrict) =ᵐ[(chaosSampleLaw M).toMeasure] H := by
    filter_upwards [hH.2] with omega homega
    have hlim : Tendsto (fun L => infraredPartialSum (κ (T.domRestrict omega)) L)
        atTop (nhds (H omega)) := by
      have heq : (fun L => infraredPartialSum (κ (T.domRestrict omega)) L) =
          (fun L => infraredPartialSum omega L) := by
        funext L
        exact hsum_eq omega L
      rw [heq]
      exact homega
    have hgoodκ : κ (T.domRestrict omega) ∈ good := ⟨H omega, hlim⟩
    have hGeq : G (κ (T.domRestrict omega)) = H omega := by
      dsimp [G]
      rw [dite_eq_left hgoodκ]
      exact tendsto_nhds_unique (Classical.choose_spec hgoodκ) hlim
    exact hGeq
  exact hcomp.congr hright hleft

end SubdiffusiveProcess
