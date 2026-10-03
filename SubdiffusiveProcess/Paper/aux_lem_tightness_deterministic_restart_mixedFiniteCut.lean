module

public import SubdiffusiveProcess.Paper.in_crossing
public import MarkovProcess.Restart.FinitePastRestart
public import MarkovProcess.FiniteTime.ProjectiveFamily
public import MarkovProcess.FiniteTime.KernelMixedPullback
public import MarkovProcess.Kernel.CompProdReindex
public import SubdiffusiveProcess.Main.DiffusionPath

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem aux_lem_tightness_deterministic_restart_mixedFiniteCut
    {alpha : Type*} [TopologicalSpace alpha] [T1Space alpha] [T2Space alpha]
    [MeasurableSpace alpha] [BorelSpace alpha]
    [StandardBorelSpace (ContinuousPath alpha)]
    [MeasurableSpace.CountablySeparated (DenseTime → alpha)]
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (Q : Kernel alpha (ContinuousPath alpha)) [IsMarkovKernel Q]
    (hfd : ∀ U : Finset ℝ≥0,
      Q.map (ContinuousPath.finsetEvaluation U) =
        SubMarkovKernelSemigroup.finiteSetKernel P U)
    (t : ℝ≥0) :
    ∀ I : Finset (Set.Iic t ⊕ DenseTime),
    ∃ Jpast Jfuture : Finset ℝ≥0,
        ∃ ht : t ∈ Jpast,
        ∃ hPast : ∀ r : Set.Iic t, Sum.inl r ∈ I → r.1 ∈ Jpast,
        ∃ hPastExact : ∀ u : ℝ≥0, u ∈ Jpast →
          u = t ∨ ∃ r : Set.Iic t, Sum.inl r ∈ I ∧ r.1 = u,
        ∃ hFuture : ∀ q : DenseTime, Sum.inr q ∈ I → 0 < q →
          DenseTime.castOrderEmbedding q ∈ Jfuture,
        ∃ hFutureExact : ∀ u : ℝ≥0, u ∈ Jfuture → 0 < u ∧
          ∃ q : DenseTime, Sum.inr q ∈ I ∧ 0 < q ∧
            DenseTime.castOrderEmbedding q = u,
    ∃ cutIndex : I → Jpast ⊕ Jfuture,
          ∃ G : ((Jpast → alpha) × (Jfuture → alpha)) → (I → alpha),
            (∀ (i : I),
              match hi : i.1 with
              | Sum.inl r =>
                  cutIndex i = Sum.inl
                    ⟨r.1, hPast r (by simpa [hi] using i.2)⟩
              | Sum.inr q =>
                  if hq : q = 0 then
                    cutIndex i = Sum.inl ⟨t, ht⟩
                  else
                    cutIndex i = Sum.inr
                      ⟨DenseTime.castOrderEmbedding q,
                        hFuture q (by simpa [hi] using i.2)
                          (bot_lt_iff_ne_bot.mpr hq)⟩) ∧
            (∀ z i, G z i = Sum.elim z.1 z.2 (cutIndex i)) ∧
            Measurable G ∧
            (Q.map
              ((I.restrict ∘ Kernel.finitePastDenseFuture
                (index := Set.Iic t) (alpha := alpha)) ∘
                (fun path : ContinuousPath alpha ↦
                  (fun r : Set.Iic t ↦ path (r : ℝ≥0),
                    ContinuousPath.shift t path)))) =
              ((SubMarkovKernelSemigroup.finiteSetKernel P Jpast) ⊗ₖ
                Kernel.prodMkLeft alpha
              ((SubMarkovKernelSemigroup.finiteSetKernel P Jfuture).comap
                    (fun z : Jpast → alpha => z ⟨t, ht⟩)
                    (measurable_pi_apply _))).map G := by
  classical
  intro I
  let A : Finset ℝ≥0 :=
    {t} ∪ I.toLeft.map ⟨fun r : Set.Iic t ↦ r.1, fun _ _ h ↦ Subtype.ext h⟩
  let B : Finset ℝ≥0 :=
    I.toRight.filter (fun q ↦ 0 < q) |>.map DenseTime.castOrderEmbedding.toEmbedding
  have ht : t ∈ A := by simp [A]
  have hPast : ∀ r : Set.Iic t, Sum.inl r ∈ I → r.1 ∈ A := by
    intro r hr
    simp only [A, Finset.mem_union, Finset.mem_singleton, Finset.mem_map]
    right
    exact ⟨r, Finset.mem_toLeft.mpr hr, rfl⟩
  have hPastExact : ∀ u : ℝ≥0, u ∈ A →
      u = t ∨ ∃ r : Set.Iic t, Sum.inl r ∈ I ∧ r.1 = u := by
    intro u hu
    simp only [A, Finset.mem_union, Finset.mem_singleton, Finset.mem_map] at hu
    rcases hu with rfl | ⟨r, hr, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨r, Finset.mem_toLeft.mp hr, rfl⟩
  have hFuture : ∀ q : DenseTime, Sum.inr q ∈ I → 0 < q →
      DenseTime.castOrderEmbedding q ∈ B := by
    intro q hq hqpos
    simp only [B, Finset.mem_map]
    exact ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_toRight.mpr hq, hqpos⟩, rfl⟩
  have hFutureExact : ∀ u : ℝ≥0, u ∈ B → 0 < u ∧
      ∃ q : DenseTime, Sum.inr q ∈ I ∧ 0 < q ∧
        DenseTime.castOrderEmbedding q = u := by
    intro u hu
    simp only [B, Finset.mem_map] at hu
    rcases hu with ⟨q, hq, rfl⟩
    have hpos : 0 < (DenseTime.castOrderEmbedding q : ℝ≥0) := by
      simpa [DenseTime.castOrderEmbedding, NNRat.castOrderEmbedding_apply] using!
        (Finset.mem_filter.mp hq).2
    exact ⟨hpos,
      ⟨q, Finset.mem_toRight.mp (Finset.mem_filter.mp hq).1,
        (Finset.mem_filter.mp hq).2, rfl⟩⟩
  let c : I → A ⊕ B := fun i ↦
    match hi : i.1 with
    | Sum.inl r => Sum.inl ⟨r.1, hPast r (by simpa [hi] using! i.2)⟩
    | Sum.inr q =>
        if hq : q = 0 then
          Sum.inl ⟨t, ht⟩
        else
          Sum.inr ⟨DenseTime.castOrderEmbedding q,
            hFuture q (by simpa [hi] using! i.2) (bot_lt_iff_ne_bot.mpr hq)⟩
  let g : ((A → alpha) × (B → alpha)) → (I → alpha) :=
    fun z i ↦ Sum.elim z.1 z.2 (c i)
  refine ⟨A, B, ht, hPast, hPastExact, hFuture, hFutureExact, c, g, ?_, ?_, ?_, ?_⟩
  · intro i
    rcases i with ⟨i, hiI⟩
    cases i with
    | inl r => rfl
    | inr q =>
        by_cases hq : q = 0 <;> simp [c, hq]
  · intro z i
    rfl
  · rw [measurable_pi_iff]
    intro i
    cases hc : c i with
    | inl a =>
        simpa only [g, hc, Sum.elim_inl] using!
          (measurable_pi_apply a).comp (measurable_fst : Measurable (Prod.fst :
            (A → alpha) × (B → alpha) → (A → alpha)))
    | inr b =>
        simpa only [g, hc, Sum.elim_inr] using!
          (measurable_pi_apply b).comp (measurable_snd : Measurable (Prod.snd :
            (A → alpha) × (B → alpha) → (B → alpha)))
  · let BT : Finset ℝ≥0 := B.map (addLeftEmbedding t)
    let K : Finset ℝ≥0 := A ∪ BT
    have hAle : ∀ a : ℝ≥0, a ∈ A → a ≤ t := by
      intro a ha
      rcases hPastExact a ha with rfl | ⟨r, hr, hra⟩
      · exact le_rfl
      · rw [← hra]
        exact r.2
    have hdis : Disjoint A BT := by
      rw [Finset.disjoint_left]
      intro a ha hBT
      rcases Finset.mem_map.mp hBT with ⟨b, hb, rfl⟩
      have htb : t < t + b := by
        exact lt_add_of_pos_right t (hFutureExact b hb).1
      exact (not_lt_of_ge (hAle _ ha)) htb
    have hKcard : K.card = A.card + B.card := by
      simp only [K, Finset.card_union_of_disjoint hdis, BT, Finset.card_map]
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero
      (Finset.card_ne_zero.mpr ⟨t, ht⟩)
    have htot : B.card + (m + 1) = K.card := by
      omega
    let eSub : ∀ {S T : Finset ℝ≥0}, S ⊆ T → Fin S.card ↪o Fin T.card :=
      fun {S T} hST ↦
        (S.orderIsoOfFin rfl).toOrderEmbedding |>.trans
          (OrderEmbedding.ofStrictMono
            (fun s : S ↦ (⟨s, hST s.property⟩ : T))
            (fun _ _ h ↦ h)) |>.trans
          (T.orderIsoOfFin rfl).symm.toOrderEmbedding
    let eA : Fin A.card ↪o Fin K.card :=
      eSub (Finset.subset_union_left : A ⊆ K)
    let eBT : Fin BT.card ↪o Fin K.card :=
      eSub (Finset.subset_union_right : BT ⊆ K)
    let eB0 : Fin B.card ↪o Fin BT.card :=
      (Fin.castOrderIso (by simp only [BT, Finset.card_map])).toOrderEmbedding
    let eB : Fin B.card ↪o Fin K.card := eB0.trans eBT
    let timesAB : FiniteOrderedTimes (A.card + B.card) :=
      OrderEmbedding.ofStrictMono
        (Fin.addCases (fun a ↦ SubMarkovKernelSemigroup.finiteSetTimes A a)
          (fun b ↦ t + SubMarkovKernelSemigroup.finiteSetTimes B b)) (by
            intro i j hij
            cases i using Fin.addCases with
            | left iA =>
              cases j using Fin.addCases with
              | left jA =>
                simpa only [Fin.addCases_left] using!
                  (SubMarkovKernelSemigroup.finiteSetTimes A).strictMono hij
              | right jB =>
                simpa only [Fin.addCases_left, Fin.addCases_right] using!
                  (lt_of_le_of_lt (hAle _
                    (Finset.orderEmbOfFin_mem A rfl _))
                    (lt_add_of_pos_right t
                      (hFutureExact _ (Finset.orderEmbOfFin_mem B rfl _)).1))
            | right iB =>
              cases j using Fin.addCases with
              | left jA =>
                simp only [Fin.addCases_left, Fin.addCases_right] at hij ⊢
                change A.card + iB.val < jA.val at hij
                exfalso
                omega
              | right jB =>
                have hij' : iB < jB := (Fin.natAdd_lt_natAdd_iff A.card).mp hij
                simpa only [Fin.addCases_right, add_comm] using! add_lt_add_left
                  ((SubMarkovKernelSemigroup.finiteSetTimes B).strictMono hij') t)
    let eK : Fin (B.card + (m + 1)) ↪o Fin K.card :=
      (Fin.castOrderIso htot).toOrderEmbedding
    let times : FiniteOrderedTimes (B.card + (m + 1)) :=
      eK.trans (SubMarkovKernelSemigroup.finiteSetTimes K)
    have htimesABmem : ∀ i : Fin (A.card + B.card), timesAB i ∈ K := by
      intro i
      cases i using Fin.addCases with
      | left iA =>
          rw [show timesAB (Fin.castAdd B.card iA) =
              (SubMarkovKernelSemigroup.finiteSetTimes A) iA by
                simp [timesAB, OrderEmbedding.ofStrictMono, Fin.addCases_left, Fin.addCases_right]]
          exact Finset.mem_union_left BT
            (Finset.orderEmbOfFin_mem A rfl iA)
      | right iB =>
          rw [show timesAB (Fin.natAdd A.card iB) =
              t + (SubMarkovKernelSemigroup.finiteSetTimes B) iB by
                simp [timesAB, OrderEmbedding.ofStrictMono, Fin.addCases_left, Fin.addCases_right]]
          exact Finset.mem_union_right A
            (Finset.mem_map_of_mem (addLeftEmbedding t)
              (Finset.orderEmbOfFin_mem B rfl iB))
    have hab : B.card + (m + 1) = A.card + B.card := by
      omega
    let eAB : Fin (B.card + (m + 1)) ↪o Fin (A.card + B.card) :=
      (Fin.castOrderIso hab).toOrderEmbedding
    let timesABm : FiniteOrderedTimes (B.card + (m + 1)) := eAB.trans timesAB
    have htimes_order : times = K.orderEmbOfFin htot.symm := by
      have h := Finset.orderEmbOfFin_unique (s := K) htot.symm
        (f := times)
        (by intro i; exact Finset.orderEmbOfFin_mem K rfl (eK i))
        ((SubMarkovKernelSemigroup.finiteSetTimes K).strictMono.comp eK.strictMono)
      exact DFunLike.ext _ _ (fun i ↦ congrFun h i)
    have htimesABm_order : timesABm = K.orderEmbOfFin htot.symm := by
      have h := Finset.orderEmbOfFin_unique (s := K) htot.symm
        (f := timesABm) (by intro i; exact htimesABmem (eAB i))
        (timesAB.strictMono.comp eAB.strictMono)
      exact DFunLike.ext _ _ (fun i ↦ congrFun h i)
    have htimes : times = timesABm := htimes_order.trans htimesABm_order.symm
    have hm' : A.card = m + 1 := by
      simpa only [Nat.succ_eq_add_one] using! hm
    let pastIndex : A → Fin (m + 1) := fun a ↦
      Fin.cast hm' ((A.orderIsoOfFin rfl).symm a)
    let castA : Fin (m + 1) ↪o Fin A.card :=
      (Fin.castOrderIso hm'.symm).toOrderEmbedding
    let timesA : FiniteOrderedTimes (m + 1) :=
      castA.trans (SubMarkovKernelSemigroup.finiteSetTimes A)
    let futureIndex : B → Fin B.card := fun b ↦
      (B.orderIsoOfFin rfl).symm b
    let futureOpt : B → Option (Fin B.card) := fun b ↦ some (futureIndex b)
    have hinit : FiniteOrderedTimes.initialSegment times = timesA := by
      rw [htimes]
      apply DFunLike.ext _ _
      intro i
      change timesABm
          (cutIndexOrderIso m B.card (Fin.castAdd B.card i)) = timesA i
      have hidx : eAB (cutIndexOrderIso m B.card (Fin.castAdd B.card i)) =
          Fin.castAdd B.card (castA i) := by
        apply Fin.ext
        simp [eAB, castA, cutIndexOrderIso]
      change timesAB (eAB (cutIndexOrderIso m B.card (Fin.castAdd B.card i))) =
        timesA i
      rw [hidx]
      simp [timesAB, OrderEmbedding.ofStrictMono, timesA, castA]
    have hlastIndex :
        (A.orderIsoOfFin rfl).symm (⟨t, ht⟩ : A) = castA (Fin.last m) := by
      have hle : ∀ k : Fin A.card,
          k ≤ (A.orderIsoOfFin rfl).symm (⟨t, ht⟩ : A) := by
        intro k
        apply (A.orderIsoOfFin rfl).le_iff_le.mp
        simpa only [OrderIso.apply_symm_apply] using!
          (hAle _ (Finset.orderEmbOfFin_mem A rfl k))
      apply Fin.ext
      have hle' := hle (castA (Fin.last m))
      have hleval := (Fin.le_iff_val_le_val.mp hle')
      have hcast : (castA (Fin.last m)).val = m := by
        rfl
      have hcard := hm'
      omega
    have hAtLast : timesA (Fin.last m) = t := by
      change (SubMarkovKernelSemigroup.finiteSetTimes A) (castA (Fin.last m)) = t
      rw [show castA (Fin.last m) =
          (A.orderIsoOfFin rfl).symm (⟨t, ht⟩ : A) by exact hlastIndex.symm]
      change ((A.orderIsoOfFin rfl)
        ((A.orderIsoOfFin rfl).symm (⟨t, ht⟩ : A)) : ℝ≥0) = t
      rw [OrderIso.apply_symm_apply]
    have hrel : FiniteOrderedTimes.relativeFinalSegment times =
        SubMarkovKernelSemigroup.finiteSetTimes B := by
      rw [htimes]
      apply DFunLike.ext _ _
      intro j
      change timesAB
          (eAB (cutIndexOrderIso m B.card
            (Fin.natAdd (m + 1) j))) -
          timesAB (eAB (cutIndexOrderIso m B.card
            (Fin.castAdd B.card (Fin.last m)))) =
        (SubMarkovKernelSemigroup.finiteSetTimes B) j
      have hidxF : eAB (cutIndexOrderIso m B.card
            (Fin.natAdd (m + 1) j)) = Fin.natAdd A.card j := by
        apply Fin.ext
        simp [eAB, cutIndexOrderIso, hm', Nat.add_comm]
      have hidxC : eAB (cutIndexOrderIso m B.card
            (Fin.castAdd B.card (Fin.last m))) = Fin.castAdd B.card (castA (Fin.last m)) := by
        apply Fin.ext
        simp [eAB, castA, cutIndexOrderIso]
      rw [hidxF, hidxC]
      have hAcut : (SubMarkovKernelSemigroup.finiteSetTimes A)
          (castA (Fin.last m)) = t := by
        simpa only [timesA] using! hAtLast
      rw [show timesAB (Fin.natAdd A.card j) =
          t + (SubMarkovKernelSemigroup.finiteSetTimes B) j by
            simp [timesAB, OrderEmbedding.ofStrictMono, Fin.addCases_left, Fin.addCases_right]]
      rw [show timesAB (Fin.castAdd B.card (castA (Fin.last m))) =
          (SubMarkovKernelSemigroup.finiteSetTimes A) (castA (Fin.last m)) by
            simp [timesAB, OrderEmbedding.ofStrictMono, Fin.addCases_left, Fin.addCases_right]]
      rw [hAcut]
      exact add_tsub_cancel_left t _
    let pK : A → K := fun a ↦
      ⟨a, Finset.mem_union_left BT a.property⟩
    let fK : B → K := fun b ↦
      ⟨t + b, Finset.mem_union_right A
        (Finset.mem_map_of_mem (addLeftEmbedding t) b.property)⟩
    let rp : (Fin (m + 1) → alpha) → (A → alpha) := fun path a ↦
      path (pastIndex a)
    let rf : (Fin B.card → alpha) → (B → alpha) := fun path b ↦
      path (futureIndex b)
    let last : (Fin (m + 1) → alpha) → alpha := fun path ↦
      path (Fin.last m)
    let terminalA : (A → alpha) → alpha := fun path ↦ path ⟨t, ht⟩
    let splitK : (K → alpha) → (A → alpha) × (B → alpha) := fun path ↦
      (fun a ↦ path (pK a), fun b ↦ path (fK b))
    let splitAB : (Fin (B.card + (m + 1)) → alpha) →
        (A → alpha) × (B → alpha) :=
      fun path ↦
        (rp (SubMarkovKernelSemigroup.splitFinitePath path).1,
          rf (SubMarkovKernelSemigroup.splitFinitePath path).2)
    have hsplitK : Measurable splitK := by
      apply Measurable.prodMk
      · rw [measurable_pi_iff]
        intro a
        exact measurable_pi_apply (pK a)
      · rw [measurable_pi_iff]
        intro b
        exact measurable_pi_apply (fK b)
    have hsplitAB : Measurable splitAB := by
      apply Measurable.prodMk
      · rw [measurable_pi_iff]
        intro a
        exact (measurable_pi_apply (pastIndex a)).comp
          (SubMarkovKernelSemigroup.measurable_splitFinitePath |> Measurable.fst)
      · rw [measurable_pi_iff]
        intro b
        exact (measurable_pi_apply (futureIndex b)).comp
          (SubMarkovKernelSemigroup.measurable_splitFinitePath |> Measurable.snd)
    have hrp : Measurable rp := by
      rw [measurable_pi_iff]
      intro a
      exact measurable_pi_apply (pastIndex a)
    have hrf : Measurable rf := by
      rw [measurable_pi_iff]
      intro b
      exact measurable_pi_apply (futureIndex b)
    have hlast : Measurable last := measurable_pi_apply _
    have hterminalA : Measurable terminalA := measurable_pi_apply _
    have hcastPast : ∀ a : A, castA (pastIndex a) =
        (A.orderIsoOfFin rfl).symm a := by
      intro a
      apply Fin.ext
      simp [castA, pastIndex]
    have hPastIdx : ∀ a : A,
        eK (cutIndexOrderIso m B.card (Fin.castAdd B.card (pastIndex a))) =
          (K.orderIsoOfFin rfl).symm (pK a) := by
      intro a
      apply (SubMarkovKernelSemigroup.finiteSetTimes K).injective
      calc
        (SubMarkovKernelSemigroup.finiteSetTimes K)
            (eK (cutIndexOrderIso m B.card
              (Fin.castAdd B.card (pastIndex a)))) =
            times (cutIndexOrderIso m B.card
              (Fin.castAdd B.card (pastIndex a))) := rfl
        _ = FiniteOrderedTimes.initialSegment times (pastIndex a) := rfl
        _ = timesA (pastIndex a) := by rw [hinit]
        _ = (SubMarkovKernelSemigroup.finiteSetTimes A)
              (castA (pastIndex a)) := rfl
        _ = (a : ℝ≥0) := by
          rw [hcastPast a]
          simpa only [SubMarkovKernelSemigroup.finiteSetTimes] using!
            (congrArg Subtype.val
              (OrderIso.apply_symm_apply (A.orderIsoOfFin rfl) a))
        _ = (pK a : ℝ≥0) := rfl
        _ = (SubMarkovKernelSemigroup.finiteSetTimes K)
              ((K.orderIsoOfFin rfl).symm (pK a)) := by
          symm
          simpa only [SubMarkovKernelSemigroup.finiteSetTimes] using!
            (congrArg Subtype.val
              (OrderIso.apply_symm_apply (K.orderIsoOfFin rfl) (pK a)))
    have htermIndex : pastIndex ⟨t, ht⟩ = Fin.last m := by
      apply castA.injective
      rw [hcastPast, hlastIndex]
    have hcompat : terminalA ∘ rp = last := by
      funext path
      change path (pastIndex ⟨t, ht⟩) = path (Fin.last m)
      rw [htermIndex]
    have hcut : times (cutIndexOrderIso m B.card
          (Fin.castAdd B.card (Fin.last m))) = t := by
      calc
        times (cutIndexOrderIso m B.card
            (Fin.castAdd B.card (Fin.last m))) =
            FiniteOrderedTimes.initialSegment times (Fin.last m) := rfl
        _ = timesA (Fin.last m) := by rw [hinit]
        _ = t := hAtLast
    have hFutureIdx : ∀ b : B,
        eK (cutIndexOrderIso m B.card
          (Fin.natAdd (m + 1) (futureIndex b))) =
          (K.orderIsoOfFin rfl).symm (fK b) := by
      intro b
      apply (SubMarkovKernelSemigroup.finiteSetTimes K).injective
      have hidx : cutIndexOrderIso m B.card
          (Fin.castAdd B.card (Fin.last m)) ≤
          cutIndexOrderIso m B.card
            (Fin.natAdd (m + 1) (futureIndex b)) := by
        apply (cutIndexOrderIso m B.card).monotone
        apply Fin.mk_le_mk.mpr
        change m ≤ m + 1 + (futureIndex b).val
        omega
      have htime : times (cutIndexOrderIso m B.card
          (Fin.natAdd (m + 1) (futureIndex b))) =
          (SubMarkovKernelSemigroup.finiteSetTimes B) (futureIndex b) +
            times (cutIndexOrderIso m B.card
              (Fin.castAdd B.card (Fin.last m))) := by
        apply (tsub_eq_iff_eq_add_of_le (times.monotone hidx)).mp
        rw [← hrel]
        rfl
      calc
        (SubMarkovKernelSemigroup.finiteSetTimes K)
            (eK (cutIndexOrderIso m B.card
              (Fin.natAdd (m + 1) (futureIndex b)))) =
            times (cutIndexOrderIso m B.card
              (Fin.natAdd (m + 1) (futureIndex b))) := rfl
        _ = (SubMarkovKernelSemigroup.finiteSetTimes B) (futureIndex b) + t := by
          rw [htime, hcut]
        _ = (fK b : ℝ≥0) := by
          change (SubMarkovKernelSemigroup.finiteSetTimes B) (futureIndex b) + t = t + b
          have hB : (SubMarkovKernelSemigroup.finiteSetTimes B)
              (futureIndex b) = b := by
            simp only [futureIndex, SubMarkovKernelSemigroup.finiteSetTimes]
            exact congrArg Subtype.val
              (OrderIso.apply_symm_apply (B.orderIsoOfFin rfl) b)
          rw [hB]
          exact add_comm _ _
        _ = (SubMarkovKernelSemigroup.finiteSetTimes K)
              ((K.orderIsoOfFin rfl).symm (fK b)) := by
          symm
          simpa only [SubMarkovKernelSemigroup.finiteSetTimes] using!
            (congrArg Subtype.val
              (OrderIso.apply_symm_apply (K.orderIsoOfFin rfl) (fK b)))
    have hcoords :
        splitK ∘ SubMarkovKernelSemigroup.orderedPathToFiniteSet K =
          splitAB ∘ FiniteOrderedTimes.restrictPath eK := by
      funext path
      apply Prod.ext
      · funext a
        change path ((K.orderIsoOfFin rfl).symm (pK a)) =
          path (eK (cutIndexOrderIso m B.card
            (Fin.castAdd B.card (pastIndex a))))
        rw [hPastIdx a]
      · funext b
        change path ((K.orderIsoOfFin rfl).symm (fK b)) =
          path (eK (cutIndexOrderIso m B.card
            (Fin.natAdd (m + 1) (futureIndex b))))
        rw [hFutureIdx b]
    have hAmap :
        (SubMarkovKernelSemigroup.finiteTimeKernel P timesA).map rp =
          SubMarkovKernelSemigroup.finiteSetKernel P A := by
      rw [SubMarkovKernelSemigroup.finiteSetKernel_eq_map]
      have hrestrict := hP.finiteTimeKernel_map_restrictPath P
        (SubMarkovKernelSemigroup.finiteSetTimes A) castA
      have hcompA : rp ∘ FiniteOrderedTimes.restrictPath castA =
          SubMarkovKernelSemigroup.orderedPathToFiniteSet A := by
        funext path a
        change path (castA (pastIndex a)) =
          path ((A.orderIsoOfFin rfl).symm a)
        rw [hcastPast a]
      calc
        (SubMarkovKernelSemigroup.finiteTimeKernel P timesA).map rp =
            ((SubMarkovKernelSemigroup.finiteTimeKernel P
              (SubMarkovKernelSemigroup.finiteSetTimes A)).map
              (FiniteOrderedTimes.restrictPath castA)).map rp := by
                change (SubMarkovKernelSemigroup.finiteTimeKernel P
                  ((SubMarkovKernelSemigroup.finiteSetTimes A).restrict castA)).map rp =
                  ((SubMarkovKernelSemigroup.finiteTimeKernel P
                    (SubMarkovKernelSemigroup.finiteSetTimes A)).map
                    (FiniteOrderedTimes.restrictPath castA)).map rp
                rw [hrestrict]
        _ = (SubMarkovKernelSemigroup.finiteTimeKernel P
              (SubMarkovKernelSemigroup.finiteSetTimes A)).map
              (rp ∘ FiniteOrderedTimes.restrictPath castA) := by
                exact (Kernel.map_comp_right _
                  (FiniteOrderedTimes.measurable_restrictPath castA) hrp).symm
        _ = (SubMarkovKernelSemigroup.finiteTimeKernel P
              (SubMarkovKernelSemigroup.finiteSetTimes A)).map
              (SubMarkovKernelSemigroup.orderedPathToFiniteSet A) := by
                rw [hcompA]
    have hBmap :
        (SubMarkovKernelSemigroup.finiteTimeKernel P
          (SubMarkovKernelSemigroup.finiteSetTimes B)).map rf =
          SubMarkovKernelSemigroup.finiteSetKernel P B := by
      rw [SubMarkovKernelSemigroup.finiteSetKernel_eq_map]
      congr 1
    letI : IsMarkovKernel
        (SubMarkovKernelSemigroup.finiteTimeKernel P timesA) :=
      hP.isMarkovKernel_finiteTimeKernel P timesA
    letI : IsMarkovKernel
        (SubMarkovKernelSemigroup.finiteTimeKernel P
          (SubMarkovKernelSemigroup.finiteSetTimes B)) :=
      hP.isMarkovKernel_finiteTimeKernel P
        (SubMarkovKernelSemigroup.finiteSetTimes B)
    have hfactor :
        (SubMarkovKernelSemigroup.finiteTimeKernel P times).map splitAB =
          ((SubMarkovKernelSemigroup.finiteTimeKernel P timesA) ⊗ₖ
            Kernel.prodMkLeft alpha
              ((SubMarkovKernelSemigroup.finiteTimeKernel P
                (SubMarkovKernelSemigroup.finiteSetTimes B)).comap last hlast)).map
            (Prod.map rp rf) := by
      calc
        (SubMarkovKernelSemigroup.finiteTimeKernel P times).map splitAB =
            ((SubMarkovKernelSemigroup.finiteTimeKernel P times).map
              (SubMarkovKernelSemigroup.splitFinitePath
                (alpha := alpha) (m := m) (n := B.card))).map
              (Prod.map rp rf) := by
                simpa [splitAB] using!
                  (Kernel.map_comp_right _
                    SubMarkovKernelSemigroup.measurable_splitFinitePath
                    (hrp.prodMap hrf))
        _ = ((SubMarkovKernelSemigroup.finiteTimeKernel P
              (FiniteOrderedTimes.initialSegment times)) ⊗ₖ
              ((SubMarkovKernelSemigroup.finiteTimeKernel P
                  (FiniteOrderedTimes.relativeFinalSegment times)).comap
                (SubMarkovKernelSemigroup.splitPastTerminal
                  (alpha := alpha) (m := m))
                SubMarkovKernelSemigroup.measurable_splitPastTerminal)).map
              (Prod.map rp rf) := by
                rw [hP.finiteTimeKernel_map_splitFinitePath P m B.card times]
        _ = ((SubMarkovKernelSemigroup.finiteTimeKernel P timesA) ⊗ₖ
              Kernel.prodMkLeft alpha
                ((SubMarkovKernelSemigroup.finiteTimeKernel P
                  (SubMarkovKernelSemigroup.finiteSetTimes B)).comap last hlast)).map
              (Prod.map rp rf) := by
                rw [hinit, hrel]
                change ((SubMarkovKernelSemigroup.finiteTimeKernel P timesA) ⊗ₖ
                  Kernel.prodMkLeft alpha
                    ((SubMarkovKernelSemigroup.finiteTimeKernel P
                      (SubMarkovKernelSemigroup.finiteSetTimes B)).comap last hlast)).map
                  (Prod.map rp rf) = _
                rfl
    have hfinite :
        (SubMarkovKernelSemigroup.finiteSetKernel P K).map splitK =
          (SubMarkovKernelSemigroup.finiteSetKernel P A ⊗ₖ
            Kernel.prodMkLeft alpha
              ((SubMarkovKernelSemigroup.finiteSetKernel P B).comap
                terminalA hterminalA)) := by
      rw [SubMarkovKernelSemigroup.finiteSetKernel_eq_map]
      calc
        ((SubMarkovKernelSemigroup.finiteTimeKernel P
            (SubMarkovKernelSemigroup.finiteSetTimes K)).map
          (SubMarkovKernelSemigroup.orderedPathToFiniteSet K)).map splitK =
            (SubMarkovKernelSemigroup.finiteTimeKernel P
              (SubMarkovKernelSemigroup.finiteSetTimes K)).map
              (splitK ∘ SubMarkovKernelSemigroup.orderedPathToFiniteSet K) := by
                exact (Kernel.map_comp_right _
                  (SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet K)
                  hsplitK).symm
        _ = (SubMarkovKernelSemigroup.finiteTimeKernel P
              (SubMarkovKernelSemigroup.finiteSetTimes K)).map
              (splitAB ∘ FiniteOrderedTimes.restrictPath eK) := by
                rw [hcoords]
        _ = ((SubMarkovKernelSemigroup.finiteTimeKernel P
              (SubMarkovKernelSemigroup.finiteSetTimes K)).map
              (FiniteOrderedTimes.restrictPath eK)).map splitAB := by
                exact Kernel.map_comp_right _
                  (FiniteOrderedTimes.measurable_restrictPath eK) hsplitAB
        _ = (SubMarkovKernelSemigroup.finiteTimeKernel P times).map splitAB := by
                rw [hP.finiteTimeKernel_map_restrictPath P
                  (SubMarkovKernelSemigroup.finiteSetTimes K) eK]
                rfl
        _ = ((SubMarkovKernelSemigroup.finiteTimeKernel P timesA) ⊗ₖ
              Kernel.prodMkLeft alpha
                ((SubMarkovKernelSemigroup.finiteTimeKernel P
                  (SubMarkovKernelSemigroup.finiteSetTimes B)).comap last hlast)).map
              (Prod.map rp rf) := hfactor
        _ = ((SubMarkovKernelSemigroup.finiteTimeKernel P timesA).map rp ⊗ₖ
              Kernel.prodMkLeft alpha
                (((SubMarkovKernelSemigroup.finiteTimeKernel P
                  (SubMarkovKernelSemigroup.finiteSetTimes B)).map rf).comap
                    terminalA hterminalA)) := by
                exact Kernel.map_compProd_prodMkLeft_comap
                  _ _ last terminalA hterminalA rp hrp rf hrf hcompat
        _ = (SubMarkovKernelSemigroup.finiteSetKernel P A ⊗ₖ
              Kernel.prodMkLeft alpha
                ((SubMarkovKernelSemigroup.finiteSetKernel P B).comap
                  terminalA hterminalA)) := by
                rw [hAmap, hBmap]
    let H : ContinuousPath alpha →
        ((A → alpha) × (B → alpha)) :=
      splitK ∘ ContinuousPath.finsetEvaluation K
    have hH : Measurable H := by
      dsimp [H]
      exact hsplitK.comp (ContinuousPath.measurable_finsetEvaluation K)
    have hQ :
        Q.map H =
          (SubMarkovKernelSemigroup.finiteSetKernel P A ⊗ₖ
            Kernel.prodMkLeft alpha
              ((SubMarkovKernelSemigroup.finiteSetKernel P B).comap
                terminalA hterminalA)) := by
      calc
        Q.map H =
            (Q.map (ContinuousPath.finsetEvaluation K)).map splitK := by
              change Q.map (splitK ∘ ContinuousPath.finsetEvaluation K) = _
              exact Kernel.map_comp_right Q
                (ContinuousPath.measurable_finsetEvaluation K) hsplitK
        _ = (SubMarkovKernelSemigroup.finiteSetKernel P K).map splitK := by
              rw [hfd K]
        _ = _ := hfinite
    have hpoint :
        ((I.restrict ∘ Kernel.finitePastDenseFuture
            (index := Set.Iic t) (alpha := alpha)) ∘
          (fun path : ContinuousPath alpha ↦
            (fun r : Set.Iic t ↦ path (r : ℝ≥0),
              ContinuousPath.shift t path))) = g ∘ H := by
      funext path
      funext i
      rcases i with ⟨i, hi⟩
      rcases i with r | q
      · simp [H, g, c, Function.comp_apply, Kernel.finitePastDenseFuture,
          splitK, pK, ContinuousPath.finsetEvaluation,
          ContinuousPath.finiteEvaluation]
      · by_cases hq : q = 0
        · subst q
          simp [H, g, c, Function.comp_apply, Kernel.finitePastDenseFuture,
            splitK, pK, fK, ContinuousPath.finsetEvaluation,
            ContinuousPath.finiteEvaluation,
            ContinuousPath.denseRestriction_apply, ContinuousPath.shift_apply,
            DenseTime.castOrderEmbedding, NNRat.castOrderEmbedding_apply]
        · simp [H, g, c, Function.comp_apply, Kernel.finitePastDenseFuture,
            splitK, pK, fK, ContinuousPath.finsetEvaluation, hq,
            ContinuousPath.finiteEvaluation,
            ContinuousPath.denseRestriction_apply, ContinuousPath.shift_apply]
    have hg : Measurable g := by
      rw [measurable_pi_iff]
      intro i
      cases hc : c i with
      | inl a =>
          simpa only [g, hc, Sum.elim_inl] using!
            (measurable_pi_apply a).comp (measurable_fst : Measurable (Prod.fst :
              (A → alpha) × (B → alpha) → (A → alpha)))
      | inr b =>
          simpa only [g, hc, Sum.elim_inr] using!
            (measurable_pi_apply b).comp (measurable_snd : Measurable (Prod.snd :
              (A → alpha) × (B → alpha) → (B → alpha)))
    calc
      Q.map ((I.restrict ∘ Kernel.finitePastDenseFuture
          (index := Set.Iic t) (alpha := alpha)) ∘
        (fun path : ContinuousPath alpha ↦
          (fun r : Set.Iic t ↦ path (r : ℝ≥0),
            ContinuousPath.shift t path))) = Q.map (g ∘ H) := by
              rw [hpoint]
      _ = (Q.map H).map g := by
              exact Kernel.map_comp_right Q hH hg
      _ = (SubMarkovKernelSemigroup.finiteSetKernel P A ⊗ₖ
            Kernel.prodMkLeft alpha
              ((SubMarkovKernelSemigroup.finiteSetKernel P B).comap
                (fun z : A → alpha => z ⟨t, ht⟩)
                (measurable_pi_apply _))).map g := by
              rw [hQ]

end Paper
