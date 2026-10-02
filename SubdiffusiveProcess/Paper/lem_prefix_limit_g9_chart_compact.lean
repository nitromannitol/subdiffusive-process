import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Main.ChaosSampleLaw
import Homogenization.Book.Ch02.Matrices
import SubdiffusiveProcess.Paper.lem_prefix_limit_g9_unit_chart_compact
import SubdiffusiveProcess.Main.ChaosRootFieldLaw
import SubdiffusiveProcess.Main.ScaledLayerLaw
import SubdiffusiveProcess.Main.LayerScaling
import SubdiffusiveProcess.Main.CommonScaleLaw
import SubdiffusiveProcess.Main.InfraredPartialSum
import SubdiffusiveProcess.Probability.GMCFieldLaws
import SubdiffusiveProcess.Lane4.CubeDilation
import SubdiffusiveProcess.Lane4.Bridge
import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.Tactic
import SubdiffusiveProcess.Paper.lem_prefix_limit_g9_chart_transport


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology

noncomputable section
namespace Paper

theorem aux_lem_prefix_limit_g9_chart_compact_pullback_compact
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Ω → Ω) (hS : MeasurePreserving S μ μ)
    (f : ℕ → Ω → ℝ) (hfm : ∀ n, MemLp (f n) 1 μ)
    (hfc : IsCompact (closure (Set.range fun n => (hfm n).toLp (f n))))
    (g : ℕ → Ω → ℝ) (hgm : ∀ n, MemLp (g n) 1 μ)
    (index : ℕ → Option ℕ)
    (hrel : ∀ n, g n =ᵐ[μ] fun omega =>
      match index n with
      | none => 0
      | some k => f k (S omega)) :
    IsCompact (closure (Set.range fun n => (hgm n).toLp (g n))) := by
  let pull : Lp ℝ 1 μ → Lp ℝ 1 μ := Lp.compMeasurePreserving S hS
  have hpull : Isometry pull := Lp.isometry_compMeasurePreserving hS
  let K : Set (Lp ℝ 1 μ) := closure (Set.range fun n => (hfm n).toLp (f n))
  have hK : IsCompact K := hfc
  have hpullK : IsCompact (pull '' K) := hK.image hpull.continuous
  have hC : IsCompact (pull '' K ∪ ({0} : Set (Lp ℝ 1 μ))) :=
    hpullK.union isCompact_singleton
  refine hC.of_isClosed_subset isClosed_closure ?_
  refine closure_minimal ?_ hC.isClosed
  rintro _ ⟨n, rfl⟩
  cases hi : index n with
  | none =>
      have heq : (hgm n).toLp (g n) = (MemLp.zero : MemLp (0 : Ω → ℝ) 1 μ).toLp 0 :=
        MemLp.toLp_congr (hgm n) MemLp.zero (by simpa [hi] using hrel n)
      rw [MemLp.toLp_zero] at heq
      exact Set.mem_union_right _ (by simpa [heq])
  | some k =>
      have heq : (hgm n).toLp (g n) =
          ((hfm k).comp_measurePreserving hS).toLp (fun omega => f k (S omega)) :=
        MemLp.toLp_congr (hgm n) ((hfm k).comp_measurePreserving hS) (by
          simpa [hi] using hrel n)
      have heq' : (hgm n).toLp (g n) = pull ((hfm k).toLp (f k)) := by
        change (hgm n).toLp (g n) =
          Lp.compMeasurePreserving S hS ((hfm k).toLp (f k))
        exact heq.trans (Lp.toLp_compMeasurePreserving (hfm k) hS).symm
      exact Set.mem_union_left _ ⟨(hfm k).toLp (f k),
        subset_closure ⟨k, rfl⟩, heq'.symm⟩



theorem lem_prefix_limit_g9_chart_compact {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (_Poincare : Paper.in_poincare d hd I)
    (_Extension : Paper.in_extension d hd I) (_Perturbation : Lane4.SmallPerturbationInput d)
    (_Sobolev : Lane4.SobolevFoundationalInput d hd)
    (D : Paper.lane4_deterministic_good_scale_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp) (sigma s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : Paper.in_6_16 d M) (_It : Paper.in_iteration d M I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ (sidePos : ∀ n : ℤ, 0 < (3 : ℝ) ^ (-n)) (nn mm : ℤ) (z w : SpatialCoordinates d),
      let kappa : ℕ → ℝ := fun J =>
        Real.exp (((J : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) * ahom M J
      let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
        fun n zz omega => if 0 ≤ n then ∑ j ∈ Finset.Ico (0 : ℤ) n, omega (-j) zz
          else -∑ j ∈ Finset.Ico n (0 : ℤ), omega (-j) zz
      let reference : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
        fun N n zz omega => kappa ((N : ℤ) - n).toNat / kappa N *
          Real.exp (H omega zz + retained n zz omega)
      let ellVal : ℕ → BilateralField d → Fin 3 ⊕ ((Bool × (Fin d × Fin d)) ⊕ Fin 2) → ℝ :=
        fun N omega rt =>
          let aN := Lane4.cutoffPositiveCoefficient M H omega N w (sidePos mm)
          let r := (3 : ℝ) ^ (-mm)
          let ref := reference N mm w omega
          if nn ≤ (N : ℤ) ∧ mm ≤ (N : ℤ) then
            Sum.elim
              (fun j => if j = 0 then I.lam w r (sidePos mm) aN w r sigma 2 / ref
                else if j = 1 then I.Lam w r (sidePos mm) aN w r sigma 2 / ref
                else ref / I.lam w r (sidePos mm) aN w r sigma 2)
              (Sum.elim
                (fun ab => if ab.1 then
                  (Homogenization.Book.Ch02.sigmaCoarse
                    (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                    ((I.chart w r (sidePos mm) aN w r).coeffOn
                      (Homogenization.originCube d 0))) ab.2.1 ab.2.2 / ref
                  else ref * (Homogenization.Book.Ch02.sigmaStarInvCoarse
                    (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                    ((I.chart w r (sidePos mm) aN w r).coeffOn
                      (Homogenization.originCube d 0))) ab.2.1 ab.2.2)
                (fun j => if j = 0 then I.err w r (sidePos mm) aN w r ref s 2
                  else reference N nn z omega / ref)) rt
          else 0
      ∀ rt : Fin 3 ⊕ ((Bool × (Fin d × Fin d)) ⊕ Fin 2), rt ≠ Sum.inr (Sum.inr 1) →
        ∃ hmem : ∀ N, MemLp (ellVal N · rt) 1 (chaosSampleLaw M).toMeasure,
          IsCompact (closure (Set.range (fun N => (hmem N).toLp (ellVal N · rt)))) := by
  obtain ⟨delta0, hdelta0, hunit⟩ :=
    lem_prefix_limit_g9_unit_chart_compact hd I _Poincare _Extension _Perturbation _Sobolev D
      Cresp hCresp sigma s hs hsigma
  refine ⟨delta0, hdelta0, ?_⟩
  intro M hM Rm hRm Sreg It H hH sidePos nn mm z w
  let kappa : ℕ → ℝ := fun J =>
    Real.exp (((J : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) * ahom M J
  let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
    fun n zz omega => if 0 ≤ n then ∑ j ∈ Finset.Ico (0 : ℤ) n, omega (-j) zz
      else -∑ j ∈ Finset.Ico n (0 : ℤ), omega (-j) zz
  let reference : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
    fun N n zz omega => kappa ((N : ℤ) - n).toNat / kappa N *
      Real.exp (H omega zz + retained n zz omega)
  let F : ℕ → BilateralField d → Homogenization.Book.Ch02.TriadicCoeffFamily d :=
    fun K omega => aux_U2_unitChart I M H omega K
  let uVal : ℕ → BilateralField d → Fin 3 ⊕ ((Bool × (Fin d × Fin d)) ⊕ Unit) → ℝ :=
    fun K omega rt =>
      Sum.elim
        (fun j => if j = 0 then aux_U2_lamF sigma (F K omega)
          else if j = 1 then aux_U2_LamF sigma (F K omega)
          else (aux_U2_lamF sigma (F K omega))⁻¹)
        (Sum.elim
          (fun ab => if ab.1 then aux_U2_sigF ab.2.1 ab.2.2 (F K omega)
            else aux_U2_sigStarInvF ab.2.1 ab.2.2 (F K omega))
          (fun _ => aux_U2_errF s (F K omega) 1)) rt
  have hunitM := hunit M hM Rm hRm Sreg It H hH
  have hunit' : ∀ rt : Fin 3 ⊕ ((Bool × (Fin d × Fin d)) ⊕ Unit),
      ∃ hmem : ∀ K, MemLp (uVal K · rt) 1 (chaosSampleLaw M).toMeasure,
        IsCompact (closure (Set.range (fun K => (hmem K).toLp (uVal K · rt)))) := by
    simpa [uVal, F, aux_U2_unitChart, aux_U2_lamF, aux_U2_LamF, aux_U2_sigF,
      aux_U2_sigStarInvF, aux_U2_errF] using hunitM
  let ellVal : ℕ → BilateralField d → Fin 3 ⊕ ((Bool × (Fin d × Fin d)) ⊕ Fin 2) → ℝ :=
    fun N omega rt =>
      let aN := Lane4.cutoffPositiveCoefficient M H omega N w (sidePos mm)
      let r := (3 : ℝ) ^ (-mm)
      let ref := reference N mm w omega
      if nn ≤ (N : ℤ) ∧ mm ≤ (N : ℤ) then
        Sum.elim
          (fun j => if j = 0 then I.lam w r (sidePos mm) aN w r sigma 2 / ref
            else if j = 1 then I.Lam w r (sidePos mm) aN w r sigma 2 / ref
            else ref / I.lam w r (sidePos mm) aN w r sigma 2)
          (Sum.elim
            (fun ab => if ab.1 then
              (Homogenization.Book.Ch02.sigmaCoarse
                (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                ((I.chart w r (sidePos mm) aN w r).coeffOn
                  (Homogenization.originCube d 0))) ab.2.1 ab.2.2 / ref
              else ref * (Homogenization.Book.Ch02.sigmaStarInvCoarse
                (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                ((I.chart w r (sidePos mm) aN w r).coeffOn
                  (Homogenization.originCube d 0))) ab.2.1 ab.2.2)
            (fun j => if j = 0 then I.err w r (sidePos mm) aN w r ref s 2
              else reference N nn z omega / ref)) rt
      else 0
  change ∀ rt : Fin 3 ⊕ ((Bool × (Fin d × Fin d)) ⊕ Fin 2), rt ≠ Sum.inr (Sum.inr 1) →
      ∃ hmem : ∀ N, MemLp (ellVal N · rt) 1 (chaosSampleLaw M).toMeasure,
        IsCompact (closure (Set.range (fun N => (hmem N).toLp (ellVal N · rt))))
  have hlam0 : ∀ N : ℕ, nn ≤ (N : ℤ) → mm ≤ (N : ℤ) →
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        I.lam w ((3 : ℝ) ^ (-mm)) (sidePos mm)
            (Lane4.cutoffPositiveCoefficient M H omega N w (sidePos mm)) w
            ((3 : ℝ) ^ (-mm)) sigma 2 /
          reference N mm w omega =
        aux_U2_lamF sigma (F ((N : ℤ) - mm).toNat (aux_g9chart_transport_S mm w omega)) := by
    intro N _ hNm
    have hsc := aux_U2_T4_chart_identity I M H hH N mm hNm w (sidePos mm)
    filter_upwards [hsc] with omega hsc
    have hp := aux_g9chart_transport_reference_pos M H N mm w omega
    have heq := aux_U2_lam_eq I w ((3 : ℝ) ^ (-mm)) (sidePos mm)
      (Lane4.cutoffPositiveCoefficient M H omega N w (sidePos mm)) sigma hsigma
    have hhom := aux_U2_lamF_scaled sigma
      (aux_g9chart_transport_reference M H N mm w omega) hp
      (aux_U2_unitChart I M H (aux_g9chart_transport_S mm w omega) ((N : ℤ) - mm).toNat)
      (I.chart w ((3 : ℝ) ^ (-mm)) (sidePos mm)
        (Lane4.cutoffPositiveCoefficient M H omega N w (sidePos mm)) w ((3 : ℝ) ^ (-mm))) hsc
    rw [heq, hhom]
    have href : reference N mm w omega = aux_g9chart_transport_reference M H N mm w omega := by
      rfl
    rw [href]
    field_simp
    simpa [F]
  have hLam1 : ∀ N : ℕ, nn ≤ (N : ℤ) → mm ≤ (N : ℤ) →
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        I.Lam w ((3 : ℝ) ^ (-mm)) (sidePos mm)
            (Lane4.cutoffPositiveCoefficient M H omega N w (sidePos mm)) w
            ((3 : ℝ) ^ (-mm)) sigma 2 /
          reference N mm w omega =
        aux_U2_LamF sigma (F ((N : ℤ) - mm).toNat (aux_g9chart_transport_S mm w omega)) := by
    intro N _ hNm
    have hsc := aux_U2_T4_chart_identity I M H hH N mm hNm w (sidePos mm)
    filter_upwards [hsc] with omega hsc
    have hp := aux_g9chart_transport_reference_pos M H N mm w omega
    have heq := aux_U2_Lam_eq I w ((3 : ℝ) ^ (-mm)) (sidePos mm)
      (Lane4.cutoffPositiveCoefficient M H omega N w (sidePos mm)) sigma hsigma
    have hhom := aux_U2_LamF_scaled sigma
      (aux_g9chart_transport_reference M H N mm w omega) hp
      (aux_U2_unitChart I M H (aux_g9chart_transport_S mm w omega) ((N : ℤ) - mm).toNat)
      (I.chart w ((3 : ℝ) ^ (-mm)) (sidePos mm)
        (Lane4.cutoffPositiveCoefficient M H omega N w (sidePos mm)) w ((3 : ℝ) ^ (-mm))) hsc
    rw [heq, hhom]
    have href : reference N mm w omega = aux_g9chart_transport_reference M H N mm w omega := by rfl
    rw [href]
    field_simp
    simpa [F]
  have hinv2 : ∀ N : ℕ, nn ≤ (N : ℤ) → mm ≤ (N : ℤ) →
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        reference N mm w omega /
            I.lam w ((3 : ℝ) ^ (-mm)) (sidePos mm)
              (Lane4.cutoffPositiveCoefficient M H omega N w (sidePos mm)) w
              ((3 : ℝ) ^ (-mm)) sigma 2 =
        (aux_U2_lamF sigma (F ((N : ℤ) - mm).toNat (aux_g9chart_transport_S mm w omega)))⁻¹ := by
    intro N _ hNm
    filter_upwards [hlam0 N (by omega) hNm] with omega h
    have hrefpos := aux_g9chart_transport_reference_pos M H N mm w omega
    have hrefne : reference N mm w omega ≠ 0 := by
      simpa [reference, aux_g9chart_transport_reference] using hrefpos.ne'
    have heq := aux_U2_lam_eq I w ((3 : ℝ) ^ (-mm)) (sidePos mm)
      (Lane4.cutoffPositiveCoefficient M H omega N w (sidePos mm)) sigma hsigma
    have hlampos : 0 < I.lam w ((3 : ℝ) ^ (-mm)) (sidePos mm)
        (Lane4.cutoffPositiveCoefficient M H omega N w (sidePos mm)) w
        ((3 : ℝ) ^ (-mm)) sigma 2 := by
      rw [heq]
      exact Homogenization.Book.Ch02.lambdaSq_finite_pos
        (Homogenization.originCube d 0) _ hsigma.1 (by norm_num)
    calc
      reference N mm w omega /
          I.lam w ((3 : ℝ) ^ (-mm)) (sidePos mm)
            (Lane4.cutoffPositiveCoefficient M H omega N w (sidePos mm)) w
            ((3 : ℝ) ^ (-mm)) sigma 2 =
          (I.lam w ((3 : ℝ) ^ (-mm)) (sidePos mm)
            (Lane4.cutoffPositiveCoefficient M H omega N w (sidePos mm)) w
            ((3 : ℝ) ^ (-mm)) sigma 2 /
            reference N mm w omega)⁻¹ := by
              field_simp [hrefne, hlampos.ne']
      _ = (aux_U2_lamF sigma (F ((N : ℤ) - mm).toNat
            (aux_g9chart_transport_S mm w omega)))⁻¹ := by rw [h]
  have hsig : ∀ N : ℕ, nn ≤ (N : ℤ) → mm ≤ (N : ℤ) →
      ∀ (i j : Fin d), ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        (Homogenization.Book.Ch02.sigmaCoarse
          (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
          ((I.chart w ((3 : ℝ) ^ (-mm)) (sidePos mm)
            (Lane4.cutoffPositiveCoefficient M H omega N w (sidePos mm)) w
            ((3 : ℝ) ^ (-mm))).coeffOn (Homogenization.originCube d 0))) i j /
          reference N mm w omega =
        aux_U2_sigF i j (F ((N : ℤ) - mm).toNat (aux_g9chart_transport_S mm w omega)) := by
    intro N _ hNm i j
    have hsc := aux_U2_T4_chart_identity I M H hH N mm hNm w (sidePos mm)
    filter_upwards [hsc] with omega hsc
    have hp := aux_g9chart_transport_reference_pos M H N mm w omega
    have hhom := aux_U2_sigF_scaled (aux_g9chart_transport_reference M H N mm w omega) hp
      (aux_U2_unitChart I M H (aux_g9chart_transport_S mm w omega) ((N : ℤ) - mm).toNat)
      (I.chart w ((3 : ℝ) ^ (-mm)) (sidePos mm)
        (Lane4.cutoffPositiveCoefficient M H omega N w (sidePos mm)) w ((3 : ℝ) ^ (-mm))) hsc i j
    unfold aux_U2_sigF at hhom ⊢
    rw [hhom]
    have href : reference N mm w omega = aux_g9chart_transport_reference M H N mm w omega := by rfl
    rw [href]
    field_simp
    simpa [F]
  have hsigStar : ∀ N : ℕ, nn ≤ (N : ℤ) → mm ≤ (N : ℤ) →
      ∀ (i j : Fin d), ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        reference N mm w omega *
          (Homogenization.Book.Ch02.sigmaStarInvCoarse
            (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
            ((I.chart w ((3 : ℝ) ^ (-mm)) (sidePos mm)
              (Lane4.cutoffPositiveCoefficient M H omega N w (sidePos mm)) w
              ((3 : ℝ) ^ (-mm))).coeffOn (Homogenization.originCube d 0))) i j =
        aux_U2_sigStarInvF i j (F ((N : ℤ) - mm).toNat (aux_g9chart_transport_S mm w omega)) := by
    intro N _ hNm i j
    have hsc := aux_U2_T4_chart_identity I M H hH N mm hNm w (sidePos mm)
    filter_upwards [hsc] with omega hsc
    have hp := aux_g9chart_transport_reference_pos M H N mm w omega
    have hhom := aux_U2_sigStarInvF_scaled
      (aux_g9chart_transport_reference M H N mm w omega) hp
      (aux_U2_unitChart I M H (aux_g9chart_transport_S mm w omega) ((N : ℤ) - mm).toNat)
      (I.chart w ((3 : ℝ) ^ (-mm)) (sidePos mm)
        (Lane4.cutoffPositiveCoefficient M H omega N w (sidePos mm)) w ((3 : ℝ) ^ (-mm))) hsc i j
    unfold aux_U2_sigStarInvF at hhom ⊢
    rw [hhom]
    have href : reference N mm w omega = aux_g9chart_transport_reference M H N mm w omega := by rfl
    rw [href]
    field_simp
    simpa [F]
  have herr0 : ∀ N : ℕ, nn ≤ (N : ℤ) → mm ≤ (N : ℤ) →
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        I.err w ((3 : ℝ) ^ (-mm)) (sidePos mm)
            (Lane4.cutoffPositiveCoefficient M H omega N w (sidePos mm)) w
            ((3 : ℝ) ^ (-mm)) (reference N mm w omega) s 2 =
        aux_U2_errF s (F ((N : ℤ) - mm).toNat (aux_g9chart_transport_S mm w omega)) 1 := by
    intro N _ hNm
    have hsc := aux_U2_T4_chart_identity I M H hH N mm hNm w (sidePos mm)
    filter_upwards [hsc] with omega hsc
    have hp := aux_g9chart_transport_reference_pos M H N mm w omega
    have heq := aux_U2_err_eq I w ((3 : ℝ) ^ (-mm)) (sidePos mm)
      (Lane4.cutoffPositiveCoefficient M H omega N w (sidePos mm))
      (reference N mm w omega) hp s hs
    have hhom := aux_U2_errF_scaled s (aux_g9chart_transport_reference M H N mm w omega) hp
      (aux_U2_unitChart I M H (aux_g9chart_transport_S mm w omega) ((N : ℤ) - mm).toNat)
      (I.chart w ((3 : ℝ) ^ (-mm)) (sidePos mm)
        (Lane4.cutoffPositiveCoefficient M H omega N w (sidePos mm)) w ((3 : ℝ) ^ (-mm))) hsc
    have href : reference N mm w omega = aux_g9chart_transport_reference M H N mm w omega := by rfl
    rw [href] at heq
    rw [href]
    rw [heq, hhom]
  let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  have hS : MeasurePreserving (aux_g9chart_transport_S mm w) P P := by
    simpa [P] using (aux_g9chart_transport_S_measurePreserving M mm w)
  intro rt hrt
  rcases rt with j | rest
  · fin_cases j
    · obtain ⟨hf, hfc⟩ := hunit' (Sum.inl (0 : Fin 3))
      let idx : ℕ → Option ℕ := fun N =>
        if nn ≤ (N : ℤ) ∧ mm ≤ (N : ℤ) then some ((N : ℤ) - mm).toNat else none
      let g : ℕ → BilateralField d → ℝ := fun N omega => ellVal N omega (Sum.inl 0)
      have hrel : ∀ N, g N =ᵐ[P] fun omega =>
          match idx N with
          | none => 0
          | some K => uVal K (aux_g9chart_transport_S mm w omega) (Sum.inl (0 : Fin 3)) := by
        intro N
        by_cases ha : nn ≤ (N : ℤ) ∧ mm ≤ (N : ℤ)
        · filter_upwards [hlam0 N ha.1 ha.2] with omega h
          simpa [g, idx, ellVal, uVal, F, ha]
            using h
        · simp [g, idx, ellVal, ha]
      have hgm : ∀ N, MemLp (g N) 1 P := by
        intro N
        by_cases ha : nn ≤ (N : ℤ) ∧ mm ≤ (N : ℤ)
        · have h := hrel N
          simp only [idx, ha, ↓reduceIte] at h
          exact (memLp_congr_ae h).2 ((hf ((N : ℤ) - mm).toNat).comp_measurePreserving hS)
        · have h := hrel N
          simp only [idx, ha, ↓reduceIte] at h
          exact (memLp_congr_ae h).2 MemLp.zero
      refine ⟨?_, ?_⟩
      · simpa [g] using hgm
      · simpa [g] using
          (aux_lem_prefix_limit_g9_chart_compact_pullback_compact P (aux_g9chart_transport_S mm w) hS
            (fun K omega => uVal K omega (Sum.inl (0 : Fin 3))) hf hfc g hgm idx hrel)
    · obtain ⟨hf, hfc⟩ := hunit' (Sum.inl (1 : Fin 3))
      let idx : ℕ → Option ℕ := fun N =>
        if nn ≤ (N : ℤ) ∧ mm ≤ (N : ℤ) then some ((N : ℤ) - mm).toNat else none
      let g : ℕ → BilateralField d → ℝ := fun N omega => ellVal N omega (Sum.inl 1)
      have hrel : ∀ N, g N =ᵐ[P] fun omega =>
          match idx N with
          | none => 0
          | some K => uVal K (aux_g9chart_transport_S mm w omega) (Sum.inl (1 : Fin 3)) := by
        intro N
        by_cases ha : nn ≤ (N : ℤ) ∧ mm ≤ (N : ℤ)
        · filter_upwards [hLam1 N ha.1 ha.2] with omega h
          simpa [g, idx, ellVal, uVal, F, ha] using h
        · simp [g, idx, ellVal, ha]
      have hgm : ∀ N, MemLp (g N) 1 P := by
        intro N
        by_cases ha : nn ≤ (N : ℤ) ∧ mm ≤ (N : ℤ)
        · have h := hrel N
          simp only [idx, ha, ↓reduceIte] at h
          exact (memLp_congr_ae h).2 ((hf ((N : ℤ) - mm).toNat).comp_measurePreserving hS)
        · have h := hrel N
          simp only [idx, ha, ↓reduceIte] at h
          exact (memLp_congr_ae h).2 MemLp.zero
      refine ⟨?_, ?_⟩
      · simpa [g] using hgm
      · simpa [g] using
          (aux_lem_prefix_limit_g9_chart_compact_pullback_compact P (aux_g9chart_transport_S mm w) hS
            (fun K omega => uVal K omega (Sum.inl (1 : Fin 3))) hf hfc g hgm idx hrel)
    · obtain ⟨hf, hfc⟩ := hunit' (Sum.inl (2 : Fin 3))
      let idx : ℕ → Option ℕ := fun N =>
        if nn ≤ (N : ℤ) ∧ mm ≤ (N : ℤ) then some ((N : ℤ) - mm).toNat else none
      let g : ℕ → BilateralField d → ℝ := fun N omega => ellVal N omega (Sum.inl 2)
      have hrel : ∀ N, g N =ᵐ[P] fun omega =>
          match idx N with
          | none => 0
          | some K => uVal K (aux_g9chart_transport_S mm w omega) (Sum.inl (2 : Fin 3)) := by
        intro N
        by_cases ha : nn ≤ (N : ℤ) ∧ mm ≤ (N : ℤ)
        · filter_upwards [hinv2 N ha.1 ha.2] with omega h
          simpa [g, idx, ellVal, uVal, F, ha] using h
        · simp [g, idx, ellVal, ha]
      have hgm : ∀ N, MemLp (g N) 1 P := by
        intro N
        by_cases ha : nn ≤ (N : ℤ) ∧ mm ≤ (N : ℤ)
        · have h := hrel N
          simp only [idx, ha, ↓reduceIte] at h
          exact (memLp_congr_ae h).2 ((hf ((N : ℤ) - mm).toNat).comp_measurePreserving hS)
        · have h := hrel N
          simp only [idx, ha, ↓reduceIte] at h
          exact (memLp_congr_ae h).2 MemLp.zero
      refine ⟨?_, ?_⟩
      · simpa [g] using hgm
      · simpa [g] using
          (aux_lem_prefix_limit_g9_chart_compact_pullback_compact P (aux_g9chart_transport_S mm w) hS
            (fun K omega => uVal K omega (Sum.inl (2 : Fin 3))) hf hfc g hgm idx hrel)
  · rcases rest with ab | k
    · by_cases hb : ab.1 = true
      · obtain ⟨hf, hfc⟩ := hunit' (Sum.inr (Sum.inl (true, (ab.2.1, ab.2.2))))
        let idx : ℕ → Option ℕ := fun N =>
          if nn ≤ (N : ℤ) ∧ mm ≤ (N : ℤ) then some ((N : ℤ) - mm).toNat else none
        let g : ℕ → BilateralField d → ℝ := fun N omega => ellVal N omega
          (Sum.inr (Sum.inl (true, (ab.2.1, ab.2.2))))
        have hrel : ∀ N, g N =ᵐ[P] fun omega =>
            match idx N with
            | none => 0
            | some K => uVal K (aux_g9chart_transport_S mm w omega)
                (Sum.inr (Sum.inl (true, (ab.2.1, ab.2.2)))) := by
          intro N
          by_cases ha : nn ≤ (N : ℤ) ∧ mm ≤ (N : ℤ)
          · filter_upwards [hsig N ha.1 ha.2 ab.2.1 ab.2.2] with omega h
            simpa [g, idx, ellVal, uVal, F, ha, hb] using h
          · simp [g, idx, ellVal, ha]
        have hgm : ∀ N, MemLp (g N) 1 P := by
          intro N
          by_cases ha : nn ≤ (N : ℤ) ∧ mm ≤ (N : ℤ)
          · have h := hrel N
            simp only [idx, ha, ↓reduceIte] at h
            exact (memLp_congr_ae h).2 ((hf ((N : ℤ) - mm).toNat).comp_measurePreserving hS)
          · have h := hrel N
            simp only [idx, ha, ↓reduceIte] at h
            exact (memLp_congr_ae h).2 MemLp.zero
        have hab : ab = (true, (ab.2.1, ab.2.2)) := by
          apply Prod.ext
          · exact hb
          · rfl
        rw [hab]
        refine ⟨?_, ?_⟩
        ·
          simpa [g] using hgm
        · simpa [g] using
            (aux_lem_prefix_limit_g9_chart_compact_pullback_compact P (aux_g9chart_transport_S mm w) hS
              (fun K omega => uVal K omega
                (Sum.inr (Sum.inl (true, (ab.2.1, ab.2.2))))) hf hfc g hgm idx hrel)
      · have hb' : ab.1 = false := by
          cases h : ab.1 with
          | false => rfl
          | true => exact (hb h).elim
        obtain ⟨hf, hfc⟩ := hunit' (Sum.inr (Sum.inl (false, (ab.2.1, ab.2.2))))
        let idx : ℕ → Option ℕ := fun N =>
          if nn ≤ (N : ℤ) ∧ mm ≤ (N : ℤ) then some ((N : ℤ) - mm).toNat else none
        let g : ℕ → BilateralField d → ℝ := fun N omega => ellVal N omega
          (Sum.inr (Sum.inl (false, (ab.2.1, ab.2.2))))
        have hrel : ∀ N, g N =ᵐ[P] fun omega =>
            match idx N with
            | none => 0
            | some K => uVal K (aux_g9chart_transport_S mm w omega)
                (Sum.inr (Sum.inl (false, (ab.2.1, ab.2.2)))) := by
          intro N
          by_cases ha : nn ≤ (N : ℤ) ∧ mm ≤ (N : ℤ)
          · filter_upwards [hsigStar N ha.1 ha.2 ab.2.1 ab.2.2] with omega h
            simpa [g, idx, ellVal, uVal, F, ha, hb'] using h
          · simp [g, idx, ellVal, ha]
        have hgm : ∀ N, MemLp (g N) 1 P := by
          intro N
          by_cases ha : nn ≤ (N : ℤ) ∧ mm ≤ (N : ℤ)
          · have h := hrel N
            simp only [idx, ha, ↓reduceIte] at h
            exact (memLp_congr_ae h).2 ((hf ((N : ℤ) - mm).toNat).comp_measurePreserving hS)
          · have h := hrel N
            simp only [idx, ha, ↓reduceIte] at h
            exact (memLp_congr_ae h).2 MemLp.zero
        have hab : ab = (false, (ab.2.1, ab.2.2)) := by
          apply Prod.ext
          · exact hb'
          · rfl
        rw [hab]
        refine ⟨?_, ?_⟩
        ·
          simpa [g] using hgm
        · simpa [g] using
            (aux_lem_prefix_limit_g9_chart_compact_pullback_compact P (aux_g9chart_transport_S mm w) hS
              (fun K omega => uVal K omega
                (Sum.inr (Sum.inl (false, (ab.2.1, ab.2.2))))) hf hfc g hgm idx hrel)
    · fin_cases k
      · obtain ⟨hf, hfc⟩ := hunit' (Sum.inr (Sum.inr ()))
        let idx : ℕ → Option ℕ := fun N =>
          if nn ≤ (N : ℤ) ∧ mm ≤ (N : ℤ) then some ((N : ℤ) - mm).toNat else none
        let g : ℕ → BilateralField d → ℝ := fun N omega => ellVal N omega
          (Sum.inr (Sum.inr 0))
        have hrel : ∀ N, g N =ᵐ[P] fun omega =>
            match idx N with
            | none => 0
            | some K => uVal K (aux_g9chart_transport_S mm w omega) (Sum.inr (Sum.inr ())) := by
          intro N
          by_cases ha : nn ≤ (N : ℤ) ∧ mm ≤ (N : ℤ)
          · filter_upwards [herr0 N ha.1 ha.2] with omega h
            simpa [g, idx, ellVal, uVal, F, ha] using h
          · simp [g, idx, ellVal, ha]
        have hgm : ∀ N, MemLp (g N) 1 P := by
          intro N
          by_cases ha : nn ≤ (N : ℤ) ∧ mm ≤ (N : ℤ)
          · have h := hrel N
            simp only [idx, ha, ↓reduceIte] at h
            exact (memLp_congr_ae h).2 ((hf ((N : ℤ) - mm).toNat).comp_measurePreserving hS)
          · have h := hrel N
            simp only [idx, ha, ↓reduceIte] at h
            exact (memLp_congr_ae h).2 MemLp.zero
        refine ⟨?_, ?_⟩
        · simpa [g] using hgm
        · simpa [g] using
            (aux_lem_prefix_limit_g9_chart_compact_pullback_compact P (aux_g9chart_transport_S mm w) hS
              (fun K omega => uVal K omega (Sum.inr (Sum.inr ()))) hf hfc g hgm idx hrel)
      · exact False.elim (hrt rfl)

end Paper
