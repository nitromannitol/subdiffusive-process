import SubdiffusiveProcess.Paper.neumann_centered_response
import SubdiffusiveProcess.Paper.lem_15
import SubdiffusiveProcess.Paper.lem_block_projections
import SubdiffusiveProcess.Paper.prop_16_coarse_block_dirichlet
import SubdiffusiveProcess.Paper.prop_16_coarse_block_neumann
import SubdiffusiveProcess.Lane3.BandFiltration
import SubdiffusiveProcess.Paper.cor_14
import SubdiffusiveProcess.Paper.lem_neumann_15
import SubdiffusiveProcess.Paper.lem_neumann_error
import SubdiffusiveProcess.Paper.lem_infrared
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_responses

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Topology
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.Lane3

noncomputable section
namespace Paper

section Prop16_A_Prob
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess SubdiffusiveProcess.Lane3


/-- Exchanging the first components of two independent product samples preserves the
joint product law. -/
theorem aux_prop_16_swap4 {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    MeasurePreserving (fun x : (A × B) × (A × B) => ((x.2.1, x.1.2), (x.1.1, x.2.2)))
      ((μ.prod ν).prod (μ.prod ν)) ((μ.prod ν).prod (μ.prod ν)) := by
  have f1 := measurePreserving_prodAssoc μ ν (μ.prod ν)
  have f2 : MeasurePreserving (Prod.map id Prod.swap)
      (μ.prod (ν.prod (μ.prod ν))) (μ.prod ((μ.prod ν).prod ν)) :=
    (MeasurePreserving.id μ).prod Measure.measurePreserving_swap
  have f3 : MeasurePreserving (Prod.map id MeasurableEquiv.prodAssoc)
      (μ.prod ((μ.prod ν).prod ν)) (μ.prod (μ.prod (ν.prod ν))) :=
    (MeasurePreserving.id μ).prod (measurePreserving_prodAssoc μ ν ν)
  have f4 := (measurePreserving_prodAssoc μ μ (ν.prod ν)).symm
  have f5 : MeasurePreserving (Prod.map Prod.swap Prod.swap)
      ((μ.prod μ).prod (ν.prod ν)) ((μ.prod μ).prod (ν.prod ν)) :=
    Measure.measurePreserving_swap.prod Measure.measurePreserving_swap
  have g1 := measurePreserving_prodAssoc μ μ (ν.prod ν)
  have g2 : MeasurePreserving (Prod.map id MeasurableEquiv.prodAssoc.symm)
      (μ.prod (μ.prod (ν.prod ν))) (μ.prod ((μ.prod ν).prod ν)) :=
    (MeasurePreserving.id μ).prod (measurePreserving_prodAssoc μ ν ν).symm
  have g3 : MeasurePreserving (Prod.map id (Prod.map Prod.swap id))
      (μ.prod ((μ.prod ν).prod ν)) (μ.prod ((ν.prod μ).prod ν)) :=
    (MeasurePreserving.id μ).prod
      (Measure.measurePreserving_swap.prod (MeasurePreserving.id ν))
  have g4 : MeasurePreserving (Prod.map id MeasurableEquiv.prodAssoc)
      (μ.prod ((ν.prod μ).prod ν)) (μ.prod (ν.prod (μ.prod ν))) :=
    (MeasurePreserving.id μ).prod (measurePreserving_prodAssoc ν μ ν)
  have g5 := (measurePreserving_prodAssoc μ ν (μ.prod ν)).symm
  have h := g5.comp (g4.comp (g3.comp (g2.comp (g1.comp
    (f5.comp (f4.comp (f3.comp (f2.comp f1))))))))
  convert h using 1

/-- Exchanging an arbitrary block of coordinates between two independent samples of an
infinite product preserves the joint law. -/
theorem aux_prop_16_block_swap {I : Type*} {X : I → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : (i : I) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (S : Set I) [DecidablePred (fun i => i ∈ S)] :
    MeasurePreserving
      (fun z : ((i : I) → X i) × ((i : I) → X i) =>
        ((fun i : I => if i ∈ S then z.2 i else z.1 i),
          (fun i : I => if i ∈ S then z.1 i else z.2 i)))
      ((Measure.infinitePi μ).prod (Measure.infinitePi μ))
      ((Measure.infinitePi μ).prod (Measure.infinitePi μ)) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd X (fun i => i ∈ S)
  let νS := Measure.infinitePi (fun i : S => μ i)
  let νC := Measure.infinitePi (fun i : {i // i ∉ S} => μ i)
  have hsplit : MeasurePreserving e (Measure.infinitePi μ) (νS.prod νC) :=
    measurePreserving_infinitePi_split μ (fun i => i ∈ S)
  have h := ((MeasurePreserving.symm e hsplit).prod (MeasurePreserving.symm e hsplit)).comp
    ((aux_prop_16_swap4 νS νC).comp (hsplit.prod hsplit))
  convert h using 1

/-- Replacing one coordinate by the same coordinate of an independent copy preserves the law. -/
theorem aux_prop_16_update_mp {I : Type*} [DecidableEq I] {X : Type*}
    [MeasurableSpace X] (μs : I → Measure X) [∀ i, IsProbabilityMeasure (μs i)] (k0 : I) :
    MeasurePreserving (fun p : (I → X) × (I → X) => Function.update p.1 k0 (p.2 k0))
      ((Measure.infinitePi μs).prod (Measure.infinitePi μs)) (Measure.infinitePi μs) := by
  classical
  have h := SubdiffusiveProcess.measurePreserving_copy_infinitePi_block
    (X := fun _ : I => X) μs ({k0} : Set I)
  convert h using 1
  funext p i
  by_cases hi : i = k0
  · subst hi; simp
  · simp [Function.update, hi]

/-- Conditional Jensen through an independent resampling of the discarded block. -/
theorem aux_prop_16_resample_jensen {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace B] {ξ : Measure Ω} [IsProbabilityMeasure ξ] {μ : Measure A}
    {ν : Measure B} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (e : Ω ≃ᵐ A × B) (he : MeasurePreserving e ξ (μ.prod ν))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ⊤) {f : Ω → ℝ} (hf : Integrable f ξ) :
    eLpNorm (f - ξ[f | (inferInstance : MeasurableSpace A).comap (fun x => (e x).1)]) p ξ ≤
      eLpNorm (fun q : Ω × Ω => f q.1 - f (e.symm ((e q.1).1, (e q.2).2))) p
        (ξ.prod ξ) := by
  have hce := condExp_equiv_fst_integral e he hf
  have h1 : MeasurePreserving (Prod.map (fun x => (e x).1) id) (ξ.prod ν) (μ.prod ν) :=
    (measurePreserving_fst.comp he).prod (MeasurePreserving.id ν)
  have hΘ : MeasurePreserving (fun xb : Ω × B => e.symm ((e xb.1).1, xb.2)) (ξ.prod ν) ξ :=
    (he.symm e).comp h1
  have hg : Integrable (fun xb : Ω × B => f (e.symm ((e xb.1).1, xb.2))) (ξ.prod ν) :=
    hΘ.integrable_comp_of_integrable hf
  let F : Ω × B → ℝ := fun xb => f xb.1 - f (e.symm ((e xb.1).1, xb.2))
  have hF : Integrable F (ξ.prod ν) := (hf.comp_fst ν).sub hg
  have hae : (f - ξ[f | (inferInstance : MeasurableSpace A).comap (fun x => (e x).1)])
      =ᵐ[ξ] fun x => ∫ b, F (x, b) ∂ν := by
    filter_upwards [hce, hg.prod_right_ae] with x hx hxint
    simp only [Pi.sub_apply, hx, F]
    rw [integral_sub (integrable_const _) hxint, integral_const]
    simp
  rw [eLpNorm_congr_ae hae]
  have hfst : MeasurePreserving (Prod.fst : Ω × B → Ω) (ξ.prod ν) ξ := measurePreserving_fst
  rw [← eLpNorm_comp_measurePreserving hF.integral_prod_left.aestronglyMeasurable hfst]
  refine (eLpNorm_prod_integral_le hp hp_top hF.aestronglyMeasurable).trans (le_of_eq ?_)
  have hT : MeasurePreserving (Prod.map id (fun x => (e x).2)) (ξ.prod ξ) (ξ.prod ν) :=
    (MeasurePreserving.id ξ).prod (measurePreserving_snd.comp he)
  rw [← eLpNorm_comp_measurePreserving hF.aestronglyMeasurable hT]
  rfl

/-- The retained block of the three-block decomposition generates the band σ-field. -/
theorem aux_prop_16_band_sigma_eq {X : Type} [MeasurableSpace X] (h : ℕ) :
    bandSigma (fun _ : ℤ => X) h =
      middleSigma.comap (threeBlockEquiv (X := fun _ : ℤ => X)
        (fun j : ℤ => j ≤ (h : ℤ)) (fun j => j < -(h : ℤ))) := by
  classical
  set e := threeBlockEquiv (X := fun _ : ℤ => X) (fun j : ℤ => j ≤ (h : ℤ))
    (fun j => j < -(h : ℤ))
  have hmid : middleSigma.comap e =
      (inferInstance : MeasurableSpace
        ((i : {i : {j : ℤ // j ≤ (h : ℤ)} // ¬ i.1 < -(h : ℤ)}) → X)).comap
        (fun om => (e om).1.2) := by
    rw [middleSigma, MeasurableSpace.comap_comp]
    rfl
  rw [hmid]
  apply le_antisymm
  · refine iSup₂_le fun j hj => ?_
    have hj1 : j ≤ (h : ℤ) := hj.2
    have hj2 : ¬ j < -(h : ℤ) := not_lt.mpr hj.1
    have hfun : (fun om : ℤ → X => om j) =
        (fun b : ((i : {i : {j : ℤ // j ≤ (h : ℤ)} // ¬ i.1 < -(h : ℤ)}) → X) =>
          b ⟨⟨j, hj1⟩, hj2⟩) ∘ (fun om => (e om).1.2) := rfl
    rw [hfun, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le
  · show MeasurableSpace.comap (fun om => (e om).1.2) MeasurableSpace.pi ≤ _
    simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
    refine iSup_le fun i => ?_
    have hi : i.1.1 ∈ Set.Icc (-(h : ℤ)) (h : ℤ) := ⟨not_lt.mp i.2, i.1.2⟩
    exact le_iSup₂ (f := fun (k : ℤ) (_ : k ∈ Set.Icc (-(h : ℤ)) (h : ℤ)) =>
        (inferInstance : MeasurableSpace X).comap (fun om : ℤ → X => om k)) i.1.1 hi

theorem aux_prop_16_coarse_symm {X : Type} [MeasurableSpace X] (h : ℕ)
    (q : (ℤ → X) × (ℤ → X)) :
    let e := threeBlockEquiv (X := fun _ : ℤ => X) (fun j : ℤ => j ≤ (h : ℤ))
      (fun j => j < -(h : ℤ))
    e.symm ((e q.1).1, (e q.2).2) = fun j => if (h : ℤ) < j then q.2 j else q.1 j := by
  intro e
  apply e.injective
  rw [MeasurableEquiv.apply_symm_apply]
  refine Prod.ext ?_ ?_
  · have hfun : (fun i : {j : ℤ // j ≤ (h : ℤ)} => q.1 i) =
        (fun i : {j : ℤ // j ≤ (h : ℤ)} => if (h : ℤ) < (i : ℤ) then q.2 i else q.1 i) :=
      funext fun i => (if_neg (not_lt.mpr i.2)).symm
    exact congrArg (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : {j : ℤ // j ≤ (h : ℤ)} => X)
      (fun i => (i : ℤ) < -(h : ℤ))) hfun
  · funext i
    show q.2 i = if (h : ℤ) < (i : ℤ) then q.2 i else q.1 i
    rw [if_pos (lt_of_not_ge i.2)]

theorem aux_prop_16_fine_symm {X : Type} [MeasurableSpace X] (h : ℕ)
    (q : (ℤ → X) × (ℤ → X)) :
    let e := threeBlockEquiv (X := fun _ : ℤ => X) (fun j : ℤ => j ≤ (h : ℤ))
      (fun j => j < -(h : ℤ))
    let e2 := e.trans (MeasurableEquiv.prodAssoc.trans MeasurableEquiv.prodComm)
    e2.symm ((e2 q.1).1, (e2 q.2).2) = fun j => if j < -(h : ℤ) then q.2 j else q.1 j := by
  intro e e2
  apply e2.injective
  rw [MeasurableEquiv.apply_symm_apply]
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · funext i
    show q.1 i.1 = if (i.1 : ℤ) < -(h : ℤ) then q.2 i.1 else q.1 i.1
    rw [if_neg i.2]
  · funext i
    show q.1 i = if (i : ℤ) < -(h : ℤ) then q.2 i else q.1 i
    have : ¬ (i : ℤ) < -(h : ℤ) := by have := i.2; omega
    rw [if_neg this]
  · funext i
    show q.2 i.1 = if (i.1 : ℤ) < -(h : ℤ) then q.2 i.1 else q.1 i.1
    rw [if_pos i.2]

/-- **Band split.** The band error is bounded by the coarse-copy and fine-copy increments. -/
theorem aux_prop_16_band_split {X : Type} [MeasurableSpace X]
    (laws : ℤ → Measure X) [∀ j, IsProbabilityMeasure (laws j)] (h : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    {f : (ℤ → X) → ℝ} (hf : Integrable f (Measure.infinitePi laws)) :
    eLpNorm (fun om => f om - (Measure.infinitePi laws)[f | bandSigma (fun _ : ℤ => X) h] om) p
        (Measure.infinitePi laws) ≤
      eLpNorm (fun q : (ℤ → X) × (ℤ → X) =>
          f q.1 - f (fun j => if (h : ℤ) < j then q.2 j else q.1 j)) p
        ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) +
      eLpNorm (fun q : (ℤ → X) × (ℤ → X) =>
          f q.1 - f (fun j => if j < -(h : ℤ) then q.2 j else q.1 j)) p
        ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) := by
  have hmain := infinitePi_integer_band_error_le laws h hp hp_top hf
  simp only at hmain
  set e := threeBlockEquiv (X := fun _ : ℤ => X) (fun j : ℤ => j ≤ (h : ℤ))
    (fun j => j < -(h : ℤ)) with he_def
  rw [← aux_prop_16_band_sigma_eq] at hmain
  have he := measurePreserving_infinitePi_threeBlock laws (fun j : ℤ => j ≤ (h : ℤ))
    (fun j => j < -(h : ℤ))
  refine hmain.trans (add_le_add ?_ ?_)
  · have hlm : leftMiddleSigma.comap e =
        (inferInstance : MeasurableSpace _).comap (fun x => (e x).1) := by
      rw [leftMiddleSigma, MeasurableSpace.comap_comp]
      rfl
    rw [hlm]
    refine (aux_prop_16_resample_jensen e he hp hp_top hf).trans (le_of_eq ?_)
    congr 1
    funext q
    rw [aux_prop_16_coarse_symm h q]
  · let e2 := e.trans (MeasurableEquiv.prodAssoc.trans MeasurableEquiv.prodComm)
    have he2 : MeasurePreserving e2 (Measure.infinitePi laws) _ :=
      (Measure.measurePreserving_swap.comp (measurePreserving_prodAssoc _ _ _)).comp he
    have hmr : middleRightSigma.comap e =
        (inferInstance : MeasurableSpace _).comap (fun x => (e2 x).1) := by
      rw [middleRightSigma, MeasurableSpace.comap_comp]
      rfl
    rw [hmr]
    refine (aux_prop_16_resample_jensen e2 he2 hp hp_top hf).trans (le_of_eq ?_)
    congr 1
    funext q
    rw [aux_prop_16_fine_symm h q]

/-- **Fine telescoping.** If `f` is determined by the coordinates `≥ -N` on a full-measure
set, the fine-copy increment is bounded by the one-coordinate replacement increments of the
layers strictly between the band and the cutoff. -/
theorem aux_prop_16_fine_telescope {X : Type} [MeasurableSpace X]
    (laws : ℤ → Measure X) [∀ j, IsProbabilityMeasure (laws j)]
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (f : (ℤ → X) → ℝ) (hf : AEStronglyMeasurable f (Measure.infinitePi laws))
    (G : Set (ℤ → X)) (hG : ∀ᵐ om ∂(Measure.infinitePi laws), om ∈ G)
    (h N : ℕ)
    (hdet : ∀ ω₁ ∈ G, ∀ ω₂ ∈ G, (∀ j : ℤ, -(N : ℤ) ≤ j → ω₁ j = ω₂ j) → f ω₁ = f ω₂)
    (c : ℕ → ℝ≥0∞)
    (hstep : ∀ k : ℕ, h < k → k ≤ N →
      eLpNorm (fun q : (ℤ → X) × (ℤ → X) =>
          f q.1 - f (Function.update q.1 (-(k : ℤ)) (q.2 (-(k : ℤ))))) p
        ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) ≤ c k) :
    eLpNorm (fun q : (ℤ → X) × (ℤ → X) =>
        f q.1 - f (fun j => if j < -(h : ℤ) then q.2 j else q.1 j)) p
      ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) ≤
      ∑ k ∈ Finset.Ioc h N, c k := by
  classical
  set P := Measure.infinitePi laws with hP
  let W : ℕ → (ℤ → X) × (ℤ → X) → (ℤ → X) := fun k q j =>
    if -(k : ℤ) ≤ j ∧ j < -(h : ℤ) then q.2 j else q.1 j
  have hWmp : ∀ k, MeasurePreserving (W k) (P.prod P) P := fun k =>
    measurePreserving_copy_infinitePi_block laws {j : ℤ | -(k : ℤ) ≤ j ∧ j < -(h : ℤ)}
  let Sw : ℕ → (ℤ → X) × (ℤ → X) → (ℤ → X) × (ℤ → X) := fun k q =>
    (W k q, fun j => if -(k : ℤ) ≤ j ∧ j < -(h : ℤ) then q.1 j else q.2 j)
  have hSwmp : ∀ k, MeasurePreserving (Sw k) (P.prod P) (P.prod P) := fun k =>
    aux_prop_16_block_swap laws {j : ℤ | -(k : ℤ) ≤ j ∧ j < -(h : ℤ)}
  have hfW : ∀ k, AEStronglyMeasurable (fun q => f (W k q)) (P.prod P) := fun k =>
    hf.comp_measurePreserving (hWmp k)
  have hf1 : AEStronglyMeasurable (fun q : (ℤ → X) × (ℤ → X) => f q.1) (P.prod P) :=
    hf.comp_measurePreserving measurePreserving_fst
  -- one step
  have hstep' : ∀ k : ℕ, h ≤ k → k + 1 ≤ N →
      eLpNorm (fun q => f (W k q) - f (W (k + 1) q)) p (P.prod P) ≤ c (k + 1) := by
    intro k hk hkN
    let Gk : (ℤ → X) × (ℤ → X) → ℝ := fun q =>
      f q.1 - f (Function.update q.1 (-((k + 1 : ℕ) : ℤ)) (q.2 (-((k + 1 : ℕ) : ℤ))))
    have hGk : AEStronglyMeasurable Gk (P.prod P) :=
      hf1.sub (hf.comp_measurePreserving (aux_prop_16_update_mp laws _))
    have hcomp : (fun q => f (W k q) - f (W (k + 1) q)) = Gk ∘ Sw k := by
      funext q
      simp only [Gk, Sw, Function.comp_apply]
      congr 2
      funext j
      by_cases hj : j = -((k + 1 : ℕ) : ℤ)
      · subst hj
        simp only [Function.update_self, W]
        have h1 : -((k + 1 : ℕ) : ℤ) ≤ -((k + 1 : ℕ) : ℤ) ∧ -((k + 1 : ℕ) : ℤ) < -(h : ℤ) :=
          ⟨le_rfl, by push_cast; omega⟩
        have h2 : ¬ (-(k : ℤ) ≤ -((k + 1 : ℕ) : ℤ) ∧ -((k + 1 : ℕ) : ℤ) < -(h : ℤ)) := by
          push_cast; omega
        rw [if_pos (by exact_mod_cast h1), if_neg h2]
      · rw [Function.update_of_ne hj]
        simp only [W]
        have hiff : (-((k + 1 : ℕ) : ℤ) ≤ j ∧ j < -(h : ℤ)) ↔ (-(k : ℤ) ≤ j ∧ j < -(h : ℤ)) := by
          push_cast at hj ⊢; omega
        by_cases hc : -(k : ℤ) ≤ j ∧ j < -(h : ℤ)
        · rw [if_pos hc, if_pos (hiff.mpr hc)]
        · rw [if_neg hc, if_neg (fun h' => hc (hiff.mp h'))]
    rw [hcomp, eLpNorm_comp_measurePreserving hGk (hSwmp k)]
    exact hstep (k + 1) (by omega) hkN
  -- the telescoping sum
  have hW0 : ∀ q, W h q = q.1 := by
    intro q
    funext j
    simp only [W]
    rw [if_neg (by omega)]
  have htel : ∀ m : ℕ, h + m ≤ N →
      eLpNorm (fun q => f q.1 - f (W (h + m) q)) p (P.prod P) ≤
        ∑ k ∈ Finset.Ioc h (h + m), c k := by
    intro m
    induction m with
    | zero =>
      intro _
      simp only [Nat.add_zero, hW0, sub_self]
      simp
    | succ m ih =>
      intro hm
      have hsplit : (fun q => f q.1 - f (W (h + (m + 1)) q)) =
          (fun q => f q.1 - f (W (h + m) q)) + (fun q => f (W (h + m) q) - f (W (h + m + 1) q)) := by
        funext q
        simp only [Pi.add_apply]
        rw [show h + (m + 1) = h + m + 1 by omega]
        ring
      rw [hsplit, show h + (m + 1) = h + m + 1 by omega, Finset.sum_Ioc_succ_top (by omega)]
      refine (eLpNorm_add_le (hf1.sub (hfW _)) ((hfW _).sub (hfW _)) hp).trans ?_
      exact add_le_add (ih (by omega)) (hstep' (h + m) (by omega) (by omega))
  -- determination by coordinates `≥ -N`
  let FC : (ℤ → X) × (ℤ → X) → (ℤ → X) := fun q j => if j < -(h : ℤ) then q.2 j else q.1 j
  have hFCmp : MeasurePreserving FC (P.prod P) P :=
    measurePreserving_copy_infinitePi_block laws {j : ℤ | j < -(h : ℤ)}
  have hGFC : ∀ᵐ q ∂(P.prod P), FC q ∈ G := hFCmp.quasiMeasurePreserving.ae hG
  have hG1 : ∀ᵐ q ∂(P.prod P), q.1 ∈ G :=
    (measurePreserving_fst : MeasurePreserving Prod.fst (P.prod P) P).quasiMeasurePreserving.ae hG
  by_cases hNh : N ≤ h
  · have hzero : (fun q : (ℤ → X) × (ℤ → X) => f q.1 - f (FC q)) =ᵐ[P.prod P] 0 := by
      filter_upwards [hGFC, hG1] with q hq1 hq2
      rw [hdet (FC q) hq1 q.1 hq2 (fun j hj => by
        simp only [FC]; rw [if_neg (by omega)])]
      simp
    change eLpNorm (fun q : (ℤ → X) × (ℤ → X) => f q.1 - f (FC q)) p (P.prod P) ≤ _
    rw [eLpNorm_congr_ae hzero, eLpNorm_zero]
    exact zero_le _
  · push_neg at hNh
    have hGW : ∀ᵐ q ∂(P.prod P), W N q ∈ G := (hWmp N).quasiMeasurePreserving.ae hG
    have heq : (fun q : (ℤ → X) × (ℤ → X) => f q.1 - f (FC q)) =ᵐ[P.prod P]
        (fun q => f q.1 - f (W (h + (N - h)) q)) := by
      filter_upwards [hGFC, hGW] with q hq1 hq2
      rw [show h + (N - h) = N by omega]
      rw [hdet (FC q) hq1 (W N q) hq2 (fun j hj => by
        simp only [FC, W]
        by_cases hj2 : j < -(h : ℤ)
        · rw [if_pos hj2, if_pos ⟨hj, hj2⟩]
        · rw [if_neg hj2, if_neg (fun h' => hj2 h'.2)])]
    change eLpNorm (fun q : (ℤ → X) × (ℤ → X) => f q.1 - f (FC q)) p (P.prod P) ≤ _
    rw [eLpNorm_congr_ae heq]
    have := htel (N - h) (by omega)
    rwa [show h + (N - h) = N by omega] at this ⊢

end Prop16_A_Prob

section Prop16_A2_Small
open MeasureTheory Filter Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Topology
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.Lane3


theorem aux_prop_16_exponent_facts (d : ℕ) (hd : 2 ≤ d) (t : ℝ)
    (ht_lower : (d : ℝ) - 1 < t) (ht_upper : t < (d : ℝ)) :
    0 < t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3) ∧
      t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3) ≤ 1 := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ht0 : 0 < t := by linarith
  have h1 : 0 < t - d + 1 := by linarith
  have h2 : t - d + 1 < 1 := by linarith
  have hlog : 1 < 8 * Real.log 3 := by
    have h2' := Real.log_two_gt_d9
    have h3 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
    linarith
  constructor
  · have : 0 < 8 * Real.log 3 := by linarith
    positivity
  · rw [div_le_one (by linarith)]
    have : t * (t - d + 1) / (t + 1) ≤ 1 := by
      rw [div_le_one (by linarith)]
      nlinarith
    linarith

theorem aux_prop_16_geom (a : ℝ) (ha : 0 < a) (Cd : ℝ) (hCd : 0 ≤ Cd) (h N : ℕ) :
    ∑ k ∈ Finset.Ioc h N, ENNReal.ofReal (Cd * (3 : ℝ) ^ (-a * (k : ℝ))) ≤
      ENNReal.ofReal (Cd * (3 : ℝ) ^ (-a * (h : ℝ)) / (1 - (3 : ℝ) ^ (-a))) := by
  have hr0 : 0 ≤ (3 : ℝ) ^ (-a) := by positivity
  have hr1 : (3 : ℝ) ^ (-a) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hpow : ∀ k : ℕ, (3 : ℝ) ^ (-a * (k : ℝ)) = ((3 : ℝ) ^ (-a)) ^ k := fun k => by
    rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  simp only [hpow]
  rw [← Finset.mul_sum]
  have hIoc : Finset.Ioc h N = Finset.Ico (h + 1) (N + 1) := by
    ext k; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
  rw [hIoc]
  have hg := geom_sum_Ico_le_of_lt_one (m := h + 1) (n := N + 1) hr0 hr1
  have h1r : 0 < 1 - (3 : ℝ) ^ (-a) := by linarith
  calc Cd * ∑ i ∈ Finset.Ico (h + 1) (N + 1), ((3 : ℝ) ^ (-a)) ^ i
      ≤ Cd * (((3 : ℝ) ^ (-a)) ^ (h + 1) / (1 - (3 : ℝ) ^ (-a))) :=
        mul_le_mul_of_nonneg_left hg hCd
    _ ≤ Cd * ((3 : ℝ) ^ (-a)) ^ h / (1 - (3 : ℝ) ^ (-a)) := by
        rw [mul_div_assoc]
        apply mul_le_mul_of_nonneg_left _ hCd
        apply div_le_div_of_nonneg_right _ h1r.le
        rw [pow_succ]
        exact mul_le_of_le_one_right (pow_nonneg hr0 _) hr1.le

theorem aux_prop_16_infrared_eq {d : ℕ} (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (ω₁ ω₂ : BilateralField d)
    (h1 : Tendsto (infraredPartialSum ω₁) atTop (𝓝 (H ω₁)))
    (h2 : Tendsto (infraredPartialSum ω₂) atTop (𝓝 (H ω₂)))
    (hagree : ∀ j : ℤ, 0 < j → ω₁ j = ω₂ j) : H ω₁ = H ω₂ := by
  have heq : infraredPartialSum ω₁ = infraredPartialSum ω₂ := by
    funext L
    unfold infraredPartialSum
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hagree (Int.ofNat (n + 1)) (by simp)]
  rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

theorem aux_prop_16_cutoff_eq {d : ℕ} (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (ω₁ ω₂ : BilateralField d) (N : ℕ) (hH : H ω₁ = H ω₂)
    (hagree : ∀ j : ℤ, -(N : ℤ) ≤ j → ω₁ j = ω₂ j) :
    cutoffPotential H ω₁ N = cutoffPotential H ω₂ N := by
  funext x
  unfold cutoffPotential
  rw [hH]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [hagree _ (by simp; omega)]

/-- The cutoff coefficient of the primitive Neumann response depends on the field only through
its cutoff potential. -/
theorem aux_prop_16_cpc_eq {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (ω₁ ω₂ : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hcut : cutoffPotential H ω₁ N = cutoffPotential H ω₂ N) :
    cutoffPositiveCoefficient M H ω₁ N z hr = cutoffPositiveCoefficient M H ω₂ N z hr := by
  have hcc : cutoffCoefficient M H ω₁ N = cutoffCoefficient M H ω₂ N := by
    funext x
    unfold cutoffCoefficient
    rw [hcut]
  have hcm : cutoffCoefficientCM M H ω₁ N z hr = cutoffCoefficientCM M H ω₂ N z hr := by
    ext x
    simp only [cutoffCoefficientCM, ContinuousMap.coe_mk, hcc]
  have key : ∀ (c₁ c₂ : C(closedCube z r hr, ℝ)) (h₁ : ∀ x, 0 < c₁ x) (h₂ : ∀ x, 0 < c₂ x),
      c₁ = c₂ →
      @normalizedContinuousPositiveCoefficient d (centeredCube z r hr) (closedCube z r hr)
          ⟨centeredCube_subset_closedCube z hr⟩ c₁ h₁ 1 one_pos =
        @normalizedContinuousPositiveCoefficient d (centeredCube z r hr) (closedCube z r hr)
          ⟨centeredCube_subset_closedCube z hr⟩ c₂ h₂ 1 one_pos := by
    intro c₁ c₂ h₁ h₂ hc
    subst hc
    rfl
  unfold cutoffPositiveCoefficient
  exact key _ _ _ _ hcm

end Prop16_A2_Small

section Prop16_B_Lem15
open MeasureTheory Filter Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology


section Prop16Lem15
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology Pointwise ContDiff

/-- The uniform single-layer replacement estimate of `lem_15` (proved by
`aux_lem_15_u_main`, whose Efron--Stein premise is unused: the BBLM constant is taken
from `aux_lem_15_bblm`).  Restated without that unused premise; the proof is the same. -/
theorem aux_prop_16_lem15
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (phi : SpatialCoordinates d → ℝ) (_hphi : ContDiff ℝ ∞ phi)
    (_hnonconst : ∃ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∃ y ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), phi x ≠ phi y)
    (b : weakSobolevGraph (centeredCube z r hr))
    (_hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi)
    (f : SpatialCoordinates d → ℝ) (_hf : ContDiff ℝ ∞ f)
    (_hfc : HasCompactSupport f)
    (_hfsupp : tsupport f ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (_hf0 : ∃ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), f x ≠ 0)
    (fL2 : DomainL2 (centeredCube z r hr))
    (_hfL2 : (fL2 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f)
    (t p B : ℝ) (ht_lower : (d : ℝ) - 1 < t) (_ht_upper : t < (d : ℝ))
    (hp : 2 ≤ p) (hB : 0 ≤ B) (dirichlet : Bool) :
    let S := killedResponseSpace hP
    let L := (sobolevVolumeLoad fL2).comp S.space.subtypeL
    ∃ C : ℝ, 0 < C ∧
      ∀ (delta : ℝ), 0 < delta → delta ≤ 1 →
        ∀ (Praw : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d))
          (_G1 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 d Praw)
          (_G2 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2 d delta Praw),
          let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
              C(SpatialCoordinates d, ℝ)) :=
            ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
          let nu := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
            forget.continuous.measurable.aemeasurable
          let P := (commonScaleLaw d nu).toMeasure
          ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
            Measurable H →
            (∀ᵐ omega ∂P,
              Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega))) →
          ∀ (kappa : ℕ → ℝ), (∀ N, 0 < kappa N) →
          ∀ (aN : ℕ → BilateralField d → PositiveCoefficient (centeredCube z r hr)),
            (∀ N omega,
              (aN N omega).val =ᵐ[volume.restrict
                (centeredCube z r hr : Set (SpatialCoordinates d))]
                (fun x => Real.exp (cutoffPotential H omega N x - Real.log (kappa N)))) →
          let RN : ℕ → BilateralField d → ℝ :=
            fun N omega =>
              if dirichlet then
                dirichletResponse S (aN N omega) b
              else
                inverseResponse S (aN N omega) L
          let gN : ℕ → BilateralField d → HilbertGradient (centeredCube z r hr) :=
            fun N omega =>
              if dirichlet then
                sobolevGradient (dirichletMinimizer S (aN N omega) b).val
              else
                subspaceGradient S.space (responseSolution S (aN N omega) L)
          ∀ (K : ℕ → BilateralField d → ℝ),
            ((∀ N, AEStronglyMeasurable (K N) P) ∧
            (∀ᵐ omega ∂P, ∀ N, 0 ≤ K N omega)) →
            (∀ᵐ omega ∂P, ∀ N, ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
              ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
                localGradientEnergy (aN N omega)
                  (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet
                  (gN N omega) ≤ K N omega * rho ^ t) →
            (∀ N,
              MemLp (K N) (ENNReal.ofReal (3 * p)) P ∧
              MemLp (RN N) (ENNReal.ofReal (3 * p)) P ∧
              eLpNorm (K N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B ∧
              eLpNorm (RN N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B) →
            ∀ (N j : ℕ), j ≤ N →
              eLpNorm
                (fun pair : BilateralField d × BilateralField d =>
                  RN N pair.1 -
                    RN N
                      (Function.update pair.1 (-(j : ℤ))
                        (pair.2 (-(j : ℤ)))))
                (ENNReal.ofReal p) (P.prod P) ≤
              ENNReal.ofReal
                (C * delta *
                  (3 : ℝ) ^
                  (-(t * (t - (d : ℝ) + 1) / (t + 1) /
                      (8 * Real.log 3)) * (j : ℝ)))
    := by
  intro S L
  have hd1 : 1 ≤ d := by omega
  have hsd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < d by omega))
  have hgeo := aux_lem_15_u_geom d hd1 (2 * Real.sqrt d) (by positivity)
  obtain ⟨Cd, hCd, hgeo⟩ := hgeo
  have hgeo2 := hgeo t ht_lower
  obtain ⟨hbpos, r0, hr0, _, hgeoR⟩ := hgeo2
  have hp0 : 0 < p := by linarith
  have hgam : 0 < t * (t - (d : ℝ) + 1) / (t + 1) / 12 := by positivity
  have hQne := aux_lem_15_u_Qt_nonempty z hr
  have hRt : 0 ≤ ‖z‖ + (r / 2 + 1) := by positivity
  have hQR := aux_lem_15_u_Qt_bound z r
  -- the uniform layer-moment bank
  have hLexp := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR p ((0 : ℕ) : ℝ) 2 _ hp0 (by norm_num) (by norm_num) hgam
  obtain ⟨Cexp, _, hLexp⟩ := hLexp
  have hLdel := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR (2 * p) ((1 : ℕ) : ℝ) 4 _ (by positivity) (by norm_num) (by norm_num) hgam
  obtain ⟨Cdel, hCdel, hLdel⟩ := hLdel
  have hLa := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR (2 * p) ((0 : ℕ) : ℝ) 7 _ (by positivity) (by norm_num) (by norm_num) hgam
  obtain ⟨Ca, hCa, hLa⟩ := hLa
  have hLb := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR (2 * p) ((1 : ℕ) : ℝ) 7 _ (by positivity) (by norm_num) (by norm_num) hgam
  obtain ⟨Cb, hCb, hLb⟩ := hLb
  have hLc := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR 1 ((0 : ℕ) : ℝ) 8 _ (by norm_num) (by norm_num) (by norm_num) hgam
  obtain ⟨Cc, hCc, hLc⟩ := hLc
  have hLe := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR 1 ((2 : ℕ) : ℝ) 8 _ (by norm_num) (by norm_num) (by norm_num) hgam
  obtain ⟨Ce, hCe, hLe⟩ := hLe
  have hL7 := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR (4 * p) ((1 : ℕ) : ℝ) 1 _ (by positivity) (by norm_num) (by norm_num) hgam
  obtain ⟨C7, hC7, hL7⟩ := hL7
  have hL8 := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR (4 * p) ((0 : ℕ) : ℝ) 1 _ (by positivity) (by norm_num) (by norm_num) hgam
  obtain ⟨C8, hC8, hL8⟩ := hL8
  -- the Efron–Stein constant (BBLM, proved in `aux_lem_15_bblm`)
  have hIES := in_efron_stein aux_lem_15_bblm p hp
  obtain ⟨Cp, hCp, hCpall⟩ := hIES
  have hCpall' : ∀ (m : ℕ) (mu : Fin m → Measure C(SpatialCoordinates d, ℝ))
      [∀ i, IsProbabilityMeasure (mu i)], aux_lem_15_u_ESProp mu p Cp := by
    intro m mu _
    exact (hCpall m (fun _ => C(SpatialCoordinates d, ℝ)) mu).1
  -- the initial scales
  have hj0 := exists_pow_lt_of_lt_one hr0 (by norm_num : (1 / 3 : ℝ) < 1)
  obtain ⟨j0, hj0⟩ := hj0
  refine ⟨(4 * Cd * (max 1 r) ^ d * Cdel * B +
      4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
        (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B) +
      2 * (C7 * C8) * B * (3 : ℝ) ^ (2 * (t * (t - (d : ℝ) + 1) / (t + 1) / 12) * j0) *
        (3 : ℝ) ^ (t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3) * j0) + 1,
    by positivity, ?_⟩
  intro delta hdelta hdelta1 Praw hG1 hG2 forget nu P H hHmeas hHconv kappa _ aN haN RN gN K
    hKmn hgrowth hmom N j hjN
  obtain ⟨hKm, hKnn⟩ := hKmn
  have hmomN := hmom N
  obtain ⟨_, _, hmomK, hmomR⟩ := hmomN
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have ha0 : 0 ≤ t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3) := by positivity
  have hrs : (0 : ℝ) < (3 : ℝ) ^ (-(j : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hY0 : 0 ≤ (3 : ℝ) ^ (-(t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3)) * (j : ℝ)) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  by_cases hj : j0 ≤ j
  · -- masking case
    have hrsr0 : (3 : ℝ) ^ (-(j : ℝ)) ≤ r0 := by
      have h1 : (3 : ℝ) ^ (-(j : ℝ)) = (1 / 3 : ℝ) ^ j := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]
      rw [h1]
      exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) hj).trans hj0.le
    have hgeom := hgeoR z r hr _ hrs hrsr0
    have hM1 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 0
      (hLexp delta hdelta hdelta1 Praw hG1 hG2 j)
    have hM2 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 1
      (hLdel delta hdelta hdelta1 Praw hG1 hG2 j)
    have hM3 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 0
      (hLa delta hdelta hdelta1 Praw hG1 hG2 j)
    have hM4 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 1
      (hLb delta hdelta hdelta1 Praw hG1 hG2 j)
    have hM5 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 0
      (hLc delta hdelta hdelta1 Praw hG1 hG2 j)
    have hM6 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 2
      (hLe delta hdelta hdelta1 Praw hG1 hG2 j)
    simp only [pow_zero, one_mul, pow_one, Real.rpow_natCast, ENNReal.ofReal_one,
      mul_one] at hM1 hM2 hM3 hM4 hM5 hM6
    have hmask := aux_lem_15_u_mask_case d hd z r hr S dirichlet b L t p B hp hB Cd hCd hbpos
      Cp hCp hCpall' _ Cdel Ca Cb Cc Ce hCdel.le hCa.le hCb.le hCc.le hCe.le delta hdelta
      hdelta1 Praw hG1 hG2 H hHmeas hHconv kappa aN haN K hKm hKnn hgrowth N j hjN hmomK
      hmomR _ rfl hgeom hM1 hM2 hM3 hM4 hM5 hM6
    refine hmask.trans (ENNReal.ofReal_le_ofReal ?_)
    have hexp := aux_lem_15_u_exponent (t * (t - (d : ℝ) + 1) / (t + 1)) hbpos.le j
    have hrw : ((3 : ℝ) ^ (-(j : ℝ))) ^ (3 * (t * (t - (d : ℝ) + 1) / (t + 1)) / 8) =
        (3 : ℝ) ^ (-(3 * (t * (t - (d : ℝ) + 1) / (t + 1)) / 8) * (j : ℝ)) := by
      rw [← Real.rpow_mul (by norm_num)]; congr 1; ring
    rw [hrw]
    have hK0 : 0 ≤ 4 * Cd * (max 1 r) ^ d * Cdel * B +
        4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
          (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B := by positivity
    have hKi : 0 ≤ 2 * (C7 * C8) * B * (3 : ℝ) ^ (2 * (t * (t - (d : ℝ) + 1) / (t + 1) / 12) * j0) *
        (3 : ℝ) ^ (t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3) * j0) := by positivity
    calc (4 * Cd * (max 1 r) ^ d * Cdel * B +
          4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
            (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B) * delta *
          (3 : ℝ) ^ (-(3 * (t * (t - (d : ℝ) + 1) / (t + 1)) / 8) * (j : ℝ))
        ≤ (4 * Cd * (max 1 r) ^ d * Cdel * B +
          4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
            (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B) * delta *
          (3 : ℝ) ^ (-(t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3)) * (j : ℝ)) := by
          gcongr
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hdelta.le) hY0
          linarith
  · -- initial scales
    push_neg at hj
    have hM7 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 1
      (hL7 delta hdelta hdelta1 Praw hG1 hG2 j)
    have hM8 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 0
      (hL8 delta hdelta hdelta1 Praw hG1 hG2 j)
    simp only [pow_zero, one_mul, pow_one, Real.rpow_natCast, mul_one] at hM7 hM8
    have hinit := aux_lem_15_u_init_case d hd z r hr S dirichlet b L t p B hp delta hdelta
      hdelta1 Praw hG1 hG2 H hHmeas hHconv kappa aN haN K hKnn hgrowth N j hjN hmomR _ _
      (by positivity) (by positivity) hM7 hM8
    refine hinit.trans (ENNReal.ofReal_le_ofReal ?_)
    have hnum := aux_lem_15_u_init_numeric C7 C8 B delta
      (t * (t - (d : ℝ) + 1) / (t + 1) / 12)
      (t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3)) j j0 hj.le hC7.le hC8.le hB
      hdelta.le hgam.le ha0
    have hK0 : 0 ≤ 4 * Cd * (max 1 r) ^ d * Cdel * B +
        4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
          (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B := by positivity
    have hd0 : 0 ≤ delta := hdelta.le
    refine hnum.trans ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hd0) hY0
    linarith

end Prop16Lem15

end Prop16_B_Lem15

section Prop16_D_Tail1
open MeasureTheory Filter Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Topology
open SubdiffusiveProcess


/-- A finite cover of a closed ball by balls of radius `1/4`, containing the origin. -/
theorem aux_prop_16_tail_cover (d : ℕ) (R : ℝ) :
    ∃ S : Finset (SpatialCoordinates d), S.Nonempty ∧
      ∀ x ∈ Metric.closedBall (0 : SpatialCoordinates d) R,
        ∃ z ∈ S, x ∈ Metric.ball z (1 / 4 : ℝ) := by
  classical
  obtain ⟨S₀, hS₀⟩ :=
    (isCompact_closedBall (0 : SpatialCoordinates d) R).elim_finite_subcover
      (fun z : SpatialCoordinates d => Metric.ball z (1 / 4 : ℝ))
      (fun _ => Metric.isOpen_ball) (by
        intro x hx
        exact mem_iUnion.2 ⟨x, Metric.mem_ball_self (by norm_num)⟩)
  refine ⟨insert 0 S₀, ⟨0, Finset.mem_insert_self 0 S₀⟩, ?_⟩
  intro x hx
  obtain ⟨z, hzS₀, hzx⟩ : ∃ z, ∃ (_ : z ∈ S₀), x ∈ Metric.ball z (1 / 4 : ℝ) := by
    simpa only [mem_iUnion] using hS₀ hx
  exact ⟨z, Finset.mem_insert_of_mem hzS₀, hzx⟩

/-- The translated `(g2)` observables over a fixed cover control the Lipschitz constant of a
potential field on the covered ball. -/
theorem aux_prop_16_tail_lip {d : ℕ} (R : ℝ) (S : Finset (SpatialCoordinates d))
    (hS : ∀ x ∈ Metric.closedBall (0 : SpatialCoordinates d) R,
      ∃ z ∈ S, x ∈ Metric.ball z (1 / 4 : ℝ))
    (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :
    LipschitzOnWith (∑ z ∈ S, (⟨SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z g),
        SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable_nonneg _⟩ : ℝ≥0))
      (fun x => g x) (Metric.closedBall (0 : SpatialCoordinates d) R) := by
  classical
  have hball_cube {z x : SpatialCoordinates d}
      (hx : x ∈ Metric.ball z (1 / 4 : ℝ)) :
      x - z ∈ Homogenization.openCubeSet (Homogenization.originCube d 0) := by
    have hxm : x - z ∈ Metric.ball (0 : SpatialCoordinates d) (1 / 2 : ℝ) := by
      have hxnorm : ‖x - z‖ < (1 / 4 : ℝ) := by
        simpa [Metric.mem_ball, dist_eq_norm] using hx
      have hx' : ‖x - z‖ < (1 / 2 : ℝ) := by linarith
      simpa [Metric.mem_ball, dist_zero_right, sub_zero] using hx'
    rw [← Homogenization.ball_cubeCenter_eq_openCubeSet]
    have hcenter : Homogenization.cubeCenter
        (Homogenization.originCube d 0) = (0 : SpatialCoordinates d) := by
      ext i
      simp [Homogenization.cubeCenter, Homogenization.originCube]
    have hradius : Homogenization.cubeRadius
        (Homogenization.originCube d 0) = (1 / 2 : ℝ) := by
      unfold Homogenization.cubeRadius
      rw [Homogenization.cubeScaleFactor_eq_one_of_scale_eq_zero]
      · norm_num
      · rfl
    rw [hcenter, hradius]
    exact hxm
  let Wnn : ℝ≥0 := ∑ z ∈ S, (⟨SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z g),
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable_nonneg _⟩ : ℝ≥0)
  have hderiv_bound {x : SpatialCoordinates d} (hx : x ∈ Metric.closedBall 0 R) :
      ‖SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g x‖ ≤ (Wnn : ℝ) := by
    obtain ⟨z, hzS, hzx⟩ := hS x hx
    have hlocal := SubdiffusiveProcess.Frozen.Assumptions.PotentialField.norm_deriv_le_g2Observable
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z g) (hball_cube hzx)
    have hderiv :
        fderiv ℝ ((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z g :
          SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :
          SpatialCoordinates d → ℝ) (x - z) =
          fderiv ℝ (fun y => g y) x := by
      simpa [SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate_apply, sub_add_cancel] using
        (fderiv_comp_add_right (𝕜 := ℝ) (f := (fun y => g y)) z
          (x := x - z))
    have hlocal' :
        ‖SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g x‖ ≤
          SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z g) := by
      calc
        ‖SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g x‖ =
            ‖fderiv ℝ (fun y => g y) x‖ := by
              rw [(g.hasFDerivAt x).fderiv]
        _ = ‖fderiv ℝ ((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z g :
              SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :
              SpatialCoordinates d → ℝ) (x - z)‖ := by rw [hderiv]
        _ = ‖(SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z g).deriv (x - z)‖ := by
              rw [(SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z g).hasFDerivAt
                (x - z) |>.fderiv]
        _ ≤ _ := hlocal
    have hcoe : (Wnn : ℝ) = ∑ y ∈ S, SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate y g) := by
      simp only [Wnn]
      rw [NNReal.coe_sum]
      rfl
    have hsum_le : SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z g) ≤
        ∑ y ∈ S, SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate y g) :=
      Finset.single_le_sum (f := fun y => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate y g))
        (fun y _ => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable_nonneg _) hzS
    rw [hcoe]
    exact hlocal'.trans hsum_le
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · intro x hx
    exact (g.hasFDerivAt x).differentiableAt
  · intro x hx
    have hb : (‖fderiv ℝ (fun y => g y) x‖₊ : ℝ) ≤ (Wnn : ℝ) := by
      have hb' := hderiv_bound hx
      change ‖g.deriv x‖ ≤ (Wnn : ℝ) at hb'
      simpa [(g.hasFDerivAt x).fderiv] using hb'
    exact NNReal.coe_le_coe.mp hb
  · exact convex_closedBall 0 R

/-- `(g2)` and stationarity: the translated-observable sum over a cover is sub-Gaussian with
parameter `card S · δ`. -/
theorem aux_prop_16_tail_W_orlicz {d : ℕ} (S : Finset (SpatialCoordinates d))
    (hS0 : S.Nonempty) (delta : ℝ) (hdelta : 0 < delta)
    (Praw : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d))
    (G1 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 d Praw)
    (G2 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2 d delta Praw) :
    ∫⁻ g, ENNReal.ofReal (Real.exp (((∑ z ∈ S,
        SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z g)) /
        ((S.card : ℝ) * delta)) ^ 2))
      ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure ≤ 2 := by
  classical
  set μ₀ := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).toMeasure with hμ₀
  have hone : ∫⁻ g, ENNReal.ofReal (Real.exp
      ((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable g / delta) ^ 2)) ∂μ₀ ≤ 2 := by
    obtain ⟨hint, hle⟩ := G2.regularity_expectation
    have heq : (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d => Real.exp ((delta⁻¹ *
          max (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable g) 0) ^ (2 : ℝ))) =
        fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d => Real.exp
          ((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable g / delta) ^ 2) := by
      funext g
      rw [max_eq_left (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable_nonneg g),
        Real.rpow_two, inv_mul_eq_div]
    rw [heq] at hint hle
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun g => (Real.exp_pos _).le)]
    calc ENNReal.ofReal (∫ g, Real.exp
          ((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable g / delta) ^ 2) ∂μ₀)
        ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hle
      _ = 2 := by norm_num
  have hF : Measurable (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
      ENNReal.ofReal (Real.exp
        ((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable g / delta) ^ 2))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable_measurable.div_const delta).pow_const
        2))
  have htr : ∀ z, ∫⁻ g, ENNReal.ofReal (Real.exp
      ((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z g) / delta) ^ 2)) ∂μ₀ ≤ 2 := by
    intro z
    have hmap : Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z) μ₀ = μ₀ :=
      G1.stationary z
    have h := lintegral_map hF (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_translate z)
      (μ := μ₀)
    rw [hmap] at h
    rw [← h]
    exact hone
  have hsum := SubdiffusiveProcess.lintegral_exp_sq_finset_sum_le μ₀ S
    (fun z g => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z g))
    (fun _ => delta) hS0
    (fun z _ => (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable_measurable.comp
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_translate z)).aestronglyMeasurable)
    (fun z _ => ae_of_all _ fun g =>
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable_nonneg _)
    (fun _ _ => hdelta) (fun z _ => htr z)
  simpa [Finset.sum_const, nsmul_eq_mul] using hsum

/-- The anchored sup-norm of a continuous field on a compact set. -/
def aux_prop_16_Y {d : ℕ} (K : Compacts (SpatialCoordinates d))
    (g : C(SpatialCoordinates d, ℝ)) : ℝ :=
  ‖(g - ContinuousMap.const _ (g 0)).restrict (K : Set (SpatialCoordinates d))‖

theorem aux_prop_16_Y_continuous {d : ℕ} (K : Compacts (SpatialCoordinates d)) :
    Continuous (aux_prop_16_Y K) := by
  unfold aux_prop_16_Y
  refine continuous_norm.comp ((ContinuousMap.continuous_restrict _).comp ?_)
  exact continuous_id.sub (ContinuousMap.continuous_const'.comp
    (continuous_eval_const (0 : SpatialCoordinates d)))

theorem aux_prop_16_Y_nonneg {d : ℕ} (K : Compacts (SpatialCoordinates d))
    (g : C(SpatialCoordinates d, ℝ)) : 0 ≤ aux_prop_16_Y K g := norm_nonneg _

theorem aux_prop_16_Y_le {d : ℕ} (K : Compacts (SpatialCoordinates d))
    (g : C(SpatialCoordinates d, ℝ)) {x : SpatialCoordinates d}
    (hx : x ∈ (K : Set (SpatialCoordinates d))) :
    |g x - g 0| ≤ aux_prop_16_Y K g := by
  have h := (ContinuousMap.norm_le
    ((g - ContinuousMap.const _ (g 0)).restrict (K : Set (SpatialCoordinates d)))
    (norm_nonneg _)).1 le_rfl ⟨x, hx⟩
  rw [ContinuousMap.restrict_apply, ContinuousMap.sub_apply, ContinuousMap.const_apply,
    Real.norm_eq_abs] at h
  exact h

/-- The anchored sup-norm of a rescaled layer is controlled by the Lipschitz majorant. -/
theorem aux_prop_16_Y_scaling {d : ℕ} (K : Compacts (SpatialCoordinates d)) (R : ℝ)
    (hR : 0 ≤ R) (hKR : ∀ x ∈ (K : Set (SpatialCoordinates d)), ‖x‖ ≤ R)
    (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) (W : ℝ≥0)
    (hW : LipschitzOnWith W (fun x => g x) (Metric.closedBall (0 : SpatialCoordinates d) R))
    (m : ℕ) :
    aux_prop_16_Y K (layerScaling d (m : ℤ) g.1.1) ≤
      R * (1 / 3 : ℝ) ^ m * (W : ℝ) := by
  have hc0 : 0 ≤ (1 / 3 : ℝ) ^ m := by positivity
  have hc1 : (1 / 3 : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hzpow : (3 : ℝ) ^ (-(m : ℤ)) = (1 / 3 : ℝ) ^ m := by
    rw [zpow_neg, zpow_natCast, one_div, inv_pow]
  unfold aux_prop_16_Y
  refine (ContinuousMap.norm_le _ (by positivity)).2 ?_
  intro x
  have hxK := x.2
  have hxR := hKR x hxK
  simp only [ContinuousMap.restrict_apply, ContinuousMap.sub_apply, ContinuousMap.const_apply,
    layerScaling, ContinuousMap.compRightContinuousMap_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, smul_zero, Real.norm_eq_abs]
  rw [hzpow]
  have hy : (1 / 3 : ℝ) ^ m • (x : SpatialCoordinates d) ∈
      Metric.closedBall (0 : SpatialCoordinates d) R := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hc0]
    nlinarith [norm_nonneg (x : SpatialCoordinates d)]
  have h0 : (0 : SpatialCoordinates d) ∈ Metric.closedBall (0 : SpatialCoordinates d) R :=
    Metric.mem_closedBall_self hR
  have hl := hW.dist_le_mul _ hy _ h0
  change dist (g.1.1 _) (g.1.1 0) ≤ _ at hl
  rw [Real.dist_eq, dist_zero_right, norm_smul, Real.norm_of_nonneg hc0] at hl
  calc |g.1.1 ((1 / 3 : ℝ) ^ m • (x : SpatialCoordinates d)) - g.1.1 0|
      ≤ (W : ℝ) * ((1 / 3 : ℝ) ^ m * ‖(x : SpatialCoordinates d)‖) := hl
    _ ≤ (W : ℝ) * ((1 / 3 : ℝ) ^ m * R) := by gcongr
    _ = R * (1 / 3 : ℝ) ^ m * (W : ℝ) := by ring

end Prop16_D_Tail1

section Prop16_D_Tail2
open MeasureTheory Filter Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Topology
open SubdiffusiveProcess


/-- Per-layer sub-Gaussian bound for the anchored sup-norm under the common-scale law. -/
theorem aux_prop_16_tail_layer_orlicz {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (K : Compacts (SpatialCoordinates d)) (R : ℝ) (hR : 0 < R)
    (hKR : ∀ x ∈ (K : Set (SpatialCoordinates d)), ‖x‖ ≤ R)
    (S : Finset (SpatialCoordinates d)) (hS0 : S.Nonempty)
    (hS : ∀ x ∈ Metric.closedBall (0 : SpatialCoordinates d) R,
      ∃ z ∈ S, x ∈ Metric.ball z (1 / 4 : ℝ))
    (delta : ℝ) (hdelta : 0 < delta)
    (Praw : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d))
    (G1 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 d Praw)
    (G2 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2 d delta Praw) (m : ℕ) :
    let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
        C(SpatialCoordinates d, ℝ)) :=
      ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
    let nu := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
      forget.continuous.measurable.aemeasurable
    ∫⁻ om, ENNReal.ofReal (Real.exp ((aux_prop_16_Y K (om (m : ℤ)) /
        (R * (1 / 3 : ℝ) ^ m * ((S.card : ℝ) * delta))) ^ 2))
      ∂(commonScaleLaw d nu).toMeasure ≤ 2 := by
  intro forget nu
  set A := R * (1 / 3 : ℝ) ^ m * ((S.card : ℝ) * delta) with hA_def
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS0.card_pos
  have hA : 0 < A := by positivity
  have hFm : Measurable (fun g : C(SpatialCoordinates d, ℝ) =>
      ENNReal.ofReal (Real.exp ((aux_prop_16_Y K g / A) ^ 2))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (((aux_prop_16_Y_continuous K).measurable.div_const A).pow_const 2))
  have hcoord : (commonScaleLaw d nu).toMeasure.map (fun om : BilateralField d => om (m : ℤ)) =
      (scaledLayerLaw d nu (m : ℤ) : Measure C(SpatialCoordinates d, ℝ)) :=
    Measure.infinitePi_map_eval _ (m : ℤ)
  rw [← lintegral_map hFm (measurable_pi_apply (m : ℤ)), hcoord]
  simp only [scaledLayerLaw, ProbabilityMeasure.toMeasure_map]
  rw [lintegral_map hFm (layerScaling d (m : ℤ)).continuous.measurable]
  simp only [nu, ProbabilityMeasure.toMeasure_map]
  have hFm2 : Measurable (fun g : C(SpatialCoordinates d, ℝ) =>
      ENNReal.ofReal (Real.exp ((aux_prop_16_Y K ((layerScaling d (m : ℤ)) g) / A) ^ 2))) :=
    hFm.comp (layerScaling d (m : ℤ)).continuous.measurable
  rw [lintegral_map hFm2 forget.continuous.measurable]
  refine le_trans (lintegral_mono fun G => ?_)
    (aux_prop_16_tail_W_orlicz S hS0 delta hdelta Praw G1 G2)
  have hlip := aux_prop_16_tail_lip R S hS G
  have hsc := aux_prop_16_Y_scaling K R hR.le hKR G _ hlip m
  rw [NNReal.coe_sum] at hsc
  simp only [NNReal.coe_mk] at hsc
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  apply pow_le_pow_left₀ (div_nonneg (aux_prop_16_Y_nonneg _ _) hA.le)
  have hY : aux_prop_16_Y K (layerScaling d (m : ℤ) (forget G)) / A ≤
      (R * (1 / 3 : ℝ) ^ m * ∑ z ∈ S, SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z G)) / A :=
    div_le_div_of_nonneg_right hsc hA.le
  refine hY.trans (le_of_eq ?_)
  rw [hA_def]
  have h3 : (0 : ℝ) < (1 / 3 : ℝ) ^ m := by positivity
  field_simp

/-- A countable family of nonnegative sub-Gaussian variables with summable parameters is
almost surely summable, and its sum is sub-Gaussian with the summed parameter. -/
theorem aux_prop_16_orlicz_tsum {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (X : ℕ → α → ℝ) (a : ℕ → ℝ)
    (hXm : ∀ n, Measurable (X n)) (hX0 : ∀ n q, 0 ≤ X n q) (ha : ∀ n, 0 < a n)
    (hsuma : Summable a)
    (hb : ∀ n, ∫⁻ q, ENNReal.ofReal (Real.exp ((X n q / a n) ^ 2)) ∂μ ≤ 2) :
    (∀ᵐ q ∂μ, Summable (fun n => X n q)) ∧
      ∫⁻ q, ENNReal.ofReal (Real.exp (((∑' n, X n q) / (∑' n, a n)) ^ 2)) ∂μ ≤ 2 := by
  have hlin : ∀ n, ∫⁻ q, ENNReal.ofReal (X n q) ∂μ ≤ ENNReal.ofReal (2 * a n) := by
    intro n
    have hpt : ∀ q, ENNReal.ofReal (X n q) ≤
        ENNReal.ofReal (a n) * ENNReal.ofReal (Real.exp ((X n q / a n) ^ 2)) := by
      intro q
      rw [← ENNReal.ofReal_mul (ha n).le]
      apply ENNReal.ofReal_le_ofReal
      have hyle : X n q / a n ≤ Real.exp ((X n q / a n) ^ 2) := by
        have := Real.add_one_le_exp ((X n q / a n) ^ 2)
        nlinarith [sq_nonneg (X n q / a n - 1 / 2)]
      have han := (ha n).ne'
      calc X n q = a n * (X n q / a n) := by field_simp
        _ ≤ a n * Real.exp ((X n q / a n) ^ 2) := mul_le_mul_of_nonneg_left hyle (ha n).le
    calc ∫⁻ q, ENNReal.ofReal (X n q) ∂μ
        ≤ ∫⁻ q, ENNReal.ofReal (a n) * ENNReal.ofReal (Real.exp ((X n q / a n) ^ 2)) ∂μ :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (a n) *
            ∫⁻ q, ENNReal.ofReal (Real.exp ((X n q / a n) ^ 2)) ∂μ :=
          lintegral_const_mul _ (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
            (((hXm n).div_const (a n)).pow_const 2)))
      _ ≤ ENNReal.ofReal (a n) * 2 := mul_le_mul_left' (hb n) _
      _ = ENNReal.ofReal (2 * a n) := by
          rw [ENNReal.ofReal_mul (by norm_num), mul_comm]; norm_num
  have htsum : ∫⁻ q, ∑' n, ENNReal.ofReal (X n q) ∂μ ≠ ⊤ := by
    rw [lintegral_tsum (f := fun n q => ENNReal.ofReal (X n q))
      (fun n => (ENNReal.measurable_ofReal.comp (hXm n)).aemeasurable)]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hlin)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by linarith [ha n]) (hsuma.mul_left 2)]
    exact ENNReal.ofReal_ne_top
  have hae : ∀ᵐ q ∂μ, ∑' n, ENNReal.ofReal (X n q) < ⊤ :=
    ae_lt_top (Measurable.ennreal_tsum fun n => ENNReal.measurable_ofReal.comp (hXm n)) htsum
  have hsumX : ∀ᵐ q ∂μ, Summable (fun n => X n q) := by
    filter_upwards [hae] with q hq
    have hs := ENNReal.summable_toReal hq.ne
    refine hs.congr fun n => ?_
    exact ENNReal.toReal_ofReal (hX0 n q)
  exact ⟨hsumX, SubdiffusiveProcess.lintegral_exp_sq_tsum_le μ X a
    (fun n => (hXm n).aestronglyMeasurable) (fun n => ae_of_all _ (hX0 n)) ha hsuma hsumX hb⟩

theorem aux_prop_16_tail_tsum_param (R c : ℝ) (h : ℕ) :
    Summable (fun n : ℕ => 2 * (R * (1 / 3 : ℝ) ^ (n + h + 1) * c)) ∧
      ∑' n : ℕ, 2 * (R * (1 / 3 : ℝ) ^ (n + h + 1) * c) = R * c * (1 / 3 : ℝ) ^ h := by
  have hgeom : Summable (fun n : ℕ => (1 / 3 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have h1 : (fun n : ℕ => 2 * (R * (1 / 3 : ℝ) ^ (n + h + 1) * c)) =
      fun n : ℕ => (2 * R * (1 / 3 : ℝ) ^ (h + 1) * c) * (1 / 3 : ℝ) ^ n := by
    funext n
    rw [show n + h + 1 = n + (h + 1) by omega, pow_add]
    ring
  rw [h1]
  refine ⟨hgeom.mul_left _, ?_⟩
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num), pow_succ]
  ring

end Prop16_D_Tail2

section Prop16_D_Tail2b
open MeasureTheory Filter Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Topology
open SubdiffusiveProcess


/-- Pairing two independent copies of a sub-Gaussian layer. -/
theorem aux_prop_16_tail_pair_gen {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P : Measure (BilateralField d)) [IsProbabilityMeasure P]
    (K : Compacts (SpatialCoordinates d)) (c : ℝ) (hc : 0 < c) (m : ℤ)
    (hlayer : ∫⁻ om, ENNReal.ofReal (Real.exp ((aux_prop_16_Y K (om m) / c) ^ 2)) ∂P ≤ 2) :
    ∫⁻ q, ENNReal.ofReal (Real.exp (((aux_prop_16_Y K (q.2 m) +
      aux_prop_16_Y K (q.1 m)) / (2 * c)) ^ 2)) ∂(P.prod P) ≤ 2 := by
  have hYm : Measurable (fun om : BilateralField d => aux_prop_16_Y K (om m)) :=
    (aux_prop_16_Y_continuous K).measurable.comp (measurable_pi_apply m)
  have hFm : Measurable (fun om : BilateralField d =>
      ENNReal.ofReal (Real.exp ((aux_prop_16_Y K (om m) / c) ^ 2))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((hYm.div_const c).pow_const 2))
  have hsnd : ∫⁻ q, ENNReal.ofReal (Real.exp ((aux_prop_16_Y K (q.2 m) / c) ^ 2))
      ∂(P.prod P) ≤ 2 := by
    rw [(measurePreserving_snd : MeasurePreserving Prod.snd (P.prod P) P).lintegral_comp hFm]
    exact hlayer
  have hfst : ∫⁻ q, ENNReal.ofReal (Real.exp ((aux_prop_16_Y K (q.1 m) / c) ^ 2))
      ∂(P.prod P) ≤ 2 := by
    rw [(measurePreserving_fst : MeasurePreserving Prod.fst (P.prod P) P).lintegral_comp hFm]
    exact hlayer
  have hsum := SubdiffusiveProcess.lintegral_exp_sq_finset_sum_le (P.prod P)
    (Finset.univ : Finset Bool)
    (fun b q => if b then aux_prop_16_Y K (q.2 m) else aux_prop_16_Y K (q.1 m))
    (fun _ => c) Finset.univ_nonempty
    (fun b _ => by
      cases b
      · exact (hYm.comp measurable_fst).aestronglyMeasurable
      · exact (hYm.comp measurable_snd).aestronglyMeasurable)
    (fun b _ => ae_of_all _ fun q => by
      cases b
      · exact aux_prop_16_Y_nonneg _ _
      · exact aux_prop_16_Y_nonneg _ _)
    (fun _ _ => hc)
    (fun b _ => by
      cases b
      · simpa using hfst
      · simpa using hsnd)
  simpa [Fintype.sum_bool, two_mul] using hsum

/-- Countable coarse-layer sum over an abstract probability law with per-layer sub-Gaussian
bounds `R 3^{-m} c`. -/
theorem aux_prop_16_tail_sum_gen {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P : Measure (BilateralField d)) [IsProbabilityMeasure P]
    (K : Compacts (SpatialCoordinates d)) (R c : ℝ) (hR : 0 < R) (hc : 0 < c) (h : ℕ)
    (hlayer : ∀ m : ℕ, ∫⁻ om, ENNReal.ofReal (Real.exp ((aux_prop_16_Y K (om (m : ℤ)) /
      (R * (1 / 3 : ℝ) ^ m * c)) ^ 2)) ∂P ≤ 2) :
    (∀ᵐ q ∂(P.prod P), Summable (fun n : ℕ =>
        aux_prop_16_Y K (q.2 ((n + h + 1 : ℕ) : ℤ)) +
          aux_prop_16_Y K (q.1 ((n + h + 1 : ℕ) : ℤ)))) ∧
    ∫⁻ q, ENNReal.ofReal (Real.exp (((∑' n : ℕ,
        (aux_prop_16_Y K (q.2 ((n + h + 1 : ℕ) : ℤ)) +
          aux_prop_16_Y K (q.1 ((n + h + 1 : ℕ) : ℤ)))) /
        (R * c * (1 / 3 : ℝ) ^ h)) ^ 2)) ∂(P.prod P) ≤ 2 := by
  obtain ⟨hsuma, htsa⟩ := aux_prop_16_tail_tsum_param R c h
  have hYm : ∀ m : ℤ, Measurable (fun om : BilateralField d => aux_prop_16_Y K (om m)) :=
    fun m => (aux_prop_16_Y_continuous K).measurable.comp (measurable_pi_apply m)
  have hXm : ∀ n : ℕ, Measurable (fun q : BilateralField d × BilateralField d =>
      aux_prop_16_Y K (q.2 ((n + h + 1 : ℕ) : ℤ)) +
        aux_prop_16_Y K (q.1 ((n + h + 1 : ℕ) : ℤ))) := fun n =>
    ((hYm ((n + h + 1 : ℕ) : ℤ)).comp measurable_snd).add
      ((hYm ((n + h + 1 : ℕ) : ℤ)).comp measurable_fst)
  have hb : ∀ n : ℕ, ∫⁻ q, ENNReal.ofReal (Real.exp (((aux_prop_16_Y K (q.2 ((n + h + 1 : ℕ) : ℤ)) +
      aux_prop_16_Y K (q.1 ((n + h + 1 : ℕ) : ℤ))) /
      (2 * (R * (1 / 3 : ℝ) ^ (n + h + 1) * c))) ^ 2)) ∂(P.prod P) ≤ 2 := fun n =>
    aux_prop_16_tail_pair_gen P K _ (by positivity) _ (hlayer (n + h + 1))
  have hres := aux_prop_16_orlicz_tsum (P.prod P)
    (fun n q => aux_prop_16_Y K (q.2 ((n + h + 1 : ℕ) : ℤ)) +
      aux_prop_16_Y K (q.1 ((n + h + 1 : ℕ) : ℤ)))
    (fun n => 2 * (R * (1 / 3 : ℝ) ^ (n + h + 1) * c))
    hXm (fun n q => add_nonneg (aux_prop_16_Y_nonneg _ _) (aux_prop_16_Y_nonneg _ _))
    (fun n => by positivity) hsuma hb
  rw [htsa] at hres
  exact hres

end Prop16_D_Tail2b

section Prop16_D_Tail3
open MeasureTheory Filter Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Topology
open SubdiffusiveProcess


/-- On the infrared convergence events and the summability event, the coarse tail equals the
sup-norm of the infrared difference on the closed cube, and is dominated by the layer sum. -/
theorem aux_prop_16_tail_bridge {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (K : Compacts (SpatialCoordinates d))
    (hK : (K : Set (SpatialCoordinates d)) = Metric.closedBall z (r / 2))
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (h : ℕ)
    (q : BilateralField d × BilateralField d)
    (h1 : Tendsto (infraredPartialSum q.1) atTop (𝓝 (H q.1)))
    (h2 : Tendsto (infraredPartialSum (fun j => if (h : ℤ) < j then q.2 j else q.1 j)) atTop
      (𝓝 (H (fun j => if (h : ℤ) < j then q.2 j else q.1 j))))
    (hsum : Summable (fun n : ℕ => aux_prop_16_Y K (q.2 ((n + h + 1 : ℕ) : ℤ)) +
      aux_prop_16_Y K (q.1 ((n + h + 1 : ℕ) : ℤ)))) :
    sSup ((fun x : SpatialCoordinates d =>
        |∑' n : ℕ,
          ((q.2 ((n : ℤ) + (h : ℤ) + 1) x - q.2 ((n : ℤ) + (h : ℤ) + 1) 0) -
            (q.1 ((n : ℤ) + (h : ℤ) + 1) x - q.1 ((n : ℤ) + (h : ℤ) + 1) 0))|) ''
        (centeredCube z r hr : Set (SpatialCoordinates d))) =
      ‖(H (fun j => if (h : ℤ) < j then q.2 j else q.1 j) - H q.1).restrict
        (K : Set (SpatialCoordinates d))‖ ∧
    ‖(H (fun j => if (h : ℤ) < j then q.2 j else q.1 j) - H q.1).restrict
        (K : Set (SpatialCoordinates d))‖ ≤
      ∑' n : ℕ, (aux_prop_16_Y K (q.2 ((n + h + 1 : ℕ) : ℤ)) +
        aux_prop_16_Y K (q.1 ((n + h + 1 : ℕ) : ℤ))) := by
  set T : BilateralField d := fun j => if (h : ℤ) < j then q.2 j else q.1 j with hT
  set D : C(SpatialCoordinates d, ℝ) := H T - H q.1 with hD_def
  set X : ℕ → ℝ := fun n => aux_prop_16_Y K (q.2 ((n + h + 1 : ℕ) : ℤ)) +
    aux_prop_16_Y K (q.1 ((n + h + 1 : ℕ) : ℤ)) with hX_def
  set Q : Set (SpatialCoordinates d) := (centeredCube z r hr : Set (SpatialCoordinates d))
    with hQ_def
  let w : ℕ → SpatialCoordinates d → ℝ := fun n x =>
    (q.2 ((n : ℤ) + (h : ℤ) + 1) x - q.2 ((n : ℤ) + (h : ℤ) + 1) 0) -
      (q.1 ((n : ℤ) + (h : ℤ) + 1) x - q.1 ((n : ℤ) + (h : ℤ) + 1) 0)
  have hQK : Q ⊆ (K : Set (SpatialCoordinates d)) := by
    intro x hx
    rw [hK]
    exact Metric.mem_closedBall.mpr (Metric.mem_ball.mp hx).le
  have hcast : ∀ n : ℕ, (((n + h + 1 : ℕ) : ℤ)) = (n : ℤ) + (h : ℤ) + 1 := fun n => by
    push_cast; ring
  have hX0 : ∀ n, 0 ≤ X n := fun n =>
    add_nonneg (aux_prop_16_Y_nonneg _ _) (aux_prop_16_Y_nonneg _ _)
  have hw_bound : ∀ x ∈ (K : Set (SpatialCoordinates d)), ∀ n, |w n x| ≤ X n := by
    intro x hx n
    have e1 := aux_prop_16_Y_le K (q.2 ((n + h + 1 : ℕ) : ℤ)) hx
    have e2 := aux_prop_16_Y_le K (q.1 ((n + h + 1 : ℕ) : ℤ)) hx
    rw [hcast] at e1 e2
    have hX' : X n = aux_prop_16_Y K (q.2 ((n : ℤ) + (h : ℤ) + 1)) +
        aux_prop_16_Y K (q.1 ((n : ℤ) + (h : ℤ) + 1)) := by
      simp only [hX_def, hcast]
    rw [hX']
    exact (abs_sub _ _).trans (add_le_add e1 e2)
  have hw_sum : ∀ x ∈ (K : Set (SpatialCoordinates d)), Summable (fun n => w n x) :=
    fun x hx => Summable.of_norm_bounded hsum
      (fun n => by rw [Real.norm_eq_abs]; exact hw_bound x hx n)
  have hD : ∀ x ∈ (K : Set (SpatialCoordinates d)), ∑' n, w n x = D x := by
    intro x hx
    let v : ℕ → ℝ := fun n =>
      (T (Int.ofNat (n + 1)) x - T (Int.ofNat (n + 1)) 0) -
        (q.1 (Int.ofNat (n + 1)) x - q.1 (Int.ofNat (n + 1)) 0)
    have htend : Tendsto (fun L => ∑ n ∈ Finset.range L, v n) atTop (𝓝 (D x)) := by
      have hc := ((continuous_eval_const x).tendsto _).comp (h2.sub h1)
      refine Tendsto.congr (fun L => ?_) hc
      simp only [Function.comp_apply, ContinuousMap.sub_apply, infraredPartialSum,
        ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.const_apply, v,
        ContinuousMap.coe_sub, Pi.sub_apply]
      rw [← Finset.sum_sub_distrib]
    have hv0 : ∀ n, n < h → v n = 0 := by
      intro n hn
      have hne : ¬ (h : ℤ) < Int.ofNat (n + 1) := by
        rw [Int.ofNat_eq_coe]; push_cast; omega
      simp only [v, hT, if_neg hne, sub_self]
    have hvh : ∀ n, v (n + h) = w n x := by
      intro n
      have e : Int.ofNat (n + h + 1) = (n : ℤ) + (h : ℤ) + 1 := by
        rw [Int.ofNat_eq_coe]; push_cast; ring
      have hlt : (h : ℤ) < Int.ofNat (n + h + 1) := by rw [e]; omega
      simp only [v, w, hT, if_pos hlt]
      rw [e]
    have hvs : Summable v := by
      refine (summable_nat_add_iff h).mp ?_
      have hfun : (fun n => v (n + h)) = fun n => w n x := funext hvh
      rw [hfun]
      exact hw_sum x hx
    have h1' : ∑' n, v n = D x := tendsto_nhds_unique hvs.hasSum.tendsto_sum_nat htend
    rw [← h1', ← hvs.sum_add_tsum_nat_add h,
      Finset.sum_eq_zero (fun n hn => hv0 n (Finset.mem_range.mp hn)), zero_add]
    exact tsum_congr (fun n => (hvh n).symm)
  have hQne : Q.Nonempty := ⟨z, Metric.mem_ball_self (half_pos hr)⟩
  have himg : (fun x => |∑' n, w n x|) '' Q = (fun x => |D x|) '' Q :=
    Set.image_congr (fun x hx => by rw [hD x (hQK hx)])
  have hbnd : ∀ x ∈ Q, |D x| ≤ ‖D.restrict (K : Set (SpatialCoordinates d))‖ := by
    intro x hx
    have := (ContinuousMap.norm_le (D.restrict (K : Set (SpatialCoordinates d)))
      (norm_nonneg _)).1 le_rfl ⟨x, hQK hx⟩
    rw [ContinuousMap.restrict_apply, Real.norm_eq_abs] at this
    exact this
  have hbdd : BddAbove ((fun x => |D x|) '' Q) := by
    refine ⟨‖D.restrict (K : Set (SpatialCoordinates d))‖, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hbnd x hx
  have hle1 : sSup ((fun x => |D x|) '' Q) ≤ ‖D.restrict (K : Set (SpatialCoordinates d))‖ := by
    refine csSup_le (hQne.image _) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hbnd x hx
  have hle2 : ‖D.restrict (K : Set (SpatialCoordinates d))‖ ≤ sSup ((fun x => |D x|) '' Q) := by
    have hs0 : 0 ≤ sSup ((fun x => |D x|) '' Q) := by
      apply Real.sSup_nonneg
      rintro _ ⟨x, _, rfl⟩
      exact abs_nonneg _
    refine (ContinuousMap.norm_le _ hs0).2 fun x => ?_
    have hclosed : IsClosed {y : SpatialCoordinates d | |D y| ≤ sSup ((fun x => |D x|) '' Q)} :=
      isClosed_le (continuous_abs.comp D.continuous) continuous_const
    have hsub : Q ⊆ {y : SpatialCoordinates d | |D y| ≤ sSup ((fun x => |D x|) '' Q)} :=
      fun y hy => le_csSup hbdd ⟨y, hy, rfl⟩
    have hcl : closure Q = Metric.closedBall z (r / 2) := by
      simp [hQ_def, centeredCube, closure_ball, ne_of_gt (half_pos hr)]
    have hxK : (x : SpatialCoordinates d) ∈ closure Q := by
      rw [hcl, ← hK]
      exact x.2
    have hx := (hclosed.closure_subset_iff.2 hsub) hxK
    simpa [Real.norm_eq_abs] using hx
  refine ⟨?_, ?_⟩
  · change sSup ((fun x => |∑' n, w n x|) '' Q) = _
    rw [himg]
    exact le_antisymm hle1 hle2
  · refine (ContinuousMap.norm_le _ (tsum_nonneg hX0)).2 fun x => ?_
    have hx : (x : SpatialCoordinates d) ∈ (K : Set (SpatialCoordinates d)) := x.2
    rw [ContinuousMap.restrict_apply, Real.norm_eq_abs, ← hD x hx]
    have habs : Summable (fun n => ‖w n x‖) :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _)
        (fun n => by rw [Real.norm_eq_abs]; exact hw_bound x hx n) hsum
    calc |∑' n, w n x| = ‖∑' n, w n x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑' n, ‖w n x‖ := norm_tsum_le_tsum_norm habs
      _ ≤ ∑' n, X n := habs.tsum_le_tsum
          (fun n => by rw [Real.norm_eq_abs]; exact hw_bound x hx n) hsum

/-- The coarse-block tail moments (sub-Gaussian in `q`, uniform exponential moments). -/
theorem aux_prop_16_coarse_tail (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ Ctail : ℝ, 0 < Ctail ∧
      ∀ (delta : ℝ), 0 < delta → delta ≤ 1 →
        ∀ (Praw : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d))
          (_G1 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 d Praw)
          (_G2 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2 d delta Praw),
          let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
              C(SpatialCoordinates d, ℝ)) :=
            ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
          let nu := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
            forget.continuous.measurable.aemeasurable
          let P := (commonScaleLaw d nu).toMeasure
          ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
            Measurable H →
            (∀ᵐ omega ∂P,
              Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega))) →
          let coarseTail : ℕ → (BilateralField d × BilateralField d) → ℝ :=
            fun h pair =>
              sSup ((fun x : SpatialCoordinates d =>
                |∑' n : ℕ,
                  ((pair.2 ((n : ℤ) + (h : ℤ) + 1) x -
                      pair.2 ((n : ℤ) + (h : ℤ) + 1) 0) -
                    (pair.1 ((n : ℤ) + (h : ℤ) + 1) x -
                      pair.1 ((n : ℤ) + (h : ℤ) + 1) 0))|) ''
                (centeredCube z r hr : Set (SpatialCoordinates d)))
          (∀ (h : ℕ) (q : ℝ), 2 ≤ q →
              MemLp (coarseTail h) (ENNReal.ofReal q) (P.prod P) ∧
              eLpNorm (coarseTail h) (ENNReal.ofReal q) (P.prod P) ≤
                ENNReal.ofReal (Ctail * delta * Real.sqrt q *
                  (3 : ℝ) ^ (-(h : ℝ)))) ∧
            (∀ (lambda : ℝ), 0 ≤ lambda →
              ∃ C_lambda : ℝ, 0 < C_lambda ∧
                ∀ h : ℕ,
                  Integrable (fun pair =>
                    Real.exp (lambda * coarseTail h pair)) (P.prod P) ∧
                  (∫ pair, Real.exp (lambda * coarseTail h pair) ∂(P.prod P)) ≤
                    C_lambda) := by
  obtain ⟨Cu, hCu, horl⟩ := SubdiffusiveProcess.exists_universal_orlicz_eLpNorm_constant
  set R : ℝ := ‖z‖ + r / 2 with hR_def
  have hR : 0 < R := by positivity
  obtain ⟨S, hS0, hS⟩ := aux_prop_16_tail_cover d R
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS0.card_pos
  refine ⟨Cu * (R * S.card), by positivity, ?_⟩
  intro delta hdelta hdelta1 Praw G1 G2 forget nu P H hH hHconv coarseTail
  let K : Compacts (SpatialCoordinates d) :=
    ⟨Metric.closedBall z (r / 2), isCompact_closedBall z (r / 2)⟩
  have hK : (K : Set (SpatialCoordinates d)) = Metric.closedBall z (r / 2) := rfl
  have hKR : ∀ x ∈ (K : Set (SpatialCoordinates d)), ‖x‖ ≤ R := by
    intro x hx
    have hdist : dist x z ≤ r / 2 := Metric.mem_closedBall.mp hx
    calc ‖x‖ = ‖(x - z) + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
      _ = dist x z + ‖z‖ := by rw [dist_eq_norm]
      _ ≤ R := by rw [hR_def]; linarith
  have hmain : ∀ h : ℕ, ∃ V : BilateralField d × BilateralField d → ℝ,
      Measurable V ∧ (∀ q, 0 ≤ V q) ∧ (coarseTail h =ᵐ[P.prod P] V) ∧
      ∫⁻ q, ENNReal.ofReal (Real.exp ((V q / (R * ((S.card : ℝ) * delta) *
        (1 / 3 : ℝ) ^ h)) ^ 2)) ∂(P.prod P) ≤ 2 := by
    intro h
    let T : BilateralField d × BilateralField d → BilateralField d :=
      fun q j => if (h : ℤ) < j then q.2 j else q.1 j
    have hTmp : MeasurePreserving T (P.prod P) P :=
      measurePreserving_copy_infinitePi_block
        (fun j : ℤ => (scaledLayerLaw d nu j : Measure C(SpatialCoordinates d, ℝ)))
        {j : ℤ | (h : ℤ) < j}
    let V : BilateralField d × BilateralField d → ℝ := fun q =>
      ‖(H (T q) - H q.1).restrict (K : Set (SpatialCoordinates d))‖
    have hVm : Measurable V :=
      (continuous_norm.comp (ContinuousMap.continuous_restrict
        (K : Set (SpatialCoordinates d)))).measurable.comp
        ((hH.comp hTmp.measurable).sub (hH.comp measurable_fst))
    have hlayer : ∀ m : ℕ, ∫⁻ om, ENNReal.ofReal (Real.exp ((aux_prop_16_Y K (om (m : ℤ)) /
        (R * (1 / 3 : ℝ) ^ m * ((S.card : ℝ) * delta))) ^ 2)) ∂P ≤ 2 := fun m => by
      have hl := aux_prop_16_tail_layer_orlicz K R hR hKR S hS0 hS delta hdelta Praw G1 G2 m
      simpa only using hl
    obtain ⟨hsumae, horlZ⟩ :=
      aux_prop_16_tail_sum_gen P K R ((S.card : ℝ) * delta) hR (by positivity) h hlayer
    have hconv1 : ∀ᵐ q ∂(P.prod P), Tendsto (infraredPartialSum q.1) atTop (𝓝 (H q.1)) :=
      (measurePreserving_fst : MeasurePreserving Prod.fst (P.prod P) P).quasiMeasurePreserving.ae
        hHconv
    have hconvT : ∀ᵐ q ∂(P.prod P),
        Tendsto (infraredPartialSum (T q)) atTop (𝓝 (H (T q))) :=
      hTmp.quasiMeasurePreserving.ae hHconv
    have hbr : ∀ᵐ q ∂(P.prod P), coarseTail h q = V q ∧
        V q ≤ ∑' n : ℕ, (aux_prop_16_Y K (q.2 ((n + h + 1 : ℕ) : ℤ)) +
          aux_prop_16_Y K (q.1 ((n + h + 1 : ℕ) : ℤ))) := by
      filter_upwards [hconv1, hconvT, hsumae] with q hq1 hq2 hq3
      exact aux_prop_16_tail_bridge z r hr K hK H h q hq1 hq2 hq3
    have hA : 0 < R * ((S.card : ℝ) * delta) * (1 / 3 : ℝ) ^ h := by positivity
    refine ⟨V, hVm, fun q => norm_nonneg _, ?_, ?_⟩
    · filter_upwards [hbr] with q hq
      exact hq.1
    · refine le_trans (lintegral_mono_ae ?_) horlZ
      filter_upwards [hbr] with q hq
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      apply pow_le_pow_left₀ (div_nonneg (norm_nonneg _) hA.le)
      exact div_le_div_of_nonneg_right hq.2 hA.le
  refine ⟨fun h q hq => ?_, fun lambda hlambda => ?_⟩
  · obtain ⟨V, hVm, hV0, hVeq, hVorl⟩ := hmain h
    have hA : 0 < R * ((S.card : ℝ) * delta) * (1 / 3 : ℝ) ^ h := by positivity
    have hq' : (2 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
      have := ENNReal.ofReal_le_ofReal hq
      rwa [ENNReal.ofReal_ofNat] at this
    have hb := horl (P.prod P) V _ hVm hV0 hA hVorl (ENNReal.ofReal q) ENNReal.ofReal_ne_top hq'
    rw [ENNReal.toReal_ofReal (by linarith)] at hb
    have heL : eLpNorm (coarseTail h) (ENNReal.ofReal q) (P.prod P) =
        eLpNorm V (ENNReal.ofReal q) (P.prod P) := eLpNorm_congr_ae hVeq
    have h3 : (1 / 3 : ℝ) ^ h = (3 : ℝ) ^ (-(h : ℝ)) := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]
    refine ⟨⟨hVm.aestronglyMeasurable.congr hVeq.symm, ?_⟩, ?_⟩
    · rw [heL]
      exact hb.trans_lt ENNReal.ofReal_lt_top
    · rw [heL]
      refine hb.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
      rw [← h3]
      ring
  · refine ⟨2 * Real.exp (lambda ^ 2 * (R * S.card) ^ 2 / 4), by positivity, fun h => ?_⟩
    obtain ⟨V, hVm, hV0, hVeq, hVorl⟩ := hmain h
    set A := R * ((S.card : ℝ) * delta) * (1 / 3 : ℝ) ^ h with hA_def
    have hA : 0 < A := by positivity
    have hA1 : A ≤ R * S.card := by
      have h13 : (1 / 3 : ℝ) ^ h ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hRc : 0 ≤ R * S.card := by positivity
      calc A = (R * S.card) * (delta * (1 / 3 : ℝ) ^ h) := by rw [hA_def]; ring
        _ ≤ (R * S.card) * (1 * 1) := by
            apply mul_le_mul_of_nonneg_left _ hRc
            exact mul_le_mul hdelta1 h13 (by positivity) (by norm_num)
        _ = R * S.card := by ring
    have hpt : ∀ q, Real.exp (lambda * V q) ≤
        Real.exp (lambda ^ 2 * A ^ 2 / 4) * Real.exp ((V q / A) ^ 2) := by
      intro q
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hVA : V q = A * (V q / A) := by field_simp
      rw [hVA]
      have hy := sq_nonneg (V q / A - lambda * A / 2)
      rw [mul_div_cancel_left₀ _ hA.ne']
      nlinarith [hy]
    have hEm : Measurable (fun q => Real.exp (lambda * V q)) :=
      Real.measurable_exp.comp (hVm.const_mul lambda)
    have hlint : ∫⁻ q, ENNReal.ofReal (Real.exp (lambda * V q)) ∂(P.prod P) ≤
        ENNReal.ofReal (2 * Real.exp (lambda ^ 2 * A ^ 2 / 4)) := by
      calc ∫⁻ q, ENNReal.ofReal (Real.exp (lambda * V q)) ∂(P.prod P)
          ≤ ∫⁻ q, ENNReal.ofReal (Real.exp (lambda ^ 2 * A ^ 2 / 4)) *
              ENNReal.ofReal (Real.exp ((V q / A) ^ 2)) ∂(P.prod P) :=
            lintegral_mono (fun q => by
              rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
              exact ENNReal.ofReal_le_ofReal (hpt q))
        _ = ENNReal.ofReal (Real.exp (lambda ^ 2 * A ^ 2 / 4)) *
              ∫⁻ q, ENNReal.ofReal (Real.exp ((V q / A) ^ 2)) ∂(P.prod P) :=
            lintegral_const_mul _ (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
              ((hVm.div_const A).pow_const 2)))
        _ ≤ ENNReal.ofReal (Real.exp (lambda ^ 2 * A ^ 2 / 4)) * 2 :=
            mul_le_mul_left' hVorl _
        _ = ENNReal.ofReal (2 * Real.exp (lambda ^ 2 * A ^ 2 / 4)) := by
            rw [ENNReal.ofReal_mul (by norm_num), mul_comm]
            norm_num
    have hInt : Integrable (fun q => Real.exp (lambda * V q)) (P.prod P) := by
      refine ⟨hEm.aestronglyMeasurable, ?_⟩
      unfold HasFiniteIntegral
      have hfun : (fun q => ‖Real.exp (lambda * V q)‖ₑ) =
          fun q => ENNReal.ofReal (Real.exp (lambda * V q)) := by
        funext q
        exact Real.enorm_of_nonneg (Real.exp_pos _).le
      rw [hfun]
      exact hlint.trans_lt ENNReal.ofReal_lt_top
    have hcongr : (fun q => Real.exp (lambda * coarseTail h q)) =ᵐ[P.prod P]
        (fun q => Real.exp (lambda * V q)) := by
      filter_upwards [hVeq] with q hq
      rw [hq]
    refine ⟨hInt.congr hcongr.symm, ?_⟩
    rw [integral_congr_ae hcongr, integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun q => (Real.exp_pos _).le) hEm.aestronglyMeasurable]
    have hmono := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlint
    rw [ENNReal.toReal_ofReal (by positivity)] at hmono
    refine hmono.trans ?_
    have hA2 : A ^ 2 ≤ (R * S.card) ^ 2 := pow_le_pow_left₀ hA.le hA1 2
    have hl2 : 0 ≤ lambda ^ 2 := sq_nonneg _
    gcongr

end Prop16_D_Tail3

section Prop16_C_Clause1
open MeasureTheory Filter Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Topology
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.Lane3


theorem aux_prop_16_dirichlet :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ ∞ phi)
    (hnonconst : ∃ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∃ y ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), phi x ≠ phi y)
    (b : weakSobolevGraph (centeredCube z r hr))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi)
    (f : SpatialCoordinates d → ℝ) (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f)
    (hfsupp : tsupport f ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hf0 : ∃ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), f x ≠ 0)
    (fL2 : DomainL2 (centeredCube z r hr))
    (hfL2 : (fL2 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f)
    (t p B : ℝ) (ht_lower : (d : ℝ) - 1 < t) (ht_upper : t < (d : ℝ))
    (hp : 2 ≤ p) (hB : 0 ≤ B) (dirichlet : Bool),
    let S := killedResponseSpace hP
    let L := (sobolevVolumeLoad fL2).comp S.space.subtypeL
    ∃ C : ℝ, 0 < C ∧
      ∀ (delta : ℝ), 0 < delta → delta ≤ 1 →
        ∀ (Praw : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d))
          (_G1 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 d Praw)
          (_G2 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2 d delta Praw),
          let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
              C(SpatialCoordinates d, ℝ)) :=
            ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
          let nu := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
            forget.continuous.measurable.aemeasurable
          let P := (commonScaleLaw d nu).toMeasure
          ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
            Measurable H →
            (∀ᵐ omega ∂P,
              Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega))) →
            ∀ (kappa : ℕ → ℝ), (∀ N, 0 < kappa N) →
            ∀ (aN : ℕ → BilateralField d → PositiveCoefficient (centeredCube z r hr)),
              (∀ N omega,
                (aN N omega).val =ᵐ[volume.restrict
                  (centeredCube z r hr : Set (SpatialCoordinates d))]
                  (fun x => Real.exp (cutoffPotential H omega N x - Real.log (kappa N)))) →
            let RN : ℕ → BilateralField d → ℝ :=
            fun N omega =>
              if dirichlet then
                dirichletResponse S (aN N omega) b
              else
                inverseResponse S (aN N omega) L
          let gN : ℕ → BilateralField d → HilbertGradient (centeredCube z r hr) :=
            fun N omega =>
              if dirichlet then
                sobolevGradient (dirichletMinimizer S (aN N omega) b).val
              else
                subspaceGradient S.space (responseSolution S (aN N omega) L)
          ∀ (K : ℕ → BilateralField d → ℝ),
            ((∀ N, AEStronglyMeasurable (K N) P) ∧
            (∀ᵐ omega ∂P, ∀ N, 0 ≤ K N omega)) →
            (∀ᵐ omega ∂P, ∀ N, ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
              ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
                localGradientEnergy (aN N omega)
                  (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet
                  (gN N omega) ≤ K N omega * rho ^ t) →
            (∀ N,
              MemLp (K N) (ENNReal.ofReal (3 * p)) P ∧
              MemLp (RN N) (ENNReal.ofReal (3 * p)) P ∧
              eLpNorm (K N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B ∧
              eLpNorm (RN N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B) →
            (∀ h N : ℕ,
              let sigma_h := bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h
              eLpNorm
                (fun om => RN N om - (P[RN N | sigma_h]) om)
                (ENNReal.ofReal p) P ≤
              ENNReal.ofReal
                (C * delta *
                  (3 : ℝ) ^
                    (-(t * (t - (d : ℝ) + 1) / (t + 1) /
                        (8 * Real.log 3)) * (h : ℝ)))) ∧
            (∀ h N : ℕ, N < h →
              let sigma_h := bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h
              eLpNorm
                (fun om => RN N om - (P[RN N | sigma_h]) om)
                (ENNReal.ofReal p) P ≤
              ENNReal.ofReal
                (C * delta * (3 : ℝ) ^ (-(h : ℝ))))
    := by
  intro d hd instM instB z r hr hP phi hphi hnonconst b hb f hf hfc hfsupp hf0 fL2 hfL2
    t p B ht_lower ht_upper hp hB dirichlet S L
  obtain ⟨C15, hC15, h15⟩ := aux_prop_16_lem15 d hd z r hr hP phi hphi hnonconst b hb
    f hf hfc hfsupp hf0 fL2 hfL2 t p B ht_lower ht_upper hp hB dirichlet
  obtain ⟨Ctail, hCtail, htail⟩ := aux_prop_16_coarse_tail d z r hr
  obtain ⟨Ccb, hCcb, hcb⟩ := prop_16_coarse_block_dirichlet d hd z r hr hP b fL2 t p B
    ht_lower ht_upper hp hB dirichlet Ctail hCtail
  obtain ⟨ha0, ha1⟩ := aux_prop_16_exponent_facts d hd t ht_lower ht_upper
  set a := t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3) with ha_def
  have hr1 : (3 : ℝ) ^ (-a) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h1r : 0 < 1 - (3 : ℝ) ^ (-a) := by linarith
  refine ⟨C15 / (1 - (3 : ℝ) ^ (-a)) + Ccb, by positivity, ?_⟩
  intro delta hdelta hdelta1 Praw G1 G2 forget nu P H hH hHconv kappa hkappa aN haN RN gN
    K hK hgrowth hmom
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ p)
  have hkey : ∀ h N : ℕ,
      eLpNorm (fun om => RN N om -
          (P[RN N | bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]) om)
        (ENNReal.ofReal p) P ≤
      (∑ k ∈ Finset.Ioc h N,
          ENNReal.ofReal (C15 * delta * (3 : ℝ) ^ (-a * (k : ℝ)))) +
        ENNReal.ofReal (Ccb * delta * (3 : ℝ) ^ (-(h : ℝ))) := by
    intro h N
    have hRmem : MemLp (RN N) (ENNReal.ofReal (3 * p)) P := (hmom N).2.1
    have hRint : Integrable (RN N) P :=
      hRmem.integrable (by simpa using ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ 3 * p))
    have hsplit := aux_prop_16_band_split
      (fun j : ℤ => (scaledLayerLaw d nu j : Measure C(SpatialCoordinates d, ℝ))) h hp1
      ENNReal.ofReal_ne_top hRint
    refine hsplit.trans ?_
    rw [add_comm]
    refine add_le_add ?_ ?_
    · have hdet : ∀ ω₁ ∈ {om : BilateralField d | Tendsto (infraredPartialSum om) atTop (𝓝 (H om))},
          ∀ ω₂ ∈ {om : BilateralField d | Tendsto (infraredPartialSum om) atTop (𝓝 (H om))},
          (∀ j : ℤ, -(N : ℤ) ≤ j → ω₁ j = ω₂ j) → RN N ω₁ = RN N ω₂ := by
        intro ω₁ h1 ω₂ h2 hagree
        have hH12 := aux_prop_16_infrared_eq H ω₁ ω₂ h1 h2 (fun j hj => hagree j (by omega))
        have hcut := aux_prop_16_cutoff_eq H ω₁ ω₂ N hH12 hagree
        have haeq : aN N ω₁ = aN N ω₂ := by
          apply Subtype.ext
          apply Lp.ext
          filter_upwards [haN N ω₁, haN N ω₂] with x hx1 hx2
          rw [hx1, hx2, hcut]
        simp only [RN, haeq]
      exact aux_prop_16_fine_telescope _ hp1 (RN N) hRmem.aestronglyMeasurable _ hHconv h N hdet
        (fun k => ENNReal.ofReal (C15 * delta * (3 : ℝ) ^ (-a * (k : ℝ))))
        (fun k _ hkN => h15 delta hdelta hdelta1 Praw G1 G2 H hH hHconv kappa hkappa aN haN
          K hK hgrowth hmom N k hkN)
    · have hcb' := hcb delta hdelta hdelta1 Praw G1 G2 H hH hHconv kappa hkappa aN haN
        (htail delta hdelta hdelta1 Praw G1 G2 H hH hHconv)
        (fun N => ⟨(hmom N).2.1, (hmom N).2.2.2⟩) h N
      have hTmp := measurePreserving_copy_infinitePi_block
        (fun j : ℤ => (scaledLayerLaw d nu j : Measure C(SpatialCoordinates d, ℝ)))
        {j : ℤ | (h : ℤ) < j}
      have hmeas : AEStronglyMeasurable (fun q : BilateralField d × BilateralField d =>
          RN N q.1 - RN N (fun j => if (h : ℤ) < j then q.2 j else q.1 j)) (P.prod P) :=
        (hRmem.aestronglyMeasurable.comp_measurePreserving measurePreserving_fst).sub
          (hRmem.aestronglyMeasurable.comp_measurePreserving hTmp)
      exact (eLpNorm_le_eLpNorm_of_exponent_le
        (ENNReal.ofReal_le_ofReal (by linarith)) hmeas).trans hcb'
  refine ⟨fun h N => ?_, fun h N hNh => ?_⟩
  · refine (hkey h N).trans ?_
    have hg := aux_prop_16_geom a ha0 (C15 * delta) (by positivity) h N
    refine (add_le_add hg le_rfl).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h3 : (3 : ℝ) ^ (-(h : ℝ)) ≤ (3 : ℝ) ^ (-a * (h : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have : (0 : ℝ) ≤ h := Nat.cast_nonneg h
      nlinarith
    have h4 : 0 ≤ (3 : ℝ) ^ (-a * (h : ℝ)) := by positivity
    calc C15 * delta * (3 : ℝ) ^ (-a * (h : ℝ)) / (1 - (3 : ℝ) ^ (-a)) +
          Ccb * delta * (3 : ℝ) ^ (-(h : ℝ))
        ≤ C15 * delta * (3 : ℝ) ^ (-a * (h : ℝ)) / (1 - (3 : ℝ) ^ (-a)) +
          Ccb * delta * (3 : ℝ) ^ (-a * (h : ℝ)) := by gcongr
      _ = (C15 / (1 - (3 : ℝ) ^ (-a)) + Ccb) * delta * (3 : ℝ) ^ (-a * (h : ℝ)) := by
          field_simp
  · refine (hkey h N).trans ?_
    rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, zero_add]
    apply ENNReal.ofReal_le_ofReal
    have : 0 ≤ C15 / (1 - (3 : ℝ) ^ (-a)) := by positivity
    have h4 : 0 ≤ delta * (3 : ℝ) ^ (-(h : ℝ)) := by positivity
    nlinarith

end Prop16_C_Clause1

section Prop16_E_Clause2
open MeasureTheory Filter Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Topology
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.Lane3


/-- The relabelling at cutoff `N`: layer `j` is the original layer `j - N`, read at `3^{-N} x`
(the construction of `aux_rem_resolved_meshes_relabel`). -/
def aux_prop_16_relab {d : ℕ} (N : ℕ) (omega : BilateralField d) : BilateralField d :=
  fun j => ContinuousMap.compRightContinuousMap ℝ
    (⟨fun x : SpatialCoordinates d => (3 : ℝ) ^ (-(N : ℤ)) • x,
      continuous_const.smul continuous_id⟩ :
      C(SpatialCoordinates d, SpatialCoordinates d))
    (omega (j - (N : ℤ)))

theorem aux_prop_16_layerScaling_comp {d : ℕ} (N : ℕ) (j : ℤ) :
    (layerScaling d (N : ℤ)).comp (layerScaling d (j - (N : ℤ))) = layerScaling d j := by
  ext g x
  simp only [layerScaling, ContinuousMap.comp_apply, ContinuousMap.compRightContinuousMap_apply,
    ContinuousMap.coe_mk]
  congr 1
  rw [smul_smul, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  congr 2
  ring

/-- The relabelling preserves the common-scale law. -/
theorem aux_prop_16_relab_mp {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) :
    MeasurePreserving (aux_prop_16_relab (d := d) N)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure := by
  set ν := chaosRootFieldLaw M
  let laws : ℤ → Measure C(SpatialCoordinates d, ℝ) :=
    fun j => (scaledLayerLaw d ν j : Measure C(SpatialCoordinates d, ℝ))
  have hP : (chaosSampleLaw M).toMeasure = Measure.infinitePi laws := rfl
  let S : C(SpatialCoordinates d, ℝ) → C(SpatialCoordinates d, ℝ) := layerScaling d (N : ℤ)
  have hS : Measurable S := (layerScaling d (N : ℤ)).continuous.measurable
  have hshift_eq : (MeasurableEquiv.piCongrLeft (fun _ : ℤ => C(SpatialCoordinates d, ℝ))
      (Equiv.addRight (N : ℤ)) : BilateralField d → BilateralField d) =
      fun omega j => omega (j - (N : ℤ)) := by
    funext omega j
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply, sub_eq_add_neg]
  have hshift_meas : Measurable (fun (omega : BilateralField d) (j : ℤ) => omega (j - (N : ℤ))) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply (j - (N : ℤ)))
  have hrel_eq : aux_prop_16_relab (d := d) N =
      (fun (x : BilateralField d) (j : ℤ) => S (x j)) ∘
        (fun (omega : BilateralField d) (j : ℤ) => omega (j - (N : ℤ))) := by
    funext omega j
    rfl
  have hmeas_comp : Measurable (fun (x : BilateralField d) (j : ℤ) => S (x j)) :=
    measurable_pi_lambda _ (fun j => hS.comp (measurable_pi_apply j))
  refine ⟨hrel_eq ▸ hmeas_comp.comp hshift_meas, ?_⟩
  rw [hrel_eq, ← Measure.map_map hmeas_comp hshift_meas, hP]
  have h1 : (Measure.infinitePi laws).map (fun (omega : BilateralField d) (j : ℤ) =>
      omega (j - (N : ℤ))) = Measure.infinitePi (fun j => laws (j - (N : ℤ))) := by
    have h := Measure.infinitePi_map_piCongrLeft (fun j => laws (j - (N : ℤ)))
      (Equiv.addRight (N : ℤ))
    rw [hshift_eq] at h
    have hl : (fun a : ℤ => laws ((Equiv.addRight (N : ℤ)) a - (N : ℤ))) = laws := by
      funext a
      simp
    rw [hl] at h
    exact h
  rw [h1]
  refine (Measure.infinitePi_map_pi (μ := fun j => laws (j - (N : ℤ))) (f := fun _ => S)
    (fun _ => hS)).trans ?_
  congr 1
  funext j
  change ((scaledLayerLaw d ν (j - (N : ℤ)) : Measure C(SpatialCoordinates d, ℝ))).map
      (layerScaling d (N : ℤ)) = (scaledLayerLaw d ν j : Measure C(SpatialCoordinates d, ℝ))
  simp only [scaledLayerLaw, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (layerScaling d (N : ℤ)).continuous.measurable
    (layerScaling d (j - (N : ℤ))).continuous.measurable]
  congr 1
  exact congrArg (fun F : C(C(SpatialCoordinates d, ℝ), C(SpatialCoordinates d, ℝ)) =>
    (F : C(SpatialCoordinates d, ℝ) → C(SpatialCoordinates d, ℝ)))
    (aux_prop_16_layerScaling_comp N j)

/-- Transport of an `L^p` norm through a measure-preserving map, in lambda form. -/
theorem aux_prop_16_eLpNorm_mp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} (p : ℝ≥0∞) (T : α → β) (hT : MeasurePreserving T μ ν)
    (g : β → ℝ) (hg : AEStronglyMeasurable g ν) :
    eLpNorm (fun x => g (T x)) p μ = eLpNorm g p ν :=
  eLpNorm_comp_measurePreserving hg hT

theorem aux_prop_16_relab_apply {d : ℕ} (N : ℕ) (om : BilateralField d) (i : ℤ)
    (x : SpatialCoordinates d) :
    aux_prop_16_relab N om i x = om (i - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • x) := by
  simp only [aux_prop_16_relab, ContinuousMap.compRightContinuousMap_apply,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk]

/-- A copy increment is at most twice the centred norm. -/
theorem aux_prop_16_copy_centered {X : Type} [MeasurableSpace X]
    (laws : ℤ → Measure X) [∀ j, IsProbabilityMeasure (laws j)]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (f : (ℤ → X) → ℝ)
    (hf : AEStronglyMeasurable f (Measure.infinitePi laws))
    (T : (ℤ → X) × (ℤ → X) → (ℤ → X))
    (hT : MeasurePreserving T ((Measure.infinitePi laws).prod (Measure.infinitePi laws))
      (Measure.infinitePi laws)) (c : ℝ) :
    eLpNorm (fun q : (ℤ → X) × (ℤ → X) => f q.1 - f (T q)) p
        ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) ≤
      2 * eLpNorm (fun om => f om - c) p (Measure.infinitePi laws) := by
  let g : (ℤ → X) → ℝ := fun om => f om - c
  have hgm : AEStronglyMeasurable g (Measure.infinitePi laws) :=
    hf.sub aestronglyMeasurable_const
  have h1 := aux_prop_16_eLpNorm_mp p Prod.fst
    (measurePreserving_fst : MeasurePreserving Prod.fst
      ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) (Measure.infinitePi laws))
    g hgm
  have h2 := aux_prop_16_eLpNorm_mp p T hT g hgm
  have m1 : AEStronglyMeasurable (fun q : (ℤ → X) × (ℤ → X) => g q.1)
      ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) :=
    hgm.comp_measurePreserving measurePreserving_fst
  have m2 : AEStronglyMeasurable (fun q : (ℤ → X) × (ℤ → X) => g (T q))
      ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) :=
    hgm.comp_measurePreserving hT
  have hsplit : (fun q : (ℤ → X) × (ℤ → X) => f q.1 - f (T q)) =
      (fun q => g q.1) - (fun q => g (T q)) := by
    funext q
    simp only [g, Pi.sub_apply]
    ring
  rw [hsplit]
  refine (eLpNorm_sub_le m1 m2 hp).trans ?_
  rw [h1, h2, two_mul]

theorem aux_prop_16_min_sqrt {E : ℝ≥0∞} {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h1 : E ≤ ENNReal.ofReal x) (h2 : E ≤ ENNReal.ofReal y) :
    E ≤ ENNReal.ofReal (Real.sqrt (x * y)) := by
  have hE : E ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
  rw [← ENNReal.ofReal_toReal hE]
  apply ENNReal.ofReal_le_ofReal
  have t1 : E.toReal ≤ x := ENNReal.toReal_le_of_le_ofReal hx h1
  have t2 : E.toReal ≤ y := ENNReal.toReal_le_of_le_ofReal hy h2
  have t0 : 0 ≤ E.toReal := ENNReal.toReal_nonneg
  calc E.toReal = Real.sqrt (E.toReal ^ 2) := (Real.sqrt_sq t0).symm
    _ ≤ Real.sqrt (x * y) := Real.sqrt_le_sqrt (by nlinarith)

/-- The smoothing-width choice `ε = 3^{-aH/4}` and the interpolation `min(A,B) ≤ √(AB)`. -/
theorem aux_prop_16_neumann_numeric (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) (h : ℕ)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (Ccn B Cn Cc : ℝ) (hCcn : 0 ≤ Ccn) (hB : 0 ≤ B) (hCn : 0 ≤ Cn) (hCc : 0 ≤ Cc)
    (E : ℝ≥0∞)
    (hE1 : ∀ ε : ℝ, 0 < ε ∧ ε < 1 / 8 →
      E ≤ ENNReal.ofReal (Ccn * δ * (3 : ℝ) ^ (-(h : ℝ)) + 2 * B * ε ^ (1 / 4 : ℝ) +
        Cn * δ * ε ^ (-2 : ℝ) * (3 : ℝ) ^ (-a * (h : ℝ)) / (1 - (3 : ℝ) ^ (-a))))
    (hE2 : E ≤ ENNReal.ofReal (4 * Cc * δ)) :
    E ≤ ENNReal.ofReal ((Real.sqrt (4 * (Ccn + 2 * B + Cn / (1 - (3 : ℝ) ^ (-a))) * Cc) +
      8 * Cc) * Real.sqrt δ * (3 : ℝ) ^ (-((a / 32) * (h : ℝ)))) := by
  have hr1 : (3 : ℝ) ^ (-a) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h1r : 0 < 1 - (3 : ℝ) ^ (-a) := by linarith
  set D := Ccn + 2 * B + Cn / (1 - (3 : ℝ) ^ (-a)) with hD_def
  have hD : 0 ≤ D := by positivity
  set u := a * (h : ℝ) with hu
  have hu0 : 0 ≤ u := by positivity
  have hexp : (3 : ℝ) ^ (-((a / 32) * (h : ℝ))) = (3 : ℝ) ^ (-u / 32) := by
    congr 1
    rw [hu]
    ring
  rw [hexp]
  have hsd : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg δ
  have h32 : 0 < (3 : ℝ) ^ (-u / 32) := by positivity
  by_cases hsmall : (3 : ℝ) ^ (-u / 4) < 1 / 8
  · set ε := (3 : ℝ) ^ (-u / 4) with hε_def
    have hε0 : 0 < ε := by positivity
    have h1 := hE1 ε ⟨hε0, hsmall⟩
    have hε14 : ε ^ (1 / 4 : ℝ) = (3 : ℝ) ^ (-u / 16) := by
      rw [hε_def, ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    have hεm2 : ε ^ (-2 : ℝ) * (3 : ℝ) ^ (-a * (h : ℝ)) = (3 : ℝ) ^ (-u / 2) := by
      rw [hε_def, ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
      congr 1
      rw [hu]
      ring
    have hh16 : (3 : ℝ) ^ (-(h : ℝ)) ≤ (3 : ℝ) ^ (-u / 16) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have : (0 : ℝ) ≤ h := Nat.cast_nonneg h
      rw [hu]
      nlinarith
    have h216 : (3 : ℝ) ^ (-u / 2) ≤ (3 : ℝ) ^ (-u / 16) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    have h16 : 0 < (3 : ℝ) ^ (-u / 16) := by positivity
    have hRHS : Ccn * δ * (3 : ℝ) ^ (-(h : ℝ)) + 2 * B * ε ^ (1 / 4 : ℝ) +
        Cn * δ * ε ^ (-2 : ℝ) * (3 : ℝ) ^ (-a * (h : ℝ)) / (1 - (3 : ℝ) ^ (-a)) ≤
        D * (3 : ℝ) ^ (-u / 16) := by
      rw [hε14]
      have e1 : Cn * δ * ε ^ (-2 : ℝ) * (3 : ℝ) ^ (-a * (h : ℝ)) / (1 - (3 : ℝ) ^ (-a)) =
          Cn / (1 - (3 : ℝ) ^ (-a)) * δ * (ε ^ (-2 : ℝ) * (3 : ℝ) ^ (-a * (h : ℝ))) := by
        field_simp
      rw [e1, hεm2, hD_def]
      have hq : 0 ≤ Cn / (1 - (3 : ℝ) ^ (-a)) := by positivity
      have t1 : Ccn * δ * (3 : ℝ) ^ (-(h : ℝ)) ≤ Ccn * (3 : ℝ) ^ (-u / 16) := by
        calc Ccn * δ * (3 : ℝ) ^ (-(h : ℝ)) ≤ Ccn * 1 * (3 : ℝ) ^ (-u / 16) := by gcongr
          _ = Ccn * (3 : ℝ) ^ (-u / 16) := by ring
      have t3 : Cn / (1 - (3 : ℝ) ^ (-a)) * δ * (3 : ℝ) ^ (-u / 2) ≤
          Cn / (1 - (3 : ℝ) ^ (-a)) * (3 : ℝ) ^ (-u / 16) := by
        calc Cn / (1 - (3 : ℝ) ^ (-a)) * δ * (3 : ℝ) ^ (-u / 2)
            ≤ Cn / (1 - (3 : ℝ) ^ (-a)) * 1 * (3 : ℝ) ^ (-u / 16) := by gcongr
          _ = _ := by ring
      nlinarith
    have hE1' : E ≤ ENNReal.ofReal (D * (3 : ℝ) ^ (-u / 16)) :=
      h1.trans (ENNReal.ofReal_le_ofReal hRHS)
    have hE3 := aux_prop_16_min_sqrt (by positivity) (by positivity) hE1' hE2
    refine hE3.trans (ENNReal.ofReal_le_ofReal ?_)
    have hsq : Real.sqrt (D * (3 : ℝ) ^ (-u / 16) * (4 * Cc * δ)) =
        Real.sqrt (4 * D * Cc) * Real.sqrt δ * (3 : ℝ) ^ (-u / 32) := by
      rw [show D * (3 : ℝ) ^ (-u / 16) * (4 * Cc * δ) = (4 * D * Cc) * δ * (3 : ℝ) ^ (-u / 16) by
        ring]
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
      congr 1
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    rw [hsq]
    have : 0 ≤ 8 * Cc * Real.sqrt δ * (3 : ℝ) ^ (-u / 32) := by positivity
    nlinarith
  · push_neg at hsmall
    have hhalf : (1 / 2 : ℝ) ≤ (3 : ℝ) ^ (-u / 32) := by
      have h8 : ((3 : ℝ) ^ (-u / 32)) ^ (8 : ℕ) = (3 : ℝ) ^ (-u / 4) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        congr 1
        push_cast
        ring
      by_contra hlt
      push_neg at hlt
      have hpow : ((3 : ℝ) ^ (-u / 32)) ^ (8 : ℕ) < (1 / 2 : ℝ) ^ (8 : ℕ) :=
        pow_lt_pow_left₀ hlt h32.le (by norm_num)
      rw [h8] at hpow
      norm_num at hpow
      linarith
    have hδs : δ ≤ Real.sqrt δ := by
      have hs1 : Real.sqrt δ ≤ 1 := Real.sqrt_le_one.mpr hδ1
      have hsq : Real.sqrt δ * Real.sqrt δ = δ := Real.mul_self_sqrt hδ0.le
      nlinarith
    refine hE2.trans (ENNReal.ofReal_le_ofReal ?_)
    have e1 : 4 * Cc * δ ≤ 8 * Cc * Real.sqrt δ * (3 : ℝ) ^ (-u / 32) := by
      have : 4 * Cc * δ ≤ 4 * Cc * Real.sqrt δ := by gcongr
      nlinarith [mul_nonneg hCc hsd]
    have e2 : 0 ≤ Real.sqrt (4 * D * Cc) * Real.sqrt δ * (3 : ℝ) ^ (-u / 32) := by positivity
    nlinarith

theorem aux_prop_16_geom_neg (a : ℝ) (ha : 0 < a) (Cd : ℝ) (hCd : 0 ≤ Cd) (h N : ℕ) :
    ∑ k ∈ Finset.Ioc h N, ENNReal.ofReal (Cd * (3 : ℝ) ^ (-(a * (k : ℝ)))) ≤
      ENNReal.ofReal (Cd * (3 : ℝ) ^ (-a * (h : ℝ)) / (1 - (3 : ℝ) ^ (-a))) := by
  have hg := aux_prop_16_geom a ha Cd hCd h N
  simp only [neg_mul] at hg ⊢
  exact hg

theorem aux_prop_16_neumann :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (Cresp : ℝ) (hCresp : 0 < Cresp)
    (rho : ℝ → ℝ),
    ContDiff ℝ ∞ rho →
    (∀ tau, 0 ≤ rho tau) →
    (∀ tau, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) →
    (∫ tau, rho tau) = 1 →
    ∀ (pvec : Fin d → ℝ),
      (∑ i : Fin d, (pvec i) ^ 2) = 1 →
    ∀ (hP : ∃ Kp : ℝ≥0, ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
        ‖(u : SobolevData (unitNeumannCube d)).1‖ ≤
          Kp * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) u‖),
      let Q := unitNeumannCube d
      let S := meanZeroResponseSpace hP
      let L0 : S.space →L[ℝ] ℝ :=
        (affineNeumannLoad pvec).comp (subspaceGradient (meanZeroSobolevGraph Q))
      ∀ (fL2 : ℝ → DomainL2 Q),
        (∀ eps : ℝ, (0 < eps ∧ eps < 1 / 8) →
          ((fL2 eps : SpatialCoordinates d → ℝ) =ᵐ[
            volume.restrict (Q : Set (SpatialCoordinates d))]
            faceBump rho pvec eps)) →
        let Leps : ℝ → S.space →L[ℝ] ℝ := fun eps =>
          (sobolevVolumeLoad (fL2 eps)).comp S.space.subtypeL
        ∀ (t p B : ℝ),
          ((d : ℝ) - 1 < t ∧ t < (d : ℝ) ∧ 2 ≤ p ∧ 0 ≤ B) →
          ∃ delta0 C : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧ 0 < C ∧
            ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d),
              (0 < M.delta ∧ M.delta ≤ delta0) →
              ∀ (Rinput : Paper.in_responses d M),
                Rinput.C ≤ Cresp →
                4 * p ≤ Cresp⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
                ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
                InfraredCharacterization M H →
                let P : Measure (BilateralField d) :=
                  (chaosSampleLaw M).toMeasure
                let aN : ℕ → BilateralField d → PositiveCoefficient Q := fun N om =>
                  cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos
                let yN : ℕ → BilateralField d → ℝ := fun N om =>
                  inverseResponse S (aN N om) L0
                let yeps : ℝ → ℕ → BilateralField d → ℝ := fun eps N om =>
                  inverseResponse S (aN N om) (Leps eps)
                let ueps : ℝ → ℕ → BilateralField d → S.space := fun eps N om =>
                  responseSolution S (aN N om) (Leps eps)
                ∀ (K : ℕ → BilateralField d → ℝ),
                  (∀ N, AEStronglyMeasurable (K N) P) →
                  (∀ᵐ om ∂P, ∀ N, 0 ≤ K N om) →
                  (∀ᵐ om ∂P,
                    ∀ (N : ℕ) (eps : ℝ),
                      (0 < eps ∧ eps < 1 / 8) →
                      ∀ (x : SpatialCoordinates d) (rad : ℝ),
                        x ∈ Q → (0 < rad ∧ rad ≤ 1) →
                        localGradientEnergy (aN N om)
                            (s := Metric.ball x rad ∩ (Q : Set (SpatialCoordinates d)))
                            (isOpen_ball.measurableSet.inter Q.isOpen.measurableSet)
                            (subspaceGradient S.space (ueps eps N om)) ≤
                          K N om * eps ^ (-2 : ℝ) * rad ^ t) →
                  (∀ N,
                    MemLp (K N) (ENNReal.ofReal (3 * p)) P ∧
                      eLpNorm (K N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B) →
                  (∀ N eps, (0 < eps ∧ eps < 1 / 8) →
                    MemLp (yeps eps N) (ENNReal.ofReal (3 * p)) P ∧
                      eLpNorm (yeps eps N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B) →
                  (∀ N,
                    MemLp (yN N) (ENNReal.ofReal (4 * p)) P ∧
                      eLpNorm (yN N) (ENNReal.ofReal (4 * p)) P ≤ ENNReal.ofReal B) →
                  (∀ N eps, (0 < eps ∧ eps < 1 / 8) →
                    eLpNorm (fun om => yN N om - yeps eps N om)
                      (ENNReal.ofReal p) P ≤
                      ENNReal.ofReal (B * eps ^ (1 / 4 : ℝ))) →
                  (∀ h N : ℕ,
                    let sigma_h := bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h
                    eLpNorm
                      (fun om => yN N om - (P[yN N | sigma_h]) om)
                      (ENNReal.ofReal p) P ≤
                    ENNReal.ofReal
                      (C * Real.sqrt M.delta *
                        (3 : ℝ) ^
                          (-((t * (t - (d : ℝ) + 1) / (t + 1) /
                              (8 * Real.log 3) / 32) * (h : ℝ))))) ∧
                  (∀ h N : ℕ, N < h →
                    let sigma_h := bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h
                    eLpNorm
                      (fun om => yN N om - (P[yN N | sigma_h]) om)
                      (ENNReal.ofReal p) P ≤
                    ENNReal.ofReal
                      (C * M.delta * (3 : ℝ) ^ (-(h : ℝ))))
    := by
  intro d hd instM instB I Cresp hCresp rho hrho1 hrho2 hrho3 hrho4 pvec hpvec hP Q S L0
    fL2 hfL2 Leps t p B htpB
  obtain ⟨ht_lower, ht_upper, hp, hB⟩ := htpB
  obtain ⟨Cn, hCn, hn15⟩ := lem_neumann_15 d hd rho hrho1 hrho2 hrho3 hrho4 pvec hpvec hP
    fL2 hfL2 t p B ⟨ht_lower, ht_upper, hp, hB⟩
  obtain ⟨Ccn, hCcn, hcbn⟩ := prop_16_coarse_block_neumann d hd Cresp hCresp pvec hpvec hP
    p B hp hB
  obtain ⟨delta0, Cc, hdelta0, hdelta01, hCc, hcent⟩ :=
    neumann_centered_response d hd I Cresp hCresp p hp pvec hpvec hP
  obtain ⟨ha0, ha1⟩ := aux_prop_16_exponent_facts d hd t ht_lower ht_upper
  set a := t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3) with ha_def
  have hr1 : (3 : ℝ) ^ (-a) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h1r : 0 < 1 - (3 : ℝ) ^ (-a) := by linarith
  refine ⟨delta0, Real.sqrt (4 * (Ccn + 2 * B + Cn / (1 - (3 : ℝ) ^ (-a))) * Cc) + 8 * Cc +
    Ccn + 1, hdelta0, hdelta01, by positivity, ?_⟩
  intro M hM Rinput hRC hscale H hH P aN yN yeps ueps K hKm hK0 hgrowth hKmom hyeps hyN
    hsmooth
  obtain ⟨hδ0, hδ⟩ := hM
  have hδ1 : M.delta ≤ 1 := hδ.trans hdelta01
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ p)
  let laws : ℤ → Measure C(SpatialCoordinates d, ℝ) := fun j =>
    (scaledLayerLaw d (chaosRootFieldLaw M) j : Measure C(SpatialCoordinates d, ℝ))
  have hc := hcent M ⟨hδ0, hδ⟩ Rinput hRC hscale H hH (fun N => aux_prop_16_relab N)
    (fun N => aux_prop_16_relab_mp M N)
    (ae_of_all _ fun om N i x => aux_prop_16_relab_apply N om i x)
  let G : Set (BilateralField d) :=
    {om | Tendsto (infraredPartialSum om) atTop (𝓝 (H om))}
  have hG : ∀ᵐ om ∂(Measure.infinitePi laws), om ∈ G := hH.2
  have hdetA : ∀ N : ℕ, ∀ ω₁ ∈ G, ∀ ω₂ ∈ G, (∀ j : ℤ, -(N : ℤ) ≤ j → ω₁ j = ω₂ j) →
      aN N ω₁ = aN N ω₂ := by
    intro N ω₁ h1 ω₂ h2 hagree
    have hH12 := aux_prop_16_infrared_eq H ω₁ ω₂ h1 h2 (fun j hj => hagree j (by omega))
    exact aux_prop_16_cpc_eq M H ω₁ ω₂ N _ one_pos
      (aux_prop_16_cutoff_eq H ω₁ ω₂ N hH12 hagree)
  have hdetN : ∀ N : ℕ, ∀ ω₁ ∈ G, ∀ ω₂ ∈ G, (∀ j : ℤ, -(N : ℤ) ≤ j → ω₁ j = ω₂ j) →
      yN N ω₁ = yN N ω₂ := by
    intro N ω₁ h1 ω₂ h2 hagree
    show inverseResponse S (aN N ω₁) L0 = inverseResponse S (aN N ω₂) L0
    rw [hdetA N ω₁ h1 ω₂ h2 hagree]
  have hyNm : ∀ N, AEStronglyMeasurable (yN N) (Measure.infinitePi laws) := fun N =>
    (hyN N).1.aestronglyMeasurable
  have hyNint : ∀ N, Integrable (yN N) (Measure.infinitePi laws) := fun N =>
    (hyN N).1.integrable (by
      simpa using ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ 4 * p))
  have hFCmp : ∀ h : ℕ, MeasurePreserving
      (fun q : BilateralField d × BilateralField d => fun j =>
        if j < -(h : ℤ) then q.2 j else q.1 j)
      ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) (Measure.infinitePi laws) :=
    fun h => measurePreserving_copy_infinitePi_block laws {j : ℤ | j < -(h : ℤ)}
  have hCCmp : ∀ h : ℕ, MeasurePreserving
      (fun q : BilateralField d × BilateralField d => fun j =>
        if (h : ℤ) < j then q.2 j else q.1 j)
      ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) (Measure.infinitePi laws) :=
    fun h => measurePreserving_copy_infinitePi_block laws {j : ℤ | (h : ℤ) < j}
  have hcoarse : ∀ h N : ℕ,
      eLpNorm (fun q : BilateralField d × BilateralField d =>
          yN N q.1 - yN N (fun j => if (h : ℤ) < j then q.2 j else q.1 j))
        (ENNReal.ofReal p) ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) ≤
      ENNReal.ofReal (Ccn * M.delta * (3 : ℝ) ^ (-(h : ℝ))) := by
    intro h N
    have hmeas : AEStronglyMeasurable (fun q : BilateralField d × BilateralField d =>
        yN N q.1 - yN N (fun j => if (h : ℤ) < j then q.2 j else q.1 j))
        ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) :=
      ((hyNm N).comp_measurePreserving measurePreserving_fst).sub
        ((hyNm N).comp_measurePreserving (hCCmp h))
    exact (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (by linarith))
      hmeas).trans (hcbn M ⟨hδ0, hδ1⟩ Rinput hRC hscale H hH hyN h N)
  have hfine0 : ∀ h N : ℕ, N ≤ h →
      eLpNorm (fun q : BilateralField d × BilateralField d =>
          yN N q.1 - yN N (fun j => if j < -(h : ℤ) then q.2 j else q.1 j))
        (ENNReal.ofReal p) ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) ≤ 0 := by
    intro h N hNh
    have htel := aux_prop_16_fine_telescope laws hp1 (yN N) (hyNm N) G hG h N (hdetN N)
      (fun _ => 0) (fun k hk hkN => absurd (lt_of_lt_of_le hk hkN) (by omega))
    simpa using htel
  have hfine : ∀ h N : ℕ, ∀ ε : ℝ, 0 < ε ∧ ε < 1 / 8 →
      eLpNorm (fun q : BilateralField d × BilateralField d =>
          yN N q.1 - yN N (fun j => if j < -(h : ℤ) then q.2 j else q.1 j))
        (ENNReal.ofReal p) ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) ≤
      ENNReal.ofReal (2 * B * ε ^ (1 / 4 : ℝ) + Cn * M.delta * ε ^ (-2 : ℝ) *
        (3 : ℝ) ^ (-a * (h : ℝ)) / (1 - (3 : ℝ) ^ (-a))) := by
    intro h N ε hε
    have hyem : AEStronglyMeasurable (yeps ε N) (Measure.infinitePi laws) :=
      (hyeps N ε hε).1.aestronglyMeasurable
    have hdiff : eLpNorm (fun om => yN N om - yeps ε N om) (ENNReal.ofReal p)
        (Measure.infinitePi laws) ≤ ENNReal.ofReal (B * ε ^ (1 / 4 : ℝ)) := hsmooth N ε hε
    have hdetE : ∀ ω₁ ∈ G, ∀ ω₂ ∈ G, (∀ j : ℤ, -(N : ℤ) ≤ j → ω₁ j = ω₂ j) →
        yeps ε N ω₁ = yeps ε N ω₂ := by
      intro ω₁ h1 ω₂ h2 hagree
      show inverseResponse S (aN N ω₁) (Leps ε) = inverseResponse S (aN N ω₂) (Leps ε)
      rw [hdetA N ω₁ h1 ω₂ h2 hagree]
    have htel := aux_prop_16_fine_telescope laws hp1 (yeps ε N) hyem G hG h N hdetE
      (fun k => ENNReal.ofReal (Cn * M.delta * ε ^ (-2 : ℝ) * (3 : ℝ) ^ (-(a * (k : ℝ)))))
      (fun k _ hkN => hn15 M ⟨hδ0, hδ1⟩ H hH K hKm hK0 hgrowth hKmom hyeps hyN hsmooth
        ε hε N k hkN)
    have hgeo := aux_prop_16_geom_neg a ha0 (Cn * M.delta * ε ^ (-2 : ℝ))
      (by have : 0 ≤ ε ^ (-2 : ℝ) := Real.rpow_nonneg hε.1.le _; positivity) h N
    let FC : BilateralField d × BilateralField d → BilateralField d := fun q j =>
      if j < -(h : ℤ) then q.2 j else q.1 j
    have m1 : AEStronglyMeasurable (fun q : BilateralField d × BilateralField d =>
        yN N q.1 - yeps ε N q.1)
        ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) :=
      ((hyNm N).sub hyem).comp_measurePreserving measurePreserving_fst
    have m2 : AEStronglyMeasurable (fun q : BilateralField d × BilateralField d =>
        yeps ε N q.1 - yeps ε N (FC q))
        ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) :=
      (hyem.comp_measurePreserving measurePreserving_fst).sub
        (hyem.comp_measurePreserving (hFCmp h))
    have m3 : AEStronglyMeasurable (fun q : BilateralField d × BilateralField d =>
        yN N (FC q) - yeps ε N (FC q))
        ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) :=
      ((hyNm N).sub hyem).comp_measurePreserving (hFCmp h)
    have hsplit : (fun q : BilateralField d × BilateralField d => yN N q.1 - yN N (FC q)) =
        ((fun q => yN N q.1 - yeps ε N q.1) + (fun q => yeps ε N q.1 - yeps ε N (FC q))) -
          (fun q => yN N (FC q) - yeps ε N (FC q)) := by
      funext q
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    change eLpNorm (fun q : BilateralField d × BilateralField d => yN N q.1 - yN N (FC q))
      (ENNReal.ofReal p) ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) ≤ _
    rw [hsplit]
    refine (eLpNorm_sub_le (m1.add m2) m3 hp1).trans ?_
    refine (add_le_add (eLpNorm_add_le m1 m2 hp1) le_rfl).trans ?_
    let gd : BilateralField d → ℝ := fun om => yN N om - yeps ε N om
    have hgd : AEStronglyMeasurable gd (Measure.infinitePi laws) := (hyNm N).sub hyem
    have e1 := aux_prop_16_eLpNorm_mp (ENNReal.ofReal p) Prod.fst
      (measurePreserving_fst : MeasurePreserving Prod.fst
        ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) (Measure.infinitePi laws))
      gd hgd
    have e3 := aux_prop_16_eLpNorm_mp (ENNReal.ofReal p) FC (hFCmp h) gd hgd
    change eLpNorm (fun q : BilateralField d × BilateralField d => gd q.1)
        (ENNReal.ofReal p) ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) +
      eLpNorm (fun q : BilateralField d × BilateralField d =>
        yeps ε N q.1 - yeps ε N (FC q)) (ENNReal.ofReal p)
        ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) +
      eLpNorm (fun q : BilateralField d × BilateralField d => gd (FC q))
        (ENNReal.ofReal p) ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) ≤ _
    rw [e1, e3]
    have hB0 : 0 ≤ B * ε ^ (1 / 4 : ℝ) := by
      have : 0 ≤ ε ^ (1 / 4 : ℝ) := Real.rpow_nonneg hε.1.le _
      positivity
    have hF0 : 0 ≤ Cn * M.delta * ε ^ (-2 : ℝ) * (3 : ℝ) ^ (-a * (h : ℝ)) /
        (1 - (3 : ℝ) ^ (-a)) := by
      have : 0 ≤ ε ^ (-2 : ℝ) := Real.rpow_nonneg hε.1.le _
      positivity
    calc eLpNorm (fun om => yN N om - yeps ε N om) (ENNReal.ofReal p) (Measure.infinitePi laws) +
          eLpNorm (fun q : BilateralField d × BilateralField d =>
            yeps ε N q.1 - yeps ε N (FC q)) (ENNReal.ofReal p)
            ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) +
          eLpNorm (fun om => yN N om - yeps ε N om) (ENNReal.ofReal p) (Measure.infinitePi laws)
        ≤ ENNReal.ofReal (B * ε ^ (1 / 4 : ℝ)) +
            ENNReal.ofReal (Cn * M.delta * ε ^ (-2 : ℝ) * (3 : ℝ) ^ (-a * (h : ℝ)) /
              (1 - (3 : ℝ) ^ (-a))) +
            ENNReal.ofReal (B * ε ^ (1 / 4 : ℝ)) :=
          add_le_add (add_le_add hdiff (htel.trans hgeo)) hdiff
      _ = ENNReal.ofReal (2 * B * ε ^ (1 / 4 : ℝ) + Cn * M.delta * ε ^ (-2 : ℝ) *
            (3 : ℝ) ^ (-a * (h : ℝ)) / (1 - (3 : ℝ) ^ (-a))) := by
          rw [← ENNReal.ofReal_add hB0 hF0, ← ENNReal.ofReal_add (by positivity) hB0]
          congr 1
          ring
  have hcentE : ∀ h N : ℕ,
      eLpNorm (fun om => yN N om -
          ((Measure.infinitePi laws)[yN N | bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ))
            h]) om) (ENNReal.ofReal p) (Measure.infinitePi laws) ≤
        ENNReal.ofReal (4 * Cc * M.delta) := by
    intro h N
    have hcN := (hc N).2.2.2.2
    refine (aux_prop_16_band_split laws h hp1 ENNReal.ofReal_ne_top (hyNint N)).trans ?_
    have c1 := aux_prop_16_copy_centered laws hp1 (yN N) (hyNm N) _ (hCCmp h)
      (∫ om, yN N om ∂(Measure.infinitePi laws))
    have c2 := aux_prop_16_copy_centered laws hp1 (yN N) (hyNm N) _ (hFCmp h)
      (∫ om, yN N om ∂(Measure.infinitePi laws))
    have hx : 0 ≤ Cc * M.delta := by positivity
    calc _ ≤ 2 * eLpNorm (fun om => yN N om - ∫ om, yN N om ∂(Measure.infinitePi laws))
            (ENNReal.ofReal p) (Measure.infinitePi laws) +
          2 * eLpNorm (fun om => yN N om - ∫ om, yN N om ∂(Measure.infinitePi laws))
            (ENNReal.ofReal p) (Measure.infinitePi laws) := add_le_add c1 c2
      _ ≤ 2 * ENNReal.ofReal (Cc * M.delta) + 2 * ENNReal.ofReal (Cc * M.delta) := by
          gcongr <;> exact hcN
      _ = ENNReal.ofReal (4 * Cc * M.delta) := by
          rw [two_mul, ← ENNReal.ofReal_add hx hx, ← ENNReal.ofReal_add (by positivity)
            (by positivity)]
          congr 1
          ring
  refine ⟨fun h N => ?_, fun h N hNh => ?_⟩
  · have hE1 : ∀ ε : ℝ, 0 < ε ∧ ε < 1 / 8 →
        eLpNorm (fun om => yN N om -
          ((Measure.infinitePi laws)[yN N | bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ))
            h]) om) (ENNReal.ofReal p) (Measure.infinitePi laws) ≤
        ENNReal.ofReal (Ccn * M.delta * (3 : ℝ) ^ (-(h : ℝ)) + 2 * B * ε ^ (1 / 4 : ℝ) +
          Cn * M.delta * ε ^ (-2 : ℝ) * (3 : ℝ) ^ (-a * (h : ℝ)) / (1 - (3 : ℝ) ^ (-a))) := by
      intro ε hε
      refine (aux_prop_16_band_split laws h hp1 ENNReal.ofReal_ne_top (hyNint N)).trans ?_
      refine (add_le_add (hcoarse h N) (hfine h N ε hε)).trans ?_
      have hF0 : 0 ≤ 2 * B * ε ^ (1 / 4 : ℝ) + Cn * M.delta * ε ^ (-2 : ℝ) *
          (3 : ℝ) ^ (-a * (h : ℝ)) / (1 - (3 : ℝ) ^ (-a)) := by
        have : 0 ≤ ε ^ (-2 : ℝ) := Real.rpow_nonneg hε.1.le _
        have : 0 ≤ ε ^ (1 / 4 : ℝ) := Real.rpow_nonneg hε.1.le _
        positivity
      rw [← ENNReal.ofReal_add (by positivity) hF0]
      apply ENNReal.ofReal_le_ofReal (le_of_eq (by ring))
    have hnum := aux_prop_16_neumann_numeric a ha0 ha1 h M.delta hδ0 hδ1 Ccn B Cn Cc hCcn.le hB
      hCn.le hCc.le _ hE1 (hcentE h N)
    refine hnum.trans (ENNReal.ofReal_le_ofReal ?_)
    have hsd : 0 ≤ Real.sqrt M.delta := Real.sqrt_nonneg _
    have he : 0 ≤ (3 : ℝ) ^ (-((a / 32) * (h : ℝ))) := by positivity
    apply mul_le_mul_of_nonneg_right _ he
    apply mul_le_mul_of_nonneg_right _ hsd
    linarith
  · refine (aux_prop_16_band_split laws h hp1 ENNReal.ofReal_ne_top (hyNint N)).trans ?_
    refine (add_le_add (hcoarse h N) (hfine0 h N hNh.le)).trans ?_
    rw [add_zero]
    apply ENNReal.ofReal_le_ofReal
    have h2 : 0 ≤ Real.sqrt (4 * (Ccn + 2 * B + Cn / (1 - (3 : ℝ) ^ (-a))) * Cc) + 8 * Cc := by
      positivity
    have he : 0 ≤ (3 : ℝ) ^ (-(h : ℝ)) := by positivity
    apply mul_le_mul_of_nonneg_right _ he
    apply mul_le_mul_of_nonneg_right _ hδ0.le
    linarith

end Prop16_E_Clause2



theorem prop_16 :
  (∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ ∞ phi)
    (hnonconst : ∃ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∃ y ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), phi x ≠ phi y)
    (b : weakSobolevGraph (centeredCube z r hr))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi)
    (f : SpatialCoordinates d → ℝ) (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f)
    (hfsupp : tsupport f ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hf0 : ∃ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), f x ≠ 0)
    (fL2 : DomainL2 (centeredCube z r hr))
    (hfL2 : (fL2 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f)
    (t p B : ℝ) (ht_lower : (d : ℝ) - 1 < t) (ht_upper : t < (d : ℝ))
    (hp : 2 ≤ p) (hB : 0 ≤ B) (dirichlet : Bool),
    let S := killedResponseSpace hP
    let L := (sobolevVolumeLoad fL2).comp S.space.subtypeL
    ∃ C : ℝ, 0 < C ∧
      ∀ (delta : ℝ), 0 < delta → delta ≤ 1 →
        ∀ (Praw : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d))
          (_G1 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 d Praw)
          (_G2 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2 d delta Praw),
          let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
              C(SpatialCoordinates d, ℝ)) :=
            ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
          let nu := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
            forget.continuous.measurable.aemeasurable
          let P := (commonScaleLaw d nu).toMeasure
          ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
            Measurable H →
            (∀ᵐ omega ∂P,
              Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega))) →
            ∀ (kappa : ℕ → ℝ), (∀ N, 0 < kappa N) →
            ∀ (aN : ℕ → BilateralField d → PositiveCoefficient (centeredCube z r hr)),
              (∀ N omega,
                (aN N omega).val =ᵐ[volume.restrict
                  (centeredCube z r hr : Set (SpatialCoordinates d))]
                  (fun x => Real.exp (cutoffPotential H omega N x - Real.log (kappa N)))) →
            let RN : ℕ → BilateralField d → ℝ :=
            fun N omega =>
              if dirichlet then
                dirichletResponse S (aN N omega) b
              else
                inverseResponse S (aN N omega) L
          let gN : ℕ → BilateralField d → HilbertGradient (centeredCube z r hr) :=
            fun N omega =>
              if dirichlet then
                sobolevGradient (dirichletMinimizer S (aN N omega) b).val
              else
                subspaceGradient S.space (responseSolution S (aN N omega) L)
          ∀ (K : ℕ → BilateralField d → ℝ),
            ((∀ N, AEStronglyMeasurable (K N) P) ∧
            (∀ᵐ omega ∂P, ∀ N, 0 ≤ K N omega)) →
            (∀ᵐ omega ∂P, ∀ N, ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
              ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
                localGradientEnergy (aN N omega)
                  (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet
                  (gN N omega) ≤ K N omega * rho ^ t) →
            (∀ N,
              MemLp (K N) (ENNReal.ofReal (3 * p)) P ∧
              MemLp (RN N) (ENNReal.ofReal (3 * p)) P ∧
              eLpNorm (K N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B ∧
              eLpNorm (RN N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B) →
            (∀ h N : ℕ,
              let sigma_h := bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h
              eLpNorm
                (fun om => RN N om - (P[RN N | sigma_h]) om)
                (ENNReal.ofReal p) P ≤
              ENNReal.ofReal
                (C * delta *
                  (3 : ℝ) ^
                    (-(t * (t - (d : ℝ) + 1) / (t + 1) /
                        (8 * Real.log 3)) * (h : ℝ)))) ∧
            (∀ h N : ℕ, N < h →
              let sigma_h := bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h
              eLpNorm
                (fun om => RN N om - (P[RN N | sigma_h]) om)
                (ENNReal.ofReal p) P ≤
              ENNReal.ofReal
                (C * delta * (3 : ℝ) ^ (-(h : ℝ)))) ) ∧
  (∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (Cresp : ℝ) (hCresp : 0 < Cresp)
    (rho : ℝ → ℝ),
    ContDiff ℝ ∞ rho →
    (∀ tau, 0 ≤ rho tau) →
    (∀ tau, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) →
    (∫ tau, rho tau) = 1 →
    ∀ (pvec : Fin d → ℝ),
      (∑ i : Fin d, (pvec i) ^ 2) = 1 →
    ∀ (hP : ∃ Kp : ℝ≥0, ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
        ‖(u : SobolevData (unitNeumannCube d)).1‖ ≤
          Kp * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) u‖),
      let Q := unitNeumannCube d
      let S := meanZeroResponseSpace hP
      let L0 : S.space →L[ℝ] ℝ :=
        (affineNeumannLoad pvec).comp (subspaceGradient (meanZeroSobolevGraph Q))
      ∀ (fL2 : ℝ → DomainL2 Q),
        (∀ eps : ℝ, (0 < eps ∧ eps < 1 / 8) →
          ((fL2 eps : SpatialCoordinates d → ℝ) =ᵐ[
            volume.restrict (Q : Set (SpatialCoordinates d))]
            faceBump rho pvec eps)) →
        let Leps : ℝ → S.space →L[ℝ] ℝ := fun eps =>
          (sobolevVolumeLoad (fL2 eps)).comp S.space.subtypeL
        ∀ (t p B : ℝ),
          ((d : ℝ) - 1 < t ∧ t < (d : ℝ) ∧ 2 ≤ p ∧ 0 ≤ B) →
          ∃ delta0 C : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧ 0 < C ∧
            ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d),
              (0 < M.delta ∧ M.delta ≤ delta0) →
              ∀ (Rinput : Paper.in_responses d M),
                Rinput.C ≤ Cresp →
                4 * p ≤ Cresp⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
                ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
                InfraredCharacterization M H →
                let P : Measure (BilateralField d) :=
                  (chaosSampleLaw M).toMeasure
                let aN : ℕ → BilateralField d → PositiveCoefficient Q := fun N om =>
                  cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos
                let yN : ℕ → BilateralField d → ℝ := fun N om =>
                  inverseResponse S (aN N om) L0
                let yeps : ℝ → ℕ → BilateralField d → ℝ := fun eps N om =>
                  inverseResponse S (aN N om) (Leps eps)
                let ueps : ℝ → ℕ → BilateralField d → S.space := fun eps N om =>
                  responseSolution S (aN N om) (Leps eps)
                ∀ (K : ℕ → BilateralField d → ℝ),
                  (∀ N, AEStronglyMeasurable (K N) P) →
                  (∀ᵐ om ∂P, ∀ N, 0 ≤ K N om) →
                  (∀ᵐ om ∂P,
                    ∀ (N : ℕ) (eps : ℝ),
                      (0 < eps ∧ eps < 1 / 8) →
                      ∀ (x : SpatialCoordinates d) (rad : ℝ),
                        x ∈ Q → (0 < rad ∧ rad ≤ 1) →
                        localGradientEnergy (aN N om)
                            (s := Metric.ball x rad ∩ (Q : Set (SpatialCoordinates d)))
                            (isOpen_ball.measurableSet.inter Q.isOpen.measurableSet)
                            (subspaceGradient S.space (ueps eps N om)) ≤
                          K N om * eps ^ (-2 : ℝ) * rad ^ t) →
                  (∀ N,
                    MemLp (K N) (ENNReal.ofReal (3 * p)) P ∧
                      eLpNorm (K N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B) →
                  (∀ N eps, (0 < eps ∧ eps < 1 / 8) →
                    MemLp (yeps eps N) (ENNReal.ofReal (3 * p)) P ∧
                      eLpNorm (yeps eps N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B) →
                  (∀ N,
                    MemLp (yN N) (ENNReal.ofReal (4 * p)) P ∧
                      eLpNorm (yN N) (ENNReal.ofReal (4 * p)) P ≤ ENNReal.ofReal B) →
                  (∀ N eps, (0 < eps ∧ eps < 1 / 8) →
                    eLpNorm (fun om => yN N om - yeps eps N om)
                      (ENNReal.ofReal p) P ≤
                      ENNReal.ofReal (B * eps ^ (1 / 4 : ℝ))) →
                  (∀ h N : ℕ,
                    let sigma_h := bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h
                    eLpNorm
                      (fun om => yN N om - (P[yN N | sigma_h]) om)
                      (ENNReal.ofReal p) P ≤
                    ENNReal.ofReal
                      (C * Real.sqrt M.delta *
                        (3 : ℝ) ^
                          (-((t * (t - (d : ℝ) + 1) / (t + 1) /
                              (8 * Real.log 3) / 32) * (h : ℝ))))) ∧
                  (∀ h N : ℕ, N < h →
                    let sigma_h := bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h
                    eLpNorm
                      (fun om => yN N om - (P[yN N | sigma_h]) om)
                      (ENNReal.ofReal p) P ≤
                    ENNReal.ofReal
                      (C * M.delta * (3 : ℝ) ^ (-(h : ℝ)))) ) := by
  exact ⟨aux_prop_16_dirichlet, aux_prop_16_neumann⟩

end Paper
