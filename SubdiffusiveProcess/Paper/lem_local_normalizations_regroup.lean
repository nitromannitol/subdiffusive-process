import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
import SubdiffusiveProcess.Paper.rem_bank
import SubdiffusiveProcess.Paper.prop_16
import SubdiffusiveProcess.Paper.prop_response_compact
import SubdiffusiveProcess.Paper.lem_prefix_limit_atom_extraction
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Lane4.CubeDilation
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Lane2.BoundaryResponse
import SubdiffusiveProcess.Lane2.ExternalInputs
import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Sobolev.DomainPoincare
import SubdiffusiveProcess.Sobolev.AffineData
import SubdiffusiveProcess.Lane4.Bridge
import SubdiffusiveProcess.Probability.ConditionalPullback
import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
import Homogenization.Sobolev.H1.BasicLemmas
import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.ScalarFieldPackaging
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SparseLayerReduction
import Mathlib.Analysis.Seminorm
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Tactic




open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Metric
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

def aux_lem_local_normalizations_lnaff_response {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (b : weakSobolevGraph Ω) : SubdiffusiveProcess.Lane3.Response Ω where
  eval g := dirichletResponse S (expPotentialCoefficient g) b
  mass g _ := dirichletResponse S (expPotentialCoefficient g) b
  eval_nonneg g := dirichletResponse_nonneg S _ b
  mass_nonneg g _ := dirichletResponse_nonneg S _ b
  mass_mono _ _ _ _ _ _ := le_rfl
  mass_univ _ := rfl
  exp_comparison g h := by
    have h2 := (dirichletResponse_potential_comparison S b h g).2
    rwa [norm_sub_rev] at h2
  response_perturbation h g _ _ _ := by
    apply aux_lem_prefix_limit_atom_extraction_real_perturb ‖g‖ _ _ (norm_nonneg g)
      (dirichletResponse_nonneg S _ b)
    · have hc := (dirichletResponse_potential_comparison S b h (h + g)).2
      rwa [show h - (h + g) = -g by abel, norm_neg] at hc
    · have hc := (dirichletResponse_potential_comparison S b (h + g) h).2
      rwa [add_sub_cancel_left] at hc
  mass_perturbation h g _ _ _ := by
    have hc := (dirichletResponse_potential_comparison S b h (h + g)).2
    rw [show h - (h + g) = -g by abel, norm_neg] at hc
    have hn := dirichletResponse_nonneg S (expPotentialCoefficient h) b
    have h1 : 1 ≤ 2 * (1 + ‖g‖ ^ 2 * Real.exp (4 * ‖g‖)) := by
      nlinarith [sq_nonneg ‖g‖, Real.exp_pos (4 * ‖g‖), mul_nonneg (sq_nonneg ‖g‖)
        (Real.exp_pos (4 * ‖g‖)).le]
    calc dirichletResponse S (expPotentialCoefficient (h + g)) b
        ≤ Real.exp ‖g‖ * dirichletResponse S (expPotentialCoefficient h) b := hc
      _ ≤ 2 * Real.exp ‖g‖ * (1 + ‖g‖ ^ 2 * Real.exp (4 * ‖g‖)) *
            dirichletResponse S (expPotentialCoefficient h) b := by
          have hE := Real.exp_pos ‖g‖
          nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hE.le hn)]

theorem aux_lem_local_normalizations_lnaff_response_eval {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (b : weakSobolevGraph Ω) (g : SubdiffusiveProcess.Lane3.Potential Ω) :
    (aux_lem_local_normalizations_lnaff_response S b).eval g = dirichletResponse S (expPotentialCoefficient g) b := rfl




section aux_lem_local_normalizations_lnorm_regroup_section

variable (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- Coordinate types for the regrouped bilateral field: index `0` carries the
root layer together with the WHOLE coarse block (so it is band-measurable at
every depth), index `n+1 ≥ 1` carries the negative layer `-(n+1)`, and every
negative index is unused padding. -/
def aux_lem_local_normalizations_lnorm_regroup_Y : ℤ → Type
  | Int.ofNat 0 => C(SpatialCoordinates d, ℝ) × (ℕ → C(SpatialCoordinates d, ℝ))
  | Int.ofNat (_ + 1) => C(SpatialCoordinates d, ℝ)
  | Int.negSucc _ => PUnit

instance aux_lem_local_normalizations_lnorm_regroup_Y_measurableSpace :
    ∀ j : ℤ, MeasurableSpace (aux_lem_local_normalizations_lnorm_regroup_Y d j)
  | Int.ofNat 0 =>
      inferInstanceAs (MeasurableSpace
        (C(SpatialCoordinates d, ℝ) × (ℕ → C(SpatialCoordinates d, ℝ))))
  | Int.ofNat (_ + 1) => inferInstanceAs (MeasurableSpace C(SpatialCoordinates d, ℝ))
  | Int.negSucc _ => inferInstanceAs (MeasurableSpace PUnit)

example : aux_lem_local_normalizations_lnorm_regroup_Y d 0 =
    (C(SpatialCoordinates d, ℝ) × (ℕ → C(SpatialCoordinates d, ℝ))) := rfl

example (n : ℕ) : aux_lem_local_normalizations_lnorm_regroup_Y d (n + 1 : ℕ) = C(SpatialCoordinates d, ℝ) := rfl

example (n : ℕ) : aux_lem_local_normalizations_lnorm_regroup_Y d (Int.negSucc n) = PUnit := rfl

/-! #### Index-level bookkeeping for the three-way `ℤ` split at position `0`. -/

instance aux_lem_local_normalizations_lnorm_regroup_unique_zero : Unique {j : ℤ // ¬ (j ≠ 0)} where
  default := ⟨0, by simp⟩
  uniq := fun x => Subtype.ext (not_not.mp x.2)



def aux_lem_local_normalizations_lnorm_regroup_ePos : ℕ ≃ {i : {j : ℤ // j ≠ 0} // 0 < i.1} where
  toFun n :=
    have hne : (Int.ofNat (n + 1) : ℤ) ≠ 0 := by
      show ((n + 1 : ℕ) : ℤ) ≠ 0
      exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    have hpos : (0 : ℤ) < Int.ofNat (n + 1) := by
      show (0 : ℤ) < ((n + 1 : ℕ) : ℤ)
      exact Nat.cast_pos.mpr (Nat.succ_pos n)
    ⟨⟨Int.ofNat (n + 1), hne⟩, hpos⟩
  invFun i := i.1.1.toNat - 1
  left_inv n := by simp
  right_inv i := by
    obtain ⟨⟨j, hj⟩, hj1⟩ := i
    simp only at hj1
    have hjt : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj1.le
    apply Subtype.ext
    apply Subtype.ext
    show ((j.toNat - 1 + 1 : ℕ) : ℤ) = j
    omega



def aux_lem_local_normalizations_lnorm_regroup_eNeg : ℕ ≃ {i : {j : ℤ // j ≠ 0} // ¬ 0 < i.1} where
  toFun n :=
    have hne : (Int.negSucc n : ℤ) ≠ 0 := Int.negSucc_ne_zero n
    have hnp : ¬ (0 : ℤ) < Int.negSucc n := not_lt.mpr (Int.negSucc_lt_zero n).le
    ⟨⟨Int.negSucc n, hne⟩, hnp⟩
  invFun i := (-i.1.1).toNat - 1
  left_inv n := by simp
  right_inv i := by
    obtain ⟨⟨j, hj⟩, hj1⟩ := i
    simp only at hj1
    have hjneg : j < 0 := by omega
    have hjt : ((-j).toNat : ℤ) = -j := Int.toNat_of_nonneg (by omega)
    apply Subtype.ext
    apply Subtype.ext
    show (Int.negSucc ((-j).toNat - 1) : ℤ) = j
    have hkey : ((-j).toNat - 1 + 1 : ℕ) = (-j).toNat := by omega
    have : (Int.negSucc ((-j).toNat - 1) : ℤ) = -(((-j).toNat - 1 + 1 : ℕ) : ℤ) := by
      simp [Int.negSucc_eq]
    rw [this, hkey, hjt]
    ring

/-! #### The two three-way splits (dependent `Y`-fiber and constant `C`-fiber). -/

abbrev aux_lem_local_normalizations_lnorm_regroup_p : ℤ → Prop := fun j => j ≠ 0
abbrev aux_lem_local_normalizations_lnorm_regroup_q : ℤ → Prop := fun j => 0 < j

instance : DecidablePred (aux_lem_local_normalizations_lnorm_regroup_p) := fun j => inferInstanceAs (Decidable (j ≠ 0))
instance : DecidablePred (aux_lem_local_normalizations_lnorm_regroup_q) := fun j => inferInstanceAs (Decidable (0 < j))

/-- Insert an unused `ℕ → PUnit` padding factor: any type is measurably
equivalent to itself times a space with exactly one point. -/
def aux_lem_local_normalizations_lnorm_regroup_padEquiv (α : Type) [MeasurableSpace α] :
    α ≃ᵐ α × (ℕ → PUnit) where
  toFun a := (a, fun _ => PUnit.unit)
  invFun p := p.1
  left_inv _ := rfl
  right_inv p := by
    obtain ⟨a, f⟩ := p
    congr 1
  measurable_toFun := by fun_prop
  measurable_invFun := measurable_fst

variable {d}

/-- The dependent `Y`-space, split at position `0` and then by sign, with the
positive-index block relabelled to `ℕ → C` and the negative-index block
(unused padding) relabelled to `ℕ → PUnit`. -/
def aux_lem_local_normalizations_lnorm_regroup_ΦY :
    ((j : ℤ) → aux_lem_local_normalizations_lnorm_regroup_Y d j) ≃ᵐ
      ((ℕ → C(SpatialCoordinates d, ℝ)) × (ℕ → PUnit)) ×
        (C(SpatialCoordinates d, ℝ) × (ℕ → C(SpatialCoordinates d, ℝ))) :=
  (threeBlockEquiv (X := aux_lem_local_normalizations_lnorm_regroup_Y d)
      aux_lem_local_normalizations_lnorm_regroup_p aux_lem_local_normalizations_lnorm_regroup_q).trans
    (((MeasurableEquiv.piCongrLeft (fun i => aux_lem_local_normalizations_lnorm_regroup_Y d i.1.1)
          aux_lem_local_normalizations_lnorm_regroup_ePos).symm.prodCongr
        (MeasurableEquiv.piCongrLeft (fun i => aux_lem_local_normalizations_lnorm_regroup_Y d i.1.1)
          aux_lem_local_normalizations_lnorm_regroup_eNeg).symm).prodCongr
      (MeasurableEquiv.piUnique
        (fun i : {i : ℤ // ¬ aux_lem_local_normalizations_lnorm_regroup_p i} => aux_lem_local_normalizations_lnorm_regroup_Y d i)))

/-- The original bilateral field, split the same way (constant `C` fiber). -/
def aux_lem_local_normalizations_lnorm_regroup_ΦC :
    (ℤ → C(SpatialCoordinates d, ℝ)) ≃ᵐ
      ((ℕ → C(SpatialCoordinates d, ℝ)) × (ℕ → C(SpatialCoordinates d, ℝ))) ×
        C(SpatialCoordinates d, ℝ) :=
  (threeBlockEquiv (X := fun _ : ℤ => C(SpatialCoordinates d, ℝ))
      aux_lem_local_normalizations_lnorm_regroup_p aux_lem_local_normalizations_lnorm_regroup_q).trans
    (((MeasurableEquiv.piCongrLeft (fun _ => C(SpatialCoordinates d, ℝ))
          aux_lem_local_normalizations_lnorm_regroup_ePos).symm.prodCongr
        (MeasurableEquiv.piCongrLeft (fun _ => C(SpatialCoordinates d, ℝ))
          aux_lem_local_normalizations_lnorm_regroup_eNeg).symm).prodCongr
      (MeasurableEquiv.funUnique {i : ℤ // ¬ aux_lem_local_normalizations_lnorm_regroup_p i}
        C(SpatialCoordinates d, ℝ)))

/-- Pure bookkeeping: reorder `(coarse, fine, root)` into `(fine, padding, root, coarse)`,
inserting the unused padding factor. -/
def aux_lem_local_normalizations_lnorm_regroup_bridge :
    ((ℕ → C(SpatialCoordinates d, ℝ)) × (ℕ → C(SpatialCoordinates d, ℝ))) ×
        C(SpatialCoordinates d, ℝ) ≃ᵐ
      ((ℕ → C(SpatialCoordinates d, ℝ)) × (ℕ → PUnit)) ×
        (C(SpatialCoordinates d, ℝ) × (ℕ → C(SpatialCoordinates d, ℝ))) :=
  ((MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl _)).trans
    (MeasurableEquiv.prodAssoc.trans
      ((MeasurableEquiv.refl _).prodCongr MeasurableEquiv.prodComm))).trans
    ((aux_lem_local_normalizations_lnorm_regroup_padEquiv _).prodCongr (MeasurableEquiv.refl _))

/-- **The regroup equivalence.** Index `0` carries the root layer together with
the whole coarse block, and the fine (negative) layers are relabelled onto the
positive indices, matching `aux_lem_local_normalizations_lnorm_regroup_Y`. -/
def aux_lem_local_normalizations_lnorm_regroup :
    (ℤ → C(SpatialCoordinates d, ℝ)) ≃ᵐ ((j : ℤ) → aux_lem_local_normalizations_lnorm_regroup_Y d j) :=
  (aux_lem_local_normalizations_lnorm_regroup_ΦC.trans aux_lem_local_normalizations_lnorm_regroup_bridge).trans aux_lem_local_normalizations_lnorm_regroup_ΦY.symm

/-! #### Measure preservation. -/

variable (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)

/-- The root layer, coarse-block, and fine-block laws out of which every
measure in this file is assembled. -/
def aux_lem_local_normalizations_lnorm_regroup_rootLaw : Measure C(SpatialCoordinates d, ℝ) :=
  (scaledLayerLaw d (chaosRootFieldLaw M) 0).toMeasure

def aux_lem_local_normalizations_lnorm_regroup_coarseLaws : ℕ → Measure C(SpatialCoordinates d, ℝ) :=
  fun n => (scaledLayerLaw d (chaosRootFieldLaw M) ((n : ℤ) + 1)).toMeasure

def aux_lem_local_normalizations_lnorm_regroup_fineLaws : ℕ → Measure C(SpatialCoordinates d, ℝ) :=
  fun n => (scaledLayerLaw d (chaosRootFieldLaw M) (Int.negSucc n)).toMeasure

instance : IsProbabilityMeasure (aux_lem_local_normalizations_lnorm_regroup_rootLaw M) := by
  unfold aux_lem_local_normalizations_lnorm_regroup_rootLaw; infer_instance

instance (n : ℕ) : IsProbabilityMeasure (aux_lem_local_normalizations_lnorm_regroup_coarseLaws M n) := by
  unfold aux_lem_local_normalizations_lnorm_regroup_coarseLaws; infer_instance

instance (n : ℕ) : IsProbabilityMeasure (aux_lem_local_normalizations_lnorm_regroup_fineLaws M n) := by
  unfold aux_lem_local_normalizations_lnorm_regroup_fineLaws; infer_instance

/-- The `Y`-space laws, matching `aux_lem_local_normalizations_lnorm_regroup_Y`'s own case split: index
`0` carries the root and the whole coarse block, index `n + 1` carries the
fine (original negative) layer `-(n+1)`, and every negative index is a point
mass on the unused padding coordinate. -/
def aux_lem_local_normalizations_lnorm_regroup_laws : ∀ j : ℤ, Measure (aux_lem_local_normalizations_lnorm_regroup_Y d j)
  | Int.ofNat 0 =>
      (aux_lem_local_normalizations_lnorm_regroup_rootLaw M).prod
        (Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_coarseLaws M))
  | Int.ofNat (n + 1) => aux_lem_local_normalizations_lnorm_regroup_fineLaws M n
  | Int.negSucc _ => Measure.dirac PUnit.unit

instance aux_lem_local_normalizations_lnorm_regroup_laws_isProbabilityMeasure :
    ∀ j : ℤ, IsProbabilityMeasure (aux_lem_local_normalizations_lnorm_regroup_laws M j)
  | Int.ofNat 0 => inferInstanceAs (IsProbabilityMeasure
      ((aux_lem_local_normalizations_lnorm_regroup_rootLaw M).prod
        (Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_coarseLaws M))))
  | Int.ofNat (n + 1) => inferInstanceAs (IsProbabilityMeasure (aux_lem_local_normalizations_lnorm_regroup_fineLaws M n))
  | Int.negSucc _ => inferInstanceAs (IsProbabilityMeasure (Measure.dirac PUnit.unit))

/-- The original, un-regrouped bilateral-field layer laws. -/
def aux_lem_local_normalizations_lnorm_regroup_laws0 : ℤ → Measure C(SpatialCoordinates d, ℝ) :=
  fun j => (scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure

instance (j : ℤ) : IsProbabilityMeasure (aux_lem_local_normalizations_lnorm_regroup_laws0 M j) := by
  unfold aux_lem_local_normalizations_lnorm_regroup_laws0; infer_instance

theorem aux_lem_local_normalizations_lnorm_regroup_chaosSampleLaw_eq :
    (chaosSampleLaw M).toMeasure = Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_laws0 M) := rfl

/-! #### Generic relabelling lemmas, reused for both the `Y`-fiber and the
constant-`C`-fiber applications. -/

theorem aux_lem_local_normalizations_lnorm_regroup_piCongrLeft_mp {ι : Type} (e : ℕ ≃ ι)
    {F : ι → Type} [∀ i, MeasurableSpace (F i)] (μ : ∀ i, Measure (F i))
    [∀ i, IsProbabilityMeasure (μ i)] :
    MeasurePreserving (MeasurableEquiv.piCongrLeft F e)
      (Measure.infinitePi (fun n => μ (e n))) (Measure.infinitePi μ) :=
  ⟨(MeasurableEquiv.piCongrLeft F e).measurable, Measure.infinitePi_map_piCongrLeft μ e⟩

theorem aux_lem_local_normalizations_lnorm_regroup_piUnique_mp {ι : Type} [Unique ι] [Fintype ι]
    {F : ι → Type} [∀ i, MeasurableSpace (F i)] (μ : ∀ i, Measure (F i))
    [∀ i, IsProbabilityMeasure (μ i)] :
    MeasurePreserving (MeasurableEquiv.piUnique F) (Measure.infinitePi μ) (μ default) := by
  rw [Measure.infinitePi_eq_pi]
  exact measurePreserving_piUnique μ




theorem aux_lem_local_normalizations_lnorm_regroup_hΦC :
    MeasurePreserving (aux_lem_local_normalizations_lnorm_regroup_ΦC (d := d)) (chaosSampleLaw M).toMeasure
      (((Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_coarseLaws M)).prod
          (Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_fineLaws M))).prod
        (aux_lem_local_normalizations_lnorm_regroup_rootLaw M)) := by
  rw [aux_lem_local_normalizations_lnorm_regroup_chaosSampleLaw_eq]
  have hstep1 := measurePreserving_infinitePi_threeBlock (aux_lem_local_normalizations_lnorm_regroup_laws0 M)
    aux_lem_local_normalizations_lnorm_regroup_p aux_lem_local_normalizations_lnorm_regroup_q (X := fun _ : ℤ => C(SpatialCoordinates d, ℝ))
  have hpos := (aux_lem_local_normalizations_lnorm_regroup_piCongrLeft_mp aux_lem_local_normalizations_lnorm_regroup_ePos
    (fun i : {i : {j : ℤ // aux_lem_local_normalizations_lnorm_regroup_p j} // aux_lem_local_normalizations_lnorm_regroup_q i.1} =>
      aux_lem_local_normalizations_lnorm_regroup_laws0 M i.1.1)).symm
  have hneg := (aux_lem_local_normalizations_lnorm_regroup_piCongrLeft_mp aux_lem_local_normalizations_lnorm_regroup_eNeg
    (fun i : {i : {j : ℤ // aux_lem_local_normalizations_lnorm_regroup_p j} // ¬ aux_lem_local_normalizations_lnorm_regroup_q i.1} =>
      aux_lem_local_normalizations_lnorm_regroup_laws0 M i.1.1)).symm
  have hzero := aux_lem_local_normalizations_lnorm_regroup_piUnique_mp
    (fun i : {i : ℤ // ¬ aux_lem_local_normalizations_lnorm_regroup_p i} => aux_lem_local_normalizations_lnorm_regroup_laws0 M i)
  exact ((hpos.prod hneg).prod hzero).comp hstep1

theorem aux_lem_local_normalizations_lnorm_regroup_hΦY :
    MeasurePreserving (aux_lem_local_normalizations_lnorm_regroup_ΦY (d := d)) (Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_laws M))
      (((Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_fineLaws M)).prod
          (Measure.dirac (fun _ : ℕ => PUnit.unit))).prod
        ((aux_lem_local_normalizations_lnorm_regroup_rootLaw M).prod
          (Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_coarseLaws M)))) := by
  have hstep1 := measurePreserving_infinitePi_threeBlock (aux_lem_local_normalizations_lnorm_regroup_laws M)
    aux_lem_local_normalizations_lnorm_regroup_p aux_lem_local_normalizations_lnorm_regroup_q (X := aux_lem_local_normalizations_lnorm_regroup_Y d)
  have hpos := (aux_lem_local_normalizations_lnorm_regroup_piCongrLeft_mp aux_lem_local_normalizations_lnorm_regroup_ePos
    (fun i : {i : {j : ℤ // aux_lem_local_normalizations_lnorm_regroup_p j} // aux_lem_local_normalizations_lnorm_regroup_q i.1} =>
      aux_lem_local_normalizations_lnorm_regroup_laws M i.1.1)).symm
  have hneg0 := (aux_lem_local_normalizations_lnorm_regroup_piCongrLeft_mp aux_lem_local_normalizations_lnorm_regroup_eNeg
    (fun i : {i : {j : ℤ // aux_lem_local_normalizations_lnorm_regroup_p j} // ¬ aux_lem_local_normalizations_lnorm_regroup_q i.1} =>
      aux_lem_local_normalizations_lnorm_regroup_laws M i.1.1)).symm
  have heq : (Measure.infinitePi (fun n : ℕ =>
      aux_lem_local_normalizations_lnorm_regroup_laws M (aux_lem_local_normalizations_lnorm_regroup_eNeg n).1.1)) =
      Measure.dirac (fun _ : ℕ => PUnit.unit) := by
    rw [show (fun n : ℕ => aux_lem_local_normalizations_lnorm_regroup_laws M (aux_lem_local_normalizations_lnorm_regroup_eNeg n).1.1) =
        (fun _ : ℕ => (Measure.dirac PUnit.unit : Measure PUnit)) from rfl]
    exact Measure.infinitePi_dirac _
  have hneg : MeasurePreserving _
      (Measure.infinitePi (fun i : {i : {j : ℤ // aux_lem_local_normalizations_lnorm_regroup_p j} //
          ¬ aux_lem_local_normalizations_lnorm_regroup_q i.1} => aux_lem_local_normalizations_lnorm_regroup_laws M i.1.1))
      (Measure.dirac (fun _ : ℕ => PUnit.unit)) := heq ▸ hneg0
  have hzero := aux_lem_local_normalizations_lnorm_regroup_piUnique_mp
    (fun i : {i : ℤ // ¬ aux_lem_local_normalizations_lnorm_regroup_p i} => aux_lem_local_normalizations_lnorm_regroup_laws M i)
  exact ((hpos.prod hneg).prod hzero).comp hstep1

theorem aux_lem_local_normalizations_lnorm_regroup_hBridge :
    MeasurePreserving (aux_lem_local_normalizations_lnorm_regroup_bridge (d := d))
      (((Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_coarseLaws M)).prod
          (Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_fineLaws M))).prod
        (aux_lem_local_normalizations_lnorm_regroup_rootLaw M))
      (((Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_fineLaws M)).prod
          (Measure.dirac (fun _ : ℕ => PUnit.unit))).prod
        ((aux_lem_local_normalizations_lnorm_regroup_rootLaw M).prod
          (Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_coarseLaws M)))) := by
  have h1 := (Measure.measurePreserving_swap
      (μ := Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_coarseLaws M))
      (ν := Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_fineLaws M))).prod
    (MeasurePreserving.id (aux_lem_local_normalizations_lnorm_regroup_rootLaw M))
  have h2 := measurePreserving_prodAssoc
    (Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_fineLaws M))
    (Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_coarseLaws M)) (aux_lem_local_normalizations_lnorm_regroup_rootLaw M)
  have h3 := (MeasurePreserving.id (Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_fineLaws M))).prod
    (Measure.measurePreserving_swap (μ := Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_coarseLaws M))
      (ν := aux_lem_local_normalizations_lnorm_regroup_rootLaw M))
  have h4 : MeasurePreserving (aux_lem_local_normalizations_lnorm_regroup_padEquiv (ℕ → C(SpatialCoordinates d, ℝ)))
      (Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_fineLaws M))
      ((Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_fineLaws M)).prod
        (Measure.dirac (fun _ : ℕ => PUnit.unit))) :=
    ⟨(aux_lem_local_normalizations_lnorm_regroup_padEquiv _).measurable, (Measure.prod_dirac _).symm⟩
  have h5 := h4.prod
    (MeasurePreserving.id ((aux_lem_local_normalizations_lnorm_regroup_rootLaw M).prod
      (Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_coarseLaws M))))
  exact h5.comp (h3.comp (h2.comp h1))

/-- **The regroup measure-preserving equivalence.** The regrouped bilateral
field carries `chaosSampleLaw M` to `Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_laws M)`:
index `0` is band-measurable at every depth `H`, since `0 ∈ bandSet H` always. -/
theorem aux_lem_local_normalizations_lnorm_regroup_measurePreserving :
    MeasurePreserving (aux_lem_local_normalizations_lnorm_regroup (d := d)) (chaosSampleLaw M).toMeasure
      (Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_laws M)) :=
  (MeasurePreserving.symm aux_lem_local_normalizations_lnorm_regroup_ΦY (aux_lem_local_normalizations_lnorm_regroup_hΦY M)).comp
    ((aux_lem_local_normalizations_lnorm_regroup_hBridge M).comp (aux_lem_local_normalizations_lnorm_regroup_hΦC M))

end aux_lem_local_normalizations_lnorm_regroup_section




section aux_lem_local_normalizations_lnorm_htilde_section

variable (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]

/-- `infraredPartialSum`'s defining finite sum, applied directly to a raw sequence of positive
layers `ctail : ℕ → C(SpatialCoordinates d, ℝ)` (rather than to `fun n => omega (n + 1)`). -/
def aux_lem_local_normalizations_lnorm_htilde_partialSumOfSeq (ctail : ℕ → C(SpatialCoordinates d, ℝ)) (L : ℕ) :
    C(SpatialCoordinates d, ℝ) :=
  Finset.sum (Finset.range L) (fun n => ctail n - ContinuousMap.const _ (ctail n 0))

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lem_local_normalizations_lnorm_htilde_partialSumOfSeq_eq_infraredPartialSum
    (omega : BilateralField d) (L : ℕ) :
    aux_lem_local_normalizations_lnorm_htilde_partialSumOfSeq d (fun n => omega (n + 1)) L =
      infraredPartialSum omega L :=
  rfl

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lem_local_normalizations_lnorm_htilde_partialSumOfSeq_continuous (L : ℕ) :
    Continuous (fun ctail : ℕ → C(SpatialCoordinates d, ℝ) =>
      aux_lem_local_normalizations_lnorm_htilde_partialSumOfSeq d ctail L) := by
  unfold aux_lem_local_normalizations_lnorm_htilde_partialSumOfSeq
  refine continuous_finset_sum _ (fun n _ => Continuous.sub ?_ ?_)
  · exact continuous_apply n
  · exact ContinuousMap.continuous_const'.comp
      ((continuous_eval_const (0 : SpatialCoordinates d)).comp (continuous_apply n))

/-- The genuinely total (limit-or-`0`) proxy for the infrared field, as a function of the raw
positive-layer sequence alone. -/
noncomputable def aux_lem_local_normalizations_lnorm_htilde (ctail : ℕ → C(SpatialCoordinates d, ℝ)) :
    C(SpatialCoordinates d, ℝ) :=
  limUnder Filter.atTop (aux_lem_local_normalizations_lnorm_htilde_partialSumOfSeq d ctail)

theorem aux_lem_local_normalizations_lnorm_htilde_measurable [BorelSpace C(SpatialCoordinates d, ℝ)] :
    Measurable (aux_lem_local_normalizations_lnorm_htilde d) := by
  have hSM : ∀ L : ℕ, StronglyMeasurable
      (fun ctail : ℕ → C(SpatialCoordinates d, ℝ) => aux_lem_local_normalizations_lnorm_htilde_partialSumOfSeq d ctail L) :=
    fun L => (aux_lem_local_normalizations_lnorm_htilde_partialSumOfSeq_continuous d L).stronglyMeasurable
  unfold aux_lem_local_normalizations_lnorm_htilde
  exact (MeasureTheory.StronglyMeasurable.limUnder (l := Filter.atTop) hSM).measurable

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lem_local_normalizations_lnorm_htilde_eq_of_tendsto {ctail : ℕ → C(SpatialCoordinates d, ℝ)}
    {c : C(SpatialCoordinates d, ℝ)}
    (h : Filter.Tendsto (aux_lem_local_normalizations_lnorm_htilde_partialSumOfSeq d ctail) Filter.atTop (nhds c)) :
    aux_lem_local_normalizations_lnorm_htilde d ctail = c := by
  unfold aux_lem_local_normalizations_lnorm_htilde
  exact h.limUnder_eq

theorem aux_lem_local_normalizations_lnorm_htilde_eq_H_ae [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d}
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)}
    (hH : InfraredCharacterization M H) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, aux_lem_local_normalizations_lnorm_htilde d (fun n => omega (n + 1)) = H omega := by
  filter_upwards [hH.2] with omega hten
  apply aux_lem_local_normalizations_lnorm_htilde_eq_of_tendsto
  have heq : aux_lem_local_normalizations_lnorm_htilde_partialSumOfSeq d (fun n => omega (n + 1)) =
      infraredPartialSum omega :=
    funext (aux_lem_local_normalizations_lnorm_htilde_partialSumOfSeq_eq_infraredPartialSum d omega)
  rw [heq]
  exact hten

end aux_lem_local_normalizations_lnorm_htilde_section

/-- **The pointwise action of `aux_lem_local_normalizations_lnorm_regroup` at coordinate `0`.** Coordinate `0` of the
regrouped field is exactly the pair (root layer, whole coarse block), by RFL: `aux_lem_local_normalizations_lnorm_regroup`'s
composite unfolds through `threeBlockEquiv`/`piEquivPiSubtypeProd` and, at index `0` (which always
lands in the `¬p`/"zero" branch, since `aux_lem_local_normalizations_lnorm_regroup_p 0 = (0 ≠ 0)` is decidably `False`),
through `piUnique`/`uniqueElim` at the unique point of `{j : ℤ // ¬ aux_lem_local_normalizations_lnorm_regroup_p j}` — none of
which touches the `ePos`/`eNeg` relabelling (that only matters for coordinates `n+1`/`negSucc n`), so
no non-`rfl` equivalence proof is on the reduction path. -/
theorem aux_lem_local_normalizations_lnorm_regroup_apply_zero (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (omega : BilateralField d) :
    aux_lem_local_normalizations_lnorm_regroup omega 0 = (omega 0, fun n : ℕ => omega ((n : ℤ) + 1)) := by
  rfl



theorem aux_lem_local_normalizations_lnorm_regroup_bridgeC_apply (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (omega : BilateralField d) :
    aux_lem_local_normalizations_lnorm_regroup_bridge (aux_lem_local_normalizations_lnorm_regroup_ΦC omega) =
      ((fun n : ℕ => omega (Int.negSucc n), fun _ : ℕ => PUnit.unit),
        (omega 0, fun n : ℕ => omega ((n : ℤ) + 1))) := by
  rfl

/-- **The pointwise action of `aux_lem_local_normalizations_lnorm_regroup` at coordinates `n+1` (the relabelled negative
layers).** Unlike `aux_lem_local_normalizations_lnorm_regroup_apply_zero`, this is NOT provable by bare `rfl`: coordinate
`n+1` (for symbolic `n`) is routed through `ΦY.symm`'s forward `piCongrLeft` step, whose underlying
cast is only propositionally (not syntactically-`rfl`) trivial for a symbolic index, unlike the
`Unique`-typed "zero" branch. The proof instead threads the two nested `piEquivPiSubtypeProd.symm`
`dite`s explicitly via `dif_pos` (on the always-true facts `aux_lem_local_normalizations_lnorm_regroup_p (n+1)` and
`aux_lem_local_normalizations_lnorm_regroup_q (n+1)`) and closes with `MeasurableEquiv.piCongrLeft_apply_apply`. -/
theorem aux_lem_local_normalizations_lnorm_regroup_apply_succ (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (omega : BilateralField d) (n : ℕ) :
    aux_lem_local_normalizations_lnorm_regroup omega ((n : ℤ) + 1) = omega (Int.negSucc n) := by
  show aux_lem_local_normalizations_lnorm_regroup_ΦY.symm (aux_lem_local_normalizations_lnorm_regroup_bridge (aux_lem_local_normalizations_lnorm_regroup_ΦC omega))
      ((n : ℤ) + 1) = omega (Int.negSucc n)
  rw [aux_lem_local_normalizations_lnorm_regroup_bridgeC_apply]
  show (threeBlockEquiv aux_lem_local_normalizations_lnorm_regroup_p aux_lem_local_normalizations_lnorm_regroup_q).symm
      (((MeasurableEquiv.piCongrLeft (fun i : {i : {j : ℤ // aux_lem_local_normalizations_lnorm_regroup_p j} //
              aux_lem_local_normalizations_lnorm_regroup_q i.1} => aux_lem_local_normalizations_lnorm_regroup_Y d i.1.1) aux_lem_local_normalizations_lnorm_regroup_ePos).prodCongr
          (MeasurableEquiv.piCongrLeft (fun i : {i : {j : ℤ // aux_lem_local_normalizations_lnorm_regroup_p j} //
              ¬ aux_lem_local_normalizations_lnorm_regroup_q i.1} => aux_lem_local_normalizations_lnorm_regroup_Y d i.1.1) aux_lem_local_normalizations_lnorm_regroup_eNeg)).prodCongr
        (MeasurableEquiv.piUnique
          (fun i : {i : ℤ // ¬ aux_lem_local_normalizations_lnorm_regroup_p i} => aux_lem_local_normalizations_lnorm_regroup_Y d i)).symm
        ((fun k : ℕ => omega (Int.negSucc k), fun _ : ℕ => (PUnit.unit : PUnit)),
          (omega 0, fun k : ℕ => omega ((k : ℤ) + 1))))
      ((n : ℤ) + 1) = omega (Int.negSucc n)
  show (MeasurableEquiv.piEquivPiSubtypeProd (fun j : ℤ => aux_lem_local_normalizations_lnorm_regroup_Y d j)
        aux_lem_local_normalizations_lnorm_regroup_p).symm
      (((MeasurableEquiv.piEquivPiSubtypeProd
            (fun i : {j : ℤ // aux_lem_local_normalizations_lnorm_regroup_p j} => aux_lem_local_normalizations_lnorm_regroup_Y d i.1)
            (fun i : {j : ℤ // aux_lem_local_normalizations_lnorm_regroup_p j} => aux_lem_local_normalizations_lnorm_regroup_q i.1)).prodCongr
          (MeasurableEquiv.refl _)).symm
        (((MeasurableEquiv.piCongrLeft (fun i : {i : {j : ℤ // aux_lem_local_normalizations_lnorm_regroup_p j} //
                aux_lem_local_normalizations_lnorm_regroup_q i.1} => aux_lem_local_normalizations_lnorm_regroup_Y d i.1.1) aux_lem_local_normalizations_lnorm_regroup_ePos)
              (fun k : ℕ => omega (Int.negSucc k)),
            (MeasurableEquiv.piCongrLeft (fun i : {i : {j : ℤ // aux_lem_local_normalizations_lnorm_regroup_p j} //
                ¬ aux_lem_local_normalizations_lnorm_regroup_q i.1} => aux_lem_local_normalizations_lnorm_regroup_Y d i.1.1) aux_lem_local_normalizations_lnorm_regroup_eNeg)
              (fun _ : ℕ => (PUnit.unit : PUnit))),
          (MeasurableEquiv.piUnique
            (fun i : {i : ℤ // ¬ aux_lem_local_normalizations_lnorm_regroup_p i} => aux_lem_local_normalizations_lnorm_regroup_Y d i)).symm
            (omega 0, fun k : ℕ => omega ((k : ℤ) + 1))))
      ((n : ℤ) + 1) = omega (Int.negSucc n)
  have hp' : aux_lem_local_normalizations_lnorm_regroup_p ((n : ℤ) + 1) := by
    show ((n : ℤ) + 1) ≠ 0
    omega
  have hq' : aux_lem_local_normalizations_lnorm_regroup_q (⟨(n : ℤ) + 1, hp'⟩ : {j : ℤ // aux_lem_local_normalizations_lnorm_regroup_p j}).1 := by
    show (0 : ℤ) < (n : ℤ) + 1
    omega
  simp only [MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]
  rw [dif_pos hp']
  show (MeasurableEquiv.piEquivPiSubtypeProd
      (fun i : {j : ℤ // aux_lem_local_normalizations_lnorm_regroup_p j} => aux_lem_local_normalizations_lnorm_regroup_Y d i.1)
      (fun i : {j : ℤ // aux_lem_local_normalizations_lnorm_regroup_p j} => aux_lem_local_normalizations_lnorm_regroup_q i.1)).symm
    ((MeasurableEquiv.piCongrLeft (fun i : {i : {j : ℤ // aux_lem_local_normalizations_lnorm_regroup_p j} //
          aux_lem_local_normalizations_lnorm_regroup_q i.1} => aux_lem_local_normalizations_lnorm_regroup_Y d i.1.1) aux_lem_local_normalizations_lnorm_regroup_ePos)
        (fun k : ℕ => omega (Int.negSucc k)),
      (MeasurableEquiv.piCongrLeft (fun i : {i : {j : ℤ // aux_lem_local_normalizations_lnorm_regroup_p j} //
          ¬ aux_lem_local_normalizations_lnorm_regroup_q i.1} => aux_lem_local_normalizations_lnorm_regroup_Y d i.1.1) aux_lem_local_normalizations_lnorm_regroup_eNeg)
        (fun _ : ℕ => (PUnit.unit : PUnit)))
    ⟨(n : ℤ) + 1, hp'⟩ = omega (Int.negSucc n)
  simp only [MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]
  rw [dif_pos hq']
  exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun i : {i : {j : ℤ // aux_lem_local_normalizations_lnorm_regroup_p j} //
        aux_lem_local_normalizations_lnorm_regroup_q i.1} => aux_lem_local_normalizations_lnorm_regroup_Y d i.1.1) aux_lem_local_normalizations_lnorm_regroup_ePos
    (fun k : ℕ => omega (Int.negSucc k)) n

/-! ============ `rembank_moments_PROVED.lean` (already landed, copied verbatim) ============ -/

/-- Generic: from a bound on a left-associated sum of six `ℝ≥0∞` terms, extract that the third and
fifth summands are individually `≤ B`. -/
theorem aux_lem_local_normalizations_ennreal_le_of_add_six {a1 a2 a3 a4 a5 a6 B : ℝ≥0∞}
    (h : a1 + a2 + a3 + a4 + a5 + a6 ≤ B) :
    a3 ≤ B ∧ a5 ≤ B := by
  have e3 : a3 ≤ a1 + a2 + a3 + a4 + a5 + a6 := by
    calc a3 = 0 + 0 + a3 + 0 + 0 + 0 := by ring
      _ ≤ a1 + a2 + a3 + a4 + a5 + a6 := by gcongr <;> exact zero_le _
  have e5 : a5 ≤ a1 + a2 + a3 + a4 + a5 + a6 := by
    calc a5 = 0 + 0 + 0 + 0 + a5 + 0 := by ring
      _ ≤ a1 + a2 + a3 + a4 + a5 + a6 := by gcongr <;> exact zero_le _
  exact ⟨e3.trans h, e5.trans h⟩

theorem aux_lem_local_normalizations_test_rembank_rd_moments
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (W : SmallPerturbationInput d) (Sf : SobolevFoundationalInput d hd)
    (D : @lane4_deterministic_good_scale_input d ⟨by omega⟩) :
    ∃ (q : ℝ) (delta0 : ℝ), 2 < q ∧ 0 < delta0 ∧
    ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
    ∀ (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
      (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ ∞ phi)
      (b : weakSobolevGraph (centeredCube z r hr))
      (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi),
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (Rm : in_responses d M) (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ))
      (hH : InfraredCharacterization M H),
      M.delta ≤ min 1 delta0 →
      let Pm : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
      let a : ℕ → BilateralField d → PositiveCoefficient (centeredCube z r hr) :=
        fun N omega => cutoffPositiveCoefficient M H omega N z hr
      let RD : ℕ → BilateralField d → ℝ :=
        fun N omega => dirichletResponse (killedResponseSpace hP) (a N omega) b
      ∃ Cmom : ℝ, 0 ≤ Cmom ∧
        ∀ N, MemLp (RD N) (ENNReal.ofReal 6) Pm ∧ MemLp (RD N) (ENNReal.ofReal q) Pm ∧
          eLpNorm (RD N) (ENNReal.ofReal 6) Pm ≤ ENNReal.ofReal Cmom ∧
          eLpNorm (RD N) (ENNReal.ofReal q) Pm ≤ ENNReal.ofReal Cmom := by
  have ht0 : (d : ℝ) - 1 < (d : ℝ) - 1 / 2 := by linarith
  have ht1 : (d : ℝ) - 1 / 2 < (d : ℝ) := by linarith
  obtain ⟨aexpOf, qOf, ordersOf, thresholdOf, _, _, haexppos, haexpeq, hmain⟩ :=
    rem_bank d hd Jc Pc Xc W Sf D ((d : ℝ) - 1 / 2) ht0 ht1
  obtain ⟨hpq, hdeltapos, h3p, hqmem, h12p, h4q, hall⟩ := hmain 2 (by norm_num)
  refine ⟨qOf 2 d ((d:ℝ) - 1/2), thresholdOf d ((d:ℝ)-1/2) (ordersOf 2 d ((d:ℝ)-1/2)),
    by linarith, hdeltapos, ?_⟩
  intro z r hr hrle hP phi hphi b hb M Rm Sreg It H hH hdelta
  intro Pm a RD
  obtain ⟨hdir, -, -⟩ := hall M Rm Sreg It H hH hdelta
  obtain ⟨KD, KK, B, hB0, -, hmemLp, hnormsum⟩ :=
    hdir z r hr hrle hP phi hphi b hb (0 : SpatialCoordinates d → ℝ) contDiff_const
      HasCompactSupport.zero (by simp) (domainConstantL2 (Ω := centeredCube z r hr) 0)
      (domainConstantL2_coeFn 0)
  have h6 : (3 : ℝ) * 2 = 6 := by norm_num
  rw [h6] at hnormsum hmemLp
  refine ⟨B, hB0, fun N => ⟨(hmemLp N).2.2.1, (hmemLp N).2.2.2.2.1,
    aux_lem_local_normalizations_ennreal_le_of_add_six (hnormsum N)⟩⟩

/-! ============ `prop16_band_PROVED.lean` (already landed, copied verbatim) ============ -/

/-- Generic six-term extraction, all six individual bounds. -/
theorem aux_lem_local_normalizations_prop16_le_of_add_six {a1 a2 a3 a4 a5 a6 B : ℝ≥0∞}
    (h : a1 + a2 + a3 + a4 + a5 + a6 ≤ B) :
    a1 ≤ B ∧ a2 ≤ B ∧ a3 ≤ B ∧ a4 ≤ B ∧ a5 ≤ B ∧ a6 ≤ B := by
  have e1 : a1 ≤ a1 + a2 + a3 + a4 + a5 + a6 := by
    calc a1 = a1 + 0 + 0 + 0 + 0 + 0 := by ring
      _ ≤ a1 + a2 + a3 + a4 + a5 + a6 := by gcongr <;> exact zero_le _
  have e2 : a2 ≤ a1 + a2 + a3 + a4 + a5 + a6 := by
    calc a2 = 0 + a2 + 0 + 0 + 0 + 0 := by ring
      _ ≤ a1 + a2 + a3 + a4 + a5 + a6 := by gcongr <;> exact zero_le _
  have e3 : a3 ≤ a1 + a2 + a3 + a4 + a5 + a6 := by
    calc a3 = 0 + 0 + a3 + 0 + 0 + 0 := by ring
      _ ≤ a1 + a2 + a3 + a4 + a5 + a6 := by gcongr <;> exact zero_le _
  have e4 : a4 ≤ a1 + a2 + a3 + a4 + a5 + a6 := by
    calc a4 = 0 + 0 + 0 + a4 + 0 + 0 := by ring
      _ ≤ a1 + a2 + a3 + a4 + a5 + a6 := by gcongr <;> exact zero_le _
  have e5 : a5 ≤ a1 + a2 + a3 + a4 + a5 + a6 := by
    calc a5 = 0 + 0 + 0 + 0 + a5 + 0 := by ring
      _ ≤ a1 + a2 + a3 + a4 + a5 + a6 := by gcongr <;> exact zero_le _
  have e6 : a6 ≤ a1 + a2 + a3 + a4 + a5 + a6 := by
    calc a6 = 0 + 0 + 0 + 0 + 0 + a6 := by ring
      _ ≤ a1 + a2 + a3 + a4 + a5 + a6 := by gcongr <;> exact zero_le _
  exact ⟨e1.trans h, e2.trans h, e3.trans h, e4.trans h, e5.trans h, e6.trans h⟩

/-- `lem_local_normalizations`'s own `kap`, restated. -/
def aux_lem_local_normalizations_prop16_kap {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) : ℝ :=
  Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N

theorem aux_lem_local_normalizations_prop16_kap_pos {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) :
    0 < aux_lem_local_normalizations_prop16_kap M N :=
  mul_pos (Real.exp_pos _) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)

/-- The `prop_16` Dirichlet band exponent at `t = d - 1/2`. -/
def aux_lem_local_normalizations_prop16_aD (d : ℕ) : ℝ :=
  ((d : ℝ) - 1 / 2) * (((d : ℝ) - 1 / 2) - (d : ℝ) + 1) / (((d : ℝ) - 1 / 2) + 1) /
    (8 * Real.log 3)

/-- `cutoffPositiveCoefficient`'s value is `exp(cutoffPotential - log kap)`, for ANY cell
`(z, r, hr)`. -/
theorem aux_lem_local_normalizations_prop16_cutoff_ae_exp {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ) (omega : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ((cutoffPositiveCoefficient M H omega N z hr).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      (fun x => Real.exp (cutoffPotential H omega N x - Real.log (aux_lem_local_normalizations_prop16_kap M N))) := by
  haveI : Fact ((centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ closedCube z r hr) :=
    ⟨centeredCube_subset_closedCube z hr⟩
  have h0 := normalizedContinuousPositiveCoefficient_coeFn
    (Ω := centeredCube z r hr) (closedCube z r hr) (cutoffCoefficientCM M H omega N z hr)
    (cutoffCoefficientCM_pos M H omega N z hr) 1 one_pos
  filter_upwards [h0, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx hxm
  have := hx hxm
  change (cutoffPositiveCoefficient M H omega N z hr).val x = _
  unfold cutoffPositiveCoefficient
  rw [this, div_one]
  change cutoffCoefficient M H omega N x = _
  unfold cutoffCoefficient aux_lem_local_normalizations_prop16_kap
  have hA := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
  have key : ∀ u : ℝ, Real.exp (u - Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)) =
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ * Real.exp u := by
    intro u; rw [Real.exp_sub, Real.exp_log hA, div_eq_inv_mul]
  rw [Real.log_mul (Real.exp_pos _).ne' hA.ne', Real.log_exp, sub_add_eq_sub_sub]
  exact (key _).symm

/-- Local energy on `ball ∩ Ω` equals local energy on `ball`. -/
theorem aux_lem_local_normalizations_prop16_lge_inter {d : ℕ} {Ω : Opens (SpatialCoordinates d)} (a : PositiveCoefficient Ω)
    (x : SpatialCoordinates d) (rho : ℝ) (g : HilbertGradient Ω) :
    localGradientEnergy a (s := Metric.ball x rho ∩ (Ω : Set (SpatialCoordinates d)))
        (Metric.isOpen_ball.inter Ω.isOpen).measurableSet g =
      localGradientEnergy a (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet g := by
  simp only [localGradientEnergy_eq_integral]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Measure.restrict_restrict (Metric.isOpen_ball.inter Ω.isOpen).measurableSet,
    Measure.restrict_restrict Metric.isOpen_ball.measurableSet, Set.inter_assoc, Set.inter_self]

/-- A smooth, compactly-supported, nonzero-somewhere, `[0,1]`-valued function on
`centeredCube z r hr`. -/
theorem aux_lem_local_normalizations_prop16_bump {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ f : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
      (∃ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), f x ≠ 0) ∧
      (∀ x, 0 ≤ f x ∧ f x ≤ 1) := by
  have hcube : (centeredCube z r hr : Set (SpatialCoordinates d)) = Metric.ball z (r / 2) := rfl
  set bmp : ContDiffBump z := ⟨r / 8, r / 4, by linarith, by linarith⟩ with hbmp
  refine ⟨bmp, bmp.contDiff, bmp.hasCompactSupport, ?_, ⟨z, ?_, ?_⟩,
    fun x => ⟨bmp.nonneg' x, bmp.le_one⟩⟩
  · rw [bmp.tsupport_eq, hcube]
    apply Metric.closedBall_subset_ball
    dsimp [bmp]
    linarith
  · rw [hcube]
    exact Metric.mem_ball_self (by linarith)
  · have := bmp.one_of_mem_closedBall (Metric.mem_closedBall_self (by dsimp [bmp]; linarith))
    rw [this]
    norm_num

/-- The `prop_16` half of the `hmom`/`hband` recipe: for a GENERAL cell `(z,r,hr)` and a GENERAL
admissible boundary datum `phi`, extract the uniform-in-`N` conditional-expectation band bound
`finite_response_ramp` needs for `RD` at `p := 2`. -/
theorem aux_lem_local_normalizations_test_prop16_rd_band
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (W : SmallPerturbationInput d) (Sf : SobolevFoundationalInput d hd)
    (D : @lane4_deterministic_good_scale_input d ⟨by omega⟩) :
    ∃ (delta0 : ℝ), 0 < delta0 ∧
    ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
    ∀ (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
      (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ ∞ phi)
      (hnonconst : ∃ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∃ y ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), phi x ≠ phi y)
      (b : weakSobolevGraph (centeredCube z r hr))
      (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi),
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (Rm : in_responses d M) (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ))
      (hH : InfraredCharacterization M H),
      M.delta ≤ min 1 delta0 →
      let Pm : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
      let a : ℕ → BilateralField d → PositiveCoefficient (centeredCube z r hr) :=
        fun N omega => cutoffPositiveCoefficient M H omega N z hr
      let RD : ℕ → BilateralField d → ℝ :=
        fun N omega => dirichletResponse (killedResponseSpace hP) (a N omega) b
      ∃ Cband : ℝ, 0 < Cband ∧
        ∀ (h N : ℕ),
          eLpNorm (fun omega => RD N omega -
              (Pm[RD N | bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]) omega)
            (ENNReal.ofReal 2) Pm ≤
          ENNReal.ofReal (Cband * M.delta * (3 : ℝ) ^ (-(aux_lem_local_normalizations_prop16_aD d) * (h : ℝ))) := by
  have ht0 : (d : ℝ) - 1 < (d : ℝ) - 1 / 2 := by linarith
  have ht1 : (d : ℝ) - 1 / 2 < (d : ℝ) := by linarith
  obtain ⟨aexpOf, qOf, ordersOf, thresholdOf, _, _, haexppos, haexpeq, hmain0⟩ :=
    rem_bank d hd Jc Pc Xc W Sf D ((d : ℝ) - 1 / 2) ht0 ht1
  obtain ⟨hpq, hdeltapos, h3p, hqmem, h12p, h4q, hall⟩ := hmain0 2 (by norm_num)
  refine ⟨thresholdOf d ((d:ℝ)-1/2) (ordersOf 2 d ((d:ℝ)-1/2)), hdeltapos, ?_⟩
  intro z r hr hrle hP phi hphi hnonconst b hb M Rm Sreg It H hH hdelta
  intro Pm a RD
  obtain ⟨hdir, -, -⟩ := hall M Rm Sreg It H hH hdelta
  obtain ⟨f, hf, hfc, hfsupp, hf0, hfbdd⟩ := aux_lem_local_normalizations_prop16_bump z r hr
  have hfmem : MemLp f 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    MemLp.of_bound hf.continuous.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hfbdd x).1]; exact (hfbdd x).2)
  have hfL2 : ((hfmem.toLp f : DomainL2 (centeredCube z r hr)) : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f := hfmem.coeFn_toLp
  obtain ⟨KD, KK, B, hB0, hae, hmemLp, hnormsum⟩ :=
    hdir z r hr hrle hP phi hphi b hb f hf hfc hfsupp (hfmem.toLp f) hfL2
  obtain ⟨C, hC, hbmain⟩ := Paper.prop_16.1 d hd z r hr hP phi hphi hnonconst b hb f hf hfc hfsupp
    hf0 (hfmem.toLp f) hfL2 ((d : ℝ) - 1 / 2) 2 B ht0 ht1 (by norm_num) hB0 true
  refine ⟨C, hC, ?_⟩
  intro h N
  have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hK : (∀ n, AEStronglyMeasurable (KD n) Pm) ∧ (∀ᵐ omega ∂Pm, ∀ n, 0 ≤ KD n omega) :=
    ⟨fun n => (hmemLp n).1.1, hae.mono (fun omega hom n => (hom n).1)⟩
  have hMor : ∀ᵐ omega ∂Pm, ∀ n, ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
        localGradientEnergy (a n omega) (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet
          (sobolevGradient (dirichletMinimizer (killedResponseSpace hP) (a n omega) b).val) ≤
          KD n omega * rho ^ ((d : ℝ) - 1 / 2) := by
    filter_upwards [hae] with omega hom n x hx rho h0 h1
    have := (hom n).2.2.1 x hx rho h0 h1
    rwa [aux_lem_local_normalizations_prop16_lge_inter] at this
  have hmoms : ∀ n, MemLp (KD n) (ENNReal.ofReal (3 * 2)) Pm ∧
      MemLp (RD n) (ENNReal.ofReal (3 * 2)) Pm ∧
      eLpNorm (KD n) (ENNReal.ofReal (3 * 2)) Pm ≤ ENNReal.ofReal B ∧
      eLpNorm (RD n) (ENNReal.ofReal (3 * 2)) Pm ≤ ENNReal.ofReal B := fun n =>
    ⟨(hmemLp n).1, (hmemLp n).2.2.1, (aux_lem_local_normalizations_prop16_le_of_add_six (hnormsum n)).1,
      (aux_lem_local_normalizations_prop16_le_of_add_six (hnormsum n)).2.2.1⟩
  refine (hbmain M.delta hδpos (hdelta.trans (min_le_left _ _)) M.P M.G1 M.G2 H hH.1 hH.2
    (aux_lem_local_normalizations_prop16_kap M) (aux_lem_local_normalizations_prop16_kap_pos M) (fun n omega => cutoffPositiveCoefficient M H omega n z hr)
    (fun n omega => aux_lem_local_normalizations_prop16_cutoff_ae_exp M H n omega z r hr) KD ?_ ?_ ?_).1 h N
  · exact hK
  · exact hMor
  · exact hmoms

/-! ===== NEW WORK (round 5): general-cell proxy potential + `hsplit` ===== -/

section AuxLnormProxy

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- Generic per-fiber `MeasurableSpace` instance on the TWO specific subtypes `bandSet H` and
`{j // j not in bandSet H}` used below (NOT a fully generic `forall p : Int to Prop` instance,
which caused a diamond with the regroup section's own ad-hoc subtype resolutions, using DIFFERENT
subtypes `{j // aux_lem_local_normalizations_lnorm_regroup_p j}` and `{i // aux_lem_local_normalizations_lnorm_regroup_q i.1}`; these two are
disjoint from those, so there is no overlap). Needed for the Pi `MeasurableSpace` on a band or
tail restricted tuple. Declared HERE (after the regroup section, not next to
`aux_lem_local_normalizations_lnorm_regroup_Y_measurableSpace` itself) so it cannot interfere with the ALREADY-elaborated
proofs above. -/
instance aux_lem_local_normalizations_lnorm_proxy_subtype_measurableSpace (p : ℤ → Prop) :
    ∀ j : Subtype p, MeasurableSpace (aux_lem_local_normalizations_lnorm_regroup_Y d j.1) :=
  fun j => aux_lem_local_normalizations_lnorm_regroup_Y_measurableSpace d j.1

/-- The general-cell cutoff potential built from an arbitrary continuous "infrared term"
`Hterm` in place of `H omega` (mirrors `G9_unit_compact.lean`'s `g9_contFn`, generalized from
the unit cube `(0,1)` to any `(z,r,hr)`). -/
def aux_lem_local_normalizations_lnorm_proxy_contFn (Hterm : C(SpatialCoordinates d, ℝ))
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) (omega : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    C(closedCube z r hr, ℝ) :=
  (Hterm + ∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ))).restrict (closedCube z r hr) -
    ContinuousMap.const _ (Real.log (aux_lem_local_normalizations_prop16_kap M N))

def aux_lem_local_normalizations_lnorm_proxy_pot (Hterm : C(SpatialCoordinates d, ℝ))
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) (omega : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    SubdiffusiveProcess.Lane3.Potential (centeredCube z r hr) :=
  compactPotentialLp (closedCube z r hr) (aux_lem_local_normalizations_lnorm_proxy_contFn Hterm M N omega z r hr)

theorem aux_lem_local_normalizations_lnorm_proxy_contFn_apply (Hterm M N omega z r hr)
    (x : closedCube z r hr) :
    aux_lem_local_normalizations_lnorm_proxy_contFn Hterm M N omega z r hr x =
      Hterm (x : SpatialCoordinates d) +
        (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) (x : SpatialCoordinates d)) -
        Real.log (aux_lem_local_normalizations_prop16_kap M N) := by
  have hsum : (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)))
      ((x : SpatialCoordinates d)) =
      ∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) (x : SpatialCoordinates d) := by
    have h := map_sum ContinuousMap.coeFnAddMonoidHom
      (fun j : ℕ => omega (-(j : ℤ))) (Finset.range (N + 1))
    simp only [ContinuousMap.coeFnAddMonoidHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h
    have h' := congrFun h (x : SpatialCoordinates d)
    simpa only [Finset.sum_apply] using h'
  change Hterm (x : SpatialCoordinates d) +
      (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ))) ((x : SpatialCoordinates d)) -
      Real.log (aux_lem_local_normalizations_prop16_kap M N) = _
  rw [hsum]

/-- `compactPotentialLp` at a FIXED compact root is `1`-Lipschitz for ANY enclosed domain
(generic linearity + norm bound; the atom-extraction proof does not use `Q0 = centeredCube 0 1`
anywhere, so it transfers verbatim to any `(z, r, hr)`). -/
theorem aux_lem_local_normalizations_lnorm_proxy_cp_lipschitz (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    LipschitzWith 1 (compactPotentialLp (Ω := centeredCube z r hr) (closedCube z r hr)) := by
  refine LipschitzWith.of_dist_le_mul fun f g => ?_
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  have hsub : compactPotentialLp (Ω := centeredCube z r hr) (closedCube z r hr) (f - g) =
      compactPotentialLp (closedCube z r hr) f - compactPotentialLp (closedCube z r hr) g := by
    have hfg : f - g = f + (-1 : ℝ) • g := by rw [neg_one_smul, sub_eq_add_neg]
    rw [hfg, compactPotentialLp_add, compactPotentialLp_smul, neg_one_smul, ← sub_eq_add_neg]
  rw [← hsub]
  exact compactPotentialLp_norm_le _ _

/-- **General-cell coefficient identity.** `cutoffPositiveCoefficient` is EXACTLY
`expPotentialCoefficient` of the `Hterm = H omega` proxy potential, for any `(z, r, hr)`
(generalizes `G9_unit_compact.lean`'s `g9_pot_eq_coefficient` from `z = 0, r = 1`). -/
theorem aux_lem_local_normalizations_lnorm_proxy_pot_eq_coefficient
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ) (omega : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    cutoffPositiveCoefficient M H omega N z hr =
      expPotentialCoefficient (aux_lem_local_normalizations_lnorm_proxy_pot (H omega) M N omega z r hr) := by
  unfold cutoffPositiveCoefficient normalizedContinuousPositiveCoefficient aux_lem_local_normalizations_lnorm_proxy_pot
  rw [compactPotentialToLp_apply]
  congr 2
  apply ContinuousMap.ext
  intro x
  rw [aux_lem_local_normalizations_lnorm_proxy_contFn_apply]
  show Real.log ((cutoffCoefficientCM M H omega N z hr) x) - Real.log 1 = _
  have hcm : (cutoffCoefficientCM M H omega N z hr) x =
      cutoffCoefficient M H omega N (x : SpatialCoordinates d) := rfl
  rw [hcm, Real.log_one, sub_zero]
  unfold cutoffCoefficient cutoffPotential aux_lem_local_normalizations_prop16_kap
  have hA : (0 : ℝ) < SubdiffusiveProcess.CoarseGrainingVocab.ahom M N := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
  have hcast : ∀ j : ℕ, omega (-(Int.ofNat j)) = omega (-(j : ℤ)) := fun j => by norm_num
  have hlog1 : ∀ c u : ℝ, 0 < c → Real.log (c⁻¹ * Real.exp u) = u - Real.log c := by
    intro c u hc
    rw [Real.log_mul (inv_ne_zero hc.ne') (Real.exp_pos _).ne', Real.log_inv, Real.log_exp]
    ring
  have hlog2 : ∀ c v : ℝ, 0 < c → Real.log (Real.exp v * c) = v + Real.log c := by
    intro c v hc
    rw [Real.log_mul (Real.exp_pos _).ne' hc.ne', Real.log_exp]
  simp only [hcast]
  rw [hlog1 _ _ hA, hlog2 _ _ hA]
  ring

/-! #### The NATIVE (regrouped-`y`-coordinate) potential, and its exact identity with
`aux_lem_local_normalizations_lnorm_proxy_pot` at `y = aux_lem_local_normalizations_lnorm_regroup omega`. -/

/-- The `m`-th positive (fine-layer) coordinate of a regrouped point `y`, at the LITERAL
constructor form `Int.ofNat (m + 1)` so that `aux_lem_local_normalizations_lnorm_regroup_Y`'s pattern match fires by
ordinary iota-reduction (unlike `y ((m : ℤ) + 1)`, whose index needs an extra `Int.add`
unfolding that plain elaboration does not perform, even though it IS defeq). -/
def aux_lem_local_normalizations_lnorm_proxy_fineCoord (y : (j : ℤ) → aux_lem_local_normalizations_lnorm_regroup_Y d j) (m : ℕ) :
    C(SpatialCoordinates d, ℝ) :=
  y (Int.ofNat (m + 1))

theorem aux_lem_local_normalizations_lnorm_proxy_fineCoord_at_regroup (omega : BilateralField d) (m : ℕ) :
    aux_lem_local_normalizations_lnorm_proxy_fineCoord (aux_lem_local_normalizations_lnorm_regroup omega) m = omega (-((m : ℤ) + 1)) := by
  show aux_lem_local_normalizations_lnorm_regroup omega ((m : ℤ) + 1) = omega (-((m : ℤ) + 1))
  rw [aux_lem_local_normalizations_lnorm_regroup_apply_succ]
  congr 1

/-- The general-cell cutoff potential built DIRECTLY from a regrouped point `y`'s own
coordinates: `(y 0).1` supplies the root layer `omega 0`, and `aux_lem_local_normalizations_lnorm_proxy_fineCoord y m` for
`m < N` supplies the fine layer `omega (-(m+1))` (both via `aux_lem_local_normalizations_lnorm_regroup_apply_zero`/
`_apply_succ`, EXACTLY, not a.e.). Total (defined for every `y`, not just images of
`aux_lem_local_normalizations_lnorm_regroup`), matching `hsplit`'s own `∀ ω` (no a.e. qualifier). -/
def aux_lem_local_normalizations_lnorm_proxy_contFn' (Hterm : C(SpatialCoordinates d, ℝ))
    (N : ℕ) (y : (j : ℤ) → aux_lem_local_normalizations_lnorm_regroup_Y d j)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    C(closedCube z r hr, ℝ) :=
  (Hterm + (y 0).1 +
      ∑ m ∈ Finset.range N, aux_lem_local_normalizations_lnorm_proxy_fineCoord y m).restrict
      (closedCube z r hr) -
    ContinuousMap.const _ (Real.log (aux_lem_local_normalizations_prop16_kap M N))

theorem aux_lem_local_normalizations_lnorm_proxy_contFn'_apply (Hterm N y z r hr M)
    (x : closedCube z r hr) :
    aux_lem_local_normalizations_lnorm_proxy_contFn' Hterm N y z r hr M x =
      Hterm (x : SpatialCoordinates d) + (y 0).1 (x : SpatialCoordinates d) +
        (∑ m ∈ Finset.range N, aux_lem_local_normalizations_lnorm_proxy_fineCoord y m (x : SpatialCoordinates d)) -
        Real.log (aux_lem_local_normalizations_prop16_kap M N) := by
  have hsum : (Hterm + (y 0).1 + ∑ m ∈ Finset.range N, aux_lem_local_normalizations_lnorm_proxy_fineCoord y m)
      ((x : SpatialCoordinates d)) =
      Hterm (x : SpatialCoordinates d) + (y 0).1 (x : SpatialCoordinates d) +
        (∑ m ∈ Finset.range N, aux_lem_local_normalizations_lnorm_proxy_fineCoord y m (x : SpatialCoordinates d)) := by
    have h := map_sum ContinuousMap.coeFnAddMonoidHom
      (fun m : ℕ => aux_lem_local_normalizations_lnorm_proxy_fineCoord y m) (Finset.range N)
    simp only [ContinuousMap.coeFnAddMonoidHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h
    have h' := congrFun h (x : SpatialCoordinates d)
    simp only [ContinuousMap.add_apply, Finset.sum_apply] at h' ⊢
    rw [h']
  change (Hterm + (y 0).1 + ∑ m ∈ Finset.range N, aux_lem_local_normalizations_lnorm_proxy_fineCoord y m)
      ((x : SpatialCoordinates d)) - Real.log (aux_lem_local_normalizations_prop16_kap M N) = _
  rw [hsum]

/-- **Exact identity**: the native potential at `y = aux_lem_local_normalizations_lnorm_regroup omega` literally equals
`aux_lem_local_normalizations_lnorm_proxy_contFn` at `omega` (no a.e. qualifier — every step is `aux_lem_local_normalizations_lnorm_regroup_apply_zero`
/`_apply_succ`, both EXACT). -/
theorem aux_lem_local_normalizations_lnorm_proxy_contFn'_at_regroup (Hterm : C(SpatialCoordinates d, ℝ))
    (N : ℕ) (omega : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    aux_lem_local_normalizations_lnorm_proxy_contFn' Hterm N (aux_lem_local_normalizations_lnorm_regroup omega) z r hr M =
      aux_lem_local_normalizations_lnorm_proxy_contFn Hterm M N omega z r hr := by
  apply ContinuousMap.ext
  intro x
  rw [aux_lem_local_normalizations_lnorm_proxy_contFn_apply, aux_lem_local_normalizations_lnorm_proxy_contFn'_apply]
  have h0 : (aux_lem_local_normalizations_lnorm_regroup omega 0).1 = omega 0 := by
    rw [aux_lem_local_normalizations_lnorm_regroup_apply_zero]
  have hreindex : (∑ m ∈ Finset.range N,
      aux_lem_local_normalizations_lnorm_proxy_fineCoord (aux_lem_local_normalizations_lnorm_regroup omega) m (x : SpatialCoordinates d)) =
      ∑ m ∈ Finset.range N, omega (-((m : ℤ) + 1)) (x : SpatialCoordinates d) :=
    Finset.sum_congr rfl (fun m _ => by rw [aux_lem_local_normalizations_lnorm_proxy_fineCoord_at_regroup])
  rw [h0, hreindex]
  have hsplit0 : (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) (x : SpatialCoordinates d)) =
      (∑ m ∈ Finset.range N, omega (-((m : ℤ) + 1)) (x : SpatialCoordinates d)) +
        omega (-(0 : ℤ)) (x : SpatialCoordinates d) := by
    rw [Finset.sum_range_succ']
    push_cast
    ring_nf
  rw [hsplit0]
  simp only [neg_zero]
  ring

/-! #### The band/tail split of the fine-layer coordinates, and `V`/`tail`/`pot_split`. -/

theorem aux_lem_local_normalizations_lnorm_proxy_bandSet_zero_mem (H : ℕ) : (0 : ℤ) ∈ bandSet H := by
  simp only [bandSet, Set.mem_Icc]; omega

open Classical in
/-- The `m`-th fine-layer coordinate of a BAND-restricted sample (zero when `m+1` is outside the
band); mirrors `aux_lem_prefix_limit_atom_extraction_bandCoord`, indexed at the LITERAL
`Int.ofNat (m+1)` form so the type reduces to `C(...)` directly. -/
def aux_lem_local_normalizations_lnorm_proxy_bandCoord (H : ℕ)
    (b : (j : bandSet H) → aux_lem_local_normalizations_lnorm_regroup_Y d j.1) (m : ℕ) : C(SpatialCoordinates d, ℝ) :=
  if h : (Int.ofNat (m + 1) : ℤ) ∈ bandSet H then
    (b ⟨Int.ofNat (m + 1), h⟩ : C(SpatialCoordinates d, ℝ))
  else 0

open Classical in
/-- The `m`-th fine-layer coordinate of a TAIL-restricted sample (zero when `m+1` is inside the
band). -/
def aux_lem_local_normalizations_lnorm_proxy_tailCoord (H : ℕ)
    (t : (j : {j : ℤ // j ∉ bandSet H}) → aux_lem_local_normalizations_lnorm_regroup_Y d j.1) (m : ℕ) :
    C(SpatialCoordinates d, ℝ) :=
  if h : (Int.ofNat (m + 1) : ℤ) ∉ bandSet H then
    (t ⟨Int.ofNat (m + 1), h⟩ : C(SpatialCoordinates d, ℝ))
  else 0

theorem aux_lem_local_normalizations_lnorm_proxy_bandCoord_apply (H : ℕ) (y : (j : ℤ) → aux_lem_local_normalizations_lnorm_regroup_Y d j)
    (m : ℕ) (hm : m < H) :
    aux_lem_local_normalizations_lnorm_proxy_bandCoord H (fun j => y j.1) m = aux_lem_local_normalizations_lnorm_proxy_fineCoord y m := by
  have h : (Int.ofNat (m + 1) : ℤ) ∈ bandSet H := by
    simp only [bandSet, Set.mem_Icc, Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]
    omega
  rw [aux_lem_local_normalizations_lnorm_proxy_bandCoord, dif_pos h]
  rfl

theorem aux_lem_local_normalizations_lnorm_proxy_tailCoord_apply (H : ℕ) (y : (j : ℤ) → aux_lem_local_normalizations_lnorm_regroup_Y d j)
    (m : ℕ) (hm : H ≤ m) :
    aux_lem_local_normalizations_lnorm_proxy_tailCoord H (fun j => y j.1) m = aux_lem_local_normalizations_lnorm_proxy_fineCoord y m := by
  have h : (Int.ofNat (m + 1) : ℤ) ∉ bandSet H := by
    simp only [bandSet, Set.mem_Icc, Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]
    omega
  rw [aux_lem_local_normalizations_lnorm_proxy_tailCoord, dif_pos h]
  rfl

/-- `bandCoord`/`tailCoord` are MEASURABLE (the local `MeasurableSpace` instances above make the
domain Pi-types sensible; no topology is registered on the mixed-type `aux_lem_local_normalizations_lnorm_regroup_Y`, so
continuity is never claimed for these — only for the FINAL real-valued composite, via the
`compactPotentialLp_add` rewrite below). -/
theorem aux_lem_local_normalizations_lnorm_proxy_bandCoord_measurable (H m : ℕ) :
    Measurable (fun b : (j : bandSet H) → aux_lem_local_normalizations_lnorm_regroup_Y d j.1 =>
      aux_lem_local_normalizations_lnorm_proxy_bandCoord H b m) := by
  unfold aux_lem_local_normalizations_lnorm_proxy_bandCoord
  split_ifs with h
  · exact measurable_pi_apply _
  · exact measurable_const

theorem aux_lem_local_normalizations_lnorm_proxy_tailCoord_measurable (H m : ℕ) :
    Measurable (fun t : (j : {j : ℤ // j ∉ bandSet H}) → aux_lem_local_normalizations_lnorm_regroup_Y d j.1 =>
      aux_lem_local_normalizations_lnorm_proxy_tailCoord H t m) := by
  unfold aux_lem_local_normalizations_lnorm_proxy_tailCoord
  split_ifs with h
  · exact measurable_const
  · exact measurable_pi_apply (⟨Int.ofNat (m + 1), h⟩ : {j : ℤ // j ∉ bandSet H})

/-- The band potential (root + total infrared proxy from the whole coarse block, packaged into
band coordinate `0` by `aux_lem_local_normalizations_lnorm_regroup`, + fine layers `-1,…,-H`), restricted to the closed
cube `K = closedCube z r hr` so it matches `compactPotentialLp K`'s own input type directly
(mirrors `aux_lem_prefix_limit_atom_extraction_V`'s choice `X := C(K,ℝ)`). Only MEASURABLE (the
infrared-proxy term `aux_lem_local_normalizations_lnorm_htilde` is not continuous), matching `hsplit`'s own `Measurable V`
requirement (not `Continuous V`). -/
def aux_lem_local_normalizations_lnorm_proxy_V (H : ℕ) (b : (j : bandSet H) → aux_lem_local_normalizations_lnorm_regroup_Y d j.1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) : C(closedCube z r hr, ℝ) :=
  (aux_lem_local_normalizations_lnorm_htilde d (b ⟨0, aux_lem_local_normalizations_lnorm_proxy_bandSet_zero_mem H⟩).2 +
    (b ⟨0, aux_lem_local_normalizations_lnorm_proxy_bandSet_zero_mem H⟩).1 +
    ∑ m ∈ Finset.range H, aux_lem_local_normalizations_lnorm_proxy_bandCoord H b m).restrict (closedCube z r hr)

theorem aux_lem_local_normalizations_lnorm_proxy_V_measurable (H : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    [MeasurableSpace C(closedCube z r hr, ℝ)] [BorelSpace C(closedCube z r hr, ℝ)] :
    Measurable (fun b : (j : bandSet H) → aux_lem_local_normalizations_lnorm_regroup_Y d j.1 =>
      aux_lem_local_normalizations_lnorm_proxy_V H b z r hr) := by
  unfold aux_lem_local_normalizations_lnorm_proxy_V
  refine (ContinuousMap.continuous_restrict _).measurable.comp ?_
  refine Measurable.add (Measurable.add ?_ ?_) ?_
  · exact (aux_lem_local_normalizations_lnorm_htilde_measurable d).comp
      (measurable_snd.comp
        (measurable_pi_apply (⟨0, aux_lem_local_normalizations_lnorm_proxy_bandSet_zero_mem H⟩ : bandSet H)))
  · exact measurable_fst.comp
      (measurable_pi_apply (⟨0, aux_lem_local_normalizations_lnorm_proxy_bandSet_zero_mem H⟩ : bandSet H))
  · exact Finset.measurable_sum _ fun m _ => aux_lem_local_normalizations_lnorm_proxy_bandCoord_measurable H m

/-- The tail SUM alone (before restriction/normalization), as a plain `C(SpatialCoordinates d,ℝ)`-
valued function of the tail-restricted tuple — MEASURABLE (the ambient section-level
`[MeasurableSpace C(SpatialCoordinates d,ℝ)]` instance suffices; no instance on `Potential Q`
or on the mixed `aux_lem_local_normalizations_lnorm_regroup_Y` domain is ever needed). -/
def aux_lem_local_normalizations_lnorm_proxy_tailSum (H N : ℕ)
    (t : (j : {j : ℤ // j ∉ bandSet H}) → aux_lem_local_normalizations_lnorm_regroup_Y d j.1) :
    C(SpatialCoordinates d, ℝ) :=
  ∑ m ∈ Finset.Ico H N, aux_lem_local_normalizations_lnorm_proxy_tailCoord H t m

theorem aux_lem_local_normalizations_lnorm_proxy_tailSum_measurable (H N : ℕ) :
    Measurable (aux_lem_local_normalizations_lnorm_proxy_tailSum (d := d) H N) :=
  Finset.measurable_sum _ fun m _ => aux_lem_local_normalizations_lnorm_proxy_tailCoord_measurable H m

/-- The fine tail potential at cutoff `N` (layers `-(H+1),…,-N`), including the deterministic
normalization. -/
def aux_lem_local_normalizations_lnorm_proxy_tail (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H N : ℕ)
    (t : (j : {j : ℤ // j ∉ bandSet H}) → aux_lem_local_normalizations_lnorm_regroup_Y d j.1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    SubdiffusiveProcess.Lane3.Potential (centeredCube z r hr) :=
  compactPotentialLp (closedCube z r hr)
    ((aux_lem_local_normalizations_lnorm_proxy_tailSum H N t).restrict (closedCube z r hr) -
      ContinuousMap.const _ (Real.log (aux_lem_local_normalizations_prop16_kap M N)))

/-- The NATIVE (regrouped-`y`-coordinate) potential at cutoff `N`, with the infrared term
computed FROM `y` ITSELF (via `aux_lem_local_normalizations_lnorm_htilde` applied to coordinate `0`'s coarse-block
component) rather than from an external `H`. This is `hsplit`'s `Rf` datum: total (defined for
every `y`), so `hsplit`'s `∀ ω` (no a.e. qualifier) pointwise identity can hold EXACTLY. -/
def aux_lem_local_normalizations_lnorm_proxy_pot' (N : ℕ) (y : (j : ℤ) → aux_lem_local_normalizations_lnorm_regroup_Y d j)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    SubdiffusiveProcess.Lane3.Potential (centeredCube z r hr) :=
  compactPotentialLp (closedCube z r hr)
    (aux_lem_local_normalizations_lnorm_proxy_contFn' (aux_lem_local_normalizations_lnorm_htilde d (y 0).2) N y z r hr M)

/-- **The `hsplit` pointwise identity, at the level of continuous functions (before
`compactPotentialLp`).** Splits the native potential's defining continuous function at depth `H`
into its band part (`aux_lem_local_normalizations_lnorm_proxy_V`, using `aux_lem_local_normalizations_lnorm_proxy_bandCoord_apply`) and tail part
(`aux_lem_local_normalizations_lnorm_proxy_tailSum`, using `aux_lem_local_normalizations_lnorm_proxy_tailCoord_apply`), mirroring
`aux_lem_prefix_limit_atom_extraction_pot_split` exactly, generalized from the fixed unit cube to
`(z, r, hr)` and from a bare fine-layer sum to the `aux_lem_local_normalizations_lnorm_htilde`-carrying `contFn'`. -/
theorem aux_lem_local_normalizations_lnorm_proxy_contFn'_split (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H N : ℕ)
    (hHN : H ≤ N) (y : (j : ℤ) → aux_lem_local_normalizations_lnorm_regroup_Y d j)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    aux_lem_local_normalizations_lnorm_proxy_contFn' (aux_lem_local_normalizations_lnorm_htilde d (y 0).2) N y z r hr M =
      aux_lem_local_normalizations_lnorm_proxy_V H (fun j => y j.1) z r hr +
        ((aux_lem_local_normalizations_lnorm_proxy_tailSum H N (fun j => y j.1)).restrict (closedCube z r hr) -
          ContinuousMap.const _ (Real.log (aux_lem_local_normalizations_prop16_kap M N))) := by
  have hbandsum : (∑ m ∈ Finset.range H, aux_lem_local_normalizations_lnorm_proxy_bandCoord H (fun j => y j.1) m) =
      (∑ m ∈ Finset.range H, aux_lem_local_normalizations_lnorm_proxy_fineCoord y m) :=
    Finset.sum_congr rfl
      (fun m hm => aux_lem_local_normalizations_lnorm_proxy_bandCoord_apply H y m (Finset.mem_range.mp hm))
  have htailsum : (∑ m ∈ Finset.Ico H N, aux_lem_local_normalizations_lnorm_proxy_tailCoord H (fun j => y j.1) m) =
      (∑ m ∈ Finset.Ico H N, aux_lem_local_normalizations_lnorm_proxy_fineCoord y m) :=
    Finset.sum_congr rfl
      (fun m hm => aux_lem_local_normalizations_lnorm_proxy_tailCoord_apply H y m (Finset.mem_Ico.mp hm).1)
  have hfullsplit : (∑ m ∈ Finset.range N, aux_lem_local_normalizations_lnorm_proxy_fineCoord y m) =
      (∑ m ∈ Finset.range H, aux_lem_local_normalizations_lnorm_proxy_fineCoord y m) +
        ∑ m ∈ Finset.Ico H N, aux_lem_local_normalizations_lnorm_proxy_fineCoord y m := by
    simp only [Finset.range_eq_Ico]
    rw [Finset.sum_Ico_consecutive _ (Nat.zero_le H) hHN]
  have hVzero : (fun j : bandSet H => y j.1) ⟨(0 : ℤ), aux_lem_local_normalizations_lnorm_proxy_bandSet_zero_mem H⟩ =
      y 0 := rfl
  have hV0 : (aux_lem_local_normalizations_lnorm_htilde d ((fun j : bandSet H => y j.1)
      ⟨0, aux_lem_local_normalizations_lnorm_proxy_bandSet_zero_mem H⟩).2 : C(SpatialCoordinates d, ℝ)) =
      aux_lem_local_normalizations_lnorm_htilde d (y 0).2 := by rw [hVzero]
  have hV1 : ((fun j : bandSet H => y j.1) ⟨0, aux_lem_local_normalizations_lnorm_proxy_bandSet_zero_mem H⟩).1 =
      (y 0).1 := by rw [hVzero]
  show (aux_lem_local_normalizations_lnorm_htilde d (y 0).2 + (y 0).1 +
      ∑ m ∈ Finset.range N, aux_lem_local_normalizations_lnorm_proxy_fineCoord y m).restrict (closedCube z r hr) -
      ContinuousMap.const _ (Real.log (aux_lem_local_normalizations_prop16_kap M N)) = _
  unfold aux_lem_local_normalizations_lnorm_proxy_V aux_lem_local_normalizations_lnorm_proxy_tailSum
  rw [hV0, hV1, hbandsum, htailsum, hfullsplit]
  have hradd : ∀ f g : C(SpatialCoordinates d, ℝ),
      (f + g).restrict (closedCube z r hr) =
        f.restrict (closedCube z r hr) + g.restrict (closedCube z r hr) := by
    intro f g; ext x; rfl
  simp only [hradd]
  abel

/-- **The `hsplit` pointwise identity, at the level of `Potential`.** -/
theorem aux_lem_local_normalizations_lnorm_proxy_pot'_split (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H N : ℕ)
    (hHN : H ≤ N) (y : (j : ℤ) → aux_lem_local_normalizations_lnorm_regroup_Y d j)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    aux_lem_local_normalizations_lnorm_proxy_pot' N y z r hr M =
      compactPotentialLp (closedCube z r hr) (aux_lem_local_normalizations_lnorm_proxy_V H (fun j => y j.1) z r hr) +
        aux_lem_local_normalizations_lnorm_proxy_tail M H N (fun j => y j.1) z r hr := by
  unfold aux_lem_local_normalizations_lnorm_proxy_pot' aux_lem_local_normalizations_lnorm_proxy_tail
  rw [aux_lem_local_normalizations_lnorm_proxy_contFn'_split M H N hHN y z r hr, compactPotentialLp_add]

/-! #### The `hsplit` existential assembly for `prop_response_compact`. -/

/-- **`hsplit`'s `Rf` datum.** The native (regrouped-`y`-coordinate) Dirichlet response at the
GENERAL cell `(z, r, hr)` and GENERAL admissible datum `b`, using the `aux_lem_local_normalizations_lnorm_htilde` proxy for
the infrared field (computed from `y` itself, so this is a TOTAL function, matching `hsplit`'s
`∀ ω` with no a.e. qualifier). -/
def aux_lem_local_normalizations_lnorm_proxy_Rf
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (b : weakSobolevGraph (centeredCube z r hr))
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (y : (j : ℤ) → aux_lem_local_normalizations_lnorm_regroup_Y d j) : ℝ :=
  (aux_lem_local_normalizations_lnaff_response (killedResponseSpace hP) b).eval (aux_lem_local_normalizations_lnorm_proxy_pot' N y z r hr M)



theorem aux_lem_local_normalizations_lnorm_proxy_response_eval_continuous {Ω : Opens (SpatialCoordinates d)}
    (R : SubdiffusiveProcess.Lane3.Response Ω) :
    Continuous R.eval := by
  have he := equicontinuous_of_exp_comparison
    (f := fun _ : Unit => R.eval) (C := 1) (by norm_num)
    (fun _ g => R.eval_nonneg g)
    (fun _ g h => by rw [one_mul, dist_eq_norm]; exact R.exp_comparison g h)
    (fun g => ⟨R.eval g, fun _ => le_rfl⟩)
  exact he.continuous ()

/-- The tail piece as a plain `C(closedCube z r hr, ℝ)`-valued function (before
`compactPotentialLp`), matching `X`'s own type so `compactPotentialLp_add` can recombine it with
`psi z.1`. MEASURABLE (the ambient `[MeasurableSpace C(closedCube z r hr,ℝ)]` ties this to `X`'s
own instance, supplied once at the `hsplit` call site). -/
def aux_lem_local_normalizations_lnorm_proxy_tailContFn (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H N : ℕ)
    (t : (j : {j : ℤ // j ∉ bandSet H}) → aux_lem_local_normalizations_lnorm_regroup_Y d j.1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) : C(closedCube z r hr, ℝ) :=
  (aux_lem_local_normalizations_lnorm_proxy_tailSum H N t).restrict (closedCube z r hr) -
    ContinuousMap.const _ (Real.log (aux_lem_local_normalizations_prop16_kap M N))

theorem aux_lem_local_normalizations_lnorm_proxy_tailContFn_measurable (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    [MeasurableSpace C(closedCube z r hr, ℝ)] [BorelSpace C(closedCube z r hr, ℝ)] :
    Measurable (fun t : (j : {j : ℤ // j ∉ bandSet H}) → aux_lem_local_normalizations_lnorm_regroup_Y d j.1 =>
      aux_lem_local_normalizations_lnorm_proxy_tailContFn M H N t z r hr) := by
  unfold aux_lem_local_normalizations_lnorm_proxy_tailContFn
  refine Measurable.sub ?_ measurable_const
  exact (ContinuousMap.continuous_restrict _).measurable.comp (aux_lem_local_normalizations_lnorm_proxy_tailSum_measurable H N)

theorem aux_lem_local_normalizations_lnorm_proxy_tail_eq_compactPotentialLp (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H N : ℕ) (t : (j : {j : ℤ // j ∉ bandSet H}) → aux_lem_local_normalizations_lnorm_regroup_Y d j.1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    aux_lem_local_normalizations_lnorm_proxy_tail M H N t z r hr =
      compactPotentialLp (closedCube z r hr) (aux_lem_local_normalizations_lnorm_proxy_tailContFn M H N t z r hr) := rfl



theorem aux_lem_local_normalizations_lnorm_proxy_hsplit
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (b : weakSobolevGraph (centeredCube z r hr))
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : ℕ) :
    ∃ (X : Type) (_ : MetricSpace X) (_ : TopologicalSpace.SeparableSpace X)
      (_ : MeasurableSpace X) (_ : BorelSpace X) (Q : Opens (SpatialCoordinates d))
      (R : SubdiffusiveProcess.Lane3.Response Q)
      (V : ((j : bandSet H) → aux_lem_local_normalizations_lnorm_regroup_Y d j.1) → X)
      (psi : X → SubdiffusiveProcess.Lane3.Potential Q)
      (tail : ℕ → ((j : {j : ℤ // j ∉ bandSet H}) → aux_lem_local_normalizations_lnorm_regroup_Y d j.1) →
        SubdiffusiveProcess.Lane3.Potential Q),
      Measurable V ∧
      LipschitzWith 1 psi ∧
      (∀ N : ℕ, H ≤ N →
        Measurable (fun w : X × ((j : {j : ℤ // j ∉ bandSet H}) → aux_lem_local_normalizations_lnorm_regroup_Y d j.1) =>
          R.eval (psi w.1 + tail N w.2))) ∧
      (∀ N : ℕ, H ≤ N → ∀ omg : (j : ℤ) → aux_lem_local_normalizations_lnorm_regroup_Y d j,
        aux_lem_local_normalizations_lnorm_proxy_Rf z r hr hP b M N omg =
          R.eval (psi (V (fun j => omg j.1)) + tail N (fun j => omg j.1))) := by
  letI mX : MeasurableSpace C(closedCube z r hr, ℝ) := borel _
  haveI bX : BorelSpace C(closedCube z r hr, ℝ) := ⟨rfl⟩
  refine ⟨C(closedCube z r hr, ℝ), inferInstance, inferInstance, mX, bX,
    centeredCube z r hr, aux_lem_local_normalizations_lnaff_response (killedResponseSpace hP) b,
    (fun b => aux_lem_local_normalizations_lnorm_proxy_V H b z r hr), compactPotentialLp (closedCube z r hr),
    fun N t => aux_lem_local_normalizations_lnorm_proxy_tail M H N t z r hr,
    aux_lem_local_normalizations_lnorm_proxy_V_measurable H z r hr, aux_lem_local_normalizations_lnorm_proxy_cp_lipschitz z r hr, ?_, ?_⟩
  · intro N _
    have hRfromC : Continuous (fun f : C(closedCube z r hr, ℝ) =>
        (aux_lem_local_normalizations_lnaff_response (killedResponseSpace hP) b).eval
          (compactPotentialLp (closedCube z r hr) f)) :=
      (aux_lem_local_normalizations_lnorm_proxy_response_eval_continuous (aux_lem_local_normalizations_lnaff_response (killedResponseSpace hP) b)).comp
        (aux_lem_local_normalizations_lnorm_proxy_cp_lipschitz z r hr).continuous
    have hinner : Measurable (fun w : C(closedCube z r hr, ℝ) ×
        ((j : {j : ℤ // j ∉ bandSet H}) → aux_lem_local_normalizations_lnorm_regroup_Y d j.1) =>
        w.1 + aux_lem_local_normalizations_lnorm_proxy_tailContFn M H N w.2 z r hr) :=
      Measurable.add measurable_fst
        ((aux_lem_local_normalizations_lnorm_proxy_tailContFn_measurable M H N z r hr).comp measurable_snd)
    have heq : (fun w : C(closedCube z r hr, ℝ) ×
        ((j : {j : ℤ // j ∉ bandSet H}) → aux_lem_local_normalizations_lnorm_regroup_Y d j.1) =>
        (aux_lem_local_normalizations_lnaff_response (killedResponseSpace hP) b).eval
          (compactPotentialLp (closedCube z r hr) w.1 + aux_lem_local_normalizations_lnorm_proxy_tail M H N w.2 z r hr)) =
        (fun f : C(closedCube z r hr, ℝ) => (aux_lem_local_normalizations_lnaff_response (killedResponseSpace hP) b).eval
            (compactPotentialLp (closedCube z r hr) f)) ∘
          (fun w => w.1 + aux_lem_local_normalizations_lnorm_proxy_tailContFn M H N w.2 z r hr) := by
      funext w
      show _ = (aux_lem_local_normalizations_lnaff_response (killedResponseSpace hP) b).eval
          (compactPotentialLp (closedCube z r hr) (w.1 + aux_lem_local_normalizations_lnorm_proxy_tailContFn M H N w.2 z r hr))
      rw [aux_lem_local_normalizations_lnorm_proxy_tail_eq_compactPotentialLp, ← compactPotentialLp_add]
    rw [heq]
    exact hRfromC.measurable.comp hinner
  · intro N hN omg
    unfold aux_lem_local_normalizations_lnorm_proxy_Rf
    rw [aux_lem_local_normalizations_lnorm_proxy_pot'_split M H N hN omg z r hr]

/-! #### Transport: `Rf` composed with `regroup` equals the TRUE (`H`-based) response, a.e. -/

/-- **Exact identity**: the native `Potential` at `y = aux_lem_local_normalizations_lnorm_regroup omega`, with infrared term
`Hterm`, equals `aux_lem_local_normalizations_lnorm_proxy_pot Hterm M N omega z r hr` (no a.e. qualifier). -/
theorem aux_lem_local_normalizations_lnorm_proxy_pot'_at_regroup (Hterm : C(SpatialCoordinates d, ℝ))
    (N : ℕ) (omega : BilateralField d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    compactPotentialLp (closedCube z r hr)
        (aux_lem_local_normalizations_lnorm_proxy_contFn' Hterm N (aux_lem_local_normalizations_lnorm_regroup omega) z r hr M) =
      aux_lem_local_normalizations_lnorm_proxy_pot Hterm M N omega z r hr := by
  unfold aux_lem_local_normalizations_lnorm_proxy_pot
  rw [aux_lem_local_normalizations_lnorm_proxy_contFn'_at_regroup]

/-- The general-cell Dirichlet response at the TRUE infrared field `H` (matches the two
suppliers' own local `RD`, restated as a top-level `def` for reuse). -/
def aux_lem_local_normalizations_lnorm_proxy_RD
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (b : weakSobolevGraph (centeredCube z r hr))
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ) (omega : BilateralField d) : ℝ :=
  dirichletResponse (killedResponseSpace hP) (cutoffPositiveCoefficient M H omega N z hr) b

/-- **The central transport fact.** `Rf` composed with the regroup equivalence agrees a.e. with
the TRUE (`H`-based) response `RD`: the ONLY non-exact step is
`aux_lem_local_normalizations_lnorm_htilde_eq_H_ae` (the infrared partial sums converge to `H` only a.e.); everything else
(`aux_lem_local_normalizations_lnorm_proxy_pot'_at_regroup`, `aux_lem_local_normalizations_lnorm_proxy_pot_eq_coefficient`,
`aux_lem_local_normalizations_lnaff_response_eval`) is an EXACT identity. -/
theorem aux_lem_local_normalizations_lnorm_proxy_Rf_comp_regroup_ae_eq_RD
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (b : weakSobolevGraph (centeredCube z r hr))
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (N : ℕ) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      aux_lem_local_normalizations_lnorm_proxy_Rf z r hr hP b M N (aux_lem_local_normalizations_lnorm_regroup omega) =
        aux_lem_local_normalizations_lnorm_proxy_RD z r hr hP b M H N omega := by
  filter_upwards [aux_lem_local_normalizations_lnorm_htilde_eq_H_ae d hH] with omega heq
  unfold aux_lem_local_normalizations_lnorm_proxy_Rf aux_lem_local_normalizations_lnorm_proxy_RD
  rw [aux_lem_local_normalizations_lnaff_response_eval]
  have hcoord : aux_lem_local_normalizations_lnorm_regroup omega 0 = (omega 0, fun n : ℕ => omega ((n : ℤ) + 1)) :=
    aux_lem_local_normalizations_lnorm_regroup_apply_zero d omega
  have hHterm : aux_lem_local_normalizations_lnorm_htilde d (aux_lem_local_normalizations_lnorm_regroup omega 0).2 = H omega := by
    rw [hcoord]; exact heq
  rw [show aux_lem_local_normalizations_lnorm_proxy_pot' N (aux_lem_local_normalizations_lnorm_regroup omega) z r hr M =
      compactPotentialLp (closedCube z r hr)
        (aux_lem_local_normalizations_lnorm_proxy_contFn' (aux_lem_local_normalizations_lnorm_htilde d (aux_lem_local_normalizations_lnorm_regroup omega 0).2) N
          (aux_lem_local_normalizations_lnorm_regroup omega) z r hr M) from rfl,
    hHterm, aux_lem_local_normalizations_lnorm_proxy_pot'_at_regroup, ← aux_lem_local_normalizations_lnorm_proxy_pot_eq_coefficient]

/-! #### `hmom`/`hmem`: transported from the `rem_bank` supplier via the regroup measure-preserving
equivalence and the central transport fact above. -/

theorem aux_lem_local_normalizations_lnorm_regroup_laws_eq_map (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_laws M) =
      Measure.map (aux_lem_local_normalizations_lnorm_regroup (d := d)) (chaosSampleLaw M).toMeasure :=
  (aux_lem_local_normalizations_lnorm_regroup_measurePreserving M).map_eq.symm

/-- **`hmom`/`hmem`, transported.** Any uniform `L^q` moment bound for the TRUE response `RD`
transports to the SAME bound for `Rf` under `Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_laws M)`. -/
theorem aux_lem_local_normalizations_lnorm_proxy_hmom
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (b : weakSobolevGraph (centeredCube z r hr))
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (q : ℝ≥0∞) (N : ℕ) (Cmom : ℝ) (hCmom : 0 ≤ Cmom)
    (hRDmem : MemLp (aux_lem_local_normalizations_lnorm_proxy_RD z r hr hP b M H N) q (chaosSampleLaw M).toMeasure)
    (hRDbound : eLpNorm (aux_lem_local_normalizations_lnorm_proxy_RD z r hr hP b M H N) q (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal Cmom) :
    MemLp (aux_lem_local_normalizations_lnorm_proxy_Rf z r hr hP b M N) q (Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_laws M)) ∧
      eLpNorm (aux_lem_local_normalizations_lnorm_proxy_Rf z r hr hP b M N) q
          (Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_laws M)) ≤ ENNReal.ofReal Cmom := by
  have hae := aux_lem_local_normalizations_lnorm_proxy_Rf_comp_regroup_ae_eq_RD z r hr hP b M H hH N
  have hcomp_ae : (aux_lem_local_normalizations_lnorm_proxy_Rf z r hr hP b M N ∘ aux_lem_local_normalizations_lnorm_regroup) =ᵐ[(chaosSampleLaw M).toMeasure]
      aux_lem_local_normalizations_lnorm_proxy_RD z r hr hP b M H N := hae
  have hmem_comp : MemLp (aux_lem_local_normalizations_lnorm_proxy_Rf z r hr hP b M N ∘ aux_lem_local_normalizations_lnorm_regroup) q
      (chaosSampleLaw M).toMeasure := hRDmem.ae_eq hcomp_ae.symm
  rw [aux_lem_local_normalizations_lnorm_regroup_laws_eq_map]
  have hmemRf : MemLp (aux_lem_local_normalizations_lnorm_proxy_Rf z r hr hP b M N) q
      (Measure.map (aux_lem_local_normalizations_lnorm_regroup (d := d)) (chaosSampleLaw M).toMeasure) :=
    (MeasurableEquiv.memLp_map_measure_iff (aux_lem_local_normalizations_lnorm_regroup (d := d))).mpr hmem_comp
  refine ⟨hmemRf, ?_⟩
  rw [eLpNorm_map_measure hmemRf.aestronglyMeasurable
      (aux_lem_local_normalizations_lnorm_regroup (d := d)).measurable.aemeasurable,
    eLpNorm_congr_ae hcomp_ae]
  exact hRDbound

/-! #### `hband` via condexp contraction: the sigma-algebra containment. -/

/-- Coordinate `k` (of the REGROUPED index space) is `bandSigma`-measurable whenever `|k| ≤ H`. -/
theorem aux_lem_local_normalizations_lnorm_regroup_bandSigma_apply_measurable (H : ℕ) (k : ℤ)
    (hk : k ∈ Set.Icc (-(H : ℤ)) (H : ℤ)) :
    Measurable[bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) H]
      (fun y : (k' : ℤ) → aux_lem_local_normalizations_lnorm_regroup_Y d k' => y k) := by
  have hle : (aux_lem_local_normalizations_lnorm_regroup_Y_measurableSpace d k).comap
      (fun y : (k' : ℤ) → aux_lem_local_normalizations_lnorm_regroup_Y d k' => y k) ≤
        bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) H :=
    le_iSup₂ (f := fun (k' : ℤ) (_ : k' ∈ Set.Icc (-(H : ℤ)) (H : ℤ)) =>
      (aux_lem_local_normalizations_lnorm_regroup_Y_measurableSpace d k').comap
        (fun y : (k'' : ℤ) → aux_lem_local_normalizations_lnorm_regroup_Y d k'' => y k')) k hk
  exact measurable_iff_comap_le.mpr hle

theorem aux_lem_local_normalizations_lnorm_regroup_bandSigma_le (H : ℕ) :
    bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) H ≤
      (bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) H).comap (aux_lem_local_normalizations_lnorm_regroup (d := d)) := by
  refine iSup₂_le (fun j hj => ?_)
  obtain ⟨hj1, hj2⟩ := Set.mem_Icc.mp hj
  have key : ∃ φ : ((k : ℤ) → aux_lem_local_normalizations_lnorm_regroup_Y d k) → C(SpatialCoordinates d, ℝ),
      Measurable[bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) H] φ ∧
      ∀ omega : BilateralField d, φ (aux_lem_local_normalizations_lnorm_regroup omega) = omega j := by
    rcases lt_trichotomy j 0 with hneg | hzero | hpos
    · -- j < 0 (fine layer): regrouped coordinate `m+1` holds `omega (-(m+1)) = omega j`.
      have hnn : (0 : ℤ) ≤ -j - 1 := by omega
      set m : ℕ := (-j - 1).toNat with hm
      have hmcast : ((-j - 1).toNat : ℤ) = -j - 1 := Int.toNat_of_nonneg hnn
      have hjeq : j = -((m : ℤ) + 1) := by rw [hm]; omega
      have hmem : (Int.ofNat (m + 1) : ℤ) ∈ Set.Icc (-(H : ℤ)) (H : ℤ) := by
        rw [Set.mem_Icc]
        simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]
        constructor <;> omega
      refine ⟨fun y => aux_lem_local_normalizations_lnorm_proxy_fineCoord y m, aux_lem_local_normalizations_lnorm_regroup_bandSigma_apply_measurable H
        (Int.ofNat (m + 1)) hmem, fun omega => ?_⟩
      show aux_lem_local_normalizations_lnorm_regroup omega ((m : ℤ) + 1) = omega j
      rw [aux_lem_local_normalizations_lnorm_regroup_apply_succ, hjeq]
      congr 1
    · -- j = 0 (root layer): the FIRST component of regrouped coordinate `0`.
      have h0 : (0 : ℤ) ∈ Set.Icc (-(H : ℤ)) (H : ℤ) := by rw [Set.mem_Icc]; omega
      refine ⟨fun y => (y 0).1,
        measurable_fst.comp (aux_lem_local_normalizations_lnorm_regroup_bandSigma_apply_measurable H 0 h0),
        fun omega => ?_⟩
      show (aux_lem_local_normalizations_lnorm_regroup omega 0).1 = omega j
      rw [aux_lem_local_normalizations_lnorm_regroup_apply_zero, hzero]
    · -- j > 0 (coarse layer): the SECOND component of regrouped coordinate `0`, at `j - 1`.
      have hnn : (0 : ℤ) ≤ j - 1 := by omega
      set m : ℕ := (j - 1).toNat with hm
      have hmcast : ((j - 1).toNat : ℤ) = j - 1 := Int.toNat_of_nonneg hnn
      have hjeq : j = (m : ℤ) + 1 := by rw [hm]; omega
      have h0 : (0 : ℤ) ∈ Set.Icc (-(H : ℤ)) (H : ℤ) := by rw [Set.mem_Icc]; omega
      refine ⟨fun y => (y 0).2 m,
        (measurable_pi_apply m).comp (measurable_snd.comp
          (aux_lem_local_normalizations_lnorm_regroup_bandSigma_apply_measurable H 0 h0)),
        fun omega => ?_⟩
      show (aux_lem_local_normalizations_lnorm_regroup omega 0).2 m = omega j
      rw [aux_lem_local_normalizations_lnorm_regroup_apply_zero, hjeq]
  obtain ⟨φ, hφmeas, hφeq⟩ := key
  have heq : (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)).comap
      (fun omega : BilateralField d => omega j) =
      ((inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)).comap φ).comap
        (aux_lem_local_normalizations_lnorm_regroup (d := d)) := by
    rw [MeasurableSpace.comap_comp]
    congr 1
    funext omega
    exact (hφeq omega).symm
  rw [heq]
  exact MeasurableSpace.comap_mono (measurable_iff_comap_le.mp hφmeas)

/-! #### The condExp contraction lemma: nested sigma-algebras give nested condexp errors. -/

/-- **Conditional-expectation contraction.** If `m1 ≤ m2` (both `≤` the ambient `m0`), the
`L²` error of the FINER conditional expectation `μ[f|m2]` is no larger than that of the COARSER
`μ[f|m1]`: standard Hilbert-space fact (`condExpL2` is the orthogonal projection onto
`lpMeas m 2 μ`, and `lpMeas m1 2 μ ⊆ lpMeas m2 2 μ`), proved directly via the Pythagorean identity
`‖F - a1‖² = ‖F - a2‖² + ‖a2 - a1‖²` (the cross term vanishes since `a2 - a1` is `m2`-measurable
and `F - a2` has zero `m2`-conditional expectation, `inner_condExpL2_eq_inner_fun`). -/
theorem aux_lem_local_normalizations_lnorm_condExp_contraction {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {m1 m2 : MeasurableSpace Ω} (hm1 : m1 ≤ m0) (hm2 : m2 ≤ m0)
    (hm12 : m1 ≤ m2) {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    eLpNorm (fun x => f x - (μ[f|m2]) x) 2 μ ≤ eLpNorm (fun x => f x - (μ[f|m1]) x) 2 μ := by
  set F2 : Lp ℝ 2 μ := hf.toLp f with hF2def
  set a1 : Lp ℝ 2 μ := (condExpL2 ℝ ℝ hm1 F2 : Lp ℝ 2 μ) with ha1def
  set a2 : Lp ℝ 2 μ := (condExpL2 ℝ ℝ hm2 F2 : Lp ℝ 2 μ) with ha2def
  have hF2eq : (F2 : Ω → ℝ) =ᵐ[μ] f := by rw [hF2def]; exact hf.coeFn_toLp
  have ha1eq : (a1 : Ω → ℝ) =ᵐ[μ] (μ[f|m1]) := by rw [ha1def, hF2def]; exact hf.condExpL2_ae_eq_condExp hm1
  have ha2eq : (a2 : Ω → ℝ) =ᵐ[μ] (μ[f|m2]) := by rw [ha2def, hF2def]; exact hf.condExpL2_ae_eq_condExp hm2
  have ha1meas : AEStronglyMeasurable[m1] (a1 : Ω → ℝ) μ := aestronglyMeasurable_condExpL2 hm1 F2
  have ha2meas : AEStronglyMeasurable[m2] (a2 : Ω → ℝ) μ := aestronglyMeasurable_condExpL2 hm2 F2
  have hsub_meas : AEStronglyMeasurable[m2] ((a2 - a1 : Lp ℝ 2 μ) : Ω → ℝ) μ := by
    refine AEStronglyMeasurable.congr ?_ (Lp.coeFn_sub a2 a1).symm
    exact ha2meas.sub (ha1meas.mono hm12)
  have hinner : (@inner ℝ (Lp ℝ 2 μ) _ F2 (a2 - a1)) = (@inner ℝ (Lp ℝ 2 μ) _ a2 (a2 - a1)) := by
    have h := inner_condExpL2_eq_inner_fun (𝕜 := ℝ) hm2 F2 (a2 - a1) hsub_meas
    rw [← ha2def] at h
    exact h.symm
  have horth : (@inner ℝ (Lp ℝ 2 μ) _ (F2 - a2) (a2 - a1)) = (0 : ℝ) := by
    rw [inner_sub_left, hinner, sub_self]
  have hpyth : ‖(F2 - a1 : Lp ℝ 2 μ)‖ * ‖(F2 - a1 : Lp ℝ 2 μ)‖ =
      ‖(F2 - a2 : Lp ℝ 2 μ)‖ * ‖(F2 - a2 : Lp ℝ 2 μ)‖ +
        ‖(a2 - a1 : Lp ℝ 2 μ)‖ * ‖(a2 - a1 : Lp ℝ 2 μ)‖ := by
    have hsplit : (F2 - a1 : Lp ℝ 2 μ) = (F2 - a2 : Lp ℝ 2 μ) + (a2 - a1 : Lp ℝ 2 μ) := by abel
    rw [hsplit]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  have hle : ‖(F2 - a2 : Lp ℝ 2 μ)‖ ≤ ‖(F2 - a1 : Lp ℝ 2 μ)‖ := by
    nlinarith [norm_nonneg (F2 - a2 : Lp ℝ 2 μ), norm_nonneg (F2 - a1 : Lp ℝ 2 μ),
      norm_nonneg (a2 - a1 : Lp ℝ 2 μ), sq_nonneg (‖(a2 - a1 : Lp ℝ 2 μ)‖)]
  have hae1 : (F2 - a1 : Lp ℝ 2 μ) =ᵐ[μ] (fun x => f x - (μ[f|m1]) x) := by
    filter_upwards [Lp.coeFn_sub F2 a1, hF2eq, ha1eq] with x hx hfx hcx
    rw [hx]; simp only [Pi.sub_apply]; rw [hfx, hcx]
  have hae2 : (F2 - a2 : Lp ℝ 2 μ) =ᵐ[μ] (fun x => f x - (μ[f|m2]) x) := by
    filter_upwards [Lp.coeFn_sub F2 a2, hF2eq, ha2eq] with x hx hfx hcx
    rw [hx]; simp only [Pi.sub_apply]; rw [hfx, hcx]
  have hnorm1 : eLpNorm (fun x => f x - (μ[f|m1]) x) 2 μ = ENNReal.ofReal ‖(F2 - a1 : Lp ℝ 2 μ)‖ := by
    rw [← eLpNorm_congr_ae hae1, Lp.norm_def]
    exact (ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)).symm
  have hnorm2 : eLpNorm (fun x => f x - (μ[f|m2]) x) 2 μ = ENNReal.ofReal ‖(F2 - a2 : Lp ℝ 2 μ)‖ := by
    rw [← eLpNorm_congr_ae hae2, Lp.norm_def]
    exact (ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)).symm
  rw [hnorm1, hnorm2]
  exact ENNReal.ofReal_le_ofReal hle

/-! #### `hband`, assembled. -/

/-- **`hband`, transported.** The condexp-approximation error of `Rf` at band depth `H`, under
`Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_laws M)`, is bounded by the SAME bound the TRUE response
`RD`'s error satisfies at the SAME depth under the original band filtration: conditioning on the
regrouped band reveals AT LEAST as much (`aux_lem_local_normalizations_lnorm_regroup_bandSigma_le`), so its condexp error is
no larger (`aux_lem_local_normalizations_lnorm_condExp_contraction`), and it transports across `regroup` exactly like
`hmom` did. -/
theorem aux_lem_local_normalizations_lnorm_proxy_hband
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (b : weakSobolevGraph (centeredCube z r hr))
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (Cband aD : ℝ) (Cmom6 : ℝ)
    (hRDmoment6 : ∀ N, MemLp (aux_lem_local_normalizations_lnorm_proxy_RD z r hr hP b M H N) (ENNReal.ofReal 6)
      (chaosSampleLaw M).toMeasure)
    (hRDband : ∀ (h N : ℕ),
      eLpNorm (fun omega => aux_lem_local_normalizations_lnorm_proxy_RD z r hr hP b M H N omega -
          (((chaosSampleLaw M).toMeasure)[aux_lem_local_normalizations_lnorm_proxy_RD z r hr hP b M H N |
            bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]) omega)
        (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Cband * M.delta * (3 : ℝ) ^ (-aD * (h : ℝ))))
    (Hd Nd : ℕ) :
    eLpNorm (fun y => aux_lem_local_normalizations_lnorm_proxy_Rf z r hr hP b M Nd y -
        ((Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_laws M))[aux_lem_local_normalizations_lnorm_proxy_Rf z r hr hP b M Nd |
          bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd]) y) (ENNReal.ofReal 2)
      (Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_laws M)) ≤
    ENNReal.ofReal (Cband * M.delta * (3 : ℝ) ^ (-aD * (Hd : ℝ))) := by
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
  set Pm := (chaosSampleLaw M).toMeasure with hPmdef
  set laws := Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_laws M) with hlawsdef
  set RD := aux_lem_local_normalizations_lnorm_proxy_RD z r hr hP b M H Nd with hRDdef
  set Rf := aux_lem_local_normalizations_lnorm_proxy_Rf z r hr hP b M Nd with hRfdef
  have hm1 : bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) Hd ≤
      (MeasurableSpace.pi : MeasurableSpace (BilateralField d)) := by
    refine iSup₂_le fun j _ s hs => ?_
    obtain ⟨t, ht, hst⟩ := hs
    exact hst ▸ measurable_pi_apply j ht
  have hm2Y : bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd ≤
      (MeasurableSpace.pi : MeasurableSpace ((j : ℤ) → aux_lem_local_normalizations_lnorm_regroup_Y d j)) := by
    refine iSup₂_le fun j _ s hs => ?_
    obtain ⟨t, ht, hst⟩ := hs
    exact hst ▸ measurable_pi_apply j ht
  have hm2 : (bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd).comap (aux_lem_local_normalizations_lnorm_regroup (d := d)) ≤
      (MeasurableSpace.pi : MeasurableSpace (BilateralField d)) :=
    le_trans (MeasurableSpace.comap_mono hm2Y)
      (measurable_iff_comap_le.mp (aux_lem_local_normalizations_lnorm_regroup (d := d)).measurable)
  have hm12 : bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) Hd ≤
      (bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd).comap (aux_lem_local_normalizations_lnorm_regroup (d := d)) :=
    aux_lem_local_normalizations_lnorm_regroup_bandSigma_le Hd
  have hRDmem2 : MemLp RD 2 Pm := by
    rw [hRDdef, hPmdef]; exact (hRDmoment6 Nd).mono_exponent (by norm_num)
  have hcontraction := aux_lem_local_normalizations_lnorm_condExp_contraction (Ω := BilateralField d) (μ := Pm)
    (m0 := MeasurableSpace.pi) hm1 hm2 hm12 hRDmem2
  have hbandbound := hRDband Hd Nd
  rw [h2] at hcontraction
  have hRHS : eLpNorm (fun x => RD x -
      (Pm[RD|bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) Hd]) x) (ENNReal.ofReal 2) Pm ≤
      ENNReal.ofReal (Cband * M.delta * (3 : ℝ) ^ (-aD * (Hd : ℝ))) := hbandbound
  have hmid := hcontraction.trans hRHS
  -- hmid : eLpNorm (fun x => RD x -
  --   (Pm[RD | (bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd).comap regroup]) x) (ENNReal.ofReal 2) Pm
  --   ≤ RHS bound
  have hae : Rf ∘ (aux_lem_local_normalizations_lnorm_regroup (d := d)) =ᵐ[Pm] RD := by
    rw [hRfdef, hRDdef, hPmdef]
    exact aux_lem_local_normalizations_lnorm_proxy_Rf_comp_regroup_ae_eq_RD z r hr hP b M H hH Nd
  have hRDmem6 : MemLp RD (ENNReal.ofReal 6) Pm := by rw [hRDdef, hPmdef]; exact hRDmoment6 Nd
  have hRfmem_comp : MemLp (Rf ∘ (aux_lem_local_normalizations_lnorm_regroup (d := d))) (ENNReal.ofReal 6) Pm :=
    hRDmem6.ae_eq hae.symm
  have hmp : MeasurePreserving (aux_lem_local_normalizations_lnorm_regroup (d := d)) Pm laws := by
    rw [hPmdef, hlawsdef]; exact aux_lem_local_normalizations_lnorm_regroup_measurePreserving M
  have hRfmem : MemLp Rf (ENNReal.ofReal 6) laws := by
    rw [← hmp.map_eq]
    exact (MeasurableEquiv.memLp_map_measure_iff (aux_lem_local_normalizations_lnorm_regroup (d := d))).mpr hRfmem_comp
  have htransport : Integrable Rf laws := hRfmem.integrable (by norm_num)
  have hcep := SubdiffusiveProcess.condExp_comp_measurePreserving hmp
    (bandSigma_le (Y := aux_lem_local_normalizations_lnorm_regroup_Y d) Hd) htransport
  -- hcep : Pm[Rf ∘ regroup | (bandSigma Y Hd).comap regroup] =ᵐ[Pm] (laws[Rf|bandSigma Y Hd]) ∘ regroup
  have hcongr1 : Pm[Rf ∘ (aux_lem_local_normalizations_lnorm_regroup (d := d)) |
      (bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd).comap (aux_lem_local_normalizations_lnorm_regroup (d := d))] =ᵐ[Pm]
      Pm[RD | (bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd).comap (aux_lem_local_normalizations_lnorm_regroup (d := d))] :=
    condExp_congr_ae hae
  have hkey : (laws[Rf | bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd]) ∘ (aux_lem_local_normalizations_lnorm_regroup (d := d))
      =ᵐ[Pm] Pm[RD | (bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd).comap (aux_lem_local_normalizations_lnorm_regroup (d := d))] :=
    hcep.symm.trans hcongr1
  have hgoal_ae : (fun omega => Rf (aux_lem_local_normalizations_lnorm_regroup omega) -
      (laws[Rf | bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd]) (aux_lem_local_normalizations_lnorm_regroup omega))
      =ᵐ[Pm] (fun x => RD x -
        (Pm[RD | (bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd).comap (aux_lem_local_normalizations_lnorm_regroup (d := d))]) x) := by
    filter_upwards [hae, hkey] with omega h1 h2
    simp only [Function.comp_apply] at h1 h2
    show Rf (aux_lem_local_normalizations_lnorm_regroup omega) -
      (laws[Rf | bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd]) (aux_lem_local_normalizations_lnorm_regroup omega) = _
    rw [h1, h2]
  have hcompeq : eLpNorm (fun y => Rf y -
      (laws[Rf | bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd]) y) (ENNReal.ofReal 2) laws =
      eLpNorm (fun omega => Rf (aux_lem_local_normalizations_lnorm_regroup omega) -
        (laws[Rf | bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd]) (aux_lem_local_normalizations_lnorm_regroup omega))
        (ENNReal.ofReal 2) Pm := by
    have hgmeas : AEStronglyMeasurable (fun y => Rf y -
        (laws[Rf | bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd]) y) laws :=
      hRfmem.aestronglyMeasurable.sub
        (stronglyMeasurable_condExp.aestronglyMeasurable.mono (bandSigma_le Hd))
    exact (eLpNorm_comp_measurePreserving hgmeas hmp).symm
  rw [hcompeq, eLpNorm_congr_ae hgoal_ae]
  exact hmid

/-! #### Item 5: extracting `∀ψ,∃ψ',∃L,a.e. Tendsto` from `IsCompact`, for an ARBITRARY
prescribed subsequence `phi` (mirrors `aux_lem_prefix_limit_atom_extraction_subseq`, generalized
from the hardcoded `p := 1` there to an arbitrary `p`, and specialized to a SINGLE index rather
than a countable family — sequential compactness alone suffices, no need for
`aux_countable_compact_subseq`'s countable-choice machinery). -/
theorem aux_lem_local_normalizations_lnorm_proxy_subseq {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] (X : ℕ → Ω → ℝ)
    (hmem : ∀ N, MemLp (X N) p μ)
    (hcomp : IsCompact (closure (Set.range (fun N => (hmem N).toLp (X N)))))
    (phi : ℕ → ℕ) (hphi : StrictMono phi) :
    ∃ psi : ℕ → ℕ, StrictMono psi ∧ ∃ lim : Ω → ℝ,
      ∀ᵐ omega ∂μ, Tendsto (fun i => X (phi (psi i)) omega) atTop (𝓝 (lim omega)) := by
  let toLpX : ℕ → Lp ℝ p μ := fun N => (hmem N).toLp (X N)
  have hcomp' : IsCompact (closure (Set.range toLpX)) := hcomp
  have hresult := aux_countable_compact_subseq (κ := Unit)
    (fun _ : Unit => closure (Set.range toLpX)) (fun _ : Unit => hcomp')
    (fun _ : Unit => fun n => toLpX (phi n))
    (by intro _ n; exact subset_closure (Set.mem_range_self (phi n)))
  obtain ⟨psi, hpsi, hlim⟩ := hresult
  obtain ⟨g, hg⟩ := hlim ()
  have h := aux_raw_tendsto_of_lp (p := p) (f := fun i => X (phi (psi i)))
    (fun i => hmem (phi (psi i))) hg
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp.out).ne'
  have htim : TendstoInMeasure μ (fun i om => X (phi (psi i)) om) atTop (g : Ω → ℝ) :=
    tendstoInMeasure_of_tendsto_eLpNorm hp0
      (fun i => (hmem (phi (psi i))).aestronglyMeasurable) (Lp.memLp g).aestronglyMeasurable h
  obtain ⟨ns, hns, hae⟩ := htim.exists_seq_tendsto_ae
  exact ⟨psi ∘ ns, hpsi.comp hns, (g : Ω → ℝ), hae⟩



theorem aux_lem_local_normalizations_lnorm_proxy_compact_transport
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (b : weakSobolevGraph (centeredCube z r hr))
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]
    (hRDmem : ∀ N, MemLp (aux_lem_local_normalizations_lnorm_proxy_RD z r hr hP b M H N) p (chaosSampleLaw M).toMeasure)
    (hRfmem : ∀ N, MemLp (aux_lem_local_normalizations_lnorm_proxy_Rf z r hr hP b M N) p
      (Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_laws M)))
    (hcompact : IsCompact (closure (Set.range (fun N =>
      (hRfmem N).toLp (aux_lem_local_normalizations_lnorm_proxy_Rf z r hr hP b M N))))) :
    IsCompact (closure (Set.range (fun N =>
      (hRDmem N).toLp (aux_lem_local_normalizations_lnorm_proxy_RD z r hr hP b M H N)))) := by
  have hmp := aux_lem_local_normalizations_lnorm_regroup_measurePreserving M
  set pull := Lp.compMeasurePreserving (E := ℝ) (p := p) (aux_lem_local_normalizations_lnorm_regroup (d := d)) hmp
    with pulldef
  have hiso : Isometry pull := Lp.isometry_compMeasurePreserving hmp
  have hrep : (fun N => (hRDmem N).toLp (aux_lem_local_normalizations_lnorm_proxy_RD z r hr hP b M H N)) =
      pull ∘ (fun N => (hRfmem N).toLp (aux_lem_local_normalizations_lnorm_proxy_Rf z r hr hP b M N)) := by
    funext N
    have hae : Filter.EventuallyEq (MeasureTheory.ae (chaosSampleLaw M).toMeasure)
        (aux_lem_local_normalizations_lnorm_proxy_Rf z r hr hP b M N ∘ (aux_lem_local_normalizations_lnorm_regroup (d := d)))
        (aux_lem_local_normalizations_lnorm_proxy_RD z r hr hP b M H N) :=
      aux_lem_local_normalizations_lnorm_proxy_Rf_comp_regroup_ae_eq_RD z r hr hP b M H hH N
    have hstep : pull ((hRfmem N).toLp (aux_lem_local_normalizations_lnorm_proxy_Rf z r hr hP b M N)) =
        ((hRfmem N).comp_measurePreserving hmp).toLp
          (aux_lem_local_normalizations_lnorm_proxy_Rf z r hr hP b M N ∘ (aux_lem_local_normalizations_lnorm_regroup (d := d))) := by
      rw [pulldef]; exact Lp.toLp_compMeasurePreserving (hRfmem N) hmp
    show _ = pull ((hRfmem N).toLp (aux_lem_local_normalizations_lnorm_proxy_Rf z r hr hP b M N))
    rw [hstep]
    apply Lp.ext
    exact ((((hRfmem N).comp_measurePreserving hmp).coeFn_toLp).trans
      (hae.trans (hRDmem N).coeFn_toLp.symm)).symm
  rw [hrep, Set.range_comp pull,
    hiso.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous hiso.continuous]
  exact hcompact.image hiso.continuous



theorem aux_lem_local_normalizations_lnorm_general_compact
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (b : weakSobolevGraph (centeredCube z r hr))
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (Cmom6 Cband aD : ℝ) (hCmom6 : 0 ≤ Cmom6) (hCband : 0 < Cband) (haD : 0 < aD)
    (hRDmem6 : ∀ N, MemLp (aux_lem_local_normalizations_lnorm_proxy_RD z r hr hP b M H N) (ENNReal.ofReal 6)
      (chaosSampleLaw M).toMeasure)
    (hRDbound6 : ∀ N, eLpNorm (aux_lem_local_normalizations_lnorm_proxy_RD z r hr hP b M H N) (ENNReal.ofReal 6)
      (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cmom6)
    (hRDband : ∀ (h N : ℕ),
      eLpNorm (fun omega => aux_lem_local_normalizations_lnorm_proxy_RD z r hr hP b M H N omega -
          (((chaosSampleLaw M).toMeasure)[aux_lem_local_normalizations_lnorm_proxy_RD z r hr hP b M H N |
            bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]) omega)
        (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Cband * M.delta * (3 : ℝ) ^ (-aD * (h : ℝ))))
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ) :
    ∃ ψ' : ℕ → ℕ, StrictMono ψ' ∧ ∃ L : BilateralField d → ℝ,
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        Tendsto (fun n => aux_lem_local_normalizations_lnorm_proxy_RD z r hr hP b M H (ψ (ψ' n)) omega)
          atTop (𝓝 (L omega)) := by
  haveI hp2 : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 2) :=
    ⟨by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)⟩
  have hpq : ENNReal.ofReal (2 : ℝ) < ENNReal.ofReal (6 : ℝ) :=
    (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 6)).mpr (by norm_num)
  have hq6 : ENNReal.ofReal (6 : ℝ) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hRfmomN : ∀ N, MemLp (aux_lem_local_normalizations_lnorm_proxy_Rf z r hr hP b M N) (ENNReal.ofReal 6)
      (Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_laws M)) ∧
      eLpNorm (aux_lem_local_normalizations_lnorm_proxy_Rf z r hr hP b M N) (ENNReal.ofReal 6)
        (Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_laws M)) ≤ ENNReal.ofReal Cmom6 := fun N =>
    aux_lem_local_normalizations_lnorm_proxy_hmom z r hr hP b M H hH (ENNReal.ofReal 6) N Cmom6 hCmom6
      (hRDmem6 N) (hRDbound6 N)
  obtain ⟨hcompactRf, -, -, -, -⟩ := Paper.prop_response_compact d
    (aux_lem_local_normalizations_lnorm_regroup_Y d) (aux_lem_local_normalizations_lnorm_regroup_laws M) PUnit Empty
    (fun (_ : PUnit) (N : ℕ) (y : (j : ℤ) → aux_lem_local_normalizations_lnorm_regroup_Y d j) =>
      aux_lem_local_normalizations_lnorm_proxy_Rf z r hr hP b M N y)
    (fun (e : Empty) (_ : ℕ) (_ : (j : ℤ) → aux_lem_local_normalizations_lnorm_regroup_Y d j) => e.elim)
    (ENNReal.ofReal 2) (ENNReal.ofReal 6) hpq hq6
    aD M.delta haD M.shellPrefix.delta_pos
    (fun _ => Cband) (fun _ => hCband.le)
    (fun _ => ENNReal.ofReal Cmom6) (fun _ => ENNReal.ofReal_ne_top)
    (fun _ N => (hRfmomN N).1) (fun _ N => (hRfmomN N).2)
    (fun _ h N _ => by
      have hb := aux_lem_local_normalizations_lnorm_proxy_hband z r hr hP b M H hH Cband aD Cmom6 hRDmem6 hRDband h N
      rwa [neg_mul] at hb)
    (fun _ h => aux_lem_local_normalizations_lnorm_proxy_hsplit z r hr hP b M h)
    (fun e => e.elim) (fun e => e.elim) (fun w => w.elim)
  have hcompactRf' := hcompactRf PUnit.unit
  have hRDmem2 : ∀ N, MemLp (aux_lem_local_normalizations_lnorm_proxy_RD z r hr hP b M H N) (ENNReal.ofReal 2)
      (chaosSampleLaw M).toMeasure := fun N => (hRDmem6 N).mono_exponent hpq.le
  have hRfmem2 : ∀ N, MemLp (aux_lem_local_normalizations_lnorm_proxy_Rf z r hr hP b M N) (ENNReal.ofReal 2)
      (Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_laws M)) := fun N =>
    (hRfmomN N).1.mono_exponent hpq.le
  have hcompactRD := aux_lem_local_normalizations_lnorm_proxy_compact_transport z r hr hP b M H hH
    (p := ENNReal.ofReal 2) hRDmem2 hRfmem2 hcompactRf'
  exact aux_lem_local_normalizations_lnorm_proxy_subseq (Ω := BilateralField d) (μ := (chaosSampleLaw M).toMeasure)
    (p := ENNReal.ofReal 2) (aux_lem_local_normalizations_lnorm_proxy_RD z r hr hP b M H) hRDmem2 hcompactRD ψ hψ

/-- Every centered cube is an open bounded convex domain (generalizes
`aux_lem_local_normalizations_unit_poincare`'s own unit-cube geometry witness to any `(z,r,hr)`):
`centeredCube z r hr` is definitionally `Metric.ball z (r/2)`, which is open and convex for any
center/radius, and bounded by `‖z‖ + r/2` (any coordinate of a ball point is within `r/2` of the
corresponding coordinate of `z`, itself at most `‖z‖`). -/
theorem aux_lem_local_normalizations_lnorm_isOpenBoundedConvexDomain {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    Homogenization.IsOpenBoundedConvexDomain (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  have hcube : (centeredCube z r hr : Set (SpatialCoordinates d)) = Metric.ball z (r / 2) := rfl
  rw [hcube]
  refine ⟨Metric.isOpen_ball, ⟨‖z‖ + r / 2, by positivity, ?_⟩, convex_ball z (r / 2)⟩
  intro x hx i
  have hxz : dist x z < r / 2 := hx
  have hi : dist (x i) (z i) ≤ dist x z := dist_le_pi_dist x z i
  have hzi : |z i| ≤ ‖z‖ := by
    simpa [Real.norm_eq_abs] using (norm_le_pi_norm z i)
  have hxzi : |x i - z i| ≤ r / 2 := by
    have := hi.trans hxz.le
    simpa [Real.dist_eq] using this
  have htri : |x i| ≤ |x i - z i| + |z i| := by
    have heq : x i = (x i - z i) + z i := by ring
    calc |x i| = |(x i - z i) + z i| := by rw [← heq]
      _ ≤ |x i - z i| + |z i| := by
          simpa [Real.norm_eq_abs] using norm_add_le (x i - z i) (z i)
  calc |x i| ≤ |x i - z i| + |z i| := htri
    _ ≤ r / 2 + ‖z‖ := add_le_add hxzi hzi
    _ = ‖z‖ + r / 2 := by ring

/-- The pure (coefficient-free) Poincaré bound `hP` for the killed Sobolev graph on any cell. -/
theorem aux_lem_local_normalizations_lnorm_hP_general (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
      ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖ := by
  haveI : NeZero d := ⟨by omega⟩
  exact (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain
    (centeredCube z r hr) (aux_lem_local_normalizations_lnorm_isOpenBoundedConvexDomain z r hr)).1

/-- The fixed affine boundary datum `∑ i, x i` is non-constant on the frontier of any cell (needs
`d > 0`, from `hd : 2 ≤ d`): move by `± r/2` in a single coordinate from two frontier points of the
cube, at distance exactly `r/2` (hence on the sphere = frontier of the ball), whose coordinate sums
differ by exactly `r ≠ 0`. -/
theorem aux_lem_local_normalizations_lnorm_affine_nonconst (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∃ y ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
        (∑ i : Fin d, (1 : ℝ) * x i) ≠ ∑ i : Fin d, (1 : ℝ) * y i := by
  have hcube : (centeredCube z r hr : Set (SpatialCoordinates d)) = Metric.ball z (r / 2) := rfl
  have hfr : frontier (centeredCube z r hr : Set (SpatialCoordinates d)) =
      Metric.sphere z (r / 2) := by
    rw [hcube]; exact frontier_ball z (half_pos hr).ne'
  have hi0 : (0 : ℕ) < d := by omega
  set i0 : Fin d := ⟨0, hi0⟩ with hi0def
  set p : SpatialCoordinates d := fun i => z i + (if i = i0 then r / 2 else 0) with hpdef
  set q : SpatialCoordinates d := fun i => z i - (if i = i0 then r / 2 else 0) with hqdef
  have hmemsphere : ∀ s : SpatialCoordinates d, (∀ i, dist (s i) (z i) ≤ r / 2) →
      dist (s i0) (z i0) = r / 2 → s ∈ Metric.sphere z (r / 2) := by
    intro s hall heq
    rw [sphere_pi z (Or.inl (half_pos hr))]
    exact ⟨Set.mem_iUnion.mpr ⟨i0, heq⟩, (Metric.mem_closedBall).mpr
      ((dist_pi_le_iff (half_pos hr).le).mpr hall)⟩
  have hdist_pos : dist (p i0) (z i0) = r / 2 := by
    have heq : p i0 - z i0 = r / 2 := by
      show z i0 + (if i0 = i0 then r / 2 else 0) - z i0 = r / 2
      rw [if_pos rfl]; ring
    rw [Real.dist_eq, heq, abs_of_nonneg (half_pos hr).le]
  have hdist_neg : dist (q i0) (z i0) = r / 2 := by
    have heq : q i0 - z i0 = -(r / 2) := by
      show z i0 - (if i0 = i0 then r / 2 else 0) - z i0 = -(r / 2)
      rw [if_pos rfl]; ring
    rw [Real.dist_eq, heq, abs_neg, abs_of_nonneg (half_pos hr).le]
  have hbound_p : ∀ i, dist (p i) (z i) ≤ r / 2 := by
    intro i
    by_cases hi : i = i0
    · subst hi; rw [hdist_pos]
    · have heq : p i - z i = 0 := by
        show z i + (if i = i0 then r / 2 else 0) - z i = 0
        rw [if_neg hi]; ring
      rw [Real.dist_eq, heq, abs_zero]; exact (half_pos hr).le
  have hbound_q : ∀ i, dist (q i) (z i) ≤ r / 2 := by
    intro i
    by_cases hi : i = i0
    · subst hi; rw [hdist_neg]
    · have heq : q i - z i = 0 := by
        show z i - (if i = i0 then r / 2 else 0) - z i = 0
        rw [if_neg hi]; ring
      rw [Real.dist_eq, heq, abs_zero]; exact (half_pos hr).le
  refine ⟨p, ?_, q, ?_, ?_⟩
  · rw [hfr]; exact hmemsphere p hbound_p hdist_pos
  · rw [hfr]; exact hmemsphere q hbound_q hdist_neg
  · have hsum : (∑ i : Fin d, (1 : ℝ) * p i) - ∑ i : Fin d, (1 : ℝ) * q i =
        ∑ i : Fin d, (1 : ℝ) * (p i - q i) := by
      rw [← Finset.sum_sub_distrib]; congr 1; funext i; ring
    have hpq : ∀ i : Fin d, p i - q i = if i = i0 then r else 0 := by
      intro i
      by_cases hi : i = i0
      · subst hi
        show z i0 + (if i0 = i0 then r / 2 else 0) -
          (z i0 - (if i0 = i0 then r / 2 else 0)) = r
        rw [if_pos rfl]; ring
      · show z i + (if i = i0 then r / 2 else 0) -
          (z i - (if i = i0 then r / 2 else 0)) = if i = i0 then r else 0
        rw [if_neg hi, if_neg hi]; ring
    have hval : (∑ i : Fin d, (1 : ℝ) * p i) - ∑ i : Fin d, (1 : ℝ) * q i = r := by
      rw [hsum]
      simp only [hpq, mul_ite, mul_zero, one_mul]
      rw [Finset.sum_ite_eq' Finset.univ i0 (fun _ : Fin d => r)]
      simp
    intro hcontra
    rw [hcontra, sub_self] at hval
    exact hr.ne' hval.symm


end AuxLnormProxy

/-- **Infrared regroup transport for local normalizations.** For the finite list of prescribed
`L^p` orders supplied by `rem_bank`, the killed Dirichlet response at any admissible cell, smooth
Neumann datum and continuous positive coefficient obtained from a genuine infrared field `H` admits
a cutoff-uniform `L^6`/`L^q` moment bound, for every model below a threshold depending only on the
standing inputs. Restatement of `aux_lem_local_normalizations_test_rembank_rd_moments` (this file's
own supplier), kept as the file's principal declaration so that `g9_dirichlet_response_compact` and
`g9_neumann_response_wrapper` have a single stable entry point into this regroup/proxy apparatus. -/
theorem lem_local_normalizations_regroup
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (W : SmallPerturbationInput d) (Sf : SobolevFoundationalInput d hd)
    (D : @lane4_deterministic_good_scale_input d ⟨by omega⟩) :
    ∃ (q : ℝ) (delta0 : ℝ), 2 < q ∧ 0 < delta0 ∧
    ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
    ∀ (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
      (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ ∞ phi)
      (b : weakSobolevGraph (centeredCube z r hr))
      (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi),
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (Rm : in_responses d M) (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ))
      (hH : InfraredCharacterization M H),
      M.delta ≤ min 1 delta0 →
      let Pm : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
      let a : ℕ → BilateralField d → PositiveCoefficient (centeredCube z r hr) :=
        fun N omega => cutoffPositiveCoefficient M H omega N z hr
      let RD : ℕ → BilateralField d → ℝ :=
        fun N omega => dirichletResponse (killedResponseSpace hP) (a N omega) b
      ∃ Cmom : ℝ, 0 ≤ Cmom ∧
        ∀ N, MemLp (RD N) (ENNReal.ofReal 6) Pm ∧ MemLp (RD N) (ENNReal.ofReal q) Pm ∧
          eLpNorm (RD N) (ENNReal.ofReal 6) Pm ≤ ENNReal.ofReal Cmom ∧
          eLpNorm (RD N) (ENNReal.ofReal q) Pm ≤ ENNReal.ofReal Cmom :=
  aux_lem_local_normalizations_test_rembank_rd_moments d hd Jc Pc Xc W Sf D

end Paper
