import SubdiffusiveProcess.Main.CutoffCoefficient
import Homogenization.Sobolev.H1.BasicLemmas
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Lane4.CubeDilation
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Lane2.BoundaryResponse
import SubdiffusiveProcess.Lane2.ExternalInputs
import SubdiffusiveProcess.Sobolev.DirichletResponse
import Mathlib.Analysis.Seminorm
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Tactic
import Mathlib
import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
import SubdiffusiveProcess.Sobolev.DomainPoincare
import SubdiffusiveProcess.Lane4.Bridge
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.ScalarFieldPackaging
import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SparseLayerReduction
import SubdiffusiveProcess.Probability.ConditionalPullback
import SubdiffusiveProcess.Sobolev.AffineData
import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Lane3.Interfaces

/-! This module establishes BoundaryResponseFamily for the cutoff-response compactness construction;
it does not identify subsequential limits or assert local-normalization convergence. -/

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Metric
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff
noncomputable section

namespace SubdiffusiveProcess.Lnorm

section


/-- response difference of exp comparison for the cutoff-response compactness construction. -/
theorem response_difference_of_exp_comparison (x E Y : ℝ) (hx : 0 ≤ x)
    (hY : 0 ≤ Y) (hup : E ≤ Real.exp x * Y) (hlo : Y ≤ Real.exp x * E) :
    |E - Y| ≤ 2 * x * Real.exp (4 * x) * Y := by
  have h1 : Real.exp x - 1 ≤ x * Real.exp x := by
    have := Real.add_one_le_exp (-x)
    have hex : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp only [neg_add_cancel, Real.exp_zero]
    nlinarith only [this, hex, Real.exp_pos x]
  have h2 : x * Real.exp x ≤ 2 * x * Real.exp (4 * x) := by
    have : Real.exp x ≤ Real.exp (4 * x) := Real.exp_le_exp.mpr (by linarith only [hx, hY, hup, hlo, h1])
    nlinarith only [hx, hY, hup, hlo, h1, this, Real.exp_pos x]
  have hEnn : 0 ≤ E := by
    by_contra hE
    push_neg at hE
    have : Real.exp x * E < 0 := mul_neg_of_pos_of_neg (Real.exp_pos x) hE
    linarith only [hx, hY, hup, hlo, h1, h2, hE, this]
  have hlo' : Real.exp (-x) * Y ≤ E := by
    have hex : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp only [neg_add_cancel, Real.exp_zero]
    calc Real.exp (-x) * Y ≤ Real.exp (-x) * (Real.exp x * E) :=
          mul_le_mul_of_nonneg_left hlo (Real.exp_pos _).le
      _ = E := by rw [← mul_assoc, hex, one_mul]
  have h3 : 1 - Real.exp (-x) ≤ x := by linarith only [hx, hY, hup, hlo, h1, h2, hEnn, hlo', Real.add_one_le_exp (-x)]
  rw [abs_le]
  constructor
  · nlinarith only [hx, hY, hup, hlo, h1, h2, hEnn, hlo', h3, mul_le_mul_of_nonneg_right h3 hY, mul_le_mul_of_nonneg_right h2 hY, mul_le_mul_of_nonneg_right h1 hY, mul_nonneg hx (Real.exp_pos x).le]
  · nlinarith only [hx, hY, hup, hlo, h1, h2, hEnn, hlo', h3, mul_le_mul_of_nonneg_right h1 hY, mul_le_mul_of_nonneg_right h2 hY]

end

section


/-- lnaff response for the cutoff-response compactness construction. -/
def lnaff_response {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
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
    apply SubdiffusiveProcess.Lnorm.response_difference_of_exp_comparison ‖g‖ _ _ (norm_nonneg g)
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
      nlinarith only [hc, sq_nonneg ‖g‖, Real.exp_pos (4 * ‖g‖), mul_nonneg (sq_nonneg ‖g‖) (Real.exp_pos (4 * ‖g‖)).le]
    calc dirichletResponse S (expPotentialCoefficient (h + g)) b
        ≤ Real.exp ‖g‖ * dirichletResponse S (expPotentialCoefficient h) b := hc
      _ ≤ 2 * Real.exp ‖g‖ * (1 + ‖g‖ ^ 2 * Real.exp (4 * ‖g‖)) *
            dirichletResponse S (expPotentialCoefficient h) b := by
          have hE := Real.exp_pos ‖g‖
          nlinarith only [hc, hn, h1, mul_le_mul_of_nonneg_left h1 (mul_nonneg hE.le hn)]

end

section


/-- lnaff response eval for the cutoff-response compactness construction. -/
theorem lnaff_response_eval {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (b : weakSobolevGraph Ω) (g : SubdiffusiveProcess.Lane3.Potential Ω) :
    (SubdiffusiveProcess.Lnorm.lnaff_response S b).eval g = dirichletResponse S (expPotentialCoefficient g) b := rfl

end

section
variable (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]

/-- regroup Y for the cutoff-response compactness construction. -/
def regroup_Y : ℤ → Type
  | Int.ofNat 0 => C(SpatialCoordinates d, ℝ) × (ℕ → C(SpatialCoordinates d, ℝ))
  | Int.ofNat (_ + 1) => C(SpatialCoordinates d, ℝ)
  | Int.negSucc _ => PUnit

end

section
variable (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]

/-- regroup Y measurableSpace for the cutoff-response compactness construction. -/
instance regroup_Y_measurableSpace :
    ∀ j : ℤ, MeasurableSpace (SubdiffusiveProcess.Lnorm.regroup_Y d j)
  | Int.ofNat 0 =>
      inferInstanceAs (MeasurableSpace
        (C(SpatialCoordinates d, ℝ) × (ℕ → C(SpatialCoordinates d, ℝ))))
  | Int.ofNat (_ + 1) => inferInstanceAs (MeasurableSpace C(SpatialCoordinates d, ℝ))
  | Int.negSucc _ => inferInstanceAs (MeasurableSpace PUnit)

example : SubdiffusiveProcess.Lnorm.regroup_Y d 0 =
    (C(SpatialCoordinates d, ℝ) × (ℕ → C(SpatialCoordinates d, ℝ))) := rfl

example (n : ℕ) : SubdiffusiveProcess.Lnorm.regroup_Y d (n + 1 : ℕ) = C(SpatialCoordinates d, ℝ) := rfl

example (n : ℕ) : SubdiffusiveProcess.Lnorm.regroup_Y d (Int.negSucc n) = PUnit := rfl

end

section
variable (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]

/-- regroup unique zero for the cutoff-response compactness construction. -/
instance regroup_unique_zero : Unique {j : ℤ // ¬ (j ≠ 0)} where
  default := ⟨0, by simp only [ne_eq, not_true_eq_false, not_false_eq_true]⟩
  uniq := fun x => Subtype.ext (not_not.mp x.2)

end

section
variable (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]

/-- regroup ePos for the cutoff-response compactness construction. -/
def regroup_ePos : ℕ ≃ {i : {j : ℤ // j ≠ 0} // 0 < i.1} where
  toFun n :=
    have hne : (Int.ofNat (n + 1) : ℤ) ≠ 0 := by
      show ((n + 1 : ℕ) : ℤ) ≠ 0
      exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    have hpos : (0 : ℤ) < Int.ofNat (n + 1) := by
      show (0 : ℤ) < ((n + 1 : ℕ) : ℤ)
      exact Nat.cast_pos.mpr (Nat.succ_pos n)
    ⟨⟨Int.ofNat (n + 1), hne⟩, hpos⟩
  invFun i := i.1.1.toNat - 1
  left_inv n := by simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one, Int.toNat_natCast_add_one, add_tsub_cancel_right]
  right_inv i := by
    obtain ⟨⟨j, hj⟩, hj1⟩ := i
    simp only at hj1
    have hjt : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj1.le
    apply Subtype.ext
    apply Subtype.ext
    show ((j.toNat - 1 + 1 : ℕ) : ℤ) = j
    omega

end

section
variable (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]

/-- regroup eNeg for the cutoff-response compactness construction. -/
def regroup_eNeg : ℕ ≃ {i : {j : ℤ // j ≠ 0} // ¬ 0 < i.1} where
  toFun n :=
    have hne : (Int.negSucc n : ℤ) ≠ 0 := Int.negSucc_ne_zero n
    have hnp : ¬ (0 : ℤ) < Int.negSucc n := not_lt.mpr (Int.negSucc_lt_zero n).le
    ⟨⟨Int.negSucc n, hne⟩, hnp⟩
  invFun i := (-i.1.1).toNat - 1
  left_inv n := by simp only [Int.neg_negSucc, Nat.cast_add, Nat.cast_one, Int.toNat_natCast_add_one, add_tsub_cancel_right]
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
      simp only [Int.negSucc_eq, neg_add_rev, Int.reduceNeg, Nat.cast_add, Nat.cast_one]
    rw [this, hkey, hjt]
    ring

end

section
variable (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]

/-- regroup p for the cutoff-response compactness construction. -/
abbrev regroup_p : ℤ → Prop := fun j => j ≠ 0

end

section
variable (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]

/-- regroup q for the cutoff-response compactness construction. -/
abbrev regroup_q : ℤ → Prop := fun j => 0 < j

instance : DecidablePred (SubdiffusiveProcess.Lnorm.regroup_p) := fun j => inferInstanceAs (Decidable (j ≠ 0))
instance : DecidablePred (SubdiffusiveProcess.Lnorm.regroup_q) := fun j => inferInstanceAs (Decidable (0 < j))

end

section
variable (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]

/-- regroup padEquiv for the cutoff-response compactness construction. -/
def regroup_padEquiv (α : Type) [MeasurableSpace α] :
    α ≃ᵐ α × (ℕ → PUnit) where
  toFun a := (a, fun _ => PUnit.unit)
  invFun p := p.1
  left_inv _ := rfl
  right_inv p := by
    obtain ⟨a, f⟩ := p
    congr 1
  measurable_toFun := by fun_prop
  measurable_invFun := measurable_fst

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]

/-- regroup ΦY for the cutoff-response compactness construction. -/
def regroup_ΦY :
    ((j : ℤ) → SubdiffusiveProcess.Lnorm.regroup_Y d j) ≃ᵐ
      ((ℕ → C(SpatialCoordinates d, ℝ)) × (ℕ → PUnit)) ×
        (C(SpatialCoordinates d, ℝ) × (ℕ → C(SpatialCoordinates d, ℝ))) :=
  (threeBlockEquiv (X := SubdiffusiveProcess.Lnorm.regroup_Y d)
      SubdiffusiveProcess.Lnorm.regroup_p SubdiffusiveProcess.Lnorm.regroup_q).trans
    (((MeasurableEquiv.piCongrLeft (fun i => SubdiffusiveProcess.Lnorm.regroup_Y d i.1.1)
          SubdiffusiveProcess.Lnorm.regroup_ePos).symm.prodCongr
        (MeasurableEquiv.piCongrLeft (fun i => SubdiffusiveProcess.Lnorm.regroup_Y d i.1.1)
          SubdiffusiveProcess.Lnorm.regroup_eNeg).symm).prodCongr
      (MeasurableEquiv.piUnique
        (fun i : {i : ℤ // ¬ SubdiffusiveProcess.Lnorm.regroup_p i} => SubdiffusiveProcess.Lnorm.regroup_Y d i)))

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]

/-- regroup ΦC for the cutoff-response compactness construction. -/
def regroup_ΦC :
    (ℤ → C(SpatialCoordinates d, ℝ)) ≃ᵐ
      ((ℕ → C(SpatialCoordinates d, ℝ)) × (ℕ → C(SpatialCoordinates d, ℝ))) ×
        C(SpatialCoordinates d, ℝ) :=
  (threeBlockEquiv (X := fun _ : ℤ => C(SpatialCoordinates d, ℝ))
      SubdiffusiveProcess.Lnorm.regroup_p SubdiffusiveProcess.Lnorm.regroup_q).trans
    (((MeasurableEquiv.piCongrLeft (fun _ => C(SpatialCoordinates d, ℝ))
          SubdiffusiveProcess.Lnorm.regroup_ePos).symm.prodCongr
        (MeasurableEquiv.piCongrLeft (fun _ => C(SpatialCoordinates d, ℝ))
          SubdiffusiveProcess.Lnorm.regroup_eNeg).symm).prodCongr
      (MeasurableEquiv.funUnique {i : ℤ // ¬ SubdiffusiveProcess.Lnorm.regroup_p i}
        C(SpatialCoordinates d, ℝ)))

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]



def regroup_bridge :
    ((ℕ → C(SpatialCoordinates d, ℝ)) × (ℕ → C(SpatialCoordinates d, ℝ))) ×
        C(SpatialCoordinates d, ℝ) ≃ᵐ
      ((ℕ → C(SpatialCoordinates d, ℝ)) × (ℕ → PUnit)) ×
        (C(SpatialCoordinates d, ℝ) × (ℕ → C(SpatialCoordinates d, ℝ))) :=
  ((MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl _)).trans
    (MeasurableEquiv.prodAssoc.trans
      ((MeasurableEquiv.refl _).prodCongr MeasurableEquiv.prodComm))).trans
    ((SubdiffusiveProcess.Lnorm.regroup_padEquiv _).prodCongr (MeasurableEquiv.refl _))

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]

/-- regroup for the cutoff-response compactness construction. -/
def regroup :
    (ℤ → C(SpatialCoordinates d, ℝ)) ≃ᵐ ((j : ℤ) → SubdiffusiveProcess.Lnorm.regroup_Y d j) :=
  (SubdiffusiveProcess.Lnorm.regroup_ΦC.trans SubdiffusiveProcess.Lnorm.regroup_bridge).trans SubdiffusiveProcess.Lnorm.regroup_ΦY.symm

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
variable [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)

/-- regroup rootLaw for the cutoff-response compactness construction. -/
def regroup_rootLaw : Measure C(SpatialCoordinates d, ℝ) :=
  (scaledLayerLaw d (chaosRootFieldLaw M) 0).toMeasure

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
variable [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)

/-- regroup coarseLaws for the cutoff-response compactness construction. -/
def regroup_coarseLaws : ℕ → Measure C(SpatialCoordinates d, ℝ) :=
  fun n => (scaledLayerLaw d (chaosRootFieldLaw M) ((n : ℤ) + 1)).toMeasure

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
variable [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)

/-- regroup fineLaws for the cutoff-response compactness construction. -/
def regroup_fineLaws : ℕ → Measure C(SpatialCoordinates d, ℝ) :=
  fun n => (scaledLayerLaw d (chaosRootFieldLaw M) (Int.negSucc n)).toMeasure

instance : IsProbabilityMeasure (SubdiffusiveProcess.Lnorm.regroup_rootLaw M) := by
  unfold SubdiffusiveProcess.Lnorm.regroup_rootLaw; infer_instance

instance (n : ℕ) : IsProbabilityMeasure (SubdiffusiveProcess.Lnorm.regroup_coarseLaws M n) := by
  unfold SubdiffusiveProcess.Lnorm.regroup_coarseLaws; infer_instance

instance (n : ℕ) : IsProbabilityMeasure (SubdiffusiveProcess.Lnorm.regroup_fineLaws M n) := by
  unfold SubdiffusiveProcess.Lnorm.regroup_fineLaws; infer_instance

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
variable [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)

/-- regroup laws for the cutoff-response compactness construction. -/
def regroup_laws : ∀ j : ℤ, Measure (SubdiffusiveProcess.Lnorm.regroup_Y d j)
  | Int.ofNat 0 =>
      (SubdiffusiveProcess.Lnorm.regroup_rootLaw M).prod
        (Measure.infinitePi (SubdiffusiveProcess.Lnorm.regroup_coarseLaws M))
  | Int.ofNat (n + 1) => SubdiffusiveProcess.Lnorm.regroup_fineLaws M n
  | Int.negSucc _ => Measure.dirac PUnit.unit

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
variable [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)

/-- regroup laws isProbabilityMeasure for the cutoff-response compactness construction. -/
instance regroup_laws_isProbabilityMeasure :
    ∀ j : ℤ, IsProbabilityMeasure (SubdiffusiveProcess.Lnorm.regroup_laws M j)
  | Int.ofNat 0 => inferInstanceAs (IsProbabilityMeasure
      ((SubdiffusiveProcess.Lnorm.regroup_rootLaw M).prod
        (Measure.infinitePi (SubdiffusiveProcess.Lnorm.regroup_coarseLaws M))))
  | Int.ofNat (n + 1) => inferInstanceAs (IsProbabilityMeasure (SubdiffusiveProcess.Lnorm.regroup_fineLaws M n))
  | Int.negSucc _ => inferInstanceAs (IsProbabilityMeasure (Measure.dirac PUnit.unit))

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
variable [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)

/-- regroup laws0 for the cutoff-response compactness construction. -/
def regroup_laws0 : ℤ → Measure C(SpatialCoordinates d, ℝ) :=
  fun j => (scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure

instance (j : ℤ) : IsProbabilityMeasure (SubdiffusiveProcess.Lnorm.regroup_laws0 M j) := by
  unfold SubdiffusiveProcess.Lnorm.regroup_laws0; infer_instance

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
variable [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)

/-- regroup chaosSampleLaw eq for the cutoff-response compactness construction. -/
theorem regroup_chaosSampleLaw_eq :
    (chaosSampleLaw M).toMeasure = Measure.infinitePi (SubdiffusiveProcess.Lnorm.regroup_laws0 M) := rfl

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
variable [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)

/-- regroup piCongrLeft mp for the cutoff-response compactness construction. -/
theorem regroup_piCongrLeft_mp {ι : Type} (e : ℕ ≃ ι)
    {F : ι → Type} [∀ i, MeasurableSpace (F i)] (μ : ∀ i, Measure (F i))
    [∀ i, IsProbabilityMeasure (μ i)] :
    MeasurePreserving (MeasurableEquiv.piCongrLeft F e)
      (Measure.infinitePi (fun n => μ (e n))) (Measure.infinitePi μ) :=
  ⟨(MeasurableEquiv.piCongrLeft F e).measurable, Measure.infinitePi_map_piCongrLeft μ e⟩

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
variable [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)

/-- regroup piUnique mp for the cutoff-response compactness construction. -/
theorem regroup_piUnique_mp {ι : Type} [Unique ι] [Fintype ι]
    {F : ι → Type} [∀ i, MeasurableSpace (F i)] (μ : ∀ i, Measure (F i))
    [∀ i, IsProbabilityMeasure (μ i)] :
    MeasurePreserving (MeasurableEquiv.piUnique F) (Measure.infinitePi μ) (μ default) := by
  rw [Measure.infinitePi_eq_pi]
  exact measurePreserving_piUnique μ

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
variable [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)

/-- regroup hΦC for the cutoff-response compactness construction. -/
theorem regroup_hΦC :
    MeasurePreserving (SubdiffusiveProcess.Lnorm.regroup_ΦC (d := d)) (chaosSampleLaw M).toMeasure
      (((Measure.infinitePi (SubdiffusiveProcess.Lnorm.regroup_coarseLaws M)).prod
          (Measure.infinitePi (SubdiffusiveProcess.Lnorm.regroup_fineLaws M))).prod
        (SubdiffusiveProcess.Lnorm.regroup_rootLaw M)) := by
  rw [SubdiffusiveProcess.Lnorm.regroup_chaosSampleLaw_eq]
  have hstep1 := measurePreserving_infinitePi_threeBlock (SubdiffusiveProcess.Lnorm.regroup_laws0 M)
    SubdiffusiveProcess.Lnorm.regroup_p SubdiffusiveProcess.Lnorm.regroup_q (X := fun _ : ℤ => C(SpatialCoordinates d, ℝ))
  have hpos := (SubdiffusiveProcess.Lnorm.regroup_piCongrLeft_mp SubdiffusiveProcess.Lnorm.regroup_ePos
    (fun i : {i : {j : ℤ // SubdiffusiveProcess.Lnorm.regroup_p j} // SubdiffusiveProcess.Lnorm.regroup_q i.1} =>
      SubdiffusiveProcess.Lnorm.regroup_laws0 M i.1.1)).symm
  have hneg := (SubdiffusiveProcess.Lnorm.regroup_piCongrLeft_mp SubdiffusiveProcess.Lnorm.regroup_eNeg
    (fun i : {i : {j : ℤ // SubdiffusiveProcess.Lnorm.regroup_p j} // ¬ SubdiffusiveProcess.Lnorm.regroup_q i.1} =>
      SubdiffusiveProcess.Lnorm.regroup_laws0 M i.1.1)).symm
  have hzero := SubdiffusiveProcess.Lnorm.regroup_piUnique_mp
    (fun i : {i : ℤ // ¬ SubdiffusiveProcess.Lnorm.regroup_p i} => SubdiffusiveProcess.Lnorm.regroup_laws0 M i)
  exact ((hpos.prod hneg).prod hzero).comp hstep1

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
variable [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)

/-- regroup hΦY for the cutoff-response compactness construction. -/
theorem regroup_hΦY :
    MeasurePreserving (SubdiffusiveProcess.Lnorm.regroup_ΦY (d := d)) (Measure.infinitePi (SubdiffusiveProcess.Lnorm.regroup_laws M))
      (((Measure.infinitePi (SubdiffusiveProcess.Lnorm.regroup_fineLaws M)).prod
          (Measure.dirac (fun _ : ℕ => PUnit.unit))).prod
        ((SubdiffusiveProcess.Lnorm.regroup_rootLaw M).prod
          (Measure.infinitePi (SubdiffusiveProcess.Lnorm.regroup_coarseLaws M)))) := by
  have hstep1 := measurePreserving_infinitePi_threeBlock (SubdiffusiveProcess.Lnorm.regroup_laws M)
    SubdiffusiveProcess.Lnorm.regroup_p SubdiffusiveProcess.Lnorm.regroup_q (X := SubdiffusiveProcess.Lnorm.regroup_Y d)
  have hpos := (SubdiffusiveProcess.Lnorm.regroup_piCongrLeft_mp SubdiffusiveProcess.Lnorm.regroup_ePos
    (fun i : {i : {j : ℤ // SubdiffusiveProcess.Lnorm.regroup_p j} // SubdiffusiveProcess.Lnorm.regroup_q i.1} =>
      SubdiffusiveProcess.Lnorm.regroup_laws M i.1.1)).symm
  have hneg0 := (SubdiffusiveProcess.Lnorm.regroup_piCongrLeft_mp SubdiffusiveProcess.Lnorm.regroup_eNeg
    (fun i : {i : {j : ℤ // SubdiffusiveProcess.Lnorm.regroup_p j} // ¬ SubdiffusiveProcess.Lnorm.regroup_q i.1} =>
      SubdiffusiveProcess.Lnorm.regroup_laws M i.1.1)).symm
  have heq : (Measure.infinitePi (fun n : ℕ =>
      SubdiffusiveProcess.Lnorm.regroup_laws M (SubdiffusiveProcess.Lnorm.regroup_eNeg n).1.1)) =
      Measure.dirac (fun _ : ℕ => PUnit.unit) := by
    rw [show (fun n : ℕ => SubdiffusiveProcess.Lnorm.regroup_laws M (SubdiffusiveProcess.Lnorm.regroup_eNeg n).1.1) =
        (fun _ : ℕ => (Measure.dirac PUnit.unit : Measure PUnit)) from rfl]
    exact Measure.infinitePi_dirac _
  have hneg : MeasurePreserving _
      (Measure.infinitePi (fun i : {i : {j : ℤ // SubdiffusiveProcess.Lnorm.regroup_p j} //
          ¬ SubdiffusiveProcess.Lnorm.regroup_q i.1} => SubdiffusiveProcess.Lnorm.regroup_laws M i.1.1))
      (Measure.dirac (fun _ : ℕ => PUnit.unit)) := heq ▸ hneg0
  have hzero := SubdiffusiveProcess.Lnorm.regroup_piUnique_mp
    (fun i : {i : ℤ // ¬ SubdiffusiveProcess.Lnorm.regroup_p i} => SubdiffusiveProcess.Lnorm.regroup_laws M i)
  exact ((hpos.prod hneg).prod hzero).comp hstep1

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
variable [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)

/-- regroup hBridge for the cutoff-response compactness construction. -/
theorem regroup_hBridge :
    MeasurePreserving (SubdiffusiveProcess.Lnorm.regroup_bridge (d := d))
      (((Measure.infinitePi (SubdiffusiveProcess.Lnorm.regroup_coarseLaws M)).prod
          (Measure.infinitePi (SubdiffusiveProcess.Lnorm.regroup_fineLaws M))).prod
        (SubdiffusiveProcess.Lnorm.regroup_rootLaw M))
      (((Measure.infinitePi (SubdiffusiveProcess.Lnorm.regroup_fineLaws M)).prod
          (Measure.dirac (fun _ : ℕ => PUnit.unit))).prod
        ((SubdiffusiveProcess.Lnorm.regroup_rootLaw M).prod
          (Measure.infinitePi (SubdiffusiveProcess.Lnorm.regroup_coarseLaws M)))) := by
  have h1 := (Measure.measurePreserving_swap
      (μ := Measure.infinitePi (SubdiffusiveProcess.Lnorm.regroup_coarseLaws M))
      (ν := Measure.infinitePi (SubdiffusiveProcess.Lnorm.regroup_fineLaws M))).prod
    (MeasurePreserving.id (SubdiffusiveProcess.Lnorm.regroup_rootLaw M))
  have h2 := measurePreserving_prodAssoc
    (Measure.infinitePi (SubdiffusiveProcess.Lnorm.regroup_fineLaws M))
    (Measure.infinitePi (SubdiffusiveProcess.Lnorm.regroup_coarseLaws M)) (SubdiffusiveProcess.Lnorm.regroup_rootLaw M)
  have h3 := (MeasurePreserving.id (Measure.infinitePi (SubdiffusiveProcess.Lnorm.regroup_fineLaws M))).prod
    (Measure.measurePreserving_swap (μ := Measure.infinitePi (SubdiffusiveProcess.Lnorm.regroup_coarseLaws M))
      (ν := SubdiffusiveProcess.Lnorm.regroup_rootLaw M))
  have h4 : MeasurePreserving (SubdiffusiveProcess.Lnorm.regroup_padEquiv (ℕ → C(SpatialCoordinates d, ℝ)))
      (Measure.infinitePi (SubdiffusiveProcess.Lnorm.regroup_fineLaws M))
      ((Measure.infinitePi (SubdiffusiveProcess.Lnorm.regroup_fineLaws M)).prod
        (Measure.dirac (fun _ : ℕ => PUnit.unit))) :=
    ⟨(SubdiffusiveProcess.Lnorm.regroup_padEquiv _).measurable, (Measure.prod_dirac _).symm⟩
  have h5 := h4.prod
    (MeasurePreserving.id ((SubdiffusiveProcess.Lnorm.regroup_rootLaw M).prod
      (Measure.infinitePi (SubdiffusiveProcess.Lnorm.regroup_coarseLaws M))))
  exact h5.comp (h3.comp (h2.comp h1))

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
variable [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)

/-- regroup measurePreserving for the cutoff-response compactness construction. -/
theorem regroup_measurePreserving :
    MeasurePreserving (SubdiffusiveProcess.Lnorm.regroup (d := d)) (chaosSampleLaw M).toMeasure
      (Measure.infinitePi (SubdiffusiveProcess.Lnorm.regroup_laws M)) :=
  (MeasurePreserving.symm SubdiffusiveProcess.Lnorm.regroup_ΦY (SubdiffusiveProcess.Lnorm.regroup_hΦY M)).comp
    ((SubdiffusiveProcess.Lnorm.regroup_hBridge M).comp (SubdiffusiveProcess.Lnorm.regroup_hΦC M))

end

section
variable (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]

/-- htilde partialSumOfSeq for the cutoff-response compactness construction. -/
def htilde_partialSumOfSeq (ctail : ℕ → C(SpatialCoordinates d, ℝ)) (L : ℕ) :
    C(SpatialCoordinates d, ℝ) :=
  Finset.sum (Finset.range L) (fun n => ctail n - ContinuousMap.const _ (ctail n 0))

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] in

end

end SubdiffusiveProcess.Lnorm
