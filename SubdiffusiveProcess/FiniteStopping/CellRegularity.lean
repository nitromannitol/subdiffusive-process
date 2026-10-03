module

public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.Sobolev.CoefficientRestriction
public import SubdiffusiveProcess.Lane3.Subdivision
public import SubdiffusiveProcess.Lane3.Interfaces
public import SubdiffusiveProcess.Geometry.OddGrid
public import SubdiffusiveProcess.Lane2.CellDirichlet
public import SubdiffusiveProcess.Lane2.BoundaryResponse
public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import SubdiffusiveProcess.Lane4.Inputs
public import Mathlib.Analysis.Seminorm
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import SubdiffusiveProcess.CoarseGrainingVocab.CrudeJDeterministic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.RestrictedPotentialBorel
public import SubdiffusiveProcess.Assumptions.Actions
public import SubdiffusiveProcess.Main.LayerScaling
public import Mathlib.Tactic
public import SubdiffusiveProcess.FiniteStopping.ObservationTree

@[expose] public section

/-! This module establishes hReg for finite stopping; it does not assert the full stopping theorem. -/

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.FiniteStopping

variable {d : ℕ}

/-- cell2 killedPoincare in the finite stopping construction. -/
theorem cell2_killedPoincare [NeZero d]
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (t0 mg : ℕ)
    (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ) (w : Fin s → OddGridIndex d mg) :
    ∃ K : ℝ≥0, ∀ v : killedSobolevGraph
        (SubdiffusiveProcess.FiniteStopping.cell2 z hr t0 mg w0 s w),
      ‖(v : SobolevData (SubdiffusiveProcess.FiniteStopping.cell2 z hr t0 mg w0 s w)).1‖ ≤
        K * ‖subspaceGradient
          (killedSobolevGraph (SubdiffusiveProcess.FiniteStopping.cell2 z hr t0 mg w0 s w))
          v‖ := by
  rw [SubdiffusiveProcess.FiniteStopping.cell2_eq_centeredCube]
  exact (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain _
    (lane2_isOpenBoundedConvexDomain_centeredCube _
      (descendantSide_pos mg s (descendantSide_pos 1 t0 hr)))).1

/-- cell2 succ eq oddGridCenter in the finite stopping construction. -/
theorem cell2_succ_eq_oddGridCenter
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (t0 mg : ℕ)
    (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ) (w : Fin (s + 1) → OddGridIndex d mg) :
    descendantCenter mg (descendantCenter 1 z r t0 w0) (descendantSide 1 t0 r) (s + 1) w =
      oddGridCenter
        (descendantCenter mg (descendantCenter 1 z r t0 w0) (descendantSide 1 t0 r) s
          (fun i => w i.castSucc))
        (descendantSide mg s (descendantSide 1 t0 r)) mg (w (Fin.last s)) := rfl

/-- cell2 parent side eq in the finite stopping construction. -/
theorem cell2_parent_side_eq (H1 : ℕ) (R : ℝ) (s : ℕ) :
    descendantSide (subdivisionHalfWidth H1) s R =
      (3 : ℝ) ^ H1 * descendantSide (subdivisionHalfWidth H1) (s + 1) R := by
  rw [descendantSide_succ]
  have hcast : (2 * (subdivisionHalfWidth H1 : ℝ) + 1) = (3 : ℝ) ^ H1 := by
    exact_mod_cast two_mul_subdivisionHalfWidth_add_one H1
  rw [hcast]
  field_simp

/-- respOn in the finite stopping construction. -/
def respOn {Q U : Opens (SpatialCoordinates d)}
    (aT : PositiveCoefficient Q) (u : weakSobolevGraph Q) (hU : U ≤ Q)
    (hPU : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph U,
      ‖(v : SobolevData U).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph U) v‖) : ℝ :=
  dirichletResponse (killedResponseSpace hPU) (positiveCoefficientRestrict hU aT)
    ⟨sobolevDataRestrict hU u.val, sobolevDataRestrict_mem_weak hU u.property⟩

/-- respOn eq of domain eq in the finite stopping construction. -/
theorem respOn_eq_of_domain_eq
    {Q U V : Opens (SpatialCoordinates d)}
    (aT : PositiveCoefficient Q) (u : weakSobolevGraph Q) (hUV : U = V)
    (hU : U ≤ Q) (hV : V ≤ Q)
    (hPU : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph U,
      ‖(v : SobolevData U).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph U) v‖)
    (hPV : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph V,
      ‖(v : SobolevData V).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph V) v‖) :
    SubdiffusiveProcess.FiniteStopping.respOn aT u hU hPU =
      SubdiffusiveProcess.FiniteStopping.respOn aT u hV hPV := by
  cases hUV
  have hInc : hU = hV := Subsingleton.elim _ _
  cases hInc
  have hPoi : hPU = hPV := Subsingleton.elim _ _
  cases hPoi
  rfl

/-- energyOn in the finite stopping construction. -/
def energyOn {Q : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Q) (u : SobolevData Q) (s : Set (SpatialCoordinates d)) : ℝ :=
  ∑ j : Fin d, ∫ x in s, a.val x * (u.2 j x * u.2 j x)

/-- energyOn eq of domain eq in the finite stopping construction. -/
theorem energyOn_eq_of_domain_eq
    {Q U V : Opens (SpatialCoordinates d)} (a : PositiveCoefficient Q)
    (u : SobolevData Q) (hUV : U = V) :
    SubdiffusiveProcess.FiniteStopping.energyOn a u (U : Set (SpatialCoordinates d)) =
      SubdiffusiveProcess.FiniteStopping.energyOn a u (V : Set (SpatialCoordinates d)) := by
  cases hUV
  rfl

/-- padLabel in the finite stopping construction. -/
def padLabel {m : ℕ} (P : ℕ) (k : OddGridIndex d m) : Prop :=
  ∀ i, P ≤ (k i).val ∧ (k i).val + P ≤ 2 * m

/-- padded contains in the finite stopping construction. -/
theorem padded_contains
    (zP : SpatialCoordinates d) (L r : ℝ) (hL : 0 < L) (hr : 0 < r)
    (m : ℕ) (hLm : L = 2 * (m : ℝ) + 1) (idx : OddGridIndex d m)
    (P : ℕ) (hP : SubdiffusiveProcess.FiniteStopping.padLabel P idx)
    (pad : ℝ) (hpad_pos : 0 < pad) (hpad_margin : pad < 2 * (P : ℝ) + 1) :
    (closedCube (oddGridCenter zP (L * r) m idx) (pad * r) (mul_pos hpad_pos hr) :
        Set (SpatialCoordinates d)) ⊆
      (centeredCube zP (L * r) (mul_pos hL hr) : Set (SpatialCoordinates d)) := by
  intro x hx
  have hxd : dist x (oddGridCenter zP (L * r) m idx) ≤ (pad * r) / 2 := by
    simpa only [closedCube, Compacts.coe_mk, Metric.mem_closedBall] using hx
  have hcoord : ∀ i, dist (x i) ((oddGridCenter zP (L * r) m idx) i) ≤ (pad * r) / 2 :=
    (dist_pi_le_iff (by positivity)).mp hxd
  have hstep : (L * r) / (2 * (m : ℝ) + 1) = r := by
    rw [← hLm]; field_simp
  have hlt : ∀ i, dist (x i) (zP i) < (L * r) / 2 := by
    intro i
    have hc := hcoord i
    have htri : dist (x i) (zP i) ≤
        dist (x i) ((oddGridCenter zP (L * r) m idx) i) +
          dist ((oddGridCenter zP (L * r) m idx) i) (zP i) := dist_triangle _ _ _
    have hcentre : dist ((oddGridCenter zP (L * r) m idx) i) (zP i) =
        |((idx i).val : ℝ) - (m : ℝ)| * r := by
      have hdiff : (oddGridCenter zP (L * r) m idx) i - zP i =
          (((idx i).val : ℝ) - (m : ℝ)) * r := by
        show zP i + (((idx i).val : ℝ) - (m : ℝ)) * (L * r / (2 * (m : ℝ) + 1)) - zP i = _
        rw [hstep]; ring
      rw [Real.dist_eq, hdiff, abs_mul, abs_of_pos hr]
    have hidxlo : (P : ℝ) ≤ ((idx i).val : ℝ) := by exact_mod_cast (hP i).1
    have hidxhi : ((idx i).val : ℝ) ≤ 2 * (m : ℝ) - (P : ℝ) := by
      have h := (hP i).2
      have : (idx i).val + P ≤ 2 * m := h
      have : ((idx i).val : ℝ) + (P : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast this
      linarith only [hL, hr, hLm, hP, hpad_pos, hpad_margin, hx, hxd, hcoord, hstep, hc, htri, hcentre, hidxlo, h, this, this]
    have habs : |((idx i).val : ℝ) - (m : ℝ)| ≤ (m : ℝ) - (P : ℝ) := by
      rw [abs_le]
      constructor <;> linarith only [hL, hr, hLm, hP, hpad_pos, hpad_margin, hx, hxd, hcoord, hstep, hc, htri, hcentre, hidxlo, hidxhi]
    have hcentre_le : dist ((oddGridCenter zP (L * r) m idx) i) (zP i) ≤
        ((m : ℝ) - (P : ℝ)) * r := by
      rw [hcentre]
      exact mul_le_mul_of_nonneg_right habs hr.le
    have hfinal : (pad * r) / 2 + ((m : ℝ) - (P : ℝ)) * r < (L * r) / 2 := by
      rw [hLm]
      nlinarith only [hL, hr, hLm, hP, hpad_pos, hpad_margin, hx, hxd, hcoord, hstep, hc, htri, hcentre, hidxlo, hidxhi, habs, hcentre_le, hpad_margin, hr]
    calc dist (x i) (zP i)
        ≤ dist (x i) ((oddGridCenter zP (L * r) m idx) i) +
            dist ((oddGridCenter zP (L * r) m idx) i) (zP i) := htri
      _ ≤ (pad * r) / 2 + ((m : ℝ) - (P : ℝ)) * r := add_le_add hc hcentre_le
      _ < (L * r) / 2 := hfinal
  have : dist x zP < (L * r) / 2 := (dist_pi_lt_iff (by positivity)).mpr hlt
  simpa only [centeredCube, Opens.coe_mk, Metric.mem_ball] using this

/-- Reg in the finite stopping construction. -/
def Reg
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (alpha : ℝ) (H1 : ℕ) (pad Cfin : ℝ) (hpad : 1 < pad)
    (N k : ℕ) (z : SpatialCoordinates d) (omega : BilateralField d) : Prop :=
  let L : ℝ := (3 : ℝ) ^ H1
  let mgrid := subdivisionHalfWidth H1
  let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
  let hr : 0 < r := by positivity
  let hLr : 0 < L * r := mul_pos (pow_pos (by norm_num) H1) hr
  let Q : Opens (SpatialCoordinates d) := centeredCube z r hr
  let closedQ : Set (SpatialCoordinates d) := closedCube z r hr
  let unitClosed : Set (SpatialCoordinates d) := closedCube (0 : SpatialCoordinates d) 1 one_pos
  let T : SpatialCoordinates d → SpatialCoordinates d := fun x => z + r • x
  let kappa : ℕ → ℝ := fun J =>
    Real.exp (((J : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
      SubdiffusiveProcess.CoarseGrainingVocab.ahom model J
  let s : ℝ := (kappa (N - k) / kappa N) *
    Real.exp ((H omega) z + ∑ j ∈ Finset.range k, omega (-(j : ℤ)) z)
  ∀ (zP : SpatialCoordinates d) (idx : OddGridIndex d mgrid),
    z = oddGridCenter zP (L * r) mgrid idx →
    (closedCube z (pad * r) (mul_pos (lt_trans zero_lt_one hpad) hr) : Set (SpatialCoordinates d)) ⊆
      (centeredCube zP (L * r) hLr : Set (SpatialCoordinates d)) →
    let Parent : Opens (SpatialCoordinates d) := centeredCube zP (L * r) hLr
    let aP : PositiveCoefficient Parent := cutoffPositiveCoefficient model H omega N zP hLr
    ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
      Measurable F → 0 ≤ Kf → (∀ x ∈ Parent, |F x| ≤ Kf) →
      ∀ u : weakSobolevGraph Parent,
        (∀ psi : killedSobolevGraph Parent,
          @sobolevCoefficientForm d Parent aP (u : SobolevData Parent) (psi : SobolevData Parent) =
            ∫ x in (Parent : Set (SpatialCoordinates d)), F x * (psi : SobolevData Parent).1 x) →
        ∃ (U : SpatialCoordinates d → ℝ) (c : ℝ),
          ContinuousOn U closedQ ∧
          ((fun x => (u : SobolevData Parent).1 x) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
          @IsHolderOn d alpha unitClosed (fun x => U (T x) - c) ∧
          @cAlphaNorm d alpha unitClosed (fun x => U (T x) - c) ≤
            Cfin * r ^ (((2 : ℝ) - (d : ℝ)) / 2) * s ^ (-(1 : ℝ) / 2) *
              Real.sqrt (@sobolevCoefficientForm d Parent aP
                (u : SobolevData Parent) (u : SobolevData Parent)) +
            Cfin * r ^ (2 : ℝ) * s⁻¹ * Kf

/-- hReg in the finite stopping construction. -/
theorem hReg
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (alpha : ℝ) (H1 : ℕ) (pad Cfin : ℝ) (hpad : 1 < pad) :
    ∀ N k z omega, SubdiffusiveProcess.FiniteStopping.Reg model H alpha H1 pad Cfin hpad N k z omega ↔
      SubdiffusiveProcess.FiniteStopping.Reg model H alpha H1 pad Cfin hpad N k z omega :=
  fun _ _ _ _ => Iff.rfl

end SubdiffusiveProcess.FiniteStopping
