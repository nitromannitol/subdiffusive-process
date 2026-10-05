module

public import SubdiffusiveProcess.Paper.thm_prop_base
public import SubdiffusiveProcess.Paper.prop_conc_setup
public import SubdiffusiveProcess.Paper.affine_source_cells_env
public import SubdiffusiveProcess.Paper.thm_prop_env_cell_arrays
public import SubdiffusiveProcess.Paper.thm_prop_env_measure

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

section Part0
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped Topology ENNReal NNReal InnerProductSpace BigOperators

/-- Killed Poincare inequality for an arbitrary centred cube. -/
theorem aux_thm_prop_env_hPcube {d : ℕ} [NeZero d] (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖ :=
  (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain
      (centeredCube z r hr) (lane2_isOpenBoundedConvexDomain_centeredCube z hr)).1

/-- The normalized response of the concentration setup is the normalized affine response on the cube
of radius `r = 3 ^ (-k)`. -/
theorem aux_thm_prop_env_setup_resp_eq {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (z : SpatialCoordinates d) (k : ℕ)
    (r : ℝ) (hr : 0 < r) (hrk : r = (3 : ℝ) ^ (-(k : ℝ)))
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (hPk : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
        (centeredCube z ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _)),
      ‖(u : SobolevData
          (centeredCube z ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _))).1‖ ≤
        K * ‖subspaceGradient
          (killedSobolevGraph
            (centeredCube z ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _))) u‖)
    (N : ℕ) (β : BilateralField d) (p : Fin d → ℝ) :
    aux_prop_conc_setup_resp model H z k hPk N β p =
      affineDirichletResponse (centeredCube_isBounded z hr) hP
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β N z hr) p /
        (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
  subst hrk
  rfl

end Part0

section Part1
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped Topology ENNReal NNReal InnerProductSpace BigOperators

/-- The basis slopes `e_i` and `e_i + e_j`. -/
def aux_thm_prop_env_basis (d : ℕ) : Fin d ⊕ (Fin d × Fin d) → (Fin d → ℝ)
  | Sum.inl i => (Pi.single i (1 : ℝ) : Fin d → ℝ)
  | Sum.inr ij => (Pi.single ij.1 (1 : ℝ) : Fin d → ℝ) + (Pi.single ij.2 (1 : ℝ) : Fin d → ℝ)

theorem aux_thm_prop_env_basis_mem {d : ℕ} (q : Fin d ⊕ (Fin d × Fin d)) :
    ((∃ i : Fin d, aux_thm_prop_env_basis d q = (Pi.single i (1 : ℝ) : Fin d → ℝ)) ∨
      (∃ i j : Fin d, aux_thm_prop_env_basis d q =
        (Pi.single i (1 : ℝ) : Fin d → ℝ) + (Pi.single j (1 : ℝ) : Fin d → ℝ))) := by
  cases q with
  | inl i => exact Or.inl ⟨i, rfl⟩
  | inr ij => exact Or.inr ⟨ij.1, ij.2, rfl⟩

theorem aux_thm_prop_env_quad_symm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (p : Fin d → ℝ) :
    p ⬝ᵥ (((1 / 2 : ℝ) • (A + A.transpose))).mulVec p = p ⬝ᵥ A.mulVec p := by
  have h : p ⬝ᵥ (A.transpose).mulVec p = p ⬝ᵥ A.mulVec p := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  rw [Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul, dotProduct_add, h]
  simp only [smul_eq_mul]; ring

theorem aux_thm_prop_env_quad_smul {d : ℕ} (c : ℝ) (A : Matrix (Fin d) (Fin d) ℝ) (p : Fin d → ℝ) :
    p ⬝ᵥ (c • A).mulVec p = c * (p ⬝ᵥ A.mulVec p) := by
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- The normalized response of a cell is a quadratic form with a symmetric matrix. -/
theorem aux_thm_prop_env_resp_quadratic {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (z : SpatialCoordinates d) (k : ℕ)
    (hPk : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
        (centeredCube z ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _)),
      ‖(u : SobolevData
          (centeredCube z ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _))).1‖ ≤
        K * ‖subspaceGradient
          (killedSobolevGraph
            (centeredCube z ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _))) u‖)
    (N : ℕ) (β : BilateralField d) :
    ∃ A : Fin d → Fin d → ℝ, (∀ i j, A i j = A j i) ∧
      ∀ p, aux_prop_conc_setup_resp model H z k hPk N β p =
        ∑ i : Fin d, ∑ j : Fin d, A i j * p i * p j := by
  obtain ⟨A, hA, hq⟩ := aux_lem_band_rcJ_bridge_B2_dirichlet_quadratic
    (centeredCube_isBounded z (Real.rpow_pos_of_pos zero_lt_three _)) hPk
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H β N z (Real.rpow_pos_of_pos zero_lt_three _))
  set v : ℝ := (volume (centeredCube z ((3 : ℝ) ^ (-(k : ℝ)))
    (Real.rpow_pos_of_pos zero_lt_three _) : Set (SpatialCoordinates d))).toReal
  refine ⟨fun i j => A i j / v, fun i j => by simp only [hA i j], fun p => ?_⟩
  unfold aux_prop_conc_setup_resp
  rw [hq p, Finset.sum_div]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl; intro j _
  ring

end Part1

section Part2
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped Topology ENNReal NNReal InnerProductSpace BigOperators

theorem aux_thm_prop_env_w_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hHm : Measurable H)
    (z : SpatialCoordinates d) (k : ℕ) :
    Measurable (fun β : BilateralField d =>
      Real.exp (H β z + ∑ j ∈ Finset.Ico (0 : ℤ) (k : ℤ), β (-j) z)) := by
  have hev : Measurable (fun f : C(SpatialCoordinates d, ℝ) => f z) :=
    (continuous_eval_const z).measurable
  refine Real.measurable_exp.comp ((hev.comp hHm).add (Finset.measurable_sum _ fun j _ => ?_))
  exact hev.comp (measurable_pi_apply (-j))

/-- **Original-space limits of the mass-cell affine responses.**  From the constructor's arrays: the
normalized affine responses of the cells `(z c.1, 3 ^ (-(H1 * c.2)))` converge in measure and, along one
common subsequence, almost surely, to quadratic forms of measurable symmetric matrices. -/
theorem thm_prop_env_orig_limits {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hHm : Measurable H)
    (s sigma : ℝ) (gH cbuf : ℕ)
    (Zs : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → ℝ)
    (Draw : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → ENNReal)
    (H1 : ℕ) (z : ℕ → SpatialCoordinates d)
    (Ncut : Fin 2 → ℕ → ℕ) (hNcut : ∀ a, StrictMono (Ncut a)) (psi : ℕ → ℕ) (hpsi : StrictMono psi)
    (eRef : Fin 2 → ℕ → ℝ)
    (hkappa : ∀ a (k : ℕ), Tendsto (fun n =>
      (let kappa : ℕ → ℝ := fun J =>
        Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
       kappa (((Ncut a (psi n) : ℤ) - (k : ℤ)).toNat) / kappa (Ncut a (psi n))))
      atTop (𝓝 (eRef a k)))
    (ZLim DLim : Fin 2 → (ℕ × ℕ) → ∀ (_U : Fin 3 × (Fin d → Fin 3)) (D : ℕ),
      ((Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) → BilateralField d → ℝ)
    (loLim hiLim : Fin 2 → (ℕ × ℕ) → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → ℝ)
    (AELim : Fin 2 → (ℕ × ℕ) → (Fin 3 × (Fin d → Fin 3)) → BilateralField d →
      Matrix (Fin d) (Fin d) ℝ)
    (errLim ratioLim : Fin 2 → (ℕ × ℕ) → Unit → BilateralField d → ℝ)
    (harr : ∀ (a : Fin 2) (c : ℕ × ℕ), aux_affine_source_cells_env_cellArrays I M H s sigma gH cbuf Zs Draw
      (fun n => Ncut a (psi n)) (H1 * c.2) (z c.1) (ZLim a c) (DLim a c) (loLim a c) (hiLim a c)
      (AELim a c) (errLim a c) (ratioLim a c))
    (hAEm : ∀ (a : Fin 2) (c : ℕ × ℕ) (i j : Fin d), Measurable (fun β => AELim a c (0, fun _ => 1) β i j))
    (hPk : ∀ c : ℕ × ℕ, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
        (centeredCube (z c.1) ((3 : ℝ) ^ (-((H1 * c.2 : ℕ) : ℝ)))
          (Real.rpow_pos_of_pos zero_lt_three _)),
      ‖(u : SobolevData (centeredCube (z c.1) ((3 : ℝ) ^ (-((H1 * c.2 : ℕ) : ℝ)))
          (Real.rpow_pos_of_pos zero_lt_three _))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube (z c.1)
          ((3 : ℝ) ^ (-((H1 * c.2 : ℕ) : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _))) u‖) :
    ∃ (psi2 : ℕ → ℕ) (A : Fin 2 → ℕ × ℕ → BilateralField d → Matrix (Fin d) (Fin d) ℝ),
      StrictMono psi2 ∧ (∀ (a : Fin 2) (c : ℕ × ℕ) β, (A a c β).transpose = A a c β) ∧
      (∀ (a : Fin 2) (c : ℕ × ℕ) (i j : Fin d), Measurable (fun β => A a c β i j)) ∧
      (∀ (a : Fin 2) (c : ℕ × ℕ) (p : Fin d → ℝ), TendstoInMeasure (chaosSampleLaw M).toMeasure
        (fun n β => aux_prop_conc_setup_resp M H (z c.1) (H1 * c.2) (hPk c) (Ncut a (psi n)) β p)
        atTop (fun β => p ⬝ᵥ (A a c β).mulVec p)) ∧
      (∀ᵐ β ∂(chaosSampleLaw M).toMeasure, ∀ (a : Fin 2) (c : ℕ × ℕ) (p : Fin d → ℝ),
        Tendsto (fun m => aux_prop_conc_setup_resp M H (z c.1) (H1 * c.2) (hPk c)
          (Ncut a (psi (psi2 m))) β p) atTop (𝓝 (p ⬝ᵥ (A a c β).mulVec p))) := by
  classical
  let P0 : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  have : IsProbabilityMeasure P0 := inferInstance
  let U0 : Fin 3 × (Fin d → Fin 3) := (0, fun _ => 1)
  let w : Fin 2 → ℕ × ℕ → BilateralField d → ℝ := fun a c β =>
    Real.exp (H β (z c.1) + ∑ j ∈ Finset.Ico (0 : ℤ) ((H1 * c.2 : ℕ) : ℤ), β (-j) (z c.1)) *
      (eRef a (H1 * c.2) * 1)
  have hwm : ∀ (a : Fin 2) (c : ℕ × ℕ), Measurable (w a c) := fun a c =>
    (aux_thm_prop_env_w_measurable H hHm (z c.1) (H1 * c.2)).mul measurable_const
  let A : Fin 2 → ℕ × ℕ → BilateralField d → Matrix (Fin d) (Fin d) ℝ := fun a c β =>
    (w a c β) • ((1 / 2 : ℝ) • (AELim a c U0 β + (AELim a c U0 β).transpose))
  have hAquad : ∀ (a : Fin 2) (c : ℕ × ℕ) β (p : Fin d → ℝ), p ⬝ᵥ (A a c β).mulVec p = w a c β * (p ⬝ᵥ (AELim a c U0 β).mulVec p) := by
    intro a c β p
    simp only [A]
    rw [aux_thm_prop_env_quad_smul, aux_thm_prop_env_quad_symm]
  have hAsym : ∀ (a : Fin 2) (c : ℕ × ℕ) β, (A a c β).transpose = A a c β := by
    intro a c β
    simp only [A, Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose]
    rw [add_comm]
  have hAmeas : ∀ (a : Fin 2) (c : ℕ × ℕ) (i j : Fin d), Measurable (fun β => A a c β i j) := by
    intro a c i j
    simp only [A, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
    exact (hwm a c).mul (measurable_const.mul ((hAEm a c i j).add (hAEm a c j i)))
  -- the response of the cell
  have hinM : ∀ (a : Fin 2) (c : ℕ × ℕ) (p : Fin d → ℝ), TendstoInMeasure P0
      (fun n β => aux_prop_conc_setup_resp M H (z c.1) (H1 * c.2) (hPk c) (Ncut a (psi n)) β p)
      atTop (fun β => p ⬝ᵥ (A a c β).mulVec p) := by
    intro a c p
    have hr : (0 : ℝ) < (3 : ℝ) ^ (-((H1 * c.2 : ℕ) : ℝ)) := Real.rpow_pos_of_pos zero_lt_three _
    have hrk : (3 : ℝ) ^ (-((H1 * c.2 : ℕ) : ℝ)) = (3 : ℝ) ^ (-((H1 * c.2 : ℕ) : ℤ)) := by
      rw [← Real.rpow_intCast]; simp
    have hphi : Tendsto (fun n => Ncut a (psi n)) atTop atTop :=
      ((hNcut a).comp hpsi).tendsto_atTop
    have h := thm_prop_env_cell_arrays I M H s sigma gH cbuf Zs Draw
      (fun n => Ncut a (psi n)) (H1 * c.2) (z c.1) (ZLim a c) (DLim a c) (loLim a c) (hiLim a c)
      (AELim a c) (errLim a c) (ratioLim a c) (harr a c) ((3 : ℝ) ^ (-((H1 * c.2 : ℕ) : ℝ))) hr hrk
      hHm (hAEm a c) hphi (eRef a (H1 * c.2)) (hkappa a (H1 * c.2)) (hPk c) p
    have hfun : (fun β => p ⬝ᵥ (A a c β).mulVec p) =
        fun β => w a c β * (p ⬝ᵥ (AELim a c U0 β).mulVec p) := funext fun β => hAquad a c β p
    rw [hfun]
    exact h
  -- one common subsequence for the countably many basis slopes
  obtain ⟨psi2, hpsi2, hae⟩ := aux_env_common_ae_subseq_of_inMeasure (P := P0)
    (ι := Fin 2 × (ℕ × ℕ) × (Fin d ⊕ (Fin d × Fin d)))
    (fun i n β => aux_prop_conc_setup_resp M H (z i.2.1.1) (H1 * i.2.1.2) (hPk i.2.1)
      (Ncut i.1 (psi n)) β (aux_thm_prop_env_basis d i.2.2))
    (fun i β => (aux_thm_prop_env_basis d i.2.2) ⬝ᵥ
      (A i.1 i.2.1 β).mulVec (aux_thm_prop_env_basis d i.2.2))
    (fun i => hinM i.1 i.2.1 _)
  refine ⟨psi2, A, hpsi2, hAsym, hAmeas, hinM, ?_⟩
  filter_upwards [hae] with β hβ a c p
  obtain ⟨AN, A', hsymN, hquadN, hAN, hsymA', hlim⟩ :=
    aux_thm_prop_env_quadratic_matrix_limit_basis (d := d)
      (fun m p => aux_prop_conc_setup_resp M H (z c.1) (H1 * c.2) (hPk c)
        (Ncut a (psi (psi2 m))) β p)
      (fun m => aux_thm_prop_env_resp_quadratic M H (z c.1) (H1 * c.2) (hPk c)
        (Ncut a (psi (psi2 m))) β)
      (fun p hp => by
        rcases hp with ⟨i, hi⟩ | ⟨i, j, hij⟩
        · exact ⟨_, by simpa [hi] using! hβ (a, c, Sum.inl i)⟩
        · exact ⟨_, by simpa [hij] using! hβ (a, c, Sum.inr (i, j))⟩)
  have hbasis : ∀ q : Fin d ⊕ (Fin d × Fin d),
      (aux_thm_prop_env_basis d q) ⬝ᵥ (Matrix.of A').mulVec (aux_thm_prop_env_basis d q) =
      (aux_thm_prop_env_basis d q) ⬝ᵥ (A a c β).mulVec (aux_thm_prop_env_basis d q) := by
    intro q
    rw [aux_thm_prop_matrix_quadratic_eq]
    exact tendsto_nhds_unique (hlim _) (hβ (a, c, q))
  have hEq : Matrix.of A' = A a c β := by
    apply aux_thm_prop_env_matrix_eq_of_basis
    · ext i j; simp [hsymA' i j]
    · exact hAsym a c β
    · intro q hq
      obtain ⟨q', rfl⟩ : ∃ q', aux_thm_prop_env_basis d q' = q := by
        rcases hq with ⟨i, rfl⟩ | ⟨i, j, rfl⟩
        · exact ⟨Sum.inl i, rfl⟩
        · exact ⟨Sum.inr (i, j), rfl⟩
      exact hbasis q'
  have h2 := hlim p
  have hq := aux_thm_prop_matrix_quadratic_eq (Matrix.of A') p
  simp only [Matrix.of_apply] at hq
  rw [← hq, hEq] at h2
  exact h2

end Part2

end SubdiffusiveProcess.Paper
end
