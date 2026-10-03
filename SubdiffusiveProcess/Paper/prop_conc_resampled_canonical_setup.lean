module

public import SubdiffusiveProcess.Paper.prop_conc_setup
public import SubdiffusiveProcess.Paper.prop_conc_weighted_identification_transfer
public import SubdiffusiveProcess.Paper.prop_conc_resampled_limit_order
public import SubdiffusiveProcess.Sobolev.KilledVolumeResponse
public import SubdiffusiveProcess.Sobolev.AffineData
public import SubdiffusiveProcess.Sobolev.MeanZero
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import Mathlib.Tactic

@[expose] public section

/-! The setup of `prop_conc` at the canonical field space.  From a represented setup on `(Ω, P, field)` with `field_* P = chaos`,
the same data read as functions of the field itself give the setup on `(BilateralField d, chaos, id)`: the cutoff operators are
the volume-response operators of the cutoff coefficient of the field, their limits (existing on a measurable set) are the
`limUnder`s, the form order transfers through the reversed order of the quadratic forms of the operators (a closed condition on a
countable dense set), and the response matrices are the polarizations of the limits of the (quadratic) affine responses.  This lets
the frozen typical-pair statement be applied at a sample space on which the resampled fields are again sample points. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology BigOperators

namespace Paper
noncomputable section


theorem aux_prop_conc_resampled_canonical_setup_quadratic_of_linear {d : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (M : (Fin d → ℝ) → V)
    (hMadd : ∀ p q, M (p + q) = M p + M q)
    (hMsmul : ∀ (r : ℝ) (p : Fin d → ℝ), M (r • p) = r • M p)
    (bil : V → V → ℝ)
    (hbil_add_l : ∀ u v w, bil (u + v) w = bil u w + bil v w)
    (hbil_smul_l : ∀ (r : ℝ) u w, bil (r • u) w = r * bil u w)
    (hbil_add_r : ∀ u v w, bil u (v + w) = bil u v + bil u w)
    (hbil_smul_r : ∀ (r : ℝ) u w, bil u (r • w) = r * bil u w)
    (e : Fin d → ℝ) :
    bil (M e) (M e) =
      ∑ i : Fin d, ∑ j : Fin d, bil (M ((Pi.single i 1 : Fin d → ℝ))) (M ((Pi.single j 1 : Fin d → ℝ))) * e i * e j := by
  classical
  have hM0 : M 0 = 0 := by simpa using hMsmul 0 0
  have hbil0l : ∀ w, bil 0 w = 0 := by
    intro w
    have h := hbil_add_l 0 0 w
    simpa using h
  have hbil0r : ∀ u, bil u 0 = 0 := by
    intro u
    have h := hbil_add_r u 0 0
    simpa using h
  have hMsum : ∀ (s : Finset (Fin d)) (c : Fin d → ℝ),
      M (∑ i ∈ s, c i • (Pi.single i 1 : Fin d → ℝ)) = ∑ i ∈ s, c i • M ((Pi.single i 1 : Fin d → ℝ)) := by
    intro s c
    induction s using Finset.induction with
    | empty => simpa using hM0
    | insert a s' hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx, hMadd, hMsmul, ih]
  have hbilsum_l : ∀ (s : Finset (Fin d)) (v : Fin d → V) (w : V),
      bil (∑ i ∈ s, v i) w = ∑ i ∈ s, bil (v i) w := by
    intro s v w
    induction s using Finset.induction with
    | empty => simpa using hbil0l w
    | insert a s' hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx, hbil_add_l, ih]
  have hbilsum_r : ∀ (s : Finset (Fin d)) (u : V) (v : Fin d → V),
      bil u (∑ j ∈ s, v j) = ∑ j ∈ s, bil u (v j) := by
    intro s u v
    induction s using Finset.induction with
    | empty => simpa using hbil0r u
    | insert a s' hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx, hbil_add_r, ih]
  have he : e = ∑ i : Fin d, e i • Pi.single (M := fun _ : Fin d => ℝ) i 1 := pi_eq_sum_univ' e
  have hMe : M e = ∑ i : Fin d, e i • M ((Pi.single i 1 : Fin d → ℝ)) := by
    conv_lhs => rw [he]
    exact hMsum Finset.univ e
  rw [hMe, hbilsum_l Finset.univ (fun i => e i • M ((Pi.single i 1 : Fin d → ℝ))) (∑ j, e j • M ((Pi.single j 1 : Fin d → ℝ)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hbil_smul_l, hbilsum_r Finset.univ (M ((Pi.single i 1 : Fin d → ℝ))) (fun j => e j • M ((Pi.single j 1 : Fin d → ℝ)))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hbil_smul_r]
  ring

section DomainConstant

variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
  [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]

theorem aux_prop_conc_resampled_canonical_setup_domainConstantL2_add (c1 c2 : ℝ) :
    domainConstantL2 (Ω := Ω) (c1 + c2) = domainConstantL2 c1 + domainConstantL2 c2 := by
  unfold domainConstantL2
  have hfun : (fun _ : SpatialCoordinates d => c1 + c2) =
      (fun _ : SpatialCoordinates d => c1) + (fun _ : SpatialCoordinates d => c2) := by
    funext x; simp
  rw [MemLp.toLp_congr (memLp_const (c1 + c2)) ((memLp_const c1).add (memLp_const c2))
    (Filter.EventuallyEq.of_eq hfun), MemLp.toLp_add]

theorem aux_prop_conc_resampled_canonical_setup_domainConstantL2_smul (r c : ℝ) :
    domainConstantL2 (Ω := Ω) (r * c) = r • domainConstantL2 c := by
  unfold domainConstantL2
  have hfun : (fun _ : SpatialCoordinates d => r * c) = r • (fun _ : SpatialCoordinates d => c) := by
    funext x; simp
  rw [MemLp.toLp_congr (memLp_const (r * c)) ((memLp_const c).const_smul r)
    (Filter.EventuallyEq.of_eq hfun), MemLp.toLp_const_smul]

end DomainConstant

section DirichletQuadratic

variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
  [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]

theorem aux_prop_conc_resampled_canonical_setup_affineL2_add (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (p q : Fin d → ℝ) :
    affineL2 hΩ (p + q) 0 = affineL2 hΩ p 0 + affineL2 hΩ q 0 := by
  unfold affineL2
  have hfun : (fun x => affineSlope (p + q) x + 0) =
      (fun x => affineSlope p x + 0) + (fun x => affineSlope q x + 0) := by
    funext x
    simp only [Pi.add_apply, affineSlope_apply, add_zero]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [MemLp.toLp_congr (affine_memLp hΩ (p + q) 0) ((affine_memLp hΩ p 0).add (affine_memLp hΩ q 0))
    (Filter.EventuallyEq.of_eq hfun), MemLp.toLp_add]

theorem aux_prop_conc_resampled_canonical_setup_affineL2_smul (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (r : ℝ) (p : Fin d → ℝ) :
    affineL2 hΩ (r • p) 0 = r • affineL2 hΩ p 0 := by
  unfold affineL2
  have hfun : (fun x => affineSlope (r • p) x + 0) = r • (fun x => affineSlope p x + 0) := by
    funext x
    simp only [Pi.smul_apply, affineSlope_apply, add_zero, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [MemLp.toLp_congr (affine_memLp hΩ (r • p) 0) ((affine_memLp hΩ p 0).const_smul r)
    (Filter.EventuallyEq.of_eq hfun), MemLp.toLp_const_smul]

theorem aux_prop_conc_resampled_canonical_setup_affineSobolev_add
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d))) (p q : Fin d → ℝ) :
    affineSobolev hΩ (p + q) 0 = affineSobolev hΩ p 0 + affineSobolev hΩ q 0 := by
  apply Subtype.ext
  show affineSobolevData hΩ (p + q) 0 =
      (affineSobolev hΩ p 0 : SobolevData Ω) + (affineSobolev hΩ q 0 : SobolevData Ω)
  show affineSobolevData hΩ (p + q) 0 = affineSobolevData hΩ p 0 + affineSobolevData hΩ q 0
  unfold affineSobolevData
  apply Prod.ext
  · exact aux_prop_conc_resampled_canonical_setup_affineL2_add hΩ p q
  · funext i
    show domainConstantL2 ((p + q) i) = domainConstantL2 (p i) + domainConstantL2 (q i)
    rw [Pi.add_apply]
    exact aux_prop_conc_resampled_canonical_setup_domainConstantL2_add (p i) (q i)

theorem aux_prop_conc_resampled_canonical_setup_affineSobolev_smul
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d))) (r : ℝ) (p : Fin d → ℝ) :
    affineSobolev hΩ (r • p) 0 = r • affineSobolev hΩ p 0 := by
  apply Subtype.ext
  show affineSobolevData hΩ (r • p) 0 = r • (affineSobolev hΩ p 0 : SobolevData Ω)
  show affineSobolevData hΩ (r • p) 0 = r • affineSobolevData hΩ p 0
  unfold affineSobolevData
  apply Prod.ext
  · exact aux_prop_conc_resampled_canonical_setup_affineL2_smul hΩ r p
  · funext i
    show domainConstantL2 (Ω := Ω) ((r • p) i) = r • domainConstantL2 (Ω := Ω) (p i)
    rw [Pi.smul_apply, smul_eq_mul]
    exact aux_prop_conc_resampled_canonical_setup_domainConstantL2_smul r (p i)

end DirichletQuadratic
section DirichletQuadraticFinal

variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
  [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]

theorem aux_prop_conc_resampled_canonical_setup_dirichlet_quadratic
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hP : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) z‖)
    (a : PositiveCoefficient Ω) :
    ∃ A : Fin d → Fin d → ℝ, (∀ i j, A i j = A j i) ∧
      ∀ e : Fin d → ℝ,
        affineDirichletResponse hΩ hP a e = ∑ i : Fin d, ∑ j : Fin d, A i j * e i * e j := by
  set S := killedResponseSpace hP with hSdef
  let Mv : (Fin d → ℝ) → SobolevData Ω :=
    fun p => (dirichletMinimizer S a (affineSobolev hΩ p 0) : SobolevData Ω)
  have hMvadd : ∀ p q, Mv (p + q) = Mv p + Mv q := by
    intro p q
    show (dirichletMinimizer S a (affineSobolev hΩ (p + q) 0) : SobolevData Ω) = _
    rw [aux_prop_conc_resampled_canonical_setup_affineSobolev_add hΩ, dirichletMinimizer_add]
    rfl
  have hMvsmul : ∀ (r : ℝ) p, Mv (r • p) = r • Mv p := by
    intro r p
    show (dirichletMinimizer S a (affineSobolev hΩ (r • p) 0) : SobolevData Ω) = _
    rw [aux_prop_conc_resampled_canonical_setup_affineSobolev_smul hΩ, dirichletMinimizer_smul]
    rfl
  have hbil_add_l : ∀ u v w : SobolevData Ω, sobolevCoefficientForm a (u + v) w =
      sobolevCoefficientForm a u w + sobolevCoefficientForm a v w := by
    intro u v w; simp only [map_add, ContinuousLinearMap.add_apply]
  have hbil_smul_l : ∀ (r : ℝ) (u w : SobolevData Ω),
      sobolevCoefficientForm a (r • u) w = r * sobolevCoefficientForm a u w := by
    intro r u w; simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hbil_add_r : ∀ u v w : SobolevData Ω, sobolevCoefficientForm a u (v + w) =
      sobolevCoefficientForm a u v + sobolevCoefficientForm a u w := by
    intro u v w; simp only [map_add]
  have hbil_smul_r : ∀ (r : ℝ) (u w : SobolevData Ω),
      sobolevCoefficientForm a u (r • w) = r * sobolevCoefficientForm a u w := by
    intro r u w; simp only [map_smul, smul_eq_mul]
  refine ⟨fun i j => sobolevCoefficientForm a (Mv (Pi.single i 1)) (Mv (Pi.single j 1)),
    fun i j => ?_, fun e => ?_⟩
  · exact sobolevCoefficientForm_symm a _ _
  · have hq := aux_prop_conc_resampled_canonical_setup_quadratic_of_linear Mv hMvadd hMvsmul
      (fun u v => sobolevCoefficientForm a u v) hbil_add_l hbil_smul_l hbil_add_r hbil_smul_r e
    unfold affineDirichletResponse dirichletResponse
    exact hq

end DirichletQuadraticFinal


section Polarization
variable {d : ℕ}

/-- The symmetric matrix whose quadratic form is polarized from the values `ell` at the slopes `e_i`, `e_i + e_j`. -/
def aux_prop_conc_resampled_canonical_setup_polMat (ell : (Fin d → ℝ) → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun a b => if a = b then ell (Pi.single a 1)
    else (ell (Pi.single a 1 + Pi.single b 1) - ell (Pi.single a 1) - ell (Pi.single b 1)) / 2

theorem aux_prop_conc_resampled_canonical_setup_polMat_symm (ell : (Fin d → ℝ) → ℝ) :
    (aux_prop_conc_resampled_canonical_setup_polMat ell).transpose =
      aux_prop_conc_resampled_canonical_setup_polMat ell := by
  ext a b
  simp only [Matrix.transpose_apply, aux_prop_conc_resampled_canonical_setup_polMat, Matrix.of_apply]
  by_cases hab : a = b
  · subst hab; simp
  · have hba : b ≠ a := fun h => hab h.symm
    simp only [hab, hba, if_false, add_comm (Pi.single b (1 : ℝ) : Fin d → ℝ)]
    ring

/-- The polarization of a family of quadratic forms whose values at the polarizing slopes converge converges
everywhere to the quadratic form of the polarized limit matrix. -/
theorem aux_prop_conc_resampled_canonical_setup_polarize
    (rho : ℕ → (Fin d → ℝ) → ℝ)
    (hq : ∀ n, ∃ A : Fin d → Fin d → ℝ, (∀ i j, A i j = A j i) ∧
      ∀ e : Fin d → ℝ, rho n e = ∑ i : Fin d, ∑ j : Fin d, A i j * e i * e j)
    (ell : (Fin d → ℝ) → ℝ)
    (hl : ∀ a b : Fin d, Tendsto (fun n => rho n (Pi.single a 1)) atTop (𝓝 (ell (Pi.single a 1))) ∧
      Tendsto (fun n => rho n (Pi.single a 1 + Pi.single b 1)) atTop
        (𝓝 (ell (Pi.single a 1 + Pi.single b 1)))) (pvec : Fin d → ℝ) :
    Tendsto (fun n => rho n pvec) atTop
      (𝓝 (pvec ⬝ᵥ (aux_prop_conc_resampled_canonical_setup_polMat ell).mulVec pvec)) := by
  classical
  choose A hAsymm hA using hq
  have hdiag : ∀ n a, A n a a = rho n (Pi.single a 1) := by
    intro n a
    rw [hA n]
    simp [Pi.single_apply]
  have hsum : ∀ n a b, rho n (Pi.single a 1 + Pi.single b 1) =
      A n a a + A n a b + A n b a + A n b b := by
    intro n a b
    rw [hA n]
    simp [Pi.single_apply, mul_add, Finset.sum_add_distrib]
    ring
  have hentry : ∀ a b : Fin d, Tendsto (fun n => A n a b) atTop
      (𝓝 (aux_prop_conc_resampled_canonical_setup_polMat ell a b)) := by
    intro a b
    by_cases hab : a = b
    · subst hab
      simp only [aux_prop_conc_resampled_canonical_setup_polMat, Matrix.of_apply, if_true]
      exact (hl a a).1.congr (fun n => (hdiag n a).symm)
    · simp only [aux_prop_conc_resampled_canonical_setup_polMat, Matrix.of_apply, hab, if_false]
      have h := (((hl a b).2.sub (hl a a).1).sub (hl b b).1).div_const 2
      refine h.congr (fun n => ?_)
      have e1 := hsum n a b
      rw [hAsymm n b a] at e1
      rw [hdiag n a, hdiag n b] at e1
      linarith
  have hfin : ∀ n, rho n pvec = ∑ i : Fin d, ∑ j : Fin d, A n i j * pvec i * pvec j := fun n => hA n pvec
  have hMsum : pvec ⬝ᵥ (aux_prop_conc_resampled_canonical_setup_polMat ell).mulVec pvec =
      ∑ i : Fin d, ∑ j : Fin d, aux_prop_conc_resampled_canonical_setup_polMat ell i j * pvec i * pvec j := by
    simp only [dotProduct, Matrix.mulVec]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hMsum]
  refine Tendsto.congr (fun n => (hfin n).symm) ?_
  refine tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ => ?_
  exact ((hentry i j).mul_const _).mul_const _

/-- Transfer of the convergence of a quadratic response family from a represented field to its law: the limit exists
on a measurable set (the values at the polarizing slopes), and the polarized matrix of the limits carries all slopes. -/
theorem aux_prop_conc_resampled_canonical_setup_matrix_transfer
    {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω] {P : Measure Ω} {μ : Measure X}
    {field : Ω → X} (hfield : MeasurePreserving field P μ)
    (rho : ℕ → X → (Fin d → ℝ) → ℝ)
    (hrm : ∀ n p, Measurable (fun x => rho n x p))
    (hq : ∀ n x, ∃ A : Fin d → Fin d → ℝ, (∀ i j, A i j = A j i) ∧
      ∀ e : Fin d → ℝ, rho n x e = ∑ i : Fin d, ∑ j : Fin d, A i j * e i * e j)
    (B : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hB : ∀ᵐ ω ∂P, ∀ pvec : Fin d → ℝ, Tendsto (fun n => rho n (field ω) pvec) atTop
      (𝓝 (pvec ⬝ᵥ (B ω).mulVec pvec))) :
    ∀ᵐ x ∂μ, ∀ pvec : Fin d → ℝ, Tendsto (fun n => rho n x pvec) atTop
      (𝓝 (pvec ⬝ᵥ (aux_prop_conc_resampled_canonical_setup_polMat
        (fun p => limUnder atTop (fun n => rho n x p))).mulVec pvec)) := by
  classical
  let Sl : (Fin d → ℝ) → Set X := fun p => {x | ∃ L, Tendsto (fun n => rho n x p) atTop (𝓝 L)}
  have hSl : ∀ p, MeasurableSet (Sl p) := fun p =>
    measurableSet_exists_tendsto (l := atTop) (fun n => hrm n p)
  let S : Set X := ⋂ a : Fin d, ⋂ b : Fin d, Sl (Pi.single a 1) ∩ Sl (Pi.single a 1 + Pi.single b 1)
  have hS : MeasurableSet S :=
    MeasurableSet.iInter fun a => MeasurableSet.iInter fun b => (hSl _).inter (hSl _)
  have hmem : ∀ᵐ ω ∂P, field ω ∈ S := by
    filter_upwards [hB] with ω hω
    simp only [S, Set.mem_iInter]
    intro a b
    exact ⟨⟨_, hω _⟩, ⟨_, hω _⟩⟩
  have hae := aux_prop_conc_weighted_identification_transfer_ae hfield hS hmem
  filter_upwards [hae] with x hx pvec
  simp only [S, Set.mem_iInter] at hx
  refine aux_prop_conc_resampled_canonical_setup_polarize (fun n => rho n x) (fun n => hq n x) _
    (fun a b => ⟨tendsto_nhds_limUnder (hx a b).1, tendsto_nhds_limUnder (hx a b).2⟩) pvec

end Polarization

section Order
variable {d : ℕ}

/-- Symmetry passes to norm limits. -/
theorem aux_prop_conc_resampled_canonical_setup_limit_symm {Q : Opens (SpatialCoordinates d)}
    (U : ℕ → DomainL2 Q →L[ℝ] DomainL2 Q) (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hU : Tendsto U atTop (𝓝 G))
    (hs : ∀ n a b, inner ℝ (U n a) b = inner ℝ a (U n b)) :
    ∀ a b, inner ℝ (G a) b = inner ℝ a (G b) := by
  intro a b
  have hUa : ∀ v : DomainL2 Q, Tendsto (fun n => U n v) atTop (𝓝 (G v)) := fun v =>
    ((ContinuousLinearMap.apply ℝ (DomainL2 Q) v).continuous.tendsto G).comp hU
  have h1 := Filter.Tendsto.inner (𝕜 := ℝ) (hUa a) (tendsto_const_nhds (x := b))
  have h2 := Filter.Tendsto.inner (𝕜 := ℝ) (tendsto_const_nhds (x := a)) (hUa b)
  exact tendsto_nhds_unique (h1.congr (fun n => hs n a b)) h2

/-- Nonnegativity of the quadratic form passes to norm limits. -/
theorem aux_prop_conc_resampled_canonical_setup_limit_nonneg {Q : Opens (SpatialCoordinates d)}
    (U : ℕ → DomainL2 Q →L[ℝ] DomainL2 Q) (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hU : Tendsto U atTop (𝓝 G)) (hp : ∀ n a, 0 ≤ inner ℝ a (U n a)) :
    ∀ a, 0 ≤ inner ℝ a (G a) := by
  intro a
  have hUa : Tendsto (fun n => U n a) atTop (𝓝 (G a)) :=
    ((ContinuousLinearMap.apply ℝ (DomainL2 Q) a).continuous.tendsto G).comp hU
  have h1 := Filter.Tendsto.inner (𝕜 := ℝ) (tendsto_const_nhds (x := a)) hUa
  exact ge_of_tendsto h1 (Eventually.of_forall fun n => hp n a)


/-- Transfer of the form order of the limit forms from a represented field to its law, through the reversed order of the
quadratic forms of the operators (a closed condition tested on a countable dense set). -/
theorem aux_prop_conc_resampled_canonical_setup_order_transfer
    {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω] {P : Measure Ω} {μ : Measure X}
    {field : Ω → X} (hfield : MeasurePreserving field P μ) (Q : Opens (SpatialCoordinates d))
    (UE UF : ℕ → X → DomainL2 Q →L[ℝ] DomainL2 Q)
    (hUE : ∀ n, StronglyMeasurable (UE n)) (hUF : ∀ n, StronglyMeasurable (UF n))
    (hsE : ∀ n x a b, inner ℝ (UE n x a) b = inner ℝ a (UE n x b))
    (hpE : ∀ n x a, 0 ≤ inner ℝ a (UE n x a))
    (hsF : ∀ n x a b, inner ℝ (UF n x a) b = inner ℝ a (UF n x b))
    (hpF : ∀ n x a, 0 ≤ inner ℝ a (UF n x a))
    (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
    (LE LF : Ω → DomainL2 Q →L[ℝ] DomainL2 Q)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => UE n (field ω)) atTop (𝓝 (LE ω)) ∧
      Tendsto (fun n => UF n (field ω)) atTop (𝓝 (LF ω)))
    (hord : ∀ᵐ ω ∂P, limitFormDomain (LE ω) = limitFormDomain (LF ω) ∧
      ∀ u ∈ limitFormDomain (LE ω), m * (limitFormEnergy (LE ω) u).toReal ≤
        (limitFormEnergy (LF ω) u).toReal ∧
        (limitFormEnergy (LF ω) u).toReal ≤ M * (limitFormEnergy (LE ω) u).toReal) :
    ∀ᵐ x ∂μ, (∃ G, Tendsto (fun n => UE n x) atTop (𝓝 G)) ∧
      (∃ G, Tendsto (fun n => UF n x) atTop (𝓝 G)) ∧
      (limitFormDomain (limUnder atTop (fun n => UE n x)) =
          limitFormDomain (limUnder atTop (fun n => UF n x)) ∧
        ∀ u ∈ limitFormDomain (limUnder atTop (fun n => UE n x)),
          m * (limitFormEnergy (limUnder atTop (fun n => UE n x)) u).toReal ≤
            (limitFormEnergy (limUnder atTop (fun n => UF n x)) u).toReal ∧
          (limitFormEnergy (limUnder atTop (fun n => UF n x)) u).toReal ≤
            M * (limitFormEnergy (limUnder atTop (fun n => UE n x)) u).toReal) := by
  classical
  obtain ⟨u, hu⟩ := exists_dense_seq_domainL2 Q
  -- the scalar quadratic forms along the sequences
  let qE : ℕ → ℕ → X → ℝ := fun k n x => inner ℝ (u k) (UE n x (u k))
  let qF : ℕ → ℕ → X → ℝ := fun k n x => inner ℝ (u k) (UF n x (u k))
  have hcontq : ∀ k, Continuous (fun A : DomainL2 Q →L[ℝ] DomainL2 Q => inner ℝ (u k) (A (u k))) :=
    fun k => (innerSL ℝ (u k)).continuous.comp
      (ContinuousLinearMap.apply ℝ (DomainL2 Q) (u k)).continuous
  have hqE : ∀ k n, Measurable (qE k n) := fun k n =>
    ((hcontq k).comp_stronglyMeasurable (hUE n)).measurable
  have hqF : ∀ k n, Measurable (qF k n) := fun k n =>
    ((hcontq k).comp_stronglyMeasurable (hUF n)).measurable
  let ellE : ℕ → X → ℝ := fun k x => limUnder atTop (fun n => qE k n x)
  let ellF : ℕ → X → ℝ := fun k x => limUnder atTop (fun n => qF k n x)
  have hellE : ∀ k, Measurable (ellE k) := fun k =>
    (StronglyMeasurable.limUnder (l := atTop) (fun n => (hqE k n).stronglyMeasurable)).measurable
  have hellF : ∀ k, Measurable (ellF k) := fun k =>
    (StronglyMeasurable.limUnder (l := atTop) (fun n => (hqF k n).stronglyMeasurable)).measurable
  let S1 : Set X := {x | ∃ G, Tendsto (fun n => UE n x) atTop (𝓝 G)}
  let S2 : Set X := {x | ∃ G, Tendsto (fun n => UF n x) atTop (𝓝 G)}
  let S3 : Set X := ⋂ k : ℕ, {x | ellF k x ≤ m⁻¹ * ellE k x ∧ M⁻¹ * ellE k x ≤ ellF k x}
  have hS1 : MeasurableSet S1 := aux_prop_conc_weighted_identification_transfer_operator_event Q UE hUE
  have hS2 : MeasurableSet S2 := aux_prop_conc_weighted_identification_transfer_operator_event Q UF hUF
  have hS3 : MeasurableSet S3 := MeasurableSet.iInter fun k =>
    (measurableSet_le (hellF k) ((hellE k).const_mul _)).inter
      (measurableSet_le ((hellE k).const_mul _) (hellF k))
  -- the scalar limit is the quadratic form of the operator limit
  have hlimq : ∀ (U : ℕ → DomainL2 Q →L[ℝ] DomainL2 Q) (G : DomainL2 Q →L[ℝ] DomainL2 Q)
      (k : ℕ), Tendsto U atTop (𝓝 G) →
      limUnder atTop (fun n => inner ℝ (u k) (U n (u k))) = inner ℝ (u k) (G (u k)) := by
    intro U G k hU
    refine Tendsto.limUnder_eq ?_
    exact ((hcontq k).tendsto G).comp hU
  have hmem : ∀ᵐ ω ∂P, field ω ∈ S1 ∩ S2 ∩ S3 := by
    filter_upwards [hlim, hord] with ω hlimω hordω
    have hEs := aux_prop_conc_resampled_canonical_setup_limit_symm (fun n => UE n (field ω)) (LE ω)
      hlimω.1 (fun n a b => hsE n (field ω) a b)
    have hEp := aux_prop_conc_resampled_canonical_setup_limit_nonneg (fun n => UE n (field ω)) (LE ω)
      hlimω.1 (fun n a => hpE n (field ω) a)
    have hFs := aux_prop_conc_resampled_canonical_setup_limit_symm (fun n => UF n (field ω)) (LF ω)
      hlimω.2 (fun n a b => hsF n (field ω) a b)
    have hFp := aux_prop_conc_resampled_canonical_setup_limit_nonneg (fun n => UF n (field ω)) (LF ω)
      hlimω.2 (fun n a => hpF n (field ω) a)
    have hop := (prop_conc_resampled_limit_order (LE ω) (LF ω) hEs hEp hFs hFp m M hm hM).mp hordω
    refine ⟨⟨⟨_, hlimω.1⟩, ⟨_, hlimω.2⟩⟩, ?_⟩
    simp only [S3, Set.mem_iInter, Set.mem_setOf_eq]
    intro k
    have e1 : ellE k (field ω) = inner ℝ (u k) (LE ω (u k)) := hlimq (fun n => UE n (field ω)) _ k hlimω.1
    have e2 : ellF k (field ω) = inner ℝ (u k) (LF ω (u k)) := hlimq (fun n => UF n (field ω)) _ k hlimω.2
    rw [e1, e2]
    exact hop (u k)
  have hae := aux_prop_conc_weighted_identification_transfer_ae hfield ((hS1.inter hS2).inter hS3) hmem
  filter_upwards [hae] with x hx
  obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hx
  obtain ⟨GE, hGE⟩ := hx1
  obtain ⟨GF, hGF⟩ := hx2
  refine ⟨⟨GE, hGE⟩, ⟨GF, hGF⟩, ?_⟩
  have hlE : limUnder atTop (fun n => UE n x) = GE := hGE.limUnder_eq
  have hlF : limUnder atTop (fun n => UF n x) = GF := hGF.limUnder_eq
  rw [hlE, hlF]
  refine aux_prop_conc_resampled_limit_order_form_of_op GE GF m M hm hM (fun f => ?_)
  -- density
  have hc1 : IsClosed {f : DomainL2 Q | inner ℝ f (GF f) ≤ m⁻¹ * inner ℝ f (GE f)} :=
    isClosed_le (continuous_id.inner GF.continuous)
      (continuous_const.mul (continuous_id.inner GE.continuous))
  have hc2 : IsClosed {f : DomainL2 Q | M⁻¹ * inner ℝ f (GE f) ≤ inner ℝ f (GF f)} :=
    isClosed_le (continuous_const.mul (continuous_id.inner GE.continuous))
      (continuous_id.inner GF.continuous)
  have hclosed : IsClosed {f : DomainL2 Q | inner ℝ f (GF f) ≤ m⁻¹ * inner ℝ f (GE f) ∧
      M⁻¹ * inner ℝ f (GE f) ≤ inner ℝ f (GF f)} := hc1.inter hc2
  have hsub : Set.range u ⊆ {f : DomainL2 Q | inner ℝ f (GF f) ≤ m⁻¹ * inner ℝ f (GE f) ∧
      M⁻¹ * inner ℝ f (GE f) ≤ inner ℝ f (GF f)} := by
    rintro _ ⟨k, rfl⟩
    have h3 := Set.mem_iInter.mp hx3 k
    simp only [Set.mem_setOf_eq] at h3
    have e1 : ellE k x = inner ℝ (u k) (GE (u k)) := hlimq (fun n => UE n x) GE k hGE
    have e2 : ellF k x = inner ℝ (u k) (GF (u k)) := hlimq (fun n => UF n x) GF k hGF
    rw [e1, e2] at h3
    exact h3
  have hall : ∀ f, f ∈ {f : DomainL2 Q | inner ℝ f (GF f) ≤ m⁻¹ * inner ℝ f (GE f) ∧
      M⁻¹ * inner ℝ f (GE f) ≤ inner ℝ f (GF f)} := by
    intro f
    have := (hclosed.closure_subset_iff.mpr hsub)
    rw [hu.closure_range] at this
    exact this (Set.mem_univ f)
  exact hall f

end Order


section Main
variable {d : ℕ}

/-- The normalized affine response of the cutoff coefficient is a quadratic form in the slope. -/
theorem aux_prop_conc_resampled_canonical_setup_resp_quadratic
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (zcell : SpatialCoordinates d) (k : ℕ)
    (hPk : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
        (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity)),
      ‖(u : SobolevData
          (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity))).1‖ ≤
        K * ‖subspaceGradient
          (killedSobolevGraph
            (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity))) u‖)
    (N : ℕ) (om : BilateralField d) :
    ∃ A : Fin d → Fin d → ℝ, (∀ i j, A i j = A j i) ∧ ∀ e : Fin d → ℝ,
      aux_prop_conc_setup_resp model H zcell k hPk N om e =
        ∑ i : Fin d, ∑ j : Fin d, A i j * e i * e j := by
  obtain ⟨A, hAs, hA⟩ := aux_prop_conc_resampled_canonical_setup_dirichlet_quadratic
    (centeredCube_isBounded zcell (Real.rpow_pos_of_pos zero_lt_three ((-(k : ℝ)))))
    hPk (Lane4.cutoffPositiveCoefficient model H om N zcell
      (Real.rpow_pos_of_pos zero_lt_three ((-(k : ℝ)))))
  refine ⟨fun i j => A i j / (volume (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ)))
    (Real.rpow_pos_of_pos zero_lt_three _) : Set (SpatialCoordinates d))).toReal,
    fun i j => by simp only [hAs i j], fun e => ?_⟩
  unfold aux_prop_conc_setup_resp
  rw [hA e, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring


/-- The normalized affine response of the cutoff coefficient is measurable in the field. -/
theorem aux_prop_conc_resampled_canonical_setup_resp_measurable
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (zcell : SpatialCoordinates d) (k : ℕ)
    (hPk : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
        (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity)),
      ‖(u : SobolevData
          (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity))).1‖ ≤
        K * ‖subspaceGradient
          (killedSobolevGraph
            (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity))) u‖)
    (N : ℕ) (p : Fin d → ℝ) :
    Measurable (fun η : BilateralField d => aux_prop_conc_setup_resp model H zcell k hPk N η p) := by
  have h := (aux_prop_conc_weighted_identification_transfer_response_measurable model H hH N
    zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity) hPk p).div_const
    (volume (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity) :
      Set (SpatialCoordinates d))).toReal
  exact h

/-- **The setup of `prop_conc` at the canonical field space.**  A represented setup on `(Ω, P, field)` gives the setup on
`(BilateralField d, chaos, id)` with the same cells, cutoff subsequences and constants. -/
theorem prop_conc_resampled_canonical_setup
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GN : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ] DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ] DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (C0 m M : ℝ) (hC0 : 1 ≤ C0)
    (zcell : SpatialCoordinates d) (k : ℕ) (cellIdx paddedIdx : ℕ)
    (hPk : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
        (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity)),
      ‖(u : SobolevData
          (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity))).1‖ ≤
        K * ‖subspaceGradient
          (killedSobolevGraph
            (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity))) u‖)
    (AE AF : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hyps : prop_conc_setup d model H Ω P field z r hr Sspace GN GE GF NE NF C0 m M
      zcell k cellIdx paddedIdx hPk AE AF) :
    ∃ (GNc : (i : ℕ) → ℕ → BilateralField d →
        DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ] DomainL2 (centeredCube (z i) (r i) (hr i)))
      (GEc GFc : (i : ℕ) → BilateralField d →
        DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ] DomainL2 (centeredCube (z i) (r i) (hr i)))
      (AEc AFc : BilateralField d → Matrix (Fin d) (Fin d) ℝ),
      prop_conc_setup d model H (BilateralField d) (chaosSampleLaw model).toMeasure id z r hr Sspace
        GNc GEc GFc NE NF C0 m M zcell k cellIdx paddedIdx hPk AEc AFc := by
  classical
  obtain ⟨⟨hprob, hmeas, hmap, hIR, ⟨hNE, hNF⟩, hSall, hGNall, hlimall⟩, hCm, hord, hcellEq,
    hpadEq, hsymAE, hsymAF, hAE, hAF⟩ := hyps
  haveI : IsProbabilityMeasure P := hprob
  have hH : Measurable H := hIR.1
  have hfmp : MeasurePreserving field P (chaosSampleLaw model).toMeasure := ⟨hmeas, hmap⟩
  have hm : 0 < m := lt_of_lt_of_le (inv_pos.2 (by linarith)) hCm.1
  have hM : 0 < M := lt_of_lt_of_le hm hCm.2.1
  let GNc : (i : ℕ) → ℕ → BilateralField d →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ] DomainL2 (centeredCube (z i) (r i) (hr i)) :=
    fun i N η => volumeResponseOperator (Sspace i)
      (Lane4.cutoffPositiveCoefficient model H η N (z i) (hr i))
  have hGNeq : ∀ i N ω, GNc i N (field ω) = GN i N ω := by
    intro i N ω
    apply ContinuousLinearMap.ext
    intro f
    rw [hGNall i N ω f]
    exact volumeResponseOperator_apply (Sspace i) _ f
  have hGNsm : ∀ i N, StronglyMeasurable (GNc i N) := fun i N =>
    aux_prop_conc_weighted_identification_transfer_operator_measurable model H hH N (z i) (r i)
      (hr i) (Sspace i)
  have hsym : ∀ i N η a b, inner ℝ (GNc i N η a) b = inner ℝ a (GNc i N η b) := by
    intro i N η a b
    rw [real_inner_comm]
    exact volumeResponseOperator_symm (Sspace i) _ b a
  have hpos : ∀ i N η a, 0 ≤ inner ℝ a (GNc i N η a) := by
    intro i N η a
    change 0 ≤ inner ℝ a (volumeResponseOperator (Sspace i) _ a)
    rw [volumeResponseOperator_apply]
    exact volumeResponse_pairing_nonneg (Sspace i) _ a
  -- order and convergence at each cell
  have hordT : ∀ i, ∀ᵐ η ∂(chaosSampleLaw model).toMeasure,
      (∃ G, Tendsto (fun n => GNc i (NE n) η) atTop (𝓝 G)) ∧
      (∃ G, Tendsto (fun n => GNc i (NF n) η) atTop (𝓝 G)) ∧
      (limitFormDomain (limUnder atTop (fun n => GNc i (NE n) η)) =
          limitFormDomain (limUnder atTop (fun n => GNc i (NF n) η)) ∧
        ∀ u ∈ limitFormDomain (limUnder atTop (fun n => GNc i (NE n) η)),
          m * (limitFormEnergy (limUnder atTop (fun n => GNc i (NE n) η)) u).toReal ≤
            (limitFormEnergy (limUnder atTop (fun n => GNc i (NF n) η)) u).toReal ∧
          (limitFormEnergy (limUnder atTop (fun n => GNc i (NF n) η)) u).toReal ≤
            M * (limitFormEnergy (limUnder atTop (fun n => GNc i (NE n) η)) u).toReal) := by
    intro i
    refine aux_prop_conc_resampled_canonical_setup_order_transfer hfmp _
      (fun n η => GNc i (NE n) η) (fun n η => GNc i (NF n) η)
      (fun n => hGNsm i (NE n)) (fun n => hGNsm i (NF n))
      (fun n η a b => hsym i (NE n) η a b) (fun n η a => hpos i (NE n) η a)
      (fun n η a b => hsym i (NF n) η a b) (fun n η a => hpos i (NF n) η a)
      m M hm hM (GE i) (GF i) ?_ ?_
    · filter_upwards [hlimall] with ω hω
      exact ⟨(hω i).1.congr (fun n => (hGNeq i (NE n) ω).symm),
        (hω i).2.congr (fun n => (hGNeq i (NF n) ω).symm)⟩
    · filter_upwards [hord] with ω hω
      exact hω i
  have hall := ae_all_iff.mpr hordT
  refine ⟨GNc, fun i η => limUnder atTop (fun n => GNc i (NE n) η),
    fun i η => limUnder atTop (fun n => GNc i (NF n) η),
    fun η => aux_prop_conc_resampled_canonical_setup_polMat
      (fun p => limUnder atTop (fun n => aux_prop_conc_setup_resp model H zcell k hPk (NE n) η p)),
    fun η => aux_prop_conc_resampled_canonical_setup_polMat
      (fun p => limUnder atTop (fun n => aux_prop_conc_setup_resp model H zcell k hPk (NF n) η p)),
    ⟨inferInstance, measurable_id, Measure.map_id, hIR, ⟨hNE, hNF⟩, hSall,
      fun i N η f => volumeResponseOperator_apply (Sspace i) _ f, ?_⟩,
    hCm, ?_, hcellEq, hpadEq,
    fun η => aux_prop_conc_resampled_canonical_setup_polMat_symm _,
    fun η => aux_prop_conc_resampled_canonical_setup_polMat_symm _, ?_, ?_⟩
  · filter_upwards [hall] with η hη i
    exact ⟨tendsto_nhds_limUnder (hη i).1, tendsto_nhds_limUnder (hη i).2.1⟩
  · filter_upwards [hall] with η hη i
    exact (hη i).2.2
  · have hresp := aux_prop_conc_resampled_canonical_setup_matrix_transfer hfmp
      (fun n η p => aux_prop_conc_setup_resp model H zcell k hPk (NE n) η p)
      (fun n p => aux_prop_conc_resampled_canonical_setup_resp_measurable model H hH zcell k hPk
        (NE n) p)
      (fun n η => aux_prop_conc_resampled_canonical_setup_resp_quadratic model H zcell k hPk (NE n) η)
      AE hAE
    exact hresp
  · have hresp := aux_prop_conc_resampled_canonical_setup_matrix_transfer hfmp
      (fun n η p => aux_prop_conc_setup_resp model H zcell k hPk (NF n) η p)
      (fun n p => aux_prop_conc_resampled_canonical_setup_resp_measurable model H hH zcell k hPk
        (NF n) p)
      (fun n η => aux_prop_conc_resampled_canonical_setup_resp_quadratic model H zcell k hPk (NF n) η)
      AF hAF
    exact hresp

end Main

end
end Paper
