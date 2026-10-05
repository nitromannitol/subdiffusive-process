module

public import SubdiffusiveProcess.LambdaStability.FieldAdapters

@[expose] public section

/-! The literal scalar response probes used by the symmetric paper. -/
open Homogenization Homogenization.Book MeasureTheory
open scoped BigOperators

noncomputable section
namespace SubdiffusiveProcess.LambdaStability
variable {d : ℕ} [NeZero d]

/-- The scalar unit-sphere response maximum with fixed load maps. -/
def probeMax (U : Set (Vec d)) (g : CoeffField d) (B A : Mat d) : ℝ :=
  sSup {y : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
    y = ResponseJ U (matVecMul B e) (matVecMul A e) g}

theorem probeSet_nonempty (U : Set (Vec d)) (g : CoeffField d) (B A : Mat d) :
    {y : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
      y = ResponseJ U (matVecMul B e) (matVecMul A e) g}.Nonempty := by
  classical
  let i : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  refine ⟨_, Pi.single i 1, ?_, rfl⟩
  rw [vecNormSq, vecDot, Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    rw [Pi.single_eq_of_ne hji]
    ring
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

omit [NeZero d] in
theorem probeMax_nonneg (U : Set (Vec d)) (g : CoeffField d) (B A : Mat d) :
    0 ≤ probeMax U g B A := by
  apply Real.sSup_nonneg
  rintro y ⟨e, _, rfl⟩
  exact Homogenization.responseJ_nonneg U _ _ g

/-- The uniform bound needed to justify all response series. -/
def probeBound (lam Lam : ℝ) (B A : Mat d) : ℝ :=
  lam⁻¹ * (Lam ^ 2 * Ch02.matrixOperatorNorm B ^ 2 + Ch02.matrixOperatorNorm A ^ 2)

omit [NeZero d] in
theorem probeResponse_le_bound (U : Ch02.Domain d) {g : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) g) (B A : Mat d)
    (e : Vec d) (he : vecNormSq e = 1) :
    ResponseJ U (matVecMul B e) (matVecMul A e) g ≤ probeBound lam Lam B A := by
  unfold ResponseJ
  refine csSup_le (responseJValueSet_nonempty _ _ _ _) ?_
  rintro y ⟨u, rfl⟩
  have hraw : volumeAverage U (scalarResponseIntegrand U g (matVecMul B e) (matVecMul A e) u) ≤
      lam⁻¹ * (Lam ^ 2 * vecNormSq (matVecMul B e) + vecNormSq (matVecMul A e)) := by
    exact volumeAverage_le_of_le_on U.measurableSet
      (scalarResponseIntegrand_integrableOn_of_isEllipticFieldOn hEll _ _ u)
      (Homogenization.Internal.Ch02.BookCh02.domain_volume_pos U).ne'
      (scalarResponseIntegrand_le_plainUpperBound_of_isEllipticFieldOn hEll _ _ u)
  have hlam : 0 < lam := (coeffOn U g hEll).lam_pos
  have hp := Ch02.vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq B e
  have hq := Ch02.vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq A e
  rw [he, mul_one] at hp hq
  refine hraw.trans ?_
  unfold probeBound
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hlam.le)
  exact add_le_add (mul_le_mul_of_nonneg_left hp (sq_nonneg Lam)) hq

theorem probeMax_le_bound (U : Ch02.Domain d) {g : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) g) (B A : Mat d) :
    probeMax U g B A ≤ probeBound lam Lam B A := by
  apply csSup_le (probeSet_nonempty _ _ _ _)
  rintro y ⟨e, he, rfl⟩
  exact probeResponse_le_bound U hEll B A e he

omit [NeZero d] in
theorem probeResponse_le_max (U : Ch02.Domain d) {g : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) g) (B A : Mat d)
    (e : Vec d) (he : vecNormSq e = 1) :
    ResponseJ U (matVecMul B e) (matVecMul A e) g ≤ probeMax U g B A := by
  apply le_csSup
  · exact ⟨probeBound lam Lam B A, by rintro y ⟨v, hv, rfl⟩; exact probeResponse_le_bound U hEll B A v hv⟩
  · exact ⟨e, he, rfl⟩

def probeShell (w : Vec d) (P : TriadicCube d) (k : ℤ) (g : CoeffField d) (B A : Mat d) : ℝ :=
  Ch02.finsetSupReal (descendantsAtScale P k)
    (fun R => probeMax (translateSet w (openCubeSet R)) g B A)

def translatedDomain (w : Vec d) (P : TriadicCube d) : Ch02.Domain d where
  carrier := translateSet w (openCubeSet P)
  isDomain := (isOpenBoundedConvexDomain_openCubeSet P).translateSet w
  nonempty := by
    obtain ⟨x, hx⟩ := Ch02.openCubeSet_nonempty P
    exact ⟨w + x, mem_translateSet_iff_sub_mem.2 (by simpa using hx)⟩

omit [NeZero d] in
theorem probeShell_nonneg (w : Vec d) (P : TriadicCube d) (k : ℤ)
    (g : CoeffField d) (B A : Mat d) : 0 ≤ probeShell w P k g B A :=
  Ch02.finsetSupReal_nonneg _ _ (fun _ _ => probeMax_nonneg _ _ _ _)

theorem probeShell_le_bound (w : Vec d) (P : TriadicCube d) {k : ℤ} (hk : k ≤ P.scale)
    {g : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam Set.univ g)
    (B A : Mat d) : probeShell w P k g B A ≤ probeBound lam Lam B A := by
  apply Ch02.finsetSupReal_le _ (descendantsAtScale_nonempty P hk)
  intro R _
  exact probeMax_le_bound (translatedDomain w R)
    (hEll.mono (translatedDomain w R).measurableSet (Set.subset_univ _)) B A

/-- Subadditivity bounds a grid response maximum by any finer shell in the root. -/
theorem probeMax_le_gridShell {K R : TriadicCube d} {k : ℤ}
    {g : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam Set.univ g)
    (B A : Mat d) (hR : R ∈ descendantsAtScale K R.scale) (hk : k ≤ R.scale) :
    probeMax (openCubeSet R) g B A ≤ probeShell 0 K k g B A := by
  classical
  have hRK : R.scale ≤ K.scale := scale_le_of_mem_descendantsAtScale hR
  have hkK := hk.trans hRK
  let j : ℕ := (R.scale - k).toNat
  have hj : R.scale - (j : ℤ) = k := by dsimp [j]; omega
  have hEllR := hEll.mono (measurableSet_openCubeSet R) (Set.subset_univ _)
  apply csSup_le (probeSet_nonempty _ _ _ _)
  rintro y ⟨e, he, rfl⟩
  have hsub := responseJ_subadditive_openCubeSet_descendantsAtDepth_of_isEllipticFieldOn
    j R g hEllR (matVecMul B e) (matVecMul A e)
  refine hsub.trans ?_
  have hcell : ∀ S ∈ descendantsAtDepth R j,
      ResponseJ (openCubeSet S) (matVecMul B e) (matVecMul A e) g ≤ probeShell 0 K k g B A := by
    intro S hS
    have hSk : S ∈ descendantsAtScale R k := by
      rw [descendantsAtScale_eq_descendantsAtDepth R hk]
      exact hS
    have hSK := mem_descendantsAtScale_trans hR hSk
    have hresp := probeResponse_le_max (Ch02.cubeDomain S)
      (hEll.mono (measurableSet_openCubeSet S) (Set.subset_univ _)) B A e he
    refine hresp.trans ?_
    unfold probeShell Ch02.finsetSupReal
    apply le_csSup ((Set.toFinite _).image _).bddAbove
    exact ⟨S, hSK, by simp only [translateSet_zero, Ch02.cubeDomain_coe]⟩
  have havg := descendantsAverage_le_descendantsAverage R j hcell
  have hconst : descendantsAverage R j (fun _ => probeShell 0 K k g B A) =
      probeShell 0 K k g B A := by
    unfold descendantsAverage
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((descendantsAtDepth R j).card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr (descendantsAtDepth_nonempty R j)
    rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]
  exact havg.trans_eq hconst

theorem probeShell_monotone (K : TriadicCube d) {g : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam Set.univ g) (B A : Mat d) :
    Monotone (fun l : ℕ => probeShell 0 K (K.scale - (l : ℤ)) g B A) := by
  intro m n hmn
  unfold probeShell
  apply Ch02.finsetSupReal_le _ (descendantsAtScale_nonempty K (by omega))
  intro R hR
  rw [translateSet_zero]
  have hscale := descendant_scale_eq_of_mem_descendantsAtScale hR
  apply probeMax_le_gridShell hEll B A
  · simpa only [hscale] using hR
  · omega

end SubdiffusiveProcess.LambdaStability
