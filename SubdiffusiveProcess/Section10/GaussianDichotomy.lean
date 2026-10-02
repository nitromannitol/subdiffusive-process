import Mathlib
import SubdiffusiveProcess.Model.HeatSemigroupVec
import SubdiffusiveProcess.Section10.GaussianSupport
import SubdiffusiveProcess.Main.DiffusionPath
open MeasureTheory ProbabilityTheory Module Filter Topology
open SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace Paper

def aux_lim_nongaussian_covarianceForm {d : ℕ} (P : Measure (SpatialCoordinates d)) :
    LinearMap.BilinForm ℝ (StrongDual ℝ (SpatialCoordinates d)) :=
  (ContinuousLinearMap.coeLM ℝ).comp (covarianceBilinDual P).toLinearMap

theorem aux_lim_nongaussian_orthogonal_dual_basis {d : ℕ}
    (P : Measure (SpatialCoordinates d)) :
    ∃ b : Basis (Fin (Module.finrank ℝ (StrongDual ℝ (SpatialCoordinates d)))) ℝ
      (StrongDual ℝ (SpatialCoordinates d)),
      ∀ i j, i ≠ j → covarianceBilinDual P (b i) (b j) = 0 := by
  have hs : LinearMap.IsSymm (aux_lim_nongaussian_covarianceForm P) :=
    ⟨fun L K => covarianceBilinDual_comm (μ := P) L K⟩
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis hs
  exact ⟨b, fun i j hij => hb hij⟩

theorem aux_lim_nongaussian_strongDual_finrank {d : ℕ} :
    Module.finrank ℝ (StrongDual ℝ (SpatialCoordinates d)) = d := by
  calc _ = Module.finrank ℝ (Module.Dual ℝ (SpatialCoordinates d)) :=
      (LinearMap.toContinuousLinearMap :
        Module.Dual ℝ (SpatialCoordinates d) ≃ₗ[ℝ] StrongDual ℝ (SpatialCoordinates d)).finrank_eq.symm
    _ = d := by simp [Subspace.dual_finrank_eq, SpatialCoordinates]


theorem aux_lim_nongaussian_dual_basis_total
    {d : ℕ} {I : Type*} [Fintype I]
    (b : Basis I ℝ (StrongDual ℝ (SpatialCoordinates d)))
    (x : SpatialCoordinates d) (hx : ∀ i, b i x = 0) :
    x = 0 := by
  apply NormedSpace.eq_zero_of_forall_dual_eq_zero ℝ
  intro f
  rw [← Module.Basis.sum_repr b f]
  rw [ContinuousLinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  rw [ContinuousLinearMap.smul_apply, hx i, smul_zero]


theorem aux_lim_nongaussian_orthogonal_basis_fin {d : ℕ}
    (P : Measure (SpatialCoordinates d)) :
    ∃ b : Basis (Fin d) ℝ (StrongDual ℝ (SpatialCoordinates d)),
      ∀ i j, i ≠ j → covarianceBilinDual P (b i) (b j) = 0 := by
  obtain ⟨b, hb⟩ := aux_lim_nongaussian_orthogonal_dual_basis P
  let e := finCongr (aux_lim_nongaussian_strongDual_finrank (d := d))
  refine ⟨b.reindex e, ?_⟩
  intro i j hij
  simpa only [Basis.reindex_apply] using
    hb (e.symm i) (e.symm j) (fun h => hij (e.symm.injective h))

theorem aux_lim_nongaussian_basis_coordinates {d : ℕ}
    (b : Basis (Fin d) ℝ (StrongDual ℝ (SpatialCoordinates d))) :
    ∃ e : SpatialCoordinates d ≃L[ℝ] (Fin d → ℝ),
      ∀ x i, e x i = b i x := by
  let T : SpatialCoordinates d →L[ℝ] (Fin d → ℝ) := ContinuousLinearMap.pi (fun i => b i)
  have hinj : Function.Injective T := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply aux_lim_nongaussian_dual_basis_total b (x - y)
    intro i
    simp only [map_sub]
    exact sub_eq_zero.mpr (congr_fun hxy i)
  have hdim : Module.finrank ℝ (SpatialCoordinates d) = Module.finrank ℝ (Fin d → ℝ) := rfl
  have hsurj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  exact ⟨(LinearEquiv.ofBijective T.toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv,
    fun _ _ => rfl⟩


theorem aux_lim_nongaussian_real_comp {d : ℕ}
    (f : ℝ →L[ℝ] ℝ) (L : StrongDual ℝ (SpatialCoordinates d)) :
    f.comp L = (f 1) • L := by
  ext x
  simpa [smul_eq_mul, mul_comm] using f.map_smul (L x) (1 : ℝ)

theorem aux_lim_nongaussian_covariance_comp {d : ℕ}
    (P : Measure (SpatialCoordinates d))
    (L K : StrongDual ℝ (SpatialCoordinates d))
    (hLK : covarianceBilinDual P L K = 0) (f g : ℝ →L[ℝ] ℝ) :
    covarianceBilinDual P (f.comp L) (g.comp K) = 0 := by
  rw [aux_lim_nongaussian_real_comp, aux_lim_nongaussian_real_comp]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, hLK, mul_zero]

theorem aux_lim_nongaussian_dual_comp_coordinates {d : ℕ}
    (b : Fin d → StrongDual ℝ (SpatialCoordinates d))
    (e : SpatialCoordinates d ≃L[ℝ] (Fin d → ℝ)) (he : ∀ x i, e x i = b i x)
    (L : StrongDual ℝ (Fin d → ℝ)) :
    L.comp e.toContinuousLinearMap =
      ∑ i, (L.comp (ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i)).comp (b i) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.sum_apply]
  have h := ContinuousLinearMap.sum_comp_single ℝ (fun _ : Fin d => ℝ) L (e x)
  simpa only [he] using h.symm



theorem aux_lim_nongaussian_gaussian_pi_density
    {d : ℕ} (m : Fin d → ℝ) (v : Fin d → ℝ≥0) (hv : ∀ i, v i ≠ 0) :
    Measure.pi (fun i => gaussianReal (m i) (v i)) =
      (volume : Measure (Fin d → ℝ)).withDensity (fun y => ∏ i, gaussianPDF (m i) (v i) (y i)) := by
  refine Measure.pi_eq (fun s hs => ?_)
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), volume_pi, Measure.restrict_pi_pi]
  rw [SubdiffusiveProcess.Model.HeatSemigroupVec.lintegral_fin_prod_eq_prod
        (μ := fun i => (volume : Measure ℝ).restrict (s i))
        (f := fun i z => gaussianPDF (m i) (v i) z)
        (fun i => measurable_gaussianPDF (m i) (v i))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  exact (gaussianReal_apply (m i) (hv i) (s i)).symm



theorem aux_lim_nongaussian_gaussian_ac_equiv
    {d n : ℕ} (P : Measure (SpatialCoordinates d))
    (e : SpatialCoordinates d ≃L[ℝ] (Fin n → ℝ))
    (h : P.map e ≪ (volume : Measure (Fin n → ℝ))) :
    P ≪ (volume : Measure (SpatialCoordinates d)) := by
  have he : Measurable (DFunLike.coe e) := e.continuous.measurable
  have hes : Measurable (DFunLike.coe e.symm) := e.symm.continuous.measurable
  have hcomp : (DFunLike.coe e.symm) ∘ (DFunLike.coe e) = id := by
    funext x
    exact e.symm_apply_apply x
  have hP : (Measure.map (DFunLike.coe e) P).map (DFunLike.coe e.symm) = P := by
    rw [Measure.map_map hes he, hcomp, Measure.map_id]
  have hstep : (Measure.map (DFunLike.coe e) P).map (DFunLike.coe e.symm)
      ≪ (volume : Measure (Fin n → ℝ)).map (DFunLike.coe e.symm) :=
    h.map hes
  rw [hP] at hstep
  have hhaar : (Measure.map (DFunLike.coe e.symm) (volume : Measure (Fin n → ℝ))).IsAddHaarMeasure :=
    ContinuousLinearEquiv.isAddHaarMeasure_map e.symm (volume : Measure (Fin n → ℝ))
  have hvol : (volume : Measure (Fin n → ℝ)).map (DFunLike.coe e.symm)
      ≪ (volume : Measure (SpatialCoordinates d)) :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  exact hstep.trans hvol



theorem aux_lim_nongaussian_gaussian_variance_sum
    {d : ℕ} (P : Measure (SpatialCoordinates d)) [IsGaussian P]
    {I : Type*} [Fintype I] (L : I → StrongDual ℝ (SpatialCoordinates d))
    (horth : ∀ i j, i ≠ j → covarianceBilinDual P (L i) (L j) = 0) :
    Var[(∑ i, L i); P] = ∑ i, Var[L i; P] := by
    have hLp : MemLp id 2 P := IsGaussian.memLp_two_id
    have hfun : (∑ i, (⇑(L i) : SpatialCoordinates d → ℝ)) = ⇑(∑ i, L i) := by
      ext x
      simp only [Finset.sum_apply, ContinuousLinearMap.sum_apply]
    have hexpand : ((covarianceBilinDual P) (∑ i, L i)) (∑ i, L i)
        = ∑ i, ∑ j, ((covarianceBilinDual P) (L i)) (L j) := by
      rw [map_sum (covarianceBilinDual P) L Finset.univ]
      rw [ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_sum]
    rw [hfun, ← covarianceBilinDual_self_eq_variance hLp (∑ i, L i), hexpand]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i (fun b _ hb => horth i b (Ne.symm hb))
        (fun hi => absurd (Finset.mem_univ i) hi)]
    exact covarianceBilinDual_self_eq_variance hLp (L i)



theorem aux_lim_nongaussian_gaussian_charfun_sum
    {d : ℕ} (P : Measure (SpatialCoordinates d)) [IsGaussian P]
    {I : Type*} [Fintype I] (L : I → StrongDual ℝ (SpatialCoordinates d))
    (horth : ∀ i j, i ≠ j → covarianceBilinDual P (L i) (L j) = 0) :
    charFunDual P (∑ i, L i) = ∏ i, charFunDual P (L i) := by
  have hsum : (⇑(∑ i, L i) : SpatialCoordinates d → ℝ) = ∑ i, ⇑(L i) := by
    ext x
    simp only [ContinuousLinearMap.sum_apply, Finset.sum_apply]
  have hvar := aux_lim_nongaussian_gaussian_variance_sum P L horth
  have hint : (∫ x, (↑((∑ i, L i) x) : ℂ) ∂P) = ∑ i, ∫ x, (↑(L i x) : ℂ) ∂P := by
    have h1 : (fun x => (↑((∑ i, L i) x) : ℂ)) = fun x => ∑ i, (↑(L i x) : ℂ) := by
      ext x
      simp only [ContinuousLinearMap.sum_apply, Complex.ofReal_sum]
    rw [h1, integral_finset_sum]
    exact fun i _ => (IsGaussian.integrable_dual P (L i)).ofReal
  have h2 : (↑Var[⇑(∑ i, L i); P] : ℂ) = ∑ i, (↑Var[⇑(L i); P] : ℂ) := by
    rw [hsum, hvar, Complex.ofReal_sum]
  have harg : (∫ x, (↑((∑ i, L i) x) : ℂ) ∂P) * Complex.I
      - ↑Var[⇑(∑ i, L i); P] / 2
      = ∑ i, ((∫ x, (↑(L i x) : ℂ) ∂P) * Complex.I - ↑Var[⇑(L i); P] / 2) := by
    rw [hint, h2, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_div]
  rw [IsGaussian.charFunDual_eq]
  rw [show (∏ i, charFunDual P (L i))
        = ∏ i, Complex.exp ((∫ x, (↑(L i x) : ℂ) ∂P) * Complex.I - ↑Var[⇑(L i); P] / 2) from
      Finset.prod_congr rfl (fun i _ => IsGaussian.charFunDual_eq (L i))]
  rw [← Complex.exp_sum, harg]


theorem aux_lim_nongaussian_map_coordinates_product {d : ℕ}
    (P : Measure (SpatialCoordinates d)) [IsGaussian P]
    (b : Fin d → StrongDual ℝ (SpatialCoordinates d))
    (horth : ∀ i j, i ≠ j → covarianceBilinDual P (b i) (b j) = 0)
    (e : SpatialCoordinates d ≃L[ℝ] (Fin d → ℝ)) (he : ∀ x i, e x i = b i x) :
    P.map e = Measure.pi (fun i => P.map (b i)) := by
  apply charFunDual_eq_pi_iff.mp
  intro L
  change charFunDual (P.map e.toContinuousLinearMap) L = _
  rw [charFunDual_map, aux_lim_nongaussian_dual_comp_coordinates b e he L,
    aux_lim_nongaussian_gaussian_charfun_sum P _ (fun i j hij =>
      aux_lim_nongaussian_covariance_comp P (b i) (b j) (horth i j hij) _ _)]
  exact Finset.prod_congr rfl (fun i _ => (charFunDual_map (b i) _).symm)

theorem aux_lim_nongaussian_gaussian_nondegenerate_ac {d : ℕ}
    (P : Measure (SpatialCoordinates d)) [IsGaussian P]
    (hvar : ∀ L : StrongDual ℝ (SpatialCoordinates d), L ≠ 0 → 0 < Var[L; P]) :
    P ≪ (volume : Measure (SpatialCoordinates d)) := by
  obtain ⟨b, horth⟩ := aux_lim_nongaussian_orthogonal_basis_fin P
  obtain ⟨e, he⟩ := aux_lim_nongaussian_basis_coordinates b
  apply aux_lim_nongaussian_gaussian_ac_equiv P e
  rw [aux_lim_nongaussian_map_coordinates_product P b horth e he]
  simp_rw [IsGaussian.map_eq_gaussianReal]
  rw [aux_lim_nongaussian_gaussian_pi_density _ _ (fun i =>
    ne_of_gt (Real.toNNReal_pos.mpr (hvar (b i) (b.ne_zero i))))]
  exact withDensity_absolutelyContinuous _ _

theorem aux_lim_nongaussian_gaussian_dichotomy {d : ℕ}
    (P : Measure (SpatialCoordinates d)) [IsGaussian P] :
    (P ≪ volume) ∨ ∃ L : StrongDual ℝ (SpatialCoordinates d), L ≠ 0 ∧
      ∃ a : ℝ, P {x | L x ≠ a} = 0 := by
  by_cases h : ∀ L : StrongDual ℝ (SpatialCoordinates d), L ≠ 0 → 0 < Var[L; P]
  · exact Or.inl (aux_lim_nongaussian_gaussian_nondegenerate_ac P h)
  · push_neg at h
    obtain ⟨L, hL, hv⟩ := h
    exact Or.inr ⟨L, hL, ∫ x, L x ∂P,
      aux_lim_nongaussian_gaussian_zero_variance P L (le_antisymm hv (variance_nonneg _ _))⟩


end Paper
