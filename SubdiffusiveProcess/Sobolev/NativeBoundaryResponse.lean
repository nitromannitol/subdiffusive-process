import SubdiffusiveProcess.Lane2.NativeBridge
import SubdiffusiveProcess.Lane2.BoundaryResponse
import SubdiffusiveProcess.Sobolev.AffineResponses

/-! Identify the native boundary-energy infimum with the finite-cutoff
Sobolev Dirichlet response. These identities concern one positive coefficient;
they do not assert convergence of limiting forms or boundary minimizers. -/

open MeasureTheory Set TopologicalSpace Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal BigOperators

namespace SubdiffusiveProcess
noncomputable section

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

/-- Native Sobolev addition agrees with addition of the function and gradient data. -/
theorem sobolevDataOfH1_add (u v : H1Function (Q : Set (SpatialCoordinates d))) :
    sobolevDataOfH1 (u + v) = sobolevDataOfH1 u + sobolevDataOfH1 v := by
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [sobolevDataOfH1_fst_coeFn (u + v),
      sobolevDataOfH1_fst_coeFn u, sobolevDataOfH1_fst_coeFn v,
      Lp.coeFn_add (sobolevDataOfH1 u).1 (sobolevDataOfH1 v).1] with x huv hu hv hadd
    exact huv.trans (by
      change u.toFun x + v.toFun x = ((sobolevDataOfH1 u).1 + (sobolevDataOfH1 v).1) x
      rw [hadd, Pi.add_apply, hu, hv])
  · funext i
    apply Lp.ext
    filter_upwards [sobolevDataOfH1_snd_coeFn (u + v) i,
      sobolevDataOfH1_snd_coeFn u i, sobolevDataOfH1_snd_coeFn v i,
      Lp.coeFn_add ((sobolevDataOfH1 u).2 i) ((sobolevDataOfH1 v).2 i)] with x huv hu hv hadd
    exact huv.trans (by
      change u.grad x i + v.grad x i =
        ((sobolevDataOfH1 u).2 i + (sobolevDataOfH1 v).2 i) x
      rw [hadd, Pi.add_apply, hu, hv])

/-- Pointwise equality of the native functions and gradients gives equality of Sobolev data. -/
theorem sobolevDataOfH1_eq_of_representatives
    (u v : H1Function (Q : Set (SpatialCoordinates d)))
    (hfun : ∀ x, u.toFun x = v.toFun x) (hgrad : ∀ x, u.grad x = v.grad x) :
    sobolevDataOfH1 u = sobolevDataOfH1 v := by
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [sobolevDataOfH1_fst_coeFn u, sobolevDataOfH1_fst_coeFn v] with x hu hv
    exact hu.trans ((hfun x).trans hv.symm)
  · funext i
    apply Lp.ext
    filter_upwards [sobolevDataOfH1_snd_coeFn u i, sobolevDataOfH1_snd_coeFn v i] with x hu hv
    exact hu.trans ((congrFun (hgrad x) i).trans hv.symm)

/-- A native representative of a killed Sobolev datum recovers the same datum. -/
theorem sobolevDataOfH1_native_killed
    (w : killedSobolevGraph Q) (v : H10Function (Q : Set (SpatialCoordinates d)))
    (hfun : v.toH1Function.toFun = fun x => w.val.1 x)
    (hgrad : v.toH1Function.grad = fun x i => w.val.2 i x) :
    sobolevDataOfH1 v.toH1Function = w.val := by
  apply Prod.ext
  · apply Lp.ext
    exact (sobolevDataOfH1_fst_coeFn v.toH1Function).trans (by rw [hfun])
  · funext i
    apply Lp.ext
    exact (sobolevDataOfH1_snd_coeFn v.toH1Function i).trans (by rw [hgrad])

/-- The native scalar energy equals the Sobolev coefficient form without normalization. -/
theorem energy_eq_sobolevCoefficientForm
    (a : PositiveCoefficient Q) (c : SpatialCoordinates d → ℝ)
    (hc : (fun x => a.val x) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] c)
    (u : H1Function (Q : Set (SpatialCoordinates d))) :
    energy c (Q : Set (SpatialCoordinates d)) u =
      sobolevCoefficientForm a (sobolevDataOfH1 u) (sobolevDataOfH1 u) := by
  rw [Lane4.sobolevCoefficientForm_eq_upstream_integral a c hc]
  apply integral_congr_ae
  have hgrad := ae_all_iff.mpr (fun i => sobolevDataOfH1_snd_coeFn u i)
  filter_upwards [hgrad] with x hx
  rw [Lane4.vecDot_matVecMul_scalarCoeffField]
  exact congrArg (c x * ·) (congrArg₂ vecDot (funext hx).symm (funext hx).symm)

/-- Native zero-trace competitors and killed Sobolev competitors have the same energy values. -/
theorem native_boundary_energy_set_eq
    (a : PositiveCoefficient Q) (c : SpatialCoordinates d → ℝ)
    (hc : (fun x => a.val x) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] c)
    (beta : H1Function (Q : Set (SpatialCoordinates d))) :
    {e : ℝ | ∃ u : H1Function (Q : Set (SpatialCoordinates d)),
      HasZeroTraceDifferenceOn (Q : Set (SpatialCoordinates d)) u beta ∧
        e = energy c (Q : Set (SpatialCoordinates d)) u} =
      Set.range (fun w : killedSobolevGraph Q =>
        sobolevCoefficientForm a (sobolevDataOfH1 beta + w.val)
          (sobolevDataOfH1 beta + w.val)) := by
  ext e
  constructor
  · rintro ⟨u, ⟨v, hvfun, hvgrad⟩, rfl⟩
    let w : killedSobolevGraph Q := ⟨sobolevDataOfH1 v.toH1Function,
      sobolevDataOfH1_mem_killed v⟩
    refine ⟨w, ?_⟩
    have hu : sobolevDataOfH1 u = sobolevDataOfH1 beta + w.val := by
      rw [← sobolevDataOfH1_add]
      exact sobolevDataOfH1_eq_of_representatives u (beta + v.toH1Function) hvfun hvgrad
    rw [energy_eq_sobolevCoefficientForm a c hc, hu]
  · rintro ⟨w, rfl⟩
    obtain ⟨v, hvfun, hvgrad⟩ := exists_nativeH10Function_of_killedSobolevGraph w
    refine ⟨beta + v.toH1Function, ⟨v, (fun _ => rfl), (fun _ => rfl)⟩, ?_⟩
    rw [energy_eq_sobolevCoefficientForm a c hc, sobolevDataOfH1_add,
      sobolevDataOfH1_native_killed w v hvfun hvgrad]

/-- The native cell infimum is exactly the response for its native Sobolev datum. -/
theorem cellDirichletInfimum_eq_dirichletResponse
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph Q,
      ‖w.val.1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Q) w‖)
    (a : PositiveCoefficient Q) (c : SpatialCoordinates d → ℝ)
    (hc : (fun x => a.val x) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] c)
    (beta : H1Function (Q : Set (SpatialCoordinates d))) :
    cellDirichletInfimum c (Q : Set (SpatialCoordinates d)) beta =
      dirichletResponse (killedResponseSpace hP) a
        ⟨sobolevDataOfH1 beta, sobolevDataOfH1_mem_weak beta⟩ := by
  rw [cellDirichletInfimum, native_boundary_energy_set_eq a c hc beta]
  exact (dirichletResponse_isLeast (killedResponseSpace hP) a
    ⟨sobolevDataOfH1 beta, sobolevDataOfH1_mem_weak beta⟩).csInf_eq

variable [IsFiniteMeasure (volume.restrict (Q : Set (SpatialCoordinates d)))]

/-- A native datum equal almost everywhere to an affine function has its affine Sobolev data. -/
theorem sobolevDataOfH1_eq_affine_of_ae
    (hQ : Bornology.IsBounded (Q : Set (SpatialCoordinates d)))
    (beta : H1Function (Q : Set (SpatialCoordinates d))) (p : Fin d → ℝ) (b : ℝ)
    (hbeta : beta.toFun =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
      fun x => affineSlope p x + b) :
    sobolevDataOfH1 beta = affineSobolevData hQ p b := by
  have hf : (sobolevDataOfH1 beta).1 = (affineSobolevData hQ p b).1 :=
    Lp.ext ((sobolevDataOfH1_fst_coeFn beta).trans
      (hbeta.trans (affineL2_coeFn hQ p b).symm))
  apply Prod.ext hf
  apply weakSobolevGraph_gradient_unique (u := (affineSobolevData hQ p b).1)
  · rw [← hf]
    exact sobolevDataOfH1_mem_weak beta
  · exact affineSobolevData_mem hQ p b

/-- The native infimum for an affine datum is the actual affine Dirichlet response. -/
theorem cellDirichletInfimum_eq_affineDirichletResponse
    (hQ : Bornology.IsBounded (Q : Set (SpatialCoordinates d)))
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph Q,
      ‖w.val.1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Q) w‖)
    (a : PositiveCoefficient Q) (c : SpatialCoordinates d → ℝ)
    (hc : (fun x => a.val x) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] c)
    (beta : H1Function (Q : Set (SpatialCoordinates d))) (p : Fin d → ℝ)
    (hbeta : beta.toFun =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
      fun x => ∑ i, p i * x i) :
    cellDirichletInfimum c (Q : Set (SpatialCoordinates d)) beta =
      affineDirichletResponse hQ hP a p := by
  have hb : (⟨sobolevDataOfH1 beta, sobolevDataOfH1_mem_weak beta⟩ : weakSobolevGraph Q) =
      affineSobolev hQ p 0 := by
    apply Subtype.ext
    exact sobolevDataOfH1_eq_affine_of_ae hQ beta p 0
      (by simpa only [affineSlope_apply, add_zero] using hbeta)
  rw [cellDirichletInfimum_eq_dirichletResponse hP a c hc beta, hb]
  rfl

end
end SubdiffusiveProcess

