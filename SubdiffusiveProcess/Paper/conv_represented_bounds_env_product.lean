module

public import SubdiffusiveProcess.Paper.prop_regularity_product_limit
public import SubdiffusiveProcess.Paper.inputs_classical_bounded_h10_h1_product
public import SubdiffusiveProcess.VariationalResponses.NativeBridge
public import SubdiffusiveProcess.EllipticRegularity.Bridge
public import SubdiffusiveProcess.VariationalResponses.MeshGeometry
public import SubdiffusiveProcess.Geometry.Cube

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

variable {d : ℕ} {z : SpatialCoordinates d} {R : ℝ} {hR : 0 < R}
variable {Q : Opens (SpatialCoordinates d)}

/-- The root-uniform cutoff supplier returns an `H¹` representative and a response-space
representative. Convert its exact Sobolev-data identity and profile equality to the a.e. profile
equality required by the native product input. -/
theorem aux_conv_represented_bounds_env_product_root_cutoff_profile_ae
    (S : ResponseSpace Q)
    (v : ℕ → H1Function (Q : Set (SpatialCoordinates d)))
    (vS : ℕ → S.space)
    (profile : ℕ → SpatialCoordinates d → ℝ)
    (hS : ∀ n, (vS n).val = sobolevDataOfH1 (v n))
    (hprofile : ∀ n,
      (vS n).val.1 =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] profile n) :
    ∀ n, (v n).toFun =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] profile n := by
  intro n
  have hrepr := hprofile n
  rw [hS n] at hrepr
  exact (sobolevDataOfH1_fst_coeFn (v n)).symm.trans hrepr

/-- **Paper-specific O5b supplier for the represented-bounds field `hW`.**

For each catalogue source, the actual finite-cutoff solution is in the killed response space and
has the existing uniform Hölder representative bound. A native `H¹` collar cutoff with its
root-uniform `[0,1]` representative is multiplied by that solution using the explicitly frozen
classical O5b input. The product is returned in `S.space` and its value is the `hW`
representative used by `prop_regularity_product_limit`. Off the catalogue, the total family `w`
uses the original response solution; the bundle constrains `hW` only on `D`. -/
theorem conv_represented_bounds_env_product
    {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (hS : S.space = killedSobolevGraph (centeredCube z R hR))
    (a : ℕ → PositiveCoefficient (centeredCube z R hR))
    (D : Submodule ℚ (DomainL2 (centeredCube z R hR)))
    (u : DomainL2 (centeredCube z R hR) → ℕ → S.space)
    (uc : DomainL2 (centeredCube z R hR) → ℕ → SpatialCoordinates d → ℝ)
    (hU : ∀ (f : DomainL2 (centeredCube z R hR)) (n : ℕ),
      u f n = responseSolution S (a n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL))
    (hUrep : ∀ (f : DomainL2 (centeredCube z R hR)) (n : ℕ),
      (u f n).val.1
        =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] uc f n)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hUholder : ∀ f : D, ∃ Kf : ℝ, 0 ≤ Kf ∧ ∀ n : ℕ,
      ContinuousOn (uc f.val n)
        (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
      _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
        (closure (centeredCube z R hR : Set (SpatialCoordinates d))) (uc f.val n) ∧
      _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
        (closure (centeredCube z R hR : Set (SpatialCoordinates d))) (uc f.val n) ≤ Kf ∧
      ∀ x ∈ frontier (centeredCube z R hR : Set (SpatialCoordinates d)),
        uc f.val n x = 0)
    (v : ℕ → ℕ → H1Function
      (centeredCube z R hR : Set (SpatialCoordinates d)))
    (chi : ℕ → ℕ → SpatialCoordinates d → ℝ)
    (hv : ∀ k n,
      (v k n).toFun =ᵐ[volume.restrict
        (centeredCube z R hR : Set (SpatialCoordinates d))] chi k n)
    (hchiRange : ∀ k n, ∀ x ∈ closure
        (centeredCube z R hR : Set (SpatialCoordinates d)),
      0 ≤ chi k n x ∧ chi k n x ≤ 1) :
    ∃ un : D → ℕ → H10Function (centeredCube z R hR : Set (SpatialCoordinates d)),
      (∀ (f : D) (n : ℕ),
        (un f n).toH1Function.toFun
          =ᵐ[volume.restrict
            (centeredCube z R hR : Set (SpatialCoordinates d))] uc f.val n) ∧
      (∀ (f : D) (n : ℕ) (i : Fin d),
        (fun x => (un f n).toH1Function.grad x i)
          =ᵐ[volume.restrict
            (centeredCube z R hR : Set (SpatialCoordinates d))]
            (fun x =>
              (responseSolution S (a n)
                ((sobolevVolumeLoad f.val).comp S.space.subtypeL)).val.2 i x)) ∧
      ∃ w : DomainL2 (centeredCube z R hR) → ℕ → ℕ → S.space,
        (∀ (f : D) (k n : ℕ),
          ((w f.val k n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict
              (centeredCube z R hR : Set (SpatialCoordinates d))]
              (fun x => uc f.val n x * chi k n x)) ∧
        (∀ (f : D) (k n : ℕ) (i : Fin d),
          ((w f.val k n).val.2 i : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict
              (centeredCube z R hR : Set (SpatialCoordinates d))]
              (fun x =>
                (un f n).toH1Function.toFun x * (v k n).grad x i +
                  (v k n).toFun x * (un f n).toH1Function.grad x i)) := by
  classical
  let Qc : Set (SpatialCoordinates d) := centeredCube z R hR
  let μ : Measure (SpatialCoordinates d) := volume.restrict Qc
  have hdom : IsOpenBoundedConvexDomain Qc := by
    refine ⟨(centeredCube z R hR).isOpen,
      (centeredCube_isBounded z hR).isBoundedDomain, convex_ball z (R / 2)⟩
  have hNative : ∀ (f : D) (n : ℕ),
      ∃ un : H10Function Qc,
        un.toH1Function.toFun =ᵐ[μ] uc f.val n ∧
        ∀ i : Fin d,
          (fun x => un.toH1Function.grad x i) =ᵐ[μ]
            (fun x =>
              (responseSolution S (a n)
                ((sobolevVolumeLoad f.val).comp S.space.subtypeL)).val.2 i x) := by
    intro f n
    let sol : S.space := responseSolution S (a n)
      ((sobolevVolumeLoad f.val).comp S.space.subtypeL)
    have hkill : sol.val ∈ killedSobolevGraph (centeredCube z R hR) := by
      rw [← hS]
      exact sol.property
    let ks : killedSobolevGraph (centeredCube z R hR) := ⟨sol.val, hkill⟩
    obtain ⟨un, hval, hgrad⟩ :=
      exists_nativeH10Function_of_killedSobolevGraph ks
    have hvalAE : un.toH1Function.toFun =ᵐ[μ] sol.val.1 := by
      filter_upwards [] with x
      exact congrFun hval x
    have hrepSol : sol.val.1 =ᵐ[μ] uc f.val n := by
      have h := hUrep f.val n
      rw [hU f.val n] at h
      exact h
    refine ⟨un, hvalAE.trans hrepSol, ?_⟩
    intro i
    filter_upwards [] with x
    change un.toH1Function.grad x i = sol.val.2 i x
    exact congrFun (congrFun hgrad x) i
  choose un hunval hungrad using hNative
  have hProd : ∀ (f : D) (k n : ℕ),
      ∃ p : H10Function Qc,
        p.toH1Function.toFun =ᵐ[μ]
          (fun x => (un f n).toH1Function.toFun x * (v k n).toFun x) ∧
        ∀ i : Fin d,
          (fun x => p.toH1Function.grad x i) =ᵐ[μ]
            (fun x =>
              (un f n).toH1Function.toFun x * (v k n).grad x i +
                (v k n).toFun x * (un f n).toH1Function.grad x i) := by
    intro f k n
    obtain ⟨Kf, hKf, hK⟩ := hUholder f
    rcases hK n with ⟨hcont, hholder, hnorm, hfront⟩
    have hboundData := aux_prop_regularity_product_limit_holder_data
      (lane2_isCompact_closure_centeredCube z hR) hcont hholder hnorm halpha
    have huBound : ∀ᵐ x ∂μ, |(un f n).toH1Function.toFun x| ≤ Kf := by
      filter_upwards [hunval f n,
        ae_restrict_mem (centeredCube z R hR).isOpen.measurableSet] with x hrep hx
      rw [hrep]
      exact hboundData.1 x (subset_closure hx)
    have hvBound : ∀ᵐ x ∂μ, |(v k n).toFun x| ≤ 1 := by
      filter_upwards [hv k n,
        ae_restrict_mem (centeredCube z R hR).isOpen.measurableSet] with x hrep hx
      rw [hrep]
      have hrange := hchiRange k n x (subset_closure hx)
      rw [abs_le]
      exact ⟨by linarith, hrange.2⟩
    exact inputs_classical_bounded_h10_h1_product hdom (un f n) (v k n)
      hKf (by norm_num) huBound hvBound
  choose p hpval hpgrad using hProd
  have hGraph : ∀ (f : D) (k n : ℕ),
      ∃ g : killedSobolevGraph (centeredCube z R hR),
        g.val.1 =ᵐ[μ] (p f k n : SpatialCoordinates d → ℝ) ∧
        ∀ i : Fin d,
          (fun x => g.val.2 i x) =ᵐ[μ]
            (fun x => p f k n |>.toH1Function.grad x i) := by
    intro f k n
    exact _root_.SubdiffusiveProcess.EllipticRegularity.exists_killedSobolevGraph_of_nativeH10 (p f k n)
  choose g hgval hggrad using hGraph
  let embed : killedSobolevGraph (centeredCube z R hR) → S.space := fun g =>
    ⟨g.val, by
      rw [hS]
      exact g.property⟩
  let w : DomainL2 (centeredCube z R hR) → ℕ → ℕ → S.space := fun f k n =>
    if hf : f ∈ D then embed (g ⟨f, hf⟩ k n) else u f n
  refine ⟨un, hunval, hungrad, w, ?_, ?_⟩
  · intro f k n
    have hw : w f.val k n = embed (g f k n) := by
      simp [w, f.property]
    rw [hw]
    change (g f k n).val.1 =ᵐ[μ] (fun x => uc f.val n x * chi k n x)
    calc
      (g f k n).val.1 =ᵐ[μ] (p f k n : SpatialCoordinates d → ℝ) := hgval f k n
      _ =ᵐ[μ] (fun x => (un f n).toH1Function.toFun x * (v k n).toFun x) :=
        hpval f k n
      _ =ᵐ[μ] (fun x => uc f.val n x * chi k n x) :=
        (hunval f n).mul (hv k n)
  · intro f k n i
    have hw : w f.val k n = embed (g f k n) := by
      simp [w, f.property]
    rw [hw]
    change (fun x => (g f k n).val.2 i x) =ᵐ[μ]
      (fun x =>
        (un f n).toH1Function.toFun x * (v k n).grad x i +
          (v k n).toFun x * (un f n).toH1Function.grad x i)
    exact (hggrad f k n i).trans (hpgrad f k n i)

end SubdiffusiveProcess.Paper
