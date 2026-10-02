import SubdiffusiveProcess.Paper.in_represented_bounds
import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Lane2.BoundaryPackaging
import SubdiffusiveProcess.Lane2.NativeBridge
import SubdiffusiveProcess.Lane2.ResponseMarkov
import SubdiffusiveProcess.Lane2.ExternalInputs
import SubdiffusiveProcess.Lane2.BoundaryResponse
import SubdiffusiveProcess.Lane2.MeshGluing
import SubdiffusiveProcess.Main.MeasureTrace
import SubdiffusiveProcess.Main.CubeFractionalL2Norm
import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Lane4.Carriers

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



def in_represented_bounds_seq
    (d : ℕ) (hd : 2 ≤ d)
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (S : ResponseSpace (centeredCube z0 r0 hr0))
    (a : ℕ → PositiveCoefficient (centeredCube z0 r0 hr0))
    (G : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0)) :
    Prop :=
  ∃
    
    (KN : ℕ → ℝ) (_hKN : ∀ n, 0 ≤ KN n)
    (Kstar : ℝ) (_hKstar : ∀ n, KN n ≤ Kstar)
    (_hfrac : ∀ w : S.space,
      cubeFractionalL2Seminorm hd z0 r0 hr0 Lane4.threeQuarterOrder
        (fun _ : Fin 1 => w.val.1) < ⊤)
    (_hcoercive : ∀ n (w : S.space),
      ‖w.val.1‖ ^ 2 + volume.real (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) *
          ((cubeFractionalL2Seminorm hd z0 r0 hr0 Lane4.threeQuarterOrder
              (fun _ : Fin 1 => w.val.1)).toReal) ^ 2 ≤
        KN n * responseForm S (a n) w w)
    (hInterp : CubeFractionalInterpolationInput d hd)
    (t : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (_hcutoffs : ∀ (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O →
      closure O ⊆ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → S.space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n) (closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))] chic n ∧
          (∀ x ∈ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)),
            0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
          responseForm S (a n)
            (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)),
            ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict
                (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))).withDensity
                (fun y => ENNReal.ofReal
                  ((a n).val y *
                    ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)))
    
    (D : Submodule ℚ (DomainL2 (centeredCube z0 r0 hr0))) (_ : Countable D)
    (_hDdense : Dense (D : Set (DomainL2 (centeredCube z0 r0 hr0))))
    (phi : D → H1Function (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)))
    (_hPhi : ∀ f : D, ContDiff ℝ (⊤ : ℕ∞) (phi f).toFun ∧
      HasCompactSupport (phi f).toFun ∧
      tsupport (phi f).toFun ⊆ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) ∧
      (sobolevDataOfH1 (phi f)).1 = f.val)
    (alpha eta : ℝ)
    (_halpha_gt : 1 / 2 < alpha) (_halpha_lt : alpha < 1)
    (_heta_pos : 0 < eta) (_heta_lt : 1 + eta < 2 * alpha)
    (u : DomainL2 (centeredCube z0 r0 hr0) → ℕ → S.space)
    (uc : DomainL2 (centeredCube z0 r0 hr0) → ℕ → SpatialCoordinates d → ℝ)
    (_hU : ∀ (f : DomainL2 (centeredCube z0 r0 hr0)) (n : ℕ),
      u f n = responseSolution S (a n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL))
    (_hUrep : ∀ (f : DomainL2 (centeredCube z0 r0 hr0)) (n : ℕ),
      (u f n).val.1
        =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))] uc f n)
    (_hUconv : ∀ f : DomainL2 (centeredCube z0 r0 hr0),
      Tendsto (fun n => (u f n).val.1) atTop (𝓝 (G f)))
    (_hUholder : ∀ f : D, ∃ Kf : ℝ, 0 ≤ Kf ∧ ∀ n : ℕ,
      ContinuousOn (uc f.val n) (closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) ∧
      Lane4.IsHolderOn alpha
        (closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) (uc f.val n) ∧
      Lane4.cAlphaNorm alpha
        (closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) (uc f.val n) ≤ Kf ∧
      ∀ x ∈ frontier (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)), uc f.val n x = 0)
    (rho : ℕ → ℝ) (_hrho : ∀ k : ℕ, rho k = r0 / (10 * (3 : ℝ) ^ k))
    (chi : ℕ → ℕ → SpatialCoordinates d → ℝ)
    (_hChi : ∀ k : ℕ, ∃ Kchi : ℝ, 0 ≤ Kchi ∧ ∀ n : ℕ,
      ContinuousOn (chi k n) (closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) ∧
      Lane4.IsHolderOn alpha
        (closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) (chi k n) ∧
      Lane4.cAlphaNorm alpha
        (closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) (chi k n) ≤ Kchi ∧
      (∀ x ∈ closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)),
        0 ≤ chi k n x ∧ chi k n x ≤ 1) ∧
      (∀ x ∈ closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)),
        Metric.infDist x ((centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))ᶜ) ≤ rho k →
          chi k n x = 0) ∧
      (∀ x ∈ closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)),
        3 * rho k ≤ Metric.infDist x ((centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))ᶜ) →
          chi k n x = 1))
    (w : DomainL2 (centeredCube z0 r0 hr0) → ℕ → ℕ → S.space)
    (_hW : ∀ (f : D) (k n : ℕ),
      ((w f.val k n).val.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))]
          (fun x => uc f.val n x * chi k n x))
    (_hCollarError : ∀ f : D, ∃ Kf : ℝ, 0 ≤ Kf ∧ ∀ k n : ℕ,
      responseForm S (a n)
          (u f.val n - w f.val k n) (u f.val n - w f.val k n) ≤
        Kf * ((rho k) ^ (t - (d : ℝ) + 1) + (rho k) ^ (2 * alpha - 1 - eta)))
    (_hFiniteMesh : ∀ f : D, ∃ Cphi : ℝ, 0 ≤ Cphi ∧ ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∃ vN : ℕ → S.space, ∃ vcN : ℕ → SpatialCoordinates d → ℝ,
      ∃ Kset : Set (SpatialCoordinates d),
        IsCompact Kset ∧ Kset ⊆ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) ∧
        ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ,
          (vN n).val.1
            =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))] vcN n ∧
          ContinuousOn (vcN n) (closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) ∧
          (∀ x ∈ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) \ Kset, vcN n x = 0) ∧
          Lane4.IsHolderOn alpha
            (closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) (vcN n) ∧
          Lane4.cAlphaNorm alpha
            (closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))) (vcN n) ≤ M ∧
          responseForm S (a n)
            (vN n) (vN n) ≤ M ∧
          ∀ x ∈ closure (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)),
            |vcN n x - (phi f).toFun x| ≤ Cphi * (r0 / (3 : ℝ) ^ k))
    (_hsmooth : ∀ f : SpatialCoordinates d → ℝ, Continuous f → HasCompactSupport f →
      tsupport f ⊆ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) →
      ∀ ε : ℝ, 0 < ε →
      ∃ g : D, ∀ x : SpatialCoordinates d, |(phi g).toFun x - f x| ≤ ε),
    True

/-- The fixed-sample bundle is the abstract bundle at the fixed-sample coefficient family. -/
theorem aux_in_represented_bounds_seq_iff
    (d : ℕ) (hd : 2 ≤ d)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d)
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (S : ResponseSpace (centeredCube z0 r0 hr0))
    (G : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (N : ℕ → ℕ) :
    aux_in_represented_bounds_side d hd model H om z0 r0 hr0 S G N ↔
      in_represented_bounds_seq d hd z0 r0 hr0 S
        (fun n => Lane4.cutoffPositiveCoefficient model H om (N n) z0 hr0) G :=
  Iff.rfl

end Paper
