module

public import SubdiffusiveProcess.Paper.in_represented_bounds_seq
@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped Topology ENNReal NNReal
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem aux_represented_bounds_subseq_cutoffs
    (d : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (t : ℝ)
    (h : ∀ (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O →
      closure O ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → S.space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n) (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] chic n ∧
          (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
            0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
          responseForm S (a n)
            (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
            ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict
                (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
                (fun y => ENNReal.ofReal
                  ((a n).val y *
                    ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t))) (psi : ℕ → ℕ) :
    ∀ (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O →
      closure O ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → S.space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n) (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] chic n ∧
          (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
            0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
          responseForm S (a (psi n))
            (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
            ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict
                (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
                (fun y => ENNReal.ofReal
                  ((a (psi n)).val y *
                    ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)) := by
  intro K O hK hO hKO hOQ
  obtain ⟨V, cut, rep, B, hVo, hKV, hVO, hB, hcut⟩ := h K O hK hO hKO hOQ
  exact ⟨V, (fun n => cut (psi n)), (fun n => rep (psi n)), B,
    hVo, hKV, hVO, hB, fun n => hcut (psi n)⟩

theorem aux_represented_bounds_subseq_mesh
    (d : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (D : Submodule ℚ (DomainL2 (centeredCube z r hr)))
    (phi : D → Homogenization.H1Function (centeredCube z r hr : Set (SpatialCoordinates d)))
    (alpha : ℝ)
    (h : ∀ f : D, ∃ Cphi : ℝ, 0 ≤ Cphi ∧ ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∃ vN : ℕ → S.space, ∃ vcN : ℕ → SpatialCoordinates d → ℝ,
      ∃ Kset : Set (SpatialCoordinates d),
        IsCompact Kset ∧ Kset ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
        ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ,
          (vN n).val.1
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vcN n ∧
          ContinuousOn (vcN n) (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
          (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) \ Kset, vcN n x = 0) ∧
          Lane4.IsHolderOn alpha
            (closure (centeredCube z r hr : Set (SpatialCoordinates d))) (vcN n) ∧
          Lane4.cAlphaNorm alpha
            (closure (centeredCube z r hr : Set (SpatialCoordinates d))) (vcN n) ≤ M ∧
          responseForm S (a n)
            (vN n) (vN n) ≤ M ∧
          ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
            |vcN n x - (phi f).toFun x| ≤ Cphi * (r / (3 : ℝ) ^ k)) (psi : ℕ → ℕ) :
    ∀ f : D, ∃ Cphi : ℝ, 0 ≤ Cphi ∧ ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∃ vN : ℕ → S.space, ∃ vcN : ℕ → SpatialCoordinates d → ℝ,
      ∃ Kset : Set (SpatialCoordinates d),
        IsCompact Kset ∧ Kset ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
        ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ,
          (vN n).val.1
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vcN n ∧
          ContinuousOn (vcN n) (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
          (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) \ Kset, vcN n x = 0) ∧
          Lane4.IsHolderOn alpha
            (closure (centeredCube z r hr : Set (SpatialCoordinates d))) (vcN n) ∧
          Lane4.cAlphaNorm alpha
            (closure (centeredCube z r hr : Set (SpatialCoordinates d))) (vcN n) ≤ M ∧
          responseForm S (a (psi n))
            (vN n) (vN n) ≤ M ∧
          ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
            |vcN n x - (phi f).toFun x| ≤ Cphi * (r / (3 : ℝ) ^ k) := by
  intro f
  obtain ⟨C, hC, k0, hbound⟩ := h f
  refine ⟨C, hC, k0, fun k hk => ?_⟩
  obtain ⟨v, vc, K, hK, hKQ, B, hB, hbound⟩ := hbound k hk
  exact ⟨(fun n => v (psi n)), (fun n => vc (psi n)), K, hK, hKQ, B, hB,
    fun n => hbound (psi n)⟩

/-- Every concrete represented bound, collar and finite mesh is retained along
one further subsequence. The form, constants and source/trace banks are unchanged. -/
theorem represented_bounds_subseq
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (h : in_represented_bounds_seq d hd z r hr S a G)
    (psi : ℕ → ℕ) (hpsi : Tendsto psi atTop atTop) :
    in_represented_bounds_seq d hd z r hr S (fun n => a (psi n)) G := by
  unfold in_represented_bounds_seq at h ⊢
  rcases h with ⟨KN, hKN, Kstar, hKstar, hfrac, hcoercive, hInterp, t, ht, htd,
    hcutoffs, D, hDc, hDdense, phi, hPhi, alpha, eta, hag, hal, hep, hel, u, uc,
    hU, hUr, hUc, hUh, rho, hrho, chi, hChi, w, hW, hCollar, hMesh, hSmooth, _⟩
  letI : Countable D := hDc
  refine ⟨(fun n => KN (psi n)), (fun n => hKN (psi n)), Kstar,
    (fun n => hKstar (psi n)), hfrac, (fun n => hcoercive (psi n)),
    hInterp, t, ht, htd,
    aux_represented_bounds_subseq_cutoffs d z r hr S a t hcutoffs psi, D, hDc, hDdense, phi, hPhi, alpha, eta, hag, hal, hep, hel,
    (fun f n => u f (psi n)), (fun f n => uc f (psi n)), (fun f n => hU f (psi n)),
    (fun f n => hUr f (psi n)), (fun f => (hUc f).comp hpsi), ?_, rho, hrho,
    (fun k n => chi k (psi n)), ?_, (fun f k n => w f k (psi n)),
    (fun f k n => hW f k (psi n)), ?_,
    aux_represented_bounds_subseq_mesh d z r hr S a D phi alpha hMesh psi, hSmooth, trivial⟩
  · intro f
    obtain ⟨Kf, hKf, hbound⟩ := hUh f
    exact ⟨Kf, hKf, fun n => hbound (psi n)⟩
  · intro k
    obtain ⟨Kc, hKc, hbound⟩ := hChi k
    exact ⟨Kc, hKc, fun n => hbound (psi n)⟩
  · intro f
    obtain ⟨Kf, hKf, hbound⟩ := hCollar f
    exact ⟨Kf, hKf, fun k n => hbound k (psi n)⟩

end Paper
