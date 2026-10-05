module

public import Mathlib
public import SubdiffusiveProcess.Paper.conv_represented_catalogue_traces
public import SubdiffusiveProcess.Paper.Foundations.CollarBufferedProfile

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped Topology ENNReal NNReal ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The buffered collar profiles are `C^∞`. -/
theorem aux_conv_represented_catalogue_traces_buffered_smooth (d : ℕ) (z : SpatialCoordinates d)
    (R r : ℝ) : ContDiff ℝ ∞ (bufferedCollarProfile d z R r) := by
  unfold bufferedCollarProfile
  refine contDiff_prod fun i _ => ?_
  have hi : ContDiff ℝ ∞ (fun x : SpatialCoordinates d => x i) := contDiff_apply ℝ ℝ i
  have h1 : ContDiff ℝ ∞ (fun x : SpatialCoordinates d =>
      (x i - (z i - R / 2) - 3 * r / 2) / r) :=
    (((hi.sub contDiff_const).sub contDiff_const).div_const r)
  have h2 : ContDiff ℝ ∞ (fun x : SpatialCoordinates d =>
      ((z i + R / 2) - x i - 3 * r / 2) / r) :=
    (((contDiff_const.sub hi).sub contDiff_const).div_const r)
  exact (Real.smoothTransition.contDiff.comp h1).mul (Real.smoothTransition.contDiff.comp h2)

/-- **Catalogue trace family with the buffered collar profiles (strengthened constructor).**  The
conclusion of `conv_represented_catalogue_traces` (clauses D5–D9) together with the requirement that,
for every catalogue cube `j'`, every level `k` and every cube `j`, the buffered collar profile
`bufferedCollarProfile d (z j') (r j') (r j' / (10 * 3 ^ k))` is a trace on `j` (the same smooth function
for every cube, so all its restrictions to subcubes are traces as well). -/
theorem conv_represented_catalogue_traces_buffered (d : ℕ) (hd : 2 ≤ d) (beta alpha : ℝ)
    (hb : 1 / 2 < beta) (hba : beta < alpha) (ha1 : alpha < 1)
    (J : Type) [Countable J] (z : J → SpatialCoordinates d) (r : J → ℝ) (hr : ∀ j, 0 < r j)
    (D : J → Type) [∀ j, Countable (D j)] (f : ∀ j, D j → SpatialCoordinates d → ℝ)
    (hf : ∀ j g, ContDiff ℝ ∞ (f j g)) :
    ∃ (theta : J → ℕ → SpatialCoordinates d → ℝ)
      (thetaH1 : ∀ j, ℕ → Homogenization.H1Function
        (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))),
      (∀ j : J, ∀ h : ℕ, ContDiff ℝ ∞ (theta j h) ∧ (thetaH1 j h).toFun = theta j h) ∧
      (∀ j : J, ∀ g : D j, ∃ h : ℕ, theta j h = f j g) ∧
      (∀ j k : J,
        (centeredCube (z k) (r k) (hr k) : Set (SpatialCoordinates d)) ⊆
          (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) →
        ∀ h : ℕ, ∃ h' : ℕ, theta k h' = theta j h) ∧
      (∀ j : J, ∀ b : SpatialCoordinates d → ℝ,
        IsHolderOn alpha
          (frontier (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))) b →
        IsCellBoundaryClass beta (z j) (r j) b →
        ∃ h : ℕ → ℕ,
          (∀ k : ℕ, IsCellBoundaryClass beta (z j) (r j) (theta j (h k) - b)) ∧
          Tendsto (fun k : ℕ =>
            cellBoundaryQuotientNorm beta (z j) (r j) (theta j (h k) - b)) atTop (𝓝 0) ∧
          TendstoUniformlyOn (fun k : ℕ => theta j (h k)) b atTop
            (frontier (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))) ∧
      (∀ j : J, ∀ s o : Finset J,
        (⋃ k ∈ s, closure (centeredCube (z k) (r k) (hr k) : Set (SpatialCoordinates d))) ⊆
          (⋃ k ∈ o, (centeredCube (z k) (r k) (hr k) : Set (SpatialCoordinates d))) →
        closure (⋃ k ∈ o, (centeredCube (z k) (r k) (hr k) : Set (SpatialCoordinates d))) ⊆
          (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) →
        ∀ _m : ℕ, ∃ h : ℕ, ∃ V : Set (SpatialCoordinates d),
          IsOpen V ∧
          (⋃ k ∈ s, closure (centeredCube (z k) (r k) (hr k) : Set (SpatialCoordinates d))) ⊆ V ∧
          V ⊆ (⋃ k ∈ o, (centeredCube (z k) (r k) (hr k) : Set (SpatialCoordinates d))) ∧
          (∀ x : SpatialCoordinates d, 0 ≤ theta j h x ∧ theta j h x ≤ 1) ∧
          (∀ x ∈ V, theta j h x = 1) ∧
          tsupport (theta j h) ⊆
            (⋃ k ∈ o, (centeredCube (z k) (r k) (hr k) : Set (SpatialCoordinates d)))) ∧
      (∀ (j' : J) (k : ℕ) (j : J), ∃ h : ℕ,
        theta j h = bufferedCollarProfile d (z j') (r j') (r j' / (10 * (3 : ℝ) ^ k))) := by
  classical
  obtain ⟨theta, thetaH1, h5, h6, h7, h8, h9⟩ :=
    conv_represented_catalogue_traces d hd beta alpha hb hba ha1 J z r hr
      (fun j => D j ⊕ (J × ℕ))
      (fun j g => Sum.elim (f j) (fun p => bufferedCollarProfile d (z p.1) (r p.1)
        (r p.1 / (10 * (3 : ℝ) ^ p.2))) g)
      (fun j g => by
        rcases g with g | p
        · exact hf j g
        · exact aux_conv_represented_catalogue_traces_buffered_smooth d (z p.1) (r p.1) _)
  refine ⟨theta, thetaH1, h5, fun j g => h6 j (Sum.inl g), h7, h8, h9, ?_⟩
  intro j' k j
  exact h6 j (Sum.inr (j', k))

end SubdiffusiveProcess.Paper
