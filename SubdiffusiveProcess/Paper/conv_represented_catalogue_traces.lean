module

public import Mathlib
public import SubdiffusiveProcess.Paper.conv_represented_catalogue_holder_family
public import SubdiffusiveProcess.Paper.conv_represented_catalogue_plateau
public import SubdiffusiveProcess.VariationalResponses.CellDirichlet

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped Topology ENNReal NNReal ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- **Catalogue trace family (clauses D5–D9 of `conv_represented_estimates`).**  For any countable family of
cubes `(z j, r j)` and any countable smooth source family `f j g`, there is ONE countable family `theta`
(indexed by `ℕ`, the same functions for every cube) of smooth functions with `H¹` packaging on every cube such
that: every `f j g` is a trace; the family is closed under restriction to subcubes; every boundary datum that is
`α`-Hölder on the frontier and lies in the `β`-cell class is approximated by traces in the `β` quotient norm and
uniformly on the frontier; and every compact union of closed cubes inside an open union of cubes admits a smooth
plateau in the family. -/
theorem conv_represented_catalogue_traces (d : ℕ) (hd : 2 ≤ d) (beta alpha : ℝ)
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
            (⋃ k ∈ o, (centeredCube (z k) (r k) (hr k) : Set (SpatialCoordinates d)))) := by
  classical
  -- traces approximating Hölder data, one family per cube
  choose ι2 hι2c θ2 hθ2s hθ2 using fun j =>
    conv_represented_catalogue_holder_family d hd beta alpha hb hba ha1 (z j) (r j) (hr j)
  -- plateaus, one per triple `(j, s, o)`
  have hplateau : ∀ t : J × Finset J × Finset J, ∃ P : SpatialCoordinates d → ℝ,
      ContDiff ℝ ∞ P ∧
      ((⋃ k ∈ t.2.1, closure (centeredCube (z k) (r k) (hr k) : Set (SpatialCoordinates d))) ⊆
          (⋃ k ∈ t.2.2, (centeredCube (z k) (r k) (hr k) : Set (SpatialCoordinates d))) →
        (∀ x : SpatialCoordinates d, 0 ≤ P x ∧ P x ≤ 1) ∧
        ∃ V : Set (SpatialCoordinates d), IsOpen V ∧
          (⋃ k ∈ t.2.1, closure (centeredCube (z k) (r k) (hr k) : Set (SpatialCoordinates d))) ⊆ V ∧
          V ⊆ (⋃ k ∈ t.2.2, (centeredCube (z k) (r k) (hr k) : Set (SpatialCoordinates d))) ∧
          (∀ x ∈ V, P x = 1) ∧
          tsupport P ⊆
            (⋃ k ∈ t.2.2, (centeredCube (z k) (r k) (hr k) : Set (SpatialCoordinates d)))) := by
    intro t
    by_cases hK : (⋃ k ∈ t.2.1, closure (centeredCube (z k) (r k) (hr k) :
        Set (SpatialCoordinates d))) ⊆
        (⋃ k ∈ t.2.2, (centeredCube (z k) (r k) (hr k) : Set (SpatialCoordinates d)))
    · have hcomp : IsCompact (⋃ k ∈ t.2.1, closure (centeredCube (z k) (r k) (hr k) :
          Set (SpatialCoordinates d))) :=
        (t.2.1).isCompact_biUnion fun k _ =>
          (centeredCube_isBounded (z k) (hr k)).isCompact_closure
      have hopen : IsOpen (⋃ k ∈ t.2.2, (centeredCube (z k) (r k) (hr k) :
          Set (SpatialCoordinates d))) :=
        isOpen_biUnion fun k _ => (centeredCube (z k) (r k) (hr k)).isOpen
      obtain ⟨P, hPs, hP01, V, hVo, hKV, hVW, hV1, hsupp⟩ :=
        conv_represented_catalogue_plateau d _ _ hcomp hopen hK
      exact ⟨P, hPs, fun _ => ⟨hP01, V, hVo, hKV, hVW, hV1, hsupp⟩⟩
    · exact ⟨fun _ => 0, contDiff_const, fun h => absurd h hK⟩
  choose P hPs hPprop using hplateau
  -- one enumeration
  let ι : Type := Option ((Σ j, D j) ⊕ (Σ j, ι2 j) ⊕ (J × Finset J × Finset J))
  have : ∀ j, Countable (ι2 j) := hι2c
  let Θ : ι → SpatialCoordinates d → ℝ := fun i =>
    match i with
    | none => fun _ => 0
    | some (Sum.inl a) => f a.1 a.2
    | some (Sum.inr (Sum.inl b)) => θ2 b.1 b.2
    | some (Sum.inr (Sum.inr t)) => P t
  have hΘs : ∀ i, ContDiff ℝ ∞ (Θ i) := by
    intro i
    rcases i with _ | a | b | t
    · exact contDiff_const
    · exact hf a.1 a.2
    · exact hθ2s b.1 b.2
    · exact hPs t
  obtain ⟨enum, henum⟩ := exists_surjective_nat ι
  let theta : J → ℕ → SpatialCoordinates d → ℝ := fun _ h => Θ (enum h)
  let thetaH1 : ∀ j, ℕ → Homogenization.H1Function
      (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) := fun j h =>
    Homogenization.H1Function.ofContDiffOnIsOpenBoundedConvexDomain
      (lane2_isOpenBoundedConvexDomain_centeredCube (z j) (hr j))
      ((hΘs (enum h)).of_le (by norm_num))
  refine ⟨theta, thetaH1, fun j h => ⟨hΘs (enum h), rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro j g
    obtain ⟨h, hh⟩ := henum (some (Sum.inl ⟨j, g⟩))
    exact ⟨h, by simp only [theta, hh, Θ]⟩
  · intro j k _ h
    exact ⟨h, rfl⟩
  · intro j b hbH hbC
    obtain ⟨h, hc, hq, hu⟩ := hθ2 j b hbH hbC
    choose h' hh' using fun k => henum (some (Sum.inr (Sum.inl ⟨j, h k⟩)))
    have hth : ∀ k, theta j (h' k) = θ2 j (h k) := fun k => by simp only [theta, hh', Θ]
    have hfun : (fun k => theta j (h' k)) = fun k => θ2 j (h k) := funext hth
    refine ⟨h', fun k => ?_, ?_, ?_⟩
    · rw [hth]; exact hc k
    · simp only [hth]; exact hq
    · rw [hfun]; exact hu
  · intro j s o hK hcl m
    obtain ⟨h, hh⟩ := henum (some (Sum.inr (Sum.inr (j, s, o))))
    have hth : theta j h = P (j, s, o) := by simp only [theta, hh, Θ]
    obtain ⟨h01, V, hVo, hKV, hVW, hV1, hsupp⟩ := hPprop (j, s, o) hK
    exact ⟨h, V, hVo, hKV, hVW, by rw [hth]; exact h01, by rw [hth]; exact hV1,
      by rw [hth]; exact hsupp⟩

end SubdiffusiveProcess.Paper
