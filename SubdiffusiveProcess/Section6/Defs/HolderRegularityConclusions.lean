module

public import SubdiffusiveProcess.Section6.Defs.Excess
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FractionalReadout
public import SubdiffusiveProcess.Section6.Defs.TruncatedCube

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab

open Homogenization
attribute [local instance] Classical.propDecidable

/-- The full three-clause conclusion imported by the two Hölder regularity anchors. -/
noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.HolderRegularityConclusions {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (C : ℝ) (L : ℕ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) (alpha : ℝ) (m X : ℕ)
    (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d) : Prop :=
  (∀ n : ℕ, (n : ℤ) ≤ (m : ℤ) - (X : ℤ) →
      ∀ x ∈ cube d m, ∀ ell : ℕ, ell ≤ n →
      ∀ y : Vec d, OnTriadicGrid ell y → y ∈ truncatedCube d m n x →
        (3 : ℝ) ^ (alpha * ((n : ℝ) - (ell : ℝ))) *
            normalizedL2On (truncatedCube d m ell y)
              (fun z ↦ u.toFun z - averageOn (truncatedCube d m ell y) u.toFun) ≤
          C * (3 : ℝ) ^ (-alpha * ((m : ℝ) - (n : ℝ))) *
            (normalizedL2On (cube d m)
                (fun z ↦ u.toFun z - averageOn (cube d m) u.toFun) +
              (tailAverage M L m ω (cube d m))⁻¹ * (3 : ℝ) ^ (3 * (m : ℝ) / 2) *
                holderSeminormOn (cube d m) (1 / 2) g +
              (if x ∈ cube d (m - 1) then 0 else
                (3 : ℝ) ^ (3 * (m : ℝ) / 2) *
                  fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m)
                    (1 / 2) h.grad))) ∧
    (∀ n : ℕ, (n : ℤ) ≤ (m : ℤ) - (X : ℤ) → ∀ x ∈ cube d m,
      vectorNormalizedL2On (truncatedCube d m n x)
          (fun z ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L ω z) • u.grad z) ≤
        C * (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
          (vectorNormalizedL2On (cube d m)
              (fun z ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L ω z) • u.grad z) +
            (tailAverage M L m ω (cube d m)) ^ (-1 / 2 : ℝ) *
              (3 : ℝ) ^ ((m : ℝ) / 2) *
              holderSeminormOn (cube d m) (1 / 2) g +
            (if x ∈ cube d (m - 1) then 0 else
              (tailAverage M L m ω (cube d m)) ^ (1 / 2 : ℝ) *
                (3 : ℝ) ^ ((m : ℝ) / 2) *
                fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m)
                  (1 / 2) h.grad))) ∧
    (∀ n : ℕ, (X : ℤ) ≤ (m : ℤ) - (n : ℤ) →
      (m : ℝ) - (n : ℝ) ≤ (1 - alpha)⁻¹ →
      ∀ ell : ℕ, n ≤ ell → ell + 5 ≤ m → ∀ x ∈ cube d m,
        excess n (truncatedCube d m n x) u.toFun ≤
          C * (3 : ℝ) ^ (-((ell : ℝ) - (n : ℝ)) / 4) *
              excess ell (truncatedCube d m ell x) u.toFun +
            C * Real.sqrt (1 - alpha) * (3 : ℝ) ^ (-(ell : ℝ)) *
              normalizedL2On (truncatedCube d m ell x)
                (fun z ↦ u.toFun z - averageOn (truncatedCube d m ell x) u.toFun) +
            C * (tailAverage M L m ω (cube d m))⁻¹ *
              (3 : ℝ) ^ ((ell : ℝ) / 2) *
              holderSeminormOn (cube d m) (1 / 2) g +
            (if x ∈ cube d (m - 1) then 0 else
              C * ((1 - alpha) * ((m : ℝ) - (n : ℝ)) *
                vectorSupNormOn (cube d m) h.grad +
                (3 : ℝ) ^ ((ell : ℝ) / 2) *
                  fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m)
                    (1 / 2) h.grad)))
