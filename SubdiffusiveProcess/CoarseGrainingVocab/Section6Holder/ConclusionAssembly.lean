module

public import SubdiffusiveProcess.Section6.Defs.HolderRegularityConclusions
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.EnergyReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.OffGridConditional

@[expose] public section

/-!
# Hölder regularity: internal conclusion assembly

The pathwise conclusion is a conjunction of three rows.  Keeping its
constructor here lets the Campanato, energy-density, and excess arguments be
developed independently.  In particular, the intermediate hypothesis used by
the energy argument remains below the provider surface.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Exact constructor for the three Hölder rows.  The second argument
is where the harmonic argument's gap-power aggregation is consumed internally;
it is not a provider premise. -/
theorem holderRegularityConclusions_of_rows {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (C : ℝ) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (alpha : ℝ) (m X : ℕ)
    (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
    (hcampanato :
      ∀ n : ℕ, (n : ℤ) ≤ (m : ℤ) - (X : ℤ) →
        ∀ x ∈ cube d m, ∀ ell : ℕ, ell ≤ n →
        ∀ y : Vec d, OnTriadicGrid ell y → y ∈ truncatedCube d m n x →
          (3 : ℝ) ^ (alpha * ((n : ℝ) - (ell : ℝ))) *
              normalizedL2On (truncatedCube d m ell y)
                (fun z ↦ u.toFun z - averageOn (truncatedCube d m ell y) u.toFun) ≤
            C * (3 : ℝ) ^ (-alpha * ((m : ℝ) - (n : ℝ))) *
              (normalizedL2On (cube d m)
                  (fun z ↦ u.toFun z - averageOn (cube d m) u.toFun) +
                (tailAverage M L m omega (cube d m))⁻¹ *
                    (3 : ℝ) ^ (3 * (m : ℝ) / 2) *
                  holderSeminormOn (cube d m) (1 / 2) g +
                (if x ∈ cube d (m - 1) then 0 else
                  (3 : ℝ) ^ (3 * (m : ℝ) / 2) *
                    fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m)
                      (1 / 2) h.grad)))
    (henergy :
      ∀ n : ℕ, (n : ℤ) ≤ (m : ℤ) - (X : ℤ) → ∀ x ∈ cube d m,
        vectorNormalizedL2On (truncatedCube d m n x)
            (fun z ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega z) •
              u.grad z) ≤
          C * (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
            (vectorNormalizedL2On (cube d m)
                (fun z ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega z) •
                  u.grad z) +
              (tailAverage M L m omega (cube d m)) ^ (-1 / 2 : ℝ) *
                (3 : ℝ) ^ ((m : ℝ) / 2) *
                holderSeminormOn (cube d m) (1 / 2) g +
              (if x ∈ cube d (m - 1) then 0 else
                (tailAverage M L m omega (cube d m)) ^ (1 / 2 : ℝ) *
                  (3 : ℝ) ^ ((m : ℝ) / 2) *
                  fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m)
                    (1 / 2) h.grad)))
    (hexcess :
      ∀ n : ℕ, (X : ℤ) ≤ (m : ℤ) - (n : ℤ) →
        (m : ℝ) - (n : ℝ) ≤ (1 - alpha)⁻¹ →
        ∀ ell : ℕ, n ≤ ell → ell + 5 ≤ m → ∀ x ∈ cube d m,
          excess n (truncatedCube d m n x) u.toFun ≤
            C * (3 : ℝ) ^ (-((ell : ℝ) - (n : ℝ)) / 4) *
                excess ell (truncatedCube d m ell x) u.toFun +
              C * Real.sqrt (1 - alpha) * (3 : ℝ) ^ (-(ell : ℝ)) *
                normalizedL2On (truncatedCube d m ell x)
                  (fun z ↦ u.toFun z - averageOn (truncatedCube d m ell x) u.toFun) +
              C * (tailAverage M L m omega (cube d m))⁻¹ *
                (3 : ℝ) ^ ((ell : ℝ) / 2) *
                holderSeminormOn (cube d m) (1 / 2) g +
              (if x ∈ cube d (m - 1) then 0 else
                C * ((1 - alpha) * ((m : ℝ) - (n : ℝ)) *
                    vectorSupNormOn (cube d m) h.grad +
                  (3 : ℝ) ^ ((ell : ℝ) / 2) *
                    fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m)
                      (1 / 2) h.grad))) :
    HolderRegularityConclusions M C L omega alpha m X u h g := by
  exact ⟨hcampanato, henergy, hexcess⟩

/-- The energy row can be assembled after the Campanato and excess rows have
already been assembled.  This order is convenient while the gap-power bound
is owned by the harmonic-approximation argument. -/
theorem holderRegularityConclusions_of_campanato_excess_and_energy {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (C : ℝ) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (alpha : ℝ) (m X : ℕ)
    (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
    (hwithoutEnergy :
      (∀ n : ℕ, (n : ℤ) ≤ (m : ℤ) - (X : ℤ) →
        ∀ x ∈ cube d m, ∀ ell : ℕ, ell ≤ n →
        ∀ y : Vec d, OnTriadicGrid ell y → y ∈ truncatedCube d m n x →
          (3 : ℝ) ^ (alpha * ((n : ℝ) - (ell : ℝ))) *
              normalizedL2On (truncatedCube d m ell y)
                (fun z ↦ u.toFun z - averageOn (truncatedCube d m ell y) u.toFun) ≤
            C * (3 : ℝ) ^ (-alpha * ((m : ℝ) - (n : ℝ))) *
              (normalizedL2On (cube d m)
                  (fun z ↦ u.toFun z - averageOn (cube d m) u.toFun) +
                (tailAverage M L m omega (cube d m))⁻¹ *
                    (3 : ℝ) ^ (3 * (m : ℝ) / 2) *
                  holderSeminormOn (cube d m) (1 / 2) g +
                (if x ∈ cube d (m - 1) then 0 else
                  (3 : ℝ) ^ (3 * (m : ℝ) / 2) *
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
              C * (tailAverage M L m omega (cube d m))⁻¹ *
                (3 : ℝ) ^ ((ell : ℝ) / 2) *
                holderSeminormOn (cube d m) (1 / 2) g +
              (if x ∈ cube d (m - 1) then 0 else
                C * ((1 - alpha) * ((m : ℝ) - (n : ℝ)) *
                    vectorSupNormOn (cube d m) h.grad +
                  (3 : ℝ) ^ ((ell : ℝ) / 2) *
                    fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m)
                      (1 / 2) h.grad))))
    (henergy :
      ∀ n : ℕ, (n : ℤ) ≤ (m : ℤ) - (X : ℤ) → ∀ x ∈ cube d m,
        vectorNormalizedL2On (truncatedCube d m n x)
            (fun z ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega z) •
              u.grad z) ≤
          C * (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
            (vectorNormalizedL2On (cube d m)
                (fun z ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega z) •
                  u.grad z) +
              (tailAverage M L m omega (cube d m)) ^ (-1 / 2 : ℝ) *
                (3 : ℝ) ^ ((m : ℝ) / 2) *
                holderSeminormOn (cube d m) (1 / 2) g +
              (if x ∈ cube d (m - 1) then 0 else
                (tailAverage M L m omega (cube d m)) ^ (1 / 2 : ℝ) *
                  (3 : ℝ) ^ ((m : ℝ) / 2) *
                  fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m)
                    (1 / 2) h.grad))) :
    HolderRegularityConclusions M C L omega alpha m X u h g := by
  exact holderRegularityConclusions_of_rows M C L omega alpha m X u h g
    hwithoutEnergy.1 henergy hwithoutEnergy.2

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
