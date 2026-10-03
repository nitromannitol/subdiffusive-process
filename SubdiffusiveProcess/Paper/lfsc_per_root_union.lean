module

public import SubdiffusiveProcess.FiniteStopping.SourcedGoodStep
public import SubdiffusiveProcess.Paper.finite_interval_packing_generic

@[expose] public section

/-! Interval packing for the L-adic subdivision of every root cell of a triadic root, for two arbitrary predicates
(generic version of `lfsgs_per_root_union`: no infrared characterization, `Reg` and `TraceClose` abstract). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace Paper

variable {d : ℕ}

theorem lfsc_per_root_union
    (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (a b theta : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (htheta : 0 < theta) (hthetab : theta < b - a)
    (H1 : ℕ) (hH1 : 0 < H1) (B : ℝ)
    (hB : B > 1000 * (H1 : ℝ) * ((d : ℝ) + 1) * (Real.log 3 + 1) / theta)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (z : SpatialCoordinates d) (j : ℤ)
    (Reg : ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop)
    (hRegWitness : ∀ (N k : ℕ) (zc : SpatialCoordinates d), k ≤ N →
      ∃ W : ℕ+ → Set (BilateralField d),
        (∀ h : ℕ+, MeasurableSet[MeasurableSpace.comap
          ((Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))).restrict)
          (inferInstance : MeasurableSpace
            ((i : Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))) →
              C(SpatialCoordinates d, ℝ)))] (W h)) ∧
        (∀ h : ℕ+, (chaosSampleLaw model).toMeasure (W h) ≤
          ENNReal.ofReal (Real.exp (-B * (h : ℝ)))) ∧
        (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure,
          ¬Reg N k zc omega → omega ∈ ⋃ h : ℕ+, W h))
    (m0 : ℕ)
    (TraceClose : ℕ → ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop)
    (hTraceWitness : ∀ (N M k : ℕ) (zc : SpatialCoordinates d),
      k ≤ N → k ≤ M → m0 ≤ N - k → m0 ≤ M - k →
      ∃ W : ℕ+ → Set (BilateralField d),
        (∀ h : ℕ+, MeasurableSet[MeasurableSpace.comap
          ((Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))).restrict)
          (inferInstance : MeasurableSpace
            ((i : Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))) →
              C(SpatialCoordinates d, ℝ)))] (W h)) ∧
        (∀ h : ℕ+, (chaosSampleLaw model).toMeasure (W h) ≤
          ENNReal.ofReal (Real.exp (-B * (h : ℝ)))) ∧
        (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure,
          ¬TraceClose N M k zc omega → omega ∈ ⋃ h : ℕ+, W h)) :
    ∃ Ceta ceta : ℝ, ∃ N0 : ℕ, 0 < Ceta ∧ 0 < ceta ∧
      ∀ N M : ℕ, N0 ≤ N → N ≤ M →
        (∀ k : ℤ, a * (N : ℝ) ≤ (k : ℝ) → (k : ℝ) ≤ b * (N : ℝ) →
          0 ≤ k ∧ m0 ≤ N - k.toNat ∧ m0 ≤ M - k.toNat) ∧
        ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
          (chaosSampleLaw model).toMeasure Bad ≤ ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-ceta * (N : ℝ))) ∧
          ∀ omega : BilateralField d, omega ∉ Bad →
            ∀ (v : Fin (SubdiffusiveProcess.FiniteStopping.rootRho H1 j) → OddGridIndex d 1)
              (w : ℕ → OddGridIndex d (subdivisionHalfWidth H1)),
              let k : ℕ → ℤ := fun n => (H1 : ℤ) * (n : ℤ) -
                (H1 : ℤ) * SubdiffusiveProcess.FiniteStopping.rootQ H1 j
              let zc : ℕ → SpatialCoordinates d := fun n =>
                descendantCenter (subdivisionHalfWidth H1)
                  (SubdiffusiveProcess.FiniteStopping.rootCell H1 j z v)
                  ((3 : ℝ) ^ ((H1 : ℤ) * SubdiffusiveProcess.FiniteStopping.rootQ H1 j)) n
                  (fun i : Fin n => w i)
              (Nat.card {n : ℕ // a * (N : ℝ) ≤ (k n : ℝ) ∧
                (k n : ℝ) ≤ b * (N : ℝ) ∧
                ¬(Reg N (k n).toNat (zc n) omega ∧
                  Reg M (k n).toNat (zc n) omega ∧
                  TraceClose N M (k n).toNat (zc n) omega)} : ℝ) ≤
                theta * (N : ℝ) / (H1 : ℝ) := by
  have hi : ∀ v : Fin (SubdiffusiveProcess.FiniteStopping.rootRho H1 j) → OddGridIndex d 1,
      ∃ Ceta ceta : ℝ, ∃ N0 : ℕ, 0 < Ceta ∧ 0 < ceta ∧
      ∀ N M : ℕ, N0 ≤ N → N ≤ M →
        (∀ k : ℤ, a * (N : ℝ) ≤ (k : ℝ) → (k : ℝ) ≤ b * (N : ℝ) →
          0 ≤ k ∧ m0 ≤ N - k.toNat ∧ m0 ≤ M - k.toNat) ∧
        ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
          (chaosSampleLaw model).toMeasure Bad ≤
            ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-ceta * (N : ℝ))) ∧
          ∀ omega : BilateralField d, omega ∉ Bad →
            ∀ w : ℕ → OddGridIndex d (subdivisionHalfWidth H1),
              let k : ℕ → ℤ := fun n => (H1 : ℤ) * (n : ℤ) -
                (H1 : ℤ) * SubdiffusiveProcess.FiniteStopping.rootQ H1 j
              let zc : ℕ → SpatialCoordinates d := fun n =>
                descendantCenter (subdivisionHalfWidth H1)
                  (SubdiffusiveProcess.FiniteStopping.rootCell H1 j z v)
                  ((3 : ℝ) ^ ((H1 : ℤ) * SubdiffusiveProcess.FiniteStopping.rootQ H1 j)) n
                  (fun i : Fin n => w i)
              (Nat.card {n : ℕ // a * (N : ℝ) ≤ (k n : ℝ) ∧
                (k n : ℝ) ≤ b * (N : ℝ) ∧
                ¬(Reg N (k n).toNat (zc n) omega ∧
                  Reg M (k n).toNat (zc n) omega ∧
                  TraceClose N M (k n).toNat (zc n) omega)} : ℝ) ≤
                theta * (N : ℝ) / (H1 : ℝ) := by
    intro v
    exact finite_interval_packing_generic d hd a b theta ha hab hb htheta hthetab H1 hH1 B hB
      model (SubdiffusiveProcess.FiniteStopping.rootCell H1 j z v)
      ((H1 : ℤ) * SubdiffusiveProcess.FiniteStopping.rootQ H1 j) Reg hRegWitness m0
      TraceClose hTraceWitness
  exact SubdiffusiveProcess.FiniteStopping.fip_union_over_roots model H1
    (subdivisionHalfWidth H1)
    (fun v => SubdiffusiveProcess.FiniteStopping.rootCell H1 j z v)
    ((H1 : ℤ) * SubdiffusiveProcess.FiniteStopping.rootQ H1 j)
    Reg TraceClose a b theta m0 hi

end Paper
