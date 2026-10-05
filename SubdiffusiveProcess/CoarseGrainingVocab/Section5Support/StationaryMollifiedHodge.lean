module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StationaryMollifierDerivative

@[expose] public section

/-!
# Smooth stationary Hodge energy identities

This file packages the coordinate derivatives supplied by stationary
mollification into literal vector `L²` gradients.  It then combines the
potential/solenoidal orthogonality with stationary integration by parts.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section


namespace Stationary

variable {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]
variable {mu : Measure Omega}

/-- The stationary vector `L²` pairing is the sum of its scalar coordinate
pairings. -/
theorem inner_vectorL2_eq_sum_inner_coord
    (F G : VectorL2 d mu) :
    inner ℝ F G = ∑ i : Fin d,
      inner ℝ (vectorL2Coord (mu := mu) i F)
        (vectorL2Coord (mu := mu) i G) := by
  simp_rw [L2.inner_def]
  have hcoord : ∀ i : Fin d, ∀ᵐ omega ∂mu,
      (vectorL2Coord (mu := mu) i F : Omega → ℝ) omega = F omega i ∧
      (vectorL2Coord (mu := mu) i G : Omega → ℝ) omega = G omega i := by
    intro i
    filter_upwards
      [(PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin d => ℝ) i).coeFn_compLpL F,
        (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin d => ℝ) i).coeFn_compLpL G]
      with omega hF hG
    exact ⟨hF, hG⟩
  rw [← integral_finsetSum Finset.univ (fun i _ =>
    L2.integrable_inner
      (vectorL2Coord (mu := mu) i F)
      (vectorL2Coord (mu := mu) i G))]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.2 hcoord] with omega homega
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(homega i).1, (homega i).2]

/-- Stationary vector `L²` fields are determined by their finitely many
scalar coordinates. -/
theorem vectorL2_eq_of_coord_eq
    (F G : VectorL2 d mu)
    (hcoord : ∀ i : Fin d,
      vectorL2Coord (mu := mu) i F = vectorL2Coord (mu := mu) i G) :
    F = G := by
  have hinner : inner ℝ (F - G) (F - G) = 0 := by
    rw [inner_vectorL2_eq_sum_inner_coord]
    simp_rw [map_sub, hcoord, sub_self, inner_zero_left]
    simp
  have hnorm : ‖F - G‖ ^ 2 = 0 := by
    rwa [real_inner_self_eq_norm_sq] at hinner
  have hzero : F - G = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (F - G)]
  exact sub_eq_zero.mp hzero

end Stationary

/-- Assemble scalar stationary coordinates into a vector stationary `L²`
field. -/
def assembleScalarCoordinates {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (X : Fin d → Stationary.ScalarL2 M.P.toMeasure) :
    Stationary.VectorL2 d M.P.toMeasure :=
  ∑ i : Fin d,
    scalarToVectorL2 M.P.toMeasure (Pi.single i 1) (X i)

theorem vectorL2Coord_assembleScalarCoordinates {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (X : Fin d → Stationary.ScalarL2 M.P.toMeasure) (j : Fin d) :
    Stationary.vectorL2Coord (mu := M.P.toMeasure) j
        (assembleScalarCoordinates M X) = X j := by
  classical
  rw [assembleScalarCoordinates, map_sum]
  simp_rw [vectorL2Coord_scalarToVectorL2]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [hij]
  · simp

/-- Reassembling all scalar coordinates recovers the original vector field. -/
theorem assembleScalarCoordinates_vectorL2Coord {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (F : Stationary.VectorL2 d M.P.toMeasure) :
    assembleScalarCoordinates M
        (fun i => Stationary.vectorL2Coord (mu := M.P.toMeasure) i F) = F := by
  apply Stationary.vectorL2_eq_of_coord_eq
  intro i
  rw [vectorL2Coord_assembleScalarCoordinates]

/-- Pairing a scalar field embedded in one coordinate with a vector field
extracts precisely that scalar coordinate pairing. -/
theorem inner_scalarToVectorL2_basis {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (X : Stationary.ScalarL2 M.P.toMeasure)
    (F : Stationary.VectorL2 d M.P.toMeasure) (i : Fin d) :
    inner ℝ (scalarToVectorL2 M.P.toMeasure (Pi.single i 1) X) F =
      inner ℝ X
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) i F) := by
  classical
  rw [Stationary.inner_vectorL2_eq_sum_inner_coord]
  simp_rw [vectorL2Coord_scalarToVectorL2]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

/-- Right-slot form of `inner_scalarToVectorL2_basis`. -/
theorem inner_scalarToVectorL2_basis_right {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (F : Stationary.VectorL2 d M.P.toMeasure)
    (X : Stationary.ScalarL2 M.P.toMeasure) (i : Fin d) :
    inner ℝ F (scalarToVectorL2 M.P.toMeasure (Pi.single i 1) X) =
      inner ℝ (Stationary.vectorL2Coord (mu := M.P.toMeasure) i F) X := by
  rw [real_inner_comm, inner_scalarToVectorL2_basis, real_inner_comm]

/-- The vector of all coordinate derivatives of a smooth stationary scalar
mollification. -/
def mollifiedGradientL2 {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (kappa : Vec d → ℝ) (X : Stationary.ScalarL2 M.P.toMeasure) :
    Stationary.VectorL2 d M.P.toMeasure :=
  letI := potentialSequenceVAddInvariant M
  assembleScalarCoordinates M fun i =>
    Stationary.mollifyL2 (mu := M.P.toMeasure)
      (Stationary.kernelDeriv kappa i) X

/-- A smooth stationary mollification has the assembled kernel-derivative
field as its strong horizontal gradient. -/
theorem hasHorizontalGradient_mollifyL2 {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa)
    (X : Stationary.ScalarL2 M.P.toMeasure)
    (hX : letI := potentialSequenceVAddInvariant M
      Continuous (fun z : Vec d =>
        Stationary.koopman (mu := M.P.toMeasure) z X)) :
    letI := potentialSequenceVAddInvariant M
    Stationary.HasHorizontalGradient (mu := M.P.toMeasure)
      (Stationary.mollifyL2 (mu := M.P.toMeasure) kappa X)
      (mollifiedGradientL2 M kappa X) := by
  let := potentialSequenceVAddInvariant M
  intro i
  rw [mollifiedGradientL2, vectorL2Coord_assembleScalarCoordinates]
  exact Stationary.hasDerivAt_koopman_mollifyL2_of_continuous
    hcompact hkappa X hX i

/-- Hessian rows of a smooth stationary scalar mollification. -/
def mollifiedHessianRowL2 {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (kappa : Vec d → ℝ) (X : Stationary.ScalarL2 M.P.toMeasure)
    (k : Fin d) : Stationary.VectorL2 d M.P.toMeasure :=
  mollifiedGradientL2 M (Stationary.kernelDeriv kappa k) X

/-- Every row of the mollified gradient has the corresponding Hessian row
as its strong horizontal gradient. -/
theorem hasHorizontalGradient_vectorL2Coord_mollifiedGradientL2 {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa)
    (X : Stationary.ScalarL2 M.P.toMeasure)
    (hX : letI := potentialSequenceVAddInvariant M
      Continuous (fun z : Vec d =>
        Stationary.koopman (mu := M.P.toMeasure) z X))
    (k : Fin d) :
    letI := potentialSequenceVAddInvariant M
    Stationary.HasHorizontalGradient (mu := M.P.toMeasure)
      (Stationary.vectorL2Coord (mu := M.P.toMeasure) k
        (mollifiedGradientL2 M kappa X))
      (mollifiedHessianRowL2 M kappa X k) := by
  let := potentialSequenceVAddInvariant M
  rw [mollifiedGradientL2, vectorL2Coord_assembleScalarCoordinates]
  exact hasHorizontalGradient_mollifyL2 M
    (Stationary.hasCompactSupport_kernelDeriv hcompact k)
    (Stationary.contDiff_kernelDeriv hkappa k) X hX

/-- Symmetry of the Hessian of a smooth stationary scalar mollification. -/
theorem vectorL2Coord_mollifiedHessianRowL2_comm {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {kappa : Vec d → ℝ} (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa)
    (X : Stationary.ScalarL2 M.P.toMeasure) (i j : Fin d) :
    Stationary.vectorL2Coord (mu := M.P.toMeasure) i
        (mollifiedHessianRowL2 M kappa X j) =
      Stationary.vectorL2Coord (mu := M.P.toMeasure) j
        (mollifiedHessianRowL2 M kappa X i) := by
  rw [mollifiedHessianRowL2, mollifiedHessianRowL2,
    mollifiedGradientL2, mollifiedGradientL2,
    vectorL2Coord_assembleScalarCoordinates,
    vectorL2Coord_assembleScalarCoordinates,
    Stationary.kernelDeriv_kernelDeriv_comm hkappa j i]

/-- A smooth stationary scalar mollification with zero stationary Laplacian
has zero horizontal gradient. -/
theorem mollifiedGradientL2_eq_zero_of_sum_secondDeriv_eq_zero {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa)
    (X : Stationary.ScalarL2 M.P.toMeasure)
    (hX : letI := potentialSequenceVAddInvariant M
      Continuous (fun z : Vec d =>
        Stationary.koopman (mu := M.P.toMeasure) z X))
    (hlap : letI := potentialSequenceVAddInvariant M
      (∑ i : Fin d, Stationary.mollifyL2 (mu := M.P.toMeasure)
        (Stationary.kernelDeriv (Stationary.kernelDeriv kappa i) i) X) = 0) :
    mollifiedGradientL2 M kappa X = 0 := by
  let := potentialSequenceVAddInvariant M
  classical
  let Z := Stationary.mollifyL2 (mu := M.P.toMeasure) kappa X
  let G := mollifiedGradientL2 M kappa X
  let H : Fin d → Stationary.VectorL2 d M.P.toMeasure := fun i =>
    mollifiedHessianRowL2 M kappa X i
  have hG : Stationary.HasHorizontalGradient (mu := M.P.toMeasure) Z G :=
    hasHorizontalGradient_mollifyL2 M hcompact hkappa X hX
  have hH : ∀ i : Fin d,
      Stationary.HasHorizontalGradient (mu := M.P.toMeasure)
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) i G) (H i) := by
    intro i
    exact hasHorizontalGradient_vectorL2Coord_mollifiedGradientL2
      M hcompact hkappa X hX i
  have hdiag : (∑ i : Fin d,
      Stationary.vectorL2Coord (mu := M.P.toMeasure) i (H i)) = 0 := by
    dsimp only [H, mollifiedHessianRowL2, mollifiedGradientL2]
    simpa only [vectorL2Coord_assembleScalarCoordinates] using hlap
  have hGG : inner ℝ G G = 0 := by
    rw [Stationary.inner_vectorL2_eq_sum_inner_coord]
    calc
      (∑ i : Fin d, inner ℝ
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) i G)
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) i G)) =
          ∑ i : Fin d, -inner ℝ Z
            (Stationary.vectorL2Coord (mu := M.P.toMeasure) i (H i)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hG.inner_coord_eq_neg_inner_coord (hH i) i
      _ = -inner ℝ Z (∑ i : Fin d,
          Stationary.vectorL2Coord (mu := M.P.toMeasure) i (H i)) := by
        rw [inner_sum, Finset.sum_neg_distrib]
      _ = 0 := by simp [hdiag]
  rw [real_inner_self_eq_norm_sq] at hGG
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hGG)

/-- The divergence of a smooth stationary vector mollification. -/
def mollifiedDivergenceL2 {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (kappa : Vec d → ℝ)
    (R : Stationary.VectorL2 d M.P.toMeasure) :
    Stationary.ScalarL2 M.P.toMeasure :=
  letI := potentialSequenceVAddInvariant M
  ∑ i : Fin d, Stationary.mollifyL2 (mu := M.P.toMeasure)
    (Stationary.kernelDeriv kappa i)
    (Stationary.vectorL2Coord (mu := M.P.toMeasure) i R)

/-- The smooth divergence has a strong horizontal gradient. -/
theorem hasHorizontalGradient_mollifiedDivergenceL2 {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa)
    (R : Stationary.VectorL2 d M.P.toMeasure)
    (hR : letI := potentialSequenceVAddInvariant M
      Continuous (fun z : Vec d =>
        Stationary.koopman (mu := M.P.toMeasure) z R)) :
    letI := potentialSequenceVAddInvariant M
    ∃ G : Stationary.VectorL2 d M.P.toMeasure,
      Stationary.HasHorizontalGradient (mu := M.P.toMeasure)
        (mollifiedDivergenceL2 M kappa R) G := by
  let := potentialSequenceVAddInvariant M
  classical
  have hcoord : ∀ i : Fin d, Continuous (fun z : Vec d =>
      Stationary.koopman (mu := M.P.toMeasure) z
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) i R)) := by
    intro i
    have hc := (Stationary.vectorL2Coord
      (mu := M.P.toMeasure) i).continuous.comp hR
    convert hc using 1
    funext z
    exact Stationary.koopman_vectorL2Coord z i R
  have hs : ∀ s : Finset (Fin d),
      ∃ G : Stationary.VectorL2 d M.P.toMeasure,
        Stationary.HasHorizontalGradient (mu := M.P.toMeasure)
          (∑ i ∈ s, Stationary.mollifyL2 (mu := M.P.toMeasure)
            (Stationary.kernelDeriv kappa i)
            (Stationary.vectorL2Coord (mu := M.P.toMeasure) i R)) G := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨0, Stationary.hasHorizontalGradient_zero⟩
    | @insert i s his ih =>
      obtain ⟨G, hG⟩ := ih
      let phi := Stationary.mollifyL2 (mu := M.P.toMeasure)
        (Stationary.kernelDeriv kappa i)
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) i R)
      let F := mollifiedGradientL2 M (Stationary.kernelDeriv kappa i)
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) i R)
      have hphi : Stationary.HasHorizontalGradient (mu := M.P.toMeasure)
          phi F :=
        hasHorizontalGradient_mollifyL2 M
          (Stationary.hasCompactSupport_kernelDeriv hcompact i)
          (Stationary.contDiff_kernelDeriv hkappa i)
          (Stationary.vectorL2Coord (mu := M.P.toMeasure) i R) (hcoord i)
      rw [Finset.sum_insert his]
      exact ⟨F + G, hphi.add hG⟩
  simpa only [mollifiedDivergenceL2, Finset.sum_filter, Finset.mem_univ,
    ite_true] using hs Finset.univ

/-- A strongly continuous solenoidal stationary field has zero divergence
after every smooth compactly supported stationary mollification. -/
theorem mollifiedDivergenceL2_eq_zero_of_mem_solenoidal {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa)
    (R : Stationary.VectorL2 d M.P.toMeasure)
    (hR : letI := potentialSequenceVAddInvariant M
      Continuous (fun z : Vec d =>
        Stationary.koopman (mu := M.P.toMeasure) z R))
    (hsol : letI := potentialSequenceVAddInvariant M
      R ∈ Stationary.stationarySolenoidalSubspace
        (mu := M.P.toMeasure) (d := d)) :
    mollifiedDivergenceL2 M kappa R = 0 := by
  let := potentialSequenceVAddInvariant M
  classical
  let D := mollifiedDivergenceL2 M kappa R
  let S := Stationary.mollifyL2 (mu := M.P.toMeasure) kappa R
  obtain ⟨G, hD⟩ := hasHorizontalGradient_mollifiedDivergenceL2
    M hcompact hkappa R hR
  have hGpot : G ∈ Stationary.stationaryPotentialSubspace
      (mu := M.P.toMeasure) (d := d) :=
    Submodule.le_topologicalClosure
      (Stationary.horizontalGradientRange (mu := M.P.toMeasure) (d := d))
      ⟨D, hD⟩
  have hSsol : S ∈ Stationary.stationarySolenoidalSubspace
      (mu := M.P.toMeasure) (d := d) :=
    Stationary.mollifyL2_mem_stationarySolenoidalSubspace_of_continuous
      hkappa.continuous hcompact hsol hR
  have horth : inner ℝ G S = 0 :=
    Stationary.inner_eq_zero_of_mem_potential_of_mem_solenoidal hGpot hSsol
  have hcoordR : ∀ i : Fin d, Continuous (fun z : Vec d =>
      Stationary.koopman (mu := M.P.toMeasure) z
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) i R)) := by
    intro i
    have hc := (Stationary.vectorL2Coord
      (mu := M.P.toMeasure) i).continuous.comp hR
    convert hc using 1
    funext z
    exact Stationary.koopman_vectorL2Coord z i R
  have hterm : ∀ i : Fin d,
      inner ℝ (Stationary.vectorL2Coord (mu := M.P.toMeasure) i G)
          (Stationary.vectorL2Coord (mu := M.P.toMeasure) i S) =
        -inner ℝ D
          (Stationary.mollifyL2 (mu := M.P.toMeasure)
            (Stationary.kernelDeriv kappa i)
            (Stationary.vectorL2Coord (mu := M.P.toMeasure) i R)) := by
    intro i
    let H := mollifiedGradientL2 M kappa
      (Stationary.vectorL2Coord (mu := M.P.toMeasure) i R)
    have hSi : Stationary.HasHorizontalGradient (mu := M.P.toMeasure)
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) i S) H := by
      dsimp only [S]
      rw [Stationary.vectorL2Coord_mollifyL2_of_continuous
        (mu := M.P.toMeasure) hkappa.continuous hcompact R hR]
      exact hasHorizontalGradient_mollifyL2 M hcompact hkappa
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) i R) (hcoordR i)
    have hibp := hD.inner_coord_eq_neg_inner_coord hSi i
    dsimp only [H] at hibp
    rw [mollifiedGradientL2,
      vectorL2Coord_assembleScalarCoordinates] at hibp
    exact hibp
  rw [Stationary.inner_vectorL2_eq_sum_inner_coord] at horth
  have hsum :
      (∑ i : Fin d,
        inner ℝ (Stationary.vectorL2Coord (mu := M.P.toMeasure) i G)
          (Stationary.vectorL2Coord (mu := M.P.toMeasure) i S)) =
        -inner ℝ D D := by
    calc
      _ = ∑ i : Fin d, -inner ℝ D
          (Stationary.mollifyL2 (mu := M.P.toMeasure)
            (Stationary.kernelDeriv kappa i)
            (Stationary.vectorL2Coord (mu := M.P.toMeasure) i R)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hterm i
      _ = -inner ℝ D (∑ i : Fin d,
          Stationary.mollifyL2 (mu := M.P.toMeasure)
            (Stationary.kernelDeriv kappa i)
            (Stationary.vectorL2Coord (mu := M.P.toMeasure) i R)) := by
        rw [inner_sum]
        simp only [Finset.sum_neg_distrib]
      _ = -inner ℝ D D := by rfl
  rw [horth] at hsum
  have hDD : inner ℝ D D = 0 := by linarith
  have hDzero : D = 0 := by
    rw [real_inner_self_eq_norm_sq] at hDD
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hDD)
  exact hDzero

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
