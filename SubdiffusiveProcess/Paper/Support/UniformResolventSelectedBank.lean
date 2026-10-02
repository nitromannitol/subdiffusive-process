import SubdiffusiveProcess.Paper.Support.UniformResolventInputs
import SubdiffusiveProcess.Paper.Support.UniformResolventEnvelope
import SubdiffusiveProcess.Paper.Support.UniformResolventSelectedIdentification

/-!
Internal proof support for the unconditional killed-resolvent proposition.
These declarations are not paper statement principals.
Supports: mfd_prop_uniform_resolvent
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess
open SubdiffusiveProcess SubdiffusiveProcess.Lane4 SubdiffusiveProcess.Section9 SubdiffusiveProcess.Analysis
open scoped ENNReal NNReal
noncomputable section
namespace Paper

theorem aux_mfd_prop_uniform_resolvent_selected_bank
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cp : CampanatoInput d) (Interp : CubeFractionalInterpolationInput d hd)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon' : epsilon < 1 / (8 * ((d : ℝ) + 2)))
    (q : ℝ) (hq : 1 ≤ q)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (A : aux_mfd_prop_uniform_resolvent_Inputs d hd M H KN epsilon q)
    (psi : ℕ → ℕ) (hpsi : StrictMono psi) :
    ∃ (phi : ℕ → ℕ), StrictMono phi ∧
      ∃ (R : ℕ → ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ → BilateralField d → C(SpatialCoordinates d, ℝ))
        (B : ℕ → BilateralField d → ℝ),
        (∀ i, Measurable (B i) ∧ (∀ omega, 0 ≤ B i omega) ∧ MemLp (B i) (ENNReal.ofReal (q / 2)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i lam, 0 < lam → ∀ f, Measurable (R i lam f)) ∧
        (∀ i lam, 0 < lam → ∀ f, ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
          ∃ N0 : ℕ, ∀ N, N0 ≤ N → (chaosSampleLaw M).toMeasure
            {omega | ∃ x ∈ closure (determiningCube d i : Set (SpatialCoordinates d)), eps ≤
              |killedOccupationResolvent (determiningCube d i) KN (psi (phi N)) omega lam f x - R i lam f omega x|} ≤
              ENNReal.ofReal rho) ∧
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ i,
          (∀ N lam, 0 < lam → ∀ f, ContinuousOn (killedOccupationResolvent (determiningCube d i) KN N omega lam f)
            (closure (determiningCube d i : Set (SpatialCoordinates d))) ∧
            ∀ x ∈ frontier (determiningCube d i : Set (SpatialCoordinates d)),
              killedOccupationResolvent (determiningCube d i) KN N omega lam f x = 0) ∧
          ∀ lam, 0 < lam → ∀ f,
            ((R i lam f omega : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (determiningCube d i : Set (SpatialCoordinates d))]
              ((A.O i omega).ustar lam f : SpatialCoordinates d → ℝ)) ∧
            (∀ x ∉ (determiningCube d i : Set (SpatialCoordinates d)), R i lam f omega x = 0) ∧
            (∀ x ∈ closure (determiningCube d i : Set (SpatialCoordinates d)), |R i lam f omega x| ≤ ‖f‖ / lam) ∧
            (∀ x ∈ closure (determiningCube d i : Set (SpatialCoordinates d)), |R i lam f omega x| ≤ B i omega * ‖f‖) ∧
            ∀ x ∈ closure (determiningCube d i : Set (SpatialCoordinates d)), ∀ y ∈ closure (determiningCube d i : Set (SpatialCoordinates d)),
              |R i lam f omega x - R i lam f omega y| ≤ B i omega * ‖f‖ * dist x y ^ (1 / 4 : ℝ)) := by
  classical
  let P := (chaosSampleLaw M).toMeasure
  let RN := fun i N omega lam f => killedOccupationResolvent (determiningCube d i) KN N omega lam f
  have hepsilon1 : epsilon < 1 := by
    refine hepsilon'.trans ?_
    rw [div_lt_one (by positivity)]
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  let beta := 1 / 2 - ((d : ℝ) + 2) * epsilon
  have hbeta : 1 / 4 ≤ beta :=
    (aux_prop_uniform_resolvent_cutoff_oscillation_exponent hd epsilon hepsilon hepsilon').le
  obtain ⟨phi, hphi, hMosco⟩ := aux_mfd_prop_uniform_resolvent_common_mosco_subsequence
    d M H A.G A.hGconv psi hpsi
  let theta := fun n => psi (phi n)
  have htheta : StrictMono theta := hpsi.comp hphi
  have hosc := fun i => aux_mfd_prop_uniform_resolvent_oscillation_family hd epsilon hepsilon hepsilon1
    (A.Qroot i) (rationalTriadicCenter d i) (rationalTriadicSide d i) (rationalTriadicSide_pos d i)
    (A.hroot i) M H (RN i) (A.uN i) (A.Kmu i) (A.Kcoer i) (A.Khol i)
    (A.hgrowth.mono fun omega h => ⟨(h i).1, fun N => A.hKnonneg i N omega⟩)
    (A.hgrowth.mono fun omega h x hx rho hrho hrho1 N =>
      (h i).2.1 N x (A.hrootRegion i hx) rho hrho hrho1)
    (A.hcoer.mono fun omega h N v => ⟨(h i N v).1, (h i N v).2.1⟩)
    (A.hHolder.mono fun omega h => h i)
    (A.hfinite.mono fun omega h N lam hlam f =>
      ⟨(h i N lam hlam f).1, fun x _ => A.hRNbound i N omega lam hlam f x, (h i N lam hlam f).2.1⟩)
  choose V hV hvar using hosc
  have hEnv := fun i => aux_mfd_prop_uniform_resolvent_envelope hd Cp P
    (rationalTriadicCenter d i) (rationalTriadicSide d i) (rationalTriadicSide_pos d i)
    epsilon beta hbeta (V i) (hV i)
    (fun n => RN i (theta n)) (fun n omega lam f => (A.uN i (theta n) omega lam f).val.1)
    (A.Kmu i) (fun n => A.Kcoer i (theta n)) (fun n => A.Khol i (theta n)) q hq
    ⟨A.hKmuMeas i, fun n => (A.hKmeas i (theta n)).1, fun n => (A.hKmeas i (theta n)).2⟩
    (A.hgrowth.mono fun omega h => ⟨(h i).1, fun n => A.hKnonneg i (theta n) omega⟩)
    ⟨A.hKmuMom i, ⟨A.Cbound i, fun n =>
      ⟨ENNReal.toReal_le_of_le_ofReal (A.hCbound i) (A.hKbound i (theta n)).1,
        ENNReal.toReal_le_of_le_ofReal (A.hCbound i) (A.hKbound i (theta n)).2⟩⟩,
      fun n => A.hKmom i (theta n)⟩
    ((hvar i).mono fun omega h n => h (theta n))
    (A.hfinite.mono fun omega h n lam hlam f => (h i (theta n) lam hlam f).1)
    (A.hpoint.mono fun omega h n => h i (theta n))
  choose B hBm hB0 hBp hcampK hstrong hregularSelected using hEnv
  have hRegularFull := fun i => aux_mfd_prop_uniform_resolvent_envelope hd Cp P
    (rationalTriadicCenter d i) (rationalTriadicSide d i) (rationalTriadicSide_pos d i)
    epsilon beta hbeta (V i) (hV i) (RN i) (fun n omega lam f => (A.uN i n omega lam f).val.1)
    (A.Kmu i) (A.Kcoer i) (A.Khol i) q hq
    ⟨A.hKmuMeas i, fun n => (A.hKmeas i n).1, fun n => (A.hKmeas i n).2⟩
    (A.hgrowth.mono fun omega h => ⟨(h i).1, fun n => A.hKnonneg i n omega⟩)
    ⟨A.hKmuMom i, ⟨A.Cbound i, fun n =>
      ⟨ENNReal.toReal_le_of_le_ofReal (A.hCbound i) (A.hKbound i n).1,
        ENNReal.toReal_le_of_le_ofReal (A.hCbound i) (A.hKbound i n).2⟩⟩, fun n => A.hKmom i n⟩
    (hvar i) (A.hfinite.mono fun omega h n lam hlam f => (h i n lam hlam f).1)
    (A.hpoint.mono fun omega h => h i)
  have hRegular : ∀ i, ∀ᵐ omega ∂P, ∀ N lam, 0 < lam → ∀ f,
      ContinuousOn (RN i N omega lam f) (closure (determiningCube d i : Set (SpatialCoordinates d))) ∧
      ∀ x ∈ frontier (determiningCube d i : Set (SpatialCoordinates d)), RN i N omega lam f x = 0 := by
    intro i
    obtain ⟨_, _, _, _, _, _, h⟩ := hRegularFull i
    exact h
  have hident : ∀ i, ∀ᵐ omega ∂P, ∀ lam, 0 < lam → ∀ f,
      ∀ g : C(SpatialCoordinates d, ℝ), ∀ Mb : ℕ,
        (∃ sigma : ℕ → ℕ, StrictMono sigma ∧
          (∀ k, A.Kcoer i (theta (sigma k)) omega ≤ Mb ∧ A.Khol i (theta (sigma k)) omega ≤ Mb) ∧
          ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k →
            ∀ x ∈ closure (determiningCube d i : Set (SpatialCoordinates d)),
              |RN i (theta (sigma k)) omega lam f x - g x| < eps) →
        ((g : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (determiningCube d i : Set (SpatialCoordinates d))]
          ((A.O i omega).ustar lam f : SpatialCoordinates d → ℝ)) := by
    intro i
    filter_upwards [A.hmu, A.hgrowth, A.hcoer, A.hForm, A.hfinite, hMosco]
      with omega hm hgr hc hf hfi hmo lam hlam f g Mb hcluster
    obtain ⟨sigma, hsigma, hb, hu⟩ := hcluster
    haveI := hm.2.1
    have hfin := (centeredCube_isBounded (rationalTriadicCenter d i) (rationalTriadicSide_pos d i)).isCompact_closure.measure_lt_top (μ := A.muFull omega)
    rcases hf i with ⟨hKt, hCt, _, hT, hJ, _, hminall⟩
    obtain ⟨hufin, hmin, huniq⟩ := hminall lam hlam f
    exact aux_mfd_prop_uniform_resolvent_ident_selected_sample hd epsilon hepsilon'
      (rationalTriadicCenter d i) (rationalTriadicSide d i) (rationalTriadicSide_pos d i)
      M H omega theta (A.Region i) (A.hNeighborhood i) (A.muFull omega)
      ⟨fun test => (hm.1 test).comp htheta.tendsto_atTop, hm.2.2.2.2 i, hfin⟩
      (A.Kmu i omega) (hgr i).1
      (fun x hx r hr hr1 => ⟨(hgr i).2.2 x hx r hr hr1, fun N => (hgr i).2.1 (theta N) x hx r hr hr1⟩)
      (fun u => (limitFormEnergy (A.G i omega) u).toENNReal) ⟨(hmo i).2.2.2.1, (hmo i).2.2.2.2⟩
      (A.O i omega).T (A.Kmu i omega) (A.O i omega).Ctrace ⟨hKt, hCt, hT⟩
      (A.lift i omega) (A.hlift i omega) (A.O i omega).J hJ lam hlam f ((A.O i omega).ustar lam f)
      ⟨hufin, fun u hu => (hmin u hu).2.2, huniq⟩
      (fun N => A.uN i (theta N) omega lam f) (fun N => RN i (theta N) omega lam f)
      (fun N => hfi i (theta N) lam hlam f) (fun N => A.Kcoer i (theta N) omega)
      (fun N v => (hc i (theta N) v).2.2) Interp g Mb sigma hsigma (fun k => (hb k).1) hu
  have hReduction := fun i => aux_mfd_prop_uniform_resolvent_selected_reduction P
    (rationalTriadicCenter d i) (rationalTriadicSide d i) (rationalTriadicSide_pos d i) beta hbeta
    (fun N => RN i (theta N)) (fun N omega lam f => (A.uN i (theta N) omega lam f).val.1)
    (fun omega => (A.O i omega).ustar) (fun N => A.Kcoer i (theta N)) (fun N => A.Khol i (theta N))
    (fun N => A.hKmeas i (theta N)) (fun N => A.hRNmeas i (theta N))
    (aux_prop_uniform_resolvent_tight_levels P _ _ q hq
      ⟨A.Cbound i, fun N =>
        ⟨ENNReal.toReal_le_of_le_ofReal (A.hCbound i) (A.hKbound i (theta N)).1,
          ENNReal.toReal_le_of_le_ofReal (A.hCbound i) (A.hKbound i (theta N)).2⟩⟩
      (fun N => A.hKmom i (theta N)))
    (hcampK i)
    (A.hfinite.mono fun omega h N lam hlam f =>
      ⟨(h i (theta N) lam hlam f).1, fun x _ => A.hRNbound i (theta N) omega lam hlam f x⟩)
    (SubdiffusiveProcess.Analysis.exists_zero_extension_holder_of_mean_oscillation Cp)
    (A.hpoint.mono fun omega h N => h i (theta N)) (hident i) (B i) (hstrong i)
  choose R _ hRm hRprob _ _ hRstrong hRmin using hReduction
  refine ⟨phi, hphi, R, B, fun i => ⟨hBm i, hB0 i, hBp i⟩, hRm, hRprob, ?_⟩
  filter_upwards [ae_all_iff.mpr hRegular, ae_all_iff.mpr hRstrong, ae_all_iff.mpr hRmin]
    with omega hr hs hm i
  refine ⟨hr i, fun lam hlam f => ?_⟩
  obtain ⟨hae, hzero, hcontract⟩ := hm i lam hlam f
  obtain ⟨hbound, hholder⟩ := hs i lam hlam f
  exact ⟨hae, hzero, hcontract, hbound, hholder⟩

end Paper
