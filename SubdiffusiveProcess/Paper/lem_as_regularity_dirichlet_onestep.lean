module

public import SubdiffusiveProcess.Paper.lem_as_regularity_actual_dirichlet
public import SubdiffusiveProcess.Paper.lem_as_regularity_dirichlet_window
public import SubdiffusiveProcess.Paper.lem_as_regularity_actual_root

@[expose] public section

/-! The original native allowance yields physical Dirichlet window decay.
This deterministic receiver does not supply a probabilistic allowance bound. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open Homogenization hiding Vec
open scoped ENNReal BigOperators Pointwise
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- One admissible original allowance bounds the physical Dirichlet oscillation window. -/
theorem lem_as_regularity_dirichlet_onestep (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d,ℝ)] [BorelSpace C(SpatialCoordinates d,ℝ)]
    (E : in_J d) (D : lane4_deterministic_good_scale_input d) (rho : ℝ) (hrho : 0 < rho) :
    ∃ eps rate delta0 C Cp : ℝ, eps ∈ Ioo (0:ℝ) 1 ∧ 0 < rate ∧ 0 < delta0 ∧ 0 < C ∧ 0 < Cp ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
      (H : BilateralField d → C(SpatialCoordinates d,ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
    ∀ (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
      (Fs Ps Rs Draw : ℕ → ℕ → Vec d → BilateralField d → ℝ≥0∞)
      (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
      (good : ℕ → ℕ → Vec d → BilateralField d → Prop),
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,∀ N i y,
        eta N omega i y = omega ((i:ℤ)-(N:ℤ)) ((3:ℝ)^(-(N:ℤ)) • y)) →
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,∀ N,
        primitive_scores d M (1/32) eps (eta N omega)
          (fun m y => Fs N m y omega) (fun m y => Ps N m y omega)
          (fun m y => Rs N m y omega) (fun m y => Draw N m y omega)
          (fun m y => Z N m y omega) (fun m y => good N m y omega)) →
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
    ∀ N k : ℕ,k ≤ N → ∀ w ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
      nativeScoreAllowance (fun j => Z N j ((3:ℝ)^N • w) omega)
        (fun j => Draw N j ((3:ℝ)^N • w) omega) N rate ≤ k →
    ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),0 ≤ Kf →
      AEMeasurable F (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
      (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),|F y| ≤ Kf) →
    ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),ContDiff ℝ 2 phi →
      c2Norm (closedCube (fun _ : Fin d => (1/2:ℝ)) 1 one_pos : Set (SpatialCoordinates d)) phi ≤ Cphi →
    ∀ b u : weakSobolevGraph (unitNeumannCube d),
      ((b : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] phi →
      SolvesDirichlet (cutoffPositiveCoefficient M H omega N (fun _ => (1/2:ℝ)) one_pos) F b u →
    ∀ Ks : ℝ,0 ≤ Ks →
      (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
        |((u : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ) y| ≤ Ks) →
      let W := Metric.ball w ((9/2:ℝ)*(3:ℝ)^(-(k:ℤ))) ∩ (unitNeumannCube d : Set (SpatialCoordinates d))
      normalizedL2On W (fun y => (u : SobolevData (unitNeumannCube d)).1 y-
        averageOn W ((u : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)) ≤
        C*(3:ℝ)^(-((1-rho)*k))*(243*Ks+(d:ℝ)*Cphi+
          (aux_in_deterministic_onestep_sref M H omega N 0 w)⁻¹*Cp*Kf) := by
  obtain ⟨eps,rate,delta0,C,heps,hrate,hd0,hC,hiter⟩ := lem_as_regularity_actual_dirichlet d hd E D rho hrho
  obtain ⟨Cp,hCp,hwindow⟩ := lem_as_regularity_dirichlet_window d hd
  refine ⟨eps,rate,delta0,9*C,Cp,heps,hrate,hd0,by positivity,hCp,?_⟩
  intro M Rm H hIR hdelta eta Fs Ps Rs Draw Z good hEta hPS
  filter_upwards [hiter M Rm H hIR hdelta eta Fs Ps Rs Draw Z good hEta hPS] with omega hi
  intro N k hkN w hw hallow F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol Ks hKs hsup W
  have hallow' : nativeScoreAllowance (fun j => Z N j ((3:ℝ)^N • w) omega)
      (fun j => Draw N j ((3:ℝ)^N • w) omega) N rate ≤ N-(N-k) := by omega
  have hgap := (nativeScoreAllowance_window (fun j => Z N j ((3:ℝ)^N • w) omega)
    (fun j => Draw N j ((3:ℝ)^N • w) omega) N (N-k) rate (Nat.sub_le _ _) hallow').1
  have hk : 26 ≤ k := by omega
  let z0 : SpatialCoordinates d := fun _ => (1/2:ℝ)
  have hR : (0:ℝ) < 3^N := by positivity
  obtain ⟨aT,haT,hcoef⟩ := aux_lem_as_regularity_actual_root_dilate M H omega N _ hR
  have ha : ∀ᵐ y ∂volume.restrict (openCubeSet (originCube d N)),
      cutoffCoefficient M H omega N ((3:ℝ)^(-(N:ℤ)) • y+z0) = aT.val (y+(3:ℝ)^N • z0) := by
    let coeff : SpatialCoordinates d → ℝ := aT.val
    change coeff =ᵐ[volume.restrict (centeredCube ((3:ℝ)^N • z0) ((3:ℝ)^N) hR : Set (SpatialCoordinates d))] _ at haT
    rw [centeredCube_eq_translateSet_cube N _ hR] at haT
    have hp := aux_in_deterministic_core_ae_affine (R := 1) zero_lt_one
      ((3:ℝ)^N • z0) (cube d N) (by simpa only [one_smul] using! haT)
    filter_upwards [hp] with y hy
    rw [one_smul,smul_add,smul_smul,inv_mul_cancel₀ hR.ne',one_smul] at hy
    rw [show ((3:ℝ)^N)⁻¹=(3:ℝ)^(-(N:ℤ)) by rw [zpow_neg,zpow_natCast]] at hy
    exact hy.symm
  let data := continuousScalarFamily (fun y => cutoffCoefficient M H omega N
    ((3:ℝ)^(-(N:ℤ)) • (y+(3:ℝ)^N • (w-z0))+z0))
    ((cutoffCoefficient_continuous M H omega N).comp (by fun_prop))
    (fun y => cutoffCoefficient_pos M H omega N _)
  have hnw := cutoff_nativeCentre_mem_cube N w z0 hw
  have hout := hwindow N k hk hkN z0 w hw
    (cutoffPositiveCoefficient M H omega N z0 one_pos) aT _ hcoef ha
    (C*(3:ℝ)^(rho*k)) (aux_in_deterministic_onestep_sref M H omega N 0 w)
    (by positivity) (aux_in_deterministic_onestep_sref_pos M H omega N 0 w) (by
      intro un hn gn hdir hgn hhn
      have hF := exists_fractionalOrder_memCubeEuclideanFullWsp_of_memHolder
        (by omega : 1 ≤ d) (by norm_num : (0:ℝ)<1/4) le_rfl hgn
      have hh := hi N N (N-k) (Nat.sub_le _ _) w z0 hnw hallow' data un hn gn hdir hF hgn hhn
      rw [sub_self,Nat.cast_sub hkN,sub_sub_cancel] at hh
      exact hh)
    F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol Ks hKs hsup
  have hpow : (3:ℝ)^(rho*k)*(3:ℝ)^(-(k:ℤ)) = (3:ℝ)^(-((1-rho)*k)) := by
    rw [← Real.rpow_intCast,← Real.rpow_add (by norm_num)]
    congr 1
    push_cast
    ring
  have hid : 9*(C*(3:ℝ)^(rho*k))*(3:ℝ)^(-(k:ℤ)) = (9*C)*(3:ℝ)^(-((1-rho)*k)) := by
    calc _ = (9*C)*((3:ℝ)^(rho*k)*(3:ℝ)^(-(k:ℤ))) := by ring
         _ = _ := by rw [hpow]
  rw [hid] at hout
  exact hout

end SubdiffusiveProcess.Paper
