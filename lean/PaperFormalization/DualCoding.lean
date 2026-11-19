import PaperFormalization.DualBallModel
import PaperFormalization.EffrosHyperspace
import PaperFormalization.EffrosStandard

namespace PaperFormalization

open Filter Set Topology TopologicalSpace
open scoped ENNReal

section Normalize

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private noncomputable def normalize (x : E) : E := (max (1 : ℝ) ‖x‖)⁻¹ • x

private theorem norm_normalize_le (x : E) : ‖normalize x‖ ≤ 1 := by
  have hpos : 0 < max (1 : ℝ) ‖x‖ := zero_lt_one.trans_le (le_max_left _ _)
  rw [normalize, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hpos.le), ← div_eq_inv_mul,
    div_le_iff₀ hpos, one_mul]
  exact le_max_right _ _

private theorem normalize_eq_of_norm_le {x : E} (hx : ‖x‖ ≤ 1) : normalize x = x := by
  simp [normalize, max_eq_left hx]

private theorem continuous_normalize : Continuous (normalize (E := E)) :=
  ((continuous_const.max continuous_norm).inv₀ fun _ =>
    (zero_lt_one.trans_le (le_max_left _ _)).ne').smul continuous_id

end Normalize

theorem exists_borel_unitBall_selectors :
    ∃ d : ℕ → BanachCode → BanachAmbient, (∀ i, Measurable (d i)) ∧
      ∀ X, closure (range fun i => d i X) =
        Metric.closedBall (0 : BanachAmbient) 1 ∩ (X.val : Set BanachAmbient) := by
  obtain ⟨s, hs, hd⟩ := ClosedSubspaces.exists_borel_dense_selectors (E := BanachAmbient)
  refine ⟨fun n X => normalize (s n X), fun n => continuous_normalize.measurable.comp (hs n), ?_⟩
  intro X
  apply le_antisymm
  · refine closure_minimal ?_ (Metric.isClosed_closedBall.inter X.property)
    rintro _ ⟨n, rfl⟩
    exact ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using norm_normalize_le (s n X),
      X.val.smul_mem _ (show s n X ∈ (X.val : Set BanachAmbient) from
        hd X ▸ subset_closure (mem_range_self n))⟩
  · intro x hx
    have hnx : normalize x = x := normalize_eq_of_norm_le (by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx.1)
    have hmem : x ∈ closure (range fun n => s n X) := (hd X).symm ▸ hx.2
    have h := image_closure_subset_closure_image continuous_normalize
      (mem_image_of_mem normalize hmem)
    rwa [hnx, ← range_comp] at h

/-- Fixed Borel coordinates dense in each coded closed unit ball. -/
noncomputable def unitBallSelector : ℕ → BanachCode → BanachAmbient :=
  Classical.choose exists_borel_unitBall_selectors

theorem measurable_unitBallSelector (n : ℕ) : Measurable (unitBallSelector n) :=
  (Classical.choose_spec exists_borel_unitBall_selectors).1 n

theorem closure_range_unitBallSelector (X : BanachCode) :
    closure (range fun n => unitBallSelector n X) =
      Metric.closedBall (0 : BanachAmbient) 1 ∩ (X.val : Set BanachAmbient) :=
  (Classical.choose_spec exists_borel_unitBall_selectors).2 X

private noncomputable def typedSelector (X : BanachCode) (n : ℕ) : X.val :=
  ⟨unitBallSelector n X, (show unitBallSelector n X ∈
    Metric.closedBall (0 : BanachAmbient) 1 ∩ (X.val : Set BanachAmbient) from
      closure_range_unitBallSelector X ▸ subset_closure (mem_range_self n)).2⟩

private theorem closure_range_typedSelector (X : BanachCode) :
    closure (range (typedSelector X)) = Metric.closedBall 0 1 := by
  rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, ← range_comp,
    show Subtype.val ∘ typedSelector X = (fun n => unitBallSelector n X) by rfl,
    closure_range_unitBallSelector]
  ext x
  simp only [mem_preimage, mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
  exact ⟨fun h => h.1, fun h => ⟨h, x.property⟩⟩

/-- The linear isometry from the dual into the normed space of bounded sequences. -/
noncomputable def codedDualEvaluation (X : BanachCode) :
    StrongDual ℝ X.val →ₗᵢ[ℝ] lp (fun _ : ℕ => ℝ) ∞ :=
  dualEvaluationLinearIsometry (typedSelector X) (closure_range_typedSelector X)

private theorem typedSelector_norm_le (X : BanachCode) (n : ℕ) : ‖typedSelector X n‖ ≤ 1 := by
  have h : typedSelector X n ∈ Metric.closedBall (0 : X.val) 1 :=
    closure_range_typedSelector X ▸ subset_closure (mem_range_self n)
  simpa only [Metric.mem_closedBall, dist_zero_right] using h

private noncomputable def weakStarCode (X : BanachCode) (f : WeakStarUnitBall X.val) : DualCube :=
  fun n => ⟨f.val (typedSelector X n), abs_le.mp (by
    have h := f.val.toStrongDual.le_of_opNorm_le (weakStarUnitBall_opNorm_le f) (typedSelector X n)
    have h' : ‖f.val (typedSelector X n)‖ ≤ ‖typedSelector X n‖ := by
      change ‖f.val.toStrongDual (typedSelector X n)‖ ≤ _
      simpa only [one_mul] using h
    exact h'.trans (typedSelector_norm_le X n))⟩

private theorem continuous_weakStarCode (X : BanachCode) : Continuous (weakStarCode X) :=
  continuous_pi fun n =>
    ((WeakDual.eval_continuous (typedSelector X n)).comp continuous_subtype_val).subtype_mk _

private theorem weakStarCode_toLInfinity (X : BanachCode) (f : WeakStarUnitBall X.val) :
    (weakStarCode X f).toLInfinity = codedDualEvaluation X f.val.toStrongDual :=
  lp.ext rfl

/-- The compact weak-star dual-ball code for a coded Banach space. -/
noncomputable def codedDualBall (X : BanachCode) : NonemptyCompacts DualCube :=
  ⟨⟨range (weakStarCode X), isCompact_range (continuous_weakStarCode X)⟩, range_nonempty _⟩

private noncomputable def weakStarRestrict (X : BanachCode) (g : WeakStarUnitBall BanachAmbient) :
    WeakStarUnitBall X.val := by
  let G : StrongDual ℝ X.val := g.val.toStrongDual.comp X.val.subtypeL
  have hg : ‖G‖ ≤ 1 := G.opNorm_le_bound zero_le_one fun x =>
    g.val.toStrongDual.le_of_opNorm_le (weakStarUnitBall_opNorm_le g) x.val
  exact ⟨G.toWeakDual, by simpa only [mem_preimage, StrongDual.toStrongDual_toWeakDual,
    Metric.mem_closedBall, dist_zero_right] using hg⟩

private theorem weakStarRestrict_surjective (X : BanachCode) :
    Function.Surjective (weakStarRestrict X) := by
  intro f
  obtain ⟨G, hG, hnorm⟩ := exists_extension_norm_eq X.val f.val.toStrongDual
  let g : WeakStarUnitBall BanachAmbient :=
    ⟨G.toWeakDual, by simpa only [mem_preimage, StrongDual.toStrongDual_toWeakDual,
        Metric.mem_closedBall, dist_zero_right, hnorm] using weakStarUnitBall_opNorm_le f⟩
  refine ⟨g, Subtype.ext (WeakDual.toStrongDual.injective ?_)⟩
  exact ContinuousLinearMap.ext hG

private theorem continuous_weakStarCode_restrict (X : BanachCode) :
    Continuous (weakStarCode X ∘ weakStarRestrict X) :=
  continuous_pi fun n =>
    ((WeakDual.eval_continuous (unitBallSelector n X)).comp continuous_subtype_val).subtype_mk _

/-- Restricting a fixed countable family of ambient dual functionals gives Borel dense
selectors in all the coded dual balls. -/
theorem exists_borel_codedDualBall_selectors :
    ∃ s : ℕ → BanachCode → DualCube, (∀ n, Measurable (s n)) ∧
      ∀ X, closure (range fun n => s n X) = (codedDualBall X : Set DualCube) := by
  obtain ⟨f, hf⟩ := exists_weakStarUnitBall_denseSeq (E := BanachAmbient)
  let s (n : ℕ) (X : BanachCode) := weakStarCode X (weakStarRestrict X (f n))
  refine ⟨s, fun n => ?_, fun X => ?_⟩
  · apply measurable_pi_lambda
    intro i
    exact ((f n).val.toStrongDual.continuous.measurable.comp
      (measurable_unitBallSelector i)).subtype_mk
  · apply le_antisymm
    · exact closure_minimal (range_subset_iff.mpr fun n => ⟨_, rfl⟩)
        (codedDualBall X).isCompact.isClosed
    · have he : range (weakStarCode X ∘ weakStarRestrict X) =
          (codedDualBall X : Set DualCube) := (weakStarRestrict_surjective X).range_comp (weakStarCode X)
      have h := (continuous_weakStarCode_restrict X).range_subset_closure_image_dense hf
      rw [he, ← range_comp] at h
      exact h

theorem measurable_codedDualBall :
    @Measurable BanachCode (NonemptyCompacts DualCube) _ (borel _) codedDualBall := by
  let _ : MetricSpace DualCube := TopologicalSpace.metrizableSpaceMetric DualCube
  have : Nonempty DualCube := ⟨fun _ => ⟨0, by norm_num⟩⟩
  obtain ⟨s, hs, hS⟩ := exists_borel_codedDualBall_selectors
  exact measurable_nonemptyCompacts_of_dense_selectors s hs hS

private noncomputable def toCodedDualBall (X : BanachCode) :
    WeakStarUnitBall X.val → (codedDualBall X : Set DualCube) :=
  fun f => ⟨weakStarCode X f, mem_range_self f⟩

private theorem bijective_toCodedDualBall (X : BanachCode) :
    Function.Bijective (toCodedDualBall X) := by
  constructor
  · intro f g he
    apply Subtype.ext
    apply WeakDual.toStrongDual.injective
    apply (codedDualEvaluation X).injective
    rw [← weakStarCode_toLInfinity, ← weakStarCode_toLInfinity]
    exact congrArg (DualCube.toLInfinity ∘ Subtype.val) he
  · rintro ⟨_, f, rfl⟩
    exact ⟨f, rfl⟩

private theorem isHomeomorph_toCodedDualBall (X : BanachCode) :
    IsHomeomorph (toCodedDualBall X) :=
  isHomeomorph_iff_continuous_bijective.mpr
    ⟨(continuous_weakStarCode X).subtype_mk _, bijective_toCodedDualBall X⟩

/-- The coding is a weak-star homeomorphism on each dual ball. -/
noncomputable def codedDualBallHomeomorph (X : BanachCode) :
    WeakStarUnitBall X.val ≃ₜ (codedDualBall X : Set DualCube) :=
  Classical.choose (isHomeomorph_iff_exists_homeomorph.mp (isHomeomorph_toCodedDualBall X))

theorem codedDualBallHomeomorph_apply (X : BanachCode) (f : WeakStarUnitBall X.val) :
    codedDualBallHomeomorph X f = toCodedDualBall X f :=
  congrFun (Classical.choose_spec
    (isHomeomorph_iff_exists_homeomorph.mp (isHomeomorph_toCodedDualBall X))) f

private theorem codedDualBallHomeomorph_symm_eval (X : BanachCode)
    (c : (codedDualBall X : Set DualCube)) (n : ℕ) :
    ((codedDualBallHomeomorph X).symm c).val (typedSelector X n) = (c.val n).val := by
  have h := (codedDualBallHomeomorph X).apply_symm_apply c
  rw [codedDualBallHomeomorph_apply] at h
  exact congrArg (fun c : (codedDualBall X : Set DualCube) => (c.val n).val) h

/-- The weak-star cube code has the dual norm when read in ℓ∞. -/
theorem dist_codedDualBallHomeomorph (X : BanachCode) (f g : WeakStarUnitBall X.val) :
    dist (codedDualBallHomeomorph X f).val.toLInfinity
      (codedDualBallHomeomorph X g).val.toLInfinity = dist f.val.toStrongDual g.val.toStrongDual := by
  rw [codedDualBallHomeomorph_apply, codedDualBallHomeomorph_apply]
  change dist ((weakStarCode X f).toLInfinity) ((weakStarCode X g).toLInfinity) = _
  rw [weakStarCode_toLInfinity, weakStarCode_toLInfinity]
  exact (codedDualEvaluation X).isometry.dist_eq _ _

theorem range_codedDualEvaluation (X : BanachCode) :
    (codedDualEvaluation X).toLinearMap.range =
      Submodule.span ℝ (DualCube.toLInfinity '' (codedDualBall X : Set DualCube)) := by
  let W := Submodule.span ℝ (DualCube.toLInfinity '' (codedDualBall X : Set DualCube))
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    let c := max 1 ‖f‖
    have hc : 0 < c := zero_lt_one.trans_le (le_max_left _ _)
    let g : StrongDual ℝ X.val := c⁻¹ • f
    have hg : ‖g‖ ≤ 1 := by
      apply g.opNorm_le_bound zero_le_one
      intro x
      change ‖(c⁻¹ : ℝ) • f x‖ ≤ 1 * ‖x‖
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hc.le)]
      calc
        _ ≤ c⁻¹ * (‖f‖ * ‖x‖) := mul_le_mul_of_nonneg_left (f.le_opNorm x) (inv_nonneg.mpr hc.le)
        _ ≤ 1 * ‖x‖ := by
          rw [← mul_assoc]
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          rw [← div_eq_inv_mul, div_le_iff₀ hc, one_mul]
          exact le_max_right _ _
    let u : WeakStarUnitBall X.val := ⟨g.toWeakDual, by
      simpa only [mem_preimage, StrongDual.toStrongDual_toWeakDual,
        Metric.mem_closedBall, dist_zero_right] using hg⟩
    have hu : codedDualEvaluation X g ∈ W := Submodule.subset_span
      ⟨weakStarCode X u, mem_range_self u, weakStarCode_toLInfinity X u⟩
    have hs : c • g = f := by simp [g, smul_smul, mul_inv_cancel₀ hc.ne']
    change codedDualEvaluation X f ∈ W
    simpa only [← map_smul, hs] using W.smul_mem c hu
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, ⟨f, rfl⟩, rfl⟩
    exact ⟨f.val.toStrongDual, (weakStarCode_toLInfinity X f).symm⟩

/-- The triples on which the parametrized dual pairing is defined. -/
def dualPairingSet : Set (BanachCode × DualCube × BanachAmbient) :=
  {p | p.2.1 ∈ (codedDualBall p.1 : Set DualCube) ∧ p.2.2 ∈ p.1.val}

theorem measurableSet_dualPairingSet : MeasurableSet dualPairingSet := by
  let _ : MetricSpace DualCube := TopologicalSpace.metrizableSpaceMetric DualCube
  obtain ⟨s, hs, hd⟩ := exists_borel_codedDualBall_selectors
  let P := BanachCode × DualCube × BanachAmbient
  have he : {p : P | p.2.1 ∈ (codedDualBall p.1 : Set DualCube)} =
      ⋂ n : ℕ, ⋃ i : ℕ, {p : P | dist p.2.1 (s i p.1) < (1 : ℝ) / (n + 1)} := by
    ext p
    change p.2.1 ∈ (codedDualBall p.1 : Set DualCube) ↔ _
    rw [← hd p.1]
    simp only [Metric.mem_closure_iff, mem_iInter, mem_iUnion, mem_ofPred_eq]
    constructor
    · intro h n
      obtain ⟨_, ⟨i, rfl⟩, hi⟩ := h (1 / (n + 1)) (by positivity)
      exact ⟨i, hi⟩
    · intro h ε hε
      obtain ⟨n, hn⟩ := exists_nat_gt (ε⁻¹)
      have hr : (1 : ℝ) / (n + 1) < ε := by
        rw [one_div, inv_lt_comm₀ (by positivity) hε]
        linarith
      obtain ⟨i, hi⟩ := h n
      exact ⟨_, mem_range_self i, hi.trans hr⟩
  have hm : MeasurableSet {p : P | p.2.1 ∈ (codedDualBall p.1 : Set DualCube)} := by
    rw [he]
    exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun i =>
      measurableSet_lt (Measurable.dist (measurable_fst.comp measurable_snd)
        ((hs i).comp measurable_fst)) measurable_const
  exact hm.inter ((measurable_fst.prodMk (measurable_snd.comp measurable_snd))
    (ClosedSubspaces.measurableSet_mem (E := BanachAmbient)))

/-- Evaluate the functional represented by a point of the dual-pairing domain. -/
noncomputable def codedDualPairing (p : dualPairingSet) : ℝ :=
  ((codedDualBallHomeomorph p.val.1).symm ⟨p.val.2.1, p.property.1⟩).val
    ⟨p.val.2.2, p.property.2⟩

private theorem measurable_cubeEval : Measurable (fun p : DualCube × ℕ => (p.1 p.2).val) := by
  intro U hU
  have he : (fun p : DualCube × ℕ => (p.1 p.2).val) ⁻¹' U =
      ⋃ n : ℕ, (Prod.snd ⁻¹' {n}) ∩ {p : DualCube × ℕ | (p.1 n).val ∈ U} := by
    ext p
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_singleton_iff, mem_ofPred_eq]
    exact ⟨fun h => ⟨p.2, rfl, h⟩, fun ⟨n, hn, h⟩ => hn ▸ h⟩
  rw [he]
  exact MeasurableSet.iUnion fun n => (measurable_snd (measurableSet_singleton n)).inter
    ((measurable_subtype_coe.comp ((measurable_pi_apply n).comp measurable_fst)) hU)

/-- Parametrized evaluation is Borel in the subspace, the dual coordinates, and the vector. -/
theorem measurable_codedDualPairing : Measurable codedDualPairing := by
  classical
  let X (p : dualPairingSet) := p.val.1
  let x (p : dualPairingSet) := p.val.2.2
  let c (p : dualPairingSet) := p.val.2.1
  let scale (p : dualPairingSet) := max (1 : ℝ) ‖x p‖
  let y (p : dualPairingSet) := normalize (x p)
  have hX : Measurable X := measurable_fst.comp measurable_subtype_coe
  have hx : Measurable x := (measurable_snd.comp measurable_snd).comp measurable_subtype_coe
  have hc : Measurable c := (measurable_fst.comp measurable_snd).comp measurable_subtype_coe
  have hy : Measurable y := continuous_normalize.measurable.comp hx
  have hscale : Measurable scale := measurable_const.max hx.norm
  have hmem (p : dualPairingSet) :
      y p ∈ closure (range fun i => unitBallSelector i (X p)) := by
    rw [closure_range_unitBallSelector]
    exact ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using norm_normalize_le (x p),
      (X p).val.smul_mem _ p.property.2⟩
  let r (n : ℕ) : ℝ := 1 / (n + 1)
  have hex (n : ℕ) (p : dualPairingSet) :
      ∃ i, dist (unitBallSelector i (X p)) (y p) < r n := by
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := Metric.mem_closure_iff.mp (hmem p) (r n)
      (by dsimp [r]; positivity)
    exact ⟨i, by rwa [dist_comm]⟩
  let idx (n : ℕ) (p : dualPairingSet) := Nat.find (hex n p)
  have hidx (n : ℕ) : Measurable (idx n) := measurable_find (hex n) fun i =>
    measurableSet_lt (((measurable_unitBallSelector i).comp hX).dist hy) measurable_const
  let g (n : ℕ) (p : dualPairingSet) := scale p * ((c p) (idx n p)).val
  have hg (n : ℕ) : Measurable (g n) :=
    hscale.mul (measurable_cubeEval.comp (hc.prodMk (hidx n)))
  apply measurable_of_tendsto_metrizable hg
  rw [tendsto_pi_nhds]
  intro p
  let z : (X p).val := ⟨x p, p.property.2⟩
  let z' : (X p).val := (scale p)⁻¹ • z
  have hto : Tendsto (fun n => typedSelector (X p) (idx n p)) atTop (𝓝 z') := by
    apply IsEmbedding.subtypeVal.tendsto_nhds_iff.mpr
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg)
    · exact fun n => (Nat.find_spec (hex n p)).le
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
  let f := ((codedDualBallHomeomorph (X p)).symm ⟨c p, p.property.1⟩).val
  have hto' : Tendsto (fun n => f (typedSelector (X p) (idx n p))) atTop (𝓝 (f z')) :=
    f.toStrongDual.continuous.continuousAt.tendsto.comp hto
  have hto'' := (tendsto_const_nhds (x := scale p)).mul hto'
  have hval : scale p * f z' = f z := by
    change scale p * f.toStrongDual ((scale p)⁻¹ • z) = f.toStrongDual z
    have hpos : 0 < scale p := zero_lt_one.trans_le (le_max_left _ _)
    rw [map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
  have heval (n : ℕ) :
      f (typedSelector (X p) (idx n p)) = ((c p) (idx n p)).val :=
    codedDualBallHomeomorph_symm_eval (X p) ⟨c p, p.property.1⟩ (idx n p)
  change Tendsto (fun n => g n p) atTop (𝓝 (f z))
  simpa only [hval, heval, g] using hto''

/-- The pairing on a fixed space is jointly continuous for the two norm topologies. -/
theorem continuous_codedDualPairing_norm (X : BanachCode) :
    @Continuous (↥(codedDualBall X : Set DualCube) × X.val) ℝ
      (@instTopologicalSpaceProd _ _ (TopologicalSpace.induced
        (fun c : ↥(codedDualBall X : Set DualCube) => c.val.toLInfinity) inferInstance)
        inferInstance) inferInstance
      (fun p => ((codedDualBallHomeomorph X).symm p.1).val p.2) := by
  let e := codedDualBallHomeomorph X
  let c : ↥(codedDualBall X : Set DualCube) → lp (fun _ : ℕ => ℝ) ⊤ :=
    fun u => u.val.toLInfinity
  let f (u : (codedDualBall X : Set DualCube)) := (e.symm u).val.toStrongDual
  have he : codedDualEvaluation X ∘ f = c := by
    funext u
    have h := e.apply_symm_apply u
    change codedDualBallHomeomorph X (e.symm u) = u at h
    rw [codedDualBallHomeomorph_apply] at h
    exact (weakStarCode_toLInfinity X _).symm.trans (congrArg (DualCube.toLInfinity ∘ Subtype.val) h)
  let _ : TopologicalSpace ↥(codedDualBall X : Set DualCube) := TopologicalSpace.induced c inferInstance
  have hf : Continuous f := (codedDualEvaluation X).isometry.isEmbedding.isInducing.continuous_iff.mpr
    (he.symm ▸ continuous_induced_dom)
  change Continuous (fun p : ↥(codedDualBall X : Set DualCube) × X.val => f p.1 p.2)
  exact isBoundedBilinearMap_apply.continuous.comp₂ (hf.comp continuous_fst) continuous_snd

theorem image_unitBall_codedDualEvaluation (X : BanachCode) :
    codedDualEvaluation X '' Metric.closedBall (0 : StrongDual ℝ X.val) 1 =
      DualCube.toLInfinity '' (codedDualBall X : Set DualCube) := by
  ext a
  constructor
  · rintro ⟨f, hf, rfl⟩
    let u : WeakStarUnitBall X.val := ⟨f.toWeakDual, by simpa only [mem_preimage,
      StrongDual.toStrongDual_toWeakDual] using hf⟩
    exact ⟨weakStarCode X u, mem_range_self u, weakStarCode_toLInfinity X u⟩
  · rintro ⟨c, ⟨f, rfl⟩, rfl⟩
    exact ⟨f.val.toStrongDual, f.property, (weakStarCode_toLInfinity X f).symm⟩

/-- The compact-ball map is Borel into the Effros hyperspace, with compact image values. -/
theorem measurable_effros_codedDualBall :
    Measurable (NonemptyCompacts.toCloseds ∘ codedDualBall) :=
  measurable_nonemptyCompacts_toCloseds.comp measurable_codedDualBall

/-- The Borel coding and pairing, with the linear isometry and its unit-ball image. -/
theorem borel_parametrized_dualBall :
    Measurable (NonemptyCompacts.toCloseds ∘ codedDualBall) ∧
      MeasurableSet dualPairingSet ∧ Measurable codedDualPairing ∧
      ∀ X : BanachCode,
        (codedDualEvaluation X).toLinearMap.range =
          Submodule.span ℝ (DualCube.toLInfinity '' (codedDualBall X : Set DualCube)) ∧
        codedDualEvaluation X '' Metric.closedBall (0 : StrongDual ℝ X.val) 1 =
          DualCube.toLInfinity '' (codedDualBall X : Set DualCube) :=
  ⟨measurable_effros_codedDualBall, measurableSet_dualPairingSet, measurable_codedDualPairing,
    fun X => ⟨range_codedDualEvaluation X, image_unitBall_codedDualEvaluation X⟩⟩

end PaperFormalization
