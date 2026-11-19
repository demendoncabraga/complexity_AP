import PaperFormalization.ComplementedAnalytic
import PaperFormalization.DescriptiveClasses

namespace PaperFormalization

open Set Topology TopologicalSpace
open scoped BigOperators

/-- An isometric copy with a bounded linear left inverse. -/
def IsometricallyComplementablyEmbeds (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] : Prop :=
  ∃ i : E →ₗᵢ[ℝ] F, ∃ r : F →L[ℝ] E, Function.LeftInverse r i

theorem IsometricallyComplementablyEmbeds.complementablyEmbeds
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (h : IsometricallyComplementablyEmbeds E F) :
    ComplementablyEmbeds E F := by
  obtain ⟨i, r, hri⟩ := h
  exact ⟨i.toContinuousLinearMap, r, hri⟩

private theorem comp_interleave {U V : Type*} (f : U → V) (a b : ℕ → U) :
    f ∘ interleaveSequences a b = interleaveSequences (f ∘ a) (f ∘ b) := by
  funext n
  cases h : Equiv.natSumNatEquivNat.symm n <;> simp [interleaveSequences, h]

private theorem sum_single_coefficient {G : Type*} [AddCommMonoid G] [Module ℝ G]
    {n : ℕ} (v : Fin n → G) (i : Fin n) :
    (∑ j : Fin n, (((Pi.single i (1 : ℚ) : Fin n → ℚ) j : ℚ) : ℝ) • v j) = v i := by
  classical
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

private theorem SequenceLinearBound.value_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {d : ℕ → E} {a : ℕ → F} {c : ℝ}
    (h : SequenceLinearBound d a c) (n : ℕ) : ‖a n‖ ≤ c * ‖d n‖ := by
  let i : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
  have hb := h (n + 1) (Pi.single i 1)
  rw [sum_single_coefficient, sum_single_coefficient] at hb
  exact hb

private def coversSequence (a e : ℕ → BanachAmbient) : Prop :=
  ∀ n k : ℕ, ∃ j : ℕ, dist (e n) (a j) < (1 : ℝ) / (k + 1)

private def operatorBounds (isometric onto : Bool)
    (d e a b : ℕ → BanachAmbient) (c k : ℕ) : Prop :=
  SequenceLinearBound d a c ∧
    SequenceLinearBound (interleaveSequences e a) (interleaveSequences b d) k ∧
      (isometric = true → c = 1 ∧ SequenceLinearBound a d 1) ∧
      (onto = true → coversSequence a e)

private def asTyped (X : BanachCode) (d : ℕ → BanachAmbient) (h : ∀ n, d n ∈ X.val) :
    ℕ → X.val := fun n => ⟨d n, h n⟩

private theorem selectors_mem {X : BanachCode} {d : ℕ → BanachAmbient}
    (h : closure (range d) = (X.val : Set BanachAmbient)) (n : ℕ) : d n ∈ X.val := by
  change d n ∈ (X.val : Set BanachAmbient)
  exact h ▸ subset_closure (mem_range_self n)

private theorem denseRange_asTyped {X : BanachCode} {d : ℕ → BanachAmbient}
    (h : closure (range d) = (X.val : Set BanachAmbient)) :
    DenseRange (asTyped X d (selectors_mem h)) := by
  intro x
  rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, mem_preimage,
    ← range_comp, show Subtype.val ∘ asTyped X d (selectors_mem h) = d from rfl, h]
  exact x.property

private theorem denseRange_of_coversSequence (Y : BanachCode) (a e : ℕ → BanachAmbient)
    (ha : ∀ n, a n ∈ Y.val) (he : closure (range e) = (Y.val : Set BanachAmbient))
    (h : coversSequence a e) : DenseRange (asTyped Y a ha) := by
  let A := asTyped Y a ha
  let E := asTyped Y e (selectors_mem he)
  intro y
  apply closure_minimal (range_subset_iff.mpr ?_) isClosed_closure (denseRange_asTyped he y)
  intro n
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (ε⁻¹)
  have hrad : (1 : ℝ) / (k + 1) < ε := by
    rw [one_div, inv_lt_comm₀ (by positivity) hε]
    linarith
  obtain ⟨j, hj⟩ := h n k
  exact ⟨A j, mem_range_self j, hj.trans hrad⟩

set_option maxHeartbeats 700000 in
private theorem operatorBounds_iff (isometric onto : Bool)
    (X Y : BanachCode) (d e : ℕ → BanachAmbient)
    (hd : closure (range d) = (X.val : Set BanachAmbient))
    (he : closure (range e) = (Y.val : Set BanachAmbient)) :
    (∃ a b : ℕ → BanachAmbient, ∃ c k : ℕ,
      (∀ n, a n ∈ Y.val) ∧ (∀ n, b n ∈ X.val) ∧ operatorBounds isometric onto d e a b c k) ↔
    ∃ (I : X.val →L[ℝ] Y.val) (R : Y.val →L[ℝ] X.val), Function.LeftInverse R I ∧
      (isometric = true → ∀ x, ‖I x‖ = ‖x‖) ∧ (onto = true → Function.Surjective I) := by
  let D := asTyped X d (selectors_mem hd)
  let E := asTyped Y e (selectors_mem he)
  have hD : DenseRange D := denseRange_asTyped hd
  have hE : DenseRange E := denseRange_asTyped he
  let j := X.val.subtypeₗᵢ
  let l := Y.val.subtypeₗᵢ
  constructor
  · rintro ⟨a, b, c, k, ha, hb, h₁, h₂, hi, ho⟩
    let A := asTyped Y a ha
    let B := asTyped X b hb
    have h₁' := (SequenceLinearBound.comp_isometries_iff j l D A c).mp h₁
    obtain ⟨I, hI, _⟩ := h₁'.exists_operator hD
    have hmerge : DenseRange (interleaveSequences E A) := by
      apply hE.mono
      rintro _ ⟨n, rfl⟩
      exact ⟨Equiv.natSumNatEquivNat (.inl n), interleaveSequences_left E A n⟩
    have h₂' := (SequenceLinearBound.comp_isometries_iff l j (interleaveSequences E A)
      (interleaveSequences B D) k).mp (by
        rw [comp_interleave, comp_interleave]
        change SequenceLinearBound (interleaveSequences e a) (interleaveSequences b d) k
        exact h₂)
    obtain ⟨R, hR, _⟩ := h₂'.exists_operator hmerge
    have hRI : Function.LeftInverse R I := by
      have eq : R ∘ I = id := hD.equalizer (R.continuous.comp I.continuous) continuous_id (by
        funext n
        change R (I (D n)) = D n
        rw [hI]
        simpa only [interleaveSequences_right] using hR (Equiv.natSumNatEquivNat (.inr n)))
      exact fun z => congrFun eq z
    refine ⟨I, R, hRI, ?_, ?_⟩
    · intro hiso x
      obtain ⟨hc, hrev⟩ := hi hiso
      have hh := (SequenceLinearBound.comp_isometries_iff l j A D (1 : ℝ)).mp hrev
      refine hD.induction_on x (isClosed_eq I.continuous.norm continuous_norm) fun n => ?_
      rw [hI]
      exact le_antisymm (by simpa only [hc, Nat.cast_one, one_mul] using h₁'.value_le n)
        (by simpa only [one_mul] using hh.value_le n)
    · intro honto
      have hA : DenseRange A := denseRange_of_coversSequence Y a e ha he (ho honto)
      have hfixed : I ∘ R = id := hA.equalizer (I.continuous.comp R.continuous) continuous_id (by
        funext n
        change I (R (A n)) = A n
        rw [← hI, hRI _])
      exact fun y => ⟨R y, congrFun hfixed y⟩
  · rintro ⟨I, R, hRI, hIso, hOnto⟩
    let A := I ∘ D
    let B := R ∘ E
    obtain ⟨c₀, hc₀⟩ := exists_nat_gt ‖I‖
    obtain ⟨k, hk⟩ := exists_nat_gt ‖R‖
    let c := if isometric = true then 1 else c₀
    have hc : ‖I‖ ≤ c := by
      by_cases hi : isometric = true
      · simpa only [c, if_pos hi, Nat.cast_one] using
          I.opNorm_le_bound zero_le_one (fun x => by simp [hIso hi x])
      · simpa only [c, if_neg hi] using hc₀.le
    refine ⟨l ∘ A, j ∘ B, c, k, ?_, ?_, ?_⟩
    · exact fun n => (A n).property
    · exact fun n => (B n).property
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (SequenceLinearBound.comp_isometries_iff j l D A c).mpr
        ((SequenceLinearBound.of_operator I D).mono hc)
    · have hcomp : R ∘ interleaveSequences E A = interleaveSequences B D := by
        rw [comp_interleave]
        congr 1
        funext n
        exact hRI (D n)
      have h := (SequenceLinearBound.of_operator R (interleaveSequences E A)).mono hk.le
      have h' : SequenceLinearBound (interleaveSequences E A) (R ∘ interleaveSequences E A) k := h
      rw [hcomp] at h'
      have h'' := (SequenceLinearBound.comp_isometries_iff l j (interleaveSequences E A)
        (interleaveSequences B D) k).mpr h'
      rw [comp_interleave, comp_interleave] at h''
      exact h''
    · intro hiso
      refine ⟨if_pos hiso, (SequenceLinearBound.comp_isometries_iff l j A D 1).mpr ?_⟩
      intro n q
      have h := hIso hiso (∑ i : Fin n, (q i : ℝ) • D i)
      have hv : I (∑ i : Fin n, (q i : ℝ) • D i) = ∑ i : Fin n, (q i : ℝ) • A i := by
        simp only [map_sum, map_smul, A, Function.comp_apply]
      rw [hv] at h
      rw [one_mul]
      exact h.symm.le
    · intro honto n k'
      obtain ⟨z, hz⟩ := hOnto honto (E n)
      have hz' : z ∈ closure (range D) := hD z
      have hm := image_closure_subset_closure_image I.continuous
        (mem_image_of_mem I hz')
      rw [← range_comp, hz] at hm
      obtain ⟨_, ⟨i, rfl⟩, hi⟩ := Metric.mem_closure_iff.mp hm
        ((1 : ℝ) / (k' + 1)) (by positivity)
      exact ⟨i, hi⟩

private theorem measurable_interleave {A : Type*} [MeasurableSpace A]
    {a b : ℕ → A → BanachAmbient} (ha : ∀ i, Measurable (a i)) (hb : ∀ i, Measurable (b i))
    (n : ℕ) : Measurable (fun p => interleaveSequences (fun i => a i p) (fun i => b i p) n) := by
  cases h : Equiv.natSumNatEquivNat.symm n with
  | inl i =>
    simpa only [interleaveSequences, Function.comp_apply, h, Sum.elim_inl] using ha i
  | inr i =>
    simpa only [interleaveSequences, Function.comp_apply, h, Sum.elim_inr] using hb i

private theorem measurableSet_retractionBounds {A : Type*} [MeasurableSpace A]
    (d e a b : ℕ → A → BanachAmbient)
    (hd : ∀ i, Measurable (d i)) (he : ∀ i, Measurable (e i))
    (ha : ∀ i, Measurable (a i)) (hb : ∀ i, Measurable (b i)) (k : ℕ) :
    MeasurableSet {p | SequenceLinearBound (interleaveSequences (fun i => e i p) (fun i => a i p))
      (interleaveSequences (fun i => b i p) (fun i => d i p)) k} :=
  measurableSet_sequenceLinearBound _ _ (measurable_interleave he ha)
    (measurable_interleave hb hd) k

private theorem measurableSet_operatorBounds {A : Type*} [MeasurableSpace A]
    (isometric onto : Bool) (d e a b : ℕ → A → BanachAmbient)
    (hd : ∀ i, Measurable (d i)) (he : ∀ i, Measurable (e i))
    (ha : ∀ i, Measurable (a i)) (hb : ∀ i, Measurable (b i)) (c k : ℕ) :
    MeasurableSet {p | operatorBounds isometric onto (fun i => d i p) (fun i => e i p)
      (fun i => a i p) (fun i => b i p) c k} := by
  have hi : MeasurableSet {p | isometric = true → c = 1 ∧
      SequenceLinearBound (fun i => a i p) (fun i => d i p) 1} := by
    by_cases h : isometric = true
    · simp only [h, true_implies]
      exact (MeasurableSet.const _).inter (measurableSet_sequenceLinearBound a d ha hd 1)
    · simp [h]
  have ho : MeasurableSet {p | onto = true → coversSequence (fun i => a i p) (fun i => e i p)} := by
    by_cases h : onto = true
    · have heq : {p | onto = true → coversSequence (fun i => a i p) (fun i => e i p)} =
          ⋂ n : ℕ, ⋂ k' : ℕ, ⋃ j : ℕ,
            {p | dist (e n p) (a j p) < (1 : ℝ) / (k' + 1)} := by
        ext p
        simp [h, coversSequence]
      rw [heq]
      exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun k' => MeasurableSet.iUnion fun j =>
        measurableSet_lt ((he n).dist (ha j)) measurable_const
    · simp [h]
  exact (measurableSet_sequenceLinearBound d a hd ha c).inter
    ((measurableSet_retractionBounds d e a b hd he ha hb k).inter (hi.inter ho))

private abbrev CodedPair := BanachCode × BanachCode
private abbrev Witness := CodedPair × (ℕ → BanachAmbient) × (ℕ → BanachAmbient)

private theorem measurableSet_sequence_mem {A : Type*} [MeasurableSpace A]
    {W : A → BanachCode} (hW : Measurable W)
    {a : ℕ → A → BanachAmbient} (ha : ∀ n, Measurable (a n)) :
    MeasurableSet {p | ∀ n, a n p ∈ (W p).val} := by
  have he : {p | ∀ n, a n p ∈ (W p).val} = ⋂ n, {p | a n p ∈ (W p).val} := by
    ext p
    simp
  rw [he]
  exact MeasurableSet.iInter fun n => (hW.prodMk (ha n)) ClosedSubspaces.measurableSet_mem

private theorem borelAnalytic_operatorRelation (isometric onto : Bool) :
    BorelAnalytic {p : CodedPair |
      ∃ (I : p.1.val →L[ℝ] p.2.val) (R : p.2.val →L[ℝ] p.1.val), Function.LeftInverse R I ∧
        (isometric = true → ∀ x, ‖I x‖ = ‖x‖) ∧ (onto = true → Function.Surjective I)} := by
  obtain ⟨s, hs, hdense⟩ := ClosedSubspaces.exists_borel_dense_selectors (E := BanachAmbient)
  let d (n : ℕ) (p : Witness) := s n p.1.1
  let e (n : ℕ) (p : Witness) := s n p.1.2
  let a (n : ℕ) (p : Witness) := p.2.1 n
  let b (n : ℕ) (p : Witness) := p.2.2 n
  have hd (i : ℕ) : Measurable (d i) := (hs i).comp (measurable_fst.comp measurable_fst)
  have he (i : ℕ) : Measurable (e i) := (hs i).comp (measurable_snd.comp measurable_fst)
  have ha (i : ℕ) : Measurable (a i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  have hb (i : ℕ) : Measurable (b i) :=
    (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)
  let S (c k : ℕ) : Set Witness := {p | (∀ n, p.2.1 n ∈ p.1.2.val) ∧
    (∀ n, p.2.2 n ∈ p.1.1.val) ∧ operatorBounds isometric onto (fun n => s n p.1.1)
      (fun n => s n p.1.2) p.2.1 p.2.2 c k}
  have hS (c k : ℕ) : MeasurableSet (S c k) :=
    (measurableSet_sequence_mem (measurable_snd.comp measurable_fst) ha).inter
      ((measurableSet_sequence_mem (measurable_fst.comp measurable_fst) hb).inter
        (measurableSet_operatorBounds isometric onto d e a b hd he ha hb c k))
  have hEq : Prod.fst '' (⋃ c : ℕ, ⋃ k : ℕ, S c k) =
      {p : CodedPair |
        ∃ (I : p.1.val →L[ℝ] p.2.val) (R : p.2.val →L[ℝ] p.1.val), Function.LeftInverse R I ∧
          (isometric = true → ∀ x, ‖I x‖ = ‖x‖) ∧ (onto = true → Function.Surjective I)} := by
    ext p
    rw [mem_ofPred_eq, ← operatorBounds_iff isometric onto p.1 p.2 (fun n => s n p.1)
      (fun n => s n p.2) (hdense p.1) (hdense p.2)]
    constructor
    · rintro ⟨⟨p', u, v⟩, hp, rfl⟩
      obtain ⟨c, hp⟩ := mem_iUnion.mp hp
      obtain ⟨k, hp⟩ := mem_iUnion.mp hp
      exact ⟨u, v, c, k, hp⟩
    · rintro ⟨u, v, c, k, hp⟩
      exact ⟨(p, u, v), mem_iUnion.mpr ⟨c, mem_iUnion.mpr ⟨k, hp⟩⟩, rfl⟩
  rw [← hEq]
  have : StandardBorelSpace BanachCode := banachCode_standardBorel
  have : StandardBorelSpace (ℕ → BanachAmbient) := inferInstance
  have : StandardBorelSpace CodedPair := inferInstance
  have : StandardBorelSpace ((ℕ → BanachAmbient) × (ℕ → BanachAmbient)) := inferInstance
  have : StandardBorelSpace Witness := inferInstance
  exact BorelAnalytic.of_measurable_image
    (MeasurableSet.iUnion fun c => MeasurableSet.iUnion (hS c)) measurable_fst

/-- Complemented containment of two varying coded spaces is analytic. -/
theorem borelAnalytic_complementablyEmbeds_relation :
    BorelAnalytic {p : BanachCode × BanachCode | ComplementablyEmbeds p.1.val p.2.val} := by
  simpa [ComplementablyEmbeds] using borelAnalytic_operatorRelation false false

/-- Isometric complemented containment of two varying coded spaces is analytic. -/
theorem borelAnalytic_isometricallyComplementablyEmbeds_relation :
    BorelAnalytic {p : BanachCode × BanachCode | IsometricallyComplementablyEmbeds p.1.val p.2.val} := by
  convert borelAnalytic_operatorRelation true false using 1
  ext p
  simp only [mem_ofPred_eq, true_implies, Bool.false_eq_true, IsEmpty.forall_iff, and_true]
  constructor
  · rintro ⟨i, r, hri⟩
    exact ⟨i.toContinuousLinearMap, r, hri, i.norm_map⟩
  · rintro ⟨i, r, hri, hi⟩
    exact ⟨⟨i.toLinearMap, hi⟩, r, hri⟩

/-- Isomorphism of coded real Banach spaces is analytic. -/
theorem borelAnalytic_isomorphism :
    BorelAnalytic {p : BanachCode × BanachCode | Nonempty (p.1.val ≃L[ℝ] p.2.val)} := by
  convert borelAnalytic_operatorRelation false true using 1
  ext p
  simp only [mem_ofPred_eq, true_implies, Bool.false_eq_true, IsEmpty.forall_iff, true_and]
  constructor
  · rintro ⟨e⟩
    exact ⟨e.toContinuousLinearMap, e.symm.toContinuousLinearMap, e.left_inv, e.surjective⟩
  · rintro ⟨i, r, hri, hsurj⟩
    exact ⟨ContinuousLinearEquiv.ofBijective i (LinearMap.ker_eq_bot.mpr hri.injective)
      (LinearMap.range_eq_top.mpr hsurj)⟩

/-- Linear isometry of coded real Banach spaces is analytic. -/
theorem borelAnalytic_isometry :
    BorelAnalytic {p : BanachCode × BanachCode | Nonempty (p.1.val ≃ₗᵢ[ℝ] p.2.val)} := by
  convert borelAnalytic_operatorRelation true true using 1
  ext p
  simp only [mem_ofPred_eq, true_implies]
  constructor
  · rintro ⟨e⟩
    exact ⟨e.toLinearIsometry.toContinuousLinearMap, e.symm.toLinearIsometry.toContinuousLinearMap,
      e.left_inv, e.norm_map, e.surjective⟩
  · rintro ⟨i, _, _, hi, hsurj⟩
    exact ⟨LinearIsometryEquiv.ofSurjective ⟨i.toLinearMap, hi⟩ hsurj⟩

/-- The isometric complemented-copy class for a fixed coded space. -/
def isometricComplementedClass (E : BanachCode) : Set BanachCode :=
  {X | IsometricallyComplementablyEmbeds E.val X.val}

/-- The complemented-copy class for a fixed coded space. -/
def complementedClass (E : BanachCode) : Set BanachCode :=
  {X | ComplementablyEmbeds E.val X.val}

theorem borelAnalytic_isometricComplementedClass (E : BanachCode) :
    BorelAnalytic (isometricComplementedClass E) := by
  have : StandardBorelSpace BanachCode := banachCode_standardBorel
  exact borelAnalytic_isometricallyComplementablyEmbeds_relation.preimage
    (measurable_const.prodMk measurable_id)

theorem completeAnalytic_isometricComplementedClass (E : BanachCode)
    (p : RealBanachSpace → Prop) (hp : IsL1StableComplementedProperty p)
    (hE : ¬ p (RealBanachSpace.of E.val)) : CompleteAnalytic (isometricComplementedClass E) := by
  rw [completeAnalytic_iff_illFounded_reduces]
  have : SeparableSpace E.val := inferInstance
  obtain ⟨Φ, hΦ, hW, hI⟩ := exists_borelReduction E.val
  refine ⟨borelAnalytic_isometricComplementedClass E, Φ, hΦ, Set.ext fun T => ?_⟩
  change IsometricallyComplementablyEmbeds E.val (Φ T).val ↔ T.IsIllFounded
  constructor
  · intro h
    by_contra hn
    have hw : T.IsWellFounded := not_nonempty_iff_eq_empty.mp hn
    exact hE (hp.2 (X := RealBanachSpace.of E.val) (Y := RealBanachSpace.of (Φ T).val)
      h.complementablyEmbeds (hW T hw p hp.1))
  · intro h
    obtain ⟨i, r, _, hri⟩ := hI T h
    exact ⟨i, r, hri⟩

/-- The inclusion of one coded subspace into another admits a bounded retraction. -/
def IsComplementedSubspace (W V : BanachCode) : Prop :=
  ∃ h : W.val ≤ V.val, ∃ R : V.val →L[ℝ] W.val, Function.LeftInverse R (Submodule.inclusion h)

private theorem complementedSubspace_iff_retractionBounds
    (W V : BanachCode) (d e : ℕ → BanachAmbient)
    (hd : closure (range d) = (W.val : Set BanachAmbient))
    (he : closure (range e) = (V.val : Set BanachAmbient)) :
    IsComplementedSubspace W V ↔ ∃ b : ℕ → BanachAmbient, ∃ k : ℕ,
      W.val ≤ V.val ∧ (∀ n, b n ∈ W.val) ∧
      SequenceLinearBound (interleaveSequences e d) (interleaveSequences b d) k := by
  let D := asTyped W d (selectors_mem hd)
  let E := asTyped V e (selectors_mem he)
  let iW := W.val.subtypeₗᵢ
  let iV := V.val.subtypeₗᵢ
  constructor
  · rintro ⟨h, R, hR⟩
    obtain ⟨k, hk⟩ := exists_nat_gt ‖R‖
    let A := Submodule.inclusion h ∘ D
    let B := R ∘ E
    refine ⟨iW ∘ B, k, h, fun n => (B n).property, ?_⟩
    have hcomp : R ∘ interleaveSequences E A = interleaveSequences B D := by
      rw [comp_interleave]
      congr 1
      funext n
      exact hR (D n)
    have hB : SequenceLinearBound (interleaveSequences E A) (R ∘ interleaveSequences E A) k :=
      (SequenceLinearBound.of_operator R _).mono hk.le
    rw [hcomp] at hB
    have hAmbient := (SequenceLinearBound.comp_isometries_iff iV iW (interleaveSequences E A)
      (interleaveSequences B D) k).mpr hB
    rw [comp_interleave, comp_interleave] at hAmbient
    exact hAmbient
  · rintro ⟨b, k, h, hb, hB⟩
    let A := Submodule.inclusion h ∘ D
    let B := asTyped W b hb
    have hBound := (SequenceLinearBound.comp_isometries_iff iV iW (interleaveSequences E A)
      (interleaveSequences B D) k).mp (by
        rw [comp_interleave, comp_interleave]
        exact hB)
    have hDense : DenseRange (interleaveSequences E A) := by
      apply (denseRange_asTyped he).mono
      rintro _ ⟨n, rfl⟩
      exact ⟨Equiv.natSumNatEquivNat (.inl n), interleaveSequences_left E A n⟩
    obtain ⟨R, hR, _⟩ := hBound.exists_operator hDense
    let j : W.val →L[ℝ] V.val :=
      ⟨Submodule.inclusion h, continuous_subtype_val.subtype_mk _⟩
    have heq : R ∘ j = id := (denseRange_asTyped hd).equalizer
      (R.continuous.comp j.continuous) continuous_id (by
        funext n
        change R (A n) = D n
        simpa only [interleaveSequences_right] using hR (Equiv.natSumNatEquivNat (.inr n)))
    exact ⟨h, R, fun x => congrFun heq x⟩

/-- Being a complemented subspace, with the inclusion fixed, is an analytic relation. -/
theorem borelAnalytic_isComplementedSubspace :
    BorelAnalytic {p : BanachCode × BanachCode | IsComplementedSubspace p.1 p.2} := by
  obtain ⟨s, hs, hdense⟩ := ClosedSubspaces.exists_borel_dense_selectors (E := BanachAmbient)
  let P := CodedPair × (ℕ → BanachAmbient)
  let d (n : ℕ) (p : P) := s n p.1.1
  let e (n : ℕ) (p : P) := s n p.1.2
  let b (n : ℕ) (p : P) := p.2 n
  have hd (n : ℕ) : Measurable (d n) := (hs n).comp (measurable_fst.comp measurable_fst)
  have he (n : ℕ) : Measurable (e n) := (hs n).comp (measurable_snd.comp measurable_fst)
  have hb (n : ℕ) : Measurable (b n) := (measurable_pi_apply n).comp measurable_snd
  let S (k : ℕ) : Set P := {p | p.1.1.val ≤ p.1.2.val ∧ (∀ n, p.2 n ∈ p.1.1.val) ∧
    SequenceLinearBound (interleaveSequences (fun n => e n p) (fun n => d n p))
      (interleaveSequences (fun n => b n p) (fun n => d n p)) k}
  have hS (k : ℕ) : MeasurableSet (S k) :=
    (measurable_fst (ClosedSubspaces.measurableSet_le (E := BanachAmbient))).inter
      ((measurableSet_sequence_mem (measurable_fst.comp measurable_fst) hb).inter
        (measurableSet_retractionBounds d e d b hd he hd hb k))
  have heq : Prod.fst '' (⋃ k : ℕ, S k) =
      {p : BanachCode × BanachCode | IsComplementedSubspace p.1 p.2} := by
    ext p
    rw [mem_ofPred_eq, complementedSubspace_iff_retractionBounds p.1 p.2 (fun n => s n p.1)
      (fun n => s n p.2) (hdense p.1) (hdense p.2)]
    constructor
    · rintro ⟨⟨q, b'⟩, hq, rfl⟩
      obtain ⟨k, hk⟩ := mem_iUnion.mp hq
      exact ⟨b', k, hk⟩
    · rintro ⟨b', k, hk⟩
      exact ⟨(p, b'), mem_iUnion.mpr ⟨k, hk⟩, rfl⟩
  rw [← heq]
  have : StandardBorelSpace BanachCode := banachCode_standardBorel
  have : StandardBorelSpace CodedPair := inferInstance
  have : StandardBorelSpace (ℕ → BanachAmbient) := inferInstance
  have : StandardBorelSpace P := inferInstance
  exact BorelAnalytic.of_measurable_image (MeasurableSet.iUnion hS) measurable_fst

end PaperFormalization
