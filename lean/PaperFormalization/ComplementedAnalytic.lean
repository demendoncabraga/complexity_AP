import PaperFormalization.OperatorCode
import PaperFormalization.EffrosStandard
import PaperFormalization.MainReduction
import PaperFormalization.TreeCompleteness

namespace PaperFormalization

open Set Topology TopologicalSpace MeasureTheory
open scoped BigOperators

@[instance_reducible] noncomputable def banachCodePolishTopology : TopologicalSpace BanachCode :=
  (upgradeStandardBorel BanachCode).toTopologicalSpace

def interleaveSequences {V : Type*} (a b : ℕ → V) : ℕ → V :=
  Sum.elim a b ∘ Equiv.natSumNatEquivNat.symm

theorem interleaveSequences_left {V : Type*} (a b : ℕ → V) (i : ℕ) :
    interleaveSequences a b (Equiv.natSumNatEquivNat (.inl i)) = a i := by simp [interleaveSequences]

theorem interleaveSequences_right {V : Type*} (a b : ℕ → V) (i : ℕ) :
    interleaveSequences a b (Equiv.natSumNatEquivNat (.inr i)) = b i := by simp [interleaveSequences]

theorem SequenceLinearBound.comp_isometries_iff
    {E F E' F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (i : E →ₗᵢ[ℝ] E') (j : F →ₗᵢ[ℝ] F') (x : ℕ → E) (y : ℕ → F) (C : ℝ) :
    SequenceLinearBound (i ∘ x) (j ∘ y) C ↔ SequenceLinearBound x y C := by
  simp only [SequenceLinearBound, Function.comp_apply, ← LinearIsometry.map_smul,
    ← map_sum, LinearIsometry.norm_map]

theorem SequenceLinearBound.mono
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {x : ℕ → E} {y : ℕ → F} {C D : ℝ}
    (h : SequenceLinearBound x y C) (hle : C ≤ D) : SequenceLinearBound x y D :=
  fun n a => (h n a).trans (mul_le_mul_of_nonneg_right hle (norm_nonneg _))

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

private theorem complemented_iff_sequenceBound
    (e : ℕ → E) (he : DenseRange e)
    (X : BanachCode) (d : ℕ → BanachAmbient)
    (hd : closure (range d) = (X.val : Set BanachAmbient)) :
    ComplementablyEmbeds E X.val ↔
      ∃ a : ℕ → BanachAmbient, ∃ b : ℕ → E, ∃ c k : ℕ,
        (∀ i, a i ∈ X.val) ∧ SequenceLinearBound e a c ∧
        SequenceLinearBound (interleaveSequences d a) (interleaveSequences b e) k := by
  classical
  let D (n : ℕ) : X.val := ⟨d n, show d n ∈ (X.val : Set _) from hd ▸ subset_closure (mem_range_self n)⟩
  have hD : DenseRange D := by
    intro x
    rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, mem_preimage,
      ← range_comp, show Subtype.val ∘ D = d from rfl, hd]
    exact x.property
  let f := X.val.subtypeₗᵢ
  constructor
  · rintro ⟨I, R, hRI⟩
    obtain ⟨c, hc⟩ := exists_nat_gt ‖I‖
    obtain ⟨k, hk⟩ := exists_nat_gt ‖R‖
    let a := I ∘ e
    let b := R ∘ D
    refine ⟨f ∘ a, b, c, k, fun i => (a i).property, ?_, ?_⟩
    · exact (SequenceLinearBound.comp_isometries_iff (LinearIsometry.id) f e a c).mpr
        ((SequenceLinearBound.of_operator I e).mono hc.le)
    · have h₁ : f ∘ interleaveSequences D a = interleaveSequences d (f ∘ a) := by
        funext n
        cases h : Equiv.natSumNatEquivNat.symm n <;> simp [interleaveSequences, h, D, f]
      have h₂ : R ∘ interleaveSequences D a = interleaveSequences b e := by
        funext n
        cases h : Equiv.natSumNatEquivNat.symm n with
        | inl i => simp [interleaveSequences, h, b]
        | inr i => simpa [interleaveSequences, h, a] using hRI (e i)
      rw [← h₁, ← h₂]
      exact (SequenceLinearBound.comp_isometries_iff f LinearIsometry.id (interleaveSequences D a)
        (R ∘ interleaveSequences D a) k).mpr ((SequenceLinearBound.of_operator R _).mono hk.le)
  · rintro ⟨a, b, c, k, ha, h₁, h₂⟩
    let A (i : ℕ) : X.val := ⟨a i, ha i⟩
    obtain ⟨I, hI, _⟩ := SequenceLinearBound.exists_operator
      ((SequenceLinearBound.comp_isometries_iff LinearIsometry.id f e A c).mp h₁) he
    have hmerge : DenseRange (interleaveSequences D A) := by
      apply hD.mono
      rintro _ ⟨n, rfl⟩
      exact ⟨Equiv.natSumNatEquivNat (.inl n), interleaveSequences_left D A n⟩
    have hm : f ∘ interleaveSequences D A = interleaveSequences d a := by
      funext n
      cases h : Equiv.natSumNatEquivNat.symm n <;> simp [interleaveSequences, h, D, A, f]
    rw [← hm] at h₂
    obtain ⟨R, hR, _⟩ := ((SequenceLinearBound.comp_isometries_iff f LinearIsometry.id
      (interleaveSequences D A) (interleaveSequences b e) k).mp h₂).exists_operator hmerge
    have hcomp : R ∘ I = id := he.equalizer (R.continuous.comp I.continuous) continuous_id (by
      funext n
      change R (I (e n)) = e n
      rw [hI]
      simpa only [interleaveSequences_right] using hR (Equiv.natSumNatEquivNat (.inr n)))
    exact ⟨I, R, fun z => congrFun hcomp z⟩

end

/-- Proposition 2.1 for every separable real Banach space, in the Effros coding. -/
theorem analyticSet_complementablyEmbeds
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [SeparableSpace E] :
    @AnalyticSet BanachCode banachCodePolishTopology {X | ComplementablyEmbeds E X.val} := by
  let t := upgradeStandardBorel BanachCode
  let : TopologicalSpace BanachCode := banachCodePolishTopology
  have : PolishSpace BanachCode := t.toPolishSpace
  have : BorelSpace BanachCode := t.toBorelSpace
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  obtain ⟨d, hd, hdense⟩ := ClosedSubspaces.exists_borel_dense_selectors (E := BanachAmbient)
  let e := denseSeq E
  let P := BanachCode × (ℕ → BanachAmbient) × (ℕ → E)
  let B (c k : ℕ) : Set P := {p |
    (∀ i, p.2.1 i ∈ p.1.val) ∧ SequenceLinearBound e p.2.1 c ∧
    SequenceLinearBound (interleaveSequences (fun i => d i p.1) p.2.1) (interleaveSequences p.2.2 e) k}
  have ha (i : ℕ) : Measurable (fun p : P => p.2.1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  have hb (i : ℕ) : Measurable (fun p : P => p.2.2 i) :=
    (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)
  have hB (c k : ℕ) : MeasurableSet (B c k) := by
    have hB_eq : B c k = (⋂ i : ℕ, {p : P | p.2.1 i ∈ p.1.val}) ∩
        ({p : P | SequenceLinearBound e p.2.1 c} ∩ {p : P |
          SequenceLinearBound (interleaveSequences (fun i => d i p.1) p.2.1) (interleaveSequences p.2.2 e) k}) := by
      ext p
      simp [B]
    rw [hB_eq]
    refine (MeasurableSet.iInter fun i =>
      (measurable_fst.prodMk (ha i)) ClosedSubspaces.measurableSet_mem).inter ?_
    refine (measurableSet_sequenceLinearBound (fun i _ => e i) (fun i (p : P) => p.2.1 i)
      (fun _ => measurable_const) ha c).inter ?_
    apply measurableSet_sequenceLinearBound
    · intro n
      cases h : Equiv.natSumNatEquivNat.symm n <;>
        simp only [interleaveSequences, Function.comp_apply, h, Sum.elim_inl, Sum.elim_inr]
      · exact (hd _).comp measurable_fst
      · exact ha _
    · intro n
      cases h : Equiv.natSumNatEquivNat.symm n <;>
        simp only [interleaveSequences, Function.comp_apply, h, Sum.elim_inl, Sum.elim_inr]
      · exact hb _
      · exact measurable_const
  have heq : Prod.fst '' (⋃ c : ℕ, ⋃ k : ℕ, B c k) =
      {X | ComplementablyEmbeds E X.val} := by
    ext X
    rw [mem_ofPred_eq, complemented_iff_sequenceBound e (denseRange_denseSeq E)
      X (fun i => d i X) (hdense X)]
    constructor
    · rintro ⟨⟨Y, a, b⟩, hp, rfl⟩
      obtain ⟨c, hp⟩ := mem_iUnion.mp hp
      obtain ⟨k, hp⟩ := mem_iUnion.mp hp
      exact ⟨a, b, c, k, hp⟩
    · rintro ⟨a, b, c, k, hp⟩
      exact ⟨(X, a, b), mem_iUnion.mpr ⟨c, mem_iUnion.mpr ⟨k, hp⟩⟩, rfl⟩
  rw [← heq]
  have : StandardBorelSpace P := by
    change StandardBorelSpace (BanachCode × (ℕ → BanachAmbient) × (ℕ → E))
    have : StandardBorelSpace BanachCode := banachCode_standardBorel
    have : StandardBorelSpace (ℕ → BanachAmbient) := inferInstance
    have : StandardBorelSpace (ℕ → E) := inferInstance
    have : StandardBorelSpace ((ℕ → BanachAmbient) × (ℕ → E)) := inferInstance
    infer_instance
  exact (MeasurableSet.iUnion fun c => MeasurableSet.iUnion (hB c)).analyticSet_image measurable_fst

/-- Ill-foundedness reduces to complemented containment when the given space
fails a property inherited by complemented subspaces and stable under ℓ₁ sums. -/
theorem exists_reduction_complementablyEmbeds
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [SeparableSpace E]
    (p : RealBanachSpace → Prop) (hp : IsL1StableComplementedProperty p)
    (hE : ¬ p (RealBanachSpace.of E)) :
    ∃ Φ : NatTree → BanachCode, Measurable Φ ∧
      Φ ⁻¹' {X | ComplementablyEmbeds E X.val} = {T | T.IsIllFounded} := by
  obtain ⟨Φ, hΦ, hW, hI⟩ := exists_borelReduction E
  refine ⟨Φ, hΦ, Set.ext fun T => ⟨?_, ?_⟩⟩
  · intro hT
    by_contra! hn
    have hw : T.IsWellFounded := Set.not_nonempty_iff_eq_empty.mp hn
    exact hE (hp.2 (X := RealBanachSpace.of E) (Y := RealBanachSpace.of (Φ T).val) hT (hW T hw p hp.1))
  · intro hT
    obtain ⟨i, r, _, hr⟩ := hI T hT
    exact ⟨i.toContinuousLinearMap, r, hr⟩

/-- The class of spaces containing a complemented copy of a fixed space is
complete analytic under the hypothesis of the manuscript's corollary. -/
theorem completeAnalytic_complementablyEmbeds
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [SeparableSpace E]
    (p : RealBanachSpace → Prop) (hp : IsL1StableComplementedProperty p)
    (hE : ¬ p (RealBanachSpace.of E)) :
    @AnalyticSet BanachCode banachCodePolishTopology {X | ComplementablyEmbeds E X.val} ∧
      ∀ (Y Z : Type*) [MeasurableSpace Y] [StandardBorelSpace Y]
        [MeasurableSpace Z] [StandardBorelSpace Z] (g : Z → Y) (B : Set Z),
        Measurable g → MeasurableSet B →
        ∃ f : Y → BanachCode, Measurable f ∧
          f ⁻¹' {X | ComplementablyEmbeds E X.val} = g '' B := by
  refine ⟨analyticSet_complementablyEmbeds E, ?_⟩
  intro Y Z _ _ _ _ g B hg hB
  obtain ⟨f, hf, he⟩ := NatTree.analyticImage_reduces_illFounded hg hB
  obtain ⟨Φ, hΦ, hΦe⟩ := exists_reduction_complementablyEmbeds E p hp hE
  refine ⟨Φ ∘ f, hΦ.comp hf, ?_⟩
  rw [Set.preimage_comp, hΦe, he]

end PaperFormalization
