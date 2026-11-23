import PaperFormalization.CodingCorollaries
import PaperFormalization.RadonNikodymProperty
import PaperFormalization.SchurProperty
import PaperFormalization.TreeOrder
import PaperFormalization.BranchGeometry
import PaperFormalization.DualCoding

/-! # Definitions used in the manuscript
Each `#check` resolves the existing definition. The preceding comment
shows its actual source definition without introducing a second definition. -/

/-
def HasApproximationProperty (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ K : Set E, IsCompact K →
    ∃ A : E →L[ℝ] E, FiniteDimensional ℝ A.toLinearMap.range ∧
      ∀ x ∈ K, ‖x - A x‖ ≤ ε
-/
#check @PaperFormalization.HasApproximationProperty

/-
def ComplementablyEmbeds (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] : Prop :=
  ∃ i : E →L[ℝ] F, ∃ r : F →L[ℝ] E, Function.LeftInverse r i
-/
#check @PaperFormalization.ComplementablyEmbeds

/-
def IsometricOneComplementablyEmbeds (E F : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] : Prop :=
  ∃ i : E →ₗᵢ[ℝ] F, ∃ r : F →L[ℝ] E, ‖r‖ ≤ 1 ∧ Function.LeftInverse r i
-/
#check @PaperFormalization.IsometricOneComplementablyEmbeds

/-
def IsometricallyComplementablyEmbeds (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] : Prop :=
  ∃ i : E →ₗᵢ[ℝ] F, ∃ r : F →L[ℝ] E, Function.LeftInverse r i
-/
#check @PaperFormalization.IsometricallyComplementablyEmbeds

/-
def NatTree := {T : Set (List ℕ) // ∀ s t, s <+: t → t ∈ T → s ∈ T}
-/
#check @PaperFormalization.NatTree

/-
def branches (T : NatTree) : Set (ℕ → ℕ) :=
  {b | ∀ n, List.ofFn (fun i : Fin n => b i) ∈ T.val}
-/
#check @PaperFormalization.NatTree.branches

/-
def IsWellFounded (T : NatTree) : Prop := T.branches = ∅
-/
#check @PaperFormalization.NatTree.IsWellFounded

/-
def IsIllFounded (T : NatTree) : Prop := T.branches.Nonempty
-/
#check @PaperFormalization.NatTree.IsIllFounded

/-
def BorelAnalytic {X : Type*} [MeasurableSpace X] (A : Set X) : Prop :=
  ∃ B : Set (ℕ → ℕ), MeasurableSet B ∧ ∃ f : B → X, Measurable f ∧ range f = A
-/
#check @PaperFormalization.BorelAnalytic

/-
def BorelCoanalytic {X : Type*} [MeasurableSpace X] (A : Set X) : Prop :=
  BorelAnalytic Aᶜ
-/
#check @PaperFormalization.BorelCoanalytic

/-
def BorelReduces {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (A : Set X) (B : Set Y) : Prop :=
  ∃ f : X → Y, Measurable f ∧ f ⁻¹' B = A
-/
#check @PaperFormalization.BorelReduces

/-
def CompleteAnalytic {X : Type*} [MeasurableSpace X] (A : Set X) : Prop :=
  BorelAnalytic A ∧ ∀ (Y : Type) [MeasurableSpace Y] [StandardBorelSpace Y] (B : Set Y),
    BorelAnalytic B → BorelReduces B A
-/
#check @PaperFormalization.CompleteAnalytic

/-
def CompleteCoanalytic {X : Type*} [MeasurableSpace X] (A : Set X) : Prop :=
  CompleteAnalytic Aᶜ
-/
#check @PaperFormalization.CompleteCoanalytic

/-
structure IsL1StableProperty (p : RealBanachSpace → Prop) : Prop where
  invariant : ∀ {X Y : RealBanachSpace}, (X ≃L[ℝ] Y) → p X → p Y
  zero : p (RealBanachSpace.of PUnit)
  real : p (RealBanachSpace.of ℝ)
  sum : ∀ {ι : Type} (F : ι → RealBanachSpace), (∀ i, p (F i)) →
    p (RealBanachSpace.of (lp (fun i => (F i : Type)) 1))
-/
#check @PaperFormalization.IsL1StableProperty

/-
def IsL1StableComplementedProperty (p : RealBanachSpace → Prop) : Prop :=
  IsL1StableProperty p ∧
    ∀ {X Y : RealBanachSpace}, ComplementablyEmbeds X Y → p Y → p X
-/
#check @PaperFormalization.IsL1StableComplementedProperty

/-
def ClosedSubspaces (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  {W : Submodule ℝ E // IsClosed (W : Set E)}
-/
#check @PaperFormalization.ClosedSubspaces

/-
def hit (U : Set E) : Set (ClosedSubspaces E) :=
  {W | ((W.val : Set E) ∩ U).Nonempty}
-/
#check @PaperFormalization.ClosedSubspaces.hit

/-
abbrev BanachAmbient := C(Set.Icc (0 : ℝ) 1, ℝ)
-/
#check @PaperFormalization.BanachAmbient

/-
abbrev BanachCode := ClosedSubspaces BanachAmbient
-/
#check @PaperFormalization.BanachCode

/-
def complementedClass (E : BanachCode) : Set BanachCode :=
  {X | ComplementablyEmbeds E.val X.val}
-/
#check @PaperFormalization.complementedClass

/-
def isometricComplementedClass (E : BanachCode) : Set BanachCode :=
  {X | IsometricallyComplementablyEmbeds E.val X.val}
-/
#check @PaperFormalization.isometricComplementedClass

/-
def approximationPropertyClass : Set BanachCode := {X | HasApproximationProperty X.val}
-/
#check @PaperFormalization.approximationPropertyClass

/-
def HasSchurProperty (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∀ x : ℕ → E, WeaklyNull x → Tendsto x atTop (𝓝 0)
-/
#check @PaperFormalization.HasSchurProperty

/-
def HasRadonNikodymProperty (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∀ (Ω : Type v) [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ν : VectorMeasure Ω E), IsFiniteMeasure ν.variation → ν ≪ᵥ μ.toENNRealVectorMeasure →
      ∃ f : Ω → E, Integrable f μ ∧ μ.withDensityᵥ f = ν
-/
#check @PaperFormalization.HasRadonNikodymProperty

/-
abbrev L1 (ι : Type*) := lp (fun _ : ι => ℝ) 1
-/
#check @PaperFormalization.L1

/-
noncomputable def branchKernelSpan {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : L1 ℕ →L[ℝ] E) : Submodule ℝ (L1 (List ℕ)) :=
  (⨆ b : ℕ → ℕ, P.toLinearMap.ker.map (branchInclusion b).toLinearMap).topologicalClosure
-/
#check @PaperFormalization.branchKernelSpan

/-
abbrev TreeQuotient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : L1 ℕ →L[ℝ] E) := L1 (List ℕ) ⧸ branchKernelSpan P
-/
#check @PaperFormalization.TreeQuotient

/-
noncomputable def branchOperator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : L1 ℕ →L[ℝ] E) (b : ℕ → ℕ) : supportedL1 (branchTree b) →L[ℝ] E :=
  P.comp (branchEnumerationIsometry b).toLinearIsometry.toContinuousLinearMap
-/
#check @PaperFormalization.branchOperator

/-
noncomputable def treeSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : L1 ℕ →L[ℝ] E) (T : NatTree) : Submodule ℝ (TreeQuotient P) :=
  (Submodule.span ℝ ((fun s => (branchKernelSpan P).mkQ (lp.single 1 s 1)) ''
    T.val)).topologicalClosure
-/
#check @PaperFormalization.treeSpace

/-
def derivative (T : NatTree) : NatTree :=
  ⟨{s | ∃ m : ℕ, s ++ [m] ∈ T.val}, by
    intro s t hst ht
    obtain ⟨m, hm⟩ := ht
    obtain ⟨u, rfl⟩ := hst
    cases u with
    | nil => exact ⟨m, by simpa only [List.append_nil] using hm⟩
    | cons i u =>
      exact ⟨i, T.property _ _ ⟨u ++ [m], by simp [List.append_assoc]⟩ hm⟩⟩
-/
#check @PaperFormalization.NatTree.derivative

/-
noncomputable def prune (T : NatTree) (α : Ordinal.{0}) : NatTree :=
  @Ordinal.limitRecOn (fun _ => NatTree) α T (fun _ S => S.derivative)
    (fun α _ prev => intersectStages α prev)
-/
#check @PaperFormalization.NatTree.prune

/-
noncomputable def order (T : NatTree) (hT : T.IsWellFounded) : Ordinal :=
  if [] ∈ T.val then Order.succ (acc_isChild hT).rank else 0
-/
#check @PaperFormalization.NatTree.order
