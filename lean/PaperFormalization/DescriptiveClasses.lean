import PaperFormalization.AnalyticPreimage
import PaperFormalization.TreeCompleteness

namespace PaperFormalization

open Set MeasureTheory

/-- Analyticity in a standard Borel space, using measurable images of Borel subspaces
of Baire space. -/
def BorelAnalytic {X : Type*} [MeasurableSpace X] (A : Set X) : Prop :=
  ∃ B : Set (ℕ → ℕ), MeasurableSet B ∧ ∃ f : B → X, Measurable f ∧ range f = A

/-- Coanalyticity is analyticity of the complement. -/
def BorelCoanalytic {X : Type*} [MeasurableSpace X] (A : Set X) : Prop :=
  BorelAnalytic Aᶜ

/-- A Borel reduction realizes the source set as a Borel preimage of the target set. -/
def BorelReduces {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (A : Set X) (B : Set Y) : Prop :=
  ∃ f : X → Y, Measurable f ∧ f ⁻¹' B = A

namespace BorelReduces

theorem trans {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    {A : Set X} {B : Set Y} {C : Set Z} (hAB : BorelReduces A B) (hBC : BorelReduces B C) :
    BorelReduces A C := by
  obtain ⟨f, hf, he⟩ := hAB
  obtain ⟨g, hg, hg'⟩ := hBC
  exact ⟨g ∘ f, hg.comp hf, by rw [preimage_comp, hg', he]⟩

theorem compl {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {A : Set X} {B : Set Y}
    (h : BorelReduces A B) : BorelReduces Aᶜ Bᶜ := by
  obtain ⟨f, hf, he⟩ := h
  exact ⟨f, hf, by rw [preimage_compl, he]⟩

end BorelReduces

/-- Complete analytic sets are analytic and Borel-hard for analytic sets. -/
def CompleteAnalytic {X : Type*} [MeasurableSpace X] (A : Set X) : Prop :=
  BorelAnalytic A ∧ ∀ (Y : Type) [MeasurableSpace Y] [StandardBorelSpace Y] (B : Set Y),
    BorelAnalytic B → BorelReduces B A

/-- Taking complements turns analytic completeness into coanalytic completeness. -/
def CompleteCoanalytic {X : Type*} [MeasurableSpace X] (A : Set X) : Prop :=
  CompleteAnalytic Aᶜ

namespace BorelAnalytic

theorem iff_analyticSet {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] (A : Set X) :
    BorelAnalytic A ↔ AnalyticSet A := by
  constructor
  · rintro ⟨B, hB, f, hf, rfl⟩
    have := hB.standardBorel
    simpa only [image_univ] using (MeasurableSet.univ : MeasurableSet (univ : Set B)).analyticSet_image hf
  · rw [AnalyticSet]
    rintro (rfl | ⟨f, hf, rfl⟩)
    · exact ⟨∅, MeasurableSet.empty, fun x => False.elim x.property, measurable_of_empty _,
        range_eq_empty _⟩
    · refine ⟨univ, MeasurableSet.univ, f ∘ Subtype.val,
        hf.measurable.comp measurable_subtype_coe, ?_⟩
      rw [range_comp, Subtype.range_coe, image_univ]

theorem of_measurable_image {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y]
    {B : Set X} {f : X → Y} (hB : MeasurableSet B) (hf : Measurable f) :
    BorelAnalytic (f '' B) := by
  let _ := upgradeStandardBorel Y
  exact (iff_analyticSet _).mpr (hB.analyticSet_image hf)

theorem preimage {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] {A : Set Y} (hA : BorelAnalytic A)
    {f : X → Y} (hf : Measurable f) : BorelAnalytic (f ⁻¹' A) := by
  let _ := upgradeStandardBorel X
  let _ := upgradeStandardBorel Y
  exact (iff_analyticSet _).mpr (analyticSet_preimage_measurable hf ((iff_analyticSet _).mp hA))

theorem reduces_illFounded {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    {A : Set X} (hA : BorelAnalytic A) :
    BorelReduces A {T : NatTree | T.IsIllFounded} := by
  let _ := upgradeStandardBorel X
  exact NatTree.analyticSet_reduces_illFounded ((iff_analyticSet _).mp hA)

end BorelAnalytic

theorem completeAnalytic_iff_illFounded_reduces
    {X : Type*} [MeasurableSpace X] {A : Set X} :
    CompleteAnalytic A ↔
      BorelAnalytic A ∧ BorelReduces {T : NatTree | T.IsIllFounded} A := by
  constructor
  · rintro ⟨hA, h⟩
    exact ⟨hA, h NatTree _ ((BorelAnalytic.iff_analyticSet _).mpr NatTree.analyticSet_illFounded)⟩
  · rintro ⟨hA, h⟩
    exact ⟨hA, fun Y _ _ B hB => hB.reduces_illFounded.trans h⟩

theorem CompleteAnalytic.reduces {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace Y] {A : Set X} {B : Set Y}
    (hA : CompleteAnalytic A) (hB : BorelAnalytic B) : BorelReduces B A :=
  hB.reduces_illFounded.trans (completeAnalytic_iff_illFounded_reduces.mp hA).2

theorem completeCoanalytic_iff_wellFounded_reduces
    {X : Type*} [MeasurableSpace X] {A : Set X} :
    CompleteCoanalytic A ↔
      BorelCoanalytic A ∧ BorelReduces {T : NatTree | T.IsWellFounded} A := by
  rw [CompleteCoanalytic, completeAnalytic_iff_illFounded_reduces, BorelCoanalytic]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    simpa only [NatTree.wellFounded_eq_compl_illFounded, compl_compl] using h.compl
  · intro h
    simpa only [NatTree.wellFounded_eq_compl_illFounded, compl_compl] using h.compl

end PaperFormalization
