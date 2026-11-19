import PaperFormalization.Basic

namespace PaperFormalization

open scoped ENNReal

/-- Bundled real Banach spaces on which isomorphism-invariant properties are predicates. -/
structure RealBanachSpace where
  carrier : Type
  [normedAddCommGroup : NormedAddCommGroup carrier]
  [normedSpace : NormedSpace ℝ carrier]
  [completeSpace : CompleteSpace carrier]

attribute [instance] RealBanachSpace.normedAddCommGroup RealBanachSpace.normedSpace
  RealBanachSpace.completeSpace

instance RealBanachSpace.instCoeSort : CoeSort RealBanachSpace Type :=
  ⟨RealBanachSpace.carrier⟩

/-- Bundle a type with its real Banach-space structure. -/
abbrev RealBanachSpace.of (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] : RealBanachSpace :=
  ⟨X⟩

/-- Membership in the paper's class of properties stable under ℓ₁ sums. -/
structure IsL1StableProperty (p : RealBanachSpace → Prop) : Prop where
  invariant : ∀ {X Y : RealBanachSpace}, (X ≃L[ℝ] Y) → p X → p Y
  zero : p (RealBanachSpace.of PUnit)
  real : p (RealBanachSpace.of ℝ)
  sum : ∀ {ι : Type} (F : ι → RealBanachSpace), (∀ i, p (F i)) →
    p (RealBanachSpace.of (lp (fun i => (F i : Type)) 1))

/-- The subclass of sum-stable properties inherited by complemented subspaces. -/
def IsL1StableComplementedProperty (p : RealBanachSpace → Prop) : Prop :=
  IsL1StableProperty p ∧
    ∀ {X Y : RealBanachSpace}, ComplementablyEmbeds X Y → p Y → p X

namespace IsL1StableProperty

variable {p : RealBanachSpace → Prop}

theorem of_subsingleton (h : IsL1StableProperty p) (X : RealBanachSpace) [Subsingleton X] : p X :=
  h.invariant (X := RealBanachSpace.of PUnit) (Y := X)
    { LinearEquiv.ofSubsingleton (R := ℝ) PUnit (X : Type) with
      continuous_toFun := continuous_const
      continuous_invFun := continuous_const } h.zero

theorem of_finrank_le_one (h : IsL1StableProperty p) (X : RealBanachSpace)
    [FiniteDimensional ℝ X] (hX : Module.finrank ℝ X ≤ 1) : p X := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hX with hzero | hone
  · let _ : Subsingleton X := Module.finrank_zero_iff.mp hzero
    exact h.of_subsingleton X
  · let e : ℝ ≃L[ℝ] X := ContinuousLinearEquiv.ofFinrankEq (by simpa using hone.symm)
    exact h.invariant (X := RealBanachSpace.of ℝ) (Y := X) e h.real

end IsL1StableProperty

/-- A two-coordinate ℓ₁ sum is continuously linearly equivalent to the product. -/
noncomputable def l1BoolProductEquiv (F : Bool → RealBanachSpace) :
    lp (fun b => (F b : Type)) 1 ≃L[ℝ] (F false × F true) := by
  let f := (lp.evalCLM ℝ (fun b => (F b : Type)) 1 false).prod
    (lp.evalCLM ℝ (fun b => (F b : Type)) 1 true)
  apply ContinuousLinearEquiv.ofBijective f
  · apply LinearMap.ker_eq_bot.mpr
    intro x y he
    refine lp.ext (funext fun b => ?_)
    cases b
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he
  · apply LinearMap.range_eq_top.mpr
    intro y
    let x : ∀ b, F b := fun b => Bool.rec y.1 y.2 b
    exact ⟨⟨x, Memℓp.all x⟩, rfl⟩

theorem IsL1StableProperty.prod {p : RealBanachSpace → Prop} (h : IsL1StableProperty p)
    (X Y : RealBanachSpace) (hX : p X) (hY : p Y) : p (RealBanachSpace.of (X × Y)) := by
  let F : Bool → RealBanachSpace
    | false => X
    | true => Y
  exact h.invariant (l1BoolProductEquiv F) (h.sum F fun b => by cases b <;> assumption)

end PaperFormalization
