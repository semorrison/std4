import Std.Logic
import Std.Tactic.RCases
import Std.Data.Int.Lemmas
import Std

/--
Given a variable `v : Int`, the largest coefficient `m` of `v` in an upper bound for `v`,
and the collection `bounds` of lower bounds for `v` described as a `List (Int × Int)`
(where for each `(f, c)` we have `f ≤ c * v`),
`greyShadows v m bounds none` is the proposition describing the "grey" shadows alternatives
in the `omega` algorithm.

Namely, the disjunction over lower bounds `f ≤ c * v` and `j = 0, 1, ..., (c * m - c - m)/m`
of `c * v = j` and for each previously considered lower bound `c * v - f > (c * m - c - m)/m`.
-/
def greyShadows (v m : Int) : List (Int × Int) → Option Nat → Prop
  | [], _ => False
  | (f, c) :: bounds, none =>
    greyShadows v m ((f, c) :: bounds) (some ((c * m - c - m)/m).natAbs)
  | (f, c) :: bounds, some 0 =>
    c * v - f = 0 ∨ c * v - f > (c * m - c - m)/m ∧ greyShadows v m bounds none
  | (f, c) :: bounds, some (j + 1) =>
    c * v - f = j + 1 ∨ greyShadows v m ((f, c) :: bounds) j
termination_by greyShadows v m bounds j => (bounds, if j.isNone then 1 else 0, j.getD 0)
decreasing_by sorry

def greyShadows' (v m : Int) (lowerBounds : List (Int × Int)) : Prop :=
    ∃ l, l ∈ lowerBounds ∧ ∃ j : Nat, j ≤ (l.2 * m - l.2 - m)/m ∧ l.2 * v - l.1 = j

theorem greyShadows_iff (v m : Int) (lowerBounds : List (Int × Int)) (sat : ∀ l, l ∈ lowerBounds → l.1 ≤ l.2 * v) :
    greyShadows v m lowerBounds none ↔ greyShadows' v m lowerBounds :=
  -- We'll need more intermediate steps here!
  sorry

def darkShadow (v : Int) : List (Int × Int) → List (Int × Int) → Prop
  | [], _ => True
  | (f, c) :: lowerBounds, upperBounds =>
    go (f, c) upperBounds ∧ darkShadow v lowerBounds upperBounds
where
  go : Int × Int → List (Int × Int) → Prop
  | _, [] => True
  | (f, c), (f', c') :: upperBounds =>
    c * f' - c' * f ≥ c * c' - c - c' + 1 ∧ go (f, c) upperBounds

theorem darkShadow_of_cons_right (h : darkShadow v l (q :: u)) : darkShadow v l u := sorry

theorem darkShadow_iff (v : Int) (lowerBounds upperBounds : List (Int × Int)) :
    darkShadow v lowerBounds upperBounds ↔
      ∀ l u, l ∈ lowerBounds → u ∈ upperBounds →
        l.2 * u.1 - u.2 * l.1 ≥ l.2 * u.2 - l.2 - u.2 + 1 := by
  induction lowerBounds generalizing upperBounds with
  | nil => simp [darkShadow]
  | cons p lowerBounds ih =>
    simp only [darkShadow, List.mem_cons, ge_iff_le]
    constructor
    · rintro ⟨h₁, h₂⟩ l u l_mem u_mem
      rcases l_mem with rfl | l_mem
      · clear ih
        induction upperBounds with
        | nil => simp_all
        | cons q upperBounds ih' =>
          rw [darkShadow.go] at h₁
          cases u_mem with
          | head _ => exact h₁.1
          | tail q m =>
            apply ih'
            · exact darkShadow_of_cons_right h₂
            · exact m
            · exact h₁.2
      · rw [ih] at h₂
        exact h₂ l u l_mem u_mem
    · intro h
      constructor
      · specialize h p
        replace h := fun u => h u (.inl rfl)
        clear ih
        induction upperBounds with
        | nil => trivial
        | cons q upperBounds ih' =>
          dsimp [darkShadow.go]
          constructor
          · exact h q (List.mem_cons_self _ _)
          · apply ih'
            intro u u_mem
            exact h u (List.mem_cons_of_mem _ u_mem)
      · rw [ih]
        intro l u l_mem u_mem
        exact h l u (.inr l_mem) u_mem

theorem shadows_sat (v m : Int) (lowerBounds upperBounds : List (Int × Int))
    (lowerBounds_sat : ∀ l, l ∈ lowerBounds → l.1 ≤ l.2 * v) :
    (darkShadow v lowerBounds upperBounds) ∨ (greyShadows v m lowerBounds none) := by
  rw [Classical.or_iff_not_imp_left]
  intro h
  rw [darkShadow_iff] at h
  rw [Classical.not_forall] at h
  obtain ⟨l, h⟩ := h
  rw [Classical.not_forall] at h
  obtain ⟨u, h⟩ := h
  rw [Classical.not_forall] at h
  obtain ⟨l_mem, h⟩ := h
  rw [Classical.not_forall] at h
  obtain ⟨u_mem, h⟩ := h
  rw [Int.not_le] at h
  rw [greyShadows_iff _ _ _ lowerBounds_sat, greyShadows']
  refine ⟨l, l_mem, ?_⟩
  refine ⟨(l.2 * v - l.1).natAbs, ?_⟩
  rw [Int.natAbs_of_nonneg sorry] -- easy from `lowerBounds_sat`
  refine ⟨?_, rfl⟩
  sorry -- Still a bit of work from here, need a fact about `m`
