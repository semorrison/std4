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
    if c = 1 then
      greyShadows v m bounds none
    else
      greyShadows v m ((f, c) :: bounds) (some ((c * m - c - m)/m).toNat)
  | (f, c) :: bounds, some 0 =>
    c * v - f = 0 ∨ c * v - f > (c * m - c - m)/m ∧ greyShadows v m bounds none
  | (f, c) :: bounds, some (j + 1) =>
    c * v - f = j + 1 ∨ greyShadows v m ((f, c) :: bounds) j
termination_by greyShadows v m bounds j => (bounds, if j.isNone then 1 else 0, j.getD 0)
decreasing_by sorry

def greyShadows' (v m : Int) (lowerBounds : List (Int × Int)) : Prop :=
    ∃ l, l ∈ lowerBounds ∧ ∃ j : Nat, j ≤ (l.2 * m - l.2 - m)/m ∧ l.2 * v - l.1 = j

theorem greyShadows_iff_aux :
    greyShadows v m ((f, c) :: lowerBounds) (some j) ↔
      (∃ j' : Nat, j' ≤ j ∧ c * v - f = j') ∨
        ((c * m - c - m) / m < c * v - f ∧ greyShadows v m lowerBounds none) := by
  induction j with
  | zero =>
    simp [greyShadows]
  | succ j ih =>
    rw [greyShadows, ih]
    have : ∀ a, a ≤ j + 1 ↔ a = j + 1 ∨ a ≤ j := by
      intro a
      constructor
      · exact fun h => or_comm.mp (Nat.le_or_eq_of_le_succ h)
      · rintro (h | h)
        · exact Nat.le_of_eq h
        · exact Nat.le_succ_of_le h
    simp only [this]
    simp [exists_eq_or_imp]
    rw [or_assoc]

-- These sorries are just arithmetic:
theorem greyShadows_of (v m : Int)
    (two_le_m : 2 ≤ m)
    (lowerBounds : List (Int × Int))
    (lowerBounds_pos : ∀ l, l ∈ lowerBounds → 0 < l.2)
    (sat : ∀ l, l ∈ lowerBounds → l.1 ≤ l.2 * v) :
      greyShadows' v m lowerBounds → greyShadows v m lowerBounds none := by
  induction lowerBounds with
  | nil => simp [greyShadows, greyShadows']
  | cons p lowerBounds ih =>
    rcases p with ⟨f, c⟩
    rw [greyShadows, greyShadows_iff_aux]
    split <;> rename_i hc
    · subst hc
      rw [greyShadows']
      have w : ∀ j : Nat, j ≤ (m - 1 - m) / m ↔ False := sorry
      simp only [w, List.mem_cons, exists_eq_or_imp, Int.one_mul, false_and, exists_const, false_or]
      rw [← greyShadows']
      apply ih
      · exact fun p m => lowerBounds_pos p (List.mem_cons_of_mem _ m)
      · exact fun p m => sat p (List.mem_cons_of_mem _ m)
    · replace hc : 2 ≤ c := sorry
      rw [greyShadows']
      simp
      rw [← greyShadows']
      intro h
      rcases h with ⟨j, le, eq⟩ | h
      · left
        refine ⟨j, ?_, eq⟩
        · rw [← Int.ofNat_le]
          rw [Int.toNat_of_nonneg]
          exact le
          sorry
      · rw [Classical.or_iff_not_imp_left]
        simp
        intro h'
        constructor
        · sorry
        · apply ih _ _ h
          · exact fun p m => lowerBounds_pos p (List.mem_cons_of_mem _ m)
          · exact fun p m => sat p (List.mem_cons_of_mem _ m)

def darkShadow (v : Int) : List (Int × Int) → List (Int × Int) → Prop
  | [], _ => True
  | (f, c) :: lowerBounds, upperBounds =>
    go (f, c) upperBounds ∧ darkShadow v lowerBounds upperBounds
where
  go : Int × Int → List (Int × Int) → Prop
  | _, [] => True
  | (f, c), (f', c') :: upperBounds =>
    c * f' - c' * f ≥ c * c' - c - c' + 1 ∧ go (f, c) upperBounds

theorem darkShadow_of_cons_right (h : darkShadow v l (q :: u)) : darkShadow v l u := by
  induction l with
  | nil => simp [darkShadow]
  | cons p l ih => sorry

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

instance : @Trans Int Int Int (· ≤ ·) (· ≤ ·) (· ≤ ·) := sorry

-- The sorries here are all easy.
theorem shadows_sat (v m : Int) (two_le_m : 2 ≤ m) (lowerBounds upperBounds : List (Int × Int))
    (lowerBounds_pos : ∀ l, l ∈ lowerBounds → 0 < l.2)
    (lowerBounds_sat : ∀ l, l ∈ lowerBounds → l.1 ≤ l.2 * v)
    (upperBounds_sat : ∀ u, u ∈ upperBounds → u.2 * v ≤ u.1)
    (mh : ∀ u, u ∈ upperBounds → u.2 ≤ m) :
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
  apply greyShadows_of _ _ two_le_m _ lowerBounds_pos lowerBounds_sat
  rw [greyShadows']
  refine ⟨l, l_mem, ?_⟩
  rcases l with ⟨c, f⟩
  rcases u with ⟨c', f'⟩
  refine ⟨(f * v - c).natAbs, ?_⟩
  specialize upperBounds_sat _ u_mem
  specialize lowerBounds_sat _ l_mem
  specialize mh _ u_mem
  dsimp at *
  rw [Int.natAbs_of_nonneg sorry] -- easy from `lowerBounds_sat`
  refine ⟨?_, rfl⟩
  have w := calc
    f' * (f * v - c) = f * (f' * v) - f' * c := sorry
    _ ≤ f * c' - f' * c := sorry
    _ ≤ f * f' - f - f' := sorry
  have w' : f * v - c ≤ (f * f' - f - f') / f' := sorry
  sorry
