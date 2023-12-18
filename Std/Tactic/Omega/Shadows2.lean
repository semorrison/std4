import Std.Tactic.Omega.Shadows
import Std.Tactic.Omega.Constraint
import Std.Tactic.Omega.Core

set_option linter.missingDocs false

namespace Std.Tactic.Omega

-- Recall that `(f, c)` a lower bound means `f ≤ c * v`
-- and `(f, c)` an upper bound means `c * v ≤ f`.

-- Given `⟨x, s, j⟩ : Fact` and `c` the coefficient of `v` in `x`:
-- If `c > 0` then we match `s` against `⟨some r, _⟩`.
-- `j` can provide a proof that `r ≤ dot x atoms`
-- Thus the lower bound is `(f, c)` where `f = r - dot x atoms + c * v ≤ c * v`.

-- If on the other hand `c < 0`, then we match `s` against `⟨_, some r⟩`.
-- `j` can provide a proof that `dot x atoms ≤ r`
-- Thus the lower bound is `(f, -c)` where `f = dot x atoms - r + (-c) * v ≤ (-c) * v`/
def Shadows
    (v : Int) (atoms : Coeffs)
    (lowerBounds upperBounds : List ({ p : Coeffs × Constraint // p.2.sat' p.1 atoms } × Int)) : Prop :=
  let lowerBounds' : List (Int × Int) := lowerBounds.filterMap fun ⟨⟨⟨x, s⟩, _⟩, c⟩ =>
    if c > 0 then
      if let ⟨some r, _⟩ := s then
        -- `r ≤ dot x atoms`, so `r - dot x atoms + c * v ≤ c * v`
        some (r - Coeffs.dot x atoms + c * v, c)
      else
        none
    else
      if let ⟨_, some r⟩ := s then
        -- `dot x atoms ≤ r` so `Coeffs.dot x atoms - r + (-c) * v ≤ (-c) * v`
        some (Coeffs.dot x atoms - r + (-c) * v, -c)
      else
        none
  let upperBounds' : List (Int × Int) := upperBounds.filterMap fun ⟨⟨⟨x, s⟩, _⟩, c⟩ =>
    if c > 0 then
      if let ⟨_, some r⟩ := s then
        -- `dot x atoms ≤ r`, so `c * v ≤ r - dot x atoms + c * v`
        some (r - Coeffs.dot x atoms + c * v, c)
      else
        none
    else
      if let ⟨some r, _⟩ := s then
        -- `r ≤ dot x atoms`, so `c * v ≤ dot x atoms - r + (-c) * v`
        some (Coeffs.dot x atoms - r + (-c) * v, -c)
      else
        none
  let m := upperBounds.map (·.2.natAbs) |>.maximum? |>.getD 0
  (darkShadow v lowerBounds' upperBounds') ∨ (greyShadows v m lowerBounds' none)

theorem shadows_sat'
    (v : Int) (atoms : Coeffs)
    (lowerBounds upperBounds : List ({ p : Coeffs × Constraint // p.2.sat' p.1 atoms } × Int))
    (lowerBounds_nz : ∀ p, p ∈ lowerBounds → p.2 ≠ 0)
    (two_le_m : 2 ≤ (upperBounds.map (·.2.natAbs) |>.maximum? |>.getD 0 : Int)) :
    Shadows v atoms lowerBounds upperBounds := by
  apply shadows_sat _ _ two_le_m
  · simp only [List.mem_filterMap, forall_exists_index, and_imp]
    intro (f, c) (⟨(x, s), w⟩, c') m
    dsimp
    split <;> rename_i h
    · split
      · simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
        rintro - rfl
        assumption
      · simp
    · split
      · simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
        rintro - rfl
        specialize lowerBounds_nz _ m
        dsimp at *
        rw [Int.not_lt] at h
        apply Int.neg_pos_of_neg
        rw [Int.lt_iff_le_and_ne]
        exact ⟨h, lowerBounds_nz⟩
      · simp
  · intro (f, c) m
    simp at m
    simp
    obtain ⟨⟨⟨⟨x, s⟩, w⟩, c'⟩, m, h⟩ := m
    split at h <;> rename_i h'
    · split at h <;> rename_i h'' _
      · simp at h
        obtain ⟨rfl, rfl⟩ := h
        subst h''
        simp [Constraint.sat', Constraint.sat] at w
        apply Int.add_le_of_le_sub_right
        rw [Int.sub_self]
        apply Int.sub_nonpos_of_le w.1
      · simp at h
    · split at h <;> rename_i h'' _
      · simp at h
        obtain ⟨rfl, rfl⟩ := h
        subst h''
        simp [Constraint.sat', Constraint.sat] at w
        apply Int.add_le_of_le_sub_right
        rw [Int.sub_self]
        apply Int.sub_nonpos_of_le w.2
      · simp at h
  · intro (f, c) m
    simp at m
    simp
    obtain ⟨⟨⟨⟨x, s⟩, w⟩, c'⟩, m, h⟩ := m
    split at h <;> rename_i h'
    · split at h <;> rename_i h'' _
      · simp at h
        obtain ⟨rfl, rfl⟩ := h
        subst h''
        simp [Constraint.sat', Constraint.sat] at w
        exact Int.le_add_of_nonneg_left (Int.sub_nonneg_of_le w.2)
      · simp at h
    · split at h <;> rename_i h'' _
      · simp at h
        obtain ⟨rfl, rfl⟩ := h
        subst h''
        simp [Constraint.sat', Constraint.sat] at w
        exact Int.le_add_of_nonneg_left (Int.sub_nonneg_of_le w.1)
      · simp at h
  · simp only [List.mem_filterMap, forall_exists_index, and_imp]
    intro (f, c) m
    split
    · split
      · simp
        rintro mem rfl rfl
        replace mem := List.mem_map_of_mem (fun x => (x.2.natAbs : Int)) mem
        sorry -- true but tedious!
      · simp
    · split
      · simp
        rintro mem rfl rfl
        sorry -- true but tedious!
      · simp
