import Lean
import Std

theorem foldr_or_of_exists_mem {L : List α} {P : α → Prop} (w : ∃ a, a ∈ L ∧ P a) :
    L.foldr (init := False) (fun a Q => P a ∨ Q) := by
  induction L with
  | nil => simp_all
  | cons a L ih =>
    simp only [List.mem_cons, exists_eq_or_imp] at w
    rcases w with (w₁ | w₂)
    · left
      exact w₁
    · right
      exact ih w₂

open Lean Meta

/--
Suppose that in the context of a goal `g`, we have a proof `w` that `∃ a, a ∈ A ∧ P a`.
(Here `A : List α` and `P : α → Prop`.)

We would like to split that goal according to the alternatives `P a₁ ∨ P a₂ ∨ ... ∨ P aₙ`,
and in each alternative run a monadic function `run aᵢ gᵢ wᵢ`, accumulating a value,
where `gᵢ` is the subgoal in which `wᵢ` is a proof that `P aᵢ`.
-/
def runInAlternatives (A : List α)
    (run : α → MVarId → Expr → β → MetaM β)
    (g : MVarId) (w : Expr) (init : β) : MetaM β := do
  -- `w` is a proof, valid in `g`'s context, that `P a₁ ∨ P a₂ ∨ ... ∨ P aₙ ∨ False`
  -- (right associated).
  let w' ← mkAppM ``foldr_or_of_exists_mem #[w]
  let (_, _, b) ← A.foldlM (init := (g, w', init)) fun ⟨g, w, b⟩ a => do
    let (⟨g₁, w₁⟩, ⟨g₂, w₂⟩) ← g.cases₂ w
    let b₂ ← run a g₁ (.fvar w₁) b
    pure (g₂, (.fvar w₂), b₂)
  return b
