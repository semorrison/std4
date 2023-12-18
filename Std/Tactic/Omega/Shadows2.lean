
def darkShadow (L U : List (Int × Nat)) : Prop :=
  ∀ l, l ∈ L → ∀ u, u ∈ U → l.2 * u.1 - u.2 * l.1 ≥ l.2 * u.2 - l.2 - u.2 + 1

def greyShadowIndices (m : Nat) (cs : List Nat) : List (Nat × Nat) :=
  cs.enum.bind fun (i, c) => (i, ·) <$> if c ≤ 1 then .nil else List.range ((c * m - c - m)/m + 1)

def greyShadowComponent_eq (v : Int) (L : List (Int × Nat)) (a : Nat × Nat) : Prop :=
  match L.get? a.1 with
  | none => True
  | some (f, c) => c * v - f = a.2

def greyShadowComponent_gt (v : Int) (m : Nat) (L : List (Int × Nat)) (a : Nat × Nat) (i : Nat) : Prop :=
  match L.get? i, decide (i < a.1) with
  | some (f, c), true => c * v - f > (c * m - c - m)/m
  | _, _ => True

def greyShadowComponent (v : Int) (m : Nat) (L : List (Int × Nat)) (a : Nat × Nat) : Prop :=
  greyShadowComponent_eq v L a ∧
  (List.range a.1).foldr (init := True) fun i P => greyShadowComponent_gt v m L a i ∧ P

def greyShadow (v : Int) (m : Nat) (L : List (Int × Nat)) : Prop :=
  ∃ a, a ∈ greyShadowIndices m ((·.2) <$> L) ∧ greyShadowComponent v m L a

theorem greyShadowComponent_eq_of_greyShadowComponent (w : greyShadowComponent v m L a) :
    greyShadowComponent_eq v L a := w.1
theorem greyShadowComponent_gt_of_greyShadowComponent (w : greyShadowComponent v m L a) (i : Nat) :
    greyShadowComponent_gt v m L a i :=
  sorry

theorem shadows (v : Int) (L U : List (Int × Nat))
    (L_sat : ∀ l, l ∈ L → l.1 ≤ l.2 * v) (U_sat : ∀ u, u ∈ U → u.2 * v ≤ u.1) :
    darkShadow L U ∨ greyShadow v sorry L :=
  sorry

def darkShadow_contraints : sorry := sorry
theorem darkShadow_constraints_sat : sorry := sorry

def greyShadow_eq_constraint : sorry := sorry
theorem greyShadow_eq_constraint_sat : sorry := sorry

def greyShadow_gt_constraints : sorry := sorry
theorem greyShadow_gt_constraints_sat : sorry := sorry
