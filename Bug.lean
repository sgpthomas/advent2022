abbrev Vector (α : Type u) (n : Nat) := { l : List α // l.length = n }

def Vector.enum {α : Type u} {n : Nat} (l : Vector α n) : Vector (Fin n × α) n :=
  match Nat.decLt 0 n with
  | isTrue p =>
    let l' := l.val.map (λ a => (Fin.mk 0 p, a))
    let p' : List.length l' = n := by
      induction l.property with
      | refl => simp
    ⟨ l', p' ⟩
  | isFalse _ =>
    let p := by
      have lprop := l.property
      simp_arith [*] at *
      subst n
      rfl
    ⟨ [], p ⟩
