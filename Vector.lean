import Utils

namespace Vector
-- Brief detour into defining a vector
-- we're using the subtype notation
abbrev Vector (α : Type u) (n : Nat) := { l : List α // l.length = n }

def Vector.nil : Vector α 0 := ⟨[], rfl⟩
def Vector.cons {α : Type u} (e : α) (v : Vector α n) : Vector α (n + 1) :=
  ⟨e :: v.val, by simp exact v.property⟩
def Vector.length {α : Type u} (_ : Vector α n) := n
def Vector.nth {α : Type u} (v : Vector α n) (idx : Fin n) :=
  let p : idx.val < v.val.length := by rw [v.property] exact idx.isLt
  v.val[idx.val]'p
def Vector.set {α : Type u} (v : Vector α n) (idx : Fin n) (el : α) : Vector α n :=
  ⟨ v.val.set idx.val el, by simp exact v.property ⟩
def Vector.fromList {α} (l : List α) : Vector α l.length := ⟨ l,  rfl ⟩

def Vector.mkSize {α} (default : α) (n : Nat) : Vector α n :=
  ⟨ Utils.List.mkLength default n, Utils.List.mkLengthCorrect ⟩

def Vector.enum {α : Type u} {n : Nat} (l : Vector α n) : Vector (Fin n × α) n :=
  -- this is a proof that List (Fin l.length × α) = List (Fin n × a)
  let l' : List (Fin n × α) := (Eq.symm l.property) ▸ Utils.enumFin l.val
  
  let p : List.length l' = n := by
    cases l with
    | mk val => 
      subst n
      simp
      exact Eq.symm (Utils.enumFin_preserves_length val)

  ⟨ l', p ⟩
 
notation a ":::" b => Vector.cons a b

end Vector
