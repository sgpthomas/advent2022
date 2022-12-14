import Utils

namespace Dec5

-- Brief detour into defining a vector
-- we're using the subtype notation
abbrev Vector (α : Type u) (n : Nat) := { l : List α // l.length = n }

theorem enum_from_preserves_items (α : Type u) (n : Nat) (l : List α) : (l.enumFrom n).map Prod.snd = l := by
  induction l generalizing n with
  | nil => simp [List.map]
  | cons hd tl IH => simp [List.enum, List.enumFrom, List.map]
                     specialize IH (n + 1)
                     rw [IH]
                     
theorem enum_preserves_items (α : Type u) (l : List α) : l.enum.map Prod.snd = l := by
  simp [List.enum]
  apply enum_from_preserves_items

theorem list_enum_preserves_length (α) (l : List α) : l.length = l.enum.length := by
  
                     
  -- simp [List.enum]
  -- induction l with
  -- | nil => simp [List.enumFrom]
  -- | cons hd tl IH => simp [List.enumFrom]

  -- induction l with
  -- | nil => simp
  -- | cons h t H => simp [List.enum]
  --                 rw [H]
  --                 simp [List.enum, List.enumFrom]

def Vector.nil : Vector α 0 := ⟨[], rfl⟩
def Vector.cons {α : Type u} (e : α) (v : Vector α n) : Vector α (n + 1) :=
  ⟨e :: v.val, by simp exact v.property⟩
def Vector.length {α : Type u} (_ : Vector α n) := n
def Vector.nth {α : Type u} (v : Vector α n) (idx : Fin n) :=
  let p : idx.val < v.val.length := by
    have x := v.property
    rw [x]
    exact idx.isLt
  v.val[idx.val]'p
def Vector.set {α : Type u} (v : Vector α n) (idx : Fin n) (el : α) : Vector α n :=
  ⟨ v.val.set idx.val el, by simp exact v.property ⟩
def Vector.fromList {α} (l : List α) : Vector α l.length := ⟨ l,  rfl ⟩
def Vector.enum {α} {n} (l : Vector α n) : Vector (Fin n × α) n :=
  let l' := List.enum
  let l' := l.val.enum.map (λ (i, a) => (Fin.mk i _, a))
  ⟨ l' , by simp ⟩

-- def Vector.foldlEnum {α β} {n} (f : α -> β -> Fin n -> α) (init : α) (v : Vector β n) : α :=
--   (h f init v).snd
-- where h {α β} {n} (f : α -> β -> Fin n -> α) (init : (Fin n × α)) (v : Vector β n) : (Fin n × α) :=
--   match v with
--   | [] => init
--   | h :: tl => h f init tl

notation a ":::" b => Vector.cons a b

structure StackMachine (n : Nat) where
  stacks : Vector (List Char) n
deriving Repr
  
def StackMachine.empty : StackMachine 0 :=
  StackMachine.mk $ Vector.nil
  
def StackMachine.addCol {n : Nat} (sm : StackMachine n) : StackMachine (n + 1) :=
  StackMachine.mk $ sm.stacks.cons []
  
def StackMachine.take {n : Nat} (frm : Fin n) (sm : StackMachine n) : Option (Char × StackMachine n) :=
  let stack := sm.stacks.nth frm
  match stack with
  | h :: tl => (h, StackMachine.mk $ sm.stacks.set frm tl)
  | [] => none
  
def StackMachine.place {n : Nat} (to : Fin n) (c : Char) (sm : StackMachine n) : StackMachine n :=
  let stack := sm.stacks.nth to
  StackMachine.mk $ sm.stacks.set to (c :: stack)
  
-- Move `num` boxes from stack `frm` to stack `to`
def StackMachine.move {n : Nat} (num : Nat) (frm : Fin n) (to : Fin n) (sm : StackMachine n) : StackMachine n :=
  match num with
  | 0 => sm
  | n + 1 => 
    let sm' := match sm.take frm with
               | some (c, sm') => sm'.place to c
               | none => sm
    sm'.move n frm to
    
-- #eval StackMachine.empty
--       |> StackMachine.addCol
--       |> StackMachine.addCol
--       |> StackMachine.addCol
--       |> StackMachine.place 0 'Z'
--       |> StackMachine.place 0 'N'
--       |> StackMachine.place 1 'M'
--       |> StackMachine.place 1 'C'
--       |> StackMachine.place 1 'D'
--       |> StackMachine.place 2 'E'
--       |> StackMachine.move 1 1 0
--       |> StackMachine.move 3 0 2

def data : String := "data/dec5.txt"

-- def List.foldl_dep {β} {α : (x : β) -> γ} (f : α → β → α) : (init : α) → List β → α
--   | a, List.nil      => a
--   | a, List.cons b l => foldl_dep f (f a b) l

def parseStartingMachine (l : List String) : Option ((n : Nat) × StackMachine n) := do
  -- clean up the input
  let clean := l |> List.reverse
                 |> List.map String.data
                 |> List.map (Utils.windows 4)
                 |> List.map (List.filterMap (List.get? · 1))

  let hd <- clean.head?
  let tl <- clean.tail?
                 
  let cleanVecs : List (Vector Char hd.length) :=
    tl.filterMap (λ l =>
                    match l.length.decEq hd.length with
                    | isTrue p => some $ ⟨ l, p ⟩
                    | isFalse _ => none)
                 
  pure ⟨ hd.length, cleanVecs ⟩

#eval do (<- Utils.lines data)
      |> List.groupBy (λ (x y : String) =>
           (x.startsWith "move" && y.startsWith "move") || (!x.startsWith "move" && !y.startsWith "move"))
      |> (List.get! · 0)
      |> parseStartingMachine
      |> pure

def run : IO Unit := do

  let part1 := ()
  let part2 := ()
  
  let stdout <- IO.getStdout
  stdout.putStrLn s!"Part1: {part1}"
  stdout.putStrLn s!"Part2: {part2}"

  pure ()

end Dec5
