import Utils

namespace Dec5

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
    

-- TODO! fix this definition. how the heck does type equality work?
def Vector.enum {α} {n} (l : Vector α n) : Vector (Fin n × α) n :=
  -- this is a proof that List (Fin l.length × α) = List (Fin n × a)
  let l' : List (Fin n × α) := (Eq.symm l.property) ▸ Utils.enum l.val
  let p : List.length l' = n := by
    have leq : l.val.length = l'.length := sorry
    rw [<- leq]
    exact l.property

  ⟨ l', p ⟩
  
#eval Vector.enum (Vector.fromList ['a', 'b', 'c'])

notation a ":::" b => Vector.cons a b

structure StackMachine (n : Nat) where
  stacks : Vector (List Char) n
deriving Repr
  
def StackMachine.empty : StackMachine 0 :=
  StackMachine.mk Vector.nil
  
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
                    
  let sm : StackMachine hd.length :=
    StackMachine.mk (Vector.mkSize [] hd.length)
    
  let sm' : StackMachine hd.length :=
    cleanVecs.foldl
      (λ acc v =>
        let v' := v.enum
        v'.val.foldl (λ acc (p, c) => acc.place p c) acc)
      sm
                 
  pure ⟨ hd.length, sm' ⟩

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
