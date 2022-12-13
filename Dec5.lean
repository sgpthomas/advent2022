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
  let p : idx.val < v.val.length := by
    have x := v.property
    rw [x]
    exact idx.isLt
  v.val[idx.val]'p
def Vector.set {α : Type u} (v : Vector α n) (idx : Fin n) (el : α) : Vector α n :=
  ⟨ v.val.set idx.val el, by simp exact v.property ⟩
def Vector.fromList {α} (l : List α) : Vector α l.length := ⟨ l,  rfl ⟩

theorem take_length {α} (n : Nat) (l : List α) (H : (Nat.succ n) < l.length)
        : List.length (List.take (Nat.succ n) l) = Nat.succ (List.length (List.take n l)) :=
  sorry

def Vector.truncateList {α} (l : List α) (nf : Fin (Nat.succ l.length)) : Vector α n :=
  let ⟨ n, lt ⟩ := nf
  -- let p : List.length (List.take n l) = n := by
  --   induction l with
  --   | nil => cases n with
  --            | zero => simp [List.take]
  --            | succ n' => simp [List.take]; simp [*] at *; sorry
  --   | cons h t H => cases n with
  --            | zero => simp [List.take]
  --            | succ n' =>  simp [List.take]
    -- induction n with
    -- | zero => simp [List.take]
    -- | succ n' H => cases l with
    --                | nil => sorry
    --                | cons h t => simp [List.take]

    -- induction n.val
    -- · simp [List.take]
    -- · rw [take_length]
    --   · simp assumption
      -- · simp assumption

  ⟨ l.take n , p ⟩

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
    
#eval StackMachine.empty
      |> StackMachine.addCol
      |> StackMachine.addCol
      |> StackMachine.addCol
      |> StackMachine.place 0 'Z'
      |> StackMachine.place 0 'N'
      |> StackMachine.place 1 'M'
      |> StackMachine.place 1 'C'
      |> StackMachine.place 1 'D'
      |> StackMachine.place 2 'E'
      |> StackMachine.move 1 1 0
      |> StackMachine.move 3 0 2

def data : String := "data/dec5.txt"

-- def List.foldl_dep {β} {α : (x : β) -> γ} (f : α → β → α) : (init : α) → List β → α
--   | a, List.nil      => a
--   | a, List.cons b l => foldl_dep f (f a b) l

def parseStartingMachine (l : List String) : Option (List (List Char)) := do
  -- clean up the input
  let clean := l |> List.reverse
                 |> List.map String.data
                 |> List.map (Utils.windows 4)
                 |> List.map (List.filterMap (List.get? · 1))
                 
  pure clean
  -- let hd <- clean.head?
  -- let tl <- clean.tail?
  
  -- let uniform := tl.all (λ x => x.length = hd.length)
  -- if uniform then
  --   let init : (n : Nat) × StackMachine n := ⟨ 0, StackMachine.empty ⟩
  --   let initMach := hd.foldl (λ ⟨ n, acc ⟩ _ => ⟨ n + 1, acc.addCol ⟩) init

  --   let mach := tl.foldl
  --               (λ oacc el =>
  --                   (Utils.enum el).foldl (λ iacc (i, el) => iacc.place i el)
  --                               oacc)
  --               initMach.snd

  --   some ⟨ initMach.fst, mach ⟩
  -- else
  --   none

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
