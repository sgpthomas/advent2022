import Utils
import Vector

namespace Dec5

open Vector

structure StackMachine (n : Nat) where
  stacks : Vector (List Char) n
deriving Repr
  
def StackMachine.empty : StackMachine 0 :=
  StackMachine.mk Vector.nil
  
def StackMachine.addCol {n : Nat} (sm : StackMachine n) : StackMachine (n + 1) :=
  StackMachine.mk $ sm.stacks.cons []
  
def StackMachine.endIdx {n : Nat} (sm : StackMachine n) (H : n > 0) : Fin n :=
  let len := sm.stacks.length - 1
  Fin.mk len (by simp_arith [Vector.length, Nat.sub]
                 cases n with
                 | zero => contradiction
                 | succ n' => simp)
                 
def StackMachine.takeN {n : Nat} (frm : Fin n) (c : Nat) (sm : StackMachine n) : (List Char × StackMachine n) :=
  let stack := (sm.stacks.nth frm).enum
  let ltPred : (Nat × Char) -> Bool := λ x => x.fst < c
  let elems := stack.takeWhile ltPred |> List.map Prod.snd
  let drop := stack.dropWhile ltPred |> List.map Prod.snd
  (elems, StackMachine.mk $ sm.stacks.set frm drop)
  
def StackMachine.take {n : Nat} (frm : Fin n) (sm : StackMachine n) : Option (Char × StackMachine n) :=
  match sm.takeN frm 1 with
  | ([c], sm') => some (c, sm')
  | _ => none
  
def StackMachine.placeN {n : Nat} (to : Fin n) (cs : List Char) (sm : StackMachine n) : StackMachine n :=
  let stack := sm.stacks.nth to
  StackMachine.mk $ sm.stacks.set to (cs ++ stack)
  
def StackMachine.place {n : Nat} (to : Fin n) (c : Char) (sm : StackMachine n) : StackMachine n :=
  sm.placeN to [c]
  
-- Move `num` boxes from stack `frm` to stack `to`
def StackMachine.move {n : Nat} (num : Nat) (frm : Fin n) (to : Fin n) (sm : StackMachine n)
    : StackMachine n :=
  match num with
  | 0 => sm
  | n + 1 => 
    let sm' := match sm.take frm with
               | some (c, sm') => sm'.place to c
               | none => sm
    sm'.move n frm to
    
def StackMachine.move9001 {n : Nat} (num : Nat) (frm : Fin n) (to : Fin n) (sm : StackMachine n)
    : StackMachine n :=
  let (chars, sm') := sm.takeN frm num
  sm'.placeN to chars
    
def StackMachine.top {n : Nat} (sm : StackMachine n) : List Char :=
  match Nat.decLt 0 n with
  | isTrue p => h sm (sm.endIdx p)
  | isFalse _ => []
where h {n : Nat} (sm : StackMachine n) (acc : Fin n) : List Char :=
  match acc with
  | ⟨0, _⟩ =>
    match sm.take acc with
    | some (el, _) => [el]
    | none => []
  | ⟨i+1, lt⟩ =>
    let f := ⟨i, Nat.lt_of_succ_lt lt⟩
    match sm.take acc with
    | some (el, _) => el :: h sm f
    | none => h sm f
    
def data : String := "data/dec5.txt"

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
        v'.val.foldl (λ acc (p, c) => if c ≠ ' ' then acc.place p c else acc) acc)
      sm
                 
  pure ⟨ hd.length, sm' ⟩
  
def parseMoves (n : Nat) (input : String) : Option (Nat × Fin n × Fin n) := do
  let s := input.split (· = ' ')
  let countStr <- s.get? 1
  let frmStr <- s.get? 3
  let toStr <- s.get? 5
  
  let count <- String.toNat? countStr
  let frm <- String.toNat? frmStr
  let frm' := frm - 1
  let to <- String.toNat? toStr
  let to' := to - 1
  
  match frm'.decLt n, to'.decLt n with
  | isTrue fp, isTrue tp => return (count, Fin.mk frm' fp, Fin.mk to' tp)
  | _, _ => none

def run : IO Unit := do
  let lines <- Utils.lines data
  let split := lines.groupBy (λ (x y : String) =>
           (x.startsWith "move" && y.startsWith "move")
            || (!x.startsWith "move" && !y.startsWith "move"))
            
  let initMachineInput := split.get! 0
  let movesInput := split.get! 1

  let part1 := do
    let ⟨n, start⟩ <- parseStartingMachine initMachineInput
    let moves := movesInput.reverse.filterMap (parseMoves n)
    
    let sm' : StackMachine n := moves.foldl
           (λ acc (c, f, t) => acc.move c f t)
           start
    return sm'.top.reverse.asString

  let part2 := do
    let ⟨n, start⟩ <- parseStartingMachine initMachineInput
    let moves := movesInput.reverse.filterMap (parseMoves n)

    let sm' : StackMachine n := moves.foldl
           (λ acc (c, f, t) => acc.move9001 c f t)
           start
    return sm'.top.reverse.asString
  
  let stdout <- IO.getStdout
  stdout.putStrLn s!"Part1: {part1}"
  stdout.putStrLn s!"Part2: {part2}"
  
#eval run

end Dec5
