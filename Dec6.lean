import Utils
import Vector

namespace Dec6

open Vector

def data : String := "data/dec6.txt"

def List.slide {α : Type u} (n : Nat) (l : List α) : List (Vector α n) :=
  let (_, l') := l.foldl
    (λ (cur, acc) el =>
      match Nat.decEq cur.length n with
      | isTrue p =>
        let vec := ⟨ cur.reverse, by simp exact p ⟩
        (el :: cur.dropLast, vec :: acc)
      | isFalse _ => (el :: cur, acc))
    ([], [])
  l'.reverse
  
def List.unique [BEq α] (l : List α) : Bool :=
  match l with
  | [] => true
  | hd :: tl => ¬(tl.elem hd) && unique tl

def run : IO Unit := do

  let lines : String <- IO.FS.readFile data
  let chars : List Char := lines.data

  let part1 := chars
    |> List.slide 4
    |> List.enum
    |> List.find? (List.unique ∘ Subtype.val ∘ Prod.snd)
    |> Option.map ((· + 4) ∘ Prod.fst)
  let part2 := chars
    |> List.slide 14
    |> List.enum
    |> List.find? (List.unique ∘ Subtype.val ∘ Prod.snd)
    |> Option.map ((· + 14) ∘ Prod.fst)
  
  let stdout <- IO.getStdout
  stdout.putStrLn s!"Part1: {part1}"
  stdout.putStrLn s!"Part2: {part2}"

  pure ()
  
#eval run

end Dec6
