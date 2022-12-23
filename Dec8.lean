import Utils

namespace Dec8

def visible (l : List (Nat × Bool)) : List (Nat × Bool) :=
  let f := 
    Prod.snd ∘
    List.foldl
      (λ (max, vals) (el, vis) =>
        match max with
        | none => (some el, (el, true) :: vals)
        | some m =>
          if el <= m then
            (some m, (el, vis) :: vals)
          else
            (some el, (el, true) :: vals))
      (none, [])

  l |> f |> f
  
def countBack (needle : Nat) (l : List Nat) :=
  let (_, cnt) := l.foldl
    (λ (done, cnt) el =>
      if done then
        (done, cnt)
      else if el >= needle then
        (true, cnt + 1)
      else
        (false, cnt + 1))
    (false, 0)
  cnt
  
def countVisible (l : List (Nat × Nat)) : List (Nat × Nat) :=
  let f := Prod.snd ∘ List.foldl
    (λ (seen, res) (el, score) =>
      (el :: seen, (el, ((countBack el seen) * score)) :: res))
    ([], [])
  l |> f |> f

def data : String := "data/dec8.txt"

def run := do

  let lines <- Utils.lines data
  let grid := lines.map String.data
    |> List.map (List.map (λ x => s!"{x}".toNat!))
    
  let vis := grid
    |> List.map (List.map (λ x => (x, false)))
    |> List.map visible |> Utils.transpose
    |> List.map visible |> Utils.transpose

  let count := vis
    |> List.join
    |> List.map Prod.snd
    |> List.map (λ x : Bool => if x then 1 else 0)
    |> List.foldl Nat.add 0

  let part1 := count
  
  let visCount := grid
    |> List.map (List.map (·, 1))
    |> List.map countVisible
    |> Utils.transpose
    |> List.map countVisible
    |> Utils.transpose

  let _dbg := visCount
    |> List.map (List.map Prod.snd)
    |> List.map (List.map (λ x => s!"{x} "))
    |> List.map String.join
    |> String.intercalate "\n"
    -- |> List.foldl Nat.add 0
    
  let _dbgGrid := grid
    |> List.map (List.map (λ x => s!"{x} "))
    |> List.map String.join
    |> String.intercalate "\n"
  
  let part2 := visCount
    |> List.map (List.map Prod.snd)
    |> List.join
    |> List.maximum?
  
  let stdout <- IO.getStdout
  stdout.putStrLn s!"Part1: {part1}"
  stdout.putStrLn s!"Part2: {part2}"
  -- stdout.putStrLn s!"-----"
  -- stdout.putStrLn s!"{dbg}"
  -- stdout.putStrLn s!"-----"
  -- stdout.putStrLn s!"{dbgGrid}"

  pure ()
  
#eval run

end Dec8
