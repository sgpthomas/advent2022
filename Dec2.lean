namespace Dec2

def parse : IO (List String) := do
  let text <- IO.FS.readFile "data/dec2.txt"
  let lines := String.split text (· = '\n')
  pure lines
  
inductive Move where
| rock : Move
| paper : Move
| scissors : Move
deriving BEq, Repr

def fromStr (input : String) : Option Move :=
  match input with
  | "A" | "X" => Move.rock
  | "B" | "Y" => Move.paper
  | "C" | "Z" => Move.scissors
  | _ => none

inductive Outcome where
| win : Outcome
| lose : Outcome
| tie : Outcome


def score (me : Move) (opp : Move) : Outcome :=
  if me == opp then
    Outcome.tie
  else match me, opp with
    | Move.rock, Move.scissors => Outcome.win
    | Move.paper, Move.rock => Outcome.win
    | Move.scissors, Move.paper => Outcome.win
    | _, _ => Outcome.lose

def run : IO Unit := do
  
  let lines <- parse
  
  let res :=
    lines |> List.map (String.split · (· = ' '))
          |> List.map (List.map fromStr ·)
          -- |> 

  -- let split := List.map (String.split · (· = ' ')) lines
  
  -- let moves : List (Option Move × Option Move) := List.map (λ x => ((fromStr ∘ Prod.fst) x, (fromStr ∘ Prod.snd) x)) split
   -- let moves : List (Move × Move) :=

  let stdout <- IO.getStdout
  stdout.putStrLn "Part 1: xxx"
  stdout.putStrLn "Part 2: xxx"


end Dec2
