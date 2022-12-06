namespace Dec2

def parse : IO (List String) := do
  let text <- IO.FS.readFile "data/dec2.txt"
  let lines := String.split text (· = '\n')
  pure lines
  
inductive Move where
| Rock : Move
| Paper : Move
| Scissors : Move
deriving BEq

inductive Outcome where
| Win : Outcome
| Lose : Outcome
| Tie : Outcome

def score (me : Move) (opp : Move) : Outcome :=
  if me == opp then
    Outcome.Tie
  else match me, opp with
    | Move.Rock, Move.Scissors => Outcome.Win
    | Move.Paper, Move.Rock => Outcome.Win
    | Move.Scissors, Move.Paper => Outcome.Win
    | _, _ => Outcome.Lose

def run : IO Unit := do
  
  let lines <- parse
  
  

  let stdout <- IO.getStdout
  stdout.putStrLn "Part 1: xxx"
  stdout.putStrLn "Part 2: xxx"


end Dec2
