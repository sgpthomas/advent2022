namespace Dec2

universe u

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
  
def prodMap {α β : Type} (e : (α × α)) (f : (α → β)) : (β × β) :=
  let (x, y) := e
  (f x, f y)
  
structure UniProd (α : Type u) where
  fst : α
  snd : α
  
instance (α : Type) : Coe (α × α) (UniProd α) where
  coe x := UniProd.mk x.1 x.2
  
instance [ToString α] : ToString (UniProd α) where
  toString x := s!"({x.fst}, {x.snd})"
  
-- the type of uniform products
instance : Functor UniProd where
  map f e := (f e.fst, f e.snd)
  
def liftOption {α : Type} (x y : Option α) : Option (α × α) :=
  match x, y with
  | some x, some y => (x, y)
  | _, _ => none

inductive Outcome where
| win : Outcome
| lose : Outcome
| tie : Outcome
deriving Repr, BEq

instance : ToString Outcome where
  toString x := match x with
                | Outcome.win => "win"
                | Outcome.lose => "lose"
                | Outcome.tie => "tie"
                
def outcomeVal (o : Outcome) : Nat :=
  match o with
  | Outcome.win => 6
  | Outcome.lose => 0
  | Outcome.tie => 3
  
def choiceVal (m : Move) : Nat :=
  match m with
  | Move.rock => 1
  | Move.paper => 2
  | Move.scissors => 3

def score (me : Move) (opp : Move) : Outcome :=
  if me == opp then
    Outcome.tie
  else match me, opp with
    | Move.rock, Move.scissors => Outcome.win
    | Move.paper, Move.rock => Outcome.win
    | Move.scissors, Move.paper => Outcome.win
    | _, _ => Outcome.lose

def chooseOption (m : Move) (outcome : Outcome) : Move :=
  match outcome, m with
  | Outcome.win, Move.rock => Move.paper
  | Outcome.win, Move.paper => Move.scissors
  | Outcome.win, Move.scissors => Move.rock
  | Outcome.lose, Move.rock => Move.scissors
  | Outcome.lose, Move.paper => Move.rock
  | Outcome.lose, Move.scissors => Move.paper
  | Outcome.tie, move => move
  
def moveToOutcome (m : Move) : Outcome :=
  match m with
  | Move.rock => Outcome.lose
  | Move.paper => Outcome.tie
  | Move.scissors => Outcome.win
  
theorem chooseOptionCorrect (m : Move) (o : Outcome) : score (chooseOption m o) m = o :=
  by
    match m with
    | Move.rock => match o with
                   | Outcome.win => rfl
                   | Outcome.lose => rfl
                   | Outcome.tie => rfl
    | Move.paper => match o with
                   | Outcome.win => rfl
                   | Outcome.lose => rfl
                   | Outcome.tie => rfl
    | Move.scissors => match o with
                       | Outcome.win => rfl
                       | Outcome.lose => rfl
                       | Outcome.tie => rfl

def run : IO Unit := do
  
  let lines <- parse
  
  let parsed : List (Move × Move) :=
    lines |> List.map (String.split · (· = ' '))
          |> List.map (λ x => (x[0]!, x[1]!))
          |> List.map (λ x => fromStr <$> (x : UniProd String))
          |> List.filterMap (λ x => liftOption x.fst x.snd)

  let part1 := 
    parsed |> List.map (λ x => outcomeVal (score x.2 x.1) + choiceVal x.2)
           |> List.foldl (· + ·) 0
           
  let part2 :=
    parsed |> List.map (λ (e, h) => (e, moveToOutcome h))
           |> List.map (λ (e, o) => (e, chooseOption e o))
           |> List.map (λ (e, h) => outcomeVal (score h e) + choiceVal h)
           |> List.foldl (· + ·) 0
  

  let stdout <- IO.getStdout
  stdout.putStrLn s!"Part 1: {part1}"
  stdout.putStrLn s!"Part 2: {part2}"



end Dec2
