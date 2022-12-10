namespace Dec3

universe u

def Common {α : Type u} (e : α) (a : List α) (b : List α) := e ∈ a ∧ e ∈ b

theorem ex : Common 1 [2, 1] [1, 3] :=
  by
    simp [Common]
    
-- inductive Unique (α : Type u) where
    
inductive Rucksack (α : Type u) where
| nil : (e : α) -> Rucksack α
| cons : (p : α × α) -> Rucksack α -> Rucksack α
deriving Repr

instance (α : Type u) : HAppend (α × α) (Rucksack α) (Rucksack α) where
  hAppend := Rucksack.cons
  
def fromList {α : Type u} (rs : List (α × α)) (e : α) : Rucksack α :=
  List.foldr (λ e a => Rucksack.cons e a) (Rucksack.nil e) rs
  
#eval fromList [(1, 2), (1, 2), (5, 4)] 4

-- I want the members of Rucksack 4 to be a pair of lists that both contain the element 4


def parse : IO (List String) := do
  let text <- IO.FS.readFile "data/dec3.txt"
  pure []
  
def validate (input : List String) := false

def run : IO Unit := do
  let part1 := "todo"
  let part2 := "todo"
  
  let stdout <- IO.getStdout
  stdout.putStrLn s!"Part 1: {part1}"
  stdout.putStrLn s!"Part 2: {part2}"

end Dec3
