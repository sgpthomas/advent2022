
namespace Dec1
def insert_nat (i : Nat) (l : List Nat) :=
  match l with
  | [] => [i]
  | h :: t => if i <= h then i :: h :: t else h :: (insert_nat i t)
  
def sort_nat (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | h :: t => insert_nat h (sort_nat t)

def parse : IO (List String) := do
  let text <- IO.FS.readFile "data/dec1.txt"
  let lines := String.split text (· = '\n')
  pure lines

def run : IO Unit := do
  let stdout <- IO.getStdout
  
  let lines <- parse
  
  let groups : List (List String) :=
    Prod.snd (List.foldl
      (fun (curr, all) el => if el == "" then ([], curr :: all) else (el :: curr, all)) 
      ([], [])
      lines)
     
  let parsed_groups : List (List Nat) :=
    List.map (List.map String.toNat! ·) groups
    
  let group_sums : List Nat :=
    List.map (List.foldl (· + ·) 0 ·) parsed_groups
    
  let group_max := List.maximum? group_sums
  
  let sorted_groups := List.reverse (sort_nat group_sums)
  
  let answer := match sorted_groups with
  | a :: b :: c :: _  => a + b + c
  | _ => 0
  
  stdout.putStrLn s!"Part 1: {group_max}"
  stdout.putStrLn s!"Part 2: {answer}"

end Dec1
