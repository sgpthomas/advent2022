import Utils

namespace Dec5

structure StackMachine (α : Type u) where
  stacks : List (List α)

def data : String := "data/dec5.txt"

def run : IO Unit := do

  let part1 := ()
  let part2 := ()
  
  let stdout <- IO.getStdout
  stdout.putStrLn s!"Part1: {part1}"
  stdout.putStrLn s!"Part2: {part2}"

  pure ()

end Dec5
