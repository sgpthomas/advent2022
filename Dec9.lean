import Utils

namespace Dec9

def data : String := "data/dec9.txt"

def run : IO Unit := do

  let part1 := ()
  let part2 := ()
  
  let stdout <- IO.getStdout
  stdout.putStrLn s!"Part1: {part1}"
  stdout.putStrLn s!"Part2: {part2}"

  pure ()

end Dec9
