namespace Dec3

def parse : IO (List String) := do
  let text <- IO.FS.readFile "data/dec3.txt"

def run : IO Unit := do
  let part1 := "todo"
  let part2 := "todo"
  
  let stdout <- IO.getStdout
  stdout.putStrLn s!"Part 1: {part1}"
  stdout.putStrLn s!"Part 2: {part2}"

end Dec3
