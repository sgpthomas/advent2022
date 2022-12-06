import Dec1
import Dec2

def main : IO Unit := do
  let stdout <- IO.getStdout
  stdout.putStrLn "=== Dec1 ==="
  Dec1.run

  stdout.putStrLn "=== Dec2 ==="
  Dec2.run
  
  -- let sorted_groups := List.

