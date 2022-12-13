namespace Utils

def curry {α β γ : Type u} (f : α × β -> γ) : α -> β -> γ :=
  λ x y => f (x, y)
  
def uncurry {α β γ : Type u} (f : α -> β -> γ) : α × β -> γ :=
  λ (x, y) => f x y
  
/-- `lines path` returns a list of lines from the file `path`. -/
def lines (path : String) : IO (List String) := do
  let text <- IO.FS.readFile path
  let lines := String.split text (· = '\n')
  pure $ lines.filter (· ≠ "")

end Utils
