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

def windows (n : Nat) (l : List α) : List (List α) :=
  l |> List.enum
    |> List.map (λ (i, x) => (i / n, x)) 
    |> List.groupBy (λ (i, _) (j, _) => i = j)
    |> List.map (List.map Prod.snd)
    
def enum {α} (l : List α) : List (Fin l.length × α) :=
  match l with
  | [] => []
  | h :: tl => (Fin.mk tl.length (by simp_arith), h) :: (enum tl).map (λ (f, a) => (Fin.succ f, a))

-- match enum tl with
-- | [] => [(Fin.mk 0 _, h)]
-- | (f, e) :: rst => (Fin.mk (f + 1) _, h) :: (Fin.mk f _, e) :: rst
                

end Utils
