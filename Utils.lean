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

def finCastUp {n : Nat} (f : Fin n) (m : Nat) (lt : n <= m) : Fin m :=
  Fin.mk 
    (f.val)
    (by simp_arith exact Nat.le_trans f.isLt lt)

def enumFinAx {α : Type u} (l : List α) : List (Fin l.length × α) :=
  match l with
  | [] => []
  | hd :: tl => let tl' := enumFinAx tl
                let n := (hd :: tl).length
                let f : Fin n := Fin.ofNat tl'.length
                let fix : List (Fin n × α) :=
                  (List.map
                    (λ (x : Fin tl.length × α) =>
                      let p : tl.length <= n := by simp_arith
                      (finCastUp x.fst n p, x.snd))
                    tl')
                (f, hd) :: fix
                
def enumFin {α : Type u} (l : List α) : List (Fin l.length × α) :=
  -- l |> List.reverse |> enumFinAx |> List.reverse
  let l' := l.reverse |> enumFinAx
    
  -- cast the list to the right type
  let l'' : List (Fin l.length × α) := by
    have eq : l.length = l.reverse.length := by induction l <;> simp
    rw [eq]
    exact l'
      
  -- reverse the list again to get the right order
  l'' |> List.reverse
  
def List.mkLength {α} (default : α) (n : Nat) : List α :=
  match n with
  | 0 => []
  | n+1 => default :: (mkLength default n)
  
theorem List.mkLengthCorrect {α} {default : α} {n : Nat}
        : (List.mkLength default n).length = n := by
  induction n with
  | zero => simp [mkLength]
  | succ n IH => simp [mkLength] exact IH
  
-- example (α : Type u) (hd : α) (tl : List α)
--   : enumFin (hd :: tl) = (0, hd) :: enumFin tl := by simp
  
-- theorem enumFin_keeps_elems {α : Type u} (l : List α)
--         : List.map Prod.snd (enumFin l) = l := by
--   induction l with
--   | nil => simp [List.map]
--   | cons hd tl IH =>
--          simp [enumFin]
--          match (Eq.symm IH) with
--          | Eq.refl tl =>
--            rw [<- IH]
--            simp [List.reverse, enumFin, enumFinAx, List.reverseAux, List.map, *]
           

-- theorem enumFin_succ {α : Type u} (hd : α) (tl : List α)
--         : (enumFin (hd :: tl)).length = 1 + (enumFin tl).length := by
--   simp [enumFin]
--   rw [List.reverse_cons]
  
theorem enumFin_preserves_length {α : Type u} (l : List α) : l.length = (enumFin l).length := by
  induction l with
  | nil => simp [enumFin, List.length]
  | cons hd tl H =>
    simp
    sorry
    
end Utils
