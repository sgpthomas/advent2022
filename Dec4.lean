import Utils

namespace Dec4

structure InclusiveRange where
  lower : Nat
  upper : Nat
  isValid : lower <= upper
  
instance : ToString InclusiveRange where
  toString ir := s!"({ir.lower}..={ir.upper})"
  
notation:40 e₁ "##" e₂ => InclusiveRange.mk e₁ e₂ (by decide : e₁ <= e₂)
notation:40 e₁ "#(" p ")#" e₂ => InclusiveRange.mk e₁ e₂ (p : e₁ <= e₂)

#eval 4 #((by decide : _))# 5

def InclusiveRange.fromString (input : String) : Option InclusiveRange := do
  let parts := input.split (· = '-')
  match parts with
  | [lowStr, upStr] => let low <- lowStr.toNat?
                       let up  <- upStr.toNat?
                       match low.decLe up with
                       | isTrue p => (low #(p)# up)
                       | isFalse _ => none
  | _ => none
  
def InclusiveRange.contains (ir₁ ir₂ : InclusiveRange) : Bool :=
  (ir₂.lower <= ir₁.lower) ∧ (ir₁.upper <= ir₂.upper)
  
-- This doesn't seem to be working in that way that I would expect
-- Not sure why, but using <= just doesn't work
instance : LE InclusiveRange where
  le ir₁ ir₂ := InclusiveRange.contains ir₁ ir₂ = true
  
-- instance : DecidableRel InclusiveRange.contains :=
--   fun ir₁ ir₂ => match ir₂.lower.decLe ir₁.lower, ir₁.upper.decLe ir₂.upper with
--     | isTrue p₁, isTrue p₂ => isTrue (And.intro p₁ p₂)
--     | isFalse np₁, isTrue _ => isFalse (by simp [InclusiveRange.contains] at *
--                                            intro H
--                                            have t := And.left H
--                                            contradiction)
--     | isTrue _, isFalse np₂ => isFalse (by simp [InclusiveRange.contains] at *
--                                            intro H
--                                            have t := And.right H
--                                            contradiction)
--     | isFalse np₁, isFalse _ => isFalse (by simp [InclusiveRange.contains] at *
--                                             intro H
--                                             have t := And.left H
--                                             contradiction)
                                            
def InclusiveRange.overlaps (ir₁ ir₂ : InclusiveRange) : Bool :=
  ¬(ir₂.upper < ir₁.lower ∨ ir₁.upper < ir₂.lower)
  
def data : String := "data/dec4.txt"

#eval do (<- Utils.lines data)
         |> List.map (λ (x : String) => x.split (· = ','))
         |> List.map (List.filterMap InclusiveRange.fromString)
         -- |> (List.get! · 0)
         |> List.filterMap (λ l => match l with
            | [r₁, r₂] => some $ (InclusiveRange.contains r₁ r₂) || (InclusiveRange.contains r₂ r₁)
            | _ => none)
         |> List.map (λ (x : Bool) => if x then 1 else 0)
         |> List.foldl (· + ·) 0
         |> pure

def run : IO Unit := do

  let lines <- Utils.lines data
  let common := List.map (String.split · (· = ',')) lines
                |> List.map (List.filterMap InclusiveRange.fromString)
  
  let part1 := common
    |> List.filterMap (λ l => match l with
      | [r₁, r₂] => some $ (InclusiveRange.contains r₁ r₂) || (InclusiveRange.contains r₂ r₁)
      | _ => none)
    |> List.map (λ (x : Bool) => if x then 1 else 0)
    |> List.foldl (· + ·) 0

  let part2 := common
    |> List.filterMap (λ l => match l with
      | [r₁, r₂] => some $ InclusiveRange.overlaps r₁ r₂
      | _ => none)
    |> List.map (λ (x : Bool) => if x then 1 else 0)
    |> List.foldl (· + ·) 0

  let stdout <- IO.getStdout
  stdout.putStrLn s!"Part1: {part1}"
  stdout.putStrLn s!"Part2: {part2}"
  
#eval run

end Dec4
