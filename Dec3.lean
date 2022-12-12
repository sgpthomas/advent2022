import Utils

namespace Dec3

universe u

def Common {α : Type u} (e : α) (a : List α) (b : List α) := e ∈ a ∧ e ∈ b

example : Common 1 [2, 1] [1, 3] :=
  by
    simp [Common]
    
-- inductive Unique (α : Type u) where
    
-- A rucksack has a designated element `e`. To add something to the rucksack
-- you have to show that this element is not equal to the designated element
inductive Rucksack {α : Type u} : (e : α) -> Type u where
| nil : Rucksack e
| cons : (x : α × α) -> (x.fst ≠ e ∧ x.snd ≠ e) -> Rucksack e -> Rucksack e

def Rucksack.toList {α : Type u} {e : α} (rs : Rucksack e) : List α × List α := 
  match rs with
  | Rucksack.nil => ([e], [e])
  | Rucksack.cons (x, y) _ rs' => let (l, r) := rs'.toList
                                  (x :: l, y :: r)

/-- if α is decidable, then we can automatically syntehsize the proof
we need to construct the element of the rucksack -/
def Rucksack.consDec [DecidableEq α] {e : α}
    (rs : Rucksack e) (new : α × α) : Option (Rucksack e)
  :=
    match (decEq new.fst e), (decEq new.snd e) with
    | isFalse hl, isFalse hr => Rucksack.cons new (And.intro hl hr) rs
    | _, _ => none

inductive EvenList (α : Type u) where
| even_nil : EvenList α
| even_cons (x y : α) (tl : EvenList α) : EvenList α
deriving Repr

def EvenList.length {α : Type u} (l : EvenList α) : Nat :=
  match l with
  | EvenList.even_nil => 0
  | EvenList.even_cons _ _ tl => 2 + tl.length
  
def EvenList.toList {α : Type u} (l : EvenList α) : List α :=
  match l with
  | EvenList.even_nil => []
  | EvenList.even_cons x y tl => x :: y :: tl.toList
    
def EvenList.split {α : Type u} (l : EvenList α) : List α × List α :=
  h (l.length / 2) l
where h len l :=
  match l with
  | EvenList.even_nil => ([], [])
  | EvenList.even_cons x y tl =>
    let (ll, lr) := h len tl
    if lr.length >= len then
      (x :: y :: ll, lr)
    else if lr.length + 1 == len then
      (x :: ll, y :: lr)
    else
      (ll, x :: y :: lr)
  
def EvenList.mk {α : Type u} (l : List α) : Option (EvenList α) :=
  match l with
  | x :: y :: tl => EvenList.even_cons x y <$> (EvenList.mk tl)
  | [] => some EvenList.even_nil 
  | _ => none

def findCommon [BEq α] (l₁ : List α) (l₂ : List α) : Option α :=
  match l₁ with
  | [] => none
  | x :: tl => match l₂.find? (· == x) with
               | some e => e
               | none => findCommon tl l₂

def test : List String := [
    "vJrwpWtwJgWrhcsFMMfFFhFp",
    "jqHRNqRjqzjGDLGLrsFMfFZSrLrFZsSL",
    "PmmdzqPrVvPwwTWBwg",
    "wMqvLMZHhHMvwLHjbvcjnnSBnvTQFn",
    "ttgJtRGJQctTZtZT",
    "CrZsJsPPZsGzwwsLwLmpwMDw"
  ]

def Rucksack.mk [BEq α] [DecidableEq α] (l₁ l₂ : List α) (e : α) : Option (Rucksack e) := do
  match l₁, l₂ with
  | [], [] => some Rucksack.nil
  | x :: l₁' , y :: l₂' =>
    let rs <- Rucksack.mk l₁' l₂' e
    match rs.consDec (x, y) with
    | some x => x
    | none => rs
  | _, _ => none
  
def Rucksack.fromStr (input : String) : Option ((e : Char) × Rucksack e) := do
  let el <- EvenList.mk input.data
  let (l₁, l₂) := el.split
  let dist <- findCommon l₁ l₂
  let rs <- Rucksack.mk l₁ l₂ dist
  pure ⟨dist, rs⟩
  
def Char.priority (e : Char) : Nat :=
  if e.isLower then
    e.toNat - 96
  else
    e.toNat - 38
  
def Rucksack.priority {e : Char} (_ : Rucksack e) : Nat := Char.priority e

def findBadgeHelp [BEq α] (l₁ l₂ l₃ : List α) : Option α :=
  match l₁ with
  | [] => none
  | x :: tl => match l₂.find? (· == x), l₃.find? (· == x) with
               | some _, some _ => some x
               | _, _ => findBadgeHelp tl l₂ l₃
    
def Rucksack.findBadge [BEq α] {e₁ e₂ e₃ : α}
    (rs₁ : Rucksack e₁)
    (rs₂ : Rucksack e₂)
    (rs₃ : Rucksack e₃)
    : Option α :=
  let (ll₁, lr₁) := rs₁.toList
  let (ll₂, lr₂) := rs₂.toList
  let (ll₃, lr₃) := rs₃.toList
  findBadgeHelp (ll₁ ++ lr₁) (ll₂ ++ lr₂) (ll₃ ++ lr₃)
               
def Rucksack.findBadgeList [BEq α] : List ((e : α) × Rucksack e) -> Option α
  | [rs₁, rs₂, rs₃] => Rucksack.findBadge rs₁.snd rs₂.snd rs₃.snd
  | _ => none

def parse : IO (List String) := do
  let text <- IO.FS.readFile "data/dec3.txt"
  let lines := String.split text (· = '\n')
  let lines' := List.filter (· ≠ "") lines
  pure lines'
  
def List.windows (n : Nat) (l : List α) : List (List α) :=
  l |> List.enum
    |> List.map (λ (i, x) => (i / n, x)) 
    |> List.groupBy (λ (i, _) (j, _) => i = j)
    |> List.map (List.map Prod.snd)

def run : IO Unit := do

  let lines <- parse
  let sacks := lines.filterMap Rucksack.fromStr

  let part1 := sacks |> List.map (λ x => Rucksack.priority (Sigma.snd x))
                     |> List.foldl (· + ·) 0

  let part2 := lines |> List.map String.data
               |> List.windows 3
               |> List.filterMap (λ x => match x with
                                         | [l1, l2, l3] => findBadgeHelp l1 l2 l3
                                         | _ => none)
               |> List.map Char.priority
               |> List.foldl (· + ·) 0
  
  let stdout <- IO.getStdout
  stdout.putStrLn s!"Part 1: {part1}"
  stdout.putStrLn s!"Part 2: {part2}"
  
#eval run

end Dec3
