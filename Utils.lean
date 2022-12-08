
class Plus (α : Type) where
  plus : α -> α -> α
  

instance : Plus Nat where
  plus := Nat.add
