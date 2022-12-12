namespace Utils

class Plus (α : Type) where
  plus : α -> α -> α
  

instance : Plus Nat where
  plus := Nat.add

def curry {α β γ : Type u} (f : α × β -> γ) : α -> β -> γ :=
  λ x y => f (x, y)
  
def uncurry {α β γ : Type u} (f : α -> β -> γ) : α × β -> γ :=
  λ (x, y) => f x y

end Utils
