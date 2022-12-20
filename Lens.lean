import Utils


namespace Lens

universe u

structure Lens (σ α : Type u) where
  view : σ -> α
  over : (α -> α) -> σ -> σ
  
def set (l : Lens σ α) (a : α) : σ -> σ :=
  l.over (λ _ => a)
  
def compose (l₁ : Lens σ β) (l₂ : Lens β α) : Lens σ α :=
  { view := l₂.view ∘ l₁.view, over := l₁.over ∘ l₂.over }
  
instance : HMul (Lens σ β) (Lens β α) (Lens σ α) where
  hMul := Lens.compose

end Lens
