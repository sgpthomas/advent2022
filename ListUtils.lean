-- This file will contain some List utils


-- inductive pairwise : List α → Prop
-- | nil : pairwise []
-- | cons : ∀ {a : α} {l : List α},
--   (∀ (a' : α),  a' ∈ l → R a a')
--   → pairwise R l → pairwise R (a :: l)
