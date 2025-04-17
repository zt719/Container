open import Data.Product
open import Data.Unit
open import Data.Empty

record Cont₂ : Set₁ where
  constructor _◁_,_,_
  inductive
  pattern
  field
    S : Set
    P₀ : S → Set
    R₀ : (s : S) → P₀ s → Cont₂    
    P₁ : S → Set

⟦_⟧ : Cont₂ → (Set → Set) → Set → Set
⟦ S ◁ P₀ , R₀ , P₁ ⟧ F X =
  Σ[ s ∈ S ] ((p : P₀ s) → F (⟦ R₀ s p ⟧ F X))
             × (P₁ s → X)
             
H : Cont₂
H = ⊤ ◁ (λ _ → ⊤) ,
        (λ _ _ → ⊤ ◁ (λ _ → ⊤) ,
          (λ _ _ → ⊤ ◁ (λ _ → ⊥) , (λ _ ()) , λ _ → ⊤) ,
          λ _ → ⊤) ,
        λ _ → ⊤ 
