{- Fω -}

data Kind : Set where
  * : Kind
  _⇒_ : Kind → Kind → Kind

data ConK : Set where
  • : ConK
  _▷_ : ConK → Kind → ConK

variable κ κ' : Kind
variable Θ Θ' : ConK

data Ty : ConK → Kind → Set where
  zero : Ty (Θ ▷ κ) κ
  suc : Ty Θ κ → Ty (Θ ▷ κ') κ
  lam : Ty (Θ ▷ κ) κ' → Ty Θ (κ ⇒ κ')
  app : Ty Θ (κ ⇒ κ') → Ty Θ κ → Ty Θ κ'
  _⇨_ : Ty Θ * → Ty Θ * → Ty Θ *
  all : (κ : Kind) → Ty (Θ ▷ κ) * → Ty Θ *
  sucT : Ty Θ * → (κ : Kind) → Ty (Θ ▷ κ) *
  _[_]T : Ty (Θ ▷ κ) * → Ty Θ κ → Ty Θ *

data ConT (Θ : ConK) : Set where
  • : ConT Θ
  _▷_ : ConT Θ → Ty Θ * → ConT Θ

variable Γ Δ : ConT Θ
variable σ τ : Ty Θ *

sucT* : ConT Θ → (κ : Kind) → ConT (Θ ▷ κ)
sucT* • κ = •
sucT* (Γ ▷ σ) κ = sucT* Γ κ ▷ sucT σ κ

data Tm : (Θ : ConK) → ConT Θ → Ty Θ * → Set where
  zero : Tm Θ (Δ ▷ σ) σ
  suc : Tm Θ Δ σ → Tm Θ (Δ ▷ τ) σ
  lam : Tm Θ (Δ ▷ σ) τ → Tm Θ Δ (σ ⇨ τ)
  app : Tm Θ Δ (σ ⇨ τ) → Tm Θ Δ σ → Tm Θ Δ τ
  Lam : {σ : Ty (Θ ▷ κ) *} → Tm (Θ ▷ κ) (sucT* Δ κ) σ → Tm Θ Δ (all κ σ)
  App : {σ : Ty (Θ ▷ κ) *} → Tm Θ Δ (all κ σ) → (τ : Ty Θ κ) → Tm Θ Δ (σ [ τ ]T)

-- ID : all (X : *) X : *
-- id : ID
-- Nat = all (X : *) X → (X → X) → X 
-- Bush = Lam (A : *) all (F : * ⇒ *) (all X : *) X → (X → F (F X) → F A) : * ⇒ * 


    

   
