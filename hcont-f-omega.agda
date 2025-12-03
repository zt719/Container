{- HCont -}

data Kind : Set where
  * : Kind
  _⇒_ : Kind → Kind → Kind

data ConK : Set where
  • : ConK
  _▷_ : ConK → Kind → ConK

variable κ κ' : Kind
variable Θ Θ' : ConK

data Ty : ConK → Kind → Set₁ where
  zero : Ty (Θ ▷ κ) κ
  suc : Ty Θ κ → Ty (Θ ▷ κ') κ
  lam : Ty (Θ ▷ κ) κ' → Ty Θ (κ ⇒ κ')
  app : Ty Θ (κ ⇒ κ') → Ty Θ κ → Ty Θ κ'
  Π : (I : Set) → (I → Ty Θ *) → Ty Θ *
  Σ : (I : Set) → (I → Ty Θ *) → Ty Θ *

  -- sucT : Ty Θ * → (κ : Kind) → Ty (Θ ▷ κ) *
  -- _[_]T : Ty (Θ ▷ κ) * → Ty Θ κ → Ty Θ *

data ConT (Θ : ConK) : Set₁ where
  • : ConT Θ
  _▷_ : ConT Θ → Ty Θ * → ConT Θ

variable Γ Δ : ConT Θ
variable σ τ : Ty Θ *

-- sucT* : ConT Θ → (κ : Kind) → ConT (Θ ▷ κ)
-- sucT* • κ = •
-- sucT* (Γ ▷ σ) κ = sucT* Γ κ ▷ sucT σ κ

variable I : Set

data Tm : (Θ : ConK) → ConT Θ → Ty Θ * → Set₁ where
  zero : Tm Θ (Δ ▷ σ) σ
  suc : Tm Θ Δ σ → Tm Θ (Δ ▷ τ) σ
  inj : (F : I → Ty Θ *)(i : I) → Tm Θ Δ (F i) → Tm Θ Δ (Σ I F)
  case : (F : I → Ty Θ *) → ((i : I) → Tm Θ (Δ ▷ F i) τ) → Tm Θ (Δ ▷ Σ I F) τ 
  prj : (F : I → Ty Θ *) → Tm Θ Δ (Π I F) → (i : I) → Tm Θ Δ (F i)
  pair : (F : I → Ty Θ *) → ((i : I) → Tm Θ Δ (F i)) → Tm Θ Δ (Π I F)
