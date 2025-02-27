{-# OPTIONS --type-in-type --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

{- Syntax -}

data Ty : Set where
  set : Ty
  _⇒_ : Ty → Ty → Ty

{- Semantics -}

⟦_⟧T : Ty → Set
⟦ set ⟧T = Set
⟦ A ⇒ B ⟧T = ⟦ A ⟧T → ⟦ B ⟧T

record Cat (Obj : Set) : Set where
  field
    Hom : Obj → Obj → Set
    id : ∀ {X} → Hom X X
    _∘_ : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z
    idl : ∀ {X Y} (f : Hom X Y) → id ∘ f ≡ f
    idr : ∀ {X Y} (f : Hom X Y) → f ∘ id ≡ f
    ass : ∀ {W X Y Z} (f : Hom X W) (g : Hom Y X) (h : Hom Z Y)
          → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)
  infixr 9 _∘_

record Func {X Y : Set} (C : Cat X)(D : Cat Y)(F : X → Y) : Set where
  open Cat
  open Cat C renaming (_∘_ to _∘C_)
  open Cat D renaming (_∘_ to _∘D_)  
  field
    fmap : ∀ {X Y} → Hom C X Y → Hom D (F X) (F Y)
    fmapid : ∀ {X} → fmap {X} (id C) ≡ id D
    fmap∘ : ∀ {X Y Z} (f : Hom C Y Z) (g : Hom C X Y)
          → fmap (f ∘C g) ≡ (fmap f) ∘D (fmap g)

record Nat {X Y : Set}(C : Cat X)(D : Cat Y)(F G : X → Y)
           (FF : Func C D F)(GG : Func C D G) : Set where
  open Cat
  open Cat D renaming (_∘_ to _∘D_)
  open Func
  field
    η : ∀ X → Hom D (F X) (G X)
    nat : ∀ {X Y} (f : Hom C X Y) →
          fmap GG f ∘D η X ≡ η Y ∘D fmap FF f

postulate
  Nat≡ : {X Y : Set} {C : Cat X} {D : Cat Y} {F G : X → Y}
    → {FF : Func C D F} {GG : Func C D G}
    → {α β : Nat C D F G FF GG}
    → Nat.η α ≡ Nat.η β
    → α ≡ β

⟦_⟧F : (A : Ty) → ⟦ A ⟧T → Set
⟦_⟧C : (A : Ty) → Cat (Σ ⟦ A ⟧T ⟦ A ⟧F)

⟦ set ⟧F X = ⊤
⟦ A ⇒ B ⟧F H = Σ[ HH ∈ ((F : ⟦ A ⟧T) → ⟦ A ⟧F F → ⟦ B ⟧F (H F)) ]
               Func ⟦ A ⟧C ⟦ B ⟧C (λ (F , FF) → H F , HH F FF)

⟦ set ⟧C = record
  { Hom = λ (X , _) (Y , _) → X → Y
  ; id = λ x → x
  ; _∘_ = λ f g x → f (g x)
  ; idl = λ f → refl
  ; idr = λ f → refl
  ; ass = λ f g h → refl
  }

⟦ A ⇒ B ⟧C = record
  { Hom = λ (F , FF , FFF) (G , GG , GGG)
    → Nat ⟦ A ⟧C ⟦ B ⟧C (λ (X , XX) → F X , FF X XX) (λ (X , XX) → G X , GG X XX) FFF GGG

  ; id = record { η = λ X → id ; nat = λ f → idr _ ∙ sym (idl _) }
  ; _∘_ = λ{ record { η = η₁ ; nat = nat₁ } record { η = η₂ ; nat = nat₂ }
    → record { η = λ X → η₁ X ∘ η₂ X ; nat = λ f → sym (ass _ _ _) ∙ cong (_∘ _) (nat₁ f)
              ∙ (ass _ _ _) ∙ cong (_ ∘_) (nat₂ f) ∙ sym (ass _ _ _) } }
  ; idl = λ α → Nat≡ (λ i X → idl (α .Nat.η X) i)
  ; idr = λ α → Nat≡ (λ i X → idr (α .Nat.η X) i)
  ; ass = λ α β γ → Nat≡ (λ i X → ass (α .Nat.η X) (β .Nat.η X) (γ .Nat.η X) i)
  }
  where
    open Cat ⟦ B ⟧C

-- Examples :

N : ⟦ set ⇒ set ⟧T
N X = ⊤ ⊎ X

FuncN : ⟦ set ⇒ set ⟧F N
FuncN = _ , record
  { fmap = λ{ f (inl tt) → inl tt ; f (inr x) → inr (f x) }
  ; fmapid = λ{ i (inl tt) → inl tt ; i (inr x) → inr x }
  ; fmap∘ = λ{ f g i (inl tt) → inl tt ; f g i (inr x) → inr (f (g x)) }
  }

B : ⟦ (set ⇒ set) ⇒ (set ⇒ set) ⟧T
B F X = X × F (F X)

FuncB : ⟦ (set ⇒ set) ⇒ (set ⇒ set) ⟧F B
FuncB = BB , BBB
  where
  open Func

  -- B maps 1st-order functor to 1st-order functor
  BB : (F : Set → Set) → ⟦ set ⇒ set ⟧F F → ⟦ set ⇒ set ⟧F (B F)
  BB F (_ , record { fmap = fmap ; fmapid = fmapid ; fmap∘ = fmap∘ }) = _ , record
    { fmap = λ f (x , ffx) → f x , fmap (fmap f) ffx
    ; fmapid = λ i (x , ffx) → x , (cong fmap fmapid ∙ fmapid) i ffx
    ; fmap∘ = λ f g i (x , ffx) → f (g x) , (cong fmap (fmap∘ f g) ∙ fmap∘ (fmap f) (fmap g)) i ffx
    }

  -- 2nd-order functorial of B
  BBB : Func ⟦ set ⇒ set ⟧C ⟦ set ⇒ set ⟧C _

  BBB .fmap {F , _ , FF} {G , _ , GG} record { η = η ; nat = nat }
    = record
    { η = λ (X , _) (x , ffx) → x , η (G X , tt) (fmap FF (η (X , tt)) ffx)
    ; nat = λ f i (x , ffx) → f x , aux f i ffx
    }
    where
      open Cat ⟦ set ⟧C
      aux : {X Y : Set} (f : X → Y)
        → fmap GG (fmap GG f) ∘ η (G X , tt) ∘ fmap FF (η (X , tt))
        ≡ η (G Y , tt) ∘ fmap FF (η (Y , tt)) ∘ fmap FF (fmap FF f)
      aux {X} {Y} f =
        fmap GG (fmap GG f) ∘ η (G X , tt) ∘ fmap FF (η (X , tt))
          ≡⟨ cong (fmap GG (fmap GG f) ∘_) (sym (nat (η (X , tt)))) ⟩
        fmap GG (fmap GG f) ∘ fmap GG (η (X , tt)) ∘ η (F X , tt)
          ≡⟨ cong (_∘ η (F X , tt)) (sym (fmap∘ GG (fmap GG f) (η (X , tt)))) ⟩
        fmap GG (fmap GG f ∘ η (X , tt)) ∘ η (F X , tt)
          ≡⟨ cong (_∘ η (F X , tt)) (cong (fmap GG) (nat f)) ⟩
        fmap GG (η (Y , tt) ∘ fmap FF f) ∘ η (F X , tt)
          ≡⟨ cong (_∘ η (F X , tt)) (fmap∘ GG (η (Y , tt)) (fmap FF f)) ⟩
        fmap GG (η (Y , tt)) ∘ fmap GG (fmap FF f) ∘ η (F X , tt)
          ≡⟨ cong (fmap GG (η (Y , tt)) ∘_) (nat (fmap FF f)) ⟩
        fmap GG (η (Y , tt)) ∘ η (F Y , tt) ∘ fmap FF (fmap FF f)
          ≡⟨ cong (_∘ fmap FF (fmap FF f)) (nat (η (Y , tt))) ⟩
        η (G Y , tt) ∘ fmap FF (η (Y , tt)) ∘ fmap FF (fmap FF f)
          ∎

  BBB .fmapid {F , _ , FF} = Nat≡ (λ i (X , _) (x , ffx) → x , fmapid FF i ffx)

  BBB .fmap∘ {F , _ , FF} {G , _ , GG} {H , _ , HH}
    record { η = η₁ ; nat = nat₁ }
    record { η = η₂ ; nat = nat₂ }
    = Nat≡ (λ i (X , _) (x , ffx) → x , aux i ffx)
    where
      open Cat ⟦ set ⟧C
      aux : {X : Set}
        → η₁ (H X , tt) ∘ η₂ (H X , tt) ∘ fmap FF(η₁ (X , tt) ∘ η₂ (X , tt))
        ≡ η₁ (H X , tt) ∘ fmap GG (η₁ (X , tt)) ∘ η₂ (G X , tt) ∘ fmap FF (η₂ (X , tt))
      aux {X} =
        η₁ (H X , tt) ∘ η₂ (H X , tt) ∘ fmap FF (η₁ (X , tt) ∘ η₂ (X , tt))
          ≡⟨ cong ((η₁ (H X , tt) ∘ η₂ (H X , tt)) ∘_) (fmap∘ FF (η₁ (X , tt)) (η₂ (X , tt))) ⟩
        η₁ (H X , tt) ∘ η₂ (H X , tt) ∘ fmap FF (η₁ (X , tt)) ∘ fmap FF (η₂ (X , tt))
          ≡⟨ cong (η₁ (H X , tt) ∘_) (cong (_∘ fmap FF (η₂ (X , tt))) (sym (nat₂ (η₁ (X , tt))))) ⟩
        η₁ (H X , tt) ∘ fmap GG (η₁ (X , tt)) ∘ η₂ (G X , tt) ∘ fmap FF (η₂ (X , tt)) ∎
