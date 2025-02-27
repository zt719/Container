{-# OPTIONS --type-in-type #-}

{- tree types, with dom and appT -}

open import Data.Product
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality

{- Syntax -}

data Ty : Set where
  set : Ty
  _⇒_ : Ty → Ty → Ty

data Con : Set where
  • : Con
  _▷_ : Con → Ty → Con

infixl 5 _▷_

dom : Ty → Con
dom set = •
dom (A ⇒ B) = dom B ▷ A

variable A B C : Ty
variable Γ Δ : Con

data Var : Con → Ty → Set where
  zero : Var (Γ ▷ A) A
  suc  : Var Γ A → Var (Γ ▷ B) A

record HCont-Set (Γ : Con) : Set

data HCont-NE (Γ : Con) : Con → Set

data HCont-NF : Con → Ty → Set where
  lam : HCont-NF (Γ ▷ A) B → HCont-NF Γ (A ⇒ B)
  ne  : HCont-Set Γ → HCont-NF Γ set

record HCont-Set Γ  where
  inductive
  field
    S : Var Γ A → Set
    P : {x : Var Γ A}(s : S x) → Set
    R : {x : Var Γ A}{s : S x}(p : P s) → HCont-NE Γ (dom A)

data HCont-NE Γ where
  ε : HCont-NE Γ • 
  _,_ : HCont-NE Γ Δ → HCont-NF Γ A → HCont-NE Γ (Δ ▷ A)

HCont : Ty → Set
HCont A = HCont-NF • A

-- Semantics

⟦_⟧T : Ty → Set
⟦ set ⟧T = Set
⟦ A ⇒ B ⟧T = ⟦ A ⟧T → ⟦ B ⟧T

⟦_⟧C : Con → Set
⟦ • ⟧C = ⊤
⟦ Γ ▷ A ⟧C = ⟦ Γ ⟧C × ⟦ A ⟧T

appT : ⟦ A ⟧T → ⟦ dom A ⟧C → Set
appT {A = set} X tt = X
appT {A = A ⇒ B} f (β , a) = appT {A = B} (f a) β

⟦_⟧v : Var Γ A → ⟦ Γ ⟧C → ⟦ A ⟧T
⟦ zero ⟧v (_ , a) = a
⟦ suc x ⟧v (γ , _) = ⟦ x ⟧v γ

--record ⟦_⟧set (DD : HCont-Set Γ)(γ : ⟦ Γ ⟧C) : Set
⟦_⟧set : (DD : HCont-Set Γ)(γ : ⟦ Γ ⟧C) → Set
⟦_⟧ne : HCont-NE Γ Δ → ⟦ Γ ⟧C → ⟦ Δ ⟧C

⟦_⟧nf : HCont-NF Γ A → ⟦ Γ ⟧C → ⟦ A ⟧T
⟦ lam CC ⟧nf γ a = ⟦ CC ⟧nf (γ , a)
⟦ ne DD ⟧nf γ = ⟦ DD ⟧set γ

app : HCont-NF Γ (A ⇒ B) → HCont-NF (Γ ▷ A) B
app (lam CC) = CC

⟦_⟧set {Γ} record { S = S ; P = P ; R = R } γ =
  Σ[ s ∈ ({A : Ty}(x : Var Γ A) → S x) ]
    ({A : Ty}{x : Var Γ A}{s : S x}(p : P s) → appT (⟦ x ⟧v γ) (⟦ R p ⟧ne γ) )

⟦_⟧H : HCont A → ⟦ A ⟧T
⟦ C ⟧H = ⟦ C ⟧nf tt

{-
record ⟦_⟧set {Γ} CC γ where
  inductive
  open HCont-Set CC
  field
    s : (x : Var Γ A) → S x
    r : {x : Var Γ A}{s : S x}(p : P s) → appT (⟦ x ⟧v γ) (⟦ R p ⟧ne γ) 
-}
⟦ ε ⟧ne γ = tt
⟦ CC* , CC ⟧ne γ = ⟦ CC* ⟧ne γ , ⟦ CC ⟧nf γ

-- morphisms


{-
record Cat : Set where
  field
    obj : Set
    hom : obj → obj → Set
    id : {A : obj} → hom A A
    _∘_ : {A B C : obj} → hom B C → hom A B → hom A C

record FuncSet (A B : Cat) : Set where
  open Cat A renaming (obj to objA ; hom to homA ; id to idA ; _∘_ to _∘A_)
  open Cat B renaming (obj to objB ; hom to homB ; id to idB ; _∘_ to _∘B_)   
  field
    Fobj : objA → objB
    Fmap : {X Y : objA} → homA X Y → homB (Fobj X) (Fobj Y)

Func : Cat → Cat → Cat

record Nat {A B : Cat} (F G : FuncSet A B) : Set where
  open Cat A renaming (obj to objA ; hom to homA ; id to idA ; _∘_ to _∘A_)
  open Cat B renaming (obj to objB ; hom to homB ; id to idB ; _∘_ to _∘B_)
  open FuncSet F
  open FuncSet G renaming (Fobj to Gobj ; Fmap to Gmap)
  field 
     fam : (X : objA) → homB (Fobj X) (Gobj X)
     -- nat : {X Y : objA}(f : homA X Y) →
     --          (Gmap f) ∘B (α X) ≡ (α Y) ∘B (Fmap f)  

Func A B =
  record {
    obj = FuncSet A B ;
    hom = λ F G → Nat F G ;
    id = λ {F} →
        record { fam = λ X → idB {(FuncSet.Fobj F X)} } ;
    _∘_ = λ {F} {G} {H} β α →
        record { fam = λ X → (Nat.fam β) X ∘B Nat.fam α X} }
  where
    open Cat A renaming (obj to objA ; hom to homA ; id to idA ; _∘_ to _∘A_)
    open Cat B renaming (obj to objB ; hom to homB ; id to idB ; _∘_ to _∘B_)

SET : Cat
Cat.obj SET = Set
Cat.hom SET = λ X Y → X → Y
Cat.id SET = λ x → x
Cat._∘_ SET = λ g f a → g (f a)

⟦_⟧Cat : Ty → Cat
⟦ set ⟧Cat = SET
⟦ A ⇒ B ⟧Cat = Func ⟦ A ⟧Cat ⟦ B ⟧Cat

⊤-Cat : Cat
⊤-Cat = record { obj = ⊤ ; hom = λ tt tt → ⊤ ; id = tt ; _∘_ = λ tt tt → tt }

_×-Cat_ : Cat → Cat → Cat
A ×-Cat B =
  record { obj = objA × objB ;
           hom = λ (A₀ , B₀) (A₁ , B₁) → homA A₀ A₁ × homB B₀ B₁ ;
           id = λ {(X , Y)} → idA {X} , idB {Y} ;
           _∘_ = λ (f₀ , g₀) (f₁ , g₁) → (f₀ ∘A f₁) , (g₀ ∘B g₁) }
    where
    open Cat A renaming (obj to objA ; hom to homA ; id to idA ; _∘_ to _∘A_)
    open Cat B renaming (obj to objB ; hom to homB ; id to idB ; _∘_ to _∘B_)

⟦_⟧Cat-C : Con → Cat
⟦ • ⟧Cat-C = ⊤-Cat
⟦ Γ ▷ A ⟧Cat-C = ⟦ Γ ⟧Cat-C ×-Cat ⟦ A ⟧Cat

⟦_⟧cat-nf : HCont-NF Γ A → FuncSet ⟦ Γ ⟧Cat-C ⟦ A ⟧Cat
⟦ CC ⟧cat-nf = {!!}


⟦_⟧cat : {A : Ty} → HCont A → Cat.obj (⟦ A ⟧Cat)
⟦ CC ⟧cat = {!!}

-}


{-
record Cat : Set where
  field
    obj : Set
    hom : obj → obj → Set
    id : {A : obj} → hom A A
    _∘_ : {A B C : obj} → hom B C → hom A B → hom A C

record FuncSet (A B : Cat) : Set where
  open Cat A renaming (obj to objA ; hom to homA ; id to idA ; _∘_ to _∘A_)
  open Cat B renaming (obj to objB ; hom to homB ; id to idB ; _∘_ to _∘B_)   
  field
    Fobj : objA → objB
    Fmap : {X Y : objA} → homA X Y → homB (Fobj X) (Fobj Y)

Func : Cat → Cat → Cat

record Nat {A B : Cat} (F G : FuncSet A B) : Set where
  open Cat A renaming (obj to objA ; hom to homA ; id to idA ; _∘_ to _∘A_)
  open Cat B renaming (obj to objB ; hom to homB ; id to idB ; _∘_ to _∘B_)
  open FuncSet F
  open FuncSet G renaming (Fobj to Gobj ; Fmap to Gmap)
  field 
     α : (X : objA) → homB (Fobj X) (Gobj X)
     nat : {X Y : objA}(f : homA X Y) →
              (Gmap f) ∘B (α X) ≡ (α Y) ∘B (Fmap f)  

Func A B =
  record {
    obj = FuncSet A B ;
    hom = λ F G → Nat F G ;
    id = λ {F} →
         record { α = λ X → idB {(FuncSet.Fobj F X)} ;
                  nat = {!!} } ;
    _∘_ = {!!} }
  where
    open Cat A renaming (obj to objA ; hom to homA ; id to idA ; _∘_ to _∘A_)
    open Cat B renaming (obj to objB ; hom to homB ; id to idB ; _∘_ to _∘B_)   
--    F : 
-}


{-
⟦_⟧ : HCont A → ⟦ A ⟧T
⟦ CC ⟧ = ⟦ CC ⟧nf tt

⟦_⟧T* : Ty → Set

record Func (A B : Ty) : Set 
record Nat {A B} (F G : Func A B) : Set
⟦_⟧Tm : (A : Ty) → (X Y : ⟦ A ⟧T) → Set
⟦ set ⟧Tm X Y = X → Y
⟦ A ⇒ B ⟧Tm F G = {!Nat F G!}




record Func A B where
  field
    F : ⟦ A ⟧T → ⟦ B ⟧T
    fmap : {X Y : ⟦ A ⟧T} → ⟦ A ⟧Tm X Y → ⟦ B ⟧Tm (F X) (F Y)

record Nat {A}{B} F G where
  field
    α : (X : ⟦ A ⟧T) → ⟦ B ⟧Tm (Func.F F X) (Func.F G X)
--    nat : {X Y : ⟦ A ⟧T} (f : ⟦ A ⟧Tm X Y)

-}
-- example

H : (Set → Set) → (Set → Set)
H F A = A × F (F A)

TT : Ty
TT =  ((set ⇒ set)  ⇒ (set ⇒ set))
HC : HCont TT
HC = lam (lam (ne (record { S = S ; P = P ; R = R })))
  where Γ₀ : Con
        Γ₀ = • ▷ (set ⇒ set) ▷ set
        S : {A : Ty} → Var Γ₀ A → Set
        S zero = ⊤
        S (suc zero) = ⊤
        P : {A : Ty} {x : Var Γ₀ A} → S x → Set
        P {x = zero} tt = ⊤
        P {x = suc zero} tt = ⊤
        R-FA-S : {A : Ty} → Var Γ₀ A → Set
        R-FA-S zero = ⊤
        R-FA-S (suc zero) = ⊤
        R-FA-P :  {A : Ty} {x : Var Γ₀ A} → R-FA-S x → Set 
        R-FA-P {x = zero} tt = ⊤
        R-FA-P {x = suc zero} tt = ⊥
        R-FA-R :  {A : Ty} {x : Var Γ₀ A} {s : R-FA-S x} → R-FA-P s → HCont-NE Γ₀ (dom A)
        R-FA-R {x = zero} tt = ε
        R-FA-R {x = suc zero} ()
        R-FA-R {x = suc (suc ())} s
        R-FA : HCont-Set Γ₀
        R-FA = record { S = R-FA-S ; P = R-FA-P ; R = R-FA-R }            
        R-FFA-S : {A : Ty} → Var Γ₀ A → Set
        R-FFA-S zero = ⊤
        R-FFA-S (suc zero) = ⊤
        R-FFA-P :  {A : Ty} {x : Var Γ₀ A} → R-FFA-S x → Set 
        R-FFA-P {x = zero} tt = ⊥
        R-FFA-P {x = suc zero} tt = ⊤
        R-FFA-R :  {A : Ty} {x : Var Γ₀ A} {s : R-FFA-S x} → R-FFA-P s → HCont-NE Γ₀ (dom A)
        R-FFA-R {x = zero} ()
        R-FFA-R {x = suc zero} p = ε , (ne R-FA)
        R-FFA-R {x = suc (suc ())} s
        R-FFA : HCont-Set Γ₀
        R-FFA = record { S = R-FFA-S ; P = R-FFA-P ; R = R-FFA-R }  
        R : {A : Ty} {x : Var Γ₀ A} {s : S x} → P s → HCont-NE Γ₀ (dom A)
        R {x = zero} p = ε
        R {x = suc zero} p = ε , (ne R-FFA) 

-- first order containers

record Cont : Set where
  constructor _◁_
  field
    S : Set
    P : S → Set

cont→hcont : Cont → HCont (set ⇒ set)
cont→hcont (S ◁ P) = lam (ne (record { S = T ; P = Q ; R = λ {A} {x} {s} p → R {s = s} p }))
  where T : Var (• ▷ set) A → Set
        T zero = S
        Q : {x : Var (• ▷ set) A} → T x → Set
        Q {x = zero} s = P s
        R : {A : Ty}{x : Var (• ▷ set) A} {s : T x} → Q {x = x} s → HCont-NE (• ▷ set) (dom A)
        R {x = zero} {s = s} q = ε {Γ = (• ▷ set)}
        
hcont→cont : HCont (set ⇒ set) → Cont
hcont→cont (lam (ne record { S = S ; P = P ; R = R })) = (S zero) ◁ P {x = zero}

--- categorical structure

{-

IC-NF : HCont-NF (• ▷ A) A
IC-NF {set} = {!!}
IC-NF {A ⇒ B} = {!!}

IC : HCont (A ⇒ A)
IC = {!!} -- lam {!!}

-}
