{-# OPTIONS --guardedness #-}

module SCWF where

open import Data.Empty
open import Data.Unit
open import Data.Sum hiding ([_,_])
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])

postulate
  funExt : {ℓ ℓ' : _} {A : Set ℓ} {B : A → Set ℓ'} {f g : (x : A) → B x}
    → ((x : A) → f x ≡ g x)
    → f ≡ g

funExt⁻ : {A : Set} {B : A → Set} {f g : (x : A) → B x}
  → f ≡ g
  → (x : A) → f x ≡ g x
funExt⁻ refl x = refl

{-- Syntax --}
  
{- Types & Contexts & Variables -}

infixr 20 _⇒_
data Ty : Set where
  * : Ty
  _⇒_ : Ty → Ty → Ty

variable A B C : Ty

infixl 5 _▹_
data Con : Set where
  ∙   : Con
  _▹_ : Con → Ty → Con

variable Γ Δ Θ : Con

data Var : Con → Ty → Set where
  vz : Var (Γ ▹ A) A
  vs : Var Γ A → Var (Γ ▹ B) A

variable x y : Var Γ A

{- Normal Forms -}

infixr 4 _,_

data Nf : Con → Ty → Set₁

record Ne (Γ : Con) (B : Ty) : Set₁

data Sp : Con → Ty → Ty → Set₁

data Nf where
  lam : Nf (Γ ▹ A) B → Nf Γ (A ⇒ B)
  ne  : Ne Γ * → Nf Γ *

variable t u w : Nf Γ A

record Ne Γ B where
  constructor _◃_◃_
  inductive
  field
    S : Set
    P : Var Γ A → S → Set
    R : (x : Var Γ A) (s : S) → P x s → Sp Γ A B

variable spr tql : Ne Γ A

data Sp where
  ε   : Sp Γ A A
  _,_ : Nf Γ A → Sp Γ B C → Sp Γ (A ⇒ B) C
  
variable ts us ws : Sp Γ A B

HCont : Ty → Set₁
HCont = Nf ∙

ap : Nf Γ (A ⇒ B) → Nf (Γ ▹ A) B
ap (lam t) = t

en : Nf Γ * → Ne Γ *
en (ne spr) = spr

_-_ : (Γ : Con) → Var Γ A → Con
∙ - ()
(Γ ▹ A) - vz = Γ
(Γ ▹ A) - (vs x) = (Γ - x) ▹ A

wkv : (x : Var Γ A) → Var (Γ - x) B → Var Γ B
wkv vz y = vs y
wkv (vs x) vz = vz
wkv (vs x) (vs y) = vs (wkv x y)

data EqVar : Var Γ A → Var Γ B → Set where
  same : EqVar x x
  diff : (x : Var Γ A) (y : Var (Γ - x) B) → EqVar x (wkv x y)

eq : (x : Var Γ A) (y : Var Γ B) → EqVar x y
eq vz vz = same
eq vz (vs y) = diff vz y
eq (vs x) vz = diff (vs x) vz
eq (vs x) (vs y) with eq x y
eq (vs x) (vs .x)          | same = same
eq (vs x) (vs .(wkv x y′)) | diff .x y′ = diff (vs x) (vs y′)

{- Normal Forms Weakening -}

wkNf : (x : Var Γ A) → Nf (Γ - x) B → Nf Γ B

wkNe : (x : Var Γ A) → Ne (Γ - x) B → Ne Γ B

wkSp : (x : Var Γ A) → Sp (Γ - x) B C → Sp Γ B C

wkNf x (lam t) = lam (wkNf (vs x) t)
wkNf x (ne spr) = ne (wkNe x spr)

wkNe {Γ} {A} {C} x (S ◃ P ◃ R) = S′ ◃ P′ ◃ R′
  where
  S′ : Set
  S′ = S
  
  P′ : Var Γ B → S → Set
  P′ y  s with eq x y
  P′ .x s | same = ⊥
  P′ y  s | diff .x y′ = P y′ s

  R′ : (y : Var Γ B) (s : S) → P′ y s → Sp Γ B C
  R′ y s p with eq x y
  R′ y s p | diff .x y′ = wkSp x (R y′ s p)

wkSp x ε = ε
wkSp x (t , ts) = wkNf x t , wkSp x ts

{- η-expansion -}

appSp : Sp Γ A (B ⇒ C) → Nf Γ B → Sp Γ A C
appSp ε u = u , ε
appSp (t , ts) u = t , appSp ts u

nvar : Var Γ A → Nf Γ A

ne2nf : Ne Γ A → Nf Γ A

nvar {Γ} {B} x = ne2nf (S ◃ P ◃ R)
  where
  S : Set
  S = ⊤

  P : Var Γ A → S → Set
  P y  tt with eq x y
  P .x tt | same = ⊤
  P y  tt | diff .x y′ = ⊥

  R : (y : Var Γ A) (s : S) → P y s → Sp Γ A B
  R y tt p with eq x y
  R .x tt p | same = ε
  R y tt () | diff .x y′

ne2nf {Γ} {*} spr = ne spr
ne2nf {Γ} {A ⇒ C} (S ◃ P ◃ R) = lam (ne2nf (S ◃ P′ ◃ R′))
  where
  P′ : Var (Γ ▹ A) B → S → Set
  P′ vz s = ⊥
  P′ (vs x) s = P x s

  R′ : (x : Var (Γ ▹ A) B) (s : S) → P′ x s → Sp (Γ ▹ A) B C
  R′ vz s ()
  R′ (vs x) s p = appSp (wkSp vz (R x s p)) (nvar vz)

{- Normalization -}

_[_:=_] : Nf Γ B → (x : Var Γ A) → Nf (Γ - x) A → Nf (Γ - x) B

_<_:=_> : Sp Γ B C → (x : Var Γ A) → Nf (Γ - x) A → Sp (Γ - x) B C

lam t [ x := u ] = lam (t [ vs x := wkNf vz u ])
ne {Γ} (S ◃ P ◃ R) [ x := u ] = ne (S′ ◃ P′ ◃ R′)
  where
  S′ : Set
  S′ = S
  
  P′ : Var (Γ - x) A → S → Set
  P′ y s = P (wkv x y) s
  
  R′ : (y : Var (Γ - x) A) (s : S) → P′ y s → Sp (Γ - x) A *
  R′ y s p = R (wkv x y) s p < x := u >

ε < x := u > = ε
(t , ts) < x := u > = (t [ x := u ]) , (ts < x := u >)

napp : Nf Γ (A ⇒ B) → Nf Γ A → Nf Γ B
napp (lam t) u = t [ vz := u ]

_◇_ : Nf Γ A → Sp Γ A B → Nf Γ B
t ◇ ε = t
t ◇ (u , us) = napp t u ◇ us

⊤nf : Nf Γ A
⊤nf {Γ} {*} = ne (⊤ ◃ (λ{ x tt → ⊥ }) ◃ λ{ x tt () })
⊤nf {Γ} {A ⇒ B} = lam ⊤nf

⊥nf : Nf Γ A
⊥nf {Γ} {*} = ne (⊥ ◃ (λ x ()) ◃ (λ x ()))
⊥nf {Γ} {A ⇒ B} = lam ⊥nf

_×nf_ : Nf Γ A → Nf Γ A → Nf Γ A
lam t ×nf lam u = lam (t ×nf u)
_×nf_ {Γ} {B} (ne (S ◃ P ◃ R)) (ne (T ◃ Q ◃ L)) = ne (S′ ◃ P′ ◃ R′)
  where
  S′ : Set
  S′ = S × T

  P′ : Var Γ A → S′ → Set
  P′ x (s , t) = P x s ⊎ Q x t

  R′ : (x : Var Γ A) (s : S′) → P′ x s → Sp Γ A B
  R′ x (s , t) (inj₁ p) = R x s p
  R′ x (s , t) (inj₂ q) = L x t q

_⊎nf_ : Nf Γ A → Nf Γ A → Nf Γ A
lam t ⊎nf lam u = lam (t ⊎nf u)
_⊎nf_ {Γ} {B} (ne (S ◃ P ◃ R)) (ne (T ◃ Q ◃ L)) = ne (S′ ◃ P′ ◃ R′)
  where
  S′ : Set
  S′ = S ⊎ T

  P′ : Var Γ A → S′ → Set
  P′ x (inj₁ s) = P x s
  P′ x (inj₂ t) = Q x t

  R′ : (x : Var Γ A) (s : S′) → P′ x s → Sp Γ A B
  R′ x (inj₁ s) p = R x s p
  R′ x (inj₂ t) q = L x t q

Πnf : (I : Set) → (I → Nf Γ A) → Nf Γ A
Πnf {Γ} {A ⇒ B} I ts = lam (Πnf I (λ i → ap (ts i)))
Πnf {Γ} {*} I ts = ne (S ◃ P ◃ R)
  where
  S : Set
  S = (i : I) → en (ts i) .Ne.S

  P : Var Γ A → S → Set
  P x f = Σ[ i ∈ I ] en (ts i) .Ne.P x (f i)

  R : (x : Var Γ A) (s : S) → P x s → Sp Γ A *
  R x f (i , p) = en (ts i) .Ne.R x (f i) p

Σnf : (I : Set) → (I → Nf Γ A) → Nf Γ A
Σnf {Γ} {A ⇒ B} I f = lam (Σnf I (λ i → ap (f i)))
Σnf {Γ} {*} I f = ne (S ◃ P ◃ R)
  where
  S : Set
  S = Σ[ i ∈ I ] en (f i) .Ne.S

  P : Var Γ A → S → Set
  P x (i , s) = en (f i) .Ne.P x s

  R : (x : Var Γ A) (s : S) → P x s → Sp Γ A *
  R x (i , s) p = en (f i) .Ne.R x s p

infix 2 Σnf-syntax
Σnf-syntax : (I : Set) → (I → Nf Γ A) → Nf Γ A
Σnf-syntax = Πnf
syntax Σnf-syntax A (λ x → B) = Σnf[ x ∈ A ] B

infix 2 Πnf-syntax
Πnf-syntax : (I : Set) → (I → Nf Γ A) → Nf Γ A
Πnf-syntax = Πnf
syntax Πnf-syntax A (λ x → B) = Πnf[ x ∈ A ] B

data Nfs : Con → Con → Set₁ where
  ε   : Nfs Γ ∙
  _,_ : Nfs Δ Γ → Nf Δ A → Nfs Δ (Γ ▹ A)

variable γ δ : Nfs Γ Δ

wkNfs : (x : Var Δ A) → Nfs (Δ - x) Γ → Nfs Δ Γ
wkNfs x ε = ε
wkNfs x (γ , t) = wkNfs x γ , wkNf x t

_↑ : Nfs Δ Γ → Nfs (Δ ▹ A) (Γ ▹ A)
γ ↑ = wkNfs vz γ , nvar vz

subv : Var Γ A → Nfs Δ Γ → Nf Δ A
subv vz (γ , t) = t
subv (vs x) (γ , t) = subv x γ

_[_] : Nf Γ A → Nfs Δ Γ → Nf Δ A

_[_]sp : Sp Γ A B → Nfs Δ Γ → Sp Δ A B

lam t [ γ ] = lam (t [ γ ↑ ])
ne {Γ} (S ◃ P ◃ R) [ γ ] = Σnf S (λ s →
  Πnf Ty (λ A → Πnf (Var Γ A) (λ x → Πnf (P x s) (λ p →
  subv x γ ◇ (R x s p [ γ ]sp)
  ))))

{-
Σnf[ s ∈ S ]
  Πnf[ A ∈ Ty ] Πnf[ x ∈ Var Γ A ] Πnf[ p ∈ P x s ]
  (subv x γ) ◇ (R x s p [ γ ]sp)
-}
ε [ γ ]sp = ε
(t , ts) [ γ ]sp = t [ γ ] , ts [ γ ]sp

id : Nfs Γ Γ
id {∙} = ε
id {Γ ▹ A} = id ↑

_∘_ : Nfs Δ Γ → Nfs Θ Δ → Nfs Θ Γ
ε ∘ γ = ε
(δ , t) ∘ γ = (δ ∘ γ) , t [ γ ]

π₁ : Nfs Δ (Γ ▹ A) → Nfs Δ Γ
π₁ (γ , t) = γ

π₂ : Nfs Δ (Γ ▹ A) → Nf Δ A
π₂ (γ , t) = t

π₁β : π₁ (γ , t) ≡ γ
π₁β = refl

π₂β : π₂ (γ , t) ≡ t
π₂β = refl

πη : (π₁ γ , π₂ γ) ≡ γ
πη {γ = γ , t} = refl

,∘ : (γ , t) ∘ δ ≡ (γ ∘ δ , t [ δ ])
,∘ = refl

{- Not easy part -}

ne≡ : {Γ : Con} {B : Ty}
  {S T : Set} (eq-shape : S ≡ T)
  {P : {A : Ty} (x : Var Γ A) (s : S) → Set}
  {Q : {A : Ty} (x : Var Γ A) (t : T) → Set}
  (eq-pos : _≡_ {A = {A : Ty} (x : Var Γ A) (s : S) → Set} P
    (λ {A} x s → Q {A} x (subst (λ S → S) eq-shape s)))
  {R : {A : Ty} (x : Var Γ A) (s : S) (p : P x s) → Sp Γ A B}
  {L : {A : Ty} (x : Var Γ A) (t : T) (q : Q x t) → Sp Γ A B}
  (eq-rec : _≡_ {A = {A : Ty} (x : Var Γ A) (s : S) (p : P x s) → Sp Γ A B} R
    λ {A} x s p → L {A} x (subst (λ S → S) eq-shape s)
      (subst₂ (λ S P → P x s) eq-shape eq-pos p))
  → _≡_ {A = Ne Γ B} (S ◃ P ◃ R) (T ◃ Q ◃ L)
ne≡ refl refl refl = refl

[id] : {Γ : Con} {A : Ty} {t : Nf Γ A} → t [ id ] ≡ t
[id] {Γ} {A ⇒ B} {lam t} = cong lam [id]
[id] {Γ} {*} {ne (S ◃ P ◃ R)} = cong ne (ne≡ {!!} {!!} {!!})

↑∘ : {Γ Δ Θ : Con} {γ : Nfs Δ Γ} {δ : Nfs Θ Δ} {A : Ty}
  → _↑ {A = A} (γ ∘ δ) ≡ (γ ↑) ∘ (δ ↑)
↑∘ {∙} {Δ} {Θ} {ε} {δ} {A} = cong₂ _,_ refl {!!}
↑∘ {Γ ▹ A} {Δ} {Θ} {γ , t} {δ} {B} = cong₂ _,_ (cong₂ _,_ {!!} {!!}) {!!}

[∘] : {Γ Δ Θ : Con} {A : Ty} {t : Nf Γ A} {γ : Nfs Δ Γ} {δ : Nfs Θ Δ}
  → t [ γ ∘ δ ] ≡ (t [ γ ]) [ δ ]
[∘] {Γ} {Δ} {Θ} {A} {lam t} {γ} {δ} = cong lam (trans (cong (t [_]) ↑∘) ([∘] {t = t}))
[∘] {Γ} {Δ} {Θ} {A} {ne x} {γ} {δ} = cong ne {!!}

nvz[] : (nvar vz) [ γ , t ] ≡ t
nvz[] {Γ} {Δ} {γ} {*} {ne e} = cong ne {!!}
nvz[] {Γ} {Δ} {γ} {A ⇒ B} {lam t} = cong lam {!!}

lem2 : (wkNfs vz id ∘ (γ , t)) ≡ γ
lem2 {Γ} {∙} {ε} {A} {t} = refl
lem2 {Γ} {Δ ▹ A} {γ , t} {B} {u} = cong₂ _,_ {!!} {!!}

idl : {Γ Δ : Con} {γ : Nfs Δ Γ} → id ∘ γ ≡ γ
idl {Γ} {Δ} {ε} = refl
idl {Γ} {Δ} {γ , t} = cong₂ _,_ lem2 nvz[]

idr : {Γ Δ : Con} {γ : Nfs Δ Γ} → γ ∘ id ≡ γ
idr {Γ} {Δ} {ε} = refl
idr {Γ} {Δ} {γ , t} = cong₂ _,_ idr [id]

ass : {Γ Δ Θ Ξ : Con} {γ : Nfs Δ Γ} {δ : Nfs Θ Δ} {θ : Nfs Ξ Θ}
   → (γ ∘ δ) ∘ θ ≡ γ ∘ (δ ∘ θ)
ass {Γ} {Δ} {Θ} {Ξ} {ε} {δ} {θ} = refl
ass {Γ ▹ A} {Δ} {Θ} {Ξ} {γ , t} {δ} {θ} = cong₂ _,_ ass (sym ([∘] {t = t} {γ = δ} {δ = θ}))

∙-η : {Γ : Con}{γ : Nfs Γ ∙} → γ ≡ ε
∙-η {Γ} {ε} = refl
