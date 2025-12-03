{-# OPTIONS --guardedness #-}

module TmSCWF where

open import Function.Base
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
  _▹_ : (Γ : Con) (A : Ty) → Con

variable Γ Δ Θ : Con

data Var : Con → Ty → Set where
  vz : Var (Γ ▹ A) A
  vs : (x : Var Γ A) → Var (Γ ▹ B) A

variable x y : Var Γ A

data Tm : Con → Ty → Set₁ where
  var : (x : Var Γ A) → Tm Γ A
  lam : (t : Tm (Γ ▹ A) B) → Tm Γ (A ⇒ B)
  app : (t : Tm Γ (A ⇒ B)) (u : Tm Γ A) → Tm Γ B
  Π : (I : Set) (f : I → Tm Γ A) → Tm Γ A
  Σ : (I : Set) (f : I → Tm Γ A) → Tm Γ A

variable t u : Tm Γ A

infixl 5 _,_
data Tms : Con → Con → Set₁ where
  ε   : Tms Γ ∙
  _,_ : (γ : Tms Δ Γ) (t : Tm Δ A) → Tms Δ (Γ ▹ A)

variable γ δ θ : Tms Γ Δ

_-_ : (Γ : Con) (x : Var Γ A) → Con
(Γ ▹ A) - vz = Γ
(Γ ▹ A) - vs x = (Γ - x) ▹ A

wkv : (x : Var Γ A) (y : Var (Γ - x) B) → Var Γ B
wkv vz y = vs y
wkv (vs x) vz = vz
wkv (vs x) (vs y) = vs (wkv x y)

wkTm : (x : Var Γ A) (t : Tm (Γ - x) B) → Tm Γ B
wkTm x (var v) = var (wkv x v)
wkTm x (lam t) = lam (wkTm (vs x) t)
wkTm x (app t u) = app (wkTm x t) (wkTm x u)
wkTm x (Π I f) = Π I (wkTm x ∘ f)
wkTm x (Σ I f) = Σ I (wkTm x ∘ f)

wkTms : (x : Var Δ A) (γ : Tms (Δ - x) Γ) → Tms Δ Γ
wkTms x ε = ε
wkTms x (γ , t) = wkTms x γ , wkTm x t

_↑_ : (γ : Tms Δ Γ) (A : Ty) → Tms (Δ ▹ A) (Γ ▹ A)
γ ↑ A = wkTms vz γ , var vz

_[_]v : (x : Var Γ A) (γ : Tms Δ Γ) → Tm Δ A
vz [ γ , t ]v = t
vs x [ γ , t ]v = x [ γ ]v

_[_] : (t : Tm Γ A) (γ : Tms Δ Γ) → Tm Δ A
var x [ γ ] = x [ γ ]v
lam t [ γ ] = lam (t [ γ ↑ _ ])
app t u [ γ ] = app (t [ γ ]) (u [ γ ])
Π I f [ γ ] = Π I (_[ γ ] ∘ f)
Σ I f [ γ ] = Σ I (_[ γ ] ∘ f)

id' : Tms Γ Γ
id' {∙} = ε
id' {Γ ▹ A} = id' {Γ} ↑ A

_∘'_ : (γ : Tms Δ Γ) (δ : Tms Θ Δ) → Tms Θ Γ
ε ∘' γ = ε
(δ , t) ∘' γ = (δ ∘' γ) , t [ γ ]

π₁ : Tms Δ (Γ ▹ A) → Tms Δ Γ
π₁ (γ , t) = γ

π₂ : Tms Δ (Γ ▹ A) → Tm Δ A
π₂ (γ , t) = t

π₁β : π₁ (γ , t) ≡ γ
π₁β = refl

π₂β : π₂ (γ , t) ≡ t
π₂β = refl

πη : (π₁ γ , π₂ γ) ≡ γ
πη {γ = γ , t} = refl

,∘ : (γ , t) ∘' δ ≡ γ ∘' δ , t [ δ ]
,∘ = refl

open ≡-Reasoning

nat[]v : (vs x) [ γ ↑ A ]v ≡ wkTm vz (x [ γ ]v)
nat[]v {x = vz} {γ = γ , t} = refl
nat[]v {x = vs x} {γ = γ , t} = nat[]v {x = x}
  
[id]v : x [ id' ]v ≡ var x
[id]v {x = vz} = refl
[id]v {x = vs x} = begin
  vs x [ id' ]v        ≡⟨⟩
  x [ wkTms vz id' ]v  ≡⟨ nat[]v {x = x} ⟩
  wkTm vz (x [ id' ]v) ≡⟨ cong (wkTm vz) [id]v ⟩
  wkTm vz (var x)      ≡⟨⟩
  var (vs x)           ∎

[id] : t [ id' ] ≡ t
[id] {t = var x} = [id]v {x = x}
[id] {t = lam t} = cong lam [id]
[id] {t = app t u} = cong₂ app [id] [id]
[id] {t = Π I x} = cong (Π I) (funExt λ i → [id])
[id] {t = Σ I x} = cong (Σ I) (funExt λ i → [id])

[∘]v : x [ γ ∘' δ ]v ≡ x [ γ ]v [ δ ]
[∘]v {x = vz} {γ = γ , t} = refl
[∘]v {x = vs x} {γ = γ , t} = [∘]v {x = x}

tvz : Tm (Γ ▹ A) A
tvz = var vz

tvs : Tm Γ A → Tm (Γ ▹ B) A
tvs t = wkTm vz t

{-
_++_ : (Γ Δ : Con) → Con
Γ ++ ∙ = Γ
Γ ++ (Δ ▹ A) = (Γ ++ Δ) ▹ A

rule : ∙ ++ Γ ≡ Γ
rule {∙} = refl
rule {Γ ▹ A} = cong₂ _++_ (rule {Γ}) refl

_↑↑_ : (γ : Tms Δ Γ) (Θ : Con) → Tms (Δ ++ Θ) (Γ ++ Θ)
γ ↑↑ ∙ = γ
γ ↑↑ (Θ ▹ A) = (γ ↑↑ Θ) ↑ A
-}

{-
nat : t [ wkTms vz γ ] ≡ wkTm vz (t [ γ ])
nat {t = var x} = nat[]v {x = x}
nat {t = lam t} = cong lam {!!}
nat {t = app t u} = cong₂ app (nat {t = t}) (nat {t = u})
nat {t = Π I f} = cong (Π I) (funExt (λ i → nat {t = f i}))
nat {t = Σ I f} = cong (Σ I) (funExt (λ i → nat {t = f i}))
-}

nat[] : wkTm vz t [ γ ↑ A ] ≡ wkTm vz (t [ γ ])
nat[] {t = var x} = nat[]v {x = x}
nat[] {B ⇒ C} {Γ} {A} {lam t} {Δ} {γ}
  = cong lam (begin
  wkTm (vs vz) t [ (γ ↑ A) ↑ B ] ≡⟨ {!!} ⟩
  wkTm (vs vz) (t [ γ ↑ B ])     ∎)
nat[] {t = app t u} = cong₂ app (nat[] {t = t}) (nat[] {t = u})
nat[] {t = Π I f} = cong (Π I) (funExt (λ i → nat[] {t = f i}))
nat[] {t = Σ I f} = cong (Σ I) (funExt (λ i → nat[] {t = f i}))

lem : wkTms vz γ ∘' (δ ↑ A) ≡ wkTms vz (γ ∘' δ)
lem {γ = ε} = refl
lem {γ = γ , t} = cong₂ _,_ lem (nat[] {t = t})

↑∘ : (γ ↑ A) ∘' (δ ↑ A) ≡ (γ ∘' δ) ↑ A
↑∘ {γ = ε} = refl
↑∘ {γ = γ , t} = cong₂ _,_ (cong₂ _,_ lem (nat[] {t = t})) refl

[∘] : t [ γ ∘' δ ] ≡ t [ γ ] [ δ ]
[∘] {t = var x} = [∘]v {x = x}
[∘] {t = lam t} {γ = γ} {δ = δ} = begin
  lam t [ γ ∘' δ ]                ≡⟨⟩
  lam (t [ (γ ∘' δ) ↑ _ ])        ≡⟨ cong (λ γ → lam (t [ γ ])) (sym ↑∘) ⟩
  lam (t [ (γ ↑ _) ∘' (δ ↑ _) ])  ≡⟨ cong lam ([∘] {t = t}) ⟩  
  lam (t [ γ ↑ _ ] [ δ ↑ _ ])     ∎
[∘] {t = app t u} = cong₂ app ([∘] {t = t}) ([∘] {t = u})
[∘] {t = Π I f} = cong (Π I) (funExt λ i → [∘] {t = f i})
[∘] {t = Σ I f} = cong (Σ I) (funExt λ i → [∘] {t = f i})

lem1 : wkTms vz id' ∘' (γ , t) ≡ γ
lem1 {Γ} {Δ} {ε} {A} {t} = refl
lem1 {Γ} {Δ ▹ A} {γ , t} {B} {u} = {!!}

idl : id' ∘' γ ≡ γ
idl {Γ} {Δ} {ε} = refl
idl {Γ} {Δ} {γ , t} = cong₂ _,_ lem1 refl

idr : γ ∘' id' ≡ γ
idr {γ = ε} = refl
idr {γ = γ , t} = cong₂ _,_ idr [id]

ass : (γ ∘' δ) ∘' θ ≡ γ ∘' (δ ∘' θ)
ass {γ = ε} = refl
ass {γ = γ , t} = cong₂ _,_ ass (sym ([∘] {t = t}))

∙-η : γ ≡ ε
∙-η {Γ} {ε} = refl
