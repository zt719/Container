%\documentclass{beamer}
\documentclass[handout]{beamer}

%include lhs2TeX.fmt
%include agda.fmt
%include lib.fmt

%\usepackage{latexsym, amsmath, amssymb}
% \usepackage{graphicx}
% \usepackage{multimedia}
% \usepackage{animate}

\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{mathpartir}

\newcommand{\Set}{\mathbf{Set}}
\newcommand{\Prop}{\mathbf{Prop}}
\newcommand{\Type}{\mathbf{Type}}
\renewcommand{\iff}{\leftrightarrow}
\newcommand{\Nat}{\mathbb{N}}
\newcommand{\Int}{\mathbb{Z}}
\newcommand{\Rat}{\mathbb{Q}}
\newcommand{\Real}{\mathbb{R}}
\newcommand{\Bool}{\mathrm{Bool}}

%\newtheorem{theorem}{Theorem}

\providecommand\mathbbm{\mathbb}

% \usepackage{latex/agda}
% \usepackage{catchfilebetweentags}

\usepackage{ucs}
\usepackage[utf8x]{inputenc}
%\usepackage[utf8]{inputenc}
%\usepackage{textcomp}

\DeclareUnicodeCharacter{"2237}{:\!:}
\newcommand{\textlambda}{$\lambda$}

\mode<presentation>
{
  \usetheme[secheader]{Boadilla}
%  \setbeamercovered{transparent}
%  \setbeamercovered{highly dynamic} 
}

% prooftree


\author{Thorsten Altenkirch}
\institute[Nottingham] % (optional, but mostly needed)
{
  Functional Programming Laboratory\\
  School of Computer Science\\
  University of Nottingham
}


\beamerdefaultoverlayspecification{<+->}

\setbeamercovered{invisible}

\title{Containers in Higher Kinds}
\subtitle{jww Zhili Tian and H{\aa}kon Gylterud}

\begin{document}

\begin{frame}
  
    \titlepage 

\end{frame}

\begin{frame}{Old paper}

  \begin{block}{TLCA01}
    A. "Representations of first order function types as terminal
    coalgebras." \\
    Typed Lambda Calculi and Applications: 5th International Conference, TLCA 2001 
  \end{block}
  
\end{frame}

\begin{frame}{Example : Streams}

  |Stream A ≅ ℕ → A|
  
\end{frame}

\begin{frame}

  Given |ℕ ≅ 1 + ℕ|

  \begin{align*}
    |ℕ → A| & \cong |(1 + ℕ) → A|\\
            & \cong  |A × (ℕ → A)| 
\end{align*}

Hence:

|ℕ → A ≅ ν X : Set. A × X|
    
\end{frame}

\begin{frame}
  \frametitle{What about trees?}

  \begin{code}
  data BT : Type where
    leaf : BT
    node : BT → BT → BT
  \end{code}
  
\end{frame}


\begin{frame}

  Given |BT ≅ 1 + BT × BT|

  \begin{align*}
    |BT → A| & \cong |(1 + BT × BT) → A|\\
             & \cong  |A × (BT × BT → A)| \\
             & \cong  |A × (BT → (BT → A))|         
\end{align*}

Hence:

|BT → A ≅ (ν F : Set → Set . λ X . X × F (F X)) A|
    
\end{frame}

\begin{frame}

  \begin{code}
record Bush (A : Type) : Type where
  coinductive
  field
    head : A
    tail : Bush (Bush A)

 app :  Bush A → BT → A
 app bsh leaf = head bsh
 app bsh (node l r) = app (app (tail bsh) l) r

 lam : (BT → A) → Bush A
 head (lam f) = f leaf
 tail (lam f) = φ (λ l → φ (λ r → f (node l r)))
  \end{code}
  
\end{frame}

\begin{frame}{Another old paper}

  \begin{block}{TCS05}
    Abbott, Michael, A., and Neil Ghani. \\
    "Containers: Constructing strictly positive types." \\
    Theoretical Computer Science 342.1 (2005):  \end{block}
  
\end{frame}

\begin{frame}

  \begin{code}
record Cont : Set₁ where
  constructor _◁_
  field
    S : Set
    P : S → Set

⟦_⟧ : Cont → Set → Set
⟦ S ◁ P ⟧ X = Σ[ s ∈ S ] (P s → X) 
  \end{code}
  
\end{frame}

\begin{frame}
  \frametitle{Results on containers}

  \begin{itemize}
    
  \item Initial and terminal algebras
    \begin{align*}
      \mu |⟦ S ◁ P ⟧| & \cong |W S P|\\
      \nu |⟦ S ◁ P ⟧| & \cong |M S P|      
    \end{align*}
  \item Container morphisms
    \begin{align*}
      \int_{X : |Set|} |⟦ S ◁ P ⟧ X → ⟦ T ◁ Q ⟧ X|  & \cong \\
      |Σ[ f ∈ S → T ] (Q (f s) → P s)|
    \end{align*}
 
  \item Cont is cartesian closed.\\
    CIE 2010 (w Paul Levy and Sm Staton)
   % \begin{block}{CIE10}
   %   A., Paul Levy, and Sam Staton.\\
   %   "Higher-order containers."\\
   %   CiE 2010\end{block}
     
  \item Cont gives rise to a Category with families (CwF)\\
    TYPES 2021 abstract (w Ambrus Kaposi)
    
   % \begin{block}{TYPES21}
   %   Altenkirch, Thorsten, and Ambrus Kaposi.\\
   %   "A container model of type theory."\\
   %   TYPES 2021     
  % \end{block}
     .
  \end{itemize}
 
\end{frame}

\begin{frame}

  \Large
  How to express the results from the TLCA01 paper
  in the language of TCS05?
  
\end{frame}

\begin{frame}{What are containers in higher kinds?}

  \begin{code}
    H : (Set → Set) → Set → Set
    H F X = X × F (F X)
  \end{code}

\end{frame}

\begin{frame}{2nd order containers}
  \begin{code}
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

  \end{code}

\end{frame}

\begin{frame}
  \begin{code}
H : Cont₂
-- H F X = X × F (F X)
H = ⊤ ◁ (λ _ → ⊤) ,
        (λ _ _ → -- H' F X = F X
           ⊤ ◁ (λ _ → ⊤) ,
          (λ _ _ → -- H'' F X = X
            ⊤ ◁ (λ _ → ⊥) , (λ _ ()) , λ _ → ⊤) ,
          λ _ → ⊤) ,
        λ _ → ⊤ 
  \end{code}

\end{frame}

\begin{frame}{Higher containers}

  \begin{code}
data Ty : Set where
  ∘ : Ty
  _⇒_ : Ty → Ty → Ty

data Con : Set where
  ∙   : Con
  _▹_ : Con → Ty → Con

data Var : Con → Ty → Set where
  vz : Var (Γ ▹ A) A
  vs : Var Γ A → Var (Γ ▹ B) A
  \end{code}
  
\end{frame}

\begin{frame}
  \begin{code}
data Nf : Con → Ty → Set

record Ne (Γ : Con) (B : Ty) : Set

data Sp : Con → Ty → Ty → Set

data Nf where
  lam : Nf (Γ ▹ A) B → Nf Γ (A ⇒ B)
  ne  : Ne Γ ∘ → Nf Γ ∘

record Ne Γ B where
  inductive
  field
    S : Set
    P : S → Var Γ A → Set
    R : (s : S) (x : Var Γ A) (p : P s x) → Sp Γ A B

data Sp where
  ε   : Sp Γ A A
  _,_ : Nf Γ A → Sp Γ B C → Sp Γ (A ⇒ B) C
\end{code}

%HCont : Ty → Set
%HCont A = Nf ∙ A 
\end{frame}

\begin{frame}
  \frametitle{Semantics}
  \begin{code}
⟦_⟧T : Ty → Set
⟦ ∘ ⟧T = Set
⟦ A ⇒ B ⟧T = ⟦ A ⟧T → ⟦ B ⟧T

⟦_⟧C : Con → Set
⟦ ∙ ⟧C = ⊤
⟦ Γ ▹ A ⟧C = ⟦ Γ ⟧C × ⟦ A ⟧T

⟦_⟧v : Var Γ A → ⟦ Γ ⟧C → ⟦ A ⟧T
⟦ vz ⟧v (γ , a) = a
⟦ vs x ⟧v (γ , a) = ⟦ x ⟧v γ    
  \end{code}
\end{frame}

\begin{frame}
  \begin{code}
⟦_⟧nf : Nf Γ A → ⟦ Γ ⟧C → ⟦ A ⟧T
⟦_⟧ne : Ne Γ ∘ → ⟦ Γ ⟧C → Set
⟦_⟧sp : Sp Γ A B → ⟦ Γ ⟧C → ⟦ A ⟧T → ⟦ B ⟧T

⟦ lam x ⟧nf γ a = ⟦ x ⟧nf (γ , a)
⟦ ne x ⟧nf γ = ⟦ x ⟧ne γ

⟦_⟧ne {Γ} record { S = S ; P = P ; R = R } γ =
  Σ[ s ∈ S ]  ({A : Ty} (x : Var Γ A)
              (p : P s x) → ⟦ R s x p ⟧sp γ (⟦ x ⟧v γ))

⟦ ε ⟧sp γ a = a
⟦ n , ns ⟧sp γ f = ⟦ ns ⟧sp γ (f (⟦ n ⟧nf γ))
  \end{code}
\end{frame}

\begin{frame}
  \frametitle{Results?}

  \begin{itemize}
  \item Interpretation of simply typed $\lambda$-calculus\\
    Using ideas from heredetary substitutions\\
    Still need to check equations.
  \item Functoriality \\
    Need to interpret using heredetary higher functors\\
    In progress
  \item Morphisms ?\\
    Seems to work for |Cont₂|, generalize?
  \item Initial algebras, terminal coalgebras
   \begin{align*}
      \mu & : |HCont (A ⇒ A) ⇒ A|\\
      \nu  & : |HCont (A ⇒ A) ⇒ A|
    \end{align*}        
    Some issues (restrict universe?)
  \item Translation from TLCA01\\
    sketch on paper\\
    proof?    
  \end{itemize}
  
\end{frame}

\begin{frame}{Heredetary functors}

  \begin{code}
record Cat (Obj : Set) : Set

record Func (C : Cat X)(D : Cat Y)(F : X → Y) : Set

⟦_⟧F : (A : Ty) → ⟦ A ⟧T → Set
⟦_⟧C : (A : Ty) → Cat (Σ ⟦ A ⟧T ⟦ A ⟧F)

⟦ set ⟧F X = ⊤
⟦ A ⇒ B ⟧F H =
  Σ[ HH ∈ ((F : ⟦ A ⟧T) → ⟦ A ⟧F F → ⟦ B ⟧F (H F)) ]
         Func ⟦ A ⟧C ⟦ B ⟧C (λ (F , FF) → H F , HH F FF)
  \end{code}
  
\end{frame}

\begin{frame}
  \frametitle{Example for $\mu$}

  | H F X = 1 + X × F (F X)|\\

  construct |μ H|
  
  \begin{code}
data S : Set
P : S → Set

data S where
  s⊥ : S
  node : (s : S) → (P s → S) → S

P s⊥ = ⊥
P (node s f) = Maybe (Σ[ p ∈ P s ] (P (f p)))
  \end{code}

\end{frame}

\begin{frame}
  |H F X = X × F (F X)|\\
  construct |nu H| (we know it is |1 ◁ BT|)

  \frametitle{Example for $\nu$}
  \begin{code}
record S : Set
data P : S → Set

record S where
  coinductive
  field
    s : S
    f : P s → S

data P where
  hd : (sf : S) → P sf
  tl : (sf : S)( p : P (S.s sf))(q : P (S.f sf p)) → P sf
\end{code}

\textbf{Problem} : not strictly positive!
\end{frame}


\end{document}
