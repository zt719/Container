\documentclass{easychair}
%include lhs2TeX.fmt
%include agda.fmt
%include lib.fmt
\usepackage{amssymb}

% use this if you have a long article and want to create an index
% \usepackage{makeidx}

% In order to save space or manage large tables or figures in a
% landscape-like text, you can use the rotating and pdflscape
% packages. Uncomment the desired from the below.
%
% \usepackage{rotating}
% \usepackage{pdflscape}

% Some of our commands for this guide.
%

%\makeindex

%% Front Matter
%%
% Regular title as in the article class.
%
\title{Containers in Higher Kinds}

% Authors are joined by \and. Their affiliations are given by \inst, which indexes
% into the list defined using \institute
%
\author{
  Thorsten Altenkirch \and
  H{\aa}kan Gylterud \and
  Zhili Tian
}

\institute{
  School of Computer Science, University of Nottingham, UK\\
  \email{\{psztxa,psxzt8\}@@nottingham.ac.uk}
}

%  \authorrunning{} has to be set for the shorter version of the authors' names;
% otherwise a warning will be rendered in the running heads. When processed by
% EasyChair, this command is mandatory: a document without \authorrunning
% will be rejected by EasyChair

\authorrunning{Altenkirch, Gylterud, Tian}

% \titlerunning{} has to be set to either the main title or its shorter
% version for the running heads. When processed by
% EasyChair, this command is mandatory: a document without \titlerunning
% will be rejected by EasyChair
\titlerunning{Containers in Higher Kinds}

\begin{document}

\maketitle

Strictly positive types can be represented as containers \cite{containers}, that is |S : Set| and a family of positions |P : S → Set| giving rise to a functor |⟦ S ◁ P ⟧ : Set ⇒ Set|. Every container has an initial algebra (The W-type) and a terminal coalgebra (The M-type). However, there are types which don't fit into this scheme, an example is the type |Bush| which can be defined:

\begin{code}
data Bush (A : Set) : Set where
  [] : Bush A
  _::_ : A → Bush (Bush A) → Bush A
\end{code}

Although |Bush A| is not a W-type, the type constructor |Bush| itself arises as the initial algebra of a functor on a functor category\cite{bird1998nested, bird1999generalised}. This motivates the development of a notion of containers at higher kinds capable of modelling strictly positive functors over containers.

\section*{Second-Order Containers}

We introduce a recursive syntax |2Cont| by extending the |Cont| with a family |PF : S → Set| of positions of |F| and a continuation |RF : (s : S) → PF s → 2Cont|. Those give rise to an endofunctor |⟦ S ◁ PX ◁ PF ◁ RF ⟧ : Cont ⇒ Cont|. 

In the |Bush| example, the higher-order signature of such is given by |H F X = 1 + X × F (F X)|. There is a sum involved and therefore two shapes (|S = Bool|). The left shape is trivial with a constant, while in the right shape, there is one position of |X| (|PX true = ⊤|) and one position of |F| (|PF true = ⊤|). Finally, we need to model |H' F X = F X| which procceds recursively (|RF true tt = H'|).

We define a second-order least-fixpoint operator |2W : 2Cont → Cont| by inductive-recursion, thereby recovering |Bush| as the initial algebra of |H|. However, attempts to define a greatest fixpoint operator |2M : 2Cont → Cont| by coinductive-induction shows an non-positive issue.

\section*{Higher-Order Containers}

To continue the story of constructing strictly positive functor of functor categories, we define a notion of higher container |HCont : Ty → Set|, where |Ty| are just the types of simply typed $\lambda$-calculus with one base type |*| which represents |Set|. |HCont| is just a special case of
|Nf : Con → Ty → Set| where |Con| are the contexts of simply typed
$\lambda$-calculus |HCont A = Nf • A|. We also use |Var : Con → Ty → Set|
for the typed de Bruijn variables. For brevity, we do not present the full syntax. We remark that normal forms |Nf| are defined mutually with neutral terms and spines, following the standard presentation of normalization for simply typed $\lambda$-calculus\cite{keller2010normalization} .With this setting, it is easy to see that |Set ≅ HCont *|, |Cont ≅ HCont (* ⇒ *)| and |2Cont ≅ HCont ((* ⇒ *) ⇒ * ⇒ *)|. 

For the semantics, it seems there are two ways to go. A naive interpretation would be what we call hereditary functor, which is given by:

\begin{code}
record Cat (Obj : Set) : Set where
record Func (C : Cat X) (D : Cat Y) (F : X → Y) : Set
⟦_⟧F : (A : Ty) → ⟦ A ⟧T → Set
⟦_⟧C : (A : Ty) → Cat (Σ ⟦ A ⟧T ⟦ A ⟧F)

⟦ * ⟧F X = Lift ⊤
⟦ A ⇒ B ⟧F H =
  Σ[ HH ∈ ((F : ⟦ A ⟧T) → ⟦ A ⟧F F → ⟦ B ⟧F (H F)) ]
  Func ⟦ A ⟧C ⟦ B ⟧C (λ (F , FF) → H F , HH F FF)
\end{code}

where |⟦_⟧T : Ty → Set| and |⟦_⟧C : Con → Set| are the interpretation
of types and contexts in the intended model. However, there is an inconsistency with the model when constructing the general least-fixpoint. We construct a higher container as counterexample:

\begin{code}
C : HCont (((* ⇒ *) ⇒ *) ⇒ (* ⇒ *) ⇒ *)
C F G = G (F G)
\end{code}

If an external fixpoint operator |3W : HCont (((* ⇒ *) ⇒ *) ⇒ (* ⇒ *) ⇒ *) → HCont ((* ⇒ *) ⇒ *)| exists, applying it to |C| leads to an internal fixpoint operator |intW : HCont ((* ⇒ *) ⇒ *)|. In the semantics, |intW| takes least-fixpoint of any functor, but we know such thing does not exist. To fix this issue, we can add fixpoint operators (|μ and ν|) to our syntax and define an anlternative semantics. The new model interprets higher containers |HCont (A ⇒ B)| as strictly positive functors |HCont A ⇒ HCont B|. The external fixpoint |3W| now gives rise to external |W|. Notice that this is also consistent with our first-order and second-order semantics.

TODO : talk about coinductive definition

As a secondary contribution, we show higher containers are normalized $\lambda$-terms closed under arbitrary products and coproducts (maybe also under least-fixpoint and greatest-fixpoint). That is we can define a syntax of |Tm|:

\begin{code}
data Tm : Con → Ty → Set₁ where
  var : Var Γ A → Tm Γ A
  lam : Tm (Γ ▹ A) B → Tm Γ (A ⇒ B)
  app : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  Π : (I : Set) → (I → Tm Γ A) → Tm Γ A
  Σ : (I : Set) → (I → Tm Γ A) → Tm Γ A
\end{code}

together with a normalization function |nf : Tm Γ A → Nf Γ A|. Furthermore, we show |(Con, Tms, Ty, Tm)| is a model of STLC (simply-typed $\lambda$-calculus), where |Tms| is a list of |Tm|. Similarly, we also hope to prove that the normalized model |(Con, Nfs, Ty, Nf)| is also a STLC, where |Nfs| is a list of |Nf|.

\bibliographystyle{plain}
\bibliography{references}

%------------------------------------------------------------------------------

\end{document}
