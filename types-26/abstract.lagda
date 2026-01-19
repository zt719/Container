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
  Thorsten Altenkirch\inst{1} \and
  H{\aa}kon Robbestad Gylterud\inst{2} \and
  Zhili Tian\inst{1}
}

\institute{
  $^{1}$School of Computer Science, University of Nottingham\\
  \email{\{psztxa,psxzt8\}@@nottingham.ac.uk}\\
  $^{2}$Department of Informatics, University of Bergen\\
  \email{hakon.gylterud@@uib.no}
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

Strictly positive types can be represented as containers \cite{containers},
that is |S : Set| and a family of positions |P : S → Set| giving rise to a
functor |⟦ S ◁ P ⟧ : Set ⇒ Set|. Every container has an initial algebra
(The W-type) and a terminal coalgebra (The M-type). However, there are
inductive/coinductive types which do not fit the scheme of W-types/M-types.
An example of such a type is the inductive type |Bush|, defined as follows:

\begin{code}
data Bush (A : Set) : Set where
  [] : Bush A
  _::_ : A → Bush (Bush A) → Bush A
\end{code}

Even though |Bush A| is not a W-type, the type constructor |Bush| itself arises
as the initial algebra of a functor on a functor category\cite{bird1998nested,
bird1999generalised}. This motivates the development of a notion of containers
at higher kinds (such as |(* ⇒ *) ⇒ (* ⇒ *)| or |(* ⇒ *) ⇒ *|) capable of modelling
strictly positive functors over containers.

\section*{Second-Order Containers}

We introduce a recursive syntax |Cont²| by extending the |Cont| with a family
|PF : S → Set| of positions of |F| and an inductive continuation |RF : (s : S) → PF s → Cont²|.
These, second order containers are of kind |(* ⇒ *) ⇒ (* ⇒ *)|. Hence, each of them gives rise
to an endofunctor |⟦ S ◁ PX ◁ PF ◁ RF ⟧ : Cont ⇒ Cont|. 

The |Bush| example can be specified using the following higher-order signature:
|H F X = 1 + X × F (F X)|. There is a sum involved and therefore two shapes
(|S = Bool|). The left shape is trivial with a constant, while in the right
shape, there is one position of |X| (|PX true = ⊤|) and one position of
|F| (|PF true = ⊤|). Finally, we need to model |H' F X = F X| which proceeds
recursively (|RF true tt = H'|).

We define a second-order least-fixpoint operator |W² : Cont² → Cont| by
induction-recursion, thereby recovering |Bush| as the initial algebra of
|H|. However, attempts to define a greatest fixpoint operator
|M² : Cont² → Cont| by coinduction-induction shows positivity issue.

\section*{Higher-Order Containers}

To continue the story of constructing strictly positive functors of functor
categories, we define a notion of higher container |HCont : Ty → Set|, where
|Ty| are just the types of simply typed $\lambda$-calculus with one base type
|*| which represents |Set|. |HCont| is just a special case of
|Nf : Con → Ty → Set| where |Con| are the contexts of simply typed
$\lambda$-calculus |HCont A = Nf • A|. We also use |Var : Con → Ty → Set|
for the typed de Bruijn variables. For brevity, we do not present the full
syntax. We remark that normal forms |Nf| are defined mutually with neutral terms
and spines, following the standard presentation of hereditary substitution for
simply typed $\lambda$-calculus\cite{keller2010normalization}. With this setting,
it is easy to see that |Set ≅ HCont *|, |Cont ≅ HCont (* ⇒ *)| and
|Cont² ≅ HCont ((* ⇒ *) ⇒ * ⇒ *)|. 

For the semantics, it seems there are two ways to go: A naive interpretation
using what we have called a hereditary functor, built iteratively on sets, and
a more principled semantics restricting the domain in each iteration to containers.
The naive interpretation is specified by:

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
of types and contexts in the intended model. However, using this semantics
we can shot that there is no third order fixed-point operators, |W³|.
Consider the following higher order container:

\begin{code}
C : HCont (((* ⇒ *) ⇒ *) ⇒ (* ⇒ *) ⇒ *)
C F G = G (F G)
\end{code}

If an external fixpoint operator |W³ : HCont (((* ⇒ *) ⇒ *) ⇒ (* ⇒ *) ⇒ *) → HCont ((* ⇒ *) ⇒ *)|
exists, applying it to |C| leads to an internal fixpoint operator |intW : HCont ((* ⇒ *) ⇒ *)|.
According to the semantics, |intW : (Set ⇒ Set) ⇒ Set| gives a least fixpoint of any functor, but we know such thing does not
exist.

One approach to fixing this problem, is to add fixpoint operators (|μ and ν|) to our syntax and define
an alternative semantics. The alternative we have in mind interprets higher containers |HCont (A ⇒ B)| as functors |HCont A ⇒ HCont B|. Applying the external fixpoint |W³| to |C| now gives rise to external
|extW : HCont ((* ⇒ *) ⇒ *)|, which its semantics corresponds to exactly the usual fixed-point operator |W : Cont ⇒ Set|.

Instead of adding the fixed point operators to the syntax explicitly, we could also add fixed-points
implicitly by passing to a coinductive syntax with infinite terms. The semantics would then
have to choose wether to interpret these as inductive or coinductive fixed points.

\section*{Higher containers as normalized $\lambda$-terms}

Furthermore, we show higher containers are normalized $\lambda$-terms
closed under arbitrary products and coproducts (maybe also under least-fixpoint and
greatest-fixpoint), together with a normalization function |nf : Tm Γ A → Nf Γ A|.

We also show |(Con, Tms, Ty, Tm)| is a model of simply-typed
$\lambda$-calculus (STLC), where |Tms| is a list of |Tm|. Similarly, we hope
to prove that the normalized model |(Con, Nfs, Ty, Nf)| is also a model of STLC, where
|Nfs| is a list of |Nf|.

\bibliographystyle{plain}
\bibliography{references}

%------------------------------------------------------------------------------

\end{document}
