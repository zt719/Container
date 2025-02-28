\documentclass{easychair}
%include lhs2TeX.fmt
%include agda.fmt
%include lib.fmt
\usepackage{amssymb}

% use this if you have a long article and want to create an index
% \usepackage{makeidx}

% In order to save space or manage large tables or figures in a
% landcape-like text, you can use the rotating and pdflscape
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
  Zhili Tian
}

\institute{
  School of Computer Science, University of Nottingham, UK\\
  \email{\{psztxa,psx???\}@@nottingham.ac.uk}
}

%  \authorrunning{} has to be set for the shorter version of the authors' names;
% otherwise a warning will be rendered in the running heads. When processed by
% EasyChair, this command is mandatory: a document without \authorrunning
% will be rejected by EasyChair

\authorrunning{Altenkirch, Tian}

% \titlerunning{} has to be set to either the main title or its shorter
% version for the running heads. When processed by
% EasyChair, this command is mandatory: a document without \titlerunning
% will be rejected by EasyChair
\titlerunning{Containers in Higher Kinds}

\begin{document}

\maketitle
Strictly positive types can be represented as containers, that is 
|S : Set| and a family of positions |P : S → Set| giving rise to a
functor |S ◁ P : Set ⇒ Set| given by |(S ◁ P) X = Σ s : S . P s → X|.
Every container has an inital algebra (The W-type) and a terminal
coalgebra (The M-type). However, there are types which don't fit into
this scheme, an example is the type |Bush| which can be defined
coinductively :
\begin{code}
record Bush (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Bush (Bush A)
\end{code}
This type is isomorphic to the type of functions of binary trees, that
is |(BT → A) ≅ Bush A| where |BT| is defined inductively as the
initial algebra of |F X = 1 ⊎ X × X|, see \cite{repr-of-terminal}.

Hence we want to define a notion of containers in higher kinds which
model strictly positive functors like the functor giving rise to
|Bush| which is
\begin{code}
B : (Set → Set) → Set → Set
B F X = X × F (F X)
\end{code}

We define a notion of higher container |HCont : Ty → Set| where |Ty|
are just the types of simply typed $\lambda$-calculus with one base
type |set|. |HCont is just a special case of |HCont-NF : Con → Ty →
Set| where |Con| are the contexts of simply typed $\lambda$-calculus
|HCont A = HCont-NF ∙ A|. We also use |Var : Con → Ty → Set| for the
typed de Bruijn variables|

The definition of |HCont-NF| is straightforward:
\begin{code}
data HCont-NF where
  lam : HCont-NF (Γ ▹ A) B → HCont-NF Γ (A ⇒ B)
  ne  : HCont-NE Γ → HCont-NF Γ set
\end{code}
This is defined mutually with |HCont-NE : Con → Set| which represent
the type expressions in a given context, and also |HCont-SP : Con → Ty
→ Set| which is interpreted as the list of |HCont-NF| for the spine,
i.e. the iterated domains of a given type (E.g. the spine of |A ⇒ B ⇒
Set| is the context |• ▷ A ▷ B|.
\begin{code}
record HCont-NE Γ where
  inductive
  field
    S : Var Γ A → Set
    P : {x : Var Γ A} (s : S x) → Set
    R : {x : Var Γ A} {s : S x} (p : P s) → HCont-SP Γ A

data HCont-SP where
  ε : HCont-SP Γ set
  _,_ : HCont-NF Γ A → HCont-SP Γ B → HCont-SP Γ (A ⇒ B)
\end{code}
In the example we define an element of
|HCont (set ⇒ set) ⇒  (set ⇒ set)| using |lam| twice reducing it to
|HContNE Γ₀| with |Γ₀ = ∙ ▹ set ⇒ set ▹ set|. Since there are no sums
involved |S| is always |⊤|. We have two elements of |Var Γ A| in both
cases |P x = ⊤| since there is exactly one top-level occurence. In the
first case with |A = set| there is no recursion since the domain
context s empty, while in the second one we need to model
|B' F X = F (F X)| which proceeds recursively.

We can define
\begin{code}
⟦_⟧set : (DD : HCont-Set Γ)(γ : ⟦ Γ ⟧C) → Set
⟦_⟧ne : HCont-NE Γ Δ → ⟦ Γ ⟧C → ⟦ Δ ⟧C
⟦_⟧nf : HCont-NF Γ A → ⟦ Γ ⟧C → ⟦ A ⟧T
⟦_⟧H : HCont A → ⟦ A ⟧T
⟦ C ⟧H = ⟦ C ⟧nf tt
\end{code}
where |⟦_⟧T : Ty → Set₁| and |⟦_⟧C : Con → Set₁| are the interpretation
of types in the intended model.

we have just started our investigation, and hope to be able to extend
the standard results of containers to these higher kinded
containers. In particular we would like to show
\begin{itemize}
\item that higher containers give rise to higher heredetary functors,
 
\item that higher containers for a model of simply typed
  $\lambda$-calculus,
  
\item Provide a notion of higher container morphisms which are
  complete,

\item Construct initial algebras and terminal coalgebras of
  endo-containers,

\item reinterpret and extend the results from \cite{repr-of-terminal}.
 
\end{itemize}

\section*{Acknowledgements}
\label{sec:acknowledgements}

This development is based on discussions the first author had with
H{\aa}kan Gylterud.


\bibliographystyle{plain}
%\bibliographystyle{alpha}
%\bibliographystyle{unsrt}
%\bibliographystyle{abbrv}
\bibliography{references}

%------------------------------------------------------------------------------

\end{document}
