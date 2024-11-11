\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{notes}[2024 Lecture notes class]

\LoadClass[a5paper,12pt,DIV=calc,oneside,parskip=half]{scrreprt}


\RequirePackage[a5paper,margin=1.2cm,footskip=0cm,headsep=0.2cm]{geometry}
\RequirePackage[utf8]{inputenc}
\RequirePackage{textcomp}
\RequirePackage[hyperindex]{hyperref}
\RequirePackage[french]{babel}
\RequirePackage[framemethod=TikZ]{mdframed}
\RequirePackage{amsfonts,amsmath,amsthm}
\RequirePackage{enumerate}
\RequirePackage{graphicx} % importing images
\RequirePackage{thmtools} % just useful macros for theorems
\RequirePackage{minitoc}  % mini table of contents
\RequirePackage{enumitem} % change enum color
\RequirePackage{stmaryrd} % for \bigsqcap
\RequirePackage{bold-extra}
\RequirePackage{slantsc}
\RequirePackage{mleftright} % scale sets like { BIG THING HERE |  }
\RequirePackage{mathtools}
\RequirePackage{tikz}
\usetikzlibrary{automata, positioning, arrows}
\RequirePackage{svg}
\RequirePackage{adjustbox}
\RequirePackage{tikz-cd}
\RequirePackage{fontspec}
\RequirePackage{tablefootnote}

\newcommand\removefootnoteinside[1]{
  \AfterEndEnvironment{#1}{%
   \tfn@tablefootnoteprintout% 
   \gdef\tfn@fnt{0}% 
  }
}

\let\footnote\tablefootnote

\RequirePackage{array}
\RequirePackage{ebproof}
\RequirePackage{BOONDOX-calo}
\ebproofset{right label template=$\inserttext$, left label template=\tiny$\inserttext$, center=false}


\RequirePackage{dsfont}
\RequirePackage{algorithm}
\RequirePackage[rightComments=false,beginComment=$\qquad\triangleright$~]{algpseudocodex}
\RequirePackage{listings}

\RequirePackage{accents}
\newcommand\ubar[1]{\underaccent{\bar}{#1}}

\lstset{
  basicstyle=\ttfamily,
  captionpos=b,
  escapeinside={@}{@},
  mathescape=true
}

\RequirePackage{fancyhdr}
\pagestyle{fancy}
\renewcommand{\headrule}{}

\fancypagestyle{plain}{
  \fancyhead{}
  \fancyfoot{\itshape\hfill--\hspace{0.5em}\thepage/\pageref*{LastPage}\hspace{0.5em}--\hfill}
}

\fancyhead{}
\fancyhead[R]{\@title}
\fancyhead[L]{Hugo \textsc{Salou} -- \textit{\textsc{l3 ens lyon}}}
\fancyfoot{\itshape\hfill--\hspace{0.5em}\thepage/\pageref*{LastPage}\hspace{0.5em}--\hfill}

\RequirePackage[dvipsnames]{xcolor}
\definecolor{blue}{HTML}{5aa9e6}
\colorlet{deeppurple}{DarkOrchid}
\colorlet{deepgreen}{ForestGreen!70!black}
\colorlet{deepblue}{NavyBlue!70!black}
\colorlet{deepred}{RawSienna!70!black}
\colorlet{nicered}{BrickRed!70!white}


\RequirePackage[autostyle, style=french]{csquotes}
\MakeOuterQuote{"}

\newcommand\separatorBlock{
  \raisebox{-0.2em}{
    \tikz{ \draw[deepblue,ultra thick, line cap=round] (0,0) -- (0,1em); }
  }
}

\RequirePackage{caption}
\DeclareCaptionLabelFormat{labelformat}{\textsc{\textbf{#1~#2}}\separatorBlock}
\captionsetup{labelformat=labelformat,labelsep=none,textfont=sl}

\renewcommand\lstlistingname{Code}

\mdfsetup{skipabove=1em,skipbelow=0em}

\theoremstyle{definition}

\declaretheoremstyle[
    headfont=\bfseries\sffamily\color{deepgreen}, bodyfont=\normalfont,
    mdframed={
        linewidth=2pt,
        rightline=false, topline=false, bottomline=false,
        linecolor=ForestGreen, backgroundcolor=ForestGreen!5,
    },
    numberwithin=section,
]{thmgreenbox}

\declaretheoremstyle[
    headfont=\bfseries\sffamily\color{deepblue}, bodyfont=\normalfont,
    mdframed={
        linewidth=2pt,
        rightline=false, topline=false, bottomline=false,
        linecolor=NavyBlue, backgroundcolor=NavyBlue!5,
    },
    numberwithin=section,
]{thmbluebox}

\declaretheoremstyle[
    headfont=\bfseries\sffamily\color{deepblue}, bodyfont=\normalfont,
    mdframed={
        linewidth=2pt,
        rightline=false, topline=false, bottomline=false,
        linecolor=NavyBlue,
    },
    numberwithin=section,
]{thmblueline}

\declaretheoremstyle[
    headfont=\bfseries\sffamily\color{deepred}, bodyfont=\normalfont,
    mdframed={
        linewidth=2pt,
        rightline=false, topline=false, bottomline=false,
        linecolor=RawSienna, backgroundcolor=RawSienna!5,
    },
    numberwithin=section,
]{thmredbox}

\declaretheoremstyle[
    headfont=\bfseries\sffamily\color{deepred}, bodyfont=\normalfont,
    numbered=no,
    mdframed={
        linewidth=2pt,
        rightline=false, topline=false, bottomline=false,
        linecolor=RawSienna, backgroundcolor=RawSienna!1,
    },
    numberwithin=section,
    qed=\qedsymbol
]{thmproofbox}

\declaretheoremstyle[
    headfont=\bfseries\sffamily\color{deepblue}, bodyfont=\normalfont,
    numbered=no,
    mdframed={
        linewidth=2pt,
        rightline=false, topline=false, bottomline=false,
        linecolor=NavyBlue, backgroundcolor=NavyBlue!1,
    },
    numberwithin=section,
]{thmexplanationbox}

\newcommand\defineMarkerColor[2]{
  \AtBeginEnvironment{#1}{
    \setlist[enumerate]{font={\bfseries\color{#2}}}
    %\renewcommand{\labelitemi}{\color{#2}‣} % IF FONT SUPPORTS UNICODE TRIANGLE ARROW
    \renewcommand{\labelitemi}{\bfseries\color{#2}$\triangleright$} % OTHERWISE USE MATH TRIANGLE ARROW
    \renewcommand{\labelitemii}{\bfseries\color{#2}–}
    \renewcommand{\labelitemiii}{\bfseries\color{#2}•}
  }
}

\declaretheorem[style=thmgreenbox, name=Définition]{defn} \defineMarkerColor{defn}{deepgreen} \removefootnoteinside{defn}
\declaretheorem[style=thmbluebox, name=Exemple]{exm}      \defineMarkerColor{exm}{deepblue}   \removefootnoteinside{exm}
\declaretheorem[style=thmredbox, name=Proposition]{prop}  \defineMarkerColor{prop}{deepred}   \removefootnoteinside{prop}
\declaretheorem[style=thmredbox, name=Théorème]{thm}      \defineMarkerColor{thm}{deepred}    \removefootnoteinside{thm}
\declaretheorem[style=thmredbox, name=Lemme]{lem}         \defineMarkerColor{lem}{deepred}    \removefootnoteinside{lem}
\declaretheorem[style=thmredbox, name=Corollaire]{crlr}   \defineMarkerColor{crlr}{deepred}   \removefootnoteinside{crlr}
\declaretheorem[style=thmblueline, name=Remarque]{rmk}    \defineMarkerColor{rmk}{deepblue}   \removefootnoteinside{rmk}
\declaretheorem[style=thmblueline, name=Note]{note}       \defineMarkerColor{note}{deepblue}  \removefootnoteinside{note}

\declaretheorem[style=thmbluebox, name=Question]{ques}    \defineMarkerColor{ques}{deepblue}  \removefootnoteinside{ques}

\declaretheorem[style=thmexplanationbox, name=Réponse]{replacementrep}
\newenvironment{rep}[1][\proofname]{\vspace{-12pt}\begin{replacementrep}}{\end{replacementrep}}\defineMarkerColor{rep}{deepblue}  \removefootnoteinside{rep}

\declaretheorem[style=thmproofbox, name=Preuve]{replacementproof}
\newenvironment{prv}[1][\proofname]{\vspace{-12pt}\begin{replacementproof}}{\end{replacementproof}} \removefootnoteinside{prv} \defineMarkerColor{prv}{deepred}

\newtheorem*{nota}{Notation}

\RequirePackage[fontsize=12pt]{fontsize}
\AtBeginDocument{\setlength{\parindent}{0cm}\emergencystretch 1em}

\newcommand\redQuestionBox{
  \tikz[baseline]{
    \node[rectangle,fill=nicered,anchor=base,rounded corners=2pt] (A) {\color{white}\textsf{\textbf{?}}\ensuremath{\,}};
  }
}

\AtBeginDocument{
  \setlist[enumerate]{font={\bfseries\color{deepblue}}}
  %\renewcommand{\labelitemi}{\bfseries\color{deepblue}‣} % IF FONT SUPPORTS UNICODE TRIANGLE ARROW
  \renewcommand{\labelitemi}{\bfseries\color{deepblue}$\triangleright$} % OTHERWISE USE MATH TRIANGLE ARROW
  \renewcommand{\labelitemii}{\bfseries\color{deepblue}–}
  \renewcommand{\labelitemiii}{\bfseries\color{deepblue}•}
}

\newcommand\vertical[1]{
  \rotatebox[origin=c]{270}{\ensuremath{#1}}
}

\RequirePackage[makeroom, thicklines]{cancel}
\renewcommand{\CancelColor}{\color{nicered}}

\RequirePackage[explicit]{titlesec}
\titleformat{\section}{\fontsize{16}{18}\sffamily\bfseries}{\thesection}{16pt}{#1}
\titleformat{\subsection}{\fontsize{14}{16}\sffamily\bfseries}{\thesubsection}{14pt}{#1}
\titleformat{\subsubsection}{\fontsize{12}{14}\sffamily\large\bfseries}{\thesubsubsection}{12pt}{#1}

\titlespacing*{\section}{0pt}{5pt}{5pt}
\titlespacing*{\subsection}{0pt}{5pt}{5pt}
\titlespacing*{\subsubsection}{0pt}{5pt}{5pt}

\AtBeginDocument{\renewcommand\ldots{\ensuremath{\mathinner{\ldotp\ldotp\ldotp}}}}

\RequirePackage{lastpage}
\RequirePackage{hyperref}
\hypersetup{
    colorlinks,
    citecolor=black,
    filecolor=black,
    linkcolor=deepblue,
    urlcolor=blue
}

\renewcommand\mtifont{\large\sffamily\bfseries\itshape}
\renewcommand\mtctitle{Sommaire.}

\renewcommand\maketitle{
  \begin{titlepage}
    ~
    \vfill
    \vfill
    \begin{center}
      \Huge{\sffamily\bfseries \@title}

      \vspace{2cm}

      \large{
        \slshape
        \@author
      }

      \vfill

      \includegraphics[width=5cm]{/Users/hugos29/Documents/ecole/ens.pdf}

      \vfill

      \textit{\@date}
    \end{center}
    ~\\~
  \end{titlepage}
}


\lstdefinelanguage{Coq}{ 
    % Anything betweeen $ becomes LaTeX math mode
    mathescape=true,
    % Comments may or not include Latex commands
    texcl=false, 
    % Vernacular commands
    morekeywords=[1]{Section, Module, End, Require, Import, Export,
        Variable, Variables, Parameter, Parameters, Axiom, Hypothesis,
        Hypotheses, Notation, Local, Tactic, Reserved, Scope, Open, Close,
        Bind, Delimit, Definition, Let, Ltac, Fixpoint, CoFixpoint, Add,
        Morphism, Relation, Implicit, Arguments, Unset, Contextual,
        Strict, Prenex, Implicits, Inductive, CoInductive, Record,
        Structure, Canonical, Coercion, Context, Class, Global, Instance,
        Program, Infix, Theorem, Lemma, Corollary, Proposition, Fact,
        Remark, Example, Proof, Goal, Save, Qed, Defined, Hint, Resolve,
        Rewrite, View, Search, Show, Print, Printing, All, Eval, Check,
        Projections, inside, outside, Def},
    % Gallina
    morekeywords=[2]{forall, exists, exists2, fun, fix, cofix, struct,
        match, with, end, as, in, return, let, if, is, then, else, for, of,
        nosimpl, when},
    % Sorts
    morekeywords=[3]{Type, Prop, Set, true, false, option},
    % Various tactics, some are std Coq subsumed by ssr, for the manual purpose
    morekeywords=[4]{pose, set, move, case, elim, apply, clear, hnf,
        intro, intros, generalize, rename, pattern, after, destruct,
        induction, using, refine, inversion, injection, rewrite, congr,
        unlock, compute, ring, field, fourier, replace, fold, unfold,
        change, cutrewrite, simpl, have, suff, wlog, suffices, without,
        loss, nat_norm, assert, cut, trivial, revert, bool_congr, nat_congr,
        symmetry, transitivity, auto, split, left, right, autorewrite},
    % Terminators
    morekeywords=[5]{by, done, exact, reflexivity, tauto, romega, omega,
        assumption, solve, contradiction, discriminate},
    % Control
    morekeywords=[6]{do, last, first, try, idtac, repeat},
    % Comments delimiters, we do turn this off for the manual
    morecomment=[s]{(*}{*)},
    % Spaces are not displayed as a special character
    showstringspaces=false,
    % String delimiters
    morestring=[b]",
    morestring=[d]",
    % Size of tabulations
    tabsize=3,
    % Enables ASCII chars 128 to 255
    extendedchars=false,
    % Case sensitivity
    sensitive=true,
    % Automatic breaking of long lines
    breaklines=false,
    % Position of captions is bottom
    captionpos=b,
    % flexible columns
    columns=[l]flexible,
    % Style for (listings') identifiers
    identifierstyle={\ttfamily\color{Black}},
    % Style for declaration keywords
    keywordstyle=[1]{\ttfamily\color{Purple}},
    % Style for gallina keywords
    keywordstyle=[2]{\ttfamily\color{ForestGreen}},
    % Style for sorts keywords
    keywordstyle=[3]{\ttfamily\color{Turquoise}},
    % Style for tactics keywords
    keywordstyle=[4]{\ttfamily\color{Turquoise}},
    % Style for terminators keywords
    keywordstyle=[5]{\ttfamily\color{WildStrawberry}},
    %Style for iterators
    %keywordstyle=[6]{\ttfamily\color{dkpink}},
    % Style for strings
    stringstyle=\ttfamily,
    % Style for comments
    commentstyle={\ttfamily\color{ForestGreen}},
    %moredelim=**[is][\ttfamily\color{red}]{/&}{&/},
    literate=
    {\\forall}{{\color{ForestGreen}{$\forall\;$}}}1
    {\\exists}{{$\exists\;$}}1
    {<-}{{$\leftarrow\;$}}1
    {=>}{{$\Rightarrow\;$}}1
    {==}{{\code{==}\;}}1
    {==>}{{\code{==>}\;}}1
    %    {:>}{{\code{:>}\;}}1
    {->}{{$\rightarrow\;$}}1
    {<->}{{$\leftrightarrow\;$}}1
    {<==}{{$\leq\;$}}1
    {\#}{{$^\star$}}1 
    {\\o}{{$\circ\;$}}1 
    {\@}{{$\cdot$}}1 
    {\/\\}{{$\wedge\;$}}1
    {\\\/}{{$\vee\;$}}1
    {++}{{\code{++}}}1
    {~}{{$\sim$}}1
    {\@\@}{{$@$}}1
    {\\mapsto}{{$\mapsto\;$}}1
    {\\hline}{{\rule{\linewidth}{0.5pt}}}1
    %
}[keywords,comments,strings]

\newfontface\unshape[]{Latin Modern Roman Unslanted} 
\newcommand\textun[1]{{\unshape #1}}
