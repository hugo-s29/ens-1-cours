\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{notes}[2024 Lecture notes class]

\LoadClass{article}


\RequirePackage[a5paper,margin=1.2cm,footskip=0cm,headsep=0.2cm]{geometry}
\RequirePackage[utf8]{inputenc}
\RequirePackage{textcomp}
\RequirePackage[hyperindex]{hyperref}
\RequirePackage[french]{babel}
\RequirePackage[framemethod=TikZ]{mdframed}
\RequirePackage{amsfonts,amsmath,amsthm,amssymb}
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
\usetikzlibrary {automata,positioning}
\RequirePackage{svg}
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


\RequirePackage{dsfont}
\RequirePackage{algorithm}
\RequirePackage[rightComments=false,beginComment=$\qquad\triangleright$~]{algpseudocodex}
\RequirePackage{listings}

\lstset{
  basicstyle=\ttfamily,
  captionpos=b,
  escapeinside={@}{@},
  mathescape=true
}

\RequirePackage[dvipsnames]{xcolor}
\definecolor{blue}{HTML}{5aa9e6}
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
    }
]{thmgreenbox}

\declaretheoremstyle[
    headfont=\bfseries\sffamily\color{deepblue}, bodyfont=\normalfont,
    mdframed={
        linewidth=2pt,
        rightline=false, topline=false, bottomline=false,
        linecolor=NavyBlue, backgroundcolor=NavyBlue!5,
    }
]{thmbluebox}

\declaretheoremstyle[
    headfont=\bfseries\sffamily\color{deepblue}, bodyfont=\normalfont,
    mdframed={
        linewidth=2pt,
        rightline=false, topline=false, bottomline=false,
        linecolor=NavyBlue,
    }
]{thmblueline}

\declaretheoremstyle[
    headfont=\bfseries\sffamily\color{deepred}, bodyfont=\normalfont,
    mdframed={
        linewidth=2pt,
        rightline=false, topline=false, bottomline=false,
        linecolor=RawSienna, backgroundcolor=RawSienna!5,
    }
]{thmredbox}

\declaretheoremstyle[
    headfont=\bfseries\sffamily\color{deepred}, bodyfont=\normalfont,
    numbered=no,
    mdframed={
        linewidth=2pt,
        rightline=false, topline=false, bottomline=false,
        linecolor=RawSienna, backgroundcolor=RawSienna!1,
    },
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
]{thmexplanationbox}

\newcommand\defineMarkerColor[2]{
  \AtBeginEnvironment{#1}{
    \setlist[enumerate]{font={\color{#2}}}
    %\renewcommand{\labelitemi}{\color{#2}‣} % IF FONT SUPPORTS UNICODE TRIANGLE ARROW
    \renewcommand{\labelitemi}{\color{#2}$\triangleright$} % OTHERWISE USE MATH TRIANGLE ARROW
    \renewcommand{\labelitemii}{\color{#2}–}
    \renewcommand{\labelitemiii}{\color{#2}•}
  }
}

\AtBeginDocument{
  \setlist[enumerate]{font={\color{deepblue}}}
  %\renewcommand{\labelitemi}{\color{deepblue}‣} % IF FONT SUPPORTS UNICODE TRIANGLE ARROW
  \renewcommand{\labelitemi}{\color{deepblue}$\triangleright$} % OTHERWISE USE MATH TRIANGLE ARROW
  \renewcommand{\labelitemii}{\color{deepblue}–}
  \renewcommand{\labelitemiii}{\color{deepblue}•}
}


\declaretheorem[style=thmgreenbox, name=Définition]{defn} \defineMarkerColor{defn}{deepgreen} \removefootnoteinside{defn}
\declaretheorem[style=thmbluebox, name=Exemple]{exm}      \defineMarkerColor{exm}{deepblue}   \removefootnoteinside{exm}
\declaretheorem[style=thmredbox, name=Proposition]{prop}  \defineMarkerColor{prop}{deepred}   \removefootnoteinside{prop}
\declaretheorem[style=thmredbox, name=Théorème]{thm}      \defineMarkerColor{thm}{deepred}    \removefootnoteinside{thm}
\declaretheorem[style=thmredbox, name=Lemme]{lem}         \defineMarkerColor{lem}{deepred}    \removefootnoteinside{lem}
\declaretheorem[style=thmredbox, name=Corollaire]{crlr}   \defineMarkerColor{crlr}{deepred}   \removefootnoteinside{crlr}
\declaretheorem[style=thmblueline, name=Remarque]{rmk}    \defineMarkerColor{rmk}{deepblue}   \removefootnoteinside{rmk}
\declaretheorem[style=thmblueline, name=Note]{note}       \defineMarkerColor{note}{deepblue}  \removefootnoteinside{note}

\declaretheorem[style=thmproofbox, name=Preuve]{replacementproof}
\newenvironment{prv}[1][\proofname]{\vspace{-12pt}\begin{replacementproof}}{\end{replacementproof}} \removefootnoteinside{prv}

\newtheorem*{nota}{Notation}

\RequirePackage[fontsize=12pt]{fontsize}
\AtBeginDocument{\setlength{\parindent}{0cm}\emergencystretch 1em}

\newcommand\redQuestionBox{
  \tikz[baseline]{
    \node[rectangle,fill=nicered,anchor=base,rounded corners=2pt] (A) {\color{white}\textsf{\textbf{?}}\ensuremath{\,}};
  }
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
