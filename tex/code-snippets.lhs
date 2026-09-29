%include polycode.fmt
%include spacing.fmt
%include lineno.fmt

%format b1
%format b2
%format b3
%format b4

%format c1
%format c2
%format c3
%format c4

%format P1
%format P2
%format P3
%format P4

%format Si = "\Varid{S}_{\Varid{i}}"
%format Sj = "\Varid{S}_{\Varid{j}}"

%format alpha  = "\alpha "
%format lambda = "\lambda "
%format sigma  = "\sigma "

%format . = "."
%format ; = "\mathop{;}"
%format ~ = ";"
%format * = "\mathord{*}"
%format ! = "\mathord{!}"
%format || = "\mathop{\|}"
%format ... = "\dots"
%format forall a = "\forall " a
%format par = "\mathrel{\|}"
%format ox = "\otimes "

%format ell  = "\ell "
%format elli = "\ell_i "
%format ellj = "\ell_j "

%subst keyword a = "\CodeKw{" a "}"
%format send    = "\CodeOp{send}"
%format recv    = "\CodeOp{recv}"
%format select  = "\CodeOp{select}"
%format branch  = "\CodeOp{branch}"
%format lsplit  = "\CodeOp{lsplit}"
%format rsplit  = "\CodeOp{rsplit}"
%format drop    = "\CodeOp{drop}"
%format acquire = "\CodeOp{acquire}"
%format fork    = "\CodeOp{fork}"
%format close   = "\CodeOp{close}"
%format wait    = "\CodeOp{wait}"
%format Skip    = "\CodeTy{Skip}"
%format Drop    = "\CodeTy{Drop}"
%format Acq     = "\CodeTy{Acq}"
%format Close   = "\CodeTy{Close}"
%format Wait    = "\CodeTy{Wait}"
%format Unit    = "\CodeTy{Unit}"

%format (lab (x)) = "\CodeLbl{" x "}"
%format (ref a) = "\mathord{\&\mkern-1mu}" a
%format nu (x) (y) = "\boldsymbol{\nu}[\mkern1mu\relax " x "\mkern1mu][\mkern1mu\relax " y "\mkern1mu]"

%format (brOut (x)) = "\oplus\{\mkern1mu\relax " x "\mkern1mu\}"
%format (brIn (x)) = "\&\{\mkern1mu\relax " x "\mkern1mu\}"
%format (variant (x)) = "\langle\mkern1.5mu\relax " x "\mkern1.5mu\rangle "

\newcommand\ApiOld{%
\begin{code}
send    : forall alpha sigma. alpha -> !alpha;sigma  -> sigma
recv    : forall alpha sigma. alpha -> ?alpha;sigma  -> alpha ox sigma
select ellj  : brOut (elli : Si) -> Sj
branch       : brIn (elli : Si) -> variant (elli : Si)
\end{code}
}

\newcommand\ApiNew{{%
\BorrowCodeStyle
\begin{code}
send    : forall alpha. alpha -> !alpha  -> Unit
recv    : forall alpha. alpha -> ?alpha  -> alpha
select ellj  : brOut (elli : Si) -> Sj
branch       : brIn (elli : Si) -> variant (elli : Si)
\end{code}
}}

\newcommand\HtmlProtocolDefn{{%
\BorrowCodeStyle
\begin{code}
type HtmlChan   = brOut (lab Text : !String, ^^ lab Elem : !String;ChildChan)
type ChildChan  = brOut (lab Done : Skip, ^^ lab Child : HtmlChan;ChildChan)
\end{code}
}}

\newcommand\CodeSendTree{%
\begin{code}
sendTree : Tree -> forall sigma. TreeChan;sigma -> sigma
sendTree Leaf          c = select Leaf c
sendTree (Node x l r)  c =
  let c1 = select Node c   in   {- |c1 : !Int;TreeChan;TreeChan;sigma| -}
  let c2 = send x c1       in   {- |c2 : TreeChan;TreeChan;sigma| -}         {-"\label{ln:sendTree/c2-def}"-}
  let c3 = sendTree l c2   in   {- |c3 : TreeChan;sigma| -}                  {-"\label{ln:sendTree/c2-use}"-}
  let c4 = sendTree r c3   in   {- |c4 : sigma| -}
  c4
\end{code}
}

\newcommand\CodeSendTreeB{%
\begin{code}
sendTreeB : Tree -> TreeChan -> Skip
sendTreeB Leaf          c = select Leaf c
sendTreeB (Node x l r)  c =
  let c = select Node c in   {- |c : !Int;TreeChan;TreeChan| -}
  send x (ref c) ~           {- |c : TreeChan;TreeChan| -}
  sendTreeB l (ref c) ~      {- |c : TreeChan| -}
  sendTreeB r (ref c)        {- |c : Skip| -}
\end{code}
}

\newcommand\CodeRenderExample{{%
\SaveColumns{renderExample}%
\begin{code}
renderUser : User -> HtmlChan;Close -> Unit
renderUser user c =
  let c = select Elem c in
  send "div" (ref c) ~
  let c = select Child c in
  fork (lambda ^ () -> renderProf user (ref c)) ~  {- |c : Acq;ChildChan;Close| -}   {-"\label{ln:renderExample/transBegin}"-}
  let msgs = getMessages user in
  renderRest msgs (acquire c)                                                        {-"\label{ln:renderExample/transEnd}"-}

renderRest : Messages -> ChildChan;Close -> Unit
renderRest msgs c =
  let c = select Child c in
  renderMsgArea msgs (ref c) ~
  close (select Done c)

renderProf : User -> HtmlChan;Drop -> Unit
renderProf user c = ^^ ... ^^ drop c
\end{code}
}}

\newcommand\CodeRenderExampleSnippet{%
\RestoreColumns{renderExample}%
\begin{code}
  fork (lambda ^ () -> renderProf user (ref c)) ~  {- |c : Acq;ChildChan;Close| -}
  let msgs = getMessages user in
  renderRest msgs (acquire c)
\end{code}
}

\newcommand\CodeRenderExampleSnippetTrans{{%
\RestoreColumns{renderExample}%
\begin{code}
                                                   {- |c : HtmlChan;ChildChan;Close| -}
  let c1,c2 = rsplit c in                          {- |c1 : HtmlChan;Drop| -}
                                                   {- |c2 : Acq;ChildChan;Close| -}
  fork (lambda ^ () -> renderProf user c1) ~
  let msgs = getMessages user in
  renderRest msgs (acquire c2)
\end{code}
}}

\newcommand\CodeRenderRest{
\begin{code}
renderRest msgs c =
  let c = select Child c in
  let c1,c2 = lsplit c in
  renderMsgArea msgs c1 ~
  close (select Done c2)
\end{code}
}

\newcommand\LocalSplitReduction{{%
\setlength{\abovedisplayskip}{0pt}%
\setlength{\belowdisplayskip}{0pt}%
\begingroup
\SaveColumns{localSplit}%
\begin{code}
nu c b1 in
  (P1  par  let c = select Child c in
            let c1,c2 = lsplit c in
            renderMsgArea msgs c1 ~
            close (select Done c2))
\end{code}
\endgroup
\RestoreColumns{localSplit}%
\ExampleReduction*
\begin{code}
nu c b2 in
  (P2  par  let c1,c2 = lsplit c in
            renderMsgArea msgs c1 ~
            close (select Done c2))
\end{code}
\ExampleReduction
\begin{code}
nu (c1 ^ c2) b3 in
  (P3  par  renderMsgArea msgs c1 ~
            close (select Done c2))
\end{code}
\ExampleReduction*
\begin{code}
nu c2 b3 in
  (P3  par  close (select Done c2))
\end{code}
\ExampleReduction
\begin{code}
nu c2 d in
  (P4 ^ [wait d] par c2)
\end{code}
\ExampleReduction
\begin{code}
(P4 ^ [*] par ^^ *)
\end{code}
}}

\newcommand\RemoteSplitReduction{{%
\setlength{\abovedisplayskip}{0pt}%
\setlength{\belowdisplayskip}{0pt}%
\begin{code}
nu c (...) in
  let c1,c2 = rsplit c in
  fork (lambda ^ () -> renderProf user c1) ~
  let msgs = ... in
  renderRest msgs (acquire c2)
\end{code}
\ExampleReduction
\begin{code}
nu (c1||c2) (...) in
  fork (lambda ^ () -> renderProf user c1) ~
  let msgs = ... in
  renderRest msgs (acquire c2)
\end{code}
\ExampleReduction*
\begin{code}
nu (c1||c2) (...) in
  ( ^  drop c1 par
       renderRest msgs (acquire c2))
\end{code}
\ExampleReduction
\begin{code}
nu (||c2) (...) in
  renderRest msgs (acquire c2)
\end{code}
\ExampleReduction
\begin{code}
nu c2 (...) in
  renderRest msgs c2
\end{code}
}}
