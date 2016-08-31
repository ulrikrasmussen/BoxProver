{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE OverloadedStrings #-}
module RenderHtml where

import           Data.String
import           Data.List (intersperse)

import           Control.Monad
                 
import           Text.Blaze.Html5 (Html, (!))
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A
import qualified Data.Set as S

import           LinearProof
import           Syntax

metaKindSpan :: String -> Html
metaKindSpan = (H.span ! A.class_ "metakind") . fromString

metaQuantifierSpan :: String -> Html
metaQuantifierSpan = (H.span ! A.class_ "metaquantifier") . fromString

varSpan :: String -> Html
varSpan = (H.span ! A.class_ "var") . fromString

termIntroSpan :: String -> Html
termIntroSpan = (H.span ! A.class_ "termIntro") . fromString
          
parSpan :: String -> Html
parSpan = (H.span ! A.class_ "par") . fromString

opSpan :: String -> Html
opSpan = (H.span ! A.class_ "op") . fromString

predSpan :: String -> Html
predSpan = (H.span ! A.class_ "pred") . fromString

holeSpan :: Html -> Html
holeSpan = H.span ! A.class_ "hole"

cdots :: Html
cdots = H.span ! A.class_ "cdots" $ fromString "⋯"

render :: OpenLineProof -> Html
render l@(OpenLineProof hyps frags) = do
  let pclosed = H.p ! A.style "float: right;"
  if isClosedProof l then
     pclosed ! A.class_ "closed-indicator" $
       "Proof is closed!"
  else
     pclosed ! A.class_ "open-indicator" $
       "Proof contains holes and/or higher-order objects."
  let implicits = S.fromList [ x | b <- hyps, bindImplicit b, Just x <- [bindVar b] ]
  renderFrags implicits frags
  H.h2 $ fromString "Premise(s) and assumptions(s)"
  renderProofHypotheses hyps

parens :: Html -> Html
parens h = parSpan "(" >> h >> parSpan ")"

renderFrags :: S.Set VarName -> [ProofFragment] -> Html
renderFrags implicits frags =
  H.table ! A.class_ "boxproof" $ mapM_ (renderFrag 0 S.empty S.empty) frags
  where
    nboxcols = depth frags
    renderFrag d open close frag =
      let ocClass l = if S.member l open then "open" else
                        if S.member l close then "close" else
                          ""
          boxcols emptyLine rev l inner =
            forM_ ((if rev then reverse else id) [1 .. nboxcols]) $ \i ->
            let classes = unwords $ ["box"]
                                    ++ ["active" | or [i <= d && not (emptyLine && S.member l close)
                                                      ,i < d] ]
                                    ++ [ocClass l | or [i >= d && not (emptyLine || rev)
                                                       ,i > d && not emptyLine]]
            in H.td ! A.class_ (fromString classes) $ if i == d then inner else ""
          line l lineLabel varLabel concLabel refLabel = do
            H.tr $ do
              H.td ! A.class_ "line" $ fromString lineLabel
              boxcols False False l $ fromString varLabel
              H.td ! A.class_ (fromString $ unwords ["conc", ocClass l])
                $ concLabel
              H.td ! A.class_ (fromString $ unwords ["rule", ocClass l])
                $ refLabel
              boxcols False True l ""
            H.tr ! A.class_ "empty" $ do
              H.td ! A.class_ "line" $ " "
              boxcols True False l " "
              H.td ! A.class_ (fromString $ unwords ["conc"]) $ " "
              H.td ! A.class_ (fromString $ unwords ["rule"]) $ " "
              boxcols True True l " "
      in case frag of
         VarIntroduction l x -> line l (show l) x "" (renderReference implicits "var" [])
         Line l sq rule refs ->
           line l (show l) "" (renderSequent sq) (renderReference implicits rule refs)
         HoleLine l (ProofType bt) h _args
           | S.member h implicits ->
             line l (show l) "" (holeSpan $ renderSequent bt) (holeSpan $ fromString h)
           | otherwise -> line l (show l) "" (renderSequent bt) (fromString h)
         Box l1 l2 frags' ->
           let open' = S.insert l1 open
               close' = S.insert l2 close
            in mapM_ (renderFrag (d+1) open' close') frags'

renderReference :: S.Set VarName -> String -> [LineRef] -> Html
renderReference implicits rule refs = do
  let ruleTable = (map (\(x,y) -> (x, fromString y))
                  [ ("top_i", "⊤i"), ("con_i", "∧i"), ("con_e1", "∧e₁"), ("con_e2", "∧e₂")
                  , ("dis_i1", "∨i₁"), ("dis_i2", "∨i₂"), ("dis_e","∨e"), ("imp_i","→i")
                  , ("imp_e","→e"), ("neg_i","¬i"), ("neg_e","¬e"), ("bot_e","⊥e")
                  , ("all_i","∀i"), ("all_e","∀e"), ("exi_i","∃i"), ("exi_e","∃e")
                  , ("eq_i","=i"), ("eq_e","=e"), ("lem", "LEM"), ("nne", "¬¬e")
                  , ("mt", "MT"), ("nni", "¬¬i"), ("pbc", "PBC")
                  ]) ++ [("var", termIntroSpan "variable")]
  let renderLineRef r =
        case r of
        LineRefSingle l' -> fromString $ show l'
        LineRefMulti l1 l2 -> fromString $ concat [show l1, "-", show l2]
        LineRefHole h
           | S.member h implicits -> holeSpan $ fromString $ concat ["(",h,")"]
           | otherwise -> fromString $ concat ["(",h,")"]
  _ <- (maybe (fromString rule) id (lookup rule ruleTable))
  _ <- fromString " "
  sequence_ (intersperse (fromString ", ") $ map renderLineRef refs)

flag_renderAllHypotheses :: Bool
flag_renderAllHypotheses = False

-- Render a tabular representation of the full proof context, including implicit
-- hypotheses.
renderProofHypotheses :: [HypBinding] -> Html
renderProofHypotheses hyps =
  H.table ! A.class_ "hypotheses" $ mapM_ renderHyp $ filter isVisible hyps
  where
    isVisible (HypBinding _ implicit typ) =
      or [flag_renderAllHypotheses
         ,implicit
         ,isJudgment typ
         ]
    
    renderHyp (HypBinding mx implicit typ) = H.tr $ do
      H.td $ (if implicit then holeSpan else id) $ fromString $ maybe "" id mx
      H.td $ maybe "" (const " : ") mx
      H.td $ renderObjType typ
    renderObjType :: ObjType -> Html
    renderObjType (TermTy c@(Open hyps' TermConst))
        | all (isClosedTermTy . bindTy) hyps' =
            let arity = length hyps' in
            if arity == 0 then metaKindSpan "Constant" else
                metaKindSpan "Term" >> parens (fromString $ show arity)
        | otherwise = renderContextual (const (metaKindSpan "Term")) c
    renderObjType (PropTy c@(Open hyps' PropConst))
        | all (isClosedTermTy . bindTy) hyps' =
            let arity = length hyps' in
            if arity == 0 then metaKindSpan "Proposition" else
                metaKindSpan "Predicate" >> parens (fromString $ show arity)
        | otherwise = renderContextual (const (metaKindSpan "Proposition")) c
    renderObjType (RefTy c) =
        renderContextual
          (\(RefType bt) -> {-metaKindSpan "Ref to " >>-} (renderSequent bt))
          c
    renderObjType (SequentTy c) =
        renderContextual (const (metaKindSpan "Sequent")) c
    renderObjType (ProofTy c) =
        flip renderContextual c $
          \(ProofType bt) -> metaKindSpan "Proof of " >> (renderSequent bt)
    renderContextual :: (a -> Html) -> Open a -> Html
    renderContextual f (Open [] a) = f a
    renderContextual f (Open bindings a) = do
      f a
      H.div ! A.class_ "context-separator" $ "with premise(s) and assumption(s)"
      H.div ! A.class_ "context" $ renderProofHypotheses bindings

type Precedence = Int
data Fixity = FixPrefix | FixInfix Assoc | FixPostfix
  deriving (Eq)
data Assoc = AssocLeft | AssocRight | AssocNone
  deriving (Show, Eq)
data Position = PosLeft | PosRight
  deriving (Show, Eq)
type OpSpec = (Precedence, Fixity)
type CtxHtml = (OpSpec, Html)

par :: OpSpec -> Position -> CtxHtml -> Html
par (pprec, pfix) cpos ((cprec, cfix), s)
  = if not isUnambiguous then parens s else s
  where
    isUnambiguous =
      (cprec > pprec) || and [cprec == pprec, cfix == pfix, posCompatible]
    posCompatible =
      case cfix of
      FixInfix AssocLeft  -> cpos == PosLeft
      FixInfix AssocRight -> cpos == PosRight
      FixInfix AssocNone  -> False
      _                   -> True
      
showInfixOp :: OpSpec -> Html -> CtxHtml -> CtxHtml -> CtxHtml
showInfixOp spec op t1 t2 =
  (spec, par spec PosLeft t1 >> op >> par spec PosRight t2)

showPrefixOp :: OpSpec -> Html -> CtxHtml -> CtxHtml
showPrefixOp spec op t1 =
  (spec, op >> par spec PosRight t1)

showConst :: Html -> CtxHtml
showConst cnst = ((maxBound, FixPrefix), cnst)

renderFormula :: Formula -> Html
renderFormula phi = let (_, s) = go phi in s
  where
    go p =
      case p of
      Top -> showConst "⊤"
      Bot -> showConst "⊥"
      Conj p1 p2 -> showInfixOp (3, FixInfix AssocNone) (opSpan " ∧ ") (go p1) (go p2)
      Disj p1 p2 -> showInfixOp (3, FixInfix AssocNone) (opSpan " ∨ ") (go p1) (go p2)
      Imp p1 p2  -> showInfixOp (1, FixInfix AssocRight) (opSpan " → ") (go p1) (go p2)
      Neg p'     -> showPrefixOp (5, FixPrefix) (opSpan "¬") (go p')
      Pred q ts  -> showConst $ predSpan q >> objsListHtml ts
      Eq t1 t2   -> showConst $ renderTerm t1 >> predSpan " = " >> renderTerm t2
      All x phi' -> showPrefixOp (4, FixPrefix)
                                 (opSpan "∀" >> varSpan x >> fromString " ") (go phi')
      Exi x phi' -> showPrefixOp (4, FixPrefix)
                                 (opSpan "∃" >> varSpan x >> fromString " ") (go phi')

objsListHtml :: [Obj] -> Html
objsListHtml ts = appList (map renderObj ts)

-- Given a list [h1, ..., hn], renders nothing if n = 0 and otherwise renders
-- the sequence enclosed in parameters and separated by commas.
appList :: [Html] -> Html
appList [] = return ()
appList hs =
  parSpan "(" >> sequence_ (intersperse (fromString ", ") hs) >> parSpan ")"

renderObj :: Obj -> Html
renderObj o =
  case o of
  ObjTerm    (Open bs t)   -> lam bs >> renderTerm t
  ObjProp    (Open bs phi) -> lam bs >> renderFormula phi
  ObjRef     (Open bs ref) -> lam bs >> renderRef ref
  ObjSequent (Open bs sq)  -> lam bs >> renderSequent sq
  ObjProof   (Open bs _pt)  -> lam bs >> fromString "<proof term>"
  where
    lam [] = (return () :: Html)
    lam bs = do _ <- fromString "λ"
                let hs = map (fromString . maybe "_" id . bindVar) bs
                sequence_ $ intersperse (fromString ", ") hs
                fromString ". "

renderRef :: Ref -> Html
renderRef (RefApp x []) = varSpan x
renderRef (RefApp x args) = varSpan x >> objsListHtml args

renderTerm :: Term -> Html
renderTerm (Var x) = varSpan x
renderTerm (App f ts) = varSpan f >> objsListHtml ts

renderSequent :: Sequent -> Html
renderSequent (Sequent [] (Left (x, ys))) = varSpan x >> appList (map varSpan ys)
renderSequent (Sequent [] (Right phi)) = renderFormula phi
renderSequent (Sequent as c) =
  sequence_ (intersperse (fromString ", ") (map aux as))
  >> case c of
     Left (x,ys) -> fromString "|" >> varSpan x >> appList (map varSpan ys)
     Right phi -> fromString " ⊢ " >> renderFormula phi
  where
    aux (Left x) = varSpan x >> fromString ":" >> metaKindSpan "Term"
    aux (Right phi) = renderFormula phi

---- Render a compact representation of an open object, excluding implicit
---- hypotheses.
renderOpen :: (a -> Html) -> Open a -> Html
renderOpen f (Open hyps a) =
  quantification >> derivations >> rest
  where
    explicitHyps = filter (not . bindImplicit) hyps
    (subjects, hyps')   = span (\h -> isSubject (bindTy h)) explicitHyps
    (judgments, hyps'') = span (\h -> isJudgment (bindTy h)) hyps'

    quantification
      | null subjects || null judgments = return ()
      | otherwise     = do metaQuantifierSpan "for all "
                           mapM_ subj subjects
                           fromString ", "
    derivations
      | null judgments = return ()
      | otherwise      = do --metaQuantifierSpan "using "
                            mapM_ judg judgments
                            cdots
    rest | null hyps'' = f a
         | otherwise   = renderOpen f (Open hyps'' a)

    subj (HypBinding Nothing _ _) = return ()
    subj (HypBinding (Just x) _ ty) =
      case ty of
      TermTy (Open hs TermConst) ->
        do varSpan x
           H.sup . fromString $ concat ["(",show $ length hs,")"]
           fromString " "
      PropTy (Open hs PropConst) ->
        do varSpan x
           when (not . null $ hs) $
             H.sup . fromString $ concat ["(",show $ length hs,")"]
           fromString " "
      -- We don't really know how to render explicit quantification of sequents.
      -- Use cases are also quite limited.
      SequentTy (Open _hs SequentConst) -> return ()
      -- Remaining cases shouldn't happen
      _ -> return ()
    judg (HypBinding _ _ ty) =
      case ty of
      ProofTy (Open hs (ProofType sq)) ->
        parens (renderOpen renderSequent (Open hs sq)) >> fromString " "
      RefTy (Open hs (RefType sq)) ->
        parens (renderOpen renderSequent (Open hs sq)) >> fromString " "
      -- Remaining cases should not happen
      _ -> return ()

isSubject :: ObjType -> Bool
isSubject (PropTy _)    = True
isSubject (TermTy _)    = True
isSubject (SequentTy _) = True
isSubject (RefTy _)     = False
isSubject (ProofTy _)   = False

isJudgment :: ObjType -> Bool
isJudgment = not . isSubject
