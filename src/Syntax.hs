{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
module Syntax where

import           Language.Twelf.IntSyn

type PredName = String
type VarName = String
type RefName = String
type HoleName = String
type Arity = Int

-- | The type of a "box" is a possibly empty list of hypothetical terms and
-- proof references followed by a conclusion.
data Sequent =
  Sequent { antecedent :: [Either VarName Formula]
            -- If this is a partial sequent with a hole, the consequent
            -- is an application of a hole to some list of objects from the context.
            -- Otherwise, the consequent is a concrete formula.
          , consequent :: (Either (VarName, [VarName]) Formula)
          }
             deriving (Eq, Ord, Show)

-- | Unit types representing the unindexed type constants "box", "term" and "prop"
data SequentConst = SequentConst deriving (Eq, Ord, Show)
data TermConst = TermConst deriving (Eq, Ord, Show)
data PropConst = PropConst deriving (Eq, Ord, Show)

-- | Union of types of objects that may appear in a valid context.
data ObjType = TermTy (Open TermConst)
             | PropTy (Open PropConst)
             | RefTy (Open RefType)
             | SequentTy (Open SequentConst)
             | ProofTy (Open ProofType)
             deriving (Eq, Ord, Show)

data Obj = ObjTerm (Open Term)
         | ObjProp (Open Formula)
         | ObjRef (Open Ref)
         | ObjSequent (Open Sequent)
         | ObjProof (Open ProofTerm)
     deriving (Eq, Ord, Show)

-- | A binder for a hypothetical object.
data HypBinding = HypBinding { bindVar :: Maybe VarName
                             , bindImplicit :: Bool
                             , bindTy :: ObjType
                             }
                deriving (Eq, Ord, Show)

data Ref = RefApp VarName [Obj]
     deriving (Eq, Ord, Show)

-- | A reference type is simply a wrapped box type.
data RefType = RefType Sequent deriving (Eq, Ord, Show)

-- | The type of open proofs. This includes the box type that the proof proves, as well
--   as a list of hypothetical objects.
data ProofType = ProofType Sequent deriving (Eq, Ord, Show)

-- | General type of open objects.
data Open a = Open [HypBinding] a deriving (Eq, Ord, Show)

-- | Formula data type. Represents propositions.
data Formula = Top
             | Bot
             | Conj Formula Formula
             | Disj Formula Formula
             | Imp Formula Formula
             | Neg Formula
             | Pred PredName [Obj]
             | Eq Term Term
             | All VarName Formula
             | Exi VarName Formula
  deriving (Eq, Ord, Show)

-- | Term representation.
data Term = Var VarName
          | App VarName [Obj]
  deriving (Eq, Ord, Show)

-- | Fitch proof term.
data ProofTerm = VarIntro Sequent (Maybe VarName) ProofTerm
               | Assumption Sequent Formula (Maybe RefName) ProofTerm
               | Seq Sequent Sequent ProofTerm (Maybe RefName) ProofTerm
               | Copy Formula RefName
               | TopI
               | ConI Formula Formula RefName RefName
               | ConE1 Formula Formula RefName
               | ConE2 Formula Formula RefName
               | DisE Formula Formula Formula RefName RefName RefName
               | DisI1 Formula Formula RefName
               | DisI2 Formula Formula RefName
               | ImpI Formula Formula RefName
               | ImpE Formula Formula RefName RefName
               | NegI Formula RefName
               | NegE Formula RefName RefName
               | BotE Formula RefName
               | AllI (Maybe VarName) Formula RefName
               | AllE (Maybe VarName) Formula Term RefName
               | ExiI (Maybe VarName) Formula Term RefName
               | ExiE (Maybe VarName) Formula Formula RefName RefName
               | EqI Term
               | EqE Term Term (Maybe VarName) Formula RefName RefName
               | LEM Formula
               | NNE Formula RefName
               | PBC Formula RefName
               | NNI Formula RefName
               | MT Formula Formula RefName RefName
               | Hole ProofType VarName [Obj] -- A by Hole(dep1, ..., depn)
  deriving (Eq, Ord, Show)

isClosedTermTy :: ObjType -> Bool
isClosedTermTy (TermTy (Open [] TermConst)) = True
isClosedTermTy _ = False

isClosedPropTy :: ObjType -> Bool
isClosedPropTy (PropTy (Open [] PropConst)) = True
isClosedPropTy _ = False

isExoticTermTy :: ObjType -> Bool
isExoticTermTy (TermTy (Open termHyps TermConst)) =
               any (not . isClosedTermTy . bindTy) termHyps
isExoticTermTy _ = False

isExoticPropTy :: ObjType -> Bool
isExoticPropTy (PropTy (Open propHyps PropConst)) =
               any (not . isClosedTermTy . bindTy) propHyps
isExoticPropTy _ = False

isHoleTy :: ObjType -> Bool
isHoleTy (RefTy _) = True
isHoleTy (SequentTy _) = True
isHoleTy (ProofTy _) = True
isHoleTy _ = False
               
-- | Given a type of the form
--     term -> term -> ... -> term,
--   returns the number of "term" occurrences in negative position.
termArity' :: A -> Int
termArity' (A bindings _) = length bindings

-- | Given a type of the form
--     term -> term -> ... -> prop,
--   returns the number of "term" occurrences in negative position.
propArity :: A -> Int
propArity (A bindings _) = length bindings

convertObj :: ObjType -> M -> Obj
convertObj t (M bindings r) =
  let binder = Open (map convertHypothesis bindings)
  in case t of
     TermTy _    -> ObjTerm    . binder . convertTerm      $ M [] r
     PropTy _    -> ObjProp    . binder . convertProp      $ M [] r
     RefTy _     -> ObjRef     . binder . convertRef       $ M [] r
     SequentTy _ -> ObjSequent . binder . convertSequent   $ M [] r
     ProofTy _   -> ObjProof   . binder . convertProofTerm $ M [] r

convertRef :: M -> Ref
convertRef (M [] (R (RVar x (A bindings _)) args)) =
           RefApp x (zipWith convertObj (map (bindTy . convertHypothesis) bindings) args)
convertRef m = error . concat $ ["Malformed reference: ", show m]

convertTerm :: M -> Term
convertTerm m =
  case m of
  M [] (R (RVar f (A bindings _)) args)
    | not (null args) -> App f (zipWith
                                 convertObj
                                 (map (bindTy . convertHypothesis) bindings)
                                 args)
  M [] (R (RVar x _) []) -> Var x
  _ -> error $ concat ["Malformed term: ", show m]

convertProp :: M -> Formula
convertProp m =
  case m of
  M [] (R (RConst "top") [])            -> Top
  M [] (R (RConst "bot") [])            -> Bot
  M [] (R (RConst "\\/") [m1, m2])      -> Disj (convertProp m1) (convertProp m2)
  M [] (R (RConst "/\\") [m1, m2])      -> Conj (convertProp m1) (convertProp m2)
  M [] (R (RConst "=>") [m1, m2])       -> Imp (convertProp m1) (convertProp m2)
  M [] (R (RConst "~") [m1])            -> Neg (convertProp m1)
  M [] (R (RConst "==") [m1, m2])       -> Eq (convertTerm m1) (convertTerm m2)
  M [] (R (RConst "all")
           [M [(mx, _, _)] r])          -> All (maybe "_" id mx)
                                               (convertProp (M [] r))
  M [] (R (RConst "exi")
           [M [(mx, _, _)] r])          -> Exi (maybe "_" id mx)
                                               (convertProp (M [] r))
  M [] (R (RVar p (A bindings _)) args) ->
    Pred p (zipWith
             convertObj
             (map (bindTy . convertHypothesis) bindings)
             args)
  _ -> error $ concat ["Malformed proposition: ", show m]

convertSequent :: M -> Sequent
convertSequent m =
  case m of
  M [] (R (RConst ",") [m1, m2]) ->
    let assmForm = convertProp m1
        Sequent as cf = convertSequent m2
    in Sequent (Right assmForm:as) cf
  M [] (R (RConst "tm") [M [(mv, _, _)] r]) ->
    let Sequent as cf = convertSequent (M [] r)
        assmTerm = maybe "_" id mv
    in Sequent (Left assmTerm:as) cf
  M [] (R (RConst "|-") [pm]) ->
    Sequent [] (Right $ convertProp pm)
  M [] (R (RVar x _) ys) ->
    Sequent [] (Left (x, map convertVarName ys))
  _ -> error $ concat ["Malformed sequent: ", show m]

convertRefType :: P -> RefType
convertRefType (P "ref" [bt]) = RefType (convertSequent bt)
convertRefType p = error $ "Not a ref type: " ++ show p

convertSequentConst :: P -> SequentConst
convertSequentConst (P "sequent" []) = SequentConst
convertSequentConst p = error $ "Not a sequent constant: " ++ show p

convertProofType :: P -> ProofType
convertProofType (P "proof" [bt]) = ProofType (convertSequent bt)
convertProofType p = error $ "Not a proof type: " ++ show p

convertTermType :: P -> TermConst
convertTermType (P "term" []) = TermConst
convertTermType p = error $ "Not a term constant: " ++ show p

convertPropType :: P -> PropConst
convertPropType (P "prop" []) = PropConst
convertPropType p = error $ "Not a prop constant: " ++ show p

convertOpen :: (P -> a) -> A -> Open a
convertOpen f (A bindings p) = Open (map convertHypothesis bindings) (f p)

convertHypothesis :: Binding -> HypBinding
convertHypothesis b@(mn, _, a@(A _ (P name _))) =
  HypBinding mn (isImplicit b) $
     case name of
       "term"    -> TermTy (convertOpen convertTermType a)
       "prop"    -> PropTy (convertOpen convertPropType a)
       "proof"   -> ProofTy (convertOpen convertProofType a)
       "ref"     -> RefTy (convertOpen convertRefType a)
       "sequent" -> SequentTy (convertOpen convertSequentConst a)
       _         -> error $ concat ["Hypothetical object '"
                                   , show mn, "' has unknown type: ", show a]

convertVarName :: M -> VarName
convertVarName (M [] (R (RVar x _) _)) = x
convertVarName m = error $ concat ["Not a variable: ", show m]

splitBinder :: M -> (Maybe String, M)
splitBinder (M [(mv, _, _)] r) = (mv, M [] r)
splitBinder m = error $ concat ["Not a single-argument lambda: ", show m]

convertOpenProofTerm :: A -> M -> Open (ProofTerm, Sequent)
convertOpenProofTerm (A _ (P "proof" [sq])) (M hyps r) =
  Open (map convertHypothesis hyps) (convertProofTerm (M [] r)
                                    ,convertSequent sq)
convertOpenProofTerm _ _ = error "Malformed open proof term"

convertProofTerm :: M -> ProofTerm
convertProofTerm m =
  case m of
  M [] (R (RConst "var") [mOBS, mOPT]) ->
    let (mv, mOPT') = splitBinder mOPT
        (_, mOBS')  = splitBinder mOBS
     in VarIntro (convertSequent mOBS') mv (convertProofTerm mOPT')
  M [] (R (RConst "assumption;") [mBS, mPhi, mPT]) ->
    let (mv, mPT') = splitBinder mPT in
    Assumption (convertSequent mBS) (convertProp mPhi) mv (convertProofTerm mPT')
  M [] (R (RConst ";") [mBS, mBT, mPT1, mPT2]) ->
    let (mv, mPT2') = splitBinder mPT2 in
    Seq (convertSequent mBS) (convertSequent mBT)
        (convertProofTerm mPT1) mv (convertProofTerm mPT2')
  M [] (R (RConst "copy") [mPhi, mRef]) ->
    Copy (convertProp mPhi) (convertVarName mRef)
  M [] (R (RConst "top_i") []) -> TopI
  M [] (R (RConst "con_i") [mPA, mPB, mRefA, mRefB]) ->
    ConI (convertProp mPA) (convertProp mPB)
         (convertVarName mRefA) (convertVarName mRefB)
  M [] (R (RConst "con_e1") [mPA, mPB, mRef]) ->
    ConE1 (convertProp mPA) (convertProp mPB) (convertVarName mRef)
  M [] (R (RConst "con_e2") [mPA, mPB, mRef]) ->
    ConE2 (convertProp mPA) (convertProp mPB) (convertVarName mRef)
  M [] (R (RConst "dis_e") [mPA, mPB, mPC, mRef1, mRef2, mRef3]) ->
    DisE (convertProp mPA) (convertProp mPB) (convertProp mPC)
         (convertVarName mRef1) (convertVarName mRef2) (convertVarName mRef3)
  M [] (R (RConst "dis_i1") [mPA, mPB, mRef]) ->
    DisI1 (convertProp mPA) (convertProp mPB) (convertVarName mRef)
  M [] (R (RConst "dis_i2") [mPA, mPB, mRef]) ->
    DisI2 (convertProp mPA) (convertProp mPB) (convertVarName mRef)
  M [] (R (RConst "imp_i") [mPA, mPB, mRef]) ->
    ImpI (convertProp mPA) (convertProp mPB) (convertVarName mRef)
  M [] (R (RConst "imp_e") [mPA, mPB, mRef1, mRef2]) ->
    ImpE (convertProp mPA) (convertProp mPB)
         (convertVarName mRef1) (convertVarName mRef2)
  M [] (R (RConst "neg_i") [mPA, mRef]) ->
    NegI (convertProp mPA) (convertVarName mRef)
  M [] (R (RConst "neg_e") [mPA, mRef1, mRef2]) ->
    NegE (convertProp mPA) (convertVarName mRef1) (convertVarName mRef2)
  M [] (R (RConst "bot_e") [mPA, mRef]) ->
    BotE (convertProp mPA) (convertVarName mRef)
  M [] (R (RConst "all_i") [mOPA, mRef]) ->
    let (mv, mOPA') = splitBinder mOPA in
    AllI mv (convertProp mOPA') (convertVarName mRef)
  M [] (R (RConst "all_e") [mOPA, mT, mRef]) ->
    let (mv, mOPA') = splitBinder mOPA in
    AllE mv (convertProp mOPA') (convertTerm mT) (convertVarName mRef)
  M [] (R (RConst "exi_i") [mOPA, mT, mRef]) ->
    let (mv, mOPA') = splitBinder mOPA in
    ExiI mv (convertProp mOPA') (convertTerm mT) (convertVarName mRef)
  M [] (R (RConst "exi_e") [mOPA, mPB, mRef1, mRef2]) ->
    let (mv, mOPA') = splitBinder mOPA in
    ExiE mv (convertProp mOPA') (convertProp mPB)
         (convertVarName mRef1) (convertVarName mRef2)
  M [] (R (RConst "eq_i") [mT]) ->
    EqI (convertTerm mT)
  M [] (R (RConst "eq_e") [mS, mT, mOPA, mRef1, mRef2]) ->
    let (mv, mOPA') = splitBinder mOPA in
    EqE (convertTerm mS) (convertTerm mT) mv (convertProp mOPA')
        (convertVarName mRef1) (convertVarName mRef2)
  M [] (R (RConst "lem") [mPA]) ->
    LEM (convertProp mPA)
  M [] (R (RConst "nne") [mPA, mRef]) ->
    NNE (convertProp mPA) (convertVarName mRef)
  M [] (R (RConst "pbc") [mPA, mRef]) ->
    PBC (convertProp mPA) (convertVarName mRef)
  M [] (R (RConst "mt") [mPA, mPB, mRef1, mRef2]) ->
    MT (convertProp mPA) (convertProp mPB) (convertVarName mRef1) (convertVarName mRef2)
  M [] (R (RConst "nni") [mPA, mRef]) ->
    NNI (convertProp mPA) (convertVarName mRef)
  M (_:_) _ -> error $ concat ["Encountered unexpected open proof term."]
  M [] (R (RVar hole (A bindings p)) args) ->
    Hole (convertProofType p)
         hole
         (zipWith convertObj (map (bindTy . convertHypothesis) bindings) args)
  M _ (R root args) ->
    error $ concat ["Encountered unknown proof-term with root '"
                   ,show root, "' and "
                   ,show $ length args
                   ," arguments."]
