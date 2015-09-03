{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
module Syntax where

import qualified Data.Set as S

import           Language.Twelf.IntSyn

type PredName = String
type VarName = String
type RefName = String
type HoleName = String
type Arity = Int

-- | The type of a "box" is a possibly empty list of hypothetical terms and
-- proof references followed by a conclusion.
data BoxType = BoxType [Either VarName Formula] -- ^ Antecedent: Terms or assumptions
                       (Either VarName Formula) -- ^ Consequent: A box-type hole or
                                                --   a formula
             deriving (Eq, Ord, Show)

-- | Representation of possible hypothetical objects.
data HypType = HypTerm Arity
             | HypProp Arity
             | HypRef RefType
             | HypBox
             | HypProof ProofType
             deriving (Eq, Ord, Show)

-- | A binder for a hypothetical object.
data HypBinding = HypBinding (Maybe VarName) HypType deriving (Eq, Ord, Show)

-- | A reference type is simply a wrapped box type.
data RefType = RefType BoxType deriving (Eq, Ord, Show)

-- | The type of open proofs. This includes the box type that the proof proves, as well
--   as a list of hypothetical objects.
data ProofType = ProofType [HypBinding] BoxType deriving (Eq, Ord, Show)

-- | Formula data type. Represents propositions.
data Formula = Top
             | Bot
             | Conj Formula Formula
             | Disj Formula Formula
             | Imp Formula Formula
             | Neg Formula
             | Pred PredName [Term]
             | Eq Term Term
             | All VarName Formula
             | Exi VarName Formula
  deriving (Eq, Ord, Show)

-- | Term representation.
data Term = Var VarName
          | App VarName [Term]
  deriving (Eq, Ord, Show)

-- | Fitch proof term.
data ProofTerm = VarIntro (Maybe VarName) ProofTerm
               | Assumption BoxType Formula (Maybe RefName) ProofTerm
               | Seq BoxType BoxType ProofTerm (Maybe RefName) ProofTerm
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
               | Hole ProofType VarName
  deriving (Eq, Ord, Show)

data OpenProofTerm = OpenProofTerm [HypBinding] ProofTerm deriving (Eq, Ord, Show)

class FreeVars t where
  ftv :: t -> S.Set String

instance FreeVars Formula where
  ftv p =
    case p of
    Top        -> S.empty
    Bot        -> S.empty
    Conj p1 p2 -> S.unions [ftv p1, ftv p2]
    Disj p1 p2 -> S.unions [ftv p1, ftv p2]
    Imp p1 p2  -> S.unions [ftv p1, ftv p2]
    Neg p1     -> ftv p1
    Pred _ ts  -> S.unions $ map ftv ts
    Eq t1 t2   -> S.unions [ftv t1, ftv t2]
    All x p'   -> S.delete x $ ftv p'
    Exi x p'   -> S.delete x $ ftv p'

instance FreeVars Term where
  ftv t =
    case t of
    Var x    -> S.singleton x
    App x ts -> S.insert x $ S.unions $ map ftv ts

instance FreeVars ProofTerm where
  ftv pt =
    case pt of
    VarIntro mx pt' -> maybe id S.delete mx $ ftv pt'
    Assumption bt phi mx pt' -> S.unions [ftv bt, ftv phi, maybe id S.delete mx $ ftv pt']
    Seq bt1 bt2 pt1 mx pt' ->
      S.unions [ftv bt1, ftv bt2, ftv pt1, maybe id S.delete mx $ ftv pt']
    Copy phi r -> S.insert r $ ftv phi
    TopI -> S.empty
    ConI phi1 phi2 r1 r2 -> S.unions [S.fromList [r1, r2], ftv phi1, ftv phi2]
    ConE1 phi1 phi2 r -> S.insert r $ S.unions [ftv phi1, ftv phi2]
    ConE2 phi1 phi2 r -> S.insert r $ S.unions [ftv phi1, ftv phi2]
    DisE phi1 phi2 phi3 r1 r2 r3 ->
      S.unions [S.fromList [r1,r2,r3], ftv phi1, ftv phi2, ftv phi3]
    DisI1 phi1 phi2 r -> S.insert r $ S.unions [ftv phi1, ftv phi2]
    DisI2 phi1 phi2 r -> S.insert r $ S.unions [ftv phi1, ftv phi2]
    ImpI phi1 phi2 r -> S.insert r $ S.unions [ftv phi1, ftv phi2]
    ImpE phi1 phi2 r1 r2 -> S.unions [S.fromList [r1, r2], ftv phi1, ftv phi2]
    NegI phi r -> S.insert r $ ftv phi
    NegE phi r1 r2 -> S.unions [S.fromList [r1, r2], ftv phi]
    BotE phi r -> S.insert r $ ftv phi
    AllI mx phi r -> S.insert r $ maybe id S.delete mx $ ftv phi
    AllE mx phi t r -> S.unions [ftv t, S.insert r $ maybe id S.delete mx $ ftv phi]
    ExiI mx phi t r -> S.unions [ftv t, S.insert r $ maybe id S.delete mx $ ftv phi]
    ExiE mx phi1 phi2 r1 r2 ->
      S.unions [S.fromList [r1, r2], maybe id S.delete mx $ ftv phi1, ftv phi2]
    EqI t -> ftv t
    EqE t1 t2 mx phi r1 r2 ->
      S.unions [ftv t1, ftv t2, maybe id S.delete mx $ ftv phi, S.fromList [r1, r2]]
    LEM phi -> ftv phi
    NNE phi r -> S.insert r $ ftv phi
    Hole typ x -> S.insert x $ ftv typ

instance FreeVars ProofType where
  ftv (ProofType [] bt) = ftv bt
  ftv (ProofType (HypBinding mx ht:hs) bt) =
    S.unions [ftv' ht, maybe id S.delete mx $ ftv (ProofType hs bt)]
    where
      ftv' (HypProof pt) = ftv pt
      ftv' (HypRef rt) = ftv rt
      ftv' _ = S.empty

instance FreeVars RefType where
  ftv (RefType bt) = ftv bt

instance FreeVars BoxType where
  ftv (BoxType [] conc) = either S.singleton ftv conc
  ftv (BoxType (Left x:as) conc) = S.delete x $ ftv $ BoxType as conc
  ftv (BoxType (Right phi:as) conc) = S.unions [ftv phi, ftv $ BoxType as conc]

class Subst u where
  subst :: Term -> VarName -> u -> u

instance Subst Formula where
  subst t x = go
    where
      go phi =
        case phi of
        Top            -> Top
        Bot            -> Bot
        Conj phi1 phi2 -> Conj (go phi1) (go phi2)
        Disj phi1 phi2 -> Disj (go phi1) (go phi2)
        Imp phi1 phi2  -> Imp (go phi1) (go phi2)
        Neg phi'       -> Neg (go phi')
        Pred p ts      -> Pred p $ map (subst t x) ts
        Eq t1 t2       -> Eq (subst t x t1) (subst t x t2)
        All y phi'     -> if x == y then phi else All y (go phi')
        Exi y phi'     -> if x == y then phi else Exi y (go phi')

instance Subst Term where
  subst t x = go
    where
      go t' =
        case t' of
        Var y -> if y == x then t else t'
        App f _ | f == x -> error $ "Attempt to substitute term for function symbol"
        App f ts -> App f (map go ts)

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

convertTerm :: M -> Term
convertTerm m =
  case m of
  M [] (R (RVar f _) args) | not (null args) -> App f (map convertTerm args)
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
  M [] (R (RVar p _) args)              -> Pred p (map convertTerm args)
  _ -> error $ concat ["Malformed proposition: ", show m]

convertBoxType :: M -> BoxType
convertBoxType m =
  case m of
  M [] (R (RConst ",,,") [m1, m2]) ->
    let assmForm = convertProp m1
        BoxType as cf = convertBoxType m2
    in BoxType (Right assmForm:as) cf
  M [] (R (RConst "tm") [M [(mv, _, _)] r]) ->
    let BoxType as cf = convertBoxType (M [] r)
        assmTerm = maybe "_" id mv
    in BoxType (Left assmTerm:as) cf
  M [] (R (RConst "$") [pm]) ->
    BoxType [] (Right $ convertProp pm)
  M [] (R (RVar x _) []) -> BoxType [] (Left x)
  _ -> error $ concat ["Malformed box type: ", show m]

convertRefType :: A -> RefType
convertRefType (A _ (P "ref" [bt])) = RefType (convertBoxType bt)
convertRefType _ = error "Not a reference type"

convertProofType :: A -> ProofType
convertProofType (A bindings (P "proof" [bt])) =
  ProofType (map convertHypothesis bindings) (convertBoxType bt)
convertProofType _ = error "Not a proof type"

convertHypothesis :: Binding -> HypBinding
convertHypothesis (mn, _, a@(A _ (P name _))) =
  case name of
    "term"    -> HypBinding mn (HypTerm (termArity' a))
    "prop"    -> HypBinding mn (HypProp (propArity a))
    "proof"   -> HypBinding mn (HypProof (convertProofType a))
    "ref"     -> HypBinding mn (HypRef (convertRefType a))
    "boxtype" -> HypBinding mn HypBox
    _         -> error $ concat ["Hypothetical object '"
                                , show mn, "' has unknown kind: ", show a]      

convertVarName :: M -> VarName
convertVarName (M [] (R (RVar x _) _)) = x
convertVarName m = error $ concat ["Not a variable: ", show m]

splitBinder :: M -> (Maybe String, M)
splitBinder (M [(mv, _, _)] r) = (mv, M [] r)
splitBinder m = error $ concat ["Not a single-argument lambda: ", show m]

convertOpenProofTerm :: M -> OpenProofTerm
convertOpenProofTerm (M hyps r) =
  OpenProofTerm (map convertHypothesis hyps) (convertProofTerm (M [] r))

convertProofTerm :: M -> ProofTerm
convertProofTerm m =
  case m of
  M [] (R (RConst "var") [_mOBS, mOPT]) ->
    let (mv, mOPT') = splitBinder mOPT in
    VarIntro mv (convertProofTerm mOPT')
  M [] (R (RConst "assumption;") [mBS, mPhi, mPT]) ->
    let (mv, mPT') = splitBinder mPT in
    Assumption (convertBoxType mBS) (convertProp mPhi) mv (convertProofTerm mPT')
  M [] (R (RConst ";") [mBS, mBT, mPT1, mPT2]) ->
    let (mv, mPT2') = splitBinder mPT2 in
    Seq (convertBoxType mBS) (convertBoxType mBT)
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
  M (_:_) _ -> error $ concat ["Encountered unexpected open proof term."]
  M [] (R (RVar hole a) _args) ->
    Hole (convertProofType a) hole
  M _ (R root args) ->
    error $ concat ["Encountered unknown proof-term with root '"
                   ,show root, "' and "
                   ,show $ length args
                   ," arguments."]
