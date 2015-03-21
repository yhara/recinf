-- 多相型レコード計算

import Test.Hspec
import qualified Data.Map as M hiding ((\\))
import Data.List ((\\))
import Data.Maybe (catMaybes)
import Control.Monad.State
import Control.Applicative

-- Types

type Label = String
type Name = String

data Prim = PBool Bool | PInt Int
  deriving (Eq, Show)
type VId = Int
type Fields = M.Map Label MonoTy
data MonoTy = TyPrim Prim
            | TyVar VId
            | TyFun MonoTy MonoTy
            | TyRecord Fields
            | TyVariant Fields
  deriving (Eq, Show)
type KindedTy = ([(VId, Kind)], MonoTy)

data Kind = KiU
          | KiRecord Fields
          | KiVariant Fields

occursTy :: Int -> MonoTy -> Bool
occursTy i (TyPrim _) = False
occursTy i (TyVar ii) = (i == ii)
occursTy i (TyFun ty1 ty2) = occursTy i ty1 || occursTy i ty2
occursTy i (TyRecord fields) = any (occursTy i) (M.elems fields)
occursTy i (TyVariant fields) = any (occursTy i) (M.elems fields)

sameFields :: Fields -> Fields -> Bool
sameFields fields1 fields2 =
  M.null $ M.difference fields1 fields2

newTyVar :: StateT Int (Either String) MonoTy
newTyVar = do
  newId <- get
  put (newId+1)
  return (TyVar newId)

-- Expr

data Expr
  = EVar Name
  | ELit Prim 
  | EAbs Name Expr
  | EApp Expr Expr
  | ELet Name Expr Expr
  | ERecord [(Label, Expr)]
  | ERecordRef Expr Label
  | ERecModify Expr Label Expr
  | EVariant Label Expr
  | ECase Expr [(Label, Expr)]
  deriving (Eq, Show)

--varIds :: MonoTy -> [VId]
--varIds (TyPrim _) = []
--varIds (TyVar id) = [id]
--varIds (TyFun t1 t2) = varIds t1 ++ varIds t2
--
--freeTypeIds :: KindedTy -> [VId]
--freeTypeIds (ids, t) = (varIds t) \\ ids


-- Subst

type Subst = M.Map VId MonoTy

substMonoTy :: Subst -> MonoTy -> MonoTy
substMonoTy ss t@(TyPrim _) = t
substMonoTy ss t@(TyVar i) =
  case M.lookup i ss of
    Just ts -> ts
    Nothing -> t
substMonoTy ss (TyFun ts1 ts2) = TyFun (substMonoTy ss ts1) (substMonoTy ss ts2)
substMonoTy ss (TyRecord fields) = TyRecord $ M.map (substMonoTy ss) fields
substMonoTy ss (TyVariant fields) = TyVariant $ M.map (substMonoTy ss) fields

substKindedTy :: Subst -> KindedTy -> KindedTy
substKindedTy ss (ids, ty) = (ids, substMonoTy ss ty)

substKind :: Subst -> Kind -> Kind
substKind ss KiU = KiU
substKind ss (KiRecord fields) = KiRecord $ M.map (substMonoTy ss) fields
substKind ss (KiVariant fields) = KiVariant $ M.map (substMonoTy ss) fields

substSubst :: Subst -> Subst -> Subst
substSubst ss target = M.map (substMonoTy ss) target

mergeSubsts :: [Subst] -> Subst
mergeSubsts sss = foldr1 substSubst sss

-- Unification

type TyEq = (MonoTy, MonoTy)
type KiEnv = M.Map VId Kind

substTyEq :: Subst -> TyEq -> TyEq
substTyEq ss (t1, t2) = (substMonoTy ss t1, substMonoTy ss t2)
substTyEqs :: Subst -> [TyEq] -> [TyEq]
substTyEqs ss = map (substTyEq ss)

substKiEnv :: Subst -> KiEnv -> KiEnv
substKiEnv ss kenv = M.map (substKind ss) kenv


-- p.258 図6.5
unify :: [TyEq] -> KiEnv -> Either String (KiEnv, Subst)
unify tyeqs kenv = unify' tyeqs kenv M.empty M.empty
  where
    unify' :: [TyEq] -> KiEnv -> Subst -> KiEnv ->
              Either String (KiEnv, Subst)
    unify' [] kenv subst senv = Right (kenv, subst)

    unify' ((ty1, ty2):rest) kenv subst senv =
      case (ty1, ty2) of
        _ | ty1 == ty2 ->  -- (i)
          unify' rest kenv subst senv

        (TyVar id1, ty2) -> do
          case M.lookup id1 kenv of
            Just kiU -> -- (ii)
              if occursTy id1 ty2
              then Left "id1 occurs in ty2"
              else let ss = M.singleton id1 ty2 in
                unify' (substTyEqs ss rest)
                       (substKiEnv ss (M.delete id1 kenv))
                       (M.insert id1 ty2 (substSubst ss subst))
                       (M.insert id1 KiU (substKiEnv ss senv))

            Just (KiRecord fields) -> undefined -- (iii),(iv)
            Just (KiVariant fields) -> undefined
            Nothing -> Left "id1 not in kenv"

        (TyRecord fields1, TyRecord fields2) -> -- (v)
          if sameFields fields1 fields2 
          then
            let makePair = (\k -> (,) <$> (M.lookup k fields1) <*> (M.lookup k fields2)) in
              let tyeqs = catMaybes $ map makePair (M.keys fields1) in
                unify' (tyeqs ++ rest) kenv subst senv
          else Left "label mismatch"

        (TyVariant fields1, TyVariant fields2) -> 
          undefined

        (TyFun ty1 ty2, TyFun ty3 ty4) -> -- (vi)
          unify' ((ty1, ty3):(ty2, ty4):rest) kenv subst senv

        _ -> Left "unify' no match"

-- Infer

type TyEnv = M.Map Name KindedTy
substTyEnv :: Subst -> TyEnv -> TyEnv
substTyEnv ss env = M.map (substKindedTy ss) env 

infer :: KiEnv -> TyEnv -> Expr -> Either String (Int, KiEnv, Subst, MonoTy)
infer kenv env expr = do
  ((kenv', ss, ty), i) <- runStateT (infer' kenv env expr) 0
  return (i, kenv', ss, ty)

infer' :: KiEnv -> TyEnv -> Expr -> StateT Int (Either String) (KiEnv, Subst, MonoTy)
infer' kenv env (ELit prim) = undefined
infer' kenv env (EVar name) =
  case M.lookup name env of
    Just (tykis, varTy) -> do
      ss <- foldM (\ss' (id, ki) -> do
                    ty' <- newTyVar
                    return $ M.insert id ty' ss')
                  M.empty
                  tykis
      let adds = map (\(id, ki) -> (id, substKind ss ki)) tykis
      let newKenv = M.union kenv (M.fromList adds)
      return (newKenv, M.empty, substMonoTy ss varTy)
    Nothing -> lift $ Left "infer': undefined variable"

infer' kenv env (EAbs name bodyExpr) = do
  argTy@(TyVar id) <- newTyVar
  (kenv', ss, bodyTy) <- infer' (M.insert id KiU kenv)
                                (M.insert name ([], argTy) env)
                                bodyExpr
  return (kenv', ss, TyFun (substMonoTy ss argTy) bodyTy)

infer' kenv env (EApp funExpr argExpr) = do
  (kenv1, ss1, funTy) <- infer' kenv env funExpr
  (kenv2, ss2, argTy) <- infer' kenv1 (substTyEnv ss1 env) argExpr
  retTy <- newTyVar
  let tyeq = ((substMonoTy ss2 funTy), TyFun argTy retTy)
  (kenv3, ss3) <- lift $ unify [tyeq] kenv2
  return (kenv3, mergeSubsts [ss3, ss2, ss1], substMonoTy ss3 retTy)

infer' kenv env (ERecord pairs) = do
  infers <- foldM (\sum (label, elemExpr) -> do
                    let (kenv_, env_, ss_, _) = head sum
                    let env' = substTyEnv ss_ env_
                    (kenv', ss', elemTy) <- infer' kenv_ env' elemExpr
                    return $ (kenv', env', ss', elemTy):sum)
                  [(kenv, env, M.empty, TyVar (-1))]
                  pairs
  let (kenv', _, ss', _) = head infers
  let labels = map fst pairs
  let elemTys = map (\(_, _, _, elemTy) -> substMonoTy ss' elemTy)
                    (init infers) -- 最後のダミーを除く
  return (kenv', ss', TyRecord (M.fromList $ zip labels elemTys))

infer' kenv env (ERecordRef recExpr label) = do
  (kenv1, ss1, recTy) <- infer' kenv env recExpr
  t1@(TyVar id1) <- newTyVar
  t2@(TyVar id2) <- newTyVar
  let newKenv = M.insert id1 KiU $
                M.insert id2 (KiRecord $ M.singleton label t1) $
                kenv
  (kenv2, ss2) <- lift $ unify [(t2, recTy)] newKenv
  return (kenv2, mergeSubsts [ss2, ss1], substMonoTy ss2 t1) 

infer' kenv env (ELet name varExpr bodyExpr) = undefined

infer' kenv env (ERecModify recExpr label valExpr) = undefined
infer' kenv env (EVariant label variExpr) = undefined
infer' kenv env (ECase expr pairs) = undefined
