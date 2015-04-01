-- 多相型レコード計算

import Test.Hspec
import qualified Data.Map as M hiding ((\\))
import Data.List ((\\), union)
import Data.Maybe (catMaybes)
import Control.Monad.State
import Control.Applicative
import Debug.Trace (trace)

-- Types

type Label = String
type Name = String

data Prim = PBool Bool | PInt Int
  deriving (Show)
instance Eq Prim where
  (==) (PBool _) (PBool _) = True
  (==) (PInt _) (PInt _) = True
  (==) _ _ = False

type VId = Int
type Fields = M.Map Label MonoTy
data MonoTy = TyPrim Prim
            | TyVar VId
            | TyFun MonoTy MonoTy
            | TyRecord Fields
            | TyVariant Fields
  deriving (Eq, Show)

data Kind = KiU
          | KiRecord Fields
          | KiVariant Fields
  deriving (Eq, Show)
type KiEnv = M.Map VId Kind
type KindedTy = (KiEnv, MonoTy)

type TyEnv = M.Map Name KindedTy

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

ftv :: MonoTy -> [VId]
ftv (TyPrim _) = []
ftv (TyVar id) = [id]
ftv (TyFun t1 t2) = ftv t1 ++ ftv t2
ftv (TyRecord fields)  = concatMap ftv (M.elems fields)
ftv (TyVariant fields) = concatMap ftv (M.elems fields)

ftvKind :: Kind -> [VId]
ftvKind KiU = []
ftvKind (KiRecord fields)  = concatMap ftv (M.elems fields)
ftvKind (KiVariant fields) = concatMap ftv (M.elems fields)

  -- KindedTy: 'a::U, 'b::{{x: 'c}} in 'a -> 'b -> 'c
  -- p.248 FTV(t::k . o) = FTV(k) `union` FTV(o) \\ {t}
ftvKindedTy :: KindedTy -> [VId]
ftvKindedTy (tykis, ty) =
  let ftvks = concatMap ftvKind $ M.elems tykis in
    (Data.List.union ftvks (ftv ty)) \\ (M.keys tykis)

ftvEnv :: TyEnv -> [VId]
ftvEnv env = concatMap ftvKindedTy (M.elems env)

  -- KiEnv: 'a::U, 'b::{{x: Int}}, 'c::{{y: 'a, z: 'd}}
ftvKiEnv :: KiEnv -> [VId]
ftvKiEnv kenv = (concatMap ftvKind $ M.elems kenv) \\ (M.keys kenv)

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
substKindedTy ss (kenv, ty) = (substKiEnv ss kenv, substMonoTy ss ty)

substKind :: Subst -> Kind -> Kind
substKind ss KiU = KiU
substKind ss (KiRecord fields) = KiRecord $ M.map (substMonoTy ss) fields
substKind ss (KiVariant fields) = KiVariant $ M.map (substMonoTy ss) fields

substTyEnv :: Subst -> TyEnv -> TyEnv
substTyEnv ss env = M.map (substKindedTy ss) env 

substKiEnv :: Subst -> KiEnv -> KiEnv
substKiEnv ss kenv = M.map (substKind ss) kenv

substSubst :: Subst -> Subst -> Subst
substSubst ss2 ss1 = M.union (M.map (substMonoTy ss2) ss1)
                             ss2

mergeSubsts :: [Subst] -> Subst
mergeSubsts sss = 
  let ret = foldr1 substSubst sss in
    trace ("mergeSubsts: "++show sss++"\n"++
           "  -> "++show ret++"\n")
          ret

-- Unification

type TyEq = (MonoTy, MonoTy)

substTyEq :: Subst -> TyEq -> TyEq
substTyEq ss (t1, t2) = (substMonoTy ss t1, substMonoTy ss t2)
substTyEqs :: Subst -> [TyEq] -> [TyEq]
substTyEqs ss = map (substTyEq ss)

-- p.258 図6.5
unify :: [TyEq] -> KiEnv -> Either String (KiEnv, Subst)
unify tyeqs kenv = 
  let ret = unify' tyeqs kenv M.empty M.empty in
    trace ("unify: "++show tyeqs++"\n"++
           "kenv: "++show kenv++"\n"++
           "-> "++show ret++"\n")
          ret
  where
    unify' :: [TyEq] -> KiEnv -> Subst -> KiEnv ->
              Either String (KiEnv, Subst)
    unify' [] kenv subst senv = Right (kenv, subst)

    unify' ((ty1, ty2):rest) kenv subst senv =
      case (ty1, ty2) of
        _ | ty1 == ty2 ->  -- (i)
          unify' rest kenv subst senv

        (TyVar id1, TyPrim prim) ->
          let ss = M.singleton id1 ty2 in
            unify' (substTyEqs ss rest)
                   (substKiEnv ss (M.delete id1 kenv))
                   (M.insert id1 ty2 (substSubst ss subst))
                   (M.insert id1 KiU (substKiEnv ss senv))

        (TyPrim prim, TyVar id2) -> unify' ((ty2, ty1):rest) kenv subst senv

        (TyVar id1, ty2) | M.lookup id1 kenv == Just KiU -> -- (ii)
          case M.lookup id1 kenv of
            Just kiU -> -- (ii)
              if occursTy id1 ty2
              then Left "id1 occurs in ty2"
              else let ss = M.singleton id1 ty2 in
                unify' (substTyEqs ss rest)
                       (substKiEnv ss (M.delete id1 kenv))
                       (M.insert id1 ty2 (substSubst ss subst))
                       (M.insert id1 KiU (substKiEnv ss senv))

        (ty1, TyVar id2) | M.lookup id2 kenv == Just KiU ->
           unify' ((ty2, ty1):rest) kenv subst senv

        (TyVar id1, ty2@(TyVar id2)) ->  -- (iii)
          case (M.lookup id1 kenv, M.lookup id2 kenv) of
            (Just (KiRecord fields1), Just (KiRecord fields2)) ->
              let newKenv = M.delete id1 $ M.delete id2 kenv in
              let ss = M.singleton id1 ty2 in
              let tyeqs = M.elems $ M.intersectionWith (,) fields1 fields2 in
              let kind2 = substKind ss $ KiRecord (M.union fields2 fields1) in
                unify' (substTyEqs ss (tyeqs ++ rest))
                       (M.insert id2 kind2 (substKiEnv ss newKenv))
                       (M.insert id1 ty2 (substSubst ss subst))
                       (M.insert id1 (KiRecord fields1) (substKiEnv ss senv))

            (Just (KiVariant fields1), Just (KiVariant fields2)) ->
              undefined

            (ki1, ki2) -> Left $ "kind mismatch: "++(show (ki1, ki2))

        (TyVar id1, ty2@(TyRecord fields2)) ->  --- (iv)
          case M.lookup id1 kenv of
            Just (KiRecord fields1) ->
              if not $ M.null $ M.difference fields1 fields2
              then Left "fields1 is not subset of fields2"
              else
                if elem id1 (ftv ty2)
                then Left "id1 included in ty2"
                else
                  let ss = M.singleton id1 ty2 in
                  let tyeqs = M.elems $ M.intersectionWith (,) fields1 fields2 in
                    unify' (substTyEqs ss $ tyeqs ++ rest)
                           (substKiEnv ss $ M.delete id1 kenv)
                           (M.insert id1 ty2 $ substSubst ss subst)
                           (M.insert id1 (KiRecord fields1) $ substKiEnv ss senv)

            _ -> Left "invalid kind"

        (TyVar id1, TyVariant fields2) ->  --- (iv)
          undefined

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

        _ -> Left $ "unify' no match: "++(show (ty1, ty2))

-- Infer

-- MonoTyの型変数のうち、kenvとenvに現れないものを多相にしたもの
-- kenv, envは外側のプログラムの状況を表す
-- そのため、これらに現れるTyVarは勝手に多相にしてはいけない
typeClosure :: KiEnv -> TyEnv -> MonoTy -> (KiEnv, KindedTy)
typeClosure kenv env ty =
  let freeIds = (ftv ty \\ ftvKiEnv kenv) \\ (ftvEnv env) in
  let newKenv = M.fromList $ map (\id -> (id, KiU)) freeIds in
  (M.union kenv newKenv, (newKenv, ty))

  -- 1.hsでは、(varIds ty)からenv内のtsのfreeTypeIdsを引いていた
  -- tsは(ids, ty)の組
  -- ただし let g = x -> x in
  --        let f = y -> g y
  -- とかだと、fはちゃんと多相になる。
  -- typeClosureを呼ぶ前にenvにsubstを適用しているからだと思う(多分)

infer :: Expr -> Either String (Int, KiEnv, Subst, MonoTy)
infer expr = do
  ((kenv', ss, ty), i) <- runStateT (infer'' M.empty M.empty expr) 0
  return (i, kenv', ss, ty)


infer'' :: KiEnv -> TyEnv -> Expr -> StateT Int (Either String) (KiEnv, Subst, MonoTy)
infer'' kenv env expr = do
  (kenv', ss, ty) <- infer' kenv env expr
  return $ trace ("infer: "++show expr++"\n"++
                  "kenv,env: "++show (kenv, env)++"\n"++
                  "ret: "++show (kenv', ss, ty)++"\n") $
    (kenv', ss, ty)

infer' :: KiEnv -> TyEnv -> Expr -> StateT Int (Either String) (KiEnv, Subst, MonoTy)
infer' kenv env (ELit prim) = do
  return (kenv, M.empty, TyPrim prim)

infer' kenv env (EVar name) =
  case M.lookup name env of
    Just (tykis, varTy) -> do
      ss <- foldM (\ss' (id, ki) -> do
                    ty' <- newTyVar
                    return $ M.insert id ty' ss')
                  M.empty
                  (M.toList tykis)
      let adds = map (\(id, ki) -> (id, substKind ss ki)) (M.toList tykis)
      let newKenv = M.union kenv (M.fromList adds)
      return (newKenv, M.empty, substMonoTy ss varTy)
    Nothing -> lift $ Left "infer': undefined variable"

infer' kenv env (EAbs name bodyExpr) = do
  argTy@(TyVar id) <- newTyVar
  (kenv', ss, bodyTy) <- infer'' (M.insert id KiU kenv)
                                (M.insert name (M.empty, argTy) env)
                                bodyExpr
  return $ (kenv', ss, TyFun (substMonoTy ss argTy) bodyTy)

infer' kenv env (EApp funExpr argExpr) = do
  (kenv1, ss1, funTy) <- infer'' kenv env funExpr
  (kenv2, ss2, argTy) <- infer'' kenv1 (substTyEnv ss1 env) argExpr
  retTy <- newTyVar
  let tyeq = ((substMonoTy ss2 funTy), TyFun argTy retTy)
  (kenv3, ss3) <- lift $ unify [tyeq] kenv2
  return (kenv3, mergeSubsts [ss3, ss2, ss1], substMonoTy ss3 retTy)

infer' kenv env (ERecord pairs) = do
  infers <- foldM (\sum (label, elemExpr) -> do
                    let (kenv_, env_, ss_, _) = head sum
                    let env' = substTyEnv ss_ env_
                    (kenv', ss', elemTy) <- infer'' kenv_ env' elemExpr
                    return $ (kenv', env', ss', elemTy):sum)
                  [(kenv, env, M.empty, TyVar (-1))]
                  pairs
  let (kenv', _, ss', _) = head infers
  let labels = map fst pairs
                                           -- ssを二重にかけているが大丈夫か？
  let elemTys = map (\(_, _, _, elemTy) -> substMonoTy ss' elemTy)
                    (init infers) -- 最後のダミーを除く
  return (kenv', ss', TyRecord (M.fromList $ zip labels elemTys))

infer' kenv env (ERecordRef recExpr label) = do
  (kenv1, ss1, recTy) <- infer'' kenv env recExpr
  t1@(TyVar id1) <- newTyVar
  t2@(TyVar id2) <- newTyVar
  let newKenv = M.insert id1 KiU $
                M.insert id2 (KiRecord $ M.singleton label t1) $
                kenv
  (kenv2, ss2) <- lift $ unify [(t2, recTy)] newKenv
  return (kenv2, mergeSubsts [ss2, ss1], substMonoTy ss2 t1) 

infer' kenv env (ERecModify recExpr label valExpr) = do
  (kenv1, ss1, recTy) <- infer'' kenv env recExpr
  (kenv2, ss2, valTy) <- infer'' kenv (substTyEnv ss1 env) valExpr
  t1@(TyVar id1) <- newTyVar
  t2@(TyVar id2) <- newTyVar
  let newKenv = M.insert id1 KiU $
                M.insert id2 (KiRecord $ M.singleton label t1) $
                kenv
  (kenv3, ss3) <- lift $ unify [(t1, valTy), (t2, substMonoTy ss2 recTy)]
                               newKenv
  return (kenv3, mergeSubsts [ss3, ss2, ss1], substMonoTy ss3 t2)

infer' kenv env (ECase condExpr pairs) = do
  (kenv0, ss0, condTy) <- infer'' kenv env condExpr
  infers <- foldM (\sum (label, elemExpr) -> do
                    let (kenv_, env_, ss_, _) = head sum
                    let env' = substTyEnv ss_ env_
                    (kenv', ss', elemTy) <- infer'' kenv_ env' elemExpr
                    return $ (kenv', env', ss', elemTy):sum)
                  [(kenv0, env, ss0, TyVar (-1))]
                  pairs
  let tys = map (\(_, _, _, ty) -> ty) (init infers) -- initで最後のダミーを除く
  let (kenvn, _, ssn, _) = head infers

  t0@(TyVar id0) <- newTyVar
  newTys <- mapM (\_ -> newTyVar) [1..(length pairs)]
  let newKenv = M.insert id0 KiU $
                M.union (M.fromList $ map (\(TyVar id) -> (id, KiU)) newTys) $
                kenvn
  let tyeq0 = (substMonoTy ssn condTy,   -- substを2重掛けしているが大丈夫か
               TyRecord $ M.fromList $ zip (map fst pairs) newTys)
  let tyeqs = map (\(ty, newTy) -> (substMonoTy ssn ty, TyFun newTy t0))
                  (zip tys newTys)
  (kenvn1, ssn1) <- lift $ unify (tyeq0:tyeqs) newKenv
  return (kenvn1, mergeSubsts [ssn1, ssn], substMonoTy ssn1 t0)

infer' kenv env (EVariant label valExpr) = do
  (kenv1, ss1, valTy) <- infer'' kenv env valExpr
  t@(TyVar id) <- newTyVar
  return (M.insert id (KiVariant $ M.singleton label valTy) kenv,
          ss1,
          t)

infer' kenv env (ELet name varExpr bodyExpr) = do
  (kenv1, ss1, varTy) <- infer'' kenv env varExpr
  let (kenv1', ts1) = typeClosure kenv1 (substTyEnv ss1 env) varTy
  let env' = M.insert name ts1 (substTyEnv ss1 env)
  (kenv2, ss2, bodyTy) <- infer'' kenv1' env' bodyExpr
  return (kenv2, mergeSubsts [ss2, ss1], bodyTy)

-- Main

p98 = PInt 98
p99 = PInt 99

main = hspec $ do
  describe "infer" $ do
--    it "prim" $ do
--      infer (ELit p99)
--      `shouldBe`
--      Right (0, M.empty, M.empty, TyPrim p99)
--
--    it "abs, varref" $ do
--      infer (EAbs "x" $ EVar "x")
--      `shouldBe`
--      Right (1,
--             M.singleton 0 KiU,
--             M.empty,
--             TyFun (TyVar 0) (TyVar 0))

    it "abs, record ref" $ do
      infer (EAbs "x" (ERecordRef (EVar "x") "a"))
      `shouldBe`
      Right (3,
             M.fromList [(1, KiU),
                         (2, KiRecord $ M.singleton "a" (TyVar 1))],
             M.fromList [(0, TyVar 2)],
             TyFun (TyVar 2) (TyVar 1))

--    it "app" $ do
--      infer (EApp (EAbs "x" $ EVar "x") (ELit p99))
--      `shouldBe`
--      Right (2, M.empty, M.empty, TyPrim p99)
--
--    it "record" $ do
--      infer (ERecord [("x", ELit p99)])
--      `shouldBe`
--      Right (0, M.empty, M.empty,
--             TyRecord $ M.singleton "x" (TyPrim p99))
--
--    it "record ref" $ do
--      infer (ERecordRef (ERecord [("x", ELit p99)]) "x")
--      `shouldBe`
--      Right (2, M.empty, M.empty, TyPrim p99)
--
--    it "record modify" $ do
--      infer (ERecModify (ERecord [("x", ELit p99)]) "x" (ELit p98))
--      `shouldBe`
--      Right (2, M.empty, M.empty,
--             TyRecord $ M.singleton "x" (TyPrim p99))

--    it "let" $ do
--    it "variant" $ do
--    it "case" $ do
