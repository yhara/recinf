-- 単相型推論＋組型
import Test.Hspec
import qualified Data.Map as M
import Control.Monad (foldM)
--{-# LANGUAGE TypeSynonymInstances #-}
-- 

type Label = String
type Name = String

-- Types

data Prim = PBool Bool | PInt Int
  deriving (Eq, Show)
type VId = Int
data MonoTy = TyPrim Prim
           | TyVar VId
           | TyFun MonoTy MonoTy
           | TyTuple Int [MonoTy]
           | TyVariant Int [MonoTy]
  deriving (Eq, Show)

ftv :: MonoTy -> [VId]
ftv (TyPrim _) = []
ftv (TyVar i) = [i]
ftv (TyFun ts1 ts2) = (ftv ts1) ++ (ftv ts2)

occurs :: Int -> MonoTy -> Bool
occurs i (TyPrim _) = False
occurs i (TyVar ii) = (i == ii)
occurs i (TyFun ts1 ts2) = occurs i ts1 || occurs i ts2

-- p.165 なぜ型変数、型スキーマが必要か？
-- 「与えられた式に対して、それを満たす型判定の集合を求める」には、
-- 型判定の集合(一般には無限)を表す方法が必要。
-- そこで型変数を使って、「(a->a)->a」みたいに表す。
-- 型スキーマ＝型変数を含んだ型

type Subst = [(VId, MonoTy)]

substMonoTy :: Subst -> MonoTy -> MonoTy
substMonoTy ss orig@(TyPrim _) = orig
substMonoTy ss orig@(TyVar i) =
  case Prelude.lookup i ss of
    Just ts -> ts
    Nothing -> orig
substMonoTy ss (TyFun ts1 ts2) =
  TyFun (substMonoTy ss ts1) (substMonoTy ss ts2)

substSubst :: Subst -> Subst -> Subst
substSubst ss target = Prelude.map substEntry target
  where substEntry (vid, tyscm) = (vid, substMonoTy ss tyscm)

-- Unification

type TyEq = (MonoTy, MonoTy)
type Constraints = ([TyEq], Subst)

substTyEq :: Subst -> TyEq -> TyEq
substTyEq ss (t1, t2) = (substMonoTy ss t1, substMonoTy ss t2)

unify :: [TyEq] -> Maybe Subst
unify tyeqs = unify' tyeqs []
  where
    unify' [] subst = Just subst
    unify' ((ts1, ts2):rest) subst =
      case (ts1, ts2) of
        (TyVar id1, TyVar id2) | id1 == id2 ->
          unify' rest subst
        (TyVar id1, _) -> 
          if occurs id1 ts2
          then Nothing
          else let ss = [(id1, ts2)] in
                 unify' (Prelude.map (substTyEq ss) rest)
                        (ss ++ (substSubst ss subst))
        (_, TyVar id2) ->
          unify' ((ts2, ts1):rest) subst
        (TyFun t1 t2, TyFun t3 t4) ->
          unify' ((t1, t3):(t2, t4):rest) subst
        (TyTuple n1 tys1, TyTuple n2 tys2) ->
          if (n1 /= n2) || (length tys1 /= length tys2)
          then Nothing
          else unify' (zip tys1 tys2) subst
        --(TyVariant n tys) ->

-- Inference

data Expr
  = ELit Prim 
  | EVar Name
  | EAbs Name Expr
  | EApp Expr Expr

  | ETuple [Expr]
  | ETupleRef Expr Int Int    -- e.i[n]
  | EVariant Int Expr Int -- (<i=e>:n)
  | ECase Expr [Expr]         -- case e of e1,e2,...en
  deriving (Eq, Show)

type TyEnv = M.Map Name MonoTy --[(VId, MonoTy)]
substTyEnv :: Subst -> TyEnv -> TyEnv
substTyEnv ss env = M.map (substMonoTy ss) env 

-- p.171のmatches
-- matches({e1,...,en}) = ...
--   各eiとejについて
--     両者で重複しているキーxについて,(ei[x],ej[x])をとる
-- つまり、e1,...,enからすべての方程式を抽出する
extractTyEqs :: [TyEnv] -> [TyEq]
extractTyEqs envs = concat [extractTyEq2 e1 e2 | e1 <- envs, e2 <- envs]
  where
    extractTyEq2 :: TyEnv -> TyEnv -> [TyEq]
    extractTyEq2 e1 e2 = M.elems $ M.intersectionWith (,) e1 e2

infer :: Int -> Expr -> Maybe (Int, TyEnv, MonoTy)
infer i (ELit prim) =
  Just (i, M.empty, TyPrim prim)
infer i (EVar name) =
  Just (i+1, M.singleton name (TyVar i), TyVar i)
infer i (EAbs name expr) = do
  (i', env, tret) <- infer i expr
  case M.lookup name env of
    Just targ -> Just (i', M.delete name env, TyFun targ tret)
    Nothing -> Just (i'+1, env, TyFun (TyVar i') tret)
infer i (EApp fexpr aexpr) = do
  (i',  e1, t1) <- infer i fexpr
  (i'', e2, t2) <- infer i' aexpr
  let tret = TyVar i''
  ss <- unify ((extractTyEqs [e1, e2]) ++ [(t1, TyFun t2 tret)])
  return (i''+1,
          M.union (substTyEnv ss e1) (substTyEnv ss e2),
          substMonoTy ss tret)

infer i (ETuple exprs) = do
  let l = length exprs
  (i', envs, tys) <- foldM (\(ii, envs, tys) expr -> do
                            (ii', env', ty') <- infer ii expr
                            return (ii', env':envs, ty':tys))
                          (i, [], [])
                          exprs
  ss <- unify (extractTyEqs envs)
  let newenv = substTyEnv ss (M.unions envs)
  let tuplety = TyTuple (length exprs) (map (substMonoTy ss) tys)
  return (i+l, newenv, tuplety)

infer i (ETupleRef tupleExpr idx nElms) = do
  (i', env, ty1) <- infer i tupleExpr
  let tyvars = map TyVar [i'..i'+nElms-1]
  let ty2 = TyTuple nElms tyvars
  ss <- unify [(ty1, ty2)]
  return (i'+nElms, substTyEnv ss env, substMonoTy ss (tyvars !! idx))

infer i (EVariant idx valExpr nElms) = undefined
infer i (ECase valExpr caseExprs) = undefined

-- Main

--ts = [
--  (TyVar 1, TyVar 2),
--  (TyVar 2, TyPrim PBool)
--  ]
--main = print $ unify (ts, [])
--

p98 = PInt 98
p99 = PInt 99
pTrue = PBool True
pFalse = PBool False

main = hspec $ do
  describe "ftv" $ do
    it "primitive" $ do
      ftv (TyPrim $ PBool True) `shouldBe` []

    it "var" $ do
      ftv (TyVar 3) `shouldBe` [3]

    it "fun" $ do
      ftv (TyFun (TyVar 3) (TyPrim $ PInt 99)) `shouldBe` [3]
  
  describe "infer" $ do
    it "primitive" $ do
      infer 0 (ELit $ PInt 99)
      `shouldBe`
      Just (0, M.empty, (TyPrim $ PInt 99))

    it "varref" $ do
      infer 0 (EVar "x")
      `shouldBe`
      Just (1, M.fromList [("x", TyVar 0)], (TyVar 0))

    it "abs" $ do
      infer 0 (EAbs "x" (EVar "x"))
      `shouldBe`
      Just (1, M.empty, (TyFun (TyVar 0) (TyVar 0)))

    it "tuple" $ do
      infer 0 (ETuple [ELit p99, ELit p99])
      `shouldBe`
      Just (2, M.empty, (TyTuple 2 [TyPrim p99, TyPrim p99]))

    it "tupleRef" $ do
      infer 0 (ETupleRef (ETuple [ELit p98, ELit pTrue]) 1 2)
      `shouldBe`
      Just (4, M.empty, TyPrim p98)

    it "variant" $ do
      infer 0 (EVariant 1 (ELit p99) 2)
      `shouldBe`
      Just (1, M.empty, TyVariant 2 [TyVar 0, TyPrim p99])

--    it "case" $ do
--      infer 0 (ECase (EVariant 1 (ELit p99) 2)
--                [(EAbs "b" 
--      `shouldBe`
--      Just (1, M.empty, TyVariant 2 [TyVar 0, TyPrim p99])
