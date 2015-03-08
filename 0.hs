import Test.Hspec
import Data.Map
--{-# LANGUAGE TypeSynonymInstances #-}
-- 

type Label = String
type Name = String

-- Types

data Prim = PBool Bool | PInt Int
  deriving (Eq, Show)
type VId = Int
data TyScm = TyPrim Prim
           | TyVar VId
           | TyFun TyScm TyScm
  deriving (Eq, Show)

ftv :: TyScm -> [VId]
ftv (TyPrim _) = []
ftv (TyVar i) = [i]
ftv (TyFun ts1 ts2) = (ftv ts1) ++ (ftv ts2)

occurs :: Int -> TyScm -> Bool
occurs i (TyPrim _) = False
occurs i (TyVar ii) = (i == ii)
occurs i (TyFun ts1 ts2) = occurs i ts1 || occurs i ts2

-- p.165 なぜ型変数、型スキーマが必要か？
-- 「与えられた式に対して、それを満たす型判定の集合を求める」には、
-- 型判定の集合(一般には無限)を表す方法が必要。
-- そこで型変数を使って、「(a->a)->a」みたいに表す。
-- 型スキーマ＝型変数を含んだ型

type Subst = Map VId TyScm

substTyScm :: Subst -> TyScm -> TyScm
substTyScm ss orig@(TyPrim _) = orig
substTyScm ss orig@(TyVar i) =
  case Data.Map.lookup i ss of
    Just ts -> ts
    Nothing -> orig
substTyScm ss (TyFun ts1 ts2) =
  TyFun (substTyScm ss ts1) (substTyScm ss ts2)

substSubst :: Subst -> Subst -> Subst
substSubst ss target = Data.Map.map (substTyScm ss) target

-- Unification

type TyEq = (TyScm, TyScm)
type Constraints = ([TyEq], Subst)

substTyEq :: Subst -> TyEq -> TyEq
substTyEq ss (t1, t2) = (substTyScm ss t1, substTyScm ss t2)

unify :: [TyEq] -> Maybe Subst
unify tyeqs = unify' tyeqs Data.Map.empty
  where
    unify' [] subst = Just subst
    unify' ((ts1, ts2):rest) subst =
      case (ts1, ts2) of
        (TyVar id1, TyVar id2) | id1 == id2 ->
          unify' rest subst
        (TyVar id1, _) -> 
          if occurs id1 ts2
          then Nothing
          else let ss = Data.Map.singleton id1 ts2 in
                 unify' (Prelude.map (substTyEq ss) rest)
                        (union ss (substSubst ss subst))
        (_, TyVar id2) ->
          unify' ((ts2, ts1):rest) subst
        (TyFun t1 t2, TyFun t3 t4) ->
          unify' ((t1, t3):(t2, t4):rest) subst

-- Inference

data Expr
  = ELit Prim 
  | EVar Name
  | EAbs Name Expr
  | EApp Expr Expr
  deriving (Eq, Show)

type TyEnv = Map Name TyScm --[(VId, TyScm)]
substTyEnv :: Subst -> TyEnv -> TyEnv
substTyEnv ss env = Data.Map.map (substTyScm ss) env 

-- p.171のmatches
-- matches({e1,...,en}) = ...
--   各eiとejについて
--     両者で重複しているキーxについて,(ei[x],ej[x])をとる
-- つまり、e1,...,enからすべての方程式を抽出する
extractTyEqs :: TyEnv -> TyEnv -> [TyEq]
extractTyEqs e1 e2 = elems $ intersectionWith (,) e1 e2

infer :: Int -> Expr -> Maybe (Int, TyEnv, TyScm)
infer i (ELit prim) =
  Just (i, Data.Map.empty, TyPrim prim)
infer i (EVar name) =
  Just (i+1, Data.Map.singleton name (TyVar i), TyVar i)
infer i (EAbs name expr) = do
  (i', env, tret) <- infer i expr
  case Data.Map.lookup name env of
    Just targ -> Just (i', delete name env, TyFun targ tret)
    Nothing -> Just (i'+1, env, TyFun (TyVar i') tret)
infer i (EApp fexpr aexpr) = do
  (i',  e1, t1) <- infer i fexpr
  (i'', e2, t2) <- infer i' aexpr
  let tret = TyVar i''
  ss <- unify ((extractTyEqs e1 e2) ++ [(t1, TyFun t2 tret)])
  return (i''+1,
          union (substTyEnv ss e1) (substTyEnv ss e2),
          substTyScm ss tret)

-- Main

--ts = [
--  (TyVar 1, TyVar 2),
--  (TyVar 2, TyPrim PBool)
--  ]
--main = print $ unify (ts, [])
--

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
      Just (0, empty, (TyPrim $ PInt 99))

    it "varref" $ do
      infer 0 (EVar "x")
      `shouldBe`
      Just (1, fromList [("x", TyVar 0)], (TyVar 0))

    it "abs" $ do
      infer 0 (EAbs "x" (EVar "x"))
      `shouldBe`
      Just (1, empty, (TyFun (TyVar 0) (TyVar 0)))
