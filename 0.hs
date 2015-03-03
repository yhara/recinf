--{-# LANGUAGE TypeSynonymInstances #-}
-- 

type Label = String
type Name = String

-- Types

data Prim = PBool | PInt
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

-- p.165 なぜ型変数、型スキーマが必要か？
-- 「与えられた式に対して、それを満たす型判定の集合を求める」には、
-- 型判定の集合(一般には無限)を表す方法が必要。
-- そこで型変数を使って、「(a->a)->a」みたいに表す。
-- 型スキーマ＝型変数を含んだ型

type Subst = [(VId, TyScm)]

substTyScm :: Subst -> TyScm -> TyScm
substTyScm ss orig@(TyPrim _) = orig
substTyScm ss orig@(TyVar i) =
  case lookup i ss of
    Just ts -> ts
    Nothing -> orig
substTyScm ss (TyFun ts1 ts2) =
  TyFun (substTyScm ss ts1) (substTyScm ss ts2)

substSubst :: Subst -> Subst -> Subst
substSubst ss target = map substEntry target
  where substEntry (vid, tyscm) = (vid, substTyScm ss tyscm)

-- Unification

type TyEq = (TyScm, TyScm)
type Constraints = ([TyEq], Subst)

substTyEq :: Subst -> TyEq -> TyEq
substTyEq ss (t1, t2) = (substTyScm ss t1, substTyScm ss t2)

unify :: Constraints -> Constraints
unify ([], subst) = ([], subst)

unify ((ts1, ts2):tyeqs, subst) =
  case (ts1, ts2) of
    (TyVar id1, TyVar id2) | id1 == id2 ->
      unify (tyeqs, subst)
    (TyVar id1, _) -> 
      let ss = [(id1, ts2)] in
        unify ((map (substTyEq ss) tyeqs),
               ss ++ (substSubst ss subst))
    (_, TyVar id2) ->
      unify ((ts2, ts1):tyeqs, subst)
    (TyFun t1 t2, TyFun t3 t4) ->
      unify ((t1, t3):(t2, t4):tyeqs, subst)

-- Main

ts = [
  (TyVar 1, TyVar 2),
  (TyVar 2, TyPrim PBool)
  ]
main = print $ unify (ts, [])

