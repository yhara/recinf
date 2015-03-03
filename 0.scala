sealed trait Tree[T]
case class Node[T](left: Tree[T], right: Tree[T]) extends Tree[T]
case class Leaf[T](value: T) extends Tree[T]

sealed trait TyScm
case class TyVar(id: Int) extends TyScm
case class TyFun(ts1: TyScm, ts2: TyScm) extends TyScm



print(1)
