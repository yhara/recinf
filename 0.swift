// Util

protocol Inspectable {
  func inspect() -> String
}

// Types

enum Prim : Inspectable {
  case PBool(Bool)
  case PInt(Int)

  func inspect() -> String {
    switch(self) {
      case .PBool(let b): return b ? "true" : "false"
      case .PInt(let i): return String(i)
    }
  }
}

enum TyScm : Inspectable {
  case TyPrim(Prim)
  case TyVar(Int)
  case TyFun(TyScm, TyScm)

  func inspect() -> String {
    return "TODO"
  }
}

// Main

enum Barcode : Inspectable {
  case UPCA(Int, Int, Int, Int)
  case QRCode(String)

  func inspect() -> String {
    switch(self) {
    case .UPCA:
      return "upca"
     case .QRCode:
      return "qr"
    }
  }
}


var productBarcode = Barcode.UPCA(8, 85909, 51226, 3)

println(productBarcode.inspect())
