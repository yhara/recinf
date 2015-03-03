require 'pattern-match'

module RecInf
  class Type
    class Base

    end

    class Primitive < Base

    end

    class Fun < Base

    end

    class Record < Base

    end

    class Variant < Base

    end

  end

  class TypeVar
    class Base
    end

    class Mono < Base

    end

    class Kinded < Base

    end
  end

  class Kind
    class Base

    end

    class U < Base

    end

    class Record < Base

    end

    class Variant < Base

    end
  end

end
