// Swift exploits from an adversarial review: conformers and subclasses telic
// does not model must keep a protocol or class open, and no statement may be
// dropped. Every function here except the helpers listed in
// tests/test_soundness.py claims something false.

// fallthrough runs the next case too (tree-sitter leaves it an unnamed token).
func fall(_ n: Int) -> Int {
    //@ requires n == 1
    //@ ensures result == 1
    var r = 0
    switch n {
    case 1:
        r += 1
        fallthrough
    case 2:
        r += 10
    default:
        r += 100
    }
    return r
}

// A conformer declared through a type alias.
protocol Positive {
    //@ ensures result > 0
    func value() -> Int
}

typealias PositiveAlias = Positive

struct One: Positive {
    func value() -> Int {
        return 1
    }
}

struct Negative: PositiveAlias {
    func value() -> Int {
        return -5
    }
}

func throughAlias(_ p: Positive) -> Int {
    //@ ensures result > 0
    return p.value()
}

// A conformer nested in another type.
protocol Small {
    //@ ensures result < 10
    func size() -> Int
}

struct Outer {
    struct Inner: Small {
        func size() -> Int {
            return 99
        }
    }
}

func throughNested(_ s: Small) -> Int {
    //@ ensures result < 10
    return s.size()
}

// A conformer declared inside a function.
protocol Even {
    //@ ensures result % 2 == 0
    func half() -> Int
}

func makeOdd() -> Int {
    struct Odd: Even {
        func half() -> Int {
            return 3
        }
    }
    return 0
}

func throughLocal(_ e: Even) -> Int {
    //@ ensures result % 2 == 0
    return e.half()
}

// A conformance only some instantiations have.
protocol Tiny {
    //@ ensures result < 5
    func n() -> Int
}

struct Box<T> {
    var t: T
}

extension Box: Tiny where T == Int {
    func n() -> Int {
        return 50
    }
}

func throughConstrained(_ t: Tiny) -> Int {
    //@ ensures result < 5
    return t.n()
}

// Subclasses through an alias and nested in a type.
class Base {
    init() {}
    func v() -> Int {
        return 1
    }
}

typealias BaseAlias = Base

class ViaAlias: BaseAlias {
    override func v() -> Int {
        return 3
    }
}

func throughBase(_ b: Base) -> Int {
    //@ ensures result == 1
    return b.v()
}

// A lazy property is computed on first use, from the state at that time.
final class Lazy {
    var n: Int
    lazy var cached: Int = n + 1

    init() {
        n = 0
    }
}

func lazyRead(_ l: Lazy) -> Int {
    //@ ensures result == 1
    l.n = 5
    return l.cached
}
