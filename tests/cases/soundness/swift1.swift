// Swift exploits: every function here except the helpers listed in
// tests/test_soundness.py claims something false about the real program.

struct Point {
    var x: Int
    var y: Int
}

final class Box {
    var p: Point
    init(p: Point) {
        self.p = p
    }
}

// A struct is copied on assignment: b is not a.
func structAlias(_ a: Point) -> Int {
    //@ ensures result == 5
    var c = a
    var b = c
    b.x = 5
    return c.x
}

// ... and an array of structs holds copies too.
func arrayOfStructs(_ xs: [Point]) -> Int {
    //@ requires xs.count == 1 && xs[0].x == 0
    //@ ensures result == 1
    var ys = xs
    ys[0].x = 1
    return xs[0].x
}

// A struct passed to a function is a copy the callee cannot change.
func touch(_ b: Box, _ q: Point) -> Int {
    //@ ensures result == q.x
    b.p.x = q.x + 1
    return q.x
}

func passesAField(_ b: Box) -> Int {
    //@ requires b.p.x == 0
    //@ ensures result == 1
    return touch(b, b.p)
}

// A class is shared: a change through one reference is seen through the other.
func classAlias(_ b: Box) -> Int {
    //@ requires b.p.x < 100
    //@ ensures result == old(b.p.x)
    let c = b
    c.p.x = c.p.x + 1
    return b.p.x
}

// && binds tighter than ||: tree-sitter-swift parses this as a && (b || c).
func precedence(_ a: Bool, _ b: Bool, _ c: Bool) -> Bool {
    //@ ensures result == (a && (b || c))
    return a && b || c
}

// A prefix operator binds tighter than * but looser than member access.
func prefixMember(_ xs: [Int]) -> Bool {
    //@ ensures result == xs.isEmpty
    return !xs.isEmpty
}

// "\u{212A}" (KELVIN SIGN) is canonically equivalent to "K" in Swift.
func kelvin() -> Bool {
    //@ ensures result == false
    return "\u{212A}" == "K"
}

// Dictionary keys compare by canonical equivalence too.
func kelvinKey() -> Int {
    //@ ensures result == 0
    var d: [String: Int] = [:]
    d["K"] = 1
    return d["\u{212A}"] ?? 0
}

// Integer arithmetic traps; it does not wrap.
func overflowWraps(_ x: Int) -> Bool {
    //@ ensures result
    return x + 1 > x
}

// reduce(0, +) traps as soon as a running total overflows.
func runningTotal(_ xs: [Int]) -> Int {
    //@ requires xs.count == 3 && xs[0] == Int.max && xs[1] == 1 && xs[2] == -1
    //@ ensures result == Int.max
    return xs.reduce(0, +)
}

// % takes the sign of the dividend.
func remainderSign(_ a: Int) -> Int {
    //@ requires a == -7
    //@ ensures result == 2
    return a % 3
}

// / truncates toward zero.
func divisionRounds(_ a: Int) -> Int {
    //@ requires a == -7
    //@ ensures result == -4
    return a / 2
}

// try? turns a throw into nil.
enum Oops: Error {
    case bad
}

func mayThrow(_ x: Int) throws -> Int {
    if x < 0 {
        throw Oops.bad
    }
    return x
}

func tryOptional(_ x: Int) -> Int? {
    //@ ensures result != nil
    return try? mayThrow(x)
}

// A catch clause runs from the state at the throw, not after the call.
func catchState(_ x: Int) -> Int {
    //@ ensures result == 1
    var n = 0
    do {
        n = try mayThrow(x)
        n = 1
    } catch {
        return n
    }
    return n
}

// An inout scalar changes (telic does not model it: it must not assume it stays).
func bump(_ x: inout Int) {
    x += 1
}

func inoutScalar(_ y: Int) -> Int {
    //@ requires y < 100
    //@ ensures result == y
    var z = y
    bump(&z)
    return z
}

// A closure that captures a variable may change it whenever unchecked code runs.
func runIt(_ f: () -> Void) {
    f()
}

func captured() -> Int {
    //@ ensures result == 0
    var n = 0
    runIt { n += 1 }
    return n
}

// A protocol call is checked against the requirement's contract, not a conformer's body.
protocol Metric {
    //@ ensures result >= 0
    func size() -> Int
}

struct Ten: Metric {
    func size() -> Int {
        return 10
    }
}

struct Three: Metric {
    func size() -> Int {
        return 3
    }
}

func throughProtocol(_ m: Metric) -> Int {
    //@ ensures result == 10
    return m.size()
}

// A public protocol may have conformers outside these files.
public protocol Open {
    func value() -> Int
}

struct Five: Open {
    func value() -> Int {
        return 5
    }
}

struct Six: Open {
    func value() -> Int {
        return 6
    }
}

func openProtocol(_ o: Open) -> Int {
    //@ ensures result == 5
    return o.value()
}

// A payload enum's unused slots do not take part in ==.
enum Tag: Equatable {
    case a(Int)
    case b(Int)
}

func tagEquality(_ t: Tag, _ u: Tag) -> Bool {
    //@ requires t == .a(1)
    //@ ensures result == (u == .a(1))
    return t == u && false
}

// Shadowing: the inner x is a different variable.
func shadow() -> Int {
    //@ ensures result == 2
    let x = 1
    if x > 0 {
        let x = 2
        _ = x
    }
    return x
}

// A switch 'break' leaves the switch, not the loop.
func switchBreak(_ n: Int) -> Int {
    //@ requires n == 3
    //@ ensures result == 1
    var count = 0
    for i in 0..<n {
        switch i {
        case 1: break
        default: count += 1
        }
    }
    return count
}

// Double arithmetic does not overflow, but Int(d) traps outside Int's range.
func doubleToInt(_ d: Double) -> Int {
    //@ ensures true
    return Int(d * 2)
}
