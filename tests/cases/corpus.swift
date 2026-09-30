// Verdict corpus for the Swift frontend: `// expect: <verdict>` above each
// function pins what telic must report. The file is valid Swift (compiled by
// tests/test_swift.py with swiftc when it is installed); every refutation is
// replayed there.

// MARK: integers

// expect: proved
func addSmall(_ a: Int, _ b: Int) -> Int {
    //@ requires a >= 0 && a <= 1000 && b >= 0 && b <= 1000
    //@ ensures result == a + b
    return a + b
}

// expect: refuted
func addAny(_ a: Int, _ b: Int) -> Int {
    return a + b
}

// expect: refuted
func inc8(_ x: Int8) -> Int8 {
    return x + 1
}

// expect: proved
func wrapInc(_ x: UInt8) -> UInt8 {
    //@ ensures x == 255 ? result == 0 : result == x + 1
    return x &+ 1
}

// expect: refuted
func ratio(_ a: Int, _ b: Int) -> Int {
    //@ requires b != 0
    return a / b
}

// expect: proved
func ratioPositive(_ a: Int, _ b: Int) -> Int {
    //@ requires b > 0
    //@ ensures result * b <= a || a < 0
    return a / b
}

// expect: proved
func remainderSign(_ a: Int) -> Int {
    //@ requires a < 0
    //@ ensures result <= 0 && result > -3
    return a % 3
}

// expect: proved
func even(_ n: Int) -> Bool {
    //@ ensures result == (n % 2 == 0)
    return n.isMultiple(of: 2)
}

// expect: proved
func precedence(_ a: Bool, _ b: Bool, _ c: Bool) -> Bool {
    //@ ensures result == ((a && b) || c)
    return a && b || c
}

// expect: proved
func negate(_ a: Int, _ b: Int) -> Int {
    //@ requires a >= -100 && a <= 100 && b >= -100 && b <= 100
    //@ ensures result == (0 - a) * b + 1
    return -a * b + 1
}

// expect: refuted
func negateMin(_ a: Int) -> Int {
    return -a
}

// expect: proved
func half(_ x: Double) -> Double {
    //@ ensures result * 2 == x
    return x / 2
}

// expect: refuted
func narrow(_ x: Int) -> Int8 {
    return Int8(x)
}

// MARK: arrays

// expect: refuted
func first(_ xs: [Int]) -> Int {
    return xs[0]
}

// expect: proved
func firstChecked(_ xs: [Int]) -> Int {
    //@ requires !xs.isEmpty
    return xs[0]
}

// expect: proved
func lastIndex(_ xs: [Int]) -> Int {
    //@ ensures result == xs.count - 1
    return xs.count - 1
}

// expect: proved
func total(_ xs: [Int]) -> Int {
    //@ requires xs.allSatisfy { $0 >= 0 && $0 <= 100 }
    //@ requires xs.count <= 1000
    //@ ensures result >= 0
    var t = 0
    //@ invariant t >= 0 && t <= 100 * i
    for i in 0..<xs.count {
        t += xs[i]
    }
    return t
}

// expect: refuted
func dropLast(_ xs: [Int]) -> [Int] {
    var ys = xs
    ys.removeLast()
    return ys
}

// expect: proved
func appendOne(_ xs: [Int]) -> [Int] {
    //@ ensures result.count == xs.count + 1
    //@ ensures result[xs.count] == 1
    var ys = xs
    ys.append(1)
    return ys
}

// expect: proved
func clampAll(_ xs: [Int]) -> [Int] {
    //@ ensures result.count == xs.count
    //@ ensures result.allSatisfy { $0 >= 0 }
    var out: [Int] = []
    //@ invariant out.count == i && out.allSatisfy { $0 >= 0 }
    for (i, x) in xs.enumerated() {
        out.append(max(x, 0))
    }
    return out
}

// expect: proved
func countDown(_ n: Int) -> Int {
    //@ requires n >= 0 && n <= 1000
    //@ ensures result == n
    var k = 0
    //@ invariant k == n - i
    for i in (0..<n).reversed() {
        k += 1
    }
    return k
}

// expect: proved
func zeroOut(_ xs: inout [Int]) {
    //@ requires !xs.isEmpty
    //@ ensures xs[0] == 0 && xs.count == old(xs.count)
    xs[0] = 0
}

// MARK: optionals

// expect: refuted
func force(_ x: Int?) -> Int {
    return x!
}

// expect: proved
func orZero(_ x: Int?) -> Int {
    //@ ensures x == nil ? result == 0 : result == x!
    return x ?? 0
}

// expect: proved
func guardLet(_ x: Int?, _ y: Int?) -> Int {
    //@ requires x == nil || x! >= 0 && x! <= 100
    //@ requires y == nil || y! >= 0 && y! <= 100
    //@ ensures result >= 0
    guard let a = x, let b = y else { return 0 }
    return a + b
}

// expect: proved
func ifLet(_ x: Int?) -> Int {
    //@ ensures result >= 0
    if let v = x, v > 0 {
        return v
    }
    return 0
}

// MARK: structs (value semantics) and invariants

struct Interval: Equatable {
    //@ invariant lo <= hi
    var lo: Int
    var hi: Int

    init(lo: Int, hi: Int) {
        //@ requires lo <= hi
        self.lo = lo
        self.hi = hi
    }

    // expect: refuted
    var width: Int {
        return hi - lo
    }

    // expect: proved
    func contains(_ x: Int) -> Bool {
        //@ ensures result == (lo <= x && x <= hi)
        return lo <= x && x <= hi
    }

    // expect: proved
    mutating func widen(by k: Int) {
        //@ requires k >= 0 && hi <= Int.max - k
        //@ ensures hi == old(hi) + k && lo == old(lo)
        hi += k
    }

    // expect: refuted
    mutating func shift(by k: Int) {
        //@ requires k >= -1000 && k <= 1000 && lo >= -1000 && lo <= 1000
        lo += k
    }
}

// expect: proved
func copyIsIndependent(_ r: Interval) -> Int {
    //@ requires r.lo == 0 && r.hi == 10
    //@ ensures result == 0
    let a = r
    var b = a
    b.lo = 5
    return a.lo
}

// expect: proved
func sameInterval(_ a: Interval) -> Bool {
    //@ ensures result
    let b = a
    return a == b
}

// expect: proved
func unit(_ x: Int) -> Interval {
    //@ requires x < Int.max
    return Interval(lo: x, hi: x + 1)
}

// MARK: classes (reference semantics) and invariants

enum BankError: Error {
    case insufficient
}

final class Account {
    //@ invariant balance >= 0
    var balance: Int

    init(balance: Int) {
        //@ requires balance >= 0
        self.balance = balance
    }

    // expect: proved
    func deposit(_ amount: Int) {
        //@ requires amount >= 0 && balance <= Int.max - amount
        //@ ensures balance == old(balance) + amount
        balance += amount
    }

    // expect: refuted
    func withdraw(_ amount: Int) {
        //@ requires amount >= 0
        balance -= amount
    }

    // expect: proved
    func withdrawChecked(_ amount: Int) throws {
        //@ requires amount >= 0
        //@ raises amount > balance
        //@ ensures balance == old(balance) - amount
        guard amount <= balance else { throw BankError.insufficient }
        balance -= amount
    }
}

// expect: proved
func sharedAccount(_ a: Account) -> Int {
    //@ requires a.balance <= 100
    //@ ensures result == old(a.balance) + 5
    let b = a
    b.deposit(5)
    return a.balance
}

// expect: proved
func tryWithdraw(_ a: Account, _ amount: Int) -> Bool {
    //@ requires amount >= 0
    //@ ensures result == (amount <= old(a.balance))
    do {
        try a.withdrawChecked(amount)
        return true
    } catch {
        return false
    }
}

// MARK: enums and switch

enum Light {
    case red, yellow, green
}

// expect: proved
func next(_ l: Light) -> Light {
    //@ ensures result != l
    switch l {
    case .red: return .green
    case .green: return .yellow
    case .yellow: return .red
    }
}

enum Shape: Equatable {
    case circle(r: Double)
    case rect(w: Double, h: Double)
    case empty
}

// expect: refuted
func area(_ s: Shape) -> Double {
    //@ ensures result >= 0
    switch s {
    case .circle(let r): return 3 * r * r
    case let .rect(w, h): return w * h
    case .empty: return 0
    }
}

// expect: proved
func isEmpty(_ s: Shape) -> Bool {
    //@ ensures result == (s == .empty)
    if case .empty = s {
        return true
    }
    return false
}

// expect: proved
func scaled(_ s: Shape) -> Shape {
    //@ ensures s == .empty ? result == .empty : true
    switch s {
    case .circle(let r): return .circle(r: r * 2)
    case .rect(let w, let h): return .rect(w: w * 2, h: h * 2)
    case .empty: return .empty
    }
}

enum Status: Int {
    case ok = 200
    case notFound = 404
    case teapot = 418
}

// expect: proved
func isError(_ s: Status) -> Bool {
    //@ ensures result == (s.rawValue >= 400)
    return s.rawValue >= 400
}

// expect: proved
func grade(_ score: Int) -> Int {
    //@ ensures result >= 0 && result <= 2
    switch score {
    case ..<50: return 0
    case 50...79: return 1
    default: return 2
    }
}

// MARK: errors

enum ParseError: Error {
    case notPositive
}

// expect: proved
func positive(_ x: Int) throws -> Int {
    //@ raises x <= 0
    //@ ensures result == x
    if x <= 0 {
        throw ParseError.notPositive
    }
    return x
}

// expect: refuted
func positiveLoose(_ x: Int) throws -> Int {
    //@ raises x < 0
    if x <= 0 {
        throw ParseError.notPositive
    }
    return x
}

// expect: proved
func positiveOrZero(_ x: Int) -> Int {
    //@ ensures result >= 0
    do {
        return try positive(x)
    } catch {
        return 0
    }
}

// expect: proved
func positiveOptional(_ x: Int) -> Int? {
    //@ ensures x > 0 ? result == x : result == nil
    return try? positive(x)
}

// expect: refuted
func positiveForced(_ x: Int) -> Int {
    return try! positive(x)
}

// MARK: protocols

protocol HasArea {
    //@ ensures result >= 0
    func area() -> Int
}

struct Square: HasArea {
    //@ invariant side >= 0 && side <= 1000
    var side: Int

    // expect: proved
    func area() -> Int {
        return side * side
    }
}

struct Signed: HasArea {
    var k: Int

    // expect: refuted
    func area() -> Int {
        return k
    }
}

// expect: proved
func biggerArea(_ a: HasArea, _ b: HasArea) -> Int {
    //@ ensures result >= 0
    return max(a.area(), b.area())
}

// expect: proved
func largest<S: HasArea>(_ xs: [S]) -> Int {
    //@ ensures result >= 0
    var best = 0
    //@ invariant best >= 0
    for x in xs {
        best = max(best, x.area())
    }
    return best
}

// MARK: generics

// expect: proved
func middle<T>(_ xs: [T]) -> T {
    //@ requires !xs.isEmpty
    return xs[xs.count / 2]
}

// expect: refuted
func secondOf<T>(_ xs: [T]) -> T {
    //@ requires !xs.isEmpty
    return xs[1]
}

// MARK: dictionaries

// expect: proved
func lookup(_ d: [Int: Int], _ k: Int) -> Int {
    //@ ensures d[k] == nil ? result == 0 : result == d[k]!
    return d[k] ?? 0
}

// expect: proved
func setThenGet(_ k: Int) -> Int {
    //@ ensures result == 5
    var d: [Int: Int] = [:]
    d[k] = 5
    return d[k]!
}

// expect: refuted
func missing(_ d: [Int: Int]) -> Int {
    return d[3]!
}

// expect: proved
func removed(_ d: [String: Int], _ k: String) -> Bool {
    //@ ensures result
    var e = d
    e[k] = nil
    return e[k] == nil
}

// MARK: strings

// expect: proved
func greet(_ name: String) -> String {
    //@ ensures result == "Hello, " + name
    return "Hello, " + name
}

// expect: proved
func emptyName(_ name: String) -> Bool {
    //@ ensures result == name.isEmpty
    return name == ""
}
