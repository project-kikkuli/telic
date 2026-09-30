// Closures handed on as values run where telic cannot see the call: given to
// std methods that call them on each element, or stored. Each closure traps
// for some element or captured value.

func pos(_ x: Int) -> Int {
    //@ requires x > 0
    return 10 / x
}

func sortedDiv(_ xs: [Int]) -> Int {
    //@ ensures result == 0
    let ys = xs.sorted { 10 / $0 < 10 / $1 }
    _ = ys
    return 0
}

func forEachDiv(_ xs: [Int]) -> Int {
    //@ ensures result == 0
    xs.forEach { x in
        let y = 10 / x
        print(y)
    }
    return 0
}

func stored(_ n: Int) -> Int {
    //@ ensures result == 0
    let h = { pos(n) }
    _ = h
    return 0
}
