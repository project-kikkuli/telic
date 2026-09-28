export function rebindVar(xs: number[]): void {
  //@ ensures xs.length === 0
  var xs: number[] = [];
}

export function blockShadowParam(xs: number[]): void {
  //@ ensures xs.length === 0
  if (xs.length > 0) {
    let xs: number[] = [];
  }
}
