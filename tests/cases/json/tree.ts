// A binary tree parsed from JSON, validated by a trusted predicate.
type int = number;

//@ trusted
//@ ensures result >= 0
function depth(t: any): int {
  if (t === null || typeof t !== "object") return 0;
  let d = 0;
  for (const v of Object.values(t)) d = Math.max(d, depth(v));
  return d + 1;
}

//@ trusted
//@ ensures result === (typeof t === "object" && t !== null && "kind" in t
//@   && (t.kind === "leaf" && typeof t.value === "number"
//@       || t.kind === "node" && "left" in t && "right" in t && wfTree(t.left) && wfTree(t.right)
//@          && depth(t.left) < depth(t) && depth(t.right) < depth(t)))
function wfTree(t: any): boolean {
  if (typeof t !== "object" || t === null || !("kind" in t)) return false;
  if (t.kind === "leaf") return typeof t.value === "number";
  return t.kind === "node" && "left" in t && "right" in t && wfTree(t.left) && wfTree(t.right);
}

//@ requires wfTree(t)
//@ decreases depth(t)
//@ ensures result >= 1
function leaves(t: any): int {
  if (t.kind === "leaf") return 1;
  if (t.kind === "node") return leaves(t.left) + leaves(t.right);
  throw new Error("not a tree");
}

//@ requires wfTree(t)
//@ decreases depth(t)
//@ ensures result >= 2
function overclaims(t: any): int {
  if (t.kind === "leaf") return 1;
  if (t.kind === "node") return overclaims(t.left) + overclaims(t.right);
  throw new Error("not a tree");
}
