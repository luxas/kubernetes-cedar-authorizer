//! R-10: Lean (cedar-spec #1015, type-erased printer) vs Rust (cedar #2581, EST JSON) residuals.
use spike::audit::*;

#[test]
fn r10_lean_and_rust_residuals_agree() {
    let golden = std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/lean/R10.out")).unwrap();
    let mut lean: Vec<(String, String, String)> = golden.lines().map(|l| {
        let mut it = l.splitn(3, '|');
        (it.next().unwrap().into(), it.next().unwrap().into(), it.next().unwrap().into())
    }).collect();
    lean.sort();
    let (s, ps) = (schema(), kep5());
    let mut rust = vec![];
    for sc in scenarios() {
        for (id, c) in canonical_residuals(&s, &ps, &sc) { rust.push((sc.name.to_string(), id, c)); }
    }
    rust.sort();
    assert!(lean.len() >= 20, "vacuity guard: {} Lean rows", lean.len());
    assert!(lean.iter().all(|(_, _, c)| !c.starts_with("LEAN-ERROR")), "{lean:?}");
    // at least one non-trivial residual per scenario and at least one decided one
    assert!(lean.iter().filter(|(_, _, c)| c.starts_with("(and")).count() >= 10);
    assert!(lean.iter().any(|(_, _, c)| c == "true") && lean.iter().any(|(_, _, c)| c == "false"));
    assert_eq!(lean.len(), rust.len());
    for (l, r) in lean.iter().zip(rust.iter()) {
        assert_eq!(l, r, "Lean vs Rust residual differ");
    }
}

#[test]
fn r10_mutation_is_detected() {
    // flipping one character of a Lean row must make the comparison fail
    let golden = std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/lean/R10.out")).unwrap();
    let mutated = golden.replacen("\"alice\"", "\"alicf\"", 1);
    assert_ne!(golden, mutated);
    let (s, ps) = (schema(), kep5());
    let sc = &scenarios()[0];
    let rust = canonical_residuals(&s, &ps, sc);
    let row = mutated.lines().find(|l| l.starts_with("create|owner|")).unwrap();
    assert_ne!(row.splitn(3, '|').nth(2).unwrap(), rust["owner"]);
}
