use spike::r13::*;
fn main() {
    let mut ok = 0; let mut n = 0;
    let (mut dropped, mut coerced, mut pairs, mut fl, mut opq, mut mns, mut rec) = (0, 0, 0, 0, 0, 0, 0);
    for stem in fixtures(true) {
        match run(&stem) {
            None => println!("{stem:<60} (no OpenAPI schema, skipped)"),
            Some(r) => {
                n += 1;
                if r.result.is_ok() { ok += 1; }
                dropped += r.dropped; coerced += r.coerced; pairs += r.map_pairs;
                fl += r.gen.dropped_float; opq += r.gen.dropped_opaque; mns += r.gen.dropped_map_non_string; rec += r.gen.dropped_recursion;
                println!("{:<60} {:<5} dropped={} coerced={} maps={} attrs={} float={} opaque={} recursion={} {}", r.stem,
                    if r.result.is_ok() { "OK" } else { "FAIL" }, r.dropped, r.coerced, r.map_pairs, r.gen.attrs, r.gen.dropped_float, r.gen.dropped_opaque, r.gen.dropped_recursion,
                    r.result.as_ref().err().map(|e| e.chars().take(150).collect::<String>()).unwrap_or_default());
            }
        }
    }
    println!("conform {ok}/{n}; undeclared fields dropped (instances) {dropped}; int-or-string coerced {coerced}; maps->pairs {pairs}; type-level drops: float {fl}, opaque {opq}, non-string maps {mns}, recursion {rec}");
}
