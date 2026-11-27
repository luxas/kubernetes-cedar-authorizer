//! Prints the per-shape table used in docs/spike.md (R-12).
use spike::{engine::*, shapes::*};
fn main() {
    let e = Engine::new();
    println!("{:<36} {:<34} {:<10} {:<10} {:<10} {:<10} {:<8}", "shape", "phase1 outcome", "baseline", "phase2", "reauth", "plain", "expect");
    for s in load() {
        match run_shape(&e, &s, NameSource::Plan) {
            Err(m) => println!("{:<36} ERROR {m}", s["id"].as_str().unwrap()),
            Ok(r) => { if std::env::args().any(|a| a == "--residuals") { for x in &r.phase1.residuals { println!("    residual {} {} text={}B json={}B error_node={}", x.policy_id, x.effect, x.text_len, x.json_len, x.has_error_node); } }
              for (i, q) in r.requests.iter().enumerate() {
                println!("{:<36} {:<34} {:<10} {:<10} {:<10} {:<10} {:<8} placeholder-reauth={}", r.id, outcome_kind(&r.outcome),
                    format!("{:?}", q.baseline), format!("{:?}", q.phase2), format!("{:?}", q.reauthorize), format!("{:?}", q.plain_residual_set),
                    format!("{:?}", r.expect[i]), match &q.reauthorize_placeholder { Ok(c) => format!("{c:?}"), Err(x) => format!("ERR({})", &x[..x.len().min(40)]) });
            } }
        }
    }
}
