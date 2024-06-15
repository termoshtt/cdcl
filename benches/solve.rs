use cdcl::{Solver, CNF, DPLL};
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};

const SAT_DIGETS: &[&str] = &[
    "7e19f295d35c30ac4d5386ffec1fcf28", // ~10ms
    "866f6730afd797a244fea4f28ac3a218", // ~140ms
    "8345bdb88fa777b2940145d3306bbf7e", // ~200ms
    "2367a7e13ff5d039978a26c3081a4342", // ~400ms
];
const UNSAT_DIGEST: &[&str] = &[
    "38de0de52a209b6d0beb50986fd8b506",
    "2b738a1991a7318cad993a809b10cc2c",
    "18f54820956791d3028868b56a09c6cd",
    "04e47e6635908600ef3938b32644825a",
    "00f969737ba4338bd233cd3ed249bd55",
];

fn dpll(c: &mut Criterion) {
    let mut sat = c.benchmark_group("SAT");
    for digest in SAT_DIGETS {
        let mut solver = DPLL::default();
        let expr = CNF::from_rgbd(rgbd::Digest::new(digest.to_string()).read().unwrap());
        sat.bench_with_input(BenchmarkId::new(solver.name(), digest), &expr, |b, expr| {
            b.iter(|| {
                let _solution = solver.solve_cancelable(expr.clone(), Default::default());
            })
        });
    }
    drop(sat);

    let mut unsat = c.benchmark_group("UNSAT");
    for digest in UNSAT_DIGEST {
        let mut solver = DPLL::default();
        let expr = CNF::from_rgbd(rgbd::Digest::new(digest.to_string()).read().unwrap());
        unsat.bench_with_input(BenchmarkId::new(solver.name(), digest), &expr, |b, expr| {
            b.iter(|| {
                let _solution = solver.solve_cancelable(expr.clone(), Default::default());
            })
        });
    }
}

criterion_group!(benches, dpll);
criterion_main!(benches);
