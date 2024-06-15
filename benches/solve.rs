use cdcl::{Solver, CNF, DPLL};
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};

const SAT_DIGETS: &[&str] = &[
    "0ef68fc7aa6f2bc7fb74ada9d865da06",
    "2367a7e13ff5d039978a26c3081a4342",
    "3eaa112593cb66052d579c16f3d5a37e",
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
