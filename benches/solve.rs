use cdcl::{Solver, CNF, DPLL};
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};

const SAT_DIGETS: &[&str] = &[
    "1cf67760092ebabc1bb42706fb8d43dc",
    "0ef68fc7aa6f2bc7fb74ada9d865da06",
    "2367a7e13ff5d039978a26c3081a4342",
    "23a92c04ee9248308a18d6a44e5d15f0",
    "3eaa112593cb66052d579c16f3d5a37e",
];
const UNSAT_DIGEST: &[&str] = &[
    "38de0de52a209b6d0beb50986fd8b506",
    "2b738a1991a7318cad993a809b10cc2c",
    "21ca756baf6af7f15098455977b88d6d",
    "18f54820956791d3028868b56a09c6cd",
    "04e47e6635908600ef3938b32644825a",
    "067dc6945c4aec1c2bc1fdc2e5819124",
    "00f969737ba4338bd233cd3ed249bd55",
];

fn dpll(c: &mut Criterion, digests: &[&str]) {
    for digest in digests {
        let mut solver = DPLL::default();
        let expr = CNF::from_rgbd(rgbd::Digest::new(digest.to_string()).read().unwrap());
        c.bench_with_input(BenchmarkId::new(solver.name(), digest), &expr, |b, expr| {
            b.iter(|| {
                let _solution = solver.solve_cancelable(expr.clone(), Default::default());
            })
        });
    }
}

fn dpll_sat(c: &mut Criterion) {
    dpll(c, SAT_DIGETS);
}

fn dpll_unsat(c: &mut Criterion) {
    dpll(c, UNSAT_DIGEST);
}

criterion_group!(benches, dpll_sat, dpll_unsat);
criterion_main!(benches);
