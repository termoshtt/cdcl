use cdcl::{dpll, CancelToken, CNF};
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};

const SAT_DIGETS: &[(&str, &str)] = &[
    ("sat1", "7e19f295d35c30ac4d5386ffec1fcf28"),
    ("sat2", "866f6730afd797a244fea4f28ac3a218"),
    ("sat3", "8345bdb88fa777b2940145d3306bbf7e"),
    ("sat4", "2367a7e13ff5d039978a26c3081a4342"),
];
const UNSAT_DIGEST: &[(&str, &str)] = &[
    ("unsat1", "2b738a1991a7318cad993a809b10cc2c"),
    ("unsat2", "18f54820956791d3028868b56a09c6cd"),
    ("unsat3", "00f969737ba4338bd233cd3ed249bd55"),
    ("unsat4", "38de0de52a209b6d0beb50986fd8b506"),
    ("unsat5", "04e47e6635908600ef3938b32644825a"),
];

fn bench_dpll(c: &mut Criterion) {
    let mut group = c.benchmark_group("dpll");
    for (title, digest) in SAT_DIGETS {
        let expr = CNF::from_rgbd(rgbd::Digest::new(digest.to_string()).read().unwrap());
        group.bench_with_input(BenchmarkId::new("dpll", title), &expr, |b, expr| {
            b.iter(|| {
                let _solution = dpll(expr.clone(), CancelToken::new()).unwrap();
            })
        });
    }

    for (title, digest) in UNSAT_DIGEST {
        let expr = CNF::from_rgbd(rgbd::Digest::new(digest.to_string()).read().unwrap());
        group.bench_with_input(BenchmarkId::new("dpll", title), &expr, |b, expr| {
            b.iter(|| {
                let _solution = dpll(expr.clone(), Default::default());
            })
        });
    }
}

criterion_group!(benches, bench_dpll);
criterion_main!(benches);
