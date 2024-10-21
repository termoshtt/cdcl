macro_rules! impl_inverse {
    ($trait:ident , $f:ident; $lhs:ty, $rhs:ty) => {
        impl $trait<$rhs> for $lhs {
            type Output = <$rhs as $trait<$lhs>>::Output;
            fn $f(self, rhs: $rhs) -> Self::Output {
                $trait::$f(rhs, self)
            }
        }
    };
}

macro_rules! impl_bitand_inverse {
    ($lhs:ty, $rhs:ty) => {
        impl_inverse!(BitAnd, bitand; $lhs, $rhs);
    };
}
macro_rules! impl_bitor_inverse {
    ($lhs:ty, $rhs:ty) => {
        impl_inverse!(BitOr, bitor; $lhs, $rhs);
    };
}

mod clause;
mod cnf;
mod literal;

pub use clause::*;
pub use cnf::*;
pub use literal::*;
