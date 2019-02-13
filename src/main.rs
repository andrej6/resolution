use resolution::Expr;

fn main() {
    let exp = Expr::and(Expr::atom("P"), Expr::not(Expr::atom("P")));
    println!("{}", exp);

    match exp {
        Expr::Conj(_,_) => println!("Conjunction!"),
        _ => println!("Not that!"),
    }
}
