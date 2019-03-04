use resolution::ast::Ast;

fn main() {
    let expr = Ast::and(
        Ast::or(Ast::prop("P"), Ast::not(Ast::prop("Q"))),
        Ast::not(Ast::and(
            Ast::prop("Q"),
            Ast::implies(Ast::prop("W"), Ast::not(Ast::prop("W"))),
        )),
    );
    println!("{}", expr);

    let expr = Ast::and(
        Ast::and(Ast::and(Ast::prop("P"), Ast::prop("Q")), Ast::prop("R")),
        Ast::or(Ast::prop("S"), Ast::prop("T")),
    );
    println!("{}", expr);

    let expr = Ast::and(
        Ast::and(Ast::prop("P"), Ast::prop("Q")),
        Ast::and(Ast::prop("R"), Ast::prop("S")),
    );
    println!("{}", expr);
}
