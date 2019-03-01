use resolution::ast::Node;

fn main() {
    let expr = Node::and(
        Node::or(Node::prop("P"), Node::not(Node::prop("Q"))),
        Node::not(Node::and(
            Node::prop("Q"),
            Node::implies(Node::prop("W"), Node::not(Node::prop("W"))),
        )),
    );
    println!("{}", expr);

    let expr = Node::and(
        Node::and(Node::and(Node::prop("P"), Node::prop("Q")), Node::prop("R")),
        Node::or(Node::prop("S"), Node::prop("T")),
    );
    println!("{}", expr);

    let expr = Node::and(
        Node::and(Node::prop("P"), Node::prop("Q")),
        Node::and(Node::prop("R"), Node::prop("S")),
    );
    println!("{}", expr);
}
