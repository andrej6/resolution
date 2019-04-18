use crate::cnf::*;

use std::error::Error;
use std::fs::File;
use std::io::prelude::*;
use std::path::Path;

fn get_clauses(filename: &str) -> Vec<Clause> {
    let filepath = format!("./src/{}", String::from(filename));
    let path = Path::new(&filepath);
    let display = path.display();
     
    //println!("here is the filepath: {}", filepath);

    let mut file = match File::open(&path) {
        Err(why) => panic!("couldn't open {}: {}", display, why.description()),
        Ok(file) => file,
    };

    let mut s = String::new();
    match file.read_to_string(&mut s) {
        Err(why) => panic!("couldn't read {}: {}", display, why.description()),
        Ok(_) => print!("{} contains:\n{}", display, s),
    }

    let inputlength = s.len();
    let mut current_index = 0;
    let mut slice = &s[..14];

    let mut clause = Clause::new();
    let mut clause_label = String::new();
    let mut parent1 = String::new();
    let mut parent2 = String::new();

    println!("first 14 charactrers: {}\n", slice);

    current_index = 14;

    //read up until the first space

    let mut i = current_index;

    while i+1 <= inputlength {
        slice = &s[i..(i+1)];
        if slice == ":" {
            println!("FOUND COLON AT INDEX {}", i);
            break;
        } else {
            println!("read {}", slice);
        }

        i += 1;
    }

    clause_label = s[current_index..i].to_string();

    println!("clause label: {}", clause_label);

    current_index = i+3;

    //read until the comma
    
    i = current_index;
    while i+1 <= inputlength {
        slice = &s[i..(i+1)];
        if slice == "}" {
            println!("FOUND }} AT INDEX {}", i);
            break;
        } else {
            println!("read {}", slice);
        }

        i += 1;
    }

    let mut clause_strings = s[current_index..i].to_string();

    println!("clause names: {}", clause_strings);

    //split the strings and strip the newlines

    let mut split = clause_strings.split(",");

    for st in split {
        let mut name = st.trim();
        println!("string: {}      length: {}", name, name.len());

        slice = &name[..1];

        println!("slice: {}", slice);

        if slice == "~" {
            println!("this one's negated");
            clause.add(Literal::new_negated(&name[1..]));
        } else {
            println!("not negated");
            clause.add(Literal::new(name));
        }
    }
        
    //read until the first (

    current_index = i+3;
    i = current_index;

    while i+1 <= inputlength {
        slice = &s[i..(i+1)];
        if slice == ")" {
            println!("FOUND ) AT INDEX {}", i);
            break;
        } else {
            println!("read {}", slice);
        }

        i += 1;
    }


    let mut full_labels = s[current_index..i].to_string();
    let mut length_of_labels = full_labels.len();
    println!("full labels: {}      length: {}", full_labels, length_of_labels);

    current_index = i+1;






    slice = &s[current_index..(current_index+1)];

    println!("next char: {}", slice);
    if slice == "\n" {
        println!("reached end of line!");
    }



    println!("\n Cool B-)\n");

    let mut vec = Vec::new();
    //clause.add(Literal::new("P"));
    //clause.add(Literal::new_negated("Q"));

    vec.push(clause);

    return vec;
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn attempt() {
        let cl = get_clauses("test.txt");
        println!("results: {:?}", cl);
    }
}



//fn main() {
//    let cl = get_clauses("test.txt");
//    println!("results: {:?}", cl);
//
//}
