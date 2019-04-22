use crate::cnf::*;
use crate::resolution_graph::ResolutionGraph;

use std::error::Error;
use std::fs::File;
use std::io::prelude::*;
use std::path::Path;
use std::collections::HashMap;

fn get_clauses(filename: &str) -> ResolutionGraph {
    let filepath = format!("./src/{}", String::from(filename));
    let path = Path::new(&filepath);
    let display = path.display();
     
    let mut file = match File::open(&path) {
        Err(why) => panic!("couldn't open {}: {}", display, why.description()),
        Ok(file) => file,
    };

    let mut input = String::new();
    match file.read_to_string(&mut input) {
        Err(why) => panic!("couldn't read {}: {}", display, why.description()),
        Ok(_) => (), 
    }

    let inputlength = input.len();
    let mut slice = &input[..14];
    let mut vec = Vec::new();

    

    let mut graph = ResolutionGraph::new();

    for line in input.lines() {

        let mut current_index = 0;
        let mut clause = Clause::new();
        let mut clause_label = String::new();
        let mut parent1 = String::new();
        let mut parent2 = String::new();

        //read up until the first space

        let mut i = current_index;

        while i+1 <= inputlength {
            slice = &line[i..(i+1)];
            if slice == ":" {
                break;
            } 
            i += 1;
        }
        
        //get the label of the current clause
        clause_label = line[current_index..i].to_string();

        current_index = i+3;

        i = current_index;

        //read until the delimiting }
        while i+1 <= line.len() {
            slice = &line[i..(i+1)];
            if slice == "}" {
                break;
            } 
            i += 1;
        }


        //get each of the clause literals, and add each one to the current clause object
        let mut clause_strings = line[current_index..i].to_string();

        let mut split = clause_strings.split(",");

        for st in split {
            let mut name = st.trim();

            if st.len() > 0 {
                slice = &name[..1];

                if slice == "~" {
                    clause.add(Literal::new_negated(&name[1..]));
                } else {
                    clause.add(Literal::new(name));
                }
            }
        }
            

        //read the labels of the parent clauses (if they exist)
        current_index = i+3;
        i = current_index;

        while i+1 <= inputlength {
            slice = &line[i..(i+1)];
            if slice == ")" {
                break;
            } 
            i += 1;
        }


        let mut full_labels = line[current_index..i].to_string();
        let mut length_of_labels = full_labels.len();

        if full_labels.len() != 0 {
            let mut parents_vec = Vec::new();

            split = full_labels.split(",");

            for st in split {
                let mut lab = st.trim();
                parents_vec.push(lab);
            }

            if parents_vec.len() != 2 {
                println!("ERROR: each clause must have exactly two parents!");
            }

            parent1 = parents_vec[0].to_string();
            parent2 = parents_vec[1].to_string();
        }


        vec.push((clause_label, clause, parent1, parent2));

    }

    //construct the resolution graph

    let mut index = 0usize;
    let mut will_repeat = true;
    let mut bools = Vec::new();
    let mut ids = HashMap::new();


    for item in vec.iter() {
        bools.push(false);
    }

    assert_eq!(vec.len(), bools.len());

    while will_repeat {
        will_repeat = false;
        index = 0;

        while index < vec.len() {
            if bools[index] == false {
                let mut label = &vec[index].0;
                let mut cl = &vec[index].1;
                let mut p1 = &vec[index].2;
                let mut p2 = &vec[index].3;

                if p1.len() == 0 && p2.len() == 0 {
                    let mut id = graph.add_clause(cl.clone());
                    ids.insert(label, id);
                    bools[index] = true;
                    will_repeat = true;
                    index += 1;


                } else {

                    match ids.get(p1) {
                        Some(&cid) => {
                            let mut p1id = cid;
                            match ids.get(p2) {
                                Some(&cid2) => {
                                    let mut p2id = cid2;
                                    let mut id = graph.add_clause(cl.clone());
                                    ids.insert(label, id);
                                    graph.add_resolution_ids(p1id, p2id, id);
                                    bools[index] = true;
                                    will_repeat = true;
                                    index += 1
                                },
                                _ => index += 1,
                            }
                        },
                        _ => index += 1, 
                    }

                }

            } else {
                index += 1;
            }
        }
    }

    return graph;
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn attempt() {
        let graph = get_clauses("test.txt");
        println!("results: {:?}", graph);
        println!("is correct?  {:?}", graph.verify());
    }
}



//fn main() {
//    let cl = get_clauses("test.txt");
//    println!("results: {:?}", cl);
//
//}
