use crate::cnf::*;
use crate::resolution_graph::ResolutionGraph;

use std::collections::HashMap;
use std::fs::File;
use std::io::prelude::*;
use std::path::Path;

#[derive(Debug)]
pub enum FileParseError {
    IOError(std::io::Error),
    ParseError(String),
}

impl std::fmt::Display for FileParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            IOError(e) => write!(f, "{}", e),
            ParseError(s) => write!(f, "{}", s),
        }
    }
}

use FileParseError::*;

pub type Result = std::result::Result<ResolutionGraph, FileParseError>;

impl std::convert::Into<Result> for FileParseError {
    fn into(self) -> Result {
        Err(self)
    }
}

pub fn get_clauses(filename: &Path) -> Result {
    let mut file = match File::open(&filename) {
        Err(why) => return IOError(why).into(),
        Ok(file) => file,
    };

    let mut input = String::new();
    match file.read_to_string(&mut input) {
        Err(why) => return IOError(why).into(),
        Ok(_) => (),
    }

    let inputlength = input.len();
    let mut slice;
    let mut vec = Vec::new();

    let mut graph = ResolutionGraph::new();

    for line in input.lines() {
        let mut current_index = 0;
        let mut clause = Clause::new();
        let mut clause_label;
        let mut parent1 = String::new();
        let mut parent2 = String::new();

        //read up until the first space

        let mut i = current_index;

        while i + 1 <= inputlength {
            slice = &line[i..(i + 1)];
            if slice == ":" {
                break;
            }
            i += 1;
        }

        //get the label of the current clause
        clause_label = line[current_index..i].to_string();

        current_index = i + 3;

        i = current_index;

        //read until the delimiting }
        while i + 1 <= line.len() {
            slice = &line[i..(i + 1)];
            if slice == "}" {
                break;
            }
            i += 1;
        }

        //get each of the clause literals, and add each one to the current clause object
        let clause_strings = line[current_index..i].to_string();

        let mut split = clause_strings.split(",");

        for st in split {
            let name = st.trim();

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
        current_index = i + 3;
        i = current_index;

        while i + 1 <= inputlength {
            slice = &line[i..(i + 1)];
            if slice == ")" {
                break;
            }
            i += 1;
        }

        let full_labels = line[current_index..i].to_string();

        if full_labels.len() != 0 {
            let mut parents_vec = Vec::new();

            split = full_labels.split(",");

            for st in split {
                let lab = st.trim();
                parents_vec.push(lab);
            }

            if parents_vec.len() != 2 {
                return ParseError("ERROR: each clause must have exactly two parents!".to_string())
                    .into();
            }

            parent1 = parents_vec[0].to_string();
            parent2 = parents_vec[1].to_string();
        }

        vec.push((clause_label, clause, parent1, parent2));
    }

    //construct the resolution graph

    let mut index;
    let mut will_repeat = true;
    let mut bools = Vec::new();
    let mut ids = HashMap::new();

    for _item in vec.iter() {
        bools.push(false);
    }

    assert_eq!(vec.len(), bools.len());

    while will_repeat {
        will_repeat = false;
        index = 0;

        while index < vec.len() {
            if bools[index] == false {
                let label = &vec[index].0;
                let cl = &vec[index].1;
                let p1 = &vec[index].2;
                let p2 = &vec[index].3;

                if p1.len() == 0 && p2.len() == 0 {
                    let id = graph.add_clause(cl.clone());
                    ids.insert(label, id);
                    bools[index] = true;
                    will_repeat = true;
                    index += 1;
                } else {
                    match ids.get(p1) {
                        Some(&cid) => {
                            let p1id = cid;
                            match ids.get(p2) {
                                Some(&cid2) => {
                                    let p2id = cid2;
                                    let id = graph.add_clause(cl.clone());
                                    ids.insert(label, id);
                                    if let Err(s) = graph.add_resolution_ids(p1id, p2id, id) {
                                        return ParseError(format!(
                                            "ERROR failed to create resolution: {}",
                                            s
                                        ))
                                        .into();
                                    }
                                    bools[index] = true;
                                    will_repeat = true;
                                    index += 1
                                }
                                _ => index += 1,
                            }
                        }
                        _ => index += 1,
                    }
                }
            } else {
                index += 1;
            }
        }
    }

    Ok(graph)
}

/*
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
*/
