// pub fn add(left: u64, right: u64) -> u64 {
//     left + right
// }

// #[cfg(test)]
// mod tests {
//     use super::*;

//     #[test]
//     fn it_works() {
//         let result = add(2, 2);
//         assert_eq!(result, 4);
//     }
// }

use std::collections::{HashMap, HashSet};
use permlib;

pub fn parse_tuple(n: usize, myvec_str: &String) -> Vec<Vec<usize>> {
    let mut parsed_vec = allocate_vector(n);

    // // allocate empty vec
    // for i in 0..n {
    //     parsed_vec.push(Vec::<usize>::new());
    //     for _ in 0..n {
    //         parsed_vec[i].push(0);
    //     }
    // }

    let mut val:usize = 0;
    let mut was_num = false;
    let mut row:usize = 0;
    let mut col:usize = 0;
    for l in myvec_str.chars() {
        if l == ' ' || l == '\t' {
            continue;
        }
        if l == '(' {
        }
        if l == ')' {
            if was_num {
                parsed_vec[row][col] = val;
                was_num = false;
            }
            row += 1;
            col = 0;
        }

        if l >= '0' && l <= '9' {
            // println!("{l}");
            if was_num {
                val = 10*val + (l as usize) - ('0' as usize);
            }
            else {
                was_num = true;
                val = (l as usize) - ('0' as usize); 
            }
        }
        if l == ',' {
            if was_num {
                // println!("({row},{col}) = {val}");
                parsed_vec[row][col] = val;
                col += 1;
                was_num = false;
                val = 0;
            }
        }
    }
    //println!("{parsed_vec:?}");
    // println!("Level: {}", level);
    return parsed_vec;
}


pub fn allocate_vector(n: usize) -> Vec<Vec<usize>> {
    let mut result_vec:Vec<Vec<usize>> = vec![];
    
    // allocate empty vec
    for i in 0..n {
        result_vec.push(Vec::<usize>::new());
        for _ in 0..n {
            result_vec[i].push(0);
        }
    }
    result_vec
}    

pub fn rel_isomorphic_image(rel:&Vec<Vec<usize>>, perm:&Vec<usize>)->Vec<Vec<usize>> 
{    
    let n = rel.len();

    let mut res = allocate_vector(n);

    for i in 0..n {
        for j in  0..n {
            res[perm[i]][perm[j]] = rel[i][j];
        }
    }

    return res;
}

pub fn find_canonical_quasi_order(rel_qord:&Vec<Vec<usize>>) -> Vec<Vec<usize>> {
    let n = rel_qord.len();

    // copy of rel_a
    let mut new_rel_qord = allocate_vector(n);
    for i in 0..n {
        for j in 0..n {
            new_rel_qord[i][j] = rel_qord[i][j];
        }
    }
    let mut b_found = true;
    let mut vi:usize = 0;
    let mut vj:usize = 0;

    while b_found {
        b_found = false;
        for i in 0..n {
            if !b_found {
                for j in 0..n {
                    if i != j {
                        if new_rel_qord[i][j] == 1 && new_rel_qord[j][i] != 1 && i > j {
                            b_found = true;
                            vi = i;
                            vj = j;
                            break;
                        }
                    }
                }
            }
        }
        
        if b_found {
            // (i,j) violates canonicity
            // println!("violation: {} {} {:?}", vi,vj, nRelA)
            let mut perm = (0..n).into_iter().collect::<Vec<_>>();
            perm[vi] = vj;
            perm[vj] = vi;
            new_rel_qord = rel_isomorphic_image(&new_rel_qord, &perm);
        }
    }
    new_rel_qord
}

// rel_qord is already canonical quasi order        
fn rel_quasi_order_perm_preserves_canonical_quasi_order(rel_qord:&Vec<Vec<usize>>, perm:&Vec<usize>) -> bool 
{
    let n = rel_qord.len();

    for i in 0..n {
        for j in 0..n {
            if i!=j && rel_qord[perm[i]][perm[j]] == 1 && rel_qord[perm[j]][perm[i]] != 1 && perm[i] > perm[j] {
                return false;
            }
        }
    }

    true
}

fn get_interp(aa:&Vec<Vec<usize>>) -> Vec<usize> {
    let n = aa.len();
    
    let mut interp_aa = Vec::<usize>::new();
    
    for i in 0..n {
        for j in 0..n {
            if i != j {
                interp_aa.push(aa[i][j]);
            }
        }
    }

    interp_aa
}

// strictly greater, if equal -> False
fn is_greater_interp(aa1:&Vec<Vec<usize>>, aa2:&Vec<Vec<usize>>) -> bool {
    let interp_aa1 = get_interp(aa1);
    let interp_aa2 = get_interp(aa2);
    let ni = interp_aa1.len();
    let mut idx = 0usize;
    while idx < ni && interp_aa1[idx] == interp_aa2[idx] {
        idx+=1;
    }

    if idx < ni {
        if interp_aa1[idx] > interp_aa2[idx] {
            return true;
        }
        else {
            return false;
        }
    }
    false
}

// quasi order canonical maximal
pub fn rel_quasi_order_find_can_max_repr(rel_qord:&Vec<Vec<usize>>) -> Vec<Vec<usize>> {
    // copy c_rel_qord
    let c_rel_qord =  find_canonical_quasi_order(rel_qord);

    let n = c_rel_qord.len();
    
    let mut b_repr_cmax_rel_qord = false;

    let mut perm = (0..n).into_iter().collect::<Vec<_>>();

    let mut cmax_rel_qord_repr = allocate_vector(n);
    loop {
        if rel_quasi_order_perm_preserves_canonical_quasi_order(&c_rel_qord, &perm) {
            let rel_qord_iso = rel_isomorphic_image(&c_rel_qord, &perm);
            if !b_repr_cmax_rel_qord {
                cmax_rel_qord_repr = rel_qord_iso;
                b_repr_cmax_rel_qord = true;
            }
            else {
                // compare new representation
                if is_greater_interp(&rel_qord_iso, &cmax_rel_qord_repr) {
                    cmax_rel_qord_repr = rel_qord_iso;
                }
            }

        }
        
        if !permlib::next_perm(&mut perm, n) {
            break;
        }
    }

    cmax_rel_qord_repr
}

// quasi order canonical maximal
pub fn rel_quasi_order_find_can_max_repr_from_can_quasi_order(rel_qord:&Vec<Vec<usize>>) -> Vec<Vec<usize>> {
    // copy c_rel_qord
    //let c_rel_qord =  find_canonical_quasi_order(rel_qord);

    let n = rel_qord.len();
    
    let mut b_repr_cmax_rel_qord = false;

    let mut perm = (0..n).into_iter().collect::<Vec<_>>();

    let mut cmax_rel_qord_repr = allocate_vector(n);
    loop {
        if rel_quasi_order_perm_preserves_canonical_quasi_order(rel_qord, &perm) {
            let rel_qord_iso = rel_isomorphic_image(rel_qord, &perm);
            if !b_repr_cmax_rel_qord {
                cmax_rel_qord_repr = rel_qord_iso;
                b_repr_cmax_rel_qord = true;
            }
            else {
                // compare new representation
                if is_greater_interp(&rel_qord_iso, &cmax_rel_qord_repr) {
                    cmax_rel_qord_repr = rel_qord_iso;
                }
            }

        }
        
        if !crate::permlib::next_perm(&mut perm, n) {
            break;
        }
    }

    cmax_rel_qord_repr
}

pub fn gen_sum(v:usize, m:usize) -> Vec<Vec<usize>> {


    match m {
        1 => return vec!(vec![v]),
        2.. => {
            let mut res:Vec<Vec<usize>> = vec![];
            for i in 0..=v {
                for v in gen_sum(v-i, m-1) {
                    res.push([vec![i], v].concat());
                }
            }
            res
        },
        _ => return Vec::<Vec<usize>>::new()
    }
}


pub fn gen_quasi_orders_from_order_just_repr_set(rel_ord:&Vec<Vec<usize>>, n: usize) -> HashSet<Vec<Vec<usize>>> {
    let m = rel_ord.len();

    if m >= n {
        return HashSet::new();
    }
    
    let mut quasi_orders_repr:HashSet<Vec<Vec<usize>>> = HashSet::new();

    for s in gen_sum(n - m, m) {
        let mut vert_map:HashMap<usize, HashSet<usize>> = HashMap::new();
        let mut n_idx = m;

        for idx in 0..s.len() {
            let mut tmp_set = HashSet::from([idx]);
            //vert_map[&idx] = HashSet::from([idx]);
            for _ in 0..s[idx] {
                tmp_set.insert(n_idx);
                n_idx+=1;
            }
            vert_map.insert(idx, tmp_set);
        } 

        // println!("{:?}", vert_map);
        let gen_rel = gen_quasi_order_from_dict(rel_ord, n, &vert_map);
        quasi_orders_repr.insert(rel_quasi_order_find_can_max_repr(&gen_rel));
    }

    quasi_orders_repr
}

pub fn gen_quasi_orders_from_order_set(rel_ord:&Vec<Vec<usize>>, n: usize) -> HashSet<Vec<Vec<usize>>> {
    let m = rel_ord.len();

    if m >= n {
        return HashSet::new();
    }
    
    let mut quasi_orders_repr:HashSet<Vec<Vec<usize>>> = HashSet::new();

    for s in gen_sum(n - m, m) {
        let mut vert_map:HashMap<usize, HashSet<usize>> = HashMap::new();
        let mut n_idx = m;

        for idx in 0..s.len() {
            let mut tmp_set = HashSet::from([idx]);
            //vert_map[&idx] = HashSet::from([idx]);
            for _ in 0..s[idx] {
                tmp_set.insert(n_idx);
                n_idx+=1;
            }
            vert_map.insert(idx, tmp_set);
        } 

        // println!("{:?}", vert_map);
        let gen_rel = gen_quasi_order_from_dict(rel_ord, n, &vert_map);
        quasi_orders_repr.insert(find_canonical_quasi_order(&gen_rel));
    }

    quasi_orders_repr
}


fn gen_quasi_order_from_dict(rel_ord: &Vec<Vec<usize>>, n: usize, vert_dict:&HashMap<usize, HashSet<usize>>) -> Vec<Vec<usize>> {
    let m = rel_ord.len();

    let mut res = allocate_vector(n);

    for i in 0..m {
        for j in 0..m {
            if rel_ord[i][j] == 1 {
                for ei in &vert_dict[&i] {
                    for ej in &vert_dict[&j] {
                        res[*ei][*ej] = 1;
                    }
                }
            }
        }
    }
    res
}

pub fn find_canonical_rel_order_repr2_v3(rel_a:&Vec<Vec<usize>>) -> Vec<Vec<usize>> 
{
    let n = rel_a.len();

    let mut b_repr = false;

    let mut perm = (0..n).into_iter().collect::<Vec<_>>();
    let mut rel_a_repr2:Vec<Vec<usize>> = Vec::new();
    loop {
        if perm_preserves_canonical_order(rel_a, &perm) {
            let h_a = rel_isomorphic_image(rel_a, &perm);
            if !b_repr {
                rel_a_repr2 = h_a;
                b_repr = true;
            }
            else {
                if is_greater_interp(&h_a, &rel_a_repr2) {
                    rel_a_repr2 = h_a;
                }
            }
        }

        if !permlib::next_perm(&mut perm, n) {
            break;
        }
    }
    rel_a_repr2
}

fn perm_preserves_canonical_order(rel_a: &Vec<Vec<usize>>, perm: &Vec<usize>) -> bool {
    let n = rel_a.len();

    for i in 0..n {
        for j in (i+1)..n {
            if rel_a[i][j] == 1 && perm[i] > perm[j] {
                return false;
            }
        }
    }
    true
}



// def find_canonical_rel_quasi_order_repr2_v3(rel_a):
//     n = len(rel_a)
//     repr_relA = None
//     for perm in itertools.permutations(range(n)):        
//         if perm_preserves_canonical_quasi_order(rel_a, perm):
//             hA = isomorphic_rel_image(rel_a, perm)
//             if not repr_relA:
//                 repr_relA = hA
//             else:
//                 if is_greater_interp(hA, repr_relA):
//                     repr_relA = hA

//     return repr_relA



pub fn expand_order_by_one_canonical_rec3(level:usize, rel_old: &Vec<Vec<usize>>, rel_new:&mut Vec<Vec<usize>>, res: &mut HashSet<Vec<Vec<usize>>>)
{
    let n = rel_old.len();

    if level == n {
        res.insert(rel_new.clone());
    }
    else {
        for q in 0..2 {
            if q == 0 {
               rel_new[level][n] = 0;
               rel_new[n][level] = 0;
               expand_order_by_one_canonical_rec3(level + 1, rel_old, rel_new, res); 
            }
            else {
                let mut b_found = false;
                for k in 0..level {
                    if rel_old[k][level] == 1 && rel_new[k][n] == 0 {
                        b_found = true;
                        break;
                    }
                }
                if !b_found {
                    rel_new[level][n] = 1;
                    rel_new[n][level] = 0;
                
                    expand_order_by_one_canonical_rec3(level + 1, rel_old, rel_new, res);
                
                    rel_new[level][n] = 0;
                    rel_new[n][level] = 0;
                }
            }
        }
    }
}



// def gen_quasi_order_from_dict(rel_old, n, vert_dict):
//     m = len(rel_old)

//     #init order table
//     res = []
//     for i in range(n):
//         res.append([])
//         for _ in range(n):
//             res[i].append(0)

//     for i in range(m):
//         for j in range(m):
//             if rel_old[i][j]:
//                 for e in vert_dict[i]:
//                     for f in vert_dict[j]:
//                         res[e][f] = 1
//     return res



// def gen_quasi_orders_from_order_just_repr_set(rel_old, n):
// m = len(rel_old)

// if m >= n:
//     return []

// quasi_orders_repr = set()
// for s in gen_sum(n - m, m):
//     vert_dict = dict()
//     n_idx = m
//     for idx,v in enumerate(s):
//         vert_dict[idx] = set({idx})
//         for _ in range(v):
//             vert_dict[idx].add(n_idx)
//             n_idx+=1
    
//     #print(s, vert_dict) # debug
//     genrel = gen_quasi_order_from_dict(rel_old, n, vert_dict)
//     quasi_orders_repr.add(tuple(tuple(r) for r in find_canonical_rel_quasi_order_repr2_v4(genrel)))

// return quasi_orders_repr
//def gen_sum(v, m):
// """
// Returns all possibilities how to obtain value `v` by a sum of `m` integer values.
// """
// if m <= 0:
//     return []
// if m == 1:
//     return [[v]]

// res = []
// for i in range(v+1):
//     for e in gen_sum(v-i, m-1):            
//         res.append([i] + e)
// return res

