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

pub fn parse_vector(n: usize, myvec_str: &String) -> Vec<Vec<usize>> {
    let mut parsed_vec = allocate_vector(n);

    let mut val:usize = 0;
    let mut was_num = false;
    let mut row:usize = 0;
    let mut col:usize = 0;
    for l in myvec_str.chars() {
        if l == ' ' || l == '\t' {
            continue;
        }
        if l == '[' {
        }
        if l == ']' {
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
            if perm[i] > perm[j] {
                // if rel_qord[perm[i]][perm[j]] == 1 && rel_qord[perm[j]][perm[i]] != 1 {
                if rel_qord[i][j] == 1 && rel_qord[j][i] != 1 {
                    return false;
                }
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

// strictly greater, if equal -> False
fn rel_quasi_order_is_greater_rel(aa1:&Vec<Vec<usize>>, aa2:&Vec<Vec<usize>>) -> bool {
    let n1 = aa1.len();

    let mut idx_i = 0usize;
    let mut idx_j = 0usize;

    while idx_i < n1 && aa1[idx_i][idx_j] == aa2[idx_i][idx_j] {
        if idx_j < n1 - 1 {
            idx_j +=1;
        }
        else {
            idx_i += 1;
            idx_j  = 0;
        }
    }

    if idx_i < n1 {
        if aa1[idx_i][idx_j] > aa2[idx_i][idx_j] {
            return true;
        }
        else {
            return false;
        }
    }
    false
}

// strictly lesser, if equal -> False
fn rel_quasi_order_is_lesser_rel(aa1:&Vec<Vec<usize>>, aa2:&Vec<Vec<usize>>) -> bool {
    let n1 = aa1.len();

    let mut idx_i = 0usize;
    let mut idx_j = 0usize;

    while idx_i < n1 && aa1[idx_i][idx_j] == aa2[idx_i][idx_j] {
        if idx_j < n1 - 1 {
            idx_j +=1;
        }
        else {
            idx_i += 1;
            idx_j  = 0;
        }
    }

    if idx_i < n1 {
        if aa1[idx_i][idx_j] < aa2[idx_i][idx_j] {
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
pub fn rel_quasi_order_find_can_min_repr(rel_qord:&Vec<Vec<usize>>) -> Vec<Vec<usize>> {
    // copy c_rel_qord
    let c_rel_qord =  find_canonical_quasi_order(rel_qord);

    let n = c_rel_qord.len();
    
    let mut b_repr_cmin_rel_qord = false;

    let mut perm = (0..n).into_iter().collect::<Vec<_>>();

    let mut cmin_rel_qord_repr = allocate_vector(n);
    loop {
        if rel_quasi_order_perm_preserves_canonical_quasi_order(&c_rel_qord, &perm) {
            let rel_qord_iso = rel_isomorphic_image(&c_rel_qord, &perm);
            if !b_repr_cmin_rel_qord {
                cmin_rel_qord_repr = rel_qord_iso;
                b_repr_cmin_rel_qord = true;
            }
            else {
                // compare new representation
                if rel_quasi_order_is_lesser_rel(&rel_qord_iso, &cmin_rel_qord_repr) {
                    cmin_rel_qord_repr = rel_qord_iso;
                }
            }

        }
        
        if !permlib::next_perm(&mut perm, n) {
            break;
        }
    }

    cmin_rel_qord_repr
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

fn rel_are_pair_antisymmetric(rel1: &Vec<Vec<usize>>, rel2: &Vec<Vec<usize>>) -> bool {
    let n = rel1.len();

    for i in 0..n {
        for j in 0.. n {
            if rel1[i][j] == 1 && rel2[j][i] == 1 && i != j {
                return false;
            }
        }
    }
    
    true
}

fn rel_is_reflexive(rel: &Vec<Vec<usize>>) -> bool {
    let n = rel.len();

    for i in 0..n {
        if rel[i][i] == 0 {
            return false;
        }
    }
    true
}

fn rel_is_antisymmetric(rel: &Vec<Vec<usize>>) -> bool {
    let n = rel.len();

    for i in 0..n {
        for j in (i+1)..n {
            if rel[i][j] == 1 && rel[j][i] == 1 {
                return false;
            }
        }
    }

    true
}

fn rel_is_transitive(rel: &Vec<Vec<usize>>) -> bool {
    let n = rel.len();

    for i in 0..n {
        for j in 0..n {
            if rel[i][j] == 1 {
                for k in 0..n {
                    if rel[j][k] ==1 && rel[i][k] == 0 {
                        return false;
                    }
                }
            }
        }
    }
    true
}

fn falg_test_f1(falg: &Vec<Vec<usize>>, b_print: bool) -> bool {
    let n = falg.len();

    for x in 0..n {
        for y in 0..n {
            if falg[x][falg[x][y]] != falg[x][y] {
                if b_print {
                   println!("x = {}, y = {}, F[{}][{}] = {}, F[{}][{}] != F[{}][{}]",
                         x, y, x, y, falg[x][y], x, falg[x][y], x, y);
                }
                return false;
            }
        }
    }

    true
}

fn falg_test_f2(falg: &Vec<Vec<usize>>, b_print: bool) -> bool {
    let n = falg.len();

    for x in 0..n {
        for y in 0..n {
            if falg[falg[x][y]][y] != falg[x][y] {
                if b_print {
                   println!("x = {}, y = {}, F[{}][{}] = {}, F[{}][{}] != F[{}][{}]",
                         x, y, x, y, falg[x][y], x, falg[x][y], x, y);
                }
                return false;
            }
        }
    }

    true
}

fn falg_test_f3(falg: &Vec<Vec<usize>>, b_print: bool) -> bool {
    let n = falg.len();

    for x in 0..n {
        for y in 0..n {
            if falg[x][y] == x {
                for z in 0..n {
                    if falg[y][z] == y && falg[x][z] != x {
                        if b_print {
                            println!("x = {}, y = {}, z = {}, F[{}][{}] = {}, F[{}][{}] = {}, F[{}][{}] = {}",
                                x, y, z, x, y, falg[x][y], y, z, falg[y][z], x, z, falg[x][z]);

                        }
                        return false;
                    }
                }
            }
        }
    }
    true
}

fn falg_test_f4(falg: &Vec<Vec<usize>>, b_print: bool) -> bool {
    let n = falg.len();

    for x in 0..n {
        for y in 0..n {
            if falg[x][y] == y {
                for z in 0..n {
                    if falg[y][z] == z && falg[x][z] != z {
                        if b_print {
                            println!("x = {}, y = {}, z = {}, F[{}][{}] = {}, F[{}][{}] = {}, F[{}][{}] = {}",
                                x, y, z, x, y, falg[x][y], y, z, falg[y][z], x, z, falg[x][z]);

                        }
                        return false;
                    }
                }
            }
        }
    }
    true
}

fn falg_test_f5(falg: &Vec<Vec<usize>>, b_print: bool) -> bool {
    let n = falg.len();

    for x in 0..n {
        for y in 0..n {
            if falg[x][y] == x {
                for z in 0..n {
                    if falg[falg[x][z]][falg[y][z]] != falg[x][z] {
                        if b_print {
                            println!("x = {}, y = {}, z = {}", x, y, z);
                        }
                        return false;
                    }
                }
            }
        }
    }
    true
}

fn falg_test_f6(falg: &Vec<Vec<usize>>, b_print: bool) -> bool {
    let n = falg.len();

    for x in 0..n {
        for y in 0..n {
            if falg[x][y] == y {
                for z in 0..n {
                    if falg[falg[z][x]][falg[z][y]] != falg[z][y] {
                        if b_print {
                            println!("x = {}, y = {}, z = {}", x, y, z);
                        }
                        return false;
                    }
                }
            }
        }
    }
    true
}

fn falg_is_elem_left_annihilator(falg: &Vec<Vec<usize>>, elem: usize) -> bool {
    let n = falg.len();

    for x in 0..n {
        if falg[elem][x] != elem {
            return false;
        }
    }
    true
}

fn falg_is_elem_right_annihilator(falg: &Vec<Vec<usize>>, elem: usize) -> bool {
    let n = falg.len();

    for x in 0..n {
        if falg[x][elem] != elem {
            return false;
        }
    }
    true
}

fn falg_is_elem_left_identity(falg: &Vec<Vec<usize>>, elem: usize) -> bool {
    let n = falg.len();

    for x in 0..n {
        if falg[elem][x] != x {
            return false;
        }
    }
    true
}

fn falg_is_elem_right_identity(falg: &Vec<Vec<usize>>, elem: usize) -> bool {
    let n = falg.len();

    for x in 0..n {
        if falg[x][elem] != x {
            return false;
        }
    }
    true
}

fn falg_is_commutative(falg: &Vec<Vec<usize>>) -> bool {
    let n = falg.len();

    for x in 0..n {
        for y in (x+1)..n {
            if falg[x][y] != falg[y][x] {
                return false;
            }
        }
    }
    true
}

fn falg_is_associative(falg: &Vec<Vec<usize>>) -> bool {
    let n = falg.len();

    for x in 0..n {
        for y in 0..n {
            for z in 0..n {
                if falg[falg[x][y]][z] != falg[x][falg[y][z]] {
                    return false;
                }
            }
        }
    }
    true
}

fn falg_associativity_problems(falg: &Vec<Vec<usize>>) -> Vec<String> {
    let n = falg.len();

    let mut res:Vec<String> = Vec::new();

    for x in 0..n {
        for y in 0..n {
            for z in 0..n {
                let v1 = falg[falg[x][y]][z];
                let v2 = falg[x][falg[y][z]];
                if v1 != v2 {
                    res.push(format!("x = {}, y = {}, z = {}, F(F(x,y),z) = {}, F(x, F(y,z)) = {}",x, y, z, v1, v2));
                }
            }
        }
    }
    res
}

fn falg_is_internal(falg: &Vec<Vec<usize>>) -> bool {
    let n = falg.len();

    for x in 0..n {
        for y in 0..n {
            if falg[x][y] != x && falg[x][y] != y {
                return false;
            }
        }
    }
    true
}

fn falg_transpose(falg: &Vec<Vec<usize>>) -> Vec<Vec<usize>> {
    let n = falg.len();

    let mut trans_falg = allocate_vector(n);

    for x in 0..n {
        for y in 0..n {
            trans_falg[x][y] = falg[y][x];
        }
    }
    trans_falg
}

fn falg_is_less1(falg: &Vec<Vec<usize>>, x: usize, y:usize) -> bool {
    falg[x][y] == x
}

fn falg_is_less2(falg: &Vec<Vec<usize>>, x: usize, y:usize) -> bool {
    falg[y][x] == x
}

fn falg_set_u_xy(falg: &Vec<Vec<usize>>, x: usize, y:usize) -> HashSet<usize> {
    let n = falg.len();

    let mut res_u_xy = HashSet::<usize>::new();

    for q in 0..n {
        if falg_is_less1(falg, q, y) && falg_is_less2(falg, q, x) {
            res_u_xy.insert(q);
        }
    }
    res_u_xy
}

fn rel_pair_set_u_xy(rel1: &Vec<Vec<usize>>, rel2: &Vec<Vec<usize>>, x: usize, y:usize) -> HashSet<usize> {
    let n = rel1.len();

    let mut res_u_xy = HashSet::<usize>::new();

    for q in 0..n {
        if rel1[q][y] == 1 && rel2[q][x] == 1 {
            res_u_xy.insert(q);
        }
    }
    res_u_xy
}

fn falg_set_s1_x(falg: &Vec<Vec<usize>>, x: usize) -> HashSet<usize> {
    let n = falg.len();

    let mut res_s1_x = HashSet::<usize>::new();

    for q in 0..n {
        if falg_is_less1(falg, q, x) && falg_is_less1(falg, x, q) {
            res_s1_x.insert(q);
        }
    }
    res_s1_x
}

fn falg_set_s2_x(falg: &Vec<Vec<usize>>, x: usize) -> HashSet<usize> {
    let n = falg.len();

    let mut res_s2_x = HashSet::<usize>::new();

    for q in 0..n {
        if falg_is_less2(falg, q, x) && falg_is_less2(falg, x, q) {
            res_s2_x.insert(q);
        }
    }
    res_s2_x
}

// # rel_S1x, rel_S2x depends only on used rel
fn rel_set_sn_x(rel: &Vec<Vec<usize>>, x: usize) -> HashSet<usize> {
    let n = rel.len();

    let mut res_sn_x = HashSet::<usize>::new();

    for q in 0..n {
        if rel[q][x] == 1 && rel[x][q] == 1 {
            res_sn_x.insert(q);
        }
    }
    res_sn_x
}

// x dominates y: if x <=_i y then y in Si(x)
fn falg_x_dominates_y(falg: &Vec<Vec<usize>>, x: usize, y:usize) -> bool {
    if falg_is_less1(falg, x, y) && !falg_set_s1_x(falg, x).contains(&y) {
        return false;
    }
    if falg_is_less2(falg, x, y) && !falg_set_s2_x(falg, x).contains(&y) {
        return false;
    }
    true
}

fn rel_pair_x_dominates_y(rel1: &Vec<Vec<usize>>, rel2: &Vec<Vec<usize>>, x: usize, y:usize) -> bool {
    if rel1[x][y] == 1 && !rel_set_sn_x(rel1, x).contains(&y) {
        return false;
    }
    if rel2[x][y] == 1 && !rel_set_sn_x(rel2, x).contains(&y) {
        return false;
    }
    true
}

fn falg_x_strictly_dominates_y(falg: &Vec<Vec<usize>>, x: usize, y:usize) -> bool {
    if falg_is_less1(falg, y, x) && !falg_set_s1_x(falg, x).contains(&y) {
        return true;
    }
    if falg_is_less2(falg, y, x) && !falg_set_s2_x(falg, x).contains(&y) {
        return true;
    }
    false
}

fn rel_pair_x_strictly_dominates_y(rel1: &Vec<Vec<usize>>, rel2: &Vec<Vec<usize>>, x: usize, y:usize) -> bool {
    if rel1[y][x] == 1 && !rel_set_sn_x(rel1, x).contains(&y) {
        return true;
    }
    if rel2[y][x] == 1 && !rel_set_sn_x(rel2, x).contains(&y) {
        return true;
    }
    false
}

fn falg_set_s_xy(falg: &Vec<Vec<usize>>, x: usize, y:usize) -> HashSet<usize> {
    let n = falg.len();
    
    let mut res_set_s_xy = HashSet::<usize>::new();

    let set_u_xy = falg_set_u_xy(falg, x, y);

    for q in set_u_xy.iter() {
        let mut b_dominates = true;

        for u in set_u_xy.iter() {
            if !falg_x_dominates_y(falg, *q, *u) {
                b_dominates = false;
                break;
            }
        }
        if b_dominates {
            res_set_s_xy.insert(*q);
        }
    }
    res_set_s_xy
}

fn rel_pair_set_s_xy(rel1: &Vec<Vec<usize>>, rel2: &Vec<Vec<usize>>, x: usize, y:usize) -> HashSet<usize> {
    let n = rel1.len();
    
    let mut res_set_s_xy = HashSet::<usize>::new();

    let set_u_xy = rel_pair_set_u_xy(rel1, rel2, x, y);

    for q in set_u_xy.iter() {
        let mut b_dominates = true;

        for u in set_u_xy.iter() {
            if !rel_pair_x_dominates_y(rel1, rel2, *q, *u) {
                b_dominates = false;
                break;
            }
        }
        if b_dominates {
            res_set_s_xy.insert(*q);
        }
    }
    res_set_s_xy
}

fn falg_set_t_xy(falg: &Vec<Vec<usize>>, x: usize, y:usize) -> HashSet<usize> {
    if falg[x][y] == x {
        return HashSet::from([x]);
    }

    if falg[x][y] == y {
        return HashSet::from([y]);
    }
    return falg_set_s_xy(falg, x, y);
}

fn rel_pair_set_t_xy(rel1: &Vec<Vec<usize>>, rel2: &Vec<Vec<usize>>, x: usize, y:usize) -> HashSet<usize> {
    if rel1[x][y] == 1 {
        return HashSet::from([x]);
    }

    if rel2[y][x] == 1 {
        return HashSet::from([y]);
    }
    return rel_pair_set_s_xy(rel1, rel2, x, y);
}



fn rel_pair_az_relation(rel1: &Vec<Vec<usize>>, rel2: &Vec<Vec<usize>>, x: usize, y:usize) -> bool {
    // x in S_1^y
    if rel_set_sn_x(rel1, y).contains(&x) {
        return true;
    }
    // x in S_2^y
    if rel_set_sn_x(rel2, y).contains(&x) {
        return true;
    }
    // exists k != x, y: x in S_1^k and y in S_2^k(x)
    let n = rel1.len();
    for k in 0..n {
        if k != x && k != y && rel_set_sn_x(rel1, k).contains(&x) && rel_set_sn_x(rel2, k).contains(&y) {
            return true;
        }
    }
    // exists m != x, y: x in S_2^m and y in S_1^m(x)
    for m in 0..n {
        if m != x && m != y && rel_set_sn_x(rel1, m).contains(&y) && rel_set_sn_x(rel2, m).contains(&x) {
            return true;
        }
    }
    false
}

fn falg_test_cond_n1(falg: &Vec<Vec<usize>>) -> bool {
    let n = falg.len();

    for x in 0..n {
        for y in 0 .. n {
            if x != y {
                for z in 0..n {
                    if x != z && y != z {
                        let set_s_xyz = falg_set_s_xy(falg, falg[x][y], falg[y][z]);

                        if set_s_xyz.len() != 1 {
                            return false;
                        }
                    }
                }
            }
        }
    }
    true
}

fn falg_test_cond_n2(falg: &Vec<Vec<usize>>, b_print: bool) -> bool {
    let n = falg.len();

    for x in 0..n {
        for y in 0..n {
            if falg[x][y] != x {
                for z in 0..n {
                    let s_xyz = falg_set_s_xy(falg, falg[x][y], falg[y][z]);

                    if s_xyz.contains(&x) && s_xyz.contains(&falg[x][y]) {
                        if b_print {
                            println!("N2: x = {}, y = {}, z = {}", x, y, z);
                            println!("    F(x,y) = {}, F(y,z) = {}, S_{{F(x,y),F(y,z)}} = {:?}", falg[x][y], falg[y][z], s_xyz);
                        }
                        return true;
                    }
                }
            }
        }
    }
    false
}

fn falg_test_cond_n3(falg: &Vec<Vec<usize>>, b_print: bool) -> bool {
    let n = falg.len();

    for y in 0..n {
        for z in 0..n {
            if falg[y][z] != z {
                for x in 0..n {
                    let s_xyz = falg_set_s_xy(falg, falg[x][y], falg[y][z]);

                    if s_xyz.contains(&z) && s_xyz.contains(&falg[y][z]) {
                        if b_print {
                            println!("N3: x = {}, y = {}, z = {}", x, y, z);
                            println!("    F(y,z) = {},  F(x,y) = {}, S_{{F(x,y),F(y,z)}} = {:?}", falg[y][z], falg[x][y], s_xyz);
                        }
                        return true;
                    }
                }
            }
        }
    }
    false
}

fn falg_test_cond_n4(falg: &Vec<Vec<usize>>, b_print: bool) -> bool {
    let n = falg.len();

    for x in 0..n {
        for y in 0..n {
            for yp in 0..n {
                if falg[x][y] == falg[x][yp] {
                    for z in 0..n {
                        for zp in 0.. n {
                            if z != zp && falg[y][z] == falg[yp][zp] {
                                let u = falg[x][y];
                                let v = falg[y][z];
                                let s_uv = falg_set_s_xy(falg, u, v);
                                if s_uv.contains(&z) && s_uv.contains(&zp) {
                                    if b_print {
                                        println!("N4: x = {}, y = {}, y' = {}, z' = {}, z' = {}", x, y, yp, z, zp);
                                        println!("    F(x,y) = F(x,y') = {}, F(y,z) = F(y',z') = {}, S_u,v = {:?}", u, v, s_uv)
                                    }
                                    return true;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    false
}

fn falg_test_cond_n5(falg: &Vec<Vec<usize>>, b_print: bool) -> bool {
    let n = falg.len();

    for z in 0..n {
        for y in 0..n {
            for yp in 0..n {
                if falg[y][z] == falg[yp][z] {
                    for x in 0..n {
                        for xp in 0.. n {
                            if x != xp && falg[x][y] == falg[xp][yp] {
                                let u = falg[x][y];
                                let v = falg[y][z];
                                let s_uv = falg_set_s_xy(falg, u, v);
                                if s_uv.contains(&x) && s_uv.contains(&xp) {
                                    if b_print {
                                        println!("N5: x = {}, x' = {}, y = {}, y' = {}, z = {}", x, xp, y, yp, z);
                                        println!("     F(x,y) = F(x',y') = {}, F(y,z) = F(y',z) = {}, S_u,v = {:?}", u, v, s_uv)
                                    }
                                    return true;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    false
}
