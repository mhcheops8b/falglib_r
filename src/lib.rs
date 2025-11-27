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
use std::io::Write;
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

// new condition to reduce allowed pairs [TODO]
pub fn rel_quasi_order_preserves_order_test(rel_qord:&Vec<Vec<usize>>) -> bool {
    let n = rel_qord.len();

    for x in 0.. n {
        for y in 0 .. n {
            if x > y && rel_qord[x][y] == 1 && rel_qord[y][x] == 0 {
                let mut b_found = false;
                for t in 0..y {
                    if rel_qord[t][y] == 1 && rel_qord[t][x] == 1 && rel_qord[x][t] == 1 {
                        b_found = true;
                        break;
                    }
                }
                if !b_found {
                    return false;
                }
            }
        }
    }
    true
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

// quasi order maximal repr
pub fn rel_quasi_order_find_max_repr(rel_qord:&Vec<Vec<usize>>) -> Vec<Vec<usize>> {    
    let n = rel_qord.len();
    
    let mut b_repr_max_rel_qord = false;

    let mut perm = (0..n).into_iter().collect::<Vec<_>>();

    let mut max_rel_qord_repr = allocate_vector(n);
    loop {
        //if rel_quasi_order_perm_preserves_canonical_quasi_order(&c_rel_qord, &perm) {
        let rel_qord_iso = rel_isomorphic_image(&rel_qord, &perm);
        if !b_repr_max_rel_qord {
            max_rel_qord_repr = rel_qord_iso;
            b_repr_max_rel_qord = true;
        }
        else {
            // compare new representation
            if rel_quasi_order_is_greater_rel(&rel_qord_iso, &max_rel_qord_repr) {
                max_rel_qord_repr = rel_qord_iso;
            }
        }

        //}
        
        if !permlib::next_perm(&mut perm, n) {
            break;
        }
    }

    max_rel_qord_repr
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

pub fn rel_are_pair_antisymmetric(rel1: &Vec<Vec<usize>>, rel2: &Vec<Vec<usize>>) -> bool {
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

pub fn rel_isomorphic_expand(qord: &Vec<Vec<usize>>) -> (HashSet<Vec<Vec<usize>>>, HashMap<Vec<usize>, Vec<Vec<usize>>>) {
    let size = qord.len();
    let mut perm = Vec::<usize>::new();
    for i in 0..size {
        perm.push(i);
    }

    let mut res: HashSet<Vec<Vec<usize>>> = HashSet::new();
    let mut permiso: HashMap<Vec<usize>, Vec<Vec<usize>>> = HashMap::new();

    let mut old_size =res.len();
    loop {

        let iso_image = rel_isomorphic_image(&qord, &perm);

        res.insert(iso_image.clone());

        if old_size != res.len() {
            // println!("\tNew {:?}", iso_image);
            permiso.insert(perm.clone(), iso_image);

            old_size = res.len();
        }
      
        if !permlib::next_perm(&mut perm, size) {
            break;
        }
    }

    (res, permiso)
}

pub fn rel_isomorphic_expand_vec(qord: &Vec<Vec<usize>>) -> (Vec<Vec<Vec<usize>>>, HashMap<Vec<usize>, Vec<Vec<usize>>>) {
    let size = qord.len();
    let mut perm = Vec::<usize>::new();
    for i in 0..size {
        perm.push(i);
    }

    let mut res: HashSet<Vec<Vec<usize>>> = HashSet::new();
    let mut resvec: Vec<Vec<Vec<usize>>> = Vec::new();
    let mut permiso: HashMap<Vec<usize>, Vec<Vec<usize>>> = HashMap::new();

    let mut old_size =res.len();
    loop {

        let iso_image = rel_isomorphic_image(&qord, &perm);

        res.insert(iso_image.clone());

        if old_size != res.len() {
            // println!("\tNew {:?}", iso_image);
            resvec.push(iso_image.clone());
            permiso.insert(perm.clone(), iso_image);

            old_size = res.len();
        }
      
        if !permlib::next_perm(&mut perm, size) {
            break;
        }
    }

    (resvec, permiso)
}

pub fn rel_isomorphic_expand_full_size(qord: &Vec<Vec<usize>>) -> usize {
    let size = qord.len();
    let mut perm = Vec::<usize>::new();
    for i in 0..size {
        perm.push(i);
    }

    let mut res: HashSet<Vec<Vec<usize>>> = HashSet::new();
    
    loop {

        let iso_image = rel_isomorphic_image(&qord, &perm);

        res.insert(iso_image.clone());
      
        if !permlib::next_perm(&mut perm, size) {
            break;
        }
    }

    res.len()
}



// new condition applied 
pub fn rel_isomorphic_expand_reduced_vec(qord: &Vec<Vec<usize>>) -> (Vec<Vec<Vec<usize>>>, HashMap<Vec<usize>, Vec<Vec<usize>>>) {
    let size = qord.len();
    let mut perm = Vec::<usize>::new();
    for i in 0..size {
        perm.push(i);
    }

    let mut res: HashSet<Vec<Vec<usize>>> = HashSet::new();
    let mut resvec: Vec<Vec<Vec<usize>>> = Vec::new();
    let mut permiso: HashMap<Vec<usize>, Vec<Vec<usize>>> = HashMap::new();

    let mut old_size =res.len();
    loop {

        let iso_image = rel_isomorphic_image(&qord, &perm);
        if rel_quasi_order_preserves_order_test(&iso_image) {
            res.insert(iso_image.clone());

            if old_size != res.len() {
                // println!("\tNew {:?}", iso_image);
                resvec.push(iso_image.clone());
                permiso.insert(perm.clone(), iso_image);

                old_size = res.len();
            }
        }
      
        if !permlib::next_perm(&mut perm, size) {
            break;
        }
    }

    (resvec, permiso)
}


pub fn rel_is_reflexive(rel: &Vec<Vec<usize>>) -> bool {
    let n = rel.len();

    for i in 0..n {
        if rel[i][i] == 0 {
            return false;
        }
    }
    true
}

pub fn rel_is_antisymmetric(rel: &Vec<Vec<usize>>) -> bool {
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

pub fn rel_is_transitive(rel: &Vec<Vec<usize>>) -> bool {
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

pub fn falg_test_f1(falg: &Vec<Vec<usize>>, b_print: bool) -> bool {
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

pub fn falg_test_f2(falg: &Vec<Vec<usize>>, b_print: bool) -> bool {
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

pub fn falg_test_f3(falg: &Vec<Vec<usize>>, b_print: bool) -> bool {
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

pub fn falg_test_f4(falg: &Vec<Vec<usize>>, b_print: bool) -> bool {
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

pub fn falg_test_f5(falg: &Vec<Vec<usize>>, b_print: bool) -> bool {
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

pub fn falg_test_f6(falg: &Vec<Vec<usize>>, b_print: bool) -> bool {
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

pub fn falg_all_tests_no_print(falg: &Vec<Vec<usize>>) -> bool {
    falg_test_f3(falg, false) &&
    falg_test_f4(falg, false) &&
    falg_test_f5(falg, false) &&
    falg_test_f6(falg, false) &&
    falg_test_f1(falg, false) &&
    falg_test_f2(falg, false)
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

pub fn falg_transpose(falg: &Vec<Vec<usize>>) -> Vec<Vec<usize>> {
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

pub fn falg_get_qord1(falg: &Vec<Vec<usize>>) -> Vec<Vec<usize>> {
    let n = falg.len();
    let mut qord_res = allocate_vector(n);

    for i in 0..n {
        for j in 0..n {
            if i==j || falg_is_less1(&falg, i, j) {
                qord_res[i][j] = 1;
            }
        }
    }

    qord_res
}

fn falg_is_less2(falg: &Vec<Vec<usize>>, x: usize, y:usize) -> bool {
    falg[y][x] == x
}

// pub fn falg_get_qord1(falg: &Vec<Vec<usize>>) -> Vec<Vec<usize>> {
//     let n = falg.len();

//     let mut qord1_res = allocate_vector(n);

//     for x in 0..n {
//         for y in 0..n {
//             if falg_is_less1(falg, x, y) {
//                 qord1_res[x][y] = 1
//             }
//         }
//     }
//     qord1_res
// }

pub fn falg_get_qord2(falg: &Vec<Vec<usize>>) -> Vec<Vec<usize>> {
    let n = falg.len();

    let mut qord2_res = allocate_vector(n);

    for x in 0..n {
        for y in 0..n {
            if falg_is_less2(falg, x, y) {
                qord2_res[x][y] = 1
            }
        }
    }
    qord2_res
}


// pub fn falg_get_qord2(falg: &Vec<Vec<usize>>) -> Vec<Vec<usize>> {
//     let n = falg.len();
//     let mut qord_res = allocate_vector(n);

//     for i in 0..n {
//         for j in 0..n {
//             if i==j || falg_is_less2(&falg, i, j) {
//                 qord_res[i][j] = 1;
//             }
//         }
//     }

//     qord_res
// }

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

pub fn rel_is_stabilizer_perm(rel: &Vec<Vec<usize>>, perm: &Vec<usize>) -> bool {
    let n = perm.len();

    for i in 0..n {
        for j in 0..n {
            if rel[i][j] == 1 && rel[perm[i]][perm[j]] != 1 {
                return false;
            }
            if rel[perm[i]][perm[j]] == 1 && rel[i][j] != 1 {
                return false;
            }
        }
    }
    true
}

pub fn rel_get_stabilizer_perms(rel: &Vec<Vec<usize>>) -> HashSet<Vec<usize>> {
    let n = rel.len();
    let mut res = HashSet::<Vec<usize>>::new();

    let mut perm = (0..n).collect::<Vec<_>>();
    loop {
        if rel_is_stabilizer_perm(&rel, &perm) {
            res.insert(perm.clone());
        }
        if !permlib::next_perm(&mut perm, n) {
            break;
        }
    }

    res
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



pub fn rel_count_strict_minimal_elements(qord: &Vec<Vec<usize>>) -> usize {
    let n = qord.len();
    let mut min_count= 0usize;
    for x in 0..n {
        let mut bfound = false;
        for t in 0..n {
            if t != x && qord[t][x] == 1 {
                bfound=true;
                break;
            }
        }
        if !bfound {
            min_count+=1;
        }
    }
    min_count
}

pub fn rel_is_equiv(qord:&Vec<Vec<usize>>, x: usize, y:usize) -> bool {
    qord[x][y] == 1 && qord[y][x]==1
}

pub fn rel_get_classes_map(qord:&Vec<Vec<usize>>) -> HashMap<usize, Vec<usize>> {
    let n = qord.len();

    let mut b_has_class_vec = Vec::<bool>::new();
    let mut id_to_cls_vec_map = HashMap::<usize, Vec<usize>>::new();
    for i in 0..n {
        b_has_class_vec.push(false);
    }

    let mut last_class_id = 0usize;
    for x in 0..n {
        if !b_has_class_vec[x] {
            last_class_id +=1;
            id_to_cls_vec_map.insert(last_class_id, Vec::from([x]));

            for y in (x+1)..n {
                if rel_is_equiv(qord, x, y) {
                    b_has_class_vec[y] = true;
                    id_to_cls_vec_map.get_mut(&last_class_id).unwrap().push(y);

                }
            }
        }
    }
    id_to_cls_vec_map 
}

pub fn rel_get_classes_cover_rel(qord:&Vec<Vec<usize>>, cls_map:&HashMap<usize, Vec<usize>>) -> Vec<Vec<usize>> {
    let n = cls_map.len();

    let mut vec_res = Vec::<Vec<usize>>::new();
    for i in 0..n {
        vec_res.push(Vec::<usize>::new());
        for _ in 0..n {
            vec_res[i].push(0);
        }

    }

    for i in 1..=n {
        for j in 1..=n {
            if i != j {
                let x_i = cls_map.get(&i).unwrap()[0];
                let x_j = cls_map.get(&j).unwrap()[0];
                if qord[x_i][x_j] == 1 {
                    let mut b_found = false;
                    for k in 1..=n {
                        if k != i && k != j {
                            let x_k = cls_map.get(&k).unwrap()[0];
                            if qord[x_i][x_k] == 1 && qord[x_k][x_j] == 1 {
                                b_found = true;
                                break;
                            }
                        }
                    }
                    if !b_found {
                        vec_res[i-1][j-1] = 1;
                    }
                }
            }
        }
    }
    vec_res
}

pub fn cov_rel_get_class_coords(cov_rel: &Vec<Vec<usize>>) -> Vec<(usize,usize)> {
    let n = cov_rel.len();

    let mut max_levels = Vec::<usize>::new();
    let mut x_coords = Vec::<usize>::new();
    let mut last_x_coord = Vec::<usize>::new();
    for _ in 0..n {
        max_levels.push(0);
        x_coords.push(0);
        last_x_coord.push(0);
    }

    for i in 0..n {
        if max_levels[i] == 0 {
            max_levels[i] = 1;
      //      x_coords[i] = 
        }
        for j in 0..n {
            if cov_rel[i][j] == 1 {
                max_levels[j] = std::cmp::max(max_levels[j], max_levels[i] + 1);
            }
        }
    }
    //println!("{:?}", max_levels);
    for j in 0..n {
        last_x_coord[max_levels[j] - 1] +=1;
        x_coords[j] = last_x_coord[max_levels[j] - 1]; 
    }
    //println!("{:?}", x_coords);
    let iter = std::iter::zip(x_coords,max_levels);
    let v:Vec<_> = iter.map(|(a,b)| (a-1,b-1)).collect();

    v
}

pub fn cov_rel_get_class_coords_perm(cov_rel: &Vec<Vec<usize>>, perm: &Vec<usize>) -> Vec<(usize,usize)> {
    let n = cov_rel.len();

    let mut max_levels = Vec::<usize>::new();
    let mut x_coords = Vec::<usize>::new();
    let mut last_x_coord = Vec::<usize>::new();
    for _ in 0..n {
        max_levels.push(0);
        x_coords.push(0);
        last_x_coord.push(0);
    }

    for i in 0..n {
        if max_levels[i] == 0 {
            max_levels[i] = 1;
      //      x_coords[i] = 
        }
        for j in 0..n {
            if cov_rel[i][j] == 1 {
                max_levels[j] = std::cmp::max(max_levels[j], max_levels[i] + 1);
            }
        }
    }
    //println!("{:?}", max_levels);
    for j in 0..n {
        last_x_coord[max_levels[perm[j]] - 1] +=1;
        x_coords[perm[j]] = last_x_coord[max_levels[perm[j]] - 1]; 
    }
    //println!("{:?}", x_coords);
    let iter = std::iter::zip(x_coords,max_levels);
    let v:Vec<_> = iter.map(|(a,b)| (a-1,b-1)).collect();

    v
}

pub fn _rel_qord_print_tikz(cls_map: &HashMap<usize, Vec<usize>>, cov_rel: &Vec<Vec<usize>>, cls_coords: &Vec<(usize, usize)>) {
    println!("\\tikz {{");
    for i in 1..=cov_rel.len() {
        print!("\\node [circle,fill,label={{[name=cls{}]below:$", i);
        let mut b_first = true;
        for e in &cls_map[&i] {
            if b_first {
                b_first = false;
            }
            else {
                print!(", ");
            }
            print!("{}", e);
        }
            
        println!("$}}] at {:?} {{}};", cls_coords[i-1]);
    }
    for i in 0..cov_rel.len() {
        for j in 0..cov_rel.len() {
            if cov_rel[i][j] == 1 {
                println!("\\draw {:?} -- {:?};", cls_coords[i], cls_coords[j]);
            }
        }
    }
    println!("}}");
}

pub fn rel_qord_print_tikz(qord: &Vec<Vec<usize>>) {//cls_map: &HashMap<usize, Vec<usize>>, cov_rel: &Vec<Vec<usize>>, cls_coords: &Vec<(usize, usize)>) {
    let cls_map = rel_get_classes_map(&qord);
    let cov_rel = rel_get_classes_cover_rel(&qord, &cls_map);
    let cls_coords = cov_rel_get_class_coords(&cov_rel);
    _rel_qord_print_tikz(&cls_map, &cov_rel, &cls_coords);
}


// minimal classes
pub fn rel_count_strict_minimal_classes(qord: &Vec<Vec<usize>>) -> usize {
    let n = qord.len();
    let mut min_cls_count= 0usize;
    let mut min_cands_set:HashSet<usize> = HashSet::new();
    let mut min_cands_map:HashMap<usize,usize> = HashMap::new();
    for x in 0..n {
        let mut bfound = false;
        for t in 0..n {
            if t != x && qord[t][x] == 1 && qord[x][t] == 0 {
                bfound=true;
                break;
            }
        }
        if !bfound {
            let mut b_already_repr = false;
            for t in &min_cands_set {
                if rel_is_equiv(qord, *t, x) {
                    b_already_repr = true;
                    if let Some(val) = min_cands_map.get_mut(t) {
                        *val+=1;
                    }
                }
            }
            if !b_already_repr {
                min_cands_set.insert(x);
                min_cands_map.insert(x, 1);
            }
        }
    }
    min_cands_set.len()
}

pub fn rel_get_strict_minimal_classes(qord: &Vec<Vec<usize>>) -> (HashSet<usize>, HashMap<usize,usize>) {
    let n = qord.len();
    let mut min_cls_count= 0usize;
    let mut min_cands_set:HashSet<usize> = HashSet::new();
    let mut min_cands_map:HashMap<usize,usize> = HashMap::new();
    for x in 0..n {
        let mut bfound = false;
        for t in 0..n {
            if t != x && qord[t][x] == 1 && qord[x][t] == 0 {
                bfound=true;
                break;
            }
        }
        if !bfound {
            let mut b_already_repr = false;
            for t in &min_cands_set {
                if rel_is_equiv(qord, *t, x) {
                    b_already_repr = true;
                    if let Some(val) = min_cands_map.get_mut(t) {
                        *val+=1;
                    }
                }
            }
            if !b_already_repr {
                min_cands_set.insert(x);
                min_cands_map.insert(x, 1);
            }
        }
    }
    (min_cands_set, min_cands_map)
}

pub fn rel_get_strict_minimal_classes2(qord: &Vec<Vec<usize>>) -> (HashSet<usize>, HashMap<usize,HashSet<usize>>) {
    let n = qord.len();
    let mut min_cls_count= 0usize;
    let mut min_cands_set:HashSet<usize> = HashSet::new();
    let mut min_cands_map:HashMap<usize,HashSet<usize>> = HashMap::new();
    for x in 0..n {
        let mut bfound = false;
        for t in 0..n {
            if t != x && qord[t][x] == 1 && qord[x][t] == 0 {
                bfound=true;
                break;
            }
        }
        if !bfound {
            let mut b_already_repr = false;
            for t in &min_cands_set {
                if rel_is_equiv(qord, *t, x) {
                    b_already_repr = true;

                    if let Some(val) = min_cands_map.get_mut(t) {
                        val.insert(x);
                    }
                }
            }
            if !b_already_repr {
                min_cands_set.insert(x);
                min_cands_map.insert(x, HashSet::from([x]));
            }
        }
    }
    (min_cands_set, min_cands_map)
}

// minimal classes
pub fn rel_strict_minimal_classes_le_one(qord: &Vec<Vec<usize>>) -> bool {
    let n = qord.len();
    let mut min_cands_set:HashSet<usize> = HashSet::new();
    for x in 0..n {
        let mut bfound = false;
        for t in 0..n {
            if t != x && qord[t][x] == 1 && qord[x][t] == 0 {
                bfound=true;
                break;
            }
        }
        if !bfound {
            let mut b_already_repr = false;
            for t in &min_cands_set {
                if rel_is_equiv(qord, *t, x) {
                    b_already_repr = true;
                }
            }
            if !b_already_repr {
                min_cands_set.insert(x);
            }
            if min_cands_set.len() > 1 {
                return false;
            }
        }
    }
    true
}

// quick check for rel_count_strict_minimal_elements, if >= 2 false, else true
pub fn rel_strict_minimal_elements_le_one(qord: &Vec<Vec<usize>>) -> bool {
    let n = qord.len();
    let mut min_count= 0usize;
    for x in 0..n {
        if min_count > 1 {
            return false;
        }
        let mut bfound = false;
        for t in 0..n {
            if t != x && qord[t][x] == 1 {
                bfound=true;
                break;
            }
        }
        if !bfound {
            min_count+=1;
        }
    }
    true
}


fn rel_pair_has_candidates_check_pair(qord1:&Vec<Vec<usize>>, qord2:&Vec<Vec<usize>>, x: usize, y:usize) -> bool {
    // x <=_1 y -> (x,y) = x or y <=_2 x (x,y) = y
    if qord1[x][y] == 1 || qord2[y][x] == 1 {
        return true;
    }
    
    for t in 0..qord1.len() {
        if t != x && t != y && qord1[t][y] == 1 && qord2[t][x] == 1 {
            return true;
        }
    }
    false
}

pub fn rel_pair_has_all_candidates_check(qord1:&Vec<Vec<usize>>, qord2:&Vec<Vec<usize>>) -> bool {
    let n = qord1.len();
    for x in 0..n {
        for y in x+1..n {
            if  !rel_pair_has_candidates_check_pair(qord1, qord2, x, y) ||
                !rel_pair_has_candidates_check_pair(qord1, qord2, y, x) {
                    return false;
                }
        }
    }
    return true;
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

pub fn falg_isomorphic_image(falg: &Vec<Vec<usize>>, perm: &Vec<usize>) -> Vec<Vec<usize>> {
    let size = perm.len();
    let mut res = allocate_vector(size);
    
    for i in 0..size {
        for j in  0..size {
            res[perm[i]][perm[j]] = perm[falg[i][j]];
        }
    }

    res
}

pub fn falg_isomorphic_expand(falg: &Vec<Vec<usize>>) -> (HashSet<Vec<Vec<usize>>>, HashMap<Vec<usize>, Vec<Vec<usize>>>) {
    let size = falg.len();
    let mut perm = Vec::<usize>::new();
    for i in 0..size {
        perm.push(i);
    }

    let mut res: HashSet<Vec<Vec<usize>>> = HashSet::new();
    let mut permiso: HashMap<Vec<usize>, Vec<Vec<usize>>> = HashMap::new();

    let mut old_size =res.len();
    loop {

        let iso_image = falg_isomorphic_image(&falg, &perm);

        res.insert(iso_image.clone());

        if old_size != res.len() {
            // println!("\tNew {:?}", iso_image);
            permiso.insert(perm.clone(), iso_image);

            old_size = res.len();
        }
      
        if !permlib::next_perm(&mut perm, size) {
            break;
        }
    }

    (res, permiso)
}

pub fn falg_init(size: usize) -> Vec<Vec<usize>> {
    let mut falg_res = Vec::<Vec<usize>>::new();

    for x in 0..size {
        falg_res.push(Vec::<usize>::new());
        for y in 0..size {
            if x == y {
                falg_res[x].push(x);
            }
            else {
                falg_res[x].push(0);
            }
        }
    }
    falg_res
}

// based on generate_As_with_ords3
pub fn falg_generate_with_qords(qord1: &Vec<Vec<usize>>, qord2: &Vec<Vec<usize>>) -> bool {
    let n = qord1.len();
    let mut falg = falg_init(n);
    let mut b_filled_arr = Vec::<Vec<bool>>::new();
    // init b_filled_arr
    for x in 0..n {
        b_filled_arr.push(Vec::<bool>::new());
        for y in 0..n {
            if x == y {
                b_filled_arr[x].push(true);
            }
            else {
                b_filled_arr[x].push(false);
            }
        }
    }
    // quasi-order induced fillings
    // x <=_1 y, iff A[x][y] == x
    // x <=_2 y, iff A[y][x] == x
    for x in 0..n {
        for y in 0..n {
            if x != y {
                if qord1[x][y] == 1 {
                    if !b_filled_arr[x][y] {
                        falg[x][y] = x;
                        b_filled_arr[x][y] = true;
                    }
                    else {
                        if falg[x][y] != x {
                            // eprintln!("HH1");
                            return false;
                        }
                    }
                }
                if qord2[x][y] == 1 {
                    if !b_filled_arr[y][x] {
                        falg[y][x] = x;
                        b_filled_arr[y][x] = true;
                    }
                    else {
                        if falg[y][x] != x {
                            // eprintln!("HH2");
                            return false;
                        }
                    }
                }
            }
        }
    }

    // F5 consequence x <=_1 y => A[ A[x][z] ][ A[y][z]] = A[x][z] <=> A[x][z] <=_1 A[y][z]
    // for z = x: x <=_1 A[y][x]
    // F6 consequence x <=_2 y => A[z][x] <=_2 A[z][y]
    // for z = x: x  <=_2 A[x][y]
    for x in 0..n {
        for y in 0..n {
            if x != y {
                if b_filled_arr[x][y] && b_filled_arr[y][x] {
                    if qord1[x][y] == 1 && qord1[x][falg[y][x]] != 1 {
                        // eprintln!("HH3");
                        return false;
                    }
                    if qord2[x][y] == 1 && qord2[x][falg[x][y]] != 1 {
                        // eprintln!("HH4");
                        return false;
                    }
                }
            }
        }
    }
    let mut cand_idx = 0usize;
    let mut missing_cnt = 0usize;
    let mut cands_map = HashMap::<usize, HashSet<usize>>::new();
    let mut pairs_map = HashMap::<usize, (usize, usize)>::new();
    let mut pairs_inv_map = HashMap::<(usize, usize), usize>::new();
    for x in 0..n {
        for y in 0..n {
            if x != y {
                if !b_filled_arr[x][y] {
                    missing_cnt += 1;
                    let mut fill_candidates = rel_pair_set_s_xy(qord1, qord2, x, y);
                    // remove x, y if present
                    // (x,y) is unfilled, thus it holds ! x<=_1 y and ! y <=_2 x
                    fill_candidates.remove(&x);
                    fill_candidates.remove(&y);
                    // let mut fill_candidates = HashSet::<usize>::new();

                    // // Assumption q = A[x][y], 
                    // // since x !<=_1 y and y !<=_2 x
                    // // A[x][y] != x, y
                    // for q in 0..n {
                    //     // F1: A[x][y] <=_2 x
                    //     if qord2[q][x] == 1 {
                    //         if q != x {
                    //             fill_candidates.insert(q);
                    //         }
                    //     }
                    //     // F2: A[x][y] <=_1 y
                    //     if qord1[q][y] == 1 {
                    //         if q != y {
                    //             fill_candidates.insert(q);
                    //         }
                    //     }
                    // }
                    let fc_size = fill_candidates.len();
                    // no candidates to fill (x,y)
                    if fc_size == 0 {
                        // eprintln!("No candidates for ({x}, {y})");
                        return false;
                    }
                    if fc_size == 1 {
                        if let Some(&c) = fill_candidates.iter().next() {
                            falg[x][y] = c;
                            b_filled_arr[x][y] = true;
                            missing_cnt -= 1;
                        }
                    }
                    else {
                        cands_map.insert(cand_idx, fill_candidates);
                        pairs_map.insert(cand_idx, (x,y));
                        pairs_inv_map.insert((x,y), cand_idx);
                    }
                }
                cand_idx +=1;
            }
        }
    }
    if missing_cnt == 0 {
        if falg_all_tests_no_print(&falg) {
            println!("{:?}", falg);
        }
    }
    else {
        // eprintln!("missing: {}", missing_cnt);
        // eprintln!("candidates: {cands_map:?}");
        // eprintln!("pairs: {pairs_map:?}");
        // eprintln!("inv pairs: {pairs_inv_map:?}");
        let mut key_arr = pairs_map.keys().map(|&x| x).collect::<Vec<_>>();
        key_arr.sort();
        // eprintln!("map keys: {key_arr:?}");
        falg_fill_missing_v3(0, &key_arr, &cands_map, &pairs_map, &pairs_inv_map, qord1, qord2, &mut falg, &mut b_filled_arr);
    }
    true
}

pub fn falg_generate_with_qords_writer(out_writer: &mut &std::fs::File, qord1: &Vec<Vec<usize>>, qord2: &Vec<Vec<usize>>) -> bool {
    let n = qord1.len();
    let mut falg = falg_init(n);
    let mut b_filled_arr = Vec::<Vec<bool>>::new();
    // init b_filled_arr
    for x in 0..n {
        b_filled_arr.push(Vec::<bool>::new());
        for y in 0..n {
            if x == y {
                b_filled_arr[x].push(true);
            }
            else {
                b_filled_arr[x].push(false);
            }
        }
    }
    // quasi-order induced fillings
    // x <=_1 y, iff A[x][y] == x
    // x <=_2 y, iff A[y][x] == x
    for x in 0..n {
        for y in 0..n {
            if x != y {
                if qord1[x][y] == 1 {
                    if !b_filled_arr[x][y] {
                        falg[x][y] = x;
                        b_filled_arr[x][y] = true;
                    }
                    else {
                        if falg[x][y] != x {
                            // eprintln!("HH1");
                            return false;
                        }
                    }
                }
                if qord2[x][y] == 1 {
                    if !b_filled_arr[y][x] {
                        falg[y][x] = x;
                        b_filled_arr[y][x] = true;
                    }
                    else {
                        if falg[y][x] != x {
                            // eprintln!("HH2");
                            return false;
                        }
                    }
                }
            }
        }
    }

    // F5 consequence x <=_1 y => A[ A[x][z] ][ A[y][z]] = A[x][z] <=> A[x][z] <=_1 A[y][z]
    // for z = x: x <=_1 A[y][x]
    // F6 consequence x <=_2 y => A[z][x] <=_2 A[z][y]
    // for z = x: x  <=_2 A[x][y]
    for x in 0..n {
        for y in 0..n {
            if x != y {
                if b_filled_arr[x][y] && b_filled_arr[y][x] {
                    if qord1[x][y] == 1 && qord1[x][falg[y][x]] != 1 {
                        // eprintln!("HH3");
                        return false;
                    }
                    if qord2[x][y] == 1 && qord2[x][falg[x][y]] != 1 {
                        // eprintln!("HH4");
                        return false;
                    }
                }
            }
        }
    }
    let mut cand_idx = 0usize;
    let mut missing_cnt = 0usize;
    let mut cands_map = HashMap::<usize, HashSet<usize>>::new();
    let mut pairs_map = HashMap::<usize, (usize, usize)>::new();
    let mut pairs_inv_map = HashMap::<(usize, usize), usize>::new();
    for x in 0..n {
        for y in 0..n {
            if x != y {
                if !b_filled_arr[x][y] {
                    missing_cnt += 1;
                    let mut fill_candidates = rel_pair_set_s_xy(qord1, qord2, x, y);
                    // remove x, y if present
                    // (x,y) is unfilled, thus it holds ! x<=_1 y and ! y <=_2 x
                    fill_candidates.remove(&x);
                    fill_candidates.remove(&y);
                    // let mut fill_candidates = HashSet::<usize>::new();

                    // // Assumption q = A[x][y], 
                    // // since x !<=_1 y and y !<=_2 x
                    // // A[x][y] != x, y
                    // for q in 0..n {
                    //     // F1: A[x][y] <=_2 x
                    //     if qord2[q][x] == 1 {
                    //         if q != x {
                    //             fill_candidates.insert(q);
                    //         }
                    //     }
                    //     // F2: A[x][y] <=_1 y
                    //     if qord1[q][y] == 1 {
                    //         if q != y {
                    //             fill_candidates.insert(q);
                    //         }
                    //     }
                    // }
                    let fc_size = fill_candidates.len();
                    // no candidates to fill (x,y)
                    if fc_size == 0 {
                        // eprintln!("No candidates for ({x}, {y})");
                        return false;
                    }
                    if fc_size == 1 {
                        if let Some(&c) = fill_candidates.iter().next() {
                            falg[x][y] = c;
                            b_filled_arr[x][y] = true;
                            missing_cnt -= 1;
                        }
                    }
                    else {
                        cands_map.insert(cand_idx, fill_candidates);
                        pairs_map.insert(cand_idx, (x,y));
                        pairs_inv_map.insert((x,y), cand_idx);
                    }
                }
                cand_idx +=1;
            }
        }
    }
    if missing_cnt == 0 {
        if falg_all_tests_no_print(&falg) {
            writeln!(out_writer, "{:?}", falg).unwrap();
            //println!("{:?}", falg);
        }
    }
    else {
        // eprintln!("missing: {}", missing_cnt);
        // eprintln!("candidates: {cands_map:?}");
        // eprintln!("pairs: {pairs_map:?}");
        // eprintln!("inv pairs: {pairs_inv_map:?}");
        let mut key_arr = pairs_map.keys().map(|&x| x).collect::<Vec<_>>();
        key_arr.sort();
        // eprintln!("map keys: {key_arr:?}");
        falg_fill_missing_v3_writer(out_writer, 0, &key_arr, &cands_map, &pairs_map, &pairs_inv_map, qord1, qord2, &mut falg, &mut b_filled_arr);
    }
    true
}


// no speculative tests
pub fn falg_fill_missing_v0(cur_idx:usize, key_arr:&Vec<usize>, cands_map: &HashMap<usize, HashSet<usize>>, pairs_map: &HashMap<usize, (usize, usize)>, pairs_inv_map: &HashMap<(usize, usize), usize>, part_falg: &mut Vec<Vec<usize>>, part_b_filled_arr: &mut Vec<Vec<bool>>) {
    if cur_idx == cands_map.len() {
        // test conditions for falg
        if falg_all_tests_no_print(part_falg) {
            println!("{:?}", part_falg);
        }
    }
    else {
        let key_idx = key_arr[cur_idx];
        let cur_cands = cands_map.get(&key_idx).unwrap();
        let (cur_x, cur_y) = pairs_map.get(&key_idx).unwrap();
        for c in cur_cands {
            // no tests
            part_falg[*cur_x][*cur_y] = *c;
            part_b_filled_arr[*cur_x][*cur_y] = true;
            falg_fill_missing_v0(cur_idx + 1, key_arr, cands_map, pairs_map, pairs_inv_map, part_falg, part_b_filled_arr);
            part_falg[*cur_x][*cur_y] = 0;
            part_b_filled_arr[*cur_x][*cur_y] = false;
        }
    }

}

// with speculative tests
// test forced rules
// c = A[x][y]
// F1: F(x, F(x,c)) = F(x,c) = c
pub fn falg_fill_missing_v1(cur_idx:usize, key_arr: &Vec<usize>, cands_map: &HashMap<usize, HashSet<usize>>, pairs_map: &HashMap<usize, (usize, usize)>, pairs_inv_map: &HashMap<(usize, usize), usize>, part_falg: &mut Vec<Vec<usize>>, part_b_filled_arr: &mut Vec<Vec<bool>>) {
    if cur_idx == cands_map.len() {
        // test conditions for falg
        if falg_all_tests_no_print(part_falg) {
            println!("{:?}", part_falg);
        }
    }
    else {
        let key_idx = key_arr[cur_idx];
        let cur_cands = cands_map.get(&key_idx).unwrap();
        let (cur_x, cur_y) = *pairs_map.get(&key_idx).unwrap();
        for &c in cur_cands {
            // c = F(x,y)
            // F1: F(x, F(x,c)) = F(x,c) = c
            if part_b_filled_arr[cur_x][c] && part_falg[cur_x][c] != c {
                continue;
            }
            // F2: F(F(c,y),y) = F(c,y) = c
            if part_b_filled_arr[c][cur_y] && part_falg[c][cur_y] != c {
                continue;
            }
            if !part_b_filled_arr[cur_x][c] {
                let p_idx = pairs_inv_map.get(&(cur_x, c)).expect("no inv index");
                let cand_set = cands_map.get(&p_idx).expect("no cands entry");
                if !cand_set.contains(&c) {
                    continue;
                }
            }
            if !part_b_filled_arr[c][cur_y] {
                let p_idx = pairs_inv_map.get(&(c, cur_y)).expect("no inv index");
                let cand_set = cands_map.get(&p_idx).expect("no cands entry");
                if !cand_set.contains(&c) {
                    continue;
                }
            }
            // F5: F(y, x) = y =>  F(y, F(x,y)) = y
            if part_b_filled_arr[cur_y][cur_x] && part_falg[cur_y][cur_x] == cur_y {
                if part_b_filled_arr[cur_y][c] && part_falg[cur_y][c] != cur_y {
                    continue;
                }
                if !part_b_filled_arr[cur_y][c] {
                    let p_idx = pairs_inv_map.get(&(cur_y, c)).expect("no inv index");
                    let cand_set = cands_map.get(&p_idx).expect("no cands entry");
                    if !cand_set.contains(&cur_y) {
                        continue;
                    }

                }
            }
            // F6: F(y, x) = x =>  F( F(x,y), x) = x
            if part_b_filled_arr[cur_y][cur_x] && part_falg[cur_y][cur_x] == cur_x {
                if part_b_filled_arr[c][cur_x] && part_falg[c][cur_x] != cur_x {
                    continue;
                }
                if !part_b_filled_arr[c][cur_x] {
                    let p_idx = pairs_inv_map.get(&(c, cur_x)).expect("no inv index");
                    let cand_set = cands_map.get(&p_idx).expect("no cands entry");
                    if !cand_set.contains(&cur_x) {
                        continue;
                    }
                }
            }
            // F5_2: t <=_1 x ==> F(t,y) <=_1 F(x,y) = c
            // F5_2: x <=_1 t ==> c = F(x,y) <=_1 F(t,y)
            // TODO

            // F6_1: t <=_2 y ==> F(x,t) <=_2 F(x,y) = c
            // F6_2: y <=_2 t ==> c = F(x,y) <=_2 F(x,t)
            // TODO
            part_falg[cur_x][cur_y] = c;
            part_b_filled_arr[cur_x][cur_y] = true;
            falg_fill_missing_v1(cur_idx + 1, key_arr, cands_map, pairs_map, pairs_inv_map, part_falg, part_b_filled_arr);
            part_falg[cur_x][cur_y] = 0;
            part_b_filled_arr[cur_x][cur_y] = false;
        }
    }

}


pub fn falg_fill_missing_v2(cur_idx:usize, key_arr: &Vec<usize>, cands_map: &HashMap<usize, HashSet<usize>>, pairs_map: &HashMap<usize, (usize, usize)>, pairs_inv_map: &HashMap<(usize, usize), usize>, part_falg: &mut Vec<Vec<usize>>, part_b_filled_arr: &mut Vec<Vec<bool>>) {
    if cur_idx == cands_map.len() {
        // test conditions for falg
        if falg_all_tests_no_print(part_falg) {
            println!("{:?}", part_falg);
        }
    }
    else {
        let key_idx = key_arr[cur_idx];
        let cur_cands = cands_map.get(&key_idx).unwrap();
        let (cur_x, cur_y) = *pairs_map.get(&key_idx).unwrap();
        if !part_b_filled_arr[cur_x][cur_y] {
            for &c in cur_cands {
                let mut to_fill_map = HashMap::<(usize,usize),usize>::new();
                // c = F(x,y)
                // F1: F(x, F(x,c)) = F(x,c) = c
                if part_b_filled_arr[cur_x][c] && part_falg[cur_x][c] != c {
                    continue;
                }
                // F2: F(F(c,y),y) = F(c,y) = c
                if part_b_filled_arr[c][cur_y] && part_falg[c][cur_y] != c {
                    continue;
                }
                if !part_b_filled_arr[cur_x][c] {
                    let p_idx = pairs_inv_map.get(&(cur_x, c)).expect("no inv index");
                    let cand_set = cands_map.get(&p_idx).expect("no cands entry");
                    if !cand_set.contains(&c) {
                        continue;
                    }
                    else {
                        to_fill_map.insert((cur_x, c), c);
                    }
                }
                if !part_b_filled_arr[c][cur_y] {
                    let p_idx = pairs_inv_map.get(&(c, cur_y)).expect("no inv index");
                    let cand_set = cands_map.get(&p_idx).expect("no cands entry");
                    if !cand_set.contains(&c) {
                        continue;
                    }
                    else {
                        to_fill_map.insert((c, cur_y), c);
                    }
                }
                // F5: F(y, x) = y =>  F(y, F(x,y)) = y
                if part_b_filled_arr[cur_y][cur_x] && part_falg[cur_y][cur_x] == cur_y {
                    if part_b_filled_arr[cur_y][c] && part_falg[cur_y][c] != cur_y {
                        continue;
                    }
                    if !part_b_filled_arr[cur_y][c] {
                        let p_idx = pairs_inv_map.get(&(cur_y, c)).expect("no inv index");
                        let cand_set = cands_map.get(&p_idx).expect("no cands entry");
                        if !cand_set.contains(&cur_y) {
                            continue;
                        }
                        else {
                            to_fill_map.insert((cur_y, c), cur_y);
                        }
                    }
                }
                // F6: F(y, x) = x =>  F( F(x,y), x) = x
                if part_b_filled_arr[cur_y][cur_x] && part_falg[cur_y][cur_x] == cur_x {
                    if part_b_filled_arr[c][cur_x] && part_falg[c][cur_x] != cur_x {
                        continue;
                    }
                    if !part_b_filled_arr[c][cur_x] {
                        let p_idx = pairs_inv_map.get(&(c, cur_x)).expect("no inv index");
                        let cand_set = cands_map.get(&p_idx).expect("no cands entry");
                        if !cand_set.contains(&cur_x) {
                            continue;
                        }
                        else {
                            to_fill_map.insert((c, cur_x), cur_x);
                        }
                    }
                }
                // F5_2: t <=_1 x ==> F(t,y) <=_1 F(x,y) = c
                // F5_2: x <=_1 t ==> c = F(x,y) <=_1 F(t,y)
                // TODO

                // F6_1: t <=_2 y ==> F(x,t) <=_2 F(x,y) = c
                // F6_2: y <=_2 t ==> c = F(x,y) <=_2 F(x,t)
                // TODO
                part_falg[cur_x][cur_y] = c;
                part_b_filled_arr[cur_x][cur_y] = true;
                let mut b_error = false;
                for (&k,&v) in to_fill_map.iter() {
                    if !part_b_filled_arr[k.0][k.1] {
                        part_falg[k.0][k.1] = v;
                        part_b_filled_arr[k.0][k.1] = true;
                    }
                    else {
                        if part_falg[k.0][k.1] != v {
                            b_error = true;
                            break;
                        }

                    }
                }
                if b_error {
                    continue; 
                }
                falg_fill_missing_v2(cur_idx + 1, key_arr, cands_map, pairs_map, pairs_inv_map, part_falg, part_b_filled_arr);
                part_falg[cur_x][cur_y] = 0;
                part_b_filled_arr[cur_x][cur_y] = false;
                for (k,v) in to_fill_map {
                    if part_b_filled_arr[k.0][k.1] {
                        part_falg[k.0][k.1] = 0;
                        part_b_filled_arr[k.0][k.1] = false;
                    }
                }
            }
        }
        else {
            falg_fill_missing_v2(cur_idx + 1, key_arr, cands_map, pairs_map, pairs_inv_map, part_falg, part_b_filled_arr);
        }
    }

}


pub fn falg_fill_missing_v3(cur_idx:usize, key_arr: &Vec<usize>, cands_map: &HashMap<usize, HashSet<usize>>, pairs_map: &HashMap<usize, (usize, usize)>, pairs_inv_map: &HashMap<(usize, usize), usize>, qord1: &Vec<Vec<usize>>, qord2: &Vec<Vec<usize>>, part_falg: &mut Vec<Vec<usize>>, part_b_filled_arr: &mut Vec<Vec<bool>>) {
    if cur_idx == cands_map.len() {
        // test conditions for falg
        if falg_all_tests_no_print(part_falg) {
            println!("{:?}", part_falg);
        }
    }
    else {
        let key_idx = key_arr[cur_idx];
        let cur_cands = cands_map.get(&key_idx).unwrap();
        let (cur_x, cur_y) = *pairs_map.get(&key_idx).unwrap();
        if !part_b_filled_arr[cur_x][cur_y] {
            for &c in cur_cands {
                let mut to_fill_map = HashMap::<(usize,usize),usize>::new();
                // c = F(x,y)
                // F1: F(x, F(x,c)) = F(x,c) = c
                if part_b_filled_arr[cur_x][c] && part_falg[cur_x][c] != c {
                    continue;
                }
                // F2: F(F(c,y),y) = F(c,y) = c
                if part_b_filled_arr[c][cur_y] && part_falg[c][cur_y] != c {
                    continue;
                }
                if !part_b_filled_arr[cur_x][c] {
                    let p_idx = pairs_inv_map.get(&(cur_x, c)).expect("no inv index");
                    let cand_set = cands_map.get(&p_idx).expect("no cands entry");
                    if !cand_set.contains(&c) {
                        continue;
                    }
                    else {
                        to_fill_map.insert((cur_x, c), c);
                    }
                }
                if !part_b_filled_arr[c][cur_y] {
                    let p_idx = pairs_inv_map.get(&(c, cur_y)).expect("no inv index");
                    let cand_set = cands_map.get(&p_idx).expect("no cands entry");
                    if !cand_set.contains(&c) {
                        continue;
                    }
                    else {
                        to_fill_map.insert((c, cur_y), c);
                    }
                }
                // F5: F(y, x) = y =>  F(y, F(x,y)) = y
                if part_b_filled_arr[cur_y][cur_x] && part_falg[cur_y][cur_x] == cur_y {
                    if part_b_filled_arr[cur_y][c] && part_falg[cur_y][c] != cur_y {
                        continue;
                    }
                    if !part_b_filled_arr[cur_y][c] {
                        let p_idx = pairs_inv_map.get(&(cur_y, c)).expect("no inv index");
                        let cand_set = cands_map.get(&p_idx).expect("no cands entry");
                        if !cand_set.contains(&cur_y) {
                            continue;
                        }
                        else {
                            to_fill_map.insert((cur_y, c), cur_y);
                        }
                    }
                }
                // F6: F(y, x) = x =>  F( F(x,y), x) = x
                if part_b_filled_arr[cur_y][cur_x] && part_falg[cur_y][cur_x] == cur_x {
                    if part_b_filled_arr[c][cur_x] && part_falg[c][cur_x] != cur_x {
                        continue;
                    }
                    if !part_b_filled_arr[c][cur_x] {
                        let p_idx = pairs_inv_map.get(&(c, cur_x)).expect("no inv index");
                        let cand_set = cands_map.get(&p_idx).expect("no cands entry");
                        if !cand_set.contains(&cur_x) {
                            continue;
                        }
                        else {
                            to_fill_map.insert((c, cur_x), cur_x);
                        }
                    }
                }
                // F5_2: t <=_1 x ==> F(t,y) <=_1 F(x,y) = c
                // F5_2: x <=_1 t ==> c = F(x,y) <=_1 F(t,y)
                let falg_size = qord1.len();
                let mut b_problem = false;
                for t in 0..falg_size {
                    if t != cur_x {
                        if qord1[t][cur_x] == 1 {
                            if part_b_filled_arr[t][cur_y] && qord1[part_falg[t][cur_y]][c]==0 {
                                b_problem = true;
                                break;
                            }
                        
                            if !part_b_filled_arr[t][cur_y] {
                                let p_idx = pairs_inv_map.get(&(t, cur_y)).expect("no inv index");
                                let cand_set = cands_map.get(&p_idx).expect("no cands entry");
                                let mut b_found = false;
                                for s in cand_set {
                                    if qord1[*s][c] == 1 {
                                        b_found = true;
                                        break;
                                    }
                                }
                                if !b_found {
                                    b_problem = true;
                                    break;
                                }
                            }
                        }

                        if qord1[cur_x][t] == 1 {
                            if part_b_filled_arr[t][cur_y] && qord1[c][part_falg[t][cur_y]]==0 {
                                b_problem = true;
                                break;
                            }
                        
                            if !part_b_filled_arr[t][cur_y] {
                                let p_idx = pairs_inv_map.get(&(t, cur_y)).expect("no inv index");
                                let cand_set = cands_map.get(&p_idx).expect("no cands entry");
                                let mut b_found = false;
                                for s in cand_set {
                                    if qord1[c][*s] == 1 {
                                        b_found = true;
                                        break;
                                    }
                                }
                                if !b_found {
                                    b_problem = true;
                                    break;
                                }
                            }
                        }
                    }

                }
                
                if b_problem {
                    continue;
                }

                // F6_1: t <=_2 y ==> F(x,t) <=_2 F(x,y) = c
                // F6_2: y <=_2 t ==> c = F(x,y) <=_2 F(x,t)
                let mut b_problem = false;
                for t in 0..falg_size {
                    if t != cur_x {
                        if qord2[t][cur_y] == 1 {
                            if part_b_filled_arr[cur_x][t] && qord2[part_falg[cur_x][t]][c]==0 {
                                b_problem = true;
                                break;
                            }
                        
                            if !part_b_filled_arr[cur_x][t] {
                                let p_idx = pairs_inv_map.get(&(cur_x, t)).expect("no inv index");
                                let cand_set = cands_map.get(&p_idx).expect("no cands entry");
                                let mut b_found = false;
                                for s in cand_set {
                                    if qord2[*s][c] == 1 {
                                        b_found = true;
                                        break;
                                    }
                                }
                                if !b_found {
                                    b_problem = true;
                                    break;
                                }
                            }
                        }

                        if qord2[cur_y][t] == 1 {
                            if part_b_filled_arr[cur_x][t] && qord2[c][part_falg[cur_x][t]]==0 {
                                b_problem = true;
                                break;
                            }
                        
                            if !part_b_filled_arr[cur_x][t] {
                                let p_idx = pairs_inv_map.get(&(cur_x, t)).expect("no inv index");
                                let cand_set = cands_map.get(&p_idx).expect("no cands entry");
                                let mut b_found = false;
                                for s in cand_set {
                                    if qord2[c][*s] == 1 {
                                        b_found = true;
                                        break;
                                    }
                                }
                                if !b_found {
                                    b_problem = true;
                                    break;
                                }
                            }
                        }
                    }

                }
                
                if b_problem {
                    continue;
                }
                


                part_falg[cur_x][cur_y] = c;
                part_b_filled_arr[cur_x][cur_y] = true;
                let mut b_error = false;
                for (&k,&v) in to_fill_map.iter() {
                    if !part_b_filled_arr[k.0][k.1] {
                        part_falg[k.0][k.1] = v;
                        part_b_filled_arr[k.0][k.1] = true;
                    }
                    else {
                        if part_falg[k.0][k.1] != v {
                            b_error = true;
                            break;
                        }

                    }
                }
                if b_error {
                    continue; 
                }
                falg_fill_missing_v3(cur_idx + 1, key_arr, cands_map, pairs_map, pairs_inv_map, qord1, qord2, part_falg, part_b_filled_arr);
                part_falg[cur_x][cur_y] = 0;
                part_b_filled_arr[cur_x][cur_y] = false;
                for (k,v) in to_fill_map {
                    if part_b_filled_arr[k.0][k.1] {
                        part_falg[k.0][k.1] = 0;
                        part_b_filled_arr[k.0][k.1] = false;
                    }
                }
            }
        }
        else {
            falg_fill_missing_v3(cur_idx + 1, key_arr, cands_map, pairs_map, pairs_inv_map, qord1, qord2, part_falg, part_b_filled_arr);
        }
    }

}

pub fn falg_fill_missing_v3_writer(out_writer: &mut &std::fs::File, cur_idx:usize, key_arr: &Vec<usize>, cands_map: &HashMap<usize, HashSet<usize>>, pairs_map: &HashMap<usize, (usize, usize)>, pairs_inv_map: &HashMap<(usize, usize), usize>, qord1: &Vec<Vec<usize>>, qord2: &Vec<Vec<usize>>, part_falg: &mut Vec<Vec<usize>>, part_b_filled_arr: &mut Vec<Vec<bool>>) {
    if cur_idx == cands_map.len() {
        // test conditions for falg
        if falg_all_tests_no_print(part_falg) {
            writeln!(out_writer, "{:?}", part_falg).unwrap();
            //println!("{:?}", part_falg);
        }
    }
    else {
        let key_idx = key_arr[cur_idx];
        let cur_cands = cands_map.get(&key_idx).unwrap();
        let (cur_x, cur_y) = *pairs_map.get(&key_idx).unwrap();
        if !part_b_filled_arr[cur_x][cur_y] {
            for &c in cur_cands {
                let mut to_fill_map = HashMap::<(usize,usize),usize>::new();
                // c = F(x,y)
                // F1: F(x, F(x,c)) = F(x,c) = c
                if part_b_filled_arr[cur_x][c] && part_falg[cur_x][c] != c {
                    continue;
                }
                // F2: F(F(c,y),y) = F(c,y) = c
                if part_b_filled_arr[c][cur_y] && part_falg[c][cur_y] != c {
                    continue;
                }
                if !part_b_filled_arr[cur_x][c] {
                    let p_idx = pairs_inv_map.get(&(cur_x, c)).expect("no inv index");
                    let cand_set = cands_map.get(&p_idx).expect("no cands entry");
                    if !cand_set.contains(&c) {
                        continue;
                    }
                    else {
                        to_fill_map.insert((cur_x, c), c);
                    }
                }
                if !part_b_filled_arr[c][cur_y] {
                    let p_idx = pairs_inv_map.get(&(c, cur_y)).expect("no inv index");
                    let cand_set = cands_map.get(&p_idx).expect("no cands entry");
                    if !cand_set.contains(&c) {
                        continue;
                    }
                    else {
                        to_fill_map.insert((c, cur_y), c);
                    }
                }
                // F5: F(y, x) = y =>  F(y, F(x,y)) = y
                if part_b_filled_arr[cur_y][cur_x] && part_falg[cur_y][cur_x] == cur_y {
                    if part_b_filled_arr[cur_y][c] && part_falg[cur_y][c] != cur_y {
                        continue;
                    }
                    if !part_b_filled_arr[cur_y][c] {
                        let p_idx = pairs_inv_map.get(&(cur_y, c)).expect("no inv index");
                        let cand_set = cands_map.get(&p_idx).expect("no cands entry");
                        if !cand_set.contains(&cur_y) {
                            continue;
                        }
                        else {
                            to_fill_map.insert((cur_y, c), cur_y);
                        }
                    }
                }
                // F6: F(y, x) = x =>  F( F(x,y), x) = x
                if part_b_filled_arr[cur_y][cur_x] && part_falg[cur_y][cur_x] == cur_x {
                    if part_b_filled_arr[c][cur_x] && part_falg[c][cur_x] != cur_x {
                        continue;
                    }
                    if !part_b_filled_arr[c][cur_x] {
                        let p_idx = pairs_inv_map.get(&(c, cur_x)).expect("no inv index");
                        let cand_set = cands_map.get(&p_idx).expect("no cands entry");
                        if !cand_set.contains(&cur_x) {
                            continue;
                        }
                        else {
                            to_fill_map.insert((c, cur_x), cur_x);
                        }
                    }
                }
                // F5_2: t <=_1 x ==> F(t,y) <=_1 F(x,y) = c
                // F5_2: x <=_1 t ==> c = F(x,y) <=_1 F(t,y)
                let falg_size = qord1.len();
                let mut b_problem = false;
                for t in 0..falg_size {
                    if t != cur_x {
                        if qord1[t][cur_x] == 1 {
                            if part_b_filled_arr[t][cur_y] && qord1[part_falg[t][cur_y]][c]==0 {
                                b_problem = true;
                                break;
                            }
                        
                            if !part_b_filled_arr[t][cur_y] {
                                let p_idx = pairs_inv_map.get(&(t, cur_y)).expect("no inv index");
                                let cand_set = cands_map.get(&p_idx).expect("no cands entry");
                                let mut b_found = false;
                                for s in cand_set {
                                    if qord1[*s][c] == 1 {
                                        b_found = true;
                                        break;
                                    }
                                }
                                if !b_found {
                                    b_problem = true;
                                    break;
                                }
                            }
                        }

                        if qord1[cur_x][t] == 1 {
                            if part_b_filled_arr[t][cur_y] && qord1[c][part_falg[t][cur_y]]==0 {
                                b_problem = true;
                                break;
                            }
                        
                            if !part_b_filled_arr[t][cur_y] {
                                let p_idx = pairs_inv_map.get(&(t, cur_y)).expect("no inv index");
                                let cand_set = cands_map.get(&p_idx).expect("no cands entry");
                                let mut b_found = false;
                                for s in cand_set {
                                    if qord1[c][*s] == 1 {
                                        b_found = true;
                                        break;
                                    }
                                }
                                if !b_found {
                                    b_problem = true;
                                    break;
                                }
                            }
                        }
                    }

                }
                
                if b_problem {
                    continue;
                }

                // F6_1: t <=_2 y ==> F(x,t) <=_2 F(x,y) = c
                // F6_2: y <=_2 t ==> c = F(x,y) <=_2 F(x,t)
                let mut b_problem = false;
                for t in 0..falg_size {
                    if t != cur_x {
                        if qord2[t][cur_y] == 1 {
                            if part_b_filled_arr[cur_x][t] && qord2[part_falg[cur_x][t]][c]==0 {
                                b_problem = true;
                                break;
                            }
                        
                            if !part_b_filled_arr[cur_x][t] {
                                let p_idx = pairs_inv_map.get(&(cur_x, t)).expect("no inv index");
                                let cand_set = cands_map.get(&p_idx).expect("no cands entry");
                                let mut b_found = false;
                                for s in cand_set {
                                    if qord2[*s][c] == 1 {
                                        b_found = true;
                                        break;
                                    }
                                }
                                if !b_found {
                                    b_problem = true;
                                    break;
                                }
                            }
                        }

                        if qord2[cur_y][t] == 1 {
                            if part_b_filled_arr[cur_x][t] && qord2[c][part_falg[cur_x][t]]==0 {
                                b_problem = true;
                                break;
                            }
                        
                            if !part_b_filled_arr[cur_x][t] {
                                let p_idx = pairs_inv_map.get(&(cur_x, t)).expect("no inv index");
                                let cand_set = cands_map.get(&p_idx).expect("no cands entry");
                                let mut b_found = false;
                                for s in cand_set {
                                    if qord2[c][*s] == 1 {
                                        b_found = true;
                                        break;
                                    }
                                }
                                if !b_found {
                                    b_problem = true;
                                    break;
                                }
                            }
                        }
                    }

                }
                
                if b_problem {
                    continue;
                }
                


                part_falg[cur_x][cur_y] = c;
                part_b_filled_arr[cur_x][cur_y] = true;
                let mut b_error = false;
                for (&k,&v) in to_fill_map.iter() {
                    if !part_b_filled_arr[k.0][k.1] {
                        part_falg[k.0][k.1] = v;
                        part_b_filled_arr[k.0][k.1] = true;
                    }
                    else {
                        if part_falg[k.0][k.1] != v {
                            b_error = true;
                            break;
                        }

                    }
                }
                if b_error {
                    continue; 
                }
                falg_fill_missing_v3_writer(out_writer, cur_idx + 1, key_arr, cands_map, pairs_map, pairs_inv_map, qord1, qord2, part_falg, part_b_filled_arr);
                part_falg[cur_x][cur_y] = 0;
                part_b_filled_arr[cur_x][cur_y] = false;
                for (k,v) in to_fill_map {
                    if part_b_filled_arr[k.0][k.1] {
                        part_falg[k.0][k.1] = 0;
                        part_b_filled_arr[k.0][k.1] = false;
                    }
                }
            }
        }
        else {
            falg_fill_missing_v3_writer(out_writer, cur_idx + 1, key_arr, cands_map, pairs_map, pairs_inv_map, qord1, qord2, part_falg, part_b_filled_arr);
        }
    }

}




//             # F5_2: t <=_1 x ==> F(t,y) <=_1 F(x,y) = c
//             # F5_2: x <=_1 t ==> c = F(x,y) <=_1 F(t,y)
//             b_problem = False
//             n = len(qord1)
//             for t in range(n):
//                 if t != x:
//                     if qord1[t][x] == 1:
//                         if b_arr[t][y] and qord1[AA[t][y]][c] == 0:
//                             b_problem = True
//                             break
//                         if not b_arr[t][y]: 
//                             b_found = False
//                             for s in cands[get_inv_key(n, t, y)]:
//                                 if qord1[s][c] == 1:
//                                     b_found = True
//                                     break
//                             if not b_found:
//                                 b_problem = True
//                                 break
//                     if qord1[x][t] == 1:
//                         if b_arr[t][y] and qord1[c][AA[t][y]] == 0:
//                             b_problem = True
//                             break
//                         if not b_arr[t][y]: 
//                             b_found = False
//                             for s in cands[get_inv_key(n, t, y)]:
//                                 if qord1[c][s] == 1:
//                                     b_found = True
//                                     break
//                             if not b_found:
//                                 b_problem = True
//                                 break




// def fill_missing_rec4(cur_idx, cands, key_map, AA, b_arr, qord1, qord2, res_AAs, res_msgs, debug_print = False, strcallback=None, *args):
//     global g_tested_filled, g_success
//     global g_ts
//     global g_te
    
//     #print("HERE", file=sys.stderr)
//     if cur_idx >= len(cands):
//         g_tested_filled += 1
//         if g_tested_filled % 1_000_000 == 0:
//             g_te = time.perf_counter()
//             print("State: (", end="",file=sys.stderr)
//             b_first=True
//             for k in cands.keys():
//                 if not b_first:
//                     print(", ", end="", file=sys.stderr)
//                 else:
//                     b_first = False
//                 print(AA[ key_map[k][0] ][key_map[k][1]], end="", file=sys.stderr)
//             print(")", file=sys.stderr)
//             print("Time: {} s".format(g_te - g_ts), file=sys.stderr)
//             g_ts = g_te

//         if just_test(AA):
//         #b1 = test_F1(AA, True)
//         #b2 = test_F2(AA, True)
//         #b3 = test_F3(AA, True)
//         #b4 = test_F4(AA, True)
//             g_success += 1
//             msg = ""
//             if strcallback:
//                 msg = strcallback(*args)

//             print(AA, '#', msg, flush=True, file=sys.stderr)
//             res_AAs.append(AA)
//             res_msgs.append(msg)
//         #exit()
//     else:
//         #print("DEBUG: {}/{}".format(cur_idx, len(cands)), file=sys.stderr)
//         cur_key = list(cands.keys())[cur_idx]
//         x = key_map[cur_key][0]
//         y = key_map[cur_key][1]
//         n = len(AA)
//         b_arr[x][y] = True
//         for c in cands[cur_key]:
//             #if cur_idx == 0:
//             #    print(c, file=sys.stderr)
//             AA[x][y] = c
//             # test forced rules
//             # F1: F(x, F(x,c)) = F(x,c)
//             if b_arr[x][c] and AA[x][c] != c:
//                 continue
//             # F2: F(F(c,y),y) = F(c,y)
//             if b_arr[c][y] and AA[c][y] != c:
//                 continue
//             if not b_arr[x][c]:
//                 #print(get_inv_key(n, x, c))
//                 #print("x = {}, c= {}".format(x, c))
//                 #print_partial(AA, b_arr)
//                 if c not in cands[get_inv_key(n, x, c)]:
//                     continue
//             if not b_arr[c][y]:
//                 #print(get_inv_key(n, c, y))
//                 #print("c = {}, y= {}".format(c, y))
//                 #print_partial(AA, b_arr)
//                 if c not in cands[get_inv_key(n, c, y)]:
//                     continue
//             # F5: F[y][x] == y and F(y, F(x,y)) != y
//             if b_arr[y][x] and AA[y][x] == y:
//                 if b_arr[y][AA[x][y]] and AA[y][AA[x][y]] != y:
//                     #print("F5HERE", file=sys.stderr)
//                     continue
//                 # AA[x][y] = c
//                 if not b_arr[y][AA[x][y]] and y not in cands[get_inv_key(n, y, c)]:
//                     #print("F5-2HERE", file=sys.stderr)
//                     continue
//             # F6: F[y][x] == x and F(F(x,y), x) != x
//             if b_arr[y][x] and AA[y][x] == x:
//                 if b_arr[AA[x][y]][x] and AA[AA[x][y]][x] != x:
//                     #print("F6HERE", file=sys.stderr)
//                     continue
//                 # AA[x][y] = c
//                 if not b_arr[AA[x][y]][x] and x not in cands[get_inv_key(n, c, x)]:
//                     #print("F6-2HERE", file=sys.stderr)
//                     continue

//             # F5_2: t <=_1 x ==> F(t,y) <=_1 F(x,y) = c
//             # F5_2: x <=_1 t ==> c = F(x,y) <=_1 F(t,y)
//             b_problem = False
//             n = len(qord1)
//             for t in range(n):
//                 if t != x:
//                     if qord1[t][x] == 1:
//                         if b_arr[t][y] and qord1[AA[t][y]][c] == 0:
//                             b_problem = True
//                             break
//                         if not b_arr[t][y]: 
//                             b_found = False
//                             for s in cands[get_inv_key(n, t, y)]:
//                                 if qord1[s][c] == 1:
//                                     b_found = True
//                                     break
//                             if not b_found:
//                                 b_problem = True
//                                 break
//                     if qord1[x][t] == 1:
//                         if b_arr[t][y] and qord1[c][AA[t][y]] == 0:
//                             b_problem = True
//                             break
//                         if not b_arr[t][y]: 
//                             b_found = False
//                             for s in cands[get_inv_key(n, t, y)]:
//                                 if qord1[c][s] == 1:
//                                     b_found = True
//                                     break
//                             if not b_found:
//                                 b_problem = True
//                                 break

//             if b_problem:
//                 continue

//             # F6_1: t <=_2 y ==> F(x,t) <=_2 F(x,y) = c
//             # F5_2: y <=_2 t ==> c = F(x,y) <=_2 F(x,t)
//             b_problem = False            
//             for t in range(n):
//                 if t != x:
//                     if qord2[t][y] == 1:
//                         if b_arr[x][t] and qord2[AA[x][t]][c] == 0:
//                             b_problem = True
//                             break
//                         if not b_arr[x][t]: 
//                             b_found = False
//                             for s in cands[get_inv_key(n, x, t)]:
//                                 if qord2[s][c] == 1:
//                                     b_found = True
//                                     break
//                             if not b_found:
//                                 b_problem = True
//                                 break
//                     if qord2[y][t] == 1:
//                         if b_arr[x][t] and qord2[c][AA[x][t]] == 0:
//                             b_problem = True
//                             break
//                         if not b_arr[x][t]: 
//                             b_found = False
//                             for s in cands[get_inv_key(n, x, t)]:
//                                 if qord1[c][s] == 1:
//                                     b_found = True
//                                     break
//                             if not b_found:
//                                 b_problem = True
//                                 break

//             if b_problem:
//                 continue

//             #if test_part_F3(AA, b_arr) and test_part_F4(AA, b_arr) and \
//             #    test_part_F5(AA, b_arr) and test_part_F6(AA, b_arr):
//             fill_missing_rec4(cur_idx + 1, cands, key_map, AA, b_arr, qord1, qord2, res_AAs, res_msgs, debug_print, strcallback, *args)
//         b_arr[x][y] = False






//      idx = 0
//         for x in range(n):
//             for y in range(n):
//                 if x != y:
//                     if not b_arr[x][y]:
//                         #print("x = {}, y = {}".format(x,y))
//                         is_missing = True
//                         # get candidates
//                         candidates=set()
//                         for q in range(n):
//                             # F1: A[x][y] <=_2 x
//                             if rel2[q][x]:
//                                 if debug_print:
//                                     print("Adding candidate for ({}, {}) due F1: A[x][y] <=_2 x: {}".format(x,y,q), file=sys.stderr)
//                                 candidates.add(q)
//                             # F2: A[x][y] <=_1 y    
//                             if rel1[q][y]:
//                                 if debug_print:
//                                     print("Adding candidate for ({}, {}) due F2: A[x][y] <=_1 y: {}".format(x,y,q), file=sys.stderr)
//                                 candidates.add(q)
//                         # candidates = set(range(n))
//                         if rel1[x][y] == 0:
//                             if debug_print:
//                                 print("Removing candidate for ({}, {}) since x !<=_1 y ==> A[x][y] != x: {}".format(x,y,x), file=sys.stderr)
//                             candidates.remove(x)
//                         if rel2[y][x] == 0:
//                             if debug_print:
//                                 print("Removing candidate for ({}, {}) since y !<=_2 x ==> A[x][y] != y: {}".format(x,y,y), file=sys.stderr)
//                             candidates.remove(y)
//                         if len(candidates) == 0:
//                             if debug_print:
//                                 print("No suitable candidates for ({}, {}).".format(x,y), file=sys.stderr)
//                             can_coexist = False
//                             return False
//                         if can_coexist:
//                             cands[idx] = candidates
//                             key_map[idx] = (x,y)
//                             #print(idx, ": ", sep="", end="")
//                             #print(candidates)


//                     idx+= 1

// def generate_As_with_ords3(rel1, rel2, debug_print = False, callback=None, *args):
//     n = len(rel1)
//     res_AAs = []
//     res_msgs = []
//     #print(n)
//     A = initA(n)
//     #print(A)
//     can_coexist = True
//     b_arr = []
//     for x in range(n):
//         b_arr.append([])
//         for y in range(n):
//             if x == y:
//                 b_arr[x].append(True)
//             else:
//                 b_arr[x].append(False)
//     #print(b_arr)
//     #print("Rel1:", rel1)
//     #print("Rel2:", rel2)
//     for x in range(n):
//         for y in range(n):
//             if x != y:
//                 if rel1[x][y] == 1:
//                     #print("HH1")
//                     #b_arr[x][y] = True
//                     #A[x][y] = x
//                     #print("Part fill:", A)
//                     if b_arr[x][y] and A[x][y] != x:
//                         if debug_print:
//                             print("x <=_1 y, but A[x][y] != x: x = {}, y = {}".format(x,y), file=sys.stderr)
//                         can_coexist = False
//                         return False
//                     if not b_arr[x][y]:
//                         if debug_print:
//                             print("x <=_1 y ==> A[x][y] = x: x = {}, y = {}".format(x,y), file=sys.stderr)                        
//                         A[x][y] = x
//                         b_arr[x][y] = True

//                 if rel2[x][y] == 1:
//                     #print("HH2")
//                     #A[y][x] = x
//                     #b_arr[y][x] = True
//                     #print("Part fill:", A)
//                     if b_arr[y][x] and A[y][x] != x:
//                         if debug_print:
//                             print("x <=_2 y, but A[y][x] != x: x = {}, y = {}".format(x,y), file=sys.stderr)
//                         can_coexist = False
//                         return False
//                     if not b_arr[y][x]:
//                         if debug_print:
//                             print("x <=_2 y ==> A[y][x] = x: x = {}, y = {}".format(x,y), file=sys.stderr)                        
//                         A[y][x] = x
//                         b_arr[y][x] = True

//     for x in range(n):
//         for y in range(n):
//             if x != y:
//                 if b_arr[x][y] and b_arr[y][x]:
//                     if rel1[x][y] and not rel1[x][A[y][x]]:
//                         if debug_print:
//                             print("F5 failed: x <=_1 y, but x = A[x][x] !<=_1 A[y][x]: x = {}, y = {}".format(x,y), file=sys.stderr)
//                         can_coexist = False
//                         return False
//                     if rel2[y][x] and not rel2[y][A[y][x]]:
//                         if debug_print:
//                             print("F6 failed: x <=_2 y, but A[y][x] !<=_2 y = A[y][y]: x = {}, y = {}".format(x,y), file=sys.stderr)
//                         can_coexist = False
//                         return False
    
//     if debug_print:
//         print_partial(A, b_arr, sys.stderr)
//     cands = dict()
//     key_map = dict()
//     is_missing = False
//     if can_coexist:
//         #print(A)
//         #print("Missing indexes: ")
        
//         idx = 0
//         for x in range(n):
//             for y in range(n):
//                 if x != y:
//                     if not b_arr[x][y]:
//                         #print("x = {}, y = {}".format(x,y))
//                         is_missing = True
//                         # get candidates
//                         candidates=set()
//                         for q in range(n):
//                             # F1: A[x][y] <=_2 x
//                             if rel2[q][x]:
//                                 if debug_print:
//                                     print("Adding candidate for ({}, {}) due F1: A[x][y] <=_2 x: {}".format(x,y,q), file=sys.stderr)
//                                 candidates.add(q)
//                             # F2: A[x][y] <=_1 y    
//                             if rel1[q][y]:
//                                 if debug_print:
//                                     print("Adding candidate for ({}, {}) due F2: A[x][y] <=_1 y: {}".format(x,y,q), file=sys.stderr)
//                                 candidates.add(q)
//                         # candidates = set(range(n))
//                         if rel1[x][y] == 0:
//                             if debug_print:
//                                 print("Removing candidate for ({}, {}) since x !<=_1 y ==> A[x][y] != x: {}".format(x,y,x), file=sys.stderr)
//                             candidates.remove(x)
//                         if rel2[y][x] == 0:
//                             if debug_print:
//                                 print("Removing candidate for ({}, {}) since y !<=_2 x ==> A[x][y] != y: {}".format(x,y,y), file=sys.stderr)
//                             candidates.remove(y)
//                         if len(candidates) == 0:
//                             if debug_print:
//                                 print("No suitable candidates for ({}, {}).".format(x,y), file=sys.stderr)
//                             can_coexist = False
//                             return False
//                         if can_coexist:
//                             cands[idx] = candidates
//                             key_map[idx] = (x,y)
//                             #print(idx, ": ", sep="", end="")
//                             #print(candidates)


//                     idx+= 1
//         #print("--")
//         #for m in m_idx:
//         if can_coexist:
//             #print(can_coexist)
//             #print("A:", A)
//             AA = A.copy()
//             for i in range(n):
//                 AA[i] = A[i].copy()
//             # fill single candidates
//             keys_to_delete = []
//             for key,values in cands.items():
//                 if len(values) == 1:
//                     sg_val = values.pop()
//                     #del cands[key]
//                     keys_to_delete.append(key)
//                     xx = key_map[key][0]
//                     yy = key_map[key][1]
//                     if debug_print:
//                         print("Filling single value candidate for ({}, {}): {}".format(xx, yy, sg_val), file=sys.stderr)
//                     AA[xx][yy] = sg_val
//                     b_arr[xx][yy] = True
//             for k in keys_to_delete:
//                 del cands[k]
//             is_missing = not all(all(r) for r in b_arr)
//             if debug_print:
//                 print_partial(AA, b_arr, sys.stderr)
//             if is_missing:
//                 if test_part_F3(AA, b_arr) and test_part_F4(AA, b_arr) and\
//                     test_part_F5(AA, b_arr) and test_part_F6(AA, b_arr):
//                     if True:
//                         print("Candidates: ", cands, file=sys.stderr)
//                         if callback:
//                             msg = callback(*args)
//                             print(msg, file=sys.stderr)
//                     #print_partial(AA, b_arr)
//                     #print(rel1)
//                     #print(rel2)
//                     #return
//                     prodlist = []
//                     for k in cands.keys():
//                         prodlist.append(list(cands[k]))
//                     #print(prodlist)
                    
//                     ####
//                     if False:
//                         prod_count = 0
//                         ts = time.perf_counter()
//                         for q in itertools.product(*prodlist):
//                             prod_count +=1
//                             if prod_count % 1_000_000 == 0:
//                                 te = time.perf_counter()
//                                 print("State: {}".format(q), file=sys.stderr)
//                                 print("Time: {} s".format(te-ts), file=sys.stderr)
//                                 ts = te
//                             #print("q:", q)
//                             k_idx = 0
//                             for k in cands.keys():
//                                 AA[key_map[k][0]][key_map[k][1]] = q[k_idx]
//                                 k_idx+=1
//                             #print("AA:", AA)
//                             #cur_test(AA)
//                             if just_test(AA):
//                                 print(AA, flush=True)
//                             #print("--")
//                     else:
//                         global g_ts, g_tested_filled, g_success
//                         g_ts = time.perf_counter()
//                         l_ts = time.perf_counter()
//                         g_tested_filled = 0
//                         g_success = 0
//                         fill_missing_rec4(0, cands, key_map, AA, b_arr, rel1, rel2, res_AAs, res_msgs, debug_print, callback, *args)
//                         l_te = time.perf_counter()
//                         if True:
//                             print("Total tested: {}, Success: {}".format(g_tested_filled, g_success), file=sys.stderr)
//                             print("Total time: {}".format(l_te - l_ts), file=sys.stderr)
//             else:
//                 l_success = 0
//                 if just_test(AA):
//                     l_success +=1
//                     if callback:
//                         msg = callback(*args)
//                     print(AA, '#', msg, flush=True, file=sys.stderr)
//                     res_AAs.append(AA)
//                     res_msgs.append(msg)
//                 if True:
//                     if callback:
//                         msg = callback(*args)
//                         print(msg, file=sys.stderr)
//                     print("Immediately filled.", file=sys.stderr)
//                     print("Total tested: {}, Success: {}".format(1, l_success), file=sys.stderr)

//                 #cur_test(AA)
//                 #print("--")
//     #else:
//     # print("HERE: ", res_AAs, res_msgs)
//     return (res_AAs, res_msgs)

pub fn falg_find_min_repr(falg: &Vec<Vec<usize>>) -> Vec<Vec<usize>> {
    let n = falg.len();

    let mut perm:Vec<usize> = (0..n).collect();

    let mut b_first = true;
    let mut falg_min_repr = falg.clone();

    loop {
        if b_first {
            b_first = false;
        }
        else {
            let falg_iso = falg_isomorphic_image(falg, &perm);

            if rel_quasi_order_is_lesser_rel(&falg_iso, &falg_min_repr) {
                falg_min_repr = falg_iso;
            }
        }

        if !permlib::next_perm(&mut perm, n) {
            break;
        }
    }

    falg_min_repr
}

pub fn falg_is_min_repr(falg: &Vec<Vec<usize>>) -> bool {
    let n = falg.len();

    let mut perm:Vec<usize> = (0..n).collect();

    // let mut b_first = true;
    // let mut falg_min_repr = falg.clone();

    loop {
        // if b_first {
        //     b_first = false;
        // }
        // else {
        let falg_iso = falg_isomorphic_image(falg, &perm);

        if rel_quasi_order_is_lesser_rel(&falg_iso, falg) {
            return false;
        }
        // }

        if !permlib::next_perm(&mut perm, n) {
            break;
        }
    }

    true
}


pub fn falg_find_max_repr(falg: &Vec<Vec<usize>>) -> Vec<Vec<usize>> {
    let n = falg.len();

    let mut perm:Vec<usize> = (0..n).collect();

    let mut b_first = true;
    let mut falg_max_repr = falg.clone();

    loop {
        if b_first {
            b_first = false;
        }
        else {
            let falg_iso = falg_isomorphic_image(falg, &perm);

            if rel_quasi_order_is_greater_rel(&falg_iso, &falg_max_repr) {
                falg_max_repr = falg_iso;
            }
        }

        if !permlib::next_perm(&mut perm, n) {
            break;
        }
    }

    falg_max_repr
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn falg_init_test() {
        let res1 = falg_init(0);
        assert_eq!(res1, Vec::<Vec<usize>>::new());

        let res2 = falg_init(1);
        assert_eq!(res2, vec!(vec!(0)));

        let res3 = falg_init(2);
        assert_eq!(res3, vec!(vec!(0,0),vec!(0,1)));

    }

    #[test]
    fn falg_test1() {
        let falg = vec![vec![0usize, 0, 0, 0], vec![0, 1, 0, 0], vec![0, 0, 2, 0], vec![0, 1, 2, 3]];

        assert_eq!(falg_all_tests_no_print(&falg), false);

    }

    #[test]
    fn rel_stab_tst1() {
        let rel1 = vec![vec![1,0],vec![0,1usize]];
        let mut hs1 = HashSet::<Vec<usize>>::new();
        hs1.insert(vec![0,1]);
        hs1.insert(vec![1,0]);
        
        assert_eq!(rel_get_stabilizer_perms(&rel1), hs1);

        let rel2 = vec![vec![1,0,0], vec![0,1,0], vec![0,0,1usize]];
        let mut hs2 = HashSet::<Vec<usize>>::new();
        hs2.insert(vec![0,1,2]);
        hs2.insert(vec![0,2,1]);
        hs2.insert(vec![1,0,2]);
        hs2.insert(vec![1,2,0]);
        hs2.insert(vec![2,0,1]);
        hs2.insert(vec![2,1,0]);

        assert_eq!(rel_get_stabilizer_perms(&rel2), hs2);

        let rel3 = vec![vec![1,0,1], vec![0,1,1], vec![0,0,1usize]];
        let mut hs3 = HashSet::<Vec<usize>>::new();
        hs3.insert(vec![0,1,2]);
        hs3.insert(vec![1,0,2]);
        assert_eq!(rel_get_stabilizer_perms(&rel3), hs3);
    }

    #[test]
    fn test_rel_isomorphic_expand_vec() {
        let rel = vec![vec![1usize,1,1], vec![0,1,1], vec![0,0,1]];
        let aa1 = rel_isomorphic_expand_vec(&rel);
        let aa2 = rel_isomorphic_expand_vec(&rel);
        assert_eq!(aa1.0, aa2.0);
    }

    #[test]
    fn test_rel_isomorphic_expand_vec2() {
        let rel = vec![vec![1usize,1,1], vec![0,1,1], vec![0,0,1]];
        let aa1 = rel_isomorphic_expand_vec(&rel);
        assert_eq!(aa1.0.len(), 6);
        assert_eq!(aa1.0[0], vec![vec![1,1,1],vec![0,1,1],vec![0,0,1]]);
        assert_eq!(aa1.0[1], vec![vec![1,1,1],vec![0,1,0],vec![0,1,1]]);
        assert_eq!(aa1.0[2], vec![vec![1,0,1],vec![1,1,1],vec![0,0,1]]);
        assert_eq!(aa1.0[3], vec![vec![1,0,0],vec![1,1,1],vec![1,0,1]]);
        assert_eq!(aa1.0[4], vec![vec![1,1,0],vec![0,1,0],vec![1,1,1]]);
        assert_eq!(aa1.0[5], vec![vec![1,0,0],vec![1,1,0],vec![1,1,1]]);
    }


    #[test]
    fn test_rel_isomorphic_expand() {
        let rel = vec![vec![1usize,1,1], vec![0,1,1], vec![0,0,1]];
        let aa1 = rel_isomorphic_expand(&rel);
        let aa2 = rel_isomorphic_expand(&rel);
        println!("{:?} {:?}", aa1.0, aa2.0);
        assert_eq!(aa1.0, aa2.0);
    }

        #[test]
    fn test_rel_isomorphic_expand2() {
        // should fail
        let rel = vec![vec![1usize,1,1], vec![0,1,1], vec![0,0,1]];
        let aa1 = rel_isomorphic_expand(&rel);
        let bb1:Vec<Vec<Vec<usize>>> = aa1.0.into_iter().collect();
        
        assert_eq!(bb1.len(), 6);
        
        let cond = 
            (bb1[0] == vec![vec![1,1,1],vec![0,1,1],vec![0,0,1]]) &&
            (bb1[1] == vec![vec![1,1,1],vec![0,1,0],vec![0,1,1]]) &&
            (bb1[2] == vec![vec![1,0,1],vec![1,1,1],vec![0,0,1]]) &&
            (bb1[3] == vec![vec![1,0,0],vec![1,1,1],vec![1,0,1]]) &&
            (bb1[4] == vec![vec![1,1,0],vec![0,1,0],vec![1,1,1]]) &&
            (bb1[5] == vec![vec![1,0,0],vec![1,1,0],vec![1,1,1]]);
        assert_eq!(cond, false);
    }
    
    #[test]
    fn test_cov_rel_get_class_coords_perm() {
        let cov_rel = vec![vec![0,0,1,0,0,0,0],vec![0,0,0,1,1,0,0],vec![0,0,0,1,0,0,0],vec![0,0,0,0,0,1,0],vec![0,0,0,0,0,1,0],vec![0,0,0,0,0,0,1],vec![0,0,0,0,0,0,0]];

        let coord1 = cov_rel_get_class_coords(&cov_rel);

        assert_eq!(coord1, vec![(0,0), (1,0), (0,1), (0,2), (1,1), (0,3),(0,4)]);

        let coord2 = cov_rel_get_class_coords_perm(&cov_rel,&vec![0,1,2,3,4,5,6]);
        assert_eq!(coord1, coord2);
        let coord3 = cov_rel_get_class_coords_perm(&cov_rel,&vec![2,1,0,3,4,5,6]);
        assert_eq!(coord3, vec![(1,0), (0,0), (0,1), (0,2), (1,1), (0,3), (0,4)]);
    }
}
