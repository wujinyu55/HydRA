
pub mod distributed_ecdsa;
pub mod interpolation;
pub mod triple;

use ark_bls12_381::{Bls12_381, Fr, G1Affine, G1Projective};
use ark_ec::{pairing::Pairing,  CurveGroup, PrimeGroup};
use ark_ff::{Field,  UniformRand, Zero};
use ark_poly::{
    univariate::DensePolynomial
};
use ark_std::rand::{ RngCore};
use sha2::{Digest, Sha256,};

use num_bigint::BigUint;
type Poly = DensePolynomial<Fr>;
type GT = <Bls12_381 as Pairing>::TargetField;

use distributed_ecdsa::{Commitment, Share, Srs, Witness, commit, create_witness, open, poly_from_coeffs, setup, verify_aggregated};
use interpolation::{ith_lagrange_coefficient};
use triple::{AdditiveShares, BeaverTripleShares, beaver_multiply_n_n, gen_beaver_triple_n_n, share_secret_n_n};
use std::time::{Duration, Instant};

use rayon::{prelude::*};
use rand::{RngExt, SeedableRng};
use rand::rngs::StdRng;

pub fn dqea_setup<R: RngCore>(thresh_num: usize, rng: &mut R) -> Srs {
    setup(thresh_num, rng).unwrap()
}

pub fn dqea_thresshare_one_phase(
    total_num: usize,
    thres_num: usize,
    srs: Srs,
    rho: Fr,
) -> (
    Vec<Fr>,
    Vec<Commitment>,
    Vec<G1Projective>,
    Vec<DensePolynomial<Fr>>,
) {
    let vecs: Vec<_> = (0..total_num)
        .into_par_iter()
        .enumerate()
        .map(|(idx, _)| {
            let mut rng = StdRng::seed_from_u64(idx as u64);

            let coeffs: Vec<_> = (0..=thres_num)
                .map(|_| rng.random_range(10011..255451))
                .collect();

            poly_from_coeffs(&coeffs)
        })
        .collect();

    let x_i_vector = vecs.par_iter().map(|vec| vec[0]).collect::<Vec<_>>();

    let comm_i_vector = vecs
        .par_iter()
        .map(|poly| commit(&srs, poly).unwrap())
        .collect::<Vec<_>>();

    let y_i_vector = vecs
        .par_iter()
        .map(|x| G1Projective::generator() * x[0])
        .collect::<Vec<_>>();

    let results: Vec<_> = (0..total_num)
        .into_par_iter()
        .map(|j| {
            let value = open(&vecs[1], Fr::from(j as u32));
            let fy_small_val = G1Projective::generator() * value.0;

            let w_val = create_witness(&srs, &vecs[1], 2, Fr::from(j as u32), rho).unwrap();

            (value.clone(), fy_small_val, w_val)
        })
        .collect();

    let (mut fy_big, mut fy_small, mut w) = (Vec::new(), Vec::new(), Vec::new());

    for (value, fy_small_val, w_val) in results {
        fy_big.push(value);
        fy_small.push(fy_small_val);
        w.push(w_val);
    }

    (x_i_vector, comm_i_vector, y_i_vector, vecs)
}

pub fn dqea_thresshare_two_phase(
    x_i_vector: Vec<Fr>,
    comm_i_vector: Vec<Commitment>,
    y_i_vector: Vec<G1Projective>,
    srs: Srs,
    rho: Fr,
    vecs: Vec<DensePolynomial<Fr>>,
    shares: Vec<Share>,
    witnesses: Vec<Witness>,
    total_num: usize,
) -> (Vec<Fr>, G1Projective) {
    let mut u = Fr::zero();

    let vk: G1Projective = y_i_vector.iter().sum();

    let ok = verify_aggregated(
        &srs,
        &comm_i_vector,
        &shares,
        &witnesses,
        Fr::from(2),
        rho,
    )
    .unwrap();

    assert_eq!(ok, true);

    let u_i_small_vector: Vec<Fr> = (0..total_num)
        .into_par_iter()
        .map(|value| {
            let x: Fr = vecs
                .par_iter()
                .map(|p| open(p, Fr::from(value as i32)).0)
                .sum();

            x
        })
        .collect();

    let u_i_big_vector = u_i_small_vector
        .par_iter()
        .map(|x| G1Projective::generator() * x)
        .collect::<Vec<_>>();

    let pi_i_vector = (0..total_num)
        .into_par_iter()
        .map(|index| {
            get_nizk_proof(
                y_i_vector[index],
                u_i_big_vector[index],
                x_i_vector[index],
                u_i_small_vector[index],
                index,
                total_num,
            )
        })
        .collect::<Vec<_>>();

    for index in 0..total_num {
        verify_nizk_proof(
            y_i_vector[index],
            u_i_big_vector[index],
            index,
            pi_i_vector[index],
            total_num,
        );
    }

    (u_i_small_vector, vk)
}

pub fn verify_nizk_proof(
    y_i_vector: G1Projective,
    u_i_big_vector: G1Projective,
    index: usize,
    pi_i_vector: Fr,
    num: usize,
) {
    let mut hasher = Sha256::new();

    let y_temp = y_i_vector.to_string().as_bytes().to_vec();
    let u_temp = u_i_big_vector.to_string().as_bytes().to_vec();
    let i_temp = index.to_string().as_bytes().to_vec();
    let total = num.to_string().as_bytes().to_vec();

    hasher.update(y_temp);
    hasher.update(u_temp);
    hasher.update(i_temp);
    hasher.update(total);

    let result = hasher.finalize();

    let pii = Fr::from(BigUint::from_bytes_be(result.as_slice()));

    let a = G1Projective::generator() * pi_i_vector;
    let b = y_i_vector * pii + u_i_big_vector;

    assert_eq!(a, b);
}

pub fn get_nizk_proof(
    y_i_vector: G1Projective,
    u_i_big_vector: G1Projective,
    x_i_vector: Fr,
    u_i_small_vector: Fr,
    index: usize,
    num: usize,
) -> Fr {
    let mut hasher = Sha256::new();

    let y_temp = y_i_vector.to_string().as_bytes().to_vec();
    let u_temp = u_i_big_vector.to_string().as_bytes().to_vec();
    let i_temp = index.to_string().as_bytes().to_vec();
    let total = num.to_string().as_bytes().to_vec();

    hasher.update(y_temp);
    hasher.update(u_temp);
    hasher.update(i_temp);
    hasher.update(total);

    let result = hasher.finalize();

    let x_bar = Fr::from(BigUint::from_bytes_be(result.as_slice()));

    x_bar * x_i_vector + u_i_small_vector
}

pub fn dqea_compute_sharesandwitness(
    vecs: Vec<DensePolynomial<Fr>>,
    srs: Srs,
    rho: Fr,
    i_value: Fr,
) -> (Vec<Share>, Vec<Witness>) {
    let shares = vecs
        .par_iter()
        .map(|p| open(p, i_value))
        .collect::<Vec<_>>();

    let witnesses = vecs
        .par_iter()
        .enumerate()
        .map(|(idx, p)| create_witness(&srs, p, idx + 1, i_value, rho))
        .collect::<Result<Vec<_>, _>>()
        .unwrap();

    (shares, witnesses)
}

pub fn dqea_prequote_phase<R: RngCore>(
    triple: BeaverTripleShares<Fr>,
    x_i_vector: Vec<Fr>,
    y_i_vector: Vec<G1Projective>,
    lambda_i_vector: Vec<Fr>,
    u_i_small_vector: Vec<Fr>,
    rng: &mut R,
    thres_num: usize,
) -> (
    AdditiveShares<Fr>,
    AdditiveShares<Fr>,
    Vec<G1Projective>,
    Vec<Fr>,
    AdditiveShares<Fr>,
) {
    let k_i_vector = share_secret_n_n(Fr::rand(rng), thres_num + 1, rng);

    let fy_i_vector = k_i_vector
        .shares
        .par_iter()
        .map(|x| G1Projective::generator() * x)
        .collect::<Vec<_>>();

    let w_i_vector = (0..thres_num + 1)
        .into_par_iter()
        .map(|i| u_i_small_vector[i] * lambda_i_vector[i])
        .collect::<Vec<_>>();

    let w_i_vector = AdditiveShares { shares: w_i_vector };

    let V_i_vector = beaver_multiply_n_n(&k_i_vector, &w_i_vector, &triple);

    let pi_i_two_vector = (0..thres_num + 1)
        .into_par_iter()
        .map(|index| {
            get_nizk_proof(
                y_i_vector[index],
                fy_i_vector[index],
                x_i_vector[index],
                k_i_vector.shares[index],
                index,
                thres_num,
            )
        })
        .collect::<Vec<_>>();

    (
        k_i_vector,
        w_i_vector,
        fy_i_vector,
        pi_i_two_vector,
        V_i_vector,
    )
}

pub fn dqea_quote_phase(
    vk: G1Projective,
    y_i_vector: Vec<G1Projective>,
    fy_i_vector: Vec<G1Projective>,
    pi_i_two_vector: Vec<Fr>,
    V_i_vector: AdditiveShares<Fr>,
    k_i_vector: AdditiveShares<Fr>,
    w_i_vector: AdditiveShares<Fr>,
    report_m: &[u8],
    header_phi: &[u8],
    thres_num: usize,
) -> (Vec<Fr>, Fr, Fr, Fr, G1Affine) {
    for index in 0..thres_num + 1 {
        verify_nizk_proof(
            y_i_vector[index],
            fy_i_vector[index],
            index,
            pi_i_two_vector[index],
            thres_num,
        );
    }

    let mut hasher1 = Sha256::new();

    hasher1.update(report_m);
    hasher1.update(header_phi);

    let res = hasher1.finalize();

    let mut hasher2 = Sha256::new();

    for index in 0..thres_num + 1 {
        hasher2.update(pi_i_two_vector[index].to_string().as_bytes().to_vec());
        hasher2.update(fy_i_vector[index].to_string().as_bytes().to_vec());
        hasher2.update(V_i_vector.shares[index].to_string().as_bytes().to_vec());
    }

    hasher2.update(vk.to_string().as_bytes().to_vec());
    hasher2.update(res);

    let Lambda = hasher2.finalize();
    let Theta = Sha256::digest(Lambda);

    let Lambda_new = Fr::from(BigUint::from_bytes_be(Lambda.as_slice()));
    let Theta_new = Fr::from(BigUint::from_bytes_be(Theta.as_slice()));

    let deta_i_vector: Vec<_> = (0..thres_num + 1)
        .into_par_iter()
        .map(|index| {
            Lambda_new * V_i_vector.shares[index] + Theta_new * w_i_vector.shares[index]
        })
        .collect();

    let deta: Fr = deta_i_vector.iter().sum();

    let R = vk * deta.inverse().unwrap();
    let R_new = R.into_affine();
    let r = R_new.x;

    let r_new = Fr::from(BigUint::from_bytes_be(r.to_string().as_bytes()));

    let s_i_vector = (0..thres_num + 1)
        .into_par_iter()
        .map(|index| {
            let temp1 = k_i_vector.shares[index] * Fr::from(BigUint::from_bytes_be(res.as_slice()))
                + r_new * V_i_vector.shares[index];

            let temp2 = r_new * Theta_new * w_i_vector.shares[index];

            Lambda_new * temp1 + temp2
        })
        .collect::<Vec<_>>();

    let pi_ii_vector: Vec<_> = s_i_vector.par_iter().map(|x| R * x).collect();

    let hash_message_to_field = Fr::from(BigUint::from_bytes_be(res.as_slice()));

    (
        s_i_vector,
        Theta_new,
        r_new,
        hash_message_to_field,
        R_new,
    )
}

pub fn dqea_verify(hash_message_to_field: Fr, vk: G1Projective, sig: (Fr, Fr)) {
    let s = sig.1;
    let r_new = sig.0;

    let q1 = G1Projective::generator() * hash_message_to_field + vk * r_new;

    let s = q1 * s.inverse().unwrap();
    let s_new = s.into_affine().x;

    let rr = Fr::from(BigUint::from_bytes_be(s_new.to_string().as_bytes()));

    assert_eq!(r_new, rr);
}

pub fn get_nizk_type2(s_i_vector: Vec<Fr>, R_new: G1Affine) -> Vec<G1Projective> {
    let p_iii = s_i_vector
        .par_iter()
        .map(|value| R_new * value)
        .collect::<Vec<_>>();

    p_iii
}

pub fn verify_nizk_type2(
    R_new: G1Affine,
    r_new: Fr,
    vk: G1Projective,
    p_iii: Vec<G1Projective>,
    hash_message_to_field: Fr,
    Theta_new: Fr,
) {
    let u1 = R_new * hash_message_to_field * Theta_new;

    let u2: G1Projective = p_iii.iter().sum();

    let u3 = vk * r_new + G1Projective::generator() * hash_message_to_field;

    assert_eq!(u1 + u2, u3);
}
