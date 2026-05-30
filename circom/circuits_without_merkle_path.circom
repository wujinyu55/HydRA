pragma circom 2.1.6;

include "circomlib/circuits/poseidon.circom";

template AttestationCircuitNoPath(ROOT_LEN) {
    assert(ROOT_LEN > 0);

    /*
        public input:
        pk
        root[0..ROOT_LEN-1]
        output
        time
        period

        private witness:
        sk
        ar
    */

    signal input pk;
    signal input sk;
    signal input ar;
    signal input time;
    signal input period;
    signal input output;

    signal input root[ROOT_LEN];

    /*
        m = Poseidon(ar, sk)
        leaf = Poseidon(m, pk)
    */

    component hash_m = Poseidon(2);
    hash_m.inputs[0] <== ar;
    hash_m.inputs[1] <== sk;

    component hash_leaf = Poseidon(2);
    hash_leaf.inputs[0] <== hash_m.out;
    hash_leaf.inputs[1] <== pk;

    /*
        Rust:
        leaf.enforce_equal(&root[0])?;
    */
    hash_leaf.out === root[0];

    /*
        output = Poseidon(Poseidon(Poseidon(pk, ar), time), period)
    */

    component hash_result_1 = Poseidon(2);
    hash_result_1.inputs[0] <== pk;
    hash_result_1.inputs[1] <== ar;

    component hash_result_2 = Poseidon(2);
    hash_result_2.inputs[0] <== hash_result_1.out;
    hash_result_2.inputs[1] <== time;

    component hash_result = Poseidon(2);
    hash_result.inputs[0] <== hash_result_2.out;
    hash_result.inputs[1] <== period;

    output === hash_result.out;
}
