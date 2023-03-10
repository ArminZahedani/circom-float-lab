pragma circom 2.0.0;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////// Templates from the circomlib ////////////////////////////////
////////////////// Copy-pasted here for easy reference //////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

/*
 * Outputs `a` AND `b`
 */
template AND() {
    signal input a;
    signal input b;
    signal output out;

    out <== a*b;
}

/*
 * Outputs `a` OR `b`
 */
template OR() {
    signal input a;
    signal input b;
    signal output out;

    out <== a + b - a*b;
}

/*
 * `out` = `cond` ? `L` : `R`
 */
template IfThenElse() {
    signal input cond;
    signal input L;
    signal input R;
    signal output out;

    out <== cond * (L - R) + R;
}

/*
 * (`outL`, `outR`) = `sel` ? (`R`, `L`) : (`L`, `R`)
 */
template Switcher() {
    signal input sel;
    signal input L;
    signal input R;
    signal output outL;
    signal output outR;

    signal aux;

    aux <== (R-L)*sel;
    outL <==  aux + L;
    outR <== -aux + R;
}

/*
 * Decomposes `in` into `b` bits, given by `bits`.
 * Least significant bit in `bits[0]`.
 * Enforces that `in` is at most `b` bits long.
 */
template Num2Bits(b) {
    signal input in;
    signal output bits[b];

    for (var i = 0; i < b; i++) {
        bits[i] <-- (in >> i) & 1;
        bits[i] * (1 - bits[i]) === 0;
    }
    var sum_of_bits = 0;
    for (var i = 0; i < b; i++) {
        sum_of_bits += (2 ** i) * bits[i];
    }
    sum_of_bits === in;
}

/*
 * Reconstructs `out` from `b` bits, given by `bits`.
 * Least significant bit in `bits[0]`.
 */
template Bits2Num(b) {
    signal input bits[b];
    signal output out;
    var lc = 0;

    for (var i = 0; i < b; i++) {
        lc += (bits[i] * (1 << i));
    }
    out <== lc;
}

/*
 * Checks if `in` is zero and returns the output in `out`.
 */
template IsZero() {
    signal input in;
    signal output out;

    signal inv;

    inv <-- in!=0 ? 1/in : 0;

    out <== -in*inv +1;
    in*out === 0;
}

/*
 * Checks if `in[0]` == `in[1]` and returns the output in `out`.
 */
template IsEqual() {
    signal input in[2];
    signal output out;

    component isz = IsZero();

    in[1] - in[0] ==> isz.in;

    isz.out ==> out;
}

/*
 * Checks if `in[0]` < `in[1]` and returns the output in `out`.
 */
template LessThan(n) {
    assert(n <= 252);
    signal input in[2];
    signal output out;

    component n2b = Num2Bits(n+1);

    n2b.in <== in[0]+ (1<<n) - in[1];

    out <== 1-n2b.bits[n];
}

/////////////////////////////////////////////////////////////////////////////////////
///////////////////////// Templates for this lab ////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

/*
 * Outputs `out` = 1 if `in` is at most `b` bits long, and 0 otherwise.
 */
template CheckBitLength(b) {
    signal input in;
    signal output out;

    signal bits[b];

    for (var i = 0; i < b; i++) {
        bits[i] <-- (in >> i) & 1;
        bits[i] * (1 - bits[i]) === 0;
    }
    var sum_of_bits = 0;
    for (var i = 0; i < b; i++) {
        sum_of_bits += (2 ** i) * bits[i];
    }
    component checker = IsEqual();
    checker.in[0] <== sum_of_bits;
    checker.in[1] <== in;
    out <== checker.out;
}

/*
 * Enforces the well-formedness of an exponent-mantissa pair (e, m), which is defined as follows:
 * if `e` is zero, then `m` must be zero
 * else, `e` must be at most `k` bits long, and `m` must be in the range [2^p, 2^p+1)
 */
template CheckWellFormedness(k, p) {
    signal input e;
    signal input m;

    // check if `e` is zero
    component is_e_zero = IsZero();
    is_e_zero.in <== e;

    // Case I: `e` is zero
    //// `m` must be zero
    component is_m_zero = IsZero();
    is_m_zero.in <== m;

    // Case II: `e` is nonzero
    //// `e` is `k` bits
    component check_e_bits = CheckBitLength(k);
    check_e_bits.in <== e;
    //// `m` is `p`+1 bits with the MSB equal to 1
    //// equivalent to check `m` - 2^`p` is in `p` bits
    component check_m_bits = CheckBitLength(p);
    check_m_bits.in <== m - (1 << p);

    // choose the right checks based on `is_e_zero`
    component if_else = IfThenElse();
    if_else.cond <== is_e_zero.out;
    if_else.L <== is_m_zero.out;
    //// check_m_bits.out * check_e_bits.out is equivalent to check_m_bits.out AND check_e_bits.out
    if_else.R <== check_m_bits.out * check_e_bits.out;

    // assert that those checks passed
    if_else.out === 1;
}

/*
 * Right-shifts `x` by `shift` bits to output `y`, where `shift` is a public circuit parameter.
 */
template RightShift(shift) {
    signal input x;
    signal output y;
    
    signal bits[shift];
    signal rightShift[shift + 1];

    for (var i = 0; i < shift; i++) {
        bits[i] <-- (x >> i) & 1;   //extracts the bits we shift away i.e. bits[0] is the first bit we shift away, bits[1] is the next
        bits[i] * (1 - bits[i]) === 0;
    }
    signal intermediate <-- x >> shift; //do the actual bit shifts
    rightShift[shift] <== intermediate;
    for(var i = shift - 1; i >= 0; i+= -1) {
        rightShift[i] <== (rightShift[i + 1] * 2) + bits[i];
    }
    x === rightShift[0];
    y <== intermediate;

}

/*
 * Rounds the input floating-point number and checks to ensure that rounding does not make the mantissa unnormalized.
 * Rounding is necessary to prevent the bitlength of the mantissa from growing with each successive operation.
 * The input is a normalized floating-point number (e, m) with precision `P`, where `e` is a `k`-bit exponent and `m` is a `P`+1-bit mantissa.
 * The output is a normalized floating-point number (e_out, m_out) representing the same value with a lower precision `p`.
 */
template RoundAndCheck(k, p, P) {
    signal input e;
    signal input m;
    signal output e_out;
    signal output m_out;
    assert(P > p);

    // check if no overflow occurs
    component if_no_overflow = LessThan(P+1);
    if_no_overflow.in[0] <== m;
    if_no_overflow.in[1] <== (1 << (P+1)) - (1 << (P-p-1));
    signal no_overflow <== if_no_overflow.out;

    var round_amt = P-p;
    // Case I: no overflow
    // compute (m + 2^{round_amt-1}) >> round_amt
    var m_prime = m + (1 << (round_amt-1));
    component right_shift = RightShift(round_amt);
    right_shift.x <== m_prime;
    var m_out_1 = right_shift.y;
    var e_out_1 = e;

    // Case II: overflow
    var e_out_2 = e + 1;
    var m_out_2 = (1 << p);

    // select right output based on no_overflow
    component if_else[2];
    for (var i = 0; i < 2; i++) {
        if_else[i] = IfThenElse();
        if_else[i].cond <== no_overflow;
    }
    if_else[0].L <== e_out_1;
    if_else[0].R <== e_out_2;
    if_else[1].L <== m_out_1;
    if_else[1].R <== m_out_2;
    e_out <== if_else[0].out;
    m_out <== if_else[1].out;
}

/*
 * Left-shifts `x` by `shift` bits to output `y`.
 * Enforces 0 <= `shift` < `shift_bound`.
 * If `skip_checks` = 1, then we don't care about the output and the `shift_bound` constraint is not enforced.
 */
template LeftShift(shift_bound) {
    signal input x;
    signal input shift;
    signal input skip_checks;
    signal output y;

    //idea: if 0 <= shift then we can check if shift +1 is greater than 0 i.e. if shift = -1, then shift + 1 = 0 which is not greater than 1.
    // if shift = 0, then shift + 1 = 1, which is greater than 0.

    var num_bits_shift_bound = 0;
    while(1 << num_bits_shift_bound < shift_bound){
        num_bits_shift_bound++;
    }

    component less_than_bound = LessThan(num_bits_shift_bound + 1);
    less_than_bound.in[0] <== 0;
    less_than_bound.in[1] <== shift + 1; //check if 0 < shift + 1 i.e. 0 <= shift.

    component less_than_bound2 = LessThan(num_bits_shift_bound + 1);
    less_than_bound2.in[0] <== shift;
    less_than_bound2.in[1] <== shift_bound;
    //Done checks
    
    component n2b = Num2Bits(num_bits_shift_bound + 1);
    n2b.in <== shift;

    signal left[num_bits_shift_bound + 1];
    left[num_bits_shift_bound] <== x;
    var multiplier;
    for(var i = num_bits_shift_bound - 1; i >= 0; i--){
        multiplier = 1 << (1 << (i));
        left[i] <== n2b.bits[i] * (left[i+1] * multiplier - left[i+1]) + left[i+1];
    }
    y <== left[0];

    //if skip_checks = 1, then check only left shift, otherwise also bound.
    component if_else = IfThenElse();
    if_else.cond <== skip_checks;
    if_else.L <== 1;
    if_else.R <== less_than_bound.out * less_than_bound2.out;

    if_else.out === 1;
}

/*
 * Find the Most-Significant Non-Zero Bit (MSNZB) of `in`, where `in` is assumed to be non-zero value of `b` bits.
 * Outputs the MSNZB as a one-hot vector `one_hot` of `b` bits, where `one_hot`[i] = 1 if MSNZB(`in`) = i and 0 otherwise.
 * The MSNZB is output as a one-hot vector to reduce the number of constraints in the subsequent `Normalize` template.
 * Enforces that `in` is non-zero as MSNZB(0) is undefined.
 * If `skip_checks` = 1, then we don't care about the output and the non-zero constraint is not enforced.
 */
template MSNZB(b) {
    signal input in;
    signal input skip_checks;
    signal output one_hot[b];

    component isZero = IsZero();
    isZero.in <== in;

    component toBits = Num2Bits(b + 1);
    toBits.in <== in;
    signal bits[b + 1] <== toBits.bits;

    signal sawOne[b + 1]; //sawOne will be 0 until seeing the first 1 where it will be 1 forever.
    sawOne[b] <== 0;        //initializer
    for(var i = b - 1; i >= 0; i--) {
        sawOne[i] <== sawOne[i + 1] + (bits[i]) - (sawOne[i + 1] * (bits[i]));  //OR between whether we have ever seen a 1, with the current bit position.
    }
    for(var i = 0; i < b; i++){
        one_hot[i] <== sawOne[i] + sawOne[i + 1] - 2 * sawOne[i] * sawOne[i + 1];   //XOR between subsequent positions. Since the MSB will have 0 as its 
                                                                                    // neighbor, the MSB will be the only 1.
    }

    component if_else = IfThenElse();
    if_else.cond <== skip_checks;
    if_else.L <== 1;
    if_else.R <== 1 - isZero.out; //enforce NOT zero.

    if_else.out === 1;

}

/*
 * Normalizes the input floating-point number.
 * The input is a floating-point number with a `k`-bit exponent `e` and a `P`+1-bit *unnormalized* mantissa `m` with precision `p`, where `m` is assumed to be non-zero.
 * The output is a floating-point number representing the same value with exponent `e_out` and a *normalized* mantissa `m_out` of `P`+1-bits and precision `P`.
 * Enforces that `m` is non-zero as a zero-value can not be normalized.
 * If `skip_checks` = 1, then we don't care about the output and the non-zero constraint is not enforced.
 */
template Normalize(k, p, P) {
    signal input e;
    signal input m;
    signal input skip_checks;
    signal output e_out;
    signal output m_out;
    assert(P > p);

    component msnzb = MSNZB(P + 1);
    msnzb.in <== m;
    msnzb.skip_checks <== skip_checks;

    signal shifter[P + 1];
    shifter[0] <== 1;
    for(var i = 1; i < P + 1; i++){
        shifter[i] <== msnzb.one_hot[i] * (i * shifter[i - 1] - shifter[i - 1]) + shifter[i - 1];
    }
    
    component left_shift = LeftShift(P);
    left_shift.x <== m;
    left_shift.shift <== (P - shifter[P]);
    left_shift.skip_checks <== skip_checks;
    
    m_out <== left_shift.y;
    e_out <== e + shifter[P] - p;
}

/*
 * Adds two floating-point numbers.
 * The inputs are normalized floating-point numbers with `k`-bit exponents `e` and `p`+1-bit mantissas `m` with scale `p`.
 * Does not assume that the inputs are well-formed and makes appropriate checks for the same.
 * The output is a normalized floating-point number with exponent `e_out` and mantissa `m_out` of `p`+1-bits and scale `p`.
 * Enforces that inputs are well-formed.
 */
template FloatAdd(k, p) {
    signal input e[2];
    signal input m[2];
    signal output e_out;
    signal output m_out;

    component checkWell1 = CheckWellFormedness(k, p);
    checkWell1.e <== e[0];
    checkWell1.m <== m[0];

    component checkWell2 = CheckWellFormedness(k, p);
    checkWell2.e <== e[1];
    checkWell2.m <== m[1];

    component left_shift1 = LeftShift(k + p);
    left_shift1.x <== e[0];
    left_shift1.shift <== p + 1;
    left_shift1.skip_checks <== 0;
    signal mgn1 <== left_shift1.y + m[0];

    component left_shift2 = LeftShift(k + p);
    left_shift2.x <== e[1];
    left_shift2.shift <== p + 1;
    left_shift2.skip_checks <== 0;
    signal mgn2 <== left_shift2.y + m[1];
    
    component mgn2_less_mgn1 = LessThan(k + p); //check mgn2 < mgn1
    mgn2_less_mgn1.in[0] <== mgn2;
    mgn2_less_mgn1.in[1] <== mgn1;

    signal alpha_e;
    signal alpha_m;
    signal beta_e;
    signal beta_m;

    alpha_e <== mgn2_less_mgn1.out * (e[0] - e[1]) + e[1];
    alpha_m <== mgn2_less_mgn1.out * (m[0] - m[1]) + m[1];

    beta_e <== (1 - mgn2_less_mgn1.out) * (e[0] - e[1]) + e[1];
    beta_m <== (1 - mgn2_less_mgn1.out) * (m[0] - m[1]) + m[1];

    signal diff <== alpha_e - beta_e;

    component less_p_1_diff = LessThan(k + p + 1);
    less_p_1_diff.in[0] <== p + 1;
    less_p_1_diff.in[1] <== diff;

    component is_alpha_e_zero = IsZero();
    is_alpha_e_zero.in <== alpha_e;

    signal length <== less_p_1_diff.out + (is_alpha_e_zero.out) - less_p_1_diff.out * (is_alpha_e_zero.out);

    // The else condition
    component alpha_m_prime = LeftShift(k + p);
    alpha_m_prime.x <== (1 - length) * alpha_m;
    alpha_m_prime.shift <== (1 - length) * diff;
    alpha_m_prime.skip_checks <== length;
    signal m_new <== (1 - length) * (alpha_m_prime.y + beta_m);
    signal e_new <== beta_e;

    component normalized = Normalize(k, p, 2 * p + 1);
    normalized.e <== (1 - length) * e_new;
    normalized.m <== (1 - length) * m_new;
    normalized.skip_checks <== (length);

    component round_check = RoundAndCheck(k, p, 2 * p + 1);
    round_check.e <== normalized.e_out;
    round_check.m <== normalized.m_out;
    // end else
    
    e_out <== (length) * (alpha_e - round_check.e_out) + round_check.e_out;
    m_out <== (length) * (alpha_m - round_check.m_out) + round_check.m_out;
}
