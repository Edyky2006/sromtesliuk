#include <iostream>
#include <array>
#include <cstdint>
#include <iomanip>
#include <sstream>
#include <string>
#include <algorithm>
#include <chrono>
#include <x86intrin.h>
#include <vector>
#include <random>

using namespace std;

template <size_t N>
class BigInt {
private:
    array<uint32_t, N> blocks;

public:
    BigInt() {
        blocks.fill(0);
    }

    BigInt(uint32_t value) {
        blocks.fill(0);
        if (N > 0) {
            blocks[0] = value;
        }
    }

    uint32_t getBlock(size_t index) const {
        return blocks[index];
    }

    BigInt<N> operator+(const BigInt<N>& other) const {
        BigInt<N> result;
        uint64_t carry = 0;

        for (size_t i = 0; i < N; ++i) {
            uint64_t sum = static_cast<uint64_t>(this->blocks[i]) + other.blocks[i] + carry;

            result.blocks[i] = static_cast<uint32_t>(sum);

            carry = sum >> 32;
        }


        return result;
    }


    BigInt<N> operator-(const BigInt<N>& other) const {
        BigInt<N> result;
        uint64_t borrow = 0;

        for (size_t i = 0; i < N; ++i) {
            uint64_t diff = static_cast<uint64_t>(this->blocks[i]) - other.blocks[i] - borrow;

            result.blocks[i] = static_cast<uint32_t>(diff);

            borrow = (diff >> 32) & 1;
        }


        return result;
    }

    BigInt<N> operator*(const BigInt<N>& other) const {
        BigInt<N> result;

        for (size_t i = 0; i < N; ++i) {
            uint64_t carry = 0;

            for (size_t j = 0; j < N - i; ++j) {
                uint64_t prod = static_cast<uint64_t>(this->blocks[i]) * other.blocks[j];

                uint64_t sum = static_cast<uint64_t>(result.blocks[i + j]) + prod + carry;

                result.blocks[i + j] = static_cast<uint32_t>(sum);

                carry = sum >> 32;
            }
        }

        return result;
    }

    BigInt<N> square() const {
        BigInt<N> result;

        for (size_t i = 0; i < N; ++i) {
            if (this->blocks[i] == 0) continue;

            uint64_t carry = 0;
            for (size_t j = i + 1; i + j < N; ++j) {
                uint64_t prod = static_cast<uint64_t>(this->blocks[i]) * this->blocks[j];
                uint64_t sum = static_cast<uint64_t>(result.blocks[i + j]) + prod + carry;

                result.blocks[i + j] = static_cast<uint32_t>(sum);
                carry = sum >> 32;
            }
        }

        uint32_t bit_carry = 0;
        for (size_t i = 0; i < N; ++i) {
            uint32_t next_carry = result.blocks[i] >> 31;
            result.blocks[i] = (result.blocks[i] << 1) | bit_carry;
            bit_carry = next_carry;
        }

        uint64_t carry = 0;
        for (size_t i = 0; i < N; ++i) {
            uint64_t sum = static_cast<uint64_t>(result.blocks[i]) + carry;

            if (i % 2 == 0) {
                size_t idx = i / 2;
                uint64_t sq = static_cast<uint64_t>(this->blocks[idx]) * this->blocks[idx];

                sum += static_cast<uint32_t>(sq);
                carry = (sum >> 32) + (sq >> 32);
            } else {
                carry = sum >> 32;
            }
            result.blocks[i] = static_cast<uint32_t>(sum);
        }

        return result;
    }


    size_t bitLength() const {
        for (int i = N - 1; i >= 0; --i) {
            if (this->blocks[i] != 0) {
                uint32_t block = this->blocks[i];
                size_t bits = 0;
                while (block > 0) {
                    bits++;
                    block >>= 1;
                }
                return (i * 32) + bits;
            }
        }
        return 0;
    }


    BigInt<N> shiftLeft(size_t shift) const {
        BigInt<N> result;
        if (shift == 0) return *this;

        size_t blockShift = shift / 32;
        size_t bitShift = shift % 32;

        for (size_t i = 0; i < N; ++i) {
            if (i + blockShift < N) {
                result.blocks[i + blockShift] |= (this->blocks[i] << bitShift);
            }
            if (bitShift > 0 && i + blockShift + 1 < N) {
                result.blocks[i + blockShift + 1] |= (this->blocks[i] >> (32 - bitShift));
            }
        }
        return result;
    }

    BigInt<N> shiftRight(size_t shift) const {
        BigInt<N> result;
        if (shift == 0) return *this;

        size_t blockShift = shift / 32;
        size_t bitShift = shift % 32;

        for (size_t i = 0; i < N; ++i) {
            if (i >= blockShift) {
                result.blocks[i - blockShift] |= (this->blocks[i] >> bitShift);
            }
            if (bitShift > 0 && i >= blockShift + 1) {
                result.blocks[i - blockShift - 1] |= (this->blocks[i] << (32 - bitShift));
            }
        }
        return result;
    }

    void setBit(size_t index) {
        if (index < N * 32) {
            this->blocks[index / 32] |= (1U << (index % 32));
        }
    }

    void clearBit(size_t index) {
        if (index < N * 32) {
            this->blocks[index / 32] &= ~(1U << (index % 32));
        }
    }


    bool operator>=(const BigInt<N>& other) const {
        return !(*this < other);
    }

    bool operator>(const BigInt<N>& other) const {
        return other < *this;
    }

    bool operator!=(const BigInt<N>& other) const {
        return !(*this == other);
    }

    bool operator<(const BigInt<N>& other) const {
        for (int i = N - 1; i >= 0; --i) {
            if (this->blocks[i] != other.blocks[i]) {
                return this->blocks[i] < other.blocks[i];
            }
        }
        return false;
    }

    bool operator==(const BigInt<N>& other) const {
        for (size_t i = 0; i < N; ++i) {
            if (this->blocks[i] != other.blocks[i]) return false;
        }
        return true;
    }


    static void divMod(const BigInt<N>& A, const BigInt<N>& B, BigInt<N>& Q, BigInt<N>& R) {
        size_t k = B.bitLength();
        if (k == 0) {
            throw invalid_argument("Division by zero");
        }

        R = A;
        Q = BigInt<N>();

        while (R >= B) {
            size_t t = R.bitLength();
            BigInt<N> C = B.shiftLeft(t - k);

            if (R < C) {
                t = t - 1;
                C = B.shiftLeft(t - k);
            }

            R = R - C;
            Q.setBit(t - k);
        }
    }

    BigInt<N> operator/(const BigInt<N>& other) const {
        BigInt<N> Q, R;
        divMod(*this, other, Q, R);
        return Q;
    }

    BigInt<N> operator%(const BigInt<N>& other) const {
        BigInt<N> Q, R;
        divMod(*this, other, Q, R);
        return R;
    }


    bool getBit(size_t index) const {
        if (index >= N * 32) return false;
        return (this->blocks[index / 32] >> (index % 32)) & 1;
    }

    BigInt<N> power(const BigInt<N>& B) const {
        BigInt<N> C(1);
        BigInt<N> A = *this;
        size_t m = B.bitLength();

        for (size_t i = 0; i < m; ++i) {
            if (B.getBit(i)) {
                C = C * A;
            }
            A = A * A;
        }

        return C;
    }



    string toHex() const {
        stringstream ss;
        ss << hex << setfill('0');

        bool foundNonZero = false;

        for (int i = N - 1; i >= 0; --i) {
            if (blocks[i] != 0 || foundNonZero) {
                if (!foundNonZero) {
                    ss << blocks[i];
                    foundNonZero = true;
                } else {

                    ss << setw(8) << blocks[i];
                }
            }
        }

        if (!foundNonZero) {
            return "0";
        }

        return ss.str();
    }

    BigInt(const string& str, int base = 16) {
        blocks.fill(0);

        if (base == 16) {
            size_t blockIdx = 0, bitShift = 0;
            for (int i = str.length() - 1; i >= 0; --i) {
                char c = str[i];
                uint32_t val = 0;
                if (c >= '0' && c <= '9') val = c - '0';
                else if (c >= 'a' && c <= 'f') val = c - 'a' + 10;
                else if (c >= 'A' && c <= 'F') val = c - 'A' + 10;
                else continue;

                if (blockIdx < N) {
                    blocks[blockIdx] |= (val << bitShift);
                    bitShift += 4;
                    if (bitShift >= 32) { bitShift = 0; blockIdx++; }
                }
            }
        }
        else if (base == 10) {
            for (char c : str) {
                if (c >= '0' && c <= '9') {
                    *this = (*this) * BigInt<N>(10) + BigInt<N>(c - '0');
                }
            }
        }
        else if (base == 2) {
            size_t blockIdx = 0, bitShift = 0;
            for (int i = str.length() - 1; i >= 0; --i) {
                char c = str[i];
                if (c == '1' && blockIdx < N) {
                    blocks[blockIdx] |= (1U << bitShift);
                }
                if (c == '0' || c == '1') {
                    bitShift++;
                    if (bitShift >= 32) { bitShift = 0; blockIdx++; }
                }
            }
        }
    }

    string toDec() const {
        if (*this == BigInt<N>(0)) return "0";

        BigInt<N> temp = *this;
        BigInt<N> ten(10);
        string res = "";

        while (!(temp == BigInt<N>(0))) {
            BigInt<N> Q, R;
            divMod(temp, ten, Q, R);
            res += to_string(R.blocks[0]);
            temp = Q;
        }

        reverse(res.begin(), res.end());
        return res;
    }

    string toBin() const {
        if (*this == BigInt<N>(0)) return "0";
        string res = "";
        size_t len = bitLength();

        for (int i = len - 1; i >= 0; --i) {
            res += getBit(i) ? '1' : '0';
        }
        return res;
    }

    static BigInt<N> generateRandom() {
        BigInt<N> result;
        static random_device rd;
        static mt19937 gen(rd());
        static uniform_int_distribution<uint32_t> dist(0, 0xFFFFFFFF);

        for (size_t i = 0; i < N; ++i) {
            result.blocks[i] = dist(gen);
        }
        if (result.blocks[N - 1] == 0) {
            result.blocks[N - 1] = 1;
        }
        return result;
    }

    // ===============-----------===========================

    static BigInt<N> gcdClassic(BigInt<N> a, BigInt<N> b) {
        BigInt<N> zero(0);

        while (!(b == zero)) {
            BigInt<N> Q, R;

            divMod(a, b, Q, R);

            a = b;
            b = R;
        }

        return a;
    }

    static BigInt<N> gcdBinary(BigInt<N> a, BigInt<N> b) {
        BigInt<N> zero(0);

        if (a == zero) return b;
        if (b == zero) return a;

        size_t shiftCount = 0;

        while ((a.blocks[0] & 1) == 0 && (b.blocks[0] & 1) == 0) {
            a = a.shiftRight(1);
            b = b.shiftRight(1);
            shiftCount++;
        }

        while ((a.blocks[0] & 1) == 0) {
            a = a.shiftRight(1);
        }

        while (!(b == zero)) {
            while ((b.blocks[0] & 1) == 0) {
                b = b.shiftRight(1);
            }

            if (a > b) {
                std::swap(a, b);
            }
            b = b - a;
        }

        return a.shiftLeft(shiftCount);
    }



    static BigInt<N> lcm(const BigInt<N>& a, const BigInt<N>& b) {
        BigInt<N> zero(0);
        if (a == zero || b == zero) return zero;

        return (a / gcdBinary(a, b)) * b;
    }


    BigInt<N> addMod(const BigInt<N>& other, const BigInt<N>& mod) const {
        BigInt<N> result = *this + other;

        if (result >= mod) {
            result = result - mod;
        }

        return result;
    }

    BigInt<N> subMod(const BigInt<N>& other, const BigInt<N>& mod) const {
        if (*this >= other) {
            return *this - other;
        } else {
            return mod - (other - *this);
        }
    }


    static BigInt<N> computeBarrettMu(const BigInt<N>& mod) {
        size_t k = 0;

        for (int i = N - 1; i >= 0; --i) {
            if (mod.blocks[i] != 0) {
                k = i + 1;
                break;
            }
        }

        if (k == 0) throw invalid_argument("Modulus cannot be zero");

        BigInt<N> dividend(0);

        if (2 * k < N) {
            dividend.setBit(2 * k * 32);
        } else {
            throw overflow_error("Modulus is too large for Barrett reduction with fixed N");
        }

        BigInt<N> Q, R;
        divMod(dividend, mod, Q, R);
        return Q;
    }

    BigInt<N> barrettReduce(const BigInt<N>& mod, const BigInt<N>& mu) const {
        size_t k = 0;
        for (int i = N - 1; i >= 0; --i) {
            if (mod.blocks[i] != 0) {
                k = i + 1;
                break;
            }
        }

        if (k == 0) throw invalid_argument("Modulus cannot be zero");

        if (*this < mod) {
            return *this;
        }

        BigInt<N> q1 = (k > 1) ? this->shiftRight((k - 1) * 32) : *this;
        BigInt<N> q2 = q1 * mu;
        BigInt<N> q3 = q2.shiftRight((k + 1) * 32);

        BigInt<N> q3_mod = q3 * mod;

        BigInt<N> r = *this - q3_mod;

        while (r >= mod) {
            r = r - mod;
        }

        return r;
    }

    BigInt<N> mulMod(const BigInt<N>& other, const BigInt<N>& mod, const BigInt<N>& mu) const {
        BigInt<N> prod = *this * other;

        return prod.barrettReduce(mod, mu);
    }

    BigInt<N> squareMod(const BigInt<N>& mod, const BigInt<N>& mu) const {
        BigInt<N> sq = this->square();

        return sq.barrettReduce(mod, mu);
    }


    BigInt<N> powerMod(const BigInt<N>& exp, const BigInt<N>& mod) const {
        BigInt<N> zero(0);
        if (mod == zero) throw invalid_argument("Modulus cannot be zero");
        if (exp == zero) return BigInt<N>(1);

        BigInt<N> mu = computeBarrettMu(mod);

        BigInt<N> C(1);
        BigInt<N> A = *this;

        int maxBlock = N - 1;
        while (exp.blocks[maxBlock] == 0) {
            maxBlock--;
        }

        for (int i = 0; i <= maxBlock; ++i) {
            uint32_t currentBlock = exp.blocks[i];

            int bitsToProcess = 32;
            if (i == maxBlock) {
                while (bitsToProcess > 0 && (currentBlock & (1U << (bitsToProcess - 1))) == 0) {
                    bitsToProcess--;
                }
            }

            for (int j = 0; j < bitsToProcess; ++j) {
                if (currentBlock & (1U << j)) {
                    C = C.mulMod(A, mod, mu);
                }

                A = A.squareMod(mod, mu);
            }
        }

        return C;
    }
};

template <size_t N>
void testDistributiveProperty(const BigInt<N>& a, const BigInt<N>& b, const BigInt<N>& c) {
    cout << "Test 1: (a + b) * c == c * (a + b) == a * c + b * c\n";

    BigInt<N> left1 = (a + b) * c;
    BigInt<N> mid1 = c * (a + b);
    BigInt<N> right1 = (a * c) + (b * c);

    if ((left1 == mid1) && (left1 == right1)) {
        cout << "[SUCCESS]\n";
        cout << "Result: " << left1.toDec() << "\n\n";
    } else {
        cout << "[FAILED]\n\n";
    }
}

template <size_t N>
void testRepeatedAddition(const BigInt<N>& a, int n_times) {
    cout << "Test 2: n * a == a + a + ... + a (" << n_times << " times)\n";

    BigInt<N> n(to_string(n_times), 10);
    BigInt<N> mult_result = a * n;

    BigInt<N> sum_result("0", 10);
    for (int i = 0; i < n_times; ++i) {
        sum_result = sum_result + a;
    }

    if (mult_result == sum_result) {
        cout << "[SUCCESS]\n";
        cout << "Result: " << mult_result.toDec() << "\n\n";
    } else {
        cout << "[FAILED]\n\n";
    }
}

template <size_t N>
void testDivisionIdentity(const BigInt<N>& divisor, const BigInt<N>& dividend) {
    cout << "Test 3: A = B * Q + R\n";

    BigInt<N> Q, R;
    BigInt<N>::divMod(dividend, divisor, Q, R);

    BigInt<N> rebuilt = (divisor * Q) + R;

    if (rebuilt == dividend) {
        cout << "[SUCCESS]\n";
        cout << "Original: " << dividend.toDec() << "\n";
        cout << "Rebuilt : " << rebuilt.toDec() << "\n\n";
    } else {
        cout << "[FAILED]\n\n";
    }
}

template <size_t N>
void testExponentiation(const BigInt<N>& a) {
    cout << "Test 4: a^3 == a * a * a\n";

    BigInt<N> exp("3", 10);
    BigInt<N> power_result = a.power(exp);

    BigInt<N> direct_result = a * a * a;

    if (power_result == direct_result) {
        cout << "[SUCCESS]\n";
        cout << "Result: " << power_result.toDec() << "\n\n";
    } else {
        cout << "[FAILED]\n\n";
    }
}

// ===================================

template <size_t N>
void testModularDistributive(const BigInt<N>& a, const BigInt<N>& b, const BigInt<N>& c, const BigInt<N>& mod) {
    cout << "Test 1: (a + b)*c == c*(a + b) == a*c + b*c (mod n)\n";

    BigInt<N> mu = BigInt<N>::computeBarrettMu(mod);

    BigInt<N> a_plus_b = a.addMod(b, mod);

    BigInt<N> left = a_plus_b.mulMod(c, mod, mu);

    BigInt<N> mid = c.mulMod(a_plus_b, mod, mu);

    BigInt<N> ac = a.mulMod(c, mod, mu);
    BigInt<N> bc = b.mulMod(c, mod, mu);
    BigInt<N> right = ac.addMod(bc, mod);

    if ((left == mid) && (left == right)) {
        cout << "[SUCCESS] Result: " << left.toDec() << "\n\n";
    } else {
        cout << "[FAILED]\n\n";
    }
}

template <size_t N>
void testModularRepeatedAddition(const BigInt<N>& a, int n_times, const BigInt<N>& mod) {
    cout << "Test 2: n * a == a + a + ... + a (mod m) (" << n_times << " times)\n";
    BigInt<N> mu = BigInt<N>::computeBarrettMu(mod);

    BigInt<N> n_big(to_string(n_times), 10);
    BigInt<N> mult_result = a.mulMod(n_big, mod, mu);

    BigInt<N> sum_result("0", 10);
    for (int i = 0; i < n_times; ++i) {
        sum_result = sum_result.addMod(a, mod);
    }

    if (mult_result == sum_result) {
        cout << "[SUCCESS] Result: " << mult_result.toDec() << "\n\n";
    } else {
        cout << "[FAILED]\n\n";
    }
}

template <size_t N>
void testEulerTheorem() {
    cout << "Test 3: a^phi(n) == 1 (mod n)\n";

    BigInt<N> p("2147483647", 10);
    BigInt<N> phi_p = p - BigInt<N>(1);
    BigInt<N> a1("123456789", 10);

    BigInt<N> res1 = a1.powerMod(phi_p, p);
    cout << " (Prime M31, a^p-1 mod p) : ";
    if (res1 == BigInt<N>(1)) cout << "[SUCCESS]\n Result: " << res1.toDec() << "\n";
    else cout << "[FAILED] " << res1.toDec() << "\n";

    BigInt<N> three("3", 10);
    BigInt<N> two("2", 10);
    BigInt<N> k_40("40", 10);
    BigInt<N> k_39("39", 10);

    BigInt<N> n_3k = three.power(k_40);
    BigInt<N> phi_3k = two * three.power(k_39);

    BigInt<N> a2("10000000000000000000", 10);

    BigInt<N> res2 = a2.powerMod(phi_3k, n_3k);
    cout << " (n = 3^40, a^phi(n) mod n): ";
    if (res2 == BigInt<N>(1)) cout << "[SUCCESS]\n\n Result: " << res2.toDec() << "\n\n";
    else cout << "[FAILED] " << res2.toDec() << "\n\n";
}

template <size_t N>
void runModularTests() {
    cout << "=== B) ===\n\n";
    BigInt<N> a("98765432109876543210", 10);
    BigInt<N> b("12345678901234567890", 10);
    BigInt<N> c("55555555555555555555", 10);
    BigInt<N> mod("99999999999999999989", 10);

    cout << "a: " << a.toDec() << endl;
    cout << "b: " << b.toDec() << endl;
    cout << "c: " << c.toDec() << endl;
    cout << "mod: " << mod.toDec() << endl;

    testModularDistributive(a, b, c, mod);
    testModularRepeatedAddition(a, 150, mod);
    testEulerTheorem<N>();
}

template <size_t N>
void runCustomTests() {
    cout << "=== CUSTOM TESTS ===\n\n";

    cout << "Test 1: a * b == GCD(a,b) * LCM(a,b)\n";
    BigInt<N> a("12345678901234567890", 10);
    BigInt<N> b("98765432109876543210", 10);

    cout << "a: " << a.toDec() << endl;
    cout << "b: " << b.toDec() << endl;

    BigInt<N> ab = a * b;
    BigInt<N> gcd_ab = BigInt<N>::gcdBinary(a, b);
    BigInt<N> lcm_ab = BigInt<N>::lcm(a, b);
    BigInt<N> gcd_lcm = gcd_ab * lcm_ab;

    cout << "ab: " << ab.toDec() << endl;
    cout << "Result: " << gcd_lcm.toDec() << endl;

    if (ab == gcd_lcm) {
        cout << "[SUCCESS]\n\n";
    } else {
        cout << "[FAILED]\n\n";
    }

    cout << "Test 2: X^(A+B) mod M == (X^A * X^B) mod M\n";
    BigInt<N> x("42", 10);
    BigInt<N> expA("1000", 10);
    BigInt<N> expB("1500", 10);
    BigInt<N> mod("99991", 10);

    cout << "X: " << x.toDec() << endl;
    cout << "A: " << expA.toDec() << endl;
    cout << "B: " << expB.toDec() << endl;
    cout << "mod: " << mod.toDec() << endl;

    BigInt<N> expSum = expA + expB;
    BigInt<N> left = x.powerMod(expSum, mod);

    BigInt<N> mu = BigInt<N>::computeBarrettMu(mod);
    BigInt<N> xa = x.powerMod(expA, mod);
    BigInt<N> xb = x.powerMod(expB, mod);
    BigInt<N> right = xa.mulMod(xb, mod, mu);

    cout << "X^(A+B) mod M: " << left.toDec() << endl;
    cout << "(X^A * X^B) mod M\n: " << right.toDec() << endl;

    if (left == right) {
        cout << "[SUCCESS]\n\n";
    } else {
        cout << "[FAILED]\n\n";
    }

    cout << "Test 3: A^p == A (mod p)\n";
    BigInt<N> p("2147483647", 10);
    BigInt<N> A("999999999999999999", 10);

    cout << "p: " << p.toDec() << endl;
    cout << "A: " << A.toDec() << endl;

    BigInt<N> res = A.powerMod(p, p);
    BigInt<N> expected = A % p;

    cout << "expected: " << expected.toDec() << endl;
    cout << "result: " << res.toDec() << endl;

    if (res == expected) {
        cout << "[SUCCESS]\n\n";
    } else {
        cout << "[FAILED]\n\n";
    }
}

template <size_t N>
void runTime() {
    const int ITERATIONS = 10000;

    cout << "--- BENCHMARKS (Average over " << ITERATIONS << " runs) ---\n";
    cout << left << setw(20) << "Operation"
         << setw(25) << "Time (nanoseconds)"
         << setw(25) << "CPU Cycles (ticks)" << "\n";
    cout << string(65, '-') << "\n";

    vector<BigInt<N>> data_A(ITERATIONS);
    vector<BigInt<N>> data_B(ITERATIONS);
    for (int i = 0; i < ITERATIONS; ++i) {
        data_A[i] = BigInt<N>::generateRandom();
        data_B[i] = BigInt<N>::generateRandom();
        data_A[i].setBit(N * 32 - 1);
        data_B[i].clearBit(N * 32 - 1);
    }

    BigInt<N> exp("5", 10);
    BigInt<N> mod = BigInt<N>::generateRandom();
    mod = mod.shiftRight((N / 2 + 1) * 32);
    if (mod == BigInt<N>(0)) mod = BigInt<N>(1);
    BigInt<N> mu = BigInt<N>::computeBarrettMu(mod);

    vector<BigInt<N>> mod_A(ITERATIONS);
    vector<BigInt<N>> mod_B(ITERATIONS);
    for (int i = 0; i < ITERATIONS; ++i) {
        mod_A[i] = data_A[i] % mod;
        mod_B[i] = data_B[i] % mod;
    }

    auto benchmark = [&](const string& name, auto op) {
        auto start_time = chrono::high_resolution_clock::now();
        uint64_t start_cycles = __rdtsc();

        BigInt<N> dummy;
        for (int i = 0; i < ITERATIONS; ++i) {
            dummy = op(i);
        }

        uint64_t end_cycles = __rdtsc();
        auto end_time = chrono::high_resolution_clock::now();

        auto duration_ns = chrono::duration_cast<chrono::nanoseconds>(end_time - start_time).count();

        cout << left << setw(20) << name
             << setw(20) << (duration_ns / ITERATIONS)
             << setw(20) << ((end_cycles - start_cycles) / ITERATIONS)
             << "\n";
    };

    benchmark("Add Mod", [&](int i) { return mod_A[i].addMod(mod_B[i], mod); });
    benchmark("Sub Mod", [&](int i) { return mod_A[i].subMod(mod_B[i], mod); });
    benchmark("Mul Mod (Barrett)", [&](int i) { return mod_A[i].mulMod(mod_B[i], mod, mu); });
    benchmark("Square Mod (Barrett)", [&](int i) { return mod_A[i].squareMod(mod, mu); });
    benchmark("Power Mod (^5)", [&](int i) { return mod_A[i].powerMod(exp, mod); });

    benchmark("GCD (Classic Euclid)", [&](int i) { return BigInt<N>::gcdClassic(mod_A[i], mod_B[i]); });
    benchmark("GCD (Binary Stein)", [&](int i) { return BigInt<N>::gcdBinary(mod_A[i], mod_B[i]); });
    benchmark("LCM", [&](int i) { return BigInt<N>::lcm(mod_A[i], mod_B[i]); });

    cout << string(75, '-') << "\n\n";
}

template <size_t N>
void printNumberRepresentations(const string& name, const BigInt<N>& num) {
    cout << "--- Representation of Number " << name << " ---\n";
    cout << "Symbolic (Hex) : " << num.toHex() << "\n";
    cout << "Symbolic (Dec) : " << num.toDec() << "\n";
    cout << "Bitwise  (Bin) : " << num.toBin() << "\n\n";
}


template <size_t N>
void runModularCalculatorTest() {
    cout << "=== A) ===\n\n";

    BigInt<N> mod("3141592653589793238462643383279502884197169399375105820974944592307816406286208998628034825342117067982148086513282306647093844609550582231725359408128481117450284102701938521105559644622948954930381964428810975665933446128475648233786783165271201909145648566923460348610454326648213393607260249141273", 10);
    BigInt<N> A("271828182845904523536028747135266249775724709369995957496696762772407663035354759457138217852516642742746639193200305992181741359662904357290033429526059563073813232862794349076323382988075319525101901157383418793070215408914993488416750924476146066808226480016847741185374234544243710753907774499206955170276183860626133138458300075204493382656029760673711320070932870912744374704723069697720931014169283681902551510865746377", 10);
    BigInt<N> B("115792089237316195423570985008687907853269984665640564039457584007913129639747", 10);
    BigInt<N> exp("115792089237316195423570985008687907853269984665640564039457584007913129639747", 10);

    cout << "Given N: " << mod.toDec() << endl;
    cout << "Given number: " << A.toDec() << endl;
    cout << "Given number: " << B.toDec() << endl;
    cout << "gcd(A, B)= " << BigInt<N>::gcdBinary(A, B).toDec() << "\n";
    cout << "lcm(A, B)= " << BigInt<N>::lcm(A, B).toDec() << "\n\n";


    A=A%mod;
    B=B%mod;

    BigInt<N> mu = BigInt<N>::computeBarrettMu(mod);

    cout << "N  : " << mod.toDec() << "\n";
    cout << "Number A     : " << A.toDec() << "\n";
    cout << "Number B     : " << B.toDec() << "\n";
    cout << "Exponent (E) : " << exp.toDec() << "\n\n";

    cout << "(A + B) mod M = " << A.addMod(B, mod).toDec() << "\n";
    cout << "(A - B) mod M = " << A.subMod(B, mod).toDec() << "\n";
    cout << "(A * B) mod M = " << A.mulMod(B, mod, mu).toDec() << "\n";
    cout << "(A ^ 2) mod M = " << A.squareMod(mod, mu).toDec() << "\n";
    cout << "(A ^ E) mod M = " << A.powerMod(exp, mod).toDec() << "\n\n";
}

int main() {
    runModularCalculatorTest<128>();

    runModularTests<64>();
    runCustomTests<64>();

    runTime<64>();


    return 0;
}
