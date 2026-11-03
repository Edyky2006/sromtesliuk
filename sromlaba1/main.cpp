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


    bool operator>=(const BigInt<N>& other) const {
        return !(*this < other);
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

template <size_t N>
void runTime() {
    const int ITERATIONS = 1000000;

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

        if (data_A[i] < data_B[i]) {
            swap(data_A[i], data_B[i]);
        }
    }
    BigInt<N> exp("5", 10);

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

    benchmark("Addition (+)", [&](int i) { return data_A[i] + data_B[i]; });
    benchmark("Subtraction (-)", [&](int i) { return data_A[i] - data_B[i]; });
    benchmark("Multiplication (*)", [&](int i) { return data_A[i] * data_B[i]; });

    BigInt<N> Q, R;
    benchmark("Division (/)", [&](int i) {
        BigInt<N>::divMod(data_A[i], data_B[i], Q, R);
        return Q;
    });

    benchmark("Power (^5)", [&](int i) { return data_A[i].power(exp); });

    benchmark("Square (^2)", [&](int i) { return data_A[i].square(); });

    cout << string(65, '-') << "\n\n";
}

template <size_t N>
void printNumberRepresentations(const string& name, const BigInt<N>& num) {
    cout << "--- Representation of Number " << name << " ---\n";
    cout << "Symbolic (Hex) : " << num.toHex() << "\n";
    cout << "Symbolic (Dec) : " << num.toDec() << "\n";
    cout << "Bitwise  (Bin) : " << num.toBin() << "\n\n";
}


int main() {
    BigInt<32> A("987654321098765432109876", 10);
    BigInt<32> B("123456789012345678901234", 10);

    if (A < B) {
        swap(A, B);
    }

    BigInt<32> C("555555555", 10);

    cout << "=== Representations of Numbers (1024 and 512 bits) ===\n\n";
    printNumberRepresentations("A (1024-bit)", A);
    printNumberRepresentations("B (1024-bit)", B);
    printNumberRepresentations("C (512-bit)", C);

    cout << "=== Results of Basic Operations ===\n\n";

    BigInt<32> sum = A + B;
    printNumberRepresentations("A + B", sum);

    BigInt<32> diff = A - B;
    printNumberRepresentations("A - B", diff);

    BigInt<32> prod = A * B;
    printNumberRepresentations("A * B", prod);

    BigInt<32> div_res = A / C;
    printNumberRepresentations("A / C", div_res);

    BigInt<32> mod_res = A % C;
    printNumberRepresentations("A mod C", mod_res);


    cout << "=== Tests ===\n\n";

    BigInt<5> a("123", 10);
    BigInt<5> b("9876", 10);
    BigInt<5> c_small("55555555555555555555", 10);

    testDistributiveProperty(a, b, c_small);
    testRepeatedAddition(a, 100);
    testDivisionIdentity(b, a);
    testExponentiation(a);

    runTime<32>();

    return 0;
}
