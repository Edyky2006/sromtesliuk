#include <iostream>
#include <array>
#include <cstdint>
#include <iomanip>
#include <sstream>
#include <string>
#include <algorithm>
#include <chrono>
#include <x86intrin.h>

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
        return (*this) * (*this);
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
};


int main(){

    return 0;
};
