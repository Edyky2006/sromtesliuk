#include <iostream>
#include <array>
#include <cstdint>
#include <iomanip>
#include <sstream>
#include <string>

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
};

int main() {

    return 0;
}
