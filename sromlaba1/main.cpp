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
