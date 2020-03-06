#include <assert.h>
#include <stdint.h>
#include <stdlib.h>
#include <new>
#include <vector>

#ifndef NDEBUG
#include <cstdlib>
#endif // NDEBUG

#ifndef EVM_HPP
#define EVM_HPP

// ** environment **

// WASM has no support for exception handling, here is a simple
// mechanism to simulate support for exceptions and maintain code redability
#ifdef NATIVE_EXCEPTIONS
    #define _throws(F) F
    #define _handles(F) F
    #define _handles0(F) F
    #define _throw(E) throw (E)
    #define _throw0(E) throw (E)
    #define _try(C, X, H) try { C } catch (X) { H }
    #define _catches(F) F
    #define _trythrow(E) throw (E)
#else
    #define _throws_args(...) (Error &_ex, __VA_ARGS__)
    #define _handles_args(...) (_ex, __VA_ARGS__); if (_ex != NONE) return
    #define _handles_args0(...) (_ex, __VA_ARGS__); if (_ex != NONE) return 0
    #define _catches_args(...) (_exlocal, __VA_ARGS__); if (_exlocal != NONE) break

    #define _throws(F) F _throws_args
    #define _handles(F) F _handles_args
    #define _handles0(F) F _handles_args0
    #define _throw(E) { _ex = (E); return; }
    #define _throw0(E) return (_ex = (E), 0)
    #define _try(C, X, H) { Error _extemp = NONE; { Error _exlocal = _extemp; switch(0) { default: { C } } _extemp = _exlocal; } if (_extemp != NONE) { X = _extemp; { H } } }
    #define _catches(F) F _catches_args
    #define _trythrow(E) { _exlocal = (E); break; }
#endif // NATIVE_EXCEPTIONS

// list of errors raised by the interpreter
enum Error {
    NONE = 0,
    CODE_CONFLICT,
    CODE_EXCEEDED,
    GAS_EXAUSTED,
    ILLEGAL_TARGET,
    ILLEGAL_UPDATE,
    INSUFFICIENT_BALANCE,
    INSUFFICIENT_SPACE,
    INVALID_ENCODING,
    INVALID_OPCODE,
    INVALID_SIGNATURE,
    INVALID_SIZE,
    INVALID_TRANSACTION,
    NONCE_MISMATCH,
    OUTOFBOUNDS_VALUE,
    RECURSION_LIMITED,
    STACK_OVERFLOW,
    STACK_UNDERFLOW,
};

// companion table with error names
static const char *errors[STACK_UNDERFLOW+1] = {
    "NONE",
    "CODE_CONFLICT",
    "CODE_EXCEEDED",
    "GAS_EXAUSTED",
    "ILLEGAL_TARGET",
    "ILLEGAL_UPDATE",
    "INSUFFICIENT_BALANCE",
    "INSUFFICIENT_SPACE",
    "INVALID_ENCODING",
    "INVALID_OPCODE",
    "INVALID_SIGNATURE",
    "INVALID_SIZE",
    "INVALID_TRANSACTION",
    "NONCE_MISMATCH",
    "OUTOFBOUNDS_VALUE",
    "RECURSION_LIMITED",
    "STACK_OVERFLOW",
    "STACK_UNDERFLOW",
};

// simple memory allocator override
// aborts execution in case of memory exaustion
template<typename T>
static T *_new(uint64_t size)
{
    if (size == 0) return nullptr;
    T* p = new(std::nothrow) T[size];
    if (p == nullptr) abort();
    return p;
}

template<typename T>
static void _delete(T *p)
{
    if (p != nullptr) delete p;
}

// this replaces dynamic stack allocation which is non standard and
// causes memory violation problems in the WASM interpreter
// instead of writing, for instance, uint8_t buffer[size];
// the following idiom is used
// local<uint8_t> buffer_l(size); uint8_t *buffer = buffer_l.data;
template<typename T>
class local {
public:
    T *data = nullptr;
    local(uint64_t size) { data = _new<T>(size); }
    ~local() { _delete(data); }
};

// handy min/max functions
static inline uint64_t _min(uint64_t v1, uint64_t v2) { return v1 < v2 ? v1 : v2; }
static inline uint64_t _max(uint64_t v1, uint64_t v2) { return v1 > v2 ? v1 : v2; }

// ** bigint **

// a class to support arbitrary length unsigned integers
// used in the implementation of BIGMODEXP and ECDSA calculations
class bigint {
private:
    uint64_t W = 0; // number of 32-bit words
    uint64_t capacity = 0; // capacity in 32-bit words
    uint32_t *data = nullptr; // word array holding the bignum (little endian)
    // ensures there is room for somany 32-bit words
    void ensure(uint64_t size) {
        if (W >= size) return;
        if (capacity >= size) {
            for (uint64_t i = W; i < size; i++) data[i] = 0;
            W = size;
            return;
        }
        uint32_t *new_data = _new<uint32_t>(size);
        for (uint64_t i = 0; i < W; i++) new_data[i] = data[i];
        for (uint64_t i = W; i < size; i++) new_data[i] = 0;
        _delete(data);
        data = new_data;
        capacity = size;
        W = size;
    }
    // compacts the number removing leading zeros
    void pack() { while (W > 0 && data[W-1] == 0) W--; }
    // number comparison
    int cmp(const bigint& v) const {
        uint64_t _W = W < v.W ? W : v.W;
        for (uint64_t i = v.W; i > _W; i--) {
            if (0 < v.data[i-1]) return -1;
        }
        for (uint64_t i = W; i > _W; i--) {
            if (data[i-1] > 0) return 1;
        }
        for (uint64_t i = _W; i > 0; i--) {
            if (data[i-1] < v.data[i-1]) return -1;
            if (data[i-1] > v.data[i-1]) return 1;
        }
        return 0;
    }
public:
    bigint() {}
    ~bigint() { _delete(data); }
    bigint(uint64_t v) { ensure(2); data[0] = v; data[1] = v >> 32; }
    bigint(const bigint &v) {
        ensure(v.W);
        for (uint64_t i = 0; i < v.W; i++) data[i] = v.data[i];
    }
    bigint& operator=(const bigint& v) {
        ensure(v.W);
        for (uint64_t i = 0; i < v.W; i++) data[i] = v.data[i];
        for (uint64_t i = v.W; i < W; i++) data[i] = 0;
        return *this;
    }
    uint64_t bitlen() const {
        for (uint64_t i = 32 * W; i > 0; i--) {
            if (bit(i - 1)) return i;
        }
        return 0;
    }
    uint64_t cast64() const {
        uint64_t _W = W;
        while (_W > 0 && data[_W-1] == 0) _W--;
        assert(_W <= 2);
        return 0
            | (uint64_t)(W > 1 ? data[1] : 0) << 32
            | (uint64_t)(W > 0 ? data[0] : 0);
    }
    inline bool bit(uint64_t index) const {
        uint64_t i = index / 32;
        uint64_t j = index % 32;
        if (i >= W) return false;
        return (data[i] & (1 << j)) > 0;
    }
    bigint& operator++() {
        if (W == 0) ensure(1);
        ensure(data[W-1] == 0xffffffff ? W+1 : W);
        for (uint64_t i = 0; i < W; i++) {
            if (++data[i] != 0) break;
        }
        return *this;
    }
    bigint& operator--() {
        assert(*this > 0);
        for (uint64_t i = 0; i < W; i++) {
            if (data[i]-- != 0) break;
        }
        return *this;
    }
    const bigint operator++(int) { const bigint v = *this; ++(*this); return v; }
    const bigint operator--(int) { const bigint v = *this; --(*this); return v; }
    bigint& operator+=(const bigint& v)
    {
        ensure(_max(W, v.W) + 1);
        uint64_t carry = 0;
        for (uint64_t i = 0; i < v.W; i++) {
            uint64_t n = data[i] + (v.data[i] + carry);
            data[i] = n & 0xffffffff;
            carry = n >> 32;
        }
        for (uint64_t i = v.W; i < W; i++) {
            if (carry == 0) break;
            uint64_t n = data[i] + carry;
            data[i] = n & 0xffffffff;
            carry = n >> 32;
        }
        pack();
        return *this;
    }
    bigint& operator-=(const bigint& v) {
        assert(*this >= v);
        bigint t = v;
        t.ensure(W);
        uint64_t _W = W;
        for (uint64_t i = 0; i < t.W; i++) t.data[i] = ~t.data[i];
        t++;
        *this += t;
        for (uint64_t i = _W; i < W; i++) data[i] = 0;
        pack();
        return *this;
    }
    bigint& operator*=(const bigint& v) {
        uint64_t _W = W + v.W;
        ensure(_W);
        bigint t = *this;
        *this = 0;
        for (uint64_t j = 0; j < v.W; j++) {
            uint64_t base = v.data[j];
            if (base == 0) continue;
            uint64_t carry = 0;
            for (uint64_t i = j; i < _W; i++) {
                uint64_t n = data[i] + base * t.data[i-j] + carry;
                data[i] = n & 0xffffffff;
                carry = n >> 32;
            }
        }
        pack();
        return *this;
    }
    bigint& operator/=(const bigint& v) { bigint t1 = *this, t2; quorem(t1, v, *this, t2); return *this; }
    bigint& operator%=(const bigint& v) { bigint t1 = *this, t2; quorem(t1, v, t2, *this); return *this; }
    bigint& operator&=(const bigint& v) {
        ensure(v.W);
        for (uint64_t i = 0; i < v.W; i++) data[i] &= v.data[i];
        for (uint64_t i = v.W; i < W; i++) data[i] = 0;
        W = v.W;
        pack();
        return *this;
    }
    bigint& operator|=(const bigint& v) { ensure(v.W); for (uint64_t i = 0; i < v.W; i++) data[i] |= v.data[i]; pack(); return *this; }
    bigint& operator^=(const bigint& v) { ensure(v.W); for (uint64_t i = 0; i < v.W; i++) data[i] ^= v.data[i]; pack(); return *this; }
    bigint& operator<<=(uint64_t n) {
        if (n == 0) return *this;
        ensure(W + (n + 31) / 32);
        uint64_t index = n / 32;
        uint64_t shift = n % 32;
        for (uint64_t i = W; i > 0; i--) {
            uint32_t w = 0;
            if (i > index) w |= data[i - index - 1] << shift;
            if (i > index + 1 && shift > 0) w |= data[i - index - 2] >> (32 - shift);
            data[i - 1] = w;
        }
        pack();
        return *this;
    }
    bigint& operator>>=(uint64_t n) {
        if (n == 0) return *this;
        uint64_t index = n / 32;
        uint64_t shift = n % 32;
        for (uint64_t i = 0; i < W; i++) {
            uint32_t w = 0;
            if (W > i + index) w |= data[i + index] >> shift;
            if (W > i + index + 1 && shift > 0) w |= data[i + index + 1] << (32 - shift);
            data[i] = w;
        }
        pack();
        return *this;
    }
    static void quorem(const bigint &num, const bigint &div, bigint &quo, bigint &rem) {
        assert(div > 0);
        quo = 0;
        rem = num;
        uint64_t shift = 0;
        bigint _num = num;
        bigint _div = div;
        _div.ensure(_num.W);
        while (_div <= _num) {
            _div <<= 32;
            shift += 32;
        }
        if (shift == 0) return;
        quo.ensure((shift + 31) / 32);
        while (shift+1 > 0) {
            if (_num >= _div) {
                _num -= _div;
                int i = shift / 32;
                int j = shift % 32;
                quo.data[i] |= 1 << j;
            }
            _div >>= 1;
            shift--;
        }
        rem = _num;
        quo.pack();
        rem.pack();
    }
    static const bigint pow(const bigint &v1, const bigint &v2) {
        bigint v0 = v2;
        v0.pack();
        bigint x1 = 1;
        bigint x2 = v1;
        for (uint64_t n = 32*v0.W; n > 0; n--) {
            x1 *= x1;
            if (v0.bit(n - 1)) x1 *= x2;
        }
        return x1;
    }
    static const bigint powmod(const bigint &v1, const bigint &v2, const bigint &v3) {
        bigint v0 = v2;
        v0.pack();
        bigint x1 = 1;
        bigint x2 = v1;
        for (uint64_t i = 32*v0.W; i > 0; i--) {
            x1 = mulmod(x1, x1, v3);
            if (v2.bit(i - 1)) x1 = mulmod(x1, x2, v3);
        }
        return x1 % v3;
    }
    static const bigint addmod(const bigint &v1, const bigint &v2, const bigint &v3) { return (v1 + v2) % v3; }
    static const bigint mulmod(const bigint &v1, const bigint &v2, const bigint &v3) { return (v1 * v2) % v3; }
    friend const bigint operator+(const bigint& v1, const bigint& v2) { return bigint(v1) += v2; }
    friend const bigint operator-(const bigint& v1, const bigint& v2) { return bigint(v1) -= v2; }
    friend const bigint operator*(const bigint& v1, const bigint& v2) { return bigint(v1) *= v2; }
    friend const bigint operator/(const bigint& v1, const bigint& v2) { return bigint(v1) /= v2; }
    friend const bigint operator%(const bigint& v1, const bigint& v2) { return bigint(v1) %= v2; }
    friend const bigint operator&(const bigint& v1, const bigint& v2) { return bigint(v1) &= v2; }
    friend const bigint operator|(const bigint& v1, const bigint& v2) { return bigint(v1) |= v2; }
    friend const bigint operator^(const bigint& v1, const bigint& v2) { return bigint(v1) ^= v2; }
    friend const bigint operator<<(const bigint& v, int n) { return bigint(v) <<= n; }
    friend const bigint operator>>(const bigint& v, int n) { return bigint(v) >>= n; }
    friend bool operator==(const bigint& v1, const bigint& v2) { return v1.cmp(v2) == 0; }
    friend bool operator!=(const bigint& v1, const bigint& v2) { return v1.cmp(v2) != 0; }
    friend bool operator<(const bigint& v1, const bigint& v2) { return v1.cmp(v2) < 0; }
    friend bool operator>(const bigint& v1, const bigint& v2) { return v1.cmp(v2) > 0; }
    friend bool operator<=(const bigint& v1, const bigint& v2) { return v1.cmp(v2) <= 0; }
    friend bool operator>=(const bigint& v1, const bigint& v2) { return v1.cmp(v2) >= 0; }
    static const bigint from(const uint8_t *buffer, uint64_t size) {
        bigint v = 0;
        v.ensure((size + 3) / 4);
        for (uint64_t j = 0; j < size; j++) {
            uint64_t i = size - (j + 1);
            uint64_t x = i / 4;
            uint64_t y = i % 4;
            v.data[x] |= buffer[j] << 8*y;
        }
        return v;
    }
    static void to(const bigint &v, uint8_t *buffer, uint64_t size) {
        uint64_t B = _min(size, 4*v.W);
        for (uint64_t j = 0; j < size-B; j++) buffer[j] = 0;
        for (uint64_t j = size-B; j < size; j++) {
            uint64_t i = size - (j + 1);
            uint64_t x = i / 4;
            uint64_t y = i % 4;
            buffer[j] = (v.data[x] >> 8*y) & 0xff;
        }
    }
#ifndef NDEBUG
    friend std::ostream& operator<<(std::ostream &os, const bigint &v) {
        for (uint64_t i = v.W; i > 0; i--) {
            os << std::hex << std::setw(8) << std::setfill('0') << v.data[i-1];
        }
        if (v.W == 0) {
            os << std::hex << std::setw(8) << std::setfill('0') << 0;
        }
        return os;
    }
#endif // NDEBUG
};

// reads bigint from decimal string
static bigint big(const char *s)
{
    bigint t = 0;
    for (uint64_t i = 0; s[i] != '\0'; i++) {
        assert(s[i] >= '0' && s[i] <= '9');
        t = 10 * t + (s[i] - '0');
    }
    return t;
}

#ifdef NATIVE_CRYPTO
static bigint bigmodexp(const bigint& base, const bigint& exp, const bigint& mod);
#else
static bigint bigmodexp(const bigint& base, const bigint& exp, const bigint& mod)
{
    return bigint::powmod(base, exp, mod);
}
#endif // NATIVE_CRYPTO

// ** U<N> **

// provides a fixed length, multiple of 32-bit, n-bits unsigned integer
// implemented as a recursive template for best compiler optimization
// it has two base cases, 32-bit and 64-bit
// used in most bytecode interpreter calculations
// N is the size in bits, assumed to be a multiple of 32-bit
template <int N>
struct U {
    static constexpr int L = 32*((N/32)/2); // rounds down the size of the lower word
    static constexpr int H = N - L; // higher word is the remaining
    U<L> lo; // lower word defined recursivelly (little endian)
    U<H> hi; // higher word, ditto
    inline U() {}
    U(uint64_t v) : lo(v), hi(0) {}
    U(const U<L>& _lo, const U<H>& _hi) : lo(_lo), hi(_hi) {}
    template<int M> U(const U<M>& v) : U<N>(v, 0) {}
    template<int M> U(const U<M>& v, uint64_t base) : lo(v, base), hi(v, base + L/32) {}

    // the following list explicitly call class methods instead of implementing them
    // this was required to avoid implicit compiler resolution of operators internally
    // which led to undesired/unexpected recursion when resolving ambiguity
    inline U operator-() const { return U<N>::neg(*this); }
    inline U operator~() const { return U<N>::lno(*this); }

    inline U operator++(int) { return U<N>::icp(*this); }
    inline U operator--(int) { return U<N>::dcp(*this); }

    inline U& operator++() { return U<N>::_pic(*this); }
    inline U& operator--() { return U<N>::_pdc(*this); }

    inline U& operator=(const U& v) { return U<N>::_cpy(*this, v); }

    inline U& operator+=(const U& v) { return U<N>::_add(*this, v); }
    inline U& operator-=(const U& v) { return U<N>::_sub(*this, v); }
    inline U& operator*=(const U& v) { return U<N>::_mul(*this, v); }
    inline U& operator/=(const U& v) { return U<N>::_div(*this, v); }
    inline U& operator%=(const U& v) { return U<N>::_mod(*this, v); }
    inline U& operator&=(const U& v) { return U<N>::_lan(*this, v); }
    inline U& operator|=(const U& v) { return U<N>::_lor(*this, v); }
    inline U& operator^=(const U& v) { return U<N>::_lxr(*this, v); }

    inline U& operator=(uint64_t v) { return U<N>::_cpy(*this, v); }

    inline U& operator+=(uint64_t v) { return U<N>::_add(*this, v); }
    inline U& operator-=(uint64_t v) { return U<N>::_sub(*this, v); }
    inline U& operator*=(uint64_t v) { return U<N>::_mul(*this, v); }
    inline U& operator/=(uint64_t v) { return U<N>::_div(*this, v); }
    inline U& operator%=(uint64_t v) { return U<N>::_mod(*this, v); }
    inline U& operator&=(uint64_t v) { return U<N>::_lan(*this, v); }
    inline U& operator|=(uint64_t v) { return U<N>::_lor(*this, v); }
    inline U& operator^=(uint64_t v) { return U<N>::_lxr(*this, v); }

    inline U& operator<<=(uint64_t k) { return U<N>::_shl(*this, k); }
    inline U& operator>>=(uint64_t k) { return U<N>::_shr(*this, k); }

    friend inline bool operator==(const U& v1, const U& v2) { return U<N>::equ(v1, v2); }
    friend inline bool operator!=(const U& v1, const U& v2) { return U<N>::neq(v1, v2); }
    friend inline bool operator<(const U& v1, const U& v2) { return U<N>::ltn(v1, v2); }
    friend inline bool operator<=(const U& v1, const U& v2) { return U<N>::lte(v1, v2); }
    friend inline bool operator>(const U& v1, const U& v2) { return U<N>::gtn(v1, v2); }
    friend inline bool operator>=(const U& v1, const U& v2) { return U<N>::gte(v1, v2); }

    friend inline U operator+(const U& v1, const U& v2) { return U<N>::add(v1, v2); }
    friend inline U operator-(const U& v1, const U& v2) { return U<N>::sub(v1, v2); }
    friend inline U operator*(const U& v1, const U& v2) { return U<N>::mul(v1, v2); }
    friend inline U operator/(const U& v1, const U& v2) { return U<N>::div(v1, v2); }
    friend inline U operator%(const U& v1, const U& v2) { return U<N>::mod(v1, v2); }
    friend inline U operator&(const U& v1, const U& v2) { return U<N>::lan(v1, v2); }
    friend inline U operator|(const U& v1, const U& v2) { return U<N>::lor(v1, v2); }
    friend inline U operator^(const U& v1, const U& v2) { return U<N>::lxr(v1, v2); }

    friend inline bool operator==(uint64_t v1, const U& v2) { return U<N>::equ(v1, v2); }
    friend inline bool operator!=(uint64_t v1, const U& v2) { return U<N>::neq(v1, v2); }
    friend inline bool operator<(uint64_t v1, const U& v2) { return U<N>::ltn(v1, v2); }
    friend inline bool operator<=(uint64_t v1, const U& v2) { return U<N>::lte(v1, v2); }
    friend inline bool operator>(uint64_t v1, const U& v2) { return U<N>::gtn(v1, v2); }
    friend inline bool operator>=(uint64_t v1, const U& v2) { return U<N>::gte(v1, v2); }

    friend inline U operator+(uint64_t v1, const U& v2) { return U<N>::add(v1, v2); }
    friend inline U operator-(uint64_t v1, const U& v2) { return U<N>::sub(v1, v2); }
    friend inline U operator*(uint64_t v1, const U& v2) { return U<N>::mul(v1, v2); }
    friend inline U operator/(uint64_t v1, const U& v2) { return U<N>::div(v1, v2); }
    friend inline U operator%(uint64_t v1, const U& v2) { return U<N>::mod(v1, v2); }
    friend inline U operator&(uint64_t v1, const U& v2) { return U<N>::lan(v1, v2); }
    friend inline U operator|(uint64_t v1, const U& v2) { return U<N>::lor(v1, v2); }
    friend inline U operator^(uint64_t v1, const U& v2) { return U<N>::lxr(v1, v2); }

    friend inline bool operator==(const U& v1, uint64_t v2) { return U<N>::equ(v1, v2); }
    friend inline bool operator!=(const U& v1, uint64_t v2) { return U<N>::neq(v1, v2); }
    friend inline bool operator<(const U& v1, uint64_t v2) { return U<N>::ltn(v1, v2); }
    friend inline bool operator<=(const U& v1, uint64_t v2) { return U<N>::lte(v1, v2); }
    friend inline bool operator>(const U& v1, uint64_t v2) { return U<N>::gtn(v1, v2); }
    friend inline bool operator>=(const U& v1, uint64_t v2) { return U<N>::gte(v1, v2); }

    friend inline U operator+(const U& v1, uint64_t v2) { return U<N>::add(v1, v2); }
    friend inline U operator-(const U& v1, uint64_t v2) { return U<N>::sub(v1, v2); }
    friend inline U operator*(const U& v1, uint64_t v2) { return U<N>::mul(v1, v2); }
    friend inline U operator/(const U& v1, uint64_t v2) { return U<N>::div(v1, v2); }
    friend inline U operator%(const U& v1, uint64_t v2) { return U<N>::mod(v1, v2); }
    friend inline U operator&(const U& v1, uint64_t v2) { return U<N>::lan(v1, v2); }
    friend inline U operator|(const U& v1, uint64_t v2) { return U<N>::lor(v1, v2); }
    friend inline U operator^(const U& v1, uint64_t v2) { return U<N>::lxr(v1, v2); }

    friend inline U operator<<(const U& v, uint64_t k) { return U<N>::shl(v, k); }
    friend inline U operator>>(const U& v, uint64_t k) { return U<N>::shr(v, k); }

    // the actual implementation starts here
    // every operation explicitly states the typing os the operators to avoid
    // ambiguity and misleading operator resolution by the compiler
    // this is done internally only
    static U neg(const U& v) { U<N> t(U<N>::lno(v)); U<N>::_pic(t); return t; }
    static U lno(const U& v) { return U<N>{U<L>::lno(v.lo), U<H>::lno(v.hi)}; }

    static U icp(U& v) { U<N> t(v); U<N>::_pic(v); return t; }
    static U dcp(U& v) { U<N> t(v); U<N>::_pdc(v); return t; }

    static U& _pic(U& v) { U<L>::_pic(v.lo); if (U<L>::equ(v.lo, 0)) U<H>::_pic(v.hi); return v; }
    static U& _pdc(U& v) { if (U<L>::equ(v.lo, 0)) U<H>::_pdc(v.hi); U<L>::_pdc(v.lo); return v; }

    static U& _cpy(U& v1, const U& v2) { U<L>::_cpy(v1.lo, v2.lo); U<H>::_cpy(v1.hi, v2.hi); return v1; }

    static U& _add(U& v1, const U& v2) { U<L>::_add(v1.lo, v2.lo); U<H>::_add(v1.hi, v2.hi); if (U<L>::ltn(v1.lo, v2.lo)) U<H>::_pic(v1.hi); return v1; }
    static U& _sub(U& v1, const U& v2) { U<L> t = v1.lo; U<L>::_sub(v1.lo, v2.lo); U<H>::_sub(v1.hi, v2.hi); if (U<L>::gtn(v1.lo, t)) U<H>::_pdc(v1.hi); return v1; }
    static U& _mul(U& v1, const U& v2) { v1 = U<N>::mul_(v1, v2); return v1; }
    static U& _div(U& v1, const U& v2) { U<N> quo, rem; quorem(v1, v2, quo, rem); v1 = quo; return v1; }
    static U& _mod(U& v1, const U& v2) { U<N> quo, rem; quorem(v1, v2, quo, rem); v1 = rem; return v1; }
    static U& _lan(U& v1, const U& v2) { U<L>::_lan(v1.lo, v2.lo); U<H>::_lan(v1.hi, v2.hi); return v1; }
    static U& _lor(U& v1, const U& v2) { U<L>::_lor(v1.lo, v2.lo); U<H>::_lor(v1.hi, v2.hi); return v1; }
    static U& _lxr(U& v1, const U& v2) { U<L>::_lxr(v1.lo, v2.lo); U<H>::_lxr(v1.hi, v2.hi); return v1; }

    static U& _cpy(U& v1, uint64_t v2) { U<L>::_cpy(v1.lo, v2); U<H>::_cpy(v1.hi, 0); return v1; }

    static U& _add(U& v1, uint64_t v2) { U<L>::_add(v1.lo, v2); if (U<L>::ltn(v1.lo, v2)) U<H>::_pic(v1.hi); return v1; }
    static U& _sub(U& v1, uint64_t v2) { U<L> t = v1.lo; U<L>::_sub(v1.lo, v2); if (U<L>::gtn(v1.lo, t)) U<H>::_pdc(v1.hi); return v1; }
    static U& _mul(U& v1, uint64_t v2) { v1 = U<N>::mul_(v1, v2); return v1; }
    static U& _div(U& v1, uint64_t v2) { U<N> quo, rem, v = v2; quorem(v1, v, quo, rem); v1 = quo; return v1; }
    static U& _mod(U& v1, uint64_t v2) { U<N> quo, rem, v = v2; quorem(v1, v, quo, rem); v1 = rem; return v1; }
    static U& _lan(U& v1, uint64_t v2) { U<L>::_lan(v1.lo, v2); U<H>::_cpy(v1.hi, 0); return v1; }
    static U& _lor(U& v1, uint64_t v2) { U<L>::_lor(v1.lo, v2); return v1; }
    static U& _lxr(U& v1, uint64_t v2) { U<L>::_lxr(v1.lo, v2); return v1; }

    static U& _shl(U& v, uint64_t k) { v = U<N>::shl(v, k); return v; }
    static U& _shr(U& v, uint64_t k) { v = U<N>::shr(v, k); return v; }

    static bool equ(const U& v1, const U& v2) { return U<L>::equ(v1.lo, v2.lo) && U<H>::equ(v1.hi, v2.hi); }
    static bool neq(const U& v1, const U& v2) { return U<L>::neq(v1.lo, v2.lo) || U<H>::neq(v1.hi, v2.hi); }
    static bool ltn(const U& v1, const U& v2) { return U<H>::ltn(v1.hi, v2.hi) || (U<H>::equ(v1.hi, v2.hi) && U<L>::ltn(v1.lo, v2.lo)); }
    static bool lte(const U& v1, const U& v2) { return U<H>::ltn(v1.hi, v2.hi) || (U<H>::equ(v1.hi, v2.hi) && U<L>::lte(v1.lo, v2.lo)); }
    static bool gtn(const U& v1, const U& v2) { return U<H>::gtn(v1.hi, v2.hi) || (U<H>::equ(v1.hi, v2.hi) && U<L>::gtn(v1.lo, v2.lo)); }
    static bool gte(const U& v1, const U& v2) { return U<H>::gtn(v1.hi, v2.hi) || (U<H>::equ(v1.hi, v2.hi) && U<L>::gte(v1.lo, v2.lo)); }

    static U add(const U& v1, const U& v2) { U<L> lo = U<L>::add(v1.lo, v2.lo); U<H> hi = U<H>::add(v1.hi, v2.hi); if (U<L>::ltn(lo, v1.lo)) U<H>::_pic(hi); return U<N>{lo, hi}; }
    static U sub(const U& v1, const U& v2) { U<L> lo = U<L>::sub(v1.lo, v2.lo); U<H> hi = U<H>::sub(v1.hi, v2.hi); if (U<L>::gtn(lo, v1.lo)) U<H>::_pdc(hi); return U<N>{lo, hi}; }
    static U mul(const U& v1, const U& v2) { return U<N>::mul_(v1, v2); }
    static U div(const U& v1, const U& v2) { U<N> quo, rem; quorem(v1, v2, quo, rem); return quo; }
    static U mod(const U& v1, const U& v2) { U<N> quo, rem; quorem(v1, v2, quo, rem); return rem; }
    static U lan(const U& v1, const U& v2) { return U<N>{U<L>::lan(v1.lo, v2.lo), U<H>::lan(v1.hi, v2.hi)}; }
    static U lor(const U& v1, const U& v2) { return U<N>{U<L>::lor(v1.lo, v2.lo), U<H>::lor(v1.hi, v2.hi)}; }
    static U lxr(const U& v1, const U& v2) { return U<N>{U<L>::lxr(v1.lo, v2.lo), U<H>::lxr(v1.hi, v2.hi)}; }

    static bool equ(uint64_t v1, const U& v2) { return U<L>::equ(v1, v2.lo) && U<H>::equ(0, v2.hi); }
    static bool neq(uint64_t v1, const U& v2) { return U<L>::neq(v1, v2.lo) || U<H>::neq(0, v2.hi); }
    static bool ltn(uint64_t v1, const U& v2) { return U<H>::neq(0, v2.hi) || U<L>::ltn(v1, v2.lo); }
    static bool lte(uint64_t v1, const U& v2) { return U<H>::neq(0, v2.hi) || U<L>::lte(v1, v2.lo); }
    static bool gtn(uint64_t v1, const U& v2) { return U<H>::equ(0, v2.hi) && U<L>::gtn(v1, v2.lo); }
    static bool gte(uint64_t v1, const U& v2) { return U<H>::equ(0, v2.hi) && U<L>::gte(v1, v2.lo); }

    static U add(uint64_t v1, const U& v2) { U<L> lo = U<L>::add(v1, v2.lo); U<H> hi = v2.hi; if (U<L>::ltn(lo, v1)) U<H>::_pic(hi); return U<N>{lo, hi}; }
    static U sub(uint64_t v1, const U& v2) { U<L> lo = U<L>::sub(v1, v2.lo); U<H> hi = v2.hi; if (U<L>::gtn(lo, v1)) U<H>::_pdc(hi); return U<N>{lo, hi}; }
    static U mul(uint64_t v1, const U& v2) { return U<N>::mul_(v1, v2); }
    static U div(uint64_t v1, const U& v2) { U<N> quo, rem, v = v1; quorem(v, v2, quo, rem); return quo; }
    static U mod(uint64_t v1, const U& v2) { U<N> quo, rem, v = v1; quorem(v, v2, quo, rem); return rem; }
    static U lan(uint64_t v1, const U& v2) { return U<N>{U<L>::lan(v1, v2.lo), U<H>(0)}; }
    static U lor(uint64_t v1, const U& v2) { return U<N>{U<L>::lor(v1, v2.lo), v2.hi}; }
    static U lxr(uint64_t v1, const U& v2) { return U<N>{U<L>::lxr(v1, v2.lo), v2.hi}; }

    static bool equ(const U& v1, uint64_t v2) { return U<L>::equ(v1.lo, v2) && U<H>::equ(v1.hi, 0); }
    static bool neq(const U& v1, uint64_t v2) { return U<L>::neq(v1.lo, v2) || U<H>::neq(v1.hi, 0); }
    static bool ltn(const U& v1, uint64_t v2) { return U<H>::equ(v1.hi, 0) && U<L>::ltn(v1.lo, v2); }
    static bool lte(const U& v1, uint64_t v2) { return U<H>::equ(v1.hi, 0) && U<L>::lte(v1.lo, v2); }
    static bool gtn(const U& v1, uint64_t v2) { return U<H>::neq(v1.hi, 0) || U<L>::gtn(v1.lo, v2); }
    static bool gte(const U& v1, uint64_t v2) { return U<H>::neq(v1.hi, 0) || U<L>::gte(v1.lo, v2); }

    static U add(const U& v1, uint64_t v2) { U<L> lo = U<L>::add(v1.lo, v2); U<H> hi = v1.hi; if (U<L>::ltn(lo, v1.lo)) U<H>::_pic(hi); return U<N>{lo, hi}; }
    static U sub(const U& v1, uint64_t v2) { U<L> lo = U<L>::sub(v1.lo, v2); U<H> hi = v1.hi; if (U<L>::gtn(lo, v1.lo)) U<H>::_pdc(hi); return U<N>{lo, hi}; }
    static U mul(const U& v1, uint64_t v2) { return U<N>::mul_(v1, v2); }
    static U div(const U& v1, uint64_t v2) { U<N> quo, rem, v = v2; quorem(v1, v, quo, rem); return quo; }
    static U mod(const U& v1, uint64_t v2) { U<N> quo, rem, v = v2; quorem(v1, v, quo, rem); return rem; }
    static U lan(const U& v1, uint64_t v2) { return U<N>{U<L>::lan(v1.lo, v2), U<H>(0)}; }
    static U lor(const U& v1, uint64_t v2) { return U<N>{U<L>::lor(v1.lo, v2), v1.hi}; }
    static U lxr(const U& v1, uint64_t v2) { return U<N>{U<L>::lxr(v1.lo, v2), v1.hi}; }

    static U shl(const U& v, uint64_t k) {
        assert(k < N);
        if (k == 0) return v;
        if (k < L) return U<N>{U<L>::shl(v.lo, k), U<H>::lor(U<H>::shl(v.hi, k), U<H>(U<L>::shr(v.lo, L - k)))};
        if (k < H) return U<N>{U<L>(0), U<H>::lor(U<H>::shl(v.hi, k), U<H>::shl(U<H>(v.lo), k - L))};
        return U<N>{0, U<H>::shl(U<H>(v.lo), k - L)};
    }
    static U shr(const U& v, uint64_t k) {
        assert(k < N);
        if (k == 0) return v;
        if (k < L) return U<N>{U<L>::lor(U<L>::shr(v.lo, k), U<L>::shl(U<L>(v.hi), L - k)), U<H>::shr(v.hi, k)};
        if (k < H) return U<N>{U<L>(U<H>::shr(v.hi, k - L)), U<H>::shr(v.hi, k)};
        return U<N>{U<L>(U<H>::shr(v.hi, k - L)), U<H>(0)};
    }
    static U sar(const U& v, uint64_t k) {
        assert(k < N);
        if (k == 0) return v;
        if (k < L) return U<N>{U<L>::lor(U<L>::shr(v.lo, k), U<L>::shl(U<L>(v.hi), L - k)), U<H>::sar(v.hi, k)};
        if (k < H) return U<N>{U<L>(U<H>::shr(v.hi, k - L)), U<H>::sar(v.hi, k)};
        return U<N>{U<L>(U<H>::sar(v.hi, k - L)), v.hi.bit(H - 1) ? ~U<H>(0) : U<H>(0)};
    }

    // multiplication with double precision result
    static U muc(const U& v1, const U& v2, U& v3) {
        U<L> z0_hi;
        U<L> z0_lo = U<L>::muc(v1.lo, v2.lo, z0_hi);
        U<H> z1_hi, z2_hi, z3_hi;
        U<H> z1_lo = U<H>::muc(U<H>(v1.lo), v2.hi, z1_hi);
        U<H> z2_lo = U<H>::muc(v1.hi, U<H>(v2.lo), z2_hi);
        U<H> z3_lo = U<H>::muc(v1.hi, v2.hi, z3_hi);
        U<2*N> t0 = U<2*N>{U<N>{z0_lo, U<H>(z0_hi)}, U<N>{z3_lo, z3_hi}};
        U<2*N>::_add(t0, U<2*N>{U<N>{0, U<H>(z1_lo)}, U<N>{z1_hi, 0}});
        U<2*N>::_add(t0, U<2*N>{U<N>{0, U<H>(z2_lo)}, U<N>{z2_hi, 0}});
        v3 = t0.hi;
        return t0.lo;
    }
    static U muc(uint64_t v1, const U& v2, U& v3) {
        U<L> z0_hi, z1_hi;
        U<L> z0_lo = U<L>::muc(v1, v2.lo, z0_hi);
        U<H> z1_lo = U<L>::muc(v1, v2.hi, z1_hi);
        U<2*N> t0 = U<2*N>{U<N>{z0_lo, z0_hi}, 0};
        U<2*N>::_add(t0, U<2*N>{U<N>{0, z1_lo}, U<N>{z1_hi, 0}});
        v3 = t0.hi;
        return t0.lo;
    }
    static U muc(const U& v1, uint64_t v2, U& v3) {
        U<L> z0_hi;
        U<L> z0_lo = U<L>::muc(v1.lo, v2, z0_hi);
        U<H> z2_hi;
        U<H> z2_lo = U<L>::muc(v1.hi, v2, z2_hi);
        U<2*N> t0 = U<2*N>{U<N>{z0_lo, z0_hi}, 0};
        U<2*N>::_add(t0, U<2*N>{U<N>{0, z2_lo}, U<N>{z2_hi, 0}});
        v3 = t0.hi;
        return t0.lo;
    }

    // multiplication used internally
    // implemented separated from the reamaining operations for readability
    static U mul_(const U& v1, const U& v2) {
        U<L> z0_hi;
        U<L> z0_lo = U<L>::muc(v1.lo, v2.lo, z0_hi);
        U<H> z0_hi_(z0_hi);
        U<H>::_add(z0_hi_, U<H>::mul_(U<H>(v1.lo), v2.hi));
        U<H>::_add(z0_hi_, U<H>::mul_(v1.hi, U<H>(v2.lo)));
        return U<N>{z0_lo, z0_hi_};
    }
    static U mul_(uint64_t v1, const U& v2) {
        U<L> z0_hi;
        U<L> z0_lo = U<L>::muc(v1, v2.lo, z0_hi);
        U<H> z0_hi_(z0_hi);
        U<H>::_add(z0_hi_, U<H>::mul_(v1, v2.hi));
        return U<N>{z0_lo, z0_hi_};
    }
    static U mul_(const U& v1, uint64_t v2) {
        U<L> z0_hi;
        U<L> z0_lo = U<L>::muc(v1.lo, v2, z0_hi);
        U<H> z0_hi_(z0_hi);
        U<H>::_add(z0_hi_, U<H>::mul_(v1.hi, v2));
        return U<N>{z0_lo, z0_hi_};
    }

    static const U pow(const U& v1, const U& v2) {
        U<N> x1 = 1;
        U<N> x2 = v1;
        for (uint64_t i = v2.bitlen(); i > 0; i--) {
            U<N>::_mul(x1, x1);
            if (v2.bit(i - 1)) U<N>::_mul(x1, x2);
        }
        return x1;
    }

    static void quorem(const U &num, const U &div, U &quo, U &rem) {
        assert(div > 0);
        quo = 0;
        rem = num;
        uint64_t num_bitlen = num.bitlen();
        uint64_t div_bitlen = div.bitlen();
        if (div_bitlen > num_bitlen) return;
        uint64_t shift = num_bitlen - div_bitlen;
        U<N> _div = U<N>::shl(div, shift);
        while (shift + 1 > 0) {
            if (U<N>::gte(rem, _div)) {
                U<N>::_sub(rem, _div);
                quo.setbit(shift);
            }
            U<N>::_shr(_div, 1);
            shift--;
        }
    }

    static U addmod(const U& v1, const U& v2, const U& v3) {
        return U<N>(U<N+32>::mod(U<N+32>::add(U<N+32>(v1), U<N+32>(v2)), U<N+32>(v3)));
    }

    static U mulmod(const U& v1, const U& v2, const U& v3) {
        return U<N>(U<2*N>::mod(U<2*N>::mul(U<2*N>(v1), U<2*N>(v2)), U<2*N>(v3)));
    }

    static U powmod(const U& v1, const U& v2, const U& v3) {
        U<2*N> x1 = 1;
        U<2*N> x2 = v1;
        U<2*N> x3 = v3;
        for (uint64_t i = v2.bitlen(); i > 0; i--) {
            x1 = U<2*N>::mod(U<2*N>::mul(x1, x1), x3);
            if (v2.bit(i - 1)) x1 = U<2*N>::mod(U<2*N>::mul(x1, x2), x3);
        }
        return U<N>(U<2*N>::mod(x1, x3));
    }

    // does not deal properly with N = 96, when the lower word is only 32-bits
    // which is not necessary for this implementation
    // given that all instances have at least 128-bit which always
    // results in a lower word of 64-bits
    uint64_t cast64() const { assert(U<H>::equ(hi, 0)); return lo.cast64(); }

    bool bit(uint64_t k) const { assert(k < N); return k < L ? lo.bit(k) : hi.bit(k - L); }
    void setbit(uint64_t k) { assert(k < N); k < L ? lo.setbit(k) : hi.setbit(k - L); }
    void clrbit(uint64_t k) { assert(k < N); k < L ? lo.clrbit(k) : hi.clrbit(k - L); }

    uint8_t byte(uint64_t k) const { assert(k < N/8); return k < L/8 ? lo.byte(k) : hi.byte(k - L/8); }
    void setbyte(uint64_t k, uint8_t v) { assert(k < N/8); k < L/8 ? lo.setbyte(k, v) : hi.setbyte(k - L/8, v); }

    uint32_t word(uint64_t k) const { assert(k < N/32); return k < L/32 ? lo.word(k) : hi.word(k - L/32); }
    void setword(uint64_t k, uint32_t v) { assert(k < N/32); k < L/32 ? lo.setword(k, v) : hi.setword(k - L/32, v); }

    uint64_t bitlen() const { uint64_t len = hi.bitlen(); return len > 0 ? len + L : lo.bitlen(); }
    uint64_t bytelen() const { uint64_t len = hi.bytelen(); return len > 0 ? len + (L/8) : lo.bytelen(); }
    uint64_t wordlen() const { uint64_t len = hi.wordlen(); return len > 0 ? len + (L/32) : lo.wordlen(); }

    // flips the most significant bit
    U signflip() { return U{lo, hi.signflip()}; }

    // extends the most significant bit of the given byte
    U signext(uint64_t k) const {
        assert(k < N/8);
        if (k < L/8) {
            U<L> _lo = lo.signext(k);
            U<H> _hi = _lo.bit(L - 1) ? ~U<H>(0) : U<H>(0);
            return U<N>{_lo, _hi};
        }
        return U<N>{lo, hi.signext(k - L/8)};
    }

    static const U from(const uint8_t *buffer) { return U<N>::from(buffer, N/8); }
    static const U from(const uint8_t *buffer, uint64_t size) {
        U<N> v = U<N>{0, 0};
        if (size > L/8) {
            uint64_t _size = size > N/8 ? N/8 : size;
            v.hi = U<H>::from(&buffer[size - _size], _size - L/8);
        }
        if (size > 0) {
            uint64_t _size = size > L/8 ? L/8 : size;
            v.lo = U<L>::from(&buffer[size - _size], _size);
        }
        return v;
    }

    static void to(const U& v, uint8_t *buffer) { U<N>::to(v, buffer, N/8); }
    static void to(const U& v, uint8_t *buffer, uint64_t size) {
        if (size > N/8) {
            for (uint64_t i = 0; i < size - N/8; i++) buffer[i] = 0;
        }
        if (size > L/8) {
            uint64_t _size = size > N/8 ? N/8 : size;
            U<H>::to(v.hi, &buffer[size - _size], _size - L/8);
        }
        if (size > 0) {
            uint64_t _size = size > L/8 ? L/8 : size;
            U<L>::to(v.lo, &buffer[size - _size], _size);
        }
    }

    static bigint to_big(const U& v) {
        uint8_t buffer[N/8];
        U<N>::to(v, buffer);
        return bigint::from(buffer, N/8);
    }

    // murmur3 32-bit hash function
    // used to implement a fast low colision hash for this number
    uint32_t murmur3_(uint32_t seed) const { return lo.murmur3_(hi.murmur3_(seed)); }
    uint32_t murmur3(uint32_t seed) const {
        uint32_t h = lo.murmur3_(hi.murmur3_(seed));
        h ^= N/32;
        h ^= h >> 16;
        h *= 0x85ebca6b;
        h ^= h >> 13;
        h *= 0xc2b2ae35;
        h ^= h >> 16;
        return h;
    }

#ifndef NDEBUG
    friend std::ostream& operator<<(std::ostream &os, const U &v) {
        os << v.hi << ":" << v.lo;
        return os;
    }
#endif // NDEBUG
};

// base case for 64-bit numbers
template <>
struct U<64> {
    uint64_t n; // the actual 64-bit number
    inline U() {}
    inline U(uint64_t _n) : n(_n) {}
    template<int M> inline U(const U<M>& v) : U<64>(v, 0) {}
    template<int M> inline U(const U<M>& v, uint64_t base) : U<64>(base < M/32 ? v.word(base) : 0, base + 1 < M/32 ? v.word(base + 1) : 0) {}
    inline U(uint32_t n1, uint32_t n2) : n((uint64_t)n2 << 32 | (uint64_t)n1) {}

    inline U operator-() const { return U{-n}; }
    inline U operator~() const { return U{~n}; }

    inline U operator++(int) { return U{n++}; }
    inline U operator--(int) { return U{n--}; }

    inline U& operator++() { ++n; return *this; }
    inline U& operator--() { --n; return *this; }

    inline U& operator=(U v) { n = v.n; return *this; }

    inline U& operator+=(U v) { n += v.n; return *this; }
    inline U& operator-=(U v) { n -= v.n; return *this; }
    inline U& operator*=(U v) { n *= v.n; return *this; }
    inline U& operator/=(U v) { assert(v.n > 0); n /= v.n; return *this; }
    inline U& operator%=(U v) { assert(v.n > 0); n %= v.n; return *this; }
    inline U& operator&=(U v) { n &= v.n; return *this; }
    inline U& operator|=(U v) { n |= v.n; return *this; }
    inline U& operator^=(U v) { n ^= v.n; return *this; }

    inline U& operator=(uint64_t v) { n = v; return *this; }

    inline U& operator+=(uint64_t v) { n += v; return *this; }
    inline U& operator-=(uint64_t v) { n -= v; return *this; }
    inline U& operator*=(uint64_t v) { n *= v; return *this; }
    inline U& operator/=(uint64_t v) { assert(v > 0); n /= v; return *this; }
    inline U& operator%=(uint64_t v) { assert(v > 0); n %= v; return *this; }
    inline U& operator&=(uint64_t v) { n &= v; return *this; }
    inline U& operator|=(uint64_t v) { n |= v; return *this; }
    inline U& operator^=(uint64_t v) { n ^= v; return *this; }

    inline U& operator<<=(uint64_t k) { assert(k < 64); n <<= k; return *this; }
    inline U& operator>>=(uint64_t k) { assert(k < 64); n <<= k; return *this; }

    friend inline bool operator==(U v1, U v2) { return v1.n == v2.n; }
    friend inline bool operator!=(U v1, U v2) { return v1.n != v2.n; }
    friend inline bool operator<(U v1, U v2) { return v1.n < v2.n; }
    friend inline bool operator<=(U v1, U v2) { return v1.n <= v2.n; }
    friend inline bool operator>(U v1, U v2) { return v1.n > v2.n; }
    friend inline bool operator>=(U v1, U v2) { return v1.n >= v2.n; }

    friend inline U operator+(U v1, U v2) { return U{v1.n + v2.n}; }
    friend inline U operator-(U v1, U v2) { return U{v1.n - v2.n}; }
    friend inline U operator*(U v1, U v2) { return U{v1.n * v2.n}; }
    friend inline U operator/(U v1, U v2) { assert(v2.n > 0); return U{v1.n / v2.n}; }
    friend inline U operator%(U v1, U v2) { assert(v2.n > 0); return U{v1.n % v2.n}; }
    friend inline U operator&(U v1, U v2) { return U{v1.n & v2.n}; }
    friend inline U operator|(U v1, U v2) { return U{v1.n | v2.n}; }
    friend inline U operator^(U v1, U v2) { return U{v1.n ^ v2.n}; }

    friend inline bool operator==(uint64_t v1, U v2) { return v1 == v2.n; }
    friend inline bool operator!=(uint64_t v1, U v2) { return v1 != v2.n; }
    friend inline bool operator<(uint64_t v1, U v2) { return v1 < v2.n; }
    friend inline bool operator<=(uint64_t v1, U v2) { return v1 <= v2.n; }
    friend inline bool operator>(uint64_t v1, U v2) { return v1 > v2.n; }
    friend inline bool operator>=(uint64_t v1, U v2) { return v1 >= v2.n; }

    friend inline U operator+(uint64_t v1, U v2) { return U{v1 + v2.n}; }
    friend inline U operator-(uint64_t v1, U v2) { return U{v1 - v2.n}; }
    friend inline U operator*(uint64_t v1, U v2) { return U{v1 * v2.n}; }
    friend inline U operator/(uint64_t v1, U v2) { assert(v2.n > 0); return U{v1 / v2.n}; }
    friend inline U operator%(uint64_t v1, U v2) { assert(v2.n > 0); return U{v1 % v2.n}; }
    friend inline U operator&(uint64_t v1, U v2) { return U{v1 & v2.n}; }
    friend inline U operator|(uint64_t v1, U v2) { return U{v1 | v2.n}; }
    friend inline U operator^(uint64_t v1, U v2) { return U{v1 ^ v2.n}; }

    friend inline bool operator==(U v1, uint64_t v2) { return v1.n == v2; }
    friend inline bool operator!=(U v1, uint64_t v2) { return v1.n != v2; }
    friend inline bool operator<(U v1, uint64_t v2) { return v1.n < v2; }
    friend inline bool operator<=(U v1, uint64_t v2) { return v1.n <= v2; }
    friend inline bool operator>(U v1, uint64_t v2) { return v1.n > v2; }
    friend inline bool operator>=(U v1, uint64_t v2) { return v1.n >= v2; }

    friend inline U operator+(U v1, uint64_t v2) { return U{v1.n + v2}; }
    friend inline U operator-(U v1, uint64_t v2) { return U{v1.n - v2}; }
    friend inline U operator*(U v1, uint64_t v2) { return U{v1.n * v2}; }
    friend inline U operator/(U v1, uint64_t v2) { assert(v2 > 0); return U{v1.n / v2}; }
    friend inline U operator%(U v1, uint64_t v2) { assert(v2 > 0); return U{v1.n % v2}; }
    friend inline U operator&(U v1, uint64_t v2) { return U{v1.n & v2}; }
    friend inline U operator|(U v1, uint64_t v2) { return U{v1.n | v2}; }
    friend inline U operator^(U v1, uint64_t v2) { return U{v1.n ^ v2}; }

    friend inline U operator<<(U v, uint64_t k) { assert(k < 64); return U{v.n << k}; }
    friend inline U operator>>(U v, uint64_t k) { assert(k < 64); return U{v.n >> k}; }

    static inline U neg(U v) { return U{-v.n}; }
    static inline U lno(U v) { return U{~v.n}; }

    static inline U icp(U& v) { return U{v.n++}; }
    static inline U dcp(U& v) { return U{v.n--}; }

    static inline U& _pic(U& v) { ++v.n; return v; }
    static inline U& _pdc(U& v) { --v.n; return v; }

    static inline U& _cpy(U& v1, U v2) { v1.n = v2.n; return v1; }

    static inline U& _add(U& v1, U v2) { v1.n += v2.n; return v1; }
    static inline U& _sub(U& v1, U v2) { v1.n -= v2.n; return v1; }
    static inline U& _mul(U& v1, U v2) { v1.n *= v2.n; return v1; }
    static inline U& _div(U& v1, U v2) { assert(v2.n > 0); v1.n /= v2.n; return v1; }
    static inline U& _mod(U& v1, U v2) { assert(v2.n > 0); v1.n %= v2.n; return v1; }
    static inline U& _lan(U& v1, U v2) { v1.n &= v2.n; return v1; }
    static inline U& _lor(U& v1, U v2) { v1.n |= v2.n; return v1; }
    static inline U& _lxr(U& v1, U v2) { v1.n ^= v2.n; return v1; }

    static inline U& _cpy(U& v1, uint64_t v2) { v1.n = v2; return v1; }

    static inline U& _add(U& v1, uint64_t v2) { v1.n += v2; return v1; }
    static inline U& _sub(U& v1, uint64_t v2) { v1.n -= v2; return v1; }
    static inline U& _mul(U& v1, uint64_t v2) { v1.n *= v2; return v1; }
    static inline U& _div(U& v1, uint64_t v2) { assert(v2 > 0); v1.n /= v2; return v1; }
    static inline U& _mod(U& v1, uint64_t v2) { assert(v2 > 0); v1.n %= v2; return v1; }
    static inline U& _lan(U& v1, uint64_t v2) { v1.n &= v2; return v1; }
    static inline U& _lor(U& v1, uint64_t v2) { v1.n |= v2; return v1; }
    static inline U& _lxr(U& v1, uint64_t v2) { v1.n ^= v2; return v1; }

    static inline U& _shl(U& v, uint64_t k) { assert(k < 64); v.n <<= k; return v; }
    static inline U& _shr(U& v, uint64_t k) { assert(k < 64); v.n >>= k; return v; }
    static inline U& _sar(U& v, uint64_t k) { assert(k < 64); v.n = (v.n >> 63) > 0 ? ~(~v.n >> k) : v.n >> k; return v; }

    static inline bool equ(U v1, U v2) { return v1.n == v2.n; }
    static inline bool neq(U v1, U v2) { return v1.n != v2.n; }
    static inline bool ltn(U v1, U v2) { return v1.n < v2.n; }
    static inline bool lte(U v1, U v2) { return v1.n <= v2.n; }
    static inline bool gtn(U v1, U v2) { return v1.n > v2.n; }
    static inline bool gte(U v1, U v2) { return v1.n >= v2.n; }

    static inline U add(U v1, U v2) { return U{v1.n + v2.n}; }
    static inline U sub(U v1, U v2) { return U{v1.n - v2.n}; }
    static inline U mul(U v1, U v2) { return U{v1.n * v2.n}; }
    static inline U div(U v1, U v2) { assert(v2.n > 0); return U{v1.n / v2.n}; }
    static inline U mod(U v1, U v2) { assert(v2.n > 0); return U{v1.n % v2.n}; }
    static inline U lan(U v1, U v2) { return U{v1.n & v2.n}; }
    static inline U lor(U v1, U v2) { return U{v1.n | v2.n}; }
    static inline U lxr(U v1, U v2) { return U{v1.n ^ v2.n}; }

    static inline bool equ(uint64_t v1, U v2) { return v1 == v2.n; }
    static inline bool neq(uint64_t v1, U v2) { return v1 != v2.n; }
    static inline bool ltn(uint64_t v1, U v2) { return v1 < v2.n; }
    static inline bool lte(uint64_t v1, U v2) { return v1 <= v2.n; }
    static inline bool gtn(uint64_t v1, U v2) { return v1 > v2.n; }
    static inline bool gte(uint64_t v1, U v2) { return v1 >= v2.n; }

    static inline U add(uint64_t v1, U v2) { return U{v1 + v2.n}; }
    static inline U sub(uint64_t v1, U v2) { return U{v1 - v2.n}; }
    static inline U mul(uint64_t v1, U v2) { return U{v1 * v2.n}; }
    static inline U div(uint64_t v1, U v2) { assert(v2.n > 0); return U{v1 / v2.n}; }
    static inline U mod(uint64_t v1, U v2) { assert(v2.n > 0); return U{v1 % v2.n}; }
    static inline U lan(uint64_t v1, U v2) { return U{v1 & v2.n}; }
    static inline U lor(uint64_t v1, U v2) { return U{v1 | v2.n}; }
    static inline U lxr(uint64_t v1, U v2) { return U{v1 ^ v2.n}; }

    static inline bool equ(U v1, uint64_t v2) { return v1.n == v2; }
    static inline bool neq(U v1, uint64_t v2) { return v1.n != v2; }
    static inline bool ltn(U v1, uint64_t v2) { return v1.n < v2; }
    static inline bool lte(U v1, uint64_t v2) { return v1.n <= v2; }
    static inline bool gtn(U v1, uint64_t v2) { return v1.n > v2; }
    static inline bool gte(U v1, uint64_t v2) { return v1.n >= v2; }

    static inline U add(U v1, uint64_t v2) { return U{v1.n + v2}; }
    static inline U sub(U v1, uint64_t v2) { return U{v1.n - v2}; }
    static inline U mul(U v1, uint64_t v2) { return U{v1.n * v2}; }
    static inline U div(U v1, uint64_t v2) { assert(v2 > 0); return U{v1.n / v2}; }
    static inline U mod(U v1, uint64_t v2) { assert(v2 > 0); return U{v1.n % v2}; }
    static inline U lan(U v1, uint64_t v2) { return U{v1.n & v2}; }
    static inline U lor(U v1, uint64_t v2) { return U{v1.n | v2}; }
    static inline U lxr(U v1, uint64_t v2) { return U{v1.n ^ v2}; }

    static inline U shl(U v, uint64_t k) { assert(k < 64); return U{v.n << k}; }
    static inline U shr(U v, uint64_t k) { assert(k < 64); return U{v.n >> k}; }
    static inline U sar(U v, uint64_t k) { assert(k < 64); return U{(v.n >> 63) > 0 ? ~(~v.n >> k) : v.n >> k}; }

    static U muc(U v1, U v2, U& v3) {
        uint64_t v1_hi = v1.n >> 32;
        uint64_t v1_lo = v1.n & 0xffffffff;
        uint64_t v2_hi = v2.n >> 32;
        uint64_t v2_lo = v2.n & 0xffffffff;
        uint64_t z0 = v1_lo * v2_lo;
        uint64_t z0_hi = z0 >> 32;
        uint64_t z0_lo = z0 & 0xffffffff;
        uint64_t z1 = v1_lo * v2_hi;
        uint64_t z1_hi = z1 >> 32;
        uint64_t z1_lo = z1 & 0xffffffff;
        uint64_t z2 = v1_hi * v2_lo;
        uint64_t z2_hi = z2 >> 32;
        uint64_t z2_lo = z2 & 0xffffffff;
        uint64_t z3 = v1_hi * v2_hi;
        uint64_t z3_hi = z3 >> 32;
        uint64_t z3_lo = z3 & 0xffffffff;
        uint64_t s1 = z0_hi + z1_lo + z2_lo;
        uint64_t s1_hi = s1 >> 32;
        uint64_t s1_lo = s1 & 0xffffffff;
        uint64_t s2 = s1_hi + z1_hi + z2_hi + z3_lo;
        uint64_t s2_hi = s2 >> 32;
        uint64_t s2_lo = s2 & 0xffffffff;
        uint64_t s3 = s2_hi + z3_hi;
        uint64_t s3_lo = s3 & 0xffffffff;
        uint32_t t0_lo = (uint32_t)z0_lo;
        uint32_t t1_lo = (uint32_t)s1_lo;
        uint32_t t2_lo = (uint32_t)s2_lo;
        uint32_t t3_lo = (uint32_t)s3_lo;
        v3 = U<64>{t2_lo, t3_lo};
        return U<64>{t0_lo, t1_lo};
    }
    static U muc(uint64_t v1, U v2, U& v3) { return U<64>::muc(U<64>{v1}, v2, v3); }
    static U muc(U v1, uint64_t v2, U& v3) { return U<64>::muc(v1, U<64>{v2}, v3); }

    static inline U mul_(U v1, U v2) { return U{v1.n * v2.n}; }
    static inline U mul_(uint64_t v1, U v2) { return U{v1 * v2.n}; }
    static inline U mul_(U v1, uint64_t v2) { return U{v1.n * v2}; }

    static const U pow(U v1, U v2) {
        uint64_t x1 = 1;
        uint64_t x2 = v1.n;
        for (uint64_t i = 32; i > 0; i--) {
            x1 *= x1;
            if (v2.bit(i - 1)) x1 *= x2;
        }
        return x1;
    }

    static inline void quorem(U num, U div, U &quo, U &rem) {
        assert(div.n > 0);
        quo = U{num.n / div.n};
        rem = U{num.n % div.n};
    }

    static U addmod(U v1, U v2, U v3) {
        assert(v3.n > 0);
        return U<64>(U<128>::mod(U<128>::add(U<128>(v1), U<128>(v2)), U<128>(v3)));
    }

    static U mulmod(U v1, U v2, U v3) {
        assert(v3.n > 0);
        return U<64>(U<128>::mod(U<128>::mul(U<128>(v1), U<128>(v2)), U<128>(v3)));
    }

    static U powmod(U v1, U v2, U v3) {
        U<128> x1 = 1;
        U<128> x2 = v1;
        U<128> x3 = v3;
        for (uint64_t i = v2.bitlen(); i > 0; i--) {
            x1 = U<128>::mod(U<128>::mul(x1, x1), x3);
            if (v2.bit(i - 1)) x1 = U<128>::mod(U<128>::mul(x1, x2), x3);
        }
        return U<64>(U<128>::mod(x1, x3));
    }

    inline uint64_t cast64() const { return n; }

    inline bool bit(uint64_t k) const { assert(k < 64); return (n & ((uint64_t)1 << k)) > 0; }
    inline void setbit(uint64_t k) { assert(k < 64); n |= (uint64_t)1 << k; }
    inline void clrbit(uint64_t k) { assert(k < 64); n &= ~((uint64_t)1 << k); }

    inline uint8_t byte(uint64_t k) const { assert(k < 8); return (uint8_t)((n >> (k << 3)) & 0xff); }
    inline void setbyte(uint64_t k, uint8_t v) {
        assert(k < 8);
        n = (n & ~((uint64_t)0xff << (k << 3))) | ((uint64_t)v << (k << 3));
    }

    inline uint32_t word(uint64_t k) const { assert(k < 2); return (uint32_t)((n >> (k << 5)) & 0xffffffff); }
    inline void setword(uint64_t k, uint32_t v) {
        assert(k < 2);
        n = (n & ~((uint64_t)0xffffffff << (k << 5))) | ((uint64_t)v << (k << 5));
    }

    uint64_t bitlen() const { for (uint64_t k = 64; k > 0; k--) if (bit(k - 1)) return k; return 0; }
    uint64_t bytelen() const { for (uint64_t k = 8; k > 0; k--) if (byte(k - 1) > 0) return k; return 0; }
    uint64_t wordlen() const { for (uint64_t k = 2; k > 0; k--) if (word(k - 1) > 0) return k; return 0; }

    inline U signflip() { return U{n ^ ((uint64_t)1 << 63)}; }

    inline U signext(uint64_t k) const {
        assert(k < 8);
        uint64_t mask = (~(uint64_t)0xff) << (k << 3);
        return U<64>{(n & ((uint64_t)1 << (((k + 1) << 3) - 1))) > 0 ? n | mask : n & ~mask};
    }

    static inline const U from(const uint8_t *buffer) { return U<64>::from(buffer, 8); }
    static inline const U from(const uint8_t *buffer, uint64_t size) {
        return U<64>{0
            | (size > 7 ? (uint64_t)buffer[size-8] << 56 : 0)
            | (size > 6 ? (uint64_t)buffer[size-7] << 48 : 0)
            | (size > 5 ? (uint64_t)buffer[size-6] << 40 : 0)
            | (size > 4 ? (uint64_t)buffer[size-5] << 32 : 0)
            | (size > 3 ? (uint64_t)buffer[size-4] << 24 : 0)
            | (size > 2 ? (uint64_t)buffer[size-3] << 16 : 0)
            | (size > 1 ? (uint64_t)buffer[size-2] << 8 : 0)
            | (size > 0 ? (uint64_t)buffer[size-1] : 0)
        };
    }

    static void to(const U& v, uint8_t *buffer) { U<64>::to(v, buffer, 8); }
    static void to(const U& v, uint8_t *buffer, uint64_t size) {
        if (size > 8) {
            for (uint64_t i = 0; i < size - 8; i++) buffer[i] = 0;
        }
        if (size > 7) buffer[size - 8] = (uint8_t)(v.n >> 56);
        if (size > 6) buffer[size - 7] = (uint8_t)(v.n >> 48);
        if (size > 5) buffer[size - 6] = (uint8_t)(v.n >> 40);
        if (size > 4) buffer[size - 5] = (uint8_t)(v.n >> 32);
        if (size > 3) buffer[size - 4] = (uint8_t)(v.n >> 24);
        if (size > 2) buffer[size - 3] = (uint8_t)(v.n >> 16);
        if (size > 1) buffer[size - 2] = (uint8_t)(v.n >> 8);
        if (size > 0) buffer[size - 1] = (uint8_t)v.n;
    }

    static bigint to_big(const U& v) {
        uint8_t buffer[8];
        U<64>::to(v, buffer);
        return bigint::from(buffer, 8);
    }

    uint32_t murmur3_(uint32_t seed) const {
        uint32_t h = seed;
        uint32_t k = (uint32_t)(n >> 32);
        k *= 0xcc9e2d51;
        k = (k << 15) | (k >> 17);
        k *= 0x1b873593;
        h ^= k;
        h = (h << 13) | (h >> 19);
        h = h * 5 + 0xe6546b64;
        k = (uint32_t)n;
        k *= 0xcc9e2d51;
        k = (k << 15) | (k >> 17);
        k *= 0x1b873593;
        h ^= k;
        h = (h << 13) | (h >> 19);
        h = h * 5 + 0xe6546b64;
        return h;
    }
    uint64_t murmur3(uint32_t seed) const {
        uint32_t h = murmur3_(seed);
        h ^= 2;
        h ^= h >> 16;
        h *= 0x85ebca6b;
        h ^= h >> 13;
        h *= 0xc2b2ae35;
        h ^= h >> 16;
        return h;
    }

#ifndef NDEBUG
    friend std::ostream& operator<<(std::ostream &os, U v) {
        os << std::hex << std::setw(16) << std::setfill('0') << v.n;
        return os;
    }
#endif // NDEBUG
};

// base case for 32-bit numbers
// some operations with 64-bit operands may lose precision 
// however they are never used for numbers with at least 128-bits
// given that least significant base word of these numbers is always 64-bit
// this is the case for this implementation
template <>
struct U<32> {
    uint32_t n; // the actual 32-bit number
    inline U() {}
    inline U(uint32_t _n) : n(_n) {}
    template<int M> inline U(const U<M>& v) : U<32>(v, 0) {}
    template<int M> inline U(const U<M>& v, uint64_t base) : n(base < M/32 ? v.word(base) : 0) {}

    inline U operator-() const { return U{-n}; }
    inline U operator~() const { return U{~n}; }

    inline U operator++(int) { return U{n++}; }
    inline U operator--(int) { return U{n--}; }

    inline U& operator++() { ++n; return *this; }
    inline U& operator--() { --n; return *this; }

    inline U& operator=(U v) { n = v.n; return *this; }
    inline U& operator+=(U v) { n += v.n; return *this; }
    inline U& operator-=(U v) { n -= v.n; return *this; }
    inline U& operator*=(U v) { n *= v.n; return *this; }
    inline U& operator/=(U v) { assert(v.n > 0); n /= v.n; return *this; }
    inline U& operator%=(U v) { assert(v.n > 0); n %= v.n; return *this; }
    inline U& operator&=(U v) { n &= v.n; return *this; }
    inline U& operator|=(U v) { n |= v.n; return *this; }
    inline U& operator^=(U v) { n ^= v.n; return *this; }

    inline U& operator=(uint64_t v) { n = v; return *this; }
    inline U& operator+=(uint64_t v) { n += v; return *this; }
    inline U& operator-=(uint64_t v) { n -= v; return *this; }
    inline U& operator*=(uint64_t v) { n *= v; return *this; }
    inline U& operator/=(uint64_t v) { assert(v > 0); n /= v; return *this; }
    inline U& operator%=(uint64_t v) { assert(v > 0); n %= v; return *this; }
    inline U& operator&=(uint64_t v) { n &= v; return *this; }
    inline U& operator|=(uint64_t v) { n |= v; return *this; }
    inline U& operator^=(uint64_t v) { n ^= v; return *this; }

    inline U& operator<<=(uint64_t k) { assert(k < 32); n <<= k; return *this; }
    inline U& operator>>=(uint64_t k) { assert(k < 32); n <<= k; return *this; }

    friend inline bool operator==(U v1, U v2) { return v1.n == v2.n; }
    friend inline bool operator!=(U v1, U v2) { return v1.n != v2.n; }
    friend inline bool operator<(U v1, U v2) { return v1.n < v2.n; }
    friend inline bool operator<=(U v1, U v2) { return v1.n <= v2.n; }
    friend inline bool operator>(U v1, U v2) { return v1.n > v2.n; }
    friend inline bool operator>=(U v1, U v2) { return v1.n >= v2.n; }

    friend inline U operator+(U v1, U v2) { return U{v1.n + v2.n}; }
    friend inline U operator-(U v1, U v2) { return U{v1.n - v2.n}; }
    friend inline U operator*(U v1, U v2) { return U{v1.n * v2.n}; }
    friend inline U operator/(U v1, U v2) { assert(v2.n > 0); return U{v1.n / v2.n}; }
    friend inline U operator%(U v1, U v2) { assert(v2.n > 0); return U{v1.n % v2.n}; }
    friend inline U operator&(U v1, U v2) { return U{v1.n & v2.n}; }
    friend inline U operator|(U v1, U v2) { return U{v1.n | v2.n}; }
    friend inline U operator^(U v1, U v2) { return U{v1.n ^ v2.n}; }

    friend inline bool operator==(uint64_t v1, U v2) { return v1 == v2.n; }
    friend inline bool operator!=(uint64_t v1, U v2) { return v1 != v2.n; }
    friend inline bool operator<(uint64_t v1, U v2) { return v1 < v2.n; }
    friend inline bool operator<=(uint64_t v1, U v2) { return v1 <= v2.n; }
    friend inline bool operator>(uint64_t v1, U v2) { return v1 > v2.n; }
    friend inline bool operator>=(uint64_t v1, U v2) { return v1 >= v2.n; }

    friend inline U operator+(uint64_t v1, U v2) { return U{(uint32_t)v1 + v2.n}; }
    friend inline U operator-(uint64_t v1, U v2) { return U{(uint32_t)v1 - v2.n}; }
    friend inline U operator*(uint64_t v1, U v2) { return U{(uint32_t)v1 * v2.n}; }
    friend inline U operator/(uint64_t v1, U v2) { assert(v2.n > 0); return U{(uint32_t)(v1 / v2.n)}; }
    friend inline U operator%(uint64_t v1, U v2) { assert(v2.n > 0); return U{(uint32_t)(v1 % v2.n)}; }
    friend inline U operator&(uint64_t v1, U v2) { return U{(uint32_t)v1 & v2.n}; }
    friend inline U operator|(uint64_t v1, U v2) { return U{(uint32_t)v1 | v2.n}; }
    friend inline U operator^(uint64_t v1, U v2) { return U{(uint32_t)v1 ^ v2.n}; }

    friend inline bool operator==(U v1, uint64_t v2) { return v1.n == v2; }
    friend inline bool operator!=(U v1, uint64_t v2) { return v1.n != v2; }
    friend inline bool operator<(U v1, uint64_t v2) { return v1.n < v2; }
    friend inline bool operator<=(U v1, uint64_t v2) { return v1.n <= v2; }
    friend inline bool operator>(U v1, uint64_t v2) { return v1.n > v2; }
    friend inline bool operator>=(U v1, uint64_t v2) { return v1.n >= v2; }

    friend inline U operator+(U v1, uint64_t v2) { return U{v1.n + (uint32_t)v2}; }
    friend inline U operator-(U v1, uint64_t v2) { return U{v1.n - (uint32_t)v2}; }
    friend inline U operator*(U v1, uint64_t v2) { return U{v1.n * (uint32_t)v2}; }
    friend inline U operator/(U v1, uint64_t v2) { assert(v2 > 0); return U{(uint32_t)(v1.n / v2)}; }
    friend inline U operator%(U v1, uint64_t v2) { assert(v2 > 0); return U{(uint32_t)(v1.n % v2)}; }
    friend inline U operator&(U v1, uint64_t v2) { return U{v1.n & (uint32_t)v2}; }
    friend inline U operator|(U v1, uint64_t v2) { return U{v1.n | (uint32_t)v2}; }
    friend inline U operator^(U v1, uint64_t v2) { return U{v1.n ^ (uint32_t)v2}; }

    friend inline U operator<<(U v, uint64_t k) { assert(k < 32); return U{v.n << k}; }
    friend inline U operator>>(U v, uint64_t k) { assert(k < 32); return U{v.n >> k}; }

    static inline U neg(U v) { return U{-v.n}; }
    static inline U lno(U v) { return U{~v.n}; }

    static inline U icp(U& v) { return U{v.n++}; }
    static inline U dcp(U& v) { return U{v.n--}; }

    static inline U& _pic(U& v) { ++v.n; return v; }
    static inline U& _pdc(U& v) { --v.n; return v; }

    static inline U& _cpy(U& v1, U v2) { v1.n = v2.n; return v1; }

    static inline U& _add(U& v1, U v2) { v1.n += v2.n; return v1; }
    static inline U& _sub(U& v1, U v2) { v1.n -= v2.n; return v1; }
    static inline U& _mul(U& v1, U v2) { v1.n *= v2.n; return v1; }
    static inline U& _div(U& v1, U v2) { assert(v2.n > 0); v1.n /= v2.n; return v1; }
    static inline U& _mod(U& v1, U v2) { assert(v2.n > 0); v1.n %= v2.n; return v1; }
    static inline U& _lan(U& v1, U v2) { v1.n &= v2.n; return v1; }
    static inline U& _lor(U& v1, U v2) { v1.n |= v2.n; return v1; }
    static inline U& _lxr(U& v1, U v2) { v1.n ^= v2.n; return v1; }

    static inline U& _cpy(U& v1, uint64_t v2) { v1.n = v2; return v1; }

    static inline U& _add(U& v1, uint64_t v2) { v1.n += v2; return v1; }
    static inline U& _sub(U& v1, uint64_t v2) { v1.n -= v2; return v1; }
    static inline U& _mul(U& v1, uint64_t v2) { v1.n *= v2; return v1; }
    static inline U& _div(U& v1, uint64_t v2) { assert(v2 > 0); v1.n /= v2; return v1; }
    static inline U& _mod(U& v1, uint64_t v2) { assert(v2 > 0); v1.n %= v2; return v1; }
    static inline U& _lan(U& v1, uint64_t v2) { v1.n &= v2; return v1; }
    static inline U& _lor(U& v1, uint64_t v2) { v1.n |= v2; return v1; }
    static inline U& _lxr(U& v1, uint64_t v2) { v1.n ^= v2; return v1; }

    static inline U& _shl(U& v, uint64_t k) { assert(k < 32); v.n <<= k; return v; }
    static inline U& _shr(U& v, uint64_t k) { assert(k < 32); v.n >>= k; return v; }
    static inline U& _sar(U& v, uint64_t k) { assert(k < 32); v.n = (v.n >> 31) > 0 ? ~(~v.n >> k) : v.n >> k; return v; }

    static inline bool equ(U v1, U v2) { return v1.n == v2.n; }
    static inline bool neq(U v1, U v2) { return v1.n != v2.n; }
    static inline bool ltn(U v1, U v2) { return v1.n < v2.n; }
    static inline bool lte(U v1, U v2) { return v1.n <= v2.n; }
    static inline bool gtn(U v1, U v2) { return v1.n > v2.n; }
    static inline bool gte(U v1, U v2) { return v1.n >= v2.n; }

    static inline U add(U v1, U v2) { return U{v1.n + v2.n}; }
    static inline U sub(U v1, U v2) { return U{v1.n - v2.n}; }
    static inline U mul(U v1, U v2) { return U{v1.n * v2.n}; }
    static inline U div(U v1, U v2) { assert(v2.n > 0); return U{v1.n / v2.n}; }
    static inline U mod(U v1, U v2) { assert(v2.n > 0); return U{v1.n % v2.n}; }
    static inline U lan(U v1, U v2) { return U{v1.n & v2.n}; }
    static inline U lor(U v1, U v2) { return U{v1.n | v2.n}; }
    static inline U lxr(U v1, U v2) { return U{v1.n ^ v2.n}; }

    static inline bool equ(uint64_t v1, U v2) { return v1 == v2.n; }
    static inline bool neq(uint64_t v1, U v2) { return v1 != v2.n; }
    static inline bool ltn(uint64_t v1, U v2) { return v1 < v2.n; }
    static inline bool lte(uint64_t v1, U v2) { return v1 <= v2.n; }
    static inline bool gtn(uint64_t v1, U v2) { return v1 > v2.n; }
    static inline bool gte(uint64_t v1, U v2) { return v1 >= v2.n; }

    static inline U add(uint64_t v1, U v2) { return U{(uint32_t)v1 + v2.n}; }
    static inline U sub(uint64_t v1, U v2) { return U{(uint32_t)v1 - v2.n}; }
    static inline U mul(uint64_t v1, U v2) { return U{(uint32_t)v1 * v2.n}; }
    static inline U div(uint64_t v1, U v2) { assert(v2.n > 0); return U{(uint32_t)(v1 / v2.n)}; }
    static inline U mod(uint64_t v1, U v2) { assert(v2.n > 0); return U{(uint32_t)(v1 % v2.n)}; }
    static inline U lan(uint64_t v1, U v2) { return U{(uint32_t)v1 & v2.n}; }
    static inline U lor(uint64_t v1, U v2) { return U{(uint32_t)v1 | v2.n}; }
    static inline U lxr(uint64_t v1, U v2) { return U{(uint32_t)v1 ^ v2.n}; }

    static inline bool equ(U v1, uint64_t v2) { return v1.n == v2; }
    static inline bool neq(U v1, uint64_t v2) { return v1.n != v2; }
    static inline bool ltn(U v1, uint64_t v2) { return v1.n < v2; }
    static inline bool lte(U v1, uint64_t v2) { return v1.n <= v2; }
    static inline bool gtn(U v1, uint64_t v2) { return v1.n > v2; }
    static inline bool gte(U v1, uint64_t v2) { return v1.n >= v2; }

    static inline U add(U v1, uint64_t v2) { return U{v1.n + (uint32_t)v2}; }
    static inline U sub(U v1, uint64_t v2) { return U{v1.n - (uint32_t)v2}; }
    static inline U mul(U v1, uint64_t v2) { return U{v1.n * (uint32_t)v2}; }
    static inline U div(U v1, uint64_t v2) { assert(v2 > 0); return U{(uint32_t)(v1.n / v2)}; }
    static inline U mod(U v1, uint64_t v2) { assert(v2 > 0); return U{(uint32_t)(v1.n % v2)}; }
    static inline U lan(U v1, uint64_t v2) { return U{v1.n & (uint32_t)v2}; }
    static inline U lor(U v1, uint64_t v2) { return U{v1.n | (uint32_t)v2}; }
    static inline U lxr(U v1, uint64_t v2) { return U{v1.n ^ (uint32_t)v2}; }

    static inline U shl(U v, uint64_t k) { assert(k < 32); return U{v.n << k}; }
    static inline U shr(U v, uint64_t k) { assert(k < 32); return U{v.n >> k}; }
    static inline U sar(U v, uint64_t k) { assert(k < 32); return U{(v.n >> 31) > 0 ? ~(~v.n >> k) : v.n >> k}; }

    static inline U muc(U v1, U v2, U& v3) {
        uint64_t n = (uint64_t)v1.n * (uint64_t)v2.n;
        v3 = U{(uint32_t)(n >> 32)};
        return U{(uint32_t)(n & 0xffffffff)};
    }

    static inline U muc(uint64_t v1, U v2, U& v3) {
        uint64_t n = v1 * (uint64_t)v2.n;
        v3 = U{(uint32_t)(n >> 32)};
        return U{(uint32_t)(n & 0xffffffff)};
    }

    static inline U muc(U v1, uint64_t v2, U& v3) {
        uint64_t n = (uint64_t)v1.n * v2;
        v3 = U{(uint32_t)(n >> 32)};
        return U{(uint32_t)(n & 0xffffffff)};
    }

    static inline U mul_(U v1, U v2) { return U{v1.n * v2.n}; }
    static inline U mul_(uint64_t v1, U v2) { return U{(uint32_t)v1 * v2.n}; }
    static inline U mul_(U v1, uint64_t v2) { return U{v1.n * (uint32_t)v2}; }

    static const U pow(U v1, U v2) {
        uint32_t x1 = 1;
        uint32_t x2 = v1.n;
        for (uint64_t i = 32; i > 0; i--) {
            x1 *= x1;
            if (v2.bit(i - 1)) x1 *= x2;
        }
        return x1;
    }

    static inline void quorem(U num, U div, U &quo, U &rem) {
        assert(div.n > 0);
        quo = U{num.n / div.n};
        rem = U{num.n % div.n};
    }

    static inline U addmod(U v1, U v2, U v3) {
        assert(v3.n > 0);
        return U<32>{(uint32_t)(((uint64_t)v1.n + (uint64_t)v2.n) % (uint64_t)v3.n)};
    }

    static inline U mulmod(U v1, U v2, U v3) {
        assert(v3.n > 0);
        return U<32>{(uint32_t)(((uint64_t)v1.n * (uint64_t)v2.n) % (uint64_t)v3.n)};
    }

    static U powmod(U v1, U v2, U v3) {
        uint64_t x1 = 1;
        uint64_t x2 = (uint64_t)v1.n;
        uint64_t x3 = (uint64_t)v3.n;
        for (uint64_t i = 32; i > 0; i--) {
            x1 = (x1 * x1) % x3;
            if (v2.bit(i - 1)) x1 = (x1 * x2) % x3;
        }
        return U<32>{(uint32_t)(x1 % x3)};
    }

    inline uint64_t cast64() const { return n; }

    inline bool bit(uint64_t k) const { assert(k < 32); return (n & ((uint32_t)1 << k)) > 0; }
    inline void setbit(uint64_t k) { assert(k < 32); n |= (uint32_t)1 << k; }
    inline void clrbit(uint64_t k) { assert(k < 32); n &= ~((uint32_t)1 << k); }

    inline uint8_t byte(uint64_t k) const { assert(k < 4); return (uint8_t)((n >> (k << 3)) & 0xff); }
    inline void setbyte(uint64_t k, uint8_t v) {
        assert(k < 4);
        n = (n & ~((uint32_t)0xff << (k << 3))) | ((uint32_t)v << (k << 3));
    }

    inline uint32_t word(uint64_t k) const { assert(k < 1); return n; }
    inline void setword(uint64_t k, uint32_t v) { assert(k < 1); n = v; }

    uint64_t bitlen() const { for (uint64_t k = 32; k > 0; k--) if (bit(k - 1)) return k; return 0; }
    uint64_t bytelen() const { for (uint64_t k = 4; k > 0; k--) if (byte(k - 1) > 0) return k; return 0; }
    uint64_t wordlen() const { for (uint64_t k = 1; k > 0; k--) if (word(k - 1) > 0) return k; return 0; }

    inline U signflip() { return U{n ^ ((uint32_t)1 << 31)}; }

    inline U signext(uint64_t k) const {
        assert(k < 4);
        uint32_t mask = (~(uint32_t)0xff) << (k << 3);
        return U<32>{(n & ((uint32_t)1 << (((k + 1) << 3) - 1))) > 0 ? n | mask : n & ~mask};
    }

    static const U from(const uint8_t *buffer) { return U<32>::from(buffer, 4); }
    static const U from(const uint8_t *buffer, uint64_t size) {
        return U<32>{0
            | (size > 3 ? (uint32_t)buffer[size-4] << 24 : 0)
            | (size > 2 ? (uint32_t)buffer[size-3] << 16 : 0)
            | (size > 1 ? (uint32_t)buffer[size-2] << 8 : 0)
            | (size > 0 ? (uint32_t)buffer[size-1] : 0)
        };
    }

    static void to(const U& v, uint8_t *buffer) { U<32>::to(v, buffer, 4); }
    static void to(const U& v, uint8_t *buffer, uint64_t size) {
        if (size > 4) {
            for (uint64_t i = 0; i < size - 4; i++) buffer[i] = 0;
        }
        if (size > 3) buffer[size - 4] = (uint8_t)(v.n >> 24);
        if (size > 2) buffer[size - 3] = (uint8_t)(v.n >> 16);
        if (size > 1) buffer[size - 2] = (uint8_t)(v.n >> 8);
        if (size > 0) buffer[size - 1] = (uint8_t)v.n;
    }

    static bigint to_big(const U& v) {
        uint8_t buffer[4];
        U<32>::to(v, buffer);
        return bigint::from(buffer, 4);
    }

    uint32_t murmur3_(uint32_t seed) const {
        uint32_t h = seed;
        uint32_t k = n;
        k *= 0xcc9e2d51;
        k = (k << 15) | (k >> 17);
        k *= 0x1b873593;
        h ^= k;
        h = (h << 13) | (h >> 19);
        h = h * 5 + 0xe6546b64;
        return h;
    }
    uint64_t murmur3(uint32_t seed) const {
        uint32_t h = murmur3_(seed);
        h ^= 1;
        h ^= h >> 16;
        h *= 0x85ebca6b;
        h ^= h >> 13;
        h *= 0xc2b2ae35;
        h ^= h >> 16;
        return h;
    }

#ifndef NDEBUG
    friend std::ostream& operator<<(std::ostream &os, U v) {
        os << std::hex << std::setw(8) << std::setfill('0') << v.n;
        return os;
    }
#endif // NDEBUG
};

// conversion from decimal string
template<int N>
static U<N> udec(const char *s)
{
    U<N> t = 0;
    for (uint64_t i = 0; s[i] != '\0'; i++) {
        assert('0' <= s[i] && s[i] <= '9');
        t = 10 * t + (s[i] - '0');
    }
    return t;
}

// conversion from hexadecimal string
template<int N>
static U<N> uhex(const char *s)
{
    U<N> t = 0;
    for (uint64_t i = 0; s[i] != '\0'; i++) {
        assert(('0' <= s[i] && s[i] <= '9') || ('A' <= s[i] && s[i] <= 'F') || ('a' <= s[i] && s[i] <= 'f'));
        if (s[i] >= 'a') { t = 16 * t + (s[i] - 'a' + 10); continue; }
        if (s[i] >= 'A') { t = 16 * t + (s[i] - 'A' + 10); continue; }
        t = 16 * t + (s[i] - '0');
    }
    return t;
}

// 160-bit instance of U<N>
// used to represent evm addresses
struct uint160_t : public U<160> {
public:
    inline uint160_t() {}
    inline uint160_t(uint64_t v) : U(v) {}
    inline uint160_t(const U& v) : U(v) {}
};
static inline uint160_t udec160(const char *s) { return udec<160>(s); }
static inline uint160_t uhex160(const char *s) { return uhex<160>(s); }

// 256-bit instance of U<N>
// used to represent evm words
struct uint256_t : public U<256> {
public:
    inline uint256_t() {}
    inline uint256_t(uint64_t v) : U(v) {}
    inline uint256_t(const U& v) : U(v) {}
};
static inline uint256_t udec256(const char *s) { return udec<256>(s); }
static inline uint256_t uhex256(const char *s) { return uhex<256>(s); }

// 416-bit instance of U<N>
// used to represent storage locations as a combination of
// a 160-bit address + a 256-bit location key
struct uint416_t : public U<416> {
public:
    inline uint416_t() {}
    inline uint416_t(uint64_t v) : U(v) {}
    inline uint416_t(const U& v) : U(v) {}
};
static inline uint416_t udec416(const char *s) { return udec<416>(s); }
static inline uint416_t uhex416(const char *s) { return uhex<416>(s); }

// ** hashing **

// sha3 256-bit implementation (keccak flavor) and auxiliary functions
static inline uint64_t rot(uint64_t x, int y) { return y > 0 ? (x >> (64 - y)) ^ (x << y) : x; }
static inline uint64_t b2w64le(const uint8_t *b)
{
    return 0
        | ((uint64_t)b[7] << 56)
        | ((uint64_t)b[6] << 48)
        | ((uint64_t)b[5] << 40)
        | ((uint64_t)b[4] << 32)
        | ((uint64_t)b[3] << 24)
        | ((uint64_t)b[2] << 16)
        | ((uint64_t)b[1] << 8)
        | (uint64_t)b[0];
}
static inline void w2b64le(uint64_t w, uint8_t *b)
{
    b[0] = (uint8_t)w;
    b[1] = (uint8_t)(w >> 8);
    b[2] = (uint8_t)(w >> 16);
    b[3] = (uint8_t)(w >> 24);
    b[4] = (uint8_t)(w >> 32);
    b[5] = (uint8_t)(w >> 40);
    b[6] = (uint8_t)(w >> 48);
    b[7] = (uint8_t)(w >> 56);
}
static void sha3(const uint8_t *message, uint64_t size, bool compressed, uint64_t r, uint8_t eof, uint8_t *output)
{
    if (!compressed) {
        uint64_t bitsize = 8 * size;
        uint64_t padding = (r - bitsize % r) / 8;
        uint64_t b_len = size + padding;
        local<uint8_t> b_l(b_len); uint8_t *b = b_l.data;
        for (uint64_t i = 0; i < size; i++) b[i] = message[i];
        for (uint64_t i = size; i < b_len; i++) b[i] = 0;
        b[size] |= eof;
        b[b_len-1] |= 0x80;
        sha3(b, b_len, true, r, eof, output);
        return;
    }
    static const uint64_t RC[24] = {
        0x0000000000000001L, 0x0000000000008082L, 0x800000000000808aL,
        0x8000000080008000L, 0x000000000000808bL, 0x0000000080000001L,
        0x8000000080008081L, 0x8000000000008009L, 0x000000000000008aL,
        0x0000000000000088L, 0x0000000080008009L, 0x000000008000000aL,
        0x000000008000808bL, 0x800000000000008bL, 0x8000000000008089L,
        0x8000000000008003L, 0x8000000000008002L, 0x8000000000000080L,
        0x000000000000800aL, 0x800000008000000aL, 0x8000000080008081L,
        0x8000000000008080L, 0x0000000080000001L, 0x8000000080008008L,
    };
    static const uint8_t R[5][5] = {
        { 0, 36,  3, 41, 18},
        { 1, 44, 10, 45,  2},
        {62,  6, 43, 15, 61},
        {28, 55, 25, 21, 56},
        {27, 20, 39,  8, 14},
    };
    uint64_t s[5][5];
    for (int y = 0; y < 5; y++) {
        for (int x = 0; x < 5; x++) {
            s[x][y] = 0;
        }
    }
    uint64_t k = r / 64;
    for (uint64_t j = 0; j < size/8; j += k) {
        uint64_t w[25];
        for (uint64_t i = 0; i < k; i++) {
            w[i] = b2w64le(&message[8*(j+i)]);
        }
        for (int i = k; i < 25; i++) {
            w[i] = 0;
        }
        for (int y = 0; y < 5; y++) {
            for (int x = 0; x < 5; x++) {
                s[x][y] ^= w[5 * y + x];
            }
        }
        for (int j = 0; j < 24; j++) {
            uint64_t c[5];
            for (int x = 0; x < 5; x++) {
                c[x] = s[x][0] ^ s[x][1] ^ s[x][2] ^ s[x][3] ^ s[x][4];
            }
            uint64_t d[5];
            for (int x = 0; x < 5; x++) {
                d[x] = c[(x + 4) % 5] ^ rot(c[(x + 1) % 5], 1);
            }
            for (int x = 0; x < 5; x++) {
                for (int y = 0; y < 5; y++) {
                    s[x][y] ^= d[x];
                }
            }
            uint64_t b[5][5];
            for (int x = 0; x < 5; x++) {
                for (int y = 0; y < 5; y++) {
                    b[y][(2 * x + 3 * y) % 5] = rot(s[x][y], R[x][y]);
                }
            }
            for (int x = 0; x < 5; x++) {
                for (int y = 0; y < 5; y++) {
                    s[x][y] = b[x][y] ^ (~b[(x + 1) % 5][y] & b[(x + 2) % 5][y]);
                }
            }
            s[0][0] ^= RC[j];
        }
    }
    w2b64le(s[0][0], &output[0]);
    w2b64le(s[1][0], &output[8]);
    w2b64le(s[2][0], &output[16]);
    w2b64le(s[3][0], &output[24]);
    w2b64le(s[4][0], &output[32]);
    w2b64le(s[0][1], &output[40]);
    w2b64le(s[1][1], &output[48]);
    w2b64le(s[2][1], &output[56]);
}
#ifdef NATIVE_CRYPTO
static uint256_t sha3(const uint8_t *buffer, uint64_t size);
#else
static uint256_t sha3(const uint8_t *buffer, uint64_t size)
{
    local<uint8_t> output_l(64); uint8_t *output = output_l.data;
    sha3(buffer, size, false, 1088, 0x01, output);
    return uint256_t::from(output);
}
#endif // NATIVE_CRYPTO

// sha256 implementation and auxiliary functions
static inline uint32_t ch(uint32_t x, uint32_t y, uint32_t z) { return (x & (y ^ z)) ^ z; }
static inline uint32_t maj(uint32_t x, uint32_t y, uint32_t z) { return (x & y) ^ ((x ^ y) & z); }
static inline uint32_t rtr(uint32_t x, int y) { return (x >> y) ^ (x << (32 - y)); }
static inline uint32_t ep0(uint32_t x) { return rtr(x, 2) ^ rtr(x, 13) ^ rtr(x, 22); }
static inline uint32_t ep1(uint32_t x) { return rtr(x, 6) ^ rtr(x, 11) ^ rtr(x, 25); }
static inline uint32_t sig0(uint32_t x) { return rtr(x, 7) ^ rtr(x, 18) ^ (x >> 3); }
static inline uint32_t sig1(uint32_t x) { return rtr(x, 17) ^ rtr(x, 19) ^ (x >> 10); }
static inline uint32_t b2w32be(const uint8_t *b)
{
    return 0
        | ((uint64_t)b[0] << 24)
        | ((uint64_t)b[1] << 16)
        | ((uint64_t)b[2] << 8)
        | (uint64_t)b[3];
}
static inline void w2b32be(uint32_t w, uint8_t *b)
{
    b[3] = (uint8_t)w;
    b[2] = (uint8_t)(w >> 8);
    b[1] = (uint8_t)(w >> 16);
    b[0] = (uint8_t)(w >> 24);
}
static void sha256(const uint8_t *message, uint64_t size, bool compressed, uint8_t *output)
{
    if (!compressed) {
        uint64_t bitsize = 8 * size;
        uint64_t modulo = (size + 1 + 8) % 64;
        uint64_t padding = modulo > 0 ? 64 - modulo : 0;
        uint64_t b_len = size + 1 + padding + 8;
        local<uint8_t> b_l(b_len); uint8_t *b = b_l.data;
        for (uint64_t i = 0; i < size; i++) b[i] = message[i];
        for (uint64_t i = size; i < b_len; i++) b[i] = 0;
        b[size] = 0x80;
        w2b32be(bitsize >> 32, &b[b_len-8]);
        w2b32be(bitsize, &b[b_len-4]);
        sha256(b, b_len, true, output);
        return;
    }
    static const uint32_t S[8] = {
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
        0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
    };
    static const uint32_t K[64] = {
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
        0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
        0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
        0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
        0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
        0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
        0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
        0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
        0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
        0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
        0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
    };
    uint32_t s0 = S[0];
    uint32_t s1 = S[1];
    uint32_t s2 = S[2];
    uint32_t s3 = S[3];
    uint32_t s4 = S[4];
    uint32_t s5 = S[5];
    uint32_t s6 = S[6];
    uint32_t s7 = S[7];
    for (uint32_t j = 0; j < size/4; j += 16) {
        uint32_t w[64];
        for (int i = 0; i < 16; i++) {
            w[i] = b2w32be(&message[4*(j+i)]);
        }
        for (int i = 16; i < 64; i++) {
            w[i] = w[i-16] + sig0(w[i-15]) + w[i-7] + sig1(w[i-2]);
        }
        uint32_t a = s0;
        uint32_t b = s1;
        uint32_t c = s2;
        uint32_t d = s3;
        uint32_t e = s4;
        uint32_t f = s5;
        uint32_t g = s6;
        uint32_t h = s7;
        for (int i = 0; i < 64; i++) {
            uint32_t t1 = h + ep1(e) + ch(e, f, g) + K[i] + w[i];
            uint32_t t2 = ep0(a) + maj(a, b, c);
            h = g;
            g = f;
            f = e;
            e = d + t1;
            d = c;
            c = b;
            b = a;
            a = t1 + t2;
        }
        s0 += a;
        s1 += b;
        s2 += c;
        s3 += d;
        s4 += e;
        s5 += f;
        s6 += g;
        s7 += h;
    }
    w2b32be(s0, &output[0]);
    w2b32be(s1, &output[4]);
    w2b32be(s2, &output[8]);
    w2b32be(s3, &output[12]);
    w2b32be(s4, &output[16]);
    w2b32be(s5, &output[20]);
    w2b32be(s6, &output[24]);
    w2b32be(s7, &output[28]);
}
#ifdef NATIVE_CRYPTO
static uint256_t sha256(const uint8_t *buffer, uint64_t size);
#else
static uint256_t sha256(const uint8_t *buffer, uint64_t size)
{
    local<uint8_t> output_l(32); uint8_t *output = output_l.data;
    sha256(buffer, size, false, output);
    return uint256_t::from(output);
}
#endif // NATIVE_CRYPTO

// ripemd160 implementation and auxiliary functions
static inline uint32_t b2w32le(const uint8_t *b)
{
    return 0
        | ((uint64_t)b[3] << 24)
        | ((uint64_t)b[2] << 16)
        | ((uint64_t)b[1] << 8)
        | (uint64_t)b[0];
}
static inline void w2b32le(uint32_t w, uint8_t *b)
{
    b[0] = (uint8_t)w;
    b[1] = (uint8_t)(w >> 8);
    b[2] = (uint8_t)(w >> 16);
    b[3] = (uint8_t)(w >> 24);
}
static inline uint32_t rol(uint32_t x, int n) { return (x << n) ^ (x >> (32 - n)); }
static inline uint32_t f(uint32_t x, uint32_t y, uint32_t z) { return x ^ y ^ z; }
static inline uint32_t g(uint32_t x, uint32_t y, uint32_t z) { return (x & y) ^ (~x & z); }
static inline uint32_t h(uint32_t x, uint32_t y, uint32_t z) { return (x | ~y) ^ z; }
static inline uint32_t i(uint32_t x, uint32_t y, uint32_t z) { return (x & z) ^ (y & ~z); }
static inline uint32_t j(uint32_t x, uint32_t y, uint32_t z) { return x ^ (y | ~z); }
static void ripemd160(const uint8_t *message, uint64_t size, bool compressed, uint8_t *output)
{
    if (!compressed) {
        uint64_t bitsize = 8 * size;
        uint64_t modulo = (size + 1 + 8) % 64;
        uint64_t padding = modulo > 0 ? 64 - modulo : 0;
        uint64_t b_len = size + 1 + padding + 8;
        local<uint8_t> b_l(b_len); uint8_t *b = b_l.data;
        for (uint64_t i = 0; i < size; i++) b[i] = message[i];
        for (uint64_t i = size; i < b_len; i++) b[i] = 0;
        b[size] = 0x80;
        w2b32le(bitsize, &b[b_len-8]);
        w2b32le(bitsize >> 32, &b[b_len-4]);
        ripemd160(b, b_len, true, output);
        return;
    }
    static uint32_t (*F1[5])(uint32_t,uint32_t,uint32_t) = { f, g, h, i, j };
    static const uint32_t K1[5] = { 0x00000000, 0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xa953fd4e };
    static const uint8_t O1[5][16] = {
        { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15 },
        { 7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8 },
        { 3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12 },
        { 1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2 },
        { 4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13 },
    };
    static const uint8_t P1[5][16] = {
        { 11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8 },
        { 7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12 },
        { 11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5 },
        { 11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12 },
        { 9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6 },
    };
    static uint32_t (*F2[5])(uint32_t,uint32_t,uint32_t) = { j, i, h, g, f };
    const uint32_t K2[5] = { 0x50a28be6, 0x5c4dd124, 0x6d703ef3, 0x7a6d76e9, 0x00000000 };
    const uint8_t O2[5][16] = {
        { 5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12 },
        { 6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2 },
        { 15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13 },
        { 8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14 },
        { 12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11 },
    };
    const uint8_t P2[5][16] = {
        { 8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6 },
        { 9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11 },
        { 9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5 },
        { 15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8 },
        { 8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11 },
    };
    const uint32_t S[5] = { 0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0 };
    uint32_t s0 = S[0], s1 = S[1], s2 = S[2], s3 = S[3], s4 = S[4];
    for (uint64_t j = 0; j < size/4; j += 16) {
        uint32_t w[64];
        for (int i = 0; i < 16; i++) {
            w[i] = b2w32le(&message[4*(j+i)]);
        }
        for (int i = 16; i < 64; i++) {
            w[i] = 0;
        }
        uint32_t u0, u1, u2, u3, u4;
        {
            uint32_t a = s0, b = s1, c = s2, d = s3, e = s4;
            for (int i = 0; i < 5; i++) {
                uint32_t (*f)(uint32_t,uint32_t,uint32_t) = F1[i];
                uint32_t k = K1[i];
                const uint8_t *o = O1[i];
                const uint8_t *p = P1[i];
                for (int j = 0; j < 16; j++) {
                    a = rol(a + f(b, c, d) + w[o[j]] + k, p[j]) + e;
                    c = rol(c, 10);
                    uint32_t t = e; e = d; d = c; c = b; b = a; a = t;
                }
            }
            u0 = a; u1 = b; u2 = c; u3 = d; u4 = e;
        }
        uint32_t v0, v1, v2, v3, v4;
        {
            uint32_t a = s0, b = s1, c = s2, d = s3, e = s4;
            for (int i = 0; i < 5; i++) {
                uint32_t (*f)(uint32_t,uint32_t,uint32_t) = F2[i];
                uint32_t k = K2[i];
                const uint8_t *o = O2[i];
                const uint8_t *p = P2[i];
                for (int j = 0; j < 16; j++) {
                    a = rol(a + f(b, c, d) + w[o[j]] + k, p[j]) + e;
                    c = rol(c, 10);
                    uint32_t t = e; e = d; d = c; c = b; b = a; a = t;
                }
            }
            v0 = a; v1 = b; v2 = c; v3 = d; v4 = e;
        }
        s0 += u1 + v2;
        s1 += u2 + v3;
        s2 += u3 + v4;
        s3 += u4 + v0;
        s4 += u0 + v1;
        uint32_t t = s0; s0 = s1; s1 = s2; s2 = s3; s3 = s4; s4 = t;
    }
    w2b32le(s0, &output[0]);
    w2b32le(s1, &output[4]);
    w2b32le(s2, &output[8]);
    w2b32le(s3, &output[12]);
    w2b32le(s4, &output[16]);
}
#ifdef NATIVE_CRYPTO
static uint160_t ripemd160(const uint8_t *buffer, uint64_t size);
#else
static uint160_t ripemd160(const uint8_t *buffer, uint64_t size)
{
    local<uint8_t> output_l(20); uint8_t *output = output_l.data;
    ripemd160(buffer, size, false, output);
    return uint160_t::from(output);
}
#endif // NATIVE_CRYPTO

// blake2f internal cipher implementation and auxiliary functions
static inline uint64_t ror(uint64_t x, int n) { return (x << (64 - n)) ^ (x >> n); }
static inline void mix(
    uint64_t a, uint64_t b, uint64_t c, uint64_t d,
    uint64_t x, uint64_t y,
    uint64_t &_a, uint64_t &_b, uint64_t &_c, uint64_t &_d) {
    a = a + b + x;
    d = ror(d ^ a, 32);
    c = c + d;
    b = ror(b ^ c, 24);
    a = a + b + y;
    d = ror(d ^ a, 16);
    c = c + d;
    b = ror(b ^ c, 63);
    _a = a; _b = b; _c = c; _d = d;
}
#ifdef NATIVE_CRYPTO
static void blake2f(const uint32_t ROUNDS,
    uint64_t &h0, uint64_t &h1, uint64_t &h2, uint64_t &h3,
    uint64_t &h4, uint64_t &h5, uint64_t &h6, uint64_t &h7,
    uint64_t w[16], uint64_t t0, uint64_t t1, bool last_chunk);
#else
static void blake2f(const uint32_t ROUNDS,
    uint64_t &h0, uint64_t &h1, uint64_t &h2, uint64_t &h3,
    uint64_t &h4, uint64_t &h5, uint64_t &h6, uint64_t &h7,
    uint64_t w[16], uint64_t t0, uint64_t t1, bool last_chunk)
{
    static const uint8_t SIGMA[10][16] = {
        {  0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15 },
        { 14, 10,  4,  8,  9, 15, 13,  6,  1, 12,  0,  2, 11,  7,  5,  3 },
        { 11,  8, 12,  0,  5,  2, 15, 13, 10, 14,  3,  6,  7,  1,  9,  4 },
        {  7,  9,  3,  1, 13, 12, 11, 14,  2,  6,  5, 10,  4,  0, 15,  8 },
        {  9,  0,  5,  7,  2,  4, 10, 15, 14,  1, 11, 12,  6,  8,  3, 13 },
        {  2, 12,  6, 10,  0, 11,  8,  3,  4, 13,  7,  5, 15, 14,  1,  9 },
        { 12,  5,  1, 15, 14, 13,  4, 10,  0,  7,  6,  3,  9,  2,  8, 11 },
        { 13, 11,  7, 14, 12,  1,  3,  9,  5,  0, 15,  4,  8,  6,  2, 10 },
        {  6, 15, 14,  9, 11,  3,  0,  8, 12,  2, 13,  7,  1,  4, 10,  5 },
        { 10,  2,  8,  4,  7,  6,  1,  5, 15, 11,  9, 14,  3, 12, 13,  0 },
    };
    static const uint64_t iv[8] = {
        0x6a09e667f3bcc908, 0xbb67ae8584caa73b,
        0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
        0x510e527fade682d1, 0x9b05688c2b3e6c1f,
        0x1f83d9abfb41bd6b, 0x5be0cd19137e2179
    };
    uint64_t v0 = h0,  v1 = h1, v2 = h2, v3 = h3, v4 = h4, v5 = h5, v6 = h6, v7 = h7;
    uint64_t v8 = iv[0], v9 = iv[1], v10 = iv[2], v11 = iv[3], v12 = iv[4], v13 = iv[5], v14 = iv[6], v15 = iv[7];
    v12 ^= t0;
    v13 ^= t1;
    if (last_chunk) v14 ^= 0xffffffffffffffffL;
    for (uint32_t r = 0; r < ROUNDS; r++) {
        const uint8_t *indexes = SIGMA[r % 10];
        uint64_t m[16];
        for (int i = 0; i < 16; i++) m[i] = w[indexes[i]];
        uint64_t _v0, _v1, _v2, _v3, _v4, _v5, _v6, _v7;
        uint64_t _v8, _v9, _v10, _v11, _v12, _v13, _v14, _v15;
        mix(v0, v4, v8, v12, m[0], m[1], _v0, _v4, _v8, _v12);
        mix(v1, v5, v9, v13, m[2], m[3], _v1, _v5, _v9, _v13);
        mix(v2, v6, v10, v14, m[4], m[5], _v2, _v6, _v10, _v14);
        mix(v3, v7, v11, v15, m[6], m[7], _v3, _v7, _v11, _v15);
        mix(_v0, _v5, _v10, _v15, m[8], m[9], _v0, _v5, _v10, _v15);
        mix(_v1, _v6, _v11, _v12, m[10], m[11], _v1, _v6, _v11, _v12);
        mix(_v2, _v7, _v8, _v13, m[12], m[13], _v2, _v7, _v8, _v13);
        mix(_v3, _v4, _v9, _v14, m[14], m[15], _v3, _v4, _v9, _v14);
        v0 = _v0; v1 = _v1; v2 = _v2; v3 = _v3; v4 = _v4; v5 = _v5; v6 = _v6; v7 = _v7;
        v8 = _v8; v9 = _v9; v10 = _v10; v11 = _v11; v12 = _v12; v13 = _v13; v14 = _v14; v15 = _v15;
    }
    h0 ^= v0 ^ v8;
    h1 ^= v1 ^ v9;
    h2 ^= v2 ^ v10;
    h3 ^= v3 ^ v11;
    h4 ^= v4 ^ v12;
    h5 ^= v5 ^ v13;
    h6 ^= v6 ^ v14;
    h7 ^= v7 ^ v15;
}
#endif // NATIVE_CRYPTO

// ** elliptic curves **

// a double coordinate
// implemented as a template to allow instantiation with different field parameters
// required by this implemenation only to perform bn256 pairing
template<const char *_P>
struct Gen2_t {
    using Gen2 = Gen2_t;
    bigint x, y;
    Gen2_t() {}
    Gen2_t(const bigint &_x, const bigint &_y) : x(_x), y(_y) {}
    bool is_zero() const { return x == 0 && y == 0; }
    bool is_one() const { return x == 0 && y == 1; }
    Gen2 conj() const { return Gen2(neg(x), y); }
    Gen2 twice() const { return Gen2(x << 1, y << 1); }
    Gen2 mulxi() const { return Gen2((x << 3) + x + y, (y << 3) + neg(x) + y); }
    Gen2 sqr() const { return Gen2(((x * y) << 1) % P(), ((y + neg(x)) * (y + x)) % P()); }
    Gen2 inv() const { bigint inv = bigint::powmod(x * x + y * y, P() - 2, P()); return Gen2((neg(x) * inv) % P(), (y * inv) % P()); }
    Gen2 canon() const { return Gen2(x % P(), y % P()); }
    Gen2& operator=(const bigint& v) { x = 0; y = v; return *this; }
    Gen2& operator=(const Gen2& v) { x = v.x; y = v.y; return *this; }
    Gen2 operator-() const { Gen2 v = *this; v.x = neg(x); v.y = neg(y); return v; }
    Gen2& operator+=(const Gen2& v) { x += v.x; y += v.y; return *this; }
    Gen2& operator-=(const Gen2& v) { x += neg(v.x); y += neg(v.y); return *this; }
    Gen2& operator*=(const bigint& v) { x *= v; y *= v; return *this; }
    Gen2& operator*=(const Gen2& v2) {
        Gen2 v1 = *this;
        x = (v1.x * v2.y + v1.y * v2.x) % P();
        y = (v1.y * v2.y + neg(v1.x * v2.x)) % P();
        return *this;
    }
    friend const Gen2 operator+(const Gen2& v1, const Gen2& v2) { return Gen2(v1) += v2; }
    friend const Gen2 operator-(const Gen2& v1, const Gen2& v2) { return Gen2(v1) -= v2; }
    friend const Gen2 operator*(const Gen2& v1, const Gen2& v2) { return Gen2(v1) *= v2; }
    friend const Gen2 operator*(const Gen2& v1, const bigint& v2) { return Gen2(v1) *= v2; }
    static bigint neg(const bigint &v) { return P() - (v % P()); }
    static bigint P() { static bigint P = big(_P); return P; }
};

// a triple of double coordinates
// implemented as a template to allow instantiation with different field paramters
// required by this implemenation only to perform bn256 pairing
// not made completely general as some constants for bn256 are inlined
template<class Gen2>
struct Gen6_t {
    using Gen6 = Gen6_t;
    Gen2 x, y, z;
    Gen6_t() {}
    Gen6_t(const Gen2 &_x, const Gen2 &_y, const Gen2 &_z) : x(_x), y(_y), z(_z) {}
    bool is_zero() const { return x.is_zero() && y.is_zero() && z.is_zero(); }
    bool is_one() const { return x.is_zero() && y.is_zero() && z.is_one(); }
    Gen6 twice() const { return Gen6(x.twice(), y.twice(), z.twice()); }
    Gen6 frob() const {
        static const Gen2 XI_2_P_2_3(
            big("19937756971775647987995932169929341994314640652964949448313374472400716661030"),
            big("2581911344467009335267311115468803099551665605076196740867805258568234346338")
        );
        static const Gen2 XI_P_1_3(
            big("10307601595873709700152284273816112264069230130616436755625194854815875713954"),
            big("21575463638280843010398324269430826099269044274347216827212613867836435027261")
        );
        return Gen6(x.conj() * XI_2_P_2_3, y.conj() * XI_P_1_3, z.conj());
    }
    Gen6 frob2() const {
        static const bigint XI_2_P2_2_3 = big("2203960485148121921418603742825762020974279258880205651966");
        static const bigint XI_P2_1_3 = big("21888242871839275220042445260109153167277707414472061641714758635765020556616");
        return Gen6(x * XI_2_P2_2_3, y * XI_P2_1_3, z);
    }
    Gen6 inv() const {
        Gen2 t0 = x.sqr().mulxi() - (y * z);
        Gen2 t1 = y.sqr() - (x * z);
        Gen2 t2 = z.sqr() - (x * y).mulxi();
        Gen2 t3 = ((t1 * y).mulxi() + t2 * z + (t0 * x).mulxi()).inv();
        return Gen6(t1 * t3, t0 * t3, t2 * t3);
    }
    Gen6 multau() const { return Gen6(y, z, x.mulxi()); }
    Gen6 sqr() const {
        Gen2 t0 = x.sqr();
        Gen2 t1 = y.sqr();
        Gen2 t2 = z.sqr();
        Gen2 t3 = (x + z).sqr() - (t2 + t0) + t1;
        Gen2 t4 = (y + z).sqr() - (t2 + t1) + t0.mulxi();
        Gen2 t5 = ((x + y).sqr() - (t1 + t0)).mulxi() + t2;
        return Gen6(t3, t4, t5);
    }
    Gen6 canon() const { return Gen6(x.canon(), y.canon(), z.canon()); }
    Gen6& operator=(const bigint& v) { x = 0; y = 0; z = v; return *this; }
    Gen6 operator-() const { return Gen6(-x, -y, -z); }
    Gen6& operator+=(const Gen6& v) { x += v.x; y += v.y; z += v.z; return *this; }
    Gen6& operator-=(const Gen6& v) { x -= v.x; y -= v.y; z -= v.z; return *this; }
    Gen6& operator*=(const Gen6& v2) {
        Gen6 v1 = *this;
        Gen2 t0 = v1.x * v2.x;
        Gen2 t1 = v1.y * v2.y;
        Gen2 t2 = v1.z * v2.z;
        x = (v1.x + v1.z) * (v2.x + v2.z) - (t2 + t0) + t1;
        y = (v1.y + v1.z) * (v2.y + v2.z) - (t2 + t1) + t0.mulxi();
        z = (((v1.x + v1.y) * (v2.x + v2.y)) - (t1 + t0)).mulxi() + t2;
        return *this;
    }
    Gen6& operator*=(const Gen2& v) { x *= v; y *= v; z *= v; return *this; }
    Gen6& operator*=(const bigint &v) { x *= v; y *= v; z *= v; return *this; }
    friend const Gen6 operator+(const Gen6& v1, const Gen6& v2) { return Gen6(v1) += v2; }
    friend const Gen6 operator-(const Gen6& v1, const Gen6& v2) { return Gen6(v1) -= v2; }
    friend const Gen6 operator*(const Gen6& v1, const Gen6& v2) { return Gen6(v1) *= v2; }
    friend const Gen6 operator*(const Gen6& v1, const Gen2& v2) { return Gen6(v1) *= v2; }
    friend const Gen6 operator*(const Gen6& v1, const bigint& v2) { return Gen6(v1) *= v2; }
};

// a pair of triple coordinates of double coordinates
// implemented as a template to allow instantiation with different field paramters
// required by this implemenation only to perform bn256 pairing
// not made completely general as some constants for bn256 are inlined
template<class Gen2, class Gen6>
struct Gen12_t {
    using Gen12 = Gen12_t;
    Gen6 x, y;
    Gen12_t() {}
    Gen12_t(const Gen6 &_x, const Gen6 &_y) : x(_x), y(_y) {}
    Gen12 conj() const { return Gen12(-x, y); }
    Gen12 pow(const bigint &power) const {
        const Gen12 &a = *this;
        Gen12 sum; sum = 1;
        for (uint64_t i = power.bitlen(); i > 0; i--) {
            Gen12 t = sum.sqr();
            sum = power.bit(i - 1) ? t * a : t;
        }
        return sum;
    }
    Gen12 frob() const {
        static const Gen2 XI_P_1_6(
            big("16469823323077808223889137241176536799009286646108169935659301613961712198316"),
            big("8376118865763821496583973867626364092589906065868298776909617916018768340080")
        );
        return Gen12(x.frob() * XI_P_1_6, y.frob());
    }
    Gen12 frob2() const {
        static const bigint XI_P2_1_6 = big("21888242871839275220042445260109153167277707414472061641714758635765020556617");
        return Gen12(x.frob2() * XI_P2_1_6, y.frob2());
    }
    Gen12 inv() const { return Gen12(-x, y) * (y.sqr() - x.sqr().multau()).inv(); }
    Gen12 sqr() const {
        Gen6 t0 = x * y;
        Gen6 t1 = (x + y) * (x.multau() + y) - (t0 + t0.multau());
        return Gen12(t0.twice(), t1);
    }
    bool is_one() const { Gen12 t = canon(); return t.x.is_zero() && t.y.is_one(); }
    Gen12 canon() const { return Gen12(x.canon(), y.canon()); }
    Gen12& operator=(const bigint& v) { x = 0; y = v; return *this; }
    Gen12& operator*=(const Gen12& v2) {
        Gen12 v1 = *this;
        x = v1.x * v2.y + v1.y * v2.x;
        y = (v1.y * v2.y) + (v1.x * v2.x).multau();
        return *this;
    }
    Gen12& operator*=(const Gen6& v) { x *= v; y *= v; return *this; }
    friend const Gen12 operator*(const Gen12& v1, const Gen12& v2) { return Gen12(v1) *= v2; }
    friend const Gen12 operator*(const Gen12& v1, const Gen6& v2) { return Gen12(v1) *= v2; }
};

// a general elliptic curve point encoded as a jacobian
// parameterized over the field prime P and the constant B
// assumes A is always zero, which is the case of use in this implementation
template<const char *_P, int _B>
struct CurvePoint_t {
    using CurvePoint = CurvePoint_t;
    bigint x, y, z, t;
    CurvePoint_t() {}
    CurvePoint_t(const bigint &_x, const bigint &_y) : x(_x), y(_y) {
        if (x == 0 && y == 0) { y = 1; z = 0; t = 0; } else { z = 1; t = 1; }
    }
    CurvePoint_t(const bigint &_x, const bigint &_y, const bigint &_z, const bigint &_t) : x(_x), y(_y), z(_z), t(_t) {}
    bool is_inf() const { return z == 0; }
    bool is_valid() const {
        bigint t = y * y + neg(x * x * x + _B);
        if (t >= P()) t %= P();
        return t == 0;
    }
    CurvePoint twice() const {
        bigint a = (x * x) % P();
        bigint b = (y * y) % P();
        bigint c = (b * b) % P();
        bigint t0 = x + b;
        bigint d = ((t0 * t0) % P()) + neg(a + c);
        bigint e = d + d;
        bigint f = a + a + a;
        bigint g = (y * z) % P();
        bigint h = c + c;
        bigint i = h + h;
        bigint _x = ((f * f) % P()) + neg(e + e);
        bigint _y = ((f * (e + neg(_x))) % P()) + neg(i + i);
        bigint _z = g + g;
        bigint _t = t; // check
        return CurvePoint(_x, _y, _z, _t);
    }
    CurvePoint affine() const {
        if (z == 1) return *this;
        if (is_inf()) { return CurvePoint(0, 1, 0, 0); }
        bigint zinv = bigint::powmod(z, P() - 2, P());
        bigint zinv2 = (zinv * zinv) % P();
        bigint _x = (x * zinv2) % P();
        bigint _y = (((y * zinv2) % P()) * zinv) % P();
        return CurvePoint(_x, _y, 1, 1);
    }
    void inf() { z = 0; }
    CurvePoint operator-() const { return CurvePoint(x, neg(y), z, 0); }
    CurvePoint& operator+=(const CurvePoint& b) {
        CurvePoint a = *this;
        if (a.is_inf()) { *this = b; return *this; }
        if (b.is_inf()) { *this = a; return *this; }
        bigint z1z1 = (a.z * a.z) % P();
        bigint z2z2 = (b.z * b.z) % P();
        bigint u1 = (a.x * z2z2) % P();
        bigint u2 = (b.x * z1z1) % P();
        bigint s1 = (a.y * ((b.z * z2z2) % P())) % P();
        bigint s2 = (a.z * ((b.y * z1z1) % P())) % P();
        bigint h = (u2 + neg(u1)) % P();
        bigint t = (s2 + neg(s1)) % P();
        if (h == 0 && t == 0) { *this = a.twice(); return *this; }
        bigint _t = h + h;
        bigint i = (_t * _t) % P();
        bigint j = (h * i) % P();
        bigint r = t + t;
        bigint v = (u1 * i) % P();
        bigint w = (s1 * j) % P();
        bigint t0 = a.z + b.z;
        x = ((r * r) % P()) + neg(j + v + v);
        y = ((r * (v + neg(x))) % P()) + neg(w + w);
        z = ((((t0 * t0) % P()) + neg(z1z1 + z2z2)) * h) % P();
        // check t
        return *this;
    }
    CurvePoint& operator*=(const bigint& scalar) {
        CurvePoint a = *this;
        CurvePoint sum; sum.inf();
        for (uint64_t i = scalar.bitlen() + 1; i > 0; i--) {
            CurvePoint t = sum.twice();
            sum = scalar.bit(i - 1) ? t + a : t;
        }
        *this = sum;
        return *this;
    }
    friend const CurvePoint operator+(const CurvePoint& v1, const CurvePoint& v2) { return CurvePoint(v1) += v2; }
    friend const CurvePoint operator*(const CurvePoint& v1, const bigint& v2) { return CurvePoint(v1) *= v2; }
    static bigint neg(const bigint &v) { return P() - (v % P()); }
    static bigint P() { static bigint P = big(_P); return P; }
};

// the dual twist point to the curve point
// parameterized over the pair of coordinates and order Q
// required by this implemenation only to perform bn256 pairing
// not made completely general as some constants for bn256 are inlined
template<class Gen2, const char *_Q>
struct TwistPoint_t {
    using TwistPoint = TwistPoint_t;
    Gen2 x, y, z, t;
    TwistPoint_t() {}
    TwistPoint_t(const Gen2 &_x, const Gen2 &_y) : x(_x), y(_y) {
        if (x.is_zero() && y.is_zero()) { y = 1; z = 0; t = 0; } else { z = 1; t = 1; }
    }
    TwistPoint_t(const Gen2 &_x, const Gen2 &_y, const Gen2 &_z, const Gen2 &_t) : x(_x), y(_y), z(_z), t(_t) {}
    bool is_inf() const { return z.is_zero(); }
    bool is_valid() const {
        static const Gen2 twistB(
            big("266929791119991161246907387137283842545076965332900288569378510910307636690"),
            big("19485874751759354771024239261021720505790618469301721065564631296452457478373")
        );
        Gen2 t = y.sqr() - (x.sqr() * x + twistB);
        t = t.canon();
        if (t.x != 0 || t.y != 0) return false;
        TwistPoint p = *this * Q();
        return p.z.is_zero();
    }
    TwistPoint twice() const {
        Gen2 a = x.sqr();
        Gen2 b = y.sqr();
        Gen2 c = b.sqr();
        Gen2 d = (x + b).sqr() - (a + c);
        Gen2 e = d + d;
        Gen2 f = a + a + a;
        Gen2 g = y * z;
        Gen2 h = c + c;
        Gen2 i = h + h;
        Gen2 _x = f.sqr() - (e + e);
        Gen2 _y = f * (e - _x) - (i + i);
        Gen2 _z = g + g;
        Gen2 _t; _t = 0; // check
        return TwistPoint(_x, _y, _z, _t);
    }
    TwistPoint affine() const {
        if (z.is_one()) return *this;
        if (is_inf()) { Gen2 _x, _y, _z, _t; _x = 0; _y = 1; _z = 0; _t = 0; return TwistPoint(_x, _y, _z, _t); }
        Gen2 zinv = z.inv();
        Gen2 zinv2 = zinv.sqr();
        Gen2 _x = x * zinv2;
        Gen2 _y = y * zinv2 * zinv;
        Gen2 _z; _z = 1;
        Gen2 _t; _t = 1;
        return TwistPoint(_x, _y, _z, _t);
    }
    void inf() { z = 0; }
    TwistPoint operator-() const { Gen2 t; t = 0; return TwistPoint(x, -y, z, t); }
    TwistPoint& operator+=(const TwistPoint& b) {
        TwistPoint a = *this;
        if (a.is_inf()) { *this = b; return *this; }
        if (b.is_inf()) { *this = a; return *this; }
        Gen2 z1z1 = a.z.sqr();
        Gen2 z2z2 = b.z.sqr();
        Gen2 u1 = a.x * z2z2;
        Gen2 u2 = b.x * z1z1;
        Gen2 s1 = a.y * b.z * z2z2;
        Gen2 s2 = a.z * b.y * z1z1;
        Gen2 h = u2 - u1;
        Gen2 t = s2 - s1;
        if (h.is_zero() && t.is_zero()) { *this = a.twice(); return *this; }
        Gen2 i = (h + h).sqr();
        Gen2 j = h * i;
        Gen2 r = t + t;
        Gen2 v = u1 * i;
        Gen2 w = s1 * j;
        x = r.sqr() - (j + v + v);
        y = (r * (v - x)) - (w + w);
        z = ((a.z + b.z).sqr() - (z1z1 + z2z2)) * h;
        // check t
        return *this;
    }
    TwistPoint& operator*=(const bigint& scalar) {
        TwistPoint a = *this;
        TwistPoint sum; sum.inf();
        for (uint64_t i = scalar.bitlen() + 1; i > 0; i--) {
            TwistPoint t = sum.twice();
            sum = scalar.bit(i - 1) ? t + a : t;
        }
        *this = sum;
        return *this;
    }
    friend const TwistPoint operator+(const TwistPoint& v1, const TwistPoint& v2) { return TwistPoint(v1) += v2; }
    friend const TwistPoint operator*(const TwistPoint& v1, const bigint& v2) { return TwistPoint(v1) *= v2; }
    static bigint Q() { static bigint Q = big(_Q); return Q; }
};

// ** secp256k1 **

// seckp256k1 constants
static const char p_[] = "115792089237316195423570985008687907853269984665640564039457584007908834671663";
static const char q_[] = "115792089237316195423570985008687907852837564279074904382605163141518161494337";

// seckp256k1 curve definition
using G0 = CurvePoint_t<p_, 7>;

#ifdef NATIVE_CRYPTO
static G0 ecrecover(const uint256_t &_h, const uint256_t &_v, const uint256_t &_r, const uint256_t &_s);
#else
static G0 ecrecover(const uint256_t &_h, const uint256_t &_v, const uint256_t &_r, const uint256_t &_s)
{
    static const bigint P = big(p_);
    static const bigint Q = big(q_);
    static const G0 G = G0(
        big("55066263022277343669578718895168534326250603453777594175500187360389116729240"),
        big("32670510020758816978083085130507043184471273380659243275938904335757337482424")
    );

    bigint h = uint256_t::to_big(_h);
    bigint v = uint256_t::to_big(_v);
    bigint r = uint256_t::to_big(_r);
    bigint s = uint256_t::to_big(_s);
    bigint y = bigint::powmod(((r * r) % P * r) % P + 7, (P + 1) / 4, P);
    if ((v == 28) == ((y % 2) == 0)) y = P - y;
    G0 q(r, y);
    if (!q.is_valid()) return G0(0, 0);
    bigint u = Q - (h % Q);
    bigint z = bigint::powmod(r, Q - 2, Q);
    G0 t = ((q * s) + (G * u)) * z;
    t = t.affine();
    return t;
}
#endif // NATIVE_CRYPTO

// secp256k1 publickey (in fact 160-bit address) recovery from signature
// it follows the elliptic curve algorithm
static uint160_t _throws(ecrecover)(const uint256_t &h, const uint256_t &v, const uint256_t &r, const uint256_t &s)
{
    static const uint256_t P = udec256(p_);
    if (v < 27 || v > 28) _throw0(INVALID_SIGNATURE);
    if (r == 0 || r >= P) _throw0(INVALID_SIGNATURE);
    if (s == 0 || r >= P) _throw0(INVALID_SIGNATURE);
    G0 t = ecrecover(h, v, r, s);
    if (t.is_inf()) _throw0(INVALID_SIGNATURE);
    local<uint8_t> buffer_l(64); uint8_t *buffer = buffer_l.data;
    uint64_t offset = 0;
    bigint::to(t.x, &buffer[offset], 32); offset += 32;
    bigint::to(t.y, &buffer[offset], 32); offset += 32;
    return (uint160_t)sha3(buffer, 64);
}

// ** bn256 **

// bn256 constants
static const char P_[] = "21888242871839275222246405745257275088696311157297823662689037894645226208583";
static const char Q_[] = "21888242871839275222246405745257275088548364400416034343698204186575808495617";

// bn256 curve/twist definitions
using Gen2 = Gen2_t<P_>;
using Gen6 = Gen6_t<Gen2>;
using Gen12 = Gen12_t<Gen2, Gen6>;
using G1 = CurvePoint_t<P_, 3>;
using G2 = TwistPoint_t<Gen2, Q_>;

// bn256 miller's pairing algorithm
static void mul_line(const Gen2 &a, const Gen2 &b, const Gen2 &c, Gen12 &inout)
{
    Gen2 _0; _0 = 0;
    Gen6 t1 = inout.x * Gen6(_0, a, b);
    Gen6 t2 = inout.y * c;
    inout.x = (inout.x + inout.y) * Gen6(_0, a, b + c) - (t1 + t2);
    inout.y = t1.multau() + t2;
}
static G2 line_func_twice(const G1 &q, const G2 &r, Gen2 &a, Gen2 &b, Gen2 &c)
{
    Gen2 A = r.x.sqr();
    Gen2 B = r.y.sqr();
    Gen2 C = B.sqr();
    Gen2 D = (r.x + B).sqr() - (A + C);
    Gen2 E = D + D;
    Gen2 F = A + A + A;
    Gen2 G = F.sqr();
    Gen2 H = G - (E + E);
    Gen2 I = C + C;
    Gen2 J = I + I;
    Gen2 K = (r.y + r.z).sqr() - (B + r.t);
    Gen2 L = F * r.t;
    Gen2 M = B + B;
    Gen2 N = K * r.t;
    a = ((r.x + F).sqr() - (A + G)) - (M + M);
    b = -(L + L) * q.x;
    c = (N + N) * q.y;
    return G2(H, (E - H) * F - (J + J), K, K.sqr());
}
static G2 line_func_add(const G1 &q, const G2 &r, const G2 &p, const Gen2 &r2, Gen2 &a, Gen2&b, Gen2&c)
{
    Gen2 A = ((p.y + r.z).sqr() - (r2 + r.t)) * r.t - (r.y + r.y);
    Gen2 B = p.x * r.t;
    Gen2 C = B - r.x;
    Gen2 D = C.sqr();
    Gen2 E = D + D;
    Gen2 F = E + E;
    Gen2 G = C * F;
    Gen2 H = r.x * F;
    Gen2 I = A.sqr() - (G + H + H);
    Gen2 J = r.y * G;
    Gen2 K = (r.z + C).sqr() - (r.t + D);
    Gen2 L = K.sqr();
    Gen2 M = A * p.x;
    Gen2 N = K * q.y;
    Gen2 O = -A * q.x;
    a = M + M - (p.y + K).sqr() + r2 + L;
    b = O + O;
    c = N + N;
    return G2(I, (H - I) * A - (J + J), K, L);
}
static Gen12 miller(const G1 &_A, const G2 &_B)
{
    static const int8_t sixuPlus2NAF[] = {
        1, 0, 1, 0, 0, -1, 0, 1, 1, 0, 0, 0, -1, 0, 0, 1,
        1, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 1,
        1, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1, 0, 1, 1, 0,
        0, 1, 0, 0, -1, 1, 0, 0, -1, 0, 1, 0, 1, 0, 0, 0,
    };

    static const bigint XI_P2_1_3 = big("21888242871839275220042445260109153167277707414472061641714758635765020556616");
    static const Gen2 XI_P_1_3(
        big("10307601595873709700152284273816112264069230130616436755625194854815875713954"),
        big("21575463638280843010398324269430826099269044274347216827212613867836435027261")
    );
    static const Gen2 XI_P_1_2(
        big("3505843767911556378687030309984248845540243509899259641013678093033130930403"),
        big("2821565182194536844548159561693502659359617185244120367078079554186484126554")
    );

    Gen2 _1; _1 = 1;
    G1 A = _A.affine();
    G2 B = _B; B.affine();
    G2 C = -B;
    G2 P(B.x.conj() * XI_P_1_3, B.y.conj() * XI_P_1_2, _1, _1);
    G2 Q(B.x * XI_P2_1_3, B.y, _1, _1);
    G2 R = B;
    Gen2 r2 = B.y.sqr();
    Gen2 a, b, c;
    Gen12 ret; ret = 1;
    for (uint64_t i = 0; i < sizeof(sixuPlus2NAF); i++) {
        R = line_func_twice(A, R, a, b, c);
        if (i > 0) ret = ret.sqr();
        mul_line(a, b, c, ret);
        if (sixuPlus2NAF[i] == 0) continue;
        if (sixuPlus2NAF[i] > 0) R = line_func_add(A, R, B, r2, a, b, c);
        if (sixuPlus2NAF[i] < 0) R = line_func_add(A, R, C, r2, a, b, c);
        mul_line(a, b, c, ret);
    }
    R = line_func_add(A, R, P, P.y.sqr(), a, b, c);
    mul_line(a, b, c, ret);
    R = line_func_add(A, R, Q, Q.y.sqr(), a, b, c);
    mul_line(a, b, c, ret);
    return ret;
}
static Gen12 bn256check(const Gen12 &v)
{
    static const bigint U = big("4965661367192848881");
    Gen12 t0 = Gen12(-v.x, v.y) * v.inv();
    Gen12 t1 = t0 * t0.frob2();
    Gen12 t2 = t1.frob2();
    Gen12 t3 = t1.pow(U);
    Gen12 t4 = t3.pow(U);
    Gen12 t5 = t4.pow(U);
    Gen12 t6 = t4.conj();
    Gen12 t7 = (t5 * t5.frob()).conj().sqr() * (t3 * t4.frob()).conj() * t6;
    Gen12 t8 = ((t7 * t3.frob().conj() * t6).sqr() * t7 * t4.frob2()).sqr();
    return (t8 * t1.conj()).sqr() * t8 * t1.frob() * t2 * t2.frob();
}
#ifdef NATIVE_CRYPTO
static G1 bn256add(const G1& p1, const G1& p2);
static G1 bn256scalarmul(const G1& p1, const bigint& e);
static bool bn256pairing(const std::vector<G1> &a, const std::vector<G2> &b, uint64_t count);
#else
static G1 bn256add(const G1& p1, const G1& p2)
{
    return (p1 + p2).affine();
}
static G1 bn256scalarmul(const G1& p1, const bigint& e)
{
    return (p1 * e).affine();
}
static bool bn256pairing(const std::vector<G1> &a, const std::vector<G2> &b, uint64_t count)
{
    Gen12 prod; prod = 1;
    for (uint64_t i = 0; i < count; i++) {
        if (a[i].is_inf() || b[i].is_inf()) continue;
        prod *= miller(a[i], b[i]);
    }
    Gen12 value = bn256check(prod);
    return value.is_one();
}
#endif // NATIVE_CRYPTO

// ** rlp encoder/decoder **

// writes a non-leading zeros number into a buffer
// if buffer is null simply returns the required size
static uint64_t _throws(dump_nlzint)(uint256_t v, uint8_t *b, uint64_t s)
{
    uint64_t l = 32;
    while (l > 0 && v.byte(l - 1) == 0) l--;
    if (b != nullptr) {
        if (s < l) _throw0(INSUFFICIENT_SPACE);
        uint256_t::to(v, &b[s - l], l);
    }
    return l;
}
static uint64_t _throws(dump_nlzint)(uint256_t v)
{
    return _handles0(dump_nlzint)(v, nullptr, 0);
}

// parses a non-leading zeros number from a buffer
static uint256_t _throws(parse_nlzint)(const uint8_t *&b, uint64_t &s, uint64_t l)
{
    if (l == 0) return 0;
    if (s < l) _throw0(INVALID_ENCODING);
    if (b[0] == 0) _throw0(INVALID_ENCODING);
    if (l > 32) _throw0(INVALID_ENCODING);
    uint256_t v = uint256_t::from(b, l);
    b += l; s -= l;
    return v;
}
static uint256_t _throws(parse_nlzint)(const uint8_t *b, uint64_t s)
{
    return _handles0(parse_nlzint)(b, s, s);
}

// writes a variable length into a buffer
// if buffer is null simply returns the required size
static uint64_t _throws(dump_varlen)(uint8_t base, uint8_t c, uint64_t n, uint8_t *b, uint64_t s)
{
    if (base == 0x80 && c < 0x80 && n == 1) return 0;
    uint64_t size = 0;
    if (n > 55) {
        size += _handles0(dump_nlzint)(n, b, s - size);
        n = 55 + size;
    }
    if (b != nullptr) {
        if (s - size < 1) _throw0(INSUFFICIENT_SPACE);
        b[s - size - 1] = base + n;
    }
    size += 1;
    return size;
}

// parses a variable length from a buffer
static uint64_t _throws(parse_varlen)(const uint8_t *&b, uint64_t &s, bool &is_list)
{
    if (s < 1) _throw0(INVALID_ENCODING);
    uint8_t n = b[0];
    if (n < 0x80) { is_list = false; return 1; }
    b++; s--;
    if (n >= 0xc0 + 56) {
        uint256_t t = _handles0(parse_nlzint)(b, s, n - (0xc0 + 56) + 1);
        uint64_t l = t.cast64();
        if (l < 56) _throw0(INVALID_ENCODING);
        is_list = true; return l;
    }
    if (n >= 0xc0) { is_list = true; return n - 0xc0; }
    if (n >= 0x80 + 56) {
        uint256_t t = _handles0(parse_nlzint)(b, s, n - (0x80 + 56) + 1);
        uint64_t l = t.cast64();
        if (l < 56) _throw0(INVALID_ENCODING);
        is_list = false; return l;
    }
    if (n == 0x81) {
        if (s < 1) _throw0(INVALID_ENCODING);
        uint8_t n = b[0];
        if (n < 0x80) _throw0(INVALID_ENCODING);
    }
    is_list = false; return n - 0x80;
}

// simple rlp structure implemented in C style
struct rlp {
    bool is_list;
    uint64_t size;
    union {
        uint8_t *data;
        struct rlp *list;
    };
};

// releases the memory allocated for the rlp
static void free_rlp(struct rlp &rlp)
{
    if (rlp.is_list) {
        for (uint64_t i = 0; i < rlp.size; i++) free_rlp(rlp.list[i]);
        _delete(rlp.list);
        rlp.size = 0;
        rlp.list = nullptr;
    } else {
        _delete(rlp.data);
        rlp.size = 0;
        rlp.data = nullptr;
    }
}

// writes the rlp into a buffer
// if buffer is null simply returns the required size
static uint64_t _throws(dump_rlp)(const struct rlp &rlp, uint8_t *b, uint64_t s)
{
    uint64_t size = 0;
    if (rlp.is_list) {
        uint8_t c = 0;
        for (uint64_t i = 0; i < rlp.size; i++) {
            uint64_t j = rlp.size - (i + 1);
            size += _handles0(dump_rlp)(rlp.list[j], b, s - size);
        }
        size += _handles0(dump_varlen)(0xc0, c, size, b, s - size);
    } else {
        uint8_t c = rlp.size > 0 ? rlp.data[0] : 0;
        if (b != nullptr) {
            if (s < rlp.size) _throw0(INSUFFICIENT_SPACE);
            for (uint64_t i = 0; i < rlp.size; i++) {
                uint64_t j = (s - rlp.size) + i;
                b[j] = rlp.data[i];
            }
        }
        size += rlp.size;
        size += _handles0(dump_varlen)(0x80, c, size, b, s - size);
    }
    return size;
}

// parses an rlp from a buffer
static void _throws(parse_rlp)(const uint8_t *&b, uint64_t &s, struct rlp &rlp)
{
    bool is_list = false;
    uint64_t l = _handles(parse_varlen)(b, s, is_list);
    if (l > s) _throw(INVALID_ENCODING);
    const uint8_t *_b = b;
    uint64_t _s = l;
    b += l; s -= l;
    if (is_list) {
        uint64_t size = 0;
        struct rlp *list = nullptr;
        while (_s > 0) {
            _try({
                struct rlp *new_list = _new<struct rlp>(size + 1);
                for (uint64_t i = 0; i < size; i++) new_list[i] = list[i];
                _delete(list);
                list = new_list;
                _catches(parse_rlp)(_b, _s, list[size]);
            }, Error e, {
                for (uint64_t i = 0; i < size; i++) free_rlp(list[i]);
                _delete(list);
                _throw(e);
            })
            size++;
        }
        rlp.is_list = is_list;
        rlp.size = size;
        rlp.list = list;
    } else {
        uint64_t size = _s;
        uint8_t *data = _new<uint8_t>(size);
        for (uint64_t i = 0; i < size; i++) data[i] = _b[i];
        rlp.is_list = is_list;
        rlp.size = size;
        rlp.data = data;
    }
}

// ** releases **

// the chain id used by eip-155, hardcoded here
static const uint8_t CHAIN_ID = 1;

// the list of relevant upgrades/releases of the ethereum platform
enum Release : uint8_t {
    FRONTIER = 0,
    // FRONTIER_THAWING
    HOMESTEAD,
    // DAO
    TANGERINE_WHISTLE, // eip-150
    SPURIOUS_DRAGON,   // epi-155, eip-158
    BYZANTIUM,
    CONSTANTINOPLE,
    PETERSBURG,
    ISTANBUL,
    // MUIR_GLACIER
};

// table associating block number to release
static const uint32_t releaseforkblock[ISTANBUL+1] = {
    0000000, // 2015-07-30 FRONTIER
    1150000, // 2016-03-15 HOMESTEAD
    2463000, // 2016-10-18 TANGERINE_WHISTLE
    2675000, // 2016-11-23 SPURIOUS_DRAGON
    4370000, // 2017-10-16 BYZANTIUM
    7280000, // 2019-02-28 CONSTANTINOPLE
    7280000, // 2019-02-28 PETERSBURG
    9069000, // 2019-12-08 ISTANBUL
};

// gets the supported release at given block number
static Release get_release(uint64_t number)
{
    for (uint64_t i = ISTANBUL+1; i > 0; i--) {
        Release release = (Release)(i - 1);
        if (number >= releaseforkblock[release]) return release;
    }
    assert(false);
    return FRONTIER;
}

// ** transaction **

// transaction C-style declaration following its definition
struct txn {
    uint256_t nonce;
    uint256_t gasprice;
    uint256_t gaslimit;
    bool has_to;
    uint160_t to;
    uint256_t value;
    uint8_t *data;
    uint64_t data_size;
    bool is_signed;
    uint256_t v;
    uint256_t r;
    uint256_t s;
};

// encodes a transaction as rlp into a buffer
static uint64_t _throws(encode_txn)(const struct txn &txn, uint8_t *buffer, uint64_t size)
{
    uint64_t result;
    struct rlp rlp;
    rlp.is_list = true;
    rlp.size = txn.is_signed ? 9 : 6;
    rlp.list = _new<struct rlp>(rlp.size);
    for (uint64_t i = 0; i < rlp.size; i++) {
        rlp.list[i].is_list = false;
        rlp.list[i].size = 0;
        rlp.list[i].data = nullptr;
    }
    _try({
        rlp.list[0].size = _catches(dump_nlzint)(txn.nonce);
        rlp.list[1].size = _catches(dump_nlzint)(txn.gasprice);
        rlp.list[2].size = _catches(dump_nlzint)(txn.gaslimit);
        rlp.list[3].size = txn.has_to ? 20 : 0;
        rlp.list[4].size = _catches(dump_nlzint)(txn.value);
        rlp.list[5].size = txn.data_size;
        if (txn.is_signed) {
            rlp.list[6].size = _catches(dump_nlzint)(txn.v);
            rlp.list[7].size = _catches(dump_nlzint)(txn.r);
            rlp.list[8].size = _catches(dump_nlzint)(txn.s);
        }
        for (uint64_t i = 0; i < rlp.size; i++) {
            if (rlp.list[i].size > 0) {
                rlp.list[i].data = _new<uint8_t>(rlp.list[i].size);
            }
        }
        _catches(dump_nlzint)(txn.nonce, rlp.list[0].data, rlp.list[0].size);
        _catches(dump_nlzint)(txn.gasprice, rlp.list[1].data, rlp.list[1].size);
        _catches(dump_nlzint)(txn.gaslimit, rlp.list[2].data, rlp.list[2].size);
        if (txn.has_to) {
            uint256_t::to(txn.to, rlp.list[3].data, rlp.list[3].size);
        }
        _catches(dump_nlzint)(txn.value, rlp.list[4].data, rlp.list[4].size);
        for (uint64_t i = 0; i < txn.data_size; i++) rlp.list[5].data[i] = txn.data[i];
        if (txn.is_signed) {
            _catches(dump_nlzint)(txn.v, rlp.list[6].data, rlp.list[6].size);
            _catches(dump_nlzint)(txn.r, rlp.list[7].data, rlp.list[7].size);
            _catches(dump_nlzint)(txn.s, rlp.list[8].data, rlp.list[8].size);
        }
        result = _catches(dump_rlp)(rlp, buffer, size);
        free_rlp(rlp);
    }, Error e, {
        free_rlp(rlp);
        _throw0(e);
    })
    return result;
}
static uint64_t _throws(encode_txn)(const struct txn &txn)
{
    return _handles0(encode_txn)(txn, nullptr, 0);
}

// decodes a transaction as rlp from a buffer
static void _throws(decode_txn)(const uint8_t *buffer, uint64_t size, struct txn &txn)
{
    struct rlp rlp = {false, 0, {nullptr}};
    _handles(parse_rlp)(buffer, size, rlp);
    txn.data = nullptr;
    _try({
        if (size > 0) _trythrow(INVALID_TRANSACTION);
        if (rlp.size != 6 && rlp.size != 9) _trythrow(INVALID_TRANSACTION);
        if (!rlp.is_list) _trythrow(INVALID_TRANSACTION);
        bool invalid = false;
        for (uint64_t i = 0; i < rlp.size; i++) {
            if (rlp.list[i].is_list) { invalid = true; break; }
        }
        if (invalid) _trythrow(INVALID_TRANSACTION);
        txn.nonce = _catches(parse_nlzint)(rlp.list[0].data, rlp.list[0].size);
        txn.gasprice = _catches(parse_nlzint)(rlp.list[1].data, rlp.list[1].size);
        txn.gaslimit = _catches(parse_nlzint)(rlp.list[2].data, rlp.list[2].size);
        txn.has_to = rlp.list[3].size > 0;
        if (txn.has_to) {
            if (rlp.list[3].size != 20) _trythrow(INVALID_TRANSACTION);
            txn.to = uint160_t::from(rlp.list[3].data, rlp.list[3].size);
        }
        txn.value = _catches(parse_nlzint)(rlp.list[4].data, rlp.list[4].size);
        txn.data_size = rlp.list[5].size;
        txn.data = _new<uint8_t>(txn.data_size);
        for (uint64_t i = 0; i < txn.data_size; i++) txn.data[i] = rlp.list[5].data[i];
        txn.is_signed = rlp.size > 6;
        if (txn.is_signed) {
            txn.v = _catches(parse_nlzint)(rlp.list[6].data, rlp.list[6].size);
            txn.r = _catches(parse_nlzint)(rlp.list[7].data, rlp.list[7].size);
            txn.s = _catches(parse_nlzint)(rlp.list[8].data, rlp.list[8].size);
        }
    }, Error e, {
        _delete(txn.data);
        free_rlp(rlp);
        _throw(e);
    })
    free_rlp(rlp);
}

// verifies is transaction is signed and its parameters v, s
// it does not verify r, s for P bounds as that gets performed by ecrecover
static void _throws(verify_txn)(Release release, struct txn &txn)
{
    if (!txn.is_signed) _throw(INVALID_TRANSACTION);
    if (txn.v != 27 && txn.v != 28) {
        if (release < SPURIOUS_DRAGON) _throw(INVALID_TRANSACTION);
        if (txn.v < 35) _throw(INVALID_TRANSACTION); // assumes CHAIN_ID >= 0
        uint256_t chainid = (txn.v - 35) / 2;
        if (chainid != CHAIN_ID) _throw(INVALID_TRANSACTION);
    }
    if (release >= HOMESTEAD) {
        if (2*uint256_t::to_big(txn.s) > G0::P()) _throw(INVALID_TRANSACTION);
    }
}

// calculates the sha3 hash for the signed transaction without its signature
static uint256_t _throws(hash_txn)(struct txn &txn)
{
    assert(txn.is_signed);
    assert(txn.v == 27 || txn.v == 28 || txn.v == 35 + 2 * CHAIN_ID || txn.v == 36 + 2 * CHAIN_ID);
    uint256_t v = txn.v;
    uint256_t r = txn.r;
    uint256_t s = txn.s;
    txn.is_signed = v > 28;
    txn.v = CHAIN_ID;
    txn.r = 0;
    txn.s = 0;
    uint64_t unsigned_size = _handles0(encode_txn)(txn);
    local<uint8_t> unsigned_buffer_l(unsigned_size); uint8_t *unsigned_buffer = unsigned_buffer_l.data;
    _handles0(encode_txn)(txn, unsigned_buffer, unsigned_size);
    uint256_t h = sha3(unsigned_buffer, unsigned_size);
    txn.is_signed = true;
    txn.v = v > 28 ? v - (8 + 2 * CHAIN_ID) : v;
    txn.r = r;
    txn.s = s;
    assert(txn.v == 27 || txn.v == 28);
    return h;
}

// ** contract id **

// encodes a contract id as rlp into a buffer
// used to calculate an address for a new contract which is a hash of
// an address and a nonce in rpl form
static uint64_t _throws(encode_cid)(const uint256_t &from, const uint256_t &nonce, uint8_t *buffer, uint64_t size)
{
    uint64_t result;
    struct rlp rlp;
    rlp.is_list = true;
    rlp.size = 2;
    rlp.list = _new<struct rlp>(rlp.size);
    for (uint64_t i = 0; i < rlp.size; i++) {
        rlp.list[i].is_list = false;
        rlp.list[i].size = 0;
        rlp.list[i].data = nullptr;
    }
    _try({
        rlp.list[0].size = _catches(dump_nlzint)(from);
        rlp.list[1].size = _catches(dump_nlzint)(nonce);
        for (uint64_t i = 0; i < rlp.size; i++) {
            if (rlp.list[i].size > 0) {
                rlp.list[i].data = _new<uint8_t>(rlp.list[i].size);
            }
        }
        _catches(dump_nlzint)(from, rlp.list[0].data, rlp.list[0].size);
        _catches(dump_nlzint)(nonce, rlp.list[1].data, rlp.list[1].size);
        result = _catches(dump_rlp)(rlp, buffer, size);
        free_rlp(rlp);
    }, Error e, {
        free_rlp(rlp);
        _throw0(e);
    })
    return result;
}
static uint64_t _throws(encode_cid)(const uint256_t &from, const uint256_t &nonce)
{
    return _handles0(encode_cid)(from, nonce, nullptr, 0);
}

// generates a contract address given caller and nonce (CREATE method)
static uint160_t _throws(gen_contract_address)(const uint160_t &from, const uint256_t &nonce)
{
    uint64_t size = _handles0(encode_cid)((uint256_t)from, nonce);
    local<uint8_t> buffer_l(size); uint8_t *buffer = buffer_l.data;
    _handles0(encode_cid)((uint256_t)from, nonce, buffer, size);
    return (uint160_t)sha3(buffer, size);
}

// generates a contract address given caller, salt, and code hash (CREATE2 method)
static uint160_t gen_contract_address(const uint160_t &from, const uint256_t &salt, const uint256_t &hash)
{
    uint64_t size = 1 + 20 + 32 + 32;
    local<uint8_t> buffer_l(size); uint8_t *buffer = buffer_l.data;
    uint64_t offset = 0;
    buffer[offset] = 0xff; offset += 1;
    uint160_t::to(from, &buffer[offset]); offset += 20;
    uint256_t::to(salt, &buffer[offset]); offset += 32;
    uint256_t::to(hash, &buffer[offset]); offset += 32;
    return (uint160_t)sha3(buffer, size);
}

// ** gas **

// types of gas expenditure constants
// used to index tables with actual gas cost
enum GasType : uint8_t {
    GasNone = 0,
    GasQuickStep,
    GasFastestStep,
    GasFastStep,
    GasMidStep,
    GasSlowStep,
    GasExtStep,
    GasExp,
    GasExpByte,
    GasSha3,
    GasSha3Word,
    GasBalance,
    GasExtcodeSize,
    GasExtcodeCopy,
    GasExtcodeHash,
    GasSload,
    GasSstoreLegacySet,
    GasSstoreLegacyClear,
    GasSstoreLegacyReset,
    GasSstoreLegacyRefund,
    GasSstoreSentry,
    GasSstoreNoop,
    GasSstoreInit,
    GasSstoreClean,
    GasSstoreDirty,
    GasSstoreInitRefund,
    GasSstoreCleanRefund,
    GasSstoreClearRefund,
    GasJumpdest,
    GasCreate,
    GasCreateData,
    GasCall,
    GasCallNewAccount,
    GasCallValueTransfer,
    GasCallValueTransferStipend,
    GasCreate2,
    GasSelfDestruct,
    GasSelfDestructNewAccount,
    GasSelfDestructRefund,
    GasMemory,
    GasMemoryDiv,
    GasCopy,
    GasLog,
    GasLogTopic,
    GasLogData,
    GasEcRecover,
    GasSha256,
    GasSha256Word,
    GasRipemd160,
    GasRipemd160Word,
    GasDataCopy,
    GasDataCopyWord,
    GasBigModExpDiv,
    GasBn256Add,
    GasBn256ScalarMul,
    GasBn256Pairing,
    GasBn256PairingPoint,
    GasBlake2f,
    GasBlake2fRound,
    GasTxMessageCall,
    GasTxContractCreation,
    GasTxDataZero,
    GasTxDataNonZero,
};

// gas cost contants
// declares both the original values and their new values (for some of them)
// given platform upgrades/new releases
enum GasCost : uint32_t {
    _GasNone = 0,
    _GasQuickStep = 2,
    _GasFastestStep = 3,
    _GasFastStep = 5,
    _GasMidStep = 8,
    _GasSlowStep = 10,
    _GasExtStep = 20,
    _GasExp = 10,
    _GasExpByte = 10,
    _GasSha3 = 30,
    _GasSha3Word = 6,
    _GasBalance = 20,
    _GasExtcodeSize = 20,
    _GasExtcodeCopy = 20,
    _GasExtcodeHash = 400,
    _GasSload = 50,
    _GasSstoreLegacySet = 20000,
    _GasSstoreLegacyClear = 5000,
    _GasSstoreLegacyReset = 5000,
    _GasSstoreLegacyRefund = 15000,
    _GasSstoreSentry = 0,
    _GasSstoreNoop = 200,
    _GasSstoreInit = 20000,
    _GasSstoreClean = 5000,
    _GasSstoreDirty = 200,
    _GasSstoreInitRefund = 19800,
    _GasSstoreCleanRefund = 4800,
    _GasSstoreClearRefund = 15000,
    _GasJumpdest = 1,
    _GasCreate = 32000,
    _GasCreateData = 200,
    _GasCall = 40,
    _GasCallNewAccount = 25000,
    _GasCallValueTransfer = 9000,
    _GasCallValueTransferStipend = 2300,
    _GasCreate2 = 32000,
    _GasSelfDestruct = 5000,
    _GasSelfDestructNewAccount = 25000,
    _GasSelfDestructRefund = 24000,
    _GasMemory = 3,
    _GasMemoryDiv = 512,
    _GasCopy = 3,
    _GasLog = 375,
    _GasLogTopic = 375,
    _GasLogData = 8,
    _GasEcRecover = 3000,
    _GasSha256 = 60,
    _GasSha256Word = 12,
    _GasRipemd160 = 600,
    _GasRipemd160Word = 120,
    _GasDataCopy = 15,
    _GasDataCopyWord = 3,
    _GasBigModExpDiv = 20,
    _GasBn256Add = 500,
    _GasBn256ScalarMul = 40000,
    _GasBn256Pairing = 100000,
    _GasBn256PairingPoint = 80000,
    _GasBlake2f = 0,
    _GasBlake2fRound = 1,
    _GasTxMessageCall = 21000,
    _GasTxContractCreation = 21000,
    _GasTxDataZero = 4,
    _GasTxDataNonZero = 68,

    // homestead
    _GasTxContractCreation_Homestead = 53000,

    // tangerine whistle
    _GasBalance_TangerineWhistle = 400,
    _GasExtcodeSize_TangerineWhistle = 700,
    _GasExtcodeCopy_TangerineWhistle = 700,
    _GasSload_TangerineWhistle = 200,
    _GasCall_TangerineWhistle = 700,

    // spurious dragon
    _GasExpByte_SpuriousDragon = 50,

    // istanbul
    _GasBalance_Istanbul = 700,
    _GasExtcodeHash_Istanbul = 700,
    _GasSload_Istanbul = 800,
    _GasSstoreSentry_Istanbul = 2300,
    _GasSstoreNoop_Istanbul = 800,
    _GasSstoreInit_Istanbul = 20000,
    _GasSstoreClean_Istanbul = 5000,
    _GasSstoreDirty_Istanbul = 800,
    _GasSstoreInitRefund_Istanbul = 19200,
    _GasSstoreCleanRefund_Istanbul = 4200,
    _GasSstoreClearRefund_Istanbul = 15000,
    _GasBn256Add_Istanbul = 150,
    _GasBn256ScalarMul_Istanbul = 6000,
    _GasBn256Pairing_Istanbul = 45000,
    _GasBn256PairingPoint_Istanbul = 34000,
    _GasTxDataNonZero_Istanbul = 16,
};

// ** opcodes **

// max call depth in the EVM
static const uint16_t CALL_DEPTH = 1024;

// max code size in the EVM (enforced after spurious dragon)
static const uint16_t CODE_SIZE = 24576;

// max frame stack
static const uint16_t STACK_SIZE = 1024;

// handy constant identifying empty bytecode
static const uint256_t EMPTY_CODEHASH = sha3(nullptr, 0);

// the list of opcodes
enum Opcode : uint8_t {
    STOP = 0x00, ADD, MUL, SUB, DIV, SDIV, MOD, SMOD,
    ADDMOD, MULMOD, EXP, SIGNEXTEND,
    // 0x0c .. 0x0f
    LT = 0x10, GT, SLT, SGT, EQ, ISZERO, AND, OR,
    XOR, NOT, BYTE, SHL, SHR, SAR,
    // 0x1e .. 0x1f
    SHA3 = 0x20,
    // 0x21 .. 0x2f
    ADDRESS = 0x30, BALANCE, ORIGIN, CALLER, CALLVALUE, CALLDATALOAD, CALLDATASIZE, CALLDATACOPY,
    CODESIZE, CODECOPY, GASPRICE, EXTCODESIZE, EXTCODECOPY, RETURNDATASIZE, RETURNDATACOPY, EXTCODEHASH,
    BLOCKHASH, COINBASE, TIMESTAMP, NUMBER, DIFFICULTY, GASLIMIT, CHAINID, SELFBALANCE,
    // 0x48 .. 0x4f
    POP = 0x50, MLOAD, MSTORE, MSTORE8, SLOAD, SSTORE, JUMP, JUMPI,
    PC, MSIZE, GAS, JUMPDEST,
    // 0x5c .. 0x5f
    PUSH1 = 0x60, PUSH2, PUSH3, PUSH4, PUSH5, PUSH6, PUSH7, PUSH8,
    PUSH9, PUSH10, PUSH11, PUSH12, PUSH13, PUSH14, PUSH15, PUSH16,
    PUSH17, PUSH18, PUSH19, PUSH20, PUSH21, PUSH22, PUSH23, PUSH24,
    PUSH25, PUSH26, PUSH27, PUSH28, PUSH29, PUSH30, PUSH31, PUSH32,
    DUP1, DUP2, DUP3, DUP4, DUP5, DUP6, DUP7, DUP8,
    DUP9, DUP10, DUP11, DUP12, DUP13, DUP14, DUP15, DUP16,
    SWAP1, SWAP2, SWAP3, SWAP4, SWAP5, SWAP6, SWAP7, SWAP8,
    SWAP9, SWAP10, SWAP11, SWAP12, SWAP13, SWAP14, SWAP15, SWAP16,
    LOG0, LOG1, LOG2, LOG3, LOG4,
    // 0xa5 .. 0xef
    CREATE = 0xf0, CALL, CALLCODE, RETURN, DELEGATECALL, CREATE2,
    // 0xf6 .. 0xf9
    STATICCALL = 0xfa,
    // 0xfb .. 0xfc
    REVERT = 0xfd,
    // 0xfe .. 0xfe
    SELFDESTRUCT = 0xff,
};

#ifndef NDEBUG
// an associated opcode string table for debbuging
static const char *opcodes[256] = {
    "STOP", "ADD", "MUL", "SUB", "DIV", "SDIV", "MOD", "SMOD",
    "ADDMOD", "MULMOD", "EXP", "SIGNEXTEND", "0x0c", "0x0d", "0x0e", "0x0f",
    "LT", "GT", "SLT", "SGT", "EQ", "ISZERO", "AND", "OR",
    "XOR", "NOT", "BYTE", "SHL", "SHR", "SAR", "0x1e", "0x1f",
    "SHA3", "0x21", "0x22", "0x23", "0x24", "0x25", "0x26", "0x27",
    "0x28", "0x29", "0x2a", "0x2b", "0x2c", "0x2d", "0x2e", "0x2f",
    "ADDRESS", "BALANCE", "ORIGIN", "CALLER", "CALLVALUE", "CALLDATALOAD", "CALLDATASIZE", "CALLDATACOPY",
    "CODESIZE", "CODECOPY", "GASPRICE", "EXTCODESIZE", "EXTCODECOPY", "RETURNDATASIZE", "RETURNDATACOPY", "EXTCODEHASH",
    "BLOCKHASH", "COINBASE", "TIMESTAMP", "NUMBER", "DIFFICULTY", "GASLIMIT", "CHAINID", "SELFBALANCE",
    "0x48", "0x49", "0x4a", "0x4b", "0x4c", "0x4d", "0x4e", "0x4f",
    "POP", "MLOAD", "MSTORE", "MSTORE8", "SLOAD", "SSTORE", "JUMP", "JUMPI",
    "PC", "MSIZE", "GAS", "JUMPDEST", "0x5c", "0x5d", "0x5e", "0x5f",
    "PUSH1", "PUSH2", "PUSH3", "PUSH4", "PUSH5", "PUSH6", "PUSH7", "PUSH8",
    "PUSH9", "PUSH10", "PUSH11", "PUSH12", "PUSH13", "PUSH14", "PUSH15", "PUSH16",
    "PUSH17", "PUSH18", "PUSH19", "PUSH20", "PUSH21", "PUSH22", "PUSH23", "PUSH24",
    "PUSH25", "PUSH26", "PUSH27", "PUSH28", "PUSH29", "PUSH30", "PUSH31", "PUSH32",
    "DUP1", "DUP2", "DUP3", "DUP4", "DUP5", "DUP6", "DUP7", "DUP8",
    "DUP9", "DUP10", "DUP11", "DUP12", "DUP13", "DUP14", "DUP15", "DUP16",
    "SWAP1", "SWAP2", "SWAP3", "SWAP4", "SWAP5", "SWAP6", "SWAP7", "SWAP8",
    "SWAP9", "SWAP10", "SWAP11", "SWAP12", "SWAP13", "SWAP14", "SWAP15", "SWAP16",
    "LOG0", "LOG1", "LOG2", "LOG3", "LOG4", "0xa5", "0xa6", "0xa7",
    "0xa8", "0xa9", "0xaa", "0xab", "0xac", "0xad", "0xae", "0xaf",
    "0xb0", "0xb1", "0xb2", "0xb3", "0xb4", "0xb5", "0xb6", "0xb7",
    "0xb8", "0xb9", "0xba", "0xbb", "0xbc", "0xbd", "0xbe", "0xbf",
    "0xc0", "0xc1", "0xc2", "0xc3", "0xc4", "0xc5", "0xc6", "0xc7",
    "0xc8", "0xc9", "0xca", "0xcb", "0xcc", "0xcd", "0xce", "0xcf",
    "0xd0", "0xd1", "0xd2", "0xd3", "0xd4", "0xd5", "0xd6", "0xd7",
    "0xd8", "0xd9", "0xda", "0xdb", "0xdc", "0xdd", "0xde", "0xdf",
    "0xe0", "0xe1", "0xe2", "0xe3", "0xe4", "0xe5", "0xe6", "0xe7",
    "0xe8", "0xe9", "0xea", "0xeb", "0xec", "0xed", "0xee", "0xef",
    "CREATE", "CALL", "CALLCODE", "RETURN", "DELEGATECALL", "CREATE2", "0xf6", "0xf7",
    "0xf8", "0xf9", "STATICCALL", "0xfb", "0xfc", "REVERT", "0xfe", "SELFDESTRUCT",
};
#endif // NDEBUG

// frame stack bounds (min and max values) for every opcode
// used to quickly check for opcode valitidy reqgarding the stack
static const uint16_t stackbounds[256][2] = {
    { 0, STACK_SIZE - (0 - 0) }, // STOP
    { 2, STACK_SIZE - (1 - 2) }, // ADD
    { 2, STACK_SIZE - (1 - 2) }, // MUL
    { 2, STACK_SIZE - (1 - 2) }, // SUB
    { 2, STACK_SIZE - (1 - 2) }, // DIV
    { 2, STACK_SIZE - (1 - 2) }, // SDIV
    { 2, STACK_SIZE - (1 - 2) }, // MOD
    { 2, STACK_SIZE - (1 - 2) }, // SMOD
    { 3, STACK_SIZE - (1 - 3) }, // ADDMOD
    { 3, STACK_SIZE - (1 - 3) }, // MULMOD
    { 2, STACK_SIZE - (1 - 2) }, // EXP
    { 2, STACK_SIZE - (1 - 2) }, // SIGNEXTEND
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 2, STACK_SIZE - (1 - 2) }, // LT
    { 2, STACK_SIZE - (1 - 2) }, // GT
    { 2, STACK_SIZE - (1 - 2) }, // SLT
    { 2, STACK_SIZE - (1 - 2) }, // SGT
    { 2, STACK_SIZE - (1 - 2) }, // EQ
    { 1, STACK_SIZE - (1 - 1) }, // ISZERO
    { 2, STACK_SIZE - (1 - 2) }, // AND
    { 2, STACK_SIZE - (1 - 2) }, // OR
    { 2, STACK_SIZE - (1 - 2) }, // XOR
    { 1, STACK_SIZE - (1 - 1) }, // NOT
    { 2, STACK_SIZE - (1 - 2) }, // BYTE
    { 2, STACK_SIZE - (1 - 2) }, // SHL
    { 2, STACK_SIZE - (1 - 2) }, // SHR
    { 2, STACK_SIZE - (1 - 2) }, // SAR
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 2, STACK_SIZE - (1 - 2) }, // SHA3
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (1 - 0) }, // ADDRESS
    { 1, STACK_SIZE - (1 - 1) }, // BALANCE
    { 0, STACK_SIZE - (1 - 0) }, // ORIGIN
    { 0, STACK_SIZE - (1 - 0) }, // CALLER
    { 0, STACK_SIZE - (1 - 0) }, // CALLVALUE
    { 1, STACK_SIZE - (1 - 1) }, // CALLDATALOAD
    { 0, STACK_SIZE - (1 - 0) }, // CALLDATASIZE
    { 3, STACK_SIZE - (0 - 3) }, // CALLDATACOPY
    { 0, STACK_SIZE - (1 - 0) }, // CODESIZE
    { 3, STACK_SIZE - (0 - 3) }, // CODECOPY
    { 0, STACK_SIZE - (1 - 0) }, // GASPRICE
    { 1, STACK_SIZE - (1 - 1) }, // EXTCODESIZE
    { 4, STACK_SIZE - (0 - 4) }, // EXTCODECOPY
    { 0, STACK_SIZE - (1 - 0) }, // RETURNDATASIZE
    { 3, STACK_SIZE - (0 - 3) }, // RETURNDATACOPY
    { 1, STACK_SIZE - (1 - 1) }, // EXTCODEHASH
    { 1, STACK_SIZE - (1 - 1) }, // BLOCKHASH
    { 0, STACK_SIZE - (1 - 0) }, // COINBASE
    { 0, STACK_SIZE - (1 - 0) }, // TIMESTAMP
    { 0, STACK_SIZE - (1 - 0) }, // NUMBER
    { 0, STACK_SIZE - (1 - 0) }, // DIFFICULTY
    { 0, STACK_SIZE - (1 - 0) }, // GASLIMIT
    { 0, STACK_SIZE - (1 - 0) }, // CHAINID
    { 0, STACK_SIZE - (1 - 0) }, // SELFBALANCE
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 1, STACK_SIZE - (0 - 1) }, // POP
    { 1, STACK_SIZE - (1 - 1) }, // MLOAD
    { 2, STACK_SIZE - (0 - 2) }, // MSTORE
    { 2, STACK_SIZE - (0 - 2) }, // MSTORE8
    { 1, STACK_SIZE - (1 - 1) }, // SLOAD
    { 2, STACK_SIZE - (0 - 2) }, // SSTORE
    { 1, STACK_SIZE - (0 - 1) }, // JUMP
    { 2, STACK_SIZE - (0 - 2) }, // JUMPI
    { 0, STACK_SIZE - (1 - 0) }, // PC
    { 0, STACK_SIZE - (1 - 0) }, // MSIZE
    { 0, STACK_SIZE - (1 - 0) }, // GAS
    { 0, STACK_SIZE - (0 - 0) }, // JUMPDEST
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (1 - 0) }, // PUSH1
    { 0, STACK_SIZE - (1 - 0) }, // PUSH2
    { 0, STACK_SIZE - (1 - 0) }, // PUSH3
    { 0, STACK_SIZE - (1 - 0) }, // PUSH4
    { 0, STACK_SIZE - (1 - 0) }, // PUSH5
    { 0, STACK_SIZE - (1 - 0) }, // PUSH6
    { 0, STACK_SIZE - (1 - 0) }, // PUSH7
    { 0, STACK_SIZE - (1 - 0) }, // PUSH8
    { 0, STACK_SIZE - (1 - 0) }, // PUSH9
    { 0, STACK_SIZE - (1 - 0) }, // PUSH10
    { 0, STACK_SIZE - (1 - 0) }, // PUSH11
    { 0, STACK_SIZE - (1 - 0) }, // PUSH12
    { 0, STACK_SIZE - (1 - 0) }, // PUSH13
    { 0, STACK_SIZE - (1 - 0) }, // PUSH14
    { 0, STACK_SIZE - (1 - 0) }, // PUSH15
    { 0, STACK_SIZE - (1 - 0) }, // PUSH16
    { 0, STACK_SIZE - (1 - 0) }, // PUSH17
    { 0, STACK_SIZE - (1 - 0) }, // PUSH18
    { 0, STACK_SIZE - (1 - 0) }, // PUSH19
    { 0, STACK_SIZE - (1 - 0) }, // PUSH20
    { 0, STACK_SIZE - (1 - 0) }, // PUSH21
    { 0, STACK_SIZE - (1 - 0) }, // PUSH22
    { 0, STACK_SIZE - (1 - 0) }, // PUSH23
    { 0, STACK_SIZE - (1 - 0) }, // PUSH24
    { 0, STACK_SIZE - (1 - 0) }, // PUSH25
    { 0, STACK_SIZE - (1 - 0) }, // PUSH26
    { 0, STACK_SIZE - (1 - 0) }, // PUSH27
    { 0, STACK_SIZE - (1 - 0) }, // PUSH28
    { 0, STACK_SIZE - (1 - 0) }, // PUSH29
    { 0, STACK_SIZE - (1 - 0) }, // PUSH30
    { 0, STACK_SIZE - (1 - 0) }, // PUSH31
    { 0, STACK_SIZE - (1 - 0) }, // PUSH32
    { 1, STACK_SIZE - (2 - 1) }, // DUP1
    { 2, STACK_SIZE - (3 - 2) }, // DUP2
    { 3, STACK_SIZE - (4 - 3) }, // DUP3
    { 4, STACK_SIZE - (5 - 4) }, // DUP4
    { 5, STACK_SIZE - (6 - 5) }, // DUP5
    { 6, STACK_SIZE - (7 - 6) }, // DUP6
    { 7, STACK_SIZE - (8 - 7) }, // DUP7
    { 8, STACK_SIZE - (9 - 8) }, // DUP8
    { 9, STACK_SIZE - (10- 9) }, // DUP9
    { 10,STACK_SIZE - (11-10) }, // DUP10
    { 11,STACK_SIZE - (12-11) }, // DUP11
    { 12,STACK_SIZE - (13-12) }, // DUP12
    { 13,STACK_SIZE - (14-13) }, // DUP13
    { 14,STACK_SIZE - (15-14) }, // DUP14
    { 15,STACK_SIZE - (16-15) }, // DUP15
    { 16,STACK_SIZE - (17-16) }, // DUP16
    { 2, STACK_SIZE - (2 - 2) }, // SWAP1
    { 3, STACK_SIZE - (3 - 3) }, // SWAP2
    { 4, STACK_SIZE - (4 - 4) }, // SWAP3
    { 5, STACK_SIZE - (5 - 5) }, // SWAP4
    { 6, STACK_SIZE - (6 - 6) }, // SWAP5
    { 7, STACK_SIZE - (7 - 7) }, // SWAP6
    { 8, STACK_SIZE - (8 - 8) }, // SWAP7
    { 9, STACK_SIZE - (9 - 9) }, // SWAP8
    { 10,STACK_SIZE - (10-10) }, // SWAP9
    { 11,STACK_SIZE - (11-11) }, // SWAP10
    { 12,STACK_SIZE - (12-12) }, // SWAP11
    { 13,STACK_SIZE - (13-13) }, // SWAP12
    { 14,STACK_SIZE - (14-14) }, // SWAP13
    { 15,STACK_SIZE - (15-15) }, // SWAP14
    { 16,STACK_SIZE - (16-16) }, // SWAP15
    { 17,STACK_SIZE - (17-17) }, // SWAP16
    { 2, STACK_SIZE - (0 - 2) }, // LOG0
    { 3, STACK_SIZE - (0 - 3) }, // LOG1
    { 4, STACK_SIZE - (0 - 4) }, // LOG2
    { 5, STACK_SIZE - (0 - 5) }, // LOG3
    { 6, STACK_SIZE - (0 - 6) }, // LOG4
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 3, STACK_SIZE - (1 - 3) }, // CREATE
    { 7, STACK_SIZE - (1 - 7) }, // CALL
    { 7, STACK_SIZE - (1 - 7) }, // CALLCODE
    { 2, STACK_SIZE - (0 - 2) }, // RETURN
    { 6, STACK_SIZE - (1 - 6) }, // DELEGATECALL
    { 4, STACK_SIZE - (1 - 4) }, // CREATE2
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 6, STACK_SIZE - (1 - 6) }, // STATICCALL
    { 0, STACK_SIZE - (0 - 0) },
    { 0, STACK_SIZE - (0 - 0) },
    { 2, STACK_SIZE - (0 - 2) }, // REVERT
    { 0, STACK_SIZE - (0 - 0) },
    { 1, STACK_SIZE - (0 - 1) }, // SELFDESTRUCT
};

// opcode to gas mapping table
// handles gas consumption when its calculation is constant
static const GasType constgas[256] = {
    // STOP, ADD, MUL, SUB, DIV, SDIV, MOD, SMOD
    GasNone, GasFastestStep, GasFastStep, GasFastestStep, GasFastStep, GasFastStep, GasFastStep, GasFastStep,
    // ADDMOD, MULMOD, EXP, SIGNEXTEND
    GasMidStep, GasMidStep, GasExp, GasFastStep, GasNone, GasNone, GasNone, GasNone,
    // LT, GT, SLT, SGT, EQ, ISZERO, AND, OR
    GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep,
    // XOR, NOT, BYTE, SHL, SHR, SAR
    GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasNone, GasNone,
    // SHA3
    GasSha3, GasNone, GasNone, GasNone, GasNone, GasNone, GasNone, GasNone,
    GasNone, GasNone, GasNone, GasNone, GasNone, GasNone, GasNone, GasNone,
    // ADDRESS, BALANCE, ORIGIN, CALLER, CALLVALUE, CALLDATALOAD, CALLDATASIZE. CALLDATACOPY
    GasQuickStep, GasBalance, GasQuickStep, GasQuickStep, GasQuickStep, GasFastestStep, GasQuickStep, GasFastestStep,
    // CODESIZE, CODECOPY, GASPRICE, EXTCODESIZE, EXTCODECOPY, RETURNDATASIZE, RETURNDATACOPY, EXTCODEHASH
    GasQuickStep, GasFastestStep, GasQuickStep, GasExtcodeSize, GasExtcodeCopy, GasQuickStep, GasFastestStep, GasExtcodeHash,
    // BLOCKHASH, COINBASE, TIMESTAMP, NUMBER, DIFFICULTY, GASLIMIT, CHAINID, SELFBALANCE
    GasExtStep, GasQuickStep, GasQuickStep, GasQuickStep, GasQuickStep, GasQuickStep, GasQuickStep, GasFastStep,
    GasNone, GasNone, GasNone, GasNone, GasNone, GasNone, GasNone, GasNone,
    // POP, MLOAD, MSTORE, MSTORE8, SLOAD, SSTORE, JUMP, JUMPI
    GasQuickStep, GasFastestStep, GasFastestStep, GasFastestStep, GasSload, GasNone, GasMidStep, GasSlowStep,
    // PC, MSIZE, GAS, JUMPDEST
    GasQuickStep, GasQuickStep, GasQuickStep, GasJumpdest, GasNone, GasNone, GasNone, GasNone,
    // PUSH1, PUSH2, PUSH3, PUSH4, PUSH5, PUSH6, PUSH7, PUSH8
    GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep,
    // PUSH9, PUSH10, PUSH11, PUSH12, PUSH13, PUSH14, PUSH15, PUSH16
    GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep,
    // PUSH17, PUSH18, PUSH19, PUSH20, PUSH21, PUSH22, PUSH23, PUSH24
    GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep,
    // PUSH25, PUSH26, PUSH27, PUSH28, PUSH29, PUSH30, PUSH31, PUSH32
    GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep,
    // DUP1, DUP2, DUP3, DUP4, DUP5, DUP6, DUP7, DUP8
    GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep,
    // DUP9, DUP10, DUP11, DUP12, DUP13, DUP14, DUP15, DUP16
    GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep,
    // SWAP1, SWAP2, SWAP3, SWAP4, SWAP5, SWAP6, SWAP7, SWAP8
    GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep,
    // SWAP9, SWAP10, SWAP11, SWAP12, SWAP13, SWAP14, SWAP15, SWAP16
    GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep, GasFastestStep,
    // LOG0, LOG1, LOG2, LOG3, LOG4
    GasNone, GasNone, GasNone, GasNone, GasNone, GasNone, GasNone, GasNone,
    GasNone, GasNone, GasNone, GasNone, GasNone, GasNone, GasNone, GasNone,
    GasNone, GasNone, GasNone, GasNone, GasNone, GasNone, GasNone, GasNone,
    GasNone, GasNone, GasNone, GasNone, GasNone, GasNone, GasNone, GasNone,
    GasNone, GasNone, GasNone, GasNone, GasNone, GasNone, GasNone, GasNone,
    GasNone, GasNone, GasNone, GasNone, GasNone, GasNone, GasNone, GasNone,
    GasNone, GasNone, GasNone, GasNone, GasNone, GasNone, GasNone, GasNone,
    GasNone, GasNone, GasNone, GasNone, GasNone, GasNone, GasNone, GasNone,
    GasNone, GasNone, GasNone, GasNone, GasNone, GasNone, GasNone, GasNone,
    GasNone, GasNone, GasNone, GasNone, GasNone, GasNone, GasNone, GasNone,
    // CREATE, CALL, CALLCODE, RETURN, DELEGATECALL, CREATE2
    GasCreate, GasCall, GasCall, GasNone, GasCall, GasCreate2, GasNone, GasNone,
    // STATICCALL, REVERT, SELFDESTRUCT
    GasNone, GasNone, GasCall, GasNone, GasNone, GasNone, GasNone, GasNone,
};

// list of precompiled contracts
enum Precompiled : uint8_t {
    ECRECOVER = 0x01,
    SHA256,
    RIPEMD160,
    DATACOPY,
    BIGMODEXP,
    BN256ADD,
    BN256SCALARMUL,
    BN256PAIRING,
    BLAKE2F,
};

#ifndef NDEBUG
// an associated precompiled contract string table for debbuging
static const char *prenames[BLAKE2F+1] = {
    "?",
    "ECRECOVER",
    "SHA256",
    "RIPEMD160",
    "DATACOPY",
    "BIGMODEXP",
    "BN256ADD",
    "BN256SCALARMUL",
    "BN256PAIRING",
    "BLAKE2F",
};
#endif // NDEBUG

// sets of supported opcodes by release (encoded as 256-bit words)
static const uint256_t _1 = (uint256_t)1;
static const uint256_t is_frontier = 0
    | _1 << STOP | _1 << ADD | _1 << MUL | _1 << SUB | _1 << DIV | _1 << SDIV | _1 << MOD | _1 << SMOD
    | _1 << ADDMOD | _1 << MULMOD | _1 << EXP | _1 << SIGNEXTEND
    | _1 << LT | _1 << GT | _1 << SLT | _1 << SGT | _1 << EQ | _1 << ISZERO | _1 << AND | _1 << OR
    | _1 << XOR | _1 << NOT | _1 << BYTE
    | _1 << SHA3
    | _1 << ADDRESS | _1 << BALANCE | _1 << ORIGIN | _1 << CALLER | _1 << CALLVALUE | _1 << CALLDATALOAD | _1 << CALLDATASIZE | _1 << CALLDATACOPY
    | _1 << CODESIZE | _1 << CODECOPY | _1 << GASPRICE | _1 << EXTCODESIZE | _1 << EXTCODECOPY
    | _1 << BLOCKHASH | _1 << COINBASE | _1 << TIMESTAMP | _1 << NUMBER | _1 << DIFFICULTY | _1 << GASLIMIT
    | _1 << POP | _1 << MLOAD | _1 << MSTORE | _1 << MSTORE8 | _1 << SLOAD | _1 << SSTORE | _1 << JUMP | _1 << JUMPI
    | _1 << PC | _1 << MSIZE | _1 << GAS | _1 << JUMPDEST
    | _1 << PUSH1 | _1 << PUSH2 | _1 << PUSH3 | _1 << PUSH4 | _1 << PUSH5 | _1 << PUSH6 | _1 << PUSH7 | _1 << PUSH8
    | _1 << PUSH9 | _1 << PUSH10 | _1 << PUSH11 | _1 << PUSH12 | _1 << PUSH13 | _1 << PUSH14 | _1 << PUSH15 | _1 << PUSH16
    | _1 << PUSH17 | _1 << PUSH18 | _1 << PUSH19 | _1 << PUSH20 | _1 << PUSH21 | _1 << PUSH22 | _1 << PUSH23 | _1 << PUSH24
    | _1 << PUSH25 | _1 << PUSH26 | _1 << PUSH27 | _1 << PUSH28 | _1 << PUSH29 | _1 << PUSH30 | _1 << PUSH31 | _1 << PUSH32
    | _1 << DUP1 | _1 << DUP2 | _1 << DUP3 | _1 << DUP4 | _1 << DUP5 | _1 << DUP6 | _1 << DUP7 | _1 << DUP8
    | _1 << DUP9 | _1 << DUP10 | _1 << DUP11 | _1 << DUP12 | _1 << DUP13 | _1 << DUP14 | _1 << DUP15 | _1 << DUP16
    | _1 << SWAP1 | _1 << SWAP2 | _1 << SWAP3 | _1 << SWAP4 | _1 << SWAP5 | _1 << SWAP6 | _1 << SWAP7 | _1 << SWAP8
    | _1 << SWAP9 | _1 << SWAP10 | _1 << SWAP11 | _1 << SWAP12 | _1 << SWAP13 | _1 << SWAP14 | _1 << SWAP15 | _1 << SWAP16
    | _1 << LOG0 | _1 << LOG1 | _1 << LOG2 | _1 << LOG3 | _1 << LOG4
    | _1 << CREATE | _1 << CALL | _1 << CALLCODE | _1 << RETURN
    | _1 << SELFDESTRUCT;
static const uint256_t is_homestead = is_frontier
    | _1 << DELEGATECALL;
static const uint256_t is_tangerine_whistle = is_homestead;
static const uint256_t is_spurious_dragon = is_tangerine_whistle;
static const uint256_t is_byzantium = is_spurious_dragon
    | _1 << STATICCALL
    | _1 << RETURNDATASIZE
    | _1 << RETURNDATACOPY
    | _1 << REVERT;
static const uint256_t is_constantinople = is_byzantium
    | _1 << SHL
    | _1 << SHR
    | _1 << SAR
    | _1 << EXTCODEHASH
    | _1 << CREATE2;
static const uint256_t is_petersburg = is_constantinople;
static const uint256_t is_istanbul = is_petersburg
    | _1 << CHAINID
    | _1 << SELFBALANCE;

// this table is used to check if opcode is available for a given release
static const uint256_t is[ISTANBUL+1] = {
    is_frontier,
    is_homestead,
    is_tangerine_whistle,
    is_spurious_dragon,
    is_byzantium,
    is_constantinople,
    is_petersburg,
    is_istanbul,
};

// sets of supported precompiled contracts by release (encoded as 256-bit words)
static uint256_t pre_frontier = 0;
static uint256_t pre_homestead = pre_frontier
    | 1 << ECRECOVER
    | 1 << SHA256
    | 1 << RIPEMD160
    | 1 << DATACOPY;
static uint256_t pre_tangerine_whistle = pre_homestead;
static uint256_t pre_spurious_dragon = pre_tangerine_whistle;
static uint256_t pre_byzantium = pre_spurious_dragon
    | 1 << BIGMODEXP
    | 1 << BN256ADD
    | 1 << BN256SCALARMUL
    | 1 << BN256PAIRING;
static uint256_t pre_constantinople = pre_byzantium;
static uint256_t pre_petersburg = pre_constantinople;
static uint256_t pre_istanbul = pre_petersburg
    | 1 << BLAKE2F;

// this table is used to check if precompiled contract is available for a given release
static const uint256_t pre[ISTANBUL+1] = {
    pre_frontier,
    pre_homestead,
    pre_tangerine_whistle,
    pre_spurious_dragon,
    pre_byzantium,
    pre_constantinople,
    pre_petersburg,
    pre_istanbul,
};

// some useful sets of opcodes checked by the interpreter (encoded as 256-bit words)
static const uint256_t is_halts = 0
    | _1 << STOP
    | _1 << RETURN
    | _1 << SELFDESTRUCT;
static const uint256_t is_jumps = 0
    | _1 << JUMP | _1 << JUMPI;
static const uint256_t is_writes = 0
    | _1 << SSTORE
    | _1 << LOG0 | _1 << LOG1 | _1 << LOG2 | _1 << LOG3 | _1 << LOG4
    | _1 << CREATE | _1 << CREATE2
    | _1 << SELFDESTRUCT;
static const uint256_t is_reverts = 0
    | _1 << REVERT;
static const uint256_t is_returns = 0
    | _1 << CREATE | _1 << CREATE2
    | _1 << CALL | _1 << CALLCODE | _1 << DELEGATECALL | _1 << STATICCALL
    | _1 << REVERT;

// ** gas calcs **

// large table associating the gastype to its gas cost per release
// in order to avoid waste, 4 releases were packed in a single entry
static const uint32_t is_gas_table[5][GasTxDataNonZero+1] = {
    {   // frontier
        _GasNone,
        _GasQuickStep,
        _GasFastestStep,
        _GasFastStep,
        _GasMidStep,
        _GasSlowStep,
        _GasExtStep,
        _GasExp,
        _GasExpByte,
        _GasSha3,
        _GasSha3Word,
        _GasBalance,
        _GasExtcodeSize,
        _GasExtcodeCopy,
        _GasExtcodeHash,
        _GasSload,
        _GasSstoreLegacySet,
        _GasSstoreLegacyClear,
        _GasSstoreLegacyReset,
        _GasSstoreLegacyRefund,
        _GasSstoreSentry,
        _GasSstoreNoop,
        _GasSstoreInit,
        _GasSstoreClean,
        _GasSstoreDirty,
        _GasSstoreInitRefund,
        _GasSstoreCleanRefund,
        _GasSstoreClearRefund,
        _GasJumpdest,
        _GasCreate,
        _GasCreateData,
        _GasCall,
        _GasCallNewAccount,
        _GasCallValueTransfer,
        _GasCallValueTransferStipend,
        _GasCreate2,
        _GasSelfDestruct,
        _GasSelfDestructNewAccount,
        _GasSelfDestructRefund,
        _GasMemory,
        _GasMemoryDiv,
        _GasCopy,
        _GasLog,
        _GasLogTopic,
        _GasLogData,
        _GasEcRecover,
        _GasSha256,
        _GasSha256Word,
        _GasRipemd160,
        _GasRipemd160Word,
        _GasDataCopy,
        _GasDataCopyWord,
        _GasBigModExpDiv,
        _GasBn256Add,
        _GasBn256ScalarMul,
        _GasBn256Pairing,
        _GasBn256PairingPoint,
        _GasBlake2f,
        _GasBlake2fRound,
        _GasTxMessageCall,
        _GasTxContractCreation,
        _GasTxDataZero,
        _GasTxDataNonZero,
    },
    {   // homestead
        _GasNone,
        _GasQuickStep,
        _GasFastestStep,
        _GasFastStep,
        _GasMidStep,
        _GasSlowStep,
        _GasExtStep,
        _GasExp,
        _GasExpByte,
        _GasSha3,
        _GasSha3Word,
        _GasBalance,
        _GasExtcodeSize,
        _GasExtcodeCopy,
        _GasExtcodeHash,
        _GasSload,
        _GasSstoreLegacySet,
        _GasSstoreLegacyClear,
        _GasSstoreLegacyReset,
        _GasSstoreLegacyRefund,
        _GasSstoreSentry,
        _GasSstoreNoop,
        _GasSstoreInit,
        _GasSstoreClean,
        _GasSstoreDirty,
        _GasSstoreInitRefund,
        _GasSstoreCleanRefund,
        _GasSstoreClearRefund,
        _GasJumpdest,
        _GasCreate,
        _GasCreateData,
        _GasCall,
        _GasCallNewAccount,
        _GasCallValueTransfer,
        _GasCallValueTransferStipend,
        _GasCreate2,
        _GasSelfDestruct,
        _GasSelfDestructNewAccount,
        _GasSelfDestructRefund,
        _GasMemory,
        _GasMemoryDiv,
        _GasCopy,
        _GasLog,
        _GasLogTopic,
        _GasLogData,
        _GasEcRecover,
        _GasSha256,
        _GasSha256Word,
        _GasRipemd160,
        _GasRipemd160Word,
        _GasDataCopy,
        _GasDataCopyWord,
        _GasBigModExpDiv,
        _GasBn256Add,
        _GasBn256ScalarMul,
        _GasBn256Pairing,
        _GasBn256PairingPoint,
        _GasBlake2f,
        _GasBlake2fRound,
        _GasTxMessageCall,
        _GasTxContractCreation_Homestead,
        _GasTxDataZero,
        _GasTxDataNonZero,
    },
    {   // tangerine whistle
        _GasNone,
        _GasQuickStep,
        _GasFastestStep,
        _GasFastStep,
        _GasMidStep,
        _GasSlowStep,
        _GasExtStep,
        _GasExp,
        _GasExpByte,
        _GasSha3,
        _GasSha3Word,
        _GasBalance_TangerineWhistle,
        _GasExtcodeSize_TangerineWhistle,
        _GasExtcodeCopy_TangerineWhistle,
        _GasExtcodeHash,
        _GasSload_TangerineWhistle,
        _GasSstoreLegacySet,
        _GasSstoreLegacyClear,
        _GasSstoreLegacyReset,
        _GasSstoreLegacyRefund,
        _GasSstoreSentry,
        _GasSstoreNoop,
        _GasSstoreInit,
        _GasSstoreClean,
        _GasSstoreDirty,
        _GasSstoreInitRefund,
        _GasSstoreCleanRefund,
        _GasSstoreClearRefund,
        _GasJumpdest,
        _GasCreate,
        _GasCreateData,
        _GasCall_TangerineWhistle,
        _GasCallNewAccount,
        _GasCallValueTransfer,
        _GasCallValueTransferStipend,
        _GasCreate2,
        _GasSelfDestruct,
        _GasSelfDestructNewAccount,
        _GasSelfDestructRefund,
        _GasMemory,
        _GasMemoryDiv,
        _GasCopy,
        _GasLog,
        _GasLogTopic,
        _GasLogData,
        _GasEcRecover,
        _GasSha256,
        _GasSha256Word,
        _GasRipemd160,
        _GasRipemd160Word,
        _GasDataCopy,
        _GasDataCopyWord,
        _GasBigModExpDiv,
        _GasBn256Add,
        _GasBn256ScalarMul,
        _GasBn256Pairing,
        _GasBn256PairingPoint,
        _GasBlake2f,
        _GasBlake2fRound,
        _GasTxMessageCall,
        _GasTxContractCreation_Homestead,
        _GasTxDataZero,
        _GasTxDataNonZero,
    },
    {   // spurious dragon, byzantium, constantinople, petersburg
        _GasNone,
        _GasQuickStep,
        _GasFastestStep,
        _GasFastStep,
        _GasMidStep,
        _GasSlowStep,
        _GasExtStep,
        _GasExp,
        _GasExpByte_SpuriousDragon,
        _GasSha3,
        _GasSha3Word,
        _GasBalance_TangerineWhistle,
        _GasExtcodeSize_TangerineWhistle,
        _GasExtcodeCopy_TangerineWhistle,
        _GasExtcodeHash,
        _GasSload_TangerineWhistle,
        _GasSstoreLegacySet,
        _GasSstoreLegacyClear,
        _GasSstoreLegacyReset,
        _GasSstoreLegacyRefund,
        _GasSstoreSentry,
        _GasSstoreNoop,
        _GasSstoreInit,
        _GasSstoreClean,
        _GasSstoreDirty,
        _GasSstoreInitRefund,
        _GasSstoreCleanRefund,
        _GasSstoreClearRefund,
        _GasJumpdest,
        _GasCreate,
        _GasCreateData,
        _GasCall_TangerineWhistle,
        _GasCallNewAccount,
        _GasCallValueTransfer,
        _GasCallValueTransferStipend,
        _GasCreate2,
        _GasSelfDestruct,
        _GasSelfDestructNewAccount,
        _GasSelfDestructRefund,
        _GasMemory,
        _GasMemoryDiv,
        _GasCopy,
        _GasLog,
        _GasLogTopic,
        _GasLogData,
        _GasEcRecover,
        _GasSha256,
        _GasSha256Word,
        _GasRipemd160,
        _GasRipemd160Word,
        _GasDataCopy,
        _GasDataCopyWord,
        _GasBigModExpDiv,
        _GasBn256Add,
        _GasBn256ScalarMul,
        _GasBn256Pairing,
        _GasBn256PairingPoint,
        _GasBlake2f,
        _GasBlake2fRound,
        _GasTxMessageCall,
        _GasTxContractCreation_Homestead,
        _GasTxDataZero,
        _GasTxDataNonZero,
    },
    {   // istanbul
        _GasNone,
        _GasQuickStep,
        _GasFastestStep,
        _GasFastStep,
        _GasMidStep,
        _GasSlowStep,
        _GasExtStep,
        _GasExp,
        _GasExpByte_SpuriousDragon,
        _GasSha3,
        _GasSha3Word,
        _GasBalance_Istanbul,
        _GasExtcodeSize_TangerineWhistle,
        _GasExtcodeCopy_TangerineWhistle,
        _GasExtcodeHash_Istanbul,
        _GasSload_Istanbul,
        _GasSstoreLegacySet,
        _GasSstoreLegacyClear,
        _GasSstoreLegacyReset,
        _GasSstoreLegacyRefund,
        _GasSstoreSentry_Istanbul,
        _GasSstoreNoop_Istanbul,
        _GasSstoreInit_Istanbul,
        _GasSstoreClean_Istanbul,
        _GasSstoreDirty_Istanbul,
        _GasSstoreInitRefund_Istanbul,
        _GasSstoreCleanRefund_Istanbul,
        _GasSstoreClearRefund_Istanbul,
        _GasJumpdest,
        _GasCreate,
        _GasCreateData,
        _GasCall_TangerineWhistle,
        _GasCallNewAccount,
        _GasCallValueTransfer,
        _GasCallValueTransferStipend,
        _GasCreate2,
        _GasSelfDestruct,
        _GasSelfDestructNewAccount,
        _GasSelfDestructRefund,
        _GasMemory,
        _GasMemoryDiv,
        _GasCopy,
        _GasLog,
        _GasLogTopic,
        _GasLogData,
        _GasEcRecover,
        _GasSha256,
        _GasSha256Word,
        _GasRipemd160,
        _GasRipemd160Word,
        _GasDataCopy,
        _GasDataCopyWord,
        _GasBigModExpDiv,
        _GasBn256Add_Istanbul,
        _GasBn256ScalarMul_Istanbul,
        _GasBn256Pairing_Istanbul,
        _GasBn256PairingPoint_Istanbul,
        _GasBlake2f,
        _GasBlake2fRound,
        _GasTxMessageCall,
        _GasTxContractCreation_Homestead,
        _GasTxDataZero,
        _GasTxDataNonZero_Istanbul,
    },
};
static uint8_t is_gas_index[ISTANBUL+1] = { 0, 1, 2, 3, 3, 3, 3, 4 };

// randy function to retrieve gas cost given release and gas type
static inline uint64_t _gas(Release release, GasType type)
{
    return is_gas_table[is_gas_index[release]][type];
}

// handy function to retrieve the constant part of the gas consumption cost for opcodes
static inline uint64_t gas_opcode(Release release, uint8_t opc)
{
    return _gas(release, constgas[opc]);
}

// calculation of transaction intrinsic gas
static uint64_t gas_intrinsic(Release release, bool is_message_call, const uint8_t *data, uint64_t data_size)
{
    // check for overflow
    uint64_t gas = _gas(release, is_message_call ? GasTxMessageCall : GasTxContractCreation);
    uint64_t zero_count = 0;
    for (uint64_t i = 0; i < data_size; i++) if (data[i] == 0) zero_count++;
    gas += zero_count * _gas(release, GasTxDataZero);
    gas += (data_size - zero_count) * _gas(release, GasTxDataNonZero);
    return gas;
}

// calculation of gas consumption for memory related operations
static inline uint64_t gas_memory(Release release, uint64_t _size1, uint64_t _size2)
{
    uint256_t size1 = _size1;
    uint256_t size2 = _size2;
    uint256_t words1 = (size1 + 31) / 32;
    uint256_t words2 = (size2 + 31) / 32;
    if (words2 <= words1) return 0;
    uint256_t used_gas = (words2 - words1) * _gas(release, GasMemory)
        + (words2 * words2) / _gas(release, GasMemoryDiv) - (words1 * words1) / _gas(release, GasMemoryDiv);
    if ((used_gas >> 64) > 0) return ~(uint64_t)0;
    return used_gas.cast64();
}

// calculation of gas consumption for data copying operations
static inline uint64_t gas_copy(Release release, uint64_t size)
{
    uint64_t words = (size + 31) / 32;
    return words * _gas(release, GasCopy);
}

// calculation of gas consumption for logging operations
static inline uint64_t gas_log(Release release, uint64_t n, uint64_t size)
{
    return _gas(release, GasLog) + n * _gas(release, GasLogTopic) + size * _gas(release, GasLogData);
}

// calculation of gas consumption for SHA3
static inline uint64_t gas_sha3(Release release, uint64_t size)
{
    uint64_t words = (size + 31) / 32;
    return words * _gas(release, GasSha3Word);
}

// calculation of gas consumption for EXP
static inline uint64_t gas_exp(Release release, uint64_t size)
{
    return size * _gas(release, GasExpByte);
}

// calculation of gas consumption for call operations
static uint64_t gas_call(Release release, bool funds, bool empty, bool exists)
{
    uint32_t used_gas = 0;
    bool is_legacy = release < SPURIOUS_DRAGON;
    bool is_new = (is_legacy && !exists) || (!is_legacy && empty && funds);
    if (is_new) used_gas += _gas(release, GasCallNewAccount);
    if (funds) used_gas += _gas(release, GasCallValueTransfer);
    return used_gas;
}

// calculation of gas stipend for calls that transfer funds
static uint64_t gas_stipend_call(Release release, bool funds)
{
    uint32_t stipend_gas = 0;
    if (funds) stipend_gas += _gas(release, GasCallValueTransferStipend);
    return stipend_gas;
}

// caps the call/create gas regarding to call gas limit parameter according to release
static uint64_t gas_cap(Release release, uint64_t gas, uint64_t reserved_gas)
{
    if (release >= TANGERINE_WHISTLE) {
        uint64_t capped_gas = gas - (gas / 64);
        if (capped_gas < reserved_gas) return capped_gas;
    }
    return reserved_gas;
}

// calculation of gas consumption for create operations
static uint64_t gas_create(Release release, uint64_t size)
{
    return size * _gas(release, GasCreateData);
}

// calculation of gas consumption for selfdestruct operation
static uint64_t gas_selfdestruct(Release release, bool funds, bool empty, bool exists)
{
    if (release >= TANGERINE_WHISTLE) {
        uint64_t used_gas = _gas(release, GasSelfDestruct);
        bool is_legacy = release < SPURIOUS_DRAGON;
        bool is_new = (is_legacy && !exists) || (!is_legacy && empty && funds);
        if (is_new) used_gas += _gas(release, GasSelfDestructNewAccount);
        return used_gas;
    }
    return 0;
}

// calculates refund for selfdestruct operation
static uint64_t gas_refund_selfdestruct(Release release)
{
    return _gas(release, GasSelfDestructRefund);
}

// calculation of gas consumption for sstore operation
static inline uint64_t gas_sstore(Release release, uint64_t gas, bool init, bool dirty, bool noop, bool sets, bool clears, bool cleans)
{
    if (gas <= _gas(release, GasSstoreSentry)) return gas + 1; // forces the consumption of all gas
    if (release < CONSTANTINOPLE || (PETERSBURG <= release && release < ISTANBUL)) {
        if (sets) return _gas(release, GasSstoreLegacySet);
        if (clears) return _gas(release, GasSstoreLegacyClear);
        return _gas(release, GasSstoreLegacyReset);
    }
    if (noop) return _gas(release, GasSstoreNoop);
    if (dirty)  return _gas(release, GasSstoreDirty);
    if (init) return _gas(release, GasSstoreInit);
    return _gas(release, GasSstoreClean);
}

// calculates refund for sstore operation
static inline uint64_t gas_refund_sstore(Release release, bool init, bool dirty, bool noop, bool sets, bool clears, bool cleans)
{
    if (release < CONSTANTINOPLE || (PETERSBURG <= release && release < ISTANBUL)) {
        if (clears) return _gas(release, GasSstoreLegacyRefund);
        return 0;
    }
	if (!init && clears) return _gas(release, GasSstoreClearRefund);
    if (dirty && cleans) return _gas(release, init ? GasSstoreInitRefund : GasSstoreCleanRefund);
    return 0;
}

// calculates refund for sstore operation
static inline uint64_t gas_unrefund_sstore(Release release, bool init, bool dirty, bool noop, bool sets, bool clears, bool cleans)
{
    if (release < CONSTANTINOPLE || (PETERSBURG <= release && release < ISTANBUL)) return 0;
	if (!init && sets) return _gas(release, GasSstoreClearRefund);
    return 0;
}

// calculation of gas consumption for ecrecover precompiled contract
static uint64_t gas_ecrecover(Release release)
{
    return _gas(release, GasEcRecover);
}

// calculation of gas consumption for sha256 precompiled contract
static uint64_t gas_sha256(Release release, uint64_t size)
{
    uint64_t words = (size + 31) / 32;
    return _gas(release, GasSha256) + words * _gas(release, GasSha256Word);
}

// calculation of gas consumption for ripemd160 precompiled contract
static uint64_t gas_ripemd160(Release release, uint64_t size)
{
    uint64_t words = (size + 31) / 32;
    return _gas(release, GasRipemd160) + words * _gas(release, GasRipemd160Word);
}

// calculation of gas consumption for datacopy precompiled contract
static uint64_t gas_datacopy(Release release, uint64_t size)
{
    uint64_t words = (size + 31) / 32;
    return _gas(release, GasDataCopy) + words * _gas(release, GasDataCopyWord);
}

// calculation of gas consumption for bigmodexp precompiled contract
static uint64_t gas_bigmodexp(Release release, const bigint& base_len, const bigint& exp_len, const bigint& mod_len, const bigint& log2_exp)
{
    bigint max_len = base_len > mod_len ? base_len : mod_len;
    bigint base_gas;
    if (max_len <= 64) base_gas = max_len * max_len;
    else if (max_len <= 1024) base_gas = (max_len * max_len) / 4 + (96 * max_len - 3072);
    else base_gas = (max_len * max_len) / 16 + (480 * max_len - 199680);
    bigint exp_gas;
    if (exp_len <= 32) exp_gas = log2_exp;
    else exp_gas = 8 * (exp_len - 32) + log2_exp;
    bigint used_gas = (base_gas * (exp_gas > 1 ? exp_gas : 1)) / _gas(release, GasBigModExpDiv);
    if ((used_gas >> 64) > 0) return ~(uint64_t)0;
    return used_gas.cast64();
}

// calculation of gas consumption for bn256add precompiled contract
static uint64_t gas_bn256add(Release release)
{
    return _gas(release, GasBn256Add);
}

// calculation of gas consumption for bn256scalarmul precompiled contract
static uint64_t gas_bn256scalarmul(Release release)
{
    return _gas(release, GasBn256ScalarMul);
}

// calculation of gas consumption for bn256pairing precompiled contract
static uint64_t gas_bn256pairing(Release release, uint64_t points)
{
    return _gas(release, GasBn256Pairing) + points * _gas(release, GasBn256PairingPoint);
}

// calculation of gas consumption for blake2f precompiled contract
static uint64_t gas_blake2f(Release release, uint64_t rounds)
{
    return _gas(release, GasBlake2f) + rounds * _gas(release, GasBlake2fRound);
}

// handy routine to consume gas, checks for gas exaustion
static inline void _throws(consume_gas)(uint64_t &gas, uint64_t cost)
{
    if (cost > gas) _throw(GAS_EXAUSTED);
    gas -= cost;
}

// handy routine to credit back gas
static inline void credit_gas(uint64_t &gas, uint64_t stipend)
{
    assert(gas + stipend >= gas);
    gas += stipend;
}

// ** execution components **

// simple frame stack implementation
// limited to 1024 words, could be made to grow dynamically
class Stack {
private:
    static constexpr int L = STACK_SIZE;
    uint16_t _top = 0; // current size
    uint256_t *data = nullptr; // stack contents
public:
    Stack() { data = _new<uint256_t>(L); }
    ~Stack() { _delete(data); }
    inline uint64_t top() const { return _top; }
    inline const uint256_t pop() { assert(_top > 0); return data[--_top]; }
    inline void push(const uint256_t& v) {  assert(_top < L); data[_top++] = v; }
    inline uint256_t& operator[](uint64_t i) { assert(i <= _top); return data[_top - i]; }
};

// simple frame memory implementation
// since memory can grow arbitrarily with gaps, the implementation uses
// a two level sparce matrix to avoid waste
class Memory {
private:
    static constexpr int P = 16 * 1024; // page size in bytes
    static constexpr int S = P / sizeof(uint8_t*); // index vector increment
    uint64_t limit = 0; // 256 bit aligned, except for the very last one
    uint64_t page_count = 0;
    uint8_t **pages = nullptr;
    // makes sure a page is allocated prior to access
    void ensure_page(uint64_t page_index) {
        assert(page_index < page_count);
        if (pages[page_index] == nullptr) {
            pages[page_index] = _new<uint8_t>(P);
            for (uint64_t i = 0; i < P; i++) pages[page_index][i] = 0;
        }
    }
    // expands the page table to create room
    void expand(uint64_t end) {
        if (end == 0) return;
        uint64_t i = end - 1;
        uint64_t page_index = i / P;
        if (page_index >= page_count) {
            uint64_t new_page_count = ((page_index / S) + 1) * S;
            uint8_t **new_pages = _new<uint8_t*>(new_page_count);
            for (uint64_t i = 0; i < page_count; i++) new_pages[i] = pages[i];
            for (uint64_t i = page_count; i < new_page_count; i++) new_pages[i] = nullptr;
            _delete(pages);
            pages = new_pages;
            page_count = new_page_count;
        }
        mark(end);
    }
    // reads a byte
    uint8_t get(uint64_t i) const {
        uint64_t page_index = i / P;
        uint64_t byte_index = i % P;
        if (page_index >= page_count) return 0;
        if (pages[page_index] == nullptr) return 0;
        return pages[page_index][byte_index];
    }
    // writes a byte
    void set(uint64_t i, uint8_t v) {
        uint64_t page_index = i / P;
        uint64_t byte_index = i % P;
        ensure_page(page_index);
        assert(pages[page_index] != nullptr);
        pages[page_index][byte_index] = v;
    }
public:
    ~Memory() {
        for (uint64_t i = 0; i < page_count; i++) _delete(pages[i]);
        _delete(pages);
    }
    // current memory limit
    inline uint64_t size() const { return limit; }
    // marks the memory limit, if exceeded
    void mark(uint64_t end) {
        if (end > limit) {
            limit = ((end + 31) / 32) * 32;
            if (limit == 0) limit--; // special case, overflow
        }
    }
    // loads a 256-bit word in memory
    uint256_t load(uint64_t offset) {
        uint8_t buffer[32];
        dump(offset, 32, buffer);
        return uint256_t::from(buffer);
    }
    // stores a 256-bit word in memory
    void store(uint64_t offset, const uint256_t& v) {
        uint8_t buffer[32];
        uint256_t::to(v, buffer);
        burn(offset, 32, buffer, 32);
    }
    // dumps memory to a buffer
    void dump(uint64_t offset, uint64_t size, uint8_t *buffer) {
        assert(offset + size >= offset);
        if (size > 0) mark(offset + size);
        for (uint64_t i = 0; i < size; i++) buffer[i] = get(offset+i);
    }
    // burns memory from a buffer
    void burn(uint64_t offset, const uint8_t *buffer, uint64_t size) {
        burn(offset, size, buffer, size);
    }
    // burns memory from a buffer, padding right with zeros
    void burn(uint64_t offset, uint64_t size, const uint8_t *buffer, uint64_t burnsize) {
        assert(offset + size >= offset);
        if (size > 0) expand(offset + size);
        if (burnsize > size) burnsize = size;
        for (uint64_t i = 0; i < burnsize; i++) set(offset+i, buffer[i]);
        for (uint64_t i = burnsize; i < size; i++) set(offset+i, 0);
    }
};

// state abstraction, gateway for the information that is stored permanently in the blockchain
// this is read at any time, but modified only in the very end of the transaction execution
// intermediate storage changes are cached by the interpreter as there is need to rollback
// in case of an exceptional condition occurs
class State {
public:
    virtual uint64_t get_nonce(const uint160_t &address) const = 0;
    virtual void set_nonce(const uint160_t &address, const uint64_t &nonce) = 0;
    virtual uint256_t get_balance(const uint160_t &address) const = 0;
    virtual void set_balance(const uint160_t &address, const uint256_t &balance) = 0;
    virtual uint256_t get_codehash(const uint160_t &address) const = 0;
    virtual void set_codehash(const uint160_t &address, const uint256_t &codehash) = 0;
    virtual uint8_t *load_code(const uint256_t &codehash, uint64_t &code_size) const = 0;
    virtual void store_code(const uint256_t &codehash, const uint8_t *code, uint64_t code_size) = 0;
    virtual uint256_t load(const uint160_t &address, const uint256_t &key) const = 0;
    virtual void store(const uint160_t &address, const uint256_t &key, const uint256_t& value) = 0;
    virtual void log0(const uint160_t &address, const uint8_t *data, uint64_t data_size) = 0;
    virtual void log1(const uint160_t &address, const uint256_t &v1, const uint8_t *data, uint64_t data_size) = 0;
    virtual void log2(const uint160_t &address, const uint256_t &v1, const uint256_t &v2, const uint8_t *data, uint64_t data_size) = 0;
    virtual void log3(const uint160_t &address, const uint256_t &v1, const uint256_t &v2, const uint256_t &v3, const uint8_t *data, uint64_t data_size) = 0;
    virtual void log4(const uint160_t &address, const uint256_t &v1, const uint256_t &v2, const uint256_t &v3, const uint256_t &v4, const uint8_t *data, uint64_t data_size) = 0;
    virtual void clear(const uint160_t &address) = 0;
    virtual void remove(const uint160_t &address) = 0;
};

// simple cache implementation, maps keys into values
template<class K, class V>
class Cache {
private:
    friend class CachedState;
    static constexpr int minfreeslots = 8; // free entries before rehashing 1/8 (12.5% should be free)
    static constexpr int minsize = 32; // min number of slots
    static constexpr int growthdiv = 4; // growth factor 4 means 1/4 (25% per rehashing)
    struct cache_entry {
        K key;
        V value;
    };
    uint64_t size = 0; // hash table size
    struct cache_entry **table = nullptr; // hash table
    uint64_t key_count = 0; // number os keys in the hash table
    uint64_t find_index(const K &key) const { return key.murmur3(0) % size; }
    void grow(uint64_t increment) {
        uint64_t new_size = size + increment;
        struct cache_entry **new_table = _new<struct cache_entry*>(new_size);
        for (uint64_t i = 0; i < new_size; i++) new_table[i] = nullptr;
        struct cache_entry **old_table = table;
        uint64_t old_size = size;
        table = new_table;
        size = new_size;
        // rehashing
        for (uint64_t i = 0; i < old_size; i++) {
            struct cache_entry *entry = old_table[i];
            if (entry != nullptr) {
                uint64_t j = find_index(entry->key);
                if (table[j] != nullptr) {
                    _delete(table[j]); key_count--;
                }
                table[j] = entry;
            }
        }
        _delete(old_table);
    }
public:
    ~Cache() { clear(); _delete(table); }
    const V *get(const K &key) const {
        if (size == 0) return nullptr;
        uint64_t i = find_index(key);
        struct cache_entry *entry = table[i];
        if (entry != nullptr) {
            if (entry->key == key) return &entry->value;
        }
        return nullptr;
    }
    void set(const K &key, const V &value) {
        if (key_count + (size / minfreeslots) >= size) grow(_max(minsize, size / growthdiv));
        uint64_t i = find_index(key);
        struct cache_entry *entry = table[i];
        if (entry == nullptr) {
            entry = _new<struct cache_entry>(1); key_count++;
            table[i] = entry;
        }
        entry->key = key;
        entry->value = value;
    }
    void del(const K &key) {
        if (size == 0) return;
        uint64_t i = find_index(key);
        struct cache_entry *entry = table[i];
        if (entry != nullptr) {
            if (entry->key == key) {
                _delete(table[i]); key_count--;
                table[i] = nullptr;
            }
        }
    }
    void clear() {
        for (uint64_t i = 0; i < size; i++) {
            if (table[i] != nullptr) {
                _delete(table[i]); key_count--;
            }
            table[i] = nullptr;
        }
        assert(key_count == 0);
    }
};

// provides a read cache view of the state
class CachedState : public State {
private:
    State *underlying; // the abstracted state that implements the actual blockchain storage
    mutable Cache<uint160_t, uint64_t> nonce_cache; // caches state nonce for faster access
    mutable Cache<uint160_t, uint256_t> balance_cache; // caches state balance for faster access
    mutable Cache<uint160_t, uint256_t> codehash_cache; // caches state codehash for faster access
    mutable Cache<uint416_t, uint256_t> data_cache; // caches state data for faster access
public:
    CachedState(State *_underlying) : underlying(_underlying) {}
    uint64_t get_nonce(const uint160_t &address) const {
        const uint64_t *p_nonce = nonce_cache.get(address);
        if (p_nonce != nullptr) return *p_nonce;
        uint64_t nonce = underlying->get_nonce(address);
        nonce_cache.set(address, nonce);
        return nonce;
    }
    void set_nonce(const uint160_t &address, const uint64_t &nonce) {
        nonce_cache.set(address, nonce);
        underlying->set_nonce(address, nonce);
    }
    uint256_t get_balance(const uint160_t &address) const {
        const uint256_t *p_balance = balance_cache.get(address);
        if (p_balance != nullptr) return *p_balance;
        uint256_t balance = underlying->get_balance(address);
        balance_cache.set(address, balance);
        return balance;
    }
    void set_balance(const uint160_t &address, const uint256_t &balance) {
        balance_cache.set(address, balance);
        underlying->set_balance(address, balance);
    }
    uint256_t get_codehash(const uint160_t &address) const {
        const uint256_t *p_codehash = codehash_cache.get(address);
        if (p_codehash != nullptr) return *p_codehash;
        uint256_t codehash = underlying->get_codehash(address);
        codehash_cache.set(address, codehash);
        return codehash;
    }
    void set_codehash(const uint160_t &address, const uint256_t &codehash) {
        codehash_cache.set(address, codehash);
        underlying->set_codehash(address, codehash);
    }
    uint8_t *load_code(const uint256_t &codehash, uint64_t &code_size) const {
        return underlying->load_code(codehash, code_size);
    }
    void store_code(const uint256_t &codehash, const uint8_t *code, uint64_t code_size) {
        underlying->store_code(codehash, code, code_size);
    }
    uint256_t load(const uint160_t &address, const uint256_t &key) const {
        uint416_t extkey = ((uint416_t)address << 256) | (uint416_t)key;
        const uint256_t *p_value = data_cache.get(extkey);
        if (p_value != nullptr) return *p_value;
        uint256_t value = underlying->load(address, key);
        data_cache.set(extkey, value);
        return value;
    }
    void store(const uint160_t &address, const uint256_t &key, const uint256_t& value) {
        uint416_t extkey = ((uint416_t)address << 256) | (uint416_t)key;
        data_cache.set(extkey, value);
        underlying->store(address, key, value);
    }
    void log0(const uint160_t &address, const uint8_t *data, uint64_t data_size) {
        underlying->log0(address, data, data_size);
    }
    void log1(const uint160_t &address, const uint256_t &v1, const uint8_t *data, uint64_t data_size) {
        underlying->log1(address, v1, data, data_size);
    }
    void log2(const uint160_t &address, const uint256_t &v1, const uint256_t &v2, const uint8_t *data, uint64_t data_size) {
        underlying->log2(address, v1, v2, data, data_size);
    }
    void log3(const uint160_t &address, const uint256_t &v1, const uint256_t &v2, const uint256_t &v3, const uint8_t *data, uint64_t data_size) {
        underlying->log3(address, v1, v2, v3, data, data_size);
    }
    void log4(const uint160_t &address, const uint256_t &v1, const uint256_t &v2, const uint256_t &v3, const uint256_t &v4, const uint8_t *data, uint64_t data_size) {
        underlying->log4(address, v1, v2, v3, v4, data, data_size);
    }
    void clear(const uint160_t &address) {
        underlying->clear(address);
        for (uint64_t i = 0; i < data_cache.size; i++) {
            auto entry = data_cache.table[i];
            if (entry != nullptr) {
                uint160_t _address = (uint160_t)(entry->key >> 256);
                if (_address == address) {
                    _delete(data_cache.table[i]); data_cache.key_count--;
                    data_cache.table[i] = nullptr;
                }
            }
        }
    }
    void remove(const uint160_t &address) {
        underlying->remove(address);
        nonce_cache.del(address);
        balance_cache.del(address);
        codehash_cache.del(address);
    }
};

// simple interface that defines the three operations associated with
// transactional state
class Transactional {
public:
    virtual uint64_t snapshot() = 0;
    virtual void commit(uint64_t snapshot) = 0;
    virtual void rollback(uint64_t snapshot) = 0;
};

// simple hash map implementation, maps keys into values
// used to hold temporary nonces, balances, and storage values
// supports nested commits and rollbacks
template<class K, class V>
class Store : public Transactional {
private:
    friend class Storage;
    static constexpr int avgmaxperslot = 3; // approximate max entries per slot before rehashing
    static constexpr int minsize = 32; // min number of slots
    static constexpr int growthdiv = 4; // growth factor 4 means 1/4 (25% per rehashing)
    // list of values, stored according to snapshot order (lifo, newest first)
    struct value_stack {
        uint32_t serial;
        V value;
        struct value_stack *next;
    };
    // list of keys in no particular order
    struct key_list {
        K key;
        struct value_stack *values;
        struct key_list *next;
    };
    uint64_t size = 0; // hash table size
    struct key_list **table = nullptr; // hash table, each entry is a list of keys each pointing to a list of values
    uint64_t key_count = 0; // number os keys in the hash table
    uint64_t serial = 1; // serial number used to mark snapshots
    uint64_t find_index(const K &key) const { return key.murmur3(0) % size; }
    void grow(uint64_t increment) {
        uint64_t new_size = size + increment;
        struct key_list **new_table = _new<struct key_list*>(new_size);
        for (uint64_t i = 0; i < new_size; i++) new_table[i] = nullptr;
        struct key_list **old_table = table;
        uint64_t old_size = size;
        table = new_table;
        size = new_size;
        // rehashing
        for (uint64_t i = 0; i < old_size; i++) {
            struct key_list *keys = old_table[i];
            while (keys != nullptr) {
                uint64_t j = find_index(keys->key);
                struct key_list *next = keys->next;
                keys->next = table[j];
                table[j] = keys;
                keys = next;
            }
        }
        _delete(old_table);
    }
public:
    ~Store() { rollback(0); _delete(table); }
    const V &get(const K &key, const V &default_value) const {
        if (size == 0) return default_value;
        uint64_t i = find_index(key);
        for (struct key_list *keys = table[i]; keys != nullptr; keys = keys->next) {
            if (keys->key == key) {
                if (keys->values != nullptr) return keys->values->value;
                return default_value;
            }
        }
        return default_value;
    }
    void set(const K &key, const V &value, const V &default_value) {
        if (key_count / avgmaxperslot >= size) grow(_max(minsize, size / growthdiv));
        uint64_t i = find_index(key);
        struct key_list *prev = nullptr;
        struct key_list *keys = table[i];
        while (keys != nullptr) {
            if (keys->key == key) {
                if (prev == nullptr) table[i] = keys->next; else prev->next = keys->next;
                keys->next = table[i];
                table[i] = keys;
                break;
            }
            prev = keys;
            keys = keys->next;
        }
        if (keys == nullptr) {
            if (value == default_value) return;
            keys = _new<struct key_list>(1); key_count++;
            keys->key = key;
            keys->values = nullptr;
            keys->next = table[i];
            table[i] = keys;
        }
        assert(keys->values == nullptr || keys->values->serial <= serial);
        if (keys->values == nullptr || (keys->values->serial < serial && keys->values->value != value)) {
            struct value_stack *values = _new<struct value_stack>(1);
            values->serial = serial;
            values->next = keys->values;
            keys->values = values;
        }
        keys->values->value = value;
        assert(keys->values->next == nullptr || keys->values->next->serial < serial);
    }
    inline uint64_t snapshot() { return serial++; }
    // flattens all entry values with serial greater than snapshot
    void commit(uint64_t snapshot) {
        assert(snapshot < serial);
        for (uint64_t i = 0; i < size; i++) {
            struct key_list *prev = nullptr;
            struct key_list *keys = table[i];
            while (keys != nullptr) {
                if (keys->values == nullptr) {
                    struct key_list *next = keys->next;
                    _delete(keys); key_count--;
                    keys = next;
                    if (prev == nullptr) table[i] = keys; else prev->next = keys;
                    continue;
                }
                if (keys->values->serial > snapshot) {
                    while (keys->values->next != nullptr && keys->values->next->serial >= snapshot) {
                        assert(keys->values->next->serial == snapshot);
                        struct value_stack *next = keys->values->next->next;
                        _delete(keys->values->next);
                        keys->values->next = next;
                    }
                    keys->values->serial = snapshot;
                }
                prev = keys;
                keys = keys->next;
            }
        }
        serial = snapshot;
    }
    // removes all entry values with serial greater than snapshot
    void rollback(uint64_t snapshot) {
        assert(snapshot < serial);
        for (uint64_t i = 0; i < size; i++) {
            struct key_list *prev = nullptr;
            struct key_list *keys = table[i];
            while (keys != nullptr) {
                while (keys->values != nullptr && keys->values->serial > snapshot) {
                    struct value_stack *next = keys->values->next;
                    _delete(keys->values);
                    keys->values = next;
                }
                if (keys->values == nullptr) {
                    struct key_list *next = keys->next;
                    _delete(keys); key_count--;
                    keys = next;
                    if (prev == nullptr) table[i] = keys; else prev->next = keys;
                    continue;
                }
                prev = keys;
                keys = keys->next;
            }
        }
        serial = snapshot;
    }
};

// a simple class that stores log data
// supports nested commits and rollbacks
class Log : public Transactional {
protected:
    friend class Storage;
    // entry structure in the log
    struct log {
        uint160_t address;
        uint256_t *topics;
        uint8_t topic_count;
        uint8_t *data;
        uint64_t data_size;
    };
    static constexpr int capacity_increment = 32; // growth chunk
    uint64_t capacity = 0; // allocated size
    uint64_t count = 0; // actual size
    struct log *entries = nullptr;
    // makes room for a new log entry
    log &new_entry(int topic_count, uint64_t data_size) {
        assert(topic_count >= 0);
        if (count == capacity) {
            uint64_t new_capacity = capacity + capacity_increment;
            struct log *new_entries = _new<struct log>(new_capacity);
            for (uint64_t i = 0; i < capacity; i++) new_entries[i] = entries[i];
            for (uint64_t i = capacity; i < new_capacity; i++) {
                new_entries[i].topics = nullptr;
                new_entries[i].data = nullptr;
            }
            _delete(entries);
            entries = new_entries;
            capacity = new_capacity;
        }
        uint64_t index = count++;
        entries[index].topics = _new<uint256_t>(topic_count);
        entries[index].data = _new<uint8_t>(data_size);
        return entries[index];
    }
public:
    ~Log() {
        for (uint64_t i = 0; i < count; i++) {
            _delete(entries[i].topics);
            _delete(entries[i].data);
        }
        _delete(entries);
    }
    inline uint64_t size() { return count; }
    void log0(const uint160_t &address, const uint8_t *data, uint64_t data_size) {
        struct log &log = new_entry(0, data_size);
        log.address = address;
        log.topic_count = 0;
        for (uint64_t i = 0; i < data_size; i++) log.data[i] = data[i];
        log.data_size = data_size;
    }
    void log1(const uint160_t &address, const uint256_t &v1, const uint8_t *data, uint64_t data_size) {
        struct log &log = new_entry(1, data_size);
        log.address = address;
        log.topic_count = 1;
        log.topics[0] = v1;
        for (uint64_t i = 0; i < data_size; i++) log.data[i] = data[i];
        log.data_size = data_size;
    }
    void log2(const uint160_t &address, const uint256_t &v1, const uint256_t &v2, const uint8_t *data, uint64_t data_size) {
        struct log &log = new_entry(2, data_size);
        log.address = address;
        log.topic_count = 2;
        log.topics[0] = v1;
        log.topics[1] = v2;
        for (uint64_t i = 0; i < data_size; i++) log.data[i] = data[i];
        log.data_size = data_size;
    }
    void log3(const uint160_t &address, const uint256_t &v1, const uint256_t &v2, const uint256_t &v3, const uint8_t *data, uint64_t data_size) {
        struct log &log = new_entry(3, data_size);
        log.address = address;
        log.topic_count = 3;
        log.topics[0] = v1;
        log.topics[1] = v2;
        log.topics[2] = v3;
        for (uint64_t i = 0; i < data_size; i++) log.data[i] = data[i];
        log.data_size = data_size;
    }
    void log4(const uint160_t &address, const uint256_t &v1, const uint256_t &v2, const uint256_t &v3, const uint256_t &v4, const uint8_t *data, uint64_t data_size) {
        struct log &log = new_entry(4, data_size);
        log.address = address;
        log.topic_count = 4;
        log.topics[0] = v1;
        log.topics[1] = v2;
        log.topics[2] = v3;
        log.topics[3] = v4;
        for (uint64_t i = 0; i < data_size; i++) log.data[i] = data[i];
        log.data_size = data_size;
    }
    inline uint64_t snapshot() { return count; }
    inline void commit(uint64_t snapshot) {
        assert(snapshot <= count);
    }
    void rollback(uint64_t snapshot) {
        assert(snapshot <= count);
        for (uint64_t i = snapshot; i < count; i++) {
            _delete(entries[i].topics);
            _delete(entries[i].data);
        }
        count = snapshot;
    }
};

// simple storage implementation, it carries temporary state changes during execution
// supports nested commits and rollbacks
// storage is written to the blockchain state at the end of a successful transaction 
class Storage : public State, public Transactional {
protected:
    CachedState state; // the cached state that implements the actual blockchain storage
    Store<uint160_t, uint64_t> nonces; // storage area for nonces
    Store<uint160_t, uint256_t> balances; // storage area for balances
    Store<uint160_t, uint256_t> codehashes; // storage area for code
    Store<uint416_t, uint256_t> data; // storage area for data
    Store<uint160_t, bool> created; // creation flag
    Store<uint160_t, bool> destructed; // destruction flag
    Log logs; // storage for logs
    uint64_t refund_gas = 0; // gas refund accumulator, refund is performed at the very end
    uint64_t *refund_gas_snapshot = nullptr; // refund gas snapshot stack
public:
    Storage(State *_underlying) : state(_underlying) {
        refund_gas_snapshot = _new<uint64_t>(CALL_DEPTH+1);
    }
    ~Storage() { _delete(refund_gas_snapshot); }
    // nonce access methods
    uint64_t get_nonce(const uint160_t &address) const {
        return nonces.get(address, state.get_nonce(address));
    }
    void set_nonce(const uint160_t &address, const uint64_t &nonce) {
        nonces.set(address, nonce, state.get_nonce(address));
    }
    void increment_nonce(const uint160_t &address) {
        set_nonce(address, get_nonce(address) + 1);
    }
    // balance access methods
    uint256_t get_balance(const uint160_t &address) const {
        return balances.get(address, state.get_balance(address));
    }
    void set_balance(const uint160_t &address, const uint256_t &balance) {
        balances.set(address, balance, state.get_balance(address));
    }
    void add_balance(const uint160_t &address, uint256_t amount) {
        set_balance(address, get_balance(address) + amount);
    }
    void sub_balance(const uint160_t &address, uint256_t amount) {
        set_balance(address, get_balance(address) - amount);
    }
    // code access methods
    uint256_t get_codehash(const uint160_t &address) const {
        return codehashes.get(address, state.get_codehash(address));
    }
    void set_codehash(const uint160_t &address, const uint256_t &codehash) {
        codehashes.set(address, codehash, state.get_codehash(address));
    }
    uint8_t *load_code(const uint256_t &codehash, uint64_t &code_size) const {
        return state.load_code(codehash, code_size);
    }
    void store_code(const uint256_t &codehash, const uint8_t *code, uint64_t code_size) {
        state.store_code(codehash, code, code_size);
    }
    uint8_t *get_code(const uint160_t &address, uint64_t &code_size) const {
        return load_code(get_codehash(address), code_size);
    }
    uint8_t *get_call_code(const uint160_t &address, uint64_t &code_size) const {
        if (is_precompiled(address)) { code_size = 0; return (uint8_t*)(intptr_t)address.cast64(); }
        return load_code(get_codehash(address), code_size);
    }
    void release_code(uint8_t *code) const {
        if (is_precompiled((uint160_t)(intptr_t)code)) return;
        _delete(code);
    }
    uint64_t get_codesize(const uint160_t &address) const {
        uint64_t code_size;
        const uint8_t *code = load_code(get_codehash(address), code_size);
        _delete(code);
        return code_size;
    }
    void register_code(const uint160_t &account, const uint8_t *code, uint64_t code_size) {
        uint256_t codehash = sha3(code, code_size);
        store_code(codehash, code, code_size);
        set_codehash(account, codehash);
    }
    // data access methods
    uint256_t load(const uint160_t &address, const uint256_t &key) const {
        uint416_t extkey = ((uint416_t)address << 256) | (uint416_t)key;
        return data.get(extkey, _load(address, key));
    }
    void store(const uint160_t &address, const uint256_t &key, const uint256_t& value) {
        uint416_t extkey = ((uint416_t)address << 256) | (uint416_t)key;
        data.set(extkey, value, _load(address, key));
    }
    // loads original value directly from the state
    uint256_t _load(const uint160_t &address, const uint256_t &key) const {
        return created.get(address, false) ? 0 : state.load(address, key);
    }
    // address storage clearing
    void clear(const uint160_t &address) {
        created.set(address, true, false);
    }
    // address removal
    void remove(const uint160_t &address) {
        set_nonce(address, 0);
        set_balance(address, 0);
        set_codehash(address, 0);
    }
    // refund access methods
    uint64_t get_refund() {
        return refund_gas;
    }
    void add_refund(uint64_t cost) {
        assert(refund_gas + cost >= refund_gas);
        refund_gas += cost;
    }
    void sub_refund(uint64_t cost) {
        assert(refund_gas >= cost);
        refund_gas -= cost;
    }
    // log access methods
    inline void log0(const uint160_t &address, const uint8_t *data, uint64_t data_size) {
        logs.log0(address, data, data_size);
    }
    inline void log1(const uint160_t &address, const uint256_t &v1, const uint8_t *data, uint64_t data_size) {
        logs.log1(address, v1, data, data_size);
    }
    inline void log2(const uint160_t &address, const uint256_t &v1, const uint256_t &v2, const uint8_t *data, uint64_t data_size) {
        logs.log2(address, v1, v2, data, data_size);
    }
    inline void log3(const uint160_t &address, const uint256_t &v1, const uint256_t &v2, const uint256_t &v3, const uint8_t *data, uint64_t data_size) {
        logs.log3(address, v1, v2, v3, data, data_size);
    }
    inline void log4(const uint160_t &address, const uint256_t &v1, const uint256_t &v2, const uint256_t &v3, const uint256_t &v4, const uint8_t *data, uint64_t data_size) {
        logs.log4(address, v1, v2, v3, v4, data, data_size);
    }
    // transactional methods
    uint64_t snapshot() {
        uint64_t serial1 = nonces.snapshot();
        uint64_t serial2 = balances.snapshot();
        uint64_t serial3 = codehashes.snapshot();
        uint64_t serial4 = data.snapshot();
        uint64_t serial5 = created.snapshot();
        uint64_t serial6 = destructed.snapshot();
        uint64_t serial7 = logs.snapshot();
        assert(serial1 == serial2);
        assert(serial1 == serial3);
        assert(serial1 == serial4);
        assert(serial1 == serial5);
        assert(serial1 == serial6);
        refund_gas_snapshot[serial1-1] = refund_gas;
        uint64_t serial = serial1 << 32 | serial7;
        return serial;
    }
    void commit(uint64_t serial) {
        uint64_t serial1 = serial >> 32;
        uint64_t serial2 = serial & 0xffffffff;
        nonces.commit(serial1);
        balances.commit(serial1);
        codehashes.commit(serial1);
        data.commit(serial1);
        created.commit(serial1);
        destructed.commit(serial1);
        logs.commit(serial2);
    }
    void rollback(uint64_t serial) {
        uint64_t serial1 = serial >> 32;
        uint64_t serial2 = serial & 0xffffffff;
        nonces.rollback(serial1);
        balances.rollback(serial1);
        codehashes.rollback(serial1);
        data.rollback(serial1);
        created.rollback(serial1);
        destructed.rollback(serial1);
        logs.rollback(serial2);
        refund_gas = refund_gas_snapshot[serial1-1];
    }
    inline uint64_t begin() {
        return snapshot();
    }
    void end(uint64_t snapshot, bool success) {
        success ? commit(snapshot) : rollback(snapshot);
    }
    // method to persist changes to the state, called at the end of a transaction
    void flush() {
        Store<uint160_t, bool> touched;
        for (uint64_t i = 0; i < created.size; i++) {
            for (auto keys = created.table[i]; keys != nullptr; keys = keys->next) {
                if (keys->values != nullptr) {
                    if (keys->values->value) state.clear(keys->key);
                }
            }
        }
        for (uint64_t i = 0; i < nonces.size; i++) {
            for (auto keys = nonces.table[i]; keys != nullptr; keys = keys->next) {
                if (keys->values != nullptr) {
                    state.set_nonce(keys->key, keys->values->value);
                    touched.set(keys->key, true, false);
                }
            }
        }
        for (uint64_t i = 0; i < balances.size; i++) {
            for (auto keys = balances.table[i]; keys != nullptr; keys = keys->next) {
                if (keys->values != nullptr) {
                    state.set_balance(keys->key, keys->values->value);
                    touched.set(keys->key, true, false);
                }
            }
        }
        for (uint64_t i = 0; i < codehashes.size; i++) {
            for (auto keys = codehashes.table[i]; keys != nullptr; keys = keys->next) {
                if (keys->values != nullptr) {
                    state.set_codehash(keys->key, keys->values->value);
                    touched.set(keys->key, true, false);
                }
            }
        }
        for (uint64_t i = 0; i < data.size; i++) {
            for (auto keys = data.table[i]; keys != nullptr; keys = keys->next) {
                uint160_t address = (uint160_t)(keys->key >> 256);
                uint256_t key = (uint256_t)keys->key;
                if (keys->values != nullptr) {
                    state.store(address, key, keys->values->value);
                }
            }
        }
        for (uint64_t i = 0; i < destructed.size; i++) {
            for (auto keys = destructed.table[i]; keys != nullptr; keys = keys->next) {
                if (keys->values != nullptr) {
                    if (keys->values->value) state.remove(keys->key);
                }
            }
        }
        for (uint64_t i = 0; i < touched.size; i++) {
            for (auto keys = touched.table[i]; keys != nullptr; keys = keys->next) {
                if (keys->values != nullptr) {
                    if (is_empty(keys->key)) state.remove(keys->key);
                }
            }
        }
        for (uint64_t i = 0; i < logs.count; i++) {
            auto entry = &logs.entries[i];
            switch (entry->topic_count) {
            case 0: state.log0(entry->address, entry->data, entry->data_size); break;
            case 1: state.log1(entry->address, entry->topics[0], entry->data, entry->data_size); break;
            case 2: state.log2(entry->address, entry->topics[0], entry->topics[1], entry->data, entry->data_size); break;
            case 3: state.log3(entry->address, entry->topics[0], entry->topics[1], entry->topics[2], entry->data, entry->data_size); break;
            case 4: state.log4(entry->address, entry->topics[0], entry->topics[1], entry->topics[2], entry->topics[3], entry->data, entry->data_size); break;
            }
        }
    }
    // handy methods to test/modify address state
    void create_account(const uint160_t &address, bool clear_storage) {
        set_codehash(address, EMPTY_CODEHASH);
        if (clear_storage) clear(address);
    }
    bool exists(const uint160_t &address) const {
        uint64_t nonce = get_nonce(address);
        uint256_t balance = get_balance(address);
        uint256_t codehash = get_codehash(address);
        return nonce > 0 || balance > 0 || codehash > 0;
    }
    bool is_empty(const uint160_t &address) const {
        uint64_t nonce = get_nonce(address);
        uint256_t balance = get_balance(address);
        uint256_t codehash = get_codehash(address);
        return nonce == 0 && balance == 0 && (codehash == 0 || codehash == EMPTY_CODEHASH);
    }
    bool has_contract(const uint160_t &address) const {
        uint64_t nonce = get_nonce(address);
        uint256_t codehash = get_codehash(address);
        return nonce > 0 || (codehash != 0 && codehash != EMPTY_CODEHASH);
    }
    bool is_precompiled(const uint160_t &address) const {
        return ECRECOVER <= address && address <= BLAKE2F;
    }
    void destruct_account(const uint160_t &address) {
        destructed.set(address, true, false);
    }
    bool is_destructed(const uint160_t &address) const {
        return destructed.get(address, false);
    }
};

// a simple abstraction of the current block/blockchain
class Block {
public:
    virtual uint64_t forknumber() = 0; // original ethereum mainnet block number, used to pick current release
    virtual uint64_t number() = 0; // block number as provided
    virtual uint64_t timestamp() = 0; // block timestamp as provided
    virtual uint64_t gaslimit() = 0; // block gas limit as provided
    virtual uint160_t coinbase() = 0; // block coinbase as provided
    virtual uint256_t difficulty() = 0; // block difficulty as provided
    virtual uint256_t hash(const uint256_t &number) = 0; // provides block hash from block number
};

// ** execution validation **

// handy routine to check stack bounds
static inline void _throws(stack_check)(uint8_t opc, uint64_t stacktop)
{
    if (stacktop < stackbounds[opc][0]) _throw(STACK_UNDERFLOW);
    if (stacktop > stackbounds[opc][1]) _throw(STACK_OVERFLOW);
}

// handy routine to check memory bounds
static inline void _throws(memory_check)(uint256_t &offset, const uint256_t &size)
{
    // subtlety here: when size is zero memory operation is a nop
    // so we set offset to zero in that regard
    if (size == 0) { offset = 0; return; }
    if ((size >> 64) > 0) _throw(OUTOFBOUNDS_VALUE);
    if ((offset >> 64) > 0) _throw(OUTOFBOUNDS_VALUE);
    if (((offset + size) >> 64) > 0) _throw(OUTOFBOUNDS_VALUE);
}

// handy routine to check contract code size agains limit
static inline void _throws(code_size_check)(Release release, const uint64_t code_size)
{
    if (release >= SPURIOUS_DRAGON) {
        if (code_size > CODE_SIZE) _throw(CODE_EXCEEDED);
    }
}

// a routine to validate JUMP/JUMPI destination against PUSH immediates
// performed on the go, uses an auxiliary bitvector to mark JUMPDEST locations
static void _throws(jumpdest_check)(const uint8_t *code, uint64_t code_size, uint64_t pc, uint8_t *pc_valid, uint64_t &pc_limit)
{
    assert(pc < code_size);
    uint8_t opc = code[pc];
    if (opc != JUMPDEST) _throw(ILLEGAL_TARGET);
    for (; pc_limit <= pc; pc_limit++) {
        uint64_t byte_index = pc_limit / 8;
        uint64_t bit_index = pc_limit % 8;
        if (bit_index == 0) pc_valid[byte_index] = 0;
        uint8_t opc = code[pc_limit];
        switch (opc) {
        case JUMPDEST: { pc_valid[byte_index] |= (1 << bit_index); break; }
        case PUSH1: case PUSH2: case PUSH3: case PUSH4: case PUSH5: case PUSH6: case PUSH7: case PUSH8:
        case PUSH9: case PUSH10: case PUSH11: case PUSH12: case PUSH13: case PUSH14: case PUSH15: case PUSH16:
        case PUSH17: case PUSH18: case PUSH19: case PUSH20: case PUSH21: case PUSH22: case PUSH23: case PUSH24:
        case PUSH25: case PUSH26: case PUSH27: case PUSH28: case PUSH29: case PUSH30: case PUSH31: case PUSH32: {
            const int n = opc - PUSH1 + 1;
            pc_limit += n;
            break;
        }
        default: break;
        }
    }
    uint64_t byte_index = pc / 8;
    uint64_t bit_index = pc % 8;
    if ((pc_valid[byte_index] & (1 << bit_index)) == 0) _throw(ILLEGAL_TARGET);
}

// handy routine to ensure we have enough memory allocated for the call return data
// the call return data is shared across all calls, its capacity is adjusted to hold
// the max amount of data and never shrinks
static inline void _ensure_capacity(uint8_t *&data, uint64_t &size, uint64_t &capacity)
{
    if (size > capacity) {
        uint8_t *buffer = _new<uint8_t>(size);
        _delete(data);
        data = buffer;
        capacity = size;
    }
}

// ** precompiled contracts **

static void _throws(vm_ecrecover)(Release release,
    const uint8_t *call_data, const uint64_t call_size,
    uint8_t *&return_data, uint64_t &return_size, uint64_t &return_capacity, uint64_t &gas)
{
    _handles(consume_gas)(gas, gas_ecrecover(release));
    uint64_t size = 32 + 32 + 32 + 32;
    local<uint8_t> buffer_l(size); uint8_t *buffer = buffer_l.data;
    uint64_t minsize = _min(size, call_size);
    for (uint64_t i = 0; i < minsize; i++) buffer[i] = call_data[i];
    for (uint64_t i = minsize; i < size; i++) buffer[i] = 0;
    uint64_t offset = 0;
    uint256_t h = uint256_t::from(&buffer[offset]); offset += 32;
    uint256_t v = uint256_t::from(&buffer[offset]); offset += 32;
    uint256_t r = uint256_t::from(&buffer[offset]); offset += 32;
    uint256_t s = uint256_t::from(&buffer[offset]); offset += 32;
    uint256_t address;
    _try({
        address = (uint256_t)_catches(ecrecover)(h, v, r, s);
    }, Error e, {
        return_size = 0;
        return;
    })
    return_size = 32;
    _ensure_capacity(return_data, return_size, return_capacity);
    uint256_t::to(address, return_data, return_size);
}

static void _throws(vm_sha256)(Release release,
    const uint8_t *call_data, const uint64_t call_size,
    uint8_t *&return_data, uint64_t &return_size, uint64_t &return_capacity, uint64_t &gas)
{
    _handles(consume_gas)(gas, gas_sha256(release, call_size));
    uint256_t hash = sha256(call_data, call_size);
    return_size = 32;
    _ensure_capacity(return_data, return_size, return_capacity);
    uint256_t::to(hash, return_data, return_size);
}

static void _throws(vm_ripemd160)(Release release,
    const uint8_t *call_data, const uint64_t call_size,
    uint8_t *&return_data, uint64_t &return_size, uint64_t &return_capacity, uint64_t &gas)
{
    _handles(consume_gas)(gas, gas_ripemd160(release, call_size));
    uint256_t hash = (uint256_t)ripemd160(call_data, call_size);
    return_size = 32;
    _ensure_capacity(return_data, return_size, return_capacity);
    uint256_t::to(hash, return_data, return_size);
}

static void _throws(vm_datacopy)(Release release,
    const uint8_t *call_data, const uint64_t call_size,
    uint8_t *&return_data, uint64_t &return_size, uint64_t &return_capacity, uint64_t &gas)
{
    _handles(consume_gas)(gas, gas_datacopy(release, call_size));
    return_size = call_size;
    _ensure_capacity(return_data, return_size, return_capacity);
    for (uint64_t i = 0; i < return_size; i++) return_data[i] = call_data[i];
}

static void _throws(vm_bigmodexp)(Release release,
    const uint8_t *call_data, const uint64_t call_size,
    uint8_t *&return_data, uint64_t &return_size, uint64_t &return_capacity, uint64_t &gas)
{
    uint64_t size1 = 3 * 32;
    local<uint8_t> buffer1_l(size1); uint8_t *buffer1 = buffer1_l.data;
    uint64_t minsize1 = _min(size1, call_size);
    for (uint64_t i = 0; i < minsize1; i++) buffer1[i] = call_data[i];
    for (uint64_t i = minsize1; i < size1; i++) buffer1[i] = 0;
    uint64_t offset1 = 0;
    bigint base_len = bigint::from(&buffer1[offset1], 32); offset1 += 32;
    bigint exp_len = bigint::from(&buffer1[offset1], 32); offset1 += 32;
    bigint mod_len = bigint::from(&buffer1[offset1], 32); offset1 += 32;
    bigint base;
    bigint base_mul;
    {
        bigint size2 = base_len;
        uint64_t minsize2 = size2 > call_size - minsize1 ? call_size - minsize1 : size2.cast64();
        base = bigint::from(&call_data[minsize1], minsize2); minsize1 += minsize2;
        base_mul = size2 - minsize2;
    }
    bigint exp;
    bigint exp_mul;
    {
        bigint size2 = exp_len;
        uint64_t minsize2 = size2 > call_size - minsize1 ? call_size - minsize1 : size2.cast64();
        exp = bigint::from(&call_data[minsize1], minsize2); minsize1 += minsize2;
        exp_mul = size2 - minsize2;
    }
    bigint mod;
    bigint mod_mul;
    {
        bigint size2 = mod_len;
        uint64_t minsize2 = size2 > call_size - minsize1 ? call_size - minsize1 : size2.cast64();
        mod = bigint::from(&call_data[minsize1], minsize2); minsize1 += minsize2;
        mod_mul = size2 - minsize2;
    }
    bigint log2_exp = exp > 0 ? exp.bitlen() - 1 + 8 * exp_mul : 0;
    bigint cut_off = exp_len > 32 ? 8 * (exp_len - 32) : 0;
    log2_exp = log2_exp > cut_off ? log2_exp - cut_off : 0;
    _handles(consume_gas)(gas, gas_bigmodexp(release, base_len, exp_len, mod_len, log2_exp));
    if (exp > 0) exp <<= 8 * exp_mul.cast64();
    if (base > 0) base <<= 8 * base_mul.cast64();
    if (mod > 0) mod <<= 8 * mod_mul.cast64();
    bigint res = mod == 0 ? 0 : bigmodexp(base, exp, mod);
    return_size = mod_len.cast64();
    _ensure_capacity(return_data, return_size, return_capacity);
    bigint::to(res, return_data, return_size);
}

static void _throws(vm_bn256add)(Release release,
    const uint8_t *call_data, const uint64_t call_size,
    uint8_t *&return_data, uint64_t &return_size, uint64_t &return_capacity, uint64_t &gas)
{
    _handles(consume_gas)(gas, gas_bn256add(release));
    uint64_t size = 2 * 2 * 32;
    local<uint8_t> buffer_l(size); uint8_t *buffer = buffer_l.data;
    uint64_t minsize = _min(size, call_size);
    for (uint64_t i = 0; i < minsize; i++) buffer[i] = call_data[i];
    for (uint64_t i = minsize; i < size; i++) buffer[i] = 0;
    uint64_t offset = 0;
    bigint x1 = bigint::from(&buffer[offset], 32); offset += 32;
    bigint y1 = bigint::from(&buffer[offset], 32); offset += 32;
    bigint x2 = bigint::from(&buffer[offset], 32); offset += 32;
    bigint y2 = bigint::from(&buffer[offset], 32); offset += 32;
    if (x1 >= G1::P()) _throw(INVALID_ENCODING);
    if (y1 >= G1::P()) _throw(INVALID_ENCODING);
    if (x2 >= G1::P()) _throw(INVALID_ENCODING);
    if (y2 >= G1::P()) _throw(INVALID_ENCODING);
    G1 p1(x1, y1);
    G1 p2(x2, y2);
    if (!(x1 == 0 && y1 == 0)) {
        if (!p1.is_valid()) _throw(INVALID_ENCODING);
    }
    if (!(x2 == 0 && y2 == 0)) {
        if (!p2.is_valid()) _throw(INVALID_ENCODING);
    }
    G1 p3 = bn256add(p1, p2);
    bigint x3 = p3.x;
    bigint y3 = p3.y;
    if (p3.is_inf()) { x3 = 0; y3 = 0; }
    return_size = 2 * 32;
    _ensure_capacity(return_data, return_size, return_capacity);
    uint64_t return_offset = 0;
    bigint::to(x3, &return_data[return_offset], 32); return_offset += 32;
    bigint::to(y3, &return_data[return_offset], 32); return_offset += 32;
}

static void _throws(vm_bn256scalarmul)(Release release,
    const uint8_t *call_data, const uint64_t call_size,
    uint8_t *&return_data, uint64_t &return_size, uint64_t &return_capacity, uint64_t &gas)
{
    _handles(consume_gas)(gas, gas_bn256scalarmul(release));
    uint64_t size = 2 * 32 + 32;
    local<uint8_t> buffer_l(size); uint8_t *buffer = buffer_l.data;
    uint64_t minsize = _min(size, call_size);
    for (uint64_t i = 0; i < minsize; i++) buffer[i] = call_data[i];
    for (uint64_t i = minsize; i < size; i++) buffer[i] = 0;
    uint64_t offset = 0;
    bigint x1 = bigint::from(&buffer[offset], 32); offset += 32;
    bigint y1 = bigint::from(&buffer[offset], 32); offset += 32;
    bigint e = bigint::from(&buffer[offset], 32); offset += 32;
    if (x1 >= G1::P()) _throw(INVALID_ENCODING);
    if (y1 >= G1::P()) _throw(INVALID_ENCODING);
    G1 p1(x1, y1);
    if (!(x1 == 0 && y1 == 0)) {
        if (!p1.is_valid()) _throw(INVALID_ENCODING);
    }
    G1 p2 = bn256scalarmul(p1, e);
    bigint x2 = p2.x;
    bigint y2 = p2.y;
    if (p2.is_inf()) { x2 = 0; y2 = 0; }
    return_size = 2 * 32;
    _ensure_capacity(return_data, return_size, return_capacity);
    uint64_t return_offset = 0;
    bigint::to(x2, &return_data[return_offset], 32); return_offset += 32;
    bigint::to(y2, &return_data[return_offset], 32); return_offset += 32;
}

static void _throws(vm_bn256pairing)(Release release,
    const uint8_t *call_data, const uint64_t call_size,
    uint8_t *&return_data, uint64_t &return_size, uint64_t &return_capacity, uint64_t &gas)
{
    if (call_size % (2 * 32 + 2 * 2 * 32) != 0) _throw(INVALID_SIZE);
    uint64_t count = call_size / (2 * 32 + 2 * 2 * 32);
    _handles(consume_gas)(gas, gas_bn256pairing(release, count));
    std::vector<G1> curve_points(count);
    std::vector<G2> twist_points(count);
    uint64_t call_offset = 0;
    for (uint64_t i = 0; i < count; i++) {
        bigint x1 = bigint::from(&call_data[call_offset], 32); call_offset += 32;
        bigint y1 = bigint::from(&call_data[call_offset], 32); call_offset += 32;
        if (x1 >= G1::P()) _throw(INVALID_ENCODING);
        if (y1 >= G1::P()) _throw(INVALID_ENCODING);
        G1 g1(x1, y1);
        if (!(x1 == 0 && y1 == 0)) {
            if (!g1.is_valid()) _throw(INVALID_ENCODING);
        }
        curve_points[i] = g1;
        bigint xx2 = bigint::from(&call_data[call_offset], 32); call_offset += 32;
        bigint xy2 = bigint::from(&call_data[call_offset], 32); call_offset += 32;
        bigint yx2 = bigint::from(&call_data[call_offset], 32); call_offset += 32;
        bigint yy2 = bigint::from(&call_data[call_offset], 32); call_offset += 32;
        if (xx2 >= G1::P()) _throw(INVALID_ENCODING);
        if (xy2 >= G1::P()) _throw(INVALID_ENCODING);
        if (yx2 >= G1::P()) _throw(INVALID_ENCODING);
        if (yy2 >= G1::P()) _throw(INVALID_ENCODING);
        G2 g2(Gen2(xx2, xy2), Gen2(yx2, yy2));
        if (!(xx2 == 0 && xy2 == 0 && yx2 == 0 && yy2 == 0)) {
            if (!g2.is_valid()) _throw(INVALID_ENCODING);
        }
        twist_points[i] = g2;
    }
    bool pairs = bn256pairing(curve_points, twist_points, count);
    return_size = 32;
    _ensure_capacity(return_data, return_size, return_capacity);
    uint256_t::to(pairs, return_data);
}

static void _throws(vm_blake2f)(Release release,
    const uint8_t *call_data, const uint64_t call_size,
    uint8_t *&return_data, uint64_t &return_size, uint64_t &return_capacity, uint64_t &gas)
{
    if (call_size != 4 + 8 * 8 + 16 * 8 + 2 * 8 + 1) _throw(INVALID_SIZE);
    if (call_data[call_size-1] > 1) _throw(INVALID_ENCODING);
    uint64_t call_offset = 0;
    uint32_t rounds = b2w32be(&call_data[call_offset]); call_offset += 4;
    _handles(consume_gas)(gas, gas_blake2f(release, rounds));
    uint64_t h0 = b2w64le(&call_data[call_offset]); call_offset += 8;
    uint64_t h1 = b2w64le(&call_data[call_offset]); call_offset += 8;
    uint64_t h2 = b2w64le(&call_data[call_offset]); call_offset += 8;
    uint64_t h3 = b2w64le(&call_data[call_offset]); call_offset += 8;
    uint64_t h4 = b2w64le(&call_data[call_offset]); call_offset += 8;
    uint64_t h5 = b2w64le(&call_data[call_offset]); call_offset += 8;
    uint64_t h6 = b2w64le(&call_data[call_offset]); call_offset += 8;
    uint64_t h7 = b2w64le(&call_data[call_offset]); call_offset += 8;
    uint64_t w[16];
    for (int i = 0; i < 16; i++) { w[i] = b2w64le(&call_data[call_offset]); call_offset += 8; }
    uint64_t t0 = b2w64le(&call_data[call_offset]); call_offset += 8;
    uint64_t t1 = b2w64le(&call_data[call_offset]); call_offset += 8;
    bool last_chunk = call_data[call_size-1] > 0;
    blake2f(rounds,
        h0, h1, h2, h3,
        h4, h5, h6, h7,
        w, t0, t1, last_chunk);
    return_size = 8 * 8;
    _ensure_capacity(return_data, return_size, return_capacity);
    uint64_t return_offset = 0;
    w2b64le(h0, &return_data[return_offset]); return_offset += 8;
    w2b64le(h1, &return_data[return_offset]); return_offset += 8;
    w2b64le(h2, &return_data[return_offset]); return_offset += 8;
    w2b64le(h3, &return_data[return_offset]); return_offset += 8;
    w2b64le(h4, &return_data[return_offset]); return_offset += 8;
    w2b64le(h5, &return_data[return_offset]); return_offset += 8;
    w2b64le(h6, &return_data[return_offset]); return_offset += 8;
    w2b64le(h7, &return_data[return_offset]); return_offset += 8;
}

// ** interpreter **

// this is the main interpreter routine, which implements all opcodes
// it takes as parameters the full context: release, block abstraction, storage,
// origin address, gas price, current contract address, current contract bytecode,
// caller address, call amount, call data, return data, and available gas
// additionally it takes the current read/read-write mode and call stack depth
// it holds the stack frame for the evm which comprises stack, memory and pc
// it is called recursivelly for CALL and CREATE families of opcodes
// it throws on error and returns true on success and false on revert
static bool _throws(vm_run)(Release release, Block &block, Storage &storage,
    const uint160_t &origin_address, const uint256_t &gas_price,
    const uint160_t &owner_address, const uint8_t *code, const uint64_t code_size,
    const uint160_t &caller_address, const uint256_t &call_value, const uint8_t *call_data, const uint64_t call_size,
    uint8_t *&return_data, uint64_t &return_size, uint64_t &return_capacity, uint64_t &gas,
    bool read_only, uint64_t depth)
{
    if (code_size == 0) { // do nothing if contract code is empty
        if ((intptr_t)code < 256) { // but first test for precompiled contract
            uint8_t opc = (intptr_t)code;
            if ((pre[release] & (_1 << opc)) > 0) { // and which precompiled contracts are available
#ifndef NDEBUG
                if (std::getenv("EVM_DEBUG")) std::cout << prenames[opc] << std::endl;
#endif // NDEBUG
                switch (opc) {
                case ECRECOVER: {
                    _handles0(vm_ecrecover)(release, call_data, call_size, return_data, return_size, return_capacity, gas);
                    return true;
                }
                case SHA256: {
                    _handles0(vm_sha256)(release, call_data, call_size, return_data, return_size, return_capacity, gas);
                    return true;
                }
                case RIPEMD160: {
                    _handles0(vm_ripemd160)(release, call_data, call_size, return_data, return_size, return_capacity, gas);
                    return true;
                }
                case DATACOPY: {
                    _handles0(vm_datacopy)(release, call_data, call_size, return_data, return_size, return_capacity, gas);
                    return true;
                }
                case BIGMODEXP: {
                    _handles0(vm_bigmodexp)(release, call_data, call_size, return_data, return_size, return_capacity, gas);
                    return true;
                }
                case BN256ADD: {
                    _handles0(vm_bn256add)(release, call_data, call_size, return_data, return_size, return_capacity, gas);
                    return true;
                }
                case BN256SCALARMUL: {
                    _handles0(vm_bn256scalarmul)(release, call_data, call_size, return_data, return_size, return_capacity, gas);
                    return true;
                }
                case BN256PAIRING: {
                    _handles0(vm_bn256pairing)(release, call_data, call_size, return_data, return_size, return_capacity, gas);
                    return true;
                }
                case BLAKE2F: {
                    _handles0(vm_blake2f)(release, call_data, call_size, return_data, return_size, return_capacity, gas);
                    return true;
                }
                default: assert(false);
                }
            }
        }
        return_size = 0;
        return true;
    }
    return_size = 0;
    Stack stack;
    Memory memory;
    uint64_t pc_limit = 0;
    local<uint8_t> pc_valid_l((code_size + 7) / 8); uint8_t *pc_valid = pc_valid_l.data;
    for (uint64_t pc = 0; ; pc++) { // main execution loop, one opcode at a time
        uint8_t opc = pc < code_size ? code[pc] : STOP; // get the next opcode
#ifndef NDEBUG
        if (std::getenv("EVM_DEBUG")) std::cout << opcodes[opc] << std::endl;
#endif // NDEBUG
        if ((is[release] & (_1 << opc)) == 0) _throw0(INVALID_OPCODE); // check is the opcode is available
        _handles0(stack_check)(opc, stack.top()); // validates the stack
        if (read_only && (is_writes & (_1 << opc)) > 0) _throw0(ILLEGAL_UPDATE); // validates write opcode in read-only mode
        _handles0(consume_gas)(gas, gas_opcode(release, opc)); // consumes the constant part of gas for the opcode
        switch (opc) {
        case STOP: { return_size = 0; return true; }
        case ADD: { uint256_t v1 = stack.pop(), v2 = stack.pop(); stack.push(v1 + v2); break; }
        case MUL: { uint256_t v1 = stack.pop(), v2 = stack.pop(); stack.push(v1 * v2); break; }
        case SUB: { uint256_t v1 = stack.pop(), v2 = stack.pop(); stack.push(v1 - v2); break; }
        case DIV: { uint256_t v1 = stack.pop(), v2 = stack.pop(); stack.push(v2 == 0 ? 0 : v1 / v2); break; }
        case SDIV: {
            uint256_t v1 = stack.pop(), v2 = stack.pop();
            bool is_neg1 = (v1.byte(31) & 0x80) > 0;
            bool is_neg2 = (v2.byte(31) & 0x80) > 0;
            if (is_neg1) v1 = -v1;
            if (is_neg2) v2 = -v2;
            uint256_t v3 = v2 == 0 ? 0 : v1 / v2;
            if (is_neg1 != is_neg2) v3 = -v3;
            stack.push(v3);
            break;
        }
        case MOD: { uint256_t v1 = stack.pop(), v2 = stack.pop(); stack.push(v2 == 0 ? 0 : v1 % v2); break; }
        case SMOD: {
            uint256_t v1 = stack.pop(), v2 = stack.pop();
            bool is_neg1 = (v1.byte(31) & 0x80) > 0;
            bool is_neg2 = (v2.byte(31) & 0x80) > 0;
            if (is_neg1) v1 = -v1;
            if (is_neg2) v2 = -v2;
            uint256_t v3 = v2 == 0 ? 0 : v1 % v2;
            if (is_neg1) v3 = -v3;
            stack.push(v3);
            break;
        }
        case ADDMOD: { uint256_t v1 = stack.pop(), v2 = stack.pop(), v3 = stack.pop(); stack.push(v3 == 0 ? 0 : uint256_t::addmod(v1, v2, v3)); break; }
        case MULMOD: { uint256_t v1 = stack.pop(), v2 = stack.pop(), v3 = stack.pop(); stack.push(v3 == 0 ? 0 : uint256_t::mulmod(v1, v2, v3)); break; }
        case EXP: {
            uint256_t v1 = stack.pop(), v2 = stack.pop();
            _handles0(consume_gas)(gas, gas_exp(release, v2.bytelen()));
            stack.push(uint256_t::pow(v1, v2));
            break;
        }
        case SIGNEXTEND: { uint256_t v1 = stack.pop(), v2 = stack.pop(); stack.push(v1 < 31 ? v2.signext(v1.cast64()) : v2); break; }
        case LT: { uint256_t v1 = stack.pop(), v2 = stack.pop(); stack.push(v1 < v2); break; }
        case GT: { uint256_t v1 = stack.pop(), v2 = stack.pop(); stack.push(v1 > v2); break; }
        case SLT: { uint256_t v1 = stack.pop(), v2 = stack.pop(); stack.push(v1.signflip() < v2.signflip()); break; }
        case SGT: { uint256_t v1 = stack.pop(), v2 = stack.pop(); stack.push(v1.signflip() > v2.signflip()); break; }
        case EQ: { uint256_t v1 = stack.pop(), v2 = stack.pop(); stack.push(v1 == v2); break; }
        case ISZERO: { uint256_t v1 = stack.pop(); stack.push(v1 == 0); break; }
        case AND: { uint256_t v1 = stack.pop(), v2 = stack.pop(); stack.push(v1 & v2); break; }
        case OR: { uint256_t v1 = stack.pop(), v2 = stack.pop(); stack.push(v1 | v2); break; }
        case XOR: { uint256_t v1 = stack.pop(), v2 = stack.pop(); stack.push(v1 ^ v2); break; }
        case NOT: { uint256_t v1 = stack.pop(); stack.push(~v1); break; }
        case BYTE: { uint256_t v1 = stack.pop(), v2 = stack.pop(); stack.push(v1 < 32 ? v2.byte(31 - v1.cast64()) : 0); break; }
        case SHL: { uint256_t v1 = stack.pop(), v2 = stack.pop(); stack.push(v1 > 255 ? 0 : v2 << v1.cast64()); break; }
        case SHR: { uint256_t v1 = stack.pop(), v2 = stack.pop(); stack.push(v1 > 255 ? 0 : v2 >> v1.cast64()); break; }
        case SAR: { uint256_t v1 = stack.pop(), v2 = stack.pop(); stack.push(v1 > 255 ? ((v2.byte(31) & 0x80) > 0 ? ~(uint256_t)0 : 0) : uint256_t::sar(v2, v1.cast64())); break; }
        case SHA3: {
            uint256_t v1 = stack.pop(), v2 = stack.pop();
            _handles0(memory_check)(v1, v2);
            uint64_t offset = v1.cast64(), size = v2.cast64();
            _handles0(consume_gas)(gas, gas_memory(release, memory.size(), offset + size));
            _handles0(consume_gas)(gas, gas_sha3(release, size));
            local<uint8_t> buffer_l(size); uint8_t *buffer = buffer_l.data;
            memory.dump(offset, size, buffer);
            stack.push(sha3(buffer, size));
            break;
        }
        case ADDRESS: { stack.push((uint256_t)owner_address); break; }
        case BALANCE: { uint160_t address = (uint160_t)stack.pop(); stack.push(storage.get_balance(address)); break; }
        case ORIGIN: { stack.push((uint256_t)origin_address); break; }
        case CALLER: { stack.push((uint256_t)caller_address); break; }
        case CALLVALUE: { stack.push(call_value); break; }
        case CALLDATALOAD: {
            uint256_t v1 = stack.pop();
            uint64_t offset = v1 > call_size ? call_size : v1.cast64();
            uint8_t buffer[32];
            uint64_t size = 32;
            if (offset + size > call_size) size = call_size - offset;
            for (uint64_t i = 0; i < size; i++) buffer[i] = call_data[offset + i];
            for (uint64_t i = size; i < 32; i++) buffer[i] = 0;
            stack.push(uint256_t::from(buffer));
            break;
        }
        case CALLDATASIZE: { stack.push(call_size); break; }
        case CALLDATACOPY: {
            uint256_t v1 = stack.pop(), v2 = stack.pop(), v3 = stack.pop();
            _handles0(memory_check)(v1, v3);
            uint64_t offset1 = v1.cast64(), size = v3.cast64();
            _handles0(consume_gas)(gas, gas_memory(release, memory.size(), offset1 + size));
            _handles0(consume_gas)(gas, gas_copy(release, size));
            uint64_t offset2 = v2 > call_size ? call_size : v2.cast64();
            memory.burn(offset1, size, &call_data[offset2], _min(size, call_size - offset2));
            break;
        }
        case CODESIZE: { stack.push(code_size); break; }
        case CODECOPY: {
            uint256_t v1 = stack.pop(), v2 = stack.pop(), v3 = stack.pop();
            _handles0(memory_check)(v1, v3);
            uint64_t offset1 = v1.cast64(), size = v3.cast64();
            _handles0(consume_gas)(gas, gas_memory(release, memory.size(), offset1 + size));
            _handles0(consume_gas)(gas, gas_copy(release, size));
            uint64_t offset2 = v2 > code_size ? code_size : v2.cast64();
            memory.burn(offset1, size, &code[offset2], _min(size, code_size - offset2));
            break;
        }
        case GASPRICE: { stack.push(gas_price); break; }
        case EXTCODESIZE: { uint160_t address = (uint160_t)stack.pop(); stack.push(storage.get_codesize(address)); break; }
        case EXTCODECOPY: {
            uint160_t address = (uint160_t)stack.pop();
            uint256_t v2 = stack.pop(), v3 = stack.pop(), v4 = stack.pop();
            _handles0(memory_check)(v2, v4);
            uint64_t offset1 = v2.cast64(), size = v4.cast64();
            _handles0(consume_gas)(gas, gas_memory(release, memory.size(), offset1 + size));
            _handles0(consume_gas)(gas, gas_copy(release, size));
            uint64_t extcode_size;
            uint8_t *extcode = storage.get_code(address, extcode_size);
            uint64_t offset2 = v3 > extcode_size ? extcode_size : v3.cast64();
            memory.burn(offset1, size, &extcode[offset2], _min(size, extcode_size - offset2));
            storage.release_code(extcode);
            break;
        }
        case RETURNDATASIZE: { stack.push(return_size); break; }
        case RETURNDATACOPY: {
            uint256_t v1 = stack.pop(), v2 = stack.pop(), v3 = stack.pop();
            _handles0(memory_check)(v1, v3);
            uint64_t offset1 = v1.cast64(), size = v3.cast64();
            _handles0(consume_gas)(gas, gas_memory(release, memory.size(), offset1 + size));
            _handles0(consume_gas)(gas, gas_copy(release, size));
            if (v2 + size < v2) _throw0(OUTOFBOUNDS_VALUE);
            if (v2 + size > return_size) _throw0(OUTOFBOUNDS_VALUE); // this seems to be an exception among copy
            uint64_t offset2 = v2 > return_size ? return_size : v2.cast64();
            memory.burn(offset1, size, &return_data[offset2], _min(size, return_size - offset2));
            break;
        }
        case EXTCODEHASH: { uint160_t address = (uint160_t)stack.pop(); stack.push(storage.get_codehash(address)); break; }
        case BLOCKHASH: { uint256_t v1 = stack.pop(); stack.push(v1 < block.number()-256 || v1 >= block.number() ? 0 : block.hash(v1)); break; }
        case COINBASE: { stack.push((uint256_t)block.coinbase()); break; }
        case TIMESTAMP: { stack.push(block.timestamp()); break; }
        case NUMBER: { stack.push(block.number()); break; }
        case DIFFICULTY: { stack.push(block.difficulty()); break; }
        case GASLIMIT: { stack.push(block.gaslimit()); break; }
        case CHAINID: { stack.push(CHAIN_ID); break; }
        case SELFBALANCE: { stack.push(storage.get_balance(owner_address)); break; }
        case POP: { stack.pop(); break; }
        case MLOAD: {
            uint256_t v1 = stack.pop();
            _handles0(memory_check)(v1, 32);
            uint64_t offset = v1.cast64();
            _handles0(consume_gas)(gas, gas_memory(release, memory.size(), offset + 32));
            stack.push(memory.load(offset));
            break;
        }
        case MSTORE: {
            uint256_t v1 = stack.pop(), v2 = stack.pop();
            _handles0(memory_check)(v1, 32);
            uint64_t offset = v1.cast64();
            _handles0(consume_gas)(gas, gas_memory(release, memory.size(), offset + 32));
            memory.store(offset, v2);
            break;
        }
        case MSTORE8: {
            uint256_t v1 = stack.pop(), v2 = stack.pop();
            _handles0(memory_check)(v1, 1);
            uint64_t offset = v1.cast64();
            _handles0(consume_gas)(gas, gas_memory(release, memory.size(), offset + 1));
            uint8_t buffer[1];
            buffer[0] = v2.byte(0);
            memory.burn(offset, buffer, 1);
            break;
        }
        case SLOAD: { uint256_t address = stack.pop(); stack.push(storage.load(owner_address, address)); break; }
        case SSTORE: {
            uint256_t address = stack.pop(), value = stack.pop();
            uint256_t current = storage.load(owner_address, address);
            uint256_t original = storage._load(owner_address, address);
            bool init = original == 0;
            bool dirty = current != original;
            bool noop = current == value;
            bool sets = current == 0 && value > 0;
            bool clears = current > 0 && value == 0;
            bool cleans = original == value;
            _handles0(consume_gas)(gas, gas_sstore(release, gas, init, dirty, noop, sets, clears, cleans));
            storage.add_refund(gas_refund_sstore(release, init, dirty, noop, sets, clears, cleans));
            storage.sub_refund(gas_unrefund_sstore(release, init, dirty, noop, sets, clears, cleans));
            storage.store(owner_address, address, value);
            break;
        }
        case JUMP: {
            uint256_t v1 = stack.pop();
            if (v1 >= code_size) _throw0(ILLEGAL_TARGET);
            pc = v1.cast64();
            _handles0(jumpdest_check)(code, code_size, pc, pc_valid, pc_limit);
            pc--;
            break;
        }
        case JUMPI: {
            uint256_t v1 = stack.pop(), v2 = stack.pop();
            if (v2 != 0) {
                if (v1 >= code_size) _throw0(ILLEGAL_TARGET);
                pc = v1.cast64();
                _handles0(jumpdest_check)(code, code_size, pc, pc_valid, pc_limit);
                pc--;
                break;
            }
            break;
        }
        case PC: { stack.push(pc); break; }
        case MSIZE: { stack.push(memory.size()); break; }
        case GAS: { stack.push(gas); break; }
        case JUMPDEST: { break; }
        case PUSH1: case PUSH2: case PUSH3: case PUSH4: case PUSH5: case PUSH6: case PUSH7: case PUSH8:
        case PUSH9: case PUSH10: case PUSH11: case PUSH12: case PUSH13: case PUSH14: case PUSH15: case PUSH16:
        case PUSH17: case PUSH18: case PUSH19: case PUSH20: case PUSH21: case PUSH22: case PUSH23: case PUSH24:
        case PUSH25: case PUSH26: case PUSH27: case PUSH28: case PUSH29: case PUSH30: case PUSH31: case PUSH32: {
            const int n = opc - PUSH1 + 1;
            uint256_t v1 = uint256_t::from(&code[pc+1], _min(n, code_size - (pc + 1)));
            stack.push(v1);
            pc += n;
            break;
        }
        case DUP1: case DUP2: case DUP3: case DUP4: case DUP5: case DUP6: case DUP7: case DUP8:
        case DUP9: case DUP10: case DUP11: case DUP12: case DUP13: case DUP14: case DUP15: case DUP16: {
            const int n = opc - DUP1 + 1;
            uint256_t v1 = stack[n];
            stack.push(v1);
            break;
        }
        case SWAP1: case SWAP2: case SWAP3: case SWAP4: case SWAP5: case SWAP6: case SWAP7: case SWAP8:
        case SWAP9: case SWAP10: case SWAP11: case SWAP12: case SWAP13: case SWAP14: case SWAP15: case SWAP16: {
            const int n = opc - SWAP1 + 2;
            uint256_t v1 = stack[1];
            stack[1] = stack[n];
            stack[n] = v1;
            break;
        }
        case LOG0: {
            uint256_t v1 = stack.pop(), v2 = stack.pop();
            _handles0(memory_check)(v1, v2);
            uint64_t offset = v1.cast64(), size = v2.cast64();
            _handles0(consume_gas)(gas, gas_memory(release, memory.size(), offset + size));
            _handles0(consume_gas)(gas, gas_log(release, 0, size));
            local<uint8_t> buffer_l(size); uint8_t *buffer = buffer_l.data;
            memory.dump(offset, size, buffer);
            storage.log0(owner_address, buffer, size);
            break;
        }
        case LOG1: {
            uint256_t v1 = stack.pop(), v2 = stack.pop(), v3 = stack.pop();
            _handles0(memory_check)(v1, v2);
            uint64_t offset = v1.cast64(), size = v2.cast64();
            _handles0(consume_gas)(gas, gas_memory(release, memory.size(), offset + size));
            _handles0(consume_gas)(gas, gas_log(release, 1, size));
            local<uint8_t> buffer_l(size); uint8_t *buffer = buffer_l.data;
            memory.dump(offset, size, buffer);
            storage.log1(owner_address, v3, buffer, size);
            break;
        }
        case LOG2: {
            uint256_t v1 = stack.pop(), v2 = stack.pop(), v3 = stack.pop(), v4 = stack.pop();
            _handles0(memory_check)(v1, v2);
            uint64_t offset = v1.cast64(), size = v2.cast64();
            _handles0(consume_gas)(gas, gas_memory(release, memory.size(), offset + size));
            _handles0(consume_gas)(gas, gas_log(release, 2, size));
            local<uint8_t> buffer_l(size); uint8_t *buffer = buffer_l.data;
            memory.dump(offset, size, buffer);
            storage.log2(owner_address, v3, v4, buffer, size);
            break;
        }
        case LOG3: {
            uint256_t v1 = stack.pop(), v2 = stack.pop(), v3 = stack.pop(), v4 = stack.pop(), v5 = stack.pop();
            _handles0(memory_check)(v1, v2);
            uint64_t offset = v1.cast64(), size = v2.cast64();
            _handles0(consume_gas)(gas, gas_memory(release, memory.size(), offset + size));
            _handles0(consume_gas)(gas, gas_log(release, 3, size));
            local<uint8_t> buffer_l(size); uint8_t *buffer = buffer_l.data;
            memory.dump(offset, size, buffer);
            storage.log3(owner_address, v3, v4, v5, buffer, size);
            break;
        }
        case LOG4: {
            uint256_t v1 = stack.pop(), v2 = stack.pop(), v3 = stack.pop(), v4 = stack.pop(), v5 = stack.pop(), v6 = stack.pop();
            _handles0(memory_check)(v1, v2);
            uint64_t offset = v1.cast64(), size = v2.cast64();
            _handles0(consume_gas)(gas, gas_memory(release, memory.size(), offset + size));
            _handles0(consume_gas)(gas, gas_log(release, 4, size));
            local<uint8_t> buffer_l(size); uint8_t *buffer = buffer_l.data;
            memory.dump(offset, size, buffer);
            storage.log4(owner_address, v3, v4, v5, v6, buffer, size);
            break;
        }
        case CREATE: {
            uint256_t value = stack.pop();
            uint256_t v1 = stack.pop(), v2 = stack.pop();
            _handles0(memory_check)(v1, v2);
            uint64_t init_offset = v1.cast64(), init_size = v2.cast64();
            _handles0(consume_gas)(gas, gas_memory(release, memory.size(), init_offset + init_size));
            uint64_t create_gas = gas_cap(release, gas, gas);
            _handles0(consume_gas)(gas, create_gas);
            local<uint8_t> init_l(init_size); uint8_t *init = init_l.data;
            memory.dump(init_offset, init_size, init);
            if (depth >= CALL_DEPTH || storage.get_balance(owner_address) < value) {
                return_size = 0;
                credit_gas(gas, create_gas);
                stack.push(false);
                break;
            }
            uint160_t code_address = _handles0(gen_contract_address)(owner_address, storage.get_nonce(owner_address));
            storage.increment_nonce(owner_address);
            uint64_t snapshot = storage.begin();
            bool success;
            _try({
                if (storage.has_contract(code_address)) _trythrow(CODE_CONFLICT);
                storage.create_account(code_address, true);
                if (release >= SPURIOUS_DRAGON) storage.set_nonce(code_address, 1);
                storage.sub_balance(owner_address, value);
                storage.add_balance(code_address, value);
                success = _catches(vm_run)(release, block, storage,
                                origin_address, gas_price,
                                code_address, init, init_size,
                                owner_address, value, nullptr, 0,
                                return_data, return_size, return_capacity, create_gas,
                                read_only, depth+1);
                if (success) {
                    _catches(code_size_check)(release, return_size);
                    _try({
                        _catches(consume_gas)(create_gas, gas_create(release, return_size));
                        storage.register_code(code_address, return_data, return_size);
                    }, Error e ,{
                        if (release >= HOMESTEAD) _trythrow(e);
                    })
                    return_size = 0;
                }
                credit_gas(gas, create_gas);
            }, Error e, {
                success = false;
                return_size = 0;
            })
            storage.end(snapshot, success);
            stack.push(success ? (uint256_t)code_address : 0);
            break;
        }
        case CALL: {
            uint256_t v0 = stack.pop();
            uint160_t code_address = (uint160_t)stack.pop();
            uint256_t value = stack.pop();
            uint256_t v1 = stack.pop(), v2 = stack.pop(), v3 = stack.pop(), v4 = stack.pop();
            if (read_only && value != 0) _throw0(ILLEGAL_UPDATE);
            _handles0(memory_check)(v1, v2);
            _handles0(memory_check)(v3, v4);
            uint64_t args_offset = v1.cast64(), args_size = v2.cast64(), ret_offset = v3.cast64(), ret_size = v4.cast64();
            _handles0(consume_gas)(gas, gas_memory(release, memory.size(), _max(args_offset + args_size, ret_offset + ret_size)));
            _handles0(consume_gas)(gas, gas_call(release, value > 0, storage.is_empty(code_address), storage.exists(code_address)));
            uint64_t reserved_gas = v0 > gas ? gas : v0.cast64();
            uint64_t call_gas = gas_cap(release, gas, reserved_gas);
            _handles0(consume_gas)(gas, call_gas);
            credit_gas(call_gas, gas_stipend_call(release, value > 0));
            local<uint8_t> args_data_l(args_size); uint8_t *args_data = args_data_l.data;
            memory.dump(args_offset, args_size, args_data);
            memory.mark(ret_offset + ret_size);
            if (depth >= CALL_DEPTH || storage.get_balance(owner_address) < value) {
                return_size = 0;
                credit_gas(gas, call_gas);
                stack.push(false);
                break;
            }
            if (release >= SPURIOUS_DRAGON) {
                if (value == 0) {
                    if (!storage.is_precompiled(code_address)) {
                        if (!storage.exists(code_address)) {
                            return_size = 0;
                            credit_gas(gas, call_gas);
                            memory.burn(ret_offset, return_data, _min(ret_size, return_size));
                            stack.push(true);
                            break;
                        }
                    }
                }
            }
            uint64_t snapshot = storage.begin();
            uint64_t code_size;
            uint8_t *code = storage.get_call_code(code_address, code_size);
            bool success;
            _try({
                if (!storage.exists(code_address)) storage.create_account(code_address, false);
                storage.sub_balance(owner_address, value);
                storage.add_balance(code_address, value);
                success = _catches(vm_run)(release, block, storage,
                                origin_address, gas_price,
                                code_address, code, code_size,
                                owner_address, value, args_data, args_size,
                                return_data, return_size, return_capacity, call_gas,
                                read_only, depth+1);
                credit_gas(gas, call_gas);
                memory.burn(ret_offset, return_data, _min(ret_size, return_size));
            }, Error e, {
                success = false;
                return_size = 0;
            })
            storage.release_code(code);
            storage.end(snapshot, success);
            stack.push(success);
            break;
        }
        case CALLCODE: {
            uint256_t v0 = stack.pop();
            uint160_t code_address = (uint160_t)stack.pop();
            uint256_t value = stack.pop();
            uint256_t v1 = stack.pop(), v2 = stack.pop(), v3 = stack.pop(), v4 = stack.pop();
            _handles0(memory_check)(v1, v2);
            _handles0(memory_check)(v3, v4);
            uint64_t args_offset = v1.cast64(), args_size = v2.cast64(), ret_offset = v3.cast64(), ret_size = v4.cast64();
            _handles0(consume_gas)(gas, gas_memory(release, memory.size(), _max(args_offset + args_size, ret_offset + ret_size)));
            _handles0(consume_gas)(gas, gas_call(release, value > 0, false, true));
            uint64_t reserved_gas = v0 > gas ? gas : v0.cast64();
            uint64_t call_gas = gas_cap(release, gas, reserved_gas);
            _handles0(consume_gas)(gas, call_gas);
            credit_gas(call_gas, gas_stipend_call(release, value > 0));
            local<uint8_t> args_data_l(args_size); uint8_t *args_data = args_data_l.data;
            memory.dump(args_offset, args_size, args_data);
            memory.mark(ret_offset + ret_size);
            if (depth >= CALL_DEPTH || storage.get_balance(owner_address) < value) {
                return_size = 0;
                credit_gas(gas, call_gas);
                stack.push(false);
                break;
            }
            uint64_t snapshot = storage.begin();
            uint64_t code_size;
            uint8_t *code = storage.get_call_code(code_address, code_size);
            bool success;
            _try({
                success = _catches(vm_run)(release, block, storage,
                                origin_address, gas_price,
                                owner_address, code, code_size,
                                owner_address, value, args_data, args_size,
                                return_data, return_size, return_capacity, call_gas,
                                read_only, depth+1);
                credit_gas(gas, call_gas);
                memory.burn(ret_offset, return_data, _min(ret_size, return_size));
            }, Error e, {
                success = false;
                return_size = 0;
            })
            storage.release_code(code);
            storage.end(snapshot, success);
            stack.push(success);
            break;
        }
        case RETURN: {
            uint256_t v1 = stack.pop(), v2 = stack.pop();
            _handles0(memory_check)(v1, v2);
            uint64_t offset = v1.cast64(), size = v2.cast64();
            _handles0(consume_gas)(gas, gas_memory(release, memory.size(), offset + size));
            return_size = size;
            _ensure_capacity(return_data, return_size, return_capacity);
            memory.dump(offset, return_size, return_data);
            return true;
        }
        case DELEGATECALL: {
            uint256_t v0 = stack.pop();
            uint160_t code_address = (uint160_t)stack.pop();
            uint256_t v1 = stack.pop(), v2 = stack.pop(), v3 = stack.pop(), v4 = stack.pop();
            _handles0(memory_check)(v1, v2);
            _handles0(memory_check)(v3, v4);
            uint64_t args_offset = v1.cast64(), args_size = v2.cast64(), ret_offset = v3.cast64(), ret_size = v4.cast64();
            _handles0(consume_gas)(gas, gas_memory(release, memory.size(), _max(args_offset + args_size, ret_offset + ret_size)));
            _handles0(consume_gas)(gas, gas_call(release, false, false, true));
            uint64_t reserved_gas = v0 > gas ? gas : v0.cast64();
            uint64_t call_gas = gas_cap(release, gas, reserved_gas);
            _handles0(consume_gas)(gas, call_gas);
            local<uint8_t> args_data_l(args_size); uint8_t *args_data = args_data_l.data;
            memory.dump(args_offset, args_size, args_data);
            memory.mark(ret_offset + ret_size);
            if (depth >= CALL_DEPTH) {
                return_size = 0;
                credit_gas(gas, call_gas);
                stack.push(false);
                break;
            }
            uint64_t snapshot = storage.begin();
            uint64_t code_size;
            uint8_t *code = storage.get_call_code(code_address, code_size);
            bool success;
            _try({
                success = _catches(vm_run)(release, block, storage,
                                origin_address, gas_price,
                                owner_address, code, code_size,
                                caller_address, call_value, args_data, args_size,
                                return_data, return_size, return_capacity, call_gas,
                                read_only, depth+1);
                credit_gas(gas, call_gas);
                memory.burn(ret_offset, return_data, _min(ret_size, return_size));
            }, Error e, {
                success = false;
                return_size = 0;
            })
            storage.release_code(code);
            storage.end(snapshot, success);
            stack.push(success);
            break;
        }
        case CREATE2: {
            uint256_t value = stack.pop(), v1 = stack.pop(), v2 = stack.pop(), salt = stack.pop();
            _handles0(memory_check)(v1, v2);
            uint64_t init_offset = v1.cast64(), init_size = v2.cast64();
            _handles0(consume_gas)(gas, gas_memory(release, memory.size(), init_offset + init_size));
            _handles0(consume_gas)(gas, gas_sha3(release, init_size));
            uint64_t create_gas = gas_cap(release, gas, gas);
            _handles0(consume_gas)(gas, create_gas);
            local<uint8_t> init_l(init_size); uint8_t *init = init_l.data;
            memory.dump(init_offset, init_size, init);
            if (depth >= CALL_DEPTH || storage.get_balance(owner_address) < value) {
                return_size = 0;
                credit_gas(gas, create_gas);
                stack.push(false);
                break;
            }
            uint160_t code_address = gen_contract_address(owner_address, salt, sha3(init, init_size));
            storage.increment_nonce(owner_address);
            uint64_t snapshot = storage.begin();
            bool success;
            _try({
                if (storage.has_contract(code_address)) _trythrow(CODE_CONFLICT);
                storage.create_account(code_address, true);
                if (release >= SPURIOUS_DRAGON) storage.set_nonce(code_address, 1);
                storage.sub_balance(owner_address, value);
                storage.add_balance(code_address, value);
                success = _catches(vm_run)(release, block, storage,
                                origin_address, gas_price,
                                code_address, init, init_size,
                                owner_address, value, nullptr, 0,
                                return_data, return_size, return_capacity, create_gas,
                                read_only, depth+1);
                if (success) {
                    _catches(code_size_check)(release, return_size);
                    _try({
                        _catches(consume_gas)(create_gas, gas_create(release, return_size));
                        storage.register_code(code_address, return_data, return_size);
                    }, Error e ,{
                        if (release >= HOMESTEAD) _trythrow(e);
                    })
                    return_size = 0;
                }
                credit_gas(gas, create_gas);
            }, Error e, {
                success = false;
                return_size = 0;
            })
            storage.end(snapshot, success);
            stack.push(success ? (uint256_t)code_address : 0);
            break;
        }
        case STATICCALL: {
            uint256_t v0 = stack.pop();
            uint160_t code_address = (uint160_t)stack.pop();
            uint256_t v1 = stack.pop(), v2 = stack.pop(), v3 = stack.pop(), v4 = stack.pop();
            _handles0(memory_check)(v1, v2);
            _handles0(memory_check)(v3, v4);
            uint64_t args_offset = v1.cast64(), args_size = v2.cast64(), ret_offset = v3.cast64(), ret_size = v4.cast64();
            _handles0(consume_gas)(gas, gas_memory(release, memory.size(), _max(args_offset + args_size, ret_offset + ret_size)));
            _handles0(consume_gas)(gas, gas_call(release, false, false, true));
            uint64_t reserved_gas = v0 > gas ? gas : v0.cast64();
            uint64_t call_gas = gas_cap(release, gas, reserved_gas);
            _handles0(consume_gas)(gas, call_gas);
            local<uint8_t> args_data_l(args_size); uint8_t *args_data = args_data_l.data;
            memory.dump(args_offset, args_size, args_data);
            memory.mark(ret_offset + ret_size);
            if (depth >= CALL_DEPTH) {
                return_size = 0;
                credit_gas(gas, call_gas);
                stack.push(false);
                break;
            }
            uint64_t snapshot = storage.begin();
            uint64_t code_size;
            uint8_t *code = storage.get_call_code(code_address, code_size);
            bool success;
            _try({
                success = _catches(vm_run)(release, block, storage,
                                origin_address, gas_price,
                                code_address, code, code_size,
                                owner_address, 0, args_data, args_size,
                                return_data, return_size, return_capacity, call_gas,
                                true, depth+1);
                credit_gas(gas, call_gas);
                memory.burn(ret_offset, return_data, _min(ret_size, return_size));
            }, Error e, {
                success = false;
                return_size = 0;
            })
            storage.release_code(code);
            storage.end(snapshot, success);
            stack.push(success);
            break;
        }
        case REVERT: {
            uint256_t v1 = stack.pop(), v2 = stack.pop();
            _handles0(memory_check)(v1, v2);
            uint64_t offset = v1.cast64(), size = v2.cast64();
            _handles0(consume_gas)(gas, gas_memory(release, memory.size(), offset + size));
            return_size = size;
            _ensure_capacity(return_data, return_size, return_capacity);
            memory.dump(offset, return_size, return_data);
            return false;
        }
        case SELFDESTRUCT: {
            uint160_t to = (uint160_t)stack.pop();
            uint256_t amount = storage.get_balance(owner_address);
            _handles0(consume_gas)(gas, gas_selfdestruct(release, amount > 0, storage.is_empty(to), storage.exists(to)));
            if (!storage.is_destructed(owner_address)) storage.add_refund(gas_refund_selfdestruct(release));
            storage.add_balance(to, amount);
            storage.set_balance(owner_address, 0);
            storage.destruct_account(owner_address);
            return_size = 0;
            return true;
        }
        default: assert(false);
        }
    }
}

// executes a transaction
// it takes a block abstraction, the persistent state and the transaction data
// a new storage is create and the release is inferred from the forkblock method
// two additional parameters are provided: an alternate sender in case the transaction
// has r = 0 and v = 0, and a flag indicating wheter or not the gas will be deducted from
// the sender's balance
// this routine is a customized version of opcodes CALL and CREATE with additional
// handling of the transaction and state
static void _throws(vm_txn)(Block &block, State &state, const uint8_t *buffer, uint64_t size, uint160_t sender, bool pays_gas)
{
    Release release = get_release(block.forknumber());
    Storage storage(&state);

    struct txn txn = {0, 0, 0, false, 0, 0, nullptr, 0, false, 0, 0, 0};
    _handles(decode_txn)(buffer, size, txn);
    _handles(verify_txn)(release, txn);

    uint160_t from = sender;
    if (sender == 0) {
        uint256_t h = _handles(hash_txn)(txn);
        from = _handles(ecrecover)(h, txn.v, txn.r, txn.s);
    }
    if (txn.nonce != storage.get_nonce(from)) _throw(NONCE_MISMATCH);
    uint160_t to = txn.has_to ? txn.to : _handles(gen_contract_address)(from, storage.get_nonce(from));
    storage.increment_nonce(from);

    if (txn.gaslimit > block.gaslimit()) _throw(OUTOFBOUNDS_VALUE);
    uint64_t gas = txn.gaslimit.cast64();
    _handles(consume_gas)(gas, gas_intrinsic(release, txn.has_to, txn.data, txn.data_size));
    uint256_t gas_cost = txn.gaslimit * txn.gasprice;
    if (pays_gas) {
        if (storage.get_balance(from) < gas_cost) _throw(INSUFFICIENT_BALANCE);
        storage.sub_balance(from, gas_cost);
    }
    if (storage.get_balance(from) < txn.value) _throw(INSUFFICIENT_BALANCE);

    uint64_t return_size = 0;
    uint64_t return_capacity = 0;
    uint8_t *return_data = nullptr;

    bool success;
    uint64_t snapshot = storage.begin();
    if (txn.has_to) { // message call
        uint64_t code_size;
        uint8_t *code = storage.get_call_code(to, code_size);
        _try({
            if (!storage.exists(to)) storage.create_account(to, false);
            storage.sub_balance(from, txn.value);
            storage.add_balance(to, txn.value);
            success = _catches(vm_run)(release, block, storage,
                            from, txn.gasprice,
                            to, code, code_size,
                            from, txn.value, txn.data, txn.data_size,
                            return_data, return_size, return_capacity, gas,
                            false, 1);
        }, Error e, {
            success = false;
            gas = 0;
        })
        storage.release_code(code);
    } else { // contract creation
        _try({
            if (storage.has_contract(to)) _trythrow(CODE_CONFLICT);
            storage.create_account(to, true);
            if (release >= SPURIOUS_DRAGON) storage.set_nonce(to, 1);
            storage.sub_balance(from, txn.value);
            storage.add_balance(to, txn.value);
            success = _catches(vm_run)(release, block, storage,
                            from, txn.gasprice,
                            to, txn.data, txn.data_size,
                            from, txn.value, nullptr, 0,
                            return_data, return_size, return_capacity, gas,
                            false, 1);
            if (success) {
                _catches(code_size_check)(release, return_size);
                _try({
                    _catches(consume_gas)(gas, gas_create(release, return_size));
                    storage.register_code(to, return_data, return_size);
                }, Error e ,{
                    if (release >= HOMESTEAD) _trythrow(e);
                })
            }
        }, Error e, {
            success = false;
            gas = 0;
        })
    }
    storage.end(snapshot, success);

    _delete(return_data);

    uint64_t refund_gas = storage.get_refund();
    uint64_t used_gas_before_refund = txn.gaslimit.cast64() - gas;
    credit_gas(gas, _min(refund_gas, used_gas_before_refund / 2));
    uint64_t used_gas = txn.gaslimit.cast64() - gas;
    if (pays_gas) {
        storage.add_balance(from, gas * txn.gasprice);
        storage.add_balance(block.coinbase(), used_gas * txn.gasprice);
    }

    storage.flush();
}

#endif // EVM_HPP
