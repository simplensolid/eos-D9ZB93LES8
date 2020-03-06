#include <eosio/chain/evm/ecl.hpp>

#include "./evm.hpp"

namespace evm
{
    void evm_keccak256(const char* data, uint32_t datalen, char* hash_val) {
        uint256_t h = sha3((const uint8_t*)data, datalen);
        uint256_t::to(h, (uint8_t*)hash_val);
    }

    void evm_ecrecover(const char* digest, const char* sig, uint32_t siglen, char* pub, uint32_t publen) {
        uint256_t h = uint256_t::from((const uint8_t*)digest);
        uint256_t v = sig[0];
        uint256_t r = uint256_t::from((const uint8_t*)&sig[1]);
        uint256_t s = uint256_t::from((const uint8_t*)&sig[33]);
        G0 p = ecrecover(h, v, r, s);
        bigint x = p.x;
        bigint y = p.y;
        if (p.is_inf()) { x = 0; y = 0; }
        pub[0] = 4;
        bigint::to(x, (uint8_t*)&pub[1], 32);
        bigint::to(y, (uint8_t*)&pub[33], 32);
    }

    void evm_bigmodexp(const char* base, uint32_t baselen, const char* exp, uint32_t explen, const char* mod, uint32_t modlen, char* output, uint32_t outlen) {
        bigint _base = bigint::from((const uint8_t*)base, baselen);
        bigint _exp = bigint::from((const uint8_t*)exp, explen);
        bigint _mod = bigint::from((const uint8_t*)mod, modlen);
        bigint _out = bigmodexp(_base, _exp, _mod);
        bigint::to(_out, (uint8_t*)output, 32);
    }

    void evm_bn256add(const char* point1, const char* point2, char* point3) {
        bigint x1 = bigint::from((const uint8_t*)&point1[0], 32);
        bigint y1 = bigint::from((const uint8_t*)&point1[32], 32);
        bigint x2 = bigint::from((const uint8_t*)&point2[0], 32);
        bigint y2 = bigint::from((const uint8_t*)&point2[32], 32);
        G1 p1(x1, y1);
        G1 p2(x2, y2);
        G1 p3 = bn256add(p1, p2);
        bigint x3 = p3.x;
        bigint y3 = p3.y;
        if (p3.is_inf()) { x3 = 0; y3 = 0; }
        bigint::to(x3, (uint8_t*)&point3[0], 32);
        bigint::to(y3, (uint8_t*)&point3[32], 32);
    }

    void evm_bn256scalarmul(const char* point1, const char* scalar, char* point2) {
        bigint x1 = bigint::from((const uint8_t*)&point1[0], 32);
        bigint y1 = bigint::from((const uint8_t*)&point1[32], 32);
        bigint e = bigint::from((const uint8_t*)scalar, 32);
        G1 p1(x1, y1);
        G1 p2 = bn256scalarmul(p1, e);
        bigint x2 = p2.x;
        bigint y2 = p2.y;
        if (p2.is_inf()) { x2 = 0; y2 = 0; }
        bigint::to(x2, (uint8_t*)&point2[0], 32);
        bigint::to(y2, (uint8_t*)&point2[32], 32);
    }

    bool evm_bn256pairing(const char* point_twistx_twisty_list, uint32_t count) {
        std::vector<G1> curve_points(count);
        std::vector<G2> twist_points(count);
        uint64_t offset = 0;
        for (uint64_t i = 0; i < count; i++) {
            bigint x1 = bigint::from((const uint8_t*)&point_twistx_twisty_list[offset], 32); offset += 32;
            bigint y1 = bigint::from((const uint8_t*)&point_twistx_twisty_list[offset], 32); offset += 32;
            bigint xx2 = bigint::from((const uint8_t*)&point_twistx_twisty_list[offset], 32); offset += 32;
            bigint xy2 = bigint::from((const uint8_t*)&point_twistx_twisty_list[offset], 32); offset += 32;
            bigint yx2 = bigint::from((const uint8_t*)&point_twistx_twisty_list[offset], 32); offset += 32;
            bigint yy2 = bigint::from((const uint8_t*)&point_twistx_twisty_list[offset], 32); offset += 32;
            curve_points[i] = G1(x1, y1);
            twist_points[i] = G2(Gen2(xx2, xy2), Gen2(yx2, yy2));
        }
        return bn256pairing(curve_points, twist_points, count);
    }

    void evm_blake2f(const char* data, char* state, const char* offset, bool last, uint32_t rounds) {
        uint64_t t0 = b2w64le((uint8_t*)&offset[0]);
        uint64_t t1 = b2w64le((uint8_t*)&offset[8]);
        uint64_t h0 = b2w64le((uint8_t*)&state[0]);
        uint64_t h1 = b2w64le((uint8_t*)&state[8]);
        uint64_t h2 = b2w64le((uint8_t*)&state[16]);
        uint64_t h3 = b2w64le((uint8_t*)&state[24]);
        uint64_t h4 = b2w64le((uint8_t*)&state[32]);
        uint64_t h5 = b2w64le((uint8_t*)&state[40]);
        uint64_t h6 = b2w64le((uint8_t*)&state[48]);
        uint64_t h7 = b2w64le((uint8_t*)&state[56]);
        blake2f(rounds, h0, h1, h2, h3, h4, h5, h6, h7, (uint64_t*)data, t0, t1, last);
        w2b64le(h0, (uint8_t*)&state[0]);
        w2b64le(h1, (uint8_t*)&state[8]);
        w2b64le(h2, (uint8_t*)&state[16]);
        w2b64le(h3, (uint8_t*)&state[24]);
        w2b64le(h4, (uint8_t*)&state[32]);
        w2b64le(h5, (uint8_t*)&state[40]);
        w2b64le(h6, (uint8_t*)&state[48]);
        w2b64le(h7, (uint8_t*)&state[56]);
    }
}
