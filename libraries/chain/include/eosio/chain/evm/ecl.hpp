#include <stdint.h>

namespace evm
{
    void evm_keccak256(const char* data, uint32_t datalen, char* hash_val);
    void evm_ecrecover(const char* digest, const char* sig, uint32_t siglen, char* pub, uint32_t publen);
    void evm_bigmodexp(const char* base, uint32_t baselen, const char* exp, uint32_t explen, const char* mod, uint32_t modlen, char* output, uint32_t outlen);
    void evm_bn256add(const char* point1, const char* point2, char* point3);
    void evm_bn256scalarmul(const char* point1, const char* scalar, char* point2);
    bool evm_bn256pairing(const char* point_twistx_twisty_list, uint32_t count);
    void evm_blake2f(const char* data, char* state, const char* offset, bool last, uint32_t rounds);
}
