/*
-------------------------------------------
       Higher order masking functions
-------------------------------------------
*/

#include <string.h>

#define NROUNDS 24

#define SHAKE128_RATE 168
#define SHAKE256_RATE 136
#define SHA3_256_RATE 136
#define SHA3_384_RATE 104
#define SHA3_512_RATE  72

#define ROL(a, offset) ((a << offset) ^ (a >> (64-offset)))

static void __attribute__ ((noinline)) memxor(void *dest, const void *src, size_t len)
{
    char *d = dest;
    const char *s = src;
    while (len--) {
        *d++ ^= *s++;
    }
}

const int keccakf_piln[24] = {
    10, 7,  11, 17, 18, 3, 5,  16, 8,  21, 24, 4,
    15, 23, 19, 13, 12, 2, 20, 14, 22, 9,  6,  1
};

const int keccakf_rotc[24] = {
    1,  3,  6,  10, 15, 21, 28, 36, 45, 55, 2,  14,
    27, 41, 56, 8,  25, 43, 62, 18, 39, 61, 20, 44
};

// Theta, Rho , Pi functions
static void __attribute__ ((noinline)) sha3_theta_rho_pi(uint64_t st[25], uint64_t bc[5])
{

    int i, j;
    uint64_t t;

    for (i = 0; i < 5; i++) {
        bc[i] = st[i] ^ st[i + 5] ^ st[i + 10] ^ st[i + 15] ^ st[i + 20];
    }

    for (i = 0; i < 5; i++) {
        t = bc[(i + 4) % 5] ^ ROL(bc[(i + 1) % 5], 1);
        for (j = 0; j < 25; j += 5) {
            st[j + i] ^= t;
        }
    }

    t = st[1];
    for (i = 0; i < 24; i++) {
        j = keccakf_piln[i];
        bc[0] = st[j];
        st[j] = ROL(t, keccakf_rotc[i]);
        t = bc[0];
    }
}

static void  __attribute__ ((noinline)) sha3_chi_masked(uint64_t st[D+1][25],uint64_t bc[D+1][5])
{
    int i, j, k, l;
    int64_t rand_no=((D+1)*D)/2;
    uint64_t random[rand_no];
    
    for (i = 0; i < rand_no; i++)
    	random[i] = next();
    	
    for (j = 0; j < 25; j += 5) {
        for (i = 0; i < 5; i++)
        {
            for (k = 0; k < D+1; k++)
            {
                bc[k][i] = st[k][j + i];
            }
        }
        for (i = 0; i < 5; i++)
        {
             for (l = 0; l < D+1; l++)
             {
                st[l][j + i] ^= ((~bc[l][(i + 1) % 5]) & bc[l][(i + 2) % 5]);
                for (k = 0; k < D+1; k++)
                {   
                    if(k<l) 
                        st[l][j+i] ^= (bc[l][(i + 1) % 5] & bc[k][(i + 2) % 5])^random[k+((l*(l-1))/2)];
                    else if(k>l)
                        st[l][j+i] ^= (bc[l][(i + 1) % 5] & bc[k][(i + 2) % 5])^random[l+((k*(k-1))/2)];
                }
	     }
      
        }
    }
}

static void __attribute__ ((noinline)) KeccakF1600_StatePermute_masked(uint64_t st[D+1][25])
{

    // variables
    int r,i;
    uint64_t bc[D+1][5];

    // constants
    const uint64_t keccakf_rndc[24] = {
        0x0000000000000001, 0x0000000000008082, 0x800000000000808a,
        0x8000000080008000, 0x000000000000808b, 0x0000000080000001,
        0x8000000080008081, 0x8000000000008009, 0x000000000000008a,
        0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
        0x000000008000808b, 0x800000000000008b, 0x8000000000008089,
        0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
        0x000000000000800a, 0x800000008000000a, 0x8000000080008081,
        0x8000000000008080, 0x0000000080000001, 0x8000000080008008
    };

    // actual iteration
    for (r = 0; r < NROUNDS; r++) {

        // Theta Rho Pi
        for (i = 0; i < D+1; i++){
            sha3_theta_rho_pi(st[i], bc[i]);
        }
        //  Chi
        sha3_chi_masked(st, bc);

        //  Iota
        st[0][0] ^= keccakf_rndc[r];
    }
}

static void __attribute__ ((noinline)) keccak_absorb_masked(uint64_t s[D+1][25], uint32_t r, size_t mlen, const uint8_t m[D+1][mlen], uint8_t p)
{
    size_t i, l = 0;

    while (mlen >= r) {
        for (i = 0; i < D+1; i++){
            memxor(s[i], &m[i][l], r);
        }    
        KeccakF1600_StatePermute_masked(s);
        mlen -= r;
        l += r;
    }
    for (i = 0; i < D+1; i++){
        memxor(s[i], &m[i][l], mlen);
    }
    // padding
    ((uint8_t *) s[0])[mlen] ^= p;
    ((uint8_t *) s[0])[r - 1] ^= 128;
}

static void __attribute__ ((noinline)) keccak_squeezeblocks_masked(uint32_t r, size_t nblocks, size_t tlen, uint8_t t[D+1][tlen], uint64_t s[D+1][25])
{

    size_t i,l = 0;

    while (nblocks > 0) {

        KeccakF1600_StatePermute_masked(s);
        for (i = 0; i < D+1; i++){
            memcpy(&t[i][l], s[i], r);
        }

        l += r;
        nblocks--;

    }
}

void shake128_masked_HO(size_t outlen, uint8_t output[D+1][outlen], size_t inlen, const uint8_t input[D+1][inlen])
{
    size_t i, l;
    uint64_t s[D+1][25] = {0};
    unsigned char t[D+1][SHAKE128_RATE];
    unsigned long long nblocks = outlen / SHAKE128_RATE;

    /* Absorb input */
    keccak_absorb_masked(s, SHAKE128_RATE, inlen, input, 0x1F);

    /* Squeeze output */
    keccak_squeezeblocks_masked(SHAKE128_RATE, nblocks, outlen, output, s);

    l = nblocks * SHAKE128_RATE;
    outlen -= nblocks * SHAKE128_RATE;

    if (outlen) {
        keccak_squeezeblocks_masked(SHAKE128_RATE, 1, SHAKE128_RATE, t, s);

        for (i = 0; i < D+1; i++) {
            memcpy(&output[i][l], t[i], outlen);
        }
    }
}

void shake256_masked_HO(size_t outlen, uint8_t output[D+1][outlen], size_t inlen, const uint8_t input[D+1][inlen])
{
    size_t i, l;
    uint64_t s[D+1][25] = {0};
    unsigned char t[D+1][SHAKE256_RATE];
    unsigned long long nblocks = outlen / SHAKE256_RATE;

    /* Absorb input */
    keccak_absorb_masked(s, SHAKE256_RATE, inlen, input, 0x1F);

    /* Squeeze output */
    keccak_squeezeblocks_masked(SHAKE256_RATE, nblocks, outlen, output, s);

    l = nblocks * SHAKE256_RATE;
    outlen -= nblocks * SHAKE256_RATE;

    if (outlen) {
        keccak_squeezeblocks_masked(SHAKE256_RATE, 1, SHAKE256_RATE, t, s);

        for (i = 0; i < D+1; i++) {
            memcpy(&output[i][l], t[i], outlen);
        }
    }
}


void sha3_384_masked_HO(uint8_t output[D+1][48], size_t inlen, const uint8_t input[D+1][inlen])
{
    size_t i;
    uint64_t s[D+1][25] = {0};
    uint8_t t[D+1][SHA3_384_RATE];

    /* Absorb input */
    keccak_absorb_masked(s, SHA3_384_RATE, inlen, input, 0x06);

    /* Squeeze output */
    keccak_squeezeblocks_masked(SHA3_384_RATE, 1, SHA3_384_RATE, t, s);

    for (i = 0; i < D+1; i++) {
        memcpy(output[i], t[i], 48);
    }
}

