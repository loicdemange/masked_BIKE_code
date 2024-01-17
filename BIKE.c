#include <stdio.h> 
#include <string.h>
#include <inttypes.h>
#include "xoshiro256starstar.h"


#define LEVEL 1
#define D 1
#include "hash.c"

#if LEVEL == 1
	#define R 12323
	#define BITS 13
	#define N 2*R
	#define W 142
	#define T 134
	#define T1 58487
	#define T1_LOG 15
	#define T2 113497866
	#define T3 23
	#define T4 36
	#define R_64_TAB 193
	#define DIFF 4130
	#define RPUI 16384 
	#define RPUI_TAB 256
	#define RPUI2_TAB 512
	#define LOG2W 6
	
uint64_t permut_2[BITS] = {2,4,16,256,3921,7460,932,6014,191,11835,4007,11503,6958}; 
uint64_t r_mod[BITS] = {2, 2, 2, 2, 2, 2597, 2597, 2597, 2597, 2597, 2597, 2597, 4408};

#elif LEVEL == 3
	#define R 24659
	#define BITS 14
	#define N 2*R
	#define W 206
	#define T 199
	#define SEUIL(x) (MAX((32768023488 + (uint64_t)11306501 * (x)) >> 31, 52))
	#define T1 11306501
	#define T1_LOG 23
	#define T2 32768023488
	#define T3 31
	#define T4 52
	#define R_64_TAB 386
	#define RPUI 32768
	#define RPUI_TAB 512
	#define RPUI2_TAB 1024
	#define LOG2W 7
	
uint64_t permut_2[BITS] = {2,4,16,256,16218,10630,9362,8958,5378,22536,19191,12316,6347, 16262}; 
uint64_t r_mod[BITS] = {2, 2, 2, 2, 7777, 7777, 14906, 14906, 14906, 14906, 14906, 14906, 14906, 3402};
	
#elif LEVEL == 5
	#define R 40973
	#define BITS 15
	#define N 2*R
	#define W 274
	#define T 264
	#define SEUIL(x) (MAX((1199805825 + (uint64_t)269987 * (x)) >> 26, 69))
	#define T1 269987
	#define T1_LOG 18
	#define T2 1199805825
	#define T3 26
	#define T4 69
	#define R_64_TAB 641
	#define RPUI 65536
	#define RPUI_TAB 1024
	#define RPUI2_TAB 2048
	#define LOG2W 7
	
uint64_t permut_2[BITS] = {2,4,16,256,24563,13544,3815,8810,13238,3123,1555,618,13167,13126,411}; 
uint64_t r_mod[BITS] = {2, 8, 8, 2048, 2048, 2048, 2048, 2048, 2048, 2048, 2048, 2048, 2048, 3760, 3760};
#endif


uint64_t ticks(){
    unsigned int lo,hi;
    __asm__ __volatile__ ("rdtsc" : "=a" (lo), "=d" (hi));
    return ((uint64_t)hi << 32) | lo;
}

void H(uint64_t inlen, uint64_t outlen, uint64_t value[(inlen/8)+1][D+1], uint32_t res[(outlen/4)][D+1])
{
	uint8_t v[D+1][inlen], ret[D+1][outlen];
	for(int i = 0; i < inlen; ++i)
	{
		for(int d = 0; d<=D; ++d)
			v[d][i] = (value[i/8][d] >> i) & (uint8_t)(-1);
	}
	
	memset(ret, 0, outlen*(D+1));
	shake256_masked_HO(outlen, ret, inlen, v);
	
	memset(res, 0, outlen*(D+1));
	for(int i = 0; i < outlen; ++i)
	{
		for(int d = 0; d <= D; ++d)
			res[i/4][d] ^= ret[d][i] << (24-((i*8)&31));
	}

}

void boolean_refresh(uint64_t *x)
{
	int i, j;
	for(i = 0; i <= D; ++i)
	{
		for(j = 1; j <= D; ++j)
		{
			uint64_t r = next();
			x[0] ^= r;
			x[j] ^= r;
		}
	}	
}

uint64_t boolean_resolve(uint64_t x[D+1])
{
	uint64_t z = x[0];
	for(int d = 1; d <= D; ++d)
		z ^= x[d];
	return z;
}

void boolean_sec_and(uint64_t *x, uint64_t *y, uint64_t *z)
{
	for(int i = 0; i <= D; ++i)
		z[i] = x[i] & y[i];
	
	for(int i = 0; i <= D; ++i)
	{
		for(int j = i+1; j <= D; ++j)
		{
			uint64_t r = next();
			z[i] ^= r;
			r ^= x[i] & y[j];
			r ^= x[j] & y[i];
			z[j] ^= r;
		}
	}	
}

void boolean_sec_plus(uint64_t *x, uint64_t *y, uint64_t *z)
{
	uint64_t p[D+1];
	for(int i = 0; i <= D; ++i)
		p[i] = x[i] ^ y[i];
	
	uint64_t g[D+1];
	boolean_sec_and(x, y, g);
	
	uint64_t a[D+1];
	
	uint8_t w = 5;
	
	for(int j = 0; j < w; ++j)
	{
		uint8_t pow = 1 << j;
		uint64_t a1[D+1];
		for(int i = 0; i <= D; ++i)
		{
			a[i] = g[i] << pow;
			a1[i] = p[i] << pow;
		}
			
		uint64_t t[D+1];
		boolean_sec_and(a, p, t);
		for(int i = 0; i <= D; ++i)
		{
			a[i] = t[i];
			g[i] ^= a[i];
		}
		
		boolean_refresh(a1);
		boolean_sec_and(p, a1, t);
		for(int i = 0; i <= D; ++i)
			p[i] = t[i];
		
	}
	for(int i = 0; i <= D; ++i)
		a[i] = g[i] << (1 << w);
	
	uint64_t t[D+1];
	boolean_sec_and(a, p, t);
	for(int i = 0; i <= D; ++i)
	{
		g[i] ^= t[i];
		z[i] = x[i] ^ y[i] ^ (g[i] << 1);
	}
}

void boolean_demi_mult(uint64_t x[D+1], uint64_t y, uint64_t z[D+1], uint8_t bits)
{
	uint64_t t[D+1];
	memcpy(t, x, 8*(D+1));
	memset(z, 0, 8*(D+1));
	
	for(int i = 0; i < bits + 1; ++i)
	{
		if((y >> i) & 1)
		{
			uint64_t t1[D+1];
			boolean_sec_plus(z, t, t1);
			memcpy(z, t1, 8*(D+1));
		}
		for(int d = 0; d<=D; ++d)
			t[d] <<= 1;
	}

}

void sec_if_vector(uint64_t a[][D+1], uint64_t b[][D+1], uint64_t c[D+1], uint64_t res[][D+1], uint64_t size)
{
	uint64_t t[D+1], t1[D+1];
	for(int d = 0; d<=D; ++d)
		t[d] = (c[d] & 1) * (uint64_t)(-1);
	
	for(int i = 0; i < size; ++i)
	{
		boolean_sec_and(a[i], t, res[i]);
		t[0] ^= (uint64_t)(-1);
		boolean_sec_and(b[i], t, t1);
		t[0] ^= (uint64_t)(-1);
		boolean_refresh(t);
		
		for(int d = 0; d<=D; ++d)
			res[i][d] ^= t1[d];
	}
}

void sec_if(uint64_t a[D+1], uint64_t b[D+1], uint64_t c[D+1], uint64_t res[D+1])
{
	uint64_t t[D+1], t1[D+1];
	for(int d = 0; d<=D; ++d)
		t[d] = (c[d] & 1) * (uint64_t)(-1);
		
		
	boolean_sec_and(a, t, res);
	t[0] ^= (uint64_t)(-1);
	boolean_sec_and(b, t, t1);
	
	for(int d = 0; d<=D; ++d)
		res[d] ^= t1[d];
}

void boolean_demi_sec_plus(uint64_t x[D+1], uint64_t y, uint64_t z[D+1])
{
	uint64_t p[D+1];
	memcpy(p, x, 8*(D+1));
	p[0] ^= y;
	
	uint64_t g[D+1];
	for(int d = 0; d <= D; ++d)
		g[d] = x[d] & y;
	
	uint64_t a[D+1];
	
	uint8_t w = 5;
	
	for(int j = 0; j < w; ++j)
	{
		uint8_t pow = 1 << j;
		uint64_t a1[D+1];
		for(int i = 0; i <= D; ++i)
		{
			a[i] = g[i] << pow;
			a1[i] = p[i] << pow;
		}
			
		uint64_t t[D+1];
		boolean_sec_and(a, p, t);
		for(int i = 0; i <= D; ++i)
		{
			a[i] = t[i];
			g[i] ^= a[i];
		}
		
		boolean_refresh(a1);
		boolean_sec_and(p, a1, t);
		for(int i = 0; i <= D; ++i)
			p[i] = t[i];
		
	}
	for(int i = 0; i <= D; ++i)
		a[i] = g[i] << (1 << w);
	
	uint64_t t[D+1];
	boolean_sec_and(a, p, t);
	
	g[0] ^= t[0];
	z[0] = x[0] ^ y ^ (g[0] << 1);
	
	for(int i = 1; i <= D; ++i)
	{
		g[i] ^= t[i];
		z[i] = x[i] ^ (g[i] << 1);
	}
}

void cyclic_shift(uint64_t p1[][D+1], uint64_t out[][D+1], uint16_t shift, uint16_t size_64)
{
	
	for(int i = 0; i < size_64; ++i)
	{
		for(int d = 0; d <= D; ++d)
			out[i][d] = p1[i][d];
	}
	
	uint16_t diff = ((R_64_TAB) * (64)) - R;
	if(diff == 0) diff = 64;
	
	int size = 1 << (31 - __builtin_clz(shift));
	size/= 64;
	
	if(size >= 1)
	{
		uint64_t t[size_64][D+1];
		memcpy(&(t[size]), out, (size_64-size)*8*(D+1));
		
		for(int d = 0; d <= D; ++d)
		{
			for(int i = 0; i < size; ++i)
			{
				t[i][d] = (out[size_64 - size + i][d] >> diff);
				t[i][d] ^= ((out[size_64 - size + i - 1][d] & (((uint64_t)1 << diff) - 1))) << (64-diff);
			}
			t[size_64 - 1][d] &= ~(((uint64_t)1 << diff) - 1);
			
		}
			
		memcpy(out, t, (size_64)*8*(D+1));
		shift -= size*64;
	}
	
	if(shift == 0) return;
	
	uint16_t nbr_shift = shift/diff;
	shift = shift - nbr_shift*diff;
	for(int i = 0; i < nbr_shift; ++i)
	{
		uint8_t index = 0;
		uint64_t t[2][D+1] = {0};

		for(int j = 0; j < size_64 - 1; ++j)
		{
			for(int d = 0; d <= D; ++d)
			{
				t[index][d] = (out[j][d] & (((uint64_t)1 << (diff)) - 1));
				out[j][d] >>= diff;
				out[j][d] ^= (t[1-index][d] << (64 - diff));
			}
			
			index ^= 1;
		}
			
		for(int d = 0; d <= D; ++d)
		{
			out[size_64 - 1][d] >>= diff;
			out[size_64 - 1][d] ^= t[1-index][d] << (64 - diff);
			t[index][d] = out[size_64 - 1][d] & (((uint64_t)1 << diff) - 1);
			out[size_64 - 1][d] &= ~(((uint64_t)1 << diff) - 1);
			out[0][d] ^= (t[index][d] << (64-diff));
		}
		
		
	}
	
	if(shift == 0) return;
	
	uint8_t index = 0;
	uint64_t t[2][D+1] = {0};

	for(int j = 0; j < size_64 - 1; ++j)
	{
		for(int d = 0; d <= D; ++d)
		{
			t[index][d] = (out[j][d] & (((uint64_t)1 << (shift)) - 1));
			out[j][d] >>= shift;
			out[j][d] ^= (t[1-index][d] << (64 - shift));
		}
		
		index ^= 1;
	}
		
	for(int d = 0; d <= D; ++d)
	{
		out[size_64 - 1][d] >>= shift;
		out[size_64 - 1][d] ^= t[1-index][d] << (64 - shift);
		t[index][d] = out[size_64 - 1][d] & (((uint64_t)1 << diff) - 1);
		out[size_64 - 1][d] &= ~(((uint64_t)1 << diff) - 1);
		out[0][d] ^= (t[index][d] << (64-diff));	
		
	}		
	
}

void cyclic_shift_left(uint64_t p1[][D+1], uint64_t out[][D+1], uint16_t shift, uint16_t size_64)
{
	
	for(int i = 0; i < size_64; ++i)
	{
		for(int d = 0; d <= D; ++d)
			out[i][d] = p1[i][d];
	}
	
	uint16_t diff = ((R_64_TAB) * (64)) - R;
	if(diff == 0) diff = 64;
	
	int size = 1 << (31 - __builtin_clz(shift));
	size/= 64;
	
	if(size >= 1)
	{
		uint64_t t[size_64][D+1];
		memcpy(t, &out[size], (size_64-size)*8*(D+1));
		
		for(int d = 0; d <= D; ++d)
		{
			for(int i = 0; i < size; ++i)
			{
				t[size_64 - size + i - 1][d] ^= (out[i][d] >> (64-diff));
				t[size_64 - size + i][d] = out[i][d] << diff;
			}					
		}
			
		memcpy(out, t, (size_64)*8*(D+1));
		
		shift -= size*64;
	}
	
	if(shift == 0) return;
	
	uint16_t nbr_shift = shift/(64-diff);
	shift = shift - nbr_shift*(64-diff);
	for(int i = 0; i < nbr_shift; ++i)
	{
		uint8_t index = 0;
		uint64_t t[2][D+1] = {0};

		for(int j = size_64 - 1; j >= 0; --j)
		{
			for(int d = 0; d <= D; ++d)
			{
				t[index][d] = (out[j][d] & ~(((uint64_t)1 << (diff)) - 1));
				out[j][d] <<= 64-diff;
				out[j][d] ^= (t[1-index][d] >> diff);
			}
			
			index ^= 1;
		}
		
		for(int d = 0; d <=D; ++d)
			out[size_64 - 1][d] ^= t[1-index][d];
	}
	
	if(shift == 0) return;

	uint8_t index = 0;
	uint64_t t[2][D+1] = {0};

	for(int j = size_64 - 1; j >= 0; --j)
	{
		for(int d = 0; d <= D; ++d)
		{
			t[index][d] = (out[j][d] & ~(((uint64_t)1 << (64-shift)) - 1));
			out[j][d] <<= shift;
			out[j][d] ^= (t[1-index][d] >> 64-shift);
		}
		
		index ^= 1;
	}
	
	for(int d = 0; d <=D; ++d)
		out[size_64 - 1][d] ^= t[1-index][d];
}

void sec_shift(uint64_t x_dense[][D+1], uint64_t shift[D+1], uint64_t z[][D+1])
{
	
	for(int j = 0; j < R_64_TAB; ++j)
	{
		for(int d = 0; d <= D; ++d)
			z[j][d] = x_dense[j][d];
	}

	for(int j = 0; j < BITS + 1; ++j)
	{
		
		uint64_t t[R_64_TAB][D+1];
		cyclic_shift(z, t, ((uint64_t)1 << j), R_64_TAB);

		uint64_t val_bin[D+1];
		for(int d = 0; d <= D; ++d)
			val_bin[d] = ((shift[d] >> j) & 1);
		
		uint64_t t1[R_64_TAB][D+1];
		sec_if_vector(t, z, val_bin, t1, R_64_TAB);
		memcpy(z, t1, R_64_TAB*(D+1)*8);
	}
}

void sec_shift_left(uint64_t x_dense[][D+1], uint64_t shift[D+1], uint64_t z[][D+1])
{
	
	for(int j = 0; j < R_64_TAB; ++j)
	{
		for(int d = 0; d <= D; ++d)
			z[j][d] = x_dense[j][d];
	}
	for(int j = 0; j < BITS + 1; ++j)
	{
		
		uint64_t t[R_64_TAB][D+1];
		cyclic_shift_left(z, t,((uint64_t)1 << j), R_64_TAB); 

		uint64_t val_bin[D+1];
		for(int d = 0; d <= D; ++d)
			val_bin[d] = ((shift[d] >> j) & 1);	
		
		uint64_t t1[R_64_TAB][D+1];
		sec_if_vector(t, z, val_bin, t1, R_64_TAB);
		memcpy(z, t1, R_64_TAB*(D+1)*8);
	}
}

void sec_sparsedense(uint64_t x_dense[][D+1], uint64_t y_sparse[][D+1], uint64_t z[][D+1], uint16_t size_sparse)
{
	memset(z, 0, (D+1)*(R_64_TAB)*8);
	
	for(int i = 0; i < size_sparse; ++i)
	{
		uint64_t t[R_64_TAB][D+1];
		sec_shift(x_dense, y_sparse[i], t);	
		
		for(int j = 0; j < R_64_TAB; ++j)
		{
			boolean_refresh(x_dense[j]);
			for(int d = 0; d <= D; ++d)
				z[j][d] ^= t[j][d];
		}
		
	}
}
void masked_nmul_F2_64(uint64_t p1[1][D+1], uint64_t p2[1][D+1], uint64_t out[][D+1]){
   	memset(out, 0, (D+1) * 2 * 8);   
    for(int i = 0; i < 64; ++i)
    {
		uint64_t t[D+1];
		
		for(int d = 0; d <= D; ++d)	
		{
			uint64_t temp = ((p1[0][d]) >> (63 - i)) & 1;
			temp *= (uint64_t)(-1);
			t[d] = temp;
		}
		
		uint64_t u[D+1];
		boolean_sec_and(t, (uint64_t*)p2[0], u);
		
		
		if(i > 0)
		{
			for(int d = 0; d <= D; ++d)
			{
				out[0][d] ^= (u[d] >> i);
				out[1][d] ^= (u[d] & (((uint64_t)(1) << i) - 1)) << (64 - i);
			}
		}
		else
			memcpy(out, u, (D+1)*8);
			
	}	
}

void masked_karatsuba_F2(uint64_t p1[][D+1], uint64_t p2[][D+1], uint64_t out[][D+1], uint32_t index, uint32_t size){
	uint16_t size_64 = size/64;

	if (size_64 == 1){
		if(index < R_64_TAB)
			masked_nmul_F2_64(p1, p2, out);
        return;
    }

	uint64_t t1[size_64/2][D+1], t2[size_64/2][D+1], t3[size_64][D+1];	
	uint64_t z1[size_64][D+1], z2[size_64][D+1];

    masked_karatsuba_F2(p1+(size_64/2), p2+(size_64/2), z1, (size_64/2), size/2);
    masked_karatsuba_F2(p1, p2, z2, 0, size/2);
    
    for(int d = 0; d <= D; ++d)
    {
		 for(int i = 0; i < (size_64/2); ++i) {
			
			if(index+i+(size_64/2) >= R_64_TAB)
			{
				t1[i][d] = p1[i][d];
				t2[i][d] = p2[i][d];
			}
			else
			{
				
				t1[i][d] = p1[i][d] ^ p1[i+(size_64/2)][d];
				t2[i][d] = p2[i][d] ^ p2[i+(size_64/2)][d];
			}
			
				
		}	
	}
	masked_karatsuba_F2(t1, t2, t3, 0, size/2);  

    for(int d = 0; d <= D; ++d)
    {
		for (int i=0; i < size_64; ++i)
			t3[i][d] ^= z1[i][d] ^ z2[i][d];
	}
	
	if(size_64 > R_64_TAB)
		memset(out, 0, (D+1) * (2*R_64_TAB) * 8);
	else
		memset(out, 0, (D+1) * (2*size_64) * 8);
	
    for(int d = 0; d <= D; ++d)
    {
		for(int i = 0; i < size_64; ++i)
		{
			out[i][d] ^= z2[i][d];
			if(i+size_64/2 < 2*R_64_TAB)
				out[i+size_64/2][d] ^= t3[i][d];	
			if(i+size_64 < 2*R_64_TAB)
				out[i+size_64][d] ^= z1[i][d];
		}	
	}
}

void modulo(uint64_t x[R_64_TAB*2][D+1], uint64_t out[R_64_TAB][D+1])
{
	uint8_t diff = 64 - R&63;
	memcpy(out, x, R_64_TAB * (D+1) * 8);
	
	for(int d = 0; d <= D; ++d)
		out[R_64_TAB - 1][d] = out[R_64_TAB - 1][d] & ~(((uint64_t)1 << diff) - 1);
	
	for(int i = 0; i < R_64_TAB; ++i)
	{
		for(int d = 0; d <= D; ++d)
		{
			out[i][d] ^= (x[i - 1 + R_64_TAB][d] << (64 - diff));
			out[i][d] ^= (x[i + R_64_TAB][d] >> diff);
		}		
	}

		
}

void masked_karatsuba_all(uint64_t p1[R_64_TAB][D+1], uint64_t p2[R_64_TAB][D+1], uint64_t out[R_64_TAB][D+1])
{
	uint64_t p1_pui[RPUI_TAB][D+1] = {0}, p2_pui[RPUI_TAB][D+1] = {0};
	memcpy(p1_pui, p1, R_64_TAB*(D+1)*8);
	memcpy(p2_pui, p2, R_64_TAB*(D+1)*8);
	
	uint64_t out_double[R_64_TAB*2][D+1] = {0};
	
	masked_karatsuba_F2(p1, p2, out_double, 0, RPUI);
	modulo(out_double, out);
}

void sec_fill(uint64_t tab[R_64_TAB][LOG2W+1][D+1], uint64_t val[D+1])
{
	for(int i = 0; i < R_64_TAB; ++i)
	{
		for(int j = 0; j < LOG2W+1; ++j)
		{
			for(int d = 0; d<=D; ++d)
			{
				uint64_t v = (val[d] >> j) & 1;
				tab[i][j][d] = v * (uint64_t)(-1);
			}
		}
		boolean_refresh(val);
	}
}

void sec_max(uint64_t a[D+1], uint64_t b[D+1], uint64_t res[D+1])
{
	uint64_t b_neg[D+1], t[D+1];
	memcpy(b_neg, b, 8*(D+1));
	b_neg[0] ^= (uint64_t)(-1);
	boolean_demi_sec_plus(b_neg, 1, t);
	memcpy(b_neg, t, 8*(D+1));
	boolean_sec_plus(a, b_neg, t);
	
	for(int d = 0; d<=D; ++d)
		t[d] >>= 63;
	
	sec_if(b, a, t, res);
}

void compute_threshold(uint64_t x[D+1], uint64_t res[D+1])
{
	memset(res, 0, (D+1)*8);
	boolean_demi_mult(x, T1, res, T1_LOG);

	uint64_t temp[D+1];
	boolean_demi_sec_plus(res, T2, temp);
	
	for(int d = 0; d <= D; ++d)
		res[d] = temp[d] >> T3;

	uint64_t t[D+1], t4[D+1] = {0};
	t4[0] = T4;
	sec_max(res, t4, t);
	memcpy(res, t, 8*(D+1));
}


void half_adder(uint64_t a[D+1], uint64_t b[D+1], uint64_t c[D+1], uint64_t r[D+1])
{
	for(int d = 0; d<=D; ++d)
		c[d] = a[d] ^ b[d];
	
	boolean_sec_and(a, b, r);
}

void adder(uint64_t a[D+1], uint64_t b[D+1], uint64_t r1[D+1], uint64_t c[D+1], uint64_t r[D+1])
{
	uint64_t t[D+1], s[D+1], u[D+1];
	half_adder(a, b, t, s);
	half_adder(t, r1, c, u);
	for(int d = 0; d<=D; ++d)
		r[d] = s[d] ^ u[d];
		
}

void half_bitslice(int max, uint64_t x[][max][D+1], uint64_t y[][D+1], int size, int k)
{
	for(int i = 0; i < size; ++i)
	{	
		uint64_t carry[D+1];
		memcpy(carry, y[i], 8*(D+1));
		for(int j = 0; j < k; ++j)
		{
			uint64_t c[D+1], d[D+1];
			half_adder(x[i][j], carry, c, d);
			memcpy(x[i][j], c, 8*(D+1));
			memcpy(carry, d, 8*(D+1));
		}
		if(k != max)
		{
			for(int d = 0; d <= D; ++d)
				x[i][k][d] ^= carry[d];
		}
	}
}

void full_bitslice(int max, uint64_t x[][max][D+1], uint64_t y[][max][D+1], int size, int k)
{
	for(int i = 0; i < size; ++i)
	{	
		uint64_t carry[D+1] = {0};
		for(int j = 0; j < k; ++j)
		{
			uint64_t c[D+1], d[D+1];
			adder(x[i][j], y[i][j], carry, c, d);
			memcpy(x[i][j], c, 8*(D+1));
			memcpy(carry, d, 8*(D+1));
		}
		
		if(k != max)
		{
			for(int d = 0; d <= D; ++d)
				x[i][k][d] ^= carry[d];
		}
	}
}

void hamming_weight(uint64_t x[][D+1], uint64_t res[D+1])
{
	uint64_t tt[RPUI_TAB/2][BITS+1][D+1];
	memset(tt, 0, (RPUI_TAB/2) * (BITS+1)*(D+1)*8);
	for(int i = 0; i < RPUI_TAB/2; ++i)
	{
		for(int d = 0; d <= D; ++d)
			tt[i][0][d] = x[i][d];
	}
	
	half_bitslice(BITS+1, tt, x+(RPUI_TAB/2), R_64_TAB - RPUI_TAB/2, 1);	
	
	int lim = 2;
	for(int i = RPUI_TAB/4; i != 0; i/=2)
	{
		full_bitslice(BITS+1, tt, (tt+i), i, lim);
		lim++;
	}
		
	
	for(int k = 32; k != 0; k /= 2)
	{
		uint64_t tab1[1][lim][D+1];
		for(int i = 0; i < lim; ++i)
		{
			for(int d = 0; d <= D; ++d)
			{
				tab1[0][i][d] = tt[0][i][d] & (((uint64_t)1 << k) - 1);
				tt[0][i][d] = (tt[0][i][d] >> k);
			}
		}
		full_bitslice(BITS+1, tt, tab1, 1, lim);
		if(lim < BITS + 1) lim++;
	}

	memset(res, 0, 8*(D+1));
	for(int d = 0; d <= D; ++d)
	{
		for(int j = 0; j < BITS+1; ++j)
			res[d] ^= ((tt[0][j][d] & 1) << j);	
	}
	
}

void compute_syndrome(uint64_t h0[W/2][D+1], uint64_t h1[W/2][D+1], uint64_t e[2][R_64_TAB][D+1], uint64_t s_initial[R_64_TAB][D+1], uint64_t syndrome[R_64_TAB][D+1])
{
	uint64_t k0[R_64_TAB][D+1], k1[R_64_TAB][D+1];
		
	sec_sparsedense(e[0], h0, k0, W/2);
	
	for(int i = 0; i < W/2; ++i)
		boolean_refresh(h0[i]);
	
	sec_sparsedense(e[1], h1, k1, W/2);
	
	for(int i = 0; i < W/2; ++i)
		boolean_refresh(h1[i]);
	
	for(int i = 0; i < R_64_TAB; ++i)
	{
		for(int d = 0; d <= D; ++d)
			syndrome[i][d] = s_initial[i][d] ^ k0[i][d] ^ k1[i][d]; // modulo 2
	}
}

void compute_syndrome_dense(uint64_t h0[W/2][D+1], uint64_t h1[W/2][D+1], uint64_t h0_dense[R_64_TAB][D+1], uint64_t h1_dense[R_64_TAB][D+1], uint64_t e[2][R_64_TAB][D+1], uint64_t s_initial[R_64_TAB][D+1], uint64_t syndrome[R_64_TAB][D+1])
{
	uint64_t k0[R_64_TAB][D+1], k1[R_64_TAB][D+1];
		

	masked_karatsuba_all(e[0], h0_dense, k0);
	
	for(int i = 0; i < W/2; ++i)
		boolean_refresh(h0[i]);
	
	masked_karatsuba_all(e[1], h1_dense, k1);
	
	for(int i = 0; i < W/2; ++i)
		boolean_refresh(h1[i]);
	
	for(int i = 0; i < R_64_TAB; ++i)
	{
		for(int d = 0; d <= D; ++d)
			syndrome[i][d] = s_initial[i][d] ^ k0[i][d] ^ k1[i][d]; // modulo 2
	}
}

void thresold(uint64_t syndrome[R_64_TAB][D+1], uint64_t thresold[D+1])
{
	uint64_t weight[D+1];
	hamming_weight(syndrome, weight);
	

	compute_threshold(weight, thresold);
}



void counter(uint64_t h0[W/2][D+1], uint64_t h1[W/2][D+1], uint64_t tab[2][R_64_TAB][LOG2W+1][D+1], uint64_t syndrome[R_64_TAB][D+1], uint64_t thresold[D+1])
{
	memset(tab, 0, 2*(LOG2W+1)*(R_64_TAB)*(D+1)*8);	
	uint64_t **poly[2] = {(uint64_t**)h0, (uint64_t**)h1};	
	int index = 1;
	for(int p = 0; p < 2; ++p)
	{
		index = 1;
		for(int j = 0; j < W/2; ++j)
		{
			if(j == ((1 << index) - 1))
				index++;
				
			uint64_t z[R_64_TAB][D+1]={0};
			sec_shift_left(syndrome, poly[p]+(j*(D+1)), z);
			
			half_bitslice(LOG2W+1, tab[p], z, R_64_TAB, index);
		}
	}

	uint64_t negative_thresold[D+1];
	
	thresold[0] ^= (uint64_t)(-1);
	boolean_demi_sec_plus(thresold, 1, negative_thresold);

	uint64_t temp[R_64_TAB][LOG2W+1][D+1];	
	sec_fill(temp, negative_thresold);
	
	full_bitslice(LOG2W+1, tab[0], temp, R_64_TAB, LOG2W+1);
	full_bitslice(LOG2W+1, tab[1], temp, R_64_TAB, LOG2W+1);
}

void grey_zone(uint64_t h0[W/2][D+1], uint64_t h1[W/2][D+1], uint64_t tab[2][2][R_64_TAB][LOG2W+1][D+1], uint64_t s_initial[R_64_TAB][D+1], uint64_t e[2][R_64_TAB][D+1])
{
	uint64_t tau[D+1] ={0};
	tau[0] = 3;

	boolean_refresh(tau);

	uint64_t v[R_64_TAB][LOG2W+1][D+1];
	sec_fill(v, tau);
	
	//tab[1] = tab_grey
	memcpy(tab[1], tab[0], 8*2*R_64_TAB*(LOG2W+1)*(D+1));
	
	full_bitslice(LOG2W+1, tab[1][0], v, R_64_TAB, LOG2W+1);
	full_bitslice(LOG2W+1, tab[1][1], v, R_64_TAB, LOG2W+1);

	for(int p = 0; p < 2; ++p)
	{	
		for(int j = 0; j < R_64_TAB; ++j)
		{
			for(int d = 0; d <= D; ++d)
				tab[1][p][j][LOG2W][d] ^= tab[0][p][j][LOG2W][d];
		}
		
	}

	uint64_t thresold[D+1] = {0};
	thresold[0] = (((W/2)+1)/2 + 1);
	boolean_refresh(thresold);
	
	uint64_t tab_BGF[2][R_64_TAB][LOG2W+1][D+1];

	for(int l = 0; l < 2; ++l)
	{
		uint64_t s[R_64_TAB][D+1]={0};
		compute_syndrome(h0, h1, e, s_initial, s);
		counter(h0, h1, tab_BGF, s, thresold);
		
		for(int p = 0; p < 2; ++p)
		{
			for(int j = 0; j < R_64_TAB; ++j)
			{		
				tab_BGF[p][j][LOG2W][0] ^= (uint64_t)(-1);
				uint64_t val[D+1];
				boolean_sec_and(tab_BGF[p][j][LOG2W], tab[l][p][j][LOG2W], val);
			
				for(int d = 0; d <= D; ++d)
					e[p][j][d] ^= val[d];
					
			}
		}
	}
}

void grey_zone_dense(uint64_t h0[W/2][D+1], uint64_t h1[W/2][D+1], uint64_t h0_dense[R_64_TAB][D+1], uint64_t h1_dense[R_64_TAB][D+1], uint64_t tab[2][2][R_64_TAB][LOG2W+1][D+1], uint64_t s_initial[R_64_TAB][D+1], uint64_t e[2][R_64_TAB][D+1])
{
	uint64_t tau[D+1] ={0};
	tau[0] = 3;

	boolean_refresh(tau);

	uint64_t v[R_64_TAB][LOG2W+1][D+1];
	sec_fill(v, tau);
	
	//tab[1] = tab_grey
	memcpy(tab[1], tab[0], 8*2*R_64_TAB*(LOG2W+1)*(D+1));

	full_bitslice(LOG2W+1, tab[1][0], v, R_64_TAB, LOG2W+1);
	full_bitslice(LOG2W+1, tab[1][1], v, R_64_TAB, LOG2W+1);

	//
	for(int p = 0; p < 2; ++p)
	{	
		for(int j = 0; j < R_64_TAB; ++j)
		{
			for(int d = 0; d <= D; ++d)
				tab[1][p][j][LOG2W][d] ^= tab[0][p][j][LOG2W][d];
		}
		
	}

	uint64_t thresold[D+1] = {0};
	thresold[0] = (((W/2)+1)/2 + 1);
	boolean_refresh(thresold);
	
	uint64_t tab_BGF[2][R_64_TAB][LOG2W+1][D+1];

	for(int l = 0; l < 2; ++l)
	{
		uint64_t s[R_64_TAB][D+1]={0};
		compute_syndrome_dense(h0, h1, h0_dense, h1_dense, e, s_initial, s);
		counter(h0, h1, tab_BGF, s, thresold);
		
		for(int p = 0; p < 2; ++p)
		{
			for(int j = 0; j < R_64_TAB; ++j)
			{		
				tab_BGF[p][j][LOG2W][0] ^= (uint64_t)(-1);
				uint64_t val[D+1];
				boolean_sec_and(tab_BGF[p][j][LOG2W], tab[l][p][j][LOG2W], val); 
			
				for(int d = 0; d <= D; ++d)
					e[p][j][d] ^= val[d];
					
			}
		}
	}
}

void decode_BGF(uint64_t h0[W/2][D+1], uint64_t h1[W/2][D+1], uint64_t c0[R_64_TAB][D+1], uint64_t e[2][R_64_TAB][D+1])
{
	memset(e, 0, 2*R_64_TAB*(D+1)*8);
	
	for(int i = 0; i < R_64_TAB; ++i)
	{
		boolean_refresh(e[0][i]); //e_0
		boolean_refresh(e[1][i]); //e_1
	}
		
	uint64_t s_initial[R_64_TAB][D+1];
		
	sec_sparsedense(c0, h0, s_initial, W/2);
	
	for(int i = 0; i < W/2; ++i)
		boolean_refresh(h0[i]);
	
	for(int i = 0; i < 5; ++i)
	{
		uint64_t s[R_64_TAB][D+1];
		compute_syndrome(h0, h1, e, s_initial, s);
		
		uint64_t thresold_v[D+1];
		thresold(s, thresold_v);
		
		uint64_t tab[2][2][R_64_TAB][LOG2W+1][D+1];
		counter(h0, h1, tab[0], s, thresold_v	);
		
		for(int p = 0; p < 2; ++p)
		{
			for(int j = 0; j < R_64_TAB; ++j)
			{		
				for(int d = 0; d <= D; ++d)
					e[p][j][d] ^= tab[0][p][j][LOG2W][d];
					
				e[p][j][0] ^= (uint64_t)(-1);
			}
		}
		
		if(i == 0)
			grey_zone(h0, h1, tab, s_initial, e);
	}
}

void decode_BGF_dense(uint64_t h0[W/2][D+1], uint64_t h1[W/2][D+1], uint64_t h0_dense[R_64_TAB][D+1], uint64_t h1_dense[R_64_TAB][D+1], uint64_t c0[R_64_TAB][D+1], uint64_t e[2][R_64_TAB][D+1])
{
	memset(e, 0, 2*R_64_TAB*(D+1)*8);
	
	for(int i = 0; i < R_64_TAB; ++i)
	{
		boolean_refresh(e[0][i]);
		boolean_refresh(e[1][i]);
	}
		
	uint64_t s_initial[R_64_TAB][D+1];
		
	masked_karatsuba_all(c0, h0_dense, s_initial);

	for(int i = 0; i < R_64_TAB; ++i)
		boolean_refresh(h0_dense[i]);
	
	for(int i = 0; i < 5; ++i)
	{
		uint64_t s[R_64_TAB][D+1];
		compute_syndrome_dense(h0, h1, h0_dense, h1_dense, e, s_initial, s);
		
		uint64_t thresold_v[D+1];
		thresold(s, thresold_v);
		
		uint64_t tab[2][2][R_64_TAB][LOG2W+1][D+1];
		counter(h0, h1, tab[0], s, thresold_v);
		
		for(int p = 0; p < 2; ++p)
		{
			for(int j = 0; j < R_64_TAB; ++j)
			{		
				for(int d = 0; d <= D; ++d)
					e[p][j][d] ^= tab[0][p][j][LOG2W][d];
					
				e[p][j][0] ^= (uint64_t)(-1);
			}
		}
		
		if(i == 0)
			grey_zone_dense(h0, h1, h0_dense, h1_dense, tab, s_initial, e);
	}
}

void sec_equality(uint64_t x[D+1], uint64_t y[D+1], uint64_t z[D+1])
{
	uint64_t temp[D+1];
	for(int d = 0; d <= D; ++d)
		temp[d] = x[d] ^ y[d];
	
	uint64_t t[D+1], t2[D+1];

	memset(z, 0, 8*(D+1));
		
	uint64_t a[D+1];
	for(int d = 0; d<=D; ++d)
		z[d] = temp[d];
		
	for(int k = 32; k != 0; k /= 2)
	{
		uint64_t a[D+1], b[D+1];
		for(int d = 0; d<=D; ++d)
		{
			a[d] = z[d] & (((uint64_t)1 << k) - 1);
			b[d] = (z[d] >> k);
		}
		
		a[0] ^= (((uint64_t)1 << k) - 1);
		b[0] ^= (((uint64_t)1 << k) - 1);
		
		boolean_sec_and(a, b, z);
			
		z[0] ^= (((uint64_t)1 << k) - 1);
	}
}

void fisher_yates(uint64_t x[][D+1], uint16_t s, uint64_t n, uint16_t bits)
{
	for(int i = s - 1; i >= 0; --i)
		{
			uint64_t val_i[D+1]={0};
			val_i[0] = i;
			boolean_refresh(val_i);
			
			uint64_t r[D+1];
			boolean_demi_mult(x[i], n - i, r, bits);
			
			for(int d = 0; d<=D;++d)
				r[d] = r[d] >> 32;	
				
			boolean_demi_sec_plus(r, i, x[i]);
			
			for(int j = i + 1; j < s; ++j)
			{
				uint64_t temp[D+1]={0}, temp1[D+1]={0};
				sec_equality(x[i], x[j], temp);
				
				sec_if(x[i], val_i, temp, temp1);
				memcpy(x[i], temp1, 8*(D+1));				
			}
		}
}
// Fisher-Yates
void sec_rand_keys(uint64_t seed[4][D+1], uint64_t h0[W/2][D+1],  uint64_t h1[W/2][D+1])
{
	uint64_t h[W][D+1];
	uint32_t h_32[W][D+1];
	
	H(32, W*4, seed, h_32); // seed is on 32bytes, so 256bits
	
	// we cast on 64 bits
	for(int i = 0; i < W/2; ++i)
	{
		for(int d = 0; d<=D; ++d)
		{
			h0[i][d] = h_32[i][d];
			h1[i][d] = h_32[i+W/2][d];
		}
	}
	
	fisher_yates(h0, W/2, R, BITS);
	fisher_yates(h1, W/2, R, BITS);
	
}

void sec_elevation(uint64_t x[R_64_TAB][D+1], uint64_t y[R_64_TAB][D+1], int p)
{
	memset(y, 0, R_64_TAB*(D+1)*8);
	for(int i = 0; i < R; ++i)
	{
		int dest = (p * i) % R;
		int big = i/64;
		int little = i & 63;
		int big_dest = dest/64;
		int little_dest = dest & 63;
		
		uint64_t val[D+1];
		
		for(int d = 0; d<=D; ++d)
		{
			val[d] = ((x[big][d] >> (63 - little)) & 1);
			y[big_dest][d] ^= val[d] << (63 - little_dest);
		}
		
	}
}

void masked_fast_inversion(uint64_t x_sparse[][D+1], uint64_t out[R_64_TAB][D+1], int size_sparse)
{
	uint64_t x[R_64_TAB][D+1]={0}, t[R_64_TAB][D+1]={0};
	
	t[0][0] = (uint64_t)(1) << 63;
	sec_sparsedense(t, x_sparse, x, size_sparse);
	
	uint64_t f[R_64_TAB][D+1], g[R_64_TAB][D+1];
	memcpy(f, x, R_64_TAB * (D+1)* 8);
	memcpy(out, x, R_64_TAB * (D+1)* 8);
	
	for(int i = 0; i < BITS; ++i)
	{
		sec_elevation(f, g, permut_2[i]);
				
		masked_karatsuba_all(f, g, t); 
		
		memcpy(f, t, R_64_TAB * (D+1) * 8);
		
		if(((R - 2) >> (i+1)) & 1)
		{
			sec_elevation(f, t, r_mod[i]);
			uint64_t t1[R_64_TAB][D+1];
			masked_karatsuba_all(out, t, t1);
			memcpy(out, t1, R_64_TAB * (D+1) * 8);	
		}
		
	}

	for(int i = 0; i < R_64_TAB; ++i)
	{
		for(int d = 0; d<=D; ++d)
			out[i][d] = t[i][d] << 1;
	}
	memcpy(out, t, R_64_TAB * (D+1) * 8);	
}

void masked_fast_inversion_dense(uint64_t x[R_64_TAB][D+1], uint64_t out[R_64_TAB][D+1])
{
	uint64_t t[R_64_TAB][D+1], f[R_64_TAB][D+1], g[R_64_TAB][D+1];
	memcpy(f, x, R_64_TAB * (D+1)* 8);
	memcpy(out, x, R_64_TAB * (D+1)* 8);
	
	for(int i = 0; i < BITS; ++i)
	{
		sec_elevation(f, g, permut_2[i]);
				
		masked_karatsuba_all(f, g, t);
		
		memcpy(f, t, R_64_TAB * (D+1) * 8);
		
		if(((R - 2) >> (i+1)) & 1)
		{
			sec_elevation(f, t, r_mod[i]);
			uint64_t t1[R_64_TAB][D+1];
			masked_karatsuba_all(out, t, t1);
			memcpy(out, t1, R_64_TAB * (D+1) * 8);	
		}
		
	}

	sec_elevation(out, t, 2);
	memcpy(out, t, R_64_TAB * (D+1) * 8);		
}

void generate_keys(uint64_t h0[W/2][D+1], uint64_t h1[W/2][D+1], uint64_t h[R_64_TAB][D+1], uint64_t sigma[4][D+1])
{
	uint64_t m[4][D+1];
	for(int i = 0; i < 4; ++i)
	{
		for(int d = 0; d<=D;++d)
			m[i][d] = next();
	}
	
	sec_rand_keys(m, h0, h1);
	

	uint64_t inv_h0[R_64_TAB][D+1]={0};
	masked_fast_inversion(h0, inv_h0, W/2);
	
	sec_sparsedense(inv_h0, h1, h, W/2);
	
	for(int i = 0; i < 4; ++i)
	{
		for(int d = 0; d<=D;++d)
			sigma[i][d] = next();
	}
}

void generate_keys_dense(uint64_t h0[W/2][D+1], uint64_t h1[W/2][D+1], uint64_t h0_dense[R_64_TAB][D+1], uint64_t h1_dense[R_64_TAB][D+1], uint64_t h[R_64_TAB][D+1], uint64_t sigma[4][D+1])
{
	uint64_t m[4][D+1];
	for(int i = 0; i < 4; ++i)
	{
		for(int d = 0; d<=D;++d)
			m[i][d] = next();
	}
	sec_rand_keys(m, h0, h1);
	
	uint64_t un[R_64_TAB][D+1] = {0};
	un[0][0] = (uint64_t)(1) << 63;
	
	for(int i = 0; i < R_64_TAB; ++i)
		boolean_refresh(un[i]);

	sec_sparsedense(un, h0, h0_dense, W/2);
	for(int i = 0; i < R_64_TAB; ++i)
		boolean_refresh(un[i]);
	sec_sparsedense(un, h1, h1_dense, W/2);

	uint64_t inv_h0[R_64_TAB][D+1]={0};

	masked_fast_inversion_dense(h0_dense, inv_h0);
	masked_karatsuba_all(inv_h0, h1_dense, h);
	
	for(int i = 0; i < 4; ++i)
	{
		for(int d = 0; d<=D;++d)
			sigma[i][d] = next();
	}
}

void L(uint64_t e[2][R_64_TAB][D+1], uint64_t res[4][D+1])
{
	int size = R/8 + (R&7 ? 1 : 0);
	uint8_t v[D+1][2*size], ret[D+1][48];
	for(int p = 0; p < 2; ++p)
	{
		for(int i = 0; i < size; ++i)
		{
			for(int d = 0; d<=D; ++d)
				v[d][i+(size*p)] = (e[p][i/8][d] >> i) & (uint8_t)(-1);
		}
	}
	
	memset(ret, 0, 48*(D+1));
	sha3_384_masked_HO(ret, 2*size, v);
	
	// we take the first 256 bits
	memset(res, 0, 32*(D+1));
	for(int i = 0; i < 32; ++i)
	{
		for(int d = 0; d <= D; ++d)
			res[i/8][d] ^= (uint64_t)ret[d][i] << (56-((i*8)&63));
	}
}

void generate_errors(uint64_t m[4][D+1], uint64_t e[2][R_64_TAB][D+1])
{		
	uint64_t e_sparse[T][D+1] = {0};
	uint32_t e_32[T][D+1];
	H(32, 4*T, m, e_32);
	
	// we cast on 64 bits
	for(int i = 0; i < T; ++i)
	{
		for(int d = 0; d<=D; ++d)
			e_sparse[i][d] = e_32[i][d];
	}
	fisher_yates(e_sparse, T, N, BITS+1);

	uint64_t un[R_64_TAB][D+1] = {0};
	un[0][0] = (uint64_t)(1) << 63;
	
	for(int i = 0; i < T; ++i)
	{
		for(int j = 0; j < R_64_TAB; ++j)
			boolean_refresh(un[i]);
			
		uint64_t temp[R_64_TAB][D+1] = {0};
		
		uint64_t e_reduit[D+1];
		boolean_demi_sec_plus(e_sparse[i], -R, e_reduit);
		
		boolean_refresh(e_sparse[i]);
			
		uint64_t res[D+1] = {0};
		for(int d = 0; d<=D;++d)
			res[d] = ((e_reduit[d] >> 63) & 1) * (uint64_t)(-1);
			
		uint64_t s[D+1];
		sec_if(e_sparse[i], e_reduit, res, s);
		
		sec_shift(un, s, temp);
		
		for(int j = 0; j < R_64_TAB; ++j)
		{
			uint64_t e0[D+1]={0}, e1[D+1]={0};
			boolean_sec_and(temp[j], res, e0);
			res[0] ^= (uint64_t)(-1);
			boolean_sec_and(temp[j], res, e1);
			res[0] ^= (uint64_t)(-1);
			
			for(int d = 0; d<=D; ++d)
			{
				
				e[0][j][d] ^= e0[d];
				e[1][j][d] ^= e1[d];
			}
		}
	}
	
}


void K(uint64_t m[4][D+1], uint64_t c[R_64_TAB+4][D+1], uint64_t res[4][D+1])
{
	int t = R/8 + (R&7 ? 1 : 0);
	int size = 32 + t + 32;
	
	uint8_t v[D+1][size], ret[D+1][48];
	
	for(int i = 0; i < 32; ++i)
	{
		for(int d = 0; d<=D; ++d)
			v[d][i] = (m[i/8][d] >> i) & (uint8_t)(-1);
	}	
	
	for(int i = 0; i < t; ++i)
	{
		for(int d = 0; d<=D; ++d)
			v[d][i+32] = (c[i/8][d] >> i) & (uint8_t)(-1);
	}
	
	for(int i = 0; i < 32; ++i)
	{
		for(int d = 0; d<=D; ++d)
			v[d][i+t+32] = (c[i/8+R_64_TAB][d] >> i) & (uint8_t)(-1);
	}

	
	memset(ret, 0, 48*(D+1));
	sha3_384_masked_HO(ret, size, v);
	
	// we take the first 256 bits
	memset(res, 0, 32*(D+1));
	for(int i = 0; i < 32; ++i)
	{
		for(int d = 0; d <= D; ++d)
			res[i/8][d] ^= (uint64_t)ret[d][i] << (56-((i*8)&63));
	}
}

void encaps(uint64_t h[R_64_TAB][D+1], uint64_t c[R_64_TAB+4][D+1])
{	
	uint64_t m[4][D+1];
	for(int i = 0; i < 4; ++i)
	{
		for(int d = 0; d<=D;++d)
			m[i][d] = next();
	}
	
	uint64_t e[2][R_64_TAB][D+1] = {0};
	generate_errors(m, e);
	
	for(int i = 0; i < 4; ++i)
		boolean_refresh(m[i]);
	
	memset(c, 0, (R_64_TAB+4)*(D+1)*8);
	
	masked_karatsuba_all(e[1], h, c); //e1h
	
	for(int i = 0; i < R_64_TAB; ++i)
	{
		for(int d = 0; d<=D; ++d)
			c[i][d] ^= e[0][i][d]; //e0 + e1h
	}
	
	L(e, &c[R_64_TAB]);
	
	for(int i = 0; i < 4; ++i)
	{
		for(int d = 0; d <= D; ++d)
			c[i+R_64_TAB][d] ^= m[i][d];
	}
}

void decaps(uint64_t h0[W/2][D+1], uint64_t h1[W/2][D+1], uint64_t h0_dense[R_64_TAB][D+1], uint64_t h1_dense[R_64_TAB][D+1], uint64_t c[R_64_TAB+4][D+1], uint64_t sigma[4][D+1], uint64_t k[4][D+1])
{
	uint64_t e_prime[2][R_64_TAB][D+1] = {0};
	decode_BGF_dense(h0, h1, h0_dense, h1_dense, c, e_prime);
	
	uint64_t m_prime[4][D+1] = {0};
	L(e_prime, m_prime);
	
	for(int i = 0; i < 4; ++i)
	{
		for(int d = 0; d<=D; ++d)
			m_prime[i][d] ^= c[R_64_TAB+i][d]; 
	}
	
	uint64_t e_construct[2][R_64_TAB][D+1] = {0};
	generate_errors(m_prime, e_construct);
	
	for(int i = 0; i < 4; ++i)
		boolean_refresh(m_prime[i]);
		
	// compare e_prime and e_construct
	uint64_t val[D+1] = {0};
	val[0] = 1;
	boolean_refresh(val);
	
	for(int i = 0; i < 2; ++i)
	{
		for(int j = 0; j < R_64_TAB; ++j)
		{
			uint64_t t[D+1], t1[D+1];
			sec_equality(e_prime[i][j], e_construct[i][j], t);
			t[0] ^= 1;
			boolean_sec_and(val, t, t1);
			memcpy(val, t1, (D+1)*8);
			
		}
	}
	
	uint64_t t[4][D+1] = {0}, t1[4][D+1] = {0};
	K(m_prime, c, t);
	K(sigma, c, t1);
	
	sec_if_vector(t, t1, val, k, 4);	
}

void decaps_sparse(uint64_t h0[W/2][D+1], uint64_t h1[W/2][D+1], uint64_t c[R_64_TAB+4][D+1], uint64_t sigma[4][D+1], uint64_t k[4][D+1])
{
	
	uint64_t e_prime[2][R_64_TAB][D+1] = {0};
	decode_BGF(h0, h1, c, e_prime);
	
	uint64_t m_prime[4][D+1] = {0};
	L(e_prime, m_prime);
	
	for(int i = 0; i < 4; ++i)
	{
		for(int d = 0; d<=D; ++d)
			m_prime[i][d] ^= c[R_64_TAB+i][d]; 
	}
	
	uint64_t e_construct[2][R_64_TAB][D+1] = {0};
	generate_errors(m_prime, e_construct);
	for(int i = 0; i < 4; ++i)
		boolean_refresh(m_prime[i]);
	
	// compare e_prime and e_construct
	uint64_t val[D+1] = {0};
	val[0] = 1;
	boolean_refresh(val);
	
	for(int i = 0; i < 2; ++i)
	{
		for(int j = 0; j < R_64_TAB; ++j)
		{
			uint64_t t[D+1], t1[D+1];
			sec_equality(e_prime[i][j], e_construct[i][j], t);
			t[0] ^= 1;
			boolean_sec_and(val, t, t1);
			memcpy(val, t1, (D+1)*8);
			
		}
	}
	
	uint64_t t[4][D+1] = {0}, t1[4][D+1] = {0};
	K(m_prime, c, t);
	K(sigma, c, t1);
	
	sec_if_vector(t, t1, val, k, 4);
}

int main()
{
	if (!seed()) {
		return 1;
	}
	
	// HYBRID DENSE-SPARSE	
	uint64_t h0[W/2][D+1], h1[W/2][D+1];
	uint64_t h0_dense[R_64_TAB][D+1], h1_dense[R_64_TAB][D+1];
	uint64_t h[R_64_TAB][D+1];
	uint64_t c[R_64_TAB+4][D+1];
	uint64_t sigma[4][D+1];
	uint64_t k[4][D+1];
	
	generate_keys_dense(h0, h1, h0_dense, h1_dense, h, sigma);
	encaps(h, c);
	decaps(h0, h1, h0_dense, h1_dense, c, sigma, k);
		
	//SPARSE
	
	/*
	uint64_t h0[W/2][D+1], h1[W/2][D+1];
	uint64_t h[R_64_TAB][D+1];
	uint64_t c[R_64_TAB+4][D+1];
	uint64_t sigma[4][D+1];
	uint64_t k[4][D+1];
	
	generate_keys(h0, h1, h, sigma);
	encaps(h, c);
	decaps_sparse(h0, h1, c, sigma, k);
	*/

	return 0;
}
