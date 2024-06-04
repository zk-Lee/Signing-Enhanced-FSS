// Crypto 2001 version using relative primes

#include <openssl/rsa.h>
#include <openssl/rand.h>
#include <openssl/bn.h>
#include <openssl/sha.h>
#include <stdio.h>
#include <time.h>
#include <math.h>
#include <string.h>
FILE* file;

struct FwSecSigPubKey {
	int T;
	BIGNUM* N;
	BIGNUM* v;
}* gPubKey;

struct FwSecSigPriKey {
	int i;
	BIGNUM* s;
	BIGNUM* t;
	int seed;
}* gPriKey;

struct FwSecSigSign {
	int i;
	BIGNUM* z;
	BIGNUM* sigma;
	BIGNUM* e;
};

int gRSALength;		// k
int l = SHA_DIGEST_LENGTH*8;
int gNumPeriod;	// T
int seed = 9;	// seed value for random prime generation

BN_CTX* ctx;

void initializeStructures()
{
	// public key
	gPubKey->N = BN_new();
	gPubKey->v = BN_new();

	// private key
	gPriKey->s = BN_new();
	gPriKey->t = BN_new();
	gPriKey->seed = 0;
}
	

void hash(BIGNUM* r, int i, BIGNUM* a, BIGNUM* b, BIGNUM* c)
{
	char hash_digest[SHA_DIGEST_LENGTH];
	char temp[2048];
	SHA_CTX sha_ctx;
	SHA1_Init(&sha_ctx);

	sprintf(temp, "%x", i);
	SHA1_Update(&sha_ctx, temp, strlen(temp));

	BN_bn2bin(a, temp);
	SHA1_Update(&sha_ctx, temp, BN_num_bytes(a));

	BN_bn2bin(b, temp);
	SHA1_Update(&sha_ctx, temp, BN_num_bytes(b));

	BN_bn2bin(c, temp);
	SHA1_Update(&sha_ctx, temp, BN_num_bytes(c));

	SHA1_Final(hash_digest, &sha_ctx);

	BN_bin2bn(hash_digest, SHA_DIGEST_LENGTH, r);
}

int isRelativePrime(BIGNUM** es, int bound)
{
	BIGNUM* t1 = BN_new();
	for(int i=0; i<bound; i++) {
		BN_gcd(t1, es[i], es[bound],ctx);
		if(!BN_is_one(t1)) return 0;
	}

	return 1;
}

void generateRelativePrimeForTimeConsuming(BIGNUM** e, int seed)
{
	//BN_GENCB *cb = BN_GENCB_new();
	//for(int i=0; i<gPubKey->T; i++)
	for(int i=0; i<log2(gPubKey->T); i++)	// optimized version
		BN_generate_prime_ex(e[i], l, 0, NULL, NULL, NULL);
}

void generateE(BIGNUM* e, int index)
{
	char rnd_seed[80];
	sprintf(rnd_seed, "%d:%d",seed, index);
	RAND_seed(rnd_seed, sizeof(rnd_seed));

        BIGNUM* num = BN_new();
        BIGNUM* range = BN_new();
        BIGNUM* two_l = BN_new();
        BIGNUM* offset = BN_new();

        BN_one(two_l);
        BN_lshift(two_l, two_l, l);
        BN_copy(range, two_l);
        BN_div_word(range, gPubKey->T);

        BN_copy(offset, two_l);
	BN_set_word(num, index);
	BN_mul(num, range, num, ctx);
	BN_add(offset, offset, num);
        while(1) {
                BN_pseudo_rand_range(e, range);
                BN_add(e, e, offset);
                if(BN_is_prime_ex(e, l, ctx, NULL)) break;
        }
}


	
int setup()
{
	BIGNUM* t1 = BN_new();
	BIGNUM* t2 = BN_new();
	BIGNUM* t3 = BN_new();

/*
	// key generate
	RSA* rsa;

	// p,q <-- Z, N=pq
	rsa = RSA_generate_key(gRSALength, 5, NULL, NULL);
        if(RSA_check_key(rsa) != 1) {
               perror("not gnerate RSA key");
               exit(0);
	}

	BIGNUM* phi = BN_new();
	BN_one(t1);
	BN_sub(t2, rsa->p, t1);
	BN_sub(t3, rsa->q, t1);
	BN_mul(phi, t2, t3, ctx);
	 
	BN_copy(gPubKey->N,rsa->n);
*/

	BIGNUM* phi = BN_new();
        // safe RSA is generated
        // p<--2p'+1; p' <-- 2p''+1; p, p', p'' are primes
        // q<--2q'+1; q' <-- 2q''+1; q, q', q'' are primes
        // p,q <-- Z, N=pq
        BIGNUM* p = BN_new();
        BIGNUM* q = BN_new();

        BN_generate_prime_ex(p, gRSALength/2, 1, NULL, NULL, NULL);
        BN_generate_prime_ex(q, gRSALength/2, 1, NULL, NULL, NULL);

        BN_mul(gPubKey->N, p, q, ctx);

        // use phi(N)
        phi = BN_new();
        BN_sub(t1, p, BN_value_one());
        BN_sub(t2, q, BN_value_one());
        BN_mul(phi,t1, t2,ctx);

	// t1 <-- Z_N
	BN_rand_range(t1, gPubKey->N);

	// f2
	BIGNUM* f2 = BN_new();
	BN_one(f2);
	BIGNUM* e0 = BN_new();
	BIGNUM* e = BN_new();

	char rnd_seed[80];
	sprintf(rnd_seed, "%d:%d",seed, 0);
	RAND_seed(rnd_seed, sizeof rnd_seed);
	BN_generate_prime_ex(e0, l, 0, NULL, NULL, NULL);
	for(int i=1; i<gPubKey->T; i++) {
		// e1, ..., eT
		//sprintf(rnd_seed, "%d:%d",seed, i);
		//RAND_seed(rnd_seed, sizeof rnd_seed);
		//BN_generate_prime_ex(e, l, 0, NULL, NULL, NULL);
		generateE(e, i);
		BN_mod_mul(t2, f2, e, phi, ctx);

		BN_copy(f2,t2); 
	}

	// s1<-- t1^f2
	BN_mod_exp(gPriKey->s, t1, f2, gPubKey->N, ctx);
	
	// v <-- 1/s1^e1
	BN_mod_exp(t3, gPriKey->s, e0, gPubKey->N, ctx);
	BN_mod_inverse(gPubKey->v, t3, gPubKey->N, ctx);

	// t2 <-- t1^e1
	BN_mod_exp(gPriKey->t, t1, e0, gPubKey->N, ctx);

	gPriKey->i = 0;

	BN_free(t1);
	BN_free(t2);
	BN_free(t3);
	BN_free(phi);
	BN_free(f2);
	BN_free(e0);
	BN_free(e);
	//RSA_free(rsa);

	return 0;
}

void signMessage(struct FwSecSigSign* sign, BIGNUM* m)
{
	BIGNUM* t1 = BN_new();

	// r <-- Z_N
	BIGNUM* r = BN_new();
	BN_rand_range(r, gPubKey->N);

	// y <-- r^{ei}
	BIGNUM* y = BN_new();

	//char rnd_seed[80];
	//sprintf(rnd_seed, "%d:%d",seed, gPriKey->i);
	//RAND_seed(rnd_seed, sizeof rnd_seed);
	//BN_generate_prime_ex(sign->e, l, 0, NULL, NULL, NULL);
	generateE(sign->e, gPriKey->i);

	BN_mod_exp(y, r, sign->e, gPubKey->N, ctx);

	// sigma <-- H(i, ei, y, m)
	hash(sign->sigma, gPriKey->i, sign->e, y, m);

	// z <-- rs^sigma
	BN_mod_exp(t1, gPriKey->s, sign->sigma, gPubKey->N, ctx);
	BN_mod_mul(sign->z, r, t1, gPubKey->N, ctx);

/*
	printf("%d\n", l);
	BN_print_fp(stdout, sign->e);
	printf("\n");
	BN_print_fp(stdout, r);
	printf("\n");
	BN_print_fp(stdout, t1);
	printf("\n");
	BN_print_fp(stdout, sign->z);
	printf("\n");
*/
	sign->i = gPriKey->i;

	BN_free(t1);
	BN_free(r);
	BN_free(y);
}

void update()
{
	if(gPriKey->i == gPubKey->T-1) return;

	// update secret key

	int i;

	BIGNUM* e = BN_new();

	// just for time consuming
	//generateRelativePrimeForTimeConsuming(es, gPriKey->seed);

	// sj+1 <-- tj+1 ^ ej+2 .. eT
	BIGNUM* t1 = BN_new();
	BIGNUM* t2 = BN_new();
	BN_copy(t1, gPriKey->t);
	char rnd_seed[80];
	for(i=0; i<gPubKey->T; i++) {	// just for time consuming log2(T)
		// FIXME: the i should be properly changed.
		//sprintf(rnd_seed, "%d:%d",seed, i);
		//RAND_seed(rnd_seed, sizeof(rnd_seed));
		//BN_generate_prime_ex(e, l, 0, NULL, NULL, NULL);
		generateE(e, i);
		BN_mod_exp(t1, t1, e, gPubKey->N, ctx);
	} 
	BN_copy(gPriKey->s, t1);

	//sprintf(rnd_seed, "%d:%d",seed, gPriKey->i + 1);
	//RAND_seed(rnd_seed, sizeof(rnd_seed));
	//BN_generate_prime_ex(e, l, 0, NULL, NULL, NULL);
	generateE(e, gPriKey->i + 1);
	BN_mod_exp(t1, gPriKey->t, e, gPubKey->N, ctx);
	BN_copy(gPriKey->t, t1);

	// i++
	gPriKey->i ++;

	BN_free(t1);
	BN_free(t2);
}

void allocSign(struct FwSecSigSign* sign)
{
	sign->z = BN_new();
	sign->sigma = BN_new();
	sign->e = BN_new();
}


int verify(struct FwSecSigSign* sign, BIGNUM** m, struct FwSecSigPubKey* pubKey)
{
	BIGNUM* y = BN_new();
	BIGNUM* c = BN_new();
	BIGNUM* t1 = BN_new();
	BIGNUM* t2 = BN_new();

	// y' <-- z^e v^sigma
	BN_mod_exp(t1, sign->z, sign->e, pubKey->N, ctx);
	BN_mod_exp(t2, pubKey->v, sign->sigma, pubKey->N, ctx);
	BN_mod_mul(y, t1, t2, pubKey->N, ctx);

	hash(c, sign->i, sign->e, y, m[0]);
	
	int flag = (BN_cmp(sign->sigma, c)==0);

	BN_free(y);
	BN_free(c);
	BN_free(t1);
	BN_free(t2);

	return flag;
}

int main(int argc, const char* argv[])
{
	clock_t start, end;

	ctx = BN_CTX_new();
//	file = fopen("output.txt","w");

	gPubKey = malloc(sizeof(struct FwSecSigPubKey));
	gPriKey = malloc(sizeof(struct FwSecSigPriKey));


	// argument : rsa_bit_length period_length hash_size
	if(argc < 3) return 0;
	gRSALength = atoi(argv[1]);	// k
	gPubKey->T = atoi(argv[2]);	// T


	initializeStructures();


	//printf("%d\t", gPubKey->T);
		
	start = clock();
	setup();
	end = clock();
	printf("Setup: %f\t", (float)(end-start)/CLOCKS_PER_SEC);

	// test
	struct FwSecSigSign **sign;
	BIGNUM** message;
	sign = malloc(sizeof(struct FwSecSigSign*)*gPubKey->T);
	message = malloc(sizeof(BIGNUM*)*gPubKey->T);

	int i;
	char* tempMsg = malloc(SHA_DIGEST_LENGTH);
	for(i=0; i<gPubKey->T; i++) {
		sign[i] = malloc(sizeof(struct FwSecSigSign));
		allocSign(sign[i]);

		message[i] = BN_new();
		
		RAND_bytes(tempMsg, SHA_DIGEST_LENGTH);
		BN_bin2bn(tempMsg, SHA_DIGEST_LENGTH, message[i]);
	}

	start = clock();

	// sign and update
	//for(i=0; i<gPubKey->T; i++) {
	for(i=0; i<1; i++) {
		signMessage(sign[i], message[i]);
	end = clock();
	printf("Sign: %f\t", (float)(end-start)/CLOCKS_PER_SEC);
	start = clock();
		update();
	}

	end = clock();
	printf("Update: %f\t", (float)(end-start)/CLOCKS_PER_SEC);

	start = clock();
	// verification for each sign	
	//for(i=0; i<gPubKey->T; i++) {
	for(i=0; i<1; i++) {
		if(!verify(sign[i], &message[i], gPubKey)) {
//			printf("sign[%d] is invalid\n", i);
		}
	}
	end = clock();
	printf("Sign: %f\t", (float)(end-start)/CLOCKS_PER_SEC);


    int x = 0;
    x += BN_num_bytes(gPubKey->N);
    x += BN_num_bytes(gPubKey->v);
    x += sizeof(int);

    int y = 0;
    y += sizeof(int);
    y += sizeof(int);
    y += BN_num_bytes(gPriKey->s);
    y += BN_num_bytes(gPriKey->t);

    printf("Pub size: %d\n", x);
    printf("Pri size: %d\n", y);
    printf("sign size: %d\n", BN_num_bytes(sign[0]->z)+BN_num_bytes(sign[0]->sigma)+BN_num_bytes(sign[0]->e)+sizeof(int));
}
