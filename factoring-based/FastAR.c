// Asiacrypto 2000 version

#include <openssl/rsa.h>
#include <openssl/rand.h>
#include <openssl/bn.h>
#include <openssl/sha.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

#define l 160

BIGNUM* phi;

struct FwSecSigPubKey {
	int T;
	BIGNUM* U;
	BIGNUM* N;
}* gPubKey;

struct FwSecSigPriKey {
	int i;
	BIGNUM* g;
	BIGNUM* X;
	BIGNUM* S;
}* gPriKey;

struct FwSecSigSign {
	int i;
	BIGNUM* Z;
	BIGNUM* sigma;
};

int gRSALength;		// k

BN_CTX* ctx;

void initializeStructures()
{
	// public key
	gPubKey->U = BN_new();
	gPubKey->N = BN_new();

	// private key
	gPriKey->g = BN_new();
	gPriKey->X = BN_new();
	gPriKey->S = BN_new();
}
	

void hash(BIGNUM* r, int a, BIGNUM* b, BIGNUM* c)
{
	char hash_digest[SHA_DIGEST_LENGTH];
	char temp[2048];
	SHA_CTX sha_ctx;
	SHA1_Init(&sha_ctx);

	sprintf(temp,"%x",a);
	SHA1_Update(&sha_ctx, temp, strlen(temp));

	BN_bn2bin(b, temp);
	SHA1_Update(&sha_ctx, temp, BN_num_bytes(b));

	BN_bn2bin(c, temp);
	SHA1_Update(&sha_ctx, temp, BN_num_bytes(c));

	SHA1_Final(hash_digest, &sha_ctx);

	BN_bin2bn(hash_digest, l/8, r);
}

void exp_twos_power(BIGNUM* y, BIGNUM* x, int n)
{
	// y = x^u^i
	BIGNUM* t1 = BN_new();
	BN_copy(t1,x);

	int i;
	for(i=0; i<n; i++) {
		BN_mod_mul(y, t1, t1, gPubKey->N, ctx);
		BN_copy(t1, y);
	}

	BN_free(t1);
}

int isCongruent3Mod4(const BIGNUM *num) {
    BN_ULONG remainder = BN_mod_word(num, 4);
    return (remainder == 3);
}

int orderCheck(const BIGNUM *g, const BIGNUM *e) {  //NEED CHECK 
    BIGNUM *result = BN_new();
	BN_mod_exp(result, g, e, gPubKey->N, ctx);
    int one = (BN_get_word(result) == 1);
    BN_free(result);
    return one;
}

int orderCheck2(const BIGNUM *g, const BIGNUM *e) { //NEED CHECK 
    BIGNUM *result = BN_new();
	BN_mod_exp(result, g, e, gPubKey->N, ctx);
    int minus_one = (BN_get_word(result) == -1);
    BN_free(result);
    return minus_one;
}


int setup()
{
	BIGNUM* t1 = BN_new();
	BIGNUM* t2 = BN_new();
	BIGNUM* x = BN_new();
	BIGNUM* s = BN_new();

	BIGNUM* p = BN_new();
	BIGNUM* q = BN_new();




    do {
        BN_generate_prime_ex(p, gRSALength/2, 1, NULL, NULL, NULL);
    } while (!isCongruent3Mod4(p)); //NEED CHECK 

    do {
        BN_generate_prime_ex(q, gRSALength/2, 1, NULL, NULL, NULL);
    } while (!isCongruent3Mod4(q)); //NEED CHECK 

	BN_mul(gPubKey->N, p, q, ctx);

	// use phi(N)
	phi = BN_new();
	BN_sub(t1, p, BN_value_one());
	BN_sub(t2, q, BN_value_one());
	BN_mul(phi, t1, t2, ctx);




	BIGNUM* little_p = BN_new();
	BIGNUM* little_q = BN_new();
	BIGNUM* little_pq = BN_new();
	BIGNUM* little_2pq = BN_new();
	BIGNUM* little_2p = BN_new();
	BIGNUM* little_2q = BN_new();

    BN_copy(little_p, t1);
    BN_copy(little_q, t2);
    BN_rshift1(little_p, gPubKey->N);
    BN_rshift1(little_q, gPubKey->N);





	// 2^{l(T+1)} mod phi(N)
	BN_set_word(t1, 2);
	BN_set_word(t2, l*(gPubKey->T+1));
	BN_mod_exp(x, t1, t2, phi, ctx);



	BN_mod_mul(little_pq, little_p, little_q, gPubKey->N, ctx);
	BN_mod_mul(little_2pq, little_pq, t1, gPubKey->N, ctx);
	BN_mod_mul(little_2p, little_p, t1, gPubKey->N, ctx);
	BN_mod_mul(little_2q, little_q, t1, gPubKey->N, ctx);
    // generate g and compute X <- R^{2^{l*(T+1)}}
    do {
        BN_rand_range(gPriKey->g, gPubKey->N);
    } while ( !orderCheck(gPriKey->g, little_2pq)       //NEED CHECK 
             && orderCheck(gPriKey->g, little_pq)       //NEED CHECK 
             && orderCheck(gPriKey->g, little_2q)       //NEED CHECK 
             && orderCheck(gPriKey->g, little_2p)       //NEED CHECK 
             && orderCheck2(gPriKey->g, little_pq) );   //NEED CHECK 

	BN_mod_exp(gPriKey->X, gPriKey->g, x, gPubKey->N, ctx);
	
    BN_rshift1(t1, gPubKey->N);
	BN_rand_range(s, t1);
	BN_mod_exp(gPriKey->S, gPriKey->g, s, gPubKey->N, ctx);
	BN_mod_exp(t2, gPriKey->X, s, gPubKey->N, ctx);
	BN_mod_inverse(gPubKey->U, t2, gPubKey->N, ctx);	
	gPriKey->i = 0;

	BN_free(t1);
	BN_free(t2);
	BN_free(x);
	BN_free(s);
	BN_free(p);
	BN_free(q);

	BN_free(little_p);
	BN_free(little_q);
	BN_free(little_2pq);
	BN_free(little_pq);
	BN_free(little_2p);
	BN_free(little_2q);

	return 0;
}


void signMessage(struct FwSecSigSign* sign, BIGNUM* m)
{
	BIGNUM* t1 = BN_new();

    BIGNUM* e = BN_new();

    BN_rshift1(t1, gPubKey->N);
	BN_rand_range(e, t1);

    BIGNUM* R = BN_new();
    BN_mod_exp(R, gPriKey->g, e, gPubKey->N, ctx);

    BN_mod_exp(t1, gPriKey->X, e, gPubKey->N, ctx);

	hash(sign->sigma, gPriKey->i, t1, m);

	// Z <-- RS^sigma
	BN_mod_exp(t1, gPriKey->S, sign->sigma, gPubKey->N, ctx);
	BN_mod_mul(sign->Z, R, t1, gPubKey->N, ctx);

	sign->i = gPriKey->i;
	BN_free(t1);
	BN_free(e);
	BN_free(R);
}

void update()
{
	if(gPriKey->i == gPubKey->T-1) return;

	gPriKey->i ++;
	exp_twos_power(gPriKey->S, gPriKey->S, l);
}

void allocSign(struct FwSecSigSign* sign)
{
	sign->Z = BN_new();
	sign->sigma = BN_new();
}


int verify(struct FwSecSigSign* sign, BIGNUM** m, struct FwSecSigPubKey* pubKey)
{
	BIGNUM* sigma = BN_new();
	BIGNUM* Y = BN_new();
	BIGNUM* t1 = BN_new();
	BIGNUM* t2 = BN_new();
	BIGNUM* t3 = BN_new();

	// Y' <-- Z^{2^{l*(T+1)}} U^sigma
	exp_twos_power(t1, sign->Z, l*(pubKey->T+1-sign->i));
	BN_mod_exp(t2, pubKey->U, sign->sigma, pubKey->N, ctx);
	BN_mod_mul(t3, t1, t2, pubKey->N, ctx);

	if(sign->i>0)
		exp_twos_power(Y, t3, l*(sign->i));
	else BN_copy(Y, t3);


	hash(sigma, sign->i, Y, m[0]);

	int flag = (BN_cmp(sigma, sign->sigma)==0);

	BN_free(Y);
	BN_free(t1);
	BN_free(t2);
	BN_free(t3);

	return flag;
}

int main(int argc, const char* argv[])
{
	clock_t start, end;

	ctx = BN_CTX_new();

	gPubKey = malloc(sizeof(struct FwSecSigPubKey));
	gPriKey = malloc(sizeof(struct FwSecSigPriKey));

	initializeStructures();

	// argument : rsa_bit_length period_length hash_size
	if(argc < 3) return 0;
	gRSALength = atoi(argv[1]);	// k
	gPubKey->T = atoi(argv[2]);	// T
		
	start = clock();
	setup();
	end = clock();
	printf("Setup: %f\t", (float)(end-start)/CLOCKS_PER_SEC);

	// test
	struct FwSecSigSign **sign;
	BIGNUM** message;
//	sign = malloc(sizeof(struct FwSecSigSign*)*gPubKey->T);
//	message = malloc(sizeof(BIGNUM*)*gPubKey->T);
	sign = malloc(sizeof(struct FwSecSigSign*));
	message = malloc(sizeof(BIGNUM*));

	int i;
	char* tempMsg = malloc(SHA_DIGEST_LENGTH);
//	for(i=0; i<gPubKey->T; i++) {
	for(i=0; i<1; i++) {
		sign[i] = malloc(sizeof(struct FwSecSigSign));
		allocSign(sign[i]);

		message[i] = BN_new();
		
		RAND_bytes(tempMsg, SHA_DIGEST_LENGTH);
		BN_bin2bn(tempMsg, SHA_DIGEST_LENGTH, message[i]);
	}

	start = clock();

	// sign and update
//	for(i=0; i<gPubKey->T; i++) {
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
			printf("sign[%d] is invalid\n", i);
		}
	}
	end = clock();
	printf("Verification: %f\t", (float)(end-start)/CLOCKS_PER_SEC);

	BN_free(phi);

    int x = 0;
    x += BN_num_bytes(gPubKey->U);
    x += BN_num_bytes(gPubKey->N);
    x += sizeof(int);

    int y = 0;
    y += sizeof(int);
    y += BN_num_bytes(gPriKey->g);
    y += BN_num_bytes(gPriKey->X);
    y += BN_num_bytes(gPriKey->S);

    printf("Pub size: %d\n", x);
    printf("Pri size: %d\n", y);
    printf("sign size: %d\n", BN_num_bytes(sign[0]->Z)+BN_num_bytes(sign[0]->sigma)+sizeof(int));
}
