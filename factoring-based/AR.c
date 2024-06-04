// Asiacrypto 2000 version

#include <openssl/rsa.h>
#include <openssl/rand.h>
#include <openssl/bn.h>
#include <openssl/sha.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
FILE* file;

#define l 160

struct FwSecSigPubKey {
	int T;
	BIGNUM* U;
	BIGNUM* N;
}* gPubKey;

struct FwSecSigPriKey {
	int i;
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
	gPriKey->S = BN_new();
}
	

void hash(BIGNUM* r, int a, BIGNUM* b, BIGNUM* c)
{
	clock_t start, end;
	char hash_digest[SHA_DIGEST_LENGTH];
	char temp[2048];

//	start = clock();
	SHA_CTX sha_ctx;
	SHA1_Init(&sha_ctx);

	sprintf(temp,"%x",a);
	SHA1_Update(&sha_ctx, temp, strlen(temp));

	BN_bn2bin(b, temp);
	SHA1_Update(&sha_ctx, temp, BN_num_bytes(b));

	BN_bn2bin(c, temp);
	SHA1_Update(&sha_ctx, temp, BN_num_bytes(c));

	SHA1_Final(hash_digest, &sha_ctx);

//	end = clock();

	BN_bin2bn(hash_digest, l/8, r);

//	printf("hash %f\n", (float)(end-start)/CLOCKS_PER_SEC);
}

// sign
void hash_exp_mul(BIGNUM* sign, BIGNUM* r, BIGNUM* x, int i, BIGNUM* m, BIGNUM* R)
{
	BIGNUM* c = BN_new();
	hash(c, i, m, R);

	BIGNUM* t1 = BN_new();
	BN_mod_exp(t1, x, c, gPubKey->N, ctx); 
	BN_mod_mul(sign, r, t1, gPubKey->N, ctx);

	BN_free(c);
	BN_free(t1);
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

int setup()
{
	BIGNUM* t1 = BN_new();
	BIGNUM* t2 = BN_new();
	BIGNUM* t3 = BN_new();

	// key generate
/*
	RSA* rsa;

	// p,q <-- Z, N=pq

	rsa = RSA_generate_key(gRSALength, 5, NULL, NULL);
        if(RSA_check_key(rsa) != 1) {
               perror("not gnerate RSA key");
               exit(0);
	}

	BN_copy(gPubKey->N,rsa->n);
*/

	BIGNUM* p = BN_new();
    BIGNUM* q = BN_new();
	while(1) {
        BN_generate_prime_ex(p, gRSALength/2, 0, NULL, NULL, NULL); 
		if(BN_is_bit_set(p, 1)) break;
	}

	while(1) {
        BN_generate_prime_ex(q, gRSALength/2, 0, NULL, NULL, NULL);
		if(BN_is_bit_set(q, 1)) break;
	}

	BN_mul(gPubKey->N, p, q, ctx);

	// S0 <-- Z_N
	BN_rand_range(gPriKey->S, gPubKey->N);

	// U <-- 1/S^{2^{l(T+1)}}
	//BN_set_word(t2, 2);
	//BN_set_word(t3, l*(gPubKey->T+1));
	exp_twos_power(t1, gPriKey->S, l*(gPubKey->T+1));
//	multi_exp(t1, gPriKey->S, t2, t3);
	BN_mod_inverse(gPubKey->U, t1, gPubKey->N, ctx);
	
	gPriKey->i = 0;

	BN_free(t1);
	BN_free(t2);
	BN_free(t3);
	//RSA_free(rsa);
	BN_free(p);
    BN_free(q);

	return 0;
}

void signMessage(struct FwSecSigSign* sign, BIGNUM* m)
{
	BIGNUM* t1 = BN_new();
	//BIGNUM* t2 = BN_new();
	//BIGNUM* t3 = BN_new();
	clock_t start, end;

	// R <-- Z_N
	BIGNUM* R = BN_new();
	BN_rand_range(R, gPubKey->N);

	// Y <-- R^{2^{l(T+1-i)}}
	BIGNUM* Y = BN_new();
	//BN_set_word(t2,2);
	//BN_set_word(t3, l*(gPubKey->T+1-gPriKey->i));
	exp_twos_power(Y, R, l*(gPubKey->T+1 - gPriKey->i));
	//multi_exp(Y, R, t2, t3);

/*
	// debug
	fprintf(file,"Y = ");
        BN_print_fp(file, Y);
        fprintf(file,"\n");
*/

	// sigma <-- H(..)
	//BN_set_word(t1, gPriKey->i);
//	start = clock();

//	for(int i=0; i<1000; i++) 
	hash(sign->sigma, gPriKey->i, Y, m);

//	end = clock();
//	printf("hash:%f\n", (float)(end-start)/CLOCKS_PER_SEC);

	// Z <-- RS^sigma
	//start = clock();
	BN_mod_exp(t1, gPriKey->S, sign->sigma, gPubKey->N, ctx);
	//end = clock();
	//printf("hash:%f\n", (float)(end-start)/CLOCKS_PER_SEC);
	BN_mod_mul(sign->Z, R, t1, gPubKey->N, ctx);
/*
	// debug
	fprintf(file,"Z = ");
        BN_print_fp(file, sign->Z);
        fprintf(file,"\n");
*/

	sign->i = gPriKey->i;
}

void update()
{
	if(gPriKey->i == gPubKey->T-1) return;

	// update secret key
	// i++
	gPriKey->i ++;

	// S_i^{2^l}
	BIGNUM* t1 = BN_new();
	BIGNUM* t2 = BN_new();
	BIGNUM* t3 = BN_new();
	//BN_set_word(t2, 2);
	//BN_set_word(t3, l);
	exp_twos_power(t1, gPriKey->S, l);
	//multi_exp(t1, gPriKey->S,t2, t3);
	BN_copy(gPriKey->S, t1);

	BN_free(t1);
	BN_free(t2);
	BN_free(t3);
}

void allocSign(struct FwSecSigSign* sign)
{
	sign->Z = BN_new();
	sign->sigma = BN_new();
}


int verify(struct FwSecSigSign* sign, BIGNUM** m, struct FwSecSigPubKey* pubKey)
{
	BIGNUM* Y = BN_new();
	BIGNUM* t1 = BN_new();
	BIGNUM* t2 = BN_new();
	BIGNUM* t3 = BN_new();

	// Y' <-- Z^{2^{l*(T+1-i)}} U^sigma
	//BN_set_word(t2,2);
	//BN_set_word(t3, l*(pubKey->T+1-sign->i));
	exp_twos_power(t1, sign->Z, l*(pubKey->T+1-sign->i));
	//multi_exp(t1, sign->Z, t2, t3);
	BN_mod_exp(t2, pubKey->U, sign->sigma, pubKey->N, ctx);
	BN_mod_mul(Y, t1, t2, pubKey->N, ctx);

/*
	// debug
	fprintf(file,"Z^... = ");
        BN_print_fp(file, t1);
        fprintf(file,"\n");
	fprintf(file,"U^sigma = ");
        BN_print_fp(file, t2);
        fprintf(file,"\n");
*/

	// H(j,Y', M)
	//BN_set_word(t1, sign->i);
	hash(t2, sign->i, Y, m[0]);

	int flag = (BN_cmp(sign->sigma,t2)==0);

/*
	//debug
	fprintf(file,"Y' = ");
        BN_print_fp(file, Y);
        fprintf(file,"\n");
	fprintf(file,"sign->sigma = ");
        BN_print_fp(file, sign->sigma);
        fprintf(file,"\n");
	fprintf(file,"H = ");
        BN_print_fp(file, t2);
        fprintf(file,"\n");
*/

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
//	file = fopen("output.txt","w");

	gPubKey = malloc(sizeof(struct FwSecSigPubKey));
	gPriKey = malloc(sizeof(struct FwSecSigPriKey));

	initializeStructures();

	// argument : rsa_bit_length period_length hash_size
	if(argc < 3) return 0;
	gRSALength = atoi(argv[1]);	// k
	gPubKey->T = atoi(argv[2]);	// T

	//printf("%d\t", gPubKey->T);
		
	start = clock();
	setup();
	end = clock();
	printf("Setup: %f\t", (float)(end-start)/CLOCKS_PER_SEC);

	// test
	struct FwSecSigSign **sign;
	BIGNUM** message;
	//sign = malloc(sizeof(struct FwSecSigSign*)*gPubKey->T);
	//message = malloc(sizeof(BIGNUM*)*gPubKey->T);
	sign = malloc(sizeof(struct FwSecSigSign*));
	message = malloc(sizeof(BIGNUM*));

	int i;
	char* tempMsg = malloc(SHA_DIGEST_LENGTH);
	//for(i=0; i<gPubKey->T; i++) {
	for(i=0; i<1; i++) {
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
			printf("sign[%d] is invalid\n", i);
		}
	}
	end = clock();
	printf("Verification: %f\n", (float)(end-start)/CLOCKS_PER_SEC);


    int x = 0;
    x += BN_num_bytes(gPubKey->U);
    x += BN_num_bytes(gPubKey->N);
    x += sizeof(int);

    int y = 0;
    y += sizeof(int);
    y += BN_num_bytes(gPriKey->S);

    printf("Pub size: %d\n", x);
    printf("Pri size: %d\n", y);
    printf("sign size: %d\n", BN_num_bytes(sign[0]->Z)+BN_num_bytes(sign[0]->sigma)+sizeof(int));
}
