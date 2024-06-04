// Crypto 1999 version

#include <openssl/rsa.h>
#include <openssl/rand.h>
#include <openssl/bn.h>
#include <openssl/sha.h>
#include <stdio.h>
#include <time.h>
FILE* file;

#define l 160

struct FwSecSigPubKey {
	int T;
	BIGNUM* N;
	BIGNUM* U[l];
}* gPubKey;

struct FwSecSigPriKey {
	int i;
	BIGNUM* S[l];
}* gPriKey;

struct FwSecSigSign {
	int i;
	BIGNUM* Y;
	BIGNUM* Z;
};

int gRSALength;		// k

BN_CTX* ctx;

void initializeStructures()
{
	// public key
	gPubKey->N = BN_new();

	for(int i=0; i<l; i++) {
		gPubKey->U[i] = BN_new();

		// private key
		gPriKey->S[i] = BN_new();
	}
}
	

void hash(BIGNUM* r, BIGNUM* a, BIGNUM* b, BIGNUM* c)
{
	char hash_digest[SHA_DIGEST_LENGTH];
	char temp[2048];
	SHA_CTX sha_ctx;
	SHA1_Init(&sha_ctx);

	BN_bn2bin(a, temp);
	SHA1_Update(&sha_ctx, temp, BN_num_bytes(a));

	BN_bn2bin(b, temp);
	SHA1_Update(&sha_ctx, temp, BN_num_bytes(b));

	BN_bn2bin(c, temp);
	SHA1_Update(&sha_ctx, temp, BN_num_bytes(c));

	SHA1_Final(hash_digest, &sha_ctx);

	BN_bin2bn(hash_digest, l/8, r);
}

void exp_twos_power(BIGNUM* y, BIGNUM* x, int n)
{
        // y = x^(2^n)
        BIGNUM* t1 = BN_new();
        BN_copy(t1,x);
        BN_copy(y,x);

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


	for(int i=0; i<l; i++) {

		// S_i <-- Z_N
		BN_rand_range(gPriKey->S[i], gPubKey->N);

		// U_i <-- S^{2^{T+1}}
		exp_twos_power(gPubKey->U[i], gPriKey->S[i], gPubKey->T+1);
	}
	
	gPriKey->i = 0;

	BN_free(t1);
	BN_free(t2);
	BN_free(t3);
//	RSA_free(rsa);

	return 0;
}

void signMessage(struct FwSecSigSign* sign, BIGNUM* m)
{
	BIGNUM* t1 = BN_new();
	BIGNUM* t2 = BN_new();
	BIGNUM* t3 = BN_new();
	BIGNUM* t4 = BN_new();
	BIGNUM* c = BN_new();

	// R <-- Z_N
	BIGNUM* R = BN_new();
	BN_rand_range(R, gPubKey->N);

	// Y <-- R^{2^{(T+1-i)}}
	BIGNUM* Y = BN_new();
	exp_twos_power(Y, R, gPubKey->T+1-gPriKey->i);

	// c_i <-- H(..)
	BN_set_word(t1, gPriKey->i);
	hash(c, t1, Y, m);

	// Z <-- R PI S^c_i
	BN_one(t2);
	for(int i=0; i<l; i++) {
		if(BN_is_bit_set(c,i)) {
			BN_mod_mul(t1, t2, gPriKey->S[i], gPubKey->N, ctx);
			BN_copy(t2,t1);
		}
	}
	BN_mod_mul(sign->Z, R, t2, gPubKey->N, ctx);
	BN_copy(sign->Y, Y);

	sign->i = gPriKey->i;
}

void update()
{
	if(gPriKey->i == gPubKey->T) return;

	// update secret key
	// i++
	gPriKey->i ++;

	BIGNUM* t1 = BN_new();
	for(int i=0; i<l; i++) {
		BN_mod_mul(t1, gPriKey->S[i], gPriKey->S[i], gPubKey->N, ctx);
		BN_copy(gPriKey->S[i], t1);
	} 

	BN_free(t1);
}

void allocSign(struct FwSecSigSign* sign)
{
	sign->Z = BN_new();
	sign->Y = BN_new();
}


int verify(struct FwSecSigSign* sign, BIGNUM** m, struct FwSecSigPubKey* pubKey)
{
	BIGNUM* Y = BN_new();
	BIGNUM* c = BN_new();
	BIGNUM* t1 = BN_new();
	BIGNUM* t2 = BN_new();
	BIGNUM* t3 = BN_new();

	// c_i <-- H(..)
	BN_set_word(t1, sign->i);
	hash(c, t1, sign->Y, m[0]);

	// Z^{2^{(T+1-i)}}
	exp_twos_power(Y, sign->Z, gPubKey->T+1-sign->i);

	// Y* PI U^c_i
	BN_one(t2);
	for(int i=0; i<l; i++) {
		if(BN_is_bit_set(c,i)) {
			BN_mod_mul(t1, t2, pubKey->U[i], pubKey->N, ctx);
			BN_copy(t2,t1);
		}
	}

	BN_mod_mul(t1, sign->Y, t2, pubKey->N, ctx);

	int flag = (BN_cmp(Y, t1)==0);

	BN_free(Y);
	BN_free(c);
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
	sign = malloc(sizeof(struct FwSecSigSign*)*gPubKey->T);
	message = malloc(sizeof(BIGNUM*)*gPubKey->T);

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
	printf("Verification: %f\n", (float)(end-start)/CLOCKS_PER_SEC);



    int x = 0;
    x += BN_num_bytes(gPubKey->N);
    x += sizeof(int);
    for( i = 0; i < l; i++ ) {
        x += BN_num_bytes(gPubKey->U[i]);
    }

    int y = 0;
    y += sizeof(int);
    for( i = 0; i < l; i++ ) {
        y += BN_num_bytes(gPriKey->S[i]);
    }

    printf("Pub size: %d\n", x);
    printf("Pri size: %d\n", y);
    printf("sign size: %d\n", BN_num_bytes(sign[0]->Z)+BN_num_bytes(sign[0]->Y)+sizeof(int));

}
