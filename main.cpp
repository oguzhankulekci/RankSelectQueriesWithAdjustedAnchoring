//
//  main.cpp
//  rankselectAA
//
//  Created by muhammed oguzhan kulekci on 16.12.2020.
//

#include <iostream>
#include <stdlib.h>
#include <time.h>
#include <sdsl/bit_vectors.hpp>
#include <immintrin.h>
#include <bitset>
#include <bit>

using namespace std;
using namespace sdsl;

bit_vector bitmap;
rrr_vector<> rrrbitmap;


unsigned int bitmapLength = 1024*1024*32;

unsigned long long int SetBitCntIn128Bits = 16;
unsigned long long int SetBitsPerSuperblock;
unsigned int setCount=0;
unsigned int* testRankVector;
unsigned int* testSelectVector;

union packedBits{
    __uint64_t *packed64;
    unsigned char *packed8;
} rawBitStream;

#define SET3

#ifdef SET1
    unsigned long long int D = 64;
    unsigned long long int logD = 6;

    unsigned long long int K = 256;
    unsigned long long int logK = 8;

    unsigned long long int P = 64;
    unsigned long long int logP = 6;
#endif


#ifdef SET2
    unsigned long long int D = 128;
    unsigned long long int logD = 7;

    unsigned long long int K = 256;
    unsigned long long int logK = 8;

    unsigned long long int P = 64;
    unsigned long long int logP = 6;
#endif

#ifdef SET3
    unsigned long long int D = 256;
    unsigned long long int logD = 8;

    unsigned long long int K = 256;
    unsigned long long int logK = 8;

    unsigned long long int P = 64;
    unsigned long long int logP = 6;
#endif


unsigned long long int mask64[64] = {
    0x0000000000000001, 0x0000000000000003, 0x0000000000000007, 0x000000000000000F,
    0x000000000000001F, 0x000000000000003F, 0x000000000000007F, 0x00000000000000FF,
    0x00000000000001FF, 0x00000000000003FF, 0x00000000000007FF, 0x0000000000000FFF,
    0x0000000000001FFF, 0x0000000000003FFF, 0x0000000000007FFF, 0x000000000000FFFF,
    0x000000000001FFFF, 0x000000000003FFFF, 0x000000000007FFFF, 0x00000000000FFFFF,
    0x00000000001FFFFF, 0x00000000003FFFFF, 0x00000000007FFFFF, 0x0000000000FFFFFF,
    0x0000000001FFFFFF, 0x0000000003FFFFFF, 0x0000000007FFFFFF, 0x000000000FFFFFFF,
    0x000000001FFFFFFF, 0x000000003FFFFFFF, 0x000000007FFFFFFF, 0x00000000FFFFFFFF,
    0x00000001FFFFFFFF, 0x00000003FFFFFFFF, 0x00000007FFFFFFFF, 0x0000000FFFFFFFFF,
    0x0000001FFFFFFFFF, 0x0000003FFFFFFFFF, 0x0000007FFFFFFFFF, 0x000000FFFFFFFFFF,
    0x000001FFFFFFFFFF, 0x000003FFFFFFFFFF, 0x000007FFFFFFFFFF, 0x00000FFFFFFFFFFF,
    0x00001FFFFFFFFFFF, 0x00003FFFFFFFFFFF, 0x00007FFFFFFFFFFF, 0x0000FFFFFFFFFFFF,
    0x0001FFFFFFFFFFFF, 0x0003FFFFFFFFFFFF, 0x0007FFFFFFFFFFFF, 0x000FFFFFFFFFFFFF,
    0x001FFFFFFFFFFFFF, 0x003FFFFFFFFFFFFF, 0x007FFFFFFFFFFFFF, 0x00FFFFFFFFFFFFFF,
    0x01FFFFFFFFFFFFFF, 0x03FFFFFFFFFFFFFF, 0x07FFFFFFFFFFFFFF, 0x0FFFFFFFFFFFFFFF,
    0x1FFFFFFFFFFFFFFF, 0x3FFFFFFFFFFFFFFF, 0x7FFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF
};

unsigned long long int *S; // number of set bits in B[0 .. (i.D.P)-1] for i=0 to i= bitmapLength/(D*P) values
unsigned char *MR; // modular rank MR[i] for i=0 to i=bitmapLength/D
bit_vector *Nbitmap; // Nbitmap[i]=0 if observed mod K == expected mod K


unsigned long long int kthSetBitIn64BitIntP(unsigned long long int p, unsigned  int k ){
    unsigned long long int r = 1ULL << k ;
    return _tzcnt_u64(_pdep_u64(  1ULL << k   , p));
    return _pdep_u64(  1ULL << k   , p);
}

void generateBitmap(unsigned int length, unsigned int t){
    
    unsigned char byteReverseTable[256] = {
        0, 128, 64, 192, 32, 160, 96, 224, 16, 144, 80, 208, 48, 176, 112, 240,
        8, 136, 72, 200, 40, 168, 104, 232, 24, 152, 88, 216, 56, 184, 120, 248,
        4, 132, 68, 196, 36, 164, 100, 228, 20, 148, 84, 212, 52, 180, 116, 244,
        12, 140, 76, 204, 44, 172, 108, 236, 28, 156, 92, 220, 60, 188, 124, 252,
        2, 130, 66, 194, 34, 162, 98, 226, 18, 146, 82, 210, 50, 178, 114, 242,
        10, 138, 74, 202, 42, 170, 106, 234, 26, 154, 90, 218, 58, 186, 122, 250,
        6, 134, 70, 198, 38, 166, 102, 230, 22, 150, 86, 214, 54, 182, 118, 246,
        14, 142, 78, 206, 46, 174, 110, 238, 30, 158, 94, 222, 62, 190, 126, 254,
        1, 129, 65, 193, 33, 161, 97, 225, 17, 145, 81, 209, 49, 177, 113, 241,
        9, 137, 73, 201, 41, 169, 105, 233, 25, 153, 89, 217, 57, 185, 121, 249,
        5, 133, 69, 197, 37, 165, 101, 229, 21, 149, 85, 213, 53, 181, 117, 245,
        13, 141, 77, 205, 45, 173, 109, 237, 29, 157, 93, 221, 61, 189, 125, 253,
        3, 131, 67, 195, 35, 163, 99, 227, 19, 147, 83, 211, 51, 179, 115, 243,
        11, 139, 75, 203, 43, 171, 107, 235, 27, 155, 91, 219, 59, 187, 123, 251,
        7, 135, 71, 199, 39, 167, 103, 231, 23, 151, 87, 215, 55, 183, 119, 247,
        15, 143, 79, 207, 47, 175, 111, 239, 31, 159, 95, 223, 63, 191, 127, 255 };
    
    
    // t indicates the average number of set bits in 128-bits
    
    bitmap.resize(length);
    
    srand(time(NULL));
    
    unsigned char* ptr8  = &(rawBitStream.packed8[0]);
    unsigned char tmp=0;
    
    for(unsigned int i=0;i<length;i++){
        
        if ((rand() % 128)<t){
            bitmap[i] = 1;
            setCount++;
        }else
            bitmap[i] = 0;
        
        tmp = tmp*2+bitmap[i];
        
        if (((i+1)%8==0) && (i>0)){
            //cout << bitset<8>(tmp) << endl;
            *ptr8 = byteReverseTable[tmp] ;
            tmp   = 0 ;
            ptr8++ ;
        }
    }
    
    tmp = tmp << (8 - (length % 8));
    *ptr8 = byteReverseTable[tmp] ;
    
}

void preprocessAdjustedRSV2(){
    
    MR      = new unsigned char[ bitmapLength / D + 1];
    S       = new unsigned long long int[bitmapLength / ( D * P ) + 2];
    Nbitmap = new bit_vector((bitmapLength / D) + 1 , 0);
    
    unsigned long int indexMR = 0, indexS=0;
    unsigned long int setBitCount=0;
    unsigned long int exceptioncount=0, maxExceptionRun=0, tmprun=0;
    
    for(unsigned long int i=0; i < bitmapLength; i++){
        
        if (0 == (i % (D*P))){
            S[indexS] = setBitCount;
            //cout << "S:" << indexS << '\t' << S[indexS] << endl;
            indexS++;
        }

        if (1==bitmap[i]) setBitCount++;
    }
    S[indexS++] = setCount;

    setBitCount=0;
    for(unsigned long int i=0; i < bitmapLength; i++){
    
        if (0 == (i % (D*P))){
            if (tmprun>maxExceptionRun) maxExceptionRun=tmprun;
            tmprun = 0;
        }
        
        if (0 == (i % D)){
            
            unsigned long long int sid = i / (D*P);
            
            MR[indexMR] = ( setBitCount - S[sid] )  % K;
            
            unsigned long long int setbitsperblock = (S[sid+1]-S[sid]) / P ;
            
            unsigned long long int observed = ( setBitCount - S[sid] ) / K;
           
            unsigned long long int expected = ( ((indexMR ) -  (sid*P)) * setbitsperblock) / K;
            //unsigned long long int expected = (((indexMR * D) -  (sid*D*P)) / 128 * SetBitCntIn128Bits) / K;
            
            if (observed != expected){
                (*Nbitmap)[indexMR]=1;
                exceptioncount++;
                tmprun++;
            }else{
                (*Nbitmap)[indexMR] = 0;
                if (tmprun>maxExceptionRun) maxExceptionRun=tmprun;
                tmprun = 0;
            }
            
            //cout << "MR:" << indexMR << '\t' << (unsigned int) MR[indexMR] << '\t' << (*Nbitmap)[indexMR] << "\tsetbitsperblock " << setbitsperblock << endl;

            indexMR++;
        }
        
        if (1==bitmap[i]) setBitCount++;
    }
   
    
    cout <<  "bitsper128: "<< SetBitCntIn128Bits << " K: " << K << " D: " << D << " P: " << P << "\tException ratio: " << exceptioncount/ double(bitmapLength / D + 1) << "\tMax ExceptionRun: " << maxExceptionRun << endl;
        
}


unsigned long int rankAA_256V2(unsigned long long int i){
        
    unsigned long long int rank ;
    
    unsigned long long int superBlockID = i >> (logP+logD);
    unsigned long long int blockID      = i >> logD;
    unsigned long long int h = i & 255;
    
    if (h<64){
        rank = _mm_popcnt_u64(rawBitStream.packed64[(blockID<<2)] & mask64[i & 63]);
    }else if (h<128){
        rank = _mm_popcnt_u64(rawBitStream.packed64[(blockID<<2)]) + _mm_popcnt_u64(rawBitStream.packed64[(blockID<<2)+1] & mask64[i & 63]);
    }else if (h<192){
        rank = _mm_popcnt_u64(rawBitStream.packed64[(blockID<<2)]) + _mm_popcnt_u64(rawBitStream.packed64[(blockID<<2)+1]) + _mm_popcnt_u64(rawBitStream.packed64[(blockID<<2)+2] & mask64[i & 63]);
    }else{
        rank = _mm_popcnt_u64(rawBitStream.packed64[(blockID<<2)]) + _mm_popcnt_u64(rawBitStream.packed64[(blockID<<2)+1]) + _mm_popcnt_u64(rawBitStream.packed64[(blockID<<2)+2]) + _mm_popcnt_u64(rawBitStream.packed64[(blockID<<2)+3] & mask64[i & 63]);
    }
    
    //unsigned long long int innerblockRank = _mm_popcnt_u64(rawBitStream.packed64[(blockID<<2)]   & mask256[(h<<2)]) + _mm_popcnt_u64(rawBitStream.packed64[(blockID<<2)+1] & mask256[(h<<2)+1]) + _mm_popcnt_u64(rawBitStream.packed64[(blockID<<2)+2] & mask256[(h<<2)+2]) + _mm_popcnt_u64(rawBitStream.packed64[(blockID<<2)+3] & mask256[(h<<2)+3]);
    rank += S[superBlockID];
    while ((*Nbitmap)[blockID]){
        blockID--;
        rank += _mm_popcnt_u64(rawBitStream.packed64[(blockID << 2)]) + _mm_popcnt_u64(rawBitStream.packed64[(blockID << 2)+1]) + _mm_popcnt_u64(rawBitStream.packed64[(blockID << 2)+2]) + _mm_popcnt_u64(rawBitStream.packed64[(blockID << 2)+3]);
    }
    rank += MR[blockID] + (((blockID & (P-1)) * ((S[superBlockID+1]-S[superBlockID]) >> logP) ) & 0xFFFFFFFFFFFFFF00);

    return rank;
}


unsigned long int rankAA_128V2(unsigned long long int i){
        
    unsigned long long int rank ;
    
    unsigned long long int superBlockID = i >> (logP+logD);
    unsigned long long int blockID      = i >> logD;
    unsigned long long int h = i & 127;
    
    if (h<64){
        rank = _mm_popcnt_u64(rawBitStream.packed64[(blockID<<1)] & mask64[i & 63]);
    }else{
        rank = _mm_popcnt_u64(rawBitStream.packed64[(blockID<<1)]) + _mm_popcnt_u64(rawBitStream.packed64[(blockID<<1)+1] & mask64[i & 63]);
    }
    
    rank += S[superBlockID];
    while ((*Nbitmap)[blockID]){
        blockID--;
        rank += _mm_popcnt_u64(rawBitStream.packed64[(blockID << 1)]) + _mm_popcnt_u64(rawBitStream.packed64[(blockID << 1)+1]);
    }
    rank += MR[blockID] + ( ((blockID & (P-1)) * ((S[superBlockID+1]-S[superBlockID]) >> logP) ) & 0xFFFFFFFFFFFFFF00);

    return rank;
}

unsigned long int rankAA_64V2(unsigned long long int i){
        
    unsigned long long int rank ;
    unsigned long long int superBlockID = i >> (logP+logD);
    unsigned long long int blockID      = i >> logD;
    
    rank = _mm_popcnt_u64(rawBitStream.packed64[blockID] & mask64[i & 63]);
    
    rank += S[superBlockID];
    while ((*Nbitmap)[blockID]){
        blockID--;
        rank += _mm_popcnt_u64(rawBitStream.packed64[blockID]);
    }
    rank += MR[blockID] + ( ((blockID & (P-1)) * ((S[superBlockID+1]-S[superBlockID]) >> logP) ) & 0xFFFFFFFFFFFFFF00);

    return rank;
}


unsigned long long int selectAA_256(unsigned long long int i){
    
    unsigned long long int superblockID = i / SetBitsPerSuperblock;
    while (S[superblockID] >= i)  superblockID--;
    while (S[superblockID+1] < i) superblockID++; // now superblock is fixed
    
    unsigned long long int relativeblockID = (i-S[superblockID]) / (1+((S[superblockID+1] - S[superblockID]) >> logP));
    
    unsigned long long int blockID = (superblockID << logP) + relativeblockID; //expected blockID

    unsigned long long int a=0;

    while ((*Nbitmap)[blockID]) {blockID--;}
    
    unsigned long long int rank = S[superblockID] + MR[blockID] + ( ((blockID & (P-1)) * ((S[superblockID+1]-S[superblockID]) >> logP) ) & 0xFFFFFFFFFFFFFF00);
    
    if (rank>=i){
        do{
            blockID--;
            rank -= (_mm_popcnt_u64(rawBitStream.packed64[4*blockID]) + _mm_popcnt_u64(rawBitStream.packed64[4*blockID+1]) + _mm_popcnt_u64(rawBitStream.packed64[4*blockID+2]) + _mm_popcnt_u64(rawBitStream.packed64[4*blockID+3]));
        }while(rank>=i);
    }else{
        while ((a = rank + _mm_popcnt_u64(rawBitStream.packed64[4*blockID]) + _mm_popcnt_u64(rawBitStream.packed64[4*blockID+1]) + _mm_popcnt_u64(rawBitStream.packed64[4*blockID+2]) + _mm_popcnt_u64(rawBitStream.packed64[4*blockID+3]) ) < i) {
            blockID++;
            rank = a;
        }
    }
    
    a = i - rank ;
    
    if (a==0){
        if (rawBitStream.packed64[4*blockID+3])
            return (blockID >> logD) - _tzcnt_u64(rawBitStream.packed64[4*blockID+3]) - 1;
        else  if (rawBitStream.packed64[4*blockID+2)
            return (blockID >> logD) - _tzcnt_u64(rawBitStream.packed64[4*blockID+2]) - 1;
        else  if (rawBitStream.packed64[4*blockID+1)
            return (blockID >> logD) - _tzcnt_u64(rawBitStream.packed64[4*blockID+1]) - 1;
        else
            return (blockID >> logD) - _tzcnt_u64(rawBitStream.packed64[4*blockID]) - 1;
    }
    
    if (_mm_popcnt_u64(rawBitStream.packed64[4*blockID]) > a )
        return (blockID << logD) + _tzcnt_u64(_pdep_u64(  1ULL << (a-1)   , rawBitStream.packed64[4*blockID] )) ;
        
    a -= _mm_popcnt_u64(rawBitStream.packed64[4*blockID]) ;
    if (_mm_popcnt_u64(rawBitStream.packed64[4*blockID+1]) > a )
        return (blockID << logD) + 64 + _tzcnt_u64(_pdep_u64(  1ULL << (a-1)   , rawBitStream.packed64[4*blockID+1] )) ;

    
    a -= _mm_popcnt_u64(rawBitStream.packed64[4*blockID+1]) ;
    if (_mm_popcnt_u64(rawBitStream.packed64[4*blockID+2]) > a )
        return (blockID << logD) + 128 + _tzcnt_u64(_pdep_u64(  1ULL << (a-1)   , rawBitStream.packed64[4*blockID+2] )) ;

    
    a -= _mm_popcnt_u64(rawBitStream.packed64[4*blockID+2]) ;
    return (blockID << logD) + 192 + _tzcnt_u64(_pdep_u64(  1ULL << (a-1)   , rawBitStream.packed64[4*blockID+3] )) ;
    
}



unsigned long long int selectAA_128(unsigned long long int i){
    
    unsigned long long int superblockID = i / SetBitsPerSuperblock;
    while (S[superblockID] >= i)  superblockID--;
    while (S[superblockID+1] < i) superblockID++; // now superblock is fixed
    
    unsigned long long int relativeblockID = (i-S[superblockID]) / (1+((S[superblockID+1] - S[superblockID]) >> logP));
    
    unsigned long long int blockID = (superblockID << logP) + relativeblockID; //expected blockID

    unsigned long long int a=0;

    while ((*Nbitmap)[blockID]) {blockID--;}
    
    unsigned long long int rank = S[superblockID] + MR[blockID] + ( ((blockID & (P-1)) * ((S[superblockID+1]-S[superblockID]) >> logP) ) & 0xFFFFFFFFFFFFFF00);
    
    if (rank>=i){
        
        do{
            blockID--;
            rank -= (_mm_popcnt_u64(rawBitStream.packed64[2*blockID]) + _mm_popcnt_u64(rawBitStream.packed64[2*blockID+1]));
        }while (rank>=i);
    
    }else{
    
        while ((a = rank + _mm_popcnt_u64(rawBitStream.packed64[2*blockID]) + _mm_popcnt_u64(rawBitStream.packed64[2*blockID+1]) ) < i) {
            blockID++;
            rank = a;
        }
        
    }
    
    a = i - rank ;
    
    if (a==0){
        if (rawBitStream.packed64[2*blockID+1])
            return (blockID >> logD) - _tzcnt_u64(rawBitStream.packed64[2*blockID-1]) - 1;
        else
            return (blockID >> logD) - _tzcnt_u64(rawBitStream.packed64[2*blockID]) - 1;
    }
    if (_mm_popcnt_u64(rawBitStream.packed64[2*blockID]) > a )
        return (blockID << logD) + _tzcnt_u64(_pdep_u64(  1ULL << (a-1)   , rawBitStream.packed64[2*blockID] )) ;
        
    a -= _mm_popcnt_u64(rawBitStream.packed64[2*blockID]) ;
    return (blockID << logD) + 64 + _tzcnt_u64(_pdep_u64(  1ULL << (a-1)   , rawBitStream.packed64[2*blockID+1] )) ;
    
}



unsigned long long int selectAA_64(unsigned long long int i){
    
    unsigned long long int superblockID = i / SetBitsPerSuperblock;
    while (S[superblockID] >= i)  superblockID--;
    while (S[superblockID+1] < i) superblockID++; // now superblock is fixed
    
    unsigned long long int relativeblockID = (i-S[superblockID]) / (1+((S[superblockID+1] - S[superblockID]) >> logP));
    
    unsigned long long int blockID = (superblockID << logP) + relativeblockID; //expected blockID

    unsigned long long int a=0;

    while ((*Nbitmap)[blockID]) {blockID--;}
    
    unsigned long long int rank = S[superblockID] + MR[blockID] + ( ((blockID & (P-1)) * ((S[superblockID+1]-S[superblockID]) >> logP) ) & 0xFFFFFFFFFFFFFF00);
    
    if (rank>=i){
        do{
            blockID--;
            rank -= _mm_popcnt_u64(rawBitStream.packed64[blockID]);
        }while(rank>=i);
    }else{
        while ((a = rank + _mm_popcnt_u64(rawBitStream.packed64[blockID]))<i){
            blockID++;
            rank = a;
        }
    }
    
    a = i - rank ;

    if (a==0){
        return (blockID >> logD) - _tzcnt_u64(rawBitStream.packed64[blockID]) - 1;
    }
    
    return (blockID << logD) + _tzcnt_u64(_pdep_u64(  1ULL << (i-rank-1)   , rawBitStream.packed64[blockID] ));
}

int main(int argc, const char * argv[]) {

    cout << fixed ;
    cout << setprecision(3);
    
    std::chrono::high_resolution_clock::time_point start,end;

    SetBitCntIn128Bits = atoi(argv[1]);
    bitmapLength = 1 << atoi(argv[2]);
    
    rawBitStream.packed8 = new unsigned char[bitmapLength / 8  + 1 ];
    
    generateBitmap(bitmapLength, SetBitCntIn128Bits);
    SetBitsPerSuperblock = 1+(setCount / (bitmapLength / ( D * P )));
    
 /*
     {
        D = 64; SetBitCntIn128Bits = 64; K = 64; P=16;
        generateBitmap(bitmapLength, SetBitCntIn128Bits);
        preprocessAdjustedRSV2();
        
        D = 64; SetBitCntIn128Bits = 32; K = 32; P=5;
        generateBitmap(bitmapLength, SetBitCntIn128Bits);
        preprocessAdjustedRSV2();
       
        D = 64; SetBitCntIn128Bits = 16; K = 16; P=2;
        generateBitmap(bitmapLength, SetBitCntIn128Bits);
        preprocessAdjustedRSV2();
        
        D = 128; SetBitCntIn128Bits = 64; K = 128; P=32;
        generateBitmap(bitmapLength, SetBitCntIn128Bits);
        preprocessAdjustedRSV2();
        
        D = 128; SetBitCntIn128Bits = 32; K = 64; P=10;
        generateBitmap(bitmapLength, SetBitCntIn128Bits);
        preprocessAdjustedRSV2();
        
        D = 128; SetBitCntIn128Bits = 16; K = 32; P=4;
        generateBitmap(bitmapLength, SetBitCntIn128Bits);
        preprocessAdjustedRSV2();
        
        D = 256; SetBitCntIn128Bits = 64; K = 256; P=64;
        generateBitmap(bitmapLength, SetBitCntIn128Bits);
        preprocessAdjustedRSV2();
        
        D = 256; SetBitCntIn128Bits = 32; K = 128; P=20;
        generateBitmap(bitmapLength, SetBitCntIn128Bits);
        preprocessAdjustedRSV2();
        
        D = 256; SetBitCntIn128Bits = 16; K = 64; P=9;
        generateBitmap(bitmapLength, SetBitCntIn128Bits);
        preprocessAdjustedRSV2();
    }
    return 1;
    */
    
    preprocessAdjustedRSV2();
    
    std::random_device rd;     // only used once to initialise (seed) engine
    std::mt19937 rng(rd());    // random-number engine used (Mersenne-Twister in this case)

    testRankVector = new unsigned int[bitmapLength/10];
    std::uniform_int_distribution<int> uniR(1,bitmapLength-1); // guaranteed unbiased
    for(unsigned int i =0; i < bitmapLength/10 ; i++)      testRankVector[i] = uniR(rng) ;
   
    testSelectVector = new unsigned int[setCount/10];
    std::uniform_int_distribution<int> uniS(1,setCount-1); // guaranteed unbiased
    for(unsigned int i =0; i < setCount/10 ; i++)  testSelectVector[i] = uniS(rng) ;
    

    rank_support_v<1> bitmap_rankv1(&bitmap);
    rank_support_v5<> bitmap_rankv5(&bitmap);
    select_support_mcl<1> bitmap_selectmcl(&bitmap);

    bit_vector_il<> bitmapil(bitmap);
    rank_support_il<> bitmap_rankil(&bitmapil);
    select_support_il<> bitmapil_select(&bitmapil);

    rrr_vector<> rrrbitmap(bitmap) ;
    rrr_vector<>::rank_1_type rrrb_rank(&rrrbitmap);
    rrr_vector<>::select_1_type rrrb_select(&rrrbitmap);

    sd_vector<> sdbitmap(bitmap);
    sd_vector<>::rank_1_type sdb_rank(&sdbitmap);
    sd_vector<>::select_1_type sdb_sel(&sdbitmap);

    cout << "Raw bitmap size: " << size_in_bytes(bitmap)*8 << endl;
    
    unsigned long int sum=0;

    cout << "AA\t\t\tMCL\t\tIL\t\t\tRRR\t\tSD\t\t AA\t\tV1\t\tV5\t\tIL\t\tRRR\t\tSD" << endl;
    cout << "Space\tSpeed\tSpace\tSpeed\tSpace\tSpeed\tSpace\tSpeed\tSpace\tSpeed\tSpace\tSpeed\tSpace\tSpeed\tSpace\tSpeed\tSpace\tSpeed\tSpace\tSpeed\tSpace\tSpeed" << endl;

//    cout << "SELECT with AA on RAW BITMAP" << endl;
    cout << (((bitmapLength/D)+1)*9 + (((bitmapLength/D)/P)+1)*64 ) / (double)bitmapLength << '\t';
    start = std::chrono::high_resolution_clock::now();
    for(unsigned int i =0; i < setCount/10 ; i++) {
#ifdef SET1
        /*if (selectAA_64(testSelectVector[i]) != bitmap_selectmcl.select(testSelectVector[i])){
            cout << selectAA_64(testSelectVector[i]) << endl;
            cout << bitmap_selectmcl.select(testSelectVector[i]) << endl;
        }*/
        sum += selectAA_64(testSelectVector[i]);
#endif
        
#ifdef SET2
        /*if (selectAA_128(testSelectVector[i]) != bitmap_selectmcl.select(testSelectVector[i])){
            cout << selectAA_256(testSelectVector[i]) << endl;
            cout << bitmap_selectmcl.select(testSelectVector[i]) << endl;
        }*/
        sum += selectAA_128(testSelectVector[i]);
#endif
        
#ifdef SET3
        /*if (selectAA_256(testSelectVector[i]) != bitmap_selectmcl.select(testSelectVector[i])){
            cout << selectAA_256(testSelectVector[i]) << endl;
            cout << bitmap_selectmcl.select(testSelectVector[i]) << endl;
        }*/
        sum += selectAA_256(testSelectVector[i]);
#endif

    }
    end = std::chrono::high_resolution_clock::now();
    cout << std::chrono::duration_cast<std::chrono::microseconds>( end - start ).count() / double(setCount/10) << '\t' ;
//  cout << sum << endl;

    
//  cout << "SELECT with MCL on RAW BITMAP" << endl;
    cout <<  size_in_bytes(bitmap_selectmcl)*8 / (double)bitmapLength << '\t';
    start = std::chrono::high_resolution_clock::now();
    for(unsigned int i =0, sum=0; i < setCount/10 ; i++) {
        sum += bitmap_selectmcl.select(testSelectVector[i]);
    }
    end = std::chrono::high_resolution_clock::now();
    cout << std::chrono::duration_cast<std::chrono::microseconds>( end - start ).count() / double(setCount/10) << '\t' ;
//    cout << sum << endl;
    
    
//    cout << "SELECT on Interleaved BITMAP" << endl;
    cout << (size_in_bytes(bitmapil)*8 - bitmapLength) / (double)bitmapLength << '\t';
    start = std::chrono::high_resolution_clock::now();
    for(unsigned int i =0, sum=0; i < setCount/10 ; i++) {
        sum += bitmapil_select.select(testSelectVector[i]);
    }
    end = std::chrono::high_resolution_clock::now();
    cout <<  std::chrono::duration_cast<std::chrono::microseconds>( end - start ).count()/ double(setCount/10) << '\t';
//    cout << sum << endl;
    
    
//    cout << "SELECT on RRR BITMAP" << endl;
    cout <<  (long long int)(size_in_bytes(rrrbitmap)*8 - bitmapLength) / (double)bitmapLength << '\t';
    start = std::chrono::high_resolution_clock::now();
    for(unsigned int i =0, sum=0; i < setCount/10 ; i++) {
        sum += rrrb_select.select(testSelectVector[i]);
    }
    end = std::chrono::high_resolution_clock::now();
    cout << std::chrono::duration_cast<std::chrono::microseconds>( end - start ).count()  / double(setCount/10) << '\t' ;
//    cout << sum << endl;
    
    
 //   cout << "SELECT on SD BITMAP" << endl;
    cout <<  (long long int)(size_in_bytes(sdbitmap)*8 - bitmapLength) / (double)bitmapLength << '\t';
    start = std::chrono::high_resolution_clock::now();
    for(unsigned int i =0, sum=0; i < setCount/10 ; i++) {
        sum += sdb_sel.select(testSelectVector[i]);
    }
    end = std::chrono::high_resolution_clock::now();
    cout <<  std::chrono::duration_cast<std::chrono::microseconds>( end - start ).count()  / double(setCount/10) << '\t' ;
//    cout << sum << endl;
    
  
//    cout << "RANK with AA on RAW BITMAP" << endl;
    cout  << (((bitmapLength/D)+1)*9 + (((bitmapLength/D)/P)+1)*64 ) / (double)bitmapLength << '\t';
    start = std::chrono::high_resolution_clock::now();
    sum=0;
    for(unsigned int i =0; i < bitmapLength/10 ; i++) {
        
#ifdef SET1
        /*if (rankAA_64V2(testRankVector[i]-1) != bitmap_rankv1.rank(testRankVector[i])){
            cout << bitmap_rankv1.rank(testRankVector[i]) << endl;
            cout << bitmap_rankv5.rank(testRankVector[i]) << endl;
            cout << rankAA_256V2(testRankVector[i]-1) << endl;
        }*/
        sum+=rankAA_64V2(testRankVector[i]-1);
#endif
        
#ifdef SET2
        /*if (rankAA_128V2(testRankVector[i]-1) != bitmap_rankv1.rank(testRankVector[i])){
            cout << bitmap_rankv1.rank(testRankVector[i]) << endl;
            cout << bitmap_rankv5.rank(testRankVector[i]) << endl;
            cout << rankAA_256V2(testRankVector[i]-1) << endl;
        }*/
        sum+=rankAA_128V2(testRankVector[i]-1);
#endif
        
#ifdef SET3
        /*if (rankAA_256V2(testRankVector[i]-1) != bitmap_rankv1.rank(testRankVector[i])){
            cout << bitmap_rankv1.rank(testRankVector[i]) << endl;
            cout << bitmap_rankv5.rank(testRankVector[i]) << endl;
            cout << rankAA_256V2(testRankVector[i]-1) << endl;
        }*/
        sum+=rankAA_256V2(testRankVector[i]-1);
#endif
        
    }
    end = std::chrono::high_resolution_clock::now();
    cout << std::chrono::duration_cast<std::chrono::microseconds>( end - start ).count() / double(bitmapLength/10) << '\t' ;
//    cout << sum << endl;
    
    sum=0;
    //cout << "RANK with V1 on RAW BITMAP" << endl;
    cout << size_in_bytes(bitmap_rankv1)*8 / (double)bitmapLength << '\t';
    start = std::chrono::high_resolution_clock::now();
    for(unsigned int i =0; i < bitmapLength/10 ; i++) {
        sum+=bitmap_rankv1.rank(testRankVector[i]);
    }
    end = std::chrono::high_resolution_clock::now();
    cout << std::chrono::duration_cast<std::chrono::microseconds>( end - start ).count() / double(bitmapLength/10) << '\t' ;
//    cout << sum << endl;

    sum = 0;
    //cout << "RANK with V5 on RAW BITMAP" << endl;
    cout <<  size_in_bytes(bitmap_rankv5)*8 / (double)bitmapLength << '\t';
    start = std::chrono::high_resolution_clock::now();
    for(unsigned int i =0; i < bitmapLength/10 ; i++) {
        sum += bitmap_rankv5.rank(testRankVector[i]);
    }
    end = std::chrono::high_resolution_clock::now();
    cout << std::chrono::duration_cast<std::chrono::microseconds>( end - start ).count() / double(bitmapLength/10) << '\t' ;
 //   cout << sum << endl;
    
    sum = 0;
    //cout << "RANK on Interleaved BITMAP" << endl;
    cout << (size_in_bytes(bitmapil)*8 - bitmapLength) / (double)bitmapLength << '\t';
    start = std::chrono::high_resolution_clock::now();
    for(unsigned int i =0; i < bitmapLength/10 ; i++) {
        sum += bitmap_rankil.rank(testRankVector[i]);
    }
    end = std::chrono::high_resolution_clock::now();
    cout <<  std::chrono::duration_cast<std::chrono::microseconds>( end - start ).count() / double(bitmapLength/10) << '\t' ;
    //cout << sum << endl;


    sum = 0;
    //cout << "RANK on RRR BITMAP" << endl;
    cout << (long long int)(size_in_bytes(rrrbitmap)*8 - bitmapLength) / (double)bitmapLength << '\t';
    start = std::chrono::high_resolution_clock::now();
    for(unsigned int i =0; i < bitmapLength/10 ; i++) {
        sum += rrrb_rank.rank(testRankVector[i]);
    }
    end = std::chrono::high_resolution_clock::now();
    cout << std::chrono::duration_cast<std::chrono::microseconds>( end - start ).count() / double(bitmapLength/10) << '\t' ;
   // cout << sum << endl;
        
    sum = 0;
    //cout << "RANK on SD BITMAP" << endl;
    cout  << (long long int)(size_in_bytes(sdbitmap)*8 - bitmapLength)/ (double)bitmapLength << '\t';
    start = std::chrono::high_resolution_clock::now();
    for(unsigned int i =0; i < bitmapLength/10 ; i++) {
        sum += sdb_rank.rank(testRankVector[i]);
    }
    end = std::chrono::high_resolution_clock::now();
    cout <<  std::chrono::duration_cast<std::chrono::microseconds>( end - start ).count() / double(bitmapLength/10) << '\t' << endl;
    //cout << sum << endl;
    
    return 0;
}

