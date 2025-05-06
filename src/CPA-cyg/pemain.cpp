/*
   Boneh & Franklin's Identity Based Encryption
   
   Set-up phase

   After this program has run the file common.ibe contains

   <Size of prime modulus in bits>
   <Prime p>
   <Prime q (divides p+1) >
   <Point P - x coordinate>
   <Point P - y coordinate>
   <Point Ppub - x coordinate>
   <Point Ppub - y coordinate>
   <Cube root of unity in Fp2 - x component >
   <Cube root of unity in Fp2 - y component >

   The file master.ibe contains

   <The master secret s>

   Requires: zzn2.cpp big.cpp zzn.cpp ecn.cpp

 */
#include <time.h>
#include <iostream>
#include<vector>
#include <fstream>
#include <cstring>
#include <thread>
#include <sstream>
using namespace std;

#include "ecn.h"
#include "zzn.h"
#include "zzn2.h"

//C++中用来告诉编译器这部分代码是C语言编写的，因此在链接时应该使用C语言的链接约定
extern "C"
{
   #include"miracl.h"
   #include"mirdef.h"
}

//2015版更新
//提供一个兼容性层,为了在不同版本的MSVC运行时库之间提供一种兼容性机制，使得旧代码能够在新版本的库中正常运行，而不需要对代码进行大量修改。
FILE* __cdecl __iob_func(unsigned i) {
    return __acrt_iob_func(i);
}

#ifdef __cplusplus
extern "C" 
#endif
//extern "C" { FILE __iob_func[3] = { *stdin,*stdout,*stderr }; }
FILE _iob[3] = {__iob_func(0)[0], __iob_func(1)[1], __iob_func(2)[2]}; 

//一个特定于Microsoft Visual C++编译器的指令，用于控制链接器的行为。它的作用是告诉链接器在链接过程中不要默认链接到libc.lib这个库。
#pragma comment(linker, "/NODEFAULTLIB:libc.lib")


#define renum 2500

#define HASH_LEN 32
#define HASH_LEN1 20   //用于求H2，因为本程序中q是160位的二进制数，而160/8=20
                                        //H2中采用sha256要求HASH_LEN1 必须是32的倍数，因此，自己将H2内部函数其改为sha-1


#define PBITS 512
#define QBITS 160

// Using SHA-256 as basic hash algorithm

//
// Define one or the other of these
//
// Which is faster depends on the I/M ratio - See imratio.c
// Roughly if I/M ratio > 16 use PROJECTIVE, otherwise use AFFINE
//

// #define AFFINE
#define PROJECTIVE

// Define this to use this idea ftp://ftp.computing.dcu.ie/pub/resources/crypto/short.pdf
// which enables denominator elimination
#define SCOTT

Miracl precision(16,0);  // increase if PBITS increases. (32,0) for 1024 bit p

/*----------------------------------------------------------------------------Tate Paring 计算所需要的函数-----------------------------------------------------*/
void extract(ECn& A,ZZn& x,ZZn& y)  //仿射坐标
{ 
    x=(A.get_point())->X;
    y=(A.get_point())->Y;
}

void extract(ECn& A,ZZn& x,ZZn& y,ZZn& z)  //射影坐标
{ 
    big t;
    x=(A.get_point())->X;
    y=(A.get_point())->Y;
    t=(A.get_point())->Z;
    if (A.get_status()!=MR_EPOINT_GENERAL) 
        z=1;
    else                                   
        z=t;
}

//
// Line from A to destination C. Let A=(x,y)
// Line Y-slope.X-c=0, through A, so intercept c=y-slope.x
// Line Y-slope.X-y+slope.x = (Y-y)-slope.(X-x) = 0
// Now evaluate at Q -> return (Qy-y)-slope.(Qx-x)
//

ZZn2 line(ECn& A, ECn& C, ZZn& slope, ZZn2& Qx, ZZn2& Qy)  //计算椭圆曲线上的点Q到A到C的直线
{ 
    ZZn2 n=Qx,w=Qy;
    ZZn x,y,z,t;
#ifdef AFFINE
    extract(A,x,y);
    n-=x; n*=slope;            // 2 ZZn muls
    w-=y; n-=w;
#endif
#ifdef PROJECTIVE
    extract(A,x,y,z);
    x*=z; t=z; z*=z; z*=t;          
    n*=z; n-=x;                // 9 ZZn muls
    w*=z; w-=y; 
    extract(C,x,y,z);
    w*=z; n*=slope; n-=w;                     
#endif
    return n;
}

#ifndef SCOTT

//
// Vertical line through point A
//

ZZn2 vertical(ECn& A,ZZn2& Qx)
{
    ZZn2 n=Qx;
    ZZn x,y,z;
#ifdef AFFINE
    extract(A,x,y);
    n-=x;
#endif
#ifdef PROJECTIVE
    extract(A,x,y,z);
    z*=z;                    
    n*=z; n-=x;                // 3 ZZn muls
#endif
    return n;
}

#endif

//
// Add A=A+B  (or A=A+A) 
// Bump up num and denom
//
// AFFINE doubling     - 12 ZZn muls, plus 1 inversion
// AFFINE adding       - 11 ZZn muls, plus 1 inversion
//
// PROJECTIVE doubling - 26 ZZn muls
// PROJECTIVE adding   - 34 ZZn muls
//


void g(ECn& A,ECn& B,ZZn2& Qx,ZZn2& Qy,ZZn2& num) 
{
    ZZn  lam,mQy;
    ZZn2 d,u;
    big ptr;
    ECn P=A;

// Evaluate line from A
    ptr=A.add(B);

#ifndef SCOTT
    if (A.iszero())   { u=vertical(P,Qx); d=1; }
    else
    {
#endif
        if (ptr==NULL)
            u=1;
        else 
        {
            lam=ptr;
            u=line(P,A,lam,Qx,Qy);
        }
#ifndef SCOTT
        d=vertical(A,Qx);
    }

    num*=(u*conj(d));    // 6 ZZn muls  
#else
// denominator elimination!
    num*=u;
#endif
}

//
// Tate Pairing 
//

BOOL fast_tate_pairing(ECn& P, ZZn2& Qx, ZZn2& Qy, Big& q, ZZn2& res) //P:生成元，Qx,Qy:椭圆曲线上的点Q的坐标，q:素数阶，res:双线性对结果
{ 
    int i,nb;
    Big n,p;
    ECn A;


// q.P = 2^17*(2^142.P +P) + P

    res=1;
    A=P;    // reset A

#ifdef SCOTT
// we can avoid last iteration..
    n=q-1;
#else
    n=q;
#endif
    nb=bits(n);

    for (i=nb-2;i>=0;i--)
    {
        res*=res;         
        g(A,A,Qx,Qy,res); 
        if (bit(n,i))
            g(A,P,Qx,Qy,res);       
    }

#ifdef SCOTT
    if (A!=-P || res.iszero()) return FALSE;
#else
    if (!A.iszero()) return FALSE;
#endif

    p=get_modulus();         // get p
    res= pow(res,(p+1)/q);   // raise to power of (p^2-1)/q
    res=conj(res)/res;
    if (res.isunity()) return FALSE;
    return TRUE;   
}


BOOL ecap(ECn& P,ECn& Q,Big& order,ZZn2& cube,ZZn2& res)  //P:生成元，Q:任意点，order:素数阶，cube:立方根，res:双线性对结果
{
     ZZn2 Qx,Qy;
     Big xx,yy;
#ifdef SCOTT
     ZZn a,b,x,y,ib,w,t1,y2,ib2;
#else
     ZZn2 lambda,ox;
#endif
     Q.get(xx,yy);
     Qx=(ZZn)xx*cube;
     Qy=(ZZn)yy;

#ifndef SCOTT
// point doubling
     lambda=(3*Qx*Qx)/(Qy+Qy);
     ox=Qx;
     Qx=lambda*lambda-(Qx+Qx);
     Qy=lambda*(ox-Qx)-Qy;
#else
 //explicit point subtraction
     Qx.get(a,b);
     y=yy;
     ib=(ZZn)1/b;

     t1=a*b*b;
     y2=y*y;
     ib2=ib*ib;
     w=y2+2*t1;
     x=-w*ib2;
     y=-y*(w+t1)*(ib2*ib);
     Qx.set(x); 
     Qy.set((ZZn)0,y);

#endif

     if (fast_tate_pairing(P,Qx,Qy,order,res)) return TRUE;
     return FALSE;
}


//
// ecap(.) function - apply distortion map
//
// Qx is in ZZn if SCOTT is defined. Qy is in ZZn if SCOTT is not defined. 
// This can be exploited for some further optimisations. 
/*----------------------------------------------------------------------------Tate Paring 计算所需要的函数-----------------------------------------------------*/


/*----------------------------------------------------------------------------相关Hash函数所需的函数-----------------------------------------------------*/
// 实现了一个将字符串哈希到小于模数 p 的大整数 Big 的函数 H1
Big H1(char *string)
{ // Hash a zero-terminated string to a number < modulus
    Big h,p;
    char s[HASH_LEN];
    int i,j; 
    sha256 sh;

    shs256_init(&sh);

    for (i=0;;i++)
    {
        if (string[i]==0) 
            break;
        shs256_process(&sh,string[i]);
    }
    shs256_hash(&sh,s);
    p=get_modulus();
	//cout<<"modulus"<<p<<endl;//自己加的查看p值的语句，通过p值可知get_modulus()调用了get_mip()函数，
	//而get_mip()得到的是当前主函数中群的阶值q.
    h=1; j=0; i=1;
    forever
    {
        h*=256; 
        if (j==HASH_LEN)  
        {h+=i++; j=0;}
        else        
            h+=s[j++];
        if (h>=p)
            break;
    }
    h%=p;
    return h;
}
   
//
// Given y, get x=(y^2-1)^(1/3) mod p (from curve equation)
// 在给定 (y) 值的情况下，
// 找到满足椭圆曲线方程 (y^2 = x^3 + 1) 的 (x) 值
//

Big getx(Big y)
{
    Big p=get_modulus();
    Big t=modmult(y+1,y-1,p);   // avoids overflow
    return pow(t,(2*p-1)/3,p);
}
 
// MapToPoint
//将一个字符串标识符（ID）映射到椭圆曲线上的一个点的过程
ECn map_to_point(char *ID)
{
    ECn Q;
    Big x0,y0=H1(ID);
 
    x0=getx(y0);

    Q.set(x0,y0);

    return Q;
}
// 假设 Miracl 提供 inverse 计算函数，或使用扩展欧几里得算法计算逆元
/*
Big invmod(const Big& a, const Big& m) {
    return a.inverse(m);
}
*/
Big gcd1(Big a, Big b, Big& x, Big& y) {
    if (b == 0) {
        x = 1;
        y = 0;
        return a;
    }
    else {
        Big g = gcd1(b, a % b, y, x);
        y -= a / b * x;
        return g;
    }
}

Big invmod(Big d, Big q) {
    Big x, y;
    Big g = gcd1(d, q, x, y);
    if (g != 1) {
        return -1; // 逆元不存在
    }
    else {
        return (x % q + q) % q; // 确保结果为正数
    }
}
Big getHashFromPoint(const ECn& pt) {
    Big X;
    // 假定 ECn::get(Big&) 可提取该点的 x 坐标，或使用其它适当的方法转换
    pt.get(X);
    return X;
}

// 辅助函数：将 ECn 点转换为字符串，此处仅提取其 x 坐标作为标识
std::string pointToString(const ECn& P) {
    Big X, Y;
    P.get(X, Y);
    std::ostringstream oss;
    oss << X;  // 或者 oss << X << "_" << Y; 根据实际需求而定
    return oss.str();
}
/*-------------------------------------------- Sign + Enc --------------------------------------------*/


// 时间陷门结构体
typedef struct TimetrapDoor {
    ECn st1;
    ECn st2;
}Timetrapdoor;

// Enc公开参数
typedef struct params {
    ECn P, P1, P2, P3, P4 ,g,h,g1,h1,g2,h2;
    ECn u[257];
    ECn v[257];
    ZZn2 e_g1_g2;
    ZZn2 e_g3_g4;
    ZZn2 e_g_g;
}params;

// PKG私钥
typedef struct sk_pkg {
    Big alpha;
    ECn sk_pkg;
}sk_pkg;

// TimeServer私钥
typedef struct sk_ts {
    Big beta;
    ECn sk_ts;
    Big s;
}sk_ts;
//11111密文结构体
typedef struct Ciphtertext {

    ZZn2 c1;              // 带有明文消息的密文
    ECn c2, c3, c4, c5;

	ZZn2 c6;             // 带有签名的密文
    ECn c7;

}Ciphtertext;

typedef struct Ciphtertext1 {

    ECn c1;              // 密文
    ZZn2 c2;
    ECn V;              // 签名

}Ciphtertext1;



// 签名结构体
typedef struct
{
    ECn X;
	Big s;
    ZZn2 es;
}SignOfMessage;

/*---------------------------------------------------------相关Hash函数所需的函数-----------------------------------------------------*/
/*---------------------------------------------------------------------------------------------------------------------主函数---------------------------------------------------------------------------------------------------*/
/*---------------------------------------------------------------------------------------------------------------------主函数---------------------------------------------------------------------------------------------------*/
/*---------------------------------------------------------------------------------------------------------------------主函数---------------------------------------------------------------------------------------------------*/
/*---------------------------------------------------------------------------------------------------------------------主函数---------------------------------------------------------------------------------------------------*/
/*---------------------------------------------------------------------------------------------------------------------主函数---------------------------------------------------------------------------------------------------*/
int main()
{

    //ofstream common("common.ibe");
    //ofstream master("master.ibe");
    // 以二进制方式打开文件  
    ofstream outputFile1("Ciphertext.ibe");
    ofstream outputFile3("Ciphertext2.ibe");
    ofstream outputFile2("St.ibe");

    // 检查文件是否成功打开  
    if (!outputFile1) {
        std::cerr << "无法打开文件!" << std::endl;
        return 1; // 返回错误代码  
    }
    // 检查文件是否成功打开  
    if (!outputFile2) {
        std::cerr << "无法打开文件!" << std::endl;
        return 1; // 返回错误代码  
    }


    ECn P, Q, R, Ppub, Qid;                    //Ppub:Master Public Key, Qid:Identity Public Key P:生成元，Q:任意点，R:中间变量
    ZZn2 Qx, Qy, gid, gid1, cube, w;//自加     //gid:双线性对结果，gid1:双线性对结果，cube:立方根，w:幂运算结果 Qx,Qy:椭圆曲线上的点Q的坐标
    Big px, py, qx, qy, ab, r1;//自加         //px,py:椭圆曲线上的点P的坐标，qx,qy:椭圆曲线上的点Q的坐标，ab:椭圆曲线上的点Qid的坐标，r1:哈希值
    int i, tag;//自加 

    Big a, b, c, d1, d2, p, q, t, n, cof, x, y;  //a:私钥，b:私钥，c:私钥，d1:私钥，d2:私钥，p:素数p，q:素数q，t:素数阶，n:随机数，cof:系数，x:椭圆曲线上的点的坐标，y:椭圆曲线上的点的坐标
    big x1, y1, x2, y2;                          //x1,y1:椭圆曲线上的点的坐标，x2,y2:椭圆曲线上的点的坐标
    long seed;                                   //seed:随机数种子
    char pad[HASH_LEN1];//自加                   //pad:哈希值
    //char pad[20]={0};
    clock_t start_time, end_time;
    float t_dec;
    ZZn2 g0;
	Big m1, m2, m3;                             	//m1:明文，m2:明文，m3:明文
    params params;
	ECn QtTimeToBeDec, QtTimeNow;
    Big fid;
    SignOfMessage m1_sign, m2_sign, m3_sign;
    sk_pkg sk_pkg;
    sk_ts sk_ts;

    TimetrapDoor st_TimeNow;
    Ciphtertext CT1, CT2, CT3;
    Ciphtertext1 CT1111;

    /*------------------------------------------------Enc+Sign变量定义---------------------------------------------------------------*/
    char Alice[100] = "Alice@email.com";
    char Bob[100] = "Bob@@email.com";
    char TimeToBeDec[9] = "20241212";
    char TimeNow[9] = "20241212";


    /*---------------------------------------------------------TS----------------------------------------------*/
    miracl* mip = &precision;                    //miracl* mip:精度

    cout << "由于有些基本操作耗时不足1毫秒，所有基本操作都将重复执行" << renum << "次 " << endl;
    cout << "Enter 9 digit random number seed  = ";
    cin >> seed;
    irand(seed);

    // SET-UP
    /*-------------------------------------------------------------产生素数阶q-------------------------------------------------------------------------*/
    q = pow((Big)2, 159) + pow((Big)2, 17) + 1; 

    cout << "q= " << q << endl;

/*--------------------------------------------------------------产生素数p-------------------------------------------------------------------------*/
    t = (pow((Big)2, PBITS) - 1) / (2 * q);
    a = (pow((Big)2, PBITS - 1) - 1) / (2 * q);
    forever
    {
        n = rand(t);
        if (n < a) continue;
        p = 2 * n * q - 1;
        if (p % 24 != 11) continue;  // must be 2 mod 3, also 3 mod 8
        if (prime(p)) break;
    }

    cof = 2 * n;  //椭圆曲线余因子

    ecurve(0, 1, p, MR_PROJECTIVE);    // elliptic curve y^2=x^3+1 mod p，射影坐标系统

   
    forever
    {
            cube = pow(randn2(),(p + 1) / 3); 
            cube = pow(cube,p - 1);
            if (!cube.isunity()) break;  
    }

    cout << "Cube root of unity= " << cube << endl;

    if (!(cube * cube * cube).isunity())
    {
        cout << "sanity check failed" << endl;
        exit(0);
    }
    
    /*---------------------------------------------------------生成公开参数params----------------------------------------------*/
    //产生椭圆曲线上生成元g
    forever
    {
        while (!params.g.set(randn()));
        params.g *= cof;
        if (!params.g.iszero()) break;
    }


    //产生椭圆曲线上生成元h
    forever
    {
        while (!params.h.set(randn()));
        params.h *= cof;
        if (!params.h.iszero()) {
			cout << "685" << params.h << endl;
            break;
        }
    }
    /*---------------------------------------------------------PKISI----------------------------------------------*/

    cout << "由于有些基本操作耗时不足1毫秒，所有基本操作都将重复执行" << renum << "次 " << endl;
    cout << "Enter 9 digit random number seed  = ";
    cin >> seed;
    irand(seed);

    // SET-UP
    /*-------------------------------------------------------------产生素数阶q-------------------------------------------------------------------------*/
    q = pow((Big)2, 159) + pow((Big)2, 17) + 1;

    cout << "q= " << q << endl;

    /*--------------------------------------------------------------产生素数p-------------------------------------------------------------------------*/
    t = (pow((Big)2, PBITS) - 1) / (2 * q);
    a = (pow((Big)2, PBITS - 1) - 1) / (2 * q);
    forever
    {
        n = rand(t);
        if (n < a) continue;
        p = 2 * n * q - 1;
        if (p % 24 != 11) continue;  // must be 2 mod 3, also 3 mod 8
        if (prime(p)) break;
    }

    cof = 2 * n;  //椭圆曲线余因子

    ecurve(0, 1, p, MR_PROJECTIVE);    // elliptic curve y^2=x^3+1 mod p，射影坐标系统


    forever
    {
            cube = pow(randn2(),(p + 1) / 3);
            cube = pow(cube,p - 1);
            if (!cube.isunity()) break;
    }

    cout << "Cube root of unity= " << cube << endl;

    if (!(cube * cube * cube).isunity())
    {
        cout << "sanity check failed" << endl;
        exit(0);
    }

    /*---------------------------------------------------------生成公开参数params----------------------------------------------*/

    //产生椭圆曲线上生成元g
    forever
    {
        while (!params.g2.set(randn()));
        params.g2 *= cof;
        if (!params.g2.iszero()) break;
    }

    //产生椭圆曲线上生成元h
    forever
    {
        while (!params.h2.set(randn()));
        params.h2 *= cof;
        if (!params.h2.iszero()) break;
    }
    sk_pkg.alpha = rand(q);

    cout << "sk_pkg.alpha= " << sk_pkg.alpha << endl;

    params.g1 = sk_pkg.alpha * params.g;

    // ======================= PKISI KeyGen 部分 ============================

    vector<string> userIDs;
    for (int j = 0; j < 257; j++) {
        string id = "用户" + to_string(j); // 直接生成用户 ID，如 "用户0", "用户1", ...
        userIDs.push_back(id);
    }

    // 计算每个用户的公钥 upk_j = H1(ID_j)
    vector<Big> upks;
    for (int j = 0; j < 257; j++) {
        Big H_ID = H1((char*)userIDs[j].c_str());
        upks.push_back(H_ID);
    }

    // 检查是否存在 α = H1(ID_j)
    bool conflict = false;
    for (int j = 0; j < 257; j++) {
        if (upks[j] == sk_pkg.alpha) {
            conflict = true;
            break;
        }
    }
    if (conflict) {
        cout << "检测到 α = H1(ID)，系统将重新生成参数和所有用户的私钥。" << endl;
        // 重新生成 sk_pkg.alpha，并更新公钥 params.g1
        sk_pkg.alpha = rand(q);
        params.g1 = sk_pkg.alpha * params.g;
    }

    // 计算私钥 usk_j = (r, K)
    for (int j = 0; j < 257; j++) {
        cout << "-----------------------" << endl;
        cout << "处理用户 " << userIDs[j] << " ..." << endl;

        // 计算 H1(ID_j)
        Big userH = upks[j];

        // 计算分母 d = (α - H1(ID_j)) mod q，确保为正
        Big d = sk_pkg.alpha - userH;
        if (d < 0) d += q;
        if (d == 0) {
            cout << "错误：用户 " << userIDs[j] << " 出现 α = H1(ID)，无法计算私钥！" << endl;
            exit(0);
        }

        // 计算 d 在 Z_q 中的逆元
        Big d_inv = invmod(d, q);

        // 随机选择 r ∈ Z_p*，确保 r ≠ 0
        Big r;
        do {
            r = rand(p);
        } while (r == 0);

        // 计算 h - r*g
        ECn tmp = params.h;
        ECn tmp2 = params.g;
        tmp2 *= r;
        tmp -= tmp2;

        // 计算 K = (h - r*g) * d_inv
        ECn K = tmp;
        K *= d_inv;

        // 私钥分发（此处仅模拟）
        cout << "用户 " << userIDs[j] << " 的私钥已生成：" << endl;
        cout << "    r = " << r << endl;
        cout << "    K = " << K << endl;
        cout << "私钥已通过安全信道发送给用户 " << userIDs[j] << endl;
    }

    // ===============================================================
    cout << "PKISI 用户私钥生成完成！" << endl;
    sk_ts.s = rand(q);

    cout << "sk_ts.s= " << sk_ts.s << endl;

    params.g1 = sk_ts.s * params.g;
    Big k1= rand(q);
    Big k2 = rand(q);





    // -----------------------------------------
// 加密过程：计算密文 (c1, c2, c3, c4, c5)
// 其中使用自定义的配对函数 ecap 完成配对计算

    // --------------------- 计算 c2 ---------------------
    ecap(params.g, params.g, q, cube, params.e_g_g);
    // 计算 c2 = (e(g, g))^(k1)
    ZZn2 c2 = pow(params.e_g_g, k1);


    // --------------------- 计算 c1 ---------------------
    // 定义时间戳字符串 T，并计算 H(T)（这里使用 H1() 函数进行哈希，输出 Big 类型）
    char T[9] = "20241212";
    Big hashT = H1(T);
    cout << hashT << endl;

    // 计算 c1 = k1*g1 - k1*H(T)*g
    ECn c1 = params.g1;
    c1 *= k1;
    ECn tmp = params.g;

    // 先计算 k1 * hashT 的乘积，存入中间变量
    Big scalar = k1 * hashT;
    tmp *= scalar;  // 使用中间变量进行点的标量乘法

    c1 -= tmp;


    // --------------------- 计算 c3 ---------------------
    // 定义时间服务器身份标识 ID_s，并计算 H(ID_s)
// 对于身份标识，现在使用前面 257 个点中 u[0]。将 u[0] 转换为字符串表示
    std::string idStr = pointToString(params.u[0]);
    Big hashID = H1((char*)idStr.c_str());

    // 计算 c3 = k2*g1 - k2*H(ID_s)*g
    ECn c3 = params.g1;
    c3 *= k2;
    tmp = params.g;
    tmp *= (k2 * hashID);
    c3 -= tmp;

    // --------------------- 计算 c4 ---------------------
    // 针对 u[0]对应的身份，随机生成一个 r_id_s 用于 c4
    Big r_id_s = rand(q);
    // 计算 c4 = (e(g, g))^(k2 * r_id_s)
    // 这里继续沿用之前计算的 base1，即 e(g, g)
    ZZn2 c4 = pow(params.e_g_g, k2 * r_id_s);

    // --------------------- 计算 c5 ---------------------
    // 计算配对 e(g, h) 使用 ecap 替换 pairing(params.g, params.h)
    ZZn2 pairing_gh;
    if (!ecap(params.g, params.h, q, cube, pairing_gh))
    {
        cout << "Error computing ecap(params.g, params.h)" << endl;
        exit(1);
    }

    // 获取待加密消息 M，并通过 hash_to_GT() 映射到目标群内（类型为 ZZn2）
    ZZn2 M_GT = 123;  // 假设 hash_to_GT() 根据输入字符串生成 ZZn2 元素

    // 计算 c5 = M * (e(g, h))^-(k1+k2)
    Big exp = k1 + k2;
    ZZn2 factor = pow(pairing_gh, exp);
    factor = inverse(factor);  // 得到 (e(g, h))^-(k1+k2)
    ZZn2 c5 = M_GT * factor;

    // -----------------------------------------
    // 输出密文各部分
    cout << "加密后的密文为:" << endl;
    cout << "c1 = " << c1 << endl;  // 椭圆曲线上的点类型 ECn
    cout << "c2 = " << c2 << endl;  // 目标群 ZZn2 类型
    cout << "c3 = " << c3 << endl;
    cout << "c4 = " << c4 << endl;
    cout << "c5 = " << c5 << endl;


    return 0;


















    

    // 将结构体写入文件  
    outputFile1.write(reinterpret_cast<char*>(&CT3), sizeof(CT3));

    outputFile1.close(); // 关闭文件  
    std::cout << "结构体已成功写入文件1" << std::endl;

    // 将结构体写入文件  
    outputFile2.write(reinterpret_cast<char*>(&st_TimeNow), sizeof(st_TimeNow));

    outputFile2.close(); // 关闭文件  
    std::cout << "结构体已成功写入文件1" << std::endl;

    // 将结构体写入文件  
    outputFile3.write(reinterpret_cast<char*>(&CT1111), sizeof(CT1111));

    outputFile3.close(); // 关闭文件  
    std::cout << "结构体已成功写入文件1" << std::endl;



    //return 0;
}


	