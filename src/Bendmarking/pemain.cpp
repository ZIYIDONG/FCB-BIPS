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
#include <fstream>
#include <cstring>
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


#define renum 1000

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

//这段代码实现了一个将 Fp2 元素哈希到一个 n 字节字符串的函数 H2。这个函数的目的是将 Fp2 域中的元素映射到一个固定长度的字符串
//这个函数的主要作用是将 Fp2 域中的元素通过 SHA-1 哈希算法转换为一个固定长度的字符串
int H2(ZZn2 x,char *s)
{ // Hash an Fp2 to an n-byte string s[.]. Return n
   sha sh;
    Big a,b;
    int m;

    shs_init(&sh);
    x.get(a,b);

    while (a>0)
    {
        m=a%160;
        shs_process(&sh,m);
        a/=160;
    }
    while (b>0)
    {
        m=b%160;
        shs_process(&sh,m);
        b/=160;
    }
    shs_hash(&sh,s);

  return HASH_LEN1;
	/*sha256 sh;
    Big a,b;
    int m;

    shs256_init(&sh);
    x.get(a,b);

    while (a>0)
    {
        m=a%256;
        shs256_process(&sh,m);
        a/=256;
    }
    while (b>0)
    {
        m=b%256;
        shs256_process(&sh,m);
        b/=256;
    }
    shs256_hash(&sh,s);

  return HASH_LEN1;
	// return 20;*/
}

// 这段代码实现了一个将零终止字符串哈希到小于给定模数 qm 的大整数 Big 的函数 H3，
// 这个函数的主要作用是将输入的字符串通过 SHA-1 哈希算法转换为一个固定长度的哈希值，
// 然后将这个哈希值映射到一个大整数，并确保这个大整数小于给定的模数 qm
Big H3(char *string,Big qm)
{ // Hash a zero-terminated string to a number < modulus q
    Big h;
    char s[HASH_LEN1];
    int i,j; 
    sha sh;

    shs_init(&sh);

    for (i=0;;i++)
    {
        if (string[i]==0) break;
        shs_process(&sh,string[i]);
    }
    shs_hash(&sh,s);
    //q=get_modulus();
	//cout<<"modulus"<<p<<endl;//自己加的查看p值的语句，通过p值可知get_modulus()得到了椭圆曲线所在有限域的素数P
    h=1; j=0; i=1;
    forever
    {
        h*=160; 
        if (j==HASH_LEN1)  
        {h+=i++; j=0;}
        else        
            h+=s[j++];
        if (h>=qm) break;
    }
    h%=qm;
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
 
//
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
/*----------------------------------------------------------------------------相关Hash函数所需的函数-----------------------------------------------------*/
/*---------------------------------------------------------------------------------------------------------------------主函数---------------------------------------------------------------------------------------------------*/
/*---------------------------------------------------------------------------------------------------------------------主函数---------------------------------------------------------------------------------------------------*/
/*---------------------------------------------------------------------------------------------------------------------主函数---------------------------------------------------------------------------------------------------*/
/*---------------------------------------------------------------------------------------------------------------------主函数---------------------------------------------------------------------------------------------------*/
/*---------------------------------------------------------------------------------------------------------------------主函数---------------------------------------------------------------------------------------------------*/
int main()
{
    ofstream common("common.ibe");
    ofstream master("master.ibe");
    //ECn P,Ppub;
    ECn P,Q, R, Ppub, Qid;                    //Ppub:Master Public Key, Qid:Identity Public Key P:生成元，Q:任意点，R:中间变量
    //ZZn px,py;//自加，定义的是点的x,y坐标
    ZZn2 Qx, Qy, gid, gid1, cube, w;//自加     //gid:双线性对结果，gid1:双线性对结果，cube:立方根，w:幂运算结果 Qx,Qy:椭圆曲线上的点Q的坐标
   // Big xx,yy,ab,r1;//自加
    Big px, py, qx, qy, ab, r1;//自加         //px,py:椭圆曲线上的点P的坐标，qx,qy:椭圆曲线上的点Q的坐标，ab:椭圆曲线上的点Qid的坐标，r1:哈希值
    int i, tag;//自加                         //i:循环变量，tag:标志位
   // float t1,t_sub,t2,t_div,t3,t4,t5,t_ecsub,t6,t7,t8,t9,t10,t11,t_div_G2,t_comp;//自加
    float t1, t_sub, t2, t_div, t3, t33, t4, t5, t_ecsub, t6, t7, t8, t88, t9, t10, t11, t_div_G2, t_comp, t_G1_xor;//自加  //:素数阶，t1:哈希值计算时间，t_sub:点减运算时间，t2:点加运算时间，t_div:模除运算时间，t3:模乘运算时间，t4:点乘运算时间，t5:点加运算时间，t_ecsub:点减运算时间，t6:双线性对运算时间，t7:幂运算时间，t8:map_to_point,即H2:G2--->G1计算时间，t9:H2:G2--->{0,1}^logp计算时间，t10:H:{0,1}^*--->Z^*_q计算时间，t11:模乘运算in G2：gid*gid1 计算时间，t_div_G2:模除运算in G2：gid1/gid 计算时间，t_comp:测试ZZn2上的运算是否是模运算
   // ZZn2 cube;
   // Big s,p,q,t,n,cof,x,y;
    Big a, b, c, d1, d2,d22, p, q, t, n, cof, x, y;  //a:私钥，b:私钥，c:私钥，d1:私钥，d2:私钥，p:素数p，q:素数q，t:素数阶，n:随机数，cof:系数，x:椭圆曲线上的点的坐标，y:椭圆曲线上的点的坐标
    big x1, y1, x2, y2;                          //x1,y1:椭圆曲线上的点的坐标，x2,y2:椭圆曲线上的点的坐标
    long seed;                                   //seed:随机数种子
    char pad[HASH_LEN1];//自加                   //pad:哈希值
    //char pad[20]={0};

    Big mmm,nnn;


    miracl* mip = &precision;                    //miracl* mip:精度

    cout << "由于有些基本操作耗时不足1毫秒，所有基本操作都将重复执行" << renum << "次 " << endl;
    cout << "Enter 9 digit random number seed  = ";
    cin >> seed;
    irand(seed);

    // SET-UP
    /*-------------------------------------------------------------产生素数阶q-------------------------------------------------------------------------*/
    q = pow((Big)2, 159) + pow((Big)2, 17) + 1; 
    //  q=pow((Big)2,160)-pow((Big)2,76)-1;



    cout << "q= " << q << endl;
    //int logq=bits(q);//计算q的二进制位数，这里是160
    //	cout << "log q= " << logq << endl;

/*--------------------------------------------------------------产生素数p-------------------------------------------------------------------------*/
//generate p
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

    // Find suitable cube root of unity (solution in Fp2 of x^3=1 mod p)
   
    forever
    {
        //  cube=pow(randn2(),(p+1)*(p-1)/3);
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

    /*
    mmm = rand(q);
    nnn = rand(q);
    cout << "mmm:::" << mmm  << endl;
    cout << endl;
    cout << "nnn:::" << nnn << endl;
    cout << endl;
    cout << "mmm + nnn:::" << mmm + nnn << endl;
    cout << endl;
    cout << "q:::" << q << endl;
    cout << endl;
    cout << "p:::" << p << endl;
    cout << endl;
    cout << "1/(mmm+nnn):::" << inverse(mmm + nnn, p) << endl;
    cout << endl;
    cout << "1/mmm * mmm:::" << ( inverse(mmm + nnn, p) * ( mmm + nnn) ) % p << endl;
    cout << endl;
    */



    //
    // Choosing an arbitrary P ....
    /*-------------------------------------------------------------产生椭圆曲线上任意点P（生成元）-------------------------------------------------------------------------*/
    forever
    {
        while (!P.set(randn()));
        P *= cof;
        if (!P.iszero()) break;
    }

    // cout << "Point P= " << P << endl; //
    cout << "生成元P=" << P << endl;

    //
        // Choosing an arbitrary Q ....
    /*-------------------------------------------------------------产生椭圆曲线上任意点Q-------------------------------------------------------------------------*/
    forever
    {
        while (!Q.set(randn()));
        Q *= cof;
        if (!Q.iszero()) break;
    }

    cout << "Point Q= " << Q << endl; //

 //
 // Pick a random master key s (s被改成了a)
    a = rand(q);
    b = rand(q);
    cout << "a= " << a << endl;
    cout << "b= " << b << endl;


    /*_________________________测试异或结果是否正确，经测试异或结果是正确的，-----*/
        /*P.get(px,py);
        Q.get(qx,qy);
        ecn_xor(px,py,qx,qy);


          cout << "Point R= (" << qx<<"," <<qy<<")"<< endl;
          ecn_xor(px,py,qx,qy);
         // P.get(xx,yy);
         // R.set(qx,qy);
         // P=Q^R;
          cout << "Point R= (" << qx<<"," <<qy<<")"<< endl;
          R.set(qx,qy);
        cout << "Point P= " << R << endl;
        R.get(qx,qy);
         cout << "Point R= (" << qx<<"," <<qy<<")"<< endl;

    /*---------------------------------------------------------------------- ----------------------------------------------------------------------------*/
    clock_t start_time, end_time;

    /*----------------------------------------------------------------------点加运算：P+Q----------------------------------------------------------------------------*/
      // clock_t start_time,end_time;
    cout << "Q= " << Q << endl;
    R = Q;
    start_time = clock();
    for (i = 1; i < renum; i++)
        P + R;//P+R,即R=P+R，相当于R=P+Q；
    end_time = clock();
    t5 = end_time - start_time;
    cout << "P+Q计算时间为：" << t5 << "毫秒" << endl;
    //ecurve_mult(a,P,Ppub);//此IBE例子重新定义了大整数Big类，miracl提供的大整数类型big作为了Big类里面的数据类型
   // cout << "Secret a= " <<a << endl;
    cout << "点加运算P+Q= " << R << endl;
    //cout << "Point Q= " << Q << endl;
/*----------------------------------------------------------------------点减运算：Q-P----------------------------------------------------------------------------*/
  // clock_t start_time,end_time;
    start_time = clock();
    for (i = 1; i < renum; i++)
        R - P;//R-P即R=R-P,相当于Q=R-P；
    end_time = clock();
    t_ecsub = end_time - start_time;
    cout << "Q-P计算时间为：" << t_ecsub << "毫秒" << endl;
    //ecurve_mult(a,P,Ppub);//此IBE例子重新定义了大整数Big类，miracl提供的大整数类型big作为了Big类里面的数据类型
   // cout << "Secret a= " <<a << endl;
    cout << "点减运算Q-P= " << R << endl;
    //cout << "Point Q= " << Q << endl; 
    /*----------------------------------------------------------------------点乘运算：aP----------------------------------------------------------------------------*/
  // clock_t start_time,end_time;
    //a=a/2;
    //cout << "a= " <<a << endl;
    //cout << "b= " <<b << endl;
    start_time = clock();
    for (i = 1; i < renum; i++)
        Ppub = a * P;
    end_time = clock();
    t4 = end_time - start_time;
    cout << "aP计算时间为：" << t4 << "毫秒" << endl;
    //ecurve_mult(a,P,Ppub);//此IBE例子重新定义了大整数Big类，miracl提供的大整数类型big作为了Big类里面的数据类型
   // cout << "Secret a= " <<a << endl;
    //cout << "点乘运算a*P= " << Ppub << endl;
    cout << "点乘运算a*P= " << Ppub << endl;
    R = Q;
    //cout << "R= " << R << endl;

   /*--------------点异或运算：P模2加Q,由于点异或运算效率不高，且带来实现表示的不方便（由于异或后的点很可能不在椭圆曲线上，导致系统将其值置为（0,0）），最好修改方案中的异或为点加运算，除非是不强行置（0,0）的大整数库，PBC库是否满足？----------------------------------------------------------------------------  */
       //R=P^Q;//重载^,函数中的t值被系统传出时被置为（0,0），由于t是其他两点异或的结果，因此，t很可能不在椭圆曲线上，导致输出为：Infinity，认为其是无穷远点，并将其坐标置为（0,0）。

    start_time = clock();
    for (i = 1; i < renum; i++)
    {
        P.get(px, py);
        Q.get(qx, qy);
        ecn_xor(px, py, qx, qy);
    }
    end_time = clock();
    t_G1_xor = end_time - start_time;
    cout << "P^Q计算时间为：" << t_G1_xor << "毫秒" << endl;
    cout << "P^Q= (" << qx << "," << qy << ")" << endl;
    /*ecn_xor(P,Q,xx,yy);

      cout << "Point R= (" << xx<<"," <<yy<<")"<< endl;
      R.set(xx,yy);
     // P=Q^R;
    cout << "Point P= " << R << endl;
    R.get(xx,yy);
     cout << "Point R= (" << xx<<"," <<yy<<")"<< endl;  */
     // cout<<"生成元P="<<P<<endl;//输出测试语句，经测试epoint_get(a.get_point(),px,py)是实现提取点坐标的函数，而并不是：px=(a.get_point())->X;py=(a.get_point())->Y;
/*----------------------------------------------------------------------双线性对运算：e(P,Q)----------------------------------------------------------------------------*/
 /*  //  ZZn2 Qx,Qy;
   //  Big xx,yy;
     Q=R;
     //	cout << "Point Q= " << Q << endl;
     Q.get(xx,yy);
     Qx=(ZZn)xx*cube;
     Qy=(ZZn)yy;
    //fast_tate_pairing(P,Qx,Qy,order,res);
//   clock_t start_time,end_time;*/
    start_time = clock();
    // fast_tate_pairing(P,Qx,Qy,q,gid);
    for (i = 1; i < renum; i++)
        ecap(P, Q, q, cube, gid);
    end_time = clock();
    t6 = end_time - start_time;
    cout << " e(P,Q)计算时间为：" << t6 << "毫秒" << endl;
    //  cout << "e(P,Q)= (" << gid.a<<","<<gid.b<<")" << endl;
    cout << "e(P,Q)= " << gid << endl;


    /*----------------------------------------------------------------------幂运算in G2：e(P,Q)^a----------------------------------------------------------------------------*/
       // r=rand(q);
    start_time = clock();
    for (i = 1; i < renum; i++)
        w = pow(gid, a);
    end_time = clock();
    t7 = end_time - start_time;
    cout << " gid^a(gid=e(P,Q))计算时间为：" << t7 << "毫秒" << endl;
    //  cout << "e(P,Q)= (" << gid.a<<","<<gid.b<<")" << endl;
    cout << "gid^a(gid=e(P,Q))= " << w << endl;

    /*  Big a1,b1;
      gid.get(a1,b1);
          cout << "a1 " << a1 << endl;
          cout << "b1 " << b1 << endl;*/

          /*----------------------------------------------------------------------map_to_point,即H2:G2--->G1----------------------------------------------------------*/
    char idg[320] = "51341908562371167605710158199067961877051973585785126975865952864942182692255307043887891178551779856597871073815558580774624711401650558170516227136612693897559425945196872344227925384638844402629916160447986326191069372638589347839806296896192897540804561935865359967423094257397342627225356739623783946540";
    // cout << "Enter your correspondents email address (lower case)" << endl;
    // cin.get();
    // cin.getline(id,1000);
     //get_char_g2(gid,id);
    mip->IOBASE = 10;
    start_time = clock();
    for (i = 1; i < renum; i++)
        Qid = map_to_point(idg);
    end_time = clock();
    t8 = end_time - start_time;
    cout << " map_to_point,即H2:G2--->G1计算时间为：" << t8 << "毫秒" << endl;
    cout << "H2:G2--->G1:" << Qid << endl;
    /*----------------------------------------------------------------------map_to_point,即H2:{0,1}^*--->G1----------------------------------------------------------*/
   // char id[320]="51341908562371167605710158199067961877051973585785126975865952864942182692255307043887891178551779856597871073815558580774624711401650558170516227136612693897559425945196872344227925384638844402629916160447986326191069372638589347839806296896192897540804561935865359967423094257397342627225356739623783946540";
   //cout << "Enter your correspondents email address (lower case)" << endl;
   //cin.get();
   //cin.getline(id,1000);
    //get_char_g2(gid,id);
    char id[100] = "yuanke_hhhh@163.com";
    mip->IOBASE = 10;
    start_time = clock();
    for (i = 1; i < renum; i++)
        Qid = map_to_point(id);
    end_time = clock();
    t88 = end_time - start_time;
    cout << " map_to_point,即H2:{0,1}^*--->G1计算时间为：" << t88 << "毫秒" << endl;
    cout << "H2:{0,1}^*--->G1:" << Qid << endl;
    /*----------------------------------------------------------------------Z^*_q 上的模加运算----------------------------------------------------------------------------*/

    /*--------------------------------------------------------------------H2:G2--->{0,1}^logp----------------------------------------------------------*/
    start_time = clock();
    for (i = 1; i < renum; i++)
        H2(w, pad);
    end_time = clock();
    t9 = end_time - start_time;
    cout << " H2:G2--->{0,1}^logp计算时间为：" << t9 << "毫秒" << endl;
    //cout << "H2:G2--->{0,1}^logp " << pad << endl;
/*--------------------------------------------------------------------H:{0,1}^*--->Z^*_q----------------------------------------------------------*/
    char rt[100] = "2015-11-19-08-30";
    //cout << "Enter your correspondents email address (lower case)" << endl;
   // cin.get();
   // cin.getline(id,1000);
    start_time = clock();
    for (i = 1; i < renum; i++)
        r1 = H3(rt, q);
    end_time = clock();
    t10 = end_time - start_time;
    cout << " H:{0,1}^*--->Z^*_q计算时间为：" << t10 << "毫秒" << endl;
    cout << "H1(rt) " << r1 << endl;

    /*----------------------------------------------------------------------模乘运算in G2：gid*gid1（ZZn2上重载的算数运算本身就是模运算）-------------------------------------------------------------------------*/
        //gid1=randn2(void);
    ecap(Ppub, Qid, q, cube, gid1);
    start_time = clock();
    // fast_tate_pairing(P,Qx,Qy,q,gid);
    for (i = 1; i < renum; i++)
        gid1 = gid1 * gid;
    end_time = clock();
    t11 = end_time - start_time;
    cout << "模乘运算in G2：gid*gid1 计算时间为：" << t11 << "毫秒" << endl;
    //  cout << "e(P,Q)= (" << gid.a<<","<<gid.b<<")" << endl;
    cout << "gid*gid1 = " << gid1 << endl;
    /*----------------------------------------------------------------------测试ZZn2上的运算是否是模运算----------------------------------------------------------------------------*/
      /*ecap(Ppub,Qid,q,cube,gid1);
        cout << "原始gid1= " << gid1 << endl;
        for(i=1;i<renum;i++)
            gid1=gid1*gid;
        for(i=1;i<renum;i++)
            gid1=gid1/gid;
        cout << "gid1*gid^rnum^{1/renm}= " << gid1 << endl;*/
        /*----------------------------------------------------------------------经测试ZZn2上的运算是模运算，因为gid1*gid^rnum^{1/renm}=gid1----------------------------------------------------------------------------*/
        /*----------------------------------------------------------------------模除运算in G2：gid1/gid（ZZn2上重载的算数运算本身就是模运算）-------------------------------------------------------------------------*/
            //gid1=randn2(void);
    start_time = clock();
    // fast_tate_pairing(P,Qx,Qy,q,gid);
    for (i = 1; i < renum; i++)
        gid1 = gid1 / gid;
    end_time = clock();
    t_div_G2 = end_time - start_time;
    cout << " 模除运算in G2：gid1/gid：" << t_div_G2 << "毫秒" << endl;
    //  cout << "e(P,Q)= (" << gid.a<<","<<gid.b<<")" << endl;
    cout << "gid1*gid^rnum^{1/renm}= " << gid1 << endl;


    /*-------------------------------Z^*_q 上的模加减乘除运算如果放在a*P等运算前，则程序溢出，可能的原因是：Z^*_q 上的模加减乘除运算调用了n剩余函数，使得a,b变成了n剩余类型的big 类型---------------------------------------*/
        /*比如：模加函数：9.2.27	nres_modadd

    Function:	void nres_modadd(x,y,z)
            big x,y,z;

    Module:	mrmonty.c

    Description:	Modular addition of two n-residues

    Parameters:	Three n-residue numbers x, y, and z.
            On exit z=x+y mod n, where n is the current Montgomery modulus.

    Return value:	None

    Restrictions:	Must be preceded by a call to prepare_monty. */
    /*----------------------------------------------------------------------测试两个元素in G2是否相等-------------------------------------------------------------------------*/
    start_time = clock();
    for (i = 1; i < renum; i++)
        tag = gid == gid;
    end_time = clock();
    t_comp = end_time - start_time;
    cout << "测试两个元素in G2是否相等计算时间为：" << t_comp << "毫秒" << endl;
    //  cout << "e(P,Q)= (" << gid.a<<","<<gid.b<<")" << endl;
    cout << "gid是否同gid相等，1表示相等，0表示不等： " << tag << endl;
    /*----------------------------------------------------------------------测试ZZn2上的运算是否是模运算----------------------------------------------------------------------------*/

          /* start_time=clock();
        for(i=1;i<500;i++)
            c=(a+b)%q;
        end_time=clock();
        t1=end_time-start_time;
        cout<<"a+b mod q 计算时间为："<<t1<<"毫秒"<<endl;
        cout << "a+b mod q " <<c<< endl;*/
        // clock_t start_time,end_time;
    start_time = clock();
    for (i = 1; i < renum; i++)
        c = modadd(a, b, q);
    end_time = clock();
    t1 = end_time - start_time;
    cout << "a+b mod q 计算时间为：" << t1 << "毫秒" << endl;
    cout << "a+b mod q " << c << endl;
    //modadd(const Big& b1,const Big& b2,const Big& z)
    /*----------------------------------------------------------------------Z^*_q 上的模减运算----------------------------------------------------------------------------*/

   /* start_time=clock();
    for(i=1;i<500;i++)
        c=(a+b)%q;
    end_time=clock();
    t1=end_time-start_time;
    cout<<"a+b mod q 计算时间为："<<t1<<"毫秒"<<endl;
    cout << "a+b mod q " <<c<< endl;*/
    // clock_t start_time,end_time;
    start_time = clock();
    for (i = 1; i < renum; i++)
        a = modsub(c, b, q);
    end_time = clock();
    t_sub = end_time - start_time;
    cout << "c-b mod q 计算时间为：" << t_sub << "毫秒" << endl;
    cout << "c-b mod q " << a << endl;
    //modadd(const Big& b1,const Big& b2,const Big& z)
/*----------------------------------------------------------------------Z^*_q 上的模乘运算----------------------------------------------------------------------------*/
    start_time = clock();
    for (i = 1; i < renum; i++)
        ab = modmult(a, b, q);
    end_time = clock();
    t2 = end_time - start_time;
    cout << "a*b mod q 计算时间为：" << t2 << "毫秒" << endl;
    cout << "a*b mod q " << ab << endl;
    /*----------------------------------------------------------------------Z^*_q 上的模除运算----------------------------------------------------------------------------*/
    start_time = clock();
    for (i = 1; i < renum; i++)
        d1 = moddiv(a, b, q);
    end_time = clock();
    t_div = end_time - start_time;
    cout << "a/b mod q 计算时间为：" << t_div << "毫秒" << endl;
    cout << "a/b mod q " << d1 << endl;
    /*----------------------------------------------------------------------Z^*_q 上的模逆运算----------------------------------------------------------------------------*/
    start_time = clock();
    for (i = 1; i < renum; i++)
        d2 = inverse(b, q);
    end_time = clock();
    t3 = end_time - start_time;
    cout << "1/b mod q 计算时间为：" << t3 << "毫秒" << endl;
    cout << "1/b mod q " << d2 << endl;

    /*----------------------------------------------------------------------Z^*_q 上的模逆运算----------------------------------------------------------------------------*/
    start_time = clock();
    for (i = 1; i < renum; i++)
        d22 = pow(b,q,q);
    end_time = clock();
    t33 = end_time - start_time;
    cout << "b^q mod p 计算时间为：" << t33 << "毫秒" << endl;
    cout << "b^q mod p " << d22 << endl;

    /*----------------------------------------------------------------------Z^*_q 上的模除转化为模逆模乘运算a/b=a*(1/b),运算计时表明，这种方法用时大概是直接使用模除函数的耗时的125%（循环执行300次以上），也许是赋值稍多的原因----------------------------------------------------------------------------*/
   /* start_time=clock();
    for(i=1;i<renum;i++)
       { d2= inverse(b,q);
         d1=modmult(a,d2,q);}
    end_time=clock();
    t1=end_time-start_time;
    cout<<"a/b=a*(1/b) mod q 计算时间为："<<t1<<"毫秒"<<endl;
    cout << "1/a mod q " <<d2<< endl;
    cout << "Point P= " << P << endl;
    cout << "Point Q= " << Q << endl; */


    /*-------------------------------------------------各基本操作相对于点乘运算的计算时间比重------------------------------------------------------*/
    t1 = t1 / t4;
    cout << "Z^*_q 上的模加a+b mod q耗时比重: " << t1 << endl;
    t_sub = t_sub / t4;
    cout << "Z^*_q 上的模减a-b mod q耗时比重: " << t_sub << endl;
    t2 = t2 / t4;
    cout << "Z^*_q 上的模乘a*b mod q耗时比重: " << t2 << endl;
    t_div = t_div / t4;
    cout << "Z^*_q 上的模除a/b mod q耗时比重: " << t_div << endl;
    t3 = t3 / t4;
    cout << "Z^*_q 上的模逆1/b mod q耗时比重: " << t3 << endl;
    t33 = t33 / t4;
    cout << "Z^*_q 上的模逆b^q mod p耗时比重: " << t33 << endl;
    //t4=t4/t4;
    cout << "点乘运算 aP 耗时比重: " << 1 << endl;
    t5 = t5 / t4;
    cout << "点加运算 P+Q=R模加耗时比重: " << t5 << endl;
    t_ecsub = t_ecsub / t4;
    cout << "点减运算 Q=R-P 模加耗时比重: " << t_ecsub << endl;
    t6 = t6 / t4;
    cout << "双线性对运算e(P,Q) 耗时比重: " << t6 << endl;
    t7 = t7 / t4;
    cout << "幂运算in G2 耗时比重: " << t7 << endl;
    t8 = t8 / t4;
    cout << "H1:G2--->G1耗时比重: " << t8 << endl;
    t88 = t88 / t4;
    cout << "H1:{0,1}^*--->G1耗时比重: " << t88 << endl;
    t9 = t9 / t4;
    cout << "H2:G2--->{0,1}^logp耗时比重: " << t9 << endl;
    t10 = t10 / t4;
    cout << " H:{0,1}^*--->Z^*_q耗时比重: " << t10 << endl;
    t11 = t11 / t4;
    cout << " 模乘运算in G2：gid*gid1 耗时比重: " << t11 << endl;
    t_div_G2 = t_div_G2 / t4;
    cout << " 模除运算in G2：gid1/gid 耗时比重: " << t_div_G2 << endl;
    t_comp = t_comp / t4;
    cout << " 测试两个元素in G2是否相等 耗时比重: " << t_comp << endl;
    t_G1_xor = t_G1_xor / t4;
    cout << " 测试两个元素in G1异或运算 耗时比重: " << t_G1_xor << endl;

    //return 0;
    int Readkey();
    int aa;
    cin >> aa;
}


	