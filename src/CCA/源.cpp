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
#define _CRT_SECURE_NO_WARNINGS
#include <cstring> // 或其他相关头文件
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
FILE _iob[3] = { __iob_func(0)[0], __iob_func(1)[1], __iob_func(2)[2] };

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

Miracl precision(16, 0);  // increase if PBITS increases. (32,0) for 1024 bit p




/*-------------------------------------------------------------------结构体声明-------------------------------------------------------------*/
//时间服务器
typedef struct ts_g {
    Big s;
    ECn g, h;
    ZZn2 e_g1_g2;
} ts_g;
//MPK
typedef struct mpk {
    ECn g, g1, h;
} mpk;
//PKISI
typedef struct pkisi_g {
    Big s, msk;
    mpk mpk;
    ECn g, h;
    ZZn2 e_g1_g2;
} pkisi_g;
//用户私钥
typedef struct usk_j {
    Big rid_j;
    ECn kid_j;
}usk_j;
//密文
typedef struct Ciphtertext {
    ECn c1, c3, c6;
    ZZn2 c2, c4, c5, c3_;

} Ciphtertext;
typedef struct ReCiphtertext {
    Ciphtertext CT;
    ECn RK_2;
    ZZn2 c3_;
} ReCiphtertext;
//用户
typedef struct user {
    char id[20] = " ";
    Big upk;
    usk_j usk;
    ZZn2 v, w, X_, X;
    ECn u, RK;
}user;
//时间陷阱
typedef struct ts {
    Big priv;
    ECn pub;
} ts;
typedef struct ST {
    Big rT;
    ECn KT;
} ST;




/*------------------------------------相关Hash函数--------------------------------------------*/
// 实现了一个将字符串哈希到小于模数 p 的大整数 Big 的函数 H1
Big H1(char* string)
{ // Hash a zero-terminated string to a number < modulus
    Big h, p;
    char s[HASH_LEN];
    int i, j;
    sha256 sh;

    shs256_init(&sh);

    for (i = 0;; i++)
    {
        if (string[i] == 0)
            break;
        shs256_process(&sh, string[i]);
    }
    shs256_hash(&sh, s);
    p = get_modulus();
    //cout<<"modulus"<<p<<endl;//自己加的查看p值的语句，通过p值可知get_modulus()调用了get_mip()函数，
    //而get_mip()得到的是当前主函数中群的阶值q.
    h = 1; j = 0; i = 1;
    forever
    {
        h *= 256;
        if (j == HASH_LEN)
        {
h += i++; j = 0;
}
else
    h += s[j++];
if (h >= p)
    break;
    }
    h %= p;
    return h;
}

//这段代码实现了一个将 Fp2 元素哈希到一个 n 字节字符串的函数 H2。这个函数的目的是将 Fp2 域中的元素映射到一个固定长度的字符串
//这个函数的主要作用是将 Fp2 域中的元素通过 SHA-1 哈希算法转换为一个固定长度的字符串
int H2(ZZn2 x, char* s)
{ // Hash an Fp2 to an n-byte string s[.]. Return n
    sha sh;
    Big a, b;
    int m;

    shs_init(&sh);
    x.get(a, b);

    while (a > 0)
    {
        m = a % 160;
        shs_process(&sh, m);
        a /= 160;
    }
    while (b > 0)
    {
        m = b % 160;
        shs_process(&sh, m);
        b /= 160;
    }
    shs_hash(&sh, s);

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
Big H3(char* string, Big qm)
{ // Hash a zero-terminated string to a number < modulus q
    Big h;
    char s[HASH_LEN1];
    int i, j;
    sha sh;

    shs_init(&sh);

    for (i = 0;; i++)
    {
        if (string[i] == 0) break;
        shs_process(&sh, string[i]);
    }
    shs_hash(&sh, s);
    //q=get_modulus();
    //cout<<"modulus"<<p<<endl;//自己加的查看p值的语句，通过p值可知get_modulus()得到了椭圆曲线所在有限域的素数P
    h = 1; j = 0; i = 1;
    forever
    {
        h *= 160;
        if (j == HASH_LEN1)
        {
h += i++; j = 0;
}
else
    h += s[j++];
if (h >= qm) break;
    }
    h %= qm;
    return h;
}

//
// Given y, get x=(y^2-1)^(1/3) mod p (from curve equation)
// 在给定 (y) 值的情况下，
// 找到满足椭圆曲线方程 (y^2 = x^3 + 1) 的 (x) 值
//

Big getx(Big y)
{
    Big p = get_modulus();
    Big t = modmult(y + 1, y - 1, p);   // avoids overflow
    return pow(t, (2 * p - 1) / 3, p);
}

// MapToPoint
//将一个字符串标识符（ID）映射到椭圆曲线上的一个点的过程
ECn map_to_point(char* ID)
{
    ECn Q;
    Big x0, y0 = H1(ID);

    x0 = getx(y0);

    Q.set(x0, y0);

    return Q;
}
void extract(ECn& A, ZZn& x, ZZn& y, ZZn& z)  //射影坐标
{
    big t;
    x = (A.get_point())->X;
    y = (A.get_point())->Y;
    t = (A.get_point())->Z;
    if (A.get_status() != MR_EPOINT_GENERAL)
        z = 1;
    else
        z = t;
}
ZZn2 line(ECn& A, ECn& C, ZZn& slope, ZZn2& Qx, ZZn2& Qy)  //计算椭圆曲线上的点Q到A到C的直线
{
    ZZn2 n = Qx, w = Qy;
    ZZn x, y, z, t;
#ifdef AFFINE
    extract(A, x, y);
    n -= x; n *= slope;            // 2 ZZn muls
    w -= y; n -= w;
#endif
#ifdef PROJECTIVE
    extract(A, x, y, z);
    x *= z; t = z; z *= z; z *= t;
    n *= z; n -= x;                // 9 ZZn muls
    w *= z; w -= y;
    extract(C, x, y, z);
    w *= z; n *= slope; n -= w;
#endif
    return n;
}
void g(ECn& A, ECn& B, ZZn2& Qx, ZZn2& Qy, ZZn2& num)
{
    ZZn  lam, mQy;
    ZZn2 d, u;
    big ptr;
    ECn P = A;

    // Evaluate line from A
    ptr = A.add(B);

#ifndef SCOTT
    if (A.iszero()) { u = vertical(P, Qx); d = 1; }
    else
    {
#endif
        if (ptr == NULL)
            u = 1;
        else
        {
            lam = ptr;
            u = line(P, A, lam, Qx, Qy);
        }
#ifndef SCOTT
        d = vertical(A, Qx);
    }

    num *= (u * conj(d));    // 6 ZZn muls  
#else
        // denominator elimination!
        num *= u;
#endif
}

    BOOL fast_tate_pairing(ECn& P, ZZn2& Qx, ZZn2& Qy, Big& q, ZZn2& res) //P:生成元，Qx,Qy:椭圆曲线上的点Q的坐标，q:素数阶，res:双线性对结果
    {
        int i, nb;
        Big n, p;
        ECn A;


        // q.P = 2^17*(2^142.P +P) + P

        res = 1;
        A = P;    // reset A

#ifdef SCOTT
        // we can avoid last iteration..
        n = q - 1;
#else
        n = q;
#endif
        nb = bits(n);

        for (i = nb - 2; i >= 0; i--)
        {
            res *= res;
            g(A, A, Qx, Qy, res);
            if (bit(n, i))
                g(A, P, Qx, Qy, res);
        }

#ifdef SCOTT
        if (A != -P || res.iszero()) return FALSE;
#else
        if (!A.iszero()) return FALSE;
#endif

        p = get_modulus();         // get p
        res = pow(res, (p + 1) / q);   // raise to power of (p^2-1)/q
        res = conj(res) / res;
        if (res.isunity()) return FALSE;
        return TRUE;
    }
    BOOL ecap(ECn& P, ECn& Q, Big& order, ZZn2& cube, ZZn2& res) //P:生成元，Q:任意点，order:素数阶，cube:立方根，res:双线性对结果
    {
        ZZn2 Qx, Qy;
        Big xx, yy;
#ifdef SCOTT
        ZZn a, b, x, y, ib, w, t1, y2, ib2;
#else
        ZZn2 lambda, ox;
#endif
        Q.get(xx, yy);
        Qx = (ZZn)xx * cube;
        Qy = (ZZn)yy;

#ifndef SCOTT
        // point doubling
        lambda = (3 * Qx * Qx) / (Qy + Qy);
        ox = Qx;
        Qx = lambda * lambda - (Qx + Qx);
        Qy = lambda * (ox - Qx) - Qy;
#else
        //explicit point subtraction
        Qx.get(a, b);
        y = yy;
        ib = (ZZn)1 / b;

        t1 = a * b * b;
        y2 = y * y;
        ib2 = ib * ib;
        w = y2 + 2 * t1;
        x = -w * ib2;
        y = -y * (w + t1) * (ib2 * ib);
        Qx.set(x);
        Qy.set((ZZn)0, y);

#endif

        if (fast_tate_pairing(P, Qx, Qy, order, res)) return TRUE;
        return FALSE;
    }

    /*------------------------------------自定义函数--------------------------------------------*/

// 实现连接操作函数
   /*ZZn2 concatenate(const ZZn2& zzn2_obj, const ECn& ecn_obj) {
        // 获取 ECn 对象的坐标
        Big x_coord, y_coord;
        ecn_obj.getxy(x_coord, y_coord);

        // 将 ECn 的坐标转换为字节数组
        size_t x_len = x_coord.sizeinbase(256);
        size_t y_len = y_coord.sizeinbase(256);
        std::unique_ptr<unsigned char[]> x_bytes(new unsigned char[x_len]);
        std::unique_ptr<unsigned char[]> y_bytes(new unsigned char[y_len]);
        x_coord.to_bytes(x_bytes.get(), x_len);
        y_coord.to_bytes(y_bytes.get(), y_len);

        // 获取 ZZn2 对象的组成部分
        Big a, b;
        zzn2_obj.get(a, b);

        // 将 ZZn2 的组成部分转换为字节数组
        size_t a_len = a.sizeinbase(256);
        size_t b_len = b.sizeinbase(256);
        std::unique_ptr<unsigned char[]> a_bytes(new unsigned char[a_len]);
        std::unique_ptr<unsigned char[]> b_bytes(new unsigned char[b_len]);
        a.to_bytes(a_bytes.get(), a_len);
        b.to_bytes(b_bytes.get(), b_len);

        // 计算拼接后的总长度
        size_t total_len = a_len + b_len + x_len + y_len;
        std::unique_ptr<unsigned char[]> combined_bytes(new unsigned char[total_len]);

        // 拼接字节数组
        size_t index = 0;
        std::copy(a_bytes.get(), a_bytes.get() + a_len, combined_bytes.get() + index);
        index += a_len;
        std::copy(b_bytes.get(), b_bytes.get() + b_len, combined_bytes.get() + index);
        index += b_len;
        std::copy(x_bytes.get(), x_bytes.get() + x_len, combined_bytes.get() + index);
        index += x_len;
        std::copy(y_bytes.get(), y_bytes.get() + y_len, combined_bytes.get() + index);

        // 从拼接后的字节数组恢复 ZZn2 对象
        Big new_a, new_b;
        new_a.from_bytes(combined_bytes.get(), a_len);
        new_b.from_bytes(combined_bytes.get() + a_len, b_len);
        ZZn2 result;
        result.set(new_a, new_b);

        return result;
    }*/

    // 实现连接操作函数
    ZZn2 concatenate(const ZZn2& x, const ECn& RK) {
        // 获取椭圆曲线点 RK 的坐标
        Big x_coord, y_coord;
        RK.getxy(x_coord, y_coord);
        // 计算 x_coord 和 y_coord 的字节长度并转换为字节数组
        int tem_n = 9999999;
        char* ten = new char[tem_n];
        int x_len = to_binary(x_coord, tem_n, ten, TRUE);
        if (x_len == 0) {
            cerr << "Error: x_coord to_binary returned length 0." << endl;
        }
        unsigned char* x_bytes = new unsigned char[x_len];
        to_binary(x_coord, x_len, (char*)x_bytes, TRUE);

        int y_len = to_binary(y_coord, tem_n, ten, TRUE);
        if (y_len == 0) {
            cerr << "Error: y_coord to_binary returned length 0." << endl;
        }
        unsigned char* y_bytes = new unsigned char[y_len];
        to_binary(y_coord, y_len, (char*)y_bytes, TRUE);

        // 获取 ZZn2 对象 x 的分量并转换为字节数组
        Big a, b;
        x.get(a, b);

        int a_len = to_binary(a, tem_n, ten, TRUE);
        if (a_len == 0) {
            cerr << "Error: a to_binary returned length 0." << endl;
        }
        unsigned char* a_bytes = new unsigned char[a_len];
        to_binary(a, a_len, (char*)a_bytes, TRUE);

        int b_len = to_binary(b, tem_n, ten, TRUE);
        if (b_len == 0) {
            cerr << "Error: b to_binary returned length 0." << endl;
        }
        unsigned char* b_bytes = new unsigned char[b_len];
        to_binary(b, b_len, (char*)b_bytes, TRUE);

        // 连接所有字节数组
        int total_len = a_len + b_len + x_len + y_len;
        cout << "a_len: " << a_len << endl;
        cout << "b_len: " << b_len << endl;
        cout << "x_len: " << x_len << endl;
        cout << "y_len: " << y_len << endl;
        cout << "Total length: " << total_len << endl;

        unsigned char* combined_bytes = new unsigned char[total_len];
        int index = 0;

        memcpy(combined_bytes + index, a_bytes, a_len);
        index += a_len;
        memcpy(combined_bytes + index, b_bytes, b_len);
        index += b_len;
        memcpy(combined_bytes + index, x_bytes, x_len);
        index += x_len;
        memcpy(combined_bytes + index, y_bytes, y_len);

        // 调试输出拼接后的字节数组内容
        /*cout << "Combined bytes: ";
        for (int i = 0; i < total_len; i++) {
            cout << hex << (int)combined_bytes[i] << " ";
        }
        cout << endl;*/

        // 从字节数组构造新的 ZZn2 对象
        Big new_a = from_binary(a_len, (char*)combined_bytes);
        Big new_b = from_binary(b_len, (char*)(combined_bytes + a_len));
        ZZn2 result;
        result.set(new_a, new_b);

        // 释放内存
        delete[] x_bytes;
        delete[] y_bytes;
        delete[] a_bytes;
        delete[] b_bytes;
        delete[] combined_bytes;

        return result;
    }


    void KeyGen(pkisi_g& pkisi_g, user* users, int n, Big q)
    {
        for (int i = 0; i < n; i++) {
            users[i].usk.rid_j = rand(pkisi_g.s);
            cout << "user.usk.rid_j: " << users[i].usk.rid_j << endl;

            ECn tem;
            tem = users[i].usk.rid_j * (-pkisi_g.g);
            tem = tem + pkisi_g.h;
            Big tem1 = pkisi_g.msk - users[i].upk;
            tem1 = inverse(tem1, q);
            users[i].usk.kid_j = tem1 * tem;
            cout << "user.usk.kid_j: " << users[i].usk.kid_j << endl;

            if (pkisi_g.msk == users[i].upk)
            {
                pkisi_g.msk = rand(pkisi_g.s);
                pkisi_g.mpk.g1 = pkisi_g.msk * pkisi_g.mpk.g;
                i = n;
                KeyGen(pkisi_g, users, n, q);
            }
        }
    }

    void Enc(Big p, ts_g ts_g, pkisi_g pkisi_g, ECn ts_pub, char* T, Big upk_s, user user, ZZn2& e_g_g, ZZn2& e_g_h, ZZn2 m, Ciphtertext& CT, char* vk)
    {
        Big k1, k2;
        k1 = rand(p);
        cout << "k1: " << k1 << endl;
        k2 = rand(p);
        cout << "k2: " << k2 << endl;

        // 计算 c1 = k1 * mpk.g1 + (-k1 * H1(T) * g)
        ECn temp1 = k1 * pkisi_g.mpk.g1;
        cout << "temp1 (k1 * mpk.g1): " << temp1 << endl;

        Big h1 = H1(T);
        cout << "H1(T): " << h1 << endl;

        ECn temp2 = -pkisi_g.g;
        temp2 = k1 * temp2;
        temp2 = h1 * temp2;

        CT.c1 = temp1 + temp2;
        cout << "Encrypted c1: " << CT.c1 << endl;

        // 计算 c2 = e_g_g^k1
        CT.c2 = pow(e_g_g, k1);
        cout << "Encrypted c2: " << CT.c2 << endl;

        // 计算 c3 = k2 * mpk.g1 + (-k2 * H1(user.id) * g)
        ECn temp3 = k2 * pkisi_g.mpk.g1;
        cout << "temp3 (k2 * mpk.g1): " << temp3 << endl;

        Big h2 = H1(user.id);
        cout << "H1(user.id): " << h2 << endl;

        ECn temp4 = k2 * (-pkisi_g.g);
        temp4 = h2 * temp4;
        CT.c3 = temp3 + temp4;
        cout << "Encrypted c3: " << CT.c3 << endl;

        // 计算 c4 = e_g_g^(k2 * user.usk.rid_j)
        //CT.c4 = pow(e_g_g, k2 * user.usk.rid_j);
        ZZn2 tem5 = pow(e_g_g, k2);
        CT.c4 = pow(tem5, user.usk.rid_j);
        cout << "Encrypted c4: " << CT.c4 << endl;

        // 计算 c5 = m * e_g_h^(-k1) * e_g_h^(-k2)
        CT.c5 = m * pow(inverse(e_g_h), k1) * pow(inverse(e_g_h), k2);
        cout << "Encrypted c5: " << CT.c5 << endl;

        // 计算 c6 = H1(vk) * g
        CT.c6 = H1(vk) * pkisi_g.g;
        cout << "Encrypted c6: " << CT.c6 << endl;
    }
    void RKGen(Big p, Big q, ZZn2 cube, pkisi_g pkisi_g, user* receiver, user& user, int n, ZZn2& e_g_g, ZZn2& e_g_h, Ciphtertext& CT, Big cof)
    {
        ECn Q, Qrid;

        forever{
            while (true) {
                Big random_value = randn();
                cout << "Random value: " << random_value << endl;
                if (Q.set(random_value)) {
                    cout << "Q set successfully." << endl;
                    break;
                }
                //else {
                //    cout << "Failed to set Q. Retrying..." << endl;
                //}

            }
            Q *= cof;
            cout << "Q after multiplication with cof: " << Q << endl;
            if (!Q.iszero()) {
                cout << "Q is non-zero." << endl;
                break;
            }
            //else {
            //    cout << "Q is zero. Retrying..." << endl;
            //}
        }

        Qrid = user.usk.rid_j * Q;
        cout << "Qrid: " << Qrid << endl;

        user.RK = user.usk.kid_j + Qrid;
        cout << "user.RK: " << user.RK << endl;

        Big k3;
        k3 = rand(p);
        cout << "k3: " << k3 << endl;

        ZZn2 e_c3_Qrid, X;
        ecap(CT.c3, Qrid, p, cube, e_c3_Qrid);
        X = e_c3_Qrid;
        cout << "X: " << X << endl;
        user.X = X;
        //user.X_ = concatenate(X, user.RK);
        //cout << "user.X_: " << user.X_ << endl;

        /*Big hid = H1(user.id);
        cout<<"hid:"<<hid << endl;
        ECn ten1=k3 * pkisi_g.mpk.g1;
        cout << "ten1: " << ten1 << endl;
        Big ten2=( - k3)* hid;
        cout << "ten2: " << ten2 << endl;
        ECn ten3 = ten2 * pkisi_g.g;
        cout << "ten3: " << ten3 << endl;
        user.u = ten1+ten3;
        cout << "user.u: " << user.u << endl;*/
        for (int i = 0; i < n; i++) {
            //receiver[i].X_ = user.X_;
            //receiver[i].X= user.X;
            receiver[i].RK = user.RK;
            Big hid = H1(receiver[i].id);
            ECn ten1 = k3 * pkisi_g.mpk.g1;
            ECn ten2 = k3 * (-pkisi_g.g);
            ten2 = hid * ten2;
            receiver[i].u = ten1 + ten2;
            //cout << "user.u: " << user.u << endl;
            receiver[i].v = pow(e_g_g, k3);
            //cout << "user.v: " << user.v << endl;

            receiver[i].w = user.X * pow(inverse(e_g_h), k3);
            //cout << "user.w: " << user.w << endl;
        }
    }
    void ReEnc(Big p, pkisi_g pkisi_g, user user, Ciphtertext& CT, ReCiphtertext& RCT, ZZn2& cube, char* vk)
    {
        Big r;
        r = rand(p);
        Big hvk = H1(vk);
        ECn tem1 = r * pkisi_g.g;
        ECn tem2 = hvk * pkisi_g.g;
        ECn tem3 = tem1 + tem2;
        ECn RK_1 = user.RK + tem3;
        RCT.RK_2 = r * pkisi_g.g;
        ecap(CT.c3, RK_1, p, cube, CT.c3_);
        RCT.c3_ = CT.c3_;
        RCT.CT.c1 = CT.c1;
        RCT.CT.c2 = CT.c2;
        RCT.CT.c3 = CT.c3;
        RCT.CT.c4 = CT.c4;
        RCT.CT.c5 = CT.c5;
        RCT.CT.c6 = CT.c6;

    }
    void RtTrd(Big p, ts_g ts_g, ts& ts, char* T, ST& st, Big q)
    {
        st.rT = rand(p);
        st.KT = inverse((ts.priv - H1(T)), q) * (ts_g.h + st.rT * (-ts_g.g));
        while (ts.priv == H1(T))
        {
            ts.priv = rand(p);
            ts.pub = ts.priv * ts_g.g;
            st.KT = inverse((ts.priv - H1(T)), q) * (ts_g.h - st.rT * ts_g.g);
        }

    }



    void Dec1(ts_g ts_g, pkisi_g pkisi_g, user& u, ZZn2& cube) {
        ZZn2 tem;
        ecap(u.u, u.usk.kid_j, ts_g.s, cube, tem);
        tem *= pow(u.v, u.usk.rid_j);
        u.X = tem * u.w;
    }
    void Dec2(ts_g ts_g, pkisi_g pkisi_g, ST ST, user u, user s, char T[], Ciphtertext& C, ZZn2 cube, ECn RK_2) {
        ZZn2 tem2, tem3;
        ECn tem4;
        ecap(C.c3, u.RK, ts_g.s, cube, tem2);
        tem4 = C.c6 + RK_2;
        ecap(C.c3, tem4, ts_g.s, cube, tem3);
        tem2 *= tem3;
        if (C.c3_ != tem2) {
            cout << "——_____——" << endl;
            return;
        }
        ZZn2 tem, tem1;
        ecap(C.c1, ST.KT, ts_g.s, cube, tem);
        tem *= pow(C.c2, ST.rT);
        tem *= C.c3_;
        tem *= C.c4;
        tem *= C.c5;
        ECn tem5 = C.c6 + RK_2;
        ecap(C.c3, tem5, ts_g.s, cube, tem1);
        tem1 = s.X * tem1;
        cout << "解密者的X为：" << u.X << endl;
        cout << u.id << "(接收者)解密成功" << endl;
        cout << tem / tem1 << endl;
    }
    void Dec(ts_g& ts_g, pkisi_g& pkisi_g, ST& ST, user& u, char T[], Ciphtertext& C, ZZn2& cube, char vk[]) {
        Big r1 = rand(ts_g.s);
        ECn RK1, RK2;
        ECn tem11 = r1 * ts_g.g;
        ECn tem22 = H1(vk) * ts_g.g;
        RK1 = u.usk.kid_j + (tem11 + tem22);
        RK2 = r1 * ts_g.g;
        ZZn2 tem1, tem2;
        ecap(C.c1, ST.KT, ts_g.s, cube, tem1);
        ecap(C.c3, RK1, ts_g.s, cube, tem2);
        tem1 *= pow(C.c2, ST.rT);
        tem1 *= tem2;
        tem1 *= C.c4;
        tem1 *= C.c5;
        RK2 += C.c6;
        ecap(C.c3, RK2, ts_g.s, cube, tem2);
        cout << "解密者的X为：" << u.X << endl;
        cout << u.id << "(发送者)解密成功" << endl;
        cout << tem1 / tem2 << endl;
    }


    int main() {
        Big p, q, t, a, n, cof, a1, b1;
        ZZn2 cube, e_g_g, e_g_h, m;
        ts_g ts_g;
        pkisi_g pkisi_g;
        Ciphtertext CT;
        ReCiphtertext RCT;
        ST st;
        ts ts;
        char vk[100], sk[100], T[100];
        cout << "系统开始运行" << endl;

        // 初始化随机数生成器
        srand(static_cast<unsigned int>(time(nullptr)));

        /*------------------------参数定义--------------------------*/
        strcpy(vk, "cui");
        strcpy(T, "time123");
        strcpy(sk, "liu");


        /*--------------------------------ini------------------------------------*/
        cout << "-----------------------------------------------------------------系统参数初始化-----------------------------------------------------------------" << endl;
        // 生成素数阶 q
        q = pow((Big)2, 159) + pow((Big)2, 17) + 1;
        cout << "产生素数阶 q：" << endl;
        cout << "q= " << q << endl;

        // 生成模数 p
        t = (pow((Big)2, PBITS) - 1) / (2 * q);
        a = (pow((Big)2, PBITS - 1) - 1) / (2 * q);
        forever{
            n = rand(t);
            if (n < a) continue;
            p = 2 * n * q - 1;
            if (p % 24 != 11) continue; // 必须是 2 mod 3，同时 3 mod 8
            if (prime(p)) break;
        }
        cout << "产生模数 p:" << endl;
        cout << "p= " << p << endl;

        cof = 2 * n; // 椭圆曲线余因子

        ecurve(0, 1, p, MR_PROJECTIVE); // 初始化椭圆曲线
        forever{
            cube = pow(randn2(), (p + 1) / 3);
            cube = pow(cube, p - 1);
            if (!cube.isunity()) break;
        }

        cout << "Cube root of unity= " << cube << endl;

        if (!(cube * cube * cube).isunity()) {
            cout << "sanity check failed" << endl;
            exit(0);
        }

        // 初始化 ts_g 参数
        ts_g.s = q;
        forever{
            while (!ts_g.g.set(randn())) {
                cout << "Attempting to generate ts_g.g..." << endl;
            }
            ts_g.g *= cof;
            if (!ts_g.g.iszero()) break;
            cout << "ts_g.g generated but is zero. Retrying..." << endl;
        }

            forever{
                while (!ts_g.h.set(randn())) {
                    cout << "Attempting to generate ts_g.h..." << endl;
                }
                ts_g.h *= cof;
                if (!ts_g.h.iszero()) break;
                cout << "ts_g.h generated but is zero. Retrying..." << endl;
        }

        cout << "ts_g 参数生成完毕" << endl;

        // 初始化 pkisi_g 参数
        pkisi_g.s = ts_g.s;
        pkisi_g.g = ts_g.g;
        pkisi_g.h = ts_g.h;
        pkisi_g.msk = rand(q);
        pkisi_g.mpk.g = pkisi_g.g;
        pkisi_g.mpk.g1 = pkisi_g.msk * pkisi_g.g;
        pkisi_g.mpk.h = pkisi_g.h;

        cout << "pkisig 参数生成完毕" << endl;
        cout << "-----------------------------------------------------------------用户初始化-----------------------------------------------------------------" << endl;

        // 用户初始化
        user Bob, Alice, Lihua;
        strcpy(Bob.id, "Bob");
        strcpy(Alice.id, "Alice");
        strcpy(Lihua.id, "Lihua");

        cout << "用户 ID 生成完毕" << endl;

        // 密钥生成
        Bob.upk = H1(Bob.id);
        Alice.upk = H1(Alice.id);
        Lihua.upk = H1(Lihua.id);

        user u[3] = { Bob, Alice, Lihua };
        KeyGen(pkisi_g, u, 3, q);
        Bob = u[0];
        Alice = u[1];
        Lihua = u[2];

        cout << "用户私钥生成完毕" << endl;

        cout << "-----------------------------------------------------------------时间服务器初始化-----------------------------------------------------------------" << endl;
        // 时间服务器初始化
        ts.priv = rand(q);
        ts.pub = ts.priv * pkisi_g.g;


        cout << "时间服务器公钥私钥生成完毕" << endl;
        cout << "-----------------------------------------------------------------加密过程-----------------------------------------------------------------" << endl;

        // 加密过程
        a1 = rand(q);
        b1 = rand(q);
        m.set(a1, b1);
        cout << "m:" << m << endl;

        // 生成 e_g_g 和 e_g_h
        if (!ecap(pkisi_g.g, pkisi_g.g, q, cube, e_g_g)) {
            cerr << "Failed to compute e_g_g." << endl;
            exit(1);
        }
        if (!ecap(pkisi_g.g, pkisi_g.h, q, cube, e_g_h)) {
            cerr << "Failed to compute e_g_h." << endl;
            exit(1);
        }

        Enc(q, ts_g, pkisi_g, ts.pub, T, Bob.upk, Bob, e_g_g, e_g_h, m, CT, vk);

        cout << "加密成功" << endl;

        // RK 生成
        user reveiver[2] = { Alice,Lihua };
        RKGen(q, p, cube, pkisi_g, reveiver, Bob, 2, e_g_g, e_g_h, CT, cof);
        Alice = reveiver[0];
        Lihua = reveiver[1];


        cout << "RK 生成成功" << endl;

        // 重加密过程
        ReEnc(q, pkisi_g, Bob, CT, RCT, cube, vk);

        cout << "重加密成功" << endl;

        // 时间戳功能
        RtTrd(q, ts_g, ts, T, st, p);

        cout << "时间戳成功" << endl;

        cout << "-----------------------------------------------------------------解密过程-----------------------------------------------------------------" << endl;
        // 解密过程
        Dec1(ts_g, pkisi_g, Alice, cube);
        Dec1(ts_g, pkisi_g, Lihua, cube);

        Dec2(ts_g, pkisi_g, st, Alice, Bob, T, CT, cube, RCT.RK_2);

        Dec2(ts_g, pkisi_g, st, Lihua, Bob, T, CT, cube, RCT.RK_2);

        Dec(ts_g, pkisi_g, st, Bob, T, CT, cube, vk);


        return 0;
    }