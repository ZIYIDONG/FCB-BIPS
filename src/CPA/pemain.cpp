#include <time.h>
#include <iostream>
#include <fstream>
#include <cstring>
#include <thread>
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

/*----------------------------------------------------------------------------Tate Paring 计算所需要的函数-----------------------------------------------------*/
void extract(ECn& A, ZZn& x, ZZn& y)  //仿射坐标
{
	x = (A.get_point())->X;
	y = (A.get_point())->Y;
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

//
// Line from A to destination C. Let A=(x,y)
// Line Y-slope.X-c=0, through A, so intercept c=y-slope.x
// Line Y-slope.X-y+slope.x = (Y-y)-slope.(X-x) = 0
// Now evaluate at Q -> return (Qy-y)-slope.(Qx-x)
//

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

#ifndef SCOTT

//
// Vertical line through point A
//

ZZn2 vertical(ECn& A, ZZn2& Qx)
{
	ZZn2 n = Qx;
	ZZn x, y, z;
#ifdef AFFINE
	extract(A, x, y);
	n -= x;
#endif
#ifdef PROJECTIVE
	extract(A, x, y, z);
	z *= z;
	n *= z; n -= x;                // 3 ZZn muls
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

	//
	// Tate Pairing 
	//

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

		for (i = nb - 2;i >= 0;i--)
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
		//cout << p << "217" << endl;
		res = pow(res, (p + 1) / q);   // raise to power of (p^2-1)/q
		res = conj(res) / res;
		if (res.isunity()) return FALSE;
		return TRUE;
	}
	BOOL ecap(ECn& P, ECn& Q, Big& order, ZZn2& cube, ZZn2& res)  //P:生成元，Q:任意点，order:素数阶，cube:立方根，res:双线性对结果
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
	// 实现了一个将字符串哈希到小于模数 p 的大整数 Big 的函数 H1
	Big H1(char* string)
	{ // Hash a zero-terminated string to a number < modulus
		Big h, p;
		char s[HASH_LEN];
		int i, j;
		sha256 sh;

		shs256_init(&sh);

		for (i = 0;;i++)
		{
			if (string[i] == 0)
				break;
			shs256_process(&sh, string[i]);
		}
		shs256_hash(&sh, s);
		p = get_modulus();
		//cout<<"modulus" << ":" << "280" << ":" << p << endl;//自己加的查看p值的语句，通过p值可知get_modulus()调用了get_mip()函数，
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
		//cout << "295:" << "h= " << h << endl;
		h %= p;
		//cout << "297:" << "h= " << h << endl;
		return h;
	}

	// the public key of PKISI
	typedef struct PKISI_MPK {
		ECn g, h, g1;
	}PKISI_MPK;

	// the public params of pkisi
	typedef struct params_pkisi
	{
		//ECn g;
		//ZZn2 e;
		PKISI_MPK MPK;
		ZZn2 e_g_g, e_g_h;
	}params_pkisi;

	// the public params of ts
	typedef struct params_ts
	{
		ECn g, h;
		ZZn2 e_g_g,e_g_h;
		ECn ts_pub;
	}params_ts;

	// the private key of PKISI  \\ 只有一个元素，没必要设置结构体
	/*typedef struct  PKISI_MSK {
		Big alpha;
	}PKISI_MSK;*/
	


	////时间服务器私钥          \\ 只有一个元素，没必要设置结构体
	//typedef struct TRS_MSK {
	//	Big s;
	//}TRS_MSK;

	////公钥       \\ 只有一个元素，没必要设置结构体
	//typedef struct TRS_MPK {
	//	ECn g1;
	//}TRS_MPK;

	//用户私钥
	typedef struct user_msk {
		Big r;
		ECn K;
	}user_msk;

	// 原始密文结构体
	typedef struct Ciphtertext {
		ECn c1;
		ZZn2 c2;
		ECn c3;
		ZZn2 c4;
		ZZn2 c5;
	}Ciphtertext;

	// 代理重加密密文结构体
	typedef struct ReCiphtertext {
		ECn c1;
		ZZn2 c2;
		ZZn2 c3;
		ZZn2 c4;
		ZZn2 c5;
	}ReCiphtertext;


	////Enc公开参数
	//typedef struct params {
	//	ZZn2 e_g_g;
	//	ZZn2 e_g_h;
	//}Params;

	typedef struct RK_user {
		ECn u;
		ZZn2 v;
		ZZn2 w;
	}RK_user;


	//时间陷门结构体
	typedef struct St {
		Big rt;
		ECn Kt;
	}St;

	//PKISI计算用户私钥
	void  KeyGen(params_pkisi params_pkisi, Big pkisi_msk, Big upk, user_msk& msk, Big q, Big p) {
		msk.r = rand(q);
		msk.K = msk.r * (-params_pkisi.MPK.g);
		msk.K = msk.K + params_pkisi.MPK.h;
		Big y = pkisi_msk - upk;
		cout << "y=" << y << endl;
		Big z = inverse(y, p);
		cout << "z=" << z << endl;
		//cout << (z * y) % q << endl;
		//cout << "test2" << endl;
		msk.K = z * msk.K;
		cout << "KeyGen complete" << endl;
	}
	/*——————————————————————————————————— Enc-------------------------------------*/
	void Enc(params_ts params_ts, params_pkisi params_pkisi, user_msk user_msk, Big upk, Big QT, ZZn2 PT, Big q, Big p, Ciphtertext& CT) {
		Big k1 = rand(q);
		Big k2 = rand(q);
		CT.c1 = (k1 * params_ts.ts_pub) + ((k1 * (-params_ts.g)) + (QT * (-params_ts.g)));
		CT.c2 = pow(params_ts.e_g_g, k1);
		CT.c3 = (k2 * params_pkisi.MPK.g1) + ((k2 * (-params_pkisi.MPK.g)) + (upk * (-params_pkisi.MPK.g)));
		//c.c3 = (k2 * params_pkisi.MPK.g1) + (k2 * upk * (-params_pkisi.MPK.g));
		CT.c4 = pow(params_pkisi.e_g_g, k2 * user_msk.r);
		CT.c5 = PT * pow(params_ts.e_g_h, (-k1)) * pow(params_pkisi.e_g_h, (-k2));
		cout << "Enc complete" << endl;
	}
	/*---------------------------------------- ReEnc----------------------------------------------------------------*/
	void  ReEnc(Ciphtertext c, Big q, ZZn2 cube, ECn rk, ReCiphtertext& CT) {
		CT.c1 = c.c1;
		CT.c2 = c.c2;
		ecap(c.c3, rk, q, cube, CT.c3);
		CT.c4 = c.c4;
		CT.c5 = c.c5;
		cout << "ReEnc complete" << endl;
	}
	/*-------------------------------RKGen----------------------------------------------*/
	void RKGen(user_msk usk, Big upk, PKISI_MPK pkisi_mpk, ECn& rk, params_ts params_ts, Big cof, Big q, ZZn2 cube, Ciphtertext c, RK_user& rr) {
		ECn Q;
		forever
		{
			while (!Q.set(randn()));
			Q *= cof;
			if (!Q.iszero()) break;
		}
			//待定
		rk = usk.K + Q;
		Big k3 = rand(q);
		ZZn2 X;
		ecap(c.c3, Q, q, cube, X);
		rr.u = (k3 * pkisi_mpk.g1) + (((-k3) + upk) * pkisi_mpk.g);
		rr.v = pow(params_ts.e_g_g, k3);
		rr.w = X * pow(params_ts.e_g_h, -k3);
	}

	void RTtrd(params_ts params_ts, Big ts_msk, Big QtTimeNow, St st, Big q, Big p) {
		st.rt = rand(q);
		Big y = ts_msk - QtTimeNow;
		y = inverse(y, p);
		st.Kt = (params_ts.h + (st.rt * (-params_ts.g)));
		st.Kt = y * st.Kt;
		/*while (ts_msk == QtTimeNow) {
			ts_msk = rand(q);
			params_ts.ts_pub = ts_msk * params_ts.g;
			y = ts_msk - QtTimeNow;
			y = inverse(y, p);
			st.Kt = (params_ts.h + ((-st.rt) * params_ts.g));
			st.Kt = y * st.Kt;
		}*/
		//cout << "ts_msk= " << ts_msk << endl;
		cout << "RTtrd complete" << endl;
	}
	void DeCT(RK_user rr, user_msk user_msk, Big q, ZZn2 cube, St st, ZZn2& X) {
		ZZn2 Y;
		ecap(rr.u, user_msk.K, q, cube, Y);
		X = Y * pow(rr.v, user_msk.r) * rr.w;
	}

	void Dec2(St st, ZZn2 X, ReCiphtertext CT, Big q, ZZn2 cube, ZZn2& ming1) {
		ZZn2 Y;
		ecap(CT.c1, st.Kt, q, cube, Y);
		ming1 = Y * pow(CT.c2, st.rt) * CT.c3 * CT.c4 * CT.c5;
		ming1 = ming1 / X;
	}

	void Dec(Ciphtertext CT, user_msk user_msk, Big q, ZZn2 cube, St st, ZZn2& PT_Alice) {
		ZZn2 Y1;
		ZZn2 Y2;
		ecap(CT.c1, st.Kt, q, cube, Y1);
		if (ecap(CT.c1, st.Kt, q, cube, Y1)) {
			cout << "Y1 Success" << endl;
		}
		else {
			cout << "Y1 Failure" << endl;
		}
		ecap(CT.c3, user_msk.K, q, cube, Y2);
		if (ecap(CT.c3, user_msk.K, q, cube, Y2)) {
			cout << "Y2 Success" << endl;
		}
		else {
			cout << "Y2 Failure" << endl;
		}
		//cout << Y1 << " " << pow(c.c2, st.rt) << " " << Y2 << " " << c.c4 << " " << c.c5 << endl;
		PT_Alice = Y1 * pow(CT.c2, st.rt) * Y2 * CT.c4 * CT.c5;
	}

	
	int main() {            
		// 修改：缺少大量椭圆曲线操作中间参数
		ECn P, Q, R; //椭圆曲线上的点
		ZZn2 g0, Qx, Qy, gid, gid1, cube, w;//自加     //gid:双线性对结果，gid1:双线性对结果，cube:立方根，w:幂运算结果 Qx,Qy:椭圆曲线上的点Q的坐标
		Big px, py, qx, qy, ab, r1;//自加         //px,py:椭圆曲线上的点P的坐标，qx,qy:椭圆曲线上的点Q的坐标，ab:椭圆曲线上的点Qid的坐标，r1:哈希值
		big x1, y1, x2, y2;                          //x1,y1:椭圆曲线上的点的坐标，x2,y2:椭圆曲线上的点的坐标
		Big a, b, c, d1, d2, p, q, t, n, cof, x, y;  //a:私钥，b:私钥，c:私钥，d1:私钥，d2:私钥，p:素数p，q:素数q，t:素数阶，n:随机数，cof:系数，x:椭圆曲线上的点的坐标，y:椭圆曲线上的点的坐标
		char pad[HASH_LEN1];//自加                   //pad:哈希值

		//
		long seed;                                   //seed:随机数种子
		//Big p;//p:素数
		Big pkisi_msk;          //a
		params_pkisi params_pkisi;
		//PKISI_MPK pkisi_mpk;   主公钥是公开参数的一部分，故进行合并
		//Big cof, n, a, t;//系数，n:随机数
		Big ts_msk;
		params_ts params_ts;
		//TRS_MPK trs_mpk;
		char Alice[100] = "Alice@email.com";//发送者
		char Bob[100] = "Bob@@email.com";
		char Tom[100] = "Tom@qq.com";
		char Andy[100] = "Andy@qq.com";
		char TimeToBeDec[] = "20241212";
		char TimeNow[] = "20241212";
		Big QtTimeToBeDec, QtTimeNow;
		Ciphtertext CT;  // 密文
		ReCiphtertext RCT; // 代理重加密密文
		Big upk_Alice, upk_Bob, upk_Tom, upk_Andy;//用户公钥
		//Big q;//素数取模
		user_msk user_msk_Alice, user_msk_Bob, user_msk_Tom, user_msk_Andy;
		//ZZn2 mi;
		//ZZn2 cube;//立方根

		RK_user RK_bob, RK_tom, RK_andy;   //Rj
		ECn RK;
		ZZn2 PT;   // Plaintext to be encrypted
		ZZn2 PT_Alice ,PT_Bob, PT_Tom, PT_Andy;
		St st;
		ZZn2 X_Bob, X_Tom, X_Andy;    // 解密所用中间参数 X
		miracl* mip = &precision;                    //miracl* mip:精度

		cout << "由于有些基本操作耗时不足1毫秒，所有基本操作都将重复执行" << renum << "次 " << endl;
		cout << "Enter 9 digit random number seed  = ";
		cin >> seed;
		irand(seed);
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
		/*--------------------------------------------------------------产生素数p 结束-------------------------------------------------------------------------*/
		

	    /*--------------------------------------------------------------初始化时间服务器公开参数，私钥-------------------------------------------------------------------------*/

		// 生成时间服务器公开参数中第一个生成元g
		forever
		{
			while (!params_ts.g.set(randn()));
				params_ts.g *= cof;
			if (!params_ts.g.iszero()) break;
		}

		// 生成时间服务器公开参数中第二个生成元h
		forever
		{
			while (!params_ts.h.set(randn()));
				params_ts.h *= cof;
			if (!params_ts.h.iszero()) break;
		}
		//产生params_ts椭圆曲线上双线性映射 e(g,g) 和 e(g,h)
		ecap(params_ts.g, params_ts.g, q, cube, params_ts.e_g_g);
		if (ecap(params_ts.g, params_ts.g, q, cube, params_ts.e_g_g)) {
			cout << "params_ts ecap:e_g_g success" << endl;
		}
		else {
			cout << "params_ts ecap:e_g_g error" << endl;
		}
		ecap(params_ts.g, params_ts.h, q, cube, params_ts.e_g_h);
		if (ecap(params_ts.g, params_ts.h, q, cube, params_ts.e_g_h)) {
			cout << "params_ts ecap:e_g_h success" << endl;
		}
		else {
			cout << "params_ts ecap:e_g_h error" << endl;
		}

		// 时间服务器私钥生成，
		ts_msk = rand(q);
		params_ts.ts_pub = ts_msk * params_ts.g;

		/*----------------------------------------产生明文----------------------------------------------------*/
		PT =randn2();
		cout << "加密明文为：" << PT << endl;

		pkisi_msk = rand(q);
		//产生g,h
		forever
		{
			while (!params_pkisi.MPK.g.set(randn()));
				params_pkisi.MPK.g *= cof;
			if (!params_pkisi.MPK.g.iszero()) break;
		}
			//产生椭圆曲线上生成元P1(g1)
		params_pkisi.MPK.g1 = pkisi_msk * params_pkisi.MPK.g;

		forever
		{
			while (!params_pkisi.MPK.h.set(randn()));
				params_pkisi.MPK.h *= cof;
			if (!params_pkisi.MPK.h.iszero()) break;
		}
		//产生params_pkisi椭圆曲线上双线性映射 e(g,g) 和 e(g,h)
		ecap(params_pkisi.MPK.g, params_pkisi.MPK.g, q, cube, params_pkisi.e_g_g);
		if (ecap(params_pkisi.MPK.g, params_pkisi.MPK.g, q, cube, params_pkisi.e_g_g)) {
			cout << "params_pkisi ecap:e_g_g success" << endl;
		}
		else {
			cout << "params_pkisi ecap:e_g_g error" << endl;
		}
		ecap(params_pkisi.MPK.g, params_pkisi.MPK.h, q, cube, params_pkisi.e_g_h);
		if (ecap(params_pkisi.MPK.g, params_pkisi.MPK.h, q, cube, params_pkisi.e_g_h)) {
			cout << "params_pkisi ecap:e_g_h success" << endl;
		}
		else {
			cout << "params_pkisi ecap:e_g_h error" << endl;
		}
		/*------------------------ KeyGen pkisi .该阶段包括下述操作-----------------------------------------*/
		upk_Alice = H1(Alice);//用户公钥
		upk_Bob = H1(Bob);
		upk_Tom = H1(Tom);
		upk_Andy = H1(Andy);
		QtTimeToBeDec = H1(TimeToBeDec);
		QtTimeNow = H1(TimeNow);
		/*while (pkisi_msk == upk_Alice || pkisi_msk == upk_Bob || pkisi_msk == upk_Tom || pkisi_msk == upk_Andy) {
			pkisi_msk = rand(q);
			params_pkisi.MPK.g1 = pkisi_msk * params_pkisi.MPK.g;
		}*/
		cout << "pkisi_msk.alpha= " << pkisi_msk << endl;
		/*PKG为用户生成私钥*/
		KeyGen(params_pkisi, pkisi_msk, upk_Alice, user_msk_Alice, q, p);
		/*KeyGen(pkisi_mpk.h, pkisi_mpk.g, pkisi_msk.alpha, user_msk_Bob.r, q, user_msk_Bob.K, upk_Bob);
		KeyGen(pkisi_mpk.h, pkisi_mpk.g, pkisi_msk.alpha, user_msk_Tom.r, q, user_msk_Tom.K, upk_Tom);
		KeyGen(pkisi_mpk.h, pkisi_mpk.g, pkisi_msk.alpha, user_msk_Andy.r, q, user_msk_Andy.K, upk_Andy);*/
		/*-------------------------------加密-------------------------------------------*/
		RTtrd(params_ts, ts_msk, QtTimeNow, st, q, p);
		Enc(params_ts, params_pkisi, user_msk_Alice, upk_Alice, QtTimeToBeDec, PT, q, p,CT);
		Dec(CT, user_msk_Alice, q, cube, st, PT_Alice);
		//cout << params_pkisi.MPK.g << endl;
		cout << "发送者解密明文为：" << PT << endl;
		/*--------------------------------RkGen-----------------------------------*/
		
		/*RKGen(user_msk_Alice, upk_Bob, pkisi_mpk, rk, params, cof, q, cube, CT, rr2);
		RKGen(user_msk_Alice, upk_Tom, pkisi_mpk, rk, params, cof, q, cube, CT, rr3);
		RKGen(user_msk_Alice, upk_Tom, pkisi_mpk, rk, params, cof, q, cube, CT, rr4);*/

		/*---------------------------------------ReEnc--------------------------------*/
		//ReEnc(CT,q,cube,rk,c21);
		

		/*------------------------------RTtrd---------------------------------------*/
		//RTtrd(pkisi_mpk,p, QtTimeNow, trs_mpk,trs_msk,st);

		/*-------------------------------DeCT----------------------------------------*/
		/*DeCT(rr2, user_msk_Bob,q,cube,st,x2);
		DeCT(rr3, user_msk_Tom, q, cube, st, x3);
		DeCT(rr4, user_msk_Andy, q, cube, st, x4);*/
		/*----------------------------------Dec2----------------------------------------*/
		/*Dec2(st,x2,c21,q,cube,ming21);
		Dec2(st, x3, c21, q, cube, ming31);
		Dec2(st, x4, c21, q, cube, ming41);*/
/*cout << "接收者1解密明文为：" << ming21 << endl;
		cout << "接收者2解密明文为：" << ming31 << endl;
		cout << "接收者3解密明文为：" << ming41  << endl;*/
		/*
		/*void Dec(Ciphtertext c, user_msk user_msk, Big q, ZZn2 cube, St st, ZZn2& ming1) {
		ZZn2 Y1;
		ZZn2 Y2;
		ecap(c.CT, st.Kt, q, cube, Y1);
		ecap(c.c3, user_msk.K, q, cube, Y2);
		ming1 = Y1 * pow(c.c2, st.rt) * Y2 * c.c4 * c.c5;
	}*/
		
	}