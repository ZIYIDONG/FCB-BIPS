#include <time.h>
#include <iostream>
#include <fstream>
#include <cstring>
#include <thread>
using namespace std;

#include "ecn.h"
#include "zzn.h"
#include "zzn2.h"

//C++���������߱������ⲿ�ִ�����C���Ա�д�ģ����������ʱӦ��ʹ��C���Ե�����Լ��
extern "C"
{
#include"miracl.h"
#include"mirdef.h"
}

//2015�����
//�ṩһ�������Բ�,Ϊ���ڲ�ͬ�汾��MSVC����ʱ��֮���ṩһ�ּ����Ի��ƣ�ʹ�þɴ����ܹ����°汾�Ŀ����������У�������Ҫ�Դ�����д����޸ġ�
FILE* __cdecl __iob_func(unsigned i) {
	return __acrt_iob_func(i);
}

#ifdef __cplusplus
extern "C"
#endif
//extern "C" { FILE __iob_func[3] = { *stdin,*stdout,*stderr }; }
FILE _iob[3] = { __iob_func(0)[0], __iob_func(1)[1], __iob_func(2)[2] };

//һ���ض���Microsoft Visual C++��������ָ����ڿ�������������Ϊ�����������Ǹ��������������ӹ����в�ҪĬ�����ӵ�libc.lib����⡣
#pragma comment(linker, "/NODEFAULTLIB:libc.lib")


#define renum 2500

#define HASH_LEN 32
#define HASH_LEN1 20   //������H2����Ϊ��������q��160λ�Ķ�����������160/8=20
										//H2�в���sha256Ҫ��HASH_LEN1 ������32�ı�������ˣ��Լ���H2�ڲ��������Ϊsha-1


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

/*----------------------------------------------------------------------------Tate Paring ��������Ҫ�ĺ���-----------------------------------------------------*/
void extract(ECn& A, ZZn& x, ZZn& y)  //��������
{
	x = (A.get_point())->X;
	y = (A.get_point())->Y;
}

void extract(ECn& A, ZZn& x, ZZn& y, ZZn& z)  //��Ӱ����
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

ZZn2 line(ECn& A, ECn& C, ZZn& slope, ZZn2& Qx, ZZn2& Qy)  //������Բ�����ϵĵ�Q��A��C��ֱ��
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

	BOOL fast_tate_pairing(ECn& P, ZZn2& Qx, ZZn2& Qy, Big& q, ZZn2& res) //P:����Ԫ��Qx,Qy:��Բ�����ϵĵ�Q�����꣬q:�����ף�res:˫���ԶԽ��
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
		res = pow(res, (p + 1) / q);   // raise to power of (p^2-1)/q
		res = conj(res) / res;
		if (res.isunity()) return FALSE;
		return TRUE;
	}
	BOOL ecap(ECn& P, ECn& Q, Big& order, ZZn2& cube, ZZn2& res)  //P:����Ԫ��Q:����㣬order:�����ף�cube:��������res:˫���ԶԽ��
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
	// ʵ����һ�����ַ�����ϣ��С��ģ�� p �Ĵ����� Big �ĺ��� H1
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
		//cout<<"modulus"<<p<<endl;//�Լ��ӵĲ鿴pֵ����䣬ͨ��pֵ��֪get_modulus()������get_mip()������
		//��get_mip()�õ����ǵ�ǰ��������Ⱥ�Ľ�ֵq.
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
	
	// the public params of ts
	typedef struct params_ts
	{
		ECn g, h;
		ZZn2 e_g_g,e_g_h;
		ECn ts_pub;
	}params_ts;

	// the public params of pkisi
	typedef struct params_pkisi
	{
		ECn g;
		ZZn2 e;
		PKISI_MPK MPK;
	}params_pkisi;


	// the private key of PKISI  \\ ֻ��һ��Ԫ�أ�û��Ҫ���ýṹ��
	/*typedef struct  PKISI_MSK {
		Big alpha;
	}PKISI_MSK;*/
	
	// the public key of PKISI
	typedef struct PKISI_MPK {
		ECn g, h, g1;
	}PKISI_MPK;

	////ʱ�������˽Կ          \\ ֻ��һ��Ԫ�أ�û��Ҫ���ýṹ��
	//typedef struct TRS_MSK {
	//	Big s;
	//}TRS_MSK;

	////��Կ       \\ ֻ��һ��Ԫ�أ�û��Ҫ���ýṹ��
	//typedef struct TRS_MPK {
	//	ECn g1;
	//}TRS_MPK;

	//�û�˽Կ
	typedef struct user_msk {
		Big r;
		ECn K;
	}user_msk;

	// ԭʼ���Ľṹ��
	typedef struct Ciphtertext {
		ECn c1;
		ZZn2 c2;
		ECn c3;
		ZZn2 c4;
		ZZn2 c5;
	}Ciphtertext;

	// �����ؼ������Ľṹ��
	typedef struct ReCiphtertext {
		ECn c1;
		ZZn2 c2;
		ZZn2 c3;
		ZZn2 c4;
		ZZn2 c5;
	}ReCiphtertext;


	////Enc��������
	//typedef struct params {
	//	ZZn2 e_g_g;
	//	ZZn2 e_g_h;
	//}Params;

	typedef struct RK_user {
		ECn u;
		ZZn2 v;
		ZZn2 w;
	}RK_user;


	//ʱ�����Žṹ��
	typedef struct St {
		Big rt;
		ECn Kt;
	}St;

	//PKISI�����û�˽Կ
	void  KeyGen(ECn h, ECn g, Big alpha, Big& r, Big q, ECn& K, Big upk) {
		r = rand(q);
		// r = inverse(1, r); �޸ģ�ɾ��
		K = (-r) * g;
		K = K + h;
		Big y = alpha - upk;
		y = inverse(1, y);
		K = y * K;
	}
	/*���������������������������������������������������������������������� Enc-------------------------------------*/
	void Enc(PKISI_MPK pkisi_mpk, Big q, user_msk user_msk, Big upk, Big QT, Params params, ZZn2 ming, Ciphtertext& c) {
		Big k1 = rand(q);
		Big k2 = rand(q);
		c.c1 = (k1 * pkisi_mpk.g1) + (-k1 * (QT%q) * pkisi_mpk.g);
		//cout << "YES";
		c.c2 = pow(params.e_g_g, k1);
		c.c3 = (k2 * pkisi_mpk.g1) + (-k2 * (upk%q) * pkisi_mpk.g);
		c.c4 = pow(params.e_g_g, k2 * user_msk.r);
		c.c5 = ming * pow(params.e_g_h,-k1) *pow(params.e_g_h, -k2);
	}
	/*---------------------------------------- ReEnc----------------------------------------------------------------*/
	void  ReEnc(Ciphtertext c, Big q, ZZn2 cube, ECn rk, ReCiphtertext& c1) {
		c1.c1 = c.c1;
		c1.c2 = c.c2;
		ecap(c.c3, rk, q, cube, c1.c3);
		c1.c4 = c.c4;
		c1.c5 = c.c5;
	}
	/*-------------------------------RKGen----------------------------------------------*/
	void RKGen(user_msk usk, Big upk, PKISI_MPK pkisi_mpk, ECn& rk, Params params, Big cof, Big q, ZZn2 cube, Ciphtertext c, RR& rr) {
		ECn Q;
		forever
		{
			while (!Q.set(randn()));
			Q *= cof;
			if (!Q.iszero()) break;
		}
			//����
		rk = usk.K + Q;
		Big k3 = rand(q);
		ZZn2 X;
		ecap(c.c3, Q, q, cube, X);
		rr.u = (k3 * pkisi_mpk.g1) + (((-k3) + upk) * pkisi_mpk.g);
		rr.v = pow(params.e_g_g, k3);
		rr.w = X * pow(params.e_g_h, -k3);
	}

	void RTtrd(PKISI_MPK pkisi_mpk, Big q, Big QtTimeToBeDec, TRS_MPK &trs_mpk,TRS_MSK& trs_msk, St& st) {
		st.rt = rand(q);
		Big y = trs_msk.s - QtTimeToBeDec;
		y = inverse(1, y);
		st.Kt = (pkisi_mpk.h + ((-st.rt) * pkisi_mpk.g));
		st.Kt = y*st.Kt;
		while (trs_msk.s == QtTimeToBeDec) {
			trs_msk.s = rand(q);
			trs_mpk.g1 = trs_msk.s * pkisi_mpk.g;
			Big y = trs_msk.s - QtTimeToBeDec;
			y = inverse(1, y);
			st.Kt = (pkisi_mpk.h + ((-st.rt) * pkisi_mpk.g));
			st.Kt = y * st.Kt;
		}
		cout << "trs_msk.s= " << trs_msk.s << endl;
	}
	void Dec1(RR rr, user_msk user_msk, Big q, ZZn2 cube, St st, ZZn2& X) {
		ZZn2 Y;
		ecap(rr.u, user_msk.K, q, cube, Y);
		X = Y * pow(rr.v, user_msk.r) * rr.w;
	}

	void Dec2(St st, ZZn2 X, ReCiphtertext c1, Big q, ZZn2 cube, ZZn2& ming1) {
		ZZn2 Y;
		ecap(c1.c1, st.Kt, q, cube, Y);
		ming1 = Y * pow(c1.c2, st.rt) * c1.c3 * c1.c4 * c1.c5;
		ming1 = ming1 / X;
	}

	void Dec(Ciphtertext c, user_msk user_msk, Big q, ZZn2 cube, St st, ZZn2& ming1) {
		ZZn2 Y1;
		ZZn2 Y2;
		ecap(c.c1, st.Kt, q, cube, Y1);
		ecap(c.c3, user_msk.K, q, cube, Y2);
		//cout << Y1 << " " << pow(c.c2, st.rt) << " " << Y2 << " " << c.c4 << " " << c.c5 << endl;
		ming1 = Y1 * pow(c.c2, st.rt) * Y2 * c.c4 * c.c5;
	}

	
	int main() {            

		// �޸ģ�ȱ�ٴ�����Բ���߲����м����
		ECn P, Q, R; //��Բ�����ϵĵ�
		ZZn2 g0, Qx, Qy, gid, gid1, cube, w;//�Լ�     //gid:˫���ԶԽ����gid1:˫���ԶԽ����cube:��������w:�������� Qx,Qy:��Բ�����ϵĵ�Q������
		Big px, py, qx, qy, ab, r1;//�Լ�         //px,py:��Բ�����ϵĵ�P�����꣬qx,qy:��Բ�����ϵĵ�Q�����꣬ab:��Բ�����ϵĵ�Qid�����꣬r1:��ϣֵ
		big x1, y1, x2, y2;                          //x1,y1:��Բ�����ϵĵ�����꣬x2,y2:��Բ�����ϵĵ������
		Big a, b, c, d1, d2, p, q, t, n, cof, x, y;  //a:˽Կ��b:˽Կ��c:˽Կ��d1:˽Կ��d2:˽Կ��p:����p��q:����q��t:�����ף�n:�������cof:ϵ����x:��Բ�����ϵĵ�����꣬y:��Բ�����ϵĵ������
		char pad[HASH_LEN1];//�Լ�                   //pad:��ϣֵ

		//
		long seed;                                   //seed:���������
		//Big p;//p:����
		Big pkisi_msk;
		//PKISI_MPK pkisi_mpk;   ����Կ�ǹ���������һ���֣��ʽ��кϲ�
		//Big cof, n, a, t;//ϵ����n:�����
		Big ts_msk;
		//TRS_MPK trs_mpk;
		char Alice[100] = "Alice@email.com";//������
		char Bob[100] = "Bob@@email.com";
		char Tom[100] = "Tom@qq.com";
		char Andy[100] = "Andy@qq.com";
		char TimeToBeDec[9] = "20241212";
		char TimeNow[9] = "20241212";
		Big QtTimeToBeDec, QtTimeNow;
		Ciphtertext c1;
		// ReCiphtertext c21; �޸ģ�ɾ������
		Big upk1, upk2, upk3, upk4;//�û���Կ
		//Big q;//����ȡģ
		user_msk user_msk1, user_msk2, user_msk3, user_msk4;
		ZZn2 mi;
		//ZZn2 cube;//������
		params_ts params_ts;
		RK_user RK_bob, RK_tom, RK_andy;   //Rj
		ECn RK;
		ZZn2 PT;   // Plaintext to be encrypted
		ZZn2 PT_bob, PT_tom, PT_andy;
		St st;
		ZZn2 X_Bob, X_Tom, X_Andy;    // ���������м���� X
		miracl* mip = &precision;                    //miracl* mip:����

		cout << "������Щ����������ʱ����1���룬���л������������ظ�ִ��" << renum << "�� " << endl;
		cout << "Enter 9 digit random number seed  = ";
		cin >> seed;
		irand(seed);
		/*-------------------------------------------------------------����������q-------------------------------------------------------------------------*/
		q = pow((Big)2, 159) + pow((Big)2, 17) + 1;

		cout << "q= " << q << endl;

		/*--------------------------------------------------------------��������p-------------------------------------------------------------------------*/
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
		cof = 2 * n;  //��Բ����������
		ecurve(0, 1, p, MR_PROJECTIVE);    // elliptic curve y^2=x^3+1 mod p����Ӱ����ϵͳ

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
		/*--------------------------------------------------------------��������p ����-------------------------------------------------------------------------*/
		

	    /*--------------------------------------------------------------��ʼ��ʱ�����������������˽Կ-------------------------------------------------------------------------*/

		// ����ʱ����������������е�һ������Ԫg
		forever
		{
			while (!params_ts.g.set(randn()));
		params_ts.g *= cof;
			if (!params_ts.g.iszero()) break;
		}

		// ����ʱ����������������еڶ�������Ԫh
		forever
		{
			while (!params_ts.h.set(randn()));
		params_ts.h *= cof;
			if (!params_ts.h.iszero()) break;
		}
		//������Բ������˫����ӳ�� e(g,g) �� e(g,h)
		ecap(params_ts.g, params_ts.g, q, cube, params_ts.e_g_g);
		if (ecap(params_ts.g, params_ts.g, q, cube, params_ts.e_g_g)) {
			cout << "ecap:e_g_g success" << endl;
		}
		else {
			cout << "ecap:e_g_g error" << endl;
		}
		ecap(params_ts.g, params_ts.h, q, cube, params_ts.e_g_h);
		if (ecap(params_ts.g, params_ts.g, q, cube, params_ts.e_g_h)) {
			cout << "ecap:e_g_h success" << endl;
		}
		else {
			cout << "ecap:e_g_h error" << endl;
		}

		// ʱ�������˽Կ���ɣ�
		ts_msk = rand(q);
		params_ts.ts_pub = ts_msk * params_ts.g;

		/*----------------------------------------��������----------------------------------------------------*/
		ming = randn2();
		cout << "��������Ϊ��" << ming << endl;

		pkisi_msk.alpha = rand(q);
		//����g,h
		forever
		{
			while (!pkisi_mpk.g.set(randn()));
			pkisi_mpk.g *= cof;
			if (!pkisi_mpk.g.iszero()) break;
		}
			//������Բ����������ԪP1(g1)
		pkisi_mpk.g1 = pkisi_msk.alpha * pkisi_mpk.g;

		forever
		{
			while (!pkisi_mpk.h.set(randn()));
			pkisi_mpk.h *= cof;
			if (!pkisi_mpk.h.iszero()) break;
		}
		ecap(pkisi_mpk.g, pkisi_mpk.g, q, cube, params.e_g_g);
		if (ecap(pkisi_mpk.g, pkisi_mpk.g, q, cube, params.e_g_g)) {
			cout << "ecap:e_g_g success" << endl;
		}
		else {
			cout << "ecap:e_g_g error" << endl;
		}
		ecap(pkisi_mpk.g, pkisi_mpk.h, q, cube, params.e_g_h);
		if (ecap(pkisi_mpk.g, pkisi_mpk.h, q, cube, params.e_g_h)) {
			cout<<"ecap:e_g_h success" << endl;
		}
		else {
			cout << "ecap:e_g_h error" << endl;
		}
		/*------------------------ KeyGen pkisi .�ý׶ΰ�����������-----------------------------------------*/
		upk1 = H1(Alice);//�û���Կ
		upk2 = H1(Bob);
		upk3 = H1(Tom);
		upk4 = H1(Andy);
		QtTimeToBeDec = H1(TimeToBeDec);
		QtTimeNow = H1(TimeNow);
		while (pkisi_msk.alpha == upk1|| pkisi_msk.alpha == upk2|| pkisi_msk.alpha == upk3|| pkisi_msk.alpha == upk4) {
			pkisi_msk.alpha = rand(q);
			pkisi_mpk.g1 = pkisi_msk.alpha * pkisi_mpk.g;
		}
		cout << "pkisi_msk.alpha= " << pkisi_msk.alpha << endl;
		/*PKGΪ�û�����˽Կ*/
		/*void  KeyGen(ECn h, ECn g, Big alpha, Big& r, Big q, ECn& K, Big upk) {
		r = rand(q);
		K = (- r )* g;
		K = K + h;
		Big y = alpha - upk;
		y = inverse(1, y);
		K = y * K;
	}*/
		KeyGen(pkisi_mpk.h, pkisi_mpk.g, pkisi_msk.alpha, user_msk1.r, q, user_msk1.K, upk1);

		/*KeyGen(pkisi_mpk.h, pkisi_mpk.g, pkisi_msk.alpha, user_msk2.r, q, user_msk2.K, upk2);
		KeyGen(pkisi_mpk.h, pkisi_mpk.g, pkisi_msk.alpha, user_msk3.r, q, user_msk3.K, upk3);
		KeyGen(pkisi_mpk.h, pkisi_mpk.g, pkisi_msk.alpha, user_msk4.r, q, user_msk4.K, upk4);*/
		/*-------------------------------����-------------------------------------------*/
		/*void Enc(TRS_MPK trs_mpk, PKISI_MPK pkisi_mpk, Big p, user_msk user_msk, Big upk, Big QT, Params params, ZZn2 ming, Ciphtertext& c) {
		Big k1 = rand(p);
		Big k2 = rand(p);
		c.c1 = (k1 * pkisi_mpk.g1) + (((-k1) + QT) * pkisi_mpk.g);
		c.c2 = pow(params.e_g_g, k1);
		c.c3 = (k2 * pkisi_mpk.g1) + (((-k2) + upk) * pkisi_mpk.g);
		c.c4 = pow(params.e_g_g, k2 * user_msk.r);
		c.c5 = ming * pow(params.e_g_h, -k1) * pow(params.e_g_h, -k2);
	}*/
		Enc(pkisi_mpk, q, user_msk1, upk1, QtTimeToBeDec, params, ming, c1);
		RTtrd(pkisi_mpk, q, QtTimeNow, trs_mpk, trs_msk, st);
		Dec(c1, user_msk1, q, cube, st, ming11);
		cout << "�����߽�������Ϊ��" << ming11 << endl;
		/*--------------------------------RkGen-----------------------------------*/
		
		/*RKGen(user_msk1, upk2, pkisi_mpk, rk, params, cof, q, cube, c1, rr2);
		RKGen(user_msk1, upk3, pkisi_mpk, rk, params, cof, q, cube, c1, rr3);
		RKGen(user_msk1, upk3, pkisi_mpk, rk, params, cof, q, cube, c1, rr4);*/

		/*---------------------------------------ReEnc--------------------------------*/
		//ReEnc(c1,q,cube,rk,c21);
		

		/*------------------------------RTtrd---------------------------------------*/
		//RTtrd(pkisi_mpk,p, QtTimeNow, trs_mpk,trs_msk,st);

		/*-------------------------------Dec1----------------------------------------*/
		/*Dec1(rr2, user_msk2,q,cube,st,x2);
		Dec1(rr3, user_msk3, q, cube, st, x3);
		Dec1(rr4, user_msk4, q, cube, st, x4);*/
		/*----------------------------------Dec2----------------------------------------*/
		/*Dec2(st,x2,c21,q,cube,ming21);
		Dec2(st, x3, c21, q, cube, ming31);
		Dec2(st, x4, c21, q, cube, ming41);*/
/*cout << "������1��������Ϊ��" << ming21 << endl;
		cout << "������2��������Ϊ��" << ming31 << endl;
		cout << "������3��������Ϊ��" << ming41  << endl;*/
		/*
		/*void Dec(Ciphtertext c, user_msk user_msk, Big q, ZZn2 cube, St st, ZZn2& ming1) {
		ZZn2 Y1;
		ZZn2 Y2;
		ecap(c.c1, st.Kt, q, cube, Y1);
		ecap(c.c3, user_msk.K, q, cube, Y2);
		ming1 = Y1 * pow(c.c2, st.rt) * Y2 * c.c4 * c.c5;
	}*/
		
	}