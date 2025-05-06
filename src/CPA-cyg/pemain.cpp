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
FILE _iob[3] = {__iob_func(0)[0], __iob_func(1)[1], __iob_func(2)[2]}; 

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

Miracl precision(16,0);  // increase if PBITS increases. (32,0) for 1024 bit p

/*----------------------------------------------------------------------------Tate Paring ��������Ҫ�ĺ���-----------------------------------------------------*/
void extract(ECn& A,ZZn& x,ZZn& y)  //��������
{ 
    x=(A.get_point())->X;
    y=(A.get_point())->Y;
}

void extract(ECn& A,ZZn& x,ZZn& y,ZZn& z)  //��Ӱ����
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

ZZn2 line(ECn& A, ECn& C, ZZn& slope, ZZn2& Qx, ZZn2& Qy)  //������Բ�����ϵĵ�Q��A��C��ֱ��
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

BOOL fast_tate_pairing(ECn& P, ZZn2& Qx, ZZn2& Qy, Big& q, ZZn2& res) //P:����Ԫ��Qx,Qy:��Բ�����ϵĵ�Q�����꣬q:�����ף�res:˫���ԶԽ��
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


BOOL ecap(ECn& P,ECn& Q,Big& order,ZZn2& cube,ZZn2& res)  //P:����Ԫ��Q:����㣬order:�����ף�cube:��������res:˫���ԶԽ��
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
/*----------------------------------------------------------------------------Tate Paring ��������Ҫ�ĺ���-----------------------------------------------------*/


/*----------------------------------------------------------------------------���Hash��������ĺ���-----------------------------------------------------*/
// ʵ����һ�����ַ�����ϣ��С��ģ�� p �Ĵ����� Big �ĺ��� H1
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
	//cout<<"modulus"<<p<<endl;//�Լ��ӵĲ鿴pֵ����䣬ͨ��pֵ��֪get_modulus()������get_mip()������
	//��get_mip()�õ����ǵ�ǰ��������Ⱥ�Ľ�ֵq.
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
// �ڸ��� (y) ֵ������£�
// �ҵ�������Բ���߷��� (y^2 = x^3 + 1) �� (x) ֵ
//

Big getx(Big y)
{
    Big p=get_modulus();
    Big t=modmult(y+1,y-1,p);   // avoids overflow
    return pow(t,(2*p-1)/3,p);
}
 
// MapToPoint
//��һ���ַ�����ʶ����ID��ӳ�䵽��Բ�����ϵ�һ����Ĺ���
ECn map_to_point(char *ID)
{
    ECn Q;
    Big x0,y0=H1(ID);
 
    x0=getx(y0);

    Q.set(x0,y0);

    return Q;
}
// ���� Miracl �ṩ inverse ���㺯������ʹ����չŷ������㷨������Ԫ
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
        return -1; // ��Ԫ������
    }
    else {
        return (x % q + q) % q; // ȷ�����Ϊ����
    }
}
Big getHashFromPoint(const ECn& pt) {
    Big X;
    // �ٶ� ECn::get(Big&) ����ȡ�õ�� x ���꣬��ʹ�������ʵ��ķ���ת��
    pt.get(X);
    return X;
}

// ������������ ECn ��ת��Ϊ�ַ������˴�����ȡ�� x ������Ϊ��ʶ
std::string pointToString(const ECn& P) {
    Big X, Y;
    P.get(X, Y);
    std::ostringstream oss;
    oss << X;  // ���� oss << X << "_" << Y; ����ʵ���������
    return oss.str();
}
/*-------------------------------------------- Sign + Enc --------------------------------------------*/


// ʱ�����Žṹ��
typedef struct TimetrapDoor {
    ECn st1;
    ECn st2;
}Timetrapdoor;

// Enc��������
typedef struct params {
    ECn P, P1, P2, P3, P4 ,g,h,g1,h1,g2,h2;
    ECn u[257];
    ECn v[257];
    ZZn2 e_g1_g2;
    ZZn2 e_g3_g4;
    ZZn2 e_g_g;
}params;

// PKG˽Կ
typedef struct sk_pkg {
    Big alpha;
    ECn sk_pkg;
}sk_pkg;

// TimeServer˽Կ
typedef struct sk_ts {
    Big beta;
    ECn sk_ts;
    Big s;
}sk_ts;
//11111���Ľṹ��
typedef struct Ciphtertext {

    ZZn2 c1;              // ����������Ϣ������
    ECn c2, c3, c4, c5;

	ZZn2 c6;             // ����ǩ��������
    ECn c7;

}Ciphtertext;

typedef struct Ciphtertext1 {

    ECn c1;              // ����
    ZZn2 c2;
    ECn V;              // ǩ��

}Ciphtertext1;



// ǩ���ṹ��
typedef struct
{
    ECn X;
	Big s;
    ZZn2 es;
}SignOfMessage;

/*---------------------------------------------------------���Hash��������ĺ���-----------------------------------------------------*/
/*---------------------------------------------------------------------------------------------------------------------������---------------------------------------------------------------------------------------------------*/
/*---------------------------------------------------------------------------------------------------------------------������---------------------------------------------------------------------------------------------------*/
/*---------------------------------------------------------------------------------------------------------------------������---------------------------------------------------------------------------------------------------*/
/*---------------------------------------------------------------------------------------------------------------------������---------------------------------------------------------------------------------------------------*/
/*---------------------------------------------------------------------------------------------------------------------������---------------------------------------------------------------------------------------------------*/
int main()
{

    //ofstream common("common.ibe");
    //ofstream master("master.ibe");
    // �Զ����Ʒ�ʽ���ļ�  
    ofstream outputFile1("Ciphertext.ibe");
    ofstream outputFile3("Ciphertext2.ibe");
    ofstream outputFile2("St.ibe");

    // ����ļ��Ƿ�ɹ���  
    if (!outputFile1) {
        std::cerr << "�޷����ļ�!" << std::endl;
        return 1; // ���ش������  
    }
    // ����ļ��Ƿ�ɹ���  
    if (!outputFile2) {
        std::cerr << "�޷����ļ�!" << std::endl;
        return 1; // ���ش������  
    }


    ECn P, Q, R, Ppub, Qid;                    //Ppub:Master Public Key, Qid:Identity Public Key P:����Ԫ��Q:����㣬R:�м����
    ZZn2 Qx, Qy, gid, gid1, cube, w;//�Լ�     //gid:˫���ԶԽ����gid1:˫���ԶԽ����cube:��������w:�������� Qx,Qy:��Բ�����ϵĵ�Q������
    Big px, py, qx, qy, ab, r1;//�Լ�         //px,py:��Բ�����ϵĵ�P�����꣬qx,qy:��Բ�����ϵĵ�Q�����꣬ab:��Բ�����ϵĵ�Qid�����꣬r1:��ϣֵ
    int i, tag;//�Լ� 

    Big a, b, c, d1, d2, p, q, t, n, cof, x, y;  //a:˽Կ��b:˽Կ��c:˽Կ��d1:˽Կ��d2:˽Կ��p:����p��q:����q��t:�����ף�n:�������cof:ϵ����x:��Բ�����ϵĵ�����꣬y:��Բ�����ϵĵ������
    big x1, y1, x2, y2;                          //x1,y1:��Բ�����ϵĵ�����꣬x2,y2:��Բ�����ϵĵ������
    long seed;                                   //seed:���������
    char pad[HASH_LEN1];//�Լ�                   //pad:��ϣֵ
    //char pad[20]={0};
    clock_t start_time, end_time;
    float t_dec;
    ZZn2 g0;
	Big m1, m2, m3;                             	//m1:���ģ�m2:���ģ�m3:����
    params params;
	ECn QtTimeToBeDec, QtTimeNow;
    Big fid;
    SignOfMessage m1_sign, m2_sign, m3_sign;
    sk_pkg sk_pkg;
    sk_ts sk_ts;

    TimetrapDoor st_TimeNow;
    Ciphtertext CT1, CT2, CT3;
    Ciphtertext1 CT1111;

    /*------------------------------------------------Enc+Sign��������---------------------------------------------------------------*/
    char Alice[100] = "Alice@email.com";
    char Bob[100] = "Bob@@email.com";
    char TimeToBeDec[9] = "20241212";
    char TimeNow[9] = "20241212";


    /*---------------------------------------------------------TS----------------------------------------------*/
    miracl* mip = &precision;                    //miracl* mip:����

    cout << "������Щ����������ʱ����1���룬���л������������ظ�ִ��" << renum << "�� " << endl;
    cout << "Enter 9 digit random number seed  = ";
    cin >> seed;
    irand(seed);

    // SET-UP
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
    
    /*---------------------------------------------------------���ɹ�������params----------------------------------------------*/
    //������Բ����������Ԫg
    forever
    {
        while (!params.g.set(randn()));
        params.g *= cof;
        if (!params.g.iszero()) break;
    }


    //������Բ����������Ԫh
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

    cout << "������Щ����������ʱ����1���룬���л������������ظ�ִ��" << renum << "�� " << endl;
    cout << "Enter 9 digit random number seed  = ";
    cin >> seed;
    irand(seed);

    // SET-UP
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

    /*---------------------------------------------------------���ɹ�������params----------------------------------------------*/

    //������Բ����������Ԫg
    forever
    {
        while (!params.g2.set(randn()));
        params.g2 *= cof;
        if (!params.g2.iszero()) break;
    }

    //������Բ����������Ԫh
    forever
    {
        while (!params.h2.set(randn()));
        params.h2 *= cof;
        if (!params.h2.iszero()) break;
    }
    sk_pkg.alpha = rand(q);

    cout << "sk_pkg.alpha= " << sk_pkg.alpha << endl;

    params.g1 = sk_pkg.alpha * params.g;

    // ======================= PKISI KeyGen ���� ============================

    vector<string> userIDs;
    for (int j = 0; j < 257; j++) {
        string id = "�û�" + to_string(j); // ֱ�������û� ID���� "�û�0", "�û�1", ...
        userIDs.push_back(id);
    }

    // ����ÿ���û��Ĺ�Կ upk_j = H1(ID_j)
    vector<Big> upks;
    for (int j = 0; j < 257; j++) {
        Big H_ID = H1((char*)userIDs[j].c_str());
        upks.push_back(H_ID);
    }

    // ����Ƿ���� �� = H1(ID_j)
    bool conflict = false;
    for (int j = 0; j < 257; j++) {
        if (upks[j] == sk_pkg.alpha) {
            conflict = true;
            break;
        }
    }
    if (conflict) {
        cout << "��⵽ �� = H1(ID)��ϵͳ���������ɲ����������û���˽Կ��" << endl;
        // �������� sk_pkg.alpha�������¹�Կ params.g1
        sk_pkg.alpha = rand(q);
        params.g1 = sk_pkg.alpha * params.g;
    }

    // ����˽Կ usk_j = (r, K)
    for (int j = 0; j < 257; j++) {
        cout << "-----------------------" << endl;
        cout << "�����û� " << userIDs[j] << " ..." << endl;

        // ���� H1(ID_j)
        Big userH = upks[j];

        // �����ĸ d = (�� - H1(ID_j)) mod q��ȷ��Ϊ��
        Big d = sk_pkg.alpha - userH;
        if (d < 0) d += q;
        if (d == 0) {
            cout << "�����û� " << userIDs[j] << " ���� �� = H1(ID)���޷�����˽Կ��" << endl;
            exit(0);
        }

        // ���� d �� Z_q �е���Ԫ
        Big d_inv = invmod(d, q);

        // ���ѡ�� r �� Z_p*��ȷ�� r �� 0
        Big r;
        do {
            r = rand(p);
        } while (r == 0);

        // ���� h - r*g
        ECn tmp = params.h;
        ECn tmp2 = params.g;
        tmp2 *= r;
        tmp -= tmp2;

        // ���� K = (h - r*g) * d_inv
        ECn K = tmp;
        K *= d_inv;

        // ˽Կ�ַ����˴���ģ�⣩
        cout << "�û� " << userIDs[j] << " ��˽Կ�����ɣ�" << endl;
        cout << "    r = " << r << endl;
        cout << "    K = " << K << endl;
        cout << "˽Կ��ͨ����ȫ�ŵ����͸��û� " << userIDs[j] << endl;
    }

    // ===============================================================
    cout << "PKISI �û�˽Կ������ɣ�" << endl;
    sk_ts.s = rand(q);

    cout << "sk_ts.s= " << sk_ts.s << endl;

    params.g1 = sk_ts.s * params.g;
    Big k1= rand(q);
    Big k2 = rand(q);





    // -----------------------------------------
// ���ܹ��̣��������� (c1, c2, c3, c4, c5)
// ����ʹ���Զ������Ժ��� ecap �����Լ���

    // --------------------- ���� c2 ---------------------
    ecap(params.g, params.g, q, cube, params.e_g_g);
    // ���� c2 = (e(g, g))^(k1)
    ZZn2 c2 = pow(params.e_g_g, k1);


    // --------------------- ���� c1 ---------------------
    // ����ʱ����ַ��� T�������� H(T)������ʹ�� H1() �������й�ϣ����� Big ���ͣ�
    char T[9] = "20241212";
    Big hashT = H1(T);
    cout << hashT << endl;

    // ���� c1 = k1*g1 - k1*H(T)*g
    ECn c1 = params.g1;
    c1 *= k1;
    ECn tmp = params.g;

    // �ȼ��� k1 * hashT �ĳ˻��������м����
    Big scalar = k1 * hashT;
    tmp *= scalar;  // ʹ���м�������е�ı����˷�

    c1 -= tmp;


    // --------------------- ���� c3 ---------------------
    // ����ʱ���������ݱ�ʶ ID_s�������� H(ID_s)
// ������ݱ�ʶ������ʹ��ǰ�� 257 ������ u[0]���� u[0] ת��Ϊ�ַ�����ʾ
    std::string idStr = pointToString(params.u[0]);
    Big hashID = H1((char*)idStr.c_str());

    // ���� c3 = k2*g1 - k2*H(ID_s)*g
    ECn c3 = params.g1;
    c3 *= k2;
    tmp = params.g;
    tmp *= (k2 * hashID);
    c3 -= tmp;

    // --------------------- ���� c4 ---------------------
    // ��� u[0]��Ӧ����ݣ��������һ�� r_id_s ���� c4
    Big r_id_s = rand(q);
    // ���� c4 = (e(g, g))^(k2 * r_id_s)
    // �����������֮ǰ����� base1���� e(g, g)
    ZZn2 c4 = pow(params.e_g_g, k2 * r_id_s);

    // --------------------- ���� c5 ---------------------
    // ������� e(g, h) ʹ�� ecap �滻 pairing(params.g, params.h)
    ZZn2 pairing_gh;
    if (!ecap(params.g, params.h, q, cube, pairing_gh))
    {
        cout << "Error computing ecap(params.g, params.h)" << endl;
        exit(1);
    }

    // ��ȡ��������Ϣ M����ͨ�� hash_to_GT() ӳ�䵽Ŀ��Ⱥ�ڣ�����Ϊ ZZn2��
    ZZn2 M_GT = 123;  // ���� hash_to_GT() ���������ַ������� ZZn2 Ԫ��

    // ���� c5 = M * (e(g, h))^-(k1+k2)
    Big exp = k1 + k2;
    ZZn2 factor = pow(pairing_gh, exp);
    factor = inverse(factor);  // �õ� (e(g, h))^-(k1+k2)
    ZZn2 c5 = M_GT * factor;

    // -----------------------------------------
    // ������ĸ�����
    cout << "���ܺ������Ϊ:" << endl;
    cout << "c1 = " << c1 << endl;  // ��Բ�����ϵĵ����� ECn
    cout << "c2 = " << c2 << endl;  // Ŀ��Ⱥ ZZn2 ����
    cout << "c3 = " << c3 << endl;
    cout << "c4 = " << c4 << endl;
    cout << "c5 = " << c5 << endl;


    return 0;


















    

    // ���ṹ��д���ļ�  
    outputFile1.write(reinterpret_cast<char*>(&CT3), sizeof(CT3));

    outputFile1.close(); // �ر��ļ�  
    std::cout << "�ṹ���ѳɹ�д���ļ�1" << std::endl;

    // ���ṹ��д���ļ�  
    outputFile2.write(reinterpret_cast<char*>(&st_TimeNow), sizeof(st_TimeNow));

    outputFile2.close(); // �ر��ļ�  
    std::cout << "�ṹ���ѳɹ�д���ļ�1" << std::endl;

    // ���ṹ��д���ļ�  
    outputFile3.write(reinterpret_cast<char*>(&CT1111), sizeof(CT1111));

    outputFile3.close(); // �ر��ļ�  
    std::cout << "�ṹ���ѳɹ�д���ļ�1" << std::endl;



    //return 0;
}


	