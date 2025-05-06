/*
 *    MIRACL  C++  functions ecn.cpp
 *
 *    AUTHOR  :    M. Scott
 *             
 *    PURPOSE :    Implementation of class ECn functions using Montgomery
 *                 representation
 *    NOTE    :    Must be used in conjunction with big.h and big.cpp
 *
 *    Copyright (c) 1988-2004 Shamus Software Ltd.
 */

#include "ecn.h"

int ECn::get(Big& x,Big& y) const 
        {return epoint_get(p,x.getbig(),y.getbig());}
int ECn::get(Big& x) const   
        {return epoint_get(p,x.getbig(),x.getbig());}
void ECn::getx(Big &x) const
        {epoint_getxyz(p,x.getbig(),NULL,NULL);}
void ECn::getxy(Big &x,Big &y) const
        {epoint_getxyz(p,x.getbig(),y.getbig(),NULL);}
void ECn::getxyz(Big &x,Big &y, Big &z) const
        {epoint_getxyz(p,x.getbig(),y.getbig(),z.getbig());}


BOOL ECn::iszero() const
        {if (p->marker==MR_EPOINT_INFINITY) return TRUE; return FALSE;}

epoint * ECn::get_point() const
{ return p; }

ECn operator-(const ECn& e)
{ ECn t=e; epoint_negate(t.p); return t;}

ECn mul(const Big& e1,const ECn& p1,const Big& e2,const ECn& p2)
{ 
    ECn t; 
    ecurve_mult2(e1.getbig(),p1.get_point(),e2.getbig(),p2.get_point(),t.get_point());
    return t;
}

ECn operator*(const Big& e,const ECn& b)
{
    ECn t;
    ecurve_mult(e.getbig(),b.p,t.p);
    return t;
}
/*---------yk增加的异或运算符重载:由于点异或运算效率不高，且带来实现表示的不方便（由于异或后的点很可能不在椭圆曲线上，导致系统将其值置为（0,0）），修改方案中的异或为点加运算,不再使用该操作，除非是不强行置（0,0）的大整数库，PBC库是否满足？-------------------------------------------------*/
//ECn operator^(const ECn& a,const ECn& b)
//void ecn_xor(const ECn& a,const ECn& b,Big& c, Big& d)
void ecn_xor(Big& px,Big& py,Big& qx,Big& qy)
{
	int i;
/*————————————方法1：使用较多空间,耗时比重0.00179———————————————————*/
	char ptrpx[64]={0},ptrpy[64]={0},ptrqx[64]={0},ptrqy[64]={0};
	BOOL justify=1;
	big_to_bytes(64,px.getbig(),ptrpx,justify);//大整数转换为二进制
	big_to_bytes(64,py.getbig(),ptrpy,justify);
	big_to_bytes(64,qx.getbig(),ptrqx,justify);
	big_to_bytes(64,qy.getbig(),ptrqy,justify);

	for(i=0;i<64;i++)//实现异或
		{
			ptrqx[i]=ptrpx[i]^ptrqx[i];//测试是否实现了异或，经测试，成功实现了异或
			ptrqy[i]=ptrpy[i]^ptrqy[i];
	    }
	bytes_to_big(64,ptrqx,qx.getbig());//实现二进制转换为大整数
	bytes_to_big(64,ptrqy,qy.getbig());//实现二进制转换为大整数*/
/*————————————方法2：使用较少空间,耗时比重0.00179———————————————————*/
	/*char ptr1[64]={0},ptr2[64]={0};
	BOOL justify=1;
	big_to_bytes(64,px.getbig(),ptr1,justify);//大整数转换为二进制
	big_to_bytes(64,qx.getbig(),ptr2,justify);
	for(i=0;i<64;i++)//实现异或
		ptr2[i]=ptr1[i]^ptr2[i];//测试是否实现了异或，经测试，成功实现了异或
	bytes_to_big(64,ptr2,qx.getbig());//实现二进制转换为大整数

    big_to_bytes(64,py.getbig(),ptr1,justify);//大整数转换为二进制
	big_to_bytes(64,qy.getbig(),ptr2,justify);
	for(i=0;i<64;i++)//实现异或
		ptr2[i]=ptr1[i]^ptr2[i];//测试是否实现了异或，经测试，成功实现了异或
	bytes_to_big(64,ptr2,qy.getbig());//实现二进制转换为大整数*/







	
	/*int i;
	big px,py,qx,qy,tx,ty;
	char ptrpx[64]={0},ptrpy[64]={0},ptrqx[64]={0},ptrqy[64]={0},ptrtx[64]={0},ptrty[64]={0};
	BOOL justify=1;
	px=mirvar(0);  // all big variables need to be "mirvar"ed 
    py=mirvar(0);
	qx=mirvar(0);  // all big variables need to be "mirvar"ed 
    qy=mirvar(0);
	tx=mirvar(0);  // all big variables need to be "mirvar"ed 
    ty=mirvar(0);

	epoint_get(a.get_point(),px,py);//取坐标
	epoint_get(b.get_point(),qx,qy);

	//cotnum(px,stdout);//输出大整数测试
	//cotnum(py,stdout);//
	//cotnum(qx,stdout);//输出大整数测试
	//cotnum(qy,stdout);//

	big_to_bytes(64,px,ptrpx,justify);//大整数转换为二进制
	big_to_bytes(64,py,ptrpy,justify);
	big_to_bytes(64,qx,ptrqx,justify);
	big_to_bytes(64,qy,ptrqy,justify);

	/*bytes_to_big(64,ptrpx,px);//实现二进制转换为大整数
	bytes_to_big(64,ptrpy,py);
	bytes_to_big(64,ptrqx,qx);//实现二进制转换为大整数
	bytes_to_big(64,ptrqy,qy);

	cotnum(px,stdout);//输出大整数测试
	cotnum(py,stdout);//
	cotnum(qx,stdout);//输出大整数测试
	cotnum(qy,stdout);//*/

	
	//bytes_to_big(64,ptrpx,px);//测试是否实现了异或，经测试，成功实现了异或
	//bytes_to_big(64,ptrpy,py);//测试是否实现了异或，经测试，成功实现了异或

	//cotnum(tx,stdout);//输出大整数测试
	//cotnum(ty,stdout);//
	//cotnum(px,stdout);//测试是否实现了异或，经测试，成功实现了异或
	//cotnum(py,stdout);//测试是否实现了异或，经测试，成功实现了异或

	//c=tx;
	//d=ty;
	///cotnum(c.getbig(),stdout);//输出大整数测试
	//cotnum(d.getbig(),stdout);//

	//epoint_set(tx,ty,1,t.get_point());//实现为点坐标赋值
	//epoint_get(t.get_point(),tx,ty);
	//big_to_bytes(64,tx,ptrtx,justify);
	//big_to_bytes(64,ty,ptrty,justify);
	//for (i=0;i<64;i++) printf("%02x",ptrtx[i]);
	//printf("\n");
	//for (i=0;i<64;i++) printf("%02x",ptrty[i]);
	//printf("\n");
	//return t;//由于t是其他两点异或的结果，因此，t可能不在椭圆曲线上，导致输出为：Infinity，认为其是无穷远点。
 
}
/*---------------------------------------------------------------------自己增加的异或运算符重载-------------------------------------------------------------------------------------------------*/
/*ECn operator^(const ECn& a,const ECn& b)
//void ecn_xor(const ECn& a,const ECn& b,Big& c, Big& d)
{
	ECn t;
    int i;
	big px,py,qx,qy,tx,ty;
	char ptrpx[64]={0},ptrpy[64]={0},ptrqx[64]={0},ptrqy[64]={0},ptrtx[64]={0},ptrty[64]={0};
	BOOL justify=1;
	px=mirvar(0);  // all big variables need to be "mirvar"ed 
    py=mirvar(0);
	qx=mirvar(0);  // all big variables need to be "mirvar"ed 
    qy=mirvar(0);
	tx=mirvar(0);  // all big variables need to be "mirvar"ed 
    ty=mirvar(0);

	epoint_get(a.get_point(),px,py);//取坐标
	epoint_get(b.get_point(),qx,qy);

	cotnum(px,stdout);//输出大整数测试
	cotnum(py,stdout);//
	cotnum(qx,stdout);//输出大整数测试
	cotnum(qy,stdout);//

	big_to_bytes(64,px,ptrpx,justify);//大整数转换为二进制
	big_to_bytes(64,py,ptrpy,justify);
	big_to_bytes(64,qx,ptrqx,justify);
	big_to_bytes(64,qy,ptrqy,justify);

	/*bytes_to_big(64,ptrpx,px);//实现二进制转换为大整数
	bytes_to_big(64,ptrpy,py);
	bytes_to_big(64,ptrqx,qx);//实现二进制转换为大整数
	bytes_to_big(64,ptrqy,qy);

	cotnum(px,stdout);//输出大整数测试
	cotnum(py,stdout);//
	cotnum(qx,stdout);//输出大整数测试
	cotnum(qy,stdout);//*/

	/*for(i=0;i<64;i++)//实现异或
		{
			ptrtx[i]=ptrpx[i]^ptrqx[i];
			ptrty[i]=ptrpy[i]^ptrqy[i];
			//ptrtx[i]=ptrpx[i]^0;
			//ptrty[i]=ptrpy[i]^0;
	    }
	/*for (i=0;i<64;i++) printf("%02x",ptrtx[i]);
	printf("\n");
	for (i=0;i<64;i++) printf("%02x",ptrty[i]);
	printf("\n");
	bytes_to_big(64,ptrtx,tx);//实现二进制转换为大整数
	bytes_to_big(64,ptrty,ty);
	big_to_bytes(64,tx,ptrtx,justify);
	big_to_bytes(64,ty,ptrty,justify);
	for (i=0;i<64;i++) printf("%02x",ptrtx[i]);
	printf("\n");
	for (i=0;i<64;i++) printf("%02x",ptrty[i]);
	printf("\n");*/

	/*bytes_to_big(64,ptrtx,tx);//实现二进制转换为大整数
	bytes_to_big(64,ptrty,ty);
	

	cotnum(tx,stdout);//输出大整数测试
	cotnum(ty,stdout);//

	epoint_set(tx,ty,1,t.get_point());//实现为点坐标赋值
	//epoint_get(t.get_point(),tx,ty);
	//big_to_bytes(64,tx,ptrtx,justify);
	//big_to_bytes(64,ty,ptrty,justify);
	//for (i=0;i<64;i++) printf("%02x",ptrtx[i]);
	//printf("\n");
	//for (i=0;i<64;i++) printf("%02x",ptrty[i]);
	//printf("\n");
	return t;//由于t是其他两点异或的结果，因此，t可能不在椭圆曲线上，导致输出为：Infinity，认为其是无穷远点。
	
	
	
	
	/* ECn t;
	int i;
	big px,py,qx,qy,tx,ty;
	char ptrpx[64],ptrpy[64],ptrqx[64],ptrqy[64],ptrtx[64],ptrty[64];
	BOOL justify=1;
	px=mirvar(0);  // all big variables need to be "mirvar"ed 
    py=mirvar(0);
	qx=mirvar(0);  // all big variables need to be "mirvar"ed 
    qy=mirvar(0);
	tx=mirvar(0);  // all big variables need to be "mirvar"ed 
    ty=mirvar(0);

	epoint_get(a.get_point(),px,py);//取坐标
	epoint_get(b.get_point(),qx,qy);

	big_to_bytes(64,px,ptrpx,justify);//大整数转换为二进制
	big_to_bytes(64,py,ptrpy,justify);
	big_to_bytes(64,qx,ptrqx,justify);
	big_to_bytes(64,qy,ptrqy,justify);

	for(i=0;i<64;i++)//实现异或
		{
			ptrtx[i]=ptrpx[i]^ptrqx[i];
			ptrty[i]=ptrpy[i]^ptrqy[i];
	    }
	for (i=0;i<64;i++) printf("%02x",ptrtx[i]);
	printf("\n");
	for (i=0;i<64;i++) printf("%02x",ptrty[i]);
	printf("\n");
	bytes_to_big(64,ptrtx,tx);//实现二进制转换为大整数
	bytes_to_big(64,ptrty,ty);
	big_to_bytes(64,tx,ptrtx,justify);
	big_to_bytes(64,ty,ptrty,justify);
	for (i=0;i<64;i++) printf("%02x",ptrtx[i]);
	printf("\n");
	for (i=0;i<64;i++) printf("%02x",ptrty[i]);
	printf("\n");
	bytes_to_big(64,ptrtx,tx);//实现二进制转换为大整数
	bytes_to_big(64,ptrty,ty);

	epoint_set(tx,ty,1,t.get_point());//实现为点坐标赋值
	epoint_get(t.get_point(),tx,ty);
	big_to_bytes(64,tx,ptrtx,justify);
	big_to_bytes(64,ty,ptrty,justify);
	for (i=0;i<64;i++) printf("%02x",ptrtx[i]);
	printf("\n");
	for (i=0;i<64;i++) printf("%02x",ptrty[i]);
	printf("\n");
	return t;*/
	/*epoint_get(a.get_point(),px,py);//输出测试表明，epoint_get(a.get_point(),px,py)是实现提取点坐标的函数，而并不是：px=(a.get_point())->X;py=(a.get_point())->Y;
	//px=(a.get_point())->X;//不是实现取坐标的语句
	//py=(a.get_point())->Y;//不是实现取坐标的语句
	big_to_bytes(64,px,ptrpx,justify);
	big_to_bytes(64,py,ptrpy,justify);
	for (i=0;i<64;i++) printf("%02x",ptrpx[i]);
	printf("\n");
	for (i=0;i<64;i++) printf("%02x",ptrpy[i]);
	printf("\n");
	epoint_set(px,py,1,a.get_point());*/

    /*px=(a.get_point())->X;
	py=(a.get_point())->Y;
	qx=(b.get_point())->X;
	qy=(b.get_point())->Y;
	big_to_bytes(64,px,ptrpx,justify);
	//for (i=0;i<64;i++) printf("%02x",ptrpx[i]);
   // printf("\n");
	big_to_bytes(64,py,ptrpy,justify);
	big_to_bytes(64,qx,ptrqx,justify);
	big_to_bytes(64,qy,ptrqy,justify);

	for (i=0;i<64;i++) printf("%02x",ptrpx[i]);
	printf("\n");
	for (i=0;i<64;i++) printf("%02x",ptrpy[i]);
	printf("\n");
	for (i=0;i<64;i++) printf("%02x",ptrqx[i]);
	printf("\n");
	for (i=0;i<64;i++) printf("%02x",ptrqy[i]);
	printf("\n");


		tx=(t.get_point())->X;
		ty=(t.get_point())->Y;
	big_to_bytes(64,tx,ptrtx,justify);
	big_to_bytes(64,ty,ptrty,justify);
	for (i=0;i<64;i++) printf("%02x",ptrtx[i]);
	printf("\n");
	for (i=0;i<64;i++) printf("%02x",ptrty[i]);
	printf("\n");


	for(i=0;i<64;i++)
		{
			*(ptrtx+i)=*(ptrpx+i)^*(ptrqx+i);
			*(ptrty+i)=*(ptrpy+i)^*(ptrqy+i);
	    }
	for (i=0;i<64;i++) printf("%02x",ptrtx[i]);
    printf("\n");
	bytes_to_big(64,ptrtx,tx);
	bytes_to_big(64,ptrty,ty);
	//(t.get_point())->X=tx;
	//(t.get_point())->Y=ty;
	//t.set(tx,ty);
	tx=(t.get_point())->X;
	big_to_bytes(64,tx,ptrtx,justify);
	for (i=0;i<64;i++) printf("%02x",ptrtx[i]);//
	printf("\n");
	ty=(t.get_point())->Y;
	big_to_bytes(64,ty,ptrty,justify);
	for (i=0;i<64;i++) printf("%02x",ptrty[i]);//

    printf("\n");
   
}*/
/*---------------------------------------------------------------------yk增加的异或运算符重载-------------------------------------------------------------------------------------------------*/
/*------------------------------------------------------------------  ---yk增加的点加函数-------------------------------------------------------------------------------------------------*/
 ECn operator+(const ECn& b1, const ECn& b2)
{ ecurve_add(b1.p,b2.p); return  b2;}
/*------------------------------------------------------------------  ---yk增加的点加函数-------------------------------------------------------------------------------------------------*/
 /*------------------------------------------------------------------  ---yk增加的点减函数-------------------------------------------------------------------------------------------------*/
 ECn operator-(const ECn& b1, const ECn& b2)
{ ecurve_sub(b2.p,b1.p); return  b1;}
/*------------------------------------------------------------------  ---yk增加的点减函数-------------------------------------------------------------------------------------------------*/

#ifndef MR_STATIC

ECn mul(int n,const Big *y,ECn *x)
{
    ECn w;
    int i;
    big *a=(big *)mr_alloc(n,sizeof(big));
    epoint **b=(epoint **)mr_alloc(n,sizeof(epoint *));
    for (i=0;i<n;i++)
    {
        a[i]=y[i].getbig();
        b[i]=x[i].p;
    }
    ecurve_multn(n,a,b,w.p);

    mr_free(b);
    mr_free(a);
    return w;  
}

void multi_add(int m,ECn *x, ECn *w)
{
    int i;
    epoint **xp=(epoint **)mr_alloc(m,sizeof(epoint *));
    epoint **wp=(epoint **)mr_alloc(m,sizeof(epoint *));
    for (i=0;i<m;i++)
    {
        xp[i]=x[i].p;
        wp[i]=w[i].p;
    }
    ecurve_multi_add(m,xp,wp);
    mr_free(wp);
    mr_free(xp);
}

#endif

void double_add(ECn& A,ECn& B,ECn& C,ECn& D,big& s1,big& s2)
{
    ecurve_double_add(A.p,B.p,C.p,D.p,&s1,&s2);
}

#ifndef MR_NO_STANDARD_IO

ostream& operator<<(ostream& s,const ECn& b)
{
    Big x,y;
    if (b.iszero())
        s << "(Infinity)";
    else
    {
        b.get(x,y);
        s << "(" << x << "," << y << ")";
    }
    return s;
}

#endif

void ecurve(const Big& a,const Big& b,const Big& p,int t)
{
    ecurve_init(a.fn,b.fn,p.fn,t);
}

#ifndef MR_NOSUPPORT_COMPRESSION
#ifndef MR_NOTESTXONCURVE


BOOL is_on_curve(const Big& a)
{ return epoint_x(a.fn);}

#endif
#endif
