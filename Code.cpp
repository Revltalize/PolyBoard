/*

POLYBOARD (1.5.0)
_____________________________________________
|                                            |
|  AUTHER   : Revitalize                     |
|  Nation   : China                          |
|  Province : Shaanxi                        |
|  School   : Middle School Attached to NPU  |
|  LOCATION : Shaoxing No.1 Middle School    |
|  TIME     : 2025/7/16                      |
|____________________________________________|


Menu:
IO ------------------------ Fastio (From:luuia)
Pre ----------------------- Preworks
    | Q ----------------------- Fastpow
    | Inv --------------------- Get number theory inv
    | initYG ------------------ Serve for NTT
Pint ---------------------- Integers Calculate in Modulo
    | addt -------------------- Plus to
    | delt -------------------- Minus to
    | add --------------------- Plus
    | del --------------------- Minus
    | tp ---------------------- To Positive
    | Vmax -------------------- Manumax
Quad ----------------------- Quadratic Residue
    | NTC --------------------- Manucomplex
    | Q ----------------------- Fastpow with Any Modulo
    | q ----------------------- Conplex Fastpow
    | Cipolla ----------------- Cipolla (
    | work -------------------- Get Quadratic Residue
POLY ----------------------- POLY
    | PIO --------------------- Poly Input/Output
        | pin --------------------- Statement of Input
        | pout -------------------- Statement of Output
    | Poly -------------------- Class of Poly
        | resize ------------------ Resize ans Shrink
        | shrink ------------------ Update n
        | rev --------------------- Reverse
        | pb ---------------------- Push Back
        | tp ---------------------- To Positive
        | NTT --------------------- NTT (
UCPF ----------------------- Unclassable Polyfunctions
    | Dx ----------------------- Get Derivative
    | Integ -------------------- Get Integral
    | Ln ----------------------- Get Logarithm of e
    | Exp ---------------------- Get Power of e
    | Sqrt --------------------- Get Sqrt

Update:
ARCTri.




*/

#include <bits/stdc++.h>
using namespace std;
namespace IO
{
    const int __SIZE = (1 << 21) + 1;
    char ibuf[__SIZE], *iS, *iT, obuf[__SIZE], *oS = obuf, *oT = oS + __SIZE - 1, _c, qu[55];
    int __f, qr, _eof;
#define Gc() (iS == iT ? (iT = (iS = ibuf) + fread(ibuf, 1, __SIZE, stdin), (iS == iT ? EOF : *iS++)) : *iS++)

    inline void flush()
    {
        fwrite(obuf, 1, oS - obuf, stdout);
        oS = obuf;
    }

    inline void gc(char &x)
    {
        x = Gc();
    }

    inline void pc(char x)
    {
        *oS++ = x;
        if (oS == oT)
        {
            flush();
        }
    }

    inline void pstr(const char *s)
    {
        int __len = strlen(s);
        for (__f = 0; __f < __len; ++__f)
        {
            pc(s[__f]);
        }
    }

    inline void gstr(char *s)
    {
        for (_c = Gc(); _c < 32 || _c > 126 || _c == ' ';)
        {
            _c = Gc();
        }
        for (; _c > 31 && _c < 127 && _c != ' ' && _c != '\n' && _c != '\r'; ++s, _c = Gc())
        {
            *s = _c;
        }
        *s = 0;
    }

    template <class I>
    inline bool read(I &x)
    {
        _eof = 0;
        for (__f = 1, _c = Gc(); (_c < '0' || _c > '9') && !_eof; _c = Gc())
        {
            if (_c == '-')
            {
                __f = -1;
            }
            _eof |= _c == EOF;
        }
        for (x = 0; _c <= '9' && _c >= '0' && !_eof; _c = Gc())
        {
            x = x * 10 + (_c & 15), _eof |= _c == EOF;
        }
        x *= __f;
        return !_eof;
    }

    template <class I>
    inline void print(I x)
    {
        if (!x)
        {
            pc('0');
        }
        if (x < 0)
        {
            pc('-');
            x = -x;
        }
        while (x)
        {
            qu[++qr] = x % 10 + '0', x /= 10;
        }
        while (qr)
        {
            pc(qu[qr--]);
        }
    }

    struct Flusher_
    {
        ~Flusher_() { flush(); }
    } io_flusher_;
}
using IO::gc;
using IO::gstr;
using IO::pc;
using IO::print;
using IO::pstr;
using IO::read;

const constexpr int P = 998244353, Y = 3, I = 332748118, B = (P + 1) >> 1, N = 600005, _I_ = 86583718;

namespace Pre
{
    int gp[N], igp[N], ny[N], inv[N];

    inline int Q(int a, int b)
    {
        int res = 1;
        while (b)
        {
            if (b & 1)
            {
                res = 1ll * res * a % P;
            }
            a = 1ll * a * a % P, b >>= 1;
        }
        return res % P;
    }

    inline int Inv(int __x)
    {
        if (__x <= 500000)
        {
            return ny[__x];
        }
        return Q(__x, P - 2);
    }

    inline void initYG()
    {
        int tmpg = Q(Y, (P - 1) / (1 << 19)), tmpig = Q(I, (P - 1) / (1 << 19));
        gp[0] = igp[0] = 1;
        for (register int i = 1; i <= (1 << 19); ++i)
        {
            gp[i] = 1ll * tmpg * gp[i - 1] % P;
            igp[i] = 1ll * tmpig * igp[i - 1] % P;
        }
        ny[1] = 1;
        for (int i = 2; i <= 500010; ++i)
        {
            ny[i] = 1ll * (P - P / i) * ny[P % i] % P;
        }
        inv[1] = 1;
        inv[2] = 499122177;
        inv[4] = 748683265;
        inv[8] = 873463809;
        inv[16] = 935854081;
        inv[32] = 967049217;
        inv[64] = 982646785;
        inv[128] = 990445569;
        inv[256] = 994344961;
        inv[512] = 996294657;
        inv[1024] = 997269505;
        inv[2048] = 997756929;
        inv[4096] = 998000641;
        inv[8192] = 998122497;
        inv[16384] = 998183425;
        inv[32768] = 998213889;
        inv[65536] = 998229121;
        inv[131072] = 998236737;
        inv[262144] = 998240545;
        inv[524288] = 998242449;
    }
}

namespace Pint
{
    template <class T>
    inline T addt(T &__a, T __b)
    {
        if ((__a += __b) >= P)
        {
            __a -= P;
        }
        return __a;
    }

    template <class T>
    inline T delt(T &__a, T __b)
    {
        if ((__a -= __b) < 0)
        {
            __a += P;
        }
        return __a;
    }

    template <class T>
    inline T add(T __a, T __b)
    {
        return addt(__a, __b);
    }

    template <class T>
    inline T del(T __a, T __b)
    {
        return delt(__a, __b);
    }

    inline int tp(int x)
    {
        if (x < 0)
        {
            x += P;
        }
        return x;
    }

    template <class T>
    inline T Vmax(T a, T b)
    {
        return ((a > b) ? a : b);
    }
}

using namespace Pint;
mt19937 rnd(time(0));
namespace Quad
{
    int t, n, p = 998244353, ii;

    struct NTC
    {
        int Re, Im;
        NTC operator*(NTC __A) const
        {
            NTC __res;
            __res.Re = (1ll * Re * __A.Re % p + 1ll * ii * Im % p * __A.Im % p + p) % p;
            __res.Im = (1ll * Re * __A.Im % p + 1ll * Im * __A.Re % p + p) % p;
            return __res;
        }
    };
    inline int Q(int __a, int __b, int __p)
    {
        int __res = 1;
        while (__b)
        {
            if (__b & 1)
            {
                __res = 1ll * __res * __a % __p;
            }
            __a = 1ll * __a * __a % __p;
            __b >>= 1;
        }
        return __res % __p;
    }

    inline NTC q(NTC __a, int __b, int &__p)
    {
        NTC __res = {1, 0};
        while (__b)
        {
            if (__b & 1)
            {
                __res = __res * __a;
            }
            __a = __a * __a;
            __b >>= 1;
        }
        return __res;
    }
    inline int Cipolla(int n, int p)
    {
        p = 998244353;
        n %= p;
        if (Q(n, (p - 1) >> 1, p) == p - 1)
            return -1;
        int a;
        while (true)
        {
            a = rnd() % p;
            ii = ((1ll * a * a % p - n + p) % p + p) % p;
            if (Q(ii, (p - 1) >> 1, 998244353) == p - 1)
                break;
        }
        NTC x = {a, 1};
        return (q(x, B, p).Re % p + p) % p;
    }
    inline int work(int n, int p)
    {
        if (!n)
        {
            return 0;
        }
        int u = Cipolla(n, p), v = p - u;
        if (u == -1)
        {
            return 998244354;
        }
        u = (u + p) % p;
        v = (v + p) % p;
        if (u > v)
            swap(u, v);
        return u;
    }
}

namespace POLY
{
    int __Binary_reverse[2000005];
    class poly;

    namespace PIO
    {
        void pin(poly &f, int __n);
        void ppri(poly __f, int __n);
    }

    namespace UCPF
    {
        inline poly Ln(poly __f);
        inline poly Exp(poly __f);
        inline poly Sqrt(poly __f);
        inline poly Sin(poly __f);
        inline poly Cos(poly __f);
        inline poly Tan(poly __f);
        inline poly ArcSin(poly __f);
        inline poly ArcCos(poly __f);
        inline poly ArcTan(poly __f);
    }
    using namespace UCPF;
    using namespace PIO;

    class poly
    {
    public:
        int n;
        vector<int> a;
        poly()
        {
            n = 0;
        }
        poly(int __n)
        {
            resize(__n);
        }

        int &operator[](int id)
        {
            return a[id];
        }

        inline void resize(int __lim_siz)
        {
            a.resize(__lim_siz);
            a.shrink_to_fit();
            n = __lim_siz;
        }

        inline void shrink()
        {
            resize(n);
        }

        inline void rev(vector<int>::iterator __st, vector<int>::iterator __en)
        {
            reverse(__st, __en);
        }

        inline void pb(int x)
        {
            a.push_back(x);
            ++n;
        }

        inline void tp(int __n)
        {
            for (register int i = 0; i < __n; ++i)
            {
                Pint::tp(a[i]);
            }
        }

        poly operator+=(const poly &__tmpa)
        {
            int nm = Vmax(n, __tmpa.n);
            resize(nm);
            for (register int i = 0; i < nm; ++i)
            {
                a[i] = add((i < __tmpa.n) ? __tmpa.a[i] : 0, (i < n) ? a[i] : 0);
            }
            return *this;
        }

        poly operator-=(const poly &__tmpa)
        {
            int nm = Vmax(n, __tmpa.n);
            resize(nm);
            for (register int i = 0; i < nm; ++i)
            {
                a[i] = del((i < n) ? a[i] : 0, (i < __tmpa.n) ? __tmpa.a[i] : 0);
            }
            return *this;
        }

        poly operator+(poly __tmpa) const
        {
            poly __tmp = *this;
            return (__tmpa += __tmp);
        }

        poly operator-(poly __tmpa) const
        {
            poly __tmp = *this;
            return (__tmp -= __tmpa);
        }

        inline void NTT(bool __)
        {
            for (register int i = 0; i < n; ++i)
            {
                if (i < __Binary_reverse[i])
                {
                    swap(a[i], a[__Binary_reverse[i]]);
                }
            }
            for (register int r = 1, base = (1 << 18); r < n; r <<= 1, base >>= 1)
            {
                for (register int i = 0; i < n; i += (r << 1))
                {
                    for (register int j = 0, bj = 0; j < r; ++j, bj += base)
                    {
                        int __I = a[j | i], __II = 1ll * (__ ? Pre::gp[bj] : Pre::igp[bj]) * a[j | r | i] % P;
                        a[j | i] = add(__I, __II);
                        a[j | r | i] = del(__I, __II);
                    }
                }
            }
            if (!__)
            {
                long long invtmp = Pre::inv[n];
                for (register int i = 0; i < n; ++i)
                {
                    a[i] = a[i] * invtmp % P;
                }
            }
            tp(n);
        }

        poly operator*=(const poly &__tmpa)
        {
            poly __tmpmuly = __tmpa;
            int __siz = n + __tmpa.n - 1;
            int __len = 1, __L = 0;
            while (__len < n + __tmpa.n)
            {
                __len <<= 1;
                __L++;
            }
            for (register int i = 1; i < __len; ++i)
            {
                __Binary_reverse[i] = (__Binary_reverse[i >> 1] >> 1) | ((i & 1) << (__L - 1));
            }
            resize(__len);
            __tmpmuly.resize(__len);
            NTT(1);
            __tmpmuly.NTT(1);
            for (register int i = 0; i < __len; ++i)
            {
                a[i] = 1ll * a[i] * __tmpmuly[i] % P;
            }
            NTT(0);
            resize(__siz);
            return *this;
        }

        poly operator*=(const int __tmpa)
        {
            for (register int i = 0; i < n; ++i)
            {
                a[i] = 1ll * a[i] * __tmpa % P;
            }
            return *this;
        }

        template <class T>
        poly operator*(const T &__tmpa) const
        {
            poly ans = *this;
            return ans *= __tmpa;
        }

        poly operator&(const poly &__tmpa) const
        {
            poly __tmpmulx = *this, __tmpmuly = __tmpa;
            int nnn = a.size(), mmm = __tmpa.a.size();
            int len = 1, L = 0;
            while (len < nnn)
            {
                len <<= 1;
                L++;
            }
            for (register int i = 1; i < len; ++i)
            {
                __Binary_reverse[i] = (__Binary_reverse[i >> 1] >> 1) | ((i & 1) << (L - 1));
            }
            __tmpmulx.resize(len);
            __tmpmuly.resize(len);
            __tmpmulx.NTT(1);
            __tmpmuly.NTT(1);
            poly res(len);
            for (register long long i = 0; i < len; ++i)
            {
                res[i] = 1ll * ((1ll * __tmpmulx[i] * __tmpmuly[i] % P) + P) % P;
            }
            res.NTT(0);
            poly ans(nnn - mmm + 1);
            for (register int __i = mmm - 1; __i < nnn; __i++)
            {
                ans[__i - mmm + 1] = res[__i];
            }
            return ans;
        }

        poly operator~() const
        {
            poly __f = *this, __tmpf;
            int cst = __f.a[0];
            int L = 0;
            poly ans;
            int dep = 1;
            ans.pb(Pre::Inv(cst));
            while (dep < (n << 1))
            {
                ++L;
                for (register int i = 1; i < (dep << 1); ++i)
                {
                    __Binary_reverse[i] = (__Binary_reverse[i >> 1] >> 1) | ((i & 1) << (L - 1));
                }
                __tmpf.a.clear();
                __tmpf = *this;
                __tmpf.resize(dep);
                __tmpf.resize(dep << 1);
                if (dep != 1)
                {
                    ans.resize(dep >> 1);
                }
                ans.resize(dep << 1);
                __tmpf.NTT(1);
                ans.NTT(1);
                for (register int i = 0; i < (dep << 1); ++i)
                {
                    ans[i] = 1ll * ans[i] * Pint::tp(2ll - 1ll * __tmpf[i] * ans[i] % P + P) % P;
                }
                ans.NTT(0);
                ans.resize(dep << 1);
                ans.tp(ans.n);
                dep <<= 1;
            }
            ans.resize(n);
            return ans;
        }

        poly operator/=(poly g)
        {
            rev(a.begin(), a.end());
            g.rev(g.a.begin(), g.a.end());
            int m = g.n;
            g.resize(n - m + 1);
            poly q = ~g * *this;
            q.rev(q.a.begin(), q.a.begin() + n - m + 1);
            return q;
        }

        poly operator/=(int g)
        {
            for (register int i = 0; i < n; ++i)
            {
                a[i] = 1ll * a[i] * Pre::Inv(g) % P;
            }
            tp(n);
            return *this;
        }

        template <class T>
        poly operator/(T &g) const
        {
            poly res = *this;
            return res /= g;
        }

        poly operator%=(poly g) const
        {
            poly q = *this / g;
            q.resize(n - g.n + 1);
            return *this - q * g;
        }

        poly operator%(poly g) const
        {
            poly res = *this;
            return res %= g;
        }

        poly operator^=(int g)
        {
            *this = Ln(*this);
            *this *= g;
            *this = Exp(*this);
            return *this;
        }

        poly operator^(int g) const
        {
            poly res = *this;
            return res ^= g;
        }
    };
}

using namespace POLY;
inline poly Dx(poly &__f)
{
    poly ans;
    for (register int i = 1; i < __f.n; ++i)
    {
        ans.pb(1ll * i * __f[i] % P);
    }
    return ans;
}

inline poly Integ(poly &__f)
{
    poly ans;
    ans.pb(0);
    for (register int i = 0; i < __f.n; ++i)
    {
        ans.a.push_back(1ll * Pre::ny[i + 1] * __f.a[i] % P);
    }
    return ans;
}

inline poly UCPF::Ln(poly __F)
{
    poly dF = Dx(__F);
    dF *= ~__F;
    dF.resize(__F.n);
    dF = Integ(dF);
    dF.resize(__F.n);
    return dF;
}

inline poly UCPF::Exp(poly __f)
{
    poly ans;
    int dep = 1;
    ans.pb(1);
    poly lnf, tmpff;
    while (dep < __f.n << 1)
    {
        lnf = Ln(ans);
        lnf = __f - lnf;
        lnf.resize(dep << 1);
        ++lnf.a[0];
        ans *= lnf;
        ans.resize(dep << 1);
        dep <<= 1;
    }
    ans.resize(__f.n);
    return ans;
}

inline poly UCPF::Sqrt(poly __f)
{
    int tmp = __f[0];
    __f *= Pre::Inv(__f[0]);
    __f = Ln(__f);
    __f *= B;
    __f = Exp(__f);
    tmp = (tmp != 1) ? Quad::work(tmp, 998244353) : 1;
    __f *= tmp;
    return __f;
}

inline poly UCPF::Sin(poly __f)
{
    return (Exp(__f * _I_) - Exp(__f * (P - _I_))) * B * Pre::Inv(_I_);
}

inline poly UCPF::Cos(poly __f)
{
    return (Exp(__f * _I_) + Exp(__f * (P - _I_))) * B;
}

inline poly UCPF::Tan(poly __f)
{
    return Sin(__f) * ~Cos(__f);
}

inline poly UCPF::ArcSin(poly __f)
{
    poly __tmp = __f;
    int __n = __f.n;
    __f = __f * __f;
    __f.resize(__n);
    __f *= (P - 1);
    __f[0]++;
    __f = Sqrt(__f);
    __f = ~__f;
    __f *= Dx(__tmp);
    __f.resize(__n);
    __f = Integ(__f);
    return __f;
}

inline poly UCPF::ArcCos(poly __f)
{
    return ArcSin(__f) * (P - 1);
}

inline poly UCPF::ArcTan(poly __f)
{
    poly __tmp = __f;
    int __n = __f.n;
    __f = __f * __f;
    __f.resize(__n);
    __f[0]++;
    __f = ~__f;
    __f *= Dx(__tmp);
    __f.resize(__n);
    __f = Integ(__f);
    return __f;
}

void PIO::pin(poly &f, int __n)
{
    for (register int i = 0; i < __n; ++i)
    {
        int x;
        read(x);
        f.pb(x);
    }
}

void PIO::ppri(poly __f, int __n)
{
    __f.tp(__f.n);
    __f.resize(__n);
    for (register int i = 0; i < __n; ++i)
    {
        print(__f[i]);
        pc(' ');
    }
    pc('\n');
}

namespace Multipoint_Evel
{
    poly t[N << 1];
    int an[N];
    void build(int l, int r, int p, int *a)
    {
        if (l == r)
        {
            t[p].pb(1ll);
            t[p].pb(P - a[l]);
            return;
        }
        int mid = (l + r) >> 1;
        build(l, mid, p << 1, a);
        build(mid + 1, r, p << 1 | 1, a);
        t[p] = t[p << 1] * t[p << 1 | 1];
    }

    void multipoint_evel(int l, int r, int p, poly __f)
    {

        if (l == r)
        {
            an[l] = __f[0];
            return;
        }
        poly r1 = __f & t[p << 1 | 1], r2 = __f & t[p << 1];
        int mid = (l + r) >> 1;
        multipoint_evel(l, mid, p << 1, r1);
        multipoint_evel(mid + 1, r, p << 1 | 1, r2);
    }

    void PMPE(int *val, poly __f, int mm, int *ans)
    {
        int con = __f[0];
        int lm = mm, nn = __f.n;
        if (nn < mm - 1)
        {
            __f.resize(mm + 1);
        }
        else if (nn >= mm - 1)
        {
            mm = Vmax(mm, nn - 1);
        }   
        build(1, mm, 1, val);
        __f.rev(__f.a.begin(), __f.a.end());
        __f.resize(nn << 1);
        poly tmp = __f * ~t[1];
        tmp.resize(mm);
        multipoint_evel(1, mm, 1, tmp);
        for (int i = 1; i <= lm; i++)
        {
            ans[i] = ((1ll * val[i] * an[i] % P + con) % P + P) % P;
        }
    }
}
using namespace Multipoint_Evel;

int n, m, a[N], Ans[N];

inline void work()
{
    poly f;
    read(n);
    read(m);
    pin(f, n + 1);
    for (int i = 1; i <= m; i++)
    {
        read(a[i]);
    }
    PMPE(a, f, m, Ans);
    for (int i = 1; i <= m; i++)
    {
        print(Ans[i]);
        pc(' ');
    }
}
signed main()
{
    ios::sync_with_stdio(false);
    cin.tie(0), cout.tie(0);
    Pre::initYG();
    work();
    return 0;
}
