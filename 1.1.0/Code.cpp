/*

POLYBOARD (1.1.0)
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

const constexpr int P = 998244353, Y = 3, I = 332748118, B = (P + 1) >> 1, N = 600005;

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
        if(__x <= 500000 )
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
    template<class T>
    inline T addt(T &__a, T __b)
    {
        if ((__a += __b) >= P)
        {
            __a -= P;
        }
        return __a;
    }

    template<class T>
    inline T delt(T &__a, T __b)
    {
        if ((__a -= __b) < 0)
        {
            __a += P;
        }
        return __a;
    }

    template<class T>
    inline T add(T __a, T __b)
    {
        return addt(__a, __b);
    }

    template<class T>
    inline T del(T __a, T __b)
    {
        return delt(__a, __b);
    }

    inline int tp(int &x)
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

namespace POLY
{
    int __Binary_reverse[2000005];
    class poly;

    namespace PIO
    {
        void pin(poly &f, int __n);
        void ppri(poly __f, int __n);
    }
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

        inline void rev(int __st, int __len) 
        { 
            reverse(a.begin() + __st, a.begin() + __st + __len); 
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

    private:
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

    public:
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

        template<class T>
        poly operator*(const T &__tmpa) const
        {
            poly ans = *this;
            return ans *= __tmpa;
        }
        poly operator~() const
        {
            poly __f = *this;
            int cst = __f.a[0];
            int len = 1, L = 0;
            while (len < (n << 1))
            {
                len <<= 1;
                L++;
            }
            for (register int i = 0; i < len; ++i)
            {
                __Binary_reverse[i] = (__Binary_reverse[i >> 1] >> 1) | ((i & 1) << (L - 1));
            }
            __f.resize(len);
            __f.NTT(1);
            poly ans;
            int dep = 1;
            ans.pb(1);
            while (dep < n)
            {
                ans.resize(len);
                ans.NTT(1);
                for (register int i = 0; i < len; ++i)
                    ans[i] = 1ll * ans[i] * (2ll - 1ll * __f[i] * ans[i] % P + P) % P;
                ans.NTT(0);
                ans.tp(ans.n);
                ans.resize(dep << 1);
                dep <<= 1;
            }
            ans.resize(__f.n);
            return ans;
        }
    };
}

using namespace POLY;

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
    for (register int i = 0; i < __n; ++i)
    {
        print(__f[i]);
        pc(' ');
    }
    pc('\n');
}

int n;

inline void work()
{
    poly f;
    read(n);
    pin(f, n);
    ppri(~f, n);
}

signed main()
{
    ios::sync_with_stdio(false);
    cin.tie(0), cout.tie(0);
    Pre::initYG();
    work();
    return 0;
}