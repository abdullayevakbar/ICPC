#include <bits/stdc++.h>
#include <functional>
#include <vector>
#include <stack>
#include <list>
#include <set>
#include <deque>
#include <queue>
#include <map>
#define pb push_back
#define ppb pop_back
#define pf push_front
#define ppf pop_front
#define in insert
#define ll long long int
#define ld long double
#define frr(i, a, b, c) for (ll i = a; i < b; i += c)
#define rfr(i, a, b, c) for (int i = a; i >= b; i -= c)
#define fr(i, a) for (int i = 0; i < a; i++)
#define rf(i, a) for (int i = a; i >= 0; i--)
#define fori(it, x) for (__typeof((x).begin()) it = (x).begin(); it != (x).end(); it++)
#define llu unsigned long long int
#define all(x) (x).begin(), (x).end()
#define mk make_pair
#define f(a) a.first
#define s(a) a.second
#define md 1000000007
#define INF 1e18
using namespace std;
struct segtree
{
    vector<pair<ll, ll>> tree;
    int size;
    void init(int n)
    {
        size = 1;
        while (size < n)
        {
            size *= 2;
        }
        tree.assign(2 * size - 1, {INF, 0});
    }
    void build(vector<ll> &a, int x, int lx, int rx)
    {
        if (rx == lx + 1)
        {
            if (lx < a.size())
                tree[x] = {a[lx], 1};
        }
        else
        {
            int m = (lx + rx) / 2;
            build(a, 2 * x + 1, lx, m);
            build(a, 2 * x + 2, m, rx);
            if (f(tree[2 * x + 1]) == f(tree[2 * x + 2]))
            {
                tree[x] = {f(tree[2 * x + 1]), s(tree[2 * x + 1]) + s(tree[2 * x + 2])};
            }
            else if (f(tree[2 * x + 1]) < f(tree[2 * x + 2]))
            {
                tree[x] = tree[2 * x + 1];
            }
            else
            {
                tree[x] = tree[2 * x + 2];
            }
        }
    }
    void build(vector<ll> &a)
    {
        init(a.size());
        build(a, 0, 0, size);
    }
    void set(int i, int v, int x, int lx, int rx)
    {
        if (rx - lx == 1)
        {
            tree[x] = {v, 1};
            return;
        }
        int m = (lx + rx) / 2;
        if (i < m)
        {
            set(i, v, 2 * x + 1, lx, m);
        }
        else
        {
            set(i, v, 2 * x + 2, m, rx);
        }
        if (f(tree[2 * x + 1]) == f(tree[2 * x + 2]))
        {
            tree[x] = {f(tree[2 * x + 1]), s(tree[2 * x + 1]) + s(tree[2 * x + 2])};
        }
        else if (f(tree[2 * x + 1]) < f(tree[2 * x + 2]))
        {
            tree[x] = tree[2 * x + 1];
        }
        else
        {
            tree[x] = tree[2 * x + 2];
        }
    }
    pair<ll, ll> sum(int l, int r, int x, int lx, int rx)
    {
        if (l >= rx || r <= lx)
        {
            return {INF, 0};
        }
        if (l <= lx && r >= rx)
        {
            return tree[x];
        }
        int m = (lx + rx) / 2;
        pair<ll, ll> s1 = sum(l, r, 2 * x + 1, lx, m);
        pair<ll, ll> s2 = sum(l, r, 2 * x + 2, m, rx);
        if (f(s1) == f(s2))
        {
            return {f(s1), s(s1) + s(s2)};
        }
        else if (f(s1) < f(s2))
        {
            return s1;
        }
        else
        {
            return s2;
        }
    }
    pair<ll, ll> sum(int l, int r)
    {
        return sum(l, r, 0, 0, size);
    }
    void set(int i, int v)
    {
        set(i, v, 0, 0, size);
    }
};
void fenwick2()
{
    int n;
    vector<vector<ll>> tree(n, vector<ll>(n, 0));
    function<void(ll, ll, ll)> update = [&](ll x, ll y, ll val)
    {
        for (int i = x; i < n; i = (i | (i + 1)))
            for (int j = y; j < n; j = (j | (j + 1)))
                tree[i][j] += val;
    };
    function<ll(ll, ll)> sum = [&](ll x, ll y)
    {
        int result = 0;
        for (int i = x; i >= 0; i = (i & (i + 1)) - 1)
            for (int j = y; j >= 0; j = (j & (j + 1)) - 1)
                result += tree[i][j];
        return result;
    };
    function<ll(ll, ll, ll, ll)> sum1 = [&](ll x, ll y, ll a, ll b)
    {
        return sum(a, b) - sum(x - 1, b) - sum(a, y - 1) + sum(x - 1, y - 1);
    };
}
void fenwick()
{
    int n;
    vector<ll> tree(n, 0);
    function<void(ll, ll)> update = [&](ll ind, ll val)
    {
        for (; ind < n; ind = (ind | (ind + 1)))
            tree[ind] += val;
    };
    function<ll(ll)> sum1 = [&](ll ind)
    {
        ll s = 0;
        for (; ind >= 0; ind = (ind & (ind + 1)) - 1)
            s += tree[ind];
        return s;
    };
    function<ll(ll, ll)> sum = [&](ll l, ll r)
    {
        return sum1(r) - sum1(l - 1);
    };
}
ll butun_kordinata(ll a, ll b, ll x, ll y)
{
    ll n, ans = 0;
    long double x1, y1;
    n = __gcd(abs(a - x), abs(b - y));
    x1 = (a - x) / (n * 1.00);
    y1 = (b - y) / (n * 1.00);
    for (int i = 1; i < n; i++)
    {
        if (x + x1 * i - (ll)(x + x1 * i) == 0.0 && y + y1 * i - (ll)(y + y1 * i) == 0.0)
        {
            ans = (n - 1) / i;
            break;
        }
    }
    return ans + 2;
}
ld area(ld x, ld y, ld x1, ld y1, ld x2, ld y2)
{
    return abs((x - x2) * (y1 - y2) - (x1 - x2) * (y - y2));
}
void tofunction()
{
    function<string(string, int)> mul2 = [](string s, int k)
    {
        string res = "";
        while (k--)
            res += s;
        return res;
    };
}
vector<ll> heap_sort(vector<ll> v)
{
    function<void(ll, ll)> insert = [&v](ll x, ll n)
    {
        v[n] = x;
        while (n > 0 && v[n] < v[(n - 1) / 2])
        {
            swap(v[n], v[(n - 1) / 2]);
            n = (n - 1) / 2;
        }
    };
    function<ll(ll)> remuve_min = [&v](ll n)
    {
        ll res = v[0];
        v[0] = v[n];
        ll i = 0;
        while (true)
        {
            ll j = i;
            if (2 * i + 1 < n && v[2 * i + 1] < v[j])
                j = 2 * i + 1;
            if (2 * i + 2 < n && v[2 * i + 2] < v[j])
                j = i * 2 + 2;
            if (j == i)
                break;
            swap(v[i], v[j]);
            i = j;
        }
        return res;
    };
    fr(i, v.size()) insert(v[i], i);
    fr(i, v.size()) v[v.size() - 1 - i] = remuve_min(v.size() - i - 1);
    reverse(all(v));
    return v;
}
deque<ll> z_function(string s)
{
    ll n, m = 0, var;
    n = (ll)s.size();
    deque<ll> z(n, 0);
    ll l = 0, r = 0;
    frr(i, 1, n, 1)
    {
        if (r >= i)
            z[i] = min(r - i + 1, z[i - l]);
        while (i + z[i] < n && s[i + z[i]] == s[z[i]])
        {
            z[i]++;
        }
        if (i + z[i] - 1 > r)
        {
            l = i;
            r = i + z[i] - 1;
        }
    }
    return z;
}
int binpow(int a, int n)
{
    int res = 1;
    while (n)
    {
        if (n & 1)
            res *= a;
        a *= a;
        n >>= 1;
    }
    return res;
}
int main()
{
    priority_queue<long long, vector<long long>, greater<long long>> st;

    deque<pair<tuple<ll, ll, ll>, ll>> v;

    function<void(tuple<ll, ll, ll>)> gett = [&](tuple<ll, ll, ll> g)
    {
        int a, b, c;
        a = get<0>(g);
        b = get<1>(g);
        c = get<2>(g);
    };
    return 0;
}
