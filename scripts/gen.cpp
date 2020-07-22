#include <vector>
#include <iostream>
using namespace std;

#define pb push_back
#define mp make_pair
#define eb emplace_back
#define all(a) begin(a), end(a)
#define has(a, b) (a.find(b) != a.end())
#define fora(i, n) for(int i = 0; i < n; i++)
#define forb(i, n) for(int i = 1; i <= n; i++)
#define forc(a, b) for(const auto &a : b)
#define ford(i, n) for(int i = n; i >= 0; i--)
#define maxval(t) numeric_limits<t>::max()
#define minval(t) numeric_limits<t>::min()
#define imin(a, b) a = min(a, b)
#define imax(a, b) a = max(a, b)
#define sz(x) (int)(x).size()
#define pvec(v) copy(all(v), ostream_iterator<decltype(v)::value_type>(cout, " "))

#define dbgs(x) #x << " = " << x
#define dbgs2(x, y) dbgs(x) << ", " << dbgs(y)
#define dbgs3(x, y, z) dbgs2(x, y) << ", " << dbgs(z)
#define dbgs4(w, x, y, z) dbgs3(w, x, y) << ", " << dbgs(z)

using ll = long long;
using ld = long double;

bool solve(vector<vector<int>> &s, int i, int j) {
	if (j == 9) { ++i; j = 0; }
	if (i == 9) return true;

	if (s[i][j] != 0) return solve(s, i, j + 1);

	forb(k, 9) {
		bool ok = true;
		fora(l, 9) if (s[i][l] == k) ok = false;
		fora(l, 9) if (s[l][j] == k) ok = false;
		fora(l, 3) fora(m, 3) {
			if (s[3 * (i / 3) + l][3 * (j / 3) + m] == k) ok = false;
		}
		if (!ok) continue;
		s[i][j] = k;
		if (solve(s, i, j + 1)) return true;
	}
	s[i][j] = 0;

	return false;
}

int main()
{
	ios_base::sync_with_stdio(false);
	cin.tie(nullptr);

	vector<vector<int>> s(9, vector<int>(9));

	fora(i, 9) fora(j, 9) {
		cin >> s[i][j];
	}

	cout << "import widget\n\nopen sudoku\n\ntheorem play (s : sudoku)";

	fora(i, 9) fora (j, 9) {
		if (s[i][j] == 0) continue;
		cout << " (c" << i << j << " : s.f (" << i << ", " << j << ") = " << s[i][j] << ")";
	}

	solve(s, 0, 0);

	cout << " :";

	fora(i, 9) fora(j, 9) {
		cout << " s.f (" << i << ", " << j << ") = " << s[i][j];
		if (i != 8 || j != 8) cout << " ∧";
	}

	cout << " :=\nbegin [show_sudoku]\n\nend\n";
}
