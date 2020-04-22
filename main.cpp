#include <fstream>
#include <set>
#include <algorithm>
#include <vector>
#include <queue>

using namespace std;

struct DFA
{
    int n, m, q0, k, l, tranzitie[1005][260];
    char alfabet[260];
    set<int> stari_finale;
}dfa, dfa_min;

int codif[1005];

void citire_DFA(DFA& d)
{
    ifstream f("automat.in");

    int i, j, x, y;
    char c;

    f >> d.n;
    f >> d.m;
    for(i = 0; i < d.m; i++)
        f >> d.alfabet[i];
    f >> d.q0;
    f >> d.k;
    for(i = 0; i < d.k; i++)
    {
        f >> x;
        d.stari_finale.insert(x);
    }
    f >> d.l;
    for(i = 0; i < d.n; i++)
        for(j = 0; j < d.m; j++)
            d.tranzitie[i][int(d.alfabet[j])] = -1;
    for(i = 0; i < d.l; i++)
    {
        f >> x >> c >> y;
        d.tranzitie[x][int(c)] = y;
    }
    f.close();
}

void construire_DFAmin(DFA& d, DFA& dm)
{
    int i, j, k, s1, s2, lit, aux[1005][256];
    bool ok, elim[1005], viz[1005], echivalenta[1005][1005];

    queue<int> q;

    vector<set<int>> stari_compuse;

    set<int> a;
    set<int>::iterator it;

    ok = false;
    for(i = 1; i < d.n; i++)
        for(j = 0; j < i; j++)
            if(d.stari_finale.find(i) != d.stari_finale.end() && d.stari_finale.find(j) == d.stari_finale.end())
            {
                echivalenta[i][j] = false;
                ok = true;
            }
            else
                if(d.stari_finale.find(i) == d.stari_finale.end() && d.stari_finale.find(j) != d.stari_finale.end())
                {
                    echivalenta[i][j] = false;
                    ok = true;
                }
                else
                    echivalenta[i][j] = true;   /// matricea de ehivalenta in stare initiala
    while(ok)   /// cat timp mai apar modificari in matrice
    {
        ok = false;
        for(i = 1; i < d.n; i++)
            for(j = 0; j < i; j++)
                if(echivalenta[i][j])
                {
                    for(k = 0; k < d.m; k++)
                    {
                        lit = int(d.alfabet[k]);
                        s1 = d.tranzitie[i][lit];
                        s2 = d.tranzitie[j][lit];
                        if(s1 >= 0 && s2 >= 0 && s1 != s2 && !echivalenta[max(s1, s2)][min(s1, s2)])
                            break;  /// daca avem o pereche de tranzitii neechivalente, ne oprim
                    }               /// inseamna ca nici starile i si j nu sunt echivalente
                    if(k < d.m)
                    {
                        echivalenta[i][j] = false;
                        ok = true;  /// apar modificari in matrice
                    }
                }
    }
    for(i = 0; i < d.n; i++)
        viz[i] = false;
    stari_compuse.clear();  /// formam starile compuse
    for(i = d.n - 1; i >= 0; i--)
        if(!viz[i])     /// daca starea i nu apare intr-o alta stare compusa, construim una noua
        {
            viz[i] = true;
            a.clear();
            a.insert(i);
            for(j = i - 1; j >= 0; j--)
                if(echivalenta[i][j])
                {
                    viz[j] = true;
                    a.insert(j);
                }
            stari_compuse.push_back(a);
        }
    dm.n = stari_compuse.size();    /// in DFA min, avem atatea stari cate stari compuse am creat
    dm.m = d.m;
    for(i = 0; i < d.m; i++)
        dm.alfabet[i] = d.alfabet[i];   /// alfabetul ramane acelasi
    for(i = 0; i < dm.n; i++)
        for(j = 0; j < dm.m; j++)
            dm.tranzitie[i][int(dm.alfabet[j])] = -1;   /// marcam toate tranzitiile din DFA min cu -1
    for(i = 0; i < dm.n; i++)
        for(j = 0; j < dm.m; j++)
            for(it = stari_compuse[i].begin(); it != stari_compuse[i].end(); it++)
                if(d.tranzitie[*it][int(d.alfabet[j])] != -1)
                {
                    for(k = 0; k < dm.n; k++)
                        if(stari_compuse[k].find(d.tranzitie[*it][int(d.alfabet[j])]) != stari_compuse[k].end())
                        {
                            dm.tranzitie[i][int(d.alfabet[j])] = k;
                            break;      /// formam tranzitiile din DFA min cu starile compuse
                        }
                    if(k < dm.n)
                        break;
                }
    dm.k = 0;
    for(i = 0; i < dm.n; i++)
    {
        if(stari_compuse[i].find(d.q0) != stari_compuse[i].end())
            dm.q0 = i;  /// starea initiala din DFA min
        for(it = stari_compuse[i].begin(); it != stari_compuse[i].end(); it++)
            if(d.stari_finale.find(*it) == d.stari_finale.end())
                break;
        if(it == stari_compuse[i].end())
        {
            dm.stari_finale.insert(i);
            dm.k++;
        }   /// construim starile finale din DFA min
        elim[i] = false;    /// momentan, nicio stare nu este eliminata
    }
    for(i = 0; i < dm.n; i++)
        if(dm.stari_finale.find(i) == dm.stari_finale.end())
        {
            ok = false;
            for(j = 0; j < dm.n; j++)
                viz[j] = false;
            while(!q.empty())
                q.pop();
            q.push(i);
            while(!q.empty())
            {
                k = q.front();
                viz[k] = true;
                if(dm.stari_finale.find(k) != dm.stari_finale.end())
                    ok = true;
                q.pop();
                for(j = 0; j < dm.m; j++)
                    if(dm.tranzitie[k][int(dm.alfabet[j])] != -1 && !viz[dm.tranzitie[k][int(dm.alfabet[j])]])
                        q.push(dm.tranzitie[k][int(dm.alfabet[j])]);
            }
            if(!ok)
                elim[i] = true;     /// eliminam starea i daca nu exista un drum de la starea i la o stare finala
        }
    a.clear();
    while(!q.empty())
        q.pop();
    q.push(dm.q0);
    while(!q.empty())
    {
        k = q.front();
        a.insert(k);
        q.pop();
        for(i = 0; i < dm.m; i++)
        {
            j = dm.tranzitie[k][int(dm.alfabet[i])];
            if(j != -1 && !elim[j] && a.find(j) == a.end())
                q.push(j);
        }
    }   /// a = parcurgere in latime din starea initiala
    for(i = 0; i < dm.n; i++)
    {
        if(!elim[i] && a.find(i) == a.end())
            elim[i] = true; /// daca starea i nu se gaseste in a, insemana ca nu exista drum de la starea initiala la i si elimin i
        if(elim[i] && d.stari_finale.find(i) != d.stari_finale.end())
        {
            dm.k--;
            dm.stari_finale.erase(i);   /// daca starea i este eliminata, o elimin si din starile finale
        }
    }
    dm.l = 0;
    k = 0;
    for(i = 0; i < dm.n; i++)
        if(!elim[i])
        {
            codif[i] = k++;     /// codificam starile neeliminate cu numere consecutive
            for(j = 0; j < dm.m; j++)
            {
                s1 = dm.tranzitie[i][int(dm.alfabet[j])];
                if(s1 != -1 && !elim[s1])
                    dm.l++;
            }
        }   /// calculam numarul de tranzitii
    for(i = 0; i < dm.n; i++)
        for(j = 0; j < dm.m; j++)
        {
            aux[i][int(dm.alfabet[j])] = dm.tranzitie[i][int(dm.alfabet[j])];
            dm.tranzitie[i][int(dm.alfabet[j])] = -1;
        }
    for(i = 0; i < dm.n; i++)
        if(!elim[i])
            for(j = 0; j < dm.m; j++)
            {
                s1 = aux[i][int(dm.alfabet[j])];
                if(s1 != -1 && !elim[s1])
                    dm.tranzitie[codif[i]][int(dm.alfabet[j])] = codif[s1];
            }      /// refacem tranzitiile dupa codificarea starilor
    dm.q0 = codif[dm.q0];
    dm.n = k;   /// actualizam starea initiala si numarul de stari
    for(it = dm.stari_finale.begin(); it != dm.stari_finale.end(); it++)
    {
        k = codif[*it];
        dm.stari_finale.erase(*it);
        dm.stari_finale.insert(k);  /// actualizam starile finale
    }
}

void afisare_DFA(const DFA& d)
{
    ofstream g("automat.out");

    int i, j;
    set<int>::iterator it;

    g << "DFA min:\n" << d.n << '\n' << d.m << '\n';
    for(i = 0; i < d.m; i++)
        g << d.alfabet[i] << ' ';
    g << '\n' << d.q0 << '\n' << d.k << '\n';
    for(it = d.stari_finale.begin(); it != d.stari_finale.end(); it++)
        g << *it << ' ';
    g << '\n' << d.l << '\n';
    for(i = 0; i < d.n; i++)
        for(j = 0; j < d.m; j++)
            if(d.tranzitie[i][int(d.alfabet[j])] != -1)
                g << i << ' ' << d.alfabet[j] << ' ' << d.tranzitie[i][int(d.alfabet[j])] << '\n';
    g.close();
}

int main()
{
    citire_DFA(dfa);
    construire_DFAmin(dfa, dfa_min);
    afisare_DFA(dfa_min);
    return 0;
}
