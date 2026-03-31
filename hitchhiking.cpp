#include<bits/stdc++.h>

using namespace std;

const int epsilon = -1;
const int bottom = -2;

bool in(int element, const set<int>& s) {
    return s.find(element) != s.end();
}

unordered_map<int,int> id;
int nxt = 0;

int get_id(int x) {
    if (!id.count(x))
        id[x] = nxt++;
    return id[x];
};

int main() {
    int num_roots;
    cin >> num_roots;
    vector<int> roots(num_roots);
    for (int i = 0; i < num_roots; i++) {
        cin >> roots[i];
        roots[i] = get_id(roots[i]);
    }

    int num_nodes, num_edges;
    cin >> num_nodes >> num_edges;
    vector<vector<int>> g(num_nodes);
    for (int i = 0; i < num_edges; i++) {
        int u, v;
        cin >> u >> v;
        u = get_id(u);
        v = get_id(v);
        g[u].push_back(v);
    }

    vector<bool> is_red(num_nodes, false);
    int num_red_nodes;
    cin >> num_red_nodes;
    for (int i = 0; i < num_red_nodes; i++) {
        int red_node;
        cin >> red_node;
        red_node = get_id(red_node);
        is_red[red_node] = true;    
    }

    set<int> open_nodes;
    set<int> active_red_nodes;
    set<int> interrupted_nodes;
    vector<int> p(num_nodes, bottom);

    for (int root : roots) {
        open_nodes.insert(root);
        if (is_red
            [root]) {
            active_red_nodes.insert(root);
            p[root] = root;
        } else {
            p[root] = epsilon;
        }
    }

    while (!open_nodes.empty()) {


        while (!open_nodes.empty()) {
            int node = *open_nodes.begin();
            open_nodes.erase(node);

            int alpha = p[node];

            for (int child : g[node]) {
                if (alpha == child) {
                    cout << "Detected an accepting cycle, counter example found!" << endl;
                    return 0;
                }
            
                if (p[child] == bottom && is_red[child]) {
                    active_red_nodes.insert(child);
                    if (child > alpha)
                        alpha = child;
                    else 
                        interrupted_nodes.insert(child); //first interruption case
                }

                int beta = p[child];
                p[child] = max(alpha, beta);

                if (alpha > beta && beta > epsilon && in(child, open_nodes))
                    interrupted_nodes.insert(beta); // second interruption case

                if(beta > alpha && alpha > epsilon && !in(child, active_red_nodes))
                    interrupted_nodes.insert(alpha); // third interruption case
                
                if (alpha > beta)
                    open_nodes.insert(child);
            }


        }

        if (!interrupted_nodes.empty()) {
            for (int node = 0; node < num_nodes; node++) {

                if (in(node, active_red_nodes)) { 
                    if (in(node, interrupted_nodes) && p[node] != node) {
                        open_nodes.insert(node);
                    }
                    else {
                        active_red_nodes.erase(node);
                    }

                    if (in(node, interrupted_nodes)) {
                        interrupted_nodes.erase(node);
                    }   
                }
                if (in(node, active_red_nodes))
                    p[node] = node;
                else
                    p[node] = epsilon;
            }
        }
    }

    cout << "No accepting cycle detected, no counter example found!" << endl;

}

// 1 0
// 5 5
// 0 1 1 2 2 3 3 4 4 1
// 1 3