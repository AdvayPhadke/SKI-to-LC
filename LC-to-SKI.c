
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
 
/* ── AST ──────────────────────────────────────────────────────────────── */
 
typedef enum { VAR, APP, ABS, COMB } NodeKind;
 
typedef struct Node {
    NodeKind kind;
    char     var;          /* VAR / ABS  */
    char     comb[3];      /* COMB: "S","K","I"  */
    struct Node *left;     /* APP: function; ABS: body */
    struct Node *right;    /* APP: argument */
} Node;
 
static Node *new_var(char v) {
    Node *n = calloc(1, sizeof *n);
    n->kind = VAR; n->var = v;
    return n;
}
static Node *new_app(Node *f, Node *x) {
    Node *n = calloc(1, sizeof *n);
    n->kind = APP; n->left = f; n->right = x;
    return n;
}
static Node *new_abs(char v, Node *body) {
    Node *n = calloc(1, sizeof *n);
    n->kind = ABS; n->var = v; n->left = body;
    return n;
}
static Node *new_comb(const char *name) {
    Node *n = calloc(1, sizeof *n);
    n->kind = COMB; strncpy(n->comb, name, 2);
    return n;
}
 
static void free_node(Node *n) {
    if (!n) return;
    free_node(n->left);
    free_node(n->right);
    free(n);
}
 
/* Deep copy */
static Node *copy_node(const Node *n) {
    if (!n) return NULL;
    Node *c = calloc(1, sizeof *c);
    *c = *n;
    c->left  = copy_node(n->left);
    c->right = copy_node(n->right);
    return c;
}
 
/* ── Parser ───────────────────────────────────────────────────────────── */
 
static const char *src;
static int         pos;
 
static void skip_ws(void) { while (src[pos] == ' ' || src[pos] == '\t') pos++; }
 
static Node *parse_expr(void);
 
/* Parse a single atom: variable, combinator literal (S/K/I), or parenthesised expr */
static Node *parse_atom(void) {
    skip_ws();
    char c = src[pos];
 
    /* Lambda abstraction: Lx.body or Lx Ly . body */
    if (c == 'L') {
        pos++; skip_ws();
        if (!isalpha(src[pos])) { fprintf(stderr,"Expected variable after L\n"); exit(1); }
        char var = src[pos++]; skip_ws();
        /* Support chained: Lx Ly.body  → Lx.(Ly.body) */
        Node *body;
        if (src[pos] == '.') { pos++; body = parse_expr(); }
        else                 { body = parse_atom(); }   /* another L */
        return new_abs(var, body);
    }
 
    /* Parenthesised group */
    if (c == '(') {
        pos++;
        Node *e = parse_expr();
        skip_ws();
        if (src[pos] != ')') { fprintf(stderr,"Expected ')'\n"); exit(1); }
        pos++;
        return e;
    }
 
    /* Upper-case S/K/I treated as combinator literals */
    if (c == 'S' || c == 'K' || c == 'I') {
        char name[2] = { c, 0 };
        pos++;
        return new_comb(name);
    }
 
    /* Lower-case variable */
    if (islower(c)) { pos++; return new_var(c); }
 
    fprintf(stderr, "Unexpected character '%c' at position %d\n", c, pos);
    exit(1);
}
 
/* Left-associative application */
static Node *parse_expr(void) {
    skip_ws();
    Node *e = parse_atom();
    for (;;) {
        skip_ws();
        char c = src[pos];
        if (c == '\0' || c == ')') break;
        Node *arg = parse_atom();
        e = new_app(e, arg);
    }
    return e;
}
 
/* ── Free-variable check ──────────────────────────────────────────────── */
 
static int is_free(char v, const Node *n) {
    if (!n) return 0;
    switch (n->kind) {
        case VAR:  return n->var == v;
        case COMB: return 0;
        case APP:  return is_free(v, n->left) || is_free(v, n->right);
        case ABS:  return (n->var == v) ? 0 : is_free(v, n->left);
    }
    return 0;
}
 
/* ── Bracket abstraction (eliminate variable v from expression e) ──────── */
 
static Node *eliminate(char v, Node *e);
 
static Node *translate(Node *e) {
    if (!e) return NULL;
    switch (e->kind) {
        case VAR:
        case COMB:
            return copy_node(e);
        case APP:
            return new_app(translate(e->left), translate(e->right));
        case ABS:
            /* Translate body first, then eliminate the bound variable */
            {
                Node *tbody = translate(e->left);
                Node *result = eliminate(e->var, tbody);
                free_node(tbody);
                return result;
            }
    }
    return NULL; /* unreachable */
}
 
static Node *eliminate(char v, Node *e) {
    switch (e->kind) {
        /* ELIM(x, x) = I */
        case VAR:
            if (e->var == v) return new_comb("I");
            /* ELIM(x, y) = K y  (x≠y) */
            return new_app(new_comb("K"), copy_node(e));
 
        /* ELIM(x, C) = K C  for combinators */
        case COMB:
            return new_app(new_comb("K"), copy_node(e));
 
        /* ELIM(x, Ly.body) — shouldn't appear after full translation,
           but handle defensively */
        case ABS: {
            Node *inner = translate(e);
            Node *result = eliminate(v, inner);
            free_node(inner);
            return result;
        }
 
        /* ELIM(x, (E F)) */
        case APP: {
            int freeL = is_free(v, e->left);
            int freeR = is_free(v, e->right);
 
            /* x not free in either: K (E F) */
            if (!freeL && !freeR)
                return new_app(new_comb("K"), copy_node(e));
 
            /* x free only in right: (K E) (ELIM x F)
               — optimisation: avoids unnecessary S */
            if (!freeL)
                return new_app(
                    new_app(new_comb("K"), copy_node(e->left)),
                    eliminate(v, e->right));
 
            /* x free only in left: S (ELIM x E) (K F) */
            if (!freeR)
                return new_app(
                    new_app(new_comb("S"), eliminate(v, e->left)),
                    new_app(new_comb("K"), copy_node(e->right)));
 
            /* x free in both: S (ELIM x E) (ELIM x F) */
            return new_app(
                new_app(new_comb("S"), eliminate(v, e->left)),
                eliminate(v, e->right));
        }
    }
    return NULL;
}
 
/* ── Printer ──────────────────────────────────────────────────────────── */
 
static void print_node(const Node *n, int paren) {
    if (!n) return;
    switch (n->kind) {
        case VAR:  printf("%c", n->var); break;
        case COMB: printf("%s", n->comb); break;
        case ABS:
            if (paren) printf("(");
            printf("L%c.", n->var);
            print_node(n->left, 0);
            if (paren) printf(")");
            break;
        case APP:
            if (paren) printf("(");
            print_node(n->left,  n->left->kind  == APP);
            printf(" ");
            print_node(n->right, n->right->kind == APP);
            if (paren) printf(")");
            break;
    }
}
 
/* ── Main ─────────────────────────────────────────────────────────────── */
 
int main(int argc, char *argv[]) {
    if (argc < 2) {
        fprintf(stderr,
            "Usage: %s \"<lambda-expr>\"\n"
            "  Variables  : lowercase letters\n"
            "  Abstraction: Lx.body\n"
            "  Application: (f x) or f x  (left-associative)\n"
            "Examples:\n"
            "  %s \"Lx.x\"          -->  I\n"
            "  %s \"Lx.Ly.x\"       -->  K\n"
            "  %s \"Lx.Ly.Lz.(x z)(y z)\"  -->  S\n",
            argv[0], argv[0], argv[0], argv[0]);
        return 1;
    }
 
    src = argv[1];
    pos = 0;
 
    Node *ast = parse_expr();
    skip_ws();
    if (src[pos] != '\0') {
        fprintf(stderr, "Warning: trailing input ignored: \"%s\"\n", src + pos);
    }
 
    printf("Input : %s\n", argv[1]);
    printf("Parsed: "); print_node(ast, 0); printf("\n");
 
    Node *ski = translate(ast);
    printf("SKI   : "); print_node(ski, 0); printf("\n");
 
    free_node(ast);
    free_node(ski);
    return 0;
}
