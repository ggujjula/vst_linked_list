#include <stdlib.h>
#include <stddef.h>

int test_func(int input) {
    int output = input + 1;
    return output;
}

typedef struct ll {
    int val;
    struct ll *next;
} ll;

typedef struct stack {
    ll *top;
} stack;

stack *ll_empty(void) {
    stack *new = malloc(sizeof(stack));
    if (new == NULL) {
        return NULL;
    }
    new->top = NULL;
    return new;
}

int ll_push(stack *s, int val) {
    ll *new = malloc(sizeof(ll));
    if (new == NULL) {
        return 1;
    }
    new->val = val;
    new->next = s->top;
    s->top = new;
    return 0;
}

int ll_pop(stack *s, int *val) {
    ll *node = s->top;
    *val = s->top->val;
    s->top = s->top->next;
    free(node);
    return 0;
}