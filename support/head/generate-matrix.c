/* Generate one exact integer partition of the matrix defined in
   manuscript/computational-estimates.md. Tested with FLINT/Arb 3.0.1.
   Usage: generate-matrix FIRST LAST OUTPUT
   Every operation, including the large complex phase, retains its ball. */
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <flint/acb.h>
#include <flint/acb_mat.h>
#include <flint/arb_mat.h>

enum { ORDER = 62, CUTOFF = 690950, PREC = 192 };

static long integer(const char *s) {
    char *end;
    errno = 0;
    long n = strtol(s, &end, 10);
    if (errno || *end) { fprintf(stderr, "Invalid integer\n"); exit(2); }
    return n;
}

int main(int argc, char **argv) {
    if (argc != 4) return 2;
    long first = integer(argv[1]), last = integer(argv[2]);
    if (first < 1 || last > CUTOFF || first > last) return 2;
    FILE *f = fopen(argv[3], "wx");
    if (!f) { perror("output"); return 2; }
    int status = 0, io_failed;
    acb_mat_t sum, term;
    arb_mat_t ev, kv, product;
    arb_t n, ell, square;
    acb_t exponent, phase, base;
    acb_mat_init(sum, ORDER, ORDER);
    acb_mat_init(term, ORDER, ORDER);
    arb_mat_init(ev, ORDER, 1);
    arb_mat_init(kv, 1, ORDER);
    arb_mat_init(product, ORDER, ORDER);
    arb_init(n); arb_init(ell); arb_init(square);
    acb_init(exponent); acb_init(phase); acb_init(base);
    /* (-1 + i (X+1/2))/2, constructed from exact integers. */
    arb_set_si(acb_realref(exponent), -1);
    arb_mul_2exp_si(acb_realref(exponent), acb_realref(exponent), -1);
    arb_set_str(acb_imagref(exponent), "11998694683001", PREC);
    arb_mul_2exp_si(acb_imagref(exponent), acb_imagref(exponent), -2);
    for (long j = first; j <= last; ++j) {
        arb_set_si(n, j);
        arb_div_ui(ell, n, 345475, PREC);
        arb_log(ell, ell, PREC);
        arb_mul(square, ell, ell, PREC);
        arb_mul_2exp_si(square, square, -2);
        arb_one(arb_mat_entry(ev, 0, 0));
        arb_one(arb_mat_entry(kv, 0, 0));
        for (long k = 1; k < ORDER; ++k) {
            arb_mul(arb_mat_entry(ev, k, 0), arb_mat_entry(ev, k-1, 0), ell, PREC);
            arb_div_ui(arb_mat_entry(ev, k, 0), arb_mat_entry(ev, k, 0), k, PREC);
            arb_mul(arb_mat_entry(kv, 0, k), arb_mat_entry(kv, 0, k-1), square, PREC);
            arb_div_ui(arb_mat_entry(kv, 0, k), arb_mat_entry(kv, 0, k), k, PREC);
        }
        arb_mat_mul(product, ev, kv, PREC);
        acb_mat_set_arb_mat(term, product);
        acb_set_arb(base, n);
        acb_pow(phase, base, exponent, PREC);
        acb_mat_scalar_addmul_acb(sum, term, phase, PREC);
    }
    fprintf(f, "5999347341500.5,345475,%ld,%ld,62,62,192\n", first, last);
    for (long e = 0; e < ORDER; ++e) {
        for (long k = 0; k < ORDER; ++k) {
            acb_srcptr z = acb_mat_entry(sum, e, k);
            if (!acb_is_finite(z)) { status = 3; goto cleanup; }
            char *re = arb_get_str(acb_realref(z), 70, 0);
            char *im = arb_get_str(acb_imagref(z), 70, 0);
            fprintf(f, "%s | %s%s", re, im, k+1 == ORDER ? "\n" : " ; ");
            flint_free(re); flint_free(im);
        }
    }
cleanup:
    io_failed = ferror(f);
    if (fclose(f) || io_failed) status = 3;
    acb_mat_clear(sum); acb_mat_clear(term);
    arb_mat_clear(ev); arb_mat_clear(kv); arb_mat_clear(product);
    arb_clear(n); arb_clear(ell); arb_clear(square);
    acb_clear(exponent); acb_clear(phase); acb_clear(base);
    flint_cleanup();
    return status;
}
