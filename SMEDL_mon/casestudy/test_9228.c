//originally from :https://github.com/kkos/oniguruma/issues/60
//Copyright belongs to the orignal author

#include <stdio.h>
#include "./oniguruma.h"


static int
exec(OnigEncoding enc, OnigOptionType options,
     char* apattern, char* astr,  int pattern_len,
    unsigned char *end, OnigSyntaxType* sytax)
{
    int r;
    regex_t* reg;
    OnigErrorInfo einfo;
    UChar* pattern = (UChar* )apattern;
    UChar* str     = (UChar* )astr;

    onig_initialize(&enc, 1);

    r = onig_new(&reg, pattern,
                 pattern + pattern_len,
                 options, enc, sytax , &einfo);
    if (r != ONIG_NORMAL) {
        char s[ONIG_MAX_ERROR_MESSAGE_LEN];
        onig_error_code_to_str(s, r, &einfo);
        fprintf(stderr, "ERROR: %s\n", s);
        return -1;
    }

    onig_free(reg);
    onig_end();
    return 0;
}

extern int main(int argc, char* argv[])
{
    
    int r = 0;
    /* ISO 8859-1 test */
    hs_init(&argc, &argv);
    static unsigned char str[] = { 0xc7, 0xd6, 0xfe, 0xea, 0xe0, 0xe2, 0x00 };

    char* pattern = "\x5b\x5c\x48\x2d\xb0\x30\x8d\x30\x2a\x5b\x5d\x20\x20\x5d"
    "\xf9\x54\x00\x7f\x5c\x63\xef\xef\xef\xef\x52\xf7\xf7\x52"
        "\xf7\xeb\xeb\x70\x2b\xf7\x7b\x30\x2c\x32\x7d";
    printf("init succ\n");
    r = exec(ONIG_ENCODING_GB18030, ONIG_OPTION_IGNORECASE,pattern, (char*) str, 39, str + 7, ONIG_SYNTAX_DEFAULT);
    r = exec(ONIG_ENCODING_GB18030, ONIG_OPTION_IGNORECASE,pattern, (char*) str, 39, str + 7, ONIG_SYNTAX_DEFAULT);
    printf("succ\n");
    
    return r;
}
