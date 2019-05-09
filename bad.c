#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <tgmath.h>
#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <tgmath.h>
int main()
{
    double _Complex _a0[17];
    double _Complex *a0 = _a0;
    double _Complex _a1[17];
    double _Complex *a1 = _a1;
    double _Complex _a2[17];
    double _Complex *a2 = _a2;
    uint32_t r3;
    int32_t v4;
    
    assert(true && "copyArr: destination too small.");
    memcpy(a2, a0, 17 * sizeof(double _Complex));
    r3 = 4;
    for (v4 = (int32_t) r3 - 1; v4 >= 0; v4--) {
        assert((uint32_t) v4 < 17 && "setArr: index out of bounds.");
        assert((uint32_t) v4 < 17 && "arrIndex: index out of bounds.");
        assert(((uint32_t) v4 ^ 1 << (int32_t) r3) < 17 &&
            "arrIndex: index out of bounds.");
        a1[(uint32_t) v4 + 0] = a2[(uint32_t) v4 + 0] + a2[((uint32_t) v4 ^ 1 <<
                                                            (int32_t) r3) + 0];
    }
    assert(false && "oh no!");
    return 0;
}
