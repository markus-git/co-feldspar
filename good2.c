#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <tgmath.h>
#define swap_arr(a,b) do {void* TmP=a; a=b; b=TmP;} while (0)
int main()
{
    uint32_t r0;
    uint32_t let5;
    uint32_t let6;
    uint32_t let7;
    uint32_t let8;
    uint32_t let9;
    uint32_t let10;
    uint32_t let11;
    uint32_t let12;
    uint32_t let13;
    uint32_t let14;
    uint32_t let15;
    uint32_t let16;
    uint32_t let17;
    uint32_t let18;
    uint32_t let19;
    uint32_t let20;
    uint32_t let21;
    uint32_t let22;
    uint32_t let23;
    uint32_t let24;
    uint32_t let25;
    uint32_t let26;
    uint32_t let27;
    uint32_t let28;
    uint32_t let29;
    uint32_t let30;
    uint32_t let31;
    uint32_t let32;
    uint32_t let33;
    uint32_t let34;
    uint32_t let35;
    uint32_t let36;
    uint32_t let37;
    uint32_t let38;
    uint32_t let39;
    uint32_t let40;
    uint32_t let41;
    uint32_t let42;
    uint32_t let43;
    uint32_t let44;
    uint32_t let45;
    uint32_t let46;
    uint32_t let47;
    uint32_t let48;
    uint32_t let49;
    uint32_t let50;
    uint32_t let51;
    uint32_t let52;
    uint32_t let53;
    uint32_t let54;
    uint32_t let55;
    uint32_t let56;
    uint32_t let57;
    uint32_t let58;
    uint32_t let59;
    uint32_t let60;
    uint32_t let61;
    uint32_t let62;
    uint32_t let63;
    uint32_t let64;
    uint32_t let65;
    uint32_t let66;
    uint32_t let67;
    uint32_t let68;
    uint32_t let69;
    uint32_t let70;
    uint32_t let71;
    uint32_t let72;
    uint32_t let73;
    uint32_t let74;
    uint32_t let75;
    uint32_t let76;
    uint32_t let77;
    uint32_t let78;
    uint32_t let79;
    uint32_t let80;
    uint32_t let81;
    uint32_t let82;
    uint32_t let83;
    uint32_t let84;
    uint32_t let85;
    uint32_t let86;
    uint32_t let87;
    uint32_t let88;
    uint32_t let89;
    uint32_t let90;
    uint32_t let91;
    uint32_t let92;
    uint32_t let93;
    uint32_t let94;
    uint32_t let95;
    uint32_t let96;
    uint32_t let97;
    uint32_t let98;
    uint32_t let99;
    uint32_t let100;
    uint32_t let101;
    uint32_t let102;
    uint32_t let103;
    uint32_t let104;
    uint32_t let105;
    uint32_t let106;
    uint32_t let107;
    uint32_t let108;
    uint32_t let109;
    uint32_t let110;
    uint32_t let111;
    uint32_t let112;
    uint32_t let113;
    uint32_t let114;
    uint32_t let115;
    uint32_t let116;
    uint32_t let117;
    uint32_t let118;
    uint32_t let119;
    uint32_t let120;
    uint32_t let121;
    uint32_t let122;
    uint32_t let123;
    uint32_t let124;
    uint32_t let125;
    uint32_t let126;
    uint32_t let127;
    uint32_t let128;
    uint32_t r129;
    uint32_t v131;
    uint32_t v132;
    uint32_t r133;
    int32_t v134;
    uint32_t r139;
    uint32_t v140;
    
    r0 = 16;
    
    double _Complex _a1[r0];
    double _Complex *a1 = _a1;
    double _Complex _a2[r0];
    double _Complex *a2 = _a2;
    double _Complex _a3[r0];
    double _Complex *a3 = _a3;
    double _Complex _a4[r0];
    double _Complex *a4 = _a4;
    
    /* proved: copyArr: destination too small. */
    memcpy(a4, a3, r0 * sizeof(double _Complex));
    let5 = r0;
    let6 = 0;
    let7 = (uint32_t) (let5 > 65535) << 4;
    let8 = (uint32_t) (let5 > 65535) << 4;
    let9 = r0;
    let10 = 0;
    let11 = (uint32_t) (let9 > 65535) << 4;
    let12 = (uint32_t) (let9 > 65535) << 4;
    let13 = let5 >> (int32_t) let7;
    let14 = let10 | let12;
    let15 = (uint32_t) (let13 > 255) << 3;
    let16 = (uint32_t) (let13 > 255) << 3;
    let17 = r0;
    let18 = 0;
    let19 = (uint32_t) (let17 > 65535) << 4;
    let20 = (uint32_t) (let17 > 65535) << 4;
    let21 = r0;
    let22 = 0;
    let23 = (uint32_t) (let21 > 65535) << 4;
    let24 = (uint32_t) (let21 > 65535) << 4;
    let25 = let17 >> (int32_t) let19;
    let26 = let22 | let24;
    let27 = (uint32_t) (let25 > 255) << 3;
    let28 = (uint32_t) (let25 > 255) << 3;
    let29 = let13 >> (int32_t) let15;
    let30 = let26 | let28;
    let31 = (uint32_t) (let29 > 15) << 2;
    let32 = (uint32_t) (let29 > 15) << 2;
    let33 = r0;
    let34 = 0;
    let35 = (uint32_t) (let33 > 65535) << 4;
    let36 = (uint32_t) (let33 > 65535) << 4;
    let37 = r0;
    let38 = 0;
    let39 = (uint32_t) (let37 > 65535) << 4;
    let40 = (uint32_t) (let37 > 65535) << 4;
    let41 = let33 >> (int32_t) let35;
    let42 = let38 | let40;
    let43 = (uint32_t) (let41 > 255) << 3;
    let44 = (uint32_t) (let41 > 255) << 3;
    let45 = r0;
    let46 = 0;
    let47 = (uint32_t) (let45 > 65535) << 4;
    let48 = (uint32_t) (let45 > 65535) << 4;
    let49 = r0;
    let50 = 0;
    let51 = (uint32_t) (let49 > 65535) << 4;
    let52 = (uint32_t) (let49 > 65535) << 4;
    let53 = let45 >> (int32_t) let47;
    let54 = let50 | let52;
    let55 = (uint32_t) (let53 > 255) << 3;
    let56 = (uint32_t) (let53 > 255) << 3;
    let57 = let41 >> (int32_t) let43;
    let58 = let54 | let56;
    let59 = (uint32_t) (let57 > 15) << 2;
    let60 = (uint32_t) (let57 > 15) << 2;
    let61 = let29 >> (int32_t) let31;
    let62 = let58 | let60;
    let63 = (uint32_t) (let61 > 3) << 1;
    let64 = (uint32_t) (let61 > 3) << 1;
    let65 = r0;
    let66 = 0;
    let67 = (uint32_t) (let65 > 65535) << 4;
    let68 = (uint32_t) (let65 > 65535) << 4;
    let69 = r0;
    let70 = 0;
    let71 = (uint32_t) (let69 > 65535) << 4;
    let72 = (uint32_t) (let69 > 65535) << 4;
    let73 = let65 >> (int32_t) let67;
    let74 = let70 | let72;
    let75 = (uint32_t) (let73 > 255) << 3;
    let76 = (uint32_t) (let73 > 255) << 3;
    let77 = r0;
    let78 = 0;
    let79 = (uint32_t) (let77 > 65535) << 4;
    let80 = (uint32_t) (let77 > 65535) << 4;
    let81 = r0;
    let82 = 0;
    let83 = (uint32_t) (let81 > 65535) << 4;
    let84 = (uint32_t) (let81 > 65535) << 4;
    let85 = let77 >> (int32_t) let79;
    let86 = let82 | let84;
    let87 = (uint32_t) (let85 > 255) << 3;
    let88 = (uint32_t) (let85 > 255) << 3;
    let89 = let73 >> (int32_t) let75;
    let90 = let86 | let88;
    let91 = (uint32_t) (let89 > 15) << 2;
    let92 = (uint32_t) (let89 > 15) << 2;
    let93 = r0;
    let94 = 0;
    let95 = (uint32_t) (let93 > 65535) << 4;
    let96 = (uint32_t) (let93 > 65535) << 4;
    let97 = r0;
    let98 = 0;
    let99 = (uint32_t) (let97 > 65535) << 4;
    let100 = (uint32_t) (let97 > 65535) << 4;
    let101 = let93 >> (int32_t) let95;
    let102 = let98 | let100;
    let103 = (uint32_t) (let101 > 255) << 3;
    let104 = (uint32_t) (let101 > 255) << 3;
    let105 = r0;
    let106 = 0;
    let107 = (uint32_t) (let105 > 65535) << 4;
    let108 = (uint32_t) (let105 > 65535) << 4;
    let109 = r0;
    let110 = 0;
    let111 = (uint32_t) (let109 > 65535) << 4;
    let112 = (uint32_t) (let109 > 65535) << 4;
    let113 = let105 >> (int32_t) let107;
    let114 = let110 | let112;
    let115 = (uint32_t) (let113 > 255) << 3;
    let116 = (uint32_t) (let113 > 255) << 3;
    let117 = let101 >> (int32_t) let103;
    let118 = let114 | let116;
    let119 = (uint32_t) (let117 > 15) << 2;
    let120 = (uint32_t) (let117 > 15) << 2;
    let121 = let89 >> (int32_t) let91;
    let122 = let118 | let120;
    let123 = (uint32_t) (let121 > 3) << 1;
    let124 = (uint32_t) (let121 > 3) << 1;
    let125 = let61 >> (int32_t) let63;
    let126 = let122 | let124;
    let127 = (uint32_t) (let125 > 1) << 0;
    let128 = (uint32_t) (let125 > 1) << 0;
    r129 = let126 | let128;
    
    double _Complex _a130[1 << (int32_t) (r129 - 1)];
    double _Complex *a130 = _a130;
    
    for (v131 = 0; v131 <= (1 << (int32_t) (r129 - 1)) - 1; v131++) {
        /* proved: setArr: index out of bounds. */
        a130[v131 + 0] = exp(I * -(6.283185307179586 * (double) v131 /
                                   (double) (1 << (int32_t) r129)));
    }
    for (v132 = 0; v132 <= r0 - 1; v132++) {
        /* proved: setArr: index out of bounds. */
        /* proved: arrIndex: index out of bounds. */
        a2[v132 + 0] = a4[v132 + 0];
    }
    swap_arr(a1, a2);
    r133 = r0;
    for (v134 = (int32_t) r129 - 1; v134 >= 0; v134--) {
        uint32_t v135;
        
        for (v135 = 0; v135 <= r0 - 1; v135++) {
            double _Complex b136;
            
            /* proved: setArr: index out of bounds. */
            if ((bool) (v135 & 1 << (int32_t) (uint32_t) v134)) {
                double _Complex b137;
                
                /* proved: arrSlice: slice to large. */
                /* proved: arrIndex: index out of bounds. */
                /* proved: arrSlice: index out of bounds. */
                if ((bool) (v135 & 1 << (int32_t) (uint32_t) v134)) {
                    /* proved: arrSlice: slice to large. */
                    /* proved: arrIndex: index out of bounds. */
                    /* proved: arrSlice: index out of bounds. */
                    /* proved: arrSlice: slice to large. */
                    /* proved: arrIndex: index out of bounds. */
                    /* proved: arrSlice: index out of bounds. */
                    b137 = a1[(v135 ^ 1 << (int32_t) (uint32_t) v134) + 0] -
                        a1[v135 + 0];
                } else {
                    /* proved: arrSlice: slice to large. */
                    /* proved: arrIndex: index out of bounds. */
                    /* proved: arrSlice: index out of bounds. */
                    /* proved: arrSlice: slice to large. */
                    /* proved: arrIndex: index out of bounds. */
                    /* proved: arrSlice: index out of bounds. */
                    b137 = a1[v135 + 0] + a1[(v135 ^ 1 <<
                                              (int32_t) (uint32_t) v134) + 0];
                }
                b136 = a130[((v135 & ~(4294967295 <<
                                       (int32_t) (uint32_t) v134)) <<
                             (int32_t) r129 - 1 - (int32_t) (uint32_t) v134) +
                            0] * b137;
            } else {
                double _Complex b138;
                
                if ((bool) (v135 & 1 << (int32_t) (uint32_t) v134)) {
                    /* proved: arrSlice: slice to large. */
                    /* proved: arrIndex: index out of bounds. */
                    /* proved: arrSlice: index out of bounds. */
                    /* proved: arrSlice: slice to large. */
                    /* proved: arrIndex: index out of bounds. */
                    /* proved: arrSlice: index out of bounds. */
                    b138 = a1[(v135 ^ 1 << (int32_t) (uint32_t) v134) + 0] -
                        a1[v135 + 0];
                } else {
                    /* proved: arrSlice: slice to large. */
                    /* proved: arrIndex: index out of bounds. */
                    /* proved: arrSlice: index out of bounds. */
                    /* proved: arrSlice: slice to large. */
                    /* proved: arrIndex: index out of bounds. */
                    /* proved: arrSlice: index out of bounds. */
                    b138 = a1[v135 + 0] + a1[(v135 ^ 1 <<
                                              (int32_t) (uint32_t) v134) + 0];
                }
                b136 = b138;
            }
            a2[v135 + 0] = b136;
        }
        swap_arr(a1, a2);
        r133 = r0;
    }
    assert(0 + r133 <= r0 && "arrSlice: slice to large.");
    /* proved: copyArr: destination too small. */
    /* proved: arrSlice: index out of bounds. */
    /* proved: arrSlice: slice to large. */
    memcpy(a2, a1, r133 * sizeof(double _Complex));
    swap_arr(a1, a2);
    /* proved: arrSlice: slice to large. */
    r139 = r133;
    for (v140 = 1; v140 <= r129 - 1; v140++) {
        uint32_t v141;
        
        assert(0 + r139 <= r0 && "arrSlice: slice to large.");
        for (v141 = 0; v141 <= r139 - 1; v141++) {
            assert(v141 < r0 && "setArr: index out of bounds.");
            /* proved: arrSlice: slice to large. */
            assert(((v141 >> 1 >> (int32_t) v140 << 1 | (v141 & 1)) <<
                    (int32_t) v140 | (v141 >> 1 & ~(4294967295 <<
                                                    (int32_t) v140))) < r139 &&
                "arrIndex: index out of bounds.");
            /* proved: arrSlice: index out of bounds. */
            a2[v141 + 0] = a1[((v141 >> 1 >> (int32_t) v140 << 1 | (v141 &
                                                                    1)) <<
                               (int32_t) v140 | (v141 >> 1 & ~(4294967295 <<
                                                               (int32_t) v140))) +
                              0];
        }
        swap_arr(a1, a2);
        /* proved: arrSlice: slice to large. */
        r139 = r139;
    }
    return 0;
}
