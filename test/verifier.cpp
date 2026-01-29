#include "common.hpp"
#include "logic.hpp"
#include "transition_system.hpp"
#include "aiger_builder.hpp"
#include "verifier.hpp"
#include <algorithm>

namespace
{

constexpr unsigned int seed = 0x55555555;

transition_system system_from_aiger( variable_store& store, const char* str )
{
    auto aig = read_aiger( str );
    auto sys = builder::build_from_aiger( store, *aig );

    REQUIRE( sys.has_value() );

    return *sys;
}

}

TEST_CASE( "System with an unsafe initial state" )
{
    // 0 -> 1, 0 initial, 0 error
    const auto* const str =
            "aag 1 0 1 1 0\n"
            "2 1\n"
            "3\n";

    auto store = variable_store{};
    const auto system = system_from_aiger( store, str );

    auto checker = verifier{ store, system, seed };
    const auto cex = checker.run();

    REQUIRE( cex.has_value() );
    REQUIRE( cex->size() == 1 );
    REQUIRE( cex->at( 0 ).empty() );
}

TEST_CASE( "Unsafe when input is true in the initial state" )
{
    // 0 -> 1, 0 initial, 0 error under input 1
    const auto* const str =
            "aag 2 1 1 1 0\n"
            "2\n"
            "4 1\n"
            "2\n";

    auto store = variable_store{};
    const auto system = system_from_aiger( store, str );

    auto checker = verifier{ store, system, seed };
    const auto cex = checker.run();

    const auto i = literal{ system.input_vars().nth( 0 ) };

    REQUIRE( cex.has_value() );
    REQUIRE( cex->size() == 1 );
    REQUIRE( cex->at( 0 ) == std::vector{ i } );
}

TEST_CASE( "Unsafe when input is false in the initial state" )
{
    // 0 -> 1, 0 initial, 0 error under input 0
    const auto* const str =
            "aag 2 1 1 1 0\n"
            "2\n"
            "4 1\n"
            "3\n";

    auto store = variable_store{};
    const auto system = system_from_aiger( store, str );

    auto checker = verifier{ store, system, seed };
    const auto cex = checker.run();

    const auto i = literal{ system.input_vars().nth( 0 ) };

    REQUIRE( cex.has_value() );
    REQUIRE( cex->size() == 1 );
    REQUIRE( cex->at( 0 ) == std::vector{ !i } );
}

TEST_CASE( "Unsafe state reached in one step" )
{
    // 0 -> 1, 0 initial, 1 error
    const auto* const str =
            "aag 1 0 1 1 0\n"
            "2 1\n"
            "2\n";

    auto store = variable_store{};
    const auto system = system_from_aiger( store, str );

    auto checker = verifier{ store, system, seed };
    const auto cex = checker.run();

    // Actually technically two steps, the first brings us from 0 to 1 and
    // the second from 1 to "error".

    REQUIRE( cex.has_value() );
    REQUIRE( cex->size() == 2 );
    REQUIRE( cex->at( 0 ).empty() );
    REQUIRE( cex->at( 1 ).empty() );
}

TEST_CASE( "Unsafe four state system" )
{
    // 0 0 -> 1 0
    //  v      v
    // 0 1 -> 1 1
    //
    // x y = 0 0 is initial, 1 1 is error
    // Single input i: when 0, enable x, when 1, enable y

    const auto* const str =
            "aag 10 1 2 1 7\n"
            "2\n"         // i
            "4 19\n"      // x
            "6 21\n"      // y
            "12\n"        // error on x /\ y
            "8 5 3\n"     // -x /\ -i
            "10 7 2\n"    // -y /\ i
            "12 4 6\n"    // x /\ y
            "14 4 2\n"    // x /\ i
            "16 6 3\n"    // y /\ -i
            "18 9 15\n"   // -[ (-x /\ -i) \/ (x /\ i) ]
            "20 11 17\n"; // -[ (-y /\ i) \/ (y /\ -i) ]

    auto store = variable_store{};
    const auto system = system_from_aiger( store, str );

    auto checker = verifier{ store, system, seed };
    const auto cex = checker.run();

    const auto i = literal{ system.input_vars().nth( 0 ) };

    REQUIRE( cex.has_value() );
    REQUIRE( cex->size() == 3 );

    const auto upper_path =
                cex->at( 0 ) == std::vector{ !i } &&
                cex->at( 1 ) == std::vector{ i };

    const auto lower_path =
            cex->at( 0 ) == std::vector{ i } &&
            cex->at( 1 ) == std::vector{ !i };

    REQUIRE( ( upper_path || lower_path ) );
}

TEST_CASE( "Trivially safe four state system" )
{
    const auto* const str =
                "aag 10 1 2 1 7\n"
                "2\n"         // i
                "4 19\n"      // x
                "6 21\n"      // y
                "0\n"         // error is False
                "8 5 3\n"     // -x /\ -i
                "10 7 2\n"    // -y /\ i
                "12 4 6\n"    // x /\ y
                "14 4 2\n"    // x /\ i
                "16 6 3\n"    // y /\ -i
                "18 9 15\n"   // -[ (-x /\ -i) \/ (x /\ i) ]
                "20 11 17\n"; // -[ (-y /\ i) \/ (y /\ -i) ]

    auto store = variable_store{};
    const auto system = system_from_aiger( store, str );

    auto checker = verifier{ store, system, seed };
    const auto cex = checker.run();

    REQUIRE( !cex.has_value() );
}

TEST_CASE( "Unsafe state is not reachable in a two state system" )
{
    // States 0 and 1, self loops, 0 initial, 1 error
    const auto* const str =
            "aag 1 0 1 1 0\n"
            "2 2\n"
            "2\n";

    auto store = variable_store{};
    const auto system = system_from_aiger( store, str );

    auto checker = verifier{ store, system, seed };
    const auto cex = checker.run();

    REQUIRE( !cex.has_value() );
}

TEST_CASE( "Simple counter with an error after 16 steps" )
{
    const auto* const str =
        "aag 16 0 4 0 12 1\n"
        "2 18\n"
        "4 22\n"
        "6 26\n"
        "8 9\n"
        "32\n"
        "10 8 6\n"
        "12 10 4\n"
        "14 12 2\n"
        "16 13 3\n"
        "18 17 15\n"
        "20 11 5\n"
        "22 21 13\n"
        "24 9 7\n"
        "26 25 11\n"
        "28 4 2\n"
        "30 28 6\n"
        "32 30 8\n";

    auto store = variable_store{};
    const auto system = system_from_aiger( store, str );

    auto checker = verifier{ store, system, seed };
    const auto cex = checker.run();

    REQUIRE( cex.has_value() );
    REQUIRE( cex->size() == 16 );

    REQUIRE( system.initial_cube() == std::vector< bool >( 4, false ) );
    REQUIRE( std::ranges::all_of( *cex, []( const std::vector< literal >& inputs ){ return inputs.empty(); } ) );
}

TEST_CASE( "Simple unsafe HWMCC benchmark" )
{
    // This is shortp0.aig from HWMCC 2010, it is publicly available from
    // https://fmv.jku.at/hwmcc10/benchmarks.html.

    const auto* const str =
        "aag 98 10 14 1 74\n"
        "2\n"
        "4\n"
        "6\n"
        "8\n"
        "10\n"
        "12\n"
        "14\n"
        "16\n"
        "18\n"
        "20\n"
        "22 2\n"
        "24 54\n"
        "26 4\n"
        "28 6\n"
        "30 8\n"
        "32 10\n"
        "34 12\n"
        "36 14\n"
        "38 68\n"
        "40 76\n"
        "42 16\n"
        "44 78\n"
        "46 194\n"
        "48 1\n"
        "196\n"
        "50 25 22\n"
        "52 51 20\n"
        "54 53 48\n"
        "56 45 43\n"
        "58 27 25\n"
        "60 58 22\n"
        "62 61 28\n"
        "64 63 57\n"
        "66 65 39\n"
        "68 67 48\n"
        "70 26 25\n"
        "72 71 57\n"
        "74 73 41\n"
        "76 75 48\n"
        "78 57 48\n"
        "80 5 2\n"
        "82 81 7\n"
        "84 82 49\n"
        "86 27 24\n"
        "88 60 29\n"
        "90 89 87\n"
        "92 45 42\n"
        "94 92 23\n"
        "96 93 31\n"
        "98 97 95\n"
        "100 98 9\n"
        "102 99 8\n"
        "104 103 101\n"
        "106 104 90\n"
        "108 93 33\n"
        "110 92 24\n"
        "112 111 109\n"
        "114 112 11\n"
        "116 113 10\n"
        "118 117 115\n"
        "120 118 106\n"
        "122 92 27\n"
        "124 93 35\n"
        "126 125 123\n"
        "128 126 13\n"
        "130 127 12\n"
        "132 131 129\n"
        "134 132 120\n"
        "136 92 29\n"
        "138 93 37\n"
        "140 139 137\n"
        "142 140 15\n"
        "144 141 14\n"
        "146 145 143\n"
        "148 146 134\n"
        "150 31 22\n"
        "152 30 23\n"
        "154 153 151\n"
        "156 34 27\n"
        "158 35 26\n"
        "160 159 157\n"
        "162 36 29\n"
        "164 37 28\n"
        "166 165 163\n"
        "168 166 160\n"
        "170 33 25\n"
        "172 32 24\n"
        "174 173 171\n"
        "176 174 168\n"
        "178 176 154\n"
        "180 178 44\n"
        "182 180 38\n"
        "184 182 40\n"
        "186 185 18\n"
        "188 187 46\n"
        "190 188 148\n"
        "192 191 48\n"
        "194 193 85\n"
        "196 188 18\n";

    auto store = variable_store{};
    const auto system = system_from_aiger( store, str );

    auto checker = verifier{ store, system, seed };
    const auto cex = checker.run();

    REQUIRE( cex.has_value() );
    REQUIRE( system.initial_cube() == std::vector< bool >( 14, false ) );

    // The specific counterexample is not checked, as there are many instances,
    // and we have no idea which one will be picked.
}

TEST_CASE( "Simple safe HWMCC benchmark" )
{
    // This is pdtpmsarbiter.aig from HWMCC 2010, it is publicly available from
    // https://fmv.jku.at/hwmcc10/benchmarks.html.

    const auto* const str =
        "aag 258 3 46 1 209\n"
        "2\n"
        "4\n"
        "6\n"
        "8 131\n"
        "10 141\n"
        "12 152\n"
        "14 163\n"
        "16 169\n"
        "18 175\n"
        "20 185\n"
        "22 198\n"
        "24 209\n"
        "26 218\n"
        "28 236\n"
        "30 251\n"
        "32 271\n"
        "34 274\n"
        "36 284\n"
        "38 293\n"
        "40 302\n"
        "42 311\n"
        "44 327\n"
        "46 330\n"
        "48 341\n"
        "50 347\n"
        "52 366\n"
        "54 371\n"
        "56 385\n"
        "58 413\n"
        "60 419\n"
        "62 425\n"
        "64 429\n"
        "66 433\n"
        "68 233\n"
        "70 437\n"
        "72 440\n"
        "74 445\n"
        "76 456\n"
        "78 460\n"
        "80 469\n"
        "82 473\n"
        "84 481\n"
        "86 485\n"
        "88 486\n"
        "90 496\n"
        "92 503\n"
        "94 507\n"
        "96 515\n"
        "98 516\n"
        "121\n"
        "100 86 40\n"
        "102 87 41\n"
        "104 103 50\n"
        "106 105 101\n"
        "108 94 48\n"
        "110 109 15\n"
        "112 95 49\n"
        "114 113 111\n"
        "116 114 106\n"
        "118 115 107\n"
        "120 119 117\n"
        "122 43 2\n"
        "124 122 17\n"
        "126 17 2\n"
        "128 127 8\n"
        "130 129 125\n"
        "132 39 6\n"
        "134 132 11\n"
        "136 39 10\n"
        "138 136 15\n"
        "140 139 135\n"
        "142 77 31\n"
        "144 142 85\n"
        "146 145 73\n"
        "148 146 12\n"
        "150 147 13\n"
        "152 151 149\n"
        "154 88 55\n"
        "156 89 54\n"
        "158 156 19\n"
        "160 159 14\n"
        "162 161 155\n"
        "164 43 16\n"
        "166 164 95\n"
        "168 167 125\n"
        "170 11 6\n"
        "172 171 18\n"
        "174 173 135\n"
        "176 81 4\n"
        "178 176 21\n"
        "180 81 20\n"
        "182 180 49\n"
        "184 183 179\n"
        "186 91 53\n"
        "188 186 45\n"
        "190 189 47\n"
        "192 190 78\n"
        "194 65 23\n"
        "196 194 62\n"
        "198 196 192\n"
        "200 67 24\n"
        "202 200 3\n"
        "204 66 25\n"
        "206 204 50\n"
        "208 207 203\n"
        "210 145 13\n"
        "212 210 146\n"
        "214 71 34\n"
        "216 214 27\n"
        "218 216 212\n"
        "220 69 29\n"
        "222 220 147\n"
        "224 222 210\n"
        "226 69 28\n"
        "228 68 29\n"
        "230 228 36\n"
        "232 231 227\n"
        "234 232 36\n"
        "236 234 224\n"
        "238 97 58\n"
        "240 97 59\n"
        "242 240 148\n"
        "244 243 239\n"
        "246 245 83\n"
        "248 241 30\n"
        "250 249 247\n"
        "252 74 33\n"
        "254 252 40\n"
        "256 75 32\n"
        "258 75 33\n"
        "260 258 6\n"
        "262 256 6\n"
        "264 263 255\n"
        "266 264 261\n"
        "268 266 256\n"
        "270 269 255\n"
        "272 261 35\n"
        "274 273 263\n"
        "276 200 2\n"
        "278 67 25\n"
        "280 278 2\n"
        "282 281 37\n"
        "284 283 277\n"
        "286 136 14\n"
        "288 38 7\n"
        "290 288 11\n"
        "292 291 287\n"
        "294 70 27\n"
        "296 294 35\n"
        "298 71 26\n"
        "300 299 41\n"
        "302 301 297\n"
        "304 164 94\n"
        "306 42 3\n"
        "308 306 17\n"
        "310 309 305\n"
        "312 189 79\n"
        "314 89 55\n"
        "316 314 47\n"
        "318 316 312\n"
        "320 318 19\n"
        "322 159 45\n"
        "324 323 315\n"
        "326 325 321\n"
        "328 188 47\n"
        "330 329 313\n"
        "332 65 22\n"
        "334 64 23\n"
        "336 334 63\n"
        "338 337 48\n"
        "340 339 333\n"
        "342 228 37\n"
        "344 343 50\n"
        "346 345 227\n"
        "348 312 46\n"
        "350 99 61\n"
        "352 350 349\n"
        "354 350 8\n"
        "356 99 60\n"
        "358 356 9\n"
        "360 351 53\n"
        "362 360 359\n"
        "364 363 355\n"
        "366 364 353\n"
        "368 159 156\n"
        "370 369 155\n"
        "372 57 4\n"
        "374 372 93\n"
        "376 93 56\n"
        "378 376 86\n"
        "380 379 373\n"
        "382 380 376\n"
        "384 383 375\n"
        "386 96 59\n"
        "388 238 83\n"
        "390 389 387\n"
        "392 391 241\n"
        "394 242 82\n"
        "396 395 393\n"
        "398 396 238\n"
        "400 399 396\n"
        "402 238 82\n"
        "404 403 387\n"
        "406 405 395\n"
        "408 406 401\n"
        "410 404 398\n"
        "412 411 409\n"
        "414 98 61\n"
        "416 359 356\n"
        "418 417 415\n"
        "420 21 4\n"
        "422 421 62\n"
        "424 423 179\n"
        "426 337 334\n"
        "428 427 333\n"
        "430 204 51\n"
        "432 431 281\n"
        "434 294 34\n"
        "436 435 299\n"
        "438 144 73\n"
        "440 439 211\n"
        "442 266 252\n"
        "444 443 261\n"
        "446 71 27\n"
        "448 212 35\n"
        "450 449 446\n"
        "452 447 77\n"
        "454 452 297\n"
        "456 455 451\n"
        "458 191 79\n"
        "460 459 193\n"
        "462 180 48\n"
        "464 80 5\n"
        "466 464 21\n"
        "468 467 463\n"
        "470 373 82\n"
        "472 471 375\n"
        "474 229 225\n"
        "476 475 37\n"
        "478 221 84\n"
        "480 479 477\n"
        "482 393 86\n"
        "484 483 387\n"
        "486 318 18\n"
        "488 194 193\n"
        "490 195 91\n"
        "492 490 337\n"
        "494 493 197\n"
        "496 494 489\n"
        "498 92 57\n"
        "500 498 380\n"
        "502 501 379\n"
        "504 359 94\n"
        "506 505 415\n"
        "508 396 386\n"
        "510 509 395\n"
        "512 511 404\n"
        "514 513 509\n"
        "516 354 348\n";

    auto store = variable_store{};
    const auto system = system_from_aiger( store, str );

    auto checker = verifier{ store, system, seed };
    const auto cex = checker.run();

    REQUIRE( !cex.has_value() );
}