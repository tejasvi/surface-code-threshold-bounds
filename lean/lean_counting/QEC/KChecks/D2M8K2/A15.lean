import QEC.Count.ChunksK3
import QEC.KChecks.D2M8K2.A14

namespace QECKChecks.D2M8K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows3230 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3230 = true := by
  rw [show D2M8K2.u3230 = KTree.node D2M8K2.u3228 (nat_lit 7667463) (nat_lit 2919492058) (nat_lit 0) D2M8K2.u3229 from rfl, allE_node, arows3228, irow3230, arows3229]
  all_goals rfl

theorem atot3230 : totK PD2M8K2 D2M8K2.u3230 = [174930887950, 684692699561, 1308201275306, 1136836359464, 215950542689, 4977114383, 0, 0] := by
  rw [show D2M8K2.u3230 = KTree.node D2M8K2.u3228 (nat_lit 7667463) (nat_lit 2919492058) (nat_lit 0) D2M8K2.u3229 from rfl, totK_node, atot3228, atot3229]
  decide +kernel

theorem arows3233 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3233 = true := by
  rw [show D2M8K2.u3233 = KTree.node D2M8K2.u3231 (nat_lit 7675005) (nat_lit 1499823526) (nat_lit 0) D2M8K2.u3232 from rfl, allE_node, arows3231, irow3233, arows3232]
  all_goals rfl

theorem atot3233 : totK PD2M8K2 D2M8K2.u3233 = [461833412945, 1587619117163, 1376550965143, 195826925775, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u3233 = KTree.node D2M8K2.u3231 (nat_lit 7675005) (nat_lit 1499823526) (nat_lit 0) D2M8K2.u3232 from rfl, totK_node, atot3231, atot3232]
  decide +kernel

theorem arows3237 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3237 = true := by
  rw [show D2M8K2.u3237 = KTree.node D2M8K2.u3235 (nat_lit 7678453) (nat_lit 1199424954) (nat_lit 0) D2M8K2.u3236 from rfl, allE_node, arows3235, irow3237, arows3236]
  all_goals rfl

theorem atot3237 : totK PD2M8K2 D2M8K2.u3237 = [313073302598, 1236823680415, 1514065528213, 579713378766, 37554459744, 0, 0, 0] := by
  rw [show D2M8K2.u3237 = KTree.node D2M8K2.u3235 (nat_lit 7678453) (nat_lit 1199424954) (nat_lit 0) D2M8K2.u3236 from rfl, totK_node, atot3235, atot3236]
  decide +kernel

theorem arows3240 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3240 = true := by
  rw [show D2M8K2.u3240 = KTree.node D2M8K2.u3238 (nat_lit 7681781) (nat_lit 2306311609) (nat_lit 0) D2M8K2.u3239 from rfl, allE_node, arows3238, irow3240, arows3239]
  all_goals rfl

theorem atot3240 : totK PD2M8K2 D2M8K2.u3240 = [511601856036, 1556572757313, 1305194210726, 259163318671, 9474550098, 0, 0, 0] := by
  rw [show D2M8K2.u3240 = KTree.node D2M8K2.u3238 (nat_lit 7681781) (nat_lit 2306311609) (nat_lit 0) D2M8K2.u3239 from rfl, totK_node, atot3238, atot3239]
  decide +kernel

theorem arows3245 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3245 = true := by
  rw [show D2M8K2.u3245 = KTree.node D2M8K2.u3243 (nat_lit 7685650) (nat_lit 3258114910) (nat_lit 0) D2M8K2.u3244 from rfl, allE_node, arows3243, irow3245, arows3244]
  all_goals rfl

theorem atot3245 : totK PD2M8K2 D2M8K2.u3245 = [369267219880, 1428453327239, 1452412770562, 342505433092, 13243784863, 0, 0, 0] := by
  rw [show D2M8K2.u3245 = KTree.node D2M8K2.u3243 (nat_lit 7685650) (nat_lit 3258114910) (nat_lit 0) D2M8K2.u3244 from rfl, totK_node, atot3243, atot3244]
  decide +kernel

theorem arows3248 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3248 = true := by
  rw [show D2M8K2.u3248 = KTree.node D2M8K2.u3246 (nat_lit 7692101) (nat_lit 2366851252) (nat_lit 0) D2M8K2.u3247 from rfl, allE_node, arows3246, irow3248, arows3247]
  all_goals rfl

theorem atot3248 : totK PD2M8K2 D2M8K2.u3248 = [157524901095, 1080046491717, 1732714570068, 602872960127, 27384849158, 0, 0, 0] := by
  rw [show D2M8K2.u3248 = KTree.node D2M8K2.u3246 (nat_lit 7692101) (nat_lit 2366851252) (nat_lit 0) D2M8K2.u3247 from rfl, totK_node, atot3246, atot3247]
  decide +kernel

theorem arows3252 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3252 = true := by
  rw [show D2M8K2.u3252 = KTree.node D2M8K2.u3250 (nat_lit 7695949) (nat_lit 1311400635) (nat_lit 0) D2M8K2.u3251 from rfl, allE_node, arows3250, irow3252, arows3251]
  all_goals rfl

theorem atot3252 : totK PD2M8K2 D2M8K2.u3252 = [0, 485673159889, 1622979384501, 1323353728970, 159949513110, 1310285577, 0, 0] := by
  rw [show D2M8K2.u3252 = KTree.node D2M8K2.u3250 (nat_lit 7695949) (nat_lit 1311400635) (nat_lit 0) D2M8K2.u3251 from rfl, totK_node, atot3250, atot3251]
  decide +kernel

theorem arows3255 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3255 = true := by
  rw [show D2M8K2.u3255 = KTree.node D2M8K2.u3253 (nat_lit 7700793) (nat_lit 1795538838) (nat_lit 0) D2M8K2.u3254 from rfl, allE_node, arows3253, irow3255, arows3254]
  all_goals rfl

theorem atot3255 : totK PD2M8K2 D2M8K2.u3255 = [0, 508049767481, 1602747474943, 1291865772005, 211928198221, 4879840392, 0, 0] := by
  rw [show D2M8K2.u3255 = KTree.node D2M8K2.u3253 (nat_lit 7700793) (nat_lit 1795538838) (nat_lit 0) D2M8K2.u3254 from rfl, totK_node, atot3253, atot3254]
  decide +kernel

theorem arows3262 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3262 = true := by
  rw [show D2M8K2.u3262 = KTree.node D2M8K2.u3260 (nat_lit 7705067) (nat_lit 2893051917) (nat_lit 0) D2M8K2.u3261 from rfl, allE_node, arows3260, irow3262, arows3261]
  all_goals rfl

theorem atot3262 : totK PD2M8K2 D2M8K2.u3262 = [0, 432563576478, 1573149391280, 1331738411200, 216143022763, 4931404646, 0, 0] := by
  rw [show D2M8K2.u3262 = KTree.node D2M8K2.u3260 (nat_lit 7705067) (nat_lit 2893051917) (nat_lit 0) D2M8K2.u3261 from rfl, totK_node, atot3260, atot3261]
  decide +kernel

theorem arows3265 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3265 = true := by
  rw [show D2M8K2.u3265 = KTree.node D2M8K2.u3263 (nat_lit 7712046) (nat_lit 3841222845) (nat_lit 0) D2M8K2.u3264 from rfl, allE_node, arows3263, irow3265, arows3264]
  all_goals rfl

theorem atot3265 : totK PD2M8K2 D2M8K2.u3265 = [0, 354241483738, 1360690148327, 1474082706528, 371169670874, 12146940058, 0, 0] := by
  rw [show D2M8K2.u3265 = KTree.node D2M8K2.u3263 (nat_lit 7712046) (nat_lit 3841222845) (nat_lit 0) D2M8K2.u3264 from rfl, totK_node, atot3263, atot3264]
  decide +kernel

theorem arows3269 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3269 = true := by
  rw [show D2M8K2.u3269 = KTree.node D2M8K2.u3267 (nat_lit 7715291) (nat_lit 2904133038) (nat_lit 0) D2M8K2.u3268 from rfl, allE_node, arows3267, irow3269, arows3268]
  all_goals rfl

theorem atot3269 : totK PD2M8K2 D2M8K2.u3269 = [0, 490259591050, 1585178385662, 1285945810854, 212516460177, 10973378440, 0, 0] := by
  rw [show D2M8K2.u3269 = KTree.node D2M8K2.u3267 (nat_lit 7715291) (nat_lit 2904133038) (nat_lit 0) D2M8K2.u3268 from rfl, totK_node, atot3267, atot3268]
  decide +kernel

theorem arows3272 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3272 = true := by
  rw [show D2M8K2.u3272 = KTree.node D2M8K2.u3270 (nat_lit 7725792) (nat_lit 3334003043) (nat_lit 0) D2M8K2.u3271 from rfl, allE_node, arows3270, irow3272, arows3271]
  all_goals rfl

theorem atot3272 : totK PD2M8K2 D2M8K2.u3272 = [0, 358843767281, 1407393531526, 1456979945104, 337294064267, 13189998508, 0, 0] := by
  rw [show D2M8K2.u3272 = KTree.node D2M8K2.u3270 (nat_lit 7725792) (nat_lit 3334003043) (nat_lit 0) D2M8K2.u3271 from rfl, totK_node, atot3270, atot3271]
  decide +kernel

theorem arows3277 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3277 = true := by
  rw [show D2M8K2.u3277 = KTree.node D2M8K2.u3275 (nat_lit 7728919) (nat_lit 2224320227) (nat_lit 0) D2M8K2.u3276 from rfl, allE_node, arows3275, irow3277, arows3276]
  all_goals rfl

theorem atot3277 : totK PD2M8K2 D2M8K2.u3277 = [0, 475530351893, 1551395741609, 1312513405857, 212286358329, 4917684815, 0, 0] := by
  rw [show D2M8K2.u3277 = KTree.node D2M8K2.u3275 (nat_lit 7728919) (nat_lit 2224320227) (nat_lit 0) D2M8K2.u3276 from rfl, totK_node, atot3275, atot3276]
  decide +kernel

theorem arows3280 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3280 = true := by
  rw [show D2M8K2.u3280 = KTree.node D2M8K2.u3278 (nat_lit 7732851) (nat_lit 1991966946) (nat_lit 0) D2M8K2.u3279 from rfl, allE_node, arows3278, irow3280, arows3279]
  all_goals rfl

theorem atot3280 : totK PD2M8K2 D2M8K2.u3280 = [0, 317439273682, 1376263423049, 1533099876563, 363967839334, 13750795750, 0, 0] := by
  rw [show D2M8K2.u3280 = KTree.node D2M8K2.u3278 (nat_lit 7732851) (nat_lit 1991966946) (nat_lit 0) D2M8K2.u3279 from rfl, totK_node, atot3278, atot3279]
  decide +kernel

theorem arows3284 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3284 = true := by
  rw [show D2M8K2.u3284 = KTree.node D2M8K2.u3282 (nat_lit 7736312) (nat_lit 3546176706) (nat_lit 0) D2M8K2.u3283 from rfl, allE_node, arows3282, irow3284, arows3283]
  all_goals rfl

theorem atot3284 : totK PD2M8K2 D2M8K2.u3284 = [0, 0, 485093105570, 1692829151984, 1145719406916, 123616780906, 1310517177, 0] := by
  rw [show D2M8K2.u3284 = KTree.node D2M8K2.u3282 (nat_lit 7736312) (nat_lit 3546176706) (nat_lit 0) D2M8K2.u3283 from rfl, totK_node, atot3282, atot3283]
  decide +kernel

theorem arows3287 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3287 = true := by
  rw [show D2M8K2.u3287 = KTree.node D2M8K2.u3285 (nat_lit 7748718) (nat_lit 3983372916) (nat_lit 0) D2M8K2.u3286 from rfl, allE_node, arows3285, irow3287, arows3286]
  all_goals rfl

theorem atot3287 : totK PD2M8K2 D2M8K2.u3287 = [0, 0, 762885916972, 1914198927585, 795232914083, 38408224876, 0, 0] := by
  rw [show D2M8K2.u3287 = KTree.node D2M8K2.u3285 (nat_lit 7748718) (nat_lit 3983372916) (nat_lit 0) D2M8K2.u3286 from rfl, totK_node, atot3285, atot3286]
  decide +kernel

theorem arows3293 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3293 = true := by
  rw [show D2M8K2.u3293 = KTree.node D2M8K2.u3291 (nat_lit 7759349) (nat_lit 2401362874) (nat_lit 0) D2M8K2.u3292 from rfl, allE_node, arows3291, irow3293, arows3292]
  all_goals rfl

theorem atot3293 : totK PD2M8K2 D2M8K2.u3293 = [0, 444856484744, 1515672737749, 1384396694253, 320631475403, 12810146349, 0, 0] := by
  rw [show D2M8K2.u3293 = KTree.node D2M8K2.u3291 (nat_lit 7759349) (nat_lit 2401362874) (nat_lit 0) D2M8K2.u3292 from rfl, totK_node, atot3291, atot3292]
  decide +kernel

theorem arows3296 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3296 = true := by
  rw [show D2M8K2.u3296 = KTree.node D2M8K2.u3294 (nat_lit 7762067) (nat_lit 2764024456) (nat_lit 0) D2M8K2.u3295 from rfl, allE_node, arows3294, irow3296, arows3295]
  all_goals rfl

theorem atot3296 : totK PD2M8K2 D2M8K2.u3296 = [0, 346386984557, 1238407994191, 1464835357809, 567844512252, 37500007640, 0, 0] := by
  rw [show D2M8K2.u3296 = KTree.node D2M8K2.u3294 (nat_lit 7762067) (nat_lit 2764024456) (nat_lit 0) D2M8K2.u3295 from rfl, totK_node, atot3294, atot3295]
  decide +kernel

theorem arows3300 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3300 = true := by
  rw [show D2M8K2.u3300 = KTree.node D2M8K2.u3298 (nat_lit 7766032) (nat_lit 3148158631) (nat_lit 0) D2M8K2.u3299 from rfl, allE_node, arows3298, irow3300, arows3299]
  all_goals rfl

theorem atot3300 : totK PD2M8K2 D2M8K2.u3300 = [0, 426343457107, 1525375597903, 1415800890089, 263865417726, 5370412161, 0, 0] := by
  rw [show D2M8K2.u3300 = KTree.node D2M8K2.u3298 (nat_lit 7766032) (nat_lit 3148158631) (nat_lit 0) D2M8K2.u3299 from rfl, totK_node, atot3298, atot3299]
  decide +kernel

theorem arows3303 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3303 = true := by
  rw [show D2M8K2.u3303 = KTree.node D2M8K2.u3301 (nat_lit 7769415) (nat_lit 3638013176) (nat_lit 0) D2M8K2.u3302 from rfl, allE_node, arows3301, irow3303, arows3302]
  all_goals rfl

theorem atot3303 : totK PD2M8K2 D2M8K2.u3303 = [0, 411511151455, 1447436978991, 1388684549855, 331937787571, 13183084702, 0, 0] := by
  rw [show D2M8K2.u3303 = KTree.node D2M8K2.u3301 (nat_lit 7769415) (nat_lit 3638013176) (nat_lit 0) D2M8K2.u3302 from rfl, totK_node, atot3301, atot3302]
  decide +kernel

theorem arows3308 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3308 = true := by
  rw [show D2M8K2.u3308 = KTree.node D2M8K2.u3306 (nat_lit 7773027) (nat_lit 3682515351) (nat_lit 0) D2M8K2.u3307 from rfl, allE_node, arows3306, irow3308, arows3307]
  all_goals rfl

theorem atot3308 : totK PD2M8K2 D2M8K2.u3308 = [0, 417349524314, 1517956957250, 1441350674690, 263788253147, 5112446890, 0, 0] := by
  rw [show D2M8K2.u3308 = KTree.node D2M8K2.u3306 (nat_lit 7773027) (nat_lit 3682515351) (nat_lit 0) D2M8K2.u3307 from rfl, totK_node, atot3306, atot3307]
  decide +kernel

theorem arows3311 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3311 = true := by
  rw [show D2M8K2.u3311 = KTree.node D2M8K2.u3309 (nat_lit 7838433) (nat_lit 1737235550) (nat_lit 0) D2M8K2.u3310 from rfl, allE_node, arows3309, irow3311, arows3310]
  all_goals rfl

theorem atot3311 : totK PD2M8K2 D2M8K2.u3311 = [0, 396589999066, 1418587889103, 1367717137239, 350563058580, 16594763897, 0, 0] := by
  rw [show D2M8K2.u3311 = KTree.node D2M8K2.u3309 (nat_lit 7838433) (nat_lit 1737235550) (nat_lit 0) D2M8K2.u3310 from rfl, totK_node, atot3309, atot3310]
  decide +kernel

theorem arows3315 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3315 = true := by
  rw [show D2M8K2.u3315 = KTree.node D2M8K2.u3313 (nat_lit 7842448) (nat_lit 3618269625) (nat_lit 0) D2M8K2.u3314 from rfl, allE_node, arows3313, irow3315, arows3314]
  all_goals rfl

theorem atot3315 : totK PD2M8K2 D2M8K2.u3315 = [0, 426371011301, 1512077171047, 1410317977213, 272732718544, 14873436274, 0, 0] := by
  rw [show D2M8K2.u3315 = KTree.node D2M8K2.u3313 (nat_lit 7842448) (nat_lit 3618269625) (nat_lit 0) D2M8K2.u3314 from rfl, totK_node, atot3313, atot3314]
  decide +kernel

theorem arows3318 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3318 = true := by
  rw [show D2M8K2.u3318 = KTree.node D2M8K2.u3316 (nat_lit 7848686) (nat_lit 2975112356) (nat_lit 0) D2M8K2.u3317 from rfl, allE_node, arows3316, irow3318, arows3317]
  all_goals rfl

theorem atot3318 : totK PD2M8K2 D2M8K2.u3318 = [0, 445630166084, 1377739891415, 1357863716930, 434223896773, 16646887132, 0, 0] := by
  rw [show D2M8K2.u3318 = KTree.node D2M8K2.u3316 (nat_lit 7848686) (nat_lit 2975112356) (nat_lit 0) D2M8K2.u3317 from rfl, totK_node, atot3316, atot3317]
  decide +kernel

theorem arows3327 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3327 = true := by
  rw [show D2M8K2.u3327 = KTree.node D2M8K2.u3325 (nat_lit 7851803) (nat_lit 2880308392) (nat_lit 0) D2M8K2.u3326 from rfl, allE_node, arows3325, irow3327, arows3326]
  all_goals rfl

theorem atot3327 : totK PD2M8K2 D2M8K2.u3327 = [0, 341642900289, 1386155719049, 1484598102022, 351037252048, 13250685261, 0, 0] := by
  rw [show D2M8K2.u3327 = KTree.node D2M8K2.u3325 (nat_lit 7851803) (nat_lit 2880308392) (nat_lit 0) D2M8K2.u3326 from rfl, totK_node, atot3325, atot3326]
  decide +kernel

theorem arows3330 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3330 = true := by
  rw [show D2M8K2.u3330 = KTree.node D2M8K2.u3328 (nat_lit 7855488) (nat_lit 3757402556) (nat_lit 0) D2M8K2.u3329 from rfl, allE_node, arows3328, irow3330, arows3329]
  all_goals rfl

theorem atot3330 : totK PD2M8K2 D2M8K2.u3330 = [0, 459419510060, 1544627263975, 1354693316265, 222990552953, 4980514959, 0, 0] := by
  rw [show D2M8K2.u3330 = KTree.node D2M8K2.u3328 (nat_lit 7855488) (nat_lit 3757402556) (nat_lit 0) D2M8K2.u3329 from rfl, totK_node, atot3328, atot3329]
  decide +kernel

theorem arows3334 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3334 = true := by
  rw [show D2M8K2.u3334 = KTree.node D2M8K2.u3332 (nat_lit 7858728) (nat_lit 3493111030) (nat_lit 0) D2M8K2.u3333 from rfl, allE_node, arows3332, irow3334, arows3333]
  all_goals rfl

theorem atot3334 : totK PD2M8K2 D2M8K2.u3334 = [0, 30722815107, 876507281453, 1864845661168, 687239350203, 31911335214, 0, 0] := by
  rw [show D2M8K2.u3334 = KTree.node D2M8K2.u3332 (nat_lit 7858728) (nat_lit 3493111030) (nat_lit 0) D2M8K2.u3333 from rfl, totK_node, atot3332, atot3333]
  decide +kernel

theorem arows3337 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3337 = true := by
  rw [show D2M8K2.u3337 = KTree.node D2M8K2.u3335 (nat_lit 7862827) (nat_lit 1587519067) (nat_lit 0) D2M8K2.u3336 from rfl, allE_node, arows3335, irow3337, arows3336]
  all_goals rfl

theorem atot3337 : totK PD2M8K2 D2M8K2.u3337 = [0, 0, 581452820782, 1679651220947, 1134118801280, 136016835202, 1217496766, 0] := by
  rw [show D2M8K2.u3337 = KTree.node D2M8K2.u3335 (nat_lit 7862827) (nat_lit 1587519067) (nat_lit 0) D2M8K2.u3336 from rfl, totK_node, atot3335, atot3336]
  decide +kernel

theorem arows3342 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3342 = true := by
  rw [show D2M8K2.u3342 = KTree.node D2M8K2.u3340 (nat_lit 7870929) (nat_lit 1245572899) (nat_lit 0) D2M8K2.u3341 from rfl, allE_node, arows3340, irow3342, arows3341]
  all_goals rfl

theorem atot3342 : totK PD2M8K2 D2M8K2.u3342 = [0, 0, 377086089712, 1461096991261, 1382096604951, 309740938305, 13105450397, 0] := by
  rw [show D2M8K2.u3342 = KTree.node D2M8K2.u3340 (nat_lit 7870929) (nat_lit 1245572899) (nat_lit 0) D2M8K2.u3341 from rfl, totK_node, atot3340, atot3341]
  decide +kernel

theorem arows3345 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3345 = true := by
  rw [show D2M8K2.u3345 = KTree.node D2M8K2.u3343 (nat_lit 7874090) (nat_lit 4182302026) (nat_lit 0) D2M8K2.u3344 from rfl, allE_node, arows3343, irow3345, arows3344]
  all_goals rfl

theorem atot3345 : totK PD2M8K2 D2M8K2.u3345 = [0, 0, 469755441949, 1589739275277, 1160210962573, 176239365087, 4630915822, 0] := by
  rw [show D2M8K2.u3345 = KTree.node D2M8K2.u3343 (nat_lit 7874090) (nat_lit 4182302026) (nat_lit 0) D2M8K2.u3344 from rfl, totK_node, atot3343, atot3344]
  decide +kernel

theorem arows3349 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3349 = true := by
  rw [show D2M8K2.u3349 = KTree.node D2M8K2.u3347 (nat_lit 7879899) (nat_lit 1635522287) (nat_lit 0) D2M8K2.u3348 from rfl, allE_node, arows3347, irow3349, arows3348]
  all_goals rfl

theorem atot3349 : totK PD2M8K2 D2M8K2.u3349 = [0, 376911479923, 1376113839041, 1380326919775, 416832516305, 25140543007, 0, 0] := by
  rw [show D2M8K2.u3349 = KTree.node D2M8K2.u3347 (nat_lit 7879899) (nat_lit 1635522287) (nat_lit 0) D2M8K2.u3348 from rfl, totK_node, atot3347, atot3348]
  decide +kernel

theorem arows3352 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3352 = true := by
  rw [show D2M8K2.u3352 = KTree.node D2M8K2.u3350 (nat_lit 7884001) (nat_lit 1490931563) (nat_lit 0) D2M8K2.u3351 from rfl, allE_node, arows3350, irow3352, arows3351]
  all_goals rfl

theorem atot3352 : totK PD2M8K2 D2M8K2.u3352 = [0, 419665595470, 1518075245984, 1421230568610, 288535096527, 10965212115, 0, 0] := by
  rw [show D2M8K2.u3352 = KTree.node D2M8K2.u3350 (nat_lit 7884001) (nat_lit 1490931563) (nat_lit 0) D2M8K2.u3351 from rfl, totK_node, atot3350, atot3351]
  decide +kernel

theorem arows3358 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3358 = true := by
  rw [show D2M8K2.u3358 = KTree.node D2M8K2.u3356 (nat_lit 7887168) (nat_lit 3705351137) (nat_lit 0) D2M8K2.u3357 from rfl, allE_node, arows3356, irow3358, arows3357]
  all_goals rfl

theorem atot3358 : totK PD2M8K2 D2M8K2.u3358 = [0, 327026360424, 1417440457836, 1542966588773, 331307491116, 6482428250, 0, 0] := by
  rw [show D2M8K2.u3358 = KTree.node D2M8K2.u3356 (nat_lit 7887168) (nat_lit 3705351137) (nat_lit 0) D2M8K2.u3357 from rfl, totK_node, atot3356, atot3357]
  decide +kernel

theorem arows3361 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3361 = true := by
  rw [show D2M8K2.u3361 = KTree.node D2M8K2.u3359 (nat_lit 7891370) (nat_lit 4169057333) (nat_lit 0) D2M8K2.u3360 from rfl, allE_node, arows3359, irow3361, arows3360]
  all_goals rfl

theorem atot3361 : totK PD2M8K2 D2M8K2.u3361 = [0, 423601337770, 1440060885087, 1382971645708, 319010724258, 13130749562, 0, 0] := by
  rw [show D2M8K2.u3361 = KTree.node D2M8K2.u3359 (nat_lit 7891370) (nat_lit 4169057333) (nat_lit 0) D2M8K2.u3360 from rfl, totK_node, atot3359, atot3360]
  decide +kernel

theorem arows3365 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3365 = true := by
  rw [show D2M8K2.u3365 = KTree.node D2M8K2.u3363 (nat_lit 7894461) (nat_lit 1563116754) (nat_lit 0) D2M8K2.u3364 from rfl, allE_node, arows3363, irow3365, arows3364]
  all_goals rfl

theorem atot3365 : totK PD2M8K2 D2M8K2.u3365 = [0, 435665402311, 1538591899902, 1380273413742, 235307239937, 4678454933, 0, 0] := by
  rw [show D2M8K2.u3365 = KTree.node D2M8K2.u3363 (nat_lit 7894461) (nat_lit 1563116754) (nat_lit 0) D2M8K2.u3364 from rfl, totK_node, atot3363, atot3364]
  decide +kernel

theorem arows3368 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3368 = true := by
  rw [show D2M8K2.u3368 = KTree.node D2M8K2.u3366 (nat_lit 7901745) (nat_lit 1608952957) (nat_lit 0) D2M8K2.u3367 from rfl, allE_node, arows3366, irow3368, arows3367]
  all_goals rfl

theorem atot3368 : totK PD2M8K2 D2M8K2.u3368 = [0, 0, 538724817112, 1725678951922, 1083555239938, 101106644596, 1138244013, 0] := by
  rw [show D2M8K2.u3368 = KTree.node D2M8K2.u3366 (nat_lit 7901745) (nat_lit 1608952957) (nat_lit 0) D2M8K2.u3367 from rfl, totK_node, atot3366, atot3367]
  decide +kernel

theorem arows3373 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3373 = true := by
  rw [show D2M8K2.u3373 = KTree.node D2M8K2.u3371 (nat_lit 7907965) (nat_lit 1223849724) (nat_lit 0) D2M8K2.u3372 from rfl, allE_node, arows3371, irow3373, arows3372]
  all_goals rfl

theorem atot3373 : totK PD2M8K2 D2M8K2.u3373 = [0, 0, 904985489019, 1925262264190, 698767386460, 27396754644, 0, 0] := by
  rw [show D2M8K2.u3373 = KTree.node D2M8K2.u3371 (nat_lit 7907965) (nat_lit 1223849724) (nat_lit 0) D2M8K2.u3372 from rfl, totK_node, atot3371, atot3372]
  decide +kernel

theorem arows3376 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3376 = true := by
  rw [show D2M8K2.u3376 = KTree.node D2M8K2.u3374 (nat_lit 7914869) (nat_lit 2400409922) (nat_lit 0) D2M8K2.u3375 from rfl, allE_node, arows3374, irow3376, arows3375]
  all_goals rfl

theorem atot3376 : totK PD2M8K2 D2M8K2.u3376 = [0, 0, 583838295798, 1738590206333, 1032128838582, 102404704906, 1095107716, 0] := by
  rw [show D2M8K2.u3376 = KTree.node D2M8K2.u3374 (nat_lit 7914869) (nat_lit 2400409922) (nat_lit 0) D2M8K2.u3375 from rfl, totK_node, atot3374, atot3375]
  decide +kernel

theorem arows3380 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3380 = true := by
  rw [show D2M8K2.u3380 = KTree.node D2M8K2.u3378 (nat_lit 7922282) (nat_lit 3758588255) (nat_lit 0) D2M8K2.u3379 from rfl, allE_node, arows3378, irow3380, arows3379]
  all_goals rfl

theorem atot3380 : totK PD2M8K2 D2M8K2.u3380 = [0, 378836717440, 1307128904787, 1268273545512, 484342633779, 94972455908, 3819176523, 0] := by
  rw [show D2M8K2.u3380 = KTree.node D2M8K2.u3378 (nat_lit 7922282) (nat_lit 3758588255) (nat_lit 0) D2M8K2.u3379 from rfl, totK_node, atot3378, atot3379]
  decide +kernel

theorem arows3383 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3383 = true := by
  rw [show D2M8K2.u3383 = KTree.node D2M8K2.u3381 (nat_lit 7926074) (nat_lit 4243551115) (nat_lit 0) D2M8K2.u3382 from rfl, allE_node, arows3381, irow3383, arows3382]
  all_goals rfl

theorem atot3383 : totK PD2M8K2 D2M8K2.u3383 = [0, 420759482127, 1422622866807, 1393907088450, 410560362954, 24726425107, 0, 0] := by
  rw [show D2M8K2.u3383 = KTree.node D2M8K2.u3381 (nat_lit 7926074) (nat_lit 4243551115) (nat_lit 0) D2M8K2.u3382 from rfl, totK_node, atot3381, atot3382]
  decide +kernel

theorem arows3390 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3390 = true := by
  rw [show D2M8K2.u3390 = KTree.node D2M8K2.u3388 (nat_lit 7928906) (nat_lit 3991495440) (nat_lit 0) D2M8K2.u3389 from rfl, allE_node, arows3388, irow3390, arows3389]
  all_goals rfl

theorem atot3390 : totK PD2M8K2 D2M8K2.u3390 = [0, 390610287592, 1369216825222, 1474810400368, 385427229842, 13250990747, 0, 0] := by
  rw [show D2M8K2.u3390 = KTree.node D2M8K2.u3388 (nat_lit 7928906) (nat_lit 3991495440) (nat_lit 0) D2M8K2.u3389 from rfl, totK_node, atot3388, atot3389]
  decide +kernel

theorem arows3393 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3393 = true := by
  rw [show D2M8K2.u3393 = KTree.node D2M8K2.u3391 (nat_lit 7933126) (nat_lit 3475590767) (nat_lit 0) D2M8K2.u3392 from rfl, allE_node, arows3391, irow3393, arows3392]
  all_goals rfl

theorem atot3393 : totK PD2M8K2 D2M8K2.u3393 = [0, 363324727061, 1425208364374, 1457349378187, 337070997730, 13183098110, 0, 0] := by
  rw [show D2M8K2.u3393 = KTree.node D2M8K2.u3391 (nat_lit 7933126) (nat_lit 3475590767) (nat_lit 0) D2M8K2.u3392 from rfl, totK_node, atot3391, atot3392]
  decide +kernel

theorem arows3397 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3397 = true := by
  rw [show D2M8K2.u3397 = KTree.node D2M8K2.u3395 (nat_lit 7939906) (nat_lit 4097396695) (nat_lit 0) D2M8K2.u3396 from rfl, allE_node, arows3395, irow3397, arows3396]
  all_goals rfl

theorem atot3397 : totK PD2M8K2 D2M8K2.u3397 = [0, 440050482150, 1472825326880, 1379705331986, 309526155381, 8644676715, 0, 0] := by
  rw [show D2M8K2.u3397 = KTree.node D2M8K2.u3395 (nat_lit 7939906) (nat_lit 4097396695) (nat_lit 0) D2M8K2.u3396 from rfl, totK_node, atot3395, atot3396]
  decide +kernel

theorem arows3400 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3400 = true := by
  rw [show D2M8K2.u3400 = KTree.node D2M8K2.u3398 (nat_lit 7963787) (nat_lit 2634223692) (nat_lit 0) D2M8K2.u3399 from rfl, allE_node, arows3398, irow3400, arows3399]
  all_goals rfl

theorem atot3400 : totK PD2M8K2 D2M8K2.u3400 = [421562263945, 1399500228874, 1201283948770, 405734293726, 144521025467, 13338039113, 0, 0] := by
  rw [show D2M8K2.u3400 = KTree.node D2M8K2.u3398 (nat_lit 7963787) (nat_lit 2634223692) (nat_lit 0) D2M8K2.u3399 from rfl, totK_node, atot3398, atot3399]
  decide +kernel

theorem arows3405 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3405 = true := by
  rw [show D2M8K2.u3405 = KTree.node D2M8K2.u3403 (nat_lit 7970882) (nat_lit 3895788378) (nat_lit 0) D2M8K2.u3404 from rfl, allE_node, arows3403, irow3405, arows3404]
  all_goals rfl

theorem atot3405 : totK PD2M8K2 D2M8K2.u3405 = [400005378655, 1441064759551, 1422453850211, 305979557039, 10568566766, 0, 0, 0] := by
  rw [show D2M8K2.u3405 = KTree.node D2M8K2.u3403 (nat_lit 7970882) (nat_lit 3895788378) (nat_lit 0) D2M8K2.u3404 from rfl, totK_node, atot3403, atot3404]
  decide +kernel

theorem arows3408 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3408 = true := by
  rw [show D2M8K2.u3408 = KTree.node D2M8K2.u3406 (nat_lit 7974361) (nat_lit 1409730240) (nat_lit 0) D2M8K2.u3407 from rfl, allE_node, arows3406, irow3408, arows3407]
  all_goals rfl

theorem atot3408 : totK PD2M8K2 D2M8K2.u3408 = [400241123614, 1421924675463, 1405180212978, 338424163188, 13162154230, 0, 0, 0] := by
  rw [show D2M8K2.u3408 = KTree.node D2M8K2.u3406 (nat_lit 7974361) (nat_lit 1409730240) (nat_lit 0) D2M8K2.u3407 from rfl, totK_node, atot3406, atot3407]
  decide +kernel

theorem arows3412 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3412 = true := by
  rw [show D2M8K2.u3412 = KTree.node D2M8K2.u3410 (nat_lit 7977540) (nat_lit 3053779873) (nat_lit 0) D2M8K2.u3411 from rfl, allE_node, arows3410, irow3412, arows3411]
  all_goals rfl

theorem atot3412 : totK PD2M8K2 D2M8K2.u3412 = [422517799814, 1563049711911, 1399572577994, 217974831075, 3666196603, 0, 0, 0] := by
  rw [show D2M8K2.u3412 = KTree.node D2M8K2.u3410 (nat_lit 7977540) (nat_lit 3053779873) (nat_lit 0) D2M8K2.u3411 from rfl, totK_node, atot3410, atot3411]
  decide +kernel

theorem arows3415 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3415 = true := by
  rw [show D2M8K2.u3415 = KTree.node D2M8K2.u3413 (nat_lit 7984756) (nat_lit 3679448601) (nat_lit 0) D2M8K2.u3414 from rfl, allE_node, arows3413, irow3415, arows3414]
  all_goals rfl

theorem atot3415 : totK PD2M8K2 D2M8K2.u3415 = [0, 470942740750, 1623509052193, 1216187486297, 168369543663, 1369150432, 0, 0] := by
  rw [show D2M8K2.u3415 = KTree.node D2M8K2.u3413 (nat_lit 7984756) (nat_lit 3679448601) (nat_lit 0) D2M8K2.u3414 from rfl, totK_node, atot3413, atot3414]
  decide +kernel

theorem arows3421 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3421 = true := by
  rw [show D2M8K2.u3421 = KTree.node D2M8K2.u3419 (nat_lit 7991993) (nat_lit 1509413186) (nat_lit 0) D2M8K2.u3420 from rfl, allE_node, arows3419, irow3421, arows3420]
  all_goals rfl

theorem atot3421 : totK PD2M8K2 D2M8K2.u3421 = [0, 744438322970, 1896138345488, 886664082839, 44351270735, 0, 0, 0] := by
  rw [show D2M8K2.u3421 = KTree.node D2M8K2.u3419 (nat_lit 7991993) (nat_lit 1509413186) (nat_lit 0) D2M8K2.u3420 from rfl, totK_node, atot3419, atot3420]
  decide +kernel

theorem arows3424 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3424 = true := by
  rw [show D2M8K2.u3424 = KTree.node D2M8K2.u3422 (nat_lit 7998363) (nat_lit 3728057158) (nat_lit 0) D2M8K2.u3423 from rfl, allE_node, arows3422, irow3424, arows3423]
  all_goals rfl

theorem atot3424 : totK PD2M8K2 D2M8K2.u3424 = [292455968535, 1143929385237, 1543960978452, 599529117441, 32339439397, 0, 0, 0] := by
  rw [show D2M8K2.u3424 = KTree.node D2M8K2.u3422 (nat_lit 7998363) (nat_lit 3728057158) (nat_lit 0) D2M8K2.u3423 from rfl, totK_node, atot3422, atot3423]
  decide +kernel

theorem arows3428 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3428 = true := by
  rw [show D2M8K2.u3428 = KTree.node D2M8K2.u3426 (nat_lit 8010190) (nat_lit 3917406774) (nat_lit 0) D2M8K2.u3427 from rfl, allE_node, arows3426, irow3428, arows3427]
  all_goals rfl

theorem atot3428 : totK PD2M8K2 D2M8K2.u3428 = [304270041547, 1225995383590, 1510395009015, 588918860783, 37609398105, 0, 0, 0] := by
  rw [show D2M8K2.u3428 = KTree.node D2M8K2.u3426 (nat_lit 8010190) (nat_lit 3917406774) (nat_lit 0) D2M8K2.u3427 from rfl, totK_node, atot3426, atot3427]
  decide +kernel

theorem arows3431 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3431 = true := by
  rw [show D2M8K2.u3431 = KTree.node D2M8K2.u3429 (nat_lit 8013092) (nat_lit 3273355890) (nat_lit 0) D2M8K2.u3430 from rfl, allE_node, arows3429, irow3431, arows3430]
  all_goals rfl

theorem atot3431 : totK PD2M8K2 D2M8K2.u3431 = [414056614216, 1446217691807, 1408444830512, 326604783348, 13036865798, 0, 0, 0] := by
  rw [show D2M8K2.u3431 = KTree.node D2M8K2.u3429 (nat_lit 8013092) (nat_lit 3273355890) (nat_lit 0) D2M8K2.u3430 from rfl, totK_node, atot3429, atot3430]
  decide +kernel

theorem arows3436 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3436 = true := by
  rw [show D2M8K2.u3436 = KTree.node D2M8K2.u3434 (nat_lit 8016514) (nat_lit 4035629607) (nat_lit 0) D2M8K2.u3435 from rfl, allE_node, arows3434, irow3436, arows3435]
  all_goals rfl

theorem atot3436 : totK PD2M8K2 D2M8K2.u3436 = [402868221428, 1426823761484, 1423451933701, 336414817576, 13237669976, 0, 0, 0] := by
  rw [show D2M8K2.u3436 = KTree.node D2M8K2.u3434 (nat_lit 8016514) (nat_lit 4035629607) (nat_lit 0) D2M8K2.u3435 from rfl, totK_node, atot3434, atot3435]
  decide +kernel

theorem arows3439 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3439 = true := by
  rw [show D2M8K2.u3439 = KTree.node D2M8K2.u3437 (nat_lit 8019801) (nat_lit 1724618156) (nat_lit 0) D2M8K2.u3438 from rfl, allE_node, arows3437, irow3439, arows3438]
  all_goals rfl

theorem atot3439 : totK PD2M8K2 D2M8K2.u3439 = [406197326411, 1511029309559, 1470659973505, 266077860681, 4976872846, 0, 0, 0] := by
  rw [show D2M8K2.u3439 = KTree.node D2M8K2.u3437 (nat_lit 8019801) (nat_lit 1724618156) (nat_lit 0) D2M8K2.u3438 from rfl, totK_node, atot3437, atot3438]
  decide +kernel

theorem arows3443 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3443 = true := by
  rw [show D2M8K2.u3443 = KTree.node D2M8K2.u3441 (nat_lit 8023929) (nat_lit 1600947709) (nat_lit 0) D2M8K2.u3442 from rfl, allE_node, arows3441, irow3443, arows3442]
  all_goals rfl

theorem atot3443 : totK PD2M8K2 D2M8K2.u3443 = [218196713264, 1141306569653, 1608714373688, 637743366767, 48863617026, 0, 0, 0] := by
  rw [show D2M8K2.u3443 = KTree.node D2M8K2.u3441 (nat_lit 8023929) (nat_lit 1600947709) (nat_lit 0) D2M8K2.u3442 from rfl, totK_node, atot3441, atot3442]
  decide +kernel

theorem arows3446 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3446 = true := by
  rw [show D2M8K2.u3446 = KTree.node D2M8K2.u3444 (nat_lit 8030603) (nat_lit 2192430091) (nat_lit 0) D2M8K2.u3445 from rfl, allE_node, arows3444, irow3446, arows3445]
  all_goals rfl

theorem atot3446 : totK PD2M8K2 D2M8K2.u3446 = [0, 326882975739, 1230569762503, 1473687392816, 549425474245, 36921873854, 0, 0] := by
  rw [show D2M8K2.u3446 = KTree.node D2M8K2.u3444 (nat_lit 8030603) (nat_lit 2192430091) (nat_lit 0) D2M8K2.u3445 from rfl, totK_node, atot3444, atot3445]
  decide +kernel

theorem arows3454 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3454 = true := by
  rw [show D2M8K2.u3454 = KTree.node D2M8K2.u3452 (nat_lit 8033448) (nat_lit 3174340441) (nat_lit 0) D2M8K2.u3453 from rfl, allE_node, arows3452, irow3454, arows3453]
  all_goals rfl

theorem atot3454 : totK PD2M8K2 D2M8K2.u3454 = [0, 432868531972, 1538951584303, 1390963136923, 244404124890, 5159868635, 0, 0] := by
  rw [show D2M8K2.u3454 = KTree.node D2M8K2.u3452 (nat_lit 8033448) (nat_lit 3174340441) (nat_lit 0) D2M8K2.u3453 from rfl, totK_node, atot3452, atot3453]
  decide +kernel

theorem arows3457 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3457 = true := by
  rw [show D2M8K2.u3457 = KTree.node D2M8K2.u3455 (nat_lit 8037028) (nat_lit 2469626317) (nat_lit 0) D2M8K2.u3456 from rfl, allE_node, arows3455, irow3457, arows3456]
  all_goals rfl

theorem atot3457 : totK PD2M8K2 D2M8K2.u3457 = [0, 464242486708, 1542853883528, 1348860818763, 250273990674, 5218872685, 0, 0] := by
  rw [show D2M8K2.u3457 = KTree.node D2M8K2.u3455 (nat_lit 8037028) (nat_lit 2469626317) (nat_lit 0) D2M8K2.u3456 from rfl, totK_node, atot3455, atot3456]
  decide +kernel

theorem arows3461 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3461 = true := by
  rw [show D2M8K2.u3461 = KTree.node D2M8K2.u3459 (nat_lit 8040704) (nat_lit 3790638557) (nat_lit 0) D2M8K2.u3460 from rfl, allE_node, arows3459, irow3461, arows3460]
  all_goals rfl

theorem atot3461 : totK PD2M8K2 D2M8K2.u3461 = [0, 457122582032, 1597678808144, 1402238616015, 201362797226, 1415142070, 0, 0] := by
  rw [show D2M8K2.u3461 = KTree.node D2M8K2.u3459 (nat_lit 8040704) (nat_lit 3790638557) (nat_lit 0) D2M8K2.u3460 from rfl, totK_node, atot3459, atot3460]
  decide +kernel

theorem arows3464 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3464 = true := by
  rw [show D2M8K2.u3464 = KTree.node D2M8K2.u3462 (nat_lit 8044808) (nat_lit 3673013992) (nat_lit 0) D2M8K2.u3463 from rfl, allE_node, arows3462, irow3464, arows3463]
  all_goals rfl

theorem atot3464 : totK PD2M8K2 D2M8K2.u3464 = [244726993122, 770541890797, 1146526949255, 1122118014493, 296306515719, 9302370699, 0, 0] := by
  rw [show D2M8K2.u3464 = KTree.node D2M8K2.u3462 (nat_lit 8044808) (nat_lit 3673013992) (nat_lit 0) D2M8K2.u3463 from rfl, totK_node, atot3462, atot3463]
  decide +kernel

theorem arows3469 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3469 = true := by
  rw [show D2M8K2.u3469 = KTree.node D2M8K2.u3467 (nat_lit 8048789) (nat_lit 2375234260) (nat_lit 0) D2M8K2.u3468 from rfl, allE_node, arows3467, irow3469, arows3468]
  all_goals rfl

theorem atot3469 : totK PD2M8K2 D2M8K2.u3469 = [481771840902, 1615452692197, 1342262188171, 186762567491, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u3469 = KTree.node D2M8K2.u3467 (nat_lit 8048789) (nat_lit 2375234260) (nat_lit 0) D2M8K2.u3468 from rfl, totK_node, atot3467, atot3468]
  decide +kernel

theorem arows3472 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3472 = true := by
  rw [show D2M8K2.u3472 = KTree.node D2M8K2.u3470 (nat_lit 8051977) (nat_lit 1151390357) (nat_lit 0) D2M8K2.u3471 from rfl, allE_node, arows3470, irow3472, arows3471]
  all_goals rfl

theorem atot3472 : totK PD2M8K2 D2M8K2.u3472 = [337133375768, 1228189845093, 1474339942010, 583688245845, 37564539333, 0, 0, 0] := by
  rw [show D2M8K2.u3472 = KTree.node D2M8K2.u3470 (nat_lit 8051977) (nat_lit 1151390357) (nat_lit 0) D2M8K2.u3471 from rfl, totK_node, atot3470, atot3471]
  decide +kernel

theorem arows3476 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3476 = true := by
  rw [show D2M8K2.u3476 = KTree.node D2M8K2.u3474 (nat_lit 8054889) (nat_lit 1897126751) (nat_lit 0) D2M8K2.u3475 from rfl, allE_node, arows3474, irow3476, arows3475]
  all_goals rfl

theorem atot3476 : totK PD2M8K2 D2M8K2.u3476 = [358994385177, 1400009950730, 1475189077982, 338540802114, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u3476 = KTree.node D2M8K2.u3474 (nat_lit 8054889) (nat_lit 1897126751) (nat_lit 0) D2M8K2.u3475 from rfl, totK_node, atot3474, atot3475]
  decide +kernel

theorem arows3479 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3479 = true := by
  rw [show D2M8K2.u3479 = KTree.node D2M8K2.u3477 (nat_lit 8061701) (nat_lit 2331823436) (nat_lit 0) D2M8K2.u3478 from rfl, allE_node, arows3477, irow3479, arows3478]
  all_goals rfl

theorem atot3479 : totK PD2M8K2 D2M8K2.u3479 = [457072407357, 1541401334916, 1376330286743, 246113818455, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u3479 = KTree.node D2M8K2.u3477 (nat_lit 8061701) (nat_lit 2331823436) (nat_lit 0) D2M8K2.u3478 from rfl, totK_node, atot3477, atot3478]
  decide +kernel

theorem arows3485 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3485 = true := by
  rw [show D2M8K2.u3485 = KTree.node D2M8K2.u3483 (nat_lit 8066089) (nat_lit 1258498723) (nat_lit 0) D2M8K2.u3484 from rfl, allE_node, arows3483, irow3485, arows3484]
  all_goals rfl

theorem atot3485 : totK PD2M8K2 D2M8K2.u3485 = [103540504535, 990940293070, 1765959807182, 656706673895, 33014615298, 0, 0, 0] := by
  rw [show D2M8K2.u3485 = KTree.node D2M8K2.u3483 (nat_lit 8066089) (nat_lit 1258498723) (nat_lit 0) D2M8K2.u3484 from rfl, totK_node, atot3483, atot3484]
  decide +kernel

theorem arows3488 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3488 = true := by
  rw [show D2M8K2.u3488 = KTree.node D2M8K2.u3486 (nat_lit 8070262) (nat_lit 3552898783) (nat_lit 0) D2M8K2.u3487 from rfl, allE_node, arows3486, irow3488, arows3487]
  all_goals rfl

theorem atot3488 : totK PD2M8K2 D2M8K2.u3488 = [0, 513550549858, 1657261645581, 1273808980401, 152821882611, 1206465782, 0, 0] := by
  rw [show D2M8K2.u3488 = KTree.node D2M8K2.u3486 (nat_lit 8070262) (nat_lit 3552898783) (nat_lit 0) D2M8K2.u3487 from rfl, totK_node, atot3486, atot3487]
  decide +kernel

theorem arows3492 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3492 = true := by
  rw [show D2M8K2.u3492 = KTree.node D2M8K2.u3490 (nat_lit 8074750) (nat_lit 3765630645) (nat_lit 0) D2M8K2.u3491 from rfl, allE_node, arows3490, irow3492, arows3491]
  all_goals rfl

theorem atot3492 : totK PD2M8K2 D2M8K2.u3492 = [0, 398679700673, 1457463786927, 1353040730385, 303282475163, 13016197374, 0, 0] := by
  rw [show D2M8K2.u3492 = KTree.node D2M8K2.u3490 (nat_lit 8074750) (nat_lit 3765630645) (nat_lit 0) D2M8K2.u3491 from rfl, totK_node, atot3490, atot3491]
  decide +kernel

theorem arows3495 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3495 = true := by
  rw [show D2M8K2.u3495 = KTree.node D2M8K2.u3493 (nat_lit 8081341) (nat_lit 1212205351) (nat_lit 0) D2M8K2.u3494 from rfl, allE_node, arows3493, irow3495, arows3494]
  all_goals rfl

theorem atot3495 : totK PD2M8K2 D2M8K2.u3495 = [0, 486471187021, 1604012499316, 1228470382165, 180771754154, 4574395652, 0, 0] := by
  rw [show D2M8K2.u3495 = KTree.node D2M8K2.u3493 (nat_lit 8081341) (nat_lit 1212205351) (nat_lit 0) D2M8K2.u3494 from rfl, totK_node, atot3493, atot3494]
  decide +kernel

theorem arows3500 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3500 = true := by
  rw [show D2M8K2.u3500 = KTree.node D2M8K2.u3498 (nat_lit 8087267) (nat_lit 2357175640) (nat_lit 0) D2M8K2.u3499 from rfl, allE_node, arows3498, irow3500, arows3499]
  all_goals rfl

theorem atot3500 : totK PD2M8K2 D2M8K2.u3500 = [377263167847, 1310164228791, 1366168352189, 506042375978, 40252704969, 0, 0, 0] := by
  rw [show D2M8K2.u3500 = KTree.node D2M8K2.u3498 (nat_lit 8087267) (nat_lit 2357175640) (nat_lit 0) D2M8K2.u3499 from rfl, totK_node, atot3498, atot3499]
  decide +kernel

theorem arows3503 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3503 = true := by
  rw [show D2M8K2.u3503 = KTree.node D2M8K2.u3501 (nat_lit 8091389) (nat_lit 1806790331) (nat_lit 0) D2M8K2.u3502 from rfl, allE_node, arows3501, irow3503, arows3502]
  all_goals rfl

theorem atot3503 : totK PD2M8K2 D2M8K2.u3503 = [420081044414, 1497233165251, 1400492544198, 329857691818, 22752297776, 0, 0, 0] := by
  rw [show D2M8K2.u3503 = KTree.node D2M8K2.u3501 (nat_lit 8091389) (nat_lit 1806790331) (nat_lit 0) D2M8K2.u3502 from rfl, totK_node, atot3501, atot3502]
  decide +kernel

theorem arows3507 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3507 = true := by
  rw [show D2M8K2.u3507 = KTree.node D2M8K2.u3505 (nat_lit 8097650) (nat_lit 3143317647) (nat_lit 0) D2M8K2.u3506 from rfl, allE_node, arows3505, irow3507, arows3506]
  all_goals rfl

theorem atot3507 : totK PD2M8K2 D2M8K2.u3507 = [437903714595, 1410742041811, 1365951323343, 413332401016, 16179348042, 0, 0, 0] := by
  rw [show D2M8K2.u3507 = KTree.node D2M8K2.u3505 (nat_lit 8097650) (nat_lit 3143317647) (nat_lit 0) D2M8K2.u3506 from rfl, totK_node, atot3505, atot3506]
  decide +kernel

theorem arows3510 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3510 = true := by
  rw [show D2M8K2.u3510 = KTree.node D2M8K2.u3508 (nat_lit 8100925) (nat_lit 1222343378) (nat_lit 0) D2M8K2.u3509 from rfl, allE_node, arows3508, irow3510, arows3509]
  all_goals rfl

theorem atot3510 : totK PD2M8K2 D2M8K2.u3510 = [402723543342, 1393647893357, 1427856062257, 349856117016, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u3510 = KTree.node D2M8K2.u3508 (nat_lit 8100925) (nat_lit 1222343378) (nat_lit 0) D2M8K2.u3509 from rfl, totK_node, atot3508, atot3509]
  decide +kernel

theorem arows3517 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3517 = true := by
  rw [show D2M8K2.u3517 = KTree.node D2M8K2.u3515 (nat_lit 8104437) (nat_lit 1709915121) (nat_lit 0) D2M8K2.u3516 from rfl, allE_node, arows3515, irow3517, arows3516]
  all_goals rfl

theorem atot3517 : totK PD2M8K2 D2M8K2.u3517 = [349342976169, 1456475121965, 1517082908833, 294945748772, 6249254262, 0, 0, 0] := by
  rw [show D2M8K2.u3517 = KTree.node D2M8K2.u3515 (nat_lit 8104437) (nat_lit 1709915121) (nat_lit 0) D2M8K2.u3516 from rfl, totK_node, atot3515, atot3516]
  decide +kernel

theorem arows3520 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3520 = true := by
  rw [show D2M8K2.u3520 = KTree.node D2M8K2.u3518 (nat_lit 8108649) (nat_lit 1821247968) (nat_lit 0) D2M8K2.u3519 from rfl, allE_node, arows3518, irow3520, arows3519]
  all_goals rfl

theorem atot3520 : totK PD2M8K2 D2M8K2.u3520 = [0, 637476464948, 1742807368814, 1037829942371, 108456626678, 1239866073, 0, 0] := by
  rw [show D2M8K2.u3520 = KTree.node D2M8K2.u3518 (nat_lit 8108649) (nat_lit 1821247968) (nat_lit 0) D2M8K2.u3519 from rfl, totK_node, atot3518, atot3519]
  decide +kernel

theorem arows3524 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3524 = true := by
  rw [show D2M8K2.u3524 = KTree.node D2M8K2.u3522 (nat_lit 8112404) (nat_lit 3265361729) (nat_lit 0) D2M8K2.u3523 from rfl, allE_node, arows3522, irow3524, arows3523]
  all_goals rfl

theorem atot3524 : totK PD2M8K2 D2M8K2.u3524 = [0, 647477476065, 1787937659903, 1110415604048, 100420280488, 0, 0, 0] := by
  rw [show D2M8K2.u3524 = KTree.node D2M8K2.u3522 (nat_lit 8112404) (nat_lit 3265361729) (nat_lit 0) D2M8K2.u3523 from rfl, totK_node, atot3522, atot3523]
  decide +kernel

theorem arows3527 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3527 = true := by
  rw [show D2M8K2.u3527 = KTree.node D2M8K2.u3525 (nat_lit 8120775) (nat_lit 2943953624) (nat_lit 0) D2M8K2.u3526 from rfl, allE_node, arows3525, irow3527, arows3526]
  all_goals rfl

theorem atot3527 : totK PD2M8K2 D2M8K2.u3527 = [0, 380624457101, 1444224566148, 1385165788825, 308367220850, 13105450397, 0, 0] := by
  rw [show D2M8K2.u3527 = KTree.node D2M8K2.u3525 (nat_lit 8120775) (nat_lit 2943953624) (nat_lit 0) D2M8K2.u3526 from rfl, totK_node, atot3525, atot3526]
  decide +kernel

theorem arows3532 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3532 = true := by
  rw [show D2M8K2.u3532 = KTree.node D2M8K2.u3530 (nat_lit 8123952) (nat_lit 3287817672) (nat_lit 0) D2M8K2.u3531 from rfl, allE_node, arows3530, irow3532, arows3531]
  all_goals rfl

theorem atot3532 : totK PD2M8K2 D2M8K2.u3532 = [0, 483898617963, 1585657674783, 1272733567911, 193874545073, 4720618446, 0, 0] := by
  rw [show D2M8K2.u3532 = KTree.node D2M8K2.u3530 (nat_lit 8123952) (nat_lit 3287817672) (nat_lit 0) D2M8K2.u3531 from rfl, totK_node, atot3530, atot3531]
  decide +kernel

theorem arows3535 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3535 = true := by
  rw [show D2M8K2.u3535 = KTree.node D2M8K2.u3533 (nat_lit 8129619) (nat_lit 2466642975) (nat_lit 0) D2M8K2.u3534 from rfl, allE_node, arows3533, irow3535, arows3534]
  all_goals rfl

theorem atot3535 : totK PD2M8K2 D2M8K2.u3535 = [396411393819, 1421079440568, 1362857313113, 354520961287, 22159822739, 0, 0, 0] := by
  rw [show D2M8K2.u3535 = KTree.node D2M8K2.u3533 (nat_lit 8129619) (nat_lit 2466642975) (nat_lit 0) D2M8K2.u3534 from rfl, totK_node, atot3533, atot3534]
  decide +kernel

theorem arows3539 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3539 = true := by
  rw [show D2M8K2.u3539 = KTree.node D2M8K2.u3537 (nat_lit 8133237) (nat_lit 1740482660) (nat_lit 0) D2M8K2.u3538 from rfl, allE_node, arows3537, irow3539, arows3538]
  all_goals rfl

theorem atot3539 : totK PD2M8K2 D2M8K2.u3539 = [426329793101, 1432544438112, 1373406880123, 395935355427, 28232996955, 0, 0, 0] := by
  rw [show D2M8K2.u3539 = KTree.node D2M8K2.u3537 (nat_lit 8133237) (nat_lit 1740482660) (nat_lit 0) D2M8K2.u3538 from rfl, totK_node, atot3537, atot3538]
  decide +kernel

theorem arows3542 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3542 = true := by
  rw [show D2M8K2.u3542 = KTree.node D2M8K2.u3540 (nat_lit 8136053) (nat_lit 2404007425) (nat_lit 0) D2M8K2.u3541 from rfl, allE_node, arows3540, irow3542, arows3541]
  all_goals rfl

theorem atot3542 : totK PD2M8K2 D2M8K2.u3542 = [417531768947, 1432579147416, 1379875611262, 355386418309, 10490718455, 0, 0, 0] := by
  rw [show D2M8K2.u3542 = KTree.node D2M8K2.u3540 (nat_lit 8136053) (nat_lit 2404007425) (nat_lit 0) D2M8K2.u3541 from rfl, totK_node, atot3540, atot3541]
  decide +kernel

theorem arows3548 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3548 = true := by
  rw [show D2M8K2.u3548 = KTree.node D2M8K2.u3546 (nat_lit 8139450) (nat_lit 3559537141) (nat_lit 0) D2M8K2.u3547 from rfl, allE_node, arows3546, irow3548, arows3547]
  all_goals rfl

theorem atot3548 : totK PD2M8K2 D2M8K2.u3548 = [417740517569, 1433325181230, 1380830202665, 323965787239, 13083481006, 0, 0, 0] := by
  rw [show D2M8K2.u3548 = KTree.node D2M8K2.u3546 (nat_lit 8139450) (nat_lit 3559537141) (nat_lit 0) D2M8K2.u3547 from rfl, totK_node, atot3546, atot3547]
  decide +kernel

theorem arows3551 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3551 = true := by
  rw [show D2M8K2.u3551 = KTree.node D2M8K2.u3549 (nat_lit 8142828) (nat_lit 1801041407) (nat_lit 0) D2M8K2.u3550 from rfl, allE_node, arows3549, irow3551, arows3550]
  all_goals rfl

theorem atot3551 : totK PD2M8K2 D2M8K2.u3551 = [444279370890, 1474885112199, 1357701504325, 315256717117, 13149116973, 0, 0, 0] := by
  rw [show D2M8K2.u3551 = KTree.node D2M8K2.u3549 (nat_lit 8142828) (nat_lit 1801041407) (nat_lit 0) D2M8K2.u3550 from rfl, totK_node, atot3549, atot3550]
  decide +kernel

theorem arows3555 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3555 = true := by
  rw [show D2M8K2.u3555 = KTree.node D2M8K2.u3553 (nat_lit 8149981) (nat_lit 1152564544) (nat_lit 0) D2M8K2.u3554 from rfl, allE_node, arows3553, irow3555, arows3554]
  all_goals rfl

theorem atot3555 : totK PD2M8K2 D2M8K2.u3555 = [0, 749034593728, 1807771220302, 876019184043, 89712464940, 1138244013, 0, 0] := by
  rw [show D2M8K2.u3555 = KTree.node D2M8K2.u3553 (nat_lit 8149981) (nat_lit 1152564544) (nat_lit 0) D2M8K2.u3554 from rfl, totK_node, atot3553, atot3554]
  decide +kernel

theorem arows3558 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3558 = true := by
  rw [show D2M8K2.u3558 = KTree.node D2M8K2.u3556 (nat_lit 8153812) (nat_lit 2731860456) (nat_lit 0) D2M8K2.u3557 from rfl, allE_node, arows3556, irow3558, arows3557]
  all_goals rfl

theorem atot3558 : totK PD2M8K2 D2M8K2.u3558 = [0, 654558070265, 1825804918259, 1053758203707, 82649348599, 0, 0, 0] := by
  rw [show D2M8K2.u3558 = KTree.node D2M8K2.u3556 (nat_lit 8153812) (nat_lit 2731860456) (nat_lit 0) D2M8K2.u3557 from rfl, totK_node, atot3556, atot3557]
  decide +kernel

theorem arows3563 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3563 = true := by
  rw [show D2M8K2.u3563 = KTree.node D2M8K2.u3561 (nat_lit 8160145) (nat_lit 1126017602) (nat_lit 0) D2M8K2.u3562 from rfl, allE_node, arows3561, irow3563, arows3562]
  all_goals rfl

theorem atot3563 : totK PD2M8K2 D2M8K2.u3563 = [0, 743255938080, 1892617987592, 890273697355, 44722004211, 0, 0, 0] := by
  rw [show D2M8K2.u3563 = KTree.node D2M8K2.u3561 (nat_lit 8160145) (nat_lit 1126017602) (nat_lit 0) D2M8K2.u3562 from rfl, totK_node, atot3561, atot3562]
  decide +kernel

theorem arows3566 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3566 = true := by
  rw [show D2M8K2.u3566 = KTree.node D2M8K2.u3564 (nat_lit 8164916) (nat_lit 3663048984) (nat_lit 0) D2M8K2.u3565 from rfl, allE_node, arows3564, irow3566, arows3565]
  all_goals rfl

theorem atot3566 : totK PD2M8K2 D2M8K2.u3566 = [0, 456970629900, 1573133671915, 1295155849143, 224840266308, 4977114383, 0, 0] := by
  rw [show D2M8K2.u3566 = KTree.node D2M8K2.u3564 (nat_lit 8164916) (nat_lit 3663048984) (nat_lit 0) D2M8K2.u3565 from rfl, totK_node, atot3564, atot3565]
  decide +kernel

theorem arows3570 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3570 = true := by
  rw [show D2M8K2.u3570 = KTree.node D2M8K2.u3568 (nat_lit 8213377) (nat_lit 1489951043) (nat_lit 0) D2M8K2.u3569 from rfl, allE_node, arows3568, irow3570, arows3569]
  all_goals rfl

theorem atot3570 : totK PD2M8K2 D2M8K2.u3570 = [0, 441468779906, 1594829270875, 1352854850330, 184904524324, 1369150432, 0, 0] := by
  rw [show D2M8K2.u3570 = KTree.node D2M8K2.u3568 (nat_lit 8213377) (nat_lit 1489951043) (nat_lit 0) D2M8K2.u3569 from rfl, totK_node, atot3568, atot3569]
  decide +kernel

theorem arows3573 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3573 = true := by
  rw [show D2M8K2.u3573 = KTree.node D2M8K2.u3571 (nat_lit 8220713) (nat_lit 1788837400) (nat_lit 0) D2M8K2.u3572 from rfl, allE_node, arows3571, irow3573, arows3572]
  all_goals rfl

theorem atot3573 : totK PD2M8K2 D2M8K2.u3573 = [0, 418049847105, 1444620663833, 1385174084206, 293547583580, 12983449796, 0, 0] := by
  rw [show D2M8K2.u3573 = KTree.node D2M8K2.u3571 (nat_lit 8220713) (nat_lit 1788837400) (nat_lit 0) D2M8K2.u3572 from rfl, totK_node, atot3571, atot3572]
  decide +kernel

theorem arows3583 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3583 = true := by
  rw [show D2M8K2.u3583 = KTree.node D2M8K2.u3581 (nat_lit 8224510) (nat_lit 3804760116) (nat_lit 0) D2M8K2.u3582 from rfl, allE_node, arows3581, irow3583, arows3582]
  all_goals rfl

theorem atot3583 : totK PD2M8K2 D2M8K2.u3583 = [0, 405744118116, 1441161614588, 1395778204301, 303783051180, 13184317400, 0, 0] := by
  rw [show D2M8K2.u3583 = KTree.node D2M8K2.u3581 (nat_lit 8224510) (nat_lit 3804760116) (nat_lit 0) D2M8K2.u3582 from rfl, totK_node, atot3581, atot3582]
  decide +kernel

theorem arows3586 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3586 = true := by
  rw [show D2M8K2.u3586 = KTree.node D2M8K2.u3584 (nat_lit 8227634) (nat_lit 3958308645) (nat_lit 0) D2M8K2.u3585 from rfl, allE_node, arows3584, irow3586, arows3585]
  all_goals rfl

theorem atot3586 : totK PD2M8K2 D2M8K2.u3586 = [0, 208161238117, 1256040320379, 1661560286412, 407790675097, 14533263366, 0, 0] := by
  rw [show D2M8K2.u3586 = KTree.node D2M8K2.u3584 (nat_lit 8227634) (nat_lit 3958308645) (nat_lit 0) D2M8K2.u3585 from rfl, totK_node, atot3584, atot3585]
  decide +kernel

theorem arows3590 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3590 = true := by
  rw [show D2M8K2.u3590 = KTree.node D2M8K2.u3588 (nat_lit 8235145) (nat_lit 1481302006) (nat_lit 0) D2M8K2.u3589 from rfl, allE_node, arows3588, irow3590, arows3589]
  all_goals rfl

theorem atot3590 : totK PD2M8K2 D2M8K2.u3590 = [0, 0, 548436910651, 1733125722142, 1048098722315, 113517277336, 1209030869, 0] := by
  rw [show D2M8K2.u3590 = KTree.node D2M8K2.u3588 (nat_lit 8235145) (nat_lit 1481302006) (nat_lit 0) D2M8K2.u3589 from rfl, totK_node, atot3588, atot3589]
  decide +kernel

theorem arows3593 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3593 = true := by
  rw [show D2M8K2.u3593 = KTree.node D2M8K2.u3591 (nat_lit 8246117) (nat_lit 2302951550) (nat_lit 0) D2M8K2.u3592 from rfl, allE_node, arows3591, irow3593, arows3592]
  all_goals rfl

theorem atot3593 : totK PD2M8K2 D2M8K2.u3593 = [0, 0, 816636405512, 1934727531486, 735313651777, 35215870600, 0, 0] := by
  rw [show D2M8K2.u3593 = KTree.node D2M8K2.u3591 (nat_lit 8246117) (nat_lit 2302951550) (nat_lit 0) D2M8K2.u3592 from rfl, totK_node, atot3591, atot3592]
  decide +kernel

theorem arows3598 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3598 = true := by
  rw [show D2M8K2.u3598 = KTree.node D2M8K2.u3596 (nat_lit 8257835) (nat_lit 2873626545) (nat_lit 0) D2M8K2.u3597 from rfl, allE_node, arows3596, irow3598, arows3597]
  all_goals rfl

theorem atot3598 : totK PD2M8K2 D2M8K2.u3598 = [0, 444383804327, 1440450923860, 1348928247652, 418262441716, 31121113322, 0, 0] := by
  rw [show D2M8K2.u3598 = KTree.node D2M8K2.u3596 (nat_lit 8257835) (nat_lit 2873626545) (nat_lit 0) D2M8K2.u3597 from rfl, totK_node, atot3596, atot3597]
  decide +kernel

theorem arows3601 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3601 = true := by
  rw [show D2M8K2.u3601 = KTree.node D2M8K2.u3599 (nat_lit 8260567) (nat_lit 895491266) (nat_lit 0) D2M8K2.u3600 from rfl, allE_node, arows3599, irow3601, arows3600]
  all_goals rfl

theorem atot3601 : totK PD2M8K2 D2M8K2.u3601 = [0, 413609247844, 1448352900876, 1411169995305, 349323220221, 14102813400, 0, 0] := by
  rw [show D2M8K2.u3601 = KTree.node D2M8K2.u3599 (nat_lit 8260567) (nat_lit 895491266) (nat_lit 0) D2M8K2.u3600 from rfl, totK_node, atot3599, atot3600]
  decide +kernel

theorem arows3605 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3605 = true := by
  rw [show D2M8K2.u3605 = KTree.node D2M8K2.u3603 (nat_lit 8264379) (nat_lit 3450190703) (nat_lit 0) D2M8K2.u3604 from rfl, allE_node, arows3603, irow3605, arows3604]
  all_goals rfl

theorem atot3605 : totK PD2M8K2 D2M8K2.u3605 = [0, 413852330708, 1476345660540, 1404146517757, 309760567439, 14338666808, 0, 0] := by
  rw [show D2M8K2.u3605 = KTree.node D2M8K2.u3603 (nat_lit 8264379) (nat_lit 3450190703) (nat_lit 0) D2M8K2.u3604 from rfl, totK_node, atot3603, atot3604]
  decide +kernel

theorem arows3608 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3608 = true := by
  rw [show D2M8K2.u3608 = KTree.node D2M8K2.u3606 (nat_lit 8267570) (nat_lit 3949341186) (nat_lit 0) D2M8K2.u3607 from rfl, allE_node, arows3606, irow3608, arows3607]
  all_goals rfl

theorem atot3608 : totK PD2M8K2 D2M8K2.u3608 = [0, 423269314517, 1577664646714, 1411958850408, 213966146762, 3575904516, 0, 0] := by
  rw [show D2M8K2.u3608 = KTree.node D2M8K2.u3606 (nat_lit 8267570) (nat_lit 3949341186) (nat_lit 0) D2M8K2.u3607 from rfl, totK_node, atot3606, atot3607]
  decide +kernel

theorem arows3614 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3614 = true := by
  rw [show D2M8K2.u3614 = KTree.node D2M8K2.u3612 (nat_lit 8271686) (nat_lit 4138176871) (nat_lit 0) D2M8K2.u3613 from rfl, allE_node, arows3612, irow3614, arows3613]
  all_goals rfl

theorem atot3614 : totK PD2M8K2 D2M8K2.u3614 = [0, 351417302989, 1332434346602, 1547213990304, 410924010839, 13611258702, 0, 0] := by
  rw [show D2M8K2.u3614 = KTree.node D2M8K2.u3612 (nat_lit 8271686) (nat_lit 4138176871) (nat_lit 0) D2M8K2.u3613 from rfl, totK_node, atot3612, atot3613]
  decide +kernel

theorem arows3617 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3617 = true := by
  rw [show D2M8K2.u3617 = KTree.node D2M8K2.u3615 (nat_lit 8296044) (nat_lit 2904772313) (nat_lit 0) D2M8K2.u3616 from rfl, allE_node, arows3615, irow3617, arows3616]
  all_goals rfl

theorem atot3617 : totK PD2M8K2 D2M8K2.u3617 = [0, 499546867499, 1603218104655, 1303843012525, 172076292908, 1310166938, 0, 0] := by
  rw [show D2M8K2.u3617 = KTree.node D2M8K2.u3615 (nat_lit 8296044) (nat_lit 2904772313) (nat_lit 0) D2M8K2.u3616 from rfl, totK_node, atot3615, atot3616]
  decide +kernel

theorem arows3621 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3621 = true := by
  rw [show D2M8K2.u3621 = KTree.node D2M8K2.u3619 (nat_lit 8300046) (nat_lit 3774547761) (nat_lit 0) D2M8K2.u3620 from rfl, allE_node, arows3619, irow3621, arows3620]
  all_goals rfl

theorem atot3621 : totK PD2M8K2 D2M8K2.u3621 = [0, 392551429267, 1444288657604, 1429375109853, 375279231959, 15013989272, 0, 0] := by
  rw [show D2M8K2.u3621 = KTree.node D2M8K2.u3619 (nat_lit 8300046) (nat_lit 3774547761) (nat_lit 0) D2M8K2.u3620 from rfl, totK_node, atot3619, atot3620]
  decide +kernel

theorem arows3624 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3624 = true := by
  rw [show D2M8K2.u3624 = KTree.node D2M8K2.u3622 (nat_lit 8303062) (nat_lit 3342698556) (nat_lit 0) D2M8K2.u3623 from rfl, allE_node, arows3622, irow3624, arows3623]
  all_goals rfl

theorem atot3624 : totK PD2M8K2 D2M8K2.u3624 = [0, 403733088378, 1422808523601, 1441092859806, 328997916926, 13049727234, 0, 0] := by
  rw [show D2M8K2.u3624 = KTree.node D2M8K2.u3622 (nat_lit 8303062) (nat_lit 3342698556) (nat_lit 0) D2M8K2.u3623 from rfl, totK_node, atot3622, atot3623]
  decide +kernel

theorem arows3629 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3629 = true := by
  rw [show D2M8K2.u3629 = KTree.node D2M8K2.u3627 (nat_lit 8309550) (nat_lit 3750748818) (nat_lit 0) D2M8K2.u3628 from rfl, allE_node, arows3627, irow3629, arows3628]
  all_goals rfl

theorem atot3629 : totK PD2M8K2 D2M8K2.u3629 = [0, 418102898842, 1521538350406, 1394774113110, 243503179234, 4980514959, 0, 0] := by
  rw [show D2M8K2.u3629 = KTree.node D2M8K2.u3627 (nat_lit 8309550) (nat_lit 3750748818) (nat_lit 0) D2M8K2.u3628 from rfl, totK_node, atot3627, atot3628]
  decide +kernel

theorem arows3632 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3632 = true := by
  rw [show D2M8K2.u3632 = KTree.node D2M8K2.u3630 (nat_lit 8313756) (nat_lit 2607662804) (nat_lit 0) D2M8K2.u3631 from rfl, allE_node, arows3630, irow3632, arows3631]
  all_goals rfl

theorem atot3632 : totK PD2M8K2 D2M8K2.u3632 = [0, 489384159788, 1574009085215, 1315789133194, 232376211999, 4880895167, 0, 0] := by
  rw [show D2M8K2.u3632 = KTree.node D2M8K2.u3630 (nat_lit 8313756) (nat_lit 2607662804) (nat_lit 0) D2M8K2.u3631 from rfl, totK_node, atot3630, atot3631]
  decide +kernel

theorem arows3636 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3636 = true := by
  rw [show D2M8K2.u3636 = KTree.node D2M8K2.u3634 (nat_lit 8338846) (nat_lit 2645117378) (nat_lit 0) D2M8K2.u3635 from rfl, allE_node, arows3634, irow3636, arows3635]
  all_goals rfl

theorem atot3636 : totK PD2M8K2 D2M8K2.u3636 = [0, 488646070210, 1617277347339, 1344162990007, 175783705590, 1310517177, 0, 0] := by
  rw [show D2M8K2.u3636 = KTree.node D2M8K2.u3634 (nat_lit 8338846) (nat_lit 2645117378) (nat_lit 0) D2M8K2.u3635 from rfl, totK_node, atot3634, atot3635]
  decide +kernel

theorem arows3639 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3639 = true := by
  rw [show D2M8K2.u3639 = KTree.node D2M8K2.u3637 (nat_lit 8342324) (nat_lit 3703361260) (nat_lit 0) D2M8K2.u3638 from rfl, allE_node, arows3637, irow3639, arows3638]
  all_goals rfl

theorem atot3639 : totK PD2M8K2 D2M8K2.u3639 = [0, 383590384560, 1416160117153, 1464228559825, 392785385729, 15066332673, 0, 0] := by
  rw [show D2M8K2.u3639 = KTree.node D2M8K2.u3637 (nat_lit 8342324) (nat_lit 3703361260) (nat_lit 0) D2M8K2.u3638 from rfl, totK_node, atot3637, atot3638]
  decide +kernel

theorem arows3646 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3646 = true := by
  rw [show D2M8K2.u3646 = KTree.node D2M8K2.u3644 (nat_lit 8349103) (nat_lit 2012945262) (nat_lit 0) D2M8K2.u3645 from rfl, allE_node, arows3644, irow3646, arows3645]
  all_goals rfl

theorem atot3646 : totK PD2M8K2 D2M8K2.u3646 = [0, 375721817105, 1412391762939, 1437404783462, 334487292838, 13170675918, 0, 0] := by
  rw [show D2M8K2.u3646 = KTree.node D2M8K2.u3644 (nat_lit 8349103) (nat_lit 2012945262) (nat_lit 0) D2M8K2.u3645 from rfl, totK_node, atot3644, atot3645]
  decide +kernel

theorem arows3649 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3649 = true := by
  rw [show D2M8K2.u3649 = KTree.node D2M8K2.u3647 (nat_lit 8352328) (nat_lit 2883051692) (nat_lit 0) D2M8K2.u3648 from rfl, allE_node, arows3647, irow3649, arows3648]
  all_goals rfl

theorem atot3649 : totK PD2M8K2 D2M8K2.u3649 = [0, 434693009048, 1521349297835, 1410414195482, 247978492990, 4980514959, 0, 0] := by
  rw [show D2M8K2.u3649 = KTree.node D2M8K2.u3647 (nat_lit 8352328) (nat_lit 2883051692) (nat_lit 0) D2M8K2.u3648 from rfl, totK_node, atot3647, atot3648]
  decide +kernel

theorem arows3653 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3653 = true := by
  rw [show D2M8K2.u3653 = KTree.node D2M8K2.u3651 (nat_lit 8377461) (nat_lit 1737201167) (nat_lit 0) D2M8K2.u3652 from rfl, allE_node, arows3651, irow3653, arows3652]
  all_goals rfl

theorem atot3653 : totK PD2M8K2 D2M8K2.u3653 = [0, 466387607515, 1566595258417, 1293083329321, 226374272636, 4934554315, 0, 0] := by
  rw [show D2M8K2.u3653 = KTree.node D2M8K2.u3651 (nat_lit 8377461) (nat_lit 1737201167) (nat_lit 0) D2M8K2.u3652 from rfl, totK_node, atot3651, atot3652]
  decide +kernel

theorem arows3656 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3656 = true := by
  rw [show D2M8K2.u3656 = KTree.node D2M8K2.u3654 (nat_lit 8381428) (nat_lit 4069852912) (nat_lit 0) D2M8K2.u3655 from rfl, allE_node, arows3654, irow3656, arows3655]
  all_goals rfl

theorem atot3656 : totK PD2M8K2 D2M8K2.u3656 = [0, 424982773380, 1556670272902, 1437445906799, 202008210801, 1326647619, 0, 0] := by
  rw [show D2M8K2.u3656 = KTree.node D2M8K2.u3654 (nat_lit 8381428) (nat_lit 4069852912) (nat_lit 0) D2M8K2.u3655 from rfl, totK_node, atot3654, atot3655]
  decide +kernel

theorem arows3661 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3661 = true := by
  rw [show D2M8K2.u3661 = KTree.node D2M8K2.u3659 (nat_lit 8384392) (nat_lit 3735308340) (nat_lit 0) D2M8K2.u3660 from rfl, allE_node, arows3659, irow3661, arows3660]
  all_goals rfl

theorem atot3661 : totK PD2M8K2 D2M8K2.u3661 = [0, 416614945303, 1381820125092, 1358616898055, 416849343459, 23711123474, 0, 0] := by
  rw [show D2M8K2.u3661 = KTree.node D2M8K2.u3659 (nat_lit 8384392) (nat_lit 3735308340) (nat_lit 0) D2M8K2.u3660 from rfl, totK_node, atot3659, atot3660]
  decide +kernel

theorem arows3664 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3664 = true := by
  rw [show D2M8K2.u3664 = KTree.node D2M8K2.u3662 (nat_lit 8387805) (nat_lit 1565350020) (nat_lit 0) D2M8K2.u3663 from rfl, allE_node, arows3662, irow3664, arows3663]
  all_goals rfl

theorem atot3664 : totK PD2M8K2 D2M8K2.u3664 = [0, 416827096798, 1433746811207, 1393579737022, 301676321402, 12909266092, 0, 0] := by
  rw [show D2M8K2.u3664 = KTree.node D2M8K2.u3662 (nat_lit 8387805) (nat_lit 1565350020) (nat_lit 0) D2M8K2.u3663 from rfl, totK_node, atot3662, atot3663]
  decide +kernel

theorem arows3668 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3668 = true := by
  rw [show D2M8K2.u3668 = KTree.node D2M8K2.u3666 (nat_lit 8391181) (nat_lit 1391289156) (nat_lit 0) D2M8K2.u3667 from rfl, allE_node, arows3666, irow3668, arows3667]
  all_goals rfl

theorem atot3668 : totK PD2M8K2 D2M8K2.u3668 = [0, 387472347685, 1419658609314, 1445132115576, 316356688116, 13110073960, 0, 0] := by
  rw [show D2M8K2.u3668 = KTree.node D2M8K2.u3666 (nat_lit 8391181) (nat_lit 1391289156) (nat_lit 0) D2M8K2.u3667 from rfl, totK_node, atot3666, atot3667]
  decide +kernel

theorem arows3671 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3671 = true := by
  rw [show D2M8K2.u3671 = KTree.node D2M8K2.u3669 (nat_lit 8394302) (nat_lit 2914223260) (nat_lit 0) D2M8K2.u3670 from rfl, allE_node, arows3669, irow3671, arows3670]
  all_goals rfl

theorem atot3671 : totK PD2M8K2 D2M8K2.u3671 = [0, 56111990362, 1012524431566, 1864739119576, 575665922979, 26931128583, 0, 0] := by
  rw [show D2M8K2.u3671 = KTree.node D2M8K2.u3669 (nat_lit 8394302) (nat_lit 2914223260) (nat_lit 0) D2M8K2.u3670 from rfl, totK_node, atot3669, atot3670]
  decide +kernel

theorem arows3677 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3677 = true := by
  rw [show D2M8K2.u3677 = KTree.node D2M8K2.u3675 (nat_lit 8402221) (nat_lit 1088367964) (nat_lit 0) D2M8K2.u3676 from rfl, allE_node, arows3675, irow3677, arows3676]
  all_goals rfl

theorem atot3677 : totK PD2M8K2 D2M8K2.u3677 = [0, 0, 586325690435, 1729930001519, 1051368789450, 116236356277, 1138244013, 0] := by
  rw [show D2M8K2.u3677 = KTree.node D2M8K2.u3675 (nat_lit 8402221) (nat_lit 1088367964) (nat_lit 0) D2M8K2.u3676 from rfl, totK_node, atot3675, atot3676]
  decide +kernel

theorem arows3680 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3680 = true := by
  rw [show D2M8K2.u3680 = KTree.node D2M8K2.u3678 (nat_lit 8408860) (nat_lit 2169335445) (nat_lit 0) D2M8K2.u3679 from rfl, allE_node, arows3678, irow3680, arows3679]
  all_goals rfl

theorem atot3680 : totK PD2M8K2 D2M8K2.u3680 = [0, 0, 793526538746, 1899372005233, 795332419880, 46379312393, 0, 0] := by
  rw [show D2M8K2.u3680 = KTree.node D2M8K2.u3678 (nat_lit 8408860) (nat_lit 2169335445) (nat_lit 0) D2M8K2.u3679 from rfl, totK_node, atot3678, atot3679]
  decide +kernel

theorem arows3684 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3684 = true := by
  rw [show D2M8K2.u3684 = KTree.node D2M8K2.u3682 (nat_lit 8413768) (nat_lit 2196842694) (nat_lit 0) D2M8K2.u3683 from rfl, allE_node, arows3682, irow3684, arows3683]
  all_goals rfl

theorem atot3684 : totK PD2M8K2 D2M8K2.u3684 = [169749411087, 341393312455, 399431830005, 1230528014520, 1164038441452, 223026865017, 4977114383, 0] := by
  rw [show D2M8K2.u3684 = KTree.node D2M8K2.u3682 (nat_lit 8413768) (nat_lit 2196842694) (nat_lit 0) D2M8K2.u3683 from rfl, totK_node, atot3682, atot3683]
  decide +kernel

theorem arows3687 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3687 = true := by
  rw [show D2M8K2.u3687 = KTree.node D2M8K2.u3685 (nat_lit 8462241) (nat_lit 1575400985) (nat_lit 0) D2M8K2.u3686 from rfl, allE_node, arows3685, irow3687, arows3686]
  all_goals rfl

theorem atot3687 : totK PD2M8K2 D2M8K2.u3687 = [439170585685, 1583288751132, 1382970477101, 196293712040, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u3687 = KTree.node D2M8K2.u3685 (nat_lit 8462241) (nat_lit 1575400985) (nat_lit 0) D2M8K2.u3686 from rfl, totK_node, atot3685, atot3686]
  decide +kernel

theorem arows3692 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3692 = true := by
  rw [show D2M8K2.u3692 = KTree.node D2M8K2.u3690 (nat_lit 8469538) (nat_lit 3916566795) (nat_lit 0) D2M8K2.u3691 from rfl, allE_node, arows3690, irow3692, arows3691]
  all_goals rfl

theorem atot3692 : totK PD2M8K2 D2M8K2.u3692 = [401182322297, 1434654436027, 1407192676910, 329930256685, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u3692 = KTree.node D2M8K2.u3690 (nat_lit 8469538) (nat_lit 3916566795) (nat_lit 0) D2M8K2.u3691 from rfl, totK_node, atot3690, atot3691]
  decide +kernel

theorem arows3695 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3695 = true := by
  rw [show D2M8K2.u3695 = KTree.node D2M8K2.u3693 (nat_lit 8473287) (nat_lit 3416423548) (nat_lit 0) D2M8K2.u3694 from rfl, allE_node, arows3693, irow3695, arows3694]
  all_goals rfl

theorem atot3695 : totK PD2M8K2 D2M8K2.u3695 = [399855667453, 1431101770687, 1414596586979, 341384201973, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u3695 = KTree.node D2M8K2.u3693 (nat_lit 8473287) (nat_lit 3416423548) (nat_lit 0) D2M8K2.u3694 from rfl, totK_node, atot3693, atot3694]
  decide +kernel

theorem arows3699 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3699 = true := by
  rw [show D2M8K2.u3699 = KTree.node D2M8K2.u3697 (nat_lit 8479668) (nat_lit 2619742406) (nat_lit 0) D2M8K2.u3698 from rfl, allE_node, arows3697, irow3699, arows3698]
  all_goals rfl

theorem atot3699 : totK PD2M8K2 D2M8K2.u3699 = [237319555436, 1180946092172, 1620410812063, 521084238072, 23418599596, 0, 0, 0] := by
  rw [show D2M8K2.u3699 = KTree.node D2M8K2.u3697 (nat_lit 8479668) (nat_lit 2619742406) (nat_lit 0) D2M8K2.u3698 from rfl, totK_node, atot3697, atot3698]
  decide +kernel

theorem arows3702 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3702 = true := by
  rw [show D2M8K2.u3702 = KTree.node D2M8K2.u3700 (nat_lit 8482855) (nat_lit 2302159000) (nat_lit 0) D2M8K2.u3701 from rfl, allE_node, arows3700, irow3702, arows3701]
  all_goals rfl

theorem atot3702 : totK PD2M8K2 D2M8K2.u3702 = [0, 469627569769, 1619510934457, 1228961065859, 168562479864, 1369150432, 0, 0] := by
  rw [show D2M8K2.u3702 = KTree.node D2M8K2.u3700 (nat_lit 8482855) (nat_lit 2302159000) (nat_lit 0) D2M8K2.u3701 from rfl, totK_node, atot3700, atot3701]
  decide +kernel

theorem arows3710 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3710 = true := by
  rw [show D2M8K2.u3710 = KTree.node D2M8K2.u3708 (nat_lit 8491823) (nat_lit 2667825749) (nat_lit 0) D2M8K2.u3709 from rfl, allE_node, arows3708, irow3710, arows3709]
  all_goals rfl

theorem atot3710 : totK PD2M8K2 D2M8K2.u3710 = [0, 749197442680, 1898859585428, 895678952314, 49045806344, 0, 0, 0] := by
  rw [show D2M8K2.u3710 = KTree.node D2M8K2.u3708 (nat_lit 8491823) (nat_lit 2667825749) (nat_lit 0) D2M8K2.u3709 from rfl, totK_node, atot3708, atot3709]
  decide +kernel

theorem arows3713 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3713 = true := by
  rw [show D2M8K2.u3713 = KTree.node D2M8K2.u3711 (nat_lit 8505603) (nat_lit 3724153277) (nat_lit 0) D2M8K2.u3712 from rfl, allE_node, arows3711, irow3713, arows3712]
  all_goals rfl

theorem atot3713 : totK PD2M8K2 D2M8K2.u3713 = [433306685740, 1349308540832, 1362391440347, 488633574725, 28363432085, 0, 0, 0] := by
  rw [show D2M8K2.u3713 = KTree.node D2M8K2.u3711 (nat_lit 8505603) (nat_lit 3724153277) (nat_lit 0) D2M8K2.u3712 from rfl, totK_node, atot3711, atot3712]
  decide +kernel

theorem arows3717 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3717 = true := by
  rw [show D2M8K2.u3717 = KTree.node D2M8K2.u3715 (nat_lit 8508210) (nat_lit 3415279830) (nat_lit 0) D2M8K2.u3716 from rfl, allE_node, arows3715, irow3717, arows3716]
  all_goals rfl

theorem atot3717 : totK PD2M8K2 D2M8K2.u3717 = [256012786791, 1176090293265, 1581550197646, 601787990555, 37609398105, 0, 0, 0] := by
  rw [show D2M8K2.u3717 = KTree.node D2M8K2.u3715 (nat_lit 8508210) (nat_lit 3415279830) (nat_lit 0) D2M8K2.u3716 from rfl, totK_node, atot3715, atot3716]
  decide +kernel

theorem arows3720 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3720 = true := by
  rw [show D2M8K2.u3720 = KTree.node D2M8K2.u3718 (nat_lit 8511225) (nat_lit 1808419219) (nat_lit 0) D2M8K2.u3719 from rfl, allE_node, arows3718, irow3720, arows3719]
  all_goals rfl

theorem atot3720 : totK PD2M8K2 D2M8K2.u3720 = [415321266318, 1462831536133, 1415925449612, 320884498847, 12900132148, 0, 0, 0] := by
  rw [show D2M8K2.u3720 = KTree.node D2M8K2.u3718 (nat_lit 8511225) (nat_lit 1808419219) (nat_lit 0) D2M8K2.u3719 from rfl, totK_node, atot3718, atot3719]
  decide +kernel

theorem arows3725 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3725 = true := by
  rw [show D2M8K2.u3725 = KTree.node D2M8K2.u3723 (nat_lit 8514937) (nat_lit 1420264360) (nat_lit 0) D2M8K2.u3724 from rfl, allE_node, arows3723, irow3725, arows3724]
  all_goals rfl

theorem atot3725 : totK PD2M8K2 D2M8K2.u3725 = [410320304667, 1420813965276, 1447226279673, 342772375670, 13079982537, 0, 0, 0] := by
  rw [show D2M8K2.u3725 = KTree.node D2M8K2.u3723 (nat_lit 8514937) (nat_lit 1420264360) (nat_lit 0) D2M8K2.u3724 from rfl, totK_node, atot3723, atot3724]
  decide +kernel

theorem arows3728 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3728 = true := by
  rw [show D2M8K2.u3728 = KTree.node D2M8K2.u3726 (nat_lit 8519096) (nat_lit 2758254739) (nat_lit 0) D2M8K2.u3727 from rfl, allE_node, arows3726, irow3728, arows3727]
  all_goals rfl

theorem atot3728 : totK PD2M8K2 D2M8K2.u3728 = [512012713816, 1651290528639, 1306437410797, 197676416996, 3785881357, 0, 0, 0] := by
  rw [show D2M8K2.u3728 = KTree.node D2M8K2.u3726 (nat_lit 8519096) (nat_lit 2758254739) (nat_lit 0) D2M8K2.u3727 from rfl, totK_node, atot3726, atot3727]
  decide +kernel

theorem arows3732 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3732 = true := by
  rw [show D2M8K2.u3732 = KTree.node D2M8K2.u3730 (nat_lit 8522267) (nat_lit 2913744014) (nat_lit 0) D2M8K2.u3731 from rfl, allE_node, arows3730, irow3732, arows3731]
  all_goals rfl

theorem atot3732 : totK PD2M8K2 D2M8K2.u3732 = [19691318959, 871757110912, 1858517897253, 824472627495, 56997483727, 0, 0, 0] := by
  rw [show D2M8K2.u3732 = KTree.node D2M8K2.u3730 (nat_lit 8522267) (nat_lit 2913744014) (nat_lit 0) D2M8K2.u3731 from rfl, totK_node, atot3730, atot3731]
  decide +kernel

theorem arows3735 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3735 = true := by
  rw [show D2M8K2.u3735 = KTree.node D2M8K2.u3733 (nat_lit 8528642) (nat_lit 4027104210) (nat_lit 0) D2M8K2.u3734 from rfl, allE_node, arows3733, irow3735, arows3734]
  all_goals rfl

theorem atot3735 : totK PD2M8K2 D2M8K2.u3735 = [0, 292721187642, 1215143010311, 1512917346238, 561481525735, 36921873854, 0, 0] := by
  rw [show D2M8K2.u3735 = KTree.node D2M8K2.u3733 (nat_lit 8528642) (nat_lit 4027104210) (nat_lit 0) D2M8K2.u3734 from rfl, totK_node, atot3733, atot3734]
  decide +kernel

theorem arows3741 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3741 = true := by
  rw [show D2M8K2.u3741 = KTree.node D2M8K2.u3739 (nat_lit 8531752) (nat_lit 3888878535) (nat_lit 0) D2M8K2.u3740 from rfl, allE_node, arows3739, irow3741, arows3740]
  all_goals rfl

theorem atot3741 : totK PD2M8K2 D2M8K2.u3741 = [0, 449999205367, 1537586507455, 1375615988318, 248352451953, 5159868635, 0, 0] := by
  rw [show D2M8K2.u3741 = KTree.node D2M8K2.u3739 (nat_lit 8531752) (nat_lit 3888878535) (nat_lit 0) D2M8K2.u3740 from rfl, totK_node, atot3739, atot3740]
  decide +kernel

theorem arows3744 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3744 = true := by
  rw [show D2M8K2.u3744 = KTree.node D2M8K2.u3742 (nat_lit 8535595) (nat_lit 1616601959) (nat_lit 0) D2M8K2.u3743 from rfl, allE_node, arows3742, irow3744, arows3743]
  all_goals rfl

theorem atot3744 : totK PD2M8K2 D2M8K2.u3744 = [0, 446109151231, 1537670587532, 1382082298933, 257028466136, 5218872685, 0, 0] := by
  rw [show D2M8K2.u3744 = KTree.node D2M8K2.u3742 (nat_lit 8535595) (nat_lit 1616601959) (nat_lit 0) D2M8K2.u3743 from rfl, totK_node, atot3742, atot3743]
  decide +kernel

theorem arows3748 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3748 = true := by
  rw [show D2M8K2.u3748 = KTree.node D2M8K2.u3746 (nat_lit 8539829) (nat_lit 2366624603) (nat_lit 0) D2M8K2.u3747 from rfl, allE_node, arows3746, irow3748, arows3747]
  all_goals rfl

theorem atot3748 : totK PD2M8K2 D2M8K2.u3748 = [0, 524902560649, 1663939707172, 1292831549514, 179897548060, 1415142070, 0, 0] := by
  rw [show D2M8K2.u3748 = KTree.node D2M8K2.u3746 (nat_lit 8539829) (nat_lit 2366624603) (nat_lit 0) D2M8K2.u3747 from rfl, totK_node, atot3746, atot3747]
  decide +kernel

theorem arows3751 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3751 = true := by
  rw [show D2M8K2.u3751 = KTree.node D2M8K2.u3749 (nat_lit 8543219) (nat_lit 2968004670) (nat_lit 0) D2M8K2.u3750 from rfl, allE_node, arows3749, irow3751, arows3750]
  all_goals rfl

theorem atot3751 : totK PD2M8K2 D2M8K2.u3751 = [378822834728, 953454389085, 975734377414, 973651843507, 285767696862, 9302370699, 0, 0] := by
  rw [show D2M8K2.u3751 = KTree.node D2M8K2.u3749 (nat_lit 8543219) (nat_lit 2968004670) (nat_lit 0) D2M8K2.u3750 from rfl, totK_node, atot3749, atot3750]
  decide +kernel

theorem arows3756 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3756 = true := by
  rw [show D2M8K2.u3756 = KTree.node D2M8K2.u3754 (nat_lit 8547272) (nat_lit 3314462893) (nat_lit 0) D2M8K2.u3755 from rfl, allE_node, arows3754, irow3756, arows3755]
  all_goals rfl

theorem atot3756 : totK PD2M8K2 D2M8K2.u3756 = [420717295190, 1568053544317, 1448799930342, 215064824633, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u3756 = KTree.node D2M8K2.u3754 (nat_lit 8547272) (nat_lit 3314462893) (nat_lit 0) D2M8K2.u3755 from rfl, totK_node, atot3754, atot3755]
  decide +kernel

theorem arows3759 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3759 = true := by
  rw [show D2M8K2.u3759 = KTree.node D2M8K2.u3757 (nat_lit 8550124) (nat_lit 3739785811) (nat_lit 0) D2M8K2.u3758 from rfl, allE_node, arows3757, irow3759, arows3758]
  all_goals rfl

theorem atot3759 : totK PD2M8K2 D2M8K2.u3759 = [366548613667, 1257415938702, 1411477408737, 560908091552, 37560868892, 0, 0, 0] := by
  rw [show D2M8K2.u3759 = KTree.node D2M8K2.u3757 (nat_lit 8550124) (nat_lit 3739785811) (nat_lit 0) D2M8K2.u3758 from rfl, totK_node, atot3757, atot3758]
  decide +kernel

theorem arows3763 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3763 = true := by
  rw [show D2M8K2.u3763 = KTree.node D2M8K2.u3761 (nat_lit 8553264) (nat_lit 3223242483) (nat_lit 0) D2M8K2.u3762 from rfl, allE_node, arows3761, irow3763, arows3762]
  all_goals rfl

theorem atot3763 : totK PD2M8K2 D2M8K2.u3763 = [398786061358, 1420221838649, 1448532634723, 338029196651, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u3763 = KTree.node D2M8K2.u3761 (nat_lit 8553264) (nat_lit 3223242483) (nat_lit 0) D2M8K2.u3762 from rfl, totK_node, atot3761, atot3762]
  decide +kernel

theorem arows3766 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3766 = true := by
  rw [show D2M8K2.u3766 = KTree.node D2M8K2.u3764 (nat_lit 8560890) (nat_lit 3843899909) (nat_lit 0) D2M8K2.u3765 from rfl, allE_node, arows3764, irow3766, arows3765]
  all_goals rfl

theorem atot3766 : totK PD2M8K2 D2M8K2.u3766 = [426377249112, 1552493813353, 1395539730572, 237765211759, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u3766 = KTree.node D2M8K2.u3764 (nat_lit 8560890) (nat_lit 3843899909) (nat_lit 0) D2M8K2.u3765 from rfl, totK_node, atot3764, atot3765]
  decide +kernel

theorem arows3773 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3773 = true := by
  rw [show D2M8K2.u3773 = KTree.node D2M8K2.u3771 (nat_lit 8564060) (nat_lit 2530735450) (nat_lit 0) D2M8K2.u3772 from rfl, allE_node, arows3771, irow3773, arows3772]
  all_goals rfl

theorem atot3773 : totK PD2M8K2 D2M8K2.u3773 = [0, 726852149266, 1880809281409, 887495509578, 51832381302, 0, 0, 0] := by
  rw [show D2M8K2.u3773 = KTree.node D2M8K2.u3771 (nat_lit 8564060) (nat_lit 2530735450) (nat_lit 0) D2M8K2.u3772 from rfl, totK_node, atot3771, atot3772]
  decide +kernel

theorem arows3776 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3776 = true := by
  rw [show D2M8K2.u3776 = KTree.node D2M8K2.u3774 (nat_lit 8568209) (nat_lit 2209295029) (nat_lit 0) D2M8K2.u3775 from rfl, allE_node, arows3774, irow3776, arows3775]
  all_goals rfl

theorem atot3776 : totK PD2M8K2 D2M8K2.u3776 = [0, 570463318463, 1710880509789, 1182763030297, 137009539126, 1206465782, 0, 0] := by
  rw [show D2M8K2.u3776 = KTree.node D2M8K2.u3774 (nat_lit 8568209) (nat_lit 2209295029) (nat_lit 0) D2M8K2.u3775 from rfl, totK_node, atot3774, atot3775]
  decide +kernel

theorem arows3780 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3780 = true := by
  rw [show D2M8K2.u3780 = KTree.node D2M8K2.u3778 (nat_lit 8572750) (nat_lit 3607090270) (nat_lit 0) D2M8K2.u3779 from rfl, allE_node, arows3778, irow3780, arows3779]
  all_goals rfl

theorem atot3780 : totK PD2M8K2 D2M8K2.u3780 = [0, 386342181108, 1453323377586, 1374594170930, 307297630680, 13016197374, 0, 0] := by
  rw [show D2M8K2.u3780 = KTree.node D2M8K2.u3778 (nat_lit 8572750) (nat_lit 3607090270) (nat_lit 0) D2M8K2.u3779 from rfl, totK_node, atot3778, atot3779]
  decide +kernel

theorem arows3783 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3783 = true := by
  rw [show D2M8K2.u3783 = KTree.node D2M8K2.u3781 (nat_lit 8580197) (nat_lit 2343298695) (nat_lit 0) D2M8K2.u3782 from rfl, allE_node, arows3781, irow3783, arows3782]
  all_goals rfl

theorem atot3783 : totK PD2M8K2 D2M8K2.u3783 = [0, 502697424871, 1617344669837, 1250334291430, 189371639029, 4574395652, 0, 0] := by
  rw [show D2M8K2.u3783 = KTree.node D2M8K2.u3781 (nat_lit 8580197) (nat_lit 2343298695) (nat_lit 0) D2M8K2.u3782 from rfl, totK_node, atot3781, atot3782]
  decide +kernel

theorem arows3788 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3788 = true := by
  rw [show D2M8K2.u3788 = KTree.node D2M8K2.u3786 (nat_lit 8585803) (nat_lit 2224468087) (nat_lit 0) D2M8K2.u3787 from rfl, allE_node, arows3786, irow3788, arows3787]
  all_goals rfl

theorem atot3788 : totK PD2M8K2 D2M8K2.u3788 = [378914462040, 1399676357272, 1414409371968, 376772175173, 18845624966, 0, 0, 0] := by
  rw [show D2M8K2.u3788 = KTree.node D2M8K2.u3786 (nat_lit 8585803) (nat_lit 2224468087) (nat_lit 0) D2M8K2.u3787 from rfl, totK_node, atot3786, atot3787]
  decide +kernel

theorem arows3791 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3791 = true := by
  rw [show D2M8K2.u3791 = KTree.node D2M8K2.u3789 (nat_lit 8589509) (nat_lit 2275700222) (nat_lit 0) D2M8K2.u3790 from rfl, allE_node, arows3789, irow3791, arows3790]
  all_goals rfl

theorem atot3791 : totK PD2M8K2 D2M8K2.u3791 = [420789728411, 1422308532806, 1388169812930, 423442515463, 29349649617, 0, 0, 0] := by
  rw [show D2M8K2.u3791 = KTree.node D2M8K2.u3789 (nat_lit 8589509) (nat_lit 2275700222) (nat_lit 0) D2M8K2.u3790 from rfl, totK_node, atot3789, atot3790]
  decide +kernel

theorem arows3795 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3795 = true := by
  rw [show D2M8K2.u3795 = KTree.node D2M8K2.u3793 (nat_lit 8596026) (nat_lit 3943699390) (nat_lit 0) D2M8K2.u3794 from rfl, allE_node, arows3793, irow3795, arows3794]
  all_goals rfl

theorem atot3795 : totK PD2M8K2 D2M8K2.u3795 = [438320121704, 1470328085230, 1380238311284, 331832017163, 9407370064, 0, 0, 0] := by
  rw [show D2M8K2.u3795 = KTree.node D2M8K2.u3793 (nat_lit 8596026) (nat_lit 3943699390) (nat_lit 0) D2M8K2.u3794 from rfl, totK_node, atot3793, atot3794]
  decide +kernel

theorem arows3798 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3798 = true := by
  rw [show D2M8K2.u3798 = KTree.node D2M8K2.u3796 (nat_lit 8599087) (nat_lit 2172785238) (nat_lit 0) D2M8K2.u3797 from rfl, allE_node, arows3796, irow3798, arows3797]
  all_goals rfl

theorem atot3798 : totK PD2M8K2 D2M8K2.u3798 = [327348471015, 1393486435100, 1537869520074, 349804688871, 13149116973, 0, 0, 0] := by
  rw [show D2M8K2.u3798 = KTree.node D2M8K2.u3796 (nat_lit 8599087) (nat_lit 2172785238) (nat_lit 0) D2M8K2.u3797 from rfl, totK_node, atot3796, atot3797]
  decide +kernel

theorem arows3804 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3804 = true := by
  rw [show D2M8K2.u3804 = KTree.node D2M8K2.u3802 (nat_lit 8603075) (nat_lit 2696209974) (nat_lit 0) D2M8K2.u3803 from rfl, allE_node, arows3802, irow3804, arows3803]
  all_goals rfl

theorem atot3804 : totK PD2M8K2 D2M8K2.u3804 = [426423859968, 1446295304865, 1394595244473, 329962565074, 8849279479, 0, 0, 0] := by
  rw [show D2M8K2.u3804 = KTree.node D2M8K2.u3802 (nat_lit 8603075) (nat_lit 2696209974) (nat_lit 0) D2M8K2.u3803 from rfl, totK_node, atot3802, atot3803]
  decide +kernel

theorem arows3807 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3807 = true := by
  rw [show D2M8K2.u3807 = KTree.node D2M8K2.u3805 (nat_lit 8606672) (nat_lit 3788156863) (nat_lit 0) D2M8K2.u3806 from rfl, allE_node, arows3805, irow3807, arows3806]
  all_goals rfl

theorem atot3807 : totK PD2M8K2 D2M8K2.u3807 = [0, 492453041175, 1668577179644, 1230913733410, 138163213348, 1239866073, 0, 0] := by
  rw [show D2M8K2.u3807 = KTree.node D2M8K2.u3805 (nat_lit 8606672) (nat_lit 3788156863) (nat_lit 0) D2M8K2.u3806 from rfl, totK_node, atot3805, atot3806]
  decide +kernel

theorem arows3811 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3811 = true := by
  rw [show D2M8K2.u3811 = KTree.node D2M8K2.u3809 (nat_lit 8610469) (nat_lit 1307876877) (nat_lit 0) D2M8K2.u3810 from rfl, allE_node, arows3809, irow3811, arows3810]
  all_goals rfl

theorem atot3811 : totK PD2M8K2 D2M8K2.u3811 = [0, 745912198366, 1862191861806, 972081217721, 77337142612, 0, 0, 0] := by
  rw [show D2M8K2.u3811 = KTree.node D2M8K2.u3809 (nat_lit 8610469) (nat_lit 1307876877) (nat_lit 0) D2M8K2.u3810 from rfl, totK_node, atot3809, atot3810]
  decide +kernel

theorem arows3814 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3814 = true := by
  rw [show D2M8K2.u3814 = KTree.node D2M8K2.u3812 (nat_lit 8618784) (nat_lit 3487240157) (nat_lit 0) D2M8K2.u3813 from rfl, allE_node, arows3812, irow3814, arows3813]
  all_goals rfl

theorem atot3814 : totK PD2M8K2 D2M8K2.u3814 = [0, 411182262861, 1450977872583, 1373291070143, 307423870776, 13105450397, 0, 0] := by
  rw [show D2M8K2.u3814 = KTree.node D2M8K2.u3812 (nat_lit 8618784) (nat_lit 3487240157) (nat_lit 0) D2M8K2.u3813 from rfl, totK_node, atot3812, atot3813]
  decide +kernel

theorem arows3819 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3819 = true := by
  rw [show D2M8K2.u3819 = KTree.node D2M8K2.u3817 (nat_lit 8623088) (nat_lit 3471514717) (nat_lit 0) D2M8K2.u3818 from rfl, allE_node, arows3817, irow3819, arows3818]
  all_goals rfl

theorem atot3819 : totK PD2M8K2 D2M8K2.u3819 = [70593750018, 522033542177, 1520180366529, 1248799175560, 194482512194, 4720618446, 0, 0] := by
  rw [show D2M8K2.u3819 = KTree.node D2M8K2.u3817 (nat_lit 8623088) (nat_lit 3471514717) (nat_lit 0) D2M8K2.u3818 from rfl, totK_node, atot3817, atot3818]
  decide +kernel

theorem arows3822 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3822 = true := by
  rw [show D2M8K2.u3822 = KTree.node D2M8K2.u3820 (nat_lit 8669377) (nat_lit 1575612183) (nat_lit 0) D2M8K2.u3821 from rfl, allE_node, arows3820, irow3822, arows3821]
  all_goals rfl

theorem atot3822 : totK PD2M8K2 D2M8K2.u3822 = [450602605928, 1588561314293, 1363565169479, 192291591950, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u3822 = KTree.node D2M8K2.u3820 (nat_lit 8669377) (nat_lit 1575612183) (nat_lit 0) D2M8K2.u3821 from rfl, totK_node, atot3820, atot3821]
  decide +kernel

theorem arows3826 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3826 = true := by
  rw [show D2M8K2.u3826 = KTree.node D2M8K2.u3824 (nat_lit 8673245) (nat_lit 2234956051) (nat_lit 0) D2M8K2.u3825 from rfl, allE_node, arows3824, irow3826, arows3825]
  all_goals rfl

theorem atot3826 : totK PD2M8K2 D2M8K2.u3826 = [301058012645, 1256349348250, 1508102758920, 550202145593, 33085089180, 0, 0, 0] := by
  rw [show D2M8K2.u3826 = KTree.node D2M8K2.u3824 (nat_lit 8673245) (nat_lit 2234956051) (nat_lit 0) D2M8K2.u3825 from rfl, totK_node, atot3824, atot3825]
  decide +kernel

theorem arows3829 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3829 = true := by
  rw [show D2M8K2.u3829 = KTree.node D2M8K2.u3827 (nat_lit 8676045) (nat_lit 1245795180) (nat_lit 0) D2M8K2.u3828 from rfl, allE_node, arows3827, irow3829, arows3828]
  all_goals rfl

theorem atot3829 : totK PD2M8K2 D2M8K2.u3829 = [419194404053, 1433659869523, 1366624670023, 333149941403, 17347886536, 0, 0, 0] := by
  rw [show D2M8K2.u3829 = KTree.node D2M8K2.u3827 (nat_lit 8676045) (nat_lit 1245795180) (nat_lit 0) D2M8K2.u3828 from rfl, totK_node, atot3827, atot3828]
  decide +kernel

theorem arows3838 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3838 = true := by
  rw [show D2M8K2.u3838 = KTree.node D2M8K2.u3836 (nat_lit 8679411) (nat_lit 2914096891) (nat_lit 0) D2M8K2.u3837 from rfl, allE_node, arows3836, irow3838, arows3837]
  all_goals rfl

theorem atot3838 : totK PD2M8K2 D2M8K2.u3838 = [419423190697, 1461300741903, 1395319898087, 308113851547, 10663791286, 0, 0, 0] := by
  rw [show D2M8K2.u3838 = KTree.node D2M8K2.u3836 (nat_lit 8679411) (nat_lit 2914096891) (nat_lit 0) D2M8K2.u3837 from rfl, totK_node, atot3836, atot3837]
  decide +kernel

theorem arows3841 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3841 = true := by
  rw [show D2M8K2.u3841 = KTree.node D2M8K2.u3839 (nat_lit 8685902) (nat_lit 3684222948) (nat_lit 0) D2M8K2.u3840 from rfl, allE_node, arows3839, irow3841, arows3840]
  all_goals rfl

theorem atot3841 : totK PD2M8K2 D2M8K2.u3841 = [447647155819, 1518459661168, 1390701628306, 293230603504, 7396279795, 0, 0, 0] := by
  rw [show D2M8K2.u3841 = KTree.node D2M8K2.u3839 (nat_lit 8685902) (nat_lit 3684222948) (nat_lit 0) D2M8K2.u3840 from rfl, totK_node, atot3839, atot3840]
  decide +kernel

theorem arows3845 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3845 = true := by
  rw [show D2M8K2.u3845 = KTree.node D2M8K2.u3843 (nat_lit 8689345) (nat_lit 1473767533) (nat_lit 0) D2M8K2.u3844 from rfl, allE_node, arows3843, irow3845, arows3844]
  all_goals rfl

theorem atot3845 : totK PD2M8K2 D2M8K2.u3845 = [0, 560393685008, 1701001276913, 1147198251509, 122680578984, 1310285577, 0, 0] := by
  rw [show D2M8K2.u3845 = KTree.node D2M8K2.u3843 (nat_lit 8689345) (nat_lit 1473767533) (nat_lit 0) D2M8K2.u3844 from rfl, totK_node, atot3843, atot3844]
  decide +kernel

theorem arows3848 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3848 = true := by
  rw [show D2M8K2.u3848 = KTree.node D2M8K2.u3846 (nat_lit 8693042) (nat_lit 4046883989) (nat_lit 0) D2M8K2.u3847 from rfl, allE_node, arows3846, irow3848, arows3847]
  all_goals rfl

theorem atot3848 : totK PD2M8K2 D2M8K2.u3848 = [0, 687959270309, 1792978305194, 1078720532247, 95136336067, 0, 0, 0] := by
  rw [show D2M8K2.u3848 = KTree.node D2M8K2.u3846 (nat_lit 8693042) (nat_lit 4046883989) (nat_lit 0) D2M8K2.u3847 from rfl, totK_node, atot3846, atot3847]
  decide +kernel

theorem arows3853 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3853 = true := by
  rw [show D2M8K2.u3853 = KTree.node D2M8K2.u3851 (nat_lit 8697750) (nat_lit 2102532832) (nat_lit 0) D2M8K2.u3852 from rfl, allE_node, arows3851, irow3853, arows3852]
  all_goals rfl

theorem atot3853 : totK PD2M8K2 D2M8K2.u3853 = [0, 417330487905, 1548141137845, 1356518053982, 218707251505, 4879840392, 0, 0] := by
  rw [show D2M8K2.u3853 = KTree.node D2M8K2.u3851 (nat_lit 8697750) (nat_lit 2102532832) (nat_lit 0) D2M8K2.u3852 from rfl, totK_node, atot3851, atot3852]
  decide +kernel

theorem arows3856 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3856 = true := by
  rw [show D2M8K2.u3856 = KTree.node D2M8K2.u3854 (nat_lit 8701638) (nat_lit 3686403611) (nat_lit 0) D2M8K2.u3855 from rfl, allE_node, arows3854, irow3856, arows3855]
  all_goals rfl

theorem atot3856 : totK PD2M8K2 D2M8K2.u3856 = [0, 474188472030, 1576028660442, 1303364559746, 213909887424, 4931404646, 0, 0] := by
  rw [show D2M8K2.u3856 = KTree.node D2M8K2.u3854 (nat_lit 8701638) (nat_lit 3686403611) (nat_lit 0) D2M8K2.u3855 from rfl, totK_node, atot3854, atot3855]
  decide +kernel

theorem arows3860 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3860 = true := by
  rw [show D2M8K2.u3860 = KTree.node D2M8K2.u3858 (nat_lit 8708285) (nat_lit 1279977242) (nat_lit 0) D2M8K2.u3859 from rfl, allE_node, arows3858, irow3860, arows3859]
  all_goals rfl

theorem atot3860 : totK PD2M8K2 D2M8K2.u3860 = [0, 362787634994, 1356166661408, 1419522862553, 398628063311, 21751168066, 0, 0] := by
  rw [show D2M8K2.u3860 = KTree.node D2M8K2.u3858 (nat_lit 8708285) (nat_lit 1279977242) (nat_lit 0) D2M8K2.u3859 from rfl, totK_node, atot3858, atot3859]
  decide +kernel

theorem arows3863 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3863 = true := by
  rw [show D2M8K2.u3863 = KTree.node D2M8K2.u3861 (nat_lit 8711792) (nat_lit 3737803747) (nat_lit 0) D2M8K2.u3862 from rfl, allE_node, arows3861, irow3863, arows3862]
  all_goals rfl

theorem atot3863 : totK PD2M8K2 D2M8K2.u3863 = [0, 439030785506, 1585853715276, 1378182339311, 192333542082, 1369150432, 0, 0] := by
  rw [show D2M8K2.u3863 = KTree.node D2M8K2.u3861 (nat_lit 8711792) (nat_lit 3737803747) (nat_lit 0) D2M8K2.u3862 from rfl, totK_node, atot3861, atot3862]
  decide +kernel

theorem arows3869 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3869 = true := by
  rw [show D2M8K2.u3869 = KTree.node D2M8K2.u3867 (nat_lit 8718941) (nat_lit 2288192481) (nat_lit 0) D2M8K2.u3868 from rfl, allE_node, arows3867, irow3869, arows3868]
  all_goals rfl

theorem atot3869 : totK PD2M8K2 D2M8K2.u3869 = [0, 461303744468, 1529650180702, 1347408201776, 247092856036, 5172807878, 0, 0] := by
  rw [show D2M8K2.u3869 = KTree.node D2M8K2.u3867 (nat_lit 8718941) (nat_lit 2288192481) (nat_lit 0) D2M8K2.u3868 from rfl, totK_node, atot3867, atot3868]
  decide +kernel

theorem arows3872 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3872 = true := by
  rw [show D2M8K2.u3872 = KTree.node D2M8K2.u3870 (nat_lit 8722684) (nat_lit 3125289028) (nat_lit 0) D2M8K2.u3871 from rfl, allE_node, arows3870, irow3872, arows3871]
  all_goals rfl

theorem atot3872 : totK PD2M8K2 D2M8K2.u3872 = [0, 421557683113, 1507553912889, 1399232123540, 258791566620, 5228939780, 0, 0] := by
  rw [show D2M8K2.u3872 = KTree.node D2M8K2.u3870 (nat_lit 8722684) (nat_lit 3125289028) (nat_lit 0) D2M8K2.u3871 from rfl, totK_node, atot3870, atot3871]
  decide +kernel

theorem arows3876 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3876 = true := by
  rw [show D2M8K2.u3876 = KTree.node D2M8K2.u3874 (nat_lit 8729152) (nat_lit 1405514689) (nat_lit 0) D2M8K2.u3875 from rfl, allE_node, arows3874, irow3876, arows3875]
  all_goals rfl

theorem atot3876 : totK PD2M8K2 D2M8K2.u3876 = [0, 92937627352, 949167776622, 1807386472276, 658621771030, 31284882463, 0, 0] := by
  rw [show D2M8K2.u3876 = KTree.node D2M8K2.u3874 (nat_lit 8729152) (nat_lit 1405514689) (nat_lit 0) D2M8K2.u3875 from rfl, totK_node, atot3874, atot3875]
  decide +kernel

theorem arows3879 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3879 = true := by
  rw [show D2M8K2.u3879 = KTree.node D2M8K2.u3877 (nat_lit 8733030) (nat_lit 3673690346) (nat_lit 0) D2M8K2.u3878 from rfl, allE_node, arows3877, irow3879, arows3878]
  all_goals rfl

theorem atot3879 : totK PD2M8K2 D2M8K2.u3879 = [0, 0, 528894776457, 1698188452164, 1125789928762, 124655241006, 1369150432, 0] := by
  rw [show D2M8K2.u3879 = KTree.node D2M8K2.u3877 (nat_lit 8733030) (nat_lit 3673690346) (nat_lit 0) D2M8K2.u3878 from rfl, totK_node, atot3877, atot3878]
  decide +kernel

theorem arows3884 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3884 = true := by
  rw [show D2M8K2.u3884 = KTree.node D2M8K2.u3882 (nat_lit 8741705) (nat_lit 1208269967) (nat_lit 0) D2M8K2.u3883 from rfl, allE_node, arows3882, irow3884, arows3883]
  all_goals rfl

theorem atot3884 : totK PD2M8K2 D2M8K2.u3884 = [0, 0, 764131753458, 1923774443099, 828557731654, 37623528610, 0, 0] := by
  rw [show D2M8K2.u3884 = KTree.node D2M8K2.u3882 (nat_lit 8741705) (nat_lit 1208269967) (nat_lit 0) D2M8K2.u3883 from rfl, totK_node, atot3882, atot3883]
  decide +kernel

theorem arows3887 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3887 = true := by
  rw [show D2M8K2.u3887 = KTree.node D2M8K2.u3885 (nat_lit 8755051) (nat_lit 1615998974) (nat_lit 0) D2M8K2.u3886 from rfl, allE_node, arows3885, irow3887, arows3886]
  all_goals rfl

theorem atot3887 : totK PD2M8K2 D2M8K2.u3887 = [0, 445310450810, 1417976539120, 1325359459219, 450561256824, 38777101889, 0, 0] := by
  rw [show D2M8K2.u3887 = KTree.node D2M8K2.u3885 (nat_lit 8755051) (nat_lit 1615998974) (nat_lit 0) D2M8K2.u3886 from rfl, totK_node, atot3885, atot3886]
  decide +kernel

theorem arows3891 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3891 = true := by
  rw [show D2M8K2.u3891 = KTree.node D2M8K2.u3889 (nat_lit 8757871) (nat_lit 2353928751) (nat_lit 0) D2M8K2.u3890 from rfl, allE_node, arows3889, irow3891, arows3890]
  all_goals rfl

theorem atot3891 : totK PD2M8K2 D2M8K2.u3891 = [0, 414955518971, 1386976564626, 1384631935458, 417656145788, 16100220446, 0, 0] := by
  rw [show D2M8K2.u3891 = KTree.node D2M8K2.u3889 (nat_lit 8757871) (nat_lit 2353928751) (nat_lit 0) D2M8K2.u3890 from rfl, totK_node, atot3889, atot3890]
  decide +kernel

theorem arows3894 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3894 = true := by
  rw [show D2M8K2.u3894 = KTree.node D2M8K2.u3892 (nat_lit 8761313) (nat_lit 2144228027) (nat_lit 0) D2M8K2.u3893 from rfl, allE_node, arows3892, irow3894, arows3893]
  all_goals rfl

theorem atot3894 : totK PD2M8K2 D2M8K2.u3894 = [0, 415205653334, 1460204395277, 1421257026061, 313112590979, 9067749566, 0, 0] := by
  rw [show D2M8K2.u3894 = KTree.node D2M8K2.u3892 (nat_lit 8761313) (nat_lit 2144228027) (nat_lit 0) D2M8K2.u3893 from rfl, totK_node, atot3892, atot3893]
  decide +kernel

theorem arows3901 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3901 = true := by
  rw [show D2M8K2.u3901 = KTree.node D2M8K2.u3899 (nat_lit 8764920) (nat_lit 2503690754) (nat_lit 0) D2M8K2.u3900 from rfl, allE_node, arows3899, irow3901, arows3900]
  all_goals rfl

theorem atot3901 : totK PD2M8K2 D2M8K2.u3901 = [0, 345393028417, 1421871316359, 1527740885142, 349286716598, 9178989717, 0, 0] := by
  rw [show D2M8K2.u3901 = KTree.node D2M8K2.u3899 (nat_lit 8764920) (nat_lit 2503690754) (nat_lit 0) D2M8K2.u3900 from rfl, totK_node, atot3899, atot3900]
  decide +kernel

theorem arows3904 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3904 = true := by
  rw [show D2M8K2.u3904 = KTree.node D2M8K2.u3902 (nat_lit 8768696) (nat_lit 3526428380) (nat_lit 0) D2M8K2.u3903 from rfl, allE_node, arows3902, irow3904, arows3903]
  all_goals rfl

theorem atot3904 : totK PD2M8K2 D2M8K2.u3904 = [0, 429025802250, 1516125021800, 1429526531299, 264071918666, 2678578463, 0, 0] := by
  rw [show D2M8K2.u3904 = KTree.node D2M8K2.u3902 (nat_lit 8768696) (nat_lit 3526428380) (nat_lit 0) D2M8K2.u3903 from rfl, totK_node, atot3902, atot3903]
  decide +kernel

theorem arows3908 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3908 = true := by
  rw [show D2M8K2.u3908 = KTree.node D2M8K2.u3906 (nat_lit 8792889) (nat_lit 1870966113) (nat_lit 0) D2M8K2.u3907 from rfl, allE_node, arows3906, irow3908, arows3907]
  all_goals rfl

theorem atot3908 : totK PD2M8K2 D2M8K2.u3908 = [0, 378680805110, 1353602272776, 1392350695659, 395894143339, 22050969863, 0, 0] := by
  rw [show D2M8K2.u3908 = KTree.node D2M8K2.u3906 (nat_lit 8792889) (nat_lit 1870966113) (nat_lit 0) D2M8K2.u3907 from rfl, totK_node, atot3906, atot3907]
  decide +kernel

theorem arows3911 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3911 = true := by
  rw [show D2M8K2.u3911 = KTree.node D2M8K2.u3909 (nat_lit 8796712) (nat_lit 3816739308) (nat_lit 0) D2M8K2.u3910 from rfl, allE_node, arows3909, irow3911, arows3910]
  all_goals rfl

theorem atot3911 : totK PD2M8K2 D2M8K2.u3911 = [0, 420651975616, 1479505817827, 1387100647020, 359610428879, 23329198674, 0, 0] := by
  rw [show D2M8K2.u3911 = KTree.node D2M8K2.u3909 (nat_lit 8796712) (nat_lit 3816739308) (nat_lit 0) D2M8K2.u3910 from rfl, totK_node, atot3909, atot3910]
  decide +kernel

theorem arows3916 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3916 = true := by
  rw [show D2M8K2.u3916 = KTree.node D2M8K2.u3914 (nat_lit 8799528) (nat_lit 2713296051) (nat_lit 0) D2M8K2.u3915 from rfl, allE_node, arows3914, irow3916, arows3915]
  all_goals rfl

theorem atot3916 : totK PD2M8K2 D2M8K2.u3916 = [0, 437858831585, 1422447946225, 1372640494316, 361609442134, 10599952761, 0, 0] := by
  rw [show D2M8K2.u3916 = KTree.node D2M8K2.u3914 (nat_lit 8799528) (nat_lit 2713296051) (nat_lit 0) D2M8K2.u3915 from rfl, totK_node, atot3914, atot3915]
  decide +kernel

theorem arows3919 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3919 = true := by
  rw [show D2M8K2.u3919 = KTree.node D2M8K2.u3917 (nat_lit 8806359) (nat_lit 2561003610) (nat_lit 0) D2M8K2.u3918 from rfl, allE_node, arows3917, irow3919, arows3918]
  all_goals rfl

theorem atot3919 : totK PD2M8K2 D2M8K2.u3919 = [0, 327009292805, 1405042614887, 1523724760801, 327315111223, 12948334120, 0, 0] := by
  rw [show D2M8K2.u3919 = KTree.node D2M8K2.u3917 (nat_lit 8806359) (nat_lit 2561003610) (nat_lit 0) D2M8K2.u3918 from rfl, totK_node, atot3917, atot3918]
  decide +kernel

theorem arows3923 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3923 = true := by
  rw [show D2M8K2.u3923 = KTree.node D2M8K2.u3921 (nat_lit 8810302) (nat_lit 3892752328) (nat_lit 0) D2M8K2.u3922 from rfl, allE_node, arows3921, irow3923, arows3922]
  all_goals rfl

theorem atot3923 : totK PD2M8K2 D2M8K2.u3923 = [0, 426024804024, 1453033367349, 1392822740753, 311011905351, 8688132302, 0, 0] := by
  rw [show D2M8K2.u3923 = KTree.node D2M8K2.u3921 (nat_lit 8810302) (nat_lit 3892752328) (nat_lit 0) D2M8K2.u3922 from rfl, totK_node, atot3921, atot3922]
  decide +kernel

theorem arows3926 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3926 = true := by
  rw [show D2M8K2.u3926 = KTree.node D2M8K2.u3924 (nat_lit 8813953) (nat_lit 1560988708) (nat_lit 0) D2M8K2.u3925 from rfl, allE_node, arows3924, irow3926, arows3925]
  all_goals rfl

theorem atot3926 : totK PD2M8K2 D2M8K2.u3926 = [0, 0, 525469998465, 1714944555859, 1134175374521, 106658459751, 1166720416, 0] := by
  rw [show D2M8K2.u3926 = KTree.node D2M8K2.u3924 (nat_lit 8813953) (nat_lit 1560988708) (nat_lit 0) D2M8K2.u3925 from rfl, totK_node, atot3924, atot3925]
  decide +kernel

theorem arows3932 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3932 = true := by
  rw [show D2M8K2.u3932 = KTree.node D2M8K2.u3930 (nat_lit 8819860) (nat_lit 3685469850) (nat_lit 0) D2M8K2.u3931 from rfl, allE_node, arows3930, irow3932, arows3931]
  all_goals rfl

theorem atot3932 : totK PD2M8K2 D2M8K2.u3932 = [0, 0, 823219063034, 1904899365205, 831735874735, 47991083874, 0, 0] := by
  rw [show D2M8K2.u3932 = KTree.node D2M8K2.u3930 (nat_lit 8819860) (nat_lit 3685469850) (nat_lit 0) D2M8K2.u3931 from rfl, totK_node, atot3930, atot3931]
  decide +kernel

theorem arows3935 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3935 = true := by
  rw [show D2M8K2.u3935 = KTree.node D2M8K2.u3933 (nat_lit 8826994) (nat_lit 2826364861) (nat_lit 0) D2M8K2.u3934 from rfl, allE_node, arows3933, irow3935, arows3934]
  all_goals rfl

theorem atot3935 : totK PD2M8K2 D2M8K2.u3935 = [0, 0, 545493906981, 1599626067471, 1136920332366, 189215040663, 5134755853, 0] := by
  rw [show D2M8K2.u3935 = KTree.node D2M8K2.u3933 (nat_lit 8826994) (nat_lit 2826364861) (nat_lit 0) D2M8K2.u3934 from rfl, totK_node, atot3933, atot3934]
  decide +kernel

theorem arows3939 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3939 = true := by
  rw [show D2M8K2.u3939 = KTree.node D2M8K2.u3937 (nat_lit 8834407) (nat_lit 2392624099) (nat_lit 0) D2M8K2.u3938 from rfl, allE_node, arows3937, irow3939, arows3938]
  all_goals rfl

theorem atot3939 : totK PD2M8K2 D2M8K2.u3939 = [0, 378777072195, 1335772865391, 1395852670196, 428765132169, 24288401412, 0, 0] := by
  rw [show D2M8K2.u3939 = KTree.node D2M8K2.u3937 (nat_lit 8834407) (nat_lit 2392624099) (nat_lit 0) D2M8K2.u3938 from rfl, totK_node, atot3937, atot3938]
  decide +kernel

theorem arows3942 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3942 = true := by
  rw [show D2M8K2.u3942 = KTree.node D2M8K2.u3940 (nat_lit 8838110) (nat_lit 2508595618) (nat_lit 0) D2M8K2.u3941 from rfl, allE_node, arows3940, irow3942, arows3941]
  all_goals rfl

theorem atot3942 : totK PD2M8K2 D2M8K2.u3942 = [0, 420723848593, 1497953049307, 1396910544119, 338471329669, 20729740161, 0, 0] := by
  rw [show D2M8K2.u3942 = KTree.node D2M8K2.u3940 (nat_lit 8838110) (nat_lit 2508595618) (nat_lit 0) D2M8K2.u3941 from rfl, totK_node, atot3940, atot3941]
  decide +kernel

theorem arows3947 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3947 = true := by
  rw [show D2M8K2.u3947 = KTree.node D2M8K2.u3945 (nat_lit 8844401) (nat_lit 1222613634) (nat_lit 0) D2M8K2.u3946 from rfl, allE_node, arows3945, irow3947, arows3946]
  all_goals rfl

theorem atot3947 : totK PD2M8K2 D2M8K2.u3947 = [0, 438053369152, 1408165243311, 1366558569607, 374635140183, 13273918566, 0, 0] := by
  rw [show D2M8K2.u3947 = KTree.node D2M8K2.u3945 (nat_lit 8844401) (nat_lit 1222613634) (nat_lit 0) D2M8K2.u3946 from rfl, totK_node, atot3945, atot3946]
  decide +kernel

theorem arows3950 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3950 = true := by
  rw [show D2M8K2.u3950 = KTree.node D2M8K2.u3948 (nat_lit 8847745) (nat_lit 1227719821) (nat_lit 0) D2M8K2.u3949 from rfl, allE_node, arows3948, irow3950, arows3949]
  all_goals rfl

theorem atot3950 : totK PD2M8K2 D2M8K2.u3950 = [0, 327149341145, 1403011002601, 1525820078205, 347257059997, 13088430220, 0, 0] := by
  rw [show D2M8K2.u3950 = KTree.node D2M8K2.u3948 (nat_lit 8847745) (nat_lit 1227719821) (nat_lit 0) D2M8K2.u3949 from rfl, totK_node, atot3948, atot3949]
  decide +kernel

theorem arows3954 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3954 = true := by
  rw [show D2M8K2.u3954 = KTree.node D2M8K2.u3952 (nat_lit 8851754) (nat_lit 4059456874) (nat_lit 0) D2M8K2.u3953 from rfl, allE_node, arows3952, irow3954, arows3953]
  all_goals rfl

theorem atot3954 : totK PD2M8K2 D2M8K2.u3954 = [0, 426073805952, 1458047637292, 1383931713261, 305447528608, 8720386020, 0, 0] := by
  rw [show D2M8K2.u3954 = KTree.node D2M8K2.u3952 (nat_lit 8851754) (nat_lit 4059456874) (nat_lit 0) D2M8K2.u3953 from rfl, totK_node, atot3952, atot3953]
  decide +kernel

theorem arows3957 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3957 = true := by
  rw [show D2M8K2.u3957 = KTree.node D2M8K2.u3955 (nat_lit 8855311) (nat_lit 2355418099) (nat_lit 0) D2M8K2.u3956 from rfl, allE_node, arows3955, irow3957, arows3956]
  all_goals rfl

theorem atot3957 : totK PD2M8K2 D2M8K2.u3957 = [0, 0, 542568059418, 1735412682238, 1106487297519, 101675231730, 1200365979, 0] := by
  rw [show D2M8K2.u3957 = KTree.node D2M8K2.u3955 (nat_lit 8855311) (nat_lit 2355418099) (nat_lit 0) D2M8K2.u3956 from rfl, totK_node, atot3955, atot3956]
  decide +kernel

theorem arows3965 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3965 = true := by
  rw [show D2M8K2.u3965 = KTree.node D2M8K2.u3963 (nat_lit 8864726) (nat_lit 3330076560) (nat_lit 0) D2M8K2.u3964 from rfl, allE_node, arows3963, irow3965, arows3964]
  all_goals rfl

theorem atot3965 : totK PD2M8K2 D2M8K2.u3965 = [0, 0, 843935992227, 1888169560121, 839537458581, 53539160227, 0, 0] := by
  rw [show D2M8K2.u3965 = KTree.node D2M8K2.u3963 (nat_lit 8864726) (nat_lit 3330076560) (nat_lit 0) D2M8K2.u3964 from rfl, totK_node, atot3963, atot3964]
  decide +kernel

theorem arows3968 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3968 = true := by
  rw [show D2M8K2.u3968 = KTree.node D2M8K2.u3966 (nat_lit 8868413) (nat_lit 1896103485) (nat_lit 0) D2M8K2.u3967 from rfl, allE_node, arows3966, irow3968, arows3967]
  all_goals rfl

theorem atot3968 : totK PD2M8K2 D2M8K2.u3968 = [0, 0, 561280972869, 1599322390151, 1138921353976, 190101340373, 5163565574, 0] := by
  rw [show D2M8K2.u3968 = KTree.node D2M8K2.u3966 (nat_lit 8868413) (nat_lit 1896103485) (nat_lit 0) D2M8K2.u3967 from rfl, totK_node, atot3966, atot3967]
  decide +kernel

theorem arows3972 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3972 = true := by
  rw [show D2M8K2.u3972 = KTree.node D2M8K2.u3970 (nat_lit 8917251) (nat_lit 2985317758) (nat_lit 0) D2M8K2.u3971 from rfl, allE_node, arows3970, irow3972, arows3971]
  all_goals rfl

theorem atot3972 : totK PD2M8K2 D2M8K2.u3972 = [0, 398387617587, 1353168746278, 1349361201168, 431883576491, 25252656972, 0, 0] := by
  rw [show D2M8K2.u3972 = KTree.node D2M8K2.u3970 (nat_lit 8917251) (nat_lit 2985317758) (nat_lit 0) D2M8K2.u3971 from rfl, totK_node, atot3970, atot3971]
  decide +kernel

theorem arows3975 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3975 = true := by
  rw [show D2M8K2.u3975 = KTree.node D2M8K2.u3973 (nat_lit 8920920) (nat_lit 3285150778) (nat_lit 0) D2M8K2.u3974 from rfl, allE_node, arows3973, irow3975, arows3974]
  all_goals rfl

theorem atot3975 : totK PD2M8K2 D2M8K2.u3975 = [0, 427581875239, 1519871265840, 1397145453483, 296554812524, 18724171075, 0, 0] := by
  rw [show D2M8K2.u3975 = KTree.node D2M8K2.u3973 (nat_lit 8920920) (nat_lit 3285150778) (nat_lit 0) D2M8K2.u3974 from rfl, totK_node, atot3973, atot3974]
  decide +kernel

theorem arows3980 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3980 = true := by
  rw [show D2M8K2.u3980 = KTree.node D2M8K2.u3978 (nat_lit 8923778) (nat_lit 4073527318) (nat_lit 0) D2M8K2.u3979 from rfl, allE_node, arows3978, irow3980, arows3979]
  all_goals rfl

theorem atot3980 : totK PD2M8K2 D2M8K2.u3980 = [0, 418848368139, 1401108284375, 1378020495516, 383598383299, 11683261214, 0, 0] := by
  rw [show D2M8K2.u3980 = KTree.node D2M8K2.u3978 (nat_lit 8923778) (nat_lit 4073527318) (nat_lit 0) D2M8K2.u3979 from rfl, totK_node, atot3978, atot3979]
  decide +kernel

theorem arows3983 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3983 = true := by
  rw [show D2M8K2.u3983 = KTree.node D2M8K2.u3981 (nat_lit 8927194) (nat_lit 3876619929) (nat_lit 0) D2M8K2.u3982 from rfl, allE_node, arows3981, irow3983, arows3982]
  all_goals rfl

theorem atot3983 : totK PD2M8K2 D2M8K2.u3983 = [0, 419081308228, 1471407431857, 1387347141791, 289172712581, 8557595888, 0, 0] := by
  rw [show D2M8K2.u3983 = KTree.node D2M8K2.u3981 (nat_lit 8927194) (nat_lit 3876619929) (nat_lit 0) D2M8K2.u3982 from rfl, totK_node, atot3981, atot3982]
  decide +kernel

theorem arows3987 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3987 = true := by
  rw [show D2M8K2.u3987 = KTree.node D2M8K2.u3985 (nat_lit 8934027) (nat_lit 2093087893) (nat_lit 0) D2M8K2.u3986 from rfl, allE_node, arows3985, irow3987, arows3986]
  all_goals rfl

theorem atot3987 : totK PD2M8K2 D2M8K2.u3987 = [0, 447505906754, 1483494322412, 1381018856387, 299006356710, 8656689423, 0, 0] := by
  rw [show D2M8K2.u3987 = KTree.node D2M8K2.u3985 (nat_lit 8934027) (nat_lit 2093087893) (nat_lit 0) D2M8K2.u3986 from rfl, totK_node, atot3985, atot3986]
  decide +kernel

theorem arows3990 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3990 = true := by
  rw [show D2M8K2.u3990 = KTree.node D2M8K2.u3988 (nat_lit 8937103) (nat_lit 1543099432) (nat_lit 0) D2M8K2.u3989 from rfl, allE_node, arows3988, irow3990, arows3989]
  all_goals rfl

theorem atot3990 : totK PD2M8K2 D2M8K2.u3990 = [0, 0, 833930383141, 1921328495937, 730452420327, 32369734999, 0, 0] := by
  rw [show D2M8K2.u3990 = KTree.node D2M8K2.u3988 (nat_lit 8937103) (nat_lit 1543099432) (nat_lit 0) D2M8K2.u3989 from rfl, totK_node, atot3988, atot3989]
  decide +kernel

theorem arows3996 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3996 = true := by
  rw [show D2M8K2.u3996 = KTree.node D2M8K2.u3994 (nat_lit 8941155) (nat_lit 3693876886) (nat_lit 0) D2M8K2.u3995 from rfl, allE_node, arows3994, irow3996, arows3995]
  all_goals rfl

theorem atot3996 : totK PD2M8K2 D2M8K2.u3996 = [0, 0, 522983727056, 1642650232047, 1242123729818, 152245501159, 1288491354, 0] := by
  rw [show D2M8K2.u3996 = KTree.node D2M8K2.u3994 (nat_lit 8941155) (nat_lit 3693876886) (nat_lit 0) D2M8K2.u3995 from rfl, totK_node, atot3994, atot3995]
  decide +kernel

theorem arows3999 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3999 = true := by
  rw [show D2M8K2.u3999 = KTree.node D2M8K2.u3997 (nat_lit 8945914) (nat_lit 3876295039) (nat_lit 0) D2M8K2.u3998 from rfl, allE_node, arows3997, irow3999, arows3998]
  all_goals rfl

theorem atot3999 : totK PD2M8K2 D2M8K2.u3999 = [0, 0, 480245004586, 1589855810351, 1216582647008, 187089949908, 4787054165, 0] := by
  rw [show D2M8K2.u3999 = KTree.node D2M8K2.u3997 (nat_lit 8945914) (nat_lit 3876295039) (nat_lit 0) D2M8K2.u3998 from rfl, totK_node, atot3997, atot3998]
  decide +kernel

theorem arows4003 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4003 = true := by
  rw [show D2M8K2.u4003 = KTree.node D2M8K2.u4001 (nat_lit 8949634) (nat_lit 4032359778) (nat_lit 0) D2M8K2.u4002 from rfl, allE_node, arows4001, irow4003, arows4002]
  all_goals rfl

theorem atot4003 : totK PD2M8K2 D2M8K2.u4003 = [0, 0, 456099113153, 1583757002302, 1270804296178, 204136886566, 4838243418, 0] := by
  rw [show D2M8K2.u4003 = KTree.node D2M8K2.u4001 (nat_lit 8949634) (nat_lit 4032359778) (nat_lit 0) D2M8K2.u4002 from rfl, totK_node, atot4001, atot4002]
  decide +kernel

theorem arows4006 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4006 = true := by
  rw [show D2M8K2.u4006 = KTree.node D2M8K2.u4004 (nat_lit 8956606) (nat_lit 3789605832) (nat_lit 0) D2M8K2.u4005 from rfl, allE_node, arows4004, irow4006, arows4005]
  all_goals rfl

theorem atot4006 : totK PD2M8K2 D2M8K2.u4006 = [0, 94445126902, 482402107600, 1237693163762, 1335345767073, 393076783371, 21751168066, 0] := by
  rw [show D2M8K2.u4006 = KTree.node D2M8K2.u4004 (nat_lit 8956606) (nat_lit 3789605832) (nat_lit 0) D2M8K2.u4005 from rfl, totK_node, atot4004, atot4005]
  decide +kernel

theorem arows4011 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4011 = true := by
  rw [show D2M8K2.u4011 = KTree.node D2M8K2.u4009 (nat_lit 9502600) (nat_lit 3843013936) (nat_lit 0) D2M8K2.u4010 from rfl, allE_node, arows4009, irow4011, arows4010]
  all_goals rfl

theorem atot4011 : totK PD2M8K2 D2M8K2.u4011 = [0, 355489735814, 1322356994407, 1463402147317, 496692871264, 30804453458, 0, 0] := by
  rw [show D2M8K2.u4011 = KTree.node D2M8K2.u4009 (nat_lit 9502600) (nat_lit 3843013936) (nat_lit 0) D2M8K2.u4010 from rfl, totK_node, atot4009, atot4010]
  decide +kernel

theorem arows4014 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4014 = true := by
  rw [show D2M8K2.u4014 = KTree.node D2M8K2.u4012 (nat_lit 9505301) (nat_lit 2194839152) (nat_lit 0) D2M8K2.u4013 from rfl, allE_node, arows4012, irow4014, arows4013]
  all_goals rfl

theorem atot4014 : totK PD2M8K2 D2M8K2.u4014 = [0, 422758666971, 1451695904616, 1397211827372, 349115985028, 14959134004, 0, 0] := by
  rw [show D2M8K2.u4014 = KTree.node D2M8K2.u4012 (nat_lit 9505301) (nat_lit 2194839152) (nat_lit 0) D2M8K2.u4013 from rfl, totK_node, atot4012, atot4013]
  decide +kernel

theorem arows4018 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4018 = true := by
  rw [show D2M8K2.u4018 = KTree.node D2M8K2.u4016 (nat_lit 9508673) (nat_lit 2183863956) (nat_lit 0) D2M8K2.u4017 from rfl, allE_node, arows4016, irow4018, arows4017]
  all_goals rfl

theorem atot4018 : totK PD2M8K2 D2M8K2.u4018 = [0, 422967451916, 1460107453090, 1406551790428, 324842792538, 11415143963, 0, 0] := by
  rw [show D2M8K2.u4018 = KTree.node D2M8K2.u4016 (nat_lit 9508673) (nat_lit 2183863956) (nat_lit 0) D2M8K2.u4017 from rfl, totK_node, atot4016, atot4017]
  decide +kernel

theorem arows4021 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4021 = true := by
  rw [show D2M8K2.u4021 = KTree.node D2M8K2.u4019 (nat_lit 9511786) (nat_lit 2894233951) (nat_lit 0) D2M8K2.u4020 from rfl, allE_node, arows4019, irow4021, arows4020]
  all_goals rfl

theorem atot4021 : totK PD2M8K2 D2M8K2.u4021 = [0, 420368875482, 1534703048723, 1418061955462, 245571794183, 3329039539, 0, 0] := by
  rw [show D2M8K2.u4021 = KTree.node D2M8K2.u4019 (nat_lit 9511786) (nat_lit 2894233951) (nat_lit 0) D2M8K2.u4020 from rfl, totK_node, atot4019, atot4020]
  decide +kernel

theorem arows4028 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4028 = true := by
  rw [show D2M8K2.u4028 = KTree.node D2M8K2.u4026 (nat_lit 9515317) (nat_lit 1234248106) (nat_lit 0) D2M8K2.u4027 from rfl, allE_node, arows4026, irow4028, arows4027]
  all_goals rfl

theorem atot4028 : totK PD2M8K2 D2M8K2.u4028 = [0, 425375799150, 1468184633715, 1416516378693, 317020022437, 7072536087, 0, 0] := by
  rw [show D2M8K2.u4028 = KTree.node D2M8K2.u4026 (nat_lit 9515317) (nat_lit 1234248106) (nat_lit 0) D2M8K2.u4027 from rfl, totK_node, atot4026, atot4027]
  decide +kernel

theorem arows4031 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4031 = true := by
  rw [show D2M8K2.u4031 = KTree.node D2M8K2.u4029 (nat_lit 9522179) (nat_lit 2836857101) (nat_lit 0) D2M8K2.u4030 from rfl, allE_node, arows4029, irow4031, arows4030]
  all_goals rfl

theorem atot4031 : totK PD2M8K2 D2M8K2.u4031 = [0, 0, 592605609214, 1690329263427, 1133368741743, 232216442813, 21385604922, 0] := by
  rw [show D2M8K2.u4031 = KTree.node D2M8K2.u4029 (nat_lit 9522179) (nat_lit 2836857101) (nat_lit 0) D2M8K2.u4030 from rfl, totK_node, atot4029, atot4030]
  decide +kernel

theorem arows4035 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4035 = true := by
  rw [show D2M8K2.u4035 = KTree.node D2M8K2.u4033 (nat_lit 9524982) (nat_lit 2423005538) (nat_lit 0) D2M8K2.u4034 from rfl, allE_node, arows4033, irow4035, arows4034]
  all_goals rfl

theorem atot4035 : totK PD2M8K2 D2M8K2.u4035 = [0, 0, 420835669942, 1386482999540, 1378933588487, 399219332985, 15536268932, 0] := by
  rw [show D2M8K2.u4035 = KTree.node D2M8K2.u4033 (nat_lit 9524982) (nat_lit 2423005538) (nat_lit 0) D2M8K2.u4034 from rfl, totK_node, atot4033, atot4034]
  decide +kernel

theorem arows4038 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4038 = true := by
  rw [show D2M8K2.u4038 = KTree.node D2M8K2.u4036 (nat_lit 9528536) (nat_lit 3579320266) (nat_lit 0) D2M8K2.u4037 from rfl, allE_node, arows4036, irow4038, arows4037]
  all_goals rfl

theorem atot4038 : totK PD2M8K2 D2M8K2.u4038 = [0, 0, 421050996521, 1533653436591, 1410745534230, 246215109241, 5159868635, 0] := by
  rw [show D2M8K2.u4038 = KTree.node D2M8K2.u4036 (nat_lit 9528536) (nat_lit 3579320266) (nat_lit 0) D2M8K2.u4037 from rfl, totK_node, atot4036, atot4037]
  decide +kernel

theorem arows4043 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4043 = true := by
  rw [show D2M8K2.u4043 = KTree.node D2M8K2.u4041 (nat_lit 9532040) (nat_lit 3911629605) (nat_lit 0) D2M8K2.u4042 from rfl, allE_node, arows4041, irow4043, arows4042]
  all_goals rfl

theorem atot4043 : totK PD2M8K2 D2M8K2.u4043 = [0, 0, 418468901935, 1525260331925, 1395587947431, 245225637451, 5218872685, 0] := by
  rw [show D2M8K2.u4043 = KTree.node D2M8K2.u4041 (nat_lit 9532040) (nat_lit 3911629605) (nat_lit 0) D2M8K2.u4042 from rfl, totK_node, atot4041, atot4042]
  decide +kernel

theorem arows4046 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4046 = true := by
  rw [show D2M8K2.u4046 = KTree.node D2M8K2.u4044 (nat_lit 9535659) (nat_lit 3677724410) (nat_lit 0) D2M8K2.u4045 from rfl, allE_node, arows4044, irow4046, arows4045]
  all_goals rfl

theorem atot4046 : totK PD2M8K2 D2M8K2.u4046 = [0, 0, 423405147215, 1603490986127, 1428735149222, 202353506871, 1415142070, 0] := by
  rw [show D2M8K2.u4046 = KTree.node D2M8K2.u4044 (nat_lit 9535659) (nat_lit 3677724410) (nat_lit 0) D2M8K2.u4045 from rfl, totK_node, atot4044, atot4045]
  decide +kernel

theorem arows4050 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4050 = true := by
  rw [show D2M8K2.u4050 = KTree.node D2M8K2.u4048 (nat_lit 9539380) (nat_lit 3800660397) (nat_lit 0) D2M8K2.u4049 from rfl, allE_node, arows4048, irow4050, arows4049]
  all_goals rfl

theorem atot4050 : totK PD2M8K2 D2M8K2.u4050 = [0, 342837074947, 1166395571019, 1131741073287, 691242033310, 241940454824, 9302370699, 0] := by
  rw [show D2M8K2.u4050 = KTree.node D2M8K2.u4048 (nat_lit 9539380) (nat_lit 3800660397) (nat_lit 0) D2M8K2.u4049 from rfl, totK_node, atot4048, atot4049]
  decide +kernel

theorem arows4053 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4053 = true := by
  rw [show D2M8K2.u4053 = KTree.node D2M8K2.u4051 (nat_lit 9543520) (nat_lit 3741127726) (nat_lit 0) D2M8K2.u4052 from rfl, allE_node, arows4051, irow4053, arows4052]
  all_goals rfl

theorem atot4053 : totK PD2M8K2 D2M8K2.u4053 = [0, 411028237841, 1414473417328, 1373974216835, 433982041062, 29387185185, 0, 0] := by
  rw [show D2M8K2.u4053 = KTree.node D2M8K2.u4051 (nat_lit 9543520) (nat_lit 3741127726) (nat_lit 0) D2M8K2.u4052 from rfl, totK_node, atot4051, atot4052]
  decide +kernel

theorem arows4059 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4059 = true := by
  rw [show D2M8K2.u4059 = KTree.node D2M8K2.u4057 (nat_lit 9546226) (nat_lit 3952474794) (nat_lit 0) D2M8K2.u4058 from rfl, allE_node, arows4057, irow4059, arows4058]
  all_goals rfl

theorem atot4059 : totK PD2M8K2 D2M8K2.u4059 = [0, 440101113843, 1480647057907, 1393667788185, 324676525675, 9374251252, 0, 0] := by
  rw [show D2M8K2.u4059 = KTree.node D2M8K2.u4057 (nat_lit 9546226) (nat_lit 3952474794) (nat_lit 0) D2M8K2.u4058 from rfl, totK_node, atot4057, atot4058]
  decide +kernel

theorem arows4062 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4062 = true := by
  rw [show D2M8K2.u4062 = KTree.node D2M8K2.u4060 (nat_lit 9553006) (nat_lit 3678637694) (nat_lit 0) D2M8K2.u4061 from rfl, allE_node, arows4060, irow4062, arows4061]
  all_goals rfl

theorem atot4062 : totK PD2M8K2 D2M8K2.u4062 = [0, 410693717374, 1448082142381, 1408336285251, 310066365132, 12981912718, 0, 0] := by
  rw [show D2M8K2.u4062 = KTree.node D2M8K2.u4060 (nat_lit 9553006) (nat_lit 3678637694) (nat_lit 0) D2M8K2.u4061 from rfl, totK_node, atot4060, atot4061]
  decide +kernel

theorem arows4066 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4066 = true := by
  rw [show D2M8K2.u4066 = KTree.node D2M8K2.u4064 (nat_lit 9556567) (nat_lit 1068513656) (nat_lit 0) D2M8K2.u4065 from rfl, allE_node, arows4064, irow4066, arows4065]
  all_goals rfl

theorem atot4066 : totK PD2M8K2 D2M8K2.u4066 = [0, 416299879234, 1514098945823, 1435289359384, 270510567981, 5152749158, 0, 0] := by
  rw [show D2M8K2.u4066 = KTree.node D2M8K2.u4064 (nat_lit 9556567) (nat_lit 1068513656) (nat_lit 0) D2M8K2.u4065 from rfl, totK_node, atot4064, atot4065]
  decide +kernel

theorem arows4069 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4069 = true := by
  rw [show D2M8K2.u4069 = KTree.node D2M8K2.u4067 (nat_lit 9560479) (nat_lit 1453028766) (nat_lit 0) D2M8K2.u4068 from rfl, allE_node, arows4067, irow4069, arows4068]
  all_goals rfl

theorem atot4069 : totK PD2M8K2 D2M8K2.u4069 = [0, 0, 575239963792, 1762802303472, 1119722981116, 86578439668, 0, 0] := by
  rw [show D2M8K2.u4069 = KTree.node D2M8K2.u4067 (nat_lit 9560479) (nat_lit 1453028766) (nat_lit 0) D2M8K2.u4068 from rfl, totK_node, atot4067, atot4068]
  decide +kernel

theorem arows4074 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4074 = true := by
  rw [show D2M8K2.u4074 = KTree.node D2M8K2.u4072 (nat_lit 9564409) (nat_lit 1101971243) (nat_lit 0) D2M8K2.u4073 from rfl, allE_node, arows4072, irow4074, arows4073]
  all_goals rfl

theorem atot4074 : totK PD2M8K2 D2M8K2.u4074 = [0, 0, 694292325688, 1867077334059, 1000223086539, 75665412684, 0, 0] := by
  rw [show D2M8K2.u4074 = KTree.node D2M8K2.u4072 (nat_lit 9564409) (nat_lit 1101971243) (nat_lit 0) D2M8K2.u4073 from rfl, totK_node, atot4072, atot4073]
  decide +kernel

theorem arows4077 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4077 = true := by
  rw [show D2M8K2.u4077 = KTree.node D2M8K2.u4075 (nat_lit 9569377) (nat_lit 1530712526) (nat_lit 0) D2M8K2.u4076 from rfl, allE_node, arows4075, irow4077, arows4076]
  all_goals rfl

theorem atot4077 : totK PD2M8K2 D2M8K2.u4077 = [0, 0, 413678911827, 1489502377474, 1348576959546, 283029306761, 9072174562, 0] := by
  rw [show D2M8K2.u4077 = KTree.node D2M8K2.u4075 (nat_lit 9569377) (nat_lit 1530712526) (nat_lit 0) D2M8K2.u4076 from rfl, totK_node, atot4075, atot4076]
  decide +kernel

theorem arows4081 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4081 = true := by
  rw [show D2M8K2.u4081 = KTree.node D2M8K2.u4079 (nat_lit 9576702) (nat_lit 3619773953) (nat_lit 0) D2M8K2.u4080 from rfl, allE_node, arows4079, irow4081, arows4080]
  all_goals rfl

theorem atot4081 : totK PD2M8K2 D2M8K2.u4081 = [0, 0, 484731039470, 1634128596711, 1276317409699, 164222056405, 2340352732, 0] := by
  rw [show D2M8K2.u4081 = KTree.node D2M8K2.u4079 (nat_lit 9576702) (nat_lit 3619773953) (nat_lit 0) D2M8K2.u4080 from rfl, totK_node, atot4079, atot4080]
  decide +kernel

theorem arows4084 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4084 = true := by
  rw [show D2M8K2.u4084 = KTree.node D2M8K2.u4082 (nat_lit 9581870) (nat_lit 2327024492) (nat_lit 0) D2M8K2.u4083 from rfl, allE_node, arows4082, irow4084, arows4083]
  all_goals rfl

theorem atot4084 : totK PD2M8K2 D2M8K2.u4084 = [0, 564060001896, 1689957710063, 1218983746615, 163218430452, 9433566158, 0, 0] := by
  rw [show D2M8K2.u4084 = KTree.node D2M8K2.u4082 (nat_lit 9581870) (nat_lit 2327024492) (nat_lit 0) D2M8K2.u4083 from rfl, totK_node, atot4082, atot4083]
  decide +kernel

theorem arows4097 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4097 = true := by
  rw [show D2M8K2.u4097 = KTree.node D2M8K2.u4095 (nat_lit 9585926) (nat_lit 3973936901) (nat_lit 0) D2M8K2.u4096 from rfl, allE_node, arows4095, irow4097, arows4096]
  all_goals rfl

theorem atot4097 : totK PD2M8K2 D2M8K2.u4097 = [0, 291452684444, 1214724627609, 1503602403342, 581366534413, 37595089999, 0, 0] := by
  rw [show D2M8K2.u4097 = KTree.node D2M8K2.u4095 (nat_lit 9585926) (nat_lit 3973936901) (nat_lit 0) D2M8K2.u4096 from rfl, totK_node, atot4095, atot4096]
  decide +kernel

theorem arows4100 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4100 = true := by
  rw [show D2M8K2.u4100 = KTree.node D2M8K2.u4098 (nat_lit 9592139) (nat_lit 2884303107) (nat_lit 0) D2M8K2.u4099 from rfl, allE_node, arows4098, irow4100, arows4099]
  all_goals rfl

theorem atot4100 : totK PD2M8K2 D2M8K2.u4100 = [0, 389508512909, 1415092492298, 1462227851051, 348528271158, 13250685261, 0, 0] := by
  rw [show D2M8K2.u4100 = KTree.node D2M8K2.u4098 (nat_lit 9592139) (nat_lit 2884303107) (nat_lit 0) D2M8K2.u4099 from rfl, totK_node, atot4098, atot4099]
  decide +kernel

theorem arows4104 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4104 = true := by
  rw [show D2M8K2.u4104 = KTree.node D2M8K2.u4102 (nat_lit 9595187) (nat_lit 1959436237) (nat_lit 0) D2M8K2.u4103 from rfl, allE_node, arows4102, irow4104, arows4103]
  all_goals rfl

theorem atot4104 : totK PD2M8K2 D2M8K2.u4104 = [0, 433836096607, 1547297865770, 1385986138881, 235599298624, 4980514959, 0, 0] := by
  rw [show D2M8K2.u4104 = KTree.node D2M8K2.u4102 (nat_lit 9595187) (nat_lit 1959436237) (nat_lit 0) D2M8K2.u4103 from rfl, totK_node, atot4102, atot4103]
  decide +kernel

theorem arows4107 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4107 = true := by
  rw [show D2M8K2.u4107 = KTree.node D2M8K2.u4105 (nat_lit 9599049) (nat_lit 1427288554) (nat_lit 0) D2M8K2.u4106 from rfl, allE_node, arows4105, irow4107, arows4106]
  all_goals rfl

theorem atot4107 : totK PD2M8K2 D2M8K2.u4107 = [0, 339347743896, 1335552307799, 1500990560814, 434730059177, 20539705592, 0, 0] := by
  rw [show D2M8K2.u4107 = KTree.node D2M8K2.u4105 (nat_lit 9599049) (nat_lit 1427288554) (nat_lit 0) D2M8K2.u4106 from rfl, totK_node, atot4105, atot4106]
  decide +kernel

theorem arows4112 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4112 = true := by
  rw [show D2M8K2.u4112 = KTree.node D2M8K2.u4110 (nat_lit 9603403) (nat_lit 1696342550) (nat_lit 0) D2M8K2.u4111 from rfl, allE_node, arows4110, irow4112, arows4111]
  all_goals rfl

theorem atot4112 : totK PD2M8K2 D2M8K2.u4112 = [0, 0, 559079047443, 1765853446427, 1184671134854, 98124047450, 0, 0] := by
  rw [show D2M8K2.u4112 = KTree.node D2M8K2.u4110 (nat_lit 9603403) (nat_lit 1696342550) (nat_lit 0) D2M8K2.u4111 from rfl, totK_node, atot4110, atot4111]
  decide +kernel

theorem arows4115 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4115 = true := by
  rw [show D2M8K2.u4115 = KTree.node D2M8K2.u4113 (nat_lit 9612029) (nat_lit 1654391751) (nat_lit 0) D2M8K2.u4114 from rfl, allE_node, arows4113, irow4115, arows4114]
  all_goals rfl

theorem atot4115 : totK PD2M8K2 D2M8K2.u4115 = [0, 0, 612835499091, 1749618753252, 1131534382077, 116753326066, 0, 0] := by
  rw [show D2M8K2.u4115 = KTree.node D2M8K2.u4113 (nat_lit 9612029) (nat_lit 1654391751) (nat_lit 0) D2M8K2.u4114 from rfl, totK_node, atot4113, atot4114]
  decide +kernel

theorem arows4119 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4119 = true := by
  rw [show D2M8K2.u4119 = KTree.node D2M8K2.u4117 (nat_lit 9615134) (nat_lit 3646320528) (nat_lit 0) D2M8K2.u4118 from rfl, allE_node, arows4117, irow4119, arows4118]
  all_goals rfl

theorem atot4119 : totK PD2M8K2 D2M8K2.u4119 = [0, 0, 409689114949, 1510190295304, 1352397763078, 261936341904, 9135329004, 0] := by
  rw [show D2M8K2.u4119 = KTree.node D2M8K2.u4117 (nat_lit 9615134) (nat_lit 3646320528) (nat_lit 0) D2M8K2.u4118 from rfl, totK_node, atot4117, atot4118]
  decide +kernel

theorem arows4122 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4122 = true := by
  rw [show D2M8K2.u4122 = KTree.node D2M8K2.u4120 (nat_lit 9618828) (nat_lit 2681527080) (nat_lit 0) D2M8K2.u4121 from rfl, allE_node, arows4120, irow4122, arows4121]
  all_goals rfl

theorem atot4122 : totK PD2M8K2 D2M8K2.u4122 = [0, 190813401391, 857089812312, 1437597801968, 949533553272, 137309982014, 2417524611, 0] := by
  rw [show D2M8K2.u4122 = KTree.node D2M8K2.u4120 (nat_lit 9618828) (nat_lit 2681527080) (nat_lit 0) D2M8K2.u4121 from rfl, totK_node, atot4120, atot4121]
  decide +kernel

theorem arows4128 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4128 = true := by
  rw [show D2M8K2.u4128 = KTree.node D2M8K2.u4126 (nat_lit 9625370) (nat_lit 4144112085) (nat_lit 0) D2M8K2.u4127 from rfl, allE_node, arows4126, irow4128, arows4127]
  all_goals rfl

theorem atot4128 : totK PD2M8K2 D2M8K2.u4128 = [0, 557007216230, 1741543368241, 1232956073515, 115489666953, 0, 0, 0] := by
  rw [show D2M8K2.u4128 = KTree.node D2M8K2.u4126 (nat_lit 9625370) (nat_lit 4144112085) (nat_lit 0) D2M8K2.u4127 from rfl, totK_node, atot4126, atot4127]
  decide +kernel

theorem arows4131 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4131 = true := by
  rw [show D2M8K2.u4131 = KTree.node D2M8K2.u4129 (nat_lit 9628043) (nat_lit 1212015319) (nat_lit 0) D2M8K2.u4130 from rfl, allE_node, arows4129, irow4131, arows4130]
  all_goals rfl

theorem atot4131 : totK PD2M8K2 D2M8K2.u4131 = [0, 280872432327, 1171954663655, 1532750988639, 601473400107, 37601708222, 0, 0] := by
  rw [show D2M8K2.u4131 = KTree.node D2M8K2.u4129 (nat_lit 9628043) (nat_lit 1212015319) (nat_lit 0) D2M8K2.u4130 from rfl, totK_node, atot4129, atot4130]
  decide +kernel

theorem arows4135 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4135 = true := by
  rw [show D2M8K2.u4135 = KTree.node D2M8K2.u4133 (nat_lit 9631335) (nat_lit 2436066882) (nat_lit 0) D2M8K2.u4134 from rfl, allE_node, arows4133, irow4135, arows4134]
  all_goals rfl

theorem atot4135 : totK PD2M8K2 D2M8K2.u4135 = [0, 387788258269, 1435018627238, 1438983798387, 324066395845, 13049727234, 0, 0] := by
  rw [show D2M8K2.u4135 = KTree.node D2M8K2.u4133 (nat_lit 9631335) (nat_lit 2436066882) (nat_lit 0) D2M8K2.u4134 from rfl, totK_node, atot4133, atot4134]
  decide +kernel

theorem arows4138 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4138 = true := by
  rw [show D2M8K2.u4138 = KTree.node D2M8K2.u4136 (nat_lit 9634758) (nat_lit 3738511779) (nat_lit 0) D2M8K2.u4137 from rfl, allE_node, arows4136, irow4138, arows4137]
  all_goals rfl

theorem atot4138 : totK PD2M8K2 D2M8K2.u4138 = [0, 410999848228, 1439386887908, 1410665252835, 333660971180, 13250685261, 0, 0] := by
  rw [show D2M8K2.u4138 = KTree.node D2M8K2.u4136 (nat_lit 9634758) (nat_lit 3738511779) (nat_lit 0) D2M8K2.u4137 from rfl, totK_node, atot4136, atot4137]
  decide +kernel

theorem arows4143 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4143 = true := by
  rw [show D2M8K2.u4143 = KTree.node D2M8K2.u4141 (nat_lit 9637951) (nat_lit 2364330830) (nat_lit 0) D2M8K2.u4142 from rfl, allE_node, arows4141, irow4143, arows4142]
  all_goals rfl

theorem atot4143 : totK PD2M8K2 D2M8K2.u4143 = [0, 180183318095, 1182284635483, 1706516287385, 486205816417, 23242077755, 0, 0] := by
  rw [show D2M8K2.u4143 = KTree.node D2M8K2.u4141 (nat_lit 9637951) (nat_lit 2364330830) (nat_lit 0) D2M8K2.u4142 from rfl, totK_node, atot4141, atot4142]
  decide +kernel

theorem arows4146 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4146 = true := by
  rw [show D2M8K2.u4146 = KTree.node D2M8K2.u4144 (nat_lit 9646373) (nat_lit 2338578389) (nat_lit 0) D2M8K2.u4145 from rfl, allE_node, arows4144, irow4146, arows4145]
  all_goals rfl

theorem atot4146 : totK PD2M8K2 D2M8K2.u4146 = [0, 0, 563897782552, 1779893370832, 1137923015853, 94172051572, 0, 0] := by
  rw [show D2M8K2.u4146 = KTree.node D2M8K2.u4144 (nat_lit 9646373) (nat_lit 2338578389) (nat_lit 0) D2M8K2.u4145 from rfl, totK_node, atot4144, atot4145]
  decide +kernel

theorem arows4150 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4150 = true := by
  rw [show D2M8K2.u4150 = KTree.node D2M8K2.u4148 (nat_lit 9652717) (nat_lit 1132023364) (nat_lit 0) D2M8K2.u4149 from rfl, allE_node, arows4148, irow4150, arows4149]
  all_goals rfl

theorem atot4150 : totK PD2M8K2 D2M8K2.u4150 = [0, 0, 748852033560, 1901297637317, 929070457101, 50449093447, 0, 0] := by
  rw [show D2M8K2.u4150 = KTree.node D2M8K2.u4148 (nat_lit 9652717) (nat_lit 1132023364) (nat_lit 0) D2M8K2.u4149 from rfl, totK_node, atot4148, atot4149]
  decide +kernel

theorem arows4153 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4153 = true := by
  rw [show D2M8K2.u4153 = KTree.node D2M8K2.u4151 (nat_lit 9657251) (nat_lit 2156135194) (nat_lit 0) D2M8K2.u4152 from rfl, allE_node, arows4151, irow4153, arows4152]
  all_goals rfl

theorem atot4153 : totK PD2M8K2 D2M8K2.u4153 = [0, 28842453189, 470978626800, 1551792480944, 1285253695523, 209319453336, 2586295899, 0] := by
  rw [show D2M8K2.u4153 = KTree.node D2M8K2.u4151 (nat_lit 9657251) (nat_lit 2156135194) (nat_lit 0) D2M8K2.u4152 from rfl, totK_node, atot4151, atot4152]
  decide +kernel

theorem arows4160 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4160 = true := by
  rw [show D2M8K2.u4160 = KTree.node D2M8K2.u4158 (nat_lit 9665315) (nat_lit 2696684986) (nat_lit 0) D2M8K2.u4159 from rfl, allE_node, arows4158, irow4160, arows4159]
  all_goals rfl

theorem atot4160 : totK PD2M8K2 D2M8K2.u4160 = [0, 561480071873, 1729610537499, 1248046730337, 123562718717, 0, 0, 0] := by
  rw [show D2M8K2.u4160 = KTree.node D2M8K2.u4158 (nat_lit 9665315) (nat_lit 2696684986) (nat_lit 0) D2M8K2.u4159 from rfl, totK_node, atot4158, atot4159]
  decide +kernel

theorem arows4163 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4163 = true := by
  rw [show D2M8K2.u4163 = KTree.node D2M8K2.u4161 (nat_lit 9668938) (nat_lit 3843903152) (nat_lit 0) D2M8K2.u4162 from rfl, allE_node, arows4161, irow4163, arows4162]
  all_goals rfl

theorem atot4163 : totK PD2M8K2 D2M8K2.u4163 = [0, 309708381095, 1225469401590, 1491643777065, 578122683498, 37589446790, 0, 0] := by
  rw [show D2M8K2.u4163 = KTree.node D2M8K2.u4161 (nat_lit 9668938) (nat_lit 3843903152) (nat_lit 0) D2M8K2.u4162 from rfl, totK_node, atot4161, atot4162]
  decide +kernel

theorem arows4167 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4167 = true := by
  rw [show D2M8K2.u4167 = KTree.node D2M8K2.u4165 (nat_lit 9671810) (nat_lit 3142446578) (nat_lit 0) D2M8K2.u4166 from rfl, allE_node, arows4165, irow4167, arows4166]
  all_goals rfl

theorem atot4167 : totK PD2M8K2 D2M8K2.u4167 = [0, 397643612323, 1446977672732, 1440055800696, 323238183989, 11615371903, 0, 0] := by
  rw [show D2M8K2.u4167 = KTree.node D2M8K2.u4165 (nat_lit 9671810) (nat_lit 3142446578) (nat_lit 0) D2M8K2.u4166 from rfl, totK_node, atot4165, atot4166]
  decide +kernel

theorem arows4170 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4170 = true := by
  rw [show D2M8K2.u4170 = KTree.node D2M8K2.u4168 (nat_lit 9675220) (nat_lit 2415911877) (nat_lit 0) D2M8K2.u4169 from rfl, allE_node, arows4168, irow4170, arows4169]
  all_goals rfl

theorem atot4170 : totK PD2M8K2 D2M8K2.u4170 = [0, 386569390529, 1447660033907, 1447072603259, 332966224118, 11775199386, 0, 0] := by
  rw [show D2M8K2.u4170 = KTree.node D2M8K2.u4168 (nat_lit 9675220) (nat_lit 2415911877) (nat_lit 0) D2M8K2.u4169 from rfl, totK_node, atot4168, atot4169]
  decide +kernel

theorem arows4175 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4175 = true := by
  rw [show D2M8K2.u4175 = KTree.node D2M8K2.u4173 (nat_lit 9681995) (nat_lit 2924946698) (nat_lit 0) D2M8K2.u4174 from rfl, allE_node, arows4173, irow4175, arows4174]
  all_goals rfl

theorem atot4175 : totK PD2M8K2 D2M8K2.u4175 = [0, 340088530745, 1333118608767, 1533095328363, 415506411767, 12440031250, 0, 0] := by
  rw [show D2M8K2.u4175 = KTree.node D2M8K2.u4173 (nat_lit 9681995) (nat_lit 2924946698) (nat_lit 0) D2M8K2.u4174 from rfl, totK_node, atot4173, atot4174]
  decide +kernel

theorem arows4178 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4178 = true := by
  rw [show D2M8K2.u4178 = KTree.node D2M8K2.u4176 (nat_lit 9685570) (nat_lit 4111819535) (nat_lit 0) D2M8K2.u4177 from rfl, allE_node, arows4176, irow4178, arows4177]
  all_goals rfl

theorem atot4178 : totK PD2M8K2 D2M8K2.u4178 = [0, 0, 571900960432, 1734009401079, 1222104801517, 105769342231, 0, 0] := by
  rw [show D2M8K2.u4178 = KTree.node D2M8K2.u4176 (nat_lit 9685570) (nat_lit 4111819535) (nat_lit 0) D2M8K2.u4177 from rfl, totK_node, atot4176, atot4177]
  decide +kernel

theorem arows4182 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4182 = true := by
  rw [show D2M8K2.u4182 = KTree.node D2M8K2.u4180 (nat_lit 9691168) (nat_lit 3284103137) (nat_lit 0) D2M8K2.u4181 from rfl, allE_node, arows4180, irow4182, arows4181]
  all_goals rfl

theorem atot4182 : totK PD2M8K2 D2M8K2.u4182 = [0, 0, 593789729967, 1766115610761, 1165585897939, 106865885802, 0, 0] := by
  rw [show D2M8K2.u4182 = KTree.node D2M8K2.u4180 (nat_lit 9691168) (nat_lit 3284103137) (nat_lit 0) D2M8K2.u4181 from rfl, totK_node, atot4180, atot4181]
  decide +kernel

theorem arows4185 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4185 = true := by
  rw [show D2M8K2.u4185 = KTree.node D2M8K2.u4183 (nat_lit 9695066) (nat_lit 4032636964) (nat_lit 0) D2M8K2.u4184 from rfl, allE_node, arows4183, irow4185, arows4184]
  all_goals rfl

theorem atot4185 : totK PD2M8K2 D2M8K2.u4185 = [0, 0, 413154659573, 1526219694039, 1410697419476, 227647092201, 2516941024, 0] := by
  rw [show D2M8K2.u4185 = KTree.node D2M8K2.u4183 (nat_lit 9695066) (nat_lit 4032636964) (nat_lit 0) D2M8K2.u4184 from rfl, totK_node, atot4183, atot4184]
  decide +kernel

theorem arows4191 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4191 = true := by
  rw [show D2M8K2.u4191 = KTree.node D2M8K2.u4189 (nat_lit 9701874) (nat_lit 3433520064) (nat_lit 0) D2M8K2.u4190 from rfl, allE_node, arows4189, irow4191, arows4190]
  all_goals rfl

theorem atot4191 : totK PD2M8K2 D2M8K2.u4191 = [0, 0, 440772061826, 1533057744647, 1371524643482, 244108028939, 4880406129, 0] := by
  rw [show D2M8K2.u4191 = KTree.node D2M8K2.u4189 (nat_lit 9701874) (nat_lit 3433520064) (nat_lit 0) D2M8K2.u4190 from rfl, totK_node, atot4189, atot4190]
  decide +kernel

theorem arows4194 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4194 = true := by
  rw [show D2M8K2.u4194 = KTree.node D2M8K2.u4192 (nat_lit 9750226) (nat_lit 4089981287) (nat_lit 0) D2M8K2.u4193 from rfl, allE_node, arows4192, irow4194, arows4193]
  all_goals rfl

theorem atot4194 : totK PD2M8K2 D2M8K2.u4194 = [0, 0, 449934862716, 1425856967895, 1325463111567, 421233953064, 30951200104, 0] := by
  rw [show D2M8K2.u4194 = KTree.node D2M8K2.u4192 (nat_lit 9750226) (nat_lit 4089981287) (nat_lit 0) D2M8K2.u4193 from rfl, totK_node, atot4192, atot4193]
  decide +kernel

theorem arows4198 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4198 = true := by
  rw [show D2M8K2.u4198 = KTree.node D2M8K2.u4196 (nat_lit 9752958) (nat_lit 3054023083) (nat_lit 0) D2M8K2.u4197 from rfl, allE_node, arows4196, irow4198, arows4197]
  all_goals rfl

theorem atot4198 : totK PD2M8K2 D2M8K2.u4198 = [0, 0, 422758666971, 1378918774107, 1376690698867, 435056401721, 19311493318, 0] := by
  rw [show D2M8K2.u4198 = KTree.node D2M8K2.u4196 (nat_lit 9752958) (nat_lit 3054023083) (nat_lit 0) D2M8K2.u4197 from rfl, totK_node, atot4196, atot4197]
  decide +kernel

theorem arows4201 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4201 = true := by
  rw [show D2M8K2.u4201 = KTree.node D2M8K2.u4199 (nat_lit 9756379) (nat_lit 2241137686) (nat_lit 0) D2M8K2.u4200 from rfl, allE_node, arows4199, irow4201, arows4200]
  all_goals rfl

theorem atot4201 : totK PD2M8K2 D2M8K2.u4201 = [0, 0, 422967451916, 1462465584415, 1410101490410, 306896545585, 8706415949, 0] := by
  rw [show D2M8K2.u4201 = KTree.node D2M8K2.u4199 (nat_lit 9756379) (nat_lit 2241137686) (nat_lit 0) D2M8K2.u4200 from rfl, totK_node, atot4199, atot4200]
  decide +kernel

theorem arows4206 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4206 = true := by
  rw [show D2M8K2.u4206 = KTree.node D2M8K2.u4204 (nat_lit 9759590) (nat_lit 3977316729) (nat_lit 0) D2M8K2.u4205 from rfl, allE_node, arows4204, irow4206, arows4205]
  all_goals rfl

theorem atot4206 : totK PD2M8K2 D2M8K2.u4206 = [0, 0, 382863451800, 1430127311235, 1449008416530, 321950924353, 8824320960, 0] := by
  rw [show D2M8K2.u4206 = KTree.node D2M8K2.u4204 (nat_lit 9759590) (nat_lit 3977316729) (nat_lit 0) D2M8K2.u4205 from rfl, totK_node, atot4204, atot4205]
  decide +kernel

theorem arows4209 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4209 = true := by
  rw [show D2M8K2.u4209 = KTree.node D2M8K2.u4207 (nat_lit 9763320) (nat_lit 3456630115) (nat_lit 0) D2M8K2.u4208 from rfl, allE_node, arows4207, irow4209, arows4208]
  all_goals rfl

theorem atot4209 : totK PD2M8K2 D2M8K2.u4209 = [0, 0, 462881222832, 1581794291111, 1360928966417, 221644640203, 2498823382, 0] := by
  rw [show D2M8K2.u4209 = KTree.node D2M8K2.u4207 (nat_lit 9763320) (nat_lit 3456630115) (nat_lit 0) D2M8K2.u4208 from rfl, totK_node, atot4207, atot4208]
  decide +kernel

theorem arows4213 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4213 = true := by
  rw [show D2M8K2.u4213 = KTree.node D2M8K2.u4211 (nat_lit 9766523) (nat_lit 2876038074) (nat_lit 0) D2M8K2.u4212 from rfl, allE_node, arows4211, irow4213, arows4212]
  all_goals rfl

theorem atot4213 : totK PD2M8K2 D2M8K2.u4213 = [0, 0, 0, 854898749075, 1904736639481, 803431575224, 50520574951, 0] := by
  rw [show D2M8K2.u4213 = KTree.node D2M8K2.u4211 (nat_lit 9766523) (nat_lit 2876038074) (nat_lit 0) D2M8K2.u4212 from rfl, totK_node, atot4211, atot4212]
  decide +kernel

theorem arows4216 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4216 = true := by
  rw [show D2M8K2.u4216 = KTree.node D2M8K2.u4214 (nat_lit 9772920) (nat_lit 2752544041) (nat_lit 0) D2M8K2.u4215 from rfl, allE_node, arows4214, irow4216, arows4215]
  all_goals rfl

theorem atot4216 : totK PD2M8K2 D2M8K2.u4216 = [0, 0, 0, 294809261477, 1188730557952, 1516703574218, 564181292265, 36921873854] := by
  rw [show D2M8K2.u4216 = KTree.node D2M8K2.u4214 (nat_lit 9772920) (nat_lit 2752544041) (nat_lit 0) D2M8K2.u4215 from rfl, totK_node, atot4214, atot4215]
  decide +kernel

theorem arows4224 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4224 = true := by
  rw [show D2M8K2.u4224 = KTree.node D2M8K2.u4222 (nat_lit 9776025) (nat_lit 1162960339) (nat_lit 0) D2M8K2.u4223 from rfl, allE_node, arows4222, irow4224, arows4223]
  all_goals rfl

theorem atot4224 : totK PD2M8K2 D2M8K2.u4224 = [0, 0, 0, 453815421768, 1551062140349, 1329858909355, 219074024456, 5067863418] := by
  rw [show D2M8K2.u4224 = KTree.node D2M8K2.u4222 (nat_lit 9776025) (nat_lit 1162960339) (nat_lit 0) D2M8K2.u4223 from rfl, totK_node, atot4222, atot4223]
  decide +kernel

theorem arows4227 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4227 = true := by
  rw [show D2M8K2.u4227 = KTree.node D2M8K2.u4225 (nat_lit 9779934) (nat_lit 3879699817) (nat_lit 0) D2M8K2.u4226 from rfl, allE_node, arows4225, irow4227, arows4226]
  all_goals rfl

theorem atot4227 : totK PD2M8K2 D2M8K2.u4227 = [0, 0, 0, 442849060983, 1517975898576, 1333404503612, 232660619595, 5126512042] := by
  rw [show D2M8K2.u4227 = KTree.node D2M8K2.u4225 (nat_lit 9779934) (nat_lit 3879699817) (nat_lit 0) D2M8K2.u4226 from rfl, totK_node, atot4225, atot4226]
  decide +kernel

theorem arows4231 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4231 = true := by
  rw [show D2M8K2.u4231 = KTree.node D2M8K2.u4229 (nat_lit 9783453) (nat_lit 1520999190) (nat_lit 0) D2M8K2.u4230 from rfl, allE_node, arows4229, irow4231, arows4230]
  all_goals rfl

theorem atot4231 : totK PD2M8K2 D2M8K2.u4231 = [0, 0, 0, 480829781253, 1625883194821, 1316177999147, 162115721411, 1392055030] := by
  rw [show D2M8K2.u4231 = KTree.node D2M8K2.u4229 (nat_lit 9783453) (nat_lit 1520999190) (nat_lit 0) D2M8K2.u4230 from rfl, totK_node, atot4229, atot4230]
  decide +kernel

theorem arows4234 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4234 = true := by
  rw [show D2M8K2.u4234 = KTree.node D2M8K2.u4232 (nat_lit 9787279) (nat_lit 1520700120) (nat_lit 0) D2M8K2.u4233 from rfl, allE_node, arows4232, irow4234, arows4233]
  all_goals rfl

theorem atot4234 : totK PD2M8K2 D2M8K2.u4234 = [0, 0, 320804550429, 930665442039, 1071941305392, 953967530933, 262051477944, 9139067247] := by
  rw [show D2M8K2.u4234 = KTree.node D2M8K2.u4232 (nat_lit 9787279) (nat_lit 1520700120) (nat_lit 0) D2M8K2.u4233 from rfl, totK_node, atot4232, atot4233]
  decide +kernel

theorem arows4239 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4239 = true := by
  rw [show D2M8K2.u4239 = KTree.node D2M8K2.u4237 (nat_lit 9791955) (nat_lit 2584460361) (nat_lit 0) D2M8K2.u4238 from rfl, allE_node, arows4237, irow4239, arows4238]
  all_goals rfl

theorem atot4239 : totK PD2M8K2 D2M8K2.u4239 = [0, 0, 431011160076, 1496769734897, 1377914107034, 331409055139, 24256071441, 0] := by
  rw [show D2M8K2.u4239 = KTree.node D2M8K2.u4237 (nat_lit 9791955) (nat_lit 2584460361) (nat_lit 0) D2M8K2.u4238 from rfl, totK_node, atot4237, atot4238]
  decide +kernel

theorem arows4242 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4242 = true := by
  rw [show D2M8K2.u4242 = KTree.node D2M8K2.u4240 (nat_lit 9794718) (nat_lit 3587580438) (nat_lit 0) D2M8K2.u4241 from rfl, allE_node, arows4240, irow4242, arows4241]
  all_goals rfl

theorem atot4242 : totK PD2M8K2 D2M8K2.u4242 = [0, 0, 439833748684, 1449976197777, 1346473538696, 369323123445, 13231254741, 0] := by
  rw [show D2M8K2.u4242 = KTree.node D2M8K2.u4240 (nat_lit 9794718) (nat_lit 3587580438) (nat_lit 0) D2M8K2.u4241 from rfl, totK_node, atot4240, atot4241]
  decide +kernel

theorem arows4246 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4246 = true := by
  rw [show D2M8K2.u4246 = KTree.node D2M8K2.u4244 (nat_lit 9801549) (nat_lit 1496740031) (nat_lit 0) D2M8K2.u4245 from rfl, allE_node, arows4244, irow4246, arows4245]
  all_goals rfl

theorem atot4246 : totK PD2M8K2 D2M8K2.u4246 = [0, 0, 409995302347, 1460231435365, 1405626276612, 310780811066, 9094631223, 0] := by
  rw [show D2M8K2.u4246 = KTree.node D2M8K2.u4244 (nat_lit 9801549) (nat_lit 1496740031) (nat_lit 0) D2M8K2.u4245 from rfl, totK_node, atot4244, atot4245]
  decide +kernel

theorem arows4249 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4249 = true := by
  rw [show D2M8K2.u4249 = KTree.node D2M8K2.u4247 (nat_lit 9805149) (nat_lit 1379731300) (nat_lit 0) D2M8K2.u4248 from rfl, allE_node, arows4247, irow4249, arows4248]
  all_goals rfl

theorem atot4249 : totK PD2M8K2 D2M8K2.u4249 = [0, 0, 415593577730, 1498174545848, 1453270007547, 266304014364, 2586295899, 0] := by
  rw [show D2M8K2.u4249 = KTree.node D2M8K2.u4247 (nat_lit 9805149) (nat_lit 1379731300) (nat_lit 0) D2M8K2.u4248 from rfl, totK_node, atot4247, atot4248]
  decide +kernel

theorem arows4255 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4255 = true := by
  rw [show D2M8K2.u4255 = KTree.node D2M8K2.u4253 (nat_lit 9808897) (nat_lit 1427048294) (nat_lit 0) D2M8K2.u4254 from rfl, allE_node, arows4253, irow4255, arows4254]
  all_goals rfl

theorem atot4255 : totK PD2M8K2 D2M8K2.u4255 = [0, 0, 0, 881780522162, 1934403708462, 733201363474, 42127347794, 0] := by
  rw [show D2M8K2.u4255 = KTree.node D2M8K2.u4253 (nat_lit 9808897) (nat_lit 1427048294) (nat_lit 0) D2M8K2.u4254 from rfl, totK_node, atot4253, atot4254]
  decide +kernel

theorem arows4258 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4258 = true := by
  rw [show D2M8K2.u4258 = KTree.node D2M8K2.u4256 (nat_lit 9815647) (nat_lit 1687469092) (nat_lit 0) D2M8K2.u4257 from rfl, allE_node, arows4256, irow4258, arows4257]
  all_goals rfl

theorem atot4258 : totK PD2M8K2 D2M8K2.u4258 = [0, 0, 0, 606080259918, 1796792294445, 1090466681595, 79446864760, 0] := by
  rw [show D2M8K2.u4258 = KTree.node D2M8K2.u4256 (nat_lit 9815647) (nat_lit 1687469092) (nat_lit 0) D2M8K2.u4257 from rfl, totK_node, atot4256, atot4257]
  decide +kernel

theorem arows4262 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4262 = true := by
  rw [show D2M8K2.u4262 = KTree.node D2M8K2.u4260 (nat_lit 9822682) (nat_lit 3224725964) (nat_lit 0) D2M8K2.u4261 from rfl, allE_node, arows4260, irow4262, arows4261]
  all_goals rfl

theorem atot4262 : totK PD2M8K2 D2M8K2.u4262 = [0, 0, 0, 406639568713, 1587577317305, 1304216223762, 200361544037, 5320761635] := by
  rw [show D2M8K2.u4262 = KTree.node D2M8K2.u4260 (nat_lit 9822682) (nat_lit 3224725964) (nat_lit 0) D2M8K2.u4261 from rfl, totK_node, atot4260, atot4261]
  decide +kernel

theorem arows4265 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4265 = true := by
  rw [show D2M8K2.u4265 = KTree.node D2M8K2.u4263 (nat_lit 9826971) (nat_lit 3660288012) (nat_lit 0) D2M8K2.u4264 from rfl, allE_node, arows4263, irow4265, arows4264]
  all_goals rfl

theorem atot4265 : totK PD2M8K2 D2M8K2.u4265 = [0, 0, 320954541705, 1222114308064, 1375736806209, 596935245168, 70935718689, 1225787871] := by
  rw [show D2M8K2.u4265 = KTree.node D2M8K2.u4263 (nat_lit 9826971) (nat_lit 3660288012) (nat_lit 0) D2M8K2.u4264 from rfl, totK_node, atot4263, atot4264]
  decide +kernel

theorem arows4270 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4270 = true := by
  rw [show D2M8K2.u4270 = KTree.node D2M8K2.u4268 (nat_lit 9833350) (nat_lit 2469172538) (nat_lit 0) D2M8K2.u4269 from rfl, allE_node, arows4268, irow4270, arows4269]
  all_goals rfl

theorem atot4270 : totK PD2M8K2 D2M8K2.u4270 = [0, 0, 431047342452, 1515389366827, 1381295110330, 313100654986, 21393864572, 0] := by
  rw [show D2M8K2.u4270 = KTree.node D2M8K2.u4268 (nat_lit 9833350) (nat_lit 2469172538) (nat_lit 0) D2M8K2.u4269 from rfl, totK_node, atot4268, atot4269]
  decide +kernel

theorem arows4273 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4273 = true := by
  rw [show D2M8K2.u4273 = KTree.node D2M8K2.u4271 (nat_lit 9839604) (nat_lit 2762951027) (nat_lit 0) D2M8K2.u4272 from rfl, allE_node, arows4271, irow4273, arows4272]
  all_goals rfl

theorem atot4273 : totK PD2M8K2 D2M8K2.u4273 = [0, 0, 440007744190, 1436417771721, 1352897695546, 384458572638, 16091834962, 0] := by
  rw [show D2M8K2.u4273 = KTree.node D2M8K2.u4271 (nat_lit 9839604) (nat_lit 2762951027) (nat_lit 0) D2M8K2.u4272 from rfl, totK_node, atot4271, atot4272]
  decide +kernel

theorem arows4277 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4277 = true := by
  rw [show D2M8K2.u4277 = KTree.node D2M8K2.u4275 (nat_lit 9842913) (nat_lit 1744413445) (nat_lit 0) D2M8K2.u4276 from rfl, allE_node, arows4275, irow4277, arows4276]
  all_goals rfl

theorem atot4277 : totK PD2M8K2 D2M8K2.u4277 = [0, 0, 410061973523, 1457758014899, 1400555220852, 318713196634, 9198031362, 0] := by
  rw [show D2M8K2.u4277 = KTree.node D2M8K2.u4275 (nat_lit 9842913) (nat_lit 1744413445) (nat_lit 0) D2M8K2.u4276 from rfl, totK_node, atot4275, atot4276]
  decide +kernel

theorem arows4280 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4280 = true := by
  rw [show D2M8K2.u4280 = KTree.node D2M8K2.u4278 (nat_lit 9846553) (nat_lit 1287959779) (nat_lit 0) D2M8K2.u4279 from rfl, allE_node, arows4278, irow4280, arows4279]
  all_goals rfl

theorem atot4280 : totK PD2M8K2 D2M8K2.u4280 = [0, 0, 415676613225, 1511464381513, 1452169623847, 251448524288, 2586295899, 0] := by
  rw [show D2M8K2.u4280 = KTree.node D2M8K2.u4278 (nat_lit 9846553) (nat_lit 1287959779) (nat_lit 0) D2M8K2.u4279 from rfl, totK_node, atot4278, atot4279]
  decide +kernel

theorem arows4287 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4287 = true := by
  rw [show D2M8K2.u4287 = KTree.node D2M8K2.u4285 (nat_lit 9850591) (nat_lit 2358555796) (nat_lit 0) D2M8K2.u4286 from rfl, allE_node, arows4285, irow4287, arows4286]
  all_goals rfl

theorem atot4287 : totK PD2M8K2 D2M8K2.u4287 = [0, 0, 0, 907315023464, 1905429480395, 746108487142, 44091814973, 0] := by
  rw [show D2M8K2.u4287 = KTree.node D2M8K2.u4285 (nat_lit 9850591) (nat_lit 2358555796) (nat_lit 0) D2M8K2.u4286 from rfl, totK_node, atot4285, atot4286]
  decide +kernel

theorem arows4290 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4290 = true := by
  rw [show D2M8K2.u4290 = KTree.node D2M8K2.u4288 (nat_lit 9860878) (nat_lit 3927091373) (nat_lit 0) D2M8K2.u4289 from rfl, allE_node, arows4288, irow4290, arows4289]
  all_goals rfl

theorem atot4290 : totK PD2M8K2 D2M8K2.u4290 = [0, 0, 0, 604406011631, 1781924315262, 1108089692008, 83475433393, 0] := by
  rw [show D2M8K2.u4290 = KTree.node D2M8K2.u4288 (nat_lit 9860878) (nat_lit 3927091373) (nat_lit 0) D2M8K2.u4289 from rfl, totK_node, atot4288, atot4289]
  decide +kernel

theorem arows4294 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4294 = true := by
  rw [show D2M8K2.u4294 = KTree.node D2M8K2.u4292 (nat_lit 9864261) (nat_lit 1201913455) (nat_lit 0) D2M8K2.u4293 from rfl, allE_node, arows4292, irow4294, arows4293]
  all_goals rfl

theorem atot4294 : totK PD2M8K2 D2M8K2.u4294 = [0, 0, 0, 404697073573, 1568025627371, 1324940264952, 206823388301, 5352782441] := by
  rw [show D2M8K2.u4294 = KTree.node D2M8K2.u4292 (nat_lit 9864261) (nat_lit 1201913455) (nat_lit 0) D2M8K2.u4293 from rfl, totK_node, atot4292, atot4293]
  decide +kernel

theorem arows4297 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4297 = true := by
  rw [show D2M8K2.u4297 = KTree.node D2M8K2.u4295 (nat_lit 9868447) (nat_lit 2331921920) (nat_lit 0) D2M8K2.u4296 from rfl, allE_node, arows4295, irow4297, arows4296]
  all_goals rfl

theorem atot4297 : totK PD2M8K2 D2M8K2.u4297 = [0, 0, 319053168236, 1199327849787, 1378053485981, 598650602144, 70036058961, 1271866555] := by
  rw [show D2M8K2.u4297 = KTree.node D2M8K2.u4295 (nat_lit 9868447) (nat_lit 2331921920) (nat_lit 0) D2M8K2.u4296 from rfl, totK_node, atot4295, atot4296]
  decide +kernel

theorem arows4302 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4302 = true := by
  rw [show D2M8K2.u4302 = KTree.node D2M8K2.u4300 (nat_lit 9874760) (nat_lit 3883878365) (nat_lit 0) D2M8K2.u4301 from rfl, allE_node, arows4300, irow4302, arows4301]
  all_goals rfl

theorem atot4302 : totK PD2M8K2 D2M8K2.u4302 = [0, 0, 430739598440, 1544711791864, 1375692778633, 280072207776, 21396654552, 0] := by
  rw [show D2M8K2.u4302 = KTree.node D2M8K2.u4300 (nat_lit 9874760) (nat_lit 3883878365) (nat_lit 0) D2M8K2.u4301 from rfl, totK_node, atot4300, atot4301]
  decide +kernel

theorem arows4305 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4305 = true := by
  rw [show D2M8K2.u4305 = KTree.node D2M8K2.u4303 (nat_lit 9877617) (nat_lit 1786854237) (nat_lit 0) D2M8K2.u4304 from rfl, allE_node, arows4303, irow4305, arows4304]
  all_goals rfl

theorem atot4305 : totK PD2M8K2 D2M8K2.u4305 = [0, 0, 411914342465, 1370188639691, 1376424700439, 424073485862, 16094634009, 0] := by
  rw [show D2M8K2.u4305 = KTree.node D2M8K2.u4303 (nat_lit 9877617) (nat_lit 1786854237) (nat_lit 0) D2M8K2.u4304 from rfl, totK_node, atot4303, atot4304]
  decide +kernel

theorem arows4309 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4309 = true := by
  rw [show D2M8K2.u4309 = KTree.node D2M8K2.u4307 (nat_lit 9881086) (nat_lit 3775463131) (nat_lit 0) D2M8K2.u4308 from rfl, allE_node, arows4307, irow4309, arows4308]
  all_goals rfl

theorem atot4309 : totK PD2M8K2 D2M8K2.u4309 = [0, 0, 412143460518, 1456338734625, 1409304039073, 304811484572, 9094631223, 0] := by
  rw [show D2M8K2.u4309 = KTree.node D2M8K2.u4307 (nat_lit 9881086) (nat_lit 3775463131) (nat_lit 0) D2M8K2.u4308 from rfl, totK_node, atot4307, atot4308]
  decide +kernel

theorem arows4312 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4312 = true := by
  rw [show D2M8K2.u4312 = KTree.node D2M8K2.u4310 (nat_lit 9884520) (nat_lit 2689770091) (nat_lit 0) D2M8K2.u4311 from rfl, allE_node, arows4310, irow4312, arows4311]
  all_goals rfl

theorem atot4312 : totK PD2M8K2 D2M8K2.u4312 = [0, 0, 437791956100, 1501838778161, 1358128378782, 298374750007, 9216081867, 0] := by
  rw [show D2M8K2.u4312 = KTree.node D2M8K2.u4310 (nat_lit 9884520) (nat_lit 2689770091) (nat_lit 0) D2M8K2.u4311 from rfl, totK_node, atot4310, atot4311]
  decide +kernel

theorem arows4318 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4318 = true := by
  rw [show D2M8K2.u4318 = KTree.node D2M8K2.u4316 (nat_lit 9891894) (nat_lit 2604246117) (nat_lit 0) D2M8K2.u4317 from rfl, allE_node, arows4316, irow4318, arows4317]
  all_goals rfl

theorem atot4318 : totK PD2M8K2 D2M8K2.u4318 = [0, 0, 0, 931737217769, 2005723471317, 630570974258, 31004531656, 0] := by
  rw [show D2M8K2.u4318 = KTree.node D2M8K2.u4316 (nat_lit 9891894) (nat_lit 2604246117) (nat_lit 0) D2M8K2.u4317 from rfl, totK_node, atot4316, atot4317]
  decide +kernel

theorem arows4321 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4321 = true := by
  rw [show D2M8K2.u4321 = KTree.node D2M8K2.u4319 (nat_lit 9898540) (nat_lit 3811927988) (nat_lit 0) D2M8K2.u4320 from rfl, allE_node, arows4319, irow4321, arows4320]
  all_goals rfl

theorem atot4321 : totK PD2M8K2 D2M8K2.u4321 = [0, 0, 0, 772142257596, 1932204330605, 839264275343, 41987532991, 0] := by
  rw [show D2M8K2.u4321 = KTree.node D2M8K2.u4319 (nat_lit 9898540) (nat_lit 3811927988) (nat_lit 0) D2M8K2.u4320 from rfl, totK_node, atot4319, atot4320]
  decide +kernel

theorem arows4325 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4325 = true := by
  rw [show D2M8K2.u4325 = KTree.node D2M8K2.u4323 (nat_lit 9905277) (nat_lit 1547845720) (nat_lit 0) D2M8K2.u4324 from rfl, allE_node, arows4323, irow4325, arows4324]
  all_goals rfl

theorem atot4325 : totK PD2M8K2 D2M8K2.u4325 = [0, 0, 0, 684767025620, 1880512089177, 958212058773, 50765026457, 0] := by
  rw [show D2M8K2.u4325 = KTree.node D2M8K2.u4323 (nat_lit 9905277) (nat_lit 1547845720) (nat_lit 0) D2M8K2.u4324 from rfl, totK_node, atot4323, atot4324]
  decide +kernel

theorem arows4328 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4328 = true := by
  rw [show D2M8K2.u4328 = KTree.node D2M8K2.u4326 (nat_lit 9912823) (nat_lit 2034735795) (nat_lit 512) D2M8K2.u4327 from rfl, allE_node, arows4326, irow4328, arows4327]
  all_goals rfl

theorem atot4328 : totK PD2M8K2 D2M8K2.u4328 = [0, 0, 416375132788, 1283832220113, 1189595830183, 622794015024, 112417467604, 1429815836] := by
  rw [show D2M8K2.u4328 = KTree.node D2M8K2.u4326 (nat_lit 9912823) (nat_lit 2034735795) (nat_lit 512) D2M8K2.u4327 from rfl, totK_node, atot4326, atot4327]
  decide +kernel

theorem arows4333 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4333 = true := by
  rw [show D2M8K2.u4333 = KTree.node D2M8K2.u4331 (nat_lit 9917331) (nat_lit 3716614309) (nat_lit 0) D2M8K2.u4332 from rfl, allE_node, arows4331, irow4333, arows4332]
  all_goals rfl

theorem atot4333 : totK PD2M8K2 D2M8K2.u4333 = [0, 0, 337745090064, 1303713133742, 1471781433007, 487652149942, 30675760985, 0] := by
  rw [show D2M8K2.u4333 = KTree.node D2M8K2.u4331 (nat_lit 9917331) (nat_lit 3716614309) (nat_lit 0) D2M8K2.u4332 from rfl, totK_node, atot4331, atot4332]
  decide +kernel

theorem arows4336 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4336 = true := by
  rw [show D2M8K2.u4336 = KTree.node D2M8K2.u4334 (nat_lit 9920167) (nat_lit 2045656648) (nat_lit 0) D2M8K2.u4335 from rfl, allE_node, arows4334, irow4336, arows4335]
  all_goals rfl

theorem atot4336 : totK PD2M8K2 D2M8K2.u4336 = [0, 0, 413538249517, 1416331029558, 1404479607470, 364043714498, 13386914824, 0] := by
  rw [show D2M8K2.u4336 = KTree.node D2M8K2.u4334 (nat_lit 9920167) (nat_lit 2045656648) (nat_lit 0) D2M8K2.u4335 from rfl, totK_node, atot4334, atot4335]
  decide +kernel

theorem arows4340 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4340 = true := by
  rw [show D2M8K2.u4340 = KTree.node D2M8K2.u4338 (nat_lit 9923659) (nat_lit 1790597141) (nat_lit 0) D2M8K2.u4339 from rfl, allE_node, arows4338, irow4340, arows4339]
  all_goals rfl

theorem atot4340 : totK PD2M8K2 D2M8K2.u4340 = [0, 0, 413787289091, 1485800747308, 1424081044618, 299158232435, 6654590951, 0] := by
  rw [show D2M8K2.u4340 = KTree.node D2M8K2.u4338 (nat_lit 9923659) (nat_lit 1790597141) (nat_lit 0) D2M8K2.u4339 from rfl, totK_node, atot4338, atot4339]
  decide +kernel

theorem arows4343 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4343 = true := by
  rw [show D2M8K2.u4343 = KTree.node D2M8K2.u4341 (nat_lit 9930223) (nat_lit 2350916224) (nat_lit 0) D2M8K2.u4342 from rfl, allE_node, arows4341, irow4343, arows4342]
  all_goals rfl

theorem atot4343 : totK PD2M8K2 D2M8K2.u4343 = [0, 0, 442048499497, 1502466452632, 1406152774504, 282134138050, 2418991907, 0] := by
  rw [show D2M8K2.u4343 = KTree.node D2M8K2.u4341 (nat_lit 9930223) (nat_lit 2350916224) (nat_lit 0) D2M8K2.u4342 from rfl, totK_node, atot4341, atot4342]
  decide +kernel

theorem arows4352 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4352 = true := by
  rw [show D2M8K2.u4352 = KTree.node D2M8K2.u4350 (nat_lit 9936575) (nat_lit 2115149719) (nat_lit 0) D2M8K2.u4351 from rfl, allE_node, arows4350, irow4352, arows4351]
  all_goals rfl

theorem atot4352 : totK PD2M8K2 D2M8K2.u4352 = [0, 0, 0, 903612195867, 1832981475899, 829850062298, 58531428972, 0] := by
  rw [show D2M8K2.u4352 = KTree.node D2M8K2.u4350 (nat_lit 9936575) (nat_lit 2115149719) (nat_lit 0) D2M8K2.u4351 from rfl, totK_node, atot4350, atot4351]
  decide +kernel

theorem arows4355 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4355 = true := by
  rw [show D2M8K2.u4355 = KTree.node D2M8K2.u4353 (nat_lit 9941241) (nat_lit 1428969271) (nat_lit 2) D2M8K2.u4354 from rfl, allE_node, arows4353, irow4355, arows4354]
  all_goals rfl

theorem atot4355 : totK PD2M8K2 D2M8K2.u4355 = [0, 0, 0, 512444658790, 1680573469116, 1241834200132, 142677554702, 1323630408] := by
  rw [show D2M8K2.u4355 = KTree.node D2M8K2.u4353 (nat_lit 9941241) (nat_lit 1428969271) (nat_lit 2) D2M8K2.u4354 from rfl, totK_node, atot4353, atot4354]
  decide +kernel

theorem arows4359 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4359 = true := by
  rw [show D2M8K2.u4359 = KTree.node D2M8K2.u4357 (nat_lit 9945774) (nat_lit 3872776219) (nat_lit 0) D2M8K2.u4358 from rfl, allE_node, arows4357, irow4359, arows4358]
  all_goals rfl

theorem atot4359 : totK PD2M8K2 D2M8K2.u4359 = [0, 0, 0, 560431035329, 1708517694119, 1178513987779, 126944542317, 1332468113] := by
  rw [show D2M8K2.u4359 = KTree.node D2M8K2.u4357 (nat_lit 9945774) (nat_lit 3872776219) (nat_lit 0) D2M8K2.u4358 from rfl, totK_node, atot4357, atot4358]
  decide +kernel

theorem arows4362 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4362 = true := by
  rw [show D2M8K2.u4362 = KTree.node D2M8K2.u4360 (nat_lit 9953020) (nat_lit 3831955351) (nat_lit 0) D2M8K2.u4361 from rfl, allE_node, arows4360, irow4362, arows4361]
  all_goals rfl

theorem atot4362 : totK PD2M8K2 D2M8K2.u4362 = [0, 327677273344, 744594656918, 412814806028, 762647132810, 1045789494393, 247198255366, 9533751846] := by
  rw [show D2M8K2.u4362 = KTree.node D2M8K2.u4360 (nat_lit 9953020) (nat_lit 3831955351) (nat_lit 0) D2M8K2.u4361 from rfl, totK_node, atot4360, atot4361]
  decide +kernel

theorem arows4367 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4367 = true := by
  rw [show D2M8K2.u4367 = KTree.node D2M8K2.u4365 (nat_lit 9956498) (nat_lit 3638312586) (nat_lit 0) D2M8K2.u4366 from rfl, allE_node, arows4365, irow4367, arows4366]
  all_goals rfl

theorem atot4367 : totK PD2M8K2 D2M8K2.u4367 = [0, 431750616190, 1606571244231, 1381114901148, 186555437103, 1369150432, 0, 0] := by
  rw [show D2M8K2.u4367 = KTree.node D2M8K2.u4365 (nat_lit 9956498) (nat_lit 3638312586) (nat_lit 0) D2M8K2.u4366 from rfl, totK_node, atot4365, atot4366]
  decide +kernel

theorem arows4370 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4370 = true := by
  rw [show D2M8K2.u4370 = KTree.node D2M8K2.u4368 (nat_lit 9963296) (nat_lit 3500048543) (nat_lit 0) D2M8K2.u4369 from rfl, allE_node, arows4368, irow4370, arows4369]
  all_goals rfl

theorem atot4370 : totK PD2M8K2 D2M8K2.u4370 = [0, 394533041720, 1419064748929, 1428077689637, 327810746831, 13049727234, 0, 0] := by
  rw [show D2M8K2.u4370 = KTree.node D2M8K2.u4368 (nat_lit 9963296) (nat_lit 3500048543) (nat_lit 0) D2M8K2.u4369 from rfl, totK_node, atot4368, atot4369]
  decide +kernel

theorem arows4374 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4374 = true := by
  rw [show D2M8K2.u4374 = KTree.node D2M8K2.u4372 (nat_lit 9970233) (nat_lit 1899350950) (nat_lit 0) D2M8K2.u4373 from rfl, allE_node, arows4372, irow4374, arows4373]
  all_goals rfl

theorem atot4374 : totK PD2M8K2 D2M8K2.u4374 = [0, 493589057864, 1564089683287, 1327234256614, 218547811250, 4980514959, 0, 0] := by
  rw [show D2M8K2.u4374 = KTree.node D2M8K2.u4372 (nat_lit 9970233) (nat_lit 1899350950) (nat_lit 0) D2M8K2.u4373 from rfl, totK_node, atot4372, atot4373]
  decide +kernel

theorem arows4377 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4377 = true := by
  rw [show D2M8K2.u4377 = KTree.node D2M8K2.u4375 (nat_lit 9973996) (nat_lit 3771370132) (nat_lit 0) D2M8K2.u4376 from rfl, allE_node, arows4375, irow4377, arows4376]
  all_goals rfl

theorem atot4377 : totK PD2M8K2 D2M8K2.u4377 = [0, 0, 911607781161, 1947950728652, 669823622859, 28560720904, 0, 0] := by
  rw [show D2M8K2.u4377 = KTree.node D2M8K2.u4375 (nat_lit 9973996) (nat_lit 3771370132) (nat_lit 0) D2M8K2.u4376 from rfl, totK_node, atot4375, atot4376]
  decide +kernel

theorem arows4383 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4383 = true := by
  rw [show D2M8K2.u4383 = KTree.node D2M8K2.u4381 (nat_lit 9981257) (nat_lit 1806589123) (nat_lit 0) D2M8K2.u4382 from rfl, allE_node, arows4381, irow4383, arows4382]
  all_goals rfl

theorem atot4383 : totK PD2M8K2 D2M8K2.u4383 = [0, 0, 510383059586, 1701124853935, 1178809000202, 130578202688, 1369150432, 0] := by
  rw [show D2M8K2.u4383 = KTree.node D2M8K2.u4381 (nat_lit 9981257) (nat_lit 1806589123) (nat_lit 0) D2M8K2.u4382 from rfl, totK_node, atot4381, atot4382]
  decide +kernel

theorem arows4386 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4386 = true := by
  rw [show D2M8K2.u4386 = KTree.node D2M8K2.u4384 (nat_lit 9991376) (nat_lit 2571830901) (nat_lit 0) D2M8K2.u4385 from rfl, allE_node, arows4384, irow4386, arows4385]
  all_goals rfl

theorem atot4386 : totK PD2M8K2 D2M8K2.u4386 = [0, 0, 728889377943, 1908833622167, 889851795983, 41370426083, 0, 0] := by
  rw [show D2M8K2.u4386 = KTree.node D2M8K2.u4384 (nat_lit 9991376) (nat_lit 2571830901) (nat_lit 0) D2M8K2.u4385 from rfl, totK_node, atot4384, atot4385]
  decide +kernel

theorem arows4390 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4390 = true := by
  rw [show D2M8K2.u4390 = KTree.node D2M8K2.u4388 (nat_lit 9999616) (nat_lit 2888758623) (nat_lit 0) D2M8K2.u4389 from rfl, allE_node, arows4388, irow4390, arows4389]
  all_goals rfl

theorem atot4390 : totK PD2M8K2 D2M8K2.u4390 = [0, 445091534014, 1424512443221, 1339906545938, 443237049788, 36487900741, 0, 0] := by
  rw [show D2M8K2.u4390 = KTree.node D2M8K2.u4388 (nat_lit 9999616) (nat_lit 2888758623) (nat_lit 0) D2M8K2.u4389 from rfl, totK_node, atot4388, atot4389]
  decide +kernel

theorem arows4393 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4393 = true := by
  rw [show D2M8K2.u4393 = KTree.node D2M8K2.u4391 (nat_lit 10002354) (nat_lit 2631635771) (nat_lit 0) D2M8K2.u4392 from rfl, allE_node, arows4391, irow4393, arows4392]
  all_goals rfl

theorem atot4393 : totK PD2M8K2 D2M8K2.u4393 = [0, 426698916692, 1464683017514, 1410465399635, 337929121949, 9378345584, 0, 0] := by
  rw [show D2M8K2.u4393 = KTree.node D2M8K2.u4391 (nat_lit 10002354) (nat_lit 2631635771) (nat_lit 0) D2M8K2.u4392 from rfl, totK_node, atot4391, atot4392]
  decide +kernel

theorem arows4398 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4398 = true := by
  rw [show D2M8K2.u4398 = KTree.node D2M8K2.u4396 (nat_lit 10006226) (nat_lit 3965365235) (nat_lit 0) D2M8K2.u4397 from rfl, allE_node, arows4396, irow4398, arows4397]
  all_goals rfl

theorem atot4398 : totK PD2M8K2 D2M8K2.u4398 = [0, 347039505552, 1367994831713, 1528838327084, 393058835682, 18710070543, 0, 0] := by
  rw [show D2M8K2.u4398 = KTree.node D2M8K2.u4396 (nat_lit 10006226) (nat_lit 3965365235) (nat_lit 0) D2M8K2.u4397 from rfl, totK_node, atot4396, atot4397]
  decide +kernel

theorem arows4401 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4401 = true := by
  rw [show D2M8K2.u4401 = KTree.node D2M8K2.u4399 (nat_lit 10009579) (nat_lit 1568836580) (nat_lit 0) D2M8K2.u4400 from rfl, allE_node, arows4399, irow4401, arows4400]
  all_goals rfl

theorem atot4401 : totK PD2M8K2 D2M8K2.u4401 = [0, 411827884670, 1545794440967, 1434154533523, 241250769458, 3434588030, 0, 0] := by
  rw [show D2M8K2.u4401 = KTree.node D2M8K2.u4399 (nat_lit 10009579) (nat_lit 1568836580) (nat_lit 0) D2M8K2.u4400 from rfl, totK_node, atot4399, atot4400]
  decide +kernel

theorem arows4405 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4405 = true := by
  rw [show D2M8K2.u4405 = KTree.node D2M8K2.u4403 (nat_lit 10013165) (nat_lit 1613097036) (nat_lit 0) D2M8K2.u4404 from rfl, allE_node, arows4403, irow4405, arows4404]
  all_goals rfl

theorem atot4405 : totK PD2M8K2 D2M8K2.u4405 = [0, 417475016712, 1403931770374, 1427616161615, 370575353763, 11275782838, 0, 0] := by
  rw [show D2M8K2.u4405 = KTree.node D2M8K2.u4403 (nat_lit 10013165) (nat_lit 1613097036) (nat_lit 0) D2M8K2.u4404 from rfl, totK_node, atot4403, atot4404]
  decide +kernel

theorem arows4408 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4408 = true := by
  rw [show D2M8K2.u4408 = KTree.node D2M8K2.u4406 (nat_lit 10020069) (nat_lit 1435741590) (nat_lit 0) D2M8K2.u4407 from rfl, allE_node, arows4406, irow4408, arows4407]
  all_goals rfl

theorem atot4408 : totK PD2M8K2 D2M8K2.u4408 = [0, 0, 535919671842, 1562951176561, 1224942539434, 316038560845, 25191558099, 0] := by
  rw [show D2M8K2.u4408 = KTree.node D2M8K2.u4406 (nat_lit 10020069) (nat_lit 1435741590) (nat_lit 0) D2M8K2.u4407 from rfl, totK_node, atot4406, atot4407]
  decide +kernel

theorem arows4415 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4415 = true := by
  rw [show D2M8K2.u4415 = KTree.node D2M8K2.u4413 (nat_lit 10022874) (nat_lit 3625354406) (nat_lit 0) D2M8K2.u4414 from rfl, allE_node, arows4413, irow4415, arows4414]
  all_goals rfl

theorem atot4415 : totK PD2M8K2 D2M8K2.u4415 = [0, 0, 425067482734, 1462040825342, 1375335237139, 339692116969, 11730315755, 0] := by
  rw [show D2M8K2.u4415 = KTree.node D2M8K2.u4413 (nat_lit 10022874) (nat_lit 3625354406) (nat_lit 0) D2M8K2.u4414 from rfl, totK_node, atot4413, atot4414]
  decide +kernel

theorem arows4418 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4418 = true := by
  rw [show D2M8K2.u4418 = KTree.node D2M8K2.u4416 (nat_lit 10026843) (nat_lit 3620461571) (nat_lit 0) D2M8K2.u4417 from rfl, allE_node, arows4416, irow4418, arows4417]
  all_goals rfl

theorem atot4418 : totK PD2M8K2 D2M8K2.u4418 = [0, 0, 345944302442, 1405869219151, 1552254124517, 340224203046, 9191800397, 0] := by
  rw [show D2M8K2.u4418 = KTree.node D2M8K2.u4416 (nat_lit 10026843) (nat_lit 3620461571) (nat_lit 0) D2M8K2.u4417 from rfl, totK_node, atot4416, atot4417]
  decide +kernel

theorem arows4422 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4422 = true := by
  rw [show D2M8K2.u4422 = KTree.node D2M8K2.u4420 (nat_lit 10030258) (nat_lit 3531814390) (nat_lit 0) D2M8K2.u4421 from rfl, allE_node, arows4420, irow4422, arows4421]
  all_goals rfl

theorem atot4422 : totK PD2M8K2 D2M8K2.u4422 = [0, 0, 410849565325, 1574168345373, 1448771103014, 189454482874, 1186940923, 0] := by
  rw [show D2M8K2.u4422 = KTree.node D2M8K2.u4420 (nat_lit 10030258) (nat_lit 3531814390) (nat_lit 0) D2M8K2.u4421 from rfl, totK_node, atot4420, atot4421]
  decide +kernel

theorem arows4425 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4425 = true := by
  rw [show D2M8K2.u4425 = KTree.node D2M8K2.u4423 (nat_lit 10034234) (nat_lit 4228345622) (nat_lit 0) D2M8K2.u4424 from rfl, allE_node, arows4423, irow4425, arows4424]
  all_goals rfl

theorem atot4425 : totK PD2M8K2 D2M8K2.u4425 = [0, 0, 416386384292, 1477545064237, 1435785134533, 297619831850, 3899220927, 0] := by
  rw [show D2M8K2.u4425 = KTree.node D2M8K2.u4423 (nat_lit 10034234) (nat_lit 4228345622) (nat_lit 0) D2M8K2.u4424 from rfl, totK_node, atot4423, atot4424]
  decide +kernel

theorem arows4430 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4430 = true := by
  rw [show D2M8K2.u4430 = KTree.node D2M8K2.u4428 (nat_lit 10037738) (nat_lit 3085466853) (nat_lit 0) D2M8K2.u4429 from rfl, allE_node, arows4428, irow4430, arows4429]
  all_goals rfl

theorem atot4430 : totK PD2M8K2 D2M8K2.u4430 = [0, 490772665162, 1565045172616, 1225994104912, 203817184125, 73306991618, 6818291842, 0] := by
  rw [show D2M8K2.u4430 = KTree.node D2M8K2.u4428 (nat_lit 10037738) (nat_lit 3085466853) (nat_lit 0) D2M8K2.u4429 from rfl, totK_node, atot4428, atot4429]
  decide +kernel

theorem arows4433 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4433 = true := by
  rw [show D2M8K2.u4433 = KTree.node D2M8K2.u4431 (nat_lit 10041347) (nat_lit 2870585650) (nat_lit 0) D2M8K2.u4432 from rfl, allE_node, arows4431, irow4433, arows4432]
  all_goals rfl

theorem atot4433 : totK PD2M8K2 D2M8K2.u4433 = [0, 333611568285, 1309752409410, 1485969559317, 496456979372, 30763396594, 0, 0] := by
  rw [show D2M8K2.u4433 = KTree.node D2M8K2.u4431 (nat_lit 10041347) (nat_lit 2870585650) (nat_lit 0) D2M8K2.u4432 from rfl, totK_node, atot4431, atot4432]
  decide +kernel

theorem arows4437 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4437 = true := by
  rw [show D2M8K2.u4437 = KTree.node D2M8K2.u4435 (nat_lit 10044347) (nat_lit 2294897957) (nat_lit 0) D2M8K2.u4436 from rfl, allE_node, arows4435, irow4437, arows4436]
  all_goals rfl

theorem atot4437 : totK PD2M8K2 D2M8K2.u4437 = [0, 445894822140, 1465576831541, 1366307120545, 348019474380, 16365122785, 0, 0] := by
  rw [show D2M8K2.u4437 = KTree.node D2M8K2.u4435 (nat_lit 10044347) (nat_lit 2294897957) (nat_lit 0) D2M8K2.u4436 from rfl, totK_node, atot4435, atot4436]
  decide +kernel

theorem arows4440 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4440 = true := by
  rw [show D2M8K2.u4440 = KTree.node D2M8K2.u4438 (nat_lit 10050799) (nat_lit 1633914272) (nat_lit 0) D2M8K2.u4439 from rfl, allE_node, arows4438, irow4440, arows4439]
  all_goals rfl

theorem atot4440 : totK PD2M8K2 D2M8K2.u4440 = [0, 416044727244, 1516958921197, 1411623352438, 234885926232, 4558519234, 0, 0] := by
  rw [show D2M8K2.u4440 = KTree.node D2M8K2.u4438 (nat_lit 10050799) (nat_lit 1633914272) (nat_lit 0) D2M8K2.u4439 from rfl, totK_node, atot4438, atot4439]
  decide +kernel

theorem arows4446 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4446 = true := by
  rw [show D2M8K2.u4446 = KTree.node D2M8K2.u4444 (nat_lit 10054334) (nat_lit 2464211704) (nat_lit 0) D2M8K2.u4445 from rfl, allE_node, arows4444, irow4446, arows4445]
  all_goals rfl

theorem atot4446 : totK PD2M8K2 D2M8K2.u4446 = [0, 420804927456, 1466953795198, 1414284874405, 298762067491, 6188177409, 0, 0] := by
  rw [show D2M8K2.u4446 = KTree.node D2M8K2.u4444 (nat_lit 10054334) (nat_lit 2464211704) (nat_lit 0) D2M8K2.u4445 from rfl, totK_node, atot4444, atot4445]
  decide +kernel

theorem arows4449 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4449 = true := by
  rw [show D2M8K2.u4449 = KTree.node D2M8K2.u4447 (nat_lit 10057940) (nat_lit 3540893995) (nat_lit 0) D2M8K2.u4448 from rfl, allE_node, arows4447, irow4449, arows4448]
  all_goals rfl

theorem atot4449 : totK PD2M8K2 D2M8K2.u4449 = [0, 0, 553847050341, 1695300598950, 1101791788949, 120600906486, 1206465782, 0] := by
  rw [show D2M8K2.u4449 = KTree.node D2M8K2.u4447 (nat_lit 10057940) (nat_lit 3540893995) (nat_lit 0) D2M8K2.u4448 from rfl, totK_node, atot4447, atot4448]
  decide +kernel

theorem arows4453 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4453 = true := by
  rw [show D2M8K2.u4453 = KTree.node D2M8K2.u4451 (nat_lit 10061672) (nat_lit 3942464715) (nat_lit 0) D2M8K2.u4452 from rfl, allE_node, arows4451, irow4453, arows4452]
  all_goals rfl

theorem atot4453 : totK PD2M8K2 D2M8K2.u4453 = [0, 0, 693450776837, 1843336126326, 1032809778819, 82685717492, 0, 0] := by
  rw [show D2M8K2.u4453 = KTree.node D2M8K2.u4451 (nat_lit 10061672) (nat_lit 3942464715) (nat_lit 0) D2M8K2.u4452 from rfl, totK_node, atot4451, atot4452]
  decide +kernel

theorem arows4456 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4456 = true := by
  rw [show D2M8K2.u4456 = KTree.node D2M8K2.u4454 (nat_lit 10066313) (nat_lit 1627132580) (nat_lit 0) D2M8K2.u4455 from rfl, allE_node, arows4454, irow4456, arows4455]
  all_goals rfl

theorem atot4456 : totK PD2M8K2 D2M8K2.u4456 = [0, 0, 411237527730, 1464103989992, 1346232441287, 302157388819, 13016197374, 0] := by
  rw [show D2M8K2.u4456 = KTree.node D2M8K2.u4454 (nat_lit 10066313) (nat_lit 1627132580) (nat_lit 0) D2M8K2.u4455 from rfl, totK_node, atot4454, atot4455]
  decide +kernel

theorem arows4461 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4461 = true := by
  rw [show D2M8K2.u4461 = KTree.node D2M8K2.u4459 (nat_lit 10073383) (nat_lit 1561261006) (nat_lit 128) D2M8K2.u4460 from rfl, allE_node, arows4459, irow4461, arows4460]
  all_goals rfl

theorem atot4461 : totK PD2M8K2 D2M8K2.u4461 = [0, 0, 434908279153, 1582650117613, 1279100454566, 191437542615, 4574395652, 0] := by
  rw [show D2M8K2.u4461 = KTree.node D2M8K2.u4459 (nat_lit 10073383) (nat_lit 1561261006) (nat_lit 128) D2M8K2.u4460 from rfl, totK_node, atot4459, atot4460]
  decide +kernel

theorem arows4464 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4464 = true := by
  rw [show D2M8K2.u4464 = KTree.node D2M8K2.u4462 (nat_lit 10120137) (nat_lit 1896608936) (nat_lit 0) D2M8K2.u4463 from rfl, allE_node, arows4462, irow4464, arows4463]
  all_goals rfl

theorem atot4464 : totK PD2M8K2 D2M8K2.u4464 = [0, 376987030740, 1403479056076, 1406284292622, 362678056722, 17275258668, 0, 0] := by
  rw [show D2M8K2.u4464 = KTree.node D2M8K2.u4462 (nat_lit 10120137) (nat_lit 1896608936) (nat_lit 0) D2M8K2.u4463 from rfl, totK_node, atot4462, atot4463]
  decide +kernel

theorem arows4468 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4468 = true := by
  rw [show D2M8K2.u4468 = KTree.node D2M8K2.u4466 (nat_lit 10123886) (nat_lit 3854375359) (nat_lit 0) D2M8K2.u4467 from rfl, allE_node, arows4466, irow4468, arows4467]
  all_goals rfl

theorem atot4468 : totK PD2M8K2 D2M8K2.u4468 = [0, 419632389463, 1425307451977, 1391136578909, 403919857819, 28235592988, 0, 0] := by
  rw [show D2M8K2.u4468 = KTree.node D2M8K2.u4466 (nat_lit 10123886) (nat_lit 3854375359) (nat_lit 0) D2M8K2.u4467 from rfl, totK_node, atot4466, atot4467]
  decide +kernel

theorem arows4471 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4471 = true := by
  rw [show D2M8K2.u4471 = KTree.node D2M8K2.u4469 (nat_lit 10126718) (nat_lit 3906817833) (nat_lit 0) D2M8K2.u4470 from rfl, allE_node, arows4469, irow4471, arows4470]
  all_goals rfl

theorem atot4471 : totK PD2M8K2 D2M8K2.u4471 = [0, 423635629509, 1447774608777, 1381753225762, 348477852211, 10496993607, 0, 0] := by
  rw [show D2M8K2.u4471 = KTree.node D2M8K2.u4469 (nat_lit 10126718) (nat_lit 3906817833) (nat_lit 0) D2M8K2.u4470 from rfl, totK_node, atot4469, atot4470]
  decide +kernel

theorem arows4479 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4479 = true := by
  rw [show D2M8K2.u4479 = KTree.node D2M8K2.u4477 (nat_lit 10130439) (nat_lit 3623417992) (nat_lit 0) D2M8K2.u4478 from rfl, allE_node, arows4477, irow4479, arows4478]
  all_goals rfl

theorem atot4479 : totK PD2M8K2 D2M8K2.u4479 = [0, 327216534084, 1364226624080, 1507459941499, 389701163524, 20356069654, 0, 0] := by
  rw [show D2M8K2.u4479 = KTree.node D2M8K2.u4477 (nat_lit 10130439) (nat_lit 3623417992) (nat_lit 0) D2M8K2.u4478 from rfl, totK_node, atot4477, atot4478]
  decide +kernel

theorem arows4482 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4482 = true := by
  rw [show D2M8K2.u4482 = KTree.node D2M8K2.u4480 (nat_lit 10134033) (nat_lit 1590662519) (nat_lit 0) D2M8K2.u4481 from rfl, allE_node, arows4480, irow4482, arows4481]
  all_goals rfl

theorem atot4482 : totK PD2M8K2 D2M8K2.u4482 = [0, 435720955444, 1535633607228, 1393100826904, 238292753445, 4678454933, 0, 0] := by
  rw [show D2M8K2.u4482 = KTree.node D2M8K2.u4480 (nat_lit 10134033) (nat_lit 1590662519) (nat_lit 0) D2M8K2.u4481 from rfl, totK_node, atot4480, atot4481]
  decide +kernel

theorem arows4486 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4486 = true := by
  rw [show D2M8K2.u4486 = KTree.node D2M8K2.u4484 (nat_lit 10141360) (nat_lit 3275329215) (nat_lit 0) D2M8K2.u4485 from rfl, allE_node, arows4484, irow4486, arows4485]
  all_goals rfl

theorem atot4486 : totK PD2M8K2 D2M8K2.u4486 = [0, 0, 506045343813, 1687557630941, 1173965564236, 128186453160, 1138244013, 0] := by
  rw [show D2M8K2.u4486 = KTree.node D2M8K2.u4484 (nat_lit 10141360) (nat_lit 3275329215) (nat_lit 0) D2M8K2.u4485 from rfl, totK_node, atot4484, atot4485]
  decide +kernel

theorem arows4489 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4489 = true := by
  rw [show D2M8K2.u4489 = KTree.node D2M8K2.u4487 (nat_lit 10147009) (nat_lit 1490658461) (nat_lit 0) D2M8K2.u4488 from rfl, allE_node, arows4487, irow4489, arows4488]
  all_goals rfl

theorem atot4489 : totK PD2M8K2 D2M8K2.u4489 = [0, 0, 747698346226, 1908686472845, 907736843384, 51083554133, 0, 0] := by
  rw [show D2M8K2.u4489 = KTree.node D2M8K2.u4487 (nat_lit 10147009) (nat_lit 1490658461) (nat_lit 0) D2M8K2.u4488 from rfl, totK_node, atot4487, atot4488]
  decide +kernel

theorem arows4494 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4494 = true := by
  rw [show D2M8K2.u4494 = KTree.node D2M8K2.u4492 (nat_lit 10153890) (nat_lit 2352241618) (nat_lit 2048) D2M8K2.u4493 from rfl, allE_node, arows4492, irow4494, arows4493]
  all_goals rfl

theorem atot4494 : totK PD2M8K2 D2M8K2.u4494 = [0, 0, 742412306073, 1888697585709, 904516272251, 57137169247, 0, 0] := by
  rw [show D2M8K2.u4494 = KTree.node D2M8K2.u4492 (nat_lit 10153890) (nat_lit 2352241618) (nat_lit 2048) D2M8K2.u4493 from rfl, totK_node, atot4492, atot4493]
  decide +kernel

theorem arows4497 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4497 = true := by
  rw [show D2M8K2.u4497 = KTree.node D2M8K2.u4495 (nat_lit 10160862) (nat_lit 3969889731) (nat_lit 0) D2M8K2.u4496 from rfl, allE_node, arows4495, irow4497, arows4496]
  all_goals rfl

theorem atot4497 : totK PD2M8K2 D2M8K2.u4497 = [0, 379032392427, 1056806060742, 1068319547420, 820161825496, 191134878293, 4977114383, 0] := by
  rw [show D2M8K2.u4497 = KTree.node D2M8K2.u4495 (nat_lit 10160862) (nat_lit 3969889731) (nat_lit 0) D2M8K2.u4496 from rfl, totK_node, atot4495, atot4496]
  decide +kernel

theorem arows4501 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4501 = true := by
  rw [show D2M8K2.u4501 = KTree.node D2M8K2.u4499 (nat_lit 10164924) (nat_lit 2253422824) (nat_lit 0) D2M8K2.u4500 from rfl, allE_node, arows4499, irow4501, arows4500]
  all_goals rfl

theorem atot4501 : totK PD2M8K2 D2M8K2.u4501 = [0, 421127132145, 1501646085936, 1414893491860, 323528094739, 22749189839, 0, 0] := by
  rw [show D2M8K2.u4501 = KTree.node D2M8K2.u4499 (nat_lit 10164924) (nat_lit 2253422824) (nat_lit 0) D2M8K2.u4500 from rfl, totK_node, atot4499, atot4500]
  decide +kernel

theorem arows4504 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4504 = true := by
  rw [show D2M8K2.u4504 = KTree.node D2M8K2.u4502 (nat_lit 10167798) (nat_lit 1794913801) (nat_lit 0) D2M8K2.u4503 from rfl, allE_node, arows4502, irow4504, arows4503]
  all_goals rfl

theorem atot4504 : totK PD2M8K2 D2M8K2.u4504 = [0, 424480126559, 1396293269309, 1382870831177, 420360816916, 16174684836, 0, 0] := by
  rw [show D2M8K2.u4504 = KTree.node D2M8K2.u4502 (nat_lit 10167798) (nat_lit 1794913801) (nat_lit 0) D2M8K2.u4503 from rfl, totK_node, atot4502, atot4503]
  decide +kernel

theorem arows4510 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4510 = true := by
  rw [show D2M8K2.u4510 = KTree.node D2M8K2.u4508 (nat_lit 10171160) (nat_lit 2774662807) (nat_lit 0) D2M8K2.u4509 from rfl, allE_node, arows4508, irow4510, arows4509]
  all_goals rfl

theorem atot4510 : totK PD2M8K2 D2M8K2.u4510 = [0, 330299075189, 1344478410204, 1556049499129, 383799118607, 14241856732, 0, 0] := by
  rw [show D2M8K2.u4510 = KTree.node D2M8K2.u4508 (nat_lit 10171160) (nat_lit 2774662807) (nat_lit 0) D2M8K2.u4509 from rfl, totK_node, atot4508, atot4509]
  decide +kernel

theorem arows4513 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4513 = true := by
  rw [show D2M8K2.u4513 = KTree.node D2M8K2.u4511 (nat_lit 10178534) (nat_lit 4125165185) (nat_lit 0) D2M8K2.u4512 from rfl, allE_node, arows4511, irow4513, arows4512]
  all_goals rfl

theorem atot4513 : totK PD2M8K2 D2M8K2.u4513 = [0, 440262951893, 1519784515850, 1392013196054, 288616779286, 8325947751, 0, 0] := by
  rw [show D2M8K2.u4513 = KTree.node D2M8K2.u4511 (nat_lit 10178534) (nat_lit 4125165185) (nat_lit 0) D2M8K2.u4512 from rfl, totK_node, atot4511, atot4512]
  decide +kernel

theorem arows4517 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4517 = true := by
  rw [show D2M8K2.u4517 = KTree.node D2M8K2.u4515 (nat_lit 10181984) (nat_lit 2765280588) (nat_lit 0) D2M8K2.u4516 from rfl, allE_node, arows4515, irow4517, arows4516]
  all_goals rfl

theorem atot4517 : totK PD2M8K2 D2M8K2.u4517 = [0, 0, 663899661923, 1784588483848, 992707613857, 99777169300, 1310285577, 0] := by
  rw [show D2M8K2.u4517 = KTree.node D2M8K2.u4515 (nat_lit 10181984) (nat_lit 2765280588) (nat_lit 0) D2M8K2.u4516 from rfl, totK_node, atot4515, atot4516]
  decide +kernel

theorem arows4520 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4520 = true := by
  rw [show D2M8K2.u4520 = KTree.node D2M8K2.u4518 (nat_lit 10185813) (nat_lit 1625117066) (nat_lit 0) D2M8K2.u4519 from rfl, allE_node, arows4518, irow4520, arows4519]
  all_goals rfl

theorem atot4520 : totK PD2M8K2 D2M8K2.u4520 = [0, 0, 590616803312, 1753573593436, 1205291421742, 106502306886, 0, 0] := by
  rw [show D2M8K2.u4520 = KTree.node D2M8K2.u4518 (nat_lit 10185813) (nat_lit 1625117066) (nat_lit 0) D2M8K2.u4519 from rfl, totK_node, atot4518, atot4519]
  decide +kernel

theorem arows4525 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4525 = true := by
  rw [show D2M8K2.u4525 = KTree.node D2M8K2.u4523 (nat_lit 10190424) (nat_lit 2757452413) (nat_lit 0) D2M8K2.u4524 from rfl, allE_node, arows4523, irow4525, arows4524]
  all_goals rfl

theorem atot4525 : totK PD2M8K2 D2M8K2.u4525 = [0, 0, 473644665691, 1565834824357, 1323030494386, 218265820583, 4879840392, 0] := by
  rw [show D2M8K2.u4525 = KTree.node D2M8K2.u4523 (nat_lit 10190424) (nat_lit 2757452413) (nat_lit 0) D2M8K2.u4524 from rfl, totK_node, atot4523, atot4524]
  decide +kernel

theorem arows4528 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4528 = true := by
  rw [show D2M8K2.u4528 = KTree.node D2M8K2.u4526 (nat_lit 10198779) (nat_lit 3104845869) (nat_lit 0) D2M8K2.u4527 from rfl, allE_node, arows4526, irow4528, arows4527]
  all_goals rfl

theorem atot4528 : totK PD2M8K2 D2M8K2.u4528 = [0, 0, 546260149603, 1712546226863, 1237395089793, 150278451957, 1444560764, 0] := by
  rw [show D2M8K2.u4528 = KTree.node D2M8K2.u4526 (nat_lit 10198779) (nat_lit 3104845869) (nat_lit 0) D2M8K2.u4527 from rfl, totK_node, atot4526, atot4527]
  decide +kernel

theorem arows4532 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4532 = true := by
  rw [show D2M8K2.u4532 = KTree.node D2M8K2.u4530 (nat_lit 10201986) (nat_lit 2675062999) (nat_lit 512) D2M8K2.u4531 from rfl, allE_node, arows4530, irow4532, arows4531]
  all_goals rfl

theorem atot4532 : totK PD2M8K2 D2M8K2.u4532 = [0, 0, 345258147191, 1353065376546, 1435464218214, 378436828630, 18014152641, 0] := by
  rw [show D2M8K2.u4532 = KTree.node D2M8K2.u4530 (nat_lit 10201986) (nat_lit 2675062999) (nat_lit 512) D2M8K2.u4531 from rfl, totK_node, atot4530, atot4531]
  decide +kernel

theorem arows4535 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4535 = true := by
  rw [show D2M8K2.u4535 = KTree.node D2M8K2.u4533 (nat_lit 10209123) (nat_lit 2752052725) (nat_lit 0) D2M8K2.u4534 from rfl, allE_node, arows4533, irow4535, arows4534]
  all_goals rfl

theorem atot4535 : totK PD2M8K2 D2M8K2.u4535 = [0, 0, 493358511674, 1646965883203, 1302704739051, 145707612024, 1369150432, 0] := by
  rw [show D2M8K2.u4535 = KTree.node D2M8K2.u4533 (nat_lit 10209123) (nat_lit 2752052725) (nat_lit 0) D2M8K2.u4534 from rfl, totK_node, atot4533, atot4534]
  decide +kernel

theorem arows4542 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4542 = true := by
  rw [show D2M8K2.u4542 = KTree.node D2M8K2.u4540 (nat_lit 10216303) (nat_lit 2383849312) (nat_lit 0) D2M8K2.u4541 from rfl, allE_node, arows4540, irow4542, arows4541]
  all_goals rfl

theorem atot4542 : totK PD2M8K2 D2M8K2.u4542 = [0, 0, 396612246273, 1563785667311, 1398218146949, 186661981990, 2260824724, 0] := by
  rw [show D2M8K2.u4542 = KTree.node D2M8K2.u4540 (nat_lit 10216303) (nat_lit 2383849312) (nat_lit 0) D2M8K2.u4541 from rfl, totK_node, atot4540, atot4541]
  decide +kernel

theorem arows4545 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4545 = true := by
  rw [show D2M8K2.u4545 = KTree.node D2M8K2.u4543 (nat_lit 10220124) (nat_lit 3140816228) (nat_lit 0) D2M8K2.u4544 from rfl, allE_node, arows4543, irow4545, arows4544]
  all_goals rfl

theorem atot4545 : totK PD2M8K2 D2M8K2.u4545 = [0, 0, 614956942282, 1752457312856, 1198250034957, 102794261011, 0, 0] := by
  rw [show D2M8K2.u4545 = KTree.node D2M8K2.u4543 (nat_lit 10220124) (nat_lit 3140816228) (nat_lit 0) D2M8K2.u4544 from rfl, totK_node, atot4543, atot4544]
  decide +kernel

theorem arows4549 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4549 = true := by
  rw [show D2M8K2.u4549 = KTree.node D2M8K2.u4547 (nat_lit 10249392) (nat_lit 3290808411) (nat_lit 0) D2M8K2.u4548 from rfl, allE_node, arows4547, irow4549, arows4548]
  all_goals rfl

theorem atot4549 : totK PD2M8K2 D2M8K2.u4549 = [0, 0, 301080743377, 1214783343582, 1501481590165, 573011188075, 37499607470, 0] := by
  rw [show D2M8K2.u4549 = KTree.node D2M8K2.u4547 (nat_lit 10249392) (nat_lit 3290808411) (nat_lit 0) D2M8K2.u4548 from rfl, totK_node, atot4547, atot4548]
  decide +kernel

theorem arows4552 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4552 = true := by
  rw [show D2M8K2.u4552 = KTree.node D2M8K2.u4550 (nat_lit 10252200) (nat_lit 3368233183) (nat_lit 0) D2M8K2.u4551 from rfl, allE_node, arows4550, irow4552, arows4551]
  all_goals rfl

theorem atot4552 : totK PD2M8K2 D2M8K2.u4552 = [0, 0, 446124351700, 1516813094148, 1393247480543, 284573549315, 9087311183, 0] := by
  rw [show D2M8K2.u4552 = KTree.node D2M8K2.u4550 (nat_lit 10252200) (nat_lit 3368233183) (nat_lit 0) D2M8K2.u4551 from rfl, totK_node, atot4550, atot4551]
  decide +kernel

theorem arows4557 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4557 = true := by
  rw [show D2M8K2.u4557 = KTree.node D2M8K2.u4555 (nat_lit 10256625) (nat_lit 1837442505) (nat_lit 0) D2M8K2.u4556 from rfl, allE_node, arows4555, irow4557, arows4556]
  all_goals rfl

theorem atot4557 : totK PD2M8K2 D2M8K2.u4557 = [0, 0, 474695577890, 1561106681934, 1369811776521, 255731361911, 5439011083, 0] := by
  rw [show D2M8K2.u4557 = KTree.node D2M8K2.u4555 (nat_lit 10256625) (nat_lit 1837442505) (nat_lit 0) D2M8K2.u4556 from rfl, totK_node, atot4555, atot4556]
  decide +kernel

theorem arows4560 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4560 = true := by
  rw [show D2M8K2.u4560 = KTree.node D2M8K2.u4558 (nat_lit 10260073) (nat_lit 1389124103) (nat_lit 0) D2M8K2.u4559 from rfl, allE_node, arows4558, irow4560, arows4559]
  all_goals rfl

theorem atot4560 : totK PD2M8K2 D2M8K2.u4560 = [0, 0, 463308430893, 1629355871455, 1349819708917, 201480134680, 2585032425, 0] := by
  rw [show D2M8K2.u4560 = KTree.node D2M8K2.u4558 (nat_lit 10260073) (nat_lit 1389124103) (nat_lit 0) D2M8K2.u4559 from rfl, totK_node, atot4558, atot4559]
  decide +kernel

theorem arows4564 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4564 = true := by
  rw [show D2M8K2.u4564 = KTree.node D2M8K2.u4562 (nat_lit 10263503) (nat_lit 2129976506) (nat_lit 0) D2M8K2.u4563 from rfl, allE_node, arows4562, irow4564, arows4563]
  all_goals rfl

theorem atot4564 : totK PD2M8K2 D2M8K2.u4564 = [0, 0, 379094084995, 1384006790795, 1429946347317, 373088573422, 13634672981, 0] := by
  rw [show D2M8K2.u4564 = KTree.node D2M8K2.u4562 (nat_lit 10263503) (nat_lit 2129976506) (nat_lit 0) D2M8K2.u4563 from rfl, totK_node, atot4562, atot4563]
  decide +kernel

theorem arows4567 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4567 = true := by
  rw [show D2M8K2.u4567 = KTree.node D2M8K2.u4565 (nat_lit 10288231) (nat_lit 1822827962) (nat_lit 128) D2M8K2.u4566 from rfl, allE_node, arows4565, irow4567, arows4566]
  all_goals rfl

theorem atot4567 : totK PD2M8K2 D2M8K2.u4567 = [0, 0, 494649843251, 1632262440863, 1312248537901, 161939856252, 1334361349, 0] := by
  rw [show D2M8K2.u4567 = KTree.node D2M8K2.u4565 (nat_lit 10288231) (nat_lit 1822827962) (nat_lit 128) D2M8K2.u4566 from rfl, totK_node, atot4565, atot4566]
  decide +kernel

theorem arows4573 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4573 = true := by
  rw [show D2M8K2.u4573 = KTree.node D2M8K2.u4571 (nat_lit 10291476) (nat_lit 2087113344) (nat_lit 0) D2M8K2.u4572 from rfl, allE_node, arows4571, irow4573, arows4572]
  all_goals rfl

theorem atot4573 : totK PD2M8K2 D2M8K2.u4573 = [0, 0, 356533235454, 1317967731741, 1479889648505, 470738294427, 24088924277, 0] := by
  rw [show D2M8K2.u4573 = KTree.node D2M8K2.u4571 (nat_lit 10291476) (nat_lit 2087113344) (nat_lit 0) D2M8K2.u4572 from rfl, totK_node, atot4571, atot4572]
  decide +kernel

theorem arows4576 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4576 = true := by
  rw [show D2M8K2.u4576 = KTree.node D2M8K2.u4574 (nat_lit 10294384) (nat_lit 3445111236) (nat_lit 0) D2M8K2.u4575 from rfl, allE_node, arows4574, irow4576, arows4575]
  all_goals rfl

theorem atot4576 : totK PD2M8K2 D2M8K2.u4576 = [0, 0, 362287530623, 1411692236317, 1464493603455, 336355737239, 13049727234, 0] := by
  rw [show D2M8K2.u4576 = KTree.node D2M8K2.u4574 (nat_lit 10294384) (nat_lit 3445111236) (nat_lit 0) D2M8K2.u4575 from rfl, totK_node, atot4574, atot4575]
  decide +kernel

theorem arows4580 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4580 = true := by
  rw [show D2M8K2.u4580 = KTree.node D2M8K2.u4578 (nat_lit 10301223) (nat_lit 2435372169) (nat_lit 0) D2M8K2.u4579 from rfl, allE_node, arows4578, irow4580, arows4579]
  all_goals rfl

theorem atot4580 : totK PD2M8K2 D2M8K2.u4580 = [0, 0, 471977691443, 1554653949831, 1329495405980, 215967591093, 4846308403, 0] := by
  rw [show D2M8K2.u4580 = KTree.node D2M8K2.u4578 (nat_lit 10301223) (nat_lit 2435372169) (nat_lit 0) D2M8K2.u4579 from rfl, totK_node, atot4578, atot4579]
  decide +kernel

theorem arows4583 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4583 = true := by
  rw [show D2M8K2.u4583 = KTree.node D2M8K2.u4581 (nat_lit 10304749) (nat_lit 1010335783) (nat_lit 0) D2M8K2.u4582 from rfl, allE_node, arows4581, irow4583, arows4582]
  all_goals rfl

theorem atot4583 : totK PD2M8K2 D2M8K2.u4583 = [0, 0, 166094524244, 1161530854361, 1705380550159, 512755712258, 18438258534, 0] := by
  rw [show D2M8K2.u4583 = KTree.node D2M8K2.u4581 (nat_lit 10304749) (nat_lit 1010335783) (nat_lit 0) D2M8K2.u4582 from rfl, totK_node, atot4581, atot4582]
  decide +kernel

theorem arows4588 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4588 = true := by
  rw [show D2M8K2.u4588 = KTree.node D2M8K2.u4586 (nat_lit 10310245) (nat_lit 751690237) (nat_lit 2) D2M8K2.u4587 from rfl, allE_node, arows4586, irow4588, arows4587]
  all_goals rfl

theorem atot4588 : totK PD2M8K2 D2M8K2.u4588 = [0, 0, 0, 813860361624, 1911271926568, 804569272434, 48256691634, 0] := by
  rw [show D2M8K2.u4588 = KTree.node D2M8K2.u4586 (nat_lit 10310245) (nat_lit 751690237) (nat_lit 2) D2M8K2.u4587 from rfl, totK_node, atot4586, atot4587]
  decide +kernel

theorem arows4591 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4591 = true := by
  rw [show D2M8K2.u4591 = KTree.node D2M8K2.u4589 (nat_lit 10315153) (nat_lit 1469321292) (nat_lit 0) D2M8K2.u4590 from rfl, allE_node, arows4589, irow4591, arows4590]
  all_goals rfl

theorem atot4591 : totK PD2M8K2 D2M8K2.u4591 = [0, 0, 0, 452565776637, 1573907128117, 1265342866304, 224609358166, 5717851365] := by
  rw [show D2M8K2.u4591 = KTree.node D2M8K2.u4589 (nat_lit 10315153) (nat_lit 1469321292) (nat_lit 0) D2M8K2.u4590 from rfl, totK_node, atot4589, atot4590]
  decide +kernel

theorem arows4595 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4595 = true := by
  rw [show D2M8K2.u4595 = KTree.node D2M8K2.u4593 (nat_lit 10322612) (nat_lit 3702992746) (nat_lit 0) D2M8K2.u4594 from rfl, allE_node, arows4593, irow4595, arows4594]
  all_goals rfl

theorem atot4595 : totK PD2M8K2 D2M8K2.u4595 = [0, 0, 0, 565646952326, 1717990452773, 1079164757864, 122486992894, 1330264907] := by
  rw [show D2M8K2.u4595 = KTree.node D2M8K2.u4593 (nat_lit 10322612) (nat_lit 3702992746) (nat_lit 0) D2M8K2.u4594 from rfl, totK_node, atot4593, atot4594]
  decide +kernel

theorem arows4598 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4598 = true := by
  rw [show D2M8K2.u4598 = KTree.node D2M8K2.u4596 (nat_lit 10369501) (nat_lit 1212018760) (nat_lit 0) D2M8K2.u4597 from rfl, allE_node, arows4596, irow4598, arows4597]
  all_goals rfl

theorem atot4598 : totK PD2M8K2 D2M8K2.u4598 = [0, 0, 478410727792, 1544497405795, 1300242111228, 219774647899, 9012491954, 0] := by
  rw [show D2M8K2.u4598 = KTree.node D2M8K2.u4596 (nat_lit 10369501) (nat_lit 1212018760) (nat_lit 0) D2M8K2.u4597 from rfl, totK_node, atot4596, atot4597]
  decide +kernel

theorem arows4608 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4608 = true := by
  rw [show D2M8K2.u4608 = KTree.node D2M8K2.u4606 (nat_lit 10373603) (nat_lit 2930223241) (nat_lit 0) D2M8K2.u4607 from rfl, allE_node, arows4606, irow4608, arows4607]
  all_goals rfl

theorem atot4608 : totK PD2M8K2 D2M8K2.u4608 = [0, 0, 396823531221, 1453677597444, 1404985590048, 372961677841, 15013989272, 0] := by
  rw [show D2M8K2.u4608 = KTree.node D2M8K2.u4606 (nat_lit 10373603) (nat_lit 2930223241) (nat_lit 0) D2M8K2.u4607 from rfl, totK_node, atot4606, atot4607]
  decide +kernel

theorem arows4611 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4611 = true := by
  rw [show D2M8K2.u4611 = KTree.node D2M8K2.u4609 (nat_lit 10376701) (nat_lit 1225601877) (nat_lit 0) D2M8K2.u4610 from rfl, allE_node, arows4609, irow4611, arows4610]
  all_goals rfl

theorem atot4611 : totK PD2M8K2 D2M8K2.u4611 = [0, 0, 405813862478, 1420403068620, 1417976539492, 326749977764, 13049727234, 0] := by
  rw [show D2M8K2.u4611 = KTree.node D2M8K2.u4609 (nat_lit 10376701) (nat_lit 1225601877) (nat_lit 0) D2M8K2.u4610 from rfl, totK_node, atot4609, atot4610]
  decide +kernel

theorem arows4615 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4615 = true := by
  rw [show D2M8K2.u4615 = KTree.node D2M8K2.u4613 (nat_lit 10380995) (nat_lit 2602939613) (nat_lit 0) D2M8K2.u4614 from rfl, allE_node, arows4613, irow4615, arows4614]
  all_goals rfl

theorem atot4615 : totK PD2M8K2 D2M8K2.u4615 = [0, 0, 520500178092, 1677751379397, 1281548677601, 160321082406, 1334898114, 0] := by
  rw [show D2M8K2.u4615 = KTree.node D2M8K2.u4613 (nat_lit 10380995) (nat_lit 2602939613) (nat_lit 0) D2M8K2.u4614 from rfl, totK_node, atot4613, atot4614]
  decide +kernel

theorem arows4618 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4618 = true := by
  rw [show D2M8K2.u4618 = KTree.node D2M8K2.u4616 (nat_lit 10384489) (nat_lit 1478864762) (nat_lit 0) D2M8K2.u4617 from rfl, allE_node, arows4616, irow4618, arows4617]
  all_goals rfl

theorem atot4618 : totK PD2M8K2 D2M8K2.u4618 = [0, 0, 175097542693, 1205637301787, 1717667184324, 438063887415, 10762267735, 0] := by
  rw [show D2M8K2.u4618 = KTree.node D2M8K2.u4616 (nat_lit 10384489) (nat_lit 1478864762) (nat_lit 0) D2M8K2.u4617 from rfl, totK_node, atot4616, atot4617]
  decide +kernel

theorem arows4623 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4623 = true := by
  rw [show D2M8K2.u4623 = KTree.node D2M8K2.u4621 (nat_lit 10393774) (nat_lit 4003934044) (nat_lit 0) D2M8K2.u4622 from rfl, allE_node, arows4621, irow4623, arows4622]
  all_goals rfl

theorem atot4623 : totK PD2M8K2 D2M8K2.u4623 = [0, 0, 0, 861034946638, 1897524654263, 776801201479, 40939083783, 0] := by
  rw [show D2M8K2.u4623 = KTree.node D2M8K2.u4621 (nat_lit 10393774) (nat_lit 4003934044) (nat_lit 0) D2M8K2.u4622 from rfl, totK_node, atot4621, atot4622]
  decide +kernel

theorem arows4626 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4626 = true := by
  rw [show D2M8K2.u4626 = KTree.node D2M8K2.u4624 (nat_lit 10403043) (nat_lit 3461139842) (nat_lit 0) D2M8K2.u4625 from rfl, allE_node, arows4624, irow4626, arows4625]
  all_goals rfl

theorem atot4626 : totK PD2M8K2 D2M8K2.u4626 = [0, 0, 0, 762679814866, 1875075991873, 834776133661, 52261183970, 0] := by
  rw [show D2M8K2.u4626 = KTree.node D2M8K2.u4624 (nat_lit 10403043) (nat_lit 3461139842) (nat_lit 0) D2M8K2.u4625 from rfl, totK_node, atot4624, atot4625]
  decide +kernel

theorem arows4630 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4630 = true := by
  rw [show D2M8K2.u4630 = KTree.node D2M8K2.u4628 (nat_lit 10410959) (nat_lit 2156116774) (nat_lit 0) D2M8K2.u4629 from rfl, allE_node, arows4628, irow4630, arows4629]
  all_goals rfl

theorem atot4630 : totK PD2M8K2 D2M8K2.u4630 = [0, 0, 470418502887, 1376554458545, 1231503985026, 439494280224, 67933695666, 1394496256] := by
  rw [show D2M8K2.u4630 = KTree.node D2M8K2.u4628 (nat_lit 10410959) (nat_lit 2156116774) (nat_lit 0) D2M8K2.u4629 from rfl, totK_node, atot4628, atot4629]
  decide +kernel

theorem arows4633 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4633 = true := by
  rw [show D2M8K2.u4633 = KTree.node D2M8K2.u4631 (nat_lit 10414972) (nat_lit 3914972825) (nat_lit 0) D2M8K2.u4632 from rfl, allE_node, arows4631, irow4633, arows4632]
  all_goals rfl

theorem atot4633 : totK PD2M8K2 D2M8K2.u4633 = [0, 0, 327267129077, 1333085999153, 1514809967926, 458333284804, 25977880579, 0] := by
  rw [show D2M8K2.u4633 = KTree.node D2M8K2.u4631 (nat_lit 10414972) (nat_lit 3914972825) (nat_lit 0) D2M8K2.u4632 from rfl, totK_node, atot4631, atot4632]
  decide +kernel

theorem arows4639 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4639 = true := by
  rw [show D2M8K2.u4639 = KTree.node D2M8K2.u4637 (nat_lit 10417780) (nat_lit 3748576689) (nat_lit 0) D2M8K2.u4638 from rfl, allE_node, arows4637, irow4639, arows4638]
  all_goals rfl

theorem atot4639 : totK PD2M8K2 D2M8K2.u4639 = [0, 0, 422396471863, 1444985905488, 1377772493990, 342820975074, 14977117772, 0] := by
  rw [show D2M8K2.u4639 = KTree.node D2M8K2.u4637 (nat_lit 10417780) (nat_lit 3748576689) (nat_lit 0) D2M8K2.u4638 from rfl, totK_node, atot4637, atot4638]
  decide +kernel

theorem arows4642 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4642 = true := by
  rw [show D2M8K2.u4642 = KTree.node D2M8K2.u4640 (nat_lit 10421891) (nat_lit 2839553289) (nat_lit 0) D2M8K2.u4641 from rfl, allE_node, arows4640, irow4642, arows4641]
  all_goals rfl

theorem atot4642 : totK PD2M8K2 D2M8K2.u4642 = [0, 0, 557453466928, 1655116126498, 1296031381462, 199279301887, 1510868091, 0] := by
  rw [show D2M8K2.u4642 = KTree.node D2M8K2.u4640 (nat_lit 10421891) (nat_lit 2839553289) (nat_lit 0) D2M8K2.u4641 from rfl, totK_node, atot4640, atot4641]
  decide +kernel

theorem arows4646 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4646 = true := by
  rw [show D2M8K2.u4646 = KTree.node D2M8K2.u4644 (nat_lit 10429064) (nat_lit 3145088960) (nat_lit 0) D2M8K2.u4645 from rfl, allE_node, arows4644, irow4646, arows4645]
  all_goals rfl

theorem atot4646 : totK PD2M8K2 D2M8K2.u4646 = [0, 162906912950, 544052793693, 1136854223038, 1346973174476, 402110771196, 18207879604, 0] := by
  rw [show D2M8K2.u4646 = KTree.node D2M8K2.u4644 (nat_lit 10429064) (nat_lit 3145088960) (nat_lit 0) D2M8K2.u4645 from rfl, totK_node, atot4644, atot4645]
  decide +kernel

theorem arows4649 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4649 = true := by
  rw [show D2M8K2.u4649 = KTree.node D2M8K2.u4647 (nat_lit 10452888) (nat_lit 3570892849) (nat_lit 0) D2M8K2.u4648 from rfl, allE_node, arows4647, irow4649, arows4648]
  all_goals rfl

theorem atot4649 : totK PD2M8K2 D2M8K2.u4649 = [0, 437029783570, 1585142905509, 1386378862860, 192991227073, 1369150432, 0, 0] := by
  rw [show D2M8K2.u4649 = KTree.node D2M8K2.u4647 (nat_lit 10452888) (nat_lit 3570892849) (nat_lit 0) D2M8K2.u4648 from rfl, totK_node, atot4647, atot4648]
  decide +kernel

theorem arows4654 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4654 = true := by
  rw [show D2M8K2.u4654 = KTree.node D2M8K2.u4652 (nat_lit 10463449) (nat_lit 1217640296) (nat_lit 0) D2M8K2.u4653 from rfl, allE_node, arows4652, irow4654, arows4653]
  all_goals rfl

theorem atot4654 : totK PD2M8K2 D2M8K2.u4654 = [0, 400233099911, 1431564600773, 1410198290035, 330422922563, 13250685261, 0, 0] := by
  rw [show D2M8K2.u4654 = KTree.node D2M8K2.u4652 (nat_lit 10463449) (nat_lit 1217640296) (nat_lit 0) D2M8K2.u4653 from rfl, totK_node, atot4652, atot4653]
  decide +kernel

theorem arows4657 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4657 = true := by
  rw [show D2M8K2.u4657 = KTree.node D2M8K2.u4655 (nat_lit 10466880) (nat_lit 2710629201) (nat_lit 0) D2M8K2.u4656 from rfl, allE_node, arows4655, irow4657, arows4656]
  all_goals rfl

theorem atot4657 : totK PD2M8K2 D2M8K2.u4657 = [0, 464498143796, 1540424018706, 1359783399636, 225880068532, 4980514959, 0, 0] := by
  rw [show D2M8K2.u4657 = KTree.node D2M8K2.u4655 (nat_lit 10466880) (nat_lit 2710629201) (nat_lit 0) D2M8K2.u4656 from rfl, totK_node, atot4655, atot4656]
  decide +kernel

theorem arows4661 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4661 = true := by
  rw [show D2M8K2.u4661 = KTree.node D2M8K2.u4659 (nat_lit 10470652) (nat_lit 3954847455) (nat_lit 0) D2M8K2.u4660 from rfl, allE_node, arows4659, irow4661, arows4660]
  all_goals rfl

theorem atot4661 : totK PD2M8K2 D2M8K2.u4661 = [0, 179036101606, 1184393684017, 1731484159489, 489696932506, 16538199900, 0, 0] := by
  rw [show D2M8K2.u4661 = KTree.node D2M8K2.u4659 (nat_lit 10470652) (nat_lit 3954847455) (nat_lit 0) D2M8K2.u4660 from rfl, totK_node, atot4659, atot4660]
  decide +kernel

theorem arows4664 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4664 = true := by
  rw [show D2M8K2.u4664 = KTree.node D2M8K2.u4662 (nat_lit 10474396) (nat_lit 1943518921) (nat_lit 32) D2M8K2.u4663 from rfl, allE_node, arows4662, irow4664, arows4663]
  all_goals rfl

theorem atot4664 : totK PD2M8K2 D2M8K2.u4664 = [0, 0, 503394977872, 1676341849403, 1196073913106, 133706670621, 1369150432, 0] := by
  rw [show D2M8K2.u4664 = KTree.node D2M8K2.u4662 (nat_lit 10474396) (nat_lit 1943518921) (nat_lit 32) D2M8K2.u4663 from rfl, totK_node, atot4662, atot4663]
  decide +kernel

theorem arows4671 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4671 = true := by
  rw [show D2M8K2.u4671 = KTree.node D2M8K2.u4669 (nat_lit 10486441) (nat_lit 1496149245) (nat_lit 0) D2M8K2.u4670 from rfl, allE_node, arows4669, irow4671, arows4670]
  all_goals rfl

theorem atot4671 : totK PD2M8K2 D2M8K2.u4671 = [0, 0, 726736899848, 1913881562870, 869045634798, 43655229506, 0, 0] := by
  rw [show D2M8K2.u4671 = KTree.node D2M8K2.u4669 (nat_lit 10486441) (nat_lit 1496149245) (nat_lit 0) D2M8K2.u4670 from rfl, totK_node, atot4669, atot4670]
  decide +kernel

theorem arows4674 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4674 = true := by
  rw [show D2M8K2.u4674 = KTree.node D2M8K2.u4672 (nat_lit 10496704) (nat_lit 3280958396) (nat_lit 0) D2M8K2.u4673 from rfl, allE_node, arows4672, irow4674, arows4673]
  all_goals rfl

theorem atot4674 : totK PD2M8K2 D2M8K2.u4674 = [0, 445106442645, 1416741793852, 1340615694404, 448424643515, 34619752137, 0, 0] := by
  rw [show D2M8K2.u4674 = KTree.node D2M8K2.u4672 (nat_lit 10496704) (nat_lit 3280958396) (nat_lit 0) D2M8K2.u4673 from rfl, totK_node, atot4672, atot4673]
  decide +kernel

theorem arows4678 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4678 = true := by
  rw [show D2M8K2.u4678 = KTree.node D2M8K2.u4676 (nat_lit 10499702) (nat_lit 3992745006) (nat_lit 0) D2M8K2.u4677 from rfl, allE_node, arows4676, irow4678, arows4677]
  all_goals rfl

theorem atot4678 : totK PD2M8K2 D2M8K2.u4678 = [0, 346917363688, 1317206687938, 1523757787896, 481540472706, 20423179516, 0, 0] := by
  rw [show D2M8K2.u4678 = KTree.node D2M8K2.u4676 (nat_lit 10499702) (nat_lit 3992745006) (nat_lit 0) D2M8K2.u4677 from rfl, totK_node, atot4676, atot4677]
  decide +kernel

theorem arows4681 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4681 = true := by
  rw [show D2M8K2.u4681 = KTree.node D2M8K2.u4679 (nat_lit 10503319) (nat_lit 2337933458) (nat_lit 0) D2M8K2.u4680 from rfl, allE_node, arows4679, irow4681, arows4680]
  all_goals rfl

theorem atot4681 : totK PD2M8K2 D2M8K2.u4681 = [0, 426886118679, 1472142015456, 1406192341989, 320768997460, 10251579236, 0, 0] := by
  rw [show D2M8K2.u4681 = KTree.node D2M8K2.u4679 (nat_lit 10503319) (nat_lit 2337933458) (nat_lit 0) D2M8K2.u4680 from rfl, totK_node, atot4679, atot4680]
  decide +kernel

theorem arows4686 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4686 = true := by
  rw [show D2M8K2.u4686 = KTree.node D2M8K2.u4684 (nat_lit 10506701) (nat_lit 2196136473) (nat_lit 0) D2M8K2.u4685 from rfl, allE_node, arows4684, irow4686, arows4685]
  all_goals rfl

theorem atot4686 : totK PD2M8K2 D2M8K2.u4686 = [0, 411869194812, 1459890931187, 1395484675603, 317449383833, 13136429951, 0, 0] := by
  rw [show D2M8K2.u4686 = KTree.node D2M8K2.u4684 (nat_lit 10506701) (nat_lit 2196136473) (nat_lit 0) D2M8K2.u4685 from rfl, totK_node, atot4684, atot4685]
  decide +kernel

theorem arows4689 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4689 = true := by
  rw [show D2M8K2.u4689 = KTree.node D2M8K2.u4687 (nat_lit 10510238) (nat_lit 3825812487) (nat_lit 0) D2M8K2.u4688 from rfl, allE_node, arows4687, irow4689, arows4688]
  all_goals rfl

theorem atot4689 : totK PD2M8K2 D2M8K2.u4689 = [0, 417525337235, 1519629021031, 1452476714595, 270494765155, 5148576759, 0, 0] := by
  rw [show D2M8K2.u4689 = KTree.node D2M8K2.u4687 (nat_lit 10510238) (nat_lit 3825812487) (nat_lit 0) D2M8K2.u4688 from rfl, totK_node, atot4687, atot4688]
  decide +kernel

theorem arows4693 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4693 = true := by
  rw [show D2M8K2.u4693 = KTree.node D2M8K2.u4691 (nat_lit 10517150) (nat_lit 3831962033) (nat_lit 0) D2M8K2.u4692 from rfl, allE_node, arows4691, irow4693, arows4692]
  all_goals rfl

theorem atot4693 : totK PD2M8K2 D2M8K2.u4693 = [0, 0, 737201056452, 1883202023559, 968592326869, 71186662791, 0, 0] := by
  rw [show D2M8K2.u4693 = KTree.node D2M8K2.u4691 (nat_lit 10517150) (nat_lit 3831962033) (nat_lit 0) D2M8K2.u4692 from rfl, totK_node, atot4691, atot4692]
  decide +kernel

theorem arows4696 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4696 = true := by
  rw [show D2M8K2.u4696 = KTree.node D2M8K2.u4694 (nat_lit 10519856) (nat_lit 2836570750) (nat_lit 0) D2M8K2.u4695 from rfl, allE_node, arows4694, irow4696, arows4695]
  all_goals rfl

theorem atot4696 : totK PD2M8K2 D2M8K2.u4696 = [0, 0, 345816497617, 1225226343288, 1476421040405, 555410554319, 36921873854, 0] := by
  rw [show D2M8K2.u4696 = KTree.node D2M8K2.u4694 (nat_lit 10519856) (nat_lit 2836570750) (nat_lit 0) D2M8K2.u4695 from rfl, totK_node, atot4694, atot4695]
  decide +kernel

theorem arows4702 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4702 = true := by
  rw [show D2M8K2.u4702 = KTree.node D2M8K2.u4700 (nat_lit 10523870) (nat_lit 3936270956) (nat_lit 0) D2M8K2.u4701 from rfl, allE_node, arows4700, irow4702, arows4701]
  all_goals rfl

theorem atot4702 : totK PD2M8K2 D2M8K2.u4702 = [0, 0, 425257499766, 1547876617769, 1415593779168, 240789034233, 5159868635, 0] := by
  rw [show D2M8K2.u4702 = KTree.node D2M8K2.u4700 (nat_lit 10523870) (nat_lit 3936270956) (nat_lit 0) D2M8K2.u4701 from rfl, totK_node, atot4700, atot4701]
  decide +kernel

theorem arows4705 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4705 = true := by
  rw [show D2M8K2.u4705 = KTree.node D2M8K2.u4703 (nat_lit 10527366) (nat_lit 3797779054) (nat_lit 0) D2M8K2.u4704 from rfl, allE_node, arows4703, irow4705, arows4704]
  all_goals rfl

theorem atot4705 : totK PD2M8K2 D2M8K2.u4705 = [0, 0, 410893352429, 1513076437091, 1404791017031, 259018816539, 5218872685, 0] := by
  rw [show D2M8K2.u4705 = KTree.node D2M8K2.u4703 (nat_lit 10527366) (nat_lit 3797779054) (nat_lit 0) D2M8K2.u4704 from rfl, totK_node, atot4703, atot4704]
  decide +kernel

theorem arows4709 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4709 = true := by
  rw [show D2M8K2.u4709 = KTree.node D2M8K2.u4707 (nat_lit 10531012) (nat_lit 3767026690) (nat_lit 0) D2M8K2.u4708 from rfl, allE_node, arows4707, irow4709, arows4708]
  all_goals rfl

theorem atot4709 : totK PD2M8K2 D2M8K2.u4709 = [0, 0, 416435115206, 1596887076246, 1444757000608, 208737134416, 1415142070, 0] := by
  rw [show D2M8K2.u4709 = KTree.node D2M8K2.u4707 (nat_lit 10531012) (nat_lit 3767026690) (nat_lit 0) D2M8K2.u4708 from rfl, totK_node, atot4707, atot4708]
  decide +kernel

theorem arows4712 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4712 = true := by
  rw [show D2M8K2.u4712 = KTree.node D2M8K2.u4710 (nat_lit 10576316) (nat_lit 3369582561) (nat_lit 0) D2M8K2.u4711 from rfl, allE_node, arows4710, irow4712, arows4711]
  all_goals rfl

theorem atot4712 : totK PD2M8K2 D2M8K2.u4712 = [0, 397564749128, 1201827324147, 1045148458268, 654518619045, 226337861730, 9302370699, 0] := by
  rw [show D2M8K2.u4712 = KTree.node D2M8K2.u4710 (nat_lit 10576316) (nat_lit 3369582561) (nat_lit 0) D2M8K2.u4711 from rfl, totK_node, atot4710, atot4711]
  decide +kernel

theorem arows4717 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4717 = true := by
  rw [show D2M8K2.u4717 = KTree.node D2M8K2.u4715 (nat_lit 10579924) (nat_lit 2671075544) (nat_lit 0) D2M8K2.u4716 from rfl, allE_node, arows4715, irow4717, arows4716]
  all_goals rfl

theorem atot4717 : totK PD2M8K2 D2M8K2.u4717 = [0, 426968254075, 1484023879893, 1383602864835, 347300670310, 25330507241, 0, 0] := by
  rw [show D2M8K2.u4717 = KTree.node D2M8K2.u4715 (nat_lit 10579924) (nat_lit 2671075544) (nat_lit 0) D2M8K2.u4716 from rfl, totK_node, atot4715, atot4716]
  decide +kernel

theorem arows4720 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4720 = true := by
  rw [show D2M8K2.u4720 = KTree.node D2M8K2.u4718 (nat_lit 10586141) (nat_lit 1977025151) (nat_lit 0) D2M8K2.u4719 from rfl, allE_node, arows4718, irow4720, arows4719]
  all_goals rfl

theorem atot4720 : totK PD2M8K2 D2M8K2.u4720 = [0, 446026114301, 1472545564591, 1371454601401, 355163924378, 12206425282, 0, 0] := by
  rw [show D2M8K2.u4720 = KTree.node D2M8K2.u4718 (nat_lit 10586141) (nat_lit 1977025151) (nat_lit 0) D2M8K2.u4719 from rfl, totK_node, atot4718, atot4719]
  decide +kernel

theorem arows4724 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4724 = true := by
  rw [show D2M8K2.u4724 = KTree.node D2M8K2.u4722 (nat_lit 10589385) (nat_lit 1734291108) (nat_lit 0) D2M8K2.u4723 from rfl, allE_node, arows4722, irow4724, arows4723]
  all_goals rfl

theorem atot4724 : totK PD2M8K2 D2M8K2.u4724 = [0, 416110203809, 1436088519525, 1392884255621, 337059746900, 13250685261, 0, 0] := by
  rw [show D2M8K2.u4724 = KTree.node D2M8K2.u4722 (nat_lit 10589385) (nat_lit 1734291108) (nat_lit 0) D2M8K2.u4723 from rfl, totK_node, atot4722, atot4723]
  decide +kernel

theorem arows4727 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4727 = true := by
  rw [show D2M8K2.u4727 = KTree.node D2M8K2.u4725 (nat_lit 10592956) (nat_lit 3840653483) (nat_lit 0) D2M8K2.u4726 from rfl, allE_node, arows4725, irow4727, arows4726]
  all_goals rfl

theorem atot4727 : totK PD2M8K2 D2M8K2.u4727 = [0, 420891538581, 1512096752734, 1422999329461, 245515549573, 4980514959, 0, 0] := by
  rw [show D2M8K2.u4727 = KTree.node D2M8K2.u4725 (nat_lit 10592956) (nat_lit 3840653483) (nat_lit 0) D2M8K2.u4726 from rfl, totK_node, atot4725, atot4726]
  decide +kernel

theorem arows4735 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4735 = true := by
  rw [show D2M8K2.u4735 = KTree.node D2M8K2.u4733 (nat_lit 10596146) (nat_lit 1400394012) (nat_lit 0) D2M8K2.u4734 from rfl, allE_node, arows4733, irow4735, arows4734]
  all_goals rfl

theorem atot4735 : totK PD2M8K2 D2M8K2.u4735 = [0, 0, 780825457360, 1916539574401, 789831471295, 37738089782, 0, 0] := by
  rw [show D2M8K2.u4735 = KTree.node D2M8K2.u4733 (nat_lit 10596146) (nat_lit 1400394012) (nat_lit 0) D2M8K2.u4734 from rfl, totK_node, atot4733, atot4734]
  decide +kernel

theorem arows4738 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4738 = true := by
  rw [show D2M8K2.u4738 = KTree.node D2M8K2.u4736 (nat_lit 10600224) (nat_lit 2428147106) (nat_lit 0) D2M8K2.u4737 from rfl, allE_node, arows4736, irow4738, arows4737]
  all_goals rfl

theorem atot4738 : totK PD2M8K2 D2M8K2.u4738 = [0, 0, 511128250937, 1645300919592, 1280283775892, 153705260924, 1239866073, 0] := by
  rw [show D2M8K2.u4738 = KTree.node D2M8K2.u4736 (nat_lit 10600224) (nat_lit 2428147106) (nat_lit 0) D2M8K2.u4737 from rfl, totK_node, atot4736, atot4737]
  decide +kernel

theorem arows4742 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4742 = true := by
  rw [show D2M8K2.u4742 = KTree.node D2M8K2.u4740 (nat_lit 10608118) (nat_lit 3354086797) (nat_lit 0) D2M8K2.u4741 from rfl, allE_node, arows4740, irow4742, arows4741]
  all_goals rfl

theorem atot4742 : totK PD2M8K2 D2M8K2.u4742 = [0, 0, 388828729609, 1449296375001, 1402044300565, 316021360428, 13105450397, 0] := by
  rw [show D2M8K2.u4742 = KTree.node D2M8K2.u4740 (nat_lit 10608118) (nat_lit 3354086797) (nat_lit 0) D2M8K2.u4741 from rfl, totK_node, atot4740, atot4741]
  decide +kernel

theorem arows4745 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4745 = true := by
  rw [show D2M8K2.u4745 = KTree.node D2M8K2.u4743 (nat_lit 10611236) (nat_lit 3116490976) (nat_lit 0) D2M8K2.u4744 from rfl, allE_node, arows4743, irow4745, arows4744]
  all_goals rfl

theorem atot4745 : totK PD2M8K2 D2M8K2.u4745 = [0, 0, 464550343612, 1600886777097, 1244485402609, 181231958920, 4720618446, 0] := by
  rw [show D2M8K2.u4745 = KTree.node D2M8K2.u4743 (nat_lit 10611236) (nat_lit 3116490976) (nat_lit 0) D2M8K2.u4744 from rfl, totK_node, atot4743, atot4744]
  decide +kernel

theorem arows4750 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4750 = true := by
  rw [show D2M8K2.u4750 = KTree.node D2M8K2.u4748 (nat_lit 10616848) (nat_lit 3391614249) (nat_lit 0) D2M8K2.u4749 from rfl, allE_node, arows4748, irow4750, arows4749]
  all_goals rfl

theorem atot4750 : totK PD2M8K2 D2M8K2.u4750 = [0, 377059282660, 1288419242630, 1345498176017, 545305717086, 43903073402, 0, 0] := by
  rw [show D2M8K2.u4750 = KTree.node D2M8K2.u4748 (nat_lit 10616848) (nat_lit 3391614249) (nat_lit 0) D2M8K2.u4749 from rfl, totK_node, atot4748, atot4749]
  decide +kernel

theorem arows4753 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4753 = true := by
  rw [show D2M8K2.u4753 = KTree.node D2M8K2.u4751 (nat_lit 10620922) (nat_lit 3679037016) (nat_lit 0) D2M8K2.u4752 from rfl, allE_node, arows4751, irow4753, arows4752]
  all_goals rfl

theorem atot4753 : totK PD2M8K2 D2M8K2.u4753 = [0, 419665595470, 1550953874881, 1452353233427, 229977551058, 6688356276, 0, 0] := by
  rw [show D2M8K2.u4753 = KTree.node D2M8K2.u4751 (nat_lit 10620922) (nat_lit 3679037016) (nat_lit 0) D2M8K2.u4752 from rfl, totK_node, atot4751, atot4752]
  decide +kernel

theorem arows4757 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4757 = true := by
  rw [show D2M8K2.u4757 = KTree.node D2M8K2.u4755 (nat_lit 10623797) (nat_lit 2385308848) (nat_lit 0) D2M8K2.u4756 from rfl, allE_node, arows4755, irow4757, arows4756]
  all_goals rfl

theorem atot4757 : totK PD2M8K2 D2M8K2.u4757 = [0, 327098234359, 1250115977342, 1467973299680, 552550133052, 30550322668, 0, 0] := by
  rw [show D2M8K2.u4757 = KTree.node D2M8K2.u4755 (nat_lit 10623797) (nat_lit 2385308848) (nat_lit 0) D2M8K2.u4756 from rfl, totK_node, atot4755, atot4756]
  decide +kernel

theorem arows4760 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4760 = true := by
  rw [show D2M8K2.u4760 = KTree.node D2M8K2.u4758 (nat_lit 10627752) (nat_lit 2135207550) (nat_lit 0) D2M8K2.u4759 from rfl, allE_node, arows4758, irow4760, arows4759]
  all_goals rfl

theorem atot4760 : totK PD2M8K2 D2M8K2.u4760 = [0, 423825218633, 1456476480352, 1389527488957, 313562536995, 13083481006, 0, 0] := by
  rw [show D2M8K2.u4760 = KTree.node D2M8K2.u4758 (nat_lit 10627752) (nat_lit 2135207550) (nat_lit 0) D2M8K2.u4759 from rfl, totK_node, atot4758, atot4759]
  decide +kernel

theorem arows4766 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4766 = true := by
  rw [show D2M8K2.u4766 = KTree.node D2M8K2.u4764 (nat_lit 10631119) (nat_lit 2235152603) (nat_lit 0) D2M8K2.u4765 from rfl, allE_node, arows4764, irow4766, arows4765]
  all_goals rfl

theorem atot4766 : totK PD2M8K2 D2M8K2.u4766 = [0, 435739754619, 1480693946161, 1349696135942, 306513769275, 13149116973, 0, 0] := by
  rw [show D2M8K2.u4766 = KTree.node D2M8K2.u4764 (nat_lit 10631119) (nat_lit 2235152603) (nat_lit 0) D2M8K2.u4765 from rfl, totK_node, atot4764, atot4765]
  decide +kernel

theorem arows4769 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4769 = true := by
  rw [show D2M8K2.u4769 = KTree.node D2M8K2.u4767 (nat_lit 10638321) (nat_lit 1537941104) (nat_lit 0) D2M8K2.u4768 from rfl, allE_node, arows4767, irow4769, arows4768]
  all_goals rfl

theorem atot4769 : totK PD2M8K2 D2M8K2.u4769 = [0, 0, 724149162871, 1817769009460, 892605699795, 86079012461, 1138244013, 0] := by
  rw [show D2M8K2.u4769 = KTree.node D2M8K2.u4767 (nat_lit 10638321) (nat_lit 1537941104) (nat_lit 0) D2M8K2.u4768 from rfl, totK_node, atot4767, atot4768]
  decide +kernel

theorem arows4773 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4773 = true := by
  rw [show D2M8K2.u4773 = KTree.node D2M8K2.u4771 (nat_lit 10642220) (nat_lit 3786797412) (nat_lit 0) D2M8K2.u4772 from rfl, allE_node, arows4771, irow4773, arows4772]
  all_goals rfl

theorem atot4773 : totK PD2M8K2 D2M8K2.u4773 = [0, 0, 657759183276, 1838804512527, 1050948464856, 84447977748, 0, 0] := by
  rw [show D2M8K2.u4773 = KTree.node D2M8K2.u4771 (nat_lit 10642220) (nat_lit 3786797412) (nat_lit 0) D2M8K2.u4772 from rfl, totK_node, atot4771, atot4772]
  decide +kernel

theorem arows4776 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4776 = true := by
  rw [show D2M8K2.u4776 = KTree.node D2M8K2.u4774 (nat_lit 10649129) (nat_lit 1735296463) (nat_lit 0) D2M8K2.u4775 from rfl, allE_node, arows4774, irow4776, arows4775]
  all_goals rfl

theorem atot4776 : totK PD2M8K2 D2M8K2.u4776 = [0, 0, 763215858164, 1893305914707, 877585017994, 49604949613, 0, 0] := by
  rw [show D2M8K2.u4776 = KTree.node D2M8K2.u4774 (nat_lit 10649129) (nat_lit 1735296463) (nat_lit 0) D2M8K2.u4775 from rfl, totK_node, atot4774, atot4775]
  decide +kernel

theorem arows4781 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4781 = true := by
  rw [show D2M8K2.u4781 = KTree.node D2M8K2.u4779 (nat_lit 10653989) (nat_lit 1899307796) (nat_lit 0) D2M8K2.u4780 from rfl, allE_node, arows4779, irow4781, arows4780]
  all_goals rfl

theorem atot4781 : totK PD2M8K2 D2M8K2.u4781 = [0, 255770503163, 800052605099, 1226017993672, 1032684863534, 207826267002, 4977114383, 0] := by
  rw [show D2M8K2.u4781 = KTree.node D2M8K2.u4779 (nat_lit 10653989) (nat_lit 1899307796) (nat_lit 0) D2M8K2.u4780 from rfl, totK_node, atot4779, atot4780]
  decide +kernel

theorem arows4784 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4784 = true := by
  rw [show D2M8K2.u4784 = KTree.node D2M8K2.u4782 (nat_lit 10661563) (nat_lit 1675162517) (nat_lit 0) D2M8K2.u4783 from rfl, allE_node, arows4782, irow4784, arows4783]
  all_goals rfl

theorem atot4784 : totK PD2M8K2 D2M8K2.u4784 = [0, 488775418150, 1633220041880, 1349340020791, 180803209148, 1369150432, 0, 0] := by
  rw [show D2M8K2.u4784 = KTree.node D2M8K2.u4782 (nat_lit 10661563) (nat_lit 1675162517) (nat_lit 0) D2M8K2.u4783 from rfl, totK_node, atot4782, atot4783]
  decide +kernel

theorem arows4788 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4788 = true := by
  rw [show D2M8K2.u4788 = KTree.node D2M8K2.u4786 (nat_lit 10664734) (nat_lit 3132464481) (nat_lit 0) D2M8K2.u4787 from rfl, allE_node, arows4786, irow4788, arows4787]
  all_goals rfl

theorem atot4788 : totK PD2M8K2 D2M8K2.u4788 = [0, 296790853788, 1214501378998, 1534694607972, 586319323582, 37554459744, 0, 0] := by
  rw [show D2M8K2.u4788 = KTree.node D2M8K2.u4786 (nat_lit 10664734) (nat_lit 3132464481) (nat_lit 0) D2M8K2.u4787 from rfl, totK_node, atot4786, atot4787]
  decide +kernel

theorem arows4791 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4791 = true := by
  rw [show D2M8K2.u4791 = KTree.node D2M8K2.u4789 (nat_lit 10668774) (nat_lit 3732690527) (nat_lit 0) D2M8K2.u4790 from rfl, allE_node, arows4789, irow4791, arows4790]
  all_goals rfl

theorem atot4791 : totK PD2M8K2 D2M8K2.u4791 = [0, 513795387292, 1576221267574, 1298317017850, 249455063650, 8182332651, 0, 0] := by
  rw [show D2M8K2.u4791 = KTree.node D2M8K2.u4789 (nat_lit 10668774) (nat_lit 3732690527) (nat_lit 0) D2M8K2.u4790 from rfl, totK_node, atot4789, atot4790]
  decide +kernel

theorem arows4798 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4798 = true := by
  rw [show D2M8K2.u4798 = KTree.node D2M8K2.u4796 (nat_lit 10671976) (nat_lit 3577650363) (nat_lit 0) D2M8K2.u4797 from rfl, allE_node, arows4796, irow4798, arows4797]
  all_goals rfl

theorem atot4798 : totK PD2M8K2 D2M8K2.u4798 = [0, 376406383960, 1417415108997, 1459261194630, 345770104121, 13243784863, 0, 0] := by
  rw [show D2M8K2.u4798 = KTree.node D2M8K2.u4796 (nat_lit 10671976) (nat_lit 3577650363) (nat_lit 0) D2M8K2.u4797 from rfl, totK_node, atot4796, atot4797]
  decide +kernel

theorem arows4801 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4801 = true := by
  rw [show D2M8K2.u4801 = KTree.node D2M8K2.u4799 (nat_lit 10678424) (nat_lit 2861022221) (nat_lit 0) D2M8K2.u4800 from rfl, allE_node, arows4799, irow4801, arows4800]
  all_goals rfl

theorem atot4801 : totK PD2M8K2 D2M8K2.u4801 = [0, 60772201050, 932144060219, 1859876083045, 688636594788, 31403331363, 0, 0] := by
  rw [show D2M8K2.u4801 = KTree.node D2M8K2.u4799 (nat_lit 10678424) (nat_lit 2861022221) (nat_lit 0) D2M8K2.u4800 from rfl, totK_node, atot4799, atot4800]
  decide +kernel

theorem arows4805 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4805 = true := by
  rw [show D2M8K2.u4805 = KTree.node D2M8K2.u4803 (nat_lit 10682866) (nat_lit 3938046735) (nat_lit 0) D2M8K2.u4804 from rfl, allE_node, arows4803, irow4805, arows4804]
  all_goals rfl

theorem atot4805 : totK PD2M8K2 D2M8K2.u4805 = [0, 0, 508301314045, 1648312820003, 1321278172618, 152125798224, 1310285577, 0] := by
  rw [show D2M8K2.u4805 = KTree.node D2M8K2.u4803 (nat_lit 10682866) (nat_lit 3938046735) (nat_lit 0) D2M8K2.u4804 from rfl, totK_node, atot4803, atot4804]
  decide +kernel

theorem arows4808 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4808 = true := by
  rw [show D2M8K2.u4808 = KTree.node D2M8K2.u4806 (nat_lit 10687673) (nat_lit 1516516239) (nat_lit 0) D2M8K2.u4807 from rfl, allE_node, arows4806, irow4808, arows4807]
  all_goals rfl

theorem atot4808 : totK PD2M8K2 D2M8K2.u4808 = [0, 0, 500059028667, 1664822441520, 1305367648338, 168585917943, 1435164049, 0] := by
  rw [show D2M8K2.u4808 = KTree.node D2M8K2.u4806 (nat_lit 10687673) (nat_lit 1516516239) (nat_lit 0) D2M8K2.u4807 from rfl, totK_node, atot4806, atot4807]
  decide +kernel

theorem arows4813 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4813 = true := by
  rw [show D2M8K2.u4813 = KTree.node D2M8K2.u4811 (nat_lit 10692000) (nat_lit 3683631965) (nat_lit 0) D2M8K2.u4812 from rfl, allE_node, arows4811, irow4813, arows4812]
  all_goals rfl

theorem atot4813 : totK PD2M8K2 D2M8K2.u4813 = [0, 0, 479754812872, 1575061167130, 1299785063872, 215663963933, 4931404646, 0] := by
  rw [show D2M8K2.u4813 = KTree.node D2M8K2.u4811 (nat_lit 10692000) (nat_lit 3683631965) (nat_lit 0) D2M8K2.u4812 from rfl, totK_node, atot4811, atot4812]
  decide +kernel

theorem arows4816 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4816 = true := by
  rw [show D2M8K2.u4816 = KTree.node D2M8K2.u4814 (nat_lit 10698654) (nat_lit 2638626402) (nat_lit 0) D2M8K2.u4815 from rfl, allE_node, arows4814, irow4816, arows4815]
  all_goals rfl

theorem atot4816 : totK PD2M8K2 D2M8K2.u4816 = [0, 0, 372792702498, 1385829408308, 1416378342032, 376637236172, 18084324061, 0] := by
  rw [show D2M8K2.u4816 = KTree.node D2M8K2.u4814 (nat_lit 10698654) (nat_lit 2638626402) (nat_lit 0) D2M8K2.u4815 from rfl, totK_node, atot4814, atot4815]
  decide +kernel

theorem arows4820 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4820 = true := by
  rw [show D2M8K2.u4820 = KTree.node D2M8K2.u4818 (nat_lit 10702086) (nat_lit 2832987231) (nat_lit 0) D2M8K2.u4819 from rfl, allE_node, arows4818, irow4820, arows4819]
  all_goals rfl

theorem atot4820 : totK PD2M8K2 D2M8K2.u4820 = [0, 0, 490730890745, 1635675822667, 1299349570065, 151533334095, 1369150432, 0] := by
  rw [show D2M8K2.u4820 = KTree.node D2M8K2.u4818 (nat_lit 10702086) (nat_lit 2832987231) (nat_lit 0) D2M8K2.u4819 from rfl, totK_node, atot4818, atot4819]
  decide +kernel

theorem arows4823 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4823 = true := by
  rw [show D2M8K2.u4823 = KTree.node D2M8K2.u4821 (nat_lit 10714132) (nat_lit 3538039735) (nat_lit 0) D2M8K2.u4822 from rfl, allE_node, arows4821, irow4823, arows4822]
  all_goals rfl

theorem atot4823 : totK PD2M8K2 D2M8K2.u4823 = [0, 0, 586660234850, 1742001922433, 1107142747798, 105062146740, 1096505104, 0] := by
  rw [show D2M8K2.u4823 = KTree.node D2M8K2.u4821 (nat_lit 10714132) (nat_lit 3538039735) (nat_lit 0) D2M8K2.u4822 from rfl, totK_node, atot4821, atot4822]
  decide +kernel

theorem arows4829 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4829 = true := by
  rw [show D2M8K2.u4829 = KTree.node D2M8K2.u4827 (nat_lit 10718149) (nat_lit 1198269861) (nat_lit 0) D2M8K2.u4828 from rfl, allE_node, arows4827, irow4829, arows4828]
  all_goals rfl

theorem atot4829 : totK PD2M8K2 D2M8K2.u4829 = [0, 0, 670544331973, 1805311281681, 1107495136139, 95236002040, 0, 0] := by
  rw [show D2M8K2.u4829 = KTree.node D2M8K2.u4827 (nat_lit 10718149) (nat_lit 1198269861) (nat_lit 0) D2M8K2.u4828 from rfl, totK_node, atot4827, atot4828]
  decide +kernel

theorem arows4832 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4832 = true := by
  rw [show D2M8K2.u4832 = KTree.node D2M8K2.u4830 (nat_lit 10747250) (nat_lit 3945072085) (nat_lit 0) D2M8K2.u4831 from rfl, allE_node, arows4830, irow4832, arows4831]
  all_goals rfl

theorem atot4832 : totK PD2M8K2 D2M8K2.u4832 = [0, 0, 280796161259, 1170539514167, 1570549639950, 594954132934, 37500007640, 0] := by
  rw [show D2M8K2.u4832 = KTree.node D2M8K2.u4830 (nat_lit 10747250) (nat_lit 3945072085) (nat_lit 0) D2M8K2.u4831 from rfl, totK_node, atot4830, atot4831]
  decide +kernel

theorem arows4836 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4836 = true := by
  rw [show D2M8K2.u4836 = KTree.node D2M8K2.u4834 (nat_lit 10750728) (nat_lit 2583440901) (nat_lit 0) D2M8K2.u4835 from rfl, allE_node, arows4834, irow4836, arows4835]
  all_goals rfl

theorem atot4836 : totK PD2M8K2 D2M8K2.u4836 = [0, 0, 494262773995, 1612277572184, 1321776690241, 234150416490, 5370412161, 0] := by
  rw [show D2M8K2.u4836 = KTree.node D2M8K2.u4834 (nat_lit 10750728) (nat_lit 2583440901) (nat_lit 0) D2M8K2.u4835 from rfl, totK_node, atot4834, atot4835]
  decide +kernel

theorem arows4839 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4839 = true := by
  rw [show D2M8K2.u4839 = KTree.node D2M8K2.u4837 (nat_lit 10754433) (nat_lit 1766351778) (nat_lit 0) D2M8K2.u4838 from rfl, allE_node, arows4837, irow4839, arows4838]
  all_goals rfl

theorem atot4839 : totK PD2M8K2 D2M8K2.u4839 = [0, 0, 406072458959, 1457532650468, 1405460545003, 321767205209, 9190730223, 0] := by
  rw [show D2M8K2.u4839 = KTree.node D2M8K2.u4837 (nat_lit 10754433) (nat_lit 1766351778) (nat_lit 0) D2M8K2.u4838 from rfl, totK_node, atot4837, atot4838]
  decide +kernel

theorem arows4844 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4844 = true := by
  rw [show D2M8K2.u4844 = KTree.node D2M8K2.u4842 (nat_lit 10757956) (nat_lit 3430911910) (nat_lit 0) D2M8K2.u4843 from rfl, allE_node, arows4842, irow4844, arows4843]
  all_goals rfl

theorem atot4844 : totK PD2M8K2 D2M8K2.u4844 = [0, 0, 500808502358, 1626943860885, 1320659729145, 199547582101, 2585032425, 0] := by
  rw [show D2M8K2.u4844 = KTree.node D2M8K2.u4842 (nat_lit 10757956) (nat_lit 3430911910) (nat_lit 0) D2M8K2.u4843 from rfl, totK_node, atot4842, atot4843]
  decide +kernel

theorem arows4847 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4847 = true := by
  rw [show D2M8K2.u4847 = KTree.node D2M8K2.u4845 (nat_lit 10761273) (nat_lit 757235466) (nat_lit 2) D2M8K2.u4846 from rfl, allE_node, arows4845, irow4847, arows4846]
  all_goals rfl

theorem atot4847 : totK PD2M8K2 D2M8K2.u4847 = [0, 0, 401878803111, 1389252986201, 1402641017764, 375798913907, 13650900414, 0] := by
  rw [show D2M8K2.u4847 = KTree.node D2M8K2.u4845 (nat_lit 10761273) (nat_lit 757235466) (nat_lit 2) D2M8K2.u4846 from rfl, totK_node, atot4845, atot4846]
  decide +kernel

theorem arows4851 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4851 = true := by
  rw [show D2M8K2.u4851 = KTree.node D2M8K2.u4849 (nat_lit 10827974) (nat_lit 4185429624) (nat_lit 0) D2M8K2.u4850 from rfl, allE_node, arows4849, irow4851, arows4850]
  all_goals rfl

theorem atot4851 : totK PD2M8K2 D2M8K2.u4851 = [0, 0, 476681448075, 1625561126001, 1340139425110, 166184990757, 1369150432, 0] := by
  rw [show D2M8K2.u4851 = KTree.node D2M8K2.u4849 (nat_lit 10827974) (nat_lit 4185429624) (nat_lit 0) D2M8K2.u4850 from rfl, totK_node, atot4849, atot4850]
  decide +kernel

theorem arows4854 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4854 = true := by
  rw [show D2M8K2.u4854 = KTree.node D2M8K2.u4852 (nat_lit 10830699) (nat_lit 3723877040) (nat_lit 0) D2M8K2.u4853 from rfl, allE_node, arows4852, irow4854, arows4853]
  all_goals rfl

theorem atot4854 : totK PD2M8K2 D2M8K2.u4854 = [0, 0, 303190615096, 1225469007165, 1522555886681, 546714995253, 30151172974, 0] := by
  rw [show D2M8K2.u4854 = KTree.node D2M8K2.u4852 (nat_lit 10830699) (nat_lit 3723877040) (nat_lit 0) D2M8K2.u4853 from rfl, totK_node, atot4852, atot4853]
  decide +kernel

theorem arows4863 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4863 = true := by
  rw [show D2M8K2.u4863 = KTree.node D2M8K2.u4861 (nat_lit 10837296) (nat_lit 3596829569) (nat_lit 0) D2M8K2.u4862 from rfl, allE_node, arows4861, irow4863, arows4862]
  all_goals rfl

theorem atot4863 : totK PD2M8K2 D2M8K2.u4863 = [0, 0, 387028962454, 1405329056323, 1437723221470, 343305245714, 13250685261, 0] := by
  rw [show D2M8K2.u4863 = KTree.node D2M8K2.u4861 (nat_lit 10837296) (nat_lit 3596829569) (nat_lit 0) D2M8K2.u4862 from rfl, totK_node, atot4861, atot4862]
  decide +kernel

theorem arows4866 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4866 = true := by
  rw [show D2M8K2.u4866 = KTree.node D2M8K2.u4864 (nat_lit 10840423) (nat_lit 2065516491) (nat_lit 0) D2M8K2.u4865 from rfl, allE_node, arows4864, irow4866, arows4865]
  all_goals rfl

theorem atot4866 : totK PD2M8K2 D2M8K2.u4866 = [0, 0, 437998532933, 1553086507812, 1360046366483, 220880020858, 4980514959, 0] := by
  rw [show D2M8K2.u4866 = KTree.node D2M8K2.u4864 (nat_lit 10840423) (nat_lit 2065516491) (nat_lit 0) D2M8K2.u4865 from rfl, totK_node, atot4864, atot4865]
  decide +kernel

theorem arows4870 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4870 = true := by
  rw [show D2M8K2.u4870 = KTree.node D2M8K2.u4868 (nat_lit 10844043) (nat_lit 1942860770) (nat_lit 0) D2M8K2.u4869 from rfl, allE_node, arows4868, irow4870, arows4869]
  all_goals rfl

theorem atot4870 : totK PD2M8K2 D2M8K2.u4870 = [0, 0, 182137505762, 1125863165197, 1713738077698, 522504322028, 18672544577, 0] := by
  rw [show D2M8K2.u4870 = KTree.node D2M8K2.u4868 (nat_lit 10844043) (nat_lit 1942860770) (nat_lit 0) D2M8K2.u4869 from rfl, totK_node, atot4868, atot4869]
  decide +kernel

theorem arows4873 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4873 = true := by
  rw [show D2M8K2.u4873 = KTree.node D2M8K2.u4871 (nat_lit 10849512) (nat_lit 3136566461) (nat_lit 0) D2M8K2.u4872 from rfl, allE_node, arows4871, irow4873, arows4872]
  all_goals rfl

theorem atot4873 : totK PD2M8K2 D2M8K2.u4873 = [0, 0, 0, 814409025624, 1912340987837, 811902643436, 49581104732, 0] := by
  rw [show D2M8K2.u4873 = KTree.node D2M8K2.u4871 (nat_lit 10849512) (nat_lit 3136566461) (nat_lit 0) D2M8K2.u4872 from rfl, totK_node, atot4871, atot4872]
  decide +kernel

theorem arows4878 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4878 = true := by
  rw [show D2M8K2.u4878 = KTree.node D2M8K2.u4876 (nat_lit 10858027) (nat_lit 1612555834) (nat_lit 0) D2M8K2.u4877 from rfl, allE_node, arows4876, irow4878, arows4877]
  all_goals rfl

theorem atot4878 : totK PD2M8K2 D2M8K2.u4878 = [0, 0, 0, 435662912573, 1574441417406, 1270022047527, 226089813587, 5757108999] := by
  rw [show D2M8K2.u4878 = KTree.node D2M8K2.u4876 (nat_lit 10858027) (nat_lit 1612555834) (nat_lit 0) D2M8K2.u4877 from rfl, totK_node, atot4876, atot4877]
  decide +kernel

theorem arows4881 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4881 = true := by
  rw [show D2M8K2.u4881 = KTree.node D2M8K2.u4879 (nat_lit 10861740) (nat_lit 3046145070) (nat_lit 0) D2M8K2.u4880 from rfl, allE_node, arows4879, irow4881, arows4880]
  all_goals rfl

theorem atot4881 : totK PD2M8K2 D2M8K2.u4881 = [0, 0, 0, 591199078054, 1719282111346, 1087040578901, 123141334287, 1348424121] := by
  rw [show D2M8K2.u4881 = KTree.node D2M8K2.u4879 (nat_lit 10861740) (nat_lit 3046145070) (nat_lit 0) D2M8K2.u4880 from rfl, totK_node, atot4879, atot4880]
  decide +kernel

theorem arows4885 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4885 = true := by
  rw [show D2M8K2.u4885 = KTree.node D2M8K2.u4883 (nat_lit 10867186) (nat_lit 3939923099) (nat_lit 0) D2M8K2.u4884 from rfl, allE_node, arows4883, irow4885, arows4884]
  all_goals rfl

theorem atot4885 : totK PD2M8K2 D2M8K2.u4885 = [0, 0, 496709275433, 1560318134779, 1273884205176, 232812006660, 10353568507, 0] := by
  rw [show D2M8K2.u4885 = KTree.node D2M8K2.u4883 (nat_lit 10867186) (nat_lit 3939923099) (nat_lit 0) D2M8K2.u4884 from rfl, totK_node, atot4883, atot4884]
  decide +kernel

theorem arows4888 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4888 = true := by
  rw [show D2M8K2.u4888 = KTree.node D2M8K2.u4886 (nat_lit 10871311) (nat_lit 2214005087) (nat_lit 0) D2M8K2.u4887 from rfl, allE_node, arows4886, irow4888, arows4887]
  all_goals rfl

theorem atot4888 : totK PD2M8K2 D2M8K2.u4888 = [0, 0, 404980432597, 1447307577614, 1402177765123, 376527185960, 15066332673, 0] := by
  rw [show D2M8K2.u4888 = KTree.node D2M8K2.u4886 (nat_lit 10871311) (nat_lit 2214005087) (nat_lit 0) D2M8K2.u4887 from rfl, totK_node, atot4886, atot4887]
  decide +kernel

theorem arows4894 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4894 = true := by
  rw [show D2M8K2.u4894 = KTree.node D2M8K2.u4892 (nat_lit 10875462) (nat_lit 3164839281) (nat_lit 0) D2M8K2.u4893 from rfl, allE_node, arows4892, irow4894, arows4893]
  all_goals rfl

theorem atot4894 : totK PD2M8K2 D2M8K2.u4894 = [0, 0, 531411102042, 1670529094500, 1270395700894, 158982254486, 1288481286, 0] := by
  rw [show D2M8K2.u4894 = KTree.node D2M8K2.u4892 (nat_lit 10875462) (nat_lit 3164839281) (nat_lit 0) D2M8K2.u4893 from rfl, totK_node, atot4892, atot4893]
  decide +kernel

theorem arows4897 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4897 = true := by
  rw [show D2M8K2.u4897 = KTree.node D2M8K2.u4895 (nat_lit 10878963) (nat_lit 2548450691) (nat_lit 0) D2M8K2.u4896 from rfl, allE_node, arows4895, irow4897, arows4896]
  all_goals rfl

theorem atot4897 : totK PD2M8K2 D2M8K2.u4897 = [0, 0, 376386149874, 1400696355112, 1427212799941, 340679982966, 13250685261, 0] := by
  rw [show D2M8K2.u4897 = KTree.node D2M8K2.u4895 (nat_lit 10878963) (nat_lit 2548450691) (nat_lit 0) D2M8K2.u4896 from rfl, totK_node, atot4895, atot4896]
  decide +kernel

theorem arows4901 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4901 = true := by
  rw [show D2M8K2.u4901 = KTree.node D2M8K2.u4899 (nat_lit 10882177) (nat_lit 1456596065) (nat_lit 0) D2M8K2.u4900 from rfl, allE_node, arows4899, irow4901, arows4900]
  all_goals rfl

theorem atot4901 : totK PD2M8K2 D2M8K2.u4901 = [0, 0, 167115188431, 1200704267761, 1738193451764, 448164505157, 10820551980, 0] := by
  rw [show D2M8K2.u4901 = KTree.node D2M8K2.u4899 (nat_lit 10882177) (nat_lit 1456596065) (nat_lit 0) D2M8K2.u4900 from rfl, totK_node, atot4899, atot4900]
  decide +kernel

theorem arows4904 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4904 = true := by
  rw [show D2M8K2.u4904 = KTree.node D2M8K2.u4902 (nat_lit 10893334) (nat_lit 2824999073) (nat_lit 0) D2M8K2.u4903 from rfl, allE_node, arows4902, irow4904, arows4903]
  all_goals rfl

theorem atot4904 : totK PD2M8K2 D2M8K2.u4904 = [0, 0, 0, 952991084475, 1924148336061, 683791409252, 29987884338, 0] := by
  rw [show D2M8K2.u4904 = KTree.node D2M8K2.u4902 (nat_lit 10893334) (nat_lit 2824999073) (nat_lit 0) D2M8K2.u4903 from rfl, totK_node, atot4902, atot4903]
  decide +kernel

theorem arows4909 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4909 = true := by
  rw [show D2M8K2.u4909 = KTree.node D2M8K2.u4907 (nat_lit 10900635) (nat_lit 2563658610) (nat_lit 0) D2M8K2.u4908 from rfl, allE_node, arows4907, irow4909, arows4908]
  all_goals rfl

theorem atot4909 : totK PD2M8K2 D2M8K2.u4909 = [0, 0, 0, 672465432079, 1868950241557, 923618350181, 58325612839, 0] := by
  rw [show D2M8K2.u4909 = KTree.node D2M8K2.u4907 (nat_lit 10900635) (nat_lit 2563658610) (nat_lit 0) D2M8K2.u4908 from rfl, totK_node, atot4907, atot4908]
  decide +kernel

theorem arows4912 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4912 = true := by
  rw [show D2M8K2.u4912 = KTree.node D2M8K2.u4910 (nat_lit 10908397) (nat_lit 1128289678) (nat_lit 0) D2M8K2.u4911 from rfl, allE_node, arows4910, irow4912, arows4911]
  all_goals rfl

theorem atot4912 : totK PD2M8K2 D2M8K2.u4912 = [0, 0, 454235855139, 1309554702315, 1224568307316, 499404901208, 77894559111, 1430229726] := by
  rw [show D2M8K2.u4912 = KTree.node D2M8K2.u4910 (nat_lit 10908397) (nat_lit 1128289678) (nat_lit 0) D2M8K2.u4911 from rfl, totK_node, atot4910, atot4911]
  decide +kernel

theorem arows4916 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4916 = true := by
  rw [show D2M8K2.u4916 = KTree.node D2M8K2.u4914 (nat_lit 10912256) (nat_lit 2692693655) (nat_lit 0) D2M8K2.u4915 from rfl, allE_node, arows4914, irow4916, arows4915]
  all_goals rfl

theorem atot4916 : totK PD2M8K2 D2M8K2.u4916 = [0, 0, 339326678219, 1344564373511, 1488019723410, 460599608091, 26020096574, 0] := by
  rw [show D2M8K2.u4916 = KTree.node D2M8K2.u4914 (nat_lit 10912256) (nat_lit 2692693655) (nat_lit 0) D2M8K2.u4915 from rfl, totK_node, atot4914, atot4915]
  decide +kernel

theorem arows4919 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4919 = true := by
  rw [show D2M8K2.u4919 = KTree.node D2M8K2.u4917 (nat_lit 10915789) (nat_lit 1389735202) (nat_lit 0) D2M8K2.u4918 from rfl, allE_node, arows4917, irow4919, arows4918]
  all_goals rfl

theorem atot4919 : totK PD2M8K2 D2M8K2.u4919 = [0, 0, 516263383066, 1568412285974, 1316063506681, 274216453825, 8285673578, 0] := by
  rw [show D2M8K2.u4919 = KTree.node D2M8K2.u4917 (nat_lit 10915789) (nat_lit 1389735202) (nat_lit 0) D2M8K2.u4918 from rfl, totK_node, atot4917, atot4918]
  decide +kernel

theorem arows4926 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4926 = true := by
  rw [show D2M8K2.u4926 = KTree.node D2M8K2.u4924 (nat_lit 10919656) (nat_lit 3509271975) (nat_lit 0) D2M8K2.u4925 from rfl, allE_node, arows4924, irow4926, arows4925]
  all_goals rfl

theorem atot4926 : totK PD2M8K2 D2M8K2.u4926 = [0, 0, 407115416754, 1468424435386, 1412965119666, 320412265654, 9574510643, 0] := by
  rw [show D2M8K2.u4926 = KTree.node D2M8K2.u4924 (nat_lit 10919656) (nat_lit 3509271975) (nat_lit 0) D2M8K2.u4925 from rfl, totK_node, atot4924, atot4925]
  decide +kernel

theorem arows4929 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4929 = true := by
  rw [show D2M8K2.u4929 = KTree.node D2M8K2.u4927 (nat_lit 10926481) (nat_lit 888810617) (nat_lit 2) D2M8K2.u4928 from rfl, allE_node, arows4927, irow4929, arows4928]
  all_goals rfl

theorem atot4929 : totK PD2M8K2 D2M8K2.u4929 = [0, 91454885225, 481969198452, 1207383599234, 1402254581110, 409581901061, 18278260897, 0] := by
  rw [show D2M8K2.u4929 = KTree.node D2M8K2.u4927 (nat_lit 10926481) (nat_lit 888810617) (nat_lit 2) D2M8K2.u4928 from rfl, totK_node, atot4927, atot4928]
  decide +kernel

theorem arows4933 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4933 = true := by
  rw [show D2M8K2.u4933 = KTree.node D2M8K2.u4931 (nat_lit 10950415) (nat_lit 2423996495) (nat_lit 0) D2M8K2.u4932 from rfl, allE_node, arows4931, irow4933, arows4932]
  all_goals rfl

theorem atot4933 : totK PD2M8K2 D2M8K2.u4933 = [0, 484654331549, 1616803780786, 1310907111477, 179889281360, 1369150432, 0, 0] := by
  rw [show D2M8K2.u4933 = KTree.node D2M8K2.u4931 (nat_lit 10950415) (nat_lit 2423996495) (nat_lit 0) D2M8K2.u4932 from rfl, totK_node, atot4931, atot4932]
  decide +kernel

theorem arows4936 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4936 = true := by
  rw [show D2M8K2.u4936 = KTree.node D2M8K2.u4934 (nat_lit 10957594) (nat_lit 3731136522) (nat_lit 0) D2M8K2.u4935 from rfl, allE_node, arows4934, irow4936, arows4935]
  all_goals rfl

theorem atot4936 : totK PD2M8K2 D2M8K2.u4936 = [0, 400086141160, 1437745844274, 1419667516647, 307370253110, 13049727234, 0, 0] := by
  rw [show D2M8K2.u4936 = KTree.node D2M8K2.u4934 (nat_lit 10957594) (nat_lit 3731136522) (nat_lit 0) D2M8K2.u4935 from rfl, totK_node, atot4934, atot4935]
  decide +kernel

theorem arows4941 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4941 = true := by
  rw [show D2M8K2.u4941 = KTree.node D2M8K2.u4939 (nat_lit 10961100) (nat_lit 2438358378) (nat_lit 0) D2M8K2.u4940 from rfl, allE_node, arows4939, irow4941, arows4940]
  all_goals rfl

theorem atot4941 : totK PD2M8K2 D2M8K2.u4941 = [0, 405071052402, 1445660536466, 1418977501360, 309329911293, 13250685261, 0, 0] := by
  rw [show D2M8K2.u4941 = KTree.node D2M8K2.u4939 (nat_lit 10961100) (nat_lit 2438358378) (nat_lit 0) D2M8K2.u4940 from rfl, totK_node, atot4939, atot4940]
  decide +kernel

theorem arows4944 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4944 = true := by
  rw [show D2M8K2.u4944 = KTree.node D2M8K2.u4942 (nat_lit 10964513) (nat_lit 2183825540) (nat_lit 0) D2M8K2.u4943 from rfl, allE_node, arows4942, irow4944, arows4943]
  all_goals rfl

theorem atot4944 : totK PD2M8K2 D2M8K2.u4944 = [0, 263060155692, 1282125022135, 1610944053908, 400327927206, 14591428522, 0, 0] := by
  rw [show D2M8K2.u4944 = KTree.node D2M8K2.u4942 (nat_lit 10964513) (nat_lit 2183825540) (nat_lit 0) D2M8K2.u4943 from rfl, totK_node, atot4942, atot4943]
  decide +kernel

theorem arows4948 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4948 = true := by
  rw [show D2M8K2.u4948 = KTree.node D2M8K2.u4946 (nat_lit 10971969) (nat_lit 1414989034) (nat_lit 0) D2M8K2.u4947 from rfl, allE_node, arows4946, irow4948, arows4947]
  all_goals rfl

theorem atot4948 : totK PD2M8K2 D2M8K2.u4948 = [0, 0, 548477032175, 1738221009609, 1102754784298, 115503485600, 1369150432, 0] := by
  rw [show D2M8K2.u4948 = KTree.node D2M8K2.u4946 (nat_lit 10971969) (nat_lit 1414989034) (nat_lit 0) D2M8K2.u4947 from rfl, totK_node, atot4946, atot4947]
  decide +kernel

theorem arows4951 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4951 = true := by
  rw [show D2M8K2.u4951 = KTree.node D2M8K2.u4949 (nat_lit 10980893) (nat_lit 1705628365) (nat_lit 0) D2M8K2.u4950 from rfl, allE_node, arows4949, irow4951, arows4950]
  all_goals rfl

theorem atot4951 : totK PD2M8K2 D2M8K2.u4951 = [0, 0, 738510811706, 1930768362759, 855125525485, 37991077765, 0, 0] := by
  rw [show D2M8K2.u4951 = KTree.node D2M8K2.u4949 (nat_lit 10980893) (nat_lit 1705628365) (nat_lit 0) D2M8K2.u4950 from rfl, totK_node, atot4949, atot4950]
  decide +kernel

theorem arows4957 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4957 = true := by
  rw [show D2M8K2.u4957 = KTree.node D2M8K2.u4955 (nat_lit 10994370) (nat_lit 1450541680) (nat_lit 0) D2M8K2.u4956 from rfl, allE_node, arows4955, irow4957, arows4956]
  all_goals rfl

theorem atot4957 : totK PD2M8K2 D2M8K2.u4957 = [0, 444900490559, 1414585486772, 1342933815198, 427602956998, 31060983192, 0, 0] := by
  rw [show D2M8K2.u4957 = KTree.node D2M8K2.u4955 (nat_lit 10994370) (nat_lit 1450541680) (nat_lit 0) D2M8K2.u4956 from rfl, totK_node, atot4955, atot4956]
  decide +kernel

theorem arows4960 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4960 = true := by
  rw [show D2M8K2.u4960 = KTree.node D2M8K2.u4958 (nat_lit 10997116) (nat_lit 3854718101) (nat_lit 0) D2M8K2.u4959 from rfl, allE_node, arows4958, irow4960, arows4959]
  all_goals rfl

theorem atot4960 : totK PD2M8K2 D2M8K2.u4960 = [0, 413965556923, 1376874982319, 1391756159216, 444197180322, 20423179516, 0, 0] := by
  rw [show D2M8K2.u4960 = KTree.node D2M8K2.u4958 (nat_lit 10997116) (nat_lit 3854718101) (nat_lit 0) D2M8K2.u4959 from rfl, totK_node, atot4958, atot4959]
  decide +kernel

theorem arows4964 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4964 = true := by
  rw [show D2M8K2.u4964 = KTree.node D2M8K2.u4962 (nat_lit 11000546) (nat_lit 3162828252) (nat_lit 0) D2M8K2.u4963 from rfl, allE_node, arows4962, irow4964, arows4963]
  all_goals rfl

theorem atot4964 : totK PD2M8K2 D2M8K2.u4964 = [0, 414208706694, 1447575350641, 1421867961149, 325118044512, 13036865798, 0, 0] := by
  rw [show D2M8K2.u4964 = KTree.node D2M8K2.u4962 (nat_lit 11000546) (nat_lit 3162828252) (nat_lit 0) D2M8K2.u4963 from rfl, totK_node, atot4962, atot4963]
  decide +kernel

theorem arows4967 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4967 = true := by
  rw [show D2M8K2.u4967 = KTree.node D2M8K2.u4965 (nat_lit 11003920) (nat_lit 3327106612) (nat_lit 0) D2M8K2.u4966 from rfl, allE_node, arows4965, irow4967, arows4966]
  all_goals rfl

theorem atot4967 : totK PD2M8K2 D2M8K2.u4967 = [0, 390330755319, 1419196872605, 1453996512514, 340582654682, 13237669976, 0, 0] := by
  rw [show D2M8K2.u4967 = KTree.node D2M8K2.u4965 (nat_lit 11003920) (nat_lit 3327106612) (nat_lit 0) D2M8K2.u4966 from rfl, totK_node, atot4965, atot4966]
  decide +kernel

theorem arows4972 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4972 = true := by
  rw [show D2M8K2.u4972 = KTree.node D2M8K2.u4970 (nat_lit 11007720) (nat_lit 2684559728) (nat_lit 0) D2M8K2.u4971 from rfl, allE_node, arows4970, irow4972, arows4971]
  all_goals rfl

theorem atot4972 : totK PD2M8K2 D2M8K2.u4972 = [0, 378543555504, 1523427215443, 1503236828084, 267063457571, 4976872846, 0, 0] := by
  rw [show D2M8K2.u4972 = KTree.node D2M8K2.u4970 (nat_lit 11007720) (nat_lit 2684559728) (nat_lit 0) D2M8K2.u4971 from rfl, totK_node, atot4970, atot4971]
  decide +kernel

theorem arows4975 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4975 = true := by
  rw [show D2M8K2.u4975 = KTree.node D2M8K2.u4973 (nat_lit 11014836) (nat_lit 1019182125) (nat_lit 0) D2M8K2.u4974 from rfl, allE_node, arows4973, irow4975, arows4974]
  all_goals rfl

theorem atot4975 : totK PD2M8K2 D2M8K2.u4975 = [0, 0, 734849718450, 1878183496506, 981853106721, 75376736182, 0, 0] := by
  rw [show D2M8K2.u4975 = KTree.node D2M8K2.u4973 (nat_lit 11014836) (nat_lit 1019182125) (nat_lit 0) D2M8K2.u4974 from rfl, totK_node, atot4973, atot4974]
  decide +kernel

theorem arows4979 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4979 = true := by
  rw [show D2M8K2.u4979 = KTree.node D2M8K2.u4977 (nat_lit 11017562) (nat_lit 4100404273) (nat_lit 0) D2M8K2.u4978 from rfl, allE_node, arows4977, irow4979, arows4978]
  all_goals rfl

theorem atot4979 : totK PD2M8K2 D2M8K2.u4979 = [0, 0, 332530354145, 1214925722411, 1463242133747, 551382246165, 36921873854, 0] := by
  rw [show D2M8K2.u4979 = KTree.node D2M8K2.u4977 (nat_lit 11017562) (nat_lit 4100404273) (nat_lit 0) D2M8K2.u4978 from rfl, totK_node, atot4977, atot4978]
  decide +kernel

theorem arows4982 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4982 = true := by
  rw [show D2M8K2.u4982 = KTree.node D2M8K2.u4980 (nat_lit 11020975) (nat_lit 2161500995) (nat_lit 0) D2M8K2.u4981 from rfl, allE_node, arows4980, irow4982, arows4981]
  all_goals rfl

theorem atot4982 : totK PD2M8K2 D2M8K2.u4982 = [0, 0, 444583734283, 1542397610747, 1386785690100, 243450549273, 5159868635, 0] := by
  rw [show D2M8K2.u4982 = KTree.node D2M8K2.u4980 (nat_lit 11020975) (nat_lit 2161500995) (nat_lit 0) D2M8K2.u4981 from rfl, totK_node, atot4980, atot4981]
  decide +kernel

theorem arows4990 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4990 = true := by
  rw [show D2M8K2.u4990 = KTree.node D2M8K2.u4988 (nat_lit 11024708) (nat_lit 3329470629) (nat_lit 0) D2M8K2.u4989 from rfl, allE_node, arows4988, irow4990, arows4989]
  all_goals rfl

theorem atot4990 : totK PD2M8K2 D2M8K2.u4990 = [0, 0, 460501954370, 1533191286250, 1361172979611, 250983568264, 5218872685, 0] := by
  rw [show D2M8K2.u4990 = KTree.node D2M8K2.u4988 (nat_lit 11024708) (nat_lit 3329470629) (nat_lit 0) D2M8K2.u4989 from rfl, totK_node, atot4988, atot4989]
  decide +kernel

theorem arows4993 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4993 = true := by
  rw [show D2M8K2.u4993 = KTree.node D2M8K2.u4991 (nat_lit 11028581) (nat_lit 2357787354) (nat_lit 0) D2M8K2.u4992 from rfl, allE_node, arows4991, irow4993, arows4992]
  all_goals rfl

theorem atot4993 : totK PD2M8K2 D2M8K2.u4993 = [0, 0, 359069204428, 1563723794292, 1538280221841, 221668859712, 1415142070, 0] := by
  rw [show D2M8K2.u4993 = KTree.node D2M8K2.u4991 (nat_lit 11028581) (nat_lit 2357787354) (nat_lit 0) D2M8K2.u4992 from rfl, totK_node, atot4991, atot4992]
  decide +kernel

theorem arows4997 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4997 = true := by
  rw [show D2M8K2.u4997 = KTree.node D2M8K2.u4995 (nat_lit 11032382) (nat_lit 2442311913) (nat_lit 0) D2M8K2.u4996 from rfl, allE_node, arows4995, irow4997, arows4996]
  all_goals rfl

theorem atot4997 : totK PD2M8K2 D2M8K2.u4997 = [0, 377174344386, 1177560875393, 1084183724176, 679302940276, 220295928914, 9302370699, 0] := by
  rw [show D2M8K2.u4997 = KTree.node D2M8K2.u4995 (nat_lit 11032382) (nat_lit 2442311913) (nat_lit 0) D2M8K2.u4996 from rfl, totK_node, atot4995, atot4996]
  decide +kernel

theorem arows5000 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5000 = true := by
  rw [show D2M8K2.u5000 = KTree.node D2M8K2.u4998 (nat_lit 11036206) (nat_lit 3438814692) (nat_lit 0) D2M8K2.u4999 from rfl, allE_node, arows4998, irow5000, arows4999]
  all_goals rfl

theorem atot5000 : totK PD2M8K2 D2M8K2.u5000 = [0, 420009189942, 1472223733464, 1401534212115, 360449264028, 25357676561, 0, 0] := by
  rw [show D2M8K2.u5000 = KTree.node D2M8K2.u4998 (nat_lit 11036206) (nat_lit 3438814692) (nat_lit 0) D2M8K2.u4999 from rfl, totK_node, atot4998, atot4999]
  decide +kernel

theorem arows5005 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5005 = true := by
  rw [show D2M8K2.u5005 = KTree.node D2M8K2.u5003 (nat_lit 11039016) (nat_lit 2544168490) (nat_lit 0) D2M8K2.u5004 from rfl, allE_node, arows5003, irow5005, arows5004]
  all_goals rfl

theorem atot5005 : totK PD2M8K2 D2M8K2.u5005 = [0, 437716969889, 1424191403049, 1363287579838, 386147606394, 13371182392, 0, 0] := by
  rw [show D2M8K2.u5005 = KTree.node D2M8K2.u5003 (nat_lit 11039016) (nat_lit 2544168490) (nat_lit 0) D2M8K2.u5004 from rfl, totK_node, atot5003, atot5004]
  decide +kernel

theorem arows5008 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5008 = true := by
  rw [show D2M8K2.u5008 = KTree.node D2M8K2.u5006 (nat_lit 11045774) (nat_lit 3878762720) (nat_lit 0) D2M8K2.u5007 from rfl, allE_node, arows5006, irow5008, arows5007]
  all_goals rfl

theorem atot5008 : totK PD2M8K2 D2M8K2.u5008 = [0, 421856865557, 1470548578400, 1375231922357, 298864012838, 12981912718, 0, 0] := by
  rw [show D2M8K2.u5008 = KTree.node D2M8K2.u5006 (nat_lit 11045774) (nat_lit 3878762720) (nat_lit 0) D2M8K2.u5007 from rfl, totK_node, atot5006, atot5007]
  decide +kernel

theorem arows5012 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5012 = true := by
  rw [show D2M8K2.u5012 = KTree.node D2M8K2.u5010 (nat_lit 11049329) (nat_lit 1734587283) (nat_lit 0) D2M8K2.u5011 from rfl, allE_node, arows5010, irow5012, arows5011]
  all_goals rfl

theorem atot5012 : totK PD2M8K2 D2M8K2.u5012 = [0, 330025283572, 1425412926379, 1580939798089, 311964219039, 5152749158, 0, 0] := by
  rw [show D2M8K2.u5012 = KTree.node D2M8K2.u5010 (nat_lit 11049329) (nat_lit 1734587283) (nat_lit 0) D2M8K2.u5011 from rfl, totK_node, atot5010, atot5011]
  decide +kernel

theorem arows5015 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5015 = true := by
  rw [show D2M8K2.u5015 = KTree.node D2M8K2.u5013 (nat_lit 11053493) (nat_lit 2373749623) (nat_lit 0) D2M8K2.u5014 from rfl, allE_node, arows5013, irow5015, arows5014]
  all_goals rfl

theorem atot5015 : totK PD2M8K2 D2M8K2.u5015 = [0, 0, 501631720856, 1666548688995, 1192508085207, 124484400688, 1206465782, 0] := by
  rw [show D2M8K2.u5015 = KTree.node D2M8K2.u5013 (nat_lit 11053493) (nat_lit 2373749623) (nat_lit 0) D2M8K2.u5014 from rfl, totK_node, atot5013, atot5014]
  decide +kernel

theorem arows5021 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5021 = true := by
  rw [show D2M8K2.u5021 = KTree.node D2M8K2.u5019 (nat_lit 11057332) (nat_lit 3653708243) (nat_lit 0) D2M8K2.u5020 from rfl, allE_node, arows5019, irow5021, arows5020]
  all_goals rfl

theorem atot5021 : totK PD2M8K2 D2M8K2.u5021 = [0, 0, 732497203095, 1882121973984, 959107008080, 71569333972, 0, 0] := by
  rw [show D2M8K2.u5021 = KTree.node D2M8K2.u5019 (nat_lit 11057332) (nat_lit 3653708243) (nat_lit 0) D2M8K2.u5020 from rfl, totK_node, atot5019, atot5020]
  decide +kernel

theorem arows5024 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5024 = true := by
  rw [show D2M8K2.u5024 = KTree.node D2M8K2.u5022 (nat_lit 11062242) (nat_lit 1352869009) (nat_lit 0) D2M8K2.u5023 from rfl, allE_node, arows5022, irow5024, arows5023]
  all_goals rfl

theorem atot5024 : totK PD2M8K2 D2M8K2.u5024 = [0, 0, 411810841740, 1461215831220, 1334835583878, 302284220526, 13016197374, 0] := by
  rw [show D2M8K2.u5024 = KTree.node D2M8K2.u5022 (nat_lit 11062242) (nat_lit 1352869009) (nat_lit 0) D2M8K2.u5023 from rfl, totK_node, atot5022, atot5023]
  decide +kernel

theorem arows5028 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5028 = true := by
  rw [show D2M8K2.u5028 = KTree.node D2M8K2.u5026 (nat_lit 11069209) (nat_lit 1148208861) (nat_lit 0) D2M8K2.u5027 from rfl, allE_node, arows5026, irow5028, arows5027]
  all_goals rfl

theorem atot5028 : totK PD2M8K2 D2M8K2.u5028 = [0, 37944309145, 472224113620, 1534153613308, 1289475581714, 195031028692, 4574395652, 0] := by
  rw [show D2M8K2.u5028 = KTree.node D2M8K2.u5026 (nat_lit 11069209) (nat_lit 1148208861) (nat_lit 0) D2M8K2.u5027 from rfl, totK_node, atot5026, atot5027]
  decide +kernel

theorem arows5031 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5031 = true := by
  rw [show D2M8K2.u5031 = KTree.node D2M8K2.u5029 (nat_lit 11074768) (nat_lit 3322621222) (nat_lit 0) D2M8K2.u5030 from rfl, allE_node, arows5029, irow5031, arows5030]
  all_goals rfl

theorem atot5031 : totK PD2M8K2 D2M8K2.u5031 = [0, 498158640172, 1615514679042, 1317251930677, 173681939085, 1369150432, 0, 0] := by
  rw [show D2M8K2.u5031 = KTree.node D2M8K2.u5029 (nat_lit 11074768) (nat_lit 3322621222) (nat_lit 0) D2M8K2.u5030 from rfl, totK_node, atot5029, atot5030]
  decide +kernel

theorem arows5036 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5036 = true := by
  rw [show D2M8K2.u5036 = KTree.node D2M8K2.u5034 (nat_lit 11078714) (nat_lit 4102082038) (nat_lit 0) D2M8K2.u5035 from rfl, allE_node, arows5034, irow5036, arows5035]
  all_goals rfl

theorem atot5036 : totK PD2M8K2 D2M8K2.u5036 = [0, 310321538422, 1235272829574, 1496877577580, 575263668613, 37562495386, 0, 0] := by
  rw [show D2M8K2.u5036 = KTree.node D2M8K2.u5034 (nat_lit 11078714) (nat_lit 4102082038) (nat_lit 0) D2M8K2.u5035 from rfl, totK_node, atot5034, atot5035]
  decide +kernel

theorem arows5039 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5039 = true := by
  rw [show D2M8K2.u5039 = KTree.node D2M8K2.u5037 (nat_lit 11084957) (nat_lit 1867072274) (nat_lit 0) D2M8K2.u5038 from rfl, allE_node, arows5037, irow5039, arows5038]
  all_goals rfl

theorem atot5039 : totK PD2M8K2 D2M8K2.u5039 = [0, 388823439117, 1439363688776, 1434626649679, 335788668892, 13250685261, 0, 0] := by
  rw [show D2M8K2.u5039 = KTree.node D2M8K2.u5037 (nat_lit 11084957) (nat_lit 1867072274) (nat_lit 0) D2M8K2.u5038 from rfl, totK_node, atot5037, atot5038]
  decide +kernel

theorem arows5043 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5043 = true := by
  rw [show D2M8K2.u5043 = KTree.node D2M8K2.u5041 (nat_lit 11087986) (nat_lit 3786234904) (nat_lit 0) D2M8K2.u5042 from rfl, allE_node, arows5041, irow5043, arows5042]
  all_goals rfl

theorem atot5043 : totK PD2M8K2 D2M8K2.u5043 = [0, 421892135186, 1540338393366, 1415373263468, 225658712997, 2165917952, 0, 0] := by
  rw [show D2M8K2.u5043 = KTree.node D2M8K2.u5041 (nat_lit 11087986) (nat_lit 3786234904) (nat_lit 0) D2M8K2.u5042 from rfl, totK_node, atot5041, atot5042]
  decide +kernel

theorem arows5046 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5046 = true := by
  rw [show D2M8K2.u5046 = KTree.node D2M8K2.u5044 (nat_lit 11092113) (nat_lit 1666389575) (nat_lit 0) D2M8K2.u5045 from rfl, allE_node, arows5044, irow5046, arows5045]
  all_goals rfl

theorem atot5046 : totK PD2M8K2 D2M8K2.u5046 = [0, 330174384325, 1300824959087, 1514177750256, 451195171527, 21086231610, 0, 0] := by
  rw [show D2M8K2.u5046 = KTree.node D2M8K2.u5044 (nat_lit 11092113) (nat_lit 1666389575) (nat_lit 0) D2M8K2.u5045 from rfl, totK_node, atot5044, atot5045]
  decide +kernel

theorem arows5053 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5053 = true := by
  rw [show D2M8K2.u5053 = KTree.node D2M8K2.u5051 (nat_lit 11096166) (nat_lit 2459318148) (nat_lit 0) D2M8K2.u5052 from rfl, allE_node, arows5051, irow5053, arows5052]
  all_goals rfl

theorem atot5053 : totK PD2M8K2 D2M8K2.u5053 = [0, 0, 504967304728, 1663806698398, 1255497346122, 137882660270, 1239866073, 0] := by
  rw [show D2M8K2.u5053 = KTree.node D2M8K2.u5051 (nat_lit 11096166) (nat_lit 2459318148) (nat_lit 0) D2M8K2.u5052 from rfl, totK_node, atot5051, atot5052]
  decide +kernel

theorem arows5056 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5056 = true := by
  rw [show D2M8K2.u5056 = KTree.node D2M8K2.u5054 (nat_lit 11104998) (nat_lit 3880930485) (nat_lit 0) D2M8K2.u5055 from rfl, allE_node, arows5054, irow5056, arows5055]
  all_goals rfl

theorem atot5056 : totK PD2M8K2 D2M8K2.u5056 = [0, 0, 603279545119, 1739884043356, 1118228418370, 134027419293, 1171084559, 0] := by
  rw [show D2M8K2.u5056 = KTree.node D2M8K2.u5054 (nat_lit 11104998) (nat_lit 3880930485) (nat_lit 0) D2M8K2.u5055 from rfl, totK_node, atot5054, atot5055]
  decide +kernel

theorem arows5060 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5060 = true := by
  rw [show D2M8K2.u5060 = KTree.node D2M8K2.u5058 (nat_lit 11108075) (nat_lit 1940739043) (nat_lit 0) D2M8K2.u5059 from rfl, allE_node, arows5058, irow5060, arows5059]
  all_goals rfl

theorem atot5060 : totK PD2M8K2 D2M8K2.u5060 = [0, 0, 419900698703, 1477038652416, 1320209777048, 285199014350, 12987777003, 0] := by
  rw [show D2M8K2.u5060 = KTree.node D2M8K2.u5058 (nat_lit 11108075) (nat_lit 1940739043) (nat_lit 0) D2M8K2.u5059 from rfl, totK_node, atot5058, atot5059]
  decide +kernel

theorem arows5063 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5063 = true := by
  rw [show D2M8K2.u5063 = KTree.node D2M8K2.u5061 (nat_lit 11112013) (nat_lit 1047006679) (nat_lit 0) D2M8K2.u5062 from rfl, allE_node, arows5061, irow5063, arows5062]
  all_goals rfl

theorem atot5063 : totK PD2M8K2 D2M8K2.u5063 = [0, 257732979108, 909849983525, 1335555977901, 931593171513, 141456564862, 3667207281, 0] := by
  rw [show D2M8K2.u5063 = KTree.node D2M8K2.u5061 (nat_lit 11112013) (nat_lit 1047006679) (nat_lit 0) D2M8K2.u5062 from rfl, totK_node, atot5061, atot5062]
  decide +kernel

theorem arows5068 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5068 = true := by
  rw [show D2M8K2.u5068 = KTree.node D2M8K2.u5066 (nat_lit 11117420) (nat_lit 3611904842) (nat_lit 0) D2M8K2.u5067 from rfl, allE_node, arows5066, irow5068, arows5067]
  all_goals rfl

theorem atot5068 : totK PD2M8K2 D2M8K2.u5068 = [0, 457994375660, 1582905828030, 1375916233528, 177696480631, 1369150432, 0, 0] := by
  rw [show D2M8K2.u5068 = KTree.node D2M8K2.u5066 (nat_lit 11117420) (nat_lit 3611904842) (nat_lit 0) D2M8K2.u5067 from rfl, totK_node, atot5066, atot5067]
  decide +kernel

theorem arows5071 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5071 = true := by
  rw [show D2M8K2.u5071 = KTree.node D2M8K2.u5069 (nat_lit 11120688) (nat_lit 3411638501) (nat_lit 0) D2M8K2.u5070 from rfl, allE_node, arows5069, irow5071, arows5070]
  all_goals rfl

theorem atot5071 : totK PD2M8K2 D2M8K2.u5071 = [0, 285115084240, 1199493686319, 1519623417260, 589286911055, 37559395790, 0, 0] := by
  rw [show D2M8K2.u5071 = KTree.node D2M8K2.u5069 (nat_lit 11120688) (nat_lit 3411638501) (nat_lit 0) D2M8K2.u5070 from rfl, totK_node, atot5069, atot5070]
  decide +kernel

theorem arows5075 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5075 = true := by
  rw [show D2M8K2.u5075 = KTree.node D2M8K2.u5073 (nat_lit 11123561) (nat_lit 1599769123) (nat_lit 0) D2M8K2.u5074 from rfl, allE_node, arows5073, irow5075, arows5074]
  all_goals rfl

theorem atot5075 : totK PD2M8K2 D2M8K2.u5075 = [0, 410021470586, 1443869786126, 1384175269518, 318181101722, 13049727234, 0, 0] := by
  rw [show D2M8K2.u5075 = KTree.node D2M8K2.u5073 (nat_lit 11123561) (nat_lit 1599769123) (nat_lit 0) D2M8K2.u5074 from rfl, totK_node, atot5073, atot5074]
  decide +kernel

theorem arows5078 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5078 = true := by
  rw [show D2M8K2.u5078 = KTree.node D2M8K2.u5076 (nat_lit 11126955) (nat_lit 3703598000) (nat_lit 0) D2M8K2.u5077 from rfl, allE_node, arows5076, irow5078, arows5077]
  all_goals rfl

theorem atot5078 : totK PD2M8K2 D2M8K2.u5078 = [0, 422309870676, 1435095362759, 1385134117367, 325289946269, 13250685261, 0, 0] := by
  rw [show D2M8K2.u5078 = KTree.node D2M8K2.u5076 (nat_lit 11126955) (nat_lit 3703598000) (nat_lit 0) D2M8K2.u5077 from rfl, totK_node, atot5076, atot5077]
  decide +kernel

theorem arows5084 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5084 = true := by
  rw [show D2M8K2.u5084 = KTree.node D2M8K2.u5082 (nat_lit 11130204) (nat_lit 3100890068) (nat_lit 0) D2M8K2.u5083 from rfl, allE_node, arows5082, irow5084, arows5083]
  all_goals rfl

theorem atot5084 : totK PD2M8K2 D2M8K2.u5084 = [0, 269119064056, 1374437486722, 1644386838812, 338488676259, 6350335412, 0, 0] := by
  rw [show D2M8K2.u5084 = KTree.node D2M8K2.u5082 (nat_lit 11130204) (nat_lit 3100890068) (nat_lit 0) D2M8K2.u5083 from rfl, totK_node, atot5082, atot5083]
  decide +kernel

theorem arows5087 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5087 = true := by
  rw [show D2M8K2.u5087 = KTree.node D2M8K2.u5085 (nat_lit 11137598) (nat_lit 2564085372) (nat_lit 0) D2M8K2.u5086 from rfl, allE_node, arows5085, irow5087, arows5086]
  all_goals rfl

theorem atot5087 : totK PD2M8K2 D2M8K2.u5087 = [0, 0, 503813287935, 1669724392824, 1176300429021, 138907103850, 1138244013, 0] := by
  rw [show D2M8K2.u5087 = KTree.node D2M8K2.u5085 (nat_lit 11137598) (nat_lit 2564085372) (nat_lit 0) D2M8K2.u5086 from rfl, totK_node, atot5085, atot5086]
  decide +kernel

theorem arows5091 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5091 = true := by
  rw [show D2M8K2.u5091 = KTree.node D2M8K2.u5089 (nat_lit 11142758) (nat_lit 4137008514) (nat_lit 0) D2M8K2.u5090 from rfl, allE_node, arows5089, irow5091, arows5090]
  all_goals rfl

theorem atot5091 : totK PD2M8K2 D2M8K2.u5091 = [0, 0, 743978827825, 1902083722127, 888980244786, 49741935705, 0, 0] := by
  rw [show D2M8K2.u5091 = KTree.node D2M8K2.u5089 (nat_lit 11142758) (nat_lit 4137008514) (nat_lit 0) D2M8K2.u5090 from rfl, totK_node, atot5089, atot5090]
  decide +kernel

theorem arows5094 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5094 = true := by
  rw [show D2M8K2.u5094 = KTree.node D2M8K2.u5092 (nat_lit 11149395) (nat_lit 3700908241) (nat_lit 0) D2M8K2.u5093 from rfl, allE_node, arows5092, irow5094, arows5093]
  all_goals rfl

theorem atot5094 : totK PD2M8K2 D2M8K2.u5094 = [0, 0, 687991260817, 1859818031977, 979345218139, 64346640741, 0, 0] := by
  rw [show D2M8K2.u5094 = KTree.node D2M8K2.u5092 (nat_lit 11149395) (nat_lit 3700908241) (nat_lit 0) D2M8K2.u5093 from rfl, totK_node, atot5092, atot5093]
  decide +kernel

theorem arows5099 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5099 = true := by
  rw [show D2M8K2.u5099 = KTree.node D2M8K2.u5097 (nat_lit 11198062) (nat_lit 3006373761) (nat_lit 0) D2M8K2.u5098 from rfl, allE_node, arows5097, irow5099, arows5098]
  all_goals rfl

theorem atot5099 : totK PD2M8K2 D2M8K2.u5099 = [0, 0, 420863695807, 1542174424442, 1342274285088, 225664341007, 4977114383, 0] := by
  rw [show D2M8K2.u5099 = KTree.node D2M8K2.u5097 (nat_lit 11198062) (nat_lit 3006373761) (nat_lit 0) D2M8K2.u5098 from rfl, totK_node, atot5097, atot5098]
  decide +kernel

theorem arows5102 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5102 = true := by
  rw [show D2M8K2.u5102 = KTree.node D2M8K2.u5100 (nat_lit 11204956) (nat_lit 3969568137) (nat_lit 0) D2M8K2.u5101 from rfl, allE_node, arows5100, irow5102, arows5101]
  all_goals rfl

theorem atot5102 : totK PD2M8K2 D2M8K2.u5102 = [0, 0, 398794424657, 1549180565715, 1453796498592, 185158199745, 2533470052, 0] := by
  rw [show D2M8K2.u5102 = KTree.node D2M8K2.u5100 (nat_lit 11204956) (nat_lit 3969568137) (nat_lit 0) D2M8K2.u5101 from rfl, totK_node, atot5100, atot5101]
  decide +kernel

theorem arows5106 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5106 = true := by
  rw [show D2M8K2.u5106 = KTree.node D2M8K2.u5104 (nat_lit 11209003) (nat_lit 1797787643) (nat_lit 0) D2M8K2.u5105 from rfl, allE_node, arows5104, irow5106, arows5105]
  all_goals rfl

theorem atot5106 : totK PD2M8K2 D2M8K2.u5106 = [0, 0, 399033530833, 1592438374027, 1441014797562, 159390163260, 1198073392, 0] := by
  rw [show D2M8K2.u5106 = KTree.node D2M8K2.u5104 (nat_lit 11209003) (nat_lit 1797787643) (nat_lit 0) D2M8K2.u5105 from rfl, totK_node, atot5104, atot5105]
  decide +kernel

theorem arows5109 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5109 = true := by
  rw [show D2M8K2.u5109 = KTree.node D2M8K2.u5107 (nat_lit 11212477) (nat_lit 1212205351) (nat_lit 0) D2M8K2.u5108 from rfl, allE_node, arows5107, irow5109, arows5108]
  all_goals rfl

theorem atot5109 : totK PD2M8K2 D2M8K2.u5109 = [0, 0, 514645926568, 1658262475249, 1286754377447, 137319279004, 1096505104, 0] := by
  rw [show D2M8K2.u5109 = KTree.node D2M8K2.u5107 (nat_lit 11212477) (nat_lit 1212205351) (nat_lit 0) D2M8K2.u5108 from rfl, totK_node, atot5107, atot5108]
  decide +kernel

theorem arows5120 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5120 = true := by
  rw [show D2M8K2.u5120 = KTree.node D2M8K2.u5118 (nat_lit 11244012) (nat_lit 2447224439) (nat_lit 0) D2M8K2.u5119 from rfl, allE_node, arows5118, irow5120, arows5119]
  all_goals rfl

theorem atot5120 : totK PD2M8K2 D2M8K2.u5120 = [0, 0, 350078450232, 1328580226353, 1484993727836, 466881523661, 29394892645, 0] := by
  rw [show D2M8K2.u5120 = KTree.node D2M8K2.u5118 (nat_lit 11244012) (nat_lit 2447224439) (nat_lit 0) D2M8K2.u5119 from rfl, totK_node, atot5118, atot5119]
  decide +kernel

theorem arows5123 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5123 = true := by
  rw [show D2M8K2.u5123 = KTree.node D2M8K2.u5121 (nat_lit 11247036) (nat_lit 3113581972) (nat_lit 0) D2M8K2.u5122 from rfl, allE_node, arows5121, irow5123, arows5122]
  all_goals rfl

theorem atot5123 : totK PD2M8K2 D2M8K2.u5123 = [0, 0, 413609247844, 1477031165321, 1392761294352, 335753641055, 14925235974, 0] := by
  rw [show D2M8K2.u5123 = KTree.node D2M8K2.u5121 (nat_lit 11247036) (nat_lit 3113581972) (nat_lit 0) D2M8K2.u5122 from rfl, totK_node, atot5121, atot5122]
  decide +kernel

theorem arows5127 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5127 = true := by
  rw [show D2M8K2.u5127 = KTree.node D2M8K2.u5125 (nat_lit 11250546) (nat_lit 3451040612) (nat_lit 0) D2M8K2.u5126 from rfl, allE_node, arows5125, irow5127, arows5126]
  all_goals rfl

theorem atot5127 : totK PD2M8K2 D2M8K2.u5127 = [0, 0, 413852330708, 1474407483116, 1423903497382, 307912852362, 9126732845, 0] := by
  rw [show D2M8K2.u5127 = KTree.node D2M8K2.u5125 (nat_lit 11250546) (nat_lit 3451040612) (nat_lit 0) D2M8K2.u5126 from rfl, totK_node, atot5125, atot5126]
  decide +kernel

theorem arows5130 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5130 = true := by
  rw [show D2M8K2.u5130 = KTree.node D2M8K2.u5128 (nat_lit 11253816) (nat_lit 3342047042) (nat_lit 0) D2M8K2.u5129 from rfl, allE_node, arows5128, irow5130, arows5129]
  all_goals rfl

theorem atot5130 : totK PD2M8K2 D2M8K2.u5130 = [0, 0, 423269314517, 1582399015827, 1411544169208, 216813219649, 2348208889, 0] := by
  rw [show D2M8K2.u5130 = KTree.node D2M8K2.u5128 (nat_lit 11253816) (nat_lit 3342047042) (nat_lit 0) D2M8K2.u5129 from rfl, totK_node, atot5128, atot5129]
  decide +kernel

theorem arows5135 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5135 = true := by
  rw [show D2M8K2.u5135 = KTree.node D2M8K2.u5133 (nat_lit 11258238) (nat_lit 3908287112) (nat_lit 0) D2M8K2.u5134 from rfl, allE_node, arows5133, irow5135, arows5134]
  all_goals rfl

theorem atot5135 : totK PD2M8K2 D2M8K2.u5135 = [0, 0, 452959172694, 1477446368359, 1385968280116, 329604625041, 12315574980, 0] := by
  rw [show D2M8K2.u5135 = KTree.node D2M8K2.u5133 (nat_lit 11258238) (nat_lit 3908287112) (nat_lit 0) D2M8K2.u5134 from rfl, totK_node, atot5133, atot5134]
  decide +kernel

theorem arows5138 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5138 = true := by
  rw [show D2M8K2.u5138 = KTree.node D2M8K2.u5136 (nat_lit 11282697) (nat_lit 1805468829) (nat_lit 0) D2M8K2.u5137 from rfl, allE_node, arows5136, irow5138, arows5137]
  all_goals rfl

theorem atot5138 : totK PD2M8K2 D2M8K2.u5138 = [0, 0, 497397734558, 1619727572430, 1327137296255, 157446395775, 1310166938, 0] := by
  rw [show D2M8K2.u5138 = KTree.node D2M8K2.u5136 (nat_lit 11282697) (nat_lit 1805468829) (nat_lit 0) D2M8K2.u5137 from rfl, totK_node, atot5136, atot5137]
  decide +kernel

theorem arows5142 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5142 = true := by
  rw [show D2M8K2.u5142 = KTree.node D2M8K2.u5140 (nat_lit 11286347) (nat_lit 2357024104) (nat_lit 0) D2M8K2.u5141 from rfl, allE_node, arows5140, irow5142, arows5141]
  all_goals rfl

theorem atot5142 : totK PD2M8K2 D2M8K2.u5142 = [0, 0, 384291330622, 1429870317320, 1456112711519, 383867015386, 15013989272, 0] := by
  rw [show D2M8K2.u5142 = KTree.node D2M8K2.u5140 (nat_lit 11286347) (nat_lit 2357024104) (nat_lit 0) D2M8K2.u5141 from rfl, totK_node, atot5140, atot5141]
  decide +kernel

theorem arows5145 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5145 = true := by
  rw [show D2M8K2.u5145 = KTree.node D2M8K2.u5143 (nat_lit 11289426) (nat_lit 3021956194) (nat_lit 0) D2M8K2.u5144 from rfl, allE_node, arows5143, irow5145, arows5144]
  all_goals rfl

theorem atot5145 : totK PD2M8K2 D2M8K2.u5145 = [0, 0, 416662617221, 1453276887795, 1395161893013, 317268098992, 13049727234, 0] := by
  rw [show D2M8K2.u5145 = KTree.node D2M8K2.u5143 (nat_lit 11289426) (nat_lit 3021956194) (nat_lit 0) D2M8K2.u5144 from rfl, totK_node, atot5143, atot5144]
  decide +kernel

theorem arows5151 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5151 = true := by
  rw [show D2M8K2.u5151 = KTree.node D2M8K2.u5149 (nat_lit 11296263) (nat_lit 3638013176) (nat_lit 0) D2M8K2.u5150 from rfl, allE_node, arows5149, irow5151, arows5150]
  all_goals rfl

theorem atot5151 : totK PD2M8K2 D2M8K2.u5151 = [0, 0, 404189829010, 1512119707335, 1439133458434, 248332230364, 4980514959, 0] := by
  rw [show D2M8K2.u5151 = KTree.node D2M8K2.u5149 (nat_lit 11296263) (nat_lit 3638013176) (nat_lit 0) D2M8K2.u5150 from rfl, totK_node, atot5149, atot5150]
  decide +kernel

theorem arows5154 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5154 = true := by
  rw [show D2M8K2.u5154 = KTree.node D2M8K2.u5152 (nat_lit 11300906) (nat_lit 3904903498) (nat_lit 0) D2M8K2.u5153 from rfl, allE_node, arows5152, irow5154, arows5153]
  all_goals rfl

theorem atot5154 : totK PD2M8K2 D2M8K2.u5154 = [0, 0, 553354525099, 1688055687389, 1208478626607, 161474116943, 1391126877, 0] := by
  rw [show D2M8K2.u5154 = KTree.node D2M8K2.u5152 (nat_lit 11300906) (nat_lit 3904903498) (nat_lit 0) D2M8K2.u5153 from rfl, totK_node, atot5152, atot5153]
  decide +kernel

theorem arows5158 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5158 = true := by
  rw [show D2M8K2.u5158 = KTree.node D2M8K2.u5156 (nat_lit 11325926) (nat_lit 4150634215) (nat_lit 0) D2M8K2.u5157 from rfl, allE_node, arows5156, irow5158, arows5157]
  all_goals rfl

theorem atot5158 : totK PD2M8K2 D2M8K2.u5158 = [0, 0, 419551361581, 1594476686829, 1454027303190, 182925888850, 1310517177, 0] := by
  rw [show D2M8K2.u5158 = KTree.node D2M8K2.u5156 (nat_lit 11325926) (nat_lit 4150634215) (nat_lit 0) D2M8K2.u5157 from rfl, totK_node, atot5156, atot5157]
  decide +kernel

theorem arows5161 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5161 = true := by
  rw [show D2M8K2.u5161 = KTree.node D2M8K2.u5159 (nat_lit 11332539) (nat_lit 3787275780) (nat_lit 0) D2M8K2.u5160 from rfl, allE_node, arows5159, irow5161, arows5160]
  all_goals rfl

theorem atot5161 : totK PD2M8K2 D2M8K2.u5161 = [0, 0, 437716315755, 1461639348514, 1378674037188, 367400882402, 15066332673, 0] := by
  rw [show D2M8K2.u5161 = KTree.node D2M8K2.u5159 (nat_lit 11332539) (nat_lit 3787275780) (nat_lit 0) D2M8K2.u5160 from rfl, totK_node, atot5159, atot5160]
  decide +kernel

theorem arows5166 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5166 = true := by
  rw [show D2M8K2.u5166 = KTree.node D2M8K2.u5164 (nat_lit 11335779) (nat_lit 2929296303) (nat_lit 0) D2M8K2.u5165 from rfl, allE_node, arows5164, irow5166, arows5165]
  all_goals rfl

theorem atot5166 : totK PD2M8K2 D2M8K2.u5166 = [0, 0, 421225964062, 1414797013166, 1397545120238, 334713640194, 13170675918, 0] := by
  rw [show D2M8K2.u5166 = KTree.node D2M8K2.u5164 (nat_lit 11335779) (nat_lit 2929296303) (nat_lit 0) D2M8K2.u5165 from rfl, totK_node, atot5164, atot5165]
  decide +kernel

theorem arows5169 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5169 = true := by
  rw [show D2M8K2.u5169 = KTree.node D2M8K2.u5167 (nat_lit 11339352) (nat_lit 3585373603) (nat_lit 0) D2M8K2.u5168 from rfl, allE_node, arows5167, irow5169, arows5168]
  all_goals rfl

theorem atot5169 : totK PD2M8K2 D2M8K2.u5169 = [0, 0, 329866460627, 1488282131840, 1543227852896, 270911330384, 4980514959, 0] := by
  rw [show D2M8K2.u5169 = KTree.node D2M8K2.u5167 (nat_lit 11339352) (nat_lit 3585373603) (nat_lit 0) D2M8K2.u5168 from rfl, totK_node, atot5167, atot5168]
  decide +kernel

theorem arows5173 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5173 = true := by
  rw [show D2M8K2.u5173 = KTree.node D2M8K2.u5171 (nat_lit 11364436) (nat_lit 2709857969) (nat_lit 0) D2M8K2.u5172 from rfl, allE_node, arows5171, irow5173, arows5172]
  all_goals rfl

theorem atot5173 : totK PD2M8K2 D2M8K2.u5173 = [0, 0, 394617047136, 1512234722668, 1401334190939, 224547756456, 2725242758, 0] := by
  rw [show D2M8K2.u5173 = KTree.node D2M8K2.u5171 (nat_lit 11364436) (nat_lit 2709857969) (nat_lit 0) D2M8K2.u5172 from rfl, totK_node, atot5171, atot5172]
  decide +kernel

theorem arows5176 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5176 = true := by
  rw [show D2M8K2.u5176 = KTree.node D2M8K2.u5174 (nat_lit 11368106) (nat_lit 4196314580) (nat_lit 0) D2M8K2.u5175 from rfl, allE_node, arows5174, irow5176, arows5175]
  all_goals rfl

theorem atot5176 : totK PD2M8K2 D2M8K2.u5176 = [0, 0, 424982773380, 1426805182985, 1386688924299, 368647328095, 22301562661, 0] := by
  rw [show D2M8K2.u5176 = KTree.node D2M8K2.u5174 (nat_lit 11368106) (nat_lit 4196314580) (nat_lit 0) D2M8K2.u5175 from rfl, totK_node, atot5174, atot5175]
  decide +kernel

theorem arows5183 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5183 = true := by
  rw [show D2M8K2.u5183 = KTree.node D2M8K2.u5181 (nat_lit 11371063) (nat_lit 1481961020) (nat_lit 0) D2M8K2.u5182 from rfl, allE_node, arows5181, irow5183, arows5182]
  all_goals rfl

theorem atot5183 : totK PD2M8K2 D2M8K2.u5183 = [0, 0, 416614945303, 1458791881669, 1405862933508, 298846114899, 8435394354, 0] := by
  rw [show D2M8K2.u5183 = KTree.node D2M8K2.u5181 (nat_lit 11371063) (nat_lit 1481961020) (nat_lit 0) D2M8K2.u5182 from rfl, totK_node, atot5181, atot5182]
  decide +kernel

theorem arows5186 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5186 = true := by
  rw [show D2M8K2.u5186 = KTree.node D2M8K2.u5184 (nat_lit 11374738) (nat_lit 3887992169) (nat_lit 0) D2M8K2.u5185 from rfl, allE_node, arows5184, irow5186, arows5185]
  all_goals rfl

theorem atot5186 : totK PD2M8K2 D2M8K2.u5186 = [0, 0, 416827096798, 1478400908567, 1392034266251, 267283288318, 8162931527, 0] := by
  rw [show D2M8K2.u5186 = KTree.node D2M8K2.u5184 (nat_lit 11374738) (nat_lit 3887992169) (nat_lit 0) D2M8K2.u5185 from rfl, totK_node, atot5184, atot5185]
  decide +kernel

theorem arows5190 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5190 = true := by
  rw [show D2M8K2.u5190 = KTree.node D2M8K2.u5188 (nat_lit 11377864) (nat_lit 3794656059) (nat_lit 0) D2M8K2.u5189 from rfl, allE_node, arows5188, irow5190, arows5189]
  all_goals rfl

theorem atot5190 : totK PD2M8K2 D2M8K2.u5190 = [0, 0, 443584338047, 1514219966105, 1370949439374, 274425755637, 11927080088, 0] := by
  rw [show D2M8K2.u5190 = KTree.node D2M8K2.u5188 (nat_lit 11377864) (nat_lit 3794656059) (nat_lit 0) D2M8K2.u5189 from rfl, totK_node, atot5188, atot5189]
  decide +kernel

theorem arows5193 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5193 = true := by
  rw [show D2M8K2.u5193 = KTree.node D2M8K2.u5191 (nat_lit 11385085) (nat_lit 1151985785) (nat_lit 0) D2M8K2.u5192 from rfl, allE_node, arows5191, irow5193, arows5192]
  all_goals rfl

theorem atot5193 : totK PD2M8K2 D2M8K2.u5193 = [0, 0, 0, 862345931847, 1922222511348, 715980540955, 33787095718, 0] := by
  rw [show D2M8K2.u5193 = KTree.node D2M8K2.u5191 (nat_lit 11385085) (nat_lit 1151985785) (nat_lit 0) D2M8K2.u5192 from rfl, totK_node, atot5191, atot5192]
  decide +kernel

theorem arows5198 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5198 = true := by
  rw [show D2M8K2.u5198 = KTree.node D2M8K2.u5196 (nat_lit 11391724) (nat_lit 3939139242) (nat_lit 0) D2M8K2.u5197 from rfl, allE_node, arows5196, irow5198, arows5197]
  all_goals rfl

theorem atot5198 : totK PD2M8K2 D2M8K2.u5198 = [0, 0, 0, 825034504215, 1922765760185, 761703944521, 40761855869, 0] := by
  rw [show D2M8K2.u5198 = KTree.node D2M8K2.u5196 (nat_lit 11391724) (nat_lit 3939139242) (nat_lit 0) D2M8K2.u5197 from rfl, totK_node, atot5196, atot5197]
  decide +kernel

theorem arows5201 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5201 = true := by
  rw [show D2M8K2.u5201 = KTree.node D2M8K2.u5199 (nat_lit 11398584) (nat_lit 3160608274) (nat_lit 0) D2M8K2.u5200 from rfl, allE_node, arows5199, irow5201, arows5200]
  all_goals rfl

theorem atot5201 : totK PD2M8K2 D2M8K2.u5201 = [0, 0, 0, 588422679305, 1781256503255, 1075094725846, 95104988679, 0] := by
  rw [show D2M8K2.u5201 = KTree.node D2M8K2.u5199 (nat_lit 11398584) (nat_lit 3160608274) (nat_lit 0) D2M8K2.u5200 from rfl, totK_node, atot5199, atot5200]
  decide +kernel

theorem arows5205 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5205 = true := by
  rw [show D2M8K2.u5205 = KTree.node D2M8K2.u5203 (nat_lit 11447428) (nat_lit 3731426758) (nat_lit 0) D2M8K2.u5204 from rfl, allE_node, arows5203, irow5205, arows5204]
  all_goals rfl

theorem atot5205 : totK PD2M8K2 D2M8K2.u5205 = [0, 422119031540, 1391647212064, 1101194727918, 291903959647, 284610982050, 88149113051, 1493059870] := by
  rw [show D2M8K2.u5205 = KTree.node D2M8K2.u5203 (nat_lit 11447428) (nat_lit 3731426758) (nat_lit 0) D2M8K2.u5204 from rfl, totK_node, atot5203, atot5204]
  decide +kernel

theorem arows5208 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5208 = true := by
  rw [show D2M8K2.u5208 = KTree.node D2M8K2.u5206 (nat_lit 11454583) (nat_lit 2008820957) (nat_lit 0) D2M8K2.u5207 from rfl, allE_node, arows5206, irow5208, arows5207]
  all_goals rfl

theorem atot5208 : totK PD2M8K2 D2M8K2.u5208 = [0, 401071539684, 1504501922083, 1448722475537, 259621033978, 5398830306, 0, 0] := by
  rw [show D2M8K2.u5208 = KTree.node D2M8K2.u5206 (nat_lit 11454583) (nat_lit 2008820957) (nat_lit 0) D2M8K2.u5207 from rfl, totK_node, atot5206, atot5207]
  decide +kernel

theorem arows5214 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5214 = true := by
  rw [show D2M8K2.u5214 = KTree.node D2M8K2.u5212 (nat_lit 11458170) (nat_lit 3918445402) (nat_lit 0) D2M8K2.u5213 from rfl, allE_node, arows5212, irow5214, arows5213]
  all_goals rfl

theorem atot5214 : totK PD2M8K2 D2M8K2.u5214 = [0, 452229885645, 1511751127396, 1388389356590, 266081098236, 5455647540, 0, 0] := by
  rw [show D2M8K2.u5214 = KTree.node D2M8K2.u5212 (nat_lit 11458170) (nat_lit 3918445402) (nat_lit 0) D2M8K2.u5213 from rfl, totK_node, atot5212, atot5213]
  decide +kernel

theorem arows5217 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5217 = true := by
  rw [show D2M8K2.u5217 = KTree.node D2M8K2.u5215 (nat_lit 11465136) (nat_lit 3691976763) (nat_lit 0) D2M8K2.u5216 from rfl, allE_node, arows5215, irow5217, arows5216]
  all_goals rfl

theorem atot5217 : totK PD2M8K2 D2M8K2.u5217 = [0, 371853052056, 1435128714826, 1462152292614, 323874177771, 8710740030, 0, 0] := by
  rw [show D2M8K2.u5217 = KTree.node D2M8K2.u5215 (nat_lit 11465136) (nat_lit 3691976763) (nat_lit 0) D2M8K2.u5216 from rfl, totK_node, atot5215, atot5216]
  decide +kernel

theorem arows5221 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5221 = true := by
  rw [show D2M8K2.u5221 = KTree.node D2M8K2.u5219 (nat_lit 11468387) (nat_lit 1513907344) (nat_lit 0) D2M8K2.u5220 from rfl, allE_node, arows5219, irow5221, arows5220]
  all_goals rfl

theorem atot5221 : totK PD2M8K2 D2M8K2.u5221 = [0, 0, 487530361522, 1660054263958, 1218441519724, 142609234194, 1369150432, 0] := by
  rw [show D2M8K2.u5221 = KTree.node D2M8K2.u5219 (nat_lit 11468387) (nat_lit 1513907344) (nat_lit 0) D2M8K2.u5220 from rfl, totK_node, atot5219, atot5220]
  decide +kernel

theorem arows5224 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5224 = true := by
  rw [show D2M8K2.u5224 = KTree.node D2M8K2.u5222 (nat_lit 11475635) (nat_lit 2969931165) (nat_lit 0) D2M8K2.u5223 from rfl, allE_node, arows5222, irow5224, arows5223]
  all_goals rfl

theorem atot5224 : totK PD2M8K2 D2M8K2.u5224 = [0, 0, 753950694721, 1910928808433, 868792662883, 44314176490, 0, 0] := by
  rw [show D2M8K2.u5224 = KTree.node D2M8K2.u5222 (nat_lit 11475635) (nat_lit 2969931165) (nat_lit 0) D2M8K2.u5223 from rfl, totK_node, atot5222, atot5223]
  decide +kernel

theorem arows5229 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5229 = true := by
  rw [show D2M8K2.u5229 = KTree.node D2M8K2.u5227 (nat_lit 11485756) (nat_lit 3828168964) (nat_lit 0) D2M8K2.u5228 from rfl, allE_node, arows5227, irow5229, arows5228]
  all_goals rfl

theorem atot5229 : totK PD2M8K2 D2M8K2.u5229 = [0, 270969029763, 1122553057109, 1562586167868, 646831427257, 37333048441, 0, 0] := by
  rw [show D2M8K2.u5229 = KTree.node D2M8K2.u5227 (nat_lit 11485756) (nat_lit 3828168964) (nat_lit 0) D2M8K2.u5228 from rfl, totK_node, atot5227, atot5228]
  decide +kernel

theorem arows5232 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5232 = true := by
  rw [show D2M8K2.u5232 = KTree.node D2M8K2.u5230 (nat_lit 11493819) (nat_lit 3765549472) (nat_lit 0) D2M8K2.u5231 from rfl, allE_node, arows5230, irow5232, arows5231]
  all_goals rfl

theorem atot5232 : totK PD2M8K2 D2M8K2.u5232 = [0, 327116701770, 1234893661589, 1482927006981, 585960565188, 37609398105, 0, 0] := by
  rw [show D2M8K2.u5232 = KTree.node D2M8K2.u5230 (nat_lit 11493819) (nat_lit 3765549472) (nat_lit 0) D2M8K2.u5231 from rfl, totK_node, atot5230, atot5231]
  decide +kernel

theorem arows5236 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5236 = true := by
  rw [show D2M8K2.u5236 = KTree.node D2M8K2.u5234 (nat_lit 11496719) (nat_lit 2126493717) (nat_lit 0) D2M8K2.u5235 from rfl, allE_node, arows5234, irow5236, arows5235]
  all_goals rfl

theorem atot5236 : totK PD2M8K2 D2M8K2.u5236 = [0, 415255188606, 1464545741970, 1419479310327, 314502878448, 11612621147, 0, 0] := by
  rw [show D2M8K2.u5236 = KTree.node D2M8K2.u5234 (nat_lit 11496719) (nat_lit 2126493717) (nat_lit 0) D2M8K2.u5235 from rfl, totK_node, atot5234, atot5235]
  decide +kernel

theorem arows5239 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5239 = true := by
  rw [show D2M8K2.u5239 = KTree.node D2M8K2.u5237 (nat_lit 11500155) (nat_lit 3786523991) (nat_lit 0) D2M8K2.u5238 from rfl, allE_node, arows5237, irow5239, arows5238]
  all_goals rfl

theorem atot5239 : totK PD2M8K2 D2M8K2.u5239 = [0, 362464287530, 1396316725790, 1519312687620, 355634261908, 11772639972, 0, 0] := by
  rw [show D2M8K2.u5239 = KTree.node D2M8K2.u5237 (nat_lit 11500155) (nat_lit 3786523991) (nat_lit 0) D2M8K2.u5238 from rfl, totK_node, atot5237, atot5238]
  decide +kernel

theorem arows5247 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5247 = true := by
  rw [show D2M8K2.u5247 = KTree.node D2M8K2.u5245 (nat_lit 11504259) (nat_lit 3623515009) (nat_lit 0) D2M8K2.u5246 from rfl, allE_node, arows5245, irow5247, arows5246]
  all_goals rfl

theorem atot5247 : totK PD2M8K2 D2M8K2.u5247 = [0, 526285528029, 1666072390007, 1304036120071, 190151203517, 2575744806, 0, 0] := by
  rw [show D2M8K2.u5247 = KTree.node D2M8K2.u5245 (nat_lit 11504259) (nat_lit 3623515009) (nat_lit 0) D2M8K2.u5246 from rfl, totK_node, atot5245, atot5246]
  decide +kernel

theorem arows5250 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5250 = true := by
  rw [show D2M8K2.u5250 = KTree.node D2M8K2.u5248 (nat_lit 11507603) (nat_lit 2920618751) (nat_lit 0) D2M8K2.u5249 from rfl, allE_node, arows5248, irow5250, arows5249]
  all_goals rfl

theorem atot5250 : totK PD2M8K2 D2M8K2.u5250 = [0, 144995043752, 1027772029050, 1704771546520, 698557476172, 50500853437, 0, 0] := by
  rw [show D2M8K2.u5250 = KTree.node D2M8K2.u5248 (nat_lit 11507603) (nat_lit 2920618751) (nat_lit 0) D2M8K2.u5249 from rfl, totK_node, atot5248, atot5249]
  decide +kernel

theorem arows5254 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5254 = true := by
  rw [show D2M8K2.u5254 = KTree.node D2M8K2.u5252 (nat_lit 11514250) (nat_lit 3574503875) (nat_lit 0) D2M8K2.u5253 from rfl, allE_node, arows5252, irow5254, arows5253]
  all_goals rfl

theorem atot5254 : totK PD2M8K2 D2M8K2.u5254 = [0, 0, 327819879461, 1234346931995, 1470915402960, 549287211597, 36921873854, 0] := by
  rw [show D2M8K2.u5254 = KTree.node D2M8K2.u5252 (nat_lit 11514250) (nat_lit 3574503875) (nat_lit 0) D2M8K2.u5253 from rfl, totK_node, atot5252, atot5253]
  decide +kernel

theorem arows5257 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5257 = true := by
  rw [show D2M8K2.u5257 = KTree.node D2M8K2.u5255 (nat_lit 11517096) (nat_lit 3318641458) (nat_lit 0) D2M8K2.u5256 from rfl, allE_node, arows5255, irow5257, arows5256]
  all_goals rfl

theorem atot5257 : totK PD2M8K2 D2M8K2.u5257 = [0, 0, 445474123449, 1554083873738, 1379900320548, 236666534770, 5159868635, 0] := by
  rw [show D2M8K2.u5257 = KTree.node D2M8K2.u5255 (nat_lit 11517096) (nat_lit 3318641458) (nat_lit 0) D2M8K2.u5256 from rfl, totK_node, atot5255, atot5256]
  decide +kernel

theorem arows5262 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5262 = true := by
  rw [show D2M8K2.u5262 = KTree.node D2M8K2.u5260 (nat_lit 11520698) (nat_lit 3207013802) (nat_lit 0) D2M8K2.u5261 from rfl, allE_node, arows5260, irow5262, arows5261]
  all_goals rfl

theorem atot5262 : totK PD2M8K2 D2M8K2.u5262 = [0, 0, 434997563486, 1529503829379, 1419160172659, 263295143028, 5218872685, 0] := by
  rw [show D2M8K2.u5262 = KTree.node D2M8K2.u5260 (nat_lit 11520698) (nat_lit 3207013802) (nat_lit 0) D2M8K2.u5261 from rfl, totK_node, atot5260, atot5261]
  decide +kernel

theorem arows5265 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5265 = true := by
  rw [show D2M8K2.u5265 = KTree.node D2M8K2.u5263 (nat_lit 11525016) (nat_lit 2465308314) (nat_lit 0) D2M8K2.u5264 from rfl, allE_node, arows5263, irow5265, arows5264]
  all_goals rfl

theorem atot5265 : totK PD2M8K2 D2M8K2.u5265 = [0, 0, 524382720283, 1677384998731, 1295591517919, 169379673210, 1415142070, 0] := by
  rw [show D2M8K2.u5265 = KTree.node D2M8K2.u5263 (nat_lit 11525016) (nat_lit 2465308314) (nat_lit 0) D2M8K2.u5264 from rfl, totK_node, atot5263, atot5264]
  decide +kernel

theorem arows5269 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5269 = true := by
  rw [show D2M8K2.u5269 = KTree.node D2M8K2.u5267 (nat_lit 11528586) (nat_lit 3436937078) (nat_lit 0) D2M8K2.u5268 from rfl, allE_node, arows5267, irow5269, arows5268]
  all_goals rfl

theorem atot5269 : totK PD2M8K2 D2M8K2.u5269 = [0, 292271814381, 821437284043, 1082155578780, 1085173544655, 292456851790, 9302370699, 0] := by
  rw [show D2M8K2.u5269 = KTree.node D2M8K2.u5267 (nat_lit 11528586) (nat_lit 3436937078) (nat_lit 0) D2M8K2.u5268 from rfl, totK_node, atot5267, atot5268]
  decide +kernel

theorem arows5272 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5272 = true := by
  rw [show D2M8K2.u5272 = KTree.node D2M8K2.u5270 (nat_lit 11533011) (nat_lit 3716614309) (nat_lit 0) D2M8K2.u5271 from rfl, allE_node, arows5270, irow5272, arows5271]
  all_goals rfl

theorem atot5272 : totK PD2M8K2 D2M8K2.u5272 = [0, 503073467569, 1620540596683, 1346495706380, 180654614045, 1369150432, 0, 0] := by
  rw [show D2M8K2.u5272 = KTree.node D2M8K2.u5270 (nat_lit 11533011) (nat_lit 3716614309) (nat_lit 0) D2M8K2.u5271 from rfl, totK_node, atot5270, atot5271]
  decide +kernel

theorem arows5278 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5278 = true := by
  rw [show D2M8K2.u5278 = KTree.node D2M8K2.u5276 (nat_lit 11535777) (nat_lit 1792433777) (nat_lit 0) D2M8K2.u5277 from rfl, allE_node, arows5276, irow5278, arows5277]
  all_goals rfl

theorem atot5278 : totK PD2M8K2 D2M8K2.u5278 = [0, 266635319940, 1206581883451, 1546917505542, 590966706727, 37560868892, 0, 0] := by
  rw [show D2M8K2.u5278 = KTree.node D2M8K2.u5276 (nat_lit 11535777) (nat_lit 1792433777) (nat_lit 0) D2M8K2.u5277 from rfl, totK_node, atot5276, atot5277]
  decide +kernel

theorem arows5281 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5281 = true := by
  rw [show D2M8K2.u5281 = KTree.node D2M8K2.u5279 (nat_lit 11538633) (nat_lit 1745220646) (nat_lit 0) D2M8K2.u5280 from rfl, allE_node, arows5279, irow5281, arows5280]
  all_goals rfl

theorem atot5281 : totK PD2M8K2 D2M8K2.u5281 = [0, 412210410262, 1438688074027, 1428476120467, 329080687752, 13049727234, 0, 0] := by
  rw [show D2M8K2.u5281 = KTree.node D2M8K2.u5279 (nat_lit 11538633) (nat_lit 1745220646) (nat_lit 0) D2M8K2.u5280 from rfl, totK_node, atot5279, atot5280]
  decide +kernel

theorem arows5285 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5285 = true := by
  rw [show D2M8K2.u5285 = KTree.node D2M8K2.u5283 (nat_lit 11546638) (nat_lit 4017857514) (nat_lit 0) D2M8K2.u5284 from rfl, allE_node, arows5283, irow5285, arows5284]
  all_goals rfl

theorem atot5285 : totK PD2M8K2 D2M8K2.u5285 = [0, 512866193935, 1654667324796, 1284904175468, 187025135386, 3884009855, 0, 0] := by
  rw [show D2M8K2.u5285 = KTree.node D2M8K2.u5283 (nat_lit 11546638) (nat_lit 4017857514) (nat_lit 0) D2M8K2.u5284 from rfl, totK_node, atot5283, atot5284]
  decide +kernel

theorem arows5288 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5288 = true := by
  rw [show D2M8K2.u5288 = KTree.node D2M8K2.u5286 (nat_lit 11549838) (nat_lit 3641769313) (nat_lit 0) D2M8K2.u5287 from rfl, allE_node, arows5286, irow5288, arows5287]
  all_goals rfl

theorem atot5288 : totK PD2M8K2 D2M8K2.u5288 = [0, 0, 838726863464, 1926007570144, 745498969616, 36862924779, 0, 0] := by
  rw [show D2M8K2.u5288 = KTree.node D2M8K2.u5286 (nat_lit 11549838) (nat_lit 3641769313) (nat_lit 0) D2M8K2.u5287 from rfl, totK_node, atot5286, atot5287]
  decide +kernel

theorem arows5293 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5293 = true := by
  rw [show D2M8K2.u5293 = KTree.node D2M8K2.u5291 (nat_lit 11554015) (nat_lit 1834732408) (nat_lit 0) D2M8K2.u5292 from rfl, allE_node, arows5291, irow5293, arows5292]
  all_goals rfl

theorem atot5293 : totK PD2M8K2 D2M8K2.u5293 = [0, 0, 503813903153, 1670022152961, 1272124505065, 148187212195, 1206465782, 0] := by
  rw [show D2M8K2.u5293 = KTree.node D2M8K2.u5291 (nat_lit 11554015) (nat_lit 1834732408) (nat_lit 0) D2M8K2.u5292 from rfl, totK_node, atot5291, atot5292]
  decide +kernel

theorem arows5296 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5296 = true := by
  rw [show D2M8K2.u5296 = KTree.node D2M8K2.u5294 (nat_lit 11558568) (nat_lit 3408572275) (nat_lit 0) D2M8K2.u5295 from rfl, allE_node, arows5294, irow5296, arows5295]
  all_goals rfl

theorem atot5296 : totK PD2M8K2 D2M8K2.u5296 = [0, 0, 419084213737, 1483265452666, 1356369925579, 288737687890, 9467545976, 0] := by
  rw [show D2M8K2.u5296 = KTree.node D2M8K2.u5294 (nat_lit 11558568) (nat_lit 3408572275) (nat_lit 0) D2M8K2.u5295 from rfl, totK_node, atot5294, atot5295]
  decide +kernel

theorem arows5300 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5300 = true := by
  rw [show D2M8K2.u5300 = KTree.node D2M8K2.u5298 (nat_lit 11566107) (nat_lit 3566259868) (nat_lit 0) D2M8K2.u5299 from rfl, allE_node, arows5298, irow5300, arows5299]
  all_goals rfl

theorem atot5300 : totK PD2M8K2 D2M8K2.u5300 = [0, 0, 520381324973, 1702492251442, 1233108642230, 138860783480, 1330264907, 0] := by
  rw [show D2M8K2.u5300 = KTree.node D2M8K2.u5298 (nat_lit 11566107) (nat_lit 3566259868) (nat_lit 0) D2M8K2.u5299 from rfl, totK_node, atot5298, atot5299]
  decide +kernel

theorem arows5303 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5303 = true := by
  rw [show D2M8K2.u5303 = KTree.node D2M8K2.u5301 (nat_lit 11571709) (nat_lit 1186107345) (nat_lit 0) D2M8K2.u5302 from rfl, allE_node, arows5301, irow5303, arows5302]
  all_goals rfl

theorem atot5303 : totK PD2M8K2 D2M8K2.u5303 = [0, 378914462040, 1405274207138, 1410627467747, 375207078234, 18845624966, 0, 0] := by
  rw [show D2M8K2.u5303 = KTree.node D2M8K2.u5301 (nat_lit 11571709) (nat_lit 1186107345) (nat_lit 0) D2M8K2.u5302 from rfl, totK_node, atot5301, atot5302]
  decide +kernel

theorem arows5310 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5310 = true := by
  rw [show D2M8K2.u5310 = KTree.node D2M8K2.u5308 (nat_lit 11575446) (nat_lit 3502672015) (nat_lit 0) D2M8K2.u5309 from rfl, allE_node, arows5308, irow5310, arows5309]
  all_goals rfl

theorem atot5310 : totK PD2M8K2 D2M8K2.u5310 = [0, 420789728411, 1440066852492, 1398938594153, 401769071046, 28205077490, 0, 0] := by
  rw [show D2M8K2.u5310 = KTree.node D2M8K2.u5308 (nat_lit 11575446) (nat_lit 3502672015) (nat_lit 0) D2M8K2.u5309 from rfl, totK_node, atot5308, atot5309]
  decide +kernel

theorem arows5313 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5313 = true := by
  rw [show D2M8K2.u5313 = KTree.node D2M8K2.u5311 (nat_lit 11581962) (nat_lit 3914212688) (nat_lit 0) D2M8K2.u5312 from rfl, allE_node, arows5311, irow5313, arows5312]
  all_goals rfl

theorem atot5313 : totK PD2M8K2 D2M8K2.u5313 = [0, 438320121704, 1455098356906, 1372608913746, 351648526382, 10551942191, 0, 0] := by
  rw [show D2M8K2.u5313 = KTree.node D2M8K2.u5311 (nat_lit 11581962) (nat_lit 3914212688) (nat_lit 0) D2M8K2.u5312 from rfl, totK_node, atot5311, atot5312]
  decide +kernel

theorem arows5317 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5317 = true := by
  rw [show D2M8K2.u5317 = KTree.node D2M8K2.u5315 (nat_lit 11585044) (nat_lit 3533850096) (nat_lit 0) D2M8K2.u5316 from rfl, allE_node, arows5315, irow5317, arows5316]
  all_goals rfl

theorem atot5317 : totK PD2M8K2 D2M8K2.u5317 = [0, 327348471015, 1430153574552, 1545460670145, 326237248167, 12052611869, 0, 0] := by
  rw [show D2M8K2.u5317 = KTree.node D2M8K2.u5315 (nat_lit 11585044) (nat_lit 3533850096) (nat_lit 0) D2M8K2.u5316 from rfl, totK_node, atot5315, atot5316]
  decide +kernel

theorem arows5320 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5320 = true := by
  rw [show D2M8K2.u5320 = KTree.node D2M8K2.u5318 (nat_lit 11589100) (nat_lit 3180665991) (nat_lit 0) D2M8K2.u5319 from rfl, allE_node, arows5318, irow5320, arows5319]
  all_goals rfl

theorem atot5320 : totK PD2M8K2 D2M8K2.u5320 = [0, 426423859968, 1427319333424, 1392799706008, 347526224792, 9914383380, 0, 0] := by
  rw [show D2M8K2.u5320 = KTree.node D2M8K2.u5318 (nat_lit 11589100) (nat_lit 3180665991) (nat_lit 0) D2M8K2.u5319 from rfl, totK_node, atot5318, atot5319]
  decide +kernel

theorem arows5325 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5325 = true := by
  rw [show D2M8K2.u5325 = KTree.node D2M8K2.u5323 (nat_lit 11592724) (nat_lit 2771401034) (nat_lit 0) D2M8K2.u5324 from rfl, allE_node, arows5323, irow5325, arows5324]
  all_goals rfl

theorem atot5325 : totK PD2M8K2 D2M8K2.u5325 = [0, 0, 526680912809, 1684403548020, 1195154565091, 133662131684, 1239866073, 0] := by
  rw [show D2M8K2.u5325 = KTree.node D2M8K2.u5323 (nat_lit 11592724) (nat_lit 2771401034) (nat_lit 0) D2M8K2.u5324 from rfl, totK_node, atot5323, atot5324]
  decide +kernel

theorem arows5328 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5328 = true := by
  rw [show D2M8K2.u5328 = KTree.node D2M8K2.u5326 (nat_lit 11596515) (nat_lit 3472512267) (nat_lit 0) D2M8K2.u5327 from rfl, allE_node, arows5326, irow5328, arows5327]
  all_goals rfl

theorem atot5328 : totK PD2M8K2 D2M8K2.u5328 = [0, 0, 711684326732, 1862148458208, 999094784067, 77950748365, 0, 0] := by
  rw [show D2M8K2.u5328 = KTree.node D2M8K2.u5326 (nat_lit 11596515) (nat_lit 3472512267) (nat_lit 0) D2M8K2.u5327 from rfl, totK_node, atot5326, atot5327]
  decide +kernel

theorem arows5332 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5332 = true := by
  rw [show D2M8K2.u5332 = KTree.node D2M8K2.u5330 (nat_lit 11604890) (nat_lit 3646718218) (nat_lit 0) D2M8K2.u5331 from rfl, allE_node, arows5330, irow5332, arows5331]
  all_goals rfl

theorem atot5332 : totK PD2M8K2 D2M8K2.u5332 = [0, 0, 415133049447, 1484233113521, 1375948855019, 290149611758, 9527367360, 0] := by
  rw [show D2M8K2.u5332 = KTree.node D2M8K2.u5330 (nat_lit 11604890) (nat_lit 3646718218) (nat_lit 0) D2M8K2.u5331 from rfl, totK_node, atot5330, atot5331]
  decide +kernel

theorem arows5335 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5335 = true := by
  rw [show D2M8K2.u5335 = KTree.node D2M8K2.u5333 (nat_lit 11609248) (nat_lit 1966602328) (nat_lit 0) D2M8K2.u5334 from rfl, allE_node, arows5333, irow5335, arows5334]
  all_goals rfl

theorem atot5335 : totK PD2M8K2 D2M8K2.u5335 = [0, 121950136720, 692464887200, 1510266198078, 1135749965699, 140165628039, 1376099875, 0] := by
  rw [show D2M8K2.u5335 = KTree.node D2M8K2.u5333 (nat_lit 11609248) (nat_lit 1966602328) (nat_lit 0) D2M8K2.u5334 from rfl, totK_node, atot5333, atot5334]
  decide +kernel

theorem arows5341 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5341 = true := by
  rw [show D2M8K2.u5341 = KTree.node D2M8K2.u5339 (nat_lit 11655563) (nat_lit 2094083533) (nat_lit 0) D2M8K2.u5340 from rfl, allE_node, arows5339, irow5341, arows5340]
  all_goals rfl

theorem atot5341 : totK PD2M8K2 D2M8K2.u5341 = [0, 457292466443, 1590374512914, 1372989641458, 181026511846, 1369150432, 0, 0] := by
  rw [show D2M8K2.u5341 = KTree.node D2M8K2.u5339 (nat_lit 11655563) (nat_lit 2094083533) (nat_lit 0) D2M8K2.u5340 from rfl, totK_node, atot5339, atot5340]
  decide +kernel

theorem arows5344 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5344 = true := by
  rw [show D2M8K2.u5344 = KTree.node D2M8K2.u5342 (nat_lit 11659419) (nat_lit 3765844345) (nat_lit 0) D2M8K2.u5343 from rfl, allE_node, arows5342, irow5344, arows5343]
  all_goals rfl

theorem atot5344 : totK PD2M8K2 D2M8K2.u5344 = [0, 330086523988, 1228384829496, 1472995411920, 573210263173, 37516618231, 0, 0] := by
  rw [show D2M8K2.u5344 = KTree.node D2M8K2.u5342 (nat_lit 11659419) (nat_lit 3765844345) (nat_lit 0) D2M8K2.u5343 from rfl, totK_node, atot5342, atot5343]
  decide +kernel

theorem arows5348 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5348 = true := by
  rw [show D2M8K2.u5348 = KTree.node D2M8K2.u5346 (nat_lit 11662258) (nat_lit 4169072756) (nat_lit 0) D2M8K2.u5347 from rfl, allE_node, arows5346, irow5348, arows5347]
  all_goals rfl

theorem atot5348 : totK PD2M8K2 D2M8K2.u5348 = [0, 400723942218, 1429767188263, 1427912799861, 323421946164, 11627360713, 0, 0] := by
  rw [show D2M8K2.u5348 = KTree.node D2M8K2.u5346 (nat_lit 11662258) (nat_lit 4169072756) (nat_lit 0) D2M8K2.u5347 from rfl, totK_node, atot5346, atot5347]
  decide +kernel

theorem arows5351 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5351 = true := by
  rw [show D2M8K2.u5351 = KTree.node D2M8K2.u5349 (nat_lit 11665632) (nat_lit 3306375579) (nat_lit 0) D2M8K2.u5350 from rfl, allE_node, arows5349, irow5351, arows5350]
  all_goals rfl

theorem atot5351 : totK PD2M8K2 D2M8K2.u5351 = [0, 373380936182, 1428796454701, 1453794961185, 334559778281, 11781118163, 0, 0] := by
  rw [show D2M8K2.u5351 = KTree.node D2M8K2.u5349 (nat_lit 11665632) (nat_lit 3306375579) (nat_lit 0) D2M8K2.u5350 from rfl, totK_node, atot5349, atot5350]
  decide +kernel

theorem arows5356 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5356 = true := by
  rw [show D2M8K2.u5356 = KTree.node D2M8K2.u5354 (nat_lit 11672400) (nat_lit 3526957631) (nat_lit 0) D2M8K2.u5355 from rfl, allE_node, arows5354, irow5356, arows5355]
  all_goals rfl

theorem atot5356 : totK PD2M8K2 D2M8K2.u5356 = [0, 429080094848, 1472081543846, 1414228852014, 320025898601, 8710740030, 0, 0] := by
  rw [show D2M8K2.u5356 = KTree.node D2M8K2.u5354 (nat_lit 11672400) (nat_lit 3526957631) (nat_lit 0) D2M8K2.u5355 from rfl, totK_node, atot5354, atot5355]
  decide +kernel

theorem arows5359 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5359 = true := by
  rw [show D2M8K2.u5359 = KTree.node D2M8K2.u5357 (nat_lit 11675593) (nat_lit 1486006251) (nat_lit 0) D2M8K2.u5358 from rfl, allE_node, arows5357, irow5359, arows5358]
  all_goals rfl

theorem atot5359 : totK PD2M8K2 D2M8K2.u5359 = [0, 0, 489647906793, 1641721481729, 1259312711150, 140607435157, 1310285577, 0] := by
  rw [show D2M8K2.u5359 = KTree.node D2M8K2.u5357 (nat_lit 11675593) (nat_lit 1486006251) (nat_lit 0) D2M8K2.u5358 from rfl, totK_node, atot5357, atot5358]
  decide +kernel

theorem arows5363 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5363 = true := by
  rw [show D2M8K2.u5363 = KTree.node D2M8K2.u5361 (nat_lit 11679326) (nat_lit 3889182706) (nat_lit 0) D2M8K2.u5362 from rfl, allE_node, arows5361, irow5363, arows5362]
  all_goals rfl

theorem atot5363 : totK PD2M8K2 D2M8K2.u5363 = [0, 0, 741917106176, 1847149770914, 978547488541, 81905717354, 0, 0] := by
  rw [show D2M8K2.u5363 = KTree.node D2M8K2.u5361 (nat_lit 11679326) (nat_lit 3889182706) (nat_lit 0) D2M8K2.u5362 from rfl, totK_node, atot5361, atot5362]
  decide +kernel

theorem arows5366 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5366 = true := by
  rw [show D2M8K2.u5366 = KTree.node D2M8K2.u5364 (nat_lit 11684488) (nat_lit 3650433623) (nat_lit 0) D2M8K2.u5365 from rfl, allE_node, arows5364, irow5366, arows5365]
  all_goals rfl

theorem atot5366 : totK PD2M8K2 D2M8K2.u5366 = [0, 0, 432158574878, 1556943524932, 1339712409357, 210381418404, 4879840392, 0] := by
  rw [show D2M8K2.u5366 = KTree.node D2M8K2.u5364 (nat_lit 11684488) (nat_lit 3650433623) (nat_lit 0) D2M8K2.u5365 from rfl, totK_node, atot5364, atot5365]
  decide +kernel

theorem arows5375 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5375 = true := by
  rw [show D2M8K2.u5375 = KTree.node D2M8K2.u5373 (nat_lit 11691666) (nat_lit 3382543583) (nat_lit 0) D2M8K2.u5374 from rfl, allE_node, arows5373, irow5375, arows5374]
  all_goals rfl

theorem atot5375 : totK PD2M8K2 D2M8K2.u5375 = [0, 0, 478787007892, 1588030839425, 1316538786166, 211038593958, 4931404646, 0] := by
  rw [show D2M8K2.u5375 = KTree.node D2M8K2.u5373 (nat_lit 11691666) (nat_lit 3382543583) (nat_lit 0) D2M8K2.u5374 from rfl, totK_node, atot5373, atot5374]
  decide +kernel

theorem arows5378 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5378 = true := by
  rw [show D2M8K2.u5378 = KTree.node D2M8K2.u5376 (nat_lit 11694848) (nat_lit 2384650015) (nat_lit 0) D2M8K2.u5377 from rfl, allE_node, arows5376, irow5378, arows5377]
  all_goals rfl

theorem atot5378 : totK PD2M8K2 D2M8K2.u5378 = [0, 0, 359006802001, 1344174864482, 1408666532909, 394464014502, 21751168066, 0] := by
  rw [show D2M8K2.u5378 = KTree.node D2M8K2.u5376 (nat_lit 11694848) (nat_lit 2384650015) (nat_lit 0) D2M8K2.u5377 from rfl, totK_node, atot5376, atot5377]
  decide +kernel

theorem arows5382 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5382 = true := by
  rw [show D2M8K2.u5382 = KTree.node D2M8K2.u5380 (nat_lit 11698355) (nat_lit 2893975146) (nat_lit 0) D2M8K2.u5381 from rfl, allE_node, arows5380, irow5382, arows5381]
  all_goals rfl

theorem atot5382 : totK PD2M8K2 D2M8K2.u5382 = [0, 0, 503177460520, 1644713962802, 1263748879547, 157255395838, 1369150432, 0] := by
  rw [show D2M8K2.u5382 = KTree.node D2M8K2.u5380 (nat_lit 11698355) (nat_lit 2893975146) (nat_lit 0) D2M8K2.u5381 from rfl, totK_node, atot5380, atot5381]
  decide +kernel

theorem arows5385 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5385 = true := by
  rw [show D2M8K2.u5385 = KTree.node D2M8K2.u5383 (nat_lit 11707182) (nat_lit 3844506042) (nat_lit 0) D2M8K2.u5384 from rfl, allE_node, arows5383, irow5385, arows5384]
  all_goals rfl

theorem atot5385 : totK PD2M8K2 D2M8K2.u5385 = [0, 0, 798975201559, 1899743633008, 889624108673, 53958295806, 0, 0] := by
  rw [show D2M8K2.u5385 = KTree.node D2M8K2.u5383 (nat_lit 11707182) (nat_lit 3844506042) (nat_lit 0) D2M8K2.u5384 from rfl, totK_node, atot5383, atot5384]
  decide +kernel

theorem arows5390 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5390 = true := by
  rw [show D2M8K2.u5390 = KTree.node D2M8K2.u5388 (nat_lit 11741249) (nat_lit 2216843154) (nat_lit 0) D2M8K2.u5389 from rfl, allE_node, arows5388, irow5390, arows5389]
  all_goals rfl

theorem atot5390 : totK PD2M8K2 D2M8K2.u5390 = [0, 0, 469026559758, 1531197383993, 1309812137860, 343973336100, 25330798048, 0] := by
  rw [show D2M8K2.u5390 = KTree.node D2M8K2.u5388 (nat_lit 11741249) (nat_lit 2216843154) (nat_lit 0) D2M8K2.u5389 from rfl, totK_node, atot5388, atot5389]
  decide +kernel

theorem arows5393 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5393 = true := by
  rw [show D2M8K2.u5393 = KTree.node D2M8K2.u5391 (nat_lit 11744057) (nat_lit 1190163074) (nat_lit 0) D2M8K2.u5392 from rfl, allE_node, arows5391, irow5393, arows5392]
  all_goals rfl

theorem atot5393 : totK PD2M8K2 D2M8K2.u5393 = [0, 0, 412487348626, 1416129077637, 1414126273940, 381350842635, 12169858900, 0] := by
  rw [show D2M8K2.u5393 = KTree.node D2M8K2.u5391 (nat_lit 11744057) (nat_lit 1190163074) (nat_lit 0) D2M8K2.u5392 from rfl, totK_node, atot5391, atot5392]
  decide +kernel

theorem arows5397 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5397 = true := by
  rw [show D2M8K2.u5397 = KTree.node D2M8K2.u5395 (nat_lit 11747835) (nat_lit 3755701842) (nat_lit 0) D2M8K2.u5396 from rfl, allE_node, arows5395, irow5397, arows5396]
  all_goals rfl

theorem atot5397 : totK PD2M8K2 D2M8K2.u5397 = [0, 0, 412744569175, 1491446313132, 1428972544297, 291390211985, 6583681375, 0] := by
  rw [show D2M8K2.u5397 = KTree.node D2M8K2.u5395 (nat_lit 11747835) (nat_lit 3755701842) (nat_lit 0) D2M8K2.u5396 from rfl, totK_node, atot5395, atot5396]
  decide +kernel

theorem arows5400 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5400 = true := by
  rw [show D2M8K2.u5400 = KTree.node D2M8K2.u5398 (nat_lit 11751237) (nat_lit 1471370634) (nat_lit 0) D2M8K2.u5399 from rfl, allE_node, arows5398, irow5400, arows5399]
  all_goals rfl

theorem atot5400 : totK PD2M8K2 D2M8K2.u5400 = [0, 0, 344349645462, 1441613952235, 1540586842487, 320363438014, 6656488309, 0] := by
  rw [show D2M8K2.u5400 = KTree.node D2M8K2.u5398 (nat_lit 11751237) (nat_lit 1471370634) (nat_lit 0) D2M8K2.u5399 from rfl, totK_node, atot5398, atot5399]
  decide +kernel

theorem arows5406 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5406 = true := by
  rw [show D2M8K2.u5406 = KTree.node D2M8K2.u5404 (nat_lit 11755330) (nat_lit 4097396695) (nat_lit 0) D2M8K2.u5405 from rfl, allE_node, arows5404, irow5406, arows5405]
  all_goals rfl

theorem atot5406 : totK PD2M8K2 D2M8K2.u5406 = [0, 0, 428191728307, 1448345678823, 1398552337402, 327195673232, 6275136774, 0] := by
  rw [show D2M8K2.u5406 = KTree.node D2M8K2.u5404 (nat_lit 11755330) (nat_lit 4097396695) (nat_lit 0) D2M8K2.u5405 from rfl, totK_node, atot5404, atot5405]
  decide +kernel

theorem arows5409 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5409 = true := by
  rw [show D2M8K2.u5409 = KTree.node D2M8K2.u5407 (nat_lit 11779661) (nat_lit 2137984949) (nat_lit 0) D2M8K2.u5408 from rfl, allE_node, arows5407, irow5409, arows5408]
  all_goals rfl

theorem atot5409 : totK PD2M8K2 D2M8K2.u5409 = [0, 0, 498471294204, 1511276463298, 1310055811243, 277592061161, 12775735723, 0] := by
  rw [show D2M8K2.u5409 = KTree.node D2M8K2.u5407 (nat_lit 11779661) (nat_lit 2137984949) (nat_lit 0) D2M8K2.u5408 from rfl, totK_node, atot5407, atot5408]
  decide +kernel

theorem arows5413 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5413 = true := by
  rw [show D2M8K2.u5413 = KTree.node D2M8K2.u5411 (nat_lit 11783694) (nat_lit 3828501755) (nat_lit 0) D2M8K2.u5412 from rfl, allE_node, arows5411, irow5413, arows5412]
  all_goals rfl

theorem atot5413 : totK PD2M8K2 D2M8K2.u5413 = [0, 0, 326938660048, 1262373240542, 1475685414823, 537729595031, 32764831815, 0] := by
  rw [show D2M8K2.u5413 = KTree.node D2M8K2.u5411 (nat_lit 11783694) (nat_lit 3828501755) (nat_lit 0) D2M8K2.u5412 from rfl, totK_node, atot5411, atot5412]
  decide +kernel

theorem arows5416 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5416 = true := by
  rw [show D2M8K2.u5416 = KTree.node D2M8K2.u5414 (nat_lit 11786484) (nat_lit 3057864351) (nat_lit 0) D2M8K2.u5415 from rfl, allE_node, arows5414, irow5416, arows5415]
  all_goals rfl

theorem atot5416 : totK PD2M8K2 D2M8K2.u5416 = [0, 0, 401043574775, 1468814402719, 1408265415931, 308067693599, 9483552028, 0] := by
  rw [show D2M8K2.u5416 = KTree.node D2M8K2.u5414 (nat_lit 11786484) (nat_lit 3057864351) (nat_lit 0) D2M8K2.u5415 from rfl, totK_node, atot5414, atot5415]
  decide +kernel

theorem arows5421 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5421 = true := by
  rw [show D2M8K2.u5421 = KTree.node D2M8K2.u5419 (nat_lit 11793969) (nat_lit 1576394500) (nat_lit 0) D2M8K2.u5420 from rfl, allE_node, arows5419, irow5421, arows5420]
  all_goals rfl

theorem atot5421 : totK PD2M8K2 D2M8K2.u5421 = [0, 0, 584081391615, 1680382830270, 1235068233238, 159879777153, 1394496256, 0] := by
  rw [show D2M8K2.u5421 = KTree.node D2M8K2.u5419 (nat_lit 11793969) (nat_lit 1576394500) (nat_lit 0) D2M8K2.u5420 from rfl, totK_node, atot5419, atot5420]
  decide +kernel

theorem arows5424 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5424 = true := by
  rw [show D2M8K2.u5424 = KTree.node D2M8K2.u5422 (nat_lit 11797740) (nat_lit 2819188723) (nat_lit 0) D2M8K2.u5423 from rfl, allE_node, arows5422, irow5424, arows5423]
  all_goals rfl

theorem atot5424 : totK PD2M8K2 D2M8K2.u5424 = [0, 0, 164043053881, 1097946419432, 1723143469453, 548826862737, 20727495402, 0] := by
  rw [show D2M8K2.u5424 = KTree.node D2M8K2.u5422 (nat_lit 11797740) (nat_lit 2819188723) (nat_lit 0) D2M8K2.u5423 from rfl, totK_node, atot5422, atot5423]
  decide +kernel

theorem arows5428 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5428 = true := by
  rw [show D2M8K2.u5428 = KTree.node D2M8K2.u5426 (nat_lit 11803493) (nat_lit 2317268510) (nat_lit 0) D2M8K2.u5427 from rfl, allE_node, arows5426, irow5428, arows5427]
  all_goals rfl

theorem atot5428 : totK PD2M8K2 D2M8K2.u5428 = [0, 0, 0, 917836040545, 1901871816121, 752442782178, 39626936183, 0] := by
  rw [show D2M8K2.u5428 = KTree.node D2M8K2.u5426 (nat_lit 11803493) (nat_lit 2317268510) (nat_lit 0) D2M8K2.u5427 from rfl, totK_node, atot5426, atot5427]
  decide +kernel

theorem arows5431 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5431 = true := by
  rw [show D2M8K2.u5431 = KTree.node D2M8K2.u5429 (nat_lit 11812617) (nat_lit 1838833587) (nat_lit 0) D2M8K2.u5430 from rfl, allE_node, arows5429, irow5431, arows5430]
  all_goals rfl

theorem atot5431 : totK PD2M8K2 D2M8K2.u5431 = [0, 0, 0, 609405628312, 1750149946821, 1045933742981, 122936037542, 1501162176] := by
  rw [show D2M8K2.u5431 = KTree.node D2M8K2.u5429 (nat_lit 11812617) (nat_lit 1838833587) (nat_lit 0) D2M8K2.u5430 from rfl, totK_node, atot5429, atot5430]
  decide +kernel

theorem arows5438 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5438 = true := by
  rw [show D2M8K2.u5438 = KTree.node D2M8K2.u5436 (nat_lit 11820402) (nat_lit 3443727579) (nat_lit 0) D2M8K2.u5437 from rfl, allE_node, arows5436, irow5438, arows5437]
  all_goals rfl

theorem atot5438 : totK PD2M8K2 D2M8K2.u5438 = [0, 0, 375755889938, 1314668795235, 1430002574159, 442506517199, 23138407544, 0] := by
  rw [show D2M8K2.u5438 = KTree.node D2M8K2.u5436 (nat_lit 11820402) (nat_lit 3443727579) (nat_lit 0) D2M8K2.u5437 from rfl, totK_node, atot5436, atot5437]
  decide +kernel

theorem arows5441 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5441 = true := by
  rw [show D2M8K2.u5441 = KTree.node D2M8K2.u5439 (nat_lit 11824301) (nat_lit 1967479992) (nat_lit 0) D2M8K2.u5440 from rfl, allE_node, arows5439, irow5441, arows5440]
  all_goals rfl

theorem atot5441 : totK PD2M8K2 D2M8K2.u5441 = [0, 0, 420245802233, 1435450040326, 1387486576497, 397932300950, 24731817083, 0] := by
  rw [show D2M8K2.u5441 = KTree.node D2M8K2.u5439 (nat_lit 11824301) (nat_lit 1967479992) (nat_lit 0) D2M8K2.u5440 from rfl, totK_node, atot5439, atot5440]
  decide +kernel

theorem arows5445 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5445 = true := by
  rw [show D2M8K2.u5445 = KTree.node D2M8K2.u5443 (nat_lit 11830852) (nat_lit 2730668835) (nat_lit 0) D2M8K2.u5444 from rfl, allE_node, arows5443, irow5445, arows5444]
  all_goals rfl

theorem atot5445 : totK PD2M8K2 D2M8K2.u5445 = [0, 0, 434520278417, 1482629384304, 1375743803647, 318975706669, 9271841644, 0] := by
  rw [show D2M8K2.u5445 = KTree.node D2M8K2.u5443 (nat_lit 11830852) (nat_lit 2730668835) (nat_lit 0) D2M8K2.u5444 from rfl, totK_node, atot5443, atot5444]
  decide +kernel

theorem arows5448 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5448 = true := by
  rw [show D2M8K2.u5448 = KTree.node D2M8K2.u5446 (nat_lit 11834359) (nat_lit 2352607513) (nat_lit 0) D2M8K2.u5447 from rfl, allE_node, arows5446, irow5448, arows5447]
  all_goals rfl

theorem atot5448 : totK PD2M8K2 D2M8K2.u5448 = [0, 0, 406321351569, 1439140240543, 1450500544626, 321574715095, 9809781201, 0] := by
  rw [show D2M8K2.u5448 = KTree.node D2M8K2.u5446 (nat_lit 11834359) (nat_lit 2352607513) (nat_lit 0) D2M8K2.u5447 from rfl, totK_node, atot5446, atot5447]
  decide +kernel

theorem arows5453 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5453 = true := by
  rw [show D2M8K2.u5453 = KTree.node D2M8K2.u5451 (nat_lit 11838505) (nat_lit 1451707094) (nat_lit 0) D2M8K2.u5452 from rfl, allE_node, arows5451, irow5453, arows5452]
  all_goals rfl

theorem atot5453 : totK PD2M8K2 D2M8K2.u5453 = [0, 0, 342011648963, 1362153174195, 1497160548917, 390693454602, 11413764339, 0] := by
  rw [show D2M8K2.u5453 = KTree.node D2M8K2.u5451 (nat_lit 11838505) (nat_lit 1451707094) (nat_lit 0) D2M8K2.u5452 from rfl, totK_node, atot5451, atot5452]
  decide +kernel

theorem arows5456 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5456 = true := by
  rw [show D2M8K2.u5456 = KTree.node D2M8K2.u5454 (nat_lit 11844228) (nat_lit 1372710191) (nat_lit 0) D2M8K2.u5455 from rfl, allE_node, arows5454, irow5456, arows5455]
  all_goals rfl

theorem atot5456 : totK PD2M8K2 D2M8K2.u5456 = [0, 0, 0, 935114988868, 1926442163712, 704295707685, 32055016807, 0] := by
  rw [show D2M8K2.u5456 = KTree.node D2M8K2.u5454 (nat_lit 11844228) (nat_lit 1372710191) (nat_lit 0) D2M8K2.u5455 from rfl, totK_node, atot5454, atot5455]
  decide +kernel

theorem arows5460 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5460 = true := by
  rw [show D2M8K2.u5460 = KTree.node D2M8K2.u5458 (nat_lit 11852761) (nat_lit 1135733444) (nat_lit 0) D2M8K2.u5459 from rfl, allE_node, arows5458, irow5460, arows5459]
  all_goals rfl

theorem atot5460 : totK PD2M8K2 D2M8K2.u5460 = [0, 0, 0, 630080751889, 1702798364183, 1088655007163, 131283729131, 1510868091] := by
  rw [show D2M8K2.u5460 = KTree.node D2M8K2.u5458 (nat_lit 11852761) (nat_lit 1135733444) (nat_lit 0) D2M8K2.u5459 from rfl, totK_node, atot5458, atot5459]
  decide +kernel

theorem arows5463 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5463 = true := by
  rw [show D2M8K2.u5463 = KTree.node D2M8K2.u5461 (nat_lit 11859178) (nat_lit 3996530250) (nat_lit 0) D2M8K2.u5462 from rfl, allE_node, arows5461, irow5463, arows5462]
  all_goals rfl

theorem atot5463 : totK PD2M8K2 D2M8K2.u5463 = [0, 0, 394317118174, 1284637844026, 1373224380744, 516907804941, 30315463353, 0] := by
  rw [show D2M8K2.u5463 = KTree.node D2M8K2.u5461 (nat_lit 11859178) (nat_lit 3996530250) (nat_lit 0) D2M8K2.u5462 from rfl, totK_node, atot5461, atot5462]
  decide +kernel

theorem arows5469 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5469 = true := by
  rw [show D2M8K2.u5469 = KTree.node D2M8K2.u5467 (nat_lit 11906531) (nat_lit 2837519378) (nat_lit 0) D2M8K2.u5468 from rfl, allE_node, arows5467, irow5469, arows5468]
  all_goals rfl

theorem atot5469 : totK PD2M8K2 D2M8K2.u5469 = [0, 0, 427581875239, 1592306736153, 1418332715202, 197939848953, 1369150432, 0] := by
  rw [show D2M8K2.u5469 = KTree.node D2M8K2.u5467 (nat_lit 11906531) (nat_lit 2837519378) (nat_lit 0) D2M8K2.u5468 from rfl, totK_node, atot5467, atot5468]
  decide +kernel

theorem arows5472 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5472 = true := by
  rw [show D2M8K2.u5472 = KTree.node D2M8K2.u5470 (nat_lit 11909364) (nat_lit 2274193746) (nat_lit 0) D2M8K2.u5471 from rfl, allE_node, arows5470, irow5472, arows5471]
  all_goals rfl

theorem atot5472 : totK PD2M8K2 D2M8K2.u5472 = [0, 0, 395254857413, 1265879233288, 1379501326389, 524738594954, 30407432289, 0] := by
  rw [show D2M8K2.u5472 = KTree.node D2M8K2.u5470 (nat_lit 11909364) (nat_lit 2274193746) (nat_lit 0) D2M8K2.u5471 from rfl, totK_node, atot5470, atot5471]
  decide +kernel

theorem arows5476 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5476 = true := by
  rw [show D2M8K2.u5476 = KTree.node D2M8K2.u5474 (nat_lit 11912687) (nat_lit 2777452777) (nat_lit 0) D2M8K2.u5475 from rfl, allE_node, arows5474, irow5476, arows5475]
  all_goals rfl

theorem atot5476 : totK PD2M8K2 D2M8K2.u5476 = [0, 0, 422640910403, 1477875427170, 1407894658569, 279389952269, 6480510805, 0] := by
  rw [show D2M8K2.u5476 = KTree.node D2M8K2.u5474 (nat_lit 11912687) (nat_lit 2777452777) (nat_lit 0) D2M8K2.u5475 from rfl, totK_node, atot5474, atot5475]
  decide +kernel

theorem arows5479 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5479 = true := by
  rw [show D2M8K2.u5479 = KTree.node D2M8K2.u5477 (nat_lit 11919745) (nat_lit 1573165124) (nat_lit 0) D2M8K2.u5478 from rfl, allE_node, arows5477, irow5479, arows5478]
  all_goals rfl

theorem atot5479 : totK PD2M8K2 D2M8K2.u5479 = [0, 0, 397597961303, 1466630136133, 1452068204651, 293388769283, 6544344931, 0] := by
  rw [show D2M8K2.u5479 = KTree.node D2M8K2.u5477 (nat_lit 11919745) (nat_lit 1573165124) (nat_lit 0) D2M8K2.u5478 from rfl, totK_node, atot5477, atot5478]
  decide +kernel

theorem arows5484 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5484 = true := by
  rw [show D2M8K2.u5484 = KTree.node D2M8K2.u5482 (nat_lit 11922578) (nat_lit 2709195033) (nat_lit 0) D2M8K2.u5483 from rfl, allE_node, arows5482, irow5484, arows5483]
  all_goals rfl

theorem atot5484 : totK PD2M8K2 D2M8K2.u5484 = [0, 0, 56835226932, 966386216815, 1860437392591, 629736530922, 25754467639, 0] := by
  rw [show D2M8K2.u5484 = KTree.node D2M8K2.u5482 (nat_lit 11922578) (nat_lit 2709195033) (nat_lit 0) D2M8K2.u5483 from rfl, totK_node, atot5482, atot5483]
  decide +kernel

theorem arows5487 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5487 = true := by
  rw [show D2M8K2.u5487 = KTree.node D2M8K2.u5485 (nat_lit 11928123) (nat_lit 3764946393) (nat_lit 0) D2M8K2.u5486 from rfl, allE_node, arows5485, irow5487, arows5486]
  all_goals rfl

theorem atot5487 : totK PD2M8K2 D2M8K2.u5487 = [0, 0, 0, 808567977064, 1904203091152, 836200653655, 50035870933, 0] := by
  rw [show D2M8K2.u5487 = KTree.node D2M8K2.u5485 (nat_lit 11928123) (nat_lit 3764946393) (nat_lit 0) D2M8K2.u5486 from rfl, totK_node, atot5485, atot5486]
  decide +kernel

theorem arows5491 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5491 = true := by
  rw [show D2M8K2.u5491 = KTree.node D2M8K2.u5489 (nat_lit 11933698) (nat_lit 4106802390) (nat_lit 0) D2M8K2.u5490 from rfl, allE_node, arows5489, irow5491, arows5490]
  all_goals rfl

theorem atot5491 : totK PD2M8K2 D2M8K2.u5491 = [0, 0, 0, 498337376954, 1708926861416, 1194033243819, 137360977528, 1406452163] := by
  rw [show D2M8K2.u5491 = KTree.node D2M8K2.u5489 (nat_lit 11933698) (nat_lit 4106802390) (nat_lit 0) D2M8K2.u5490 from rfl, totK_node, atot5489, atot5490]
  decide +kernel

theorem arows5494 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5494 = true := by
  rw [show D2M8K2.u5494 = KTree.node D2M8K2.u5492 (nat_lit 11941042) (nat_lit 4143879860) (nat_lit 0) D2M8K2.u5493 from rfl, allE_node, arows5492, irow5494, arows5493]
  all_goals rfl

theorem atot5494 : totK PD2M8K2 D2M8K2.u5494 = [0, 0, 0, 441381476526, 1655789552767, 1313967554940, 163766183120, 1415681459] := by
  rw [show D2M8K2.u5494 = KTree.node D2M8K2.u5492 (nat_lit 11941042) (nat_lit 4143879860) (nat_lit 0) D2M8K2.u5493 from rfl, totK_node, atot5492, atot5493]
  decide +kernel

theorem arows5502 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5502 = true := by
  rw [show D2M8K2.u5502 = KTree.node D2M8K2.u5500 (nat_lit 11944662) (nat_lit 2776089533) (nat_lit 0) D2M8K2.u5501 from rfl, allE_node, arows5500, irow5502, arows5501]
  all_goals rfl

theorem atot5502 : totK PD2M8K2 D2M8K2.u5502 = [442425092496, 1218846307151, 728464134746, 86753044387, 249210617755, 617659404114, 235492752849, 10297110227] := by
  rw [show D2M8K2.u5502 = KTree.node D2M8K2.u5500 (nat_lit 11944662) (nat_lit 2776089533) (nat_lit 0) D2M8K2.u5501 from rfl, totK_node, atot5500, atot5501]
  decide +kernel

theorem arows5505 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5505 = true := by
  rw [show D2M8K2.u5505 = KTree.node D2M8K2.u5503 (nat_lit 11951433) (nat_lit 1820515306) (nat_lit 0) D2M8K2.u5504 from rfl, allE_node, arows5503, irow5505, arows5504]
  all_goals rfl

theorem atot5505 : totK PD2M8K2 D2M8K2.u5505 = [421179288580, 1560946315672, 1444455001137, 208407226276, 1164319620, 0, 0, 0] := by
  rw [show D2M8K2.u5505 = KTree.node D2M8K2.u5503 (nat_lit 11951433) (nat_lit 1820515306) (nat_lit 0) D2M8K2.u5504 from rfl, totK_node, atot5503, atot5504]
  decide +kernel

theorem arows5509 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5509 = true := by
  rw [show D2M8K2.u5509 = KTree.node D2M8K2.u5507 (nat_lit 11954872) (nat_lit 2915757099) (nat_lit 0) D2M8K2.u5508 from rfl, allE_node, arows5507, irow5509, arows5508]
  all_goals rfl

theorem atot5509 : totK PD2M8K2 D2M8K2.u5509 = [399936882060, 1423038774251, 1397585788773, 318783917350, 13083481006, 0, 0, 0] := by
  rw [show D2M8K2.u5509 = KTree.node D2M8K2.u5507 (nat_lit 11954872) (nat_lit 2915757099) (nat_lit 0) D2M8K2.u5508 from rfl, totK_node, atot5507, atot5508]
  decide +kernel

theorem arows5512 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5512 = true := by
  rw [show D2M8K2.u5512 = KTree.node D2M8K2.u5510 (nat_lit 11958254) (nat_lit 3574757201) (nat_lit 0) D2M8K2.u5511 from rfl, allE_node, arows5510, irow5512, arows5511]
  all_goals rfl

theorem atot5512 : totK PD2M8K2 D2M8K2.u5512 = [414217542484, 1432565222632, 1354867658710, 319984730888, 13149116973, 0, 0, 0] := by
  rw [show D2M8K2.u5512 = KTree.node D2M8K2.u5510 (nat_lit 11958254) (nat_lit 3574757201) (nat_lit 0) D2M8K2.u5511 from rfl, totK_node, atot5510, atot5511]
  decide +kernel

theorem arows5517 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5517 = true := by
  rw [show D2M8K2.u5517 = KTree.node D2M8K2.u5515 (nat_lit 11961787) (nat_lit 1166241734) (nat_lit 0) D2M8K2.u5516 from rfl, allE_node, arows5515, irow5517, arows5516]
  all_goals rfl

theorem atot5517 : totK PD2M8K2 D2M8K2.u5517 = [419234341778, 1500204568268, 1405963000724, 264977754897, 5152749158, 0, 0, 0] := by
  rw [show D2M8K2.u5517 = KTree.node D2M8K2.u5515 (nat_lit 11961787) (nat_lit 1166241734) (nat_lit 0) D2M8K2.u5516 from rfl, totK_node, atot5515, atot5516]
  decide +kernel

theorem arows5520 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5520 = true := by
  rw [show D2M8K2.u5520 = KTree.node D2M8K2.u5518 (nat_lit 11964939) (nat_lit 1920708392) (nat_lit 0) D2M8K2.u5519 from rfl, allE_node, arows5518, irow5520, arows5519]
  all_goals rfl

theorem atot5520 : totK PD2M8K2 D2M8K2.u5520 = [0, 740781781213, 1864130066575, 869108281091, 57254028816, 0, 0, 0] := by
  rw [show D2M8K2.u5520 = KTree.node D2M8K2.u5518 (nat_lit 11964939) (nat_lit 1920708392) (nat_lit 0) D2M8K2.u5519 from rfl, totK_node, atot5518, atot5519]
  decide +kernel

theorem arows5524 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5524 = true := by
  rw [show D2M8K2.u5524 = KTree.node D2M8K2.u5522 (nat_lit 11972043) (nat_lit 3718190072) (nat_lit 0) D2M8K2.u5523 from rfl, allE_node, arows5522, irow5524, arows5523]
  all_goals rfl

theorem atot5524 : totK PD2M8K2 D2M8K2.u5524 = [0, 507584877991, 1680745265795, 1193582780081, 155896586253, 1369150432, 0, 0] := by
  rw [show D2M8K2.u5524 = KTree.node D2M8K2.u5522 (nat_lit 11972043) (nat_lit 3718190072) (nat_lit 0) D2M8K2.u5523 from rfl, totK_node, atot5522, atot5523]
  decide +kernel

theorem arows5527 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5527 = true := by
  rw [show D2M8K2.u5527 = KTree.node D2M8K2.u5525 (nat_lit 11978620) (nat_lit 3570082827) (nat_lit 0) D2M8K2.u5526 from rfl, allE_node, arows5525, irow5527, arows5526]
  all_goals rfl

theorem atot5527 : totK PD2M8K2 D2M8K2.u5527 = [0, 724449449539, 1861181393155, 882866491636, 47079448034, 0, 0, 0] := by
  rw [show D2M8K2.u5527 = KTree.node D2M8K2.u5525 (nat_lit 11978620) (nat_lit 3570082827) (nat_lit 0) D2M8K2.u5526 from rfl, totK_node, atot5525, atot5526]
  decide +kernel

theorem arows5533 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5533 = true := by
  rw [show D2M8K2.u5533 = KTree.node D2M8K2.u5531 (nat_lit 11983518) (nat_lit 3929778058) (nat_lit 0) D2M8K2.u5532 from rfl, allE_node, arows5531, irow5533, arows5532]
  all_goals rfl

theorem atot5533 : totK PD2M8K2 D2M8K2.u5533 = [334799102639, 1237831380558, 1432698645409, 550834794044, 29733020022, 0, 0, 0] := by
  rw [show D2M8K2.u5533 = KTree.node D2M8K2.u5531 (nat_lit 11983518) (nat_lit 3929778058) (nat_lit 0) D2M8K2.u5532 from rfl, totK_node, atot5531, atot5532]
  decide +kernel

theorem arows5536 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5536 = true := by
  rw [show D2M8K2.u5536 = KTree.node D2M8K2.u5534 (nat_lit 12030185) (nat_lit 1557136191) (nat_lit 0) D2M8K2.u5535 from rfl, allE_node, arows5534, irow5536, arows5535]
  all_goals rfl

theorem atot5536 : totK PD2M8K2 D2M8K2.u5536 = [434020499903, 1586098688542, 1434654247824, 203787651023, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u5536 = KTree.node D2M8K2.u5534 (nat_lit 12030185) (nat_lit 1557136191) (nat_lit 0) D2M8K2.u5535 from rfl, totK_node, atot5534, atot5535]
  decide +kernel

theorem arows5540 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5540 = true := by
  rw [show D2M8K2.u5540 = KTree.node D2M8K2.u5538 (nat_lit 12033892) (nat_lit 3769647798) (nat_lit 0) D2M8K2.u5539 from rfl, allE_node, arows5538, irow5540, arows5539]
  all_goals rfl

theorem atot5540 : totK PD2M8K2 D2M8K2.u5540 = [440862456571, 1360513211437, 1344161818376, 481559491393, 33318032364, 0, 0, 0] := by
  rw [show D2M8K2.u5540 = KTree.node D2M8K2.u5538 (nat_lit 12033892) (nat_lit 3769647798) (nat_lit 0) D2M8K2.u5539 from rfl, totK_node, atot5538, atot5539]
  decide +kernel

theorem arows5543 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5543 = true := by
  rw [show D2M8K2.u5543 = KTree.node D2M8K2.u5541 (nat_lit 12037030) (nat_lit 3841895814) (nat_lit 0) D2M8K2.u5542 from rfl, allE_node, arows5541, irow5543, arows5542]
  all_goals rfl

theorem atot5543 : totK PD2M8K2 D2M8K2.u5543 = [354966390490, 1390490151031, 1493235051224, 343830063089, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u5543 = KTree.node D2M8K2.u5541 (nat_lit 12037030) (nat_lit 3841895814) (nat_lit 0) D2M8K2.u5542 from rfl, totK_node, atot5541, atot5542]
  decide +kernel

theorem arows5548 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5548 = true := by
  rw [show D2M8K2.u5548 = KTree.node D2M8K2.u5546 (nat_lit 12044208) (nat_lit 3603996278) (nat_lit 0) D2M8K2.u5547 from rfl, allE_node, arows5546, irow5548, arows5547]
  all_goals rfl

theorem atot5548 : totK PD2M8K2 D2M8K2.u5548 = [469810943695, 1551034678691, 1349509445244, 240075834453, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u5548 = KTree.node D2M8K2.u5546 (nat_lit 12044208) (nat_lit 3603996278) (nat_lit 0) D2M8K2.u5547 from rfl, totK_node, atot5546, atot5547]
  decide +kernel

theorem arows5551 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5551 = true := by
  rw [show D2M8K2.u5551 = KTree.node D2M8K2.u5549 (nat_lit 12047452) (nat_lit 3900969224) (nat_lit 0) D2M8K2.u5550 from rfl, allE_node, arows5549, irow5551, arows5550]
  all_goals rfl

theorem atot5551 : totK PD2M8K2 D2M8K2.u5551 = [0, 847907351493, 1918802178438, 742978135254, 34147874903, 0, 0, 0] := by
  rw [show D2M8K2.u5551 = KTree.node D2M8K2.u5549 (nat_lit 12047452) (nat_lit 3900969224) (nat_lit 0) D2M8K2.u5550 from rfl, totK_node, atot5549, atot5550]
  decide +kernel

theorem arows5555 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5555 = true := by
  rw [show D2M8K2.u5555 = KTree.node D2M8K2.u5553 (nat_lit 12051465) (nat_lit 1897289975) (nat_lit 0) D2M8K2.u5554 from rfl, allE_node, arows5553, irow5555, arows5554]
  all_goals rfl

theorem atot5555 : totK PD2M8K2 D2M8K2.u5555 = [0, 519045034535, 1662767345428, 1259200010985, 151347886891, 1206465782, 0, 0] := by
  rw [show D2M8K2.u5555 = KTree.node D2M8K2.u5553 (nat_lit 12051465) (nat_lit 1897289975) (nat_lit 0) D2M8K2.u5554 from rfl, totK_node, atot5553, atot5554]
  decide +kernel

theorem arows5558 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5558 = true := by
  rw [show D2M8K2.u5558 = KTree.node D2M8K2.u5556 (nat_lit 12056177) (nat_lit 1582786887) (nat_lit 0) D2M8K2.u5557 from rfl, allE_node, arows5556, irow5558, arows5557]
  all_goals rfl

theorem atot5558 : totK PD2M8K2 D2M8K2.u5558 = [0, 388692806586, 1455679834966, 1384698661346, 308357471966, 13016197374, 0, 0] := by
  rw [show D2M8K2.u5558 = KTree.node D2M8K2.u5556 (nat_lit 12056177) (nat_lit 1582786887) (nat_lit 0) D2M8K2.u5557 from rfl, totK_node, atot5556, atot5557]
  decide +kernel

theorem arows5565 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5565 = true := by
  rw [show D2M8K2.u5565 = KTree.node D2M8K2.u5563 (nat_lit 12062792) (nat_lit 3786099746) (nat_lit 0) D2M8K2.u5564 from rfl, allE_node, arows5563, irow5565, arows5564]
  all_goals rfl

theorem atot5565 : totK PD2M8K2 D2M8K2.u5565 = [0, 471703398900, 1598413210006, 1241326418262, 177039489383, 4574395652, 0, 0] := by
  rw [show D2M8K2.u5565 = KTree.node D2M8K2.u5563 (nat_lit 12062792) (nat_lit 3786099746) (nat_lit 0) D2M8K2.u5564 from rfl, totK_node, atot5563, atot5564]
  decide +kernel

theorem arows5568 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5568 = true := by
  rw [show D2M8K2.u5568 = KTree.node D2M8K2.u5566 (nat_lit 12068448) (nat_lit 3619169329) (nat_lit 0) D2M8K2.u5567 from rfl, allE_node, arows5566, irow5568, arows5567]
  all_goals rfl

theorem atot5568 : totK PD2M8K2 D2M8K2.u5568 = [420970288622, 1345797479180, 1300796407468, 507182871537, 42777965325, 0, 0, 0] := by
  rw [show D2M8K2.u5568 = KTree.node D2M8K2.u5566 (nat_lit 12068448) (nat_lit 3619169329) (nat_lit 0) D2M8K2.u5567 from rfl, totK_node, atot5566, atot5567]
  decide +kernel

theorem arows5572 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5572 = true := by
  rw [show D2M8K2.u5572 = KTree.node D2M8K2.u5570 (nat_lit 12079034) (nat_lit 4284098850) (nat_lit 0) D2M8K2.u5571 from rfl, allE_node, arows5570, irow5572, arows5571]
  all_goals rfl

theorem atot5572 : totK PD2M8K2 D2M8K2.u5572 = [425767693660, 1579160182709, 1414612283424, 201045207911, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u5572 = KTree.node D2M8K2.u5570 (nat_lit 12079034) (nat_lit 4284098850) (nat_lit 0) D2M8K2.u5571 from rfl, totK_node, atot5570, atot5571]
  decide +kernel

theorem arows5575 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5575 = true := by
  rw [show D2M8K2.u5575 = KTree.node D2M8K2.u5573 (nat_lit 12082307) (nat_lit 2907559209) (nat_lit 0) D2M8K2.u5574 from rfl, allE_node, arows5573, irow5575, arows5574]
  all_goals rfl

theorem atot5575 : totK PD2M8K2 D2M8K2.u5575 = [398089907899, 1423835141974, 1398613499778, 338686888845, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u5575 = KTree.node D2M8K2.u5573 (nat_lit 12082307) (nat_lit 2907559209) (nat_lit 0) D2M8K2.u5574 from rfl, totK_node, atot5573, atot5574]
  decide +kernel

theorem arows5580 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5580 = true := by
  rw [show D2M8K2.u5580 = KTree.node D2M8K2.u5578 (nat_lit 12085968) (nat_lit 2228962707) (nat_lit 0) D2M8K2.u5579 from rfl, allE_node, arows5578, irow5580, arows5579]
  all_goals rfl

theorem atot5580 : totK PD2M8K2 D2M8K2.u5580 = [403614254217, 1498796707768, 1449369457881, 255756013001, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u5580 = KTree.node D2M8K2.u5578 (nat_lit 12085968) (nat_lit 2228962707) (nat_lit 0) D2M8K2.u5579 from rfl, totK_node, atot5578, atot5579]
  decide +kernel

theorem arows5583 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5583 = true := by
  rw [show D2M8K2.u5583 = KTree.node D2M8K2.u5581 (nat_lit 12089222) (nat_lit 3162881536) (nat_lit 0) D2M8K2.u5582 from rfl, allE_node, arows5581, irow5583, arows5582]
  all_goals rfl

theorem atot5583 : totK PD2M8K2 D2M8K2.u5583 = [0, 735376639432, 1903182402764, 862777485726, 45786614436, 0, 0, 0] := by
  rw [show D2M8K2.u5583 = KTree.node D2M8K2.u5581 (nat_lit 12089222) (nat_lit 3162881536) (nat_lit 0) D2M8K2.u5582 from rfl, totK_node, atot5581, atot5582]
  decide +kernel

theorem arows5587 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5587 = true := by
  rw [show D2M8K2.u5587 = KTree.node D2M8K2.u5585 (nat_lit 12099932) (nat_lit 3464841467) (nat_lit 0) D2M8K2.u5586 from rfl, allE_node, arows5585, irow5587, arows5586]
  all_goals rfl

theorem atot5587 : totK PD2M8K2 D2M8K2.u5587 = [0, 423701067216, 1552312880184, 1360031617400, 192031111104, 2410950632, 0, 0] := by
  rw [show D2M8K2.u5587 = KTree.node D2M8K2.u5585 (nat_lit 12099932) (nat_lit 3464841467) (nat_lit 0) D2M8K2.u5586 from rfl, totK_node, atot5585, atot5586]
  decide +kernel

theorem arows5590 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5590 = true := by
  rw [show D2M8K2.u5590 = KTree.node D2M8K2.u5588 (nat_lit 12103292) (nat_lit 3364050675) (nat_lit 0) D2M8K2.u5589 from rfl, allE_node, arows5588, irow5590, arows5589]
  all_goals rfl

theorem atot5590 : totK PD2M8K2 D2M8K2.u5590 = [0, 396196586699, 1438066656657, 1356636532976, 300540940901, 12987777003, 0, 0] := by
  rw [show D2M8K2.u5590 = KTree.node D2M8K2.u5588 (nat_lit 12103292) (nat_lit 3364050675) (nat_lit 0) D2M8K2.u5589 from rfl, totK_node, atot5588, atot5589]
  decide +kernel

theorem arows5596 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5596 = true := by
  rw [show D2M8K2.u5596 = KTree.node D2M8K2.u5594 (nat_lit 12106996) (nat_lit 4053130209) (nat_lit 0) D2M8K2.u5595 from rfl, allE_node, arows5594, irow5596, arows5595]
  all_goals rfl

theorem atot5596 : totK PD2M8K2 D2M8K2.u5596 = [176663725160, 774608856395, 1428108820687, 1042123949951, 151729852051, 3667207281, 0, 0] := by
  rw [show D2M8K2.u5596 = KTree.node D2M8K2.u5594 (nat_lit 12106996) (nat_lit 4053130209) (nat_lit 0) D2M8K2.u5595 from rfl, totK_node, atot5594, atot5595]
  decide +kernel

theorem arows5599 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5599 = true := by
  rw [show D2M8K2.u5599 = KTree.node D2M8K2.u5597 (nat_lit 12111823) (nat_lit 1629057090) (nat_lit 0) D2M8K2.u5598 from rfl, allE_node, arows5597, irow5599, arows5598]
  all_goals rfl

theorem atot5599 : totK PD2M8K2 D2M8K2.u5599 = [415343756011, 1552315117696, 1422508810155, 203506141052, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u5599 = KTree.node D2M8K2.u5597 (nat_lit 12111823) (nat_lit 1629057090) (nat_lit 0) D2M8K2.u5598 from rfl, totK_node, atot5597, atot5598]
  decide +kernel

theorem arows5603 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5603 = true := by
  rw [show D2M8K2.u5603 = KTree.node D2M8K2.u5601 (nat_lit 12115974) (nat_lit 3872665113) (nat_lit 0) D2M8K2.u5602 from rfl, allE_node, arows5601, irow5603, arows5602]
  all_goals rfl

theorem atot5603 : totK PD2M8K2 D2M8K2.u5603 = [409906295404, 1368854411989, 1363023302087, 461943592353, 30700521876, 0, 0, 0] := by
  rw [show D2M8K2.u5603 = KTree.node D2M8K2.u5601 (nat_lit 12115974) (nat_lit 3872665113) (nat_lit 0) D2M8K2.u5602 from rfl, totK_node, atot5601, atot5602]
  decide +kernel

theorem arows5606 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5606 = true := by
  rw [show D2M8K2.u5606 = KTree.node D2M8K2.u5604 (nat_lit 12119288) (nat_lit 3766573488) (nat_lit 0) D2M8K2.u5605 from rfl, allE_node, arows5604, irow5606, arows5605]
  all_goals rfl

theorem atot5606 : totK PD2M8K2 D2M8K2.u5606 = [396608771916, 1424930883058, 1419832672981, 330720702441, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u5606 = KTree.node D2M8K2.u5604 (nat_lit 12119288) (nat_lit 3766573488) (nat_lit 0) D2M8K2.u5605 from rfl, totK_node, atot5604, atot5605]
  decide +kernel

theorem arows5611 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5611 = true := by
  rw [show D2M8K2.u5611 = KTree.node D2M8K2.u5609 (nat_lit 12123102) (nat_lit 3879699817) (nat_lit 0) D2M8K2.u5610 from rfl, allE_node, arows5609, irow5611, arows5610]
  all_goals rfl

theorem atot5611 : totK PD2M8K2 D2M8K2.u5611 = [415376725039, 1417260353123, 1384454600772, 330688504891, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u5611 = KTree.node D2M8K2.u5609 (nat_lit 12123102) (nat_lit 3879699817) (nat_lit 0) D2M8K2.u5610 from rfl, totK_node, atot5609, atot5610]
  decide +kernel

theorem arows5614 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5614 = true := by
  rw [show D2M8K2.u5614 = KTree.node D2M8K2.u5612 (nat_lit 12126336) (nat_lit 3465929453) (nat_lit 0) D2M8K2.u5613 from rfl, allE_node, arows5612, irow5614, arows5613]
  all_goals rfl

theorem atot5614 : totK PD2M8K2 D2M8K2.u5614 = [160403090464, 1149137360670, 1718564120402, 511125477314, 23242077755, 0, 0, 0] := by
  rw [show D2M8K2.u5614 = KTree.node D2M8K2.u5612 (nat_lit 12126336) (nat_lit 3465929453) (nat_lit 0) D2M8K2.u5613 from rfl, totK_node, atot5612, atot5613]
  decide +kernel

theorem arows5618 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5618 = true := by
  rw [show D2M8K2.u5618 = KTree.node D2M8K2.u5616 (nat_lit 12133859) (nat_lit 2970790676) (nat_lit 0) D2M8K2.u5617 from rfl, allE_node, arows5616, irow5618, arows5617]
  all_goals rfl

theorem atot5618 : totK PD2M8K2 D2M8K2.u5618 = [0, 536910437071, 1717280361734, 1172996939697, 132102712924, 1138244013, 0, 0] := by
  rw [show D2M8K2.u5618 = KTree.node D2M8K2.u5616 (nat_lit 12133859) (nat_lit 2970790676) (nat_lit 0) D2M8K2.u5617 from rfl, totK_node, atot5616, atot5617]
  decide +kernel

theorem arows5621 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5621 = true := by
  rw [show D2M8K2.u5621 = KTree.node D2M8K2.u5619 (nat_lit 12139178) (nat_lit 3781560633) (nat_lit 0) D2M8K2.u5620 from rfl, allE_node, arows5619, irow5621, arows5620]
  all_goals rfl

theorem atot5621 : totK PD2M8K2 D2M8K2.u5621 = [0, 722644163332, 1881917463261, 920535694887, 51841389289, 0, 0, 0] := by
  rw [show D2M8K2.u5621 = KTree.node D2M8K2.u5619 (nat_lit 12139178) (nat_lit 3781560633) (nat_lit 0) D2M8K2.u5620 from rfl, totK_node, atot5619, atot5620]
  decide +kernel

end QECKChecks.D2M8K2
