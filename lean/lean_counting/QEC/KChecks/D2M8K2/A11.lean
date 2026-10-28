import QEC.Count.ChunksK3
import QEC.KChecks.D2M8K2.A10

namespace QECKChecks.D2M8K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows13194 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13194 = true := by
  rw [show D2M8K2.u13194 = KTree.node D2M8K2.t13200 (nat_lit 28591998) (nat_lit 4014156936) (nat_lit 0) D2M8K2.t13201 from rfl, allE_node, rows13200, irow13194, rows13201]
  all_goals rfl

theorem atot13194 : totK PD2M8K2 D2M8K2.u13194 = [0, 334648636632, 903586323632, 536299098535, 53561062821, 0, 0, 0] := by
  rw [show D2M8K2.u13194 = KTree.node D2M8K2.t13200 (nat_lit 28591998) (nat_lit 4014156936) (nat_lit 0) D2M8K2.t13201 from rfl, totK_node, tot13200, tot13201]
  decide +kernel

theorem arows13195 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13195 = true := by
  rw [show D2M8K2.u13195 = KTree.node D2M8K2.t13202 (nat_lit 28593542) (nat_lit 4180403854) (nat_lit 0) D2M8K2.t13203 from rfl, allE_node, rows13202, irow13195, rows13203]
  all_goals rfl

theorem atot13195 : totK PD2M8K2 D2M8K2.u13195 = [0, 93373242333, 580398392916, 867558900333, 248402502906, 6033099918, 0, 0] := by
  rw [show D2M8K2.u13195 = KTree.node D2M8K2.t13202 (nat_lit 28593542) (nat_lit 4180403854) (nat_lit 0) D2M8K2.t13203 from rfl, totK_node, tot13202, tot13203]
  decide +kernel

theorem arows13197 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13197 = true := by
  rw [show D2M8K2.u13197 = KTree.node D2M8K2.t13204 (nat_lit 28595188) (nat_lit 3336138822) (nat_lit 0) D2M8K2.t13205 from rfl, allE_node, rows13204, irow13197, rows13205]
  all_goals rfl

theorem atot13197 : totK PD2M8K2 D2M8K2.u13197 = [0, 0, 389300621129, 950274438776, 411474202970, 22555167487, 0, 0] := by
  rw [show D2M8K2.u13197 = KTree.node D2M8K2.t13204 (nat_lit 28595188) (nat_lit 3336138822) (nat_lit 0) D2M8K2.t13205 from rfl, totK_node, tot13204, tot13205]
  decide +kernel

theorem arows13198 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13198 = true := by
  rw [show D2M8K2.u13198 = KTree.node D2M8K2.t13206 (nat_lit 28596889) (nat_lit 1460585262) (nat_lit 0) D2M8K2.t13207 from rfl, allE_node, rows13206, irow13198, rows13207]
  all_goals rfl

theorem atot13198 : totK PD2M8K2 D2M8K2.u13198 = [0, 0, 136256250781, 746202510664, 781941093455, 92608884478, 1310285577, 0] := by
  rw [show D2M8K2.u13198 = KTree.node D2M8K2.t13206 (nat_lit 28596889) (nat_lit 1460585262) (nat_lit 0) D2M8K2.t13207 from rfl, totK_node, tot13206, tot13207]
  decide +kernel

theorem arows13201 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13201 = true := by
  rw [show D2M8K2.u13201 = KTree.node D2M8K2.t13208 (nat_lit 28599365) (nat_lit 1393824402) (nat_lit 0) D2M8K2.t13209 from rfl, allE_node, rows13208, irow13201, rows13209]
  all_goals rfl

theorem atot13201 : totK PD2M8K2 D2M8K2.u13201 = [0, 0, 369424701678, 943418853025, 493774998052, 35380787700, 0, 0] := by
  rw [show D2M8K2.u13201 = KTree.node D2M8K2.t13208 (nat_lit 28599365) (nat_lit 1393824402) (nat_lit 0) D2M8K2.t13209 from rfl, totK_node, tot13208, tot13209]
  decide +kernel

theorem arows13202 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13202 = true := by
  rw [show D2M8K2.u13202 = KTree.node D2M8K2.t13210 (nat_lit 28605837) (nat_lit 1118481385) (nat_lit 0) D2M8K2.t13211 from rfl, allE_node, rows13210, irow13202, rows13211]
  all_goals rfl

theorem atot13202 : totK PD2M8K2 D2M8K2.u13202 = [0, 0, 338310994015, 901074196395, 507755611874, 42171955393, 0, 0] := by
  rw [show D2M8K2.u13202 = KTree.node D2M8K2.t13210 (nat_lit 28605837) (nat_lit 1118481385) (nat_lit 0) D2M8K2.t13211 from rfl, totK_node, tot13210, tot13211]
  decide +kernel

theorem arows13204 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13204 = true := by
  rw [show D2M8K2.u13204 = KTree.node D2M8K2.t13212 (nat_lit 28607414) (nat_lit 3804428773) (nat_lit 0) D2M8K2.t13213 from rfl, allE_node, rows13212, irow13204, rows13213]
  all_goals rfl

theorem atot13204 : totK PD2M8K2 D2M8K2.u13204 = [0, 0, 106828254771, 665357156556, 819634253336, 172119012588, 4931404646, 0] := by
  rw [show D2M8K2.u13204 = KTree.node D2M8K2.t13212 (nat_lit 28607414) (nat_lit 3804428773) (nat_lit 0) D2M8K2.t13213 from rfl, totK_node, tot13212, tot13213]
  decide +kernel

theorem arows13205 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13205 = true := by
  rw [show D2M8K2.u13205 = KTree.node D2M8K2.t13214 (nat_lit 28612845) (nat_lit 939653563) (nat_lit 512) D2M8K2.t13215 from rfl, allE_node, rows13214, irow13205, rows13215]
  all_goals rfl

theorem atot13205 : totK PD2M8K2 D2M8K2.u13205 = [0, 0, 385632554793, 942108920051, 456364593653, 29650110248, 0, 0] := by
  rw [show D2M8K2.u13205 = KTree.node D2M8K2.t13214 (nat_lit 28612845) (nat_lit 939653563) (nat_lit 512) D2M8K2.t13215 from rfl, totK_node, tot13214, tot13215]
  decide +kernel

theorem arows13210 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13210 = true := by
  rw [show D2M8K2.u13210 = KTree.node D2M8K2.t13216 (nat_lit 28865230) (nat_lit 3994782472) (nat_lit 0) D2M8K2.t13217 from rfl, allE_node, rows13216, irow13210, rows13217]
  all_goals rfl

theorem atot13210 : totK PD2M8K2 D2M8K2.u13210 = [0, 353190091134, 838520550080, 469087520101, 141504049258, 13646095762, 0, 0] := by
  rw [show D2M8K2.u13210 = KTree.node D2M8K2.t13216 (nat_lit 28865230) (nat_lit 3994782472) (nat_lit 0) D2M8K2.t13217 from rfl, totK_node, tot13216, tot13217]
  decide +kernel

theorem arows13211 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13211 = true := by
  rw [show D2M8K2.u13211 = KTree.node D2M8K2.t13218 (nat_lit 28866443) (nat_lit 2094083533) (nat_lit 0) D2M8K2.t13219 from rfl, allE_node, rows13218, irow13211, rows13219]
  all_goals rfl

theorem atot13211 : totK PD2M8K2 D2M8K2.u13211 = [0, 82104467767, 675434187284, 883001251504, 148460129729, 1369150432, 0, 0] := by
  rw [show D2M8K2.u13211 = KTree.node D2M8K2.t13218 (nat_lit 28866443) (nat_lit 2094083533) (nat_lit 0) D2M8K2.t13219 from rfl, totK_node, tot13218, tot13219]
  decide +kernel

theorem arows13213 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13213 = true := by
  rw [show D2M8K2.u13213 = KTree.node D2M8K2.t13220 (nat_lit 28872013) (nat_lit 1384185253) (nat_lit 0) D2M8K2.t13221 from rfl, allE_node, rows13220, irow13213, rows13221]
  all_goals rfl

theorem atot13213 : totK PD2M8K2 D2M8K2.u13213 = [0, 364663968034, 916427816582, 484205930151, 40720775671, 0, 0, 0] := by
  rw [show D2M8K2.u13213 = KTree.node D2M8K2.t13220 (nat_lit 28872013) (nat_lit 1384185253) (nat_lit 0) D2M8K2.t13221 from rfl, totK_node, tot13220, tot13221]
  decide +kernel

theorem arows13214 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13214 = true := by
  rw [show D2M8K2.u13214 = KTree.node D2M8K2.t13222 (nat_lit 28873576) (nat_lit 3747453115) (nat_lit 0) D2M8K2.t13223 from rfl, allE_node, rows13222, irow13214, rows13223]
  all_goals rfl

theorem atot13214 : totK PD2M8K2 D2M8K2.u13214 = [0, 45950195159, 512103061834, 903792693361, 275705201352, 13049727234, 0, 0] := by
  rw [show D2M8K2.u13214 = KTree.node D2M8K2.t13222 (nat_lit 28873576) (nat_lit 3747453115) (nat_lit 0) D2M8K2.t13223 from rfl, totK_node, tot13222, tot13223]
  decide +kernel

theorem arows13217 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13217 = true := by
  rw [show D2M8K2.u13217 = KTree.node D2M8K2.t13224 (nat_lit 28875434) (nat_lit 3962473851) (nat_lit 0) D2M8K2.t13225 from rfl, allE_node, rows13224, irow13217, rows13225]
  all_goals rfl

theorem atot13217 : totK PD2M8K2 D2M8K2.u13217 = [0, 337448545814, 900375439421, 517930182553, 49023136518, 0, 0, 0] := by
  rw [show D2M8K2.u13217 = KTree.node D2M8K2.t13224 (nat_lit 28875434) (nat_lit 3962473851) (nat_lit 0) D2M8K2.t13225 from rfl, totK_node, tot13224, tot13225]
  decide +kernel

theorem arows13218 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13218 = true := by
  rw [show D2M8K2.u13218 = KTree.node D2M8K2.t13226 (nat_lit 28876994) (nat_lit 4045396229) (nat_lit 0) D2M8K2.t13227 from rfl, allE_node, rows13226, irow13218, rows13227]
  all_goals rfl

theorem atot13218 : totK PD2M8K2 D2M8K2.u13218 = [0, 73386097616, 525120155147, 878948500117, 269192660622, 10680993762, 0, 0] := by
  rw [show D2M8K2.u13218 = KTree.node D2M8K2.t13226 (nat_lit 28876994) (nat_lit 4045396229) (nat_lit 0) D2M8K2.t13227 from rfl, totK_node, tot13226, tot13227]
  decide +kernel

theorem arows13220 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13220 = true := by
  rw [show D2M8K2.u13220 = KTree.node D2M8K2.t13228 (nat_lit 28878819) (nat_lit 3652105363) (nat_lit 0) D2M8K2.t13229 from rfl, allE_node, rows13228, irow13220, rows13229]
  all_goals rfl

theorem atot13220 : totK PD2M8K2 D2M8K2.u13220 = [0, 332484946232, 890557802739, 515666752272, 62733964147, 2569691499, 0, 0] := by
  rw [show D2M8K2.u13220 = KTree.node D2M8K2.t13228 (nat_lit 28878819) (nat_lit 3652105363) (nat_lit 0) D2M8K2.t13229 from rfl, totK_node, tot13228, tot13229]
  decide +kernel

theorem arows13221 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13221 = true := by
  rw [show D2M8K2.u13221 = KTree.node D2M8K2.t13230 (nat_lit 28880382) (nat_lit 3853653136) (nat_lit 0) D2M8K2.t13231 from rfl, allE_node, rows13230, irow13221, rows13231]
  all_goals rfl

theorem atot13221 : totK PD2M8K2 D2M8K2.u13221 = [0, 91637619653, 686782783007, 883126462801, 143111457825, 1096505104, 0, 0] := by
  rw [show D2M8K2.u13221 = KTree.node D2M8K2.t13230 (nat_lit 28880382) (nat_lit 3853653136) (nat_lit 0) D2M8K2.t13231 from rfl, totK_node, tot13230, tot13231]
  decide +kernel

theorem arows13225 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13225 = true := by
  rw [show D2M8K2.u13225 = KTree.node D2M8K2.t13232 (nat_lit 28882608) (nat_lit 3289899456) (nat_lit 0) D2M8K2.t13233 from rfl, allE_node, rows13232, irow13225, rows13233]
  all_goals rfl

theorem atot13225 : totK PD2M8K2 D2M8K2.u13225 = [0, 323074992700, 862092640116, 497776391095, 91212826588, 3884009855, 0, 0] := by
  rw [show D2M8K2.u13225 = KTree.node D2M8K2.t13232 (nat_lit 28882608) (nat_lit 3289899456) (nat_lit 0) D2M8K2.t13233 from rfl, totK_node, tot13232, tot13233]
  decide +kernel

theorem arows13226 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13226 = true := by
  rw [show D2M8K2.u13226 = KTree.node D2M8K2.t13234 (nat_lit 28884532) (nat_lit 2458029001) (nat_lit 0) D2M8K2.t13235 from rfl, allE_node, rows13234, irow13226, rows13235]
  all_goals rfl

theorem atot13226 : totK PD2M8K2 D2M8K2.u13226 = [0, 0, 437454547244, 989653683741, 326739623868, 10080560483, 0, 0] := by
  rw [show D2M8K2.u13226 = KTree.node D2M8K2.t13234 (nat_lit 28884532) (nat_lit 2458029001) (nat_lit 0) D2M8K2.t13235 from rfl, totK_node, tot13234, tot13235]
  decide +kernel

theorem arows13228 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13228 = true := by
  rw [show D2M8K2.u13228 = KTree.node D2M8K2.t13236 (nat_lit 28886497) (nat_lit 1499270450) (nat_lit 0) D2M8K2.t13237 from rfl, allE_node, rows13236, irow13228, rows13237]
  all_goals rfl

theorem atot13228 : totK PD2M8K2 D2M8K2.u13228 = [0, 0, 276888785435, 862331509446, 534471173133, 52493199613, 0, 0] := by
  rw [show D2M8K2.u13228 = KTree.node D2M8K2.t13236 (nat_lit 28886497) (nat_lit 1499270450) (nat_lit 0) D2M8K2.t13237 from rfl, totK_node, tot13236, tot13237]
  decide +kernel

theorem arows13229 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13229 = true := by
  rw [show D2M8K2.u13229 = KTree.node D2M8K2.t13238 (nat_lit 28888500) (nat_lit 3187246348) (nat_lit 0) D2M8K2.t13239 from rfl, allE_node, rows13238, irow13229, rows13239]
  all_goals rfl

theorem atot13229 : totK PD2M8K2 D2M8K2.u13229 = [0, 0, 206785858850, 791929348411, 644992433062, 90786030079, 1369150432, 0] := by
  rw [show D2M8K2.u13229 = KTree.node D2M8K2.t13238 (nat_lit 28888500) (nat_lit 3187246348) (nat_lit 0) D2M8K2.t13239 from rfl, totK_node, tot13238, tot13239]
  decide +kernel

theorem arows13232 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13232 = true := by
  rw [show D2M8K2.u13232 = KTree.node D2M8K2.t13240 (nat_lit 28893690) (nat_lit 3636103017) (nat_lit 0) D2M8K2.t13241 from rfl, allE_node, rows13240, irow13232, rows13241]
  all_goals rfl

theorem atot13232 : totK PD2M8K2 D2M8K2.u13232 = [0, 0, 354635445353, 956125594191, 428581500109, 20324149973, 0, 0] := by
  rw [show D2M8K2.u13232 = KTree.node D2M8K2.t13240 (nat_lit 28893690) (nat_lit 3636103017) (nat_lit 0) D2M8K2.t13241 from rfl, totK_node, tot13240, tot13241]
  decide +kernel

theorem arows13233 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13233 = true := by
  rw [show D2M8K2.u13233 = KTree.node D2M8K2.t13242 (nat_lit 28897024) (nat_lit 2219176798) (nat_lit 0) D2M8K2.t13243 from rfl, allE_node, rows13242, irow13233, rows13243]
  all_goals rfl

theorem atot13233 : totK PD2M8K2 D2M8K2.u13233 = [0, 0, 384766701392, 945621231417, 417007981032, 18822163931, 0, 0] := by
  rw [show D2M8K2.u13233 = KTree.node D2M8K2.t13242 (nat_lit 28897024) (nat_lit 2219176798) (nat_lit 0) D2M8K2.t13243 from rfl, totK_node, tot13242, tot13243]
  decide +kernel

theorem arows13235 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13235 = true := by
  rw [show D2M8K2.u13235 = KTree.node D2M8K2.t13244 (nat_lit 28900085) (nat_lit 1150927029) (nat_lit 0) D2M8K2.t13245 from rfl, allE_node, rows13244, irow13235, rows13245]
  all_goals rfl

theorem atot13235 : totK PD2M8K2 D2M8K2.u13235 = [0, 0, 375114029826, 944389434148, 428031259361, 23530719713, 0, 0] := by
  rw [show D2M8K2.u13235 = KTree.node D2M8K2.t13244 (nat_lit 28900085) (nat_lit 1150927029) (nat_lit 0) D2M8K2.t13245 from rfl, totK_node, tot13244, tot13245]
  decide +kernel

theorem arows13236 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13236 = true := by
  rw [show D2M8K2.u13236 = KTree.node D2M8K2.t13246 (nat_lit 28903973) (nat_lit 2300621315) (nat_lit 0) D2M8K2.t13247 from rfl, allE_node, rows13246, irow13236, rows13247]
  all_goals rfl

theorem atot13236 : totK PD2M8K2 D2M8K2.u13236 = [0, 127234728902, 523797877944, 838814013105, 302129011512, 9106999908, 0, 0] := by
  rw [show D2M8K2.u13236 = KTree.node D2M8K2.t13246 (nat_lit 28903973) (nat_lit 2300621315) (nat_lit 0) D2M8K2.t13247 from rfl, totK_node, tot13246, tot13247]
  decide +kernel

theorem arows13242 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13242 = true := by
  rw [show D2M8K2.u13242 = KTree.node D2M8K2.t13248 (nat_lit 28910650) (nat_lit 3199277619) (nat_lit 0) D2M8K2.t13249 from rfl, allE_node, rows13248, irow13242, rows13249]
  all_goals rfl

theorem atot13242 : totK PD2M8K2 D2M8K2.u13242 = [0, 316637552494, 912056758953, 553046716374, 51074524704, 0, 0, 0] := by
  rw [show D2M8K2.u13242 = KTree.node D2M8K2.t13248 (nat_lit 28910650) (nat_lit 3199277619) (nat_lit 0) D2M8K2.t13249 from rfl, totK_node, tot13248, tot13249]
  decide +kernel

theorem arows13243 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13243 = true := by
  rw [show D2M8K2.u13243 = KTree.node D2M8K2.t13250 (nat_lit 28912131) (nat_lit 3655480701) (nat_lit 0) D2M8K2.t13251 from rfl, allE_node, rows13250, irow13243, rows13251]
  all_goals rfl

theorem atot13243 : totK PD2M8K2 D2M8K2.u13243 = [0, 0, 374546806708, 956314726764, 456291821621, 30804453458, 0, 0] := by
  rw [show D2M8K2.u13243 = KTree.node D2M8K2.t13250 (nat_lit 28912131) (nat_lit 3655480701) (nat_lit 0) D2M8K2.t13251 from rfl, totK_node, tot13250, tot13251]
  decide +kernel

theorem arows13245 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13245 = true := by
  rw [show D2M8K2.u13245 = KTree.node D2M8K2.t13252 (nat_lit 28913445) (nat_lit 1403121625) (nat_lit 0) D2M8K2.t13253 from rfl, allE_node, rows13252, irow13245, rows13253]
  all_goals rfl

theorem atot13245 : totK PD2M8K2 D2M8K2.u13245 = [0, 334866126348, 856752147935, 500212269292, 113760447889, 6804944647, 0, 0] := by
  rw [show D2M8K2.u13245 = KTree.node D2M8K2.t13252 (nat_lit 28913445) (nat_lit 1403121625) (nat_lit 0) D2M8K2.t13253 from rfl, totK_node, tot13252, tot13253]
  decide +kernel

theorem arows13246 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13246 = true := by
  rw [show D2M8K2.u13246 = KTree.node D2M8K2.t13254 (nat_lit 28915016) (nat_lit 3884335182) (nat_lit 0) D2M8K2.t13255 from rfl, allE_node, rows13254, irow13246, rows13255]
  all_goals rfl

theorem atot13246 : totK PD2M8K2 D2M8K2.u13246 = [0, 78908693579, 536425081257, 880213215969, 265360643266, 11533271830, 0, 0] := by
  rw [show D2M8K2.u13246 = KTree.node D2M8K2.t13254 (nat_lit 28915016) (nat_lit 3884335182) (nat_lit 0) D2M8K2.t13255 from rfl, totK_node, tot13254, tot13255]
  decide +kernel

theorem arows13249 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13249 = true := by
  rw [show D2M8K2.u13249 = KTree.node D2M8K2.t13256 (nat_lit 28916866) (nat_lit 3923195380) (nat_lit 0) D2M8K2.t13257 from rfl, allE_node, rows13256, irow13249, rows13257]
  all_goals rfl

theorem atot13249 : totK PD2M8K2 D2M8K2.u13249 = [0, 335038862052, 896206375800, 538171210126, 58688912717, 1503593968, 0, 0] := by
  rw [show D2M8K2.u13249 = KTree.node D2M8K2.t13256 (nat_lit 28916866) (nat_lit 3923195380) (nat_lit 0) D2M8K2.t13257 from rfl, totK_node, tot13256, tot13257]
  decide +kernel

theorem arows13250 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13250 = true := by
  rw [show D2M8K2.u13250 = KTree.node D2M8K2.t13258 (nat_lit 28918441) (nat_lit 1242098777) (nat_lit 0) D2M8K2.t13259 from rfl, allE_node, rows13258, irow13250, rows13259]
  all_goals rfl

theorem atot13250 : totK PD2M8K2 D2M8K2.u13250 = [0, 78976767030, 578061325292, 866840700404, 245034348383, 10671004620, 0, 0] := by
  rw [show D2M8K2.u13250 = KTree.node D2M8K2.t13258 (nat_lit 28918441) (nat_lit 1242098777) (nat_lit 0) D2M8K2.t13259 from rfl, totK_node, tot13258, tot13259]
  decide +kernel

theorem arows13252 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13252 = true := by
  rw [show D2M8K2.u13252 = KTree.node D2M8K2.t13260 (nat_lit 28920274) (nat_lit 3880455095) (nat_lit 0) D2M8K2.t13261 from rfl, allE_node, rows13260, irow13252, rows13261]
  all_goals rfl

theorem atot13252 : totK PD2M8K2 D2M8K2.u13252 = [0, 333541808461, 855877101986, 542106071884, 90689039361, 2566665356, 0, 0] := by
  rw [show D2M8K2.u13252 = KTree.node D2M8K2.t13260 (nat_lit 28920274) (nat_lit 3880455095) (nat_lit 0) D2M8K2.t13261 from rfl, totK_node, tot13260, tot13261]
  decide +kernel

theorem arows13253 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13253 = true := by
  rw [show D2M8K2.u13253 = KTree.node D2M8K2.t13262 (nat_lit 28921778) (nat_lit 3083928954) (nat_lit 0) D2M8K2.t13263 from rfl, allE_node, rows13262, irow13253, rows13263]
  all_goals rfl

theorem atot13253 : totK PD2M8K2 D2M8K2.u13253 = [0, 91681601894, 714819775874, 870605593771, 137891728540, 1096156699, 0, 0] := by
  rw [show D2M8K2.u13253 = KTree.node D2M8K2.t13262 (nat_lit 28921778) (nat_lit 3083928954) (nat_lit 0) D2M8K2.t13263 from rfl, totK_node, tot13262, tot13263]
  decide +kernel

theorem arows13257 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13257 = true := by
  rw [show D2M8K2.u13257 = KTree.node D2M8K2.t13264 (nat_lit 28923956) (nat_lit 3532841343) (nat_lit 0) D2M8K2.t13265 from rfl, allE_node, rows13264, irow13257, rows13265]
  all_goals rfl

theorem atot13257 : totK PD2M8K2 D2M8K2.u13257 = [0, 330028431640, 834513641317, 550412696629, 112458099354, 3880716147, 0, 0] := by
  rw [show D2M8K2.u13257 = KTree.node D2M8K2.t13264 (nat_lit 28923956) (nat_lit 3532841343) (nat_lit 0) D2M8K2.t13265 from rfl, totK_node, tot13264, tot13265]
  decide +kernel

theorem arows13258 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13258 = true := by
  rw [show D2M8K2.u13258 = KTree.node D2M8K2.t13266 (nat_lit 28925965) (nat_lit 895266694) (nat_lit 0) D2M8K2.t13267 from rfl, allE_node, rows13266, irow13258, rows13267]
  all_goals rfl

theorem atot13258 : totK PD2M8K2 D2M8K2.u13258 = [0, 0, 459277640431, 973494341777, 346970068693, 23411282746, 0, 0] := by
  rw [show D2M8K2.u13258 = KTree.node D2M8K2.t13266 (nat_lit 28925965) (nat_lit 895266694) (nat_lit 0) D2M8K2.t13267 from rfl, totK_node, tot13266, tot13267]
  decide +kernel

theorem arows13260 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13260 = true := by
  rw [show D2M8K2.u13260 = KTree.node D2M8K2.t13268 (nat_lit 28931215) (nat_lit 2344989850) (nat_lit 0) D2M8K2.t13269 from rfl, allE_node, rows13268, irow13260, rows13269]
  all_goals rfl

theorem atot13260 : totK PD2M8K2 D2M8K2.u13260 = [0, 0, 348660325359, 934187253481, 522096498307, 29170288776, 0, 0] := by
  rw [show D2M8K2.u13260 = KTree.node D2M8K2.t13268 (nat_lit 28931215) (nat_lit 2344989850) (nat_lit 0) D2M8K2.t13269 from rfl, totK_node, tot13268, tot13269]
  decide +kernel

theorem arows13261 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13261 = true := by
  rw [show D2M8K2.u13261 = KTree.node D2M8K2.t13270 (nat_lit 28932728) (nat_lit 3834684160) (nat_lit 0) D2M8K2.t13271 from rfl, allE_node, rows13270, irow13261, rows13271]
  all_goals rfl

theorem atot13261 : totK PD2M8K2 D2M8K2.u13261 = [0, 0, 0, 409945761039, 950668320305, 397409164335, 23727080593, 0] := by
  rw [show D2M8K2.u13261 = KTree.node D2M8K2.t13270 (nat_lit 28932728) (nat_lit 3834684160) (nat_lit 0) D2M8K2.t13271 from rfl, totK_node, tot13270, tot13271]
  decide +kernel

theorem arows13264 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13264 = true := by
  rw [show D2M8K2.u13264 = KTree.node D2M8K2.t13272 (nat_lit 28934209) (nat_lit 1538186773) (nat_lit 0) D2M8K2.t13273 from rfl, allE_node, rows13272, irow13264, rows13273]
  all_goals rfl

theorem atot13264 : totK PD2M8K2 D2M8K2.u13264 = [0, 0, 350657305184, 916705103570, 497768576560, 40263912048, 0, 0] := by
  rw [show D2M8K2.u13264 = KTree.node D2M8K2.t13272 (nat_lit 28934209) (nat_lit 1538186773) (nat_lit 0) D2M8K2.t13273 from rfl, totK_node, tot13272, tot13273]
  decide +kernel

theorem arows13265 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13265 = true := by
  rw [show D2M8K2.u13265 = KTree.node D2M8K2.t13274 (nat_lit 28936040) (nat_lit 3889969880) (nat_lit 0) D2M8K2.t13275 from rfl, allE_node, rows13274, irow13265, rows13275]
  all_goals rfl

theorem atot13265 : totK PD2M8K2 D2M8K2.u13265 = [0, 0, 110948910568, 656661754839, 826158172743, 178939295426, 5159868635, 0] := by
  rw [show D2M8K2.u13265 = KTree.node D2M8K2.t13274 (nat_lit 28936040) (nat_lit 3889969880) (nat_lit 0) D2M8K2.t13275 from rfl, totK_node, tot13274, tot13275]
  decide +kernel

theorem arows13267 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13267 = true := by
  rw [show D2M8K2.u13267 = KTree.node D2M8K2.t13276 (nat_lit 28938094) (nat_lit 4007529865) (nat_lit 0) D2M8K2.t13277 from rfl, allE_node, rows13276, irow13267, rows13277]
  all_goals rfl

theorem atot13267 : totK PD2M8K2 D2M8K2.u13267 = [0, 0, 360330983678, 933046595037, 484609509631, 36465629387, 0, 0] := by
  rw [show D2M8K2.u13267 = KTree.node D2M8K2.t13276 (nat_lit 28938094) (nat_lit 4007529865) (nat_lit 0) D2M8K2.t13277 from rfl, totK_node, tot13276, tot13277]
  decide +kernel

theorem arows13268 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13268 = true := by
  rw [show D2M8K2.u13268 = KTree.node D2M8K2.t13278 (nat_lit 28939977) (nat_lit 1843520491) (nat_lit 0) D2M8K2.t13279 from rfl, allE_node, rows13278, irow13268, rows13279]
  all_goals rfl

theorem atot13268 : totK PD2M8K2 D2M8K2.u13268 = [0, 0, 96653581007, 659257490647, 824566777192, 182509101751, 5218872685, 0] := by
  rw [show D2M8K2.u13268 = KTree.node D2M8K2.t13278 (nat_lit 28939977) (nat_lit 1843520491) (nat_lit 0) D2M8K2.t13279 from rfl, totK_node, tot13278, tot13279]
  decide +kernel

theorem arows13273 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13273 = true := by
  rw [show D2M8K2.u13273 = KTree.node D2M8K2.t13280 (nat_lit 28941436) (nat_lit 3271814126) (nat_lit 0) D2M8K2.t13281 from rfl, allE_node, rows13280, irow13273, rows13281]
  all_goals rfl

theorem atot13273 : totK PD2M8K2 D2M8K2.u13273 = [0, 0, 323122864575, 901453243929, 537241864796, 44749648491, 0, 0] := by
  rw [show D2M8K2.u13273 = KTree.node D2M8K2.t13280 (nat_lit 28941436) (nat_lit 3271814126) (nat_lit 0) D2M8K2.t13281 from rfl, totK_node, tot13280, tot13281]
  decide +kernel

theorem arows13274 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13274 = true := by
  rw [show D2M8K2.u13274 = KTree.node D2M8K2.t13282 (nat_lit 28943480) (nat_lit 3820835085) (nat_lit 0) D2M8K2.t13283 from rfl, allE_node, rows13282, irow13274, rows13283]
  all_goals rfl

theorem atot13274 : totK PD2M8K2 D2M8K2.u13274 = [0, 0, 140780795527, 687073543006, 853336088254, 154179518830, 1415142070, 0] := by
  rw [show D2M8K2.u13274 = KTree.node D2M8K2.t13282 (nat_lit 28943480) (nat_lit 3820835085) (nat_lit 0) D2M8K2.t13283 from rfl, totK_node, tot13282, tot13283]
  decide +kernel

theorem arows13276 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13276 = true := by
  rw [show D2M8K2.u13276 = KTree.node D2M8K2.t13284 (nat_lit 28945649) (nat_lit 1354941675) (nat_lit 2) D2M8K2.t13285 from rfl, allE_node, rows13284, irow13276, rows13285]
  all_goals rfl

theorem atot13276 : totK PD2M8K2 D2M8K2.u13276 = [0, 178256666961, 623783277644, 719635769591, 282538179082, 15457145080, 0, 0] := by
  rw [show D2M8K2.u13276 = KTree.node D2M8K2.t13284 (nat_lit 28945649) (nat_lit 1354941675) (nat_lit 2) D2M8K2.t13285 from rfl, totK_node, tot13284, tot13285]
  decide +kernel

theorem arows13277 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13277 = true := by
  rw [show D2M8K2.u13277 = KTree.node D2M8K2.t13286 (nat_lit 28948953) (nat_lit 1572812420) (nat_lit 0) D2M8K2.t13287 from rfl, allE_node, rows13286, irow13277, rows13287]
  all_goals rfl

theorem atot13277 : totK PD2M8K2 D2M8K2.u13277 = [0, 228335789119, 758389998503, 654790109254, 111444596767, 1369150432, 0, 0] := by
  rw [show D2M8K2.u13277 = KTree.node D2M8K2.t13286 (nat_lit 28948953) (nat_lit 1572812420) (nat_lit 0) D2M8K2.t13287 from rfl, totK_node, tot13286, tot13287]
  decide +kernel

theorem arows13280 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13280 = true := by
  rw [show D2M8K2.u13280 = KTree.node D2M8K2.t13288 (nat_lit 28951331) (nat_lit 2962688467) (nat_lit 0) D2M8K2.t13289 from rfl, allE_node, rows13288, irow13280, rows13289]
  all_goals rfl

theorem atot13280 : totK PD2M8K2 D2M8K2.u13280 = [0, 251579248539, 817331391915, 683362102595, 77534649867, 0, 0, 0] := by
  rw [show D2M8K2.u13280 = KTree.node D2M8K2.t13288 (nat_lit 28951331) (nat_lit 2962688467) (nat_lit 0) D2M8K2.t13289 from rfl, totK_node, tot13288, tot13289]
  decide +kernel

theorem arows13281 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13281 = true := by
  rw [show D2M8K2.u13281 = KTree.node D2M8K2.t13290 (nat_lit 28952574) (nat_lit 3890710336) (nat_lit 0) D2M8K2.t13291 from rfl, allE_node, rows13290, irow13281, rows13291]
  all_goals rfl

theorem atot13281 : totK PD2M8K2 D2M8K2.u13281 = [0, 166329116705, 676959501609, 717478519560, 234157327746, 21155208970, 0, 0] := by
  rw [show D2M8K2.u13281 = KTree.node D2M8K2.t13290 (nat_lit 28952574) (nat_lit 3890710336) (nat_lit 0) D2M8K2.t13291 from rfl, totK_node, tot13290, tot13291]
  decide +kernel

theorem arows13283 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13283 = true := by
  rw [show D2M8K2.u13283 = KTree.node D2M8K2.t13292 (nat_lit 28954123) (nat_lit 1713671193) (nat_lit 0) D2M8K2.t13293 from rfl, allE_node, rows13292, irow13283, rows13293]
  all_goals rfl

theorem atot13283 : totK PD2M8K2 D2M8K2.u13283 = [0, 157065200967, 560080694940, 738496757929, 331094634719, 14826367994, 0, 0] := by
  rw [show D2M8K2.u13283 = KTree.node D2M8K2.t13292 (nat_lit 28954123) (nat_lit 1713671193) (nat_lit 0) D2M8K2.t13293 from rfl, totK_node, tot13292, tot13293]
  decide +kernel

theorem arows13284 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13284 = true := by
  rw [show D2M8K2.u13284 = KTree.node D2M8K2.t13294 (nat_lit 28955590) (nat_lit 3180246885) (nat_lit 0) D2M8K2.t13295 from rfl, allE_node, rows13294, irow13284, rows13295]
  all_goals rfl

theorem atot13284 : totK PD2M8K2 D2M8K2.u13284 = [0, 282671396960, 876786182214, 602796121914, 55761328166, 0, 0, 0] := by
  rw [show D2M8K2.u13284 = KTree.node D2M8K2.t13294 (nat_lit 28955590) (nat_lit 3180246885) (nat_lit 0) D2M8K2.t13295 from rfl, totK_node, tot13294, tot13295]
  decide +kernel

theorem arows13288 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13288 = true := by
  rw [show D2M8K2.u13288 = KTree.node D2M8K2.t13296 (nat_lit 28957277) (nat_lit 2299445701) (nat_lit 0) D2M8K2.t13297 from rfl, allE_node, rows13296, irow13288, rows13297]
  all_goals rfl

theorem atot13288 : totK PD2M8K2 D2M8K2.u13288 = [0, 84547450418, 530135244852, 873033614427, 282023621938, 13049727234, 0, 0] := by
  rw [show D2M8K2.u13288 = KTree.node D2M8K2.t13296 (nat_lit 28957277) (nat_lit 2299445701) (nat_lit 0) D2M8K2.t13297 from rfl, totK_node, tot13296, tot13297]
  decide +kernel

theorem arows13289 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13289 = true := by
  rw [show D2M8K2.u13289 = KTree.node D2M8K2.t13298 (nat_lit 28962068) (nat_lit 3167532524) (nat_lit 0) D2M8K2.t13299 from rfl, allE_node, rows13298, irow13289, rows13299]
  all_goals rfl

theorem atot13289 : totK PD2M8K2 D2M8K2.u13289 = [0, 340284428165, 923871649255, 515318206028, 42768463036, 0, 0, 0] := by
  rw [show D2M8K2.u13289 = KTree.node D2M8K2.t13298 (nat_lit 28962068) (nat_lit 3167532524) (nat_lit 0) D2M8K2.t13299 from rfl, totK_node, tot13298, tot13299]
  decide +kernel

theorem arows13291 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13291 = true := by
  rw [show D2M8K2.u13291 = KTree.node D2M8K2.t13300 (nat_lit 28963944) (nat_lit 3473861239) (nat_lit 0) D2M8K2.t13301 from rfl, allE_node, rows13300, irow13291, rows13301]
  all_goals rfl

theorem atot13291 : totK PD2M8K2 D2M8K2.u13291 = [0, 91794050722, 609139928664, 877232111018, 203321003950, 4980514959, 0, 0] := by
  rw [show D2M8K2.u13291 = KTree.node D2M8K2.t13300 (nat_lit 28963944) (nat_lit 3473861239) (nat_lit 0) D2M8K2.t13301 from rfl, totK_node, tot13300, tot13301]
  decide +kernel

theorem arows13292 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13292 = true := by
  rw [show D2M8K2.u13292 = KTree.node D2M8K2.t13302 (nat_lit 28966207) (nat_lit 1738112736) (nat_lit 0) D2M8K2.t13303 from rfl, allE_node, rows13302, irow13292, rows13303]
  all_goals rfl

theorem atot13292 : totK PD2M8K2 D2M8K2.u13292 = [0, 234333710046, 793809920207, 669199990291, 109537709954, 1268739303, 0, 0] := by
  rw [show D2M8K2.u13292 = KTree.node D2M8K2.t13302 (nat_lit 28966207) (nat_lit 1738112736) (nat_lit 0) D2M8K2.t13303 from rfl, totK_node, tot13302, tot13303]
  decide +kernel

theorem arows13295 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13295 = true := by
  rw [show D2M8K2.u13295 = KTree.node D2M8K2.t13304 (nat_lit 28968290) (nat_lit 2909803444) (nat_lit 0) D2M8K2.t13305 from rfl, allE_node, rows13304, irow13295, rows13305]
  all_goals rfl

theorem atot13295 : totK PD2M8K2 D2M8K2.u13295 = [0, 0, 396179692520, 963990290304, 389634065203, 17269540800, 0, 0] := by
  rw [show D2M8K2.u13295 = KTree.node D2M8K2.t13304 (nat_lit 28968290) (nat_lit 2909803444) (nat_lit 0) D2M8K2.t13305 from rfl, totK_node, tot13304, tot13305]
  decide +kernel

theorem arows13296 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13296 = true := by
  rw [show D2M8K2.u13296 = KTree.node D2M8K2.t13306 (nat_lit 28969929) (nat_lit 1819679931) (nat_lit 0) D2M8K2.t13307 from rfl, allE_node, rows13306, irow13296, rows13307]
  all_goals rfl

theorem atot13296 : totK PD2M8K2 D2M8K2.u13296 = [0, 0, 160975441361, 753557741998, 687552808600, 84483453808, 1206465782, 0] := by
  rw [show D2M8K2.u13296 = KTree.node D2M8K2.t13306 (nat_lit 28969929) (nat_lit 1819679931) (nat_lit 0) D2M8K2.t13307 from rfl, totK_node, tot13306, tot13307]
  decide +kernel

theorem arows13298 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13298 = true := by
  rw [show D2M8K2.u13298 = KTree.node D2M8K2.t13308 (nat_lit 28972346) (nat_lit 4057184514) (nat_lit 0) D2M8K2.t13309 from rfl, allE_node, rows13308, irow13298, rows13309]
  all_goals rfl

theorem atot13298 : totK PD2M8K2 D2M8K2.u13298 = [0, 0, 337114761905, 929722210266, 517028418009, 40010315139, 0, 0] := by
  rw [show D2M8K2.u13298 = KTree.node D2M8K2.t13308 (nat_lit 28972346) (nat_lit 4057184514) (nat_lit 0) D2M8K2.t13309 from rfl, totK_node, tot13308, tot13309]
  decide +kernel

theorem arows13299 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13299 = true := by
  rw [show D2M8K2.u13299 = KTree.node D2M8K2.t13310 (nat_lit 28975450) (nat_lit 3932136345) (nat_lit 0) D2M8K2.t13311 from rfl, allE_node, rows13310, irow13299, rows13311]
  all_goals rfl

theorem atot13299 : totK PD2M8K2 D2M8K2.u13299 = [0, 0, 378980247434, 938985626219, 462193443194, 29012051731, 0, 0] := by
  rw [show D2M8K2.u13299 = KTree.node D2M8K2.t13310 (nat_lit 28975450) (nat_lit 3932136345) (nat_lit 0) D2M8K2.t13311 from rfl, totK_node, tot13310, tot13311]
  decide +kernel

theorem arows13309 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13309 = true := by
  rw [show D2M8K2.u13309 = KTree.node D2M8K2.t13312 (nat_lit 28976941) (nat_lit 1095264759) (nat_lit 0) D2M8K2.t13313 from rfl, allE_node, rows13312, irow13309, rows13313]
  all_goals rfl

theorem atot13309 : totK PD2M8K2 D2M8K2.u13309 = [0, 0, 134420827091, 679919250994, 744466876936, 176157444676, 9579374723, 0] := by
  rw [show D2M8K2.u13309 = KTree.node D2M8K2.t13312 (nat_lit 28976941) (nat_lit 1095264759) (nat_lit 0) D2M8K2.t13313 from rfl, totK_node, tot13312, tot13313]
  decide +kernel

theorem arows13310 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13310 = true := by
  rw [show D2M8K2.u13310 = KTree.node D2M8K2.t13314 (nat_lit 28982290) (nat_lit 3545407379) (nat_lit 0) D2M8K2.t13315 from rfl, allE_node, rows13314, irow13310, rows13315]
  all_goals rfl

theorem atot13310 : totK PD2M8K2 D2M8K2.u13310 = [0, 0, 273615597074, 809789876889, 572347530129, 99198214827, 3436822651, 0] := by
  rw [show D2M8K2.u13310 = KTree.node D2M8K2.t13314 (nat_lit 28982290) (nat_lit 3545407379) (nat_lit 0) D2M8K2.t13315 from rfl, totK_node, tot13314, tot13315]
  decide +kernel

theorem arows13312 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13312 = true := by
  rw [show D2M8K2.u13312 = KTree.node D2M8K2.t13316 (nat_lit 28983846) (nat_lit 3402345536) (nat_lit 0) D2M8K2.t13317 from rfl, allE_node, rows13316, irow13312, rows13317]
  all_goals rfl

theorem atot13312 : totK PD2M8K2 D2M8K2.u13312 = [0, 0, 146334516602, 772636920037, 724341684359, 95247877117, 1021600638, 0] := by
  rw [show D2M8K2.u13312 = KTree.node D2M8K2.t13316 (nat_lit 28983846) (nat_lit 3402345536) (nat_lit 0) D2M8K2.t13317 from rfl, totK_node, tot13316, tot13317]
  decide +kernel

theorem arows13313 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13313 = true := by
  rw [show D2M8K2.u13313 = KTree.node D2M8K2.t13318 (nat_lit 28985945) (nat_lit 1697010133) (nat_lit 0) D2M8K2.t13319 from rfl, allE_node, rows13318, irow13313, rows13319]
  all_goals rfl

theorem atot13313 : totK PD2M8K2 D2M8K2.u13313 = [0, 0, 324767521898, 850926023149, 509558912868, 80479910868, 3552795014, 0] := by
  rw [show D2M8K2.u13313 = KTree.node D2M8K2.t13318 (nat_lit 28985945) (nat_lit 1697010133) (nat_lit 0) D2M8K2.t13319 from rfl, totK_node, tot13318, tot13319]
  decide +kernel

theorem arows13316 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13316 = true := by
  rw [show D2M8K2.u13316 = KTree.node D2M8K2.t13320 (nat_lit 28989884) (nat_lit 3369582561) (nat_lit 0) D2M8K2.t13321 from rfl, allE_node, rows13320, irow13316, rows13321]
  all_goals rfl

theorem atot13316 : totK PD2M8K2 D2M8K2.u13316 = [0, 398566149415, 935335379783, 417069127100, 29106945324, 0, 0, 0] := by
  rw [show D2M8K2.u13316 = KTree.node D2M8K2.t13320 (nat_lit 28989884) (nat_lit 3369582561) (nat_lit 0) D2M8K2.t13321 from rfl, totK_node, tot13320, tot13321]
  decide +kernel

theorem arows13317 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13317 = true := by
  rw [show D2M8K2.u13317 = KTree.node D2M8K2.t13322 (nat_lit 28991595) (nat_lit 3431252789) (nat_lit 0) D2M8K2.t13323 from rfl, allE_node, rows13322, irow13317, rows13323]
  all_goals rfl

theorem atot13317 : totK PD2M8K2 D2M8K2.u13317 = [0, 97156704769, 669683192091, 866586087076, 154933723227, 1369150432, 0, 0] := by
  rw [show D2M8K2.u13317 = KTree.node D2M8K2.t13322 (nat_lit 28991595) (nat_lit 3431252789) (nat_lit 0) D2M8K2.t13323 from rfl, totK_node, tot13322, tot13323]
  decide +kernel

theorem arows13319 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13319 = true := by
  rw [show D2M8K2.u13319 = KTree.node D2M8K2.t13324 (nat_lit 28993492) (nat_lit 2671075544) (nat_lit 0) D2M8K2.t13325 from rfl, allE_node, rows13324, irow13319, rows13325]
  all_goals rfl

theorem atot13319 : totK PD2M8K2 D2M8K2.u13319 = [0, 325018865045, 910383060752, 547114639409, 42617514119, 0, 0, 0] := by
  rw [show D2M8K2.u13319 = KTree.node D2M8K2.t13324 (nat_lit 28993492) (nat_lit 2671075544) (nat_lit 0) D2M8K2.t13325 from rfl, totK_node, tot13324, tot13325]
  decide +kernel

theorem arows13320 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13320 = true := by
  rw [show D2M8K2.u13320 = KTree.node D2M8K2.t13326 (nat_lit 28995011) (nat_lit 2816468692) (nat_lit 0) D2M8K2.t13327 from rfl, allE_node, rows13326, irow13320, rows13327]
  all_goals rfl

theorem atot13320 : totK PD2M8K2 D2M8K2.u13320 = [0, 0, 390749176288, 940230462576, 451886586451, 30553880795, 0, 0] := by
  rw [show D2M8K2.u13320 = KTree.node D2M8K2.t13326 (nat_lit 28995011) (nat_lit 2816468692) (nat_lit 0) D2M8K2.t13327 from rfl, totK_node, tot13326, tot13327]
  decide +kernel

theorem arows13324 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13324 = true := by
  rw [show D2M8K2.u13324 = KTree.node D2M8K2.t13328 (nat_lit 28999767) (nat_lit 3625627632) (nat_lit 0) D2M8K2.t13329 from rfl, allE_node, rows13328, irow13324, rows13329]
  all_goals rfl

theorem atot13324 : totK PD2M8K2 D2M8K2.u13324 = [0, 356385932744, 843516527977, 506938952431, 121297813776, 5415877171, 0, 0] := by
  rw [show D2M8K2.u13324 = KTree.node D2M8K2.t13328 (nat_lit 28999767) (nat_lit 3625627632) (nat_lit 0) D2M8K2.t13329 from rfl, totK_node, tot13328, tot13329]
  decide +kernel

theorem arows13325 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13325 = true := by
  rw [show D2M8K2.u13325 = KTree.node D2M8K2.t13330 (nat_lit 29001240) (nat_lit 3488536760) (nat_lit 0) D2M8K2.t13331 from rfl, allE_node, rows13330, irow13325, rows13331]
  all_goals rfl

theorem atot13325 : totK PD2M8K2 D2M8K2.u13325 = [0, 83518256830, 612180621579, 860312645520, 224350939838, 9668735432, 0, 0] := by
  rw [show D2M8K2.u13325 = KTree.node D2M8K2.t13330 (nat_lit 29001240) (nat_lit 3488536760) (nat_lit 0) D2M8K2.t13331 from rfl, totK_node, tot13330, tot13331]
  decide +kernel

theorem arows13327 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13327 = true := by
  rw [show D2M8K2.u13327 = KTree.node D2M8K2.t13332 (nat_lit 29003072) (nat_lit 3803927338) (nat_lit 0) D2M8K2.t13333 from rfl, allE_node, rows13332, irow13327, rows13333]
  all_goals rfl

theorem atot13327 : totK PD2M8K2 D2M8K2.u13327 = [0, 272953467053, 780016485876, 616327750178, 123548916636, 3581949829, 0, 0] := by
  rw [show D2M8K2.u13327 = KTree.node D2M8K2.t13332 (nat_lit 29003072) (nat_lit 3803927338) (nat_lit 0) D2M8K2.t13333 from rfl, totK_node, tot13332, tot13333]
  decide +kernel

theorem arows13328 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13328 = true := by
  rw [show D2M8K2.u13328 = KTree.node D2M8K2.t13334 (nat_lit 29004554) (nat_lit 2889203778) (nat_lit 0) D2M8K2.t13335 from rfl, allE_node, rows13334, irow13328, rows13335]
  all_goals rfl

theorem atot13328 : totK PD2M8K2 D2M8K2.u13328 = [0, 148141543280, 752167622268, 792989645749, 121614744895, 1096505104, 0, 0] := by
  rw [show D2M8K2.u13328 = KTree.node D2M8K2.t13334 (nat_lit 29004554) (nat_lit 2889203778) (nat_lit 0) D2M8K2.t13335 from rfl, totK_node, tot13334, tot13335]
  decide +kernel

theorem arows13331 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13331 = true := by
  rw [show D2M8K2.u13331 = KTree.node D2M8K2.t13336 (nat_lit 29006565) (nat_lit 1040799057) (nat_lit 0) D2M8K2.t13337 from rfl, allE_node, rows13336, irow13331, rows13337]
  all_goals rfl

theorem atot13331 : totK PD2M8K2 D2M8K2.u13331 = [0, 307074838857, 814113294097, 573716937102, 112957415213, 3884009855, 0, 0] := by
  rw [show D2M8K2.u13331 = KTree.node D2M8K2.t13336 (nat_lit 29006565) (nat_lit 1040799057) (nat_lit 0) D2M8K2.t13337 from rfl, totK_node, tot13336, tot13337]
  decide +kernel

theorem arows13332 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13332 = true := by
  rw [show D2M8K2.u13332 = KTree.node D2M8K2.t13338 (nat_lit 29008841) (nat_lit 1133418446) (nat_lit 0) D2M8K2.t13339 from rfl, allE_node, rows13338, irow13332, rows13339]
  all_goals rfl

theorem atot13332 : totK PD2M8K2 D2M8K2.u13332 = [0, 19199341347, 527551638720, 937860319356, 278590600874, 8771088775, 0, 0] := by
  rw [show D2M8K2.u13332 = KTree.node D2M8K2.t13338 (nat_lit 29008841) (nat_lit 1133418446) (nat_lit 0) D2M8K2.t13339 from rfl, totK_node, tot13338, tot13339]
  decide +kernel

theorem arows13334 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13334 = true := by
  rw [show D2M8K2.u13334 = KTree.node D2M8K2.t13340 (nat_lit 29010797) (nat_lit 1100826110) (nat_lit 0) D2M8K2.t13341 from rfl, allE_node, rows13340, irow13334, rows13341]
  all_goals rfl

theorem atot13334 : totK PD2M8K2 D2M8K2.u13334 = [0, 0, 314870364251, 935327021311, 464761238754, 21361993746, 0, 0] := by
  rw [show D2M8K2.u13334 = KTree.node D2M8K2.t13340 (nat_lit 29010797) (nat_lit 1100826110) (nat_lit 0) D2M8K2.t13341 from rfl, totK_node, tot13340, tot13341]
  decide +kernel

theorem arows13335 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13335 = true := by
  rw [show D2M8K2.u13335 = KTree.node D2M8K2.t13342 (nat_lit 29012840) (nat_lit 2484329771) (nat_lit 0) D2M8K2.t13343 from rfl, allE_node, rows13342, irow13335, rows13343]
  all_goals rfl

theorem atot13335 : totK PD2M8K2 D2M8K2.u13335 = [0, 0, 161997361240, 736661833062, 762611679564, 105877854827, 1239866073, 0] := by
  rw [show D2M8K2.u13335 = KTree.node D2M8K2.t13342 (nat_lit 29012840) (nat_lit 2484329771) (nat_lit 0) D2M8K2.t13343 from rfl, totK_node, tot13342, tot13343]
  decide +kernel

theorem arows13340 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13340 = true := by
  rw [show D2M8K2.u13340 = KTree.node D2M8K2.t13344 (nat_lit 29014533) (nat_lit 1724325064) (nat_lit 0) D2M8K2.t13345 from rfl, allE_node, rows13344, irow13340, rows13345]
  all_goals rfl

theorem atot13340 : totK PD2M8K2 D2M8K2.u13340 = [0, 0, 392868141234, 966853945250, 426392539686, 18704459611, 0, 0] := by
  rw [show D2M8K2.u13340 = KTree.node D2M8K2.t13344 (nat_lit 29014533) (nat_lit 1724325064) (nat_lit 0) D2M8K2.t13345 from rfl, totK_node, tot13344, tot13345]
  decide +kernel

theorem arows13341 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13341 = true := by
  rw [show D2M8K2.u13341 = KTree.node D2M8K2.t13346 (nat_lit 29021232) (nat_lit 3249623542) (nat_lit 0) D2M8K2.t13347 from rfl, allE_node, rows13346, irow13341, rows13347]
  all_goals rfl

theorem atot13341 : totK PD2M8K2 D2M8K2.u13341 = [0, 0, 299209333476, 901275794256, 557134677632, 41762107101, 0, 0] := by
  rw [show D2M8K2.u13341 = KTree.node D2M8K2.t13346 (nat_lit 29021232) (nat_lit 3249623542) (nat_lit 0) D2M8K2.t13347 from rfl, totK_node, tot13346, tot13347]
  decide +kernel

theorem arows13343 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13343 = true := by
  rw [show D2M8K2.u13343 = KTree.node D2M8K2.t13348 (nat_lit 29022956) (nat_lit 3575057190) (nat_lit 0) D2M8K2.t13349 from rfl, allE_node, rows13348, irow13343, rows13349]
  all_goals rfl

theorem atot13343 : totK PD2M8K2 D2M8K2.u13343 = [0, 0, 103438239039, 572620005710, 795166879274, 241673056556, 13105450397, 0] := by
  rw [show D2M8K2.u13343 = KTree.node D2M8K2.t13348 (nat_lit 29022956) (nat_lit 3575057190) (nat_lit 0) D2M8K2.t13349 from rfl, totK_node, tot13348, tot13349]
  decide +kernel

theorem arows13344 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13344 = true := by
  rw [show D2M8K2.u13344 = KTree.node D2M8K2.t13350 (nat_lit 29024446) (nat_lit 3692370633) (nat_lit 0) D2M8K2.t13351 from rfl, allE_node, rows13350, irow13344, rows13351]
  all_goals rfl

theorem atot13344 : totK PD2M8K2 D2M8K2.u13344 = [0, 0, 319104834899, 915086895932, 522896641824, 35829457541, 0, 0] := by
  rw [show D2M8K2.u13344 = KTree.node D2M8K2.t13350 (nat_lit 29024446) (nat_lit 3692370633) (nat_lit 0) D2M8K2.t13351 from rfl, totK_node, tot13350, tot13351]
  decide +kernel

theorem arows13347 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13347 = true := by
  rw [show D2M8K2.u13347 = KTree.node D2M8K2.t13352 (nat_lit 29026446) (nat_lit 3996905296) (nat_lit 0) D2M8K2.t13353 from rfl, allE_node, rows13352, irow13347, rows13353]
  all_goals rfl

theorem atot13347 : totK PD2M8K2 D2M8K2.u13347 = [0, 0, 163963065441, 687876552432, 724594824910, 151638188739, 4720618446, 0] := by
  rw [show D2M8K2.u13347 = KTree.node D2M8K2.t13352 (nat_lit 29026446) (nat_lit 3996905296) (nat_lit 0) D2M8K2.t13353 from rfl, totK_node, tot13352, tot13353]
  decide +kernel

theorem arows13348 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13348 = true := by
  rw [show D2M8K2.u13348 = KTree.node D2M8K2.t13354 (nat_lit 29028654) (nat_lit 3841222845) (nat_lit 0) D2M8K2.t13355 from rfl, allE_node, rows13354, irow13348, rows13355]
  all_goals rfl

theorem atot13348 : totK PD2M8K2 D2M8K2.u13348 = [0, 198027408646, 639558411241, 677400540898, 280178350012, 14041306411, 0, 0] := by
  rw [show D2M8K2.u13348 = KTree.node D2M8K2.t13354 (nat_lit 29028654) (nat_lit 3841222845) (nat_lit 0) D2M8K2.t13355 from rfl, totK_node, tot13354, tot13355]
  decide +kernel

theorem arows13350 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13350 = true := by
  rw [show D2M8K2.u13350 = KTree.node D2M8K2.t13356 (nat_lit 29031919) (nat_lit 2408006233) (nat_lit 0) D2M8K2.t13357 from rfl, allE_node, rows13356, irow13350, rows13357]
  all_goals rfl

theorem atot13350 : totK PD2M8K2 D2M8K2.u13350 = [0, 214335126354, 764677502463, 676839263990, 113540259142, 1369150432, 0, 0] := by
  rw [show D2M8K2.u13350 = KTree.node D2M8K2.t13356 (nat_lit 29031919) (nat_lit 2408006233) (nat_lit 0) D2M8K2.t13357 from rfl, totK_node, tot13356, tot13357]
  decide +kernel

theorem arows13351 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13351 = true := by
  rw [show D2M8K2.u13351 = KTree.node D2M8K2.t13358 (nat_lit 29034318) (nat_lit 3869943219) (nat_lit 0) D2M8K2.t13359 from rfl, allE_node, rows13358, irow13351, rows13359]
  all_goals rfl

theorem atot13351 : totK PD2M8K2 D2M8K2.u13351 = [0, 267412856713, 821189133072, 669165728687, 73810879415, 0, 0, 0] := by
  rw [show D2M8K2.u13351 = KTree.node D2M8K2.t13358 (nat_lit 29034318) (nat_lit 3869943219) (nat_lit 0) D2M8K2.t13359 from rfl, totK_node, tot13358, tot13359]
  decide +kernel

theorem arows13355 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13355 = true := by
  rw [show D2M8K2.u13355 = KTree.node D2M8K2.t13360 (nat_lit 29035519) (nat_lit 2392026052) (nat_lit 0) D2M8K2.t13361 from rfl, allE_node, rows13360, irow13355, rows13361]
  all_goals rfl

theorem atot13355 : totK PD2M8K2 D2M8K2.u13355 = [0, 158403939145, 681214569826, 728916800781, 237806283648, 20932498298, 0, 0] := by
  rw [show D2M8K2.u13355 = KTree.node D2M8K2.t13360 (nat_lit 29035519) (nat_lit 2392026052) (nat_lit 0) D2M8K2.t13361 from rfl, totK_node, tot13360, tot13361]
  decide +kernel

theorem arows13356 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13356 = true := by
  rw [show D2M8K2.u13356 = KTree.node D2M8K2.t13362 (nat_lit 29037052) (nat_lit 3850501190) (nat_lit 0) D2M8K2.t13363 from rfl, allE_node, rows13362, irow13356, rows13363]
  all_goals rfl

theorem atot13356 : totK PD2M8K2 D2M8K2.u13356 = [0, 148367227349, 550167489214, 755759622785, 332097574128, 14011217744, 0, 0] := by
  rw [show D2M8K2.u13356 = KTree.node D2M8K2.t13362 (nat_lit 29037052) (nat_lit 3850501190) (nat_lit 0) D2M8K2.t13363 from rfl, totK_node, tot13362, tot13363]
  decide +kernel

theorem arows13358 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13358 = true := by
  rw [show D2M8K2.u13358 = KTree.node D2M8K2.t13364 (nat_lit 29038523) (nat_lit 2248174412) (nat_lit 0) D2M8K2.t13365 from rfl, allE_node, rows13364, irow13358, rows13365]
  all_goals rfl

theorem atot13358 : totK PD2M8K2 D2M8K2.u13358 = [0, 272720853940, 852164802634, 610812801115, 66004329047, 0, 0, 0] := by
  rw [show D2M8K2.u13358 = KTree.node D2M8K2.t13364 (nat_lit 29038523) (nat_lit 2248174412) (nat_lit 0) D2M8K2.t13365 from rfl, totK_node, tot13364, tot13365]
  decide +kernel

theorem arows13359 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13359 = true := by
  rw [show D2M8K2.u13359 = KTree.node D2M8K2.t13366 (nat_lit 29040244) (nat_lit 4009723249) (nat_lit 0) D2M8K2.t13367 from rfl, allE_node, rows13366, irow13359, rows13367]
  all_goals rfl

theorem atot13359 : totK PD2M8K2 D2M8K2.u13359 = [0, 104354173249, 564777581163, 832391578770, 259867969819, 13049727234, 0, 0] := by
  rw [show D2M8K2.u13359 = KTree.node D2M8K2.t13366 (nat_lit 29040244) (nat_lit 4009723249) (nat_lit 0) D2M8K2.t13367 from rfl, totK_node, tot13366, tot13367]
  decide +kernel

theorem arows13362 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13362 = true := by
  rw [show D2M8K2.u13362 = KTree.node D2M8K2.t13368 (nat_lit 29041920) (nat_lit 3686612343) (nat_lit 0) D2M8K2.t13369 from rfl, allE_node, rows13368, irow13362, rows13369]
  all_goals rfl

theorem atot13362 : totK PD2M8K2 D2M8K2.u13362 = [0, 316926606150, 892828600869, 560839576859, 50128005165, 0, 0, 0] := by
  rw [show D2M8K2.u13362 = KTree.node D2M8K2.t13368 (nat_lit 29041920) (nat_lit 3686612343) (nat_lit 0) D2M8K2.t13369 from rfl, totK_node, tot13368, tot13369]
  decide +kernel

theorem arows13363 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13363 = true := by
  rw [show D2M8K2.u13363 = KTree.node D2M8K2.t13370 (nat_lit 29043620) (nat_lit 3193665043) (nat_lit 0) D2M8K2.t13371 from rfl, allE_node, rows13370, irow13363, rows13371]
  all_goals rfl

theorem atot13363 : totK PD2M8K2 D2M8K2.u13363 = [0, 86527685341, 515178129101, 863577837502, 290573032670, 13250685261, 0, 0] := by
  rw [show D2M8K2.u13363 = KTree.node D2M8K2.t13370 (nat_lit 29043620) (nat_lit 3193665043) (nat_lit 0) D2M8K2.t13371 from rfl, totK_node, tot13370, tot13371]
  decide +kernel

theorem arows13365 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13365 = true := by
  rw [show D2M8K2.u13365 = KTree.node D2M8K2.t13372 (nat_lit 29044978) (nat_lit 3641934925) (nat_lit 0) D2M8K2.t13373 from rfl, allE_node, rows13372, irow13365, rows13373]
  all_goals rfl

theorem atot13365 : totK PD2M8K2 D2M8K2.u13365 = [0, 358558880073, 941995093166, 502206838247, 39973299822, 0, 0, 0] := by
  rw [show D2M8K2.u13365 = KTree.node D2M8K2.t13372 (nat_lit 29044978) (nat_lit 3641934925) (nat_lit 0) D2M8K2.t13373 from rfl, totK_node, tot13372, tot13373]
  decide +kernel

theorem arows13366 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13366 = true := by
  rw [show D2M8K2.u13366 = KTree.node D2M8K2.t13374 (nat_lit 29046659) (nat_lit 2148490749) (nat_lit 0) D2M8K2.t13375 from rfl, allE_node, rows13374, irow13366, rows13375]
  all_goals rfl

theorem atot13366 : totK PD2M8K2 D2M8K2.u13366 = [0, 0, 569662684889, 1016008769770, 223338069486, 4980514959, 0, 0] := by
  rw [show D2M8K2.u13366 = KTree.node D2M8K2.t13374 (nat_lit 29046659) (nat_lit 2148490749) (nat_lit 0) D2M8K2.t13375 from rfl, totK_node, tot13374, tot13375]
  decide +kernel

theorem arows13372 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13372 = true := by
  rw [show D2M8K2.u13372 = KTree.node D2M8K2.t13376 (nat_lit 29052178) (nat_lit 3019351915) (nat_lit 0) D2M8K2.t13377 from rfl, allE_node, rows13376, irow13372, rows13377]
  all_goals rfl

theorem atot13372 : totK PD2M8K2 D2M8K2.u13372 = [0, 0, 324474079229, 940172602476, 459376704553, 24810397728, 0, 0] := by
  rw [show D2M8K2.u13372 = KTree.node D2M8K2.t13376 (nat_lit 29052178) (nat_lit 3019351915) (nat_lit 0) D2M8K2.t13377 from rfl, totK_node, tot13376, tot13377]
  decide +kernel

theorem arows13373 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13373 = true := by
  rw [show D2M8K2.u13373 = KTree.node D2M8K2.t13378 (nat_lit 29054119) (nat_lit 2344446533) (nat_lit 0) D2M8K2.t13379 from rfl, allE_node, rows13378, irow13373, rows13379]
  all_goals rfl

theorem atot13373 : totK PD2M8K2 D2M8K2.u13373 = [0, 0, 180027324132, 752003156052, 716765336947, 107752085854, 1138244013, 0] := by
  rw [show D2M8K2.u13373 = KTree.node D2M8K2.t13378 (nat_lit 29054119) (nat_lit 2344446533) (nat_lit 0) D2M8K2.t13379 from rfl, totK_node, tot13378, tot13379]
  decide +kernel

theorem arows13375 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13375 = true := by
  rw [show D2M8K2.u13375 = KTree.node D2M8K2.t13380 (nat_lit 29055945) (nat_lit 1837758669) (nat_lit 0) D2M8K2.t13381 from rfl, allE_node, rows13380, irow13375, rows13381]
  all_goals rfl

theorem atot13375 : totK PD2M8K2 D2M8K2.u13375 = [0, 0, 367029472005, 962927999781, 442544519506, 21238366550, 0, 0] := by
  rw [show D2M8K2.u13375 = KTree.node D2M8K2.t13380 (nat_lit 29055945) (nat_lit 1837758669) (nat_lit 0) D2M8K2.t13381 from rfl, totK_node, tot13380, tot13381]
  decide +kernel

theorem arows13376 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13376 = true := by
  rw [show D2M8K2.u13376 = KTree.node D2M8K2.t13382 (nat_lit 29059247) (nat_lit 1859193570) (nat_lit 0) D2M8K2.t13383 from rfl, allE_node, rows13382, irow13376, rows13383]
  all_goals rfl

theorem atot13376 : totK PD2M8K2 D2M8K2.u13376 = [0, 0, 381047974782, 943941456305, 436148457421, 25897365295, 0, 0] := by
  rw [show D2M8K2.u13376 = KTree.node D2M8K2.t13382 (nat_lit 29059247) (nat_lit 1859193570) (nat_lit 0) D2M8K2.t13383 from rfl, totK_node, tot13382, tot13383]
  decide +kernel

theorem arows13379 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13379 = true := by
  rw [show D2M8K2.u13379 = KTree.node D2M8K2.t13384 (nat_lit 29062584) (nat_lit 3424934041) (nat_lit 0) D2M8K2.t13385 from rfl, allE_node, rows13384, irow13379, rows13385]
  all_goals rfl

theorem atot13379 : totK PD2M8K2 D2M8K2.u13379 = [0, 0, 353975922966, 937142440347, 480926824636, 27303834419, 0, 0] := by
  rw [show D2M8K2.u13379 = KTree.node D2M8K2.t13384 (nat_lit 29062584) (nat_lit 3424934041) (nat_lit 0) D2M8K2.t13385 from rfl, totK_node, tot13384, tot13385]
  decide +kernel

theorem arows13380 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13380 = true := by
  rw [show D2M8K2.u13380 = KTree.node D2M8K2.t13386 (nat_lit 29065575) (nat_lit 3611269153) (nat_lit 0) D2M8K2.t13387 from rfl, allE_node, rows13386, irow13380, rows13387]
  all_goals rfl

theorem atot13380 : totK PD2M8K2 D2M8K2.u13380 = [0, 0, 371628338034, 937516807039, 451956976632, 32547243808, 0, 0] := by
  rw [show D2M8K2.u13380 = KTree.node D2M8K2.t13386 (nat_lit 29065575) (nat_lit 3611269153) (nat_lit 0) D2M8K2.t13387 from rfl, totK_node, tot13386, tot13387]
  decide +kernel

theorem arows13382 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13382 = true := by
  rw [show D2M8K2.u13382 = KTree.node D2M8K2.t13388 (nat_lit 29067269) (nat_lit 2327739443) (nat_lit 0) D2M8K2.t13389 from rfl, allE_node, rows13388, irow13382, rows13389]
  all_goals rfl

theorem atot13382 : totK PD2M8K2 D2M8K2.u13382 = [0, 0, 78198084115, 638558837365, 837062678247, 192215148162, 4977114383, 0] := by
  rw [show D2M8K2.u13382 = KTree.node D2M8K2.t13388 (nat_lit 29067269) (nat_lit 2327739443) (nat_lit 0) D2M8K2.t13389 from rfl, totK_node, tot13388, tot13389]
  decide +kernel

theorem arows13383 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13383 = true := by
  rw [show D2M8K2.u13383 = KTree.node D2M8K2.t13390 (nat_lit 29114294) (nat_lit 3696774062) (nat_lit 0) D2M8K2.t13391 from rfl, allE_node, rows13390, irow13383, rows13391]
  all_goals rfl

theorem atot13383 : totK PD2M8K2 D2M8K2.u13383 = [0, 0, 382251552001, 956787295464, 423512809118, 22386190152, 0, 0] := by
  rw [show D2M8K2.u13383 = KTree.node D2M8K2.t13390 (nat_lit 29114294) (nat_lit 3696774062) (nat_lit 0) D2M8K2.t13391 from rfl, totK_node, tot13390, tot13391]
  decide +kernel

theorem arows13387 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13387 = true := by
  rw [show D2M8K2.u13387 = KTree.node D2M8K2.t13392 (nat_lit 29115948) (nat_lit 3571884060) (nat_lit 0) D2M8K2.t13393 from rfl, allE_node, rows13392, irow13387, rows13393]
  all_goals rfl

theorem atot13387 : totK PD2M8K2 D2M8K2.u13387 = [0, 0, 101810912883, 686323831243, 854850577753, 130489173791, 1369150432, 0] := by
  rw [show D2M8K2.u13387 = KTree.node D2M8K2.t13392 (nat_lit 29115948) (nat_lit 3571884060) (nat_lit 0) D2M8K2.t13393 from rfl, totK_node, tot13392, tot13393]
  decide +kernel

theorem arows13388 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13388 = true := by
  rw [show D2M8K2.u13388 = KTree.node D2M8K2.t13394 (nat_lit 29121100) (nat_lit 3928047371) (nat_lit 0) D2M8K2.t13395 from rfl, allE_node, rows13394, irow13388, rows13395]
  all_goals rfl

theorem atot13388 : totK PD2M8K2 D2M8K2.u13388 = [0, 0, 321043300692, 912446104688, 512788083886, 33850377628, 0, 0] := by
  rw [show D2M8K2.u13388 = KTree.node D2M8K2.t13394 (nat_lit 29121100) (nat_lit 3928047371) (nat_lit 0) D2M8K2.t13395 from rfl, totK_node, tot13394, tot13395]
  decide +kernel

theorem arows13390 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13390 = true := by
  rw [show D2M8K2.u13390 = KTree.node D2M8K2.t13396 (nat_lit 29123163) (nat_lit 3699029503) (nat_lit 0) D2M8K2.t13397 from rfl, allE_node, rows13396, irow13390, rows13397]
  all_goals rfl

theorem atot13390 : totK PD2M8K2 D2M8K2.u13390 = [0, 0, 87179432255, 580579896158, 817261647850, 233504265337, 12983449796, 0] := by
  rw [show D2M8K2.u13390 = KTree.node D2M8K2.t13396 (nat_lit 29123163) (nat_lit 3699029503) (nat_lit 0) D2M8K2.t13397 from rfl, totK_node, tot13396, tot13397]
  decide +kernel

theorem arows13391 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13391 = true := by
  rw [show D2M8K2.u13391 = KTree.node D2M8K2.t13398 (nat_lit 29124916) (nat_lit 3787071353) (nat_lit 0) D2M8K2.t13399 from rfl, allE_node, rows13398, irow13391, rows13399]
  all_goals rfl

theorem atot13391 : totK PD2M8K2 D2M8K2.u13391 = [0, 0, 321249888496, 887047390229, 533661360659, 39535429873, 0, 0] := by
  rw [show D2M8K2.u13391 = KTree.node D2M8K2.t13398 (nat_lit 29124916) (nat_lit 3787071353) (nat_lit 0) D2M8K2.t13399 from rfl, totK_node, tot13398, tot13399]
  decide +kernel

theorem arows13394 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13394 = true := by
  rw [show D2M8K2.u13394 = KTree.node D2M8K2.t13400 (nat_lit 29126683) (nat_lit 2239444724) (nat_lit 0) D2M8K2.t13401 from rfl, allE_node, rows13400, irow13394, rows13401]
  all_goals rfl

theorem atot13394 : totK PD2M8K2 D2M8K2.u13394 = [0, 0, 133693195524, 600353689847, 764636487858, 232790609004, 13184317400, 0] := by
  rw [show D2M8K2.u13394 = KTree.node D2M8K2.t13400 (nat_lit 29126683) (nat_lit 2239444724) (nat_lit 0) D2M8K2.t13401 from rfl, totK_node, tot13400, tot13401]
  decide +kernel

theorem arows13395 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13395 = true := by
  rw [show D2M8K2.u13395 = KTree.node D2M8K2.t13402 (nat_lit 29128146) (nat_lit 3474668509) (nat_lit 0) D2M8K2.t13403 from rfl, allE_node, rows13402, irow13395, rows13403]
  all_goals rfl

theorem atot13395 : totK PD2M8K2 D2M8K2.u13395 = [0, 0, 281782704029, 867042931830, 570441669413, 51082819718, 0, 0] := by
  rw [show D2M8K2.u13395 = KTree.node D2M8K2.t13402 (nat_lit 29128146) (nat_lit 3474668509) (nat_lit 0) D2M8K2.t13403 from rfl, totK_node, tot13402, tot13403]
  decide +kernel

theorem arows13397 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13397 = true := by
  rw [show D2M8K2.u13397 = KTree.node D2M8K2.t13404 (nat_lit 29130101) (nat_lit 2378546130) (nat_lit 0) D2M8K2.t13405 from rfl, allE_node, rows13404, irow13397, rows13405]
  all_goals rfl

theorem atot13397 : totK PD2M8K2 D2M8K2.u13397 = [0, 0, 167878671790, 658489498806, 761711697723, 183613146692, 4980514959, 0] := by
  rw [show D2M8K2.u13397 = KTree.node D2M8K2.t13404 (nat_lit 29130101) (nat_lit 2378546130) (nat_lit 0) D2M8K2.t13405 from rfl, totK_node, tot13404, tot13405]
  decide +kernel

theorem arows13398 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13398 = true := by
  rw [show D2M8K2.u13398 = KTree.node D2M8K2.t13406 (nat_lit 29132358) (nat_lit 3784348551) (nat_lit 0) D2M8K2.t13407 from rfl, allE_node, rows13406, irow13398, rows13407]
  all_goals rfl

theorem atot13398 : totK PD2M8K2 D2M8K2.u13398 = [0, 0, 153433715120, 827442528001, 697345527179, 75081610698, 1268739303, 0] := by
  rw [show D2M8K2.u13398 = KTree.node D2M8K2.t13406 (nat_lit 29132358) (nat_lit 3784348551) (nat_lit 0) D2M8K2.t13407 from rfl, totK_node, tot13406, tot13407]
  decide +kernel

theorem arows13403 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13403 = true := by
  rw [show D2M8K2.u13403 = KTree.node D2M8K2.t13408 (nat_lit 29135056) (nat_lit 2530392442) (nat_lit 0) D2M8K2.t13409 from rfl, allE_node, rows13408, irow13403, rows13409]
  all_goals rfl

theorem atot13403 : totK PD2M8K2 D2M8K2.u13403 = [0, 0, 0, 385520934046, 946764046842, 370753622372, 22962566010, 0] := by
  rw [show D2M8K2.u13403 = KTree.node D2M8K2.t13408 (nat_lit 29135056) (nat_lit 2530392442) (nat_lit 0) D2M8K2.t13409 from rfl, totK_node, tot13408, tot13409]
  decide +kernel

theorem arows13404 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13404 = true := by
  rw [show D2M8K2.u13404 = KTree.node D2M8K2.t13410 (nat_lit 29137008) (nat_lit 3513892255) (nat_lit 0) D2M8K2.t13411 from rfl, allE_node, rows13410, irow13404, rows13411]
  all_goals rfl

theorem atot13404 : totK PD2M8K2 D2M8K2.u13404 = [0, 0, 0, 184259277659, 801359003842, 618825591044, 87930294280, 1209030869] := by
  rw [show D2M8K2.u13404 = KTree.node D2M8K2.t13410 (nat_lit 29137008) (nat_lit 3513892255) (nat_lit 0) D2M8K2.t13411 from rfl, totK_node, tot13410, tot13411]
  decide +kernel

theorem arows13406 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13406 = true := by
  rw [show D2M8K2.u13406 = KTree.node D2M8K2.t13412 (nat_lit 29142505) (nat_lit 1398124101) (nat_lit 0) D2M8K2.t13413 from rfl, allE_node, rows13412, irow13406, rows13413]
  all_goals rfl

theorem atot13406 : totK PD2M8K2 D2M8K2.u13406 = [0, 0, 0, 458597896371, 967997680187, 320491582401, 14707833475, 0] := by
  rw [show D2M8K2.u13406 = KTree.node D2M8K2.t13412 (nat_lit 29142505) (nat_lit 1398124101) (nat_lit 0) D2M8K2.t13413 from rfl, totK_node, tot13412, tot13413]
  decide +kernel

theorem arows13407 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13407 = true := by
  rw [show D2M8K2.u13407 = KTree.node D2M8K2.t13414 (nat_lit 29148008) (nat_lit 3873769982) (nat_lit 0) D2M8K2.t13415 from rfl, allE_node, rows13414, irow13407, rows13415]
  all_goals rfl

theorem atot13407 : totK PD2M8K2 D2M8K2.u13407 = [0, 0, 0, 398835064786, 948819437317, 371082664327, 19658552049, 0] := by
  rw [show D2M8K2.u13407 = KTree.node D2M8K2.t13414 (nat_lit 29148008) (nat_lit 3873769982) (nat_lit 0) D2M8K2.t13415 from rfl, totK_node, tot13414, tot13415]
  decide +kernel

theorem arows13410 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13410 = true := by
  rw [show D2M8K2.u13410 = KTree.node D2M8K2.t13416 (nat_lit 29149317) (nat_lit 1726220677) (nat_lit 0) D2M8K2.t13417 from rfl, allE_node, rows13416, irow13410, rows13417]
  all_goals rfl

theorem atot13410 : totK PD2M8K2 D2M8K2.u13410 = [0, 0, 0, 479015253513, 964871588540, 302374540838, 16122459143, 0] := by
  rw [show D2M8K2.u13410 = KTree.node D2M8K2.t13416 (nat_lit 29149317) (nat_lit 1726220677) (nat_lit 0) D2M8K2.t13417 from rfl, totK_node, tot13416, tot13417]
  decide +kernel

theorem arows13411 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13411 = true := by
  rw [show D2M8K2.u13411 = KTree.node D2M8K2.t13418 (nat_lit 29159089) (nat_lit 1297909030) (nat_lit 0) D2M8K2.t13419 from rfl, allE_node, rows13418, irow13411, rows13419]
  all_goals rfl

theorem atot13411 : totK PD2M8K2 D2M8K2.u13411 = [0, 0, 357932935788, 929779550460, 519625406766, 38006924811, 0, 0] := by
  rw [show D2M8K2.u13411 = KTree.node D2M8K2.t13418 (nat_lit 29159089) (nat_lit 1297909030) (nat_lit 0) D2M8K2.t13419 from rfl, totK_node, tot13418, tot13419]
  decide +kernel

theorem arows13413 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13413 = true := by
  rw [show D2M8K2.u13413 = KTree.node D2M8K2.t13420 (nat_lit 29160576) (nat_lit 2248510775) (nat_lit 2048) D2M8K2.t13421 from rfl, allE_node, rows13420, irow13413, rows13421]
  all_goals rfl

theorem atot13413 : totK PD2M8K2 D2M8K2.u13413 = [0, 0, 84596764418, 530536150856, 855142985602, 323273871165, 22718628358, 0] := by
  rw [show D2M8K2.u13413 = KTree.node D2M8K2.t13420 (nat_lit 29160576) (nat_lit 2248510775) (nat_lit 2048) D2M8K2.t13421 from rfl, totK_node, tot13420, tot13421]
  decide +kernel

theorem arows13414 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13414 = true := by
  rw [show D2M8K2.u13414 = KTree.node D2M8K2.t13422 (nat_lit 29162124) (nat_lit 2525274801) (nat_lit 0) D2M8K2.t13423 from rfl, allE_node, rows13422, irow13414, rows13423]
  all_goals rfl

theorem atot13414 : totK PD2M8K2 D2M8K2.u13414 = [0, 0, 300554480130, 813979997292, 600660716517, 109149587921, 1409560813, 0] := by
  rw [show D2M8K2.u13414 = KTree.node D2M8K2.t13422 (nat_lit 29162124) (nat_lit 2525274801) (nat_lit 0) D2M8K2.t13423 from rfl, totK_node, tot13422, tot13423]
  decide +kernel

theorem arows13418 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13418 = true := by
  rw [show D2M8K2.u13418 = KTree.node D2M8K2.t13424 (nat_lit 29163825) (nat_lit 1550608778) (nat_lit 0) D2M8K2.t13425 from rfl, allE_node, rows13424, irow13418, rows13425]
  all_goals rfl

theorem atot13418 : totK PD2M8K2 D2M8K2.u13418 = [0, 0, 111594056885, 667433311272, 813366450076, 179905299618, 9751947372, 0] := by
  rw [show D2M8K2.u13418 = KTree.node D2M8K2.t13424 (nat_lit 29163825) (nat_lit 1550608778) (nat_lit 0) D2M8K2.t13425 from rfl, totK_node, tot13424, tot13425]
  decide +kernel

theorem arows13419 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13419 = true := by
  rw [show D2M8K2.u13419 = KTree.node D2M8K2.t13426 (nat_lit 29165755) (nat_lit 1172708448) (nat_lit 0) D2M8K2.t13427 from rfl, allE_node, rows13426, irow13419, rows13427]
  all_goals rfl

theorem atot13419 : totK PD2M8K2 D2M8K2.u13419 = [0, 0, 346175764150, 921622017069, 509244158941, 39853482271, 0, 0] := by
  rw [show D2M8K2.u13419 = KTree.node D2M8K2.t13426 (nat_lit 29165755) (nat_lit 1172708448) (nat_lit 0) D2M8K2.t13427 from rfl, totK_node, tot13426, tot13427]
  decide +kernel

theorem arows13421 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13421 = true := by
  rw [show D2M8K2.u13421 = KTree.node D2M8K2.t13428 (nat_lit 29167885) (nat_lit 1049952993) (nat_lit 0) D2M8K2.t13429 from rfl, allE_node, rows13428, irow13421, rows13429]
  all_goals rfl

theorem atot13421 : totK PD2M8K2 D2M8K2.u13421 = [0, 0, 120779343930, 662849625440, 812598764944, 189461801291, 9882685783, 0] := by
  rw [show D2M8K2.u13421 = KTree.node D2M8K2.t13428 (nat_lit 29167885) (nat_lit 1049952993) (nat_lit 0) D2M8K2.t13429 from rfl, totK_node, tot13428, tot13429]
  decide +kernel

theorem arows13422 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13422 = true := by
  rw [show D2M8K2.u13422 = KTree.node D2M8K2.t13430 (nat_lit 29169361) (nat_lit 1499983018) (nat_lit 0) D2M8K2.t13431 from rfl, allE_node, rows13430, irow13422, rows13431]
  all_goals rfl

theorem atot13422 : totK PD2M8K2 D2M8K2.u13422 = [0, 0, 367016434126, 924604992512, 483132262259, 38295894736, 0, 0] := by
  rw [show D2M8K2.u13422 = KTree.node D2M8K2.t13430 (nat_lit 29169361) (nat_lit 1499983018) (nat_lit 0) D2M8K2.t13431 from rfl, totK_node, tot13430, tot13431]
  decide +kernel

theorem arows13425 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13425 = true := by
  rw [show D2M8K2.u13425 = KTree.node D2M8K2.t13432 (nat_lit 29171278) (nat_lit 3599225207) (nat_lit 0) D2M8K2.t13433 from rfl, allE_node, rows13432, irow13425, rows13433]
  all_goals rfl

theorem atot13425 : totK PD2M8K2 D2M8K2.u13425 = [0, 0, 90105146488, 687150442694, 889828427310, 162055225484, 2813333534, 0] := by
  rw [show D2M8K2.u13425 = KTree.node D2M8K2.t13432 (nat_lit 29171278) (nat_lit 3599225207) (nat_lit 0) D2M8K2.t13433 from rfl, totK_node, tot13432, tot13433]
  decide +kernel

theorem arows13426 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13426 = true := by
  rw [show D2M8K2.u13426 = KTree.node D2M8K2.t13434 (nat_lit 29173592) (nat_lit 2792797439) (nat_lit 0) D2M8K2.t13435 from rfl, allE_node, rows13434, irow13426, rows13435]
  all_goals rfl

theorem atot13426 : totK PD2M8K2 D2M8K2.u13426 = [0, 0, 416376789398, 1000580228149, 412732967862, 22178700658, 0, 0] := by
  rw [show D2M8K2.u13426 = KTree.node D2M8K2.t13434 (nat_lit 29173592) (nat_lit 2792797439) (nat_lit 0) D2M8K2.t13435 from rfl, totK_node, tot13434, tot13435]
  decide +kernel

theorem arows13428 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13428 = true := by
  rw [show D2M8K2.u13428 = KTree.node D2M8K2.t13436 (nat_lit 29197778) (nat_lit 3583026869) (nat_lit 0) D2M8K2.t13437 from rfl, allE_node, rows13436, irow13428, rows13437]
  all_goals rfl

theorem atot13428 : totK PD2M8K2 D2M8K2.u13428 = [0, 0, 227080085329, 763991727831, 637376355778, 94678020078, 1310166938, 0] := by
  rw [show D2M8K2.u13428 = KTree.node D2M8K2.t13436 (nat_lit 29197778) (nat_lit 3583026869) (nat_lit 0) D2M8K2.t13437 from rfl, totK_node, tot13436, tot13437]
  decide +kernel

theorem arows13429 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13429 = true := by
  rw [show D2M8K2.u13429 = KTree.node D2M8K2.t13438 (nat_lit 29200224) (nat_lit 2658080809) (nat_lit 0) D2M8K2.t13439 from rfl, allE_node, rows13438, irow13429, rows13439]
  all_goals rfl

theorem atot13429 : totK PD2M8K2 D2M8K2.u13429 = [0, 0, 250456051342, 836109821352, 658056782480, 61213845181, 0, 0] := by
  rw [show D2M8K2.u13429 = KTree.node D2M8K2.t13438 (nat_lit 29200224) (nat_lit 2658080809) (nat_lit 0) D2M8K2.t13439 from rfl, totK_node, tot13438, tot13439]
  decide +kernel

theorem arows13436 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13436 = true := by
  rw [show D2M8K2.u13436 = KTree.node D2M8K2.t13440 (nat_lit 29201838) (nat_lit 4004436567) (nat_lit 0) D2M8K2.t13441 from rfl, allE_node, rows13440, irow13436, rows13441]
  all_goals rfl

theorem atot13436 : totK PD2M8K2 D2M8K2.u13436 = [0, 0, 165299715247, 691571450695, 725716585328, 215960220858, 13604428459, 0] := by
  rw [show D2M8K2.u13436 = KTree.node D2M8K2.t13440 (nat_lit 29201838) (nat_lit 4004436567) (nat_lit 0) D2M8K2.t13441 from rfl, totK_node, tot13440, tot13441]
  decide +kernel

theorem arows13437 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13437 = true := by
  rw [show D2M8K2.u13437 = KTree.node D2M8K2.t13442 (nat_lit 29203475) (nat_lit 2570915732) (nat_lit 128) D2M8K2.t13443 from rfl, allE_node, rows13442, irow13437, rows13443]
  all_goals rfl

theorem atot13437 : totK PD2M8K2 D2M8K2.u13437 = [0, 0, 267503068189, 815261742957, 629004571114, 112171981898, 1409560813, 0] := by
  rw [show D2M8K2.u13437 = KTree.node D2M8K2.t13442 (nat_lit 29203475) (nat_lit 2570915732) (nat_lit 128) D2M8K2.t13443 from rfl, totK_node, tot13442, tot13443]
  decide +kernel

theorem arows13439 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13439 = true := by
  rw [show D2M8K2.u13439 = KTree.node D2M8K2.t13444 (nat_lit 29204941) (nat_lit 1389735202) (nat_lit 0) D2M8K2.t13445 from rfl, allE_node, rows13444, irow13439, rows13445]
  all_goals rfl

theorem atot13439 : totK PD2M8K2 D2M8K2.u13439 = [0, 0, 171045894958, 716246171568, 757720584410, 139710622698, 2309606161, 0] := by
  rw [show D2M8K2.u13439 = KTree.node D2M8K2.t13444 (nat_lit 29204941) (nat_lit 1389735202) (nat_lit 0) D2M8K2.t13445 from rfl, totK_node, tot13444, tot13445]
  decide +kernel

theorem arows13440 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13440 = true := by
  rw [show D2M8K2.u13440 = KTree.node D2M8K2.t13446 (nat_lit 29210245) (nat_lit 1367051028) (nat_lit 0) D2M8K2.t13447 from rfl, allE_node, rows13446, irow13440, rows13447]
  all_goals rfl

theorem atot13440 : totK PD2M8K2 D2M8K2.u13440 = [0, 0, 259558462419, 752640455024, 611025944436, 148336800230, 10740121073, 0] := by
  rw [show D2M8K2.u13440 = KTree.node D2M8K2.t13446 (nat_lit 29210245) (nat_lit 1367051028) (nat_lit 0) D2M8K2.t13447 from rfl, totK_node, tot13446, tot13447]
  decide +kernel

theorem arows13443 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13443 = true := by
  rw [show D2M8K2.u13443 = KTree.node D2M8K2.t13448 (nat_lit 29211480) (nat_lit 3333130305) (nat_lit 0) D2M8K2.t13449 from rfl, allE_node, rows13448, irow13443, rows13449]
  all_goals rfl

theorem atot13443 : totK PD2M8K2 D2M8K2.u13443 = [0, 0, 161830903420, 745988989535, 755795461968, 114076538286, 1096505104, 0] := by
  rw [show D2M8K2.u13443 = KTree.node D2M8K2.t13448 (nat_lit 29211480) (nat_lit 3333130305) (nat_lit 0) D2M8K2.t13449 from rfl, totK_node, tot13448, tot13449]
  decide +kernel

theorem arows13444 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13444 = true := by
  rw [show D2M8K2.u13444 = KTree.node D2M8K2.t13450 (nat_lit 29213769) (nat_lit 1649727924) (nat_lit 0) D2M8K2.t13451 from rfl, allE_node, rows13450, irow13444, rows13451]
  all_goals rfl

theorem atot13444 : totK PD2M8K2 D2M8K2.u13444 = [0, 0, 251985759824, 793327428947, 625893876143, 124435329860, 3884009855, 0] := by
  rw [show D2M8K2.u13444 = KTree.node D2M8K2.t13450 (nat_lit 29213769) (nat_lit 1649727924) (nat_lit 0) D2M8K2.t13451 from rfl, totK_node, tot13450, tot13451]
  decide +kernel

theorem arows13446 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13446 = true := by
  rw [show D2M8K2.u13446 = KTree.node D2M8K2.t13452 (nat_lit 29238456) (nat_lit 3561091855) (nat_lit 0) D2M8K2.t13453 from rfl, allE_node, rows13452, irow13446, rows13453]
  all_goals rfl

theorem atot13446 : totK PD2M8K2 D2M8K2.u13446 = [0, 0, 401215674657, 947732999002, 406745588372, 22310813927, 0, 0] := by
  rw [show D2M8K2.u13446 = KTree.node D2M8K2.t13452 (nat_lit 29238456) (nat_lit 3561091855) (nat_lit 0) D2M8K2.t13453 from rfl, totK_node, tot13452, tot13453]
  decide +kernel

theorem arows13447 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13447 = true := by
  rw [show D2M8K2.u13447 = KTree.node D2M8K2.t13454 (nat_lit 29239762) (nat_lit 3801664838) (nat_lit 0) D2M8K2.t13455 from rfl, allE_node, rows13454, irow13447, rows13455]
  all_goals rfl

theorem atot13447 : totK PD2M8K2 D2M8K2.u13447 = [0, 0, 113504407933, 701468463834, 814461256935, 114533886608, 1310517177, 0] := by
  rw [show D2M8K2.u13447 = KTree.node D2M8K2.t13454 (nat_lit 29239762) (nat_lit 3801664838) (nat_lit 0) D2M8K2.t13455 from rfl, totK_node, tot13454, tot13455]
  decide +kernel

theorem arows13451 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13451 = true := by
  rw [show D2M8K2.u13451 = KTree.node D2M8K2.t13456 (nat_lit 29242196) (nat_lit 3657281242) (nat_lit 0) D2M8K2.t13457 from rfl, allE_node, rows13456, irow13451, rows13457]
  all_goals rfl

theorem atot13451 : totK PD2M8K2 D2M8K2.u13451 = [0, 0, 378738718315, 936698231749, 481307993197, 36771068427, 0, 0] := by
  rw [show D2M8K2.u13451 = KTree.node D2M8K2.t13456 (nat_lit 29242196) (nat_lit 3657281242) (nat_lit 0) D2M8K2.t13457 from rfl, totK_node, tot13456, tot13457]
  decide +kernel

theorem arows13452 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13452 = true := by
  rw [show D2M8K2.u13452 = KTree.node D2M8K2.t13458 (nat_lit 29243930) (nat_lit 4044067566) (nat_lit 0) D2M8K2.t13459 from rfl, allE_node, rows13458, irow13452, rows13459]
  all_goals rfl

theorem atot13452 : totK PD2M8K2 D2M8K2.u13452 = [0, 0, 64011344569, 557909979681, 875562364160, 298069143210, 15066332673, 0] := by
  rw [show D2M8K2.u13452 = KTree.node D2M8K2.t13458 (nat_lit 29243930) (nat_lit 4044067566) (nat_lit 0) D2M8K2.t13459 from rfl, totK_node, tot13458, tot13459]
  decide +kernel

theorem arows13454 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13454 = true := by
  rw [show D2M8K2.u13454 = KTree.node D2M8K2.t13460 (nat_lit 29249109) (nat_lit 1734347021) (nat_lit 0) D2M8K2.t13461 from rfl, allE_node, rows13460, irow13454, rows13461]
  all_goals rfl

theorem atot13454 : totK PD2M8K2 D2M8K2.u13454 = [0, 0, 370867354868, 954343228659, 478183765767, 29897732646, 0, 0] := by
  rw [show D2M8K2.u13454 = KTree.node D2M8K2.t13460 (nat_lit 29249109) (nat_lit 1734347021) (nat_lit 0) D2M8K2.t13461 from rfl, totK_node, tot13460, tot13461]
  decide +kernel

theorem arows13455 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13455 = true := by
  rw [show D2M8K2.u13455 = KTree.node D2M8K2.t13462 (nat_lit 29250793) (nat_lit 1490688371) (nat_lit 0) D2M8K2.t13463 from rfl, allE_node, rows13462, irow13455, rows13463]
  all_goals rfl

theorem atot13455 : totK PD2M8K2 D2M8K2.u13455 = [0, 0, 0, 505748756031, 963101133700, 271527997185, 13170675918, 0] := by
  rw [show D2M8K2.u13455 = KTree.node D2M8K2.t13462 (nat_lit 29250793) (nat_lit 1490688371) (nat_lit 0) D2M8K2.t13463 from rfl, totK_node, tot13462, tot13463]
  decide +kernel

theorem arows13458 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13458 = true := by
  rw [show D2M8K2.u13458 = KTree.node D2M8K2.t13464 (nat_lit 29252171) (nat_lit 1867791544) (nat_lit 0) D2M8K2.t13465 from rfl, allE_node, rows13464, irow13458, rows13465]
  all_goals rfl

theorem atot13458 : totK PD2M8K2 D2M8K2.u13458 = [0, 0, 381500357105, 911657868983, 470863257187, 36467023279, 0, 0] := by
  rw [show D2M8K2.u13458 = KTree.node D2M8K2.t13464 (nat_lit 29252171) (nat_lit 1867791544) (nat_lit 0) D2M8K2.t13465 from rfl, totK_node, tot13464, tot13465]
  decide +kernel

theorem arows13459 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13459 = true := by
  rw [show D2M8K2.u13459 = KTree.node D2M8K2.t13466 (nat_lit 29253889) (nat_lit 1538211931) (nat_lit 0) D2M8K2.t13467 from rfl, allE_node, rows13466, irow13459, rows13467]
  all_goals rfl

theorem atot13459 : totK PD2M8K2 D2M8K2.u13459 = [0, 0, 65854189168, 614180748328, 891930202844, 201701388378, 4980514959, 0] := by
  rw [show D2M8K2.u13459 = KTree.node D2M8K2.t13466 (nat_lit 29253889) (nat_lit 1538211931) (nat_lit 0) D2M8K2.t13467 from rfl, totK_node, tot13466, tot13467]
  decide +kernel

theorem arows13461 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13461 = true := by
  rw [show D2M8K2.u13461 = KTree.node D2M8K2.t13468 (nat_lit 29256028) (nat_lit 2535959085) (nat_lit 0) D2M8K2.t13469 from rfl, allE_node, rows13468, irow13461, rows13469]
  all_goals rfl

theorem atot13461 : totK PD2M8K2 D2M8K2.u13461 = [0, 0, 383826340410, 967622492320, 447046006488, 25187746441, 0, 0] := by
  rw [show D2M8K2.u13461 = KTree.node D2M8K2.t13468 (nat_lit 29256028) (nat_lit 2535959085) (nat_lit 0) D2M8K2.t13469 from rfl, totK_node, tot13468, tot13469]
  decide +kernel

theorem arows13462 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13462 = true := by
  rw [show D2M8K2.u13462 = KTree.node D2M8K2.t13470 (nat_lit 29280344) (nat_lit 3849273495) (nat_lit 0) D2M8K2.t13471 from rfl, allE_node, rows13470, irow13462, rows13471]
  all_goals rfl

theorem atot13462 : totK PD2M8K2 D2M8K2.u13462 = [0, 0, 321239111555, 892044713554, 488189641883, 33565189122, 0, 0] := by
  rw [show D2M8K2.u13462 = KTree.node D2M8K2.t13470 (nat_lit 29280344) (nat_lit 3849273495) (nat_lit 0) D2M8K2.t13471 from rfl, totK_node, tot13470, tot13471]
  decide +kernel

theorem arows13467 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13467 = true := by
  rw [show D2M8K2.u13467 = KTree.node D2M8K2.t13472 (nat_lit 29282192) (nat_lit 3788156863) (nat_lit 0) D2M8K2.t13473 from rfl, allE_node, rows13472, irow13467, rows13473]
  all_goals rfl

theorem atot13467 : totK PD2M8K2 D2M8K2.u13467 = [0, 0, 144171881247, 685843625195, 821631574923, 133076856610, 1326647619, 0] := by
  rw [show D2M8K2.u13467 = KTree.node D2M8K2.t13472 (nat_lit 29282192) (nat_lit 3788156863) (nat_lit 0) D2M8K2.t13473 from rfl, totK_node, tot13472, tot13473]
  decide +kernel

theorem arows13468 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13468 = true := by
  rw [show D2M8K2.u13468 = KTree.node D2M8K2.t13474 (nat_lit 29283924) (nat_lit 2980128888) (nat_lit 0) D2M8K2.t13475 from rfl, allE_node, rows13474, irow13468, rows13475]
  all_goals rfl

theorem atot13468 : totK PD2M8K2 D2M8K2.u13468 = [0, 0, 276551558408, 831300570715, 572860827845, 100566773094, 10368174490, 0] := by
  rw [show D2M8K2.u13468 = KTree.node D2M8K2.t13474 (nat_lit 29283924) (nat_lit 2980128888) (nat_lit 0) D2M8K2.t13475 from rfl, totK_node, tot13474, tot13475]
  decide +kernel

theorem arows13470 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13470 = true := by
  rw [show D2M8K2.u13470 = KTree.node D2M8K2.t13476 (nat_lit 29285550) (nat_lit 3817156449) (nat_lit 0) D2M8K2.t13477 from rfl, allE_node, rows13476, irow13470, rows13477]
  all_goals rfl

theorem atot13470 : totK PD2M8K2 D2M8K2.u13470 = [0, 0, 83397781031, 507572882078, 842333778034, 321983636580, 13342948984, 0] := by
  rw [show D2M8K2.u13470 = KTree.node D2M8K2.t13476 (nat_lit 29285550) (nat_lit 3817156449) (nat_lit 0) D2M8K2.t13477 from rfl, totK_node, tot13476, tot13477]
  decide +kernel

theorem arows13471 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13471 = true := by
  rw [show D2M8K2.u13471 = KTree.node D2M8K2.t13478 (nat_lit 29286933) (nat_lit 1461484267) (nat_lit 0) D2M8K2.t13479 from rfl, allE_node, rows13478, irow13471, rows13479]
  all_goals rfl

theorem atot13471 : totK PD2M8K2 D2M8K2.u13471 = [0, 0, 333189766300, 897213717777, 526417865994, 40648998936, 0, 0] := by
  rw [show D2M8K2.u13471 = KTree.node D2M8K2.t13478 (nat_lit 29286933) (nat_lit 1461484267) (nat_lit 0) D2M8K2.t13479 from rfl, totK_node, tot13478, tot13479]
  decide +kernel

theorem arows13474 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13474 = true := by
  rw [show D2M8K2.u13474 = KTree.node D2M8K2.t13480 (nat_lit 29288702) (nat_lit 2310122502) (nat_lit 0) D2M8K2.t13481 from rfl, allE_node, rows13480, irow13474, rows13481]
  all_goals rfl

theorem atot13474 : totK PD2M8K2 D2M8K2.u13474 = [0, 0, 83423316472, 530070932440, 849359963554, 252992505357, 12909266092, 0] := by
  rw [show D2M8K2.u13474 = KTree.node D2M8K2.t13480 (nat_lit 29288702) (nat_lit 2310122502) (nat_lit 0) D2M8K2.t13481 from rfl, totK_node, tot13480, tot13481]
  decide +kernel

theorem arows13475 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13475 = true := by
  rw [show D2M8K2.u13475 = KTree.node D2M8K2.t13482 (nat_lit 29290686) (nat_lit 4064500791) (nat_lit 0) D2M8K2.t13483 from rfl, allE_node, rows13482, irow13475, rows13483]
  all_goals rfl

theorem atot13475 : totK PD2M8K2 D2M8K2.u13475 = [0, 0, 333358612823, 913129047090, 517705943825, 35845027976, 0, 0] := by
  rw [show D2M8K2.u13475 = KTree.node D2M8K2.t13482 (nat_lit 29290686) (nat_lit 4064500791) (nat_lit 0) D2M8K2.t13483 from rfl, totK_node, tot13482, tot13483]
  decide +kernel

theorem arows13477 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13477 = true := by
  rw [show D2M8K2.u13477 = KTree.node D2M8K2.t13484 (nat_lit 29292428) (nat_lit 3172335785) (nat_lit 0) D2M8K2.t13485 from rfl, allE_node, rows13484, irow13477, rows13485]
  all_goals rfl

theorem atot13477 : totK PD2M8K2 D2M8K2.u13477 = [0, 0, 86252406291, 527301210520, 852477998506, 265291945701, 13110073960, 0] := by
  rw [show D2M8K2.u13477 = KTree.node D2M8K2.t13484 (nat_lit 29292428) (nat_lit 3172335785) (nat_lit 0) D2M8K2.t13485 from rfl, totK_node, tot13484, tot13485]
  decide +kernel

theorem arows13478 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13478 = true := by
  rw [show D2M8K2.u13478 = KTree.node D2M8K2.t13486 (nat_lit 29293803) (nat_lit 3720749607) (nat_lit 0) D2M8K2.t13487 from rfl, allE_node, rows13486, irow13478, rows13487]
  all_goals rfl

theorem atot13478 : totK PD2M8K2 D2M8K2.u13478 = [0, 0, 356582788437, 924939099582, 505756468296, 39068259407, 0, 0] := by
  rw [show D2M8K2.u13478 = KTree.node D2M8K2.t13486 (nat_lit 29293803) (nat_lit 3720749607) (nat_lit 0) D2M8K2.t13487 from rfl, totK_node, tot13486, tot13487]
  decide +kernel

theorem arows13482 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13482 = true := by
  rw [show D2M8K2.u13482 = KTree.node D2M8K2.t13488 (nat_lit 29295482) (nat_lit 3847365183) (nat_lit 0) D2M8K2.t13489 from rfl, allE_node, rows13488, irow13482, rows13489]
  all_goals rfl

theorem atot13482 : totK PD2M8K2 D2M8K2.u13482 = [0, 0, 0, 581596087333, 999653164764, 219337077591, 4980514959, 0] := by
  rw [show D2M8K2.u13482 = KTree.node D2M8K2.t13488 (nat_lit 29295482) (nat_lit 3847365183) (nat_lit 0) D2M8K2.t13489 from rfl, totK_node, tot13488, tot13489]
  decide +kernel

theorem arows13483 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13483 = true := by
  rw [show D2M8K2.u13483 = KTree.node D2M8K2.t13490 (nat_lit 29301050) (nat_lit 3741070196) (nat_lit 0) D2M8K2.t13491 from rfl, allE_node, rows13490, irow13483, rows13491]
  all_goals rfl

theorem atot13483 : totK PD2M8K2 D2M8K2.u13483 = [0, 0, 0, 316958119934, 918575440649, 435896270557, 29024442026, 0] := by
  rw [show D2M8K2.u13483 = KTree.node D2M8K2.t13490 (nat_lit 29301050) (nat_lit 3741070196) (nat_lit 0) D2M8K2.t13491 from rfl, totK_node, tot13490, tot13491]
  decide +kernel

theorem arows13485 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13485 = true := by
  rw [show D2M8K2.u13485 = KTree.node D2M8K2.t13492 (nat_lit 29303146) (nat_lit 3658848478) (nat_lit 0) D2M8K2.t13493 from rfl, allE_node, rows13492, irow13485, rows13493]
  all_goals rfl

theorem atot13485 : totK PD2M8K2 D2M8K2.u13485 = [0, 0, 0, 176589460606, 770822463504, 675302830235, 99272276814, 1138244013] := by
  rw [show D2M8K2.u13485 = KTree.node D2M8K2.t13492 (nat_lit 29303146) (nat_lit 3658848478) (nat_lit 0) D2M8K2.t13493 from rfl, totK_node, tot13492, tot13493]
  decide +kernel

theorem arows13486 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13486 = true := by
  rw [show D2M8K2.u13486 = KTree.node D2M8K2.t13494 (nat_lit 29304916) (nat_lit 3997784073) (nat_lit 0) D2M8K2.t13495 from rfl, allE_node, rows13494, irow13486, rows13495]
  all_goals rfl

theorem atot13486 : totK PD2M8K2 D2M8K2.u13486 = [0, 0, 0, 411572108255, 956600167252, 381939736054, 17919718364, 0] := by
  rw [show D2M8K2.u13486 = KTree.node D2M8K2.t13494 (nat_lit 29304916) (nat_lit 3997784073) (nat_lit 0) D2M8K2.t13495 from rfl, totK_node, tot13494, tot13495]
  decide +kernel

theorem arows13489 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13489 = true := by
  rw [show D2M8K2.u13489 = KTree.node D2M8K2.t13496 (nat_lit 29308350) (nat_lit 2232948121) (nat_lit 0) D2M8K2.t13497 from rfl, allE_node, rows13496, irow13489, rows13497]
  all_goals rfl

theorem atot13489 : totK PD2M8K2 D2M8K2.u13489 = [0, 0, 0, 404724903441, 948027783094, 389388833979, 23135952166, 0] := by
  rw [show D2M8K2.u13489 = KTree.node D2M8K2.t13496 (nat_lit 29308350) (nat_lit 2232948121) (nat_lit 0) D2M8K2.t13497 from rfl, totK_node, tot13496, tot13497]
  decide +kernel

theorem arows13490 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13490 = true := by
  rw [show D2M8K2.u13490 = KTree.node D2M8K2.t13498 (nat_lit 29311802) (nat_lit 4184607552) (nat_lit 0) D2M8K2.t13499 from rfl, allE_node, rows13498, irow13490, rows13499]
  all_goals rfl

theorem atot13490 : totK PD2M8K2 D2M8K2.u13490 = [0, 0, 0, 416017010351, 940318714625, 391569639524, 26748926769, 0] := by
  rw [show D2M8K2.u13490 = KTree.node D2M8K2.t13498 (nat_lit 29311802) (nat_lit 4184607552) (nat_lit 0) D2M8K2.t13499 from rfl, totK_node, tot13498, tot13499]
  decide +kernel

theorem arows13492 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13492 = true := by
  rw [show D2M8K2.u13492 = KTree.node D2M8K2.t13500 (nat_lit 29314923) (nat_lit 2350274169) (nat_lit 0) D2M8K2.t13501 from rfl, allE_node, rows13500, irow13492, rows13501]
  all_goals rfl

theorem atot13492 : totK PD2M8K2 D2M8K2.u13492 = [0, 0, 0, 264274367161, 809714194454, 587177545404, 86987191319, 1095107716] := by
  rw [show D2M8K2.u13492 = KTree.node D2M8K2.t13500 (nat_lit 29314923) (nat_lit 2350274169) (nat_lit 0) D2M8K2.t13501 from rfl, totK_node, tot13500, tot13501]
  decide +kernel

theorem arows13493 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13493 = true := by
  rw [show D2M8K2.u13493 = KTree.node D2M8K2.t13502 (nat_lit 29316897) (nat_lit 1833548277) (nat_lit 0) D2M8K2.t13503 from rfl, allE_node, rows13502, irow13493, rows13503]
  all_goals rfl

theorem atot13493 : totK PD2M8K2 D2M8K2.u13493 = [186677387228, 459373490871, 202050743940, 9852138406, 302510027739, 493671869279, 122920430206, 3882006667] := by
  rw [show D2M8K2.u13493 = KTree.node D2M8K2.t13502 (nat_lit 29316897) (nat_lit 1833548277) (nat_lit 0) D2M8K2.t13503 from rfl, totK_node, tot13502, tot13503]
  decide +kernel

theorem arows13499 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13499 = true := by
  rw [show D2M8K2.u13499 = KTree.node D2M8K2.t13504 (nat_lit 29861318) (nat_lit 3297514726) (nat_lit 0) D2M8K2.t13505 from rfl, allE_node, rows13504, irow13499, rows13505]
  all_goals rfl

theorem atot13499 : totK PD2M8K2 D2M8K2.u13499 = [255775256361, 808850825985, 642265873208, 105322300753, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u13499 = KTree.node D2M8K2.t13504 (nat_lit 29861318) (nat_lit 3297514726) (nat_lit 0) D2M8K2.t13505 from rfl, totK_node, tot13504, tot13505]
  decide +kernel

theorem arows13500 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13500 = true := by
  rw [show D2M8K2.u13500 = KTree.node D2M8K2.t13506 (nat_lit 29866817) (nat_lit 2222245322) (nat_lit 0) D2M8K2.t13507 from rfl, allE_node, rows13506, irow13500, rows13507]
  all_goals rfl

theorem atot13500 : totK PD2M8K2 D2M8K2.u13500 = [235324397054, 810479873180, 700660005158, 81125054169, 0, 0, 0, 0] := by
  rw [show D2M8K2.u13500 = KTree.node D2M8K2.t13506 (nat_lit 29866817) (nat_lit 2222245322) (nat_lit 0) D2M8K2.t13507 from rfl, totK_node, tot13506, tot13507]
  decide +kernel

theorem arows13502 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13502 = true := by
  rw [show D2M8K2.u13502 = KTree.node D2M8K2.t13508 (nat_lit 29868340) (nat_lit 3758356247) (nat_lit 0) D2M8K2.t13509 from rfl, allE_node, rows13508, irow13502, rows13509]
  all_goals rfl

theorem atot13502 : totK PD2M8K2 D2M8K2.u13502 = [177347542369, 757813590918, 724367622056, 117833403159, 1164319620, 0, 0, 0] := by
  rw [show D2M8K2.u13502 = KTree.node D2M8K2.t13508 (nat_lit 29868340) (nat_lit 3758356247) (nat_lit 0) D2M8K2.t13509 from rfl, totK_node, tot13508, tot13509]
  decide +kernel

theorem arows13503 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13503 = true := by
  rw [show D2M8K2.u13503 = KTree.node D2M8K2.t13510 (nat_lit 29870044) (nat_lit 3927222369) (nat_lit 0) D2M8K2.t13511 from rfl, allE_node, rows13510, irow13503, rows13511]
  all_goals rfl

theorem atot13503 : totK PD2M8K2 D2M8K2.u13503 = [190466380195, 646297681246, 706227475394, 214243573917, 11885407614, 0, 0, 0] := by
  rw [show D2M8K2.u13503 = KTree.node D2M8K2.t13510 (nat_lit 29870044) (nat_lit 3927222369) (nat_lit 0) D2M8K2.t13511 from rfl, totK_node, tot13510, tot13511]
  decide +kernel

theorem arows13506 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13506 = true := by
  rw [show D2M8K2.u13506 = KTree.node D2M8K2.t13512 (nat_lit 29871708) (nat_lit 3108171929) (nat_lit 0) D2M8K2.t13513 from rfl, allE_node, rows13512, irow13506, rows13513]
  all_goals rfl

theorem atot13506 : totK PD2M8K2 D2M8K2.u13506 = [226378773154, 775367871770, 672306819595, 110982662645, 1198073392, 0, 0, 0] := by
  rw [show D2M8K2.u13506 = KTree.node D2M8K2.t13512 (nat_lit 29871708) (nat_lit 3108171929) (nat_lit 0) D2M8K2.t13513 from rfl, totK_node, tot13512, tot13513]
  decide +kernel

theorem arows13507 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13507 = true := by
  rw [show D2M8K2.u13507 = KTree.node D2M8K2.t13514 (nat_lit 29873407) (nat_lit 2300529621) (nat_lit 0) D2M8K2.t13515 from rfl, allE_node, rows13514, irow13507, rows13515]
  all_goals rfl

theorem atot13507 : totK PD2M8K2 D2M8K2.u13507 = [156361785850, 626241164219, 740722839556, 223133600962, 12052611869, 0, 0, 0] := by
  rw [show D2M8K2.u13507 = KTree.node D2M8K2.t13514 (nat_lit 29873407) (nat_lit 2300529621) (nat_lit 0) D2M8K2.t13515 from rfl, totK_node, tot13514, tot13515]
  decide +kernel

theorem arows13509 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13509 = true := by
  rw [show D2M8K2.u13509 = KTree.node D2M8K2.t13516 (nat_lit 29874851) (nat_lit 1165073085) (nat_lit 0) D2M8K2.t13517 from rfl, allE_node, rows13516, irow13509, rows13517]
  all_goals rfl

theorem atot13509 : totK PD2M8K2 D2M8K2.u13509 = [241301552354, 794153103166, 639373317566, 87073870343, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u13509 = KTree.node D2M8K2.t13516 (nat_lit 29874851) (nat_lit 1165073085) (nat_lit 0) D2M8K2.t13517 from rfl, totK_node, tot13516, tot13517]
  decide +kernel

theorem arows13510 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13510 = true := by
  rw [show D2M8K2.u13510 = KTree.node D2M8K2.t13518 (nat_lit 29877176) (nat_lit 3353144497) (nat_lit 0) D2M8K2.t13519 from rfl, allE_node, rows13518, irow13510, rows13519]
  all_goals rfl

theorem atot13510 : totK PD2M8K2 D2M8K2.u13510 = [225390261971, 742952426949, 687262985167, 143213154160, 3884009855, 0, 0, 0] := by
  rw [show D2M8K2.u13510 = KTree.node D2M8K2.t13518 (nat_lit 29877176) (nat_lit 3353144497) (nat_lit 0) D2M8K2.t13519 from rfl, totK_node, tot13518, tot13519]
  decide +kernel

theorem arows13514 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13514 = true := by
  rw [show D2M8K2.u13514 = KTree.node D2M8K2.t13520 (nat_lit 29878685) (nat_lit 2292200598) (nat_lit 0) D2M8K2.t13521 from rfl, allE_node, rows13520, irow13514, rows13521]
  all_goals rfl

theorem atot13514 : totK PD2M8K2 D2M8K2.u13514 = [198165556517, 763781561881, 723789826592, 125767191074, 1268739303, 0, 0, 0] := by
  rw [show D2M8K2.u13514 = KTree.node D2M8K2.t13520 (nat_lit 29878685) (nat_lit 2292200598) (nat_lit 0) D2M8K2.t13521 from rfl, totK_node, tot13520, tot13521]
  decide +kernel

theorem arows13515 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13515 = true := by
  rw [show D2M8K2.u13515 = KTree.node D2M8K2.t13522 (nat_lit 29880358) (nat_lit 3842747175) (nat_lit 0) D2M8K2.t13523 from rfl, allE_node, rows13522, irow13515, rows13523]
  all_goals rfl

theorem atot13515 : totK PD2M8K2 D2M8K2.u13515 = [0, 397375964825, 953678104001, 406198947375, 22149860293, 0, 0, 0] := by
  rw [show D2M8K2.u13515 = KTree.node D2M8K2.t13522 (nat_lit 29880358) (nat_lit 3842747175) (nat_lit 0) D2M8K2.t13523 from rfl, totK_node, tot13522, tot13523]
  decide +kernel

theorem arows13517 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13517 = true := by
  rw [show D2M8K2.u13517 = KTree.node D2M8K2.t13524 (nat_lit 29881829) (nat_lit 2316145649) (nat_lit 0) D2M8K2.t13525 from rfl, allE_node, rows13524, irow13517, rows13525]
  all_goals rfl

theorem atot13517 : totK PD2M8K2 D2M8K2.u13517 = [0, 279459591355, 877199109323, 545628820448, 50271802712, 0, 0, 0] := by
  rw [show D2M8K2.u13517 = KTree.node D2M8K2.t13524 (nat_lit 29881829) (nat_lit 2316145649) (nat_lit 0) D2M8K2.t13525 from rfl, totK_node, tot13524, tot13525]
  decide +kernel

theorem arows13518 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13518 = true := by
  rw [show D2M8K2.u13518 = KTree.node D2M8K2.t13526 (nat_lit 29883804) (nat_lit 3171186419) (nat_lit 0) D2M8K2.t13527 from rfl, allE_node, rows13526, irow13518, rows13527]
  all_goals rfl

theorem atot13518 : totK PD2M8K2 D2M8K2.u13518 = [0, 175798146017, 763225310507, 694148396501, 118307900074, 1369150432, 0, 0] := by
  rw [show D2M8K2.u13518 = KTree.node D2M8K2.t13526 (nat_lit 29883804) (nat_lit 3171186419) (nat_lit 0) D2M8K2.t13527 from rfl, totK_node, tot13526, tot13527]
  decide +kernel

theorem arows13521 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13521 = true := by
  rw [show D2M8K2.u13521 = KTree.node D2M8K2.t13528 (nat_lit 29888972) (nat_lit 2301073810) (nat_lit 0) D2M8K2.t13529 from rfl, allE_node, rows13528, irow13521, rows13529]
  all_goals rfl

theorem atot13521 : totK PD2M8K2 D2M8K2.u13521 = [0, 385762092776, 941284388761, 425043709896, 22421051990, 0, 0, 0] := by
  rw [show D2M8K2.u13521 = KTree.node D2M8K2.t13528 (nat_lit 29888972) (nat_lit 2301073810) (nat_lit 0) D2M8K2.t13529 from rfl, totK_node, tot13528, tot13529]
  decide +kernel

theorem arows13522 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13522 = true := by
  rw [show D2M8K2.u13522 = KTree.node D2M8K2.t13530 (nat_lit 29892253) (nat_lit 1077684915) (nat_lit 0) D2M8K2.t13531 from rfl, allE_node, rows13530, irow13522, rows13531]
  all_goals rfl

theorem atot13522 : totK PD2M8K2 D2M8K2.u13522 = [0, 353082879809, 928896867354, 465030218676, 26644536935, 0, 0, 0] := by
  rw [show D2M8K2.u13522 = KTree.node D2M8K2.t13530 (nat_lit 29892253) (nat_lit 1077684915) (nat_lit 0) D2M8K2.t13531 from rfl, totK_node, tot13530, tot13531]
  decide +kernel

theorem arows13524 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13524 = true := by
  rw [show D2M8K2.u13524 = KTree.node D2M8K2.t13532 (nat_lit 29895360) (nat_lit 3512258599) (nat_lit 0) D2M8K2.t13533 from rfl, allE_node, rows13532, irow13524, rows13533]
  all_goals rfl

theorem atot13524 : totK PD2M8K2 D2M8K2.u13524 = [0, 381693650001, 930898846878, 407914507505, 22161131776, 0, 0, 0] := by
  rw [show D2M8K2.u13524 = KTree.node D2M8K2.t13532 (nat_lit 29895360) (nat_lit 3512258599) (nat_lit 0) D2M8K2.t13533 from rfl, totK_node, tot13532, tot13533]
  decide +kernel

theorem arows13525 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13525 = true := by
  rw [show D2M8K2.u13525 = KTree.node D2M8K2.t13534 (nat_lit 29898634) (nat_lit 3946046732) (nat_lit 0) D2M8K2.t13535 from rfl, allE_node, rows13534, irow13525, rows13535]
  all_goals rfl

theorem atot13525 : totK PD2M8K2 D2M8K2.u13525 = [0, 346586936019, 954168528830, 481372179514, 21111913661, 0, 0, 0] := by
  rw [show D2M8K2.u13525 = KTree.node D2M8K2.t13534 (nat_lit 29898634) (nat_lit 3946046732) (nat_lit 0) D2M8K2.t13535 from rfl, totK_node, tot13534, tot13535]
  decide +kernel

theorem arows13530 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13530 = true := by
  rw [show D2M8K2.u13530 = KTree.node D2M8K2.t13536 (nat_lit 29943635) (nat_lit 2933783805) (nat_lit 0) D2M8K2.t13537 from rfl, allE_node, rows13536, irow13530, rows13537]
  all_goals rfl

theorem atot13530 : totK PD2M8K2 D2M8K2.u13530 = [383300556192, 911215136939, 425287249345, 59552569516, 8621106361, 0, 0, 0] := by
  rw [show D2M8K2.u13530 = KTree.node D2M8K2.t13536 (nat_lit 29943635) (nat_lit 2933783805) (nat_lit 0) D2M8K2.t13537 from rfl, totK_node, tot13536, tot13537]
  decide +kernel

theorem arows13531 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13531 = true := by
  rw [show D2M8K2.u13531 = KTree.node D2M8K2.t13538 (nat_lit 29945198) (nat_lit 3090315912) (nat_lit 0) D2M8K2.t13539 from rfl, allE_node, rows13538, irow13531, rows13539]
  all_goals rfl

theorem atot13531 : totK PD2M8K2 D2M8K2.u13531 = [106370415925, 670923940054, 872160456814, 153542597383, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u13531 = KTree.node D2M8K2.t13538 (nat_lit 29945198) (nat_lit 3090315912) (nat_lit 0) D2M8K2.t13539 from rfl, totK_node, tot13538, tot13539]
  decide +kernel

theorem arows13533 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13533 = true := by
  rw [show D2M8K2.u13533 = KTree.node D2M8K2.t13540 (nat_lit 29947494) (nat_lit 3110802912) (nat_lit 0) D2M8K2.t13541 from rfl, allE_node, rows13540, irow13533, rows13541]
  all_goals rfl

theorem atot13533 : totK PD2M8K2 D2M8K2.u13533 = [260862140786, 843395162432, 644404652928, 98485900067, 5319205844, 0, 0, 0] := by
  rw [show D2M8K2.u13533 = KTree.node D2M8K2.t13540 (nat_lit 29947494) (nat_lit 3110802912) (nat_lit 0) D2M8K2.t13541 from rfl, totK_node, tot13540, tot13541]
  decide +kernel

theorem arows13534 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13534 = true := by
  rw [show D2M8K2.u13534 = KTree.node D2M8K2.t13542 (nat_lit 29949368) (nat_lit 3920478169) (nat_lit 0) D2M8K2.t13543 from rfl, allE_node, rows13542, irow13534, rows13543]
  all_goals rfl

theorem atot13534 : totK PD2M8K2 D2M8K2.u13534 = [121298973571, 503004665392, 769087080381, 388805058715, 26436852314, 0, 0, 0] := by
  rw [show D2M8K2.u13534 = KTree.node D2M8K2.t13542 (nat_lit 29949368) (nat_lit 3920478169) (nat_lit 0) D2M8K2.t13543 from rfl, totK_node, tot13542, tot13543]
  decide +kernel

theorem arows13537 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13537 = true := by
  rw [show D2M8K2.u13537 = KTree.node D2M8K2.t13544 (nat_lit 29950882) (nat_lit 3171434965) (nat_lit 0) D2M8K2.t13545 from rfl, allE_node, rows13544, irow13537, rows13545]
  all_goals rfl

theorem atot13537 : totK PD2M8K2 D2M8K2.u13537 = [312146149977, 898366707217, 557476456348, 52065545361, 0, 0, 0, 0] := by
  rw [show D2M8K2.u13537 = KTree.node D2M8K2.t13544 (nat_lit 29950882) (nat_lit 3171434965) (nat_lit 0) D2M8K2.t13545 from rfl, totK_node, tot13544, tot13545]
  decide +kernel

theorem arows13538 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13538 = true := by
  rw [show D2M8K2.u13538 = KTree.node D2M8K2.t13546 (nat_lit 29952253) (nat_lit 976806065) (nat_lit 0) D2M8K2.t13547 from rfl, allE_node, rows13546, irow13538, rows13547]
  all_goals rfl

theorem atot13538 : totK PD2M8K2 D2M8K2.u13538 = [83994545022, 515002949550, 875784294860, 284842683814, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u13538 = KTree.node D2M8K2.t13546 (nat_lit 29952253) (nat_lit 976806065) (nat_lit 0) D2M8K2.t13547 from rfl, totK_node, tot13546, tot13547]
  decide +kernel

theorem arows13540 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13540 = true := by
  rw [show D2M8K2.u13540 = KTree.node D2M8K2.t13548 (nat_lit 29957427) (nat_lit 2568185769) (nat_lit 0) D2M8K2.t13549 from rfl, allE_node, rows13548, irow13540, rows13549]
  all_goals rfl

theorem atot13540 : totK PD2M8K2 D2M8K2.u13540 = [294753465016, 893928337374, 554126001866, 46383236994, 0, 0, 0, 0] := by
  rw [show D2M8K2.u13540 = KTree.node D2M8K2.t13548 (nat_lit 29957427) (nat_lit 2568185769) (nat_lit 0) D2M8K2.t13549 from rfl, totK_node, tot13548, tot13549]
  decide +kernel

theorem arows13541 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13541 = true := by
  rw [show D2M8K2.u13541 = KTree.node D2M8K2.t13550 (nat_lit 29959540) (nat_lit 3986318625) (nat_lit 0) D2M8K2.t13551 from rfl, allE_node, rows13550, irow13541, rows13551]
  all_goals rfl

theorem atot13541 : totK PD2M8K2 D2M8K2.u13541 = [166769743569, 657748970810, 774103677827, 184959385561, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u13541 = KTree.node D2M8K2.t13550 (nat_lit 29959540) (nat_lit 3986318625) (nat_lit 0) D2M8K2.t13551 from rfl, totK_node, tot13550, tot13551]
  decide +kernel

theorem arows13545 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13545 = true := by
  rw [show D2M8K2.u13545 = KTree.node D2M8K2.t13552 (nat_lit 29961088) (nat_lit 1732319357) (nat_lit 0) D2M8K2.t13553 from rfl, allE_node, rows13552, irow13545, rows13553]
  all_goals rfl

theorem atot13545 : totK PD2M8K2 D2M8K2.u13545 = [250158719299, 824112884295, 657233019456, 95669992001, 1268739303, 0, 0, 0] := by
  rw [show D2M8K2.u13545 = KTree.node D2M8K2.t13552 (nat_lit 29961088) (nat_lit 1732319357) (nat_lit 0) D2M8K2.t13553 from rfl, totK_node, tot13552, tot13553]
  decide +kernel

theorem arows13546 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13546 = true := by
  rw [show D2M8K2.u13546 = KTree.node D2M8K2.t13554 (nat_lit 29962801) (nat_lit 1480318570) (nat_lit 0) D2M8K2.t13555 from rfl, allE_node, rows13554, irow13546, rows13555]
  all_goals rfl

theorem atot13546 : totK PD2M8K2 D2M8K2.u13546 = [0, 420116337456, 955398153019, 393061250952, 22144019970, 0, 0, 0] := by
  rw [show D2M8K2.u13546 = KTree.node D2M8K2.t13554 (nat_lit 29962801) (nat_lit 1480318570) (nat_lit 0) D2M8K2.t13555 from rfl, totK_node, tot13554, tot13555]
  decide +kernel

theorem arows13548 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13548 = true := by
  rw [show D2M8K2.u13548 = KTree.node D2M8K2.t13556 (nat_lit 29964685) (nat_lit 1385917071) (nat_lit 0) D2M8K2.t13557 from rfl, allE_node, rows13556, irow13548, rows13557]
  all_goals rfl

theorem atot13548 : totK PD2M8K2 D2M8K2.u13548 = [0, 326892840146, 937044740932, 469659858306, 27018640446, 0, 0, 0] := by
  rw [show D2M8K2.u13548 = KTree.node D2M8K2.t13556 (nat_lit 29964685) (nat_lit 1385917071) (nat_lit 0) D2M8K2.t13557 from rfl, totK_node, tot13556, tot13557]
  decide +kernel

theorem arows13549 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13549 = true := by
  rw [show D2M8K2.u13549 = KTree.node D2M8K2.t13558 (nat_lit 29966694) (nat_lit 3563309908) (nat_lit 0) D2M8K2.t13559 from rfl, allE_node, rows13558, irow13549, rows13559]
  all_goals rfl

theorem atot13549 : totK PD2M8K2 D2M8K2.u13549 = [0, 177501810653, 731994898387, 749057406454, 113603629711, 1206465782, 0, 0] := by
  rw [show D2M8K2.u13549 = KTree.node D2M8K2.t13558 (nat_lit 29966694) (nat_lit 3563309908) (nat_lit 0) D2M8K2.t13559 from rfl, totK_node, tot13558, tot13559]
  decide +kernel

theorem arows13552 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13552 = true := by
  rw [show D2M8K2.u13552 = KTree.node D2M8K2.t13560 (nat_lit 29968686) (nat_lit 3666424926) (nat_lit 0) D2M8K2.t13561 from rfl, allE_node, rows13560, irow13552, rows13561]
  all_goals rfl

theorem atot13552 : totK PD2M8K2 D2M8K2.u13552 = [0, 341006413639, 932067522983, 504331964292, 37695707597, 0, 0, 0] := by
  rw [show D2M8K2.u13552 = KTree.node D2M8K2.t13560 (nat_lit 29968686) (nat_lit 3666424926) (nat_lit 0) D2M8K2.t13561 from rfl, totK_node, tot13560, tot13561]
  decide +kernel

theorem arows13553 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13553 = true := by
  rw [show D2M8K2.u13553 = KTree.node D2M8K2.t13562 (nat_lit 29971907) (nat_lit 2891196513) (nat_lit 0) D2M8K2.t13563 from rfl, allE_node, rows13562, irow13553, rows13563]
  all_goals rfl

theorem atot13553 : totK PD2M8K2 D2M8K2.u13553 = [0, 247537924858, 810486546851, 619621694299, 93242752499, 1162935789, 0, 0] := by
  rw [show D2M8K2.u13553 = KTree.node D2M8K2.t13562 (nat_lit 29971907) (nat_lit 2891196513) (nat_lit 0) D2M8K2.t13563 from rfl, totK_node, tot13562, tot13563]
  decide +kernel

theorem arows13555 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13555 = true := by
  rw [show D2M8K2.u13555 = KTree.node D2M8K2.t13564 (nat_lit 29973609) (nat_lit 1426804665) (nat_lit 0) D2M8K2.t13565 from rfl, allE_node, rows13564, irow13555, rows13565]
  all_goals rfl

theorem atot13555 : totK PD2M8K2 D2M8K2.u13555 = [0, 149685247596, 643820597939, 732155433576, 208661594337, 11853261585, 0, 0] := by
  rw [show D2M8K2.u13555 = KTree.node D2M8K2.t13564 (nat_lit 29973609) (nat_lit 1426804665) (nat_lit 0) D2M8K2.t13565 from rfl, totK_node, tot13564, tot13565]
  decide +kernel

theorem arows13556 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13556 = true := by
  rw [show D2M8K2.u13556 = KTree.node D2M8K2.t13566 (nat_lit 29978579) (nat_lit 1096576161) (nat_lit 0) D2M8K2.t13567 from rfl, allE_node, rows13566, irow13556, rows13567]
  all_goals rfl

theorem atot13556 : totK PD2M8K2 D2M8K2.u13556 = [0, 227289542443, 785473535058, 634439553184, 82990731996, 1021600638, 0, 0] := by
  rw [show D2M8K2.u13556 = KTree.node D2M8K2.t13566 (nat_lit 29978579) (nat_lit 1096576161) (nat_lit 0) D2M8K2.t13567 from rfl, totK_node, tot13566, tot13567]
  decide +kernel

theorem arows13564 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13564 = true := by
  rw [show D2M8K2.u13564 = KTree.node D2M8K2.t13568 (nat_lit 29980994) (nat_lit 3279461339) (nat_lit 0) D2M8K2.t13569 from rfl, allE_node, rows13568, irow13564, rows13569]
  all_goals rfl

theorem atot13564 : totK PD2M8K2 D2M8K2.u13564 = [0, 254567048849, 787044501126, 613915874180, 106043466391, 3552795014, 0, 0] := by
  rw [show D2M8K2.u13564 = KTree.node D2M8K2.t13568 (nat_lit 29980994) (nat_lit 3279461339) (nat_lit 0) D2M8K2.t13569 from rfl, totK_node, tot13568, tot13569]
  decide +kernel

theorem arows13565 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13565 = true := by
  rw [show D2M8K2.u13565 = KTree.node D2M8K2.t13570 (nat_lit 29984266) (nat_lit 3956385772) (nat_lit 0) D2M8K2.t13571 from rfl, allE_node, rows13570, irow13565, rows13571]
  all_goals rfl

theorem atot13565 : totK PD2M8K2 D2M8K2.u13565 = [220861315748, 656174018728, 642271635528, 265697432616, 21132842653, 0, 0, 0] := by
  rw [show D2M8K2.u13565 = KTree.node D2M8K2.t13570 (nat_lit 29984266) (nat_lit 3956385772) (nat_lit 0) D2M8K2.t13571 from rfl, totK_node, tot13570, tot13571]
  decide +kernel

theorem arows13567 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13567 = true := by
  rw [show D2M8K2.u13567 = KTree.node D2M8K2.t13572 (nat_lit 29985823) (nat_lit 2323947316) (nat_lit 0) D2M8K2.t13573 from rfl, allE_node, rows13572, irow13567, rows13573]
  all_goals rfl

theorem atot13567 : totK PD2M8K2 D2M8K2.u13567 = [195508859563, 765184926235, 699948247890, 116459086279, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u13567 = KTree.node D2M8K2.t13572 (nat_lit 29985823) (nat_lit 2323947316) (nat_lit 0) D2M8K2.t13573 from rfl, totK_node, tot13572, tot13573]
  decide +kernel

theorem arows13568 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13568 = true := by
  rw [show D2M8K2.u13568 = KTree.node D2M8K2.t13574 (nat_lit 29988177) (nat_lit 1760239441) (nat_lit 0) D2M8K2.t13575 from rfl, allE_node, rows13574, irow13568, rows13575]
  all_goals rfl

theorem atot13568 : totK PD2M8K2 D2M8K2.u13568 = [246020856858, 816773585375, 692654690780, 81165045294, 0, 0, 0, 0] := by
  rw [show D2M8K2.u13568 = KTree.node D2M8K2.t13574 (nat_lit 29988177) (nat_lit 1760239441) (nat_lit 0) D2M8K2.t13575 from rfl, totK_node, tot13574, tot13575]
  decide +kernel

theorem arows13571 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13571 = true := by
  rw [show D2M8K2.u13571 = KTree.node D2M8K2.t13576 (nat_lit 29989963) (nat_lit 1648238221) (nat_lit 0) D2M8K2.t13577 from rfl, allE_node, rows13576, irow13571, rows13577]
  all_goals rfl

theorem atot13571 : totK PD2M8K2 D2M8K2.u13571 = [85534938331, 539491386305, 831542670569, 348077040290, 26700035736, 0, 0, 0] := by
  rw [show D2M8K2.u13571 = KTree.node D2M8K2.t13576 (nat_lit 29989963) (nat_lit 1648238221) (nat_lit 0) D2M8K2.t13577 from rfl, totK_node, tot13576, tot13577]
  decide +kernel

theorem arows13572 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13572 = true := by
  rw [show D2M8K2.u13572 = KTree.node D2M8K2.t13578 (nat_lit 29995024) (nat_lit 2185592241) (nat_lit 0) D2M8K2.t13579 from rfl, allE_node, rows13578, irow13572, rows13579]
  all_goals rfl

theorem atot13572 : totK PD2M8K2 D2M8K2.u13572 = [323204405247, 809349290093, 553346910810, 135724775026, 6788293068, 0, 0, 0] := by
  rw [show D2M8K2.u13572 = KTree.node D2M8K2.t13578 (nat_lit 29995024) (nat_lit 2185592241) (nat_lit 0) D2M8K2.t13579 from rfl, totK_node, tot13578, tot13579]
  decide +kernel

theorem arows13574 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13574 = true := by
  rw [show D2M8K2.u13574 = KTree.node D2M8K2.t13580 (nat_lit 29996476) (nat_lit 3460311713) (nat_lit 0) D2M8K2.t13581 from rfl, allE_node, rows13580, irow13574, rows13581]
  all_goals rfl

theorem atot13574 : totK PD2M8K2 D2M8K2.u13574 = [114359324879, 640648333803, 815659057483, 217953482391, 9668735432, 0, 0, 0] := by
  rw [show D2M8K2.u13574 = KTree.node D2M8K2.t13580 (nat_lit 29996476) (nat_lit 3460311713) (nat_lit 0) D2M8K2.t13581 from rfl, totK_node, tot13580, tot13581]
  decide +kernel

theorem arows13575 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13575 = true := by
  rw [show D2M8K2.u13575 = KTree.node D2M8K2.t13582 (nat_lit 29998280) (nat_lit 3604008571) (nat_lit 0) D2M8K2.t13583 from rfl, allE_node, rows13582, irow13575, rows13583]
  all_goals rfl

theorem atot13575 : totK PD2M8K2 D2M8K2.u13575 = [264588431668, 759171668855, 626033061707, 129561188147, 3581949829, 0, 0, 0] := by
  rw [show D2M8K2.u13575 = KTree.node D2M8K2.t13582 (nat_lit 29998280) (nat_lit 3604008571) (nat_lit 0) D2M8K2.t13583 from rfl, totK_node, tot13582, tot13583]
  decide +kernel

theorem arows13579 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13579 = true := by
  rw [show D2M8K2.u13579 = KTree.node D2M8K2.t13584 (nat_lit 29999933) (nat_lit 1578411406) (nat_lit 0) D2M8K2.t13585 from rfl, allE_node, rows13584, irow13579, rows13585]
  all_goals rfl

theorem atot13579 : totK PD2M8K2 D2M8K2.u13579 = [114244887811, 713985325762, 821045925558, 128602749907, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u13579 = KTree.node D2M8K2.t13584 (nat_lit 29999933) (nat_lit 1578411406) (nat_lit 0) D2M8K2.t13585 from rfl, totK_node, tot13584, tot13585]
  decide +kernel

theorem arows13580 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13580 = true := by
  rw [show D2M8K2.u13580 = KTree.node D2M8K2.t13586 (nat_lit 30002015) (nat_lit 2035317213) (nat_lit 0) D2M8K2.t13587 from rfl, allE_node, rows13586, irow13580, rows13587]
  all_goals rfl

theorem atot13580 : totK PD2M8K2 D2M8K2.u13580 = [324723737991, 837377106388, 542518230092, 109722795712, 3884009855, 0, 0, 0] := by
  rw [show D2M8K2.u13580 = KTree.node D2M8K2.t13586 (nat_lit 30002015) (nat_lit 2035317213) (nat_lit 0) D2M8K2.t13587 from rfl, totK_node, tot13586, tot13587]
  decide +kernel

theorem arows13582 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13582 = true := by
  rw [show D2M8K2.u13582 = KTree.node D2M8K2.t13588 (nat_lit 30003580) (nat_lit 3678615999) (nat_lit 0) D2M8K2.t13589 from rfl, allE_node, rows13588, irow13582, rows13589]
  all_goals rfl

theorem atot13582 : totK PD2M8K2 D2M8K2.u13582 = [92274514042, 578436737943, 869320722063, 254890867572, 7078309226, 0, 0, 0] := by
  rw [show D2M8K2.u13582 = KTree.node D2M8K2.t13588 (nat_lit 30003580) (nat_lit 3678615999) (nat_lit 0) D2M8K2.t13589 from rfl, totK_node, tot13588, tot13589]
  decide +kernel

theorem arows13583 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13583 = true := by
  rw [show D2M8K2.u13583 = KTree.node D2M8K2.t13590 (nat_lit 30005239) (nat_lit 2224132896) (nat_lit 0) D2M8K2.t13591 from rfl, allE_node, rows13590, irow13583, rows13591]
  all_goals rfl

theorem atot13583 : totK PD2M8K2 D2M8K2.u13583 = [0, 380070233263, 943415806728, 425724760811, 26047338719, 0, 0, 0] := by
  rw [show D2M8K2.u13583 = KTree.node D2M8K2.t13590 (nat_lit 30005239) (nat_lit 2224132896) (nat_lit 0) D2M8K2.t13591 from rfl, totK_node, tot13590, tot13591]
  decide +kernel

theorem arows13586 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13586 = true := by
  rw [show D2M8K2.u13586 = KTree.node D2M8K2.t13592 (nat_lit 30006825) (nat_lit 1892005393) (nat_lit 0) D2M8K2.t13593 from rfl, allE_node, rows13592, irow13586, rows13593]
  all_goals rfl

theorem atot13586 : totK PD2M8K2 D2M8K2.u13586 = [0, 125457623494, 733047961101, 772060174280, 104355687205, 1239866073, 0, 0] := by
  rw [show D2M8K2.u13586 = KTree.node D2M8K2.t13592 (nat_lit 30006825) (nat_lit 1892005393) (nat_lit 0) D2M8K2.t13593 from rfl, totK_node, tot13592, tot13593]
  decide +kernel

theorem arows13587 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13587 = true := by
  rw [show D2M8K2.u13587 = KTree.node D2M8K2.t13594 (nat_lit 30009487) (nat_lit 2356516505) (nat_lit 0) D2M8K2.t13595 from rfl, allE_node, rows13594, irow13587, rows13595]
  all_goals rfl

theorem atot13587 : totK PD2M8K2 D2M8K2.u13587 = [0, 334467475833, 901800616461, 552819774978, 52560883733, 0, 0, 0] := by
  rw [show D2M8K2.u13587 = KTree.node D2M8K2.t13594 (nat_lit 30009487) (nat_lit 2356516505) (nat_lit 0) D2M8K2.t13595 from rfl, totK_node, tot13594, tot13595]
  decide +kernel

theorem arows13589 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13589 = true := by
  rw [show D2M8K2.u13589 = KTree.node D2M8K2.t13596 (nat_lit 30016255) (nat_lit 2374671215) (nat_lit 0) D2M8K2.t13597 from rfl, allE_node, rows13596, irow13589, rows13597]
  all_goals rfl

theorem atot13589 : totK PD2M8K2 D2M8K2.u13589 = [0, 376363592180, 941014809758, 455072211157, 32207300186, 0, 0, 0] := by
  rw [show D2M8K2.u13589 = KTree.node D2M8K2.t13596 (nat_lit 30016255) (nat_lit 2374671215) (nat_lit 0) D2M8K2.t13597 from rfl, totK_node, tot13596, tot13597]
  decide +kernel

theorem arows13590 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13590 = true := by
  rw [show D2M8K2.u13590 = KTree.node D2M8K2.t13598 (nat_lit 30017500) (nat_lit 3209401161) (nat_lit 0) D2M8K2.t13599 from rfl, allE_node, rows13598, irow13590, rows13599]
  all_goals rfl

theorem atot13590 : totK PD2M8K2 D2M8K2.u13590 = [0, 52139825349, 525821824215, 871205313458, 269578936121, 13105450397, 0, 0] := by
  rw [show D2M8K2.u13590 = KTree.node D2M8K2.t13598 (nat_lit 30017500) (nat_lit 3209401161) (nat_lit 0) D2M8K2.t13599 from rfl, totK_node, tot13598, tot13599]
  decide +kernel

theorem arows13595 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13595 = true := by
  rw [show D2M8K2.u13595 = KTree.node D2M8K2.t13600 (nat_lit 30019374) (nat_lit 3764174906) (nat_lit 0) D2M8K2.t13601 from rfl, allE_node, rows13600, irow13595, rows13601]
  all_goals rfl

theorem atot13595 : totK PD2M8K2 D2M8K2.u13595 = [0, 358079784368, 905916763792, 487025400257, 37297340526, 0, 0, 0] := by
  rw [show D2M8K2.u13595 = KTree.node D2M8K2.t13600 (nat_lit 30019374) (nat_lit 3764174906) (nat_lit 0) D2M8K2.t13601 from rfl, totK_node, tot13600, tot13601]
  decide +kernel

theorem arows13596 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13596 = true := by
  rw [show D2M8K2.u13596 = KTree.node D2M8K2.t13602 (nat_lit 30021413) (nat_lit 1425034989) (nat_lit 0) D2M8K2.t13603 from rfl, allE_node, rows13602, irow13596, rows13603]
  all_goals rfl

theorem atot13596 : totK PD2M8K2 D2M8K2.u13596 = [0, 104240125705, 639286263015, 800482472485, 161090207993, 4720618446, 0, 0] := by
  rw [show D2M8K2.u13596 = KTree.node D2M8K2.t13602 (nat_lit 30021413) (nat_lit 1425034989) (nat_lit 0) D2M8K2.t13603 from rfl, totK_node, tot13602, tot13603]
  decide +kernel

theorem arows13598 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13598 = true := by
  rw [show D2M8K2.u13598 = KTree.node D2M8K2.t13604 (nat_lit 30023141) (nat_lit 1820855382) (nat_lit 0) D2M8K2.t13605 from rfl, allE_node, rows13604, irow13598, rows13605]
  all_goals rfl

theorem atot13598 : totK PD2M8K2 D2M8K2.u13598 = [0, 330362521003, 916746386934, 538852612855, 42544488048, 0, 0, 0] := by
  rw [show D2M8K2.u13598 = KTree.node D2M8K2.t13604 (nat_lit 30023141) (nat_lit 1820855382) (nat_lit 0) D2M8K2.t13605 from rfl, totK_node, tot13604, tot13605]
  decide +kernel

theorem arows13599 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13599 = true := by
  rw [show D2M8K2.u13599 = KTree.node D2M8K2.t13606 (nat_lit 30026625) (nat_lit 1787520201) (nat_lit 0) D2M8K2.t13607 from rfl, allE_node, rows13606, irow13599, rows13607]
  all_goals rfl

theorem atot13599 : totK PD2M8K2 D2M8K2.u13599 = [397873363933, 949342514759, 420536407404, 22386190152, 0, 0, 0, 0] := by
  rw [show D2M8K2.u13599 = KTree.node D2M8K2.t13606 (nat_lit 30026625) (nat_lit 1787520201) (nat_lit 0) D2M8K2.t13607 from rfl, totK_node, tot13606, tot13607]
  decide +kernel

theorem arows13602 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13602 = true := by
  rw [show D2M8K2.u13602 = KTree.node D2M8K2.t13608 (nat_lit 30028320) (nat_lit 3719854113) (nat_lit 0) D2M8K2.t13609 from rfl, allE_node, rows13608, irow13602, rows13609]
  all_goals rfl

theorem atot13602 : totK PD2M8K2 D2M8K2.u13602 = [107931208169, 671523929181, 861960536707, 152126405583, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u13602 = KTree.node D2M8K2.t13608 (nat_lit 30028320) (nat_lit 3719854113) (nat_lit 0) D2M8K2.t13609 from rfl, totK_node, tot13608, tot13609]
  decide +kernel

theorem arows13603 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13603 = true := by
  rw [show D2M8K2.u13603 = KTree.node D2M8K2.t13610 (nat_lit 30033429) (nat_lit 1461484267) (nat_lit 0) D2M8K2.t13611 from rfl, allE_node, rows13610, irow13603, rows13611]
  all_goals rfl

theorem atot13603 : totK PD2M8K2 D2M8K2.u13603 = [314967342360, 902509448082, 542449698888, 43857708883, 0, 0, 0, 0] := by
  rw [show D2M8K2.u13603 = KTree.node D2M8K2.t13610 (nat_lit 30033429) (nat_lit 1461484267) (nat_lit 0) D2M8K2.t13611 from rfl, totK_node, tot13610, tot13611]
  decide +kernel

theorem arows13605 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13605 = true := by
  rw [show D2M8K2.u13605 = KTree.node D2M8K2.t13612 (nat_lit 30035191) (nat_lit 1203566987) (nat_lit 0) D2M8K2.t13613 from rfl, allE_node, rows13612, irow13605, rows13613]
  all_goals rfl

theorem atot13605 : totK PD2M8K2 D2M8K2.u13605 = [85190975889, 523757224741, 861397201592, 283319914896, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u13605 = KTree.node D2M8K2.t13612 (nat_lit 30035191) (nat_lit 1203566987) (nat_lit 0) D2M8K2.t13613 from rfl, totK_node, tot13612, tot13613]
  decide +kernel

theorem arows13606 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13606 = true := by
  rw [show D2M8K2.u13606 = KTree.node D2M8K2.t13614 (nat_lit 30037205) (nat_lit 1460143609) (nat_lit 0) D2M8K2.t13615 from rfl, allE_node, rows13614, irow13606, rows13615]
  all_goals rfl

theorem atot13606 : totK PD2M8K2 D2M8K2.u13606 = [315179504246, 907545415100, 541802630112, 44005980985, 0, 0, 0, 0] := by
  rw [show D2M8K2.u13606 = KTree.node D2M8K2.t13614 (nat_lit 30037205) (nat_lit 1460143609) (nat_lit 0) D2M8K2.t13615 from rfl, totK_node, tot13614, tot13615]
  decide +kernel

theorem arows13610 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13610 = true := by
  rw [show D2M8K2.u13610 = KTree.node D2M8K2.t13616 (nat_lit 30038940) (nat_lit 2714081611) (nat_lit 0) D2M8K2.t13617 from rfl, allE_node, rows13616, irow13610, rows13617]
  all_goals rfl

theorem atot13610 : totK PD2M8K2 D2M8K2.u13610 = [86654048599, 516741928089, 861879969594, 294921883123, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u13610 = KTree.node D2M8K2.t13616 (nat_lit 30038940) (nat_lit 2714081611) (nat_lit 0) D2M8K2.t13617 from rfl, totK_node, tot13616, tot13617]
  decide +kernel

theorem arows13611 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13611 = true := by
  rw [show D2M8K2.u13611 = KTree.node D2M8K2.t13618 (nat_lit 30040372) (nat_lit 3822117226) (nat_lit 0) D2M8K2.t13619 from rfl, allE_node, rows13618, irow13611, rows13619]
  all_goals rfl

theorem atot13611 : totK PD2M8K2 D2M8K2.u13611 = [336914695032, 928123742605, 499975686768, 37084267007, 0, 0, 0, 0] := by
  rw [show D2M8K2.u13611 = KTree.node D2M8K2.t13618 (nat_lit 30040372) (nat_lit 3822117226) (nat_lit 0) D2M8K2.t13619 from rfl, totK_node, tot13618, tot13619]
  decide +kernel

theorem arows13613 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13613 = true := by
  rw [show D2M8K2.u13613 = KTree.node D2M8K2.t13620 (nat_lit 30042190) (nat_lit 2897794061) (nat_lit 0) D2M8K2.t13621 from rfl, allE_node, rows13620, irow13613, rows13621]
  all_goals rfl

theorem atot13613 : totK PD2M8K2 D2M8K2.u13613 = [0, 508764775000, 1015551032933, 266416813111, 6350335412, 0, 0, 0] := by
  rw [show D2M8K2.u13613 = KTree.node D2M8K2.t13620 (nat_lit 30042190) (nat_lit 2897794061) (nat_lit 0) D2M8K2.t13621 from rfl, totK_node, tot13620, tot13621]
  decide +kernel

theorem arows13614 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13614 = true := by
  rw [show D2M8K2.u13614 = KTree.node D2M8K2.t13622 (nat_lit 30047594) (nat_lit 2974309393) (nat_lit 0) D2M8K2.t13623 from rfl, allE_node, rows13622, irow13614, rows13623]
  all_goals rfl

theorem atot13614 : totK PD2M8K2 D2M8K2.u13614 = [0, 328534603747, 919039521367, 468554935533, 32789939480, 0, 0, 0] := by
  rw [show D2M8K2.u13614 = KTree.node D2M8K2.t13622 (nat_lit 30047594) (nat_lit 2974309393) (nat_lit 0) D2M8K2.t13623 from rfl, totK_node, tot13622, tot13623]
  decide +kernel

theorem arows13617 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13617 = true := by
  rw [show D2M8K2.u13617 = KTree.node D2M8K2.t13624 (nat_lit 30049691) (nat_lit 2455977076) (nat_lit 0) D2M8K2.t13625 from rfl, allE_node, rows13624, irow13617, rows13625]
  all_goals rfl

theorem atot13617 : totK PD2M8K2 D2M8K2.u13617 = [0, 189119387589, 789006296420, 684742281837, 87999807143, 1138244013, 0, 0] := by
  rw [show D2M8K2.u13617 = KTree.node D2M8K2.t13624 (nat_lit 30049691) (nat_lit 2455977076) (nat_lit 0) D2M8K2.t13625 from rfl, totK_node, tot13624, tot13625]
  decide +kernel

theorem arows13618 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13618 = true := by
  rw [show D2M8K2.u13618 = KTree.node D2M8K2.t13626 (nat_lit 30054884) (nat_lit 2792831110) (nat_lit 0) D2M8K2.t13627 from rfl, allE_node, rows13626, irow13618, rows13627]
  all_goals rfl

theorem atot13618 : totK PD2M8K2 D2M8K2.u13618 = [0, 363022701512, 939212523551, 452976936026, 25790587952, 0, 0, 0] := by
  rw [show D2M8K2.u13618 = KTree.node D2M8K2.t13626 (nat_lit 30054884) (nat_lit 2792831110) (nat_lit 0) D2M8K2.t13627 from rfl, totK_node, tot13626, tot13627]
  decide +kernel

theorem arows13620 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13620 = true := by
  rw [show D2M8K2.u13620 = KTree.node D2M8K2.t13628 (nat_lit 30058238) (nat_lit 2971883083) (nat_lit 0) D2M8K2.t13629 from rfl, allE_node, rows13628, irow13620, rows13629]
  all_goals rfl

theorem atot13620 : totK PD2M8K2 D2M8K2.u13620 = [0, 387991571918, 950352230006, 430476953516, 18931416259, 0, 0, 0] := by
  rw [show D2M8K2.u13620 = KTree.node D2M8K2.t13628 (nat_lit 30058238) (nat_lit 2971883083) (nat_lit 0) D2M8K2.t13629 from rfl, totK_node, tot13628, tot13629]
  decide +kernel

theorem arows13621 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13621 = true := by
  rw [show D2M8K2.u13621 = KTree.node D2M8K2.t13630 (nat_lit 30061290) (nat_lit 3811028285) (nat_lit 0) D2M8K2.t13631 from rfl, allE_node, rows13630, irow13621, rows13631]
  all_goals rfl

theorem atot13621 : totK PD2M8K2 D2M8K2.u13621 = [0, 274396693311, 848313921754, 561083974999, 65555818840, 1095107716, 0, 0] := by
  rw [show D2M8K2.u13621 = KTree.node D2M8K2.t13630 (nat_lit 30061290) (nat_lit 3811028285) (nat_lit 0) D2M8K2.t13631 from rfl, totK_node, tot13630, tot13631]
  decide +kernel

theorem arows13627 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13627 = true := by
  rw [show D2M8K2.u13627 = KTree.node D2M8K2.t13632 (nat_lit 30063258) (nat_lit 3655979436) (nat_lit 0) D2M8K2.t13633 from rfl, allE_node, rows13632, irow13627, rows13633]
  all_goals rfl

theorem atot13627 : totK PD2M8K2 D2M8K2.u13627 = [176791677709, 383523406934, 443844622733, 606043138168, 155217064297, 3882006667, 0, 0] := by
  rw [show D2M8K2.u13627 = KTree.node D2M8K2.t13632 (nat_lit 30063258) (nat_lit 3655979436) (nat_lit 0) D2M8K2.t13633 from rfl, totK_node, tot13632, tot13633]
  decide +kernel

theorem arows13628 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13628 = true := by
  rw [show D2M8K2.u13628 = KTree.node D2M8K2.t13634 (nat_lit 30068593) (nat_lit 1414977894) (nat_lit 0) D2M8K2.t13635 from rfl, allE_node, rows13634, irow13628, rows13635]
  all_goals rfl

theorem atot13628 : totK PD2M8K2 D2M8K2.u13628 = [244973343078, 786601184963, 641294479334, 109438690238, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u13628 = KTree.node D2M8K2.t13634 (nat_lit 30068593) (nat_lit 1414977894) (nat_lit 0) D2M8K2.t13635 from rfl, totK_node, tot13634, tot13635]
  decide +kernel

theorem arows13630 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13630 = true := by
  rw [show D2M8K2.u13630 = KTree.node D2M8K2.t13636 (nat_lit 30070974) (nat_lit 3939396655) (nat_lit 0) D2M8K2.t13637 from rfl, allE_node, rows13636, irow13630, rows13637]
  all_goals rfl

theorem atot13630 : totK PD2M8K2 D2M8K2.u13630 = [181741072845, 776247663693, 788906258282, 96487000679, 0, 0, 0, 0] := by
  rw [show D2M8K2.u13630 = KTree.node D2M8K2.t13636 (nat_lit 30070974) (nat_lit 3939396655) (nat_lit 0) D2M8K2.t13637 from rfl, totK_node, tot13636, tot13637]
  decide +kernel

theorem arows13631 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13631 = true := by
  rw [show D2M8K2.u13631 = KTree.node D2M8K2.t13638 (nat_lit 30072711) (nat_lit 3639394546) (nat_lit 0) D2M8K2.t13639 from rfl, allE_node, rows13638, irow13631, rows13639]
  all_goals rfl

theorem atot13631 : totK PD2M8K2 D2M8K2.u13631 = [166877321919, 644636403573, 724091498474, 277218500127, 25092327913, 0, 0, 0] := by
  rw [show D2M8K2.u13631 = KTree.node D2M8K2.t13638 (nat_lit 30072711) (nat_lit 3639394546) (nat_lit 0) D2M8K2.t13639 from rfl, totK_node, tot13638, tot13639]
  decide +kernel

theorem arows13634 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13634 = true := by
  rw [show D2M8K2.u13634 = KTree.node D2M8K2.t13640 (nat_lit 30074205) (nat_lit 1372459875) (nat_lit 0) D2M8K2.t13641 from rfl, allE_node, rows13640, irow13634, rows13641]
  all_goals rfl

theorem atot13634 : totK PD2M8K2 D2M8K2.u13634 = [238842008168, 690251193267, 662065860673, 230508287620, 10703994771, 0, 0, 0] := by
  rw [show D2M8K2.u13634 = KTree.node D2M8K2.t13640 (nat_lit 30074205) (nat_lit 1372459875) (nat_lit 0) D2M8K2.t13641 from rfl, totK_node, tot13640, tot13641]
  decide +kernel

theorem arows13635 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13635 = true := by
  rw [show D2M8K2.u13635 = KTree.node D2M8K2.t13642 (nat_lit 30075731) (nat_lit 2881675544) (nat_lit 0) D2M8K2.t13643 from rfl, allE_node, rows13642, irow13635, rows13643]
  all_goals rfl

theorem atot13635 : totK PD2M8K2 D2M8K2.u13635 = [173943437419, 749951496994, 753451361983, 124380606332, 1164319620, 0, 0, 0] := by
  rw [show D2M8K2.u13635 = KTree.node D2M8K2.t13642 (nat_lit 30075731) (nat_lit 2881675544) (nat_lit 0) D2M8K2.t13643 from rfl, totK_node, tot13642, tot13643]
  decide +kernel

theorem arows13637 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13637 = true := by
  rw [show D2M8K2.u13637 = KTree.node D2M8K2.t13644 (nat_lit 30077626) (nat_lit 3785945449) (nat_lit 0) D2M8K2.t13645 from rfl, allE_node, rows13644, irow13637, rows13645]
  all_goals rfl

theorem atot13637 : totK PD2M8K2 D2M8K2.u13637 = [221945993450, 671582929038, 683706697742, 207263452307, 11879463720, 0, 0, 0] := by
  rw [show D2M8K2.u13637 = KTree.node D2M8K2.t13644 (nat_lit 30077626) (nat_lit 3785945449) (nat_lit 0) D2M8K2.t13645 from rfl, totK_node, tot13644, tot13645]
  decide +kernel

theorem arows13638 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13638 = true := by
  rw [show D2M8K2.u13638 = KTree.node D2M8K2.t13646 (nat_lit 30079152) (nat_lit 3678685636) (nat_lit 0) D2M8K2.t13647 from rfl, allE_node, rows13646, irow13638, rows13647]
  all_goals rfl

theorem atot13638 : totK PD2M8K2 D2M8K2.u13638 = [191083501060, 765279451247, 720444999568, 121206889568, 1198073392, 0, 0, 0] := by
  rw [show D2M8K2.u13638 = KTree.node D2M8K2.t13646 (nat_lit 30079152) (nat_lit 3678685636) (nat_lit 0) D2M8K2.t13647 from rfl, totK_node, tot13646, tot13647]
  decide +kernel

theorem arows13642 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13642 = true := by
  rw [show D2M8K2.u13642 = KTree.node D2M8K2.t13648 (nat_lit 30080869) (nat_lit 1358151366) (nat_lit 0) D2M8K2.t13649 from rfl, allE_node, rows13648, irow13642, rows13649]
  all_goals rfl

theorem atot13642 : totK PD2M8K2 D2M8K2.u13642 = [190740266346, 661809556076, 722088680677, 220539274229, 12045711471, 0, 0, 0] := by
  rw [show D2M8K2.u13642 = KTree.node D2M8K2.t13648 (nat_lit 30080869) (nat_lit 1358151366) (nat_lit 0) D2M8K2.t13649 from rfl, totK_node, tot13648, tot13649]
  decide +kernel

theorem arows13643 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13643 = true := by
  rw [show D2M8K2.u13643 = KTree.node D2M8K2.t13650 (nat_lit 30085950) (nat_lit 3891323600) (nat_lit 0) D2M8K2.t13651 from rfl, allE_node, rows13650, irow13643, rows13651]
  all_goals rfl

theorem atot13643 : totK PD2M8K2 D2M8K2.u13643 = [252059530312, 805264462796, 650896323175, 112884209835, 1268739303, 0, 0, 0] := by
  rw [show D2M8K2.u13643 = KTree.node D2M8K2.t13650 (nat_lit 30085950) (nat_lit 3891323600) (nat_lit 0) D2M8K2.t13651 from rfl, totK_node, tot13650, tot13651]
  decide +kernel

theorem arows13645 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13645 = true := by
  rw [show D2M8K2.u13645 = KTree.node D2M8K2.t13652 (nat_lit 30087312) (nat_lit 2832372174) (nat_lit 0) D2M8K2.t13653 from rfl, allE_node, rows13652, irow13645, rows13653]
  all_goals rfl

theorem atot13645 : totK PD2M8K2 D2M8K2.u13645 = [0, 406598228421, 963157530780, 397151308229, 22149860293, 0, 0, 0] := by
  rw [show D2M8K2.u13645 = KTree.node D2M8K2.t13652 (nat_lit 30087312) (nat_lit 2832372174) (nat_lit 0) D2M8K2.t13653 from rfl, totK_node, tot13652, tot13653]
  decide +kernel

theorem arows13646 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13646 = true := by
  rw [show D2M8K2.u13646 = KTree.node D2M8K2.t13654 (nat_lit 30089139) (nat_lit 2486961221) (nat_lit 0) D2M8K2.t13655 from rfl, allE_node, rows13654, irow13646, rows13655]
  all_goals rfl

theorem atot13646 : totK PD2M8K2 D2M8K2.u13646 = [0, 329034450531, 920470945377, 502162854803, 29605603907, 0, 0, 0] := by
  rw [show D2M8K2.u13646 = KTree.node D2M8K2.t13654 (nat_lit 30089139) (nat_lit 2486961221) (nat_lit 0) D2M8K2.t13655 from rfl, totK_node, tot13654, tot13655]
  decide +kernel

theorem arows13649 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13649 = true := by
  rw [show D2M8K2.u13649 = KTree.node D2M8K2.t13656 (nat_lit 30091138) (nat_lit 4066792849) (nat_lit 0) D2M8K2.t13657 from rfl, allE_node, rows13656, irow13649, rows13657]
  all_goals rfl

theorem atot13649 : totK PD2M8K2 D2M8K2.u13649 = [0, 173929479270, 714541040250, 800493153456, 122241378626, 1310285577, 0, 0] := by
  rw [show D2M8K2.u13649 = KTree.node D2M8K2.t13656 (nat_lit 30091138) (nat_lit 4066792849) (nat_lit 0) D2M8K2.t13657 from rfl, totK_node, tot13656, tot13657]
  decide +kernel

theorem arows13650 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13650 = true := by
  rw [show D2M8K2.u13650 = KTree.node D2M8K2.t13658 (nat_lit 30093026) (nat_lit 3991730768) (nat_lit 0) D2M8K2.t13659 from rfl, allE_node, rows13658, irow13650, rows13659]
  all_goals rfl

theorem atot13650 : totK PD2M8K2 D2M8K2.u13650 = [0, 339055594740, 926732008199, 522078905378, 41768734358, 0, 0, 0] := by
  rw [show D2M8K2.u13650 = KTree.node D2M8K2.t13658 (nat_lit 30093026) (nat_lit 3991730768) (nat_lit 0) D2M8K2.t13659 from rfl, totK_node, tot13658, tot13659]
  decide +kernel

theorem arows13652 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13652 = true := by
  rw [show D2M8K2.u13652 = KTree.node D2M8K2.t13660 (nat_lit 30096316) (nat_lit 3901800563) (nat_lit 0) D2M8K2.t13661 from rfl, allE_node, rows13660, irow13652, rows13661]
  all_goals rfl

theorem atot13652 : totK PD2M8K2 D2M8K2.u13652 = [0, 245558341129, 795675121418, 645168185003, 87157582185, 1075657031, 0, 0] := by
  rw [show D2M8K2.u13652 = KTree.node D2M8K2.t13660 (nat_lit 30096316) (nat_lit 3901800563) (nat_lit 0) D2M8K2.t13661 from rfl, totK_node, tot13660, tot13661]
  decide +kernel

theorem arows13653 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13653 = true := by
  rw [show D2M8K2.u13653 = KTree.node D2M8K2.t13662 (nat_lit 30098360) (nat_lit 2639784509) (nat_lit 0) D2M8K2.t13663 from rfl, allE_node, rows13662, irow13653, rows13663]
  all_goals rfl

theorem atot13653 : totK PD2M8K2 D2M8K2.u13653 = [0, 221286248404, 741161157912, 692648466520, 131282974751, 3804183361, 0, 0] := by
  rw [show D2M8K2.u13653 = KTree.node D2M8K2.t13662 (nat_lit 30098360) (nat_lit 2639784509) (nat_lit 0) D2M8K2.t13663 from rfl, totK_node, tot13662, tot13663]
  decide +kernel

theorem arows13658 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13658 = true := by
  rw [show D2M8K2.u13658 = KTree.node D2M8K2.t13664 (nat_lit 30099892) (nat_lit 3370489175) (nat_lit 0) D2M8K2.t13665 from rfl, allE_node, rows13664, irow13658, rows13665]
  all_goals rfl

theorem atot13658 : totK PD2M8K2 D2M8K2.u13658 = [0, 190103674078, 782222004396, 706674051940, 99218496519, 1107157161, 0, 0] := by
  rw [show D2M8K2.u13658 = KTree.node D2M8K2.t13664 (nat_lit 30099892) (nat_lit 3370489175) (nat_lit 0) D2M8K2.t13665 from rfl, totK_node, tot13664, tot13665]
  decide +kernel

theorem arows13659 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13659 = true := by
  rw [show D2M8K2.u13659 = KTree.node D2M8K2.t13666 (nat_lit 30105376) (nat_lit 2711213701) (nat_lit 0) D2M8K2.t13667 from rfl, allE_node, rows13666, irow13659, rows13667]
  all_goals rfl

theorem atot13659 : totK PD2M8K2 D2M8K2.u13659 = [0, 259962330792, 795022302959, 615309994272, 116117962996, 3824247485, 0, 0] := by
  rw [show D2M8K2.u13659 = KTree.node D2M8K2.t13666 (nat_lit 30105376) (nat_lit 2711213701) (nat_lit 0) D2M8K2.t13667 from rfl, totK_node, tot13666, tot13667]
  decide +kernel

theorem arows13661 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13661 = true := by
  rw [show D2M8K2.u13661 = KTree.node D2M8K2.t13668 (nat_lit 30106864) (nat_lit 3490515377) (nat_lit 0) D2M8K2.t13669 from rfl, allE_node, rows13668, irow13661, rows13669]
  all_goals rfl

theorem atot13661 : totK PD2M8K2 D2M8K2.u13661 = [0, 180939287263, 758537268524, 743393400958, 120269539449, 1242138600, 0, 0] := by
  rw [show D2M8K2.u13661 = KTree.node D2M8K2.t13668 (nat_lit 30106864) (nat_lit 3490515377) (nat_lit 0) D2M8K2.t13669 from rfl, totK_node, tot13668, tot13669]
  decide +kernel

theorem arows13662 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13662 = true := by
  rw [show D2M8K2.u13662 = KTree.node D2M8K2.t13670 (nat_lit 30108562) (nat_lit 4004561120) (nat_lit 0) D2M8K2.t13671 from rfl, allE_node, rows13670, irow13662, rows13671]
  all_goals rfl

theorem atot13662 : totK PD2M8K2 D2M8K2.u13662 = [0, 179733180668, 602620149464, 684404100934, 277399007738, 20509029466, 0, 0] := by
  rw [show D2M8K2.u13662 = KTree.node D2M8K2.t13670 (nat_lit 30108562) (nat_lit 4004561120) (nat_lit 0) D2M8K2.t13671 from rfl, totK_node, tot13670, tot13671]
  decide +kernel

theorem arows13665 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13665 = true := by
  rw [show D2M8K2.u13665 = KTree.node D2M8K2.t13672 (nat_lit 30110069) (nat_lit 2211537840) (nat_lit 0) D2M8K2.t13673 from rfl, allE_node, rows13672, irow13665, rows13673]
  all_goals rfl

theorem atot13665 : totK PD2M8K2 D2M8K2.u13665 = [0, 261773448770, 805189834414, 620752937076, 107159482841, 1369150432, 0, 0] := by
  rw [show D2M8K2.u13665 = KTree.node D2M8K2.t13672 (nat_lit 30110069) (nat_lit 2211537840) (nat_lit 0) D2M8K2.t13673 from rfl, totK_node, tot13672, tot13673]
  decide +kernel

theorem arows13666 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13666 = true := by
  rw [show D2M8K2.u13666 = KTree.node D2M8K2.t13674 (nat_lit 30111976) (nat_lit 3646961379) (nat_lit 0) D2M8K2.t13675 from rfl, allE_node, rows13674, irow13666, rows13675]
  all_goals rfl

theorem atot13666 : totK PD2M8K2 D2M8K2.u13666 = [0, 209216869345, 794541875514, 734198514216, 79103114797, 0, 0, 0] := by
  rw [show D2M8K2.u13666 = KTree.node D2M8K2.t13674 (nat_lit 30111976) (nat_lit 3646961379) (nat_lit 0) D2M8K2.t13675 from rfl, totK_node, tot13674, tot13675]
  decide +kernel

theorem arows13668 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13668 = true := by
  rw [show D2M8K2.u13668 = KTree.node D2M8K2.t13676 (nat_lit 30117103) (nat_lit 2340801188) (nat_lit 0) D2M8K2.t13677 from rfl, allE_node, rows13676, irow13668, rows13677]
  all_goals rfl

theorem atot13668 : totK PD2M8K2 D2M8K2.u13668 = [0, 205749399316, 777556129052, 688532070972, 99468015860, 1164319620, 0, 0] := by
  rw [show D2M8K2.u13668 = KTree.node D2M8K2.t13676 (nat_lit 30117103) (nat_lit 2340801188) (nat_lit 0) D2M8K2.t13677 from rfl, totK_node, tot13676, tot13677]
  decide +kernel

theorem arows13669 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13669 = true := by
  rw [show D2M8K2.u13669 = KTree.node D2M8K2.t13678 (nat_lit 30118822) (nat_lit 3841895814) (nat_lit 0) D2M8K2.t13679 from rfl, allE_node, rows13678, irow13669, rows13679]
  all_goals rfl

theorem atot13669 : totK PD2M8K2 D2M8K2.u13669 = [0, 176261417076, 652296473592, 722487983372, 192564157013, 11727338389, 0, 0] := by
  rw [show D2M8K2.u13669 = KTree.node D2M8K2.t13678 (nat_lit 30118822) (nat_lit 3841895814) (nat_lit 0) D2M8K2.t13679 from rfl, totK_node, tot13678, tot13679]
  decide +kernel

theorem arows13673 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13673 = true := by
  rw [show D2M8K2.u13673 = KTree.node D2M8K2.t13680 (nat_lit 30120523) (nat_lit 1776847844) (nat_lit 0) D2M8K2.t13681 from rfl, allE_node, rows13680, irow13673, rows13681]
  all_goals rfl

theorem atot13673 : totK PD2M8K2 D2M8K2.u13673 = [0, 238919242735, 789256184067, 651607687696, 96918445483, 1198073392, 0, 0] := by
  rw [show D2M8K2.u13673 = KTree.node D2M8K2.t13680 (nat_lit 30120523) (nat_lit 1776847844) (nat_lit 0) D2M8K2.t13681 from rfl, totK_node, tot13680, tot13681]
  decide +kernel

theorem arows13674 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13674 = true := by
  rw [show D2M8K2.u13674 = KTree.node D2M8K2.t13682 (nat_lit 30122236) (nat_lit 2753652085) (nat_lit 0) D2M8K2.t13683 from rfl, allE_node, rows13682, irow13674, rows13683]
  all_goals rfl

theorem atot13674 : totK PD2M8K2 D2M8K2.u13674 = [0, 155702246731, 625065698320, 744334433179, 201354872677, 11894306413, 0, 0] := by
  rw [show D2M8K2.u13674 = KTree.node D2M8K2.t13682 (nat_lit 30122236) (nat_lit 2753652085) (nat_lit 0) D2M8K2.t13683 from rfl, totK_node, tot13682, tot13683]
  decide +kernel

theorem arows13676 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13676 = true := by
  rw [show D2M8K2.u13676 = KTree.node D2M8K2.t13684 (nat_lit 30123683) (nat_lit 1165073085) (nat_lit 0) D2M8K2.t13685 from rfl, allE_node, rows13684, irow13676, rows13685]
  all_goals rfl

theorem atot13676 : totK PD2M8K2 D2M8K2.u13676 = [0, 239979594387, 789732141607, 634978574018, 85987902451, 1096505104, 0, 0] := by
  rw [show D2M8K2.u13676 = KTree.node D2M8K2.t13684 (nat_lit 30123683) (nat_lit 1165073085) (nat_lit 0) D2M8K2.t13685 from rfl, totK_node, tot13684, tot13685]
  decide +kernel

theorem arows13677 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13677 = true := by
  rw [show D2M8K2.u13677 = KTree.node D2M8K2.t13686 (nat_lit 30126012) (nat_lit 3240801578) (nat_lit 0) D2M8K2.t13687 from rfl, allE_node, rows13686, irow13677, rows13687]
  all_goals rfl

theorem atot13677 : totK PD2M8K2 D2M8K2.u13677 = [0, 238638629558, 752981127722, 671582260975, 122460620213, 3838026431, 0, 0] := by
  rw [show D2M8K2.u13677 = KTree.node D2M8K2.t13686 (nat_lit 30126012) (nat_lit 3240801578) (nat_lit 0) D2M8K2.t13687 from rfl, totK_node, tot13686, tot13687]
  decide +kernel

theorem arows13680 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13680 = true := by
  rw [show D2M8K2.u13680 = KTree.node D2M8K2.t13688 (nat_lit 30127530) (nat_lit 3837906860) (nat_lit 0) D2M8K2.t13689 from rfl, allE_node, rows13688, irow13680, rows13689]
  all_goals rfl

theorem atot13680 : totK PD2M8K2 D2M8K2.u13680 = [0, 182307975947, 759632416085, 741274187539, 117727280358, 1268739303, 0, 0] := by
  rw [show D2M8K2.u13680 = KTree.node D2M8K2.t13688 (nat_lit 30127530) (nat_lit 3837906860) (nat_lit 0) D2M8K2.t13689 from rfl, totK_node, tot13688, tot13689]
  decide +kernel

theorem arows13681 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13681 = true := by
  rw [show D2M8K2.u13681 = KTree.node D2M8K2.t13690 (nat_lit 30129247) (nat_lit 2303470709) (nat_lit 0) D2M8K2.t13691 from rfl, allE_node, rows13690, irow13681, rows13691]
  all_goals rfl

theorem atot13681 : totK PD2M8K2 D2M8K2.u13681 = [0, 0, 392745570714, 955261600224, 378711557855, 21873045024, 0, 0] := by
  rw [show D2M8K2.u13681 = KTree.node D2M8K2.t13690 (nat_lit 30129247) (nat_lit 2303470709) (nat_lit 0) D2M8K2.t13691 from rfl, totK_node, tot13690, tot13691]
  decide +kernel

theorem arows13683 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13683 = true := by
  rw [show D2M8K2.u13683 = KTree.node D2M8K2.t13692 (nat_lit 30130737) (nat_lit 1470827640) (nat_lit 0) D2M8K2.t13693 from rfl, allE_node, rows13692, irow13683, rows13693]
  all_goals rfl

theorem atot13683 : totK PD2M8K2 D2M8K2.u13683 = [0, 0, 256374077221, 805940547607, 573113633327, 93762628625, 1369150432, 0] := by
  rw [show D2M8K2.u13683 = KTree.node D2M8K2.t13692 (nat_lit 30130737) (nat_lit 1470827640) (nat_lit 0) D2M8K2.t13693 from rfl, totK_node, tot13692, tot13693]
  decide +kernel

theorem arows13684 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13684 = true := by
  rw [show D2M8K2.u13684 = KTree.node D2M8K2.t13694 (nat_lit 30132719) (nat_lit 2669677758) (nat_lit 0) D2M8K2.t13695 from rfl, allE_node, rows13694, irow13684, rows13695]
  all_goals rfl

theorem atot13684 : totK PD2M8K2 D2M8K2.u13684 = [0, 0, 242881387150, 835561920533, 594219126952, 71872849451, 0, 0] := by
  rw [show D2M8K2.u13684 = KTree.node D2M8K2.t13694 (nat_lit 30132719) (nat_lit 2669677758) (nat_lit 0) D2M8K2.t13695 from rfl, totK_node, tot13694, tot13695]
  decide +kernel

theorem arows13691 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13691 = true := by
  rw [show D2M8K2.u13691 = KTree.node D2M8K2.t13696 (nat_lit 30138031) (nat_lit 1725058681) (nat_lit 0) D2M8K2.t13697 from rfl, allE_node, rows13696, irow13691, rows13697]
  all_goals rfl

theorem atot13691 : totK PD2M8K2 D2M8K2.u13691 = [0, 0, 410352159268, 950130180870, 369851430980, 22152831983, 0, 0] := by
  rw [show D2M8K2.u13691 = KTree.node D2M8K2.t13696 (nat_lit 30138031) (nat_lit 1725058681) (nat_lit 0) D2M8K2.t13697 from rfl, totK_node, tot13696, tot13697]
  decide +kernel

theorem arows13692 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13692 = true := by
  rw [show D2M8K2.u13692 = KTree.node D2M8K2.t13698 (nat_lit 30141450) (nat_lit 3456472787) (nat_lit 0) D2M8K2.t13699 from rfl, allE_node, rows13698, irow13692, rows13699]
  all_goals rfl

theorem atot13692 : totK PD2M8K2 D2M8K2.u13692 = [0, 0, 386299925720, 941674843173, 374867860341, 22205972458, 0, 0] := by
  rw [show D2M8K2.u13692 = KTree.node D2M8K2.t13698 (nat_lit 30141450) (nat_lit 3456472787) (nat_lit 0) D2M8K2.t13699 from rfl, totK_node, tot13698, tot13699]
  decide +kernel

theorem arows13694 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13694 = true := by
  rw [show D2M8K2.u13694 = KTree.node D2M8K2.t13700 (nat_lit 30144624) (nat_lit 3394198253) (nat_lit 0) D2M8K2.t13701 from rfl, allE_node, rows13700, irow13694, rows13701]
  all_goals rfl

theorem atot13694 : totK PD2M8K2 D2M8K2.u13694 = [0, 0, 411748540939, 954754805828, 366006762740, 21804211528, 0, 0] := by
  rw [show D2M8K2.u13694 = KTree.node D2M8K2.t13700 (nat_lit 30144624) (nat_lit 3394198253) (nat_lit 0) D2M8K2.t13701 from rfl, totK_node, tot13700, tot13701]
  decide +kernel

theorem arows13695 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13695 = true := by
  rw [show D2M8K2.u13695 = KTree.node D2M8K2.t13702 (nat_lit 30148352) (nat_lit 2438836486) (nat_lit 0) D2M8K2.t13703 from rfl, allE_node, rows13702, irow13695, rows13703]
  all_goals rfl

theorem atot13695 : totK PD2M8K2 D2M8K2.u13695 = [0, 179595312347, 618491694471, 700117834220, 260481787307, 19954714514, 0, 0] := by
  rw [show D2M8K2.u13695 = KTree.node D2M8K2.t13702 (nat_lit 30148352) (nat_lit 2438836486) (nat_lit 0) D2M8K2.t13703 from rfl, totK_node, tot13702, tot13703]
  decide +kernel

theorem arows13698 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13698 = true := by
  rw [show D2M8K2.u13698 = KTree.node D2M8K2.t13704 (nat_lit 30193109) (nat_lit 2375860474) (nat_lit 0) D2M8K2.t13705 from rfl, allE_node, rows13704, irow13698, rows13705]
  all_goals rfl

theorem atot13698 : totK PD2M8K2 D2M8K2.u13698 = [0, 238514996341, 770326352021, 645258037930, 110007883210, 1369150432, 0, 0] := by
  rw [show D2M8K2.u13698 = KTree.node D2M8K2.t13704 (nat_lit 30193109) (nat_lit 2375860474) (nat_lit 0) D2M8K2.t13705 from rfl, totK_node, tot13704, tot13705]
  decide +kernel

theorem arows13699 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13699 = true := by
  rw [show D2M8K2.u13699 = KTree.node D2M8K2.t13706 (nat_lit 30195462) (nat_lit 3160555277) (nat_lit 0) D2M8K2.t13707 from rfl, allE_node, rows13706, irow13699, rows13707]
  all_goals rfl

theorem atot13699 : totK PD2M8K2 D2M8K2.u13699 = [0, 227539213097, 793489581841, 712239051045, 84293523840, 0, 0, 0] := by
  rw [show D2M8K2.u13699 = KTree.node D2M8K2.t13706 (nat_lit 30195462) (nat_lit 3160555277) (nat_lit 0) D2M8K2.t13707 from rfl, totK_node, tot13706, tot13707]
  decide +kernel

theorem arows13701 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13701 = true := by
  rw [show D2M8K2.u13701 = KTree.node D2M8K2.t13708 (nat_lit 30197402) (nat_lit 4242461733) (nat_lit 0) D2M8K2.t13709 from rfl, allE_node, rows13708, irow13701, rows13709]
  all_goals rfl

theorem atot13701 : totK PD2M8K2 D2M8K2.u13701 = [0, 100063523034, 644125841848, 864026942111, 211198477462, 5284349065, 0, 0] := by
  rw [show D2M8K2.u13701 = KTree.node D2M8K2.t13708 (nat_lit 30197402) (nat_lit 4242461733) (nat_lit 0) D2M8K2.t13709 from rfl, totK_node, tot13708, tot13709]
  decide +kernel

theorem arows13702 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13702 = true := by
  rw [show D2M8K2.u13702 = KTree.node D2M8K2.t13710 (nat_lit 30199131) (nat_lit 3757426137) (nat_lit 0) D2M8K2.t13711 from rfl, allE_node, rows13710, irow13702, rows13711]
  all_goals rfl

theorem atot13702 : totK PD2M8K2 D2M8K2.u13702 = [0, 381320340385, 938112571361, 463590059450, 32812206283, 0, 0, 0] := by
  rw [show D2M8K2.u13702 = KTree.node D2M8K2.t13710 (nat_lit 30199131) (nat_lit 3757426137) (nat_lit 0) D2M8K2.t13711 from rfl, totK_node, tot13710, tot13711]
  decide +kernel

theorem arows13706 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13706 = true := by
  rw [show D2M8K2.u13706 = KTree.node D2M8K2.t13712 (nat_lit 30200656) (nat_lit 3344895372) (nat_lit 0) D2M8K2.t13713 from rfl, allE_node, rows13712, irow13706, rows13713]
  all_goals rfl

theorem atot13706 : totK PD2M8K2 D2M8K2.u13706 = [0, 52068623752, 525257990949, 906312623215, 273701689659, 13049727234, 0, 0] := by
  rw [show D2M8K2.u13706 = KTree.node D2M8K2.t13712 (nat_lit 30200656) (nat_lit 3344895372) (nat_lit 0) D2M8K2.t13713 from rfl, totK_node, tot13712, tot13713]
  decide +kernel

theorem arows13707 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13707 = true := by
  rw [show D2M8K2.u13707 = KTree.node D2M8K2.t13714 (nat_lit 30205940) (nat_lit 3241355303) (nat_lit 0) D2M8K2.t13715 from rfl, allE_node, rows13714, irow13707, rows13715]
  all_goals rfl

theorem atot13707 : totK PD2M8K2 D2M8K2.u13707 = [0, 325019756198, 872123617639, 549786869537, 55292714361, 0, 0, 0] := by
  rw [show D2M8K2.u13707 = KTree.node D2M8K2.t13714 (nat_lit 30205940) (nat_lit 3241355303) (nat_lit 0) D2M8K2.t13715 from rfl, totK_node, tot13714, tot13715]
  decide +kernel

theorem arows13709 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13709 = true := by
  rw [show D2M8K2.u13709 = KTree.node D2M8K2.t13716 (nat_lit 30207764) (nat_lit 3206199631) (nat_lit 0) D2M8K2.t13717 from rfl, allE_node, rows13716, irow13709, rows13717]
  all_goals rfl

theorem atot13709 : totK PD2M8K2 D2M8K2.u13709 = [0, 113494021220, 628502389031, 832021267489, 179458461981, 4917269347, 0, 0] := by
  rw [show D2M8K2.u13709 = KTree.node D2M8K2.t13716 (nat_lit 30207764) (nat_lit 3206199631) (nat_lit 0) D2M8K2.t13717 from rfl, totK_node, tot13716, tot13717]
  decide +kernel

theorem arows13710 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13710 = true := by
  rw [show D2M8K2.u13710 = KTree.node D2M8K2.t13718 (nat_lit 30209605) (nat_lit 1350922084) (nat_lit 0) D2M8K2.t13719 from rfl, allE_node, rows13718, irow13710, rows13719]
  all_goals rfl

theorem atot13710 : totK PD2M8K2 D2M8K2.u13710 = [0, 353159818149, 949096037979, 502833118745, 34881967713, 0, 0, 0] := by
  rw [show D2M8K2.u13710 = KTree.node D2M8K2.t13718 (nat_lit 30209605) (nat_lit 1350922084) (nat_lit 0) D2M8K2.t13719 from rfl, totK_node, tot13718, tot13719]
  decide +kernel

theorem arows13713 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13713 = true := by
  rw [show D2M8K2.u13713 = KTree.node D2M8K2.t13720 (nat_lit 30211317) (nat_lit 1505719464) (nat_lit 0) D2M8K2.t13721 from rfl, allE_node, rows13720, irow13713, rows13721]
  all_goals rfl

theorem atot13713 : totK PD2M8K2 D2M8K2.u13713 = [0, 24749797672, 481088297481, 960793704730, 307286577482, 13684302317, 0, 0] := by
  rw [show D2M8K2.u13713 = KTree.node D2M8K2.t13720 (nat_lit 30211317) (nat_lit 1505719464) (nat_lit 0) D2M8K2.t13721 from rfl, totK_node, tot13720, tot13721]
  decide +kernel

theorem arows13714 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13714 = true := by
  rw [show D2M8K2.u13714 = KTree.node D2M8K2.t13722 (nat_lit 30234069) (nat_lit 1733370660) (nat_lit 0) D2M8K2.t13723 from rfl, allE_node, rows13722, irow13714, rows13723]
  all_goals rfl

theorem atot13714 : totK PD2M8K2 D2M8K2.u13714 = [0, 389479818927, 947151351711, 416655913875, 22262016262, 0, 0, 0] := by
  rw [show D2M8K2.u13714 = KTree.node D2M8K2.t13722 (nat_lit 30234069) (nat_lit 1733370660) (nat_lit 0) D2M8K2.t13723 from rfl, totK_node, tot13722, tot13723]
  decide +kernel

theorem arows13716 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13716 = true := by
  rw [show D2M8K2.u13716 = KTree.node D2M8K2.t13724 (nat_lit 30235759) (nat_lit 2446349698) (nat_lit 0) D2M8K2.t13725 from rfl, allE_node, rows13724, irow13716, rows13725]
  all_goals rfl

theorem atot13716 : totK PD2M8K2 D2M8K2.u13716 = [0, 89016638454, 660944852201, 891584025777, 162001734719, 1369150432, 0, 0] := by
  rw [show D2M8K2.u13716 = KTree.node D2M8K2.t13724 (nat_lit 30235759) (nat_lit 2446349698) (nat_lit 0) D2M8K2.t13725 from rfl, totK_node, tot13724, tot13725]
  decide +kernel

theorem arows13717 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13717 = true := by
  rw [show D2M8K2.u13717 = KTree.node D2M8K2.t13726 (nat_lit 30237936) (nat_lit 3179571406) (nat_lit 0) D2M8K2.t13727 from rfl, allE_node, rows13726, irow13717, rows13727]
  all_goals rfl

theorem atot13717 : totK PD2M8K2 D2M8K2.u13717 = [0, 241996330601, 843674272948, 676142609773, 77619378155, 0, 0, 0] := by
  rw [show D2M8K2.u13717 = KTree.node D2M8K2.t13726 (nat_lit 30237936) (nat_lit 3179571406) (nat_lit 0) D2M8K2.t13727 from rfl, totK_node, tot13726, tot13727]
  decide +kernel

theorem arows13722 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13722 = true := by
  rw [show D2M8K2.u13722 = KTree.node D2M8K2.t13728 (nat_lit 30243549) (nat_lit 1565350020) (nat_lit 0) D2M8K2.t13729 from rfl, allE_node, rows13728, irow13722, rows13729]
  all_goals rfl

theorem atot13722 : totK PD2M8K2 D2M8K2.u13722 = [0, 245690800671, 710117800854, 683521191515, 179028376201, 5348807592, 0, 0] := by
  rw [show D2M8K2.u13722 = KTree.node D2M8K2.t13728 (nat_lit 30243549) (nat_lit 1565350020) (nat_lit 0) D2M8K2.t13729 from rfl, totK_node, tot13728, tot13729]
  decide +kernel

theorem arows13723 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13723 = true := by
  rw [show D2M8K2.u13723 = KTree.node D2M8K2.t13730 (nat_lit 30245027) (nat_lit 2986211996) (nat_lit 0) D2M8K2.t13731 from rfl, allE_node, rows13730, irow13723, rows13731]
  all_goals rfl

theorem atot13723 : totK PD2M8K2 D2M8K2.u13723 = [0, 191642939225, 776459552616, 717179944470, 110311060569, 1178750802, 0, 0] := by
  rw [show D2M8K2.u13723 = KTree.node D2M8K2.t13730 (nat_lit 30245027) (nat_lit 2986211996) (nat_lit 0) D2M8K2.t13731 from rfl, totK_node, tot13730, tot13731]
  decide +kernel

theorem arows13725 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13725 = true := by
  rw [show D2M8K2.u13725 = KTree.node D2M8K2.t13732 (nat_lit 30246684) (nat_lit 2850338740) (nat_lit 0) D2M8K2.t13733 from rfl, allE_node, rows13732, irow13725, rows13733]
  all_goals rfl

theorem atot13725 : totK PD2M8K2 D2M8K2.u13725 = [0, 167188989745, 631535039009, 747820281614, 225602777815, 11991925116, 0, 0] := by
  rw [show D2M8K2.u13725 = KTree.node D2M8K2.t13732 (nat_lit 30246684) (nat_lit 2850338740) (nat_lit 0) D2M8K2.t13733 from rfl, totK_node, tot13732, tot13733]
  decide +kernel

theorem arows13726 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13726 = true := by
  rw [show D2M8K2.u13726 = KTree.node D2M8K2.t13734 (nat_lit 30248162) (nat_lit 4074876605) (nat_lit 0) D2M8K2.t13735 from rfl, allE_node, rows13734, irow13726, rows13735]
  all_goals rfl

theorem atot13726 : totK PD2M8K2 D2M8K2.u13726 = [0, 211314768959, 768710798546, 682960486573, 97694020105, 1096505104, 0, 0] := by
  rw [show D2M8K2.u13726 = KTree.node D2M8K2.t13734 (nat_lit 30248162) (nat_lit 4074876605) (nat_lit 0) D2M8K2.t13735 from rfl, totK_node, tot13734, tot13735]
  decide +kernel

theorem arows13729 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13729 = true := by
  rw [show D2M8K2.u13729 = KTree.node D2M8K2.t13736 (nat_lit 30250525) (nat_lit 1369587937) (nat_lit 0) D2M8K2.t13737 from rfl, allE_node, rows13736, irow13729, rows13737]
  all_goals rfl

theorem atot13729 : totK PD2M8K2 D2M8K2.u13729 = [0, 238758650812, 774509966254, 666081796519, 124123831823, 3821179711, 0, 0] := by
  rw [show D2M8K2.u13729 = KTree.node D2M8K2.t13736 (nat_lit 30250525) (nat_lit 1369587937) (nat_lit 0) D2M8K2.t13737 from rfl, totK_node, tot13736, tot13737]
  decide +kernel

theorem arows13730 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13730 = true := by
  rw [show D2M8K2.u13730 = KTree.node D2M8K2.t13738 (nat_lit 30252091) (nat_lit 1509223917) (nat_lit 0) D2M8K2.t13739 from rfl, allE_node, rows13738, irow13730, rows13739]
  all_goals rfl

theorem atot13730 : totK PD2M8K2 D2M8K2.u13730 = [0, 177290894043, 735940087658, 769113769697, 135147680385, 1232609433, 0, 0] := by
  rw [show D2M8K2.u13730 = KTree.node D2M8K2.t13738 (nat_lit 30252091) (nat_lit 1509223917) (nat_lit 0) D2M8K2.t13739 from rfl, totK_node, tot13738, tot13739]
  decide +kernel

theorem arows13732 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13732 = true := by
  rw [show D2M8K2.u13732 = KTree.node D2M8K2.t13740 (nat_lit 30274663) (nat_lit 2348579544) (nat_lit 0) D2M8K2.t13741 from rfl, allE_node, rows13740, irow13732, rows13741]
  all_goals rfl

theorem atot13732 : totK PD2M8K2 D2M8K2.u13732 = [0, 260151477161, 708277058427, 606042638292, 193097044855, 12482056447, 0, 0] := by
  rw [show D2M8K2.u13732 = KTree.node D2M8K2.t13740 (nat_lit 30274663) (nat_lit 2348579544) (nat_lit 0) D2M8K2.t13741 from rfl, totK_node, tot13740, tot13741]
  decide +kernel

theorem arows13733 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13733 = true := by
  rw [show D2M8K2.u13733 = KTree.node D2M8K2.t13742 (nat_lit 30276209) (nat_lit 1543710815) (nat_lit 0) D2M8K2.t13743 from rfl, allE_node, rows13742, irow13733, rows13743]
  all_goals rfl

theorem atot13733 : totK PD2M8K2 D2M8K2.u13733 = [0, 158217167705, 731749924853, 750368516770, 126884284321, 1369150432, 0, 0] := by
  rw [show D2M8K2.u13733 = KTree.node D2M8K2.t13742 (nat_lit 30276209) (nat_lit 1543710815) (nat_lit 0) D2M8K2.t13743 from rfl, totK_node, tot13742, tot13743]
  decide +kernel

theorem arows13737 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13737 = true := by
  rw [show D2M8K2.u13737 = KTree.node D2M8K2.t13744 (nat_lit 30281794) (nat_lit 3739956672) (nat_lit 0) D2M8K2.t13745 from rfl, allE_node, rows13744, irow13737, rows13745]
  all_goals rfl

theorem atot13737 : totK PD2M8K2 D2M8K2.u13737 = [0, 279227857285, 846541416247, 614678142329, 62868341310, 0, 0, 0] := by
  rw [show D2M8K2.u13737 = KTree.node D2M8K2.t13744 (nat_lit 30281794) (nat_lit 3739956672) (nat_lit 0) D2M8K2.t13745 from rfl, totK_node, tot13744, tot13745]
  decide +kernel

theorem arows13738 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13738 = true := by
  rw [show D2M8K2.u13738 = KTree.node D2M8K2.t13746 (nat_lit 30283342) (nat_lit 3600420522) (nat_lit 0) D2M8K2.t13747 from rfl, allE_node, rows13746, irow13738, rows13747]
  all_goals rfl

theorem atot13738 : totK PD2M8K2 D2M8K2.u13738 = [0, 119900797135, 639346381404, 801222475042, 195779948653, 9521435666, 0, 0] := by
  rw [show D2M8K2.u13738 = KTree.node D2M8K2.t13746 (nat_lit 30283342) (nat_lit 3600420522) (nat_lit 0) D2M8K2.t13747 from rfl, totK_node, tot13746, tot13747]
  decide +kernel

theorem arows13740 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13740 = true := by
  rw [show D2M8K2.u13740 = KTree.node D2M8K2.t13748 (nat_lit 30285298) (nat_lit 3689652144) (nat_lit 0) D2M8K2.t13749 from rfl, allE_node, rows13748, irow13740, rows13749]
  all_goals rfl

theorem atot13740 : totK PD2M8K2 D2M8K2.u13740 = [0, 293623504701, 803283631551, 585436312489, 102077684810, 3462014130, 0, 0] := by
  rw [show D2M8K2.u13740 = KTree.node D2M8K2.t13748 (nat_lit 30285298) (nat_lit 3689652144) (nat_lit 0) D2M8K2.t13749 from rfl, totK_node, tot13748, tot13749]
  decide +kernel

theorem arows13741 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13741 = true := by
  rw [show D2M8K2.u13741 = KTree.node D2M8K2.t13750 (nat_lit 30286852) (nat_lit 3394921380) (nat_lit 0) D2M8K2.t13751 from rfl, allE_node, rows13750, irow13741, rows13751]
  all_goals rfl

theorem atot13741 : totK PD2M8K2 D2M8K2.u13741 = [0, 102219663118, 634684602994, 822093662926, 203278452796, 9602367571, 0, 0] := by
  rw [show D2M8K2.u13741 = KTree.node D2M8K2.t13750 (nat_lit 30286852) (nat_lit 3394921380) (nat_lit 0) D2M8K2.t13751 from rfl, totK_node, tot13750, tot13751]
  decide +kernel

theorem arows13744 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13744 = true := by
  rw [show D2M8K2.u13744 = KTree.node D2M8K2.t13752 (nat_lit 30288754) (nat_lit 3024665922) (nat_lit 0) D2M8K2.t13753 from rfl, allE_node, rows13752, irow13744, rows13753]
  all_goals rfl

theorem atot13744 : totK PD2M8K2 D2M8K2.u13744 = [0, 317458532241, 813699839573, 557626150683, 102175771921, 3581949829, 0, 0] := by
  rw [show D2M8K2.u13744 = KTree.node D2M8K2.t13752 (nat_lit 30288754) (nat_lit 3024665922) (nat_lit 0) D2M8K2.t13753 from rfl, totK_node, tot13752, tot13753]
  decide +kernel

theorem arows13745 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13745 = true := by
  rw [show D2M8K2.u13745 = KTree.node D2M8K2.t13754 (nat_lit 30290257) (nat_lit 1532351776) (nat_lit 0) D2M8K2.t13755 from rfl, allE_node, rows13754, irow13745, rows13755]
  all_goals rfl

theorem atot13745 : totK PD2M8K2 D2M8K2.u13745 = [0, 105443762153, 712932627562, 840753234749, 128769585894, 1096505104, 0, 0] := by
  rw [show D2M8K2.u13745 = KTree.node D2M8K2.t13754 (nat_lit 30290257) (nat_lit 1532351776) (nat_lit 0) D2M8K2.t13755 from rfl, totK_node, tot13754, tot13755]
  decide +kernel

theorem arows13747 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13747 = true := by
  rw [show D2M8K2.u13747 = KTree.node D2M8K2.t13756 (nat_lit 30316730) (nat_lit 3778325393) (nat_lit 0) D2M8K2.t13757 from rfl, allE_node, rows13756, irow13747, rows13757]
  all_goals rfl

theorem atot13747 : totK PD2M8K2 D2M8K2.u13747 = [0, 330725126320, 833801951830, 505869444419, 99526317969, 3884009855, 0, 0] := by
  rw [show D2M8K2.u13747 = KTree.node D2M8K2.t13756 (nat_lit 30316730) (nat_lit 3778325393) (nat_lit 0) D2M8K2.t13757 from rfl, totK_node, tot13756, tot13757]
  decide +kernel

theorem arows13748 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13748 = true := by
  rw [show D2M8K2.u13748 = KTree.node D2M8K2.t13758 (nat_lit 30317978) (nat_lit 2621645474) (nat_lit 0) D2M8K2.t13759 from rfl, allE_node, rows13758, irow13748, rows13759]
  all_goals rfl

theorem atot13748 : totK PD2M8K2 D2M8K2.u13748 = [0, 89411507079, 676488594396, 881518748596, 147172119004, 1369150432, 0, 0] := by
  rw [show D2M8K2.u13748 = KTree.node D2M8K2.t13758 (nat_lit 30317978) (nat_lit 2621645474) (nat_lit 0) D2M8K2.t13759 from rfl, totK_node, tot13758, tot13759]
  decide +kernel

theorem arows13754 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13754 = true := by
  rw [show D2M8K2.u13754 = KTree.node D2M8K2.t13760 (nat_lit 30320308) (nat_lit 3792735541) (nat_lit 0) D2M8K2.t13761 from rfl, allE_node, rows13760, irow13754, rows13761]
  all_goals rfl

theorem atot13754 : totK PD2M8K2 D2M8K2.u13754 = [0, 347812456902, 915899114526, 549594310774, 48816245264, 0, 0, 0] := by
  rw [show D2M8K2.u13754 = KTree.node D2M8K2.t13760 (nat_lit 30320308) (nat_lit 3792735541) (nat_lit 0) D2M8K2.t13761 from rfl, totK_node, tot13760, tot13761]
  decide +kernel

theorem arows13755 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13755 = true := by
  rw [show D2M8K2.u13755 = KTree.node D2M8K2.t13762 (nat_lit 30322255) (nat_lit 1685867339) (nat_lit 0) D2M8K2.t13763 from rfl, allE_node, rows13762, irow13755, rows13763]
  all_goals rfl

theorem atot13755 : totK PD2M8K2 D2M8K2.u13755 = [0, 84969655104, 550215498606, 870031972642, 284666699608, 9575627623, 0, 0] := by
  rw [show D2M8K2.u13755 = KTree.node D2M8K2.t13762 (nat_lit 30322255) (nat_lit 1685867339) (nat_lit 0) D2M8K2.t13763 from rfl, totK_node, tot13762, tot13763]
  decide +kernel

theorem arows13757 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13757 = true := by
  rw [show D2M8K2.u13757 = KTree.node D2M8K2.t13764 (nat_lit 30323791) (nat_lit 1571948895) (nat_lit 0) D2M8K2.t13765 from rfl, allE_node, rows13764, irow13757, rows13765]
  all_goals rfl

theorem atot13757 : totK PD2M8K2 D2M8K2.u13757 = [0, 327140214827, 896513471031, 552669518749, 51900595069, 0, 0, 0] := by
  rw [show D2M8K2.u13757 = KTree.node D2M8K2.t13764 (nat_lit 30323791) (nat_lit 1571948895) (nat_lit 0) D2M8K2.t13765 from rfl, totK_node, tot13764, tot13765]
  decide +kernel

theorem arows13758 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13758 = true := by
  rw [show D2M8K2.u13758 = KTree.node D2M8K2.t13766 (nat_lit 30325832) (nat_lit 3636545356) (nat_lit 0) D2M8K2.t13767 from rfl, allE_node, rows13766, irow13758, rows13767]
  all_goals rfl

theorem atot13758 : totK PD2M8K2 D2M8K2.u13758 = [0, 130520046992, 637060686685, 835505263884, 194576559076, 5138457373, 0, 0] := by
  rw [show D2M8K2.u13758 = KTree.node D2M8K2.t13766 (nat_lit 30325832) (nat_lit 3636545356) (nat_lit 0) D2M8K2.t13767 from rfl, totK_node, tot13766, tot13767]
  decide +kernel

theorem arows13761 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13761 = true := by
  rw [show D2M8K2.u13761 = KTree.node D2M8K2.t13768 (nat_lit 30327636) (nat_lit 3175241463) (nat_lit 0) D2M8K2.t13769 from rfl, allE_node, rows13768, irow13761, rows13769]
  all_goals rfl

theorem atot13761 : totK PD2M8K2 D2M8K2.u13761 = [0, 281833728695, 868506911708, 604264161721, 61159915943, 0, 0, 0] := by
  rw [show D2M8K2.u13761 = KTree.node D2M8K2.t13768 (nat_lit 30327636) (nat_lit 3175241463) (nat_lit 0) D2M8K2.t13769 from rfl, totK_node, tot13768, tot13769]
  decide +kernel

theorem arows13762 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13762 = true := by
  rw [show D2M8K2.u13762 = KTree.node D2M8K2.t13770 (nat_lit 30329372) (nat_lit 3391774716) (nat_lit 0) D2M8K2.t13771 from rfl, allE_node, rows13770, irow13762, rows13771]
  all_goals rfl

theorem atot13762 : totK PD2M8K2 D2M8K2.u13762 = [0, 173127692068, 666673900141, 775616196400, 193322020366, 5193381917, 0, 0] := by
  rw [show D2M8K2.u13762 = KTree.node D2M8K2.t13770 (nat_lit 30329372) (nat_lit 3391774716) (nat_lit 0) D2M8K2.t13771 from rfl, totK_node, tot13770, tot13771]
  decide +kernel

theorem arows13764 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13764 = true := by
  rw [show D2M8K2.u13764 = KTree.node D2M8K2.t13772 (nat_lit 30334308) (nat_lit 3242035592) (nat_lit 0) D2M8K2.t13773 from rfl, allE_node, rows13772, irow13764, rows13773]
  all_goals rfl

theorem atot13764 : totK PD2M8K2 D2M8K2.u13764 = [0, 268835410623, 877360378466, 635427435636, 55623210114, 0, 0, 0] := by
  rw [show D2M8K2.u13764 = KTree.node D2M8K2.t13772 (nat_lit 30334308) (nat_lit 3242035592) (nat_lit 0) D2M8K2.t13773 from rfl, totK_node, tot13772, tot13773]
  decide +kernel

theorem arows13765 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13765 = true := by
  rw [show D2M8K2.u13765 = KTree.node D2M8K2.t13774 (nat_lit 30335950) (nat_lit 3928604825) (nat_lit 0) D2M8K2.t13775 from rfl, allE_node, rows13774, irow13765, rows13775]
  all_goals rfl

theorem atot13765 : totK PD2M8K2 D2M8K2.u13765 = [49567372496, 69446598421, 367709686334, 893957572245, 379082824307, 21897291087, 0, 0] := by
  rw [show D2M8K2.u13765 = KTree.node D2M8K2.t13774 (nat_lit 30335950) (nat_lit 3928604825) (nat_lit 0) D2M8K2.t13775 from rfl, totK_node, tot13774, tot13775]
  decide +kernel

theorem arows13769 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13769 = true := by
  rw [show D2M8K2.u13769 = KTree.node D2M8K2.t13776 (nat_lit 30403342) (nat_lit 3939038508) (nat_lit 0) D2M8K2.t13777 from rfl, allE_node, rows13776, irow13769, rows13777]
  all_goals rfl

theorem atot13769 : totK PD2M8K2 D2M8K2.u13769 = [358397957712, 935988106637, 508193983582, 41958694838, 0, 0, 0, 0] := by
  rw [show D2M8K2.u13769 = KTree.node D2M8K2.t13776 (nat_lit 30403342) (nat_lit 3939038508) (nat_lit 0) D2M8K2.t13777 from rfl, totK_node, tot13776, tot13777]
  decide +kernel

theorem arows13770 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13770 = true := by
  rw [show D2M8K2.u13770 = KTree.node D2M8K2.t13778 (nat_lit 30404779) (nat_lit 1644870148) (nat_lit 0) D2M8K2.t13779 from rfl, allE_node, rows13778, irow13770, rows13779]
  all_goals rfl

theorem atot13770 : totK PD2M8K2 D2M8K2.u13770 = [34527251780, 481462838041, 892183589061, 391836055470, 29394892645, 0, 0, 0] := by
  rw [show D2M8K2.u13770 = KTree.node D2M8K2.t13778 (nat_lit 30404779) (nat_lit 1644870148) (nat_lit 0) D2M8K2.t13779 from rfl, totK_node, tot13778, tot13779]
  decide +kernel

theorem arows13772 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13772 = true := by
  rw [show D2M8K2.u13772 = KTree.node D2M8K2.t13780 (nat_lit 30406085) (nat_lit 2343662941) (nat_lit 0) D2M8K2.t13781 from rfl, allE_node, rows13780, irow13772, rows13781]
  all_goals rfl

theorem atot13772 : totK PD2M8K2 D2M8K2.u13772 = [248432038920, 713036701410, 656960082304, 206868194560, 8214505460, 0, 0, 0] := by
  rw [show D2M8K2.u13772 = KTree.node D2M8K2.t13780 (nat_lit 30406085) (nat_lit 2343662941) (nat_lit 0) D2M8K2.t13781 from rfl, totK_node, tot13780, tot13781]
  decide +kernel

theorem arows13773 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13773 = true := by
  rw [show D2M8K2.u13773 = KTree.node D2M8K2.t13782 (nat_lit 30407554) (nat_lit 3967171411) (nat_lit 0) D2M8K2.t13783 from rfl, allE_node, rows13782, irow13773, rows13783]
  all_goals rfl

theorem atot13773 : totK PD2M8K2 D2M8K2.u13773 = [171674375026, 727051732187, 749729360033, 138815114670, 2287653690, 0, 0, 0] := by
  rw [show D2M8K2.u13773 = KTree.node D2M8K2.t13782 (nat_lit 30407554) (nat_lit 3967171411) (nat_lit 0) D2M8K2.t13783 from rfl, totK_node, tot13782, tot13783]
  decide +kernel

theorem arows13776 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13776 = true := by
  rw [show D2M8K2.u13776 = KTree.node D2M8K2.t13784 (nat_lit 30409449) (nat_lit 1884935950) (nat_lit 0) D2M8K2.t13785 from rfl, allE_node, rows13784, irow13776, rows13785]
  all_goals rfl

theorem atot13776 : totK PD2M8K2 D2M8K2.u13776 = [244467197155, 695874355530, 664246520033, 188181829485, 10608469453, 0, 0, 0] := by
  rw [show D2M8K2.u13776 = KTree.node D2M8K2.t13784 (nat_lit 30409449) (nat_lit 1884935950) (nat_lit 0) D2M8K2.t13785 from rfl, totK_node, tot13784, tot13785]
  decide +kernel

theorem arows13777 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13777 = true := by
  rw [show D2M8K2.u13777 = KTree.node D2M8K2.t13786 (nat_lit 30410934) (nat_lit 3746187051) (nat_lit 0) D2M8K2.t13787 from rfl, allE_node, rows13786, irow13777, rows13787]
  all_goals rfl

theorem atot13777 : totK PD2M8K2 D2M8K2.u13777 = [175868549765, 766559674818, 730581543683, 121323396998, 1190718505, 0, 0, 0] := by
  rw [show D2M8K2.u13777 = KTree.node D2M8K2.t13786 (nat_lit 30410934) (nat_lit 3746187051) (nat_lit 0) D2M8K2.t13787 from rfl, totK_node, tot13786, tot13787]
  decide +kernel

theorem arows13779 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13779 = true := by
  rw [show D2M8K2.u13779 = KTree.node D2M8K2.t13788 (nat_lit 30412643) (nat_lit 2986211996) (nat_lit 0) D2M8K2.t13789 from rfl, allE_node, rows13788, irow13779, rows13789]
  all_goals rfl

theorem atot13779 : totK PD2M8K2 D2M8K2.u13779 = [197003158374, 652059057058, 711149306008, 216751682264, 11884213561, 0, 0, 0] := by
  rw [show D2M8K2.u13779 = KTree.node D2M8K2.t13788 (nat_lit 30412643) (nat_lit 2986211996) (nat_lit 0) D2M8K2.t13789 from rfl, totK_node, tot13788, tot13789]
  decide +kernel

theorem arows13780 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13780 = true := by
  rw [show D2M8K2.u13780 = KTree.node D2M8K2.t13790 (nat_lit 30414038) (nat_lit 3901408561) (nat_lit 0) D2M8K2.t13791 from rfl, allE_node, rows13790, irow13780, rows13791]
  all_goals rfl

theorem atot13780 : totK PD2M8K2 D2M8K2.u13780 = [204947064364, 795944204591, 694636161829, 90163394723, 0, 0, 0, 0] := by
  rw [show D2M8K2.u13780 = KTree.node D2M8K2.t13790 (nat_lit 30414038) (nat_lit 3901408561) (nat_lit 0) D2M8K2.t13791 from rfl, totK_node, tot13790, tot13791]
  decide +kernel

theorem arows13785 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13785 = true := by
  rw [show D2M8K2.u13785 = KTree.node D2M8K2.t13792 (nat_lit 30416418) (nat_lit 2735366853) (nat_lit 0) D2M8K2.t13793 from rfl, allE_node, rows13792, irow13785, rows13793]
  all_goals rfl

theorem atot13785 : totK PD2M8K2 D2M8K2.u13785 = [246152438455, 772325623620, 671012611711, 132181318179, 3795168977, 0, 0, 0] := by
  rw [show D2M8K2.u13785 = KTree.node D2M8K2.t13792 (nat_lit 30416418) (nat_lit 2735366853) (nat_lit 0) D2M8K2.t13793 from rfl, totK_node, tot13792, tot13793]
  decide +kernel

theorem arows13786 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13786 = true := by
  rw [show D2M8K2.u13786 = KTree.node D2M8K2.t13794 (nat_lit 30417900) (nat_lit 2850442696) (nat_lit 0) D2M8K2.t13795 from rfl, allE_node, rows13794, irow13786, rows13795]
  all_goals rfl

theorem atot13786 : totK PD2M8K2 D2M8K2.u13786 = [179781219229, 750931090397, 755487256507, 134599186815, 1260002070, 0, 0, 0] := by
  rw [show D2M8K2.u13786 = KTree.node D2M8K2.t13794 (nat_lit 30417900) (nat_lit 2850442696) (nat_lit 0) D2M8K2.t13795 from rfl, totK_node, tot13794, tot13795]
  decide +kernel

theorem arows13788 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13788 = true := by
  rw [show D2M8K2.u13788 = KTree.node D2M8K2.t13796 (nat_lit 30419602) (nat_lit 4014846645) (nat_lit 0) D2M8K2.t13797 from rfl, allE_node, rows13796, irow13788, rows13797]
  all_goals rfl

theorem atot13788 : totK PD2M8K2 D2M8K2.u13788 = [0, 361515079767, 918315329308, 484185334153, 42773196243, 0, 0, 0] := by
  rw [show D2M8K2.u13788 = KTree.node D2M8K2.t13796 (nat_lit 30419602) (nat_lit 4014846645) (nat_lit 0) D2M8K2.t13797 from rfl, totK_node, tot13796, tot13797]
  decide +kernel

theorem arows13789 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13789 = true := by
  rw [show D2M8K2.u13789 = KTree.node D2M8K2.t13798 (nat_lit 30424494) (nat_lit 3833690704) (nat_lit 0) D2M8K2.t13799 from rfl, allE_node, rows13798, irow13789, rows13799]
  all_goals rfl

theorem atot13789 : totK PD2M8K2 D2M8K2.u13789 = [0, 265184791547, 856149132307, 615992032035, 90225774166, 10444649207, 0, 0] := by
  rw [show D2M8K2.u13789 = KTree.node D2M8K2.t13798 (nat_lit 30424494) (nat_lit 3833690704) (nat_lit 0) D2M8K2.t13799 from rfl, totK_node, tot13798, tot13799]
  decide +kernel

theorem arows13792 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13792 = true := by
  rw [show D2M8K2.u13792 = KTree.node D2M8K2.t13800 (nat_lit 30425996) (nat_lit 2947167133) (nat_lit 0) D2M8K2.t13801 from rfl, allE_node, rows13800, irow13792, rows13801]
  all_goals rfl

theorem atot13792 : totK PD2M8K2 D2M8K2.u13792 = [0, 10283532795, 352459529493, 922056444463, 466029413173, 26477224647, 0, 0] := by
  rw [show D2M8K2.u13792 = KTree.node D2M8K2.t13800 (nat_lit 30425996) (nat_lit 2947167133) (nat_lit 0) D2M8K2.t13801 from rfl, totK_node, tot13800, tot13801]
  decide +kernel

theorem arows13793 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13793 = true := by
  rw [show D2M8K2.u13793 = KTree.node D2M8K2.t13802 (nat_lit 30427258) (nat_lit 3956944184) (nat_lit 0) D2M8K2.t13803 from rfl, allE_node, rows13802, irow13793, rows13803]
  all_goals rfl

theorem atot13793 : totK PD2M8K2 D2M8K2.u13793 = [0, 380677725400, 929905937400, 457927285743, 35246512012, 0, 0, 0] := by
  rw [show D2M8K2.u13793 = KTree.node D2M8K2.t13802 (nat_lit 30427258) (nat_lit 3956944184) (nat_lit 0) D2M8K2.t13803 from rfl, totK_node, tot13802, tot13803]
  decide +kernel

theorem arows13795 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13795 = true := by
  rw [show D2M8K2.u13795 = KTree.node D2M8K2.t13804 (nat_lit 30429058) (nat_lit 4122712912) (nat_lit 0) D2M8K2.t13805 from rfl, allE_node, rows13804, irow13795, rows13805]
  all_goals rfl

theorem atot13795 : totK PD2M8K2 D2M8K2.u13795 = [0, 71162145513, 601724526636, 897059299410, 208812481445, 5159868635, 0, 0] := by
  rw [show D2M8K2.u13795 = KTree.node D2M8K2.t13804 (nat_lit 30429058) (nat_lit 4122712912) (nat_lit 0) D2M8K2.t13805 from rfl, totK_node, tot13804, tot13805]
  decide +kernel

theorem arows13796 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13796 = true := by
  rw [show D2M8K2.u13796 = KTree.node D2M8K2.t13806 (nat_lit 30431074) (nat_lit 4123203255) (nat_lit 0) D2M8K2.t13807 from rfl, allE_node, rows13806, irow13796, rows13807]
  all_goals rfl

theorem atot13796 : totK PD2M8K2 D2M8K2.u13796 = [0, 370620139350, 937508088897, 468971513043, 35366359020, 0, 0, 0] := by
  rw [show D2M8K2.u13796 = KTree.node D2M8K2.t13806 (nat_lit 30431074) (nat_lit 4123203255) (nat_lit 0) D2M8K2.t13807 from rfl, totK_node, tot13806, tot13807]
  decide +kernel

theorem arows13800 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13800 = true := by
  rw [show D2M8K2.u13800 = KTree.node D2M8K2.t13808 (nat_lit 30432902) (nat_lit 3010007218) (nat_lit 0) D2M8K2.t13809 from rfl, allE_node, rows13808, irow13800, rows13809]
  all_goals rfl

theorem atot13800 : totK PD2M8K2 D2M8K2.u13800 = [0, 50060237061, 597551241341, 892238209895, 214730172591, 5218872685, 0, 0] := by
  rw [show D2M8K2.u13800 = KTree.node D2M8K2.t13808 (nat_lit 30432902) (nat_lit 3010007218) (nat_lit 0) D2M8K2.t13809 from rfl, totK_node, tot13808, tot13809]
  decide +kernel

theorem arows13801 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13801 = true := by
  rw [show D2M8K2.u13801 = KTree.node D2M8K2.t13810 (nat_lit 30434366) (nat_lit 2481466265) (nat_lit 0) D2M8K2.t13811 from rfl, allE_node, rows13810, irow13801, rows13811]
  all_goals rfl

theorem atot13801 : totK PD2M8K2 D2M8K2.u13801 = [0, 349990012130, 908225194585, 503923958971, 42427333709, 0, 0, 0] := by
  rw [show D2M8K2.u13801 = KTree.node D2M8K2.t13810 (nat_lit 30434366) (nat_lit 2481466265) (nat_lit 0) D2M8K2.t13811 from rfl, totK_node, tot13810, tot13811]
  decide +kernel

theorem arows13803 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13803 = true := by
  rw [show D2M8K2.u13803 = KTree.node D2M8K2.t13812 (nat_lit 30436454) (nat_lit 4109909736) (nat_lit 0) D2M8K2.t13813 from rfl, allE_node, rows13812, irow13803, rows13813]
  all_goals rfl

theorem atot13803 : totK PD2M8K2 D2M8K2.u13803 = [0, 158316649854, 728251764905, 796417352862, 135730973704, 1415142070, 0, 0] := by
  rw [show D2M8K2.u13803 = KTree.node D2M8K2.t13812 (nat_lit 30436454) (nat_lit 4109909736) (nat_lit 0) D2M8K2.t13813 from rfl, totK_node, tot13812, tot13813]
  decide +kernel

theorem arows13804 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13804 = true := by
  rw [show D2M8K2.u13804 = KTree.node D2M8K2.t13814 (nat_lit 30438009) (nat_lit 1386978015) (nat_lit 0) D2M8K2.t13815 from rfl, allE_node, rows13814, irow13804, rows13815]
  all_goals rfl

theorem atot13804 : totK PD2M8K2 D2M8K2.u13804 = [0, 265646355895, 872652656284, 616539283278, 65282136698, 0, 0, 0] := by
  rw [show D2M8K2.u13804 = KTree.node D2M8K2.t13814 (nat_lit 30438009) (nat_lit 1386978015) (nat_lit 0) D2M8K2.t13815 from rfl, totK_node, tot13814, tot13815]
  decide +kernel

theorem arows13807 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13807 = true := by
  rw [show D2M8K2.u13807 = KTree.node D2M8K2.t13816 (nat_lit 30440194) (nat_lit 4097396695) (nat_lit 0) D2M8K2.t13817 from rfl, allE_node, rows13816, irow13807, rows13817]
  all_goals rfl

theorem atot13807 : totK PD2M8K2 D2M8K2.u13807 = [138054411630, 292274864948, 386798382385, 699623237085, 255589765534, 9302370699, 0, 0] := by
  rw [show D2M8K2.u13807 = KTree.node D2M8K2.t13816 (nat_lit 30440194) (nat_lit 4097396695) (nat_lit 0) D2M8K2.t13817 from rfl, totK_node, tot13816, tot13817]
  decide +kernel

theorem arows13808 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13808 = true := by
  rw [show D2M8K2.u13808 = KTree.node D2M8K2.t13818 (nat_lit 30442048) (nat_lit 3011021403) (nat_lit 0) D2M8K2.t13819 from rfl, allE_node, rows13818, irow13808, rows13819]
  all_goals rfl

theorem atot13808 : totK PD2M8K2 D2M8K2.u13808 = [187343934231, 755629743846, 726873777416, 120139868596, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u13808 = KTree.node D2M8K2.t13818 (nat_lit 30442048) (nat_lit 3011021403) (nat_lit 0) D2M8K2.t13819 from rfl, totK_node, tot13818, tot13819]
  decide +kernel

theorem arows13810 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13810 = true := by
  rw [show D2M8K2.u13810 = KTree.node D2M8K2.t13820 (nat_lit 30444531) (nat_lit 3681445855) (nat_lit 0) D2M8K2.t13821 from rfl, allE_node, rows13820, irow13810, rows13821]
  all_goals rfl

theorem atot13810 : totK PD2M8K2 D2M8K2.u13810 = [329313399666, 870854131881, 581644418892, 62260853926, 0, 0, 0, 0] := by
  rw [show D2M8K2.u13810 = KTree.node D2M8K2.t13820 (nat_lit 30444531) (nat_lit 3681445855) (nat_lit 0) D2M8K2.t13821 from rfl, totK_node, tot13820, tot13821]
  decide +kernel

theorem arows13811 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13811 = true := by
  rw [show D2M8K2.u13811 = KTree.node D2M8K2.t13822 (nat_lit 30446053) (nat_lit 839577079) (nat_lit 0) D2M8K2.t13823 from rfl, allE_node, rows13822, irow13811, rows13823]
  all_goals rfl

theorem atot13811 : totK PD2M8K2 D2M8K2.u13811 = [95841475714, 590240558698, 798396301752, 309815491641, 25368447013, 0, 0, 0] := by
  rw [show D2M8K2.u13811 = KTree.node D2M8K2.t13822 (nat_lit 30446053) (nat_lit 839577079) (nat_lit 0) D2M8K2.t13823 from rfl, totK_node, tot13822, tot13823]
  decide +kernel

theorem arows13820 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13820 = true := by
  rw [show D2M8K2.u13820 = KTree.node D2M8K2.t13824 (nat_lit 30447308) (nat_lit 978806384) (nat_lit 0) D2M8K2.t13825 from rfl, allE_node, rows13824, irow13820, rows13825]
  all_goals rfl

theorem atot13820 : totK PD2M8K2 D2M8K2.u13820 = [171568788750, 612409158978, 731071042702, 279131771422, 12228669804, 0, 0, 0] := by
  rw [show D2M8K2.u13820 = KTree.node D2M8K2.t13824 (nat_lit 30447308) (nat_lit 978806384) (nat_lit 0) D2M8K2.t13825 from rfl, totK_node, tot13824, tot13825]
  decide +kernel

theorem arows13821 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13821 = true := by
  rw [show D2M8K2.u13821 = KTree.node D2M8K2.t13826 (nat_lit 30448810) (nat_lit 3991841279) (nat_lit 0) D2M8K2.t13827 from rfl, allE_node, rows13826, irow13821, rows13827]
  all_goals rfl

theorem atot13821 : totK PD2M8K2 D2M8K2.u13821 = [266812347753, 804859610065, 623541123062, 103817734479, 1164319620, 0, 0, 0] := by
  rw [show D2M8K2.u13821 = KTree.node D2M8K2.t13826 (nat_lit 30448810) (nat_lit 3991841279) (nat_lit 0) D2M8K2.t13827 from rfl, totK_node, tot13826, tot13827]
  decide +kernel

theorem arows13823 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13823 = true := by
  rw [show D2M8K2.u13823 = KTree.node D2M8K2.t13828 (nat_lit 30450456) (nat_lit 2011843914) (nat_lit 0) D2M8K2.t13829 from rfl, allE_node, rows13828, irow13823, rows13829]
  all_goals rfl

theorem atot13823 : totK PD2M8K2 D2M8K2.u13823 = [151660303848, 633247899272, 774892061049, 226637763126, 11885407614, 0, 0, 0] := by
  rw [show D2M8K2.u13823 = KTree.node D2M8K2.t13828 (nat_lit 30450456) (nat_lit 2011843914) (nat_lit 0) D2M8K2.t13829 from rfl, totK_node, tot13828, tot13829]
  decide +kernel

theorem arows13824 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13824 = true := by
  rw [show D2M8K2.u13824 = KTree.node D2M8K2.t13830 (nat_lit 30455424) (nat_lit 3702502139) (nat_lit 0) D2M8K2.t13831 from rfl, allE_node, rows13830, irow13824, rows13831]
  all_goals rfl

theorem atot13824 : totK PD2M8K2 D2M8K2.u13824 = [230524026028, 792471545092, 671573897431, 95895404831, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u13824 = KTree.node D2M8K2.t13830 (nat_lit 30455424) (nat_lit 3702502139) (nat_lit 0) D2M8K2.t13831 from rfl, totK_node, tot13830, tot13831]
  decide +kernel

theorem arows13827 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13827 = true := by
  rw [show D2M8K2.u13827 = KTree.node D2M8K2.t13832 (nat_lit 30457785) (nat_lit 1663393172) (nat_lit 0) D2M8K2.t13833 from rfl, allE_node, rows13832, irow13827, rows13833]
  all_goals rfl

theorem atot13827 : totK PD2M8K2 D2M8K2.u13827 = [218946508674, 734810579939, 715776413894, 147383912918, 3884009855, 0, 0, 0] := by
  rw [show D2M8K2.u13827 = KTree.node D2M8K2.t13832 (nat_lit 30457785) (nat_lit 1663393172) (nat_lit 0) D2M8K2.t13833 from rfl, totK_node, tot13832, tot13833]
  decide +kernel

theorem arows13828 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13828 = true := by
  rw [show D2M8K2.u13828 = KTree.node D2M8K2.t13834 (nat_lit 30459307) (nat_lit 1601679787) (nat_lit 0) D2M8K2.t13835 from rfl, allE_node, rows13834, irow13828, rows13835]
  all_goals rfl

theorem atot13828 : totK PD2M8K2 D2M8K2.u13828 = [199638018810, 781594349558, 713921414889, 122259673358, 1268739303, 0, 0, 0] := by
  rw [show D2M8K2.u13828 = KTree.node D2M8K2.t13834 (nat_lit 30459307) (nat_lit 1601679787) (nat_lit 0) D2M8K2.t13835 from rfl, totK_node, tot13834, tot13835]
  decide +kernel

theorem arows13830 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13830 = true := by
  rw [show D2M8K2.u13830 = KTree.node D2M8K2.t13836 (nat_lit 30461030) (nat_lit 3996305064) (nat_lit 0) D2M8K2.t13837 from rfl, allE_node, rows13836, irow13830, rows13837]
  all_goals rfl

theorem atot13830 : totK PD2M8K2 D2M8K2.u13830 = [0, 386503052115, 959628987289, 416674533160, 22108519610, 0, 0, 0] := by
  rw [show D2M8K2.u13830 = KTree.node D2M8K2.t13836 (nat_lit 30461030) (nat_lit 3996305064) (nat_lit 0) D2M8K2.t13837 from rfl, totK_node, tot13836, tot13837]
  decide +kernel

theorem arows13831 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13831 = true := by
  rw [show D2M8K2.u13831 = KTree.node D2M8K2.t13838 (nat_lit 30462904) (nat_lit 3338834425) (nat_lit 0) D2M8K2.t13839 from rfl, allE_node, rows13838, irow13831, rows13839]
  all_goals rfl

theorem atot13831 : totK PD2M8K2 D2M8K2.u13831 = [0, 151351491967, 738574788418, 750005414595, 107834769325, 1206465782, 0, 0] := by
  rw [show D2M8K2.u13831 = KTree.node D2M8K2.t13838 (nat_lit 30462904) (nat_lit 3338834425) (nat_lit 0) D2M8K2.t13839 from rfl, totK_node, tot13838, tot13839]
  decide +kernel

theorem arows13835 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13835 = true := by
  rw [show D2M8K2.u13835 = KTree.node D2M8K2.t13840 (nat_lit 30465419) (nat_lit 2413370841) (nat_lit 0) D2M8K2.t13841 from rfl, allE_node, rows13840, irow13835, rows13841]
  all_goals rfl

theorem atot13835 : totK PD2M8K2 D2M8K2.u13835 = [0, 365617976325, 933272525614, 494104569672, 41179751876, 0, 0, 0] := by
  rw [show D2M8K2.u13835 = KTree.node D2M8K2.t13840 (nat_lit 30465419) (nat_lit 2413370841) (nat_lit 0) D2M8K2.t13841 from rfl, totK_node, tot13840, tot13841]
  decide +kernel

theorem arows13836 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13836 = true := by
  rw [show D2M8K2.u13836 = KTree.node D2M8K2.t13842 (nat_lit 30468466) (nat_lit 3804060900) (nat_lit 0) D2M8K2.t13843 from rfl, allE_node, rows13842, irow13836, rows13843]
  all_goals rfl

theorem atot13836 : totK PD2M8K2 D2M8K2.u13836 = [0, 365223608699, 926516339534, 488039980374, 36093550817, 0, 0, 0] := by
  rw [show D2M8K2.u13836 = KTree.node D2M8K2.t13842 (nat_lit 30468466) (nat_lit 3804060900) (nat_lit 0) D2M8K2.t13843 from rfl, totK_node, tot13842, tot13843]
  decide +kernel

theorem arows13838 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13838 = true := by
  rw [show D2M8K2.u13838 = KTree.node D2M8K2.t13844 (nat_lit 30469940) (nat_lit 3425100796) (nat_lit 0) D2M8K2.t13845 from rfl, allE_node, rows13844, irow13838, rows13845]
  all_goals rfl

theorem atot13838 : totK PD2M8K2 D2M8K2.u13838 = [0, 130629766741, 661017651435, 757011456186, 196538147181, 9579374723, 0, 0] := by
  rw [show D2M8K2.u13838 = KTree.node D2M8K2.t13844 (nat_lit 30469940) (nat_lit 3425100796) (nat_lit 0) D2M8K2.t13845 from rfl, totK_node, tot13844, tot13845]
  decide +kernel

theorem arows13839 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13839 = true := by
  rw [show D2M8K2.u13839 = KTree.node D2M8K2.t13846 (nat_lit 30475343) (nat_lit 2088782614) (nat_lit 0) D2M8K2.t13847 from rfl, allE_node, rows13846, irow13839, rows13847]
  all_goals rfl

theorem atot13839 : totK PD2M8K2 D2M8K2.u13839 = [0, 275258163732, 799228907117, 590520753436, 105662985820, 3436822651, 0, 0] := by
  rw [show D2M8K2.u13839 = KTree.node D2M8K2.t13846 (nat_lit 30475343) (nat_lit 2088782614) (nat_lit 0) D2M8K2.t13847 from rfl, totK_node, tot13846, tot13847]
  decide +kernel

theorem arows13842 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13842 = true := by
  rw [show D2M8K2.u13842 = KTree.node D2M8K2.t13848 (nat_lit 30477062) (nat_lit 3990561245) (nat_lit 0) D2M8K2.t13849 from rfl, allE_node, rows13848, irow13842, rows13849]
  all_goals rfl

theorem atot13842 : totK PD2M8K2 D2M8K2.u13842 = [0, 113606428670, 689027812104, 766098409268, 149289161294, 4574395652, 0, 0] := by
  rw [show D2M8K2.u13842 = KTree.node D2M8K2.t13848 (nat_lit 30477062) (nat_lit 3990561245) (nat_lit 0) D2M8K2.t13849 from rfl, totK_node, tot13848, tot13849]
  decide +kernel

theorem arows13843 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13843 = true := by
  rw [show D2M8K2.u13843 = KTree.node D2M8K2.t13850 (nat_lit 30479075) (nat_lit 2849658345) (nat_lit 0) D2M8K2.t13851 from rfl, allE_node, rows13850, irow13843, rows13851]
  all_goals rfl

theorem atot13843 : totK PD2M8K2 D2M8K2.u13843 = [0, 398601828613, 949035527524, 447195783818, 30699831778, 0, 0, 0] := by
  rw [show D2M8K2.u13843 = KTree.node D2M8K2.t13850 (nat_lit 30479075) (nat_lit 2849658345) (nat_lit 0) D2M8K2.t13851 from rfl, totK_node, tot13850, tot13851]
  decide +kernel

theorem arows13845 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13845 = true := by
  rw [show D2M8K2.u13845 = KTree.node D2M8K2.t13852 (nat_lit 30482934) (nat_lit 3818222609) (nat_lit 0) D2M8K2.t13853 from rfl, allE_node, rows13852, irow13845, rows13853]
  all_goals rfl

theorem atot13845 : totK PD2M8K2 D2M8K2.u13845 = [325540319114, 822015057804, 506393150375, 142017831706, 13552619715, 0, 0, 0] := by
  rw [show D2M8K2.u13845 = KTree.node D2M8K2.t13852 (nat_lit 30482934) (nat_lit 3818222609) (nat_lit 0) D2M8K2.t13853 from rfl, totK_node, tot13852, tot13853]
  decide +kernel

theorem arows13846 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13846 = true := by
  rw [show D2M8K2.u13846 = KTree.node D2M8K2.t13854 (nat_lit 30485117) (nat_lit 1632298630) (nat_lit 0) D2M8K2.t13855 from rfl, allE_node, rows13854, irow13846, rows13855]
  all_goals rfl

theorem atot13846 : totK PD2M8K2 D2M8K2.u13846 = [166263604103, 707532095587, 810209043768, 149654170137, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u13846 = KTree.node D2M8K2.t13854 (nat_lit 30485117) (nat_lit 1632298630) (nat_lit 0) D2M8K2.t13855 from rfl, totK_node, tot13854, tot13855]
  decide +kernel

theorem arows13851 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13851 = true := by
  rw [show D2M8K2.u13851 = KTree.node D2M8K2.t13856 (nat_lit 30486730) (nat_lit 2691735222) (nat_lit 0) D2M8K2.t13857 from rfl, allE_node, rows13856, irow13851, rows13857]
  all_goals rfl

theorem atot13851 : totK PD2M8K2 D2M8K2.u13851 = [262731427320, 827669115607, 602260671455, 114041365890, 13132762340, 0, 0, 0] := by
  rw [show D2M8K2.u13851 = KTree.node D2M8K2.t13856 (nat_lit 30486730) (nat_lit 2691735222) (nat_lit 0) D2M8K2.t13857 from rfl, totK_node, tot13856, tot13857]
  decide +kernel

theorem arows13852 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13852 = true := by
  rw [show D2M8K2.u13852 = KTree.node D2M8K2.t13858 (nat_lit 30488238) (nat_lit 3888402024) (nat_lit 0) D2M8K2.t13859 from rfl, allE_node, rows13858, irow13852, rows13859]
  all_goals rfl

theorem atot13852 : totK PD2M8K2 D2M8K2.u13852 = [28108375666, 370790325855, 902143389867, 466273295236, 24462327659, 0, 0, 0] := by
  rw [show D2M8K2.u13852 = KTree.node D2M8K2.t13858 (nat_lit 30488238) (nat_lit 3888402024) (nat_lit 0) D2M8K2.t13859 from rfl, totK_node, tot13858, tot13859]
  decide +kernel

theorem arows13854 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13854 = true := by
  rw [show D2M8K2.u13854 = KTree.node D2M8K2.t13860 (nat_lit 30493230) (nat_lit 4086215485) (nat_lit 0) D2M8K2.t13861 from rfl, allE_node, rows13860, irow13854, rows13861]
  all_goals rfl

theorem atot13854 : totK PD2M8K2 D2M8K2.u13854 = [379883085916, 937925650351, 476655835246, 35702429272, 0, 0, 0, 0] := by
  rw [show D2M8K2.u13854 = KTree.node D2M8K2.t13860 (nat_lit 30493230) (nat_lit 4086215485) (nat_lit 0) D2M8K2.t13861 from rfl, totK_node, tot13860, tot13861]
  decide +kernel

theorem arows13855 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13855 = true := by
  rw [show D2M8K2.u13855 = KTree.node D2M8K2.t13862 (nat_lit 30494442) (nat_lit 3808223712) (nat_lit 0) D2M8K2.t13863 from rfl, allE_node, rows13862, irow13855, rows13863]
  all_goals rfl

theorem atot13855 : totK PD2M8K2 D2M8K2.u13855 = [30583749538, 511409054452, 928775107520, 290127056236, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u13855 = KTree.node D2M8K2.t13862 (nat_lit 30494442) (nat_lit 3808223712) (nat_lit 0) D2M8K2.t13863 from rfl, totK_node, tot13862, tot13863]
  decide +kernel

theorem arows13858 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13858 = true := by
  rw [show D2M8K2.u13858 = KTree.node D2M8K2.t13864 (nat_lit 30496277) (nat_lit 2250642806) (nat_lit 0) D2M8K2.t13865 from rfl, allE_node, rows13864, irow13858, rows13865]
  all_goals rfl

theorem atot13858 : totK PD2M8K2 D2M8K2.u13858 = [335058917367, 881089325446, 547978833412, 63456862274, 0, 0, 0, 0] := by
  rw [show D2M8K2.u13858 = KTree.node D2M8K2.t13864 (nat_lit 30496277) (nat_lit 2250642806) (nat_lit 0) D2M8K2.t13865 from rfl, totK_node, tot13864, tot13865]
  decide +kernel

theorem arows13859 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13859 = true := by
  rw [show D2M8K2.u13859 = KTree.node D2M8K2.t13866 (nat_lit 30498105) (nat_lit 1852697587) (nat_lit 0) D2M8K2.t13867 from rfl, allE_node, rows13866, irow13859, rows13867]
  all_goals rfl

theorem atot13859 : totK PD2M8K2 D2M8K2.u13859 = [110441453076, 638712783199, 833890476735, 192993355027, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u13859 = KTree.node D2M8K2.t13866 (nat_lit 30498105) (nat_lit 1852697587) (nat_lit 0) D2M8K2.t13867 from rfl, totK_node, tot13866, tot13867]
  decide +kernel

theorem arows13861 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13861 = true := by
  rw [show D2M8K2.u13861 = KTree.node D2M8K2.t13868 (nat_lit 30499946) (nat_lit 4163998324) (nat_lit 0) D2M8K2.t13869 from rfl, allE_node, rows13868, irow13861, rows13869]
  all_goals rfl

theorem atot13861 : totK PD2M8K2 D2M8K2.u13861 = [351502754951, 941980454266, 515832828606, 38783660338, 0, 0, 0, 0] := by
  rw [show D2M8K2.u13861 = KTree.node D2M8K2.t13868 (nat_lit 30499946) (nat_lit 4163998324) (nat_lit 0) D2M8K2.t13869 from rfl, totK_node, tot13868, tot13869]
  decide +kernel

theorem arows13862 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13862 = true := by
  rw [show D2M8K2.u13862 = KTree.node D2M8K2.t13870 (nat_lit 30501641) (nat_lit 1629246227) (nat_lit 0) D2M8K2.t13871 from rfl, allE_node, rows13870, irow13862, rows13871]
  all_goals rfl

theorem atot13862 : totK PD2M8K2 D2M8K2.u13862 = [0, 453943584563, 991076721619, 335940909320, 9912687053, 0, 0, 0] := by
  rw [show D2M8K2.u13862 = KTree.node D2M8K2.t13870 (nat_lit 30501641) (nat_lit 1629246227) (nat_lit 0) D2M8K2.t13871 from rfl, totK_node, tot13870, tot13871]
  decide +kernel

theorem arows13866 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13866 = true := by
  rw [show D2M8K2.u13866 = KTree.node D2M8K2.t13872 (nat_lit 30503772) (nat_lit 2799465447) (nat_lit 0) D2M8K2.t13873 from rfl, allE_node, rows13872, irow13866, rows13873]
  all_goals rfl

theorem atot13866 : totK PD2M8K2 D2M8K2.u13866 = [0, 324541162239, 910065382832, 515384638630, 37263568873, 0, 0, 0] := by
  rw [show D2M8K2.u13866 = KTree.node D2M8K2.t13872 (nat_lit 30503772) (nat_lit 2799465447) (nat_lit 0) D2M8K2.t13873 from rfl, totK_node, tot13872, tot13873]
  decide +kernel

theorem arows13867 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13867 = true := by
  rw [show D2M8K2.u13867 = KTree.node D2M8K2.t13874 (nat_lit 30506440) (nat_lit 3831628960) (nat_lit 0) D2M8K2.t13875 from rfl, allE_node, rows13874, irow13867, rows13875]
  all_goals rfl

theorem atot13867 : totK PD2M8K2 D2M8K2.u13867 = [0, 199469114449, 743605763953, 736775479948, 118280206225, 1239866073, 0, 0] := by
  rw [show D2M8K2.u13867 = KTree.node D2M8K2.t13874 (nat_lit 30506440) (nat_lit 3831628960) (nat_lit 0) D2M8K2.t13875 from rfl, totK_node, tot13874, tot13875]
  decide +kernel

theorem arows13869 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13869 = true := by
  rw [show D2M8K2.u13869 = KTree.node D2M8K2.t13876 (nat_lit 30507630) (nat_lit 4025775211) (nat_lit 0) D2M8K2.t13877 from rfl, allE_node, rows13876, irow13869, rows13877]
  all_goals rfl

theorem atot13869 : totK PD2M8K2 D2M8K2.u13869 = [0, 398984086062, 957969749904, 428282755365, 24172565483, 0, 0, 0] := by
  rw [show D2M8K2.u13869 = KTree.node D2M8K2.t13876 (nat_lit 30507630) (nat_lit 4025775211) (nat_lit 0) D2M8K2.t13877 from rfl, totK_node, tot13876, tot13877]
  decide +kernel

theorem arows13870 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13870 = true := by
  rw [show D2M8K2.u13870 = KTree.node D2M8K2.t13878 (nat_lit 30514272) (nat_lit 3540521261) (nat_lit 0) D2M8K2.t13879 from rfl, allE_node, rows13878, irow13870, rows13879]
  all_goals rfl

theorem atot13870 : totK PD2M8K2 D2M8K2.u13870 = [0, 266157842115, 860988829050, 607562309291, 58705673916, 0, 0, 0] := by
  rw [show D2M8K2.u13870 = KTree.node D2M8K2.t13878 (nat_lit 30514272) (nat_lit 3540521261) (nat_lit 0) D2M8K2.t13879 from rfl, totK_node, tot13878, tot13879]
  decide +kernel

theorem arows13873 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13873 = true := by
  rw [show D2M8K2.u13873 = KTree.node D2M8K2.t13880 (nat_lit 30515964) (nat_lit 1971998150) (nat_lit 0) D2M8K2.t13881 from rfl, allE_node, rows13880, irow13873, rows13881]
  all_goals rfl

theorem atot13873 : totK PD2M8K2 D2M8K2.u13873 = [0, 110652807981, 569900261892, 795771611508, 257423841066, 13105450397, 0, 0] := by
  rw [show D2M8K2.u13873 = KTree.node D2M8K2.t13880 (nat_lit 30515964) (nat_lit 1971998150) (nat_lit 0) D2M8K2.t13881 from rfl, totK_node, tot13880, tot13881]
  decide +kernel

theorem arows13874 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13874 = true := by
  rw [show D2M8K2.u13874 = KTree.node D2M8K2.t13882 (nat_lit 30517567) (nat_lit 2438396026) (nat_lit 0) D2M8K2.t13883 from rfl, allE_node, rows13882, irow13874, rows13883]
  all_goals rfl

theorem atot13874 : totK PD2M8K2 D2M8K2.u13874 = [0, 270776488993, 857508705273, 584026945228, 72307029416, 1053411165, 0, 0] := by
  rw [show D2M8K2.u13874 = KTree.node D2M8K2.t13882 (nat_lit 30517567) (nat_lit 2438396026) (nat_lit 0) D2M8K2.t13883 from rfl, totK_node, tot13882, tot13883]
  decide +kernel

theorem arows13876 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13876 = true := by
  rw [show D2M8K2.u13876 = KTree.node D2M8K2.t13884 (nat_lit 30519987) (nat_lit 2373394722) (nat_lit 0) D2M8K2.t13885 from rfl, allE_node, rows13884, irow13876, rows13885]
  all_goals rfl

theorem atot13876 : totK PD2M8K2 D2M8K2.u13876 = [0, 213841685965, 742259244833, 689806804051, 121967314659, 3667207281, 0, 0] := by
  rw [show D2M8K2.u13876 = KTree.node D2M8K2.t13884 (nat_lit 30519987) (nat_lit 2373394722) (nat_lit 0) D2M8K2.t13885 from rfl, totK_node, tot13884, tot13885]
  decide +kernel

theorem arows13877 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13877 = true := by
  rw [show D2M8K2.u13877 = KTree.node D2M8K2.t13886 (nat_lit 30521514) (nat_lit 3837906860) (nat_lit 0) D2M8K2.t13887 from rfl, allE_node, rows13886, irow13877, rows13887]
  all_goals rfl

theorem atot13877 : totK PD2M8K2 D2M8K2.u13877 = [159085141884, 533675992045, 769641265019, 358000385732, 25902279123, 0, 0, 0] := by
  rw [show D2M8K2.u13877 = KTree.node D2M8K2.t13886 (nat_lit 30521514) (nat_lit 3837906860) (nat_lit 0) D2M8K2.t13887 from rfl, totK_node, tot13886, tot13887]
  decide +kernel

theorem arows13883 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13883 = true := by
  rw [show D2M8K2.u13883 = KTree.node D2M8K2.t13888 (nat_lit 30528097) (nat_lit 1425718545) (nat_lit 0) D2M8K2.t13889 from rfl, allE_node, rows13888, irow13883, rows13889]
  all_goals rfl

theorem atot13883 : totK PD2M8K2 D2M8K2.u13883 = [270042701698, 865537069607, 601253719770, 84515008039, 5319205844, 0, 0, 0] := by
  rw [show D2M8K2.u13883 = KTree.node D2M8K2.t13888 (nat_lit 30528097) (nat_lit 1425718545) (nat_lit 0) D2M8K2.t13889 from rfl, totK_node, tot13888, tot13889]
  decide +kernel

theorem arows13884 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13884 = true := by
  rw [show D2M8K2.u13884 = KTree.node D2M8K2.t13890 (nat_lit 30529618) (nat_lit 3877721196) (nat_lit 0) D2M8K2.t13891 from rfl, allE_node, rows13890, irow13884, rows13891]
  all_goals rfl

theorem atot13884 : totK PD2M8K2 D2M8K2.u13884 = [3757117624, 334730544830, 920667032022, 505015070954, 30584428395, 0, 0, 0] := by
  rw [show D2M8K2.u13884 = KTree.node D2M8K2.t13890 (nat_lit 30529618) (nat_lit 3877721196) (nat_lit 0) D2M8K2.t13891 from rfl, totK_node, tot13890, tot13891]
  decide +kernel

theorem arows13886 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13886 = true := by
  rw [show D2M8K2.u13886 = KTree.node D2M8K2.t13892 (nat_lit 30530932) (nat_lit 4076853445) (nat_lit 0) D2M8K2.t13893 from rfl, allE_node, rows13892, irow13886, rows13893]
  all_goals rfl

theorem atot13886 : totK PD2M8K2 D2M8K2.u13886 = [383052553826, 933004644430, 466914879672, 35633719015, 0, 0, 0, 0] := by
  rw [show D2M8K2.u13886 = KTree.node D2M8K2.t13892 (nat_lit 30530932) (nat_lit 4076853445) (nat_lit 0) D2M8K2.t13893 from rfl, totK_node, tot13892, tot13893]
  decide +kernel

theorem arows13887 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13887 = true := by
  rw [show D2M8K2.u13887 = KTree.node D2M8K2.t13894 (nat_lit 30532676) (nat_lit 3341709948) (nat_lit 0) D2M8K2.t13895 from rfl, allE_node, rows13894, irow13887, rows13895]
  all_goals rfl

theorem atot13887 : totK PD2M8K2 D2M8K2.u13887 = [21736622203, 498924941811, 943111820282, 295635853972, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u13887 = KTree.node D2M8K2.t13894 (nat_lit 30532676) (nat_lit 3341709948) (nat_lit 0) D2M8K2.t13895 from rfl, totK_node, tot13894, tot13895]
  decide +kernel

theorem arows13890 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13890 = true := by
  rw [show D2M8K2.u13890 = KTree.node D2M8K2.t13896 (nat_lit 30534706) (nat_lit 3909336635) (nat_lit 0) D2M8K2.t13897 from rfl, allE_node, rows13896, irow13890, rows13897]
  all_goals rfl

theorem atot13890 : totK PD2M8K2 D2M8K2.u13890 = [383927825964, 936004590935, 469166576521, 35773738642, 0, 0, 0, 0] := by
  rw [show D2M8K2.u13890 = KTree.node D2M8K2.t13896 (nat_lit 30534706) (nat_lit 3909336635) (nat_lit 0) D2M8K2.t13897 from rfl, totK_node, tot13896, tot13897]
  decide +kernel

theorem arows13891 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13891 = true := by
  rw [show D2M8K2.u13891 = KTree.node D2M8K2.t13898 (nat_lit 30536446) (nat_lit 3824633197) (nat_lit 0) D2M8K2.t13899 from rfl, allE_node, rows13898, irow13891, rows13899]
  all_goals rfl

theorem atot13891 : totK PD2M8K2 D2M8K2.u13891 = [11678264543, 495015713234, 947654332675, 305923756675, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u13891 = KTree.node D2M8K2.t13898 (nat_lit 30536446) (nat_lit 3824633197) (nat_lit 0) D2M8K2.t13899 from rfl, totK_node, tot13898, tot13899]
  decide +kernel

theorem arows13893 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13893 = true := by
  rw [show D2M8K2.u13893 = KTree.node D2M8K2.t13900 (nat_lit 30537842) (nat_lit 4057731248) (nat_lit 0) D2M8K2.t13901 from rfl, allE_node, rows13900, irow13893, rows13901]
  all_goals rfl

theorem atot13893 : totK PD2M8K2 D2M8K2.u13893 = [375594269445, 923398915633, 480928436894, 40341077072, 0, 0, 0, 0] := by
  rw [show D2M8K2.u13893 = KTree.node D2M8K2.t13900 (nat_lit 30537842) (nat_lit 4057731248) (nat_lit 0) D2M8K2.t13901 from rfl, totK_node, tot13900, tot13901]
  decide +kernel

theorem arows13894 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13894 = true := by
  rw [show D2M8K2.u13894 = KTree.node D2M8K2.t13902 (nat_lit 30539552) (nat_lit 3762414333) (nat_lit 0) D2M8K2.t13903 from rfl, allE_node, rows13902, irow13894, rows13903]
  all_goals rfl

theorem atot13894 : totK PD2M8K2 D2M8K2.u13894 = [37683970795, 614018123995, 937718124609, 216454010623, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u13894 = KTree.node D2M8K2.t13902 (nat_lit 30539552) (nat_lit 3762414333) (nat_lit 0) D2M8K2.t13903 from rfl, totK_node, tot13902, tot13903]
  decide +kernel

theorem arows13898 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13898 = true := by
  rw [show D2M8K2.u13898 = KTree.node D2M8K2.t13904 (nat_lit 30548482) (nat_lit 3919879030) (nat_lit 0) D2M8K2.t13905 from rfl, allE_node, rows13904, irow13898, rows13905]
  all_goals rfl

theorem atot13898 : totK PD2M8K2 D2M8K2.u13898 = [0, 371145688534, 939585562558, 469091283089, 39365663268, 0, 0, 0] := by
  rw [show D2M8K2.u13898 = KTree.node D2M8K2.t13904 (nat_lit 30548482) (nat_lit 3919879030) (nat_lit 0) D2M8K2.t13905 from rfl, totK_node, tot13904, tot13905]
  decide +kernel

theorem arows13899 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13899 = true := by
  rw [show D2M8K2.u13899 = KTree.node D2M8K2.t13906 (nat_lit 30551552) (nat_lit 3598993038) (nat_lit 0) D2M8K2.t13907 from rfl, allE_node, rows13906, irow13899, rows13907]
  all_goals rfl

theorem atot13899 : totK PD2M8K2 D2M8K2.u13899 = [0, 351864468952, 940833011408, 479653981269, 27593746489, 0, 0, 0] := by
  rw [show D2M8K2.u13899 = KTree.node D2M8K2.t13906 (nat_lit 30551552) (nat_lit 3598993038) (nat_lit 0) D2M8K2.t13907 from rfl, totK_node, tot13906, tot13907]
  decide +kernel

theorem arows13901 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13901 = true := by
  rw [show D2M8K2.u13901 = KTree.node D2M8K2.t13908 (nat_lit 30554910) (nat_lit 3880565180) (nat_lit 0) D2M8K2.t13909 from rfl, allE_node, rows13908, irow13901, rows13909]
  all_goals rfl

theorem atot13901 : totK PD2M8K2 D2M8K2.u13901 = [0, 401900785898, 939672739236, 449026626317, 26166128033, 0, 0, 0] := by
  rw [show D2M8K2.u13901 = KTree.node D2M8K2.t13908 (nat_lit 30554910) (nat_lit 3880565180) (nat_lit 0) D2M8K2.t13909 from rfl, totK_node, tot13908, tot13909]
  decide +kernel

theorem arows13902 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13902 = true := by
  rw [show D2M8K2.u13902 = KTree.node D2M8K2.t13910 (nat_lit 30558285) (nat_lit 1496740031) (nat_lit 0) D2M8K2.t13911 from rfl, allE_node, rows13910, irow13902, rows13911]
  all_goals rfl

theorem atot13902 : totK PD2M8K2 D2M8K2.u13902 = [0, 334569890023, 934446586147, 482761261472, 31788232132, 0, 0, 0] := by
  rw [show D2M8K2.u13902 = KTree.node D2M8K2.t13910 (nat_lit 30558285) (nat_lit 1496740031) (nat_lit 0) D2M8K2.t13911 from rfl, totK_node, tot13910, tot13911]
  decide +kernel

theorem arows13905 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13905 = true := by
  rw [show D2M8K2.u13905 = KTree.node D2M8K2.t13912 (nat_lit 30559750) (nat_lit 1626629979) (nat_lit 0) D2M8K2.t13913 from rfl, allE_node, rows13912, irow13905, rows13913]
  all_goals rfl

theorem atot13905 : totK PD2M8K2 D2M8K2.u13905 = [0, 154569040053, 761561478789, 725211219569, 109525334198, 1095107716, 0, 0] := by
  rw [show D2M8K2.u13905 = KTree.node D2M8K2.t13912 (nat_lit 30559750) (nat_lit 1626629979) (nat_lit 0) D2M8K2.t13913 from rfl, totK_node, tot13912, tot13913]
  decide +kernel

theorem arows13906 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13906 = true := by
  rw [show D2M8K2.u13906 = KTree.node D2M8K2.t13914 (nat_lit 30565508) (nat_lit 3216500022) (nat_lit 0) D2M8K2.t13915 from rfl, allE_node, rows13914, irow13906, rows13915]
  all_goals rfl

theorem atot13906 : totK PD2M8K2 D2M8K2.u13906 = [326941405754, 760978098082, 403523631134, 216429682422, 88452003642, 3882006667, 0, 0] := by
  rw [show D2M8K2.u13906 = KTree.node D2M8K2.t13914 (nat_lit 30565508) (nat_lit 3216500022) (nat_lit 0) D2M8K2.t13915 from rfl, totK_node, tot13914, tot13915]
  decide +kernel

theorem arows13908 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13908 = true := by
  rw [show D2M8K2.u13908 = KTree.node D2M8K2.t13916 (nat_lit 30567472) (nat_lit 2601861988) (nat_lit 0) D2M8K2.t13917 from rfl, allE_node, rows13916, irow13908, rows13917]
  all_goals rfl

theorem atot13908 : totK PD2M8K2 D2M8K2.u13908 = [105588958979, 695083536818, 881157921860, 157763797228, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u13908 = KTree.node D2M8K2.t13916 (nat_lit 30567472) (nat_lit 2601861988) (nat_lit 0) D2M8K2.t13917 from rfl, totK_node, tot13916, tot13917]
  decide +kernel

theorem arows13909 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13909 = true := by
  rw [show D2M8K2.u13909 = KTree.node D2M8K2.t13918 (nat_lit 30569498) (nat_lit 4241602830) (nat_lit 0) D2M8K2.t13919 from rfl, allE_node, rows13918, irow13909, rows13919]
  all_goals rfl

theorem atot13909 : totK PD2M8K2 D2M8K2.u13909 = [337254317224, 910404203682, 529461746096, 51821018729, 0, 0, 0, 0] := by
  rw [show D2M8K2.u13909 = KTree.node D2M8K2.t13918 (nat_lit 30569498) (nat_lit 4241602830) (nat_lit 0) D2M8K2.t13919 from rfl, totK_node, tot13918, tot13919]
  decide +kernel

theorem arows13914 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13914 = true := by
  rw [show D2M8K2.u13914 = KTree.node D2M8K2.t13920 (nat_lit 30570959) (nat_lit 2122592225) (nat_lit 0) D2M8K2.t13921 from rfl, allE_node, rows13920, irow13914, rows13921]
  all_goals rfl

theorem atot13914 : totK PD2M8K2 D2M8K2.u13914 = [0, 391112407816, 942976465106, 448378891396, 30784502143, 0, 0, 0] := by
  rw [show D2M8K2.u13914 = KTree.node D2M8K2.t13920 (nat_lit 30570959) (nat_lit 2122592225) (nat_lit 0) D2M8K2.t13921 from rfl, totK_node, tot13920, tot13921]
  decide +kernel

theorem arows13915 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13915 = true := by
  rw [show D2M8K2.u13915 = KTree.node D2M8K2.t13922 (nat_lit 30572287) (nat_lit 2322872439) (nat_lit 0) D2M8K2.t13923 from rfl, allE_node, rows13922, irow13915, rows13923]
  all_goals rfl

theorem atot13915 : totK PD2M8K2 D2M8K2.u13915 = [325509124295, 834244145438, 515956624397, 121123469392, 6804944647, 0, 0, 0] := by
  rw [show D2M8K2.u13915 = KTree.node D2M8K2.t13922 (nat_lit 30572287) (nat_lit 2322872439) (nat_lit 0) D2M8K2.t13923 from rfl, totK_node, tot13922, tot13923]
  decide +kernel

theorem arows13917 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13917 = true := by
  rw [show D2M8K2.u13917 = KTree.node D2M8K2.t13924 (nat_lit 30573860) (nat_lit 3230971836) (nat_lit 0) D2M8K2.t13925 from rfl, allE_node, rows13924, irow13917, rows13925]
  all_goals rfl

theorem atot13917 : totK PD2M8K2 D2M8K2.u13917 = [89359567243, 553348220250, 869521212933, 266217850358, 11405513407, 0, 0, 0] := by
  rw [show D2M8K2.u13917 = KTree.node D2M8K2.t13924 (nat_lit 30573860) (nat_lit 3230971836) (nat_lit 0) D2M8K2.t13925 from rfl, totK_node, tot13924, tot13925]
  decide +kernel

theorem arows13918 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13918 = true := by
  rw [show D2M8K2.u13918 = KTree.node D2M8K2.t13926 (nat_lit 30575709) (nat_lit 1391361936) (nat_lit 0) D2M8K2.t13927 from rfl, allE_node, rows13926, irow13918, rows13927]
  all_goals rfl

theorem atot13918 : totK PD2M8K2 D2M8K2.u13918 = [325735381765, 893005384005, 550535931168, 57340759425, 1503132863, 0, 0, 0] := by
  rw [show D2M8K2.u13918 = KTree.node D2M8K2.t13926 (nat_lit 30575709) (nat_lit 1391361936) (nat_lit 0) D2M8K2.t13927 from rfl, totK_node, tot13926, tot13927]
  decide +kernel

theorem arows13921 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13921 = true := by
  rw [show D2M8K2.u13921 = KTree.node D2M8K2.t13928 (nat_lit 30577286) (nat_lit 4179183593) (nat_lit 0) D2M8K2.t13929 from rfl, allE_node, rows13928, irow13921, rows13929]
  all_goals rfl

theorem atot13921 : totK PD2M8K2 D2M8K2.u13921 = [89381903860, 585866677031, 865234345220, 246996499221, 10657629514, 0, 0, 0] := by
  rw [show D2M8K2.u13921 = KTree.node D2M8K2.t13928 (nat_lit 30577286) (nat_lit 4179183593) (nat_lit 0) D2M8K2.t13929 from rfl, totK_node, tot13928, tot13929]
  decide +kernel

theorem arows13922 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13922 = true := by
  rw [show D2M8K2.u13922 = KTree.node D2M8K2.t13930 (nat_lit 30582555) (nat_lit 3696492614) (nat_lit 0) D2M8K2.t13931 from rfl, allE_node, rows13930, irow13922, rows13931]
  all_goals rfl

theorem atot13922 : totK PD2M8K2 D2M8K2.u13922 = [330657515537, 862677044250, 555780986047, 87311541073, 2426968038, 0, 0, 0] := by
  rw [show D2M8K2.u13922 = KTree.node D2M8K2.t13930 (nat_lit 30582555) (nat_lit 3696492614) (nat_lit 0) D2M8K2.t13931 from rfl, totK_node, tot13930, tot13931]
  decide +kernel

theorem arows13924 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13924 = true := by
  rw [show D2M8K2.u13924 = KTree.node D2M8K2.t13932 (nat_lit 30583994) (nat_lit 3455868687) (nat_lit 0) D2M8K2.t13933 from rfl, allE_node, rows13932, irow13924, rows13933]
  all_goals rfl

theorem atot13924 : totK PD2M8K2 D2M8K2.u13924 = [112776311510, 645169654395, 843462716749, 206778719119, 4967996017, 0, 0, 0] := by
  rw [show D2M8K2.u13924 = KTree.node D2M8K2.t13932 (nat_lit 30583994) (nat_lit 3455868687) (nat_lit 0) D2M8K2.t13933 from rfl, totK_node, tot13932, tot13933]
  decide +kernel

theorem arows13925 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13925 = true := by
  rw [show D2M8K2.u13925 = KTree.node D2M8K2.t13934 (nat_lit 30585661) (nat_lit 1231020925) (nat_lit 0) D2M8K2.t13935 from rfl, allE_node, rows13934, irow13925, rows13935]
  all_goals rfl

theorem atot13925 : totK PD2M8K2 D2M8K2.u13925 = [0, 397227826650, 954998326379, 417745915972, 22416853141, 0, 0, 0] := by
  rw [show D2M8K2.u13925 = KTree.node D2M8K2.t13934 (nat_lit 30585661) (nat_lit 1231020925) (nat_lit 0) D2M8K2.t13935 from rfl, totK_node, tot13934, tot13935]
  decide +kernel

theorem arows13929 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13929 = true := by
  rw [show D2M8K2.u13929 = KTree.node D2M8K2.t13936 (nat_lit 30587473) (nat_lit 1545975605) (nat_lit 0) D2M8K2.t13937 from rfl, allE_node, rows13936, irow13929, rows13937]
  all_goals rfl

theorem atot13929 : totK PD2M8K2 D2M8K2.u13929 = [0, 138692543508, 722383467585, 821312693879, 121309581951, 1310285577, 0, 0] := by
  rw [show D2M8K2.u13929 = KTree.node D2M8K2.t13936 (nat_lit 30587473) (nat_lit 1545975605) (nat_lit 0) D2M8K2.t13937 from rfl, totK_node, tot13936, tot13937]
  decide +kernel

theorem arows13930 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13930 = true := by
  rw [show D2M8K2.u13930 = KTree.node D2M8K2.t13938 (nat_lit 30589954) (nat_lit 3995497417) (nat_lit 0) D2M8K2.t13939 from rfl, allE_node, rows13938, irow13930, rows13939]
  all_goals rfl

theorem atot13930 : totK PD2M8K2 D2M8K2.u13930 = [0, 378696366330, 933411713459, 483696381034, 36620346920, 0, 0, 0] := by
  rw [show D2M8K2.u13930 = KTree.node D2M8K2.t13938 (nat_lit 30589954) (nat_lit 3995497417) (nat_lit 0) D2M8K2.t13939 from rfl, totK_node, tot13938, tot13939]
  decide +kernel

theorem arows13932 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13932 = true := by
  rw [show D2M8K2.u13932 = KTree.node D2M8K2.t13940 (nat_lit 30592988) (nat_lit 3403179886) (nat_lit 0) D2M8K2.t13941 from rfl, allE_node, rows13940, irow13932, rows13941]
  all_goals rfl

theorem atot13932 : totK PD2M8K2 D2M8K2.u13932 = [0, 332470257655, 915613347508, 517308388908, 43752990607, 0, 0, 0] := by
  rw [show D2M8K2.u13932 = KTree.node D2M8K2.t13940 (nat_lit 30592988) (nat_lit 3403179886) (nat_lit 0) D2M8K2.t13941 from rfl, totK_node, tot13940, tot13941]
  decide +kernel

theorem arows13933 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13933 = true := by
  rw [show D2M8K2.u13933 = KTree.node D2M8K2.t13942 (nat_lit 30594572) (nat_lit 2803303301) (nat_lit 0) D2M8K2.t13943 from rfl, allE_node, rows13942, irow13933, rows13943]
  all_goals rfl

theorem atot13933 : totK PD2M8K2 D2M8K2.u13933 = [0, 89165724567, 647497528787, 845880653344, 174783769621, 4879840392, 0, 0] := by
  rw [show D2M8K2.u13933 = KTree.node D2M8K2.t13942 (nat_lit 30594572) (nat_lit 2803303301) (nat_lit 0) D2M8K2.t13943 from rfl, totK_node, tot13942, tot13943]
  decide +kernel

theorem arows13936 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13936 = true := by
  rw [show D2M8K2.u13936 = KTree.node D2M8K2.t13944 (nat_lit 30596843) (nat_lit 2888309552) (nat_lit 0) D2M8K2.t13945 from rfl, allE_node, rows13944, irow13936, rows13945]
  all_goals rfl

theorem atot13936 : totK PD2M8K2 D2M8K2.u13936 = [0, 383164028360, 920123610078, 468191650617, 40231085393, 0, 0, 0] := by
  rw [show D2M8K2.u13936 = KTree.node D2M8K2.t13944 (nat_lit 30596843) (nat_lit 2888309552) (nat_lit 0) D2M8K2.t13945 from rfl, totK_node, tot13944, tot13945]
  decide +kernel

theorem arows13937 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13937 = true := by
  rw [show D2M8K2.u13937 = KTree.node D2M8K2.t13946 (nat_lit 30598595) (nat_lit 2675149644) (nat_lit 0) D2M8K2.t13947 from rfl, allE_node, rows13946, irow13937, rows13947]
  all_goals rfl

theorem atot13937 : totK PD2M8K2 D2M8K2.u13937 = [0, 105994366232, 646403960145, 825887218608, 181312756883, 4931404646, 0, 0] := by
  rw [show D2M8K2.u13937 = KTree.node D2M8K2.t13946 (nat_lit 30598595) (nat_lit 2675149644) (nat_lit 0) D2M8K2.t13947 from rfl, totK_node, tot13946, tot13947]
  decide +kernel

theorem arows13939 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13939 = true := by
  rw [show D2M8K2.u13939 = KTree.node D2M8K2.t13948 (nat_lit 30603598) (nat_lit 4022490277) (nat_lit 0) D2M8K2.t13949 from rfl, allE_node, rows13948, irow13939, rows13949]
  all_goals rfl

theorem atot13939 : totK PD2M8K2 D2M8K2.u13939 = [0, 362666900683, 948830013415, 487608715039, 32631574802, 0, 0, 0] := by
  rw [show D2M8K2.u13939 = KTree.node D2M8K2.t13948 (nat_lit 30603598) (nat_lit 4022490277) (nat_lit 0) D2M8K2.t13949 from rfl, totK_node, tot13948, tot13949]
  decide +kernel

theorem arows13940 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13940 = true := by
  rw [show D2M8K2.u13940 = KTree.node D2M8K2.t13950 (nat_lit 30605243) (nat_lit 2879332006) (nat_lit 0) D2M8K2.t13951 from rfl, allE_node, rows13950, irow13940, rows13951]
  all_goals rfl

theorem atot13940 : totK PD2M8K2 D2M8K2.u13940 = [0, 0, 506313241494, 969738021043, 270819296305, 8424427256, 0, 0] := by
  rw [show D2M8K2.u13940 = KTree.node D2M8K2.t13950 (nat_lit 30605243) (nat_lit 2879332006) (nat_lit 0) D2M8K2.t13951 from rfl, totK_node, tot13950, tot13951]
  decide +kernel

theorem arows13947 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13947 = true := by
  rw [show D2M8K2.u13947 = KTree.node D2M8K2.t13952 (nat_lit 30651944) (nat_lit 3883430745) (nat_lit 0) D2M8K2.t13953 from rfl, allE_node, rows13952, irow13947, rows13953]
  all_goals rfl

theorem atot13947 : totK PD2M8K2 D2M8K2.u13947 = [0, 344167777839, 807150520135, 525001850640, 147664128431, 13326740810, 0, 0] := by
  rw [show D2M8K2.u13947 = KTree.node D2M8K2.t13952 (nat_lit 30651944) (nat_lit 3883430745) (nat_lit 0) D2M8K2.t13953 from rfl, totK_node, tot13952, tot13953]
  decide +kernel

theorem arows13948 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13948 = true := by
  rw [show D2M8K2.u13948 = KTree.node D2M8K2.t13954 (nat_lit 30653410) (nat_lit 4158981226) (nat_lit 0) D2M8K2.t13955 from rfl, allE_node, rows13954, irow13948, rows13955]
  all_goals rfl

theorem atot13948 : totK PD2M8K2 D2M8K2.u13948 = [0, 105275039477, 612101590215, 793044703666, 297600495555, 25373788367, 0, 0] := by
  rw [show D2M8K2.u13948 = KTree.node D2M8K2.t13954 (nat_lit 30653410) (nat_lit 4158981226) (nat_lit 0) D2M8K2.t13955 from rfl, totK_node, tot13954, tot13955]
  decide +kernel

theorem arows13950 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13950 = true := by
  rw [show D2M8K2.u13950 = KTree.node D2M8K2.t13956 (nat_lit 30654634) (nat_lit 3929323232) (nat_lit 0) D2M8K2.t13957 from rfl, allE_node, rows13956, irow13950, rows13957]
  all_goals rfl

theorem atot13950 : totK PD2M8K2 D2M8K2.u13950 = [0, 159862974851, 583097859145, 767412619107, 297885010035, 12235609738, 0, 0] := by
  rw [show D2M8K2.u13950 = KTree.node D2M8K2.t13956 (nat_lit 30654634) (nat_lit 3929323232) (nat_lit 0) D2M8K2.t13957 from rfl, totK_node, tot13956, tot13957]
  decide +kernel

theorem arows13951 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13951 = true := by
  rw [show D2M8K2.u13951 = KTree.node D2M8K2.t13958 (nat_lit 30656180) (nat_lit 1848480433) (nat_lit 0) D2M8K2.t13959 from rfl, allE_node, rows13958, irow13951, rows13959]
  all_goals rfl

theorem atot13951 : totK PD2M8K2 D2M8K2.u13951 = [0, 260243439095, 817027444611, 628457516018, 85460239757, 0, 0, 0] := by
  rw [show D2M8K2.u13951 = KTree.node D2M8K2.t13958 (nat_lit 30656180) (nat_lit 1848480433) (nat_lit 0) D2M8K2.t13959 from rfl, totK_node, tot13958, tot13959]
  decide +kernel

theorem arows13954 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13954 = true := by
  rw [show D2M8K2.u13954 = KTree.node D2M8K2.t13960 (nat_lit 30657901) (nat_lit 1264980322) (nat_lit 0) D2M8K2.t13961 from rfl, allE_node, rows13960, irow13954, rows13961]
  all_goals rfl

theorem atot13954 : totK PD2M8K2 D2M8K2.u13954 = [0, 156490729458, 642854588045, 758938710786, 222402133564, 8706415949, 0, 0] := by
  rw [show D2M8K2.u13954 = KTree.node D2M8K2.t13960 (nat_lit 30657901) (nat_lit 1264980322) (nat_lit 0) D2M8K2.t13961 from rfl, totK_node, tot13960, tot13961]
  decide +kernel

theorem arows13955 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13955 = true := by
  rw [show D2M8K2.u13955 = KTree.node D2M8K2.t13962 (nat_lit 30659554) (nat_lit 3257142037) (nat_lit 0) D2M8K2.t13963 from rfl, allE_node, rows13962, irow13955, rows13963]
  all_goals rfl

theorem atot13955 : totK PD2M8K2 D2M8K2.u13955 = [0, 263845017462, 813276937906, 629309912295, 86162784300, 0, 0, 0] := by
  rw [show D2M8K2.u13955 = KTree.node D2M8K2.t13962 (nat_lit 30659554) (nat_lit 3257142037) (nat_lit 0) D2M8K2.t13963 from rfl, totK_node, tot13962, tot13963]
  decide +kernel

theorem arows13957 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13957 = true := by
  rw [show D2M8K2.u13957 = KTree.node D2M8K2.t13964 (nat_lit 30661273) (nat_lit 1351283934) (nat_lit 0) D2M8K2.t13965 from rfl, allE_node, rows13964, irow13957, rows13965]
  all_goals rfl

theorem atot13957 : totK PD2M8K2 D2M8K2.u13957 = [0, 141137605987, 623469608520, 781185864787, 234404431020, 8824320960, 0, 0] := by
  rw [show D2M8K2.u13957 = KTree.node D2M8K2.t13964 (nat_lit 30661273) (nat_lit 1351283934) (nat_lit 0) D2M8K2.t13965 from rfl, totK_node, tot13964, tot13965]
  decide +kernel

theorem arows13958 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13958 = true := by
  rw [show D2M8K2.u13958 = KTree.node D2M8K2.t13966 (nat_lit 30662720) (nat_lit 3643195736) (nat_lit 0) D2M8K2.t13967 from rfl, allE_node, rows13966, irow13958, rows13967]
  all_goals rfl

theorem atot13958 : totK PD2M8K2 D2M8K2.u13958 = [0, 260812616751, 822136851724, 619360842621, 78233970459, 0, 0, 0] := by
  rw [show D2M8K2.u13958 = KTree.node D2M8K2.t13966 (nat_lit 30662720) (nat_lit 3643195736) (nat_lit 0) D2M8K2.t13967 from rfl, totK_node, tot13966, tot13967]
  decide +kernel

theorem arows13962 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13962 = true := by
  rw [show D2M8K2.u13962 = KTree.node D2M8K2.t13968 (nat_lit 30664731) (nat_lit 2282344799) (nat_lit 0) D2M8K2.t13969 from rfl, allE_node, rows13968, irow13962, rows13969]
  all_goals rfl

theorem atot13962 : totK PD2M8K2 D2M8K2.u13962 = [0, 183205682383, 730269523364, 762373860301, 149847506793, 2498823382, 0, 0] := by
  rw [show D2M8K2.u13962 = KTree.node D2M8K2.t13968 (nat_lit 30664731) (nat_lit 2282344799) (nat_lit 0) D2M8K2.t13969 from rfl, totK_node, tot13968, tot13969]
  decide +kernel

theorem arows13963 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13963 = true := by
  rw [show D2M8K2.u13963 = KTree.node D2M8K2.t13970 (nat_lit 30666570) (nat_lit 3835629738) (nat_lit 0) D2M8K2.t13971 from rfl, allE_node, rows13970, irow13963, rows13971]
  all_goals rfl

theorem atot13963 : totK PD2M8K2 D2M8K2.u13963 = [0, 242727975301, 808641521591, 668276118894, 95222530144, 0, 0, 0] := by
  rw [show D2M8K2.u13963 = KTree.node D2M8K2.t13970 (nat_lit 30666570) (nat_lit 3835629738) (nat_lit 0) D2M8K2.t13971 from rfl, totK_node, tot13970, tot13971]
  decide +kernel

theorem arows13965 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13965 = true := by
  rw [show D2M8K2.u13965 = KTree.node D2M8K2.t13972 (nat_lit 30668290) (nat_lit 4097396695) (nat_lit 0) D2M8K2.t13973 from rfl, allE_node, rows13972, irow13965, rows13973]
  all_goals rfl

theorem atot13965 : totK PD2M8K2 D2M8K2.u13965 = [0, 0, 359449246516, 926224247432, 475461113951, 34399548718, 0, 0] := by
  rw [show D2M8K2.u13965 = KTree.node D2M8K2.t13972 (nat_lit 30668290) (nat_lit 4097396695) (nat_lit 0) D2M8K2.t13973 from rfl, totK_node, tot13972, tot13973]
  decide +kernel

theorem arows13966 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13966 = true := by
  rw [show D2M8K2.u13966 = KTree.node D2M8K2.t13974 (nat_lit 30673178) (nat_lit 4241602830) (nat_lit 0) D2M8K2.t13975 from rfl, allE_node, rows13974, irow13966, rows13975]
  all_goals rfl

theorem atot13966 : totK PD2M8K2 D2M8K2.u13966 = [0, 0, 351605891203, 931261366547, 505144818220, 39058767260, 0, 0] := by
  rw [show D2M8K2.u13966 = KTree.node D2M8K2.t13974 (nat_lit 30673178) (nat_lit 4241602830) (nat_lit 0) D2M8K2.t13975 from rfl, totK_node, tot13974, tot13975]
  decide +kernel

theorem arows13969 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13969 = true := by
  rw [show D2M8K2.u13969 = KTree.node D2M8K2.t13976 (nat_lit 30674634) (nat_lit 3892453322) (nat_lit 0) D2M8K2.t13977 from rfl, allE_node, rows13976, irow13969, rows13977]
  all_goals rfl

theorem atot13969 : totK PD2M8K2 D2M8K2.u13969 = [0, 0, 0, 385308483742, 937377524303, 430154527922, 30397782892, 0] := by
  rw [show D2M8K2.u13969 = KTree.node D2M8K2.t13976 (nat_lit 30674634) (nat_lit 3892453322) (nat_lit 0) D2M8K2.t13977 from rfl, totK_node, tot13976, tot13977]
  decide +kernel

theorem arows13970 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13970 = true := by
  rw [show D2M8K2.u13970 = KTree.node D2M8K2.t13978 (nat_lit 30675985) (nat_lit 1041300227) (nat_lit 0) D2M8K2.t13979 from rfl, allE_node, rows13978, irow13970, rows13979]
  all_goals rfl

theorem atot13970 : totK PD2M8K2 D2M8K2.u13970 = [0, 0, 329511745295, 827961560559, 505057814442, 116524785471, 6524090962, 0] := by
  rw [show D2M8K2.u13970 = KTree.node D2M8K2.t13978 (nat_lit 30675985) (nat_lit 1041300227) (nat_lit 0) D2M8K2.t13979 from rfl, totK_node, tot13978, tot13979]
  decide +kernel

theorem arows13972 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13972 = true := by
  rw [show D2M8K2.u13972 = KTree.node D2M8K2.t13980 (nat_lit 30677782) (nat_lit 3167387285) (nat_lit 0) D2M8K2.t13981 from rfl, allE_node, rows13980, irow13972, rows13981]
  all_goals rfl

theorem atot13972 : totK PD2M8K2 D2M8K2.u13972 = [0, 0, 85831680626, 615878237434, 868864627338, 184304611267, 5067863418, 0] := by
  rw [show D2M8K2.u13972 = KTree.node D2M8K2.t13980 (nat_lit 30677782) (nat_lit 3167387285) (nat_lit 0) D2M8K2.t13981 from rfl, totK_node, tot13980, tot13981]
  decide +kernel

theorem arows13973 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13973 = true := by
  rw [show D2M8K2.u13973 = KTree.node D2M8K2.t13982 (nat_lit 30679821) (nat_lit 1477747738) (nat_lit 0) D2M8K2.t13983 from rfl, allE_node, rows13982, irow13973, rows13983]
  all_goals rfl

theorem atot13973 : totK PD2M8K2 D2M8K2.u13973 = [0, 0, 381048947264, 915724654046, 464340494514, 37290111508, 0, 0] := by
  rw [show D2M8K2.u13973 = KTree.node D2M8K2.t13982 (nat_lit 30679821) (nat_lit 1477747738) (nat_lit 0) D2M8K2.t13983 from rfl, totK_node, tot13982, tot13983]
  decide +kernel

theorem arows13978 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13978 = true := by
  rw [show D2M8K2.u13978 = KTree.node D2M8K2.t13984 (nat_lit 30681643) (nat_lit 1567877642) (nat_lit 0) D2M8K2.t13985 from rfl, allE_node, rows13984, irow13978, rows13985]
  all_goals rfl

theorem atot13978 : totK PD2M8K2 D2M8K2.u13978 = [0, 0, 83979632099, 606827131249, 856113189413, 195078615179, 5126512042, 0] := by
  rw [show D2M8K2.u13978 = KTree.node D2M8K2.t13984 (nat_lit 30681643) (nat_lit 1567877642) (nat_lit 0) D2M8K2.t13985 from rfl, totK_node, tot13984, tot13985]
  decide +kernel

theorem arows13979 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13979 = true := by
  rw [show D2M8K2.u13979 = KTree.node D2M8K2.t13986 (nat_lit 30683140) (nat_lit 4044005835) (nat_lit 0) D2M8K2.t13987 from rfl, allE_node, rows13986, irow13979, rows13987]
  all_goals rfl

theorem atot13979 : totK PD2M8K2 D2M8K2.u13979 = [0, 0, 348334952096, 919934042487, 484979538704, 35104984627, 0, 0] := by
  rw [show D2M8K2.u13979 = KTree.node D2M8K2.t13986 (nat_lit 30683140) (nat_lit 4044005835) (nat_lit 0) D2M8K2.t13987 from rfl, totK_node, tot13986, tot13987]
  decide +kernel

theorem arows13981 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13981 = true := by
  rw [show D2M8K2.u13981 = KTree.node D2M8K2.t13988 (nat_lit 30685258) (nat_lit 962879266) (nat_lit 0) D2M8K2.t13989 from rfl, allE_node, rows13988, irow13981, rows13989]
  all_goals rfl

theorem atot13981 : totK PD2M8K2 D2M8K2.u13981 = [0, 0, 157141031770, 731850595353, 791851121912, 123348644996, 1392055030, 0] := by
  rw [show D2M8K2.u13981 = KTree.node D2M8K2.t13988 (nat_lit 30685258) (nat_lit 962879266) (nat_lit 0) D2M8K2.t13989 from rfl, totK_node, tot13988, tot13989]
  decide +kernel

theorem arows13982 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13982 = true := by
  rw [show D2M8K2.u13982 = KTree.node D2M8K2.t13990 (nat_lit 30686843) (nat_lit 2364735427) (nat_lit 0) D2M8K2.t13991 from rfl, allE_node, rows13990, irow13982, rows13991]
  all_goals rfl

theorem atot13982 : totK PD2M8K2 D2M8K2.u13982 = [0, 0, 262921938247, 863586243372, 612311284329, 61654600146, 0, 0] := by
  rw [show D2M8K2.u13982 = KTree.node D2M8K2.t13990 (nat_lit 30686843) (nat_lit 2364735427) (nat_lit 0) D2M8K2.t13991 from rfl, totK_node, tot13990, tot13991]
  decide +kernel

theorem arows13985 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13985 = true := by
  rw [show D2M8K2.u13985 = KTree.node D2M8K2.t13992 (nat_lit 30689045) (nat_lit 2350321469) (nat_lit 0) D2M8K2.t13993 from rfl, allE_node, rows13992, irow13985, rows13993]
  all_goals rfl

theorem atot13985 : totK PD2M8K2 D2M8K2.u13985 = [0, 155087447104, 321783412617, 367278245611, 666792512536, 232519039802, 9139067247, 0] := by
  rw [show D2M8K2.u13985 = KTree.node D2M8K2.t13992 (nat_lit 30689045) (nat_lit 2350321469) (nat_lit 0) D2M8K2.t13993 from rfl, totK_node, tot13992, tot13993]
  decide +kernel

theorem arows13986 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13986 = true := by
  rw [show D2M8K2.u13986 = KTree.node D2M8K2.t13994 (nat_lit 30690920) (nat_lit 2718783297) (nat_lit 0) D2M8K2.t13995 from rfl, allE_node, rows13994, irow13986, rows13995]
  all_goals rfl

theorem atot13986 : totK PD2M8K2 D2M8K2.u13986 = [0, 170310898757, 754989862048, 740290236637, 106421842211, 1275377855, 0, 0] := by
  rw [show D2M8K2.u13986 = KTree.node D2M8K2.t13994 (nat_lit 30690920) (nat_lit 2718783297) (nat_lit 0) D2M8K2.t13995 from rfl, totK_node, tot13994, tot13995]
  decide +kernel

theorem arows13988 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13988 = true := by
  rw [show D2M8K2.u13988 = KTree.node D2M8K2.t13996 (nat_lit 30693432) (nat_lit 3265016501) (nat_lit 0) D2M8K2.t13997 from rfl, allE_node, rows13996, irow13988, rows13997]
  all_goals rfl

theorem atot13988 : totK PD2M8K2 D2M8K2.u13988 = [0, 340764620551, 886241885804, 556707240587, 56300715221, 0, 0, 0] := by
  rw [show D2M8K2.u13988 = KTree.node D2M8K2.t13996 (nat_lit 30693432) (nat_lit 3265016501) (nat_lit 0) D2M8K2.t13997 from rfl, totK_node, tot13996, tot13997]
  decide +kernel

theorem arows13989 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13989 = true := by
  rw [show D2M8K2.u13989 = KTree.node D2M8K2.t13998 (nat_lit 30694948) (nat_lit 3983305736) (nat_lit 0) D2M8K2.t13999 from rfl, allE_node, rows13998, irow13989, rows13999]
  all_goals rfl

theorem atot13989 : totK PD2M8K2 D2M8K2.u13989 = [0, 88183717169, 538535552771, 816181770571, 346340625000, 28198438779, 0, 0] := by
  rw [show D2M8K2.u13989 = KTree.node D2M8K2.t13998 (nat_lit 30694948) (nat_lit 3983305736) (nat_lit 0) D2M8K2.t13999 from rfl, totK_node, tot13998, tot13999]
  decide +kernel

theorem arows13993 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13993 = true := by
  rw [show D2M8K2.u13993 = KTree.node D2M8K2.t14000 (nat_lit 30696208) (nat_lit 3398309562) (nat_lit 0) D2M8K2.t14001 from rfl, allE_node, rows14000, irow13993, rows14001]
  all_goals rfl

theorem atot13993 : totK PD2M8K2 D2M8K2.u13993 = [0, 208329621090, 655064202967, 694033686883, 239994176094, 9288887403, 0, 0] := by
  rw [show D2M8K2.u13993 = KTree.node D2M8K2.t14000 (nat_lit 30696208) (nat_lit 3398309562) (nat_lit 0) D2M8K2.t14001 from rfl, totK_node, tot14000, tot14001]
  decide +kernel

theorem arows13994 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13994 = true := by
  rw [show D2M8K2.u13994 = KTree.node D2M8K2.t14002 (nat_lit 30697684) (nat_lit 4038823285) (nat_lit 0) D2M8K2.t14003 from rfl, allE_node, rows14002, irow13994, rows14003]
  all_goals rfl

theorem atot13994 : totK PD2M8K2 D2M8K2.u13994 = [0, 230051515413, 797147323418, 660124675667, 104429252957, 1164319620, 0, 0] := by
  rw [show D2M8K2.u13994 = KTree.node D2M8K2.t14002 (nat_lit 30697684) (nat_lit 4038823285) (nat_lit 0) D2M8K2.t14003 from rfl, totK_node, tot14002, tot14003]
  decide +kernel

theorem arows13996 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13996 = true := by
  rw [show D2M8K2.u13996 = KTree.node D2M8K2.t14004 (nat_lit 30699371) (nat_lit 2847569660) (nat_lit 0) D2M8K2.t14005 from rfl, allE_node, rows14004, irow13996, rows14005]
  all_goals rfl

theorem atot13996 : totK PD2M8K2 D2M8K2.u13996 = [0, 151660303848, 631918229961, 766196314528, 228295415320, 11885407614, 0, 0] := by
  rw [show D2M8K2.u13996 = KTree.node D2M8K2.t14004 (nat_lit 30699371) (nat_lit 2847569660) (nat_lit 0) D2M8K2.t14005 from rfl, totK_node, tot14004, tot14005]
  decide +kernel

theorem arows13997 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13997 = true := by
  rw [show D2M8K2.u13997 = KTree.node D2M8K2.t14006 (nat_lit 30704300) (nat_lit 3791391080) (nat_lit 0) D2M8K2.t14007 from rfl, allE_node, rows14006, irow13997, rows14007]
  all_goals rfl

theorem atot13997 : totK PD2M8K2 D2M8K2.u13997 = [0, 230524026028, 793310860464, 667730697333, 95786406437, 1096505104, 0, 0] := by
  rw [show D2M8K2.u13997 = KTree.node D2M8K2.t14006 (nat_lit 30704300) (nat_lit 3791391080) (nat_lit 0) D2M8K2.t14007 from rfl, totK_node, tot14006, tot14007]
  decide +kernel

theorem arows14000 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14000 = true := by
  rw [show D2M8K2.u14000 = KTree.node D2M8K2.t14008 (nat_lit 30706669) (nat_lit 1118122026) (nat_lit 0) D2M8K2.t14009 from rfl, allE_node, rows14008, irow14000, rows14009]
  all_goals rfl

theorem atot14000 : totK PD2M8K2 D2M8K2.u14000 = [0, 252484772265, 754934643764, 668358978627, 141664414105, 3884009855, 0, 0] := by
  rw [show D2M8K2.u14000 = KTree.node D2M8K2.t14008 (nat_lit 30706669) (nat_lit 1118122026) (nat_lit 0) D2M8K2.t14009 from rfl, totK_node, tot14008, tot14009]
  decide +kernel

theorem arows14001 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14001 = true := by
  rw [show D2M8K2.u14001 = KTree.node D2M8K2.t14010 (nat_lit 30708195) (nat_lit 3476449182) (nat_lit 0) D2M8K2.t14011 from rfl, allE_node, rows14010, irow14001, rows14011]
  all_goals rfl

theorem atot14001 : totK PD2M8K2 D2M8K2.u14001 = [0, 166099755219, 753835826027, 753291558203, 134537130571, 1232398321, 0, 0] := by
  rw [show D2M8K2.u14001 = KTree.node D2M8K2.t14010 (nat_lit 30708195) (nat_lit 3476449182) (nat_lit 0) D2M8K2.t14011 from rfl, totK_node, tot14010, tot14011]
  decide +kernel

theorem arows14003 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14003 = true := by
  rw [show D2M8K2.u14003 = KTree.node D2M8K2.t14012 (nat_lit 30709929) (nat_lit 958186622) (nat_lit 0) D2M8K2.t14013 from rfl, allE_node, rows14012, irow14003, rows14013]
  all_goals rfl

theorem atot14003 : totK PD2M8K2 D2M8K2.u14003 = [0, 0, 362518347591, 964340613285, 408727149284, 19090867562, 0, 0] := by
  rw [show D2M8K2.u14003 = KTree.node D2M8K2.t14012 (nat_lit 30709929) (nat_lit 958186622) (nat_lit 0) D2M8K2.t14013 from rfl, totK_node, tot14012, tot14013]
  decide +kernel

theorem arows14004 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14004 = true := by
  rw [show D2M8K2.u14004 = KTree.node D2M8K2.t14014 (nat_lit 30713987) (nat_lit 2632422117) (nat_lit 0) D2M8K2.t14015 from rfl, allE_node, rows14014, irow14004, rows14015]
  all_goals rfl

theorem atot14004 : totK PD2M8K2 D2M8K2.u14004 = [0, 0, 404106103483, 932398865318, 438084712273, 33635285156, 0, 0] := by
  rw [show D2M8K2.u14004 = KTree.node D2M8K2.t14014 (nat_lit 30713987) (nat_lit 2632422117) (nat_lit 0) D2M8K2.t14015 from rfl, totK_node, tot14014, tot14015]
  decide +kernel

theorem arows14010 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14010 = true := by
  rw [show D2M8K2.u14010 = KTree.node D2M8K2.t14016 (nat_lit 30716986) (nat_lit 3899492587) (nat_lit 0) D2M8K2.t14017 from rfl, allE_node, rows14016, irow14010, rows14017]
  all_goals rfl

theorem atot14010 : totK PD2M8K2 D2M8K2.u14010 = [0, 0, 390417043714, 935669802940, 445467819948, 28069850128, 0, 0] := by
  rw [show D2M8K2.u14010 = KTree.node D2M8K2.t14016 (nat_lit 30716986) (nat_lit 3899492587) (nat_lit 0) D2M8K2.t14017 from rfl, totK_node, tot14016, tot14017]
  decide +kernel

theorem arows14011 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14011 = true := by
  rw [show D2M8K2.u14011 = KTree.node D2M8K2.t14018 (nat_lit 30718453) (nat_lit 1079665076) (nat_lit 0) D2M8K2.t14019 from rfl, allE_node, rows14018, irow14011, rows14019]
  all_goals rfl

theorem atot14011 : totK PD2M8K2 D2M8K2.u14011 = [0, 0, 207698543303, 841328326588, 659611646842, 62023614158, 0, 0] := by
  rw [show D2M8K2.u14011 = KTree.node D2M8K2.t14018 (nat_lit 30718453) (nat_lit 1079665076) (nat_lit 0) D2M8K2.t14019 from rfl, totK_node, tot14018, tot14019]
  decide +kernel

theorem arows14013 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14013 = true := by
  rw [show D2M8K2.u14013 = KTree.node D2M8K2.t14020 (nat_lit 30723956) (nat_lit 3666590483) (nat_lit 0) D2M8K2.t14021 from rfl, allE_node, rows14020, irow14013, rows14021]
  all_goals rfl

theorem atot14013 : totK PD2M8K2 D2M8K2.u14013 = [0, 0, 238201062087, 715983086711, 640769794391, 158308582364, 5320761635, 0] := by
  rw [show D2M8K2.u14013 = KTree.node D2M8K2.t14020 (nat_lit 30723956) (nat_lit 3666590483) (nat_lit 0) D2M8K2.t14021 from rfl, totK_node, tot14020, tot14021]
  decide +kernel

theorem arows14014 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14014 = true := by
  rw [show D2M8K2.u14014 = KTree.node D2M8K2.t14022 (nat_lit 30725667) (nat_lit 2398077429) (nat_lit 0) D2M8K2.t14023 from rfl, allE_node, rows14022, irow14014, rows14023]
  all_goals rfl

theorem atot14014 : totK PD2M8K2 D2M8K2.u14014 = [0, 0, 142164912838, 772824946377, 744919534116, 85538846404, 0, 0] := by
  rw [show D2M8K2.u14014 = KTree.node D2M8K2.t14022 (nat_lit 30725667) (nat_lit 2398077429) (nat_lit 0) D2M8K2.t14023 from rfl, totK_node, tot14022, tot14023]
  decide +kernel

theorem arows14017 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14017 = true := by
  rw [show D2M8K2.u14017 = KTree.node D2M8K2.t14024 (nat_lit 30727905) (nat_lit 1635803558) (nat_lit 0) D2M8K2.t14025 from rfl, allE_node, rows14024, irow14017, rows14025]
  all_goals rfl

theorem atot14017 : totK PD2M8K2 D2M8K2.u14017 = [0, 0, 414789201061, 922593385228, 427020519484, 44896118461, 1225787871, 0] := by
  rw [show D2M8K2.u14017 = KTree.node D2M8K2.t14024 (nat_lit 30727905) (nat_lit 1635803558) (nat_lit 0) D2M8K2.t14025 from rfl, totK_node, tot14024, tot14025]
  decide +kernel

theorem arows14018 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14018 = true := by
  rw [show D2M8K2.u14018 = KTree.node D2M8K2.t14026 (nat_lit 30731787) (nat_lit 3589746949) (nat_lit 0) D2M8K2.t14027 from rfl, allE_node, rows14026, irow14018, rows14027]
  all_goals rfl

theorem atot14018 : totK PD2M8K2 D2M8K2.u14018 = [0, 325540319114, 834971535126, 486441677850, 134813899941, 11742091552, 0, 0] := by
  rw [show D2M8K2.u14018 = KTree.node D2M8K2.t14026 (nat_lit 30731787) (nat_lit 3589746949) (nat_lit 0) D2M8K2.t14027 from rfl, totK_node, tot14026, tot14027]
  decide +kernel

theorem arows14020 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14020 = true := by
  rw [show D2M8K2.u14020 = KTree.node D2M8K2.t14028 (nat_lit 30733992) (nat_lit 3540965393) (nat_lit 0) D2M8K2.t14029 from rfl, allE_node, rows14028, irow14020, rows14029]
  all_goals rfl

theorem atot14020 : totK PD2M8K2 D2M8K2.u14020 = [0, 166263604103, 718371148678, 803054241936, 132503475823, 1310517177, 0, 0] := by
  rw [show D2M8K2.u14020 = KTree.node D2M8K2.t14028 (nat_lit 30733992) (nat_lit 3540965393) (nat_lit 0) D2M8K2.t14029 from rfl, totK_node, tot14028, tot14029]
  decide +kernel

theorem arows14021 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14021 = true := by
  rw [show D2M8K2.u14021 = KTree.node D2M8K2.t14030 (nat_lit 30735616) (nat_lit 2861885305) (nat_lit 0) D2M8K2.t14031 from rfl, allE_node, rows14030, irow14021, rows14031]
  all_goals rfl

theorem atot14021 : totK PD2M8K2 D2M8K2.u14021 = [0, 262731427320, 795468117665, 598694480523, 145245425717, 15860286962, 0, 0] := by
  rw [show D2M8K2.u14021 = KTree.node D2M8K2.t14030 (nat_lit 30735616) (nat_lit 2861885305) (nat_lit 0) D2M8K2.t14031 from rfl, totK_node, tot14030, tot14031]
  decide +kernel

theorem arows14025 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14025 = true := by
  rw [show D2M8K2.u14025 = KTree.node D2M8K2.t14032 (nat_lit 30737123) (nat_lit 2301247634) (nat_lit 0) D2M8K2.t14033 from rfl, allE_node, rows14032, irow14025, rows14033]
  all_goals rfl

theorem atot14025 : totK PD2M8K2 D2M8K2.u14025 = [0, 55954175340, 410001106801, 875257625380, 427282248184, 21625412572, 0, 0] := by
  rw [show D2M8K2.u14025 = KTree.node D2M8K2.t14032 (nat_lit 30737123) (nat_lit 2301247634) (nat_lit 0) D2M8K2.t14033 from rfl, totK_node, tot14032, tot14033]
  decide +kernel

theorem arows14026 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14026 = true := by
  rw [show D2M8K2.u14026 = KTree.node D2M8K2.t14034 (nat_lit 30742093) (nat_lit 1117667286) (nat_lit 0) D2M8K2.t14035 from rfl, allE_node, rows14034, irow14026, rows14035]
  all_goals rfl

theorem atot14026 : totK PD2M8K2 D2M8K2.u14026 = [0, 382621035780, 940306479290, 472572854784, 35635499773, 0, 0, 0] := by
  rw [show D2M8K2.u14026 = KTree.node D2M8K2.t14034 (nat_lit 30742093) (nat_lit 1117667286) (nat_lit 0) D2M8K2.t14035 from rfl, totK_node, tot14034, tot14035]
  decide +kernel

theorem arows14028 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14028 = true := by
  rw [show D2M8K2.u14028 = KTree.node D2M8K2.t14036 (nat_lit 30743744) (nat_lit 3717808584) (nat_lit 0) D2M8K2.t14037 from rfl, allE_node, rows14036, irow14028, rows14037]
  all_goals rfl

theorem atot14028 : totK PD2M8K2 D2M8K2.u14028 = [0, 0, 499537824797, 957081590011, 299292135579, 13196099988, 0, 0] := by
  rw [show D2M8K2.u14028 = KTree.node D2M8K2.t14036 (nat_lit 30743744) (nat_lit 3717808584) (nat_lit 0) D2M8K2.t14037 from rfl, totK_node, tot14036, tot14037]
  decide +kernel

theorem arows14029 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14029 = true := by
  rw [show D2M8K2.u14029 = KTree.node D2M8K2.t14038 (nat_lit 30745151) (nat_lit 2092999074) (nat_lit 0) D2M8K2.t14039 from rfl, allE_node, rows14038, irow14029, rows14039]
  all_goals rfl

theorem atot14029 : totK PD2M8K2 D2M8K2.u14029 = [0, 363107838268, 886728703880, 513560624683, 53202640833, 0, 0, 0] := by
  rw [show D2M8K2.u14029 = KTree.node D2M8K2.t14038 (nat_lit 30745151) (nat_lit 2092999074) (nat_lit 0) D2M8K2.t14039 from rfl, totK_node, tot14038, tot14039]
  decide +kernel

theorem arows14032 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14032 = true := by
  rw [show D2M8K2.u14032 = KTree.node D2M8K2.t14040 (nat_lit 30746996) (nat_lit 3667859904) (nat_lit 0) D2M8K2.t14041 from rfl, allE_node, rows14040, irow14032, rows14041]
  all_goals rfl

theorem atot14032 : totK PD2M8K2 D2M8K2.u14032 = [0, 97928180626, 648869201704, 842553088013, 191959708575, 4980514959, 0, 0] := by
  rw [show D2M8K2.u14032 = KTree.node D2M8K2.t14040 (nat_lit 30746996) (nat_lit 3667859904) (nat_lit 0) D2M8K2.t14041 from rfl, totK_node, tot14040, tot14041]
  decide +kernel

theorem arows14033 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14033 = true := by
  rw [show D2M8K2.u14033 = KTree.node D2M8K2.t14042 (nat_lit 30748820) (nat_lit 2630260662) (nat_lit 0) D2M8K2.t14043 from rfl, allE_node, rows14042, irow14033, rows14043]
  all_goals rfl

theorem atot14033 : totK PD2M8K2 D2M8K2.u14033 = [0, 339897186392, 919082977624, 530125022461, 43704671065, 0, 0, 0] := by
  rw [show D2M8K2.u14033 = KTree.node D2M8K2.t14042 (nat_lit 30748820) (nat_lit 2630260662) (nat_lit 0) D2M8K2.t14043 from rfl, totK_node, tot14042, tot14043]
  decide +kernel

theorem arows14035 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14035 = true := by
  rw [show D2M8K2.u14035 = KTree.node D2M8K2.t14044 (nat_lit 30750536) (nat_lit 2828099712) (nat_lit 0) D2M8K2.t14045 from rfl, allE_node, rows14044, irow14035, rows14045]
  all_goals rfl

theorem atot14035 : totK PD2M8K2 D2M8K2.u14035 = [0, 0, 428294295425, 982161121385, 361815017095, 11131440380, 0, 0] := by
  rw [show D2M8K2.u14035 = KTree.node D2M8K2.t14044 (nat_lit 30750536) (nat_lit 2828099712) (nat_lit 0) D2M8K2.t14045 from rfl, totK_node, tot14044, tot14045]
  decide +kernel

theorem arows14036 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14036 = true := by
  rw [show D2M8K2.u14036 = KTree.node D2M8K2.t14046 (nat_lit 30752817) (nat_lit 1500815467) (nat_lit 0) D2M8K2.t14047 from rfl, allE_node, rows14046, irow14036, rows14047]
  all_goals rfl

theorem atot14036 : totK PD2M8K2 D2M8K2.u14036 = [0, 0, 470154718894, 937294267309, 366687037529, 31084721935, 0, 0] := by
  rw [show D2M8K2.u14036 = KTree.node D2M8K2.t14046 (nat_lit 30752817) (nat_lit 1500815467) (nat_lit 0) D2M8K2.t14047 from rfl, totK_node, tot14046, tot14047]
  decide +kernel

theorem arows14041 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14041 = true := by
  rw [show D2M8K2.u14041 = KTree.node D2M8K2.t14048 (nat_lit 30756247) (nat_lit 2198362630) (nat_lit 0) D2M8K2.t14049 from rfl, allE_node, rows14048, irow14041, rows14049]
  all_goals rfl

theorem atot14041 : totK PD2M8K2 D2M8K2.u14041 = [0, 0, 357293224115, 936580864011, 462165201843, 23954076554, 0, 0] := by
  rw [show D2M8K2.u14041 = KTree.node D2M8K2.t14048 (nat_lit 30756247) (nat_lit 2198362630) (nat_lit 0) D2M8K2.t14049 from rfl, totK_node, tot14048, tot14049]
  decide +kernel

theorem arows14042 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14042 = true := by
  rw [show D2M8K2.u14042 = KTree.node D2M8K2.t14050 (nat_lit 30762957) (nat_lit 1471437730) (nat_lit 0) D2M8K2.t14051 from rfl, allE_node, rows14050, irow14042, rows14051]
  all_goals rfl

theorem atot14042 : totK PD2M8K2 D2M8K2.u14042 = [0, 0, 352276500150, 914098097390, 498019611669, 34737066993, 0, 0] := by
  rw [show D2M8K2.u14042 = KTree.node D2M8K2.t14050 (nat_lit 30762957) (nat_lit 1471437730) (nat_lit 0) D2M8K2.t14051 from rfl, totK_node, tot14050, tot14051]
  decide +kernel

theorem arows14044 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14044 = true := by
  rw [show D2M8K2.u14044 = KTree.node D2M8K2.t14052 (nat_lit 30764752) (nat_lit 1625387904) (nat_lit 0) D2M8K2.t14053 from rfl, allE_node, rows14052, irow14044, rows14053]
  all_goals rfl

theorem atot14044 : totK PD2M8K2 D2M8K2.u14044 = [0, 0, 98934374103, 617863521703, 833168047694, 194779370254, 5352782441, 0] := by
  rw [show D2M8K2.u14044 = KTree.node D2M8K2.t14052 (nat_lit 30764752) (nat_lit 1625387904) (nat_lit 0) D2M8K2.t14053 from rfl, totK_node, tot14052, tot14053]
  decide +kernel

theorem arows14045 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14045 = true := by
  rw [show D2M8K2.u14045 = KTree.node D2M8K2.t14054 (nat_lit 30766349) (nat_lit 1252557478) (nat_lit 0) D2M8K2.t14055 from rfl, allE_node, rows14054, irow14045, rows14055]
  all_goals rfl

theorem atot14045 : totK PD2M8K2 D2M8K2.u14045 = [0, 0, 280543829544, 908609951544, 565152092751, 41067924408, 0, 0] := by
  rw [show D2M8K2.u14045 = KTree.node D2M8K2.t14054 (nat_lit 30766349) (nat_lit 1252557478) (nat_lit 0) D2M8K2.t14055 from rfl, totK_node, tot14054, tot14055]
  decide +kernel

theorem arows14048 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14048 = true := by
  rw [show D2M8K2.u14048 = KTree.node D2M8K2.t14056 (nat_lit 30768912) (nat_lit 3737108960) (nat_lit 0) D2M8K2.t14057 from rfl, allE_node, rows14056, irow14048, rows14057]
  all_goals rfl

theorem atot14048 : totK PD2M8K2 D2M8K2.u14048 = [0, 0, 235109116484, 767756322308, 669263748268, 97876996215, 1271866555, 0] := by
  rw [show D2M8K2.u14048 = KTree.node D2M8K2.t14056 (nat_lit 30768912) (nat_lit 3737108960) (nat_lit 0) D2M8K2.t14057 from rfl, totK_node, tot14056, tot14057]
  decide +kernel

theorem arows14049 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14049 = true := by
  rw [show D2M8K2.u14049 = KTree.node D2M8K2.t14058 (nat_lit 30770489) (nat_lit 1219132161) (nat_lit 0) D2M8K2.t14059 from rfl, allE_node, rows14058, irow14049, rows14059]
  all_goals rfl

theorem atot14049 : totK PD2M8K2 D2M8K2.u14049 = [0, 180280610855, 621306953107, 718211648697, 289149737739, 18566504420, 0, 0] := by
  rw [show D2M8K2.u14049 = KTree.node D2M8K2.t14058 (nat_lit 30770489) (nat_lit 1219132161) (nat_lit 0) D2M8K2.t14059 from rfl, totK_node, tot14058, tot14059]
  decide +kernel

theorem arows14051 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14051 = true := by
  rw [show D2M8K2.u14051 = KTree.node D2M8K2.t14060 (nat_lit 30777148) (nat_lit 3866680884) (nat_lit 0) D2M8K2.t14061 from rfl, allE_node, rows14060, irow14051, rows14061]
  all_goals rfl

theorem atot14051 : totK PD2M8K2 D2M8K2.u14051 = [0, 248847232727, 759728293211, 598315623848, 189645183044, 21396654552, 0, 0] := by
  rw [show D2M8K2.u14051 = KTree.node D2M8K2.t14060 (nat_lit 30777148) (nat_lit 3866680884) (nat_lit 0) D2M8K2.t14061 from rfl, totK_node, tot14060, tot14061]
  decide +kernel

theorem arows14052 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14052 = true := by
  rw [show D2M8K2.u14052 = KTree.node D2M8K2.t14062 (nat_lit 30778608) (nat_lit 3186296335) (nat_lit 0) D2M8K2.t14063 from rfl, allE_node, rows14062, irow14052, rows14063]
  all_goals rfl

theorem atot14052 : totK PD2M8K2 D2M8K2.u14052 = [0, 67104705643, 444486427392, 871590162853, 389226718452, 16094634009, 0, 0] := by
  rw [show D2M8K2.u14052 = KTree.node D2M8K2.t14062 (nat_lit 30778608) (nat_lit 3186296335) (nat_lit 0) D2M8K2.t14063 from rfl, totK_node, tot14062, tot14063]
  decide +kernel

theorem arows14056 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14056 = true := by
  rw [show D2M8K2.u14056 = KTree.node D2M8K2.t14064 (nat_lit 30779906) (nat_lit 4047483344) (nat_lit 0) D2M8K2.t14065 from rfl, allE_node, rows14064, irow14056, rows14065]
  all_goals rfl

theorem atot14056 : totK PD2M8K2 D2M8K2.u14056 = [0, 335066059555, 912608332191, 522703314924, 44589161472, 0, 0, 0] := by
  rw [show D2M8K2.u14056 = KTree.node D2M8K2.t14064 (nat_lit 30779906) (nat_lit 4047483344) (nat_lit 0) D2M8K2.t14065 from rfl, totK_node, tot14064, tot14065]
  decide +kernel

theorem arows14057 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14057 = true := by
  rw [show D2M8K2.u14057 = KTree.node D2M8K2.t14066 (nat_lit 30781653) (nat_lit 1456041422) (nat_lit 0) D2M8K2.t14067 from rfl, allE_node, rows14066, irow14057, rows14067]
  all_goals rfl

theorem atot14057 : totK PD2M8K2 D2M8K2.u14057 = [0, 67163829148, 514861656754, 882172819019, 281516415316, 13049727234, 0, 0] := by
  rw [show D2M8K2.u14057 = KTree.node D2M8K2.t14066 (nat_lit 30781653) (nat_lit 1456041422) (nat_lit 0) D2M8K2.t14067 from rfl, totK_node, tot14066, tot14067]
  decide +kernel

theorem arows14059 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14059 = true := by
  rw [show D2M8K2.u14059 = KTree.node D2M8K2.t14068 (nat_lit 30783681) (nat_lit 1781114813) (nat_lit 0) D2M8K2.t14069 from rfl, allE_node, rows14068, irow14059, rows14069]
  all_goals rfl

theorem atot14059 : totK PD2M8K2 D2M8K2.u14059 = [0, 335251487571, 917567308380, 522516190238, 44763335580, 0, 0, 0] := by
  rw [show D2M8K2.u14059 = KTree.node D2M8K2.t14068 (nat_lit 30783681) (nat_lit 1781114813) (nat_lit 0) D2M8K2.t14069 from rfl, totK_node, tot14068, tot14069]
  decide +kernel

theorem arows14060 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14060 = true := by
  rw [show D2M8K2.u14060 = KTree.node D2M8K2.t14070 (nat_lit 30785424) (nat_lit 3229271102) (nat_lit 0) D2M8K2.t14071 from rfl, allE_node, rows14070, irow14060, rows14071]
  all_goals rfl

theorem atot14060 : totK PD2M8K2 D2M8K2.u14060 = [0, 70914634579, 511735388681, 877221504781, 291700473722, 13250685261, 0, 0] := by
  rw [show D2M8K2.u14060 = KTree.node D2M8K2.t14070 (nat_lit 30785424) (nat_lit 3229271102) (nat_lit 0) D2M8K2.t14071 from rfl, totK_node, tot14070, tot14071]
  decide +kernel

theorem arows14063 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14063 = true := by
  rw [show D2M8K2.u14063 = KTree.node D2M8K2.t14072 (nat_lit 30786824) (nat_lit 3637927649) (nat_lit 0) D2M8K2.t14073 from rfl, allE_node, rows14072, irow14063, rows14073]
  all_goals rfl

theorem atot14063 : totK PD2M8K2 D2M8K2.u14063 = [0, 353655970187, 930279544078, 496277938080, 39983591536, 0, 0, 0] := by
  rw [show D2M8K2.u14063 = KTree.node D2M8K2.t14072 (nat_lit 30786824) (nat_lit 3637927649) (nat_lit 0) D2M8K2.t14073 from rfl, totK_node, tot14072, tot14073]
  decide +kernel

theorem arows14064 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14064 = true := by
  rw [show D2M8K2.u14064 = KTree.node D2M8K2.t14074 (nat_lit 30788669) (nat_lit 1698005714) (nat_lit 0) D2M8K2.t14075 from rfl, allE_node, rows14074, irow14064, rows14075]
  all_goals rfl

theorem atot14064 : totK PD2M8K2 D2M8K2.u14064 = [0, 0, 539643374131, 1002040319261, 260726515960, 12011707486, 0, 0] := by
  rw [show D2M8K2.u14064 = KTree.node D2M8K2.t14074 (nat_lit 30788669) (nat_lit 1698005714) (nat_lit 0) D2M8K2.t14075 from rfl, totK_node, tot14074, tot14075]
  decide +kernel

theorem arows14066 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14066 = true := by
  rw [show D2M8K2.u14066 = KTree.node D2M8K2.t14076 (nat_lit 30797455) (nat_lit 2356516505) (nat_lit 0) D2M8K2.t14077 from rfl, allE_node, rows14076, irow14066, rows14077]
  all_goals rfl

theorem atot14066 : totK PD2M8K2 D2M8K2.u14066 = [0, 0, 335011566944, 920427491128, 505794161072, 31545100690, 0, 0] := by
  rw [show D2M8K2.u14066 = KTree.node D2M8K2.t14076 (nat_lit 30797455) (nat_lit 2356516505) (nat_lit 0) D2M8K2.t14077 from rfl, totK_node, tot14076, tot14077]
  decide +kernel

theorem arows14067 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14067 = true := by
  rw [show D2M8K2.u14067 = KTree.node D2M8K2.t14078 (nat_lit 30800512) (nat_lit 3781001236) (nat_lit 0) D2M8K2.t14079 from rfl, allE_node, rows14078, irow14067, rows14079]
  all_goals rfl

theorem atot14067 : totK PD2M8K2 D2M8K2.u14067 = [0, 0, 401720290354, 938326423623, 428371809740, 26698413895, 0, 0] := by
  rw [show D2M8K2.u14067 = KTree.node D2M8K2.t14078 (nat_lit 30800512) (nat_lit 3781001236) (nat_lit 0) D2M8K2.t14079 from rfl, totK_node, tot14078, tot14079]
  decide +kernel

theorem arows14075 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14075 = true := by
  rw [show D2M8K2.u14075 = KTree.node D2M8K2.t14080 (nat_lit 30804198) (nat_lit 3880930485) (nat_lit 0) D2M8K2.t14081 from rfl, allE_node, rows14080, irow14075, rows14081]
  all_goals rfl

theorem atot14075 : totK PD2M8K2 D2M8K2.u14075 = [0, 0, 353812990060, 951294084142, 465676461360, 24807255034, 0, 0] := by
  rw [show D2M8K2.u14075 = KTree.node D2M8K2.t14080 (nat_lit 30804198) (nat_lit 3880930485) (nat_lit 0) D2M8K2.t14081 from rfl, totK_node, tot14080, tot14081]
  decide +kernel

theorem arows14076 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14076 = true := by
  rw [show D2M8K2.u14076 = KTree.node D2M8K2.t14082 (nat_lit 30807268) (nat_lit 3984978314) (nat_lit 0) D2M8K2.t14083 from rfl, allE_node, rows14082, irow14076, rows14083]
  all_goals rfl

theorem atot14076 : totK PD2M8K2 D2M8K2.u14076 = [0, 0, 375722620296, 940972756267, 440041302159, 26544310280, 0, 0] := by
  rw [show D2M8K2.u14076 = KTree.node D2M8K2.t14082 (nat_lit 30807268) (nat_lit 3984978314) (nat_lit 0) D2M8K2.t14083 from rfl, totK_node, tot14082, tot14083]
  decide +kernel

theorem arows14078 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14078 = true := by
  rw [show D2M8K2.u14078 = KTree.node D2M8K2.t14084 (nat_lit 30808901) (nat_lit 2270366297) (nat_lit 0) D2M8K2.t14085 from rfl, allE_node, rows14084, irow14078, rows14085]
  all_goals rfl

theorem atot14078 : totK PD2M8K2 D2M8K2.u14078 = [0, 18716352131, 100100911056, 688760978118, 806018864141, 143148215989, 1429815836, 0] := by
  rw [show D2M8K2.u14078 = KTree.node D2M8K2.t14084 (nat_lit 30808901) (nat_lit 2270366297) (nat_lit 0) D2M8K2.t14085 from rfl, totK_node, tot14084, tot14085]
  decide +kernel

theorem arows14079 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14079 = true := by
  rw [show D2M8K2.u14079 = KTree.node D2M8K2.t14086 (nat_lit 30814654) (nat_lit 3861162953) (nat_lit 0) D2M8K2.t14087 from rfl, allE_node, rows14086, irow14079, rows14087]
  all_goals rfl

theorem atot14079 : totK PD2M8K2 D2M8K2.u14079 = [0, 324118994212, 935489146742, 522842771920, 31311693082, 0, 0, 0] := by
  rw [show D2M8K2.u14079 = KTree.node D2M8K2.t14086 (nat_lit 30814654) (nat_lit 3861162953) (nat_lit 0) D2M8K2.t14087 from rfl, totK_node, tot14086, tot14087]
  decide +kernel

theorem arows14082 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14082 = true := by
  rw [show D2M8K2.u14082 = KTree.node D2M8K2.t14088 (nat_lit 30817475) (nat_lit 2870342021) (nat_lit 0) D2M8K2.t14089 from rfl, allE_node, rows14088, irow14082, rows14089]
  all_goals rfl

theorem atot14082 : totK PD2M8K2 D2M8K2.u14082 = [0, 180953379104, 724847687732, 779047141710, 137692391682, 1369150432, 0, 0] := by
  rw [show D2M8K2.u14082 = KTree.node D2M8K2.t14088 (nat_lit 30817475) (nat_lit 2870342021) (nat_lit 0) D2M8K2.t14089 from rfl, totK_node, tot14088, tot14089]
  decide +kernel

theorem arows14083 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14083 = true := by
  rw [show D2M8K2.u14083 = KTree.node D2M8K2.t14090 (nat_lit 30818650) (nat_lit 4003915680) (nat_lit 0) D2M8K2.t14091 from rfl, allE_node, rows14090, irow14083, rows14091]
  all_goals rfl

theorem atot14083 : totK PD2M8K2 D2M8K2.u14083 = [0, 249910957001, 768675609532, 602998290122, 188639513041, 21391863750, 0, 0] := by
  rw [show D2M8K2.u14083 = KTree.node D2M8K2.t14090 (nat_lit 30818650) (nat_lit 4003915680) (nat_lit 0) D2M8K2.t14091 from rfl, totK_node, tot14090, tot14091]
  decide +kernel

theorem arows14085 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14085 = true := by
  rw [show D2M8K2.u14085 = KTree.node D2M8K2.t14092 (nat_lit 30820115) (nat_lit 2169702834) (nat_lit 0) D2M8K2.t14093 from rfl, allE_node, rows14092, irow14085, rows14093]
  all_goals rfl

theorem atot14085 : totK PD2M8K2 D2M8K2.u14085 = [0, 78440106414, 453004774012, 865310397009, 382692633583, 16088841882, 0, 0] := by
  rw [show D2M8K2.u14085 = KTree.node D2M8K2.t14092 (nat_lit 30820115) (nat_lit 2169702834) (nat_lit 0) D2M8K2.t14093 from rfl, totK_node, tot14092, tot14093]
  decide +kernel

theorem arows14086 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14086 = true := by
  rw [show D2M8K2.u14086 = KTree.node D2M8K2.t14094 (nat_lit 30821376) (nat_lit 3419229445) (nat_lit 0) D2M8K2.t14095 from rfl, allE_node, rows14094, irow14086, rows14095]
  all_goals rfl

theorem atot14086 : totK PD2M8K2 D2M8K2.u14086 = [0, 336428585124, 917427268351, 525035472130, 46530585284, 0, 0, 0] := by
  rw [show D2M8K2.u14086 = KTree.node D2M8K2.t14094 (nat_lit 30821376) (nat_lit 3419229445) (nat_lit 0) D2M8K2.t14095 from rfl, totK_node, tot14094, tot14095]
  decide +kernel

theorem arows14090 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14090 = true := by
  rw [show D2M8K2.u14090 = KTree.node D2M8K2.t14096 (nat_lit 30823105) (nat_lit 1414861519) (nat_lit 0) D2M8K2.t14097 from rfl, allE_node, rows14096, irow14090, rows14097]
  all_goals rfl

theorem atot14090 : totK PD2M8K2 D2M8K2.u14090 = [0, 78493953735, 542611658928, 886097110283, 266634011899, 9068544132, 0, 0] := by
  rw [show D2M8K2.u14090 = KTree.node D2M8K2.t14096 (nat_lit 30823105) (nat_lit 1414861519) (nat_lit 0) D2M8K2.t14097 from rfl, totK_node, tot14096, tot14097]
  decide +kernel

theorem arows14091 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14091 = true := by
  rw [show D2M8K2.u14091 = KTree.node D2M8K2.t14098 (nat_lit 30825094) (nat_lit 2487773761) (nat_lit 0) D2M8K2.t14099 from rfl, allE_node, rows14098, irow14091, rows14099]
  all_goals rfl

theorem atot14091 : totK PD2M8K2 D2M8K2.u14091 = [0, 336623331890, 925592269430, 525494518885, 40874698974, 0, 0, 0] := by
  rw [show D2M8K2.u14091 = KTree.node D2M8K2.t14098 (nat_lit 30825094) (nat_lit 2487773761) (nat_lit 0) D2M8K2.t14099 from rfl, totK_node, tot14098, tot14099]
  decide +kernel

theorem arows14093 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14093 = true := by
  rw [show D2M8K2.u14093 = KTree.node D2M8K2.t14100 (nat_lit 30826813) (nat_lit 1117241395) (nat_lit 0) D2M8K2.t14101 from rfl, allE_node, rows14100, irow14093, rows14101]
  all_goals rfl

theorem atot14093 : totK PD2M8K2 D2M8K2.u14093 = [0, 79434949537, 517643349663, 896668034680, 283200938018, 9179787334, 0, 0] := by
  rw [show D2M8K2.u14093 = KTree.node D2M8K2.t14100 (nat_lit 30826813) (nat_lit 1117241395) (nat_lit 0) D2M8K2.t14101 from rfl, totK_node, tot14100, tot14101]
  decide +kernel

theorem arows14094 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14094 = true := by
  rw [show D2M8K2.u14094 = KTree.node D2M8K2.t14102 (nat_lit 30831691) (nat_lit 1494798112) (nat_lit 0) D2M8K2.t14103 from rfl, allE_node, rows14102, irow14094, rows14103]
  all_goals rfl

theorem atot14094 : totK PD2M8K2 D2M8K2.u14094 = [0, 363998877510, 944855012594, 495370408392, 39033101477, 0, 0, 0] := by
  rw [show D2M8K2.u14094 = KTree.node D2M8K2.t14102 (nat_lit 30831691) (nat_lit 1494798112) (nat_lit 0) D2M8K2.t14103 from rfl, totK_node, tot14102, tot14103]
  decide +kernel

theorem arows14097 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14097 = true := by
  rw [show D2M8K2.u14097 = KTree.node D2M8K2.t14104 (nat_lit 30833320) (nat_lit 3874156875) (nat_lit 0) D2M8K2.t14105 from rfl, allE_node, rows14104, irow14097, rows14105]
  all_goals rfl

theorem atot14097 : totK PD2M8K2 D2M8K2.u14097 = [0, 0, 494881931656, 987974067002, 298405667542, 8613300288, 0, 0] := by
  rw [show D2M8K2.u14097 = KTree.node D2M8K2.t14104 (nat_lit 30833320) (nat_lit 3874156875) (nat_lit 0) D2M8K2.t14105 from rfl, totK_node, tot14104, tot14105]
  decide +kernel

theorem arows14098 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14098 = true := by
  rw [show D2M8K2.u14098 = KTree.node D2M8K2.t14106 (nat_lit 30835300) (nat_lit 2792061884) (nat_lit 0) D2M8K2.t14107 from rfl, allE_node, rows14106, irow14098, rows14107]
  all_goals rfl

theorem atot14098 : totK PD2M8K2 D2M8K2.u14098 = [0, 0, 453703593407, 942404123503, 386512517576, 32161988474, 0, 0] := by
  rw [show D2M8K2.u14098 = KTree.node D2M8K2.t14106 (nat_lit 30835300) (nat_lit 2792061884) (nat_lit 0) D2M8K2.t14107 from rfl, totK_node, tot14106, tot14107]
  decide +kernel

theorem arows14100 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14100 = true := by
  rw [show D2M8K2.u14100 = KTree.node D2M8K2.t14108 (nat_lit 30839070) (nat_lit 3849088082) (nat_lit 0) D2M8K2.t14109 from rfl, allE_node, rows14108, irow14100, rows14109]
  all_goals rfl

theorem atot14100 : totK PD2M8K2 D2M8K2.u14100 = [0, 0, 394005175481, 918455555886, 468115405824, 27232129470, 0, 0] := by
  rw [show D2M8K2.u14100 = KTree.node D2M8K2.t14108 (nat_lit 30839070) (nat_lit 3849088082) (nat_lit 0) D2M8K2.t14109 from rfl, totK_node, tot14108, tot14109]
  decide +kernel

theorem arows14101 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14101 = true := by
  rw [show D2M8K2.u14101 = KTree.node D2M8K2.t14110 (nat_lit 30842058) (nat_lit 3089710102) (nat_lit 0) D2M8K2.t14111 from rfl, allE_node, rows14110, irow14101, rows14111]
  all_goals rfl

theorem atot14101 : totK PD2M8K2 D2M8K2.u14101 = [0, 0, 346223503262, 919676202243, 497795422608, 33743809733, 0, 0] := by
  rw [show D2M8K2.u14101 = KTree.node D2M8K2.t14110 (nat_lit 30842058) (nat_lit 3089710102) (nat_lit 0) D2M8K2.t14111 from rfl, totK_node, tot14110, tot14111]
  decide +kernel

theorem arows14106 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14106 = true := by
  rw [show D2M8K2.u14106 = KTree.node D2M8K2.t14112 (nat_lit 30844340) (nat_lit 3387143671) (nat_lit 0) D2M8K2.t14113 from rfl, allE_node, rows14112, irow14106, rows14113]
  all_goals rfl

theorem atot14106 : totK PD2M8K2 D2M8K2.u14106 = [0, 0, 164981134323, 754483562000, 757149463017, 116160271161, 1323630408, 0] := by
  rw [show D2M8K2.u14106 = KTree.node D2M8K2.t14112 (nat_lit 30844340) (nat_lit 3387143671) (nat_lit 0) D2M8K2.t14113 from rfl, totK_node, tot14112, tot14113]
  decide +kernel

theorem arows14107 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14107 = true := by
  rw [show D2M8K2.u14107 = KTree.node D2M8K2.t14114 (nat_lit 30846260) (nat_lit 1489746517) (nat_lit 0) D2M8K2.t14115 from rfl, allE_node, rows14114, irow14107, rows14115]
  all_goals rfl

theorem atot14107 : totK PD2M8K2 D2M8K2.u14107 = [0, 0, 243908438499, 852489024387, 643125397878, 53389452809, 0, 0] := by
  rw [show D2M8K2.u14107 = KTree.node D2M8K2.t14114 (nat_lit 30846260) (nat_lit 1489746517) (nat_lit 0) D2M8K2.t14115 from rfl, totK_node, tot14114, tot14115]
  decide +kernel

theorem arows14109 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14109 = true := by
  rw [show D2M8K2.u14109 = KTree.node D2M8K2.t14116 (nat_lit 30851976) (nat_lit 3525977212) (nat_lit 0) D2M8K2.t14117 from rfl, allE_node, rows14116, irow14109, rows14117]
  all_goals rfl

theorem atot14109 : totK PD2M8K2 D2M8K2.u14109 = [0, 0, 255119093089, 798019726358, 628066975388, 97772971467, 1332468113, 0] := by
  rw [show D2M8K2.u14109 = KTree.node D2M8K2.t14116 (nat_lit 30851976) (nat_lit 3525977212) (nat_lit 0) D2M8K2.t14117 from rfl, totK_node, tot14116, tot14117]
  decide +kernel

theorem arows14110 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14110 = true := by
  rw [show D2M8K2.u14110 = KTree.node D2M8K2.t14118 (nat_lit 30853421) (nat_lit 2146329069) (nat_lit 0) D2M8K2.t14119 from rfl, allE_node, rows14118, irow14110, rows14119]
  all_goals rfl

theorem atot14110 : totK PD2M8K2 D2M8K2.u14110 = [0, 0, 178493127927, 754864087451, 741100737410, 107123372540, 1229550402, 0] := by
  rw [show D2M8K2.u14110 = KTree.node D2M8K2.t14118 (nat_lit 30853421) (nat_lit 2146329069) (nat_lit 0) D2M8K2.t14119 from rfl, totK_node, tot14118, tot14119]
  decide +kernel

theorem arows14113 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14113 = true := by
  rw [show D2M8K2.u14113 = KTree.node D2M8K2.t14120 (nat_lit 30855289) (nat_lit 1527080184) (nat_lit 0) D2M8K2.t14121 from rfl, allE_node, rows14120, irow14113, rows14121]
  all_goals rfl

theorem atot14113 : totK PD2M8K2 D2M8K2.u14113 = [261615090966, 602699393009, 233001649798, 146310416343, 375286522700, 163540927763, 8304201444, 0] := by
  rw [show D2M8K2.u14113 = KTree.node D2M8K2.t14120 (nat_lit 30855289) (nat_lit 1527080184) (nat_lit 0) D2M8K2.t14121 from rfl, totK_node, tot14120, tot14121]
  decide +kernel

theorem arows14114 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14114 = true := by
  rw [show D2M8K2.u14114 = KTree.node D2M8K2.t14122 (nat_lit 30856809) (nat_lit 1459559663) (nat_lit 0) D2M8K2.t14123 from rfl, allE_node, rows14122, irow14114, rows14123]
  all_goals rfl

theorem atot14114 : totK PD2M8K2 D2M8K2.u14114 = [171650519448, 737503259174, 745442111907, 127146307682, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u14114 = KTree.node D2M8K2.t14122 (nat_lit 30856809) (nat_lit 1459559663) (nat_lit 0) D2M8K2.t14123 from rfl, totK_node, tot14122, tot14123]
  decide +kernel

theorem arows14116 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14116 = true := by
  rw [show D2M8K2.u14116 = KTree.node D2M8K2.t14124 (nat_lit 30862329) (nat_lit 1863757960) (nat_lit 0) D2M8K2.t14125 from rfl, allE_node, rows14124, irow14116, rows14125]
  all_goals rfl

theorem atot14116 : totK PD2M8K2 D2M8K2.u14116 = [259837572059, 840406297416, 648558810381, 70594526697, 0, 0, 0, 0] := by
  rw [show D2M8K2.u14116 = KTree.node D2M8K2.t14124 (nat_lit 30862329) (nat_lit 1863757960) (nat_lit 0) D2M8K2.t14125 from rfl, totK_node, tot14124, tot14125]
  decide +kernel

theorem arows14117 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14117 = true := by
  rw [show D2M8K2.u14117 = KTree.node D2M8K2.t14126 (nat_lit 30863830) (nat_lit 3417492328) (nat_lit 0) D2M8K2.t14127 from rfl, allE_node, rows14126, irow14117, rows14127]
  all_goals rfl

theorem atot14117 : totK PD2M8K2 D2M8K2.u14117 = [160040357605, 683044372709, 757967192955, 178838681252, 7166294683, 0, 0, 0] := by
  rw [show D2M8K2.u14117 = KTree.node D2M8K2.t14126 (nat_lit 30863830) (nat_lit 3417492328) (nat_lit 0) D2M8K2.t14127 from rfl, totK_node, tot14126, tot14127]
  decide +kernel

theorem arows14121 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14121 = true := by
  rw [show D2M8K2.u14121 = KTree.node D2M8K2.t14128 (nat_lit 30865661) (nat_lit 2135832880) (nat_lit 0) D2M8K2.t14129 from rfl, allE_node, rows14128, irow14121, rows14129]
  all_goals rfl

theorem atot14121 : totK PD2M8K2 D2M8K2.u14121 = [240438105743, 758094821355, 624566496263, 138479642812, 5883432551, 0, 0, 0] := by
  rw [show D2M8K2.u14121 = KTree.node D2M8K2.t14128 (nat_lit 30865661) (nat_lit 2135832880) (nat_lit 0) D2M8K2.t14129 from rfl, totK_node, tot14128, tot14129]
  decide +kernel

theorem arows14122 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14122 = true := by
  rw [show D2M8K2.u14122 = KTree.node D2M8K2.t14130 (nat_lit 30868144) (nat_lit 2300254899) (nat_lit 0) D2M8K2.t14131 from rfl, allE_node, rows14130, irow14122, rows14131]
  all_goals rfl

theorem atot14122 : totK PD2M8K2 D2M8K2.u14122 = [84779694899, 540228035270, 856315873705, 272507328559, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u14122 = KTree.node D2M8K2.t14130 (nat_lit 30868144) (nat_lit 2300254899) (nat_lit 0) D2M8K2.t14131 from rfl, totK_node, tot14130, tot14131]
  decide +kernel

theorem arows14124 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14124 = true := by
  rw [show D2M8K2.u14124 = KTree.node D2M8K2.t14132 (nat_lit 30869666) (nat_lit 3922922808) (nat_lit 0) D2M8K2.t14133 from rfl, allE_node, rows14132, irow14124, rows14133]
  all_goals rfl

theorem atot14124 : totK PD2M8K2 D2M8K2.u14124 = [378524389863, 908371908139, 461080214084, 41369982603, 0, 0, 0, 0] := by
  rw [show D2M8K2.u14124 = KTree.node D2M8K2.t14132 (nat_lit 30869666) (nat_lit 3922922808) (nat_lit 0) D2M8K2.t14133 from rfl, totK_node, tot14132, tot14133]
  decide +kernel

theorem arows14125 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14125 = true := by
  rw [show D2M8K2.u14125 = KTree.node D2M8K2.t14134 (nat_lit 30871592) (nat_lit 3607397541) (nat_lit 0) D2M8K2.t14135 from rfl, allE_node, rows14134, irow14125, rows14135]
  all_goals rfl

theorem atot14125 : totK PD2M8K2 D2M8K2.u14125 = [87414637357, 625815448531, 856839797782, 194811736435, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u14125 = KTree.node D2M8K2.t14134 (nat_lit 30871592) (nat_lit 3607397541) (nat_lit 0) D2M8K2.t14135 from rfl, totK_node, tot14134, tot14135]
  decide +kernel

theorem arows14128 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14128 = true := by
  rw [show D2M8K2.u14128 = KTree.node D2M8K2.t14136 (nat_lit 30873320) (nat_lit 3021238966) (nat_lit 0) D2M8K2.t14137 from rfl, allE_node, rows14136, irow14128, rows14137]
  all_goals rfl

theorem atot14128 : totK PD2M8K2 D2M8K2.u14128 = [328860779294, 902113822986, 545574114210, 51003448637, 0, 0, 0, 0] := by
  rw [show D2M8K2.u14128 = KTree.node D2M8K2.t14136 (nat_lit 30873320) (nat_lit 3021238966) (nat_lit 0) D2M8K2.t14137 from rfl, totK_node, tot14136, tot14137]
  decide +kernel

theorem arows14129 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14129 = true := by
  rw [show D2M8K2.u14129 = KTree.node D2M8K2.t14138 (nat_lit 30874992) (nat_lit 2883638721) (nat_lit 0) D2M8K2.t14139 from rfl, allE_node, rows14138, irow14129, rows14139]
  all_goals rfl

theorem atot14129 : totK PD2M8K2 D2M8K2.u14129 = [0, 395301943789, 952670693851, 401036416448, 22048779143, 0, 0, 0] := by
  rw [show D2M8K2.u14129 = KTree.node D2M8K2.t14138 (nat_lit 30874992) (nat_lit 2883638721) (nat_lit 0) D2M8K2.t14139 from rfl, totK_node, tot14138, tot14139]
  decide +kernel

theorem arows14131 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14131 = true := by
  rw [show D2M8K2.u14131 = KTree.node D2M8K2.t14140 (nat_lit 30876811) (nat_lit 1763380803) (nat_lit 0) D2M8K2.t14141 from rfl, allE_node, rows14140, irow14131, rows14141]
  all_goals rfl

theorem atot14131 : totK PD2M8K2 D2M8K2.u14131 = [0, 390983325106, 943318952052, 398300306499, 21817061227, 0, 0, 0] := by
  rw [show D2M8K2.u14131 = KTree.node D2M8K2.t14140 (nat_lit 30876811) (nat_lit 1763380803) (nat_lit 0) D2M8K2.t14141 from rfl, totK_node, tot14140, tot14141]
  decide +kernel

theorem arows14132 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14132 = true := by
  rw [show D2M8K2.u14132 = KTree.node D2M8K2.t14142 (nat_lit 30878335) (nat_lit 1515095849) (nat_lit 0) D2M8K2.t14143 from rfl, allE_node, rows14142, irow14132, rows14143]
  all_goals rfl

theorem atot14132 : totK PD2M8K2 D2M8K2.u14132 = [0, 124240402359, 690460336930, 777083659320, 142668472581, 1369150432, 0, 0] := by
  rw [show D2M8K2.u14132 = KTree.node D2M8K2.t14142 (nat_lit 30878335) (nat_lit 1515095849) (nat_lit 0) D2M8K2.t14143 from rfl, totK_node, tot14142, tot14143]
  decide +kernel

theorem arows14138 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14138 = true := by
  rw [show D2M8K2.u14138 = KTree.node D2M8K2.t14144 (nat_lit 30883635) (nat_lit 2459260658) (nat_lit 0) D2M8K2.t14145 from rfl, allE_node, rows14144, irow14138, rows14145]
  all_goals rfl

theorem atot14138 : totK PD2M8K2 D2M8K2.u14138 = [0, 334983630018, 944320322695, 476028193901, 22786786411, 0, 0, 0] := by
  rw [show D2M8K2.u14138 = KTree.node D2M8K2.t14144 (nat_lit 30883635) (nat_lit 2459260658) (nat_lit 0) D2M8K2.t14145 from rfl, totK_node, tot14144, tot14145]
  decide +kernel

theorem arows14139 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14139 = true := by
  rw [show D2M8K2.u14139 = KTree.node D2M8K2.t14146 (nat_lit 30887477) (nat_lit 2245164743) (nat_lit 0) D2M8K2.t14147 from rfl, allE_node, rows14146, irow14139, rows14147]
  all_goals rfl

theorem atot14139 : totK PD2M8K2 D2M8K2.u14139 = [0, 406242798975, 938574293104, 414556438038, 26226771964, 0, 0, 0] := by
  rw [show D2M8K2.u14139 = KTree.node D2M8K2.t14146 (nat_lit 30887477) (nat_lit 2245164743) (nat_lit 0) D2M8K2.t14147 from rfl, totK_node, tot14146, tot14147]
  decide +kernel

theorem arows14141 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14141 = true := by
  rw [show D2M8K2.u14141 = KTree.node D2M8K2.t14148 (nat_lit 30890608) (nat_lit 2622087099) (nat_lit 0) D2M8K2.t14149 from rfl, allE_node, rows14148, irow14141, rows14149]
  all_goals rfl

theorem atot14141 : totK PD2M8K2 D2M8K2.u14141 = [0, 360141389712, 936587402902, 438462155702, 23530630971, 0, 0, 0] := by
  rw [show D2M8K2.u14141 = KTree.node D2M8K2.t14148 (nat_lit 30890608) (nat_lit 2622087099) (nat_lit 0) D2M8K2.t14149 from rfl, totK_node, tot14148, tot14149]
  decide +kernel

theorem arows14142 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14142 = true := by
  rw [show D2M8K2.u14142 = KTree.node D2M8K2.t14150 (nat_lit 30893954) (nat_lit 3946219640) (nat_lit 0) D2M8K2.t14151 from rfl, allE_node, rows14150, irow14142, rows14151]
  all_goals rfl

theorem atot14142 : totK PD2M8K2 D2M8K2.u14142 = [0, 347400712082, 950053726044, 487883566616, 22623634463, 0, 0, 0] := by
  rw [show D2M8K2.u14142 = KTree.node D2M8K2.t14150 (nat_lit 30893954) (nat_lit 3946219640) (nat_lit 0) D2M8K2.t14151 from rfl, totK_node, tot14150, tot14151]
  decide +kernel

theorem arows14145 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14145 = true := by
  rw [show D2M8K2.u14145 = KTree.node D2M8K2.t14152 (nat_lit 30900880) (nat_lit 3686841180) (nat_lit 0) D2M8K2.t14153 from rfl, allE_node, rows14152, irow14145, rows14153]
  all_goals rfl

theorem atot14145 : totK PD2M8K2 D2M8K2.u14145 = [353535550406, 907569306044, 503867097813, 68191360519, 7093008096, 0, 0, 0] := by
  rw [show D2M8K2.u14145 = KTree.node D2M8K2.t14152 (nat_lit 30900880) (nat_lit 3686841180) (nat_lit 0) D2M8K2.t14153 from rfl, totK_node, tot14152, tot14153]
  decide +kernel

theorem arows14146 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14146 = true := by
  rw [show D2M8K2.u14146 = KTree.node D2M8K2.t14154 (nat_lit 30902359) (nat_lit 2188946791) (nat_lit 0) D2M8K2.t14155 from rfl, allE_node, rows14154, irow14146, rows14155]
  all_goals rfl

theorem atot14146 : totK PD2M8K2 D2M8K2.u14146 = [89058976036, 508090248670, 825142499589, 372893511236, 29394892645, 0, 0, 0] := by
  rw [show D2M8K2.u14146 = KTree.node D2M8K2.t14154 (nat_lit 30902359) (nat_lit 2188946791) (nat_lit 0) D2M8K2.t14155 from rfl, totK_node, tot14154, tot14155]
  decide +kernel

theorem arows14148 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14148 = true := by
  rw [show D2M8K2.u14148 = KTree.node D2M8K2.t14156 (nat_lit 30903650) (nat_lit 3160816433) (nat_lit 0) D2M8K2.t14157 from rfl, allE_node, rows14156, irow14148, rows14157]
  all_goals rfl

theorem atot14148 : totK PD2M8K2 D2M8K2.u14148 = [234658447918, 684934522542, 687237861340, 220588187652, 8214505460, 0, 0, 0] := by
  rw [show D2M8K2.u14148 = KTree.node D2M8K2.t14156 (nat_lit 30903650) (nat_lit 3160816433) (nat_lit 0) D2M8K2.t14157 from rfl, totK_node, tot14156, tot14157]
  decide +kernel

theorem arows14149 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14149 = true := by
  rw [show D2M8K2.u14149 = KTree.node D2M8K2.t14158 (nat_lit 30905128) (nat_lit 3829952091) (nat_lit 0) D2M8K2.t14159 from rfl, allE_node, rows14158, irow14149, rows14159]
  all_goals rfl

theorem atot14149 : totK PD2M8K2 D2M8K2.u14149 = [190243527887, 771839847009, 715544006966, 116996438106, 1163840124, 0, 0, 0] := by
  rw [show D2M8K2.u14149 = KTree.node D2M8K2.t14158 (nat_lit 30905128) (nat_lit 3829952091) (nat_lit 0) D2M8K2.t14159 from rfl, totK_node, tot14158, tot14159]
  decide +kernel

theorem arows14153 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14153 = true := by
  rw [show D2M8K2.u14153 = KTree.node D2M8K2.t14160 (nat_lit 30906811) (nat_lit 1489127166) (nat_lit 0) D2M8K2.t14161 from rfl, allE_node, rows14160, irow14153, rows14161]
  all_goals rfl

theorem atot14153 : totK PD2M8K2 D2M8K2.u14153 = [177909920641, 638892866237, 757091027064, 223596515130, 11873025674, 0, 0, 0] := by
  rw [show D2M8K2.u14153 = KTree.node D2M8K2.t14160 (nat_lit 30906811) (nat_lit 1489127166) (nat_lit 0) D2M8K2.t14161 from rfl, totK_node, tot14160, tot14161]
  decide +kernel

theorem arows14154 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14154 = true := by
  rw [show D2M8K2.u14154 = KTree.node D2M8K2.t14162 (nat_lit 30909075) (nat_lit 3689019017) (nat_lit 0) D2M8K2.t14163 from rfl, allE_node, rows14162, irow14154, rows14163]
  all_goals rfl

theorem atot14154 : totK PD2M8K2 D2M8K2.u14154 = [153907372348, 678207349091, 777474041255, 196016248385, 8344820176, 0, 0, 0] := by
  rw [show D2M8K2.u14154 = KTree.node D2M8K2.t14162 (nat_lit 30909075) (nat_lit 3689019017) (nat_lit 0) D2M8K2.t14163 from rfl, totK_node, tot14162, tot14163]
  decide +kernel

theorem arows14156 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14156 = true := by
  rw [show D2M8K2.u14156 = KTree.node D2M8K2.t14164 (nat_lit 30910994) (nat_lit 4099311819) (nat_lit 0) D2M8K2.t14165 from rfl, allE_node, rows14164, irow14156, rows14165]
  all_goals rfl

theorem atot14156 : totK PD2M8K2 D2M8K2.u14156 = [317055434513, 871566992980, 563938747422, 75249489406, 2498878989, 0, 0, 0] := by
  rw [show D2M8K2.u14156 = KTree.node D2M8K2.t14164 (nat_lit 30910994) (nat_lit 4099311819) (nat_lit 0) D2M8K2.t14165 from rfl, totK_node, tot14164, tot14165]
  decide +kernel

theorem arows14157 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14157 = true := by
  rw [show D2M8K2.u14157 = KTree.node D2M8K2.t14166 (nat_lit 30912797) (nat_lit 2324370134) (nat_lit 0) D2M8K2.t14167 from rfl, allE_node, rows14166, irow14157, rows14167]
  all_goals rfl

theorem atot14157 : totK PD2M8K2 D2M8K2.u14157 = [111316903953, 650841942402, 833832527238, 191398436223, 4976872846, 0, 0, 0] := by
  rw [show D2M8K2.u14157 = KTree.node D2M8K2.t14166 (nat_lit 30912797) (nat_lit 2324370134) (nat_lit 0) D2M8K2.t14167 from rfl, totK_node, tot14166, tot14167]
  decide +kernel

theorem arows14160 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14160 = true := by
  rw [show D2M8K2.u14160 = KTree.node D2M8K2.t14168 (nat_lit 30914635) (nat_lit 1481904274) (nat_lit 0) D2M8K2.t14169 from rfl, allE_node, rows14168, irow14160, rows14169]
  all_goals rfl

theorem atot14160 : totK PD2M8K2 D2M8K2.u14160 = [369552348654, 936449408880, 505020630428, 39886188093, 0, 0, 0, 0] := by
  rw [show D2M8K2.u14160 = KTree.node D2M8K2.t14168 (nat_lit 30914635) (nat_lit 1481904274) (nat_lit 0) D2M8K2.t14169 from rfl, totK_node, tot14168, tot14169]
  decide +kernel

theorem arows14161 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14161 = true := by
  rw [show D2M8K2.u14161 = KTree.node D2M8K2.t14170 (nat_lit 30916332) (nat_lit 2377895191) (nat_lit 0) D2M8K2.t14171 from rfl, allE_node, rows14170, irow14161, rows14171]
  all_goals rfl

theorem atot14161 : totK PD2M8K2 D2M8K2.u14161 = [0, 483276779174, 984641153485, 316231459090, 9902458238, 0, 0, 0] := by
  rw [show D2M8K2.u14161 = KTree.node D2M8K2.t14170 (nat_lit 30916332) (nat_lit 2377895191) (nat_lit 0) D2M8K2.t14171 from rfl, totK_node, tot14170, tot14171]
  decide +kernel

theorem arows14163 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14163 = true := by
  rw [show D2M8K2.u14163 = KTree.node D2M8K2.t14172 (nat_lit 30921542) (nat_lit 3991657965) (nat_lit 0) D2M8K2.t14173 from rfl, allE_node, rows14172, irow14163, rows14173]
  all_goals rfl

theorem atot14163 : totK PD2M8K2 D2M8K2.u14163 = [0, 352685976395, 909962973870, 522988756706, 46908933934, 0, 0, 0] := by
  rw [show D2M8K2.u14163 = KTree.node D2M8K2.t14172 (nat_lit 30921542) (nat_lit 3991657965) (nat_lit 0) D2M8K2.t14173 from rfl, totK_node, tot14172, tot14173]
  decide +kernel

theorem arows14164 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14164 = true := by
  rw [show D2M8K2.u14164 = KTree.node D2M8K2.t14174 (nat_lit 30923043) (nat_lit 3687294742) (nat_lit 0) D2M8K2.t14175 from rfl, allE_node, rows14174, irow14164, rows14175]
  all_goals rfl

theorem atot14164 : totK PD2M8K2 D2M8K2.u14164 = [0, 88825966916, 557131176038, 817967854422, 325895987312, 26904681413, 0, 0] := by
  rw [show D2M8K2.u14164 = KTree.node D2M8K2.t14174 (nat_lit 30923043) (nat_lit 3687294742) (nat_lit 0) D2M8K2.t14175 from rfl, totK_node, tot14174, tot14175]
  decide +kernel

theorem arows14169 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14169 = true := by
  rw [show D2M8K2.u14169 = KTree.node D2M8K2.t14176 (nat_lit 30924297) (nat_lit 1802595438) (nat_lit 0) D2M8K2.t14177 from rfl, allE_node, rows14176, irow14169, rows14177]
  all_goals rfl

theorem atot14169 : totK PD2M8K2 D2M8K2.u14169 = [0, 203865752518, 643570210762, 702382692383, 238978927664, 8969136212, 0, 0] := by
  rw [show D2M8K2.u14169 = KTree.node D2M8K2.t14176 (nat_lit 30924297) (nat_lit 1802595438) (nat_lit 0) D2M8K2.t14177 from rfl, totK_node, tot14176, tot14177]
  decide +kernel

theorem arows14170 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14170 = true := by
  rw [show D2M8K2.u14170 = KTree.node D2M8K2.t14178 (nat_lit 30925800) (nat_lit 2651952762) (nat_lit 0) D2M8K2.t14179 from rfl, allE_node, rows14178, irow14170, rows14179]
  all_goals rfl

theorem atot14170 : totK PD2M8K2 D2M8K2.u14170 = [0, 215327935882, 839122948980, 673039577673, 68748520759, 0, 0, 0] := by
  rw [show D2M8K2.u14170 = KTree.node D2M8K2.t14178 (nat_lit 30925800) (nat_lit 2651952762) (nat_lit 0) D2M8K2.t14179 from rfl, totK_node, tot14178, tot14179]
  decide +kernel

theorem arows14172 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14172 = true := by
  rw [show D2M8K2.u14172 = KTree.node D2M8K2.t14180 (nat_lit 30928102) (nat_lit 3646599695) (nat_lit 0) D2M8K2.t14181 from rfl, allE_node, rows14180, irow14172, rows14181]
  all_goals rfl

theorem atot14172 : totK PD2M8K2 D2M8K2.u14172 = [0, 206140332299, 676594149973, 739764587652, 183288660210, 5159868635, 0, 0] := by
  rw [show D2M8K2.u14172 = KTree.node D2M8K2.t14180 (nat_lit 30928102) (nat_lit 3646599695) (nat_lit 0) D2M8K2.t14181 from rfl, totK_node, tot14180, tot14181]
  decide +kernel

theorem arows14173 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14173 = true := by
  rw [show D2M8K2.u14173 = KTree.node D2M8K2.t14182 (nat_lit 30929891) (nat_lit 2942534784) (nat_lit 0) D2M8K2.t14183 from rfl, allE_node, rows14182, irow14173, rows14183]
  all_goals rfl

theorem atot14173 : totK PD2M8K2 D2M8K2.u14173 = [0, 121044857238, 666474056246, 818143435339, 200274055375, 5218872685, 0, 0] := by
  rw [show D2M8K2.u14173 = KTree.node D2M8K2.t14182 (nat_lit 30929891) (nat_lit 2942534784) (nat_lit 0) D2M8K2.t14183 from rfl, totK_node, tot14182, tot14183]
  decide +kernel

theorem arows14176 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14176 = true := by
  rw [show D2M8K2.u14176 = KTree.node D2M8K2.t14184 (nat_lit 30931828) (nat_lit 4062894510) (nat_lit 0) D2M8K2.t14185 from rfl, allE_node, rows14184, irow14176, rows14185]
  all_goals rfl

theorem atot14176 : totK PD2M8K2 D2M8K2.u14176 = [0, 381555047773, 910046484760, 479287650707, 46525170298, 0, 0, 0] := by
  rw [show D2M8K2.u14176 = KTree.node D2M8K2.t14184 (nat_lit 30931828) (nat_lit 4062894510) (nat_lit 0) D2M8K2.t14185 from rfl, totK_node, tot14184, tot14185]
  decide +kernel

theorem arows14177 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14177 = true := by
  rw [show D2M8K2.u14177 = KTree.node D2M8K2.t14186 (nat_lit 30933895) (nat_lit 2391364211) (nat_lit 0) D2M8K2.t14187 from rfl, allE_node, rows14186, irow14177, rows14187]
  all_goals rfl

theorem atot14177 : totK PD2M8K2 D2M8K2.u14177 = [0, 124274589184, 713282246485, 824283167299, 138975057601, 1415142070, 0, 0] := by
  rw [show D2M8K2.u14177 = KTree.node D2M8K2.t14186 (nat_lit 30933895) (nat_lit 2391364211) (nat_lit 0) D2M8K2.t14187 from rfl, totK_node, tot14186, tot14187]
  decide +kernel

theorem arows14179 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14179 = true := by
  rw [show D2M8K2.u14179 = KTree.node D2M8K2.t14188 (nat_lit 30935611) (nat_lit 2241272188) (nat_lit 0) D2M8K2.t14189 from rfl, allE_node, rows14188, irow14179, rows14189]
  all_goals rfl

theorem atot14179 : totK PD2M8K2 D2M8K2.u14179 = [0, 293883890082, 904378568341, 587727767186, 55245941868, 0, 0, 0] := by
  rw [show D2M8K2.u14179 = KTree.node D2M8K2.t14188 (nat_lit 30935611) (nat_lit 2241272188) (nat_lit 0) D2M8K2.t14189 from rfl, totK_node, tot14188, tot14189]
  decide +kernel

theorem arows14180 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14180 = true := by
  rw [show D2M8K2.u14180 = KTree.node D2M8K2.t14190 (nat_lit 30937514) (nat_lit 3701539024) (nat_lit 0) D2M8K2.t14191 from rfl, allE_node, rows14190, irow14180, rows14191]
  all_goals rfl

theorem atot14180 : totK PD2M8K2 D2M8K2.u14180 = [108461727635, 243413572888, 406609059917, 745371977800, 264964415950, 9302370699, 0, 0] := by
  rw [show D2M8K2.u14180 = KTree.node D2M8K2.t14190 (nat_lit 30937514) (nat_lit 3701539024) (nat_lit 0) D2M8K2.t14191 from rfl, totK_node, tot14190, tot14191]
  decide +kernel

theorem arows14184 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14184 = true := by
  rw [show D2M8K2.u14184 = KTree.node D2M8K2.t14192 (nat_lit 30939339) (nat_lit 2123811147) (nat_lit 0) D2M8K2.t14193 from rfl, allE_node, rows14192, irow14184, rows14193]
  all_goals rfl

theorem atot14184 : totK PD2M8K2 D2M8K2.u14184 = [304714786344, 881528228194, 535448790286, 46510168284, 0, 0, 0, 0] := by
  rw [show D2M8K2.u14184 = KTree.node D2M8K2.t14192 (nat_lit 30939339) (nat_lit 2123811147) (nat_lit 0) D2M8K2.t14193 from rfl, totK_node, tot14192, tot14193]
  decide +kernel

theorem arows14185 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14185 = true := by
  rw [show D2M8K2.u14185 = KTree.node D2M8K2.t14194 (nat_lit 30941300) (nat_lit 2623164725) (nat_lit 0) D2M8K2.t14195 from rfl, allE_node, rows14194, irow14185, rows14195]
  all_goals rfl

theorem atot14185 : totK PD2M8K2 D2M8K2.u14185 = [171798127067, 691712562713, 809725479948, 149349690278, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u14185 = KTree.node D2M8K2.t14194 (nat_lit 30941300) (nat_lit 2623164725) (nat_lit 0) D2M8K2.t14195 from rfl, totK_node, tot14194, tot14195]
  decide +kernel

theorem arows14187 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14187 = true := by
  rw [show D2M8K2.u14187 = KTree.node D2M8K2.t14196 (nat_lit 30942922) (nat_lit 3186249782) (nat_lit 0) D2M8K2.t14197 from rfl, allE_node, rows14196, irow14187, rows14197]
  all_goals rfl

theorem atot14187 : totK PD2M8K2 D2M8K2.u14187 = [251745748179, 825942205407, 606818286113, 113230538281, 13135812311, 0, 0, 0] := by
  rw [show D2M8K2.u14187 = KTree.node D2M8K2.t14196 (nat_lit 30942922) (nat_lit 3186249782) (nat_lit 0) D2M8K2.t14197 from rfl, totK_node, tot14196, tot14197]
  decide +kernel

theorem arows14188 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14188 = true := by
  rw [show D2M8K2.u14188 = KTree.node D2M8K2.t14198 (nat_lit 30944452) (nat_lit 3565688996) (nat_lit 0) D2M8K2.t14199 from rfl, allE_node, rows14198, irow14188, rows14199]
  all_goals rfl

theorem atot14188 : totK PD2M8K2 D2M8K2.u14188 = [37176659836, 378986731095, 888959597914, 460022380744, 24256032251, 0, 0, 0] := by
  rw [show D2M8K2.u14188 = KTree.node D2M8K2.t14198 (nat_lit 30944452) (nat_lit 3565688996) (nat_lit 0) D2M8K2.t14199 from rfl, totK_node, tot14198, tot14199]
  decide +kernel

theorem arows14191 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14191 = true := by
  rw [show D2M8K2.u14191 = KTree.node D2M8K2.t14200 (nat_lit 30945652) (nat_lit 4076853445) (nat_lit 0) D2M8K2.t14201 from rfl, allE_node, rows14200, irow14191, rows14201]
  all_goals rfl

theorem atot14191 : totK PD2M8K2 D2M8K2.u14191 = [374874674075, 945399814836, 481186347329, 35498527673, 0, 0, 0, 0] := by
  rw [show D2M8K2.u14191 = KTree.node D2M8K2.t14200 (nat_lit 30945652) (nat_lit 4076853445) (nat_lit 0) D2M8K2.t14201 from rfl, totK_node, tot14200, tot14201]
  decide +kernel

theorem arows14192 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14192 = true := by
  rw [show D2M8K2.u14192 = KTree.node D2M8K2.t14202 (nat_lit 30947174) (nat_lit 4020885079) (nat_lit 0) D2M8K2.t14203 from rfl, allE_node, rows14202, irow14192, rows14203]
  all_goals rfl

theorem atot14192 : totK PD2M8K2 D2M8K2.u14192 = [33828699371, 516567343460, 939807265608, 283495033189, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u14192 = KTree.node D2M8K2.t14202 (nat_lit 30947174) (nat_lit 4020885079) (nat_lit 0) D2M8K2.t14203 from rfl, totK_node, tot14202, tot14203]
  decide +kernel

theorem arows14194 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14194 = true := by
  rw [show D2M8K2.u14194 = KTree.node D2M8K2.t14204 (nat_lit 30952421) (nat_lit 2371143950) (nat_lit 0) D2M8K2.t14205 from rfl, allE_node, rows14204, irow14194, rows14205]
  all_goals rfl

theorem atot14194 : totK PD2M8K2 D2M8K2.u14194 = [327311157893, 871305653483, 540511514571, 58180557387, 0, 0, 0, 0] := by
  rw [show D2M8K2.u14194 = KTree.node D2M8K2.t14204 (nat_lit 30952421) (nat_lit 2371143950) (nat_lit 0) D2M8K2.t14205 from rfl, totK_node, tot14204, tot14205]
  decide +kernel

theorem arows14195 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14195 = true := by
  rw [show D2M8K2.u14195 = KTree.node D2M8K2.t14206 (nat_lit 30954043) (nat_lit 1712318163) (nat_lit 0) D2M8K2.t14207 from rfl, allE_node, rows14206, irow14195, rows14207]
  all_goals rfl

theorem atot14195 : totK PD2M8K2 D2M8K2.u14195 = [80124423846, 613742064666, 873917075621, 199553439987, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u14195 = KTree.node D2M8K2.t14206 (nat_lit 30954043) (nat_lit 1712318163) (nat_lit 0) D2M8K2.t14207 from rfl, totK_node, tot14206, tot14207]
  decide +kernel

theorem arows14202 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14202 = true := by
  rw [show D2M8K2.u14202 = KTree.node D2M8K2.t14208 (nat_lit 30955988) (nat_lit 2983625175) (nat_lit 0) D2M8K2.t14209 from rfl, allE_node, rows14208, irow14202, rows14209]
  all_goals rfl

theorem atot14202 : totK PD2M8K2 D2M8K2.u14202 = [389415236204, 943964485221, 469460376274, 36011625415, 0, 0, 0, 0] := by
  rw [show D2M8K2.u14202 = KTree.node D2M8K2.t14208 (nat_lit 30955988) (nat_lit 2983625175) (nat_lit 0) D2M8K2.t14209 from rfl, totK_node, tot14208, tot14209]
  decide +kernel

theorem arows14203 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14203 = true := by
  rw [show D2M8K2.u14203 = KTree.node D2M8K2.t14210 (nat_lit 30957535) (nat_lit 2219190500) (nat_lit 0) D2M8K2.t14211 from rfl, allE_node, rows14210, irow14203, rows14211]
  all_goals rfl

theorem atot14203 : totK PD2M8K2 D2M8K2.u14203 = [23713104488, 527048175438, 944741155987, 286876242778, 8692638541, 0, 0, 0] := by
  rw [show D2M8K2.u14203 = KTree.node D2M8K2.t14210 (nat_lit 30957535) (nat_lit 2219190500) (nat_lit 0) D2M8K2.t14211 from rfl, totK_node, tot14210, tot14211]
  decide +kernel

theorem arows14205 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14205 = true := by
  rw [show D2M8K2.u14205 = KTree.node D2M8K2.t14212 (nat_lit 30959526) (nat_lit 2725222853) (nat_lit 0) D2M8K2.t14213 from rfl, allE_node, rows14212, irow14205, rows14213]
  all_goals rfl

theorem atot14205 : totK PD2M8K2 D2M8K2.u14205 = [0, 361684315175, 937893627174, 428327981881, 25427706409, 0, 0, 0] := by
  rw [show D2M8K2.u14205 = KTree.node D2M8K2.t14212 (nat_lit 30959526) (nat_lit 2725222853) (nat_lit 0) D2M8K2.t14213 from rfl, totK_node, tot14212, tot14213]
  decide +kernel

theorem arows14206 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14206 = true := by
  rw [show D2M8K2.u14206 = KTree.node D2M8K2.t14214 (nat_lit 30960850) (nat_lit 3678519383) (nat_lit 0) D2M8K2.t14215 from rfl, allE_node, rows14214, irow14206, rows14215]
  all_goals rfl

theorem atot14206 : totK PD2M8K2 D2M8K2.u14206 = [0, 127042647270, 723998325726, 778982195920, 108089697200, 1206465782, 0, 0] := by
  rw [show D2M8K2.u14206 = KTree.node D2M8K2.t14214 (nat_lit 30960850) (nat_lit 3678519383) (nat_lit 0) D2M8K2.t14215 from rfl, totK_node, tot14214, tot14215]
  decide +kernel

theorem arows14209 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14209 = true := by
  rw [show D2M8K2.u14209 = KTree.node D2M8K2.t14216 (nat_lit 30963260) (nat_lit 2774860709) (nat_lit 0) D2M8K2.t14217 from rfl, allE_node, rows14216, irow14209, rows14217]
  all_goals rfl

theorem atot14209 : totK PD2M8K2 D2M8K2.u14209 = [0, 381371205607, 945089188736, 461251566071, 35946416960, 0, 0, 0] := by
  rw [show D2M8K2.u14209 = KTree.node D2M8K2.t14216 (nat_lit 30963260) (nat_lit 2774860709) (nat_lit 0) D2M8K2.t14217 from rfl, totK_node, tot14216, tot14217]
  decide +kernel

theorem arows14210 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14210 = true := by
  rw [show D2M8K2.u14210 = KTree.node D2M8K2.t14218 (nat_lit 30966248) (nat_lit 3641241653) (nat_lit 0) D2M8K2.t14219 from rfl, allE_node, rows14218, irow14210, rows14219]
  all_goals rfl

theorem atot14210 : totK PD2M8K2 D2M8K2.u14210 = [0, 354993291061, 926485081271, 495959333859, 37117105344, 0, 0, 0] := by
  rw [show D2M8K2.u14210 = KTree.node D2M8K2.t14218 (nat_lit 30966248) (nat_lit 3641241653) (nat_lit 0) D2M8K2.t14219 from rfl, totK_node, tot14218, tot14219]
  decide +kernel

theorem arows14212 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14212 = true := by
  rw [show D2M8K2.u14212 = KTree.node D2M8K2.t14220 (nat_lit 30967757) (nat_lit 1780254780) (nat_lit 0) D2M8K2.t14221 from rfl, allE_node, rows14220, irow14212, rows14221]
  all_goals rfl

theorem atot14212 : totK PD2M8K2 D2M8K2.u14212 = [0, 88579576547, 625493990573, 827162754473, 211428637631, 9579374723, 0, 0] := by
  rw [show D2M8K2.u14212 = KTree.node D2M8K2.t14220 (nat_lit 30967757) (nat_lit 1780254780) (nat_lit 0) D2M8K2.t14221 from rfl, totK_node, tot14220, tot14221]
  decide +kernel

theorem arows14213 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14213 = true := by
  rw [show D2M8K2.u14213 = KTree.node D2M8K2.t14222 (nat_lit 30973051) (nat_lit 1714908850) (nat_lit 0) D2M8K2.t14223 from rfl, allE_node, rows14222, irow14213, rows14223]
  all_goals rfl

theorem atot14213 : totK PD2M8K2 D2M8K2.u14213 = [0, 307831994127, 837111449325, 522874540870, 89417636896, 3436822651, 0, 0] := by
  rw [show D2M8K2.u14213 = KTree.node D2M8K2.t14222 (nat_lit 30973051) (nat_lit 1714908850) (nat_lit 0) D2M8K2.t14223 from rfl, totK_node, tot14222, tot14223]
  decide +kernel

theorem arows14217 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14217 = true := by
  rw [show D2M8K2.u14217 = KTree.node D2M8K2.t14224 (nat_lit 30974727) (nat_lit 2422668043) (nat_lit 0) D2M8K2.t14225 from rfl, allE_node, rows14224, irow14217, rows14225]
  all_goals rfl

theorem atot14217 : totK PD2M8K2 D2M8K2.u14217 = [0, 89748608524, 642220022590, 805969727204, 156163873857, 3018368746, 0, 0] := by
  rw [show D2M8K2.u14217 = KTree.node D2M8K2.t14224 (nat_lit 30974727) (nat_lit 2422668043) (nat_lit 0) D2M8K2.t14225 from rfl, totK_node, tot14224, tot14225]
  decide +kernel

theorem arows14218 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14218 = true := by
  rw [show D2M8K2.u14218 = KTree.node D2M8K2.t14226 (nat_lit 30976716) (nat_lit 3540046477) (nat_lit 0) D2M8K2.t14227 from rfl, allE_node, rows14226, irow14218, rows14227]
  all_goals rfl

theorem atot14218 : totK PD2M8K2 D2M8K2.u14218 = [0, 402885364218, 940208115259, 444016752985, 30691740744, 0, 0, 0] := by
  rw [show D2M8K2.u14218 = KTree.node D2M8K2.t14226 (nat_lit 30976716) (nat_lit 3540046477) (nat_lit 0) D2M8K2.t14227 from rfl, totK_node, tot14226, tot14227]
  decide +kernel

theorem arows14220 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14220 = true := by
  rw [show D2M8K2.u14220 = KTree.node D2M8K2.t14228 (nat_lit 31021756) (nat_lit 3886449044) (nat_lit 0) D2M8K2.t14229 from rfl, allE_node, rows14228, irow14220, rows14229]
  all_goals rfl

theorem atot14220 : totK PD2M8K2 D2M8K2.u14220 = [328213033831, 803654215737, 490132500329, 145499677859, 13554132542, 0, 0, 0] := by
  rw [show D2M8K2.u14220 = KTree.node D2M8K2.t14228 (nat_lit 31021756) (nat_lit 3886449044) (nat_lit 0) D2M8K2.t14229 from rfl, totK_node, tot14228, tot14229]
  decide +kernel

theorem arows14221 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14221 = true := by
  rw [show D2M8K2.u14221 = KTree.node D2M8K2.t14230 (nat_lit 31023376) (nat_lit 3413034556) (nat_lit 0) D2M8K2.t14231 from rfl, allE_node, rows14230, irow14221, rows14231]
  all_goals rfl

theorem atot14221 : totK PD2M8K2 D2M8K2.u14221 = [105590054423, 666773455067, 856239521763, 151875395492, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u14221 = KTree.node D2M8K2.t14230 (nat_lit 31023376) (nat_lit 3413034556) (nat_lit 0) D2M8K2.t14231 from rfl, totK_node, tot14230, tot14231]
  decide +kernel

theorem arows14224 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14224 = true := by
  rw [show D2M8K2.u14224 = KTree.node D2M8K2.t14232 (nat_lit 31025451) (nat_lit 3675647139) (nat_lit 0) D2M8K2.t14233 from rfl, allE_node, rows14232, irow14224, rows14233]
  all_goals rfl

theorem atot14224 : totK PD2M8K2 D2M8K2.u14224 = [368589503553, 930898089674, 495649830750, 41567359730, 0, 0, 0, 0] := by
  rw [show D2M8K2.u14224 = KTree.node D2M8K2.t14232 (nat_lit 31025451) (nat_lit 3675647139) (nat_lit 0) D2M8K2.t14233 from rfl, totK_node, tot14232, tot14233]
  decide +kernel

theorem arows14225 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14225 = true := by
  rw [show D2M8K2.u14225 = KTree.node D2M8K2.t14234 (nat_lit 31026959) (nat_lit 2631143178) (nat_lit 0) D2M8K2.t14235 from rfl, allE_node, rows14234, irow14225, rows14235]
  all_goals rfl

theorem atot14225 : totK PD2M8K2 D2M8K2.u14225 = [0, 393317278668, 936328451725, 449333716194, 29380165115, 0, 0, 0] := by
  rw [show D2M8K2.u14225 = KTree.node D2M8K2.t14234 (nat_lit 31026959) (nat_lit 2631143178) (nat_lit 0) D2M8K2.t14235 from rfl, totK_node, tot14234, tot14235]
  decide +kernel

theorem arows14227 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14227 = true := by
  rw [show D2M8K2.u14227 = KTree.node D2M8K2.t14236 (nat_lit 31028354) (nat_lit 4107375869) (nat_lit 0) D2M8K2.t14237 from rfl, allE_node, rows14236, irow14227, rows14237]
  all_goals rfl

theorem atot14227 : totK PD2M8K2 D2M8K2.u14227 = [312052554122, 809029181136, 558059359817, 138297170862, 6778541047, 0, 0, 0] := by
  rw [show D2M8K2.u14227 = KTree.node D2M8K2.t14236 (nat_lit 31028354) (nat_lit 4107375869) (nat_lit 0) D2M8K2.t14237 from rfl, totK_node, tot14236, tot14237]
  decide +kernel

theorem arows14228 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14228 = true := by
  rw [show D2M8K2.u14228 = KTree.node D2M8K2.t14238 (nat_lit 31029838) (nat_lit 3797181874) (nat_lit 0) D2M8K2.t14239 from rfl, allE_node, rows14238, irow14228, rows14239]
  all_goals rfl

theorem atot14228 : totK PD2M8K2 D2M8K2.u14228 = [112767649574, 643012697421, 809286231670, 209466696824, 9587713104, 0, 0, 0] := by
  rw [show D2M8K2.u14228 = KTree.node D2M8K2.t14238 (nat_lit 31029838) (nat_lit 3797181874) (nat_lit 0) D2M8K2.t14239 from rfl, totK_node, tot14238, tot14239]
  decide +kernel

theorem arows14233 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14233 = true := by
  rw [show D2M8K2.u14233 = KTree.node D2M8K2.t14240 (nat_lit 31035151) (nat_lit 1521386076) (nat_lit 0) D2M8K2.t14241 from rfl, allE_node, rows14240, irow14233, rows14241]
  all_goals rfl

theorem atot14233 : totK PD2M8K2 D2M8K2.u14233 = [259886307317, 774734098746, 634482268651, 125229800300, 3462014130, 0, 0, 0] := by
  rw [show D2M8K2.u14233 = KTree.node D2M8K2.t14240 (nat_lit 31035151) (nat_lit 1521386076) (nat_lit 0) D2M8K2.t14241 from rfl, totK_node, tot14240, tot14241]
  decide +kernel

theorem arows14234 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14234 = true := by
  rw [show D2M8K2.u14234 = KTree.node D2M8K2.t14242 (nat_lit 31036669) (nat_lit 1214320018) (nat_lit 0) D2M8K2.t14243 from rfl, allE_node, rows14242, irow14234, rows14243]
  all_goals rfl

theorem atot14234 : totK PD2M8K2 D2M8K2.u14234 = [164271273082, 741835666428, 771264617363, 122983044461, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u14234 = KTree.node D2M8K2.t14242 (nat_lit 31036669) (nat_lit 1214320018) (nat_lit 0) D2M8K2.t14243 from rfl, totK_node, tot14242, tot14243]
  decide +kernel

theorem arows14236 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14236 = true := by
  rw [show D2M8K2.u14236 = KTree.node D2M8K2.t14244 (nat_lit 31042384) (nat_lit 3423385323) (nat_lit 0) D2M8K2.t14245 from rfl, allE_node, rows14244, irow14236, rows14245]
  all_goals rfl

theorem atot14236 : totK PD2M8K2 D2M8K2.u14236 = [0, 407321535445, 943796359848, 387158895546, 22145572651, 0, 0, 0] := by
  rw [show D2M8K2.u14236 = KTree.node D2M8K2.t14244 (nat_lit 31042384) (nat_lit 3423385323) (nat_lit 0) D2M8K2.t14245 from rfl, totK_node, tot14244, tot14245]
  decide +kernel

theorem arows14237 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14237 = true := by
  rw [show D2M8K2.u14237 = KTree.node D2M8K2.t14246 (nat_lit 31043762) (nat_lit 2530803679) (nat_lit 0) D2M8K2.t14247 from rfl, allE_node, rows14246, irow14237, rows14247]
  all_goals rfl

theorem atot14237 : totK PD2M8K2 D2M8K2.u14237 = [0, 150550172727, 773593707082, 710584644848, 92846287508, 1138244013, 0, 0] := by
  rw [show D2M8K2.u14237 = KTree.node D2M8K2.t14246 (nat_lit 31043762) (nat_lit 2530803679) (nat_lit 0) D2M8K2.t14247 from rfl, totK_node, tot14246, tot14247]
  decide +kernel

theorem arows14240 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14240 = true := by
  rw [show D2M8K2.u14240 = KTree.node D2M8K2.t14248 (nat_lit 31046222) (nat_lit 3818987115) (nat_lit 0) D2M8K2.t14249 from rfl, allE_node, rows14248, irow14240, rows14249]
  all_goals rfl

theorem atot14240 : totK PD2M8K2 D2M8K2.u14240 = [0, 343371968130, 935701010813, 508714787833, 40455910771, 0, 0, 0] := by
  rw [show D2M8K2.u14240 = KTree.node D2M8K2.t14248 (nat_lit 31046222) (nat_lit 3818987115) (nat_lit 0) D2M8K2.t14249 from rfl, totK_node, tot14248, tot14249]
  decide +kernel

theorem arows14241 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14241 = true := by
  rw [show D2M8K2.u14241 = KTree.node D2M8K2.t14250 (nat_lit 31049287) (nat_lit 1913369015) (nat_lit 0) D2M8K2.t14251 from rfl, allE_node, rows14250, irow14241, rows14251]
  all_goals rfl

theorem atot14241 : totK PD2M8K2 D2M8K2.u14241 = [0, 371609756519, 940792257342, 455270388798, 27871024226, 0, 0, 0] := by
  rw [show D2M8K2.u14241 = KTree.node D2M8K2.t14250 (nat_lit 31049287) (nat_lit 1913369015) (nat_lit 0) D2M8K2.t14251 from rfl, totK_node, tot14250, tot14251]
  decide +kernel

theorem arows14243 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14243 = true := by
  rw [show D2M8K2.u14243 = KTree.node D2M8K2.t14252 (nat_lit 31056029) (nat_lit 1964171117) (nat_lit 0) D2M8K2.t14253 from rfl, allE_node, rows14252, irow14243, rows14253]
  all_goals rfl

theorem atot14243 : totK PD2M8K2 D2M8K2.u14243 = [0, 377817008069, 936594845772, 439557039355, 27875897557, 0, 0, 0] := by
  rw [show D2M8K2.u14243 = KTree.node D2M8K2.t14252 (nat_lit 31056029) (nat_lit 1964171117) (nat_lit 0) D2M8K2.t14253 from rfl, totK_node, tot14252, tot14253]
  decide +kernel

theorem arows14244 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14244 = true := by
  rw [show D2M8K2.u14244 = KTree.node D2M8K2.t14254 (nat_lit 31057584) (nat_lit 3443103083) (nat_lit 0) D2M8K2.t14255 from rfl, allE_node, rows14254, irow14244, rows14255]
  all_goals rfl

theorem atot14244 : totK PD2M8K2 D2M8K2.u14244 = [0, 92025651062, 699265395637, 815554910601, 130311544600, 1095107716, 0, 0] := by
  rw [show D2M8K2.u14244 = KTree.node D2M8K2.t14254 (nat_lit 31057584) (nat_lit 3443103083) (nat_lit 0) D2M8K2.t14255 from rfl, totK_node, tot14254, tot14255]
  decide +kernel

theorem arows14248 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14248 = true := by
  rw [show D2M8K2.u14248 = KTree.node D2M8K2.t14256 (nat_lit 31063300) (nat_lit 4043245342) (nat_lit 0) D2M8K2.t14257 from rfl, allE_node, rows14256, irow14248, rows14257]
  all_goals rfl

theorem atot14248 : totK PD2M8K2 D2M8K2.u14248 = [345111433656, 846890947802, 387978097790, 112506804161, 70330583114, 3882006667, 0, 0] := by
  rw [show D2M8K2.u14248 = KTree.node D2M8K2.t14256 (nat_lit 31063300) (nat_lit 4043245342) (nat_lit 0) D2M8K2.t14257 from rfl, totK_node, tot14256, tot14257]
  decide +kernel

theorem arows14249 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14249 = true := by
  rw [show D2M8K2.u14249 = KTree.node D2M8K2.t14258 (nat_lit 31064889) (nat_lit 1804339598) (nat_lit 0) D2M8K2.t14259 from rfl, allE_node, rows14258, irow14249, rows14259]
  all_goals rfl

theorem atot14249 : totK PD2M8K2 D2M8K2.u14249 = [116132901016, 676274182734, 866997126938, 153330072762, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u14249 = KTree.node D2M8K2.t14258 (nat_lit 31064889) (nat_lit 1804339598) (nat_lit 0) D2M8K2.t14259 from rfl, totK_node, tot14258, tot14259]
  decide +kernel

theorem arows14251 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14251 = true := by
  rw [show D2M8K2.u14251 = KTree.node D2M8K2.t14260 (nat_lit 31066928) (nat_lit 3498887015) (nat_lit 0) D2M8K2.t14261 from rfl, allE_node, rows14260, irow14251, rows14261]
  all_goals rfl

theorem atot14251 : totK PD2M8K2 D2M8K2.u14251 = [362948396135, 936984527270, 500562922526, 41117382377, 0, 0, 0, 0] := by
  rw [show D2M8K2.u14251 = KTree.node D2M8K2.t14260 (nat_lit 31066928) (nat_lit 3498887015) (nat_lit 0) D2M8K2.t14261 from rfl, totK_node, tot14260, tot14261]
  decide +kernel

theorem arows14252 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14252 = true := by
  rw [show D2M8K2.u14252 = KTree.node D2M8K2.t14262 (nat_lit 31068421) (nat_lit 1245227011) (nat_lit 0) D2M8K2.t14263 from rfl, allE_node, rows14262, irow14252, rows14263]
  all_goals rfl

theorem atot14252 : totK PD2M8K2 D2M8K2.u14252 = [0, 409044959253, 931226969565, 437668338084, 30599093470, 0, 0, 0] := by
  rw [show D2M8K2.u14252 = KTree.node D2M8K2.t14262 (nat_lit 31068421) (nat_lit 1245227011) (nat_lit 0) D2M8K2.t14263 from rfl, totK_node, tot14262, tot14263]
  decide +kernel

theorem arows14255 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14255 = true := by
  rw [show D2M8K2.u14255 = KTree.node D2M8K2.t14264 (nat_lit 31069797) (nat_lit 1474980292) (nat_lit 0) D2M8K2.t14265 from rfl, allE_node, rows14264, irow14255, rows14265]
  all_goals rfl

theorem atot14255 : totK PD2M8K2 D2M8K2.u14255 = [297051814937, 788569279276, 588188488353, 146438102151, 6804944647, 0, 0, 0] := by
  rw [show D2M8K2.u14255 = KTree.node D2M8K2.t14264 (nat_lit 31069797) (nat_lit 1474980292) (nat_lit 0) D2M8K2.t14265 from rfl, totK_node, tot14264, tot14265]
  decide +kernel

theorem arows14256 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14256 = true := by
  rw [show D2M8K2.u14256 = KTree.node D2M8K2.t14266 (nat_lit 31071276) (nat_lit 3153161402) (nat_lit 0) D2M8K2.t14267 from rfl, allE_node, rows14266, irow14256, rows14267]
  all_goals rfl

theorem atot14256 : totK PD2M8K2 D2M8K2.u14256 = [129240351417, 648044050737, 801362945954, 210280723606, 9583672031, 0, 0, 0] := by
  rw [show D2M8K2.u14256 = KTree.node D2M8K2.t14266 (nat_lit 31071276) (nat_lit 3153161402) (nat_lit 0) D2M8K2.t14267 from rfl, totK_node, tot14266, tot14267]
  decide +kernel

theorem arows14258 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14258 = true := by
  rw [show D2M8K2.u14258 = KTree.node D2M8K2.t14268 (nat_lit 31073140) (nat_lit 2565369694) (nat_lit 0) D2M8K2.t14269 from rfl, allE_node, rows14268, irow14258, rows14269]
  all_goals rfl

theorem atot14258 : totK PD2M8K2 D2M8K2.u14258 = [255880646370, 791111778047, 647952401729, 122336582098, 3460111309, 0, 0, 0] := by
  rw [show D2M8K2.u14258 = KTree.node D2M8K2.t14268 (nat_lit 31073140) (nat_lit 2565369694) (nat_lit 0) D2M8K2.t14269 from rfl, totK_node, tot14268, tot14269]
  decide +kernel

theorem arows14259 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14259 = true := by
  rw [show D2M8K2.u14259 = KTree.node D2M8K2.t14270 (nat_lit 31074954) (nat_lit 3885565253) (nat_lit 0) D2M8K2.t14271 from rfl, allE_node, rows14270, irow14259, rows14271]
  all_goals rfl

theorem atot14259 : totK PD2M8K2 D2M8K2.u14259 = [108226444032, 608137433596, 859723698409, 236663268685, 9549167768, 0, 0, 0] := by
  rw [show D2M8K2.u14259 = KTree.node D2M8K2.t14270 (nat_lit 31074954) (nat_lit 3885565253) (nat_lit 0) D2M8K2.t14271 from rfl, totK_node, tot14270, tot14271]
  decide +kernel

theorem arows14265 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14265 = true := by
  rw [show D2M8K2.u14265 = KTree.node D2M8K2.t14272 (nat_lit 31080415) (nat_lit 1726871930) (nat_lit 0) D2M8K2.t14273 from rfl, allE_node, rows14272, irow14265, rows14273]
  all_goals rfl

theorem atot14265 : totK PD2M8K2 D2M8K2.u14265 = [375333611480, 945627365186, 486981181178, 38235829066, 0, 0, 0, 0] := by
  rw [show D2M8K2.u14265 = KTree.node D2M8K2.t14272 (nat_lit 31080415) (nat_lit 1726871930) (nat_lit 0) D2M8K2.t14273 from rfl, totK_node, tot14272, tot14273]
  decide +kernel

theorem arows14266 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14266 = true := by
  rw [show D2M8K2.u14266 = KTree.node D2M8K2.t14274 (nat_lit 31081918) (nat_lit 3857547598) (nat_lit 0) D2M8K2.t14275 from rfl, allE_node, rows14274, irow14266, rows14275]
  all_goals rfl

theorem atot14266 : totK PD2M8K2 D2M8K2.u14266 = [45093903507, 535326115273, 922156374489, 283827038422, 8710740030, 0, 0, 0] := by
  rw [show D2M8K2.u14266 = KTree.node D2M8K2.t14274 (nat_lit 31081918) (nat_lit 3857547598) (nat_lit 0) D2M8K2.t14275 from rfl, totK_node, tot14274, tot14275]
  decide +kernel

theorem arows14268 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14268 = true := by
  rw [show D2M8K2.u14268 = KTree.node D2M8K2.t14276 (nat_lit 31083860) (nat_lit 3145967956) (nat_lit 0) D2M8K2.t14277 from rfl, allE_node, rows14276, irow14268, rows14277]
  all_goals rfl

theorem atot14268 : totK PD2M8K2 D2M8K2.u14268 = [0, 389746877816, 950126817541, 424122842213, 22692591333, 0, 0, 0] := by
  rw [show D2M8K2.u14268 = KTree.node D2M8K2.t14276 (nat_lit 31083860) (nat_lit 3145967956) (nat_lit 0) D2M8K2.t14277 from rfl, totK_node, tot14276, tot14277]
  decide +kernel

theorem arows14269 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14269 = true := by
  rw [show D2M8K2.u14269 = KTree.node D2M8K2.t14278 (nat_lit 31085156) (nat_lit 2165040938) (nat_lit 0) D2M8K2.t14279 from rfl, allE_node, rows14278, irow14269, rows14279]
  all_goals rfl

theorem atot14269 : totK PD2M8K2 D2M8K2.u14269 = [0, 99077668199, 698410741364, 840508207433, 115966172227, 1310285577, 0, 0] := by
  rw [show D2M8K2.u14269 = KTree.node D2M8K2.t14278 (nat_lit 31085156) (nat_lit 2165040938) (nat_lit 0) D2M8K2.t14279 from rfl, totK_node, tot14278, tot14279]
  decide +kernel

theorem arows14272 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14272 = true := by
  rw [show D2M8K2.u14272 = KTree.node D2M8K2.t14280 (nat_lit 31087510) (nat_lit 2981990818) (nat_lit 0) D2M8K2.t14281 from rfl, allE_node, rows14280, irow14272, rows14281]
  all_goals rfl

theorem atot14272 : totK PD2M8K2 D2M8K2.u14272 = [0, 380954523025, 921323605061, 500233357230, 43664257211, 0, 0, 0] := by
  rw [show D2M8K2.u14272 = KTree.node D2M8K2.t14280 (nat_lit 31087510) (nat_lit 2981990818) (nat_lit 0) D2M8K2.t14281 from rfl, totK_node, tot14280, tot14281]
  decide +kernel

theorem arows14273 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14273 = true := by
  rw [show D2M8K2.u14273 = KTree.node D2M8K2.t14282 (nat_lit 31090569) (nat_lit 1866792087) (nat_lit 0) D2M8K2.t14283 from rfl, allE_node, rows14282, irow14273, rows14283]
  all_goals rfl

theorem atot14273 : totK PD2M8K2 D2M8K2.u14273 = [0, 354963049680, 920457335226, 497133851829, 42741208655, 0, 0, 0] := by
  rw [show D2M8K2.u14273 = KTree.node D2M8K2.t14282 (nat_lit 31090569) (nat_lit 1866792087) (nat_lit 0) D2M8K2.t14283 from rfl, totK_node, tot14282, tot14283]
  decide +kernel

theorem arows14275 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14275 = true := by
  rw [show D2M8K2.u14275 = KTree.node D2M8K2.t14284 (nat_lit 31092057) (nat_lit 1196942497) (nat_lit 0) D2M8K2.t14285 from rfl, allE_node, rows14284, irow14275, rows14285]
  all_goals rfl

theorem atot14275 : totK PD2M8K2 D2M8K2.u14275 = [0, 106776214259, 667083377779, 805544339695, 165020737451, 4879840392, 0, 0] := by
  rw [show D2M8K2.u14275 = KTree.node D2M8K2.t14284 (nat_lit 31092057) (nat_lit 1196942497) (nat_lit 0) D2M8K2.t14285 from rfl, totK_node, tot14284, tot14285]
  decide +kernel

theorem arows14276 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14276 = true := by
  rw [show D2M8K2.u14276 = KTree.node D2M8K2.t14286 (nat_lit 31094134) (nat_lit 3508230712) (nat_lit 0) D2M8K2.t14287 from rfl, allE_node, rows14286, irow14276, rows14287]
  all_goals rfl

theorem atot14276 : totK PD2M8K2 D2M8K2.u14276 = [0, 344447034184, 908005017428, 537285340940, 49152675496, 0, 0, 0] := by
  rw [show D2M8K2.u14276 = KTree.node D2M8K2.t14286 (nat_lit 31094134) (nat_lit 3508230712) (nat_lit 0) D2M8K2.t14287 from rfl, totK_node, tot14286, tot14287]
  decide +kernel

theorem arows14280 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14280 = true := by
  rw [show D2M8K2.u14280 = KTree.node D2M8K2.t14288 (nat_lit 31096372) (nat_lit 2056951797) (nat_lit 0) D2M8K2.t14289 from rfl, allE_node, rows14288, irow14280, rows14289]
  all_goals rfl

theorem atot14280 : totK PD2M8K2 D2M8K2.u14280 = [0, 134872346053, 659961520320, 801944061707, 177714717710, 4931404646, 0, 0] := by
  rw [show D2M8K2.u14280 = KTree.node D2M8K2.t14288 (nat_lit 31096372) (nat_lit 2056951797) (nat_lit 0) D2M8K2.t14289 from rfl, totK_node, tot14288, tot14289]
  decide +kernel

theorem arows14281 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14281 = true := by
  rw [show D2M8K2.u14281 = KTree.node D2M8K2.t14290 (nat_lit 31101483) (nat_lit 3648144827) (nat_lit 0) D2M8K2.t14291 from rfl, allE_node, rows14290, irow14281, rows14291]
  all_goals rfl

theorem atot14281 : totK PD2M8K2 D2M8K2.u14281 = [0, 306581653456, 897824841409, 577168094965, 49080630453, 0, 0, 0] := by
  rw [show D2M8K2.u14281 = KTree.node D2M8K2.t14290 (nat_lit 31101483) (nat_lit 3648144827) (nat_lit 0) D2M8K2.t14291 from rfl, totK_node, tot14290, tot14291]
  decide +kernel

theorem arows14283 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14283 = true := by
  rw [show D2M8K2.u14283 = KTree.node D2M8K2.t14292 (nat_lit 31103156) (nat_lit 2296921122) (nat_lit 0) D2M8K2.t14293 from rfl, allE_node, rows14292, irow14283, rows14293]
  all_goals rfl

theorem atot14283 : totK PD2M8K2 D2M8K2.u14283 = [0, 37283609705, 428817980918, 897244483345, 364553908678, 21751168066, 0, 0] := by
  rw [show D2M8K2.u14283 = KTree.node D2M8K2.t14292 (nat_lit 31103156) (nat_lit 2296921122) (nat_lit 0) D2M8K2.t14293 from rfl, totK_node, tot14292, tot14293]
  decide +kernel

theorem arows14284 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14284 = true := by
  rw [show D2M8K2.u14284 = KTree.node D2M8K2.t14294 (nat_lit 31104967) (nat_lit 2384927911) (nat_lit 0) D2M8K2.t14295 from rfl, allE_node, rows14294, irow14284, rows14295]
  all_goals rfl

theorem atot14284 : totK PD2M8K2 D2M8K2.u14284 = [0, 395602260578, 947112833021, 418004708100, 22265679629, 0, 0, 0] := by
  rw [show D2M8K2.u14284 = KTree.node D2M8K2.t14294 (nat_lit 31104967) (nat_lit 2384927911) (nat_lit 0) D2M8K2.t14295 from rfl, totK_node, tot14294, tot14295]
  decide +kernel

theorem arows14287 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14287 = true := by
  rw [show D2M8K2.u14287 = KTree.node D2M8K2.t14296 (nat_lit 31106612) (nat_lit 3181167369) (nat_lit 0) D2M8K2.t14297 from rfl, allE_node, rows14296, irow14287, rows14297]
  all_goals rfl

theorem atot14287 : totK PD2M8K2 D2M8K2.u14287 = [0, 87704378323, 678572121099, 883560668668, 151660234612, 1369150432, 0, 0] := by
  rw [show D2M8K2.u14287 = KTree.node D2M8K2.t14296 (nat_lit 31106612) (nat_lit 3181167369) (nat_lit 0) D2M8K2.t14297 from rfl, totK_node, tot14296, tot14297]
  decide +kernel

theorem arows14288 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14288 = true := by
  rw [show D2M8K2.u14288 = KTree.node D2M8K2.t14298 (nat_lit 31111702) (nat_lit 2987652673) (nat_lit 0) D2M8K2.t14299 from rfl, allE_node, rows14298, irow14288, rows14299]
  all_goals rfl

theorem atot14288 : totK PD2M8K2 D2M8K2.u14288 = [0, 334586649214, 917145084462, 508854223440, 33674683859, 0, 0, 0] := by
  rw [show D2M8K2.u14288 = KTree.node D2M8K2.t14298 (nat_lit 31111702) (nat_lit 2987652673) (nat_lit 0) D2M8K2.t14299 from rfl, totK_node, tot14298, tot14299]
  decide +kernel

theorem arows14290 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14290 = true := by
  rw [show D2M8K2.u14290 = KTree.node D2M8K2.t14300 (nat_lit 31113386) (nat_lit 4025831296) (nat_lit 0) D2M8K2.t14301 from rfl, allE_node, rows14300, irow14290, rows14301]
  all_goals rfl

theorem atot14290 : totK PD2M8K2 D2M8K2.u14290 = [0, 51750414094, 496937435015, 920464958381, 287859162117, 13049727234, 0, 0] := by
  rw [show D2M8K2.u14290 = KTree.node D2M8K2.t14300 (nat_lit 31113386) (nat_lit 4025831296) (nat_lit 0) D2M8K2.t14301 from rfl, totK_node, tot14300, tot14301]
  decide +kernel

theorem arows14291 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14291 = true := by
  rw [show D2M8K2.u14291 = KTree.node D2M8K2.t14302 (nat_lit 31115671) (nat_lit 2230937039) (nat_lit 0) D2M8K2.t14303 from rfl, allE_node, rows14302, irow14291, rows14303]
  all_goals rfl

theorem atot14291 : totK PD2M8K2 D2M8K2.u14291 = [0, 273170857218, 841470322151, 581026665511, 78390802593, 1198073392, 0, 0] := by
  rw [show D2M8K2.u14291 = KTree.node D2M8K2.t14302 (nat_lit 31115671) (nat_lit 2230937039) (nat_lit 0) D2M8K2.t14303 from rfl, totK_node, tot14302, tot14303]
  decide +kernel

theorem arows14296 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14296 = true := by
  rw [show D2M8K2.u14296 = KTree.node D2M8K2.t14304 (nat_lit 31117972) (nat_lit 3652061428) (nat_lit 0) D2M8K2.t14305 from rfl, allE_node, rows14304, irow14296, rows14305]
  all_goals rfl

theorem atot14296 : totK PD2M8K2 D2M8K2.u14296 = [0, 242698498305, 820224361415, 666820651400, 71285541726, 0, 0, 0] := by
  rw [show D2M8K2.u14296 = KTree.node D2M8K2.t14304 (nat_lit 31117972) (nat_lit 3652061428) (nat_lit 0) D2M8K2.t14305 from rfl, totK_node, tot14304, tot14305]
  decide +kernel

theorem arows14297 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14297 = true := by
  rw [show D2M8K2.u14297 = KTree.node D2M8K2.t14306 (nat_lit 31119655) (nat_lit 2330472911) (nat_lit 0) D2M8K2.t14307 from rfl, allE_node, rows14306, irow14297, rows14307]
  all_goals rfl

theorem atot14297 : totK PD2M8K2 D2M8K2.u14297 = [0, 135002877226, 715408035381, 787573533816, 118173074079, 1096505104, 0, 0] := by
  rw [show D2M8K2.u14297 = KTree.node D2M8K2.t14306 (nat_lit 31119655) (nat_lit 2330472911) (nat_lit 0) D2M8K2.t14307 from rfl, totK_node, tot14306, tot14307]
  decide +kernel

theorem arows14299 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14299 = true := by
  rw [show D2M8K2.u14299 = KTree.node D2M8K2.t14308 (nat_lit 31121764) (nat_lit 3984340264) (nat_lit 0) D2M8K2.t14309 from rfl, allE_node, rows14308, irow14299, rows14309]
  all_goals rfl

theorem atot14299 : totK PD2M8K2 D2M8K2.u14299 = [0, 323614708437, 830308256751, 544120530065, 101168779436, 3820764243, 0, 0] := by
  rw [show D2M8K2.u14299 = KTree.node D2M8K2.t14308 (nat_lit 31121764) (nat_lit 3984340264) (nat_lit 0) D2M8K2.t14309 from rfl, totK_node, tot14308, tot14309]
  decide +kernel

theorem arows14300 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14300 = true := by
  rw [show D2M8K2.u14300 = KTree.node D2M8K2.t14310 (nat_lit 31123324) (nat_lit 3858311637) (nat_lit 0) D2M8K2.t14311 from rfl, allE_node, rows14310, irow14300, rows14311]
  all_goals rfl

theorem atot14300 : totK PD2M8K2 D2M8K2.u14300 = [0, 92168731024, 614276690071, 874123218209, 210869229457, 4967996017, 0, 0] := by
  rw [show D2M8K2.u14300 = KTree.node D2M8K2.t14310 (nat_lit 31123324) (nat_lit 3858311637) (nat_lit 0) D2M8K2.t14311 from rfl, totK_node, tot14310, tot14311]
  decide +kernel

theorem arows14303 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14303 = true := by
  rw [show D2M8K2.u14303 = KTree.node D2M8K2.t14312 (nat_lit 31125413) (nat_lit 2336676377) (nat_lit 0) D2M8K2.t14313 from rfl, allE_node, rows14312, irow14303, rows14313]
  all_goals rfl

theorem atot14303 : totK PD2M8K2 D2M8K2.u14303 = [0, 0, 395953998866, 959362544193, 378958690077, 19549668190, 0, 0] := by
  rw [show D2M8K2.u14303 = KTree.node D2M8K2.t14312 (nat_lit 31125413) (nat_lit 2336676377) (nat_lit 0) D2M8K2.t14313 from rfl, totK_node, tot14312, tot14313]
  decide +kernel

theorem arows14304 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14304 = true := by
  rw [show D2M8K2.u14304 = KTree.node D2M8K2.t14314 (nat_lit 31126709) (nat_lit 1989697996) (nat_lit 0) D2M8K2.t14315 from rfl, allE_node, rows14314, irow14304, rows14315]
  all_goals rfl

theorem atot14304 : totK PD2M8K2 D2M8K2.u14304 = [0, 0, 126881713060, 743730550694, 716175260479, 105375228099, 1275377855, 0] := by
  rw [show D2M8K2.u14304 = KTree.node D2M8K2.t14314 (nat_lit 31126709) (nat_lit 1989697996) (nat_lit 0) D2M8K2.t14315 from rfl, totK_node, tot14314, tot14315]
  decide +kernel

theorem arows14306 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14306 = true := by
  rw [show D2M8K2.u14306 = KTree.node D2M8K2.t14316 (nat_lit 31132375) (nat_lit 1158260103) (nat_lit 0) D2M8K2.t14317 from rfl, allE_node, rows14316, irow14306, rows14317]
  all_goals rfl

theorem atot14306 : totK PD2M8K2 D2M8K2.u14306 = [0, 0, 377913142756, 946987138879, 408416965419, 18820143933, 0, 0] := by
  rw [show D2M8K2.u14306 = KTree.node D2M8K2.t14316 (nat_lit 31132375) (nat_lit 1158260103) (nat_lit 0) D2M8K2.t14317 from rfl, totK_node, tot14316, tot14317]
  decide +kernel

theorem arows14307 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14307 = true := by
  rw [show D2M8K2.u14307 = KTree.node D2M8K2.t14318 (nat_lit 31136359) (nat_lit 2378093395) (nat_lit 0) D2M8K2.t14319 from rfl, allE_node, rows14318, irow14307, rows14319]
  all_goals rfl

theorem atot14307 : totK PD2M8K2 D2M8K2.u14307 = [0, 0, 460947570357, 977882069350, 311730907424, 11354856277, 0, 0] := by
  rw [show D2M8K2.u14307 = KTree.node D2M8K2.t14318 (nat_lit 31136359) (nat_lit 2378093395) (nat_lit 0) D2M8K2.t14319 from rfl, totK_node, tot14318, tot14319]
  decide +kernel

theorem arows14311 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14311 = true := by
  rw [show D2M8K2.u14311 = KTree.node D2M8K2.t14320 (nat_lit 31139761) (nat_lit 1475828616) (nat_lit 0) D2M8K2.t14321 from rfl, allE_node, rows14320, irow14311, rows14321]
  all_goals rfl

theorem atot14311 : totK PD2M8K2 D2M8K2.u14311 = [0, 0, 392315896344, 962750432105, 376294436096, 15951152297, 0, 0] := by
  rw [show D2M8K2.u14311 = KTree.node D2M8K2.t14320 (nat_lit 31139761) (nat_lit 1475828616) (nat_lit 0) D2M8K2.t14321 from rfl, totK_node, tot14320, tot14321]
  decide +kernel

theorem arows14312 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14312 = true := by
  rw [show D2M8K2.u14312 = KTree.node D2M8K2.t14322 (nat_lit 31143609) (nat_lit 1090509342) (nat_lit 0) D2M8K2.t14323 from rfl, allE_node, rows14322, irow14312, rows14323]
  all_goals rfl

theorem atot14312 : totK PD2M8K2 D2M8K2.u14312 = [0, 183175457280, 630256768367, 756284466542, 252060760462, 12764577078, 0, 0] := by
  rw [show D2M8K2.u14312 = KTree.node D2M8K2.t14322 (nat_lit 31143609) (nat_lit 1090509342) (nat_lit 0) D2M8K2.t14323 from rfl, totK_node, tot14322, tot14323]
  decide +kernel

theorem arows14314 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14314 = true := by
  rw [show D2M8K2.u14314 = KTree.node D2M8K2.t14324 (nat_lit 31150254) (nat_lit 3846508441) (nat_lit 0) D2M8K2.t14325 from rfl, allE_node, rows14324, irow14314, rows14325]
  all_goals rfl

theorem atot14314 : totK PD2M8K2 D2M8K2.u14314 = [0, 259144647737, 853357745994, 613505310377, 89948029748, 10444649207, 0, 0] := by
  rw [show D2M8K2.u14314 = KTree.node D2M8K2.t14324 (nat_lit 31150254) (nat_lit 3846508441) (nat_lit 0) D2M8K2.t14325 from rfl, totK_node, tot14324, tot14325]
  decide +kernel

theorem arows14315 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14315 = true := by
  rw [show D2M8K2.u14315 = KTree.node D2M8K2.t14326 (nat_lit 31151754) (nat_lit 3645055476) (nat_lit 0) D2M8K2.t14327 from rfl, allE_node, rows14326, irow14315, rows14327]
  all_goals rfl

theorem atot14315 : totK PD2M8K2 D2M8K2.u14315 = [0, 0, 346354038508, 934224794076, 484863318001, 24880355955, 0, 0] := by
  rw [show D2M8K2.u14315 = KTree.node D2M8K2.t14326 (nat_lit 31151754) (nat_lit 3645055476) (nat_lit 0) D2M8K2.t14327 from rfl, totK_node, tot14326, tot14327]
  decide +kernel

theorem arows14318 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14318 = true := by
  rw [show D2M8K2.u14318 = KTree.node D2M8K2.t14328 (nat_lit 31153004) (nat_lit 3703213270) (nat_lit 0) D2M8K2.t14329 from rfl, allE_node, rows14328, irow14318, rows14329]
  all_goals rfl

theorem atot14318 : totK PD2M8K2 D2M8K2.u14318 = [0, 390610660546, 926233713981, 462535075308, 35666809945, 2174602308, 0, 0] := by
  rw [show D2M8K2.u14318 = KTree.node D2M8K2.t14328 (nat_lit 31153004) (nat_lit 3703213270) (nat_lit 0) D2M8K2.t14329 from rfl, totK_node, tot14328, tot14329]
  decide +kernel

theorem arows14319 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14319 = true := by
  rw [show D2M8K2.u14319 = KTree.node D2M8K2.t14330 (nat_lit 31154752) (nat_lit 3775464034) (nat_lit 0) D2M8K2.t14331 from rfl, allE_node, rows14330, irow14319, rows14331]
  all_goals rfl

theorem atot14319 : totK PD2M8K2 D2M8K2.u14319 = [0, 33688335845, 579287151424, 924438347332, 244853829435, 11873025674, 0, 0] := by
  rw [show D2M8K2.u14319 = KTree.node D2M8K2.t14330 (nat_lit 31154752) (nat_lit 3775464034) (nat_lit 0) D2M8K2.t14331 from rfl, totK_node, tot14330, tot14331]
  decide +kernel

theorem arows14321 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14321 = true := by
  rw [show D2M8K2.u14321 = KTree.node D2M8K2.t14332 (nat_lit 31156957) (nat_lit 884297894) (nat_lit 0) D2M8K2.t14333 from rfl, allE_node, rows14332, irow14321, rows14333]
  all_goals rfl

theorem atot14321 : totK PD2M8K2 D2M8K2.u14321 = [0, 331443236761, 892611518735, 566258340256, 65778547186, 0, 0, 0] := by
  rw [show D2M8K2.u14321 = KTree.node D2M8K2.t14332 (nat_lit 31156957) (nat_lit 884297894) (nat_lit 0) D2M8K2.t14333 from rfl, totK_node, tot14332, tot14333]
  decide +kernel

theorem arows14322 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14322 = true := by
  rw [show D2M8K2.u14322 = KTree.node D2M8K2.t14334 (nat_lit 31159039) (nat_lit 2314785645) (nat_lit 0) D2M8K2.t14335 from rfl, allE_node, rows14334, irow14322, rows14335]
  all_goals rfl

theorem atot14322 : totK PD2M8K2 D2M8K2.u14322 = [0, 140943570440, 653844986650, 814959995248, 201666049417, 5439011083, 0, 0] := by
  rw [show D2M8K2.u14322 = KTree.node D2M8K2.t14334 (nat_lit 31159039) (nat_lit 2314785645) (nat_lit 0) D2M8K2.t14335 from rfl, totK_node, tot14334, tot14335]
  decide +kernel

theorem arows14333 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14333 = true := by
  rw [show D2M8K2.u14333 = KTree.node D2M8K2.t14336 (nat_lit 31160507) (nat_lit 2056141803) (nat_lit 0) D2M8K2.t14337 from rfl, allE_node, rows14336, irow14333, rows14337]
  all_goals rfl

theorem atot14333 : totK PD2M8K2 D2M8K2.u14333 = [0, 241086864470, 844529360642, 657512690869, 70595535563, 0, 0, 0] := by
  rw [show D2M8K2.u14333 = KTree.node D2M8K2.t14336 (nat_lit 31160507) (nat_lit 2056141803) (nat_lit 0) D2M8K2.t14337 from rfl, totK_node, tot14336, tot14337]
  decide +kernel

theorem arows14334 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14334 = true := by
  rw [show D2M8K2.u14334 = KTree.node D2M8K2.t14338 (nat_lit 31163023) (nat_lit 1825116314) (nat_lit 0) D2M8K2.t14339 from rfl, allE_node, rows14338, irow14334, rows14339]
  all_goals rfl

theorem atot14334 : totK PD2M8K2 D2M8K2.u14334 = [0, 245916881267, 771540408295, 667488242981, 134826628180, 3880716147, 0, 0] := by
  rw [show D2M8K2.u14334 = KTree.node D2M8K2.t14338 (nat_lit 31163023) (nat_lit 1825116314) (nat_lit 0) D2M8K2.t14339 from rfl, totK_node, tot14338, tot14339]
  decide +kernel

theorem arows14336 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14336 = true := by
  rw [show D2M8K2.u14336 = KTree.node D2M8K2.t14340 (nat_lit 31164484) (nat_lit 3724415699) (nat_lit 0) D2M8K2.t14341 from rfl, allE_node, rows14340, irow14336, rows14341]
  all_goals rfl

theorem atot14336 : totK PD2M8K2 D2M8K2.u14336 = [0, 172800148695, 705338402291, 759627879156, 174168256560, 4925188030, 0, 0] := by
  rw [show D2M8K2.u14336 = KTree.node D2M8K2.t14340 (nat_lit 31164484) (nat_lit 3724415699) (nat_lit 0) D2M8K2.t14341 from rfl, totK_node, tot14340, tot14341]
  decide +kernel

theorem arows14337 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14337 = true := by
  rw [show D2M8K2.u14337 = KTree.node D2M8K2.t14342 (nat_lit 31186956) (nat_lit 3608248717) (nat_lit 0) D2M8K2.t14343 from rfl, allE_node, rows14342, irow14337, rows14343]
  all_goals rfl

theorem atot14337 : totK PD2M8K2 D2M8K2.u14337 = [0, 216438544058, 676689650026, 664018944281, 222911975541, 12866082196, 0, 0] := by
  rw [show D2M8K2.u14337 = KTree.node D2M8K2.t14342 (nat_lit 31186956) (nat_lit 3608248717) (nat_lit 0) D2M8K2.t14343 from rfl, totK_node, tot14342, tot14343]
  decide +kernel

theorem arows14340 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14340 = true := by
  rw [show D2M8K2.u14340 = KTree.node D2M8K2.t14344 (nat_lit 31188536) (nat_lit 2682498469) (nat_lit 0) D2M8K2.t14345 from rfl, allE_node, rows14344, irow14340, rows14345]
  all_goals rfl

theorem atot14340 : totK PD2M8K2 D2M8K2.u14340 = [0, 195524045221, 752482563498, 697551535219, 105573032143, 1334361349, 0, 0] := by
  rw [show D2M8K2.u14340 = KTree.node D2M8K2.t14344 (nat_lit 31188536) (nat_lit 2682498469) (nat_lit 0) D2M8K2.t14345 from rfl, totK_node, tot14344, tot14345]
  decide +kernel

theorem arows14341 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14341 = true := by
  rw [show D2M8K2.u14341 = KTree.node D2M8K2.t14346 (nat_lit 31190897) (nat_lit 1737104167) (nat_lit 0) D2M8K2.t14347 from rfl, allE_node, rows14346, irow14341, rows14347]
  all_goals rfl

theorem atot14341 : totK PD2M8K2 D2M8K2.u14341 = [0, 250919374309, 828237211444, 673673665757, 68431172621, 0, 0, 0] := by
  rw [show D2M8K2.u14341 = KTree.node D2M8K2.t14346 (nat_lit 31190897) (nat_lit 1737104167) (nat_lit 0) D2M8K2.t14347 from rfl, totK_node, tot14346, tot14347]
  decide +kernel

theorem arows14343 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14343 = true := by
  rw [show D2M8K2.u14343 = KTree.node D2M8K2.t14348 (nat_lit 31192446) (nat_lit 3900362334) (nat_lit 0) D2M8K2.t14349 from rfl, allE_node, rows14348, irow14343, rows14349]
  all_goals rfl

theorem atot14343 : totK PD2M8K2 D2M8K2.u14343 = [0, 172333883661, 654271532430, 712452119898, 256674347287, 18567029682, 0, 0] := by
  rw [show D2M8K2.u14343 = KTree.node D2M8K2.t14348 (nat_lit 31192446) (nat_lit 3900362334) (nat_lit 0) D2M8K2.t14349 from rfl, totK_node, tot14348, tot14349]
  decide +kernel

theorem arows14344 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14344 = true := by
  rw [show D2M8K2.u14344 = KTree.node D2M8K2.t14350 (nat_lit 31193792) (nat_lit 1636936995) (nat_lit 0) D2M8K2.t14351 from rfl, allE_node, rows14350, irow14344, rows14351]
  all_goals rfl

theorem atot14344 : totK PD2M8K2 D2M8K2.u14344 = [0, 176264834056, 668072200333, 752947789417, 210618189088, 5521894595, 0, 0] := by
  rw [show D2M8K2.u14344 = KTree.node D2M8K2.t14350 (nat_lit 31193792) (nat_lit 1636936995) (nat_lit 0) D2M8K2.t14351 from rfl, totK_node, tot14350, tot14351]
  decide +kernel

theorem arows14348 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14348 = true := by
  rw [show D2M8K2.u14348 = KTree.node D2M8K2.t14352 (nat_lit 31195301) (nat_lit 2314578259) (nat_lit 0) D2M8K2.t14353 from rfl, allE_node, rows14352, irow14348, rows14353]
  all_goals rfl

theorem atot14348 : totK PD2M8K2 D2M8K2.u14348 = [0, 269147497583, 815642036083, 626468751333, 101221967671, 1164319620, 0, 0] := by
  rw [show D2M8K2.u14348 = KTree.node D2M8K2.t14352 (nat_lit 31195301) (nat_lit 2314578259) (nat_lit 0) D2M8K2.t14353 from rfl, totK_node, tot14352, tot14353]
  decide +kernel

theorem arows14349 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14349 = true := by
  rw [show D2M8K2.u14349 = KTree.node D2M8K2.t14354 (nat_lit 31196929) (nat_lit 1358898502) (nat_lit 0) D2M8K2.t14355 from rfl, allE_node, rows14354, irow14349, rows14355]
  all_goals rfl

theorem atot14349 : totK PD2M8K2 D2M8K2.u14349 = [0, 153875073329, 620002478175, 772576937071, 219508868262, 11885407614, 0, 0] := by
  rw [show D2M8K2.u14349 = KTree.node D2M8K2.t14354 (nat_lit 31196929) (nat_lit 1358898502) (nat_lit 0) D2M8K2.t14355 from rfl, totK_node, tot14354, tot14355]
  decide +kernel

theorem arows14351 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14351 = true := by
  rw [show D2M8K2.u14351 = KTree.node D2M8K2.t14356 (nat_lit 31201786) (nat_lit 2441030646) (nat_lit 0) D2M8K2.t14357 from rfl, allE_node, rows14356, irow14351, rows14357]
  all_goals rfl

theorem atot14351 : totK PD2M8K2 D2M8K2.u14351 = [0, 244813245530, 810337721916, 629006457991, 86637080340, 1062926506, 0, 0] := by
  rw [show D2M8K2.u14351 = KTree.node D2M8K2.t14356 (nat_lit 31201786) (nat_lit 2441030646) (nat_lit 0) D2M8K2.t14357 from rfl, totK_node, tot14356, tot14357]
  decide +kernel

theorem arows14352 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14352 = true := by
  rw [show D2M8K2.u14352 = KTree.node D2M8K2.t14358 (nat_lit 31203840) (nat_lit 3221708637) (nat_lit 0) D2M8K2.t14359 from rfl, allE_node, rows14358, irow14352, rows14359]
  all_goals rfl

theorem atot14352 : totK PD2M8K2 D2M8K2.u14352 = [0, 173041957571, 717917996075, 760328787406, 143437942635, 3783381897, 0, 0] := by
  rw [show D2M8K2.u14352 = KTree.node D2M8K2.t14358 (nat_lit 31203840) (nat_lit 3221708637) (nat_lit 0) D2M8K2.t14359 from rfl, totK_node, tot14358, tot14359]
  decide +kernel

theorem arows14355 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14355 = true := by
  rw [show D2M8K2.u14355 = KTree.node D2M8K2.t14360 (nat_lit 31205697) (nat_lit 1241974140) (nat_lit 0) D2M8K2.t14361 from rfl, allE_node, rows14360, irow14355, rows14361]
  all_goals rfl

theorem atot14355 : totK PD2M8K2 D2M8K2.u14355 = [0, 250501968678, 790655762325, 663662620621, 107475170234, 1240621948, 0, 0] := by
  rw [show D2M8K2.u14355 = KTree.node D2M8K2.t14360 (nat_lit 31205697) (nat_lit 1241974140) (nat_lit 0) D2M8K2.t14361 from rfl, totK_node, tot14360, tot14361]
  decide +kernel

theorem arows14356 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14356 = true := by
  rw [show D2M8K2.u14356 = KTree.node D2M8K2.t14362 (nat_lit 31207472) (nat_lit 2160152931) (nat_lit 0) D2M8K2.t14363 from rfl, allE_node, rows14362, irow14356, rows14363]
  all_goals rfl

theorem atot14356 : totK PD2M8K2 D2M8K2.u14356 = [0, 0, 470191489311, 981105970548, 327894956277, 13858786386, 0, 0] := by
  rw [show D2M8K2.u14356 = KTree.node D2M8K2.t14362 (nat_lit 31207472) (nat_lit 2160152931) (nat_lit 0) D2M8K2.t14363 from rfl, totK_node, tot14362, tot14363]
  decide +kernel

theorem arows14358 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14358 = true := by
  rw [show D2M8K2.u14358 = KTree.node D2M8K2.t14364 (nat_lit 31209090) (nat_lit 1770907776) (nat_lit 0) D2M8K2.t14365 from rfl, allE_node, rows14364, irow14358, rows14365]
  all_goals rfl

theorem atot14358 : totK PD2M8K2 D2M8K2.u14358 = [0, 0, 228925666579, 800819701075, 575393999743, 83143369020, 1206465782, 0] := by
  rw [show D2M8K2.u14358 = KTree.node D2M8K2.t14364 (nat_lit 31209090) (nat_lit 1770907776) (nat_lit 0) D2M8K2.t14365 from rfl, totK_node, tot14364, tot14365]
  decide +kernel

theorem arows14359 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14359 = true := by
  rw [show D2M8K2.u14359 = KTree.node D2M8K2.t14366 (nat_lit 31211548) (nat_lit 3875912919) (nat_lit 0) D2M8K2.t14367 from rfl, allE_node, rows14366, irow14359, rows14367]
  all_goals rfl

theorem atot14359 : totK PD2M8K2 D2M8K2.u14359 = [0, 0, 276112891423, 842840324754, 589911456930, 55216407471, 0, 0] := by
  rw [show D2M8K2.u14359 = KTree.node D2M8K2.t14366 (nat_lit 31211548) (nat_lit 3875912919) (nat_lit 0) D2M8K2.t14367 from rfl, totK_node, tot14366, tot14367]
  decide +kernel

theorem arows14364 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14364 = true := by
  rw [show D2M8K2.u14364 = KTree.node D2M8K2.t14368 (nat_lit 31214706) (nat_lit 2761630622) (nat_lit 0) D2M8K2.t14369 from rfl, allE_node, rows14368, irow14364, rows14369]
  all_goals rfl

theorem atot14364 : totK PD2M8K2 D2M8K2.u14364 = [0, 0, 407393650310, 966427060128, 403428054790, 25362738656, 0, 0] := by
  rw [show D2M8K2.u14364 = KTree.node D2M8K2.t14368 (nat_lit 31214706) (nat_lit 2761630622) (nat_lit 0) D2M8K2.t14369 from rfl, totK_node, tot14368, tot14369]
  decide +kernel

theorem arows14365 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14365 = true := by
  rw [show D2M8K2.u14365 = KTree.node D2M8K2.t14370 (nat_lit 31216192) (nat_lit 3015626328) (nat_lit 0) D2M8K2.t14371 from rfl, allE_node, rows14370, irow14365, rows14371]
  all_goals rfl

theorem atot14365 : totK PD2M8K2 D2M8K2.u14365 = [0, 0, 172856664191, 769918789343, 705301345779, 110176412761, 1162935789, 0] := by
  rw [show D2M8K2.u14365 = KTree.node D2M8K2.t14370 (nat_lit 31216192) (nat_lit 3015626328) (nat_lit 0) D2M8K2.t14371 from rfl, totK_node, tot14370, tot14371]
  decide +kernel

theorem arows14367 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14367 = true := by
  rw [show D2M8K2.u14367 = KTree.node D2M8K2.t14372 (nat_lit 31221512) (nat_lit 3643078003) (nat_lit 0) D2M8K2.t14373 from rfl, allE_node, rows14372, irow14367, rows14373]
  all_goals rfl

theorem atot14367 : totK PD2M8K2 D2M8K2.u14367 = [0, 0, 209351955308, 671057123438, 634517395825, 191918641531, 11853261585, 0] := by
  rw [show D2M8K2.u14367 = KTree.node D2M8K2.t14372 (nat_lit 31221512) (nat_lit 3643078003) (nat_lit 0) D2M8K2.t14373 from rfl, totK_node, tot14372, tot14373]
  decide +kernel

theorem arows14368 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14368 = true := by
  rw [show D2M8K2.u14368 = KTree.node D2M8K2.t14374 (nat_lit 31222848) (nat_lit 3383565259) (nat_lit 0) D2M8K2.t14375 from rfl, allE_node, rows14374, irow14368, rows14375]
  all_goals rfl

theorem atot14368 : totK PD2M8K2 D2M8K2.u14368 = [0, 0, 179429366641, 771146888785, 651423332864, 87844581206, 1021600638, 0] := by
  rw [show D2M8K2.u14368 = KTree.node D2M8K2.t14374 (nat_lit 31222848) (nat_lit 3383565259) (nat_lit 0) D2M8K2.t14375 from rfl, totK_node, tot14374, tot14375]
  decide +kernel

theorem arows14371 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14371 = true := by
  rw [show D2M8K2.u14371 = KTree.node D2M8K2.t14376 (nat_lit 31225290) (nat_lit 3793877444) (nat_lit 0) D2M8K2.t14377 from rfl, allE_node, rows14376, irow14371, rows14377]
  all_goals rfl

theorem atot14371 : totK PD2M8K2 D2M8K2.u14371 = [0, 0, 295078151875, 816298619698, 525013884743, 91181596477, 3552795014, 0] := by
  rw [show D2M8K2.u14371 = KTree.node D2M8K2.t14376 (nat_lit 31225290) (nat_lit 3793877444) (nat_lit 0) D2M8K2.t14377 from rfl, totK_node, tot14376, tot14377]
  decide +kernel

theorem arows14372 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14372 = true := by
  rw [show D2M8K2.u14372 = KTree.node D2M8K2.t14378 (nat_lit 31270153) (nat_lit 1508690721) (nat_lit 0) D2M8K2.t14379 from rfl, allE_node, rows14378, irow14372, rows14379]
  all_goals rfl

theorem atot14372 : totK PD2M8K2 D2M8K2.u14372 = [0, 273758852699, 784542805946, 571446691215, 142905697894, 8935385149, 0, 0] := by
  rw [show D2M8K2.u14372 = KTree.node D2M8K2.t14378 (nat_lit 31270153) (nat_lit 1508690721) (nat_lit 0) D2M8K2.t14379 from rfl, totK_node, tot14378, tot14379]
  decide +kernel

theorem arows14374 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14374 = true := by
  rw [show D2M8K2.u14374 = KTree.node D2M8K2.t14380 (nat_lit 31271754) (nat_lit 3073020604) (nat_lit 0) D2M8K2.t14381 from rfl, allE_node, rows14380, irow14374, rows14381]
  all_goals rfl

theorem atot14374 : totK PD2M8K2 D2M8K2.u14374 = [0, 116824446283, 703445874258, 814113076334, 126423424335, 1310166938, 0, 0] := by
  rw [show D2M8K2.u14374 = KTree.node D2M8K2.t14380 (nat_lit 31271754) (nat_lit 3073020604) (nat_lit 0) D2M8K2.t14381 from rfl, totK_node, tot14380, tot14381]
  decide +kernel

theorem arows14375 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14375 = true := by
  rw [show D2M8K2.u14375 = KTree.node D2M8K2.t14382 (nat_lit 31274120) (nat_lit 3620394783) (nat_lit 0) D2M8K2.t14383 from rfl, allE_node, rows14382, irow14375, rows14383]
  all_goals rfl

theorem atot14375 : totK PD2M8K2 D2M8K2.u14375 = [0, 355819884447, 904882313088, 525817831506, 47900244700, 0, 0, 0] := by
  rw [show D2M8K2.u14375 = KTree.node D2M8K2.t14382 (nat_lit 31274120) (nat_lit 3620394783) (nat_lit 0) D2M8K2.t14383 from rfl, totK_node, tot14382, tot14383]
  decide +kernel

theorem arows14379 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14379 = true := by
  rw [show D2M8K2.u14379 = KTree.node D2M8K2.t14384 (nat_lit 31275716) (nat_lit 3340106819) (nat_lit 0) D2M8K2.t14385 from rfl, allE_node, rows14384, irow14379, rows14385]
  all_goals rfl

theorem atot14379 : totK PD2M8K2 D2M8K2.u14379 = [0, 50798055242, 517227198896, 911632919820, 337388005044, 15013989272, 0, 0] := by
  rw [show D2M8K2.u14379 = KTree.node D2M8K2.t14384 (nat_lit 31275716) (nat_lit 3340106819) (nat_lit 0) D2M8K2.t14385 from rfl, totK_node, tot14384, tot14385]
  decide +kernel

theorem arows14380 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14380 = true := by
  rw [show D2M8K2.u14380 = KTree.node D2M8K2.t14386 (nat_lit 31277311) (nat_lit 1875087344) (nat_lit 0) D2M8K2.t14387 from rfl, allE_node, rows14386, irow14380, rows14387]
  all_goals rfl

theorem atot14380 : totK PD2M8K2 D2M8K2.u14380 = [0, 351391829147, 904932122675, 511063961399, 47001021670, 0, 0, 0] := by
  rw [show D2M8K2.u14380 = KTree.node D2M8K2.t14386 (nat_lit 31277311) (nat_lit 1875087344) (nat_lit 0) D2M8K2.t14387 from rfl, totK_node, tot14386, tot14387]
  decide +kernel

theorem arows14382 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14382 = true := by
  rw [show D2M8K2.u14382 = KTree.node D2M8K2.t14388 (nat_lit 31278872) (nat_lit 3704549570) (nat_lit 0) D2M8K2.t14389 from rfl, allE_node, rows14388, irow14382, rows14389]
  all_goals rfl

theorem atot14382 : totK PD2M8K2 D2M8K2.u14382 = [0, 72246768061, 575758855082, 876700628515, 243143750931, 10568566766, 0, 0] := by
  rw [show D2M8K2.u14382 = KTree.node D2M8K2.t14388 (nat_lit 31278872) (nat_lit 3704549570) (nat_lit 0) D2M8K2.t14389 from rfl, totK_node, tot14388, tot14389]
  decide +kernel

theorem arows14383 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14383 = true := by
  rw [show D2M8K2.u14383 = KTree.node D2M8K2.t14390 (nat_lit 31284127) (nat_lit 1785391625) (nat_lit 0) D2M8K2.t14391 from rfl, allE_node, rows14390, irow14383, rows14391]
  all_goals rfl

theorem atot14383 : totK PD2M8K2 D2M8K2.u14383 = [0, 331308022482, 848484708151, 539193291477, 82732704248, 2481160468, 0, 0] := by
  rw [show D2M8K2.u14383 = KTree.node D2M8K2.t14390 (nat_lit 31284127) (nat_lit 1785391625) (nat_lit 0) D2M8K2.t14391 from rfl, totK_node, tot14390, tot14391]
  decide +kernel

theorem arows14386 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14386 = true := by
  rw [show D2M8K2.u14386 = KTree.node D2M8K2.t14392 (nat_lit 31285662) (nat_lit 3734883806) (nat_lit 0) D2M8K2.t14393 from rfl, allE_node, rows14392, irow14386, rows14393]
  all_goals rfl

theorem atot14386 : totK PD2M8K2 D2M8K2.u14386 = [0, 92237621127, 699524887281, 866042382521, 135767369192, 1096505104, 0, 0] := by
  rw [show D2M8K2.u14386 = KTree.node D2M8K2.t14392 (nat_lit 31285662) (nat_lit 3734883806) (nat_lit 0) D2M8K2.t14393 from rfl, totK_node, tot14392, tot14393]
  decide +kernel

theorem arows14387 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14387 = true := by
  rw [show D2M8K2.u14387 = KTree.node D2M8K2.t14394 (nat_lit 31291356) (nat_lit 3155185996) (nat_lit 0) D2M8K2.t14395 from rfl, allE_node, rows14394, irow14387, rows14395]
  all_goals rfl

theorem atot14387 : totK PD2M8K2 D2M8K2.u14387 = [0, 0, 362055877528, 948873056003, 396643229738, 18555423321, 0, 0] := by
  rw [show D2M8K2.u14387 = KTree.node D2M8K2.t14394 (nat_lit 31291356) (nat_lit 3155185996) (nat_lit 0) D2M8K2.t14395 from rfl, totK_node, tot14394, tot14395]
  decide +kernel

theorem arows14389 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14389 = true := by
  rw [show D2M8K2.u14389 = KTree.node D2M8K2.t14396 (nat_lit 31293319) (nat_lit 2383902045) (nat_lit 0) D2M8K2.t14397 from rfl, allE_node, rows14396, irow14389, rows14397]
  all_goals rfl

theorem atot14389 : totK PD2M8K2 D2M8K2.u14389 = [0, 0, 173250243354, 790859581185, 667607277007, 79548647015, 1103454931, 0] := by
  rw [show D2M8K2.u14389 = KTree.node D2M8K2.t14396 (nat_lit 31293319) (nat_lit 2383902045) (nat_lit 0) D2M8K2.t14397 from rfl, totK_node, tot14396, tot14397]
  decide +kernel

theorem arows14390 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14390 = true := by
  rw [show D2M8K2.u14390 = KTree.node D2M8K2.t14398 (nat_lit 31295493) (nat_lit 1711144996) (nat_lit 0) D2M8K2.t14399 from rfl, allE_node, rows14398, irow14390, rows14399]
  all_goals rfl

theorem atot14390 : totK PD2M8K2 D2M8K2.u14390 = [0, 0, 447258223097, 966363630829, 360147602104, 16260845278, 0, 0] := by
  rw [show D2M8K2.u14390 = KTree.node D2M8K2.t14398 (nat_lit 31295493) (nat_lit 1711144996) (nat_lit 0) D2M8K2.t14399 from rfl, totK_node, tot14398, tot14399]
  decide +kernel

end QECKChecks.D2M8K2
