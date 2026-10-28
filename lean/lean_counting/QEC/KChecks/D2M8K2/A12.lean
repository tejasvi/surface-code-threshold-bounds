import QEC.Count.ChunksK3
import QEC.KChecks.D2M8K2.A11

namespace QECKChecks.D2M8K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows14396 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14396 = true := by
  rw [show D2M8K2.u14396 = KTree.node D2M8K2.t14400 (nat_lit 31298931) (nat_lit 2898622615) (nat_lit 0) D2M8K2.t14401 from rfl, allE_node, rows14400, irow14396, rows14401]
  all_goals rfl

theorem atot14396 : totK PD2M8K2 D2M8K2.u14396 = [0, 0, 385289694337, 942242698462, 409500636958, 18732684427, 0, 0] := by
  rw [show D2M8K2.u14396 = KTree.node D2M8K2.t14400 (nat_lit 31298931) (nat_lit 2898622615) (nat_lit 0) D2M8K2.t14401 from rfl, totK_node, tot14400, tot14401]
  decide +kernel

theorem arows14397 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14397 = true := by
  rw [show D2M8K2.u14397 = KTree.node D2M8K2.t14402 (nat_lit 31305421) (nat_lit 1118879760) (nat_lit 0) D2M8K2.t14403 from rfl, allE_node, rows14402, irow14397, rows14403]
  all_goals rfl

theorem atot14397 : totK PD2M8K2 D2M8K2.u14397 = [0, 0, 280078306104, 846873384927, 534923191269, 61796601043, 1061529118, 0] := by
  rw [show D2M8K2.u14397 = KTree.node D2M8K2.t14402 (nat_lit 31305421) (nat_lit 1118879760) (nat_lit 0) D2M8K2.t14403 from rfl, totK_node, tot14402, tot14403]
  decide +kernel

theorem arows14399 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14399 = true := by
  rw [show D2M8K2.u14399 = KTree.node D2M8K2.t14404 (nat_lit 31307525) (nat_lit 2200345545) (nat_lit 0) D2M8K2.t14405 from rfl, allE_node, rows14404, irow14399, rows14405]
  all_goals rfl

theorem atot14399 : totK PD2M8K2 D2M8K2.u14399 = [0, 175895516967, 436948247500, 511826378065, 497622483005, 109067423929, 3718133097, 0] := by
  rw [show D2M8K2.u14399 = KTree.node D2M8K2.t14404 (nat_lit 31307525) (nat_lit 2200345545) (nat_lit 0) D2M8K2.t14405 from rfl, totK_node, tot14404, tot14405]
  decide +kernel

theorem arows14400 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14400 = true := by
  rw [show D2M8K2.u14400 = KTree.node D2M8K2.t14406 (nat_lit 31312891) (nat_lit 2161658364) (nat_lit 0) D2M8K2.t14407 from rfl, allE_node, rows14406, irow14400, rows14407]
  all_goals rfl

theorem atot14400 : totK PD2M8K2 D2M8K2.u14400 = [0, 231490115458, 771568278936, 664359914974, 107534769414, 1369150432, 0, 0] := by
  rw [show D2M8K2.u14400 = KTree.node D2M8K2.t14406 (nat_lit 31312891) (nat_lit 2161658364) (nat_lit 0) D2M8K2.t14407 from rfl, totK_node, tot14406, tot14407]
  decide +kernel

theorem arows14403 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14403 = true := by
  rw [show D2M8K2.u14403 = KTree.node D2M8K2.t14408 (nat_lit 31315282) (nat_lit 3991163690) (nat_lit 0) D2M8K2.t14409 from rfl, allE_node, rows14408, irow14403, rows14409]
  all_goals rfl

theorem atot14403 : totK PD2M8K2 D2M8K2.u14403 = [0, 261220470529, 829356333071, 675391782340, 70026360616, 0, 0, 0] := by
  rw [show D2M8K2.u14403 = KTree.node D2M8K2.t14408 (nat_lit 31315282) (nat_lit 3991163690) (nat_lit 0) D2M8K2.t14409 from rfl, totK_node, tot14408, tot14409]
  decide +kernel

theorem arows14404 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14404 = true := by
  rw [show D2M8K2.u14404 = KTree.node D2M8K2.t14410 (nat_lit 31316533) (nat_lit 1291986070) (nat_lit 0) D2M8K2.t14411 from rfl, allE_node, rows14410, irow14404, rows14411]
  all_goals rfl

theorem atot14404 : totK PD2M8K2 D2M8K2.u14404 = [0, 157931054148, 656359184404, 722736631040, 263300957563, 22212564151, 0, 0] := by
  rw [show D2M8K2.u14404 = KTree.node D2M8K2.t14410 (nat_lit 31316533) (nat_lit 1291986070) (nat_lit 0) D2M8K2.t14411 from rfl, totK_node, tot14410, tot14411]
  decide +kernel

theorem arows14406 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14406 = true := by
  rw [show D2M8K2.u14406 = KTree.node D2M8K2.t14412 (nat_lit 31318108) (nat_lit 3887696092) (nat_lit 0) D2M8K2.t14413 from rfl, allE_node, rows14412, irow14406, rows14413]
  all_goals rfl

theorem atot14406 : totK PD2M8K2 D2M8K2.u14406 = [0, 172608296538, 613069705590, 743293276657, 272300552832, 10549834746, 0, 0] := by
  rw [show D2M8K2.u14406 = KTree.node D2M8K2.t14412 (nat_lit 31318108) (nat_lit 3887696092) (nat_lit 0) D2M8K2.t14413 from rfl, totK_node, tot14412, tot14413]
  decide +kernel

theorem arows14407 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14407 = true := by
  rw [show D2M8K2.u14407 = KTree.node D2M8K2.t14414 (nat_lit 31319597) (nat_lit 2029103234) (nat_lit 0) D2M8K2.t14415 from rfl, allE_node, rows14414, irow14407, rows14415]
  all_goals rfl

theorem atot14407 : totK PD2M8K2 D2M8K2.u14407 = [0, 252510390656, 796743984394, 647706185567, 95151491602, 1164319620, 0, 0] := by
  rw [show D2M8K2.u14407 = KTree.node D2M8K2.t14414 (nat_lit 31319597) (nat_lit 2029103234) (nat_lit 0) D2M8K2.t14415 from rfl, totK_node, tot14414, tot14415]
  decide +kernel

theorem arows14411 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14411 = true := by
  rw [show D2M8K2.u14411 = KTree.node D2M8K2.t14416 (nat_lit 31321448) (nat_lit 2381345813) (nat_lit 0) D2M8K2.t14417 from rfl, allE_node, rows14416, irow14411, rows14417]
  all_goals rfl

theorem atot14411 : totK PD2M8K2 D2M8K2.u14411 = [0, 166719348841, 708314870930, 762940504985, 184917564549, 8419352411, 0, 0] := by
  rw [show D2M8K2.u14411 = KTree.node D2M8K2.t14416 (nat_lit 31321448) (nat_lit 2381345813) (nat_lit 0) D2M8K2.t14417 from rfl, totK_node, tot14416, tot14417]
  decide +kernel

theorem arows14412 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14412 = true := by
  rw [show D2M8K2.u14412 = KTree.node D2M8K2.t14418 (nat_lit 31323344) (nat_lit 2872758883) (nat_lit 0) D2M8K2.t14419 from rfl, allE_node, rows14418, irow14412, rows14419]
  all_goals rfl

theorem atot14412 : totK PD2M8K2 D2M8K2.u14412 = [0, 178019847832, 739299233848, 774094293762, 127029153986, 1198073392, 0, 0] := by
  rw [show D2M8K2.u14412 = KTree.node D2M8K2.t14418 (nat_lit 31323344) (nat_lit 2872758883) (nat_lit 0) D2M8K2.t14419 from rfl, totK_node, tot14418, tot14419]
  decide +kernel

theorem arows14414 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14414 = true := by
  rw [show D2M8K2.u14414 = KTree.node D2M8K2.t14420 (nat_lit 31328966) (nat_lit 4180403854) (nat_lit 0) D2M8K2.t14421 from rfl, allE_node, rows14420, irow14414, rows14421]
  all_goals rfl

theorem atot14414 : totK PD2M8K2 D2M8K2.u14414 = [0, 270626811635, 795418240403, 628862249670, 124389672422, 4030866388, 0, 0] := by
  rw [show D2M8K2.u14414 = KTree.node D2M8K2.t14420 (nat_lit 31328966) (nat_lit 4180403854) (nat_lit 0) D2M8K2.t14421 from rfl, totK_node, tot14420, tot14421]
  decide +kernel

theorem arows14415 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14415 = true := by
  rw [show D2M8K2.u14415 = KTree.node D2M8K2.t14422 (nat_lit 31330378) (nat_lit 3962179576) (nat_lit 0) D2M8K2.t14423 from rfl, allE_node, rows14422, irow14415, rows14423]
  all_goals rfl

theorem atot14415 : totK PD2M8K2 D2M8K2.u14415 = [0, 168006800142, 716960250101, 771543424786, 161623879256, 2304167554, 0, 0] := by
  rw [show D2M8K2.u14415 = KTree.node D2M8K2.t14422 (nat_lit 31330378) (nat_lit 3962179576) (nat_lit 0) D2M8K2.t14423 from rfl, totK_node, tot14422, tot14423]
  decide +kernel

theorem arows14418 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14418 = true := by
  rw [show D2M8K2.u14418 = KTree.node D2M8K2.t14424 (nat_lit 31332038) (nat_lit 2405650815) (nat_lit 0) D2M8K2.t14425 from rfl, allE_node, rows14424, irow14418, rows14425]
  all_goals rfl

theorem atot14418 : totK PD2M8K2 D2M8K2.u14418 = [180272889912, 443704745879, 370370164111, 506736957950, 255864454896, 19678284834, 0, 0] := by
  rw [show D2M8K2.u14418 = KTree.node D2M8K2.t14424 (nat_lit 31332038) (nat_lit 2405650815) (nat_lit 0) D2M8K2.t14425 from rfl, totK_node, tot14424, tot14425]
  decide +kernel

theorem arows14419 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14419 = true := by
  rw [show D2M8K2.u14419 = KTree.node D2M8K2.t14426 (nat_lit 31354310) (nat_lit 3312602229) (nat_lit 0) D2M8K2.t14427 from rfl, allE_node, rows14426, irow14419, rows14427]
  all_goals rfl

theorem atot14419 : totK PD2M8K2 D2M8K2.u14419 = [249146846529, 797258443897, 640256998127, 106340007897, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u14419 = KTree.node D2M8K2.t14426 (nat_lit 31354310) (nat_lit 3312602229) (nat_lit 0) D2M8K2.t14427 from rfl, totK_node, tot14426, tot14427]
  decide +kernel

theorem arows14421 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14421 = true := by
  rw [show D2M8K2.u14421 = KTree.node D2M8K2.t14428 (nat_lit 31359816) (nat_lit 3616273217) (nat_lit 0) D2M8K2.t14429 from rfl, allE_node, rows14428, irow14421, rows14429]
  all_goals rfl

theorem atot14421 : totK PD2M8K2 D2M8K2.u14421 = [240339319135, 820895093509, 672439314188, 70283255645, 0, 0, 0, 0] := by
  rw [show D2M8K2.u14421 = KTree.node D2M8K2.t14428 (nat_lit 31359816) (nat_lit 3616273217) (nat_lit 0) D2M8K2.t14429 from rfl, totK_node, tot14428, tot14429]
  decide +kernel

theorem arows14422 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14422 = true := by
  rw [show D2M8K2.u14422 = KTree.node D2M8K2.t14430 (nat_lit 31361688) (nat_lit 3443736821) (nat_lit 0) D2M8K2.t14431 from rfl, allE_node, rows14430, irow14422, rows14431]
  all_goals rfl

theorem atot14422 : totK PD2M8K2 D2M8K2.u14422 = [84757123505, 565194394971, 835790798595, 255800152087, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u14422 = KTree.node D2M8K2.t14430 (nat_lit 31361688) (nat_lit 3443736821) (nat_lit 0) D2M8K2.t14431 from rfl, totK_node, tot14430, tot14431]
  decide +kernel

theorem arows14427 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14427 = true := by
  rw [show D2M8K2.u14427 = KTree.node D2M8K2.t14432 (nat_lit 31363756) (nat_lit 3066550817) (nat_lit 0) D2M8K2.t14433 from rfl, allE_node, rows14432, irow14427, rows14433]
  all_goals rfl

theorem atot14427 : totK PD2M8K2 D2M8K2.u14427 = [336114080835, 910412269623, 520737277947, 46566963116, 0, 0, 0, 0] := by
  rw [show D2M8K2.u14427 = KTree.node D2M8K2.t14432 (nat_lit 31363756) (nat_lit 3066550817) (nat_lit 0) D2M8K2.t14433 from rfl, totK_node, tot14432, tot14433]
  decide +kernel

theorem arows14428 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14428 = true := by
  rw [show D2M8K2.u14428 = KTree.node D2M8K2.t14434 (nat_lit 31365294) (nat_lit 4050905317) (nat_lit 0) D2M8K2.t14435 from rfl, allE_node, rows14434, irow14428, rows14435]
  all_goals rfl

theorem atot14428 : totK PD2M8K2 D2M8K2.u14428 = [87346212865, 558266115129, 865173732281, 256187521066, 10680993762, 0, 0, 0] := by
  rw [show D2M8K2.u14428 = KTree.node D2M8K2.t14434 (nat_lit 31365294) (nat_lit 4050905317) (nat_lit 0) D2M8K2.t14435 from rfl, totK_node, tot14434, tot14435]
  decide +kernel

theorem arows14430 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14430 = true := by
  rw [show D2M8K2.u14430 = KTree.node D2M8K2.t14436 (nat_lit 31367129) (nat_lit 1578666161) (nat_lit 0) D2M8K2.t14437 from rfl, allE_node, rows14436, irow14430, rows14437]
  all_goals rfl

theorem atot14430 : totK PD2M8K2 D2M8K2.u14430 = [301429098637, 831694725867, 565289045589, 90558775737, 2569691499, 0, 0, 0] := by
  rw [show D2M8K2.u14430 = KTree.node D2M8K2.t14436 (nat_lit 31367129) (nat_lit 1578666161) (nat_lit 0) D2M8K2.t14437 from rfl, totK_node, tot14436, tot14437]
  decide +kernel

theorem arows14431 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14431 = true := by
  rw [show D2M8K2.u14431 = KTree.node D2M8K2.t14438 (nat_lit 31368777) (nat_lit 1905615121) (nat_lit 0) D2M8K2.t14439 from rfl, allE_node, rows14438, irow14431, rows14439]
  all_goals rfl

theorem atot14431 : totK PD2M8K2 D2M8K2.u14431 = [102638102198, 624246333033, 837717275001, 194569940901, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u14431 = KTree.node D2M8K2.t14438 (nat_lit 31368777) (nat_lit 1905615121) (nat_lit 0) D2M8K2.t14439 from rfl, totK_node, tot14438, tot14439]
  decide +kernel

theorem arows14434 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14434 = true := by
  rw [show D2M8K2.u14434 = KTree.node D2M8K2.t14440 (nat_lit 31370812) (nat_lit 3954847455) (nat_lit 0) D2M8K2.t14441 from rfl, allE_node, rows14440, irow14434, rows14441]
  all_goals rfl

theorem atot14434 : totK PD2M8K2 D2M8K2.u14434 = [387121083410, 939726087557, 464608720713, 37334492173, 0, 0, 0, 0] := by
  rw [show D2M8K2.u14434 = KTree.node D2M8K2.t14440 (nat_lit 31370812) (nat_lit 3954847455) (nat_lit 0) D2M8K2.t14441 from rfl, totK_node, tot14440, tot14441]
  decide +kernel

theorem arows14435 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14435 = true := by
  rw [show D2M8K2.u14435 = KTree.node D2M8K2.t14442 (nat_lit 31372464) (nat_lit 3528314512) (nat_lit 0) D2M8K2.t14443 from rfl, allE_node, rows14442, irow14435, rows14443]
  all_goals rfl

theorem atot14435 : totK PD2M8K2 D2M8K2.u14435 = [0, 492480671062, 976466519364, 302781265252, 8710740030, 0, 0, 0] := by
  rw [show D2M8K2.u14435 = KTree.node D2M8K2.t14442 (nat_lit 31372464) (nat_lit 3528314512) (nat_lit 0) D2M8K2.t14443 from rfl, totK_node, tot14442, tot14443]
  decide +kernel

theorem arows14437 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14437 = true := by
  rw [show D2M8K2.u14437 = KTree.node D2M8K2.t14444 (nat_lit 31374288) (nat_lit 3691793810) (nat_lit 0) D2M8K2.t14445 from rfl, allE_node, rows14444, irow14437, rows14445]
  all_goals rfl

theorem atot14437 : totK PD2M8K2 D2M8K2.u14437 = [0, 360283335048, 921420378393, 447079463574, 32422137020, 0, 0, 0] := by
  rw [show D2M8K2.u14437 = KTree.node D2M8K2.t14444 (nat_lit 31374288) (nat_lit 3691793810) (nat_lit 0) D2M8K2.t14445 from rfl, totK_node, tot14444, tot14445]
  decide +kernel

theorem arows14438 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14438 = true := by
  rw [show D2M8K2.u14438 = KTree.node D2M8K2.t14446 (nat_lit 31375497) (nat_lit 1558687540) (nat_lit 0) D2M8K2.t14447 from rfl, allE_node, rows14446, irow14438, rows14447]
  all_goals rfl

theorem atot14438 : totK PD2M8K2 D2M8K2.u14438 = [0, 87479108234, 694541960446, 798021241040, 138447416182, 1369150432, 0, 0] := by
  rw [show D2M8K2.u14438 = KTree.node D2M8K2.t14446 (nat_lit 31375497) (nat_lit 1558687540) (nat_lit 0) D2M8K2.t14447 from rfl, totK_node, tot14446, tot14447]
  decide +kernel

theorem arows14442 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14442 = true := by
  rw [show D2M8K2.u14442 = KTree.node D2M8K2.t14448 (nat_lit 31381650) (nat_lit 3081604844) (nat_lit 0) D2M8K2.t14449 from rfl, allE_node, rows14448, irow14442, rows14449]
  all_goals rfl

theorem atot14442 : totK PD2M8K2 D2M8K2.u14442 = [0, 396857155623, 935822578440, 425106884464, 29375071298, 0, 0, 0] := by
  rw [show D2M8K2.u14442 = KTree.node D2M8K2.t14448 (nat_lit 31381650) (nat_lit 3081604844) (nat_lit 0) D2M8K2.t14449 from rfl, totK_node, tot14448, tot14449]
  decide +kernel

theorem arows14443 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14443 = true := by
  rw [show D2M8K2.u14443 = KTree.node D2M8K2.t14450 (nat_lit 31385024) (nat_lit 3640172007) (nat_lit 0) D2M8K2.t14451 from rfl, allE_node, rows14450, irow14443, rows14451]
  all_goals rfl

theorem atot14443 : totK PD2M8K2 D2M8K2.u14443 = [0, 349867377291, 951266171049, 463949345627, 20104186504, 0, 0, 0] := by
  rw [show D2M8K2.u14443 = KTree.node D2M8K2.t14450 (nat_lit 31385024) (nat_lit 3640172007) (nat_lit 0) D2M8K2.t14451 from rfl, totK_node, tot14450, tot14451]
  decide +kernel

theorem arows14445 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14445 = true := by
  rw [show D2M8K2.u14445 = KTree.node D2M8K2.t14452 (nat_lit 31388122) (nat_lit 3202073180) (nat_lit 0) D2M8K2.t14453 from rfl, allE_node, rows14452, irow14445, rows14453]
  all_goals rfl

theorem atot14445 : totK PD2M8K2 D2M8K2.u14445 = [0, 377794802043, 926931485345, 430211011169, 25668463760, 0, 0, 0] := by
  rw [show D2M8K2.u14445 = KTree.node D2M8K2.t14452 (nat_lit 31388122) (nat_lit 3202073180) (nat_lit 0) D2M8K2.t14453 from rfl, totK_node, tot14452, tot14453]
  decide +kernel

theorem arows14446 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14446 = true := by
  rw [show D2M8K2.u14446 = KTree.node D2M8K2.t14454 (nat_lit 31391453) (nat_lit 2259678947) (nat_lit 0) D2M8K2.t14455 from rfl, allE_node, rows14454, irow14446, rows14455]
  all_goals rfl

theorem atot14446 : totK PD2M8K2 D2M8K2.u14446 = [0, 381078162134, 959359691881, 447799692714, 19062713096, 0, 0, 0] := by
  rw [show D2M8K2.u14446 = KTree.node D2M8K2.t14454 (nat_lit 31391453) (nat_lit 2259678947) (nat_lit 0) D2M8K2.t14455 from rfl, totK_node, tot14454, tot14455]
  decide +kernel

theorem arows14449 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14449 = true := by
  rw [show D2M8K2.u14449 = KTree.node D2M8K2.t14456 (nat_lit 31398382) (nat_lit 3938442003) (nat_lit 0) D2M8K2.t14457 from rfl, allE_node, rows14456, irow14449, rows14457]
  all_goals rfl

theorem atot14449 : totK PD2M8K2 D2M8K2.u14449 = [316444843064, 789345595824, 563831642126, 161622932208, 13468148062, 0, 0, 0] := by
  rw [show D2M8K2.u14449 = KTree.node D2M8K2.t14456 (nat_lit 31398382) (nat_lit 3938442003) (nat_lit 0) D2M8K2.t14457 from rfl, totK_node, tot14456, tot14457]
  decide +kernel

theorem arows14450 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14450 = true := by
  rw [show D2M8K2.u14450 = KTree.node D2M8K2.t14458 (nat_lit 31399873) (nat_lit 902668003) (nat_lit 0) D2M8K2.t14459 from rfl, allE_node, rows14458, irow14450, rows14459]
  all_goals rfl

theorem atot14450 : totK PD2M8K2 D2M8K2.u14450 = [126175521938, 618946117096, 762335884793, 292275494135, 25373788367, 0, 0, 0] := by
  rw [show D2M8K2.u14450 = KTree.node D2M8K2.t14458 (nat_lit 31399873) (nat_lit 902668003) (nat_lit 0) D2M8K2.t14459 from rfl, totK_node, tot14458, tot14459]
  decide +kernel

theorem arows14452 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14452 = true := by
  rw [show D2M8K2.u14452 = KTree.node D2M8K2.t14460 (nat_lit 31401082) (nat_lit 3671664694) (nat_lit 0) D2M8K2.t14461 from rfl, allE_node, rows14460, irow14452, rows14461]
  all_goals rfl

theorem atot14452 : totK PD2M8K2 D2M8K2.u14452 = [177812611450, 568579792272, 767495756595, 301731677160, 12235609738, 0, 0, 0] := by
  rw [show D2M8K2.u14452 = KTree.node D2M8K2.t14460 (nat_lit 31401082) (nat_lit 3671664694) (nat_lit 0) D2M8K2.t14461 from rfl, totK_node, tot14460, tot14461]
  decide +kernel

theorem arows14453 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14453 = true := by
  rw [show D2M8K2.u14453 = KTree.node D2M8K2.t14462 (nat_lit 31402920) (nat_lit 3311028639) (nat_lit 0) D2M8K2.t14463 from rfl, allE_node, rows14462, irow14453, rows14463]
  all_goals rfl

theorem atot14453 : totK PD2M8K2 D2M8K2.u14453 = [153875893019, 725677490773, 765991364457, 166680688929, 8298533344, 0, 0, 0] := by
  rw [show D2M8K2.u14453 = KTree.node D2M8K2.t14462 (nat_lit 31402920) (nat_lit 3311028639) (nat_lit 0) D2M8K2.t14463 from rfl, totK_node, tot14462, tot14463]
  decide +kernel

theorem arows14460 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14460 = true := by
  rw [show D2M8K2.u14460 = KTree.node D2M8K2.t14464 (nat_lit 31405093) (nat_lit 1128254914) (nat_lit 0) D2M8K2.t14465 from rfl, allE_node, rows14464, irow14460, rows14465]
  all_goals rfl

theorem atot14460 : totK PD2M8K2 D2M8K2.u14460 = [318792990751, 835609707486, 577118959574, 96697125080, 2410802975, 0, 0, 0] := by
  rw [show D2M8K2.u14460 = KTree.node D2M8K2.t14464 (nat_lit 31405093) (nat_lit 1128254914) (nat_lit 0) D2M8K2.t14465 from rfl, totK_node, tot14464, tot14465]
  decide +kernel

theorem arows14461 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14461 = true := by
  rw [show D2M8K2.u14461 = KTree.node D2M8K2.t14466 (nat_lit 31406555) (nat_lit 2143938983) (nat_lit 0) D2M8K2.t14467 from rfl, allE_node, rows14466, irow14461, rows14467]
  all_goals rfl

theorem atot14461 : totK PD2M8K2 D2M8K2.u14461 = [106316469095, 635388796679, 818981613351, 219502370581, 9661765460, 0, 0, 0] := by
  rw [show D2M8K2.u14461 = KTree.node D2M8K2.t14466 (nat_lit 31406555) (nat_lit 2143938983) (nat_lit 0) D2M8K2.t14467 from rfl, totK_node, tot14466, tot14467]
  decide +kernel

theorem arows14463 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14463 = true := by
  rw [show D2M8K2.u14463 = KTree.node D2M8K2.t14468 (nat_lit 31408499) (nat_lit 2607169838) (nat_lit 0) D2M8K2.t14469 from rfl, allE_node, rows14468, irow14463, rows14469]
  all_goals rfl

theorem atot14463 : totK PD2M8K2 D2M8K2.u14463 = [293812135693, 780775624437, 615302051015, 124698087745, 3575904516, 0, 0, 0] := by
  rw [show D2M8K2.u14463 = KTree.node D2M8K2.t14468 (nat_lit 31408499) (nat_lit 2607169838) (nat_lit 0) D2M8K2.t14469 from rfl, totK_node, tot14468, tot14469]
  decide +kernel

theorem arows14464 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14464 = true := by
  rw [show D2M8K2.u14464 = KTree.node D2M8K2.t14470 (nat_lit 31410177) (nat_lit 1787250882) (nat_lit 0) D2M8K2.t14471 from rfl, allE_node, rows14470, irow14464, rows14471]
  all_goals rfl

theorem atot14464 : totK PD2M8K2 D2M8K2.u14464 = [88800000258, 704489164899, 858952518289, 139771697522, 1096156699, 0, 0, 0] := by
  rw [show D2M8K2.u14464 = KTree.node D2M8K2.t14470 (nat_lit 31410177) (nat_lit 1787250882) (nat_lit 0) D2M8K2.t14471 from rfl, totK_node, tot14470, tot14471]
  decide +kernel

theorem arows14467 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14467 = true := by
  rw [show D2M8K2.u14467 = KTree.node D2M8K2.t14472 (nat_lit 31412141) (nat_lit 2177542753) (nat_lit 0) D2M8K2.t14473 from rfl, allE_node, rows14472, irow14467, rows14473]
  all_goals rfl

theorem atot14467 : totK PD2M8K2 D2M8K2.u14467 = [343827327490, 856866634383, 529204597733, 98436050719, 3880716147, 0, 0, 0] := by
  rw [show D2M8K2.u14467 = KTree.node D2M8K2.t14472 (nat_lit 31412141) (nat_lit 2177542753) (nat_lit 0) D2M8K2.t14473 from rfl, totK_node, tot14472, tot14473]
  decide +kernel

theorem arows14468 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14468 = true := by
  rw [show D2M8K2.u14468 = KTree.node D2M8K2.t14474 (nat_lit 31413692) (nat_lit 3082725810) (nat_lit 0) D2M8K2.t14475 from rfl, allE_node, rows14474, irow14468, rows14475]
  all_goals rfl

theorem atot14468 : totK PD2M8K2 D2M8K2.u14468 = [75459327330, 562742951078, 884593984614, 271828383732, 8676337118, 0, 0, 0] := by
  rw [show D2M8K2.u14468 = KTree.node D2M8K2.t14474 (nat_lit 31413692) (nat_lit 3082725810) (nat_lit 0) D2M8K2.t14475 from rfl, totK_node, tot14474, tot14475]
  decide +kernel

theorem arows14470 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14470 = true := by
  rw [show D2M8K2.u14470 = KTree.node D2M8K2.t14476 (nat_lit 31419048) (nat_lit 2640131982) (nat_lit 0) D2M8K2.t14477 from rfl, allE_node, rows14476, irow14470, rows14477]
  all_goals rfl

theorem atot14470 : totK PD2M8K2 D2M8K2.u14470 = [0, 346979684602, 908229868533, 529814899548, 48135432070, 0, 0, 0] := by
  rw [show D2M8K2.u14470 = KTree.node D2M8K2.t14476 (nat_lit 31419048) (nat_lit 2640131982) (nat_lit 0) D2M8K2.t14477 from rfl, totK_node, tot14476, tot14477]
  decide +kernel

theorem arows14471 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14471 = true := by
  rw [show D2M8K2.u14471 = KTree.node D2M8K2.t14478 (nat_lit 31420558) (nat_lit 3962638447) (nat_lit 0) D2M8K2.t14479 from rfl, allE_node, rows14478, irow14471, rows14479]
  all_goals rfl

theorem atot14471 : totK PD2M8K2 D2M8K2.u14471 = [0, 169736934498, 649400139677, 703517005870, 267140663816, 25191558099, 0, 0] := by
  rw [show D2M8K2.u14471 = KTree.node D2M8K2.t14478 (nat_lit 31420558) (nat_lit 3962638447) (nat_lit 0) D2M8K2.t14479 from rfl, totK_node, tot14478, tot14479]
  decide +kernel

theorem arows14475 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14475 = true := by
  rw [show D2M8K2.u14475 = KTree.node D2M8K2.t14480 (nat_lit 31421749) (nat_lit 798241957) (nat_lit 0) D2M8K2.t14481 from rfl, allE_node, rows14480, irow14475, rows14481]
  all_goals rfl

theorem atot14475 : totK PD2M8K2 D2M8K2.u14475 = [0, 155116473731, 553162788160, 799010317156, 296502445380, 11730315755, 0, 0] := by
  rw [show D2M8K2.u14475 = KTree.node D2M8K2.t14480 (nat_lit 31421749) (nat_lit 798241957) (nat_lit 0) D2M8K2.t14481 from rfl, totK_node, tot14480, tot14481]
  decide +kernel

theorem arows14476 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14476 = true := by
  rw [show D2M8K2.u14476 = KTree.node D2M8K2.t14482 (nat_lit 31423587) (nat_lit 3481550644) (nat_lit 0) D2M8K2.t14483 from rfl, allE_node, rows14482, irow14476, rows14483]
  all_goals rfl

theorem atot14476 : totK PD2M8K2 D2M8K2.u14476 = [0, 175713225586, 754444882145, 733818520715, 147141608011, 4009909289, 0, 0] := by
  rw [show D2M8K2.u14476 = KTree.node D2M8K2.t14482 (nat_lit 31423587) (nat_lit 3481550644) (nat_lit 0) D2M8K2.t14483 from rfl, totK_node, tot14482, tot14483]
  decide +kernel

theorem arows14478 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14478 = true := by
  rw [show D2M8K2.u14478 = KTree.node D2M8K2.t14484 (nat_lit 31425812) (nat_lit 3665666850) (nat_lit 0) D2M8K2.t14485 from rfl, allE_node, rows14484, irow14478, rows14485]
  all_goals rfl

theorem atot14478 : totK PD2M8K2 D2M8K2.u14478 = [0, 306347664047, 825224696545, 593981685156, 93955958709, 1149959346, 0, 0] := by
  rw [show D2M8K2.u14478 = KTree.node D2M8K2.t14484 (nat_lit 31425812) (nat_lit 3665666850) (nat_lit 0) D2M8K2.t14485 from rfl, totK_node, tot14484, tot14485]
  decide +kernel

theorem arows14479 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14479 = true := by
  rw [show D2M8K2.u14479 = KTree.node D2M8K2.t14486 (nat_lit 31427468) (nat_lit 3662522644) (nat_lit 0) D2M8K2.t14487 from rfl, allE_node, rows14486, irow14479, rows14487]
  all_goals rfl

theorem atot14479 : totK PD2M8K2 D2M8K2.u14479 = [0, 113110112629, 688364318296, 810162922857, 163403574543, 4031931762, 0, 0] := by
  rw [show D2M8K2.u14479 = KTree.node D2M8K2.t14486 (nat_lit 31427468) (nat_lit 3662522644) (nat_lit 0) D2M8K2.t14487 from rfl, totK_node, tot14486, tot14487]
  decide +kernel

theorem arows14482 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14482 = true := by
  rw [show D2M8K2.u14482 = KTree.node D2M8K2.t14488 (nat_lit 31429365) (nat_lit 1129450946) (nat_lit 0) D2M8K2.t14489 from rfl, allE_node, rows14488, irow14482, rows14489]
  all_goals rfl

theorem atot14482 : totK PD2M8K2 D2M8K2.u14482 = [0, 292836293310, 837661677098, 586815712557, 93290756151, 1186940923, 0, 0] := by
  rw [show D2M8K2.u14482 = KTree.node D2M8K2.t14488 (nat_lit 31429365) (nat_lit 1129450946) (nat_lit 0) D2M8K2.t14489 from rfl, totK_node, tot14488, tot14489]
  decide +kernel

theorem arows14483 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14483 = true := by
  rw [show D2M8K2.u14483 = KTree.node D2M8K2.t14490 (nat_lit 31431238) (nat_lit 3201843285) (nat_lit 0) D2M8K2.t14491 from rfl, allE_node, rows14490, irow14483, rows14491]
  all_goals rfl

theorem atot14483 : totK PD2M8K2 D2M8K2.u14483 = [0, 157024141252, 719694398244, 786088087128, 137718308770, 1415142070, 0, 0] := by
  rw [show D2M8K2.u14483 = KTree.node D2M8K2.t14490 (nat_lit 31431238) (nat_lit 3201843285) (nat_lit 0) D2M8K2.t14491 from rfl, totK_node, tot14490, tot14491]
  decide +kernel

theorem arows14485 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14485 = true := by
  rw [show D2M8K2.u14485 = KTree.node D2M8K2.t14492 (nat_lit 31433097) (nat_lit 1605983648) (nat_lit 0) D2M8K2.t14493 from rfl, allE_node, rows14492, irow14485, rows14493]
  all_goals rfl

theorem atot14485 : totK PD2M8K2 D2M8K2.u14485 = [0, 349972291798, 927548040770, 522831111027, 40089412590, 0, 0, 0] := by
  rw [show D2M8K2.u14485 = KTree.node D2M8K2.t14492 (nat_lit 31433097) (nat_lit 1605983648) (nat_lit 0) D2M8K2.t14493 from rfl, totK_node, tot14492, tot14493]
  decide +kernel

theorem arows14486 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14486 = true := by
  rw [show D2M8K2.u14486 = KTree.node D2M8K2.t14494 (nat_lit 31434958) (nat_lit 3909730644) (nat_lit 0) D2M8K2.t14495 from rfl, allE_node, rows14494, irow14486, rows14495]
  all_goals rfl

theorem atot14486 : totK PD2M8K2 D2M8K2.u14486 = [71933061318, 99622542677, 450664811684, 868868031210, 281394548318, 9302370699, 0, 0] := by
  rw [show D2M8K2.u14486 = KTree.node D2M8K2.t14494 (nat_lit 31434958) (nat_lit 3909730644) (nat_lit 0) D2M8K2.t14495 from rfl, totK_node, tot14494, tot14495]
  decide +kernel

theorem arows14491 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14491 = true := by
  rw [show D2M8K2.u14491 = KTree.node D2M8K2.t14496 (nat_lit 31478338) (nat_lit 3912653223) (nat_lit 0) D2M8K2.t14497 from rfl, allE_node, rows14496, irow14491, rows14497]
  all_goals rfl

theorem atot14491 : totK PD2M8K2 D2M8K2.u14491 = [341311181406, 932885278818, 473103180446, 26072191254, 0, 0, 0, 0] := by
  rw [show D2M8K2.u14491 = KTree.node D2M8K2.t14496 (nat_lit 31478338) (nat_lit 3912653223) (nat_lit 0) D2M8K2.t14497 from rfl, totK_node, tot14496, tot14497]
  decide +kernel

theorem arows14492 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14492 = true := by
  rw [show D2M8K2.u14492 = KTree.node D2M8K2.t14498 (nat_lit 31480136) (nat_lit 3697004479) (nat_lit 0) D2M8K2.t14499 from rfl, allE_node, rows14498, irow14492, rows14499]
  all_goals rfl

theorem atot14492 : totK PD2M8K2 D2M8K2.u14492 = [93305483181, 650271926378, 898699914263, 165285277969, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u14492 = KTree.node D2M8K2.t14498 (nat_lit 31480136) (nat_lit 3697004479) (nat_lit 0) D2M8K2.t14499 from rfl, totK_node, tot14498, tot14499]
  decide +kernel

theorem arows14494 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14494 = true := by
  rw [show D2M8K2.u14494 = KTree.node D2M8K2.t14500 (nat_lit 31481898) (nat_lit 3829457552) (nat_lit 0) D2M8K2.t14501 from rfl, allE_node, rows14500, irow14494, rows14501]
  all_goals rfl

theorem atot14494 : totK PD2M8K2 D2M8K2.u14494 = [330324744147, 905898283492, 530614607019, 50360728393, 0, 0, 0, 0] := by
  rw [show D2M8K2.u14494 = KTree.node D2M8K2.t14500 (nat_lit 31481898) (nat_lit 3829457552) (nat_lit 0) D2M8K2.t14501 from rfl, totK_node, tot14500, tot14501]
  decide +kernel

theorem arows14495 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14495 = true := by
  rw [show D2M8K2.u14495 = KTree.node D2M8K2.t14502 (nat_lit 31483400) (nat_lit 3883878365) (nat_lit 0) D2M8K2.t14503 from rfl, allE_node, rows14502, irow14495, rows14503]
  all_goals rfl

theorem atot14495 : totK PD2M8K2 D2M8K2.u14495 = [0, 382045442302, 945446184650, 444107776502, 30613093193, 0, 0, 0] := by
  rw [show D2M8K2.u14495 = KTree.node D2M8K2.t14502 (nat_lit 31483400) (nat_lit 3883878365) (nat_lit 0) D2M8K2.t14503 from rfl, totK_node, tot14502, tot14503]
  decide +kernel

theorem arows14498 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14498 = true := by
  rw [show D2M8K2.u14498 = KTree.node D2M8K2.t14504 (nat_lit 31488122) (nat_lit 4109651873) (nat_lit 0) D2M8K2.t14505 from rfl, allE_node, rows14504, irow14498, rows14505]
  all_goals rfl

theorem atot14498 : totK PD2M8K2 D2M8K2.u14498 = [357065584806, 863287612246, 492348910087, 114105259490, 6775760191, 0, 0, 0] := by
  rw [show D2M8K2.u14498 = KTree.node D2M8K2.t14504 (nat_lit 31488122) (nat_lit 4109651873) (nat_lit 0) D2M8K2.t14505 from rfl, totK_node, tot14504, tot14505]
  decide +kernel

theorem arows14499 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14499 = true := by
  rw [show D2M8K2.u14499 = KTree.node D2M8K2.t14506 (nat_lit 31489591) (nat_lit 2214148709) (nat_lit 0) D2M8K2.t14507 from rfl, allE_node, rows14506, irow14499, rows14507]
  all_goals rfl

theorem atot14499 : totK PD2M8K2 D2M8K2.u14499 = [88945508586, 614266789704, 866567889367, 230293952610, 9668735432, 0, 0, 0] := by
  rw [show D2M8K2.u14499 = KTree.node D2M8K2.t14506 (nat_lit 31489591) (nat_lit 2214148709) (nat_lit 0) D2M8K2.t14507 from rfl, totK_node, tot14506, tot14507]
  decide +kernel

theorem arows14501 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14501 = true := by
  rw [show D2M8K2.u14501 = KTree.node D2M8K2.t14508 (nat_lit 31491407) (nat_lit 2088812403) (nat_lit 0) D2M8K2.t14509 from rfl, allE_node, rows14508, irow14501, rows14509]
  all_goals rfl

theorem atot14501 : totK PD2M8K2 D2M8K2.u14501 = [294568301059, 789907783994, 581539888154, 115343376276, 3581949829, 0, 0, 0] := by
  rw [show D2M8K2.u14501 = KTree.node D2M8K2.t14508 (nat_lit 31491407) (nat_lit 2088812403) (nat_lit 0) D2M8K2.t14509 from rfl, totK_node, tot14508, tot14509]
  decide +kernel

theorem arows14502 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14502 = true := by
  rw [show D2M8K2.u14502 = KTree.node D2M8K2.t14510 (nat_lit 31492949) (nat_lit 2016679788) (nat_lit 0) D2M8K2.t14511 from rfl, allE_node, rows14510, irow14502, rows14511]
  all_goals rfl

theorem atot14502 : totK PD2M8K2 D2M8K2.u14502 = [102007566730, 710806154700, 841141182312, 131957338652, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u14502 = KTree.node D2M8K2.t14510 (nat_lit 31492949) (nat_lit 2016679788) (nat_lit 0) D2M8K2.t14511 from rfl, totK_node, tot14510, tot14511]
  decide +kernel

theorem arows14506 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14506 = true := by
  rw [show D2M8K2.u14506 = KTree.node D2M8K2.t14512 (nat_lit 31494991) (nat_lit 2229612231) (nat_lit 0) D2M8K2.t14513 from rfl, allE_node, rows14512, irow14506, rows14513]
  all_goals rfl

theorem atot14506 : totK PD2M8K2 D2M8K2.u14506 = [331772422912, 845834100289, 535601734835, 104922093103, 3884009855, 0, 0, 0] := by
  rw [show D2M8K2.u14506 = KTree.node D2M8K2.t14512 (nat_lit 31494991) (nat_lit 2229612231) (nat_lit 0) D2M8K2.t14513 from rfl, totK_node, tot14512, tot14513]
  decide +kernel

theorem arows14507 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14507 = true := by
  rw [show D2M8K2.u14507 = KTree.node D2M8K2.t14514 (nat_lit 31496496) (nat_lit 3425049145) (nat_lit 0) D2M8K2.t14515 from rfl, allE_node, rows14514, irow14507, rows14515]
  all_goals rfl

theorem atot14507 : totK PD2M8K2 D2M8K2.u14507 = [92620862180, 601127012736, 871704867294, 229375759377, 4949222506, 0, 0, 0] := by
  rw [show D2M8K2.u14507 = KTree.node D2M8K2.t14514 (nat_lit 31496496) (nat_lit 3425049145) (nat_lit 0) D2M8K2.t14515 from rfl, totK_node, tot14514, tot14515]
  decide +kernel

theorem arows14509 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14509 = true := by
  rw [show D2M8K2.u14509 = KTree.node D2M8K2.t14516 (nat_lit 31498179) (nat_lit 660910161) (nat_lit 0) D2M8K2.t14517 from rfl, allE_node, rows14516, irow14509, rows14517]
  all_goals rfl

theorem atot14509 : totK PD2M8K2 D2M8K2.u14509 = [0, 358588535424, 941977087661, 447011200543, 27082812728, 0, 0, 0] := by
  rw [show D2M8K2.u14509 = KTree.node D2M8K2.t14516 (nat_lit 31498179) (nat_lit 660910161) (nat_lit 0) D2M8K2.t14517 from rfl, totK_node, tot14516, tot14517]
  decide +kernel

theorem arows14510 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14510 = true := by
  rw [show D2M8K2.u14510 = KTree.node D2M8K2.t14518 (nat_lit 31499793) (nat_lit 1805487424) (nat_lit 0) D2M8K2.t14519 from rfl, allE_node, rows14518, irow14510, rows14519]
  all_goals rfl

theorem atot14510 : totK PD2M8K2 D2M8K2.u14510 = [0, 144796516941, 726480770296, 741107161071, 102983508103, 1239866073, 0, 0] := by
  rw [show D2M8K2.u14510 = KTree.node D2M8K2.t14518 (nat_lit 31499793) (nat_lit 1805487424) (nat_lit 0) D2M8K2.t14519 from rfl, totK_node, tot14518, tot14519]
  decide +kernel

theorem arows14513 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14513 = true := by
  rw [show D2M8K2.u14513 = KTree.node D2M8K2.t14520 (nat_lit 31502213) (nat_lit 2330844828) (nat_lit 0) D2M8K2.t14521 from rfl, allE_node, rows14520, irow14513, rows14521]
  all_goals rfl

theorem atot14513 : totK PD2M8K2 D2M8K2.u14513 = [0, 334521686842, 919503403171, 533314614993, 43607110266, 0, 0, 0] := by
  rw [show D2M8K2.u14513 = KTree.node D2M8K2.t14520 (nat_lit 31502213) (nat_lit 2330844828) (nat_lit 0) D2M8K2.t14521 from rfl, totK_node, tot14520, tot14521]
  decide +kernel

theorem arows14514 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14514 = true := by
  rw [show D2M8K2.u14514 = KTree.node D2M8K2.t14522 (nat_lit 31508675) (nat_lit 2852505898) (nat_lit 0) D2M8K2.t14523 from rfl, allE_node, rows14522, irow14514, rows14523]
  all_goals rfl

theorem atot14514 : totK PD2M8K2 D2M8K2.u14514 = [0, 356620286645, 911425242835, 511409343227, 42886542815, 0, 0, 0] := by
  rw [show D2M8K2.u14514 = KTree.node D2M8K2.t14522 (nat_lit 31508675) (nat_lit 2852505898) (nat_lit 0) D2M8K2.t14523 from rfl, totK_node, tot14522, tot14523]
  decide +kernel

theorem arows14516 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14516 = true := by
  rw [show D2M8K2.u14516 = KTree.node D2M8K2.t14524 (nat_lit 31510092) (nat_lit 3547315960) (nat_lit 0) D2M8K2.t14525 from rfl, allE_node, rows14524, irow14516, rows14525]
  all_goals rfl

theorem atot14516 : totK PD2M8K2 D2M8K2.u14516 = [0, 174878768978, 711473728617, 738370248979, 154199971384, 2318623666, 0, 0] := by
  rw [show D2M8K2.u14516 = KTree.node D2M8K2.t14524 (nat_lit 31510092) (nat_lit 3547315960) (nat_lit 0) D2M8K2.t14525 from rfl, totK_node, tot14524, tot14525]
  decide +kernel

theorem arows14517 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14517 = true := by
  rw [show D2M8K2.u14517 = KTree.node D2M8K2.t14526 (nat_lit 31511932) (nat_lit 2587488734) (nat_lit 0) D2M8K2.t14527 from rfl, allE_node, rows14526, irow14517, rows14527]
  all_goals rfl

theorem atot14517 : totK PD2M8K2 D2M8K2.u14517 = [0, 225680762906, 734422588815, 611877907862, 146099463682, 10786826731, 0, 0] := by
  rw [show D2M8K2.u14517 = KTree.node D2M8K2.t14526 (nat_lit 31511932) (nat_lit 2587488734) (nat_lit 0) D2M8K2.t14527 from rfl, totK_node, tot14526, tot14527]
  decide +kernel

theorem arows14523 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14523 = true := by
  rw [show D2M8K2.u14523 = KTree.node D2M8K2.t14528 (nat_lit 31513587) (nat_lit 765794466) (nat_lit 0) D2M8K2.t14529 from rfl, allE_node, rows14528, irow14523, rows14529]
  all_goals rfl

theorem atot14523 : totK PD2M8K2 D2M8K2.u14523 = [0, 168442776982, 779297653213, 718407199837, 91942128097, 1053411165, 0, 0] := by
  rw [show D2M8K2.u14523 = KTree.node D2M8K2.t14528 (nat_lit 31513587) (nat_lit 765794466) (nat_lit 0) D2M8K2.t14529 from rfl, totK_node, tot14528, tot14529]
  decide +kernel

theorem arows14524 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14524 = true := by
  rw [show D2M8K2.u14524 = KTree.node D2M8K2.t14530 (nat_lit 31515656) (nat_lit 3712152935) (nat_lit 0) D2M8K2.t14531 from rfl, allE_node, rows14530, irow14524, rows14531]
  all_goals rfl

theorem atot14524 : totK PD2M8K2 D2M8K2.u14524 = [0, 330332263056, 822029222447, 522709203713, 98426542632, 3667207281, 0, 0] := by
  rw [show D2M8K2.u14524 = KTree.node D2M8K2.t14530 (nat_lit 31515656) (nat_lit 3712152935) (nat_lit 0) D2M8K2.t14531 from rfl, totK_node, tot14530, tot14531]
  decide +kernel

theorem arows14526 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14526 = true := by
  rw [show D2M8K2.u14526 = KTree.node D2M8K2.t14532 (nat_lit 31518865) (nat_lit 1563005411) (nat_lit 0) D2M8K2.t14533 from rfl, allE_node, rows14532, irow14526, rows14533]
  all_goals rfl

theorem atot14526 : totK PD2M8K2 D2M8K2.u14526 = [242255341689, 690861058760, 590480615305, 247970459960, 22079973395, 0, 0, 0] := by
  rw [show D2M8K2.u14526 = KTree.node D2M8K2.t14532 (nat_lit 31518865) (nat_lit 1563005411) (nat_lit 0) D2M8K2.t14533 from rfl, totK_node, tot14532, tot14533]
  decide +kernel

theorem arows14527 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14527 = true := by
  rw [show D2M8K2.u14527 = KTree.node D2M8K2.t14534 (nat_lit 31520508) (nat_lit 3235948554) (nat_lit 0) D2M8K2.t14535 from rfl, allE_node, rows14534, irow14527, rows14535]
  all_goals rfl

theorem atot14527 : totK PD2M8K2 D2M8K2.u14527 = [153142458884, 712683466507, 770909567654, 132531073234, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u14527 = KTree.node D2M8K2.t14534 (nat_lit 31520508) (nat_lit 3235948554) (nat_lit 0) D2M8K2.t14535 from rfl, totK_node, tot14534, tot14535]
  decide +kernel

theorem arows14530 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14530 = true := by
  rw [show D2M8K2.u14530 = KTree.node D2M8K2.t14536 (nat_lit 31522866) (nat_lit 2730595991) (nat_lit 0) D2M8K2.t14537 from rfl, allE_node, rows14536, irow14530, rows14537]
  all_goals rfl

theorem atot14530 : totK PD2M8K2 D2M8K2.u14530 = [336922046974, 879854301830, 561766879211, 58460946939, 0, 0, 0, 0] := by
  rw [show D2M8K2.u14530 = KTree.node D2M8K2.t14536 (nat_lit 31522866) (nat_lit 2730595991) (nat_lit 0) D2M8K2.t14537 from rfl, totK_node, tot14536, tot14537]
  decide +kernel

theorem arows14531 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14531 = true := by
  rw [show D2M8K2.u14531 = KTree.node D2M8K2.t14538 (nat_lit 31524422) (nat_lit 3902154376) (nat_lit 0) D2M8K2.t14539 from rfl, allE_node, rows14538, irow14531, rows14539]
  all_goals rfl

theorem atot14531 : totK PD2M8K2 D2M8K2.u14531 = [70166284074, 523058342713, 831031271460, 367322276329, 29380002449, 0, 0, 0] := by
  rw [show D2M8K2.u14531 = KTree.node D2M8K2.t14538 (nat_lit 31524422) (nat_lit 3902154376) (nat_lit 0) D2M8K2.t14539 from rfl, totK_node, tot14538, tot14539]
  decide +kernel

theorem arows14533 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14533 = true := by
  rw [show D2M8K2.u14533 = KTree.node D2M8K2.t14540 (nat_lit 31529210) (nat_lit 2733850023) (nat_lit 0) D2M8K2.t14541 from rfl, allE_node, rows14540, irow14533, rows14541]
  all_goals rfl

theorem atot14533 : totK PD2M8K2 D2M8K2.u14533 = [256380992610, 703663169892, 641525615181, 213164317419, 8187600046, 0, 0, 0] := by
  rw [show D2M8K2.u14533 = KTree.node D2M8K2.t14540 (nat_lit 31529210) (nat_lit 2733850023) (nat_lit 0) D2M8K2.t14541 from rfl, totK_node, tot14540, tot14541]
  decide +kernel

theorem arows14534 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14534 = true := by
  rw [show D2M8K2.u14534 = KTree.node D2M8K2.t14542 (nat_lit 31530699) (nat_lit 3713622308) (nat_lit 0) D2M8K2.t14543 from rfl, allE_node, rows14542, irow14534, rows14543]
  all_goals rfl

theorem atot14534 : totK PD2M8K2 D2M8K2.u14534 = [164634488024, 754282394097, 749769226795, 128471181512, 1198073392, 0, 0, 0] := by
  rw [show D2M8K2.u14534 = KTree.node D2M8K2.t14542 (nat_lit 31530699) (nat_lit 3713622308) (nat_lit 0) D2M8K2.t14543 from rfl, totK_node, tot14542, tot14543]
  decide +kernel

theorem arows14538 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14538 = true := by
  rw [show D2M8K2.u14538 = KTree.node D2M8K2.t14544 (nat_lit 31532551) (nat_lit 2362901600) (nat_lit 0) D2M8K2.t14545 from rfl, allE_node, rows14544, irow14538, rows14545]
  all_goals rfl

theorem atot14538 : totK PD2M8K2 D2M8K2.u14538 = [188275097757, 647827492240, 714944544251, 219410585890, 12052611869, 0, 0, 0] := by
  rw [show D2M8K2.u14538 = KTree.node D2M8K2.t14544 (nat_lit 31532551) (nat_lit 2362901600) (nat_lit 0) D2M8K2.t14545 from rfl, totK_node, tot14544, tot14545]
  decide +kernel

theorem arows14539 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14539 = true := by
  rw [show D2M8K2.u14539 = KTree.node D2M8K2.t14546 (nat_lit 31533758) (nat_lit 3843185347) (nat_lit 0) D2M8K2.t14547 from rfl, allE_node, rows14546, irow14539, rows14547]
  all_goals rfl

theorem atot14539 : totK PD2M8K2 D2M8K2.u14539 = [235913108982, 797324044231, 664628147478, 100650154178, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u14539 = KTree.node D2M8K2.t14546 (nat_lit 31533758) (nat_lit 3843185347) (nat_lit 0) D2M8K2.t14547 from rfl, totK_node, tot14546, tot14547]
  decide +kernel

theorem arows14541 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14541 = true := by
  rw [show D2M8K2.u14541 = KTree.node D2M8K2.t14548 (nat_lit 31539515) (nat_lit 2750676357) (nat_lit 0) D2M8K2.t14549 from rfl, allE_node, rows14548, irow14541, rows14549]
  all_goals rfl

theorem atot14541 : totK PD2M8K2 D2M8K2.u14541 = [0, 483163056664, 976705308108, 310722744609, 13624150839, 0, 0, 0] := by
  rw [show D2M8K2.u14541 = KTree.node D2M8K2.t14548 (nat_lit 31539515) (nat_lit 2750676357) (nat_lit 0) D2M8K2.t14549 from rfl, totK_node, tot14548, tot14549]
  decide +kernel

theorem arows14542 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14542 = true := by
  rw [show D2M8K2.u14542 = KTree.node D2M8K2.t14550 (nat_lit 31541122) (nat_lit 3879710192) (nat_lit 0) D2M8K2.t14551 from rfl, allE_node, rows14550, irow14542, rows14551]
  all_goals rfl

theorem atot14542 : totK PD2M8K2 D2M8K2.u14542 = [0, 152608652007, 768711671254, 699108170267, 92412430274, 1138244013, 0, 0] := by
  rw [show D2M8K2.u14542 = KTree.node D2M8K2.t14550 (nat_lit 31541122) (nat_lit 3879710192) (nat_lit 0) D2M8K2.t14551 from rfl, totK_node, tot14550, tot14551]
  decide +kernel

theorem arows14545 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14545 = true := by
  rw [show D2M8K2.u14545 = KTree.node D2M8K2.t14552 (nat_lit 31543631) (nat_lit 2604258749) (nat_lit 0) D2M8K2.t14553 from rfl, allE_node, rows14552, irow14545, rows14553]
  all_goals rfl

theorem atot14545 : totK PD2M8K2 D2M8K2.u14545 = [0, 336377250178, 923032386712, 515681154595, 45347419730, 0, 0, 0] := by
  rw [show D2M8K2.u14545 = KTree.node D2M8K2.t14552 (nat_lit 31543631) (nat_lit 2604258749) (nat_lit 0) D2M8K2.t14553 from rfl, totK_node, tot14552, tot14553]
  decide +kernel

theorem arows14546 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14546 = true := by
  rw [show D2M8K2.u14546 = KTree.node D2M8K2.t14554 (nat_lit 31550180) (nat_lit 3264296064) (nat_lit 0) D2M8K2.t14555 from rfl, allE_node, rows14554, irow14546, rows14555]
  all_goals rfl

theorem atot14546 : totK PD2M8K2 D2M8K2.u14546 = [0, 369406273565, 938306766242, 475959545879, 29375547852, 0, 0, 0] := by
  rw [show D2M8K2.u14546 = KTree.node D2M8K2.t14554 (nat_lit 31550180) (nat_lit 3264296064) (nat_lit 0) D2M8K2.t14555 from rfl, totK_node, tot14554, tot14555]
  decide +kernel

theorem arows14548 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14548 = true := by
  rw [show D2M8K2.u14548 = KTree.node D2M8K2.t14556 (nat_lit 31553422) (nat_lit 2718592556) (nat_lit 0) D2M8K2.t14557 from rfl, allE_node, rows14556, irow14548, rows14557]
  all_goals rfl

theorem atot14548 : totK PD2M8K2 D2M8K2.u14548 = [0, 366373821682, 940388199701, 450603281982, 24625985610, 0, 0, 0] := by
  rw [show D2M8K2.u14548 = KTree.node D2M8K2.t14556 (nat_lit 31553422) (nat_lit 2718592556) (nat_lit 0) D2M8K2.t14557 from rfl, totK_node, tot14556, tot14557]
  decide +kernel

theorem arows14549 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14549 = true := by
  rw [show D2M8K2.u14549 = KTree.node D2M8K2.t14558 (nat_lit 31554672) (nat_lit 3394198253) (nat_lit 0) D2M8K2.t14559 from rfl, allE_node, rows14558, irow14549, rows14559]
  all_goals rfl

theorem atot14549 : totK PD2M8K2 D2M8K2.u14549 = [0, 179801336674, 750498557088, 703880233679, 107058882773, 1095107716, 0, 0] := by
  rw [show D2M8K2.u14549 = KTree.node D2M8K2.t14558 (nat_lit 31554672) (nat_lit 3394198253) (nat_lit 0) D2M8K2.t14559 from rfl, totK_node, tot14558, tot14559]
  decide +kernel

theorem arows14554 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14554 = true := by
  rw [show D2M8K2.u14554 = KTree.node D2M8K2.t14560 (nat_lit 31560435) (nat_lit 973944561) (nat_lit 0) D2M8K2.t14561 from rfl, allE_node, rows14560, irow14554, rows14561]
  all_goals rfl

theorem atot14554 : totK PD2M8K2 D2M8K2.u14554 = [265595993963, 657507117544, 451461865633, 304608745755, 99101322038, 3882006667, 0, 0] := by
  rw [show D2M8K2.u14554 = KTree.node D2M8K2.t14560 (nat_lit 31560435) (nat_lit 973944561) (nat_lit 0) D2M8K2.t14561 from rfl, totK_node, tot14560, tot14561]
  decide +kernel

theorem arows14555 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14555 = true := by
  rw [show D2M8K2.u14555 = KTree.node D2M8K2.t14562 (nat_lit 31562006) (nat_lit 2575359603) (nat_lit 0) D2M8K2.t14563 from rfl, allE_node, rows14562, irow14555, rows14563]
  all_goals rfl

theorem atot14555 : totK PD2M8K2 D2M8K2.u14555 = [139001670435, 705561194657, 789362805329, 138524124860, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u14555 = KTree.node D2M8K2.t14562 (nat_lit 31562006) (nat_lit 2575359603) (nat_lit 0) D2M8K2.t14563 from rfl, totK_node, tot14562, tot14563]
  decide +kernel

theorem arows14557 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14557 = true := by
  rw [show D2M8K2.u14557 = KTree.node D2M8K2.t14564 (nat_lit 31564341) (nat_lit 1276407786) (nat_lit 0) D2M8K2.t14565 from rfl, allE_node, rows14564, irow14557, rows14565]
  all_goals rfl

theorem atot14557 : totK PD2M8K2 D2M8K2.u14557 = [329731927371, 894275822341, 571858686046, 56047175261, 0, 0, 0, 0] := by
  rw [show D2M8K2.u14557 = KTree.node D2M8K2.t14564 (nat_lit 31564341) (nat_lit 1276407786) (nat_lit 0) D2M8K2.t14565 from rfl, totK_node, tot14564, tot14565]
  decide +kernel

theorem arows14558 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14558 = true := by
  rw [show D2M8K2.u14558 = KTree.node D2M8K2.t14566 (nat_lit 31565878) (nat_lit 3399640141) (nat_lit 0) D2M8K2.t14567 from rfl, allE_node, rows14566, irow14558, rows14567]
  all_goals rfl

theorem atot14558 : totK PD2M8K2 D2M8K2.u14558 = [89930864070, 526810431622, 820766014059, 354697600203, 28048680602, 0, 0, 0] := by
  rw [show D2M8K2.u14558 = KTree.node D2M8K2.t14566 (nat_lit 31565878) (nat_lit 3399640141) (nat_lit 0) D2M8K2.t14567 from rfl, totK_node, tot14566, tot14567]
  decide +kernel

theorem arows14561 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14561 = true := by
  rw [show D2M8K2.u14561 = KTree.node D2M8K2.t14568 (nat_lit 31567194) (nat_lit 3703559877) (nat_lit 0) D2M8K2.t14569 from rfl, allE_node, rows14568, irow14561, rows14569]
  all_goals rfl

theorem atot14561 : totK PD2M8K2 D2M8K2.u14561 = [236972882048, 690507012894, 675191124264, 221382139316, 9355690997, 0, 0, 0] := by
  rw [show D2M8K2.u14561 = KTree.node D2M8K2.t14568 (nat_lit 31567194) (nat_lit 3703559877) (nat_lit 0) D2M8K2.t14569 from rfl, totK_node, tot14568, tot14569]
  decide +kernel

theorem arows14562 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14562 = true := by
  rw [show D2M8K2.u14562 = KTree.node D2M8K2.t14570 (nat_lit 31568959) (nat_lit 1803155940) (nat_lit 0) D2M8K2.t14571 from rfl, allE_node, rows14570, irow14562, rows14571]
  all_goals rfl

theorem atot14562 : totK PD2M8K2 D2M8K2.u14562 = [108444201513, 641836080018, 837893941538, 214185770689, 9469033438, 0, 0, 0] := by
  rw [show D2M8K2.u14562 = KTree.node D2M8K2.t14570 (nat_lit 31568959) (nat_lit 1803155940) (nat_lit 0) D2M8K2.t14571 from rfl, totK_node, tot14570, tot14571]
  decide +kernel

theorem arows14564 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14564 = true := by
  rw [show D2M8K2.u14564 = KTree.node D2M8K2.t14572 (nat_lit 31571067) (nat_lit 3684805238) (nat_lit 0) D2M8K2.t14573 from rfl, allE_node, rows14572, irow14564, rows14573]
  all_goals rfl

theorem atot14564 : totK PD2M8K2 D2M8K2.u14564 = [336723911503, 908225715508, 529637224182, 52423499420, 0, 0, 0, 0] := by
  rw [show D2M8K2.u14564 = KTree.node D2M8K2.t14572 (nat_lit 31571067) (nat_lit 3684805238) (nat_lit 0) D2M8K2.t14573 from rfl, totK_node, tot14572, tot14573]
  decide +kernel

theorem arows14565 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14565 = true := by
  rw [show D2M8K2.u14565 = KTree.node D2M8K2.t14574 (nat_lit 31572617) (nat_lit 1697496862) (nat_lit 0) D2M8K2.t14575 from rfl, allE_node, rows14574, irow14565, rows14575]
  all_goals rfl

theorem atot14565 : totK PD2M8K2 D2M8K2.u14565 = [89753051296, 573510498706, 868739413516, 251935709408, 10676274061, 0, 0, 0] := by
  rw [show D2M8K2.u14565 = KTree.node D2M8K2.t14574 (nat_lit 31572617) (nat_lit 1697496862) (nat_lit 0) D2M8K2.t14575 from rfl, totK_node, tot14574, tot14575]
  decide +kernel

theorem arows14569 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14569 = true := by
  rw [show D2M8K2.u14569 = KTree.node D2M8K2.t14576 (nat_lit 31577870) (nat_lit 3860381495) (nat_lit 0) D2M8K2.t14577 from rfl, allE_node, rows14576, irow14569, rows14577]
  all_goals rfl

theorem atot14569 : totK PD2M8K2 D2M8K2.u14569 = [330265526224, 861434566748, 556269704271, 90068405800, 2567510802, 0, 0, 0] := by
  rw [show D2M8K2.u14569 = KTree.node D2M8K2.t14576 (nat_lit 31577870) (nat_lit 3860381495) (nat_lit 0) D2M8K2.t14577 from rfl, totK_node, tot14576, tot14577]
  decide +kernel

theorem arows14570 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14570 = true := by
  rw [show D2M8K2.u14570 = KTree.node D2M8K2.t14578 (nat_lit 31579314) (nat_lit 3077325541) (nat_lit 0) D2M8K2.t14579 from rfl, allE_node, rows14578, irow14570, rows14579]
  all_goals rfl

theorem atot14570 : totK PD2M8K2 D2M8K2.u14570 = [112771130407, 645095559932, 842380679374, 205012007930, 4967996017, 0, 0, 0] := by
  rw [show D2M8K2.u14570 = KTree.node D2M8K2.t14578 (nat_lit 31579314) (nat_lit 3077325541) (nat_lit 0) D2M8K2.t14579 from rfl, totK_node, tot14578, tot14579]
  decide +kernel

theorem arows14572 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14572 = true := by
  rw [show D2M8K2.u14572 = KTree.node D2M8K2.t14580 (nat_lit 31580990) (nat_lit 2737765369) (nat_lit 0) D2M8K2.t14581 from rfl, allE_node, rows14580, irow14572, rows14581]
  all_goals rfl

theorem atot14572 : totK PD2M8K2 D2M8K2.u14572 = [0, 395625554208, 957567564474, 415870255572, 22416853141, 0, 0, 0] := by
  rw [show D2M8K2.u14572 = KTree.node D2M8K2.t14580 (nat_lit 31580990) (nat_lit 2737765369) (nat_lit 0) D2M8K2.t14581 from rfl, totK_node, tot14580, tot14581]
  decide +kernel

theorem arows14573 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14573 = true := by
  rw [show D2M8K2.u14573 = KTree.node D2M8K2.t14582 (nat_lit 31582591) (nat_lit 2298094699) (nat_lit 0) D2M8K2.t14583 from rfl, allE_node, rows14582, irow14573, rows14583]
  all_goals rfl

theorem atot14573 : totK PD2M8K2 D2M8K2.u14573 = [0, 164142508919, 749761427444, 738209459087, 101864389226, 1310285577, 0, 0] := by
  rw [show D2M8K2.u14573 = KTree.node D2M8K2.t14582 (nat_lit 31582591) (nat_lit 2298094699) (nat_lit 0) D2M8K2.t14583 from rfl, totK_node, tot14582, tot14583]
  decide +kernel

theorem arows14576 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14576 = true := by
  rw [show D2M8K2.u14576 = KTree.node D2M8K2.t14584 (nat_lit 31584954) (nat_lit 3553682206) (nat_lit 0) D2M8K2.t14585 from rfl, allE_node, rows14584, irow14576, rows14585]
  all_goals rfl

theorem atot14576 : totK PD2M8K2 D2M8K2.u14576 = [0, 287991553964, 855707926099, 628376283668, 58188445305, 0, 0, 0] := by
  rw [show D2M8K2.u14576 = KTree.node D2M8K2.t14584 (nat_lit 31584954) (nat_lit 3553682206) (nat_lit 0) D2M8K2.t14585 from rfl, totK_node, tot14584, tot14585]
  decide +kernel

theorem arows14577 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14577 = true := by
  rw [show D2M8K2.u14577 = KTree.node D2M8K2.t14586 (nat_lit 31587967) (nat_lit 2072614832) (nat_lit 0) D2M8K2.t14587 from rfl, allE_node, rows14586, irow14577, rows14587]
  all_goals rfl

theorem atot14577 : totK PD2M8K2 D2M8K2.u14577 = [0, 385522082830, 944505464750, 463522138240, 35545489770, 0, 0, 0] := by
  rw [show D2M8K2.u14577 = KTree.node D2M8K2.t14586 (nat_lit 31587967) (nat_lit 2072614832) (nat_lit 0) D2M8K2.t14587 from rfl, totK_node, tot14586, tot14587]
  decide +kernel

theorem arows14579 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14579 = true := by
  rw [show D2M8K2.u14579 = KTree.node D2M8K2.t14588 (nat_lit 31589762) (nat_lit 2958961048) (nat_lit 0) D2M8K2.t14589 from rfl, allE_node, rows14588, irow14579, rows14589]
  all_goals rfl

theorem atot14579 : totK PD2M8K2 D2M8K2.u14579 = [0, 96434399470, 643635285096, 861466250992, 181788262498, 4879840392, 0, 0] := by
  rw [show D2M8K2.u14579 = KTree.node D2M8K2.t14588 (nat_lit 31589762) (nat_lit 2958961048) (nat_lit 0) D2M8K2.t14589 from rfl, totK_node, tot14588, tot14589]
  decide +kernel

theorem arows14580 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14580 = true := by
  rw [show D2M8K2.u14580 = KTree.node D2M8K2.t14590 (nat_lit 31592182) (nat_lit 3488724157) (nat_lit 0) D2M8K2.t14591 from rfl, allE_node, rows14590, irow14580, rows14591]
  all_goals rfl

theorem atot14580 : totK PD2M8K2 D2M8K2.u14580 = [0, 386678889913, 933896927509, 452182732454, 33092845662, 0, 0, 0] := by
  rw [show D2M8K2.u14580 = KTree.node D2M8K2.t14590 (nat_lit 31592182) (nat_lit 3488724157) (nat_lit 0) D2M8K2.t14591 from rfl, totK_node, tot14590, tot14591]
  decide +kernel

theorem arows14588 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14588 = true := by
  rw [show D2M8K2.u14588 = KTree.node D2M8K2.t14592 (nat_lit 31593916) (nat_lit 2005835124) (nat_lit 0) D2M8K2.t14593 from rfl, allE_node, rows14592, irow14588, rows14593]
  all_goals rfl

theorem atot14588 : totK PD2M8K2 D2M8K2.u14588 = [0, 95125832362, 640469920445, 842601546775, 181850687706, 4931404646, 0, 0] := by
  rw [show D2M8K2.u14588 = KTree.node D2M8K2.t14592 (nat_lit 31593916) (nat_lit 2005835124) (nat_lit 0) D2M8K2.t14593 from rfl, totK_node, tot14592, tot14593]
  decide +kernel

theorem arows14589 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14589 = true := by
  rw [show D2M8K2.u14589 = KTree.node D2M8K2.t14594 (nat_lit 31598909) (nat_lit 2322193773) (nat_lit 0) D2M8K2.t14595 from rfl, allE_node, rows14594, irow14589, rows14595]
  all_goals rfl

theorem atot14589 : totK PD2M8K2 D2M8K2.u14589 = [0, 374305011815, 950085198158, 476589850516, 32628585273, 0, 0, 0] := by
  rw [show D2M8K2.u14589 = KTree.node D2M8K2.t14594 (nat_lit 31598909) (nat_lit 2322193773) (nat_lit 0) D2M8K2.t14595 from rfl, totK_node, tot14594, tot14595]
  decide +kernel

theorem arows14591 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14591 = true := by
  rw [show D2M8K2.u14591 = KTree.node D2M8K2.t14596 (nat_lit 31600556) (nat_lit 2104408552) (nat_lit 0) D2M8K2.t14597 from rfl, allE_node, rows14596, irow14591, rows14597]
  all_goals rfl

theorem atot14591 : totK PD2M8K2 D2M8K2.u14591 = [0, 0, 515798546783, 960536387966, 269661293567, 8424427256, 0, 0] := by
  rw [show D2M8K2.u14591 = KTree.node D2M8K2.t14596 (nat_lit 31600556) (nat_lit 2104408552) (nat_lit 0) D2M8K2.t14597 from rfl, totK_node, tot14596, tot14597]
  decide +kernel

theorem arows14592 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14592 = true := by
  rw [show D2M8K2.u14592 = KTree.node D2M8K2.t14598 (nat_lit 31602389) (nat_lit 2305339268) (nat_lit 0) D2M8K2.t14599 from rfl, allE_node, rows14598, irow14592, rows14599]
  all_goals rfl

theorem atot14592 : totK PD2M8K2 D2M8K2.u14592 = [0, 345344010572, 822070302533, 463582556415, 132097422152, 13326740810, 0, 0] := by
  rw [show D2M8K2.u14592 = KTree.node D2M8K2.t14598 (nat_lit 31602389) (nat_lit 2305339268) (nat_lit 0) D2M8K2.t14599 from rfl, totK_node, tot14598, tot14599]
  decide +kernel

theorem arows14595 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14595 = true := by
  rw [show D2M8K2.u14595 = KTree.node D2M8K2.t14600 (nat_lit 31603609) (nat_lit 1491400094) (nat_lit 0) D2M8K2.t14601 from rfl, allE_node, rows14600, irow14595, rows14601]
  all_goals rfl

theorem atot14595 : totK PD2M8K2 D2M8K2.u14595 = [0, 87765346930, 689706087052, 872819440929, 144409234084, 1369150432, 0, 0] := by
  rw [show D2M8K2.u14595 = KTree.node D2M8K2.t14600 (nat_lit 31603609) (nat_lit 1491400094) (nat_lit 0) D2M8K2.t14601 from rfl, totK_node, tot14600, tot14601]
  decide +kernel

theorem arows14596 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14596 = true := by
  rw [show D2M8K2.u14596 = KTree.node D2M8K2.t14602 (nat_lit 31609422) (nat_lit 2908071040) (nat_lit 0) D2M8K2.t14603 from rfl, allE_node, rows14602, irow14596, rows14603]
  all_goals rfl

theorem atot14596 : totK PD2M8K2 D2M8K2.u14596 = [0, 324922959855, 908520114657, 519275425550, 40120934592, 0, 0, 0] := by
  rw [show D2M8K2.u14596 = KTree.node D2M8K2.t14602 (nat_lit 31609422) (nat_lit 2908071040) (nat_lit 0) D2M8K2.t14603 from rfl, totK_node, tot14602, tot14603]
  decide +kernel

theorem arows14598 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14598 = true := by
  rw [show D2M8K2.u14598 = KTree.node D2M8K2.t14604 (nat_lit 31612050) (nat_lit 3418256644) (nat_lit 0) D2M8K2.t14605 from rfl, allE_node, rows14604, irow14598, rows14605]
  all_goals rfl

theorem atot14598 : totK PD2M8K2 D2M8K2.u14598 = [0, 215580929906, 753613494759, 718215505080, 116654591947, 1164319620, 0, 0] := by
  rw [show D2M8K2.u14598 = KTree.node D2M8K2.t14604 (nat_lit 31612050) (nat_lit 3418256644) (nat_lit 0) D2M8K2.t14605 from rfl, totK_node, tot14604, tot14605]
  decide +kernel

theorem arows14599 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14599 = true := by
  rw [show D2M8K2.u14599 = KTree.node D2M8K2.t14606 (nat_lit 31613562) (nat_lit 3918445402) (nat_lit 0) D2M8K2.t14607 from rfl, allE_node, rows14606, irow14599, rows14607]
  all_goals rfl

theorem atot14599 : totK PD2M8K2 D2M8K2.u14599 = [0, 207309883138, 768269561128, 692918422542, 110871814264, 1198073392, 0, 0] := by
  rw [show D2M8K2.u14599 = KTree.node D2M8K2.t14606 (nat_lit 31613562) (nat_lit 3918445402) (nat_lit 0) D2M8K2.t14607 from rfl, totK_node, tot14606, tot14607]
  decide +kernel

theorem arows14603 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14603 = true := by
  rw [show D2M8K2.u14603 = KTree.node D2M8K2.t14608 (nat_lit 31615251) (nat_lit 2802362748) (nat_lit 0) D2M8K2.t14609 from rfl, allE_node, rows14608, irow14603, rows14609]
  all_goals rfl

theorem atot14603 : totK PD2M8K2 D2M8K2.u14603 = [0, 175535075457, 643741970131, 725680794758, 218457715891, 11991925116, 0, 0] := by
  rw [show D2M8K2.u14603 = KTree.node D2M8K2.t14608 (nat_lit 31615251) (nat_lit 2802362748) (nat_lit 0) D2M8K2.t14609 from rfl, totK_node, tot14608, tot14609]
  decide +kernel

theorem arows14604 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14604 = true := by
  rw [show D2M8K2.u14604 = KTree.node D2M8K2.t14610 (nat_lit 31616741) (nat_lit 2326679395) (nat_lit 0) D2M8K2.t14611 from rfl, allE_node, rows14610, irow14604, rows14611]
  all_goals rfl

theorem atot14604 : totK PD2M8K2 D2M8K2.u14604 = [0, 202704941401, 764803065182, 688379003176, 97735014019, 1096505104, 0, 0] := by
  rw [show D2M8K2.u14604 = KTree.node D2M8K2.t14610 (nat_lit 31616741) (nat_lit 2326679395) (nat_lit 0) D2M8K2.t14611 from rfl, totK_node, tot14610, tot14611]
  decide +kernel

theorem arows14606 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14606 = true := by
  rw [show D2M8K2.u14606 = KTree.node D2M8K2.t14612 (nat_lit 31619108) (nat_lit 2722899603) (nat_lit 0) D2M8K2.t14613 from rfl, allE_node, rows14612, irow14606, rows14613]
  all_goals rfl

theorem atot14606 : totK PD2M8K2 D2M8K2.u14606 = [0, 247120707369, 772454847049, 651939089593, 122841861817, 3821179711, 0, 0] := by
  rw [show D2M8K2.u14606 = KTree.node D2M8K2.t14612 (nat_lit 31619108) (nat_lit 2722899603) (nat_lit 0) D2M8K2.t14613 from rfl, totK_node, tot14612, tot14613]
  decide +kernel

theorem arows14607 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14607 = true := by
  rw [show D2M8K2.u14607 = KTree.node D2M8K2.t14614 (nat_lit 31620673) (nat_lit 1573165124) (nat_lit 0) D2M8K2.t14615 from rfl, allE_node, rows14614, irow14607, rows14615]
  all_goals rfl

theorem atot14607 : totK PD2M8K2 D2M8K2.u14607 = [0, 169143655275, 731730588371, 770199497901, 137825589673, 1268739303, 0, 0] := by
  rw [show D2M8K2.u14607 = KTree.node D2M8K2.t14614 (nat_lit 31620673) (nat_lit 1573165124) (nat_lit 0) D2M8K2.t14615 from rfl, totK_node, tot14614, tot14615]
  decide +kernel

theorem arows14610 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14610 = true := by
  rw [show D2M8K2.u14610 = KTree.node D2M8K2.t14616 (nat_lit 31622505) (nat_lit 1893811968) (nat_lit 0) D2M8K2.t14617 from rfl, allE_node, rows14616, irow14610, rows14617]
  all_goals rfl

theorem atot14610 : totK PD2M8K2 D2M8K2.u14610 = [0, 0, 389946155455, 974430223219, 382125440325, 16190548789, 0, 0] := by
  rw [show D2M8K2.u14610 = KTree.node D2M8K2.t14616 (nat_lit 31622505) (nat_lit 1893811968) (nat_lit 0) D2M8K2.t14617 from rfl, totK_node, tot14616, tot14617]
  decide +kernel

theorem arows14611 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14611 = true := by
  rw [show D2M8K2.u14611 = KTree.node D2M8K2.t14618 (nat_lit 31624075) (nat_lit 1510074694) (nat_lit 0) D2M8K2.t14619 from rfl, allE_node, rows14618, irow14611, rows14619]
  all_goals rfl

theorem atot14611 : totK PD2M8K2 D2M8K2.u14611 = [0, 0, 169334178784, 755941638025, 665241115050, 98076133466, 1310517177, 0] := by
  rw [show D2M8K2.u14611 = KTree.node D2M8K2.t14618 (nat_lit 31624075) (nat_lit 1510074694) (nat_lit 0) D2M8K2.t14619 from rfl, totK_node, tot14618, tot14619]
  decide +kernel

theorem arows14613 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14613 = true := by
  rw [show D2M8K2.u14613 = KTree.node D2M8K2.t14620 (nat_lit 31630010) (nat_lit 3783782558) (nat_lit 0) D2M8K2.t14621 from rfl, allE_node, rows14620, irow14613, rows14621]
  all_goals rfl

theorem atot14613 : totK PD2M8K2 D2M8K2.u14613 = [0, 0, 394689673383, 942207540960, 383402802390, 21192540485, 0, 0] := by
  rw [show D2M8K2.u14613 = KTree.node D2M8K2.t14620 (nat_lit 31630010) (nat_lit 3783782558) (nat_lit 0) D2M8K2.t14621 from rfl, totK_node, tot14620, tot14621]
  decide +kernel

theorem arows14614 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14614 = true := by
  rw [show D2M8K2.u14614 = KTree.node D2M8K2.t14622 (nat_lit 31633859) (nat_lit 2682134698) (nat_lit 0) D2M8K2.t14623 from rfl, allE_node, rows14622, irow14614, rows14623]
  all_goals rfl

theorem atot14614 : totK PD2M8K2 D2M8K2.u14614 = [0, 0, 344214404294, 946067537877, 445148559211, 21566990440, 0, 0] := by
  rw [show D2M8K2.u14614 = KTree.node D2M8K2.t14622 (nat_lit 31633859) (nat_lit 2682134698) (nat_lit 0) D2M8K2.t14623 from rfl, totK_node, tot14622, tot14623]
  decide +kernel

theorem arows14619 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14619 = true := by
  rw [show D2M8K2.u14619 = KTree.node D2M8K2.t14624 (nat_lit 31637001) (nat_lit 1753499211) (nat_lit 0) D2M8K2.t14625 from rfl, allE_node, rows14624, irow14619, rows14625]
  all_goals rfl

theorem atot14619 : totK PD2M8K2 D2M8K2.u14619 = [0, 0, 375919242113, 948446998315, 390316336166, 19296539644, 0, 0] := by
  rw [show D2M8K2.u14619 = KTree.node D2M8K2.t14624 (nat_lit 31637001) (nat_lit 1753499211) (nat_lit 0) D2M8K2.t14625 from rfl, totK_node, tot14624, tot14625]
  decide +kernel

theorem arows14620 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14620 = true := by
  rw [show D2M8K2.u14620 = KTree.node D2M8K2.t14626 (nat_lit 31640589) (nat_lit 1186018999) (nat_lit 0) D2M8K2.t14627 from rfl, allE_node, rows14626, irow14620, rows14627]
  all_goals rfl

theorem atot14620 : totK PD2M8K2 D2M8K2.u14620 = [0, 57100535768, 490994154403, 911411170135, 339289743526, 15843124820, 0, 0] := by
  rw [show D2M8K2.u14620 = KTree.node D2M8K2.t14626 (nat_lit 31640589) (nat_lit 1186018999) (nat_lit 0) D2M8K2.t14627 from rfl, totK_node, tot14626, tot14627]
  decide +kernel

theorem arows14622 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14622 = true := by
  rw [show D2M8K2.u14622 = KTree.node D2M8K2.t14628 (nat_lit 31647541) (nat_lit 1196898910) (nat_lit 0) D2M8K2.t14629 from rfl, allE_node, rows14628, irow14622, rows14629]
  all_goals rfl

theorem atot14622 : totK PD2M8K2 D2M8K2.u14622 = [0, 365896817851, 934192028752, 497045973109, 39654862578, 0, 0, 0] := by
  rw [show D2M8K2.u14622 = KTree.node D2M8K2.t14628 (nat_lit 31647541) (nat_lit 1196898910) (nat_lit 0) D2M8K2.t14629 from rfl, totK_node, tot14628, tot14629]
  decide +kernel

theorem arows14623 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14623 = true := by
  rw [show D2M8K2.u14623 = KTree.node D2M8K2.t14630 (nat_lit 31648960) (nat_lit 3778141658) (nat_lit 0) D2M8K2.t14631 from rfl, allE_node, rows14630, irow14623, rows14631]
  all_goals rfl

theorem atot14623 : totK PD2M8K2 D2M8K2.u14623 = [0, 19474609260, 473653875360, 905308574398, 388248622959, 29329034908, 0, 0] := by
  rw [show D2M8K2.u14623 = KTree.node D2M8K2.t14630 (nat_lit 31648960) (nat_lit 3778141658) (nat_lit 0) D2M8K2.t14631 from rfl, totK_node, tot14630, tot14631]
  decide +kernel

theorem arows14626 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14626 = true := by
  rw [show D2M8K2.u14626 = KTree.node D2M8K2.t14632 (nat_lit 31650526) (nat_lit 3760555231) (nat_lit 0) D2M8K2.t14633 from rfl, allE_node, rows14632, irow14626, rows14633]
  all_goals rfl

theorem atot14626 : totK PD2M8K2 D2M8K2.u14626 = [0, 246049547677, 718472350074, 652021047929, 203966983638, 8170972732, 0, 0] := by
  rw [show D2M8K2.u14626 = KTree.node D2M8K2.t14632 (nat_lit 31650526) (nat_lit 3760555231) (nat_lit 0) D2M8K2.t14633 from rfl, totK_node, tot14632, tot14633]
  decide +kernel

theorem arows14627 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14627 = true := by
  rw [show D2M8K2.u14627 = KTree.node D2M8K2.t14634 (nat_lit 31652474) (nat_lit 4026875643) (nat_lit 0) D2M8K2.t14635 from rfl, allE_node, rows14634, irow14627, rows14635]
  all_goals rfl

theorem atot14627 : totK PD2M8K2 D2M8K2.u14627 = [0, 151529302158, 638016757423, 820528382691, 204302837901, 5370412161, 0, 0] := by
  rw [show D2M8K2.u14627 = KTree.node D2M8K2.t14634 (nat_lit 31652474) (nat_lit 4026875643) (nat_lit 0) D2M8K2.t14635 from rfl, totK_node, tot14634, tot14635]
  decide +kernel

theorem arows14629 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14629 = true := by
  rw [show D2M8K2.u14629 = KTree.node D2M8K2.t14636 (nat_lit 31654513) (nat_lit 1518378357) (nat_lit 0) D2M8K2.t14637 from rfl, allE_node, rows14636, irow14629, rows14637]
  all_goals rfl

theorem atot14629 : totK PD2M8K2 D2M8K2.u14629 = [0, 358557365833, 935574059819, 493645929522, 36985464046, 0, 0, 0] := by
  rw [show D2M8K2.u14629 = KTree.node D2M8K2.t14636 (nat_lit 31654513) (nat_lit 1518378357) (nat_lit 0) D2M8K2.t14637 from rfl, totK_node, tot14636, tot14637]
  decide +kernel

theorem arows14630 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14630 = true := by
  rw [show D2M8K2.u14630 = KTree.node D2M8K2.t14638 (nat_lit 31656200) (nat_lit 3890540344) (nat_lit 0) D2M8K2.t14639 from rfl, allE_node, rows14638, irow14630, rows14639]
  all_goals rfl

theorem atot14630 : totK PD2M8K2 D2M8K2.u14630 = [0, 0, 487772481013, 968502481173, 302295271703, 13183084702, 0, 0] := by
  rw [show D2M8K2.u14630 = KTree.node D2M8K2.t14638 (nat_lit 31656200) (nat_lit 3890540344) (nat_lit 0) D2M8K2.t14639 from rfl, totK_node, tot14638, tot14639]
  decide +kernel

theorem arows14634 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14634 = true := by
  rw [show D2M8K2.u14634 = KTree.node D2M8K2.t14640 (nat_lit 31657666) (nat_lit 3900027304) (nat_lit 0) D2M8K2.t14641 from rfl, allE_node, rows14640, irow14634, rows14641]
  all_goals rfl

theorem atot14634 : totK PD2M8K2 D2M8K2.u14634 = [0, 382314415935, 918191309453, 477375279157, 42929182957, 0, 0, 0] := by
  rw [show D2M8K2.u14634 = KTree.node D2M8K2.t14640 (nat_lit 31657666) (nat_lit 3900027304) (nat_lit 0) D2M8K2.t14641 from rfl, totK_node, tot14640, tot14641]
  decide +kernel

theorem arows14635 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14635 = true := by
  rw [show D2M8K2.u14635 = KTree.node D2M8K2.t14642 (nat_lit 31659685) (nat_lit 1020072114) (nat_lit 0) D2M8K2.t14643 from rfl, allE_node, rows14642, irow14635, rows14643]
  all_goals rfl

theorem atot14635 : totK PD2M8K2 D2M8K2.u14635 = [0, 128545043771, 712451591060, 813715854625, 157301781008, 3880716147, 0, 0] := by
  rw [show D2M8K2.u14635 = KTree.node D2M8K2.t14642 (nat_lit 31659685) (nat_lit 1020072114) (nat_lit 0) D2M8K2.t14643 from rfl, totK_node, tot14642, tot14643]
  decide +kernel

theorem arows14637 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14637 = true := by
  rw [show D2M8K2.u14637 = KTree.node D2M8K2.t14644 (nat_lit 31661396) (nat_lit 3533783215) (nat_lit 0) D2M8K2.t14645 from rfl, allE_node, rows14644, irow14637, rows14645]
  all_goals rfl

theorem atot14637 : totK PD2M8K2 D2M8K2.u14637 = [0, 286826679711, 877597073305, 609579032436, 60424447055, 0, 0, 0] := by
  rw [show D2M8K2.u14637 = KTree.node D2M8K2.t14644 (nat_lit 31661396) (nat_lit 3533783215) (nat_lit 0) D2M8K2.t14645 from rfl, totK_node, tot14644, tot14645]
  decide +kernel

theorem arows14638 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14638 = true := by
  rw [show D2M8K2.u14638 = KTree.node D2M8K2.t14646 (nat_lit 31663111) (nat_lit 2358456255) (nat_lit 0) D2M8K2.t14647 from rfl, allE_node, rows14646, irow14638, rows14647]
  all_goals rfl

theorem atot14638 : totK PD2M8K2 D2M8K2.u14638 = [0, 71689983455, 458602844367, 871925364724, 362207523574, 17826494640, 0, 0] := by
  rw [show D2M8K2.u14638 = KTree.node D2M8K2.t14646 (nat_lit 31663111) (nat_lit 2358456255) (nat_lit 0) D2M8K2.t14647 from rfl, totK_node, tot14646, tot14647]
  decide +kernel

theorem arows14641 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14641 = true := by
  rw [show D2M8K2.u14641 = KTree.node D2M8K2.t14648 (nat_lit 31727187) (nat_lit 2469982535) (nat_lit 0) D2M8K2.t14649 from rfl, allE_node, rows14648, irow14641, rows14649]
  all_goals rfl

theorem atot14641 : totK PD2M8K2 D2M8K2.u14641 = [0, 340347373597, 935679758351, 470261133403, 22385530424, 0, 0, 0] := by
  rw [show D2M8K2.u14641 = KTree.node D2M8K2.t14648 (nat_lit 31727187) (nat_lit 2469982535) (nat_lit 0) D2M8K2.t14649 from rfl, totK_node, tot14648, tot14649]
  decide +kernel

theorem arows14642 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14642 = true := by
  rw [show D2M8K2.u14642 = KTree.node D2M8K2.t14650 (nat_lit 31728998) (nat_lit 3719333098) (nat_lit 0) D2M8K2.t14651 from rfl, allE_node, rows14650, irow14642, rows14651]
  all_goals rfl

theorem atot14642 : totK PD2M8K2 D2M8K2.u14642 = [0, 97501213428, 651728864294, 898617105035, 151651043216, 1369150432, 0, 0] := by
  rw [show D2M8K2.u14642 = KTree.node D2M8K2.t14650 (nat_lit 31728998) (nat_lit 3719333098) (nat_lit 0) D2M8K2.t14651 from rfl, totK_node, tot14650, tot14651]
  decide +kernel

theorem arows14644 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14644 = true := by
  rw [show D2M8K2.u14644 = KTree.node D2M8K2.t14652 (nat_lit 31730757) (nat_lit 1502490556) (nat_lit 0) D2M8K2.t14653 from rfl, allE_node, rows14652, irow14644, rows14653]
  all_goals rfl

theorem atot14644 : totK PD2M8K2 D2M8K2.u14644 = [0, 325836699752, 907928434109, 533138371429, 48489813637, 0, 0, 0] := by
  rw [show D2M8K2.u14644 = KTree.node D2M8K2.t14652 (nat_lit 31730757) (nat_lit 1502490556) (nat_lit 0) D2M8K2.t14653 from rfl, totK_node, tot14652, tot14653]
  decide +kernel

theorem arows14645 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14645 = true := by
  rw [show D2M8K2.u14645 = KTree.node D2M8K2.t14654 (nat_lit 31732281) (nat_lit 1170377951) (nat_lit 0) D2M8K2.t14655 from rfl, allE_node, rows14654, irow14645, rows14655]
  all_goals rfl

theorem atot14645 : totK PD2M8K2 D2M8K2.u14645 = [0, 0, 355393639505, 949302276177, 444829392867, 25003318349, 0, 0] := by
  rw [show D2M8K2.u14645 = KTree.node D2M8K2.t14654 (nat_lit 31732281) (nat_lit 1170377951) (nat_lit 0) D2M8K2.t14655 from rfl, totK_node, tot14654, tot14655]
  decide +kernel

theorem arows14651 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14651 = true := by
  rw [show D2M8K2.u14651 = KTree.node D2M8K2.t14656 (nat_lit 31737003) (nat_lit 3670195276) (nat_lit 0) D2M8K2.t14657 from rfl, allE_node, rows14656, irow14651, rows14657]
  all_goals rfl

theorem atot14651 : totK PD2M8K2 D2M8K2.u14651 = [0, 356600519989, 911886363306, 484647172116, 72987960784, 5147854625, 0, 0] := by
  rw [show D2M8K2.u14651 = KTree.node D2M8K2.t14656 (nat_lit 31737003) (nat_lit 3670195276) (nat_lit 0) D2M8K2.t14657 from rfl, totK_node, tot14656, tot14657]
  decide +kernel

theorem arows14652 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14652 = true := by
  rw [show D2M8K2.u14652 = KTree.node D2M8K2.t14658 (nat_lit 31738517) (nat_lit 1303478558) (nat_lit 0) D2M8K2.t14659 from rfl, allE_node, rows14658, irow14652, rows14659]
  all_goals rfl

theorem atot14652 : totK PD2M8K2 D2M8K2.u14652 = [0, 88945508586, 582590066730, 867423358309, 249872430027, 10680993762, 0, 0] := by
  rw [show D2M8K2.u14652 = KTree.node D2M8K2.t14658 (nat_lit 31738517) (nat_lit 1303478558) (nat_lit 0) D2M8K2.t14659 from rfl, totK_node, tot14658, tot14659]
  decide +kernel

theorem arows14654 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14654 = true := by
  rw [show D2M8K2.u14654 = KTree.node D2M8K2.t14660 (nat_lit 31740284) (nat_lit 3364050675) (nat_lit 0) D2M8K2.t14661 from rfl, allE_node, rows14660, irow14654, rows14661]
  all_goals rfl

theorem atot14654 : totK PD2M8K2 D2M8K2.u14654 = [0, 308777449997, 820633225134, 558771077032, 94190559048, 2569691499, 0, 0] := by
  rw [show D2M8K2.u14654 = KTree.node D2M8K2.t14660 (nat_lit 31740284) (nat_lit 3364050675) (nat_lit 0) D2M8K2.t14661 from rfl, totK_node, tot14660, tot14661]
  decide +kernel

theorem arows14655 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14655 = true := by
  rw [show D2M8K2.u14655 = KTree.node D2M8K2.t14662 (nat_lit 31741880) (nat_lit 3823380090) (nat_lit 0) D2M8K2.t14663 from rfl, allE_node, rows14662, irow14655, rows14663]
  all_goals rfl

theorem atot14655 : totK PD2M8K2 D2M8K2.u14655 = [0, 90004739926, 681346680626, 867105759753, 135255789505, 1096505104, 0, 0] := by
  rw [show D2M8K2.u14655 = KTree.node D2M8K2.t14662 (nat_lit 31741880) (nat_lit 3823380090) (nat_lit 0) D2M8K2.t14663 from rfl, totK_node, tot14662, tot14663]
  decide +kernel

theorem arows14658 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14658 = true := by
  rw [show D2M8K2.u14658 = KTree.node D2M8K2.t14664 (nat_lit 31743874) (nat_lit 3939470882) (nat_lit 0) D2M8K2.t14665 from rfl, allE_node, rows14664, irow14658, rows14665]
  all_goals rfl

theorem atot14658 : totK PD2M8K2 D2M8K2.u14658 = [0, 344719216367, 856305444465, 516441180338, 89892567221, 3884009855, 0, 0] := by
  rw [show D2M8K2.u14658 = KTree.node D2M8K2.t14664 (nat_lit 31743874) (nat_lit 3939470882) (nat_lit 0) D2M8K2.t14665 from rfl, totK_node, tot14664, tot14665]
  decide +kernel

theorem arows14659 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14659 = true := by
  rw [show D2M8K2.u14659 = KTree.node D2M8K2.t14666 (nat_lit 31745427) (nat_lit 3684479650) (nat_lit 0) D2M8K2.t14667 from rfl, allE_node, rows14666, irow14659, rows14667]
  all_goals rfl

theorem atot14659 : totK PD2M8K2 D2M8K2.u14659 = [0, 78886334381, 566508293471, 884133807484, 245262413906, 5952729029, 0, 0] := by
  rw [show D2M8K2.u14659 = KTree.node D2M8K2.t14666 (nat_lit 31745427) (nat_lit 3684479650) (nat_lit 0) D2M8K2.t14667 from rfl, totK_node, tot14666, tot14667]
  decide +kernel

theorem arows14661 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14661 = true := by
  rw [show D2M8K2.u14661 = KTree.node D2M8K2.t14668 (nat_lit 31747412) (nat_lit 3197525914) (nat_lit 0) D2M8K2.t14669 from rfl, allE_node, rows14668, irow14661, rows14669]
  all_goals rfl

theorem atot14661 : totK PD2M8K2 D2M8K2.u14661 = [0, 0, 402788305244, 938127892276, 379999252303, 22229609707, 0, 0] := by
  rw [show D2M8K2.u14661 = KTree.node D2M8K2.t14668 (nat_lit 31747412) (nat_lit 3197525914) (nat_lit 0) D2M8K2.t14669 from rfl, totK_node, tot14668, tot14669]
  decide +kernel

theorem arows14662 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14662 = true := by
  rw [show D2M8K2.u14662 = KTree.node D2M8K2.t14670 (nat_lit 31748738) (nat_lit 866262236) (nat_lit 0) D2M8K2.t14671 from rfl, allE_node, rows14670, irow14662, rows14671]
  all_goals rfl

theorem atot14662 : totK PD2M8K2 D2M8K2.u14662 = [0, 0, 104893635585, 721312852541, 763220843426, 109086847504, 1217496766, 0] := by
  rw [show D2M8K2.u14662 = KTree.node D2M8K2.t14670 (nat_lit 31748738) (nat_lit 866262236) (nat_lit 0) D2M8K2.t14671 from rfl, totK_node, tot14670, tot14671]
  decide +kernel

theorem arows14666 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14666 = true := by
  rw [show D2M8K2.u14666 = KTree.node D2M8K2.t14672 (nat_lit 31751314) (nat_lit 3977929664) (nat_lit 0) D2M8K2.t14673 from rfl, allE_node, rows14672, irow14666, rows14673]
  all_goals rfl

theorem atot14666 : totK PD2M8K2 D2M8K2.u14666 = [0, 0, 397564557917, 961074608389, 421922711592, 26845270112, 0, 0] := by
  rw [show D2M8K2.u14666 = KTree.node D2M8K2.t14672 (nat_lit 31751314) (nat_lit 3977929664) (nat_lit 0) D2M8K2.t14673 from rfl, totK_node, tot14672, tot14673]
  decide +kernel

theorem arows14667 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14667 = true := by
  rw [show D2M8K2.u14667 = KTree.node D2M8K2.t14674 (nat_lit 31758074) (nat_lit 4226979444) (nat_lit 0) D2M8K2.t14675 from rfl, allE_node, rows14674, irow14667, rows14675]
  all_goals rfl

theorem atot14667 : totK PD2M8K2 D2M8K2.u14667 = [0, 0, 387580306336, 938310942274, 443953139944, 32530581118, 0, 0] := by
  rw [show D2M8K2.u14667 = KTree.node D2M8K2.t14674 (nat_lit 31758074) (nat_lit 4226979444) (nat_lit 0) D2M8K2.t14675 from rfl, totK_node, tot14674, tot14675]
  decide +kernel

theorem arows14669 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14669 = true := by
  rw [show D2M8K2.u14669 = KTree.node D2M8K2.t14676 (nat_lit 31759330) (nat_lit 4106897673) (nat_lit 0) D2M8K2.t14677 from rfl, allE_node, rows14676, irow14669, rows14677]
  all_goals rfl

theorem atot14669 : totK PD2M8K2 D2M8K2.u14669 = [0, 0, 51735240357, 532584720020, 863185961911, 267282665971, 13105450397, 0] := by
  rw [show D2M8K2.u14669 = KTree.node D2M8K2.t14676 (nat_lit 31759330) (nat_lit 4106897673) (nat_lit 0) D2M8K2.t14677 from rfl, totK_node, tot14676, tot14677]
  decide +kernel

theorem arows14670 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14670 = true := by
  rw [show D2M8K2.u14670 = KTree.node D2M8K2.t14678 (nat_lit 31761163) (nat_lit 1742869688) (nat_lit 0) D2M8K2.t14679 from rfl, allE_node, rows14678, irow14670, rows14679]
  all_goals rfl

theorem atot14670 : totK PD2M8K2 D2M8K2.u14670 = [0, 0, 355585757391, 904668153763, 450566474322, 36698394048, 0, 0] := by
  rw [show D2M8K2.u14670 = KTree.node D2M8K2.t14678 (nat_lit 31761163) (nat_lit 1742869688) (nat_lit 0) D2M8K2.t14679 from rfl, totK_node, tot14678, tot14679]
  decide +kernel

theorem arows14673 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14673 = true := by
  rw [show D2M8K2.u14673 = KTree.node D2M8K2.t14680 (nat_lit 31763044) (nat_lit 2977405677) (nat_lit 0) D2M8K2.t14681 from rfl, allE_node, rows14680, irow14673, rows14681]
  all_goals rfl

theorem atot14673 : totK PD2M8K2 D2M8K2.u14673 = [0, 0, 121379034097, 655277909305, 738658825783, 151968773352, 4630915822, 0] := by
  rw [show D2M8K2.u14673 = KTree.node D2M8K2.t14680 (nat_lit 31763044) (nat_lit 2977405677) (nat_lit 0) D2M8K2.t14681 from rfl, totK_node, tot14680, tot14681]
  decide +kernel

theorem arows14674 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14674 = true := by
  rw [show D2M8K2.u14674 = KTree.node D2M8K2.t14682 (nat_lit 31765057) (nat_lit 1394417455) (nat_lit 0) D2M8K2.t14683 from rfl, allE_node, rows14682, irow14674, rows14683]
  all_goals rfl

theorem atot14674 : totK PD2M8K2 D2M8K2.u14674 = [0, 71990150170, 440150296377, 859606859631, 410641787313, 26454145974, 0, 0] := by
  rw [show D2M8K2.u14674 = KTree.node D2M8K2.t14682 (nat_lit 31765057) (nat_lit 1394417455) (nat_lit 0) D2M8K2.t14683 from rfl, totK_node, tot14682, tot14683]
  decide +kernel

theorem arows14676 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14676 = true := by
  rw [show D2M8K2.u14676 = KTree.node D2M8K2.t14684 (nat_lit 31768644) (nat_lit 3062633191) (nat_lit 0) D2M8K2.t14685 from rfl, allE_node, rows14684, irow14676, rows14685]
  all_goals rfl

theorem atot14676 : totK PD2M8K2 D2M8K2.u14676 = [0, 322656666298, 909109655589, 501068539454, 32683683263, 0, 0, 0] := by
  rw [show D2M8K2.u14676 = KTree.node D2M8K2.t14684 (nat_lit 31768644) (nat_lit 3062633191) (nat_lit 0) D2M8K2.t14685 from rfl, totK_node, tot14684, tot14685]
  decide +kernel

theorem arows14677 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14677 = true := by
  rw [show D2M8K2.u14677 = KTree.node D2M8K2.t14686 (nat_lit 31770512) (nat_lit 3788156863) (nat_lit 0) D2M8K2.t14687 from rfl, allE_node, rows14686, irow14677, rows14687]
  all_goals rfl

theorem atot14677 : totK PD2M8K2 D2M8K2.u14677 = [0, 147472534373, 678282179682, 832894080220, 140612289586, 1310517177, 0, 0] := by
  rw [show D2M8K2.u14677 = KTree.node D2M8K2.t14686 (nat_lit 31770512) (nat_lit 3788156863) (nat_lit 0) D2M8K2.t14687 from rfl, totK_node, tot14686, tot14687]
  decide +kernel

theorem arows14682 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14682 = true := by
  rw [show D2M8K2.u14682 = KTree.node D2M8K2.t14688 (nat_lit 31772312) (nat_lit 3642913123) (nat_lit 0) D2M8K2.t14689 from rfl, allE_node, rows14688, irow14682, rows14689]
  all_goals rfl

theorem atot14682 : totK PD2M8K2 D2M8K2.u14682 = [0, 259615796675, 828875168298, 606008814093, 120587973204, 8332571741, 0, 0] := by
  rw [show D2M8K2.u14682 = KTree.node D2M8K2.t14688 (nat_lit 31772312) (nat_lit 3642913123) (nat_lit 0) D2M8K2.t14689 from rfl, totK_node, tot14688, tot14689]
  decide +kernel

theorem arows14683 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14683 = true := by
  rw [show D2M8K2.u14683 = KTree.node D2M8K2.t14690 (nat_lit 31774004) (nat_lit 3703361260) (nat_lit 0) D2M8K2.t14691 from rfl, allE_node, rows14690, irow14683, rows14691]
  all_goals rfl

theorem atot14683 : totK PD2M8K2 D2M8K2.u14683 = [0, 142949208276, 615504225708, 790086870527, 258323140017, 6733760932, 0, 0] := by
  rw [show D2M8K2.u14683 = KTree.node D2M8K2.t14690 (nat_lit 31774004) (nat_lit 3703361260) (nat_lit 0) D2M8K2.t14691 from rfl, totK_node, tot14690, tot14691]
  decide +kernel

theorem arows14685 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14685 = true := by
  rw [show D2M8K2.u14685 = KTree.node D2M8K2.t14692 (nat_lit 31779132) (nat_lit 3047320257) (nat_lit 0) D2M8K2.t14693 from rfl, allE_node, rows14692, irow14685, rows14693]
  all_goals rfl

theorem atot14685 : totK PD2M8K2 D2M8K2.u14685 = [0, 277733619576, 866845560841, 606962515597, 59440837339, 0, 0, 0] := by
  rw [show D2M8K2.u14685 = KTree.node D2M8K2.t14692 (nat_lit 31779132) (nat_lit 3047320257) (nat_lit 0) D2M8K2.t14693 from rfl, totK_node, tot14692, tot14693]
  decide +kernel

theorem arows14686 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14686 = true := by
  rw [show D2M8K2.u14686 = KTree.node D2M8K2.t14694 (nat_lit 31780838) (nat_lit 4113698729) (nat_lit 0) D2M8K2.t14695 from rfl, allE_node, rows14694, irow14686, rows14695]
  all_goals rfl

theorem atot14686 : totK PD2M8K2 D2M8K2.u14686 = [0, 83652690359, 540320276637, 843743731040, 282292365811, 13250685261, 0, 0] := by
  rw [show D2M8K2.u14686 = KTree.node D2M8K2.t14694 (nat_lit 31780838) (nat_lit 4113698729) (nat_lit 0) D2M8K2.t14695 from rfl, totK_node, tot14694, tot14695]
  decide +kernel

theorem arows14689 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14689 = true := by
  rw [show D2M8K2.u14689 = KTree.node D2M8K2.t14696 (nat_lit 31782253) (nat_lit 1382286413) (nat_lit 0) D2M8K2.t14697 from rfl, allE_node, rows14696, irow14689, rows14697]
  all_goals rfl

theorem atot14689 : totK PD2M8K2 D2M8K2.u14689 = [0, 340115668443, 910841355192, 525710571273, 43544978512, 0, 0, 0] := by
  rw [show D2M8K2.u14689 = KTree.node D2M8K2.t14696 (nat_lit 31782253) (nat_lit 1382286413) (nat_lit 0) D2M8K2.t14697 from rfl, totK_node, tot14696, tot14697]
  decide +kernel

theorem arows14690 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14690 = true := by
  rw [show D2M8K2.u14690 = KTree.node D2M8K2.t14698 (nat_lit 31784080) (nat_lit 2767715103) (nat_lit 0) D2M8K2.t14699 from rfl, allE_node, rows14698, irow14690, rows14699]
  all_goals rfl

theorem atot14690 : totK PD2M8K2 D2M8K2.u14690 = [0, 0, 490008402289, 1006959195374, 275701145043, 6350335412, 0, 0] := by
  rw [show D2M8K2.u14690 = KTree.node D2M8K2.t14698 (nat_lit 31784080) (nat_lit 2767715103) (nat_lit 0) D2M8K2.t14699 from rfl, totK_node, tot14698, tot14699]
  decide +kernel

theorem arows14692 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14692 = true := by
  rw [show D2M8K2.u14692 = KTree.node D2M8K2.t14700 (nat_lit 31789540) (nat_lit 3782317994) (nat_lit 0) D2M8K2.t14701 from rfl, allE_node, rows14700, irow14692, rows14701]
  all_goals rfl

theorem atot14692 : totK PD2M8K2 D2M8K2.u14692 = [0, 0, 286336274085, 846863270325, 498772292753, 62329031200, 1138244013, 0] := by
  rw [show D2M8K2.u14692 = KTree.node D2M8K2.t14700 (nat_lit 31789540) (nat_lit 3782317994) (nat_lit 0) D2M8K2.t14701 from rfl, totK_node, tot14700, tot14701]
  decide +kernel

theorem arows14693 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14693 = true := by
  rw [show D2M8K2.u14693 = KTree.node D2M8K2.t14702 (nat_lit 31792170) (nat_lit 3748722671) (nat_lit 0) D2M8K2.t14703 from rfl, allE_node, rows14702, irow14693, rows14703]
  all_goals rfl

theorem atot14693 : totK PD2M8K2 D2M8K2.u14693 = [0, 0, 296641792948, 879738045041, 561381085783, 38594620660, 0, 0] := by
  rw [show D2M8K2.u14693 = KTree.node D2M8K2.t14702 (nat_lit 31792170) (nat_lit 3748722671) (nat_lit 0) D2M8K2.t14703 from rfl, totK_node, tot14702, tot14703]
  decide +kernel

theorem arows14697 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14697 = true := by
  rw [show D2M8K2.u14697 = KTree.node D2M8K2.t14704 (nat_lit 31799008) (nat_lit 2575786906) (nat_lit 0) D2M8K2.t14705 from rfl, allE_node, rows14704, irow14697, rows14705]
  all_goals rfl

theorem atot14697 : totK PD2M8K2 D2M8K2.u14697 = [0, 0, 405915144292, 960114724001, 406533411833, 21176782452, 0, 0] := by
  rw [show D2M8K2.u14697 = KTree.node D2M8K2.t14704 (nat_lit 31799008) (nat_lit 2575786906) (nat_lit 0) D2M8K2.t14705 from rfl, totK_node, tot14704, tot14705]
  decide +kernel

theorem arows14698 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14698 = true := by
  rw [show D2M8K2.u14698 = KTree.node D2M8K2.t14706 (nat_lit 31802262) (nat_lit 3627406331) (nat_lit 0) D2M8K2.t14707 from rfl, allE_node, rows14706, irow14698, rows14707]
  all_goals rfl

theorem atot14698 : totK PD2M8K2 D2M8K2.u14698 = [0, 0, 357034070156, 937847196219, 424210821441, 20534589923, 0, 0] := by
  rw [show D2M8K2.u14698 = KTree.node D2M8K2.t14706 (nat_lit 31802262) (nat_lit 3627406331) (nat_lit 0) D2M8K2.t14707 from rfl, totK_node, tot14706, tot14707]
  decide +kernel

theorem arows14700 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14700 = true := by
  rw [show D2M8K2.u14700 = KTree.node D2M8K2.t14708 (nat_lit 31803860) (nat_lit 3257634743) (nat_lit 0) D2M8K2.t14709 from rfl, allE_node, rows14708, irow14700, rows14709]
  all_goals rfl

theorem atot14700 : totK PD2M8K2 D2M8K2.u14700 = [0, 0, 178467773161, 776760717583, 671454427323, 90024787331, 1095107716, 0] := by
  rw [show D2M8K2.u14700 = KTree.node D2M8K2.t14708 (nat_lit 31803860) (nat_lit 3257634743) (nat_lit 0) D2M8K2.t14709 from rfl, totK_node, tot14708, tot14709]
  decide +kernel

theorem arows14701 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14701 = true := by
  rw [show D2M8K2.u14701 = KTree.node D2M8K2.t14710 (nat_lit 31809664) (nat_lit 3774374584) (nat_lit 0) D2M8K2.t14711 from rfl, allE_node, rows14710, irow14701, rows14711]
  all_goals rfl

theorem atot14701 : totK PD2M8K2 D2M8K2.u14701 = [0, 318670901333, 761440420680, 385148613360, 215320203497, 76590533551, 3819176523, 0] := by
  rw [show D2M8K2.u14701 = KTree.node D2M8K2.t14710 (nat_lit 31809664) (nat_lit 3774374584) (nat_lit 0) D2M8K2.t14711 from rfl, totK_node, tot14710, tot14711]
  decide +kernel

theorem arows14704 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14704 = true := by
  rw [show D2M8K2.u14704 = KTree.node D2M8K2.t14712 (nat_lit 31810970) (nat_lit 2675491240) (nat_lit 0) D2M8K2.t14713 from rfl, allE_node, rows14712, irow14704, rows14713]
  all_goals rfl

theorem atot14704 : totK PD2M8K2 D2M8K2.u14704 = [0, 88990076640, 680524980569, 879751986812, 138174265662, 1369150432, 0, 0] := by
  rw [show D2M8K2.u14704 = KTree.node D2M8K2.t14712 (nat_lit 31810970) (nat_lit 2675491240) (nat_lit 0) D2M8K2.t14713 from rfl, totK_node, tot14712, tot14713]
  decide +kernel

theorem arows14705 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14705 = true := by
  rw [show D2M8K2.u14705 = KTree.node D2M8K2.t14714 (nat_lit 31813321) (nat_lit 1321689095) (nat_lit 0) D2M8K2.t14715 from rfl, allE_node, rows14714, irow14705, rows14715]
  all_goals rfl

theorem atot14705 : totK PD2M8K2 D2M8K2.u14705 = [0, 381543393910, 917641248960, 493297005875, 45873217428, 0, 0, 0] := by
  rw [show D2M8K2.u14705 = KTree.node D2M8K2.t14714 (nat_lit 31813321) (nat_lit 1321689095) (nat_lit 0) D2M8K2.t14715 from rfl, totK_node, tot14714, tot14715]
  decide +kernel

theorem arows14707 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14707 = true := by
  rw [show D2M8K2.u14707 = KTree.node D2M8K2.t14716 (nat_lit 31814825) (nat_lit 1813608217) (nat_lit 0) D2M8K2.t14717 from rfl, allE_node, rows14716, irow14707, rows14717]
  all_goals rfl

theorem atot14707 : totK PD2M8K2 D2M8K2.u14707 = [0, 37815634106, 487885284888, 895162477149, 370276301779, 24726425107, 0, 0] := by
  rw [show D2M8K2.u14707 = KTree.node D2M8K2.t14716 (nat_lit 31814825) (nat_lit 1813608217) (nat_lit 0) D2M8K2.t14717 from rfl, totK_node, tot14716, tot14717]
  decide +kernel

theorem arows14708 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14708 = true := by
  rw [show D2M8K2.u14708 = KTree.node D2M8K2.t14718 (nat_lit 31816204) (nat_lit 3817458740) (nat_lit 0) D2M8K2.t14719 from rfl, allE_node, rows14718, irow14708, rows14719]
  all_goals rfl

theorem atot14708 : totK PD2M8K2 D2M8K2.u14708 = [0, 258828680308, 742164604901, 621042214050, 183305916738, 8078182869, 0, 0] := by
  rw [show D2M8K2.u14708 = KTree.node D2M8K2.t14718 (nat_lit 31816204) (nat_lit 3817458740) (nat_lit 0) D2M8K2.t14719 from rfl, totK_node, tot14718, tot14719]
  decide +kernel

theorem arows14715 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14715 = true := by
  rw [show D2M8K2.u14715 = KTree.node D2M8K2.t14720 (nat_lit 31818021) (nat_lit 1165593132) (nat_lit 0) D2M8K2.t14721 from rfl, allE_node, rows14720, irow14715, rows14721]
  all_goals rfl

theorem atot14715 : totK PD2M8K2 D2M8K2.u14715 = [0, 136123282252, 640673851896, 834534795509, 197716218547, 5172807878, 0, 0] := by
  rw [show D2M8K2.u14715 = KTree.node D2M8K2.t14720 (nat_lit 31818021) (nat_lit 1165593132) (nat_lit 0) D2M8K2.t14721 from rfl, totK_node, tot14720, tot14721]
  decide +kernel

theorem arows14716 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14716 = true := by
  rw [show D2M8K2.u14716 = KTree.node D2M8K2.t14722 (nat_lit 31820352) (nat_lit 3458981170) (nat_lit 0) D2M8K2.t14723 from rfl, allE_node, rows14722, irow14716, rows14723]
  all_goals rfl

theorem atot14716 : totK PD2M8K2 D2M8K2.u14716 = [0, 375266110795, 939198390960, 470164812243, 35138255537, 0, 0, 0] := by
  rw [show D2M8K2.u14716 = KTree.node D2M8K2.t14722 (nat_lit 31820352) (nat_lit 3458981170) (nat_lit 0) D2M8K2.t14723 from rfl, totK_node, tot14722, tot14723]
  decide +kernel

theorem arows14718 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14718 = true := by
  rw [show D2M8K2.u14718 = KTree.node D2M8K2.t14724 (nat_lit 31822025) (nat_lit 1033820048) (nat_lit 0) D2M8K2.t14725 from rfl, allE_node, rows14724, irow14718, rows14725]
  all_goals rfl

theorem atot14718 : totK PD2M8K2 D2M8K2.u14718 = [0, 0, 491943815718, 968876616826, 301164182046, 13183098110, 0, 0] := by
  rw [show D2M8K2.u14718 = KTree.node D2M8K2.t14724 (nat_lit 31822025) (nat_lit 1033820048) (nat_lit 0) D2M8K2.t14725 from rfl, totK_node, tot14724, tot14725]
  decide +kernel

theorem arows14719 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14719 = true := by
  rw [show D2M8K2.u14719 = KTree.node D2M8K2.t14726 (nat_lit 31826870) (nat_lit 3943137699) (nat_lit 0) D2M8K2.t14727 from rfl, allE_node, rows14726, irow14719, rows14727]
  all_goals rfl

theorem atot14719 : totK PD2M8K2 D2M8K2.u14719 = [0, 366744729367, 920890743206, 500680426937, 44838892476, 0, 0, 0] := by
  rw [show D2M8K2.u14719 = KTree.node D2M8K2.t14726 (nat_lit 31826870) (nat_lit 3943137699) (nat_lit 0) D2M8K2.t14727 from rfl, totK_node, tot14726, tot14727]
  decide +kernel

theorem arows14722 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14722 = true := by
  rw [show D2M8K2.u14722 = KTree.node D2M8K2.t14728 (nat_lit 31828378) (nat_lit 3950404598) (nat_lit 0) D2M8K2.t14729 from rfl, allE_node, rows14728, irow14722, rows14729]
  all_goals rfl

theorem atot14722 : totK PD2M8K2 D2M8K2.u14722 = [0, 75883481715, 569693973907, 893077706710, 257059491970, 5967036603, 0, 0] := by
  rw [show D2M8K2.u14722 = KTree.node D2M8K2.t14728 (nat_lit 31828378) (nat_lit 3950404598) (nat_lit 0) D2M8K2.t14729 from rfl, totK_node, tot14728, tot14729]
  decide +kernel

theorem arows14723 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14723 = true := by
  rw [show D2M8K2.u14723 = KTree.node D2M8K2.t14730 (nat_lit 32348406) (nat_lit 3691479539) (nat_lit 0) D2M8K2.t14731 from rfl, allE_node, rows14730, irow14723, rows14731]
  all_goals rfl

theorem atot14723 : totK PD2M8K2 D2M8K2.u14723 = [266170613056, 674197414080, 408186337130, 282510784902, 156551161189, 14967743524, 0, 0] := by
  rw [show D2M8K2.u14723 = KTree.node D2M8K2.t14730 (nat_lit 32348406) (nat_lit 3691479539) (nat_lit 0) D2M8K2.t14731 from rfl, totK_node, tot14730, tot14731]
  decide +kernel

theorem arows14725 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14725 = true := by
  rw [show D2M8K2.u14725 = KTree.node D2M8K2.t14732 (nat_lit 32349910) (nat_lit 3502656495) (nat_lit 0) D2M8K2.t14733 from rfl, allE_node, rows14732, irow14725, rows14733]
  all_goals rfl

theorem atot14725 : totK PD2M8K2 D2M8K2.u14725 = [169543068513, 733579615963, 768873763095, 128980289048, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u14725 = KTree.node D2M8K2.t14732 (nat_lit 32349910) (nat_lit 3502656495) (nat_lit 0) D2M8K2.t14733 from rfl, totK_node, tot14732, tot14733]
  decide +kernel

theorem arows14726 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14726 = true := by
  rw [show D2M8K2.u14726 = KTree.node D2M8K2.t14734 (nat_lit 32355472) (nat_lit 3408622960) (nat_lit 0) D2M8K2.t14735 from rfl, allE_node, rows14734, irow14726, rows14735]
  all_goals rfl

theorem atot14726 : totK PD2M8K2 D2M8K2.u14726 = [319665712363, 863668312590, 566870086597, 59861801447, 0, 0, 0, 0] := by
  rw [show D2M8K2.u14726 = KTree.node D2M8K2.t14734 (nat_lit 32355472) (nat_lit 3408622960) (nat_lit 0) D2M8K2.t14735 from rfl, totK_node, tot14734, tot14735]
  decide +kernel

theorem arows14730 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14730 = true := by
  rw [show D2M8K2.u14730 = KTree.node D2M8K2.t14736 (nat_lit 32356957) (nat_lit 1164319620) (nat_lit 0) D2M8K2.t14737 from rfl, allE_node, rows14736, irow14730, rows14737]
  all_goals rfl

theorem atot14730 : totK PD2M8K2 D2M8K2.u14730 = [87773917060, 621734499043, 841391957119, 219710364628, 9587713104, 0, 0, 0] := by
  rw [show D2M8K2.u14730 = KTree.node D2M8K2.t14736 (nat_lit 32356957) (nat_lit 1164319620) (nat_lit 0) D2M8K2.t14737 from rfl, totK_node, tot14736, tot14737]
  decide +kernel

theorem arows14731 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14731 = true := by
  rw [show D2M8K2.u14731 = KTree.node D2M8K2.t14738 (nat_lit 32358888) (nat_lit 2908418158) (nat_lit 0) D2M8K2.t14739 from rfl, allE_node, rows14738, irow14731, rows14739]
  all_goals rfl

theorem atot14731 : totK PD2M8K2 D2M8K2.u14731 = [288629079953, 799928514114, 587320367221, 113456656193, 3462014130, 0, 0, 0] := by
  rw [show D2M8K2.u14731 = KTree.node D2M8K2.t14738 (nat_lit 32358888) (nat_lit 2908418158) (nat_lit 0) D2M8K2.t14739 from rfl, totK_node, tot14738, tot14739]
  decide +kernel

theorem arows14733 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14733 = true := by
  rw [show D2M8K2.u14733 = KTree.node D2M8K2.t14740 (nat_lit 32360376) (nat_lit 3616749085) (nat_lit 0) D2M8K2.t14741 from rfl, allE_node, rows14740, irow14733, rows14741]
  all_goals rfl

theorem atot14733 : totK PD2M8K2 D2M8K2.u14733 = [122982374721, 634742942772, 799614380759, 216710026907, 9668735432, 0, 0, 0] := by
  rw [show D2M8K2.u14733 = KTree.node D2M8K2.t14740 (nat_lit 32360376) (nat_lit 3616749085) (nat_lit 0) D2M8K2.t14741 from rfl, totK_node, tot14740, tot14741]
  decide +kernel

theorem arows14734 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14734 = true := by
  rw [show D2M8K2.u14734 = KTree.node D2M8K2.t14742 (nat_lit 32362227) (nat_lit 1056790164) (nat_lit 0) D2M8K2.t14743 from rfl, allE_node, rows14742, irow14734, rows14743]
  all_goals rfl

theorem atot14734 : totK PD2M8K2 D2M8K2.u14734 = [264335134822, 776027383056, 600420590243, 119086913639, 3581949829, 0, 0, 0] := by
  rw [show D2M8K2.u14734 = KTree.node D2M8K2.t14742 (nat_lit 32362227) (nat_lit 1056790164) (nat_lit 0) D2M8K2.t14743 from rfl, totK_node, tot14742, tot14743]
  decide +kernel

theorem arows14737 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14737 = true := by
  rw [show D2M8K2.u14737 = KTree.node D2M8K2.t14744 (nat_lit 32364430) (nat_lit 3748529722) (nat_lit 0) D2M8K2.t14745 from rfl, allE_node, rows14744, irow14737, rows14745]
  all_goals rfl

theorem atot14737 : totK PD2M8K2 D2M8K2.u14737 = [141352609408, 677775208658, 773532462264, 169186394544, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u14737 = KTree.node D2M8K2.t14744 (nat_lit 32364430) (nat_lit 3748529722) (nat_lit 0) D2M8K2.t14745 from rfl, totK_node, tot14744, tot14745]
  decide +kernel

theorem arows14738 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14738 = true := by
  rw [show D2M8K2.u14738 = KTree.node D2M8K2.t14746 (nat_lit 32366304) (nat_lit 3691789053) (nat_lit 0) D2M8K2.t14747 from rfl, allE_node, rows14746, irow14738, rows14747]
  all_goals rfl

theorem atot14738 : totK PD2M8K2 D2M8K2.u14738 = [340406636637, 908711592633, 528268577070, 46511898202, 0, 0, 0, 0] := by
  rw [show D2M8K2.u14738 = KTree.node D2M8K2.t14746 (nat_lit 32366304) (nat_lit 3691789053) (nat_lit 0) D2M8K2.t14747 from rfl, totK_node, tot14746, tot14747]
  decide +kernel

theorem arows14740 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14740 = true := by
  rw [show D2M8K2.u14740 = KTree.node D2M8K2.t14748 (nat_lit 32367918) (nat_lit 2522233501) (nat_lit 0) D2M8K2.t14749 from rfl, allE_node, rows14748, irow14740, rows14749]
  all_goals rfl

theorem atot14740 : totK PD2M8K2 D2M8K2.u14740 = [0, 425717422887, 979047666895, 364325173085, 12440031250, 0, 0, 0] := by
  rw [show D2M8K2.u14740 = KTree.node D2M8K2.t14748 (nat_lit 32367918) (nat_lit 2522233501) (nat_lit 0) D2M8K2.t14749 from rfl, totK_node, tot14748, tot14749]
  decide +kernel

theorem arows14741 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14741 = true := by
  rw [show D2M8K2.u14741 = KTree.node D2M8K2.t14750 (nat_lit 32369738) (nat_lit 3612099086) (nat_lit 0) D2M8K2.t14751 from rfl, allE_node, rows14750, irow14741, rows14751]
  all_goals rfl

theorem atot14741 : totK PD2M8K2 D2M8K2.u14741 = [0, 367489001305, 925995186297, 433262575314, 31425809120, 0, 0, 0] := by
  rw [show D2M8K2.u14741 = KTree.node D2M8K2.t14750 (nat_lit 32369738) (nat_lit 3612099086) (nat_lit 0) D2M8K2.t14751 from rfl, totK_node, tot14750, tot14751]
  decide +kernel

theorem arows14746 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14746 = true := by
  rw [show D2M8K2.u14746 = KTree.node D2M8K2.t14752 (nat_lit 32371262) (nat_lit 2363526365) (nat_lit 0) D2M8K2.t14753 from rfl, allE_node, rows14752, irow14746, rows14753]
  all_goals rfl

theorem atot14746 : totK PD2M8K2 D2M8K2.u14746 = [0, 118049763478, 696582390191, 784109178273, 142668472581, 1369150432, 0, 0] := by
  rw [show D2M8K2.u14746 = KTree.node D2M8K2.t14752 (nat_lit 32371262) (nat_lit 2363526365) (nat_lit 0) D2M8K2.t14753 from rfl, totK_node, tot14752, tot14753]
  decide +kernel

theorem arows14747 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14747 = true := by
  rw [show D2M8K2.u14747 = KTree.node D2M8K2.t14754 (nat_lit 32376560) (nat_lit 3445523729) (nat_lit 0) D2M8K2.t14755 from rfl, allE_node, rows14754, irow14747, rows14755]
  all_goals rfl

theorem atot14747 : totK PD2M8K2 D2M8K2.u14747 = [0, 352890936473, 945376696047, 456465900642, 21410140740, 0, 0, 0] := by
  rw [show D2M8K2.u14747 = KTree.node D2M8K2.t14754 (nat_lit 32376560) (nat_lit 3445523729) (nat_lit 0) D2M8K2.t14755 from rfl, totK_node, tot14754, tot14755]
  decide +kernel

theorem arows14749 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14749 = true := by
  rw [show D2M8K2.u14749 = KTree.node D2M8K2.t14756 (nat_lit 32380208) (nat_lit 3779522820) (nat_lit 0) D2M8K2.t14757 from rfl, allE_node, rows14756, irow14749, rows14757]
  all_goals rfl

theorem atot14749 : totK PD2M8K2 D2M8K2.u14749 = [0, 391641442806, 948039906032, 428028099151, 22629014691, 0, 0, 0] := by
  rw [show D2M8K2.u14749 = KTree.node D2M8K2.t14756 (nat_lit 32380208) (nat_lit 3779522820) (nat_lit 0) D2M8K2.t14757 from rfl, totK_node, tot14756, tot14757]
  decide +kernel

theorem arows14750 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14750 = true := by
  rw [show D2M8K2.u14750 = KTree.node D2M8K2.t14758 (nat_lit 32383452) (nat_lit 3141604827) (nat_lit 0) D2M8K2.t14759 from rfl, allE_node, rows14758, irow14750, rows14759]
  all_goals rfl

theorem atot14750 : totK PD2M8K2 D2M8K2.u14750 = [0, 338953843748, 929256280747, 459497743295, 28119288251, 0, 0, 0] := by
  rw [show D2M8K2.u14750 = KTree.node D2M8K2.t14758 (nat_lit 32383452) (nat_lit 3141604827) (nat_lit 0) D2M8K2.t14759 from rfl, totK_node, tot14758, tot14759]
  decide +kernel

theorem arows14753 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14753 = true := by
  rw [show D2M8K2.u14753 = KTree.node D2M8K2.t14760 (nat_lit 32386805) (nat_lit 2401304114) (nat_lit 0) D2M8K2.t14761 from rfl, allE_node, rows14760, irow14753, rows14761]
  all_goals rfl

theorem atot14753 : totK PD2M8K2 D2M8K2.u14753 = [0, 407705958600, 955146372473, 427393461112, 19081906151, 0, 0, 0] := by
  rw [show D2M8K2.u14753 = KTree.node D2M8K2.t14760 (nat_lit 32386805) (nat_lit 2401304114) (nat_lit 0) D2M8K2.t14761 from rfl, totK_node, tot14760, tot14761]
  decide +kernel

theorem arows14754 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14754 = true := by
  rw [show D2M8K2.u14754 = KTree.node D2M8K2.t14762 (nat_lit 32393716) (nat_lit 4069852912) (nat_lit 0) D2M8K2.t14763 from rfl, allE_node, rows14762, irow14754, rows14763]
  all_goals rfl

theorem atot14754 : totK PD2M8K2 D2M8K2.u14754 = [321352686989, 791085297353, 556346523627, 162036526944, 13468148062, 0, 0, 0] := by
  rw [show D2M8K2.u14754 = KTree.node D2M8K2.t14762 (nat_lit 32393716) (nat_lit 4069852912) (nat_lit 0) D2M8K2.t14763 from rfl, totK_node, tot14762, tot14763]
  decide +kernel

theorem arows14756 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14756 = true := by
  rw [show D2M8K2.u14756 = KTree.node D2M8K2.t14764 (nat_lit 32395214) (nat_lit 3882570931) (nat_lit 0) D2M8K2.t14765 from rfl, allE_node, rows14764, irow14756, rows14765]
  all_goals rfl

theorem atot14756 : totK PD2M8K2 D2M8K2.u14756 = [122978065129, 620419735623, 771449429002, 295224930374, 25373788367, 0, 0, 0] := by
  rw [show D2M8K2.u14756 = KTree.node D2M8K2.t14764 (nat_lit 32395214) (nat_lit 3882570931) (nat_lit 0) D2M8K2.t14765 from rfl, totK_node, tot14764, tot14765]
  decide +kernel

theorem arows14757 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14757 = true := by
  rw [show D2M8K2.u14757 = KTree.node D2M8K2.t14766 (nat_lit 32396448) (nat_lit 2346083621) (nat_lit 0) D2M8K2.t14767 from rfl, allE_node, rows14766, irow14757, rows14767]
  all_goals rfl

theorem atot14757 : totK PD2M8K2 D2M8K2.u14757 = [157388839447, 588755590330, 772582852466, 294758407628, 12235609738, 0, 0, 0] := by
  rw [show D2M8K2.u14757 = KTree.node D2M8K2.t14766 (nat_lit 32396448) (nat_lit 2346083621) (nat_lit 0) D2M8K2.t14767 from rfl, totK_node, tot14766, tot14767]
  decide +kernel

theorem arows14761 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14761 = true := by
  rw [show D2M8K2.u14761 = KTree.node D2M8K2.t14768 (nat_lit 32398002) (nat_lit 2594755363) (nat_lit 0) D2M8K2.t14769 from rfl, allE_node, rows14768, irow14761, rows14769]
  all_goals rfl

theorem atot14761 : totK PD2M8K2 D2M8K2.u14761 = [257277526497, 805387487422, 638844415032, 102608851199, 1163840124, 0, 0, 0] := by
  rw [show D2M8K2.u14761 = KTree.node D2M8K2.t14768 (nat_lit 32398002) (nat_lit 2594755363) (nat_lit 0) D2M8K2.t14769 from rfl, totK_node, tot14768, tot14769]
  decide +kernel

theorem arows14762 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14762 = true := by
  rw [show D2M8K2.u14762 = KTree.node D2M8K2.t14770 (nat_lit 32399730) (nat_lit 2485444968) (nat_lit 0) D2M8K2.t14771 from rfl, allE_node, rows14770, irow14762, rows14771]
  all_goals rfl

theorem atot14762 : totK PD2M8K2 D2M8K2.u14762 = [157475862588, 644028675542, 768635030670, 221999937947, 11739479327, 0, 0, 0] := by
  rw [show D2M8K2.u14762 = KTree.node D2M8K2.t14770 (nat_lit 32399730) (nat_lit 2485444968) (nat_lit 0) D2M8K2.t14771 from rfl, totK_node, tot14770, tot14771]
  decide +kernel

theorem arows14764 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14764 = true := by
  rw [show D2M8K2.u14764 = KTree.node D2M8K2.t14772 (nat_lit 32401399) (nat_lit 2260203730) (nat_lit 0) D2M8K2.t14773 from rfl, allE_node, rows14772, irow14764, rows14773]
  all_goals rfl

theorem atot14764 : totK PD2M8K2 D2M8K2.u14764 = [257439096293, 810012476408, 639893874008, 101086427782, 1197396724, 0, 0, 0] := by
  rw [show D2M8K2.u14764 = KTree.node D2M8K2.t14772 (nat_lit 32401399) (nat_lit 2260203730) (nat_lit 0) D2M8K2.t14773 from rfl, totK_node, tot14772, tot14773]
  decide +kernel

theorem arows14765 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14765 = true := by
  rw [show D2M8K2.u14765 = KTree.node D2M8K2.t14774 (nat_lit 32403123) (nat_lit 2315216514) (nat_lit 0) D2M8K2.t14775 from rfl, allE_node, rows14774, irow14765, rows14775]
  all_goals rfl

theorem atot14765 : totK PD2M8K2 D2M8K2.u14765 = [140780261206, 602234202274, 818568478666, 240595613227, 11881883078, 0, 0, 0] := by
  rw [show D2M8K2.u14765 = KTree.node D2M8K2.t14774 (nat_lit 32403123) (nat_lit 2315216514) (nat_lit 0) D2M8K2.t14775 from rfl, totK_node, tot14774, tot14775]
  decide +kernel

theorem arows14768 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14768 = true := by
  rw [show D2M8K2.u14768 = KTree.node D2M8K2.t14776 (nat_lit 32404724) (nat_lit 3706580909) (nat_lit 0) D2M8K2.t14777 from rfl, allE_node, rows14776, irow14768, rows14777]
  all_goals rfl

theorem atot14768 : totK PD2M8K2 D2M8K2.u14768 = [186770637862, 825855582982, 730644559112, 85636090530, 0, 0, 0, 0] := by
  rw [show D2M8K2.u14768 = KTree.node D2M8K2.t14776 (nat_lit 32404724) (nat_lit 3706580909) (nat_lit 0) D2M8K2.t14777 from rfl, totK_node, tot14776, tot14777]
  decide +kernel

theorem arows14769 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14769 = true := by
  rw [show D2M8K2.u14769 = KTree.node D2M8K2.t14778 (nat_lit 32407401) (nat_lit 1680645636) (nat_lit 0) D2M8K2.t14779 from rfl, allE_node, rows14778, irow14769, rows14779]
  all_goals rfl

theorem atot14769 : totK PD2M8K2 D2M8K2.u14769 = [336728116587, 843842790877, 547891344964, 92814094669, 2739859532, 0, 0, 0] := by
  rw [show D2M8K2.u14769 = KTree.node D2M8K2.t14778 (nat_lit 32407401) (nat_lit 1680645636) (nat_lit 0) D2M8K2.t14779 from rfl, totK_node, tot14778, tot14779]
  decide +kernel

theorem arows14771 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14771 = true := by
  rw [show D2M8K2.u14771 = KTree.node D2M8K2.t14780 (nat_lit 32408867) (nat_lit 2324359503) (nat_lit 0) D2M8K2.t14781 from rfl, allE_node, rows14780, irow14771, rows14781]
  all_goals rfl

theorem atot14771 : totK PD2M8K2 D2M8K2.u14771 = [92999530293, 632510200596, 862650391561, 216933667956, 4961529011, 0, 0, 0] := by
  rw [show D2M8K2.u14771 = KTree.node D2M8K2.t14780 (nat_lit 32408867) (nat_lit 2324359503) (nat_lit 0) D2M8K2.t14781 from rfl, totK_node, tot14780, tot14781]
  decide +kernel

theorem arows14772 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14772 = true := by
  rw [show D2M8K2.u14772 = KTree.node D2M8K2.t14782 (nat_lit 32414246) (nat_lit 4060571057) (nat_lit 0) D2M8K2.t14783 from rfl, allE_node, rows14782, irow14772, rows14783]
  all_goals rfl

theorem atot14772 : totK PD2M8K2 D2M8K2.u14772 = [0, 354870341575, 915393560517, 505887182943, 45539324426, 0, 0, 0] := by
  rw [show D2M8K2.u14772 = KTree.node D2M8K2.t14782 (nat_lit 32414246) (nat_lit 4060571057) (nat_lit 0) D2M8K2.t14783 from rfl, totK_node, tot14782, tot14783]
  decide +kernel

theorem arows14778 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14778 = true := by
  rw [show D2M8K2.u14778 = KTree.node D2M8K2.t14784 (nat_lit 32415439) (nat_lit 2205373273) (nat_lit 0) D2M8K2.t14785 from rfl, allE_node, rows14784, irow14778, rows14785]
  all_goals rfl

theorem atot14778 : totK PD2M8K2 D2M8K2.u14778 = [0, 176933040480, 732435814797, 694380220426, 204189135516, 21385604922, 0, 0] := by
  rw [show D2M8K2.u14778 = KTree.node D2M8K2.t14784 (nat_lit 32415439) (nat_lit 2205373273) (nat_lit 0) D2M8K2.t14785 from rfl, totK_node, tot14784, tot14785]
  decide +kernel

theorem arows14779 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14779 = true := by
  rw [show D2M8K2.u14779 = KTree.node D2M8K2.t14786 (nat_lit 32416931) (nat_lit 1156438177) (nat_lit 0) D2M8K2.t14787 from rfl, allE_node, rows14786, irow14779, rows14787]
  all_goals rfl

theorem atot14779 : totK PD2M8K2 D2M8K2.u14779 = [0, 117006550469, 495519285986, 797064162706, 345310000597, 15536268932, 0, 0] := by
  rw [show D2M8K2.u14779 = KTree.node D2M8K2.t14786 (nat_lit 32416931) (nat_lit 1156438177) (nat_lit 0) D2M8K2.t14787 from rfl, totK_node, tot14786, tot14787]
  decide +kernel

theorem arows14781 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14781 = true := by
  rw [show D2M8K2.u14781 = KTree.node D2M8K2.t14788 (nat_lit 32418479) (nat_lit 1988001829) (nat_lit 0) D2M8K2.t14789 from rfl, allE_node, rows14788, irow14781, rows14789]
  all_goals rfl

theorem atot14781 : totK PD2M8K2 D2M8K2.u14781 = [0, 292785030171, 890035547403, 575913829927, 49145676513, 0, 0, 0] := by
  rw [show D2M8K2.u14781 = KTree.node D2M8K2.t14788 (nat_lit 32418479) (nat_lit 1988001829) (nat_lit 0) D2M8K2.t14789 from rfl, totK_node, tot14788, tot14789]
  decide +kernel

theorem arows14782 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14782 = true := by
  rw [show D2M8K2.u14782 = KTree.node D2M8K2.t14790 (nat_lit 32420337) (nat_lit 1488980014) (nat_lit 0) D2M8K2.t14791 from rfl, allE_node, rows14790, irow14782, rows14791]
  all_goals rfl

theorem atot14782 : totK PD2M8K2 D2M8K2.u14782 = [0, 157064894120, 664462314996, 779932693412, 193875560259, 5159868635, 0, 0] := by
  rw [show D2M8K2.u14782 = KTree.node D2M8K2.t14790 (nat_lit 32420337) (nat_lit 1488980014) (nat_lit 0) D2M8K2.t14791 from rfl, totK_node, tot14790, tot14791]
  decide +kernel

theorem arows14785 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14785 = true := by
  rw [show D2M8K2.u14785 = KTree.node D2M8K2.t14792 (nat_lit 32422042) (nat_lit 2053720417) (nat_lit 0) D2M8K2.t14793 from rfl, allE_node, rows14792, irow14785, rows14793]
  all_goals rfl

theorem atot14785 : totK PD2M8K2 D2M8K2.u14785 = [0, 256780675779, 863589151825, 628346359241, 66029838435, 0, 0, 0] := by
  rw [show D2M8K2.u14785 = KTree.node D2M8K2.t14792 (nat_lit 32422042) (nat_lit 2053720417) (nat_lit 0) D2M8K2.t14793 from rfl, totK_node, tot14792, tot14793]
  decide +kernel

theorem arows14786 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14786 = true := by
  rw [show D2M8K2.u14786 = KTree.node D2M8K2.t14794 (nat_lit 32423942) (nat_lit 4112680829) (nat_lit 0) D2M8K2.t14795 from rfl, allE_node, rows14794, irow14786, rows14795]
  all_goals rfl

theorem atot14786 : totK PD2M8K2 D2M8K2.u14786 = [0, 171473275786, 639910711121, 783212960354, 203657925591, 5218872685, 0, 0] := by
  rw [show D2M8K2.u14786 = KTree.node D2M8K2.t14794 (nat_lit 32423942) (nat_lit 4112680829) (nat_lit 0) D2M8K2.t14795 from rfl, totK_node, tot14794, tot14795]
  decide +kernel

theorem arows14788 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14788 = true := by
  rw [show D2M8K2.u14788 = KTree.node D2M8K2.t14796 (nat_lit 32425596) (nat_lit 2602914785) (nat_lit 0) D2M8K2.t14797 from rfl, allE_node, rows14796, irow14788, rows14797]
  all_goals rfl

theorem atot14788 : totK PD2M8K2 D2M8K2.u14788 = [0, 154859269859, 788582861304, 780398670192, 92588801343, 0, 0, 0] := by
  rw [show D2M8K2.u14788 = KTree.node D2M8K2.t14796 (nat_lit 32425596) (nat_lit 2602914785) (nat_lit 0) D2M8K2.t14797 from rfl, totK_node, tot14796, tot14797]
  decide +kernel

theorem arows14789 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14789 = true := by
  rw [show D2M8K2.u14789 = KTree.node D2M8K2.t14798 (nat_lit 32428207) (nat_lit 2215943935) (nat_lit 0) D2M8K2.t14799 from rfl, allE_node, rows14798, irow14789, rows14799]
  all_goals rfl

theorem atot14789 : totK PD2M8K2 D2M8K2.u14789 = [0, 342547576089, 865373822873, 529677970380, 84388138827, 1415142070, 0, 0] := by
  rw [show D2M8K2.u14789 = KTree.node D2M8K2.t14798 (nat_lit 32428207) (nat_lit 2215943935) (nat_lit 0) D2M8K2.t14799 from rfl, totK_node, tot14798, tot14799]
  decide +kernel

theorem arows14793 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14793 = true := by
  rw [show D2M8K2.u14793 = KTree.node D2M8K2.t14800 (nat_lit 32429990) (nat_lit 4113132171) (nat_lit 0) D2M8K2.t14801 from rfl, allE_node, rows14800, irow14793, rows14801]
  all_goals rfl

theorem atot14793 : totK PD2M8K2 D2M8K2.u14793 = [0, 81621031138, 648835283808, 875622213485, 195725455313, 2484078857, 0, 0] := by
  rw [show D2M8K2.u14793 = KTree.node D2M8K2.t14800 (nat_lit 32429990) (nat_lit 4113132171) (nat_lit 0) D2M8K2.t14801 from rfl, totK_node, tot14800, tot14801]
  decide +kernel

theorem arows14794 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14794 = true := by
  rw [show D2M8K2.u14794 = KTree.node D2M8K2.t14802 (nat_lit 32431851) (nat_lit 3660870313) (nat_lit 0) D2M8K2.t14803 from rfl, allE_node, rows14802, irow14794, rows14803]
  all_goals rfl

theorem atot14794 : totK PD2M8K2 D2M8K2.u14794 = [337985661236, 821831049011, 385102662404, 115304888581, 90042241549, 6818291842, 0, 0] := by
  rw [show D2M8K2.u14794 = KTree.node D2M8K2.t14802 (nat_lit 32431851) (nat_lit 3660870313) (nat_lit 0) D2M8K2.t14803 from rfl, totK_node, tot14802, tot14803]
  decide +kernel

theorem arows14796 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14796 = true := by
  rw [show D2M8K2.u14796 = KTree.node D2M8K2.t14804 (nat_lit 32433452) (nat_lit 3093399477) (nat_lit 0) D2M8K2.t14805 from rfl, allE_node, rows14804, irow14796, rows14805]
  all_goals rfl

theorem atot14796 : totK PD2M8K2 D2M8K2.u14796 = [109934480062, 679508187845, 863590623884, 152894227096, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u14796 = KTree.node D2M8K2.t14804 (nat_lit 32433452) (nat_lit 3093399477) (nat_lit 0) D2M8K2.t14805 from rfl, totK_node, tot14804, tot14805]
  decide +kernel

theorem arows14797 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14797 = true := by
  rw [show D2M8K2.u14797 = KTree.node D2M8K2.t14806 (nat_lit 32435503) (nat_lit 2437784313) (nat_lit 0) D2M8K2.t14807 from rfl, allE_node, rows14806, irow14797, rows14807]
  all_goals rfl

theorem atot14797 : totK PD2M8K2 D2M8K2.u14797 = [377865443749, 935951478213, 482291984446, 39916438325, 0, 0, 0, 0] := by
  rw [show D2M8K2.u14797 = KTree.node D2M8K2.t14806 (nat_lit 32435503) (nat_lit 2437784313) (nat_lit 0) D2M8K2.t14807 from rfl, totK_node, tot14806, tot14807]
  decide +kernel

theorem arows14800 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14800 = true := by
  rw [show D2M8K2.u14800 = KTree.node D2M8K2.t14808 (nat_lit 32436985) (nat_lit 1363912447) (nat_lit 0) D2M8K2.t14809 from rfl, allE_node, rows14808, irow14800, rows14809]
  all_goals rfl

theorem atot14800 : totK PD2M8K2 D2M8K2.u14800 = [0, 409041388333, 945611515574, 428806541810, 29199628571, 0, 0, 0] := by
  rw [show D2M8K2.u14800 = KTree.node D2M8K2.t14808 (nat_lit 32436985) (nat_lit 1363912447) (nat_lit 0) D2M8K2.t14809 from rfl, totK_node, tot14808, tot14809]
  decide +kernel

theorem arows14801 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14801 = true := by
  rw [show D2M8K2.u14801 = KTree.node D2M8K2.t14810 (nat_lit 32438355) (nat_lit 3710099078) (nat_lit 0) D2M8K2.t14811 from rfl, allE_node, rows14810, irow14801, rows14811]
  all_goals rfl

theorem atot14801 : totK PD2M8K2 D2M8K2.u14801 = [285516911903, 785616307630, 591508788362, 157544736211, 8209931632, 0, 0, 0] := by
  rw [show D2M8K2.u14801 = KTree.node D2M8K2.t14810 (nat_lit 32438355) (nat_lit 3710099078) (nat_lit 0) D2M8K2.t14811 from rfl, totK_node, tot14810, tot14811]
  decide +kernel

theorem arows14803 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14803 = true := by
  rw [show D2M8K2.u14803 = KTree.node D2M8K2.t14812 (nat_lit 32439806) (nat_lit 3059222678) (nat_lit 0) D2M8K2.t14813 from rfl, allE_node, rows14812, irow14803, rows14813]
  all_goals rfl

theorem atot14803 : totK PD2M8K2 D2M8K2.u14803 = [154328038265, 690559938373, 778273679253, 181458452069, 7166294683, 0, 0, 0] := by
  rw [show D2M8K2.u14803 = KTree.node D2M8K2.t14812 (nat_lit 32439806) (nat_lit 3059222678) (nat_lit 0) D2M8K2.t14813 from rfl, totK_node, tot14812, tot14813]
  decide +kernel

theorem arows14804 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14804 = true := by
  rw [show D2M8K2.u14804 = KTree.node D2M8K2.t14814 (nat_lit 32445059) (nat_lit 2907427195) (nat_lit 0) D2M8K2.t14815 from rfl, allE_node, rows14814, irow14804, rows14815]
  all_goals rfl

theorem atot14804 : totK PD2M8K2 D2M8K2.u14804 = [251978015378, 742597955784, 639742870288, 150923414131, 5883432551, 0, 0, 0] := by
  rw [show D2M8K2.u14804 = KTree.node D2M8K2.t14814 (nat_lit 32445059) (nat_lit 2907427195) (nat_lit 0) D2M8K2.t14815 from rfl, totK_node, tot14814, tot14815]
  decide +kernel

theorem arows14809 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14809 = true := by
  rw [show D2M8K2.u14809 = KTree.node D2M8K2.t14816 (nat_lit 32446984) (nat_lit 3771551350) (nat_lit 0) D2M8K2.t14817 from rfl, allE_node, rows14816, irow14809, rows14817]
  all_goals rfl

theorem atot14809 : totK PD2M8K2 D2M8K2.u14809 = [125170633270, 646126056653, 816875514744, 184923393562, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u14809 = KTree.node D2M8K2.t14816 (nat_lit 32446984) (nat_lit 3771551350) (nat_lit 0) D2M8K2.t14817 from rfl, totK_node, tot14816, tot14817]
  decide +kernel

theorem arows14810 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14810 = true := by
  rw [show D2M8K2.u14810 = KTree.node D2M8K2.t14818 (nat_lit 32449058) (nat_lit 3888154880) (nat_lit 0) D2M8K2.t14819 from rfl, allE_node, rows14818, irow14810, rows14819]
  all_goals rfl

theorem atot14810 : totK PD2M8K2 D2M8K2.u14810 = [375464085446, 941227954231, 483492290491, 37376396327, 0, 0, 0, 0] := by
  rw [show D2M8K2.u14810 = KTree.node D2M8K2.t14818 (nat_lit 32449058) (nat_lit 3888154880) (nat_lit 0) D2M8K2.t14819 from rfl, totK_node, tot14818, tot14819]
  decide +kernel

theorem arows14812 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14812 = true := by
  rw [show D2M8K2.u14812 = KTree.node D2M8K2.t14820 (nat_lit 32450721) (nat_lit 1484773214) (nat_lit 0) D2M8K2.t14821 from rfl, allE_node, rows14820, irow14812, rows14821]
  all_goals rfl

theorem atot14812 : totK PD2M8K2 D2M8K2.u14812 = [0, 494408728301, 983573843014, 300547445316, 8708200738, 0, 0, 0] := by
  rw [show D2M8K2.u14812 = KTree.node D2M8K2.t14820 (nat_lit 32450721) (nat_lit 1484773214) (nat_lit 0) D2M8K2.t14821 from rfl, totK_node, tot14820, tot14821]
  decide +kernel

theorem arows14813 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14813 = true := by
  rw [show D2M8K2.u14813 = KTree.node D2M8K2.t14822 (nat_lit 32452555) (nat_lit 1007231773) (nat_lit 0) D2M8K2.t14823 from rfl, allE_node, rows14822, irow14813, rows14823]
  all_goals rfl

theorem atot14813 : totK PD2M8K2 D2M8K2.u14813 = [0, 338753446191, 925435124364, 457242672822, 28154724041, 0, 0, 0] := by
  rw [show D2M8K2.u14813 = KTree.node D2M8K2.t14822 (nat_lit 32452555) (nat_lit 1007231773) (nat_lit 0) D2M8K2.t14823 from rfl, totK_node, tot14822, tot14823]
  decide +kernel

theorem arows14816 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14816 = true := by
  rw [show D2M8K2.u14816 = KTree.node D2M8K2.t14824 (nat_lit 32454201) (nat_lit 1835229511) (nat_lit 0) D2M8K2.t14825 from rfl, allE_node, rows14824, irow14816, rows14825]
  all_goals rfl

theorem atot14816 : totK PD2M8K2 D2M8K2.u14816 = [0, 168735686505, 745099480526, 740756236980, 105206412942, 1206465782, 0, 0] := by
  rw [show D2M8K2.u14816 = KTree.node D2M8K2.t14824 (nat_lit 32454201) (nat_lit 1835229511) (nat_lit 0) D2M8K2.t14825 from rfl, totK_node, tot14824, tot14825]
  decide +kernel

theorem arows14817 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14817 = true := by
  rw [show D2M8K2.u14817 = KTree.node D2M8K2.t14826 (nat_lit 32456336) (nat_lit 3530052088) (nat_lit 0) D2M8K2.t14827 from rfl, allE_node, rows14826, irow14817, rows14827]
  all_goals rfl

theorem atot14817 : totK PD2M8K2 D2M8K2.u14817 = [0, 324988705182, 925202045953, 528935612434, 40678585338, 0, 0, 0] := by
  rw [show D2M8K2.u14817 = KTree.node D2M8K2.t14826 (nat_lit 32456336) (nat_lit 3530052088) (nat_lit 0) D2M8K2.t14827 from rfl, totK_node, tot14826, tot14827]
  decide +kernel

theorem arows14819 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14819 = true := by
  rw [show D2M8K2.u14819 = KTree.node D2M8K2.t14828 (nat_lit 32459333) (nat_lit 2348298599) (nat_lit 0) D2M8K2.t14829 from rfl, allE_node, rows14828, irow14819, rows14829]
  all_goals rfl

theorem atot14819 : totK PD2M8K2 D2M8K2.u14819 = [0, 378650960969, 935648314243, 457940707970, 34867467930, 0, 0, 0] := by
  rw [show D2M8K2.u14819 = KTree.node D2M8K2.t14828 (nat_lit 32459333) (nat_lit 2348298599) (nat_lit 0) D2M8K2.t14829 from rfl, totK_node, tot14828, tot14829]
  decide +kernel

theorem arows14820 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14820 = true := by
  rw [show D2M8K2.u14820 = KTree.node D2M8K2.t14830 (nat_lit 32460880) (nat_lit 3334772653) (nat_lit 0) D2M8K2.t14831 from rfl, allE_node, rows14830, irow14820, rows14831]
  all_goals rfl

theorem atot14820 : totK PD2M8K2 D2M8K2.u14820 = [0, 56627033482, 546583843691, 849568402660, 264349851646, 13016197374, 0, 0] := by
  rw [show D2M8K2.u14820 = KTree.node D2M8K2.t14830 (nat_lit 32460880) (nat_lit 3334772653) (nat_lit 0) D2M8K2.t14831 from rfl, totK_node, tot14830, tot14831]
  decide +kernel

theorem arows14824 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14824 = true := by
  rw [show D2M8K2.u14824 = KTree.node D2M8K2.t14832 (nat_lit 32466171) (nat_lit 3662640915) (nat_lit 0) D2M8K2.t14833 from rfl, allE_node, rows14832, irow14824, rows14833]
  all_goals rfl

theorem atot14824 : totK PD2M8K2 D2M8K2.u14824 = [0, 322607689623, 913825447662, 524368528493, 38356808926, 0, 0, 0] := by
  rw [show D2M8K2.u14824 = KTree.node D2M8K2.t14832 (nat_lit 32466171) (nat_lit 3662640915) (nat_lit 0) D2M8K2.t14833 from rfl, totK_node, tot14832, tot14833]
  decide +kernel

theorem arows14825 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14825 = true := by
  rw [show D2M8K2.u14825 = KTree.node D2M8K2.t14834 (nat_lit 32468652) (nat_lit 3141727451) (nat_lit 0) D2M8K2.t14835 from rfl, allE_node, rows14834, irow14825, rows14835]
  all_goals rfl

theorem atot14825 : totK PD2M8K2 D2M8K2.u14825 = [0, 173298171207, 689698383881, 719261915321, 151370513149, 4574395652, 0, 0] := by
  rw [show D2M8K2.u14825 = KTree.node D2M8K2.t14834 (nat_lit 32468652) (nat_lit 3141727451) (nat_lit 0) D2M8K2.t14835 from rfl, totK_node, tot14834, tot14835]
  decide +kernel

theorem arows14827 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14827 = true := by
  rw [show D2M8K2.u14827 = KTree.node D2M8K2.t14836 (nat_lit 32470561) (nat_lit 1557828645) (nat_lit 0) D2M8K2.t14837 from rfl, allE_node, rows14836, irow14827, rows14837]
  all_goals rfl

theorem atot14827 : totK PD2M8K2 D2M8K2.u14827 = [103793967717, 489570046554, 781232104296, 412777508474, 30312490523, 0, 0, 0] := by
  rw [show D2M8K2.u14827 = KTree.node D2M8K2.t14836 (nat_lit 32470561) (nat_lit 1557828645) (nat_lit 0) D2M8K2.t14837 from rfl, totK_node, tot14836, tot14837]
  decide +kernel

theorem arows14828 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14828 = true := by
  rw [show D2M8K2.u14828 = KTree.node D2M8K2.t14838 (nat_lit 32473808) (nat_lit 3788156863) (nat_lit 0) D2M8K2.t14839 from rfl, allE_node, rows14838, irow14828, rows14839]
  all_goals rfl

theorem atot14828 : totK PD2M8K2 D2M8K2.u14828 = [299591631811, 878096623810, 548542775276, 48161687949, 0, 0, 0, 0] := by
  rw [show D2M8K2.u14828 = KTree.node D2M8K2.t14838 (nat_lit 32473808) (nat_lit 3788156863) (nat_lit 0) D2M8K2.t14839 from rfl, totK_node, tot14838, tot14839]
  decide +kernel

theorem arows14831 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14831 = true := by
  rw [show D2M8K2.u14831 = KTree.node D2M8K2.t14840 (nat_lit 32475787) (nat_lit 1218924919) (nat_lit 0) D2M8K2.t14841 from rfl, allE_node, rows14840, irow14831, rows14841]
  all_goals rfl

theorem atot14831 : totK PD2M8K2 D2M8K2.u14831 = [162708114747, 708392966932, 810698288149, 147578319593, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u14831 = KTree.node D2M8K2.t14840 (nat_lit 32475787) (nat_lit 1218924919) (nat_lit 0) D2M8K2.t14841 from rfl, totK_node, tot14840, tot14841]
  decide +kernel

theorem arows14832 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14832 = true := by
  rw [show D2M8K2.u14832 = KTree.node D2M8K2.t14842 (nat_lit 32477440) (nat_lit 2331615463) (nat_lit 0) D2M8K2.t14843 from rfl, allE_node, rows14842, irow14832, rows14843]
  all_goals rfl

theorem atot14832 : totK PD2M8K2 D2M8K2.u14832 = [255978850316, 789477115147, 610338303575, 148911682071, 15848128199, 0, 0, 0] := by
  rw [show D2M8K2.u14832 = KTree.node D2M8K2.t14842 (nat_lit 32477440) (nat_lit 2331615463) (nat_lit 0) D2M8K2.t14843 from rfl, totK_node, tot14842, tot14843]
  decide +kernel

theorem arows14834 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14834 = true := by
  rw [show D2M8K2.u14834 = KTree.node D2M8K2.t14844 (nat_lit 32478958) (nat_lit 3398992035) (nat_lit 0) D2M8K2.t14845 from rfl, allE_node, rows14844, irow14834, rows14845]
  all_goals rfl

theorem atot14834 : totK PD2M8K2 D2M8K2.u14834 = [71330800359, 428382506526, 859266035875, 421936392621, 21560118809, 0, 0, 0] := by
  rw [show D2M8K2.u14834 = KTree.node D2M8K2.t14844 (nat_lit 32478958) (nat_lit 3398992035) (nat_lit 0) D2M8K2.t14845 from rfl, totK_node, tot14844, tot14845]
  decide +kernel

theorem arows14835 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14835 = true := by
  rw [show D2M8K2.u14835 = KTree.node D2M8K2.t14846 (nat_lit 32483933) (nat_lit 1569662646) (nat_lit 0) D2M8K2.t14847 from rfl, allE_node, rows14846, irow14835, rows14847]
  all_goals rfl

theorem atot14835 : totK PD2M8K2 D2M8K2.u14835 = [368686991800, 947813834167, 484249948900, 35566190270, 0, 0, 0, 0] := by
  rw [show D2M8K2.u14835 = KTree.node D2M8K2.t14846 (nat_lit 32483933) (nat_lit 1569662646) (nat_lit 0) D2M8K2.t14847 from rfl, totK_node, tot14846, tot14847]
  decide +kernel

theorem arows14844 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14844 = true := by
  rw [show D2M8K2.u14844 = KTree.node D2M8K2.t14848 (nat_lit 32485582) (nat_lit 3878379649) (nat_lit 0) D2M8K2.t14849 from rfl, allE_node, rows14848, irow14844, rows14849]
  all_goals rfl

theorem atot14844 : totK PD2M8K2 D2M8K2.u14844 = [0, 487470011782, 979843226143, 302767510014, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u14844 = KTree.node D2M8K2.t14848 (nat_lit 32485582) (nat_lit 3878379649) (nat_lit 0) D2M8K2.t14849 from rfl, totK_node, tot14848, tot14849]
  decide +kernel

theorem arows14845 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14845 = true := by
  rw [show D2M8K2.u14845 = KTree.node D2M8K2.t14850 (nat_lit 32486968) (nat_lit 3048941846) (nat_lit 0) D2M8K2.t14851 from rfl, allE_node, rows14850, irow14845, rows14851]
  all_goals rfl

theorem atot14845 : totK PD2M8K2 D2M8K2.u14845 = [324118546996, 891557004766, 540954532929, 53775464316, 0, 0, 0, 0] := by
  rw [show D2M8K2.u14845 = KTree.node D2M8K2.t14850 (nat_lit 32486968) (nat_lit 3048941846) (nat_lit 0) D2M8K2.t14851 from rfl, totK_node, tot14850, tot14851]
  decide +kernel

theorem arows14847 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14847 = true := by
  rw [show D2M8K2.u14847 = KTree.node D2M8K2.t14852 (nat_lit 32489396) (nat_lit 3702992746) (nat_lit 0) D2M8K2.t14853 from rfl, allE_node, rows14852, irow14847, rows14853]
  all_goals rfl

theorem atot14847 : totK PD2M8K2 D2M8K2.u14847 = [173880593436, 681867488765, 757776690782, 181089156640, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u14847 = KTree.node D2M8K2.t14852 (nat_lit 32489396) (nat_lit 3702992746) (nat_lit 0) D2M8K2.t14853 from rfl, totK_node, tot14852, tot14853]
  decide +kernel

theorem arows14848 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14848 = true := by
  rw [show D2M8K2.u14848 = KTree.node D2M8K2.t14854 (nat_lit 32490989) (nat_lit 1606328604) (nat_lit 0) D2M8K2.t14855 from rfl, allE_node, rows14854, irow14848, rows14855]
  all_goals rfl

theorem atot14848 : totK PD2M8K2 D2M8K2.u14848 = [254798141159, 799868853526, 657137443626, 104902003166, 1268739303, 0, 0, 0] := by
  rw [show D2M8K2.u14848 = KTree.node D2M8K2.t14854 (nat_lit 32490989) (nat_lit 1606328604) (nat_lit 0) D2M8K2.t14855 from rfl, totK_node, tot14854, tot14855]
  decide +kernel

theorem arows14851 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14851 = true := by
  rw [show D2M8K2.u14851 = KTree.node D2M8K2.t14856 (nat_lit 32492675) (nat_lit 2656449059) (nat_lit 0) D2M8K2.t14857 from rfl, allE_node, rows14856, irow14851, rows14857]
  all_goals rfl

theorem atot14851 : totK PD2M8K2 D2M8K2.u14851 = [0, 411706499903, 956854174049, 397090759417, 22143218390, 0, 0, 0] := by
  rw [show D2M8K2.u14851 = KTree.node D2M8K2.t14856 (nat_lit 32492675) (nat_lit 2656449059) (nat_lit 0) D2M8K2.t14857 from rfl, totK_node, tot14856, tot14857]
  decide +kernel

theorem arows14852 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14852 = true := by
  rw [show D2M8K2.u14852 = KTree.node D2M8K2.t14858 (nat_lit 32494532) (nat_lit 2553686012) (nat_lit 0) D2M8K2.t14859 from rfl, allE_node, rows14858, irow14852, rows14859]
  all_goals rfl

theorem atot14852 : totK PD2M8K2 D2M8K2.u14852 = [0, 316448547801, 906077014152, 504017019469, 32407597631, 0, 0, 0] := by
  rw [show D2M8K2.u14852 = KTree.node D2M8K2.t14858 (nat_lit 32494532) (nat_lit 2553686012) (nat_lit 0) D2M8K2.t14859 from rfl, totK_node, tot14858, tot14859]
  decide +kernel

theorem arows14854 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14854 = true := by
  rw [show D2M8K2.u14854 = KTree.node D2M8K2.t14860 (nat_lit 32496571) (nat_lit 1675162517) (nat_lit 0) D2M8K2.t14861 from rfl, allE_node, rows14860, irow14854, rows14861]
  all_goals rfl

theorem atot14854 : totK PD2M8K2 D2M8K2.u14854 = [0, 165875177043, 735330128850, 771824988766, 115160999383, 1239866073, 0, 0] := by
  rw [show D2M8K2.u14854 = KTree.node D2M8K2.t14860 (nat_lit 32496571) (nat_lit 1675162517) (nat_lit 0) D2M8K2.t14861 from rfl, totK_node, tot14860, tot14861]
  decide +kernel

theorem arows14855 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14855 = true := by
  rw [show D2M8K2.u14855 = KTree.node D2M8K2.t14862 (nat_lit 32498260) (nat_lit 3953278546) (nat_lit 0) D2M8K2.t14863 from rfl, allE_node, rows14862, irow14855, rows14863]
  all_goals rfl

theorem atot14855 : totK PD2M8K2 D2M8K2.u14855 = [0, 400308193764, 959316031672, 431131438695, 24023757527, 0, 0, 0] := by
  rw [show D2M8K2.u14855 = KTree.node D2M8K2.t14862 (nat_lit 32498260) (nat_lit 3953278546) (nat_lit 0) D2M8K2.t14863 from rfl, totK_node, tot14862, tot14863]
  decide +kernel

theorem arows14859 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14859 = true := by
  rw [show D2M8K2.u14859 = KTree.node D2M8K2.t14864 (nat_lit 32504901) (nat_lit 1270654221) (nat_lit 0) D2M8K2.t14865 from rfl, allE_node, rows14864, irow14859, rows14865]
  all_goals rfl

theorem atot14859 : totK PD2M8K2 D2M8K2.u14859 = [0, 290051943407, 876996803823, 585483838110, 52194170931, 0, 0, 0] := by
  rw [show D2M8K2.u14859 = KTree.node D2M8K2.t14864 (nat_lit 32504901) (nat_lit 1270654221) (nat_lit 0) D2M8K2.t14865 from rfl, totK_node, tot14864, tot14865]
  decide +kernel

theorem arows14860 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14860 = true := by
  rw [show D2M8K2.u14860 = KTree.node D2M8K2.t14866 (nat_lit 32506590) (nat_lit 3854580037) (nat_lit 0) D2M8K2.t14867 from rfl, allE_node, rows14866, irow14860, rows14867]
  all_goals rfl

theorem atot14860 : totK PD2M8K2 D2M8K2.u14860 = [0, 78938184031, 547812263640, 819373489371, 264247376347, 13105450397, 0, 0] := by
  rw [show D2M8K2.u14860 = KTree.node D2M8K2.t14866 (nat_lit 32506590) (nat_lit 3854580037) (nat_lit 0) D2M8K2.t14867 from rfl, totK_node, tot14866, tot14867]
  decide +kernel

theorem arows14862 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14862 = true := by
  rw [show D2M8K2.u14862 = KTree.node D2M8K2.t14868 (nat_lit 32508304) (nat_lit 2522044255) (nat_lit 0) D2M8K2.t14869 from rfl, allE_node, rows14868, irow14862, rows14869]
  all_goals rfl

theorem atot14862 : totK PD2M8K2 D2M8K2.u14862 = [0, 244003080873, 816283355323, 644455314492, 80432960223, 1053411165, 0, 0] := by
  rw [show D2M8K2.u14862 = KTree.node D2M8K2.t14868 (nat_lit 32508304) (nat_lit 2522044255) (nat_lit 0) D2M8K2.t14869 from rfl, totK_node, tot14868, tot14869]
  decide +kernel

theorem arows14863 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14863 = true := by
  rw [show D2M8K2.u14863 = KTree.node D2M8K2.t14870 (nat_lit 32510908) (nat_lit 3840653483) (nat_lit 0) D2M8K2.t14871 from rfl, allE_node, rows14870, irow14863, rows14871]
  all_goals rfl

theorem atot14863 : totK PD2M8K2 D2M8K2.u14863 = [0, 281427481789, 793021177670, 593757094959, 108277901207, 3667207281, 0, 0] := by
  rw [show D2M8K2.u14863 = KTree.node D2M8K2.t14870 (nat_lit 32510908) (nat_lit 3840653483) (nat_lit 0) D2M8K2.t14871 from rfl, totK_node, tot14870, tot14871]
  decide +kernel

theorem arows14866 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14866 = true := by
  rw [show D2M8K2.u14866 = KTree.node D2M8K2.t14872 (nat_lit 32555577) (nat_lit 1785904054) (nat_lit 0) D2M8K2.t14873 from rfl, allE_node, rows14872, irow14866, rows14873]
  all_goals rfl

theorem atot14866 : totK PD2M8K2 D2M8K2.u14866 = [228091081257, 666123685799, 634736690792, 271396355972, 22079952194, 0, 0, 0] := by
  rw [show D2M8K2.u14866 = KTree.node D2M8K2.t14872 (nat_lit 32555577) (nat_lit 1785904054) (nat_lit 0) D2M8K2.t14873 from rfl, totK_node, tot14872, tot14873]
  decide +kernel

theorem arows14867 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14867 = true := by
  rw [show D2M8K2.u14867 = KTree.node D2M8K2.t14874 (nat_lit 32557114) (nat_lit 3937868485) (nat_lit 0) D2M8K2.t14875 from rfl, allE_node, rows14874, irow14867, rows14875]
  all_goals rfl

theorem atot14867 : totK PD2M8K2 D2M8K2.u14867 = [189279165674, 749070359256, 721492289044, 121577625389, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u14867 = KTree.node D2M8K2.t14874 (nat_lit 32557114) (nat_lit 3937868485) (nat_lit 0) D2M8K2.t14875 from rfl, totK_node, tot14874, tot14875]
  decide +kernel

theorem arows14869 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14869 = true := by
  rw [show D2M8K2.u14869 = KTree.node D2M8K2.t14876 (nat_lit 32559464) (nat_lit 3612636489) (nat_lit 0) D2M8K2.t14877 from rfl, allE_node, rows14876, irow14869, rows14877]
  all_goals rfl

theorem atot14869 : totK PD2M8K2 D2M8K2.u14869 = [267883696161, 830501780271, 658400957422, 76510334005, 0, 0, 0, 0] := by
  rw [show D2M8K2.u14869 = KTree.node D2M8K2.t14876 (nat_lit 32559464) (nat_lit 3612636489) (nat_lit 0) D2M8K2.t14877 from rfl, totK_node, tot14876, tot14877]
  decide +kernel

theorem arows14870 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14870 = true := by
  rw [show D2M8K2.u14870 = KTree.node D2M8K2.t14878 (nat_lit 32560696) (nat_lit 3359797656) (nat_lit 0) D2M8K2.t14879 from rfl, allE_node, rows14878, irow14870, rows14879]
  all_goals rfl

theorem atot14870 : totK PD2M8K2 D2M8K2.u14870 = [159209688015, 652181763341, 720191501945, 269171131816, 24234642673, 0, 0, 0] := by
  rw [show D2M8K2.u14870 = KTree.node D2M8K2.t14878 (nat_lit 32560696) (nat_lit 3359797656) (nat_lit 0) D2M8K2.t14879 from rfl, totK_node, tot14878, tot14879]
  decide +kernel

theorem arows14875 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14875 = true := by
  rw [show D2M8K2.u14875 = KTree.node D2M8K2.t14880 (nat_lit 32562217) (nat_lit 1362497470) (nat_lit 0) D2M8K2.t14881 from rfl, allE_node, rows14880, irow14875, rows14881]
  all_goals rfl

theorem atot14875 : totK PD2M8K2 D2M8K2.u14875 = [173020644527, 587507778792, 742913075388, 295955189082, 13090401234, 0, 0, 0] := by
  rw [show D2M8K2.u14875 = KTree.node D2M8K2.t14880 (nat_lit 32562217) (nat_lit 1362497470) (nat_lit 0) D2M8K2.t14881 from rfl, totK_node, tot14880, tot14881]
  decide +kernel

theorem arows14876 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14876 = true := by
  rw [show D2M8K2.u14876 = KTree.node D2M8K2.t14882 (nat_lit 32563728) (nat_lit 3633748302) (nat_lit 0) D2M8K2.t14883 from rfl, allE_node, rows14882, irow14876, rows14883]
  all_goals rfl

theorem atot14876 : totK PD2M8K2 D2M8K2.u14876 = [249002981558, 820792946399, 645365110073, 92834726159, 1164319620, 0, 0, 0] := by
  rw [show D2M8K2.u14876 = KTree.node D2M8K2.t14882 (nat_lit 32563728) (nat_lit 3633748302) (nat_lit 0) D2M8K2.t14883 from rfl, totK_node, tot14882, tot14883]
  decide +kernel

theorem arows14878 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14878 = true := by
  rw [show D2M8K2.u14878 = KTree.node D2M8K2.t14884 (nat_lit 32565411) (nat_lit 3559456113) (nat_lit 0) D2M8K2.t14885 from rfl, allE_node, rows14884, irow14878, rows14885]
  all_goals rfl

theorem atot14878 : totK PD2M8K2 D2M8K2.u14878 = [126426574475, 607403827255, 811791006809, 237477220483, 11738734009, 0, 0, 0] := by
  rw [show D2M8K2.u14878 = KTree.node D2M8K2.t14884 (nat_lit 32565411) (nat_lit 3559456113) (nat_lit 0) D2M8K2.t14885 from rfl, totK_node, tot14884, tot14885]
  decide +kernel

theorem arows14879 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14879 = true := by
  rw [show D2M8K2.u14879 = KTree.node D2M8K2.t14886 (nat_lit 32567074) (nat_lit 3364839306) (nat_lit 0) D2M8K2.t14887 from rfl, allE_node, rows14886, irow14879, rows14887]
  all_goals rfl

theorem atot14879 : totK PD2M8K2 D2M8K2.u14879 = [295804607770, 873420207604, 592833961299, 57813747157, 0, 0, 0, 0] := by
  rw [show D2M8K2.u14879 = KTree.node D2M8K2.t14886 (nat_lit 32567074) (nat_lit 3364839306) (nat_lit 0) D2M8K2.t14887 from rfl, totK_node, tot14886, tot14887]
  decide +kernel

theorem arows14882 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14882 = true := by
  rw [show D2M8K2.u14882 = KTree.node D2M8K2.t14888 (nat_lit 32568777) (nat_lit 1737369977) (nat_lit 0) D2M8K2.t14889 from rfl, allE_node, rows14888, irow14882, rows14889]
  all_goals rfl

theorem atot14882 : totK PD2M8K2 D2M8K2.u14882 = [87123270202, 549466515162, 857194614802, 282329006528, 13071894232, 0, 0, 0] := by
  rw [show D2M8K2.u14882 = KTree.node D2M8K2.t14888 (nat_lit 32568777) (nat_lit 1737369977) (nat_lit 0) D2M8K2.t14889 from rfl, totK_node, tot14888, tot14889]
  decide +kernel

theorem arows14883 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14883 = true := by
  rw [show D2M8K2.u14883 = KTree.node D2M8K2.t14890 (nat_lit 32573621) (nat_lit 2300761511) (nat_lit 0) D2M8K2.t14891 from rfl, allE_node, rows14890, irow14883, rows14891]
  all_goals rfl

theorem atot14883 : totK PD2M8K2 D2M8K2.u14883 = [361086053141, 928518943827, 521462987385, 43239687965, 0, 0, 0, 0] := by
  rw [show D2M8K2.u14883 = KTree.node D2M8K2.t14890 (nat_lit 32573621) (nat_lit 2300761511) (nat_lit 0) D2M8K2.t14891 from rfl, totK_node, tot14890, tot14891]
  decide +kernel

theorem arows14885 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14885 = true := by
  rw [show D2M8K2.u14885 = KTree.node D2M8K2.t14892 (nat_lit 32575231) (nat_lit 1765997998) (nat_lit 0) D2M8K2.t14893 from rfl, allE_node, rows14892, irow14885, rows14893]
  all_goals rfl

theorem atot14885 : totK PD2M8K2 D2M8K2.u14885 = [0, 464557145217, 993116901759, 332079207328, 9938656398, 0, 0, 0] := by
  rw [show D2M8K2.u14885 = KTree.node D2M8K2.t14892 (nat_lit 32575231) (nat_lit 1765997998) (nat_lit 0) D2M8K2.t14893 from rfl, totK_node, tot14892, tot14893]
  decide +kernel

theorem arows14886 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14886 = true := by
  rw [show D2M8K2.u14886 = KTree.node D2M8K2.t14894 (nat_lit 32577029) (nat_lit 2382707516) (nat_lit 0) D2M8K2.t14895 from rfl, allE_node, rows14894, irow14886, rows14895]
  all_goals rfl

theorem atot14886 : totK PD2M8K2 D2M8K2.u14886 = [0, 359451101394, 947586935161, 437371616368, 22544449898, 0, 0, 0] := by
  rw [show D2M8K2.u14886 = KTree.node D2M8K2.t14894 (nat_lit 32577029) (nat_lit 2382707516) (nat_lit 0) D2M8K2.t14895 from rfl, totK_node, tot14894, tot14895]
  decide +kernel

theorem arows14890 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14890 = true := by
  rw [show D2M8K2.u14890 = KTree.node D2M8K2.t14896 (nat_lit 32578663) (nat_lit 1420714150) (nat_lit 0) D2M8K2.t14897 from rfl, allE_node, rows14896, irow14890, rows14897]
  all_goals rfl

theorem atot14890 : totK PD2M8K2 D2M8K2.u14890 = [0, 126287304881, 690280387454, 843043900185, 122137824186, 1310285577, 0, 0] := by
  rw [show D2M8K2.u14890 = KTree.node D2M8K2.t14896 (nat_lit 32578663) (nat_lit 1420714150) (nat_lit 0) D2M8K2.t14897 from rfl, totK_node, tot14896, tot14897]
  decide +kernel

theorem arows14891 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14891 = true := by
  rw [show D2M8K2.u14891 = KTree.node D2M8K2.t14898 (nat_lit 32580678) (nat_lit 3849525874) (nat_lit 0) D2M8K2.t14899 from rfl, allE_node, rows14898, irow14891, rows14899]
  all_goals rfl

theorem atot14891 : totK PD2M8K2 D2M8K2.u14891 = [0, 351116503297, 935831454569, 514796359960, 37626572893, 0, 0, 0] := by
  rw [show D2M8K2.u14891 = KTree.node D2M8K2.t14898 (nat_lit 32580678) (nat_lit 3849525874) (nat_lit 0) D2M8K2.t14899 from rfl, totK_node, tot14898, tot14899]
  decide +kernel

theorem arows14893 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14893 = true := by
  rw [show D2M8K2.u14893 = KTree.node D2M8K2.t14900 (nat_lit 32583692) (nat_lit 1492768249) (nat_lit 0) D2M8K2.t14901 from rfl, allE_node, rows14900, irow14893, rows14901]
  all_goals rfl

theorem atot14893 : totK PD2M8K2 D2M8K2.u14893 = [0, 343874518991, 894333776473, 504328879426, 44955212189, 0, 0, 0] := by
  rw [show D2M8K2.u14893 = KTree.node D2M8K2.t14900 (nat_lit 32583692) (nat_lit 1492768249) (nat_lit 0) D2M8K2.t14901 from rfl, totK_node, tot14900, tot14901]
  decide +kernel

theorem arows14894 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14894 = true := by
  rw [show D2M8K2.u14894 = KTree.node D2M8K2.t14902 (nat_lit 32585266) (nat_lit 3797577698) (nat_lit 0) D2M8K2.t14903 from rfl, allE_node, rows14902, irow14894, rows14903]
  all_goals rfl

theorem atot14894 : totK PD2M8K2 D2M8K2.u14894 = [0, 90540398475, 638643699473, 858629400357, 179992715640, 4879840392, 0, 0] := by
  rw [show D2M8K2.u14894 = KTree.node D2M8K2.t14902 (nat_lit 32585266) (nat_lit 3797577698) (nat_lit 0) D2M8K2.t14903 from rfl, totK_node, tot14902, tot14903]
  decide +kernel

theorem arows14897 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14897 = true := by
  rw [show D2M8K2.u14897 = KTree.node D2M8K2.t14904 (nat_lit 32587521) (nat_lit 1778475950) (nat_lit 0) D2M8K2.t14905 from rfl, allE_node, rows14904, irow14897, rows14905]
  all_goals rfl

theorem atot14897 : totK PD2M8K2 D2M8K2.u14897 = [0, 382306591007, 937938625865, 452448953484, 32910464902, 0, 0, 0] := by
  rw [show D2M8K2.u14897 = KTree.node D2M8K2.t14904 (nat_lit 32587521) (nat_lit 1778475950) (nat_lit 0) D2M8K2.t14905 from rfl, totK_node, tot14904, tot14905]
  decide +kernel

theorem arows14898 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14898 = true := by
  rw [show D2M8K2.u14898 = KTree.node D2M8K2.t14906 (nat_lit 32589260) (nat_lit 2934295076) (nat_lit 0) D2M8K2.t14907 from rfl, allE_node, rows14906, irow14898, rows14907]
  all_goals rfl

theorem atot14898 : totK PD2M8K2 D2M8K2.u14898 = [0, 106256217329, 635104820221, 834375335047, 181678759138, 4931404646, 0, 0] := by
  rw [show D2M8K2.u14898 = KTree.node D2M8K2.t14906 (nat_lit 32589260) (nat_lit 2934295076) (nat_lit 0) D2M8K2.t14907 from rfl, totK_node, tot14906, tot14907]
  decide +kernel

theorem arows14900 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14900 = true := by
  rw [show D2M8K2.u14900 = KTree.node D2M8K2.t14908 (nat_lit 32594256) (nat_lit 3654800869) (nat_lit 0) D2M8K2.t14909 from rfl, allE_node, rows14908, irow14900, rows14909]
  all_goals rfl

theorem atot14900 : totK PD2M8K2 D2M8K2.u14900 = [0, 359303690966, 952886856136, 492870520681, 32679690692, 0, 0, 0] := by
  rw [show D2M8K2.u14900 = KTree.node D2M8K2.t14908 (nat_lit 32594256) (nat_lit 3654800869) (nat_lit 0) D2M8K2.t14909 from rfl, totK_node, tot14908, tot14909]
  decide +kernel

theorem arows14901 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14901 = true := by
  rw [show D2M8K2.u14901 = KTree.node D2M8K2.t14910 (nat_lit 32595897) (nat_lit 1646194771) (nat_lit 0) D2M8K2.t14911 from rfl, allE_node, rows14910, irow14901, rows14911]
  all_goals rfl

theorem atot14901 : totK PD2M8K2 D2M8K2.u14901 = [0, 0, 510400438444, 964694851810, 271218436577, 8424427256, 0, 0] := by
  rw [show D2M8K2.u14901 = KTree.node D2M8K2.t14910 (nat_lit 32595897) (nat_lit 1646194771) (nat_lit 0) D2M8K2.t14911 from rfl, totK_node, tot14910, tot14911]
  decide +kernel

theorem arows14907 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14907 = true := by
  rw [show D2M8K2.u14907 = KTree.node D2M8K2.t14912 (nat_lit 32597721) (nat_lit 1731128826) (nat_lit 0) D2M8K2.t14913 from rfl, allE_node, rows14912, irow14907, rows14913]
  all_goals rfl

theorem atot14907 : totK PD2M8K2 D2M8K2.u14907 = [0, 347033201396, 832915600881, 461480562873, 130731621013, 13326740810, 0, 0] := by
  rw [show D2M8K2.u14907 = KTree.node D2M8K2.t14912 (nat_lit 32597721) (nat_lit 1731128826) (nat_lit 0) D2M8K2.t14913 from rfl, totK_node, tot14912, tot14913]
  decide +kernel

theorem arows14908 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14908 = true := by
  rw [show D2M8K2.u14908 = KTree.node D2M8K2.t14914 (nat_lit 32598947) (nat_lit 2092515340) (nat_lit 0) D2M8K2.t14915 from rfl, allE_node, rows14914, irow14908, rows14915]
  all_goals rfl

theorem atot14908 : totK PD2M8K2 D2M8K2.u14908 = [0, 88680480173, 687888873618, 881617230801, 145584373388, 1369150432, 0, 0] := by
  rw [show D2M8K2.u14908 = KTree.node D2M8K2.t14914 (nat_lit 32598947) (nat_lit 2092515340) (nat_lit 0) D2M8K2.t14915 from rfl, totK_node, tot14914, tot14915]
  decide +kernel

theorem arows14910 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14910 = true := by
  rw [show D2M8K2.u14910 = KTree.node D2M8K2.t14916 (nat_lit 32604510) (nat_lit 2466145275) (nat_lit 0) D2M8K2.t14917 from rfl, allE_node, rows14916, irow14910, rows14917]
  all_goals rfl

theorem atot14910 : totK PD2M8K2 D2M8K2.u14910 = [0, 373351809620, 906838512296, 470644653390, 40813098282, 0, 0, 0] := by
  rw [show D2M8K2.u14910 = KTree.node D2M8K2.t14916 (nat_lit 32604510) (nat_lit 2466145275) (nat_lit 0) D2M8K2.t14917 from rfl, totK_node, tot14916, tot14917]
  decide +kernel

theorem arows14911 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14911 = true := by
  rw [show D2M8K2.u14911 = KTree.node D2M8K2.t14918 (nat_lit 32606212) (nat_lit 3866437580) (nat_lit 0) D2M8K2.t14919 from rfl, allE_node, rows14918, irow14911, rows14919]
  all_goals rfl

theorem atot14911 : totK PD2M8K2 D2M8K2.u14911 = [0, 52638720481, 596398574905, 921507832527, 215775258890, 5172807878, 0, 0] := by
  rw [show D2M8K2.u14911 = KTree.node D2M8K2.t14918 (nat_lit 32606212) (nat_lit 3866437580) (nat_lit 0) D2M8K2.t14919 from rfl, totK_node, tot14918, tot14919]
  decide +kernel

theorem arows14914 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14914 = true := by
  rw [show D2M8K2.u14914 = KTree.node D2M8K2.t14920 (nat_lit 32608326) (nat_lit 3892297328) (nat_lit 0) D2M8K2.t14921 from rfl, allE_node, rows14920, irow14914, rows14921]
  all_goals rfl

theorem atot14914 : totK PD2M8K2 D2M8K2.u14914 = [0, 389380577380, 932487024095, 442022777747, 32038952823, 0, 0, 0] := by
  rw [show D2M8K2.u14914 = KTree.node D2M8K2.t14920 (nat_lit 32608326) (nat_lit 3892297328) (nat_lit 0) D2M8K2.t14921 from rfl, totK_node, tot14920, tot14921]
  decide +kernel

theorem arows14915 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14915 = true := by
  rw [show D2M8K2.u14915 = KTree.node D2M8K2.t14922 (nat_lit 32610030) (nat_lit 4086215485) (nat_lit 0) D2M8K2.t14923 from rfl, allE_node, rows14922, irow14915, rows14923]
  all_goals rfl

theorem atot14915 : totK PD2M8K2 D2M8K2.u14915 = [0, 54330972770, 578481839634, 922923079265, 223314231454, 5228939780, 0, 0] := by
  rw [show D2M8K2.u14915 = KTree.node D2M8K2.t14922 (nat_lit 32610030) (nat_lit 4086215485) (nat_lit 0) D2M8K2.t14923 from rfl, totK_node, tot14922, tot14923]
  decide +kernel

theorem arows14917 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14917 = true := by
  rw [show D2M8K2.u14917 = KTree.node D2M8K2.t14924 (nat_lit 32611829) (nat_lit 1150927029) (nat_lit 0) D2M8K2.t14925 from rfl, allE_node, rows14924, irow14917, rows14925]
  all_goals rfl

theorem atot14917 : totK PD2M8K2 D2M8K2.u14917 = [0, 266303699294, 826718647202, 572083450023, 76135561717, 1096505104, 0, 0] := by
  rw [show D2M8K2.u14917 = KTree.node D2M8K2.t14924 (nat_lit 32611829) (nat_lit 1150927029) (nat_lit 0) D2M8K2.t14925 from rfl, totK_node, tot14924, tot14925]
  decide +kernel

theorem arows14918 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14918 = true := by
  rw [show D2M8K2.u14918 = KTree.node D2M8K2.t14926 (nat_lit 32614464) (nat_lit 3583556475) (nat_lit 0) D2M8K2.t14927 from rfl, allE_node, rows14926, irow14918, rows14927]
  all_goals rfl

theorem atot14918 : totK PD2M8K2 D2M8K2.u14918 = [0, 248472321342, 831903929418, 650966675363, 68823088105, 0, 0, 0] := by
  rw [show D2M8K2.u14918 = KTree.node D2M8K2.t14926 (nat_lit 32614464) (nat_lit 3583556475) (nat_lit 0) D2M8K2.t14927 from rfl, totK_node, tot14926, tot14927]
  decide +kernel

theorem arows14922 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14922 = true := by
  rw [show D2M8K2.u14922 = KTree.node D2M8K2.t14928 (nat_lit 32615950) (nat_lit 3579208203) (nat_lit 0) D2M8K2.t14929 from rfl, allE_node, rows14928, irow14922, rows14929]
  all_goals rfl

theorem atot14922 : totK PD2M8K2 D2M8K2.u14922 = [0, 179867083042, 730076728866, 758672807972, 140209040676, 1268739303, 0, 0] := by
  rw [show D2M8K2.u14922 = KTree.node D2M8K2.t14928 (nat_lit 32615950) (nat_lit 3579208203) (nat_lit 0) D2M8K2.t14929 from rfl, totK_node, tot14928, tot14929]
  decide +kernel

theorem arows14923 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14923 = true := by
  rw [show D2M8K2.u14923 = KTree.node D2M8K2.t14930 (nat_lit 32617644) (nat_lit 2803394435) (nat_lit 0) D2M8K2.t14931 from rfl, allE_node, rows14930, irow14923, rows14931]
  all_goals rfl

theorem atot14923 : totK PD2M8K2 D2M8K2.u14923 = [0, 0, 357047543195, 942748987861, 432138665242, 25990639879, 0, 0] := by
  rw [show D2M8K2.u14923 = KTree.node D2M8K2.t14930 (nat_lit 32617644) (nat_lit 2803394435) (nat_lit 0) D2M8K2.t14931 from rfl, totK_node, tot14930, tot14931]
  decide +kernel

theorem arows14925 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14925 = true := by
  rw [show D2M8K2.u14925 = KTree.node D2M8K2.t14932 (nat_lit 32619211) (nat_lit 1407840849) (nat_lit 0) D2M8K2.t14933 from rfl, allE_node, rows14932, irow14925, rows14933]
  all_goals rfl

theorem atot14925 : totK PD2M8K2 D2M8K2.u14925 = [0, 0, 255616929805, 815688418274, 569409002744, 85985976646, 1369150432, 0] := by
  rw [show D2M8K2.u14925 = KTree.node D2M8K2.t14932 (nat_lit 32619211) (nat_lit 1407840849) (nat_lit 0) D2M8K2.t14933 from rfl, totK_node, tot14932, tot14933]
  decide +kernel

theorem arows14926 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14926 = true := by
  rw [show D2M8K2.u14926 = KTree.node D2M8K2.t14934 (nat_lit 32624767) (nat_lit 2089211455) (nat_lit 0) D2M8K2.t14935 from rfl, allE_node, rows14934, irow14926, rows14935]
  all_goals rfl

theorem atot14926 : totK PD2M8K2 D2M8K2.u14926 = [0, 0, 247397327759, 872314669608, 581168589349, 41617091181, 0, 0] := by
  rw [show D2M8K2.u14926 = KTree.node D2M8K2.t14934 (nat_lit 32624767) (nat_lit 2089211455) (nat_lit 0) D2M8K2.t14935 from rfl, totK_node, tot14934, tot14935]
  decide +kernel

theorem arows14929 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14929 = true := by
  rw [show D2M8K2.u14929 = KTree.node D2M8K2.t14936 (nat_lit 32628164) (nat_lit 2970612717) (nat_lit 0) D2M8K2.t14937 from rfl, allE_node, rows14936, irow14929, rows14937]
  all_goals rfl

theorem atot14929 : totK PD2M8K2 D2M8K2.u14929 = [0, 0, 410883210182, 982033938610, 367412466322, 12594469520, 0, 0] := by
  rw [show D2M8K2.u14929 = KTree.node D2M8K2.t14936 (nat_lit 32628164) (nat_lit 2970612717) (nat_lit 0) D2M8K2.t14937 from rfl, totK_node, tot14936, tot14937]
  decide +kernel

theorem arows14930 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14930 = true := by
  rw [show D2M8K2.u14930 = KTree.node D2M8K2.t14938 (nat_lit 32629801) (nat_lit 1442669715) (nat_lit 0) D2M8K2.t14939 from rfl, allE_node, rows14938, irow14930, rows14939]
  all_goals rfl

theorem atot14930 : totK PD2M8K2 D2M8K2.u14930 = [0, 0, 362166829559, 948424482984, 397157158486, 16439024909, 0, 0] := by
  rw [show D2M8K2.u14930 = KTree.node D2M8K2.t14938 (nat_lit 32629801) (nat_lit 1442669715) (nat_lit 0) D2M8K2.t14939 from rfl, totK_node, tot14938, tot14939]
  decide +kernel

theorem arows14932 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14932 = true := by
  rw [show D2M8K2.u14932 = KTree.node D2M8K2.t14940 (nat_lit 32635205) (nat_lit 2250027172) (nat_lit 0) D2M8K2.t14941 from rfl, allE_node, rows14940, irow14932, rows14941]
  all_goals rfl

theorem atot14932 : totK PD2M8K2 D2M8K2.u14932 = [0, 0, 375455900500, 963064627021, 400148957350, 14447010309, 0, 0] := by
  rw [show D2M8K2.u14932 = KTree.node D2M8K2.t14940 (nat_lit 32635205) (nat_lit 2250027172) (nat_lit 0) D2M8K2.t14941 from rfl, totK_node, tot14940, tot14941]
  decide +kernel

theorem arows14933 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14933 = true := by
  rw [show D2M8K2.u14933 = KTree.node D2M8K2.t14942 (nat_lit 32642243) (nat_lit 2870342021) (nat_lit 0) D2M8K2.t14943 from rfl, allE_node, rows14942, irow14933, rows14943]
  all_goals rfl

theorem atot14933 : totK PD2M8K2 D2M8K2.u14933 = [0, 182603865993, 628570889540, 731757455899, 266590935834, 17376665387, 0, 0] := by
  rw [show D2M8K2.u14933 = KTree.node D2M8K2.t14942 (nat_lit 32642243) (nat_lit 2870342021) (nat_lit 0) D2M8K2.t14943 from rfl, totK_node, tot14942, tot14943]
  decide +kernel

theorem arows14938 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14938 = true := by
  rw [show D2M8K2.u14938 = KTree.node D2M8K2.t14944 (nat_lit 32643399) (nat_lit 3628263446) (nat_lit 0) D2M8K2.t14945 from rfl, allE_node, rows14944, irow14938, rows14945]
  all_goals rfl

theorem atot14938 : totK PD2M8K2 D2M8K2.u14938 = [0, 261726886125, 774919714897, 591933594768, 188086659136, 21400436502, 0, 0] := by
  rw [show D2M8K2.u14938 = KTree.node D2M8K2.t14944 (nat_lit 32643399) (nat_lit 3628263446) (nat_lit 0) D2M8K2.t14945 from rfl, totK_node, tot14944, tot14945]
  decide +kernel

theorem arows14939 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14939 = true := by
  rw [show D2M8K2.u14939 = KTree.node D2M8K2.t14946 (nat_lit 32644848) (nat_lit 2918818776) (nat_lit 0) D2M8K2.t14947 from rfl, allE_node, rows14946, irow14939, rows14947]
  all_goals rfl

theorem atot14939 : totK PD2M8K2 D2M8K2.u14939 = [0, 67008747100, 442040070508, 886651790142, 386771222245, 16100220446, 0, 0] := by
  rw [show D2M8K2.u14939 = KTree.node D2M8K2.t14946 (nat_lit 32644848) (nat_lit 2918818776) (nat_lit 0) D2M8K2.t14947 from rfl, totK_node, tot14946, tot14947]
  decide +kernel

theorem arows14941 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14941 = true := by
  rw [show D2M8K2.u14941 = KTree.node D2M8K2.t14948 (nat_lit 32646109) (nat_lit 1148078553) (nat_lit 0) D2M8K2.t14949 from rfl, allE_node, rows14948, irow14941, rows14949]
  all_goals rfl

theorem atot14941 : totK PD2M8K2 D2M8K2.u14941 = [0, 347376361931, 932267934888, 507392216711, 38260097753, 0, 0, 0] := by
  rw [show D2M8K2.u14941 = KTree.node D2M8K2.t14948 (nat_lit 32646109) (nat_lit 1148078553) (nat_lit 0) D2M8K2.t14949 from rfl, totK_node, tot14948, tot14949]
  decide +kernel

theorem arows14942 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14942 = true := by
  rw [show D2M8K2.u14942 = KTree.node D2M8K2.t14950 (nat_lit 32647833) (nat_lit 1623175223) (nat_lit 0) D2M8K2.t14951 from rfl, allE_node, rows14950, irow14942, rows14951]
  all_goals rfl

theorem atot14942 : totK PD2M8K2 D2M8K2.u14942 = [0, 56012782626, 521346485001, 919392958081, 275710628674, 9067749566, 0, 0] := by
  rw [show D2M8K2.u14942 = KTree.node D2M8K2.t14950 (nat_lit 32647833) (nat_lit 1623175223) (nat_lit 0) D2M8K2.t14951 from rfl, totK_node, tot14950, tot14951]
  decide +kernel

theorem arows14945 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14945 = true := by
  rw [show D2M8K2.u14945 = KTree.node D2M8K2.t14952 (nat_lit 32649840) (nat_lit 3638710369) (nat_lit 0) D2M8K2.t14953 from rfl, allE_node, rows14952, irow14945, rows14953]
  all_goals rfl

theorem atot14945 : totK PD2M8K2 D2M8K2.u14945 = [0, 355495910857, 947666015646, 494110191876, 35736435109, 0, 0, 0] := by
  rw [show D2M8K2.u14945 = KTree.node D2M8K2.t14952 (nat_lit 32649840) (nat_lit 3638710369) (nat_lit 0) D2M8K2.t14953 from rfl, totK_node, tot14952, tot14953]
  decide +kernel

theorem arows14946 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14946 = true := by
  rw [show D2M8K2.u14946 = KTree.node D2M8K2.t14954 (nat_lit 32651558) (nat_lit 3918629950) (nat_lit 0) D2M8K2.t14955 from rfl, allE_node, rows14954, irow14946, rows14955]
  all_goals rfl

theorem atot14946 : totK PD2M8K2 D2M8K2.u14946 = [0, 37947253655, 506879119641, 945332709374, 287809337301, 9178989717, 0, 0] := by
  rw [show D2M8K2.u14946 = KTree.node D2M8K2.t14954 (nat_lit 32651558) (nat_lit 3918629950) (nat_lit 0) D2M8K2.t14955 from rfl, totK_node, tot14954, tot14955]
  decide +kernel

theorem arows14948 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14948 = true := by
  rw [show D2M8K2.u14948 = KTree.node D2M8K2.t14956 (nat_lit 32653234) (nat_lit 3713721981) (nat_lit 0) D2M8K2.t14957 from rfl, allE_node, rows14956, irow14948, rows14957]
  all_goals rfl

theorem atot14948 : totK PD2M8K2 D2M8K2.u14948 = [0, 289472903328, 885610286705, 591745244926, 64467112942, 0, 0, 0] := by
  rw [show D2M8K2.u14948 = KTree.node D2M8K2.t14956 (nat_lit 32653234) (nat_lit 3713721981) (nat_lit 0) D2M8K2.t14957 from rfl, totK_node, tot14956, tot14957]
  decide +kernel

theorem arows14949 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14949 = true := by
  rw [show D2M8K2.u14949 = KTree.node D2M8K2.t14958 (nat_lit 32655871) (nat_lit 2306844796) (nat_lit 0) D2M8K2.t14959 from rfl, allE_node, rows14958, irow14949, rows14959]
  all_goals rfl

theorem atot14949 : totK PD2M8K2 D2M8K2.u14949 = [0, 249379502395, 779921881838, 681716550294, 124033736173, 1429815836, 0, 0] := by
  rw [show D2M8K2.u14949 = KTree.node D2M8K2.t14958 (nat_lit 32655871) (nat_lit 2306844796) (nat_lit 0) D2M8K2.t14959 from rfl, totK_node, tot14958, tot14959]
  decide +kernel

theorem arows14953 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14953 = true := by
  rw [show D2M8K2.u14953 = KTree.node D2M8K2.t14960 (nat_lit 32657341) (nat_lit 1236749622) (nat_lit 0) D2M8K2.t14961 from rfl, allE_node, rows14960, irow14953, rows14961]
  all_goals rfl

theorem atot14953 : totK PD2M8K2 D2M8K2.u14953 = [0, 180127341725, 756327494168, 746480420145, 131140854570, 1248762627, 0, 0] := by
  rw [show D2M8K2.u14953 = KTree.node D2M8K2.t14960 (nat_lit 32657341) (nat_lit 1236749622) (nat_lit 0) D2M8K2.t14961 from rfl, totK_node, tot14960, tot14961]
  decide +kernel

theorem arows14954 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14954 = true := by
  rw [show D2M8K2.u14954 = KTree.node D2M8K2.t14962 (nat_lit 32659044) (nat_lit 3251650857) (nat_lit 0) D2M8K2.t14963 from rfl, allE_node, rows14962, irow14954, rows14963]
  all_goals rfl

theorem atot14954 : totK PD2M8K2 D2M8K2.u14954 = [0, 178101248760, 585705974273, 699096339944, 292575081007, 20681819431, 0, 0] := by
  rw [show D2M8K2.u14954 = KTree.node D2M8K2.t14962 (nat_lit 32659044) (nat_lit 3251650857) (nat_lit 0) D2M8K2.t14963 from rfl, totK_node, tot14962, tot14963]
  decide +kernel

theorem arows14956 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14956 = true := by
  rw [show D2M8K2.u14956 = KTree.node D2M8K2.t14964 (nat_lit 32681384) (nat_lit 2726721989) (nat_lit 0) D2M8K2.t14965 from rfl, allE_node, rows14964, irow14956, rows14965]
  all_goals rfl

theorem atot14956 : totK PD2M8K2 D2M8K2.u14956 = [0, 228595947622, 779759494510, 645560643700, 101687460468, 1369150432, 0, 0] := by
  rw [show D2M8K2.u14956 = KTree.node D2M8K2.t14964 (nat_lit 32681384) (nat_lit 2726721989) (nat_lit 0) D2M8K2.t14965 from rfl, totK_node, tot14964, tot14965]
  decide +kernel

theorem arows14957 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14957 = true := by
  rw [show D2M8K2.u14957 = KTree.node D2M8K2.t14966 (nat_lit 32683754) (nat_lit 4139872233) (nat_lit 0) D2M8K2.t14967 from rfl, allE_node, rows14966, irow14957, rows14967]
  all_goals rfl

theorem atot14957 : totK PD2M8K2 D2M8K2.u14957 = [0, 212295604251, 787635178398, 741925554924, 86436432992, 0, 0, 0] := by
  rw [show D2M8K2.u14957 = KTree.node D2M8K2.t14966 (nat_lit 32683754) (nat_lit 4139872233) (nat_lit 0) D2M8K2.t14967 from rfl, totK_node, tot14966, tot14967]
  decide +kernel

theorem arows14960 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14960 = true := by
  rw [show D2M8K2.u14960 = KTree.node D2M8K2.t14968 (nat_lit 32684989) (nat_lit 1207258479) (nat_lit 0) D2M8K2.t14969 from rfl, allE_node, rows14968, irow14960, rows14969]
  all_goals rfl

theorem atot14960 : totK PD2M8K2 D2M8K2.u14960 = [0, 202723647975, 747715547804, 649591900023, 200464413329, 19355846809, 0, 0] := by
  rw [show D2M8K2.u14960 = KTree.node D2M8K2.t14968 (nat_lit 32684989) (nat_lit 1207258479) (nat_lit 0) D2M8K2.t14969 from rfl, totK_node, tot14968, tot14969]
  decide +kernel

theorem arows14961 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14961 = true := by
  rw [show D2M8K2.u14961 = KTree.node D2M8K2.t14970 (nat_lit 32686573) (nat_lit 1276041379) (nat_lit 0) D2M8K2.t14971 from rfl, allE_node, rows14970, irow14961, rows14971]
  all_goals rfl

theorem atot14961 : totK PD2M8K2 D2M8K2.u14961 = [0, 124350470976, 519134115291, 795827237050, 336307285754, 13408985006, 0, 0] := by
  rw [show D2M8K2.u14961 = KTree.node D2M8K2.t14970 (nat_lit 32686573) (nat_lit 1276041379) (nat_lit 0) D2M8K2.t14971 from rfl, totK_node, tot14970, tot14971]
  decide +kernel

theorem arows14963 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14963 = true := by
  rw [show D2M8K2.u14963 = KTree.node D2M8K2.t14972 (nat_lit 32688035) (nat_lit 2217581573) (nat_lit 0) D2M8K2.t14973 from rfl, allE_node, rows14972, irow14963, rows14973]
  all_goals rfl

theorem atot14963 : totK PD2M8K2 D2M8K2.u14963 = [0, 311059127116, 893809922573, 564269531148, 53412109061, 0, 0, 0] := by
  rw [show D2M8K2.u14963 = KTree.node D2M8K2.t14972 (nat_lit 32688035) (nat_lit 2217581573) (nat_lit 0) D2M8K2.t14973 from rfl, totK_node, tot14972, tot14973]
  decide +kernel

theorem arows14964 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14964 = true := by
  rw [show D2M8K2.u14964 = KTree.node D2M8K2.t14974 (nat_lit 32689410) (nat_lit 1208050040) (nat_lit 0) D2M8K2.t14975 from rfl, allE_node, rows14974, irow14964, rows14975]
  all_goals rfl

theorem atot14964 : totK PD2M8K2 D2M8K2.u14964 = [0, 79122610321, 516849799838, 871625768391, 284605934804, 13049727234, 0, 0] := by
  rw [show D2M8K2.u14964 = KTree.node D2M8K2.t14974 (nat_lit 32689410) (nat_lit 1208050040) (nat_lit 0) D2M8K2.t14975 from rfl, totK_node, tot14974, tot14975]
  decide +kernel

theorem arows14971 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14971 = true := by
  rw [show D2M8K2.u14971 = KTree.node D2M8K2.t14976 (nat_lit 32694544) (nat_lit 3688162118) (nat_lit 0) D2M8K2.t14977 from rfl, allE_node, rows14976, irow14971, rows14977]
  all_goals rfl

theorem atot14971 : totK PD2M8K2 D2M8K2.u14971 = [0, 244234480993, 820438971059, 636832040257, 84062790269, 1062926506, 0, 0] := by
  rw [show D2M8K2.u14971 = KTree.node D2M8K2.t14976 (nat_lit 32694544) (nat_lit 3688162118) (nat_lit 0) D2M8K2.t14977 from rfl, totK_node, tot14976, tot14977]
  decide +kernel

theorem arows14972 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14972 = true := by
  rw [show D2M8K2.u14972 = KTree.node D2M8K2.t14978 (nat_lit 32697355) (nat_lit 1605223022) (nat_lit 0) D2M8K2.t14979 from rfl, allE_node, rows14978, irow14972, rows14979]
  all_goals rfl

theorem atot14972 : totK PD2M8K2 D2M8K2.u14972 = [0, 262761283625, 782624883364, 642612833700, 116729531922, 3720136285, 0, 0] := by
  rw [show D2M8K2.u14972 = KTree.node D2M8K2.t14978 (nat_lit 32697355) (nat_lit 1605223022) (nat_lit 0) D2M8K2.t14979 from rfl, totK_node, tot14978, tot14979]
  decide +kernel

theorem arows14974 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14974 = true := by
  rw [show D2M8K2.u14974 = KTree.node D2M8K2.t14980 (nat_lit 32698865) (nat_lit 1581600980) (nat_lit 0) D2M8K2.t14981 from rfl, allE_node, rows14980, irow14974, rows14981]
  all_goals rfl

theorem atot14974 : totK PD2M8K2 D2M8K2.u14974 = [0, 165290289616, 737480808089, 765968741286, 138887971418, 1268739303, 0, 0] := by
  rw [show D2M8K2.u14974 = KTree.node D2M8K2.t14980 (nat_lit 32698865) (nat_lit 1581600980) (nat_lit 0) D2M8K2.t14981 from rfl, totK_node, tot14980, tot14981]
  decide +kernel

theorem arows14975 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14975 = true := by
  rw [show D2M8K2.u14975 = KTree.node D2M8K2.t14982 (nat_lit 32700557) (nat_lit 1518107584) (nat_lit 0) D2M8K2.t14983 from rfl, allE_node, rows14982, irow14975, rows14983]
  all_goals rfl

theorem atot14975 : totK PD2M8K2 D2M8K2.u14975 = [0, 0, 363351085373, 950541162427, 427540778385, 23230257759, 0, 0] := by
  rw [show D2M8K2.u14975 = KTree.node D2M8K2.t14982 (nat_lit 32700557) (nat_lit 1518107584) (nat_lit 0) D2M8K2.t14983 from rfl, totK_node, tot14982, tot14983]
  decide +kernel

theorem arows14978 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14978 = true := by
  rw [show D2M8K2.u14978 = KTree.node D2M8K2.t14984 (nat_lit 32702198) (nat_lit 3152973891) (nat_lit 0) D2M8K2.t14985 from rfl, allE_node, rows14984, irow14978, rows14985]
  all_goals rfl

theorem atot14978 : totK PD2M8K2 D2M8K2.u14978 = [0, 0, 226422817294, 791598403142, 603735731248, 74319808111, 1166720416, 0] := by
  rw [show D2M8K2.u14978 = KTree.node D2M8K2.t14984 (nat_lit 32702198) (nat_lit 3152973891) (nat_lit 0) D2M8K2.t14985 from rfl, totK_node, tot14984, tot14985]
  decide +kernel

theorem arows14979 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14979 = true := by
  rw [show D2M8K2.u14979 = KTree.node D2M8K2.t14986 (nat_lit 32704720) (nat_lit 3422012555) (nat_lit 0) D2M8K2.t14987 from rfl, allE_node, rows14986, irow14979, rows14987]
  all_goals rfl

theorem atot14979 : totK PD2M8K2 D2M8K2.u14979 = [0, 0, 394926802981, 929230165833, 465018547279, 25939405395, 0, 0] := by
  rw [show D2M8K2.u14979 = KTree.node D2M8K2.t14986 (nat_lit 32704720) (nat_lit 3422012555) (nat_lit 0) D2M8K2.t14987 from rfl, totK_node, tot14986, tot14987]
  decide +kernel

theorem arows14981 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14981 = true := by
  rw [show D2M8K2.u14981 = KTree.node D2M8K2.t14988 (nat_lit 32708057) (nat_lit 1401098683) (nat_lit 0) D2M8K2.t14989 from rfl, allE_node, rows14988, irow14981, rows14989]
  all_goals rfl

theorem atot14981 : totK PD2M8K2 D2M8K2.u14981 = [0, 0, 361731863927, 948128626897, 445609896161, 28386381190, 0, 0] := by
  rw [show D2M8K2.u14981 = KTree.node D2M8K2.t14988 (nat_lit 32708057) (nat_lit 1401098683) (nat_lit 0) D2M8K2.t14989 from rfl, totK_node, tot14988, tot14989]
  decide +kernel

theorem arows14982 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14982 = true := by
  rw [show D2M8K2.u14982 = KTree.node D2M8K2.t14990 (nat_lit 32709633) (nat_lit 1494423609) (nat_lit 0) D2M8K2.t14991 from rfl, allE_node, rows14990, irow14982, rows14991]
  all_goals rfl

theorem atot14982 : totK PD2M8K2 D2M8K2.u14982 = [0, 0, 87965506125, 650035647613, 803755157531, 170624429887, 5134755853, 0] := by
  rw [show D2M8K2.u14982 = KTree.node D2M8K2.t14990 (nat_lit 32709633) (nat_lit 1494423609) (nat_lit 0) D2M8K2.t14991 from rfl, totK_node, tot14990, tot14991]
  decide +kernel

theorem arows14986 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14986 = true := by
  rw [show D2M8K2.u14986 = KTree.node D2M8K2.t14992 (nat_lit 32715244) (nat_lit 3862190486) (nat_lit 0) D2M8K2.t14993 from rfl, allE_node, rows14992, irow14986, rows14993]
  all_goals rfl

theorem atot14986 : totK PD2M8K2 D2M8K2.u14986 = [0, 0, 428074994451, 954788841370, 343230678258, 14958066271, 0, 0] := by
  rw [show D2M8K2.u14986 = KTree.node D2M8K2.t14992 (nat_lit 32715244) (nat_lit 3862190486) (nat_lit 0) D2M8K2.t14993 from rfl, totK_node, tot14992, tot14993]
  decide +kernel

theorem arows14987 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14987 = true := by
  rw [show D2M8K2.u14987 = KTree.node D2M8K2.t14994 (nat_lit 32718900) (nat_lit 3108320044) (nat_lit 0) D2M8K2.t14995 from rfl, allE_node, rows14994, irow14987, rows14995]
  all_goals rfl

theorem atot14987 : totK PD2M8K2 D2M8K2.u14987 = [0, 78205854702, 418030835601, 835280967571, 435494336769, 33024743369, 0, 0] := by
  rw [show D2M8K2.u14987 = KTree.node D2M8K2.t14994 (nat_lit 32718900) (nat_lit 3108320044) (nat_lit 0) D2M8K2.t14995 from rfl, totK_node, tot14994, tot14995]
  decide +kernel

theorem arows14989 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14989 = true := by
  rw [show D2M8K2.u14989 = KTree.node D2M8K2.t14996 (nat_lit 32722518) (nat_lit 3839372377) (nat_lit 0) D2M8K2.t14997 from rfl, allE_node, rows14996, irow14989, rows14997]
  all_goals rfl

theorem atot14989 : totK PD2M8K2 D2M8K2.u14989 = [0, 328563570772, 926168430452, 492585331694, 31466307913, 0, 0, 0] := by
  rw [show D2M8K2.u14989 = KTree.node D2M8K2.t14996 (nat_lit 32722518) (nat_lit 3839372377) (nat_lit 0) D2M8K2.t14997 from rfl, totK_node, tot14996, tot14997]
  decide +kernel

theorem arows14990 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14990 = true := by
  rw [show D2M8K2.u14990 = KTree.node D2M8K2.t14998 (nat_lit 32724352) (nat_lit 3348568611) (nat_lit 0) D2M8K2.t14999 from rfl, allE_node, rows14998, irow14990, rows14999]
  all_goals rfl

theorem atot14990 : totK PD2M8K2 D2M8K2.u14990 = [0, 112177858867, 669602092807, 877988115797, 149818201905, 1369150432, 0, 0] := by
  rw [show D2M8K2.u14990 = KTree.node D2M8K2.t14998 (nat_lit 32724352) (nat_lit 3348568611) (nat_lit 0) D2M8K2.t14999 from rfl, totK_node, tot14998, tot14999]
  decide +kernel

theorem arows14993 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14993 = true := by
  rw [show D2M8K2.u14993 = KTree.node D2M8K2.t15000 (nat_lit 32726115) (nat_lit 3688078442) (nat_lit 0) D2M8K2.t15001 from rfl, allE_node, rows15000, irow14993, rows15001]
  all_goals rfl

theorem atot14993 : totK PD2M8K2 D2M8K2.u14993 = [0, 306443226379, 899057545606, 564002778742, 57655900901, 0, 0, 0] := by
  rw [show D2M8K2.u14993 = KTree.node D2M8K2.t15000 (nat_lit 32726115) (nat_lit 3688078442) (nat_lit 0) D2M8K2.t15001 from rfl, totK_node, tot15000, tot15001]
  decide +kernel

theorem arows14994 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14994 = true := by
  rw [show D2M8K2.u14994 = KTree.node D2M8K2.t15002 (nat_lit 32727697) (nat_lit 1176844442) (nat_lit 0) D2M8K2.t15003 from rfl, allE_node, rows15002, irow14994, rows15003]
  all_goals rfl

theorem atot14994 : totK PD2M8K2 D2M8K2.u14994 = [0, 18548618087, 348985897206, 903434333658, 487549243050, 32805585335, 0, 0] := by
  rw [show D2M8K2.u14994 = KTree.node D2M8K2.t15002 (nat_lit 32727697) (nat_lit 1176844442) (nat_lit 0) D2M8K2.t15003 from rfl, totK_node, tot15002, tot15003]
  decide +kernel

theorem arows14996 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14996 = true := by
  rw [show D2M8K2.u14996 = KTree.node D2M8K2.t15004 (nat_lit 32732675) (nat_lit 2831250951) (nat_lit 0) D2M8K2.t15005 from rfl, allE_node, rows15004, irow14996, rows15005]
  all_goals rfl

theorem atot14996 : totK PD2M8K2 D2M8K2.u14996 = [0, 382972526000, 934544296295, 472020042975, 35167089884, 0, 0, 0] := by
  rw [show D2M8K2.u14996 = KTree.node D2M8K2.t15004 (nat_lit 32732675) (nat_lit 2831250951) (nat_lit 0) D2M8K2.t15005 from rfl, totK_node, tot15004, tot15005]
  decide +kernel

theorem arows14997 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14997 = true := by
  rw [show D2M8K2.u14997 = KTree.node D2M8K2.t15006 (nat_lit 32733913) (nat_lit 1219466748) (nat_lit 0) D2M8K2.t15007 from rfl, allE_node, rows15006, irow14997, rows15007]
  all_goals rfl

theorem atot14997 : totK PD2M8K2 D2M8K2.u14997 = [0, 38150555787, 520467470471, 910755207805, 288150088052, 13189998508, 0, 0] := by
  rw [show D2M8K2.u14997 = KTree.node D2M8K2.t15006 (nat_lit 32733913) (nat_lit 1219466748) (nat_lit 0) D2M8K2.t15007 from rfl, totK_node, tot15006, tot15007]
  decide +kernel

theorem arows15002 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15002 = true := by
  rw [show D2M8K2.u15002 = KTree.node D2M8K2.t15008 (nat_lit 32735736) (nat_lit 2686065782) (nat_lit 0) D2M8K2.t15009 from rfl, allE_node, rows15008, irow15002, rows15009]
  all_goals rfl

theorem atot15002 : totK PD2M8K2 D2M8K2.u15002 = [0, 323505701660, 902109854913, 540633383947, 49589440628, 0, 0, 0] := by
  rw [show D2M8K2.u15002 = KTree.node D2M8K2.t15008 (nat_lit 32735736) (nat_lit 2686065782) (nat_lit 0) D2M8K2.t15009 from rfl, totK_node, tot15008, tot15009]
  decide +kernel

theorem arows15003 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15003 = true := by
  rw [show D2M8K2.u15003 = KTree.node D2M8K2.t15010 (nat_lit 32738184) (nat_lit 3464934730) (nat_lit 0) D2M8K2.t15011 from rfl, allE_node, rows15010, irow15003, rows15011]
  all_goals rfl

theorem atot15003 : totK PD2M8K2 D2M8K2.u15003 = [0, 173511939259, 692459420842, 749069010450, 159057713992, 4917684815, 0, 0] := by
  rw [show D2M8K2.u15003 = KTree.node D2M8K2.t15010 (nat_lit 32738184) (nat_lit 3464934730) (nat_lit 0) D2M8K2.t15011 from rfl, totK_node, tot15010, tot15011]
  decide +kernel

theorem arows15005 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15005 = true := by
  rw [show D2M8K2.u15005 = KTree.node D2M8K2.t15012 (nat_lit 32739776) (nat_lit 3530460818) (nat_lit 0) D2M8K2.t15013 from rfl, allE_node, rows15012, irow15005, rows15013]
  all_goals rfl

theorem atot15005 : totK PD2M8K2 D2M8K2.u15005 = [0, 254577982652, 806002022534, 654707077786, 98829938660, 1268739303, 0, 0] := by
  rw [show D2M8K2.u15005 = KTree.node D2M8K2.t15012 (nat_lit 32739776) (nat_lit 3530460818) (nat_lit 0) D2M8K2.t15013 from rfl, totK_node, tot15012, tot15013]
  decide +kernel

theorem arows15006 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15006 = true := by
  rw [show D2M8K2.u15006 = KTree.node D2M8K2.t15014 (nat_lit 32741425) (nat_lit 1483627708) (nat_lit 0) D2M8K2.t15015 from rfl, allE_node, rows15014, irow15006, rows15015]
  all_goals rfl

theorem atot15006 : totK PD2M8K2 D2M8K2.u15006 = [0, 0, 430535345631, 959544487804, 372624699165, 20707334622, 0, 0] := by
  rw [show D2M8K2.u15006 = KTree.node D2M8K2.t15014 (nat_lit 32741425) (nat_lit 1483627708) (nat_lit 0) D2M8K2.t15015 from rfl, totK_node, tot15014, tot15015]
  decide +kernel

theorem arows15009 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15009 = true := by
  rw [show D2M8K2.u15009 = KTree.node D2M8K2.t15016 (nat_lit 32743329) (nat_lit 1515743430) (nat_lit 0) D2M8K2.t15017 from rfl, allE_node, rows15016, irow15009, rows15017]
  all_goals rfl

theorem atot15009 : totK PD2M8K2 D2M8K2.u15009 = [0, 0, 312773109630, 921920261576, 471468426411, 23130816536, 0, 0] := by
  rw [show D2M8K2.u15009 = KTree.node D2M8K2.t15016 (nat_lit 32743329) (nat_lit 1515743430) (nat_lit 0) D2M8K2.t15017 from rfl, totK_node, tot15016, tot15017]
  decide +kernel

theorem arows15010 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15010 = true := by
  rw [show D2M8K2.u15010 = KTree.node D2M8K2.t15018 (nat_lit 32745914) (nat_lit 4294967296) (nat_lit 0) D2M8K2.t15019 from rfl, allE_node, rows15018, irow15010, rows15019]
  all_goals rfl

theorem atot15010 : totK PD2M8K2 D2M8K2.u15010 = [0, 0, 248312536677, 803865732933, 642900068846, 79512255991, 1200365979, 0] := by
  rw [show D2M8K2.u15010 = KTree.node D2M8K2.t15018 (nat_lit 32745914) (nat_lit 4294967296) (nat_lit 0) D2M8K2.t15019 from rfl, totK_node, tot15018, tot15019]
  decide +kernel

theorem arows15012 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15012 = true := by
  rw [show D2M8K2.u15012 = KTree.node D2M8K2.t15020 (nat_lit 32752635) (nat_lit 2926925330) (nat_lit 0) D2M8K2.t15021 from rfl, allE_node, rows15020, irow15012, rows15021]
  all_goals rfl

theorem atot15012 : totK PD2M8K2 D2M8K2.u15012 = [0, 0, 427745457658, 962834777576, 402395315523, 21978780744, 0, 0] := by
  rw [show D2M8K2.u15012 = KTree.node D2M8K2.t15020 (nat_lit 32752635) (nat_lit 2926925330) (nat_lit 0) D2M8K2.t15021 from rfl, totK_node, tot15020, tot15021]
  decide +kernel

theorem arows15013 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15013 = true := by
  rw [show D2M8K2.u15013 = KTree.node D2M8K2.t15022 (nat_lit 32754170) (nat_lit 3979444259) (nat_lit 0) D2M8K2.t15023 from rfl, allE_node, rows15022, irow15013, rows15023]
  all_goals rfl

theorem atot15013 : totK PD2M8K2 D2M8K2.u15013 = [0, 0, 166524922457, 736272886894, 721291867298, 106871406960, 1135526696, 0] := by
  rw [show D2M8K2.u15013 = KTree.node D2M8K2.t15022 (nat_lit 32754170) (nat_lit 3979444259) (nat_lit 0) D2M8K2.t15023 from rfl, totK_node, tot15022, tot15023]
  decide +kernel

theorem arows15017 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15017 = true := by
  rw [show D2M8K2.u15017 = KTree.node D2M8K2.t15024 (nat_lit 32756290) (nat_lit 3815583622) (nat_lit 0) D2M8K2.t15025 from rfl, allE_node, rows15024, irow15017, rows15025]
  all_goals rfl

theorem atot15017 : totK PD2M8K2 D2M8K2.u15017 = [0, 0, 376442459948, 843399669821, 429451903446, 84132765184, 4028038878, 0] := by
  rw [show D2M8K2.u15017 = KTree.node D2M8K2.t15024 (nat_lit 32756290) (nat_lit 3815583622) (nat_lit 0) D2M8K2.t15025 from rfl, totK_node, tot15024, tot15025]
  decide +kernel

theorem arows15018 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15018 = true := by
  rw [show D2M8K2.u15018 = KTree.node D2M8K2.t15026 (nat_lit 32760171) (nat_lit 3196594994) (nat_lit 0) D2M8K2.t15027 from rfl, allE_node, rows15026, irow15018, rows15027]
  all_goals rfl

theorem atot15018 : totK PD2M8K2 D2M8K2.u15018 = [0, 0, 359342411105, 946465464587, 462936792798, 25552881246, 0, 0] := by
  rw [show D2M8K2.u15018 = KTree.node D2M8K2.t15026 (nat_lit 32760171) (nat_lit 3196594994) (nat_lit 0) D2M8K2.t15027 from rfl, totK_node, tot15026, tot15027]
  decide +kernel

theorem arows15020 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15020 = true := by
  rw [show D2M8K2.u15020 = KTree.node D2M8K2.t15028 (nat_lit 32805182) (nat_lit 1743727942) (nat_lit 0) D2M8K2.t15029 from rfl, allE_node, rows15028, irow15020, rows15029]
  all_goals rfl

theorem atot15020 : totK PD2M8K2 D2M8K2.u15020 = [0, 379188357549, 908150377798, 416865551062, 73707250656, 9758758476, 0, 0] := by
  rw [show D2M8K2.u15020 = KTree.node D2M8K2.t15028 (nat_lit 32805182) (nat_lit 1743727942) (nat_lit 0) D2M8K2.t15029 from rfl, totK_node, tot15028, tot15029]
  decide +kernel

theorem arows15021 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15021 = true := by
  rw [show D2M8K2.u15021 = KTree.node D2M8K2.t15030 (nat_lit 32806776) (nat_lit 3552761585) (nat_lit 0) D2M8K2.t15031 from rfl, allE_node, rows15030, irow15021, rows15031]
  all_goals rfl

theorem atot15021 : totK PD2M8K2 D2M8K2.u15021 = [0, 114948887837, 684956793270, 869387880669, 138342365723, 1369150432, 0, 0] := by
  rw [show D2M8K2.u15021 = KTree.node D2M8K2.t15030 (nat_lit 32806776) (nat_lit 3552761585) (nat_lit 0) D2M8K2.t15031 from rfl, totK_node, tot15030, tot15031]
  decide +kernel

theorem arows15024 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15024 = true := by
  rw [show D2M8K2.u15024 = KTree.node D2M8K2.t15032 (nat_lit 32808780) (nat_lit 2241201828) (nat_lit 0) D2M8K2.t15033 from rfl, allE_node, rows15032, irow15024, rows15033]
  all_goals rfl

theorem atot15024 : totK PD2M8K2 D2M8K2.u15024 = [0, 349808447617, 931274661476, 516619013073, 40318406398, 0, 0, 0] := by
  rw [show D2M8K2.u15024 = KTree.node D2M8K2.t15032 (nat_lit 32808780) (nat_lit 2241201828) (nat_lit 0) D2M8K2.t15033 from rfl, totK_node, tot15032, tot15033]
  decide +kernel

theorem arows15025 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15025 = true := by
  rw [show D2M8K2.u15025 = KTree.node D2M8K2.t15034 (nat_lit 32810266) (nat_lit 3178538980) (nat_lit 0) D2M8K2.t15035 from rfl, allE_node, rows15034, irow15025, rows15035]
  all_goals rfl

theorem atot15025 : totK PD2M8K2 D2M8K2.u15025 = [0, 0, 402457007052, 950967180086, 415361452258, 23602487642, 0, 0] := by
  rw [show D2M8K2.u15025 = KTree.node D2M8K2.t15034 (nat_lit 32810266) (nat_lit 3178538980) (nat_lit 0) D2M8K2.t15035 from rfl, totK_node, tot15034, tot15035]
  decide +kernel

theorem arows15027 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15027 = true := by
  rw [show D2M8K2.u15027 = KTree.node D2M8K2.t15036 (nat_lit 32811638) (nat_lit 3976190923) (nat_lit 0) D2M8K2.t15037 from rfl, allE_node, rows15036, irow15027, rows15037]
  all_goals rfl

theorem atot15027 : totK PD2M8K2 D2M8K2.u15027 = [0, 298907427953, 791270712926, 570001413131, 144755521529, 6804944647, 0, 0] := by
  rw [show D2M8K2.u15027 = KTree.node D2M8K2.t15036 (nat_lit 32811638) (nat_lit 3976190923) (nat_lit 0) D2M8K2.t15037 from rfl, totK_node, tot15036, tot15037]
  decide +kernel

theorem arows15028 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15028 = true := by
  rw [show D2M8K2.u15028 = KTree.node D2M8K2.t15038 (nat_lit 32813134) (nat_lit 3867413933) (nat_lit 0) D2M8K2.t15039 from rfl, allE_node, rows15038, irow15028, rows15039]
  all_goals rfl

theorem atot15028 : totK PD2M8K2 D2M8K2.u15028 = [0, 122531782185, 646859665363, 806548405013, 198912722534, 7611474319, 0, 0] := by
  rw [show D2M8K2.u15028 = KTree.node D2M8K2.t15038 (nat_lit 32813134) (nat_lit 3867413933) (nat_lit 0) D2M8K2.t15039 from rfl, totK_node, tot15038, tot15039]
  decide +kernel

theorem arows15034 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15034 = true := by
  rw [show D2M8K2.u15034 = KTree.node D2M8K2.t15040 (nat_lit 32815054) (nat_lit 3967757557) (nat_lit 0) D2M8K2.t15041 from rfl, allE_node, rows15040, irow15034, rows15041]
  all_goals rfl

theorem atot15034 : totK PD2M8K2 D2M8K2.u15034 = [0, 274684781547, 802950327557, 629415761631, 98961777532, 946121569, 0, 0] := by
  rw [show D2M8K2.u15034 = KTree.node D2M8K2.t15040 (nat_lit 32815054) (nat_lit 3967757557) (nat_lit 0) D2M8K2.t15041 from rfl, totK_node, tot15040, tot15041]
  decide +kernel

theorem arows15035 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15035 = true := by
  rw [show D2M8K2.u15035 = KTree.node D2M8K2.t15042 (nat_lit 32816548) (nat_lit 2306319960) (nat_lit 0) D2M8K2.t15043 from rfl, allE_node, rows15042, irow15035, rows15043]
  all_goals rfl

theorem atot15035 : totK PD2M8K2 D2M8K2.u15035 = [0, 146966136639, 659360004558, 769178324387, 200650631501, 7680527984, 0, 0] := by
  rw [show D2M8K2.u15035 = KTree.node D2M8K2.t15042 (nat_lit 32816548) (nat_lit 2306319960) (nat_lit 0) D2M8K2.t15043 from rfl, totK_node, tot15042, tot15043]
  decide +kernel

theorem arows15037 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15037 = true := by
  rw [show D2M8K2.u15037 = KTree.node D2M8K2.t15044 (nat_lit 32821877) (nat_lit 2073221722) (nat_lit 0) D2M8K2.t15045 from rfl, allE_node, rows15044, irow15037, rows15045]
  all_goals rfl

theorem atot15037 : totK PD2M8K2 D2M8K2.u15037 = [0, 265490514522, 806422650646, 645880307773, 106099155581, 976161439, 0, 0] := by
  rw [show D2M8K2.u15037 = KTree.node D2M8K2.t15044 (nat_lit 32821877) (nat_lit 2073221722) (nat_lit 0) D2M8K2.t15045 from rfl, totK_node, tot15044, tot15045]
  decide +kernel

theorem arows15038 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15038 = true := by
  rw [show D2M8K2.u15038 = KTree.node D2M8K2.t15046 (nat_lit 32823300) (nat_lit 2884972150) (nat_lit 0) D2M8K2.t15047 from rfl, allE_node, rows15046, irow15038, rows15047]
  all_goals rfl

theorem atot15038 : totK PD2M8K2 D2M8K2.u15038 = [0, 182497872290, 746296825648, 756835574815, 137145068622, 1268739303, 0, 0] := by
  rw [show D2M8K2.u15038 = KTree.node D2M8K2.t15046 (nat_lit 32823300) (nat_lit 2884972150) (nat_lit 0) D2M8K2.t15047 from rfl, totK_node, tot15046, tot15047]
  decide +kernel

theorem arows15041 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15041 = true := by
  rw [show D2M8K2.u15041 = KTree.node D2M8K2.t15048 (nat_lit 32824962) (nat_lit 2894651604) (nat_lit 0) D2M8K2.t15049 from rfl, allE_node, rows15048, irow15041, rows15049]
  all_goals rfl

theorem atot15041 : totK PD2M8K2 D2M8K2.u15041 = [0, 0, 366793209774, 954119406193, 421582113218, 23301045897, 0, 0] := by
  rw [show D2M8K2.u15041 = KTree.node D2M8K2.t15048 (nat_lit 32824962) (nat_lit 2894651604) (nat_lit 0) D2M8K2.t15049 from rfl, totK_node, tot15048, tot15049]
  decide +kernel

theorem arows15042 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15042 = true := by
  rw [show D2M8K2.u15042 = KTree.node D2M8K2.t15050 (nat_lit 32826578) (nat_lit 3701083268) (nat_lit 0) D2M8K2.t15051 from rfl, allE_node, rows15050, irow15042, rows15051]
  all_goals rfl

theorem atot15042 : totK PD2M8K2 D2M8K2.u15042 = [0, 0, 236811680064, 795199956609, 604466534257, 87340088839, 1288491354, 0] := by
  rw [show D2M8K2.u15042 = KTree.node D2M8K2.t15050 (nat_lit 32826578) (nat_lit 3701083268) (nat_lit 0) D2M8K2.t15051 from rfl, totK_node, tot15050, tot15051]
  decide +kernel

theorem arows15044 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15044 = true := by
  rw [show D2M8K2.u15044 = KTree.node D2M8K2.t15052 (nat_lit 32828956) (nat_lit 3875912919) (nat_lit 0) D2M8K2.t15053 from rfl, allE_node, rows15052, irow15044, rows15053]
  all_goals rfl

theorem atot15044 : totK PD2M8K2 D2M8K2.u15044 = [0, 0, 263838190271, 845350640958, 622072630893, 57621925347, 0, 0] := by
  rw [show D2M8K2.u15044 = KTree.node D2M8K2.t15052 (nat_lit 32828956) (nat_lit 3875912919) (nat_lit 0) D2M8K2.t15053 from rfl, totK_node, tot15052, tot15053]
  decide +kernel

theorem arows15045 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15045 = true := by
  rw [show D2M8K2.u15045 = KTree.node D2M8K2.t15054 (nat_lit 32832103) (nat_lit 1514678520) (nat_lit 0) D2M8K2.t15055 from rfl, allE_node, rows15054, irow15045, rows15055]
  all_goals rfl

theorem atot15045 : totK PD2M8K2 D2M8K2.u15045 = [0, 0, 418046323234, 957837657581, 406380730815, 26536785720, 0, 0] := by
  rw [show D2M8K2.u15045 = KTree.node D2M8K2.t15054 (nat_lit 32832103) (nat_lit 1514678520) (nat_lit 0) D2M8K2.t15055 from rfl, totK_node, tot15054, tot15055]
  decide +kernel

theorem arows15049 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15049 = true := by
  rw [show D2M8K2.u15049 = KTree.node D2M8K2.t15056 (nat_lit 32833710) (nat_lit 3726115627) (nat_lit 0) D2M8K2.t15057 from rfl, allE_node, rows15056, irow15049, rows15057]
  all_goals rfl

theorem atot15049 : totK PD2M8K2 D2M8K2.u15049 = [0, 0, 154317133126, 714327466842, 728048296371, 124906131465, 2083783650, 0] := by
  rw [show D2M8K2.u15049 = KTree.node D2M8K2.t15056 (nat_lit 32833710) (nat_lit 3726115627) (nat_lit 0) D2M8K2.t15057 from rfl, totK_node, tot15056, tot15057]
  decide +kernel

theorem arows15050 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15050 = true := by
  rw [show D2M8K2.u15050 = KTree.node D2M8K2.t15058 (nat_lit 32835808) (nat_lit 3514856368) (nat_lit 0) D2M8K2.t15059 from rfl, allE_node, rows15058, irow15050, rows15059]
  all_goals rfl

theorem atot15050 : totK PD2M8K2 D2M8K2.u15050 = [0, 0, 305299177221, 858317237380, 527442255075, 66189495618, 2703270515, 0] := by
  rw [show D2M8K2.u15050 = KTree.node D2M8K2.t15058 (nat_lit 32835808) (nat_lit 3514856368) (nat_lit 0) D2M8K2.t15059 from rfl, totK_node, tot15058, tot15059]
  decide +kernel

theorem arows15052 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15052 = true := by
  rw [show D2M8K2.u15052 = KTree.node D2M8K2.t15060 (nat_lit 32837380) (nat_lit 3335261616) (nat_lit 0) D2M8K2.t15061 from rfl, allE_node, rows15060, irow15052, rows15061]
  all_goals rfl

theorem atot15052 : totK PD2M8K2 D2M8K2.u15052 = [0, 0, 109974802622, 675576616017, 764262942061, 157943006657, 4838243418, 0] := by
  rw [show D2M8K2.u15052 = KTree.node D2M8K2.t15060 (nat_lit 32837380) (nat_lit 3335261616) (nat_lit 0) D2M8K2.t15061 from rfl, totK_node, tot15060, tot15061]
  decide +kernel

theorem arows15053 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15053 = true := by
  rw [show D2M8K2.u15053 = KTree.node D2M8K2.t15062 (nat_lit 32842904) (nat_lit 2508143077) (nat_lit 0) D2M8K2.t15063 from rfl, allE_node, rows15062, irow15053, rows15063]
  all_goals rfl

theorem atot15053 : totK PD2M8K2 D2M8K2.u15053 = [0, 0, 349111930253, 916605837503, 496963635602, 42010575485, 0, 0] := by
  rw [show D2M8K2.u15053 = KTree.node D2M8K2.t15062 (nat_lit 32842904) (nat_lit 2508143077) (nat_lit 0) D2M8K2.t15063 from rfl, totK_node, tot15062, tot15063]
  decide +kernel

theorem arows15056 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15056 = true := by
  rw [show D2M8K2.u15056 = KTree.node D2M8K2.t15064 (nat_lit 32844425) (nat_lit 1343186591) (nat_lit 0) D2M8K2.t15065 from rfl, allE_node, rows15064, irow15056, rows15065]
  all_goals rfl

theorem atot15056 : totK PD2M8K2 D2M8K2.u15056 = [0, 0, 93587166913, 585385053931, 847677719353, 229142167849, 5842784248, 0] := by
  rw [show D2M8K2.u15056 = KTree.node D2M8K2.t15064 (nat_lit 32844425) (nat_lit 1343186591) (nat_lit 0) D2M8K2.t15065 from rfl, totK_node, tot15064, tot15065]
  decide +kernel

theorem arows15057 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15057 = true := by
  rw [show D2M8K2.u15057 = KTree.node D2M8K2.t15066 (nat_lit 32846072) (nat_lit 3841767734) (nat_lit 0) D2M8K2.t15067 from rfl, allE_node, rows15066, irow15057, rows15067]
  all_goals rfl

theorem atot15057 : totK PD2M8K2 D2M8K2.u15057 = [0, 267847118239, 682445575878, 409914182816, 274809583765, 151488759652, 14896018734, 0] := by
  rw [show D2M8K2.u15057 = KTree.node D2M8K2.t15066 (nat_lit 32846072) (nat_lit 3841767734) (nat_lit 0) D2M8K2.t15067 from rfl, totK_node, tot15066, tot15067]
  decide +kernel

theorem arows15059 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15059 = true := by
  rw [show D2M8K2.u15059 = KTree.node D2M8K2.t15068 (nat_lit 32847565) (nat_lit 1391987541) (nat_lit 0) D2M8K2.t15069 from rfl, allE_node, rows15068, irow15059, rows15069]
  all_goals rfl

theorem atot15059 : totK PD2M8K2 D2M8K2.u15059 = [0, 174605525350, 741098532396, 768108604327, 127877567186, 1369150432, 0, 0] := by
  rw [show D2M8K2.u15059 = KTree.node D2M8K2.t15068 (nat_lit 32847565) (nat_lit 1391987541) (nat_lit 0) D2M8K2.t15069 from rfl, totK_node, tot15068, tot15069]
  decide +kernel

theorem arows15060 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15060 = true := by
  rw [show D2M8K2.u15060 = KTree.node D2M8K2.t15070 (nat_lit 32853128) (nat_lit 3865834180) (nat_lit 0) D2M8K2.t15071 from rfl, allE_node, rows15070, irow15060, rows15071]
  all_goals rfl

theorem atot15060 : totK PD2M8K2 D2M8K2.u15060 = [0, 310713798304, 865297906477, 569981890211, 59634554732, 0, 0, 0] := by
  rw [show D2M8K2.u15060 = KTree.node D2M8K2.t15070 (nat_lit 32853128) (nat_lit 3865834180) (nat_lit 0) D2M8K2.t15071 from rfl, totK_node, tot15070, tot15071]
  decide +kernel

theorem arows15065 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15065 = true := by
  rw [show D2M8K2.u15065 = KTree.node D2M8K2.t15072 (nat_lit 32854600) (nat_lit 3648899999) (nat_lit 0) D2M8K2.t15073 from rfl, allE_node, rows15072, irow15065, rows15073]
  all_goals rfl

theorem atot15065 : totK PD2M8K2 D2M8K2.u15065 = [0, 105920131535, 629551629145, 822968844641, 209795043181, 9587713104, 0, 0] := by
  rw [show D2M8K2.u15065 = KTree.node D2M8K2.t15072 (nat_lit 32854600) (nat_lit 3648899999) (nat_lit 0) D2M8K2.t15073 from rfl, totK_node, tot15072, tot15073]
  decide +kernel

theorem arows15066 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15066 = true := by
  rw [show D2M8K2.u15066 = KTree.node D2M8K2.t15074 (nat_lit 32856467) (nat_lit 2901676247) (nat_lit 0) D2M8K2.t15075 from rfl, allE_node, rows15074, irow15066, rows15075]
  all_goals rfl

theorem atot15066 : totK PD2M8K2 D2M8K2.u15066 = [0, 272943117133, 783219993371, 612160387172, 115031572110, 3462014130, 0, 0] := by
  rw [show D2M8K2.u15066 = KTree.node D2M8K2.t15074 (nat_lit 32856467) (nat_lit 2901676247) (nat_lit 0) D2M8K2.t15075 from rfl, totK_node, tot15074, tot15075]
  decide +kernel

theorem arows15068 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15068 = true := by
  rw [show D2M8K2.u15068 = KTree.node D2M8K2.t15076 (nat_lit 32857999) (nat_lit 2431606759) (nat_lit 0) D2M8K2.t15077 from rfl, allE_node, rows15076, irow15068, rows15077]
  all_goals rfl

theorem atot15068 : totK PD2M8K2 D2M8K2.u15068 = [0, 140110859336, 646688574111, 770914936944, 205730107407, 9668735432, 0, 0] := by
  rw [show D2M8K2.u15068 = KTree.node D2M8K2.t15076 (nat_lit 32857999) (nat_lit 2431606759) (nat_lit 0) D2M8K2.t15077 from rfl, totK_node, tot15076, tot15077]
  decide +kernel

theorem arows15069 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15069 = true := by
  rw [show D2M8K2.u15069 = KTree.node D2M8K2.t15078 (nat_lit 32859798) (nat_lit 3666576963) (nat_lit 0) D2M8K2.t15079 from rfl, allE_node, rows15078, irow15069, rows15079]
  all_goals rfl

theorem atot15069 : totK PD2M8K2 D2M8K2.u15069 = [0, 240846464013, 754067788084, 637803120761, 118229153051, 3581949829, 0, 0] := by
  rw [show D2M8K2.u15069 = KTree.node D2M8K2.t15078 (nat_lit 32859798) (nat_lit 3666576963) (nat_lit 0) D2M8K2.t15079 from rfl, totK_node, tot15078, tot15079]
  decide +kernel

theorem arows15072 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15072 = true := by
  rw [show D2M8K2.u15072 = KTree.node D2M8K2.t15080 (nat_lit 32861438) (nat_lit 2680801870) (nat_lit 0) D2M8K2.t15081 from rfl, allE_node, rows15080, irow15072, rows15081]
  all_goals rfl

theorem atot15072 : totK PD2M8K2 D2M8K2.u15072 = [0, 156816874191, 739496209411, 770342113190, 107331261449, 1096505104, 0, 0] := by
  rw [show D2M8K2.u15072 = KTree.node D2M8K2.t15080 (nat_lit 32861438) (nat_lit 2680801870) (nat_lit 0) D2M8K2.t15081 from rfl, totK_node, tot15080, tot15081]
  decide +kernel

theorem arows15073 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15073 = true := by
  rw [show D2M8K2.u15073 = KTree.node D2M8K2.t15082 (nat_lit 32863474) (nat_lit 3957355096) (nat_lit 0) D2M8K2.t15083 from rfl, allE_node, rows15082, irow15073, rows15083]
  all_goals rfl

theorem atot15073 : totK PD2M8K2 D2M8K2.u15073 = [0, 315584361262, 807207917429, 562008206360, 110404311704, 3884009855, 0, 0] := by
  rw [show D2M8K2.u15073 = KTree.node D2M8K2.t15082 (nat_lit 32863474) (nat_lit 3957355096) (nat_lit 0) D2M8K2.t15083 from rfl, totK_node, tot15082, tot15083]
  decide +kernel

theorem arows15075 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15075 = true := by
  rw [show D2M8K2.u15075 = KTree.node D2M8K2.t15084 (nat_lit 32864955) (nat_lit 3014409101) (nat_lit 0) D2M8K2.t15085 from rfl, allE_node, rows15084, irow15075, rows15085]
  all_goals rfl

theorem atot15075 : totK PD2M8K2 D2M8K2.u15075 = [0, 107971457226, 629256190581, 843198563457, 212576286471, 4967996017, 0, 0] := by
  rw [show D2M8K2.u15075 = KTree.node D2M8K2.t15084 (nat_lit 32864955) (nat_lit 3014409101) (nat_lit 0) D2M8K2.t15085 from rfl, totK_node, tot15084, tot15085]
  decide +kernel

theorem arows15076 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15076 = true := by
  rw [show D2M8K2.u15076 = KTree.node D2M8K2.t15086 (nat_lit 32866643) (nat_lit 2861354393) (nat_lit 0) D2M8K2.t15087 from rfl, allE_node, rows15086, irow15076, rows15087]
  all_goals rfl

theorem atot15076 : totK PD2M8K2 D2M8K2.u15076 = [0, 0, 392082062986, 948093618994, 415709127505, 26691696689, 0, 0] := by
  rw [show D2M8K2.u15076 = KTree.node D2M8K2.t15086 (nat_lit 32866643) (nat_lit 2861354393) (nat_lit 0) D2M8K2.t15087 from rfl, totK_node, tot15086, tot15087]
  decide +kernel

theorem arows15080 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15080 = true := by
  rw [show D2M8K2.u15080 = KTree.node D2M8K2.t15088 (nat_lit 32868143) (nat_lit 2778802946) (nat_lit 0) D2M8K2.t15089 from rfl, allE_node, rows15088, irow15080, rows15089]
  all_goals rfl

theorem atot15080 : totK PD2M8K2 D2M8K2.u15080 = [0, 0, 192083430212, 762878896832, 669986162218, 115212015805, 1369150432, 0] := by
  rw [show D2M8K2.u15080 = KTree.node D2M8K2.t15088 (nat_lit 32868143) (nat_lit 2778802946) (nat_lit 0) D2M8K2.t15089 from rfl, totK_node, tot15088, tot15089]
  decide +kernel

theorem arows15081 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15081 = true := by
  rw [show D2M8K2.u15081 = KTree.node D2M8K2.t15090 (nat_lit 32873697) (nat_lit 1659972361) (nat_lit 0) D2M8K2.t15091 from rfl, allE_node, rows15090, irow15081, rows15091]
  all_goals rfl

theorem atot15081 : totK PD2M8K2 D2M8K2.u15081 = [0, 0, 275794955328, 875224414634, 565537508002, 50994099177, 0, 0] := by
  rw [show D2M8K2.u15081 = KTree.node D2M8K2.t15090 (nat_lit 32873697) (nat_lit 1659972361) (nat_lit 0) D2M8K2.t15091 from rfl, totK_node, tot15090, tot15091]
  decide +kernel

theorem arows15083 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15083 = true := by
  rw [show D2M8K2.u15083 = KTree.node D2M8K2.t15092 (nat_lit 32877013) (nat_lit 1267650260) (nat_lit 0) D2M8K2.t15093 from rfl, allE_node, rows15092, irow15083, rows15093]
  all_goals rfl

theorem atot15083 : totK PD2M8K2 D2M8K2.u15083 = [0, 0, 385707750071, 959021518335, 416116777619, 16633215577, 0, 0] := by
  rw [show D2M8K2.u15083 = KTree.node D2M8K2.t15092 (nat_lit 32877013) (nat_lit 1267650260) (nat_lit 0) D2M8K2.t15093 from rfl, totK_node, tot15092, tot15093]
  decide +kernel

theorem arows15084 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15084 = true := by
  rw [show D2M8K2.u15084 = KTree.node D2M8K2.t15094 (nat_lit 32878586) (nat_lit 3894460552) (nat_lit 0) D2M8K2.t15095 from rfl, allE_node, rows15094, irow15084, rows15095]
  all_goals rfl

theorem atot15084 : totK PD2M8K2 D2M8K2.u15084 = [0, 0, 378008974836, 939827515740, 408908322116, 21336897897, 0, 0] := by
  rw [show D2M8K2.u15084 = KTree.node D2M8K2.t15094 (nat_lit 32878586) (nat_lit 3894460552) (nat_lit 0) D2M8K2.t15095 from rfl, totK_node, tot15094, tot15095]
  decide +kernel

theorem arows15087 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15087 = true := by
  rw [show D2M8K2.u15087 = KTree.node D2M8K2.t15096 (nat_lit 32881638) (nat_lit 3823146296) (nat_lit 0) D2M8K2.t15097 from rfl, allE_node, rows15096, irow15087, rows15097]
  all_goals rfl

theorem atot15087 : totK PD2M8K2 D2M8K2.u15087 = [0, 0, 345467526429, 938585721763, 445378723981, 23445005681, 0, 0] := by
  rw [show D2M8K2.u15087 = KTree.node D2M8K2.t15096 (nat_lit 32881638) (nat_lit 3823146296) (nat_lit 0) D2M8K2.t15097 from rfl, totK_node, tot15096, tot15097]
  decide +kernel

theorem arows15088 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15088 = true := by
  rw [show D2M8K2.u15088 = KTree.node D2M8K2.t15098 (nat_lit 32885286) (nat_lit 3780083652) (nat_lit 0) D2M8K2.t15099 from rfl, allE_node, rows15098, irow15088, rows15099]
  all_goals rfl

theorem atot15088 : totK PD2M8K2 D2M8K2.u15088 = [0, 108844600523, 509737301610, 780151223822, 374306754886, 25732277379, 0, 0] := by
  rw [show D2M8K2.u15088 = KTree.node D2M8K2.t15098 (nat_lit 32885286) (nat_lit 3780083652) (nat_lit 0) D2M8K2.t15099 from rfl, totK_node, tot15098, tot15099]
  decide +kernel

theorem arows15090 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15090 = true := by
  rw [show D2M8K2.u15090 = KTree.node D2M8K2.t15100 (nat_lit 32929985) (nat_lit 2218671823) (nat_lit 0) D2M8K2.t15101 from rfl, allE_node, rows15100, irow15090, rows15101]
  all_goals rfl

theorem atot15090 : totK PD2M8K2 D2M8K2.u15090 = [0, 310279434488, 887789620843, 534302251254, 45604395822, 0, 0, 0] := by
  rw [show D2M8K2.u15090 = KTree.node D2M8K2.t15100 (nat_lit 32929985) (nat_lit 2218671823) (nat_lit 0) D2M8K2.t15101 from rfl, totK_node, tot15100, tot15101]
  decide +kernel

theorem arows15091 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15091 = true := by
  rw [show D2M8K2.u15091 = KTree.node D2M8K2.t15102 (nat_lit 32931942) (nat_lit 3669340041) (nat_lit 0) D2M8K2.t15103 from rfl, allE_node, rows15102, irow15091, rows15103]
  all_goals rfl

theorem atot15091 : totK PD2M8K2 D2M8K2.u15091 = [0, 162750957962, 693389538521, 820337914570, 149401607643, 1369150432, 0, 0] := by
  rw [show D2M8K2.u15091 = KTree.node D2M8K2.t15102 (nat_lit 32931942) (nat_lit 3669340041) (nat_lit 0) D2M8K2.t15103 from rfl, totK_node, tot15102, tot15103]
  decide +kernel

theorem arows15099 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15099 = true := by
  rw [show D2M8K2.u15099 = KTree.node D2M8K2.t15104 (nat_lit 32933873) (nat_lit 1579302274) (nat_lit 0) D2M8K2.t15105 from rfl, allE_node, rows15104, irow15099, rows15105]
  all_goals rfl

theorem atot15099 : totK PD2M8K2 D2M8K2.u15099 = [0, 164600935416, 688458816887, 725961144222, 234558080049, 19844998608, 0, 0] := by
  rw [show D2M8K2.u15099 = KTree.node D2M8K2.t15104 (nat_lit 32933873) (nat_lit 1579302274) (nat_lit 0) D2M8K2.t15105 from rfl, totK_node, tot15104, tot15105]
  decide +kernel

theorem arows15100 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15100 = true := by
  rw [show D2M8K2.u15100 = KTree.node D2M8K2.t15106 (nat_lit 32935749) (nat_lit 1511480967) (nat_lit 0) D2M8K2.t15107 from rfl, allE_node, rows15106, irow15100, rows15107]
  all_goals rfl

theorem atot15100 : totK PD2M8K2 D2M8K2.u15100 = [0, 227349524559, 669279802644, 671394450816, 239584935219, 12173535661, 0, 0] := by
  rw [show D2M8K2.u15100 = KTree.node D2M8K2.t15106 (nat_lit 32935749) (nat_lit 1511480967) (nat_lit 0) D2M8K2.t15107 from rfl, totK_node, tot15106, tot15107]
  decide +kernel

theorem arows15102 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15102 = true := by
  rw [show D2M8K2.u15102 = KTree.node D2M8K2.t15108 (nat_lit 32937205) (nat_lit 1189885273) (nat_lit 0) D2M8K2.t15109 from rfl, allE_node, rows15108, irow15102, rows15109]
  all_goals rfl

theorem atot15102 : totK PD2M8K2 D2M8K2.u15102 = [0, 210027735334, 782332096323, 693740830294, 110190181744, 1164319620, 0, 0] := by
  rw [show D2M8K2.u15102 = KTree.node D2M8K2.t15108 (nat_lit 32937205) (nat_lit 1189885273) (nat_lit 0) D2M8K2.t15109 from rfl, totK_node, tot15108, tot15109]
  decide +kernel

theorem arows15103 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15103 = true := by
  rw [show D2M8K2.u15103 = KTree.node D2M8K2.t15110 (nat_lit 32938891) (nat_lit 1180080957) (nat_lit 0) D2M8K2.t15111 from rfl, allE_node, rows15110, irow15103, rows15111]
  all_goals rfl

theorem atot15103 : totK PD2M8K2 D2M8K2.u15103 = [0, 157970222024, 637100807791, 766410758634, 219555578665, 11885407614, 0, 0] := by
  rw [show D2M8K2.u15103 = KTree.node D2M8K2.t15110 (nat_lit 32938891) (nat_lit 1180080957) (nat_lit 0) D2M8K2.t15111 from rfl, totK_node, tot15110, tot15111]
  decide +kernel

theorem arows15106 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15106 = true := by
  rw [show D2M8K2.u15106 = KTree.node D2M8K2.t15112 (nat_lit 32943835) (nat_lit 2229063769) (nat_lit 0) D2M8K2.t15113 from rfl, allE_node, rows15112, irow15106, rows15113]
  all_goals rfl

theorem atot15106 : totK PD2M8K2 D2M8K2.u15106 = [0, 220777788014, 778778980137, 676990324664, 97500283392, 1096505104, 0, 0] := by
  rw [show D2M8K2.u15106 = KTree.node D2M8K2.t15112 (nat_lit 32943835) (nat_lit 2229063769) (nat_lit 0) D2M8K2.t15113 from rfl, totK_node, tot15112, tot15113]
  decide +kernel

theorem arows15107 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15107 = true := by
  rw [show D2M8K2.u15107 = KTree.node D2M8K2.t15114 (nat_lit 32946198) (nat_lit 3570504702) (nat_lit 0) D2M8K2.t15115 from rfl, allE_node, rows15114, irow15107, rows15115]
  all_goals rfl

theorem atot15107 : totK PD2M8K2 D2M8K2.u15107 = [0, 255639615161, 780526973573, 646304151646, 122720261278, 3884009855, 0, 0] := by
  rw [show D2M8K2.u15107 = KTree.node D2M8K2.t15114 (nat_lit 32946198) (nat_lit 3570504702) (nat_lit 0) D2M8K2.t15115 from rfl, totK_node, tot15114, tot15115]
  decide +kernel

theorem arows15109 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15109 = true := by
  rw [show D2M8K2.u15109 = KTree.node D2M8K2.t15116 (nat_lit 32947763) (nat_lit 2978412160) (nat_lit 0) D2M8K2.t15117 from rfl, allE_node, rows15116, irow15109, rows15117]
  all_goals rfl

theorem atot15109 : totK PD2M8K2 D2M8K2.u15109 = [0, 161288847707, 718763954012, 785927211563, 151192294327, 1268739303, 0, 0] := by
  rw [show D2M8K2.u15109 = KTree.node D2M8K2.t15116 (nat_lit 32947763) (nat_lit 2978412160) (nat_lit 0) D2M8K2.t15117 from rfl, totK_node, tot15116, tot15117]
  decide +kernel

theorem arows15110 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15110 = true := by
  rw [show D2M8K2.u15110 = KTree.node D2M8K2.t15118 (nat_lit 32949482) (nat_lit 3893059990) (nat_lit 0) D2M8K2.t15119 from rfl, allE_node, rows15118, irow15110, rows15119]
  all_goals rfl

theorem atot15110 : totK PD2M8K2 D2M8K2.u15110 = [0, 0, 349615987299, 928954495218, 467107864792, 30615192383, 0, 0] := by
  rw [show D2M8K2.u15110 = KTree.node D2M8K2.t15118 (nat_lit 32949482) (nat_lit 3893059990) (nat_lit 0) D2M8K2.t15119 from rfl, totK_node, tot15118, tot15119]
  decide +kernel

theorem arows15114 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15114 = true := by
  rw [show D2M8K2.u15114 = KTree.node D2M8K2.t15120 (nat_lit 32951038) (nat_lit 3846585313) (nat_lit 0) D2M8K2.t15121 from rfl, allE_node, rows15120, irow15114, rows15121]
  all_goals rfl

theorem atot15114 : totK PD2M8K2 D2M8K2.u15114 = [0, 0, 228188209516, 786648619950, 621087906914, 87433660599, 1206465782, 0] := by
  rw [show D2M8K2.u15114 = KTree.node D2M8K2.t15120 (nat_lit 32951038) (nat_lit 3846585313) (nat_lit 0) D2M8K2.t15121 from rfl, totK_node, tot15120, tot15121]
  decide +kernel

theorem arows15115 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15115 = true := by
  rw [show D2M8K2.u15115 = KTree.node D2M8K2.t15122 (nat_lit 32953494) (nat_lit 3152595542) (nat_lit 0) D2M8K2.t15123 from rfl, allE_node, rows15122, irow15115, rows15123]
  all_goals rfl

theorem atot15115 : totK PD2M8K2 D2M8K2.u15115 = [0, 0, 278396366314, 891035655319, 582141155955, 50663154972, 0, 0] := by
  rw [show D2M8K2.u15115 = KTree.node D2M8K2.t15122 (nat_lit 32953494) (nat_lit 3152595542) (nat_lit 0) D2M8K2.t15123 from rfl, totK_node, tot15122, tot15123]
  decide +kernel

theorem arows15117 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15117 = true := by
  rw [show D2M8K2.u15117 = KTree.node D2M8K2.t15124 (nat_lit 32956814) (nat_lit 3867728386) (nat_lit 0) D2M8K2.t15125 from rfl, allE_node, rows15124, irow15117, rows15125]
  all_goals rfl

theorem atot15117 : totK PD2M8K2 D2M8K2.u15117 = [0, 0, 380841333285, 928426349509, 474148845477, 34280683784, 0, 0] := by
  rw [show D2M8K2.u15117 = KTree.node D2M8K2.t15124 (nat_lit 32956814) (nat_lit 3867728386) (nat_lit 0) D2M8K2.t15125 from rfl, totK_node, tot15124, tot15125]
  decide +kernel

theorem arows15118 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15118 = true := by
  rw [show D2M8K2.u15118 = KTree.node D2M8K2.t15126 (nat_lit 32958287) (nat_lit 2110372907) (nat_lit 0) D2M8K2.t15127 from rfl, allE_node, rows15126, irow15118, rows15127]
  all_goals rfl

theorem atot15118 : totK PD2M8K2 D2M8K2.u15118 = [0, 0, 106808449551, 680958554081, 788486218025, 172480550182, 5395128787, 0] := by
  rw [show D2M8K2.u15118 = KTree.node D2M8K2.t15126 (nat_lit 32958287) (nat_lit 2110372907) (nat_lit 0) D2M8K2.t15127 from rfl, totK_node, tot15126, tot15127]
  decide +kernel

theorem arows15121 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15121 = true := by
  rw [show D2M8K2.u15121 = KTree.node D2M8K2.t15128 (nat_lit 32963877) (nat_lit 1404621419) (nat_lit 0) D2M8K2.t15129 from rfl, allE_node, rows15128, irow15121, rows15129]
  all_goals rfl

theorem atot15121 : totK PD2M8K2 D2M8K2.u15121 = [0, 0, 357806232551, 926834235662, 458561758840, 31705106206, 0, 0] := by
  rw [show D2M8K2.u15121 = KTree.node D2M8K2.t15128 (nat_lit 32963877) (nat_lit 1404621419) (nat_lit 0) D2M8K2.t15129 from rfl, totK_node, tot15128, tot15129]
  decide +kernel

theorem arows15122 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15122 = true := by
  rw [show D2M8K2.u15122 = KTree.node D2M8K2.t15130 (nat_lit 32967269) (nat_lit 2367384341) (nat_lit 0) D2M8K2.t15131 from rfl, allE_node, rows15130, irow15122, rows15131]
  all_goals rfl

theorem atot15122 : totK PD2M8K2 D2M8K2.u15122 = [0, 0, 338893707537, 945383930506, 491136221192, 29278687957, 0, 0] := by
  rw [show D2M8K2.u15122 = KTree.node D2M8K2.t15130 (nat_lit 32967269) (nat_lit 2367384341) (nat_lit 0) D2M8K2.t15131 from rfl, totK_node, tot15130, tot15131]
  decide +kernel

theorem arows15124 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15124 = true := by
  rw [show D2M8K2.u15124 = KTree.node D2M8K2.t15132 (nat_lit 32970826) (nat_lit 3862752225) (nat_lit 0) D2M8K2.t15133 from rfl, allE_node, rows15132, irow15124, rows15133]
  all_goals rfl

theorem atot15124 : totK PD2M8K2 D2M8K2.u15124 = [0, 295517022797, 783840429502, 546639194075, 160382593235, 13566920432, 0, 0] := by
  rw [show D2M8K2.u15124 = KTree.node D2M8K2.t15132 (nat_lit 32970826) (nat_lit 3862752225) (nat_lit 0) D2M8K2.t15133 from rfl, totK_node, tot15132, tot15133]
  decide +kernel

theorem arows15125 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15125 = true := by
  rw [show D2M8K2.u15125 = KTree.node D2M8K2.t15134 (nat_lit 32972066) (nat_lit 2618681085) (nat_lit 0) D2M8K2.t15135 from rfl, allE_node, rows15134, irow15125, rows15135]
  all_goals rfl

theorem atot15125 : totK PD2M8K2 D2M8K2.u15125 = [0, 123641764684, 705485001614, 812720221592, 138847846120, 1369150432, 0, 0] := by
  rw [show D2M8K2.u15125 = KTree.node D2M8K2.t15134 (nat_lit 32972066) (nat_lit 2618681085) (nat_lit 0) D2M8K2.t15135 from rfl, totK_node, tot15134, tot15135]
  decide +kernel

theorem arows15130 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15130 = true := by
  rw [show D2M8K2.u15130 = KTree.node D2M8K2.t15136 (nat_lit 32974680) (nat_lit 3268954807) (nat_lit 0) D2M8K2.t15137 from rfl, allE_node, rows15136, irow15130, rows15137]
  all_goals rfl

theorem atot15130 : totK PD2M8K2 D2M8K2.u15130 = [0, 331555795189, 900296897867, 569329564371, 53640824217, 0, 0, 0] := by
  rw [show D2M8K2.u15130 = KTree.node D2M8K2.t15136 (nat_lit 32974680) (nat_lit 3268954807) (nat_lit 0) D2M8K2.t15137 from rfl, totK_node, tot15136, tot15137]
  decide +kernel

theorem arows15131 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15131 = true := by
  rw [show D2M8K2.u15131 = KTree.node D2M8K2.t15138 (nat_lit 32976514) (nat_lit 3842563464) (nat_lit 0) D2M8K2.t15139 from rfl, allE_node, rows15138, irow15131, rows15139]
  all_goals rfl

theorem atot15131 : totK PD2M8K2 D2M8K2.u15131 = [0, 32194035719, 412784385691, 901256621555, 441275881840, 32096557826, 0, 0] := by
  rw [show D2M8K2.u15131 = KTree.node D2M8K2.t15138 (nat_lit 32976514) (nat_lit 3842563464) (nat_lit 0) D2M8K2.t15139 from rfl, totK_node, tot15138, tot15139]
  decide +kernel

theorem arows15133 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15133 = true := by
  rw [show D2M8K2.u15133 = KTree.node D2M8K2.t15140 (nat_lit 32981558) (nat_lit 3968625444) (nat_lit 0) D2M8K2.t15141 from rfl, allE_node, rows15140, irow15133, rows15141]
  all_goals rfl

theorem atot15133 : totK PD2M8K2 D2M8K2.u15133 = [0, 385935041740, 939826527741, 468167337148, 33774997235, 0, 0, 0] := by
  rw [show D2M8K2.u15133 = KTree.node D2M8K2.t15140 (nat_lit 32981558) (nat_lit 3968625444) (nat_lit 0) D2M8K2.t15141 from rfl, totK_node, tot15140, tot15141]
  decide +kernel

theorem arows15134 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15134 = true := by
  rw [show D2M8K2.u15134 = KTree.node D2M8K2.t15142 (nat_lit 32983205) (nat_lit 1472494690) (nat_lit 0) D2M8K2.t15143 from rfl, allE_node, rows15142, irow15134, rows15143]
  all_goals rfl

theorem atot15134 : totK PD2M8K2 D2M8K2.u15134 = [0, 19434652667, 514554181282, 940295016351, 289785979819, 13250685261, 0, 0] := by
  rw [show D2M8K2.u15134 = KTree.node D2M8K2.t15142 (nat_lit 32983205) (nat_lit 1472494690) (nat_lit 0) D2M8K2.t15143 from rfl, totK_node, tot15142, tot15143]
  decide +kernel

theorem arows15137 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15137 = true := by
  rw [show D2M8K2.u15137 = KTree.node D2M8K2.t15144 (nat_lit 32984634) (nat_lit 3537081954) (nat_lit 0) D2M8K2.t15145 from rfl, allE_node, rows15144, irow15137, rows15145]
  all_goals rfl

theorem atot15137 : totK PD2M8K2 D2M8K2.u15137 = [0, 356530249848, 880897464812, 515414857327, 54265131218, 0, 0, 0] := by
  rw [show D2M8K2.u15137 = KTree.node D2M8K2.t15144 (nat_lit 32984634) (nat_lit 3537081954) (nat_lit 0) D2M8K2.t15145 from rfl, totK_node, tot15144, tot15145]
  decide +kernel

theorem arows15138 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15138 = true := by
  rw [show D2M8K2.u15138 = KTree.node D2M8K2.t15146 (nat_lit 32986470) (nat_lit 2917531415) (nat_lit 0) D2M8K2.t15147 from rfl, allE_node, rows15146, irow15138, rows15147]
  all_goals rfl

theorem atot15138 : totK PD2M8K2 D2M8K2.u15138 = [0, 107855799797, 639459434966, 839448926657, 181405733707, 4980514959, 0, 0] := by
  rw [show D2M8K2.u15138 = KTree.node D2M8K2.t15146 (nat_lit 32986470) (nat_lit 2917531415) (nat_lit 0) D2M8K2.t15147 from rfl, totK_node, tot15146, tot15147]
  decide +kernel

theorem arows15140 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15140 = true := by
  rw [show D2M8K2.u15140 = KTree.node D2M8K2.t15148 (nat_lit 32988308) (nat_lit 2634774515) (nat_lit 0) D2M8K2.t15149 from rfl, allE_node, rows15148, irow15140, rows15149]
  all_goals rfl

theorem atot15140 : totK PD2M8K2 D2M8K2.u15140 = [0, 331445521867, 928744188017, 540810695159, 41338042978, 0, 0, 0] := by
  rw [show D2M8K2.u15140 = KTree.node D2M8K2.t15148 (nat_lit 32988308) (nat_lit 2634774515) (nat_lit 0) D2M8K2.t15149 from rfl, totK_node, tot15148, tot15149]
  decide +kernel

theorem arows15141 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15141 = true := by
  rw [show D2M8K2.u15141 = KTree.node D2M8K2.t15150 (nat_lit 32989997) (nat_lit 1595006556) (nat_lit 0) D2M8K2.t15151 from rfl, allE_node, rows15150, irow15141, rows15151]
  all_goals rfl

theorem atot15141 : totK PD2M8K2 D2M8K2.u15141 = [0, 0, 426524857150, 978267766458, 364134290476, 13467081304, 0, 0] := by
  rw [show D2M8K2.u15141 = KTree.node D2M8K2.t15150 (nat_lit 32989997) (nat_lit 1595006556) (nat_lit 0) D2M8K2.t15151 from rfl, totK_node, tot15150, tot15151]
  decide +kernel

theorem arows15145 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15145 = true := by
  rw [show D2M8K2.u15145 = KTree.node D2M8K2.t15152 (nat_lit 32991922) (nat_lit 3933563267) (nat_lit 0) D2M8K2.t15153 from rfl, allE_node, rows15152, irow15145, rows15153]
  all_goals rfl

theorem atot15145 : totK PD2M8K2 D2M8K2.u15145 = [0, 0, 398234475214, 947575503051, 394271046397, 23455396357, 0, 0] := by
  rw [show D2M8K2.u15145 = KTree.node D2M8K2.t15152 (nat_lit 32991922) (nat_lit 3933563267) (nat_lit 0) D2M8K2.t15153 from rfl, totK_node, tot15152, tot15153]
  decide +kernel

theorem arows15146 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15146 = true := by
  rw [show D2M8K2.u15146 = KTree.node D2M8K2.t15154 (nat_lit 32993647) (nat_lit 2446349698) (nat_lit 0) D2M8K2.t15155 from rfl, allE_node, rows15154, irow15146, rows15155]
  all_goals rfl

theorem atot15146 : totK PD2M8K2 D2M8K2.u15146 = [0, 0, 108505821620, 729799118256, 814270434942, 117426499574, 1239866073, 0] := by
  rw [show D2M8K2.u15146 = KTree.node D2M8K2.t15154 (nat_lit 32993647) (nat_lit 2446349698) (nat_lit 0) D2M8K2.t15155 from rfl, totK_node, tot15154, tot15155]
  decide +kernel

theorem arows15148 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15148 = true := by
  rw [show D2M8K2.u15148 = KTree.node D2M8K2.t15156 (nat_lit 32995900) (nat_lit 3683638083) (nat_lit 0) D2M8K2.t15157 from rfl, allE_node, rows15156, irow15148, rows15157]
  all_goals rfl

theorem atot15148 : totK PD2M8K2 D2M8K2.u15148 = [0, 0, 376702202300, 936037328943, 475185376554, 32892857751, 0, 0] := by
  rw [show D2M8K2.u15148 = KTree.node D2M8K2.t15156 (nat_lit 32995900) (nat_lit 3683638083) (nat_lit 0) D2M8K2.t15157 from rfl, totK_node, tot15156, tot15157]
  decide +kernel

theorem arows15149 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15149 = true := by
  rw [show D2M8K2.u15149 = KTree.node D2M8K2.t15158 (nat_lit 33002548) (nat_lit 2028966834) (nat_lit 0) D2M8K2.t15159 from rfl, allE_node, rows15158, irow15149, rows15159]
  all_goals rfl

theorem atot15149 : totK PD2M8K2 D2M8K2.u15149 = [0, 0, 300494543194, 884084690638, 560317780847, 45223049561, 0, 0] := by
  rw [show D2M8K2.u15149 = KTree.node D2M8K2.t15158 (nat_lit 33002548) (nat_lit 2028966834) (nat_lit 0) D2M8K2.t15159 from rfl, totK_node, tot15158, tot15159]
  decide +kernel

theorem arows15152 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15152 = true := by
  rw [show D2M8K2.u15152 = KTree.node D2M8K2.t15160 (nat_lit 33004303) (nat_lit 2432917385) (nat_lit 0) D2M8K2.t15161 from rfl, allE_node, rows15160, irow15152, rows15161]
  all_goals rfl

theorem atot15152 : totK PD2M8K2 D2M8K2.u15152 = [0, 0, 149917210474, 701763641186, 750626170641, 172507629019, 5425831197, 0] := by
  rw [show D2M8K2.u15152 = KTree.node D2M8K2.t15160 (nat_lit 33004303) (nat_lit 2432917385) (nat_lit 0) D2M8K2.t15161 from rfl, totK_node, tot15160, tot15161]
  decide +kernel

theorem arows15153 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15153 = true := by
  rw [show D2M8K2.u15153 = KTree.node D2M8K2.t15162 (nat_lit 33006010) (nat_lit 1304181346) (nat_lit 0) D2M8K2.t15163 from rfl, allE_node, rows15162, irow15153, rows15163]
  all_goals rfl

theorem atot15153 : totK PD2M8K2 D2M8K2.u15153 = [0, 0, 393548188198, 951566414378, 409163606045, 19167463455, 0, 0] := by
  rw [show D2M8K2.u15153 = KTree.node D2M8K2.t15162 (nat_lit 33006010) (nat_lit 1304181346) (nat_lit 0) D2M8K2.t15163 from rfl, totK_node, tot15162, tot15163]
  decide +kernel

theorem arows15155 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15155 = true := by
  rw [show D2M8K2.u15155 = KTree.node D2M8K2.t15164 (nat_lit 33009348) (nat_lit 3046801075) (nat_lit 0) D2M8K2.t15165 from rfl, allE_node, rows15164, irow15155, rows15165]
  all_goals rfl

theorem atot15155 : totK PD2M8K2 D2M8K2.u15155 = [0, 90861460542, 436498233233, 788901042101, 474100392891, 38630842457, 0, 0] := by
  rw [show D2M8K2.u15155 = KTree.node D2M8K2.t15164 (nat_lit 33009348) (nat_lit 3046801075) (nat_lit 0) D2M8K2.t15165 from rfl, totK_node, tot15164, tot15165]
  decide +kernel

theorem arows15156 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15156 = true := by
  rw [show D2M8K2.u15156 = KTree.node D2M8K2.t15166 (nat_lit 33012834) (nat_lit 3318771954) (nat_lit 0) D2M8K2.t15167 from rfl, allE_node, rows15166, irow15156, rows15167]
  all_goals rfl

theorem atot15156 : totK PD2M8K2 D2M8K2.u15156 = [0, 329776033403, 909329437588, 505649065408, 36068558124, 0, 0, 0] := by
  rw [show D2M8K2.u15156 = KTree.node D2M8K2.t15166 (nat_lit 33012834) (nat_lit 3318771954) (nat_lit 0) D2M8K2.t15167 from rfl, totK_node, tot15166, tot15167]
  decide +kernel

theorem arows15162 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15162 = true := by
  rw [show D2M8K2.u15162 = KTree.node D2M8K2.t15168 (nat_lit 33014651) (nat_lit 2099351725) (nat_lit 0) D2M8K2.t15169 from rfl, allE_node, rows15168, irow15162, rows15169]
  all_goals rfl

theorem atot15162 : totK PD2M8K2 D2M8K2.u15162 = [0, 154236233185, 714529053047, 792160470824, 138443766517, 1369150432, 0, 0] := by
  rw [show D2M8K2.u15162 = KTree.node D2M8K2.t15168 (nat_lit 33014651) (nat_lit 2099351725) (nat_lit 0) D2M8K2.t15169 from rfl, totK_node, tot15168, tot15169]
  decide +kernel

theorem arows15163 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15163 = true := by
  rw [show D2M8K2.u15163 = KTree.node D2M8K2.t15170 (nat_lit 33019936) (nat_lit 2357946604) (nat_lit 0) D2M8K2.t15171 from rfl, allE_node, rows15170, irow15163, rows15171]
  all_goals rfl

theorem atot15163 : totK PD2M8K2 D2M8K2.u15163 = [0, 245898187332, 791069473753, 651470032812, 96659384077, 1164319620, 0, 0] := by
  rw [show D2M8K2.u15163 = KTree.node D2M8K2.t15170 (nat_lit 33019936) (nat_lit 2357946604) (nat_lit 0) D2M8K2.t15171 from rfl, totK_node, tot15170, tot15171]
  decide +kernel

theorem arows15165 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15165 = true := by
  rw [show D2M8K2.u15165 = KTree.node D2M8K2.t15172 (nat_lit 33021706) (nat_lit 3012524983) (nat_lit 0) D2M8K2.t15173 from rfl, allE_node, rows15172, irow15165, rows15173]
  all_goals rfl

theorem atot15165 : totK PD2M8K2 D2M8K2.u15165 = [0, 154319968341, 654010310050, 766165541260, 205629990716, 11885407614, 0, 0] := by
  rw [show D2M8K2.u15165 = KTree.node D2M8K2.t15172 (nat_lit 33021706) (nat_lit 3012524983) (nat_lit 0) D2M8K2.t15173 from rfl, totK_node, tot15172, tot15173]
  decide +kernel

theorem arows15166 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15166 = true := by
  rw [show D2M8K2.u15166 = KTree.node D2M8K2.t15174 (nat_lit 33023449) (nat_lit 1409730240) (nat_lit 0) D2M8K2.t15175 from rfl, allE_node, rows15174, irow15166, rows15175]
  all_goals rfl

theorem atot15166 : totK PD2M8K2 D2M8K2.u15166 = [0, 246050511794, 786017797828, 660126571742, 100070955326, 1198073392, 0, 0] := by
  rw [show D2M8K2.u15166 = KTree.node D2M8K2.t15174 (nat_lit 33023449) (nat_lit 1409730240) (nat_lit 0) D2M8K2.t15175 from rfl, totK_node, tot15174, tot15175]
  decide +kernel

theorem arows15169 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15169 = true := by
  rw [show D2M8K2.u15169 = KTree.node D2M8K2.t15176 (nat_lit 33025216) (nat_lit 1955286538) (nat_lit 0) D2M8K2.t15177 from rfl, allE_node, rows15176, irow15169, rows15177]
  all_goals rfl

theorem atot15169 : totK PD2M8K2 D2M8K2.u15169 = [0, 159521618790, 657614568916, 759028628595, 208202791927, 12052611869, 0, 0] := by
  rw [show D2M8K2.u15169 = KTree.node D2M8K2.t15176 (nat_lit 33025216) (nat_lit 1955286538) (nat_lit 0) D2M8K2.t15177 from rfl, totK_node, tot15176, tot15177]
  decide +kernel

theorem arows15170 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15170 = true := by
  rw [show D2M8K2.u15170 = KTree.node D2M8K2.t15178 (nat_lit 33026648) (nat_lit 3884234293) (nat_lit 0) D2M8K2.t15179 from rfl, allE_node, rows15178, irow15170, rows15179]
  all_goals rfl

theorem atot15170 : totK PD2M8K2 D2M8K2.u15170 = [0, 264047124841, 808711099652, 623407398404, 89318150128, 1096505104, 0, 0] := by
  rw [show D2M8K2.u15170 = KTree.node D2M8K2.t15178 (nat_lit 33026648) (nat_lit 3884234293) (nat_lit 0) D2M8K2.t15179 from rfl, totK_node, tot15178, tot15179]
  decide +kernel

theorem arows15172 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15172 = true := by
  rw [show D2M8K2.u15172 = KTree.node D2M8K2.t15180 (nat_lit 33028592) (nat_lit 3770030118) (nat_lit 0) D2M8K2.t15181 from rfl, allE_node, rows15180, irow15172, rows15181]
  all_goals rfl

theorem atot15172 : totK PD2M8K2 D2M8K2.u15172 = [0, 0, 478527824276, 994192749789, 301540712846, 12153240826, 0, 0] := by
  rw [show D2M8K2.u15172 = KTree.node D2M8K2.t15180 (nat_lit 33028592) (nat_lit 3770030118) (nat_lit 0) D2M8K2.t15181 from rfl, totK_node, tot15180, tot15181]
  decide +kernel

theorem arows15173 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15173 = true := by
  rw [show D2M8K2.u15173 = KTree.node D2M8K2.t15182 (nat_lit 33033896) (nat_lit 2760260434) (nat_lit 0) D2M8K2.t15183 from rfl, allE_node, rows15182, irow15173, rows15183]
  all_goals rfl

theorem atot15173 : totK PD2M8K2 D2M8K2.u15173 = [0, 0, 243482251779, 814369859583, 577810495701, 78913786674, 1138244013, 0] := by
  rw [show D2M8K2.u15173 = KTree.node D2M8K2.t15182 (nat_lit 33033896) (nat_lit 2760260434) (nat_lit 0) D2M8K2.t15183 from rfl, totK_node, tot15182, tot15183]
  decide +kernel

theorem arows15177 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15177 = true := by
  rw [show D2M8K2.u15177 = KTree.node D2M8K2.t15184 (nat_lit 33039681) (nat_lit 1820251945) (nat_lit 0) D2M8K2.t15185 from rfl, allE_node, rows15184, irow15177, rows15185]
  all_goals rfl

theorem atot15177 : totK PD2M8K2 D2M8K2.u15177 = [0, 0, 297511602492, 912067151932, 524284412759, 36557316556, 0, 0] := by
  rw [show D2M8K2.u15177 = KTree.node D2M8K2.t15184 (nat_lit 33039681) (nat_lit 1820251945) (nat_lit 0) D2M8K2.t15185 from rfl, totK_node, tot15184, tot15185]
  decide +kernel

theorem arows15178 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15178 = true := by
  rw [show D2M8K2.u15178 = KTree.node D2M8K2.t15186 (nat_lit 33043018) (nat_lit 2719718797) (nat_lit 0) D2M8K2.t15187 from rfl, allE_node, rows15186, irow15178, rows15187]
  all_goals rfl

theorem atot15178 : totK PD2M8K2 D2M8K2.u15178 = [0, 0, 362682647149, 949027141168, 445404245769, 21760816089, 0, 0] := by
  rw [show D2M8K2.u15178 = KTree.node D2M8K2.t15186 (nat_lit 33043018) (nat_lit 2719718797) (nat_lit 0) D2M8K2.t15187 from rfl, totK_node, tot15186, tot15187]
  decide +kernel

theorem arows15180 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15180 = true := by
  rw [show D2M8K2.u15180 = KTree.node D2M8K2.t15188 (nat_lit 33046389) (nat_lit 1739799179) (nat_lit 0) D2M8K2.t15189 from rfl, allE_node, rows15188, irow15180, rows15189]
  all_goals rfl

theorem atot15180 : totK PD2M8K2 D2M8K2.u15180 = [0, 0, 380990888043, 973234474245, 405740031290, 16202309099, 0, 0] := by
  rw [show D2M8K2.u15180 = KTree.node D2M8K2.t15188 (nat_lit 33046389) (nat_lit 1739799179) (nat_lit 0) D2M8K2.t15189 from rfl, totK_node, tot15188, tot15189]
  decide +kernel

theorem arows15181 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15181 = true := by
  rw [show D2M8K2.u15181 = KTree.node D2M8K2.t15190 (nat_lit 33047673) (nat_lit 1903903263) (nat_lit 0) D2M8K2.t15191 from rfl, allE_node, rows15190, irow15181, rows15191]
  all_goals rfl

theorem atot15181 : totK PD2M8K2 D2M8K2.u15181 = [0, 194625098643, 648448553667, 675675609724, 243463702939, 14787543972, 0, 0] := by
  rw [show D2M8K2.u15181 = KTree.node D2M8K2.t15190 (nat_lit 33047673) (nat_lit 1903903263) (nat_lit 0) D2M8K2.t15191 from rfl, totK_node, tot15190, tot15191]
  decide +kernel

theorem arows15184 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15184 = true := by
  rw [show D2M8K2.u15184 = KTree.node D2M8K2.t15192 (nat_lit 33054707) (nat_lit 2897870831) (nat_lit 0) D2M8K2.t15193 from rfl, allE_node, rows15192, irow15184, rows15193]
  all_goals rfl

theorem atot15184 : totK PD2M8K2 D2M8K2.u15184 = [0, 227139922144, 777627743558, 676434525533, 112501151558, 1369150432, 0, 0] := by
  rw [show D2M8K2.u15184 = KTree.node D2M8K2.t15192 (nat_lit 33054707) (nat_lit 2897870831) (nat_lit 0) D2M8K2.t15193 from rfl, totK_node, tot15192, tot15193]
  decide +kernel

theorem arows15185 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15185 = true := by
  rw [show D2M8K2.u15185 = KTree.node D2M8K2.t15194 (nat_lit 33057059) (nat_lit 2962688467) (nat_lit 0) D2M8K2.t15195 from rfl, allE_node, rows15194, irow15185, rows15195]
  all_goals rfl

theorem atot15185 : totK PD2M8K2 D2M8K2.u15185 = [0, 258412381221, 822869752157, 688704247788, 79506443855, 0, 0, 0] := by
  rw [show D2M8K2.u15185 = KTree.node D2M8K2.t15194 (nat_lit 33057059) (nat_lit 2962688467) (nat_lit 0) D2M8K2.t15195 from rfl, totK_node, tot15194, tot15195]
  decide +kernel

theorem arows15187 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15187 = true := by
  rw [show D2M8K2.u15187 = KTree.node D2M8K2.t15196 (nat_lit 33058829) (nat_lit 2175808801) (nat_lit 0) D2M8K2.t15197 from rfl, allE_node, rows15196, irow15187, rows15197]
  all_goals rfl

theorem atot15187 : totK PD2M8K2 D2M8K2.u15187 = [0, 90206013543, 577280800327, 839720918905, 310857676605, 21912686248, 0, 0] := by
  rw [show D2M8K2.u15187 = KTree.node D2M8K2.t15196 (nat_lit 33058829) (nat_lit 2175808801) (nat_lit 0) D2M8K2.t15197 from rfl, totK_node, tot15196, tot15197]
  decide +kernel

theorem arows15188 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15188 = true := by
  rw [show D2M8K2.u15188 = KTree.node D2M8K2.t15198 (nat_lit 33060362) (nat_lit 3341342973) (nat_lit 0) D2M8K2.t15199 from rfl, allE_node, rows15198, irow15188, rows15199]
  all_goals rfl

theorem atot15188 : totK PD2M8K2 D2M8K2.u15188 = [0, 257645513458, 744471919274, 614230882135, 197194258365, 9434345190, 0, 0] := by
  rw [show D2M8K2.u15188 = KTree.node D2M8K2.t15198 (nat_lit 33060362) (nat_lit 3341342973) (nat_lit 0) D2M8K2.t15199 from rfl, totK_node, tot15198, tot15199]
  decide +kernel

theorem arows15193 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15193 = true := by
  rw [show D2M8K2.u15193 = KTree.node D2M8K2.t15200 (nat_lit 33061902) (nat_lit 3782400991) (nat_lit 0) D2M8K2.t15201 from rfl, allE_node, rows15200, irow15193, rows15201]
  all_goals rfl

theorem atot15193 : totK PD2M8K2 D2M8K2.u15193 = [0, 155139932129, 661657033005, 772948766007, 196987718708, 7832068735, 0, 0] := by
  rw [show D2M8K2.u15193 = KTree.node D2M8K2.t15200 (nat_lit 33061902) (nat_lit 3782400991) (nat_lit 0) D2M8K2.t15201 from rfl, totK_node, tot15200, tot15201]
  decide +kernel

theorem arows15194 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15194 = true := by
  rw [show D2M8K2.u15194 = KTree.node D2M8K2.t15202 (nat_lit 33063794) (nat_lit 2321137536) (nat_lit 0) D2M8K2.t15203 from rfl, allE_node, rows15202, irow15194, rows15203]
  all_goals rfl

theorem atot15194 : totK PD2M8K2 D2M8K2.u15194 = [0, 257800009766, 797911209270, 651471323280, 107926097524, 980350181, 0, 0] := by
  rw [show D2M8K2.u15194 = KTree.node D2M8K2.t15202 (nat_lit 33063794) (nat_lit 2321137536) (nat_lit 0) D2M8K2.t15203 from rfl, totK_node, tot15202, tot15203]
  decide +kernel

theorem arows15196 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15196 = true := by
  rw [show D2M8K2.u15196 = KTree.node D2M8K2.t15204 (nat_lit 33065344) (nat_lit 3334968772) (nat_lit 0) D2M8K2.t15205 from rfl, allE_node, rows15204, irow15196, rows15205]
  all_goals rfl

theorem atot15196 : totK PD2M8K2 D2M8K2.u15196 = [0, 155229484744, 674200855926, 777640112310, 187512221992, 6922002537, 0, 0] := by
  rw [show D2M8K2.u15196 = KTree.node D2M8K2.t15204 (nat_lit 33065344) (nat_lit 3334968772) (nat_lit 0) D2M8K2.t15205 from rfl, totK_node, tot15204, tot15205]
  decide +kernel

theorem arows15197 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15197 = true := by
  rw [show D2M8K2.u15197 = KTree.node D2M8K2.t15206 (nat_lit 33070661) (nat_lit 2336278503) (nat_lit 0) D2M8K2.t15207 from rfl, allE_node, rows15206, irow15197, rows15207]
  all_goals rfl

theorem atot15197 : totK PD2M8K2 D2M8K2.u15197 = [0, 261125138266, 792217716546, 643232121140, 124161472490, 1991429766, 0, 0] := by
  rw [show D2M8K2.u15197 = KTree.node D2M8K2.t15206 (nat_lit 33070661) (nat_lit 2336278503) (nat_lit 0) D2M8K2.t15207 from rfl, totK_node, tot15206, tot15207]
  decide +kernel

theorem arows15200 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15200 = true := by
  rw [show D2M8K2.u15200 = KTree.node D2M8K2.t15208 (nat_lit 33072121) (nat_lit 1438272545) (nat_lit 0) D2M8K2.t15209 from rfl, allE_node, rows15208, irow15200, rows15209]
  all_goals rfl

theorem atot15200 : totK PD2M8K2 D2M8K2.u15200 = [0, 181674658392, 739265754398, 763596614896, 140421177880, 1268739303, 0, 0] := by
  rw [show D2M8K2.u15200 = KTree.node D2M8K2.t15208 (nat_lit 33072121) (nat_lit 1438272545) (nat_lit 0) D2M8K2.t15209 from rfl, totK_node, tot15208, tot15209]
  decide +kernel

theorem arows15201 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15201 = true := by
  rw [show D2M8K2.u15201 = KTree.node D2M8K2.t15210 (nat_lit 33073785) (nat_lit 999305339) (nat_lit 0) D2M8K2.t15211 from rfl, allE_node, rows15210, irow15201, rows15211]
  all_goals rfl

theorem atot15201 : totK PD2M8K2 D2M8K2.u15201 = [0, 0, 375493804258, 951485930531, 426755012723, 23301045897, 0, 0] := by
  rw [show D2M8K2.u15201 = KTree.node D2M8K2.t15210 (nat_lit 33073785) (nat_lit 999305339) (nat_lit 0) D2M8K2.t15211 from rfl, totK_node, tot15210, tot15211]
  decide +kernel

theorem arows15203 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15203 = true := by
  rw [show D2M8K2.u15203 = KTree.node D2M8K2.t15212 (nat_lit 33075389) (nat_lit 2113172757) (nat_lit 0) D2M8K2.t15213 from rfl, allE_node, rows15212, irow15203, rows15213]
  all_goals rfl

theorem atot15203 : totK PD2M8K2 D2M8K2.u15203 = [0, 0, 243694949218, 814991933043, 618701833011, 86308760481, 1310285577, 0] := by
  rw [show D2M8K2.u15203 = KTree.node D2M8K2.t15212 (nat_lit 33075389) (nat_lit 2113172757) (nat_lit 0) D2M8K2.t15213 from rfl, totK_node, tot15212, tot15213]
  decide +kernel

theorem arows15204 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15204 = true := by
  rw [show D2M8K2.u15204 = KTree.node D2M8K2.t15214 (nat_lit 33077755) (nat_lit 2215337533) (nat_lit 0) D2M8K2.t15215 from rfl, allE_node, rows15214, irow15204, rows15215]
  all_goals rfl

theorem atot15204 : totK PD2M8K2 D2M8K2.u15204 = [0, 0, 235984728910, 806883594587, 709394125394, 68780665701, 0, 0] := by
  rw [show D2M8K2.u15204 = KTree.node D2M8K2.t15214 (nat_lit 33077755) (nat_lit 2215337533) (nat_lit 0) D2M8K2.t15215 from rfl, totK_node, tot15214, tot15215]
  decide +kernel

theorem arows15208 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15208 = true := by
  rw [show D2M8K2.u15208 = KTree.node D2M8K2.t15216 (nat_lit 33080956) (nat_lit 3854718101) (nat_lit 0) D2M8K2.t15217 from rfl, allE_node, rows15216, irow15208, rows15217]
  all_goals rfl

theorem atot15208 : totK PD2M8K2 D2M8K2.u15208 = [0, 0, 368253557874, 939822806501, 492150572479, 34555894510, 0, 0] := by
  rw [show D2M8K2.u15208 = KTree.node D2M8K2.t15216 (nat_lit 33080956) (nat_lit 3854718101) (nat_lit 0) D2M8K2.t15217 from rfl, totK_node, tot15216, tot15217]
  decide +kernel

theorem arows15209 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15209 = true := by
  rw [show D2M8K2.u15209 = KTree.node D2M8K2.t15218 (nat_lit 33082542) (nat_lit 3726115627) (nat_lit 0) D2M8K2.t15219 from rfl, allE_node, rows15218, irow15209, rows15219]
  all_goals rfl

theorem atot15209 : totK PD2M8K2 D2M8K2.u15209 = [0, 0, 154305128355, 716587872771, 757001708703, 128694606523, 2125526286, 0] := by
  rw [show D2M8K2.u15209 = KTree.node D2M8K2.t15218 (nat_lit 33082542) (nat_lit 3726115627) (nat_lit 0) D2M8K2.t15219 from rfl, totK_node, tot15218, tot15219]
  decide +kernel

theorem arows15211 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15211 = true := by
  rw [show D2M8K2.u15211 = KTree.node D2M8K2.t15220 (nat_lit 33084641) (nat_lit 2027931396) (nat_lit 0) D2M8K2.t15221 from rfl, allE_node, rows15220, irow15211, rows15221]
  all_goals rfl

theorem atot15211 : totK PD2M8K2 D2M8K2.u15211 = [0, 0, 298925482943, 862027587341, 571280394539, 69064291661, 2754314106, 0] := by
  rw [show D2M8K2.u15211 = KTree.node D2M8K2.t15220 (nat_lit 33084641) (nat_lit 2027931396) (nat_lit 0) D2M8K2.t15221 from rfl, totK_node, tot15220, tot15221]
  decide +kernel

theorem arows15212 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15212 = true := by
  rw [show D2M8K2.u15212 = KTree.node D2M8K2.t15222 (nat_lit 33086166) (nat_lit 3602540812) (nat_lit 0) D2M8K2.t15223 from rfl, allE_node, rows15222, irow15212, rows15223]
  all_goals rfl

theorem atot15212 : totK PD2M8K2 D2M8K2.u15212 = [0, 0, 112464439539, 685573650172, 785868389834, 156588487638, 4931404646, 0] := by
  rw [show D2M8K2.u15212 = KTree.node D2M8K2.t15222 (nat_lit 33086166) (nat_lit 3602540812) (nat_lit 0) D2M8K2.t15223 from rfl, totK_node, tot15222, tot15223]
  decide +kernel

theorem arows15215 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15215 = true := by
  rw [show D2M8K2.u15215 = KTree.node D2M8K2.t15224 (nat_lit 33091715) (nat_lit 2746135022) (nat_lit 0) D2M8K2.t15225 from rfl, allE_node, rows15224, irow15215, rows15225]
  all_goals rfl

theorem atot15215 : totK PD2M8K2 D2M8K2.u15215 = [0, 0, 347383046518, 916200631795, 518908693694, 46227344049, 0, 0] := by
  rw [show D2M8K2.u15215 = KTree.node D2M8K2.t15224 (nat_lit 33091715) (nat_lit 2746135022) (nat_lit 0) D2M8K2.t15225 from rfl, totK_node, tot15224, tot15225]
  decide +kernel

theorem arows15216 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15216 = true := by
  rw [show D2M8K2.u15216 = KTree.node D2M8K2.t15226 (nat_lit 33093198) (nat_lit 3703064702) (nat_lit 0) D2M8K2.t15227 from rfl, allE_node, rows15226, irow15216, rows15227]
  all_goals rfl

theorem atot15216 : totK PD2M8K2 D2M8K2.u15216 = [0, 0, 93518571537, 605790571080, 846642194933, 215973592661, 5842784248, 0] := by
  rw [show D2M8K2.u15216 = KTree.node D2M8K2.t15226 (nat_lit 33093198) (nat_lit 3703064702) (nat_lit 0) D2M8K2.t15227 from rfl, totK_node, tot15226, tot15227]
  decide +kernel

theorem arows15218 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15218 = true := by
  rw [show D2M8K2.u15218 = KTree.node D2M8K2.t15228 (nat_lit 33094874) (nat_lit 3134606968) (nat_lit 0) D2M8K2.t15229 from rfl, allE_node, rows15228, irow15218, rows15229]
  all_goals rfl

theorem atot15218 : totK PD2M8K2 D2M8K2.u15218 = [0, 0, 267188724542, 753877068528, 573040918012, 183390978575, 15908383818, 0] := by
  rw [show D2M8K2.u15218 = KTree.node D2M8K2.t15228 (nat_lit 33094874) (nat_lit 3134606968) (nat_lit 0) D2M8K2.t15229 from rfl, totK_node, tot15228, tot15229]
  decide +kernel

theorem arows15219 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15219 = true := by
  rw [show D2M8K2.u15219 = KTree.node D2M8K2.t15230 (nat_lit 33096376) (nat_lit 3366457695) (nat_lit 0) D2M8K2.t15231 from rfl, allE_node, rows15230, irow15219, rows15231]
  all_goals rfl

theorem atot15219 : totK PD2M8K2 D2M8K2.u15219 = [0, 0, 174317904896, 744559311557, 756462890172, 126008624609, 1369150432, 0] := by
  rw [show D2M8K2.u15219 = KTree.node D2M8K2.t15230 (nat_lit 33096376) (nat_lit 3366457695) (nat_lit 0) D2M8K2.t15231 from rfl, totK_node, tot15230, tot15231]
  decide +kernel

theorem arows15226 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15226 = true := by
  rw [show D2M8K2.u15226 = KTree.node D2M8K2.t15232 (nat_lit 33101926) (nat_lit 3639178577) (nat_lit 0) D2M8K2.t15233 from rfl, allE_node, rows15232, irow15226, rows15233]
  all_goals rfl

theorem atot15226 : totK PD2M8K2 D2M8K2.u15226 = [0, 0, 309825564725, 871334039190, 578657223565, 46912515756, 0, 0] := by
  rw [show D2M8K2.u15226 = KTree.node D2M8K2.t15232 (nat_lit 33101926) (nat_lit 3639178577) (nat_lit 0) D2M8K2.t15233 from rfl, totK_node, tot15232, tot15233]
  decide +kernel

theorem arows15227 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15227 = true := by
  rw [show D2M8K2.u15227 = KTree.node D2M8K2.t15234 (nat_lit 33103429) (nat_lit 1335752211) (nat_lit 0) D2M8K2.t15235 from rfl, allE_node, rows15234, irow15227, rows15235]
  all_goals rfl

theorem atot15227 : totK PD2M8K2 D2M8K2.u15227 = [0, 0, 105140703936, 644832830905, 838385862564, 168980228176, 5352208004, 0] := by
  rw [show D2M8K2.u15227 = KTree.node D2M8K2.t15234 (nat_lit 33103429) (nat_lit 1335752211) (nat_lit 0) D2M8K2.t15235 from rfl, totK_node, tot15234, tot15235]
  decide +kernel

theorem arows15229 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15229 = true := by
  rw [show D2M8K2.u15229 = KTree.node D2M8K2.t15236 (nat_lit 33105535) (nat_lit 2420449048) (nat_lit 0) D2M8K2.t15237 from rfl, allE_node, rows15236, irow15229, rows15237]
  all_goals rfl

theorem atot15229 : totK PD2M8K2 D2M8K2.u15229 = [0, 0, 328772986160, 901169190011, 533269554544, 37558026828, 0, 0] := by
  rw [show D2M8K2.u15229 = KTree.node D2M8K2.t15236 (nat_lit 33105535) (nat_lit 2420449048) (nat_lit 0) D2M8K2.t15237 from rfl, totK_node, tot15236, tot15237]
  decide +kernel

theorem arows15230 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15230 = true := by
  rw [show D2M8K2.u15230 = KTree.node D2M8K2.t15238 (nat_lit 33107022) (nat_lit 3776321014) (nat_lit 0) D2M8K2.t15239 from rfl, allE_node, rows15238, irow15230, rows15239]
  all_goals rfl

theorem atot15230 : totK PD2M8K2 D2M8K2.u15230 = [0, 0, 86407673651, 621577405654, 884203114273, 179745947171, 5408826336, 0] := by
  rw [show D2M8K2.u15230 = KTree.node D2M8K2.t15238 (nat_lit 33107022) (nat_lit 3776321014) (nat_lit 0) D2M8K2.t15239 from rfl, totK_node, tot15238, tot15239]
  decide +kernel

theorem arows15233 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15233 = true := by
  rw [show D2M8K2.u15233 = KTree.node D2M8K2.t15240 (nat_lit 33109107) (nat_lit 3564856250) (nat_lit 0) D2M8K2.t15241 from rfl, allE_node, rows15240, irow15233, rows15241]
  all_goals rfl

theorem atot15233 : totK PD2M8K2 D2M8K2.u15233 = [0, 0, 358204022394, 901059169171, 478635092861, 32928640307, 0, 0] := by
  rw [show D2M8K2.u15233 = KTree.node D2M8K2.t15240 (nat_lit 33109107) (nat_lit 3564856250) (nat_lit 0) D2M8K2.t15241 from rfl, totK_node, tot15240, tot15241]
  decide +kernel

theorem arows15234 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15234 = true := by
  rw [show D2M8K2.u15234 = KTree.node D2M8K2.t15242 (nat_lit 33110852) (nat_lit 3369024564) (nat_lit 0) D2M8K2.t15243 from rfl, allE_node, rows15242, irow15234, rows15243]
  all_goals rfl

theorem atot15234 : totK PD2M8K2 D2M8K2.u15234 = [0, 0, 125663354255, 736219737232, 822176470281, 97086813350, 1096505104, 0] := by
  rw [show D2M8K2.u15234 = KTree.node D2M8K2.t15242 (nat_lit 33110852) (nat_lit 3369024564) (nat_lit 0) D2M8K2.t15243 from rfl, totK_node, tot15242, tot15243]
  decide +kernel

theorem arows15236 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15236 = true := by
  rw [show D2M8K2.u15236 = KTree.node D2M8K2.t15244 (nat_lit 33112829) (nat_lit 1174638327) (nat_lit 0) D2M8K2.t15245 from rfl, allE_node, rows15244, irow15236, rows15245]
  all_goals rfl

theorem atot15236 : totK PD2M8K2 D2M8K2.u15236 = [0, 0, 332761069974, 901860055883, 540618806292, 40163278703, 0, 0] := by
  rw [show D2M8K2.u15236 = KTree.node D2M8K2.t15244 (nat_lit 33112829) (nat_lit 1174638327) (nat_lit 0) D2M8K2.t15245 from rfl, totK_node, tot15244, tot15245]
  decide +kernel

theorem arows15237 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15237 = true := by
  rw [show D2M8K2.u15237 = KTree.node D2M8K2.t15246 (nat_lit 33114511) (nat_lit 1502251380) (nat_lit 0) D2M8K2.t15247 from rfl, allE_node, rows15246, irow15237, rows15247]
  all_goals rfl

theorem atot15237 : totK PD2M8K2 D2M8K2.u15237 = [0, 0, 0, 413019872710, 963392091328, 347580030249, 21771963874, 0] := by
  rw [show D2M8K2.u15237 = KTree.node D2M8K2.t15246 (nat_lit 33114511) (nat_lit 1502251380) (nat_lit 0) D2M8K2.t15247 from rfl, totK_node, tot15246, tot15247]
  decide +kernel

theorem arows15241 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15241 = true := by
  rw [show D2M8K2.u15241 = KTree.node D2M8K2.t15248 (nat_lit 33116352) (nat_lit 3529347033) (nat_lit 0) D2M8K2.t15249 from rfl, allE_node, rows15248, irow15241, rows15249]
  all_goals rfl

theorem atot15241 : totK PD2M8K2 D2M8K2.u15241 = [0, 0, 0, 414554945124, 985160833775, 350467475681, 10822163863, 0] := by
  rw [show D2M8K2.u15241 = KTree.node D2M8K2.t15248 (nat_lit 33116352) (nat_lit 3529347033) (nat_lit 0) D2M8K2.t15249 from rfl, totK_node, tot15248, tot15249]
  decide +kernel

theorem arows15242 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15242 = true := by
  rw [show D2M8K2.u15242 = KTree.node D2M8K2.t15250 (nat_lit 33118076) (nat_lit 2747208146) (nat_lit 8) D2M8K2.t15251 from rfl, allE_node, rows15250, irow15242, rows15251]
  all_goals rfl

theorem atot15242 : totK PD2M8K2 D2M8K2.u15242 = [0, 0, 0, 86403723232, 712235741160, 787504132090, 120165724155, 1369150432] := by
  rw [show D2M8K2.u15242 = KTree.node D2M8K2.t15250 (nat_lit 33118076) (nat_lit 2747208146) (nat_lit 8) D2M8K2.t15251 from rfl, totK_node, tot15250, tot15251]
  decide +kernel

theorem arows15244 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15244 = true := by
  rw [show D2M8K2.u15244 = KTree.node D2M8K2.t15252 (nat_lit 33123657) (nat_lit 1828798327) (nat_lit 0) D2M8K2.t15253 from rfl, allE_node, rows15252, irow15244, rows15253]
  all_goals rfl

theorem atot15244 : totK PD2M8K2 D2M8K2.u15244 = [0, 0, 0, 427987639442, 984600324651, 328606915050, 15331736325, 0] := by
  rw [show D2M8K2.u15244 = KTree.node D2M8K2.t15252 (nat_lit 33123657) (nat_lit 1828798327) (nat_lit 0) D2M8K2.t15253 from rfl, totK_node, tot15252, tot15253]
  decide +kernel

theorem arows15245 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15245 = true := by
  rw [show D2M8K2.u15245 = KTree.node D2M8K2.t15254 (nat_lit 33127157) (nat_lit 1255465289) (nat_lit 544) D2M8K2.t15255 from rfl, allE_node, rows15254, irow15245, rows15255]
  all_goals rfl

theorem atot15245 : totK PD2M8K2 D2M8K2.u15245 = [0, 0, 0, 424577688775, 978692769543, 327599835132, 15364757343, 0] := by
  rw [show D2M8K2.u15245 = KTree.node D2M8K2.t15254 (nat_lit 33127157) (nat_lit 1255465289) (nat_lit 544) D2M8K2.t15255 from rfl, totK_node, tot15254, tot15255]
  decide +kernel

theorem arows15248 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15248 = true := by
  rw [show D2M8K2.u15248 = KTree.node D2M8K2.t15256 (nat_lit 33130436) (nat_lit 3401468245) (nat_lit 0) D2M8K2.t15257 from rfl, allE_node, rows15256, irow15248, rows15257]
  all_goals rfl

theorem atot15248 : totK PD2M8K2 D2M8K2.u15248 = [0, 0, 0, 461073282790, 1034646994801, 272745415903, 4779388410, 0] := by
  rw [show D2M8K2.u15248 = KTree.node D2M8K2.t15256 (nat_lit 33130436) (nat_lit 3401468245) (nat_lit 0) D2M8K2.t15257 from rfl, totK_node, tot15256, tot15257]
  decide +kernel

theorem arows15249 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15249 = true := by
  rw [show D2M8K2.u15249 = KTree.node D2M8K2.t15258 (nat_lit 33134204) (nat_lit 2487942052) (nat_lit 0) D2M8K2.t15259 from rfl, allE_node, rows15258, irow15249, rows15259]
  all_goals rfl

theorem atot15249 : totK PD2M8K2 D2M8K2.u15249 = [0, 0, 179595312347, 582912916775, 704945868221, 285515648971, 21055313582, 0] := by
  rw [show D2M8K2.u15249 = KTree.node D2M8K2.t15258 (nat_lit 33134204) (nat_lit 2487942052) (nat_lit 0) D2M8K2.t15259 from rfl, totK_node, tot15258, tot15259]
  decide +kernel

theorem arows15251 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15251 = true := by
  rw [show D2M8K2.u15251 = KTree.node D2M8K2.t15260 (nat_lit 33178955) (nat_lit 1575941301) (nat_lit 0) D2M8K2.t15261 from rfl, allE_node, rows15260, irow15251, rows15261]
  all_goals rfl

theorem atot15251 : totK PD2M8K2 D2M8K2.u15251 = [0, 0, 238514996341, 797595081269, 617696517480, 94888794367, 1369150432, 0] := by
  rw [show D2M8K2.u15251 = KTree.node D2M8K2.t15260 (nat_lit 33178955) (nat_lit 1575941301) (nat_lit 0) D2M8K2.t15261 from rfl, totK_node, tot15260, tot15261]
  decide +kernel

theorem arows15252 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15252 = true := by
  rw [show D2M8K2.u15252 = KTree.node D2M8K2.t15262 (nat_lit 33180911) (nat_lit 2776205875) (nat_lit 0) D2M8K2.t15263 from rfl, allE_node, rows15262, irow15252, rows15263]
  all_goals rfl

theorem atot15252 : totK PD2M8K2 D2M8K2.u15252 = [0, 0, 177761932530, 769912433733, 790613439267, 91503927817, 0, 0] := by
  rw [show D2M8K2.u15252 = KTree.node D2M8K2.t15262 (nat_lit 33180911) (nat_lit 2776205875) (nat_lit 0) D2M8K2.t15263 from rfl, totK_node, tot15262, tot15263]
  decide +kernel

theorem arows15257 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15257 = true := by
  rw [show D2M8K2.u15257 = KTree.node D2M8K2.t15264 (nat_lit 33183172) (nat_lit 3772544887) (nat_lit 0) D2M8K2.t15265 from rfl, allE_node, rows15264, irow15257, rows15265]
  all_goals rfl

theorem atot15257 : totK PD2M8K2 D2M8K2.u15257 = [0, 0, 190278575310, 775565013322, 750847079327, 124069158204, 1527735764, 0] := by
  rw [show D2M8K2.u15257 = KTree.node D2M8K2.t15264 (nat_lit 33183172) (nat_lit 3772544887) (nat_lit 0) D2M8K2.t15265 from rfl, totK_node, tot15264, tot15265]
  decide +kernel

theorem arows15258 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15258 = true := by
  rw [show D2M8K2.u15258 = KTree.node D2M8K2.t15266 (nat_lit 33185152) (nat_lit 3781001236) (nat_lit 0) D2M8K2.t15267 from rfl, allE_node, rows15266, irow15258, rows15267]
  all_goals rfl

theorem atot15258 : totK PD2M8K2 D2M8K2.u15258 = [0, 0, 380535832407, 937214560851, 466288573167, 31116446293, 0, 0] := by
  rw [show D2M8K2.u15258 = KTree.node D2M8K2.t15266 (nat_lit 33185152) (nat_lit 3781001236) (nat_lit 0) D2M8K2.t15267 from rfl, totK_node, tot15266, tot15267]
  decide +kernel

theorem arows15260 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15260 = true := by
  rw [show D2M8K2.u15260 = KTree.node D2M8K2.t15268 (nat_lit 33186836) (nat_lit 3061053753) (nat_lit 0) D2M8K2.t15269 from rfl, allE_node, rows15268, irow15260, rows15269]
  all_goals rfl

theorem atot15260 : totK PD2M8K2 D2M8K2.u15260 = [0, 0, 52367425283, 596171382421, 950590734207, 207601628245, 5398830306, 0] := by
  rw [show D2M8K2.u15260 = KTree.node D2M8K2.t15268 (nat_lit 33186836) (nat_lit 3061053753) (nat_lit 0) D2M8K2.t15269 from rfl, totK_node, tot15268, tot15269]
  decide +kernel

theorem arows15261 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15261 = true := by
  rw [show D2M8K2.u15261 = KTree.node D2M8K2.t15270 (nat_lit 33192142) (nat_lit 3860499858) (nat_lit 0) D2M8K2.t15271 from rfl, allE_node, rows15270, irow15261, rows15271]
  all_goals rfl

theorem atot15261 : totK PD2M8K2 D2M8K2.u15261 = [0, 0, 341895108184, 930185699552, 482704342610, 25705360076, 0, 0] := by
  rw [show D2M8K2.u15261 = KTree.node D2M8K2.t15270 (nat_lit 33192142) (nat_lit 3860499858) (nat_lit 0) D2M8K2.t15271 from rfl, totK_node, tot15270, tot15271]
  decide +kernel

theorem arows15264 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15264 = true := by
  rw [show D2M8K2.u15264 = KTree.node D2M8K2.t15272 (nat_lit 33194326) (nat_lit 2253142027) (nat_lit 0) D2M8K2.t15273 from rfl, allE_node, rows15272, irow15264, rows15273]
  all_goals rfl

theorem atot15264 : totK PD2M8K2 D2M8K2.u15264 = [0, 0, 166385995759, 750801033097, 780738871954, 95719199924, 1096505104, 0] := by
  rw [show D2M8K2.u15264 = KTree.node D2M8K2.t15272 (nat_lit 33194326) (nat_lit 2253142027) (nat_lit 0) D2M8K2.t15273 from rfl, totK_node, tot15272, tot15273]
  decide +kernel

theorem arows15265 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15265 = true := by
  rw [show D2M8K2.u15265 = KTree.node D2M8K2.t15274 (nat_lit 33196327) (nat_lit 2292363113) (nat_lit 0) D2M8K2.t15275 from rfl, allE_node, rows15274, irow15265, rows15275]
  all_goals rfl

theorem atot15265 : totK PD2M8K2 D2M8K2.u15265 = [0, 0, 249589912045, 799741666501, 666769979654, 101282995500, 1232398321, 0] := by
  rw [show D2M8K2.u15265 = KTree.node D2M8K2.t15274 (nat_lit 33196327) (nat_lit 2292363113) (nat_lit 0) D2M8K2.t15275 from rfl, totK_node, tot15274, tot15275]
  decide +kernel

theorem arows15267 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15267 = true := by
  rw [show D2M8K2.u15267 = KTree.node D2M8K2.t15276 (nat_lit 33198129) (nat_lit 897266170) (nat_lit 0) D2M8K2.t15277 from rfl, allE_node, rows15276, irow15267, rows15277]
  all_goals rfl

theorem atot15267 : totK PD2M8K2 D2M8K2.u15267 = [0, 0, 160530476227, 651711034223, 754644426330, 217183533277, 12451903996, 0] := by
  rw [show D2M8K2.u15267 = KTree.node D2M8K2.t15276 (nat_lit 33198129) (nat_lit 897266170) (nat_lit 0) D2M8K2.t15277 from rfl, totK_node, tot15276, tot15277]
  decide +kernel

theorem arows15268 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15268 = true := by
  rw [show D2M8K2.u15268 = KTree.node D2M8K2.t15278 (nat_lit 33220441) (nat_lit 1413477595) (nat_lit 0) D2M8K2.t15279 from rfl, allE_node, rows15278, irow15268, rows15279]
  all_goals rfl

theorem atot15268 : totK PD2M8K2 D2M8K2.u15268 = [0, 0, 257616742368, 799762688606, 611262673319, 95563024220, 1369150432, 0] := by
  rw [show D2M8K2.u15268 = KTree.node D2M8K2.t15278 (nat_lit 33220441) (nat_lit 1413477595) (nat_lit 0) D2M8K2.t15279 from rfl, totK_node, tot15278, tot15279]
  decide +kernel

theorem arows15272 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15272 = true := by
  rw [show D2M8K2.u15272 = KTree.node D2M8K2.t15280 (nat_lit 33222844) (nat_lit 3804072973) (nat_lit 0) D2M8K2.t15281 from rfl, allE_node, rows15280, irow15272, rows15281]
  all_goals rfl

theorem atot15272 : totK PD2M8K2 D2M8K2.u15272 = [0, 0, 177858628197, 777634950009, 791638153188, 89939798657, 0, 0] := by
  rw [show D2M8K2.u15272 = KTree.node D2M8K2.t15280 (nat_lit 33222844) (nat_lit 3804072973) (nat_lit 0) D2M8K2.t15281 from rfl, totK_node, tot15280, tot15281]
  decide +kernel

theorem arows15273 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15273 = true := by
  rw [show D2M8K2.u15273 = KTree.node D2M8K2.t15282 (nat_lit 33224647) (nat_lit 2320598580) (nat_lit 0) D2M8K2.t15283 from rfl, allE_node, rows15282, irow15273, rows15283]
  all_goals rfl

theorem atot15273 : totK PD2M8K2 D2M8K2.u15273 = [0, 0, 204004210429, 780926349251, 734208679450, 122241949014, 1535615586, 0] := by
  rw [show D2M8K2.u15273 = KTree.node D2M8K2.t15282 (nat_lit 33224647) (nat_lit 2320598580) (nat_lit 0) D2M8K2.t15283 from rfl, totK_node, tot15282, tot15283]
  decide +kernel

theorem arows15275 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15275 = true := by
  rw [show D2M8K2.u15275 = KTree.node D2M8K2.t15284 (nat_lit 33230405) (nat_lit 1928807960) (nat_lit 0) D2M8K2.t15285 from rfl, allE_node, rows15284, irow15275, rows15285]
  all_goals rfl

theorem atot15275 : totK PD2M8K2 D2M8K2.u15275 = [0, 0, 378358566006, 947239162389, 470715160243, 31359313794, 0, 0] := by
  rw [show D2M8K2.u15275 = KTree.node D2M8K2.t15284 (nat_lit 33230405) (nat_lit 1928807960) (nat_lit 0) D2M8K2.t15285 from rfl, totK_node, tot15284, tot15285]
  decide +kernel

theorem arows15276 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15276 = true := by
  rw [show D2M8K2.u15276 = KTree.node D2M8K2.t15286 (nat_lit 33232065) (nat_lit 1793251838) (nat_lit 0) D2M8K2.t15287 from rfl, allE_node, rows15286, irow15276, rows15287]
  all_goals rfl

theorem atot15276 : totK PD2M8K2 D2M8K2.u15276 = [0, 0, 41803805519, 587652580081, 950539846279, 216175713008, 5436324950, 0] := by
  rw [show D2M8K2.u15276 = KTree.node D2M8K2.t15286 (nat_lit 33232065) (nat_lit 1793251838) (nat_lit 0) D2M8K2.t15287 from rfl, totK_node, tot15286, tot15287]
  decide +kernel

theorem arows15279 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15279 = true := by
  rw [show D2M8K2.u15279 = KTree.node D2M8K2.t15288 (nat_lit 33233725) (nat_lit 987341109) (nat_lit 0) D2M8K2.t15289 from rfl, allE_node, rows15288, irow15279, rows15289]
  all_goals rfl

theorem atot15279 : totK PD2M8K2 D2M8K2.u15279 = [0, 0, 344825257504, 936842204987, 485652337377, 25804602326, 0, 0] := by
  rw [show D2M8K2.u15279 = KTree.node D2M8K2.t15288 (nat_lit 33233725) (nat_lit 987341109) (nat_lit 0) D2M8K2.t15289 from rfl, totK_node, tot15288, tot15289]
  decide +kernel

theorem arows15280 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15280 = true := by
  rw [show D2M8K2.u15280 = KTree.node D2M8K2.t15290 (nat_lit 33235807) (nat_lit 2310890434) (nat_lit 0) D2M8K2.t15291 from rfl, allE_node, rows15290, irow15280, rows15291]
  all_goals rfl

theorem atot15280 : totK PD2M8K2 D2M8K2.u15280 = [0, 0, 166428564004, 750137014470, 781295963718, 96115471263, 1096505104, 0] := by
  rw [show D2M8K2.u15280 = KTree.node D2M8K2.t15290 (nat_lit 33235807) (nat_lit 2310890434) (nat_lit 0) D2M8K2.t15291 from rfl, totK_node, tot15290, tot15291]
  decide +kernel

theorem arows15282 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15282 = true := by
  rw [show D2M8K2.u15282 = KTree.node D2M8K2.t15292 (nat_lit 33237808) (nat_lit 3261704642) (nat_lit 0) D2M8K2.t15293 from rfl, allE_node, rows15292, irow15282, rows15293]
  all_goals rfl

theorem atot15282 : totK PD2M8K2 D2M8K2.u15282 = [0, 0, 249620980851, 793151006522, 671170364207, 102490350401, 1232609433, 0] := by
  rw [show D2M8K2.u15282 = KTree.node D2M8K2.t15292 (nat_lit 33237808) (nat_lit 3261704642) (nat_lit 0) D2M8K2.t15293 from rfl, totK_node, tot15292, tot15293]
  decide +kernel

theorem arows15283 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15283 = true := by
  rw [show D2M8K2.u15283 = KTree.node D2M8K2.t15294 (nat_lit 33239610) (nat_lit 3896407253) (nat_lit 0) D2M8K2.t15295 from rfl, allE_node, rows15294, irow15283, rows15295]
  all_goals rfl

theorem atot15283 : totK PD2M8K2 D2M8K2.u15283 = [0, 0, 175465715302, 662207466743, 736707435000, 215041229938, 12482056447, 0] := by
  rw [show D2M8K2.u15283 = KTree.node D2M8K2.t15294 (nat_lit 33239610) (nat_lit 3896407253) (nat_lit 0) D2M8K2.t15295 from rfl, totK_node, tot15294, tot15295]
  decide +kernel

theorem arows15289 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15289 = true := by
  rw [show D2M8K2.u15289 = KTree.node D2M8K2.t15296 (nat_lit 33261862) (nat_lit 1243926359) (nat_lit 0) D2M8K2.t15297 from rfl, allE_node, rows15296, irow15289, rows15297]
  all_goals rfl

theorem atot15289 : totK PD2M8K2 D2M8K2.u15289 = [0, 0, 242902929564, 792913067957, 634277491138, 91444677309, 1369150432, 0] := by
  rw [show D2M8K2.u15289 = KTree.node D2M8K2.t15296 (nat_lit 33261862) (nat_lit 1243926359) (nat_lit 0) D2M8K2.t15297 from rfl, totK_node, tot15296, tot15297]
  decide +kernel

theorem arows15290 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15290 = true := by
  rw [show D2M8K2.u15290 = KTree.node D2M8K2.t15298 (nat_lit 33267508) (nat_lit 4009520606) (nat_lit 0) D2M8K2.t15299 from rfl, allE_node, rows15298, irow15290, rows15299]
  all_goals rfl

theorem atot15290 : totK PD2M8K2 D2M8K2.u15290 = [0, 0, 234488056956, 823568947221, 709625218980, 52063202223, 0, 0] := by
  rw [show D2M8K2.u15290 = KTree.node D2M8K2.t15298 (nat_lit 33267508) (nat_lit 4009520606) (nat_lit 0) D2M8K2.t15299 from rfl, totK_node, tot15298, tot15299]
  decide +kernel

theorem arows15292 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15292 = true := by
  rw [show D2M8K2.u15292 = KTree.node D2M8K2.t15300 (nat_lit 33269089) (nat_lit 1431170305) (nat_lit 0) D2M8K2.t15301 from rfl, allE_node, rows15300, irow15292, rows15301]
  all_goals rfl

theorem atot15292 : totK PD2M8K2 D2M8K2.u15292 = [0, 0, 164640597464, 765877253737, 745227226860, 96303091351, 1164319620, 0] := by
  rw [show D2M8K2.u15292 = KTree.node D2M8K2.t15300 (nat_lit 33269089) (nat_lit 1431170305) (nat_lit 0) D2M8K2.t15301 from rfl, totK_node, tot15300, tot15301]
  decide +kernel

theorem arows15293 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15293 = true := by
  rw [show D2M8K2.u15293 = KTree.node D2M8K2.t15302 (nat_lit 33271322) (nat_lit 4006803394) (nat_lit 0) D2M8K2.t15303 from rfl, allE_node, rows15302, irow15293, rows15303]
  all_goals rfl

theorem atot15293 : totK PD2M8K2 D2M8K2.u15293 = [0, 0, 331242500164, 894311829131, 544646867968, 41239368677, 0, 0] := by
  rw [show D2M8K2.u15293 = KTree.node D2M8K2.t15302 (nat_lit 33271322) (nat_lit 4006803394) (nat_lit 0) D2M8K2.t15303 from rfl, totK_node, tot15302, tot15303]
  decide +kernel

theorem arows15296 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15296 = true := by
  rw [show D2M8K2.u15296 = KTree.node D2M8K2.t15304 (nat_lit 33273001) (nat_lit 1244538989) (nat_lit 0) D2M8K2.t15305 from rfl, allE_node, rows15304, irow15296, rows15305]
  all_goals rfl

theorem atot15296 : totK PD2M8K2 D2M8K2.u15296 = [0, 0, 122626901600, 717021754208, 836022856275, 110471120808, 1198073392, 0] := by
  rw [show D2M8K2.u15296 = KTree.node D2M8K2.t15304 (nat_lit 33273001) (nat_lit 1244538989) (nat_lit 0) D2M8K2.t15305 from rfl, totK_node, tot15304, tot15305]
  decide +kernel

theorem arows15297 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15297 = true := by
  rw [show D2M8K2.u15297 = KTree.node D2M8K2.t15306 (nat_lit 33275096) (nat_lit 3500368473) (nat_lit 0) D2M8K2.t15307 from rfl, allE_node, rows15306, irow15297, rows15307]
  all_goals rfl

theorem atot15297 : totK PD2M8K2 D2M8K2.u15297 = [0, 0, 368400166140, 931406510260, 471125031631, 28136581031, 0, 0] := by
  rw [show D2M8K2.u15297 = KTree.node D2M8K2.t15306 (nat_lit 33275096) (nat_lit 3500368473) (nat_lit 0) D2M8K2.t15307 from rfl, totK_node, tot15306, tot15307]
  decide +kernel

theorem arows15299 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15299 = true := by
  rw [show D2M8K2.u15299 = KTree.node D2M8K2.t15308 (nat_lit 33276968) (nat_lit 3607397541) (nat_lit 0) D2M8K2.t15309 from rfl, allE_node, rows15308, irow15299, rows15309]
  all_goals rfl

theorem atot15299 : totK PD2M8K2 D2M8K2.u15299 = [0, 0, 112582420456, 746094533626, 831940427618, 105345178223, 1096505104, 0] := by
  rw [show D2M8K2.u15299 = KTree.node D2M8K2.t15308 (nat_lit 33276968) (nat_lit 3607397541) (nat_lit 0) D2M8K2.t15309 from rfl, totK_node, tot15308, tot15309]
  decide +kernel

theorem arows15300 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15300 = true := by
  rw [show D2M8K2.u15300 = KTree.node D2M8K2.t15310 (nat_lit 33303233) (nat_lit 1858375731) (nat_lit 512) D2M8K2.t15311 from rfl, allE_node, rows15310, irow15300, rows15311]
  all_goals rfl

theorem atot15300 : totK PD2M8K2 D2M8K2.u15300 = [0, 0, 307554212943, 880841182856, 546459800418, 41986741325, 0, 0] := by
  rw [show D2M8K2.u15300 = KTree.node D2M8K2.t15310 (nat_lit 33303233) (nat_lit 1858375731) (nat_lit 512) D2M8K2.t15311 from rfl, totK_node, tot15310, tot15311]
  decide +kernel

theorem arows15304 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15304 = true := by
  rw [show D2M8K2.u15304 = KTree.node D2M8K2.t15312 (nat_lit 33305219) (nat_lit 2892595378) (nat_lit 0) D2M8K2.t15313 from rfl, allE_node, rows15312, irow15304, rows15313]
  all_goals rfl

theorem atot15304 : totK PD2M8K2 D2M8K2.u15304 = [0, 0, 173835435312, 716812875891, 813311275841, 133417733770, 1369150432, 0] := by
  rw [show D2M8K2.u15304 = KTree.node D2M8K2.t15312 (nat_lit 33305219) (nat_lit 2892595378) (nat_lit 0) D2M8K2.t15313 from rfl, totK_node, tot15312, tot15313]
  decide +kernel

theorem arows15305 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15305 = true := by
  rw [show D2M8K2.u15305 = KTree.node D2M8K2.t15314 (nat_lit 33307114) (nat_lit 3984693379) (nat_lit 0) D2M8K2.t15315 from rfl, allE_node, rows15314, irow15305, rows15315]
  all_goals rfl

theorem atot15305 : totK PD2M8K2 D2M8K2.u15305 = [0, 0, 173977021590, 772512233921, 775930803588, 119800625242, 1402015981, 0] := by
  rw [show D2M8K2.u15305 = KTree.node D2M8K2.t15314 (nat_lit 33307114) (nat_lit 3984693379) (nat_lit 0) D2M8K2.t15315 from rfl, totK_node, tot15314, tot15315]
  decide +kernel

theorem arows15307 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15307 = true := by
  rw [show D2M8K2.u15307 = KTree.node D2M8K2.t15316 (nat_lit 33309170) (nat_lit 2053375728) (nat_lit 0) D2M8K2.t15317 from rfl, allE_node, rows15316, irow15307, rows15317]
  all_goals rfl

theorem atot15307 : totK PD2M8K2 D2M8K2.u15307 = [0, 0, 257009321714, 731092064932, 638405752855, 178856957314, 8173611642, 0] := by
  rw [show D2M8K2.u15307 = KTree.node D2M8K2.t15316 (nat_lit 33309170) (nat_lit 2053375728) (nat_lit 0) D2M8K2.t15317 from rfl, totK_node, tot15316, tot15317]
  decide +kernel

theorem arows15308 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15308 = true := by
  rw [show D2M8K2.u15308 = KTree.node D2M8K2.t15318 (nat_lit 33310728) (nat_lit 3574372099) (nat_lit 0) D2M8K2.t15319 from rfl, allE_node, rows15318, irow15308, rows15319]
  all_goals rfl

theorem atot15308 : totK PD2M8K2 D2M8K2.u15308 = [0, 0, 155100548217, 682877796010, 784990324698, 165974071775, 5138457373, 0] := by
  rw [show D2M8K2.u15308 = KTree.node D2M8K2.t15318 (nat_lit 33310728) (nat_lit 3574372099) (nat_lit 0) D2M8K2.t15319 from rfl, totK_node, tot15318, tot15319]
  decide +kernel

theorem arows15311 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15311 = true := by
  rw [show D2M8K2.u15311 = KTree.node D2M8K2.t15320 (nat_lit 33312763) (nat_lit 2231192147) (nat_lit 0) D2M8K2.t15321 from rfl, allE_node, rows15320, irow15311, rows15321]
  all_goals rfl

theorem atot15311 : totK PD2M8K2 D2M8K2.u15311 = [0, 0, 313209930095, 876593460478, 589733651848, 55703366858, 0, 0] := by
  rw [show D2M8K2.u15311 = KTree.node D2M8K2.t15320 (nat_lit 33312763) (nat_lit 2231192147) (nat_lit 0) D2M8K2.t15321 from rfl, totK_node, tot15320, tot15321]
  decide +kernel

theorem arows15312 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15312 = true := by
  rw [show D2M8K2.u15312 = KTree.node D2M8K2.t15322 (nat_lit 33314278) (nat_lit 2239516883) (nat_lit 0) D2M8K2.t15323 from rfl, allE_node, rows15322, irow15312, rows15323]
  all_goals rfl

theorem atot15312 : totK PD2M8K2 D2M8K2.u15312 = [0, 0, 99143845592, 646815501309, 857672832105, 179402849528, 5193381917, 0] := by
  rw [show D2M8K2.u15312 = KTree.node D2M8K2.t15322 (nat_lit 33314278) (nat_lit 2239516883) (nat_lit 0) D2M8K2.t15323 from rfl, totK_node, tot15322, tot15323]
  decide +kernel

theorem arows15314 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15314 = true := by
  rw [show D2M8K2.u15314 = KTree.node D2M8K2.t15324 (nat_lit 33319773) (nat_lit 1040233743) (nat_lit 0) D2M8K2.t15325 from rfl, allE_node, rows15324, irow15314, rows15325]
  all_goals rfl

theorem atot15314 : totK PD2M8K2 D2M8K2.u15314 = [0, 0, 348189571139, 902961510935, 538990077823, 52300695047, 0, 0] := by
  rw [show D2M8K2.u15314 = KTree.node D2M8K2.t15324 (nat_lit 33319773) (nat_lit 1040233743) (nat_lit 0) D2M8K2.t15325 from rfl, totK_node, tot15324, tot15325]
  decide +kernel

theorem arows15315 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15315 = true := by
  rw [show D2M8K2.u15315 = KTree.node D2M8K2.t15326 (nat_lit 33321218) (nat_lit 3147488237) (nat_lit 0) D2M8K2.t15327 from rfl, allE_node, rows15326, irow15315, rows15327]
  all_goals rfl

theorem atot15315 : totK PD2M8K2 D2M8K2.u15315 = [0, 0, 93773531552, 629774292067, 871651815598, 206062530199, 4882834716, 0] := by
  rw [show D2M8K2.u15315 = KTree.node D2M8K2.t15326 (nat_lit 33321218) (nat_lit 3147488237) (nat_lit 0) D2M8K2.t15327 from rfl, totK_node, tot15326, tot15327]
  decide +kernel

theorem arows15320 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15320 = true := by
  rw [show D2M8K2.u15320 = KTree.node D2M8K2.t15328 (nat_lit 33388820) (nat_lit 3676162564) (nat_lit 0) D2M8K2.t15329 from rfl, allE_node, rows15328, irow15320, rows15329]
  all_goals rfl

theorem atot15320 : totK PD2M8K2 D2M8K2.u15320 = [0, 245869199736, 561621473628, 419003715093, 386983134505, 200034575611, 17014456371, 0] := by
  rw [show D2M8K2.u15320 = KTree.node D2M8K2.t15328 (nat_lit 33388820) (nat_lit 3676162564) (nat_lit 0) D2M8K2.t15329 from rfl, totK_node, tot15328, tot15329]
  decide +kernel

theorem arows15321 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15321 = true := by
  rw [show D2M8K2.u15321 = KTree.node D2M8K2.t15330 (nat_lit 33389986) (nat_lit 4194847968) (nat_lit 0) D2M8K2.t15331 from rfl, allE_node, rows15330, irow15321, rows15331]
  all_goals rfl

theorem atot15321 : totK PD2M8K2 D2M8K2.u15321 = [0, 199700952467, 746182404683, 662662531759, 206097439466, 21400436502, 0, 0] := by
  rw [show D2M8K2.u15321 = KTree.node D2M8K2.t15330 (nat_lit 33389986) (nat_lit 4194847968) (nat_lit 0) D2M8K2.t15331 from rfl, totK_node, tot15330, tot15331]
  decide +kernel

theorem arows15323 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15323 = true := by
  rw [show D2M8K2.u15323 = KTree.node D2M8K2.t15332 (nat_lit 33391410) (nat_lit 3415279830) (nat_lit 0) D2M8K2.t15333 from rfl, allE_node, rows15332, irow15323, rows15333]
  all_goals rfl

theorem atot15323 : totK PD2M8K2 D2M8K2.u15323 = [0, 70039974391, 465683410070, 865687464217, 381056651588, 16208961603, 0, 0] := by
  rw [show D2M8K2.u15323 = KTree.node D2M8K2.t15332 (nat_lit 33391410) (nat_lit 3415279830) (nat_lit 0) D2M8K2.t15333 from rfl, totK_node, tot15332, tot15333]
  decide +kernel

theorem arows15324 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15324 = true := by
  rw [show D2M8K2.u15324 = KTree.node D2M8K2.t15334 (nat_lit 33392709) (nat_lit 1470583704) (nat_lit 0) D2M8K2.t15335 from rfl, allE_node, rows15334, irow15324, rows15335]
  all_goals rfl

theorem atot15324 : totK PD2M8K2 D2M8K2.u15324 = [0, 346128489011, 911087292412, 523426025706, 46623966761, 0, 0, 0] := by
  rw [show D2M8K2.u15324 = KTree.node D2M8K2.t15334 (nat_lit 33392709) (nat_lit 1470583704) (nat_lit 0) D2M8K2.t15335 from rfl, totK_node, tot15334, tot15335]
  decide +kernel

theorem arows15327 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15327 = true := by
  rw [show D2M8K2.u15327 = KTree.node D2M8K2.t15336 (nat_lit 33394416) (nat_lit 3181674432) (nat_lit 0) D2M8K2.t15337 from rfl, allE_node, rows15336, irow15327, rows15337]
  all_goals rfl

theorem atot15327 : totK PD2M8K2 D2M8K2.u15327 = [0, 65835198230, 526140447161, 894480410784, 278278259414, 11619426831, 0, 0] := by
  rw [show D2M8K2.u15327 = KTree.node D2M8K2.t15336 (nat_lit 33394416) (nat_lit 3181674432) (nat_lit 0) D2M8K2.t15337 from rfl, totK_node, tot15336, tot15337]
  decide +kernel

theorem arows15328 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15328 = true := by
  rw [show D2M8K2.u15328 = KTree.node D2M8K2.t15338 (nat_lit 33396366) (nat_lit 3953930835) (nat_lit 0) D2M8K2.t15339 from rfl, allE_node, rows15338, irow15328, rows15339]
  all_goals rfl

theorem atot15328 : totK PD2M8K2 D2M8K2.u15328 = [0, 354500548690, 930101299557, 504471391274, 36825110626, 0, 0, 0] := by
  rw [show D2M8K2.u15328 = KTree.node D2M8K2.t15338 (nat_lit 33396366) (nat_lit 3953930835) (nat_lit 0) D2M8K2.t15339 from rfl, totK_node, tot15338, tot15339]
  decide +kernel

theorem arows15330 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15330 = true := by
  rw [show D2M8K2.u15330 = KTree.node D2M8K2.t15340 (nat_lit 33398064) (nat_lit 3418282687) (nat_lit 0) D2M8K2.t15341 from rfl, allE_node, rows15340, irow15330, rows15341]
  all_goals rfl

theorem atot15330 : totK PD2M8K2 D2M8K2.u15330 = [0, 33314680501, 489369934714, 943078966163, 299639591865, 11778552896, 0, 0] := by
  rw [show D2M8K2.u15330 = KTree.node D2M8K2.t15340 (nat_lit 33398064) (nat_lit 3418282687) (nat_lit 0) D2M8K2.t15341 from rfl, totK_node, tot15340, tot15341]
  decide +kernel

theorem arows15331 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15331 = true := by
  rw [show D2M8K2.u15331 = KTree.node D2M8K2.t15342 (nat_lit 33399514) (nat_lit 2859915750) (nat_lit 0) D2M8K2.t15343 from rfl, allE_node, rows15342, irow15331, rows15343]
  all_goals rfl

theorem atot15331 : totK PD2M8K2 D2M8K2.u15331 = [0, 368635542237, 930349534679, 480472013872, 36818067980, 0, 0, 0] := by
  rw [show D2M8K2.u15331 = KTree.node D2M8K2.t15342 (nat_lit 33399514) (nat_lit 2859915750) (nat_lit 0) D2M8K2.t15343 from rfl, totK_node, tot15342, tot15343]
  decide +kernel

theorem arows15335 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15335 = true := by
  rw [show D2M8K2.u15335 = KTree.node D2M8K2.t15344 (nat_lit 33401450) (nat_lit 4051909980) (nat_lit 0) D2M8K2.t15345 from rfl, allE_node, rows15344, irow15335, rows15345]
  all_goals rfl

theorem atot15335 : totK PD2M8K2 D2M8K2.u15335 = [0, 88130666923, 668361764386, 880073742980, 174921991804, 2585032425, 0, 0] := by
  rw [show D2M8K2.u15335 = KTree.node D2M8K2.t15344 (nat_lit 33401450) (nat_lit 4051909980) (nat_lit 0) D2M8K2.t15345 from rfl, totK_node, tot15344, tot15345]
  decide +kernel

theorem arows15336 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15336 = true := by
  rw [show D2M8K2.u15336 = KTree.node D2M8K2.t15346 (nat_lit 33403116) (nat_lit 3261012785) (nat_lit 0) D2M8K2.t15347 from rfl, allE_node, rows15346, irow15336, rows15347]
  all_goals rfl

theorem atot15336 : totK PD2M8K2 D2M8K2.u15336 = [0, 337802990761, 903474039006, 542592231767, 52074480095, 0, 0, 0] := by
  rw [show D2M8K2.u15336 = KTree.node D2M8K2.t15346 (nat_lit 33403116) (nat_lit 3261012785) (nat_lit 0) D2M8K2.t15347 from rfl, totK_node, tot15346, tot15347]
  decide +kernel

theorem arows15338 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15338 = true := by
  rw [show D2M8K2.u15338 = KTree.node D2M8K2.t15348 (nat_lit 33404788) (nat_lit 3586169552) (nat_lit 0) D2M8K2.t15349 from rfl, allE_node, rows15348, irow15338, rows15349]
  all_goals rfl

theorem atot15338 : totK PD2M8K2 D2M8K2.u15338 = [0, 0, 408691600788, 974121445726, 382039810120, 16183166396, 0, 0] := by
  rw [show D2M8K2.u15338 = KTree.node D2M8K2.t15348 (nat_lit 33404788) (nat_lit 3586169552) (nat_lit 0) D2M8K2.t15349 from rfl, totK_node, tot15348, tot15349]
  decide +kernel

theorem arows15339 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15339 = true := by
  rw [show D2M8K2.u15339 = KTree.node D2M8K2.t15350 (nat_lit 33409977) (nat_lit 1871988145) (nat_lit 0) D2M8K2.t15351 from rfl, allE_node, rows15350, irow15339, rows15351]
  all_goals rfl

theorem atot15339 : totK PD2M8K2 D2M8K2.u15339 = [0, 0, 368728114393, 924167394725, 508383911472, 43248091783, 0, 0] := by
  rw [show D2M8K2.u15339 = KTree.node D2M8K2.t15350 (nat_lit 33409977) (nat_lit 1871988145) (nat_lit 0) D2M8K2.t15351 from rfl, totK_node, tot15350, tot15351]
  decide +kernel

theorem arows15342 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15342 = true := by
  rw [show D2M8K2.u15342 = KTree.node D2M8K2.t15352 (nat_lit 33411436) (nat_lit 3683956900) (nat_lit 0) D2M8K2.t15353 from rfl, allE_node, rows15352, irow15342, rows15353]
  all_goals rfl

theorem atot15342 : totK PD2M8K2 D2M8K2.u15342 = [0, 0, 75203464672, 523678602501, 834322660095, 356994628030, 29044448997, 0] := by
  rw [show D2M8K2.u15342 = KTree.node D2M8K2.t15352 (nat_lit 33411436) (nat_lit 3683956900) (nat_lit 0) D2M8K2.t15353 from rfl, totK_node, tot15352, tot15353]
  decide +kernel

theorem arows15343 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15343 = true := by
  rw [show D2M8K2.u15343 = KTree.node D2M8K2.t15354 (nat_lit 33412735) (nat_lit 1608585582) (nat_lit 0) D2M8K2.t15355 from rfl, allE_node, rows15354, irow15343, rows15355]
  all_goals rfl

theorem atot15343 : totK PD2M8K2 D2M8K2.u15343 = [0, 0, 247381763054, 692233166787, 656349664643, 206962420895, 7877424857, 0] := by
  rw [show D2M8K2.u15343 = KTree.node D2M8K2.t15354 (nat_lit 33412735) (nat_lit 1608585582) (nat_lit 0) D2M8K2.t15355 from rfl, totK_node, tot15354, tot15355]
  decide +kernel

theorem arows15345 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15345 = true := by
  rw [show D2M8K2.u15345 = KTree.node D2M8K2.t15356 (nat_lit 33414225) (nat_lit 1295035201) (nat_lit 0) D2M8K2.t15357 from rfl, allE_node, rows15356, irow15345, rows15357]
  all_goals rfl

theorem atot15345 : totK PD2M8K2 D2M8K2.u15345 = [0, 0, 170801653863, 761067452372, 739299065872, 116920481472, 2909416399, 0] := by
  rw [show D2M8K2.u15345 = KTree.node D2M8K2.t15356 (nat_lit 33414225) (nat_lit 1295035201) (nat_lit 0) D2M8K2.t15357 from rfl, totK_node, tot15356, tot15357]
  decide +kernel

theorem arows15346 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15346 = true := by
  rw [show D2M8K2.u15346 = KTree.node D2M8K2.t15358 (nat_lit 33416310) (nat_lit 3699696980) (nat_lit 0) D2M8K2.t15359 from rfl, allE_node, rows15358, irow15346, rows15359]
  all_goals rfl

theorem atot15346 : totK PD2M8K2 D2M8K2.u15346 = [0, 0, 247544863476, 764902301571, 664658335483, 125097659900, 2250452236, 0] := by
  rw [show D2M8K2.u15346 = KTree.node D2M8K2.t15358 (nat_lit 33416310) (nat_lit 3699696980) (nat_lit 0) D2M8K2.t15359 from rfl, totK_node, tot15358, tot15359]
  decide +kernel

theorem arows15356 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15356 = true := by
  rw [show D2M8K2.u15356 = KTree.node D2M8K2.t15360 (nat_lit 33417778) (nat_lit 4169091573) (nat_lit 0) D2M8K2.t15361 from rfl, allE_node, rows15360, irow15356, rows15361]
  all_goals rfl

theorem atot15356 : totK PD2M8K2 D2M8K2.u15356 = [0, 0, 170874428049, 745031017804, 725279405440, 138125516315, 4031931762, 0] := by
  rw [show D2M8K2.u15356 = KTree.node D2M8K2.t15360 (nat_lit 33417778) (nat_lit 4169091573) (nat_lit 0) D2M8K2.t15361 from rfl, totK_node, tot15360, tot15361]
  decide +kernel

theorem arows15357 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15357 = true := by
  rw [show D2M8K2.u15357 = KTree.node D2M8K2.t15362 (nat_lit 33419905) (nat_lit 1247514891) (nat_lit 0) D2M8K2.t15363 from rfl, allE_node, rows15362, irow15357, rows15363]
  all_goals rfl

theorem atot15357 : totK PD2M8K2 D2M8K2.u15357 = [0, 0, 277048498814, 791698348105, 621249218738, 104308071027, 1186940923, 0] := by
  rw [show D2M8K2.u15357 = KTree.node D2M8K2.t15362 (nat_lit 33419905) (nat_lit 1247514891) (nat_lit 0) D2M8K2.t15363 from rfl, totK_node, tot15362, tot15363]
  decide +kernel

theorem arows15359 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15359 = true := by
  rw [show D2M8K2.u15359 = KTree.node D2M8K2.t15364 (nat_lit 33421592) (nat_lit 3732255902) (nat_lit 0) D2M8K2.t15365 from rfl, allE_node, rows15364, irow15359, rows15365]
  all_goals rfl

theorem atot15359 : totK PD2M8K2 D2M8K2.u15359 = [0, 0, 123001750377, 756347056871, 834909037630, 90157277089, 0, 0] := by
  rw [show D2M8K2.u15359 = KTree.node D2M8K2.t15364 (nat_lit 33421592) (nat_lit 3732255902) (nat_lit 0) D2M8K2.t15365 from rfl, totK_node, tot15364, tot15365]
  decide +kernel

theorem arows15360 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15360 = true := by
  rw [show D2M8K2.u15360 = KTree.node D2M8K2.t15366 (nat_lit 33423553) (nat_lit 1439792629) (nat_lit 0) D2M8K2.t15367 from rfl, allE_node, rows15366, irow15360, rows15367]
  all_goals rfl

theorem atot15360 : totK PD2M8K2 D2M8K2.u15360 = [0, 0, 348244260153, 877929499822, 518003630752, 77545960636, 1415142070, 0] := by
  rw [show D2M8K2.u15360 = KTree.node D2M8K2.t15366 (nat_lit 33423553) (nat_lit 1439792629) (nat_lit 0) D2M8K2.t15367 from rfl, totK_node, tot15366, tot15367]
  decide +kernel

theorem arows15363 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15363 = true := by
  rw [show D2M8K2.u15363 = KTree.node D2M8K2.t15368 (nat_lit 33425333) (nat_lit 2401304114) (nat_lit 0) D2M8K2.t15369 from rfl, allE_node, rows15368, irow15363, rows15369]
  all_goals rfl

theorem atot15363 : totK PD2M8K2 D2M8K2.u15363 = [0, 0, 71490399974, 623775833110, 895900329296, 207102668405, 2484078857, 0] := by
  rw [show D2M8K2.u15363 = KTree.node D2M8K2.t15368 (nat_lit 33425333) (nat_lit 2401304114) (nat_lit 0) D2M8K2.t15369 from rfl, totK_node, tot15368, tot15369]
  decide +kernel

theorem arows15364 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15364 = true := by
  rw [show D2M8K2.u15364 = KTree.node D2M8K2.t15370 (nat_lit 33427217) (nat_lit 2211143222) (nat_lit 0) D2M8K2.t15371 from rfl, allE_node, rows15370, irow15364, rows15371]
  all_goals rfl

theorem atot15364 : totK PD2M8K2 D2M8K2.u15364 = [0, 325398345861, 849015806543, 437524284705, 94951976216, 78620634454, 6818291842, 0] := by
  rw [show D2M8K2.u15364 = KTree.node D2M8K2.t15370 (nat_lit 33427217) (nat_lit 2211143222) (nat_lit 0) D2M8K2.t15371 from rfl, totK_node, tot15370, tot15371]
  decide +kernel

theorem arows15366 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15366 = true := by
  rw [show D2M8K2.u15366 = KTree.node D2M8K2.t15372 (nat_lit 33429686) (nat_lit 3137276930) (nat_lit 0) D2M8K2.t15373 from rfl, allE_node, rows15372, irow15366, rows15373]
  all_goals rfl

theorem atot15366 : totK PD2M8K2 D2M8K2.u15366 = [0, 183106467492, 731172494584, 786267699429, 135842659597, 1369150432, 0, 0] := by
  rw [show D2M8K2.u15366 = KTree.node D2M8K2.t15372 (nat_lit 33429686) (nat_lit 3137276930) (nat_lit 0) D2M8K2.t15373 from rfl, totK_node, tot15372, tot15373]
  decide +kernel

theorem arows15367 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15367 = true := by
  rw [show D2M8K2.u15367 = KTree.node D2M8K2.t15374 (nat_lit 33431344) (nat_lit 3283467353) (nat_lit 0) D2M8K2.t15375 from rfl, allE_node, rows15374, irow15367, rows15375]
  all_goals rfl

theorem atot15367 : totK PD2M8K2 D2M8K2.u15367 = [0, 245841870228, 761884837765, 612940578001, 171859951269, 17183021007, 0, 0] := by
  rw [show D2M8K2.u15367 = KTree.node D2M8K2.t15374 (nat_lit 33431344) (nat_lit 3283467353) (nat_lit 0) D2M8K2.t15375 from rfl, totK_node, tot15374, tot15375]
  decide +kernel

theorem arows15371 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15371 = true := by
  rw [show D2M8K2.u15371 = KTree.node D2M8K2.t15376 (nat_lit 33432819) (nat_lit 3650203772) (nat_lit 0) D2M8K2.t15377 from rfl, allE_node, rows15376, irow15371, rows15377]
  all_goals rfl

theorem atot15371 : totK PD2M8K2 D2M8K2.u15371 = [0, 67143456469, 432441922166, 866238510675, 408453238317, 20414095810, 0, 0] := by
  rw [show D2M8K2.u15371 = KTree.node D2M8K2.t15376 (nat_lit 33432819) (nat_lit 3650203772) (nat_lit 0) D2M8K2.t15377 from rfl, totK_node, tot15376, tot15377]
  decide +kernel

theorem arows15372 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15372 = true := by
  rw [show D2M8K2.u15372 = KTree.node D2M8K2.t15378 (nat_lit 33434050) (nat_lit 4122712912) (nat_lit 0) D2M8K2.t15379 from rfl, allE_node, rows15378, irow15372, rows15379]
  all_goals rfl

theorem atot15372 : totK PD2M8K2 D2M8K2.u15372 = [0, 367909695402, 947233567642, 480743898926, 35575636514, 0, 0, 0] := by
  rw [show D2M8K2.u15372 = KTree.node D2M8K2.t15378 (nat_lit 33434050) (nat_lit 4122712912) (nat_lit 0) D2M8K2.t15379 from rfl, totK_node, tot15378, tot15379]
  decide +kernel

theorem arows15374 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15374 = true := by
  rw [show D2M8K2.u15374 = KTree.node D2M8K2.t15380 (nat_lit 33435700) (nat_lit 4076853445) (nat_lit 0) D2M8K2.t15381 from rfl, allE_node, rows15380, irow15374, rows15381]
  all_goals rfl

theorem atot15374 : totK PD2M8K2 D2M8K2.u15374 = [0, 0, 490889792416, 985334886179, 293326116407, 13049727234, 0, 0] := by
  rw [show D2M8K2.u15374 = KTree.node D2M8K2.t15380 (nat_lit 33435700) (nat_lit 4076853445) (nat_lit 0) D2M8K2.t15381 from rfl, totK_node, tot15380, tot15381]
  decide +kernel

theorem arows15375 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15375 = true := by
  rw [show D2M8K2.u15375 = KTree.node D2M8K2.t15382 (nat_lit 33440866) (nat_lit 3733560802) (nat_lit 0) D2M8K2.t15383 from rfl, allE_node, rows15382, irow15375, rows15383]
  all_goals rfl

theorem atot15375 : totK PD2M8K2 D2M8K2.u15375 = [0, 382184329876, 921075170199, 477995788987, 44261269790, 0, 0, 0] := by
  rw [show D2M8K2.u15375 = KTree.node D2M8K2.t15382 (nat_lit 33440866) (nat_lit 3733560802) (nat_lit 0) D2M8K2.t15383 from rfl, totK_node, tot15382, tot15383]
  decide +kernel

theorem arows15378 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15378 = true := by
  rw [show D2M8K2.u15378 = KTree.node D2M8K2.t15384 (nat_lit 33442944) (nat_lit 2758395709) (nat_lit 0) D2M8K2.t15385 from rfl, allE_node, rows15384, irow15378, rows15385]
  all_goals rfl

theorem atot15378 : totK PD2M8K2 D2M8K2.u15378 = [0, 116789802826, 710771184967, 828322727295, 152647733885, 3884009855, 0, 0] := by
  rw [show D2M8K2.u15378 = KTree.node D2M8K2.t15384 (nat_lit 33442944) (nat_lit 2758395709) (nat_lit 0) D2M8K2.t15385 from rfl, totK_node, tot15384, tot15385]
  decide +kernel

theorem arows15379 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15379 = true := by
  rw [show D2M8K2.u15379 = KTree.node D2M8K2.t15386 (nat_lit 33444618) (nat_lit 3864864668) (nat_lit 0) D2M8K2.t15387 from rfl, allE_node, rows15386, irow15379, rows15387]
  all_goals rfl

theorem atot15379 : totK PD2M8K2 D2M8K2.u15379 = [0, 301794724658, 881162413018, 594159621700, 57921992778, 0, 0, 0] := by
  rw [show D2M8K2.u15379 = KTree.node D2M8K2.t15386 (nat_lit 33444618) (nat_lit 3864864668) (nat_lit 0) D2M8K2.t15387 from rfl, totK_node, tot15386, tot15387]
  decide +kernel

theorem arows15381 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15381 = true := by
  rw [show D2M8K2.u15381 = KTree.node D2M8K2.t15388 (nat_lit 33446337) (nat_lit 1337789783) (nat_lit 0) D2M8K2.t15389 from rfl, allE_node, rows15388, irow15381, rows15389]
  all_goals rfl

theorem atot15381 : totK PD2M8K2 D2M8K2.u15381 = [0, 0, 413614849043, 957617173364, 394301724771, 22007438460, 0, 0] := by
  rw [show D2M8K2.u15381 = KTree.node D2M8K2.t15388 (nat_lit 33446337) (nat_lit 1337789783) (nat_lit 0) D2M8K2.t15389 from rfl, totK_node, tot15388, tot15389]
  decide +kernel

theorem arows15382 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15382 = true := by
  rw [show D2M8K2.u15382 = KTree.node D2M8K2.t15390 (nat_lit 33448492) (nat_lit 3683531640) (nat_lit 0) D2M8K2.t15391 from rfl, allE_node, rows15390, irow15382, rows15391]
  all_goals rfl

theorem atot15382 : totK PD2M8K2 D2M8K2.u15382 = [0, 0, 261033028039, 840749478030, 574499089212, 75948169055, 1206465782, 0] := by
  rw [show D2M8K2.u15382 = KTree.node D2M8K2.t15390 (nat_lit 33448492) (nat_lit 3683531640) (nat_lit 0) D2M8K2.t15391 from rfl, totK_node, tot15390, tot15391]
  decide +kernel

theorem arows15387 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15387 = true := by
  rw [show D2M8K2.u15387 = KTree.node D2M8K2.t15392 (nat_lit 33451112) (nat_lit 3665586835) (nat_lit 0) D2M8K2.t15393 from rfl, allE_node, rows15392, irow15387, rows15393]
  all_goals rfl

theorem atot15387 : totK PD2M8K2 D2M8K2.u15387 = [0, 0, 255125971035, 854053057479, 651622775530, 68005133806, 0, 0] := by
  rw [show D2M8K2.u15387 = KTree.node D2M8K2.t15392 (nat_lit 33451112) (nat_lit 3665586835) (nat_lit 0) D2M8K2.t15393 from rfl, totK_node, tot15392, tot15393]
  decide +kernel

theorem arows15388 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15388 = true := by
  rw [show D2M8K2.u15388 = KTree.node D2M8K2.t15394 (nat_lit 33454084) (nat_lit 3807881487) (nat_lit 0) D2M8K2.t15395 from rfl, allE_node, rows15394, irow15388, rows15395]
  all_goals rfl

theorem atot15388 : totK PD2M8K2 D2M8K2.u15388 = [0, 0, 380205795376, 934015962965, 463432461677, 31411212558, 0, 0] := by
  rw [show D2M8K2.u15388 = KTree.node D2M8K2.t15394 (nat_lit 33454084) (nat_lit 3807881487) (nat_lit 0) D2M8K2.t15395 from rfl, totK_node, tot15394, tot15395]
  decide +kernel

theorem arows15390 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15390 = true := by
  rw [show D2M8K2.u15390 = KTree.node D2M8K2.t15396 (nat_lit 33455576) (nat_lit 3078950934) (nat_lit 0) D2M8K2.t15397 from rfl, allE_node, rows15396, irow15390, rows15397]
  all_goals rfl

theorem atot15390 : totK PD2M8K2 D2M8K2.u15390 = [0, 0, 229377893940, 810758551388, 640505288001, 94410484104, 1162935789, 0] := by
  rw [show D2M8K2.u15390 = KTree.node D2M8K2.t15396 (nat_lit 33455576) (nat_lit 3078950934) (nat_lit 0) D2M8K2.t15397 from rfl, totK_node, tot15396, tot15397]
  decide +kernel

theorem arows15391 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15391 = true := by
  rw [show D2M8K2.u15391 = KTree.node D2M8K2.t15398 (nat_lit 33457304) (nat_lit 2907010437) (nat_lit 0) D2M8K2.t15399 from rfl, allE_node, rows15398, irow15391, rows15399]
  all_goals rfl

theorem atot15391 : totK PD2M8K2 D2M8K2.u15391 = [0, 0, 186414463989, 672592321368, 711818539521, 190551077968, 8304610187, 0] := by
  rw [show D2M8K2.u15391 = KTree.node D2M8K2.t15398 (nat_lit 33457304) (nat_lit 2907010437) (nat_lit 0) D2M8K2.t15399 from rfl, totK_node, tot15398, tot15399]
  decide +kernel

theorem arows15394 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15394 = true := by
  rw [show D2M8K2.u15394 = KTree.node D2M8K2.t15400 (nat_lit 33462316) (nat_lit 3810070116) (nat_lit 0) D2M8K2.t15401 from rfl, allE_node, rows15400, irow15394, rows15401]
  all_goals rfl

theorem atot15394 : totK PD2M8K2 D2M8K2.u15394 = [0, 0, 194920179277, 863497879513, 672270042111, 53757026773, 0, 0] := by
  rw [show D2M8K2.u15394 = KTree.node D2M8K2.t15400 (nat_lit 33462316) (nat_lit 3810070116) (nat_lit 0) D2M8K2.t15401 from rfl, totK_node, tot15400, tot15401]
  decide +kernel

theorem arows15395 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15395 = true := by
  rw [show D2M8K2.u15395 = KTree.node D2M8K2.t15402 (nat_lit 33464915) (nat_lit 2744439150) (nat_lit 0) D2M8K2.t15403 from rfl, allE_node, rows15402, irow15395, rows15403]
  all_goals rfl

theorem atot15395 : totK PD2M8K2 D2M8K2.u15395 = [0, 0, 325441467313, 852098495107, 543198817425, 77884193470, 1330264907, 0] := by
  rw [show D2M8K2.u15395 = KTree.node D2M8K2.t15402 (nat_lit 33464915) (nat_lit 2744439150) (nat_lit 0) D2M8K2.t15403 from rfl, totK_node, tot15402, tot15403]
  decide +kernel

theorem arows15397 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15397 = true := by
  rw [show D2M8K2.u15397 = KTree.node D2M8K2.t15404 (nat_lit 33468169) (nat_lit 1508690721) (nat_lit 0) D2M8K2.t15405 from rfl, allE_node, rows15404, irow15397, rows15405]
  all_goals rfl

theorem atot15397 : totK PD2M8K2 D2M8K2.u15397 = [0, 288095139525, 766785442126, 548324165295, 187243785267, 16297041788, 0, 0] := by
  rw [show D2M8K2.u15397 = KTree.node D2M8K2.t15404 (nat_lit 33468169) (nat_lit 1508690721) (nat_lit 0) D2M8K2.t15405 from rfl, totK_node, tot15404, tot15405]
  decide +kernel

theorem arows15398 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15398 = true := by
  rw [show D2M8K2.u15398 = KTree.node D2M8K2.t15406 (nat_lit 33470622) (nat_lit 3939896210) (nat_lit 0) D2M8K2.t15407 from rfl, allE_node, rows15406, irow15398, rows15407]
  all_goals rfl

theorem atot15398 : totK PD2M8K2 D2M8K2.u15398 = [0, 131019798779, 702426080964, 847936305372, 145511726527, 1369150432, 0, 0] := by
  rw [show D2M8K2.u15398 = KTree.node D2M8K2.t15406 (nat_lit 33470622) (nat_lit 3939896210) (nat_lit 0) D2M8K2.t15407 from rfl, totK_node, tot15406, tot15407]
  decide +kernel

theorem arows15402 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15402 = true := by
  rw [show D2M8K2.u15402 = KTree.node D2M8K2.t15408 (nat_lit 33472547) (nat_lit 2340283138) (nat_lit 0) D2M8K2.t15409 from rfl, allE_node, rows15408, irow15402, rows15409]
  all_goals rfl

theorem atot15402 : totK PD2M8K2 D2M8K2.u15402 = [0, 335420412233, 911890751832, 530166664190, 47134099623, 0, 0, 0] := by
  rw [show D2M8K2.u15402 = KTree.node D2M8K2.t15408 (nat_lit 33472547) (nat_lit 2340283138) (nat_lit 0) D2M8K2.t15409 from rfl, totK_node, tot15408, tot15409]
  decide +kernel

theorem arows15403 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15403 = true := by
  rw [show D2M8K2.u15403 = KTree.node D2M8K2.t15410 (nat_lit 33474044) (nat_lit 3357507821) (nat_lit 0) D2M8K2.t15411 from rfl, allE_node, rows15410, irow15403, rows15411]
  all_goals rfl

theorem atot15403 : totK PD2M8K2 D2M8K2.u15403 = [0, 0, 389886688122, 940329694176, 446042146051, 30795354140, 0, 0] := by
  rw [show D2M8K2.u15403 = KTree.node D2M8K2.t15410 (nat_lit 33474044) (nat_lit 3357507821) (nat_lit 0) D2M8K2.t15411 from rfl, totK_node, tot15410, tot15411]
  decide +kernel

theorem arows15405 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15405 = true := by
  rw [show D2M8K2.u15405 = KTree.node D2M8K2.t15412 (nat_lit 33478773) (nat_lit 1101992512) (nat_lit 0) D2M8K2.t15413 from rfl, allE_node, rows15412, irow15405, rows15413]
  all_goals rfl

theorem atot15405 : totK PD2M8K2 D2M8K2.u15405 = [0, 350191493351, 839104783466, 503015085214, 123952823693, 6799735859, 0, 0] := by
  rw [show D2M8K2.u15405 = KTree.node D2M8K2.t15412 (nat_lit 33478773) (nat_lit 1101992512) (nat_lit 0) D2M8K2.t15413 from rfl, totK_node, tot15412, tot15413]
  decide +kernel

theorem arows15406 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15406 = true := by
  rw [show D2M8K2.u15406 = KTree.node D2M8K2.t15414 (nat_lit 33480248) (nat_lit 3743756101) (nat_lit 0) D2M8K2.t15415 from rfl, allE_node, rows15414, irow15406, rows15415]
  all_goals rfl

theorem atot15406 : totK PD2M8K2 D2M8K2.u15406 = [0, 88383717769, 612689104583, 857971958105, 228847677064, 9668735432, 0, 0] := by
  rw [show D2M8K2.u15406 = KTree.node D2M8K2.t15414 (nat_lit 33480248) (nat_lit 3743756101) (nat_lit 0) D2M8K2.t15415 from rfl, totK_node, tot15414, tot15415]
  decide +kernel

theorem arows15409 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15409 = true := by
  rw [show D2M8K2.u15409 = KTree.node D2M8K2.t15416 (nat_lit 33482112) (nat_lit 2737168113) (nat_lit 0) D2M8K2.t15417 from rfl, allE_node, rows15416, irow15409, rows15417]
  all_goals rfl

theorem atot15409 : totK PD2M8K2 D2M8K2.u15409 = [0, 293492712391, 798150557735, 599785971033, 117062299772, 3581949829, 0, 0] := by
  rw [show D2M8K2.u15409 = KTree.node D2M8K2.t15416 (nat_lit 33482112) (nat_lit 2737168113) (nat_lit 0) D2M8K2.t15417 from rfl, totK_node, tot15416, tot15417]
  decide +kernel

theorem arows15410 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15410 = true := by
  rw [show D2M8K2.u15410 = KTree.node D2M8K2.t15418 (nat_lit 33483847) (nat_lit 2334656709) (nat_lit 0) D2M8K2.t15419 from rfl, allE_node, rows15418, irow15410, rows15419]
  all_goals rfl

theorem atot15410 : totK PD2M8K2 D2M8K2.u15410 = [0, 113034805923, 688611898230, 839526735021, 158869876169, 3884009855, 0, 0] := by
  rw [show D2M8K2.u15410 = KTree.node D2M8K2.t15418 (nat_lit 33483847) (nat_lit 2334656709) (nat_lit 0) D2M8K2.t15419 from rfl, totK_node, tot15418, tot15419]
  decide +kernel

theorem arows15412 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15412 = true := by
  rw [show D2M8K2.u15412 = KTree.node D2M8K2.t15420 (nat_lit 33485818) (nat_lit 3969426450) (nat_lit 0) D2M8K2.t15421 from rfl, allE_node, rows15420, irow15412, rows15421]
  all_goals rfl

theorem atot15412 : totK PD2M8K2 D2M8K2.u15412 = [0, 394405686972, 947076777915, 469912854647, 37523219145, 0, 0, 0] := by
  rw [show D2M8K2.u15412 = KTree.node D2M8K2.t15420 (nat_lit 33485818) (nat_lit 3969426450) (nat_lit 0) D2M8K2.t15421 from rfl, totK_node, tot15420, tot15421]
  decide +kernel

theorem arows15413 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15413 = true := by
  rw [show D2M8K2.u15413 = KTree.node D2M8K2.t15422 (nat_lit 33487526) (nat_lit 4097039310) (nat_lit 0) D2M8K2.t15423 from rfl, allE_node, rows15422, irow15413, rows15423]
  all_goals rfl

theorem atot15413 : totK PD2M8K2 D2M8K2.u15413 = [0, 0, 514994139098, 978850670666, 292394113548, 8684770685, 0, 0] := by
  rw [show D2M8K2.u15413 = KTree.node D2M8K2.t15422 (nat_lit 33487526) (nat_lit 4097039310) (nat_lit 0) D2M8K2.t15423 from rfl, totK_node, tot15422, tot15423]
  decide +kernel

theorem arows15419 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15419 = true := by
  rw [show D2M8K2.u15419 = KTree.node D2M8K2.t15424 (nat_lit 33489661) (nat_lit 1186107345) (nat_lit 0) D2M8K2.t15425 from rfl, allE_node, rows15424, irow15419, rows15425]
  all_goals rfl

theorem atot15419 : totK PD2M8K2 D2M8K2.u15419 = [0, 0, 324541162239, 929416664168, 492526046687, 33699587675, 0, 0] := by
  rw [show D2M8K2.u15419 = KTree.node D2M8K2.t15424 (nat_lit 33489661) (nat_lit 1186107345) (nat_lit 0) D2M8K2.t15425 from rfl, totK_node, tot15424, tot15425]
  decide +kernel

theorem arows15420 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15420 = true := by
  rw [show D2M8K2.u15420 = KTree.node D2M8K2.t15426 (nat_lit 33491893) (nat_lit 1147420247) (nat_lit 0) D2M8K2.t15427 from rfl, allE_node, rows15426, irow15420, rows15427]
  all_goals rfl

theorem atot15420 : totK PD2M8K2 D2M8K2.u15420 = [0, 0, 165745244471, 729022847686, 773367698210, 119642373983, 1239866073, 0] := by
  rw [show D2M8K2.u15420 = KTree.node D2M8K2.t15426 (nat_lit 33491893) (nat_lit 1147420247) (nat_lit 0) D2M8K2.t15427 from rfl, totK_node, tot15426, tot15427]
  decide +kernel

theorem arows15422 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15422 = true := by
  rw [show D2M8K2.u15422 = KTree.node D2M8K2.t15428 (nat_lit 33493569) (nat_lit 1383489077) (nat_lit 0) D2M8K2.t15429 from rfl, allE_node, rows15428, irow15422, rows15429]
  all_goals rfl

theorem atot15422 : totK PD2M8K2 D2M8K2.u15422 = [0, 0, 396406285735, 956753650022, 437309358705, 23732092148, 0, 0] := by
  rw [show D2M8K2.u15422 = KTree.node D2M8K2.t15428 (nat_lit 33493569) (nat_lit 1383489077) (nat_lit 0) D2M8K2.t15429 from rfl, totK_node, tot15428, tot15429]
  decide +kernel

theorem arows15423 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15423 = true := by
  rw [show D2M8K2.u15423 = KTree.node D2M8K2.t15430 (nat_lit 33500206) (nat_lit 3302555625) (nat_lit 0) D2M8K2.t15431 from rfl, allE_node, rows15430, irow15423, rows15431]
  all_goals rfl

theorem atot15423 : totK PD2M8K2 D2M8K2.u15423 = [0, 0, 302459512420, 887573447495, 565563196783, 49541844120, 0, 0] := by
  rw [show D2M8K2.u15423 = KTree.node D2M8K2.t15430 (nat_lit 33500206) (nat_lit 3302555625) (nat_lit 0) D2M8K2.t15431 from rfl, totK_node, tot15430, tot15431]
  decide +kernel

theorem arows15426 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15426 = true := by
  rw [show D2M8K2.u15426 = KTree.node D2M8K2.t15432 (nat_lit 33501904) (nat_lit 1857463927) (nat_lit 0) D2M8K2.t15433 from rfl, allE_node, rows15432, irow15426, rows15433]
  all_goals rfl

theorem atot15426 : totK PD2M8K2 D2M8K2.u15426 = [0, 0, 88972803789, 567849059107, 837445499424, 249325862238, 9527367360, 0] := by
  rw [show D2M8K2.u15426 = KTree.node D2M8K2.t15432 (nat_lit 33501904) (nat_lit 1857463927) (nat_lit 0) D2M8K2.t15433 from rfl, totK_node, tot15432, tot15433]
  decide +kernel

theorem arows15427 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15427 = true := by
  rw [show D2M8K2.u15427 = KTree.node D2M8K2.t15434 (nat_lit 33503498) (nat_lit 4185316874) (nat_lit 0) D2M8K2.t15435 from rfl, allE_node, rows15434, irow15427, rows15435]
  all_goals rfl

theorem atot15427 : totK PD2M8K2 D2M8K2.u15427 = [0, 0, 288528760568, 911528330145, 572460108892, 38682638324, 0, 0] := by
  rw [show D2M8K2.u15427 = KTree.node D2M8K2.t15434 (nat_lit 33503498) (nat_lit 4185316874) (nat_lit 0) D2M8K2.t15435 from rfl, totK_node, tot15434, tot15435]
  decide +kernel

theorem arows15429 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15429 = true := by
  rw [show D2M8K2.u15429 = KTree.node D2M8K2.t15436 (nat_lit 33506041) (nat_lit 1524685871) (nat_lit 0) D2M8K2.t15437 from rfl, allE_node, rows15436, irow15429, rows15437]
  all_goals rfl

theorem atot15429 : totK PD2M8K2 D2M8K2.u15429 = [0, 0, 236579903147, 781991259465, 663792910992, 100268456682, 1376099875, 0] := by
  rw [show D2M8K2.u15429 = KTree.node D2M8K2.t15436 (nat_lit 33506041) (nat_lit 1524685871) (nat_lit 0) D2M8K2.t15437 from rfl, totK_node, tot15436, tot15437]
  decide +kernel

theorem arows15430 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15430 = true := by
  rw [show D2M8K2.u15430 = KTree.node D2M8K2.t15438 (nat_lit 33507565) (nat_lit 1010094740) (nat_lit 0) D2M8K2.t15439 from rfl, allE_node, rows15438, irow15430, rows15439]
  all_goals rfl

theorem atot15430 : totK PD2M8K2 D2M8K2.u15430 = [0, 180280610855, 572370888774, 733223684213, 330939332304, 24588525227, 0, 0] := by
  rw [show D2M8K2.u15430 = KTree.node D2M8K2.t15438 (nat_lit 33507565) (nat_lit 1010094740) (nat_lit 0) D2M8K2.t15439 from rfl, totK_node, tot15438, tot15439]
  decide +kernel

theorem arows15434 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15434 = true := by
  rw [show D2M8K2.u15434 = KTree.node D2M8K2.t15440 (nat_lit 33514181) (nat_lit 2345058749) (nat_lit 0) D2M8K2.t15441 from rfl, allE_node, rows15440, irow15434, rows15441]
  all_goals rfl

theorem atot15434 : totK PD2M8K2 D2M8K2.u15434 = [0, 248847232727, 801919471838, 619299161234, 144979299077, 15863492353, 0, 0] := by
  rw [show D2M8K2.u15434 = KTree.node D2M8K2.t15440 (nat_lit 33514181) (nat_lit 2345058749) (nat_lit 0) D2M8K2.t15441 from rfl, totK_node, tot15440, tot15441]
  decide +kernel

theorem arows15435 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15435 = true := by
  rw [show D2M8K2.u15435 = KTree.node D2M8K2.t15442 (nat_lit 33515713) (nat_lit 1300548769) (nat_lit 0) D2M8K2.t15443 from rfl, allE_node, rows15442, irow15435, rows15443]
  all_goals rfl

theorem atot15435 : totK PD2M8K2 D2M8K2.u15435 = [0, 53143458605, 409726139569, 879340880122, 432526627600, 21738215869, 0, 0] := by
  rw [show D2M8K2.u15435 = KTree.node D2M8K2.t15442 (nat_lit 33515713) (nat_lit 1300548769) (nat_lit 0) D2M8K2.t15443 from rfl, totK_node, tot15442, tot15443]
  decide +kernel

theorem arows15437 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15437 = true := by
  rw [show D2M8K2.u15437 = KTree.node D2M8K2.t15444 (nat_lit 33517006) (nat_lit 3951767169) (nat_lit 0) D2M8K2.t15445 from rfl, allE_node, rows15444, irow15437, rows15445]
  all_goals rfl

theorem atot15437 : totK PD2M8K2 D2M8K2.u15437 = [0, 349027306593, 930729212084, 500949918344, 36880085567, 0, 0, 0] := by
  rw [show D2M8K2.u15437 = KTree.node D2M8K2.t15444 (nat_lit 33517006) (nat_lit 3951767169) (nat_lit 0) D2M8K2.t15445 from rfl, totK_node, tot15444, tot15445]
  decide +kernel

theorem arows15438 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15438 = true := by
  rw [show D2M8K2.u15438 = KTree.node D2M8K2.t15446 (nat_lit 33518846) (nat_lit 2310122502) (nat_lit 0) D2M8K2.t15447 from rfl, allE_node, rows15446, irow15438, rows15447]
  all_goals rfl

theorem atot15438 : totK PD2M8K2 D2M8K2.u15438 = [0, 67163829148, 577611909414, 882455090831, 245751660843, 11885407614, 0, 0] := by
  rw [show D2M8K2.u15438 = KTree.node D2M8K2.t15446 (nat_lit 33518846) (nat_lit 2310122502) (nat_lit 0) D2M8K2.t15447 from rfl, totK_node, tot15446, tot15447]
  decide +kernel

theorem arows15441 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15441 = true := by
  rw [show D2M8K2.u15441 = KTree.node D2M8K2.t15448 (nat_lit 33520856) (nat_lit 3875688189) (nat_lit 0) D2M8K2.t15449 from rfl, allE_node, rows15448, irow15441, rows15449]
  all_goals rfl

theorem atot15441 : totK PD2M8K2 D2M8K2.u15441 = [0, 335251487571, 908378974001, 537328777198, 46358515403, 0, 0, 0] := by
  rw [show D2M8K2.u15441 = KTree.node D2M8K2.t15448 (nat_lit 33520856) (nat_lit 3875688189) (nat_lit 0) D2M8K2.t15449 from rfl, totK_node, tot15448, tot15449]
  decide +kernel

theorem arows15442 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15442 = true := by
  rw [show D2M8K2.u15442 = KTree.node D2M8K2.t15450 (nat_lit 33522675) (nat_lit 2548450691) (nat_lit 0) D2M8K2.t15451 from rfl, allE_node, rows15450, irow15442, rows15451]
  all_goals rfl

theorem atot15442 : totK PD2M8K2 D2M8K2.u15442 = [0, 108818674509, 599917273828, 825525615137, 244399663383, 12052611869, 0, 0] := by
  rw [show D2M8K2.u15442 = KTree.node D2M8K2.t15450 (nat_lit 33522675) (nat_lit 2548450691) (nat_lit 0) D2M8K2.t15451 from rfl, totK_node, tot15450, tot15451]
  decide +kernel

theorem arows15444 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15444 = true := by
  rw [show D2M8K2.u15444 = KTree.node D2M8K2.t15452 (nat_lit 33524106) (nat_lit 3891784201) (nat_lit 0) D2M8K2.t15453 from rfl, allE_node, rows15452, irow15444, rows15453]
  all_goals rfl

theorem atot15444 : totK PD2M8K2 D2M8K2.u15444 = [0, 315751930257, 901418375753, 547624312869, 49065522397, 0, 0, 0] := by
  rw [show D2M8K2.u15444 = KTree.node D2M8K2.t15452 (nat_lit 33524106) (nat_lit 3891784201) (nat_lit 0) D2M8K2.t15453 from rfl, totK_node, tot15452, tot15453]
  decide +kernel

theorem arows15445 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15445 = true := by
  rw [show D2M8K2.u15445 = KTree.node D2M8K2.t15454 (nat_lit 33526142) (nat_lit 3661376432) (nat_lit 0) D2M8K2.t15455 from rfl, allE_node, rows15454, irow15445, rows15455]
  all_goals rfl

theorem atot15445 : totK PD2M8K2 D2M8K2.u15445 = [0, 0, 513618432197, 973860931139, 332929456743, 25815485168, 0, 0] := by
  rw [show D2M8K2.u15445 = KTree.node D2M8K2.t15454 (nat_lit 33526142) (nat_lit 3661376432) (nat_lit 0) D2M8K2.t15455 from rfl, totK_node, tot15454, tot15455]
  decide +kernel

theorem arows15450 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15450 = true := by
  rw [show D2M8K2.u15450 = KTree.node D2M8K2.t15456 (nat_lit 33534812) (nat_lit 3402165178) (nat_lit 0) D2M8K2.t15457 from rfl, allE_node, rows15456, irow15450, rows15457]
  all_goals rfl

theorem atot15450 : totK PD2M8K2 D2M8K2.u15450 = [0, 0, 354944512208, 964934553717, 449100842500, 24558987319, 0, 0] := by
  rw [show D2M8K2.u15450 = KTree.node D2M8K2.t15456 (nat_lit 33534812) (nat_lit 3402165178) (nat_lit 0) D2M8K2.t15457 from rfl, totK_node, tot15456, tot15457]
  decide +kernel

theorem arows15451 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15451 = true := by
  rw [show D2M8K2.u15451 = KTree.node D2M8K2.t15458 (nat_lit 33538183) (nat_lit 2019126302) (nat_lit 0) D2M8K2.t15459 from rfl, allE_node, rows15458, irow15451, rows15459]
  all_goals rfl

theorem atot15451 : totK PD2M8K2 D2M8K2.u15451 = [0, 0, 393557702985, 945232025248, 441300364493, 25877670872, 0, 0] := by
  rw [show D2M8K2.u15451 = KTree.node D2M8K2.t15458 (nat_lit 33538183) (nat_lit 2019126302) (nat_lit 0) D2M8K2.t15459 from rfl, totK_node, tot15458, tot15459]
  decide +kernel

theorem arows15453 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15453 = true := by
  rw [show D2M8K2.u15453 = KTree.node D2M8K2.t15460 (nat_lit 33541560) (nat_lit 3424934041) (nat_lit 0) D2M8K2.t15461 from rfl, allE_node, rows15460, irow15453, rows15461]
  all_goals rfl

theorem atot15453 : totK PD2M8K2 D2M8K2.u15453 = [0, 0, 352719212085, 944633584540, 484884716624, 27281941653, 0, 0] := by
  rw [show D2M8K2.u15453 = KTree.node D2M8K2.t15460 (nat_lit 33541560) (nat_lit 3424934041) (nat_lit 0) D2M8K2.t15461 from rfl, totK_node, tot15460, tot15461]
  decide +kernel

theorem arows15454 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15454 = true := by
  rw [show D2M8K2.u15454 = KTree.node D2M8K2.t15462 (nat_lit 33544580) (nat_lit 3378615208) (nat_lit 0) D2M8K2.t15463 from rfl, allE_node, rows15462, irow15454, rows15463]
  all_goals rfl

theorem atot15454 : totK PD2M8K2 D2M8K2.u15454 = [0, 0, 383389190615, 924669448381, 442802597573, 32547243808, 0, 0] := by
  rw [show D2M8K2.u15454 = KTree.node D2M8K2.t15462 (nat_lit 33544580) (nat_lit 3378615208) (nat_lit 0) D2M8K2.t15463 from rfl, totK_node, tot15462, tot15463]
  decide +kernel

theorem arows15457 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15457 = true := by
  rw [show D2M8K2.u15457 = KTree.node D2M8K2.t15464 (nat_lit 33546550) (nat_lit 1624539036) (nat_lit 0) D2M8K2.t15465 from rfl, allE_node, rows15464, irow15457, rows15465]
  all_goals rfl

theorem atot15457 : totK PD2M8K2 D2M8K2.u15457 = [0, 87029534603, 206903025318, 608923342364, 735720786890, 129904674023, 1493059870, 0] := by
  rw [show D2M8K2.u15457 = KTree.node D2M8K2.t15464 (nat_lit 33546550) (nat_lit 1624539036) (nat_lit 0) D2M8K2.t15465 from rfl, totK_node, tot15464, tot15465]
  decide +kernel

theorem arows15458 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15458 = true := by
  rw [show D2M8K2.u15458 = KTree.node D2M8K2.t15466 (nat_lit 33552298) (nat_lit 4010135701) (nat_lit 0) D2M8K2.t15467 from rfl, allE_node, rows15466, irow15458, rows15467]
  all_goals rfl

theorem atot15458 : totK PD2M8K2 D2M8K2.u15458 = [0, 255805811740, 811466174247, 642074314900, 99989436140, 1369150432, 0, 0] := by
  rw [show D2M8K2.u15458 = KTree.node D2M8K2.t15466 (nat_lit 33552298) (nat_lit 4010135701) (nat_lit 0) D2M8K2.t15467 from rfl, totK_node, tot15466, tot15467]
  decide +kernel

theorem arows15460 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15460 = true := by
  rw [show D2M8K2.u15460 = KTree.node D2M8K2.t15468 (nat_lit 33554783) (nat_lit 2034847228) (nat_lit 0) D2M8K2.t15469 from rfl, allE_node, rows15468, irow15460, rows15469]
  all_goals rfl

theorem atot15460 : totK PD2M8K2 D2M8K2.u15460 = [0, 268379818248, 836108713687, 670372271449, 75826152743, 0, 0, 0] := by
  rw [show D2M8K2.u15460 = KTree.node D2M8K2.t15468 (nat_lit 33554783) (nat_lit 2034847228) (nat_lit 0) D2M8K2.t15469 from rfl, totK_node, tot15468, tot15469]
  decide +kernel

theorem arows15461 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15461 = true := by
  rw [show D2M8K2.u15461 = KTree.node D2M8K2.t15470 (nat_lit 33555980) (nat_lit 1411339525) (nat_lit 0) D2M8K2.t15471 from rfl, allE_node, rows15470, irow15461, rows15471]
  all_goals rfl

theorem atot15461 : totK PD2M8K2 D2M8K2.u15461 = [0, 162484517857, 672256276104, 721105207651, 250642488797, 24250117784, 0, 0] := by
  rw [show D2M8K2.u15461 = KTree.node D2M8K2.t15470 (nat_lit 33555980) (nat_lit 1411339525) (nat_lit 0) D2M8K2.t15471 from rfl, totK_node, tot15470, tot15471]
  decide +kernel

theorem arows15465 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15465 = true := by
  rw [show D2M8K2.u15465 = KTree.node D2M8K2.t15472 (nat_lit 33557517) (nat_lit 1286439862) (nat_lit 0) D2M8K2.t15473 from rfl, allE_node, rows15472, irow15465, rows15473]
  all_goals rfl

theorem atot15465 : totK PD2M8K2 D2M8K2.u15465 = [0, 151336384243, 562020115807, 759498428505, 321703405286, 13339329006, 0, 0] := by
  rw [show D2M8K2.u15465 = KTree.node D2M8K2.t15472 (nat_lit 33557517) (nat_lit 1286439862) (nat_lit 0) D2M8K2.t15473 from rfl, totK_node, tot15472, tot15473]
  decide +kernel

theorem arows15466 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15466 = true := by
  rw [show D2M8K2.u15466 = KTree.node D2M8K2.t15474 (nat_lit 33559015) (nat_lit 1623425402) (nat_lit 0) D2M8K2.t15475 from rfl, allE_node, rows15474, irow15466, rows15475]
  all_goals rfl

theorem atot15466 : totK PD2M8K2 D2M8K2.u15466 = [0, 259413372703, 829438841772, 635520799853, 86974684789, 1164319620, 0, 0] := by
  rw [show D2M8K2.u15466 = KTree.node D2M8K2.t15474 (nat_lit 33559015) (nat_lit 1623425402) (nat_lit 0) D2M8K2.t15475 from rfl, totK_node, tot15474, tot15475]
  decide +kernel

theorem arows15468 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15468 = true := by
  rw [show D2M8K2.u15468 = KTree.node D2M8K2.t15476 (nat_lit 33560745) (nat_lit 1913384843) (nat_lit 0) D2M8K2.t15477 from rfl, allE_node, rows15476, irow15468, rows15477]
  all_goals rfl

theorem atot15468 : totK PD2M8K2 D2M8K2.u15468 = [0, 133759602454, 620824972469, 807456597869, 234165771756, 10463569636, 0, 0] := by
  rw [show D2M8K2.u15468 = KTree.node D2M8K2.t15476 (nat_lit 33560745) (nat_lit 1913384843) (nat_lit 0) D2M8K2.t15477 from rfl, totK_node, tot15476, tot15477]
  decide +kernel

theorem arows15469 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15469 = true := by
  rw [show D2M8K2.u15469 = KTree.node D2M8K2.t15478 (nat_lit 33562450) (nat_lit 3324910113) (nat_lit 0) D2M8K2.t15479 from rfl, allE_node, rows15478, irow15469, rows15479]
  all_goals rfl

theorem atot15469 : totK PD2M8K2 D2M8K2.u15469 = [0, 277283714901, 857516964037, 619670107757, 66452421872, 0, 0, 0] := by
  rw [show D2M8K2.u15469 = KTree.node D2M8K2.t15478 (nat_lit 33562450) (nat_lit 3324910113) (nat_lit 0) D2M8K2.t15479 from rfl, totK_node, tot15478, tot15479]
  decide +kernel

theorem arows15472 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15472 = true := by
  rw [show D2M8K2.u15472 = KTree.node D2M8K2.t15480 (nat_lit 33564176) (nat_lit 3796090795) (nat_lit 0) D2M8K2.t15481 from rfl, allE_node, rows15480, irow15472, rows15481]
  all_goals rfl

theorem atot15472 : totK PD2M8K2 D2M8K2.u15472 = [0, 114253190048, 586316947561, 823920943665, 266519901576, 11782027357, 0, 0] := by
  rw [show D2M8K2.u15472 = KTree.node D2M8K2.t15480 (nat_lit 33564176) (nat_lit 3796090795) (nat_lit 0) D2M8K2.t15481 from rfl, totK_node, tot15480, tot15481]
  decide +kernel

theorem arows15473 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15473 = true := by
  rw [show D2M8K2.u15473 = KTree.node D2M8K2.t15482 (nat_lit 33569021) (nat_lit 1692369183) (nat_lit 0) D2M8K2.t15483 from rfl, allE_node, rows15482, irow15473, rows15483]
  all_goals rfl

theorem atot15473 : totK PD2M8K2 D2M8K2.u15473 = [0, 325757324431, 904633479162, 559298285845, 53294154088, 0, 0, 0] := by
  rw [show D2M8K2.u15473 = KTree.node D2M8K2.t15482 (nat_lit 33569021) (nat_lit 1692369183) (nat_lit 0) D2M8K2.t15483 from rfl, totK_node, tot15482, tot15483]
  decide +kernel

theorem arows15475 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15475 = true := by
  rw [show D2M8K2.u15475 = KTree.node D2M8K2.t15484 (nat_lit 33570632) (nat_lit 3215965077) (nat_lit 0) D2M8K2.t15485 from rfl, allE_node, rows15484, irow15475, rows15485]
  all_goals rfl

theorem atot15475 : totK PD2M8K2 D2M8K2.u15475 = [0, 0, 422302503441, 973196929830, 370592883982, 14971720341, 0, 0] := by
  rw [show D2M8K2.u15475 = KTree.node D2M8K2.t15484 (nat_lit 33570632) (nat_lit 3215965077) (nat_lit 0) D2M8K2.t15485 from rfl, totK_node, tot15484, tot15485]
  decide +kernel

theorem arows15476 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15476 = true := by
  rw [show D2M8K2.u15476 = KTree.node D2M8K2.t15486 (nat_lit 33572482) (nat_lit 3879837356) (nat_lit 0) D2M8K2.t15487 from rfl, allE_node, rows15486, irow15476, rows15487]
  all_goals rfl

theorem atot15476 : totK PD2M8K2 D2M8K2.u15476 = [0, 0, 341236473953, 936919046981, 495815783271, 34122722863, 0, 0] := by
  rw [show D2M8K2.u15476 = KTree.node D2M8K2.t15486 (nat_lit 33572482) (nat_lit 3879837356) (nat_lit 0) D2M8K2.t15487 from rfl, totK_node, tot15486, tot15487]
  decide +kernel

theorem arows15483 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15483 = true := by
  rw [show D2M8K2.u15483 = KTree.node D2M8K2.t15488 (nat_lit 33574883) (nat_lit 2984645793) (nat_lit 0) D2M8K2.t15489 from rfl, allE_node, rows15488, irow15483, rows15489]
  all_goals rfl

theorem atot15483 : totK PD2M8K2 D2M8K2.u15483 = [0, 0, 180298466249, 725339372203, 782691816601, 125637092307, 1310285577, 0] := by
  rw [show D2M8K2.u15483 = KTree.node D2M8K2.t15488 (nat_lit 33574883) (nat_lit 2984645793) (nat_lit 0) D2M8K2.t15489 from rfl, totK_node, tot15488, tot15489]
  decide +kernel

theorem arows15484 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15484 = true := by
  rw [show D2M8K2.u15484 = KTree.node D2M8K2.t15490 (nat_lit 33576525) (nat_lit 1305506934) (nat_lit 0) D2M8K2.t15491 from rfl, allE_node, rows15490, irow15484, rows15491]
  all_goals rfl

theorem atot15484 : totK PD2M8K2 D2M8K2.u15484 = [0, 0, 392912795961, 956603806968, 450156126860, 24028099160, 0, 0] := by
  rw [show D2M8K2.u15484 = KTree.node D2M8K2.t15490 (nat_lit 33576525) (nat_lit 1305506934) (nat_lit 0) D2M8K2.t15491 from rfl, totK_node, tot15490, tot15491]
  decide +kernel

theorem arows15486 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15486 = true := by
  rw [show D2M8K2.u15486 = KTree.node D2M8K2.t15492 (nat_lit 33579745) (nat_lit 1194772036) (nat_lit 0) D2M8K2.t15493 from rfl, allE_node, rows15492, irow15486, rows15493]
  all_goals rfl

theorem atot15486 : totK PD2M8K2 D2M8K2.u15486 = [0, 0, 265630360363, 841191532442, 607937470366, 75998513030, 1075657031, 0] := by
  rw [show D2M8K2.u15486 = KTree.node D2M8K2.t15492 (nat_lit 33579745) (nat_lit 1194772036) (nat_lit 0) D2M8K2.t15493 from rfl, totK_node, tot15492, tot15493]
  decide +kernel

theorem arows15487 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15487 = true := by
  rw [show D2M8K2.u15487 = KTree.node D2M8K2.t15494 (nat_lit 33581710) (nat_lit 3897172827) (nat_lit 0) D2M8K2.t15495 from rfl, allE_node, rows15494, irow15487, rows15495]
  all_goals rfl

theorem atot15487 : totK PD2M8K2 D2M8K2.u15487 = [0, 0, 166659160540, 723646163148, 750667016912, 145555045732, 3804183361, 0] := by
  rw [show D2M8K2.u15487 = KTree.node D2M8K2.t15494 (nat_lit 33581710) (nat_lit 3897172827) (nat_lit 0) D2M8K2.t15495 from rfl, totK_node, tot15494, tot15495]
  decide +kernel

theorem arows15490 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15490 = true := by
  rw [show D2M8K2.u15490 = KTree.node D2M8K2.t15496 (nat_lit 33583420) (nat_lit 3644773608) (nat_lit 0) D2M8K2.t15497 from rfl, allE_node, rows15496, irow15490, rows15497]
  all_goals rfl

theorem atot15490 : totK PD2M8K2 D2M8K2.u15490 = [0, 0, 247127981793, 815411411816, 644764227038, 86021950726, 1107157161, 0] := by
  rw [show D2M8K2.u15490 = KTree.node D2M8K2.t15496 (nat_lit 33583420) (nat_lit 3644773608) (nat_lit 0) D2M8K2.t15497 from rfl, totK_node, tot15496, tot15497]
  decide +kernel

theorem arows15491 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15491 = true := by
  rw [show D2M8K2.u15491 = KTree.node D2M8K2.t15498 (nat_lit 33588937) (nat_lit 1512170416) (nat_lit 0) D2M8K2.t15499 from rfl, allE_node, rows15498, irow15491, rows15499]
  all_goals rfl

theorem atot15491 : totK PD2M8K2 D2M8K2.u15491 = [0, 0, 228107796941, 759122350426, 677734339959, 128576482179, 3824247485, 0] := by
  rw [show D2M8K2.u15491 = KTree.node D2M8K2.t15498 (nat_lit 33588937) (nat_lit 1512170416) (nat_lit 0) D2M8K2.t15499 from rfl, totK_node, tot15498, tot15499]
  decide +kernel

theorem arows15493 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15493 = true := by
  rw [show D2M8K2.u15493 = KTree.node D2M8K2.t15500 (nat_lit 33590394) (nat_lit 3909650542) (nat_lit 0) D2M8K2.t15501 from rfl, allE_node, rows15500, irow15493, rows15501]
  all_goals rfl

theorem atot15493 : totK PD2M8K2 D2M8K2.u15493 = [0, 0, 213783618280, 792609541202, 687701793291, 109088031875, 1242138600, 0] := by
  rw [show D2M8K2.u15493 = KTree.node D2M8K2.t15500 (nat_lit 33590394) (nat_lit 3909650542) (nat_lit 0) D2M8K2.t15501 from rfl, totK_node, tot15500, tot15501]
  decide +kernel

theorem arows15494 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15494 = true := by
  rw [show D2M8K2.u15494 = KTree.node D2M8K2.t15502 (nat_lit 33592104) (nat_lit 3470308022) (nat_lit 0) D2M8K2.t15503 from rfl, allE_node, rows15502, irow15494, rows15503]
  all_goals rfl

theorem atot15494 : totK PD2M8K2 D2M8K2.u15494 = [0, 161564142879, 328561995991, 346620240081, 622835110286, 284195461930, 20509029466, 0] := by
  rw [show D2M8K2.u15494 = KTree.node D2M8K2.t15502 (nat_lit 33592104) (nat_lit 3470308022) (nat_lit 0) D2M8K2.t15503 from rfl, totK_node, tot15502, tot15503]
  decide +kernel

theorem arows15498 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15498 = true := by
  rw [show D2M8K2.u15498 = KTree.node D2M8K2.t15504 (nat_lit 33842414) (nat_lit 3527745614) (nat_lit 0) D2M8K2.t15505 from rfl, allE_node, rows15504, irow15498, rows15505]
  all_goals rfl

theorem atot15498 : totK PD2M8K2 D2M8K2.u15498 = [0, 271701467535, 861592534927, 588782968919, 56951035035, 0, 0, 0] := by
  rw [show D2M8K2.u15498 = KTree.node D2M8K2.t15504 (nat_lit 33842414) (nat_lit 3527745614) (nat_lit 0) D2M8K2.t15505 from rfl, totK_node, tot15504, tot15505]
  decide +kernel

theorem arows15499 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15499 = true := by
  rw [show D2M8K2.u15499 = KTree.node D2M8K2.t15506 (nat_lit 33844363) (nat_lit 1185948232) (nat_lit 0) D2M8K2.t15507 from rfl, allE_node, rows15506, irow15499, rows15507]
  all_goals rfl

theorem atot15499 : totK PD2M8K2 D2M8K2.u15499 = [0, 160124191442, 729594047282, 793076570851, 131634554098, 1369150432, 0, 0] := by
  rw [show D2M8K2.u15499 = KTree.node D2M8K2.t15506 (nat_lit 33844363) (nat_lit 1185948232) (nat_lit 0) D2M8K2.t15507 from rfl, totK_node, tot15506, tot15507]
  decide +kernel

theorem arows15501 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15501 = true := by
  rw [show D2M8K2.u15501 = KTree.node D2M8K2.t15508 (nat_lit 33849470) (nat_lit 2954202364) (nat_lit 0) D2M8K2.t15509 from rfl, allE_node, rows15508, irow15501, rows15509]
  all_goals rfl

theorem atot15501 : totK PD2M8K2 D2M8K2.u15501 = [0, 263144751689, 798626387945, 625591323656, 101908687357, 1164319620, 0, 0] := by
  rw [show D2M8K2.u15501 = KTree.node D2M8K2.t15508 (nat_lit 33849470) (nat_lit 2954202364) (nat_lit 0) D2M8K2.t15509 from rfl, totK_node, tot15508, tot15509]
  decide +kernel

theorem arows15502 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15502 = true := by
  rw [show D2M8K2.u15502 = KTree.node D2M8K2.t15510 (nat_lit 33851144) (nat_lit 3643950755) (nat_lit 0) D2M8K2.t15511 from rfl, allE_node, rows15510, irow15502, rows15511]
  all_goals rfl

theorem atot15502 : totK PD2M8K2 D2M8K2.u15502 = [0, 158739087997, 638831404195, 750697238021, 219856781747, 11885407614, 0, 0] := by
  rw [show D2M8K2.u15502 = KTree.node D2M8K2.t15510 (nat_lit 33851144) (nat_lit 3643950755) (nat_lit 0) D2M8K2.t15511 from rfl, totK_node, tot15510, tot15511]
  decide +kernel

theorem arows15505 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15505 = true := by
  rw [show D2M8K2.u15505 = KTree.node D2M8K2.t15512 (nat_lit 33853194) (nat_lit 3566339142) (nat_lit 0) D2M8K2.t15513 from rfl, allE_node, rows15512, irow15505, rows15513]
  all_goals rfl

theorem atot15505 : totK PD2M8K2 D2M8K2.u15505 = [0, 162691190537, 702956985217, 738871391166, 172200959832, 5455647540, 0, 0] := by
  rw [show D2M8K2.u15505 = KTree.node D2M8K2.t15512 (nat_lit 33853194) (nat_lit 3566339142) (nat_lit 0) D2M8K2.t15513 from rfl, totK_node, tot15512, tot15513]
  decide +kernel

theorem arows15506 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15506 = true := by
  rw [show D2M8K2.u15506 = KTree.node D2M8K2.t15514 (nat_lit 33855438) (nat_lit 3299731443) (nat_lit 0) D2M8K2.t15515 from rfl, allE_node, rows15514, irow15506, rows15515]
  all_goals rfl

theorem atot15506 : totK PD2M8K2 D2M8K2.u15506 = [0, 293906052307, 857789316265, 582714134503, 63438514121, 0, 0, 0] := by
  rw [show D2M8K2.u15506 = KTree.node D2M8K2.t15514 (nat_lit 33855438) (nat_lit 3299731443) (nat_lit 0) D2M8K2.t15515 from rfl, totK_node, tot15514, tot15515]
  decide +kernel

theorem arows15508 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15508 = true := by
  rw [show D2M8K2.u15508 = KTree.node D2M8K2.t15516 (nat_lit 33857095) (nat_lit 2105113269) (nat_lit 0) D2M8K2.t15517 from rfl, allE_node, rows15516, irow15508, rows15517]
  all_goals rfl

theorem atot15508 : totK PD2M8K2 D2M8K2.u15508 = [0, 117416810786, 630990242907, 835371670278, 181437619926, 4980514959, 0, 0] := by
  rw [show D2M8K2.u15508 = KTree.node D2M8K2.t15516 (nat_lit 33857095) (nat_lit 2105113269) (nat_lit 0) D2M8K2.t15517 from rfl, totK_node, tot15516, tot15517]
  decide +kernel

theorem arows15509 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15509 = true := by
  rw [show D2M8K2.u15509 = KTree.node D2M8K2.t15518 (nat_lit 33859124) (nat_lit 3522467934) (nat_lit 0) D2M8K2.t15519 from rfl, allE_node, rows15518, irow15509, rows15519]
  all_goals rfl

theorem atot15509 : totK PD2M8K2 D2M8K2.u15509 = [0, 383476943421, 941017056761, 466326801013, 35671285417, 0, 0, 0] := by
  rw [show D2M8K2.u15509 = KTree.node D2M8K2.t15518 (nat_lit 33859124) (nat_lit 3522467934) (nat_lit 0) D2M8K2.t15519 from rfl, totK_node, tot15518, tot15519]
  decide +kernel

theorem arows15514 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15514 = true := by
  rw [show D2M8K2.u15514 = KTree.node D2M8K2.t15520 (nat_lit 33860784) (nat_lit 3528314512) (nat_lit 0) D2M8K2.t15521 from rfl, allE_node, rows15520, irow15514, rows15521]
  all_goals rfl

theorem atot15514 : totK PD2M8K2 D2M8K2.u15514 = [0, 0, 496552824890, 979939495609, 298711014434, 8710740030, 0, 0] := by
  rw [show D2M8K2.u15514 = KTree.node D2M8K2.t15520 (nat_lit 33860784) (nat_lit 3528314512) (nat_lit 0) D2M8K2.t15521 from rfl, totK_node, tot15520, tot15521]
  decide +kernel

theorem arows15515 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15515 = true := by
  rw [show D2M8K2.u15515 = KTree.node D2M8K2.t15522 (nat_lit 33862609) (nat_lit 1533549872) (nat_lit 0) D2M8K2.t15523 from rfl, allE_node, rows15522, irow15515, rows15523]
  all_goals rfl

theorem atot15515 : totK PD2M8K2 D2M8K2.u15515 = [0, 0, 348406767583, 930954279135, 441777729626, 28242304460, 0, 0] := by
  rw [show D2M8K2.u15515 = KTree.node D2M8K2.t15522 (nat_lit 33862609) (nat_lit 1533549872) (nat_lit 0) D2M8K2.t15523 from rfl, totK_node, tot15522, tot15523]
  decide +kernel

theorem arows15517 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15517 = true := by
  rw [show D2M8K2.u15517 = KTree.node D2M8K2.t15524 (nat_lit 33863860) (nat_lit 3265641280) (nat_lit 0) D2M8K2.t15525 from rfl, allE_node, rows15524, irow15517, rows15525]
  all_goals rfl

theorem atot15517 : totK PD2M8K2 D2M8K2.u15517 = [0, 0, 95041418925, 691085327899, 801925428097, 135195758064, 1369150432, 0] := by
  rw [show D2M8K2.u15517 = KTree.node D2M8K2.t15524 (nat_lit 33863860) (nat_lit 3265641280) (nat_lit 0) D2M8K2.t15525 from rfl, totK_node, tot15524, tot15525]
  decide +kernel

theorem arows15518 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15518 = true := by
  rw [show D2M8K2.u15518 = KTree.node D2M8K2.t15526 (nat_lit 33869477) (nat_lit 2346814945) (nat_lit 0) D2M8K2.t15527 from rfl, allE_node, rows15526, irow15518, rows15527]
  all_goals rfl

theorem atot15518 : totK PD2M8K2 D2M8K2.u15518 = [0, 0, 403366038285, 958072052051, 399082795634, 17707432322, 0, 0] := by
  rw [show D2M8K2.u15518 = KTree.node D2M8K2.t15526 (nat_lit 33869477) (nat_lit 2346814945) (nat_lit 0) D2M8K2.t15527 from rfl, totK_node, tot15526, tot15527]
  decide +kernel

theorem arows15521 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15521 = true := by
  rw [show D2M8K2.u15521 = KTree.node D2M8K2.t15528 (nat_lit 33873284) (nat_lit 2603802135) (nat_lit 8) D2M8K2.t15529 from rfl, allE_node, rows15528, irow15521, rows15529]
  all_goals rfl

theorem atot15521 : totK PD2M8K2 D2M8K2.u15521 = [0, 0, 350800576715, 957061147230, 458723895156, 24338215469, 0, 0] := by
  rw [show D2M8K2.u15521 = KTree.node D2M8K2.t15528 (nat_lit 33873284) (nat_lit 2603802135) (nat_lit 8) D2M8K2.t15529 from rfl, totK_node, tot15528, tot15529]
  decide +kernel

theorem arows15522 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15522 = true := by
  rw [show D2M8K2.u15522 = KTree.node D2M8K2.t15530 (nat_lit 33876464) (nat_lit 3664052384) (nat_lit 0) D2M8K2.t15531 from rfl, allE_node, rows15530, irow15522, rows15531]
  all_goals rfl

theorem atot15522 : totK PD2M8K2 D2M8K2.u15522 = [0, 0, 384567715285, 956616088291, 397265393934, 16205509301, 0, 0] := by
  rw [show D2M8K2.u15522 = KTree.node D2M8K2.t15530 (nat_lit 33876464) (nat_lit 3664052384) (nat_lit 0) D2M8K2.t15531 from rfl, totK_node, tot15530, tot15531]
  decide +kernel

theorem arows15524 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15524 = true := by
  rw [show D2M8K2.u15524 = KTree.node D2M8K2.t15532 (nat_lit 33879870) (nat_lit 3271644038) (nat_lit 0) D2M8K2.t15533 from rfl, allE_node, rows15532, irow15524, rows15533]
  all_goals rfl

theorem atot15524 : totK PD2M8K2 D2M8K2.u15524 = [0, 0, 390152962388, 965986558655, 440093661315, 17485252951, 0, 0] := by
  rw [show D2M8K2.u15524 = KTree.node D2M8K2.t15532 (nat_lit 33879870) (nat_lit 3271644038) (nat_lit 0) D2M8K2.t15533 from rfl, totK_node, tot15532, tot15533]
  decide +kernel

theorem arows15525 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15525 = true := by
  rw [show D2M8K2.u15525 = KTree.node D2M8K2.t15534 (nat_lit 33886793) (nat_lit 1628766630) (nat_lit 0) D2M8K2.t15535 from rfl, allE_node, rows15534, irow15525, rows15535]
  all_goals rfl

theorem atot15525 : totK PD2M8K2 D2M8K2.u15525 = [0, 353535550406, 842468670723, 506110115271, 120536975419, 12231389608, 0, 0] := by
  rw [show D2M8K2.u15525 = KTree.node D2M8K2.t15534 (nat_lit 33886793) (nat_lit 1628766630) (nat_lit 0) D2M8K2.t15535 from rfl, totK_node, tot15534, tot15535]
  decide +kernel

theorem arows15529 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15529 = true := by
  rw [show D2M8K2.u15529 = KTree.node D2M8K2.t15536 (nat_lit 33888290) (nat_lit 4100234929) (nat_lit 0) D2M8K2.t15537 from rfl, allE_node, rows15536, irow15529, rows15537]
  all_goals rfl

theorem atot15529 : totK PD2M8K2 D2M8K2.u15529 = [0, 89058976036, 561166968393, 830603950419, 329941487973, 25373788367, 0, 0] := by
  rw [show D2M8K2.u15529 = KTree.node D2M8K2.t15536 (nat_lit 33888290) (nat_lit 4100234929) (nat_lit 0) D2M8K2.t15537 from rfl, totK_node, tot15536, tot15537]
  decide +kernel

theorem arows15530 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15530 = true := by
  rw [show D2M8K2.u15530 = KTree.node D2M8K2.t15538 (nat_lit 33889531) (nat_lit 1124750733) (nat_lit 0) D2M8K2.t15539 from rfl, allE_node, rows15538, irow15530, rows15539]
  all_goals rfl

theorem atot15530 : totK PD2M8K2 D2M8K2.u15530 = [0, 197141082129, 634155042239, 714314830011, 260665776996, 12235609738, 0, 0] := by
  rw [show D2M8K2.u15530 = KTree.node D2M8K2.t15538 (nat_lit 33889531) (nat_lit 1124750733) (nat_lit 0) D2M8K2.t15539 from rfl, totK_node, tot15538, tot15539]
  decide +kernel

theorem arows15532 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15532 = true := by
  rw [show D2M8K2.u15532 = KTree.node D2M8K2.t15540 (nat_lit 33891033) (nat_lit 1598931878) (nat_lit 0) D2M8K2.t15541 from rfl, allE_node, rows15540, irow15532, rows15541]
  all_goals rfl

theorem atot15532 : totK PD2M8K2 D2M8K2.u15532 = [0, 227760893676, 797280100220, 667695661094, 107058669647, 1163840124, 0, 0] := by
  rw [show D2M8K2.u15532 = KTree.node D2M8K2.t15540 (nat_lit 33891033) (nat_lit 1598931878) (nat_lit 0) D2M8K2.t15541 from rfl, totK_node, tot15540, tot15541]
  decide +kernel

theorem arows15533 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15533 = true := by
  rw [show D2M8K2.u15533 = KTree.node D2M8K2.t15542 (nat_lit 33892746) (nat_lit 3541927789) (nat_lit 0) D2M8K2.t15543 from rfl, allE_node, rows15542, irow15533, rows15543]
  all_goals rfl

theorem atot15533 : totK PD2M8K2 D2M8K2.u15533 = [0, 177909920641, 637141126447, 764425112878, 224354821948, 11873025674, 0, 0] := by
  rw [show D2M8K2.u15533 = KTree.node D2M8K2.t15542 (nat_lit 33892746) (nat_lit 3541927789) (nat_lit 0) D2M8K2.t15543 from rfl, totK_node, tot15542, tot15543]
  decide +kernel

theorem arows15536 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15536 = true := by
  rw [show D2M8K2.u15536 = KTree.node D2M8K2.t15544 (nat_lit 33894710) (nat_lit 3179676548) (nat_lit 0) D2M8K2.t15545 from rfl, allE_node, rows15544, irow15536, rows15545]
  all_goals rfl

theorem atot15536 : totK PD2M8K2 D2M8K2.u15536 = [0, 153907372348, 716230687839, 790182511176, 174154291506, 7053496397, 0, 0] := by
  rw [show D2M8K2.u15536 = KTree.node D2M8K2.t15544 (nat_lit 33894710) (nat_lit 3179676548) (nat_lit 0) D2M8K2.t15545 from rfl, totK_node, tot15544, tot15545]
  decide +kernel

theorem arows15537 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15537 = true := by
  rw [show D2M8K2.u15537 = KTree.node D2M8K2.t15546 (nat_lit 33896945) (nat_lit 1736990360) (nat_lit 0) D2M8K2.t15547 from rfl, allE_node, rows15546, irow15537, rows15547]
  all_goals rfl

theorem atot15537 : totK PD2M8K2 D2M8K2.u15537 = [0, 297395867755, 842406961968, 596636025525, 95524146464, 1334898114, 0, 0] := by
  rw [show D2M8K2.u15537 = KTree.node D2M8K2.t15546 (nat_lit 33896945) (nat_lit 1736990360) (nat_lit 0) D2M8K2.t15547 from rfl, totK_node, tot15546, tot15547]
  decide +kernel

theorem arows15539 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15539 = true := by
  rw [show D2M8K2.u15539 = KTree.node D2M8K2.t15548 (nat_lit 33898800) (nat_lit 3456080827) (nat_lit 0) D2M8K2.t15549 from rfl, allE_node, rows15548, irow15539, rows15549]
  all_goals rfl

theorem atot15539 : totK PD2M8K2 D2M8K2.u15539 = [0, 153617666582, 712192081032, 794408713889, 151096670145, 3880716147, 0, 0] := by
  rw [show D2M8K2.u15539 = KTree.node D2M8K2.t15548 (nat_lit 33898800) (nat_lit 3456080827) (nat_lit 0) D2M8K2.t15549 from rfl, totK_node, tot15548, tot15549]
  decide +kernel

theorem arows15540 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15540 = true := by
  rw [show D2M8K2.u15540 = KTree.node D2M8K2.t15550 (nat_lit 33900651) (nat_lit 3719234846) (nat_lit 0) D2M8K2.t15551 from rfl, allE_node, rows15550, irow15540, rows15551]
  all_goals rfl

theorem atot15540 : totK PD2M8K2 D2M8K2.u15540 = [0, 350766944467, 931454120235, 520622242356, 40928392638, 0, 0, 0] := by
  rw [show D2M8K2.u15540 = KTree.node D2M8K2.t15550 (nat_lit 33900651) (nat_lit 3719234846) (nat_lit 0) D2M8K2.t15551 from rfl, totK_node, tot15550, tot15551]
  decide +kernel

theorem arows15546 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15546 = true := by
  rw [show D2M8K2.u15546 = KTree.node D2M8K2.t15552 (nat_lit 33902346) (nat_lit 3195329895) (nat_lit 0) D2M8K2.t15553 from rfl, allE_node, rows15552, irow15546, rows15553]
  all_goals rfl

theorem atot15546 : totK PD2M8K2 D2M8K2.u15546 = [0, 0, 454350559677, 994084254334, 339449351429, 9902458238, 0, 0] := by
  rw [show D2M8K2.u15546 = KTree.node D2M8K2.t15552 (nat_lit 33902346) (nat_lit 3195329895) (nat_lit 0) D2M8K2.t15553 from rfl, totK_node, tot15552, tot15553]
  decide +kernel

theorem arows15547 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15547 = true := by
  rw [show D2M8K2.u15547 = KTree.node D2M8K2.t15554 (nat_lit 33907563) (nat_lit 3731856320) (nat_lit 0) D2M8K2.t15555 from rfl, allE_node, rows15554, irow15547, rows15555]
  all_goals rfl

theorem atot15547 : totK PD2M8K2 D2M8K2.u15547 = [0, 0, 352685976395, 914322042040, 523571086616, 45105177329, 0, 0] := by
  rw [show D2M8K2.u15547 = KTree.node D2M8K2.t15554 (nat_lit 33907563) (nat_lit 3731856320) (nat_lit 0) D2M8K2.t15555 from rfl, totK_node, tot15554, tot15555]
  decide +kernel

theorem arows15549 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15549 = true := by
  rw [show D2M8K2.u15549 = KTree.node D2M8K2.t15556 (nat_lit 33909060) (nat_lit 770263962) (nat_lit 512) D2M8K2.t15557 from rfl, allE_node, rows15556, irow15549, rows15557]
  all_goals rfl

theorem atot15549 : totK PD2M8K2 D2M8K2.u15549 = [0, 0, 88825966916, 523350771732, 834650091076, 337926239139, 25137911187, 0] := by
  rw [show D2M8K2.u15549 = KTree.node D2M8K2.t15556 (nat_lit 33909060) (nat_lit 770263962) (nat_lit 512) D2M8K2.t15557 from rfl, totK_node, tot15556, tot15557]
  decide +kernel

theorem arows15550 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15550 = true := by
  rw [show D2M8K2.u15550 = KTree.node D2M8K2.t15558 (nat_lit 33910389) (nat_lit 1638426429) (nat_lit 0) D2M8K2.t15559 from rfl, allE_node, rows15558, irow15550, rows15559]
  all_goals rfl

theorem atot15550 : totK PD2M8K2 D2M8K2.u15550 = [0, 0, 252384295779, 694812010963, 656662576190, 198430838389, 7877424857, 0] := by
  rw [show D2M8K2.u15550 = KTree.node D2M8K2.t15558 (nat_lit 33910389) (nat_lit 1638426429) (nat_lit 0) D2M8K2.t15559 from rfl, totK_node, tot15558, tot15559]
  decide +kernel

theorem arows15553 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15553 = true := by
  rw [show D2M8K2.u15553 = KTree.node D2M8K2.t15560 (nat_lit 33911872) (nat_lit 2998678529) (nat_lit 0) D2M8K2.t15561 from rfl, allE_node, rows15560, irow15553, rows15561]
  all_goals rfl

theorem atot15553 : totK PD2M8K2 D2M8K2.u15553 = [0, 0, 170886246066, 785450559090, 741539824670, 96410964404, 0, 0] := by
  rw [show D2M8K2.u15553 = KTree.node D2M8K2.t15560 (nat_lit 33911872) (nat_lit 2998678529) (nat_lit 0) D2M8K2.t15561 from rfl, totK_node, tot15560, tot15561]
  decide +kernel

theorem arows15554 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15554 = true := by
  rw [show D2M8K2.u15554 = KTree.node D2M8K2.t15562 (nat_lit 33914147) (nat_lit 2953463228) (nat_lit 0) D2M8K2.t15563 from rfl, allE_node, rows15562, irow15554, rows15563]
  all_goals rfl

theorem atot15554 : totK PD2M8K2 D2M8K2.u15554 = [0, 0, 245931159717, 751633397372, 667830744161, 151769100102, 5159868635, 0] := by
  rw [show D2M8K2.u15554 = KTree.node D2M8K2.t15562 (nat_lit 33914147) (nat_lit 2953463228) (nat_lit 0) D2M8K2.t15563 from rfl, totK_node, tot15562, tot15563]
  decide +kernel

theorem arows15556 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15556 = true := by
  rw [show D2M8K2.u15556 = KTree.node D2M8K2.t15564 (nat_lit 33916410) (nat_lit 3943699390) (nat_lit 0) D2M8K2.t15565 from rfl, allE_node, rows15564, irow15556, rows15565]
  all_goals rfl

theorem atot15556 : totK PD2M8K2 D2M8K2.u15556 = [0, 0, 156348885095, 754049023149, 778449146408, 133764666459, 1557581783, 0] := by
  rw [show D2M8K2.u15556 = KTree.node D2M8K2.t15564 (nat_lit 33916410) (nat_lit 3943699390) (nat_lit 0) D2M8K2.t15565 from rfl, totK_node, tot15564, tot15565]
  decide +kernel

theorem arows15557 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15557 = true := by
  rw [show D2M8K2.u15557 = KTree.node D2M8K2.t15566 (nat_lit 33918091) (nat_lit 1813946904) (nat_lit 0) D2M8K2.t15567 from rfl, allE_node, rows15566, irow15557, rows15567]
  all_goals rfl

theorem atot15557 : totK PD2M8K2 D2M8K2.u15557 = [0, 0, 307577030460, 897092086318, 562368003956, 53049371202, 0, 0] := by
  rw [show D2M8K2.u15557 = KTree.node D2M8K2.t15566 (nat_lit 33918091) (nat_lit 1813946904) (nat_lit 0) D2M8K2.t15567 from rfl, totK_node, tot15566, tot15567]
  decide +kernel

theorem arows15561 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15561 = true := by
  rw [show D2M8K2.u15561 = KTree.node D2M8K2.t15568 (nat_lit 33920320) (nat_lit 2832196284) (nat_lit 0) D2M8K2.t15569 from rfl, allE_node, rows15568, irow15561, rows15569]
  all_goals rfl

theorem atot15561 : totK PD2M8K2 D2M8K2.u15561 = [0, 0, 193267952512, 750882154933, 769874077961, 117519735196, 1415142070, 0] := by
  rw [show D2M8K2.u15561 = KTree.node D2M8K2.t15568 (nat_lit 33920320) (nat_lit 2832196284) (nat_lit 0) D2M8K2.t15569 from rfl, totK_node, tot15568, tot15569]
  decide +kernel

theorem arows15562 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15562 = true := by
  rw [show D2M8K2.u15562 = KTree.node D2M8K2.t15570 (nat_lit 33922163) (nat_lit 2907377834) (nat_lit 0) D2M8K2.t15571 from rfl, allE_node, rows15570, irow15562, rows15571]
  all_goals rfl

theorem atot15562 : totK PD2M8K2 D2M8K2.u15562 = [0, 0, 224890526754, 851875574109, 675017130980, 76118502862, 0, 0] := by
  rw [show D2M8K2.u15562 = KTree.node D2M8K2.t15570 (nat_lit 33922163) (nat_lit 2907377834) (nat_lit 0) D2M8K2.t15571 from rfl, totK_node, tot15570, tot15571]
  decide +kernel

theorem arows15564 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15564 = true := by
  rw [show D2M8K2.u15564 = KTree.node D2M8K2.t15572 (nat_lit 33924089) (nat_lit 1157761238) (nat_lit 0) D2M8K2.t15573 from rfl, allE_node, rows15572, irow15564, rows15573]
  all_goals rfl

theorem atot15564 : totK PD2M8K2 D2M8K2.u15564 = [0, 200591725335, 483284037543, 373136425579, 501840976963, 217626407399, 9302370699, 0] := by
  rw [show D2M8K2.u15564 = KTree.node D2M8K2.t15572 (nat_lit 33924089) (nat_lit 1157761238) (nat_lit 0) D2M8K2.t15573 from rfl, totK_node, tot15572, tot15573]
  decide +kernel

theorem arows15565 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15565 = true := by
  rw [show D2M8K2.u15565 = KTree.node D2M8K2.t15574 (nat_lit 33925657) (nat_lit 1516127035) (nat_lit 0) D2M8K2.t15575 from rfl, allE_node, rows15574, irow15565, rows15575]
  all_goals rfl

theorem atot15565 : totK PD2M8K2 D2M8K2.u15565 = [0, 212584788644, 751814240653, 676675696556, 115105200220, 1369150432, 0, 0] := by
  rw [show D2M8K2.u15565 = KTree.node D2M8K2.t15574 (nat_lit 33925657) (nat_lit 1516127035) (nat_lit 0) D2M8K2.t15575 from rfl, totK_node, tot15574, tot15575]
  decide +kernel

theorem arows15568 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15568 = true := by
  rw [show D2M8K2.u15568 = KTree.node D2M8K2.t15576 (nat_lit 33928013) (nat_lit 2203909609) (nat_lit 0) D2M8K2.t15577 from rfl, allE_node, rows15576, irow15568, rows15577]
  all_goals rfl

theorem atot15568 : totK PD2M8K2 D2M8K2.u15568 = [0, 251010917945, 829145553072, 683655924304, 74498963699, 0, 0, 0] := by
  rw [show D2M8K2.u15568 = KTree.node D2M8K2.t15576 (nat_lit 33928013) (nat_lit 2203909609) (nat_lit 0) D2M8K2.t15577 from rfl, totK_node, tot15576, tot15577]
  decide +kernel

theorem arows15569 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15569 = true := by
  rw [show D2M8K2.u15569 = KTree.node D2M8K2.t15578 (nat_lit 33929219) (nat_lit 2870585650) (nat_lit 0) D2M8K2.t15579 from rfl, allE_node, rows15578, irow15569, rows15579]
  all_goals rfl

theorem atot15569 : totK PD2M8K2 D2M8K2.u15569 = [0, 172532957301, 664911404640, 711727080006, 237957006410, 21156758932, 0, 0] := by
  rw [show D2M8K2.u15569 = KTree.node D2M8K2.t15578 (nat_lit 33929219) (nat_lit 2870585650) (nat_lit 0) D2M8K2.t15579 from rfl, totK_node, tot15578, tot15579]
  decide +kernel

theorem arows15571 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15571 = true := by
  rw [show D2M8K2.u15571 = KTree.node D2M8K2.t15580 (nat_lit 33930766) (nat_lit 4014680920) (nat_lit 0) D2M8K2.t15581 from rfl, allE_node, rows15580, irow15571, rows15581]
  all_goals rfl

theorem atot15571 : totK PD2M8K2 D2M8K2.u15571 = [0, 154105568542, 555160658822, 744239446525, 327130361056, 14829996138, 0, 0] := by
  rw [show D2M8K2.u15571 = KTree.node D2M8K2.t15580 (nat_lit 33930766) (nat_lit 4014680920) (nat_lit 0) D2M8K2.t15581 from rfl, totK_node, tot15580, tot15581]
  decide +kernel

theorem arows15572 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15572 = true := by
  rw [show D2M8K2.u15572 = KTree.node D2M8K2.t15582 (nat_lit 33932221) (nat_lit 1213604548) (nat_lit 0) D2M8K2.t15583 from rfl, allE_node, rows15582, irow15572, rows15583]
  all_goals rfl

theorem atot15572 : totK PD2M8K2 D2M8K2.u15572 = [0, 287887201638, 893217972652, 595490635547, 55036053689, 0, 0, 0] := by
  rw [show D2M8K2.u15572 = KTree.node D2M8K2.t15582 (nat_lit 33932221) (nat_lit 1213604548) (nat_lit 0) D2M8K2.t15583 from rfl, totK_node, tot15582, tot15583]
  decide +kernel

theorem arows15577 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15577 = true := by
  rw [show D2M8K2.u15577 = KTree.node D2M8K2.t15584 (nat_lit 33933895) (nat_lit 2121005239) (nat_lit 0) D2M8K2.t15585 from rfl, allE_node, rows15584, irow15577, rows15585]
  all_goals rfl

theorem atot15577 : totK PD2M8K2 D2M8K2.u15577 = [0, 82968919721, 519602029013, 885996877841, 285803503280, 13049727234, 0, 0] := by
  rw [show D2M8K2.u15577 = KTree.node D2M8K2.t15584 (nat_lit 33933895) (nat_lit 2121005239) (nat_lit 0) D2M8K2.t15585 from rfl, totK_node, tot15584, tot15585]
  decide +kernel

theorem arows15578 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15578 = true := by
  rw [show D2M8K2.u15578 = KTree.node D2M8K2.t15586 (nat_lit 33938673) (nat_lit 1586135165) (nat_lit 0) D2M8K2.t15587 from rfl, allE_node, rows15586, irow15578, rows15587]
  all_goals rfl

theorem atot15578 : totK PD2M8K2 D2M8K2.u15578 = [0, 316936712882, 912420579108, 524416003603, 40126426591, 0, 0, 0] := by
  rw [show D2M8K2.u15578 = KTree.node D2M8K2.t15586 (nat_lit 33938673) (nat_lit 1586135165) (nat_lit 0) D2M8K2.t15587 from rfl, totK_node, tot15586, tot15587]
  decide +kernel

theorem arows15580 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15580 = true := by
  rw [show D2M8K2.u15580 = KTree.node D2M8K2.t15588 (nat_lit 33940808) (nat_lit 3713827311) (nat_lit 0) D2M8K2.t15589 from rfl, allE_node, rows15588, irow15580, rows15589]
  all_goals rfl

theorem atot15580 : totK PD2M8K2 D2M8K2.u15580 = [0, 129278630345, 641382556523, 821444129234, 180725699480, 4980514959, 0, 0] := by
  rw [show D2M8K2.u15580 = KTree.node D2M8K2.t15588 (nat_lit 33940808) (nat_lit 3713827311) (nat_lit 0) D2M8K2.t15589 from rfl, totK_node, tot15588, tot15589]
  decide +kernel

theorem arows15581 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15581 = true := by
  rw [show D2M8K2.u15581 = KTree.node D2M8K2.t15590 (nat_lit 33942287) (nat_lit 2145845470) (nat_lit 0) D2M8K2.t15591 from rfl, allE_node, rows15590, irow15581, rows15591]
  all_goals rfl

theorem atot15581 : totK PD2M8K2 D2M8K2.u15581 = [0, 291292115476, 881524302213, 603572665740, 56462152517, 0, 0, 0] := by
  rw [show D2M8K2.u15581 = KTree.node D2M8K2.t15590 (nat_lit 33942287) (nat_lit 2145845470) (nat_lit 0) D2M8K2.t15591 from rfl, totK_node, tot15590, tot15591]
  decide +kernel

theorem arows15584 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15584 = true := by
  rw [show D2M8K2.u15584 = KTree.node D2M8K2.t15592 (nat_lit 33943998) (nat_lit 3726036954) (nat_lit 0) D2M8K2.t15593 from rfl, allE_node, rows15592, irow15584, rows15593]
  all_goals rfl

theorem atot15584 : totK PD2M8K2 D2M8K2.u15584 = [0, 0, 405759296597, 957857340558, 396788125970, 22015408867, 0, 0] := by
  rw [show D2M8K2.u15584 = KTree.node D2M8K2.t15592 (nat_lit 33943998) (nat_lit 3726036954) (nat_lit 0) D2M8K2.t15593 from rfl, totK_node, tot15592, tot15593]
  decide +kernel

theorem arows15585 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15585 = true := by
  rw [show D2M8K2.u15585 = KTree.node D2M8K2.t15594 (nat_lit 33945856) (nat_lit 1808381007) (nat_lit 0) D2M8K2.t15595 from rfl, allE_node, rows15594, irow15585, rows15595]
  all_goals rfl

theorem atot15585 : totK PD2M8K2 D2M8K2.u15585 = [0, 0, 350475141403, 950923152633, 426099686857, 18717096757, 0, 0] := by
  rw [show D2M8K2.u15585 = KTree.node D2M8K2.t15594 (nat_lit 33945856) (nat_lit 1808381007) (nat_lit 0) D2M8K2.t15595 from rfl, totK_node, tot15594, tot15595]
  decide +kernel

theorem arows15587 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15587 = true := by
  rw [show D2M8K2.u15587 = KTree.node D2M8K2.t15596 (nat_lit 33947781) (nat_lit 1497997157) (nat_lit 0) D2M8K2.t15597 from rfl, allE_node, rows15596, irow15587, rows15597]
  all_goals rfl

theorem atot15587 : totK PD2M8K2 D2M8K2.u15587 = [0, 0, 138455550409, 698747938106, 805855116695, 123159543904, 1206465782, 0] := by
  rw [show D2M8K2.u15587 = KTree.node D2M8K2.t15596 (nat_lit 33947781) (nat_lit 1497997157) (nat_lit 0) D2M8K2.t15597 from rfl, totK_node, tot15596, tot15597]
  decide +kernel

theorem arows15588 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15588 = true := by
  rw [show D2M8K2.u15588 = KTree.node D2M8K2.t15598 (nat_lit 33949593) (nat_lit 1821944165) (nat_lit 0) D2M8K2.t15599 from rfl, allE_node, rows15598, irow15588, rows15599]
  all_goals rfl

theorem atot15588 : totK PD2M8K2 D2M8K2.u15588 = [0, 0, 369739500613, 951599054725, 448379409927, 25633279248, 0, 0] := by
  rw [show D2M8K2.u15588 = KTree.node D2M8K2.t15598 (nat_lit 33949593) (nat_lit 1821944165) (nat_lit 0) D2M8K2.t15599 from rfl, totK_node, tot15598, tot15599]
  decide +kernel

end QECKChecks.D2M8K2
