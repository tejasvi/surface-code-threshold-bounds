import QEC.Count.ChunksK3
import QEC.KChecks.A10K2.A12

namespace QECKChecks.A10K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows3866 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3866 = true := by
  rw [show A10K2.u3866 = KTree.node A10K2.u3850 (nat_lit 62209271) (nat_lit 11745978097) (nat_lit 0) A10K2.u3865 from rfl, allE_node, arows3850, irow3866, arows3865]
  all_goals rfl

theorem atot3866 : totK PA10K2 A10K2.u3866 = [0, 0, 582523478866, 11444411277279, 43770240452377, 60198307330478, 28862729909496, 5141410020222, 260227224558, 0] := by
  rw [show A10K2.u3866 = KTree.node A10K2.u3850 (nat_lit 62209271) (nat_lit 11745978097) (nat_lit 0) A10K2.u3865 from rfl, totK_node, atot3850, atot3865]
  decide +kernel

theorem arows3897 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3897 = true := by
  rw [show A10K2.u3897 = KTree.node A10K2.u3881 (nat_lit 63115811) (nat_lit 3516931358) (nat_lit 0) A10K2.u3896 from rfl, allE_node, arows3881, irow3897, arows3896]
  all_goals rfl

theorem atot3897 : totK PA10K2 A10K2.u3897 = [0, 4451106476601, 26028235199295, 55196956210070, 50135154443092, 18708880008924, 2802276487512, 535254778015, 142269073820, 6354482628] := by
  rw [show A10K2.u3897 = KTree.node A10K2.u3881 (nat_lit 63115811) (nat_lit 3516931358) (nat_lit 0) A10K2.u3896 from rfl, totK_node, atot3881, atot3896]
  decide +kernel

theorem arows3929 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3929 = true := by
  rw [show A10K2.u3929 = KTree.node A10K2.u3913 (nat_lit 63388900) (nat_lit 8291752774) (nat_lit 0) A10K2.u3928 from rfl, allE_node, arows3913, irow3929, arows3928]
  all_goals rfl

theorem atot3929 : totK PA10K2 A10K2.u3929 = [0, 2305653685916, 15584164519683, 42266612768104, 55595017912561, 33357018509384, 7517974238916, 570213540689, 7903172220, 0] := by
  rw [show A10K2.u3929 = KTree.node A10K2.u3913 (nat_lit 63388900) (nat_lit 8291752774) (nat_lit 0) A10K2.u3928 from rfl, totK_node, atot3913, atot3928]
  decide +kernel

theorem arows3960 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3960 = true := by
  rw [show A10K2.u3960 = KTree.node A10K2.u3944 (nat_lit 63649028) (nat_lit 9826860697) (nat_lit 0) A10K2.u3959 from rfl, allE_node, arows3944, irow3960, arows3959]
  all_goals rfl

theorem atot3960 : totK PA10K2 A10K2.u3960 = [0, 3761870872245, 23289670391650, 52991133231786, 52688636976836, 21346141042953, 3006609908971, 119306484592, 0, 0] := by
  rw [show A10K2.u3960 = KTree.node A10K2.u3944 (nat_lit 63649028) (nat_lit 9826860697) (nat_lit 0) A10K2.u3959 from rfl, totK_node, atot3944, atot3959]
  decide +kernel

theorem arows3993 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3993 = true := by
  rw [show A10K2.u3993 = KTree.node A10K2.u3977 (nat_lit 63852645) (nat_lit 7000149661) (nat_lit 0) A10K2.u3992 from rfl, allE_node, arows3977, irow3993, arows3992]
  all_goals rfl

theorem atot3993 : totK PA10K2 A10K2.u3993 = [0, 887742285343, 9001852728916, 33540512927028, 56558971994635, 42467363137123, 12299851660411, 1322828869675, 42943767608, 0] := by
  rw [show A10K2.u3993 = KTree.node A10K2.u3977 (nat_lit 63852645) (nat_lit 7000149661) (nat_lit 0) A10K2.u3992 from rfl, totK_node, atot3977, atot3992]
  decide +kernel

theorem arows4024 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4024 = true := by
  rw [show A10K2.u4024 = KTree.node A10K2.u4008 (nat_lit 64582994) (nat_lit 14949541530) (nat_lit 0) A10K2.u4023 from rfl, allE_node, arows4008, irow4024, arows4023]
  all_goals rfl

theorem atot4024 : totK PA10K2 A10K2.u4024 = [0, 5505716900399, 29930240825877, 58224982113937, 47640076891287, 15167397671448, 1703536475258, 50568959078, 0, 0] := by
  rw [show A10K2.u4024 = KTree.node A10K2.u4008 (nat_lit 64582994) (nat_lit 14949541530) (nat_lit 0) A10K2.u4023 from rfl, totK_node, atot4008, atot4023]
  decide +kernel

theorem arows4056 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4056 = true := by
  rw [show A10K2.u4056 = KTree.node A10K2.u4040 (nat_lit 64782691) (nat_lit 3573085903) (nat_lit 0) A10K2.u4055 from rfl, allE_node, arows4040, irow4056, arows4055]
  all_goals rfl

theorem atot4056 : totK PA10K2 A10K2.u4056 = [0, 0, 6386133655996, 33630737565792, 61393743640103, 44537201002042, 11470727348371, 917951938926, 14159155365, 0] := by
  rw [show A10K2.u4056 = KTree.node A10K2.u4040 (nat_lit 64782691) (nat_lit 3573085903) (nat_lit 0) A10K2.u4055 from rfl, totK_node, atot4040, atot4055]
  decide +kernel

theorem arows4087 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4087 = true := by
  rw [show A10K2.u4087 = KTree.node A10K2.u4071 (nat_lit 65006632) (nat_lit 11802388765) (nat_lit 0) A10K2.u4086 from rfl, allE_node, arows4071, irow4087, arows4086]
  all_goals rfl

theorem atot4087 : totK PA10K2 A10K2.u4087 = [2338692983822, 12465376030733, 26473554072797, 33570819706974, 36843031497520, 30492051073565, 11913016549701, 1706995895036, 73776485728, 0] := by
  rw [show A10K2.u4087 = KTree.node A10K2.u4071 (nat_lit 65006632) (nat_lit 11802388765) (nat_lit 0) A10K2.u4086 from rfl, totK_node, atot4071, atot4086]
  decide +kernel

theorem arows4125 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4125 = true := by
  rw [show A10K2.u4125 = KTree.node A10K2.u4109 (nat_lit 67308998) (nat_lit 15803271880) (nat_lit 0) A10K2.u4124 from rfl, allE_node, arows4109, irow4125, arows4124]
  all_goals rfl

theorem atot4125 : totK PA10K2 A10K2.u4125 = [3944858961693, 24099521523426, 53348115251253, 51215522815656, 20129361323684, 2852876971801, 110747515857, 0, 0, 0] := by
  rw [show A10K2.u4125 = KTree.node A10K2.u4109 (nat_lit 67308998) (nat_lit 15803271880) (nat_lit 0) A10K2.u4124 from rfl, totK_node, atot4109, atot4124]
  decide +kernel

theorem arows4156 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4156 = true := by
  rw [show A10K2.u4156 = KTree.node A10K2.u4140 (nat_lit 67516642) (nat_lit 13448927307) (nat_lit 0) A10K2.u4155 from rfl, allE_node, arows4140, irow4156, arows4155]
  all_goals rfl

theorem atot4156 : totK PA10K2 A10K2.u4156 = [833436429740, 7919925039700, 31466014189161, 56657342861221, 43032734374867, 12140685678036, 1286659264900, 41810754621, 0, 0] := by
  rw [show A10K2.u4156 = KTree.node A10K2.u4140 (nat_lit 67516642) (nat_lit 13448927307) (nat_lit 0) A10K2.u4155 from rfl, totK_node, atot4140, atot4155]
  decide +kernel

theorem arows4188 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4188 = true := by
  rw [show A10K2.u4188 = KTree.node A10K2.u4172 (nat_lit 68238778) (nat_lit 14470741792) (nat_lit 0) A10K2.u4187 from rfl, allE_node, arows4172, irow4188, arows4187]
  all_goals rfl

theorem atot4188 : totK PA10K2 A10K2.u4188 = [5118801067077, 28574899349455, 56342855003462, 46343404641217, 15372336524005, 1918802371379, 73400861101, 0, 0, 0] := by
  rw [show A10K2.u4188 = KTree.node A10K2.u4172 (nat_lit 68238778) (nat_lit 14470741792) (nat_lit 0) A10K2.u4187 from rfl, totK_node, atot4172, atot4187]
  decide +kernel

theorem arows4219 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4219 = true := by
  rw [show A10K2.u4219 = KTree.node A10K2.u4203 (nat_lit 68500631) (nat_lit 13993239748) (nat_lit 0) A10K2.u4218 from rfl, allE_node, arows4203, irow4219, arows4218]
  all_goals rfl

theorem atot4219 : totK PA10K2 A10K2.u4219 = [0, 8193346136912, 38961828435341, 61777617053423, 35696489776667, 7109209709264, 442688075185, 0, 0, 0] := by
  rw [show A10K2.u4219 = KTree.node A10K2.u4203 (nat_lit 68500631) (nat_lit 13993239748) (nat_lit 0) A10K2.u4218 from rfl, totK_node, atot4203, atot4218]
  decide +kernel

theorem arows4252 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4252 = true := by
  rw [show A10K2.u4252 = KTree.node A10K2.u4236 (nat_lit 68881874) (nat_lit 14483072709) (nat_lit 0) A10K2.u4251 from rfl, allE_node, arows4236, irow4252, arows4251]
  all_goals rfl

theorem atot4252 : totK PA10K2 A10K2.u4252 = [4449301618478, 25506501687143, 54064676527940, 50749495104761, 20090992909016, 2929142645481, 196177668405, 6354482628, 0, 0] := by
  rw [show A10K2.u4252 = KTree.node A10K2.u4236 (nat_lit 68881874) (nat_lit 14483072709) (nat_lit 0) A10K2.u4251 from rfl, totK_node, atot4236, atot4251]
  decide +kernel

theorem arows4283 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4283 = true := by
  rw [show A10K2.u4283 = KTree.node A10K2.u4267 (nat_lit 69150207) (nat_lit 13916475012) (nat_lit 0) A10K2.u4282 from rfl, allE_node, arows4267, irow4283, arows4282]
  all_goals rfl

theorem atot4283 : totK PA10K2 A10K2.u4283 = [0, 5001498144754, 27784533554101, 56325976115641, 49000686783613, 17264820242699, 2177196995533, 80784460143, 0, 0] := by
  rw [show A10K2.u4283 = KTree.node A10K2.u4267 (nat_lit 69150207) (nat_lit 13916475012) (nat_lit 0) A10K2.u4282 from rfl, totK_node, atot4267, atot4282]
  decide +kernel

theorem arows4315 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4315 = true := by
  rw [show A10K2.u4315 = KTree.node A10K2.u4299 (nat_lit 69346669) (nat_lit 6361276028) (nat_lit 0) A10K2.u4314 from rfl, allE_node, arows4299, irow4315, arows4314]
  all_goals rfl

theorem atot4315 : totK PA10K2 A10K2.u4315 = [0, 5407904574212, 29793754411754, 58108090227060, 46060449568075, 13142311746899, 1306653690628, 42173223013, 0, 0] := by
  rw [show A10K2.u4315 = KTree.node A10K2.u4299 (nat_lit 69346669) (nat_lit 6361276028) (nat_lit 0) A10K2.u4314 from rfl, totK_node, atot4299, atot4314]
  decide +kernel

theorem arows4346 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4346 = true := by
  rw [show A10K2.u4346 = KTree.node A10K2.u4330 (nat_lit 69504520) (nat_lit 14393746616) (nat_lit 0) A10K2.u4345 from rfl, allE_node, arows4330, irow4346, arows4345]
  all_goals rfl

theorem atot4346 : totK PA10K2 A10K2.u4346 = [0, 0, 6261600501390, 33043783916011, 59865783114009, 41383117171734, 10587223111636, 1089992113549, 36134558889, 0] := by
  rw [show A10K2.u4346 = KTree.node A10K2.u4330 (nat_lit 69504520) (nat_lit 14393746616) (nat_lit 0) A10K2.u4345 from rfl, totK_node, atot4330, atot4345]
  decide +kernel

theorem arows4380 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4380 = true := by
  rw [show A10K2.u4380 = KTree.node A10K2.u4364 (nat_lit 70290198) (nat_lit 2657097635) (nat_lit 0) A10K2.u4379 from rfl, allE_node, arows4364, irow4380, arows4379]
  all_goals rfl

theorem atot4380 : totK PA10K2 A10K2.u4380 = [0, 4276111124423, 24829867446462, 52769463309285, 49384189289766, 19661275150943, 3435621972900, 269614583639, 5676195732, 0] := by
  rw [show A10K2.u4380 = KTree.node A10K2.u4364 (nat_lit 70290198) (nat_lit 2657097635) (nat_lit 0) A10K2.u4379 from rfl, totK_node, atot4364, atot4379]
  decide +kernel

theorem arows4411 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4411 = true := by
  rw [show A10K2.u4411 = KTree.node A10K2.u4395 (nat_lit 70533745) (nat_lit 7601952783) (nat_lit 0) A10K2.u4410 from rfl, allE_node, arows4395, irow4411, arows4410]
  all_goals rfl

theorem atot4411 : totK PA10K2 A10K2.u4411 = [0, 1671892701588, 16503857977532, 49739606742802, 57851164985848, 23402598193028, 3026160765250, 99198744494, 0, 0] := by
  rw [show A10K2.u4411 = KTree.node A10K2.u4395 (nat_lit 70533745) (nat_lit 7601952783) (nat_lit 0) A10K2.u4410 from rfl, totK_node, atot4395, atot4410]
  decide +kernel

theorem arows4443 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4443 = true := by
  rw [show A10K2.u4443 = KTree.node A10K2.u4427 (nat_lit 70828977) (nat_lit 9063755359) (nat_lit 0) A10K2.u4442 from rfl, allE_node, arows4427, irow4443, arows4442]
  all_goals rfl

theorem atot4443 : totK PA10K2 A10K2.u4443 = [0, 4443731494829, 24817164690069, 51824090649382, 49425236158326, 21565734728790, 4062750994855, 305684757809, 5976421810, 0] := by
  rw [show A10K2.u4443 = KTree.node A10K2.u4427 (nat_lit 70828977) (nat_lit 9063755359) (nat_lit 0) A10K2.u4442 from rfl, totK_node, atot4427, atot4442]
  decide +kernel

theorem arows4474 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4474 = true := by
  rw [show A10K2.u4474 = KTree.node A10K2.u4458 (nat_lit 71946337) (nat_lit 8839683523) (nat_lit 0) A10K2.u4473 from rfl, allE_node, arows4458, irow4474, arows4473]
  all_goals rfl

theorem atot4474 : totK PA10K2 A10K2.u4474 = [4682757634830, 26133097982288, 52338712866666, 45480114486340, 18695584176662, 5529668738470, 1022896711909, 61110126106, 0, 0] := by
  rw [show A10K2.u4474 = KTree.node A10K2.u4458 (nat_lit 71946337) (nat_lit 8839683523) (nat_lit 0) A10K2.u4473 from rfl, totK_node, atot4458, atot4473]
  decide +kernel

theorem arows4507 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4507 = true := by
  rw [show A10K2.u4507 = KTree.node A10K2.u4491 (nat_lit 72170660) (nat_lit 11623958624) (nat_lit 0) A10K2.u4506 from rfl, allE_node, arows4491, irow4507, arows4506]
  all_goals rfl

theorem atot4507 : totK PA10K2 A10K2.u4507 = [1611752829918, 13047978683061, 39796981765015, 55742700683508, 35626308136285, 9485732112316, 1023712434611, 36704093874, 0, 0] := by
  rw [show A10K2.u4507 = KTree.node A10K2.u4491 (nat_lit 72170660) (nat_lit 11623958624) (nat_lit 0) A10K2.u4506 from rfl, totK_node, atot4491, atot4506]
  decide +kernel

theorem arows4538 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4538 = true := by
  rw [show A10K2.u4538 = KTree.node A10K2.u4522 (nat_lit 72352215) (nat_lit 10069467260) (nat_lit 0) A10K2.u4537 from rfl, allE_node, arows4522, irow4538, arows4537]
  all_goals rfl

theorem atot4538 : totK PA10K2 A10K2.u4538 = [3145593256673, 18801419101163, 44177632086877, 51426690356035, 29604486160656, 6562421834077, 464328642018, 6239673734, 0, 0] := by
  rw [show A10K2.u4538 = KTree.node A10K2.u4522 (nat_lit 72352215) (nat_lit 10069467260) (nat_lit 0) A10K2.u4537 from rfl, totK_node, atot4522, atot4537]
  decide +kernel

theorem arows4570 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4570 = true := by
  rw [show A10K2.u4570 = KTree.node A10K2.u4554 (nat_lit 72501814) (nat_lit 6911740774) (nat_lit 0) A10K2.u4569 from rfl, allE_node, arows4554, irow4570, arows4569]
  all_goals rfl

theorem atot4570 : totK PA10K2 A10K2.u4570 = [2809376952634, 20221626621349, 51117200408517, 54178497150523, 22065885841100, 3020193093110, 112183965871, 0, 0, 0] := by
  rw [show A10K2.u4570 = KTree.node A10K2.u4554 (nat_lit 72501814) (nat_lit 6911740774) (nat_lit 0) A10K2.u4569 from rfl, totK_node, atot4554, atot4569]
  decide +kernel

theorem arows4601 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4601 = true := by
  rw [show A10K2.u4601 = KTree.node A10K2.u4585 (nat_lit 72796727) (nat_lit 4571803918) (nat_lit 0) A10K2.u4600 from rfl, allE_node, arows4585, irow4601, arows4600]
  all_goals rfl

theorem atot4601 : totK PA10K2 A10K2.u4601 = [2211027775591, 15699691725145, 43459607103863, 55667067956301, 30457709008773, 6215156994677, 496562176972, 6354482628, 0, 0] := by
  rw [show A10K2.u4601 = KTree.node A10K2.u4585 (nat_lit 72796727) (nat_lit 4571803918) (nat_lit 0) A10K2.u4600 from rfl, totK_node, atot4585, atot4600]
  decide +kernel

theorem arows4636 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4636 = true := by
  rw [show A10K2.u4636 = KTree.node A10K2.u4620 (nat_lit 73137220) (nat_lit 7812393724) (nat_lit 0) A10K2.u4635 from rfl, allE_node, arows4620, irow4636, arows4635]
  all_goals rfl

theorem atot4636 : totK PA10K2 A10K2.u4636 = [2245477168038, 15537286335074, 42558035966463, 55905969537158, 34139911146769, 8080955134970, 597823272756, 7151180950, 0, 0] := by
  rw [show A10K2.u4636 = KTree.node A10K2.u4620 (nat_lit 73137220) (nat_lit 7812393724) (nat_lit 0) A10K2.u4635 from rfl, totK_node, atot4620, atot4635]
  decide +kernel

theorem arows4667 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4667 = true := by
  rw [show A10K2.u4667 = KTree.node A10K2.u4651 (nat_lit 74002425) (nat_lit 5956217181) (nat_lit 0) A10K2.u4666 from rfl, allE_node, arows4651, irow4667, arows4666]
  all_goals rfl

theorem atot4667 : totK PA10K2 A10K2.u4667 = [0, 4769320623747, 26249474070483, 53780929611028, 49288561978846, 19059869421189, 2646796369952, 110980545626, 0, 0] := by
  rw [show A10K2.u4667 = KTree.node A10K2.u4651 (nat_lit 74002425) (nat_lit 5956217181) (nat_lit 0) A10K2.u4666 from rfl, totK_node, atot4651, atot4666]
  decide +kernel

theorem arows4699 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4699 = true := by
  rw [show A10K2.u4699 = KTree.node A10K2.u4683 (nat_lit 74150392) (nat_lit 13299278290) (nat_lit 0) A10K2.u4698 from rfl, allE_node, arows4683, irow4699, arows4698]
  all_goals rfl

theorem atot4699 : totK PA10K2 A10K2.u4699 = [0, 3169975078601, 21602904444682, 52488433306910, 53893952355738, 21774947458588, 2932063673853, 99502968044, 0, 0] := by
  rw [show A10K2.u4699 = KTree.node A10K2.u4683 (nat_lit 74150392) (nat_lit 13299278290) (nat_lit 0) A10K2.u4698 from rfl, totK_node, atot4683, atot4698]
  decide +kernel

theorem arows4730 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4730 = true := by
  rw [show A10K2.u4730 = KTree.node A10K2.u4714 (nat_lit 74361706) (nat_lit 9087513361) (nat_lit 0) A10K2.u4729 from rfl, allE_node, arows4714, irow4730, arows4729]
  all_goals rfl

theorem atot4730 : totK PA10K2 A10K2.u4730 = [0, 1538660793789, 11867049269888, 36120534318823, 53674562553145, 37901321992948, 11031322534415, 1269991605252, 42686146280, 0] := by
  rw [show A10K2.u4730 = KTree.node A10K2.u4714 (nat_lit 74361706) (nat_lit 9087513361) (nat_lit 0) A10K2.u4729 from rfl, totK_node, atot4714, atot4729]
  decide +kernel

theorem arows4763 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4763 = true := by
  rw [show A10K2.u4763 = KTree.node A10K2.u4747 (nat_lit 74572970) (nat_lit 12996709126) (nat_lit 0) A10K2.u4762 from rfl, allE_node, arows4747, irow4763, arows4762]
  all_goals rfl

theorem atot4763 : totK PA10K2 A10K2.u4763 = [0, 4416309415518, 26396483755781, 56096470400438, 48914579823710, 15506944131144, 1701967267790, 49104847499, 0, 0] := by
  rw [show A10K2.u4763 = KTree.node A10K2.u4747 (nat_lit 74572970) (nat_lit 12996709126) (nat_lit 0) A10K2.u4762 from rfl, totK_node, atot4747, atot4762]
  decide +kernel

theorem arows4794 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4794 = true := by
  rw [show A10K2.u4794 = KTree.node A10K2.u4778 (nat_lit 74857228) (nat_lit 11697372202) (nat_lit 0) A10K2.u4793 from rfl, allE_node, arows4778, irow4794, arows4793]
  all_goals rfl

theorem atot4794 : totK PA10K2 A10K2.u4794 = [0, 2207301526707, 15477779799783, 43322630961537, 56349419081598, 29630681382734, 5564712073787, 395224636574, 6354482628, 0] := by
  rw [show A10K2.u4794 = KTree.node A10K2.u4778 (nat_lit 74857228) (nat_lit 11697372202) (nat_lit 0) A10K2.u4793 from rfl, totK_node, atot4778, atot4793]
  decide +kernel

theorem arows4826 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4826 = true := by
  rw [show A10K2.u4826 = KTree.node A10K2.u4810 (nat_lit 75205874) (nat_lit 14394963921) (nat_lit 0) A10K2.u4825 from rfl, allE_node, arows4810, irow4826, arows4825]
  all_goals rfl

theorem atot4826 : totK PA10K2 A10K2.u4826 = [2218643274008, 12869825732274, 31991296580249, 47018014387565, 42240144089522, 18157814329698, 2707373702088, 111757921133, 0, 0] := by
  rw [show A10K2.u4826 = KTree.node A10K2.u4810 (nat_lit 75205874) (nat_lit 14394963921) (nat_lit 0) A10K2.u4825 from rfl, totK_node, atot4810, atot4825]
  decide +kernel

theorem arows4857 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4857 = true := by
  rw [show A10K2.u4857 = KTree.node A10K2.u4841 (nat_lit 75671197) (nat_lit 6061322269) (nat_lit 0) A10K2.u4856 from rfl, allE_node, arows4841, irow4857, arows4856]
  all_goals rfl

theorem atot4857 : totK PA10K2 A10K2.u4857 = [3521849016027, 22612752355984, 52672862974543, 52331682954500, 20362814409381, 2938646015815, 129780370637, 0, 0, 0] := by
  rw [show A10K2.u4857 = KTree.node A10K2.u4841 (nat_lit 75671197) (nat_lit 6061322269) (nat_lit 0) A10K2.u4856 from rfl, totK_node, atot4841, atot4856]
  decide +kernel

theorem arows4891 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4891 = true := by
  rw [show A10K2.u4891 = KTree.node A10K2.u4875 (nat_lit 75901249) (nat_lit 9592270641) (nat_lit 0) A10K2.u4890 from rfl, allE_node, arows4875, irow4891, arows4890]
  all_goals rfl

theorem atot4891 : totK PA10K2 A10K2.u4891 = [848323660542, 8314907743895, 31978278515724, 56172067323852, 42427730971290, 12044178786228, 1285742079217, 41810754621, 0, 0] := by
  rw [show A10K2.u4891 = KTree.node A10K2.u4875 (nat_lit 75901249) (nat_lit 9592270641) (nat_lit 0) A10K2.u4890 from rfl, totK_node, atot4875, atot4890]
  decide +kernel

theorem arows4922 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4922 = true := by
  rw [show A10K2.u4922 = KTree.node A10K2.u4906 (nat_lit 76163754) (nat_lit 12801644120) (nat_lit 0) A10K2.u4921 from rfl, allE_node, arows4906, irow4922, arows4921]
  all_goals rfl

theorem atot4922 : totK PA10K2 A10K2.u4922 = [4904904919556, 28152612440911, 57336918941969, 47978055085268, 14875164314689, 1563015844220, 43558542526, 0, 0, 0] := by
  rw [show A10K2.u4922 = KTree.node A10K2.u4906 (nat_lit 76163754) (nat_lit 12801644120) (nat_lit 0) A10K2.u4921 from rfl, totK_node, atot4906, atot4921]
  decide +kernel

theorem arows4954 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4954 = true := by
  rw [show A10K2.u4954 = KTree.node A10K2.u4938 (nat_lit 76400276) (nat_lit 12027339891) (nat_lit 0) A10K2.u4953 from rfl, allE_node, arows4938, irow4954, arows4953]
  all_goals rfl

theorem atot4954 : totK PA10K2 A10K2.u4954 = [0, 5617007981719, 30455322016027, 58179954092383, 45137867111615, 12889750357855, 1352109789221, 42943767608, 0, 0] := by
  rw [show A10K2.u4954 = KTree.node A10K2.u4938 (nat_lit 76400276) (nat_lit 12027339891) (nat_lit 0) A10K2.u4953 from rfl, totK_node, atot4938, atot4953]
  decide +kernel

theorem arows4985 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4985 = true := by
  rw [show A10K2.u4985 = KTree.node A10K2.u4969 (nat_lit 76596380) (nat_lit 11709940717) (nat_lit 0) A10K2.u4984 from rfl, allE_node, arows4969, irow4985, arows4984]
  all_goals rfl

theorem atot4985 : totK PA10K2 A10K2.u4985 = [4097868149106, 23817243566374, 51599085170251, 50166398317998, 20926225389457, 3366370743980, 160786893662, 0, 0, 0] := by
  rw [show A10K2.u4985 = KTree.node A10K2.u4969 (nat_lit 76596380) (nat_lit 11709940717) (nat_lit 0) A10K2.u4984 from rfl, totK_node, atot4969, atot4984]
  decide +kernel

theorem arows5018 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5018 = true := by
  rw [show A10K2.u5018 = KTree.node A10K2.u5002 (nat_lit 76810524) (nat_lit 11914173453) (nat_lit 0) A10K2.u5017 from rfl, allE_node, arows5002, irow5018, arows5017]
  all_goals rfl

theorem atot5018 : totK PA10K2 A10K2.u5018 = [2343832716771, 18387604577653, 49620971131728, 55402177085735, 23669929590361, 3374932876728, 119764869613, 0, 0, 0] := by
  rw [show A10K2.u5018 = KTree.node A10K2.u5002 (nat_lit 76810524) (nat_lit 11914173453) (nat_lit 0) A10K2.u5017 from rfl, totK_node, atot5002, atot5017]
  decide +kernel

theorem arows5049 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5049 = true := by
  rw [show A10K2.u5049 = KTree.node A10K2.u5033 (nat_lit 77613602) (nat_lit 8677873280) (nat_lit 0) A10K2.u5048 from rfl, allE_node, arows5033, irow5049, arows5048]
  all_goals rfl

theorem atot5049 : totK PA10K2 A10K2.u5049 = [0, 5426356727069, 29693175394134, 57575502727534, 44885648485303, 13039797433951, 1422651993155, 42551283831, 0, 0] := by
  rw [show A10K2.u5049 = KTree.node A10K2.u5033 (nat_lit 77613602) (nat_lit 8677873280) (nat_lit 0) A10K2.u5048 from rfl, totK_node, atot5033, atot5048]
  decide +kernel

theorem arows5081 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5081 = true := by
  rw [show A10K2.u5081 = KTree.node A10K2.u5065 (nat_lit 77851866) (nat_lit 13957107525) (nat_lit 0) A10K2.u5080 from rfl, allE_node, arows5065, irow5081, arows5080]
  all_goals rfl

theorem atot5081 : totK PA10K2 A10K2.u5081 = [0, 4399763307348, 26176480755898, 55833430790281, 49866760261980, 16619654755531, 1838712174632, 50463470790, 0, 0] := by
  rw [show A10K2.u5081 = KTree.node A10K2.u5065 (nat_lit 77851866) (nat_lit 13957107525) (nat_lit 0) A10K2.u5080 from rfl, totK_node, atot5065, atot5080]
  decide +kernel

theorem arows5112 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5112 = true := by
  rw [show A10K2.u5112 = KTree.node A10K2.u5096 (nat_lit 78341987) (nat_lit 9278030917) (nat_lit 0) A10K2.u5111 from rfl, allE_node, arows5096, irow5112, arows5111]
  all_goals rfl

theorem atot5112 : totK PA10K2 A10K2.u5112 = [0, 5291314195817, 29377809294681, 57869436423998, 46486944619445, 13854793690131, 1454748878229, 43622386450, 0, 0] := by
  rw [show A10K2.u5112 = KTree.node A10K2.u5096 (nat_lit 78341987) (nat_lit 9278030917) (nat_lit 0) A10K2.u5111 from rfl, totK_node, atot5096, atot5111]
  decide +kernel

theorem arows5148 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5148 = true := by
  rw [show A10K2.u5148 = KTree.node A10K2.u5132 (nat_lit 78764909) (nat_lit 6121173289) (nat_lit 0) A10K2.u5147 from rfl, allE_node, arows5132, irow5148, arows5147]
  all_goals rfl

theorem atot5148 : totK PA10K2 A10K2.u5148 = [0, 4381329944251, 26365811409717, 56390335452468, 48882831969685, 14728312184381, 1553563436414, 48669785306, 0, 0] := by
  rw [show A10K2.u5148 = KTree.node A10K2.u5132 (nat_lit 78764909) (nat_lit 6121173289) (nat_lit 0) A10K2.u5147 from rfl, totK_node, atot5132, atot5147]
  decide +kernel

theorem arows5179 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5179 = true := by
  rw [show A10K2.u5179 = KTree.node A10K2.u5163 (nat_lit 79049943) (nat_lit 10646932672) (nat_lit 0) A10K2.u5178 from rfl, allE_node, arows5163, irow5179, arows5178]
  all_goals rfl

theorem atot5179 : totK PA10K2 A10K2.u5179 = [0, 2338692983822, 15588548323902, 42370579838635, 54429480593459, 29110973655126, 6235319284776, 520156118015, 6354482628, 0] := by
  rw [show A10K2.u5179 = KTree.node A10K2.u5163 (nat_lit 79049943) (nat_lit 10646932672) (nat_lit 0) A10K2.u5178 from rfl, totK_node, atot5163, atot5178]
  decide +kernel

theorem arows5211 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5211 = true := by
  rw [show A10K2.u5211 = KTree.node A10K2.u5195 (nat_lit 84039902) (nat_lit 4930477214) (nat_lit 0) A10K2.u5210 from rfl, allE_node, arows5195, irow5211, arows5210]
  all_goals rfl

theorem atot5211 : totK PA10K2 A10K2.u5211 = [0, 3944858961693, 24910088483432, 55557221853994, 51094016041968, 17306035810370, 1880848393674, 49456212095, 0, 0] := by
  rw [show A10K2.u5211 = KTree.node A10K2.u5195 (nat_lit 84039902) (nat_lit 4930477214) (nat_lit 0) A10K2.u5210 from rfl, totK_node, atot5195, atot5210]
  decide +kernel

theorem arows5242 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5242 = true := by
  rw [show A10K2.u5242 = KTree.node A10K2.u5226 (nat_lit 84199998) (nat_lit 9907311621) (nat_lit 0) A10K2.u5241 from rfl, allE_node, arows5226, irow5242, arows5241]
  all_goals rfl

theorem atot5242 : totK PA10K2 A10K2.u5242 = [0, 0, 5993709345767, 31604468038046, 58577176173273, 43330019154096, 11924212469593, 1269663260726, 41810754621, 0] := by
  rw [show A10K2.u5242 = KTree.node A10K2.u5226 (nat_lit 84199998) (nat_lit 9907311621) (nat_lit 0) A10K2.u5241 from rfl, totK_node, atot5226, atot5241]
  decide +kernel

theorem arows5275 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5275 = true := by
  rw [show A10K2.u5275 = KTree.node A10K2.u5259 (nat_lit 84983859) (nat_lit 1731411916) (nat_lit 0) A10K2.u5274 from rfl, allE_node, arows5259, irow5275, arows5274]
  all_goals rfl

theorem atot5275 : totK PA10K2 A10K2.u5275 = [0, 4460364782831, 24993802059923, 52430971855491, 49593548913226, 20134968528830, 2988677271361, 135255041420, 0, 0] := by
  rw [show A10K2.u5275 = KTree.node A10K2.u5259 (nat_lit 84983859) (nat_lit 1731411916) (nat_lit 0) A10K2.u5274 from rfl, totK_node, atot5259, atot5274]
  decide +kernel

theorem arows5306 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5306 = true := by
  rw [show A10K2.u5306 = KTree.node A10K2.u5290 (nat_lit 85215331) (nat_lit 5228788251) (nat_lit 0) A10K2.u5305 from rfl, allE_node, arows5290, irow5306, arows5305]
  all_goals rfl

theorem atot5306 : totK PA10K2 A10K2.u5306 = [0, 1491872713986, 15560850351309, 48130851071674, 58152194258766, 25496864327789, 3617189417681, 149266064841, 0, 0] := by
  rw [show A10K2.u5306 = KTree.node A10K2.u5290 (nat_lit 85215331) (nat_lit 5228788251) (nat_lit 0) A10K2.u5305 from rfl, totK_node, atot5290, atot5305]
  decide +kernel

theorem arows5338 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5338 = true := by
  rw [show A10K2.u5338 = KTree.node A10K2.u5322 (nat_lit 85495852) (nat_lit 12040938746) (nat_lit 0) A10K2.u5337 from rfl, allE_node, arows5322, irow5338, arows5337]
  all_goals rfl

theorem atot5338 : totK PA10K2 A10K2.u5338 = [0, 4449301618478, 23900803239130, 49304785690363, 48978570096698, 23536569773282, 4945882650133, 428064293330, 6354482628, 0] := by
  rw [show A10K2.u5338 = KTree.node A10K2.u5322 (nat_lit 85495852) (nat_lit 12040938746) (nat_lit 0) A10K2.u5337 from rfl, totK_node, atot5322, atot5337]
  decide +kernel

theorem arows5369 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5369 = true := by
  rw [show A10K2.u5369 = KTree.node A10K2.u5353 (nat_lit 85770308) (nat_lit 11552108224) (nat_lit 0) A10K2.u5368 from rfl, allE_node, arows5353, irow5369, arows5368]
  all_goals rfl

theorem atot5369 : totK PA10K2 A10K2.u5369 = [0, 1600415090483, 13170249695892, 40505405746571, 57370649692402, 36005969852345, 8168289866396, 605353180972, 7007974415, 0] := by
  rw [show A10K2.u5369 = KTree.node A10K2.u5353 (nat_lit 85770308) (nat_lit 11552108224) (nat_lit 0) A10K2.u5368 from rfl, totK_node, atot5353, atot5368]
  decide +kernel

theorem arows5403 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5403 = true := by
  rw [show A10K2.u5403 = KTree.node A10K2.u5387 (nat_lit 88753932) (nat_lit 11723843175) (nat_lit 0) A10K2.u5402 from rfl, allE_node, arows5387, irow5403, arows5402]
  all_goals rfl

theorem atot5403 : totK PA10K2 A10K2.u5403 = [0, 4694095374265, 27114419327380, 56495277429925, 49266724314237, 16007247872175, 1664830511838, 43558542526, 0, 0] := by
  rw [show A10K2.u5403 = KTree.node A10K2.u5387 (nat_lit 88753932) (nat_lit 11723843175) (nat_lit 0) A10K2.u5402 from rfl, totK_node, atot5387, atot5402]
  decide +kernel

theorem arows5434 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5434 = true := by
  rw [show A10K2.u5434 = KTree.node A10K2.u5418 (nat_lit 88980306) (nat_lit 13679011852) (nat_lit 0) A10K2.u5433 from rfl, allE_node, arows5418, irow5434, arows5433]
  all_goals rfl

theorem atot5434 : totK PA10K2 A10K2.u5434 = [0, 0, 5544930934375, 30501960475552, 58863163478262, 45076636220281, 12518744315692, 1310374008815, 42943767608, 0] := by
  rw [show A10K2.u5434 = KTree.node A10K2.u5418 (nat_lit 88980306) (nat_lit 13679011852) (nat_lit 0) A10K2.u5433 from rfl, totK_node, atot5418, atot5433]
  decide +kernel

theorem arows5466 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5466 = true := by
  rw [show A10K2.u5466 = KTree.node A10K2.u5450 (nat_lit 89180379) (nat_lit 8800321746) (nat_lit 0) A10K2.u5465 from rfl, allE_node, arows5450, irow5466, arows5465]
  all_goals rfl

theorem atot5466 : totK PA10K2 A10K2.u5466 = [0, 3700397019841, 22633091085792, 51509298373830, 51912137000022, 21928910086445, 3330910036779, 147561047426, 0, 0] := by
  rw [show A10K2.u5466 = KTree.node A10K2.u5450 (nat_lit 89180379) (nat_lit 8800321746) (nat_lit 0) A10K2.u5465 from rfl, totK_node, atot5450, atot5465]
  decide +kernel

theorem arows5497 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5497 = true := by
  rw [show A10K2.u5497 = KTree.node A10K2.u5481 (nat_lit 89397418) (nat_lit 11094131561) (nat_lit 0) A10K2.u5496 from rfl, allE_node, arows5481, irow5497, arows5496]
  all_goals rfl

theorem atot5497 : totK PA10K2 A10K2.u5497 = [0, 2254573189466, 17802189035045, 48658400214072, 55855959298434, 24664282734069, 3573438294810, 149375459184, 0, 0] := by
  rw [show A10K2.u5497 = KTree.node A10K2.u5481 (nat_lit 89397418) (nat_lit 11094131561) (nat_lit 0) A10K2.u5496 from rfl, totK_node, atot5481, atot5496]
  decide +kernel

theorem arows5530 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5530 = true := by
  rw [show A10K2.u5530 = KTree.node A10K2.u5514 (nat_lit 89751099) (nat_lit 5767473894) (nat_lit 0) A10K2.u5529 from rfl, allE_node, arows5514, irow5530, arows5529]
  all_goals rfl

theorem atot5530 : totK PA10K2 A10K2.u5530 = [0, 4456504943629, 24317273772026, 50236713061455, 48914020060060, 22740838017506, 4713252886637, 422166623761, 6354482628, 0] := by
  rw [show A10K2.u5530 = KTree.node A10K2.u5514 (nat_lit 89751099) (nat_lit 5767473894) (nat_lit 0) A10K2.u5529 from rfl, totK_node, atot5514, atot5529]
  decide +kernel

theorem arows5561 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5561 = true := by
  rw [show A10K2.u5561 = KTree.node A10K2.u5545 (nat_lit 90023763) (nat_lit 10374073118) (nat_lit 0) A10K2.u5560 from rfl, allE_node, arows5545, irow5561, arows5560]
  all_goals rfl

theorem atot5561 : totK PA10K2 A10K2.u5561 = [0, 1137674346764, 11034015788044, 38696656239188, 59587027725610, 38533064851355, 8708298427976, 617600190911, 7151180950, 0] := by
  rw [show A10K2.u5561 = KTree.node A10K2.u5545 (nat_lit 90023763) (nat_lit 10374073118) (nat_lit 0) A10K2.u5560 from rfl, totK_node, atot5545, atot5560]
  decide +kernel

theorem arows5593 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5593 = true := by
  rw [show A10K2.u5593 = KTree.node A10K2.u5577 (nat_lit 92420195) (nat_lit 5302590974) (nat_lit 0) A10K2.u5592 from rfl, allE_node, arows5577, irow5593, arows5592]
  all_goals rfl

theorem atot5593 : totK PA10K2 A10K2.u5593 = [0, 4602817943271, 26978278905326, 56405192315298, 48696999462170, 15693636835510, 1733656383935, 49456212095, 0, 0] := by
  rw [show A10K2.u5593 = KTree.node A10K2.u5577 (nat_lit 92420195) (nat_lit 5302590974) (nat_lit 0) A10K2.u5592 from rfl, totK_node, atot5577, atot5592]
  decide +kernel

theorem arows5624 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5624 = true := by
  rw [show A10K2.u5624 = KTree.node A10K2.u5608 (nat_lit 92668366) (nat_lit 14397836211) (nat_lit 0) A10K2.u5623 from rfl, allE_node, arows5608, irow5624, arows5623]
  all_goals rfl

theorem atot5624 : totK PA10K2 A10K2.u5624 = [0, 0, 6324202498098, 33270396128068, 60104203761171, 41493651325876, 10453485760083, 1090052490145, 41810754621, 0] := by
  rw [show A10K2.u5624 = KTree.node A10K2.u5608 (nat_lit 92668366) (nat_lit 14397836211) (nat_lit 0) A10K2.u5623 from rfl, totK_node, atot5608, atot5623]
  decide +kernel

theorem arows5659 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5659 = true := by
  rw [show A10K2.u5659 = KTree.node A10K2.u5643 (nat_lit 92930510) (nat_lit 13016981987) (nat_lit 0) A10K2.u5658 from rfl, allE_node, arows5643, irow5659, arows5658]
  all_goals rfl

theorem atot5659 : totK PA10K2 A10K2.u5659 = [0, 5445304759573, 29031649679493, 56289160075007, 46617396357413, 15088895681251, 1731966609021, 50411890534, 0, 0] := by
  rw [show A10K2.u5659 = KTree.node A10K2.u5643 (nat_lit 92930510) (nat_lit 13016981987) (nat_lit 0) A10K2.u5658 from rfl, totK_node, atot5643, atot5658]
  decide +kernel

theorem arows5690 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5690 = true := by
  rw [show A10K2.u5690 = KTree.node A10K2.u5674 (nat_lit 93173214) (nat_lit 12719699711) (nat_lit 2) A10K2.u5689 from rfl, allE_node, arows5674, irow5690, arows5689]
  all_goals rfl

theorem atot5690 : totK PA10K2 A10K2.u5690 = [0, 307923820525, 7829232066263, 35047358299937, 59679599597962, 40647594385279, 9752186596689, 926242433509, 36704093874, 0] := by
  rw [show A10K2.u5690 = KTree.node A10K2.u5674 (nat_lit 93173214) (nat_lit 12719699711) (nat_lit 2) A10K2.u5689 from rfl, totK_node, atot5674, atot5689]
  decide +kernel

theorem arows5722 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5722 = true := by
  rw [show A10K2.u5722 = KTree.node A10K2.u5706 (nat_lit 93372698) (nat_lit 10808391808) (nat_lit 0) A10K2.u5721 from rfl, allE_node, arows5706, irow5722, arows5721]
  all_goals rfl

theorem atot5722 : totK PA10K2 A10K2.u5722 = [0, 4097868149106, 24000812394019, 52081185668202, 49693589476009, 19955149142943, 3410626502982, 296538115923, 6239673734, 0] := by
  rw [show A10K2.u5722 = KTree.node A10K2.u5706 (nat_lit 93372698) (nat_lit 10808391808) (nat_lit 0) A10K2.u5721 from rfl, totK_node, atot5706, atot5721]
  decide +kernel

theorem arows5753 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5753 = true := by
  rw [show A10K2.u5753 = KTree.node A10K2.u5737 (nat_lit 93586274) (nat_lit 8467094194) (nat_lit 0) A10K2.u5752 from rfl, allE_node, arows5737, irow5753, arows5752]
  all_goals rfl

theorem atot5753 : totK PA10K2 A10K2.u5753 = [0, 2343832716771, 18490689706139, 49612646784653, 55282347282453, 23191895790791, 3109046119426, 125886042902, 0, 0] := by
  rw [show A10K2.u5753 = KTree.node A10K2.u5737 (nat_lit 93586274) (nat_lit 8467094194) (nat_lit 0) A10K2.u5752 from rfl, totK_node, atot5737, atot5752]
  decide +kernel

theorem arows5786 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5786 = true := by
  rw [show A10K2.u5786 = KTree.node A10K2.u5770 (nat_lit 94390560) (nat_lit 12911195160) (nat_lit 0) A10K2.u5785 from rfl, allE_node, arows5770, irow5786, arows5785]
  all_goals rfl

theorem atot5786 : totK PA10K2 A10K2.u5786 = [0, 0, 5839277451348, 31010873843111, 58337456625802, 43276861198225, 11680419570961, 1250341424071, 42551283831, 0] := by
  rw [show A10K2.u5786 = KTree.node A10K2.u5770 (nat_lit 94390560) (nat_lit 12911195160) (nat_lit 0) A10K2.u5785 from rfl, totK_node, atot5770, atot5785]
  decide +kernel

theorem arows5817 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5817 = true := by
  rw [show A10K2.u5817 = KTree.node A10K2.u5801 (nat_lit 94980353) (nat_lit 9573235790) (nat_lit 0) A10K2.u5816 from rfl, allE_node, arows5801, irow5817, arows5816]
  all_goals rfl

theorem atot5817 : totK PA10K2 A10K2.u5817 = [0, 0, 5730667843837, 30939745937924, 58776644820917, 44713438057925, 12198673350409, 1280348151661, 43558542526, 0] := by
  rw [show A10K2.u5817 = KTree.node A10K2.u5801 (nat_lit 94980353) (nat_lit 9573235790) (nat_lit 0) A10K2.u5816 from rfl, totK_node, atot5801, atot5816]
  decide +kernel

theorem arows5849 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5849 = true := by
  rw [show A10K2.u5849 = KTree.node A10K2.u5833 (nat_lit 95439408) (nat_lit 14029909380) (nat_lit 0) A10K2.u5848 from rfl, allE_node, arows5833, irow5849, arows5848]
  all_goals rfl

theorem atot5849 : totK PA10K2 A10K2.u5849 = [0, 0, 5559866915403, 30865417750739, 59105077708802, 44386606369231, 11647233631636, 1249564312282, 42121665971, 0] := by
  rw [show A10K2.u5849 = KTree.node A10K2.u5833 (nat_lit 95439408) (nat_lit 14029909380) (nat_lit 0) A10K2.u5848 from rfl, totK_node, atot5833, atot5848]
  decide +kernel

theorem arows5880 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5880 = true := by
  rw [show A10K2.u5880 = KTree.node A10K2.u5864 (nat_lit 95594652) (nat_lit 11843298650) (nat_lit 0) A10K2.u5879 from rfl, allE_node, arows5864, irow5880, arows5879]
  all_goals rfl

theorem atot5880 : totK PA10K2 A10K2.u5880 = [0, 0, 2317656958010, 19069255693595, 51481348644412, 54449245217407, 20285274203934, 2878929742727, 117238706253, 0] := by
  rw [show A10K2.u5880 = KTree.node A10K2.u5864 (nat_lit 95594652) (nat_lit 11843298650) (nat_lit 0) A10K2.u5879 from rfl, totK_node, atot5864, atot5879]
  decide +kernel

theorem arows5914 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5914 = true := by
  rw [show A10K2.u5914 = KTree.node A10K2.u5898 (nat_lit 100679970) (nat_lit 10554115919) (nat_lit 0) A10K2.u5913 from rfl, allE_node, arows5898, irow5914, arows5913]
  all_goals rfl

theorem atot5914 : totK PA10K2 A10K2.u5914 = [3386414442111, 18026221388052, 34308312966675, 29590946153259, 20627574199414, 24055223662623, 16510288350858, 4491975057858, 446040892095, 6354482628] := by
  rw [show A10K2.u5914 = KTree.node A10K2.u5898 (nat_lit 100679970) (nat_lit 10554115919) (nat_lit 0) A10K2.u5913 from rfl, totK_node, atot5898, atot5913]
  decide +kernel

theorem arows5945 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5945 = true := by
  rw [show A10K2.u5945 = KTree.node A10K2.u5929 (nat_lit 100893524) (nat_lit 10198437919) (nat_lit 0) A10K2.u5944 from rfl, allE_node, arows5929, irow5945, arows5944]
  all_goals rfl

theorem atot5945 : totK PA10K2 A10K2.u5945 = [2910957610618, 19883903640376, 50126494603630, 55099945402775, 24556400016530, 3789754734269, 152984430168, 0, 0, 0] := by
  rw [show A10K2.u5945 = KTree.node A10K2.u5929 (nat_lit 100893524) (nat_lit 10198437919) (nat_lit 0) A10K2.u5944 from rfl, totK_node, atot5929, atot5944]
  decide +kernel

theorem arows5977 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5977 = true := by
  rw [show A10K2.u5977 = KTree.node A10K2.u5961 (nat_lit 101107974) (nat_lit 8520166951) (nat_lit 0) A10K2.u5976 from rfl, allE_node, arows5961, irow5977, arows5976]
  all_goals rfl

theorem atot5977 : totK PA10K2 A10K2.u5977 = [2182481654920, 13497726475691, 35883147936234, 51514375655413, 38050769379201, 11334826972373, 1253074252018, 41810754621, 0, 0] := by
  rw [show A10K2.u5977 = KTree.node A10K2.u5961 (nat_lit 101107974) (nat_lit 8520166951) (nat_lit 0) A10K2.u5976 from rfl, totK_node, atot5961, atot5976]
  decide +kernel

theorem arows6008 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6008 = true := by
  rw [show A10K2.u6008 = KTree.node A10K2.u5992 (nat_lit 101876208) (nat_lit 14112702326) (nat_lit 0) A10K2.u6007 from rfl, allE_node, arows5992, irow6008, arows6007]
  all_goals rfl

theorem atot6008 : totK PA10K2 A10K2.u6008 = [2147550714988, 18084270973582, 50204532661550, 56458486098367, 23456963710471, 3180471549413, 116652364880, 0, 0, 0] := by
  rw [show A10K2.u6008 = KTree.node A10K2.u5992 (nat_lit 101876208) (nat_lit 14112702326) (nat_lit 0) A10K2.u6007 from rfl, totK_node, atot5992, atot6007]
  decide +kernel

theorem arows6041 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6041 = true := by
  rw [show A10K2.u6041 = KTree.node A10K2.u6025 (nat_lit 102264753) (nat_lit 8957444479) (nat_lit 0) A10K2.u6040 from rfl, allE_node, arows6025, irow6041, arows6040]
  all_goals rfl

theorem atot6041 : totK PA10K2 A10K2.u6041 = [3783711115774, 21701847755553, 48190402210703, 50830745048303, 24981269685269, 5203403849411, 452162809752, 6354482628, 0, 0] := by
  rw [show A10K2.u6041 = KTree.node A10K2.u6025 (nat_lit 102264753) (nat_lit 8957444479) (nat_lit 0) A10K2.u6040 from rfl, totK_node, atot6025, atot6040]
  decide +kernel

theorem arows6072 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6072 = true := by
  rw [show A10K2.u6072 = KTree.node A10K2.u6056 (nat_lit 102480050) (nat_lit 15024473055) (nat_lit 0) A10K2.u6071 from rfl, allE_node, arows6056, irow6072, arows6071]
  all_goals rfl

theorem atot6072 : totK PA10K2 A10K2.u6072 = [2346766361561, 16309621786845, 43827956285278, 55561911402026, 32188026492710, 7220586639872, 544817429173, 7007974415, 0, 0] := by
  rw [show A10K2.u6072 = KTree.node A10K2.u6056 (nat_lit 102480050) (nat_lit 15024473055) (nat_lit 0) A10K2.u6071 from rfl, totK_node, atot6056, atot6071]
  decide +kernel

theorem arows6104 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6104 = true := by
  rw [show A10K2.u6104 = KTree.node A10K2.u6088 (nat_lit 102708885) (nat_lit 6319730315) (nat_lit 0) A10K2.u6103 from rfl, allE_node, arows6088, irow6104, arows6103]
  all_goals rfl

theorem atot6104 : totK PA10K2 A10K2.u6104 = [0, 5113788092859, 27844977167334, 56246259547835, 50135949310073, 18048331657473, 2242273371953, 80927666678, 0, 0] := by
  rw [show A10K2.u6104 = KTree.node A10K2.u6088 (nat_lit 102708885) (nat_lit 6319730315) (nat_lit 0) A10K2.u6103 from rfl, totK_node, atot6088, atot6103]
  decide +kernel

theorem arows6135 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6135 = true := by
  rw [show A10K2.u6135 = KTree.node A10K2.u6119 (nat_lit 102907918) (nat_lit 12664857130) (nat_lit 0) A10K2.u6134 from rfl, allE_node, arows6119, irow6135, arows6134]
  all_goals rfl

theorem atot6135 : totK PA10K2 A10K2.u6135 = [0, 5133598015609, 28985067944789, 58035857278192, 47180938208811, 13726175847776, 1365899000334, 42173223013, 0, 0] := by
  rw [show A10K2.u6135 = KTree.node A10K2.u6119 (nat_lit 102907918) (nat_lit 12664857130) (nat_lit 0) A10K2.u6134 from rfl, totK_node, atot6119, atot6134]
  decide +kernel

theorem arows6172 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6172 = true := by
  rw [show A10K2.u6172 = KTree.node A10K2.u6156 (nat_lit 103059922) (nat_lit 5211368906) (nat_lit 0) A10K2.u6171 from rfl, allE_node, arows6156, irow6172, arows6171]
  all_goals rfl

theorem atot6172 : totK PA10K2 A10K2.u6172 = [0, 0, 6176293473508, 32070182170591, 58497288185791, 42368413831423, 11610893548012, 1261727118509, 41810754621, 0] := by
  rw [show A10K2.u6172 = KTree.node A10K2.u6156 (nat_lit 103059922) (nat_lit 5211368906) (nat_lit 0) A10K2.u6171 from rfl, totK_node, atot6156, atot6171]
  decide +kernel

theorem arows6203 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6203 = true := by
  rw [show A10K2.u6203 = KTree.node A10K2.u6187 (nat_lit 103846798) (nat_lit 13329368796) (nat_lit 0) A10K2.u6202 from rfl, allE_node, arows6187, irow6203, arows6202]
  all_goals rfl

theorem atot6203 : totK PA10K2 A10K2.u6203 = [0, 4326372242041, 26013771408322, 55551617216614, 49480337358614, 17156644109278, 2207898596268, 91758405390, 0, 0] := by
  rw [show A10K2.u6203 = KTree.node A10K2.u6187 (nat_lit 103846798) (nat_lit 13329368796) (nat_lit 0) A10K2.u6202 from rfl, totK_node, atot6187, atot6202]
  decide +kernel

theorem arows6235 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6235 = true := by
  rw [show A10K2.u6235 = KTree.node A10K2.u6219 (nat_lit 104224981) (nat_lit 6365199804) (nat_lit 0) A10K2.u6234 from rfl, allE_node, arows6219, irow6235, arows6234]
  all_goals rfl

theorem atot6235 : totK PA10K2 A10K2.u6235 = [0, 2176975535692, 15407289331332, 43396229096050, 56023886411435, 29255883114371, 5684171151622, 384857736009, 5976421810, 0] := by
  rw [show A10K2.u6235 = KTree.node A10K2.u6219 (nat_lit 104224981) (nat_lit 6365199804) (nat_lit 0) A10K2.u6234 from rfl, totK_node, atot6219, atot6234]
  decide +kernel

theorem arows6266 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6266 = true := by
  rw [show A10K2.u6266 = KTree.node A10K2.u6250 (nat_lit 104539569) (nat_lit 7031376947) (nat_lit 0) A10K2.u6265 from rfl, allE_node, arows6250, irow6266, arows6265]
  all_goals rfl

theorem atot6266 : totK PA10K2 A10K2.u6266 = [872244600920, 7361864145878, 27756923617966, 53613090243265, 49473516671945, 18572932591128, 2369506925568, 82162263184, 0, 0] := by
  rw [show A10K2.u6266 = KTree.node A10K2.u6250 (nat_lit 104539569) (nat_lit 7031376947) (nat_lit 0) A10K2.u6265 from rfl, totK_node, atot6250, atot6265]
  decide +kernel

theorem arows6299 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6299 = true := by
  rw [show A10K2.u6299 = KTree.node A10K2.u6283 (nat_lit 105524069) (nat_lit 7244940457) (nat_lit 0) A10K2.u6298 from rfl, allE_node, arows6283, irow6299, arows6298]
  all_goals rfl

theorem atot6299 : totK PA10K2 A10K2.u6299 = [5435849402524, 29669300729448, 57744500842377, 46500725363097, 14150540918366, 1502759020831, 43558542526, 0, 0, 0] := by
  rw [show A10K2.u6299 = KTree.node A10K2.u6283 (nat_lit 105524069) (nat_lit 7244940457) (nat_lit 0) A10K2.u6298 from rfl, totK_node, atot6283, atot6298]
  decide +kernel

theorem arows6330 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6330 = true := by
  rw [show A10K2.u6330 = KTree.node A10K2.u6314 (nat_lit 105738233) (nat_lit 6060080622) (nat_lit 0) A10K2.u6329 from rfl, allE_node, arows6314, irow6330, arows6329]
  all_goals rfl

theorem atot6330 : totK PA10K2 A10K2.u6330 = [0, 6738169102206, 34285786481529, 60041006104304, 41934135020824, 11013225285589, 1100979723512, 36704093874, 0, 0] := by
  rw [show A10K2.u6330 = KTree.node A10K2.u6314 (nat_lit 105738233) (nat_lit 6060080622) (nat_lit 0) A10K2.u6329 from rfl, totK_node, atot6314, atot6329]
  decide +kernel

theorem arows6362 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6362 = true := by
  rw [show A10K2.u6362 = KTree.node A10K2.u6346 (nat_lit 105992548) (nat_lit 13775768551) (nat_lit 0) A10K2.u6361 from rfl, allE_node, arows6346, irow6362, arows6361]
  all_goals rfl

theorem atot6362 : totK PA10K2 A10K2.u6362 = [4030358326188, 22399254695083, 47955158320919, 50022197804030, 25711337673824, 5447694650067, 396595521994, 6239673734, 0, 0] := by
  rw [show A10K2.u6362 = KTree.node A10K2.u6346 (nat_lit 105992548) (nat_lit 13775768551) (nat_lit 0) A10K2.u6361 from rfl, totK_node, atot6346, atot6361]
  decide +kernel

theorem arows6393 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6393 = true := by
  rw [show A10K2.u6393 = KTree.node A10K2.u6377 (nat_lit 106302293) (nat_lit 6811788603) (nat_lit 0) A10K2.u6392 from rfl, allE_node, arows6377, irow6393, arows6392]
  all_goals rfl

theorem atot6393 : totK PA10K2 A10K2.u6393 = [1909450982194, 15073076881313, 43393855980764, 55704699287617, 30445505469992, 6281997187176, 497165173552, 6354482628, 0, 0] := by
  rw [show A10K2.u6393 = KTree.node A10K2.u6377 (nat_lit 106302293) (nat_lit 6811788603) (nat_lit 0) A10K2.u6392 from rfl, totK_node, atot6377, atot6392]
  decide +kernel

theorem arows6427 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6427 = true := by
  rw [show A10K2.u6427 = KTree.node A10K2.u6411 (nat_lit 106541000) (nat_lit 6350043420) (nat_lit 0) A10K2.u6426 from rfl, allE_node, arows6411, irow6427, arows6426]
  all_goals rfl

theorem atot6427 : totK PA10K2 A10K2.u6427 = [4530211197570, 26639464366657, 56461138413313, 50819827221688, 17873786139815, 2184125617879, 74759484392, 0, 0, 0] := by
  rw [show A10K2.u6427 = KTree.node A10K2.u6411 (nat_lit 106541000) (nat_lit 6350043420) (nat_lit 0) A10K2.u6426 from rfl, totK_node, atot6411, atot6426]
  decide +kernel

theorem arows6458 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6458 = true := by
  rw [show A10K2.u6458 = KTree.node A10K2.u6442 (nat_lit 106753637) (nat_lit 2821650472) (nat_lit 0) A10K2.u6457 from rfl, allE_node, arows6442, irow6458, arows6457]
  all_goals rfl

theorem atot6458 : totK PA10K2 A10K2.u6458 = [0, 6154539631565, 32399474097268, 60360884714134, 46089125343713, 12805156184313, 1081143422832, 14159155365, 0, 0] := by
  rw [show A10K2.u6458 = KTree.node A10K2.u6442 (nat_lit 106753637) (nat_lit 2821650472) (nat_lit 0) A10K2.u6457 from rfl, totK_node, atot6442, atot6457]
  decide +kernel

theorem arows6490 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6490 = true := by
  rw [show A10K2.u6490 = KTree.node A10K2.u6474 (nat_lit 107556562) (nat_lit 15347524877) (nat_lit 0) A10K2.u6489 from rfl, allE_node, arows6474, irow6490, arows6489]
  all_goals rfl

theorem atot6490 : totK PA10K2 A10K2.u6490 = [0, 4648355096662, 25908293907424, 53762732776131, 49786331841021, 19196305924459, 2646796369952, 110980545626, 0, 0] := by
  rw [show A10K2.u6490 = KTree.node A10K2.u6474 (nat_lit 107556562) (nat_lit 15347524877) (nat_lit 0) A10K2.u6489 from rfl, totK_node, atot6474, atot6489]
  decide +kernel

theorem arows6521 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6521 = true := by
  rw [show A10K2.u6521 = KTree.node A10K2.u6505 (nat_lit 107705096) (nat_lit 11838067159) (nat_lit 0) A10K2.u6520 from rfl, allE_node, arows6505, irow6521, arows6520]
  all_goals rfl

theorem atot6521 : totK PA10K2 A10K2.u6521 = [0, 3239735825263, 22063415424342, 53287331004297, 53935913906099, 21131180534156, 2723989659208, 92540225693, 0, 0] := by
  rw [show A10K2.u6521 = KTree.node A10K2.u6505 (nat_lit 107705096) (nat_lit 11838067159) (nat_lit 0) A10K2.u6520 from rfl, totK_node, atot6505, atot6520]
  decide +kernel

theorem arows6554 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6554 = true := by
  rw [show A10K2.u6554 = KTree.node A10K2.u6538 (nat_lit 107921453) (nat_lit 6466289309) (nat_lit 0) A10K2.u6553 from rfl, allE_node, arows6538, irow6554, arows6553]
  all_goals rfl

theorem atot6554 : totK PA10K2 A10K2.u6554 = [0, 2187980212392, 13697020020678, 36287589644282, 51502962269348, 37580632608448, 11185874541555, 1276954347603, 42686146280, 0] := by
  rw [show A10K2.u6554 = KTree.node A10K2.u6538 (nat_lit 107921453) (nat_lit 6466289309) (nat_lit 0) A10K2.u6553 from rfl, totK_node, atot6538, atot6553]
  decide +kernel

theorem arows6585 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6585 = true := by
  rw [show A10K2.u6585 = KTree.node A10K2.u6569 (nat_lit 108167941) (nat_lit 6876893410) (nat_lit 0) A10K2.u6584 from rfl, allE_node, arows6569, irow6585, arows6584]
  all_goals rfl

theorem atot6585 : totK PA10K2 A10K2.u6585 = [0, 2149128638022, 18231743929001, 50853267349926, 56654971519169, 22621426102127, 2881241097125, 93788834248, 0, 0] := by
  rw [show A10K2.u6585 = KTree.node A10K2.u6569 (nat_lit 108167941) (nat_lit 6876893410) (nat_lit 0) A10K2.u6584 from rfl, totK_node, atot6569, atot6584]
  decide +kernel

theorem arows6617 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6617 = true := by
  rw [show A10K2.u6617 = KTree.node A10K2.u6601 (nat_lit 108564004) (nat_lit 10858341380) (nat_lit 0) A10K2.u6616 from rfl, allE_node, arows6601, irow6617, arows6616]
  all_goals rfl

theorem atot6617 : totK PA10K2 A10K2.u6617 = [0, 3785708129680, 21584524829812, 47881221937629, 51259381934176, 25264622248811, 4988246198943, 377398666726, 6354482628, 0] := by
  rw [show A10K2.u6617 = KTree.node A10K2.u6601 (nat_lit 108564004) (nat_lit 10858341380) (nat_lit 0) A10K2.u6616 from rfl, totK_node, atot6601, atot6616]
  decide +kernel

theorem arows6648 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6648 = true := by
  rw [show A10K2.u6648 = KTree.node A10K2.u6632 (nat_lit 108783091) (nat_lit 8984791200) (nat_lit 0) A10K2.u6647 from rfl, allE_node, arows6632, irow6648, arows6647]
  all_goals rfl

theorem atot6648 : totK PA10K2 A10K2.u6648 = [2231826234337, 14156281014333, 36926479549705, 50662686168117, 37633370494664, 13652259188454, 1865726980458, 74789331576, 0, 0] := by
  rw [show A10K2.u6648 = KTree.node A10K2.u6632 (nat_lit 108783091) (nat_lit 8984791200) (nat_lit 0) A10K2.u6647 from rfl, totK_node, atot6632, atot6647]
  decide +kernel

theorem arows6683 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6683 = true := by
  rw [show A10K2.u6683 = KTree.node A10K2.u6667 (nat_lit 113470637) (nat_lit 1320144879) (nat_lit 0) A10K2.u6682 from rfl, allE_node, arows6667, irow6683, arows6682]
  all_goals rfl

theorem atot6683 : totK PA10K2 A10K2.u6683 = [3571414429873, 22728635259488, 52568240362386, 52755374823540, 21814122205608, 3176990983571, 123499561224, 0, 0, 0] := by
  rw [show A10K2.u6683 = KTree.node A10K2.u6667 (nat_lit 113470637) (nat_lit 1320144879) (nat_lit 0) A10K2.u6682 from rfl, totK_node, atot6667, atot6682]
  decide +kernel

theorem arows6714 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6714 = true := by
  rw [show A10K2.u6714 = KTree.node A10K2.u6698 (nat_lit 113691198) (nat_lit 7530365630) (nat_lit 0) A10K2.u6713 from rfl, allE_node, arows6698, irow6714, arows6713]
  all_goals rfl

theorem atot6714 : totK PA10K2 A10K2.u6714 = [2238164317933, 13708903052383, 36547730037671, 52433905654669, 37983013977044, 11272468582174, 1263669208897, 41810754621, 0, 0] := by
  rw [show A10K2.u6714 = KTree.node A10K2.u6698 (nat_lit 113691198) (nat_lit 7530365630) (nat_lit 0) A10K2.u6713 from rfl, totK_node, atot6698, atot6713]
  decide +kernel

theorem arows6746 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6746 = true := by
  rw [show A10K2.u6746 = KTree.node A10K2.u6730 (nat_lit 113956972) (nat_lit 11680964347) (nat_lit 0) A10K2.u6745 from rfl, allE_node, arows6730, irow6746, arows6745]
  all_goals rfl

theorem atot6746 : totK PA10K2 A10K2.u6746 = [3577560153580, 23293423436587, 54312978628130, 53442646717307, 20251490176709, 2446582203087, 63577454720, 0, 0, 0] := by
  rw [show A10K2.u6746 = KTree.node A10K2.u6730 (nat_lit 113956972) (nat_lit 11680964347) (nat_lit 0) A10K2.u6745 from rfl, totK_node, atot6730, atot6745]
  decide +kernel

theorem arows6777 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6777 = true := by
  rw [show A10K2.u6777 = KTree.node A10K2.u6761 (nat_lit 114173367) (nat_lit 14711992164) (nat_lit 0) A10K2.u6776 from rfl, allE_node, arows6761, irow6777, arows6776]
  all_goals rfl

theorem atot6777 : totK PA10K2 A10K2.u6777 = [0, 5812320669023, 31115691446289, 58963239763592, 45554078702245, 13114074853432, 1368403385069, 42943767608, 0, 0] := by
  rw [show A10K2.u6777 = KTree.node A10K2.u6761 (nat_lit 114173367) (nat_lit 14711992164) (nat_lit 0) A10K2.u6776 from rfl, totK_node, atot6761, atot6776]
  decide +kernel

theorem arows6810 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6810 = true := by
  rw [show A10K2.u6810 = KTree.node A10K2.u6794 (nat_lit 114898203) (nat_lit 10054382329) (nat_lit 0) A10K2.u6809 from rfl, allE_node, arows6794, irow6810, arows6809]
  all_goals rfl

theorem atot6810 : totK PA10K2 A10K2.u6810 = [5469350661477, 29018846264691, 56010884037387, 46850264421531, 16262322340029, 2290255482493, 116688452218, 0, 0, 0] := by
  rw [show A10K2.u6810 = KTree.node A10K2.u6794 (nat_lit 114898203) (nat_lit 10054382329) (nat_lit 0) A10K2.u6809 from rfl, totK_node, atot6794, atot6809]
  decide +kernel

theorem arows6841 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6841 = true := by
  rw [show A10K2.u6841 = KTree.node A10K2.u6825 (nat_lit 115085652) (nat_lit 9601546731) (nat_lit 0) A10K2.u6840 from rfl, allE_node, arows6825, irow6841, arows6840]
  all_goals rfl

theorem atot6841 : totK PA10K2 A10K2.u6841 = [1124207821172, 11873166741453, 40348269114461, 58403402251389, 36191850898835, 8376046588360, 620070735959, 7007974415, 0, 0] := by
  rw [show A10K2.u6841 = KTree.node A10K2.u6825 (nat_lit 115085652) (nat_lit 9601546731) (nat_lit 0) A10K2.u6840 from rfl, totK_node, atot6825, atot6840]
  decide +kernel

theorem arows6873 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6873 = true := by
  rw [show A10K2.u6873 = KTree.node A10K2.u6857 (nat_lit 115308022) (nat_lit 16668028827) (nat_lit 0) A10K2.u6872 from rfl, allE_node, arows6857, irow6873, arows6872]
  all_goals rfl

theorem atot6873 : totK PA10K2 A10K2.u6873 = [0, 5266840843652, 28502641792925, 56235790207624, 48134857410060, 16990478801027, 2154394706383, 80927666678, 0, 0] := by
  rw [show A10K2.u6873 = KTree.node A10K2.u6857 (nat_lit 115308022) (nat_lit 16668028827) (nat_lit 0) A10K2.u6872 from rfl, totK_node, atot6857, atot6872]
  decide +kernel

theorem arows6904 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6904 = true := by
  rw [show A10K2.u6904 = KTree.node A10K2.u6888 (nat_lit 115530002) (nat_lit 14066694137) (nat_lit 0) A10K2.u6903 from rfl, allE_node, arows6888, irow6904, arows6903]
  all_goals rfl

theorem atot6904 : totK PA10K2 A10K2.u6904 = [0, 3571414429873, 23222441870529, 54236511069126, 53259522630453, 19816323426835, 2289248344703, 61911465157, 0, 0] := by
  rw [show A10K2.u6904 = KTree.node A10K2.u6888 (nat_lit 115530002) (nat_lit 14066694137) (nat_lit 0) A10K2.u6903 from rfl, totK_node, atot6888, atot6903]
  decide +kernel

theorem arows6938 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6938 = true := by
  rw [show A10K2.u6938 = KTree.node A10K2.u6922 (nat_lit 115742762) (nat_lit 8298149329) (nat_lit 0) A10K2.u6937 from rfl, allE_node, arows6922, irow6938, arows6937]
  all_goals rfl

theorem atot6938 : totK PA10K2 A10K2.u6938 = [0, 1624997771604, 12823649013866, 39844750752578, 56852374861192, 35231949259569, 8070548080545, 614165943777, 7237400819, 0] := by
  rw [show A10K2.u6938 = KTree.node A10K2.u6922 (nat_lit 115742762) (nat_lit 8298149329) (nat_lit 0) A10K2.u6937 from rfl, totK_node, atot6922, atot6937]
  decide +kernel

theorem arows6969 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6969 = true := by
  rw [show A10K2.u6969 = KTree.node A10K2.u6953 (nat_lit 116043677) (nat_lit 2837776055) (nat_lit 0) A10K2.u6968 from rfl, allE_node, arows6953, irow6969, arows6968]
  all_goals rfl

theorem atot6969 : totK PA10K2 A10K2.u6969 = [0, 4190726699909, 25556362595151, 55732249675377, 51376037161354, 18288498816791, 2071119982336, 57002277655, 0, 0] := by
  rw [show A10K2.u6969 = KTree.node A10K2.u6953 (nat_lit 116043677) (nat_lit 2837776055) (nat_lit 0) A10K2.u6968 from rfl, totK_node, atot6953, atot6968]
  decide +kernel

theorem arows7001 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7001 = true := by
  rw [show A10K2.u7001 = KTree.node A10K2.u6985 (nat_lit 116270520) (nat_lit 9891531421) (nat_lit 0) A10K2.u7000 from rfl, allE_node, arows6985, irow7001, arows7000]
  all_goals rfl

theorem atot7001 : totK PA10K2 A10K2.u7001 = [0, 1427351586688, 12403479953474, 39545677717125, 57331479928990, 36428464858524, 8403596047027, 620084130770, 7380853412, 0] := by
  rw [show A10K2.u7001 = KTree.node A10K2.u6985 (nat_lit 116270520) (nat_lit 9891531421) (nat_lit 0) A10K2.u7000 from rfl, totK_node, atot6985, atot7000]
  decide +kernel

theorem arows7032 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7032 = true := by
  rw [show A10K2.u7032 = KTree.node A10K2.u7016 (nat_lit 117012375) (nat_lit 14322617938) (nat_lit 0) A10K2.u7031 from rfl, allE_node, arows7016, irow7032, arows7031]
  all_goals rfl

theorem atot7032 : totK PA10K2 A10K2.u7032 = [0, 5166206895961, 28825219017718, 57788666188469, 48602107318869, 15467270858445, 1490458086779, 25173583472, 0, 0] := by
  rw [show A10K2.u7032 = KTree.node A10K2.u7016 (nat_lit 117012375) (nat_lit 14322617938) (nat_lit 0) A10K2.u7031 from rfl, totK_node, atot7016, atot7031]
  decide +kernel

theorem arows7065 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7065 = true := by
  rw [show A10K2.u7065 = KTree.node A10K2.u7049 (nat_lit 117211392) (nat_lit 15049380543) (nat_lit 0) A10K2.u7064 from rfl, allE_node, arows7049, irow7065, arows7064]
  all_goals rfl

theorem atot7065 : totK PA10K2 A10K2.u7065 = [0, 0, 6389732317854, 33795353104102, 61393098595556, 44079532198280, 10857370281966, 809807124306, 13585869933, 0] := by
  rw [show A10K2.u7065 = KTree.node A10K2.u7049 (nat_lit 117211392) (nat_lit 15049380543) (nat_lit 0) A10K2.u7064 from rfl, totK_node, atot7049, atot7064]
  decide +kernel

theorem arows7096 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7096 = true := by
  rw [show A10K2.u7096 = KTree.node A10K2.u7080 (nat_lit 117436448) (nat_lit 14074751939) (nat_lit 0) A10K2.u7095 from rfl, allE_node, arows7080, irow7096, arows7095]
  all_goals rfl

theorem atot7096 : totK PA10K2 A10K2.u7096 = [0, 2339048713180, 15022260086189, 38409067446486, 50025470798110, 35167331438058, 12168423057041, 1726415855068, 73776485728, 0] := by
  rw [show A10K2.u7096 = KTree.node A10K2.u7080 (nat_lit 117436448) (nat_lit 14074751939) (nat_lit 0) A10K2.u7095 from rfl, totK_node, atot7080, atot7095]
  decide +kernel

theorem arows7128 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7128 = true := by
  rw [show A10K2.u7128 = KTree.node A10K2.u7112 (nat_lit 117649044) (nat_lit 8474962952) (nat_lit 0) A10K2.u7127 from rfl, allE_node, arows7112, irow7128, arows7127]
  all_goals rfl

theorem atot7128 : totK PA10K2 A10K2.u7128 = [0, 3958323339549, 24244140826635, 53985485016909, 51808432113152, 20137535936021, 2798136439050, 112248236336, 0, 0] := by
  rw [show A10K2.u7128 = KTree.node A10K2.u7112 (nat_lit 117649044) (nat_lit 8474962952) (nat_lit 0) A10K2.u7127 from rfl, totK_node, atot7112, atot7127]
  decide +kernel

theorem arows7159 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7159 = true := by
  rw [show A10K2.u7159 = KTree.node A10K2.u7143 (nat_lit 117852197) (nat_lit 7325617465) (nat_lit 0) A10K2.u7158 from rfl, allE_node, arows7143, irow7159, arows7158]
  all_goals rfl

theorem atot7159 : totK PA10K2 A10K2.u7159 = [0, 839403861465, 8387411604521, 32300099402888, 56393188184908, 42456568606267, 11977141715939, 1293810445850, 41810754621, 0] := by
  rw [show A10K2.u7159 = KTree.node A10K2.u7143 (nat_lit 117852197) (nat_lit 7325617465) (nat_lit 0) A10K2.u7158 from rfl, totK_node, atot7143, atot7158]
  decide +kernel

theorem arows7195 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7195 = true := by
  rw [show A10K2.u7195 = KTree.node A10K2.u7179 (nat_lit 118630628) (nat_lit 13490928517) (nat_lit 0) A10K2.u7194 from rfl, allE_node, arows7179, irow7195, arows7194]
  all_goals rfl

theorem atot7195 : totK PA10K2 A10K2.u7195 = [0, 3490628508443, 23208060671929, 54175340774318, 51969696167285, 18299058848788, 2245048295844, 79724133326, 0, 0] := by
  rw [show A10K2.u7195 = KTree.node A10K2.u7179 (nat_lit 118630628) (nat_lit 13490928517) (nat_lit 0) A10K2.u7194 from rfl, totK_node, atot7179, atot7194]
  decide +kernel

theorem arows7226 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7226 = true := by
  rw [show A10K2.u7226 = KTree.node A10K2.u7210 (nat_lit 119020722) (nat_lit 13269477559) (nat_lit 0) A10K2.u7225 from rfl, allE_node, arows7210, irow7226, arows7225]
  all_goals rfl

theorem atot7226 : totK PA10K2 A10K2.u7226 = [0, 3783711115774, 21141674206092, 47195697788615, 51755211639232, 25641555294690, 4926044950729, 349002784138, 6354482628, 0] := by
  rw [show A10K2.u7226 = KTree.node A10K2.u7210 (nat_lit 119020722) (nat_lit 13269477559) (nat_lit 0) A10K2.u7225 from rfl, totK_node, atot7210, atot7225]
  decide +kernel

theorem arows7258 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7258 = true := by
  rw [show A10K2.u7258 = KTree.node A10K2.u7242 (nat_lit 119246369) (nat_lit 9911283626) (nat_lit 0) A10K2.u7257 from rfl, allE_node, arows7242, irow7258, arows7257]
  all_goals rfl

theorem atot7258 : totK PA10K2 A10K2.u7258 = [0, 2346766361561, 17913021490701, 48786465062923, 57456829563722, 27856920266292, 4698502104028, 213050431112, 0, 0] := by
  rw [show A10K2.u7258 = KTree.node A10K2.u7242 (nat_lit 119246369) (nat_lit 9911283626) (nat_lit 0) A10K2.u7257 from rfl, totK_node, atot7242, atot7257]
  decide +kernel

theorem arows7289 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7289 = true := by
  rw [show A10K2.u7289 = KTree.node A10K2.u7273 (nat_lit 119476174) (nat_lit 14578503822) (nat_lit 0) A10K2.u7288 from rfl, allE_node, arows7273, irow7289, arows7288]
  all_goals rfl

theorem atot7289 : totK PA10K2 A10K2.u7289 = [0, 0, 4378136316810, 25499817565858, 55448841446207, 52616832363777, 19349537824927, 2433692842735, 87935641093, 0] := by
  rw [show A10K2.u7289 = KTree.node A10K2.u7273 (nat_lit 119476174) (nat_lit 14578503822) (nat_lit 0) A10K2.u7288 from rfl, totK_node, atot7273, atot7288]
  decide +kernel

theorem arows7322 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7322 = true := by
  rw [show A10K2.u7322 = KTree.node A10K2.u7306 (nat_lit 119671651) (nat_lit 8550831952) (nat_lit 0) A10K2.u7321 from rfl, allE_node, arows7306, irow7322, arows7321]
  all_goals rfl

theorem atot7322 : totK PA10K2 A10K2.u7322 = [0, 0, 5869249791658, 31175687609468, 58583963681281, 44672379243800, 12468594518315, 1308477877073, 42173223013, 0] := by
  rw [show A10K2.u7322 = KTree.node A10K2.u7306 (nat_lit 119671651) (nat_lit 8550831952) (nat_lit 0) A10K2.u7321 from rfl, totK_node, atot7306, atot7321]
  decide +kernel

theorem arows7353 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7353 = true := by
  rw [show A10K2.u7353 = KTree.node A10K2.u7337 (nat_lit 119831603) (nat_lit 6751552833) (nat_lit 0) A10K2.u7352 from rfl, allE_node, arows7337, irow7353, arows7352]
  all_goals rfl

theorem atot7353 : totK PA10K2 A10K2.u7353 = [0, 0, 0, 9094586290696, 41161598310155, 62459451456538, 35062719785499, 7210434368489, 543819229274, 7903172220] := by
  rw [show A10K2.u7353 = KTree.node A10K2.u7337 (nat_lit 119831603) (nat_lit 6751552833) (nat_lit 0) A10K2.u7352 from rfl, totK_node, atot7337, atot7352]
  decide +kernel

theorem arows7385 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7385 = true := by
  rw [show A10K2.u7385 = KTree.node A10K2.u7369 (nat_lit 120721476) (nat_lit 11362666811) (nat_lit 0) A10K2.u7384 from rfl, allE_node, arows7369, irow7385, arows7384]
  all_goals rfl

theorem atot7385 : totK PA10K2 A10K2.u7385 = [0, 0, 5698502414151, 30859884878799, 58978159011629, 44681200986817, 12036628062664, 1327749227512, 47404149471, 0] := by
  rw [show A10K2.u7385 = KTree.node A10K2.u7369 (nat_lit 120721476) (nat_lit 11362666811) (nat_lit 0) A10K2.u7384 from rfl, totK_node, atot7369, atot7384]
  decide +kernel

theorem arows7416 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7416 = true := by
  rw [show A10K2.u7416 = KTree.node A10K2.u7400 (nat_lit 121220837) (nat_lit 3793976309) (nat_lit 32) A10K2.u7415 from rfl, allE_node, arows7400, irow7416, arows7415]
  all_goals rfl

theorem atot7416 : totK PA10K2 A10K2.u7416 = [0, 0, 4746950972541, 27532999054490, 57996958703620, 51450623309358, 17075123916495, 1703509412041, 34417036258, 0] := by
  rw [show A10K2.u7416 = KTree.node A10K2.u7400 (nat_lit 121220837) (nat_lit 3793976309) (nat_lit 32) A10K2.u7415 from rfl, totK_node, atot7400, atot7415]
  decide +kernel

theorem arows7450 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7450 = true := by
  rw [show A10K2.u7450 = KTree.node A10K2.u7434 (nat_lit 122275250) (nat_lit 14811310501) (nat_lit 0) A10K2.u7449 from rfl, allE_node, arows7434, irow7450, arows7449]
  all_goals rfl

theorem atot7450 : totK PA10K2 A10K2.u7450 = [0, 4648685365675, 25717200313446, 51678186923509, 45858292171825, 19751155914213, 6005418832141, 1073300228178, 61110126106, 0] := by
  rw [show A10K2.u7450 = KTree.node A10K2.u7434 (nat_lit 122275250) (nat_lit 14811310501) (nat_lit 0) A10K2.u7449 from rfl, totK_node, atot7434, atot7449]
  decide +kernel

theorem arows7481 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7481 = true := by
  rw [show A10K2.u7481 = KTree.node A10K2.u7465 (nat_lit 122500266) (nat_lit 13029250930) (nat_lit 0) A10K2.u7480 from rfl, allE_node, arows7465, irow7481, arows7480]
  all_goals rfl

theorem atot7481 : totK PA10K2 A10K2.u7481 = [0, 1659408637769, 13355176750301, 40164388726189, 55603292394469, 35349543791731, 9441153305504, 1030617362875, 36704093874, 0] := by
  rw [show A10K2.u7481 = KTree.node A10K2.u7465 (nat_lit 122500266) (nat_lit 13029250930) (nat_lit 0) A10K2.u7480 from rfl, totK_node, atot7465, atot7480]
  decide +kernel

theorem arows7513 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7513 = true := by
  rw [show A10K2.u7513 = KTree.node A10K2.u7497 (nat_lit 122650124) (nat_lit 6217940146) (nat_lit 0) A10K2.u7512 from rfl, allE_node, arows7497, irow7513, arows7512]
  all_goals rfl

theorem atot7513 : totK PA10K2 A10K2.u7513 = [0, 2749136384700, 17087181561064, 43243976409906, 54228209365611, 31341058299747, 6569973696050, 447829682561, 6239673734, 0] := by
  rw [show A10K2.u7513 = KTree.node A10K2.u7497 (nat_lit 122650124) (nat_lit 6217940146) (nat_lit 0) A10K2.u7512 from rfl, totK_node, atot7497, atot7512]
  decide +kernel

theorem arows7544 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7544 = true := by
  rw [show A10K2.u7544 = KTree.node A10K2.u7528 (nat_lit 123029171) (nat_lit 10276619565) (nat_lit 0) A10K2.u7543 from rfl, allE_node, arows7528, irow7544, arows7543]
  all_goals rfl

theorem atot7544 : totK PA10K2 A10K2.u7544 = [0, 1587972465714, 14625783533951, 44495218282502, 56965026673859, 29345302573175, 5151256058267, 250296237462, 0, 0] := by
  rw [show A10K2.u7544 = KTree.node A10K2.u7528 (nat_lit 123029171) (nat_lit 10276619565) (nat_lit 0) A10K2.u7543 from rfl, totK_node, atot7528, atot7543]
  decide +kernel

theorem arows7577 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7577 = true := by
  rw [show A10K2.u7577 = KTree.node A10K2.u7561 (nat_lit 123299272) (nat_lit 11932227570) (nat_lit 0) A10K2.u7576 from rfl, allE_node, arows7561, irow7577, arows7576]
  all_goals rfl

theorem atot7577 : totK PA10K2 A10K2.u7577 = [0, 6132911655538, 31411164231595, 58135365591803, 46004935611687, 14786256791728, 2080292610243, 187251831971, 6354482628, 0] := by
  rw [show A10K2.u7577 = KTree.node A10K2.u7561 (nat_lit 123299272) (nat_lit 11932227570) (nat_lit 0) A10K2.u7576 from rfl, totK_node, atot7561, atot7576]
  decide +kernel

theorem arows7608 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7608 = true := by
  rw [show A10K2.u7608 = KTree.node A10K2.u7592 (nat_lit 123502258) (nat_lit 14548335350) (nat_lit 0) A10K2.u7607 from rfl, allE_node, arows7592, irow7608, arows7607]
  all_goals rfl

theorem atot7608 : totK PA10K2 A10K2.u7608 = [0, 0, 7129625383085, 35339933826481, 61317400953940, 43255060806329, 11186537281596, 911636277612, 14159155365, 0] := by
  rw [show A10K2.u7608 = KTree.node A10K2.u7592 (nat_lit 123502258) (nat_lit 14548335350) (nat_lit 0) A10K2.u7607 from rfl, totK_node, atot7592, atot7607]
  decide +kernel

theorem arows7640 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7640 = true := by
  rw [show A10K2.u7640 = KTree.node A10K2.u7624 (nat_lit 123726998) (nat_lit 15438790864) (nat_lit 0) A10K2.u7639 from rfl, allE_node, arows7624, irow7640, arows7639]
  all_goals rfl

theorem atot7640 : totK PA10K2 A10K2.u7640 = [0, 0, 4689884536836, 26339055309331, 54900867662139, 50156909392116, 18649408449541, 2507281567787, 104859372337, 0] := by
  rw [show A10K2.u7640 = KTree.node A10K2.u7624 (nat_lit 123726998) (nat_lit 15438790864) (nat_lit 0) A10K2.u7639 from rfl, totK_node, atot7624, atot7639]
  decide +kernel

theorem arows7671 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7671 = true := by
  rw [show A10K2.u7671 = KTree.node A10K2.u7655 (nat_lit 124467052) (nat_lit 11153969721) (nat_lit 0) A10K2.u7670 from rfl, allE_node, arows7655, irow7671, arows7670]
  all_goals rfl

theorem atot7671 : totK PA10K2 A10K2.u7671 = [0, 0, 3963914826293, 24489369581072, 54590874176334, 51802009830012, 19522578068862, 2566581415344, 92421725248, 0] := by
  rw [show A10K2.u7671 = KTree.node A10K2.u7655 (nat_lit 124467052) (nat_lit 11153969721) (nat_lit 0) A10K2.u7670 from rfl, totK_node, atot7655, atot7670]
  decide +kernel

theorem arows7706 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7706 = true := by
  rw [show A10K2.u7706 = KTree.node A10K2.u7690 (nat_lit 124726099) (nat_lit 8900276491) (nat_lit 0) A10K2.u7705 from rfl, allE_node, arows7690, irow7706, arows7705]
  all_goals rfl

theorem atot7706 : totK PA10K2 A10K2.u7706 = [0, 0, 3516284413366, 20075967929953, 46102200626546, 51873492491429, 27706793201267, 6177922468167, 516715194132, 8047840951] := by
  rw [show A10K2.u7706 = KTree.node A10K2.u7690 (nat_lit 124726099) (nat_lit 8900276491) (nat_lit 0) A10K2.u7705 from rfl, totK_node, atot7690, atot7705]
  decide +kernel

theorem arows7737 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7737 = true := by
  rw [show A10K2.u7737 = KTree.node A10K2.u7721 (nat_lit 125340728) (nat_lit 14794659053) (nat_lit 0) A10K2.u7736 from rfl, allE_node, arows7721, irow7737, arows7736]
  all_goals rfl

theorem atot7737 : totK PA10K2 A10K2.u7737 = [0, 0, 4606532566728, 27769452545691, 58428513205667, 49629287513534, 14967713863667, 1418994041445, 27168101557, 0] := by
  rw [show A10K2.u7737 = KTree.node A10K2.u7721 (nat_lit 125340728) (nat_lit 14794659053) (nat_lit 0) A10K2.u7736 from rfl, totK_node, atot7721, atot7736]
  decide +kernel

theorem arows7769 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7769 = true := by
  rw [show A10K2.u7769 = KTree.node A10K2.u7753 (nat_lit 125562038) (nat_lit 16606316129) (nat_lit 0) A10K2.u7768 from rfl, allE_node, arows7753, irow7769, arows7768]
  all_goals rfl

theorem atot7769 : totK PA10K2 A10K2.u7769 = [0, 2231826234337, 14452549332257, 37758920462693, 50785801727853, 36829398752883, 13287815014160, 1808055014860, 74789331576, 0] := by
  rw [show A10K2.u7769 = KTree.node A10K2.u7753 (nat_lit 125562038) (nat_lit 16606316129) (nat_lit 0) A10K2.u7768 from rfl, totK_node, atot7753, atot7768]
  decide +kernel

theorem arows7800 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7800 = true := by
  rw [show A10K2.u7800 = KTree.node A10K2.u7784 (nat_lit 130250395) (nat_lit 9992812594) (nat_lit 0) A10K2.u7799 from rfl, allE_node, arows7784, irow7800, arows7799]
  all_goals rfl

theorem atot7800 : totK PA10K2 A10K2.u7800 = [0, 3571414429873, 22937217489963, 53330523810885, 53184943522903, 21268845686415, 2917258745996, 111598773623, 0, 0] := by
  rw [show A10K2.u7800 = KTree.node A10K2.u7784 (nat_lit 130250395) (nat_lit 9992812594) (nat_lit 0) A10K2.u7799 from rfl, totK_node, atot7784, atot7799]
  decide +kernel

theorem arows7833 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7833 = true := by
  rw [show A10K2.u7833 = KTree.node A10K2.u7817 (nat_lit 130486549) (nat_lit 5488907260) (nat_lit 0) A10K2.u7832 from rfl, allE_node, arows7817, irow7833, arows7832]
  all_goals rfl

theorem atot7833 : totK PA10K2 A10K2.u7833 = [0, 2238164317933, 14628038284847, 39318462816532, 53940805207662, 35893692366554, 9252454872520, 803821639738, 13364899180, 0] := by
  rw [show A10K2.u7833 = KTree.node A10K2.u7817 (nat_lit 130486549) (nat_lit 5488907260) (nat_lit 0) A10K2.u7832 from rfl, totK_node, atot7817, atot7832]
  decide +kernel

theorem arows7864 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7864 = true := by
  rw [show A10K2.u7864 = KTree.node A10K2.u7848 (nat_lit 130755738) (nat_lit 15149100895) (nat_lit 0) A10K2.u7863 from rfl, allE_node, arows7848, irow7864, arows7863]
  all_goals rfl

theorem atot7864 : totK PA10K2 A10K2.u7864 = [0, 3577560153580, 22718827261270, 52757635072607, 53197136050506, 22007296980228, 3239278549767, 138000673012, 0, 0] := by
  rw [show A10K2.u7864 = KTree.node A10K2.u7848 (nat_lit 130755738) (nat_lit 15149100895) (nat_lit 0) A10K2.u7863 from rfl, totK_node, atot7848, atot7863]
  decide +kernel

theorem arows7896 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7896 = true := by
  rw [show A10K2.u7896 = KTree.node A10K2.u7880 (nat_lit 130963676) (nat_lit 11107961971) (nat_lit 0) A10K2.u7895 from rfl, allE_node, arows7880, irow7896, arows7895]
  all_goals rfl

theorem atot7896 : totK PA10K2 A10K2.u7896 = [0, 1540001081091, 11566711742835, 36370386334572, 56362985233003, 39583729359476, 10119460150182, 837659984031, 13576218110, 0] := by
  rw [show A10K2.u7896 = KTree.node A10K2.u7880 (nat_lit 130963676) (nat_lit 11107961971) (nat_lit 0) A10K2.u7895 from rfl, totK_node, atot7880, atot7895]
  decide +kernel

theorem arows7927 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7927 = true := by
  rw [show A10K2.u7927 = KTree.node A10K2.u7911 (nat_lit 131692333) (nat_lit 5599426209) (nat_lit 0) A10K2.u7926 from rfl, allE_node, arows7911, irow7927, arows7926]
  all_goals rfl

theorem atot7927 : totK PA10K2 A10K2.u7927 = [0, 5053557401558, 28328551021781, 57272973498400, 48965017717092, 16150617954923, 1742560667087, 37172991031, 0, 0] := by
  rw [show A10K2.u7927 = KTree.node A10K2.u7911 (nat_lit 131692333) (nat_lit 5599426209) (nat_lit 0) A10K2.u7926 from rfl, totK_node, atot7911, atot7926]
  decide +kernel

theorem arows7961 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7961 = true := by
  rw [show A10K2.u7961 = KTree.node A10K2.u7945 (nat_lit 131890638) (nat_lit 14800495088) (nat_lit 0) A10K2.u7960 from rfl, allE_node, arows7945, irow7961, arows7960]
  all_goals rfl

theorem atot7961 : totK PA10K2 A10K2.u7961 = [0, 0, 6558487729400, 33784307412424, 60731098866977, 43896699933946, 11289733465622, 884080819664, 14159155365, 0] := by
  rw [show A10K2.u7961 = KTree.node A10K2.u7945 (nat_lit 131890638) (nat_lit 14800495088) (nat_lit 0) A10K2.u7960 from rfl, totK_node, atot7945, atot7960]
  decide +kernel

theorem arows7992 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7992 = true := by
  rw [show A10K2.u7992 = KTree.node A10K2.u7976 (nat_lit 132112644) (nat_lit 9103019395) (nat_lit 0) A10K2.u7991 from rfl, allE_node, arows7976, irow7992, arows7991]
  all_goals rfl

theorem atot7992 : totK PA10K2 A10K2.u7992 = [0, 0, 4653061469545, 26480189493933, 55247571857589, 49838035741551, 18126479099977, 2350150540927, 87141384908, 0] := by
  rw [show A10K2.u7992 = KTree.node A10K2.u7976 (nat_lit 132112644) (nat_lit 9103019395) (nat_lit 0) A10K2.u7991 from rfl, totK_node, atot7976, atot7991]
  decide +kernel

theorem arows8024 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8024 = true := by
  rw [show A10K2.u8024 = KTree.node A10K2.u8008 (nat_lit 132349335) (nat_lit 14616934806) (nat_lit 0) A10K2.u8023 from rfl, allE_node, arows8008, irow8024, arows8023]
  all_goals rfl

theorem atot8024 : totK PA10K2 A10K2.u8024 = [0, 0, 3568549953759, 22636196352753, 52914384408740, 53633413741388, 21909189892089, 2883509716641, 94999656960, 0] := by
  rw [show A10K2.u8024 = KTree.node A10K2.u8008 (nat_lit 132349335) (nat_lit 14616934806) (nat_lit 0) A10K2.u8023 from rfl, totK_node, atot8008, atot8023]
  decide +kernel

theorem arows8055 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8055 = true := by
  rw [show A10K2.u8055 = KTree.node A10K2.u8039 (nat_lit 132612054) (nat_lit 15601130921) (nat_lit 0) A10K2.u8054 from rfl, allE_node, arows8039, irow8055, arows8054]
  all_goals rfl

theorem atot8055 : totK PA10K2 A10K2.u8055 = [0, 0, 3000864694247, 18963182322604, 46882693708317, 54042651478253, 28008056376453, 5722159935417, 419965358374, 7237400819] := by
  rw [show A10K2.u8055 = KTree.node A10K2.u8039 (nat_lit 132612054) (nat_lit 15601130921) (nat_lit 0) A10K2.u8054 from rfl, totK_node, atot8039, atot8054]
  decide +kernel

theorem arows8088 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8088 = true := by
  rw [show A10K2.u8088 = KTree.node A10K2.u8072 (nat_lit 132885573) (nat_lit 1726874732) (nat_lit 0) A10K2.u8087 from rfl, allE_node, arows8072, irow8088, arows8087]
  all_goals rfl

theorem atot8088 : totK PA10K2 A10K2.u8088 = [0, 0, 2811976945744, 19094254768024, 48056221526866, 54569714650355, 27612372002981, 5460680519126, 384093790277, 7380853412] := by
  rw [show A10K2.u8088 = KTree.node A10K2.u8072 (nat_lit 132885573) (nat_lit 1726874732) (nat_lit 0) A10K2.u8087 from rfl, totK_node, atot8072, atot8087]
  decide +kernel

theorem arows8119 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8119 = true := by
  rw [show A10K2.u8119 = KTree.node A10K2.u8103 (nat_lit 133718135) (nat_lit 14469999615) (nat_lit 0) A10K2.u8118 from rfl, allE_node, arows8103, irow8119, arows8118]
  all_goals rfl

theorem atot8119 : totK PA10K2 A10K2.u8119 = [0, 0, 4169303979564, 24869417437840, 53953349456422, 51004368742078, 20935407079456, 3104670876255, 138230466203, 0] := by
  rw [show A10K2.u8119 = KTree.node A10K2.u8103 (nat_lit 133718135) (nat_lit 14469999615) (nat_lit 0) A10K2.u8118 from rfl, totK_node, atot8103, atot8118]
  decide +kernel

theorem arows8151 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8151 = true := by
  rw [show A10K2.u8151 = KTree.node A10K2.u8135 (nat_lit 133925965) (nat_lit 5274797582) (nat_lit 0) A10K2.u8150 from rfl, allE_node, arows8135, irow8151, arows8150]
  all_goals rfl

theorem atot8151 : totK PA10K2 A10K2.u8151 = [0, 0, 2424236405812, 17880429797501, 48396419548639, 57057571313307, 27175874185316, 4127227718364, 175084125249, 0] := by
  rw [show A10K2.u8151 = KTree.node A10K2.u8135 (nat_lit 133925965) (nat_lit 5274797582) (nat_lit 0) A10K2.u8150 from rfl, totK_node, atot8135, atot8150]
  decide +kernel

theorem arows8182 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8182 = true := by
  rw [show A10K2.u8182 = KTree.node A10K2.u8166 (nat_lit 134155675) (nat_lit 8959646947) (nat_lit 0) A10K2.u8181 from rfl, allE_node, arows8166, irow8182, arows8181]
  all_goals rfl

theorem atot8182 : totK PA10K2 A10K2.u8182 = [0, 0, 0, 4489196093464, 26196522307298, 55295087698755, 50597922721915, 18062555069662, 2337638511574, 87362355661] := by
  rw [show A10K2.u8182 = KTree.node A10K2.u8166 (nat_lit 134155675) (nat_lit 8959646947) (nat_lit 0) A10K2.u8181 from rfl, totK_node, atot8166, atot8181]
  decide +kernel

theorem arows62 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u62 = true := by
  rw [show A10K2.u62 = KTree.node A10K2.u30 (nat_lit 208341) (nat_lit 2917371423) (nat_lit 0) A10K2.u61 from rfl, allE_node, arows30, irow62, arows61]
  all_goals rfl

theorem atot62 : totK PA10K2 A10K2.u62 = [6508970599089, 40555739875583, 95162828419898, 102888510352280, 51177366384854, 11192045862618, 1073349177419, 36134558889, 0, 0] := by
  rw [show A10K2.u62 = KTree.node A10K2.u30 (nat_lit 208341) (nat_lit 2917371423) (nat_lit 0) A10K2.u61 from rfl, totK_node, atot30, atot61]
  decide +kernel

theorem arows125 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u125 = true := by
  rw [show A10K2.u125 = KTree.node A10K2.u93 (nat_lit 1130552) (nat_lit 14167745555) (nat_lit 0) A10K2.u124 from rfl, allE_node, arows93, irow125, arows124]
  all_goals rfl

theorem atot125 : totK PA10K2 A10K2.u125 = [5666557143554, 38125538702486, 95351263078155, 106529160727275, 50699005543043, 9093744005371, 524140421052, 5676195732, 0, 0] := by
  rw [show A10K2.u125 = KTree.node A10K2.u93 (nat_lit 1130552) (nat_lit 14167745555) (nat_lit 0) A10K2.u124 from rfl, totK_node, atot93, atot124]
  decide +kernel

theorem arows189 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u189 = true := by
  rw [show A10K2.u189 = KTree.node A10K2.u157 (nat_lit 1666260) (nat_lit 9826023445) (nat_lit 0) A10K2.u188 from rfl, allE_node, arows157, irow189, arows188]
  all_goals rfl

theorem atot189 : totK PA10K2 A10K2.u189 = [5885876839217, 37739750889353, 93563601322688, 108311706598661, 55305733235114, 10680622936233, 719169735437, 6354482628, 0, 0] := by
  rw [show A10K2.u189 = KTree.node A10K2.u157 (nat_lit 1666260) (nat_lit 9826023445) (nat_lit 0) A10K2.u188 from rfl, totK_node, atot157, atot188]
  decide +kernel

theorem arows252 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u252 = true := by
  rw [show A10K2.u252 = KTree.node A10K2.u220 (nat_lit 2103395) (nat_lit 4823614290) (nat_lit 0) A10K2.u251 from rfl, allE_node, arows220, irow252, arows251]
  all_goals rfl

theorem atot252 : totK PA10K2 A10K2.u252 = [0, 10171340395678, 56385173745963, 113387655371455, 96698044427525, 32170547743272, 3811608080481, 130108864106, 0, 0] := by
  rw [show A10K2.u252 = KTree.node A10K2.u220 (nat_lit 2103395) (nat_lit 4823614290) (nat_lit 0) A10K2.u251 from rfl, totK_node, atot220, atot251]
  decide +kernel

theorem arows317 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u317 = true := by
  rw [show A10K2.u317 = KTree.node A10K2.u285 (nat_lit 2534144) (nat_lit 12914873714) (nat_lit 0) A10K2.u316 from rfl, allE_node, arows285, irow317, arows316]
  all_goals rfl

theorem atot317 : totK PA10K2 A10K2.u317 = [0, 3666287800522, 29210992725190, 85368803835288, 110904522160425, 61685557431402, 14060452186876, 1359606697188, 41810754621, 0] := by
  rw [show A10K2.u317 = KTree.node A10K2.u285 (nat_lit 2534144) (nat_lit 12914873714) (nat_lit 0) A10K2.u316 from rfl, totK_node, atot285, atot316]
  decide +kernel

theorem arows380 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u380 = true := by
  rw [show A10K2.u380 = KTree.node A10K2.u348 (nat_lit 3572074) (nat_lit 7858887472) (nat_lit 0) A10K2.u379 from rfl, allE_node, arows348, irow380, arows379]
  all_goals rfl

theorem atot380 : totK PA10K2 A10K2.u380 = [0, 7002722401441, 44288766749650, 102723150876932, 104004197609761, 42804759203815, 6819673550666, 398593072049, 5976421810, 0] := by
  rw [show A10K2.u380 = KTree.node A10K2.u348 (nat_lit 3572074) (nat_lit 7858887472) (nat_lit 0) A10K2.u379 from rfl, totK_node, atot348, atot379]
  decide +kernel

theorem arows444 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u444 = true := by
  rw [show A10K2.u444 = KTree.node A10K2.u412 (nat_lit 8534718) (nat_lit 4525027683) (nat_lit 0) A10K2.u443 from rfl, allE_node, arows412, irow444, arows443]
  all_goals rfl

theorem atot444 : totK PA10K2 A10K2.u444 = [6013589397192, 37117064569648, 88106790540521, 100720922880805, 59086377091013, 18374113063830, 2492283376346, 105387157622, 0, 0] := by
  rw [show A10K2.u444 = KTree.node A10K2.u412 (nat_lit 8534718) (nat_lit 4525027683) (nat_lit 0) A10K2.u443 from rfl, totK_node, atot412, atot443]
  decide +kernel

theorem arows507 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u507 = true := by
  rw [show A10K2.u507 = KTree.node A10K2.u475 (nat_lit 9026743) (nat_lit 14808797364) (nat_lit 0) A10K2.u506 from rfl, allE_node, arows475, irow507, arows506]
  all_goals rfl

theorem atot507 : totK PA10K2 A10K2.u507 = [4334610403000, 30637961755897, 82903859282069, 106745062937021, 65023970663551, 16662090424842, 1638206930716, 47909100645, 0, 0] := by
  rw [show A10K2.u507 = KTree.node A10K2.u475 (nat_lit 9026743) (nat_lit 14808797364) (nat_lit 0) A10K2.u506 from rfl, totK_node, atot475, atot506]
  decide +kernel

theorem arows573 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u573 = true := by
  rw [show A10K2.u573 = KTree.node A10K2.u541 (nat_lit 9528552) (nat_lit 3397189322) (nat_lit 0) A10K2.u572 from rfl, allE_node, arows541, irow573, arows572]
  all_goals rfl

theorem atot573 : totK PA10K2 A10K2.u573 = [6202877974731, 40183006700197, 96856719183407, 104817184666074, 48831178857456, 8504243447232, 495158921063, 6239673734, 0, 0] := by
  rw [show A10K2.u573 = KTree.node A10K2.u541 (nat_lit 9528552) (nat_lit 3397189322) (nat_lit 0) A10K2.u572 from rfl, totK_node, atot541, atot572]
  decide +kernel

theorem arows636 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u636 = true := by
  rw [show A10K2.u636 = KTree.node A10K2.u604 (nat_lit 10617285) (nat_lit 5078250354) (nat_lit 0) A10K2.u635 from rfl, allE_node, arows604, irow636, arows635]
  all_goals rfl

theorem atot636 : totK PA10K2 A10K2.u636 = [0, 11053422297816, 60940645501184, 117648688069928, 90597944777975, 25249169769198, 2446092287381, 55810694723, 0, 0] := by
  rw [show A10K2.u636 = KTree.node A10K2.u604 (nat_lit 10617285) (nat_lit 5078250354) (nat_lit 0) A10K2.u635 from rfl, totK_node, atot604, atot635]
  decide +kernel

theorem arows700 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u700 = true := by
  rw [show A10K2.u700 = KTree.node A10K2.u668 (nat_lit 11592462) (nat_lit 10297603297) (nat_lit 0) A10K2.u699 from rfl, allE_node, arows668, irow700, arows699]
  all_goals rfl

theorem atot700 : totK PA10K2 A10K2.u700 = [0, 8336894133720, 50170419435574, 109170463741294, 99401809342673, 33303286837193, 4004180950242, 152837955209, 0, 0] := by
  rw [show A10K2.u700 = KTree.node A10K2.u668 (nat_lit 11592462) (nat_lit 10297603297) (nat_lit 0) A10K2.u699 from rfl, totK_node, atot668, atot699]
  decide +kernel

theorem arows763 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u763 = true := by
  rw [show A10K2.u763 = KTree.node A10K2.u731 (nat_lit 12623359) (nat_lit 10024016499) (nat_lit 0) A10K2.u762 from rfl, allE_node, arows731, irow763, arows762]
  all_goals rfl

theorem atot763 : totK PA10K2 A10K2.u763 = [6057296600667, 35093173903654, 78867048453496, 90896152420031, 64036790244086, 27232716497850, 5711750622319, 489767369008, 6354482628, 0] := by
  rw [show A10K2.u763 = KTree.node A10K2.u731 (nat_lit 12623359) (nat_lit 10024016499) (nat_lit 0) A10K2.u762 from rfl, totK_node, atot731, atot762]
  decide +kernel

theorem arows828 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u828 = true := by
  rw [show A10K2.u828 = KTree.node A10K2.u796 (nat_lit 13186742) (nat_lit 15439386157) (nat_lit 0) A10K2.u827 from rfl, allE_node, arows796, irow828, arows827]
  all_goals rfl

theorem atot828 : totK PA10K2 A10K2.u828 = [4457728465308, 31302576281589, 85316114402484, 110200525401249, 65421943729735, 15493240365142, 1430298014163, 41810754621, 0, 0] := by
  rw [show A10K2.u828 = KTree.node A10K2.u796 (nat_lit 13186742) (nat_lit 15439386157) (nat_lit 0) A10K2.u827 from rfl, totK_node, atot796, atot827]
  decide +kernel

theorem arows891 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u891 = true := by
  rw [show A10K2.u891 = KTree.node A10K2.u859 (nat_lit 14209376) (nat_lit 12740465934) (nat_lit 0) A10K2.u890 from rfl, allE_node, arows859, irow891, arows890]
  all_goals rfl

theorem atot891 : totK PA10K2 A10K2.u891 = [6392439720472, 39813363954219, 94943094988503, 106030092900689, 55016346671276, 12251023712950, 1118857275334, 36704093874, 0, 0] := by
  rw [show A10K2.u891 = KTree.node A10K2.u859 (nat_lit 14209376) (nat_lit 12740465934) (nat_lit 0) A10K2.u890 from rfl, totK_node, atot859, atot890]
  decide +kernel

theorem arows955 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u955 = true := by
  rw [show A10K2.u955 = KTree.node A10K2.u923 (nat_lit 14643245) (nat_lit 2834774302) (nat_lit 0) A10K2.u954 from rfl, allE_node, arows923, irow955, arows954]
  all_goals rfl

theorem atot955 : totK PA10K2 A10K2.u955 = [0, 10220713712787, 57038084901820, 114279407823734, 96488138367617, 31995432821246, 3742562471886, 124132442296, 0, 0] := by
  rw [show A10K2.u955 = KTree.node A10K2.u923 (nat_lit 14643245) (nat_lit 2834774302) (nat_lit 0) A10K2.u954 from rfl, totK_node, atot923, atot954]
  decide +kernel

theorem arows1018 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1018 = true := by
  rw [show A10K2.u1018 = KTree.node A10K2.u986 (nat_lit 15002801) (nat_lit 6742900167) (nat_lit 0) A10K2.u1017 from rfl, allE_node, arows986, irow1018, arows1017]
  all_goals rfl

theorem atot1018 : totK PA10K2 A10K2.u1018 = [0, 5812819033432, 37557952755492, 94233814051238, 109556741070792, 55231727429323, 10359059983458, 676849197288, 7237400819, 0] := by
  rw [show A10K2.u1018 = KTree.node A10K2.u986 (nat_lit 15002801) (nat_lit 6742900167) (nat_lit 0) A10K2.u1017 from rfl, totK_node, atot986, atot1017]
  decide +kernel

theorem arows1085 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1085 = true := by
  rw [show A10K2.u1085 = KTree.node A10K2.u1053 (nat_lit 15690914) (nat_lit 13672110144) (nat_lit 0) A10K2.u1084 from rfl, allE_node, arows1053, irow1085, arows1084]
  all_goals rfl

theorem atot1085 : totK PA10K2 A10K2.u1085 = [0, 6215005976057, 39644738276821, 96488804781233, 108351332745938, 54346944124768, 10266069218789, 652582437084, 7380853412, 0] := by
  rw [show A10K2.u1085 = KTree.node A10K2.u1053 (nat_lit 15690914) (nat_lit 13672110144) (nat_lit 0) A10K2.u1084 from rfl, totK_node, atot1053, atot1084]
  decide +kernel

theorem arows1148 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1148 = true := by
  rw [show A10K2.u1148 = KTree.node A10K2.u1116 (nat_lit 16610666) (nat_lit 9829067446) (nat_lit 0) A10K2.u1147 from rfl, allE_node, arows1116, irow1148, arows1147]
  all_goals rfl

theorem atot1148 : totK PA10K2 A10K2.u1148 = [0, 3409337797893, 25957436682390, 76157012455396, 108435029783234, 75792115673926, 22298911902677, 2500026178171, 87362355661, 0] := by
  rw [show A10K2.u1148 = KTree.node A10K2.u1116 (nat_lit 16610666) (nat_lit 9829067446) (nat_lit 0) A10K2.u1147 from rfl, totK_node, atot1116, atot1147]
  decide +kernel

theorem arows1212 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1212 = true := by
  rw [show A10K2.u1212 = KTree.node A10K2.u1180 (nat_lit 17034405) (nat_lit 1242064375) (nat_lit 0) A10K2.u1211 from rfl, allE_node, arows1180, irow1212, arows1211]
  all_goals rfl

theorem atot1212 : totK PA10K2 A10K2.u1212 = [0, 4128935202610, 30635218676542, 85556981026334, 109239678544100, 61609016553240, 14100712519543, 1351909626342, 41810754621, 0] := by
  rw [show A10K2.u1212 = KTree.node A10K2.u1180 (nat_lit 17034405) (nat_lit 1242064375) (nat_lit 0) A10K2.u1211 from rfl, totK_node, atot1180, atot1211]
  decide +kernel

theorem arows1275 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1275 = true := by
  rw [show A10K2.u1275 = KTree.node A10K2.u1243 (nat_lit 17971308) (nat_lit 11464515024) (nat_lit 0) A10K2.u1274 from rfl, allE_node, arows1243, irow1275, arows1274]
  all_goals rfl

theorem atot1275 : totK PA10K2 A10K2.u1275 = [0, 5666557143554, 38703546965005, 97902036492168, 108326750881644, 47353176579359, 6911903952910, 263612558435, 0, 0] := by
  rw [show A10K2.u1275 = KTree.node A10K2.u1243 (nat_lit 17971308) (nat_lit 11464515024) (nat_lit 0) A10K2.u1274 from rfl, totK_node, atot1243, atot1274]
  decide +kernel

theorem arows1340 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1340 = true := by
  rw [show A10K2.u1340 = KTree.node A10K2.u1308 (nat_lit 18576533) (nat_lit 5999753819) (nat_lit 0) A10K2.u1339 from rfl, allE_node, arows1308, irow1340, arows1339]
  all_goals rfl

theorem atot1340 : totK PA10K2 A10K2.u1340 = [0, 5885876839217, 38360233804865, 94643314305094, 108443928196519, 56746431645656, 12016799726099, 876193079642, 13362457043, 0] := by
  rw [show A10K2.u1340 = KTree.node A10K2.u1308 (nat_lit 18576533) (nat_lit 5999753819) (nat_lit 0) A10K2.u1339 from rfl, totK_node, atot1308, atot1339]
  decide +kernel

theorem arows1403 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1403 = true := by
  rw [show A10K2.u1403 = KTree.node A10K2.u1371 (nat_lit 19024018) (nat_lit 15235736758) (nat_lit 0) A10K2.u1402 from rfl, allE_node, arows1371, irow1403, arows1402]
  all_goals rfl

theorem atot1403 : totK PA10K2 A10K2.u1403 = [0, 0, 7359660766381, 45605311271481, 103178503657406, 101423297425548, 42730664020837, 8285548611371, 802947949978, 30605747850] := by
  rw [show A10K2.u1403 = KTree.node A10K2.u1371 (nat_lit 19024018) (nat_lit 15235736758) (nat_lit 0) A10K2.u1402 from rfl, totK_node, atot1371, atot1402]
  decide +kernel

theorem arows1467 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1467 = true := by
  rw [show A10K2.u1467 = KTree.node A10K2.u1435 (nat_lit 19973957) (nat_lit 6286762494) (nat_lit 0) A10K2.u1466 from rfl, allE_node, arows1435, irow1467, arows1466]
  all_goals rfl

theorem atot1467 : totK PA10K2 A10K2.u1467 = [0, 0, 5649204368835, 38863766299376, 96933255208611, 104562565861356, 47795900631639, 9120771922453, 684315512749, 11205006771] := by
  rw [show A10K2.u1467 = KTree.node A10K2.u1435 (nat_lit 19973957) (nat_lit 6286762494) (nat_lit 0) A10K2.u1466 from rfl, totK_node, atot1435, atot1466]
  decide +kernel

theorem arows1530 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1530 = true := by
  rw [show A10K2.u1530 = KTree.node A10K2.u1498 (nat_lit 20644737) (nat_lit 10346570470) (nat_lit 0) A10K2.u1529 from rfl, allE_node, arows1498, irow1530, arows1529]
  all_goals rfl

theorem atot1530 : totK PA10K2 A10K2.u1530 = [0, 3079826674364, 22381766579644, 65864384161194, 100529252668093, 82072311775579, 32026385733588, 5352073908863, 377933763513, 5976421810] := by
  rw [show A10K2.u1530 = KTree.node A10K2.u1498 (nat_lit 20644737) (nat_lit 10346570470) (nat_lit 0) A10K2.u1529 from rfl, totK_node, atot1498, atot1529]
  decide +kernel

theorem arows1596 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1596 = true := by
  rw [show A10K2.u1596 = KTree.node A10K2.u1564 (nat_lit 25465629) (nat_lit 4835018972) (nat_lit 0) A10K2.u1595 from rfl, allE_node, arows1564, irow1596, arows1595]
  all_goals rfl

theorem atot1596 : totK PA10K2 A10K2.u1596 = [0, 5119424307113, 34467487037112, 88679021716264, 106896244702446, 59302119403529, 13883564853288, 1340530637535, 41810754621, 0] := by
  rw [show A10K2.u1596 = KTree.node A10K2.u1564 (nat_lit 25465629) (nat_lit 4835018972) (nat_lit 0) A10K2.u1595 from rfl, totK_node, atot1564, atot1595]
  decide +kernel

theorem arows1659 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1659 = true := by
  rw [show A10K2.u1659 = KTree.node A10K2.u1627 (nat_lit 26102102) (nat_lit 8907601558) (nat_lit 0) A10K2.u1658 from rfl, allE_node, arows1627, irow1659, arows1658]
  all_goals rfl

theorem atot1659 : totK PA10K2 A10K2.u1659 = [0, 6055495322378, 39544400490627, 97015214211333, 106561448923513, 48465907467162, 8031842460783, 488860868112, 6239673734, 0] := by
  rw [show A10K2.u1659 = KTree.node A10K2.u1627 (nat_lit 26102102) (nat_lit 8907601558) (nat_lit 0) A10K2.u1658 from rfl, totK_node, atot1627, atot1658]
  decide +kernel

theorem arows1723 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1723 = true := by
  rw [show A10K2.u1723 = KTree.node A10K2.u1691 (nat_lit 26618016) (nat_lit 8379026097) (nat_lit 0) A10K2.u1722 from rfl, allE_node, arows1691, irow1723, arows1722]
  all_goals rfl

theorem atot1723 : totK PA10K2 A10K2.u1723 = [0, 2296331471068, 23787361366580, 79696596751081, 113400534687369, 67549308851320, 15736442425407, 1516779105085, 42551283831, 0] := by
  rw [show A10K2.u1723 = KTree.node A10K2.u1691 (nat_lit 26618016) (nat_lit 8379026097) (nat_lit 0) A10K2.u1722 from rfl, totK_node, atot1691, atot1722]
  decide +kernel

theorem arows1786 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1786 = true := by
  rw [show A10K2.u1786 = KTree.node A10K2.u1754 (nat_lit 27960567) (nat_lit 13803863588) (nat_lit 0) A10K2.u1785 from rfl, allE_node, arows1754, irow1786, arows1785]
  all_goals rfl

theorem atot1786 : totK PA10K2 A10K2.u1786 = [0, 0, 11272646593083, 61681924111089, 118558195914124, 90573396640686, 23958495315165, 2270926936248, 61502250152, 0] := by
  rw [show A10K2.u1786 = KTree.node A10K2.u1754 (nat_lit 27960567) (nat_lit 13803863588) (nat_lit 0) A10K2.u1785 from rfl, totK_node, atot1754, atot1785]
  decide +kernel

theorem arows1851 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1851 = true := by
  rw [show A10K2.u1851 = KTree.node A10K2.u1819 (nat_lit 29360391) (nat_lit 10625156513) (nat_lit 0) A10K2.u1850 from rfl, allE_node, arows1819, irow1851, arows1850]
  all_goals rfl

theorem atot1851 : totK PA10K2 A10K2.u1851 = [0, 6057296600667, 32520431720593, 71738178533660, 90213610443857, 71449774834634, 28622251533075, 5186390811663, 355404831818, 6354482628] := by
  rw [show A10K2.u1851 = KTree.node A10K2.u1819 (nat_lit 29360391) (nat_lit 10625156513) (nat_lit 0) A10K2.u1850 from rfl, totK_node, atot1819, atot1850]
  decide +kernel

theorem arows1914 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1914 = true := by
  rw [show A10K2.u1914 = KTree.node A10K2.u1882 (nat_lit 29829040) (nat_lit 12008804521) (nat_lit 0) A10K2.u1913 from rfl, allE_node, arows1882, irow1914, arows1913]
  all_goals rfl

theorem atot1914 : totK PA10K2 A10K2.u1914 = [0, 4457728465308, 32985193096517, 90551970184027, 112007847465232, 60240357509194, 12907496574409, 1164815979335, 36134558889, 0] := by
  rw [show A10K2.u1914 = KTree.node A10K2.u1882 (nat_lit 29829040) (nat_lit 12008804521) (nat_lit 0) A10K2.u1913 from rfl, totK_node, atot1882, atot1913]
  decide +kernel

theorem arows1978 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1978 = true := by
  rw [show A10K2.u1978 = KTree.node A10K2.u1946 (nat_lit 30962221) (nat_lit 5312868095) (nat_lit 0) A10K2.u1977 from rfl, allE_node, arows1946, irow1978, arows1977]
  all_goals rfl

theorem atot1978 : totK PA10K2 A10K2.u1978 = [0, 6392439720472, 40317940767868, 96979241969811, 107885094983870, 53592360842453, 10288461663860, 665024467218, 8047840951, 0] := by
  rw [show A10K2.u1978 = KTree.node A10K2.u1946 (nat_lit 30962221) (nat_lit 5312868095) (nat_lit 0) A10K2.u1977 from rfl, totK_node, atot1946, atot1977]
  decide +kernel

theorem arows2041 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2041 = true := by
  rw [show A10K2.u2041 = KTree.node A10K2.u2009 (nat_lit 31401109) (nat_lit 6567208353) (nat_lit 0) A10K2.u2040 from rfl, allE_node, arows2009, irow2041, arows2040]
  all_goals rfl

theorem atot2041 : totK PA10K2 A10K2.u2041 = [2808829852973, 15442380140721, 38106721165080, 68171982745022, 92880893764615, 71316042465469, 22903076929333, 2620557107558, 87935641093, 0] := by
  rw [show A10K2.u2041 = KTree.node A10K2.u2009 (nat_lit 31401109) (nat_lit 6567208353) (nat_lit 0) A10K2.u2040 from rfl, totK_node, atot2009, atot2040]
  decide +kernel

theorem arows2109 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2109 = true := by
  rw [show A10K2.u2109 = KTree.node A10K2.u2077 (nat_lit 38623496) (nat_lit 11626133604) (nat_lit 0) A10K2.u2108 from rfl, allE_node, arows2077, irow2109, arows2108]
  all_goals rfl

theorem atot2109 : totK PA10K2 A10K2.u2109 = [4269947457986, 30353399106423, 83484704962899, 108604238491569, 65550379745800, 16017264807636, 1472111660733, 42943767608, 0, 0] := by
  rw [show A10K2.u2109 = KTree.node A10K2.u2077 (nat_lit 38623496) (nat_lit 11626133604) (nat_lit 0) A10K2.u2108 from rfl, totK_node, atot2077, atot2108]
  decide +kernel

theorem arows2172 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2172 = true := by
  rw [show A10K2.u2172 = KTree.node A10K2.u2140 (nat_lit 38971093) (nat_lit 6149190315) (nat_lit 0) A10K2.u2171 from rfl, allE_node, arows2140, irow2172, arows2171]
  all_goals rfl

theorem atot2172 : totK PA10K2 A10K2.u2172 = [6063514277977, 39045290975791, 95217867993638, 104986754807387, 49707990356024, 9013949561184, 607738884148, 6354482628, 0, 0] := by
  rw [show A10K2.u2172 = KTree.node A10K2.u2140 (nat_lit 38971093) (nat_lit 6149190315) (nat_lit 0) A10K2.u2171 from rfl, totK_node, atot2140, atot2171]
  decide +kernel

theorem arows2236 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2236 = true := by
  rw [show A10K2.u2236 = KTree.node A10K2.u2204 (nat_lit 39560482) (nat_lit 13708722487) (nat_lit 0) A10K2.u2235 from rfl, allE_node, arows2204, irow2236, arows2235]
  all_goals rfl

theorem atot2236 : totK PA10K2 A10K2.u2236 = [4935928765675, 34552763161655, 90832917942914, 110536880483834, 61824682678001, 14276253885072, 1123101679300, 14159155365, 0, 0] := by
  rw [show A10K2.u2236 = KTree.node A10K2.u2204 (nat_lit 39560482) (nat_lit 13708722487) (nat_lit 0) A10K2.u2235 from rfl, totK_node, atot2204, atot2235]
  decide +kernel

theorem arows2299 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2299 = true := by
  rw [show A10K2.u2299 = KTree.node A10K2.u2267 (nat_lit 40514971) (nat_lit 9859220283) (nat_lit 0) A10K2.u2298 from rfl, allE_node, arows2267, irow2299, arows2298]
  all_goals rfl

theorem atot2299 : totK PA10K2 A10K2.u2299 = [0, 7384145492042, 46189056851579, 105866717041026, 104678989083302, 41344104490577, 5600588439912, 210483513670, 0, 0] := by
  rw [show A10K2.u2299 = KTree.node A10K2.u2267 (nat_lit 40514971) (nat_lit 9859220283) (nat_lit 0) A10K2.u2298 from rfl, totK_node, atot2267, atot2298]
  decide +kernel

theorem arows2364 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2364 = true := by
  rw [show A10K2.u2364 = KTree.node A10K2.u2332 (nat_lit 40945676) (nat_lit 11759478708) (nat_lit 0) A10K2.u2363 from rfl, allE_node, arows2332, irow2364, arows2363]
  all_goals rfl

theorem atot2364 : totK PA10K2 A10K2.u2364 = [0, 5670732233300, 36874981784012, 90491734293986, 102855286107009, 54457867633628, 12933561642790, 1324543638625, 42686146280, 0] := by
  rw [show A10K2.u2364 = KTree.node A10K2.u2332 (nat_lit 40945676) (nat_lit 11759478708) (nat_lit 0) A10K2.u2363 from rfl, totK_node, atot2332, atot2363]
  decide +kernel

theorem arows2427 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2427 = true := by
  rw [show A10K2.u2427 = KTree.node A10K2.u2395 (nat_lit 41495219) (nat_lit 10261700677) (nat_lit 0) A10K2.u2426 from rfl, allE_node, arows2395, irow2427, arows2426]
  all_goals rfl

theorem atot2427 : totK PA10K2 A10K2.u2427 = [796021182214, 8495089565808, 40650958841668, 95298599224773, 106902427882732, 50291966344981, 8509134505810, 508772772652, 6354482628, 0] := by
  rw [show A10K2.u2427 = KTree.node A10K2.u2395 (nat_lit 41495219) (nat_lit 10261700677) (nat_lit 0) A10K2.u2426 from rfl, totK_node, atot2395, atot2426]
  decide +kernel

theorem arows2491 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2491 = true := by
  rw [show A10K2.u2491 = KTree.node A10K2.u2459 (nat_lit 42228508) (nat_lit 11755629575) (nat_lit 0) A10K2.u2490 from rfl, allE_node, arows2459, irow2491, arows2490]
  all_goals rfl

theorem atot2491 : totK PA10K2 A10K2.u2491 = [5830248069218, 37675842388035, 91367881188848, 103094075183602, 54894012617188, 12960273724269, 1297925816300, 41810754621, 0, 0] := by
  rw [show A10K2.u2491 = KTree.node A10K2.u2459 (nat_lit 42228508) (nat_lit 11755629575) (nat_lit 0) A10K2.u2490 from rfl, totK_node, atot2459, atot2490]
  decide +kernel

theorem arows2554 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2554 = true := by
  rw [show A10K2.u2554 = KTree.node A10K2.u2522 (nat_lit 42809509) (nat_lit 7264329585) (nat_lit 0) A10K2.u2553 from rfl, allE_node, arows2522, irow2554, arows2553]
  all_goals rfl

theorem atot2554 : totK PA10K2 A10K2.u2554 = [4170502431274, 29943163245548, 83500426308186, 109620547777244, 66005937098955, 15971863222617, 1469837313151, 42943767608, 0, 0] := by
  rw [show A10K2.u2554 = KTree.node A10K2.u2522 (nat_lit 42809509) (nat_lit 7264329585) (nat_lit 0) A10K2.u2553 from rfl, totK_node, atot2522, atot2553]
  decide +kernel

theorem arows2620 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2620 = true := by
  rw [show A10K2.u2620 = KTree.node A10K2.u2588 (nat_lit 43140243) (nat_lit 10993652984) (nat_lit 0) A10K2.u2619 from rfl, allE_node, arows2588, irow2620, arows2619]
  all_goals rfl

theorem atot2620 : totK PA10K2 A10K2.u2620 = [5748398962592, 39742003838243, 99227623723046, 107224294356551, 46422670788611, 6852133327867, 287001740518, 0, 0, 0] := by
  rw [show A10K2.u2620 = KTree.node A10K2.u2588 (nat_lit 43140243) (nat_lit 10993652984) (nat_lit 0) A10K2.u2619 from rfl, totK_node, atot2588, atot2619]
  decide +kernel

theorem arows2683 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2683 = true := by
  rw [show A10K2.u2683 = KTree.node A10K2.u2651 (nat_lit 44640439) (nat_lit 13866747009) (nat_lit 0) A10K2.u2682 from rfl, allE_node, arows2651, irow2683, arows2682]
  all_goals rfl

theorem atot2683 : totK PA10K2 A10K2.u2683 = [0, 10344955506213, 57186496461927, 113682509582062, 93997711446169, 28895242448761, 3182882631403, 92464308985, 0, 0] := by
  rw [show A10K2.u2683 = KTree.node A10K2.u2651 (nat_lit 44640439) (nat_lit 13866747009) (nat_lit 0) A10K2.u2682 from rfl, totK_node, atot2651, atot2682]
  decide +kernel

theorem arows2747 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2747 = true := by
  rw [show A10K2.u2747 = KTree.node A10K2.u2715 (nat_lit 45220115) (nat_lit 8604301768) (nat_lit 0) A10K2.u2746 from rfl, allE_node, arows2715, irow2747, arows2746]
  all_goals rfl

theorem atot2747 : totK PA10K2 A10K2.u2747 = [0, 6194671456178, 43005196931252, 105215413134315, 106422184408734, 39551515268265, 5187872546237, 221131243280, 0, 0] := by
  rw [show A10K2.u2747 = KTree.node A10K2.u2715 (nat_lit 45220115) (nat_lit 8604301768) (nat_lit 0) A10K2.u2746 from rfl, totK_node, atot2715, atot2746]
  decide +kernel

theorem arows2810 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2810 = true := by
  rw [show A10K2.u2810 = KTree.node A10K2.u2778 (nat_lit 46370452) (nat_lit 5053540340) (nat_lit 0) A10K2.u2809 from rfl, allE_node, arows2778, irow2810, arows2809]
  all_goals rfl

theorem atot2810 : totK PA10K2 A10K2.u2810 = [5313003151528, 33395688002821, 81966180207524, 99507526146758, 64140083793152, 22972379438954, 4639772153366, 421097122752, 6354482628, 0] := by
  rw [show A10K2.u2810 = KTree.node A10K2.u2778 (nat_lit 46370452) (nat_lit 5053540340) (nat_lit 0) A10K2.u2809 from rfl, totK_node, atot2778, atot2809]
  decide +kernel

theorem arows2875 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2875 = true := by
  rw [show A10K2.u2875 = KTree.node A10K2.u2843 (nat_lit 46895685) (nat_lit 5657713833) (nat_lit 0) A10K2.u2874 from rfl, allE_node, arows2843, irow2875, arows2874]
  all_goals rfl

theorem atot2875 : totK PA10K2 A10K2.u2875 = [5205627883234, 34980172204785, 89326621088038, 106951643845548, 60274860649139, 14508255264415, 1391670938804, 42943767608, 0, 0] := by
  rw [show A10K2.u2875 = KTree.node A10K2.u2843 (nat_lit 46895685) (nat_lit 5657713833) (nat_lit 0) A10K2.u2874 from rfl, totK_node, atot2843, atot2874]
  decide +kernel

theorem arows2938 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2938 = true := by
  rw [show A10K2.u2938 = KTree.node A10K2.u2906 (nat_lit 47833142) (nat_lit 16097883093) (nat_lit 0) A10K2.u2937 from rfl, allE_node, arows2906, irow2938, arows2937]
  all_goals rfl

theorem atot2938 : totK PA10K2 A10K2.u2938 = [6393459185742, 40274814472683, 96485024915913, 107117781947102, 54079076985480, 10989875504775, 739224744581, 7007974415, 0, 0] := by
  rw [show A10K2.u2938 = KTree.node A10K2.u2906 (nat_lit 47833142) (nat_lit 16097883093) (nat_lit 0) A10K2.u2937 from rfl, totK_node, atot2906, atot2937]
  decide +kernel

theorem arows3002 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3002 = true := by
  rw [show A10K2.u3002 = KTree.node A10K2.u2970 (nat_lit 48241723) (nat_lit 5531928538) (nat_lit 0) A10K2.u3001 from rfl, allE_node, arows2970, irow3002, arows3001]
  all_goals rfl

theorem atot3002 : totK PA10K2 A10K2.u3002 = [0, 8443622767109, 49980954105228, 108411327524862, 102551175570355, 39998623382131, 5522060619467, 222737551539, 0, 0] := by
  rw [show A10K2.u3002 = KTree.node A10K2.u2970 (nat_lit 48241723) (nat_lit 5531928538) (nat_lit 0) A10K2.u3001 from rfl, totK_node, atot2970, atot3001]
  decide +kernel

theorem arows3065 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3065 = true := by
  rw [show A10K2.u3065 = KTree.node A10K2.u3033 (nat_lit 48883163) (nat_lit 6850827727) (nat_lit 0) A10K2.u3064 from rfl, allE_node, arows3033, irow3065, arows3064]
  all_goals rfl

theorem atot3065 : totK PA10K2 A10K2.u3065 = [0, 6067524558161, 39163072787689, 95943560992926, 107747950745347, 53619431543775, 10169120122833, 672114372774, 7237400819, 0] := by
  rw [show A10K2.u3065 = KTree.node A10K2.u3033 (nat_lit 48883163) (nat_lit 6850827727) (nat_lit 0) A10K2.u3064 from rfl, totK_node, atot3033, atot3064]
  decide +kernel

theorem arows3132 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3132 = true := by
  rw [show A10K2.u3132 = KTree.node A10K2.u3100 (nat_lit 49867839) (nat_lit 14216893575) (nat_lit 0) A10K2.u3131 from rfl, allE_node, arows3100, irow3132, arows3131]
  all_goals rfl

theorem atot3132 : totK PA10K2 A10K2.u3132 = [0, 6393459185742, 40740885291744, 98023606200683, 107826300070749, 52180532655630, 9491013580156, 584373415302, 7380853412, 0] := by
  rw [show A10K2.u3132 = KTree.node A10K2.u3100 (nat_lit 49867839) (nat_lit 14216893575) (nat_lit 0) A10K2.u3131 from rfl, totK_node, atot3100, atot3131]
  decide +kernel

theorem arows3195 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3195 = true := by
  rw [show A10K2.u3195 = KTree.node A10K2.u3163 (nat_lit 50298376) (nat_lit 14212529203) (nat_lit 0) A10K2.u3194 from rfl, allE_node, arows3163, irow3195, arows3194]
  all_goals rfl

theorem atot3195 : totK PA10K2 A10K2.u3195 = [0, 4387167801734, 29262428602076, 77927586417919, 104491546385009, 71997946790391, 21734205655103, 2499478568632, 87362355661, 0] := by
  rw [show A10K2.u3195 = KTree.node A10K2.u3163 (nat_lit 50298376) (nat_lit 14212529203) (nat_lit 0) A10K2.u3194 from rfl, totK_node, atot3163, atot3194]
  decide +kernel

theorem arows3259 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3259 = true := by
  rw [show A10K2.u3259 = KTree.node A10K2.u3227 (nat_lit 55426270) (nat_lit 11350878210) (nat_lit 0) A10K2.u3258 from rfl, allE_node, arows3227, irow3259, arows3258]
  all_goals rfl

theorem atot3259 : totK PA10K2 A10K2.u3259 = [0, 3747273612289, 28794313032501, 83464387754932, 110737434788557, 65826245868315, 15522921440051, 1436236341045, 42943767608, 0] := by
  rw [show A10K2.u3259 = KTree.node A10K2.u3227 (nat_lit 55426270) (nat_lit 11350878210) (nat_lit 0) A10K2.u3258 from rfl, totK_node, atot3227, atot3258]
  decide +kernel

theorem arows3322 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3322 = true := by
  rw [show A10K2.u3322 = KTree.node A10K2.u3290 (nat_lit 55859873) (nat_lit 7719112473) (nat_lit 0) A10K2.u3321 from rfl, allE_node, arows3290, irow3322, arows3321]
  all_goals rfl

theorem atot3322 : totK PA10K2 A10K2.u3322 = [0, 6287221779511, 40988033510417, 99065080328268, 106300752236540, 46978009155368, 7614279180014, 443888010975, 6354482628, 0] := by
  rw [show A10K2.u3322 = KTree.node A10K2.u3290 (nat_lit 55859873) (nat_lit 7719112473) (nat_lit 0) A10K2.u3321 from rfl, totK_node, atot3290, atot3321]
  decide +kernel

theorem arows3387 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3387 = true := by
  rw [show A10K2.u3387 = KTree.node A10K2.u3355 (nat_lit 56389278) (nat_lit 15213554017) (nat_lit 0) A10K2.u3386 from rfl, allE_node, arows3355, irow3387, arows3386]
  all_goals rfl

theorem atot3387 : totK PA10K2 A10K2.u3387 = [0, 3656557161077, 27573500087407, 81154235516996, 113335435532109, 73078203586106, 18361821121335, 1348436233718, 13590611789, 0] := by
  rw [show A10K2.u3387 = KTree.node A10K2.u3355 (nat_lit 56389278) (nat_lit 15213554017) (nat_lit 0) A10K2.u3386 from rfl, totK_node, atot3355, atot3386]
  decide +kernel

theorem arows3450 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3450 = true := by
  rw [show A10K2.u3450 = KTree.node A10K2.u3418 (nat_lit 57357672) (nat_lit 6344559884) (nat_lit 0) A10K2.u3449 from rfl, allE_node, arows3418, irow3450, arows3449]
  all_goals rfl

theorem atot3450 : totK PA10K2 A10K2.u3450 = [0, 0, 6496583381429, 40705050986767, 95920660206090, 102568862752176, 49767840719418, 11056396207741, 1093574218658, 36704093874] := by
  rw [show A10K2.u3450 = KTree.node A10K2.u3418 (nat_lit 57357672) (nat_lit 6344559884) (nat_lit 0) A10K2.u3449 from rfl, totK_node, atot3418, atot3449]
  decide +kernel

theorem arows3514 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3514 = true := by
  rw [show A10K2.u3514 = KTree.node A10K2.u3482 (nat_lit 57793178) (nat_lit 12666966908) (nat_lit 0) A10K2.u3513 from rfl, allE_node, arows3482, irow3514, arows3513]
  all_goals rfl

theorem atot3514 : totK PA10K2 A10K2.u3514 = [0, 0, 5657941778386, 39615010013952, 99613080553877, 106662491253920, 45702165114874, 7473728024363, 470659968216, 5982052406] := by
  rw [show A10K2.u3514 = KTree.node A10K2.u3482 (nat_lit 57793178) (nat_lit 12666966908) (nat_lit 0) A10K2.u3513 from rfl, totK_node, atot3482, atot3513]
  decide +kernel

theorem arows3577 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3577 = true := by
  rw [show A10K2.u3577 = KTree.node A10K2.u3545 (nat_lit 58428485) (nat_lit 3836024680) (nat_lit 32) A10K2.u3576 from rfl, allE_node, arows3545, irow3577, arows3576]
  all_goals rfl

theorem atot3577 : totK PA10K2 A10K2.u3577 = [0, 4328003150587, 29982219526203, 78366963015956, 99617342117159, 68599264583001, 26689881289412, 4834957423655, 352012091003, 6354482628] := by
  rw [show A10K2.u3577 = KTree.node A10K2.u3545 (nat_lit 58428485) (nat_lit 3836024680) (nat_lit 32) A10K2.u3576 from rfl, totK_node, atot3545, atot3576]
  decide +kernel

theorem arows3643 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3643 = true := by
  rw [show A10K2.u3643 = KTree.node A10K2.u3611 (nat_lit 59356940) (nat_lit 9705785245) (nat_lit 0) A10K2.u3642 from rfl, allE_node, arows3611, irow3643, arows3642]
  all_goals rfl

theorem atot3643 : totK PA10K2 A10K2.u3643 = [0, 6024247250820, 39536439026965, 97831978104633, 108331035557026, 49457103657706, 8235007287535, 472149665200, 5676195732, 0] := by
  rw [show A10K2.u3643 = KTree.node A10K2.u3611 (nat_lit 59356940) (nat_lit 9705785245) (nat_lit 0) A10K2.u3642 from rfl, totK_node, atot3611, atot3642]
  decide +kernel

theorem arows3706 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3706 = true := by
  rw [show A10K2.u3706 = KTree.node A10K2.u3674 (nat_lit 59771754) (nat_lit 8832458926) (nat_lit 0) A10K2.u3705 from rfl, allE_node, arows3674, irow3706, arows3705]
  all_goals rfl

theorem atot3706 : totK PA10K2 A10K2.u3706 = [0, 5893125426391, 35883308835679, 86836828896251, 103718466394846, 59812721600293, 14496810127410, 1406111455614, 42943767608, 0] := by
  rw [show A10K2.u3706 = KTree.node A10K2.u3674 (nat_lit 59771754) (nat_lit 8832458926) (nat_lit 0) A10K2.u3705 from rfl, totK_node, atot3674, atot3705]
  decide +kernel

theorem arows3770 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3770 = true := by
  rw [show A10K2.u3770 = KTree.node A10K2.u3738 (nat_lit 60211270) (nat_lit 13086884904) (nat_lit 0) A10K2.u3769 from rfl, allE_node, arows3738, irow3770, arows3769]
  all_goals rfl

theorem atot3770 : totK PA10K2 A10K2.u3770 = [0, 295989007569, 16092267111397, 73708992936159, 120955012602076, 76072915469133, 16148674200800, 1224140722348, 18255270229, 0] := by
  rw [show A10K2.u3770 = KTree.node A10K2.u3738 (nat_lit 60211270) (nat_lit 13086884904) (nat_lit 0) A10K2.u3769 from rfl, totK_node, atot3738, atot3769]
  decide +kernel

theorem arows3833 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3833 = true := by
  rw [show A10K2.u3833 = KTree.node A10K2.u3801 (nat_lit 61585732) (nat_lit 12205195203) (nat_lit 0) A10K2.u3832 from rfl, allE_node, arows3801, irow3833, arows3832]
  all_goals rfl

theorem atot3833 : totK PA10K2 A10K2.u3833 = [0, 0, 10318960980193, 58023083455975, 116234490125061, 94454436707337, 27453167711192, 2902576530261, 92920870656, 0] := by
  rw [show A10K2.u3833 = KTree.node A10K2.u3801 (nat_lit 61585732) (nat_lit 12205195203) (nat_lit 0) A10K2.u3832 from rfl, totK_node, atot3801, atot3832]
  decide +kernel

theorem arows3898 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3898 = true := by
  rw [show A10K2.u3898 = KTree.node A10K2.u3866 (nat_lit 62315040) (nat_lit 13047187047) (nat_lit 0) A10K2.u3897 from rfl, allE_node, arows3866, irow3898, arows3897]
  all_goals rfl

theorem atot3898 : totK PA10K2 A10K2.u3898 = [0, 4451106476601, 26610758678161, 66641367487349, 93905394895469, 78907187339402, 31678053584055, 5676664798237, 402496298378, 6354482628] := by
  rw [show A10K2.u3898 = KTree.node A10K2.u3866 (nat_lit 62315040) (nat_lit 13047187047) (nat_lit 0) A10K2.u3897 from rfl, totK_node, atot3866, atot3897]
  decide +kernel

theorem arows3961 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3961 = true := by
  rw [show A10K2.u3961 = KTree.node A10K2.u3929 (nat_lit 63555507) (nat_lit 9397451241) (nat_lit 0) A10K2.u3960 from rfl, allE_node, arows3929, irow3961, arows3960]
  all_goals rfl

theorem atot3961 : totK PA10K2 A10K2.u3961 = [0, 6067524558161, 38873834911333, 95257745999890, 108293052340638, 54703159552337, 10524584147887, 689520025281, 7903172220, 0] := by
  rw [show A10K2.u3961 = KTree.node A10K2.u3929 (nat_lit 63555507) (nat_lit 9397451241) (nat_lit 0) A10K2.u3960 from rfl, totK_node, atot3929, atot3960]
  decide +kernel

theorem arows4025 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4025 = true := by
  rw [show A10K2.u4025 = KTree.node A10K2.u3993 (nat_lit 64503922) (nat_lit 6151356710) (nat_lit 0) A10K2.u4024 from rfl, allE_node, arows3993, irow4025, arows4024]
  all_goals rfl

theorem atot4025 : totK PA10K2 A10K2.u4025 = [0, 6393459185742, 38938244911503, 91765495040965, 104199048885922, 57634760808571, 14003388135669, 1373397828753, 42943767608, 0] := by
  rw [show A10K2.u4025 = KTree.node A10K2.u3993 (nat_lit 64503922) (nat_lit 6151356710) (nat_lit 0) A10K2.u4024 from rfl, totK_node, atot3993, atot4024]
  decide +kernel

theorem arows4088 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4088 = true := by
  rw [show A10K2.u4088 = KTree.node A10K2.u4056 (nat_lit 64873682) (nat_lit 15653405069) (nat_lit 0) A10K2.u4087 from rfl, allE_node, arows4056, irow4088, arows4087]
  all_goals rfl

theorem atot4088 : totK PA10K2 A10K2.u4088 = [2338692983822, 12465376030733, 32859687728793, 67201557272766, 98252428542692, 75029252075607, 23383743898072, 2624947833962, 87935641093, 0] := by
  rw [show A10K2.u4088 = KTree.node A10K2.u4056 (nat_lit 64873682) (nat_lit 15653405069) (nat_lit 0) A10K2.u4087 from rfl, totK_node, atot4056, atot4087]
  decide +kernel

theorem arows4157 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4157 = true := by
  rw [show A10K2.u4157 = KTree.node A10K2.u4125 (nat_lit 67387731) (nat_lit 8367207111) (nat_lit 0) A10K2.u4156 from rfl, allE_node, arows4125, irow4157, arows4156]
  all_goals rfl

theorem atot4157 : totK PA10K2 A10K2.u4157 = [4778295391433, 32019446563126, 84814129440414, 107881232883988, 63162095698551, 14993562649837, 1397406780757, 41810754621, 0, 0] := by
  rw [show A10K2.u4157 = KTree.node A10K2.u4125 (nat_lit 67387731) (nat_lit 8367207111) (nat_lit 0) A10K2.u4156 from rfl, totK_node, atot4125, atot4156]
  decide +kernel

theorem arows4220 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4220 = true := by
  rw [show A10K2.u4220 = KTree.node A10K2.u4188 (nat_lit 68311606) (nat_lit 8939257634) (nat_lit 0) A10K2.u4219 from rfl, allE_node, arows4188, irow4220, arows4219]
  all_goals rfl

theorem atot4220 : totK PA10K2 A10K2.u4220 = [5118801067077, 36768245486367, 95313622696437, 108121021694640, 51068826300672, 9028012080643, 516088936286, 0, 0, 0] := by
  rw [show A10K2.u4220 = KTree.node A10K2.u4188 (nat_lit 68311606) (nat_lit 8939257634) (nat_lit 0) A10K2.u4219 from rfl, totK_node, atot4188, atot4219]
  decide +kernel

theorem arows4284 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4284 = true := by
  rw [show A10K2.u4284 = KTree.node A10K2.u4252 (nat_lit 68944816) (nat_lit 14652486819) (nat_lit 0) A10K2.u4283 from rfl, allE_node, arows4252, irow4284, arows4283]
  all_goals rfl

theorem atot4284 : totK PA10K2 A10K2.u4284 = [4449301618478, 30507999831897, 81863862568860, 107075471220402, 69091679692629, 20193962888180, 2373374663938, 87138942771, 0, 0] := by
  rw [show A10K2.u4284 = KTree.node A10K2.u4252 (nat_lit 68944816) (nat_lit 14652486819) (nat_lit 0) A10K2.u4283 from rfl, totK_node, atot4252, atot4283]
  decide +kernel

theorem arows4347 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4347 = true := by
  rw [show A10K2.u4347 = KTree.node A10K2.u4315 (nat_lit 69435337) (nat_lit 5635689344) (nat_lit 0) A10K2.u4346 from rfl, allE_node, arows4315, irow4347, arows4346]
  all_goals rfl

theorem atot4347 : totK PA10K2 A10K2.u4347 = [0, 5407904574212, 36055354913144, 91151874143071, 105926232682084, 54525428918633, 11899512491608, 1132165336562, 36134558889, 0] := by
  rw [show A10K2.u4347 = KTree.node A10K2.u4315 (nat_lit 69435337) (nat_lit 5635689344) (nat_lit 0) A10K2.u4346 from rfl, totK_node, atot4315, atot4346]
  decide +kernel

theorem arows4412 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4412 = true := by
  rw [show A10K2.u4412 = KTree.node A10K2.u4380 (nat_lit 70388545) (nat_lit 8816870068) (nat_lit 0) A10K2.u4411 from rfl, allE_node, arows4380, irow4412, arows4411]
  all_goals rfl

theorem atot4412 : totK PA10K2 A10K2.u4412 = [0, 5948003826011, 41333725423994, 102509070052087, 107244171145682, 43063873343971, 6461782738150, 368813328133, 5676195732, 0] := by
  rw [show A10K2.u4412 = KTree.node A10K2.u4380 (nat_lit 70388545) (nat_lit 8816870068) (nat_lit 0) A10K2.u4411 from rfl, totK_node, atot4380, atot4411]
  decide +kernel

theorem arows4475 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4475 = true := by
  rw [show A10K2.u4475 = KTree.node A10K2.u4443 (nat_lit 71034363) (nat_lit 6260608234) (nat_lit 0) A10K2.u4474 from rfl, allE_node, arows4443, irow4475, arows4474]
  all_goals rfl

theorem atot4475 : totK PA10K2 A10K2.u4475 = [4682757634830, 30576829477117, 77155877556735, 97304205135722, 68120820334988, 27101664075494, 5085647706764, 366794883915, 5976421810, 0] := by
  rw [show A10K2.u4475 = KTree.node A10K2.u4443 (nat_lit 71034363) (nat_lit 6260608234) (nat_lit 0) A10K2.u4474 from rfl, totK_node, atot4443, atot4474]
  decide +kernel

theorem arows4539 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4539 = true := by
  rw [show A10K2.u4539 = KTree.node A10K2.u4507 (nat_lit 72234678) (nat_lit 14996216699) (nat_lit 0) A10K2.u4538 from rfl, allE_node, arows4507, irow4539, arows4538]
  all_goals rfl

theorem atot4539 : totK PA10K2 A10K2.u4539 = [4757346086591, 31849397784224, 83974613851892, 107184387256242, 65230794296941, 16048153946393, 1488041076629, 42943767608, 0, 0] := by
  rw [show A10K2.u4539 = KTree.node A10K2.u4507 (nat_lit 72234678) (nat_lit 14996216699) (nat_lit 0) A10K2.u4538 from rfl, totK_node, atot4507, atot4538]
  decide +kernel

theorem arows4602 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4602 = true := by
  rw [show A10K2.u4602 = KTree.node A10K2.u4570 (nat_lit 72697171) (nat_lit 10511612314) (nat_lit 0) A10K2.u4601 from rfl, allE_node, arows4570, irow4602, arows4601]
  all_goals rfl

theorem atot4602 : totK PA10K2 A10K2.u4602 = [5020404728225, 35921318346494, 94576807512380, 109856076719138, 52523594849873, 9235350087787, 608746142843, 6354482628, 0, 0] := by
  rw [show A10K2.u4602 = KTree.node A10K2.u4570 (nat_lit 72697171) (nat_lit 10511612314) (nat_lit 0) A10K2.u4601 from rfl, totK_node, atot4570, atot4601]
  decide +kernel

theorem arows4668 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4668 = true := by
  rw [show A10K2.u4668 = KTree.node A10K2.u4636 (nat_lit 73342363) (nat_lit 8280335586) (nat_lit 0) A10K2.u4667 from rfl, allE_node, arows4636, irow4668, arows4667]
  all_goals rfl

theorem atot4668 : totK PA10K2 A10K2.u4668 = [2245477168038, 20306606958821, 68807510036946, 109686899148186, 83436753461201, 27140824556159, 3244619642708, 118131726576, 0, 0] := by
  rw [show A10K2.u4668 = KTree.node A10K2.u4636 (nat_lit 73342363) (nat_lit 8280335586) (nat_lit 0) A10K2.u4667 from rfl, totK_node, atot4636, atot4667]
  decide +kernel

theorem arows4731 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4731 = true := by
  rw [show A10K2.u4731 = KTree.node A10K2.u4699 (nat_lit 74284279) (nat_lit 14693586544) (nat_lit 0) A10K2.u4730 from rfl, allE_node, arows4699, irow4731, arows4730]
  all_goals rfl

theorem atot4731 : totK PA10K2 A10K2.u4731 = [0, 4708635872390, 33469953714570, 88608967625733, 107568514908883, 59690963038080, 13963386208268, 1369494573296, 42686146280, 0] := by
  rw [show A10K2.u4731 = KTree.node A10K2.u4699 (nat_lit 74284279) (nat_lit 14693586544) (nat_lit 0) A10K2.u4730 from rfl, totK_node, atot4699, atot4730]
  decide +kernel

theorem arows4795 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4795 = true := by
  rw [show A10K2.u4795 = KTree.node A10K2.u4763 (nat_lit 74714554) (nat_lit 11439761273) (nat_lit 0) A10K2.u4794 from rfl, allE_node, arows4763, irow4795, arows4794]
  all_goals rfl

theorem atot4795 : totK PA10K2 A10K2.u4795 = [0, 6623610942225, 41874263555564, 99430541123248, 105263998905308, 45137625513878, 7266679341577, 444329484073, 6354482628, 0] := by
  rw [show A10K2.u4795 = KTree.node A10K2.u4763 (nat_lit 74714554) (nat_lit 11439761273) (nat_lit 0) A10K2.u4794 from rfl, totK_node, atot4763, atot4794]
  decide +kernel

theorem arows4858 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4858 = true := by
  rw [show A10K2.u4858 = KTree.node A10K2.u4826 (nat_lit 75530824) (nat_lit 13706559810) (nat_lit 0) A10K2.u4857 from rfl, allE_node, arows4826, irow4858, arows4857]
  all_goals rfl

theorem atot4858 : totK PA10K2 A10K2.u4858 = [5740492290035, 35482578088258, 84664159554792, 99349697342065, 62616665058713, 21096460345513, 2837154072725, 111757921133, 0, 0] := by
  rw [show A10K2.u4858 = KTree.node A10K2.u4826 (nat_lit 75530824) (nat_lit 13706559810) (nat_lit 0) A10K2.u4857 from rfl, totK_node, atot4826, atot4857]
  decide +kernel

theorem arows4923 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4923 = true := by
  rw [show A10K2.u4923 = KTree.node A10K2.u4891 (nat_lit 76101476) (nat_lit 13067388287) (nat_lit 0) A10K2.u4922 from rfl, allE_node, arows4891, irow4923, arows4922]
  all_goals rfl

theorem atot4923 : totK PA10K2 A10K2.u4923 = [5753228580098, 36467520184806, 89315197457693, 104163189797407, 57302895285979, 13607194630448, 1329300621743, 41810754621, 0, 0] := by
  rw [show A10K2.u4923 = KTree.node A10K2.u4891 (nat_lit 76101476) (nat_lit 13067388287) (nat_lit 0) A10K2.u4922 from rfl, totK_node, atot4891, atot4922]
  decide +kernel

theorem arows4986 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4986 = true := by
  rw [show A10K2.u4986 = KTree.node A10K2.u4954 (nat_lit 76490390) (nat_lit 14938990363) (nat_lit 0) A10K2.u4985 from rfl, allE_node, arows4954, irow4986, arows4985]
  all_goals rfl

theorem atot4986 : totK PA10K2 A10K2.u4986 = [4097868149106, 29434251548093, 82069346176641, 108346352410381, 66064092501072, 16256121101835, 1512896682883, 42943767608, 0, 0] := by
  rw [show A10K2.u4986 = KTree.node A10K2.u4954 (nat_lit 76490390) (nat_lit 14938990363) (nat_lit 0) A10K2.u4985 from rfl, totK_node, atot4954, atot4985]
  decide +kernel

theorem arows5050 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5050 = true := by
  rw [show A10K2.u5050 = KTree.node A10K2.u5018 (nat_lit 76945504) (nat_lit 13669846470) (nat_lit 0) A10K2.u5049 from rfl, allE_node, arows5018, irow5050, arows5049]
  all_goals rfl

theorem atot5050 : totK PA10K2 A10K2.u5050 = [2343832716771, 23813961304722, 79314146525862, 112991349659739, 68555578075664, 16414730310679, 1542416862768, 42551283831, 0, 0] := by
  rw [show A10K2.u5050 = KTree.node A10K2.u5018 (nat_lit 76945504) (nat_lit 13669846470) (nat_lit 0) A10K2.u5049 from rfl, totK_node, atot5018, atot5049]
  decide +kernel

theorem arows5113 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5113 = true := by
  rw [show A10K2.u5113 = KTree.node A10K2.u5081 (nat_lit 78250788) (nat_lit 13711877624) (nat_lit 0) A10K2.u5112 from rfl, allE_node, arows5081, irow5113, arows5112]
  all_goals rfl

theorem atot5113 : totK PA10K2 A10K2.u5113 = [0, 9691077503165, 55568001928203, 113702867214279, 96353704881425, 30474448445662, 3293461052861, 94085857240, 0, 0] := by
  rw [show A10K2.u5113 = KTree.node A10K2.u5081 (nat_lit 78250788) (nat_lit 13711877624) (nat_lit 0) A10K2.u5112 from rfl, totK_node, atot5081, atot5112]
  decide +kernel

theorem arows5180 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5180 = true := by
  rw [show A10K2.u5180 = KTree.node A10K2.u5148 (nat_lit 78907940) (nat_lit 13558446609) (nat_lit 0) A10K2.u5179 from rfl, allE_node, arows5148, irow5180, arows5179]
  all_goals rfl

theorem atot5180 : totK PA10K2 A10K2.u5180 = [0, 6720022928073, 41954359733619, 98774473737712, 103312312563144, 43839285839507, 7788882721190, 568825903321, 6354482628, 0] := by
  rw [show A10K2.u5180 = KTree.node A10K2.u5148 (nat_lit 78907940) (nat_lit 13558446609) (nat_lit 0) A10K2.u5179 from rfl, totK_node, atot5148, atot5179]
  decide +kernel

theorem arows5243 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5243 = true := by
  rw [show A10K2.u5243 = KTree.node A10K2.u5211 (nat_lit 84130994) (nat_lit 15078393574) (nat_lit 0) A10K2.u5242 from rfl, allE_node, arows5211, irow5243, arows5242]
  all_goals rfl

theorem atot5243 : totK PA10K2 A10K2.u5243 = [0, 3944858961693, 30903797829199, 87176768285614, 109671192215241, 60636054964466, 13805060863267, 1319119472821, 41810754621, 0] := by
  rw [show A10K2.u5243 = KTree.node A10K2.u5211 (nat_lit 84130994) (nat_lit 15078393574) (nat_lit 0) A10K2.u5242 from rfl, totK_node, atot5211, atot5242]
  decide +kernel

theorem arows5307 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5307 = true := by
  rw [show A10K2.u5307 = KTree.node A10K2.u5275 (nat_lit 85070323) (nat_lit 2087162288) (nat_lit 0) A10K2.u5306 from rfl, allE_node, arows5275, irow5307, arows5306]
  all_goals rfl

theorem atot5307 : totK PA10K2 A10K2.u5307 = [0, 5952237496817, 40554652411232, 100561822927165, 107747830334280, 45631832856619, 6605866689042, 284521106261, 0, 0] := by
  rw [show A10K2.u5307 = KTree.node A10K2.u5275 (nat_lit 85070323) (nat_lit 2087162288) (nat_lit 0) A10K2.u5306 from rfl, totK_node, atot5275, atot5306]
  decide +kernel

theorem arows5370 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5370 = true := by
  rw [show A10K2.u5370 = KTree.node A10K2.u5338 (nat_lit 85697837) (nat_lit 6363414045) (nat_lit 0) A10K2.u5369 from rfl, allE_node, arows5338, irow5370, arows5369]
  all_goals rfl

theorem atot5370 : totK PA10K2 A10K2.u5370 = [0, 6049716708961, 37071052935022, 89810191436934, 106355583203145, 59542539625627, 13114172516529, 1033417474302, 13362457043, 0] := by
  rw [show A10K2.u5370 = KTree.node A10K2.u5338 (nat_lit 85697837) (nat_lit 6363414045) (nat_lit 0) A10K2.u5369 from rfl, totK_node, atot5338, atot5369]
  decide +kernel

theorem arows5435 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5435 = true := by
  rw [show A10K2.u5435 = KTree.node A10K2.u5403 (nat_lit 88845426) (nat_lit 11864688620) (nat_lit 0) A10K2.u5434 from rfl, allE_node, arows5403, irow5435, arows5434]
  all_goals rfl

theorem atot5435 : totK PA10K2 A10K2.u5435 = [0, 4694095374265, 32659350261755, 87009102594097, 108129887792499, 61083884092456, 14183574827530, 1353932551341, 42943767608, 0] := by
  rw [show A10K2.u5435 = KTree.node A10K2.u5403 (nat_lit 88845426) (nat_lit 11864688620) (nat_lit 0) A10K2.u5434 from rfl, totK_node, atot5403, atot5434]
  decide +kernel

theorem arows5498 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5498 = true := by
  rw [show A10K2.u5498 = KTree.node A10K2.u5466 (nat_lit 89255837) (nat_lit 2679161789) (nat_lit 0) A10K2.u5497 from rfl, allE_node, arows5466, irow5498, arows5497]
  all_goals rfl

theorem atot5498 : totK PA10K2 A10K2.u5498 = [0, 5954970209307, 40435280120837, 100167698587902, 107768096298456, 46595871982303, 6904348331589, 296936506610, 0, 0] := by
  rw [show A10K2.u5498 = KTree.node A10K2.u5466 (nat_lit 89255837) (nat_lit 2679161789) (nat_lit 0) A10K2.u5497 from rfl, totK_node, atot5466, atot5497]
  decide +kernel

theorem arows5562 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5562 = true := by
  rw [show A10K2.u5562 = KTree.node A10K2.u5530 (nat_lit 89885908) (nat_lit 7897594994) (nat_lit 0) A10K2.u5561 from rfl, allE_node, arows5530, irow5562, arows5561]
  all_goals rfl

theorem atot5562 : totK PA10K2 A10K2.u5562 = [0, 5594179290393, 35351289560070, 88941266895637, 108501047785670, 61273902868861, 13421551314613, 1039766814672, 13505663578, 0] := by
  rw [show A10K2.u5562 = KTree.node A10K2.u5530 (nat_lit 89885908) (nat_lit 7897594994) (nat_lit 0) A10K2.u5561 from rfl, totK_node, atot5530, atot5561]
  decide +kernel

theorem arows5625 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5625 = true := by
  rw [show A10K2.u5625 = KTree.node A10K2.u5593 (nat_lit 92511738) (nat_lit 9411695115) (nat_lit 40) A10K2.u5624 from rfl, allE_node, arows5593, irow5625, arows5624]
  all_goals rfl

theorem atot5625 : totK PA10K2 A10K2.u5625 = [0, 4602817943271, 33302481403424, 89675588443366, 108801203223341, 57196699856501, 12187142144018, 1139508702240, 41810754621, 0] := by
  rw [show A10K2.u5625 = KTree.node A10K2.u5593 (nat_lit 92511738) (nat_lit 9411695115) (nat_lit 40) A10K2.u5624 from rfl, totK_node, atot5593, atot5624]
  decide +kernel

theorem arows5691 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5691 = true := by
  rw [show A10K2.u5691 = KTree.node A10K2.u5659 (nat_lit 93021650) (nat_lit 15365736412) (nat_lit 0) A10K2.u5690 from rfl, allE_node, arows5659, irow5691, arows5690]
  all_goals rfl

theorem atot5691 : totK PA10K2 A10K2.u5691 = [0, 5753228580098, 36876247482168, 91336518374944, 106296995955375, 55736490066530, 11484153205710, 976654324043, 36704093874, 0] := by
  rw [show A10K2.u5691 = KTree.node A10K2.u5659 (nat_lit 93021650) (nat_lit 15365736412) (nat_lit 0) A10K2.u5690 from rfl, totK_node, atot5659, atot5690]
  decide +kernel

theorem arows5754 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5754 = true := by
  rw [show A10K2.u5754 = KTree.node A10K2.u5722 (nat_lit 93444380) (nat_lit 12202579886) (nat_lit 0) A10K2.u5753 from rfl, allE_node, arows5722, irow5754, arows5753]
  all_goals rfl

theorem atot5754 : totK PA10K2 A10K2.u5754 = [0, 6441700865877, 42491502100158, 101693832452855, 104988139338348, 43147044933734, 6519672622408, 422424158825, 6239673734, 0] := by
  rw [show A10K2.u5754 = KTree.node A10K2.u5722 (nat_lit 93444380) (nat_lit 12202579886) (nat_lit 0) A10K2.u5753 from rfl, totK_node, atot5722, atot5753]
  decide +kernel

theorem arows5818 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5818 = true := by
  rw [show A10K2.u5818 = KTree.node A10K2.u5786 (nat_lit 94521526) (nat_lit 4829350456) (nat_lit 0) A10K2.u5817 from rfl, allE_node, arows5786, irow5818, arows5817]
  all_goals rfl

theorem atot5818 : totK PA10K2 A10K2.u5818 = [0, 0, 11574774645641, 61950619781035, 117114101446719, 87990299256150, 23879092921370, 2530689575732, 86109826357, 0] := by
  rw [show A10K2.u5818 = KTree.node A10K2.u5786 (nat_lit 94521526) (nat_lit 4829350456) (nat_lit 0) A10K2.u5817 from rfl, totK_node, atot5786, atot5817]
  decide +kernel

theorem arows5881 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5881 = true := by
  rw [show A10K2.u5881 = KTree.node A10K2.u5849 (nat_lit 95528684) (nat_lit 11235991118) (nat_lit 0) A10K2.u5880 from rfl, allE_node, arows5849, irow5881, arows5880]
  all_goals rfl

theorem atot5881 : totK PA10K2 A10K2.u5881 = [0, 0, 7877523873413, 49934673444334, 110586426353214, 98835851586638, 31943743826688, 4128494055009, 159360372224, 0] := by
  rw [show A10K2.u5881 = KTree.node A10K2.u5849 (nat_lit 95528684) (nat_lit 11235991118) (nat_lit 0) A10K2.u5880 from rfl, totK_node, atot5849, atot5880]
  decide +kernel

theorem arows5946 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5946 = true := by
  rw [show A10K2.u5946 = KTree.node A10K2.u5914 (nat_lit 100808982) (nat_lit 5186936249) (nat_lit 0) A10K2.u5945 from rfl, allE_node, arows5914, irow5946, arows5945]
  all_goals rfl

theorem atot5946 : totK PA10K2 A10K2.u5946 = [6297372052729, 37915311964677, 84434807570305, 84690891556034, 45183974215944, 27844978396892, 16663272781026, 4491975057858, 446040892095, 6354482628] := by
  rw [show A10K2.u5946 = KTree.node A10K2.u5914 (nat_lit 100808982) (nat_lit 5186936249) (nat_lit 0) A10K2.u5945 from rfl, totK_node, atot5914, atot5945]
  decide +kernel

theorem arows6009 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6009 = true := by
  rw [show A10K2.u6009 = KTree.node A10K2.u5977 (nat_lit 101740489) (nat_lit 5862688744) (nat_lit 0) A10K2.u6008 from rfl, allE_node, arows5977, irow6009, arows6008]
  all_goals rfl

theorem atot6009 : totK PA10K2 A10K2.u6009 = [4330032369908, 31581997449273, 86087680597784, 107972861753780, 61513595778416, 14515298521786, 1369726616898, 41810754621, 0, 0] := by
  rw [show A10K2.u6009 = KTree.node A10K2.u5977 (nat_lit 101740489) (nat_lit 5862688744) (nat_lit 0) A10K2.u6008 from rfl, totK_node, atot5977, atot6008]
  decide +kernel

theorem arows6073 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6073 = true := by
  rw [show A10K2.u6073 = KTree.node A10K2.u6041 (nat_lit 102348183) (nat_lit 14122261932) (nat_lit 0) A10K2.u6072 from rfl, allE_node, arows6041, irow6073, arows6072]
  all_goals rfl

theorem atot6073 : totK PA10K2 A10K2.u6073 = [6130477477335, 38011469542398, 92018358495981, 106406778712261, 57169296177979, 12423990489283, 996980238925, 13362457043, 0, 0] := by
  rw [show A10K2.u6073 = KTree.node A10K2.u6041 (nat_lit 102348183) (nat_lit 14122261932) (nat_lit 0) A10K2.u6072 from rfl, totK_node, atot6041, atot6072]
  decide +kernel

theorem arows6136 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6136 = true := by
  rw [show A10K2.u6136 = KTree.node A10K2.u6104 (nat_lit 102777417) (nat_lit 9565289491) (nat_lit 0) A10K2.u6135 from rfl, allE_node, arows6104, irow6136, arows6135]
  all_goals rfl

theorem atot6136 : totK PA10K2 A10K2.u6136 = [0, 10247386108468, 56830045112123, 114282116826027, 97316887518884, 31784072794740, 3608172372287, 123100889691, 0, 0] := by
  rw [show A10K2.u6136 = KTree.node A10K2.u6104 (nat_lit 102777417) (nat_lit 9565289491) (nat_lit 0) A10K2.u6135 from rfl, totK_node, atot6104, atot6135]
  decide +kernel

theorem arows6204 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6204 = true := by
  rw [show A10K2.u6204 = KTree.node A10K2.u6172 (nat_lit 103221357) (nat_lit 5483478668) (nat_lit 0) A10K2.u6203 from rfl, allE_node, arows6172, irow6204, arows6203]
  all_goals rfl

theorem atot6204 : totK PA10K2 A10K2.u6204 = [0, 4326372242041, 32190064881830, 87621799387205, 107977625544405, 59530541419369, 13818792144280, 1353485523899, 41810754621, 0] := by
  rw [show A10K2.u6204 = KTree.node A10K2.u6172 (nat_lit 103221357) (nat_lit 5483478668) (nat_lit 0) A10K2.u6203 from rfl, totK_node, atot6172, atot6203]
  decide +kernel

theorem arows6267 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6267 = true := by
  rw [show A10K2.u6267 = KTree.node A10K2.u6235 (nat_lit 104373659) (nat_lit 5487684821) (nat_lit 0) A10K2.u6266 from rfl, allE_node, arows6235, irow6267, arows6266]
  all_goals rfl

theorem atot6267 : totK PA10K2 A10K2.u6267 = [872244600920, 9538839681570, 43164212949298, 97009319339315, 105497403083380, 47834303390320, 8053678077190, 467019999193, 5976421810, 0] := by
  rw [show A10K2.u6267 = KTree.node A10K2.u6235 (nat_lit 104373659) (nat_lit 5487684821) (nat_lit 0) A10K2.u6266 from rfl, totK_node, atot6235, atot6266]
  decide +kernel

theorem arows6331 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6331 = true := by
  rw [show A10K2.u6331 = KTree.node A10K2.u6299 (nat_lit 105608531) (nat_lit 10450939886) (nat_lit 0) A10K2.u6330 from rfl, allE_node, arows6299, irow6331, arows6330]
  all_goals rfl

theorem atot6331 : totK PA10K2 A10K2.u6331 = [5435849402524, 36407469831654, 92030287323906, 106552182407287, 56084675939190, 12515984306420, 1144538266038, 36704093874, 0, 0] := by
  rw [show A10K2.u6331 = KTree.node A10K2.u6299 (nat_lit 105608531) (nat_lit 10450939886) (nat_lit 0) A10K2.u6330 from rfl, totK_node, atot6299, atot6330]
  decide +kernel

theorem arows6394 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6394 = true := by
  rw [show A10K2.u6394 = KTree.node A10K2.u6362 (nat_lit 106055390) (nat_lit 10169835493) (nat_lit 0) A10K2.u6393 from rfl, allE_node, arows6362, irow6394, arows6393]
  all_goals rfl

theorem atot6394 : totK PA10K2 A10K2.u6394 = [5939809308382, 37472331576396, 91349014301683, 105737066927140, 56156843143816, 11729691837243, 893760695546, 12594156362, 0, 0] := by
  rw [show A10K2.u6394 = KTree.node A10K2.u6362 (nat_lit 106055390) (nat_lit 10169835493) (nat_lit 0) A10K2.u6393 from rfl, totK_node, atot6362, atot6393]
  decide +kernel

theorem arows6459 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6459 = true := by
  rw [show A10K2.u6459 = KTree.node A10K2.u6427 (nat_lit 106669217) (nat_lit 3709562166) (nat_lit 0) A10K2.u6458 from rfl, allE_node, arows6427, irow6459, arows6458]
  all_goals rfl

theorem atot6459 : totK PA10K2 A10K2.u6459 = [4530211197570, 32794003998222, 88864322072747, 111180711935822, 63962911483528, 14989281802192, 1155902907224, 14159155365, 0, 0] := by
  rw [show A10K2.u6459 = KTree.node A10K2.u6427 (nat_lit 106669217) (nat_lit 3709562166) (nat_lit 0) A10K2.u6458 from rfl, totK_node, atot6427, atot6458]
  decide +kernel

theorem arows6522 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6522 = true := by
  rw [show A10K2.u6522 = KTree.node A10K2.u6490 (nat_lit 107620576) (nat_lit 8350058040) (nat_lit 0) A10K2.u6521 from rfl, allE_node, arows6490, irow6522, arows6521]
  all_goals rfl

theorem atot6522 : totK PA10K2 A10K2.u6522 = [0, 7888090921925, 47980059389806, 107050063780428, 103722245747120, 40327486458615, 5370786029160, 203520771319, 0, 0] := by
  rw [show A10K2.u6522 = KTree.node A10K2.u6490 (nat_lit 107620576) (nat_lit 8350058040) (nat_lit 0) A10K2.u6521 from rfl, totK_node, atot6490, atot6521]
  decide +kernel

theorem arows6586 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6586 = true := by
  rw [show A10K2.u6586 = KTree.node A10K2.u6554 (nat_lit 108098849) (nat_lit 6299982427) (nat_lit 0) A10K2.u6585 from rfl, allE_node, arows6554, irow6586, arows6585]
  all_goals rfl

theorem atot6586 : totK PA10K2 A10K2.u6586 = [0, 4337108850414, 31928763949679, 87147156976635, 108157933788517, 60202058710575, 14067115638680, 1370743181851, 42686146280, 0] := by
  rw [show A10K2.u6586 = KTree.node A10K2.u6554 (nat_lit 108098849) (nat_lit 6299982427) (nat_lit 0) A10K2.u6585 from rfl, totK_node, atot6554, atot6585]
  decide +kernel

theorem arows6649 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6649 = true := by
  rw [show A10K2.u6649 = KTree.node A10K2.u6617 (nat_lit 108650902) (nat_lit 15984906244) (nat_lit 0) A10K2.u6648 from rfl, allE_node, arows6617, irow6649, arows6648]
  all_goals rfl

theorem atot6649 : totK PA10K2 A10K2.u6649 = [2231826234337, 17941989144013, 58526989285761, 98543908105746, 88892752428840, 38916881437265, 6853973179401, 452187998302, 6354482628, 0] := by
  rw [show A10K2.u6649 = KTree.node A10K2.u6617 (nat_lit 108650902) (nat_lit 15984906244) (nat_lit 0) A10K2.u6648 from rfl, totK_node, atot6617, atot6648]
  decide +kernel

theorem arows6715 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6715 = true := by
  rw [show A10K2.u6715 = KTree.node A10K2.u6683 (nat_lit 113533491) (nat_lit 5270125465) (nat_lit 0) A10K2.u6714 from rfl, allE_node, arows6683, irow6715, arows6714]
  all_goals rfl

theorem atot6715 : totK PA10K2 A10K2.u6715 = [5809578747806, 36437538311871, 89115970400057, 105194550603674, 59797136182652, 14449459565745, 1387168770121, 41810754621, 0, 0] := by
  rw [show A10K2.u6715 = KTree.node A10K2.u6683 (nat_lit 113533491) (nat_lit 5270125465) (nat_lit 0) A10K2.u6714 from rfl, totK_node, atot6683, atot6714]
  decide +kernel

theorem arows6778 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6778 = true := by
  rw [show A10K2.u6778 = KTree.node A10K2.u6746 (nat_lit 114029790) (nat_lit 11389925001) (nat_lit 0) A10K2.u6777 from rfl, allE_node, arows6746, irow6778, arows6777]
  all_goals rfl

theorem atot6778 : totK PA10K2 A10K2.u6778 = [3577560153580, 29105744105610, 85428670074419, 112405886480899, 65816958803955, 15560657056519, 1431980839789, 42943767608, 0, 0] := by
  rw [show A10K2.u6778 = KTree.node A10K2.u6746 (nat_lit 114029790) (nat_lit 11389925001) (nat_lit 0) A10K2.u6777 from rfl, totK_node, atot6746, atot6777]
  decide +kernel

theorem arows6842 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6842 = true := by
  rw [show A10K2.u6842 = KTree.node A10K2.u6810 (nat_lit 115027057) (nat_lit 8152472276) (nat_lit 0) A10K2.u6841 from rfl, allE_node, arows6810, irow6842, arows6841]
  all_goals rfl

theorem atot6842 : totK PA10K2 A10K2.u6842 = [6593558482649, 40892013006144, 96367305624124, 105253666672920, 52454173238864, 10666302070853, 736759188177, 7007974415, 0, 0] := by
  rw [show A10K2.u6842 = KTree.node A10K2.u6810 (nat_lit 115027057) (nat_lit 8152472276) (nat_lit 0) A10K2.u6841 from rfl, totK_node, atot6810, atot6841]
  decide +kernel

theorem arows6905 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6905 = true := by
  rw [show A10K2.u6905 = KTree.node A10K2.u6873 (nat_lit 115371989) (nat_lit 1678481088) (nat_lit 0) A10K2.u6904 from rfl, allE_node, arows6873, irow6905, arows6904]
  all_goals rfl

theorem atot6905 : totK PA10K2 A10K2.u6905 = [0, 8838255273525, 51725083663454, 110472301276750, 101396058521601, 36806802227862, 4443643051086, 142839131835, 0, 0] := by
  rw [show A10K2.u6905 = KTree.node A10K2.u6873 (nat_lit 115371989) (nat_lit 1678481088) (nat_lit 0) A10K2.u6904 from rfl, totK_node, atot6873, atot6904]
  decide +kernel

theorem arows6970 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6970 = true := by
  rw [show A10K2.u6970 = KTree.node A10K2.u6938 (nat_lit 115958199) (nat_lit 15084722603) (nat_lit 0) A10K2.u6969 from rfl, allE_node, arows6938, irow6970, arows6969]
  all_goals rfl

theorem atot6970 : totK PA10K2 A10K2.u6970 = [0, 5815724471513, 38395096331620, 95577000427955, 108228412022546, 53520448076360, 10141668062881, 671168221432, 7237400819, 0] := by
  rw [show A10K2.u6970 = KTree.node A10K2.u6938 (nat_lit 115958199) (nat_lit 15084722603) (nat_lit 0) A10K2.u6969 from rfl, totK_node, atot6938, atot6969]
  decide +kernel

theorem arows7033 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7033 = true := by
  rw [show A10K2.u7033 = KTree.node A10K2.u7001 (nat_lit 116941162) (nat_lit 2713719490) (nat_lit 0) A10K2.u7032 from rfl, allE_node, arows7001, irow7033, arows7032]
  all_goals rfl

theorem atot7033 : totK PA10K2 A10K2.u7033 = [0, 6593558482649, 41228698971192, 97337057625084, 105933587247859, 51895735716969, 9894054133806, 645257714242, 7380853412, 0] := by
  rw [show A10K2.u7033 = KTree.node A10K2.u7001 (nat_lit 116941162) (nat_lit 2713719490) (nat_lit 0) A10K2.u7032 from rfl, totK_node, atot7001, atot7032]
  decide +kernel

theorem arows7097 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7097 = true := by
  rw [show A10K2.u7097 = KTree.node A10K2.u7065 (nat_lit 117304533) (nat_lit 5348036753) (nat_lit 0) A10K2.u7096 from rfl, allE_node, arows7065, irow7097, arows7096]
  all_goals rfl

theorem atot7097 : totK PA10K2 A10K2.u7097 = [0, 2339048713180, 21411992404043, 72204420550588, 111418569393666, 79252211673091, 23025793339007, 2536222979374, 87362355661, 0] := by
  rw [show A10K2.u7097 = KTree.node A10K2.u7065 (nat_lit 117304533) (nat_lit 5348036753) (nat_lit 0) A10K2.u7096 from rfl, totK_node, atot7065, atot7096]
  decide +kernel

theorem arows7160 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7160 = true := by
  rw [show A10K2.u7160 = KTree.node A10K2.u7128 (nat_lit 117720407) (nat_lit 11933677) (nat_lit 0) A10K2.u7159 from rfl, allE_node, arows7128, irow7160, arows7159]
  all_goals rfl

theorem atot7160 : totK PA10K2 A10K2.u7160 = [0, 4797727201014, 32631552431156, 86285584419797, 108201632231737, 62594104542288, 14775278154989, 1406058682186, 41810754621, 0] := by
  rw [show A10K2.u7160 = KTree.node A10K2.u7128 (nat_lit 117720407) (nat_lit 11933677) (nat_lit 0) A10K2.u7159 from rfl, totK_node, atot7128, atot7159]
  decide +kernel

theorem arows7227 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7227 = true := by
  rw [show A10K2.u7227 = KTree.node A10K2.u7195 (nat_lit 118779455) (nat_lit 14145557035) (nat_lit 0) A10K2.u7226 from rfl, allE_node, arows7195, irow7227, arows7226]
  all_goals rfl

theorem atot7227 : totK PA10K2 A10K2.u7227 = [0, 7274339624217, 44349734878021, 101371038562933, 103724907806517, 43954759700513, 7171093246573, 428726917464, 6354482628, 0] := by
  rw [show A10K2.u7227 = KTree.node A10K2.u7195 (nat_lit 118779455) (nat_lit 14145557035) (nat_lit 0) A10K2.u7226 from rfl, totK_node, atot7195, atot7226]
  decide +kernel

theorem arows7290 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7290 = true := by
  rw [show A10K2.u7290 = KTree.node A10K2.u7258 (nat_lit 119310561) (nat_lit 5135721504) (nat_lit 0) A10K2.u7289 from rfl, allE_node, arows7258, irow7290, arows7289]
  all_goals rfl

theorem atot7290 : totK PA10K2 A10K2.u7290 = [0, 2346766361561, 22291157807511, 74286282628781, 112905671009929, 80478888351573, 24048039928955, 2646743273847, 87935641093, 0] := by
  rw [show A10K2.u7290 = KTree.node A10K2.u7258 (nat_lit 119310561) (nat_lit 5135721504) (nat_lit 0) A10K2.u7289 from rfl, totK_node, atot7258, atot7289]
  decide +kernel

theorem arows7354 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7354 = true := by
  rw [show A10K2.u7354 = KTree.node A10K2.u7322 (nat_lit 119762938) (nat_lit 12700502014) (nat_lit 0) A10K2.u7353 from rfl, allE_node, arows7322, irow7354, arows7353]
  all_goals rfl

theorem atot7354 : totK PA10K2 A10K2.u7354 = [0, 0, 5869249791658, 40270273900164, 99745561991436, 107144531202352, 47531314303814, 8518912245562, 585992452287, 7903172220] := by
  rw [show A10K2.u7354 = KTree.node A10K2.u7322 (nat_lit 119762938) (nat_lit 12700502014) (nat_lit 0) A10K2.u7353 from rfl, totK_node, atot7322, atot7353]
  decide +kernel

theorem arows7417 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7417 = true := by
  rw [show A10K2.u7417 = KTree.node A10K2.u7385 (nat_lit 121135108) (nat_lit 11396332684) (nat_lit 0) A10K2.u7416 from rfl, allE_node, arows7385, irow7417, arows7416]
  all_goals rfl

theorem atot7417 : totK PA10K2 A10K2.u7417 = [0, 0, 10456849719376, 58392883933289, 116975117715249, 96131824296175, 29111751979159, 3031258639553, 81821185729, 0] := by
  rw [show A10K2.u7417 = KTree.node A10K2.u7385 (nat_lit 121135108) (nat_lit 11396332684) (nat_lit 0) A10K2.u7416 from rfl, totK_node, atot7385, atot7416]
  decide +kernel

theorem arows7482 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7482 = true := by
  rw [show A10K2.u7482 = KTree.node A10K2.u7450 (nat_lit 122363293) (nat_lit 1641164774) (nat_lit 0) A10K2.u7481 from rfl, allE_node, arows7450, irow7482, arows7481]
  all_goals rfl

theorem atot7482 : totK PA10K2 A10K2.u7482 = [0, 6308094003444, 39072377063747, 91842575649698, 101463225731068, 55100699705944, 15446572137645, 2103917591053, 97814219980, 0] := by
  rw [show A10K2.u7482 = KTree.node A10K2.u7450 (nat_lit 122363293) (nat_lit 1641164774) (nat_lit 0) A10K2.u7481 from rfl, totK_node, atot7450, atot7481]
  decide +kernel

theorem arows7545 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7545 = true := by
  rw [show A10K2.u7545 = KTree.node A10K2.u7513 (nat_lit 122817057) (nat_lit 10059852256) (nat_lit 0) A10K2.u7544 from rfl, allE_node, arows7513, irow7545, arows7544]
  all_goals rfl

theorem atot7545 : totK PA10K2 A10K2.u7545 = [0, 4337108850414, 31712965095015, 87749254544664, 111193236039470, 60686360872922, 11721229754317, 698125920023, 6239673734, 0] := by
  rw [show A10K2.u7545 = KTree.node A10K2.u7513 (nat_lit 122817057) (nat_lit 10059852256) (nat_lit 0) A10K2.u7544 from rfl, totK_node, atot7513, atot7544]
  decide +kernel

theorem arows7609 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7609 = true := by
  rw [show A10K2.u7609 = KTree.node A10K2.u7577 (nat_lit 123432666) (nat_lit 13784001194) (nat_lit 0) A10K2.u7608 from rfl, allE_node, arows7577, irow7609, arows7608]
  all_goals rfl

theorem atot7609 : totK PA10K2 A10K2.u7609 = [0, 6132911655538, 38540789614680, 93475299418284, 107336120566821, 58041317598057, 13266829891839, 1098888109583, 20513637993, 0] := by
  rw [show A10K2.u7609 = KTree.node A10K2.u7577 (nat_lit 123432666) (nat_lit 13784001194) (nat_lit 0) A10K2.u7608 from rfl, totK_node, atot7577, atot7608]
  decide +kernel

theorem arows7672 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7672 = true := by
  rw [show A10K2.u7672 = KTree.node A10K2.u7640 (nat_lit 124377370) (nat_lit 13440627783) (nat_lit 0) A10K2.u7671 from rfl, allE_node, arows7640, irow7672, arows7671]
  all_goals rfl

theorem atot7672 : totK PA10K2 A10K2.u7672 = [0, 0, 8653799363129, 50828424890403, 109491741838473, 101972359849911, 38171986518403, 5073862983131, 197281097585, 0] := by
  rw [show A10K2.u7672 = KTree.node A10K2.u7640 (nat_lit 124377370) (nat_lit 13440627783) (nat_lit 0) A10K2.u7671 from rfl, totK_node, atot7640, atot7671]
  decide +kernel

theorem arows7738 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7738 = true := by
  rw [show A10K2.u7738 = KTree.node A10K2.u7706 (nat_lit 124923358) (nat_lit 14909570451) (nat_lit 0) A10K2.u7737 from rfl, allE_node, arows7706, irow7738, arows7737]
  all_goals rfl

theorem atot7738 : totK PA10K2 A10K2.u7738 = [0, 0, 8122816980094, 47845420475644, 104545623402664, 101502780004963, 42674507064934, 7596916509612, 543883295689, 8047840951] := by
  rw [show A10K2.u7738 = KTree.node A10K2.u7706 (nat_lit 124923358) (nat_lit 14909570451) (nat_lit 0) A10K2.u7737 from rfl, totK_node, atot7706, atot7737]
  decide +kernel

theorem arows7801 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7801 = true := by
  rw [show A10K2.u7801 = KTree.node A10K2.u7769 (nat_lit 130081571) (nat_lit 4096829946) (nat_lit 0) A10K2.u7800 from rfl, allE_node, arows7769, irow7801, arows7800]
  all_goals rfl

theorem atot7801 : totK PA10K2 A10K2.u7801 = [0, 5803240664210, 37389766822220, 91089444273578, 103974842080702, 58098244439298, 16205073760156, 1919653788483, 74789331576, 0] := by
  rw [show A10K2.u7801 = KTree.node A10K2.u7769 (nat_lit 130081571) (nat_lit 4096829946) (nat_lit 0) A10K2.u7800 from rfl, totK_node, atot7769, atot7800]
  decide +kernel

theorem arows7865 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7865 = true := by
  rw [show A10K2.u7865 = KTree.node A10K2.u7833 (nat_lit 130657339) (nat_lit 6268932872) (nat_lit 0) A10K2.u7864 from rfl, allE_node, arows7833, irow7865, arows7864]
  all_goals rfl

theorem atot7865 : totK PA10K2 A10K2.u7865 = [0, 5815724471513, 37346865546117, 92076097889139, 107144210191040, 57900989346782, 12491733422287, 941822312750, 13364899180, 0] := by
  rw [show A10K2.u7865 = KTree.node A10K2.u7833 (nat_lit 130657339) (nat_lit 6268932872) (nat_lit 0) A10K2.u7864 from rfl, totK_node, atot7833, atot7864]
  decide +kernel

theorem arows7928 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7928 = true := by
  rw [show A10K2.u7928 = KTree.node A10K2.u7896 (nat_lit 131621382) (nat_lit 14956523810) (nat_lit 0) A10K2.u7927 from rfl, allE_node, arows7896, irow7928, arows7927]
  all_goals rfl

theorem atot7928 : totK PA10K2 A10K2.u7928 = [0, 6593558482649, 39910219288426, 93643359832972, 105328002950095, 55734347314399, 11862020817269, 874832975062, 13576218110, 0] := by
  rw [show A10K2.u7928 = KTree.node A10K2.u7896 (nat_lit 131621382) (nat_lit 14956523810) (nat_lit 0) A10K2.u7927 from rfl, totK_node, atot7896, atot7927]
  decide +kernel

theorem arows7993 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7993 = true := by
  rw [show A10K2.u7993 = KTree.node A10K2.u7961 (nat_lit 131974576) (nat_lit 10285475664) (nat_lit 0) A10K2.u7992 from rfl, allE_node, arows7961, irow7993, arows7992]
  all_goals rfl

theorem atot7993 : totK PA10K2 A10K2.u7993 = [0, 0, 11211549198945, 60274782382021, 115978670724566, 93734735675497, 29416212565599, 3234231360591, 101300540273, 0] := by
  rw [show A10K2.u7993 = KTree.node A10K2.u7961 (nat_lit 131974576) (nat_lit 10285475664) (nat_lit 0) A10K2.u7992 from rfl, totK_node, atot7961, atot7992]
  decide +kernel

theorem arows8056 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8056 = true := by
  rw [show A10K2.u8056 = KTree.node A10K2.u8024 (nat_lit 132415045) (nat_lit 3152778010) (nat_lit 0) A10K2.u8055 from rfl, allE_node, arows8024, irow8056, arows8055]
  all_goals rfl

theorem atot8056 : totK PA10K2 A10K2.u8056 = [0, 0, 6569414648006, 41599378675357, 99797078117057, 107676065219641, 49917246268542, 8608822430068, 514965015334, 7237400819] := by
  rw [show A10K2.u8056 = KTree.node A10K2.u8024 (nat_lit 132415045) (nat_lit 3152778010) (nat_lit 0) A10K2.u8055 from rfl, totK_node, atot8024, atot8055]
  decide +kernel

theorem arows8120 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8120 = true := by
  rw [show A10K2.u8120 = KTree.node A10K2.u8088 (nat_lit 133030279) (nat_lit 14471687564) (nat_lit 0) A10K2.u8119 from rfl, allE_node, arows8088, irow8120, arows8119]
  all_goals rfl

theorem atot8120 : totK PA10K2 A10K2.u8120 = [0, 0, 6981280925308, 43963672205864, 102009570983288, 105588555079997, 48547779082437, 8565351395381, 522324256480, 7380853412] := by
  rw [show A10K2.u8120 = KTree.node A10K2.u8088 (nat_lit 133030279) (nat_lit 14471687564) (nat_lit 0) A10K2.u8119 from rfl, totK_node, atot8088, atot8119]
  decide +kernel

theorem arows8183 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8183 = true := by
  rw [show A10K2.u8183 = KTree.node A10K2.u8151 (nat_lit 133991890) (nat_lit 13096764537) (nat_lit 0) A10K2.u8182 from rfl, allE_node, arows8151, irow8183, arows8182]
  all_goals rfl

theorem atot8183 : totK PA10K2 A10K2.u8183 = [0, 0, 2424236405812, 22369625890965, 74592941855937, 112365755776599, 77773796907231, 22189782788026, 2512722636823, 87362355661] := by
  rw [show A10K2.u8183 = KTree.node A10K2.u8151 (nat_lit 133991890) (nat_lit 13096764537) (nat_lit 0) A10K2.u8182 from rfl, totK_node, atot8151, atot8182]
  decide +kernel

theorem arows126 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u126 = true := by
  rw [show A10K2.u126 = KTree.node A10K2.u62 (nat_lit 409889) (nat_lit 9870704603) (nat_lit 0) A10K2.u125 from rfl, allE_node, arows62, irow126, arows125]
  all_goals rfl

theorem atot126 : totK PA10K2 A10K2.u126 = [12175527742643, 78681278578069, 190523962202656, 209417671079555, 101876371927897, 20285789867989, 1597489598471, 41810754621, 0, 0] := by
  rw [show A10K2.u126 = KTree.node A10K2.u62 (nat_lit 409889) (nat_lit 9870704603) (nat_lit 0) A10K2.u125 from rfl, totK_node, atot62, atot125]
  decide +kernel

theorem arows253 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u253 = true := by
  rw [show A10K2.u253 = KTree.node A10K2.u189 (nat_lit 1870994) (nat_lit 13392434777) (nat_lit 0) A10K2.u252 from rfl, allE_node, arows189, irow253, arows252]
  all_goals rfl

theorem atot253 : totK PA10K2 A10K2.u253 = [5885876839217, 47911091285031, 149962167503428, 221699361970116, 152003777662639, 42851170679505, 4530777815918, 136463346734, 0, 0] := by
  rw [show A10K2.u253 = KTree.node A10K2.u189 (nat_lit 1870994) (nat_lit 13392434777) (nat_lit 0) A10K2.u252 from rfl, totK_node, atot189, atot252]
  decide +kernel

theorem arows381 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u381 = true := by
  rw [show A10K2.u381 = KTree.node A10K2.u317 (nat_lit 3277084) (nat_lit 11520834563) (nat_lit 0) A10K2.u380 from rfl, allE_node, arows317, irow381, arows380]
  all_goals rfl

theorem atot381 : totK PA10K2 A10K2.u381 = [0, 10669010201963, 73511280309403, 188091954712220, 214908719770186, 104490316635217, 20880125737542, 1758199769237, 47787176431, 0] := by
  rw [show A10K2.u381 = KTree.node A10K2.u317 (nat_lit 3277084) (nat_lit 11520834563) (nat_lit 0) A10K2.u380 from rfl, totK_node, atot317, atot380]
  decide +kernel

theorem arows508 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u508 = true := by
  rw [show A10K2.u508 = KTree.node A10K2.u444 (nat_lit 8701253) (nat_lit 6926122644) (nat_lit 0) A10K2.u507 from rfl, allE_node, arows444, irow508, arows507]
  all_goals rfl

theorem atot508 : totK PA10K2 A10K2.u508 = [10348199800192, 67755026325545, 171010649822590, 207465985817826, 124117273877208, 35036203488672, 4130490307062, 153296258267, 0, 0] := by
  rw [show A10K2.u508 = KTree.node A10K2.u444 (nat_lit 8701253) (nat_lit 6926122644) (nat_lit 0) A10K2.u507 from rfl, totK_node, atot444, atot507]
  decide +kernel

theorem arows637 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u637 = true := by
  rw [show A10K2.u637 = KTree.node A10K2.u573 (nat_lit 9782775) (nat_lit 10880166698) (nat_lit 0) A10K2.u636 from rfl, allE_node, arows573, irow637, arows636]
  all_goals rfl

theorem atot637 : totK PA10K2 A10K2.u637 = [6202877974731, 51236428998013, 157797364684591, 222476752902700, 139429123635431, 33753413216430, 2941251208444, 62050368457, 0, 0] := by
  rw [show A10K2.u637 = KTree.node A10K2.u573 (nat_lit 9782775) (nat_lit 10880166698) (nat_lit 0) A10K2.u636 from rfl, totK_node, atot573, atot636]
  decide +kernel

theorem arows764 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u764 = true := by
  rw [show A10K2.u764 = KTree.node A10K2.u700 (nat_lit 11819271) (nat_lit 7395812667) (nat_lit 0) A10K2.u763 from rfl, allE_node, arows700, irow764, arows763]
  all_goals rfl

theorem atot764 : totK PA10K2 A10K2.u764 = [6057296600667, 43430068037374, 129037467889070, 200066616161325, 163445995399426, 60536003335043, 9715931572561, 642605324217, 6354482628, 0] := by
  rw [show A10K2.u764 = KTree.node A10K2.u700 (nat_lit 11819271) (nat_lit 7395812667) (nat_lit 0) A10K2.u763 from rfl, totK_node, atot700, atot763]
  decide +kernel

theorem arows892 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u892 = true := by
  rw [show A10K2.u892 = KTree.node A10K2.u828 (nat_lit 13449997) (nat_lit 5376640305) (nat_lit 0) A10K2.u891 from rfl, allE_node, arows828, irow892, arows891]
  all_goals rfl

theorem atot892 : totK PA10K2 A10K2.u892 = [10850168185780, 71115940235808, 180259209390987, 216230618301938, 120438290401011, 27749640718397, 2549155289497, 78514848495, 0, 0] := by
  rw [show A10K2.u892 = KTree.node A10K2.u828 (nat_lit 13449997) (nat_lit 5376640305) (nat_lit 0) A10K2.u891 from rfl, totK_node, atot828, atot891]
  decide +kernel

theorem arows1019 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1019 = true := by
  rw [show A10K2.u1019 = KTree.node A10K2.u955 (nat_lit 14847431) (nat_lit 14426162014) (nat_lit 0) A10K2.u1018 from rfl, allE_node, arows955, irow1019, arows1018]
  all_goals rfl

theorem atot1019 : totK PA10K2 A10K2.u1019 = [0, 16033532746219, 94596037657312, 208513221874972, 206059305600423, 87227160250569, 14101622455344, 800981639584, 7237400819, 0] := by
  rw [show A10K2.u1019 = KTree.node A10K2.u955 (nat_lit 14847431) (nat_lit 14426162014) (nat_lit 0) A10K2.u1018 from rfl, totK_node, atot955, atot1018]
  decide +kernel

theorem arows1149 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1149 = true := by
  rw [show A10K2.u1149 = KTree.node A10K2.u1085 (nat_lit 16460978) (nat_lit 15078393574) (nat_lit 0) A10K2.u1148 from rfl, allE_node, arows1085, irow1149, arows1148]
  all_goals rfl

theorem atot1149 : totK PA10K2 A10K2.u1149 = [0, 9639422167524, 65602174959211, 172645817236629, 216786362529172, 130139059798694, 32564981121466, 3152608615255, 94743209073, 0] := by
  rw [show A10K2.u1149 = KTree.node A10K2.u1085 (nat_lit 16460978) (nat_lit 15078393574) (nat_lit 0) A10K2.u1148 from rfl, totK_node, atot1085, atot1148]
  decide +kernel

theorem arows1276 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1276 = true := by
  rw [show A10K2.u1276 = KTree.node A10K2.u1212 (nat_lit 17245639) (nat_lit 14063348317) (nat_lit 0) A10K2.u1275 from rfl, allE_node, arows1212, irow1276, arows1275]
  all_goals rfl

theorem atot1276 : totK PA10K2 A10K2.u1276 = [0, 9795492346164, 69338765641547, 183459017518502, 217580492774061, 108962193132599, 21012616472453, 1615522184777, 41810754621, 0] := by
  rw [show A10K2.u1276 = KTree.node A10K2.u1212 (nat_lit 17245639) (nat_lit 14063348317) (nat_lit 0) A10K2.u1275 from rfl, totK_node, atot1212, atot1275]
  decide +kernel

theorem arows1404 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1404 = true := by
  rw [show A10K2.u1404 = KTree.node A10K2.u1340 (nat_lit 18821022) (nat_lit 15478542823) (nat_lit 0) A10K2.u1403 from rfl, allE_node, arows1340, irow1404, arows1403]
  all_goals rfl

theorem atot1404 : totK PA10K2 A10K2.u1404 = [0, 5885876839217, 45719894571246, 140248625576575, 211637910396748, 158169729071204, 54747463746936, 9161741691013, 816310407021, 30605747850] := by
  rw [show A10K2.u1404 = KTree.node A10K2.u1340 (nat_lit 18821022) (nat_lit 15478542823) (nat_lit 0) A10K2.u1403 from rfl, totK_node, atot1340, atot1403]
  decide +kernel

theorem arows1531 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1531 = true := by
  rw [show A10K2.u1531 = KTree.node A10K2.u1467 (nat_lit 20268189) (nat_lit 6181965923) (nat_lit 0) A10K2.u1530 from rfl, allE_node, arows1467, irow1531, arows1530]
  all_goals rfl

theorem atot1531 : totK PA10K2 A10K2.u1531 = [0, 3079826674364, 28030970948479, 104728150460570, 197462507876704, 186641059602858, 79822286365227, 14472845831316, 1062249276262, 17181428581] := by
  rw [show A10K2.u1531 = KTree.node A10K2.u1467 (nat_lit 20268189) (nat_lit 6181965923) (nat_lit 0) A10K2.u1530 from rfl, totK_node, atot1467, atot1530]
  decide +kernel

theorem arows1660 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1660 = true := by
  rw [show A10K2.u1660 = KTree.node A10K2.u1596 (nat_lit 25800599) (nat_lit 14522178997) (nat_lit 0) A10K2.u1659 from rfl, allE_node, arows1596, irow1660, arows1659]
  all_goals rfl

theorem atot1660 : totK PA10K2 A10K2.u1660 = [0, 11174919629491, 74011887527739, 185694235927597, 213472215804956, 107768026870691, 21915407314071, 1829391505647, 48050428355, 0] := by
  rw [show A10K2.u1660 = KTree.node A10K2.u1596 (nat_lit 25800599) (nat_lit 14522178997) (nat_lit 0) A10K2.u1659 from rfl, totK_node, atot1596, atot1659]
  decide +kernel

theorem arows1787 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1787 = true := by
  rw [show A10K2.u1787 = KTree.node A10K2.u1723 (nat_lit 27415907) (nat_lit 9355842215) (nat_lit 0) A10K2.u1786 from rfl, allE_node, arows1723, irow1787, arows1786]
  all_goals rfl

theorem atot1787 : totK PA10K2 A10K2.u1787 = [0, 2296331471068, 35060007959663, 141378520862170, 231958730601493, 158132061334221, 39694937740572, 3787706041333, 104053533983, 0] := by
  rw [show A10K2.u1787 = KTree.node A10K2.u1723 (nat_lit 27415907) (nat_lit 9355842215) (nat_lit 0) A10K2.u1786 from rfl, totK_node, atot1723, atot1786]
  decide +kernel

theorem arows1915 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1915 = true := by
  rw [show A10K2.u1915 = KTree.node A10K2.u1851 (nat_lit 29587328) (nat_lit 13700452529) (nat_lit 0) A10K2.u1914 from rfl, allE_node, arows1851, irow1915, arows1914]
  all_goals rfl

theorem atot1915 : totK PA10K2 A10K2.u1915 = [0, 10515025065975, 65505624817110, 162303849170216, 202221457909089, 131690132343828, 41529748107484, 6351206790998, 391539390707, 6354482628] := by
  rw [show A10K2.u1915 = KTree.node A10K2.u1851 (nat_lit 29587328) (nat_lit 13700452529) (nat_lit 0) A10K2.u1914 from rfl, totK_node, atot1851, atot1914]
  decide +kernel

theorem arows2042 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2042 = true := by
  rw [show A10K2.u2042 = KTree.node A10K2.u1978 (nat_lit 31173270) (nat_lit 13259814094) (nat_lit 0) A10K2.u2041 from rfl, allE_node, arows1978, irow2042, arows2041]
  all_goals rfl

theorem atot2042 : totK PA10K2 A10K2.u2042 = [2808829852973, 21834819861193, 78424661932948, 165164484528927, 200765988748485, 124908403307922, 33191538593193, 3285581574776, 95983482044, 0] := by
  rw [show A10K2.u2042 = KTree.node A10K2.u1978 (nat_lit 31173270) (nat_lit 13259814094) (nat_lit 0) A10K2.u2041 from rfl, totK_node, atot1978, atot2041]
  decide +kernel

theorem arows2173 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2173 = true := by
  rw [show A10K2.u2173 = KTree.node A10K2.u2109 (nat_lit 38803568) (nat_lit 14698820898) (nat_lit 0) A10K2.u2172 from rfl, allE_node, arows2109, irow2173, arows2172]
  all_goals rfl

theorem atot2173 : totK PA10K2 A10K2.u2173 = [10333461735963, 69398690082214, 178717271777435, 213590993298956, 115258370101824, 25031214368820, 2079850544881, 49298250236, 0, 0] := by
  rw [show A10K2.u2173 = KTree.node A10K2.u2109 (nat_lit 38803568) (nat_lit 14698820898) (nat_lit 0) A10K2.u2172 from rfl, totK_node, atot2109, atot2172]
  decide +kernel

theorem arows2300 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2300 = true := by
  rw [show A10K2.u2300 = KTree.node A10K2.u2236 (nat_lit 39793878) (nat_lit 14738388334) (nat_lit 0) A10K2.u2299 from rfl, allE_node, arows2236, irow2300, arows2299]
  all_goals rfl

theorem atot2300 : totK PA10K2 A10K2.u2300 = [4935928765675, 41936908653697, 137021974794493, 216418335913194, 166503671761303, 55620358375649, 6723690119212, 224642669035, 0, 0] := by
  rw [show A10K2.u2300 = KTree.node A10K2.u2236 (nat_lit 39793878) (nat_lit 14738388334) (nat_lit 0) A10K2.u2299 from rfl, totK_node, atot2236, atot2299]
  decide +kernel

theorem arows2428 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2428 = true := by
  rw [show A10K2.u2428 = KTree.node A10K2.u2364 (nat_lit 41173780) (nat_lit 12867392087) (nat_lit 0) A10K2.u2427 from rfl, allE_node, arows2364, irow2428, arows2427]
  all_goals rfl

theorem atot2428 : totK PA10K2 A10K2.u2428 = [796021182214, 14165821799108, 77525940625680, 185803200910846, 209757713989741, 104749833978609, 21442696148600, 1833316411277, 49040628908, 0] := by
  rw [show A10K2.u2428 = KTree.node A10K2.u2364 (nat_lit 41173780) (nat_lit 12867392087) (nat_lit 0) A10K2.u2427 from rfl, totK_node, atot2364, atot2427]
  decide +kernel

theorem arows2555 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2555 = true := by
  rw [show A10K2.u2555 = KTree.node A10K2.u2491 (nat_lit 42579867) (nat_lit 7929161368) (nat_lit 0) A10K2.u2554 from rfl, allE_node, arows2491, irow2555, arows2554]
  all_goals rfl

theorem atot2555 : totK PA10K2 A10K2.u2555 = [10000750500492, 67619005633583, 174868307497034, 212714622960846, 120899949716143, 28940066108254, 2767763129451, 84754522229, 0, 0] := by
  rw [show A10K2.u2555 = KTree.node A10K2.u2491 (nat_lit 42579867) (nat_lit 7929161368) (nat_lit 0) A10K2.u2554 from rfl, totK_node, atot2491, atot2554]
  decide +kernel

theorem arows2684 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2684 = true := by
  rw [show A10K2.u2684 = KTree.node A10K2.u2620 (nat_lit 43427596) (nat_lit 11265283211) (nat_lit 0) A10K2.u2683 from rfl, allE_node, arows2620, irow2684, arows2683]
  all_goals rfl

theorem atot2684 : totK PA10K2 A10K2.u2684 = [5748398962592, 50086959344456, 156414120184973, 220906803938613, 140431647517991, 35747375776628, 3469884371921, 92464308985, 0, 0] := by
  rw [show A10K2.u2684 = KTree.node A10K2.u2620 (nat_lit 43427596) (nat_lit 11265283211) (nat_lit 0) A10K2.u2683 from rfl, totK_node, atot2620, atot2683]
  decide +kernel

theorem arows2811 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2811 = true := by
  rw [show A10K2.u2811 = KTree.node A10K2.u2747 (nat_lit 45499272) (nat_lit 14064435958) (nat_lit 0) A10K2.u2810 from rfl, allE_node, arows2747, irow2811, arows2810]
  all_goals rfl

theorem atot2811 : totK PA10K2 A10K2.u2811 = [5313003151528, 39590359458999, 124971377138776, 204722939281073, 170576332637844, 62523894707219, 9827644699603, 642228366032, 6354482628, 0] := by
  rw [show A10K2.u2811 = KTree.node A10K2.u2747 (nat_lit 45499272) (nat_lit 14064435958) (nat_lit 0) A10K2.u2810 from rfl, totK_node, atot2747, atot2810]
  decide +kernel

theorem arows2939 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2939 = true := by
  rw [show A10K2.u2939 = KTree.node A10K2.u2875 (nat_lit 47124478) (nat_lit 15836163304) (nat_lit 0) A10K2.u2938 from rfl, allE_node, arows2875, irow2939, arows2938]
  all_goals rfl

theorem atot2939 : totK PA10K2 A10K2.u2939 = [11599087068976, 75254986677468, 185811646003951, 214069425792650, 114369773797923, 25498130769190, 2130895683385, 49951742023, 0, 0] := by
  rw [show A10K2.u2939 = KTree.node A10K2.u2875 (nat_lit 47124478) (nat_lit 15836163304) (nat_lit 0) A10K2.u2938 from rfl, totK_node, atot2875, atot2938]
  decide +kernel

theorem arows3066 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3066 = true := by
  rw [show A10K2.u3066 = KTree.node A10K2.u3002 (nat_lit 48513863) (nat_lit 5509896283) (nat_lit 0) A10K2.u3065 from rfl, allE_node, arows3002, irow3066, arows3065]
  all_goals rfl

theorem atot3066 : totK PA10K2 A10K2.u3066 = [0, 14511147325270, 89144026892917, 204354888517788, 210299126315702, 93623564822189, 15691180742300, 894851924313, 7237400819, 0] := by
  rw [show A10K2.u3066 = KTree.node A10K2.u3002 (nat_lit 48513863) (nat_lit 5509896283) (nat_lit 0) A10K2.u3065 from rfl, totK_node, atot3002, atot3065]
  decide +kernel

theorem arows3196 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3196 = true := by
  rw [show A10K2.u3196 = KTree.node A10K2.u3132 (nat_lit 50069425) (nat_lit 8775483592) (nat_lit 0) A10K2.u3195 from rfl, allE_node, arows3132, irow3196, arows3195]
  all_goals rfl

theorem atot3196 : totK PA10K2 A10K2.u3196 = [0, 10780626987476, 70003313893820, 175951192618602, 212317846455758, 124187254929613, 31225219235259, 3083851983934, 94743209073, 0] := by
  rw [show A10K2.u3196 = KTree.node A10K2.u3132 (nat_lit 50069425) (nat_lit 8775483592) (nat_lit 0) A10K2.u3195 from rfl, totK_node, atot3132, atot3195]
  decide +kernel

theorem arows3323 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3323 = true := by
  rw [show A10K2.u3323 = KTree.node A10K2.u3259 (nat_lit 55650078) (nat_lit 11378213364) (nat_lit 0) A10K2.u3322 from rfl, allE_node, arows3259, irow3323, arows3322]
  all_goals rfl

theorem atot3323 : totK PA10K2 A10K2.u3323 = [0, 10034495391800, 69782346542918, 182540846296564, 217038187025097, 112804255023683, 23137200620065, 1880124352020, 49298250236, 0] := by
  rw [show A10K2.u3323 = KTree.node A10K2.u3259 (nat_lit 55650078) (nat_lit 11378213364) (nat_lit 0) A10K2.u3322 from rfl, totK_node, atot3259, atot3322]
  decide +kernel

theorem arows3451 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3451 = true := by
  rw [show A10K2.u3451 = KTree.node A10K2.u3387 (nat_lit 56619961) (nat_lit 6905817850) (nat_lit 0) A10K2.u3450 from rfl, allE_node, arows3387, irow3451, arows3450]
  all_goals rfl

theorem atot3451 : totK PA10K2 A10K2.u3451 = [0, 3656557161077, 34070083468836, 121859286503763, 209256095738199, 175647066338282, 68129661840753, 12411738259309, 1107164830447, 36704093874] := by
  rw [show A10K2.u3451 = KTree.node A10K2.u3387 (nat_lit 56619961) (nat_lit 6905817850) (nat_lit 0) A10K2.u3450 from rfl, totK_node, atot3387, atot3450]
  decide +kernel

theorem arows3578 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3578 = true := by
  rw [show A10K2.u3578 = KTree.node A10K2.u3514 (nat_lit 58086558) (nat_lit 13279438318) (nat_lit 0) A10K2.u3577 from rfl, allE_node, arows3514, irow3578, arows3577]
  all_goals rfl

theorem atot3578 : totK PA10K2 A10K2.u3578 = [0, 4328003150587, 35640161304589, 117981973029908, 199230422671036, 175275035275239, 72392046404286, 12308685448018, 822672059219, 12336535034] := by
  rw [show A10K2.u3578 = KTree.node A10K2.u3514 (nat_lit 58086558) (nat_lit 13279438318) (nat_lit 0) A10K2.u3577 from rfl, totK_node, atot3514, atot3577]
  decide +kernel

theorem arows3707 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3707 = true := by
  rw [show A10K2.u3707 = KTree.node A10K2.u3643 (nat_lit 59586836) (nat_lit 13248933502) (nat_lit 0) A10K2.u3706 from rfl, allE_node, arows3643, irow3707, arows3706]
  all_goals rfl

theorem atot3707 : totK PA10K2 A10K2.u3707 = [0, 11917372677211, 75419747862644, 184682055934386, 212049501951872, 109269825257999, 22731817414945, 1878261120814, 48619963340, 0] := by
  rw [show A10K2.u3707 = KTree.node A10K2.u3643 (nat_lit 59586836) (nat_lit 13248933502) (nat_lit 0) A10K2.u3706 from rfl, totK_node, atot3643, atot3706]
  decide +kernel

theorem arows3834 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3834 = true := by
  rw [show A10K2.u3834 = KTree.node A10K2.u3770 (nat_lit 61425585) (nat_lit 3454870112) (nat_lit 0) A10K2.u3833 from rfl, allE_node, arows3770, irow3834, arows3833]
  all_goals rfl

theorem atot3834 : totK PA10K2 A10K2.u3834 = [0, 295989007569, 26411228091590, 131732076392134, 237192957597249, 170527352176470, 43601841911992, 4126717252609, 111176140885, 0] := by
  rw [show A10K2.u3834 = KTree.node A10K2.u3770 (nat_lit 61425585) (nat_lit 3454870112) (nat_lit 0) A10K2.u3833 from rfl, totK_node, atot3770, atot3833]
  decide +kernel

theorem arows3962 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3962 = true := by
  rw [show A10K2.u3962 = KTree.node A10K2.u3898 (nat_lit 63180351) (nat_lit 14111345449) (nat_lit 0) A10K2.u3961 from rfl, allE_node, arows3898, irow3962, arows3961]
  all_goals rfl

theorem atot3962 : totK PA10K2 A10K2.u3962 = [0, 10518631034762, 65484593589494, 161899113487239, 202198447236107, 133624458237188, 42202637731942, 6366184823518, 410399470598, 6354482628] := by
  rw [show A10K2.u3962 = KTree.node A10K2.u3898 (nat_lit 63180351) (nat_lit 14111345449) (nat_lit 0) A10K2.u3961 from rfl, totK_node, atot3898, atot3961]
  decide +kernel

theorem arows4089 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4089 = true := by
  rw [show A10K2.u4089 = KTree.node A10K2.u4025 (nat_lit 64716245) (nat_lit 3505417292) (nat_lit 0) A10K2.u4088 from rfl, allE_node, arows4025, irow4089, arows4088]
  all_goals rfl

theorem atot4089 : totK PA10K2 A10K2.u4089 = [2338692983822, 18858835216475, 71797932640296, 158967052313731, 202454982845906, 132664012884178, 37387132033741, 3998345662715, 130879408701, 0] := by
  rw [show A10K2.u4089 = KTree.node A10K2.u4025 (nat_lit 64716245) (nat_lit 3505417292) (nat_lit 0) A10K2.u4088 from rfl, totK_node, atot4025, atot4088]
  decide +kernel

theorem arows4221 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4221 = true := by
  rw [show A10K2.u4221 = KTree.node A10K2.u4157 (nat_lit 68160972) (nat_lit 6468779237) (nat_lit 0) A10K2.u4220 from rfl, allE_node, arows4157, irow4221, arows4220]
  all_goals rfl

theorem atot4221 : totK PA10K2 A10K2.u4221 = [9897096458510, 68787692049493, 180134220916088, 216002254578628, 114230921999223, 24021574730480, 1913495717043, 41810754621, 0, 0] := by
  rw [show A10K2.u4221 = KTree.node A10K2.u4157 (nat_lit 68160972) (nat_lit 6468779237) (nat_lit 0) A10K2.u4220 from rfl, totK_node, atot4157, atot4220]
  decide +kernel

theorem arows4348 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4348 = true := by
  rw [show A10K2.u4348 = KTree.node A10K2.u4284 (nat_lit 69212947) (nat_lit 7651350275) (nat_lit 0) A10K2.u4347 from rfl, allE_node, arows4284, irow4348, arows4347]
  all_goals rfl

theorem atot4348 : totK PA10K2 A10K2.u4348 = [4449301618478, 35915904406109, 117919217482004, 198227345363473, 175025563724988, 74719391806813, 14272887155546, 1219304279333, 36134558889, 0] := by
  rw [show A10K2.u4348 = KTree.node A10K2.u4284 (nat_lit 69212947) (nat_lit 7651350275) (nat_lit 0) A10K2.u4347 from rfl, totK_node, atot4284, atot4347]
  decide +kernel

theorem arows4476 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4476 = true := by
  rw [show A10K2.u4476 = KTree.node A10K2.u4412 (nat_lit 70681122) (nat_lit 6378506782) (nat_lit 0) A10K2.u4475 from rfl, allE_node, arows4412, irow4476, arows4475]
  all_goals rfl

theorem atot4476 : totK PA10K2 A10K2.u4476 = [4682757634830, 36524833303128, 118489602980729, 199813275187809, 175371369987452, 70165537419465, 11547430444914, 735608212048, 11652617542, 0] := by
  rw [show A10K2.u4476 = KTree.node A10K2.u4412 (nat_lit 70681122) (nat_lit 6378506782) (nat_lit 0) A10K2.u4475 from rfl, totK_node, atot4412, atot4475]
  decide +kernel

theorem arows4603 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4603 = true := by
  rw [show A10K2.u4603 = KTree.node A10K2.u4539 (nat_lit 72440485) (nat_lit 7279318189) (nat_lit 0) A10K2.u4602 from rfl, allE_node, arows4539, irow4603, arows4602]
  all_goals rfl

theorem atot4603 : totK PA10K2 A10K2.u4603 = [9777750814816, 67770716130718, 178551421364272, 217047743293569, 117754389146814, 25283504034180, 2096787219472, 49298250236, 0, 0] := by
  rw [show A10K2.u4603 = KTree.node A10K2.u4539 (nat_lit 72440485) (nat_lit 7279318189) (nat_lit 0) A10K2.u4602 from rfl, totK_node, atot4539, atot4602]
  decide +kernel

theorem arows4732 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4732 = true := by
  rw [show A10K2.u4732 = KTree.node A10K2.u4668 (nat_lit 74065568) (nat_lit 6301981597) (nat_lit 0) A10K2.u4731 from rfl, allE_node, arows4668, irow4732, arows4731]
  all_goals rfl

theorem atot4732 : totK PA10K2 A10K2.u4732 = [2245477168038, 25015242831211, 102283765733113, 198295866773919, 191005268370084, 86831787594239, 17208005850976, 1487626299872, 42686146280, 0] := by
  rw [show A10K2.u4732 = KTree.node A10K2.u4668 (nat_lit 74065568) (nat_lit 6301981597) (nat_lit 0) A10K2.u4731 from rfl, totK_node, atot4668, atot4731]
  decide +kernel

theorem arows4859 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4859 = true := by
  rw [show A10K2.u4859 = KTree.node A10K2.u4795 (nat_lit 75071048) (nat_lit 12260840781) (nat_lit 0) A10K2.u4858 from rfl, allE_node, arows4795, irow4859, arows4858]
  all_goals rfl

theorem atot4859 : totK PA10K2 A10K2.u4859 = [5740492290035, 42106189030483, 126538423110356, 198780238465313, 167880663964021, 66246346700172, 10103833414302, 556087405206, 6354482628, 0] := by
  rw [show A10K2.u4859 = KTree.node A10K2.u4795 (nat_lit 75071048) (nat_lit 12260840781) (nat_lit 0) A10K2.u4858 from rfl, totK_node, atot4795, atot4858]
  decide +kernel

theorem arows4987 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4987 = true := by
  rw [show A10K2.u4987 = KTree.node A10K2.u4923 (nat_lit 76261645) (nat_lit 5782147384) (nat_lit 0) A10K2.u4986 from rfl, allE_node, arows4923, irow4987, arows4986]
  all_goals rfl

theorem atot4987 : totK PA10K2 A10K2.u4987 = [9851096729204, 65901771732899, 171384543634334, 212515324355172, 123366987787051, 29863315732283, 2842197304626, 84754522229, 0, 0] := by
  rw [show A10K2.u4987 = KTree.node A10K2.u4923 (nat_lit 76261645) (nat_lit 5782147384) (nat_lit 0) A10K2.u4986 from rfl, totK_node, atot4923, atot4986]
  decide +kernel

theorem arows5114 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5114 = true := by
  rw [show A10K2.u5114 = KTree.node A10K2.u5050 (nat_lit 77742957) (nat_lit 5420028275) (nat_lit 0) A10K2.u5113 from rfl, allE_node, arows5050, irow5114, arows5113]
  all_goals rfl

theorem atot5114 : totK PA10K2 A10K2.u5114 = [2343832716771, 33505038807887, 134882148454065, 226694216874018, 164909282957089, 46894598784616, 4835877915629, 136637141071, 0, 0] := by
  rw [show A10K2.u5114 = KTree.node A10K2.u5050 (nat_lit 77742957) (nat_lit 5420028275) (nat_lit 0) A10K2.u5113 from rfl, totK_node, atot5050, atot5113]
  decide +kernel

theorem arows5244 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5244 = true := by
  rw [show A10K2.u5244 = KTree.node A10K2.u5180 (nat_lit 83914195) (nat_lit 9344105921) (nat_lit 0) A10K2.u5243 from rfl, allE_node, arows5180, irow5244, arows5243]
  all_goals rfl

theorem atot5244 : totK PA10K2 A10K2.u5244 = [0, 10664881889766, 72858157562818, 185960586129247, 212983504778385, 104475340803973, 21593943584457, 1887945376142, 48165237249, 0] := by
  rw [show A10K2.u5244 = KTree.node A10K2.u5180 (nat_lit 83914195) (nat_lit 9344105921) (nat_lit 0) A10K2.u5243 from rfl, totK_node, atot5180, atot5243]
  decide +kernel

theorem arows5371 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5371 = true := by
  rw [show A10K2.u5371 = KTree.node A10K2.u5307 (nat_lit 85348741) (nat_lit 5201789090) (nat_lit 0) A10K2.u5370 from rfl, allE_node, arows5307, irow5371, arows5370]
  all_goals rfl

theorem atot5371 : totK PA10K2 A10K2.u5371 = [0, 12001954205778, 77625705346254, 190372014364099, 214108615326515, 105174372482246, 19720039205571, 1317938580563, 13362457043, 0] := by
  rw [show A10K2.u5371 = KTree.node A10K2.u5307 (nat_lit 85348741) (nat_lit 5201789090) (nat_lit 0) A10K2.u5370 from rfl, totK_node, atot5307, atot5370]
  decide +kernel

theorem arows5499 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5499 = true := by
  rw [show A10K2.u5499 = KTree.node A10K2.u5435 (nat_lit 89066653) (nat_lit 3030337663) (nat_lit 32) A10K2.u5498 from rfl, allE_node, arows5435, irow5499, arows5498]
  all_goals rfl

theorem atot5499 : totK PA10K2 A10K2.u5499 = [0, 10649065583572, 73094630382592, 187176801181999, 215901014428618, 107679756074759, 21087923159119, 1650869057951, 42943767608, 0] := by
  rw [show A10K2.u5499 = KTree.node A10K2.u5435 (nat_lit 89066653) (nat_lit 3030337663) (nat_lit 32) A10K2.u5498 from rfl, totK_node, atot5435, atot5498]
  decide +kernel

theorem arows5626 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5626 = true := by
  rw [show A10K2.u5626 = KTree.node A10K2.u5562 (nat_lit 92291641) (nat_lit 7183406458) (nat_lit 0) A10K2.u5625 from rfl, allE_node, arows5562, irow5626, arows5625]
  all_goals rfl

theorem atot5626 : totK PA10K2 A10K2.u5626 = [0, 10196997233664, 68653770963494, 178616855339003, 217309434415469, 118470602725362, 25608693458631, 2179275516912, 55316418199, 0] := by
  rw [show A10K2.u5626 = KTree.node A10K2.u5562 (nat_lit 92291641) (nat_lit 7183406458) (nat_lit 0) A10K2.u5625 from rfl, totK_node, atot5562, atot5625]
  decide +kernel

theorem arows5755 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5755 = true := by
  rw [show A10K2.u5755 = KTree.node A10K2.u5691 (nat_lit 93246682) (nat_lit 12658986951) (nat_lit 0) A10K2.u5754 from rfl, allE_node, arows5691, irow5755, arows5754]
  all_goals rfl

theorem atot5755 : totK PA10K2 A10K2.u5755 = [0, 12194929445975, 79367749582326, 193030350827799, 211285135293723, 98883535000264, 18016484815069, 1399078482868, 42943767608, 0] := by
  rw [show A10K2.u5755 = KTree.node A10K2.u5691 (nat_lit 93246682) (nat_lit 12658986951) (nat_lit 0) A10K2.u5754 from rfl, totK_node, atot5691, atot5754]
  decide +kernel

theorem arows5882 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5882 = true := by
  rw [show A10K2.u5882 = KTree.node A10K2.u5818 (nat_lit 95045819) (nat_lit 6741531018) (nat_lit 0) A10K2.u5881 from rfl, allE_node, arows5818, irow5882, arows5881]
  all_goals rfl

theorem atot5882 : totK PA10K2 A10K2.u5882 = [0, 0, 19452298519054, 111885293225369, 227707269330951, 186826150842788, 55822836748058, 6659183630741, 245470198581, 0] := by
  rw [show A10K2.u5882 = KTree.node A10K2.u5818 (nat_lit 95045819) (nat_lit 6741531018) (nat_lit 0) A10K2.u5881 from rfl, totK_node, atot5818, atot5881]
  decide +kernel

theorem arows6010 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6010 = true := by
  rw [show A10K2.u6010 = KTree.node A10K2.u5946 (nat_lit 100958564) (nat_lit 13567354448) (nat_lit 0) A10K2.u6009 from rfl, allE_node, arows5946, irow6010, arows6009]
  all_goals rfl

theorem atot6010 : totK PA10K2 A10K2.u6010 = [10627404422637, 69497309413950, 170522488168089, 192677320664262, 106697569994360, 42360276918678, 18032999397924, 4533785812479, 446040892095, 6354482628] := by
  rw [show A10K2.u6010 = KTree.node A10K2.u5946 (nat_lit 100958564) (nat_lit 13567354448) (nat_lit 0) A10K2.u6009 from rfl, totK_node, atot5946, atot6009]
  decide +kernel

theorem arows6137 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6137 = true := by
  rw [show A10K2.u6137 = KTree.node A10K2.u6073 (nat_lit 102556165) (nat_lit 6121858873) (nat_lit 0) A10K2.u6136 from rfl, allE_node, arows6073, irow6137, arows6136]
  all_goals rfl

theorem atot6137 : totK PA10K2 A10K2.u6137 = [6130477477335, 48258855650866, 148848403608104, 220688895538288, 154492305555736, 44208063284023, 4605152611212, 136463346734, 0, 0] := by
  rw [show A10K2.u6137 = KTree.node A10K2.u6073 (nat_lit 102556165) (nat_lit 6121858873) (nat_lit 0) A10K2.u6136 from rfl, totK_node, atot6073, atot6136]
  decide +kernel

theorem arows6268 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6268 = true := by
  rw [show A10K2.u6268 = KTree.node A10K2.u6204 (nat_lit 103991524) (nat_lit 13617425715) (nat_lit 0) A10K2.u6267 from rfl, allE_node, arows6204, irow6268, arows6267]
  all_goals rfl

theorem atot6268 : totK PA10K2 A10K2.u6268 = [872244600920, 13865211923611, 75354277831128, 184644736152235, 213475028627785, 107364844809689, 21872470221470, 1820505523092, 47787176431, 0] := by
  rw [show A10K2.u6268 = KTree.node A10K2.u6204 (nat_lit 103991524) (nat_lit 13617425715) (nat_lit 0) A10K2.u6267 from rfl, totK_node, atot6204, atot6267]
  decide +kernel

theorem arows6395 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6395 = true := by
  rw [show A10K2.u6395 = KTree.node A10K2.u6331 (nat_lit 105818410) (nat_lit 12288443943) (nat_lit 0) A10K2.u6394 from rfl, allE_node, arows6331, irow6395, arows6394]
  all_goals rfl

theorem atot6395 : totK PA10K2 A10K2.u6395 = [11375658710906, 73879801408050, 183379301625589, 212301537778370, 112241519083006, 24245676143663, 2038298961584, 49298250236, 0, 0] := by
  rw [show A10K2.u6395 = KTree.node A10K2.u6331 (nat_lit 105818410) (nat_lit 12288443943) (nat_lit 0) A10K2.u6394 from rfl, totK_node, atot6331, atot6394]
  decide +kernel

theorem arows6523 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6523 = true := by
  rw [show A10K2.u6523 = KTree.node A10K2.u6459 (nat_lit 106898608) (nat_lit 9676292772) (nat_lit 0) A10K2.u6522 from rfl, allE_node, arows6459, irow6523, arows6522]
  all_goals rfl

theorem atot6523 : totK PA10K2 A10K2.u6523 = [4530211197570, 40691771212919, 136844381462553, 218230775716250, 167685157230648, 55316768260807, 6526688936384, 217679926684, 0, 0] := by
  rw [show A10K2.u6523 = KTree.node A10K2.u6459 (nat_lit 106898608) (nat_lit 9676292772) (nat_lit 0) A10K2.u6522 from rfl, totK_node, atot6459, atot6522]
  decide +kernel

theorem arows6650 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6650 = true := by
  rw [show A10K2.u6650 = KTree.node A10K2.u6586 (nat_lit 108410096) (nat_lit 6341964461) (nat_lit 0) A10K2.u6649 from rfl, allE_node, arows6586, irow6650, arows6649]
  all_goals rfl

theorem atot6650 : totK PA10K2 A10K2.u6650 = [2231826234337, 22279097994427, 90455753235440, 185691065082381, 197057028181818, 99118940147840, 20921088818081, 1822931180153, 49040628908, 0] := by
  rw [show A10K2.u6650 = KTree.node A10K2.u6586 (nat_lit 108410096) (nat_lit 6341964461) (nat_lit 0) A10K2.u6649 from rfl, totK_node, atot6586, atot6649]
  decide +kernel

theorem arows6779 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6779 = true := by
  rw [show A10K2.u6779 = KTree.node A10K2.u6715 (nat_lit 113864695) (nat_lit 14899910164) (nat_lit 0) A10K2.u6778 from rfl, allE_node, arows6715, irow6779, arows6778]
  all_goals rfl

theorem atot6779 : totK PA10K2 A10K2.u6779 = [9387138901386, 65543282417481, 174544640474476, 217615336994737, 125614094986607, 30010116622264, 2819149609910, 84754522229, 0, 0] := by
  rw [show A10K2.u6779 = KTree.node A10K2.u6715 (nat_lit 113864695) (nat_lit 14899910164) (nat_lit 0) A10K2.u6778 from rfl, totK_node, atot6715, atot6778]
  decide +kernel

theorem arows6906 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6906 = true := by
  rw [show A10K2.u6906 = KTree.node A10K2.u6842 (nat_lit 115172246) (nat_lit 15858125233) (nat_lit 0) A10K2.u6905 from rfl, allE_node, arows6842, irow6906, arows6905]
  all_goals rfl

theorem atot6906 : totK PA10K2 A10K2.u6906 = [6593558482649, 49730268279669, 148108247412811, 215725967949670, 153850231760465, 47473104298715, 5180402239263, 149847106250, 0, 0] := by
  rw [show A10K2.u6906 = KTree.node A10K2.u6842 (nat_lit 115172246) (nat_lit 15858125233) (nat_lit 0) A10K2.u6905 from rfl, totK_node, atot6842, atot6905]
  decide +kernel

theorem arows7034 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7034 = true := by
  rw [show A10K2.u7034 = KTree.node A10K2.u6970 (nat_lit 116123418) (nat_lit 14339429804) (nat_lit 0) A10K2.u7033 from rfl, allE_node, arows6970, irow7034, arows7033]
  all_goals rfl

theorem atot7034 : totK PA10K2 A10K2.u7034 = [0, 12409282954162, 79623795302812, 192914058053039, 214176338700209, 105416183793329, 20035722196687, 1316425935674, 14618254231, 0] := by
  rw [show A10K2.u7034 = KTree.node A10K2.u6970 (nat_lit 116123418) (nat_lit 14339429804) (nat_lit 0) A10K2.u7033 from rfl, totK_node, atot6970, atot7033]
  decide +kernel

theorem arows7161 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7161 = true := by
  rw [show A10K2.u7161 = KTree.node A10K2.u7097 (nat_lit 117498220) (nat_lit 11336805943) (nat_lit 0) A10K2.u7160 from rfl, allE_node, arows7097, irow7161, arows7160]
  all_goals rfl

theorem atot7161 : totK PA10K2 A10K2.u7161 = [0, 7136775914194, 54043544835199, 158490004970385, 219631538431346, 141846316215379, 37801071493996, 3942281661560, 129173110282, 0] := by
  rw [show A10K2.u7161 = KTree.node A10K2.u7097 (nat_lit 117498220) (nat_lit 11336805943) (nat_lit 0) A10K2.u7160 from rfl, totK_node, atot7097, atot7160]
  decide +kernel

theorem arows7291 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7291 = true := by
  rw [show A10K2.u7291 = KTree.node A10K2.u7227 (nat_lit 119107568) (nat_lit 13373440222) (nat_lit 0) A10K2.u7290 from rfl, allE_node, arows7227, irow7291, arows7290]
  all_goals rfl

theorem atot7291 : totK PA10K2 A10K2.u7291 = [0, 9621105985778, 66640892685532, 175670694631936, 216630578816446, 124433648052086, 31219133175528, 3075470191311, 94290123721, 0] := by
  rw [show A10K2.u7291 = KTree.node A10K2.u7227 (nat_lit 119107568) (nat_lit 13373440222) (nat_lit 0) A10K2.u7290 from rfl, totK_node, atot7227, atot7290]
  decide +kernel

theorem arows7418 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7418 = true := by
  rw [show A10K2.u7418 = KTree.node A10K2.u7354 (nat_lit 120024218) (nat_lit 15008522642) (nat_lit 0) A10K2.u7417 from rfl, allE_node, arows7354, irow7418, arows7417]
  all_goals rfl

theorem atot7418 : totK PA10K2 A10K2.u7418 = [0, 0, 16326099511034, 98663157833453, 216735688229327, 203276355498527, 76643066282973, 11550170885115, 667813638016, 7903172220] := by
  rw [show A10K2.u7418 = KTree.node A10K2.u7354 (nat_lit 120024218) (nat_lit 15008522642) (nat_lit 0) A10K2.u7417 from rfl, totK_node, atot7354, atot7417]
  decide +kernel

theorem arows7546 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7546 = true := by
  rw [show A10K2.u7546 = KTree.node A10K2.u7482 (nat_lit 122564565) (nat_lit 2562187344) (nat_lit 0) A10K2.u7545 from rfl, allE_node, arows7482, irow7546, arows7545]
  all_goals rfl

theorem atot7546 : totK PA10K2 A10K2.u7546 = [0, 10645202853858, 70785342158762, 179591830194362, 212656461770538, 115789622766210, 27167801891962, 2802043511076, 104053893714, 0] := by
  rw [show A10K2.u7546 = KTree.node A10K2.u7482 (nat_lit 122564565) (nat_lit 2562187344) (nat_lit 0) A10K2.u7545 from rfl, totK_node, atot7482, atot7545]
  decide +kernel

theorem arows7673 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7673 = true := by
  rw [show A10K2.u7673 = KTree.node A10K2.u7609 (nat_lit 123593156) (nat_lit 6153038675) (nat_lit 0) A10K2.u7672 from rfl, allE_node, arows7609, irow7673, arows7672]
  all_goals rfl

theorem atot7673 : totK PA10K2 A10K2.u7673 = [0, 6132911655538, 47194588977809, 144303724308687, 216834015443969, 160013677447968, 51438816410242, 6172751092714, 217794735578, 0] := by
  rw [show A10K2.u7673 = KTree.node A10K2.u7609 (nat_lit 123593156) (nat_lit 6153038675) (nat_lit 0) A10K2.u7672 from rfl, totK_node, atot7609, atot7672]
  decide +kernel

theorem arows7802 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7802 = true := by
  rw [show A10K2.u7802 = KTree.node A10K2.u7738 (nat_lit 125428900) (nat_lit 11710391584) (nat_lit 0) A10K2.u7801 from rfl, allE_node, arows7738, irow7802, arows7801]
  all_goals rfl

theorem atot7802 : totK PA10K2 A10K2.u7802 = [0, 5803240664210, 45512583802314, 138946575140806, 208520465483366, 159601024444261, 58879580825090, 9516570298095, 618672627265, 8047840951] := by
  rw [show A10K2.u7802 = KTree.node A10K2.u7738 (nat_lit 125428900) (nat_lit 11710391584) (nat_lit 0) A10K2.u7801 from rfl, totK_node, atot7738, atot7801]
  decide +kernel

theorem arows7929 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7929 = true := by
  rw [show A10K2.u7929 = KTree.node A10K2.u7865 (nat_lit 130889975) (nat_lit 12753469531) (nat_lit 0) A10K2.u7928 from rfl, allE_node, arows7865, irow7929, arows7928]
  all_goals rfl

theorem atot7929 : totK PA10K2 A10K2.u7929 = [0, 12409282954162, 77257084834543, 185719457722111, 212472213141135, 113648090130712, 24353754239556, 1816655287812, 26941117290, 0] := by
  rw [show A10K2.u7929 = KTree.node A10K2.u7865 (nat_lit 130889975) (nat_lit 12753469531) (nat_lit 0) A10K2.u7928 from rfl, totK_node, atot7865, atot7928]
  decide +kernel

theorem arows8057 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8057 = true := by
  rw [show A10K2.u8057 = KTree.node A10K2.u7993 (nat_lit 132176032) (nat_lit 8903101978) (nat_lit 0) A10K2.u8056 from rfl, allE_node, arows7993, irow8057, arows8056]
  all_goals rfl

theorem atot8057 : totK PA10K2 A10K2.u8057 = [0, 0, 17780963846951, 101874161057378, 215784651943601, 201410800895138, 79333458834141, 11843053790659, 616265555607, 7237400819] := by
  rw [show A10K2.u8057 = KTree.node A10K2.u7993 (nat_lit 132176032) (nat_lit 8903101978) (nat_lit 0) A10K2.u8056 from rfl, totK_node, atot7993, atot8056]
  decide +kernel

theorem arows8184 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8184 = true := by
  rw [show A10K2.u8184 = KTree.node A10K2.u8120 (nat_lit 133791304) (nat_lit 12260840781) (nat_lit 0) A10K2.u8183 from rfl, allE_node, arows8120, irow8184, arows8183]
  all_goals rfl

theorem atot8184 : totK PA10K2 A10K2.u8184 = [0, 0, 9405517331120, 66333298096829, 176602512839225, 217954310856596, 126333836830449, 30755134183407, 3035046893303, 94743209073] := by
  rw [show A10K2.u8184 = KTree.node A10K2.u8120 (nat_lit 133791304) (nat_lit 12260840781) (nat_lit 0) A10K2.u8183 from rfl, totK_node, atot8120, atot8183]
  decide +kernel

theorem arows254 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u254 = true := by
  rw [show A10K2.u254 = KTree.node A10K2.u126 (nat_lit 1396784) (nat_lit 14354971656) (nat_lit 0) A10K2.u253 from rfl, allE_node, arows126, irow254, arows253]
  all_goals rfl

theorem atot254 : totK PA10K2 A10K2.u254 = [18061404581860, 126592369863100, 340500484677740, 431117033049671, 253880149590536, 63136960547494, 6128267414389, 178274101355, 0, 0] := by
  rw [show A10K2.u254 = KTree.node A10K2.u126 (nat_lit 1396784) (nat_lit 14354971656) (nat_lit 0) A10K2.u253 from rfl, totK_node, atot126, atot253]
  decide +kernel

theorem arows509 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u509 = true := by
  rw [show A10K2.u509 = KTree.node A10K2.u381 (nat_lit 3882213) (nat_lit 1802695513) (nat_lit 0) A10K2.u508 from rfl, allE_node, arows381, irow509, arows508]
  all_goals rfl

theorem atot509 : totK PA10K2 A10K2.u509 = [10348199800192, 78424036527508, 244521930131993, 395557940530046, 339027796342907, 139526520123889, 25010616044604, 1911496027504, 47787176431, 0] := by
  rw [show A10K2.u509 = KTree.node A10K2.u381 (nat_lit 3882213) (nat_lit 1802695513) (nat_lit 0) A10K2.u508 from rfl, totK_node, atot381, atot508]
  decide +kernel

theorem arows765 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u765 = true := by
  rw [show A10K2.u765 = KTree.node A10K2.u637 (nat_lit 11119269) (nat_lit 7210046638) (nat_lit 0) A10K2.u764 from rfl, allE_node, arows637, irow765, arows764]
  all_goals rfl

theorem atot765 : totK PA10K2 A10K2.u765 = [12260174575398, 94666497035387, 286834832573661, 422543369064025, 302882329081495, 94289416551473, 12657182781005, 704655692674, 6354482628, 0] := by
  rw [show A10K2.u765 = KTree.node A10K2.u637 (nat_lit 11119269) (nat_lit 7210046638) (nat_lit 0) A10K2.u764 from rfl, totK_node, atot637, atot764]
  decide +kernel

theorem arows1020 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1020 = true := by
  rw [show A10K2.u1020 = KTree.node A10K2.u892 (nat_lit 14417798) (nat_lit 15945280963) (nat_lit 0) A10K2.u1019 from rfl, allE_node, arows892, irow1020, arows1019]
  all_goals rfl

theorem atot1020 : totK PA10K2 A10K2.u1020 = [10850168185780, 87149472982027, 274855247048299, 424759785457873, 326497596001434, 114976800968966, 16650777744841, 879496488079, 7237400819, 0] := by
  rw [show A10K2.u1020 = KTree.node A10K2.u892 (nat_lit 14417798) (nat_lit 15945280963) (nat_lit 0) A10K2.u1019 from rfl, totK_node, atot892, atot1019]
  decide +kernel

theorem arows1277 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1277 = true := by
  rw [show A10K2.u1277 = KTree.node A10K2.u1149 (nat_lit 16812128) (nat_lit 13699160110) (nat_lit 0) A10K2.u1276 from rfl, allE_node, arows1149, irow1277, arows1276]
  all_goals rfl

theorem atot1277 : totK PA10K2 A10K2.u1277 = [0, 19434914513688, 134940940600758, 356118533915241, 434366855303233, 239101252931293, 53577597593919, 4768130800032, 136553963694, 0] := by
  rw [show A10K2.u1277 = KTree.node A10K2.u1149 (nat_lit 16812128) (nat_lit 13699160110) (nat_lit 0) A10K2.u1276 from rfl, totK_node, atot1149, atot1276]
  decide +kernel

theorem arows1532 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1532 = true := by
  rw [show A10K2.u1532 = KTree.node A10K2.u1404 (nat_lit 19187748) (nat_lit 13755931144) (nat_lit 0) A10K2.u1531 from rfl, allE_node, arows1404, irow1532, arows1531]
  all_goals rfl

theorem atot1532 : totK PA10K2 A10K2.u1532 = [0, 8965703513581, 73750865519725, 244976776037145, 409114174204596, 344810788674062, 134569750112163, 23634587522329, 1878559683283, 47787176431] := by
  rw [show A10K2.u1532 = KTree.node A10K2.u1404 (nat_lit 19187748) (nat_lit 13755931144) (nat_lit 0) A10K2.u1531 from rfl, totK_node, atot1404, atot1531]
  decide +kernel

theorem arows1788 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1788 = true := by
  rw [show A10K2.u1788 = KTree.node A10K2.u1660 (nat_lit 26335745) (nat_lit 9763450910) (nat_lit 0) A10K2.u1787 from rfl, allE_node, arows1660, irow1788, arows1787]
  all_goals rfl

theorem atot1788 : totK PA10K2 A10K2.u1788 = [0, 13471251100559, 109071895487402, 327072756789767, 445430946406449, 265909851655822, 61610345054643, 5617097546980, 152103962338, 0] := by
  rw [show A10K2.u1788 = KTree.node A10K2.u1660 (nat_lit 26335745) (nat_lit 9763450910) (nat_lit 0) A10K2.u1787 from rfl, totK_node, atot1660, atot1787]
  decide +kernel

theorem arows2043 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2043 = true := by
  rw [show A10K2.u2043 = KTree.node A10K2.u1915 (nat_lit 30127515) (nat_lit 9859220283) (nat_lit 0) A10K2.u2042 from rfl, allE_node, arows1915, irow2043, arows2042]
  all_goals rfl

theorem atot2043 : totK PA10K2 A10K2.u2043 = [2808829852973, 32349844927168, 143930286750058, 327468333699143, 402987446657574, 256608394872033, 74721286700677, 9636788365774, 487522872751, 6354482628] := by
  rw [show A10K2.u2043 = KTree.node A10K2.u1915 (nat_lit 30127515) (nat_lit 9859220283) (nat_lit 0) A10K2.u2042 from rfl, totK_node, atot1915, atot2042]
  decide +kernel

theorem arows2301 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2301 = true := by
  rw [show A10K2.u2301 = KTree.node A10K2.u2173 (nat_lit 39347385) (nat_lit 5306908948) (nat_lit 0) A10K2.u2300 from rfl, allE_node, arows2173, irow2301, arows2300]
  all_goals rfl

theorem atot2301 : totK PA10K2 A10K2.u2301 = [15269390501638, 111335598735911, 315744553480876, 430009329212150, 281762041863127, 80651572744469, 8803540664093, 273940919271, 0, 0] := by
  rw [show A10K2.u2301 = KTree.node A10K2.u2173 (nat_lit 39347385) (nat_lit 5306908948) (nat_lit 0) A10K2.u2300 from rfl, totK_node, atot2173, atot2300]
  decide +kernel

theorem arows2556 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2556 = true := by
  rw [show A10K2.u2556 = KTree.node A10K2.u2428 (nat_lit 41946524) (nat_lit 11933677) (nat_lit 0) A10K2.u2555 from rfl, allE_node, arows2428, irow2556, arows2555]
  all_goals rfl

theorem atot2556 : totK PA10K2 A10K2.u2556 = [10796771682706, 81784839366368, 252394248122714, 398517823871692, 330657663705884, 133689900086863, 24210459278051, 1918070933506, 49040628908, 0] := by
  rw [show A10K2.u2556 = KTree.node A10K2.u2428 (nat_lit 41946524) (nat_lit 11933677) (nat_lit 0) A10K2.u2555 from rfl, totK_node, atot2428, atot2555]
  decide +kernel

theorem arows2812 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2812 = true := by
  rw [show A10K2.u2812 = KTree.node A10K2.u2684 (nat_lit 44789646) (nat_lit 15075358843) (nat_lit 0) A10K2.u2811 from rfl, allE_node, arows2684, irow2812, arows2811]
  all_goals rfl

theorem atot2812 : totK PA10K2 A10K2.u2812 = [11061402114120, 89677318803455, 281385497323749, 425644818578529, 311007980155835, 98271270483847, 13297529071524, 734692675017, 6354482628, 0] := by
  rw [show A10K2.u2812 = KTree.node A10K2.u2684 (nat_lit 44789646) (nat_lit 15075358843) (nat_lit 0) A10K2.u2811 from rfl, totK_node, atot2684, atot2811]
  decide +kernel

theorem arows3067 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3067 = true := by
  rw [show A10K2.u3067 = KTree.node A10K2.u2939 (nat_lit 48048996) (nat_lit 13706250501) (nat_lit 0) A10K2.u3066 from rfl, allE_node, arows2939, irow3067, arows3066]
  all_goals rfl

theorem atot3067 : totK PA10K2 A10K2.u3067 = [11599087068976, 89766134002738, 274955672896868, 418438020560939, 324668900113625, 119121695591379, 17822076425685, 944803666336, 7237400819, 0] := by
  rw [show A10K2.u3067 = KTree.node A10K2.u2939 (nat_lit 48048996) (nat_lit 13706250501) (nat_lit 0) A10K2.u3066 from rfl, totK_node, atot2939, atot3066]
  decide +kernel

theorem arows3324 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3324 = true := by
  rw [show A10K2.u3324 = KTree.node A10K2.u3196 (nat_lit 55214363) (nat_lit 7903330282) (nat_lit 0) A10K2.u3323 from rfl, allE_node, arows3196, irow3324, arows3323]
  all_goals rfl

theorem atot3324 : totK PA10K2 A10K2.u3324 = [0, 20815122379276, 139785660436738, 358492038915166, 429363936811137, 236991509953296, 54362419855324, 4963976335954, 144041459309, 0] := by
  rw [show A10K2.u3324 = KTree.node A10K2.u3196 (nat_lit 55214363) (nat_lit 7903330282) (nat_lit 0) A10K2.u3323 from rfl, totK_node, atot3196, atot3323]
  decide +kernel

theorem arows3579 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3579 = true := by
  rw [show A10K2.u3579 = KTree.node A10K2.u3451 (nat_lit 57563287) (nat_lit 10053429044) (nat_lit 0) A10K2.u3578 from rfl, allE_node, arows3451, irow3579, arows3578]
  all_goals rfl

theorem atot3579 : totK PA10K2 A10K2.u3579 = [0, 7984560311664, 69710244773425, 239841259533671, 408486518409235, 350932155042565, 140521708245039, 24720423707327, 1929836889666, 49040628908] := by
  rw [show A10K2.u3579 = KTree.node A10K2.u3451 (nat_lit 57563287) (nat_lit 10053429044) (nat_lit 0) A10K2.u3578 from rfl, totK_node, atot3451, atot3578]
  decide +kernel

theorem arows3835 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3835 = true := by
  rw [show A10K2.u3835 = KTree.node A10K2.u3707 (nat_lit 59918336) (nat_lit 15064410632) (nat_lit 0) A10K2.u3834 from rfl, allE_node, arows3707, irow3835, arows3834]
  all_goals rfl

theorem atot3835 : totK PA10K2 A10K2.u3835 = [0, 12228426095412, 101830975954234, 316414132326520, 449242459549121, 279797177434469, 66333659326937, 6004978373423, 159796104225, 0] := by
  rw [show A10K2.u3835 = KTree.node A10K2.u3707 (nat_lit 59918336) (nat_lit 15064410632) (nat_lit 0) A10K2.u3834 from rfl, totK_node, atot3707, atot3834]
  decide +kernel

theorem arows4090 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4090 = true := by
  rw [show A10K2.u4090 = KTree.node A10K2.u3962 (nat_lit 63783777) (nat_lit 5904482456) (nat_lit 2) A10K2.u4089 from rfl, allE_node, arows3962, irow4090, arows4089]
  all_goals rfl

theorem atot4090 : totK PA10K2 A10K2.u4090 = [2338692983822, 29377466251237, 137282526229790, 320866165800970, 404653430082013, 266294375603822, 79589769765683, 10364530486233, 541278879299, 6354482628] := by
  rw [show A10K2.u4090 = KTree.node A10K2.u3962 (nat_lit 63783777) (nat_lit 5904482456) (nat_lit 2) A10K2.u4089 from rfl, totK_node, atot3962, atot4089]
  decide +kernel

theorem arows4349 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4349 = true := by
  rw [show A10K2.u4349 = KTree.node A10K2.u4221 (nat_lit 68606765) (nat_lit 6621766139) (nat_lit 0) A10K2.u4348 from rfl, allE_node, arows4221, irow4349, arows4348]
  all_goals rfl

theorem atot4349 : totK PA10K2 A10K2.u4349 = [14346398076988, 104703596455602, 298053438398092, 414229599942101, 289256485724211, 98740966537293, 16193004638728, 1261115033954, 36134558889, 0] := by
  rw [show A10K2.u4349 = KTree.node A10K2.u4221 (nat_lit 68606765) (nat_lit 6621766139) (nat_lit 0) A10K2.u4348 from rfl, totK_node, atot4221, atot4348]
  decide +kernel

theorem arows4604 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4604 = true := by
  rw [show A10K2.u4604 = KTree.node A10K2.u4476 (nat_lit 72031666) (nat_lit 13770425449) (nat_lit 0) A10K2.u4603 from rfl, allE_node, arows4476, irow4604, arows4603]
  all_goals rfl

theorem atot4604 : totK PA10K2 A10K2.u4604 = [14460508449646, 104309319859295, 297041024345001, 416861018481378, 293125759134266, 95449041453645, 13644217664386, 784906462284, 11652617542, 0] := by
  rw [show A10K2.u4604 = KTree.node A10K2.u4476 (nat_lit 72031666) (nat_lit 13770425449) (nat_lit 0) A10K2.u4603 from rfl, totK_node, atot4476, atot4603]
  decide +kernel

theorem arows4860 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4860 = true := by
  rw [show A10K2.u4860 = KTree.node A10K2.u4732 (nat_lit 74498061) (nat_lit 5771049398) (nat_lit 0) A10K2.u4859 from rfl, allE_node, arows4732, irow4860, arows4859]
  all_goals rfl

theorem atot4860 : totK PA10K2 A10K2.u4860 = [7985969458073, 67121431861694, 228822188843469, 397076105239232, 358891703383503, 153078134294411, 27311839265278, 2043713705078, 49040628908, 0] := by
  rw [show A10K2.u4860 = KTree.node A10K2.u4732 (nat_lit 74498061) (nat_lit 5771049398) (nat_lit 0) A10K2.u4859 from rfl, totK_node, atot4732, atot4859]
  decide +kernel

theorem arows5115 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5115 = true := by
  rw [show A10K2.u5115 = KTree.node A10K2.u4987 (nat_lit 76670134) (nat_lit 16118998823) (nat_lit 0) A10K2.u5114 from rfl, allE_node, arows4987, irow5115, arows5114]
  all_goals rfl

theorem atot5115 : totK PA10K2 A10K2.u5115 = [12194929445975, 99422929539609, 306266692088399, 439209541229190, 288276270744140, 76757914516899, 7678075220255, 221391663300, 0, 0] := by
  rw [show A10K2.u5115 = KTree.node A10K2.u4987 (nat_lit 76670134) (nat_lit 16118998823) (nat_lit 0) A10K2.u5114 from rfl, totK_node, atot4987, atot5114]
  decide +kernel

theorem arows5372 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5372 = true := by
  rw [show A10K2.u5372 = KTree.node A10K2.u5244 (nat_lit 84348992) (nat_lit 15482570017) (nat_lit 0) A10K2.u5371 from rfl, allE_node, arows5244, irow5372, arows5371]
  all_goals rfl

theorem atot5372 : totK PA10K2 A10K2.u5372 = [0, 22666836095544, 150483862909072, 376332600493346, 427107602674917, 209649713286219, 41313982790028, 3205883956705, 61527694292, 0] := by
  rw [show A10K2.u5372 = KTree.node A10K2.u5244 (nat_lit 84348992) (nat_lit 15482570017) (nat_lit 0) A10K2.u5371 from rfl, totK_node, atot5244, atot5371]
  decide +kernel

theorem arows5627 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5627 = true := by
  rw [show A10K2.u5627 = KTree.node A10K2.u5499 (nat_lit 89537943) (nat_lit 14261435481) (nat_lit 0) A10K2.u5626 from rfl, allE_node, arows5499, irow5627, arows5626]
  all_goals rfl

theorem atot5627 : totK PA10K2 A10K2.u5627 = [0, 20846062817236, 141748401346086, 365793656521002, 433224710279568, 226150358800121, 46696616617750, 3830144574863, 98260185807, 0] := by
  rw [show A10K2.u5627 = KTree.node A10K2.u5499 (nat_lit 89537943) (nat_lit 14261435481) (nat_lit 0) A10K2.u5626 from rfl, totK_node, atot5499, atot5626]
  decide +kernel

theorem arows5883 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5883 = true := by
  rw [show A10K2.u5883 = KTree.node A10K2.u5755 (nat_lit 93721481) (nat_lit 7039285864) (nat_lit 0) A10K2.u5882 from rfl, allE_node, arows5755, irow5883, arows5882]
  all_goals rfl

theorem atot5883 : totK PA10K2 A10K2.u5883 = [0, 12194929445975, 98820048101380, 304915644053168, 438992404624674, 285709685843052, 73846360848991, 8058262113609, 288413966189, 0] := by
  rw [show A10K2.u5883 = KTree.node A10K2.u5755 (nat_lit 93721481) (nat_lit 7039285864) (nat_lit 0) A10K2.u5882 from rfl, totK_node, atot5755, atot5882]
  decide +kernel

theorem arows6138 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6138 = true := by
  rw [show A10K2.u6138 = KTree.node A10K2.u6010 (nat_lit 102115156) (nat_lit 12357747037) (nat_lit 0) A10K2.u6137 from rfl, allE_node, arows6010, irow6138, arows6137]
  all_goals rfl

theorem atot6138 : totK PA10K2 A10K2.u6138 = [16757881899972, 117756165064816, 319370891776193, 413378573949587, 261189875550096, 86568340202701, 22638152009136, 4670249159213, 446040892095, 6354482628] := by
  rw [show A10K2.u6138 = KTree.node A10K2.u6010 (nat_lit 102115156) (nat_lit 12357747037) (nat_lit 0) A10K2.u6137 from rfl, totK_node, atot6010, atot6137]
  decide +kernel

theorem arows6396 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6396 = true := by
  rw [show A10K2.u6396 = KTree.node A10K2.u6268 (nat_lit 105461077) (nat_lit 6602162936) (nat_lit 0) A10K2.u6395 from rfl, allE_node, arows6268, irow6396, arows6395]
  all_goals rfl

theorem atot6396 : totK PA10K2 A10K2.u6396 = [12247903311826, 87745013331661, 258733579456717, 396952876093541, 325716547710791, 131610520953352, 23910769183054, 1869803773328, 47787176431, 0] := by
  rw [show A10K2.u6396 = KTree.node A10K2.u6268 (nat_lit 105461077) (nat_lit 6602162936) (nat_lit 0) A10K2.u6395 from rfl, totK_node, atot6268, atot6395]
  decide +kernel

theorem arows6651 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6651 = true := by
  rw [show A10K2.u6651 = KTree.node A10K2.u6523 (nat_lit 107836691) (nat_lit 10801545055) (nat_lit 0) A10K2.u6650 from rfl, allE_node, arows6523, irow6651, arows6650]
  all_goals rfl

theorem atot6651 : totK PA10K2 A10K2.u6651 = [6762037431907, 62970869207346, 227300134697993, 403921840798631, 364752986957521, 154435708408647, 27447777754465, 2040611106837, 49040628908, 0] := by
  rw [show A10K2.u6651 = KTree.node A10K2.u6523 (nat_lit 107836691) (nat_lit 10801545055) (nat_lit 0) A10K2.u6650 from rfl, totK_node, atot6523, atot6650]
  decide +kernel

theorem arows6907 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6907 = true := by
  rw [show A10K2.u6907 = KTree.node A10K2.u6779 (nat_lit 114261662) (nat_lit 15118434259) (nat_lit 0) A10K2.u6906 from rfl, allE_node, arows6779, irow6907, arows6906]
  all_goals rfl

theorem atot6907 : totK PA10K2 A10K2.u6907 = [15980697384035, 115273550697150, 322652887887287, 433341304944407, 279479445181331, 77483220920979, 7999551849173, 234601628479, 0, 0] := by
  rw [show A10K2.u6907 = KTree.node A10K2.u6779 (nat_lit 114261662) (nat_lit 15118434259) (nat_lit 0) A10K2.u6906 from rfl, totK_node, atot6779, atot6906]
  decide +kernel

theorem arows7162 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7162 = true := by
  rw [show A10K2.u7162 = KTree.node A10K2.u7034 (nat_lit 117145924) (nat_lit 11759720216) (nat_lit 0) A10K2.u7161 from rfl, allE_node, arows7034, irow7162, arows7161]
  all_goals rfl

theorem atot7162 : totK PA10K2 A10K2.u7162 = [0, 19546058868356, 133667340138011, 351415822743640, 433807877131555, 247262500008708, 57836793690683, 5258707597234, 143791364513, 0] := by
  rw [show A10K2.u7162 = KTree.node A10K2.u7034 (nat_lit 117145924) (nat_lit 11759720216) (nat_lit 0) A10K2.u7161 from rfl, totK_node, atot7034, atot7161]
  decide +kernel

theorem arows7419 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7419 = true := by
  rw [show A10K2.u7419 = KTree.node A10K2.u7291 (nat_lit 119539788) (nat_lit 10942262896) (nat_lit 0) A10K2.u7418 from rfl, allE_node, arows7291, irow7419, arows7418]
  all_goals rfl

theorem atot7419 : totK PA10K2 A10K2.u7419 = [0, 9621105985778, 82966992196566, 274333852465389, 433377209308669, 327710003550613, 107862199458501, 14625641076426, 762103761737, 7903172220] := by
  rw [show A10K2.u7419 = KTree.node A10K2.u7291 (nat_lit 119539788) (nat_lit 10942262896) (nat_lit 0) A10K2.u7418 from rfl, totK_node, atot7291, atot7418]
  decide +kernel

theorem arows7674 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7674 = true := by
  rw [show A10K2.u7674 = KTree.node A10K2.u7546 (nat_lit 123132449) (nat_lit 9639895118) (nat_lit 0) A10K2.u7673 from rfl, allE_node, arows7546, irow7674, arows7673]
  all_goals rfl

theorem atot7674 : totK PA10K2 A10K2.u7674 = [0, 16778114509396, 117979931136571, 323895554503049, 429490477214507, 275803300214178, 78616258197322, 8974794603790, 321848629292, 0] := by
  rw [show A10K2.u7674 = KTree.node A10K2.u7546 (nat_lit 123132449) (nat_lit 9639895118) (nat_lit 0) A10K2.u7673 from rfl, totK_node, atot7546, atot7673]
  decide +kernel

theorem arows7930 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7930 = true := by
  rw [show A10K2.u7930 = KTree.node A10K2.u7802 (nat_lit 130314633) (nat_lit 9534329249) (nat_lit 0) A10K2.u7929 from rfl, allE_node, arows7802, irow7930, arows7929]
  all_goals rfl

theorem atot7930 : totK PA10K2 A10K2.u7930 = [0, 18212523618372, 122769668636857, 324666032862917, 420992678624501, 273258648904222, 83233335064646, 11333225585907, 645613744555, 8047840951] := by
  rw [show A10K2.u7930 = KTree.node A10K2.u7802 (nat_lit 130314633) (nat_lit 9534329249) (nat_lit 0) A10K2.u7929 from rfl, totK_node, atot7802, atot7929]
  decide +kernel

theorem arows8185 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8185 = true := by
  rw [show A10K2.u8185 = KTree.node A10K2.u8057 (nat_lit 132788218) (nat_lit 12709691639) (nat_lit 0) A10K2.u8184 from rfl, allE_node, arows8057, irow8185, arows8184]
  all_goals rfl

theorem atot8185 : totK PA10K2 A10K2.u8185 = [0, 0, 27186481178071, 168207459154207, 392387164782826, 419377821443373, 205667295664590, 42598187974066, 3651312448910, 101980609892] := by
  rw [show A10K2.u8185 = KTree.node A10K2.u8057 (nat_lit 132788218) (nat_lit 12709691639) (nat_lit 0) A10K2.u8184 from rfl, totK_node, atot8057, atot8184]
  decide +kernel

theorem arows510 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u510 = true := by
  rw [show A10K2.u510 = KTree.node A10K2.u254 (nat_lit 2322953) (nat_lit 9752284467) (nat_lit 0) A10K2.u509 from rfl, allE_node, arows254, irow510, arows509]
  all_goals rfl

theorem atot510 : totK PA10K2 A10K2.u510 = [28409604382052, 205016406390608, 585022414809733, 826674973579717, 592907945933443, 202673232955850, 31138883458993, 2089770128859, 47787176431, 0] := by
  rw [show A10K2.u510 = KTree.node A10K2.u254 (nat_lit 2322953) (nat_lit 9752284467) (nat_lit 0) A10K2.u509 from rfl, totK_node, atot254, atot509]
  decide +kernel

theorem arows1021 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1021 = true := by
  rw [show A10K2.u1021 = KTree.node A10K2.u765 (nat_lit 12850026) (nat_lit 4745329050) (nat_lit 0) A10K2.u1020 from rfl, allE_node, arows765, irow1021, arows1020]
  all_goals rfl

theorem atot1021 : totK PA10K2 A10K2.u1021 = [23110342761178, 181815970017414, 561690079621960, 847303154521898, 629379925082929, 209270962849489, 29307960525846, 1584152180753, 13591883447, 0] := by
  rw [show A10K2.u1021 = KTree.node A10K2.u765 (nat_lit 12850026) (nat_lit 4745329050) (nat_lit 0) A10K2.u1020 from rfl, totK_node, atot765, atot1020]
  decide +kernel

theorem arows1533 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1533 = true := by
  rw [show A10K2.u1533 = KTree.node A10K2.u1277 (nat_lit 18270899) (nat_lit 9766283151) (nat_lit 0) A10K2.u1532 from rfl, allE_node, arows1277, irow1533, arows1532]
  all_goals rfl

theorem atot1533 : totK PA10K2 A10K2.u1533 = [0, 28400618027269, 208691806120483, 601095309952386, 843481029507829, 583921807888506, 188147347706082, 28402718322361, 2015113646977, 47787176431] := by
  rw [show A10K2.u1533 = KTree.node A10K2.u1277 (nat_lit 18270899) (nat_lit 9766283151) (nat_lit 0) A10K2.u1532 from rfl, totK_node, atot1277, atot1532]
  decide +kernel

theorem arows2044 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2044 = true := by
  rw [show A10K2.u2044 = KTree.node A10K2.u1788 (nat_lit 28456621) (nat_lit 5897492707) (nat_lit 0) A10K2.u2043 from rfl, allE_node, arows1788, irow2044, arows2043]
  all_goals rfl

theorem atot2044 : totK PA10K2 A10K2.u2044 = [2808829852973, 45821096027727, 253002182237460, 654541090488910, 848418393064023, 522518246527855, 136337529248027, 15253885912754, 639626835089, 6354482628] := by
  rw [show A10K2.u2044 = KTree.node A10K2.u1788 (nat_lit 28456621) (nat_lit 5897492707) (nat_lit 0) A10K2.u2043 from rfl, totK_node, atot1788, atot2043]
  decide +kernel

theorem arows2557 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2557 = true := by
  rw [show A10K2.u2557 = KTree.node A10K2.u2301 (nat_lit 40729843) (nat_lit 9707562710) (nat_lit 0) A10K2.u2556 from rfl, allE_node, arows2301, irow2557, arows2556]
  all_goals rfl

theorem atot2557 : totK PA10K2 A10K2.u2557 = [26066162184344, 193120438102279, 568138801603590, 828527153083842, 612419705569011, 214351180394042, 33013999942144, 2192011852777, 49040628908, 0] := by
  rw [show A10K2.u2557 = KTree.node A10K2.u2301 (nat_lit 40729843) (nat_lit 9707562710) (nat_lit 0) A10K2.u2556 from rfl, totK_node, atot2301, atot2556]
  decide +kernel

theorem arows3068 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3068 = true := by
  rw [show A10K2.u3068 = KTree.node A10K2.u2812 (nat_lit 46742536) (nat_lit 10812405538) (nat_lit 0) A10K2.u3067 from rfl, allE_node, arows2812, irow3068, arows3067]
  all_goals rfl

theorem atot3068 : totK PA10K2 A10K2.u3068 = [22660489183096, 179443452806193, 556351982626155, 844082839139468, 635676880269460, 217392966075226, 31119605497209, 1679496341353, 13591883447, 0] := by
  rw [show A10K2.u3068 = KTree.node A10K2.u2812 (nat_lit 46742536) (nat_lit 10812405538) (nat_lit 0) A10K2.u3067 from rfl, totK_node, atot2812, atot3067]
  decide +kernel

theorem arows3580 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3580 = true := by
  rw [show A10K2.u3580 = KTree.node A10K2.u3324 (nat_lit 56179934) (nat_lit 11418968776) (nat_lit 0) A10K2.u3579 from rfl, allE_node, arows3324, irow3580, arows3579]
  all_goals rfl

theorem atot3580 : totK PA10K2 A10K2.u3580 = [0, 28799682690940, 209495905210163, 598333298448837, 837861874189148, 587923664995861, 194884128100363, 29684400043281, 2073878348975, 49040628908] := by
  rw [show A10K2.u3580 = KTree.node A10K2.u3324 (nat_lit 56179934) (nat_lit 11418968776) (nat_lit 0) A10K2.u3579 from rfl, totK_node, atot3324, atot3579]
  decide +kernel

theorem arows4091 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4091 = true := by
  rw [show A10K2.u4091 = KTree.node A10K2.u3835 (nat_lit 62014340) (nat_lit 8777073235) (nat_lit 0) A10K2.u4090 from rfl, allE_node, arows3835, irow4091, arows4090]
  all_goals rfl

theorem atot4091 : totK PA10K2 A10K2.u4091 = [2338692983822, 41605892346649, 239113502184024, 637289075200725, 853895889631134, 546091553038291, 145923429092620, 16369508859656, 701074983524, 6354482628] := by
  rw [show A10K2.u4091 = KTree.node A10K2.u3835 (nat_lit 62014340) (nat_lit 8777073235) (nat_lit 0) A10K2.u4090 from rfl, totK_node, atot3835, atot4090]
  decide +kernel

theorem arows4605 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4605 = true := by
  rw [show A10K2.u4605 = KTree.node A10K2.u4349 (nat_lit 69652558) (nat_lit 6062837211) (nat_lit 0) A10K2.u4604 from rfl, allE_node, arows4349, irow4605, arows4604]
  all_goals rfl

theorem atot4605 : totK PA10K2 A10K2.u4605 = [28806906526634, 209012916314897, 595094462743093, 831090618423479, 582382244858477, 194190007990938, 29843285140325, 2046021496238, 47787176431, 0] := by
  rw [show A10K2.u4605 = KTree.node A10K2.u4349 (nat_lit 69652558) (nat_lit 6062837211) (nat_lit 0) A10K2.u4604 from rfl, totK_node, atot4349, atot4604]
  decide +kernel

theorem arows5116 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5116 = true := by
  rw [show A10K2.u5116 = KTree.node A10K2.u4860 (nat_lit 75764662) (nat_lit 16421404435) (nat_lit 0) A10K2.u5115 from rfl, allE_node, arows4860, irow5116, arows5115]
  all_goals rfl

theorem atot5116 : totK PA10K2 A10K2.u5116 = [20180898904048, 166544361401303, 535088880931868, 836302067872857, 647167974127643, 229836048811310, 34989914485533, 2265105368378, 49040628908, 0] := by
  rw [show A10K2.u5116 = KTree.node A10K2.u4860 (nat_lit 75764662) (nat_lit 16421404435) (nat_lit 0) A10K2.u5115 from rfl, totK_node, atot4860, atot5115]
  decide +kernel

theorem arows5628 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5628 = true := by
  rw [show A10K2.u5628 = KTree.node A10K2.u5372 (nat_lit 88693409) (nat_lit 7659671435) (nat_lit 0) A10K2.u5627 from rfl, allE_node, arows5372, irow5628, arows5627]
  all_goals rfl

theorem atot5628 : totK PA10K2 A10K2.u5628 = [0, 43512898912780, 292232264255158, 742126257014348, 860339972625920, 435800072086340, 88010599407778, 7036028531568, 159787880099, 0] := by
  rw [show A10K2.u5628 = KTree.node A10K2.u5372 (nat_lit 88693409) (nat_lit 7659671435) (nat_lit 0) A10K2.u5627 from rfl, totK_node, atot5372, atot5627]
  decide +kernel

theorem arows6139 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6139 = true := by
  rw [show A10K2.u6139 = KTree.node A10K2.u5883 (nat_lit 95814408) (nat_lit 13965864106) (nat_lit 0) A10K2.u6138 from rfl, allE_node, arows5883, irow6139, arows6138]
  all_goals rfl

theorem atot6139 : totK PA10K2 A10K2.u6139 = [16757881899972, 129951094510791, 418190939877573, 718294218002755, 700182280174770, 372291991909859, 96484512858127, 12728511272822, 734454858284, 6354482628] := by
  rw [show A10K2.u6139 = KTree.node A10K2.u5883 (nat_lit 95814408) (nat_lit 13965864106) (nat_lit 0) A10K2.u6138 from rfl, totK_node, atot5883, atot6138]
  decide +kernel

theorem arows6652 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6652 = true := by
  rw [show A10K2.u6652 = KTree.node A10K2.u6396 (nat_lit 106458801) (nat_lit 6513720854) (nat_lit 0) A10K2.u6651 from rfl, allE_node, arows6396, irow6652, arows6651]
  all_goals rfl

theorem atot6652 : totK PA10K2 A10K2.u6652 = [19009940743733, 150715882539007, 486040227875564, 800874716892172, 690469534668312, 286046229361999, 51358546937519, 3910414880165, 96827805339, 0] := by
  rw [show A10K2.u6652 = KTree.node A10K2.u6396 (nat_lit 106458801) (nat_lit 6513720854) (nat_lit 0) A10K2.u6651 from rfl, totK_node, atot6396, atot6651]
  decide +kernel

theorem arows7163 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7163 = true := by
  rw [show A10K2.u7163 = KTree.node A10K2.u6907 (nat_lit 115602901) (nat_lit 3761164817) (nat_lit 0) A10K2.u7162 from rfl, allE_node, arows6907, irow7163, arows7162]
  all_goals rfl

theorem atot7163 : totK PA10K2 A10K2.u7163 = [15980697384035, 134819609565506, 456320228025298, 784757127688047, 713287322312886, 324749482094504, 65836345539856, 5493309225713, 143791364513, 0] := by
  rw [show A10K2.u7163 = KTree.node A10K2.u6907 (nat_lit 115602901) (nat_lit 3761164817) (nat_lit 0) A10K2.u7162 from rfl, totK_node, atot6907, atot7162]
  decide +kernel

theorem arows7675 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7675 = true := by
  rw [show A10K2.u7675 = KTree.node A10K2.u7419 (nat_lit 121355656) (nat_lit 12614037479) (nat_lit 0) A10K2.u7674 from rfl, allE_node, arows7419, irow7675, arows7674]
  all_goals rfl

theorem atot7675 : totK PA10K2 A10K2.u7675 = [0, 26399220495174, 200946923333137, 598229406968438, 862867686523176, 603525917802270, 186478457655823, 23600435680216, 1083952391029, 7903172220] := by
  rw [show A10K2.u7675 = KTree.node A10K2.u7419 (nat_lit 121355656) (nat_lit 12614037479) (nat_lit 0) A10K2.u7674 from rfl, totK_node, atot7419, atot7674]
  decide +kernel

theorem arows8186 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8186 = true := by
  rw [show A10K2.u8186 = KTree.node A10K2.u7930 (nat_lit 131825669) (nat_lit 6540494822) (nat_lit 0) A10K2.u8185 from rfl, allE_node, arows7930, irow8186, arows8185]
  all_goals rfl

theorem atot8186 : totK PA10K2 A10K2.u8186 = [0, 18212523618372, 149956149814928, 492880032511946, 813379843407327, 692636470347595, 288900630729236, 53931413559973, 4296926193465, 110028450843] := by
  rw [show A10K2.u8186 = KTree.node A10K2.u7930 (nat_lit 131825669) (nat_lit 6540494822) (nat_lit 0) A10K2.u8185 from rfl, totK_node, atot7930, atot8185]
  decide +kernel

theorem arows1022 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1022 = true := by
  rw [show A10K2.u1022 = KTree.node A10K2.u510 (nat_lit 9306724) (nat_lit 12563277710) (nat_lit 0) A10K2.u1021 from rfl, allE_node, arows510, irow1022, arows1021]
  all_goals rfl

theorem atot1022 : totK PA10K2 A10K2.u1022 = [51519947143230, 386832376408022, 1146712494431693, 1673990691379325, 1222287871016372, 411944195805339, 60446843984839, 3673922309612, 61379059878, 0] := by
  rw [show A10K2.u1022 = KTree.node A10K2.u510 (nat_lit 9306724) (nat_lit 12563277710) (nat_lit 0) A10K2.u1021 from rfl, totK_node, atot510, atot1021]
  decide +kernel

theorem arows2045 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2045 = true := by
  rw [show A10K2.u2045 = KTree.node A10K2.u1533 (nat_lit 25304161) (nat_lit 9910741694) (nat_lit 0) A10K2.u2044 from rfl, allE_node, arows1533, irow2045, arows2044]
  all_goals rfl

theorem atot2045 : totK PA10K2 A10K2.u2045 = [2808829852973, 74221714054996, 461693988357943, 1255636400441296, 1691909333313546, 1106440054416361, 324484876954109, 43656604235115, 2654740482066, 54141659059] := by
  rw [show A10K2.u2045 = KTree.node A10K2.u1533 (nat_lit 25304161) (nat_lit 9910741694) (nat_lit 0) A10K2.u2044 from rfl, totK_node, atot1533, atot2044]
  decide +kernel

theorem arows3069 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3069 = true := by
  rw [show A10K2.u3069 = KTree.node A10K2.u2557 (nat_lit 42993826) (nat_lit 11258600701) (nat_lit 0) A10K2.u3068 from rfl, allE_node, arows2557, irow3069, arows3068]
  all_goals rfl

theorem atot3069 : totK PA10K2 A10K2.u3069 = [48737909968141, 372563890908472, 1124490784229745, 1672609992223310, 1248096585838471, 431744146469268, 64133605439353, 3871508194130, 62632512355, 0] := by
  rw [show A10K2.u3069 = KTree.node A10K2.u2557 (nat_lit 42993826) (nat_lit 11258600701) (nat_lit 0) A10K2.u3068 from rfl, totK_node, atot2557, atot3068]
  decide +kernel

theorem arows4092 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4092 = true := by
  rw [show A10K2.u4092 = KTree.node A10K2.u3580 (nat_lit 58902253) (nat_lit 5412023238) (nat_lit 0) A10K2.u4091 from rfl, allE_node, arows3580, irow4092, arows4091]
  all_goals rfl

theorem atot4092 : totK PA10K2 A10K2.u4092 = [2338692983822, 70405575037589, 448609407394187, 1235622373649562, 1691757763820282, 1134015218034152, 340812969216221, 46053908902937, 2774953332499, 55395111536] := by
  rw [show A10K2.u4092 = KTree.node A10K2.u3580 (nat_lit 58902253) (nat_lit 5412023238) (nat_lit 0) A10K2.u4091 from rfl, totK_node, atot3580, atot4091]
  decide +kernel

theorem arows5117 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5117 = true := by
  rw [show A10K2.u5117 = KTree.node A10K2.u4605 (nat_lit 73002950) (nat_lit 15595033230) (nat_lit 0) A10K2.u5116 from rfl, allE_node, arows4605, irow5117, arows5116]
  all_goals rfl

theorem atot5117 : totK PA10K2 A10K2.u5117 = [48987805430682, 375557277716200, 1130183343674961, 1667408281329566, 1229550218986120, 424026056802248, 64833199625858, 4311126864616, 96827805339, 0] := by
  rw [show A10K2.u5117 = KTree.node A10K2.u4605 (nat_lit 73002950) (nat_lit 15595033230) (nat_lit 0) A10K2.u5116 from rfl, totK_node, atot4605, atot5116]
  decide +kernel

theorem arows6140 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6140 = true := by
  rw [show A10K2.u6140 = KTree.node A10K2.u5628 (nat_lit 92762501) (nat_lit 4702062112) (nat_lit 0) A10K2.u6139 from rfl, allE_node, arows5628, irow6140, arows6139]
  all_goals rfl

theorem atot6140 : totK PA10K2 A10K2.u6140 = [16757881899972, 173463993423571, 710423204132731, 1460420475017103, 1560526954862802, 808092063996199, 184495112265905, 19764539804390, 894242738383, 6354482628] := by
  rw [show A10K2.u6140 = KTree.node A10K2.u5628 (nat_lit 92762501) (nat_lit 4702062112) (nat_lit 0) A10K2.u6139 from rfl, totK_node, atot5628, atot6139]
  decide +kernel

theorem arows7164 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7164 = true := by
  rw [show A10K2.u7164 = KTree.node A10K2.u6652 (nat_lit 113302294) (nat_lit 13652359) (nat_lit 0) A10K2.u7163 from rfl, allE_node, arows6652, irow7164, arows7163]
  all_goals rfl

theorem atot7164 : totK PA10K2 A10K2.u7164 = [34990638127768, 285535492104513, 942360455900862, 1585631858232578, 1403756856981198, 610795711456503, 117194892477375, 9403724105878, 240619169852, 0] := by
  rw [show A10K2.u7164 = KTree.node A10K2.u6652 (nat_lit 113302294) (nat_lit 13652359) (nat_lit 0) A10K2.u7163 from rfl, totK_node, atot6652, atot7163]
  decide +kernel

theorem arows8187 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8187 = true := by
  rw [show A10K2.u8187 = KTree.node A10K2.u7675 (nat_lit 124604461) (nat_lit 5855428761) (nat_lit 0) A10K2.u8186 from rfl, allE_node, arows7675, irow8187, arows8186]
  all_goals rfl

theorem atot8187 : totK PA10K2 A10K2.u8187 = [0, 44611744113546, 350903073148065, 1091109439480384, 1676247529930503, 1296162388149865, 475384943813820, 77531849240189, 5380878584494, 117931623063] := by
  rw [show A10K2.u8187 = KTree.node A10K2.u7675 (nat_lit 124604461) (nat_lit 5855428761) (nat_lit 0) A10K2.u8186 from rfl, totK_node, atot7675, atot8186]
  decide +kernel

theorem arows2046 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2046 = true := by
  rw [show A10K2.u2046 = KTree.node A10K2.u1022 (nat_lit 15413183) (nat_lit 14263530493) (nat_lit 0) A10K2.u2045 from rfl, allE_node, arows1022, irow2046, arows2045]
  all_goals rfl

theorem atot2046 : totK PA10K2 A10K2.u2046 = [54328776996203, 461054090463018, 1608406482789636, 2929627091820621, 2914211467860411, 1518384250221700, 384931720938948, 47330526544727, 2716119541944, 54141659059] := by
  rw [show A10K2.u2046 = KTree.node A10K2.u1022 (nat_lit 15413183) (nat_lit 14263530493) (nat_lit 0) A10K2.u2045 from rfl, totK_node, atot1022, atot2045]
  decide +kernel

theorem arows4093 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4093 = true := by
  rw [show A10K2.u4093 = KTree.node A10K2.u3069 (nat_lit 49111044) (nat_lit 5233052295) (nat_lit 0) A10K2.u4092 from rfl, allE_node, arows3069, irow4093, arows4092]
  all_goals rfl

theorem atot4093 : totK PA10K2 A10K2.u4093 = [51076602951963, 442969465946061, 1573105424676227, 2908232365872872, 2939854349658753, 1565759364503420, 404946574655574, 49925417097067, 2837585844854, 55395111536] := by
  rw [show A10K2.u4093 = KTree.node A10K2.u3069 (nat_lit 49111044) (nat_lit 5233052295) (nat_lit 0) A10K2.u4092 from rfl, totK_node, atot3069, atot4092]
  decide +kernel

theorem arows6141 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6141 = true := by
  rw [show A10K2.u6141 = KTree.node A10K2.u5117 (nat_lit 78692626) (nat_lit 11172642695) (nat_lit 0) A10K2.u6140 from rfl, allE_node, arows5117, irow6141, arows6140]
  all_goals rfl

theorem atot6141 : totK PA10K2 A10K2.u6141 = [65745687330654, 549021271139771, 1840617720450387, 3127828756346669, 2790077173848922, 1232118120798447, 249328311891763, 24075666669006, 991070543722, 6354482628] := by
  rw [show A10K2.u6141 = KTree.node A10K2.u5117 (nat_lit 78692626) (nat_lit 11172642695) (nat_lit 0) A10K2.u6140 from rfl, totK_node, atot5117, atot6140]
  decide +kernel

theorem arows8188 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8188 = true := by
  rw [show A10K2.u8188 = KTree.node A10K2.u7164 (nat_lit 118493988) (nat_lit 13650589155) (nat_lit 0) A10K2.u8187 from rfl, allE_node, arows7164, irow8188, arows8187]
  all_goals rfl

theorem atot8188 : totK PA10K2 A10K2.u8188 = [34990638127768, 330147236218059, 1293263529048927, 2676754948302117, 3080004386911701, 1906958099606368, 592579836291195, 86935573346067, 5621497754346, 117931623063] := by
  rw [show A10K2.u8188 = KTree.node A10K2.u7164 (nat_lit 118493988) (nat_lit 13650589155) (nat_lit 0) A10K2.u8187 from rfl, totK_node, atot7164, atot8187]
  decide +kernel

theorem arows4094 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4094 = true := by
  rw [show A10K2.u4094 = KTree.node A10K2.u2046 (nat_lit 38410560) (nat_lit 14287852619) (nat_lit 0) A10K2.u4093 from rfl, allE_node, arows2046, irow4094, arows4093]
  all_goals rfl

theorem atot4094 : totK PA10K2 A10K2.u4094 = [105405379948166, 904023556409079, 3181526195318482, 5837859457693493, 5854065817519164, 3084143614725120, 789878295594522, 97255943641794, 5553705386798, 109536770595] := by
  rw [show A10K2.u4094 = KTree.node A10K2.u2046 (nat_lit 38410560) (nat_lit 14287852619) (nat_lit 0) A10K2.u4093 from rfl, totK_node, atot2046, atot4093]
  decide +kernel

theorem arows8189 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8189 = true := by
  rw [show A10K2.u8189 = KTree.node A10K2.u6141 (nat_lit 102992749) (nat_lit 5553214288) (nat_lit 0) A10K2.u8188 from rfl, allE_node, arows6141, irow8189, arows8188]
  all_goals rfl

theorem atot8189 : totK PA10K2 A10K2.u8189 = [100736325458422, 879168507357830, 3133881249499314, 5804583704648786, 5870081560760623, 3139076220404815, 841913701397246, 111011240015073, 6612568298068, 124286105691] := by
  rw [show A10K2.u8189 = KTree.node A10K2.u6141 (nat_lit 102992749) (nat_lit 5553214288) (nat_lit 0) A10K2.u8188 from rfl, totK_node, atot6141, atot8188]
  decide +kernel

theorem arows8190 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8190 = true := by
  rw [show A10K2.u8190 = KTree.node A10K2.u4094 (nat_lit 67163415) (nat_lit 2794592643) (nat_lit 0) A10K2.u8189 from rfl, allE_node, arows4094, irow8190, arows8189]
  all_goals rfl

theorem atot8190 : totK PA10K2 A10K2.u8190 = [206141705406588, 1783192063766909, 6315407444817796, 11642445956934922, 11724147378279787, 6223219835129935, 1631791996991768, 208267183656867, 12166273684866, 233822876286] := by
  rw [show A10K2.u8190 = KTree.node A10K2.u4094 (nat_lit 67163415) (nat_lit 2794592643) (nat_lit 0) A10K2.u8189 from rfl, totK_node, atot4094, atot8189]
  decide +kernel

end QECKChecks.A10K2
