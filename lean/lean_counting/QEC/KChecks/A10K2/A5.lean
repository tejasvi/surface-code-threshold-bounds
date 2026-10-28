import QEC.Count.ChunksK3
import QEC.KChecks.A10K2.A4

namespace QECKChecks.A10K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows5993 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5993 = true := by
  rw [show A10K2.u5993 = KTree.node A10K2.t6000 (nat_lit 101879239) (nat_lit 14239205805) (nat_lit 0) A10K2.t6001 from rfl, allE_node, rows6000, irow5993, rows6001]
  all_goals rfl

theorem atot5993 : totK PA10K2 A10K2.u5993 = [0, 986517189004, 3583732063917, 3916709907856, 1149125287685, 64899520130, 0, 0, 0, 0] := by
  rw [show A10K2.u5993 = KTree.node A10K2.t6000 (nat_lit 101879239) (nat_lit 14239205805) (nat_lit 0) A10K2.t6001 from rfl, totK_node, tot6000, tot6001]
  decide +kernel

theorem arows5994 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5994 = true := by
  rw [show A10K2.u5994 = KTree.node A10K2.t6002 (nat_lit 101893403) (nat_lit 10025055015) (nat_lit 0) A10K2.t6003 from rfl, allE_node, rows6002, irow5994, rows6003]
  all_goals rfl

theorem atot5994 : totK PA10K2 A10K2.u5994 = [0, 855483093671, 3523449749386, 3903701034037, 1029397450712, 62978220501, 0, 0, 0, 0] := by
  rw [show A10K2.u5994 = KTree.node A10K2.t6002 (nat_lit 101893403) (nat_lit 10025055015) (nat_lit 0) A10K2.t6003 from rfl, totK_node, tot6002, tot6003]
  decide +kernel

theorem arows5996 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5996 = true := by
  rw [show A10K2.u5996 = KTree.node A10K2.t6004 (nat_lit 101974030) (nat_lit 14244308590) (nat_lit 0) A10K2.t6005 from rfl, allE_node, rows6004, irow5996, rows6005]
  all_goals rfl

theorem atot5996 : totK PA10K2 A10K2.u5996 = [0, 581823473866, 2687904681883, 3956755988738, 1879574671322, 285103106428, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u5996 = KTree.node A10K2.t6004 (nat_lit 101974030) (nat_lit 14244308590) (nat_lit 0) A10K2.t6005 from rfl, totK_node, tot6004, tot6005]
  decide +kernel

theorem arows5997 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5997 = true := by
  rw [show A10K2.u5997 = KTree.node A10K2.t6006 (nat_lit 101978567) (nat_lit 13297152936) (nat_lit 0) A10K2.t6007 from rfl, allE_node, rows6006, irow5997, rows6007]
  all_goals rfl

theorem atot5997 : totK PA10K2 A10K2.u5997 = [0, 257580387599, 1865956910535, 4036371040078, 2785045311033, 550598947730, 30818366867, 0, 0, 0] := by
  rw [show A10K2.u5997 = KTree.node A10K2.t6006 (nat_lit 101978567) (nat_lit 13297152936) (nat_lit 0) A10K2.t6007 from rfl, totK_node, tot6006, tot6007]
  decide +kernel

theorem arows6000 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6000 = true := by
  rw [show A10K2.u6000 = KTree.node A10K2.t6008 (nat_lit 101992229) (nat_lit 7381318460) (nat_lit 0) A10K2.t6009 from rfl, allE_node, rows6008, irow6000, rows6009]
  all_goals rfl

theorem atot6000 : totK PA10K2 A10K2.u6000 = [0, 749928254756, 3095470111834, 3985030383328, 1555122664502, 129828199739, 0, 0, 0, 0] := by
  rw [show A10K2.u6000 = KTree.node A10K2.t6008 (nat_lit 101992229) (nat_lit 7381318460) (nat_lit 0) A10K2.t6009 from rfl, totK_node, tot6008, tot6009]
  decide +kernel

theorem arows6001 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6001 = true := by
  rw [show A10K2.u6001 = KTree.node A10K2.t6010 (nat_lit 101999136) (nat_lit 14251005070) (nat_lit 0) A10K2.t6011 from rfl, allE_node, rows6010, irow6001, rows6011]
  all_goals rfl

theorem atot6001 : totK PA10K2 A10K2.u6001 = [0, 593149538699, 2690622751185, 4059106697200, 2136142177454, 316470551116, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u6001 = KTree.node A10K2.t6010 (nat_lit 101999136) (nat_lit 14251005070) (nat_lit 0) A10K2.t6011 from rfl, totK_node, tot6010, tot6011]
  decide +kernel

theorem arows6003 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6003 = true := by
  rw [show A10K2.u6003 = KTree.node A10K2.t6012 (nat_lit 102105542) (nat_lit 14437709680) (nat_lit 0) A10K2.t6013 from rfl, allE_node, rows6012, irow6003, rows6013]
  all_goals rfl

theorem atot6003 : totK PA10K2 A10K2.u6003 = [0, 763787982313, 2946035071588, 3887990626834, 1905448303678, 281926861596, 6853348008, 0, 0, 0] := by
  rw [show A10K2.u6003 = KTree.node A10K2.t6012 (nat_lit 102105542) (nat_lit 14437709680) (nat_lit 0) A10K2.t6013 from rfl, totK_node, tot6012, tot6013]
  decide +kernel

theorem arows6004 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6004 = true := by
  rw [show A10K2.u6004 = KTree.node A10K2.t6014 (nat_lit 102111492) (nat_lit 13192877467) (nat_lit 0) A10K2.t6015 from rfl, allE_node, rows6014, irow6004, rows6015]
  all_goals rfl

theorem atot6004 : totK PA10K2 A10K2.u6004 = [0, 279438172082, 2004483435212, 4075690083290, 2633971023093, 481563738380, 30074883546, 0, 0, 0] := by
  rw [show A10K2.u6004 = KTree.node A10K2.t6014 (nat_lit 102111492) (nat_lit 13192877467) (nat_lit 0) A10K2.t6015 from rfl, totK_node, tot6014, tot6015]
  decide +kernel

theorem arows6011 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6011 = true := by
  rw [show A10K2.u6011 = KTree.node A10K2.t6016 (nat_lit 102119148) (nat_lit 10838540977) (nat_lit 0) A10K2.t6017 from rfl, allE_node, rows6016, irow6011, rows6017]
  all_goals rfl

theorem atot6011 : totK PA10K2 A10K2.u6011 = [0, 554732117554, 2442793850277, 3698954904492, 2276291339161, 465544993256, 31003444686, 0, 0, 0] := by
  rw [show A10K2.u6011 = KTree.node A10K2.t6016 (nat_lit 102119148) (nat_lit 10838540977) (nat_lit 0) A10K2.t6017 from rfl, totK_node, tot6016, tot6017]
  decide +kernel

theorem arows6012 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6012 = true := by
  rw [show A10K2.u6012 = KTree.node A10K2.t6018 (nat_lit 102123795) (nat_lit 10519385241) (nat_lit 0) A10K2.t6019 from rfl, allE_node, rows6018, irow6012, rows6019]
  all_goals rfl

theorem atot6012 : totK PA10K2 A10K2.u6012 = [0, 546985495730, 2787120070226, 4149572031907, 1690808815976, 143733365323, 0, 0, 0, 0] := by
  rw [show A10K2.u6012 = KTree.node A10K2.t6018 (nat_lit 102123795) (nat_lit 10519385241) (nat_lit 0) A10K2.t6019 from rfl, totK_node, tot6018, tot6019]
  decide +kernel

theorem arows6014 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6014 = true := by
  rw [show A10K2.u6014 = KTree.node A10K2.t6020 (nat_lit 102138753) (nat_lit 10346570470) (nat_lit 0) A10K2.t6021 from rfl, allE_node, rows6020, irow6014, rows6021]
  all_goals rfl

theorem atot6014 : totK PA10K2 A10K2.u6014 = [0, 0, 1201788522640, 3970024844638, 3438145801945, 743326308747, 37547833973, 0, 0, 0] := by
  rw [show A10K2.u6014 = KTree.node A10K2.t6020 (nat_lit 102138753) (nat_lit 10346570470) (nat_lit 0) A10K2.t6021 from rfl, totK_node, tot6020, tot6021]
  decide +kernel

theorem arows6015 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6015 = true := by
  rw [show A10K2.u6015 = KTree.node A10K2.t6022 (nat_lit 102154517) (nat_lit 7018165258) (nat_lit 0) A10K2.t6023 from rfl, allE_node, rows6022, irow6015, rows6023]
  all_goals rfl

theorem atot6015 : totK PA10K2 A10K2.u6015 = [0, 0, 911519547355, 3475567799158, 3700688747939, 1046668454157, 81800179711, 0, 0, 0] := by
  rw [show A10K2.u6015 = KTree.node A10K2.t6022 (nat_lit 102154517) (nat_lit 7018165258) (nat_lit 0) A10K2.t6023 from rfl, totK_node, tot6022, tot6023]
  decide +kernel

theorem arows6018 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6018 = true := by
  rw [show A10K2.u6018 = KTree.node A10K2.t6024 (nat_lit 102160428) (nat_lit 13155048199) (nat_lit 0) A10K2.t6025 from rfl, allE_node, rows6024, irow6018, rows6025]
  all_goals rfl

theorem atot6018 : totK PA10K2 A10K2.u6018 = [315335427872, 992225209073, 1098266338912, 1889882402352, 3074122200936, 1632546774851, 265614550179, 6354482628, 0, 0] := by
  rw [show A10K2.u6018 = KTree.node A10K2.t6024 (nat_lit 102160428) (nat_lit 13155048199) (nat_lit 0) A10K2.t6025 from rfl, totK_node, tot6024, tot6025]
  decide +kernel

theorem arows6019 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6019 = true := by
  rw [show A10K2.u6019 = KTree.node A10K2.t6026 (nat_lit 102239822) (nat_lit 10893499012) (nat_lit 0) A10K2.t6027 from rfl, allE_node, rows6026, irow6019, rows6027]
  all_goals rfl

theorem atot6019 : totK PA10K2 A10K2.u6019 = [520587805808, 2506728006650, 3938633316138, 2202321324721, 416622807403, 25371180993, 0, 0, 0, 0] := by
  rw [show A10K2.u6019 = KTree.node A10K2.t6026 (nat_lit 102239822) (nat_lit 10893499012) (nat_lit 0) A10K2.t6027 from rfl, totK_node, tot6026, tot6027]
  decide +kernel

theorem arows6021 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6021 = true := by
  rw [show A10K2.u6021 = KTree.node A10K2.t6028 (nat_lit 102253113) (nat_lit 7183406458) (nat_lit 0) A10K2.t6029 from rfl, allE_node, rows6028, irow6021, rows6029]
  all_goals rfl

theorem atot6021 : totK PA10K2 A10K2.u6021 = [520503246358, 2605698778325, 4031193589346, 2034422912191, 260829036015, 5460492893, 0, 0, 0, 0] := by
  rw [show A10K2.u6021 = KTree.node A10K2.t6028 (nat_lit 102253113) (nat_lit 7183406458) (nat_lit 0) A10K2.t6029 from rfl, totK_node, tot6028, tot6029]
  decide +kernel

theorem arows6022 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6022 = true := by
  rw [show A10K2.u6022 = KTree.node A10K2.t6030 (nat_lit 102261680) (nat_lit 14609840793) (nat_lit 0) A10K2.t6031 from rfl, allE_node, rows6030, irow6022, rows6031]
  all_goals rfl

theorem atot6022 : totK PA10K2 A10K2.u6022 = [820549055654, 3179406562646, 3993691266870, 1694387682122, 231227720597, 6354482628, 0, 0, 0, 0] := by
  rw [show A10K2.u6022 = KTree.node A10K2.t6030 (nat_lit 102261680) (nat_lit 14609840793) (nat_lit 0) A10K2.t6031 from rfl, totK_node, tot6030, tot6031]
  decide +kernel

theorem arows6026 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6026 = true := by
  rw [show A10K2.u6026 = KTree.node A10K2.t6032 (nat_lit 102266810) (nat_lit 14221181365) (nat_lit 0) A10K2.t6033 from rfl, allE_node, rows6032, irow6026, rows6033]
  all_goals rfl

theorem atot6026 : totK PA10K2 A10K2.u6026 = [0, 1164598736049, 3960127840636, 3909872006485, 1061169613139, 62979767238, 0, 0, 0, 0] := by
  rw [show A10K2.u6026 = KTree.node A10K2.t6032 (nat_lit 102266810) (nat_lit 14221181365) (nat_lit 0) A10K2.t6033 from rfl, totK_node, tot6032, tot6033]
  decide +kernel

theorem arows6027 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6027 = true := by
  rw [show A10K2.u6027 = KTree.node A10K2.t6034 (nat_lit 102272414) (nat_lit 15315505269) (nat_lit 0) A10K2.t6035 from rfl, allE_node, rows6034, irow6027, rows6035]
  all_goals rfl

theorem atot6027 : totK PA10K2 A10K2.u6027 = [0, 520344036742, 2631488598060, 3984563306865, 2001145106705, 390179496577, 25239774317, 0, 0, 0] := by
  rw [show A10K2.u6027 = KTree.node A10K2.t6034 (nat_lit 102272414) (nat_lit 15315505269) (nat_lit 0) A10K2.t6035 from rfl, totK_node, tot6034, tot6035]
  decide +kernel

theorem arows6029 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6029 = true := by
  rw [show A10K2.u6029 = KTree.node A10K2.t6036 (nat_lit 102285814) (nat_lit 16034136556) (nat_lit 0) A10K2.t6037 from rfl, allE_node, rows6036, irow6029, rows6037]
  all_goals rfl

theorem atot6029 : totK PA10K2 A10K2.u6029 = [0, 518259217515, 2609425113435, 3944687396068, 1912410244490, 249028806275, 5410721913, 0, 0, 0] := by
  rw [show A10K2.u6029 = KTree.node A10K2.t6036 (nat_lit 102285814) (nat_lit 16034136556) (nat_lit 0) A10K2.t6037 from rfl, totK_node, tot6036, tot6037]
  decide +kernel

theorem arows6030 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6030 = true := by
  rw [show A10K2.u6030 = KTree.node A10K2.t6038 (nat_lit 102294406) (nat_lit 15721197482) (nat_lit 0) A10K2.t6039 from rfl, allE_node, rows6038, irow6030, rows6039]
  all_goals rfl

theorem atot6030 : totK PA10K2 A10K2.u6030 = [0, 820171017843, 3195927736227, 4033636861874, 1665428323236, 199996905793, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u6030 = KTree.node A10K2.t6038 (nat_lit 102294406) (nat_lit 15721197482) (nat_lit 0) A10K2.t6039 from rfl, totK_node, tot6038, tot6039]
  decide +kernel

theorem arows6033 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6033 = true := by
  rw [show A10K2.u6033 = KTree.node A10K2.t6040 (nat_lit 102312734) (nat_lit 8143790074) (nat_lit 0) A10K2.t6041 from rfl, allE_node, rows6040, irow6033, rows6041]
  all_goals rfl

theorem atot6033 : totK PA10K2 A10K2.u6033 = [779827310996, 3166133674824, 3986737628383, 1760227497724, 339342648100, 37674914273, 0, 0, 0, 0] := by
  rw [show A10K2.u6033 = KTree.node A10K2.t6040 (nat_lit 102312734) (nat_lit 8143790074) (nat_lit 0) A10K2.t6041 from rfl, totK_node, tot6040, tot6041]
  decide +kernel

theorem arows6034 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6034 = true := by
  rw [show A10K2.u6034 = KTree.node A10K2.t6042 (nat_lit 102326336) (nat_lit 15440360366) (nat_lit 0) A10K2.t6043 from rfl, allE_node, rows6042, irow6034, rows6043]
  all_goals rfl

theorem atot6034 : totK PA10K2 A10K2.u6034 = [599593230297, 2545602335322, 3911196573451, 2480984982345, 561909040032, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u6034 = KTree.node A10K2.t6042 (nat_lit 102326336) (nat_lit 15440360366) (nat_lit 0) A10K2.t6043 from rfl, totK_node, tot6042, tot6043]
  decide +kernel

theorem arows6036 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6036 = true := by
  rw [show A10K2.u6036 = KTree.node A10K2.t6044 (nat_lit 102331327) (nat_lit 14164603415) (nat_lit 0) A10K2.t6045 from rfl, allE_node, rows6044, irow6036, rows6045]
  all_goals rfl

theorem atot6036 : totK PA10K2 A10K2.u6036 = [227315038789, 1784061458742, 4195284360267, 3388720676420, 717223344825, 19701566325, 0, 0, 0, 0] := by
  rw [show A10K2.u6036 = KTree.node A10K2.t6044 (nat_lit 102331327) (nat_lit 14164603415) (nat_lit 0) A10K2.t6045 from rfl, totK_node, tot6044, tot6045]
  decide +kernel

theorem arows6037 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6037 = true := by
  rw [show A10K2.u6037 = KTree.node A10K2.t6046 (nat_lit 102345066) (nat_lit 9865715108) (nat_lit 0) A10K2.t6047 from rfl, allE_node, rows6046, irow6037, rows6047]
  all_goals rfl

theorem atot6037 : totK PA10K2 A10K2.u6037 = [0, 778738872532, 3228542855349, 4165108385624, 1628026792360, 137554885883, 0, 0, 0, 0] := by
  rw [show A10K2.u6037 = KTree.node A10K2.t6046 (nat_lit 102345066) (nat_lit 9865715108) (nat_lit 0) A10K2.t6047 from rfl, totK_node, tot6046, tot6047]
  decide +kernel

theorem arows6042 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6042 = true := by
  rw [show A10K2.u6042 = KTree.node A10K2.t6048 (nat_lit 102359098) (nat_lit 10355711509) (nat_lit 0) A10K2.t6049 from rfl, allE_node, rows6048, irow6042, rows6049]
  all_goals rfl

theorem atot6042 : totK PA10K2 A10K2.u6042 = [0, 599304943312, 2601473912075, 3917904528625, 2351323366718, 515989172355, 31082886609, 0, 0, 0] := by
  rw [show A10K2.u6042 = KTree.node A10K2.t6048 (nat_lit 102359098) (nat_lit 10355711509) (nat_lit 0) A10K2.t6049 from rfl, totK_node, tot6048, tot6049]
  decide +kernel

theorem arows6043 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6043 = true := by
  rw [show A10K2.u6043 = KTree.node A10K2.t6050 (nat_lit 102433342) (nat_lit 15251274003) (nat_lit 0) A10K2.t6051 from rfl, allE_node, rows6050, irow6043, rows6051]
  all_goals rfl

theorem atot6043 : totK PA10K2 A10K2.u6043 = [777824669607, 2912609251695, 3620512782777, 2010996057274, 591304021716, 50555834002, 0, 0, 0, 0] := by
  rw [show A10K2.u6043 = KTree.node A10K2.t6050 (nat_lit 102433342) (nat_lit 15251274003) (nat_lit 0) A10K2.t6051 from rfl, totK_node, tot6050, tot6051]
  decide +kernel

theorem arows6045 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6045 = true := by
  rw [show A10K2.u6045 = KTree.node A10K2.t6052 (nat_lit 102439430) (nat_lit 13049409175) (nat_lit 0) A10K2.t6053 from rfl, allE_node, rows6052, irow6045, rows6053]
  all_goals rfl

theorem atot6045 : totK PA10K2 A10K2.u6045 = [284288764057, 1940141733043, 4065806160588, 2860334720123, 591456411224, 30749153377, 0, 0, 0, 0] := by
  rw [show A10K2.u6045 = KTree.node A10K2.t6052 (nat_lit 102439430) (nat_lit 13049409175) (nat_lit 0) A10K2.t6053 from rfl, totK_node, tot6052, tot6053]
  decide +kernel

theorem arows6046 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6046 = true := by
  rw [show A10K2.u6046 = KTree.node A10K2.t6054 (nat_lit 102446378) (nat_lit 12578474049) (nat_lit 0) A10K2.t6055 from rfl, allE_node, rows6054, irow6046, rows6055]
  all_goals rfl

theorem atot6046 : totK PA10K2 A10K2.u6046 = [510827461894, 2461466546180, 4123443121515, 2588374559475, 481833327146, 24865484814, 0, 0, 0, 0] := by
  rw [show A10K2.u6046 = KTree.node A10K2.t6054 (nat_lit 102446378) (nat_lit 12578474049) (nat_lit 0) A10K2.t6055 from rfl, totK_node, tot6054, tot6055]
  decide +kernel

theorem arows6049 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6049 = true := by
  rw [show A10K2.u6049 = KTree.node A10K2.t6056 (nat_lit 102460428) (nat_lit 9053678332) (nat_lit 0) A10K2.t6057 from rfl, allE_node, rows6056, irow6049, rows6057]
  all_goals rfl

theorem atot6049 : totK PA10K2 A10K2.u6049 = [773825466003, 3254825520303, 4249731924340, 1657269309263, 131895413957, 0, 0, 0, 0, 0] := by
  rw [show A10K2.u6049 = KTree.node A10K2.t6056 (nat_lit 102460428) (nat_lit 9053678332) (nat_lit 0) A10K2.t6057 from rfl, totK_node, tot6056, tot6057]
  decide +kernel

theorem arows6050 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6050 = true := by
  rw [show A10K2.u6050 = KTree.node A10K2.t6058 (nat_lit 102464958) (nat_lit 16495835463) (nat_lit 0) A10K2.t6059 from rfl, allE_node, rows6058, irow6050, rows6059]
  all_goals rfl

theorem atot6050 : totK PA10K2 A10K2.u6050 = [0, 898944329696, 3537801482671, 4103522032924, 1304537506983, 88459438038, 0, 0, 0, 0] := by
  rw [show A10K2.u6050 = KTree.node A10K2.t6058 (nat_lit 102464958) (nat_lit 16495835463) (nat_lit 0) A10K2.t6059 from rfl, totK_node, tot6058, tot6059]
  decide +kernel

theorem arows6052 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6052 = true := by
  rw [show A10K2.u6052 = KTree.node A10K2.t6060 (nat_lit 102469623) (nat_lit 14886076046) (nat_lit 0) A10K2.t6061 from rfl, allE_node, rows6060, irow6052, rows6061]
  all_goals rfl

theorem atot6052 : totK PA10K2 A10K2.u6052 = [0, 476236816663, 2546053938637, 4239396604223, 2236576579493, 302926686394, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u6052 = KTree.node A10K2.t6060 (nat_lit 102469623) (nat_lit 14886076046) (nat_lit 0) A10K2.t6061 from rfl, totK_node, tot6060, tot6061]
  decide +kernel

theorem arows6053 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6053 = true := by
  rw [show A10K2.u6053 = KTree.node A10K2.t6062 (nat_lit 102477192) (nat_lit 13136731398) (nat_lit 0) A10K2.t6063 from rfl, allE_node, rows6062, irow6053, rows6063]
  all_goals rfl

theorem atot6053 : totK PA10K2 A10K2.u6053 = [0, 684919494344, 2867469805447, 4046729978375, 2158356511639, 333219957663, 7047025452, 0, 0, 0] := by
  rw [show A10K2.u6053 = KTree.node A10K2.t6062 (nat_lit 102477192) (nat_lit 13136731398) (nat_lit 0) A10K2.t6063 from rfl, totK_node, tot6062, tot6063]
  decide +kernel

theorem arows6057 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6057 = true := by
  rw [show A10K2.u6057 = KTree.node A10K2.t6064 (nat_lit 102491364) (nat_lit 8312633097) (nat_lit 0) A10K2.t6065 from rfl, allE_node, rows6064, irow6057, rows6065]
  all_goals rfl

theorem atot6057 : totK PA10K2 A10K2.u6057 = [0, 881770168529, 3437537515581, 4126012612885, 1475029595259, 93484106076, 0, 0, 0, 0] := by
  rw [show A10K2.u6057 = KTree.node A10K2.t6064 (nat_lit 102491364) (nat_lit 8312633097) (nat_lit 0) A10K2.t6065 from rfl, totK_node, tot6064, tot6065]
  decide +kernel

theorem arows6058 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6058 = true := by
  rw [show A10K2.u6058 = KTree.node A10K2.t6066 (nat_lit 102495956) (nat_lit 9288955319) (nat_lit 0) A10K2.t6067 from rfl, allE_node, rows6066, irow6058, rows6067]
  all_goals rfl

theorem atot6058 : totK PA10K2 A10K2.u6058 = [0, 207216491586, 1463078890610, 3669769547864, 3534992169016, 955911222058, 61110126106, 0, 0, 0] := by
  rw [show A10K2.u6058 = KTree.node A10K2.t6066 (nat_lit 102495956) (nat_lit 9288955319) (nat_lit 0) A10K2.t6067 from rfl, totK_node, tot6066, tot6067]
  decide +kernel

theorem arows6060 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6060 = true := by
  rw [show A10K2.u6060 = KTree.node A10K2.t6068 (nat_lit 102501485) (nat_lit 5292794791) (nat_lit 0) A10K2.t6069 from rfl, allE_node, rows6068, irow6060, rows6069]
  all_goals rfl

theorem atot6060 : totK PA10K2 A10K2.u6060 = [0, 628706742094, 2883673495515, 4044022046298, 1825683077621, 291989106854, 20070762815, 0, 0, 0] := by
  rw [show A10K2.u6060 = KTree.node A10K2.t6068 (nat_lit 102501485) (nat_lit 5292794791) (nat_lit 0) A10K2.t6069 from rfl, totK_node, tot6068, tot6069]
  decide +kernel

theorem arows6061 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6061 = true := by
  rw [show A10K2.u6061 = KTree.node A10K2.t6070 (nat_lit 102514760) (nat_lit 13794873941) (nat_lit 0) A10K2.t6071 from rfl, allE_node, rows6070, irow6061, rows6071]
  all_goals rfl

theorem atot6061 : totK PA10K2 A10K2.u6061 = [0, 520503246358, 2472584830139, 3819611178375, 2161926195937, 373341521243, 10709677363, 0, 0, 0] := by
  rw [show A10K2.u6061 = KTree.node A10K2.t6070 (nat_lit 102514760) (nat_lit 13794873941) (nat_lit 0) A10K2.t6071 from rfl, totK_node, tot6070, tot6071]
  decide +kernel

theorem arows6064 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6064 = true := by
  rw [show A10K2.u6064 = KTree.node A10K2.t6072 (nat_lit 102523333) (nat_lit 4843328892) (nat_lit 0) A10K2.t6073 from rfl, allE_node, rows6072, irow6064, rows6073]
  all_goals rfl

theorem atot6064 : totK PA10K2 A10K2.u6064 = [0, 820549055654, 3072918281208, 3918435168444, 1757208188721, 224515853675, 5705019915, 0, 0, 0] := by
  rw [show A10K2.u6064 = KTree.node A10K2.t6072 (nat_lit 102523333) (nat_lit 4843328892) (nat_lit 0) A10K2.t6073 from rfl, totK_node, tot6072, tot6073]
  decide +kernel

theorem arows6065 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6065 = true := by
  rw [show A10K2.u6065 = KTree.node A10K2.t6074 (nat_lit 102528226) (nat_lit 13474402621) (nat_lit 0) A10K2.t6075 from rfl, allE_node, rows6074, irow6065, rows6075]
  all_goals rfl

theorem atot6065 : totK PA10K2 A10K2.u6065 = [0, 0, 1259852742454, 4041938065795, 3827814275257, 1027079824382, 62351816811, 0, 0, 0] := by
  rw [show A10K2.u6065 = KTree.node A10K2.t6074 (nat_lit 102528226) (nat_lit 13474402621) (nat_lit 0) A10K2.t6075 from rfl, totK_node, tot6074, tot6075]
  decide +kernel

theorem arows6067 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6067 = true := by
  rw [show A10K2.u6067 = KTree.node A10K2.t6076 (nat_lit 102533921) (nat_lit 9477304812) (nat_lit 0) A10K2.t6077 from rfl, allE_node, rows6076, irow6067, rows6077]
  all_goals rfl

theorem atot6067 : totK PA10K2 A10K2.u6067 = [0, 0, 769155724557, 3256769502489, 4034535085991, 1426875544178, 118405628505, 0, 0, 0] := by
  rw [show A10K2.u6067 = KTree.node A10K2.t6076 (nat_lit 102533921) (nat_lit 9477304812) (nat_lit 0) A10K2.t6077 from rfl, totK_node, tot6076, tot6077]
  decide +kernel

theorem arows6068 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6068 = true := by
  rw [show A10K2.u6068 = KTree.node A10K2.t6078 (nat_lit 102547955) (nat_lit 5563514136) (nat_lit 0) A10K2.t6079 from rfl, allE_node, rows6078, irow6068, rows6079]
  all_goals rfl

theorem atot6068 : totK PA10K2 A10K2.u6068 = [0, 0, 809836101623, 3186875362115, 3713846810242, 1469719521559, 221429557333, 7007974415, 0, 0] := by
  rw [show A10K2.u6068 = KTree.node A10K2.t6078 (nat_lit 102547955) (nat_lit 5563514136) (nat_lit 0) A10K2.t6079 from rfl, totK_node, tot6078, tot6079]
  decide +kernel

theorem arows6074 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6074 = true := by
  rw [show A10K2.u6074 = KTree.node A10K2.t6080 (nat_lit 102559296) (nat_lit 15134377526) (nat_lit 0) A10K2.t6081 from rfl, allE_node, rows6080, irow6074, rows6081]
  all_goals rfl

theorem atot6074 : totK PA10K2 A10K2.u6074 = [0, 408659135851, 1904464990763, 3564767104139, 3187931394567, 989063089420, 68789595223, 0, 0, 0] := by
  rw [show A10K2.u6074 = KTree.node A10K2.t6080 (nat_lit 102559296) (nat_lit 15134377526) (nat_lit 0) A10K2.t6081 from rfl, totK_node, tot6080, tot6081]
  decide +kernel

theorem arows6075 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6075 = true := by
  rw [show A10K2.u6075 = KTree.node A10K2.t6082 (nat_lit 102577435) (nat_lit 10054382329) (nat_lit 0) A10K2.t6083 from rfl, allE_node, rows6082, irow6075, rows6083]
  all_goals rfl

theorem atot6075 : totK PA10K2 A10K2.u6075 = [0, 370669945331, 2214202881380, 4115227663826, 2723699991093, 565550185924, 31306924438, 0, 0, 0] := by
  rw [show A10K2.u6075 = KTree.node A10K2.t6082 (nat_lit 102577435) (nat_lit 10054382329) (nat_lit 0) A10K2.t6083 from rfl, totK_node, tot6082, tot6083]
  decide +kernel

theorem arows6077 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6077 = true := by
  rw [show A10K2.u6077 = KTree.node A10K2.t6084 (nat_lit 102590309) (nat_lit 5545447603) (nat_lit 0) A10K2.t6085 from rfl, allE_node, rows6084, irow6077, rows6085]
  all_goals rfl

theorem atot6077 : totK PA10K2 A10K2.u6077 = [0, 825408880158, 3300122853092, 4253374161131, 1804956228446, 178000352497, 0, 0, 0, 0] := by
  rw [show A10K2.u6077 = KTree.node A10K2.t6084 (nat_lit 102590309) (nat_lit 5545447603) (nat_lit 0) A10K2.t6085 from rfl, totK_node, tot6084, tot6085]
  decide +kernel

theorem arows6078 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6078 = true := by
  rw [show A10K2.u6078 = KTree.node A10K2.t6086 (nat_lit 102596088) (nat_lit 13048071877) (nat_lit 0) A10K2.t6087 from rfl, allE_node, rows6086, irow6078, rows6087]
  all_goals rfl

theorem atot6078 : totK PA10K2 A10K2.u6078 = [0, 0, 983892609077, 3599934509743, 4071945015218, 1293886119062, 88420430393, 0, 0, 0] := by
  rw [show A10K2.u6078 = KTree.node A10K2.t6086 (nat_lit 102596088) (nat_lit 13048071877) (nat_lit 0) A10K2.t6087 from rfl, totK_node, tot6086, tot6087]
  decide +kernel

theorem arows6081 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6081 = true := by
  rw [show A10K2.u6081 = KTree.node A10K2.t6088 (nat_lit 102610142) (nat_lit 11294439000) (nat_lit 0) A10K2.t6089 from rfl, allE_node, rows6088, irow6081, rows6089]
  all_goals rfl

theorem atot6081 : totK PA10K2 A10K2.u6081 = [0, 0, 527203678837, 2678154790032, 4230759055918, 2184246373143, 309613191663, 7151180950, 0, 0] := by
  rw [show A10K2.u6081 = KTree.node A10K2.t6088 (nat_lit 102610142) (nat_lit 11294439000) (nat_lit 0) A10K2.t6089 from rfl, totK_node, tot6088, tot6089]
  decide +kernel

theorem arows6082 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6082 = true := by
  rw [show A10K2.u6082 = KTree.node A10K2.t6090 (nat_lit 102624468) (nat_lit 9668568983) (nat_lit 0) A10K2.t6091 from rfl, allE_node, rows6090, irow6082, rows6091]
  all_goals rfl

theorem atot6082 : totK PA10K2 A10K2.u6082 = [0, 300827602965, 1646887520320, 3577052776221, 3444083523093, 1085211162023, 68947799775, 0, 0, 0] := by
  rw [show A10K2.u6082 = KTree.node A10K2.t6090 (nat_lit 102624468) (nat_lit 9668568983) (nat_lit 0) A10K2.t6091 from rfl, totK_node, tot6090, tot6091]
  decide +kernel

theorem arows6084 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6084 = true := by
  rw [show A10K2.u6084 = KTree.node A10K2.t6092 (nat_lit 102698929) (nat_lit 9000570098) (nat_lit 0) A10K2.t6093 from rfl, allE_node, rows6092, irow6084, rows6093]
  all_goals rfl

theorem atot6084 : totK PA10K2 A10K2.u6084 = [0, 476997066642, 2426012785108, 4024077580952, 2370241668500, 412415195554, 11991740650, 0, 0, 0] := by
  rw [show A10K2.u6084 = KTree.node A10K2.t6092 (nat_lit 102698929) (nat_lit 9000570098) (nat_lit 0) A10K2.t6093 from rfl, totK_node, tot6092, tot6093]
  decide +kernel

theorem arows6085 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6085 = true := by
  rw [show A10K2.u6085 = KTree.node A10K2.t6094 (nat_lit 102705837) (nat_lit 5010808043) (nat_lit 0) A10K2.t6095 from rfl, allE_node, rows6094, irow6085, rows6095]
  all_goals rfl

theorem atot6085 : totK PA10K2 A10K2.u6085 = [0, 685382209408, 3051381536166, 4327760680909, 1960269118132, 190074375765, 0, 0, 0, 0] := by
  rw [show A10K2.u6085 = KTree.node A10K2.t6094 (nat_lit 102705837) (nat_lit 5010808043) (nat_lit 0) A10K2.t6095 from rfl, totK_node, tot6094, tot6095]
  decide +kernel

theorem arows6089 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6089 = true := by
  rw [show A10K2.u6089 = KTree.node A10K2.t6096 (nat_lit 102719985) (nat_lit 8736671163) (nat_lit 0) A10K2.t6097 from rfl, allE_node, rows6096, irow6089, rows6097]
  all_goals rfl

theorem atot6089 : totK PA10K2 A10K2.u6089 = [0, 759112644349, 2920748868458, 3858617359879, 2087610676904, 382572247249, 12219140272, 0, 0, 0] := by
  rw [show A10K2.u6089 = KTree.node A10K2.t6096 (nat_lit 102719985) (nat_lit 8736671163) (nat_lit 0) A10K2.t6097 from rfl, totK_node, tot6096, tot6097]
  decide +kernel

theorem arows6090 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6090 = true := by
  rw [show A10K2.u6090 = KTree.node A10K2.t6098 (nat_lit 102724502) (nat_lit 15693259330) (nat_lit 0) A10K2.t6099 from rfl, allE_node, rows6098, irow6090, rows6099]
  all_goals rfl

theorem atot6090 : totK PA10K2 A10K2.u6090 = [0, 122956571035, 1600600262003, 4222828440724, 3441210989288, 676659932267, 19546091569, 0, 0, 0] := by
  rw [show A10K2.u6090 = KTree.node A10K2.t6098 (nat_lit 102724502) (nat_lit 15693259330) (nat_lit 0) A10K2.t6099 from rfl, totK_node, tot6098, tot6099]
  decide +kernel

theorem arows6092 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6092 = true := by
  rw [show A10K2.u6092 = KTree.node A10K2.t6100 (nat_lit 102730277) (nat_lit 6660389760) (nat_lit 0) A10K2.t6101 from rfl, allE_node, rows6100, irow6092, rows6101]
  all_goals rfl

theorem atot6092 : totK PA10K2 A10K2.u6092 = [0, 0, 774781949825, 3218370018365, 4168769316330, 1559647894784, 117740555116, 0, 0, 0] := by
  rw [show A10K2.u6092 = KTree.node A10K2.t6100 (nat_lit 102730277) (nat_lit 6660389760) (nat_lit 0) A10K2.t6101 from rfl, totK_node, tot6100, tot6101]
  decide +kernel

theorem arows6093 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6093 = true := by
  rw [show A10K2.u6093 = KTree.node A10K2.t6102 (nat_lit 102737399) (nat_lit 14746790914) (nat_lit 0) A10K2.t6103 from rfl, allE_node, rows6102, irow6093, rows6103]
  all_goals rfl

theorem atot6093 : totK PA10K2 A10K2.u6093 = [0, 0, 683624752506, 2985314966219, 4172979168436, 1913254171042, 235183996770, 6318667960, 0, 0] := by
  rw [show A10K2.u6093 = KTree.node A10K2.t6102 (nat_lit 102737399) (nat_lit 14746790914) (nat_lit 0) A10K2.t6103 from rfl, totK_node, tot6102, tot6103]
  decide +kernel

theorem arows6096 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6096 = true := by
  rw [show A10K2.u6096 = KTree.node A10K2.t6104 (nat_lit 102752306) (nat_lit 10491640441) (nat_lit 0) A10K2.t6105 from rfl, allE_node, rows6104, irow6096, rows6105]
  all_goals rfl

theorem atot6096 : totK PA10K2 A10K2.u6096 = [0, 0, 549025876021, 2672382009906, 4130500181500, 2210329054129, 286492903526, 6439430839, 0, 0] := by
  rw [show A10K2.u6096 = KTree.node A10K2.t6104 (nat_lit 102752306) (nat_lit 10491640441) (nat_lit 0) A10K2.t6105 from rfl, totK_node, tot6104, tot6105]
  decide +kernel

theorem arows6097 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6097 = true := by
  rw [show A10K2.u6097 = KTree.node A10K2.t6106 (nat_lit 102756826) (nat_lit 12597233880) (nat_lit 0) A10K2.t6107 from rfl, allE_node, rows6106, irow6097, rows6107]
  all_goals rfl

theorem atot6097 : totK PA10K2 A10K2.u6097 = [0, 0, 328159929781, 2084733891773, 4179491825079, 2773352270173, 459971349271, 12132367858, 0, 0] := by
  rw [show A10K2.u6097 = KTree.node A10K2.t6106 (nat_lit 102756826) (nat_lit 12597233880) (nat_lit 0) A10K2.t6107 from rfl, totK_node, tot6106, tot6107]
  decide +kernel

theorem arows6099 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6099 = true := by
  rw [show A10K2.u6099 = KTree.node A10K2.t6108 (nat_lit 102761371) (nat_lit 4364037610) (nat_lit 0) A10K2.t6109 from rfl, allE_node, rows6108, irow6099, rows6109]
  all_goals rfl

theorem atot6099 : totK PA10K2 A10K2.u6099 = [0, 869900121985, 3064025814862, 3080327633172, 1193163123883, 1015477488861, 501217979401, 48886019071, 0, 0] := by
  rw [show A10K2.u6099 = KTree.node A10K2.t6108 (nat_lit 102761371) (nat_lit 4364037610) (nat_lit 0) A10K2.t6109 from rfl, totK_node, tot6108, tot6109]
  decide +kernel

theorem arows6100 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6100 = true := by
  rw [show A10K2.u6100 = KTree.node A10K2.t6110 (nat_lit 102766869) (nat_lit 6936576876) (nat_lit 0) A10K2.t6111 from rfl, allE_node, rows6110, irow6100, rows6111]
  all_goals rfl

theorem atot6100 : totK PA10K2 A10K2.u6100 = [0, 293873915135, 1869840859135, 3941598448485, 2905031220789, 591186213547, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u6100 = KTree.node A10K2.t6110 (nat_lit 102766869) (nat_lit 6936576876) (nat_lit 0) A10K2.t6111 from rfl, totK_node, tot6110, tot6111]
  decide +kernel

theorem arows6105 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6105 = true := by
  rw [show A10K2.u6105 = KTree.node A10K2.t6112 (nat_lit 102779733) (nat_lit 6825870322) (nat_lit 0) A10K2.t6113 from rfl, allE_node, rows6112, irow6105, rows6113]
  all_goals rfl

theorem atot6105 : totK PA10K2 A10K2.u6105 = [0, 388194435581, 2268170053187, 3947513941238, 2069604767805, 208984933575, 0, 0, 0, 0] := by
  rw [show A10K2.u6105 = KTree.node A10K2.t6112 (nat_lit 102779733) (nat_lit 6825870322) (nat_lit 0) A10K2.t6113 from rfl, totK_node, tot6112, tot6113]
  decide +kernel

theorem arows6106 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6106 = true := by
  rw [show A10K2.u6106 = KTree.node A10K2.t6114 (nat_lit 102788165) (nat_lit 5270838583) (nat_lit 0) A10K2.t6115 from rfl, allE_node, rows6114, irow6106, rows6115]
  all_goals rfl

theorem atot6106 : totK PA10K2 A10K2.u6106 = [0, 787080240479, 3194777977822, 4161189706182, 1760821000929, 212106480715, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u6106 = KTree.node A10K2.t6114 (nat_lit 102788165) (nat_lit 5270838583) (nat_lit 0) A10K2.t6115 from rfl, totK_node, tot6114, tot6115]
  decide +kernel

theorem arows6108 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6108 = true := by
  rw [show A10K2.u6108 = KTree.node A10K2.t6116 (nat_lit 102792950) (nat_lit 16166237244) (nat_lit 0) A10K2.t6117 from rfl, allE_node, rows6116, irow6108, rows6117]
  all_goals rfl

theorem atot6108 : totK PA10K2 A10K2.u6108 = [0, 0, 1023137681494, 3636090390632, 3975156382196, 1198796468520, 73065519735, 0, 0, 0] := by
  rw [show A10K2.u6108 = KTree.node A10K2.t6116 (nat_lit 102792950) (nat_lit 16166237244) (nat_lit 0) A10K2.t6117 from rfl, totK_node, tot6116, tot6117]
  decide +kernel

theorem arows6109 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6109 = true := by
  rw [show A10K2.u6109 = KTree.node A10K2.t6118 (nat_lit 102797580) (nat_lit 11762192483) (nat_lit 0) A10K2.t6119 from rfl, allE_node, rows6118, irow6109, rows6119]
  all_goals rfl

theorem atot6109 : totK PA10K2 A10K2.u6109 = [0, 0, 327954541848, 2156288667667, 3928099736396, 2444379414335, 523065398562, 30650496230, 0, 0] := by
  rw [show A10K2.u6109 = KTree.node A10K2.t6118 (nat_lit 102797580) (nat_lit 11762192483) (nat_lit 0) A10K2.t6119 from rfl, totK_node, tot6118, tot6119]
  decide +kernel

theorem arows6112 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6112 = true := by
  rw [show A10K2.u6112 = KTree.node A10K2.t6120 (nat_lit 102811421) (nat_lit 6053734991) (nat_lit 0) A10K2.t6121 from rfl, allE_node, rows6120, irow6112, rows6121]
  all_goals rfl

theorem atot6112 : totK PA10K2 A10K2.u6112 = [0, 0, 679230525234, 3044907293279, 4010693502633, 1391207166595, 103168391898, 0, 0, 0] := by
  rw [show A10K2.u6112 = KTree.node A10K2.t6120 (nat_lit 102811421) (nat_lit 6053734991) (nat_lit 0) A10K2.t6121 from rfl, totK_node, tot6120, tot6121]
  decide +kernel

theorem arows6113 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6113 = true := by
  rw [show A10K2.u6113 = KTree.node A10K2.t6122 (nat_lit 102818568) (nat_lit 13953022228) (nat_lit 0) A10K2.t6123 from rfl, allE_node, rows6122, irow6113, rows6123]
  all_goals rfl

theorem atot6113 : totK PA10K2 A10K2.u6113 = [0, 0, 784550567112, 3146186206300, 3970820079499, 1586779881805, 186315517825, 5546304973, 0, 0] := by
  rw [show A10K2.u6113 = KTree.node A10K2.t6122 (nat_lit 102818568) (nat_lit 13953022228) (nat_lit 0) A10K2.t6123 from rfl, totK_node, tot6122, tot6123]
  decide +kernel

theorem arows6115 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6115 = true := by
  rw [show A10K2.u6115 = KTree.node A10K2.t6124 (nat_lit 102894084) (nat_lit 12621675841) (nat_lit 0) A10K2.t6125 from rfl, allE_node, rows6124, irow6115, rows6125]
  all_goals rfl

theorem atot6115 : totK PA10K2 A10K2.u6115 = [0, 795409072615, 3209964629663, 3967843244527, 1547655537053, 287997049630, 34954726192, 0, 0, 0] := by
  rw [show A10K2.u6115 = KTree.node A10K2.t6124 (nat_lit 102894084) (nat_lit 12621675841) (nat_lit 0) A10K2.t6125 from rfl, totK_node, tot6124, tot6125]
  decide +kernel

theorem arows6116 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6116 = true := by
  rw [show A10K2.u6116 = KTree.node A10K2.t6126 (nat_lit 102899191) (nat_lit 14916966994) (nat_lit 0) A10K2.t6127 from rfl, allE_node, rows6126, irow6116, rows6127]
  all_goals rfl

theorem atot6116 : totK PA10K2 A10K2.u6116 = [0, 293307099335, 1702658324441, 3661234295889, 2964505257080, 682746347327, 36865889447, 0, 0, 0] := by
  rw [show A10K2.u6116 = KTree.node A10K2.t6126 (nat_lit 102899191) (nat_lit 14916966994) (nat_lit 0) A10K2.t6127 from rfl, totK_node, tot6126, tot6127]
  decide +kernel

theorem arows6120 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6120 = true := by
  rw [show A10K2.u6120 = KTree.node A10K2.t6128 (nat_lit 102910023) (nat_lit 9456126756) (nat_lit 0) A10K2.t6129 from rfl, allE_node, rows6128, irow6120, rows6129]
  all_goals rfl

theorem atot6120 : totK PA10K2 A10K2.u6120 = [0, 701069329253, 3112602766875, 4024899881257, 1521448235131, 118702996132, 0, 0, 0, 0] := by
  rw [show A10K2.u6120 = KTree.node A10K2.t6128 (nat_lit 102910023) (nat_lit 9456126756) (nat_lit 0) A10K2.t6129 from rfl, totK_node, tot6128, tot6129]
  decide +kernel

theorem arows6121 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6121 = true := by
  rw [show A10K2.u6121 = KTree.node A10K2.t6130 (nat_lit 102924914) (nat_lit 5850744372) (nat_lit 0) A10K2.t6131 from rfl, allE_node, rows6130, irow6121, rows6131]
  all_goals rfl

theorem atot6121 : totK PA10K2 A10K2.u6121 = [0, 0, 1043302781142, 3786421575807, 3692608011533, 901608964598, 45137667897, 0, 0, 0] := by
  rw [show A10K2.u6121 = KTree.node A10K2.t6130 (nat_lit 102924914) (nat_lit 5850744372) (nat_lit 0) A10K2.t6131 from rfl, totK_node, tot6130, tot6131]
  decide +kernel

theorem arows6123 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6123 = true := by
  rw [show A10K2.u6123 = KTree.node A10K2.t6132 (nat_lit 102941447) (nat_lit 7776644072) (nat_lit 0) A10K2.t6133 from rfl, allE_node, rows6132, irow6123, rows6133]
  all_goals rfl

theorem atot6123 : totK PA10K2 A10K2.u6123 = [0, 0, 988246411564, 3677711923583, 3756907272836, 877483492192, 36992254861, 0, 0, 0] := by
  rw [show A10K2.u6123 = KTree.node A10K2.t6132 (nat_lit 102941447) (nat_lit 7776644072) (nat_lit 0) A10K2.t6133 from rfl, totK_node, tot6132, tot6133]
  decide +kernel

theorem arows6124 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6124 = true := by
  rw [show A10K2.u6124 = KTree.node A10K2.t6134 (nat_lit 102957113) (nat_lit 7339380254) (nat_lit 0) A10K2.t6135 from rfl, allE_node, rows6134, irow6124, rows6135]
  all_goals rfl

theorem atot6124 : totK PA10K2 A10K2.u6124 = [0, 617084332288, 2049078861566, 2703501090021, 2572189538676, 1313168622501, 193534632719, 5976421810, 0, 0] := by
  rw [show A10K2.u6124 = KTree.node A10K2.t6134 (nat_lit 102957113) (nat_lit 7339380254) (nat_lit 0) A10K2.t6135 from rfl, totK_node, tot6134, tot6135]
  decide +kernel

theorem arows6127 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6127 = true := by
  rw [show A10K2.u6127 = KTree.node A10K2.t6136 (nat_lit 102961728) (nat_lit 15065039418) (nat_lit 0) A10K2.t6137 from rfl, allE_node, rows6136, irow6127, rows6137]
  all_goals rfl

theorem atot6127 : totK PA10K2 A10K2.u6127 = [0, 300102511039, 1968238715948, 4065136678676, 2870648592170, 592286131961, 30810868011, 0, 0, 0] := by
  rw [show A10K2.u6127 = KTree.node A10K2.t6136 (nat_lit 102961728) (nat_lit 15065039418) (nat_lit 0) A10K2.t6137 from rfl, totK_node, tot6136, tot6137]
  decide +kernel

theorem arows6128 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6128 = true := by
  rw [show A10K2.u6128 = KTree.node A10K2.t6138 (nat_lit 102970579) (nat_lit 10878723544) (nat_lit 0) A10K2.t6139 from rfl, allE_node, rows6138, irow6128, rows6139]
  all_goals rfl

theorem atot6128 : totK PA10K2 A10K2.u6128 = [0, 693643356428, 3001055537105, 4223762628495, 2157448666365, 311207427406, 7380853412, 0, 0, 0] := by
  rw [show A10K2.u6128 = KTree.node A10K2.t6138 (nat_lit 102970579) (nat_lit 10878723544) (nat_lit 0) A10K2.t6139 from rfl, totK_node, tot6138, tot6139]
  decide +kernel

theorem arows6130 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6130 = true := by
  rw [show A10K2.u6130 = KTree.node A10K2.t6140 (nat_lit 102985202) (nat_lit 14096209049) (nat_lit 0) A10K2.t6141 from rfl, allE_node, rows6140, irow6130, rows6141]
  all_goals rfl

theorem atot6130 : totK PA10K2 A10K2.u6130 = [0, 557707638591, 2640335005582, 4172768635952, 2294979660433, 345007360988, 6853348008, 0, 0, 0] := by
  rw [show A10K2.u6130 = KTree.node A10K2.t6140 (nat_lit 102985202) (nat_lit 14096209049) (nat_lit 0) A10K2.t6141 from rfl, totK_node, tot6140, tot6141]
  decide +kernel

theorem arows6131 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6131 = true := by
  rw [show A10K2.u6131 = KTree.node A10K2.t6142 (nat_lit 102989816) (nat_lit 12610577433) (nat_lit 0) A10K2.t6143 from rfl, allE_node, rows6142, irow6131, rows6143]
  all_goals rfl

theorem atot6131 : totK PA10K2 A10K2.u6131 = [0, 0, 969491933301, 3630078196753, 3983961484609, 1239204317190, 81399449139, 0, 0, 0] := by
  rw [show A10K2.u6131 = KTree.node A10K2.t6142 (nat_lit 102989816) (nat_lit 12610577433) (nat_lit 0) A10K2.t6143 from rfl, totK_node, tot6142, tot6143]
  decide +kernel

theorem arows6142 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6142 = true := by
  rw [show A10K2.u6142 = KTree.node A10K2.t6144 (nat_lit 102994436) (nat_lit 11493754676) (nat_lit 0) A10K2.t6145 from rfl, allE_node, rows6144, irow6142, rows6145]
  all_goals rfl

theorem atot6142 : totK PA10K2 A10K2.u6142 = [0, 0, 518203833309, 2562802452009, 4234881462295, 2302152076761, 318339370466, 6904928264, 0, 0] := by
  rw [show A10K2.u6142 = KTree.node A10K2.t6144 (nat_lit 102994436) (nat_lit 11493754676) (nat_lit 0) A10K2.t6145 from rfl, totK_node, tot6144, tot6145]
  decide +kernel

theorem arows6143 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6143 = true := by
  rw [show A10K2.u6143 = KTree.node A10K2.t6146 (nat_lit 103014842) (nat_lit 13043660722) (nat_lit 0) A10K2.t6147 from rfl, allE_node, rows6146, irow6143, rows6147]
  all_goals rfl

theorem atot6143 : totK PA10K2 A10K2.u6143 = [0, 0, 1055630582321, 3729425762094, 3985621934536, 1248042075289, 76356028319, 0, 0, 0] := by
  rw [show A10K2.u6143 = KTree.node A10K2.t6146 (nat_lit 103014842) (nat_lit 13043660722) (nat_lit 0) A10K2.t6147 from rfl, totK_node, tot6146, tot6147]
  decide +kernel

theorem arows6145 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6145 = true := by
  rw [show A10K2.u6145 = KTree.node A10K2.t6148 (nat_lit 103019702) (nat_lit 16118998823) (nat_lit 0) A10K2.t6149 from rfl, allE_node, rows6148, irow6145, rows6149]
  all_goals rfl

theorem atot6145 : totK PA10K2 A10K2.u6145 = [0, 0, 336810361850, 2036645960054, 3954621826210, 2945913867916, 650783281893, 34570548376, 0, 0] := by
  rw [show A10K2.u6145 = KTree.node A10K2.t6148 (nat_lit 103019702) (nat_lit 16118998823) (nat_lit 0) A10K2.t6149 from rfl, totK_node, tot6148, tot6149]
  decide +kernel

theorem arows6146 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6146 = true := by
  rw [show A10K2.u6146 = KTree.node A10K2.t6150 (nat_lit 103025777) (nat_lit 8297467517) (nat_lit 0) A10K2.t6151 from rfl, allE_node, rows6150, irow6146, rows6151]
  all_goals rfl

theorem atot6146 : totK PA10K2 A10K2.u6146 = [0, 0, 609771204926, 2848682591894, 4057636842532, 1833679626778, 293814994183, 20070762815, 0, 0] := by
  rw [show A10K2.u6146 = KTree.node A10K2.t6150 (nat_lit 103025777) (nat_lit 8297467517) (nat_lit 0) A10K2.t6151 from rfl, totK_node, tot6150, tot6151]
  decide +kernel

theorem arows6149 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6149 = true := by
  rw [show A10K2.u6149 = KTree.node A10K2.t6152 (nat_lit 103039054) (nat_lit 10745604468) (nat_lit 0) A10K2.t6153 from rfl, allE_node, rows6152, irow6149, rows6153]
  all_goals rfl

theorem atot6149 : totK PA10K2 A10K2.u6149 = [0, 0, 609273215945, 2513713042500, 3683171470703, 2031763286196, 344827345043, 10760911071, 0, 0] := by
  rw [show A10K2.u6149 = KTree.node A10K2.t6152 (nat_lit 103039054) (nat_lit 10745604468) (nat_lit 0) A10K2.t6153 from rfl, totK_node, tot6152, tot6153]
  decide +kernel

theorem arows6150 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6150 = true := by
  rw [show A10K2.u6150 = KTree.node A10K2.t6154 (nat_lit 103045396) (nat_lit 13357073411) (nat_lit 0) A10K2.t6155 from rfl, allE_node, rows6154, irow6150, rows6155]
  all_goals rfl

theorem atot6150 : totK PA10K2 A10K2.u6150 = [0, 0, 544936715205, 2609040966036, 4006600412923, 1885167819953, 231334588170, 5705019915, 0, 0] := by
  rw [show A10K2.u6150 = KTree.node A10K2.t6154 (nat_lit 103045396) (nat_lit 13357073411) (nat_lit 0) A10K2.t6155 from rfl, totK_node, tot6154, tot6155]
  decide +kernel

theorem arows6152 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6152 = true := by
  rw [show A10K2.u6152 = KTree.node A10K2.t6156 (nat_lit 103051662) (nat_lit 14956680187) (nat_lit 0) A10K2.t6157 from rfl, allE_node, rows6156, irow6152, rows6157]
  all_goals rfl

theorem atot6152 : totK PA10K2 A10K2.u6152 = [0, 0, 305229480561, 2079514898917, 4141595039509, 2848178063301, 562869403585, 18381869251, 0, 0] := by
  rw [show A10K2.u6152 = KTree.node A10K2.t6156 (nat_lit 103051662) (nat_lit 14956680187) (nat_lit 0) A10K2.t6157 from rfl, totK_node, tot6156, tot6157]
  decide +kernel

theorem arows6153 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6153 = true := by
  rw [show A10K2.u6153 = KTree.node A10K2.t6158 (nat_lit 103058067) (nat_lit 3515677495) (nat_lit 0) A10K2.t6159 from rfl, allE_node, rows6158, irow6153, rows6159]
  all_goals rfl

theorem atot6153 : totK PA10K2 A10K2.u6153 = [0, 0, 0, 849894949745, 3355498180873, 3862927547917, 1293138670115, 109342852225, 0, 0] := by
  rw [show A10K2.u6153 = KTree.node A10K2.t6158 (nat_lit 103058067) (nat_lit 3515677495) (nat_lit 0) A10K2.t6159 from rfl, totK_node, tot6158, tot6159]
  decide +kernel

theorem arows6157 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6157 = true := by
  rw [show A10K2.u6157 = KTree.node A10K2.t6160 (nat_lit 103062985) (nat_lit 6481443019) (nat_lit 0) A10K2.t6161 from rfl, allE_node, rows6160, irow6157, rows6161]
  all_goals rfl

theorem atot6157 : totK PA10K2 A10K2.u6157 = [0, 0, 0, 505902306987, 2257208227229, 3537925261194, 2234619771761, 513156862715, 30605747850, 0] := by
  rw [show A10K2.u6157 = KTree.node A10K2.t6160 (nat_lit 103062985) (nat_lit 6481443019) (nat_lit 0) A10K2.t6161 from rfl, totK_node, tot6160, tot6161]
  decide +kernel

theorem arows6158 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6158 = true := by
  rw [show A10K2.u6158 = KTree.node A10K2.t6162 (nat_lit 103078053) (nat_lit 7333572875) (nat_lit 0) A10K2.t6163 from rfl, allE_node, rows6162, irow6158, rows6163]
  all_goals rfl

theorem atot6158 : totK PA10K2 A10K2.u6158 = [0, 0, 0, 628937652028, 2769017125874, 3818177988402, 1623426028905, 204139761356, 5528811039, 0] := by
  rw [show A10K2.u6158 = KTree.node A10K2.t6162 (nat_lit 103078053) (nat_lit 7333572875) (nat_lit 0) A10K2.t6163 from rfl, totK_node, tot6162, tot6163]
  decide +kernel

theorem arows6160 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6160 = true := by
  rw [show A10K2.u6160 = KTree.node A10K2.t6164 (nat_lit 103154241) (nat_lit 10286496343) (nat_lit 0) A10K2.t6165 from rfl, allE_node, rows6164, irow6160, rows6165]
  all_goals rfl

theorem atot6160 : totK PA10K2 A10K2.u6160 = [0, 0, 789704378163, 3046148449520, 3717346977121, 1743683872392, 380334387059, 29010686974, 0, 0] := by
  rw [show A10K2.u6160 = KTree.node A10K2.t6164 (nat_lit 103154241) (nat_lit 10286496343) (nat_lit 0) A10K2.t6165 from rfl, totK_node, tot6164, tot6165]
  decide +kernel

theorem arows6161 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6161 = true := by
  rw [show A10K2.u6161 = KTree.node A10K2.t6166 (nat_lit 103160092) (nat_lit 12069063697) (nat_lit 0) A10K2.t6167 from rfl, allE_node, rows6166, irow6161, rows6167]
  all_goals rfl

theorem atot6161 : totK PA10K2 A10K2.u6161 = [0, 0, 251705348851, 1834369418274, 3980433759436, 2770349611726, 570533030889, 30831673886, 0, 0] := by
  rw [show A10K2.u6161 = KTree.node A10K2.t6166 (nat_lit 103160092) (nat_lit 12069063697) (nat_lit 0) A10K2.t6167 from rfl, totK_node, tot6166, tot6167]
  decide +kernel

theorem arows6164 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6164 = true := by
  rw [show A10K2.u6164 = KTree.node A10K2.t6168 (nat_lit 103171221) (nat_lit 6714513073) (nat_lit 0) A10K2.t6169 from rfl, allE_node, rows6168, irow6164, rows6169]
  all_goals rfl

theorem atot6164 : totK PA10K2 A10K2.u6164 = [0, 0, 740755107523, 3005453828086, 3829706650404, 1534937816444, 157089823724, 5656154743, 0, 0] := by
  rw [show A10K2.u6164 = KTree.node A10K2.t6168 (nat_lit 103171221) (nat_lit 6714513073) (nat_lit 0) A10K2.t6169 from rfl, totK_node, tot6168, tot6169]
  decide +kernel

theorem arows6165 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6165 = true := by
  rw [show A10K2.u6165 = KTree.node A10K2.t6170 (nat_lit 103186481) (nat_lit 10026794723) (nat_lit 0) A10K2.t6171 from rfl, allE_node, rows6170, irow6165, rows6171]
  all_goals rfl

theorem atot6165 : totK PA10K2 A10K2.u6165 = [0, 0, 0, 1198875883955, 4020961145562, 3319928983504, 649599619901, 31987755669, 0, 0] := by
  rw [show A10K2.u6165 = KTree.node A10K2.t6170 (nat_lit 103186481) (nat_lit 10026794723) (nat_lit 0) A10K2.t6171 from rfl, totK_node, tot6170, tot6171]
  decide +kernel

theorem arows6167 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6167 = true := by
  rw [show A10K2.u6167 = KTree.node A10K2.t6172 (nat_lit 103202880) (nat_lit 15398834173) (nat_lit 0) A10K2.t6173 from rfl, allE_node, rows6172, irow6167, rows6173]
  all_goals rfl

theorem atot6167 : totK PA10K2 A10K2.u6167 = [0, 0, 0, 1088404924270, 3743585180051, 3588749043786, 855214477129, 49038890850, 0, 0] := by
  rw [show A10K2.u6167 = KTree.node A10K2.t6172 (nat_lit 103202880) (nat_lit 15398834173) (nat_lit 0) A10K2.t6173 from rfl, totK_node, tot6172, tot6173]
  decide +kernel

theorem arows6168 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6168 = true := by
  rw [show A10K2.u6168 = KTree.node A10K2.t6174 (nat_lit 103209235) (nat_lit 10408587183) (nat_lit 0) A10K2.t6175 from rfl, allE_node, rows6174, irow6168, rows6175]
  all_goals rfl

theorem atot6168 : totK PA10K2 A10K2.u6168 = [0, 0, 414273244854, 1488464596833, 2709040467829, 3072351054053, 1348828467679, 192168440399, 5676195732, 0] := by
  rw [show A10K2.u6168 = KTree.node A10K2.t6174 (nat_lit 103209235) (nat_lit 10408587183) (nat_lit 0) A10K2.t6175 from rfl, totK_node, tot6174, tot6175]
  decide +kernel

theorem arows6173 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6173 = true := by
  rw [show A10K2.u6173 = KTree.node A10K2.t6176 (nat_lit 103223367) (nat_lit 10991789459) (nat_lit 0) A10K2.t6177 from rfl, allE_node, rows6176, irow6173, rows6177]
  all_goals rfl

theorem atot6173 : totK PA10K2 A10K2.u6173 = [0, 0, 406838338344, 2362665845515, 4256446548890, 2373550357624, 372002347356, 20058242317, 0, 0] := by
  rw [show A10K2.u6173 = KTree.node A10K2.t6176 (nat_lit 103223367) (nat_lit 10991789459) (nat_lit 0) A10K2.t6177 from rfl, totK_node, tot6176, tot6177]
  decide +kernel

theorem arows6174 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6174 = true := by
  rw [show A10K2.u6174 = KTree.node A10K2.t6178 (nat_lit 103244069) (nat_lit 6488702061) (nat_lit 0) A10K2.t6179 from rfl, allE_node, rows6178, irow6174, rows6179]
  all_goals rfl

theorem atot6174 : totK PA10K2 A10K2.u6174 = [0, 0, 1216488229734, 4023325501059, 3813636469223, 1109748473680, 72473109678, 0, 0, 0] := by
  rw [show A10K2.u6174 = KTree.node A10K2.t6178 (nat_lit 103244069) (nat_lit 6488702061) (nat_lit 0) A10K2.t6179 from rfl, totK_node, tot6178, tot6179]
  decide +kernel

theorem arows6176 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6176 = true := by
  rw [show A10K2.u6176 = KTree.node A10K2.t6180 (nat_lit 103248794) (nat_lit 7452421363) (nat_lit 0) A10K2.t6181 from rfl, allE_node, rows6180, irow6176, rows6181]
  all_goals rfl

theorem atot6176 : totK PA10K2 A10K2.u6176 = [0, 213371739588, 684932456718, 1820472944151, 3792503110728, 2850325959018, 639522979452, 35503361870, 0, 0] := by
  rw [show A10K2.u6176 = KTree.node A10K2.t6180 (nat_lit 103248794) (nat_lit 7452421363) (nat_lit 0) A10K2.t6181 from rfl, totK_node, tot6180, tot6181]
  decide +kernel

theorem arows6177 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6177 = true := by
  rw [show A10K2.u6177 = KTree.node A10K2.t6182 (nat_lit 103812167) (nat_lit 11183700617) (nat_lit 0) A10K2.t6183 from rfl, allE_node, rows6182, irow6177, rows6183]
  all_goals rfl

theorem atot6177 : totK PA10K2 A10K2.u6177 = [0, 625420685475, 2812893014104, 4019787537969, 1869998068246, 303512873341, 20070762815, 0, 0, 0] := by
  rw [show A10K2.u6177 = KTree.node A10K2.t6182 (nat_lit 103812167) (nat_lit 11183700617) (nat_lit 0) A10K2.t6183 from rfl, totK_node, tot6182, tot6183]
  decide +kernel

theorem arows6180 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6180 = true := by
  rw [show A10K2.u6180 = KTree.node A10K2.t6184 (nat_lit 103825521) (nat_lit 8316042637) (nat_lit 0) A10K2.t6185 from rfl, allE_node, rows6184, irow6180, rows6185]
  all_goals rfl

theorem atot6180 : totK PA10K2 A10K2.u6180 = [0, 603329993010, 2519596539058, 3789546346105, 2209836294092, 367050378590, 10760911071, 0, 0, 0] := by
  rw [show A10K2.u6180 = KTree.node A10K2.t6184 (nat_lit 103825521) (nat_lit 8316042637) (nat_lit 0) A10K2.t6185 from rfl, totK_node, tot6184, tot6185]
  decide +kernel

theorem arows6181 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6181 = true := by
  rw [show A10K2.u6181 = KTree.node A10K2.t6186 (nat_lit 103831649) (nat_lit 9584597604) (nat_lit 0) A10K2.t6187 from rfl, allE_node, rows6186, irow6181, rows6187]
  all_goals rfl

theorem atot6181 : totK PA10K2 A10K2.u6181 = [0, 429851917541, 2483917098444, 4107713622059, 2138995342621, 300668205688, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u6181 = KTree.node A10K2.t6186 (nat_lit 103831649) (nat_lit 9584597604) (nat_lit 0) A10K2.t6187 from rfl, totK_node, tot6186, tot6187]
  decide +kernel

theorem arows6183 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6183 = true := by
  rw [show A10K2.u6183 = KTree.node A10K2.t6188 (nat_lit 103838250) (nat_lit 3360576868) (nat_lit 0) A10K2.t6189 from rfl, allE_node, rows6188, irow6183, rows6189]
  all_goals rfl

theorem atot6183 : totK PA10K2 A10K2.u6183 = [0, 295757175837, 2002853139576, 4125328791911, 3055282297383, 681441114612, 35503361870, 0, 0, 0] := by
  rw [show A10K2.u6183 = KTree.node A10K2.t6188 (nat_lit 103838250) (nat_lit 3360576868) (nat_lit 0) A10K2.t6189 from rfl, totK_node, tot6188, tot6189]
  decide +kernel

theorem arows6184 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6184 = true := by
  rw [show A10K2.u6184 = KTree.node A10K2.t6190 (nat_lit 103845042) (nat_lit 10792136195) (nat_lit 0) A10K2.t6191 from rfl, allE_node, rows6190, irow6184, rows6191]
  all_goals rfl

theorem atot6184 : totK PA10K2 A10K2.u6184 = [0, 0, 583683233590, 2740756909626, 3924407159987, 1878738687548, 374193427281, 25239774317, 0, 0] := by
  rw [show A10K2.u6184 = KTree.node A10K2.t6190 (nat_lit 103845042) (nat_lit 10792136195) (nat_lit 0) A10K2.t6191 from rfl, totK_node, tot6190, tot6191]
  decide +kernel

theorem arows6188 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6188 = true := by
  rw [show A10K2.u6188 = KTree.node A10K2.t6192 (nat_lit 103858561) (nat_lit 10408176596) (nat_lit 0) A10K2.t6193 from rfl, allE_node, rows6192, irow6188, rows6193]
  all_goals rfl

theorem atot6188 : totK PA10K2 A10K2.u6188 = [0, 0, 747777676226, 2912355587473, 3753283630353, 1728889916119, 238440702400, 5410721913, 0, 0] := by
  rw [show A10K2.u6188 = KTree.node A10K2.t6192 (nat_lit 103858561) (nat_lit 10408176596) (nat_lit 0) A10K2.t6193 from rfl, totK_node, tot6192, tot6193]
  decide +kernel

theorem arows6189 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6189 = true := by
  rw [show A10K2.u6189 = KTree.node A10K2.t6194 (nat_lit 103864685) (nat_lit 6400398420) (nat_lit 0) A10K2.t6195 from rfl, allE_node, rows6194, irow6189, rows6195]
  all_goals rfl

theorem atot6189 : totK PA10K2 A10K2.u6189 = [0, 0, 590619959281, 2807032166978, 4141381566862, 1817376635819, 219178372242, 5546304973, 0, 0] := by
  rw [show A10K2.u6189 = KTree.node A10K2.t6194 (nat_lit 103864685) (nat_lit 6400398420) (nat_lit 0) A10K2.t6195 from rfl, totK_node, tot6194, tot6195]
  decide +kernel

theorem arows6191 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6191 = true := by
  rw [show A10K2.u6191 = KTree.node A10K2.t6196 (nat_lit 103942200) (nat_lit 14437886109) (nat_lit 0) A10K2.t6197 from rfl, allE_node, rows6196, irow6191, rows6197]
  all_goals rfl

theorem atot6191 : totK PA10K2 A10K2.u6191 = [0, 762344704339, 2887841357077, 3660614262908, 1977974368170, 476622514301, 29791859037, 0, 0, 0] := by
  rw [show A10K2.u6191 = KTree.node A10K2.t6196 (nat_lit 103942200) (nat_lit 14437886109) (nat_lit 0) A10K2.t6197 from rfl, totK_node, tot6196, tot6197]
  decide +kernel

theorem arows6192 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6192 = true := by
  rw [show A10K2.u6192 = KTree.node A10K2.t6198 (nat_lit 103947276) (nat_lit 10217015745) (nat_lit 0) A10K2.t6199 from rfl, allE_node, rows6198, irow6192, rows6199]
  all_goals rfl

theorem atot6192 : totK PA10K2 A10K2.u6192 = [0, 523679276711, 2236096443825, 3720247944819, 2542037130376, 541506483106, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u6192 = KTree.node A10K2.t6198 (nat_lit 103947276) (nat_lit 10217015745) (nat_lit 0) A10K2.t6199 from rfl, totK_node, tot6198, tot6199]
  decide +kernel

theorem arows6195 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6195 = true := by
  rw [show A10K2.u6195 = KTree.node A10K2.t6200 (nat_lit 103954657) (nat_lit 4757319471) (nat_lit 0) A10K2.t6201 from rfl, allE_node, rows6200, irow6195, rows6201]
  all_goals rfl

theorem atot6195 : totK PA10K2 A10K2.u6195 = [0, 413936223319, 2223214114618, 3832695864873, 2482931997684, 495035347890, 31333686660, 0, 0, 0] := by
  rw [show A10K2.u6195 = KTree.node A10K2.t6200 (nat_lit 103954657) (nat_lit 4757319471) (nat_lit 0) A10K2.t6201 from rfl, totK_node, tot6200, tot6201]
  decide +kernel

theorem arows6196 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6196 = true := by
  rw [show A10K2.u6196 = KTree.node A10K2.t6202 (nat_lit 103959397) (nat_lit 7253494417) (nat_lit 0) A10K2.t6203 from rfl, allE_node, rows6202, irow6196, rows6203]
  all_goals rfl

theorem atot6196 : totK PA10K2 A10K2.u6196 = [0, 445153241330, 2592149804479, 4240510474094, 1942036691696, 181700210141, 0, 0, 0, 0] := by
  rw [show A10K2.u6196 = KTree.node A10K2.t6202 (nat_lit 103959397) (nat_lit 7253494417) (nat_lit 0) A10K2.t6203 from rfl, totK_node, tot6202, tot6203]
  decide +kernel

theorem arows6198 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6198 = true := by
  rw [show A10K2.u6198 = KTree.node A10K2.t6204 (nat_lit 103975200) (nat_lit 13063659673) (nat_lit 0) A10K2.t6205 from rfl, allE_node, rows6204, irow6198, rows6205]
  all_goals rfl

theorem atot6198 : totK PA10K2 A10K2.u6198 = [0, 0, 1040290194111, 3776006981814, 3846950047389, 958385209631, 45137667897, 0, 0, 0] := by
  rw [show A10K2.u6198 = KTree.node A10K2.t6204 (nat_lit 103975200) (nat_lit 13063659673) (nat_lit 0) A10K2.t6205 from rfl, totK_node, tot6204, tot6205]
  decide +kernel

theorem arows6199 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6199 = true := by
  rw [show A10K2.u6199 = KTree.node A10K2.t6206 (nat_lit 103989703) (nat_lit 11143296614) (nat_lit 0) A10K2.t6207 from rfl, allE_node, rows6206, irow6199, rows6207]
  all_goals rfl

theorem atot6199 : totK PA10K2 A10K2.u6199 = [0, 0, 984579809137, 3511261223067, 3717538711822, 1062684916209, 82303251995, 0, 0, 0] := by
  rw [show A10K2.u6199 = KTree.node A10K2.t6206 (nat_lit 103989703) (nat_lit 11143296614) (nat_lit 0) A10K2.t6207 from rfl, totK_node, tot6206, tot6207]
  decide +kernel

theorem arows6205 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6205 = true := by
  rw [show A10K2.u6205 = KTree.node A10K2.t6208 (nat_lit 103995550) (nat_lit 9388867742) (nat_lit 0) A10K2.t6209 from rfl, allE_node, rows6208, irow6205, rows6209]
  all_goals rfl

theorem atot6205 : totK PA10K2 A10K2.u6205 = [0, 0, 427553684867, 2498530694424, 4136253127151, 1980336906637, 291459347602, 6354482628, 0, 0] := by
  rw [show A10K2.u6205 = KTree.node A10K2.t6208 (nat_lit 103995550) (nat_lit 9388867742) (nat_lit 0) A10K2.t6209 from rfl, totK_node, tot6208, tot6209]
  decide +kernel

theorem arows6206 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6206 = true := by
  rw [show A10K2.u6206 = KTree.node A10K2.t6210 (nat_lit 104075145) (nat_lit 8367675134) (nat_lit 0) A10K2.t6211 from rfl, allE_node, rows6210, irow6206, rows6211]
  all_goals rfl

theorem atot6206 : totK PA10K2 A10K2.u6206 = [0, 0, 523813060156, 2549034199582, 3971570233998, 2058046438980, 395361648797, 25371180993, 0, 0] := by
  rw [show A10K2.u6206 = KTree.node A10K2.t6210 (nat_lit 104075145) (nat_lit 8367675134) (nat_lit 0) A10K2.t6211 from rfl, totK_node, tot6210, tot6211]
  decide +kernel

theorem arows6208 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6208 = true := by
  rw [show A10K2.u6208 = KTree.node A10K2.t6212 (nat_lit 104088390) (nat_lit 10317107059) (nat_lit 0) A10K2.t6213 from rfl, allE_node, rows6212, irow6208, rows6213]
  all_goals rfl

theorem atot6208 : totK PA10K2 A10K2.u6208 = [0, 0, 749316832580, 3008239752386, 3812576403420, 1655264161276, 217218807241, 5447185874, 0, 0] := by
  rw [show A10K2.u6208 = KTree.node A10K2.t6212 (nat_lit 104088390) (nat_lit 10317107059) (nat_lit 0) A10K2.t6213 from rfl, totK_node, tot6212, tot6213]
  decide +kernel

theorem arows6209 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6209 = true := by
  rw [show A10K2.u6209 = KTree.node A10K2.t6214 (nat_lit 104094573) (nat_lit 6354482628) (nat_lit 0) A10K2.t6215 from rfl, allE_node, rows6214, irow6209, rows6215]
  all_goals rfl

theorem atot6209 : totK PA10K2 A10K2.u6209 = [0, 0, 593149538699, 2691315842890, 4105809289165, 2001361976924, 246955865575, 6354482628, 0, 0] := by
  rw [show A10K2.u6209 = KTree.node A10K2.t6214 (nat_lit 104094573) (nat_lit 6354482628) (nat_lit 0) A10K2.t6215 from rfl, totK_node, tot6214, tot6215]
  decide +kernel

theorem arows6212 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6212 = true := by
  rw [show A10K2.u6212 = KTree.node A10K2.t6216 (nat_lit 104202285) (nat_lit 6414069378) (nat_lit 0) A10K2.t6217 from rfl, allE_node, rows6216, irow6212, rows6217]
  all_goals rfl

theorem atot6212 : totK PA10K2 A10K2.u6212 = [0, 0, 577284929806, 2796086412132, 4085129321613, 1998528497009, 293541214528, 6853348008, 0, 0] := by
  rw [show A10K2.u6212 = KTree.node A10K2.t6216 (nat_lit 104202285) (nat_lit 6414069378) (nat_lit 0) A10K2.t6217 from rfl, totK_node, tot6216, tot6217]
  decide +kernel

theorem arows6213 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6213 = true := by
  rw [show A10K2.u6213 = KTree.node A10K2.t6218 (nat_lit 104207204) (nat_lit 12922967299) (nat_lit 0) A10K2.t6219 from rfl, allE_node, rows6218, irow6213, rows6219]
  all_goals rfl

theorem atot6213 : totK PA10K2 A10K2.u6213 = [0, 0, 464110601391, 2161646297717, 3862688711178, 2480358436614, 467316409872, 30074883546, 0, 0] := by
  rw [show A10K2.u6213 = KTree.node A10K2.t6218 (nat_lit 104207204) (nat_lit 12922967299) (nat_lit 0) A10K2.t6219 from rfl, totK_node, tot6218, tot6219]
  decide +kernel

theorem arows6215 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6215 = true := by
  rw [show A10K2.u6215 = KTree.node A10K2.t6220 (nat_lit 104215842) (nat_lit 13708722487) (nat_lit 0) A10K2.t6221 from rfl, allE_node, rows6220, irow6215, rows6221]
  all_goals rfl

theorem atot6215 : totK PA10K2 A10K2.u6215 = [0, 0, 554125471463, 2746267896423, 4087011796251, 1800361850725, 242754114883, 6034215561, 0, 0] := by
  rw [show A10K2.u6215 = KTree.node A10K2.t6220 (nat_lit 104215842) (nat_lit 13708722487) (nat_lit 0) A10K2.t6221 from rfl, totK_node, tot6220, tot6221]
  decide +kernel

theorem arows6216 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6216 = true := by
  rw [show A10K2.u6216 = KTree.node A10K2.t6222 (nat_lit 104221012) (nat_lit 13140071320) (nat_lit 0) A10K2.t6223 from rfl, allE_node, rows6222, irow6216, rows6223]
  all_goals rfl

theorem atot6216 : totK PA10K2 A10K2.u6216 = [0, 0, 546985495730, 2850719945723, 4212892174843, 1582341839862, 122331997394, 0, 0, 0] := by
  rw [show A10K2.u6216 = KTree.node A10K2.t6222 (nat_lit 104221012) (nat_lit 13140071320) (nat_lit 0) A10K2.t6223 from rfl, totK_node, tot6222, tot6223]
  decide +kernel

theorem arows6220 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6220 = true := by
  rw [show A10K2.u6220 = KTree.node A10K2.t6224 (nat_lit 104237096) (nat_lit 12645193567) (nat_lit 0) A10K2.t6225 from rfl, allE_node, rows6224, irow6220, rows6225]
  all_goals rfl

theorem atot6220 : totK PA10K2 A10K2.u6220 = [0, 0, 0, 1212754883437, 4000850620534, 3343060396267, 716883572842, 37547833973, 0, 0] := by
  rw [show A10K2.u6220 = KTree.node A10K2.t6224 (nat_lit 104237096) (nat_lit 12645193567) (nat_lit 0) A10K2.t6225 from rfl, totK_node, tot6224, tot6225]
  decide +kernel

theorem arows6221 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6221 = true := by
  rw [show A10K2.u6221 = KTree.node A10K2.t6226 (nat_lit 104252292) (nat_lit 8756751404) (nat_lit 0) A10K2.t6227 from rfl, allE_node, rows6226, irow6221, rows6227]
  all_goals rfl

theorem atot6221 : totK PA10K2 A10K2.u6221 = [0, 0, 0, 1013931751826, 3738395948111, 3534135183872, 833493871699, 36913694812, 0, 0] := by
  rw [show A10K2.u6221 = KTree.node A10K2.t6226 (nat_lit 104252292) (nat_lit 8756751404) (nat_lit 0) A10K2.t6227 from rfl, totK_node, tot6226, tot6227]
  decide +kernel

theorem arows6223 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6223 = true := by
  rw [show A10K2.u6223 = KTree.node A10K2.t6228 (nat_lit 104333374) (nat_lit 15400967003) (nat_lit 0) A10K2.t6229 from rfl, allE_node, rows6228, irow6223, rows6229]
  all_goals rfl

theorem atot6223 : totK PA10K2 A10K2.u6223 = [0, 540022072669, 1965044916544, 1980469514527, 1268483158073, 2002049605327, 1193630820382, 193255931756, 5976421810, 0] := by
  rw [show A10K2.u6223 = KTree.node A10K2.t6228 (nat_lit 104333374) (nat_lit 15400967003) (nat_lit 0) A10K2.t6229 from rfl, totK_node, tot6228, tot6229]
  decide +kernel

theorem arows6224 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6224 = true := by
  rw [show A10K2.u6224 = KTree.node A10K2.t6230 (nat_lit 104337913) (nat_lit 6214476949) (nat_lit 0) A10K2.t6231 from rfl, allE_node, rows6230, irow6224, rows6231]
  all_goals rfl

theorem atot6224 : totK PA10K2 A10K2.u6224 = [0, 295901161011, 1922805286652, 4014585493130, 2852134900697, 578426116575, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u6224 = KTree.node A10K2.t6230 (nat_lit 104337913) (nat_lit 6214476949) (nat_lit 0) A10K2.t6231 from rfl, totK_node, tot6230, tot6231]
  decide +kernel

theorem arows6227 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6227 = true := by
  rw [show A10K2.u6227 = KTree.node A10K2.t6232 (nat_lit 104352517) (nat_lit 7024573361) (nat_lit 0) A10K2.t6233 from rfl, allE_node, rows6232, irow6227, rows6233]
  all_goals rfl

theorem atot6227 : totK PA10K2 A10K2.u6227 = [0, 671660243090, 2737325636414, 3810871459642, 1864029209264, 252574200503, 5976421810, 0, 0, 0] := by
  rw [show A10K2.u6227 = KTree.node A10K2.t6232 (nat_lit 104352517) (nat_lit 7024573361) (nat_lit 0) A10K2.t6233 from rfl, totK_node, tot6232, tot6233]
  decide +kernel

theorem arows6228 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6228 = true := by
  rw [show A10K2.u6228 = KTree.node A10K2.t6234 (nat_lit 104361170) (nat_lit 15178939812) (nat_lit 0) A10K2.t6235 from rfl, allE_node, rows6234, irow6228, rows6235]
  all_goals rfl

theorem atot6228 : totK PA10K2 A10K2.u6228 = [0, 669392058922, 2971629561626, 4197160615169, 2037590728768, 292525762077, 6853348008, 0, 0, 0] := by
  rw [show A10K2.u6228 = KTree.node A10K2.t6234 (nat_lit 104361170) (nat_lit 15178939812) (nat_lit 0) A10K2.t6235 from rfl, totK_node, tot6234, tot6235]
  decide +kernel

theorem arows6230 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6230 = true := by
  rw [show A10K2.u6230 = KTree.node A10K2.t6236 (nat_lit 104365973) (nat_lit 2189933746) (nat_lit 0) A10K2.t6237 from rfl, allE_node, rows6236, irow6230, rows6237]
  all_goals rfl

theorem atot6230 : totK PA10K2 A10K2.u6230 = [0, 0, 1064363161325, 3750225551099, 3902976543353, 1161352436462, 81522249172, 0, 0, 0] := by
  rw [show A10K2.u6230 = KTree.node A10K2.t6236 (nat_lit 104365973) (nat_lit 2189933746) (nat_lit 0) A10K2.t6237 from rfl, totK_node, tot6236, tot6237]
  decide +kernel

theorem arows6231 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6231 = true := by
  rw [show A10K2.u6231 = KTree.node A10K2.t6238 (nat_lit 104370531) (nat_lit 4121389346) (nat_lit 0) A10K2.t6239 from rfl, allE_node, rows6238, irow6231, rows6239]
  all_goals rfl

theorem atot6231 : totK PA10K2 A10K2.u6231 = [0, 0, 295657391945, 2095293049632, 4027994853460, 2502980570708, 525431639059, 30650496230, 0, 0] := by
  rw [show A10K2.u6231 = KTree.node A10K2.t6238 (nat_lit 104370531) (nat_lit 4121389346) (nat_lit 0) A10K2.t6239 from rfl, totK_node, tot6238, tot6239]
  decide +kernel

theorem arows6236 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6236 = true := by
  rw [show A10K2.u6236 = KTree.node A10K2.t6240 (nat_lit 104385086) (nat_lit 10143244566) (nat_lit 0) A10K2.t6241 from rfl, allE_node, rows6240, irow6236, rows6241]
  all_goals rfl

theorem atot6236 : totK PA10K2 A10K2.u6236 = [0, 0, 1019343946839, 3684394528033, 3866339501476, 1109168645030, 81432950487, 0, 0, 0] := by
  rw [show A10K2.u6236 = KTree.node A10K2.t6240 (nat_lit 104385086) (nat_lit 10143244566) (nat_lit 0) A10K2.t6241 from rfl, totK_node, tot6240, tot6241]
  decide +kernel

theorem arows6237 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6237 = true := by
  rw [show A10K2.u6237 = KTree.node A10K2.t6242 (nat_lit 104408499) (nat_lit 9912139066) (nat_lit 0) A10K2.t6243 from rfl, allE_node, rows6242, irow6237, rows6243]
  all_goals rfl

theorem atot6237 : totK PA10K2 A10K2.u6237 = [0, 779827310996, 2884211232233, 3619347524023, 2140893204047, 633245365327, 50548650670, 0, 0, 0] := by
  rw [show A10K2.u6237 = KTree.node A10K2.t6242 (nat_lit 104408499) (nat_lit 9912139066) (nat_lit 0) A10K2.t6243 from rfl, totK_node, tot6242, tot6243]
  decide +kernel

theorem arows6239 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6239 = true := by
  rw [show A10K2.u6239 = KTree.node A10K2.t6244 (nat_lit 104413405) (nat_lit 5725859541) (nat_lit 0) A10K2.t6245 from rfl, allE_node, rows6244, irow6239, rows6245]
  all_goals rfl

theorem atot6239 : totK PA10K2 A10K2.u6239 = [0, 278623868914, 1955521438192, 4237981107192, 3024676690573, 612281818243, 31543789865, 0, 0, 0] := by
  rw [show A10K2.u6239 = KTree.node A10K2.t6244 (nat_lit 104413405) (nat_lit 5725859541) (nat_lit 0) A10K2.t6245 from rfl, totK_node, tot6244, tot6245]
  decide +kernel

theorem arows6240 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6240 = true := by
  rw [show A10K2.u6240 = KTree.node A10K2.t6246 (nat_lit 104427164) (nat_lit 9657341456) (nat_lit 0) A10K2.t6247 from rfl, allE_node, rows6246, irow6240, rows6247]
  all_goals rfl

theorem atot6240 : totK PA10K2 A10K2.u6240 = [0, 548284400172, 2656238422272, 4227531691422, 2472379478373, 369334550780, 6585347165, 0, 0, 0] := by
  rw [show A10K2.u6240 = KTree.node A10K2.t6246 (nat_lit 104427164) (nat_lit 9657341456) (nat_lit 0) A10K2.t6247 from rfl, totK_node, tot6246, tot6247]
  decide +kernel

theorem arows6243 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6243 = true := by
  rw [show A10K2.u6243 = KTree.node A10K2.t6248 (nat_lit 104441173) (nat_lit 6830905040) (nat_lit 0) A10K2.t6249 from rfl, allE_node, rows6248, irow6243, rows6249]
  all_goals rfl

theorem atot6243 : totK PA10K2 A10K2.u6243 = [0, 0, 1097850928185, 3754913391554, 3881721255457, 1212292430772, 88197296566, 0, 0, 0] := by
  rw [show A10K2.u6243 = KTree.node A10K2.t6248 (nat_lit 104441173) (nat_lit 6830905040) (nat_lit 0) A10K2.t6249 from rfl, totK_node, tot6248, tot6249]
  decide +kernel

theorem arows6244 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6244 = true := by
  rw [show A10K2.u6244 = KTree.node A10K2.t6250 (nat_lit 104446244) (nat_lit 14146312874) (nat_lit 0) A10K2.t6251 from rfl, allE_node, rows6250, irow6244, rows6251]
  all_goals rfl

theorem atot6244 : totK PA10K2 A10K2.u6244 = [0, 0, 504494621672, 2773189443625, 4356036784996, 2172989250476, 301198357984, 7380853412, 0, 0] := by
  rw [show A10K2.u6244 = KTree.node A10K2.t6250 (nat_lit 104446244) (nat_lit 14146312874) (nat_lit 0) A10K2.t6251 from rfl, totK_node, tot6250, tot6251]
  decide +kernel

theorem arows6246 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6246 = true := by
  rw [show A10K2.u6246 = KTree.node A10K2.t6252 (nat_lit 104529977) (nat_lit 7339380254) (nat_lit 0) A10K2.t6253 from rfl, allE_node, rows6252, irow6246, rows6253]
  all_goals rfl

theorem atot6246 : totK PA10K2 A10K2.u6246 = [0, 593198486230, 2321054000963, 3425488855462, 2594522704254, 874639881529, 63233022410, 0, 0, 0] := by
  rw [show A10K2.u6246 = KTree.node A10K2.t6252 (nat_lit 104529977) (nat_lit 7339380254) (nat_lit 0) A10K2.t6253 from rfl, totK_node, tot6252, tot6253]
  decide +kernel

theorem arows6247 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6247 = true := by
  rw [show A10K2.u6247 = KTree.node A10K2.t6254 (nat_lit 104534646) (nat_lit 13596205329) (nat_lit 0) A10K2.t6255 from rfl, allE_node, rows6254, irow6247, rows6255]
  all_goals rfl

theorem atot6247 : totK PA10K2 A10K2.u6247 = [0, 437464120780, 2190118535707, 3993668800654, 2700057158932, 509475577890, 25295400199, 0, 0, 0] := by
  rw [show A10K2.u6247 = KTree.node A10K2.t6254 (nat_lit 104534646) (nat_lit 13596205329) (nat_lit 0) A10K2.t6255 from rfl, totK_node, tot6254, tot6255]
  decide +kernel

theorem arows6251 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6251 = true := by
  rw [show A10K2.u6251 = KTree.node A10K2.t6256 (nat_lit 104541925) (nat_lit 4292556535) (nat_lit 0) A10K2.t6257 from rfl, allE_node, rows6256, irow6251, rows6257]
  all_goals rfl

theorem atot6251 : totK PA10K2 A10K2.u6251 = [0, 433044328481, 2506391573977, 4330705449703, 2506238056956, 425755453084, 12692412833, 0, 0, 0] := by
  rw [show A10K2.u6251 = KTree.node A10K2.t6256 (nat_lit 104541925) (nat_lit 4292556535) (nat_lit 0) A10K2.t6257 from rfl, totK_node, tot6256, tot6257]
  decide +kernel

theorem arows6252 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6252 = true := by
  rw [show A10K2.u6252 = KTree.node A10K2.t6258 (nat_lit 104555982) (nat_lit 14760619308) (nat_lit 0) A10K2.t6259 from rfl, allE_node, rows6258, irow6252, rows6259]
  all_goals rfl

theorem atot6252 : totK PA10K2 A10K2.u6252 = [0, 883059426070, 3367041735427, 4056300023696, 1604465538736, 144499641314, 0, 0, 0, 0] := by
  rw [show A10K2.u6252 = KTree.node A10K2.t6258 (nat_lit 104555982) (nat_lit 14760619308) (nat_lit 0) A10K2.t6259 from rfl, totK_node, tot6258, tot6259]
  decide +kernel

theorem arows6254 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6254 = true := by
  rw [show A10K2.u6254 = KTree.node A10K2.t6260 (nat_lit 104560568) (nat_lit 12261905858) (nat_lit 0) A10K2.t6261 from rfl, allE_node, rows6260, irow6254, rows6261]
  all_goals rfl

theorem atot6254 : totK PA10K2 A10K2.u6254 = [0, 0, 1164531374683, 3949209153184, 3793431195972, 1021024140194, 62996513375, 0, 0, 0] := by
  rw [show A10K2.u6254 = KTree.node A10K2.t6260 (nat_lit 104560568) (nat_lit 12261905858) (nat_lit 0) A10K2.t6261 from rfl, totK_node, tot6260, tot6261]
  decide +kernel

theorem arows6255 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6255 = true := by
  rw [show A10K2.u6255 = KTree.node A10K2.t6262 (nat_lit 104566326) (nat_lit 16393281810) (nat_lit 0) A10K2.t6263 from rfl, allE_node, rows6262, irow6255, rows6263]
  all_goals rfl

theorem atot6255 : totK PA10K2 A10K2.u6255 = [0, 0, 476236816663, 2577824800318, 4205506904161, 2163426318679, 299180907387, 6904928264, 0, 0] := by
  rw [show A10K2.u6255 = KTree.node A10K2.t6262 (nat_lit 104566326) (nat_lit 16393281810) (nat_lit 0) A10K2.t6263 from rfl, totK_node, tot6262, tot6263]
  decide +kernel

theorem arows6258 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6258 = true := by
  rw [show A10K2.u6258 = KTree.node A10K2.t6264 (nat_lit 104573597) (nat_lit 5706374090) (nat_lit 0) A10K2.t6265 from rfl, allE_node, rows6264, irow6258, rows6265]
  all_goals rfl

theorem atot6258 : totK PA10K2 A10K2.u6258 = [0, 0, 684419437868, 3104956682272, 4317957221324, 1885842316323, 160857558599, 0, 0, 0] := by
  rw [show A10K2.u6258 = KTree.node A10K2.t6264 (nat_lit 104573597) (nat_lit 5706374090) (nat_lit 0) A10K2.t6265 from rfl, totK_node, tot6264, tot6265]
  decide +kernel

theorem arows6259 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6259 = true := by
  rw [show A10K2.u6259 = KTree.node A10K2.t6266 (nat_lit 104588040) (nat_lit 13862387326) (nat_lit 0) A10K2.t6267 from rfl, allE_node, rows6266, irow6259, rows6267]
  all_goals rfl

theorem atot6259 : totK PA10K2 A10K2.u6259 = [0, 0, 880779957843, 3299571601334, 3894489581766, 1665383865457, 212264548250, 6766355402, 0, 0] := by
  rw [show A10K2.u6259 = KTree.node A10K2.t6266 (nat_lit 104588040) (nat_lit 13862387326) (nat_lit 0) A10K2.t6267 from rfl, totK_node, tot6266, tot6267]
  decide +kernel

theorem arows6261 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6261 = true := by
  rw [show A10K2.u6261 = KTree.node A10K2.t6268 (nat_lit 104592723) (nat_lit 9888584122) (nat_lit 0) A10K2.t6269 from rfl, allE_node, rows6268, irow6261, rows6269]
  all_goals rfl

theorem atot6261 : totK PA10K2 A10K2.u6261 = [0, 0, 0, 1197499581988, 3959387054926, 3741235854200, 911716517888, 35098285598, 0, 0] := by
  rw [show A10K2.u6261 = KTree.node A10K2.t6268 (nat_lit 104592723) (nat_lit 9888584122) (nat_lit 0) A10K2.t6269 from rfl, totK_node, tot6268, tot6269]
  decide +kernel

theorem arows6262 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6262 = true := by
  rw [show A10K2.u6262 = KTree.node A10K2.t6270 (nat_lit 105458322) (nat_lit 15529038244) (nat_lit 0) A10K2.t6271 from rfl, allE_node, rows6270, irow6262, rows6271]
  all_goals rfl

theorem atot6262 : totK PA10K2 A10K2.u6262 = [872244600920, 3408362204235, 4004825828675, 1370203462223, 102862735796, 0, 41084160164, 26011840508, 0, 0] := by
  rw [show A10K2.u6262 = KTree.node A10K2.t6270 (nat_lit 105458322) (nat_lit 15529038244) (nat_lit 0) A10K2.t6271 from rfl, totK_node, tot6270, tot6271]
  decide +kernel

theorem arows6269 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6269 = true := by
  rw [show A10K2.u6269 = KTree.node A10K2.t6272 (nat_lit 105462939) (nat_lit 9966385584) (nat_lit 0) A10K2.t6273 from rfl, allE_node, rows6272, irow6269, rows6273]
  all_goals rfl

theorem atot6269 : totK PA10K2 A10K2.u6269 = [412332156094, 2042650429869, 3677163717090, 2731608917882, 598781947871, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u6269 = KTree.node A10K2.t6272 (nat_lit 105462939) (nat_lit 9966385584) (nat_lit 0) A10K2.t6273 from rfl, totK_node, tot6272, tot6273]
  decide +kernel

theorem arows6270 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6270 = true := by
  rw [show A10K2.u6270 = KTree.node A10K2.t6274 (nat_lit 105469224) (nat_lit 10219352061) (nat_lit 0) A10K2.t6275 from rfl, allE_node, rows6274, irow6270, rows6275]
  all_goals rfl

theorem atot6270 : totK PA10K2 A10K2.u6270 = [491133302862, 2460579508352, 4061415969870, 2043286953101, 273679356444, 6354482628, 0, 0, 0, 0] := by
  rw [show A10K2.u6270 = KTree.node A10K2.t6274 (nat_lit 105469224) (nat_lit 10219352061) (nat_lit 0) A10K2.t6275 from rfl, totK_node, tot6274, tot6275]
  decide +kernel

theorem arows6272 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6272 = true := by
  rw [show A10K2.u6272 = KTree.node A10K2.t6276 (nat_lit 105475655) (nat_lit 11179514773) (nat_lit 0) A10K2.t6277 from rfl, allE_node, rows6276, irow6272, rows6277]
  all_goals rfl

theorem atot6272 : totK PA10K2 A10K2.u6272 = [568469117275, 2691749283983, 4139244200704, 2363280060891, 399807738270, 13732569049, 0, 0, 0, 0] := by
  rw [show A10K2.u6272 = KTree.node A10K2.t6276 (nat_lit 105475655) (nat_lit 11179514773) (nat_lit 0) A10K2.t6277 from rfl, totK_node, tot6276, tot6277]
  decide +kernel

theorem arows6273 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6273 = true := by
  rw [show A10K2.u6273 = KTree.node A10K2.t6278 (nat_lit 105489749) (nat_lit 6830905040) (nat_lit 0) A10K2.t6279 from rfl, allE_node, rows6278, irow6273, rows6279]
  all_goals rfl

theorem atot6273 : totK PA10K2 A10K2.u6273 = [0, 952834988724, 3581061908377, 3896635565339, 1177434504257, 81452958604, 0, 0, 0, 0] := by
  rw [show A10K2.u6273 = KTree.node A10K2.t6278 (nat_lit 105489749) (nat_lit 6830905040) (nat_lit 0) A10K2.t6279 from rfl, totK_node, tot6278, tot6279]
  decide +kernel

theorem arows6276 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6276 = true := by
  rw [show A10K2.u6276 = KTree.node A10K2.t6280 (nat_lit 105494250) (nat_lit 12254763382) (nat_lit 0) A10K2.t6281 from rfl, allE_node, rows6280, irow6276, rows6281]
  all_goals rfl

theorem atot6276 : totK PA10K2 A10K2.u6276 = [0, 305255166090, 1911079710183, 3969147266863, 2783073038659, 571868449210, 31082886609, 0, 0, 0] := by
  rw [show A10K2.u6276 = KTree.node A10K2.t6280 (nat_lit 105494250) (nat_lit 12254763382) (nat_lit 0) A10K2.t6281 from rfl, totK_node, tot6280, tot6281]
  decide +kernel

theorem arows6277 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6277 = true := by
  rw [show A10K2.u6277 = KTree.node A10K2.t6282 (nat_lit 105498881) (nat_lit 9573235790) (nat_lit 0) A10K2.t6283 from rfl, allE_node, rows6282, irow6277, rows6283]
  all_goals rfl

theorem atot6277 : totK PA10K2 A10K2.u6277 = [0, 603049784421, 2920306824667, 4009525360891, 1511503049115, 109291298544, 0, 0, 0, 0] := by
  rw [show A10K2.u6277 = KTree.node A10K2.t6282 (nat_lit 105498881) (nat_lit 9573235790) (nat_lit 0) A10K2.t6283 from rfl, totK_node, tot6282, tot6283]
  decide +kernel

theorem arows6279 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6279 = true := by
  rw [show A10K2.u6279 = KTree.node A10K2.t6284 (nat_lit 105506477) (nat_lit 5485165328) (nat_lit 0) A10K2.t6285 from rfl, allE_node, rows6284, irow6279, rows6285]
  all_goals rfl

theorem atot6279 : totK PA10K2 A10K2.u6279 = [89269993054, 980750978093, 3098861198761, 3786522023006, 1697921884918, 224967768341, 6121173289, 0, 0, 0] := by
  rw [show A10K2.u6279 = KTree.node A10K2.t6284 (nat_lit 105506477) (nat_lit 5485165328) (nat_lit 0) A10K2.t6285 from rfl, totK_node, tot6284, tot6285]
  decide +kernel

theorem arows6280 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6280 = true := by
  rw [show A10K2.u6280 = KTree.node A10K2.t6286 (nat_lit 105522441) (nat_lit 7579191422) (nat_lit 0) A10K2.t6287 from rfl, allE_node, rows6286, irow6280, rows6287]
  all_goals rfl

theorem atot6280 : totK PA10K2 A10K2.u6280 = [741367678625, 3071228326596, 3880262261036, 1557628089358, 188445892722, 5460492893, 0, 0, 0, 0] := by
  rw [show A10K2.u6280 = KTree.node A10K2.t6286 (nat_lit 105522441) (nat_lit 7579191422) (nat_lit 0) A10K2.t6287 from rfl, totK_node, tot6286, tot6287]
  decide +kernel

theorem arows6284 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6284 = true := by
  rw [show A10K2.u6284 = KTree.node A10K2.t6288 (nat_lit 105527122) (nat_lit 14635750634) (nat_lit 0) A10K2.t6289 from rfl, allE_node, rows6288, irow6284, rows6289]
  all_goals rfl

theorem atot6284 : totK PA10K2 A10K2.u6284 = [391370401505, 1999472956794, 3855584007876, 2962940859898, 633403270190, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u6284 = KTree.node A10K2.t6288 (nat_lit 105527122) (nat_lit 14635750634) (nat_lit 0) A10K2.t6289 from rfl, totK_node, tot6288, tot6289]
  decide +kernel

theorem arows6285 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6285 = true := by
  rw [show A10K2.u6285 = KTree.node A10K2.t6290 (nat_lit 105531624) (nat_lit 7385295154) (nat_lit 0) A10K2.t6291 from rfl, allE_node, rows6290, irow6285, rows6291]
  all_goals rfl

theorem atot6285 : totK PA10K2 A10K2.u6285 = [571469793363, 2906203627990, 4138191681524, 1676755571357, 139105659938, 0, 0, 0, 0, 0] := by
  rw [show A10K2.u6285 = KTree.node A10K2.t6290 (nat_lit 105531624) (nat_lit 7385295154) (nat_lit 0) A10K2.t6291 from rfl, totK_node, tot6290, tot6291]
  decide +kernel

theorem arows6287 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6287 = true := by
  rw [show A10K2.u6287 = KTree.node A10K2.t6292 (nat_lit 105555173) (nat_lit 6962782954) (nat_lit 0) A10K2.t6293 from rfl, allE_node, rows6292, irow6287, rows6293]
  all_goals rfl

theorem atot6287 : totK PA10K2 A10K2.u6287 = [0, 963178665689, 3740142706213, 3766723210904, 900512848864, 38825421397, 0, 0, 0, 0] := by
  rw [show A10K2.u6287 = KTree.node A10K2.t6292 (nat_lit 105555173) (nat_lit 6962782954) (nat_lit 0) A10K2.t6293 from rfl, totK_node, tot6292, tot6293]
  decide +kernel

theorem arows6288 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6288 = true := by
  rw [show A10K2.u6288 = KTree.node A10K2.t6294 (nat_lit 105563428) (nat_lit 13973624068) (nat_lit 0) A10K2.t6295 from rfl, allE_node, rows6294, irow6288, rows6295]
  all_goals rfl

theorem atot6288 : totK PA10K2 A10K2.u6288 = [0, 959042129709, 3557534972001, 3891001499798, 1112078337249, 69851553646, 0, 0, 0, 0] := by
  rw [show A10K2.u6288 = KTree.node A10K2.t6294 (nat_lit 105563428) (nat_lit 13973624068) (nat_lit 0) A10K2.t6295 from rfl, totK_node, tot6294, tot6295]
  decide +kernel

theorem arows6291 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6291 = true := by
  rw [show A10K2.u6291 = KTree.node A10K2.t6296 (nat_lit 105578552) (nat_lit 14915533968) (nat_lit 0) A10K2.t6297 from rfl, allE_node, rows6296, irow6291, rows6297]
  all_goals rfl

theorem atot6291 : totK PA10K2 A10K2.u6291 = [511028321977, 1910108371845, 2842994916849, 2778511956806, 1467057348015, 259417048368, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u6291 = KTree.node A10K2.t6296 (nat_lit 105578552) (nat_lit 14915533968) (nat_lit 0) A10K2.t6297 from rfl, totK_node, tot6296, tot6297]
  decide +kernel

theorem arows6292 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6292 = true := by
  rw [show A10K2.u6292 = KTree.node A10K2.t6298 (nat_lit 105588180) (nat_lit 8971410487) (nat_lit 0) A10K2.t6299 from rfl, allE_node, rows6298, irow6292, rows6299]
  all_goals rfl

theorem atot6292 : totK PA10K2 A10K2.u6292 = [813214446787, 3120712712514, 3934020561372, 1862104917367, 308892733719, 19398939937, 0, 0, 0, 0] := by
  rw [show A10K2.u6292 = KTree.node A10K2.t6298 (nat_lit 105588180) (nat_lit 8971410487) (nat_lit 0) A10K2.t6299 from rfl, totK_node, tot6298, tot6299]
  decide +kernel

theorem arows6294 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6294 = true := by
  rw [show A10K2.u6294 = KTree.node A10K2.t6300 (nat_lit 105593000) (nat_lit 7290952342) (nat_lit 0) A10K2.t6301 from rfl, allE_node, rows6300, irow6294, rows6301]
  all_goals rfl

theorem atot6294 : totK PA10K2 A10K2.u6294 = [232865494112, 1878720600039, 4169340432622, 3012379750455, 620860573348, 31747192500, 0, 0, 0, 0] := by
  rw [show A10K2.u6294 = KTree.node A10K2.t6300 (nat_lit 105593000) (nat_lit 7290952342) (nat_lit 0) A10K2.t6301 from rfl, totK_node, tot6300, tot6301]
  decide +kernel

theorem arows6295 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6295 = true := by
  rw [show A10K2.u6295 = KTree.node A10K2.t6302 (nat_lit 105606599) (nat_lit 14506771514) (nat_lit 0) A10K2.t6303 from rfl, allE_node, rows6302, irow6295, rows6303]
  all_goals rfl

theorem atot6295 : totK PA10K2 A10K2.u6295 = [613328696870, 2799332926225, 4166976867941, 2157455940576, 319138085404, 6853348008, 0, 0, 0, 0] := by
  rw [show A10K2.u6295 = KTree.node A10K2.t6302 (nat_lit 105606599) (nat_lit 14506771514) (nat_lit 0) A10K2.t6303 from rfl, totK_node, tot6302, tot6303]
  decide +kernel

theorem arows6300 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6300 = true := by
  rw [show A10K2.u6300 = KTree.node A10K2.t6304 (nat_lit 105611219) (nat_lit 8615230461) (nat_lit 0) A10K2.t6305 from rfl, allE_node, rows6304, irow6300, rows6305]
  all_goals rfl

theorem atot6300 : totK PA10K2 A10K2.u6300 = [0, 946038880791, 3664922686306, 4189092424403, 1346607935713, 88495188222, 0, 0, 0, 0] := by
  rw [show A10K2.u6300 = KTree.node A10K2.t6304 (nat_lit 105611219) (nat_lit 8615230461) (nat_lit 0) A10K2.t6305 from rfl, totK_node, tot6304, tot6305]
  decide +kernel

theorem arows6301 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6301 = true := by
  rw [show A10K2.u6301 = KTree.node A10K2.t6306 (nat_lit 105620844) (nat_lit 11364072303) (nat_lit 0) A10K2.t6307 from rfl, allE_node, rows6306, irow6301, rows6307]
  all_goals rfl

theorem atot6301 : totK PA10K2 A10K2.u6301 = [0, 728531022364, 2924596002557, 3977920527598, 2038200020107, 319027180691, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u6301 = KTree.node A10K2.t6306 (nat_lit 105620844) (nat_lit 11364072303) (nat_lit 0) A10K2.t6307 from rfl, totK_node, tot6306, tot6307]
  decide +kernel

theorem arows6303 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6303 = true := by
  rw [show A10K2.u6303 = KTree.node A10K2.t6308 (nat_lit 105625754) (nat_lit 14947507181) (nat_lit 0) A10K2.t6309 from rfl, allE_node, rows6308, irow6303, rows6309]
  all_goals rfl

theorem atot6303 : totK PA10K2 A10K2.u6303 = [0, 428472786932, 2444556293285, 4298185194617, 2483828128699, 345175281893, 7047025452, 0, 0, 0] := by
  rw [show A10K2.u6303 = KTree.node A10K2.t6308 (nat_lit 105625754) (nat_lit 14947507181) (nat_lit 0) A10K2.t6309 from rfl, totK_node, tot6308, tot6309]
  decide +kernel

theorem arows6304 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6304 = true := by
  rw [show A10K2.u6304 = KTree.node A10K2.t6310 (nat_lit 105639603) (nat_lit 9971149180) (nat_lit 0) A10K2.t6311 from rfl, allE_node, rows6310, irow6304, rows6311]
  all_goals rfl

theorem atot6304 : totK PA10K2 A10K2.u6304 = [0, 501550152162, 2562864039480, 4171835518572, 2413524745236, 353268310869, 6066958478, 0, 0, 0] := by
  rw [show A10K2.u6304 = KTree.node A10K2.t6310 (nat_lit 105639603) (nat_lit 9971149180) (nat_lit 0) A10K2.t6311 from rfl, totK_node, tot6310, tot6311]
  decide +kernel

theorem arows6307 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6307 = true := by
  rw [show A10K2.u6307 = KTree.node A10K2.t6312 (nat_lit 105719108) (nat_lit 12012408643) (nat_lit 0) A10K2.t6313 from rfl, allE_node, rows6312, irow6307, rows6313]
  all_goals rfl

theorem atot6307 : totK PA10K2 A10K2.u6307 = [0, 643977616791, 2553145353588, 3551515079783, 2212571587326, 658211886091, 55043167628, 0, 0, 0] := by
  rw [show A10K2.u6307 = KTree.node A10K2.t6312 (nat_lit 105719108) (nat_lit 12012408643) (nat_lit 0) A10K2.t6313 from rfl, totK_node, tot6312, tot6313]
  decide +kernel

theorem arows6308 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6308 = true := by
  rw [show A10K2.u6308 = KTree.node A10K2.t6314 (nat_lit 105723583) (nat_lit 9560490173) (nat_lit 0) A10K2.t6315 from rfl, allE_node, rows6314, irow6308, rows6315]
  all_goals rfl

theorem atot6308 : totK PA10K2 A10K2.u6308 = [0, 225772793739, 1800778283609, 4086080399013, 3001693050820, 595315292134, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u6308 = KTree.node A10K2.t6314 (nat_lit 105723583) (nat_lit 9560490173) (nat_lit 0) A10K2.t6315 from rfl, totK_node, tot6314, tot6315]
  decide +kernel

theorem arows6310 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6310 = true := by
  rw [show A10K2.u6310 = KTree.node A10K2.t6316 (nat_lit 105728156) (nat_lit 11901295526) (nat_lit 0) A10K2.t6317 from rfl, allE_node, rows6316, irow6310, rows6317]
  all_goals rfl

theorem atot6310 : totK PA10K2 A10K2.u6310 = [0, 682957551718, 2998637625340, 3904519150141, 1478801378799, 114903757198, 0, 0, 0, 0] := by
  rw [show A10K2.u6310 = KTree.node A10K2.t6316 (nat_lit 105728156) (nat_lit 11901295526) (nat_lit 0) A10K2.t6317 from rfl, totK_node, tot6316, tot6317]
  decide +kernel

theorem arows6311 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6311 = true := by
  rw [show A10K2.u6311 = KTree.node A10K2.t6318 (nat_lit 105735617) (nat_lit 7180615671) (nat_lit 0) A10K2.t6319 from rfl, allE_node, rows6318, irow6311, rows6319]
  all_goals rfl

theorem atot6311 : totK PA10K2 A10K2.u6311 = [0, 787390431162, 3068505387892, 4002836627342, 1817920622189, 220671823721, 6239673734, 0, 0, 0] := by
  rw [show A10K2.u6311 = KTree.node A10K2.t6318 (nat_lit 105735617) (nat_lit 7180615671) (nat_lit 0) A10K2.t6319 from rfl, totK_node, tot6318, tot6319]
  decide +kernel

theorem arows6315 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6315 = true := by
  rw [show A10K2.u6315 = KTree.node A10K2.t6320 (nat_lit 105741539) (nat_lit 10063070566) (nat_lit 0) A10K2.t6321 from rfl, allE_node, rows6320, irow6315, rows6321]
  all_goals rfl

theorem atot6315 : totK PA10K2 A10K2.u6315 = [0, 0, 1100518135729, 3913056339955, 3909024118889, 1060046423583, 61652055495, 0, 0, 0] := by
  rw [show A10K2.u6315 = KTree.node A10K2.t6320 (nat_lit 105741539) (nat_lit 10063070566) (nat_lit 0) A10K2.t6321 from rfl, totK_node, tot6320, tot6321]
  decide +kernel

theorem arows6316 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6316 = true := by
  rw [show A10K2.u6316 = KTree.node A10K2.t6322 (nat_lit 105754323) (nat_lit 10602640485) (nat_lit 0) A10K2.t6323 from rfl, allE_node, rows6322, irow6316, rows6323]
  all_goals rfl

theorem atot6316 : totK PA10K2 A10K2.u6316 = [0, 0, 542272113780, 2594242916858, 3851894134555, 2030953611024, 403413724872, 25565504801, 0, 0] := by
  rw [show A10K2.u6316 = KTree.node A10K2.t6322 (nat_lit 105754323) (nat_lit 10602640485) (nat_lit 0) A10K2.t6323 from rfl, totK_node, tot6322, tot6323]
  decide +kernel

theorem arows6318 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6318 = true := by
  rw [show A10K2.u6318 = KTree.node A10K2.t6324 (nat_lit 105760147) (nat_lit 10746085219) (nat_lit 0) A10K2.t6325 from rfl, allE_node, rows6324, irow6318, rows6325]
  all_goals rfl

theorem atot6318 : totK PA10K2 A10K2.u6318 = [0, 0, 676681387359, 2864460967408, 3760452083643, 1554465744244, 201774221593, 5453062850, 0, 0] := by
  rw [show A10K2.u6318 = KTree.node A10K2.t6324 (nat_lit 105760147) (nat_lit 10746085219) (nat_lit 0) A10K2.t6325 from rfl, totK_node, tot6324, tot6325]
  decide +kernel

theorem arows6319 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6319 = true := by
  rw [show A10K2.u6319 = KTree.node A10K2.t6326 (nat_lit 105768084) (nat_lit 11503249504) (nat_lit 0) A10K2.t6327 from rfl, allE_node, rows6326, irow6319, rows6327]
  all_goals rfl

theorem atot6319 : totK PA10K2 A10K2.u6319 = [0, 0, 783613660093, 3045097020368, 3918126139454, 1712217797544, 213970209715, 5685526223, 0, 0] := by
  rw [show A10K2.u6319 = KTree.node A10K2.t6326 (nat_lit 105768084) (nat_lit 11503249504) (nat_lit 0) A10K2.t6327 from rfl, totK_node, tot6326, tot6327]
  decide +kernel

theorem arows6322 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6322 = true := by
  rw [show A10K2.u6322 = KTree.node A10K2.t6328 (nat_lit 105781933) (nat_lit 6166704642) (nat_lit 0) A10K2.t6329 from rfl, allE_node, rows6328, irow6322, rows6329]
  all_goals rfl

theorem atot6322 : totK PA10K2 A10K2.u6322 = [0, 830637671679, 2914273372657, 3475634735013, 1778561219445, 431849354176, 36736648791, 0, 0, 0] := by
  rw [show A10K2.u6322 = KTree.node A10K2.t6328 (nat_lit 105781933) (nat_lit 6166704642) (nat_lit 0) A10K2.t6329 from rfl, totK_node, tot6328, tot6329]
  decide +kernel

theorem arows6323 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6323 = true := by
  rw [show A10K2.u6323 = KTree.node A10K2.t6330 (nat_lit 105788870) (nat_lit 13302187486) (nat_lit 0) A10K2.t6331 from rfl, allE_node, rows6330, irow6323, rows6331]
  all_goals rfl

theorem atot6323 : totK PA10K2 A10K2.u6323 = [0, 219385222726, 1946614633740, 4126132742906, 2838462087187, 581980964191, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u6323 = KTree.node A10K2.t6330 (nat_lit 105788870) (nat_lit 13302187486) (nat_lit 0) A10K2.t6331 from rfl, totK_node, tot6330, tot6331]
  decide +kernel

theorem arows6325 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6325 = true := by
  rw [show A10K2.u6325 = KTree.node A10K2.t6332 (nat_lit 105793435) (nat_lit 9794878140) (nat_lit 0) A10K2.t6333 from rfl, allE_node, rows6332, irow6325, rows6333]
  all_goals rfl

theorem atot6325 : totK PA10K2 A10K2.u6325 = [0, 743454972142, 3079407581934, 3961092342085, 1566265737525, 134088694900, 0, 0, 0, 0] := by
  rw [show A10K2.u6325 = KTree.node A10K2.t6332 (nat_lit 105793435) (nat_lit 9794878140) (nat_lit 0) A10K2.t6333 from rfl, totK_node, tot6332, tot6333]
  decide +kernel

theorem arows6326 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6326 = true := by
  rw [show A10K2.u6326 = KTree.node A10K2.t6334 (nat_lit 105810593) (nat_lit 7628055136) (nat_lit 0) A10K2.t6335 from rfl, allE_node, rows6334, irow6326, rows6335]
  all_goals rfl

theorem atot6326 : totK PA10K2 A10K2.u6326 = [0, 0, 1183081781558, 3830096954699, 3473035304820, 787564579235, 38593611784, 0, 0, 0] := by
  rw [show A10K2.u6326 = KTree.node A10K2.t6334 (nat_lit 105810593) (nat_lit 7628055136) (nat_lit 0) A10K2.t6335 from rfl, totK_node, tot6334, tot6335]
  decide +kernel

theorem arows6332 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6332 = true := by
  rw [show A10K2.u6332 = KTree.node A10K2.t6336 (nat_lit 105825436) (nat_lit 11709940717) (nat_lit 0) A10K2.t6337 from rfl, allE_node, rows6336, irow6332, rows6337]
  all_goals rfl

theorem atot6332 : totK PA10K2 A10K2.u6332 = [0, 0, 958576674615, 3742483429091, 3876150483520, 899313815195, 44066702005, 0, 0, 0] := by
  rw [show A10K2.u6332 = KTree.node A10K2.t6336 (nat_lit 105825436) (nat_lit 11709940717) (nat_lit 0) A10K2.t6337 from rfl, totK_node, tot6336, tot6337]
  decide +kernel

theorem arows6333 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6333 = true := by
  rw [show A10K2.u6333 = KTree.node A10K2.t6338 (nat_lit 105831190) (nat_lit 5166114586) (nat_lit 0) A10K2.t6339 from rfl, allE_node, rows6338, irow6333, rows6339]
  all_goals rfl

theorem atot6333 : totK PA10K2 A10K2.u6333 = [0, 511028321977, 1802233625946, 2720918213964, 2920392357847, 1468579948595, 214649257949, 6239673734, 0, 0] := by
  rw [show A10K2.u6333 = KTree.node A10K2.t6338 (nat_lit 105831190) (nat_lit 5166114586) (nat_lit 0) A10K2.t6339 from rfl, totK_node, tot6338, tot6339]
  decide +kernel

theorem arows6335 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6335 = true := by
  rw [show A10K2.u6335 = KTree.node A10K2.t6340 (nat_lit 105850180) (nat_lit 10464976139) (nat_lit 0) A10K2.t6341 from rfl, allE_node, rows6340, irow6335, rows6341]
  all_goals rfl

theorem atot6335 : totK PA10K2 A10K2.u6335 = [0, 691713300961, 2906868666310, 4037725857050, 2054430803429, 320274751964, 7007974415, 0, 0, 0] := by
  rw [show A10K2.u6335 = KTree.node A10K2.t6340 (nat_lit 105850180) (nat_lit 10464976139) (nat_lit 0) A10K2.t6341 from rfl, totK_node, tot6340, tot6341]
  decide +kernel

theorem arows6336 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6336 = true := by
  rw [show A10K2.u6336 = KTree.node A10K2.t6342 (nat_lit 105854805) (nat_lit 6469832182) (nat_lit 0) A10K2.t6343 from rfl, allE_node, rows6342, irow6336, rows6343]
  all_goals rfl

theorem atot6336 : totK PA10K2 A10K2.u6336 = [0, 351263580851, 2014215501212, 3995940860079, 2914274734110, 611824605192, 31285368086, 0, 0, 0] := by
  rw [show A10K2.u6336 = KTree.node A10K2.t6342 (nat_lit 105854805) (nat_lit 6469832182) (nat_lit 0) A10K2.t6343 from rfl, totK_node, tot6342, tot6343]
  decide +kernel

theorem arows6339 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6339 = true := by
  rw [show A10K2.u6339 = KTree.node A10K2.t6344 (nat_lit 105868514) (nat_lit 13474369292) (nat_lit 0) A10K2.t6345 from rfl, allE_node, rows6344, irow6339, rows6345]
  all_goals rfl

theorem atot6339 : totK PA10K2 A10K2.u6339 = [0, 612405880273, 2885383677477, 4209129289537, 2053983935684, 283564808543, 6281495166, 0, 0, 0] := by
  rw [show A10K2.u6339 = KTree.node A10K2.t6344 (nat_lit 105868514) (nat_lit 13474369292) (nat_lit 0) A10K2.t6345 from rfl, totK_node, tot6344, tot6345]
  decide +kernel

theorem arows6340 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6340 = true := by
  rw [show A10K2.u6340 = KTree.node A10K2.t6346 (nat_lit 105873124) (nat_lit 4484271227) (nat_lit 0) A10K2.t6347 from rfl, allE_node, rows6346, irow6340, rows6347]
  all_goals rfl

theorem atot6340 : totK PA10K2 A10K2.u6340 = [506965099532, 1612968115968, 2046560450292, 2503440543633, 2426393443958, 775473206672, 56100664475, 0, 0, 0] := by
  rw [show A10K2.u6340 = KTree.node A10K2.t6346 (nat_lit 105873124) (nat_lit 4484271227) (nat_lit 0) A10K2.t6347 from rfl, totK_node, tot6346, tot6347]
  decide +kernel

theorem arows6342 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6342 = true := by
  rw [show A10K2.u6342 = KTree.node A10K2.t6348 (nat_lit 105985267) (nat_lit 10232086046) (nat_lit 0) A10K2.t6349 from rfl, allE_node, rows6348, irow6342, rows6349]
  all_goals rfl

theorem atot6342 : totK PA10K2 A10K2.u6342 = [335061730634, 2041564728950, 3918702477961, 2731502928732, 574710743437, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u6342 = KTree.node A10K2.t6348 (nat_lit 105985267) (nat_lit 10232086046) (nat_lit 0) A10K2.t6349 from rfl, totK_node, tot6348, tot6349]
  decide +kernel

theorem arows6343 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6343 = true := by
  rw [show A10K2.u6343 = KTree.node A10K2.t6350 (nat_lit 105989780) (nat_lit 12027339891) (nat_lit 0) A10K2.t6351 from rfl, allE_node, rows6350, irow6343, rows6351]
  all_goals rfl

theorem atot6343 : totK PA10K2 A10K2.u6343 = [750797585308, 3142542552319, 4003032910388, 1544377870019, 137148918739, 0, 0, 0, 0, 0] := by
  rw [show A10K2.u6343 = KTree.node A10K2.t6350 (nat_lit 105989780) (nat_lit 12027339891) (nat_lit 0) A10K2.t6351 from rfl, totK_node, tot6350, tot6351]
  decide +kernel

theorem arows6347 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6347 = true := by
  rw [show A10K2.u6347 = KTree.node A10K2.t6352 (nat_lit 105997590) (nat_lit 11949095168) (nat_lit 0) A10K2.t6353 from rfl, allE_node, rows6352, irow6347, rows6353]
  all_goals rfl

theorem atot6347 : totK PA10K2 A10K2.u6347 = [595155796918, 2738353178900, 4125024358753, 2115201188730, 288573826095, 6354482628, 0, 0, 0, 0] := by
  rw [show A10K2.u6347 = KTree.node A10K2.t6352 (nat_lit 105997590) (nat_lit 11949095168) (nat_lit 0) A10K2.t6353 from rfl, totK_node, tot6352, tot6353]
  decide +kernel

theorem arows6348 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6348 = true := by
  rw [show A10K2.u6348 = KTree.node A10K2.t6354 (nat_lit 106004081) (nat_lit 7298154564) (nat_lit 0) A10K2.t6355 from rfl, allE_node, rows6354, irow6348, rows6355]
  all_goals rfl

theorem atot6348 : totK PA10K2 A10K2.u6348 = [0, 1073100258462, 3780090112818, 3887461754600, 1182551945827, 82477091230, 0, 0, 0, 0] := by
  rw [show A10K2.u6348 = KTree.node A10K2.t6354 (nat_lit 106004081) (nat_lit 7298154564) (nat_lit 0) A10K2.t6355 from rfl, totK_node, tot6354, tot6355]
  decide +kernel

theorem arows6350 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6350 = true := by
  rw [show A10K2.u6350 = KTree.node A10K2.t6356 (nat_lit 106017968) (nat_lit 8129592631) (nat_lit 0) A10K2.t6357 from rfl, allE_node, rows6356, irow6350, rows6357]
  all_goals rfl

theorem atot6350 : totK PA10K2 A10K2.u6350 = [0, 375424038606, 2212940083894, 3999063433128, 2445487618707, 464834445411, 25565504801, 0, 0, 0] := by
  rw [show A10K2.u6350 = KTree.node A10K2.t6356 (nat_lit 106017968) (nat_lit 8129592631) (nat_lit 0) A10K2.t6357 from rfl, totK_node, tot6356, tot6357]
  decide +kernel

theorem arows6351 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6351 = true := by
  rw [show A10K2.u6351 = KTree.node A10K2.t6358 (nat_lit 106022564) (nat_lit 13206244922) (nat_lit 0) A10K2.t6359 from rfl, allE_node, rows6358, irow6351, rows6359]
  all_goals rfl

theorem atot6351 : totK PA10K2 A10K2.u6351 = [0, 750649439132, 3195840432087, 3946779439249, 1453099481596, 162750166191, 5517381808, 0, 0, 0] := by
  rw [show A10K2.u6351 = KTree.node A10K2.t6358 (nat_lit 106022564) (nat_lit 13206244922) (nat_lit 0) A10K2.t6359 from rfl, totK_node, tot6358, tot6359]
  decide +kernel

theorem arows6354 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6354 = true := by
  rw [show A10K2.u6354 = KTree.node A10K2.t6360 (nat_lit 106030436) (nat_lit 13162313993) (nat_lit 0) A10K2.t6361 from rfl, allE_node, rows6360, irow6354, rows6361]
  all_goals rfl

theorem atot6354 : totK PA10K2 A10K2.u6354 = [0, 592803555652, 2691723752796, 4151615276990, 2063715407146, 245940258148, 6121173289, 0, 0, 0] := by
  rw [show A10K2.u6354 = KTree.node A10K2.t6360 (nat_lit 106030436) (nat_lit 13162313993) (nat_lit 0) A10K2.t6361 from rfl, totK_node, tot6360, tot6361]
  decide +kernel

theorem arows6355 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6355 = true := by
  rw [show A10K2.u6355 = KTree.node A10K2.t6362 (nat_lit 106039968) (nat_lit 8723241862) (nat_lit 0) A10K2.t6363 from rfl, allE_node, rows6362, irow6355, rows6363]
  all_goals rfl

theorem atot6355 : totK PA10K2 A10K2.u6355 = [561156172308, 2597543351359, 3848662732143, 2068713535999, 482263811371, 57309079699, 0, 0, 0, 0] := by
  rw [show A10K2.u6355 = KTree.node A10K2.t6362 (nat_lit 106039968) (nat_lit 8723241862) (nat_lit 0) A10K2.t6363 from rfl, totK_node, tot6362, tot6363]
  decide +kernel

theorem arows6357 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6357 = true := by
  rw [show A10K2.u6357 = KTree.node A10K2.t6364 (nat_lit 106047716) (nat_lit 13490928517) (nat_lit 0) A10K2.t6365 from rfl, allE_node, rows6364, irow6357, rows6365]
  all_goals rfl

theorem atot6357 : totK PA10K2 A10K2.u6357 = [767148028666, 3063606802854, 3897973907057, 1742205977132, 227234575079, 5460492893, 0, 0, 0, 0] := by
  rw [show A10K2.u6357 = KTree.node A10K2.t6364 (nat_lit 106047716) (nat_lit 13490928517) (nat_lit 0) A10K2.t6365 from rfl, totK_node, tot6364, tot6365]
  decide +kernel

theorem arows6358 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6358 = true := by
  rw [show A10K2.u6358 = KTree.node A10K2.t6366 (nat_lit 106053015) (nat_lit 14261435481) (nat_lit 0) A10K2.t6367 from rfl, allE_node, rows6366, irow6358, rows6367]
  all_goals rfl

theorem atot6358 : totK PA10K2 A10K2.u6358 = [514073912822, 2207855065274, 3602938023298, 2575682012765, 591251569122, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u6358 = KTree.node A10K2.t6366 (nat_lit 106053015) (nat_lit 14261435481) (nat_lit 0) A10K2.t6367 from rfl, totK_node, tot6366, tot6367]
  decide +kernel

theorem arows6363 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6363 = true := by
  rw [show A10K2.u6363 = KTree.node A10K2.t6368 (nat_lit 106058177) (nat_lit 10144412804) (nat_lit 0) A10K2.t6369 from rfl, allE_node, rows6368, irow6363, rows6369]
  all_goals rfl

theorem atot6363 : totK PA10K2 A10K2.u6363 = [306750524226, 2205300757445, 4244438229532, 2346575494165, 314257329487, 6354482628, 0, 0, 0, 0] := by
  rw [show A10K2.u6363 = KTree.node A10K2.t6368 (nat_lit 106058177) (nat_lit 10144412804) (nat_lit 0) A10K2.t6369 from rfl, totK_node, tot6368, tot6369]
  decide +kernel

theorem arows6364 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6364 = true := by
  rw [show A10K2.u6364 = KTree.node A10K2.t6370 (nat_lit 106079394) (nat_lit 14523975480) (nat_lit 0) A10K2.t6371 from rfl, allE_node, rows6370, irow6364, rows6371]
  all_goals rfl

theorem atot6364 : totK PA10K2 A10K2.u6364 = [0, 1027328580372, 3738296011164, 3790374463753, 1000000342843, 58104211810, 0, 0, 0, 0] := by
  rw [show A10K2.u6364 = KTree.node A10K2.t6370 (nat_lit 106079394) (nat_lit 14523975480) (nat_lit 0) A10K2.t6371 from rfl, totK_node, tot6370, tot6371]
  decide +kernel

theorem arows6366 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6366 = true := by
  rw [show A10K2.u6366 = KTree.node A10K2.t6372 (nat_lit 106087575) (nat_lit 12046233374) (nat_lit 0) A10K2.t6373 from rfl, allE_node, rows6372, irow6366, rows6373]
  all_goals rfl

theorem atot6366 : totK PA10K2 A10K2.u6366 = [0, 1003126739580, 3639880600663, 3801869676146, 1023532875111, 63495312472, 0, 0, 0, 0] := by
  rw [show A10K2.u6366 = KTree.node A10K2.t6372 (nat_lit 106087575) (nat_lit 12046233374) (nat_lit 0) A10K2.t6373 from rfl, totK_node, tot6372, tot6373]
  decide +kernel

theorem arows6367 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6367 = true := by
  rw [show A10K2.u6367 = KTree.node A10K2.t6374 (nat_lit 106093100) (nat_lit 13000484332) (nat_lit 0) A10K2.t6375 from rfl, allE_node, rows6374, irow6367, rows6375]
  all_goals rfl

theorem atot6367 : totK PA10K2 A10K2.u6367 = [0, 479425261710, 2492651269117, 4109060770329, 2026450627642, 292264775799, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u6367 = KTree.node A10K2.t6374 (nat_lit 106093100) (nat_lit 13000484332) (nat_lit 0) A10K2.t6375 from rfl, totK_node, tot6374, tot6375]
  decide +kernel

theorem arows6370 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6370 = true := by
  rw [show A10K2.u6370 = KTree.node A10K2.t6376 (nat_lit 106247400) (nat_lit 5447554872) (nat_lit 0) A10K2.t6377 from rfl, allE_node, rows6376, irow6370, rows6377]
  all_goals rfl

theorem atot6370 : totK PA10K2 A10K2.u6370 = [0, 362601568456, 2069995855832, 3922669317461, 2674316686043, 537073034443, 25734533292, 0, 0, 0] := by
  rw [show A10K2.u6370 = KTree.node A10K2.t6376 (nat_lit 106247400) (nat_lit 5447554872) (nat_lit 0) A10K2.t6377 from rfl, totK_node, tot6376, tot6377]
  decide +kernel

theorem arows6371 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6371 = true := by
  rw [show A10K2.u6371 = KTree.node A10K2.t6378 (nat_lit 106251923) (nat_lit 10953714944) (nat_lit 0) A10K2.t6379 from rfl, allE_node, rows6378, irow6371, rows6379]
  all_goals rfl

theorem atot6371 : totK PA10K2 A10K2.u6371 = [0, 750797585308, 3150382136834, 3987179742985, 1507603016740, 127276141317, 5718040558, 0, 0, 0] := by
  rw [show A10K2.u6371 = KTree.node A10K2.t6378 (nat_lit 106251923) (nat_lit 10953714944) (nat_lit 0) A10K2.t6379 from rfl, totK_node, tot6378, tot6379]
  decide +kernel

theorem arows6373 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6373 = true := by
  rw [show A10K2.u6373 = KTree.node A10K2.t6380 (nat_lit 106259733) (nat_lit 6784375044) (nat_lit 0) A10K2.t6381 from rfl, allE_node, rows6380, irow6373, rows6381]
  all_goals rfl

theorem atot6373 : totK PA10K2 A10K2.u6373 = [0, 595155796918, 2722690370130, 4123067884288, 2100278250128, 287551502530, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u6373 = KTree.node A10K2.t6380 (nat_lit 106259733) (nat_lit 6784375044) (nat_lit 0) A10K2.t6381 from rfl, totK_node, tot6380, tot6381]
  decide +kernel

theorem arows6374 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6374 = true := by
  rw [show A10K2.u6374 = KTree.node A10K2.t6382 (nat_lit 106299457) (nat_lit 10414617741) (nat_lit 0) A10K2.t6383 from rfl, allE_node, rows6382, irow6374, rows6383]
  all_goals rfl

theorem atot6374 : totK PA10K2 A10K2.u6374 = [0, 560546078113, 2659704622661, 4121803749645, 2238767178547, 336100961705, 6962742351, 0, 0, 0] := by
  rw [show A10K2.u6374 = KTree.node A10K2.t6382 (nat_lit 106299457) (nat_lit 10414617741) (nat_lit 0) A10K2.t6383 from rfl, totK_node, tot6382, tot6383]
  decide +kernel

theorem arows6378 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6378 = true := by
  rw [show A10K2.u6378 = KTree.node A10K2.t6384 (nat_lit 106306326) (nat_lit 1718519945) (nat_lit 0) A10K2.t6385 from rfl, allE_node, rows6384, irow6378, rows6385]
  all_goals rfl

theorem atot6378 : totK PA10K2 A10K2.u6378 = [0, 580247490663, 2389794015644, 3634318981725, 2296435313085, 464993782408, 30074883546, 0, 0, 0] := by
  rw [show A10K2.u6378 = KTree.node A10K2.t6384 (nat_lit 106306326) (nat_lit 1718519945) (nat_lit 0) A10K2.t6385 from rfl, totK_node, tot6384, tot6385]
  decide +kernel

theorem arows6379 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6379 = true := by
  rw [show A10K2.u6379 = KTree.node A10K2.t6386 (nat_lit 106313431) (nat_lit 6163098359) (nat_lit 0) A10K2.t6387 from rfl, allE_node, rows6386, irow6379, rows6387]
  all_goals rfl

theorem atot6379 : totK PA10K2 A10K2.u6379 = [0, 288246241244, 1985040822849, 4086716341786, 2662420602162, 494336851563, 31003444686, 0, 0, 0] := by
  rw [show A10K2.u6379 = KTree.node A10K2.t6386 (nat_lit 106313431) (nat_lit 6163098359) (nat_lit 0) A10K2.t6387 from rfl, totK_node, tot6386, tot6387]
  decide +kernel

theorem arows6381 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6381 = true := by
  rw [show A10K2.u6381 = KTree.node A10K2.t6388 (nat_lit 106317859) (nat_lit 8602567093) (nat_lit 0) A10K2.t6389 from rfl, allE_node, rows6388, irow6381, rows6389]
  all_goals rfl

theorem atot6381 : totK PA10K2 A10K2.u6381 = [0, 717479327981, 3160175250304, 4018236262909, 1402031376134, 111870674773, 0, 0, 0, 0] := by
  rw [show A10K2.u6381 = KTree.node A10K2.t6388 (nat_lit 106317859) (nat_lit 8602567093) (nat_lit 0) A10K2.t6389 from rfl, totK_node, tot6388, tot6389]
  decide +kernel

theorem arows6382 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6382 = true := by
  rw [show A10K2.u6382 = KTree.node A10K2.t6390 (nat_lit 106332704) (nat_lit 14306278529) (nat_lit 0) A10K2.t6391 from rfl, allE_node, rows6390, irow6382, rows6391]
  all_goals rfl

theorem atot6382 : totK PA10K2 A10K2.u6382 = [0, 0, 1183086810404, 3951385393644, 3448218862266, 748124785033, 37547833973, 0, 0, 0] := by
  rw [show A10K2.u6382 = KTree.node A10K2.t6390 (nat_lit 106332704) (nat_lit 14306278529) (nat_lit 0) A10K2.t6391 from rfl, totK_node, tot6390, tot6391]
  decide +kernel

theorem arows6385 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6385 = true := by
  rw [show A10K2.u6385 = KTree.node A10K2.t6392 (nat_lit 106343837) (nat_lit 2983481776) (nat_lit 0) A10K2.t6393 from rfl, allE_node, rows6392, irow6385, rows6393]
  all_goals rfl

theorem atot6385 : totK PA10K2 A10K2.u6385 = [0, 0, 1010474984531, 3638135483931, 3589382585180, 946134290151, 75896363801, 0, 0, 0] := by
  rw [show A10K2.u6385 = KTree.node A10K2.t6392 (nat_lit 106343837) (nat_lit 2983481776) (nat_lit 0) A10K2.t6393 from rfl, totK_node, tot6392, tot6393]
  decide +kernel

theorem arows6386 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6386 = true := by
  rw [show A10K2.u6386 = KTree.node A10K2.t6394 (nat_lit 106353877) (nat_lit 6282441788) (nat_lit 0) A10K2.t6395 from rfl, allE_node, rows6394, irow6386, rows6395]
  all_goals rfl

theorem atot6386 : totK PA10K2 A10K2.u6386 = [303494667383, 698722476234, 635722768212, 2024945503262, 3478564240255, 1766036357794, 271518366089, 6354482628, 0, 0] := by
  rw [show A10K2.u6386 = KTree.node A10K2.t6394 (nat_lit 106353877) (nat_lit 6282441788) (nat_lit 0) A10K2.t6395 from rfl, totK_node, tot6394, tot6395]
  decide +kernel

theorem arows6388 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6388 = true := by
  rw [show A10K2.u6388 = KTree.node A10K2.t6396 (nat_lit 106434060) (nat_lit 10071444864) (nat_lit 0) A10K2.t6397 from rfl, allE_node, rows6396, irow6388, rows6397]
  all_goals rfl

theorem atot6388 : totK PA10K2 A10K2.u6388 = [473115181482, 2531647691754, 4153015069960, 2285203315062, 433515487553, 25371180993, 0, 0, 0, 0] := by
  rw [show A10K2.u6388 = KTree.node A10K2.t6396 (nat_lit 106434060) (nat_lit 10071444864) (nat_lit 0) A10K2.t6397 from rfl, totK_node, tot6396, tot6397]
  decide +kernel

theorem arows6389 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6389 = true := by
  rw [show A10K2.u6389 = KTree.node A10K2.t6398 (nat_lit 106455844) (nat_lit 9218053696) (nat_lit 0) A10K2.t6399 from rfl, allE_node, rows6398, irow6389, rows6399]
  all_goals rfl

theorem atot6389 : totK PA10K2 A10K2.u6389 = [826090609103, 3257143219911, 4130375498238, 1786422139996, 227769256425, 5460492893, 0, 0, 0, 0] := by
  rw [show A10K2.u6389 = KTree.node A10K2.t6398 (nat_lit 106455844) (nat_lit 9218053696) (nat_lit 0) A10K2.t6399 from rfl, totK_node, tot6398, tot6399]
  decide +kernel

theorem arows6397 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6397 = true := by
  rw [show A10K2.u6397 = KTree.node A10K2.t6400 (nat_lit 106460850) (nat_lit 15081657858) (nat_lit 0) A10K2.t6401 from rfl, allE_node, rows6400, irow6397, rows6401]
  all_goals rfl

theorem atot6397 : totK PA10K2 A10K2.u6397 = [0, 1170897950791, 3992112466157, 3924339623730, 1073029525446, 62979767238, 0, 0, 0, 0] := by
  rw [show A10K2.u6397 = KTree.node A10K2.t6400 (nat_lit 106460850) (nat_lit 15081657858) (nat_lit 0) A10K2.t6401 from rfl, totK_node, tot6400, tot6401]
  decide +kernel

theorem arows6398 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6398 = true := by
  rw [show A10K2.u6398 = KTree.node A10K2.t6402 (nat_lit 106466757) (nat_lit 4412895567) (nat_lit 0) A10K2.t6403 from rfl, allE_node, rows6402, irow6398, rows6403]
  all_goals rfl

theorem atot6398 : totK PA10K2 A10K2.u6398 = [0, 580747034572, 2732386429082, 4054402383080, 2017333140788, 396698968407, 25239774317, 0, 0, 0] := by
  rw [show A10K2.u6398 = KTree.node A10K2.t6402 (nat_lit 106466757) (nat_lit 4412895567) (nat_lit 0) A10K2.t6403 from rfl, totK_node, tot6402, tot6403]
  decide +kernel

theorem arows6400 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6400 = true := by
  rw [show A10K2.u6400 = KTree.node A10K2.t6404 (nat_lit 106488712) (nat_lit 14204873071) (nat_lit 0) A10K2.t6405 from rfl, allE_node, rows6404, irow6400, rows6405]
  all_goals rfl

theorem atot6400 : totK PA10K2 A10K2.u6400 = [0, 825712571293, 3300547754955, 4142957943243, 1687126749466, 198159169255, 5410721913, 0, 0, 0] := by
  rw [show A10K2.u6400 = KTree.node A10K2.t6404 (nat_lit 106488712) (nat_lit 14204873071) (nat_lit 0) A10K2.t6405 from rfl, totK_node, tot6404, tot6405]
  decide +kernel

theorem arows6401 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6401 = true := by
  rw [show A10K2.u6401 = KTree.node A10K2.t6406 (nat_lit 106506560) (nat_lit 3941174735) (nat_lit 0) A10K2.t6407 from rfl, allE_node, rows6406, irow6401, rows6407]
  all_goals rfl

theorem atot6401 : totK PA10K2 A10K2.u6401 = [838891203471, 3208340158623, 3789026273361, 1610161047216, 337115480906, 37674914273, 0, 0, 0, 0] := by
  rw [show A10K2.u6401 = KTree.node A10K2.t6406 (nat_lit 106506560) (nat_lit 3941174735) (nat_lit 0) A10K2.t6407 from rfl, totK_node, tot6406, tot6407]
  decide +kernel

theorem arows6404 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6404 = true := by
  rw [show A10K2.u6404 = KTree.node A10K2.t6408 (nat_lit 106511438) (nat_lit 10865090002) (nat_lit 0) A10K2.t6409 from rfl, allE_node, rows6408, irow6404, rows6409]
  all_goals rfl

theorem atot6404 : totK PA10K2 A10K2.u6404 = [423713582285, 2082642326860, 3757057721778, 2703806168281, 587719147856, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u6404 = KTree.node A10K2.t6408 (nat_lit 106511438) (nat_lit 10865090002) (nat_lit 0) A10K2.t6409 from rfl, totK_node, tot6408, tot6409]
  decide +kernel

theorem arows6405 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6405 = true := by
  rw [show A10K2.u6405 = KTree.node A10K2.t6410 (nat_lit 106519308) (nat_lit 11865991505) (nat_lit 0) A10K2.t6411 from rfl, allE_node, rows6410, irow6405, rows6411]
  all_goals rfl

theorem atot6405 : totK PA10K2 A10K2.u6405 = [601038090043, 2788467979185, 4085791273439, 1912349356006, 259120632233, 6354482628, 0, 0, 0, 0] := by
  rw [show A10K2.u6405 = KTree.node A10K2.t6410 (nat_lit 106519308) (nat_lit 11865991505) (nat_lit 0) A10K2.t6411 from rfl, totK_node, tot6410, tot6411]
  decide +kernel

theorem arows6407 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6407 = true := by
  rw [show A10K2.u6407 = KTree.node A10K2.t6412 (nat_lit 106525232) (nat_lit 14935466441) (nat_lit 0) A10K2.t6413 from rfl, allE_node, rows6412, irow6407, rows6413]
  all_goals rfl

theorem atot6407 : totK PA10K2 A10K2.u6407 = [319364795913, 2093664988305, 4293474217280, 3050537629878, 554864522914, 13814447077, 0, 0, 0, 0] := by
  rw [show A10K2.u6407 = KTree.node A10K2.t6412 (nat_lit 106525232) (nat_lit 14935466441) (nat_lit 0) A10K2.t6413 from rfl, totK_node, tot6412, tot6413]
  decide +kernel

theorem arows6408 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6408 = true := by
  rw [show A10K2.u6408 = KTree.node A10K2.t6414 (nat_lit 106539106) (nat_lit 9184479568) (nat_lit 0) A10K2.t6415 from rfl, allE_node, rows6414, irow6408, rows6415]
  all_goals rfl

theorem atot6408 : totK PA10K2 A10K2.u6408 = [0, 837802765007, 3381348105358, 4079911999591, 1361721304592, 88560907151, 0, 0, 0, 0] := by
  rw [show A10K2.u6408 = KTree.node A10K2.t6414 (nat_lit 106539106) (nat_lit 9184479568) (nat_lit 0) A10K2.t6415 from rfl, totK_node, tot6414, tot6415]
  decide +kernel

theorem arows6412 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6412 = true := by
  rw [show A10K2.u6412 = KTree.node A10K2.t6416 (nat_lit 106543795) (nat_lit 10137860900) (nat_lit 0) A10K2.t6417 from rfl, allE_node, rows6416, irow6412, rows6417]
  all_goals rfl

theorem atot6412 : totK PA10K2 A10K2.u6412 = [0, 320620677522, 1918472661886, 3810357928378, 2752179904294, 591117923729, 31082886609, 0, 0, 0] := by
  rw [show A10K2.u6412 = KTree.node A10K2.t6416 (nat_lit 106543795) (nat_lit 10137860900) (nat_lit 0) A10K2.t6417 from rfl, totK_node, tot6416, tot6417]
  decide +kernel

theorem arows6413 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6413 = true := by
  rw [show A10K2.u6413 = KTree.node A10K2.t6418 (nat_lit 106551639) (nat_lit 4550303317) (nat_lit 0) A10K2.t6419 from rfl, allE_node, rows6418, irow6413, rows6419]
  all_goals rfl

theorem atot6413 : totK PA10K2 A10K2.u6413 = [0, 703049958652, 2979026236195, 3973817351890, 1727665475325, 224376201608, 6121173289, 0, 0, 0] := by
  rw [show A10K2.u6413 = KTree.node A10K2.t6418 (nat_lit 106551639) (nat_lit 4550303317) (nat_lit 0) A10K2.t6419 from rfl, totK_node, tot6418, tot6419]
  decide +kernel

theorem arows6415 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6415 = true := by
  rw [show A10K2.u6415 = KTree.node A10K2.t6420 (nat_lit 106627341) (nat_lit 5675375080) (nat_lit 0) A10K2.t6421 from rfl, allE_node, rows6420, irow6415, rows6421]
  all_goals rfl

theorem atot6415 : totK PA10K2 A10K2.u6415 = [682871898056, 2628198809522, 3570618419275, 2394908170108, 790962938165, 61190578067, 0, 0, 0, 0] := by
  rw [show A10K2.u6415 = KTree.node A10K2.t6420 (nat_lit 106627341) (nat_lit 5675375080) (nat_lit 0) A10K2.t6421 from rfl, totK_node, tot6420, tot6421]
  decide +kernel

theorem arows6416 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6416 = true := by
  rw [show A10K2.u6416 = KTree.node A10K2.t6422 (nat_lit 106634303) (nat_lit 14140654769) (nat_lit 0) A10K2.t6423 from rfl, allE_node, rows6422, irow6416, rows6423]
  all_goals rfl

theorem atot6416 : totK PA10K2 A10K2.u6416 = [404541561496, 2265672275143, 4134657525548, 2634064512147, 482183011685, 24527926574, 0, 0, 0, 0] := by
  rw [show A10K2.u6416 = KTree.node A10K2.t6422 (nat_lit 106634303) (nat_lit 14140654769) (nat_lit 0) A10K2.t6423 from rfl, totK_node, tot6422, tot6423]
  decide +kernel

theorem arows6419 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6419 = true := by
  rw [show A10K2.u6419 = KTree.node A10K2.t6424 (nat_lit 106640630) (nat_lit 15766524011) (nat_lit 0) A10K2.t6425 from rfl, allE_node, rows6424, irow6419, rows6425]
  all_goals rfl

theorem atot6419 : totK PA10K2 A10K2.u6419 = [376643207835, 2144534021630, 4019079310127, 2705830377157, 562118197879, 31677228370, 0, 0, 0, 0] := by
  rw [show A10K2.u6419 = KTree.node A10K2.t6424 (nat_lit 106640630) (nat_lit 15766524011) (nat_lit 0) A10K2.t6425 from rfl, totK_node, tot6424, tot6425]
  decide +kernel

theorem arows6420 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6420 = true := by
  rw [show A10K2.u6420 = KTree.node A10K2.t6426 (nat_lit 106653335) (nat_lit 13435479642) (nat_lit 0) A10K2.t6427 from rfl, allE_node, rows6426, irow6420, rows6427]
  all_goals rfl

theorem atot6420 : totK PA10K2 A10K2.u6420 = [883146858471, 3431965737863, 4083348664981, 1502202331206, 134017886798, 0, 0, 0, 0, 0] := by
  rw [show A10K2.u6420 = KTree.node A10K2.t6426 (nat_lit 106653335) (nat_lit 13435479642) (nat_lit 0) A10K2.t6427 from rfl, totK_node, tot6426, tot6427]
  decide +kernel

theorem arows6422 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6422 = true := by
  rw [show A10K2.u6422 = KTree.node A10K2.t6428 (nat_lit 106658852) (nat_lit 6115815816) (nat_lit 0) A10K2.t6429 from rfl, allE_node, rows6428, irow6422, rows6429]
  all_goals rfl

theorem atot6422 : totK PA10K2 A10K2.u6422 = [0, 1097368896824, 3908828609730, 3950180259263, 1079452179504, 62996513375, 0, 0, 0, 0] := by
  rw [show A10K2.u6422 = KTree.node A10K2.t6428 (nat_lit 106658852) (nat_lit 6115815816) (nat_lit 0) A10K2.t6429 from rfl, totK_node, tot6428, tot6429]
  decide +kernel

theorem arows6423 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6423 = true := by
  rw [show A10K2.u6423 = KTree.node A10K2.t6430 (nat_lit 106663884) (nat_lit 4035251865) (nat_lit 0) A10K2.t6431 from rfl, allE_node, rows6430, irow6423, rows6431]
  all_goals rfl

theorem atot6423 : totK PA10K2 A10K2.u6423 = [0, 446820255427, 2459580094950, 4323788575083, 2435907476975, 352227841274, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u6423 = KTree.node A10K2.t6430 (nat_lit 106663884) (nat_lit 4035251865) (nat_lit 0) A10K2.t6431 from rfl, totK_node, tot6430, tot6431]
  decide +kernel

theorem arows6428 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6428 = true := by
  rw [show A10K2.u6428 = KTree.node A10K2.t6432 (nat_lit 106671219) (nat_lit 6200441575) (nat_lit 0) A10K2.t6433 from rfl, allE_node, rows6432, irow6428, rows6433]
  all_goals rfl

theorem atot6428 : totK PA10K2 A10K2.u6428 = [0, 732940690101, 3086013634617, 4051029378997, 1793614373465, 200877366054, 0, 0, 0, 0] := by
  rw [show A10K2.u6428 = KTree.node A10K2.t6432 (nat_lit 106671219) (nat_lit 6200441575) (nat_lit 0) A10K2.t6433 from rfl, totK_node, tot6432, tot6433]
  decide +kernel

theorem arows6429 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6429 = true := by
  rw [show A10K2.u6429 = KTree.node A10K2.t6434 (nat_lit 106685036) (nat_lit 7560473117) (nat_lit 0) A10K2.t6435 from rfl, allE_node, rows6434, irow6429, rows6435]
  all_goals rfl

theorem atot6429 : totK PA10K2 A10K2.u6429 = [0, 881857600930, 3317819106606, 3950178422173, 1613289372792, 174771139087, 7047025452, 0, 0, 0] := by
  rw [show A10K2.u6429 = KTree.node A10K2.t6434 (nat_lit 106685036) (nat_lit 7560473117) (nat_lit 0) A10K2.t6435 from rfl, totK_node, tot6434, tot6435]
  decide +kernel

theorem arows6431 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6431 = true := by
  rw [show A10K2.u6431 = KTree.node A10K2.t6436 (nat_lit 106689811) (nat_lit 10631379043) (nat_lit 0) A10K2.t6437 from rfl, allE_node, rows6436, irow6431, rows6437]
  all_goals rfl

theorem atot6431 : totK PA10K2 A10K2.u6431 = [0, 0, 1258911122052, 4107484376381, 3719268403559, 813263820002, 23799715721, 0, 0, 0] := by
  rw [show A10K2.u6431 = KTree.node A10K2.t6436 (nat_lit 106689811) (nat_lit 10631379043) (nat_lit 0) A10K2.t6437 from rfl, totK_node, tot6436, tot6437]
  decide +kernel

theorem arows6432 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6432 = true := by
  rw [show A10K2.u6432 = KTree.node A10K2.t6438 (nat_lit 106695681) (nat_lit 10511097145) (nat_lit 0) A10K2.t6439 from rfl, allE_node, rows6438, irow6432, rows6439]
  all_goals rfl

theorem atot6432 : totK PA10K2 A10K2.u6432 = [0, 776110475293, 3141064153577, 4009516135766, 1698739225565, 290405460730, 37310410385, 0, 0, 0] := by
  rw [show A10K2.u6432 = KTree.node A10K2.t6438 (nat_lit 106695681) (nat_lit 10511097145) (nat_lit 0) A10K2.t6439 from rfl, totK_node, tot6438, tot6439]
  decide +kernel

theorem arows6435 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6435 = true := by
  rw [show A10K2.u6435 = KTree.node A10K2.t6440 (nat_lit 106717444) (nat_lit 10986630610) (nat_lit 0) A10K2.t6441 from rfl, allE_node, rows6440, irow6435, rows6441]
  all_goals rfl

theorem atot6435 : totK PA10K2 A10K2.u6435 = [0, 703445347323, 2734752920118, 3839542824255, 2222903027120, 497355881374, 30780440178, 0, 0, 0] := by
  rw [show A10K2.u6435 = KTree.node A10K2.t6440 (nat_lit 106717444) (nat_lit 10986630610) (nat_lit 0) A10K2.t6441 from rfl, totK_node, tot6440, tot6441]
  decide +kernel

theorem arows6436 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6436 = true := by
  rw [show A10K2.u6436 = KTree.node A10K2.t6442 (nat_lit 106722184) (nat_lit 14170549419) (nat_lit 0) A10K2.t6443 from rfl, allE_node, rows6442, irow6436, rows6443]
  all_goals rfl

theorem atot6436 : totK PA10K2 A10K2.u6436 = [0, 121142009141, 1576556404277, 4156765796889, 3585347997455, 808747149081, 25037009903, 0, 0, 0] := by
  rw [show A10K2.u6436 = KTree.node A10K2.t6442 (nat_lit 106722184) (nat_lit 14170549419) (nat_lit 0) A10K2.t6443 from rfl, totK_node, tot6442, tot6443]
  decide +kernel

theorem arows6438 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6438 = true := by
  rw [show A10K2.u6438 = KTree.node A10K2.t6444 (nat_lit 106728204) (nat_lit 11854907238) (nat_lit 0) A10K2.t6445 from rfl, allE_node, rows6444, irow6438, rows6445]
  all_goals rfl

theorem atot6438 : totK PA10K2 A10K2.u6438 = [0, 0, 775623392097, 3205336227370, 4092634593333, 1639000141354, 161311382414, 0, 0, 0] := by
  rw [show A10K2.u6438 = KTree.node A10K2.t6444 (nat_lit 106728204) (nat_lit 11854907238) (nat_lit 0) A10K2.t6445 from rfl, totK_node, tot6444, tot6445]
  decide +kernel

theorem arows6439 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6439 = true := by
  rw [show A10K2.u6439 = KTree.node A10K2.t6446 (nat_lit 106750512) (nat_lit 15034937939) (nat_lit 0) A10K2.t6447 from rfl, allE_node, rows6446, irow6439, rows6447]
  all_goals rfl

theorem atot6439 : totK PA10K2 A10K2.u6439 = [0, 0, 823838388709, 3271255843248, 4060064662667, 1681223001628, 229375291440, 7007974415, 0, 0] := by
  rw [show A10K2.u6439 = KTree.node A10K2.t6446 (nat_lit 106750512) (nat_lit 15034937939) (nat_lit 0) A10K2.t6447 from rfl, totK_node, tot6446, tot6447]
  decide +kernel

theorem arows6443 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6443 = true := by
  rw [show A10K2.u6443 = KTree.node A10K2.t6448 (nat_lit 106768598) (nat_lit 13334845768) (nat_lit 0) A10K2.t6449 from rfl, allE_node, rows6448, irow6443, rows6449]
  all_goals rfl

theorem atot6443 : totK PA10K2 A10K2.u6443 = [0, 838891203471, 3124121938023, 3652569271964, 1713436590511, 461050998090, 43720954405, 0, 0, 0] := by
  rw [show A10K2.u6443 = KTree.node A10K2.t6448 (nat_lit 106768598) (nat_lit 13334845768) (nat_lit 0) A10K2.t6449 from rfl, totK_node, tot6448, tot6449]
  decide +kernel

theorem arows6444 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6444 = true := by
  rw [show A10K2.u6444 = KTree.node A10K2.t6450 (nat_lit 106773285) (nat_lit 7443344059) (nat_lit 0) A10K2.t6451 from rfl, allE_node, rows6450, irow6444, rows6451]
  all_goals rfl

theorem atot6444 : totK PA10K2 A10K2.u6444 = [0, 321146256371, 1928564427919, 3840030551574, 2827583157455, 600313650983, 31306924438, 0, 0, 0] := by
  rw [show A10K2.u6444 = KTree.node A10K2.t6450 (nat_lit 106773285) (nat_lit 7443344059) (nat_lit 0) A10K2.t6451 from rfl, totK_node, tot6450, tot6451]
  decide +kernel

theorem arows6446 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6446 = true := by
  rw [show A10K2.u6446 = KTree.node A10K2.t6452 (nat_lit 106781032) (nat_lit 9385610620) (nat_lit 0) A10K2.t6453 from rfl, allE_node, rows6452, irow6446, rows6453]
  all_goals rfl

theorem atot6446 : totK PA10K2 A10K2.u6446 = [0, 703605415957, 2951492924527, 3998775999912, 1776337699734, 229721760521, 6239673734, 0, 0, 0] := by
  rw [show A10K2.u6446 = KTree.node A10K2.t6452 (nat_lit 106781032) (nat_lit 9385610620) (nat_lit 0) A10K2.t6453 from rfl, totK_node, tot6452, tot6453]
  decide +kernel

theorem arows6447 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6447 = true := by
  rw [show A10K2.u6447 = KTree.node A10K2.t6454 (nat_lit 106787259) (nat_lit 6404301529) (nat_lit 0) A10K2.t6455 from rfl, allE_node, rows6454, irow6447, rows6455]
  all_goals rfl

theorem atot6447 : totK PA10K2 A10K2.u6447 = [0, 319364795913, 2129397799309, 4285355648957, 2949554959862, 526551765434, 13242594235, 0, 0, 0] := by
  rw [show A10K2.u6447 = KTree.node A10K2.t6454 (nat_lit 106787259) (nat_lit 6404301529) (nat_lit 0) A10K2.t6455 from rfl, totK_node, tot6454, tot6455]
  decide +kernel

theorem arows6450 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6450 = true := by
  rw [show A10K2.u6450 = KTree.node A10K2.t6456 (nat_lit 106801025) (nat_lit 3556888547) (nat_lit 0) A10K2.t6457 from rfl, allE_node, rows6456, irow6450, rows6457]
  all_goals rfl

theorem atot6450 : totK PA10K2 A10K2.u6450 = [0, 0, 879703641024, 3475826376493, 4061549043548, 1319761811001, 87736822000, 0, 0, 0] := by
  rw [show A10K2.u6450 = KTree.node A10K2.t6456 (nat_lit 106801025) (nat_lit 3556888547) (nat_lit 0) A10K2.t6457 from rfl, totK_node, tot6456, tot6457]
  decide +kernel

theorem arows6451 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6451 = true := by
  rw [show A10K2.u6451 = KTree.node A10K2.t6458 (nat_lit 106806493) (nat_lit 3257930569) (nat_lit 0) A10K2.t6459 from rfl, allE_node, rows6458, irow6451, rows6459]
  all_goals rfl

theorem atot6451 : totK PA10K2 A10K2.u6451 = [0, 0, 615151998610, 2697963400646, 3882249389301, 2003783682604, 303295638102, 7151180950, 0, 0] := by
  rw [show A10K2.u6451 = KTree.node A10K2.t6458 (nat_lit 106806493) (nat_lit 3257930569) (nat_lit 0) A10K2.t6459 from rfl, totK_node, tot6458, tot6459]
  decide +kernel

theorem arows6453 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6453 = true := by
  rw [show A10K2.u6453 = KTree.node A10K2.t6460 (nat_lit 106818736) (nat_lit 11559648354) (nat_lit 0) A10K2.t6461 from rfl, allE_node, rows6460, irow6453, rows6461]
  all_goals rfl

theorem atot6453 : totK PA10K2 A10K2.u6453 = [0, 282573750534, 1626297811214, 3584653204116, 3469168624630, 1086702659879, 68947799775, 0, 0, 0] := by
  rw [show A10K2.u6453 = KTree.node A10K2.t6460 (nat_lit 106818736) (nat_lit 11559648354) (nat_lit 0) A10K2.t6461 from rfl, totK_node, tot6460, tot6461]
  decide +kernel

theorem arows6454 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6454 = true := by
  rw [show A10K2.u6454 = KTree.node A10K2.t6462 (nat_lit 106893374) (nat_lit 15375569526) (nat_lit 0) A10K2.t6463 from rfl, allE_node, rows6462, irow6454, rows6463]
  all_goals rfl

theorem atot6454 : totK PA10K2 A10K2.u6454 = [0, 473462086531, 2408343379735, 4197368473046, 2570854603816, 442803970543, 11991740650, 0, 0, 0] := by
  rw [show A10K2.u6454 = KTree.node A10K2.t6462 (nat_lit 106893374) (nat_lit 15375569526) (nat_lit 0) A10K2.t6463 from rfl, totK_node, tot6462, tot6463]
  decide +kernel

theorem arows6460 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6460 = true := by
  rw [show A10K2.u6460 = KTree.node A10K2.t6464 (nat_lit 106900662) (nat_lit 16422212901) (nat_lit 0) A10K2.t6465 from rfl, allE_node, rows6464, irow6460, rows6465]
  all_goals rfl

theorem atot6460 : totK PA10K2 A10K2.u6460 = [0, 697843148805, 3043525300441, 4023472861072, 1824020088071, 288339520157, 12219140272, 0, 0, 0] := by
  rw [show A10K2.u6460 = KTree.node A10K2.t6464 (nat_lit 106900662) (nat_lit 16422212901) (nat_lit 0) A10K2.t6465 from rfl, totK_node, tot6464, tot6465]
  decide +kernel

theorem arows6461 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6461 = true := by
  rw [show A10K2.u6461 = KTree.node A10K2.t6466 (nat_lit 106914254) (nat_lit 14728140744) (nat_lit 0) A10K2.t6467 from rfl, allE_node, rows6466, irow6461, rows6467]
  all_goals rfl

theorem atot6461 : totK PA10K2 A10K2.u6461 = [0, 759197198641, 2914755117330, 3947046852208, 2050425030892, 248980878518, 0, 0, 0, 0] := by
  rw [show A10K2.u6461 = KTree.node A10K2.t6466 (nat_lit 106914254) (nat_lit 14728140744) (nat_lit 0) A10K2.t6467 from rfl, totK_node, tot6466, tot6467]
  decide +kernel

theorem arows6463 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6463 = true := by
  rw [show A10K2.u6463 = KTree.node A10K2.t6468 (nat_lit 106918792) (nat_lit 14170549419) (nat_lit 0) A10K2.t6469 from rfl, allE_node, rows6468, irow6463, rows6469]
  all_goals rfl

theorem atot6463 : totK PA10K2 A10K2.u6463 = [0, 122956571035, 1672484904918, 4263699328838, 3362070050413, 644831573351, 19546091569, 0, 0, 0] := by
  rw [show A10K2.u6463 = KTree.node A10K2.t6468 (nat_lit 106918792) (nat_lit 14170549419) (nat_lit 0) A10K2.t6469 from rfl, totK_node, tot6468, tot6469]
  decide +kernel

theorem arows6464 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6464 = true := by
  rw [show A10K2.u6464 = KTree.node A10K2.t6470 (nat_lit 106925101) (nat_lit 2650957297) (nat_lit 0) A10K2.t6471 from rfl, allE_node, rows6470, irow6464, rows6471]
  all_goals rfl

theorem atot6464 : totK PA10K2 A10K2.u6464 = [0, 0, 680454974973, 2998688675047, 4233663271315, 1904753880710, 179054690532, 0, 0, 0] := by
  rw [show A10K2.u6464 = KTree.node A10K2.t6470 (nat_lit 106925101) (nat_lit 2650957297) (nat_lit 0) A10K2.t6471 from rfl, totK_node, tot6470, tot6471]
  decide +kernel

theorem arows6467 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6467 = true := by
  rw [show A10K2.u6467 = KTree.node A10K2.t6472 (nat_lit 106931995) (nat_lit 9981964682) (nat_lit 0) A10K2.t6473 from rfl, allE_node, rows6472, irow6467, rows6473]
  all_goals rfl

theorem atot6467 : totK PA10K2 A10K2.u6467 = [0, 0, 778246531629, 3155243862073, 4106670200414, 1716819380099, 182111583114, 6318667960, 0, 0] := by
  rw [show A10K2.u6467 = KTree.node A10K2.t6472 (nat_lit 106931995) (nat_lit 9981964682) (nat_lit 0) A10K2.t6473 from rfl, totK_node, tot6472, tot6473]
  decide +kernel

theorem arows6468 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6468 = true := by
  rw [show A10K2.u6468 = KTree.node A10K2.t6474 (nat_lit 106946609) (nat_lit 9972015927) (nat_lit 0) A10K2.t6475 from rfl, allE_node, rows6474, irow6468, rows6475]
  all_goals rfl

theorem atot6468 : totK PA10K2 A10K2.u6468 = [0, 0, 549057671383, 2741035706661, 4134569829051, 2090695714087, 274868461545, 6439430839, 0, 0] := by
  rw [show A10K2.u6468 = KTree.node A10K2.t6474 (nat_lit 106946609) (nat_lit 9972015927) (nat_lit 0) A10K2.t6475 from rfl, totK_node, tot6474, tot6475]
  decide +kernel

theorem arows6470 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6470 = true := by
  rw [show A10K2.u6470 = KTree.node A10K2.t6476 (nat_lit 106951131) (nat_lit 5817224638) (nat_lit 0) A10K2.t6477 from rfl, allE_node, rows6476, irow6470, rows6477]
  all_goals rfl

theorem atot6470 : totK PA10K2 A10K2.u6470 = [0, 0, 328041330167, 2084532386938, 4166751180049, 2772816434332, 459971349271, 12132367858, 0, 0] := by
  rw [show A10K2.u6470 = KTree.node A10K2.t6476 (nat_lit 106951131) (nat_lit 5817224638) (nat_lit 0) A10K2.t6477 from rfl, totK_node, tot6476, tot6477]
  decide +kernel

theorem arows6471 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6471 = true := by
  rw [show A10K2.u6471 = KTree.node A10K2.t6478 (nat_lit 107554711) (nat_lit 14220573112) (nat_lit 0) A10K2.t6479 from rfl, allE_node, rows6478, irow6471, rows6479]
  all_goals rfl

theorem atot6471 : totK PA10K2 A10K2.u6471 = [0, 872244600920, 3081350916724, 3082686061497, 1200519755828, 1026791783230, 501217979401, 48886019071, 0, 0] := by
  rw [show A10K2.u6471 = KTree.node A10K2.t6478 (nat_lit 107554711) (nat_lit 14220573112) (nat_lit 0) A10K2.t6479 from rfl, totK_node, tot6478, tot6479]
  decide +kernel

theorem arows6475 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6475 = true := by
  rw [show A10K2.u6475 = KTree.node A10K2.t6480 (nat_lit 107559180) (nat_lit 11813284965) (nat_lit 0) A10K2.t6481 from rfl, allE_node, rows6480, irow6475, rows6481]
  all_goals rfl

theorem atot6475 : totK PA10K2 A10K2.u6475 = [0, 231394348301, 1641909888398, 3852508433992, 3069684426151, 640625474878, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u6475 = KTree.node A10K2.t6480 (nat_lit 107559180) (nat_lit 11813284965) (nat_lit 0) A10K2.t6481 from rfl, totK_node, tot6480, tot6481]
  decide +kernel

theorem arows6476 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6476 = true := by
  rw [show A10K2.u6476 = KTree.node A10K2.t6482 (nat_lit 107563811) (nat_lit 9851281029) (nat_lit 0) A10K2.t6483 from rfl, allE_node, rows6482, irow6476, rows6483]
  all_goals rfl

theorem atot6476 : totK PA10K2 A10K2.u6476 = [0, 452227343263, 2505767469395, 4101689876257, 1954787501368, 174841463708, 0, 0, 0, 0] := by
  rw [show A10K2.u6476 = KTree.node A10K2.t6482 (nat_lit 107563811) (nat_lit 9851281029) (nat_lit 0) A10K2.t6483 from rfl, totK_node, tot6482, tot6483]
  decide +kernel

theorem arows6478 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6478 = true := by
  rw [show A10K2.u6478 = KTree.node A10K2.t6484 (nat_lit 107572278) (nat_lit 16595278098) (nat_lit 0) A10K2.t6485 from rfl, allE_node, rows6484, irow6478, rows6485]
  all_goals rfl

theorem atot6478 : totK PA10K2 A10K2.u6478 = [0, 788312884667, 3151535638513, 4038724250335, 1922838205935, 311918148049, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u6478 = KTree.node A10K2.t6484 (nat_lit 107572278) (nat_lit 16595278098) (nat_lit 0) A10K2.t6485 from rfl, totK_node, tot6484, tot6485]
  decide +kernel

theorem arows6479 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6479 = true := by
  rw [show A10K2.u6479 = KTree.node A10K2.t6486 (nat_lit 107577047) (nat_lit 12543977232) (nat_lit 0) A10K2.t6487 from rfl, allE_node, rows6486, irow6479, rows6487]
  all_goals rfl

theorem atot6479 : totK PA10K2 A10K2.u6479 = [0, 0, 1038315371324, 3705666506055, 3891420963343, 1172269095700, 74019108011, 0, 0, 0] := by
  rw [show A10K2.u6479 = KTree.node A10K2.t6486 (nat_lit 107577047) (nat_lit 12543977232) (nat_lit 0) A10K2.t6487 from rfl, totK_node, tot6486, tot6487]
  decide +kernel

theorem arows6482 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6482 = true := by
  rw [show A10K2.u6482 = KTree.node A10K2.t6488 (nat_lit 107590868) (nat_lit 11472079345) (nat_lit 0) A10K2.t6489 from rfl, allE_node, rows6488, irow6482, rows6489]
  all_goals rfl

theorem atot6482 : totK PA10K2 A10K2.u6482 = [0, 0, 367263799603, 2139385574642, 3928047572484, 2513328706418, 492931306764, 25565504801, 0, 0] := by
  rw [show A10K2.u6482 = KTree.node A10K2.t6488 (nat_lit 107590868) (nat_lit 11472079345) (nat_lit 0) A10K2.t6489 from rfl, totK_node, tot6488, tot6489]
  decide +kernel

theorem arows6483 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6483 = true := by
  rw [show A10K2.u6483 = KTree.node A10K2.t6490 (nat_lit 107595520) (nat_lit 9855753868) (nat_lit 0) A10K2.t6491 from rfl, allE_node, rows6490, irow6483, rows6491]
  all_goals rfl

theorem atot6483 : totK PA10K2 A10K2.u6483 = [0, 0, 682996630682, 3061017724327, 3910670754895, 1411753090472, 155635555024, 5517381808, 0, 0] := by
  rw [show A10K2.u6483 = KTree.node A10K2.t6490 (nat_lit 107595520) (nat_lit 9855753868) (nat_lit 0) A10K2.t6491 from rfl, totK_node, tot6490, tot6491]
  decide +kernel

theorem arows6485 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6485 = true := by
  rw [show A10K2.u6485 = KTree.node A10K2.t6492 (nat_lit 107603104) (nat_lit 3426218030) (nat_lit 0) A10K2.t6493 from rfl, allE_node, rows6492, irow6485, rows6493]
  all_goals rfl

theorem atot6485 : totK PA10K2 A10K2.u6485 = [0, 0, 786091465839, 3049214265367, 3915974869953, 1678366890709, 206476624098, 6121173289, 0, 0] := by
  rw [show A10K2.u6485 = KTree.node A10K2.t6492 (nat_lit 107603104) (nat_lit 3426218030) (nat_lit 0) A10K2.t6493 from rfl, totK_node, tot6492, tot6493]
  decide +kernel

theorem arows6486 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6486 = true := by
  rw [show A10K2.u6486 = KTree.node A10K2.t6494 (nat_lit 107616598) (nat_lit 4791712023) (nat_lit 0) A10K2.t6495 from rfl, allE_node, rows6494, irow6486, rows6495]
  all_goals rfl

theorem atot6486 : totK PA10K2 A10K2.u6486 = [0, 724179001030, 2667252555758, 3474838862406, 2042525134805, 586985453257, 47238528649, 0, 0, 0] := by
  rw [show A10K2.u6486 = KTree.node A10K2.t6494 (nat_lit 107616598) (nat_lit 4791712023) (nat_lit 0) A10K2.t6495 from rfl, totK_node, tot6494, tot6495]
  decide +kernel

theorem arows6491 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6491 = true := by
  rw [show A10K2.u6491 = KTree.node A10K2.t6496 (nat_lit 107623720) (nat_lit 8936867871) (nat_lit 0) A10K2.t6497 from rfl, allE_node, rows6496, irow6491, rows6497]
  all_goals rfl

theorem atot6491 : totK PA10K2 A10K2.u6491 = [0, 325843893375, 2094621364280, 3998553702267, 2710989971397, 573207771220, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u6491 = KTree.node A10K2.t6496 (nat_lit 107623720) (nat_lit 8936867871) (nat_lit 0) A10K2.t6497 from rfl, totK_node, tot6496, tot6497]
  decide +kernel

theorem arows6492 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6492 = true := by
  rw [show A10K2.u6492 = KTree.node A10K2.t6498 (nat_lit 107628293) (nat_lit 6968046882) (nat_lit 0) A10K2.t6499 from rfl, allE_node, rows6498, irow6492, rows6499]
  all_goals rfl

theorem atot6492 : totK PA10K2 A10K2.u6492 = [0, 743454972142, 3087649833228, 3969820200189, 1601743423004, 155928947253, 0, 0, 0, 0] := by
  rw [show A10K2.u6492 = KTree.node A10K2.t6498 (nat_lit 107628293) (nat_lit 6968046882) (nat_lit 0) A10K2.t6499 from rfl, totK_node, tot6498, tot6499]
  decide +kernel

theorem arows6494 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6494 = true := by
  rw [show A10K2.u6494 = KTree.node A10K2.t6500 (nat_lit 107645249) (nat_lit 10076940213) (nat_lit 0) A10K2.t6501 from rfl, allE_node, rows6500, irow6494, rows6501]
  all_goals rfl

theorem atot6494 : totK PA10K2 A10K2.u6494 = [0, 0, 1180277839867, 3864670881022, 3466432847789, 817492029684, 38825421397, 0, 0, 0] := by
  rw [show A10K2.u6494 = KTree.node A10K2.t6500 (nat_lit 107645249) (nat_lit 10076940213) (nat_lit 0) A10K2.t6501 from rfl, totK_node, tot6500, tot6501]
  decide +kernel

theorem arows6495 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6495 = true := by
  rw [show A10K2.u6495 = KTree.node A10K2.t6502 (nat_lit 107659808) (nat_lit 14161777346) (nat_lit 0) A10K2.t6503 from rfl, allE_node, rows6502, irow6495, rows6503]
  all_goals rfl

theorem atot6495 : totK PA10K2 A10K2.u6495 = [0, 0, 1064540114221, 3818175252103, 3785021986160, 895767362410, 44181510898, 0, 0, 0] := by
  rw [show A10K2.u6495 = KTree.node A10K2.t6502 (nat_lit 107659808) (nat_lit 14161777346) (nat_lit 0) A10K2.t6503 from rfl, totK_node, tot6502, tot6503]
  decide +kernel

theorem arows6498 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6498 = true := by
  rw [show A10K2.u6498 = KTree.node A10K2.t6504 (nat_lit 107665770) (nat_lit 9742220965) (nat_lit 0) A10K2.t6505 from rfl, allE_node, rows6504, irow6498, rows6505]
  all_goals rfl

theorem atot6498 : totK PA10K2 A10K2.u6498 = [0, 511028321977, 1682706476578, 2594199202656, 3058617914643, 1520624655575, 214597423881, 6354482628, 0, 0] := by
  rw [show A10K2.u6498 = KTree.node A10K2.t6504 (nat_lit 107665770) (nat_lit 9742220965) (nat_lit 0) A10K2.t6505 from rfl, totK_node, tot6504, tot6505]
  decide +kernel

theorem arows6499 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6499 = true := by
  rw [show A10K2.u6499 = KTree.node A10K2.t6506 (nat_lit 107685054) (nat_lit 15422297320) (nat_lit 0) A10K2.t6507 from rfl, allE_node, rows6506, irow6499, rows6507]
  all_goals rfl

theorem atot6499 : totK PA10K2 A10K2.u6499 = [0, 585755354620, 2737226877256, 4192608784457, 2203768989235, 322039860283, 7237400819, 0, 0, 0] := by
  rw [show A10K2.u6499 = KTree.node A10K2.t6506 (nat_lit 107685054) (nat_lit 15422297320) (nat_lit 0) A10K2.t6507 from rfl, totK_node, tot6506, tot6507]
  decide +kernel

theorem arows6501 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6501 = true := by
  rw [show A10K2.u6501 = KTree.node A10K2.t6508 (nat_lit 107689663) (nat_lit 9560490173) (nat_lit 0) A10K2.t6509 from rfl, allE_node, rows6508, irow6501, rows6509]
  all_goals rfl

theorem atot6501 : totK PA10K2 A10K2.u6501 = [0, 321645541796, 1975253787613, 4038598865790, 2945337096472, 615495320044, 31747192500, 0, 0, 0] := by
  rw [show A10K2.u6501 = KTree.node A10K2.t6508 (nat_lit 107689663) (nat_lit 9560490173) (nat_lit 0) A10K2.t6509 from rfl, totK_node, tot6508, tot6509]
  decide +kernel

theorem arows6502 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6502 = true := by
  rw [show A10K2.u6502 = KTree.node A10K2.t6510 (nat_lit 107703369) (nat_lit 9478410244) (nat_lit 0) A10K2.t6511 from rfl, allE_node, rows6510, irow6502, rows6511]
  all_goals rfl

theorem atot6502 : totK PA10K2 A10K2.u6502 = [0, 752007741353, 3133523817684, 4111131257147, 1819607855787, 245024340370, 6586990447, 0, 0, 0] := by
  rw [show A10K2.u6502 = KTree.node A10K2.t6510 (nat_lit 107703369) (nat_lit 9478410244) (nat_lit 0) A10K2.t6511 from rfl, totK_node, tot6510, tot6511]
  decide +kernel

theorem arows6506 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6506 = true := by
  rw [show A10K2.u6506 = KTree.node A10K2.t6512 (nat_lit 107707968) (nat_lit 15043522443) (nat_lit 0) A10K2.t6513 from rfl, allE_node, rows6512, irow6506, rows6513]
  all_goals rfl

theorem atot6506 : totK PA10K2 A10K2.u6506 = [0, 0, 1121452458605, 3969189037039, 3974572887958, 1097856563578, 63380566186, 0, 0, 0] := by
  rw [show A10K2.u6506 = KTree.node A10K2.t6512 (nat_lit 107707968) (nat_lit 15043522443) (nat_lit 0) A10K2.t6513 from rfl, totK_node, tot6512, tot6513]
  decide +kernel

theorem arows6507 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6507 = true := by
  rw [show A10K2.u6507 = KTree.node A10K2.t6514 (nat_lit 107718025) (nat_lit 5554200842) (nat_lit 0) A10K2.t6515 from rfl, allE_node, rows6514, irow6507, rows6515]
  all_goals rfl

theorem atot6507 : totK PA10K2 A10K2.u6507 = [0, 0, 767793014310, 3190714489686, 4172241930010, 1683966910768, 140937536174, 0, 0, 0] := by
  rw [show A10K2.u6507 = KTree.node A10K2.t6514 (nat_lit 107718025) (nat_lit 5554200842) (nat_lit 0) A10K2.t6515 from rfl, totK_node, tot6514, tot6515]
  decide +kernel

theorem arows6509 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6509 = true := by
  rw [show A10K2.u6509 = KTree.node A10K2.t6516 (nat_lit 107722915) (nat_lit 10499862237) (nat_lit 0) A10K2.t6517 from rfl, allE_node, rows6516, irow6509, rows6517]
  all_goals rfl

theorem atot6509 : totK PA10K2 A10K2.u6509 = [0, 0, 389210794986, 2438706689948, 4330471398780, 2451099872730, 323486512448, 7047025452, 0, 0] := by
  rw [show A10K2.u6509 = KTree.node A10K2.t6516 (nat_lit 107722915) (nat_lit 10499862237) (nat_lit 0) A10K2.t6517 from rfl, totK_node, tot6516, tot6517]
  decide +kernel

theorem arows6510 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6510 = true := by
  rw [show A10K2.u6510 = KTree.node A10K2.t6518 (nat_lit 107736791) (nat_lit 12646239392) (nat_lit 0) A10K2.t6519 from rfl, allE_node, rows6518, irow6510, rows6519]
  all_goals rfl

theorem atot6510 : totK PA10K2 A10K2.u6510 = [0, 0, 501550152162, 2545670341826, 4221125625196, 2428775876015, 350664753736, 6157148557, 0, 0] := by
  rw [show A10K2.u6510 = KTree.node A10K2.t6518 (nat_lit 107736791) (nat_lit 12646239392) (nat_lit 0) A10K2.t6519 from rfl, totK_node, tot6518, tot6519]
  decide +kernel

theorem arows6513 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6513 = true := by
  rw [show A10K2.u6513 = KTree.node A10K2.t6520 (nat_lit 107816441) (nat_lit 5398432340) (nat_lit 0) A10K2.t6521 from rfl, allE_node, rows6520, irow6513, rows6521]
  all_goals rfl

theorem atot6513 : totK PA10K2 A10K2.u6513 = [0, 0, 780889641854, 2891329376719, 3534591488197, 1901340439561, 489721941412, 34973146469, 0, 0] := by
  rw [show A10K2.u6513 = KTree.node A10K2.t6520 (nat_lit 107816441) (nat_lit 5398432340) (nat_lit 0) A10K2.t6521 from rfl, totK_node, tot6520, tot6521]
  decide +kernel

theorem arows6514 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6514 = true := by
  rw [show A10K2.u6514 = KTree.node A10K2.t6522 (nat_lit 107820948) (nat_lit 8921435088) (nat_lit 0) A10K2.t6523 from rfl, allE_node, rows6522, irow6514, rows6523]
  all_goals rfl

theorem atot6514 : totK PA10K2 A10K2.u6514 = [0, 0, 186131159319, 1743873202770, 3986678741630, 2979686358339, 616030374568, 31768748853, 0, 0] := by
  rw [show A10K2.u6514 = KTree.node A10K2.t6522 (nat_lit 107820948) (nat_lit 8921435088) (nat_lit 0) A10K2.t6523 from rfl, totK_node, tot6522, tot6523]
  decide +kernel

theorem arows6516 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6516 = true := by
  rw [show A10K2.u6516 = KTree.node A10K2.t6524 (nat_lit 107825492) (nat_lit 13140071320) (nat_lit 0) A10K2.t6525 from rfl, allE_node, rows6524, irow6516, rows6525]
  all_goals rfl

theorem atot6516 : totK PA10K2 A10K2.u6516 = [0, 0, 564792641930, 2821525923524, 4114882412600, 1555337541492, 109831023369, 0, 0, 0] := by
  rw [show A10K2.u6516 = KTree.node A10K2.t6524 (nat_lit 107825492) (nat_lit 13140071320) (nat_lit 0) A10K2.t6525 from rfl, totK_node, tot6524, tot6525]
  decide +kernel

theorem arows6517 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6517 = true := by
  rw [show A10K2.u6517 = KTree.node A10K2.t6526 (nat_lit 107833222) (nat_lit 15551816010) (nat_lit 0) A10K2.t6527 from rfl, allE_node, rows6526, irow6517, rows6527]
  all_goals rfl

theorem atot6517 : totK PA10K2 A10K2.u6517 = [0, 0, 780536075463, 3060283346920, 3945624638098, 1879980501863, 254992262520, 6239673734, 0, 0] := by
  rw [show A10K2.u6517 = KTree.node A10K2.t6526 (nat_lit 107833222) (nat_lit 15551816010) (nat_lit 0) A10K2.t6527 from rfl, totK_node, tot6526, tot6527]
  decide +kernel

theorem arows6524 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6524 = true := by
  rw [show A10K2.u6524 = KTree.node A10K2.t6528 (nat_lit 107848866) (nat_lit 14523975480) (nat_lit 0) A10K2.t6529 from rfl, allE_node, rows6528, irow6524, rows6529]
  all_goals rfl

theorem atot6524 : totK PA10K2 A10K2.u6524 = [0, 0, 0, 1043844280196, 3832021652028, 3794368204852, 994933410022, 62065994333, 0, 0] := by
  rw [show A10K2.u6524 = KTree.node A10K2.t6528 (nat_lit 107848866) (nat_lit 14523975480) (nat_lit 0) A10K2.t6529 from rfl, totK_node, tot6528, tot6529]
  decide +kernel

theorem arows6525 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6525 = true := by
  rw [show A10K2.u6525 = KTree.node A10K2.t6530 (nat_lit 107853461) (nat_lit 6345738522) (nat_lit 0) A10K2.t6531 from rfl, allE_node, rows6530, irow6525, rows6531]
  all_goals rfl

theorem atot6525 : totK PA10K2 A10K2.u6525 = [0, 0, 0, 281106718642, 1922900189609, 3935338630677, 2664886962073, 549364755548, 31018567651, 0] := by
  rw [show A10K2.u6525 = KTree.node A10K2.t6530 (nat_lit 107853461) (nat_lit 6345738522) (nat_lit 0) A10K2.t6531 from rfl, totK_node, tot6530, tot6531]
  decide +kernel

theorem arows6527 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6527 = true := by
  rw [show A10K2.u6527 = KTree.node A10K2.t6532 (nat_lit 107858099) (nat_lit 10071710841) (nat_lit 0) A10K2.t6533 from rfl, allE_node, rows6532, irow6527, rows6533]
  all_goals rfl

theorem atot6527 : totK PA10K2 A10K2.u6527 = [0, 0, 0, 676681387359, 3012456325970, 3889527309465, 1307796256953, 96694537082, 0, 0] := by
  rw [show A10K2.u6527 = KTree.node A10K2.t6532 (nat_lit 107858099) (nat_lit 10071710841) (nat_lit 0) A10K2.t6533 from rfl, totK_node, tot6532, tot6533]
  decide +kernel

theorem arows6528 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6528 = true := by
  rw [show A10K2.u6528 = KTree.node A10K2.t6534 (nat_lit 107867140) (nat_lit 1507147892) (nat_lit 0) A10K2.t6535 from rfl, allE_node, rows6534, irow6528, rows6535]
  all_goals rfl

theorem atot6528 : totK PA10K2 A10K2.u6528 = [0, 0, 251986720587, 1671174733471, 3369420236391, 2978205301095, 1174401834179, 177220217675, 5685526223, 0] := by
  rw [show A10K2.u6528 = KTree.node A10K2.t6534 (nat_lit 107867140) (nat_lit 1507147892) (nat_lit 0) A10K2.t6535 from rfl, totK_node, tot6534, tot6535]
  decide +kernel

theorem arows6531 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6531 = true := by
  rw [show A10K2.u6531 = KTree.node A10K2.t6536 (nat_lit 107882268) (nat_lit 11956028668) (nat_lit 0) A10K2.t6537 from rfl, allE_node, rows6536, irow6531, rows6537]
  all_goals rfl

theorem atot6531 : totK PA10K2 A10K2.u6531 = [0, 0, 792685005386, 3108397023418, 3912068931423, 1585404694071, 161087975825, 5460492893, 0, 0] := by
  rw [show A10K2.u6531 = KTree.node A10K2.t6536 (nat_lit 107882268) (nat_lit 11956028668) (nat_lit 0) A10K2.t6537 from rfl, totK_node, tot6536, tot6537]
  decide +kernel

theorem arows6532 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6532 = true := by
  rw [show A10K2.u6532 = KTree.node A10K2.t6538 (nat_lit 107887109) (nat_lit 6359542315) (nat_lit 0) A10K2.t6539 from rfl, allE_node, rows6538, irow6532, rows6539]
  all_goals rfl

theorem atot6532 : totK PA10K2 A10K2.u6532 = [0, 0, 384514750815, 1971679867276, 3774894147264, 2781783663292, 598427529620, 31768748853, 0, 0] := by
  rw [show A10K2.u6532 = KTree.node A10K2.t6538 (nat_lit 107887109) (nat_lit 6359542315) (nat_lit 0) A10K2.t6539 from rfl, totK_node, tot6538, tot6539]
  decide +kernel

theorem arows6534 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6534 = true := by
  rw [show A10K2.u6534 = KTree.node A10K2.t6540 (nat_lit 107892835) (nat_lit 4686220298) (nat_lit 0) A10K2.t6541 from rfl, allE_node, rows6540, irow6534, rows6541]
  all_goals rfl

theorem atot6534 : totK PA10K2 A10K2.u6534 = [0, 0, 358002183444, 2350485396236, 4165101513894, 2121741687394, 261818840414, 6354482628, 0, 0] := by
  rw [show A10K2.u6534 = KTree.node A10K2.t6540 (nat_lit 107892835) (nat_lit 4686220298) (nat_lit 0) A10K2.t6541 from rfl, totK_node, tot6540, tot6541]
  decide +kernel

theorem arows6535 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6535 = true := by
  rw [show A10K2.u6535 = KTree.node A10K2.t6542 (nat_lit 107915112) (nat_lit 5352180346) (nat_lit 0) A10K2.t6543 from rfl, allE_node, rows6542, irow6535, rows6543]
  all_goals rfl

theorem atot6535 : totK PA10K2 A10K2.u6535 = [0, 0, 0, 1052807943543, 3797337061245, 3741622162433, 889146517160, 45352262510, 0, 0] := by
  rw [show A10K2.u6535 = KTree.node A10K2.t6542 (nat_lit 107915112) (nat_lit 5352180346) (nat_lit 0) A10K2.t6543 from rfl, totK_node, tot6542, tot6543]
  decide +kernel

theorem arows6539 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6539 = true := by
  rw [show A10K2.u6539 = KTree.node A10K2.t6544 (nat_lit 107923629) (nat_lit 6561767260) (nat_lit 0) A10K2.t6545 from rfl, allE_node, rows6544, irow6539, rows6545]
  all_goals rfl

theorem atot6539 : totK PA10K2 A10K2.u6539 = [0, 0, 0, 664658728468, 3160464577609, 4044873356521, 1211622068627, 89288868902, 0, 0] := by
  rw [show A10K2.u6539 = KTree.node A10K2.t6544 (nat_lit 107923629) (nat_lit 6561767260) (nat_lit 0) A10K2.t6545 from rfl, totK_node, tot6544, tot6545]
  decide +kernel

theorem arows6540 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6540 = true := by
  rw [show A10K2.u6540 = KTree.node A10K2.t6546 (nat_lit 107941589) (nat_lit 2647141505) (nat_lit 0) A10K2.t6547 from rfl, allE_node, rows6546, irow6540, rows6547]
  all_goals rfl

theorem atot6540 : totK PA10K2 A10K2.u6540 = [0, 0, 1018983537682, 3319385343184, 3216232094222, 1526960160236, 666449408610, 135940379984, 5982052406, 0] := by
  rw [show A10K2.u6540 = KTree.node A10K2.t6546 (nat_lit 107941589) (nat_lit 2647141505) (nat_lit 0) A10K2.t6547 from rfl, totK_node, tot6546, tot6547]
  decide +kernel

theorem arows6542 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6542 = true := by
  rw [show A10K2.u6542 = KTree.node A10K2.t6548 (nat_lit 107951429) (nat_lit 5989079635) (nat_lit 0) A10K2.t6549 from rfl, allE_node, rows6548, irow6542, rows6549]
  all_goals rfl

theorem atot6542 : totK PA10K2 A10K2.u6542 = [0, 0, 394276744602, 2235420815712, 4161742890457, 2568957944683, 471020696822, 25660650750, 0, 0] := by
  rw [show A10K2.u6542 = KTree.node A10K2.t6548 (nat_lit 107951429) (nat_lit 5989079635) (nat_lit 0) A10K2.t6549 from rfl, totK_node, tot6548, tot6549]
  decide +kernel

theorem arows6543 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6543 = true := by
  rw [show A10K2.u6543 = KTree.node A10K2.t6550 (nat_lit 107965536) (nat_lit 11215708994) (nat_lit 0) A10K2.t6551 from rfl, allE_node, rows6550, irow6543, rows6551]
  all_goals rfl

theorem atot6543 : totK PA10K2 A10K2.u6543 = [0, 0, 749122265670, 3373639321875, 4284893732687, 1587115294109, 137578524377, 0, 0, 0] := by
  rw [show A10K2.u6543 = KTree.node A10K2.t6550 (nat_lit 107965536) (nat_lit 11215708994) (nat_lit 0) A10K2.t6551 from rfl, totK_node, tot6550, tot6551]
  decide +kernel

theorem arows6546 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6546 = true := by
  rw [show A10K2.u6546 = KTree.node A10K2.t6552 (nat_lit 108078294) (nat_lit 14901031802) (nat_lit 0) A10K2.t6553 from rfl, allE_node, rows6552, irow6546, rows6553]
  all_goals rfl

theorem atot6546 : totK PA10K2 A10K2.u6546 = [0, 583460167190, 2093089655561, 2417923698520, 2185525520224, 1966951393005, 594561342464, 41590655314, 0, 0] := by
  rw [show A10K2.u6546 = KTree.node A10K2.t6552 (nat_lit 108078294) (nat_lit 14901031802) (nat_lit 0) A10K2.t6553 from rfl, totK_node, tot6552, tot6553]
  decide +kernel

theorem arows6547 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6547 = true := by
  rw [show A10K2.u6547 = KTree.node A10K2.t6554 (nat_lit 108082835) (nat_lit 10974729157) (nat_lit 0) A10K2.t6555 from rfl, allE_node, rows6554, irow6547, rows6555]
  all_goals rfl

theorem atot6547 : totK PA10K2 A10K2.u6547 = [0, 258566662976, 1829204349002, 4029752524766, 2934437301756, 593099308896, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u6547 = KTree.node A10K2.t6554 (nat_lit 108082835) (nat_lit 10974729157) (nat_lit 0) A10K2.t6555 from rfl, totK_node, tot6554, tot6555]
  decide +kernel

theorem arows6549 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6549 = true := by
  rw [show A10K2.u6549 = KTree.node A10K2.t6556 (nat_lit 108087191) (nat_lit 13206656763) (nat_lit 0) A10K2.t6557 from rfl, allE_node, rows6556, irow6549, rows6557]
  all_goals rfl

theorem atot6549 : totK PA10K2 A10K2.u6549 = [0, 750797585308, 3109482032651, 3965607940412, 1560462539072, 140932852890, 0, 0, 0, 0] := by
  rw [show A10K2.u6549 = KTree.node A10K2.t6556 (nat_lit 108087191) (nat_lit 13206656763) (nat_lit 0) A10K2.t6557 from rfl, totK_node, tot6556, tot6557]
  decide +kernel

theorem arows6550 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6550 = true := by
  rw [show A10K2.u6550 = KTree.node A10K2.t6558 (nat_lit 108095146) (nat_lit 12829074554) (nat_lit 0) A10K2.t6559 from rfl, allE_node, rows6558, irow6550, rows6559]
  all_goals rfl

theorem atot6550 : totK PA10K2 A10K2.u6550 = [0, 595155796918, 2715672775278, 4102200451609, 2148944307545, 304105452813, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u6550 = KTree.node A10K2.t6558 (nat_lit 108095146) (nat_lit 12829074554) (nat_lit 0) A10K2.t6559 from rfl, totK_node, tot6558, tot6559]
  decide +kernel

theorem arows6555 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6555 = true := by
  rw [show A10K2.u6555 = KTree.node A10K2.t6560 (nat_lit 108110997) (nat_lit 6681160818) (nat_lit 0) A10K2.t6561 from rfl, allE_node, rows6560, irow6555, rows6561]
  all_goals rfl

theorem atot6555 : totK PA10K2 A10K2.u6555 = [0, 0, 1012425149562, 3776873772129, 3930756498185, 1125634378977, 68057348304, 0, 0, 0] := by
  rw [show A10K2.u6555 = KTree.node A10K2.t6560 (nat_lit 108110997) (nat_lit 6681160818) (nat_lit 0) A10K2.t6561 from rfl, totK_node, tot6560, tot6561]
  decide +kernel

theorem arows6556 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6556 = true := by
  rw [show A10K2.u6556 = KTree.node A10K2.t6562 (nat_lit 108115420) (nat_lit 5503332563) (nat_lit 0) A10K2.t6563 from rfl, allE_node, rows6562, irow6556, rows6563]
  all_goals rfl

theorem atot6556 : totK PA10K2 A10K2.u6556 = [0, 0, 258151593043, 1909761747479, 4083368101220, 2691453969960, 549074201098, 31082886609, 0, 0] := by
  rw [show A10K2.u6556 = KTree.node A10K2.t6562 (nat_lit 108115420) (nat_lit 5503332563) (nat_lit 0) A10K2.t6563 from rfl, totK_node, tot6562, tot6563]
  decide +kernel

theorem arows6558 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6558 = true := by
  rw [show A10K2.u6558 = KTree.node A10K2.t6564 (nat_lit 108120098) (nat_lit 9162599275) (nat_lit 0) A10K2.t6565 from rfl, allE_node, rows6564, irow6558, rows6565]
  all_goals rfl

theorem atot6558 : totK PA10K2 A10K2.u6558 = [0, 0, 750649439132, 3177901178232, 3988672675729, 1431961530332, 107166177224, 0, 0, 0] := by
  rw [show A10K2.u6558 = KTree.node A10K2.t6564 (nat_lit 108120098) (nat_lit 9162599275) (nat_lit 0) A10K2.t6565 from rfl, totK_node, tot6564, tot6565]
  decide +kernel

theorem arows6559 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6559 = true := by
  rw [show A10K2.u6559 = KTree.node A10K2.t6566 (nat_lit 108128023) (nat_lit 10282356553) (nat_lit 0) A10K2.t6567 from rfl, allE_node, rows6566, irow6559, rows6567]
  all_goals rfl

theorem atot6559 : totK PA10K2 A10K2.u6559 = [0, 247698060303, 1196403826726, 2789355834635, 3553576909019, 1727011386200, 229357908174, 6121173289, 0, 0] := by
  rw [show A10K2.u6559 = KTree.node A10K2.t6566 (nat_lit 108128023) (nat_lit 10282356553) (nat_lit 0) A10K2.t6567 from rfl, totK_node, tot6566, tot6567]
  decide +kernel

theorem arows6562 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6562 = true := by
  rw [show A10K2.u6562 = KTree.node A10K2.t6568 (nat_lit 108138772) (nat_lit 12544859683) (nat_lit 0) A10K2.t6569 from rfl, allE_node, rows6568, irow6562, rows6569]
  all_goals rfl

theorem atot6562 : totK PA10K2 A10K2.u6562 = [0, 427731807956, 2246364915100, 3913440031164, 2402737962458, 467078565544, 30402056026, 0, 0, 0] := by
  rw [show A10K2.u6562 = KTree.node A10K2.t6568 (nat_lit 108138772) (nat_lit 12544859683) (nat_lit 0) A10K2.t6569 from rfl, totK_node, tot6568, tot6569]
  decide +kernel

theorem arows6563 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6563 = true := by
  rw [show A10K2.u6563 = KTree.node A10K2.t6570 (nat_lit 108145472) (nat_lit 12769192779) (nat_lit 0) A10K2.t6571 from rfl, allE_node, rows6570, irow6563, rows6571]
  all_goals rfl

theorem atot6563 : totK PA10K2 A10K2.u6563 = [0, 652874332715, 2832607247470, 3889640401984, 1936208897813, 366978668153, 20340910120, 0, 0, 0] := by
  rw [show A10K2.u6563 = KTree.node A10K2.t6570 (nat_lit 108145472) (nat_lit 12769192779) (nat_lit 0) A10K2.t6571 from rfl, totK_node, tot6570, tot6571]
  decide +kernel

theorem arows6565 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6565 = true := by
  rw [show A10K2.u6565 = KTree.node A10K2.t6572 (nat_lit 108151144) (nat_lit 9846266719) (nat_lit 0) A10K2.t6573 from rfl, allE_node, rows6572, irow6565, rows6573]
  all_goals rfl

theorem atot6565 : totK PA10K2 A10K2.u6565 = [0, 647880606010, 2627609219053, 3814313337913, 2103273929962, 316849692250, 11427838733, 0, 0, 0] := by
  rw [show A10K2.u6565 = KTree.node A10K2.t6572 (nat_lit 108151144) (nat_lit 9846266719) (nat_lit 0) A10K2.t6573 from rfl, totK_node, tot6572, tot6573]
  decide +kernel

theorem arows6566 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6566 = true := by
  rw [show A10K2.u6566 = KTree.node A10K2.t6574 (nat_lit 108156380) (nat_lit 5437265718) (nat_lit 0) A10K2.t6575 from rfl, allE_node, rows6574, irow6566, rows6575]
  all_goals rfl

theorem atot6566 : totK PA10K2 A10K2.u6566 = [0, 172943831038, 1903278539964, 4217459070148, 2670311798066, 456561768498, 26172145312, 0, 0, 0] := by
  rw [show A10K2.u6566 = KTree.node A10K2.t6574 (nat_lit 108156380) (nat_lit 5437265718) (nat_lit 0) A10K2.t6575 from rfl, totK_node, tot6574, tot6575]
  decide +kernel

theorem arows6570 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6570 = true := by
  rw [show A10K2.u6570 = KTree.node A10K2.t6576 (nat_lit 108177044) (nat_lit 11980330599) (nat_lit 0) A10K2.t6577 from rfl, allE_node, rows6576, irow6570, rows6577]
  all_goals rfl

theorem atot6570 : totK PA10K2 A10K2.u6570 = [0, 0, 1047193941749, 3758845259888, 3806403720485, 945994410980, 44211540368, 0, 0, 0] := by
  rw [show A10K2.u6570 = KTree.node A10K2.t6576 (nat_lit 108177044) (nat_lit 11980330599) (nat_lit 0) A10K2.t6577 from rfl, totK_node, tot6576, tot6577]
  decide +kernel

theorem arows6571 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6571 = true := by
  rw [show A10K2.u6571 = KTree.node A10K2.t6578 (nat_lit 108185246) (nat_lit 12712652371) (nat_lit 0) A10K2.t6579 from rfl, allE_node, rows6578, irow6571, rows6579]
  all_goals rfl

theorem atot6571 : totK PA10K2 A10K2.u6571 = [0, 0, 816680901294, 3342338942673, 3938226404764, 1178612568181, 83009222198, 0, 0, 0] := by
  rw [show A10K2.u6571 = KTree.node A10K2.t6578 (nat_lit 108185246) (nat_lit 12712652371) (nat_lit 0) A10K2.t6579 from rfl, totK_node, tot6578, tot6579]
  decide +kernel

theorem arows6573 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6573 = true := by
  rw [show A10K2.u6573 = KTree.node A10K2.t6580 (nat_lit 108340499) (nat_lit 10823858322) (nat_lit 0) A10K2.t6581 from rfl, allE_node, rows6580, irow6573, rows6581]
  all_goals rfl

theorem atot6573 : totK PA10K2 A10K2.u6573 = [0, 0, 583460167190, 2727498589632, 3999202352753, 1825047055298, 266396256971, 6354482628, 0, 0] := by
  rw [show A10K2.u6573 = KTree.node A10K2.t6580 (nat_lit 108340499) (nat_lit 10823858322) (nat_lit 0) A10K2.t6581 from rfl, totK_node, tot6580, tot6581]
  decide +kernel

theorem arows6574 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6574 = true := by
  rw [show A10K2.u6574 = KTree.node A10K2.t6582 (nat_lit 108345047) (nat_lit 9900966111) (nat_lit 0) A10K2.t6583 from rfl, allE_node, rows6582, irow6574, rows6583]
  all_goals rfl

theorem atot6574 : totK PA10K2 A10K2.u6574 = [0, 0, 332245058647, 1897752034824, 3917747697807, 2855143684585, 587333160873, 31452573850, 0, 0] := by
  rw [show A10K2.u6574 = KTree.node A10K2.t6582 (nat_lit 108345047) (nat_lit 9900966111) (nat_lit 0) A10K2.t6583 from rfl, totK_node, tot6582, tot6583]
  decide +kernel

theorem arows6577 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6577 = true := by
  rw [show A10K2.u6577 = KTree.node A10K2.t6584 (nat_lit 108349540) (nat_lit 13600911956) (nat_lit 0) A10K2.t6585 from rfl, allE_node, rows6584, irow6577, rows6585]
  all_goals rfl

theorem atot6577 : totK PA10K2 A10K2.u6577 = [0, 0, 677119189637, 3128367938629, 4111164894770, 1449919338357, 89524505899, 0, 0, 0] := by
  rw [show A10K2.u6577 = KTree.node A10K2.t6584 (nat_lit 108349540) (nat_lit 13600911956) (nat_lit 0) A10K2.t6585 from rfl, totK_node, tot6584, tot6585]
  decide +kernel

theorem arows6578 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6578 = true := by
  rw [show A10K2.u6578 = KTree.node A10K2.t6586 (nat_lit 108357461) (nat_lit 6466345868) (nat_lit 0) A10K2.t6587 from rfl, allE_node, rows6586, irow6578, rows6587]
  all_goals rfl

theorem atot6578 : totK PA10K2 A10K2.u6578 = [0, 0, 595155796918, 2700671790475, 4129112775103, 2122534854996, 277862989215, 6354482628, 0, 0] := by
  rw [show A10K2.u6578 = KTree.node A10K2.t6586 (nat_lit 108357461) (nat_lit 6466345868) (nat_lit 0) A10K2.t6587 from rfl, totK_node, tot6586, tot6587]
  decide +kernel

theorem arows6580 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6580 = true := by
  rw [show A10K2.u6580 = KTree.node A10K2.t6588 (nat_lit 108397416) (nat_lit 9602818053) (nat_lit 0) A10K2.t6589 from rfl, allE_node, rows6588, irow6580, rows6589]
  all_goals rfl

theorem atot6580 : totK PA10K2 A10K2.u6580 = [0, 0, 560546078113, 2740749537759, 4135662284248, 1941025646725, 289489316690, 6962742351, 0, 0] := by
  rw [show A10K2.u6580 = KTree.node A10K2.t6588 (nat_lit 108397416) (nat_lit 9602818053) (nat_lit 0) A10K2.t6589 from rfl, totK_node, tot6588, tot6589]
  decide +kernel

theorem arows6581 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6581 = true := by
  rw [show A10K2.u6581 = KTree.node A10K2.t6590 (nat_lit 108406798) (nat_lit 4562064353) (nat_lit 0) A10K2.t6591 from rfl, allE_node, rows6590, irow6581, rows6591]
  all_goals rfl

theorem atot6581 : totK PA10K2 A10K2.u6581 = [0, 0, 766759426747, 3040438667761, 3896948961794, 1677468068783, 201415519920, 5460492893, 0, 0] := by
  rw [show A10K2.u6581 = KTree.node A10K2.t6590 (nat_lit 108406798) (nat_lit 4562064353) (nat_lit 0) A10K2.t6591 from rfl, totK_node, tot6590, tot6591]
  decide +kernel

theorem arows6587 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6587 = true := by
  rw [show A10K2.u6587 = KTree.node A10K2.t6592 (nat_lit 108412068) (nat_lit 11722107196) (nat_lit 0) A10K2.t6593 from rfl, allE_node, rows6592, irow6587, rows6593]
  all_goals rfl

theorem atot6587 : totK PA10K2 A10K2.u6587 = [0, 0, 513073702450, 2281305356158, 3718123464495, 2334508822585, 479176204171, 31003444686, 0, 0] := by
  rw [show A10K2.u6587 = KTree.node A10K2.t6592 (nat_lit 108412068) (nat_lit 11722107196) (nat_lit 0) A10K2.t6593 from rfl, totK_node, tot6592, tot6593]
  decide +kernel

theorem arows6588 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6588 = true := by
  rw [show A10K2.u6588 = KTree.node A10K2.t6594 (nat_lit 108417322) (nat_lit 10679259678) (nat_lit 0) A10K2.t6595 from rfl, allE_node, rows6594, irow6588, rows6595]
  all_goals rfl

theorem atot6588 : totK PA10K2 A10K2.u6588 = [0, 0, 306139930691, 2262922011520, 4241228831213, 2181229884482, 300586842376, 6354482628, 0, 0] := by
  rw [show A10K2.u6588 = KTree.node A10K2.t6594 (nat_lit 108417322) (nat_lit 10679259678) (nat_lit 0) A10K2.t6595 from rfl, totK_node, tot6594, tot6595]
  decide +kernel

theorem arows6590 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6590 = true := by
  rw [show A10K2.u6590 = KTree.node A10K2.t6596 (nat_lit 108438719) (nat_lit 12441287894) (nat_lit 0) A10K2.t6597 from rfl, allE_node, rows6596, irow6590, rows6597]
  all_goals rfl

theorem atot6590 : totK PA10K2 A10K2.u6590 = [0, 0, 0, 1019108203175, 3901517927841, 3594082903736, 740517362863, 37076771047, 0, 0] := by
  rw [show A10K2.u6590 = KTree.node A10K2.t6596 (nat_lit 108438719) (nat_lit 12441287894) (nat_lit 0) A10K2.t6597 from rfl, totK_node, tot6596, tot6597]
  decide +kernel

theorem arows6591 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6591 = true := by
  rw [show A10K2.u6591 = KTree.node A10K2.t6598 (nat_lit 108447393) (nat_lit 4565097215) (nat_lit 0) A10K2.t6599 from rfl, allE_node, rows6598, irow6591, rows6599]
  all_goals rfl

theorem atot6591 : totK PA10K2 A10K2.u6591 = [0, 0, 0, 994343993492, 3577215077730, 3596539178354, 960157043280, 55396467691, 0, 0] := by
  rw [show A10K2.u6591 = KTree.node A10K2.t6598 (nat_lit 108447393) (nat_lit 4565097215) (nat_lit 0) A10K2.t6599 from rfl, totK_node, tot6598, tot6599]
  decide +kernel

theorem arows6594 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6594 = true := by
  rw [show A10K2.u6594 = KTree.node A10K2.t6600 (nat_lit 108527973) (nat_lit 7209061384) (nat_lit 0) A10K2.t6601 from rfl, allE_node, rows6600, irow6594, rows6601]
  all_goals rfl

theorem atot6594 : totK PA10K2 A10K2.u6594 = [0, 776609848865, 2469175014818, 2172362275636, 1098315325021, 1652527365173, 1098091430947, 203361510298, 6354482628, 0] := by
  rw [show A10K2.u6594 = KTree.node A10K2.t6600 (nat_lit 108527973) (nat_lit 7209061384) (nat_lit 0) A10K2.t6601 from rfl, totK_node, tot6600, tot6601]
  decide +kernel

theorem arows6595 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6595 = true := by
  rw [show A10K2.u6595 = KTree.node A10K2.t6602 (nat_lit 108533802) (nat_lit 3974365996) (nat_lit 0) A10K2.t6603 from rfl, allE_node, rows6602, irow6595, rows6603]
  all_goals rfl

theorem atot6595 : totK PA10K2 A10K2.u6595 = [0, 284639743112, 2145101376671, 4335980387078, 2664506071157, 482984519801, 25371180993, 0, 0, 0] := by
  rw [show A10K2.u6595 = KTree.node A10K2.t6602 (nat_lit 108533802) (nat_lit 3974365996) (nat_lit 0) A10K2.t6603 from rfl, totK_node, tot6602, tot6603]
  decide +kernel

theorem arows6597 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6597 = true := by
  rw [show A10K2.u6597 = KTree.node A10K2.t6604 (nat_lit 108556169) (nat_lit 8298999920) (nat_lit 0) A10K2.t6605 from rfl, allE_node, rows6604, irow6597, rows6605]
  all_goals rfl

theorem atot6597 : totK PA10K2 A10K2.u6597 = [0, 541450865991, 2543211156342, 4181162299339, 2651140343466, 469990117349, 13543209714, 0, 0, 0] := by
  rw [show A10K2.u6597 = KTree.node A10K2.t6604 (nat_lit 108556169) (nat_lit 8298999920) (nat_lit 0) A10K2.t6605 from rfl, totK_node, tot6604, tot6605]
  decide +kernel

theorem arows6598 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6598 = true := by
  rw [show A10K2.u6598 = KTree.node A10K2.t6606 (nat_lit 108560838) (nat_lit 15501732249) (nat_lit 0) A10K2.t6607 from rfl, allE_node, rows6606, irow6598, rows6607]
  all_goals rfl

theorem atot6598 : totK PA10K2 A10K2.u6598 = [0, 0, 1095041498889, 3806294025359, 3884951429078, 1141855382142, 80387723107, 0, 0, 0] := by
  rw [show A10K2.u6598 = KTree.node A10K2.t6606 (nat_lit 108560838) (nat_lit 15501732249) (nat_lit 0) A10K2.t6607 from rfl, totK_node, tot6606, tot6607]
  decide +kernel

theorem arows6602 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6602 = true := by
  rw [show A10K2.u6602 = KTree.node A10K2.t6608 (nat_lit 108567602) (nat_lit 10401026212) (nat_lit 0) A10K2.t6609 from rfl, allE_node, rows6608, irow6602, rows6609]
  all_goals rfl

theorem atot6602 : totK PA10K2 A10K2.u6602 = [0, 0, 503849805566, 2661709790339, 4297195077707, 2183974669990, 303946777901, 7237400819, 0, 0] := by
  rw [show A10K2.u6602 = KTree.node A10K2.t6608 (nat_lit 108567602) (nat_lit 10401026212) (nat_lit 0) A10K2.t6609 from rfl, totK_node, tot6608, tot6609]
  decide +kernel

theorem arows6603 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6603 = true := by
  rw [show A10K2.u6603 = KTree.node A10K2.t6610 (nat_lit 108602659) (nat_lit 10336289781) (nat_lit 0) A10K2.t6611 from rfl, allE_node, rows6610, irow6603, rows6611]
  all_goals rfl

theorem atot6603 : totK PA10K2 A10K2.u6603 = [0, 628127599786, 2491859054273, 3518291621634, 2388975562327, 741123318230, 57551169768, 0, 0, 0] := by
  rw [show A10K2.u6603 = KTree.node A10K2.t6610 (nat_lit 108602659) (nat_lit 10336289781) (nat_lit 0) A10K2.t6611 from rfl, totK_node, tot6610, tot6611]
  decide +kernel

theorem arows6605 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6605 = true := by
  rw [show A10K2.u6605 = KTree.node A10K2.t6612 (nat_lit 108607198) (nat_lit 10157317996) (nat_lit 0) A10K2.t6613 from rfl, allE_node, rows6612, irow6605, rows6613]
  all_goals rfl

theorem atot6605 : totK PA10K2 A10K2.u6605 = [0, 288208775822, 1845476061222, 3979415228920, 3017393909951, 627311274808, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u6605 = KTree.node A10K2.t6612 (nat_lit 108607198) (nat_lit 10157317996) (nat_lit 0) A10K2.t6613 from rfl, totK_node, tot6612, tot6613]
  decide +kernel

theorem arows6606 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6606 = true := by
  rw [show A10K2.u6606 = KTree.node A10K2.t6614 (nat_lit 108612450) (nat_lit 11457037723) (nat_lit 0) A10K2.t6615 from rfl, allE_node, rows6614, irow6606, rows6615]
  all_goals rfl

theorem atot6606 : totK PA10K2 A10K2.u6606 = [0, 651845267412, 2855669940003, 3962808328742, 1800685821311, 223294380037, 5982052406, 0, 0, 0] := by
  rw [show A10K2.u6606 = KTree.node A10K2.t6614 (nat_lit 108612450) (nat_lit 11457037723) (nat_lit 0) A10K2.t6615 from rfl, totK_node, tot6614, tot6615]
  decide +kernel

theorem arows6609 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6609 = true := by
  rw [show A10K2.u6609 = KTree.node A10K2.t6616 (nat_lit 108621212) (nat_lit 7587532292) (nat_lit 0) A10K2.t6617 from rfl, allE_node, rows6616, irow6609, rows6617]
  all_goals rfl

theorem atot6609 : totK PA10K2 A10K2.u6609 = [0, 614826028692, 2839779916084, 4268405032550, 2162713214041, 306812261467, 6585347165, 0, 0, 0] := by
  rw [show A10K2.u6609 = KTree.node A10K2.t6616 (nat_lit 108621212) (nat_lit 7587532292) (nat_lit 0) A10K2.t6617 from rfl, totK_node, tot6616, tot6617]
  decide +kernel

theorem arows6610 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6610 = true := by
  rw [show A10K2.u6610 = KTree.node A10K2.t6618 (nat_lit 108625910) (nat_lit 16720836805) (nat_lit 0) A10K2.t6619 from rfl, allE_node, rows6618, irow6610, rows6619]
  all_goals rfl

theorem atot6610 : totK PA10K2 A10K2.u6610 = [0, 0, 973265652841, 3634543659399, 3952776509530, 1203083472998, 82605879954, 0, 0, 0] := by
  rw [show A10K2.u6610 = KTree.node A10K2.t6618 (nat_lit 108625910) (nat_lit 16720836805) (nat_lit 0) A10K2.t6619 from rfl, totK_node, tot6618, tot6619]
  decide +kernel

theorem arows6612 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6612 = true := by
  rw [show A10K2.u6612 = KTree.node A10K2.t6620 (nat_lit 108639665) (nat_lit 5580526884) (nat_lit 0) A10K2.t6621 from rfl, allE_node, rows6620, irow6612, rows6621]
  all_goals rfl

theorem atot6612 : totK PA10K2 A10K2.u6612 = [0, 0, 295617904848, 2001799932706, 3992132301640, 2649885476421, 551412952408, 31082886609, 0, 0] := by
  rw [show A10K2.u6612 = KTree.node A10K2.t6620 (nat_lit 108639665) (nat_lit 5580526884) (nat_lit 0) A10K2.t6621 from rfl, totK_node, tot6620, tot6621]
  decide +kernel

theorem arows6613 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6613 = true := by
  rw [show A10K2.u6613 = KTree.node A10K2.t6622 (nat_lit 108645043) (nat_lit 9992920057) (nat_lit 0) A10K2.t6623 from rfl, allE_node, rows6622, irow6613, rows6623]
  all_goals rfl

theorem atot6613 : totK PA10K2 A10K2.u6613 = [0, 0, 667932178050, 2745334545157, 3846597105135, 1868079840984, 245241127849, 5885702948, 0, 0] := by
  rw [show A10K2.u6613 = KTree.node A10K2.t6622 (nat_lit 108645043) (nat_lit 9992920057) (nat_lit 0) A10K2.t6623 from rfl, totK_node, tot6622, tot6623]
  decide +kernel

theorem arows6618 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6618 = true := by
  rw [show A10K2.u6618 = KTree.node A10K2.t6624 (nat_lit 108653759) (nat_lit 14180918075) (nat_lit 0) A10K2.t6625 from rfl, allE_node, rows6624, irow6618, rows6625]
  all_goals rfl

theorem atot6618 : totK PA10K2 A10K2.u6618 = [0, 282573750534, 1583812514217, 3559104574573, 3467958005266, 1136468037626, 82973979579, 0, 0, 0] := by
  rw [show A10K2.u6618 = KTree.node A10K2.t6624 (nat_lit 108653759) (nat_lit 14180918075) (nat_lit 0) A10K2.t6625 from rfl, totK_node, tot6624, tot6625]
  decide +kernel

theorem arows6619 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6619 = true := by
  rw [show A10K2.u6619 = KTree.node A10K2.t6626 (nat_lit 108728420) (nat_lit 11027559133) (nat_lit 0) A10K2.t6627 from rfl, allE_node, rows6626, irow6619, rows6627]
  all_goals rfl

theorem atot6619 : totK PA10K2 A10K2.u6619 = [0, 514783079173, 2500273836059, 4198897531754, 2507050036622, 430554163559, 12473006693, 0, 0, 0] := by
  rw [show A10K2.u6619 = KTree.node A10K2.t6626 (nat_lit 108728420) (nat_lit 11027559133) (nat_lit 0) A10K2.t6627 from rfl, totK_node, tot6626, tot6627]
  decide +kernel

theorem arows6621 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6621 = true := by
  rw [show A10K2.u6621 = KTree.node A10K2.t6628 (nat_lit 108735679) (nat_lit 14099527719) (nat_lit 0) A10K2.t6629 from rfl, allE_node, rows6628, irow6621, rows6629]
  all_goals rfl

theorem atot6621 : totK PA10K2 A10K2.u6621 = [0, 666699837680, 2930601521504, 4032380529507, 1900152545415, 305541822002, 20300850681, 0, 0, 0] := by
  rw [show A10K2.u6621 = KTree.node A10K2.t6628 (nat_lit 108735679) (nat_lit 14099527719) (nat_lit 0) A10K2.t6629 from rfl, totK_node, tot6628, tot6629]
  decide +kernel

theorem arows6622 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6622 = true := by
  rw [show A10K2.u6622 = KTree.node A10K2.t6630 (nat_lit 108749235) (nat_lit 8236344417) (nat_lit 0) A10K2.t6631 from rfl, allE_node, rows6630, irow6622, rows6631]
  all_goals rfl

theorem atot6622 : totK PA10K2 A10K2.u6622 = [0, 670718022137, 2792781228526, 3933394436065, 2098226714507, 361479569363, 11151418702, 0, 0, 0] := by
  rw [show A10K2.u6622 = KTree.node A10K2.t6630 (nat_lit 108749235) (nat_lit 8236344417) (nat_lit 0) A10K2.t6631 from rfl, totK_node, tot6630, tot6631]
  decide +kernel

theorem arows6625 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6625 = true := by
  rw [show A10K2.u6625 = KTree.node A10K2.t6632 (nat_lit 108753522) (nat_lit 7792494334) (nat_lit 0) A10K2.t6633 from rfl, allE_node, rows6632, irow6625, rows6633]
  all_goals rfl

theorem atot6625 : totK PA10K2 A10K2.u6625 = [0, 203085421841, 1811048127339, 4251950279605, 3237057427153, 590384321922, 13816090359, 0, 0, 0] := by
  rw [show A10K2.u6625 = KTree.node A10K2.t6632 (nat_lit 108753522) (nat_lit 7792494334) (nat_lit 0) A10K2.t6633 from rfl, totK_node, tot6632, tot6633]
  decide +kernel

theorem arows6626 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6626 = true := by
  rw [show A10K2.u6626 = KTree.node A10K2.t6634 (nat_lit 108759614) (nat_lit 14461487753) (nat_lit 0) A10K2.t6635 from rfl, allE_node, rows6634, irow6626, rows6635]
  all_goals rfl

theorem atot6626 : totK PA10K2 A10K2.u6626 = [0, 0, 681893813510, 3046985034717, 4288013491217, 1868337579848, 160792921903, 0, 0, 0] := by
  rw [show A10K2.u6626 = KTree.node A10K2.t6634 (nat_lit 108759614) (nat_lit 14461487753) (nat_lit 0) A10K2.t6635 from rfl, totK_node, tot6634, tot6635]
  decide +kernel

theorem arows6628 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6628 = true := by
  rw [show A10K2.u6628 = KTree.node A10K2.t6636 (nat_lit 108766945) (nat_lit 2933868175) (nat_lit 0) A10K2.t6637 from rfl, allE_node, rows6636, irow6628, rows6637]
  all_goals rfl

theorem atot6628 : totK PA10K2 A10K2.u6628 = [0, 0, 780174937305, 3141221920240, 4025266900861, 1723138989206, 214768478834, 6632180018, 0, 0] := by
  rw [show A10K2.u6628 = KTree.node A10K2.t6636 (nat_lit 108766945) (nat_lit 2933868175) (nat_lit 0) A10K2.t6637 from rfl, totK_node, tot6636, tot6637]
  decide +kernel

theorem arows6629 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6629 = true := by
  rw [show A10K2.u6629 = KTree.node A10K2.t6638 (nat_lit 108772564) (nat_lit 9642727511) (nat_lit 0) A10K2.t6639 from rfl, allE_node, rows6638, irow6629, rows6639]
  all_goals rfl

theorem atot6629 : totK PA10K2 A10K2.u6629 = [0, 0, 551835803142, 2618329742077, 4062666237826, 2300716842213, 339160959142, 7047025452, 0, 0] := by
  rw [show A10K2.u6629 = KTree.node A10K2.t6638 (nat_lit 108772564) (nat_lit 9642727511) (nat_lit 0) A10K2.t6639 from rfl, totK_node, tot6638, tot6639]
  decide +kernel

theorem arows6633 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6633 = true := by
  rw [show A10K2.u6633 = KTree.node A10K2.t6640 (nat_lit 108785678) (nat_lit 14352618855) (nat_lit 0) A10K2.t6641 from rfl, allE_node, rows6640, irow6633, rows6641]
  all_goals rfl

theorem atot6633 : totK PA10K2 A10K2.u6633 = [0, 0, 330021797788, 2155701412155, 4211850016188, 2738373841041, 457197410105, 12224107035, 0, 0] := by
  rw [show A10K2.u6633 = KTree.node A10K2.t6640 (nat_lit 108785678) (nat_lit 14352618855) (nat_lit 0) A10K2.t6641 from rfl, totK_node, tot6640, tot6641]
  decide +kernel

theorem arows6634 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6634 = true := by
  rw [show A10K2.u6634 = KTree.node A10K2.t6642 (nat_lit 113246721) (nat_lit 10582213929) (nat_lit 0) A10K2.t6643 from rfl, allE_node, rows6642, irow6634, rows6643]
  all_goals rfl

theorem atot6634 : totK PA10K2 A10K2.u6634 = [829926626583, 2621449508646, 2387430557057, 808929581600, 1064879904184, 1347230720856, 522441368230, 48886019071, 0, 0] := by
  rw [show A10K2.u6634 = KTree.node A10K2.t6642 (nat_lit 113246721) (nat_lit 10582213929) (nat_lit 0) A10K2.t6643 from rfl, totK_node, tot6642, tot6643]
  decide +kernel

theorem arows6636 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6636 = true := by
  rw [show A10K2.u6636 = KTree.node A10K2.t6644 (nat_lit 113251254) (nat_lit 16421404435) (nat_lit 0) A10K2.t6645 from rfl, allE_node, rows6644, irow6636, rows6645]
  all_goals rfl

theorem atot6636 : totK PA10K2 A10K2.u6636 = [224246292637, 1796124784537, 3984820725128, 2942879614290, 604729186797, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u6636 = KTree.node A10K2.t6644 (nat_lit 113251254) (nat_lit 16421404435) (nat_lit 0) A10K2.t6645 from rfl, totK_node, tot6644, tot6645]
  decide +kernel

theorem arows6637 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6637 = true := by
  rw [show A10K2.u6637 = KTree.node A10K2.t6646 (nat_lit 113266696) (nat_lit 14494373409) (nat_lit 0) A10K2.t6647 from rfl, allE_node, rows6646, irow6637, rows6647]
  all_goals rfl

theorem atot6637 : totK PA10K2 A10K2.u6637 = [561092995968, 2654337640792, 3959886323705, 1903872366044, 256019247649, 6354482628, 0, 0, 0, 0] := by
  rw [show A10K2.u6637 = KTree.node A10K2.t6646 (nat_lit 113266696) (nat_lit 14494373409) (nat_lit 0) A10K2.t6647 from rfl, totK_node, tot6646, tot6647]
  decide +kernel

theorem arows6640 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6640 = true := by
  rw [show A10K2.u6640 = KTree.node A10K2.t6648 (nat_lit 113274258) (nat_lit 14128667482) (nat_lit 0) A10K2.t6649 from rfl, allE_node, rows6648, irow6640, rows6649]
  all_goals rfl

theorem atot6640 : totK PA10K2 A10K2.u6640 = [616560319149, 2812895507273, 4192683899233, 2205072893693, 335456343623, 6853348008, 0, 0, 0, 0] := by
  rw [show A10K2.u6640 = KTree.node A10K2.t6648 (nat_lit 113274258) (nat_lit 14128667482) (nat_lit 0) A10K2.t6649 from rfl, totK_node, tot6648, tot6649]
  decide +kernel

theorem arows6641 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6641 = true := by
  rw [show A10K2.u6641 = KTree.node A10K2.t6650 (nat_lit 113278962) (nat_lit 13433714546) (nat_lit 0) A10K2.t6651 from rfl, allE_node, rows6650, irow6641, rows6651]
  all_goals rfl

theorem atot6641 : totK PA10K2 A10K2.u6641 = [0, 1032274791898, 3721613499094, 3872273716839, 1154473586755, 81728738798, 0, 0, 0, 0] := by
  rw [show A10K2.u6641 = KTree.node A10K2.t6650 (nat_lit 113278962) (nat_lit 13433714546) (nat_lit 0) A10K2.t6651 from rfl, totK_node, tot6650, tot6651]
  decide +kernel

theorem arows6643 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6643 = true := by
  rw [show A10K2.u6643 = KTree.node A10K2.t6652 (nat_lit 113283513) (nat_lit 7179436958) (nat_lit 0) A10K2.t6653 from rfl, allE_node, rows6652, irow6643, rows6653]
  all_goals rfl

theorem atot6643 : totK PA10K2 A10K2.u6643 = [0, 291625312176, 2004350964385, 3929670806736, 2560007678282, 532402596715, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u6643 = KTree.node A10K2.t6652 (nat_lit 113283513) (nat_lit 7179436958) (nat_lit 0) A10K2.t6653 from rfl, totK_node, tot6652, tot6653]
  decide +kernel

theorem arows6644 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6644 = true := by
  rw [show A10K2.u6644 = KTree.node A10K2.t6654 (nat_lit 113297700) (nat_lit 14257594719) (nat_lit 0) A10K2.t6655 from rfl, allE_node, rows6654, irow6644, rows6655]
  all_goals rfl

theorem atot6644 : totK PA10K2 A10K2.u6644 = [0, 580312178592, 2681292204414, 4048521572366, 1824470375810, 173018304522, 0, 0, 0, 0] := by
  rw [show A10K2.u6644 = KTree.node A10K2.t6654 (nat_lit 113297700) (nat_lit 14257594719) (nat_lit 0) A10K2.t6655 from rfl, totK_node, tot6654, tot6655]
  decide +kernel

theorem arows6653 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6653 = true := by
  rw [show A10K2.u6653 = KTree.node A10K2.t6656 (nat_lit 113306638) (nat_lit 14689662443) (nat_lit 0) A10K2.t6657 from rfl, allE_node, rows6656, irow6653, rows6657]
  all_goals rfl

theorem atot6653 : totK PA10K2 A10K2.u6653 = [303501126640, 1623515771549, 3444732000467, 3334397734857, 1211699984678, 158208112456, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u6653 = KTree.node A10K2.t6656 (nat_lit 113306638) (nat_lit 14689662443) (nat_lit 0) A10K2.t6657 from rfl, totK_node, tot6656, tot6657]
  decide +kernel

theorem arows6654 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6654 = true := by
  rw [show A10K2.u6654 = KTree.node A10K2.t6658 (nat_lit 113380901) (nat_lit 6771011072) (nat_lit 0) A10K2.t6659 from rfl, allE_node, rows6658, irow6654, rows6659]
  all_goals rfl

theorem atot6654 : totK PA10K2 A10K2.u6654 = [456053228344, 2450305064582, 4064307940951, 2284373868060, 436833618303, 25371180993, 0, 0, 0, 0] := by
  rw [show A10K2.u6654 = KTree.node A10K2.t6658 (nat_lit 113380901) (nat_lit 6771011072) (nat_lit 0) A10K2.t6659 from rfl, totK_node, tot6658, tot6659]
  decide +kernel

theorem arows6656 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6656 = true := by
  rw [show A10K2.u6656 = KTree.node A10K2.t6660 (nat_lit 113394529) (nat_lit 8989251321) (nat_lit 0) A10K2.t6661 from rfl, allE_node, rows6660, irow6656, rows6661]
  all_goals rfl

theorem atot6656 : totK PA10K2 A10K2.u6656 = [559395152186, 2662920760380, 4069666367010, 2078195148445, 273995449391, 5460492893, 0, 0, 0, 0] := by
  rw [show A10K2.u6656 = KTree.node A10K2.t6660 (nat_lit 113394529) (nat_lit 8989251321) (nat_lit 0) A10K2.t6661 from rfl, totK_node, tot6660, tot6661]
  decide +kernel

theorem arows6657 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6657 = true := by
  rw [show A10K2.u6657 = KTree.node A10K2.t6662 (nat_lit 113410994) (nat_lit 10028977281) (nat_lit 0) A10K2.t6663 from rfl, allE_node, rows6662, irow6657, rows6663]
  all_goals rfl

theorem atot6657 : totK PA10K2 A10K2.u6657 = [0, 1034753727586, 3789907529907, 3825069704782, 972820956884, 45137667897, 0, 0, 0, 0] := by
  rw [show A10K2.u6657 = KTree.node A10K2.t6662 (nat_lit 113410994) (nat_lit 10028977281) (nat_lit 0) A10K2.t6663 from rfl, totK_node, tot6662, tot6663]
  decide +kernel

theorem arows6660 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6660 = true := by
  rw [show A10K2.u6660 = KTree.node A10K2.t6664 (nat_lit 113430565) (nat_lit 7133953813) (nat_lit 0) A10K2.t6665 from rfl, allE_node, rows6664, irow6660, rows6665]
  all_goals rfl

theorem atot6660 : totK PA10K2 A10K2.u6660 = [263701001044, 1081139105827, 2600101162422, 3534871789180, 1646748162494, 264248447455, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u6660 = KTree.node A10K2.t6664 (nat_lit 113430565) (nat_lit 7133953813) (nat_lit 0) A10K2.t6665 from rfl, totK_node, tot6664, tot6665]
  decide +kernel

theorem arows6661 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6661 = true := by
  rw [show A10K2.u6661 = KTree.node A10K2.t6666 (nat_lit 113446348) (nat_lit 6322575519) (nat_lit 0) A10K2.t6667 from rfl, allE_node, rows6666, irow6661, rows6667]
  all_goals rfl

theorem atot6661 : totK PA10K2 A10K2.u6661 = [514692062441, 2627224138529, 4066032389453, 2177888445371, 414470665991, 25351274858, 0, 0, 0, 0] := by
  rw [show A10K2.u6661 = KTree.node A10K2.t6666 (nat_lit 113446348) (nat_lit 6322575519) (nat_lit 0) A10K2.t6667 from rfl, totK_node, tot6666, tot6667]
  decide +kernel

theorem arows6663 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6663 = true := by
  rw [show A10K2.u6663 = KTree.node A10K2.t6668 (nat_lit 113452706) (nat_lit 14485505501) (nat_lit 0) A10K2.t6669 from rfl, allE_node, rows6668, irow6663, rows6669]
  all_goals rfl

theorem atot6663 : totK PA10K2 A10K2.u6663 = [590865579489, 2718685033312, 4147283416182, 2198799347188, 296313569873, 5459593153, 0, 0, 0, 0] := by
  rw [show A10K2.u6663 = KTree.node A10K2.t6668 (nat_lit 113452706) (nat_lit 14485505501) (nat_lit 0) A10K2.t6669 from rfl, totK_node, tot6668, tot6669]
  decide +kernel

theorem arows6664 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6664 = true := by
  rw [show A10K2.u6664 = KTree.node A10K2.t6670 (nat_lit 113467803) (nat_lit 8365702069) (nat_lit 0) A10K2.t6671 from rfl, allE_node, rows6670, irow6664, rows6671]
  all_goals rfl

theorem atot6664 : totK PA10K2 A10K2.u6664 = [702762968219, 2842051703134, 3925185874921, 2107491704408, 405755439776, 24852064402, 0, 0, 0, 0] := by
  rw [show A10K2.u6664 = KTree.node A10K2.t6670 (nat_lit 113467803) (nat_lit 8365702069) (nat_lit 0) A10K2.t6671 from rfl, totK_node, tot6670, tot6671]
  decide +kernel

theorem arows6668 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6668 = true := by
  rw [show A10K2.u6668 = KTree.node A10K2.t6672 (nat_lit 113472262) (nat_lit 10894672849) (nat_lit 0) A10K2.t6673 from rfl, allE_node, rows6672, irow6668, rows6673]
  all_goals rfl

theorem atot6668 : totK PA10K2 A10K2.u6668 = [165731654200, 1695378688215, 4214246824066, 3332707698232, 678669075891, 19708922258, 0, 0, 0, 0] := by
  rw [show A10K2.u6668 = KTree.node A10K2.t6672 (nat_lit 113472262) (nat_lit 10894672849) (nat_lit 0) A10K2.t6673 from rfl, totK_node, tot6672, tot6673]
  decide +kernel

theorem arows6669 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6669 = true := by
  rw [show A10K2.u6669 = KTree.node A10K2.t6674 (nat_lit 113477897) (nat_lit 9697339393) (nat_lit 0) A10K2.t6675 from rfl, allE_node, rows6674, irow6669, rows6675]
  all_goals rfl

theorem atot6669 : totK PA10K2 A10K2.u6669 = [0, 792957928350, 3226632061280, 4052599590125, 1608482285339, 139930951357, 0, 0, 0, 0] := by
  rw [show A10K2.u6669 = KTree.node A10K2.t6674 (nat_lit 113477897) (nat_lit 9697339393) (nat_lit 0) A10K2.t6675 from rfl, totK_node, tot6674, tot6675]
  decide +kernel

theorem arows6671 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6671 = true := by
  rw [show A10K2.u6671 = KTree.node A10K2.t6676 (nat_lit 113484978) (nat_lit 15274955950) (nat_lit 0) A10K2.t6677 from rfl, allE_node, rows6676, irow6671, rows6677]
  all_goals rfl

theorem atot6671 : totK PA10K2 A10K2.u6671 = [0, 589830162524, 2726224613640, 4166268440094, 2135292894696, 296482156990, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u6671 = KTree.node A10K2.t6676 (nat_lit 113484978) (nat_lit 15274955950) (nat_lit 0) A10K2.t6677 from rfl, totK_node, tot6676, tot6677]
  decide +kernel

theorem arows6672 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6672 = true := by
  rw [show A10K2.u6672 = KTree.node A10K2.t6678 (nat_lit 113491440) (nat_lit 13193618643) (nat_lit 0) A10K2.t6679 from rfl, allE_node, rows6678, irow6672, rows6679]
  all_goals rfl

theorem atot6672 : totK PA10K2 A10K2.u6672 = [0, 540460088909, 2579578090324, 4118017555233, 2387125399518, 343530792689, 7047025452, 0, 0, 0] := by
  rw [show A10K2.u6672 = KTree.node A10K2.t6678 (nat_lit 113491440) (nat_lit 13193618643) (nat_lit 0) A10K2.t6679 from rfl, totK_node, tot6678, tot6679]
  decide +kernel

theorem arows6675 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6675 = true := by
  rw [show A10K2.u6675 = KTree.node A10K2.t6680 (nat_lit 113504658) (nat_lit 13556456952) (nat_lit 0) A10K2.t6681 from rfl, allE_node, rows6680, irow6675, rows6681]
  all_goals rfl

theorem atot6675 : totK PA10K2 A10K2.u6675 = [0, 327234200007, 2088781997462, 4184970543662, 2856312762244, 467319661424, 12224107035, 0, 0, 0] := by
  rw [show A10K2.u6675 = KTree.node A10K2.t6680 (nat_lit 113504658) (nat_lit 13556456952) (nat_lit 0) A10K2.t6681 from rfl, totK_node, tot6680, tot6681]
  decide +kernel

theorem arows6676 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6676 = true := by
  rw [show A10K2.u6676 = KTree.node A10K2.t6682 (nat_lit 113509190) (nat_lit 10802019512) (nat_lit 0) A10K2.t6683 from rfl, allE_node, rows6682, irow6676, rows6683]
  all_goals rfl

theorem atot6676 : totK PA10K2 A10K2.u6676 = [0, 846984141050, 2994481580853, 3460870805193, 1797301876835, 540066003119, 48886019071, 0, 0, 0] := by
  rw [show A10K2.u6676 = KTree.node A10K2.t6682 (nat_lit 113509190) (nat_lit 10802019512) (nat_lit 0) A10K2.t6683 from rfl, totK_node, tot6682, tot6683]
  decide +kernel

theorem arows6678 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6678 = true := by
  rw [show A10K2.u6678 = KTree.node A10K2.t6684 (nat_lit 113514757) (nat_lit 7005491961) (nat_lit 0) A10K2.t6685 from rfl, allE_node, rows6684, irow6678, rows6685]
  all_goals rfl

theorem atot6678 : totK PA10K2 A10K2.u6678 = [0, 287804590978, 1895057591629, 3912360302784, 2796269497634, 578350588283, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u6678 = KTree.node A10K2.t6684 (nat_lit 113514757) (nat_lit 7005491961) (nat_lit 0) A10K2.t6685 from rfl, totK_node, tot6684, tot6685]
  decide +kernel

theorem arows6679 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6679 = true := by
  rw [show A10K2.u6679 = KTree.node A10K2.t6686 (nat_lit 113529184) (nat_lit 12740465934) (nat_lit 0) A10K2.t6687 from rfl, allE_node, rows6686, irow6679, rows6687]
  all_goals rfl

theorem atot6679 : totK PA10K2 A10K2.u6679 = [0, 592186953910, 2714049395076, 3934197157307, 1867335570745, 232269528408, 5705019915, 0, 0, 0] := by
  rw [show A10K2.u6679 = KTree.node A10K2.t6686 (nat_lit 113529184) (nat_lit 12740465934) (nat_lit 0) A10K2.t6687 from rfl, totK_node, tot6686, tot6687]
  decide +kernel

theorem arows6684 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6684 = true := by
  rw [show A10K2.u6684 = KTree.node A10K2.t6688 (nat_lit 113536612) (nat_lit 8751701039) (nat_lit 0) A10K2.t6689 from rfl, allE_node, rows6688, irow6684, rows6689]
  all_goals rfl

theorem atot6684 : totK PA10K2 A10K2.u6684 = [0, 504850548399, 2569197746009, 4265824754341, 2461819025869, 363184471998, 6853348008, 0, 0, 0] := by
  rw [show A10K2.u6684 = KTree.node A10K2.t6688 (nat_lit 113536612) (nat_lit 8751701039) (nat_lit 0) A10K2.t6689 from rfl, totK_node, tot6688, tot6689]
  decide +kernel

theorem arows6685 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6685 = true := by
  rw [show A10K2.u6685 = KTree.node A10K2.t6690 (nat_lit 113541682) (nat_lit 8525339448) (nat_lit 0) A10K2.t6691 from rfl, allE_node, rows6690, irow6685, rows6691]
  all_goals rfl

theorem atot6685 : totK PA10K2 A10K2.u6685 = [0, 0, 1123153075748, 3830926702139, 3633153396643, 930853211621, 59400237386, 0, 0, 0] := by
  rw [show A10K2.u6685 = KTree.node A10K2.t6690 (nat_lit 113541682) (nat_lit 8525339448) (nat_lit 0) A10K2.t6691 from rfl, totK_node, tot6690, tot6691]
  decide +kernel

theorem arows6687 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6687 = true := by
  rw [show A10K2.u6687 = KTree.node A10K2.t6692 (nat_lit 113547427) (nat_lit 3730659302) (nat_lit 0) A10K2.t6693 from rfl, allE_node, rows6692, irow6687, rows6693]
  all_goals rfl

theorem atot6687 : totK PA10K2 A10K2.u6687 = [0, 0, 282200127425, 1953358922407, 3849586030112, 2600801598995, 544436471612, 30605747850, 0, 0] := by
  rw [show A10K2.u6687 = KTree.node A10K2.t6692 (nat_lit 113547427) (nat_lit 3730659302) (nat_lit 0) A10K2.t6693 from rfl, totK_node, tot6692, tot6693]
  decide +kernel

theorem arows6688 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6688 = true := by
  rw [show A10K2.u6688 = KTree.node A10K2.t6694 (nat_lit 113561964) (nat_lit 11739672525) (nat_lit 0) A10K2.t6695 from rfl, allE_node, rows6694, irow6688, rows6695]
  all_goals rfl

theorem atot6688 : totK PA10K2 A10K2.u6688 = [0, 0, 588628548210, 2697723193639, 3905228481295, 1757040009356, 218166434836, 5528811039, 0, 0] := by
  rw [show A10K2.u6688 = KTree.node A10K2.t6694 (nat_lit 113561964) (nat_lit 11739672525) (nat_lit 0) A10K2.t6695 from rfl, totK_node, tot6694, tot6695]
  decide +kernel

theorem arows6691 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6691 = true := by
  rw [show A10K2.u6691 = KTree.node A10K2.t6696 (nat_lit 113639524) (nat_lit 13017262675) (nat_lit 0) A10K2.t6697 from rfl, allE_node, rows6696, irow6691, rows6697]
  all_goals rfl

theorem atot6691 : totK PA10K2 A10K2.u6691 = [0, 607953017637, 2546333062174, 3775912201615, 2352998098970, 565725977804, 43911449185, 0, 0, 0] := by
  rw [show A10K2.u6691 = KTree.node A10K2.t6696 (nat_lit 113639524) (nat_lit 13017262675) (nat_lit 0) A10K2.t6697 from rfl, totK_node, tot6696, tot6697]
  decide +kernel

theorem arows6692 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6692 = true := by
  rw [show A10K2.u6692 = KTree.node A10K2.t6698 (nat_lit 113644464) (nat_lit 14652486819) (nat_lit 0) A10K2.t6699 from rfl, allE_node, rows6698, irow6692, rows6699]
  all_goals rfl

theorem atot6692 : totK PA10K2 A10K2.u6692 = [0, 427398854657, 2203685351277, 3869002101357, 2667644375683, 564178421787, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u6692 = KTree.node A10K2.t6698 (nat_lit 113644464) (nat_lit 14652486819) (nat_lit 0) A10K2.t6699 from rfl, totK_node, tot6698, tot6699]
  decide +kernel

theorem arows6694 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6694 = true := by
  rw [show A10K2.u6694 = KTree.node A10K2.t6700 (nat_lit 113660242) (nat_lit 9354169531) (nat_lit 0) A10K2.t6701 from rfl, allE_node, rows6700, irow6694, rows6701]
  all_goals rfl

theorem atot6694 : totK PA10K2 A10K2.u6694 = [0, 282722822571, 2155275219108, 4278832090264, 2462240385639, 339405153073, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u6694 = KTree.node A10K2.t6700 (nat_lit 113660242) (nat_lit 9354169531) (nat_lit 0) A10K2.t6701 from rfl, totK_node, tot6700, tot6701]
  decide +kernel

theorem arows6695 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6695 = true := by
  rw [show A10K2.u6695 = KTree.node A10K2.t6702 (nat_lit 113675872) (nat_lit 13065288330) (nat_lit 0) A10K2.t6703 from rfl, allE_node, rows6702, irow6695, rows6703]
  all_goals rfl

theorem atot6695 : totK PA10K2 A10K2.u6695 = [0, 0, 1010619221493, 3698226043218, 3785611222463, 1001789599603, 63285205505, 0, 0, 0] := by
  rw [show A10K2.u6695 = KTree.node A10K2.t6702 (nat_lit 113675872) (nat_lit 13065288330) (nat_lit 0) A10K2.t6703 from rfl, totK_node, tot6702, tot6703]
  decide +kernel

theorem arows6699 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6699 = true := by
  rw [show A10K2.u6699 = KTree.node A10K2.t6704 (nat_lit 113705056) (nat_lit 13929524539) (nat_lit 0) A10K2.t6705 from rfl, allE_node, rows6704, irow6699, rows6705]
  all_goals rfl

theorem atot6699 : totK PA10K2 A10K2.u6699 = [0, 632240834116, 2077016113464, 2751172498675, 2509894338747, 1235875576365, 186031524292, 5676195732, 0, 0] := by
  rw [show A10K2.u6699 = KTree.node A10K2.t6704 (nat_lit 113705056) (nat_lit 13929524539) (nat_lit 0) A10K2.t6705 from rfl, totK_node, tot6704, tot6705]
  decide +kernel

theorem arows6700 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6700 = true := by
  rw [show A10K2.u6700 = KTree.node A10K2.t6706 (nat_lit 113709828) (nat_lit 12210131276) (nat_lit 0) A10K2.t6707 from rfl, allE_node, rows6706, irow6700, rows6707]
  all_goals rfl

theorem atot6700 : totK PA10K2 A10K2.u6700 = [0, 444421207990, 2401448803829, 4102364099701, 2482231195895, 462693336269, 25313348169, 0, 0, 0] := by
  rw [show A10K2.u6700 = KTree.node A10K2.t6706 (nat_lit 113709828) (nat_lit 12210131276) (nat_lit 0) A10K2.t6707 from rfl, totK_node, tot6706, tot6707]
  decide +kernel

theorem arows6702 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6702 = true := by
  rw [show A10K2.u6702 = KTree.node A10K2.t6708 (nat_lit 113718500) (nat_lit 11053316474) (nat_lit 0) A10K2.t6709 from rfl, allE_node, rows6708, irow6702, rows6709]
  all_goals rfl

theorem atot6702 : totK PA10K2 A10K2.u6702 = [0, 593216047955, 2650760613196, 4138963834763, 2367815383648, 346350017627, 7151180950, 0, 0, 0] := by
  rw [show A10K2.u6702 = KTree.node A10K2.t6708 (nat_lit 113718500) (nat_lit 11053316474) (nat_lit 0) A10K2.t6709 from rfl, totK_node, tot6708, tot6709]
  decide +kernel

theorem arows6703 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6703 = true := by
  rw [show A10K2.u6703 = KTree.node A10K2.t6710 (nat_lit 113732836) (nat_lit 4806874760) (nat_lit 0) A10K2.t6711 from rfl, allE_node, rows6710, irow6703, rows6711]
  all_goals rfl

theorem atot6703 : totK PA10K2 A10K2.u6703 = [0, 582309330060, 2787335088302, 4232469534711, 2111467990417, 294392507300, 6853348008, 0, 0, 0] := by
  rw [show A10K2.u6703 = KTree.node A10K2.t6710 (nat_lit 113732836) (nat_lit 4806874760) (nat_lit 0) A10K2.t6711 from rfl, totK_node, tot6710, tot6711]
  decide +kernel

theorem arows6706 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6706 = true := by
  rw [show A10K2.u6706 = KTree.node A10K2.t6712 (nat_lit 113737407) (nat_lit 14105813498) (nat_lit 0) A10K2.t6713 from rfl, allE_node, rows6712, irow6706, rows6713]
  all_goals rfl

theorem atot6706 : totK PA10K2 A10K2.u6706 = [466373786949, 1555833620937, 2094720156312, 2582352544746, 2393672126553, 760897745361, 55515214941, 0, 0, 0] := by
  rw [show A10K2.u6706 = KTree.node A10K2.t6712 (nat_lit 113737407) (nat_lit 14105813498) (nat_lit 0) A10K2.t6713 from rfl, totK_node, tot6712, tot6713]
  decide +kernel

theorem arows6707 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6707 = true := by
  rw [show A10K2.u6707 = KTree.node A10K2.t6714 (nat_lit 113849530) (nat_lit 15083127022) (nat_lit 0) A10K2.t6715 from rfl, allE_node, rows6714, irow6707, rows6715]
  all_goals rfl

theorem atot6707 : totK PA10K2 A10K2.u6707 = [370539782661, 2111669867195, 3897185449969, 2605538334012, 504080634536, 25734533292, 0, 0, 0, 0] := by
  rw [show A10K2.u6707 = KTree.node A10K2.t6714 (nat_lit 113849530) (nat_lit 15083127022) (nat_lit 0) A10K2.t6715 from rfl, totK_node, tot6714, tot6715]
  decide +kernel

theorem arows6709 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6709 = true := by
  rw [show A10K2.u6709 = KTree.node A10K2.t6716 (nat_lit 113854272) (nat_lit 3685319757) (nat_lit 0) A10K2.t6717 from rfl, allE_node, rows6716, irow6709, rows6717]
  all_goals rfl

theorem atot6709 : totK PA10K2 A10K2.u6709 = [584970815629, 2856415765141, 4124656993044, 1839872919555, 219490050979, 6034215561, 0, 0, 0, 0] := by
  rw [show A10K2.u6709 = KTree.node A10K2.t6716 (nat_lit 113854272) (nat_lit 3685319757) (nat_lit 0) A10K2.t6717 from rfl, totK_node, tot6716, tot6717]
  decide +kernel

theorem arows6710 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6710 = true := by
  rw [show A10K2.u6710 = KTree.node A10K2.t6718 (nat_lit 113862079) (nat_lit 14245089115) (nat_lit 0) A10K2.t6719 from rfl, allE_node, rows6718, irow6710, rows6719]
  all_goals rfl

theorem atot6710 : totK PA10K2 A10K2.u6710 = [803316883883, 3095998788118, 4014647928919, 1776832294123, 238445191513, 6354482628, 0, 0, 0, 0] := by
  rw [show A10K2.u6710 = KTree.node A10K2.t6718 (nat_lit 113862079) (nat_lit 14245089115) (nat_lit 0) A10K2.t6719 from rfl, totK_node, tot6718, tot6719]
  decide +kernel

theorem arows6716 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6716 = true := by
  rw [show A10K2.u6716 = KTree.node A10K2.t6720 (nat_lit 113867924) (nat_lit 9729922159) (nat_lit 0) A10K2.t6721 from rfl, allE_node, rows6720, irow6716, rows6721]
  all_goals rfl

theorem atot6716 : totK PA10K2 A10K2.u6716 = [0, 1120610422222, 3902684805245, 3948301755823, 1101677154635, 62911296571, 0, 0, 0, 0] := by
  rw [show A10K2.u6716 = KTree.node A10K2.t6720 (nat_lit 113867924) (nat_lit 9729922159) (nat_lit 0) A10K2.t6721 from rfl, totK_node, tot6720, tot6721]
  decide +kernel

theorem arows6717 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6717 = true := by
  rw [show A10K2.u6717 = KTree.node A10K2.t6722 (nat_lit 113880566) (nat_lit 16825448452) (nat_lit 0) A10K2.t6723 from rfl, allE_node, rows6722, irow6717, rows6723]
  all_goals rfl

theorem atot6717 : totK PA10K2 A10K2.u6717 = [0, 528683678470, 2521291557107, 3880363206221, 2099486732854, 409361754817, 25565504801, 0, 0, 0] := by
  rw [show A10K2.u6717 = KTree.node A10K2.t6722 (nat_lit 113880566) (nat_lit 16825448452) (nat_lit 0) A10K2.t6723 from rfl, totK_node, tot6722, tot6723]
  decide +kernel

theorem arows6719 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6719 = true := by
  rw [show A10K2.u6719 = KTree.node A10K2.t6724 (nat_lit 113886550) (nat_lit 10983159715) (nat_lit 0) A10K2.t6725 from rfl, allE_node, rows6724, irow6719, rows6725]
  all_goals rfl

theorem atot6719 : totK PA10K2 A10K2.u6719 = [0, 584386780734, 2749984604214, 3973493639704, 1855802696408, 239347508140, 5517381808, 0, 0, 0] := by
  rw [show A10K2.u6719 = KTree.node A10K2.t6724 (nat_lit 113886550) (nat_lit 10983159715) (nat_lit 0) A10K2.t6725 from rfl, totK_node, tot6724, tot6725]
  decide +kernel

theorem arows6720 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6720 = true := by
  rw [show A10K2.u6720 = KTree.node A10K2.t6726 (nat_lit 113894298) (nat_lit 13642329574) (nat_lit 0) A10K2.t6727 from rfl, allE_node, rows6726, irow6720, rows6727]
  all_goals rfl

theorem atot6720 : totK PA10K2 A10K2.u6720 = [0, 801883039266, 3077713304086, 3911786538874, 1751533003073, 228735605305, 6121173289, 0, 0, 0] := by
  rw [show A10K2.u6720 = KTree.node A10K2.t6726 (nat_lit 113894298) (nat_lit 13642329574) (nat_lit 0) A10K2.t6727 from rfl, totK_node, tot6726, tot6727]
  decide +kernel

theorem arows6723 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6723 = true := by
  rw [show A10K2.u6723 = KTree.node A10K2.t6728 (nat_lit 113911970) (nat_lit 14142712800) (nat_lit 0) A10K2.t6729 from rfl, allE_node, rows6728, irow6723, rows6729]
  all_goals rfl

theorem atot6723 : totK PA10K2 A10K2.u6723 = [762716802215, 2944110323121, 3661305013520, 1956684518927, 576278041536, 50499610055, 0, 0, 0, 0] := by
  rw [show A10K2.u6723 = KTree.node A10K2.t6728 (nat_lit 113911970) (nat_lit 14142712800) (nat_lit 0) A10K2.t6729 from rfl, totK_node, tot6728, tot6729]
  decide +kernel

theorem arows6724 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6724 = true := by
  rw [show A10K2.u6724 = KTree.node A10K2.t6730 (nat_lit 113917148) (nat_lit 10111373352) (nat_lit 0) A10K2.t6731 from rfl, allE_node, rows6730, irow6724, rows6731]
  all_goals rfl

theorem atot6724 : totK PA10K2 A10K2.u6724 = [561217355197, 2267390270639, 3676292704127, 2625574453194, 583978210207, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u6724 = KTree.node A10K2.t6730 (nat_lit 113917148) (nat_lit 10111373352) (nat_lit 0) A10K2.t6731 from rfl, totK_node, tot6730, tot6731]
  decide +kernel

theorem arows6726 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6726 = true := by
  rw [show A10K2.u6726 = KTree.node A10K2.t6732 (nat_lit 113924883) (nat_lit 10128564230) (nat_lit 0) A10K2.t6733 from rfl, allE_node, rows6732, irow6726, rows6733]
  all_goals rfl

theorem atot6726 : totK PA10K2 A10K2.u6726 = [0, 1489192921284, 4214823509072, 3170548267075, 656933806188, 32470817489, 0, 0, 0, 0] := by
  rw [show A10K2.u6726 = KTree.node A10K2.t6732 (nat_lit 113924883) (nat_lit 10128564230) (nat_lit 0) A10K2.t6733 from rfl, totK_node, tot6732, tot6733]
  decide +kernel

theorem arows6727 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6727 = true := by
  rw [show A10K2.u6727 = KTree.node A10K2.t6734 (nat_lit 113952530) (nat_lit 14885023895) (nat_lit 0) A10K2.t6735 from rfl, allE_node, rows6734, irow6727, rows6735]
  all_goals rfl

theorem atot6727 : totK PA10K2 A10K2.u6727 = [0, 778331340001, 3345018084082, 4205623929897, 1306220695468, 85190680793, 0, 0, 0, 0] := by
  rw [show A10K2.u6727 = KTree.node A10K2.t6734 (nat_lit 113952530) (nat_lit 14885023895) (nat_lit 0) A10K2.t6735 from rfl, totK_node, tot6734, tot6735]
  decide +kernel

theorem arows6731 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6731 = true := by
  rw [show A10K2.u6731 = KTree.node A10K2.t6736 (nat_lit 113970180) (nat_lit 9857316565) (nat_lit 0) A10K2.t6737 from rfl, allE_node, rows6736, irow6731, rows6737]
  all_goals rfl

theorem atot6731 : totK PA10K2 A10K2.u6731 = [588716830688, 2445164288442, 3494948924730, 2236879152221, 885649221547, 193455434134, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u6731 = KTree.node A10K2.t6736 (nat_lit 113970180) (nat_lit 9857316565) (nat_lit 0) A10K2.t6737 from rfl, totK_node, tot6736, tot6737]
  decide +kernel

theorem arows6732 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6732 = true := by
  rw [show A10K2.u6732 = KTree.node A10K2.t6738 (nat_lit 113977079) (nat_lit 10803467008) (nat_lit 0) A10K2.t6739 from rfl, allE_node, rows6738, irow6732, rows6739]
  all_goals rfl

theorem atot6732 : totK PA10K2 A10K2.u6732 = [796258512976, 3108093348479, 3865997958803, 1789918792117, 339984031692, 24514534640, 0, 0, 0, 0] := by
  rw [show A10K2.u6732 = KTree.node A10K2.t6738 (nat_lit 113977079) (nat_lit 10803467008) (nat_lit 0) A10K2.t6739 from rfl, totK_node, tot6738, tot6739]
  decide +kernel

theorem arows6734 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6734 = true := by
  rw [show A10K2.u6734 = KTree.node A10K2.t6740 (nat_lit 113982110) (nat_lit 11905083190) (nat_lit 0) A10K2.t6741 from rfl, allE_node, rows6740, irow6734, rows6741]
  all_goals rfl

theorem atot6734 : totK PA10K2 A10K2.u6734 = [322643786975, 1928336398327, 3985151196886, 2925454005283, 620942826996, 31747192500, 0, 0, 0, 0] := by
  rw [show A10K2.u6734 = KTree.node A10K2.t6740 (nat_lit 113982110) (nat_lit 11905083190) (nat_lit 0) A10K2.t6741 from rfl, totK_node, tot6740, tot6741]
  decide +kernel

theorem arows6735 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6735 = true := by
  rw [show A10K2.u6735 = KTree.node A10K2.t6742 (nat_lit 113995378) (nat_lit 11419339156) (nat_lit 0) A10K2.t6743 from rfl, allE_node, rows6742, irow6735, rows6743]
  all_goals rfl

theorem atot6735 : totK PA10K2 A10K2.u6735 = [546006865529, 2712874004436, 4195128547084, 2256928906684, 336092704413, 6853348008, 0, 0, 0, 0] := by
  rw [show A10K2.u6735 = KTree.node A10K2.t6742 (nat_lit 113995378) (nat_lit 11419339156) (nat_lit 0) A10K2.t6743 from rfl, totK_node, tot6742, tot6743]
  decide +kernel

theorem arows6738 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6738 = true := by
  rw [show A10K2.u6738 = KTree.node A10K2.t6744 (nat_lit 113999929) (nat_lit 7339380254) (nat_lit 0) A10K2.t6745 from rfl, allE_node, rows6744, irow6738, rows6745]
  all_goals rfl

theorem atot6738 : totK PA10K2 A10K2.u6738 = [0, 914197299958, 3582595239122, 4167776716905, 1338042046035, 87576913385, 0, 0, 0, 0] := by
  rw [show A10K2.u6738 = KTree.node A10K2.t6744 (nat_lit 113999929) (nat_lit 7339380254) (nat_lit 0) A10K2.t6745 from rfl, totK_node, tot6744, tot6745]
  decide +kernel

theorem arows6739 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6739 = true := by
  rw [show A10K2.u6739 = KTree.node A10K2.t6746 (nat_lit 114007547) (nat_lit 6034448572) (nat_lit 0) A10K2.t6747 from rfl, allE_node, rows6746, irow6739, rows6747]
  all_goals rfl

theorem atot6739 : totK PA10K2 A10K2.u6739 = [0, 526229009387, 2541533781824, 4080671912244, 2293568174011, 348005955734, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u6739 = KTree.node A10K2.t6746 (nat_lit 114007547) (nat_lit 6034448572) (nat_lit 0) A10K2.t6747 from rfl, totK_node, tot6746, tot6747]
  decide +kernel

theorem arows6741 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6741 = true := by
  rw [show A10K2.u6741 = KTree.node A10K2.t6748 (nat_lit 114013856) (nat_lit 3854360531) (nat_lit 0) A10K2.t6749 from rfl, allE_node, rows6748, irow6741, rows6749]
  all_goals rfl

theorem atot6741 : totK PA10K2 A10K2.u6741 = [0, 522709576835, 2609595037548, 4158669833713, 2332011225102, 334089796307, 7047025452, 0, 0, 0] := by
  rw [show A10K2.u6741 = KTree.node A10K2.t6748 (nat_lit 114013856) (nat_lit 3854360531) (nat_lit 0) A10K2.t6749 from rfl, totK_node, tot6748, tot6749]
  decide +kernel

theorem arows6742 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6742 = true := by
  rw [show A10K2.u6742 = KTree.node A10K2.t6750 (nat_lit 114027953) (nat_lit 9265796592) (nat_lit 0) A10K2.t6751 from rfl, allE_node, rows6750, irow6742, rows6751]
  all_goals rfl

theorem atot6742 : totK PA10K2 A10K2.u6742 = [0, 615115902947, 2782292594422, 4140163857439, 2135211310871, 280053006356, 6066958478, 0, 0, 0] := by
  rw [show A10K2.u6742 = KTree.node A10K2.t6750 (nat_lit 114027953) (nat_lit 9265796592) (nat_lit 0) A10K2.t6751 from rfl, totK_node, tot6750, tot6751]
  decide +kernel

theorem arows6747 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6747 = true := by
  rw [show A10K2.u6747 = KTree.node A10K2.t6752 (nat_lit 114032561) (nat_lit 8775483592) (nat_lit 0) A10K2.t6753 from rfl, allE_node, rows6752, irow6747, rows6753]
  all_goals rfl

theorem atot6747 : totK PA10K2 A10K2.u6747 = [0, 557168161444, 2259750163159, 3526939236253, 2622390097961, 738661170223, 55043167628, 0, 0, 0] := by
  rw [show A10K2.u6747 = KTree.node A10K2.t6752 (nat_lit 114032561) (nat_lit 8775483592) (nat_lit 0) A10K2.t6753 from rfl, totK_node, tot6752, tot6753]
  decide +kernel

theorem arows6748 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6748 = true := by
  rw [show A10K2.u6748 = KTree.node A10K2.t6754 (nat_lit 114111767) (nat_lit 10525846820) (nat_lit 0) A10K2.t6755 from rfl, allE_node, rows6754, irow6748, rows6755]
  all_goals rfl

theorem atot6748 : totK PA10K2 A10K2.u6748 = [0, 292221444102, 1957384711810, 3957830618381, 2729741517384, 568560505361, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u6748 = KTree.node A10K2.t6754 (nat_lit 114111767) (nat_lit 10525846820) (nat_lit 0) A10K2.t6755 from rfl, totK_node, tot6754, tot6755]
  decide +kernel

theorem arows6750 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6750 = true := by
  rw [show A10K2.u6750 = KTree.node A10K2.t6756 (nat_lit 114116642) (nat_lit 9162599275) (nat_lit 0) A10K2.t6757 from rfl, allE_node, rows6756, irow6750, rows6757]
  all_goals rfl

theorem atot6750 : totK PA10K2 A10K2.u6750 = [0, 584970815629, 2864533652032, 4176336373282, 1816788549377, 160227975968, 0, 0, 0, 0] := by
  rw [show A10K2.u6750 = KTree.node A10K2.t6756 (nat_lit 114116642) (nat_lit 9162599275) (nat_lit 0) A10K2.t6757 from rfl, totK_node, tot6756, tot6757]
  decide +kernel

theorem arows6751 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6751 = true := by
  rw [show A10K2.u6751 = KTree.node A10K2.t6758 (nat_lit 114124461) (nat_lit 5823958061) (nat_lit 0) A10K2.t6759 from rfl, allE_node, rows6758, irow6751, rows6759]
  all_goals rfl

theorem atot6751 : totK PA10K2 A10K2.u6751 = [0, 801848663679, 3139213328555, 4024740994288, 1783092562636, 227993546187, 6239673734, 0, 0, 0] := by
  rw [show A10K2.u6751 = KTree.node A10K2.t6758 (nat_lit 114124461) (nat_lit 5823958061) (nat_lit 0) A10K2.t6759 from rfl, totK_node, tot6758, tot6759]
  decide +kernel

theorem arows6754 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6754 = true := by
  rw [show A10K2.u6754 = KTree.node A10K2.t6760 (nat_lit 114130360) (nat_lit 13936404376) (nat_lit 0) A10K2.t6761 from rfl, allE_node, rows6760, irow6754, rows6761]
  all_goals rfl

theorem atot6754 : totK PA10K2 A10K2.u6754 = [0, 0, 999202825609, 3766100150065, 4005705511714, 1135787569481, 67541609336, 0, 0, 0] := by
  rw [show A10K2.u6754 = KTree.node A10K2.t6760 (nat_lit 114130360) (nat_lit 13936404376) (nat_lit 0) A10K2.t6761 from rfl, totK_node, tot6760, tot6761]
  decide +kernel

theorem arows6755 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6755 = true := by
  rw [show A10K2.u6755 = KTree.node A10K2.t6762 (nat_lit 114143161) (nat_lit 5162985805) (nat_lit 0) A10K2.t6763 from rfl, allE_node, rows6762, irow6755, rows6763]
  all_goals rfl

theorem atot6755 : totK PA10K2 A10K2.u6755 = [0, 0, 522754546307, 2458124348338, 3773149330281, 2111164368742, 418917722352, 25565504801, 0, 0] := by
  rw [show A10K2.u6755 = KTree.node A10K2.t6762 (nat_lit 114143161) (nat_lit 5162985805) (nat_lit 0) A10K2.t6763 from rfl, totK_node, tot6762, tot6763]
  decide +kernel

theorem arows6757 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6757 = true := by
  rw [show A10K2.u6757 = KTree.node A10K2.t6764 (nat_lit 114149143) (nat_lit 9496277659) (nat_lit 0) A10K2.t6765 from rfl, allE_node, rows6764, irow6757, rows6765]
  all_goals rfl

theorem atot6757 : totK PA10K2 A10K2.u6757 = [0, 0, 578735677257, 2763961166932, 3973804866203, 1793370092021, 219658744012, 5453062850, 0, 0] := by
  rw [show A10K2.u6757 = KTree.node A10K2.t6764 (nat_lit 114149143) (nat_lit 9496277659) (nat_lit 0) A10K2.t6765 from rfl, totK_node, tot6764, tot6765]
  decide +kernel

theorem arows6758 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6758 = true := by
  rw [show A10K2.u6758 = KTree.node A10K2.t6766 (nat_lit 114157284) (nat_lit 11505835311) (nat_lit 0) A10K2.t6767 from rfl, allE_node, rows6766, irow6758, rows6767]
  all_goals rfl

theorem atot6758 : totK PA10K2 A10K2.u6758 = [0, 304922396905, 1462719222147, 3144265899332, 3310306499202, 1414311984467, 200137334590, 5685526223, 0, 0] := by
  rw [show A10K2.u6758 = KTree.node A10K2.t6766 (nat_lit 114157284) (nat_lit 11505835311) (nat_lit 0) A10K2.t6767 from rfl, totK_node, tot6766, tot6767]
  decide +kernel

theorem arows6762 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6762 = true := by
  rw [show A10K2.u6762 = KTree.node A10K2.t6768 (nat_lit 114175443) (nat_lit 10415645920) (nat_lit 0) A10K2.t6769 from rfl, allE_node, rows6768, irow6762, rows6769]
  all_goals rfl

theorem atot6762 : totK PA10K2 A10K2.u6762 = [0, 457327470340, 2552618686232, 4123609273637, 2247943721880, 432864532854, 25734533292, 0, 0, 0] := by
  rw [show A10K2.u6762 = KTree.node A10K2.t6768 (nat_lit 114175443) (nat_lit 10415645920) (nat_lit 0) A10K2.t6769 from rfl, totK_node, tot6768, tot6769]
  decide +kernel

theorem arows6763 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6763 = true := by
  rw [show A10K2.u6763 = KTree.node A10K2.t6770 (nat_lit 114181888) (nat_lit 9209523695) (nat_lit 0) A10K2.t6771 from rfl, allE_node, rows6770, irow6763, rows6771]
  all_goals rfl

theorem atot6763 : totK PA10K2 A10K2.u6763 = [0, 561217355197, 2697111558698, 4064118153399, 2106020750689, 266175314805, 6034215561, 0, 0, 0] := by
  rw [show A10K2.u6763 = KTree.node A10K2.t6770 (nat_lit 114181888) (nat_lit 9209523695) (nat_lit 0) A10K2.t6771 from rfl, totK_node, tot6770, tot6771]
  decide +kernel

theorem arows6765 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6765 = true := by
  rw [show A10K2.u6765 = KTree.node A10K2.t6772 (nat_lit 114206499) (nat_lit 10308727980) (nat_lit 0) A10K2.t6773 from rfl, allE_node, rows6772, irow6765, rows6773]
  all_goals rfl

theorem atot6765 : totK PA10K2 A10K2.u6765 = [0, 0, 1063787283562, 3833422348538, 3771363921826, 944388857814, 45583950843, 0, 0, 0] := by
  rw [show A10K2.u6765 = KTree.node A10K2.t6772 (nat_lit 114206499) (nat_lit 10308727980) (nat_lit 0) A10K2.t6773 from rfl, totK_node, tot6772, tot6773]
  decide +kernel

theorem arows6766 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6766 = true := by
  rw [show A10K2.u6766 = KTree.node A10K2.t6774 (nat_lit 114215744) (nat_lit 12826696944) (nat_lit 0) A10K2.t6775 from rfl, allE_node, rows6774, irow6766, rows6775]
  all_goals rfl

theorem atot6766 : totK PA10K2 A10K2.u6766 = [0, 187199794786, 931977954390, 2696025557040, 3667002610548, 1620847061967, 228524816560, 6239673734, 0, 0] := by
  rw [show A10K2.u6766 = KTree.node A10K2.t6774 (nat_lit 114215744) (nat_lit 12826696944) (nat_lit 0) A10K2.t6775 from rfl, totK_node, tot6774, tot6775]
  decide +kernel

theorem arows6769 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6769 = true := by
  rw [show A10K2.u6769 = KTree.node A10K2.t6776 (nat_lit 114233343) (nat_lit 13966711711) (nat_lit 0) A10K2.t6777 from rfl, allE_node, rows6776, irow6769, rows6777]
  all_goals rfl

theorem atot6769 : totK PA10K2 A10K2.u6769 = [0, 586573281161, 2689153773211, 4207164077506, 2297754179481, 338585412351, 7007974415, 0, 0, 0] := by
  rw [show A10K2.u6769 = KTree.node A10K2.t6776 (nat_lit 114233343) (nat_lit 13966711711) (nat_lit 0) A10K2.t6777 from rfl, totK_node, tot6776, tot6777]
  decide +kernel

theorem arows6770 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6770 = true := by
  rw [show A10K2.u6770 = KTree.node A10K2.t6778 (nat_lit 114240758) (nat_lit 16319387176) (nat_lit 0) A10K2.t6779 from rfl, allE_node, rows6778, irow6770, rows6779]
  all_goals rfl

theorem atot6770 : totK PA10K2 A10K2.u6770 = [0, 597257964695, 2817857194117, 4022585976421, 2038986540945, 356059645635, 20328650499, 0, 0, 0] := by
  rw [show A10K2.u6770 = KTree.node A10K2.t6778 (nat_lit 114240758) (nat_lit 16319387176) (nat_lit 0) A10K2.t6779 from rfl, totK_node, tot6778, tot6779]
  decide +kernel

theorem arows6772 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6772 = true := by
  rw [show A10K2.u6772 = KTree.node A10K2.t6780 (nat_lit 114254290) (nat_lit 14319642472) (nat_lit 0) A10K2.t6781 from rfl, allE_node, rows6780, irow6772, rows6781]
  all_goals rfl

theorem atot6772 : totK PA10K2 A10K2.u6772 = [0, 745799516381, 2919489293417, 3923379850723, 1986302192797, 319127171540, 10956717587, 0, 0, 0] := by
  rw [show A10K2.u6772 = KTree.node A10K2.t6780 (nat_lit 114254290) (nat_lit 14319642472) (nat_lit 0) A10K2.t6781 from rfl, totK_node, tot6780, tot6781]
  decide +kernel

theorem arows6773 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6773 = true := by
  rw [show A10K2.u6773 = KTree.node A10K2.t6782 (nat_lit 114258878) (nat_lit 16128367311) (nat_lit 0) A10K2.t6783 from rfl, allE_node, rows6782, irow6773, rows6783]
  all_goals rfl

theorem atot6773 : totK PA10K2 A10K2.u6773 = [0, 122360162702, 1607822894307, 4215980231427, 3402965713438, 685949644016, 19094568524, 0, 0, 0] := by
  rw [show A10K2.u6773 = KTree.node A10K2.t6782 (nat_lit 114258878) (nat_lit 16128367311) (nat_lit 0) A10K2.t6783 from rfl, totK_node, tot6782, tot6783]
  decide +kernel

theorem arows6780 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6780 = true := by
  rw [show A10K2.u6780 = KTree.node A10K2.t6784 (nat_lit 114821381) (nat_lit 7005491961) (nat_lit 0) A10K2.t6785 from rfl, allE_node, rows6784, irow6780, rows6785]
  all_goals rfl

theorem atot6780 : totK PA10K2 A10K2.u6780 = [807420204410, 3068020735653, 3496956837032, 1386248845346, 606307997496, 337104436601, 43287591117, 0, 0, 0] := by
  rw [show A10K2.u6780 = KTree.node A10K2.t6784 (nat_lit 114821381) (nat_lit 7005491961) (nat_lit 0) A10K2.t6785 from rfl, totK_node, tot6784, tot6785]
  decide +kernel

theorem arows6781 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6781 = true := by
  rw [show A10K2.u6781 = KTree.node A10K2.t6786 (nat_lit 114826309) (nat_lit 5538311811) (nat_lit 0) A10K2.t6787 from rfl, allE_node, rows6786, irow6781, rows6787]
  all_goals rfl

theorem atot6781 : totK PA10K2 A10K2.u6781 = [441487391689, 2122579319204, 3678222273522, 2552820589711, 556322826733, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u6781 = KTree.node A10K2.t6786 (nat_lit 114826309) (nat_lit 5538311811) (nat_lit 0) A10K2.t6787 from rfl, totK_node, tot6786, tot6787]
  decide +kernel

theorem arows6783 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6783 = true := by
  rw [show A10K2.u6783 = KTree.node A10K2.t6788 (nat_lit 114844058) (nat_lit 12595333336) (nat_lit 0) A10K2.t6789 from rfl, allE_node, rows6788, irow6783, rows6789]
  all_goals rfl

theorem atot6783 : totK PA10K2 A10K2.u6783 = [749392523631, 3072572893391, 4058237070169, 1715303568358, 219962220367, 6354482628, 0, 0, 0, 0] := by
  rw [show A10K2.u6783 = KTree.node A10K2.t6788 (nat_lit 114844058) (nat_lit 12595333336) (nat_lit 0) A10K2.t6789 from rfl, totK_node, tot6788, tot6789]
  decide +kernel

theorem arows6784 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6784 = true := by
  rw [show A10K2.u6784 = KTree.node A10K2.t6790 (nat_lit 114848916) (nat_lit 10065749391) (nat_lit 0) A10K2.t6791 from rfl, allE_node, rows6790, irow6784, rows6791]
  all_goals rfl

theorem atot6784 : totK PA10K2 A10K2.u6784 = [82670484671, 1411403489881, 4126727839931, 3746069083283, 857066231660, 25664960330, 0, 0, 0, 0] := by
  rw [show A10K2.u6784 = KTree.node A10K2.t6790 (nat_lit 114848916) (nat_lit 10065749391) (nat_lit 0) A10K2.t6791 from rfl, totK_node, tot6790, tot6791]
  decide +kernel

theorem arows6787 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6787 = true := by
  rw [show A10K2.u6787 = KTree.node A10K2.t6792 (nat_lit 114854448) (nat_lit 14871589384) (nat_lit 0) A10K2.t6793 from rfl, allE_node, rows6792, irow6787, rows6793]
  all_goals rfl

theorem atot6787 : totK PA10K2 A10K2.u6787 = [0, 806933121214, 3249321915409, 3950466568299, 1442036045882, 123526350336, 0, 0, 0, 0] := by
  rw [show A10K2.u6787 = KTree.node A10K2.t6792 (nat_lit 114854448) (nat_lit 14871589384) (nat_lit 0) A10K2.t6793 from rfl, totK_node, tot6792, tot6793]
  decide +kernel

theorem arows6788 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6788 = true := by
  rw [show A10K2.u6788 = KTree.node A10K2.t6794 (nat_lit 114859514) (nat_lit 7082746934) (nat_lit 0) A10K2.t6795 from rfl, allE_node, rows6794, irow6788, rows6795]
  all_goals rfl

theorem atot6788 : totK PA10K2 A10K2.u6788 = [0, 439243362846, 2192798597668, 3680050007981, 2379437345469, 533957048182, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u6788 = KTree.node A10K2.t6794 (nat_lit 114859514) (nat_lit 7082746934) (nat_lit 0) A10K2.t6795 from rfl, totK_node, tot6794, tot6795]
  decide +kernel

theorem arows6790 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6790 = true := by
  rw [show A10K2.u6790 = KTree.node A10K2.t6796 (nat_lit 114877224) (nat_lit 12158729684) (nat_lit 0) A10K2.t6797 from rfl, allE_node, rows6796, irow6790, rows6797]
  all_goals rfl

theorem atot6790 : totK PA10K2 A10K2.u6790 = [0, 831684970491, 3261198858884, 4053432911240, 1604154345830, 186175413181, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u6790 = KTree.node A10K2.t6796 (nat_lit 114877224) (nat_lit 12158729684) (nat_lit 0) A10K2.t6797 from rfl, totK_node, tot6796, tot6797]
  decide +kernel

theorem arows6791 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6791 = true := by
  rw [show A10K2.u6791 = KTree.node A10K2.t6798 (nat_lit 114895172) (nat_lit 8045591402) (nat_lit 0) A10K2.t6799 from rfl, allE_node, rows6798, irow6791, rows6799]
  all_goals rfl

theorem atot6791 : totK PA10K2 A10K2.u6791 = [811040046021, 3143766173973, 3768619793297, 1648793674395, 366420413007, 37674914273, 0, 0, 0, 0] := by
  rw [show A10K2.u6791 = KTree.node A10K2.t6798 (nat_lit 114895172) (nat_lit 8045591402) (nat_lit 0) A10K2.t6799 from rfl, totK_node, tot6798, tot6799]
  decide +kernel

theorem arows6795 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6795 = true := by
  rw [show A10K2.u6795 = KTree.node A10K2.t6800 (nat_lit 114900152) (nat_lit 10602554422) (nat_lit 0) A10K2.t6801 from rfl, allE_node, rows6800, irow6795, rows6801]
  all_goals rfl

theorem atot6795 : totK PA10K2 A10K2.u6795 = [444538933688, 2150303788522, 3725878764506, 2603981126279, 572752737109, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u6795 = KTree.node A10K2.t6800 (nat_lit 114900152) (nat_lit 10602554422) (nat_lit 0) A10K2.t6801 from rfl, totK_node, tot6800, tot6801]
  decide +kernel

theorem arows6796 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6796 = true := by
  rw [show A10K2.u6796 = KTree.node A10K2.t6802 (nat_lit 114909741) (nat_lit 4062911479) (nat_lit 0) A10K2.t6803 from rfl, allE_node, rows6802, irow6796, rows6803]
  all_goals rfl

theorem atot6796 : totK PA10K2 A10K2.u6796 = [832772492727, 3136216057294, 3999019370087, 1714389041653, 222441950626, 6354482628, 0, 0, 0, 0] := by
  rw [show A10K2.u6796 = KTree.node A10K2.t6802 (nat_lit 114909741) (nat_lit 4062911479) (nat_lit 0) A10K2.t6803 from rfl, totK_node, tot6802, tot6803]
  decide +kernel

theorem arows6798 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6798 = true := by
  rw [show A10K2.u6798 = KTree.node A10K2.t6804 (nat_lit 114914656) (nat_lit 2802412525) (nat_lit 0) A10K2.t6805 from rfl, allE_node, rows6804, irow6798, rows6805]
  all_goals rfl

theorem atot6798 : totK PA10K2 A10K2.u6798 = [0, 1301352019550, 4120315243240, 3807831618039, 966595504489, 36970624857, 0, 0, 0, 0] := by
  rw [show A10K2.u6798 = KTree.node A10K2.t6804 (nat_lit 114914656) (nat_lit 2802412525) (nat_lit 0) A10K2.t6805 from rfl, totK_node, tot6804, tot6805]
  decide +kernel

theorem arows6799 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6799 = true := by
  rw [show A10K2.u6799 = KTree.node A10K2.t6806 (nat_lit 114928397) (nat_lit 4152171913) (nat_lit 0) A10K2.t6807 from rfl, allE_node, rows6806, irow6799, rows6807]
  all_goals rfl

theorem atot6799 : totK PA10K2 A10K2.u6799 = [0, 809951607557, 3271761763134, 4008363931710, 1440612977403, 120285827351, 0, 0, 0, 0] := by
  rw [show A10K2.u6799 = KTree.node A10K2.t6806 (nat_lit 114928397) (nat_lit 4152171913) (nat_lit 0) A10K2.t6807 from rfl, totK_node, tot6806, tot6807]
  decide +kernel

theorem arows6802 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6802 = true := by
  rw [show A10K2.u6802 = KTree.node A10K2.t6808 (nat_lit 114934931) (nat_lit 10993652984) (nat_lit 0) A10K2.t6809 from rfl, allE_node, rows6808, irow6802, rows6809]
  all_goals rfl

theorem atot6802 : totK PA10K2 A10K2.u6802 = [0, 443746184518, 2221548343226, 3707701476664, 2425780523973, 549659987952, 31082886609, 0, 0, 0] := by
  rw [show A10K2.u6802 = KTree.node A10K2.t6808 (nat_lit 114934931) (nat_lit 10993652984) (nat_lit 0) A10K2.t6809 from rfl, totK_node, tot6808, tot6809]
  decide +kernel

theorem arows6803 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6803 = true := by
  rw [show A10K2.u6803 = KTree.node A10K2.t6810 (nat_lit 114943196) (nat_lit 10711939941) (nat_lit 0) A10K2.t6811 from rfl, allE_node, rows6810, irow6803, rows6811]
  all_goals rfl

theorem atot6803 : totK PA10K2 A10K2.u6803 = [0, 832238493652, 3268197768123, 4025196951251, 1609375226426, 189612442081, 6121173289, 0, 0, 0] := by
  rw [show A10K2.u6803 = KTree.node A10K2.t6810 (nat_lit 114943196) (nat_lit 10711939941) (nat_lit 0) A10K2.t6811 from rfl, totK_node, tot6810, tot6811]
  decide +kernel

theorem arows6805 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6805 = true := by
  rw [show A10K2.u6805 = KTree.node A10K2.t6812 (nat_lit 115018247) (nat_lit 11759694273) (nat_lit 0) A10K2.t6813 from rfl, allE_node, rows6812, irow6805, rows6813]
  all_goals rfl

theorem atot6805 : totK PA10K2 A10K2.u6805 = [762038499923, 3003291664958, 3719703290103, 1792204618947, 461473990708, 44535473551, 0, 0, 0, 0] := by
  rw [show A10K2.u6805 = KTree.node A10K2.t6812 (nat_lit 115018247) (nat_lit 11759694273) (nat_lit 0) A10K2.t6813 from rfl, totK_node, tot6812, tot6813]
  decide +kernel

theorem arows6806 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6806 = true := by
  rw [show A10K2.u6806 = KTree.node A10K2.t6814 (nat_lit 115023358) (nat_lit 15919448127) (nat_lit 0) A10K2.t6815 from rfl, allE_node, rows6814, irow6806, rows6815]
  all_goals rfl

theorem atot6806 : totK PA10K2 A10K2.u6806 = [537990084717, 2416390863453, 3814353568168, 2363482209343, 506364388497, 29778615803, 0, 0, 0, 0] := by
  rw [show A10K2.u6806 = KTree.node A10K2.t6814 (nat_lit 115023358) (nat_lit 15919448127) (nat_lit 0) A10K2.t6815 from rfl, totK_node, tot6814, tot6815]
  decide +kernel

theorem arows6811 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6811 = true := by
  rw [show A10K2.u6811 = KTree.node A10K2.t6816 (nat_lit 115029716) (nat_lit 11086387258) (nat_lit 0) A10K2.t6817 from rfl, allE_node, rows6816, irow6811, rows6817]
  all_goals rfl

theorem atot6811 : totK PA10K2 A10K2.u6811 = [394551071534, 2122179318952, 3962423105860, 2798033164654, 573259610340, 30428024596, 0, 0, 0, 0] := by
  rw [show A10K2.u6811 = KTree.node A10K2.t6816 (nat_lit 115029716) (nat_lit 11086387258) (nat_lit 0) A10K2.t6817 from rfl, totK_node, tot6816, tot6817]
  decide +kernel

theorem arows6812 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6812 = true := by
  rw [show A10K2.u6812 = KTree.node A10K2.t6818 (nat_lit 115043376) (nat_lit 14797286462) (nat_lit 0) A10K2.t6819 from rfl, allE_node, rows6818, irow6812, rows6819]
  all_goals rfl

theorem atot6812 : totK PA10K2 A10K2.u6812 = [729656749638, 3153970646522, 4277855649629, 1750657912703, 161745695867, 0, 0, 0, 0, 0] := by
  rw [show A10K2.u6812 = KTree.node A10K2.t6818 (nat_lit 115043376) (nat_lit 14797286462) (nat_lit 0) A10K2.t6819 from rfl, totK_node, tot6818, tot6819]
  decide +kernel

theorem arows6814 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6814 = true := by
  rw [show A10K2.u6814 = KTree.node A10K2.t6820 (nat_lit 115047866) (nat_lit 14274413006) (nat_lit 0) A10K2.t6821 from rfl, allE_node, rows6820, irow6814, rows6821]
  all_goals rfl

theorem atot6814 : totK PA10K2 A10K2.u6814 = [0, 909492395386, 3533755836103, 4063662729519, 1283208260750, 88278425695, 0, 0, 0, 0] := by
  rw [show A10K2.u6814 = KTree.node A10K2.t6820 (nat_lit 115047866) (nat_lit 14274413006) (nat_lit 0) A10K2.t6821 from rfl, totK_node, tot6820, tot6821]
  decide +kernel

theorem arows6815 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6815 = true := by
  rw [show A10K2.u6815 = KTree.node A10K2.t6822 (nat_lit 115052549) (nat_lit 6422715266) (nat_lit 0) A10K2.t6823 from rfl, allE_node, rows6822, irow6815, rows6823]
  all_goals rfl

theorem atot6815 : totK PA10K2 A10K2.u6815 = [0, 464281269216, 2503336944610, 4218435863437, 2295421967067, 307011016098, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u6815 = KTree.node A10K2.t6822 (nat_lit 115052549) (nat_lit 6422715266) (nat_lit 0) A10K2.t6823 from rfl, totK_node, tot6822, tot6823]
  decide +kernel

theorem arows6818 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6818 = true := by
  rw [show A10K2.u6818 = KTree.node A10K2.t6824 (nat_lit 115059775) (nat_lit 14210038504) (nat_lit 0) A10K2.t6825 from rfl, allE_node, rows6824, irow6818, rows6825]
  all_goals rfl

theorem atot6818 : totK PA10K2 A10K2.u6818 = [0, 764753336025, 3104612476622, 4016046420606, 1761225547635, 182923544393, 0, 0, 0, 0] := by
  rw [show A10K2.u6818 = KTree.node A10K2.t6824 (nat_lit 115059775) (nat_lit 14210038504) (nat_lit 0) A10K2.t6825 from rfl, totK_node, tot6824, tot6825]
  decide +kernel

theorem arows6819 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6819 = true := by
  rw [show A10K2.u6819 = KTree.node A10K2.t6826 (nat_lit 115073606) (nat_lit 13415364663) (nat_lit 0) A10K2.t6827 from rfl, allE_node, rows6826, irow6819, rows6827]
  all_goals rfl

theorem atot6819 : totK PA10K2 A10K2.u6819 = [0, 877965611113, 3228843905488, 3878326741671, 1699416052645, 230136980687, 7047025452, 0, 0, 0] := by
  rw [show A10K2.u6819 = KTree.node A10K2.t6826 (nat_lit 115073606) (nat_lit 13415364663) (nat_lit 0) A10K2.t6827 from rfl, totK_node, tot6826, tot6827]
  decide +kernel

theorem arows6821 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6821 = true := by
  rw [show A10K2.u6821 = KTree.node A10K2.t6828 (nat_lit 115078354) (nat_lit 15577006858) (nat_lit 0) A10K2.t6829 from rfl, allE_node, rows6828, irow6821, rows6829]
  all_goals rfl

theorem atot6821 : totK PA10K2 A10K2.u6821 = [0, 17179869184, 1392049950043, 4176037935224, 3583367524565, 750972126373, 23799715721, 0, 0, 0] := by
  rw [show A10K2.u6821 = KTree.node A10K2.t6828 (nat_lit 115078354) (nat_lit 15577006858) (nat_lit 0) A10K2.t6829 from rfl, totK_node, tot6828, tot6829]
  decide +kernel

theorem arows6822 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6822 = true := by
  rw [show A10K2.u6822 = KTree.node A10K2.t6830 (nat_lit 115083781) (nat_lit 6779813526) (nat_lit 0) A10K2.t6831 from rfl, allE_node, rows6830, irow6822, rows6831]
  all_goals rfl

theorem atot6822 : totK PA10K2 A10K2.u6822 = [0, 806920830838, 3151295463052, 3784292516235, 1551817417536, 320642803757, 37310410385, 0, 0, 0] := by
  rw [show A10K2.u6822 = KTree.node A10K2.t6830 (nat_lit 115083781) (nat_lit 6779813526) (nat_lit 0) A10K2.t6831 from rfl, totK_node, tot6830, tot6831]
  decide +kernel

theorem arows6826 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6826 = true := by
  rw [show A10K2.u6826 = KTree.node A10K2.t6832 (nat_lit 115088630) (nat_lit 16090426362) (nat_lit 0) A10K2.t6833 from rfl, allE_node, rows6832, irow6826, rows6833]
  all_goals rfl

theorem atot6826 : totK PA10K2 A10K2.u6826 = [0, 441487391689, 2204373712756, 3711832320974, 2472130337088, 548737744723, 30780440178, 0, 0, 0] := by
  rw [show A10K2.u6826 = KTree.node A10K2.t6832 (nat_lit 115088630) (nat_lit 16090426362) (nat_lit 0) A10K2.t6833 from rfl, totK_node, tot6832, tot6833]
  decide +kernel

theorem arows6827 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6827 = true := by
  rw [show A10K2.u6827 = KTree.node A10K2.t6834 (nat_lit 115106312) (nat_lit 14437532646) (nat_lit 0) A10K2.t6835 from rfl, allE_node, rows6834, irow6827, rows6835]
  all_goals rfl

theorem atot6827 : totK PA10K2 A10K2.u6827 = [0, 830559755663, 3172948528654, 4001606450104, 1661873004035, 205393162483, 5705019915, 0, 0, 0] := by
  rw [show A10K2.u6827 = KTree.node A10K2.t6834 (nat_lit 115106312) (nat_lit 14437532646) (nat_lit 0) A10K2.t6835 from rfl, totK_node, tot6834, tot6835]
  decide +kernel

theorem arows6829 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6829 = true := by
  rw [show A10K2.u6829 = KTree.node A10K2.t6836 (nat_lit 115111305) (nat_lit 8118592989) (nat_lit 0) A10K2.t6837 from rfl, allE_node, rows6836, irow6829, rows6837]
  all_goals rfl

theorem atot6829 : totK PA10K2 A10K2.u6829 = [0, 0, 1248410403273, 4013152324497, 3839645832799, 1028526175076, 62351816811, 0, 0, 0] := by
  rw [show A10K2.u6829 = KTree.node A10K2.t6836 (nat_lit 115111305) (nat_lit 8118592989) (nat_lit 0) A10K2.t6837 from rfl, totK_node, tot6836, tot6837]
  decide +kernel

theorem arows6830 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6830 = true := by
  rw [show A10K2.u6830 = KTree.node A10K2.t6838 (nat_lit 115117057) (nat_lit 10511097145) (nat_lit 0) A10K2.t6839 from rfl, allE_node, rows6838, irow6830, rows6839]
  all_goals rfl

theorem atot6830 : totK PA10K2 A10K2.u6830 = [0, 0, 704887493065, 3099428802832, 4002737063900, 1586814755182, 162001274760, 0, 0, 0] := by
  rw [show A10K2.u6830 = KTree.node A10K2.t6838 (nat_lit 115117057) (nat_lit 10511097145) (nat_lit 0) A10K2.t6839 from rfl, totK_node, tot6838, tot6839]
  decide +kernel

theorem arows6833 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6833 = true := by
  rw [show A10K2.u6833 = KTree.node A10K2.t6840 (nat_lit 115131141) (nat_lit 6920038188) (nat_lit 0) A10K2.t6841 from rfl, allE_node, rows6840, irow6833, rows6841]
  all_goals rfl

theorem atot6833 : totK PA10K2 A10K2.u6833 = [0, 0, 755457766870, 3150697022548, 3901454419209, 1482217182425, 179970645935, 7007974415, 0, 0] := by
  rw [show A10K2.u6833 = KTree.node A10K2.t6840 (nat_lit 115131141) (nat_lit 6920038188) (nat_lit 0) A10K2.t6841 from rfl, totK_node, tot6840, tot6841]
  decide +kernel

theorem arows6834 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6834 = true := by
  rw [show A10K2.u6834 = KTree.node A10K2.t6842 (nat_lit 115142596) (nat_lit 5798669713) (nat_lit 0) A10K2.t6843 from rfl, allE_node, rows6842, irow6834, rows6843]
  all_goals rfl

theorem atot6834 : totK PA10K2 A10K2.u6834 = [0, 513260446086, 2267499924403, 3628007318572, 2683176192027, 775297252099, 56820615133, 0, 0, 0] := by
  rw [show A10K2.u6834 = KTree.node A10K2.t6842 (nat_lit 115142596) (nat_lit 5798669713) (nat_lit 0) A10K2.t6843 from rfl, totK_node, tot6842, tot6843]
  decide +kernel

theorem arows6836 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6836 = true := by
  rw [show A10K2.u6836 = KTree.node A10K2.t6844 (nat_lit 115160468) (nat_lit 9123488976) (nat_lit 0) A10K2.t6845 from rfl, allE_node, rows6844, irow6836, rows6845]
  all_goals rfl

theorem atot6836 : totK PA10K2 A10K2.u6836 = [0, 297281370121, 1942208634855, 3996380935309, 2807387444405, 583031192674, 31306924438, 0, 0, 0] := by
  rw [show A10K2.u6836 = KTree.node A10K2.t6844 (nat_lit 115160468) (nat_lit 9123488976) (nat_lit 0) A10K2.t6845 from rfl, totK_node, tot6844, tot6845]
  decide +kernel

theorem arows6837 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6837 = true := by
  rw [show A10K2.u6837 = KTree.node A10K2.t6846 (nat_lit 115166051) (nat_lit 8657417264) (nat_lit 0) A10K2.t6847 from rfl, allE_node, rows6846, irow6837, rows6847]
  all_goals rfl

theorem atot6837 : totK PA10K2 A10K2.u6837 = [0, 662049089282, 2865587727900, 4041952810680, 1899979720016, 249816195855, 6239673734, 0, 0, 0] := by
  rw [show A10K2.u6837 = KTree.node A10K2.t6846 (nat_lit 115166051) (nat_lit 8657417264) (nat_lit 0) A10K2.t6847 from rfl, totK_node, tot6846, tot6847]
  decide +kernel

theorem arows6843 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6843 = true := by
  rw [show A10K2.u6843 = KTree.node A10K2.t6848 (nat_lit 115174925) (nat_lit 3626366397) (nat_lit 0) A10K2.t6849 from rfl, allE_node, rows6848, irow6843, rows6849]
  all_goals rfl

theorem atot6843 : totK PA10K2 A10K2.u6843 = [0, 613762948205, 2811773312407, 4227007081007, 2214886656726, 304226188080, 6279851884, 0, 0, 0] := by
  rw [show A10K2.u6843 = KTree.node A10K2.t6848 (nat_lit 115174925) (nat_lit 3626366397) (nat_lit 0) A10K2.t6849 from rfl, totK_node, tot6848, tot6849]
  decide +kernel

theorem arows6844 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6844 = true := by
  rw [show A10K2.u6844 = KTree.node A10K2.t6850 (nat_lit 115188951) (nat_lit 12513327563) (nat_lit 0) A10K2.t6851 from rfl, allE_node, rows6850, irow6844, rows6851]
  all_goals rfl

theorem atot6844 : totK PA10K2 A10K2.u6844 = [0, 0, 902538870891, 3495536014756, 3997481251009, 1272378409678, 87826231206, 0, 0, 0] := by
  rw [show A10K2.u6844 = KTree.node A10K2.t6850 (nat_lit 115188951) (nat_lit 12513327563) (nat_lit 0) A10K2.t6851 from rfl, totK_node, tot6850, tot6851]
  decide +kernel

theorem arows6846 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6846 = true := by
  rw [show A10K2.u6846 = KTree.node A10K2.t6852 (nat_lit 115193572) (nat_lit 11714882760) (nat_lit 0) A10K2.t6853 from rfl, allE_node, rows6852, irow6846, rows6853]
  all_goals rfl

theorem atot6846 : totK PA10K2 A10K2.u6846 = [0, 0, 595709577051, 2689462122362, 4036021496842, 2104937988355, 303927538966, 7151180950, 0, 0] := by
  rw [show A10K2.u6846 = KTree.node A10K2.t6852 (nat_lit 115193572) (nat_lit 11714882760) (nat_lit 0) A10K2.t6853 from rfl, totK_node, tot6852, tot6853]
  decide +kernel

theorem arows6847 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6847 = true := by
  rw [show A10K2.u6847 = KTree.node A10K2.t6854 (nat_lit 115205822) (nat_lit 15400017336) (nat_lit 0) A10K2.t6855 from rfl, allE_node, rows6854, irow6847, rows6855]
  all_goals rfl

theorem atot6847 : totK PA10K2 A10K2.u6847 = [0, 128889292512, 1203811165507, 3608137863169, 3842703610706, 1201749033232, 75189232056, 0, 0, 0] := by
  rw [show A10K2.u6847 = KTree.node A10K2.t6854 (nat_lit 115205822) (nat_lit 15400017336) (nat_lit 0) A10K2.t6855 from rfl, totK_node, tot6854, tot6855]
  decide +kernel

theorem arows6850 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6850 = true := by
  rw [show A10K2.u6850 = KTree.node A10K2.t6856 (nat_lit 115281310) (nat_lit 15580346291) (nat_lit 0) A10K2.t6857 from rfl, allE_node, rows6856, irow6850, rows6857]
  all_goals rfl

theorem atot6850 : totK PA10K2 A10K2.u6850 = [0, 632647818666, 2773995771094, 3920955217992, 2039827054160, 359961744547, 11991740650, 0, 0, 0] := by
  rw [show A10K2.u6850 = KTree.node A10K2.t6856 (nat_lit 115281310) (nat_lit 15580346291) (nat_lit 0) A10K2.t6857 from rfl, totK_node, tot6856, tot6857]
  decide +kernel

theorem arows6851 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6851 = true := by
  rw [show A10K2.u6851 = KTree.node A10K2.t6858 (nat_lit 115287734) (nat_lit 15853422771) (nat_lit 0) A10K2.t6859 from rfl, allE_node, rows6858, irow6851, rows6859]
  all_goals rfl

theorem atot6851 : totK PA10K2 A10K2.u6851 = [0, 765263111575, 3140919689053, 4073774698165, 1725130073773, 168152154381, 0, 0, 0, 0] := by
  rw [show A10K2.u6851 = KTree.node A10K2.t6858 (nat_lit 115287734) (nat_lit 15853422771) (nat_lit 0) A10K2.t6859 from rfl, totK_node, tot6858, tot6859]
  decide +kernel

theorem arows6853 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6853 = true := by
  rw [show A10K2.u6853 = KTree.node A10K2.t6860 (nat_lit 115292956) (nat_lit 10797822029) (nat_lit 0) A10K2.t6861 from rfl, allE_node, rows6860, irow6853, rows6861]
  all_goals rfl

theorem atot6853 : totK PA10K2 A10K2.u6853 = [0, 390246659287, 2136777037386, 4058890266708, 2758309030234, 477383579676, 12219140272, 0, 0, 0] := by
  rw [show A10K2.u6853 = KTree.node A10K2.t6860 (nat_lit 115292956) (nat_lit 10797822029) (nat_lit 0) A10K2.t6861 from rfl, totK_node, tot6860, tot6861]
  decide +kernel

theorem arows6854 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6854 = true := by
  rw [show A10K2.u6854 = KTree.node A10K2.t6862 (nat_lit 115306170) (nat_lit 14829804677) (nat_lit 0) A10K2.t6863 from rfl, allE_node, rows6862, irow6854, rows6863]
  all_goals rfl

theorem atot6854 : totK PA10K2 A10K2.u6854 = [0, 504204779070, 2592901095666, 4241382333310, 2369414832648, 316548355335, 6772895877, 0, 0, 0] := by
  rw [show A10K2.u6854 = KTree.node A10K2.t6862 (nat_lit 115306170) (nat_lit 14829804677) (nat_lit 0) A10K2.t6863 from rfl, totK_node, tot6862, tot6863]
  decide +kernel

theorem arows6858 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6858 = true := by
  rw [show A10K2.u6858 = KTree.node A10K2.t6864 (nat_lit 115310670) (nat_lit 10892379551) (nat_lit 0) A10K2.t6865 from rfl, allE_node, rows6864, irow6858, rows6865]
  all_goals rfl

theorem atot6858 : totK PA10K2 A10K2.u6858 = [0, 0, 1087282521554, 3710112885488, 3884174076031, 1129902834079, 68058142506, 0, 0, 0] := by
  rw [show A10K2.u6858 = KTree.node A10K2.t6864 (nat_lit 115310670) (nat_lit 10892379551) (nat_lit 0) A10K2.t6865 from rfl, totK_node, tot6864, tot6865]
  decide +kernel

theorem arows6859 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6859 = true := by
  rw [show A10K2.u6859 = KTree.node A10K2.t6866 (nat_lit 115316854) (nat_lit 14780183716) (nat_lit 0) A10K2.t6867 from rfl, allE_node, rows6866, irow6859, rows6867]
  all_goals rfl

theorem atot6859 : totK PA10K2 A10K2.u6859 = [0, 0, 366650377627, 2397045043947, 4385799079239, 2340677368646, 284871461903, 6318667960, 0, 0] := by
  rw [show A10K2.u6859 = KTree.node A10K2.t6866 (nat_lit 115316854) (nat_lit 14780183716) (nat_lit 0) A10K2.t6867 from rfl, totK_node, tot6866, tot6867]
  decide +kernel

theorem arows6861 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6861 = true := by
  rw [show A10K2.u6861 = KTree.node A10K2.t6868 (nat_lit 115324189) (nat_lit 5914705366) (nat_lit 0) A10K2.t6869 from rfl, allE_node, rows6868, irow6861, rows6869]
  all_goals rfl

theorem atot6861 : totK PA10K2 A10K2.u6861 = [0, 0, 657005399934, 2835461469086, 4020260076353, 2107208023532, 277152403198, 6439430839, 0, 0] := by
  rw [show A10K2.u6861 = KTree.node A10K2.t6868 (nat_lit 115324189) (nat_lit 5914705366) (nat_lit 0) A10K2.t6869 from rfl, totK_node, tot6868, tot6869]
  decide +kernel

theorem arows6862 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6862 = true := by
  rw [show A10K2.u6862 = KTree.node A10K2.t6870 (nat_lit 115338405) (nat_lit 2449594218) (nat_lit 0) A10K2.t6871 from rfl, allE_node, rows6870, irow6862, rows6871]
  all_goals rfl

theorem atot6862 : totK PA10K2 A10K2.u6862 = [0, 0, 625687488018, 2948978898299, 4177157342765, 1839568630839, 222390655356, 6021244195, 0, 0] := by
  rw [show A10K2.u6862 = KTree.node A10K2.t6870 (nat_lit 115338405) (nat_lit 2449594218) (nat_lit 0) A10K2.t6871 from rfl, totK_node, tot6870, tot6871]
  decide +kernel

theorem arows6865 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6865 = true := by
  rw [show A10K2.u6865 = KTree.node A10K2.t6872 (nat_lit 115342994) (nat_lit 15287944291) (nat_lit 0) A10K2.t6873 from rfl, allE_node, rows6872, irow6865, rows6873]
  all_goals rfl

theorem atot6865 : totK PA10K2 A10K2.u6865 = [0, 442864610808, 1469325418554, 2037565542258, 2614325190080, 2467571524276, 760907316813, 54997142734, 0, 0] := by
  rw [show A10K2.u6865 = KTree.node A10K2.t6872 (nat_lit 115342994) (nat_lit 15287944291) (nat_lit 0) A10K2.t6873 from rfl, totK_node, tot6872, tot6873]
  decide +kernel

theorem arows6866 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6866 = true := by
  rw [show A10K2.u6866 = KTree.node A10K2.t6874 (nat_lit 115347462) (nat_lit 14882822736) (nat_lit 0) A10K2.t6875 from rfl, allE_node, rows6874, irow6866, rows6875]
  all_goals rfl

theorem atot6866 : totK PA10K2 A10K2.u6866 = [0, 400066482960, 2175551332866, 3872995715458, 2452277530973, 470872778691, 25371180993, 0, 0, 0] := by
  rw [show A10K2.u6866 = KTree.node A10K2.t6874 (nat_lit 115347462) (nat_lit 14882822736) (nat_lit 0) A10K2.t6875 from rfl, totK_node, tot6874, tot6875]
  decide +kernel

theorem arows6868 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6868 = true := by
  rw [show A10K2.u6868 = KTree.node A10K2.t6876 (nat_lit 115361036) (nat_lit 12062723343) (nat_lit 0) A10K2.t6877 from rfl, allE_node, rows6876, irow6868, rows6877]
  all_goals rfl

theorem atot6868 : totK PA10K2 A10K2.u6868 = [0, 582481005154, 2831472495551, 4080333380839, 1809276712053, 217017331364, 5460492893, 0, 0, 0] := by
  rw [show A10K2.u6868 = KTree.node A10K2.t6876 (nat_lit 115361036) (nat_lit 12062723343) (nat_lit 0) A10K2.t6877 from rfl, totK_node, tot6876, tot6877]
  decide +kernel

theorem arows6869 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6869 = true := by
  rw [show A10K2.u6869 = KTree.node A10K2.t6878 (nat_lit 115369106) (nat_lit 15612683191) (nat_lit 0) A10K2.t6879 from rfl, allE_node, rows6878, irow6869, rows6879]
  all_goals rfl

theorem atot6869 : totK PA10K2 A10K2.u6869 = [0, 802361088133, 3105466928623, 3970056418626, 1751237217428, 212322856316, 5976421810, 0, 0, 0] := by
  rw [show A10K2.u6869 = KTree.node A10K2.t6878 (nat_lit 115369106) (nat_lit 15612683191) (nat_lit 0) A10K2.t6879 from rfl, totK_node, tot6878, tot6879]
  decide +kernel

theorem arows6874 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6874 = true := by
  rw [show A10K2.u6874 = KTree.node A10K2.t6880 (nat_lit 115375172) (nat_lit 9153486125) (nat_lit 0) A10K2.t6881 from rfl, allE_node, rows6880, irow6874, rows6881]
  all_goals rfl

theorem atot6874 : totK PA10K2 A10K2.u6874 = [0, 0, 1118371094788, 3904533017031, 3927904008480, 1076868042481, 62643765077, 0, 0, 0] := by
  rw [show A10K2.u6874 = KTree.node A10K2.t6880 (nat_lit 115375172) (nat_lit 9153486125) (nat_lit 0) A10K2.t6881 from rfl, totK_node, tot6880, tot6881]
  decide +kernel

theorem arows6875 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6875 = true := by
  rw [show A10K2.u6875 = KTree.node A10K2.t6882 (nat_lit 115379668) (nat_lit 2858122425) (nat_lit 0) A10K2.t6883 from rfl, allE_node, rows6882, irow6875, rows6883]
  all_goals rfl

theorem atot6875 : totK PA10K2 A10K2.u6875 = [0, 0, 526962436300, 2575459085126, 3939118019933, 2030101999463, 400017279536, 25239774317, 0, 0] := by
  rw [show A10K2.u6875 = KTree.node A10K2.t6882 (nat_lit 115379668) (nat_lit 2858122425) (nat_lit 0) A10K2.t6883 from rfl, totK_node, tot6882, tot6883]
  decide +kernel

theorem arows6877 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6877 = true := by
  rw [show A10K2.u6877 = KTree.node A10K2.t6884 (nat_lit 115393038) (nat_lit 12891167819) (nat_lit 0) A10K2.t6885 from rfl, allE_node, rows6884, irow6877, rows6885]
  all_goals rfl

theorem atot6877 : totK PA10K2 A10K2.u6877 = [0, 0, 580312178592, 2687628846004, 3852822058769, 1798072423432, 237430095637, 5410721913, 0, 0] := by
  rw [show A10K2.u6877 = KTree.node A10K2.t6884 (nat_lit 115393038) (nat_lit 12891167819) (nat_lit 0) A10K2.t6885 from rfl, totK_node, tot6884, tot6885]
  decide +kernel

theorem arows6878 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6878 = true := by
  rw [show A10K2.u6878 = KTree.node A10K2.t6886 (nat_lit 115401224) (nat_lit 14437532646) (nat_lit 0) A10K2.t6887 from rfl, allE_node, rows6886, irow6878, rows6887]
  all_goals rfl

theorem atot6878 : totK PA10K2 A10K2.u6878 = [0, 0, 800637287452, 3126144042733, 3974005073866, 1659993653667, 205733304727, 5546304973, 0, 0] := by
  rw [show A10K2.u6878 = KTree.node A10K2.t6886 (nat_lit 115401224) (nat_lit 14437532646) (nat_lit 0) A10K2.t6887 from rfl, totK_node, tot6886, tot6887]
  decide +kernel

theorem arows6881 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6881 = true := by
  rw [show A10K2.u6881 = KTree.node A10K2.t6888 (nat_lit 115476707) (nat_lit 8816751777) (nat_lit 0) A10K2.t6889 from rfl, allE_node, rows6888, irow6881, rows6889]
  all_goals rfl

theorem atot6881 : totK PA10K2 A10K2.u6881 = [0, 759554354984, 2981904226828, 3759764109827, 1812262673806, 468833592170, 43709387373, 0, 0, 0] := by
  rw [show A10K2.u6881 = KTree.node A10K2.t6888 (nat_lit 115476707) (nat_lit 8816751777) (nat_lit 0) A10K2.t6889 from rfl, totK_node, tot6888, tot6889]
  decide +kernel

theorem arows6882 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6882 = true := by
  rw [show A10K2.u6882 = KTree.node A10K2.t6890 (nat_lit 115482040) (nat_lit 14170053537) (nat_lit 0) A10K2.t6891 from rfl, allE_node, rows6890, irow6882, rows6891]
  all_goals rfl

theorem atot6882 : totK PA10K2 A10K2.u6882 = [0, 559395152186, 2398050211253, 3664684070529, 2432172180113, 540301764295, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u6882 = KTree.node A10K2.t6890 (nat_lit 115482040) (nat_lit 14170053537) (nat_lit 0) A10K2.t6891 from rfl, totK_node, tot6890, tot6891]
  decide +kernel

theorem arows6884 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6884 = true := by
  rw [show A10K2.u6884 = KTree.node A10K2.t6892 (nat_lit 115507209) (nat_lit 9807832142) (nat_lit 0) A10K2.t6893 from rfl, allE_node, rows6892, irow6884, rows6893]
  all_goals rfl

theorem atot6884 : totK PA10K2 A10K2.u6884 = [0, 0, 1278464903892, 4114294515553, 3355137914596, 684928092630, 31987755669, 0, 0, 0] := by
  rw [show A10K2.u6884 = KTree.node A10K2.t6892 (nat_lit 115507209) (nat_lit 9807832142) (nat_lit 0) A10K2.t6893 from rfl, totK_node, tot6892, tot6893]
  decide +kernel

theorem arows6885 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6885 = true := by
  rw [show A10K2.u6885 = KTree.node A10K2.t6894 (nat_lit 115525632) (nat_lit 15064410632) (nat_lit 0) A10K2.t6895 from rfl, allE_node, rows6894, irow6885, rows6895]
  all_goals rfl

theorem atot6885 : totK PA10K2 A10K2.u6885 = [0, 0, 775468037942, 3289974252162, 4136189232660, 1316632178921, 95042903292, 0, 0, 0] := by
  rw [show A10K2.u6885 = KTree.node A10K2.t6894 (nat_lit 115525632) (nat_lit 15064410632) (nat_lit 0) A10K2.t6895 from rfl, totK_node, tot6894, tot6895]
  decide +kernel

theorem arows6889 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6889 = true := by
  rw [show A10K2.u6889 = KTree.node A10K2.t6896 (nat_lit 115542125) (nat_lit 5483478668) (nat_lit 0) A10K2.t6897 from rfl, allE_node, rows6896, irow6889, rows6897]
  all_goals rfl

theorem atot6889 : totK PA10K2 A10K2.u6889 = [0, 793104720795, 3014325475707, 3493221166483, 1652891546616, 642446374652, 129624216436, 5976421810, 0, 0] := by
  rw [show A10K2.u6889 = KTree.node A10K2.t6896 (nat_lit 115542125) (nat_lit 5483478668) (nat_lit 0) A10K2.t6897 from rfl, totK_node, tot6896, tot6897]
  decide +kernel

theorem arows6890 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6890 = true := by
  rw [show A10K2.u6890 = KTree.node A10K2.t6898 (nat_lit 115547319) (nat_lit 14879290484) (nat_lit 0) A10K2.t6899 from rfl, allE_node, rows6898, irow6890, rows6899]
  all_goals rfl

theorem atot6890 : totK PA10K2 A10K2.u6890 = [0, 590865579489, 2383254706870, 3779492846942, 2477383384802, 532861806744, 30810868011, 0, 0, 0] := by
  rw [show A10K2.u6890 = KTree.node A10K2.t6898 (nat_lit 115547319) (nat_lit 14879290484) (nat_lit 0) A10K2.t6899 from rfl, totK_node, tot6898, tot6899]
  decide +kernel

theorem arows6892 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6892 = true := by
  rw [show A10K2.u6892 = KTree.node A10K2.t6900 (nat_lit 115555399) (nat_lit 11187645446) (nat_lit 0) A10K2.t6901 from rfl, allE_node, rows6900, irow6892, rows6901]
  all_goals rfl

theorem atot6892 : totK PA10K2 A10K2.u6892 = [0, 426592152996, 2456148905314, 4219030218075, 2472516764203, 427197946384, 12681556880, 0, 0, 0] := by
  rw [show A10K2.u6892 = KTree.node A10K2.t6900 (nat_lit 115555399) (nat_lit 11187645446) (nat_lit 0) A10K2.t6901 from rfl, totK_node, tot6900, tot6901]
  decide +kernel

theorem arows6893 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6893 = true := by
  rw [show A10K2.u6893 = KTree.node A10K2.t6902 (nat_lit 115568576) (nat_lit 14627760404) (nat_lit 0) A10K2.t6903 from rfl, allE_node, rows6902, irow6893, rows6903]
  all_goals rfl

theorem atot6893 : totK PA10K2 A10K2.u6893 = [0, 441902469423, 2306174056654, 4112434175318, 2647624576150, 492238094574, 13816090359, 0, 0, 0] := by
  rw [show A10K2.u6893 = KTree.node A10K2.t6902 (nat_lit 115568576) (nat_lit 14627760404) (nat_lit 0) A10K2.t6903 from rfl, totK_node, tot6902, tot6903]
  decide +kernel

theorem arows6896 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6896 = true := by
  rw [show A10K2.u6896 = KTree.node A10K2.t6904 (nat_lit 115573139) (nat_lit 6470238243) (nat_lit 0) A10K2.t6905 from rfl, allE_node, rows6904, irow6896, rows6905]
  all_goals rfl

theorem atot6896 : totK PA10K2 A10K2.u6896 = [0, 0, 1119447731441, 3779600082442, 3778634000779, 1115628260755, 80261166969, 0, 0, 0] := by
  rw [show A10K2.u6896 = KTree.node A10K2.t6904 (nat_lit 115573139) (nat_lit 6470238243) (nat_lit 0) A10K2.t6905 from rfl, totK_node, tot6904, tot6905]
  decide +kernel

theorem arows6897 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6897 = true := by
  rw [show A10K2.u6897 = KTree.node A10K2.t6906 (nat_lit 115578949) (nat_lit 6142726048) (nat_lit 0) A10K2.t6907 from rfl, allE_node, rows6906, irow6897, rows6907]
  all_goals rfl

theorem atot6897 : totK PA10K2 A10K2.u6897 = [0, 0, 283437181451, 2228668992448, 4441298806665, 2552400776619, 348712710258, 6904928264, 0, 0] := by
  rw [show A10K2.u6897 = KTree.node A10K2.t6906 (nat_lit 115578949) (nat_lit 6142726048) (nat_lit 0) A10K2.t6907 from rfl, totK_node, tot6906, tot6907]
  decide +kernel

theorem arows6899 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6899 = true := by
  rw [show A10K2.u6899 = KTree.node A10K2.t6908 (nat_lit 115586723) (nat_lit 10547801615) (nat_lit 0) A10K2.t6909 from rfl, allE_node, rows6908, irow6899, rows6909]
  all_goals rfl

theorem atot6899 : totK PA10K2 A10K2.u6899 = [0, 0, 592503457474, 2697427882840, 4146670207591, 2298459461596, 292312556849, 6766355402, 0, 0] := by
  rw [show A10K2.u6899 = KTree.node A10K2.t6908 (nat_lit 115586723) (nat_lit 10547801615) (nat_lit 0) A10K2.t6909 from rfl, totK_node, tot6908, tot6909]
  decide +kernel

theorem arows6900 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6900 = true := by
  rw [show A10K2.u6900 = KTree.node A10K2.t6910 (nat_lit 115600996) (nat_lit 7629360561) (nat_lit 0) A10K2.t6911 from rfl, allE_node, rows6910, irow6900, rows6911]
  all_goals rfl

theorem atot6900 : totK PA10K2 A10K2.u6900 = [0, 0, 581583812515, 2716903148024, 4158990347295, 2168445245834, 273633013744, 6066958478, 0, 0] := by
  rw [show A10K2.u6900 = KTree.node A10K2.t6910 (nat_lit 115600996) (nat_lit 7629360561) (nat_lit 0) A10K2.t6911 from rfl, totK_node, tot6910, tot6911]
  decide +kernel

theorem arows6908 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6908 = true := by
  rw [show A10K2.u6908 = KTree.node A10K2.t6912 (nat_lit 115605580) (nat_lit 10804632683) (nat_lit 0) A10K2.t6913 from rfl, allE_node, rows6912, irow6908, rows6913]
  all_goals rfl

theorem atot6908 : totK PA10K2 A10K2.u6908 = [0, 0, 554885253651, 2337211303512, 3481456475065, 2436248865920, 730855144275, 55043167628, 0, 0] := by
  rw [show A10K2.u6908 = KTree.node A10K2.t6912 (nat_lit 115605580) (nat_lit 10804632683) (nat_lit 0) A10K2.t6913 from rfl, totK_node, tot6912, tot6913]
  decide +kernel

theorem arows6909 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6909 = true := by
  rw [show A10K2.u6909 = KTree.node A10K2.t6914 (nat_lit 115610110) (nat_lit 15046685384) (nat_lit 0) A10K2.t6915 from rfl, allE_node, rows6914, irow6909, rows6915]
  all_goals rfl

theorem atot6909 : totK PA10K2 A10K2.u6909 = [0, 0, 292098887399, 1915423101834, 4014616544421, 2778082411111, 553950404725, 30831673886, 0, 0] := by
  rw [show A10K2.u6909 = KTree.node A10K2.t6914 (nat_lit 115610110) (nat_lit 15046685384) (nat_lit 0) A10K2.t6915 from rfl, totK_node, tot6914, tot6915]
  decide +kernel

theorem arows6911 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6911 = true := by
  rw [show A10K2.u6911 = KTree.node A10K2.t6916 (nat_lit 115624234) (nat_lit 11960336315) (nat_lit 0) A10K2.t6917 from rfl, allE_node, rows6916, irow6911, rows6917]
  all_goals rfl

theorem atot6911 : totK PA10K2 A10K2.u6911 = [0, 0, 582481005154, 2695827386912, 3988259382251, 1824620242247, 185032796014, 0, 0, 0] := by
  rw [show A10K2.u6911 = KTree.node A10K2.t6916 (nat_lit 115624234) (nat_lit 11960336315) (nat_lit 0) A10K2.t6917 from rfl, totK_node, tot6916, tot6917]
  decide +kernel

theorem arows6912 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6912 = true := by
  rw [show A10K2.u6912 = KTree.node A10K2.t6918 (nat_lit 115632057) (nat_lit 6174911498) (nat_lit 0) A10K2.t6919 from rfl, allE_node, rows6918, irow6912, rows6919]
  all_goals rfl

theorem atot6912 : totK PA10K2 A10K2.u6912 = [0, 0, 802361088133, 3237167488838, 4074178873322, 1701177320800, 199644439853, 5705019915, 0, 0] := by
  rw [show A10K2.u6912 = KTree.node A10K2.t6918 (nat_lit 115632057) (nat_lit 6174911498) (nat_lit 0) A10K2.t6919 from rfl, totK_node, tot6918, tot6919]
  decide +kernel

theorem arows6915 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6915 = true := by
  rw [show A10K2.u6915 = KTree.node A10K2.t6920 (nat_lit 115638212) (nat_lit 5160861025) (nat_lit 0) A10K2.t6921 from rfl, allE_node, rows6920, irow6915, rows6921]
  all_goals rfl

theorem atot6915 : totK PA10K2 A10K2.u6915 = [0, 0, 0, 1049077805625, 3767740925626, 3839611628093, 1022750301542, 60698249753, 0, 0] := by
  rw [show A10K2.u6915 = KTree.node A10K2.t6920 (nat_lit 115638212) (nat_lit 5160861025) (nat_lit 0) A10K2.t6921 from rfl, totK_node, tot6920, tot6921]
  decide +kernel

theorem arows6916 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6916 = true := by
  rw [show A10K2.u6916 = KTree.node A10K2.t6922 (nat_lit 115642825) (nat_lit 6837354806) (nat_lit 0) A10K2.t6923 from rfl, allE_node, rows6922, irow6916, rows6923]
  all_goals rfl

theorem atot6916 : totK PA10K2 A10K2.u6916 = [0, 0, 0, 531504348499, 2583005700245, 3972726226414, 2045707368085, 310334363447, 7237400819, 0] := by
  rw [show A10K2.u6916 = KTree.node A10K2.t6922 (nat_lit 115642825) (nat_lit 6837354806) (nat_lit 0) A10K2.t6923 from rfl, totK_node, tot6922, tot6923]
  decide +kernel

theorem arows6918 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6918 = true := by
  rw [show A10K2.u6918 = KTree.node A10K2.t6924 (nat_lit 115663141) (nat_lit 6960559082) (nat_lit 0) A10K2.t6925 from rfl, allE_node, rows6924, irow6918, rows6925]
  all_goals rfl

theorem atot6918 : totK PA10K2 A10K2.u6918 = [0, 0, 0, 1112503917576, 3884800451646, 3798284356439, 868606402181, 35808270795, 0, 0] := by
  rw [show A10K2.u6918 = KTree.node A10K2.t6924 (nat_lit 115663141) (nat_lit 6960559082) (nat_lit 0) A10K2.t6925 from rfl, totK_node, tot6924, tot6925]
  decide +kernel

theorem arows6919 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6919 = true := by
  rw [show A10K2.u6919 = KTree.node A10K2.t6926 (nat_lit 115738976) (nat_lit 12546697981) (nat_lit 0) A10K2.t6927 from rfl, allE_node, rows6926, irow6919, rows6927]
  all_goals rfl

theorem atot6919 : totK PA10K2 A10K2.u6919 = [0, 0, 759378239577, 3145886677689, 3995304326229, 1619037096319, 256036120795, 22228207860, 0, 0] := by
  rw [show A10K2.u6919 = KTree.node A10K2.t6926 (nat_lit 115738976) (nat_lit 12546697981) (nat_lit 0) A10K2.t6927 from rfl, totK_node, tot6926, tot6927]
  decide +kernel

theorem arows6923 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6923 = true := by
  rw [show A10K2.u6923 = KTree.node A10K2.t6928 (nat_lit 115753585) (nat_lit 7450143760) (nat_lit 0) A10K2.t6929 from rfl, allE_node, rows6928, irow6923, rows6929]
  all_goals rfl

theorem atot6923 : totK PA10K2 A10K2.u6923 = [0, 0, 558696455288, 2752878288119, 4108264366393, 1795784018788, 219921502868, 5460492893, 0, 0] := by
  rw [show A10K2.u6923 = KTree.node A10K2.t6928 (nat_lit 115753585) (nat_lit 7450143760) (nat_lit 0) A10K2.t6929 from rfl, totK_node, tot6928, tot6929]
  decide +kernel

theorem arows6924 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6924 = true := by
  rw [show A10K2.u6924 = KTree.node A10K2.t6930 (nat_lit 115802964) (nat_lit 9240128698) (nat_lit 0) A10K2.t6931 from rfl, allE_node, rows6930, irow6924, rows6931]
  all_goals rfl

theorem atot6924 : totK PA10K2 A10K2.u6924 = [0, 0, 793104720795, 3053145909819, 3856415520764, 1694564433940, 213454498033, 6354482628, 0, 0] := by
  rw [show A10K2.u6924 = KTree.node A10K2.t6930 (nat_lit 115802964) (nat_lit 9240128698) (nat_lit 0) A10K2.t6931 from rfl, totK_node, tot6930, tot6931]
  decide +kernel

theorem arows6926 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6926 = true := by
  rw [show A10K2.u6926 = KTree.node A10K2.t6932 (nat_lit 115809431) (nat_lit 14038371709) (nat_lit 0) A10K2.t6933 from rfl, allE_node, rows6932, irow6926, rows6933]
  all_goals rfl

theorem atot6926 : totK PA10K2 A10K2.u6926 = [0, 0, 545310583547, 2490927354271, 3982641167931, 2418485704966, 421884250718, 12473006693, 0, 0] := by
  rw [show A10K2.u6926 = KTree.node A10K2.t6932 (nat_lit 115809431) (nat_lit 14038371709) (nat_lit 0) A10K2.t6933 from rfl, totK_node, tot6932, tot6933]
  decide +kernel

theorem arows6927 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6927 = true := by
  rw [show A10K2.u6927 = KTree.node A10K2.t6934 (nat_lit 115817636) (nat_lit 6525050845) (nat_lit 0) A10K2.t6935 from rfl, allE_node, rows6934, irow6927, rows6935]
  all_goals rfl

theorem atot6927 : totK PA10K2 A10K2.u6927 = [0, 0, 586034796747, 2702397567521, 4190043066425, 2264203479483, 298084611981, 6860445330, 0, 0] := by
  rw [show A10K2.u6927 = KTree.node A10K2.t6934 (nat_lit 115817636) (nat_lit 6525050845) (nat_lit 0) A10K2.t6935 from rfl, totK_node, tot6934, tot6935]
  decide +kernel

theorem arows6930 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6930 = true := by
  rw [show A10K2.u6930 = KTree.node A10K2.t6936 (nat_lit 115830783) (nat_lit 13968960306) (nat_lit 0) A10K2.t6937 from rfl, allE_node, rows6936, irow6930, rows6937]
  all_goals rfl

theorem atot6930 : totK PA10K2 A10K2.u6930 = [0, 0, 327737319032, 2160166405341, 4219430137155, 2768090109561, 487188999650, 13231026584, 0, 0] := by
  rw [show A10K2.u6930 = KTree.node A10K2.t6936 (nat_lit 115830783) (nat_lit 13968960306) (nat_lit 0) A10K2.t6937 from rfl, totK_node, tot6936, tot6937]
  decide +kernel

theorem arows6931 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6931 = true := by
  rw [show A10K2.u6931 = KTree.node A10K2.t6938 (nat_lit 115942898) (nat_lit 14298392437) (nat_lit 0) A10K2.t6939 from rfl, allE_node, rows6938, irow6931, rows6939]
  all_goals rfl

theorem atot6931 : totK PA10K2 A10K2.u6931 = [0, 765706699962, 2562894952217, 2668288117599, 1712584900130, 1405667471575, 529680438566, 49137536365, 0, 0] := by
  rw [show A10K2.u6931 = KTree.node A10K2.t6938 (nat_lit 115942898) (nat_lit 14298392437) (nat_lit 0) A10K2.t6939 from rfl, totK_node, tot6938, tot6939]
  decide +kernel

theorem arows6933 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6933 = true := by
  rw [show A10K2.u6933 = KTree.node A10K2.t6940 (nat_lit 115947398) (nat_lit 14458004004) (nat_lit 0) A10K2.t6941 from rfl, allE_node, rows6940, irow6933, rows6941]
  all_goals rfl

theorem atot6933 : totK PA10K2 A10K2.u6933 = [0, 172569951494, 1676516973755, 4059513365313, 3085636649245, 641248343257, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u6933 = KTree.node A10K2.t6940 (nat_lit 115947398) (nat_lit 14458004004) (nat_lit 0) A10K2.t6941 from rfl, totK_node, tot6940, tot6941]
  decide +kernel

theorem arows6934 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6934 = true := by
  rw [show A10K2.u6934 = KTree.node A10K2.t6942 (nat_lit 115952452) (nat_lit 12863214254) (nat_lit 0) A10K2.t6943 from rfl, allE_node, rows6942, irow6934, rows6943]
  all_goals rfl

theorem atot6934 : totK PA10K2 A10K2.u6934 = [0, 671461745162, 2768163458462, 3894591583198, 1868350712042, 229699460994, 5982052406, 0, 0, 0] := by
  rw [show A10K2.u6934 = KTree.node A10K2.t6942 (nat_lit 115952452) (nat_lit 12863214254) (nat_lit 0) A10K2.t6943 from rfl, totK_node, tot6942, tot6943]
  decide +kernel

theorem arows6939 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6939 = true := by
  rw [show A10K2.u6939 = KTree.node A10K2.t6944 (nat_lit 115961060) (nat_lit 9104023529) (nat_lit 0) A10K2.t6945 from rfl, allE_node, rows6944, irow6939, rows6945]
  all_goals rfl

theorem atot6939 : totK PA10K2 A10K2.u6939 = [0, 613166546329, 2944574675959, 4261031126335, 2069350085838, 300242855912, 6574379264, 0, 0, 0] := by
  rw [show A10K2.u6939 = KTree.node A10K2.t6944 (nat_lit 115961060) (nat_lit 9104023529) (nat_lit 0) A10K2.t6945 from rfl, totK_node, tot6944, tot6945]
  decide +kernel

theorem arows6940 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6940 = true := by
  rw [show A10K2.u6940 = KTree.node A10K2.t6946 (nat_lit 115965895) (nat_lit 14283163292) (nat_lit 0) A10K2.t6947 from rfl, allE_node, rows6946, irow6940, rows6947]
  all_goals rfl

theorem atot6940 : totK PA10K2 A10K2.u6940 = [0, 0, 994344470126, 3672911361947, 3848273525871, 1174272847433, 82549656006, 0, 0, 0] := by
  rw [show A10K2.u6940 = KTree.node A10K2.t6946 (nat_lit 115965895) (nat_lit 14283163292) (nat_lit 0) A10K2.t6947 from rfl, totK_node, tot6946, tot6947]
  decide +kernel

theorem arows6942 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6942 = true := by
  rw [show A10K2.u6942 = KTree.node A10K2.t6948 (nat_lit 115979605) (nat_lit 6602162936) (nat_lit 0) A10K2.t6949 from rfl, allE_node, rows6948, irow6942, rows6949]
  all_goals rfl

theorem atot6942 : totK PA10K2 A10K2.u6942 = [0, 0, 292243983067, 1996836582323, 3978390924567, 2634424994901, 552047196284, 31082886609, 0, 0] := by
  rw [show A10K2.u6942 = KTree.node A10K2.t6948 (nat_lit 115979605) (nat_lit 6602162936) (nat_lit 0) A10K2.t6949 from rfl, totK_node, tot6948, tot6949]
  decide +kernel

theorem arows6943 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6943 = true := by
  rw [show A10K2.u6943 = KTree.node A10K2.t6950 (nat_lit 115984605) (nat_lit 5747407848) (nat_lit 0) A10K2.t6951 from rfl, allE_node, rows6950, irow6943, rows6951]
  all_goals rfl

theorem atot6943 : totK PA10K2 A10K2.u6943 = [0, 0, 584386780734, 2822305916137, 4149297872131, 1704051046373, 134258374271, 0, 0, 0] := by
  rw [show A10K2.u6943 = KTree.node A10K2.t6950 (nat_lit 115984605) (nat_lit 5747407848) (nat_lit 0) A10K2.t6951 from rfl, totK_node, tot6950, tot6951]
  decide +kernel

theorem arows6946 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6946 = true := by
  rw [show A10K2.u6946 = KTree.node A10K2.t6952 (nat_lit 115992360) (nat_lit 5479538957) (nat_lit 0) A10K2.t6953 from rfl, allE_node, rows6952, irow6946, rows6953]
  all_goals rfl

theorem atot6946 : totK PA10K2 A10K2.u6946 = [0, 209557633364, 1319781843432, 3204148517947, 3525861139453, 1480305047211, 205639391269, 5885702948, 0, 0] := by
  rw [show A10K2.u6946 = KTree.node A10K2.t6952 (nat_lit 115992360) (nat_lit 5479538957) (nat_lit 0) A10K2.t6953 from rfl, totK_node, tot6952, tot6953]
  decide +kernel

theorem arows6947 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6947 = true := by
  rw [show A10K2.u6947 = KTree.node A10K2.t6954 (nat_lit 116010387) (nat_lit 10460993823) (nat_lit 0) A10K2.t6955 from rfl, allE_node, rows6954, irow6947, rows6955]
  all_goals rfl

theorem atot6947 : totK PA10K2 A10K2.u6947 = [0, 553159168851, 2646140950762, 4050399579711, 2184628251312, 419418742217, 25734533292, 0, 0, 0] := by
  rw [show A10K2.u6947 = KTree.node A10K2.t6954 (nat_lit 116010387) (nat_lit 10460993823) (nat_lit 0) A10K2.t6955 from rfl, totK_node, tot6954, tot6955]
  decide +kernel

theorem arows6949 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6949 = true := by
  rw [show A10K2.u6949 = KTree.node A10K2.t6956 (nat_lit 116016827) (nat_lit 7041197025) (nat_lit 0) A10K2.t6957 from rfl, allE_node, rows6956, irow6949, rows6957]
  all_goals rfl

theorem atot6949 : totK PA10K2 A10K2.u6949 = [0, 561217355197, 2703037235695, 4090303254149, 2090885086362, 269032583034, 5809256573, 0, 0, 0] := by
  rw [show A10K2.u6949 = KTree.node A10K2.t6956 (nat_lit 116016827) (nat_lit 7041197025) (nat_lit 0) A10K2.t6957 from rfl, totK_node, tot6956, tot6957]
  decide +kernel

theorem arows6950 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6950 = true := by
  rw [show A10K2.u6950 = KTree.node A10K2.t6958 (nat_lit 116041450) (nat_lit 12287459258) (nat_lit 0) A10K2.t6959 from rfl, allE_node, rows6958, irow6950, rows6959]
  all_goals rfl

theorem atot6950 : totK PA10K2 A10K2.u6950 = [0, 0, 1044005101767, 3818263657386, 3824488837059, 949639794191, 45698759736, 0, 0, 0] := by
  rw [show A10K2.u6950 = KTree.node A10K2.t6958 (nat_lit 116041450) (nat_lit 12287459258) (nat_lit 0) A10K2.t6959 from rfl, totK_node, tot6958, tot6959]
  decide +kernel

theorem arows6954 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6954 = true := by
  rw [show A10K2.u6954 = KTree.node A10K2.t6960 (nat_lit 116050615) (nat_lit 7624822733) (nat_lit 0) A10K2.t6961 from rfl, allE_node, rows6960, irow6954, rows6961]
  all_goals rfl

theorem atot6954 : totK PA10K2 A10K2.u6954 = [0, 111132462386, 827245944727, 2777597459446, 3801499721459, 1661355988605, 228319501284, 6354482628, 0, 0] := by
  rw [show A10K2.u6954 = KTree.node A10K2.t6960 (nat_lit 116050615) (nat_lit 7624822733) (nat_lit 0) A10K2.t6961 from rfl, totK_node, tot6960, tot6961]
  decide +kernel

theorem arows6955 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6955 = true := by
  rw [show A10K2.u6955 = KTree.node A10K2.t6962 (nat_lit 116068253) (nat_lit 1639198639) (nat_lit 0) A10K2.t6963 from rfl, allE_node, rows6962, irow6955, rows6963]
  all_goals rfl

theorem atot6955 : totK PA10K2 A10K2.u6955 = [0, 552915731769, 2595950560120, 4151979901936, 2366464376756, 399825292440, 12462147902, 0, 0, 0] := by
  rw [show A10K2.u6955 = KTree.node A10K2.t6962 (nat_lit 116068253) (nat_lit 1639198639) (nat_lit 0) A10K2.t6963 from rfl, totK_node, tot6962, tot6963]
  decide +kernel

theorem arows6957 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6957 = true := by
  rw [show A10K2.u6957 = KTree.node A10K2.t6964 (nat_lit 116075598) (nat_lit 10931748324) (nat_lit 0) A10K2.t6965 from rfl, allE_node, rows6964, irow6957, rows6965]
  all_goals rfl

theorem atot6957 : totK PA10K2 A10K2.u6957 = [0, 720927149509, 3102280340323, 4142233064760, 1787776124938, 177206947179, 0, 0, 0, 0] := by
  rw [show A10K2.u6957 = KTree.node A10K2.t6964 (nat_lit 116075598) (nat_lit 10931748324) (nat_lit 0) A10K2.t6965 from rfl, totK_node, tot6964, tot6965]
  decide +kernel

theorem arows6958 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6958 = true := by
  rw [show A10K2.u6958 = KTree.node A10K2.t6966 (nat_lit 116088946) (nat_lit 10418642867) (nat_lit 0) A10K2.t6967 from rfl, allE_node, rows6966, irow6958, rows6967]
  all_goals rfl

theorem atot6958 : totK PA10K2 A10K2.u6958 = [0, 612321450092, 2577272148780, 3820231045148, 2249965480570, 505457445730, 31522233512, 0, 0, 0] := by
  rw [show A10K2.u6958 = KTree.node A10K2.t6966 (nat_lit 116088946) (nat_lit 10418642867) (nat_lit 0) A10K2.t6967 from rfl, totK_node, tot6966, tot6967]
  decide +kernel

theorem arows6961 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6961 = true := by
  rw [show A10K2.u6961 = KTree.node A10K2.t6968 (nat_lit 116093484) (nat_lit 7687939409) (nat_lit 0) A10K2.t6969 from rfl, allE_node, rows6968, irow6961, rows6969]
  all_goals rfl

theorem atot6961 : totK PA10K2 A10K2.u6961 = [0, 244406495887, 1967579757778, 4233235958166, 3041914408757, 553422507049, 13816090359, 0, 0, 0] := by
  rw [show A10K2.u6961 = KTree.node A10K2.t6968 (nat_lit 116093484) (nat_lit 7687939409) (nat_lit 0) A10K2.t6969 from rfl, totK_node, tot6968, tot6969]
  decide +kernel

theorem arows6962 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6962 = true := by
  rw [show A10K2.u6962 = KTree.node A10K2.t6970 (nat_lit 116100192) (nat_lit 13483204426) (nat_lit 0) A10K2.t6971 from rfl, allE_node, rows6970, irow6962, rows6971]
  all_goals rfl

theorem atot6962 : totK PA10K2 A10K2.u6962 = [0, 0, 587703598815, 2801759277798, 4226452050994, 2089508299124, 257681384884, 6632180018, 0, 0] := by
  rw [show A10K2.u6962 = KTree.node A10K2.t6970 (nat_lit 116100192) (nat_lit 13483204426) (nat_lit 0) A10K2.t6971 from rfl, totK_node, tot6970, tot6971]
  decide +kernel

theorem arows6964 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6964 = true := by
  rw [show A10K2.u6964 = KTree.node A10K2.t6972 (nat_lit 116107192) (nat_lit 11800879506) (nat_lit 0) A10K2.t6973 from rfl, allE_node, rows6972, irow6964, rows6973]
  all_goals rfl

theorem atot6964 : totK PA10K2 A10K2.u6964 = [0, 0, 796114573859, 3220261904780, 4102609343462, 1660231931521, 136317408901, 0, 0, 0] := by
  rw [show A10K2.u6964 = KTree.node A10K2.t6972 (nat_lit 116107192) (nat_lit 11800879506) (nat_lit 0) A10K2.t6973 from rfl, totK_node, tot6972, tot6973]
  decide +kernel

theorem arows6965 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6965 = true := by
  rw [show A10K2.u6965 = KTree.node A10K2.t6974 (nat_lit 116112844) (nat_lit 2502793731) (nat_lit 0) A10K2.t6975 from rfl, allE_node, rows6974, irow6965, rows6975]
  all_goals rfl

theorem atot6965 : totK PA10K2 A10K2.u6965 = [0, 0, 540648836417, 2636319582668, 4084752593258, 2258989649160, 332689668799, 7047025452, 0, 0] := by
  rw [show A10K2.u6965 = KTree.node A10K2.t6974 (nat_lit 116112844) (nat_lit 2502793731) (nat_lit 0) A10K2.t6975 from rfl, totK_node, tot6974, tot6975]
  decide +kernel

theorem arows6971 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6971 = true := by
  rw [show A10K2.u6971 = KTree.node A10K2.t6976 (nat_lit 116126089) (nat_lit 9203000227) (nat_lit 0) A10K2.t6977 from rfl, allE_node, rows6976, irow6971, rows6977]
  all_goals rfl

theorem atot6971 : totK PA10K2 A10K2.u6971 = [0, 0, 327291078893, 2076404285801, 4190469291186, 2822548979947, 465889950194, 12224107035, 0, 0] := by
  rw [show A10K2.u6971 = KTree.node A10K2.t6976 (nat_lit 116126089) (nat_lit 9203000227) (nat_lit 0) A10K2.t6977 from rfl, totK_node, tot6976, tot6977]
  decide +kernel

theorem arows6972 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6972 = true := by
  rw [show A10K2.u6972 = KTree.node A10K2.t6978 (nat_lit 116205347) (nat_lit 10308727980) (nat_lit 0) A10K2.t6979 from rfl, allE_node, rows6978, irow6972, rows6979]
  all_goals rfl

theorem atot6972 : totK PA10K2 A10K2.u6972 = [0, 0, 847432163172, 3032013248750, 3480311803404, 1796091529871, 534032711397, 48886019071, 0, 0] := by
  rw [show A10K2.u6972 = KTree.node A10K2.t6978 (nat_lit 116205347) (nat_lit 10308727980) (nat_lit 0) A10K2.t6979 from rfl, totK_node, tot6978, tot6979]
  decide +kernel

theorem arows6974 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6974 = true := by
  rw [show A10K2.u6974 = KTree.node A10K2.t6980 (nat_lit 116209907) (nat_lit 10159047240) (nat_lit 0) A10K2.t6981 from rfl, allE_node, rows6980, irow6974, rows6981]
  all_goals rfl

theorem atot6974 : totK PA10K2 A10K2.u6974 = [0, 0, 350469507776, 1923989649423, 3801228196128, 2862129873354, 605845418817, 31543789865, 0, 0] := by
  rw [show A10K2.u6974 = KTree.node A10K2.t6980 (nat_lit 116209907) (nat_lit 10159047240) (nat_lit 0) A10K2.t6981 from rfl, totK_node, tot6980, tot6981]
  decide +kernel

theorem arows6975 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6975 = true := by
  rw [show A10K2.u6975 = KTree.node A10K2.t6982 (nat_lit 116217152) (nat_lit 3938593778) (nat_lit 0) A10K2.t6983 from rfl, allE_node, rows6982, irow6975, rows6983]
  all_goals rfl

theorem atot6975 : totK PA10K2 A10K2.u6975 = [0, 0, 538662218203, 2649192894117, 4143402078915, 1948192166403, 235678235666, 5982052406, 0, 0] := by
  rw [show A10K2.u6975 = KTree.node A10K2.t6982 (nat_lit 116217152) (nat_lit 3938593778) (nat_lit 0) A10K2.t6983 from rfl, totK_node, tot6982, tot6983]
  decide +kernel

theorem arows6978 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6978 = true := by
  rw [show A10K2.u6978 = KTree.node A10K2.t6984 (nat_lit 116223670) (nat_lit 16527114658) (nat_lit 0) A10K2.t6985 from rfl, allE_node, rows6984, irow6978, rows6985]
  all_goals rfl

theorem atot6978 : totK PA10K2 A10K2.u6978 = [0, 0, 496604236678, 2496172820998, 4198762333558, 2500777950518, 382373474180, 6962742351, 0, 0] := by
  rw [show A10K2.u6978 = KTree.node A10K2.t6984 (nat_lit 116223670) (nat_lit 16527114658) (nat_lit 0) A10K2.t6985 from rfl, totK_node, tot6984, tot6985]
  decide +kernel

theorem arows6979 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6979 = true := by
  rw [show A10K2.u6979 = KTree.node A10K2.t6986 (nat_lit 116237808) (nat_lit 11082825828) (nat_lit 0) A10K2.t6987 from rfl, allE_node, rows6986, irow6979, rows6987]
  all_goals rfl

theorem atot6979 : totK PA10K2 A10K2.u6979 = [0, 0, 0, 1144341916460, 3738852745237, 3655125723636, 1036261562813, 66170283597, 0, 0] := by
  rw [show A10K2.u6979 = KTree.node A10K2.t6986 (nat_lit 116237808) (nat_lit 11082825828) (nat_lit 0) A10K2.t6987 from rfl, totK_node, tot6986, tot6987]
  decide +kernel

theorem arows6981 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6981 = true := by
  rw [show A10K2.u6981 = KTree.node A10K2.t6988 (nat_lit 116242666) (nat_lit 11791025255) (nat_lit 0) A10K2.t6989 from rfl, allE_node, rows6988, irow6981, rows6989]
  all_goals rfl

theorem atot6981 : totK PA10K2 A10K2.u6981 = [0, 0, 0, 392124710355, 2513941897354, 4197909098239, 2116741326645, 310223501482, 7380853412, 0] := by
  rw [show A10K2.u6981 = KTree.node A10K2.t6988 (nat_lit 116242666) (nat_lit 11791025255) (nat_lit 0) A10K2.t6989 from rfl, totK_node, tot6988, tot6989]
  decide +kernel

theorem arows6982 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6982 = true := by
  rw [show A10K2.u6982 = KTree.node A10K2.t6990 (nat_lit 116254436) (nat_lit 11505835311) (nat_lit 0) A10K2.t6991 from rfl, allE_node, rows6990, irow6982, rows6991]
  all_goals rfl

theorem atot6982 : totK PA10K2 A10K2.u6982 = [0, 0, 304922396905, 1660974000802, 3695104954717, 3318374941985, 873137772826, 49937155258, 0, 0] := by
  rw [show A10K2.u6982 = KTree.node A10K2.t6990 (nat_lit 116254436) (nat_lit 11505835311) (nat_lit 0) A10K2.t6991 from rfl, totK_node, tot6990, tot6991]
  decide +kernel

theorem arows6986 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6986 = true := by
  rw [show A10K2.u6986 = KTree.node A10K2.t6992 (nat_lit 116272597) (nat_lit 4529392385) (nat_lit 0) A10K2.t6993 from rfl, allE_node, rows6992, irow6986, rows6993]
  all_goals rfl

theorem atot6986 : totK PA10K2 A10K2.u6986 = [0, 0, 909285031429, 3540235643363, 4066598526612, 1219057033758, 71716084455, 0, 0, 0] := by
  rw [show A10K2.u6986 = KTree.node A10K2.t6992 (nat_lit 116272597) (nat_lit 4529392385) (nat_lit 0) A10K2.t6993 from rfl, totK_node, tot6992, tot6993]
  decide +kernel

theorem arows6987 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6987 = true := by
  rw [show A10K2.u6987 = KTree.node A10K2.t6994 (nat_lit 116284072) (nat_lit 8338180901) (nat_lit 0) A10K2.t6995 from rfl, allE_node, rows6994, irow6987, rows6995]
  all_goals rfl

theorem atot6987 : totK PA10K2 A10K2.u6987 = [0, 0, 697976624796, 3052232801527, 4027476721647, 1693583296735, 228758635547, 6354482628, 0, 0] := by
  rw [show A10K2.u6987 = KTree.node A10K2.t6994 (nat_lit 116284072) (nat_lit 8338180901) (nat_lit 0) A10K2.t6995 from rfl, totK_node, tot6994, tot6995]
  decide +kernel

theorem arows6989 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6989 = true := by
  rw [show A10K2.u6989 = KTree.node A10K2.t6996 (nat_lit 116333978) (nat_lit 13786783404) (nat_lit 0) A10K2.t6997 from rfl, allE_node, rows6996, irow6989, rows6997]
  all_goals rfl

theorem atot6989 : totK PA10K2 A10K2.u6989 = [0, 0, 488147704623, 2574202074163, 4217725261859, 2303543177060, 299274630415, 6725424603, 0, 0] := by
  rw [show A10K2.u6989 = KTree.node A10K2.t6996 (nat_lit 116333978) (nat_lit 13786783404) (nat_lit 0) A10K2.t6997 from rfl, totK_node, tot6996, tot6997]
  decide +kernel

theorem arows6990 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6990 = true := by
  rw [show A10K2.u6990 = KTree.node A10K2.t6998 (nat_lit 116340154) (nat_lit 14719078453) (nat_lit 0) A10K2.t6999 from rfl, allE_node, rows6998, irow6990, rows6999]
  all_goals rfl

theorem atot6990 : totK PA10K2 A10K2.u6990 = [0, 0, 367079179829, 2043089912900, 4061520870907, 2863851183477, 492330230423, 12692412833, 0, 0] := by
  rw [show A10K2.u6990 = KTree.node A10K2.t6998 (nat_lit 116340154) (nat_lit 14719078453) (nat_lit 0) A10K2.t6999 from rfl, totK_node, tot6998, tot6999]
  decide +kernel

theorem arows6993 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6993 = true := by
  rw [show A10K2.u6993 = KTree.node A10K2.t7000 (nat_lit 116352950) (nat_lit 16799536538) (nat_lit 0) A10K2.t7001 from rfl, allE_node, rows7000, irow6993, rows7001]
  all_goals rfl

theorem atot6993 : totK PA10K2 A10K2.u6993 = [0, 0, 789276122748, 3332101987057, 4195841286641, 1565714428689, 104885007088, 0, 0, 0] := by
  rw [show A10K2.u6993 = KTree.node A10K2.t7000 (nat_lit 116352950) (nat_lit 16799536538) (nat_lit 0) A10K2.t7001 from rfl, totK_node, tot7000, tot7001]
  decide +kernel

theorem arows6994 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6994 = true := by
  rw [show A10K2.u6994 = KTree.node A10K2.t7002 (nat_lit 116358592) (nat_lit 14598147984) (nat_lit 0) A10K2.t7003 from rfl, allE_node, rows7002, irow6994, rows7003]
  all_goals rfl

theorem atot6994 : totK PA10K2 A10K2.u6994 = [0, 310694887869, 1064754319822, 1716854981555, 2806769625184, 2958868000661, 925839332675, 62382159641, 0, 0] := by
  rw [show A10K2.u6994 = KTree.node A10K2.t7002 (nat_lit 116358592) (nat_lit 14598147984) (nat_lit 0) A10K2.t7003 from rfl, totK_node, tot7002, tot7003]
  decide +kernel

theorem arows6996 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6996 = true := by
  rw [show A10K2.u6996 = KTree.node A10K2.t7004 (nat_lit 116920242) (nat_lit 13201832723) (nat_lit 0) A10K2.t7005 from rfl, allE_node, rows7004, irow6996, rows7005]
  all_goals rfl

theorem atot6996 : totK PA10K2 A10K2.u6996 = [0, 496725316541, 2384832106154, 3874452559414, 2287774120873, 443474562301, 25371180993, 0, 0, 0] := by
  rw [show A10K2.u6996 = KTree.node A10K2.t7004 (nat_lit 116920242) (nat_lit 13201832723) (nat_lit 0) A10K2.t7005 from rfl, totK_node, tot7004, tot7005]
  decide +kernel

theorem arows6997 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6997 = true := by
  rw [show A10K2.u6997 = KTree.node A10K2.t7006 (nat_lit 116934668) (nat_lit 11759478708) (nat_lit 0) A10K2.t7007 from rfl, allE_node, rows7006, irow6997, rows7007]
  all_goals rfl

theorem atot6997 : totK PA10K2 A10K2.u6997 = [0, 619931382278, 2811402510215, 3983341687932, 1849429431004, 234997791588, 5460492893, 0, 0, 0] := by
  rw [show A10K2.u6997 = KTree.node A10K2.t7006 (nat_lit 116934668) (nat_lit 11759478708) (nat_lit 0) A10K2.t7007 from rfl, totK_node, tot7006, tot7007]
  decide +kernel

theorem arows7002 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7002 = true := by
  rw [show A10K2.u7002 = KTree.node A10K2.t7008 (nat_lit 116944099) (nat_lit 9373557666) (nat_lit 0) A10K2.t7009 from rfl, allE_node, rows7008, irow7002, rows7009]
  all_goals rfl

theorem atot7002 : totK PA10K2 A10K2.u7002 = [0, 653619017713, 2877996224481, 4216385773977, 2120050215960, 305129875059, 6853348008, 0, 0, 0] := by
  rw [show A10K2.u7002 = KTree.node A10K2.t7008 (nat_lit 116944099) (nat_lit 9373557666) (nat_lit 0) A10K2.t7009 from rfl, totK_node, tot7008, tot7009]
  decide +kernel

theorem arows7003 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7003 = true := by
  rw [show A10K2.u7003 = KTree.node A10K2.t7010 (nat_lit 116948883) (nat_lit 9580474215) (nat_lit 0) A10K2.t7011 from rfl, allE_node, rows7010, irow7003, rows7011]
  all_goals rfl

theorem atot7003 : totK PA10K2 A10K2.u7003 = [0, 0, 1048779851975, 3717958857892, 3890707865249, 1173161946718, 81793495066, 0, 0, 0] := by
  rw [show A10K2.u7003 = KTree.node A10K2.t7010 (nat_lit 116948883) (nat_lit 9580474215) (nat_lit 0) A10K2.t7011 from rfl, totK_node, tot7010, tot7011]
  decide +kernel

theorem arows7005 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7005 = true := by
  rw [show A10K2.u7005 = KTree.node A10K2.t7012 (nat_lit 116953490) (nat_lit 7853318507) (nat_lit 0) A10K2.t7013 from rfl, allE_node, rows7012, irow7005, rows7013]
  all_goals rfl

theorem atot7005 : totK PA10K2 A10K2.u7005 = [0, 0, 372189300737, 2150389841198, 4041112965577, 2496456187037, 426328651964, 12477124820, 0, 0] := by
  rw [show A10K2.u7005 = KTree.node A10K2.t7012 (nat_lit 116953490) (nat_lit 7853318507) (nat_lit 0) A10K2.t7013 from rfl, totK_node, tot7012, tot7013]
  decide +kernel

theorem arows7006 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7006 = true := by
  rw [show A10K2.u7006 = KTree.node A10K2.t7014 (nat_lit 116969742) (nat_lit 9977307292) (nat_lit 0) A10K2.t7015 from rfl, allE_node, rows7014, irow7006, rows7015]
  all_goals rfl

theorem atot7006 : totK PA10K2 A10K2.u7006 = [0, 0, 759981013499, 3235203766384, 4012770935243, 1390347405115, 99454985834, 0, 0, 0] := by
  rw [show A10K2.u7006 = KTree.node A10K2.t7014 (nat_lit 116969742) (nat_lit 9977307292) (nat_lit 0) A10K2.t7015 from rfl, totK_node, tot7014, tot7015]
  decide +kernel

theorem arows7009 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7009 = true := by
  rw [show A10K2.u7009 = KTree.node A10K2.t7016 (nat_lit 116991137) (nat_lit 5503606195) (nat_lit 0) A10K2.t7017 from rfl, allE_node, rows7016, irow7009, rows7017]
  all_goals rfl

theorem atot7009 : totK PA10K2 A10K2.u7009 = [0, 513260446086, 2311358571042, 3597011187393, 2606628622028, 786378900943, 57551169768, 0, 0, 0] := by
  rw [show A10K2.u7009 = KTree.node A10K2.t7016 (nat_lit 116991137) (nat_lit 5503606195) (nat_lit 0) A10K2.t7017 from rfl, totK_node, tot7016, tot7017]
  decide +kernel

theorem arows7010 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7010 = true := by
  rw [show A10K2.u7010 = KTree.node A10K2.t7018 (nat_lit 116995575) (nat_lit 14690530377) (nat_lit 0) A10K2.t7019 from rfl, allE_node, rows7018, irow7010, rows7019]
  all_goals rfl

theorem atot7010 : totK PA10K2 A10K2.u7010 = [0, 297779599935, 1907554506546, 4021624724261, 2921306320565, 593301505785, 31543789865, 0, 0, 0] := by
  rw [show A10K2.u7010 = KTree.node A10K2.t7018 (nat_lit 116995575) (nat_lit 14690530377) (nat_lit 0) A10K2.t7019 from rfl, totK_node, tot7018, tot7019]
  decide +kernel

theorem arows7012 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7012 = true := by
  rw [show A10K2.u7012 = KTree.node A10K2.t7020 (nat_lit 117003479) (nat_lit 11093727856) (nat_lit 0) A10K2.t7021 from rfl, allE_node, rows7020, irow7012, rows7021]
  all_goals rfl

theorem atot7012 : totK PA10K2 A10K2.u7012 = [0, 842381096568, 3308327783100, 3987551602760, 1500836912189, 135853123273, 0, 0, 0, 0] := by
  rw [show A10K2.u7012 = KTree.node A10K2.t7020 (nat_lit 117003479) (nat_lit 11093727856) (nat_lit 0) A10K2.t7021 from rfl, totK_node, tot7020, tot7021]
  decide +kernel

theorem arows7013 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7013 = true := by
  rw [show A10K2.u7013 = KTree.node A10K2.t7022 (nat_lit 117010331) (nat_lit 8501118200) (nat_lit 0) A10K2.t7023 from rfl, allE_node, rows7022, irow7013, rows7023]
  all_goals rfl

theorem atot7013 : totK PA10K2 A10K2.u7013 = [0, 434930329847, 2319633113767, 4193082555639, 2709335685995, 502347442785, 13814447077, 0, 0, 0] := by
  rw [show A10K2.u7013 = KTree.node A10K2.t7022 (nat_lit 117010331) (nat_lit 8501118200) (nat_lit 0) A10K2.t7023 from rfl, totK_node, tot7022, tot7023]
  decide +kernel

theorem arows7017 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7017 = true := by
  rw [show A10K2.u7017 = KTree.node A10K2.t7024 (nat_lit 117024187) (nat_lit 7059444141) (nat_lit 0) A10K2.t7025 from rfl, allE_node, rows7024, irow7017, rows7025]
  all_goals rfl

theorem atot7017 : totK PA10K2 A10K2.u7017 = [0, 0, 1113883939703, 3706106606868, 3728848933857, 1128190929165, 81234554215, 0, 0, 0] := by
  rw [show A10K2.u7017 = KTree.node A10K2.t7024 (nat_lit 117024187) (nat_lit 7059444141) (nat_lit 0) A10K2.t7025 from rfl, totK_node, tot7024, tot7025]
  decide +kernel

theorem arows7018 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7018 = true := by
  rw [show A10K2.u7018 = KTree.node A10K2.t7026 (nat_lit 117028965) (nat_lit 5388936582) (nat_lit 0) A10K2.t7027 from rfl, allE_node, rows7026, irow7018, rows7027]
  all_goals rfl

theorem atot7018 : totK PA10K2 A10K2.u7018 = [0, 0, 289374726109, 2099843747438, 4139461994066, 2621113551920, 449704127563, 12696458652, 0, 0] := by
  rw [show A10K2.u7018 = KTree.node A10K2.t7026 (nat_lit 117028965) (nat_lit 5388936582) (nat_lit 0) A10K2.t7027 from rfl, totK_node, tot7026, tot7027]
  decide +kernel

theorem arows7020 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7020 = true := by
  rw [show A10K2.u7020 = KTree.node A10K2.t7028 (nat_lit 117039117) (nat_lit 4740060050) (nat_lit 0) A10K2.t7029 from rfl, allE_node, rows7028, irow7020, rows7029]
  all_goals rfl

theorem atot7020 : totK PA10K2 A10K2.u7020 = [0, 0, 747656256060, 3183772191550, 4177910360641, 1535826861004, 87895042935, 0, 0, 0] := by
  rw [show A10K2.u7020 = KTree.node A10K2.t7028 (nat_lit 117039117) (nat_lit 4740060050) (nat_lit 0) A10K2.t7029 from rfl, totK_node, tot7028, tot7029]
  decide +kernel

theorem arows7021 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7021 = true := by
  rw [show A10K2.u7021 = KTree.node A10K2.t7030 (nat_lit 117113348) (nat_lit 11743201875) (nat_lit 0) A10K2.t7031 from rfl, allE_node, rows7030, irow7021, rows7031]
  all_goals rfl

theorem atot7021 : totK PA10K2 A10K2.u7021 = [0, 762038499923, 2846798745334, 3624719829138, 2052237327536, 595572506190, 50555834002, 0, 0, 0] := by
  rw [show A10K2.u7021 = KTree.node A10K2.t7030 (nat_lit 117113348) (nat_lit 11743201875) (nat_lit 0) A10K2.t7031 from rfl, totK_node, tot7030, tot7031]
  decide +kernel

theorem arows7024 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7024 = true := by
  rw [show A10K2.u7024 = KTree.node A10K2.t7032 (nat_lit 117119494) (nat_lit 13049409175) (nat_lit 0) A10K2.t7033 from rfl, allE_node, rows7032, irow7024, rows7033]
  all_goals rfl

theorem atot7024 : totK PA10K2 A10K2.u7024 = [0, 298738363490, 1971713749953, 4001420952297, 2779540498707, 540797913692, 17500500512, 0, 0, 0] := by
  rw [show A10K2.u7024 = KTree.node A10K2.t7032 (nat_lit 117119494) (nat_lit 13049409175) (nat_lit 0) A10K2.t7033 from rfl, totK_node, tot7032, tot7033]
  decide +kernel

theorem arows7025 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7025 = true := by
  rw [show A10K2.u7025 = KTree.node A10K2.t7034 (nat_lit 117125114) (nat_lit 12709691639) (nat_lit 0) A10K2.t7035 from rfl, allE_node, rows7034, irow7025, rows7035]
  all_goals rfl

theorem atot7025 : totK PA10K2 A10K2.u7025 = [0, 467024804561, 2380211562373, 4017785908318, 2504494608666, 482803237656, 17754888877, 0, 0, 0] := by
  rw [show A10K2.u7025 = KTree.node A10K2.t7034 (nat_lit 117125114) (nat_lit 12709691639) (nat_lit 0) A10K2.t7035 from rfl, totK_node, tot7034, tot7035]
  decide +kernel

theorem arows7027 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7027 = true := by
  rw [show A10K2.u7027 = KTree.node A10K2.t7036 (nat_lit 117138825) (nat_lit 8720164383) (nat_lit 0) A10K2.t7037 from rfl, allE_node, rows7036, irow7027, rows7037]
  all_goals rfl

theorem atot7027 : totK PA10K2 A10K2.u7027 = [0, 896434737838, 3478203028382, 4069014535666, 1456738561406, 115563710163, 0, 0, 0, 0] := by
  rw [show A10K2.u7027 = KTree.node A10K2.t7036 (nat_lit 117138825) (nat_lit 8720164383) (nat_lit 0) A10K2.t7037 from rfl, totK_node, tot7036, tot7037]
  decide +kernel

theorem arows7028 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7028 = true := by
  rw [show A10K2.u7028 = KTree.node A10K2.t7038 (nat_lit 117143255) (nat_lit 10115826494) (nat_lit 0) A10K2.t7039 from rfl, allE_node, rows7038, irow7028, rows7039]
  all_goals rfl

theorem atot7028 : totK PA10K2 A10K2.u7028 = [0, 0, 1079669730861, 3857563731842, 3902942268871, 1064425761940, 62996513375, 0, 0, 0] := by
  rw [show A10K2.u7028 = KTree.node A10K2.t7038 (nat_lit 117143255) (nat_lit 10115826494) (nat_lit 0) A10K2.t7039 from rfl, totK_node, tot7038, tot7039]
  decide +kernel

theorem arows7035 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7035 = true := by
  rw [show A10K2.u7035 = KTree.node A10K2.t7040 (nat_lit 117149132) (nat_lit 6322575519) (nat_lit 0) A10K2.t7041 from rfl, allE_node, rows7040, irow7035, rows7041]
  all_goals rfl

theorem atot7035 : totK PA10K2 A10K2.u7035 = [0, 0, 574391294643, 2732696576688, 4109498756833, 2018153896390, 263107810398, 6904928264, 0, 0] := by
  rw [show A10K2.u7035 = KTree.node A10K2.t7040 (nat_lit 117149132) (nat_lit 6322575519) (nat_lit 0) A10K2.t7041 from rfl, totK_node, tot7040, tot7041]
  decide +kernel

theorem arows7036 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7036 = true := by
  rw [show A10K2.u7036 = KTree.node A10K2.t7042 (nat_lit 117155762) (nat_lit 14791393585) (nat_lit 0) A10K2.t7043 from rfl, allE_node, rows7042, irow7036, rows7043]
  all_goals rfl

theorem atot7036 : totK PA10K2 A10K2.u7036 = [0, 0, 764753336025, 3216991581948, 4146643828288, 1621814623637, 124742145879, 0, 0, 0] := by
  rw [show A10K2.u7036 = KTree.node A10K2.t7042 (nat_lit 117155762) (nat_lit 14791393585) (nat_lit 0) A10K2.t7043 from rfl, totK_node, tot7042, tot7043]
  decide +kernel

theorem arows7038 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7038 = true := by
  rw [show A10K2.u7038 = KTree.node A10K2.t7044 (nat_lit 117170220) (nat_lit 9319527214) (nat_lit 0) A10K2.t7045 from rfl, allE_node, rows7044, irow7038, rows7045]
  all_goals rfl

theorem atot7038 : totK PA10K2 A10K2.u7038 = [0, 0, 563781224979, 2650652560328, 4091580250848, 2166824369172, 278359286524, 7047025452, 0, 0] := by
  rw [show A10K2.u7038 = KTree.node A10K2.t7044 (nat_lit 117170220) (nat_lit 9319527214) (nat_lit 0) A10K2.t7045 from rfl, totK_node, tot7044, tot7045]
  decide +kernel

theorem arows7039 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7039 = true := by
  rw [show A10K2.u7039 = KTree.node A10K2.t7046 (nat_lit 117174706) (nat_lit 12976949940) (nat_lit 0) A10K2.t7047 from rfl, allE_node, rows7046, irow7039, rows7047]
  all_goals rfl

theorem atot7039 : totK PA10K2 A10K2.u7039 = [0, 0, 331364255318, 2126818031984, 4191637889491, 2833853487228, 467611528954, 12224107035, 0, 0] := by
  rw [show A10K2.u7039 = KTree.node A10K2.t7046 (nat_lit 117174706) (nat_lit 12976949940) (nat_lit 0) A10K2.t7047 from rfl, totK_node, tot7046, tot7047]
  decide +kernel

theorem arows7042 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7042 = true := by
  rw [show A10K2.u7042 = KTree.node A10K2.t7048 (nat_lit 117179205) (nat_lit 6352588418) (nat_lit 0) A10K2.t7049 from rfl, allE_node, rows7048, irow7042, rows7049]
  all_goals rfl

theorem atot7042 : totK PA10K2 A10K2.u7042 = [0, 0, 805380807407, 2948504758489, 3518953735381, 1893689279002, 545946517441, 48886019071, 0, 0] := by
  rw [show A10K2.u7042 = KTree.node A10K2.t7048 (nat_lit 117179205) (nat_lit 6352588418) (nat_lit 0) A10K2.t7049 from rfl, totK_node, tot7048, tot7049]
  decide +kernel

theorem arows7043 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7043 = true := by
  rw [show A10K2.u7043 = KTree.node A10K2.t7050 (nat_lit 117185281) (nat_lit 10111568244) (nat_lit 0) A10K2.t7051 from rfl, allE_node, rows7050, irow7043, rows7051]
  all_goals rfl

theorem atot7043 : totK PA10K2 A10K2.u7043 = [0, 0, 368328999156, 2029744882700, 3934191074880, 2703138766431, 483016384030, 12477124820, 0, 0] := by
  rw [show A10K2.u7043 = KTree.node A10K2.t7050 (nat_lit 117185281) (nat_lit 10111568244) (nat_lit 0) A10K2.t7051 from rfl, totK_node, tot7050, tot7051]
  decide +kernel

theorem arows7045 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7045 = true := by
  rw [show A10K2.u7045 = KTree.node A10K2.t7052 (nat_lit 117203527) (nat_lit 9934066887) (nat_lit 0) A10K2.t7053 from rfl, allE_node, rows7052, irow7045, rows7053]
  all_goals rfl

theorem atot7045 : totK PA10K2 A10K2.u7045 = [0, 0, 900318328081, 3506542392833, 4085288234462, 1321469276983, 74235121777, 0, 0, 0] := by
  rw [show A10K2.u7045 = KTree.node A10K2.t7052 (nat_lit 117203527) (nat_lit 9934066887) (nat_lit 0) A10K2.t7053 from rfl, totK_node, tot7052, tot7053]
  decide +kernel

theorem arows7046 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7046 = true := by
  rw [show A10K2.u7046 = KTree.node A10K2.t7054 (nat_lit 117208534) (nat_lit 15723628633) (nat_lit 0) A10K2.t7055 from rfl, allE_node, rows7054, irow7046, rows7055]
  all_goals rfl

theorem atot7046 : totK PA10K2 A10K2.u7046 = [0, 0, 0, 1154274638409, 3957017246882, 3909037750759, 1025559768713, 62351816811, 0, 0] := by
  rw [show A10K2.u7046 = KTree.node A10K2.t7054 (nat_lit 117208534) (nat_lit 15723628633) (nat_lit 0) A10K2.t7055 from rfl, totK_node, tot7054, tot7055]
  decide +kernel

theorem arows7050 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7050 = true := by
  rw [show A10K2.u7050 = KTree.node A10K2.t7056 (nat_lit 117214448) (nat_lit 11350074709) (nat_lit 0) A10K2.t7057 from rfl, allE_node, rows7056, irow7050, rows7057]
  all_goals rfl

theorem atot7050 : totK PA10K2 A10K2.u7050 = [0, 0, 0, 672378343948, 2984907733406, 4036044998671, 1689270705661, 212025318154, 6725424603, 0] := by
  rw [show A10K2.u7050 = KTree.node A10K2.t7056 (nat_lit 117214448) (nat_lit 11350074709) (nat_lit 0) A10K2.t7057 from rfl, totK_node, tot7056, tot7057]
  decide +kernel

theorem arows7051 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7051 = true := by
  rw [show A10K2.u7051 = KTree.node A10K2.t7058 (nat_lit 117235745) (nat_lit 10167212538) (nat_lit 0) A10K2.t7059 from rfl, allE_node, rows7058, irow7051, rows7059]
  all_goals rfl

theorem atot7051 : totK PA10K2 A10K2.u7051 = [0, 0, 0, 1048028390775, 3836624220596, 3831265463545, 988695291913, 49518614487, 0, 0] := by
  rw [show A10K2.u7051 = KTree.node A10K2.t7058 (nat_lit 117235745) (nat_lit 10167212538) (nat_lit 0) A10K2.t7059 from rfl, totK_node, tot7058, tot7059]
  decide +kernel

theorem arows7053 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7053 = true := by
  rw [show A10K2.u7053 = KTree.node A10K2.t7060 (nat_lit 117253815) (nat_lit 14381767791) (nat_lit 0) A10K2.t7061 from rfl, allE_node, rows7060, irow7053, rows7061]
  all_goals rfl

theorem atot7053 : totK PA10K2 A10K2.u7053 = [0, 0, 808999170994, 2936927765675, 3533806937308, 1966640836010, 572776210049, 50425690648, 0, 0] := by
  rw [show A10K2.u7053 = KTree.node A10K2.t7060 (nat_lit 117253815) (nat_lit 14381767791) (nat_lit 0) A10K2.t7061 from rfl, totK_node, tot7060, tot7061]
  decide +kernel

theorem arows7054 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7054 = true := by
  rw [show A10K2.u7054 = KTree.node A10K2.t7062 (nat_lit 117258525) (nat_lit 6417950217) (nat_lit 0) A10K2.t7063 from rfl, allE_node, rows7062, irow7054, rows7063]
  all_goals rfl

theorem atot7054 : totK PA10K2 A10K2.u7054 = [0, 0, 272840970372, 1942215707869, 4085965943932, 2873370732706, 501779801524, 12696458652, 0, 0] := by
  rw [show A10K2.u7054 = KTree.node A10K2.t7062 (nat_lit 117258525) (nat_lit 6417950217) (nat_lit 0) A10K2.t7063 from rfl, totK_node, tot7062, tot7063]
  decide +kernel

theorem arows7057 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7057 = true := by
  rw [show A10K2.u7057 = KTree.node A10K2.t7064 (nat_lit 117269063) (nat_lit 9934066887) (nat_lit 0) A10K2.t7065 from rfl, allE_node, rows7064, irow7057, rows7065]
  all_goals rfl

theorem atot7057 : totK PA10K2 A10K2.u7057 = [0, 0, 999573930879, 3652279517001, 3924442243620, 1266051967380, 74981226318, 0, 0, 0] := by
  rw [show A10K2.u7057 = KTree.node A10K2.t7064 (nat_lit 117269063) (nat_lit 9934066887) (nat_lit 0) A10K2.t7065 from rfl, totK_node, tot7064, tot7065]
  decide +kernel

theorem arows7058 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7058 = true := by
  rw [show A10K2.u7058 = KTree.node A10K2.t7066 (nat_lit 117274014) (nat_lit 15508892991) (nat_lit 0) A10K2.t7067 from rfl, allE_node, rows7066, irow7058, rows7067]
  all_goals rfl

theorem atot7058 : totK PA10K2 A10K2.u7058 = [0, 0, 0, 1251508191029, 4047727404462, 3800082347854, 1001005983506, 62364134685, 0, 0] := by
  rw [show A10K2.u7058 = KTree.node A10K2.t7066 (nat_lit 117274014) (nat_lit 15508892991) (nat_lit 0) A10K2.t7067 from rfl, totK_node, tot7066, tot7067]
  decide +kernel

theorem arows7060 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7060 = true := by
  rw [show A10K2.u7060 = KTree.node A10K2.t7068 (nat_lit 117288098) (nat_lit 14475107635) (nat_lit 0) A10K2.t7069 from rfl, allE_node, rows7068, irow7060, rows7069]
  all_goals rfl

theorem atot7060 : totK PA10K2 A10K2.u7060 = [0, 0, 0, 725759517459, 3076596755144, 4032398717375, 1653516389543, 194765378773, 6860445330, 0] := by
  rw [show A10K2.u7060 = KTree.node A10K2.t7068 (nat_lit 117288098) (nat_lit 14475107635) (nat_lit 0) A10K2.t7069 from rfl, totK_node, tot7068, tot7069]
  decide +kernel

theorem arows7061 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7061 = true := by
  rw [show A10K2.u7061 = KTree.node A10K2.t7070 (nat_lit 117301640) (nat_lit 13970465211) (nat_lit 0) A10K2.t7071 from rfl, allE_node, rows7070, irow7061, rows7071]
  all_goals rfl

theorem atot7061 : totK PA10K2 A10K2.u7061 = [0, 0, 0, 1141654108067, 3813046879098, 3767190870684, 1106032645015, 78120507454, 0, 0] := by
  rw [show A10K2.u7061 = KTree.node A10K2.t7070 (nat_lit 117301640) (nat_lit 13970465211) (nat_lit 0) A10K2.t7071 from rfl, totK_node, tot7070, tot7071]
  decide +kernel

theorem arows7066 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7066 = true := by
  rw [show A10K2.u7066 = KTree.node A10K2.t7072 (nat_lit 117375757) (nat_lit 5232645901) (nat_lit 0) A10K2.t7073 from rfl, allE_node, rows7072, irow7066, rows7073]
  all_goals rfl

theorem atot7066 : totK PA10K2 A10K2.u7066 = [0, 0, 756596605799, 2863612843267, 3613687891456, 2024144160705, 577826524295, 50432252117, 0, 0] := by
  rw [show A10K2.u7066 = KTree.node A10K2.t7072 (nat_lit 117375757) (nat_lit 5232645901) (nat_lit 0) A10K2.t7073 from rfl, totK_node, tot7072, tot7073]
  decide +kernel

theorem arows7067 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7067 = true := by
  rw [show A10K2.u7067 = KTree.node A10K2.t7074 (nat_lit 117382328) (nat_lit 11465925770) (nat_lit 0) A10K2.t7075 from rfl, allE_node, rows7074, irow7067, rows7075]
  all_goals rfl

theorem atot7067 : totK PA10K2 A10K2.u7067 = [0, 0, 451764689091, 2290294460275, 3919450739498, 2456985326168, 390138630401, 11694325420, 0, 0] := by
  rw [show A10K2.u7067 = KTree.node A10K2.t7074 (nat_lit 117382328) (nat_lit 11465925770) (nat_lit 0) A10K2.t7075 from rfl, totK_node, tot7074, tot7075]
  decide +kernel

theorem arows7069 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7069 = true := by
  rw [show A10K2.u7069 = KTree.node A10K2.t7076 (nat_lit 117388756) (nat_lit 8948970204) (nat_lit 0) A10K2.t7077 from rfl, allE_node, rows7076, irow7069, rows7077]
  all_goals rfl

theorem atot7069 : totK PA10K2 A10K2.u7069 = [0, 0, 453805659701, 2282178897800, 4074397100726, 2644487308730, 402582047021, 11918539728, 0, 0] := by
  rw [show A10K2.u7069 = KTree.node A10K2.t7076 (nat_lit 117388756) (nat_lit 8948970204) (nat_lit 0) A10K2.t7077 from rfl, totK_node, tot7076, tot7077]
  decide +kernel

theorem arows7070 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7070 = true := by
  rw [show A10K2.u7070 = KTree.node A10K2.t7078 (nat_lit 117402637) (nat_lit 4875711482) (nat_lit 0) A10K2.t7079 from rfl, allE_node, rows7078, irow7070, rows7079]
  all_goals rfl

theorem atot7070 : totK PA10K2 A10K2.u7070 = [0, 0, 745622975128, 3229290055061, 4216543693789, 1652669153274, 120069349343, 0, 0, 0] := by
  rw [show A10K2.u7070 = KTree.node A10K2.t7078 (nat_lit 117402637) (nat_lit 4875711482) (nat_lit 0) A10K2.t7079 from rfl, totK_node, tot7078, tot7079]
  decide +kernel

theorem arows7073 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7073 = true := by
  rw [show A10K2.u7073 = KTree.node A10K2.t7080 (nat_lit 117407159) (nat_lit 15262755396) (nat_lit 0) A10K2.t7081 from rfl, allE_node, rows7080, irow7073, rows7081]
  all_goals rfl

theorem atot7073 : totK PA10K2 A10K2.u7073 = [0, 0, 0, 915852352352, 3534168813082, 4084494553399, 1215996078426, 74533623153, 0, 0] := by
  rw [show A10K2.u7073 = KTree.node A10K2.t7080 (nat_lit 117407159) (nat_lit 15262755396) (nat_lit 0) A10K2.t7081 from rfl, totK_node, tot7080, tot7081]
  decide +kernel

theorem arows7074 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7074 = true := by
  rw [show A10K2.u7074 = KTree.node A10K2.t7082 (nat_lit 117411954) (nat_lit 9549382766) (nat_lit 0) A10K2.t7083 from rfl, allE_node, rows7082, irow7074, rows7083]
  all_goals rfl

theorem atot7074 : totK PA10K2 A10K2.u7074 = [0, 0, 0, 626483463721, 2734834005981, 4043749551954, 1994581408196, 270825303789, 6318667960, 0] := by
  rw [show A10K2.u7074 = KTree.node A10K2.t7082 (nat_lit 117411954) (nat_lit 9549382766) (nat_lit 0) A10K2.t7083 from rfl, totK_node, tot7082, tot7083]
  decide +kernel

theorem arows7076 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7076 = true := by
  rw [show A10K2.u7076 = KTree.node A10K2.t7084 (nat_lit 117419584) (nat_lit 14606116163) (nat_lit 0) A10K2.t7085 from rfl, allE_node, rows7084, irow7076, rows7085]
  all_goals rfl

theorem atot7076 : totK PA10K2 A10K2.u7076 = [0, 0, 0, 571604056622, 2850003466166, 4221807470175, 1921487166352, 237672147252, 6439430839, 0] := by
  rw [show A10K2.u7076 = KTree.node A10K2.t7084 (nat_lit 117419584) (nat_lit 14606116163) (nat_lit 0) A10K2.t7085 from rfl, totK_node, tot7084, tot7085]
  decide +kernel

theorem arows7077 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7077 = true := by
  rw [show A10K2.u7077 = KTree.node A10K2.t7086 (nat_lit 117433841) (nat_lit 7736329609) (nat_lit 0) A10K2.t7087 from rfl, allE_node, rows7086, irow7077, rows7087]
  all_goals rfl

theorem atot7077 : totK PA10K2 A10K2.u7077 = [0, 0, 0, 878740748981, 3370531398885, 3990511224545, 1479421898884, 123001052038, 0, 0] := by
  rw [show A10K2.u7077 = KTree.node A10K2.t7086 (nat_lit 117433841) (nat_lit 7736329609) (nat_lit 0) A10K2.t7087 from rfl, totK_node, tot7086, tot7087]
  decide +kernel

theorem arows7081 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7081 = true := by
  rw [show A10K2.u7081 = KTree.node A10K2.t7088 (nat_lit 117439546) (nat_lit 11711544638) (nat_lit 0) A10K2.t7089 from rfl, allE_node, rows7088, irow7081, rows7089]
  all_goals rfl

theorem atot7081 : totK PA10K2 A10K2.u7081 = [0, 321107158991, 869680282452, 549821226374, 874663244101, 3001800521538, 3150155262129, 910141810368, 61018386929, 0] := by
  rw [show A10K2.u7081 = KTree.node A10K2.t7088 (nat_lit 117439546) (nat_lit 11711544638) (nat_lit 0) A10K2.t7089 from rfl, totK_node, tot7088, tot7089]
  decide +kernel

theorem arows7082 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7082 = true := by
  rw [show A10K2.u7082 = KTree.node A10K2.t7090 (nat_lit 117443989) (nat_lit 1084703237) (nat_lit 0) A10K2.t7091 from rfl, allE_node, rows7090, irow7082, rows7091]
  all_goals rfl

theorem atot7082 : totK PA10K2 A10K2.u7082 = [0, 548792962994, 2615774932641, 3999777564479, 2073329629470, 390646950710, 25371180993, 0, 0, 0] := by
  rw [show A10K2.u7082 = KTree.node A10K2.t7090 (nat_lit 117443989) (nat_lit 1084703237) (nat_lit 0) A10K2.t7091 from rfl, totK_node, tot7090, tot7091]
  decide +kernel

theorem arows7084 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7084 = true := by
  rw [show A10K2.u7084 = KTree.node A10K2.t7092 (nat_lit 117457178) (nat_lit 9680543456) (nat_lit 0) A10K2.t7093 from rfl, allE_node, rows7092, irow7084, rows7093]
  all_goals rfl

theorem atot7084 : totK PA10K2 A10K2.u7084 = [0, 682068350716, 2625371509915, 3724804935258, 2001642365213, 281543333879, 5460492893, 0, 0, 0] := by
  rw [show A10K2.u7084 = KTree.node A10K2.t7092 (nat_lit 117457178) (nat_lit 9680543456) (nat_lit 0) A10K2.t7093 from rfl, totK_node, tot7092, tot7093]
  decide +kernel

theorem arows7085 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7085 = true := by
  rw [show A10K2.u7085 = KTree.node A10K2.t7094 (nat_lit 117463332) (nat_lit 14257594719) (nat_lit 0) A10K2.t7095 from rfl, allE_node, rows7094, irow7085, rows7095]
  all_goals rfl

theorem atot7085 : totK PA10K2 A10K2.u7085 = [0, 477186847112, 2570932811814, 4082423134835, 2035633869707, 263002555473, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u7085 = KTree.node A10K2.t7094 (nat_lit 117463332) (nat_lit 14257594719) (nat_lit 0) A10K2.t7095 from rfl, totK_node, tot7094, tot7095]
  decide +kernel

theorem arows7088 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7088 = true := by
  rw [show A10K2.u7088 = KTree.node A10K2.t7096 (nat_lit 117469446) (nat_lit 11841837919) (nat_lit 0) A10K2.t7097 from rfl, allE_node, rows7096, irow7088, rows7097]
  all_goals rfl

theorem atot7088 : totK PA10K2 A10K2.u7088 = [0, 309893393367, 2176927433146, 4308254683919, 2840819008280, 507914740121, 13731804191, 0, 0, 0] := by
  rw [show A10K2.u7088 = KTree.node A10K2.t7096 (nat_lit 117469446) (nat_lit 11841837919) (nat_lit 0) A10K2.t7097 from rfl, totK_node, tot7096, tot7097]
  decide +kernel

theorem arows7089 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7089 = true := by
  rw [show A10K2.u7089 = KTree.node A10K2.t7098 (nat_lit 117474194) (nat_lit 9643321987) (nat_lit 0) A10K2.t7099 from rfl, allE_node, rows7098, irow7089, rows7099]
  all_goals rfl

theorem atot7089 : totK PA10K2 A10K2.u7089 = [0, 0, 866546935381, 3497786767152, 4039500074442, 1265881944881, 86952810295, 0, 0, 0] := by
  rw [show A10K2.u7089 = KTree.node A10K2.t7098 (nat_lit 117474194) (nat_lit 9643321987) (nat_lit 0) A10K2.t7099 from rfl, totK_node, tot7098, tot7099]
  decide +kernel

theorem arows7091 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7091 = true := by
  rw [show A10K2.u7091 = KTree.node A10K2.t7100 (nat_lit 117479767) (nat_lit 601845398) (nat_lit 0) A10K2.t7101 from rfl, allE_node, rows7100, irow7091, rows7101]
  all_goals rfl

theorem atot7091 : totK PA10K2 A10K2.u7091 = [0, 0, 292923624175, 1934515999435, 3942892395642, 2667493151646, 563298174194, 30650496230, 0, 0] := by
  rw [show A10K2.u7091 = KTree.node A10K2.t7100 (nat_lit 117479767) (nat_lit 601845398) (nat_lit 0) A10K2.t7101 from rfl, totK_node, tot7100, tot7101]
  decide +kernel

theorem arows7092 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7092 = true := by
  rw [show A10K2.u7092 = KTree.node A10K2.t7102 (nat_lit 117494016) (nat_lit 14814158032) (nat_lit 0) A10K2.t7103 from rfl, allE_node, rows7102, irow7092, rows7103]
  all_goals rfl

theorem atot7092 : totK PA10K2 A10K2.u7092 = [0, 0, 572461686819, 2642911530976, 3800953494755, 1651443938551, 210401628521, 5546304973, 0, 0] := by
  rw [show A10K2.u7092 = KTree.node A10K2.t7102 (nat_lit 117494016) (nat_lit 14814158032) (nat_lit 0) A10K2.t7103 from rfl, totK_node, tot7102, tot7103]
  decide +kernel

theorem arows7098 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7098 = true := by
  rw [show A10K2.u7098 = KTree.node A10K2.t7104 (nat_lit 117501425) (nat_lit 8557582434) (nat_lit 0) A10K2.t7105 from rfl, allE_node, rows7104, irow7098, rows7105]
  all_goals rfl

theorem atot7098 : totK PA10K2 A10K2.u7098 = [0, 371399122619, 1809643179718, 3628666735610, 3250666205180, 1020734353908, 77311500230, 0, 0, 0] := by
  rw [show A10K2.u7098 = KTree.node A10K2.t7104 (nat_lit 117501425) (nat_lit 8557582434) (nat_lit 0) A10K2.t7105 from rfl, totK_node, tot7104, tot7105]
  decide +kernel

theorem arows7099 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7099 = true := by
  rw [show A10K2.u7099 = KTree.node A10K2.t7106 (nat_lit 117575717) (nat_lit 6984222168) (nat_lit 0) A10K2.t7107 from rfl, allE_node, rows7106, irow7099, rows7107]
  all_goals rfl

theorem atot7099 : totK PA10K2 A10K2.u7099 = [0, 410425211567, 2267457657019, 3955637104545, 2462778511118, 463963825568, 25371180993, 0, 0, 0] := by
  rw [show A10K2.u7099 = KTree.node A10K2.t7106 (nat_lit 117575717) (nat_lit 6984222168) (nat_lit 0) A10K2.t7107 from rfl, totK_node, tot7106, tot7107]
  decide +kernel

theorem arows7101 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7101 = true := by
  rw [show A10K2.u7101 = KTree.node A10K2.t7108 (nat_lit 117586204) (nat_lit 12193009390) (nat_lit 0) A10K2.t7109 from rfl, allE_node, rows7108, irow7101, rows7109]
  all_goals rfl

theorem atot7101 : totK PA10K2 A10K2.u7101 = [0, 703896199845, 2804657135950, 3739913234396, 1975941960313, 333424300349, 11494708454, 0, 0, 0] := by
  rw [show A10K2.u7101 = KTree.node A10K2.t7108 (nat_lit 117586204) (nat_lit 12193009390) (nat_lit 0) A10K2.t7109 from rfl, totK_node, tot7108, tot7109]
  decide +kernel

theorem arows7102 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7102 = true := by
  rw [show A10K2.u7102 = KTree.node A10K2.t7110 (nat_lit 117592418) (nat_lit 10815490172) (nat_lit 0) A10K2.t7111 from rfl, allE_node, rows7110, irow7102, rows7111]
  all_goals rfl

theorem atot7102 : totK PA10K2 A10K2.u7102 = [0, 290480228743, 2181125569469, 4142946626830, 2288067763139, 322699003935, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u7102 = KTree.node A10K2.t7110 (nat_lit 117592418) (nat_lit 10815490172) (nat_lit 0) A10K2.t7111 from rfl, totK_node, tot7110, tot7111]
  decide +kernel

theorem arows7105 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7105 = true := by
  rw [show A10K2.u7105 = KTree.node A10K2.t7112 (nat_lit 117607464) (nat_lit 12711763538) (nat_lit 0) A10K2.t7113 from rfl, allE_node, rows7112, irow7105, rows7113]
  all_goals rfl

theorem atot7105 : totK PA10K2 A10K2.u7105 = [0, 0, 1014905371504, 3718851289548, 3875626441417, 980316056407, 45137794371, 0, 0, 0] := by
  rw [show A10K2.u7105 = KTree.node A10K2.t7112 (nat_lit 117607464) (nat_lit 12711763538) (nat_lit 0) A10K2.t7113 from rfl, totK_node, tot7112, tot7113]
  decide +kernel

theorem arows7106 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7106 = true := by
  rw [show A10K2.u7106 = KTree.node A10K2.t7114 (nat_lit 117623054) (nat_lit 7917849212) (nat_lit 0) A10K2.t7115 from rfl, allE_node, rows7114, irow7106, rows7115]
  all_goals rfl

theorem atot7106 : totK PA10K2 A10K2.u7106 = [0, 0, 592445023990, 3072670939765, 4180056974808, 1359067715531, 94548062042, 0, 0, 0] := by
  rw [show A10K2.u7106 = KTree.node A10K2.t7114 (nat_lit 117623054) (nat_lit 7917849212) (nat_lit 0) A10K2.t7115 from rfl, totK_node, tot7114, tot7115]
  decide +kernel

theorem arows7108 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7108 = true := by
  rw [show A10K2.u7108 = KTree.node A10K2.t7116 (nat_lit 117639456) (nat_lit 13063659673) (nat_lit 0) A10K2.t7117 from rfl, allE_node, rows7116, irow7108, rows7117]
  all_goals rfl

theorem atot7108 : totK PA10K2 A10K2.u7108 = [0, 810484086859, 3078696117849, 3531346954025, 1593391999411, 612691264904, 131550150800, 6354482628, 0, 0] := by
  rw [show A10K2.u7108 = KTree.node A10K2.t7116 (nat_lit 117639456) (nat_lit 13063659673) (nat_lit 0) A10K2.t7117 from rfl, totK_node, tot7116, tot7117]
  decide +kernel

theorem arows7109 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7109 = true := by
  rw [show A10K2.u7109 = KTree.node A10K2.t7118 (nat_lit 117644471) (nat_lit 14879290484) (nat_lit 0) A10K2.t7119 from rfl, allE_node, rows7118, irow7109, rows7119]
  all_goals rfl

theorem atot7109 : totK PA10K2 A10K2.u7109 = [0, 512353472697, 2387804643206, 3998688352677, 2589060458620, 542195808258, 30810868011, 0, 0, 0] := by
  rw [show A10K2.u7109 = KTree.node A10K2.t7118 (nat_lit 117644471) (nat_lit 14879290484) (nat_lit 0) A10K2.t7119 from rfl, totK_node, tot7118, tot7119]
  decide +kernel

theorem arows7113 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7113 = true := by
  rw [show A10K2.u7113 = KTree.node A10K2.t7120 (nat_lit 117661760) (nat_lit 15483700244) (nat_lit 0) A10K2.t7121 from rfl, allE_node, rows7120, irow7113, rows7121]
  all_goals rfl

theorem atot7113 : totK PA10K2 A10K2.u7113 = [0, 626723047185, 2770235278526, 4226100955811, 2285315725024, 360941070702, 13497265543, 0, 0, 0] := by
  rw [show A10K2.u7113 = KTree.node A10K2.t7120 (nat_lit 117661760) (nat_lit 15483700244) (nat_lit 0) A10K2.t7121 from rfl, totK_node, tot7120, tot7121]
  decide +kernel

theorem arows7114 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7114 = true := by
  rw [show A10K2.u7114 = KTree.node A10K2.t7122 (nat_lit 117666318) (nat_lit 13708908750) (nat_lit 0) A10K2.t7123 from rfl, allE_node, rows7122, irow7114, rows7123]
  all_goals rfl

theorem atot7114 : totK PA10K2 A10K2.u7114 = [0, 218977231605, 1883953324025, 4231484525995, 3143195580414, 584257115399, 13816090359, 0, 0, 0] := by
  rw [show A10K2.u7114 = KTree.node A10K2.t7122 (nat_lit 117666318) (nat_lit 13708908750) (nat_lit 0) A10K2.t7123 from rfl, totK_node, tot7122, tot7123]
  decide +kernel

theorem arows7116 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7116 = true := by
  rw [show A10K2.u7116 = KTree.node A10K2.t7124 (nat_lit 117672012) (nat_lit 10903673543) (nat_lit 0) A10K2.t7125 from rfl, allE_node, rows7124, irow7116, rows7125]
  all_goals rfl

theorem atot7116 : totK PA10K2 A10K2.u7116 = [0, 0, 810337294414, 3287950321231, 4075054105931, 1547384247543, 130556372945, 0, 0, 0] := by
  rw [show A10K2.u7116 = KTree.node A10K2.t7124 (nat_lit 117672012) (nat_lit 10903673543) (nat_lit 0) A10K2.t7125 from rfl, totK_node, tot7124, tot7125]
  decide +kernel

theorem arows7117 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7117 = true := by
  rw [show A10K2.u7117 = KTree.node A10K2.t7126 (nat_lit 117677527) (nat_lit 14298283331) (nat_lit 0) A10K2.t7127 from rfl, allE_node, rows7126, irow7117, rows7127]
  all_goals rfl

theorem atot7117 : totK PA10K2 A10K2.u7117 = [0, 0, 511318055732, 2616705701232, 4335089590027, 2309392195789, 312000074243, 6904928264, 0, 0] := by
  rw [show A10K2.u7117 = KTree.node A10K2.t7126 (nat_lit 117677527) (nat_lit 14298283331) (nat_lit 0) A10K2.t7127 from rfl, totK_node, tot7126, tot7127]
  decide +kernel

theorem arows7120 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7120 = true := by
  rw [show A10K2.u7120 = KTree.node A10K2.t7128 (nat_lit 117694899) (nat_lit 8236344417) (nat_lit 0) A10K2.t7129 from rfl, allE_node, rows7128, irow7120, rows7129]
  all_goals rfl

theorem atot7120 : totK PA10K2 A10K2.u7120 = [0, 0, 722766816007, 2962693665149, 4045665587413, 2101830561638, 296055719015, 7047025452, 0, 0] := by
  rw [show A10K2.u7120 = KTree.node A10K2.t7128 (nat_lit 117694899) (nat_lit 8236344417) (nat_lit 0) A10K2.t7129 from rfl, totK_node, tot7128, tot7129]
  decide +kernel

theorem arows7121 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7121 = true := by
  rw [show A10K2.u7121 = KTree.node A10K2.t7130 (nat_lit 117699740) (nat_lit 8376348058) (nat_lit 0) A10K2.t7131 from rfl, allE_node, rows7130, irow7121, rows7131]
  all_goals rfl

theorem atot7121 : totK PA10K2 A10K2.u7121 = [0, 0, 107213596712, 1486244558491, 4068785003697, 3504007443523, 748726174784, 23799715721, 0, 0] := by
  rw [show A10K2.u7121 = KTree.node A10K2.t7130 (nat_lit 117699740) (nat_lit 8376348058) (nat_lit 0) A10K2.t7131 from rfl, totK_node, tot7130, tot7131]
  decide +kernel

theorem arows7123 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7123 = true := by
  rw [show A10K2.u7123 = KTree.node A10K2.t7132 (nat_lit 117705029) (nat_lit 6941624773) (nat_lit 0) A10K2.t7133 from rfl, allE_node, rows7132, irow7123, rows7133]
  all_goals rfl

theorem atot7123 : totK PA10K2 A10K2.u7123 = [0, 0, 867356095836, 3284175063488, 3797055177435, 1467703813392, 311539287255, 37310410385, 0, 0] := by
  rw [show A10K2.u7123 = KTree.node A10K2.t7132 (nat_lit 117705029) (nat_lit 6941624773) (nat_lit 0) A10K2.t7133 from rfl, totK_node, tot7132, tot7133]
  decide +kernel

theorem arows7124 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7124 = true := by
  rw [show A10K2.u7124 = KTree.node A10K2.t7134 (nat_lit 117709838) (nat_lit 14594430816) (nat_lit 0) A10K2.t7135 from rfl, allE_node, rows7134, irow7124, rows7135]
  all_goals rfl

theorem atot7124 : totK PA10K2 A10K2.u7124 = [0, 0, 410831171158, 2087254490400, 3795239267380, 2587139049972, 549366707377, 30831673886, 0, 0] := by
  rw [show A10K2.u7124 = KTree.node A10K2.t7134 (nat_lit 117709838) (nat_lit 14594430816) (nat_lit 0) A10K2.t7135 from rfl, totK_node, tot7134, tot7135]
  decide +kernel

theorem arows7129 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7129 = true := by
  rw [show A10K2.u7129 = KTree.node A10K2.t7136 (nat_lit 117724323) (nat_lit 8935066624) (nat_lit 0) A10K2.t7137 from rfl, allE_node, rows7136, irow7129, rows7137]
  all_goals rfl

theorem atot7129 : totK PA10K2 A10K2.u7129 = [0, 0, 568942610553, 2649838684828, 3874917008195, 1727530719478, 212058150804, 5705019915, 0, 0] := by
  rw [show A10K2.u7129 = KTree.node A10K2.t7136 (nat_lit 117724323) (nat_lit 8935066624) (nat_lit 0) A10K2.t7137 from rfl, totK_node, tot7136, tot7137]
  decide +kernel

theorem arows7130 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7130 = true := by
  rw [show A10K2.u7130 = KTree.node A10K2.t7138 (nat_lit 117730916) (nat_lit 8751701039) (nat_lit 0) A10K2.t7139 from rfl, allE_node, rows7138, irow7130, rows7139]
  all_goals rfl

theorem atot7130 : totK PA10K2 A10K2.u7130 = [0, 0, 487758371019, 2568953410579, 4281183823205, 2441862847943, 362652636197, 6853348008, 0, 0] := by
  rw [show A10K2.u7130 = KTree.node A10K2.t7138 (nat_lit 117730916) (nat_lit 8751701039) (nat_lit 0) A10K2.t7139 from rfl, totK_node, tot7138, tot7139]
  decide +kernel

theorem arows7132 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7132 = true := by
  rw [show A10K2.u7132 = KTree.node A10K2.t7140 (nat_lit 117735998) (nat_lit 15032927524) (nat_lit 0) A10K2.t7141 from rfl, allE_node, rows7140, irow7132, rows7141]
  all_goals rfl

theorem atot7132 : totK PA10K2 A10K2.u7132 = [0, 0, 0, 1124235074124, 3842064430800, 3664968413480, 925236400459, 59400237386, 0, 0] := by
  rw [show A10K2.u7132 = KTree.node A10K2.t7140 (nat_lit 117735998) (nat_lit 15032927524) (nat_lit 0) A10K2.t7141 from rfl, totK_node, tot7140, tot7141]
  decide +kernel

theorem arows7133 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7133 = true := by
  rw [show A10K2.u7133 = KTree.node A10K2.t7142 (nat_lit 117741725) (nat_lit 5076261389) (nat_lit 0) A10K2.t7143 from rfl, allE_node, rows7142, irow7133, rows7143]
  all_goals rfl

theorem atot7133 : totK PA10K2 A10K2.u7133 = [0, 0, 0, 287930791013, 1988058985242, 3907088648613, 2578840725936, 544436471612, 30605747850, 0] := by
  rw [show A10K2.u7133 = KTree.node A10K2.t7142 (nat_lit 117741725) (nat_lit 5076261389) (nat_lit 0) A10K2.t7143 from rfl, totK_node, tot7142, tot7143]
  decide +kernel

theorem arows7136 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7136 = true := by
  rw [show A10K2.u7136 = KTree.node A10K2.t7144 (nat_lit 117755908) (nat_lit 12297737635) (nat_lit 0) A10K2.t7145 from rfl, allE_node, rows7144, irow7136, rows7145]
  all_goals rfl

theorem atot7136 : totK PA10K2 A10K2.u7136 = [0, 0, 0, 499470737805, 2463026234137, 3806684418247, 1754358597634, 227731724327, 5528811039, 0] := by
  rw [show A10K2.u7136 = KTree.node A10K2.t7144 (nat_lit 117755908) (nat_lit 12297737635) (nat_lit 0) A10K2.t7145 from rfl, totK_node, tot7144, tot7145]
  decide +kernel

theorem arows7137 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7137 = true := by
  rw [show A10K2.u7137 = KTree.node A10K2.t7146 (nat_lit 117763638) (nat_lit 16512951031) (nat_lit 0) A10K2.t7147 from rfl, allE_node, rows7146, irow7137, rows7147]
  all_goals rfl

theorem atot7137 : totK PA10K2 A10K2.u7137 = [0, 0, 470372318891, 2188131835976, 3805000276772, 2807537896663, 671002234685, 43911449185, 0, 0] := by
  rw [show A10K2.u7137 = KTree.node A10K2.t7146 (nat_lit 117763638) (nat_lit 16512951031) (nat_lit 0) A10K2.t7147 from rfl, totK_node, tot7146, tot7147]
  decide +kernel

theorem arows7139 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7139 = true := by
  rw [show A10K2.u7139 = KTree.node A10K2.t7148 (nat_lit 117838164) (nat_lit 12318947998) (nat_lit 0) A10K2.t7149 from rfl, allE_node, rows7148, irow7139, rows7149]
  all_goals rfl

theorem atot7139 : totK PA10K2 A10K2.u7139 = [0, 0, 324860638317, 2053518627158, 3997492383596, 2624232508926, 546802839611, 30831673886, 0, 0] := by
  rw [show A10K2.u7139 = KTree.node A10K2.t7148 (nat_lit 117838164) (nat_lit 12318947998) (nat_lit 0) A10K2.t7149 from rfl, totK_node, tot7148, tot7149]
  decide +kernel

theorem arows7140 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7140 = true := by
  rw [show A10K2.u7140 = KTree.node A10K2.t7150 (nat_lit 117848862) (nat_lit 2029857046) (nat_lit 8) A10K2.t7151 from rfl, allE_node, rows7150, irow7140, rows7151]
  all_goals rfl

theorem atot7140 : totK PA10K2 A10K2.u7140 = [0, 0, 778974098074, 2984834972246, 3847047992804, 1674992865459, 177383459785, 6034215561, 0, 0] := by
  rw [show A10K2.u7140 = KTree.node A10K2.t7150 (nat_lit 117848862) (nat_lit 2029857046) (nat_lit 8) A10K2.t7151 from rfl, totK_node, tot7150, tot7151]
  decide +kernel

theorem arows7144 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7144 = true := by
  rw [show A10K2.u7144 = KTree.node A10K2.t7152 (nat_lit 117855587) (nat_lit 9355842215) (nat_lit 0) A10K2.t7153 from rfl, allE_node, rows7152, irow7144, rows7153]
  all_goals rfl

theorem atot7144 : totK PA10K2 A10K2.u7144 = [0, 0, 214452326151, 2005775408627, 4128983567663, 2466773742829, 412002780473, 26601763172, 0, 0] := by
  rw [show A10K2.u7144 = KTree.node A10K2.t7152 (nat_lit 117855587) (nat_lit 9355842215) (nat_lit 0) A10K2.t7153 from rfl, totK_node, tot7152, tot7153]
  decide +kernel

theorem arows7145 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7145 = true := by
  rw [show A10K2.u7145 = KTree.node A10K2.t7154 (nat_lit 117870194) (nat_lit 5842549717) (nat_lit 0) A10K2.t7155 from rfl, allE_node, rows7154, irow7145, rows7155]
  all_goals rfl

theorem atot7145 : totK PA10K2 A10K2.u7145 = [0, 0, 0, 1010843613617, 3768539514932, 3729958756078, 863142584574, 43857696895, 0, 0] := by
  rw [show A10K2.u7145 = KTree.node A10K2.t7154 (nat_lit 117870194) (nat_lit 5842549717) (nat_lit 0) A10K2.t7155 from rfl, totK_node, tot7154, tot7155]
  decide +kernel

theorem arows7147 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7147 = true := by
  rw [show A10K2.u7147 = KTree.node A10K2.t7156 (nat_lit 117887011) (nat_lit 6807655617) (nat_lit 0) A10K2.t7157 from rfl, allE_node, rows7156, irow7147, rows7157]
  all_goals rfl

theorem atot7147 : totK PA10K2 A10K2.u7147 = [0, 0, 115548944004, 740736169928, 2612744115752, 3787034044323, 1590443910944, 203613753835, 5676195732, 0] := by
  rw [show A10K2.u7147 = KTree.node A10K2.t7156 (nat_lit 117887011) (nat_lit 6807655617) (nat_lit 0) A10K2.t7157 from rfl, totK_node, tot7156, tot7157]
  decide +kernel

theorem arows7148 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7148 = true := by
  rw [show A10K2.u7148 = KTree.node A10K2.t7158 (nat_lit 117902492) (nat_lit 3609164586) (nat_lit 0) A10K2.t7159 from rfl, allE_node, rows7158, irow7148, rows7159]
  all_goals rfl

theorem atot7148 : totK PA10K2 A10K2.u7148 = [0, 0, 691762080668, 2967705686949, 4036278320607, 1830804306199, 291434075204, 20058242317, 0, 0] := by
  rw [show A10K2.u7148 = KTree.node A10K2.t7158 (nat_lit 117902492) (nat_lit 3609164586) (nat_lit 0) A10K2.t7159 from rfl, totK_node, tot7158, tot7159]
  decide +kernel

theorem arows7151 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7151 = true := by
  rw [show A10K2.u7151 = KTree.node A10K2.t7160 (nat_lit 117909228) (nat_lit 8749460879) (nat_lit 0) A10K2.t7161 from rfl, allE_node, rows7160, irow7151, rows7161]
  all_goals rfl

theorem atot7151 : totK PA10K2 A10K2.u7151 = [0, 0, 512075970115, 2602428122321, 4324905214805, 2460745817518, 339729477501, 5255105852, 0, 0] := by
  rw [show A10K2.u7151 = KTree.node A10K2.t7160 (nat_lit 117909228) (nat_lit 8749460879) (nat_lit 0) A10K2.t7161 from rfl, totK_node, tot7160, tot7161]
  decide +kernel

theorem arows7152 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7152 = true := by
  rw [show A10K2.u7152 = KTree.node A10K2.t7162 (nat_lit 117925041) (nat_lit 5572303477) (nat_lit 0) A10K2.t7163 from rfl, allE_node, rows7162, irow7152, rows7163]
  all_goals rfl

theorem atot7152 : totK PA10K2 A10K2.u7152 = [0, 0, 844755229172, 3318591162513, 4077835743744, 1659646237113, 196663333344, 7151180950, 0, 0] := by
  rw [show A10K2.u7152 = KTree.node A10K2.t7162 (nat_lit 117925041) (nat_lit 5572303477) (nat_lit 0) A10K2.t7163 from rfl, totK_node, tot7162, tot7163]
  decide +kernel

theorem arows7154 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7154 = true := by
  rw [show A10K2.u7154 = KTree.node A10K2.t7164 (nat_lit 117929746) (nat_lit 14304357421) (nat_lit 0) A10K2.t7165 from rfl, allE_node, rows7164, irow7154, rows7165]
  all_goals rfl

theorem atot7154 : totK PA10K2 A10K2.u7154 = [0, 228817696234, 572999667288, 1238968920974, 3400494254559, 3517749658000, 1008040481605, 62368562949, 0, 0] := by
  rw [show A10K2.u7154 = KTree.node A10K2.t7164 (nat_lit 117929746) (nat_lit 14304357421) (nat_lit 0) A10K2.t7165 from rfl, totK_node, tot7164, tot7165]
  decide +kernel

theorem arows7155 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7155 = true := by
  rw [show A10K2.u7155 = KTree.node A10K2.t7166 (nat_lit 118492256) (nat_lit 13857200976) (nat_lit 0) A10K2.t7167 from rfl, allE_node, rows7166, irow7155, rows7167]
  all_goals rfl

theorem atot7155 : totK PA10K2 A10K2.u7155 = [0, 601508490278, 2804909350269, 4032143163935, 1891616764705, 304517162564, 20070762815, 0, 0, 0] := by
  rw [show A10K2.u7155 = KTree.node A10K2.t7166 (nat_lit 118492256) (nat_lit 13857200976) (nat_lit 0) A10K2.t7167 from rfl, totK_node, tot7166, tot7167]
  decide +kernel

theorem arows7165 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7165 = true := by
  rw [show A10K2.u7165 = KTree.node A10K2.t7168 (nat_lit 118505591) (nat_lit 13119583939) (nat_lit 0) A10K2.t7169 from rfl, allE_node, rows7168, irow7165, rows7169]
  all_goals rfl

theorem atot7165 : totK PA10K2 A10K2.u7165 = [0, 631242532436, 2539068111265, 3770838795164, 2204213106960, 368501391839, 10760911071, 0, 0, 0] := by
  rw [show A10K2.u7165 = KTree.node A10K2.t7168 (nat_lit 118505591) (nat_lit 13119583939) (nat_lit 0) A10K2.t7169 from rfl, totK_node, tot7168, tot7169]
  decide +kernel

theorem arows7166 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7166 = true := by
  rw [show A10K2.u7166 = KTree.node A10K2.t7170 (nat_lit 118511717) (nat_lit 7128301732) (nat_lit 0) A10K2.t7171 from rfl, allE_node, rows7170, irow7166, rows7171]
  all_goals rfl

theorem atot7166 : totK PA10K2 A10K2.u7166 = [0, 416078085182, 2469137111250, 4143378091153, 2145463123211, 301105607360, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u7166 = KTree.node A10K2.t7170 (nat_lit 118511717) (nat_lit 7128301732) (nat_lit 0) A10K2.t7171 from rfl, totK_node, tot7170, tot7171]
  decide +kernel

theorem arows7168 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7168 = true := by
  rw [show A10K2.u7168 = KTree.node A10K2.t7172 (nat_lit 118518273) (nat_lit 10545653485) (nat_lit 0) A10K2.t7173 from rfl, allE_node, rows7172, irow7168, rows7173]
  all_goals rfl

theorem atot7168 : totK PA10K2 A10K2.u7168 = [0, 295757175837, 1937689529198, 4006316515390, 3161441370413, 780293939760, 42633500131, 0, 0, 0] := by
  rw [show A10K2.u7168 = KTree.node A10K2.t7172 (nat_lit 118518273) (nat_lit 10545653485) (nat_lit 0) A10K2.t7173 from rfl, totK_node, tot7172, tot7173]
  decide +kernel

theorem arows7169 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7169 = true := by
  rw [show A10K2.u7169 = KTree.node A10K2.t7174 (nat_lit 118524983) (nat_lit 14838044417) (nat_lit 0) A10K2.t7175 from rfl, allE_node, rows7174, irow7169, rows7175]
  all_goals rfl

theorem atot7169 : totK PA10K2 A10K2.u7169 = [0, 0, 624375913768, 2926035695205, 3999080647130, 1721771020672, 289973532675, 20060612110, 0, 0] := by
  rw [show A10K2.u7169 = KTree.node A10K2.t7174 (nat_lit 118524983) (nat_lit 14838044417) (nat_lit 0) A10K2.t7175 from rfl, totK_node, tot7174, tot7175]
  decide +kernel

theorem arows7172 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7172 = true := by
  rw [show A10K2.u7172 = KTree.node A10K2.t7176 (nat_lit 118538525) (nat_lit 6332833813) (nat_lit 0) A10K2.t7177 from rfl, allE_node, rows7176, irow7172, rows7177]
  all_goals rfl

theorem atot7172 : totK PA10K2 A10K2.u7172 = [0, 0, 688446050392, 2723691514610, 3739464679951, 1905580268782, 322660597006, 10589884120, 0, 0] := by
  rw [show A10K2.u7172 = KTree.node A10K2.t7176 (nat_lit 118538525) (nat_lit 6332833813) (nat_lit 0) A10K2.t7177 from rfl, totK_node, tot7176, tot7177]
  decide +kernel

theorem arows7173 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7173 = true := by
  rw [show A10K2.u7173 = KTree.node A10K2.t7178 (nat_lit 118544670) (nat_lit 5542723930) (nat_lit 0) A10K2.t7179 from rfl, allE_node, rows7178, irow7173, rows7179]
  all_goals rfl

theorem atot7173 : totK PA10K2 A10K2.u7173 = [0, 0, 542362048158, 2809585892707, 4172908863062, 1818772146552, 219178372242, 5546304973, 0, 0] := by
  rw [show A10K2.u7173 = KTree.node A10K2.t7178 (nat_lit 118544670) (nat_lit 5542723930) (nat_lit 0) A10K2.t7179 from rfl, totK_node, tot7178, tot7179]
  decide +kernel

theorem arows7175 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7175 = true := by
  rw [show A10K2.u7175 = KTree.node A10K2.t7180 (nat_lit 118621112) (nat_lit 14062283302) (nat_lit 0) A10K2.t7181 from rfl, allE_node, rows7180, irow7175, rows7181]
  all_goals rfl

theorem atot7175 : totK PA10K2 A10K2.u7175 = [0, 764175327537, 2968127717261, 3729219462099, 1901611130444, 467365260570, 30829329317, 0, 0, 0] := by
  rw [show A10K2.u7175 = KTree.node A10K2.t7180 (nat_lit 118621112) (nat_lit 14062283302) (nat_lit 0) A10K2.t7181 from rfl, totK_node, tot7180, tot7181]
  decide +kernel

theorem arows7176 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7176 = true := by
  rw [show A10K2.u7176 = KTree.node A10K2.t7182 (nat_lit 118627106) (nat_lit 11460350707) (nat_lit 0) A10K2.t7183 from rfl, allE_node, rows7182, irow7176, rows7183]
  all_goals rfl

theorem atot7176 : totK PA10K2 A10K2.u7176 = [0, 454839317077, 2112333946146, 3790153831335, 2631107094821, 568651420488, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u7176 = KTree.node A10K2.t7182 (nat_lit 118627106) (nat_lit 11460350707) (nat_lit 0) A10K2.t7183 from rfl, totK_node, tot7182, tot7183]
  decide +kernel

theorem arows7180 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7180 = true := by
  rw [show A10K2.u7180 = KTree.node A10K2.t7184 (nat_lit 118634657) (nat_lit 7632028291) (nat_lit 0) A10K2.t7185 from rfl, allE_node, rows7184, irow7180, rows7185]
  all_goals rfl

theorem atot7180 : totK PA10K2 A10K2.u7180 = [0, 422633631952, 2197265106810, 3881994497672, 2495090233107, 498291744799, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u7180 = KTree.node A10K2.t7184 (nat_lit 118634657) (nat_lit 7632028291) (nat_lit 0) A10K2.t7185 from rfl, totK_node, tot7184, tot7185]
  decide +kernel

theorem arows7181 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7181 = true := by
  rw [show A10K2.u7181 = KTree.node A10K2.t7186 (nat_lit 118639387) (nat_lit 8679776884) (nat_lit 0) A10K2.t7187 from rfl, allE_node, rows7186, irow7181, rows7187]
  all_goals rfl

theorem atot7181 : totK PA10K2 A10K2.u7181 = [0, 505902438422, 2735913961326, 4210219904138, 1798170021039, 146865153612, 0, 0, 0, 0] := by
  rw [show A10K2.u7181 = KTree.node A10K2.t7186 (nat_lit 118639387) (nat_lit 8679776884) (nat_lit 0) A10K2.t7187 from rfl, totK_node, tot7186, tot7187]
  decide +kernel

theorem arows7183 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7183 = true := by
  rw [show A10K2.u7183 = KTree.node A10K2.t7188 (nat_lit 118655203) (nat_lit 10007938196) (nat_lit 0) A10K2.t7189 from rfl, allE_node, rows7188, irow7183, rows7189]
  all_goals rfl

theorem atot7183 : totK PA10K2 A10K2.u7183 = [0, 0, 1042120817309, 3771372974835, 3831093077100, 973409983455, 45137667897, 0, 0, 0] := by
  rw [show A10K2.u7183 = KTree.node A10K2.t7188 (nat_lit 118655203) (nat_lit 10007938196) (nat_lit 0) A10K2.t7189 from rfl, totK_node, tot7188, tot7189]
  decide +kernel

theorem arows7184 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7184 = true := by
  rw [show A10K2.u7184 = KTree.node A10K2.t7190 (nat_lit 118669668) (nat_lit 13775768551) (nat_lit 0) A10K2.t7191 from rfl, allE_node, rows7190, irow7184, rows7191]
  all_goals rfl

theorem atot7184 : totK PA10K2 A10K2.u7184 = [0, 0, 952685795955, 3477661195502, 3824232299733, 1081909347090, 82738314188, 0, 0, 0] := by
  rw [show A10K2.u7184 = KTree.node A10K2.t7190 (nat_lit 118669668) (nat_lit 13775768551) (nat_lit 0) A10K2.t7191 from rfl, totK_node, tot7190, tot7191]
  decide +kernel

theorem arows7187 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7187 = true := by
  rw [show A10K2.u7187 = KTree.node A10K2.t7192 (nat_lit 118675528) (nat_lit 11534783915) (nat_lit 0) A10K2.t7193 from rfl, allE_node, rows7192, irow7187, rows7193]
  all_goals rfl

theorem atot7187 : totK PA10K2 A10K2.u7187 = [0, 0, 446891948183, 2612011534105, 4101953249744, 1911455495206, 286048911365, 6354482628, 0, 0] := by
  rw [show A10K2.u7187 = KTree.node A10K2.t7192 (nat_lit 118675528) (nat_lit 11534783915) (nat_lit 0) A10K2.t7193 from rfl, totK_node, tot7192, tot7193]
  decide +kernel

theorem arows7188 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7188 = true := by
  rw [show A10K2.u7188 = KTree.node A10K2.t7194 (nat_lit 118754931) (nat_lit 4425636671) (nat_lit 0) A10K2.t7195 from rfl, allE_node, rows7194, irow7188, rows7195]
  all_goals rfl

theorem atot7188 : totK PA10K2 A10K2.u7188 = [0, 0, 523813060156, 2535218229773, 3950759534886, 2134326656547, 405905507862, 25371180993, 0, 0] := by
  rw [show A10K2.u7188 = KTree.node A10K2.t7194 (nat_lit 118754931) (nat_lit 4425636671) (nat_lit 0) A10K2.t7195 from rfl, totK_node, tot7194, tot7195]
  decide +kernel

theorem arows7190 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7190 = true := by
  rw [show A10K2.u7190 = KTree.node A10K2.t7196 (nat_lit 118768247) (nat_lit 10081394154) (nat_lit 0) A10K2.t7197 from rfl, allE_node, rows7196, irow7190, rows7197]
  all_goals rfl

theorem atot7190 : totK PA10K2 A10K2.u7190 = [0, 0, 749928254756, 3024373525609, 3851113069932, 1629353200385, 205450542829, 5447185874, 0, 0] := by
  rw [show A10K2.u7190 = KTree.node A10K2.t7196 (nat_lit 118768247) (nat_lit 10081394154) (nat_lit 0) A10K2.t7197 from rfl, totK_node, tot7196, tot7197]
  decide +kernel

theorem arows7191 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7191 = true := by
  rw [show A10K2.u7191 = KTree.node A10K2.t7198 (nat_lit 118774610) (nat_lit 11964541943) (nat_lit 0) A10K2.t7199 from rfl, allE_node, rows7198, irow7191, rows7199]
  all_goals rfl

theorem atot7191 : totK PA10K2 A10K2.u7191 = [0, 0, 593149538699, 2735997456598, 4120146527808, 1984275730510, 234776203894, 6354482628, 0, 0] := by
  rw [show A10K2.u7191 = KTree.node A10K2.t7198 (nat_lit 118774610) (nat_lit 11964541943) (nat_lit 0) A10K2.t7199 from rfl, totK_node, tot7198, tot7199]
  decide +kernel

end QECKChecks.A10K2
