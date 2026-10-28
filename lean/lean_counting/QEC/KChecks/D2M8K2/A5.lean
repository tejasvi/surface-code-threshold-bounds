import QEC.Count.ChunksK3
import QEC.KChecks.D2M8K2.A4

namespace QECKChecks.D2M8K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows5993 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5993 = true := by
  rw [show D2M8K2.u5993 = KTree.node D2M8K2.t6000 (nat_lit 12779085) (nat_lit 1078219918) (nat_lit 0) D2M8K2.t6001 from rfl, allE_node, rows6000, irow5993, rows6001]
  all_goals rfl

theorem atot5993 : totK PD2M8K2 D2M8K2.u5993 = [0, 88183717169, 506660322155, 819847230843, 371065383408, 29321085627, 0, 0] := by
  rw [show D2M8K2.u5993 = KTree.node D2M8K2.t6000 (nat_lit 12779085) (nat_lit 1078219918) (nat_lit 0) D2M8K2.t6001 from rfl, totK_node, tot6000, tot6001]
  decide +kernel

theorem arows5994 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5994 = true := by
  rw [show D2M8K2.u5994 = KTree.node D2M8K2.t6002 (nat_lit 12780371) (nat_lit 2361047420) (nat_lit 0) D2M8K2.t6003 from rfl, allE_node, rows6002, irow5994, rows6003]
  all_goals rfl

theorem atot5994 : totK PD2M8K2 D2M8K2.u5994 = [0, 229123980406, 691957806773, 681670498777, 217925522577, 8166240555, 0, 0] := by
  rw [show D2M8K2.u5994 = KTree.node D2M8K2.t6002 (nat_lit 12780371) (nat_lit 2361047420) (nat_lit 0) D2M8K2.t6003 from rfl, totK_node, tot6002, tot6003]
  decide +kernel

theorem arows5996 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5996 = true := by
  rw [show D2M8K2.u5996 = KTree.node D2M8K2.t6004 (nat_lit 12781848) (nat_lit 3571591327) (nat_lit 0) D2M8K2.t6005 from rfl, allE_node, rows6004, irow5996, rows6005]
  all_goals rfl

theorem atot5996 : totK PD2M8K2 D2M8K2.u5996 = [0, 208833668132, 786728819865, 694160382497, 112545204032, 1164319620, 0, 0] := by
  rw [show D2M8K2.u5996 = KTree.node D2M8K2.t6004 (nat_lit 12781848) (nat_lit 3571591327) (nat_lit 0) D2M8K2.t6005 from rfl, totK_node, tot6004, tot6005]
  decide +kernel

theorem arows5997 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5997 = true := by
  rw [show D2M8K2.u5997 = KTree.node D2M8K2.t6006 (nat_lit 12783504) (nat_lit 3491333223) (nat_lit 0) D2M8K2.t6007 from rfl, allE_node, rows6006, irow5997, rows6007]
  all_goals rfl

theorem atot5997 : totK PD2M8K2 D2M8K2.u5997 = [0, 165819165509, 641710404938, 746401902804, 222338002512, 11885407614, 0, 0] := by
  rw [show D2M8K2.u5997 = KTree.node D2M8K2.t6006 (nat_lit 12783504) (nat_lit 3491333223) (nat_lit 0) D2M8K2.t6007 from rfl, totK_node, tot6006, tot6007]
  decide +kernel

theorem arows6000 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6000 = true := by
  rw [show D2M8K2.u6000 = KTree.node D2M8K2.t6008 (nat_lit 12788378) (nat_lit 4225304539) (nat_lit 0) D2M8K2.t6009 from rfl, allE_node, rows6008, irow6000, rows6009]
  all_goals rfl

theorem atot6000 : totK PD2M8K2 D2M8K2.u6000 = [0, 245890294727, 806279276973, 641535011658, 95371983825, 1096505104, 0, 0] := by
  rw [show D2M8K2.u6000 = KTree.node D2M8K2.t6008 (nat_lit 12788378) (nat_lit 4225304539) (nat_lit 0) D2M8K2.t6009 from rfl, totK_node, tot6008, tot6009]
  decide +kernel

theorem arows6001 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6001 = true := by
  rw [show D2M8K2.u6001 = KTree.node D2M8K2.t6010 (nat_lit 12790662) (nat_lit 3470944662) (nat_lit 0) D2M8K2.t6011 from rfl, allE_node, rows6010, irow6001, rows6011]
  all_goals rfl

theorem atot6001 : totK PD2M8K2 D2M8K2.u6001 = [0, 199801420773, 723405267976, 734602013773, 150888572276, 3884009855, 0, 0] := by
  rw [show D2M8K2.u6001 = KTree.node D2M8K2.t6010 (nat_lit 12790662) (nat_lit 3470944662) (nat_lit 0) D2M8K2.t6011 from rfl, totK_node, tot6010, tot6011]
  decide +kernel

theorem arows6003 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6003 = true := by
  rw [show D2M8K2.u6003 = KTree.node D2M8K2.t6012 (nat_lit 12792188) (nat_lit 2011980158) (nat_lit 0) D2M8K2.t6013 from rfl, allE_node, rows6012, irow6003, rows6013]
  all_goals rfl

theorem atot6003 : totK PD2M8K2 D2M8K2.u6003 = [0, 213309932166, 781975359928, 687802049937, 117988790020, 1232398321, 0, 0] := by
  rw [show D2M8K2.u6003 = KTree.node D2M8K2.t6012 (nat_lit 12792188) (nat_lit 2011980158) (nat_lit 0) D2M8K2.t6013 from rfl, totK_node, tot6012, tot6013]
  decide +kernel

theorem arows6004 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6004 = true := by
  rw [show D2M8K2.u6004 = KTree.node D2M8K2.t6014 (nat_lit 12793944) (nat_lit 3560977960) (nat_lit 0) D2M8K2.t6015 from rfl, allE_node, rows6014, irow6004, rows6015]
  all_goals rfl

theorem atot6004 : totK PD2M8K2 D2M8K2.u6004 = [0, 0, 408029623032, 968180651504, 376223694752, 17938303018, 0, 0] := by
  rw [show D2M8K2.u6004 = KTree.node D2M8K2.t6014 (nat_lit 12793944) (nat_lit 3560977960) (nat_lit 0) D2M8K2.t6015 from rfl, totK_node, tot6014, tot6015]
  decide +kernel

theorem arows6011 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6011 = true := by
  rw [show D2M8K2.u6011 = KTree.node D2M8K2.t6016 (nat_lit 12797961) (nat_lit 1897289975) (nat_lit 0) D2M8K2.t6017 from rfl, allE_node, rows6016, irow6011, rows6017]
  all_goals rfl

theorem atot6011 : totK PD2M8K2 D2M8K2.u6011 = [0, 0, 404051351757, 949206646739, 421855113552, 30722565051, 0, 0] := by
  rw [show D2M8K2.u6011 = KTree.node D2M8K2.t6016 (nat_lit 12797961) (nat_lit 1897289975) (nat_lit 0) D2M8K2.t6017 from rfl, totK_node, tot6016, tot6017]
  decide +kernel

theorem arows6012 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6012 = true := by
  rw [show D2M8K2.u6012 = KTree.node D2M8K2.t6018 (nat_lit 12799202) (nat_lit 3991730768) (nat_lit 0) D2M8K2.t6019 from rfl, allE_node, rows6018, irow6012, rows6019]
  all_goals rfl

theorem atot6012 : totK PD2M8K2 D2M8K2.u6012 = [0, 0, 354442258707, 943186873521, 464379116513, 27874731946, 0, 0] := by
  rw [show D2M8K2.u6012 = KTree.node D2M8K2.t6018 (nat_lit 12799202) (nat_lit 3991730768) (nat_lit 0) D2M8K2.t6019 from rfl, totK_node, tot6018, tot6019]
  decide +kernel

theorem arows6014 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6014 = true := by
  rw [show D2M8K2.u6014 = KTree.node D2M8K2.t6020 (nat_lit 12802423) (nat_lit 1678251100) (nat_lit 0) D2M8K2.t6021 from rfl, allE_node, rows6020, irow6014, rows6021]
  all_goals rfl

theorem atot6014 : totK PD2M8K2 D2M8K2.u6014 = [0, 0, 265618885128, 868454148146, 601441162367, 49606939078, 0, 0] := by
  rw [show D2M8K2.u6014 = KTree.node D2M8K2.t6020 (nat_lit 12802423) (nat_lit 1678251100) (nat_lit 0) D2M8K2.t6021 from rfl, totK_node, tot6020, tot6021]
  decide +kernel

theorem arows6015 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6015 = true := by
  rw [show D2M8K2.u6015 = KTree.node D2M8K2.t6022 (nat_lit 12804264) (nat_lit 2120536815) (nat_lit 0) D2M8K2.t6023 from rfl, allE_node, rows6022, irow6015, rows6023]
  all_goals rfl

theorem atot6015 : totK PD2M8K2 D2M8K2.u6015 = [0, 0, 181444095191, 678283761373, 715269147601, 173835242297, 5320761635, 0] := by
  rw [show D2M8K2.u6015 = KTree.node D2M8K2.t6022 (nat_lit 12804264) (nat_lit 2120536815) (nat_lit 0) D2M8K2.t6023 from rfl, totK_node, tot6022, tot6023]
  decide +kernel

theorem arows6018 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6018 = true := by
  rw [show D2M8K2.u6018 = KTree.node D2M8K2.t6024 (nat_lit 12809184) (nat_lit 3567677278) (nat_lit 0) D2M8K2.t6025 from rfl, allE_node, rows6024, irow6018, rows6025]
  all_goals rfl

theorem atot6018 : totK PD2M8K2 D2M8K2.u6018 = [0, 0, 228072063964, 889214255182, 607634190975, 46764219528, 0, 0] := by
  rw [show D2M8K2.u6018 = KTree.node D2M8K2.t6024 (nat_lit 12809184) (nat_lit 3567677278) (nat_lit 0) D2M8K2.t6025 from rfl, totK_node, tot6024, tot6025]
  decide +kernel

theorem arows6019 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6019 = true := by
  rw [show D2M8K2.u6019 = KTree.node D2M8K2.t6026 (nat_lit 12811785) (nat_lit 1600195738) (nat_lit 0) D2M8K2.t6027 from rfl, allE_node, rows6026, irow6019, rows6027]
  all_goals rfl

theorem atot6019 : totK PD2M8K2 D2M8K2.u6019 = [0, 0, 322139309876, 804855603818, 564083962220, 83497344797, 1225787871, 0] := by
  rw [show D2M8K2.u6019 = KTree.node D2M8K2.t6026 (nat_lit 12811785) (nat_lit 1600195738) (nat_lit 0) D2M8K2.t6027 from rfl, totK_node, tot6026, tot6027]
  decide +kernel

theorem arows6021 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6021 = true := by
  rw [show D2M8K2.u6021 = KTree.node D2M8K2.t6028 (nat_lit 12818783) (nat_lit 2034847228) (nat_lit 0) D2M8K2.t6029 from rfl, allE_node, rows6028, irow6021, rows6029]
  all_goals rfl

theorem atot6021 : totK PD2M8K2 D2M8K2.u6021 = [0, 255899833194, 714802732145, 637454449862, 217111817602, 13065910070, 0, 0] := by
  rw [show D2M8K2.u6021 = KTree.node D2M8K2.t6028 (nat_lit 12818783) (nat_lit 2034847228) (nat_lit 0) D2M8K2.t6029 from rfl, totK_node, tot6028, tot6029]
  decide +kernel

theorem arows6022 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6022 = true := by
  rw [show D2M8K2.u6022 = KTree.node D2M8K2.t6030 (nat_lit 12819980) (nat_lit 1460313800) (nat_lit 0) D2M8K2.t6031 from rfl, allE_node, rows6030, irow6022, rows6031]
  all_goals rfl

theorem atot6022 : totK PD2M8K2 D2M8K2.u6022 = [0, 173663064406, 647430254535, 687412891169, 267347669037, 25298831311, 0, 0] := by
  rw [show D2M8K2.u6022 = KTree.node D2M8K2.t6030 (nat_lit 12819980) (nat_lit 1460313800) (nat_lit 0) D2M8K2.t6031 from rfl, totK_node, tot6030, tot6031]
  decide +kernel

theorem arows6026 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6026 = true := by
  rw [show D2M8K2.u6026 = KTree.node D2M8K2.t6032 (nat_lit 12821516) (nat_lit 3198691698) (nat_lit 0) D2M8K2.t6033 from rfl, allE_node, rows6032, irow6026, rows6033]
  all_goals rfl

theorem atot6026 : totK PD2M8K2 D2M8K2.u6026 = [0, 161387171172, 573101765198, 760653391118, 301751945847, 12186868223, 0, 0] := by
  rw [show D2M8K2.u6026 = KTree.node D2M8K2.t6032 (nat_lit 12821516) (nat_lit 3198691698) (nat_lit 0) D2M8K2.t6033 from rfl, totK_node, tot6032, tot6033]
  decide +kernel

theorem arows6027 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6027 = true := by
  rw [show D2M8K2.u6027 = KTree.node D2M8K2.t6034 (nat_lit 12826462) (nat_lit 3262579029) (nat_lit 0) D2M8K2.t6035 from rfl, allE_node, rows6034, irow6027, rows6035]
  all_goals rfl

theorem atot6027 : totK PD2M8K2 D2M8K2.u6027 = [0, 265480580905, 851233690834, 624177098893, 70192126504, 0, 0, 0] := by
  rw [show D2M8K2.u6027 = KTree.node D2M8K2.t6034 (nat_lit 12826462) (nat_lit 3262579029) (nat_lit 0) D2M8K2.t6035 from rfl, totK_node, tot6034, tot6035]
  decide +kernel

theorem arows6029 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6029 = true := by
  rw [show D2M8K2.u6029 = KTree.node D2M8K2.t6036 (nat_lit 12828156) (nat_lit 2168449680) (nat_lit 0) D2M8K2.t6037 from rfl, allE_node, rows6036, irow6029, rows6037]
  all_goals rfl

theorem atot6029 : totK PD2M8K2 D2M8K2.u6029 = [0, 96077652455, 556412479175, 842943453606, 272293182104, 13196099988, 0, 0] := by
  rw [show D2M8K2.u6029 = KTree.node D2M8K2.t6036 (nat_lit 12828156) (nat_lit 2168449680) (nat_lit 0) D2M8K2.t6037 from rfl, totK_node, tot6036, tot6037]
  decide +kernel

theorem arows6030 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6030 = true := by
  rw [show D2M8K2.u6030 = KTree.node D2M8K2.t6038 (nat_lit 12829629) (nat_lit 1563116754) (nat_lit 0) D2M8K2.t6039 from rfl, allE_node, rows6038, irow6030, rows6039]
  all_goals rfl

theorem atot6030 : totK PD2M8K2 D2M8K2.u6030 = [0, 303997591425, 881474701623, 560784729146, 53369339717, 0, 0, 0] := by
  rw [show D2M8K2.u6030 = KTree.node D2M8K2.t6038 (nat_lit 12829629) (nat_lit 1563116754) (nat_lit 0) D2M8K2.t6039 from rfl, totK_node, tot6038, tot6039]
  decide +kernel

theorem arows6033 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6033 = true := by
  rw [show D2M8K2.u6033 = KTree.node D2M8K2.t6040 (nat_lit 12831616) (nat_lit 3546317008) (nat_lit 0) D2M8K2.t6041 from rfl, allE_node, rows6040, irow6033, rows6041]
  all_goals rfl

theorem atot6033 : totK PD2M8K2 D2M8K2.u6033 = [0, 157098051438, 668432126379, 785278221579, 193858237854, 4980514959, 0, 0] := by
  rw [show D2M8K2.u6033 = KTree.node D2M8K2.t6040 (nat_lit 12831616) (nat_lit 3546317008) (nat_lit 0) D2M8K2.t6041 from rfl, totK_node, tot6040, tot6041]
  decide +kernel

theorem arows6034 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6034 = true := by
  rw [show D2M8K2.u6034 = KTree.node D2M8K2.t6042 (nat_lit 12833240) (nat_lit 3768533122) (nat_lit 0) D2M8K2.t6043 from rfl, allE_node, rows6042, irow6034, rows6043]
  all_goals rfl

theorem atot6034 : totK PD2M8K2 D2M8K2.u6034 = [0, 248737397208, 794822577975, 655677516730, 109105015002, 1232609433, 0, 0] := by
  rw [show D2M8K2.u6034 = KTree.node D2M8K2.t6042 (nat_lit 12833240) (nat_lit 3768533122) (nat_lit 0) D2M8K2.t6043 from rfl, totK_node, tot6042, tot6043]
  decide +kernel

theorem arows6036 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6036 = true := by
  rw [show D2M8K2.u6036 = KTree.node D2M8K2.t6044 (nat_lit 12835300) (nat_lit 3523967601) (nat_lit 0) D2M8K2.t6045 from rfl, allE_node, rows6044, irow6036, rows6045]
  all_goals rfl

theorem atot6036 : totK PD2M8K2 D2M8K2.u6036 = [0, 0, 403746904682, 946230240133, 421727252389, 32726465011, 0, 0] := by
  rw [show D2M8K2.u6036 = KTree.node D2M8K2.t6044 (nat_lit 12835300) (nat_lit 3523967601) (nat_lit 0) D2M8K2.t6045 from rfl, totK_node, tot6044, tot6045]
  decide +kernel

theorem arows6037 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6037 = true := by
  rw [show D2M8K2.u6037 = KTree.node D2M8K2.t6046 (nat_lit 12840223) (nat_lit 2333882139) (nat_lit 0) D2M8K2.t6047 from rfl, allE_node, rows6046, irow6037, rows6047]
  all_goals rfl

theorem atot6037 : totK PD2M8K2 D2M8K2.u6037 = [0, 0, 376475761187, 921609132836, 474714565155, 28449340043, 0, 0] := by
  rw [show D2M8K2.u6037 = KTree.node D2M8K2.t6046 (nat_lit 12840223) (nat_lit 2333882139) (nat_lit 0) D2M8K2.t6047 from rfl, totK_node, tot6046, tot6047]
  decide +kernel

theorem arows6042 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6042 = true := by
  rw [show D2M8K2.u6042 = KTree.node D2M8K2.t6048 (nat_lit 12846936) (nat_lit 3538692472) (nat_lit 0) D2M8K2.t6049 from rfl, allE_node, rows6048, irow6042, rows6049]
  all_goals rfl

theorem atot6042 : totK PD2M8K2 D2M8K2.u6042 = [0, 0, 380436492181, 929540033348, 458522014320, 32217764434, 0, 0] := by
  rw [show D2M8K2.u6042 = KTree.node D2M8K2.t6048 (nat_lit 12846936) (nat_lit 3538692472) (nat_lit 0) D2M8K2.t6049 from rfl, totK_node, tot6048, tot6049]
  decide +kernel

theorem arows6043 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6043 = true := by
  rw [show D2M8K2.u6043 = KTree.node D2M8K2.t6050 (nat_lit 12848721) (nat_lit 1393745135) (nat_lit 0) D2M8K2.t6051 from rfl, allE_node, rows6050, irow6043, rows6051]
  all_goals rfl

theorem atot6043 : totK PD2M8K2 D2M8K2.u6043 = [0, 0, 66305857479, 601784908899, 868848714478, 197328484525, 5352782441, 0] := by
  rw [show D2M8K2.u6043 = KTree.node D2M8K2.t6050 (nat_lit 12848721) (nat_lit 1393745135) (nat_lit 0) D2M8K2.t6051 from rfl, totK_node, tot6050, tot6051]
  decide +kernel

theorem arows6045 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6045 = true := by
  rw [show D2M8K2.u6045 = KTree.node D2M8K2.t6052 (nat_lit 12850299) (nat_lit 3748308372) (nat_lit 0) D2M8K2.t6053 from rfl, allE_node, rows6052, irow6045, rows6053]
  all_goals rfl

theorem atot6045 : totK PD2M8K2 D2M8K2.u6045 = [0, 0, 332822149836, 944848266799, 488180688611, 26085190163, 0, 0] := by
  rw [show D2M8K2.u6045 = KTree.node D2M8K2.t6052 (nat_lit 12850299) (nat_lit 3748308372) (nat_lit 0) D2M8K2.t6053 from rfl, totK_node, tot6052, tot6053]
  decide +kernel

theorem arows6046 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6046 = true := by
  rw [show D2M8K2.u6046 = KTree.node D2M8K2.t6054 (nat_lit 12852465) (nat_lit 1502131574) (nat_lit 0) D2M8K2.t6055 from rfl, allE_node, rows6054, irow6046, rows6055]
  all_goals rfl

theorem atot6046 : totK PD2M8K2 D2M8K2.u6046 = [0, 0, 180957591743, 727102384829, 748455685123, 112818058113, 1271866555, 0] := by
  rw [show D2M8K2.u6046 = KTree.node D2M8K2.t6054 (nat_lit 12852465) (nat_lit 1502131574) (nat_lit 0) D2M8K2.t6055 from rfl, totK_node, tot6054, tot6055]
  decide +kernel

theorem arows6049 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6049 = true := by
  rw [show D2M8K2.u6049 = KTree.node D2M8K2.t6056 (nat_lit 12854428) (nat_lit 3875180351) (nat_lit 0) D2M8K2.t6057 from rfl, allE_node, rows6056, irow6049, rows6057]
  all_goals rfl

theorem atot6049 : totK PD2M8K2 D2M8K2.u6049 = [0, 168710648655, 580771662484, 707985688737, 325743139127, 19889085672, 0, 0] := by
  rw [show D2M8K2.u6049 = KTree.node D2M8K2.t6056 (nat_lit 12854428) (nat_lit 3875180351) (nat_lit 0) D2M8K2.t6057 from rfl, totK_node, tot6056, tot6057]
  decide +kernel

theorem arows6050 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6050 = true := by
  rw [show D2M8K2.u6050 = KTree.node D2M8K2.t6058 (nat_lit 12857718) (nat_lit 3723555697) (nat_lit 0) D2M8K2.t6059 from rfl, allE_node, rows6058, irow6050, rows6059]
  all_goals rfl

theorem atot6050 : totK PD2M8K2 D2M8K2.u6050 = [0, 154865924962, 745330002233, 758036084081, 104613003206, 1209030869, 0, 0] := by
  rw [show D2M8K2.u6050 = KTree.node D2M8K2.t6058 (nat_lit 12857718) (nat_lit 3723555697) (nat_lit 0) D2M8K2.t6059 from rfl, totK_node, tot6058, tot6059]
  decide +kernel

theorem arows6052 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6052 = true := by
  rw [show D2M8K2.u6052 = KTree.node D2M8K2.t6060 (nat_lit 12860516) (nat_lit 2784514369) (nat_lit 0) D2M8K2.t6061 from rfl, allE_node, rows6060, irow6052, rows6061]
  all_goals rfl

theorem atot6052 : totK PD2M8K2 D2M8K2.u6052 = [0, 355351020111, 892429490017, 525253525173, 52338257793, 0, 0, 0] := by
  rw [show D2M8K2.u6052 = KTree.node D2M8K2.t6060 (nat_lit 12860516) (nat_lit 2784514369) (nat_lit 0) D2M8K2.t6061 from rfl, totK_node, tot6060, tot6061]
  decide +kernel

theorem arows6053 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6053 = true := by
  rw [show D2M8K2.u6053 = KTree.node D2M8K2.t6062 (nat_lit 12862032) (nat_lit 2264251722) (nat_lit 0) D2M8K2.t6063 from rfl, allE_node, rows6062, irow6053, rows6063]
  all_goals rfl

theorem atot6053 : totK PD2M8K2 D2M8K2.u6053 = [0, 73213873603, 507309966245, 822742541760, 366655178851, 29391110695, 0, 0] := by
  rw [show D2M8K2.u6053 = KTree.node D2M8K2.t6062 (nat_lit 12862032) (nat_lit 2264251722) (nat_lit 0) D2M8K2.t6063 from rfl, totK_node, tot6062, tot6063]
  decide +kernel

theorem arows6057 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6057 = true := by
  rw [show D2M8K2.u6057 = KTree.node D2M8K2.t6064 (nat_lit 12863317) (nat_lit 1249793116) (nat_lit 0) D2M8K2.t6065 from rfl, allE_node, rows6064, irow6057, rows6065]
  all_goals rfl

theorem atot6057 : totK PD2M8K2 D2M8K2.u6057 = [0, 236456250521, 681427802954, 672354914357, 221478304787, 8100177866, 0, 0] := by
  rw [show D2M8K2.u6057 = KTree.node D2M8K2.t6064 (nat_lit 12863317) (nat_lit 1249793116) (nat_lit 0) D2M8K2.t6065 from rfl, totK_node, tot6064, tot6065]
  decide +kernel

theorem arows6058 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6058 = true := by
  rw [show D2M8K2.u6058 = KTree.node D2M8K2.t6066 (nat_lit 12864824) (nat_lit 2410515402) (nat_lit 0) D2M8K2.t6067 from rfl, allE_node, rows6066, irow6058, rows6067]
  all_goals rfl

theorem atot6058 : totK PD2M8K2 D2M8K2.u6058 = [0, 178977901183, 766037760083, 727828191858, 118439493547, 1164319620, 0, 0] := by
  rw [show D2M8K2.u6058 = KTree.node D2M8K2.t6066 (nat_lit 12864824) (nat_lit 2410515402) (nat_lit 0) D2M8K2.t6067 from rfl, totK_node, tot6066, tot6067]
  decide +kernel

theorem arows6060 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6060 = true := by
  rw [show D2M8K2.u6060 = KTree.node D2M8K2.t6068 (nat_lit 12866706) (nat_lit 3418256644) (nat_lit 0) D2M8K2.t6069 from rfl, allE_node, rows6068, irow6060, rows6069]
  all_goals rfl

theorem atot6060 : totK PD2M8K2 D2M8K2.u6060 = [0, 209831211824, 656346348949, 696955653093, 212194052145, 11885407614, 0, 0] := by
  rw [show D2M8K2.u6060 = KTree.node D2M8K2.t6068 (nat_lit 12866706) (nat_lit 3418256644) (nat_lit 0) D2M8K2.t6069 from rfl, totK_node, tot6068, tot6069]
  decide +kernel

theorem arows6061 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6061 = true := by
  rw [show D2M8K2.u6061 = KTree.node D2M8K2.t6070 (nat_lit 12868346) (nat_lit 3949994482) (nat_lit 0) D2M8K2.t6071 from rfl, allE_node, rows6070, irow6061, rows6071]
  all_goals rfl

theorem atot6061 : totK PD2M8K2 D2M8K2.u6061 = [0, 169694819981, 746145840329, 734571874919, 126775717607, 1198073392, 0, 0] := by
  rw [show D2M8K2.u6061 = KTree.node D2M8K2.t6070 (nat_lit 12868346) (nat_lit 3949994482) (nat_lit 0) D2M8K2.t6071 from rfl, totK_node, tot6070, tot6071]
  decide +kernel

theorem arows6064 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6064 = true := by
  rw [show D2M8K2.u6064 = KTree.node D2M8K2.t6072 (nat_lit 12870252) (nat_lit 3211704481) (nat_lit 0) D2M8K2.t6073 from rfl, allE_node, rows6072, irow6064, rows6073]
  all_goals rfl

theorem atot6064 : totK PD2M8K2 D2M8K2.u6064 = [0, 254793697800, 699885056994, 633215092412, 201154422125, 12052611869, 0, 0] := by
  rw [show D2M8K2.u6064 = KTree.node D2M8K2.t6072 (nat_lit 12870252) (nat_lit 3211704481) (nat_lit 0) D2M8K2.t6073 from rfl, totK_node, tot6072, tot6073]
  decide +kernel

theorem arows6065 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6065 = true := by
  rw [show D2M8K2.u6065 = KTree.node D2M8K2.t6074 (nat_lit 12871413) (nat_lit 1741952189) (nat_lit 0) D2M8K2.t6075 from rfl, allE_node, rows6074, irow6065, rows6075]
  all_goals rfl

theorem atot6065 : totK PD2M8K2 D2M8K2.u6065 = [0, 178274373545, 778510357754, 719437342409, 108452550593, 1096505104, 0, 0] := by
  rw [show D2M8K2.u6065 = KTree.node D2M8K2.t6074 (nat_lit 12871413) (nat_lit 1741952189) (nat_lit 0) D2M8K2.t6075 from rfl, totK_node, tot6074, tot6075]
  decide +kernel

theorem arows6067 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6067 = true := by
  rw [show D2M8K2.u6067 = KTree.node D2M8K2.t6076 (nat_lit 12877154) (nat_lit 3033290174) (nat_lit 0) D2M8K2.t6077 from rfl, allE_node, rows6076, irow6067, rows6077]
  all_goals rfl

theorem atot6067 : totK PD2M8K2 D2M8K2.u6067 = [0, 0, 443969360968, 993514232476, 310036666535, 7592502197, 0, 0] := by
  rw [show D2M8K2.u6067 = KTree.node D2M8K2.t6076 (nat_lit 12877154) (nat_lit 3033290174) (nat_lit 0) D2M8K2.t6077 from rfl, totK_node, tot6076, tot6077]
  decide +kernel

theorem arows6068 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6068 = true := by
  rw [show D2M8K2.u6068 = KTree.node D2M8K2.t6078 (nat_lit 12881082) (nat_lit 3434149563) (nat_lit 0) D2M8K2.t6079 from rfl, allE_node, rows6078, irow6068, rows6079]
  all_goals rfl

theorem atot6068 : totK PD2M8K2 D2M8K2.u6068 = [0, 0, 375228018043, 930319071102, 451468048392, 36100701843, 0, 0] := by
  rw [show D2M8K2.u6068 = KTree.node D2M8K2.t6078 (nat_lit 12881082) (nat_lit 3434149563) (nat_lit 0) D2M8K2.t6079 from rfl, totK_node, tot6078, tot6079]
  decide +kernel

theorem arows6074 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6074 = true := by
  rw [show D2M8K2.u6074 = KTree.node D2M8K2.t6080 (nat_lit 12884088) (nat_lit 3512967442) (nat_lit 0) D2M8K2.t6081 from rfl, allE_node, rows6080, irow6074, rows6081]
  all_goals rfl

theorem atot6074 : totK PD2M8K2 D2M8K2.u6074 = [0, 0, 393305724997, 964362797934, 424236970208, 20408784056, 0, 0] := by
  rw [show D2M8K2.u6074 = KTree.node D2M8K2.t6080 (nat_lit 12884088) (nat_lit 3512967442) (nat_lit 0) D2M8K2.t6081 from rfl, totK_node, tot6080, tot6081]
  decide +kernel

theorem arows6075 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6075 = true := by
  rw [show D2M8K2.u6075 = KTree.node D2M8K2.t6082 (nat_lit 12885683) (nat_lit 2910102465) (nat_lit 0) D2M8K2.t6083 from rfl, allE_node, rows6082, irow6075, rows6083]
  all_goals rfl

theorem atot6075 : totK PD2M8K2 D2M8K2.u6075 = [0, 0, 370718328112, 944995726562, 458420764050, 24734316422, 0, 0] := by
  rw [show D2M8K2.u6075 = KTree.node D2M8K2.t6082 (nat_lit 12885683) (nat_lit 2910102465) (nat_lit 0) D2M8K2.t6083 from rfl, totK_node, tot6082, tot6083]
  decide +kernel

theorem arows6077 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6077 = true := by
  rw [show D2M8K2.u6077 = KTree.node D2M8K2.t6084 (nat_lit 12889087) (nat_lit 2414965113) (nat_lit 0) D2M8K2.t6085 from rfl, allE_node, rows6084, irow6077, rows6085]
  all_goals rfl

theorem atot6077 : totK PD2M8K2 D2M8K2.u6077 = [0, 0, 340157272650, 931397140925, 482621347987, 29586388420, 0, 0] := by
  rw [show D2M8K2.u6077 = KTree.node D2M8K2.t6084 (nat_lit 12889087) (nat_lit 2414965113) (nat_lit 0) D2M8K2.t6085 from rfl, totK_node, tot6084, tot6085]
  decide +kernel

theorem arows6078 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6078 = true := by
  rw [show D2M8K2.u6078 = KTree.node D2M8K2.t6086 (nat_lit 12892050) (nat_lit 3335518455) (nat_lit 0) D2M8K2.t6087 from rfl, allE_node, rows6086, irow6078, rows6087]
  all_goals rfl

theorem atot6078 : totK PD2M8K2 D2M8K2.u6078 = [0, 0, 257663736981, 865259493905, 578780760030, 51948271914, 0, 0] := by
  rw [show D2M8K2.u6078 = KTree.node D2M8K2.t6086 (nat_lit 12892050) (nat_lit 3335518455) (nat_lit 0) D2M8K2.t6087 from rfl, totK_node, tot6086, tot6087]
  decide +kernel

theorem arows6081 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6081 = true := by
  rw [show D2M8K2.u6081 = KTree.node D2M8K2.t6088 (nat_lit 12897897) (nat_lit 1850577461) (nat_lit 0) D2M8K2.t6089 from rfl, allE_node, rows6088, irow6081, rows6089]
  all_goals rfl

theorem atot6081 : totK PD2M8K2 D2M8K2.u6081 = [0, 238037611883, 583081464210, 463611288473, 398477863906, 100601394923, 1429815836, 0] := by
  rw [show D2M8K2.u6081 = KTree.node D2M8K2.t6088 (nat_lit 12897897) (nat_lit 1850577461) (nat_lit 0) D2M8K2.t6089 from rfl, totK_node, tot6088, tot6089]
  decide +kernel

theorem arows6082 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6082 = true := by
  rw [show D2M8K2.u6082 = KTree.node D2M8K2.t6090 (nat_lit 12900101) (nat_lit 2342956359) (nat_lit 0) D2M8K2.t6091 from rfl, allE_node, rows6090, irow6082, rows6091]
  all_goals rfl

theorem atot6082 : totK PD2M8K2 D2M8K2.u6082 = [0, 182397228279, 726333417632, 780773625447, 129780955958, 1369150432, 0, 0] := by
  rw [show D2M8K2.u6082 = KTree.node D2M8K2.t6090 (nat_lit 12900101) (nat_lit 2342956359) (nat_lit 0) D2M8K2.t6091 from rfl, totK_node, tot6090, tot6091]
  decide +kernel

theorem arows6084 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6084 = true := by
  rw [show D2M8K2.u6084 = KTree.node D2M8K2.t6092 (nat_lit 12902248) (nat_lit 3176186931) (nat_lit 0) D2M8K2.t6093 from rfl, allE_node, rows6092, irow6084, rows6093]
  all_goals rfl

theorem atot6084 : totK PD2M8K2 D2M8K2.u6084 = [0, 335755555786, 910066637760, 527940800909, 43876245917, 0, 0, 0] := by
  rw [show D2M8K2.u6084 = KTree.node D2M8K2.t6092 (nat_lit 12902248) (nat_lit 3176186931) (nat_lit 0) D2M8K2.t6093 from rfl, totK_node, tot6092, tot6093]
  decide +kernel

theorem arows6085 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6085 = true := by
  rw [show D2M8K2.u6085 = KTree.node D2M8K2.t6094 (nat_lit 12903744) (nat_lit 3118522592) (nat_lit 0) D2M8K2.t6095 from rfl, allE_node, rows6094, irow6085, rows6095]
  all_goals rfl

theorem atot6085 : totK PD2M8K2 D2M8K2.u6085 = [0, 0, 389952447583, 933387185819, 441176525743, 30675760985, 0, 0] := by
  rw [show D2M8K2.u6085 = KTree.node D2M8K2.t6094 (nat_lit 12903744) (nat_lit 3118522592) (nat_lit 0) D2M8K2.t6095 from rfl, totK_node, tot6094, tot6095]
  decide +kernel

theorem arows6089 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6089 = true := by
  rw [show D2M8K2.u6089 = KTree.node D2M8K2.t6096 (nat_lit 12905090) (nat_lit 4073527318) (nat_lit 0) D2M8K2.t6097 from rfl, allE_node, rows6096, irow6089, rows6097]
  all_goals rfl

theorem atot6089 : totK PD2M8K2 D2M8K2.u6089 = [0, 306075364234, 792753009123, 574493632714, 145580133079, 6804944647, 0, 0] := by
  rw [show D2M8K2.u6089 = KTree.node D2M8K2.t6096 (nat_lit 12905090) (nat_lit 4073527318) (nat_lit 0) D2M8K2.t6097 from rfl, totK_node, tot6096, tot6097]
  decide +kernel

theorem arows6090 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6090 = true := by
  rw [show D2M8K2.u6090 = KTree.node D2M8K2.t6098 (nat_lit 12906588) (nat_lit 3150177418) (nat_lit 0) D2M8K2.t6099 from rfl, allE_node, rows6098, irow6090, rows6099]
  all_goals rfl

theorem atot6090 : totK PD2M8K2 D2M8K2.u6090 = [0, 107350114340, 651829020143, 820079991380, 212587675660, 7879028762, 0, 0] := by
  rw [show D2M8K2.u6090 = KTree.node D2M8K2.t6098 (nat_lit 12906588) (nat_lit 3150177418) (nat_lit 0) D2M8K2.t6099 from rfl, totK_node, tot6098, tot6099]
  decide +kernel

theorem arows6092 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6092 = true := by
  rw [show D2M8K2.u6092 = KTree.node D2M8K2.t6100 (nat_lit 12908560) (nat_lit 2715634847) (nat_lit 0) D2M8K2.t6101 from rfl, allE_node, rows6100, irow6092, rows6101]
  all_goals rfl

theorem atot6092 : totK PD2M8K2 D2M8K2.u6092 = [0, 296727828244, 809565654652, 606767238851, 103391391058, 1189515370, 0, 0] := by
  rw [show D2M8K2.u6092 = KTree.node D2M8K2.t6100 (nat_lit 12908560) (nat_lit 2715634847) (nat_lit 0) D2M8K2.t6101 from rfl, totK_node, tot6100, tot6101]
  decide +kernel

theorem arows6093 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6093 = true := by
  rw [show D2M8K2.u6093 = KTree.node D2M8K2.t6102 (nat_lit 12910221) (nat_lit 1460315211) (nat_lit 0) D2M8K2.t6103 from rfl, allE_node, rows6102, irow6093, rows6103]
  all_goals rfl

theorem atot6093 : totK PD2M8K2 D2M8K2.u6093 = [0, 88845658477, 592178789959, 850276290246, 250126119626, 9179787334, 0, 0] := by
  rw [show D2M8K2.u6093 = KTree.node D2M8K2.t6102 (nat_lit 12910221) (nat_lit 1460315211) (nat_lit 0) D2M8K2.t6103 from rfl, totK_node, tot6102, tot6103]
  decide +kernel

theorem arows6096 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6096 = true := by
  rw [show D2M8K2.u6096 = KTree.node D2M8K2.t6104 (nat_lit 12915552) (nat_lit 2650681600) (nat_lit 0) D2M8K2.t6105 from rfl, allE_node, rows6104, irow6096, rows6105]
  all_goals rfl

theorem atot6096 : totK PD2M8K2 D2M8K2.u6096 = [0, 346993355241, 896183268557, 532523396065, 58185414019, 0, 0, 0] := by
  rw [show D2M8K2.u6096 = KTree.node D2M8K2.t6104 (nat_lit 12915552) (nat_lit 2650681600) (nat_lit 0) D2M8K2.t6105 from rfl, totK_node, tot6104, tot6105]
  decide +kernel

theorem arows6097 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6097 = true := by
  rw [show D2M8K2.u6097 = KTree.node D2M8K2.t6106 (nat_lit 12916994) (nat_lit 3215490373) (nat_lit 0) D2M8K2.t6107 from rfl, allE_node, rows6106, irow6097, rows6107]
  all_goals rfl

theorem atot6097 : totK PD2M8K2 D2M8K2.u6097 = [0, 93768764846, 622921243284, 863724661340, 218276818640, 4909780899, 0, 0] := by
  rw [show D2M8K2.u6097 = KTree.node D2M8K2.t6106 (nat_lit 12916994) (nat_lit 3215490373) (nat_lit 0) D2M8K2.t6107 from rfl, totK_node, tot6106, tot6107]
  decide +kernel

theorem arows6099 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6099 = true := by
  rw [show D2M8K2.u6099 = KTree.node D2M8K2.t6108 (nat_lit 12918642) (nat_lit 2556228943) (nat_lit 0) D2M8K2.t6109 from rfl, allE_node, rows6108, irow6099, rows6109]
  all_goals rfl

theorem atot6099 : totK PD2M8K2 D2M8K2.u6099 = [0, 0, 467699502568, 966012917648, 339955795669, 18411378955, 0, 0] := by
  rw [show D2M8K2.u6099 = KTree.node D2M8K2.t6108 (nat_lit 12918642) (nat_lit 2556228943) (nat_lit 0) D2M8K2.t6109 from rfl, totK_node, tot6108, tot6109]
  decide +kernel

theorem arows6100 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6100 = true := by
  rw [show D2M8K2.u6100 = KTree.node D2M8K2.t6110 (nat_lit 12922874) (nat_lit 4242684642) (nat_lit 0) D2M8K2.t6111 from rfl, allE_node, rows6110, irow6100, rows6111]
  all_goals rfl

theorem atot6100 : totK PD2M8K2 D2M8K2.u6100 = [0, 0, 378409046240, 925808459782, 472343546583, 33581013520, 0, 0] := by
  rw [show D2M8K2.u6100 = KTree.node D2M8K2.t6110 (nat_lit 12922874) (nat_lit 4242684642) (nat_lit 0) D2M8K2.t6111 from rfl, totK_node, tot6110, tot6111]
  decide +kernel

theorem arows6105 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6105 = true := by
  rw [show D2M8K2.u6105 = KTree.node D2M8K2.t6112 (nat_lit 12925930) (nat_lit 3919268871) (nat_lit 0) D2M8K2.t6113 from rfl, allE_node, rows6112, irow6105, rows6113]
  all_goals rfl

theorem atot6105 : totK PD2M8K2 D2M8K2.u6105 = [0, 0, 346308795515, 900149435051, 516857905397, 39825347874, 0, 0] := by
  rw [show D2M8K2.u6105 = KTree.node D2M8K2.t6112 (nat_lit 12925930) (nat_lit 3919268871) (nat_lit 0) D2M8K2.t6113 from rfl, totK_node, tot6112, tot6113]
  decide +kernel

theorem arows6106 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6106 = true := by
  rw [show D2M8K2.u6106 = KTree.node D2M8K2.t6114 (nat_lit 12927794) (nat_lit 4023605475) (nat_lit 0) D2M8K2.t6115 from rfl, allE_node, rows6114, irow6106, rows6115]
  all_goals rfl

theorem atot6106 : totK PD2M8K2 D2M8K2.u6106 = [0, 0, 143883808435, 756133763394, 770219198013, 110160168806, 1323630408, 0] := by
  rw [show D2M8K2.u6106 = KTree.node D2M8K2.t6114 (nat_lit 12927794) (nat_lit 4023605475) (nat_lit 0) D2M8K2.t6115 from rfl, totK_node, tot6114, tot6115]
  decide +kernel

theorem arows6108 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6108 = true := by
  rw [show D2M8K2.u6108 = KTree.node D2M8K2.t6116 (nat_lit 12930020) (nat_lit 3189369783) (nat_lit 0) D2M8K2.t6117 from rfl, allE_node, rows6116, irow6108, rows6117]
  all_goals rfl

theorem atot6108 : totK PD2M8K2 D2M8K2.u6108 = [0, 0, 318265506761, 891394885682, 560082129036, 43018291298, 0, 0] := by
  rw [show D2M8K2.u6108 = KTree.node D2M8K2.t6116 (nat_lit 12930020) (nat_lit 3189369783) (nat_lit 0) D2M8K2.t6117 from rfl, totK_node, tot6116, tot6117]
  decide +kernel

theorem arows6109 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6109 = true := by
  rw [show D2M8K2.u6109 = KTree.node D2M8K2.t6118 (nat_lit 12935819) (nat_lit 2928354468) (nat_lit 0) D2M8K2.t6119 from rfl, allE_node, rows6118, irow6109, rows6119]
  all_goals rfl

theorem atot6109 : totK PD2M8K2 D2M8K2.u6109 = [0, 0, 204155180000, 762172104438, 713179478555, 114231450471, 1332468113, 0] := by
  rw [show D2M8K2.u6109 = KTree.node D2M8K2.t6118 (nat_lit 12935819) (nat_lit 2928354468) (nat_lit 0) D2M8K2.t6119 from rfl, totK_node, tot6118, tot6119]
  decide +kernel

theorem arows6112 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6112 = true := by
  rw [show D2M8K2.u6112 = KTree.node D2M8K2.t6120 (nat_lit 12937318) (nat_lit 3849526529) (nat_lit 0) D2M8K2.t6121 from rfl, allE_node, rows6120, irow6112, rows6121]
  all_goals rfl

theorem atot6112 : totK PD2M8K2 D2M8K2.u6112 = [0, 0, 228609488483, 846330755229, 660629282310, 56033926087, 0, 0] := by
  rw [show D2M8K2.u6112 = KTree.node D2M8K2.t6120 (nat_lit 12937318) (nat_lit 3849526529) (nat_lit 0) D2M8K2.t6121 from rfl, totK_node, tot6120, tot6121]
  decide +kernel

theorem arows6113 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6113 = true := by
  rw [show D2M8K2.u6113 = KTree.node D2M8K2.t6122 (nat_lit 12939192) (nat_lit 3229931674) (nat_lit 0) D2M8K2.t6123 from rfl, allE_node, rows6122, irow6113, rows6123]
  all_goals rfl

theorem atot6113 : totK PD2M8K2 D2M8K2.u6113 = [179984371288, 439406052484, 187861159738, 199138855016, 532023854202, 219566865795, 9533751846, 0] := by
  rw [show D2M8K2.u6113 = KTree.node D2M8K2.t6122 (nat_lit 12939192) (nat_lit 3229931674) (nat_lit 0) D2M8K2.t6123 from rfl, totK_node, tot6122, tot6123]
  decide +kernel

theorem arows6115 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6115 = true := by
  rw [show D2M8K2.u6115 = KTree.node D2M8K2.t6124 (nat_lit 12940726) (nat_lit 3576224356) (nat_lit 0) D2M8K2.t6125 from rfl, allE_node, rows6124, irow6115, rows6125]
  all_goals rfl

theorem atot6115 : totK PD2M8K2 D2M8K2.u6115 = [255500798512, 796802711906, 631551943550, 106793210766, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u6115 = KTree.node D2M8K2.t6124 (nat_lit 12940726) (nat_lit 3576224356) (nat_lit 0) D2M8K2.t6125 from rfl, totK_node, tot6124, tot6125]
  decide +kernel

theorem arows6116 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6116 = true := by
  rw [show D2M8K2.u6116 = KTree.node D2M8K2.t6126 (nat_lit 12946234) (nat_lit 3899492587) (nat_lit 0) D2M8K2.t6127 from rfl, allE_node, rows6126, irow6116, rows6127]
  all_goals rfl

theorem atot6116 : totK PD2M8K2 D2M8K2.u6116 = [230552562293, 806137668071, 711814649365, 83893263193, 0, 0, 0, 0] := by
  rw [show D2M8K2.u6116 = KTree.node D2M8K2.t6126 (nat_lit 12946234) (nat_lit 3899492587) (nat_lit 0) D2M8K2.t6127 from rfl, totK_node, tot6126, tot6127]
  decide +kernel

theorem arows6120 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6120 = true := by
  rw [show D2M8K2.u6120 = KTree.node D2M8K2.t6128 (nat_lit 12947743) (nat_lit 2132800945) (nat_lit 0) D2M8K2.t6129 from rfl, allE_node, rows6128, irow6120, rows6129]
  all_goals rfl

theorem atot6120 : totK PD2M8K2 D2M8K2.u6120 = [195588761349, 776583374549, 714283671777, 113557692880, 1164319620, 0, 0, 0] := by
  rw [show D2M8K2.u6120 = KTree.node D2M8K2.t6128 (nat_lit 12947743) (nat_lit 2132800945) (nat_lit 0) D2M8K2.t6129 from rfl, totK_node, tot6128, tot6129]
  decide +kernel

theorem arows6121 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6121 = true := by
  rw [show D2M8K2.u6121 = KTree.node D2M8K2.t6130 (nat_lit 12949416) (nat_lit 3346331192) (nat_lit 0) D2M8K2.t6131 from rfl, allE_node, rows6130, irow6121, rows6131]
  all_goals rfl

theorem atot6121 : totK PD2M8K2 D2M8K2.u6121 = [179985095148, 657886012866, 713053820073, 210710092262, 11885407614, 0, 0, 0] := by
  rw [show D2M8K2.u6121 = KTree.node D2M8K2.t6130 (nat_lit 12949416) (nat_lit 3346331192) (nat_lit 0) D2M8K2.t6131 from rfl, totK_node, tot6130, tot6131]
  decide +kernel

theorem arows6123 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6123 = true := by
  rw [show D2M8K2.u6123 = KTree.node D2M8K2.t6132 (nat_lit 12951450) (nat_lit 3869875884) (nat_lit 0) D2M8K2.t6133 from rfl, allE_node, rows6132, irow6123, rows6133]
  all_goals rfl

theorem atot6123 : totK PD2M8K2 D2M8K2.u6123 = [138985563802, 625740679886, 762199406070, 211305533212, 10680993762, 0, 0, 0] := by
  rw [show D2M8K2.u6123 = KTree.node D2M8K2.t6132 (nat_lit 12951450) (nat_lit 3869875884) (nat_lit 0) D2M8K2.t6133 from rfl, totK_node, tot6132, tot6133]
  decide +kernel

theorem arows6124 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6124 = true := by
  rw [show D2M8K2.u6124 = KTree.node D2M8K2.t6134 (nat_lit 12953481) (nat_lit 1905615121) (nat_lit 0) D2M8K2.t6135 from rfl, allE_node, rows6134, irow6124, rows6135]
  all_goals rfl

theorem atot6124 : totK PD2M8K2 D2M8K2.u6124 = [317699861224, 836346917592, 540967867024, 89640318040, 2569691499, 0, 0, 0] := by
  rw [show D2M8K2.u6124 = KTree.node D2M8K2.t6134 (nat_lit 12953481) (nat_lit 1905615121) (nat_lit 0) D2M8K2.t6135 from rfl, totK_node, tot6134, tot6135]
  decide +kernel

theorem arows6127 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6127 = true := by
  rw [show D2M8K2.u6127 = KTree.node D2M8K2.t6136 (nat_lit 12955059) (nat_lit 1216179916) (nat_lit 0) D2M8K2.t6137 from rfl, allE_node, rows6136, irow6127, rows6137]
  all_goals rfl

theorem atot6127 : totK PD2M8K2 D2M8K2.u6127 = [90838862230, 691224106864, 861311279316, 139560530341, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u6127 = KTree.node D2M8K2.t6136 (nat_lit 12955059) (nat_lit 1216179916) (nat_lit 0) D2M8K2.t6137 from rfl, totK_node, tot6136, tot6137]
  decide +kernel

theorem arows6128 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6128 = true := by
  rw [show D2M8K2.u6128 = KTree.node D2M8K2.t6138 (nat_lit 12957060) (nat_lit 1384003741) (nat_lit 0) D2M8K2.t6139 from rfl, allE_node, rows6138, irow6128, rows6139]
  all_goals rfl

theorem atot6128 : totK PD2M8K2 D2M8K2.u6128 = [321395357186, 825307930212, 537002868798, 107365573043, 3884009855, 0, 0, 0] := by
  rw [show D2M8K2.u6128 = KTree.node D2M8K2.t6138 (nat_lit 12957060) (nat_lit 1384003741) (nat_lit 0) D2M8K2.t6139 from rfl, totK_node, tot6138, tot6139]
  decide +kernel

theorem arows6130 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6130 = true := by
  rw [show D2M8K2.u6130 = KTree.node D2M8K2.t6140 (nat_lit 12958603) (nat_lit 1691634041) (nat_lit 0) D2M8K2.t6141 from rfl, allE_node, rows6140, irow6130, rows6141]
  all_goals rfl

theorem atot6130 : totK PD2M8K2 D2M8K2.u6130 = [88521112267, 556280449584, 856653122904, 268845760490, 8710740030, 0, 0, 0] := by
  rw [show D2M8K2.u6130 = KTree.node D2M8K2.t6140 (nat_lit 12958603) (nat_lit 1691634041) (nat_lit 0) D2M8K2.t6141 from rfl, totK_node, tot6140, tot6141]
  decide +kernel

theorem arows6131 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6131 = true := by
  rw [show D2M8K2.u6131 = KTree.node D2M8K2.t6142 (nat_lit 12960267) (nat_lit 1920708392) (nat_lit 0) D2M8K2.t6143 from rfl, allE_node, rows6142, irow6131, rows6143]
  all_goals rfl

theorem atot6131 : totK PD2M8K2 D2M8K2.u6131 = [0, 370011126937, 923708911129, 442467477884, 31340853708, 0, 0, 0] := by
  rw [show D2M8K2.u6131 = KTree.node D2M8K2.t6142 (nat_lit 12960267) (nat_lit 1920708392) (nat_lit 0) D2M8K2.t6143 from rfl, totK_node, tot6142, tot6143]
  decide +kernel

theorem arows6142 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6142 = true := by
  rw [show D2M8K2.u6142 = KTree.node D2M8K2.t6144 (nat_lit 12961784) (nat_lit 3546176706) (nat_lit 0) D2M8K2.t6145 from rfl, allE_node, rows6144, irow6142, rows6145]
  all_goals rfl

theorem atot6142 : totK PD2M8K2 D2M8K2.u6142 = [0, 155505132346, 741555624316, 710190795877, 125156980604, 1369150432, 0, 0] := by
  rw [show D2M8K2.u6142 = KTree.node D2M8K2.t6144 (nat_lit 12961784) (nat_lit 3546176706) (nat_lit 0) D2M8K2.t6145 from rfl, totK_node, tot6144, tot6145]
  decide +kernel

theorem arows6143 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6143 = true := by
  rw [show D2M8K2.u6143 = KTree.node D2M8K2.t6146 (nat_lit 12967375) (nat_lit 1672656188) (nat_lit 0) D2M8K2.t6147 from rfl, allE_node, rows6146, irow6143, rows6147]
  all_goals rfl

theorem atot6143 : totK PD2M8K2 D2M8K2.u6143 = [0, 337978365881, 912918353242, 497945332542, 36325109382, 0, 0, 0] := by
  rw [show D2M8K2.u6143 = KTree.node D2M8K2.t6146 (nat_lit 12967375) (nat_lit 1672656188) (nat_lit 0) D2M8K2.t6147 from rfl, totK_node, tot6146, tot6147]
  decide +kernel

theorem arows6145 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6145 = true := by
  rw [show D2M8K2.u6145 = KTree.node D2M8K2.t6148 (nat_lit 12970634) (nat_lit 3111280422) (nat_lit 0) D2M8K2.t6149 from rfl, allE_node, rows6148, irow6145, rows6149]
  all_goals rfl

theorem atot6145 : totK PD2M8K2 D2M8K2.u6145 = [0, 372045550605, 933943428929, 438618906609, 25205379176, 0, 0, 0] := by
  rw [show D2M8K2.u6145 = KTree.node D2M8K2.t6148 (nat_lit 12970634) (nat_lit 3111280422) (nat_lit 0) D2M8K2.t6149 from rfl, totK_node, tot6148, tot6149]
  decide +kernel

theorem arows6146 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6146 = true := by
  rw [show D2M8K2.u6146 = KTree.node D2M8K2.t6150 (nat_lit 12974285) (nat_lit 1986981516) (nat_lit 0) D2M8K2.t6151 from rfl, allE_node, rows6150, irow6146, rows6151]
  all_goals rfl

theorem atot6146 : totK PD2M8K2 D2M8K2.u6146 = [0, 353027580994, 935725356191, 451224569840, 25901910195, 0, 0, 0] := by
  rw [show D2M8K2.u6146 = KTree.node D2M8K2.t6150 (nat_lit 12974285) (nat_lit 1986981516) (nat_lit 0) D2M8K2.t6151 from rfl, totK_node, tot6150, tot6151]
  decide +kernel

theorem arows6149 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6149 = true := by
  rw [show D2M8K2.u6149 = KTree.node D2M8K2.t6152 (nat_lit 12977608) (nat_lit 3801566964) (nat_lit 0) D2M8K2.t6153 from rfl, allE_node, rows6152, irow6149, rows6153]
  all_goals rfl

theorem atot6149 : totK PD2M8K2 D2M8K2.u6149 = [0, 392828089848, 956709285992, 428573216442, 18568109915, 0, 0, 0] := by
  rw [show D2M8K2.u6149 = KTree.node D2M8K2.t6152 (nat_lit 12977608) (nat_lit 3801566964) (nat_lit 0) D2M8K2.t6153 from rfl, totK_node, tot6152, tot6153]
  decide +kernel

theorem arows6150 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6150 = true := by
  rw [show D2M8K2.u6150 = KTree.node D2M8K2.t6154 (nat_lit 12984596) (nat_lit 3676162564) (nat_lit 0) D2M8K2.t6155 from rfl, allE_node, rows6154, irow6150, rows6155]
  all_goals rfl

theorem atot6150 : totK PD2M8K2 D2M8K2.u6150 = [249139256659, 670095762447, 653553045044, 250372737774, 17433533548, 0, 0, 0] := by
  rw [show D2M8K2.u6150 = KTree.node D2M8K2.t6154 (nat_lit 12984596) (nat_lit 3676162564) (nat_lit 0) D2M8K2.t6155 from rfl, totK_node, tot6154, tot6155]
  decide +kernel

theorem arows6152 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6152 = true := by
  rw [show D2M8K2.u6152 = KTree.node D2M8K2.t6156 (nat_lit 12985774) (nat_lit 4054937007) (nat_lit 0) D2M8K2.t6157 from rfl, allE_node, rows6156, irow6152, rows6157]
  all_goals rfl

theorem atot6152 : totK PD2M8K2 D2M8K2.u6152 = [194946287859, 743206798083, 668178786763, 205939248312, 21400436502, 0, 0, 0] := by
  rw [show D2M8K2.u6152 = KTree.node D2M8K2.t6156 (nat_lit 12985774) (nat_lit 4054937007) (nat_lit 0) D2M8K2.t6157 from rfl, totK_node, tot6156, tot6157]
  decide +kernel

theorem arows6153 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6153 = true := by
  rw [show D2M8K2.u6153 = KTree.node D2M8K2.t6158 (nat_lit 12987245) (nat_lit 1972982894) (nat_lit 0) D2M8K2.t6159 from rfl, allE_node, rows6158, irow6153, rows6159]
  all_goals rfl

theorem atot6153 : totK PD2M8K2 D2M8K2.u6153 = [90988959560, 469368577221, 848479794461, 376137861534, 16208961603, 0, 0, 0] := by
  rw [show D2M8K2.u6153 = KTree.node D2M8K2.t6158 (nat_lit 12987245) (nat_lit 1972982894) (nat_lit 0) D2M8K2.t6159 from rfl, totK_node, tot6158, tot6159]
  decide +kernel

theorem arows6157 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6157 = true := by
  rw [show D2M8K2.u6157 = KTree.node D2M8K2.t6160 (nat_lit 12988495) (nat_lit 1527189603) (nat_lit 0) D2M8K2.t6161 from rfl, allE_node, rows6160, irow6157, rows6161]
  all_goals rfl

theorem atot6157 : totK PD2M8K2 D2M8K2.u6157 = [336392390403, 916876237781, 534045722472, 47679301628, 0, 0, 0, 0] := by
  rw [show D2M8K2.u6157 = KTree.node D2M8K2.t6160 (nat_lit 12988495) (nat_lit 1527189603) (nat_lit 0) D2M8K2.t6161 from rfl, totK_node, tot6160, tot6161]
  decide +kernel

theorem arows6158 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6158 = true := by
  rw [show D2M8K2.u6158 = KTree.node D2M8K2.t6162 (nat_lit 12990166) (nat_lit 2930599450) (nat_lit 0) D2M8K2.t6163 from rfl, allE_node, rows6162, irow6158, rows6163]
  all_goals rfl

theorem atot6158 : totK PD2M8K2 D2M8K2.u6158 = [71386502340, 520320450073, 907140166591, 287687076550, 13036865798, 0, 0, 0] := by
  rw [show D2M8K2.u6158 = KTree.node D2M8K2.t6162 (nat_lit 12990166) (nat_lit 2930599450) (nat_lit 0) D2M8K2.t6163 from rfl, totK_node, tot6162, tot6163]
  decide +kernel

theorem arows6160 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6160 = true := by
  rw [show D2M8K2.u6160 = KTree.node D2M8K2.t6164 (nat_lit 12992407) (nat_lit 2008743810) (nat_lit 0) D2M8K2.t6165 from rfl, allE_node, rows6164, irow6160, rows6165]
  all_goals rfl

theorem atot6160 : totK PD2M8K2 D2M8K2.u6160 = [257410283940, 851127508881, 650535633119, 82336175722, 0, 0, 0, 0] := by
  rw [show D2M8K2.u6160 = KTree.node D2M8K2.t6164 (nat_lit 12992407) (nat_lit 2008743810) (nat_lit 0) D2M8K2.t6165 from rfl, totK_node, tot6164, tot6165]
  decide +kernel

theorem arows6161 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6161 = true := by
  rw [show D2M8K2.u6161 = KTree.node D2M8K2.t6166 (nat_lit 12994415) (nat_lit 2777443937) (nat_lit 0) D2M8K2.t6167 from rfl, allE_node, rows6166, irow6161, rows6167]
  all_goals rfl

theorem atot6161 : totK PD2M8K2 D2M8K2.u6161 = [194479703291, 664005351025, 725497703047, 199604922234, 10698315783, 0, 0, 0] := by
  rw [show D2M8K2.u6161 = KTree.node D2M8K2.t6166 (nat_lit 12994415) (nat_lit 2777443937) (nat_lit 0) D2M8K2.t6167 from rfl, totK_node, tot6166, tot6167]
  decide +kernel

theorem arows6164 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6164 = true := by
  rw [show D2M8K2.u6164 = KTree.node D2M8K2.t6168 (nat_lit 12995793) (nat_lit 1864980272) (nat_lit 0) D2M8K2.t6169 from rfl, allE_node, rows6168, irow6164, rows6169]
  all_goals rfl

theorem atot6164 : totK PD2M8K2 D2M8K2.u6164 = [217094497630, 794356059860, 679405095999, 104340330542, 1096156699, 0, 0, 0] := by
  rw [show D2M8K2.u6164 = KTree.node D2M8K2.t6168 (nat_lit 12995793) (nat_lit 1864980272) (nat_lit 0) D2M8K2.t6169 from rfl, totK_node, tot6168, tot6169]
  decide +kernel

theorem arows6165 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6165 = true := by
  rw [show D2M8K2.u6165 = KTree.node D2M8K2.t6170 (nat_lit 12998140) (nat_lit 3823129323) (nat_lit 0) D2M8K2.t6171 from rfl, allE_node, rows6170, irow6165, rows6171]
  all_goals rfl

theorem atot6165 : totK PD2M8K2 D2M8K2.u6165 = [245633557057, 757602581616, 683566682250, 139032393244, 3880716147, 0, 0, 0] := by
  rw [show D2M8K2.u6165 = KTree.node D2M8K2.t6170 (nat_lit 12998140) (nat_lit 3823129323) (nat_lit 0) D2M8K2.t6171 from rfl, totK_node, tot6170, tot6171]
  decide +kernel

theorem arows6167 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6167 = true := by
  rw [show D2M8K2.u6167 = KTree.node D2M8K2.t6172 (nat_lit 12999634) (nat_lit 4072409954) (nat_lit 0) D2M8K2.t6173 from rfl, allE_node, rows6172, irow6167, rows6173]
  all_goals rfl

theorem atot6167 : totK PD2M8K2 D2M8K2.u6167 = [171412815235, 746104099431, 757714759845, 135097262531, 1267860612, 0, 0, 0] := by
  rw [show D2M8K2.u6167 = KTree.node D2M8K2.t6172 (nat_lit 12999634) (nat_lit 4072409954) (nat_lit 0) D2M8K2.t6173 from rfl, totK_node, tot6172, tot6173]
  decide +kernel

theorem arows6168 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6168 = true := by
  rw [show D2M8K2.u6168 = KTree.node D2M8K2.t6174 (nat_lit 13001359) (nat_lit 1543099432) (nat_lit 0) D2M8K2.t6175 from rfl, allE_node, rows6174, irow6168, rows6175]
  all_goals rfl

theorem atot6168 : totK PD2M8K2 D2M8K2.u6168 = [0, 368759376265, 919078081956, 475611142960, 42673147919, 0, 0, 0] := by
  rw [show D2M8K2.u6168 = KTree.node D2M8K2.t6174 (nat_lit 13001359) (nat_lit 1543099432) (nat_lit 0) D2M8K2.t6175 from rfl, totK_node, tot6174, tot6175]
  decide +kernel

theorem arows6173 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6173 = true := by
  rw [show D2M8K2.u6173 = KTree.node D2M8K2.t6176 (nat_lit 13006259) (nat_lit 2076161299) (nat_lit 0) D2M8K2.t6177 from rfl, allE_node, rows6176, irow6173, rows6177]
  all_goals rfl

theorem atot6173 : totK PD2M8K2 D2M8K2.u6173 = [0, 260254811420, 846901135530, 622949784689, 93886020724, 10444649207, 0, 0] := by
  rw [show D2M8K2.u6173 = KTree.node D2M8K2.t6176 (nat_lit 13006259) (nat_lit 2076161299) (nat_lit 0) D2M8K2.t6177 from rfl, totK_node, tot6176, tot6177]
  decide +kernel

theorem arows6174 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6174 = true := by
  rw [show D2M8K2.u6174 = KTree.node D2M8K2.t6178 (nat_lit 13007764) (nat_lit 2585043764) (nat_lit 0) D2M8K2.t6179 from rfl, allE_node, rows6178, irow6174, rows6179]
  all_goals rfl

theorem atot6174 : totK PD2M8K2 D2M8K2.u6174 = [0, 17755325808, 358512203367, 909719298570, 458554789114, 26477224647, 0, 0] := by
  rw [show D2M8K2.u6174 = KTree.node D2M8K2.t6178 (nat_lit 13007764) (nat_lit 2585043764) (nat_lit 0) D2M8K2.t6179 from rfl, totK_node, tot6178, tot6179]
  decide +kernel

theorem arows6176 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6176 = true := by
  rw [show D2M8K2.u6176 = KTree.node D2M8K2.t6180 (nat_lit 13009020) (nat_lit 3202190753) (nat_lit 0) D2M8K2.t6181 from rfl, allE_node, rows6180, irow6176, rows6181]
  all_goals rfl

theorem atot6176 : totK PD2M8K2 D2M8K2.u6176 = [0, 384631596859, 938149851545, 463407403492, 35410415551, 0, 0, 0] := by
  rw [show D2M8K2.u6176 = KTree.node D2M8K2.t6180 (nat_lit 13009020) (nat_lit 3202190753) (nat_lit 0) D2M8K2.t6181 from rfl, totK_node, tot6180, tot6181]
  decide +kernel

theorem arows6177 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6177 = true := by
  rw [show D2M8K2.u6177 = KTree.node D2M8K2.t6182 (nat_lit 13010814) (nat_lit 2879182551) (nat_lit 0) D2M8K2.t6183 from rfl, allE_node, rows6182, irow6177, rows6183]
  all_goals rfl

theorem atot6177 : totK PD2M8K2 D2M8K2.u6177 = [0, 61012437378, 610139558032, 916919055673, 209391960194, 5159868635, 0, 0] := by
  rw [show D2M8K2.u6177 = KTree.node D2M8K2.t6182 (nat_lit 13010814) (nat_lit 2879182551) (nat_lit 0) D2M8K2.t6183 from rfl, totK_node, tot6182, tot6183]
  decide +kernel

theorem arows6180 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6180 = true := by
  rw [show D2M8K2.u6180 = KTree.node D2M8K2.t6184 (nat_lit 13013077) (nat_lit 1035602074) (nat_lit 0) D2M8K2.t6185 from rfl, allE_node, rows6184, irow6180, rows6185]
  all_goals rfl

theorem atot6180 : totK PD2M8K2 D2M8K2.u6180 = [0, 282011364221, 872613278592, 607579876673, 65673151005, 0, 0, 0] := by
  rw [show D2M8K2.u6180 = KTree.node D2M8K2.t6184 (nat_lit 13013077) (nat_lit 1035602074) (nat_lit 0) D2M8K2.t6185 from rfl, totK_node, tot6184, tot6185]
  decide +kernel

theorem arows6181 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6181 = true := by
  rw [show D2M8K2.u6181 = KTree.node D2M8K2.t6186 (nat_lit 13015132) (nat_lit 3584837655) (nat_lit 0) D2M8K2.t6187 from rfl, allE_node, rows6186, irow6181, rows6187]
  all_goals rfl

theorem atot6181 : totK PD2M8K2 D2M8K2.u6181 = [0, 186432467177, 663587243105, 738772133320, 193617781753, 5218872685, 0, 0] := by
  rw [show D2M8K2.u6181 = KTree.node D2M8K2.t6186 (nat_lit 13015132) (nat_lit 3584837655) (nat_lit 0) D2M8K2.t6187 from rfl, totK_node, tot6186, tot6187]
  decide +kernel

theorem arows6183 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6183 = true := by
  rw [show D2M8K2.u6183 = KTree.node D2M8K2.t6188 (nat_lit 13016509) (nat_lit 1143919344) (nat_lit 0) D2M8K2.t6189 from rfl, allE_node, rows6188, irow6183, rows6189]
  all_goals rfl

theorem atot6183 : totK PD2M8K2 D2M8K2.u6183 = [0, 224163414399, 844339447946, 668133456668, 63637628167, 0, 0, 0] := by
  rw [show D2M8K2.u6183 = KTree.node D2M8K2.t6188 (nat_lit 13016509) (nat_lit 1143919344) (nat_lit 0) D2M8K2.t6189 from rfl, totK_node, tot6188, tot6189]
  decide +kernel

theorem arows6184 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6184 = true := by
  rw [show D2M8K2.u6184 = KTree.node D2M8K2.t6190 (nat_lit 13018969) (nat_lit 1428963233) (nat_lit 0) D2M8K2.t6191 from rfl, allE_node, rows6190, irow6184, rows6191]
  all_goals rfl

theorem atot6184 : totK PD2M8K2 D2M8K2.u6184 = [0, 244805794822, 777007680045, 677780723232, 121961033576, 1415142070, 0, 0] := by
  rw [show D2M8K2.u6184 = KTree.node D2M8K2.t6190 (nat_lit 13018969) (nat_lit 1428963233) (nat_lit 0) D2M8K2.t6191 from rfl, totK_node, tot6190, tot6191]
  decide +kernel

theorem arows6188 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6188 = true := by
  rw [show D2M8K2.u6188 = KTree.node D2M8K2.t6192 (nat_lit 13020466) (nat_lit 4176030581) (nat_lit 0) D2M8K2.t6193 from rfl, allE_node, rows6192, irow6188, rows6193]
  all_goals rfl

theorem atot6188 : totK PD2M8K2 D2M8K2.u6188 = [0, 171151945050, 756878694183, 745809301318, 130516883858, 1238673482, 0, 0] := by
  rw [show D2M8K2.u6188 = KTree.node D2M8K2.t6192 (nat_lit 13020466) (nat_lit 4176030581) (nat_lit 0) D2M8K2.t6193 from rfl, totK_node, tot6192, tot6193]
  decide +kernel

theorem arows6189 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6189 = true := by
  rw [show D2M8K2.u6189 = KTree.node D2M8K2.t6194 (nat_lit 13022351) (nat_lit 2775174655) (nat_lit 0) D2M8K2.t6195 from rfl, allE_node, rows6194, irow6189, rows6195]
  all_goals rfl

theorem atot6189 : totK PD2M8K2 D2M8K2.u6189 = [245216813082, 605960493846, 393061519670, 362791608474, 160280825261, 8063697217, 0, 0] := by
  rw [show D2M8K2.u6189 = KTree.node D2M8K2.t6194 (nat_lit 13022351) (nat_lit 2775174655) (nat_lit 0) D2M8K2.t6195 from rfl, totK_node, tot6194, tot6195]
  decide +kernel

theorem arows6191 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6191 = true := by
  rw [show D2M8K2.u6191 = KTree.node D2M8K2.t6196 (nat_lit 13023930) (nat_lit 3342038162) (nat_lit 0) D2M8K2.t6197 from rfl, allE_node, rows6196, irow6191, rows6197]
  all_goals rfl

theorem atot6191 : totK PD2M8K2 D2M8K2.u6191 = [171565361099, 731212685732, 762466071971, 126071168370, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u6191 = KTree.node D2M8K2.t6196 (nat_lit 13023930) (nat_lit 3342038162) (nat_lit 0) D2M8K2.t6197 from rfl, totK_node, tot6196, tot6197]
  decide +kernel

theorem arows6192 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6192 = true := by
  rw [show D2M8K2.u6192 = KTree.node D2M8K2.t6198 (nat_lit 13026245) (nat_lit 2343468112) (nat_lit 0) D2M8K2.t6199 from rfl, allE_node, rows6198, irow6192, rows6199]
  all_goals rfl

theorem atot6192 : totK PD2M8K2 D2M8K2.u6192 = [303160673940, 862429057107, 611884699395, 67105334521, 0, 0, 0, 0] := by
  rw [show D2M8K2.u6192 = KTree.node D2M8K2.t6198 (nat_lit 13026245) (nat_lit 2343468112) (nat_lit 0) D2M8K2.t6199 from rfl, totK_node, tot6198, tot6199]
  decide +kernel

theorem arows6195 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6195 = true := by
  rw [show D2M8K2.u6195 = KTree.node D2M8K2.t6200 (nat_lit 13027780) (nat_lit 3772544887) (nat_lit 0) D2M8K2.t6201 from rfl, allE_node, rows6200, irow6195, rows6201]
  all_goals rfl

theorem atot6195 : totK PD2M8K2 D2M8K2.u6195 = [123250812643, 610608671411, 765780495646, 296741027646, 25354272529, 0, 0, 0] := by
  rw [show D2M8K2.u6195 = KTree.node D2M8K2.t6200 (nat_lit 13027780) (nat_lit 3772544887) (nat_lit 0) D2M8K2.t6201 from rfl, totK_node, tot6200, tot6201]
  decide +kernel

theorem arows6196 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6196 = true := by
  rw [show D2M8K2.u6196 = KTree.node D2M8K2.t6202 (nat_lit 13029040) (nat_lit 3372978867) (nat_lit 0) D2M8K2.t6203 from rfl, allE_node, rows6202, irow6196, rows6203]
  all_goals rfl

theorem atot6196 : totK PD2M8K2 D2M8K2.u6196 = [176559373540, 612094424598, 728106203737, 286188326949, 11993935419, 0, 0, 0] := by
  rw [show D2M8K2.u6196 = KTree.node D2M8K2.t6202 (nat_lit 13029040) (nat_lit 3372978867) (nat_lit 0) D2M8K2.t6203 from rfl, totK_node, tot6202, tot6203]
  decide +kernel

theorem arows6198 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6198 = true := by
  rw [show D2M8K2.u6198 = KTree.node D2M8K2.t6204 (nat_lit 13030514) (nat_lit 4002422937) (nat_lit 0) D2M8K2.t6205 from rfl, allE_node, rows6204, irow6198, rows6205]
  all_goals rfl

theorem atot6198 : totK PD2M8K2 D2M8K2.u6198 = [270019299043, 821349690554, 635872970264, 92531796508, 1164319620, 0, 0, 0] := by
  rw [show D2M8K2.u6198 = KTree.node D2M8K2.t6204 (nat_lit 13030514) (nat_lit 4002422937) (nat_lit 0) D2M8K2.t6205 from rfl, totK_node, tot6204, tot6205]
  decide +kernel

theorem arows6199 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6199 = true := by
  rw [show D2M8K2.u6199 = KTree.node D2M8K2.t6206 (nat_lit 13032152) (nat_lit 3515630132) (nat_lit 0) D2M8K2.t6207 from rfl, allE_node, rows6206, irow6199, rows6207]
  all_goals rfl

theorem atot6199 : totK PD2M8K2 D2M8K2.u6199 = [135752362032, 618320696510, 803099392043, 229872690266, 11885407614, 0, 0, 0] := by
  rw [show D2M8K2.u6199 = KTree.node D2M8K2.t6206 (nat_lit 13032152) (nat_lit 3515630132) (nat_lit 0) D2M8K2.t6207 from rfl, totK_node, tot6206, tot6207]
  decide +kernel

theorem arows6205 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6205 = true := by
  rw [show D2M8K2.u6205 = KTree.node D2M8K2.t6208 (nat_lit 13036971) (nat_lit 3570451771) (nat_lit 0) D2M8K2.t6209 from rfl, allE_node, rows6208, irow6205, rows6209]
  all_goals rfl

theorem atot6205 : totK PD2M8K2 D2M8K2.u6205 = [283731852506, 871836459014, 590732867774, 57751856038, 0, 0, 0, 0] := by
  rw [show D2M8K2.u6205 = KTree.node D2M8K2.t6208 (nat_lit 13036971) (nat_lit 3570451771) (nat_lit 0) D2M8K2.t6209 from rfl, totK_node, tot6208, tot6209]
  decide +kernel

theorem arows6206 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6206 = true := by
  rw [show D2M8K2.u6206 = KTree.node D2M8K2.t6210 (nat_lit 13038965) (nat_lit 2378546130) (nat_lit 0) D2M8K2.t6211 from rfl, allE_node, rows6210, irow6206, rows6211]
  all_goals rfl

theorem atot6206 : totK PD2M8K2 D2M8K2.u6206 = [165576442519, 663870919815, 779274669709, 187646193059, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u6206 = KTree.node D2M8K2.t6210 (nat_lit 13038965) (nat_lit 2378546130) (nat_lit 0) D2M8K2.t6211 from rfl, totK_node, tot6210, tot6211]
  decide +kernel

theorem arows6208 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6208 = true := by
  rw [show D2M8K2.u6208 = KTree.node D2M8K2.t6212 (nat_lit 13040495) (nat_lit 2770046035) (nat_lit 0) D2M8K2.t6213 from rfl, allE_node, rows6212, irow6208, rows6213]
  all_goals rfl

theorem atot6208 : totK PD2M8K2 D2M8K2.u6208 = [258174440891, 839072798298, 642890387768, 86962118169, 1268739303, 0, 0, 0] := by
  rw [show D2M8K2.u6208 = KTree.node D2M8K2.t6212 (nat_lit 13040495) (nat_lit 2770046035) (nat_lit 0) D2M8K2.t6213 from rfl, totK_node, tot6212, tot6213]
  decide +kernel

theorem arows6209 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6209 = true := by
  rw [show D2M8K2.u6209 = KTree.node D2M8K2.t6214 (nat_lit 13042202) (nat_lit 4010773020) (nat_lit 0) D2M8K2.t6215 from rfl, allE_node, rows6214, irow6209, rows6215]
  all_goals rfl

theorem atot6209 : totK PD2M8K2 D2M8K2.u6209 = [0, 426999017095, 961350570104, 371938559458, 20592896308, 0, 0, 0] := by
  rw [show D2M8K2.u6209 = KTree.node D2M8K2.t6214 (nat_lit 13042202) (nat_lit 4010773020) (nat_lit 0) D2M8K2.t6215 from rfl, totK_node, tot6214, tot6215]
  decide +kernel

theorem arows6212 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6212 = true := by
  rw [show D2M8K2.u6212 = KTree.node D2M8K2.t6216 (nat_lit 13044096) (nat_lit 3716921436) (nat_lit 0) D2M8K2.t6217 from rfl, allE_node, rows6216, irow6212, rows6217]
  all_goals rfl

theorem atot6212 : totK PD2M8K2 D2M8K2.u6212 = [0, 324293588081, 937346006897, 477445265010, 25074884806, 0, 0, 0] := by
  rw [show D2M8K2.u6212 = KTree.node D2M8K2.t6216 (nat_lit 13044096) (nat_lit 3716921436) (nat_lit 0) D2M8K2.t6217 from rfl, totK_node, tot6216, tot6217]
  decide +kernel

theorem arows6213 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6213 = true := by
  rw [show D2M8K2.u6213 = KTree.node D2M8K2.t6218 (nat_lit 13045934) (nat_lit 3000080541) (nat_lit 0) D2M8K2.t6219 from rfl, allE_node, rows6218, irow6213, rows6219]
  all_goals rfl

theorem atot6213 : totK PD2M8K2 D2M8K2.u6213 = [0, 163898307800, 721690509220, 768295748179, 117032666572, 1206465782, 0, 0] := by
  rw [show D2M8K2.u6213 = KTree.node D2M8K2.t6218 (nat_lit 13045934) (nat_lit 3000080541) (nat_lit 0) D2M8K2.t6219 from rfl, totK_node, tot6218, tot6219]
  decide +kernel

theorem arows6215 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6215 = true := by
  rw [show D2M8K2.u6215 = KTree.node D2M8K2.t6220 (nat_lit 13047778) (nat_lit 2559668946) (nat_lit 0) D2M8K2.t6221 from rfl, allE_node, rows6220, irow6215, rows6221]
  all_goals rfl

theorem atot6215 : totK PD2M8K2 D2M8K2.u6215 = [0, 348164248006, 956949606539, 470896705317, 26818837947, 0, 0, 0] := by
  rw [show D2M8K2.u6215 = KTree.node D2M8K2.t6220 (nat_lit 13047778) (nat_lit 2559668946) (nat_lit 0) D2M8K2.t6221 from rfl, totK_node, tot6220, tot6221]
  decide +kernel

theorem arows6216 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6216 = true := by
  rw [show D2M8K2.u6216 = KTree.node D2M8K2.t6222 (nat_lit 13050702) (nat_lit 3056675856) (nat_lit 0) D2M8K2.t6223 from rfl, allE_node, rows6222, irow6216, rows6223]
  all_goals rfl

theorem atot6216 : totK PD2M8K2 D2M8K2.u6216 = [0, 353826952146, 930815689186, 507558785522, 37193159217, 0, 0, 0] := by
  rw [show D2M8K2.u6216 = KTree.node D2M8K2.t6222 (nat_lit 13050702) (nat_lit 3056675856) (nat_lit 0) D2M8K2.t6223 from rfl, totK_node, tot6222, tot6223]
  decide +kernel

theorem arows6220 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6220 = true := by
  rw [show D2M8K2.u6220 = KTree.node D2M8K2.t6224 (nat_lit 13052373) (nat_lit 1456041422) (nat_lit 0) D2M8K2.t6225 from rfl, allE_node, rows6224, irow6220, rows6225]
  all_goals rfl

theorem atot6220 : totK PD2M8K2 D2M8K2.u6220 = [0, 83524231449, 527455234047, 835991292092, 269863881096, 13016197374, 0, 0] := by
  rw [show D2M8K2.u6220 = KTree.node D2M8K2.t6224 (nat_lit 13052373) (nat_lit 1456041422) (nat_lit 0) D2M8K2.t6225 from rfl, totK_node, tot6224, tot6225]
  decide +kernel

theorem arows6221 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6221 = true := by
  rw [show D2M8K2.u6221 = KTree.node D2M8K2.t6226 (nat_lit 13057516) (nat_lit 3916293635) (nat_lit 0) D2M8K2.t6227 from rfl, allE_node, rows6226, irow6221, rows6227]
  all_goals rfl

theorem atot6221 : totK PD2M8K2 D2M8K2.u6221 = [0, 333610101413, 948044151391, 483023169936, 27019206085, 0, 0, 0] := by
  rw [show D2M8K2.u6221 = KTree.node D2M8K2.t6226 (nat_lit 13057516) (nat_lit 3916293635) (nat_lit 0) D2M8K2.t6227 from rfl, totK_node, tot6226, tot6227]
  decide +kernel

theorem arows6223 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6223 = true := by
  rw [show D2M8K2.u6223 = KTree.node D2M8K2.t6228 (nat_lit 13059477) (nat_lit 1615064355) (nat_lit 0) D2M8K2.t6229 from rfl, allE_node, rows6228, irow6223, rows6229]
  all_goals rfl

theorem atot6223 : totK PD2M8K2 D2M8K2.u6223 = [0, 124671354637, 669540637811, 768092656270, 150020283298, 4574395652, 0, 0] := by
  rw [show D2M8K2.u6223 = KTree.node D2M8K2.t6228 (nat_lit 13059477) (nat_lit 1615064355) (nat_lit 0) D2M8K2.t6229 from rfl, totK_node, tot6228, tot6229]
  decide +kernel

theorem arows6224 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6224 = true := by
  rw [show D2M8K2.u6224 = KTree.node D2M8K2.t6230 (nat_lit 13061163) (nat_lit 3550788635) (nat_lit 0) D2M8K2.t6231 from rfl, allE_node, rows6230, irow6224, rows6231]
  all_goals rfl

theorem atot6224 : totK PD2M8K2 D2M8K2.u6224 = [76372199855, 410142655812, 818076365732, 476184105642, 42747167010, 0, 0, 0] := by
  rw [show D2M8K2.u6224 = KTree.node D2M8K2.t6230 (nat_lit 13061163) (nat_lit 3550788635) (nat_lit 0) D2M8K2.t6231 from rfl, totK_node, tot6230, tot6231]
  decide +kernel

theorem arows6227 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6227 = true := by
  rw [show D2M8K2.u6227 = KTree.node D2M8K2.t6232 (nat_lit 13106182) (nat_lit 2387481192) (nat_lit 0) D2M8K2.t6233 from rfl, allE_node, rows6232, irow6227, rows6233]
  all_goals rfl

theorem atot6227 : totK PD2M8K2 D2M8K2.u6227 = [327548174582, 921510662201, 490609741722, 28777556891, 0, 0, 0, 0] := by
  rw [show D2M8K2.u6227 = KTree.node D2M8K2.t6232 (nat_lit 13106182) (nat_lit 2387481192) (nat_lit 0) D2M8K2.t6233 from rfl, totK_node, tot6232, tot6233]
  decide +kernel

theorem arows6228 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6228 = true := by
  rw [show D2M8K2.u6228 = KTree.node D2M8K2.t6234 (nat_lit 13108048) (nat_lit 3297802379) (nat_lit 0) D2M8K2.t6235 from rfl, allE_node, rows6234, irow6228, rows6235]
  all_goals rfl

theorem atot6228 : totK PD2M8K2 D2M8K2.u6228 = [103813599404, 645538471441, 885929878552, 166921314067, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u6228 = KTree.node D2M8K2.t6234 (nat_lit 13108048) (nat_lit 3297802379) (nat_lit 0) D2M8K2.t6235 from rfl, totK_node, tot6234, tot6235]
  decide +kernel

theorem arows6230 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6230 = true := by
  rw [show D2M8K2.u6230 = KTree.node D2M8K2.t6236 (nat_lit 13109804) (nat_lit 3786797412) (nat_lit 0) D2M8K2.t6237 from rfl, allE_node, rows6236, irow6230, rows6237]
  all_goals rfl

theorem atot6230 : totK PD2M8K2 D2M8K2.u6230 = [313650562615, 906178691261, 553455343003, 52970827080, 0, 0, 0, 0] := by
  rw [show D2M8K2.u6230 = KTree.node D2M8K2.t6236 (nat_lit 13109804) (nat_lit 3786797412) (nat_lit 0) D2M8K2.t6237 from rfl, totK_node, tot6236, tot6237]
  decide +kernel

theorem arows6231 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6231 = true := by
  rw [show D2M8K2.u6231 = KTree.node D2M8K2.t6238 (nat_lit 13111325) (nat_lit 1258945021) (nat_lit 0) D2M8K2.t6239 from rfl, allE_node, rows6238, irow6231, rows6239]
  all_goals rfl

theorem atot6231 : totK PD2M8K2 D2M8K2.u6231 = [0, 339510321331, 930019837472, 498933376301, 33004026400, 0, 0, 0] := by
  rw [show D2M8K2.u6231 = KTree.node D2M8K2.t6238 (nat_lit 13111325) (nat_lit 1258945021) (nat_lit 0) D2M8K2.t6239 from rfl, totK_node, tot6238, tot6239]
  decide +kernel

theorem arows6236 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6236 = true := by
  rw [show D2M8K2.u6236 = KTree.node D2M8K2.t6240 (nat_lit 13112633) (nat_lit 1188955712) (nat_lit 0) D2M8K2.t6241 from rfl, allE_node, rows6240, irow6236, rows6241]
  all_goals rfl

theorem atot6236 : totK PD2M8K2 D2M8K2.u6236 = [366613064440, 911738697751, 478629720062, 57899672410, 4412989545, 0, 0, 0] := by
  rw [show D2M8K2.u6236 = KTree.node D2M8K2.t6240 (nat_lit 13112633) (nat_lit 1188955712) (nat_lit 0) D2M8K2.t6241 from rfl, totK_node, tot6240, tot6241]
  decide +kernel

theorem arows6237 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6237 = true := by
  rw [show D2M8K2.u6237 = KTree.node D2M8K2.t6242 (nat_lit 13114190) (nat_lit 3856126188) (nat_lit 0) D2M8K2.t6243 from rfl, allE_node, rows6242, irow6237, rows6243]
  all_goals rfl

theorem atot6237 : totK PD2M8K2 D2M8K2.u6237 = [55817160339, 529357459031, 899751817869, 279370111663, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u6237 = KTree.node D2M8K2.t6242 (nat_lit 13114190) (nat_lit 3856126188) (nat_lit 0) D2M8K2.t6243 from rfl, totK_node, tot6242, tot6243]
  decide +kernel

theorem arows6239 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6239 = true := by
  rw [show D2M8K2.u6239 = KTree.node D2M8K2.t6244 (nat_lit 13116021) (nat_lit 1120392392) (nat_lit 0) D2M8K2.t6245 from rfl, allE_node, rows6244, irow6239, rows6245]
  all_goals rfl

theorem atot6239 : totK PD2M8K2 D2M8K2.u6239 = [323621509918, 895596405290, 538528982968, 54320193779, 0, 0, 0, 0] := by
  rw [show D2M8K2.u6239 = KTree.node D2M8K2.t6244 (nat_lit 13116021) (nat_lit 1120392392) (nat_lit 0) D2M8K2.t6245 from rfl, totK_node, tot6244, tot6245]
  decide +kernel

theorem arows6240 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6240 = true := by
  rw [show D2M8K2.u6240 = KTree.node D2M8K2.t6246 (nat_lit 13118335) (nat_lit 2428988519) (nat_lit 0) D2M8K2.t6247 from rfl, allE_node, rows6246, irow6240, rows6247]
  all_goals rfl

theorem atot6240 : totK PD2M8K2 D2M8K2.u6240 = [105481780695, 554446934462, 815231003499, 264941888703, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u6240 = KTree.node D2M8K2.t6246 (nat_lit 13118335) (nat_lit 2428988519) (nat_lit 0) D2M8K2.t6247 from rfl, totK_node, tot6246, tot6247]
  decide +kernel

theorem arows6243 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6243 = true := by
  rw [show D2M8K2.u6243 = KTree.node D2M8K2.t6248 (nat_lit 13119847) (nat_lit 2386208983) (nat_lit 0) D2M8K2.t6249 from rfl, allE_node, rows6248, irow6243, rows6249]
  all_goals rfl

theorem atot6243 : totK PD2M8K2 D2M8K2.u6243 = [332401058255, 920390633744, 529993069859, 44128004536, 0, 0, 0, 0] := by
  rw [show D2M8K2.u6243 = KTree.node D2M8K2.t6248 (nat_lit 13119847) (nat_lit 2386208983) (nat_lit 0) D2M8K2.t6249 from rfl, totK_node, tot6248, tot6249]
  decide +kernel

theorem arows6244 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6244 = true := by
  rw [show D2M8K2.u6244 = KTree.node D2M8K2.t6250 (nat_lit 13121660) (nat_lit 3386485054) (nat_lit 0) D2M8K2.t6251 from rfl, allE_node, rows6250, irow6244, rows6251]
  all_goals rfl

theorem atot6244 : totK PD2M8K2 D2M8K2.u6244 = [0, 486270491187, 1017755133094, 283114801058, 6350335412, 0, 0, 0] := by
  rw [show D2M8K2.u6244 = KTree.node D2M8K2.t6250 (nat_lit 13121660) (nat_lit 3386485054) (nat_lit 0) D2M8K2.t6251 from rfl, totK_node, tot6250, tot6251]
  decide +kernel

theorem arows6246 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6246 = true := by
  rw [show D2M8K2.u6246 = KTree.node D2M8K2.t6252 (nat_lit 13127073) (nat_lit 1848497439) (nat_lit 0) D2M8K2.t6253 from rfl, allE_node, rows6252, irow6246, rows6253]
  all_goals rfl

theorem atot6246 : totK PD2M8K2 D2M8K2.u6246 = [0, 315137680011, 881645953940, 500029645262, 38388034498, 0, 0, 0] := by
  rw [show D2M8K2.u6246 = KTree.node D2M8K2.t6252 (nat_lit 13127073) (nat_lit 1848497439) (nat_lit 0) D2M8K2.t6253 from rfl, totK_node, tot6252, tot6253]
  decide +kernel

theorem arows6247 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6247 = true := by
  rw [show D2M8K2.u6247 = KTree.node D2M8K2.t6254 (nat_lit 13129681) (nat_lit 1143032352) (nat_lit 0) D2M8K2.t6255 from rfl, allE_node, rows6254, irow6247, rows6255]
  all_goals rfl

theorem atot6247 : totK PD2M8K2 D2M8K2.u6247 = [0, 194367653213, 783316157808, 695346544166, 98476982628, 1138244013, 0, 0] := by
  rw [show D2M8K2.u6247 = KTree.node D2M8K2.t6254 (nat_lit 13129681) (nat_lit 1143032352) (nat_lit 0) D2M8K2.t6255 from rfl, totK_node, tot6254, tot6255]
  decide +kernel

theorem arows6251 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6251 = true := by
  rw [show D2M8K2.u6251 = KTree.node D2M8K2.t6256 (nat_lit 13130906) (nat_lit 4100404273) (nat_lit 0) D2M8K2.t6257 from rfl, allE_node, rows6256, irow6251, rows6257]
  all_goals rfl

theorem atot6251 : totK PD2M8K2 D2M8K2.u6251 = [0, 391188911909, 968813752994, 425069885204, 23575860083, 0, 0, 0] := by
  rw [show D2M8K2.u6251 = KTree.node D2M8K2.t6256 (nat_lit 13130906) (nat_lit 4100404273) (nat_lit 0) D2M8K2.t6257 from rfl, totK_node, tot6256, tot6257]
  decide +kernel

theorem arows6252 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6252 = true := by
  rw [show D2M8K2.u6252 = KTree.node D2M8K2.t6258 (nat_lit 13134144) (nat_lit 3390458902) (nat_lit 0) D2M8K2.t6259 from rfl, allE_node, rows6258, irow6252, rows6259]
  all_goals rfl

theorem atot6252 : totK PD2M8K2 D2M8K2.u6252 = [0, 365472005356, 940218451285, 461154410470, 21673227479, 0, 0, 0] := by
  rw [show D2M8K2.u6252 = KTree.node D2M8K2.t6258 (nat_lit 13134144) (nat_lit 3390458902) (nat_lit 0) D2M8K2.t6259 from rfl, totK_node, tot6258, tot6259]
  decide +kernel

theorem arows6254 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6254 = true := by
  rw [show D2M8K2.u6254 = KTree.node D2M8K2.t6260 (nat_lit 13137500) (nat_lit 3411801000) (nat_lit 0) D2M8K2.t6261 from rfl, allE_node, rows6260, irow6254, rows6261]
  all_goals rfl

theorem atot6254 : totK PD2M8K2 D2M8K2.u6254 = [0, 382523454197, 955867663879, 439510130894, 28056241111, 0, 0, 0] := by
  rw [show D2M8K2.u6254 = KTree.node D2M8K2.t6260 (nat_lit 13137500) (nat_lit 3411801000) (nat_lit 0) D2M8K2.t6261 from rfl, totK_node, tot6260, tot6261]
  decide +kernel

theorem arows6255 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6255 = true := by
  rw [show D2M8K2.u6255 = KTree.node D2M8K2.t6262 (nat_lit 13140751) (nat_lit 2342581261) (nat_lit 0) D2M8K2.t6263 from rfl, allE_node, rows6262, irow6255, rows6263]
  all_goals rfl

theorem atot6255 : totK PD2M8K2 D2M8K2.u6255 = [0, 262150932452, 814518910438, 590746496024, 81983223516, 1095107716, 0, 0] := by
  rw [show D2M8K2.u6255 = KTree.node D2M8K2.t6262 (nat_lit 13140751) (nat_lit 2342581261) (nat_lit 0) D2M8K2.t6263 from rfl, totK_node, tot6262, tot6263]
  decide +kernel

theorem arows6258 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6258 = true := by
  rw [show D2M8K2.u6258 = KTree.node D2M8K2.t6264 (nat_lit 13142736) (nat_lit 3577703716) (nat_lit 0) D2M8K2.t6265 from rfl, allE_node, rows6264, irow6258, rows6265]
  all_goals rfl

theorem atot6258 : totK PD2M8K2 D2M8K2.u6258 = [176394742691, 411681522430, 488047687326, 565335230940, 135089230013, 3882006667, 0, 0] := by
  rw [show D2M8K2.u6258 = KTree.node D2M8K2.t6264 (nat_lit 13142736) (nat_lit 3577703716) (nat_lit 0) D2M8K2.t6265 from rfl, totK_node, tot6264, tot6265]
  decide +kernel

theorem arows6259 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6259 = true := by
  rw [show D2M8K2.u6259 = KTree.node D2M8K2.t6266 (nat_lit 13148099) (nat_lit 2899885882) (nat_lit 0) D2M8K2.t6267 from rfl, allE_node, rows6266, irow6259, rows6267]
  all_goals rfl

theorem atot6259 : totK PD2M8K2 D2M8K2.u6259 = [231220643389, 770056960871, 658049675481, 112223485434, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u6259 = KTree.node D2M8K2.t6266 (nat_lit 13148099) (nat_lit 2899885882) (nat_lit 0) D2M8K2.t6267 from rfl, totK_node, tot6266, tot6267]
  decide +kernel

theorem arows6261 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6261 = true := by
  rw [show D2M8K2.u6261 = KTree.node D2M8K2.t6268 (nat_lit 13150459) (nat_lit 2224944626) (nat_lit 0) D2M8K2.t6269 from rfl, allE_node, rows6268, irow6261, rows6269]
  all_goals rfl

theorem atot6261 : totK PD2M8K2 D2M8K2.u6261 = [224024702766, 783876799783, 724284692360, 90651206806, 0, 0, 0, 0] := by
  rw [show D2M8K2.u6261 = KTree.node D2M8K2.t6268 (nat_lit 13150459) (nat_lit 2224944626) (nat_lit 0) D2M8K2.t6269 from rfl, totK_node, tot6268, tot6269]
  decide +kernel

theorem arows6262 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6262 = true := by
  rw [show D2M8K2.u6262 = KTree.node D2M8K2.t6270 (nat_lit 13151693) (nat_lit 2178443597) (nat_lit 0) D2M8K2.t6271 from rfl, allE_node, rows6270, irow6262, rows6271]
  all_goals rfl

theorem atot6262 : totK PD2M8K2 D2M8K2.u6262 = [191110652258, 740352637709, 672305517008, 206739499817, 21380039407, 0, 0, 0] := by
  rw [show D2M8K2.u6262 = KTree.node D2M8K2.t6270 (nat_lit 13151693) (nat_lit 2178443597) (nat_lit 0) D2M8K2.t6271 from rfl, totK_node, tot6270, tot6271]
  decide +kernel

theorem arows6269 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6269 = true := by
  rw [show D2M8K2.u6269 = KTree.node D2M8K2.t6272 (nat_lit 13153261) (nat_lit 1282098406) (nat_lit 0) D2M8K2.t6273 from rfl, allE_node, rows6272, irow6269, rows6273]
  all_goals rfl

theorem atot6269 : totK PD2M8K2 D2M8K2.u6269 = [123222801663, 515093411725, 791593797299, 357957550819, 16023640966, 0, 0, 0] := by
  rw [show D2M8K2.u6269 = KTree.node D2M8K2.t6272 (nat_lit 13153261) (nat_lit 1282098406) (nat_lit 0) D2M8K2.t6273 from rfl, totK_node, tot6272, tot6273]
  decide +kernel

theorem arows6270 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6270 = true := by
  rw [show D2M8K2.u6270 = KTree.node D2M8K2.t6274 (nat_lit 13154723) (nat_lit 2240432852) (nat_lit 0) D2M8K2.t6275 from rfl, allE_node, rows6274, irow6270, rows6275]
  all_goals rfl

theorem atot6270 : totK PD2M8K2 D2M8K2.u6270 = [299675086221, 883090118698, 584377612196, 56297662723, 0, 0, 0, 0] := by
  rw [show D2M8K2.u6270 = KTree.node D2M8K2.t6274 (nat_lit 13154723) (nat_lit 2240432852) (nat_lit 0) D2M8K2.t6275 from rfl, totK_node, tot6274, tot6275]
  decide +kernel

theorem arows6272 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6272 = true := by
  rw [show D2M8K2.u6272 = KTree.node D2M8K2.t6276 (nat_lit 13156424) (nat_lit 3636545356) (nat_lit 0) D2M8K2.t6277 from rfl, allE_node, rows6276, irow6272, rows6277]
  all_goals rfl

theorem atot6272 : totK PD2M8K2 D2M8K2.u6272 = [79947513563, 539112964285, 869368688436, 279227198004, 13043783340, 0, 0, 0] := by
  rw [show D2M8K2.u6272 = KTree.node D2M8K2.t6276 (nat_lit 13156424) (nat_lit 3636545356) (nat_lit 0) D2M8K2.t6277 from rfl, totK_node, tot6276, tot6277]
  decide +kernel

theorem arows6273 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6273 = true := by
  rw [show D2M8K2.u6273 = KTree.node D2M8K2.t6278 (nat_lit 13158454) (nat_lit 3561620279) (nat_lit 0) D2M8K2.t6279 from rfl, allE_node, rows6278, irow6273, rows6279]
  all_goals rfl

theorem atot6273 : totK PD2M8K2 D2M8K2.u6273 = [246742681837, 791876652114, 670916883479, 114962585452, 1198073392, 0, 0, 0] := by
  rw [show D2M8K2.u6273 = KTree.node D2M8K2.t6278 (nat_lit 13158454) (nat_lit 3561620279) (nat_lit 0) D2M8K2.t6279 from rfl, totK_node, tot6278, tot6279]
  decide +kernel

theorem arows6276 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6276 = true := by
  rw [show D2M8K2.u6276 = KTree.node D2M8K2.t6280 (nat_lit 13164029) (nat_lit 2282866798) (nat_lit 0) D2M8K2.t6281 from rfl, allE_node, rows6280, irow6276, rows6281]
  all_goals rfl

theorem atot6276 : totK PD2M8K2 D2M8K2.u6276 = [264592406772, 769902222929, 656251554829, 145276230490, 5945454258, 0, 0, 0] := by
  rw [show D2M8K2.u6276 = KTree.node D2M8K2.t6280 (nat_lit 13164029) (nat_lit 2282866798) (nat_lit 0) D2M8K2.t6281 from rfl, totK_node, tot6280, tot6281]
  decide +kernel

theorem arows6277 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6277 = true := by
  rw [show D2M8K2.u6277 = KTree.node D2M8K2.t6282 (nat_lit 13165498) (nat_lit 3946002751) (nat_lit 0) D2M8K2.t6283 from rfl, allE_node, rows6282, irow6277, rows6283]
  all_goals rfl

theorem atot6277 : totK PD2M8K2 D2M8K2.u6277 = [177251648093, 764550772092, 746093972043, 125723087181, 1268739303, 0, 0, 0] := by
  rw [show D2M8K2.u6277 = KTree.node D2M8K2.t6282 (nat_lit 13165498) (nat_lit 3946002751) (nat_lit 0) D2M8K2.t6283 from rfl, totK_node, tot6282, tot6283]
  decide +kernel

theorem arows6279 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6279 = true := by
  rw [show D2M8K2.u6279 = KTree.node D2M8K2.t6284 (nat_lit 13167157) (nat_lit 1205019937) (nat_lit 0) D2M8K2.t6285 from rfl, allE_node, rows6284, irow6279, rows6285]
  all_goals rfl

theorem atot6279 : totK PD2M8K2 D2M8K2.u6279 = [0, 396343514708, 956929047349, 404699072168, 22149860293, 0, 0, 0] := by
  rw [show D2M8K2.u6279 = KTree.node D2M8K2.t6284 (nat_lit 13167157) (nat_lit 1205019937) (nat_lit 0) D2M8K2.t6285 from rfl, totK_node, tot6284, tot6285]
  decide +kernel

theorem arows6280 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6280 = true := by
  rw [show D2M8K2.u6280 = KTree.node D2M8K2.t6286 (nat_lit 13168801) (nat_lit 1562614071) (nat_lit 0) D2M8K2.t6287 from rfl, allE_node, rows6286, irow6280, rows6287]
  all_goals rfl

theorem atot6280 : totK PD2M8K2 D2M8K2.u6280 = [0, 234735244437, 810202340361, 618591597879, 86144668473, 1310285577, 0, 0] := by
  rw [show D2M8K2.u6280 = KTree.node D2M8K2.t6286 (nat_lit 13168801) (nat_lit 1562614071) (nat_lit 0) D2M8K2.t6287 from rfl, totK_node, tot6286, tot6287]
  decide +kernel

theorem arows6284 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6284 = true := by
  rw [show D2M8K2.u6284 = KTree.node D2M8K2.t6288 (nat_lit 13171184) (nat_lit 3529192246) (nat_lit 0) D2M8K2.t6289 from rfl, allE_node, rows6288, irow6284, rows6289]
  all_goals rfl

theorem atot6284 : totK PD2M8K2 D2M8K2.u6284 = [0, 212156417142, 793061070753, 732739465367, 73404557488, 0, 0, 0] := by
  rw [show D2M8K2.u6284 = KTree.node D2M8K2.t6288 (nat_lit 13171184) (nat_lit 3529192246) (nat_lit 0) D2M8K2.t6289 from rfl, totK_node, tot6288, tot6289]
  decide +kernel

theorem arows6285 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6285 = true := by
  rw [show D2M8K2.u6285 = KTree.node D2M8K2.t6290 (nat_lit 13172426) (nat_lit 4222864817) (nat_lit 0) D2M8K2.t6291 from rfl, allE_node, rows6290, irow6285, rows6291]
  all_goals rfl

theorem atot6285 : totK PD2M8K2 D2M8K2.u6285 = [0, 374150414781, 957577419889, 462319645077, 32314654690, 0, 0, 0] := by
  rw [show D2M8K2.u6285 = KTree.node D2M8K2.t6290 (nat_lit 13172426) (nat_lit 4222864817) (nat_lit 0) D2M8K2.t6291 from rfl, totK_node, tot6290, tot6291]
  decide +kernel

theorem arows6287 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6287 = true := by
  rw [show D2M8K2.u6287 = KTree.node D2M8K2.t6292 (nat_lit 13175669) (nat_lit 2215540700) (nat_lit 0) D2M8K2.t6293 from rfl, allE_node, rows6292, irow6287, rows6293]
  all_goals rfl

theorem atot6287 : totK PD2M8K2 D2M8K2.u6287 = [0, 252452681370, 797064291542, 644002657259, 87836001732, 1075657031, 0, 0] := by
  rw [show D2M8K2.u6287 = KTree.node D2M8K2.t6292 (nat_lit 13175669) (nat_lit 2215540700) (nat_lit 0) D2M8K2.t6293 from rfl, totK_node, tot6292, tot6293]
  decide +kernel

theorem arows6288 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6288 = true := by
  rw [show D2M8K2.u6288 = KTree.node D2M8K2.t6294 (nat_lit 13177566) (nat_lit 3734936088) (nat_lit 0) D2M8K2.t6295 from rfl, allE_node, rows6294, irow6288, rows6295]
  all_goals rfl

theorem atot6288 : totK PD2M8K2 D2M8K2.u6288 = [0, 180814173998, 735961276852, 727608846274, 133058778438, 3804183361, 0, 0] := by
  rw [show D2M8K2.u6288 = KTree.node D2M8K2.t6294 (nat_lit 13177566) (nat_lit 3734936088) (nat_lit 0) D2M8K2.t6295 from rfl, totK_node, tot6294, tot6295]
  decide +kernel

theorem arows6291 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6291 = true := by
  rw [show D2M8K2.u6291 = KTree.node D2M8K2.t6296 (nat_lit 13179546) (nat_lit 3847813245) (nat_lit 0) D2M8K2.t6297 from rfl, allE_node, rows6296, irow6291, rows6297]
  all_goals rfl

theorem atot6291 : totK PD2M8K2 D2M8K2.u6291 = [0, 144801674033, 693594072634, 777253457849, 164448138740, 4931404646, 0, 0] := by
  rw [show D2M8K2.u6291 = KTree.node D2M8K2.t6296 (nat_lit 13179546) (nat_lit 3847813245) (nat_lit 0) D2M8K2.t6297 from rfl, totK_node, tot6296, tot6297]
  decide +kernel

theorem arows6292 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6292 = true := by
  rw [show D2M8K2.u6292 = KTree.node D2M8K2.t6298 (nat_lit 13185184) (nat_lit 3100220129) (nat_lit 0) D2M8K2.t6299 from rfl, allE_node, rows6298, irow6292, rows6299]
  all_goals rfl

theorem atot6292 : totK PD2M8K2 D2M8K2.u6292 = [0, 346697172606, 912555484373, 509568973701, 43853470002, 0, 0, 0] := by
  rw [show D2M8K2.u6292 = KTree.node D2M8K2.t6298 (nat_lit 13185184) (nat_lit 3100220129) (nat_lit 0) D2M8K2.t6299 from rfl, totK_node, tot6298, tot6299]
  decide +kernel

theorem arows6294 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6294 = true := by
  rw [show D2M8K2.u6294 = KTree.node D2M8K2.t6300 (nat_lit 13186702) (nat_lit 3920020301) (nat_lit 0) D2M8K2.t6301 from rfl, allE_node, rows6300, irow6294, rows6301]
  all_goals rfl

theorem atot6294 : totK PD2M8K2 D2M8K2.u6294 = [0, 89869257916, 579484239754, 844954144379, 240377452192, 8424427256, 0, 0] := by
  rw [show D2M8K2.u6294 = KTree.node D2M8K2.t6300 (nat_lit 13186702) (nat_lit 3920020301) (nat_lit 0) D2M8K2.t6301 from rfl, totK_node, tot6300, tot6301]
  decide +kernel

theorem arows6295 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6295 = true := by
  rw [show D2M8K2.u6295 = KTree.node D2M8K2.t6302 (nat_lit 13188365) (nat_lit 1836107993) (nat_lit 0) D2M8K2.t6303 from rfl, allE_node, rows6302, irow6295, rows6303]
  all_goals rfl

theorem atot6295 : totK PD2M8K2 D2M8K2.u6295 = [0, 279256940359, 769541175627, 563610072126, 159843759838, 13326740810, 0, 0] := by
  rw [show D2M8K2.u6295 = KTree.node D2M8K2.t6302 (nat_lit 13188365) (nat_lit 1836107993) (nat_lit 0) D2M8K2.t6303 from rfl, totK_node, tot6302, tot6303]
  decide +kernel

theorem arows6300 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6300 = true := by
  rw [show D2M8K2.u6300 = KTree.node D2M8K2.t6304 (nat_lit 13189882) (nat_lit 3869045902) (nat_lit 0) D2M8K2.t6305 from rfl, allE_node, rows6304, irow6300, rows6305]
  all_goals rfl

theorem atot6300 : totK PD2M8K2 D2M8K2.u6300 = [0, 155746706840, 732423837986, 777426460556, 129269699390, 1369150432, 0, 0] := by
  rw [show D2M8K2.u6300 = KTree.node D2M8K2.t6304 (nat_lit 13189882) (nat_lit 3869045902) (nat_lit 0) D2M8K2.t6305 from rfl, totK_node, tot6304, tot6305]
  decide +kernel

theorem arows6301 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6301 = true := by
  rw [show D2M8K2.u6301 = KTree.node D2M8K2.t6306 (nat_lit 13195423) (nat_lit 1573526018) (nat_lit 0) D2M8K2.t6307 from rfl, allE_node, rows6306, irow6301, rows6307]
  all_goals rfl

theorem atot6301 : totK PD2M8K2 D2M8K2.u6301 = [0, 337665145659, 885420628115, 547205919769, 51155237596, 0, 0, 0] := by
  rw [show D2M8K2.u6301 = KTree.node D2M8K2.t6306 (nat_lit 13195423) (nat_lit 1573526018) (nat_lit 0) D2M8K2.t6307 from rfl, totK_node, tot6306, tot6307]
  decide +kernel

theorem arows6303 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6303 = true := by
  rw [show D2M8K2.u6303 = KTree.node D2M8K2.t6308 (nat_lit 13196893) (nat_lit 1164319620) (nat_lit 0) D2M8K2.t6309 from rfl, allE_node, rows6308, irow6303, rows6309]
  all_goals rfl

theorem atot6303 : totK PD2M8K2 D2M8K2.u6303 = [0, 87191050473, 629777593616, 845185874784, 214181814583, 9587713104, 0, 0] := by
  rw [show D2M8K2.u6303 = KTree.node D2M8K2.t6308 (nat_lit 13196893) (nat_lit 1164319620) (nat_lit 0) D2M8K2.t6309 from rfl, totK_node, tot6308, tot6309]
  decide +kernel

theorem arows6304 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6304 = true := by
  rw [show D2M8K2.u6304 = KTree.node D2M8K2.t6310 (nat_lit 13199346) (nat_lit 3450218191) (nat_lit 0) D2M8K2.t6311 from rfl, allE_node, rows6310, irow6304, rows6311]
  all_goals rfl

theorem atot6304 : totK PD2M8K2 D2M8K2.u6304 = [0, 301846748839, 811904648300, 543781835793, 96277403984, 3462014130, 0, 0] := by
  rw [show D2M8K2.u6304 = KTree.node D2M8K2.t6310 (nat_lit 13199346) (nat_lit 3450218191) (nat_lit 0) D2M8K2.t6311 from rfl, totK_node, tot6310, tot6311]
  decide +kernel

theorem arows6307 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6307 = true := by
  rw [show D2M8K2.u6307 = KTree.node D2M8K2.t6312 (nat_lit 13201397) (nat_lit 2301834250) (nat_lit 0) D2M8K2.t6313 from rfl, allE_node, rows6312, irow6307, rows6313]
  all_goals rfl

theorem atot6307 : totK PD2M8K2 D2M8K2.u6307 = [0, 170343636120, 739724473798, 757690867632, 115867769527, 1198073392, 0, 0] := by
  rw [show D2M8K2.u6307 = KTree.node D2M8K2.t6312 (nat_lit 13201397) (nat_lit 2301834250) (nat_lit 0) D2M8K2.t6313 from rfl, totK_node, tot6312, tot6313]
  decide +kernel

theorem arows6308 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6308 = true := by
  rw [show D2M8K2.u6308 = KTree.node D2M8K2.t6314 (nat_lit 13202946) (nat_lit 3303510607) (nat_lit 0) D2M8K2.t6315 from rfl, allE_node, rows6314, irow6308, rows6315]
  all_goals rfl

theorem atot6308 : totK PD2M8K2 D2M8K2.u6308 = [0, 256149710987, 811721334755, 607242842309, 79020241017, 1096505104, 0, 0] := by
  rw [show D2M8K2.u6308 = KTree.node D2M8K2.t6314 (nat_lit 13202946) (nat_lit 3303510607) (nat_lit 0) D2M8K2.t6315 from rfl, totK_node, tot6314, tot6315]
  decide +kernel

theorem arows6310 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6310 = true := by
  rw [show D2M8K2.u6310 = KTree.node D2M8K2.t6316 (nat_lit 13204948) (nat_lit 3291258088) (nat_lit 0) D2M8K2.t6317 from rfl, allE_node, rows6316, irow6310, rows6317]
  all_goals rfl

theorem atot6310 : totK PD2M8K2 D2M8K2.u6310 = [0, 156992247839, 714899298351, 783098480394, 144461973597, 3820764243, 0, 0] := by
  rw [show D2M8K2.u6310 = KTree.node D2M8K2.t6316 (nat_lit 13204948) (nat_lit 3291258088) (nat_lit 0) D2M8K2.t6317 from rfl, totK_node, tot6316, tot6317]
  decide +kernel

theorem arows6311 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6311 = true := by
  rw [show D2M8K2.u6311 = KTree.node D2M8K2.t6318 (nat_lit 13206844) (nat_lit 3840234754) (nat_lit 0) D2M8K2.t6319 from rfl, allE_node, rows6318, irow6311, rows6319]
  all_goals rfl

theorem atot6311 : totK PD2M8K2 D2M8K2.u6311 = [0, 256141203265, 784158843791, 642402927220, 109579670476, 1268739303, 0, 0] := by
  rw [show D2M8K2.u6311 = KTree.node D2M8K2.t6318 (nat_lit 13206844) (nat_lit 3840234754) (nat_lit 0) D2M8K2.t6319 from rfl, totK_node, tot6318, tot6319]
  decide +kernel

theorem arows6315 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6315 = true := by
  rw [show D2M8K2.u6315 = KTree.node D2M8K2.t6320 (nat_lit 13208634) (nat_lit 3824082555) (nat_lit 0) D2M8K2.t6321 from rfl, allE_node, rows6320, irow6315, rows6321]
  all_goals rfl

theorem atot6315 : totK PD2M8K2 D2M8K2.u6315 = [0, 0, 464605955219, 986233822207, 323232087230, 13821724449, 0, 0] := by
  rw [show D2M8K2.u6315 = KTree.node D2M8K2.t6320 (nat_lit 13208634) (nat_lit 3824082555) (nat_lit 0) D2M8K2.t6321 from rfl, totK_node, tot6320, tot6321]
  decide +kernel

theorem arows6316 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6316 = true := by
  rw [show D2M8K2.u6316 = KTree.node D2M8K2.t6322 (nat_lit 13210210) (nat_lit 2553454135) (nat_lit 0) D2M8K2.t6323 from rfl, allE_node, rows6322, irow6316, rows6323]
  all_goals rfl

theorem atot6316 : totK PD2M8K2 D2M8K2.u6316 = [0, 0, 249837211475, 811108950197, 560653353885, 81208163204, 1275377855, 0] := by
  rw [show D2M8K2.u6316 = KTree.node D2M8K2.t6322 (nat_lit 13210210) (nat_lit 2553454135) (nat_lit 0) D2M8K2.t6323 from rfl, totK_node, tot6322, tot6323]
  decide +kernel

theorem arows6318 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6318 = true := by
  rw [show D2M8K2.u6318 = KTree.node D2M8K2.t6324 (nat_lit 13215866) (nat_lit 3101793463) (nat_lit 0) D2M8K2.t6325 from rfl, allE_node, rows6324, irow6318, rows6325]
  all_goals rfl

theorem atot6318 : totK PD2M8K2 D2M8K2.u6318 = [0, 0, 250501593129, 898984937165, 556888032869, 40208470143, 0, 0] := by
  rw [show D2M8K2.u6318 = KTree.node D2M8K2.t6324 (nat_lit 13215866) (nat_lit 3101793463) (nat_lit 0) D2M8K2.t6325 from rfl, totK_node, tot6324, tot6325]
  decide +kernel

theorem arows6319 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6319 = true := by
  rw [show D2M8K2.u6319 = KTree.node D2M8K2.t6326 (nat_lit 13217458) (nat_lit 4161564152) (nat_lit 0) D2M8K2.t6327 from rfl, allE_node, rows6326, irow6319, rows6327]
  all_goals rfl

theorem atot6319 : totK PD2M8K2 D2M8K2.u6319 = [0, 0, 406750658324, 935727725147, 365766959596, 20999887654, 0, 0] := by
  rw [show D2M8K2.u6319 = KTree.node D2M8K2.t6326 (nat_lit 13217458) (nat_lit 4161564152) (nat_lit 0) D2M8K2.t6327 from rfl, totK_node, tot6326, tot6327]
  decide +kernel

theorem arows6322 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6322 = true := by
  rw [show D2M8K2.u6322 = KTree.node D2M8K2.t6328 (nat_lit 13223145) (nat_lit 1805297501) (nat_lit 0) D2M8K2.t6329 from rfl, allE_node, rows6328, irow6322, rows6329]
  all_goals rfl

theorem atot6322 : totK PD2M8K2 D2M8K2.u6322 = [0, 0, 428762316091, 972844050522, 331891388845, 12118062284, 0, 0] := by
  rw [show D2M8K2.u6322 = KTree.node D2M8K2.t6328 (nat_lit 13223145) (nat_lit 1805297501) (nat_lit 0) D2M8K2.t6329 from rfl, totK_node, tot6328, tot6329]
  decide +kernel

theorem arows6323 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6323 = true := by
  rw [show D2M8K2.u6323 = KTree.node D2M8K2.t6330 (nat_lit 13226523) (nat_lit 3679091719) (nat_lit 0) D2M8K2.t6331 from rfl, allE_node, rows6330, irow6323, rows6331]
  all_goals rfl

theorem atot6323 : totK PD2M8K2 D2M8K2.u6323 = [0, 0, 467520642412, 977619841181, 327322832710, 9107445176, 0, 0] := by
  rw [show D2M8K2.u6323 = KTree.node D2M8K2.t6330 (nat_lit 13226523) (nat_lit 3679091719) (nat_lit 0) D2M8K2.t6331 from rfl, totK_node, tot6330, tot6331]
  decide +kernel

theorem arows6325 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6325 = true := by
  rw [show D2M8K2.u6325 = KTree.node D2M8K2.t6332 (nat_lit 13233720) (nat_lit 3224688401) (nat_lit 0) D2M8K2.t6333 from rfl, allE_node, rows6332, irow6325, rows6333]
  all_goals rfl

theorem atot6325 : totK PD2M8K2 D2M8K2.u6325 = [0, 354712777544, 826372015304, 524498372759, 127228306791, 8859721110, 0, 0] := by
  rw [show D2M8K2.u6325 = KTree.node D2M8K2.t6332 (nat_lit 13233720) (nat_lit 3224688401) (nat_lit 0) D2M8K2.t6333 from rfl, totK_node, tot6332, tot6333]
  decide +kernel

theorem arows6326 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6326 = true := by
  rw [show D2M8K2.u6326 = KTree.node D2M8K2.t6334 (nat_lit 13235218) (nat_lit 3955343679) (nat_lit 0) D2M8K2.t6335 from rfl, allE_node, rows6334, irow6326, rows6335]
  all_goals rfl

theorem atot6326 : totK PD2M8K2 D2M8K2.u6326 = [0, 88995923185, 575839019336, 827775636824, 311822817029, 25373788367, 0, 0] := by
  rw [show D2M8K2.u6326 = KTree.node D2M8K2.t6334 (nat_lit 13235218) (nat_lit 3955343679) (nat_lit 0) D2M8K2.t6335 from rfl, totK_node, tot6334, tot6335]
  decide +kernel

theorem arows6332 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6332 = true := by
  rw [show D2M8K2.u6332 = KTree.node D2M8K2.t6336 (nat_lit 13236459) (nat_lit 3482221614) (nat_lit 0) D2M8K2.t6337 from rfl, allE_node, rows6336, irow6332, rows6337]
  all_goals rfl

theorem atot6332 : totK PD2M8K2 D2M8K2.u6332 = [0, 182365284731, 617904452280, 726772360674, 277339611869, 12125819103, 0, 0] := by
  rw [show D2M8K2.u6332 = KTree.node D2M8K2.t6336 (nat_lit 13236459) (nat_lit 3482221614) (nat_lit 0) D2M8K2.t6337 from rfl, totK_node, tot6336, tot6337]
  decide +kernel

theorem arows6333 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6333 = true := by
  rw [show D2M8K2.u6333 = KTree.node D2M8K2.t6338 (nat_lit 13237963) (nat_lit 1684385683) (nat_lit 0) D2M8K2.t6339 from rfl, allE_node, rows6338, irow6333, rows6339]
  all_goals rfl

theorem atot6333 : totK PD2M8K2 D2M8K2.u6333 = [0, 240135779360, 845782921674, 659309172716, 72131681702, 0, 0, 0] := by
  rw [show D2M8K2.u6333 = KTree.node D2M8K2.t6338 (nat_lit 13237963) (nat_lit 1684385683) (nat_lit 0) D2M8K2.t6339 from rfl, totK_node, tot6338, tot6339]
  decide +kernel

theorem arows6335 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6335 = true := by
  rw [show D2M8K2.u6335 = KTree.node D2M8K2.t6340 (nat_lit 13239738) (nat_lit 3553304472) (nat_lit 0) D2M8K2.t6341 from rfl, allE_node, rows6340, irow6335, rows6341]
  all_goals rfl

theorem atot6335 : totK PD2M8K2 D2M8K2.u6335 = [0, 163102450447, 645894260186, 775799548009, 219928901580, 11873025674, 0, 0] := by
  rw [show D2M8K2.u6335 = KTree.node D2M8K2.t6340 (nat_lit 13239738) (nat_lit 3553304472) (nat_lit 0) D2M8K2.t6341 from rfl, totK_node, tot6340, tot6341]
  decide +kernel

theorem arows6336 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6336 = true := by
  rw [show D2M8K2.u6336 = KTree.node D2M8K2.t6342 (nat_lit 13242011) (nat_lit 2626673314) (nat_lit 0) D2M8K2.t6343 from rfl, allE_node, rows6342, irow6336, rows6343]
  all_goals rfl

theorem atot6336 : totK PD2M8K2 D2M8K2.u6336 = [0, 165067109471, 683628793731, 751596485468, 187735819146, 5439011083, 0, 0] := by
  rw [show D2M8K2.u6336 = KTree.node D2M8K2.t6342 (nat_lit 13242011) (nat_lit 2626673314) (nat_lit 0) D2M8K2.t6343 from rfl, totK_node, tot6342, tot6343]
  decide +kernel

theorem arows6339 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6339 = true := by
  rw [show D2M8K2.u6339 = KTree.node D2M8K2.t6344 (nat_lit 13243914) (nat_lit 3823931145) (nat_lit 0) D2M8K2.t6345 from rfl, allE_node, rows6344, irow6339, rows6345]
  all_goals rfl

theorem atot6339 : totK PD2M8K2 D2M8K2.u6339 = [0, 319806810515, 879307228157, 552452480810, 62569514237, 0, 0, 0] := by
  rw [show D2M8K2.u6339 = KTree.node D2M8K2.t6344 (nat_lit 13243914) (nat_lit 3823931145) (nat_lit 0) D2M8K2.t6345 from rfl, totK_node, tot6344, tot6345]
  decide +kernel

theorem arows6340 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6340 = true := by
  rw [show D2M8K2.u6340 = KTree.node D2M8K2.t6346 (nat_lit 13245709) (nat_lit 1232572849) (nat_lit 0) D2M8K2.t6347 from rfl, allE_node, rows6346, irow6340, rows6347]
  all_goals rfl

theorem atot6340 : totK PD2M8K2 D2M8K2.u6340 = [0, 125849005662, 689309944320, 828322386959, 161662568598, 3880716147, 0, 0] := by
  rw [show D2M8K2.u6340 = KTree.node D2M8K2.t6346 (nat_lit 13245709) (nat_lit 1232572849) (nat_lit 0) D2M8K2.t6347 from rfl, totK_node, tot6346, tot6347]
  decide +kernel

theorem arows6342 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6342 = true := by
  rw [show D2M8K2.u6342 = KTree.node D2M8K2.t6348 (nat_lit 13247540) (nat_lit 3532841343) (nat_lit 0) D2M8K2.t6349 from rfl, allE_node, rows6348, irow6342, rows6349]
  all_goals rfl

theorem atot6342 : totK PD2M8K2 D2M8K2.u6342 = [0, 381516222605, 944941320442, 477702542548, 37091743548, 0, 0, 0] := by
  rw [show D2M8K2.u6342 = KTree.node D2M8K2.t6348 (nat_lit 13247540) (nat_lit 3532841343) (nat_lit 0) D2M8K2.t6349 from rfl, totK_node, tot6348, tot6349]
  decide +kernel

theorem arows6343 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6343 = true := by
  rw [show D2M8K2.u6343 = KTree.node D2M8K2.t6350 (nat_lit 13249211) (nat_lit 2879332006) (nat_lit 0) D2M8K2.t6351 from rfl, allE_node, rows6350, irow6343, rows6351]
  all_goals rfl

theorem atot6343 : totK PD2M8K2 D2M8K2.u6343 = [0, 0, 501574529143, 992949503103, 283321433145, 6216931096, 0, 0] := by
  rw [show D2M8K2.u6343 = KTree.node D2M8K2.t6350 (nat_lit 13249211) (nat_lit 2879332006) (nat_lit 0) D2M8K2.t6351 from rfl, totK_node, tot6350, tot6351]
  decide +kernel

theorem arows6347 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6347 = true := by
  rw [show D2M8K2.u6347 = KTree.node D2M8K2.t6352 (nat_lit 13271794) (nat_lit 3808515801) (nat_lit 0) D2M8K2.t6353 from rfl, allE_node, rows6352, irow6347, rows6353]
  all_goals rfl

theorem atot6347 : totK PD2M8K2 D2M8K2.u6347 = [0, 346813991694, 850680875249, 445460196357, 115048503844, 11574339130, 0, 0] := by
  rw [show D2M8K2.u6347 = KTree.node D2M8K2.t6352 (nat_lit 13271794) (nat_lit 3808515801) (nat_lit 0) D2M8K2.t6353 from rfl, totK_node, tot6352, tot6353]
  decide +kernel

theorem arows6348 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6348 = true := by
  rw [show D2M8K2.u6348 = KTree.node D2M8K2.t6354 (nat_lit 13273395) (nat_lit 3426851771) (nat_lit 0) D2M8K2.t6355 from rfl, allE_node, rows6354, irow6348, rows6355]
  all_goals rfl

theorem atot6348 : totK PD2M8K2 D2M8K2.u6348 = [0, 120826630736, 680401438853, 861719327072, 131677356672, 1334361349, 0, 0] := by
  rw [show D2M8K2.u6348 = KTree.node D2M8K2.t6354 (nat_lit 13273395) (nat_lit 3426851771) (nat_lit 0) D2M8K2.t6355 from rfl, totK_node, tot6354, tot6355]
  decide +kernel

theorem arows6350 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6350 = true := by
  rw [show D2M8K2.u6350 = KTree.node D2M8K2.t6356 (nat_lit 13275453) (nat_lit 1256200408) (nat_lit 0) D2M8K2.t6357 from rfl, allE_node, rows6356, irow6350, rows6357]
  all_goals rfl

theorem atot6350 : totK PD2M8K2 D2M8K2.u6350 = [0, 373434484842, 938417533832, 486678404672, 38628391659, 0, 0, 0] := by
  rw [show D2M8K2.u6350 = KTree.node D2M8K2.t6356 (nat_lit 13275453) (nat_lit 1256200408) (nat_lit 0) D2M8K2.t6357 from rfl, totK_node, tot6356, tot6357]
  decide +kernel

theorem arows6351 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6351 = true := by
  rw [show D2M8K2.u6351 = KTree.node D2M8K2.t6358 (nat_lit 13276930) (nat_lit 4117096208) (nat_lit 0) D2M8K2.t6359 from rfl, allE_node, rows6358, irow6351, rows6359]
  all_goals rfl

theorem atot6351 : totK PD2M8K2 D2M8K2.u6351 = [0, 0, 471288581948, 961608795270, 361176791264, 19941272494, 0, 0] := by
  rw [show D2M8K2.u6351 = KTree.node D2M8K2.t6358 (nat_lit 13276930) (nat_lit 4117096208) (nat_lit 0) D2M8K2.t6359 from rfl, totK_node, tot6358, tot6359]
  decide +kernel

theorem arows6354 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6354 = true := by
  rw [show D2M8K2.u6354 = KTree.node D2M8K2.t6360 (nat_lit 13278377) (nat_lit 1610459422) (nat_lit 0) D2M8K2.t6361 from rfl, allE_node, rows6360, irow6354, rows6361]
  all_goals rfl

theorem atot6354 : totK PD2M8K2 D2M8K2.u6354 = [0, 341736371420, 833154166155, 542277693769, 114556530908, 4147651783, 0, 0] := by
  rw [show D2M8K2.u6354 = KTree.node D2M8K2.t6360 (nat_lit 13278377) (nat_lit 1610459422) (nat_lit 0) D2M8K2.t6361 from rfl, totK_node, tot6360, tot6361]
  decide +kernel

theorem arows6355 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6355 = true := by
  rw [show D2M8K2.u6355 = KTree.node D2M8K2.t6362 (nat_lit 13279823) (nat_lit 2183188888) (nat_lit 0) D2M8K2.t6363 from rfl, allE_node, rows6362, irow6355, rows6363]
  all_goals rfl

theorem atot6355 : totK PD2M8K2 D2M8K2.u6355 = [0, 104271980057, 644398900100, 835567201620, 212635155024, 9587713104, 0, 0] := by
  rw [show D2M8K2.u6355 = KTree.node D2M8K2.t6362 (nat_lit 13279823) (nat_lit 2183188888) (nat_lit 0) D2M8K2.t6363 from rfl, totK_node, tot6362, tot6363]
  decide +kernel

theorem arows6357 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6357 = true := by
  rw [show D2M8K2.u6357 = KTree.node D2M8K2.t6364 (nat_lit 13285108) (nat_lit 3691303981) (nat_lit 0) D2M8K2.t6365 from rfl, allE_node, rows6364, irow6357, rows6365]
  all_goals rfl

theorem atot6357 : totK PD2M8K2 D2M8K2.u6357 = [0, 260373570968, 779931577898, 637064869695, 122631371614, 3462014130, 0, 0] := by
  rw [show D2M8K2.u6357 = KTree.node D2M8K2.t6364 (nat_lit 13285108) (nat_lit 3691303981) (nat_lit 0) D2M8K2.t6365 from rfl, totK_node, tot6364, tot6365]
  decide +kernel

theorem arows6358 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6358 = true := by
  rw [show D2M8K2.u6358 = KTree.node D2M8K2.t6366 (nat_lit 13286661) (nat_lit 1502350767) (nat_lit 0) D2M8K2.t6367 from rfl, allE_node, rows6366, irow6358, rows6367]
  all_goals rfl

theorem atot6358 : totK PD2M8K2 D2M8K2.u6358 = [0, 157526790404, 743032706580, 769182733300, 105487166311, 1062926506, 0, 0] := by
  rw [show D2M8K2.u6358 = KTree.node D2M8K2.t6366 (nat_lit 13286661) (nat_lit 1502350767) (nat_lit 0) D2M8K2.t6367 from rfl, totK_node, tot6366, tot6367]
  decide +kernel

theorem arows6363 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6363 = true := by
  rw [show D2M8K2.u6363 = KTree.node D2M8K2.t6368 (nat_lit 13288672) (nat_lit 3742974697) (nat_lit 0) D2M8K2.t6369 from rfl, allE_node, rows6368, irow6363, rows6369]
  all_goals rfl

theorem atot6363 : totK PD2M8K2 D2M8K2.u6363 = [0, 296907891785, 799193807030, 590710870331, 114197406071, 3783381897, 0, 0] := by
  rw [show D2M8K2.u6363 = KTree.node D2M8K2.t6368 (nat_lit 13288672) (nat_lit 3742974697) (nat_lit 0) D2M8K2.t6369 from rfl, totK_node, tot6368, tot6369]
  decide +kernel

theorem arows6364 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6364 = true := by
  rw [show D2M8K2.u6364 = KTree.node D2M8K2.t6370 (nat_lit 13290157) (nat_lit 1062159893) (nat_lit 0) D2M8K2.t6371 from rfl, allE_node, rows6370, irow6364, rows6371]
  all_goals rfl

theorem atot6364 : totK PD2M8K2 D2M8K2.u6364 = [0, 126048264038, 649393097030, 812389319614, 194795623978, 4939878662, 0, 0] := by
  rw [show D2M8K2.u6364 = KTree.node D2M8K2.t6370 (nat_lit 13290157) (nat_lit 1062159893) (nat_lit 0) D2M8K2.t6371 from rfl, totK_node, tot6370, tot6371]
  decide +kernel

theorem arows6366 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6366 = true := by
  rw [show D2M8K2.u6366 = KTree.node D2M8K2.t6372 (nat_lit 13291971) (nat_lit 1620998158) (nat_lit 0) D2M8K2.t6373 from rfl, allE_node, rows6372, irow6366, rows6373]
  all_goals rfl

theorem atot6366 : totK PD2M8K2 D2M8K2.u6366 = [0, 0, 416462966020, 963177265724, 368598250796, 19720553401, 0, 0] := by
  rw [show D2M8K2.u6366 = KTree.node D2M8K2.t6372 (nat_lit 13291971) (nat_lit 1620998158) (nat_lit 0) D2M8K2.t6373 from rfl, totK_node, tot6372, tot6373]
  decide +kernel

theorem arows6367 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6367 = true := by
  rw [show D2M8K2.u6367 = KTree.node D2M8K2.t6374 (nat_lit 13293603) (nat_lit 2034341420) (nat_lit 0) D2M8K2.t6375 from rfl, allE_node, rows6374, irow6367, rows6375]
  all_goals rfl

theorem atot6367 : totK PD2M8K2 D2M8K2.u6367 = [0, 0, 136522137244, 735674083396, 715431080217, 101013528204, 1206465782, 0] := by
  rw [show D2M8K2.u6367 = KTree.node D2M8K2.t6374 (nat_lit 13293603) (nat_lit 2034341420) (nat_lit 0) D2M8K2.t6375 from rfl, totK_node, tot6374, tot6375]
  decide +kernel

theorem arows6370 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6370 = true := by
  rw [show D2M8K2.u6370 = KTree.node D2M8K2.t6376 (nat_lit 13296011) (nat_lit 2413370841) (nat_lit 0) D2M8K2.t6377 from rfl, allE_node, rows6376, irow6370, rows6377]
  all_goals rfl

theorem atot6370 : totK PD2M8K2 D2M8K2.u6370 = [0, 0, 419780623096, 946536416868, 412662696909, 29461051552, 0, 0] := by
  rw [show D2M8K2.u6370 = KTree.node D2M8K2.t6376 (nat_lit 13296011) (nat_lit 2413370841) (nat_lit 0) D2M8K2.t6377 from rfl, totK_node, tot6376, tot6377]
  decide +kernel

theorem arows6371 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6371 = true := by
  rw [show D2M8K2.u6371 = KTree.node D2M8K2.t6378 (nat_lit 13299216) (nat_lit 2483732750) (nat_lit 0) D2M8K2.t6379 from rfl, allE_node, rows6378, irow6371, rows6379]
  all_goals rfl

theorem atot6371 : totK PD2M8K2 D2M8K2.u6371 = [0, 0, 352337306507, 939384451489, 466862717032, 33188462008, 0, 0] := by
  rw [show D2M8K2.u6371 = KTree.node D2M8K2.t6378 (nat_lit 13299216) (nat_lit 2483732750) (nat_lit 0) D2M8K2.t6379 from rfl, totK_node, tot6378, tot6379]
  decide +kernel

theorem arows6373 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6373 = true := by
  rw [show D2M8K2.u6373 = KTree.node D2M8K2.t6380 (nat_lit 13300751) (nat_lit 1669315063) (nat_lit 0) D2M8K2.t6381 from rfl, allE_node, rows6380, irow6373, rows6381]
  all_goals rfl

theorem atot6373 : totK PD2M8K2 D2M8K2.u6373 = [0, 0, 87382242367, 583090160326, 824788042227, 233753960337, 10552856705, 0] := by
  rw [show D2M8K2.u6373 = KTree.node D2M8K2.t6380 (nat_lit 13300751) (nat_lit 1669315063) (nat_lit 0) D2M8K2.t6381 from rfl, totK_node, tot6380, tot6381]
  decide +kernel

theorem arows6374 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6374 = true := by
  rw [show D2M8K2.u6374 = KTree.node D2M8K2.t6382 (nat_lit 13306013) (nat_lit 1900190683) (nat_lit 0) D2M8K2.t6383 from rfl, allE_node, rows6382, irow6374, rows6383]
  all_goals rfl

theorem atot6374 : totK PD2M8K2 D2M8K2.u6374 = [0, 0, 321300795957, 863410858199, 486464814383, 68327885235, 2463340669, 0] := by
  rw [show D2M8K2.u6374 = KTree.node D2M8K2.t6382 (nat_lit 13306013) (nat_lit 1900190683) (nat_lit 0) D2M8K2.t6383 from rfl, totK_node, tot6382, tot6383]
  decide +kernel

theorem arows6378 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6378 = true := by
  rw [show D2M8K2.u6378 = KTree.node D2M8K2.t6384 (nat_lit 13307669) (nat_lit 2373483525) (nat_lit 0) D2M8K2.t6385 from rfl, allE_node, rows6384, irow6378, rows6385]
  all_goals rfl

theorem atot6378 : totK PD2M8K2 D2M8K2.u6378 = [0, 0, 101721056593, 647416116912, 758406663309, 153707654619, 4574395652, 0] := by
  rw [show D2M8K2.u6378 = KTree.node D2M8K2.t6384 (nat_lit 13307669) (nat_lit 2373483525) (nat_lit 0) D2M8K2.t6385 from rfl, totK_node, tot6384, tot6385]
  decide +kernel

theorem arows6379 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6379 = true := by
  rw [show D2M8K2.u6379 = KTree.node D2M8K2.t6386 (nat_lit 13309688) (nat_lit 3552994527) (nat_lit 0) D2M8K2.t6387 from rfl, allE_node, rows6386, irow6379, rows6387]
  all_goals rfl

theorem atot6379 : totK PD2M8K2 D2M8K2.u6379 = [0, 0, 402307222447, 966315852437, 404993318156, 19698073816, 0, 0] := by
  rw [show D2M8K2.u6379 = KTree.node D2M8K2.t6386 (nat_lit 13309688) (nat_lit 3552994527) (nat_lit 0) D2M8K2.t6387 from rfl, totK_node, tot6386, tot6387]
  decide +kernel

theorem arows6381 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6381 = true := by
  rw [show D2M8K2.u6381 = KTree.node D2M8K2.t6388 (nat_lit 13354870) (nat_lit 3255069376) (nat_lit 0) D2M8K2.t6389 from rfl, allE_node, rows6388, irow6381, rows6389]
  all_goals rfl

theorem atot6381 : totK PD2M8K2 D2M8K2.u6381 = [0, 386406070652, 932337491667, 408486554728, 34999598269, 5067492771, 0, 0] := by
  rw [show D2M8K2.u6381 = KTree.node D2M8K2.t6388 (nat_lit 13354870) (nat_lit 3255069376) (nat_lit 0) D2M8K2.t6389 from rfl, totK_node, tot6388, tot6389]
  decide +kernel

theorem arows6382 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6382 = true := by
  rw [show D2M8K2.u6382 = KTree.node D2M8K2.t6390 (nat_lit 13356620) (nat_lit 3219352923) (nat_lit 0) D2M8K2.t6391 from rfl, allE_node, rows6390, irow6382, rows6391]
  all_goals rfl

theorem atot6382 : totK PD2M8K2 D2M8K2.u6382 = [0, 107807068112, 680245127492, 861026561486, 140558348660, 1310166938, 0, 0] := by
  rw [show D2M8K2.u6382 = KTree.node D2M8K2.t6390 (nat_lit 13356620) (nat_lit 3219352923) (nat_lit 0) D2M8K2.t6391 from rfl, totK_node, tot6390, tot6391]
  decide +kernel

theorem arows6385 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6385 = true := by
  rw [show D2M8K2.u6385 = KTree.node D2M8K2.t6392 (nat_lit 13358541) (nat_lit 1467691419) (nat_lit 0) D2M8K2.t6393 from rfl, allE_node, rows6392, irow6385, rows6393]
  all_goals rfl

theorem atot6385 : totK PD2M8K2 D2M8K2.u6385 = [0, 324105859009, 907326022893, 544907886211, 49313201202, 0, 0, 0] := by
  rw [show D2M8K2.u6385 = KTree.node D2M8K2.t6392 (nat_lit 13358541) (nat_lit 1467691419) (nat_lit 0) D2M8K2.t6393 from rfl, totK_node, tot6392, tot6393]
  decide +kernel

theorem arows6386 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6386 = true := by
  rw [show D2M8K2.u6386 = KTree.node D2M8K2.t6394 (nat_lit 13360113) (nat_lit 1819203409) (nat_lit 0) D2M8K2.t6395 from rfl, allE_node, rows6394, irow6386, rows6395]
  all_goals rfl

theorem atot6386 : totK PD2M8K2 D2M8K2.u6386 = [0, 73966261092, 500464565298, 893253801322, 335262817528, 15013989272, 0, 0] := by
  rw [show D2M8K2.u6386 = KTree.node D2M8K2.t6394 (nat_lit 13360113) (nat_lit 1819203409) (nat_lit 0) D2M8K2.t6395 from rfl, totK_node, tot6394, tot6395]
  decide +kernel

theorem arows6388 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6388 = true := by
  rw [show D2M8K2.u6388 = KTree.node D2M8K2.t6396 (nat_lit 13361602) (nat_lit 4065776122) (nat_lit 0) D2M8K2.t6397 from rfl, allE_node, rows6396, irow6388, rows6397]
  all_goals rfl

theorem atot6388 : totK PD2M8K2 D2M8K2.u6388 = [0, 347406907163, 935426623800, 498561492180, 36329590586, 0, 0, 0] := by
  rw [show D2M8K2.u6388 = KTree.node D2M8K2.t6396 (nat_lit 13361602) (nat_lit 4065776122) (nat_lit 0) D2M8K2.t6397 from rfl, totK_node, tot6396, tot6397]
  decide +kernel

theorem arows6389 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6389 = true := by
  rw [show D2M8K2.u6389 = KTree.node D2M8K2.t6398 (nat_lit 13363310) (nat_lit 3625637998) (nat_lit 0) D2M8K2.t6399 from rfl, allE_node, rows6398, irow6389, rows6399]
  all_goals rfl

theorem atot6389 : totK PD2M8K2 D2M8K2.u6389 = [0, 25587054555, 492871562053, 954137410772, 290724022688, 13049727234, 0, 0] := by
  rw [show D2M8K2.u6389 = KTree.node D2M8K2.t6398 (nat_lit 13363310) (nat_lit 3625637998) (nat_lit 0) D2M8K2.t6399 from rfl, totK_node, tot6398, tot6399]
  decide +kernel

theorem arows6397 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6397 = true := by
  rw [show D2M8K2.u6397 = KTree.node D2M8K2.t6400 (nat_lit 13365315) (nat_lit 3641591707) (nat_lit 0) D2M8K2.t6401 from rfl, allE_node, rows6400, irow6397, rows6401]
  all_goals rfl

theorem atot6397 : totK PD2M8K2 D2M8K2.u6397 = [0, 297349059289, 870167213658, 546931570373, 57880271914, 1104198603, 0, 0] := by
  rw [show D2M8K2.u6397 = KTree.node D2M8K2.t6400 (nat_lit 13365315) (nat_lit 3641591707) (nat_lit 0) D2M8K2.t6401 from rfl, totK_node, tot6400, tot6401]
  decide +kernel

theorem arows6398 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6398 = true := by
  rw [show D2M8K2.u6398 = KTree.node D2M8K2.t6402 (nat_lit 13367816) (nat_lit 3643078003) (nat_lit 0) D2M8K2.t6403 from rfl, allE_node, rows6402, irow6398, rows6403]
  all_goals rfl

theorem atot6398 : totK PD2M8K2 D2M8K2.u6398 = [0, 191527552650, 710438963593, 743131472579, 150616955949, 3581949829, 0, 0] := by
  rw [show D2M8K2.u6398 = KTree.node D2M8K2.t6402 (nat_lit 13367816) (nat_lit 3643078003) (nat_lit 0) D2M8K2.t6403 from rfl, totK_node, tot6402, tot6403]
  decide +kernel

theorem arows6400 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6400 = true := by
  rw [show D2M8K2.u6400 = KTree.node D2M8K2.t6404 (nat_lit 13369005) (nat_lit 1506276760) (nat_lit 0) D2M8K2.t6405 from rfl, allE_node, rows6404, irow6400, rows6405]
  all_goals rfl

theorem atot6400 : totK PD2M8K2 D2M8K2.u6400 = [0, 245678469189, 808132545869, 650053683256, 96160250630, 1096505104, 0, 0] := by
  rw [show D2M8K2.u6400 = KTree.node D2M8K2.t6404 (nat_lit 13369005) (nat_lit 1506276760) (nat_lit 0) D2M8K2.t6405 from rfl, totK_node, tot6404, tot6405]
  decide +kernel

theorem arows6401 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6401 = true := by
  rw [show D2M8K2.u6401 = KTree.node D2M8K2.t6406 (nat_lit 13374721) (nat_lit 1575612183) (nat_lit 0) D2M8K2.t6407 from rfl, allE_node, rows6406, irow6401, rows6407]
  all_goals rfl

theorem atot6401 : totK PD2M8K2 D2M8K2.u6401 = [0, 0, 467218420609, 978630532090, 310904170116, 13624150839, 0, 0] := by
  rw [show D2M8K2.u6401 = KTree.node D2M8K2.t6406 (nat_lit 13374721) (nat_lit 1575612183) (nat_lit 0) D2M8K2.t6407 from rfl, totK_node, tot6406, tot6407]
  decide +kernel

theorem arows6404 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6404 = true := by
  rw [show D2M8K2.u6404 = KTree.node D2M8K2.t6408 (nat_lit 13376356) (nat_lit 3934332962) (nat_lit 0) D2M8K2.t6409 from rfl, allE_node, rows6408, irow6404, rows6409]
  all_goals rfl

theorem atot6404 : totK PD2M8K2 D2M8K2.u6404 = [0, 0, 194897358714, 811481152410, 597102537355, 69416559484, 1103454931, 0] := by
  rw [show D2M8K2.u6404 = KTree.node D2M8K2.t6408 (nat_lit 13376356) (nat_lit 3934332962) (nat_lit 0) D2M8K2.t6409 from rfl, totK_node, tot6408, tot6409]
  decide +kernel

theorem arows6405 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6405 = true := by
  rw [show D2M8K2.u6405 = KTree.node D2M8K2.t6410 (nat_lit 13378905) (nat_lit 1702590941) (nat_lit 0) D2M8K2.t6411 from rfl, allE_node, rows6410, irow6405, rows6411]
  all_goals rfl

theorem atot6405 : totK PD2M8K2 D2M8K2.u6405 = [0, 0, 411677522293, 942794970534, 424693348058, 21789099889, 0, 0] := by
  rw [show D2M8K2.u6405 = KTree.node D2M8K2.t6410 (nat_lit 13378905) (nat_lit 1702590941) (nat_lit 0) D2M8K2.t6411 from rfl, totK_node, tot6410, tot6411]
  decide +kernel

theorem arows6407 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6407 = true := by
  rw [show D2M8K2.u6407 = KTree.node D2M8K2.t6412 (nat_lit 13382255) (nat_lit 1798633036) (nat_lit 0) D2M8K2.t6413 from rfl, allE_node, rows6412, irow6407, rows6413]
  all_goals rfl

theorem atot6407 : totK PD2M8K2 D2M8K2.u6407 = [0, 0, 395773926312, 945345788986, 405022214981, 23272095769, 0, 0] := by
  rw [show D2M8K2.u6407 = KTree.node D2M8K2.t6412 (nat_lit 13382255) (nat_lit 1798633036) (nat_lit 0) D2M8K2.t6413 from rfl, totK_node, tot6412, tot6413]
  decide +kernel

theorem arows6408 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6408 = true := by
  rw [show D2M8K2.u6408 = KTree.node D2M8K2.t6414 (nat_lit 13386048) (nat_lit 3507538042) (nat_lit 0) D2M8K2.t6415 from rfl, allE_node, rows6414, irow6408, rows6415]
  all_goals rfl

theorem atot6408 : totK PD2M8K2 D2M8K2.u6408 = [0, 0, 449479808766, 958886379907, 318576735100, 10013033234, 0, 0] := by
  rw [show D2M8K2.u6408 = KTree.node D2M8K2.t6414 (nat_lit 13386048) (nat_lit 3507538042) (nat_lit 0) D2M8K2.t6415 from rfl, totK_node, tot6414, tot6415]
  decide +kernel

theorem arows6412 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6412 = true := by
  rw [show D2M8K2.u6412 = KTree.node D2M8K2.t6416 (nat_lit 13389489) (nat_lit 1854050842) (nat_lit 0) D2M8K2.t6417 from rfl, allE_node, rows6416, irow6412, rows6417]
  all_goals rfl

theorem atot6412 : totK PD2M8K2 D2M8K2.u6412 = [0, 0, 312424699445, 897320045037, 492396220149, 36285546532, 0, 0] := by
  rw [show D2M8K2.u6412 = KTree.node D2M8K2.t6416 (nat_lit 13389489) (nat_lit 1854050842) (nat_lit 0) D2M8K2.t6417 from rfl, totK_node, tot6416, tot6417]
  decide +kernel

theorem arows6413 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6413 = true := by
  rw [show D2M8K2.u6413 = KTree.node D2M8K2.t6418 (nat_lit 13391527) (nat_lit 2356037797) (nat_lit 0) D2M8K2.t6419 from rfl, allE_node, rows6418, irow6413, rows6419]
  all_goals rfl

theorem atot6413 : totK PD2M8K2 D2M8K2.u6413 = [0, 175895516967, 395522376646, 466088798007, 540513775279, 136002144629, 4779662215, 0] := by
  rw [show D2M8K2.u6413 = KTree.node D2M8K2.t6418 (nat_lit 13391527) (nat_lit 2356037797) (nat_lit 0) D2M8K2.t6419 from rfl, totK_node, tot6418, tot6419]
  decide +kernel

theorem arows6415 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6415 = true := by
  rw [show D2M8K2.u6415 = KTree.node D2M8K2.t6420 (nat_lit 13396936) (nat_lit 3725498621) (nat_lit 0) D2M8K2.t6421 from rfl, allE_node, rows6420, irow6415, rows6421]
  all_goals rfl

theorem atot6415 : totK PD2M8K2 D2M8K2.u6415 = [0, 230789075260, 777297513153, 656974595907, 105654977952, 1369150432, 0, 0] := by
  rw [show D2M8K2.u6415 = KTree.node D2M8K2.t6420 (nat_lit 13396936) (nat_lit 3725498621) (nat_lit 0) D2M8K2.t6421 from rfl, totK_node, tot6420, tot6421]
  decide +kernel

theorem arows6416 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6416 = true := by
  rw [show D2M8K2.u6416 = KTree.node D2M8K2.t6422 (nat_lit 13399301) (nat_lit 2224477769) (nat_lit 0) D2M8K2.t6423 from rfl, allE_node, rows6422, irow6416, rows6423]
  all_goals rfl

theorem atot6416 : totK PD2M8K2 D2M8K2.u6416 = [0, 227696603180, 801611845120, 712608966711, 79101444737, 0, 0, 0] := by
  rw [show D2M8K2.u6416 = KTree.node D2M8K2.t6422 (nat_lit 13399301) (nat_lit 2224477769) (nat_lit 0) D2M8K2.t6423 from rfl, totK_node, tot6422, tot6423]
  decide +kernel

theorem arows6419 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6419 = true := by
  rw [show D2M8K2.u6419 = KTree.node D2M8K2.t6424 (nat_lit 13400553) (nat_lit 1372755679) (nat_lit 0) D2M8K2.t6425 from rfl, allE_node, rows6424, irow6419, rows6425]
  all_goals rfl

theorem atot6419 : totK PD2M8K2 D2M8K2.u6419 = [0, 186809779668, 718662924326, 689496332550, 214304026276, 19354310117, 0, 0] := by
  rw [show D2M8K2.u6419 = KTree.node D2M8K2.t6424 (nat_lit 13400553) (nat_lit 1372755679) (nat_lit 0) D2M8K2.t6425 from rfl, totK_node, tot6424, tot6425]
  decide +kernel

theorem arows6420 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6420 = true := by
  rw [show D2M8K2.u6420 = KTree.node D2M8K2.t6426 (nat_lit 13402129) (nat_lit 1360883635) (nat_lit 0) D2M8K2.t6427 from rfl, allE_node, rows6426, irow6420, rows6427]
  all_goals rfl

theorem atot6420 : totK PD2M8K2 D2M8K2.u6420 = [0, 153940562603, 549178835584, 758508936550, 317936157251, 13408088780, 0, 0] := by
  rw [show D2M8K2.u6420 = KTree.node D2M8K2.t6426 (nat_lit 13402129) (nat_lit 1360883635) (nat_lit 0) D2M8K2.t6427 from rfl, totK_node, tot6426, tot6427]
  decide +kernel

theorem arows6422 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6422 = true := by
  rw [show D2M8K2.u6422 = KTree.node D2M8K2.t6428 (nat_lit 13403589) (nat_lit 1513106895) (nat_lit 0) D2M8K2.t6429 from rfl, allE_node, rows6428, irow6422, rows6429]
  all_goals rfl

theorem atot6422 : totK PD2M8K2 D2M8K2.u6422 = [0, 271772526176, 861405422710, 620316861079, 66250293324, 0, 0, 0] := by
  rw [show D2M8K2.u6422 = KTree.node D2M8K2.t6428 (nat_lit 13403589) (nat_lit 1513106895) (nat_lit 0) D2M8K2.t6429 from rfl, totK_node, tot6428, tot6429]
  decide +kernel

theorem arows6423 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6423 = true := by
  rw [show D2M8K2.u6423 = KTree.node D2M8K2.t6430 (nat_lit 13405298) (nat_lit 3995083918) (nat_lit 0) D2M8K2.t6431 from rfl, allE_node, rows6430, irow6423, rows6431]
  all_goals rfl

theorem atot6423 : totK PD2M8K2 D2M8K2.u6423 = [0, 152621159257, 651099839942, 780103725094, 209168603113, 9583672031, 0, 0] := by
  rw [show D2M8K2.u6423 = KTree.node D2M8K2.t6430 (nat_lit 13405298) (nat_lit 3995083918) (nat_lit 0) D2M8K2.t6431 from rfl, totK_node, tot6430, tot6431]
  decide +kernel

theorem arows6428 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6428 = true := by
  rw [show D2M8K2.u6428 = KTree.node D2M8K2.t6432 (nat_lit 13407424) (nat_lit 2823986371) (nat_lit 0) D2M8K2.t6433 from rfl, allE_node, rows6432, irow6428, rows6433]
  all_goals rfl

theorem atot6428 : totK PD2M8K2 D2M8K2.u6428 = [0, 169719410940, 741709884092, 769447932661, 128941882371, 1198073392, 0, 0] := by
  rw [show D2M8K2.u6428 = KTree.node D2M8K2.t6432 (nat_lit 13407424) (nat_lit 2823986371) (nat_lit 0) D2M8K2.t6433 from rfl, totK_node, tot6432, tot6433]
  decide +kernel

theorem arows6429 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6429 = true := by
  rw [show D2M8K2.u6429 = KTree.node D2M8K2.t6434 (nat_lit 13413071) (nat_lit 2154287778) (nat_lit 0) D2M8K2.t6435 from rfl, allE_node, rows6434, irow6429, rows6435]
  all_goals rfl

theorem atot6429 : totK PD2M8K2 D2M8K2.u6429 = [0, 281321592433, 800706147060, 614074657129, 122249685829, 4030866388, 0, 0] := by
  rw [show D2M8K2.u6429 = KTree.node D2M8K2.t6434 (nat_lit 13413071) (nat_lit 2154287778) (nat_lit 0) D2M8K2.t6435 from rfl, totK_node, tot6434, tot6435]
  decide +kernel

theorem arows6431 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6431 = true := by
  rw [show D2M8K2.u6431 = KTree.node D2M8K2.t6436 (nat_lit 13414514) (nat_lit 3175271420) (nat_lit 0) D2M8K2.t6437 from rfl, allE_node, rows6436, irow6431, rows6437]
  all_goals rfl

theorem atot6431 : totK PD2M8K2 D2M8K2.u6431 = [0, 159992617153, 697190241030, 787799012682, 168931222002, 2304167554, 0, 0] := by
  rw [show D2M8K2.u6431 = KTree.node D2M8K2.t6436 (nat_lit 13414514) (nat_lit 3175271420) (nat_lit 0) D2M8K2.t6437 from rfl, totK_node, tot6436, tot6437]
  decide +kernel

theorem arows6432 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6432 = true := by
  rw [show D2M8K2.u6432 = KTree.node D2M8K2.t6438 (nat_lit 13416172) (nat_lit 3771370132) (nat_lit 0) D2M8K2.t6439 from rfl, allE_node, rows6438, irow6432, rows6439]
  all_goals rfl

theorem atot6432 : totK PD2M8K2 D2M8K2.u6432 = [193081648232, 461015719043, 377104508221, 484341945719, 247128691778, 19678284834, 0, 0] := by
  rw [show D2M8K2.u6432 = KTree.node D2M8K2.t6438 (nat_lit 13416172) (nat_lit 3771370132) (nat_lit 0) D2M8K2.t6439 from rfl, totK_node, tot6438, tot6439]
  decide +kernel

theorem arows6435 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6435 = true := by
  rw [show D2M8K2.u6435 = KTree.node D2M8K2.t6440 (nat_lit 13936080) (nat_lit 3547789339) (nat_lit 0) D2M8K2.t6441 from rfl, allE_node, rows6440, irow6435, rows6441]
  all_goals rfl

theorem atot6435 : totK PD2M8K2 D2M8K2.u6435 = [239859944234, 788637477731, 646922889952, 110255121681, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u6435 = KTree.node D2M8K2.t6440 (nat_lit 13936080) (nat_lit 3547789339) (nat_lit 0) D2M8K2.t6441 from rfl, totK_node, tot6440, tot6441]
  decide +kernel

theorem arows6436 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6436 = true := by
  rw [show D2M8K2.u6436 = KTree.node D2M8K2.t6442 (nat_lit 13941589) (nat_lit 1266844294) (nat_lit 0) D2M8K2.t6443 from rfl, allE_node, rows6442, irow6436, rows6443]
  all_goals rfl

theorem atot6436 : totK PD2M8K2 D2M8K2.u6436 = [248143520574, 819853598264, 675650725544, 77942668709, 0, 0, 0, 0] := by
  rw [show D2M8K2.u6436 = KTree.node D2M8K2.t6442 (nat_lit 13941589) (nat_lit 1266844294) (nat_lit 0) D2M8K2.t6443 from rfl, totK_node, tot6442, tot6443]
  decide +kernel

theorem arows6438 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6438 = true := by
  rw [show D2M8K2.u6438 = KTree.node D2M8K2.t6444 (nat_lit 13943122) (nat_lit 3926597844) (nat_lit 0) D2M8K2.t6445 from rfl, allE_node, rows6444, irow6438, rows6445]
  all_goals rfl

theorem atot6438 : totK PD2M8K2 D2M8K2.u6438 = [165316035488, 743364751539, 758061518608, 124811374926, 1164319620, 0, 0, 0] := by
  rw [show D2M8K2.u6438 = KTree.node D2M8K2.t6444 (nat_lit 13943122) (nat_lit 3926597844) (nat_lit 0) D2M8K2.t6445 from rfl, totK_node, tot6444, tot6445]
  decide +kernel

theorem arows6439 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6439 = true := by
  rw [show D2M8K2.u6439 = KTree.node D2M8K2.t6446 (nat_lit 13945009) (nat_lit 1515350557) (nat_lit 0) D2M8K2.t6447 from rfl, allE_node, rows6446, irow6439, rows6447]
  all_goals rfl

theorem atot6439 : totK PD2M8K2 D2M8K2.u6439 = [229561492776, 676918389387, 656726817165, 204516897401, 11885407614, 0, 0, 0] := by
  rw [show D2M8K2.u6439 = KTree.node D2M8K2.t6446 (nat_lit 13945009) (nat_lit 1515350557) (nat_lit 0) D2M8K2.t6447 from rfl, totK_node, tot6446, tot6447]
  decide +kernel

theorem arows6443 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6443 = true := by
  rw [show D2M8K2.u6443 = KTree.node D2M8K2.t6448 (nat_lit 13946635) (nat_lit 1585534026) (nat_lit 0) D2M8K2.t6449 from rfl, allE_node, rows6448, irow6443, rows6449]
  all_goals rfl

theorem atot6443 : totK PD2M8K2 D2M8K2.u6443 = [150414475504, 693909701690, 763823305818, 157129699027, 2348440009, 0, 0, 0] := by
  rw [show D2M8K2.u6443 = KTree.node D2M8K2.t6448 (nat_lit 13946635) (nat_lit 1585534026) (nat_lit 0) D2M8K2.t6449 from rfl, totK_node, tot6448, tot6449]
  decide +kernel

theorem arows6444 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6444 = true := by
  rw [show D2M8K2.u6444 = KTree.node D2M8K2.t6450 (nat_lit 13948536) (nat_lit 3626985561) (nat_lit 0) D2M8K2.t6451 from rfl, allE_node, rows6450, irow6444, rows6451]
  all_goals rfl

theorem atot6444 : totK PD2M8K2 D2M8K2.u6444 = [245497822143, 718753537009, 632618847564, 172560012052, 10902245252, 0, 0, 0] := by
  rw [show D2M8K2.u6444 = KTree.node D2M8K2.t6450 (nat_lit 13948536) (nat_lit 3626985561) (nat_lit 0) D2M8K2.t6451 from rfl, totK_node, tot6450, tot6451]
  decide +kernel

theorem arows6446 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6446 = true := by
  rw [show D2M8K2.u6446 = KTree.node D2M8K2.t6452 (nat_lit 13949765) (nat_lit 2348817020) (nat_lit 0) D2M8K2.t6453 from rfl, allE_node, rows6452, irow6446, rows6453]
  all_goals rfl

theorem atot6446 : totK PD2M8K2 D2M8K2.u6446 = [175544997169, 756572010500, 739257013875, 112709162989, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u6446 = KTree.node D2M8K2.t6452 (nat_lit 13949765) (nat_lit 2348817020) (nat_lit 0) D2M8K2.t6453 from rfl, totK_node, tot6452, tot6453]
  decide +kernel

theorem arows6447 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6447 = true := by
  rw [show D2M8K2.u6447 = KTree.node D2M8K2.t6454 (nat_lit 13952032) (nat_lit 2811527571) (nat_lit 0) D2M8K2.t6455 from rfl, allE_node, rows6454, irow6447, rows6455]
  all_goals rfl

theorem atot6447 : totK PD2M8K2 D2M8K2.u6447 = [249975075282, 770900988680, 638851588092, 126068516276, 3884009855, 0, 0, 0] := by
  rw [show D2M8K2.u6447 = KTree.node D2M8K2.t6454 (nat_lit 13952032) (nat_lit 2811527571) (nat_lit 0) D2M8K2.t6455 from rfl, totK_node, tot6454, tot6455]
  decide +kernel

theorem arows6450 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6450 = true := by
  rw [show D2M8K2.u6450 = KTree.node D2M8K2.t6456 (nat_lit 13954217) (nat_lit 1795829355) (nat_lit 0) D2M8K2.t6457 from rfl, allE_node, rows6456, irow6450, rows6457]
  all_goals rfl

theorem atot6450 : totK PD2M8K2 D2M8K2.u6450 = [76459986009, 544403241715, 879810215279, 271519430047, 8710740030, 0, 0, 0] := by
  rw [show D2M8K2.u6450 = KTree.node D2M8K2.t6456 (nat_lit 13954217) (nat_lit 1795829355) (nat_lit 0) D2M8K2.t6457 from rfl, totK_node, tot6456, tot6457]
  decide +kernel

theorem arows6451 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6451 = true := by
  rw [show D2M8K2.u6451 = KTree.node D2M8K2.t6458 (nat_lit 13956077) (nat_lit 1934743799) (nat_lit 0) D2M8K2.t6459 from rfl, allE_node, rows6458, irow6451, rows6459]
  all_goals rfl

theorem atot6451 : totK PD2M8K2 D2M8K2.u6451 = [0, 349363998116, 915740776878, 453430752187, 32422137020, 0, 0, 0] := by
  rw [show D2M8K2.u6451 = KTree.node D2M8K2.t6458 (nat_lit 13956077) (nat_lit 1934743799) (nat_lit 0) D2M8K2.t6459 from rfl, totK_node, tot6458, tot6459]
  decide +kernel

theorem arows6453 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6453 = true := by
  rw [show D2M8K2.u6453 = KTree.node D2M8K2.t6460 (nat_lit 13957324) (nat_lit 3358494679) (nat_lit 0) D2M8K2.t6461 from rfl, allE_node, rows6460, irow6453, rows6461]
  all_goals rfl

theorem atot6453 : totK PD2M8K2 D2M8K2.u6453 = [0, 100489215530, 673565073080, 801683566230, 145401435901, 1369150432, 0, 0] := by
  rw [show D2M8K2.u6453 = KTree.node D2M8K2.t6460 (nat_lit 13957324) (nat_lit 3358494679) (nat_lit 0) D2M8K2.t6461 from rfl, totK_node, tot6460, tot6461]
  decide +kernel

theorem arows6454 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6454 = true := by
  rw [show D2M8K2.u6454 = KTree.node D2M8K2.t6462 (nat_lit 13962933) (nat_lit 1722417570) (nat_lit 0) D2M8K2.t6463 from rfl, allE_node, rows6462, irow6454, rows6463]
  all_goals rfl

theorem atot6454 : totK PD2M8K2 D2M8K2.u6454 = [0, 394010314558, 969532091977, 410651401645, 17707432322, 0, 0, 0] := by
  rw [show D2M8K2.u6454 = KTree.node D2M8K2.t6462 (nat_lit 13962933) (nat_lit 1722417570) (nat_lit 0) D2M8K2.t6463 from rfl, totK_node, tot6462, tot6463]
  decide +kernel

theorem arows6460 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6460 = true := by
  rw [show D2M8K2.u6460 = KTree.node D2M8K2.t6464 (nat_lit 13966593) (nat_lit 1783014365) (nat_lit 0) D2M8K2.t6465 from rfl, allE_node, rows6464, irow6460, rows6465]
  all_goals rfl

theorem atot6460 : totK PD2M8K2 D2M8K2.u6460 = [0, 360601638340, 919632701608, 460047120310, 26643838413, 0, 0, 0] := by
  rw [show D2M8K2.u6460 = KTree.node D2M8K2.t6464 (nat_lit 13966593) (nat_lit 1783014365) (nat_lit 0) D2M8K2.t6465 from rfl, totK_node, tot6464, tot6465]
  decide +kernel

theorem arows6461 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6461 = true := by
  rw [show D2M8K2.u6461 = KTree.node D2M8K2.t6466 (nat_lit 13969662) (nat_lit 3969937440) (nat_lit 0) D2M8K2.t6467 from rfl, allE_node, rows6466, irow6461, rows6467]
  all_goals rfl

theorem atot6461 : totK PD2M8K2 D2M8K2.u6461 = [0, 346976311358, 932839812092, 456360669913, 26919015333, 0, 0, 0] := by
  rw [show D2M8K2.u6461 = KTree.node D2M8K2.t6466 (nat_lit 13969662) (nat_lit 3969937440) (nat_lit 0) D2M8K2.t6467 from rfl, totK_node, tot6466, tot6467]
  decide +kernel

theorem arows6463 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6463 = true := by
  rw [show D2M8K2.u6463 = KTree.node D2M8K2.t6468 (nat_lit 13973216) (nat_lit 2884526455) (nat_lit 0) D2M8K2.t6469 from rfl, allE_node, rows6468, irow6463, rows6469]
  all_goals rfl

theorem atot6463 : totK PD2M8K2 D2M8K2.u6463 = [0, 417165009241, 975389410139, 391141413136, 14660253455, 0, 0, 0] := by
  rw [show D2M8K2.u6463 = KTree.node D2M8K2.t6468 (nat_lit 13973216) (nat_lit 2884526455) (nat_lit 0) D2M8K2.t6469 from rfl, totK_node, tot6468, tot6469]
  decide +kernel

theorem arows6464 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6464 = true := by
  rw [show D2M8K2.u6464 = KTree.node D2M8K2.t6470 (nat_lit 13980199) (nat_lit 1995407747) (nat_lit 0) D2M8K2.t6471 from rfl, allE_node, rows6470, irow6464, rows6471]
  all_goals rfl

theorem atot6464 : totK PD2M8K2 D2M8K2.u6464 = [338449428671, 800786255908, 521693992680, 155175290037, 13468148062, 0, 0, 0] := by
  rw [show D2M8K2.u6464 = KTree.node D2M8K2.t6470 (nat_lit 13980199) (nat_lit 1995407747) (nat_lit 0) D2M8K2.t6471 from rfl, totK_node, tot6470, tot6471]
  decide +kernel

theorem arows6467 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6467 = true := by
  rw [show D2M8K2.u6467 = KTree.node D2M8K2.t6472 (nat_lit 13981675) (nat_lit 1490263895) (nat_lit 0) D2M8K2.t6473 from rfl, allE_node, rows6472, irow6467, rows6473]
  all_goals rfl

theorem atot6467 : totK PD2M8K2 D2M8K2.u6467 = [100567748630, 603595455603, 797489598603, 299609999410, 25373788367, 0, 0, 0] := by
  rw [show D2M8K2.u6467 = KTree.node D2M8K2.t6472 (nat_lit 13981675) (nat_lit 1490263895) (nat_lit 0) D2M8K2.t6473 from rfl, totK_node, tot6472, tot6473]
  decide +kernel

theorem arows6468 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6468 = true := by
  rw [show D2M8K2.u6468 = KTree.node D2M8K2.t6474 (nat_lit 13982911) (nat_lit 2281222517) (nat_lit 0) D2M8K2.t6475 from rfl, allE_node, rows6474, irow6468, rows6475]
  all_goals rfl

theorem atot6468 : totK PD2M8K2 D2M8K2.u6468 = [174361741026, 585489487837, 754609930403, 295196616555, 12235609738, 0, 0, 0] := by
  rw [show D2M8K2.u6468 = KTree.node D2M8K2.t6474 (nat_lit 13982911) (nat_lit 2281222517) (nat_lit 0) D2M8K2.t6475 from rfl, totK_node, tot6474, tot6475]
  decide +kernel

theorem arows6470 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6470 = true := by
  rw [show D2M8K2.u6470 = KTree.node D2M8K2.t6476 (nat_lit 13984454) (nat_lit 4125996321) (nat_lit 0) D2M8K2.t6477 from rfl, allE_node, rows6476, irow6470, rows6477]
  all_goals rfl

theorem atot6470 : totK PD2M8K2 D2M8K2.u6470 = [241813634859, 810155347710, 658011175485, 106411749459, 1163840124, 0, 0, 0] := by
  rw [show D2M8K2.u6470 = KTree.node D2M8K2.t6476 (nat_lit 13984454) (nat_lit 4125996321) (nat_lit 0) D2M8K2.t6477 from rfl, totK_node, tot6476, tot6477]
  decide +kernel

theorem arows6471 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6471 = true := by
  rw [show D2M8K2.u6471 = KTree.node D2M8K2.t6478 (nat_lit 13986183) (nat_lit 3461015343) (nat_lit 0) D2M8K2.t6479 from rfl, allE_node, rows6478, irow6471, rows6479]
  all_goals rfl

theorem atot6471 : totK PD2M8K2 D2M8K2.u6471 = [150444073011, 622875913036, 783863578645, 227139071097, 11873025674, 0, 0, 0] := by
  rw [show D2M8K2.u6471 = KTree.node D2M8K2.t6478 (nat_lit 13986183) (nat_lit 3461015343) (nat_lit 0) D2M8K2.t6479 from rfl, totK_node, tot6478, tot6479]
  decide +kernel

theorem arows6475 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6475 = true := by
  rw [show D2M8K2.u6475 = KTree.node D2M8K2.t6480 (nat_lit 13987922) (nat_lit 3937420903) (nat_lit 0) D2M8K2.t6481 from rfl, allE_node, rows6480, irow6475, rows6481]
  all_goals rfl

theorem atot6475 : totK PD2M8K2 D2M8K2.u6475 = [230037813506, 809892070882, 662496514594, 107214304559, 1197396724, 0, 0, 0] := by
  rw [show D2M8K2.u6475 = KTree.node D2M8K2.t6480 (nat_lit 13987922) (nat_lit 3937420903) (nat_lit 0) D2M8K2.t6481 from rfl, totK_node, tot6480, tot6481]
  decide +kernel

theorem arows6476 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6476 = true := by
  rw [show D2M8K2.u6476 = KTree.node D2M8K2.t6482 (nat_lit 13989742) (nat_lit 4051426970) (nat_lit 0) D2M8K2.t6483 from rfl, allE_node, rows6482, irow6476, rows6483]
  all_goals rfl

theorem atot6476 : totK PD2M8K2 D2M8K2.u6476 = [194873206748, 645757666471, 719802002554, 221976632016, 12040273252, 0, 0, 0] := by
  rw [show D2M8K2.u6476 = KTree.node D2M8K2.t6482 (nat_lit 13989742) (nat_lit 4051426970) (nat_lit 0) D2M8K2.t6483 from rfl, totK_node, tot6482, tot6483]
  decide +kernel

theorem arows6478 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6478 = true := by
  rw [show D2M8K2.u6478 = KTree.node D2M8K2.t6484 (nat_lit 13991097) (nat_lit 1864447005) (nat_lit 0) D2M8K2.t6485 from rfl, allE_node, rows6484, irow6478, rows6485]
  all_goals rfl

theorem atot6478 : totK PD2M8K2 D2M8K2.u6478 = [227666444784, 797835271498, 663778262983, 99348897585, 1096156699, 0, 0, 0] := by
  rw [show D2M8K2.u6478 = KTree.node D2M8K2.t6484 (nat_lit 13991097) (nat_lit 1864447005) (nat_lit 0) D2M8K2.t6485 from rfl, totK_node, tot6484, tot6485]
  decide +kernel

theorem arows6479 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6479 = true := by
  rw [show D2M8K2.u6479 = KTree.node D2M8K2.t6486 (nat_lit 13993683) (nat_lit 3699729656) (nat_lit 0) D2M8K2.t6487 from rfl, allE_node, rows6486, irow6479, rows6487]
  all_goals rfl

theorem atot6479 : totK PD2M8K2 D2M8K2.u6479 = [196727694395, 724366210155, 757412848371, 153207445971, 3880716147, 0, 0, 0] := by
  rw [show D2M8K2.u6479 = KTree.node D2M8K2.t6486 (nat_lit 13993683) (nat_lit 3699729656) (nat_lit 0) D2M8K2.t6487 from rfl, totK_node, tot6486, tot6487]
  decide +kernel

theorem arows6482 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6482 = true := by
  rw [show D2M8K2.u6482 = KTree.node D2M8K2.t6488 (nat_lit 13995459) (nat_lit 3692386415) (nat_lit 0) D2M8K2.t6489 from rfl, allE_node, rows6488, irow6482, rows6489]
  all_goals rfl

theorem atot6482 : totK PD2M8K2 D2M8K2.u6482 = [132249069452, 665409364572, 810094559735, 211579087026, 6286513735, 0, 0, 0] := by
  rw [show D2M8K2.u6482 = KTree.node D2M8K2.t6488 (nat_lit 13995459) (nat_lit 3692386415) (nat_lit 0) D2M8K2.t6489 from rfl, totK_node, tot6488, tot6489]
  decide +kernel

theorem arows6483 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6483 = true := by
  rw [show D2M8K2.u6483 = KTree.node D2M8K2.t6490 (nat_lit 14000863) (nat_lit 1880718838) (nat_lit 0) D2M8K2.t6491 from rfl, allE_node, rows6490, irow6483, rows6491]
  all_goals rfl

theorem atot6483 : totK PD2M8K2 D2M8K2.u6483 = [0, 342249984050, 904571477435, 527852367290, 48211113594, 0, 0, 0] := by
  rw [show D2M8K2.u6483 = KTree.node D2M8K2.t6490 (nat_lit 14000863) (nat_lit 1880718838) (nat_lit 0) D2M8K2.t6491 from rfl, totK_node, tot6490, tot6491]
  decide +kernel

theorem arows6485 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6485 = true := by
  rw [show D2M8K2.u6485 = KTree.node D2M8K2.t6492 (nat_lit 14002365) (nat_lit 1432197053) (nat_lit 0) D2M8K2.t6493 from rfl, allE_node, rows6492, irow6485, rows6493]
  all_goals rfl

theorem atot6485 : totK PD2M8K2 D2M8K2.u6485 = [0, 136647621132, 624273918575, 749109610546, 282865248498, 25191558099, 0, 0] := by
  rw [show D2M8K2.u6485 = KTree.node D2M8K2.t6492 (nat_lit 14002365) (nat_lit 1432197053) (nat_lit 0) D2M8K2.t6493 from rfl, totK_node, tot6492, tot6493]
  decide +kernel

theorem arows6486 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6486 = true := by
  rw [show D2M8K2.u6486 = KTree.node D2M8K2.t6494 (nat_lit 14003599) (nat_lit 2081631633) (nat_lit 0) D2M8K2.t6495 from rfl, allE_node, rows6494, irow6486, rows6495]
  all_goals rfl

theorem atot6486 : totK PD2M8K2 D2M8K2.u6486 = [0, 157176254258, 585641017541, 761294968878, 277791517031, 11730315755, 0, 0] := by
  rw [show D2M8K2.u6486 = KTree.node D2M8K2.t6494 (nat_lit 14003599) (nat_lit 2081631633) (nat_lit 0) D2M8K2.t6495 from rfl, totK_node, tot6494, tot6495]
  decide +kernel

theorem arows6491 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6491 = true := by
  rw [show D2M8K2.u6491 = KTree.node D2M8K2.t6496 (nat_lit 14005124) (nat_lit 3609898978) (nat_lit 0) D2M8K2.t6497 from rfl, allE_node, rows6496, irow6491, rows6497]
  all_goals rfl

theorem atot6491 : totK PD2M8K2 D2M8K2.u6491 = [0, 258022049268, 866367431822, 633473175393, 60420341114, 0, 0, 0] := by
  rw [show D2M8K2.u6491 = KTree.node D2M8K2.t6496 (nat_lit 14005124) (nat_lit 3609898978) (nat_lit 0) D2M8K2.t6497 from rfl, totK_node, tot6496, tot6497]
  decide +kernel

theorem arows6492 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6492 = true := by
  rw [show D2M8K2.u6492 = KTree.node D2M8K2.t6498 (nat_lit 14007016) (nat_lit 3751168562) (nat_lit 0) D2M8K2.t6499 from rfl, allE_node, rows6498, irow6492, rows6499]
  all_goals rfl

theorem atot6492 : totK PD2M8K2 D2M8K2.u6492 = [0, 198679205628, 665517233539, 742374657529, 188355657279, 5159868635, 0, 0] := by
  rw [show D2M8K2.u6492 = KTree.node D2M8K2.t6498 (nat_lit 14007016) (nat_lit 3751168562) (nat_lit 0) D2M8K2.t6499 from rfl, totK_node, tot6498, tot6499]
  decide +kernel

theorem arows6494 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6494 = true := by
  rw [show D2M8K2.u6494 = KTree.node D2M8K2.t6500 (nat_lit 14008781) (nat_lit 1884071797) (nat_lit 0) D2M8K2.t6501 from rfl, allE_node, rows6500, irow6494, rows6501]
  all_goals rfl

theorem atot6494 : totK PD2M8K2 D2M8K2.u6494 = [0, 184415615032, 762968237814, 709688160036, 135400216535, 2926763925, 0, 0] := by
  rw [show D2M8K2.u6494 = KTree.node D2M8K2.t6500 (nat_lit 14008781) (nat_lit 1884071797) (nat_lit 0) D2M8K2.t6501 from rfl, totK_node, tot6500, tot6501]
  decide +kernel

theorem arows6495 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6495 = true := by
  rw [show D2M8K2.u6495 = KTree.node D2M8K2.t6502 (nat_lit 14010873) (nat_lit 1871520958) (nat_lit 0) D2M8K2.t6503 from rfl, allE_node, rows6502, irow6495, rows6503]
  all_goals rfl

theorem atot6495 : totK PD2M8K2 D2M8K2.u6495 = [0, 245342525399, 762655048198, 664044901418, 120266150406, 1186940923, 0, 0] := by
  rw [show D2M8K2.u6495 = KTree.node D2M8K2.t6502 (nat_lit 14010873) (nat_lit 1871520958) (nat_lit 0) D2M8K2.t6503 from rfl, totK_node, tot6502, tot6503]
  decide +kernel

theorem arows6498 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6498 = true := by
  rw [show D2M8K2.u6498 = KTree.node D2M8K2.t6504 (nat_lit 14012361) (nat_lit 1827098783) (nat_lit 0) D2M8K2.t6505 from rfl, allE_node, rows6504, irow6498, rows6505]
  all_goals rfl

theorem atot6498 : totK PD2M8K2 D2M8K2.u6498 = [0, 175803011529, 798580274852, 750979421894, 73853257241, 0, 0, 0] := by
  rw [show D2M8K2.u6498 = KTree.node D2M8K2.t6504 (nat_lit 14012361) (nat_lit 1827098783) (nat_lit 0) D2M8K2.t6505 from rfl, totK_node, tot6504, tot6505]
  decide +kernel

theorem arows6499 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6499 = true := by
  rw [show D2M8K2.u6499 = KTree.node D2M8K2.t6506 (nat_lit 14014694) (nat_lit 4125165185) (nat_lit 0) D2M8K2.t6507 from rfl, allE_node, rows6506, irow6499, rows6507]
  all_goals rfl

theorem atot6499 : totK PD2M8K2 D2M8K2.u6499 = [0, 328015090625, 819916061148, 589216266122, 109312952141, 1415142070, 0, 0] := by
  rw [show D2M8K2.u6499 = KTree.node D2M8K2.t6506 (nat_lit 14014694) (nat_lit 4125165185) (nat_lit 0) D2M8K2.t6507 from rfl, totK_node, tot6506, tot6507]
  decide +kernel

theorem arows6501 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6501 = true := by
  rw [show D2M8K2.u6501 = KTree.node D2M8K2.t6508 (nat_lit 14016718) (nat_lit 3909730644) (nat_lit 0) D2M8K2.t6509 from rfl, allE_node, rows6508, irow6501, rows6509]
  all_goals rfl

theorem atot6501 : totK PD2M8K2 D2M8K2.u6501 = [85882852960, 120506258462, 451209505812, 853545637635, 277291679837, 9302370699, 0, 0] := by
  rw [show D2M8K2.u6501 = KTree.node D2M8K2.t6508 (nat_lit 14016718) (nat_lit 3909730644) (nat_lit 0) D2M8K2.t6509 from rfl, totK_node, tot6508, tot6509]
  decide +kernel

theorem arows6502 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6502 = true := by
  rw [show D2M8K2.u6502 = KTree.node D2M8K2.t6510 (nat_lit 14018636) (nat_lit 3167254939) (nat_lit 0) D2M8K2.t6511 from rfl, allE_node, rows6510, irow6502, rows6511]
  all_goals rfl

theorem atot6502 : totK PD2M8K2 D2M8K2.u6502 = [321349472235, 919680259501, 502838972577, 30083536944, 0, 0, 0, 0] := by
  rw [show D2M8K2.u6502 = KTree.node D2M8K2.t6510 (nat_lit 14018636) (nat_lit 3167254939) (nat_lit 0) D2M8K2.t6511 from rfl, totK_node, tot6510, tot6511]
  decide +kernel

theorem arows6506 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6506 = true := by
  rw [show D2M8K2.u6506 = KTree.node D2M8K2.t6512 (nat_lit 14020461) (nat_lit 1389665779) (nat_lit 0) D2M8K2.t6513 from rfl, allE_node, rows6512, irow6506, rows6513]
  all_goals rfl

theorem atot6506 : totK PD2M8K2 D2M8K2.u6506 = [107477068962, 654629542892, 883770768068, 164621072838, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u6506 = KTree.node D2M8K2.t6512 (nat_lit 14020461) (nat_lit 1389665779) (nat_lit 0) D2M8K2.t6513 from rfl, totK_node, tot6512, tot6513]
  decide +kernel

theorem arows6507 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6507 = true := by
  rw [show D2M8K2.u6507 = KTree.node D2M8K2.t6514 (nat_lit 14022218) (nat_lit 4012383909) (nat_lit 0) D2M8K2.t6515 from rfl, allE_node, rows6514, irow6507, rows6515]
  all_goals rfl

theorem atot6507 : totK PD2M8K2 D2M8K2.u6507 = [311021439323, 908276415635, 558055826694, 52864344109, 0, 0, 0, 0] := by
  rw [show D2M8K2.u6507 = KTree.node D2M8K2.t6514 (nat_lit 14022218) (nat_lit 4012383909) (nat_lit 0) D2M8K2.t6515 from rfl, totK_node, tot6514, tot6515]
  decide +kernel

theorem arows6509 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6509 = true := by
  rw [show D2M8K2.u6509 = KTree.node D2M8K2.t6516 (nat_lit 14023757) (nat_lit 1631596836) (nat_lit 0) D2M8K2.t6517 from rfl, allE_node, rows6516, irow6509, rows6517]
  all_goals rfl

theorem atot6509 : totK PD2M8K2 D2M8K2.u6509 = [0, 332461342154, 937796946233, 504894725481, 32999474592, 0, 0, 0] := by
  rw [show D2M8K2.u6509 = KTree.node D2M8K2.t6516 (nat_lit 14023757) (nat_lit 1631596836) (nat_lit 0) D2M8K2.t6517 from rfl, totK_node, tot6516, tot6517]
  decide +kernel

theorem arows6510 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6510 = true := by
  rw [show D2M8K2.u6510 = KTree.node D2M8K2.t6518 (nat_lit 14025024) (nat_lit 3705351137) (nat_lit 0) D2M8K2.t6519 from rfl, allE_node, rows6518, irow6510, rows6519]
  all_goals rfl

theorem atot6510 : totK PD2M8K2 D2M8K2.u6510 = [373504498661, 927767256635, 470526774113, 50996595722, 4414412796, 0, 0, 0] := by
  rw [show D2M8K2.u6510 = KTree.node D2M8K2.t6518 (nat_lit 14025024) (nat_lit 3705351137) (nat_lit 0) D2M8K2.t6519 from rfl, totK_node, tot6518, tot6519]
  decide +kernel

theorem arows6513 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6513 = true := by
  rw [show D2M8K2.u6513 = KTree.node D2M8K2.t6520 (nat_lit 14026556) (nat_lit 3156080909) (nat_lit 0) D2M8K2.t6521 from rfl, allE_node, rows6520, irow6513, rows6521]
  all_goals rfl

theorem atot6513 : totK PD2M8K2 D2M8K2.u6513 = [67531417387, 550869773885, 910747204671, 260064124612, 10568566766, 0, 0, 0] := by
  rw [show D2M8K2.u6513 = KTree.node D2M8K2.t6520 (nat_lit 14026556) (nat_lit 3156080909) (nat_lit 0) D2M8K2.t6521 from rfl, totK_node, tot6520, tot6521]
  decide +kernel

theorem arows6514 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6514 = true := by
  rw [show D2M8K2.u6514 = KTree.node D2M8K2.t6522 (nat_lit 14031790) (nat_lit 3681874231) (nat_lit 0) D2M8K2.t6523 from rfl, allE_node, rows6522, irow6514, rows6523]
  all_goals rfl

theorem atot6514 : totK PD2M8K2 D2M8K2.u6514 = [332357677537, 878731898582, 534071598844, 72625194470, 2481160468, 0, 0, 0] := by
  rw [show D2M8K2.u6514 = KTree.node D2M8K2.t6522 (nat_lit 14031790) (nat_lit 3681874231) (nat_lit 0) D2M8K2.t6523 from rfl, totK_node, tot6522, tot6523]
  decide +kernel

theorem arows6516 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6516 = true := by
  rw [show D2M8K2.u6516 = KTree.node D2M8K2.t6524 (nat_lit 14033330) (nat_lit 3061431482) (nat_lit 0) D2M8K2.t6525 from rfl, allE_node, rows6524, irow6516, rows6525]
  all_goals rfl

theorem atot6516 : totK PD2M8K2 D2M8K2.u6516 = [91717090493, 686082088647, 875476382000, 142915949866, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u6516 = KTree.node D2M8K2.t6524 (nat_lit 14033330) (nat_lit 3061431482) (nat_lit 0) D2M8K2.t6525 from rfl, totK_node, tot6524, tot6525]
  decide +kernel

theorem arows6517 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6517 = true := by
  rw [show D2M8K2.u6517 = KTree.node D2M8K2.t6526 (nat_lit 14035304) (nat_lit 3469816882) (nat_lit 0) D2M8K2.t6527 from rfl, allE_node, rows6526, irow6517, rows6527]
  all_goals rfl

theorem atot6517 : totK PD2M8K2 D2M8K2.u6517 = [345616555263, 847794716490, 530771596669, 104260720046, 3884009855, 0, 0, 0] := by
  rw [show D2M8K2.u6517 = KTree.node D2M8K2.t6526 (nat_lit 14035304) (nat_lit 3469816882) (nat_lit 0) D2M8K2.t6527 from rfl, totK_node, tot6526, tot6527]
  decide +kernel

theorem arows6524 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6524 = true := by
  rw [show D2M8K2.u6524 = KTree.node D2M8K2.t6528 (nat_lit 14037216) (nat_lit 3274728506) (nat_lit 0) D2M8K2.t6529 from rfl, allE_node, rows6528, irow6524, rows6529]
  all_goals rfl

theorem atot6524 : totK PD2M8K2 D2M8K2.u6524 = [0, 471514933887, 971696336706, 334871079805, 18196433000, 0, 0, 0] := by
  rw [show D2M8K2.u6524 = KTree.node D2M8K2.t6528 (nat_lit 14037216) (nat_lit 3274728506) (nat_lit 0) D2M8K2.t6529 from rfl, totK_node, tot6528, tot6529]
  decide +kernel

theorem arows6525 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6525 = true := by
  rw [show D2M8K2.u6525 = KTree.node D2M8K2.t6530 (nat_lit 14039362) (nat_lit 2737086461) (nat_lit 0) D2M8K2.t6531 from rfl, allE_node, rows6530, irow6525, rows6531]
  all_goals rfl

theorem atot6525 : totK PD2M8K2 D2M8K2.u6525 = [0, 333286829844, 935965580421, 461407504569, 23682897265, 0, 0, 0] := by
  rw [show D2M8K2.u6525 = KTree.node D2M8K2.t6530 (nat_lit 14039362) (nat_lit 2737086461) (nat_lit 0) D2M8K2.t6531 from rfl, totK_node, tot6530, tot6531]
  decide +kernel

theorem arows6527 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6527 = true := by
  rw [show D2M8K2.u6527 = KTree.node D2M8K2.t6532 (nat_lit 14041252) (nat_lit 3771248344) (nat_lit 0) D2M8K2.t6533 from rfl, allE_node, rows6532, irow6527, rows6533]
  all_goals rfl

theorem atot6527 : totK PD2M8K2 D2M8K2.u6527 = [0, 163384141823, 712405677410, 777612050009, 117033596959, 1206465782, 0, 0] := by
  rw [show D2M8K2.u6527 = KTree.node D2M8K2.t6532 (nat_lit 14041252) (nat_lit 3771248344) (nat_lit 0) D2M8K2.t6533 from rfl, totK_node, tot6532, tot6533]
  decide +kernel

theorem arows6528 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6528 = true := by
  rw [show D2M8K2.u6528 = KTree.node D2M8K2.t6534 (nat_lit 14043098) (nat_lit 3968969184) (nat_lit 0) D2M8K2.t6535 from rfl, allE_node, rows6534, irow6528, rows6535]
  all_goals rfl

theorem atot6528 : totK PD2M8K2 D2M8K2.u6528 = [0, 354770345350, 954436578807, 464098592993, 26830698970, 0, 0, 0] := by
  rw [show D2M8K2.u6528 = KTree.node D2M8K2.t6534 (nat_lit 14043098) (nat_lit 3968969184) (nat_lit 0) D2M8K2.t6535 from rfl, totK_node, tot6534, tot6535]
  decide +kernel

theorem arows6531 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6531 = true := by
  rw [show D2M8K2.u6531 = KTree.node D2M8K2.t6536 (nat_lit 14046342) (nat_lit 3163810542) (nat_lit 0) D2M8K2.t6537 from rfl, allE_node, rows6536, irow6531, rows6537]
  all_goals rfl

theorem atot6531 : totK PD2M8K2 D2M8K2.u6531 = [0, 333558421726, 930657448619, 523780245545, 38418761094, 0, 0, 0] := by
  rw [show D2M8K2.u6531 = KTree.node D2M8K2.t6536 (nat_lit 14046342) (nat_lit 3163810542) (nat_lit 0) D2M8K2.t6537 from rfl, totK_node, tot6536, tot6537]
  decide +kernel

theorem arows6532 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6532 = true := by
  rw [show D2M8K2.u6532 = KTree.node D2M8K2.t6538 (nat_lit 14047741) (nat_lit 974488376) (nat_lit 0) D2M8K2.t6539 from rfl, allE_node, rows6538, irow6532, rows6539]
  all_goals rfl

theorem atot6532 : totK PD2M8K2 D2M8K2.u6532 = [0, 83655740246, 533027288627, 824849682867, 268638279219, 13016197374, 0, 0] := by
  rw [show D2M8K2.u6532 = KTree.node D2M8K2.t6538 (nat_lit 14047741) (nat_lit 974488376) (nat_lit 0) D2M8K2.t6539 from rfl, totK_node, tot6538, tot6539]
  decide +kernel

theorem arows6534 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6534 = true := by
  rw [show D2M8K2.u6534 = KTree.node D2M8K2.t6540 (nat_lit 14052873) (nat_lit 1759264913) (nat_lit 0) D2M8K2.t6541 from rfl, allE_node, rows6540, irow6534, rows6541]
  all_goals rfl

theorem atot6534 : totK PD2M8K2 D2M8K2.u6534 = [0, 338048248748, 948954488238, 486604726511, 27019206085, 0, 0, 0] := by
  rw [show D2M8K2.u6534 = KTree.node D2M8K2.t6540 (nat_lit 14052873) (nat_lit 1759264913) (nat_lit 0) D2M8K2.t6541 from rfl, totK_node, tot6540, tot6541]
  decide +kernel

theorem arows6535 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6535 = true := by
  rw [show D2M8K2.u6535 = KTree.node D2M8K2.t6542 (nat_lit 14054984) (nat_lit 3713827311) (nat_lit 0) D2M8K2.t6543 from rfl, allE_node, rows6542, irow6535, rows6543]
  all_goals rfl

theorem atot6535 : totK PD2M8K2 D2M8K2.u6535 = [0, 133190045769, 669048368379, 759427964699, 148658550426, 4574395652, 0, 0] := by
  rw [show D2M8K2.u6535 = KTree.node D2M8K2.t6542 (nat_lit 14054984) (nat_lit 3713827311) (nat_lit 0) D2M8K2.t6543 from rfl, totK_node, tot6542, tot6543]
  decide +kernel

theorem arows6539 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6539 = true := by
  rw [show D2M8K2.u6539 = KTree.node D2M8K2.t6544 (nat_lit 14057071) (nat_lit 1861731768) (nat_lit 0) D2M8K2.t6545 from rfl, allE_node, rows6544, irow6539, rows6545]
  all_goals rfl

theorem atot6539 : totK PD2M8K2 D2M8K2.u6539 = [155770311254, 549780766952, 697556033417, 381826890835, 38777357727, 0, 0, 0] := by
  rw [show D2M8K2.u6539 = KTree.node D2M8K2.t6544 (nat_lit 14057071) (nat_lit 1861731768) (nat_lit 0) D2M8K2.t6545 from rfl, totK_node, tot6544, tot6545]
  decide +kernel

theorem arows6540 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6540 = true := by
  rw [show D2M8K2.u6540 = KTree.node D2M8K2.t6546 (nat_lit 14060356) (nat_lit 3855340693) (nat_lit 0) D2M8K2.t6547 from rfl, allE_node, rows6546, irow6540, rows6547]
  all_goals rfl

theorem atot6540 : totK PD2M8K2 D2M8K2.u6540 = [239701068211, 768949102517, 640219964565, 110760577270, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u6540 = KTree.node D2M8K2.t6546 (nat_lit 14060356) (nat_lit 3855340693) (nat_lit 0) D2M8K2.t6547 from rfl, totK_node, tot6546, tot6547]
  decide +kernel

theorem arows6542 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6542 = true := by
  rw [show D2M8K2.u6542 = KTree.node D2M8K2.t6548 (nat_lit 14062825) (nat_lit 1189725006) (nat_lit 0) D2M8K2.t6549 from rfl, allE_node, rows6548, irow6542, rows6549]
  all_goals rfl

theorem atot6542 : totK PD2M8K2 D2M8K2.u6542 = [225003429251, 795921782873, 725158812350, 88439661786, 0, 0, 0, 0] := by
  rw [show D2M8K2.u6542 = KTree.node D2M8K2.t6548 (nat_lit 14062825) (nat_lit 1189725006) (nat_lit 0) D2M8K2.t6549 from rfl, totK_node, tot6548, tot6549]
  decide +kernel

theorem arows6543 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6543 = true := by
  rw [show D2M8K2.u6543 = KTree.node D2M8K2.t6550 (nat_lit 14064080) (nat_lit 3111655376) (nat_lit 0) D2M8K2.t6551 from rfl, allE_node, rows6550, irow6543, rows6551]
  all_goals rfl

theorem atot6543 : totK PD2M8K2 D2M8K2.u6543 = [178333478127, 702511728198, 692684565753, 229467218528, 21383147344, 0, 0, 0] := by
  rw [show D2M8K2.u6543 = KTree.node D2M8K2.t6550 (nat_lit 14064080) (nat_lit 3111655376) (nat_lit 0) D2M8K2.t6551 from rfl, totK_node, tot6550, tot6551]
  decide +kernel

theorem arows6546 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6546 = true := by
  rw [show D2M8K2.u6546 = KTree.node D2M8K2.t6552 (nat_lit 14065661) (nat_lit 2074116301) (nat_lit 0) D2M8K2.t6553 from rfl, allE_node, rows6552, irow6546, rows6553]
  all_goals rfl

theorem atot6546 : totK PD2M8K2 D2M8K2.u6546 = [147289589861, 548700536477, 753335021766, 338733138715, 16179348042, 0, 0, 0] := by
  rw [show D2M8K2.u6546 = KTree.node D2M8K2.t6552 (nat_lit 14065661) (nat_lit 2074116301) (nat_lit 0) D2M8K2.t6553 from rfl, totK_node, tot6552, tot6553]
  decide +kernel

theorem arows6547 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6547 = true := by
  rw [show D2M8K2.u6547 = KTree.node D2M8K2.t6554 (nat_lit 14070588) (nat_lit 3003383203) (nat_lit 0) D2M8K2.t6555 from rfl, allE_node, rows6554, irow6547, rows6555]
  all_goals rfl

theorem atot6547 : totK PD2M8K2 D2M8K2.u6547 = [278655930135, 868483076810, 611229461950, 60405975114, 0, 0, 0, 0] := by
  rw [show D2M8K2.u6547 = KTree.node D2M8K2.t6554 (nat_lit 14070588) (nat_lit 3003383203) (nat_lit 0) D2M8K2.t6555 from rfl, totK_node, tot6554, tot6555]
  decide +kernel

theorem arows6549 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6549 = true := by
  rw [show D2M8K2.u6549 = KTree.node D2M8K2.t6556 (nat_lit 14072294) (nat_lit 4113698729) (nat_lit 0) D2M8K2.t6557 from rfl, allE_node, rows6556, irow6549, rows6557]
  all_goals rfl

theorem atot6549 : totK PD2M8K2 D2M8K2.u6549 = [83817468306, 542157602443, 848522215811, 285917431485, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u6549 = KTree.node D2M8K2.t6556 (nat_lit 14072294) (nat_lit 4113698729) (nat_lit 0) D2M8K2.t6557 from rfl, totK_node, tot6556, tot6557]
  decide +kernel

theorem arows6550 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6550 = true := by
  rw [show D2M8K2.u6550 = KTree.node D2M8K2.t6558 (nat_lit 14073708) (nat_lit 3550354764) (nat_lit 0) D2M8K2.t6559 from rfl, allE_node, rows6558, irow6550, rows6559]
  all_goals rfl

theorem atot6550 : totK PD2M8K2 D2M8K2.u6550 = [339499945003, 907568807869, 528370054673, 44031587685, 0, 0, 0, 0] := by
  rw [show D2M8K2.u6550 = KTree.node D2M8K2.t6558 (nat_lit 14073708) (nat_lit 3550354764) (nat_lit 0) D2M8K2.t6559 from rfl, totK_node, tot6558, tot6559]
  decide +kernel

theorem arows6555 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6555 = true := by
  rw [show D2M8K2.u6555 = KTree.node D2M8K2.t6560 (nat_lit 14075533) (nat_lit 1111426424) (nat_lit 0) D2M8K2.t6561 from rfl, allE_node, rows6560, irow6555, rows6561]
  all_goals rfl

theorem atot6555 : totK PD2M8K2 D2M8K2.u6555 = [0, 490851793369, 1007709512042, 283144195791, 6350335412, 0, 0, 0] := by
  rw [show D2M8K2.u6555 = KTree.node D2M8K2.t6560 (nat_lit 14075533) (nat_lit 1111426424) (nat_lit 0) D2M8K2.t6561 from rfl, totK_node, tot6560, tot6561]
  decide +kernel

theorem arows6556 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6556 = true := by
  rw [show D2M8K2.u6556 = KTree.node D2M8K2.t6562 (nat_lit 14080988) (nat_lit 3395784958) (nat_lit 0) D2M8K2.t6563 from rfl, allE_node, rows6562, irow6556, rows6563]
  all_goals rfl

theorem atot6556 : totK PD2M8K2 D2M8K2.u6556 = [0, 286830025887, 846585316693, 533065277327, 66108080676, 1239866073, 0, 0] := by
  rw [show D2M8K2.u6556 = KTree.node D2M8K2.t6562 (nat_lit 14080988) (nat_lit 3395784958) (nat_lit 0) D2M8K2.t6563 from rfl, totK_node, tot6562, tot6563]
  decide +kernel

theorem arows6558 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6558 = true := by
  rw [show D2M8K2.u6558 = KTree.node D2M8K2.t6564 (nat_lit 14083541) (nat_lit 2301653355) (nat_lit 0) D2M8K2.t6565 from rfl, allE_node, rows6564, irow6558, rows6565]
  all_goals rfl

theorem atot6558 : totK PD2M8K2 D2M8K2.u6558 = [0, 214201130611, 790177102643, 717687354038, 81860011703, 0, 0, 0] := by
  rw [show D2M8K2.u6558 = KTree.node D2M8K2.t6564 (nat_lit 14083541) (nat_lit 2301653355) (nat_lit 0) D2M8K2.t6565 from rfl, totK_node, tot6564, tot6565]
  decide +kernel

theorem arows6559 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6559 = true := by
  rw [show D2M8K2.u6559 = KTree.node D2M8K2.t6566 (nat_lit 14084812) (nat_lit 3649246224) (nat_lit 0) D2M8K2.t6567 from rfl, allE_node, rows6566, irow6559, rows6567]
  all_goals rfl

theorem atot6559 : totK PD2M8K2 D2M8K2.u6559 = [0, 363046399324, 948057852851, 458387075495, 33357897877, 0, 0, 0] := by
  rw [show D2M8K2.u6559 = KTree.node D2M8K2.t6566 (nat_lit 14084812) (nat_lit 3649246224) (nat_lit 0) D2M8K2.t6567 from rfl, totK_node, tot6566, tot6567]
  decide +kernel

theorem arows6562 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6562 = true := by
  rw [show D2M8K2.u6562 = KTree.node D2M8K2.t6568 (nat_lit 14091460) (nat_lit 2860860657) (nat_lit 0) D2M8K2.t6569 from rfl, allE_node, rows6568, irow6562, rows6569]
  all_goals rfl

theorem atot6562 : totK PD2M8K2 D2M8K2.u6562 = [0, 252278565868, 797740048218, 630502434239, 98780346048, 1171084559, 0, 0] := by
  rw [show D2M8K2.u6562 = KTree.node D2M8K2.t6568 (nat_lit 14091460) (nat_lit 2860860657) (nat_lit 0) D2M8K2.t6569 from rfl, totK_node, tot6568, tot6569]
  decide +kernel

theorem arows6563 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6563 = true := by
  rw [show D2M8K2.u6563 = KTree.node D2M8K2.t6570 (nat_lit 14093192) (nat_lit 3292353196) (nat_lit 0) D2M8K2.t6571 from rfl, allE_node, rows6570, irow6563, rows6571]
  all_goals rfl

theorem atot6563 : totK PD2M8K2 D2M8K2.u6563 = [0, 170388669167, 648011775024, 711919850517, 207002149325, 11934365838, 0, 0] := by
  rw [show D2M8K2.u6563 = KTree.node D2M8K2.t6570 (nat_lit 14093192) (nat_lit 3292353196) (nat_lit 0) D2M8K2.t6571 from rfl, totK_node, tot6570, tot6571]
  decide +kernel

theorem arows6565 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6565 = true := by
  rw [show D2M8K2.u6565 = KTree.node D2M8K2.t6572 (nat_lit 14094670) (nat_lit 2990193415) (nat_lit 0) D2M8K2.t6573 from rfl, allE_node, rows6572, irow6565, rows6573]
  all_goals rfl

theorem atot6565 : totK PD2M8K2 D2M8K2.u6565 = [0, 250611642998, 822946587590, 616837649651, 77056698599, 1053411165, 0, 0] := by
  rw [show D2M8K2.u6565 = KTree.node D2M8K2.t6572 (nat_lit 14094670) (nat_lit 2990193415) (nat_lit 0) D2M8K2.t6573 from rfl, totK_node, tot6572, tot6573]
  decide +kernel

theorem arows6566 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6566 = true := by
  rw [show D2M8K2.u6566 = KTree.node D2M8K2.t6574 (nat_lit 14096691) (nat_lit 2348208907) (nat_lit 0) D2M8K2.t6575 from rfl, allE_node, rows6574, irow6566, rows6575]
  all_goals rfl

theorem atot6566 : totK PD2M8K2 D2M8K2.u6566 = [190180602404, 455678971639, 503898675309, 497169143655, 103146744381, 3667207281, 0, 0] := by
  rw [show D2M8K2.u6566 = KTree.node D2M8K2.t6574 (nat_lit 14096691) (nat_lit 2348208907) (nat_lit 0) D2M8K2.t6575 from rfl, totK_node, tot6574, tot6575]
  decide +kernel

theorem arows6570 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6570 = true := by
  rw [show D2M8K2.u6570 = KTree.node D2M8K2.t6576 (nat_lit 14101984) (nat_lit 3719324835) (nat_lit 0) D2M8K2.t6577 from rfl, allE_node, rows6576, irow6570, rows6577]
  all_goals rfl

theorem atot6570 : totK PD2M8K2 D2M8K2.u6570 = [218460259695, 768450367785, 662265785784, 112707080292, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u6570 = KTree.node D2M8K2.t6576 (nat_lit 14101984) (nat_lit 3719324835) (nat_lit 0) D2M8K2.t6577 from rfl, totK_node, tot6576, tot6577]
  decide +kernel

theorem arows6571 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6571 = true := by
  rw [show D2M8K2.u6571 = KTree.node D2M8K2.t6578 (nat_lit 14104356) (nat_lit 2026572333) (nat_lit 0) D2M8K2.t6579 from rfl, allE_node, rows6578, irow6571, rows6579]
  all_goals rfl

theorem atot6571 : totK PD2M8K2 D2M8K2.u6571 = [251558702660, 806380406759, 681340687429, 80464365825, 0, 0, 0, 0] := by
  rw [show D2M8K2.u6571 = KTree.node D2M8K2.t6578 (nat_lit 14104356) (nat_lit 2026572333) (nat_lit 0) D2M8K2.t6579 from rfl, totK_node, tot6578, tot6579]
  decide +kernel

theorem arows6573 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6573 = true := by
  rw [show D2M8K2.u6573 = KTree.node D2M8K2.t6580 (nat_lit 14105579) (nat_lit 2660434663) (nat_lit 0) D2M8K2.t6581 from rfl, allE_node, rows6580, irow6573, rows6581]
  all_goals rfl

theorem atot6573 : totK PD2M8K2 D2M8K2.u6573 = [171162320902, 694013732836, 704962273658, 223152030498, 21383112939, 0, 0, 0] := by
  rw [show D2M8K2.u6573 = KTree.node D2M8K2.t6580 (nat_lit 14105579) (nat_lit 2660434663) (nat_lit 0) D2M8K2.t6581 from rfl, totK_node, tot6580, tot6581]
  decide +kernel

theorem arows6574 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6574 = true := by
  rw [show D2M8K2.u6574 = KTree.node D2M8K2.t6582 (nat_lit 14107061) (nat_lit 2207012575) (nat_lit 0) D2M8K2.t6583 from rfl, allE_node, rows6582, irow6574, rows6583]
  all_goals rfl

theorem atot6574 : totK PD2M8K2 D2M8K2.u6574 = [134574193550, 524042518978, 767119355322, 346693154732, 16027373390, 0, 0, 0] := by
  rw [show D2M8K2.u6574 = KTree.node D2M8K2.t6582 (nat_lit 14107061) (nat_lit 2207012575) (nat_lit 0) D2M8K2.t6583 from rfl, totK_node, tot6582, tot6583]
  decide +kernel

theorem arows6577 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6577 = true := by
  rw [show D2M8K2.u6577 = KTree.node D2M8K2.t6584 (nat_lit 14108587) (nat_lit 1741435924) (nat_lit 0) D2M8K2.t6585 from rfl, allE_node, rows6584, irow6577, rows6585]
  all_goals rfl

theorem atot6577 : totK PD2M8K2 D2M8K2.u6577 = [287161750851, 878972608997, 595176796150, 55121273805, 0, 0, 0, 0] := by
  rw [show D2M8K2.u6577 = KTree.node D2M8K2.t6584 (nat_lit 14108587) (nat_lit 1741435924) (nat_lit 0) D2M8K2.t6585 from rfl, totK_node, tot6584, tot6585]
  decide +kernel

theorem arows6578 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6578 = true := by
  rw [show D2M8K2.u6578 = KTree.node D2M8K2.t6586 (nat_lit 14110306) (nat_lit 3225469000) (nat_lit 0) D2M8K2.t6587 from rfl, allE_node, rows6586, irow6578, rows6587]
  all_goals rfl

theorem atot6578 : totK PD2M8K2 D2M8K2.u6578 = [83129224478, 541614666231, 850856960644, 276448674151, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u6578 = KTree.node D2M8K2.t6586 (nat_lit 14110306) (nat_lit 3225469000) (nat_lit 0) D2M8K2.t6587 from rfl, totK_node, tot6586, tot6587]
  decide +kernel

theorem arows6580 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6580 = true := by
  rw [show D2M8K2.u6580 = KTree.node D2M8K2.t6588 (nat_lit 14111966) (nat_lit 2505776672) (nat_lit 0) D2M8K2.t6589 from rfl, allE_node, rows6588, irow6580, rows6589]
  all_goals rfl

theorem atot6580 : totK PD2M8K2 D2M8K2.u6580 = [317991257933, 884192960096, 559240943847, 46743125899, 0, 0, 0, 0] := by
  rw [show D2M8K2.u6580 = KTree.node D2M8K2.t6588 (nat_lit 14111966) (nat_lit 2505776672) (nat_lit 0) D2M8K2.t6589 from rfl, totK_node, tot6588, tot6589]
  decide +kernel

theorem arows6581 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6581 = true := by
  rw [show D2M8K2.u6581 = KTree.node D2M8K2.t6590 (nat_lit 14113734) (nat_lit 3738511779) (nat_lit 0) D2M8K2.t6591 from rfl, allE_node, rows6590, irow6581, rows6591]
  all_goals rfl

theorem atot6581 : totK PD2M8K2 D2M8K2.u6581 = [86527685341, 535141749288, 833313771438, 285318063452, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u6581 = KTree.node D2M8K2.t6590 (nat_lit 14113734) (nat_lit 3738511779) (nat_lit 0) D2M8K2.t6591 from rfl, totK_node, tot6590, tot6591]
  decide +kernel

theorem arows6587 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6587 = true := by
  rw [show D2M8K2.u6587 = KTree.node D2M8K2.t6592 (nat_lit 14115132) (nat_lit 2756610414) (nat_lit 0) D2M8K2.t6593 from rfl, allE_node, rows6592, irow6587, rows6593]
  all_goals rfl

theorem atot6587 : totK PD2M8K2 D2M8K2.u6587 = [357800183586, 929804467799, 512064741779, 41065759987, 0, 0, 0, 0] := by
  rw [show D2M8K2.u6587 = KTree.node D2M8K2.t6592 (nat_lit 14115132) (nat_lit 2756610414) (nat_lit 0) D2M8K2.t6593 from rfl, totK_node, tot6592, tot6593]
  decide +kernel

theorem arows6588 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6588 = true := by
  rw [show D2M8K2.u6588 = KTree.node D2M8K2.t6594 (nat_lit 14116929) (nat_lit 1825578435) (nat_lit 0) D2M8K2.t6595 from rfl, allE_node, rows6594, irow6588, rows6595]
  all_goals rfl

theorem atot6588 : totK PD2M8K2 D2M8K2.u6588 = [0, 528843053659, 1018646676924, 258567030698, 6350335412, 0, 0, 0] := by
  rw [show D2M8K2.u6588 = KTree.node D2M8K2.t6594 (nat_lit 14116929) (nat_lit 1825578435) (nat_lit 0) D2M8K2.t6595 from rfl, totK_node, tot6594, tot6595]
  decide +kernel

theorem arows6590 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6590 = true := by
  rw [show D2M8K2.u6590 = KTree.node D2M8K2.t6596 (nat_lit 14122332) (nat_lit 2814470669) (nat_lit 0) D2M8K2.t6597 from rfl, allE_node, rows6596, irow6590, rows6597]
  all_goals rfl

theorem atot6590 : totK PD2M8K2 D2M8K2.u6590 = [0, 320666310267, 916138154219, 468681062323, 29322472901, 0, 0, 0] := by
  rw [show D2M8K2.u6590 = KTree.node D2M8K2.t6596 (nat_lit 14122332) (nat_lit 2814470669) (nat_lit 0) D2M8K2.t6597 from rfl, totK_node, tot6596, tot6597]
  decide +kernel

theorem arows6591 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6591 = true := by
  rw [show D2M8K2.u6591 = KTree.node D2M8K2.t6598 (nat_lit 14124435) (nat_lit 1951740053) (nat_lit 0) D2M8K2.t6599 from rfl, allE_node, rows6598, irow6591, rows6599]
  all_goals rfl

theorem atot6591 : totK PD2M8K2 D2M8K2.u6591 = [0, 180027324132, 768186507000, 715237681734, 101485654270, 1138244013, 0, 0] := by
  rw [show D2M8K2.u6591 = KTree.node D2M8K2.t6598 (nat_lit 14124435) (nat_lit 1951740053) (nat_lit 0) D2M8K2.t6599 from rfl, totK_node, tot6598, tot6599]
  decide +kernel

theorem arows6594 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6594 = true := by
  rw [show D2M8K2.u6594 = KTree.node D2M8K2.t6600 (nat_lit 14126085) (nat_lit 1724325064) (nat_lit 0) D2M8K2.t6601 from rfl, allE_node, rows6600, irow6594, rows6601]
  all_goals rfl

theorem atot6594 : totK PD2M8K2 D2M8K2.u6594 = [0, 381418504068, 951496215194, 428936477316, 24378528615, 0, 0, 0] := by
  rw [show D2M8K2.u6594 = KTree.node D2M8K2.t6600 (nat_lit 14126085) (nat_lit 1724325064) (nat_lit 0) D2M8K2.t6601 from rfl, totK_node, tot6600, tot6601]
  decide +kernel

theorem arows6595 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6595 = true := by
  rw [show D2M8K2.u6595 = KTree.node D2M8K2.t6602 (nat_lit 14129355) (nat_lit 2983446240) (nat_lit 0) D2M8K2.t6603 from rfl, allE_node, rows6602, irow6595, rows6603]
  all_goals rfl

theorem atot6595 : totK PD2M8K2 D2M8K2.u6595 = [0, 358574627237, 937091731301, 466443691382, 27178324774, 0, 0, 0] := by
  rw [show D2M8K2.u6595 = KTree.node D2M8K2.t6602 (nat_lit 14129355) (nat_lit 2983446240) (nat_lit 0) D2M8K2.t6603 from rfl, totK_node, tot6602, tot6603]
  decide +kernel

theorem arows6597 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6597 = true := by
  rw [show D2M8K2.u6597 = KTree.node D2M8K2.t6604 (nat_lit 14132692) (nat_lit 2695919224) (nat_lit 0) D2M8K2.t6605 from rfl, allE_node, rows6604, irow6597, rows6605]
  all_goals rfl

theorem atot6597 : totK PD2M8K2 D2M8K2.u6597 = [0, 374509154408, 938725014230, 454203668405, 26022874940, 0, 0, 0] := by
  rw [show D2M8K2.u6597 = KTree.node D2M8K2.t6604 (nat_lit 14132692) (nat_lit 2695919224) (nat_lit 0) D2M8K2.t6605 from rfl, totK_node, tot6604, tot6605]
  decide +kernel

theorem arows6598 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6598 = true := by
  rw [show D2M8K2.u6598 = KTree.node D2M8K2.t6606 (nat_lit 14135737) (nat_lit 1379807490) (nat_lit 0) D2M8K2.t6607 from rfl, allE_node, rows6606, irow6598, rows6607]
  all_goals rfl

theorem atot6598 : totK PD2M8K2 D2M8K2.u6598 = [0, 380945934002, 933118559651, 450956606801, 32547243808, 0, 0, 0] := by
  rw [show D2M8K2.u6598 = KTree.node D2M8K2.t6606 (nat_lit 14135737) (nat_lit 1379807490) (nat_lit 0) D2M8K2.t6607 from rfl, totK_node, tot6606, tot6607]
  decide +kernel

theorem arows6602 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6602 = true := by
  rw [show D2M8K2.u6602 = KTree.node D2M8K2.t6608 (nat_lit 14137409) (nat_lit 2137554277) (nat_lit 0) D2M8K2.t6609 from rfl, allE_node, rows6608, irow6602, rows6609]
  all_goals rfl

theorem atot6602 : totK PD2M8K2 D2M8K2.u6602 = [0, 73602475273, 641227010613, 836877230839, 192215148162, 4977114383, 0, 0] := by
  rw [show D2M8K2.u6602 = KTree.node D2M8K2.t6608 (nat_lit 14137409) (nat_lit 2137554277) (nat_lit 0) D2M8K2.t6609 from rfl, totK_node, tot6608, tot6609]
  decide +kernel

theorem arows6603 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6603 = true := by
  rw [show D2M8K2.u6603 = KTree.node D2M8K2.t6610 (nat_lit 14184437) (nat_lit 1207706529) (nat_lit 0) D2M8K2.t6611 from rfl, allE_node, rows6610, irow6603, rows6611]
  all_goals rfl

theorem atot6603 : totK PD2M8K2 D2M8K2.u6603 = [0, 358766785396, 940936905996, 456573738726, 23648084212, 0, 0, 0] := by
  rw [show D2M8K2.u6603 = KTree.node D2M8K2.t6610 (nat_lit 14184437) (nat_lit 1207706529) (nat_lit 0) D2M8K2.t6611 from rfl, totK_node, tot6610, tot6611]
  decide +kernel

theorem arows6605 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6605 = true := by
  rw [show D2M8K2.u6605 = KTree.node D2M8K2.t6612 (nat_lit 14186114) (nat_lit 3585991538) (nat_lit 0) D2M8K2.t6613 from rfl, allE_node, rows6612, irow6605, rows6613]
  all_goals rfl

theorem atot6605 : totK PD2M8K2 D2M8K2.u6605 = [0, 87164153352, 671274670220, 876141264402, 151573156072, 1369150432, 0, 0] := by
  rw [show D2M8K2.u6605 = KTree.node D2M8K2.t6612 (nat_lit 14186114) (nat_lit 3585991538) (nat_lit 0) D2M8K2.t6613 from rfl, totK_node, tot6612, tot6613]
  decide +kernel

theorem arows6606 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6606 = true := by
  rw [show D2M8K2.u6606 = KTree.node D2M8K2.t6614 (nat_lit 14191516) (nat_lit 3825358501) (nat_lit 0) D2M8K2.t6615 from rfl, allE_node, rows6614, irow6606, rows6615]
  all_goals rfl

theorem atot6606 : totK PD2M8K2 D2M8K2.u6606 = [0, 325084448712, 901097496724, 540773615730, 39924036123, 0, 0, 0] := by
  rw [show D2M8K2.u6606 = KTree.node D2M8K2.t6614 (nat_lit 14191516) (nat_lit 3825358501) (nat_lit 0) D2M8K2.t6615 from rfl, totK_node, tot6614, tot6615]
  decide +kernel

theorem arows6609 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6609 = true := by
  rw [show D2M8K2.u6609 = KTree.node D2M8K2.t6616 (nat_lit 14193244) (nat_lit 3820390304) (nat_lit 0) D2M8K2.t6617 from rfl, allE_node, rows6616, irow6609, rows6617]
  all_goals rfl

theorem atot6609 : totK PD2M8K2 D2M8K2.u6609 = [0, 86311067613, 545710990956, 858038871031, 254807829503, 12983449796, 0, 0] := by
  rw [show D2M8K2.u6609 = KTree.node D2M8K2.t6616 (nat_lit 14193244) (nat_lit 3820390304) (nat_lit 0) D2M8K2.t6617 from rfl, totK_node, tot6616, tot6617]
  decide +kernel

theorem arows6610 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6610 = true := by
  rw [show D2M8K2.u6610 = KTree.node D2M8K2.t6618 (nat_lit 14194997) (nat_lit 2316623341) (nat_lit 0) D2M8K2.t6619 from rfl, allE_node, rows6618, irow6610, rows6619]
  all_goals rfl

theorem atot6610 : totK PD2M8K2 D2M8K2.u6610 = [0, 292946501147, 858110579840, 568912615759, 58726978244, 1198073392, 0, 0] := by
  rw [show D2M8K2.u6610 = KTree.node D2M8K2.t6618 (nat_lit 14194997) (nat_lit 2316623341) (nat_lit 0) D2M8K2.t6619 from rfl, totK_node, tot6618, tot6619]
  decide +kernel

theorem arows6612 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6612 = true := by
  rw [show D2M8K2.u6612 = KTree.node D2M8K2.t6620 (nat_lit 14196782) (nat_lit 3609193263) (nat_lit 0) D2M8K2.t6621 from rfl, allE_node, rows6620, irow6612, rows6621]
  all_goals rfl

theorem atot6612 : totK PD2M8K2 D2M8K2.u6612 = [0, 147341817518, 595889441768, 771372609604, 234207395160, 11986244008, 0, 0] := by
  rw [show D2M8K2.u6612 = KTree.node D2M8K2.t6620 (nat_lit 14196782) (nat_lit 3609193263) (nat_lit 0) D2M8K2.t6621 from rfl, totK_node, tot6620, tot6621]
  decide +kernel

theorem arows6613 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6613 = true := by
  rw [show D2M8K2.u6613 = KTree.node D2M8K2.t6622 (nat_lit 14198251) (nat_lit 1616193789) (nat_lit 0) D2M8K2.t6623 from rfl, allE_node, rows6622, irow6613, rows6623]
  all_goals rfl

theorem atot6613 : totK PD2M8K2 D2M8K2.u6613 = [0, 271904396197, 843284883594, 586107875613, 69771693217, 1096505104, 0, 0] := by
  rw [show D2M8K2.u6613 = KTree.node D2M8K2.t6622 (nat_lit 14198251) (nat_lit 1616193789) (nat_lit 0) D2M8K2.t6623 from rfl, totK_node, tot6622, tot6623]
  decide +kernel

theorem arows6618 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6618 = true := by
  rw [show D2M8K2.u6618 = KTree.node D2M8K2.t6624 (nat_lit 14200202) (nat_lit 3915032381) (nat_lit 0) D2M8K2.t6625 from rfl, allE_node, rows6624, irow6618, rows6625]
  all_goals rfl

theorem atot6618 : totK PD2M8K2 D2M8K2.u6618 = [0, 170310974658, 688892325425, 766813210097, 163654150152, 3884009855, 0, 0] := by
  rw [show D2M8K2.u6618 = KTree.node D2M8K2.t6624 (nat_lit 14200202) (nat_lit 3915032381) (nat_lit 0) D2M8K2.t6625 from rfl, totK_node, tot6624, tot6625]
  decide +kernel

theorem arows6619 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6619 = true := by
  rw [show D2M8K2.u6619 = KTree.node D2M8K2.t6626 (nat_lit 14202413) (nat_lit 2146329069) (nat_lit 0) D2M8K2.t6627 from rfl, allE_node, rows6626, irow6619, rows6627]
  all_goals rfl

theorem atot6619 : totK PD2M8K2 D2M8K2.u6619 = [0, 155260542918, 734634679172, 776918786652, 119153390523, 1268739303, 0, 0] := by
  rw [show D2M8K2.u6619 = KTree.node D2M8K2.t6626 (nat_lit 14202413) (nat_lit 2146329069) (nat_lit 0) D2M8K2.t6627 from rfl, totK_node, tot6626, tot6627]
  decide +kernel

theorem arows6621 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6621 = true := by
  rw [show D2M8K2.u6621 = KTree.node D2M8K2.t6628 (nat_lit 14204976) (nat_lit 3384481187) (nat_lit 0) D2M8K2.t6629 from rfl, allE_node, rows6628, irow6621, rows6629]
  all_goals rfl

theorem atot6621 : totK PD2M8K2 D2M8K2.u6621 = [0, 0, 400713072162, 945981988701, 376578856837, 21700671950, 0, 0] := by
  rw [show D2M8K2.u6621 = KTree.node D2M8K2.t6628 (nat_lit 14204976) (nat_lit 3384481187) (nat_lit 0) D2M8K2.t6629 from rfl, totK_node, tot6628, tot6629]
  decide +kernel

theorem arows6622 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6622 = true := by
  rw [show D2M8K2.u6622 = KTree.node D2M8K2.t6630 (nat_lit 14206753) (nat_lit 1561875799) (nat_lit 0) D2M8K2.t6631 from rfl, allE_node, rows6630, irow6622, rows6631]
  all_goals rfl

theorem atot6622 : totK PD2M8K2 D2M8K2.u6622 = [0, 0, 160152446918, 795763737602, 649971336173, 89192188340, 1209030869, 0] := by
  rw [show D2M8K2.u6622 = KTree.node D2M8K2.t6630 (nat_lit 14206753) (nat_lit 1561875799) (nat_lit 0) D2M8K2.t6631 from rfl, totK_node, tot6630, tot6631]
  decide +kernel

theorem arows6625 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6625 = true := by
  rw [show D2M8K2.u6625 = KTree.node D2M8K2.t6632 (nat_lit 14212376) (nat_lit 3608818374) (nat_lit 0) D2M8K2.t6633 from rfl, allE_node, rows6632, irow6625, rows6633]
  all_goals rfl

theorem atot6625 : totK PD2M8K2 D2M8K2.u6625 = [0, 0, 471191524895, 967877952940, 321571320941, 13546715223, 0, 0] := by
  rw [show D2M8K2.u6625 = KTree.node D2M8K2.t6632 (nat_lit 14212376) (nat_lit 3608818374) (nat_lit 0) D2M8K2.t6633 from rfl, totK_node, tot6632, tot6633]
  decide +kernel

theorem arows6626 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6626 = true := by
  rw [show D2M8K2.u6626 = KTree.node D2M8K2.t6634 (nat_lit 14216043) (nat_lit 3041623246) (nat_lit 0) D2M8K2.t6635 from rfl, allE_node, rows6634, irow6626, rows6635]
  all_goals rfl

theorem atot6626 : totK PD2M8K2 D2M8K2.u6626 = [0, 0, 415873307730, 957849604189, 361023658392, 15025956817, 0, 0] := by
  rw [show D2M8K2.u6626 = KTree.node D2M8K2.t6634 (nat_lit 14216043) (nat_lit 3041623246) (nat_lit 0) D2M8K2.t6635 from rfl, totK_node, tot6634, tot6635]
  decide +kernel

theorem arows6628 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6628 = true := by
  rw [show D2M8K2.u6628 = KTree.node D2M8K2.t6636 (nat_lit 14219214) (nat_lit 4003271712) (nat_lit 0) D2M8K2.t6637 from rfl, allE_node, rows6636, irow6628, rows6637]
  all_goals rfl

theorem atot6628 : totK PD2M8K2 D2M8K2.u6628 = [0, 0, 411968957959, 940866419651, 374481288340, 21916172627, 0, 0] := by
  rw [show D2M8K2.u6628 = KTree.node D2M8K2.t6636 (nat_lit 14219214) (nat_lit 4003271712) (nat_lit 0) D2M8K2.t6637 from rfl, totK_node, tot6636, tot6637]
  decide +kernel

theorem arows6629 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6629 = true := by
  rw [show D2M8K2.u6629 = KTree.node D2M8K2.t6638 (nat_lit 14228955) (nat_lit 3765844345) (nat_lit 0) D2M8K2.t6639 from rfl, allE_node, rows6638, irow6629, rows6639]
  all_goals rfl

theorem atot6629 : totK PD2M8K2 D2M8K2.u6629 = [0, 301804903204, 865256204565, 609175919973, 68859682301, 0, 0, 0] := by
  rw [show D2M8K2.u6629 = KTree.node D2M8K2.t6638 (nat_lit 14228955) (nat_lit 3765844345) (nat_lit 0) D2M8K2.t6639 from rfl, totK_node, tot6638, tot6639]
  decide +kernel

theorem arows6633 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6633 = true := by
  rw [show D2M8K2.u6633 = KTree.node D2M8K2.t6640 (nat_lit 14230452) (nat_lit 2549989323) (nat_lit 0) D2M8K2.t6641 from rfl, allE_node, rows6640, irow6633, rows6641]
  all_goals rfl

theorem atot6633 : totK PD2M8K2 D2M8K2.u6633 = [0, 140080210652, 631366170844, 747305110252, 285655429106, 25373788367, 0, 0] := by
  rw [show D2M8K2.u6633 = KTree.node D2M8K2.t6640 (nat_lit 14230452) (nat_lit 2549989323) (nat_lit 0) D2M8K2.t6641 from rfl, totK_node, tot6640, tot6641]
  decide +kernel

theorem arows6634 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6634 = true := by
  rw [show D2M8K2.u6634 = KTree.node D2M8K2.t6642 (nat_lit 14231658) (nat_lit 3799323125) (nat_lit 0) D2M8K2.t6643 from rfl, allE_node, rows6642, irow6634, rows6643]
  all_goals rfl

theorem atot6634 : totK PD2M8K2 D2M8K2.u6634 = [0, 157350121878, 586168451747, 765539966486, 293406223655, 12125190076, 0, 0] := by
  rw [show D2M8K2.u6634 = KTree.node D2M8K2.t6642 (nat_lit 14231658) (nat_lit 3799323125) (nat_lit 0) D2M8K2.t6643 from rfl, totK_node, tot6642, tot6643]
  decide +kernel

theorem arows6636 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6636 = true := by
  rw [show D2M8K2.u6636 = KTree.node D2M8K2.t6644 (nat_lit 14233203) (nat_lit 2986366710) (nat_lit 0) D2M8K2.t6645 from rfl, allE_node, rows6644, irow6636, rows6645]
  all_goals rfl

theorem atot6636 : totK PD2M8K2 D2M8K2.u6636 = [0, 258019643510, 853152261255, 641910331341, 66424695024, 0, 0, 0] := by
  rw [show D2M8K2.u6636 = KTree.node D2M8K2.t6644 (nat_lit 14233203) (nat_lit 2986366710) (nat_lit 0) D2M8K2.t6645 from rfl, totK_node, tot6644, tot6645]
  decide +kernel

theorem arows6637 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6637 = true := by
  rw [show D2M8K2.u6637 = KTree.node D2M8K2.t6646 (nat_lit 14235027) (nat_lit 3615965029) (nat_lit 0) D2M8K2.t6647 from rfl, allE_node, rows6646, irow6637, rows6647]
  all_goals rfl

theorem atot6637 : totK PD2M8K2 D2M8K2.u6637 = [0, 161095609644, 634198135614, 772031787570, 221250642599, 11873025674, 0, 0] := by
  rw [show D2M8K2.u6637 = KTree.node D2M8K2.t6646 (nat_lit 14235027) (nat_lit 3615965029) (nat_lit 0) D2M8K2.t6647 from rfl, totK_node, tot6646, tot6647]
  decide +kernel

theorem arows6640 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6640 = true := by
  rw [show D2M8K2.u6640 = KTree.node D2M8K2.t6648 (nat_lit 14236778) (nat_lit 4032767363) (nat_lit 0) D2M8K2.t6649 from rfl, allE_node, rows6648, irow6640, rows6649]
  all_goals rfl

theorem atot6640 : totK PD2M8K2 D2M8K2.u6640 = [0, 219316356818, 826226455608, 688969396049, 83913711549, 0, 0, 0] := by
  rw [show D2M8K2.u6640 = KTree.node D2M8K2.t6648 (nat_lit 14236778) (nat_lit 4032767363) (nat_lit 0) D2M8K2.t6649 from rfl, totK_node, tot6648, tot6649]
  decide +kernel

theorem arows6641 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6641 = true := by
  rw [show D2M8K2.u6641 = KTree.node D2M8K2.t6650 (nat_lit 14238814) (nat_lit 2020194138) (nat_lit 0) D2M8K2.t6651 from rfl, allE_node, rows6650, irow6641, rows6651]
  all_goals rfl

theorem atot6641 : totK PD2M8K2 D2M8K2.u6641 = [0, 245481410174, 692209880732, 651240939348, 201384446747, 12040273252, 0, 0] := by
  rw [show D2M8K2.u6641 = KTree.node D2M8K2.t6650 (nat_lit 14238814) (nat_lit 2020194138) (nat_lit 0) D2M8K2.t6651 from rfl, totK_node, tot6650, tot6651]
  decide +kernel

theorem arows6643 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6643 = true := by
  rw [show D2M8K2.u6643 = KTree.node D2M8K2.t6652 (nat_lit 14240024) (nat_lit 3651215652) (nat_lit 0) D2M8K2.t6653 from rfl, allE_node, rows6652, irow6643, rows6653]
  all_goals rfl

theorem atot6643 : totK PD2M8K2 D2M8K2.u6643 = [0, 176015966323, 810949085947, 727967955816, 78767502937, 0, 0, 0] := by
  rw [show D2M8K2.u6643 = KTree.node D2M8K2.t6652 (nat_lit 14240024) (nat_lit 3651215652) (nat_lit 0) D2M8K2.t6653 from rfl, totK_node, tot6652, tot6653]
  decide +kernel

theorem arows6644 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6644 = true := by
  rw [show D2M8K2.u6644 = KTree.node D2M8K2.t6654 (nat_lit 14242672) (nat_lit 3699841451) (nat_lit 0) D2M8K2.t6655 from rfl, allE_node, rows6654, irow6644, rows6655]
  all_goals rfl

theorem atot6644 : totK PD2M8K2 D2M8K2.u6644 = [0, 243867039428, 771040792874, 684724247932, 135807797513, 3880716147, 0, 0] := by
  rw [show D2M8K2.u6644 = KTree.node D2M8K2.t6654 (nat_lit 14242672) (nat_lit 3699841451) (nat_lit 0) D2M8K2.t6655 from rfl, totK_node, tot6654, tot6655]
  decide +kernel

theorem arows6653 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6653 = true := by
  rw [show D2M8K2.u6653 = KTree.node D2M8K2.t6656 (nat_lit 14244606) (nat_lit 3198733364) (nat_lit 0) D2M8K2.t6657 from rfl, allE_node, rows6656, irow6653, rows6657]
  all_goals rfl

theorem atot6653 : totK PD2M8K2 D2M8K2.u6653 = [0, 84985341920, 558473469516, 882454490628, 277133772042, 7416854702, 0, 0] := by
  rw [show D2M8K2.u6653 = KTree.node D2M8K2.t6656 (nat_lit 14244606) (nat_lit 3198733364) (nat_lit 0) D2M8K2.t6657 from rfl, totK_node, tot6656, tot6657]
  decide +kernel

theorem arows6654 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6654 = true := by
  rw [show D2M8K2.u6654 = KTree.node D2M8K2.t6658 (nat_lit 14267310) (nat_lit 4039708667) (nat_lit 0) D2M8K2.t6659 from rfl, allE_node, rows6658, irow6654, rows6659]
  all_goals rfl

theorem atot6654 : totK PD2M8K2 D2M8K2.u6654 = [0, 406087900798, 939175531267, 404094881307, 22315924875, 2313687853, 0, 0] := by
  rw [show D2M8K2.u6654 = KTree.node D2M8K2.t6658 (nat_lit 14267310) (nat_lit 4039708667) (nat_lit 0) D2M8K2.t6659 from rfl, totK_node, tot6658, tot6659]
  decide +kernel

theorem arows6656 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6656 = true := by
  rw [show D2M8K2.u6656 = KTree.node D2M8K2.t6660 (nat_lit 14269051) (nat_lit 2171249804) (nat_lit 0) D2M8K2.t6661 from rfl, allE_node, rows6660, irow6656, rows6661]
  all_goals rfl

theorem atot6656 : totK PD2M8K2 D2M8K2.u6656 = [0, 92864519961, 677659644705, 881711234581, 143422260566, 1310166938, 0, 0] := by
  rw [show D2M8K2.u6656 = KTree.node D2M8K2.t6660 (nat_lit 14269051) (nat_lit 2171249804) (nat_lit 0) D2M8K2.t6661 from rfl, totK_node, tot6660, tot6661]
  decide +kernel

theorem arows6657 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6657 = true := by
  rw [show D2M8K2.u6657 = KTree.node D2M8K2.t6662 (nat_lit 14270962) (nat_lit 4032797227) (nat_lit 0) D2M8K2.t6663 from rfl, allE_node, rows6662, irow6657, rows6663]
  all_goals rfl

theorem atot6657 : totK PD2M8K2 D2M8K2.u6657 = [0, 325166364721, 911831763158, 547690071130, 48402933236, 0, 0, 0] := by
  rw [show D2M8K2.u6657 = KTree.node D2M8K2.t6662 (nat_lit 14270962) (nat_lit 4032797227) (nat_lit 0) D2M8K2.t6663 from rfl, totK_node, tot6662, tot6663]
  decide +kernel

theorem arows6660 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6660 = true := by
  rw [show D2M8K2.u6660 = KTree.node D2M8K2.t6664 (nat_lit 14272516) (nat_lit 2946416157) (nat_lit 0) D2M8K2.t6665 from rfl, allE_node, rows6664, irow6660, rows6665]
  all_goals rfl

theorem atot6660 : totK PD2M8K2 D2M8K2.u6660 = [0, 85714291646, 501907399675, 888767776843, 334068013793, 15013989272, 0, 0] := by
  rw [show D2M8K2.u6660 = KTree.node D2M8K2.t6664 (nat_lit 14272516) (nat_lit 2946416157) (nat_lit 0) D2M8K2.t6665 from rfl, totK_node, tot6664, tot6665]
  decide +kernel

theorem arows6661 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6661 = true := by
  rw [show D2M8K2.u6661 = KTree.node D2M8K2.t6666 (nat_lit 14273992) (nat_lit 3857436912) (nat_lit 0) D2M8K2.t6667 from rfl, allE_node, rows6666, irow6661, rows6667]
  all_goals rfl

theorem atot6661 : totK PD2M8K2 D2M8K2.u6661 = [0, 354629830460, 945718749519, 495675811470, 36306968729, 0, 0, 0] := by
  rw [show D2M8K2.u6661 = KTree.node D2M8K2.t6666 (nat_lit 14273992) (nat_lit 3857436912) (nat_lit 0) D2M8K2.t6667 from rfl, totK_node, tot6666, tot6667]
  decide +kernel

theorem arows6663 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6663 = true := by
  rw [show D2M8K2.u6663 = KTree.node D2M8K2.t6668 (nat_lit 14275648) (nat_lit 3775464034) (nat_lit 0) D2M8K2.t6669 from rfl, allE_node, rows6668, irow6663, rows6669]
  all_goals rfl

theorem atot6663 : totK PD2M8K2 D2M8K2.u6663 = [0, 0, 501091241194, 985436929649, 289044190008, 13049727234, 0, 0] := by
  rw [show D2M8K2.u6663 = KTree.node D2M8K2.t6668 (nat_lit 14275648) (nat_lit 3775464034) (nat_lit 0) D2M8K2.t6669 from rfl, totK_node, tot6668, tot6669]
  decide +kernel

theorem arows6664 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6664 = true := by
  rw [show D2M8K2.u6664 = KTree.node D2M8K2.t6670 (nat_lit 14280769) (nat_lit 1551245451) (nat_lit 0) D2M8K2.t6671 from rfl, allE_node, rows6670, irow6664, rows6671]
  all_goals rfl

theorem atot6664 : totK PD2M8K2 D2M8K2.u6664 = [0, 367583770567, 902431466607, 487389995327, 45025642784, 0, 0, 0] := by
  rw [show D2M8K2.u6664 = KTree.node D2M8K2.t6670 (nat_lit 14280769) (nat_lit 1551245451) (nat_lit 0) D2M8K2.t6671 from rfl, totK_node, tot6670, tot6671]
  decide +kernel

theorem arows6668 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6668 = true := by
  rw [show D2M8K2.u6668 = KTree.node D2M8K2.t6672 (nat_lit 14282339) (nat_lit 2656272243) (nat_lit 0) D2M8K2.t6673 from rfl, allE_node, rows6672, irow6668, rows6673]
  all_goals rfl

theorem atot6668 : totK PD2M8K2 D2M8K2.u6668 = [0, 69827334452, 616558085214, 896637186814, 202382640741, 4980514959, 0, 0] := by
  rw [show D2M8K2.u6668 = KTree.node D2M8K2.t6672 (nat_lit 14282339) (nat_lit 2656272243) (nat_lit 0) D2M8K2.t6673 from rfl, totK_node, tot6672, tot6673]
  decide +kernel

theorem arows6669 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6669 = true := by
  rw [show D2M8K2.u6669 = KTree.node D2M8K2.t6674 (nat_lit 14284274) (nat_lit 4057746016) (nat_lit 0) D2M8K2.t6675 from rfl, allE_node, rows6674, irow6669, rows6675]
  all_goals rfl

theorem atot6669 : totK PD2M8K2 D2M8K2.u6669 = [0, 326597836342, 904816843572, 550477004201, 47240947084, 0, 0, 0] := by
  rw [show D2M8K2.u6669 = KTree.node D2M8K2.t6674 (nat_lit 14284274) (nat_lit 4057746016) (nat_lit 0) D2M8K2.t6675 from rfl, totK_node, tot6674, tot6675]
  decide +kernel

theorem arows6671 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6671 = true := by
  rw [show D2M8K2.u6671 = KTree.node D2M8K2.t6676 (nat_lit 14286834) (nat_lit 2955669859) (nat_lit 0) D2M8K2.t6677 from rfl, allE_node, rows6676, irow6671, rows6677]
  all_goals rfl

theorem atot6671 : totK PD2M8K2 D2M8K2.u6671 = [0, 155064126121, 662838843203, 771718869689, 186739053500, 4880895167, 0, 0] := by
  rw [show D2M8K2.u6671 = KTree.node D2M8K2.t6676 (nat_lit 14286834) (nat_lit 2955669859) (nat_lit 0) D2M8K2.t6677 from rfl, totK_node, tot6676, tot6677]
  decide +kernel

theorem arows6672 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6672 = true := by
  rw [show D2M8K2.u6672 = KTree.node D2M8K2.t6678 (nat_lit 14309281) (nat_lit 1562614071) (nat_lit 0) D2M8K2.t6679 from rfl, allE_node, rows6678, irow6672, rows6679]
  all_goals rfl

theorem atot6672 : totK PD2M8K2 D2M8K2.u6672 = [0, 239134642096, 779173034040, 636908989423, 99840893193, 1310517177, 0, 0] := by
  rw [show D2M8K2.u6672 = KTree.node D2M8K2.t6678 (nat_lit 14309281) (nat_lit 1562614071) (nat_lit 0) D2M8K2.t6679 from rfl, totK_node, tot6678, tot6679]
  decide +kernel

theorem arows6675 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6675 = true := by
  rw [show D2M8K2.u6675 = KTree.node D2M8K2.t6680 (nat_lit 14311722) (nat_lit 3802510447) (nat_lit 0) D2M8K2.t6681 from rfl, allE_node, rows6680, irow6675, rows6681]
  all_goals rfl

theorem atot6675 : totK PD2M8K2 D2M8K2.u6675 = [0, 249926246095, 827941630721, 689732877455, 72288446891, 0, 0, 0] := by
  rw [show D2M8K2.u6675 = KTree.node D2M8K2.t6680 (nat_lit 14311722) (nat_lit 3802510447) (nat_lit 0) D2M8K2.t6681 from rfl, totK_node, tot6680, tot6681]
  decide +kernel

theorem arows6676 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6676 = true := by
  rw [show D2M8K2.u6676 = KTree.node D2M8K2.t6682 (nat_lit 14313338) (nat_lit 4294967296) (nat_lit 0) D2M8K2.t6683 from rfl, allE_node, rows6682, irow6676, rows6683]
  all_goals rfl

theorem atot6676 : totK PD2M8K2 D2M8K2.u6676 = [0, 156753643563, 704159247458, 769803672735, 193395533723, 9654694938, 0, 0] := by
  rw [show D2M8K2.u6676 = KTree.node D2M8K2.t6682 (nat_lit 14313338) (nat_lit 4294967296) (nat_lit 0) D2M8K2.t6683 from rfl, totK_node, tot6682, tot6683]
  decide +kernel

theorem arows6678 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6678 = true := by
  rw [show D2M8K2.u6678 = KTree.node D2M8K2.t6684 (nat_lit 14318318) (nat_lit 2975112356) (nat_lit 0) D2M8K2.t6685 from rfl, allE_node, rows6684, irow6678, rows6685]
  all_goals rfl

theorem atot6678 : totK PD2M8K2 D2M8K2.u6678 = [0, 246659141971, 714955925140, 658794202166, 192498302832, 5411637735, 0, 0] := by
  rw [show D2M8K2.u6678 = KTree.node D2M8K2.t6684 (nat_lit 14318318) (nat_lit 2975112356) (nat_lit 0) D2M8K2.t6685 from rfl, totK_node, tot6684, tot6685]
  decide +kernel

theorem arows6679 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6679 = true := by
  rw [show D2M8K2.u6679 = KTree.node D2M8K2.t6686 (nat_lit 14319804) (nat_lit 3169560473) (nat_lit 0) D2M8K2.t6687 from rfl, allE_node, rows6686, irow6679, rows6687]
  all_goals rfl

theorem atot6679 : totK PD2M8K2 D2M8K2.u6679 = [0, 178660293291, 757420734614, 738607951256, 122628473091, 1178750802, 0, 0] := by
  rw [show D2M8K2.u6679 = KTree.node D2M8K2.t6686 (nat_lit 14319804) (nat_lit 3169560473) (nat_lit 0) D2M8K2.t6687 from rfl, totK_node, tot6686, tot6687]
  decide +kernel

theorem arows6684 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6684 = true := by
  rw [show D2M8K2.u6684 = KTree.node D2M8K2.t6688 (nat_lit 14321665) (nat_lit 1573021799) (nat_lit 0) D2M8K2.t6689 from rfl, allE_node, rows6688, irow6684, rows6689]
  all_goals rfl

theorem atot6684 : totK PD2M8K2 D2M8K2.u6684 = [0, 186820221602, 642019751484, 715611372269, 217119031193, 11991925116, 0, 0] := by
  rw [show D2M8K2.u6684 = KTree.node D2M8K2.t6688 (nat_lit 14321665) (nat_lit 1573021799) (nat_lit 0) D2M8K2.t6689 from rfl, totK_node, tot6688, tot6689]
  decide +kernel

theorem arows6685 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6685 = true := by
  rw [show D2M8K2.u6685 = KTree.node D2M8K2.t6690 (nat_lit 14322875) (nat_lit 1376316572) (nat_lit 0) D2M8K2.t6691 from rfl, allE_node, rows6690, irow6685, rows6691]
  all_goals rfl

theorem atot6685 : totK PD2M8K2 D2M8K2.u6685 = [0, 234964911183, 797936136678, 657198385083, 97235813032, 1096505104, 0, 0] := by
  rw [show D2M8K2.u6685 = KTree.node D2M8K2.t6690 (nat_lit 14322875) (nat_lit 1376316572) (nat_lit 0) D2M8K2.t6691 from rfl, totK_node, tot6690, tot6691]
  decide +kernel

theorem arows6687 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6687 = true := by
  rw [show D2M8K2.u6687 = KTree.node D2M8K2.t6692 (nat_lit 14349370) (nat_lit 3781116652) (nat_lit 0) D2M8K2.t6693 from rfl, allE_node, rows6692, irow6687, rows6693]
  all_goals rfl

theorem atot6687 : totK PD2M8K2 D2M8K2.u6687 = [0, 225647567591, 757352488668, 675023923414, 131934563220, 3884009855, 0, 0] := by
  rw [show D2M8K2.u6687 = KTree.node D2M8K2.t6692 (nat_lit 14349370) (nat_lit 3781116652) (nat_lit 0) D2M8K2.t6693 from rfl, totK_node, tot6692, tot6693]
  decide +kernel

theorem arows6688 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6688 = true := by
  rw [show D2M8K2.u6688 = KTree.node D2M8K2.t6694 (nat_lit 14350897) (nat_lit 1538198295) (nat_lit 0) D2M8K2.t6695 from rfl, allE_node, rows6694, irow6688, rows6695]
  all_goals rfl

theorem atot6688 : totK PD2M8K2 D2M8K2.u6688 = [0, 184497058421, 746205999487, 701957829832, 105519028316, 1326647619, 0, 0] := by
  rw [show D2M8K2.u6688 = KTree.node D2M8K2.t6694 (nat_lit 14350897) (nat_lit 1538198295) (nat_lit 0) D2M8K2.t6695 from rfl, totK_node, tot6694, tot6695]
  decide +kernel

theorem arows6691 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6691 = true := by
  rw [show D2M8K2.u6691 = KTree.node D2M8K2.t6696 (nat_lit 14353284) (nat_lit 1423420649) (nat_lit 0) D2M8K2.t6697 from rfl, allE_node, rows6696, irow6691, rows6697]
  all_goals rfl

theorem atot6691 : totK PD2M8K2 D2M8K2.u6691 = [0, 264712980047, 828975240288, 646492345364, 65389038669, 0, 0, 0] := by
  rw [show D2M8K2.u6691 = KTree.node D2M8K2.t6696 (nat_lit 14353284) (nat_lit 1423420649) (nat_lit 0) D2M8K2.t6697 from rfl, totK_node, tot6696, tot6697]
  decide +kernel

theorem arows6692 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6692 = true := by
  rw [show D2M8K2.u6692 = KTree.node D2M8K2.t6698 (nat_lit 14354831) (nat_lit 2136723247) (nat_lit 0) D2M8K2.t6699 from rfl, allE_node, rows6698, irow6692, rows6699]
  all_goals rfl

theorem atot6692 : totK PD2M8K2 D2M8K2.u6692 = [0, 157042048713, 648876468009, 732018785354, 247176515433, 18317572719, 0, 0] := by
  rw [show D2M8K2.u6692 = KTree.node D2M8K2.t6698 (nat_lit 14354831) (nat_lit 2136723247) (nat_lit 0) D2M8K2.t6699 from rfl, totK_node, tot6698, tot6699]
  decide +kernel

theorem arows6694 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6694 = true := by
  rw [show D2M8K2.u6694 = KTree.node D2M8K2.t6700 (nat_lit 14356225) (nat_lit 1573088089) (nat_lit 0) D2M8K2.t6701 from rfl, allE_node, rows6700, irow6694, rows6701]
  all_goals rfl

theorem atot6694 : totK PD2M8K2 D2M8K2.u6694 = [0, 189210620299, 659020233261, 746064135059, 205022977433, 5393550755, 0, 0] := by
  rw [show D2M8K2.u6694 = KTree.node D2M8K2.t6700 (nat_lit 14356225) (nat_lit 1573088089) (nat_lit 0) D2M8K2.t6701 from rfl, totK_node, tot6700, tot6701]
  decide +kernel

theorem arows6695 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6695 = true := by
  rw [show D2M8K2.u6695 = KTree.node D2M8K2.t6702 (nat_lit 14357697) (nat_lit 1359082161) (nat_lit 0) D2M8K2.t6703 from rfl, allE_node, rows6702, irow6695, rows6703]
  all_goals rfl

theorem atot6695 : totK PD2M8K2 D2M8K2.u6695 = [0, 230642075587, 802385372667, 661565977774, 94524890487, 1128973710, 0, 0] := by
  rw [show D2M8K2.u6695 = KTree.node D2M8K2.t6702 (nat_lit 14357697) (nat_lit 1359082161) (nat_lit 0) D2M8K2.t6703 from rfl, totK_node, tot6702, tot6703]
  decide +kernel

theorem arows6699 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6699 = true := by
  rw [show D2M8K2.u6699 = KTree.node D2M8K2.t6704 (nat_lit 14359440) (nat_lit 3464687280) (nat_lit 0) D2M8K2.t6705 from rfl, allE_node, rows6704, irow6699, rows6705]
  all_goals rfl

theorem atot6699 : totK PD2M8K2 D2M8K2.u6699 = [0, 169146838046, 649565343739, 740388136754, 203189275092, 11780292382, 0, 0] := by
  rw [show D2M8K2.u6699 = KTree.node D2M8K2.t6704 (nat_lit 14359440) (nat_lit 3464687280) (nat_lit 0) D2M8K2.t6705 from rfl, totK_node, tot6704, tot6705]
  decide +kernel

theorem arows6700 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6700 = true := by
  rw [show D2M8K2.u6700 = KTree.node D2M8K2.t6706 (nat_lit 14361080) (nat_lit 3924363918) (nat_lit 0) D2M8K2.t6707 from rfl, allE_node, rows6706, irow6700, rows6707]
  all_goals rfl

theorem atot6700 : totK PD2M8K2 D2M8K2.u6700 = [0, 230530497835, 775635630642, 658583027634, 100211004234, 1162740214, 0, 0] := by
  rw [show D2M8K2.u6700 = KTree.node D2M8K2.t6706 (nat_lit 14361080) (nat_lit 3924363918) (nat_lit 0) D2M8K2.t6707 from rfl, totK_node, tot6706, tot6707]
  decide +kernel

theorem arows6702 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6702 = true := by
  rw [show D2M8K2.u6702 = KTree.node D2M8K2.t6708 (nat_lit 14362886) (nat_lit 4095928524) (nat_lit 0) D2M8K2.t6709 from rfl, allE_node, rows6708, irow6702, rows6709]
  all_goals rfl

theorem atot6702 : totK PD2M8K2 D2M8K2.u6702 = [0, 175594001528, 659076049103, 737572998435, 206207814263, 11947333746, 0, 0] := by
  rw [show D2M8K2.u6702 = KTree.node D2M8K2.t6708 (nat_lit 14362886) (nat_lit 4095928524) (nat_lit 0) D2M8K2.t6709 from rfl, totK_node, tot6708, tot6709]
  decide +kernel

theorem arows6703 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6703 = true := by
  rw [show D2M8K2.u6703 = KTree.node D2M8K2.t6710 (nat_lit 14364267) (nat_lit 3381978580) (nat_lit 0) D2M8K2.t6711 from rfl, allE_node, rows6710, irow6703, rows6711]
  all_goals rfl

theorem atot6703 : totK PD2M8K2 D2M8K2.u6703 = [0, 267890685069, 820016083973, 620851677430, 93221647860, 1096505104, 0, 0] := by
  rw [show D2M8K2.u6703 = KTree.node D2M8K2.t6710 (nat_lit 14364267) (nat_lit 3381978580) (nat_lit 0) D2M8K2.t6711 from rfl, totK_node, tot6710, tot6711]
  decide +kernel

theorem arows6706 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6706 = true := by
  rw [show D2M8K2.u6706 = KTree.node D2M8K2.t6712 (nat_lit 14366189) (nat_lit 1711811678) (nat_lit 0) D2M8K2.t6713 from rfl, allE_node, rows6712, irow6706, rows6713]
  all_goals rfl

theorem atot6706 : totK PD2M8K2 D2M8K2.u6706 = [0, 0, 488355271689, 995810865515, 291609065030, 12047602520, 0, 0] := by
  rw [show D2M8K2.u6706 = KTree.node D2M8K2.t6712 (nat_lit 14366189) (nat_lit 1711811678) (nat_lit 0) D2M8K2.t6713 from rfl, totK_node, tot6712, tot6713]
  decide +kernel

theorem arows6707 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6707 = true := by
  rw [show D2M8K2.u6707 = KTree.node D2M8K2.t6714 (nat_lit 14371510) (nat_lit 3231474787) (nat_lit 0) D2M8K2.t6715 from rfl, allE_node, rows6714, irow6707, rows6715]
  all_goals rfl

theorem atot6707 : totK PD2M8K2 D2M8K2.u6707 = [0, 0, 231766306880, 807754664930, 567265223978, 79588052533, 1138244013, 0] := by
  rw [show D2M8K2.u6707 = KTree.node D2M8K2.t6714 (nat_lit 14371510) (nat_lit 3231474787) (nat_lit 0) D2M8K2.t6715 from rfl, totK_node, tot6714, tot6715]
  decide +kernel

theorem arows6709 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6709 = true := by
  rw [show D2M8K2.u6709 = KTree.node D2M8K2.t6716 (nat_lit 14374066) (nat_lit 3436238476) (nat_lit 0) D2M8K2.t6717 from rfl, allE_node, rows6716, irow6709, rows6717]
  all_goals rfl

theorem atot6709 : totK PD2M8K2 D2M8K2.u6709 = [0, 0, 305369247350, 887759330927, 523659839990, 45383437612, 0, 0] := by
  rw [show D2M8K2.u6709 = KTree.node D2M8K2.t6716 (nat_lit 14374066) (nat_lit 3436238476) (nat_lit 0) D2M8K2.t6717 from rfl, totK_node, tot6716, tot6717]
  decide +kernel

theorem arows6710 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6710 = true := by
  rw [show D2M8K2.u6710 = KTree.node D2M8K2.t6718 (nat_lit 14377300) (nat_lit 4041295213) (nat_lit 0) D2M8K2.t6719 from rfl, allE_node, rows6718, irow6710, rows6719]
  all_goals rfl

theorem atot6710 : totK PD2M8K2 D2M8K2.u6710 = [0, 0, 405917503164, 961847804700, 385810755715, 20937176931, 0, 0] := by
  rw [show D2M8K2.u6710 = KTree.node D2M8K2.t6718 (nat_lit 14377300) (nat_lit 4041295213) (nat_lit 0) D2M8K2.t6719 from rfl, totK_node, tot6718, tot6719]
  decide +kernel

theorem arows6716 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6716 = true := by
  rw [show D2M8K2.u6716 = KTree.node D2M8K2.t6720 (nat_lit 14380742) (nat_lit 4180272124) (nat_lit 0) D2M8K2.t6721 from rfl, allE_node, rows6720, irow6716, rows6721]
  all_goals rfl

theorem atot6716 : totK PD2M8K2 D2M8K2.u6716 = [0, 0, 400138990772, 948726506870, 389221914731, 23208721423, 0, 0] := by
  rw [show D2M8K2.u6716 = KTree.node D2M8K2.t6720 (nat_lit 14380742) (nat_lit 4180272124) (nat_lit 0) D2M8K2.t6721 from rfl, totK_node, tot6720, tot6721]
  decide +kernel

theorem arows6717 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6717 = true := by
  rw [show D2M8K2.u6717 = KTree.node D2M8K2.t6722 (nat_lit 14384192) (nat_lit 3803927338) (nat_lit 0) D2M8K2.t6723 from rfl, allE_node, rows6722, irow6717, rows6723]
  all_goals rfl

theorem atot6717 : totK PD2M8K2 D2M8K2.u6717 = [0, 0, 380031073673, 933354598059, 424388849225, 27988987451, 0, 0] := by
  rw [show D2M8K2.u6717 = KTree.node D2M8K2.t6722 (nat_lit 14384192) (nat_lit 3803927338) (nat_lit 0) D2M8K2.t6723 from rfl, totK_node, tot6722, tot6723]
  decide +kernel

theorem arows6719 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6719 = true := by
  rw [show D2M8K2.u6719 = KTree.node D2M8K2.t6724 (nat_lit 14385668) (nat_lit 3293005897) (nat_lit 0) D2M8K2.t6725 from rfl, allE_node, rows6724, irow6719, rows6725]
  all_goals rfl

theorem atot6719 : totK PD2M8K2 D2M8K2.u6719 = [0, 0, 161182880140, 755207634156, 720016359256, 110255658906, 1095107716, 0] := by
  rw [show D2M8K2.u6719 = KTree.node D2M8K2.t6724 (nat_lit 14385668) (nat_lit 3293005897) (nat_lit 0) D2M8K2.t6725 from rfl, totK_node, tot6724, tot6725]
  decide +kernel

theorem arows6720 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6720 = true := by
  rw [show D2M8K2.u6720 = KTree.node D2M8K2.t6726 (nat_lit 14432870) (nat_lit 3250974627) (nat_lit 0) D2M8K2.t6727 from rfl, allE_node, rows6726, irow6720, rows6727]
  all_goals rfl

theorem atot6720 : totK PD2M8K2 D2M8K2.u6720 = [306235076213, 721791207661, 323601155765, 113293166099, 222315599035, 89969846568, 3882006667, 0] := by
  rw [show D2M8K2.u6720 = KTree.node D2M8K2.t6726 (nat_lit 14432870) (nat_lit 3250974627) (nat_lit 0) D2M8K2.t6727 from rfl, totK_node, tot6726, tot6727]
  decide +kernel

theorem arows6723 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6723 = true := by
  rw [show D2M8K2.u6723 = KTree.node D2M8K2.t6728 (nat_lit 14434081) (nat_lit 1511738784) (nat_lit 0) D2M8K2.t6729 from rfl, allE_node, rows6728, irow6723, rows6729]
  all_goals rfl

theorem atot6723 : totK PD2M8K2 D2M8K2.u6723 = [127253961937, 713789964182, 811185579170, 138717700133, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u6723 = KTree.node D2M8K2.t6728 (nat_lit 14434081) (nat_lit 1511738784) (nat_lit 0) D2M8K2.t6729 from rfl, totK_node, tot6728, tot6729]
  decide +kernel

theorem arows6724 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6724 = true := by
  rw [show D2M8K2.u6724 = KTree.node D2M8K2.t6730 (nat_lit 14439644) (nat_lit 3360878196) (nat_lit 0) D2M8K2.t6731 from rfl, allE_node, rows6730, irow6724, rows6731]
  all_goals rfl

theorem atot6724 : totK PD2M8K2 D2M8K2.u6724 = [326510560199, 889895170401, 550814205814, 51443490253, 0, 0, 0, 0] := by
  rw [show D2M8K2.u6724 = KTree.node D2M8K2.t6730 (nat_lit 14439644) (nat_lit 3360878196) (nat_lit 0) D2M8K2.t6731 from rfl, totK_node, tot6730, tot6731]
  decide +kernel

theorem arows6726 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6726 = true := by
  rw [show D2M8K2.u6726 = KTree.node D2M8K2.t6732 (nat_lit 14441171) (nat_lit 2241750538) (nat_lit 0) D2M8K2.t6733 from rfl, allE_node, rows6732, irow6726, rows6733]
  all_goals rfl

theorem atot6726 : totK PD2M8K2 D2M8K2.u6726 = [87773917060, 584152696172, 860174401712, 242401584183, 10568566766, 0, 0, 0] := by
  rw [show D2M8K2.u6726 = KTree.node D2M8K2.t6732 (nat_lit 14441171) (nat_lit 2241750538) (nat_lit 0) D2M8K2.t6733 from rfl, totK_node, tot6732, tot6733]
  decide +kernel

theorem arows6727 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6727 = true := by
  rw [show D2M8K2.u6727 = KTree.node D2M8K2.t6734 (nat_lit 14443083) (nat_lit 3762187572) (nat_lit 0) D2M8K2.t6735 from rfl, allE_node, rows6734, irow6727, rows6735]
  all_goals rfl

theorem atot6727 : totK PD2M8K2 D2M8K2.u6727 = [294271252461, 837249529153, 564341542670, 89791738199, 2481160468, 0, 0, 0] := by
  rw [show D2M8K2.u6727 = KTree.node D2M8K2.t6734 (nat_lit 14443083) (nat_lit 3762187572) (nat_lit 0) D2M8K2.t6735 from rfl, totK_node, tot6734, tot6735]
  decide +kernel

theorem arows6731 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6731 = true := by
  rw [show D2M8K2.u6731 = KTree.node D2M8K2.t6736 (nat_lit 14444712) (nat_lit 2852824020) (nat_lit 0) D2M8K2.t6737 from rfl, allE_node, rows6736, irow6731, rows6737]
  all_goals rfl

theorem atot6731 : totK PD2M8K2 D2M8K2.u6731 = [87238298500, 534194843219, 846052946043, 277483895740, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u6731 = KTree.node D2M8K2.t6736 (nat_lit 14444712) (nat_lit 2852824020) (nat_lit 0) D2M8K2.t6737 from rfl, totK_node, tot6736, tot6737]
  decide +kernel

theorem arows6732 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6732 = true := by
  rw [show D2M8K2.u6732 = KTree.node D2M8K2.t6738 (nat_lit 14446851) (nat_lit 2982898927) (nat_lit 0) D2M8K2.t6739 from rfl, allE_node, rows6738, irow6732, rows6739]
  all_goals rfl

theorem atot6732 : totK PD2M8K2 D2M8K2.u6732 = [323551348438, 908747228783, 515293432114, 46303331748, 0, 0, 0, 0] := by
  rw [show D2M8K2.u6732 = KTree.node D2M8K2.t6738 (nat_lit 14446851) (nat_lit 2982898927) (nat_lit 0) D2M8K2.t6739 from rfl, totK_node, tot6738, tot6739]
  decide +kernel

theorem arows6734 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6734 = true := by
  rw [show D2M8K2.u6734 = KTree.node D2M8K2.t6740 (nat_lit 14449042) (nat_lit 1915628808) (nat_lit 0) D2M8K2.t6741 from rfl, allE_node, rows6740, irow6734, rows6741]
  all_goals rfl

theorem atot6734 : totK PD2M8K2 D2M8K2.u6734 = [161040959423, 664378718949, 774778259886, 186267593995, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u6734 = KTree.node D2M8K2.t6740 (nat_lit 14449042) (nat_lit 1915628808) (nat_lit 0) D2M8K2.t6741 from rfl, totK_node, tot6740, tot6741]
  decide +kernel

theorem arows6735 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6735 = true := by
  rw [show D2M8K2.u6735 = KTree.node D2M8K2.t6742 (nat_lit 14450618) (nat_lit 3948304266) (nat_lit 0) D2M8K2.t6743 from rfl, allE_node, rows6742, irow6735, rows6743]
  all_goals rfl

theorem atot6735 : totK PD2M8K2 D2M8K2.u6735 = [264728882885, 816819474543, 630772280843, 87267903602, 1268739303, 0, 0, 0] := by
  rw [show D2M8K2.u6735 = KTree.node D2M8K2.t6742 (nat_lit 14450618) (nat_lit 3948304266) (nat_lit 0) D2M8K2.t6743 from rfl, totK_node, tot6742, tot6743]
  decide +kernel

theorem arows6738 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6738 = true := by
  rw [show D2M8K2.u6738 = KTree.node D2M8K2.t6744 (nat_lit 14452259) (nat_lit 2964126074) (nat_lit 0) D2M8K2.t6745 from rfl, allE_node, rows6744, irow6738, rows6745]
  all_goals rfl

theorem atot6738 : totK PD2M8K2 D2M8K2.u6738 = [0, 427563529170, 956170603900, 372971803855, 20780039840, 0, 0, 0] := by
  rw [show D2M8K2.u6738 = KTree.node D2M8K2.t6744 (nat_lit 14452259) (nat_lit 2964126074) (nat_lit 0) D2M8K2.t6745 from rfl, totK_node, tot6744, tot6745]
  decide +kernel

theorem arows6739 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6739 = true := by
  rw [show D2M8K2.u6739 = KTree.node D2M8K2.t6746 (nat_lit 14454033) (nat_lit 1136135164) (nat_lit 0) D2M8K2.t6747 from rfl, allE_node, rows6746, irow6739, rows6747]
  all_goals rfl

theorem atot6739 : totK PD2M8K2 D2M8K2.u6739 = [0, 340146954503, 930109864325, 449833099112, 25642957767, 0, 0, 0] := by
  rw [show D2M8K2.u6739 = KTree.node D2M8K2.t6746 (nat_lit 14454033) (nat_lit 1136135164) (nat_lit 0) D2M8K2.t6747 from rfl, totK_node, tot6746, tot6747]
  decide +kernel

theorem arows6741 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6741 = true := by
  rw [show D2M8K2.u6741 = KTree.node D2M8K2.t6748 (nat_lit 14455723) (nat_lit 1521231798) (nat_lit 0) D2M8K2.t6749 from rfl, allE_node, rows6748, irow6741, rows6749]
  all_goals rfl

theorem atot6741 : totK PD2M8K2 D2M8K2.u6741 = [0, 120475736232, 702426520927, 780101549080, 140212125400, 1369150432, 0, 0] := by
  rw [show D2M8K2.u6741 = KTree.node D2M8K2.t6748 (nat_lit 14455723) (nat_lit 1521231798) (nat_lit 0) D2M8K2.t6749 from rfl, totK_node, tot6748, tot6749]
  decide +kernel

theorem arows6742 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6742 = true := by
  rw [show D2M8K2.u6742 = KTree.node D2M8K2.t6750 (nat_lit 14461156) (nat_lit 3825369563) (nat_lit 0) D2M8K2.t6751 from rfl, allE_node, rows6750, irow6742, rows6751]
  all_goals rfl

theorem atot6742 : totK PD2M8K2 D2M8K2.u6742 = [0, 379256136337, 945577332039, 438153982552, 25128719370, 0, 0, 0] := by
  rw [show D2M8K2.u6742 = KTree.node D2M8K2.t6750 (nat_lit 14461156) (nat_lit 3825369563) (nat_lit 0) D2M8K2.t6751 from rfl, totK_node, tot6750, tot6751]
  decide +kernel

theorem arows6747 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6747 = true := by
  rw [show D2M8K2.u6747 = KTree.node D2M8K2.t6752 (nat_lit 14464573) (nat_lit 1198561008) (nat_lit 0) D2M8K2.t6753 from rfl, allE_node, rows6752, irow6747, rows6753]
  all_goals rfl

theorem atot6747 : totK PD2M8K2 D2M8K2.u6747 = [0, 380742147050, 935176180109, 441703623730, 25291380580, 0, 0, 0] := by
  rw [show D2M8K2.u6747 = KTree.node D2M8K2.t6752 (nat_lit 14464573) (nat_lit 1198561008) (nat_lit 0) D2M8K2.t6753 from rfl, totK_node, tot6752, tot6753]
  decide +kernel

theorem arows6748 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6748 = true := by
  rw [show D2M8K2.u6748 = KTree.node D2M8K2.t6754 (nat_lit 14467929) (nat_lit 1880611397) (nat_lit 0) D2M8K2.t6755 from rfl, allE_node, rows6754, irow6748, rows6755]
  all_goals rfl

theorem atot6748 : totK PD2M8K2 D2M8K2.u6748 = [0, 343377699113, 950013944616, 454739001298, 23497101953, 0, 0, 0] := by
  rw [show D2M8K2.u6748 = KTree.node D2M8K2.t6754 (nat_lit 14467929) (nat_lit 1880611397) (nat_lit 0) D2M8K2.t6755 from rfl, totK_node, tot6754, tot6755]
  decide +kernel

theorem arows6750 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6750 = true := by
  rw [show D2M8K2.u6750 = KTree.node D2M8K2.t6756 (nat_lit 14471239) (nat_lit 2368751454) (nat_lit 0) D2M8K2.t6757 from rfl, allE_node, rows6756, irow6750, rows6757]
  all_goals rfl

theorem atot6750 : totK PD2M8K2 D2M8K2.u6750 = [67645289364, 414169009778, 852433500555, 442490159019, 28363432085, 0, 0, 0] := by
  rw [show D2M8K2.u6750 = KTree.node D2M8K2.t6756 (nat_lit 14471239) (nat_lit 2368751454) (nat_lit 0) D2M8K2.t6757 from rfl, totK_node, tot6756, tot6757]
  decide +kernel

theorem arows6751 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6751 = true := by
  rw [show D2M8K2.u6751 = KTree.node D2M8K2.t6758 (nat_lit 14478140) (nat_lit 3375134809) (nat_lit 0) D2M8K2.t6759 from rfl, allE_node, rows6758, irow6751, rows6759]
  all_goals rfl

theorem atot6751 : totK PD2M8K2 D2M8K2.u6751 = [367245211752, 926472176752, 497030084026, 40752954609, 0, 0, 0, 0] := by
  rw [show D2M8K2.u6751 = KTree.node D2M8K2.t6758 (nat_lit 14478140) (nat_lit 3375134809) (nat_lit 0) D2M8K2.t6759 from rfl, totK_node, tot6758, tot6759]
  decide +kernel

theorem arows6754 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6754 = true := by
  rw [show D2M8K2.u6754 = KTree.node D2M8K2.t6760 (nat_lit 14479587) (nat_lit 3655373328) (nat_lit 0) D2M8K2.t6761 from rfl, allE_node, rows6760, irow6754, rows6761]
  all_goals rfl

theorem atot6754 : totK PD2M8K2 D2M8K2.u6754 = [4194847968, 461835250284, 927619894110, 395663181744, 29394892645, 0, 0, 0] := by
  rw [show D2M8K2.u6754 = KTree.node D2M8K2.t6760 (nat_lit 14479587) (nat_lit 3655373328) (nat_lit 0) D2M8K2.t6761 from rfl, totK_node, tot6760, tot6761]
  decide +kernel

theorem arows6755 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6755 = true := by
  rw [show D2M8K2.u6755 = KTree.node D2M8K2.t6762 (nat_lit 14480959) (nat_lit 2193852504) (nat_lit 0) D2M8K2.t6763 from rfl, allE_node, rows6762, irow6755, rows6763]
  all_goals rfl

theorem atot6755 : totK PD2M8K2 D2M8K2.u6755 = [249726446068, 715045256461, 647596367366, 204487291206, 8214505460, 0, 0, 0] := by
  rw [show D2M8K2.u6755 = KTree.node D2M8K2.t6762 (nat_lit 14480959) (nat_lit 2193852504) (nat_lit 0) D2M8K2.t6763 from rfl, totK_node, tot6762, tot6763]
  decide +kernel

theorem arows6757 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6757 = true := by
  rw [show D2M8K2.u6757 = KTree.node D2M8K2.t6764 (nat_lit 14482416) (nat_lit 3596949163) (nat_lit 0) D2M8K2.t6765 from rfl, allE_node, rows6764, irow6757, rows6765]
  all_goals rfl

theorem atot6757 : totK PD2M8K2 D2M8K2.u6757 = [167426896901, 689276664727, 760475783191, 187234733579, 8124795009, 0, 0, 0] := by
  rw [show D2M8K2.u6757 = KTree.node D2M8K2.t6764 (nat_lit 14482416) (nat_lit 3596949163) (nat_lit 0) D2M8K2.t6765 from rfl, totK_node, tot6764, tot6765]
  decide +kernel

theorem arows6758 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6758 = true := by
  rw [show D2M8K2.u6758 = KTree.node D2M8K2.t6766 (nat_lit 14484414) (nat_lit 3946891661) (nat_lit 0) D2M8K2.t6767 from rfl, allE_node, rows6766, irow6758, rows6767]
  all_goals rfl

theorem atot6758 : totK PD2M8K2 D2M8K2.u6758 = [232412101965, 749804877773, 683108276888, 141037416467, 4881092576, 0, 0, 0] := by
  rw [show D2M8K2.u6758 = KTree.node D2M8K2.t6766 (nat_lit 14484414) (nat_lit 3946891661) (nat_lit 0) D2M8K2.t6767 from rfl, totK_node, tot6766, tot6767]
  decide +kernel

theorem arows6762 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6762 = true := by
  rw [show D2M8K2.u6762 = KTree.node D2M8K2.t6768 (nat_lit 14485951) (nat_lit 2332151599) (nat_lit 0) D2M8K2.t6769 from rfl, allE_node, rows6768, irow6762, rows6769]
  all_goals rfl

theorem atot6762 : totK PD2M8K2 D2M8K2.u6762 = [153421184897, 675699351632, 769894523790, 205184082548, 9562610978, 0, 0, 0] := by
  rw [show D2M8K2.u6762 = KTree.node D2M8K2.t6768 (nat_lit 14485951) (nat_lit 2332151599) (nat_lit 0) D2M8K2.t6769 from rfl, totK_node, tot6768, tot6769]
  decide +kernel

theorem arows6763 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6763 = true := by
  rw [show D2M8K2.u6763 = KTree.node D2M8K2.t6770 (nat_lit 14488109) (nat_lit 2121503409) (nat_lit 0) D2M8K2.t6771 from rfl, allE_node, rows6770, irow6763, rows6771]
  all_goals rfl

theorem atot6763 : totK PD2M8K2 D2M8K2.u6763 = [283231627940, 801596010823, 642113537145, 111145235242, 2491535930, 0, 0, 0] := by
  rw [show D2M8K2.u6763 = KTree.node D2M8K2.t6770 (nat_lit 14488109) (nat_lit 2121503409) (nat_lit 0) D2M8K2.t6771 from rfl, totK_node, tot6770, tot6771]
  decide +kernel

theorem arows6765 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6765 = true := by
  rw [show D2M8K2.u6765 = KTree.node D2M8K2.t6772 (nat_lit 14490254) (nat_lit 3652508158) (nat_lit 0) D2M8K2.t6773 from rfl, allE_node, rows6772, irow6765, rows6773]
  all_goals rfl

theorem atot6765 : totK PD2M8K2 D2M8K2.u6765 = [163080073351, 741474676918, 770172992345, 149837970834, 3869034280, 0, 0, 0] := by
  rw [show D2M8K2.u6765 = KTree.node D2M8K2.t6772 (nat_lit 14490254) (nat_lit 3652508158) (nat_lit 0) D2M8K2.t6773 from rfl, totK_node, tot6772, tot6773]
  decide +kernel

theorem arows6766 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6766 = true := by
  rw [show D2M8K2.u6766 = KTree.node D2M8K2.t6774 (nat_lit 14491944) (nat_lit 3471467821) (nat_lit 0) D2M8K2.t6775 from rfl, allE_node, rows6774, irow6766, rows6775]
  all_goals rfl

theorem atot6766 : totK PD2M8K2 D2M8K2.u6766 = [307320676048, 883954385464, 577134437722, 55792104871, 0, 0, 0, 0] := by
  rw [show D2M8K2.u6766 = KTree.node D2M8K2.t6774 (nat_lit 14491944) (nat_lit 3471467821) (nat_lit 0) D2M8K2.t6775 from rfl, totK_node, tot6774, tot6775]
  decide +kernel

theorem arows6769 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6769 = true := by
  rw [show D2M8K2.u6769 = KTree.node D2M8K2.t6776 (nat_lit 14493608) (nat_lit 1968244956) (nat_lit 0) D2M8K2.t6777 from rfl, allE_node, rows6776, irow6769, rows6777]
  all_goals rfl

theorem atot6769 : totK PD2M8K2 D2M8K2.u6769 = [0, 410135640286, 950728157458, 396582796571, 22028021799, 0, 0, 0] := by
  rw [show D2M8K2.u6769 = KTree.node D2M8K2.t6776 (nat_lit 14493608) (nat_lit 1968244956) (nat_lit 0) D2M8K2.t6777 from rfl, totK_node, tot6776, tot6777]
  decide +kernel

theorem arows6770 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6770 = true := by
  rw [show D2M8K2.u6770 = KTree.node D2M8K2.t6778 (nat_lit 14498790) (nat_lit 3843926231) (nat_lit 0) D2M8K2.t6779 from rfl, allE_node, rows6778, irow6770, rows6779]
  all_goals rfl

theorem atot6770 : totK PD2M8K2 D2M8K2.u6770 = [0, 366004900279, 930767903019, 496958476406, 37250944130, 0, 0, 0] := by
  rw [show D2M8K2.u6770 = KTree.node D2M8K2.t6778 (nat_lit 14498790) (nat_lit 3843926231) (nat_lit 0) D2M8K2.t6779 from rfl, totK_node, tot6778, tot6779]
  decide +kernel

theorem arows6772 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6772 = true := by
  rw [show D2M8K2.u6772 = KTree.node D2M8K2.t6780 (nat_lit 14500250) (nat_lit 4242461733) (nat_lit 0) D2M8K2.t6781 from rfl, allE_node, rows6780, irow6772, rows6781]
  all_goals rfl

theorem atot6772 : totK PD2M8K2 D2M8K2.u6772 = [0, 52622787700, 489305490592, 862191103872, 369669214482, 29044448997, 0, 0] := by
  rw [show D2M8K2.u6772 = KTree.node D2M8K2.t6780 (nat_lit 14500250) (nat_lit 4242461733) (nat_lit 0) D2M8K2.t6781 from rfl, totK_node, tot6780, tot6781]
  decide +kernel

theorem arows6773 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6773 = true := by
  rw [show D2M8K2.u6773 = KTree.node D2M8K2.t6782 (nat_lit 14501568) (nat_lit 3449492573) (nat_lit 0) D2M8K2.t6783 from rfl, allE_node, rows6782, irow6773, rows6783]
  all_goals rfl

theorem atot6773 : totK PD2M8K2 D2M8K2.u6773 = [0, 249231149011, 713099093487, 646528829528, 192394942783, 7877424857, 0, 0] := by
  rw [show D2M8K2.u6773 = KTree.node D2M8K2.t6782 (nat_lit 14501568) (nat_lit 3449492573) (nat_lit 0) D2M8K2.t6783 from rfl, totK_node, tot6782, tot6783]
  decide +kernel

theorem arows6780 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6780 = true := by
  rw [show D2M8K2.u6780 = KTree.node D2M8K2.t6784 (nat_lit 14503083) (nat_lit 3477443229) (nat_lit 0) D2M8K2.t6785 from rfl, allE_node, rows6784, irow6780, rows6785]
  all_goals rfl

theorem atot6780 : totK PD2M8K2 D2M8K2.u6780 = [0, 166849040158, 735460793672, 749321790787, 142250250743, 4009909289, 0, 0] := by
  rw [show D2M8K2.u6780 = KTree.node D2M8K2.t6784 (nat_lit 14503083) (nat_lit 3477443229) (nat_lit 0) D2M8K2.t6785 from rfl, totK_node, tot6784, tot6785]
  decide +kernel

theorem arows6781 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6781 = true := by
  rw [show D2M8K2.u6781 = KTree.node D2M8K2.t6786 (nat_lit 14505210) (nat_lit 3921281593) (nat_lit 0) D2M8K2.t6787 from rfl, allE_node, rows6786, irow6781, rows6787]
  all_goals rfl

theorem atot6781 : totK PD2M8K2 D2M8K2.u6781 = [0, 268965907016, 784905305521, 650647761190, 109601852464, 1149959346, 0, 0] := by
  rw [show D2M8K2.u6781 = KTree.node D2M8K2.t6786 (nat_lit 14505210) (nat_lit 3921281593) (nat_lit 0) D2M8K2.t6787 from rfl, totK_node, tot6786, tot6787]
  decide +kernel

theorem arows6783 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6783 = true := by
  rw [show D2M8K2.u6783 = KTree.node D2M8K2.t6788 (nat_lit 14506941) (nat_lit 1449018175) (nat_lit 0) D2M8K2.t6789 from rfl, allE_node, rows6788, irow6783, rows6789]
  all_goals rfl

theorem atot6783 : totK PD2M8K2 D2M8K2.u6783 = [0, 115880449303, 667031649318, 813948025594, 194984681262, 5218872685, 0, 0] := by
  rw [show D2M8K2.u6783 = KTree.node D2M8K2.t6788 (nat_lit 14506941) (nat_lit 1449018175) (nat_lit 0) D2M8K2.t6789 from rfl, totK_node, tot6788, tot6789]
  decide +kernel

theorem arows6784 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6784 = true := by
  rw [show D2M8K2.u6784 = KTree.node D2M8K2.t6790 (nat_lit 14509036) (nat_lit 3916293635) (nat_lit 0) D2M8K2.t6791 from rfl, allE_node, rows6790, irow6784, rows6791]
  all_goals rfl

theorem atot6784 : totK PD2M8K2 D2M8K2.u6784 = [0, 329179257552, 902529000671, 552748873269, 53802263904, 0, 0, 0] := by
  rw [show D2M8K2.u6784 = KTree.node D2M8K2.t6790 (nat_lit 14509036) (nat_lit 3916293635) (nat_lit 0) D2M8K2.t6791 from rfl, totK_node, tot6790, tot6791]
  decide +kernel

theorem arows6787 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6787 = true := by
  rw [show D2M8K2.u6787 = KTree.node D2M8K2.t6792 (nat_lit 14511338) (nat_lit 4116668324) (nat_lit 0) D2M8K2.t6793 from rfl, allE_node, rows6792, irow6787, rows6793]
  all_goals rfl

theorem atot6787 : totK PD2M8K2 D2M8K2.u6787 = [0, 161132822848, 731687516432, 799860202255, 148792775560, 1415142070, 0, 0] := by
  rw [show D2M8K2.u6787 = KTree.node D2M8K2.t6792 (nat_lit 14511338) (nat_lit 4116668324) (nat_lit 0) D2M8K2.t6793 from rfl, totK_node, tot6792, tot6793]
  decide +kernel

theorem arows6788 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6788 = true := by
  rw [show D2M8K2.u6788 = KTree.node D2M8K2.t6794 (nat_lit 14513191) (nat_lit 2234601212) (nat_lit 0) D2M8K2.t6795 from rfl, allE_node, rows6794, irow6788, rows6795]
  all_goals rfl

theorem atot6788 : totK PD2M8K2 D2M8K2.u6788 = [0, 264613567556, 868832917787, 615609151186, 60014521477, 0, 0, 0] := by
  rw [show D2M8K2.u6788 = KTree.node D2M8K2.t6794 (nat_lit 14513191) (nat_lit 2234601212) (nat_lit 0) D2M8K2.t6795 from rfl, totK_node, tot6794, tot6795]
  decide +kernel

theorem arows6790 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6790 = true := by
  rw [show D2M8K2.u6790 = KTree.node D2M8K2.t6796 (nat_lit 14515049) (nat_lit 1606595090) (nat_lit 0) D2M8K2.t6797 from rfl, allE_node, rows6796, irow6790, rows6797]
  all_goals rfl

theorem atot6790 : totK PD2M8K2 D2M8K2.u6790 = [178250561612, 388425051226, 358517013489, 599024145357, 243063962485, 9302370699, 0, 0] := by
  rw [show D2M8K2.u6790 = KTree.node D2M8K2.t6796 (nat_lit 14515049) (nat_lit 1606595090) (nat_lit 0) D2M8K2.t6797 from rfl, totK_node, tot6796, tot6797]
  decide +kernel

theorem arows6791 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6791 = true := by
  rw [show D2M8K2.u6791 = KTree.node D2M8K2.t6798 (nat_lit 14516652) (nat_lit 3577977093) (nat_lit 0) D2M8K2.t6799 from rfl, allE_node, rows6798, irow6791, rows6799]
  all_goals rfl

theorem atot6791 : totK PD2M8K2 D2M8K2.u6791 = [229742625436, 770369070554, 652422047422, 111159485812, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u6791 = KTree.node D2M8K2.t6798 (nat_lit 14516652) (nat_lit 3577977093) (nat_lit 0) D2M8K2.t6799 from rfl, totK_node, tot6798, tot6799]
  decide +kernel

theorem arows6795 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6795 = true := by
  rw [show D2M8K2.u6795 = KTree.node D2M8K2.t6800 (nat_lit 14519018) (nat_lit 4139872233) (nat_lit 0) D2M8K2.t6801 from rfl, allE_node, rows6800, irow6795, rows6801]
  all_goals rfl

theorem atot6795 : totK PD2M8K2 D2M8K2.u6795 = [211739018666, 789164038590, 742175288089, 92064370829, 0, 0, 0, 0] := by
  rw [show D2M8K2.u6795 = KTree.node D2M8K2.t6800 (nat_lit 14519018) (nat_lit 4139872233) (nat_lit 0) D2M8K2.t6801 from rfl, totK_node, tot6800, tot6801]
  decide +kernel

theorem arows6796 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6796 = true := by
  rw [show D2M8K2.u6796 = KTree.node D2M8K2.t6802 (nat_lit 14520246) (nat_lit 3110798951) (nat_lit 0) D2M8K2.t6803 from rfl, allE_node, rows6802, irow6796, rows6803]
  all_goals rfl

theorem atot6796 : totK PD2M8K2 D2M8K2.u6796 = [204601796918, 739647529072, 654630609443, 205640317573, 21382878902, 0, 0, 0] := by
  rw [show D2M8K2.u6796 = KTree.node D2M8K2.t6802 (nat_lit 14520246) (nat_lit 3110798951) (nat_lit 0) D2M8K2.t6803 from rfl, totK_node, tot6802, tot6803]
  decide +kernel

theorem arows6798 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6798 = true := by
  rw [show D2M8K2.u6798 = KTree.node D2M8K2.t6804 (nat_lit 14521790) (nat_lit 2975174593) (nat_lit 0) D2M8K2.t6805 from rfl, allE_node, rows6804, irow6798, rows6805]
  all_goals rfl

theorem atot6798 : totK PD2M8K2 D2M8K2.u6798 = [112859636424, 507303130314, 808089836093, 362129070319, 16027375701, 0, 0, 0] := by
  rw [show D2M8K2.u6798 = KTree.node D2M8K2.t6804 (nat_lit 14521790) (nat_lit 2975174593) (nat_lit 0) D2M8K2.t6805 from rfl, totK_node, tot6804, tot6805]
  decide +kernel

theorem arows6799 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6799 = true := by
  rw [show D2M8K2.u6799 = KTree.node D2M8K2.t6806 (nat_lit 14523277) (nat_lit 1382254861) (nat_lit 0) D2M8K2.t6807 from rfl, allE_node, rows6806, irow6799, rows6807]
  all_goals rfl

theorem atot6799 : totK PD2M8K2 D2M8K2.u6799 = [324335651356, 910690573882, 552536273682, 50136681132, 0, 0, 0, 0] := by
  rw [show D2M8K2.u6799 = KTree.node D2M8K2.t6806 (nat_lit 14523277) (nat_lit 1382254861) (nat_lit 0) D2M8K2.t6807 from rfl, totK_node, tot6806, tot6807]
  decide +kernel

theorem arows6802 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6802 = true := by
  rw [show D2M8K2.u6802 = KTree.node D2M8K2.t6808 (nat_lit 14524657) (nat_lit 1353320213) (nat_lit 0) D2M8K2.t6809 from rfl, allE_node, rows6808, irow6802, rows6809]
  all_goals rfl

theorem atot6802 : totK PD2M8K2 D2M8K2.u6802 = [80968783094, 511328923206, 891123100628, 290138651115, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u6802 = KTree.node D2M8K2.t6808 (nat_lit 14524657) (nat_lit 1353320213) (nat_lit 0) D2M8K2.t6809 from rfl, totK_node, tot6808, tot6809]
  decide +kernel

theorem arows6803 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6803 = true := by
  rw [show D2M8K2.u6803 = KTree.node D2M8K2.t6810 (nat_lit 14529755) (nat_lit 2246664516) (nat_lit 0) D2M8K2.t6811 from rfl, allE_node, rows6810, irow6803, rows6811]
  all_goals rfl

theorem atot6803 : totK PD2M8K2 D2M8K2.u6803 = [262070416306, 842651933294, 616083941707, 83395811136, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u6803 = KTree.node D2M8K2.t6810 (nat_lit 14529755) (nat_lit 2246664516) (nat_lit 0) D2M8K2.t6811 from rfl, totK_node, tot6810, tot6811]
  decide +kernel

theorem arows6805 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6805 = true := by
  rw [show D2M8K2.u6805 = KTree.node D2M8K2.t6812 (nat_lit 14532484) (nat_lit 3772546580) (nat_lit 0) D2M8K2.t6813 from rfl, allE_node, rows6812, irow6805, rows6813]
  all_goals rfl

theorem atot6805 : totK PD2M8K2 D2M8K2.u6805 = [191337702465, 720398089808, 752579293119, 160962256374, 3884009855, 0, 0, 0] := by
  rw [show D2M8K2.u6805 = KTree.node D2M8K2.t6812 (nat_lit 14532484) (nat_lit 3772546580) (nat_lit 0) D2M8K2.t6813 from rfl, totK_node, tot6812, tot6813]
  decide +kernel

theorem arows6806 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6806 = true := by
  rw [show D2M8K2.u6806 = KTree.node D2M8K2.t6814 (nat_lit 14533985) (nat_lit 2207073867) (nat_lit 0) D2M8K2.t6815 from rfl, allE_node, rows6814, irow6806, rows6815]
  all_goals rfl

theorem atot6806 : totK PD2M8K2 D2M8K2.u6806 = [236714736590, 793289072742, 668616431207, 114699361601, 1268739303, 0, 0, 0] := by
  rw [show D2M8K2.u6806 = KTree.node D2M8K2.t6814 (nat_lit 14533985) (nat_lit 2207073867) (nat_lit 0) D2M8K2.t6815 from rfl, totK_node, tot6814, tot6815]
  decide +kernel

theorem arows6811 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6811 = true := by
  rw [show D2M8K2.u6811 = KTree.node D2M8K2.t6816 (nat_lit 14535690) (nat_lit 3745201620) (nat_lit 0) D2M8K2.t6817 from rfl, allE_node, rows6816, irow6811, rows6817]
  all_goals rfl

theorem atot6811 : totK PD2M8K2 D2M8K2.u6811 = [0, 405955416251, 956148568010, 403431580911, 22144019970, 0, 0, 0] := by
  rw [show D2M8K2.u6811 = KTree.node D2M8K2.t6816 (nat_lit 14535690) (nat_lit 3745201620) (nat_lit 0) D2M8K2.t6817 from rfl, totK_node, tot6816, tot6817]
  decide +kernel

theorem arows6812 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6812 = true := by
  rw [show D2M8K2.u6812 = KTree.node D2M8K2.t6818 (nat_lit 14537258) (nat_lit 3916020761) (nat_lit 0) D2M8K2.t6819 from rfl, allE_node, rows6818, irow6812, rows6819]
  all_goals rfl

theorem atot6812 : totK PD2M8K2 D2M8K2.u6812 = [0, 268774140493, 832586214243, 558687128687, 72381501572, 1206465782, 0, 0] := by
  rw [show D2M8K2.u6812 = KTree.node D2M8K2.t6818 (nat_lit 14537258) (nat_lit 3916020761) (nat_lit 0) D2M8K2.t6819 from rfl, totK_node, tot6818, tot6819]
  decide +kernel

theorem arows6814 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6814 = true := by
  rw [show D2M8K2.u6814 = KTree.node D2M8K2.t6820 (nat_lit 14539754) (nat_lit 4139872233) (nat_lit 0) D2M8K2.t6821 from rfl, allE_node, rows6820, irow6814, rows6821]
  all_goals rfl

theorem atot6814 : totK PD2M8K2 D2M8K2.u6814 = [0, 218412728770, 819451729319, 698262780447, 73917406561, 0, 0, 0] := by
  rw [show D2M8K2.u6814 = KTree.node D2M8K2.t6820 (nat_lit 14539754) (nat_lit 4139872233) (nat_lit 0) D2M8K2.t6821 from rfl, totK_node, tot6820, tot6821]
  decide +kernel

theorem arows6815 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6815 = true := by
  rw [show D2M8K2.u6815 = KTree.node D2M8K2.t6822 (nat_lit 14541003) (nat_lit 3740217982) (nat_lit 0) D2M8K2.t6823 from rfl, allE_node, rows6822, irow6815, rows6823]
  all_goals rfl

theorem atot6815 : totK PD2M8K2 D2M8K2.u6815 = [0, 374980515142, 959920096487, 452003699541, 28982520623, 0, 0, 0] := by
  rw [show D2M8K2.u6815 = KTree.node D2M8K2.t6822 (nat_lit 14541003) (nat_lit 3740217982) (nat_lit 0) D2M8K2.t6823 from rfl, totK_node, tot6822, tot6823]
  decide +kernel

theorem arows6818 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6818 = true := by
  rw [show D2M8K2.u6818 = KTree.node D2M8K2.t6824 (nat_lit 14544216) (nat_lit 3026268009) (nat_lit 0) D2M8K2.t6825 from rfl, allE_node, rows6824, irow6818, rows6825]
  all_goals rfl

theorem atot6818 : totK PD2M8K2 D2M8K2.u6818 = [0, 265114455954, 828456839980, 607423717636, 85186751614, 1162935789, 0, 0] := by
  rw [show D2M8K2.u6818 = KTree.node D2M8K2.t6824 (nat_lit 14544216) (nat_lit 3026268009) (nat_lit 0) D2M8K2.t6825 from rfl, totK_node, tot6824, tot6825]
  decide +kernel

theorem arows6819 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6819 = true := by
  rw [show D2M8K2.u6819 = KTree.node D2M8K2.t6826 (nat_lit 14545900) (nat_lit 3710658952) (nat_lit 0) D2M8K2.t6827 from rfl, allE_node, rows6826, irow6819, rows6827]
  all_goals rfl

theorem atot6819 : totK PD2M8K2 D2M8K2.u6819 = [0, 161596490957, 643912770486, 724361080503, 212412055533, 11853261585, 0, 0] := by
  rw [show D2M8K2.u6819 = KTree.node D2M8K2.t6826 (nat_lit 14545900) (nat_lit 3710658952) (nat_lit 0) D2M8K2.t6827 from rfl, totK_node, tot6826, tot6827]
  decide +kernel

theorem arows6821 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6821 = true := by
  rw [show D2M8K2.u6821 = KTree.node D2M8K2.t6828 (nat_lit 14551062) (nat_lit 3187254211) (nat_lit 0) D2M8K2.t6829 from rfl, allE_node, rows6828, irow6821, rows6829]
  all_goals rfl

theorem atot6821 : totK PD2M8K2 D2M8K2.u6821 = [0, 180062671018, 795394629361, 717103962053, 92042267538, 1021600638, 0, 0] := by
  rw [show D2M8K2.u6821 = KTree.node D2M8K2.t6828 (nat_lit 14551062) (nat_lit 3187254211) (nat_lit 0) D2M8K2.t6829 from rfl, totK_node, tot6828, tot6829]
  decide +kernel

theorem arows6822 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6822 = true := by
  rw [show D2M8K2.u6822 = KTree.node D2M8K2.t6830 (nat_lit 14553576) (nat_lit 2233721318) (nat_lit 0) D2M8K2.t6831 from rfl, allE_node, rows6830, irow6822, rows6831]
  all_goals rfl

theorem atot6822 : totK PD2M8K2 D2M8K2.u6822 = [0, 300474096028, 809842991434, 564608571266, 101741987969, 3552795014, 0, 0] := by
  rw [show D2M8K2.u6822 = KTree.node D2M8K2.t6830 (nat_lit 14553576) (nat_lit 2233721318) (nat_lit 0) D2M8K2.t6831 from rfl, totK_node, tot6830, tot6831]
  decide +kernel

theorem arows6826 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6826 = true := by
  rw [show D2M8K2.u6826 = KTree.node D2M8K2.t6832 (nat_lit 14556782) (nat_lit 1849197893) (nat_lit 0) D2M8K2.t6833 from rfl, allE_node, rows6832, irow6826, rows6833]
  all_goals rfl

theorem atot6826 : totK PD2M8K2 D2M8K2.u6826 = [242887224404, 698596958346, 607213392080, 232072459402, 17476474534, 0, 0, 0] := by
  rw [show D2M8K2.u6826 = KTree.node D2M8K2.t6832 (nat_lit 14556782) (nat_lit 1849197893) (nat_lit 0) D2M8K2.t6833 from rfl, totK_node, tot6832, tot6833]
  decide +kernel

theorem arows6827 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6827 = true := by
  rw [show D2M8K2.u6827 = KTree.node D2M8K2.t6834 (nat_lit 14558401) (nat_lit 1575612183) (nat_lit 0) D2M8K2.t6835 from rfl, allE_node, rows6834, irow6827, rows6835]
  all_goals rfl

theorem atot6827 : totK PD2M8K2 D2M8K2.u6827 = [153396427969, 704389472891, 772239741530, 136906254724, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u6827 = KTree.node D2M8K2.t6834 (nat_lit 14558401) (nat_lit 1575612183) (nat_lit 0) D2M8K2.t6835 from rfl, totK_node, tot6834, tot6835]
  decide +kernel

theorem arows6829 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6829 = true := by
  rw [show D2M8K2.u6829 = KTree.node D2M8K2.t6836 (nat_lit 14560757) (nat_lit 2394265572) (nat_lit 0) D2M8K2.t6837 from rfl, allE_node, rows6836, irow6829, rows6837]
  all_goals rfl

theorem atot6829 : totK PD2M8K2 D2M8K2.u6829 = [319710817639, 876478918333, 589934560183, 62941666682, 0, 0, 0, 0] := by
  rw [show D2M8K2.u6829 = KTree.node D2M8K2.t6836 (nat_lit 14560757) (nat_lit 2394265572) (nat_lit 0) D2M8K2.t6837 from rfl, totK_node, tot6836, tot6837]
  decide +kernel

theorem arows6830 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6830 = true := by
  rw [show D2M8K2.u6830 = KTree.node D2M8K2.t6838 (nat_lit 14562337) (nat_lit 649394240) (nat_lit 0) D2M8K2.t6839 from rfl, allE_node, rows6838, irow6830, rows6839]
  all_goals rfl

theorem atot6830 : totK PD2M8K2 D2M8K2.u6830 = [88459214294, 542191752829, 808425290355, 351853176226, 28205077490, 0, 0, 0] := by
  rw [show D2M8K2.u6830 = KTree.node D2M8K2.t6838 (nat_lit 14562337) (nat_lit 649394240) (nat_lit 0) D2M8K2.t6839 from rfl, totK_node, tot6838, tot6839]
  decide +kernel

theorem arows6833 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6833 = true := by
  rw [show D2M8K2.u6833 = KTree.node D2M8K2.t6840 (nat_lit 14567130) (nat_lit 3901361371) (nat_lit 0) D2M8K2.t6841 from rfl, allE_node, rows6840, irow6833, rows6841]
  all_goals rfl

theorem atot6833 : totK PD2M8K2 D2M8K2.u6833 = [228925180663, 685640757791, 679163565596, 223046710276, 9353868799, 0, 0, 0] := by
  rw [show D2M8K2.u6833 = KTree.node D2M8K2.t6840 (nat_lit 14567130) (nat_lit 3901361371) (nat_lit 0) D2M8K2.t6841 from rfl, totK_node, tot6840, tot6841]
  decide +kernel

theorem arows6834 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6834 = true := by
  rw [show D2M8K2.u6834 = KTree.node D2M8K2.t6842 (nat_lit 14568628) (nat_lit 3387915907) (nat_lit 0) D2M8K2.t6843 from rfl, allE_node, rows6842, irow6834, rows6843]
  all_goals rfl

theorem atot6834 : totK PD2M8K2 D2M8K2.u6834 = [197475585436, 769591608880, 722026232087, 115995502709, 1198073392, 0, 0, 0] := by
  rw [show D2M8K2.u6834 = KTree.node D2M8K2.t6842 (nat_lit 14568628) (nat_lit 3387915907) (nat_lit 0) D2M8K2.t6843 from rfl, totK_node, tot6842, tot6843]
  decide +kernel

theorem arows6836 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6836 = true := by
  rw [show D2M8K2.u6836 = KTree.node D2M8K2.t6844 (nat_lit 14570329) (nat_lit 1489021467) (nat_lit 0) D2M8K2.t6845 from rfl, allE_node, rows6844, irow6836, rows6845]
  all_goals rfl

theorem atot6836 : totK PD2M8K2 D2M8K2.u6836 = [172824233102, 659504789899, 730741849679, 221609338631, 12052611869, 0, 0, 0] := by
  rw [show D2M8K2.u6836 = KTree.node D2M8K2.t6844 (nat_lit 14570329) (nat_lit 1489021467) (nat_lit 0) D2M8K2.t6845 from rfl, totK_node, tot6844, tot6845]
  decide +kernel

theorem arows6837 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6837 = true := by
  rw [show D2M8K2.u6837 = KTree.node D2M8K2.t6846 (nat_lit 14575434) (nat_lit 3835629738) (nat_lit 0) D2M8K2.t6847 from rfl, allE_node, rows6846, irow6837, rows6847]
  all_goals rfl

theorem atot6837 : totK PD2M8K2 D2M8K2.u6837 = [254342633005, 789132945399, 651606882916, 115098633832, 1268739303, 0, 0, 0] := by
  rw [show D2M8K2.u6837 = KTree.node D2M8K2.t6846 (nat_lit 14575434) (nat_lit 3835629738) (nat_lit 0) D2M8K2.t6847 from rfl, totK_node, tot6846, tot6847]
  decide +kernel

theorem arows6843 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6843 = true := by
  rw [show D2M8K2.u6843 = KTree.node D2M8K2.t6848 (nat_lit 14577133) (nat_lit 1332509896) (nat_lit 0) D2M8K2.t6849 from rfl, allE_node, rows6848, irow6843, rows6849]
  all_goals rfl

theorem atot6843 : totK PD2M8K2 D2M8K2.u6843 = [0, 403163650055, 960014372756, 399181446722, 22143218390, 0, 0, 0] := by
  rw [show D2M8K2.u6843 = KTree.node D2M8K2.t6848 (nat_lit 14577133) (nat_lit 1332509896) (nat_lit 0) D2M8K2.t6849 from rfl, totK_node, tot6848, tot6849]
  decide +kernel

theorem arows6844 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6844 = true := by
  rw [show D2M8K2.u6844 = KTree.node D2M8K2.t6850 (nat_lit 14578715) (nat_lit 1235489335) (nat_lit 0) D2M8K2.t6851 from rfl, allE_node, rows6850, irow6844, rows6851]
  all_goals rfl

theorem atot6844 : totK PD2M8K2 D2M8K2.u6844 = [0, 281958378440, 833800314252, 556136574366, 72146946033, 1239866073, 0, 0] := by
  rw [show D2M8K2.u6844 = KTree.node D2M8K2.t6850 (nat_lit 14578715) (nat_lit 1235489335) (nat_lit 0) D2M8K2.t6851 from rfl, totK_node, tot6850, tot6851]
  decide +kernel

theorem arows6846 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6846 = true := by
  rw [show D2M8K2.u6846 = KTree.node D2M8K2.t6852 (nat_lit 14581230) (nat_lit 4040525131) (nat_lit 0) D2M8K2.t6853 from rfl, allE_node, rows6852, irow6846, rows6853]
  all_goals rfl

theorem atot6846 : totK PD2M8K2 D2M8K2.u6846 = [0, 231479500550, 817037791687, 693209909026, 72367244279, 0, 0, 0] := by
  rw [show D2M8K2.u6846 = KTree.node D2M8K2.t6852 (nat_lit 14581230) (nat_lit 4040525131) (nat_lit 0) D2M8K2.t6853 from rfl, totK_node, tot6852, tot6853]
  decide +kernel

theorem arows6847 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6847 = true := by
  rw [show D2M8K2.u6847 = KTree.node D2M8K2.t6854 (nat_lit 14582501) (nat_lit 2255453641) (nat_lit 0) D2M8K2.t6855 from rfl, allE_node, rows6854, irow6847, rows6855]
  all_goals rfl

theorem atot6847 : totK PD2M8K2 D2M8K2.u6847 = [0, 347881973178, 933933600654, 491965954458, 36169031821, 0, 0, 0] := by
  rw [show D2M8K2.u6847 = KTree.node D2M8K2.t6854 (nat_lit 14582501) (nat_lit 2255453641) (nat_lit 0) D2M8K2.t6855 from rfl, totK_node, tot6854, tot6855]
  decide +kernel

theorem arows6850 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6850 = true := by
  rw [show D2M8K2.u6850 = KTree.node D2M8K2.t6856 (nat_lit 14589217) (nat_lit 1553244865) (nat_lit 0) D2M8K2.t6857 from rfl, allE_node, rows6856, irow6850, rows6857]
  all_goals rfl

theorem atot6850 : totK PD2M8K2 D2M8K2.u6850 = [0, 253152625477, 799673746626, 629334669808, 96569989117, 1171084559, 0, 0] := by
  rw [show D2M8K2.u6850 = KTree.node D2M8K2.t6856 (nat_lit 14589217) (nat_lit 1553244865) (nat_lit 0) D2M8K2.t6857 from rfl, totK_node, tot6856, tot6857]
  decide +kernel

theorem arows6851 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6851 = true := by
  rw [show D2M8K2.u6851 = KTree.node D2M8K2.t6858 (nat_lit 14590912) (nat_lit 1361865874) (nat_lit 0) D2M8K2.t6859 from rfl, allE_node, rows6858, irow6851, rows6859]
  all_goals rfl

theorem atot6851 : totK PD2M8K2 D2M8K2.u6851 = [0, 172179909266, 665529542259, 716925365342, 206521539296, 11934365838, 0, 0] := by
  rw [show D2M8K2.u6851 = KTree.node D2M8K2.t6858 (nat_lit 14590912) (nat_lit 1361865874) (nat_lit 0) D2M8K2.t6859 from rfl, totK_node, tot6858, tot6859]
  decide +kernel

theorem arows6853 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6853 = true := by
  rw [show D2M8K2.u6853 = KTree.node D2M8K2.t6860 (nat_lit 14595788) (nat_lit 3098909808) (nat_lit 0) D2M8K2.t6861 from rfl, allE_node, rows6860, irow6853, rows6861]
  all_goals rfl

theorem atot6853 : totK PD2M8K2 D2M8K2.u6853 = [90585905067, 447855326834, 781623325316, 460551259930, 38720155712, 0, 0, 0] := by
  rw [show D2M8K2.u6853 = KTree.node D2M8K2.t6860 (nat_lit 14595788) (nat_lit 3098909808) (nat_lit 0) D2M8K2.t6861 from rfl, totK_node, tot6860, tot6861]
  decide +kernel

theorem arows6854 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6854 = true := by
  rw [show D2M8K2.u6854 = KTree.node D2M8K2.t6862 (nat_lit 14640745) (nat_lit 1446174803) (nat_lit 0) D2M8K2.t6863 from rfl, allE_node, rows6862, irow6854, rows6863]
  all_goals rfl

theorem atot6854 : totK PD2M8K2 D2M8K2.u6854 = [323438167067, 896852868243, 516724949402, 39155751818, 0, 0, 0, 0] := by
  rw [show D2M8K2.u6854 = KTree.node D2M8K2.t6862 (nat_lit 14640745) (nat_lit 1446174803) (nat_lit 0) D2M8K2.t6863 from rfl, totK_node, tot6862, tot6863]
  decide +kernel

theorem arows6858 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6858 = true := by
  rw [show D2M8K2.u6858 = KTree.node D2M8K2.t6864 (nat_lit 14642587) (nat_lit 2103079748) (nat_lit 0) D2M8K2.t6865 from rfl, allE_node, rows6864, irow6858, rows6865]
  all_goals rfl

theorem atot6858 : totK PD2M8K2 D2M8K2.u6858 = [138002238038, 674161194906, 850557834889, 156136786423, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u6858 = KTree.node D2M8K2.t6864 (nat_lit 14642587) (nat_lit 2103079748) (nat_lit 0) D2M8K2.t6865 from rfl, totK_node, tot6864, tot6865]
  decide +kernel

theorem arows6859 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6859 = true := by
  rw [show D2M8K2.u6859 = KTree.node D2M8K2.t6866 (nat_lit 14644310) (nat_lit 3926217980) (nat_lit 0) D2M8K2.t6867 from rfl, allE_node, rows6866, irow6859, rows6867]
  all_goals rfl

theorem atot6859 : totK PD2M8K2 D2M8K2.u6859 = [282849632478, 885791732004, 586943266066, 62927596448, 0, 0, 0, 0] := by
  rw [show D2M8K2.u6859 = KTree.node D2M8K2.t6866 (nat_lit 14644310) (nat_lit 3926217980) (nat_lit 0) D2M8K2.t6867 from rfl, totK_node, tot6866, tot6867]
  decide +kernel

theorem arows6861 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6861 = true := by
  rw [show D2M8K2.u6861 = KTree.node D2M8K2.t6868 (nat_lit 14645816) (nat_lit 1936858591) (nat_lit 0) D2M8K2.t6869 from rfl, allE_node, rows6868, irow6861, rows6869]
  all_goals rfl

theorem atot6861 : totK PD2M8K2 D2M8K2.u6861 = [0, 330050195113, 915940258059, 508036894443, 37370690916, 0, 0, 0] := by
  rw [show D2M8K2.u6861 = KTree.node D2M8K2.t6868 (nat_lit 14645816) (nat_lit 1936858591) (nat_lit 0) D2M8K2.t6869 from rfl, totK_node, tot6868, tot6869]
  decide +kernel

theorem arows6862 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6862 = true := by
  rw [show D2M8K2.u6862 = KTree.node D2M8K2.t6870 (nat_lit 14647115) (nat_lit 2888716578) (nat_lit 0) D2M8K2.t6871 from rfl, allE_node, rows6870, irow6862, rows6871]
  all_goals rfl

theorem atot6862 : totK PD2M8K2 D2M8K2.u6862 = [384196173977, 932770897933, 462863297448, 35398108280, 0, 0, 0, 0] := by
  rw [show D2M8K2.u6862 = KTree.node D2M8K2.t6870 (nat_lit 14647115) (nat_lit 2888716578) (nat_lit 0) D2M8K2.t6871 from rfl, totK_node, tot6870, tot6871]
  decide +kernel

theorem arows6865 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6865 = true := by
  rw [show D2M8K2.u6865 = KTree.node D2M8K2.t6872 (nat_lit 14648677) (nat_lit 1125277340) (nat_lit 0) D2M8K2.t6873 from rfl, allE_node, rows6872, irow6865, rows6873]
  all_goals rfl

theorem atot6865 : totK PD2M8K2 D2M8K2.u6865 = [34764112273, 526246604836, 931448753947, 282685092032, 13020426360, 0, 0, 0] := by
  rw [show D2M8K2.u6865 = KTree.node D2M8K2.t6872 (nat_lit 14648677) (nat_lit 1125277340) (nat_lit 0) D2M8K2.t6873 from rfl, totK_node, tot6872, tot6873]
  decide +kernel

theorem arows6866 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6866 = true := by
  rw [show D2M8K2.u6866 = KTree.node D2M8K2.t6874 (nat_lit 14650510) (nat_lit 3606856051) (nat_lit 0) D2M8K2.t6875 from rfl, allE_node, rows6874, irow6866, rows6875]
  all_goals rfl

theorem atot6866 : totK PD2M8K2 D2M8K2.u6866 = [349582986000, 900540215681, 507694115915, 45860096625, 0, 0, 0, 0] := by
  rw [show D2M8K2.u6866 = KTree.node D2M8K2.t6874 (nat_lit 14650510) (nat_lit 3606856051) (nat_lit 0) D2M8K2.t6875 from rfl, totK_node, tot6874, tot6875]
  decide +kernel

theorem arows6868 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6868 = true := by
  rw [show D2M8K2.u6868 = KTree.node D2M8K2.t6876 (nat_lit 14652105) (nat_lit 1390210214) (nat_lit 0) D2M8K2.t6877 from rfl, allE_node, rows6876, irow6868, rows6877]
  all_goals rfl

theorem atot6868 : totK PD2M8K2 D2M8K2.u6868 = [53441125967, 536426052952, 907247643166, 268307721442, 10571929038, 0, 0, 0] := by
  rw [show D2M8K2.u6868 = KTree.node D2M8K2.t6876 (nat_lit 14652105) (nat_lit 1390210214) (nat_lit 0) D2M8K2.t6877 from rfl, totK_node, tot6876, tot6877]
  decide +kernel

theorem arows6869 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6869 = true := by
  rw [show D2M8K2.u6869 = KTree.node D2M8K2.t6878 (nat_lit 14657429) (nat_lit 2193070825) (nat_lit 0) D2M8K2.t6879 from rfl, allE_node, rows6878, irow6869, rows6879]
  all_goals rfl

theorem atot6869 : totK PD2M8K2 D2M8K2.u6869 = [353693544884, 923178088072, 520259064631, 49484651182, 0, 0, 0, 0] := by
  rw [show D2M8K2.u6869 = KTree.node D2M8K2.t6878 (nat_lit 14657429) (nat_lit 2193070825) (nat_lit 0) D2M8K2.t6879 from rfl, totK_node, tot6878, tot6879]
  decide +kernel

theorem arows6874 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6874 = true := by
  rw [show D2M8K2.u6874 = KTree.node D2M8K2.t6880 (nat_lit 14658899) (nat_lit 2902633054) (nat_lit 0) D2M8K2.t6881 from rfl, allE_node, rows6880, irow6874, rows6881]
  all_goals rfl

theorem atot6874 : totK PD2M8K2 D2M8K2.u6874 = [93924006320, 611216357318, 881868486962, 225905610291, 4967996017, 0, 0, 0] := by
  rw [show D2M8K2.u6874 = KTree.node D2M8K2.t6880 (nat_lit 14658899) (nat_lit 2902633054) (nat_lit 0) D2M8K2.t6881 from rfl, totK_node, tot6880, tot6881]
  decide +kernel

theorem arows6875 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6875 = true := by
  rw [show D2M8K2.u6875 = KTree.node D2M8K2.t6882 (nat_lit 14660505) (nat_lit 1726355408) (nat_lit 0) D2M8K2.t6883 from rfl, allE_node, rows6882, irow6875, rows6883]
  all_goals rfl

theorem atot6875 : totK PD2M8K2 D2M8K2.u6875 = [0, 352249032921, 940411336130, 454421718309, 26435335346, 0, 0, 0] := by
  rw [show D2M8K2.u6875 = KTree.node D2M8K2.t6882 (nat_lit 14660505) (nat_lit 1726355408) (nat_lit 0) D2M8K2.t6883 from rfl, totK_node, tot6882, tot6883]
  decide +kernel

theorem arows6877 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6877 = true := by
  rw [show D2M8K2.u6877 = KTree.node D2M8K2.t6884 (nat_lit 14662140) (nat_lit 3235948554) (nat_lit 0) D2M8K2.t6885 from rfl, allE_node, rows6884, irow6877, rows6885]
  all_goals rfl

theorem atot6877 : totK PD2M8K2 D2M8K2.u6877 = [0, 152755471415, 725072638830, 753977324027, 103633546549, 1310285577, 0, 0] := by
  rw [show D2M8K2.u6877 = KTree.node D2M8K2.t6884 (nat_lit 14662140) (nat_lit 3235948554) (nat_lit 0) D2M8K2.t6885 from rfl, totK_node, tot6884, tot6885]
  decide +kernel

theorem arows6878 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6878 = true := by
  rw [show D2M8K2.u6878 = KTree.node D2M8K2.t6886 (nat_lit 14664448) (nat_lit 3778141658) (nat_lit 0) D2M8K2.t6887 from rfl, allE_node, rows6886, irow6878, rows6887]
  all_goals rfl

theorem atot6878 : totK PD2M8K2 D2M8K2.u6878 = [0, 332755836889, 867759763049, 568595374079, 54624720949, 0, 0, 0] := by
  rw [show D2M8K2.u6878 = KTree.node D2M8K2.t6886 (nat_lit 14664448) (nat_lit 3778141658) (nat_lit 0) D2M8K2.t6887 from rfl, totK_node, tot6886, tot6887]
  decide +kernel

theorem arows6881 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6881 = true := by
  rw [show D2M8K2.u6881 = KTree.node D2M8K2.t6888 (nat_lit 14667467) (nat_lit 2354094115) (nat_lit 0) D2M8K2.t6889 from rfl, allE_node, rows6888, irow6881, rows6889]
  all_goals rfl

theorem atot6881 : totK PD2M8K2 D2M8K2.u6881 = [0, 353854332922, 943657555773, 494836971935, 36852717805, 0, 0, 0] := by
  rw [show D2M8K2.u6881 = KTree.node D2M8K2.t6888 (nat_lit 14667467) (nat_lit 2354094115) (nat_lit 0) D2M8K2.t6889 from rfl, totK_node, tot6888, tot6889]
  decide +kernel

theorem arows6882 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6882 = true := by
  rw [show D2M8K2.u6882 = KTree.node D2M8K2.t6890 (nat_lit 14668996) (nat_lit 3793800199) (nat_lit 0) D2M8K2.t6891 from rfl, allE_node, rows6890, irow6882, rows6891]
  all_goals rfl

theorem atot6882 : totK PD2M8K2 D2M8K2.u6882 = [0, 156799562566, 698545282985, 750624475733, 153213131229, 4879840392, 0, 0] := by
  rw [show D2M8K2.u6882 = KTree.node D2M8K2.t6890 (nat_lit 14668996) (nat_lit 3793800199) (nat_lit 0) D2M8K2.t6891 from rfl, totK_node, tot6890, tot6891]
  decide +kernel

theorem arows6884 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6884 = true := by
  rw [show D2M8K2.u6884 = KTree.node D2M8K2.t6892 (nat_lit 14671073) (nat_lit 2064381835) (nat_lit 0) D2M8K2.t6893 from rfl, allE_node, rows6892, irow6884, rows6893]
  all_goals rfl

theorem atot6884 : totK PD2M8K2 D2M8K2.u6884 = [0, 283105249941, 844558219277, 589529409272, 66950798421, 0, 0, 0] := by
  rw [show D2M8K2.u6884 = KTree.node D2M8K2.t6892 (nat_lit 14671073) (nat_lit 2064381835) (nat_lit 0) D2M8K2.t6893 from rfl, totK_node, tot6892, tot6893]
  decide +kernel

theorem arows6885 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6885 = true := by
  rw [show D2M8K2.u6885 = KTree.node D2M8K2.t6894 (nat_lit 14672603) (nat_lit 2138785766) (nat_lit 0) D2M8K2.t6895 from rfl, allE_node, rows6894, irow6885, rows6895]
  all_goals rfl

theorem atot6885 : totK PD2M8K2 D2M8K2.u6885 = [0, 117928812513, 672354048453, 785894809540, 165669037400, 4931404646, 0, 0] := by
  rw [show D2M8K2.u6885 = KTree.node D2M8K2.t6894 (nat_lit 14672603) (nat_lit 2138785766) (nat_lit 0) D2M8K2.t6895 from rfl, totK_node, tot6894, tot6895]
  decide +kernel

theorem arows6889 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6889 = true := by
  rw [show D2M8K2.u6889 = KTree.node D2M8K2.t6896 (nat_lit 14678150) (nat_lit 3885612275) (nat_lit 0) D2M8K2.t6897 from rfl, allE_node, rows6896, irow6889, rows6897]
  all_goals rfl

theorem atot6889 : totK PD2M8K2 D2M8K2.u6889 = [0, 351800156843, 916848213336, 516477507735, 45987044522, 0, 0, 0] := by
  rw [show D2M8K2.u6889 = KTree.node D2M8K2.t6896 (nat_lit 14678150) (nat_lit 3885612275) (nat_lit 0) D2M8K2.t6897 from rfl, totK_node, tot6896, tot6897]
  decide +kernel

theorem arows6890 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6890 = true := by
  rw [show D2M8K2.u6890 = KTree.node D2M8K2.t6898 (nat_lit 14679629) (nat_lit 1762557174) (nat_lit 0) D2M8K2.t6899 from rfl, allE_node, rows6898, irow6890, rows6899]
  all_goals rfl

theorem atot6890 : totK PD2M8K2 D2M8K2.u6890 = [0, 93669046305, 608916672598, 847871357195, 213591242831, 5842784248, 0, 0] := by
  rw [show D2M8K2.u6890 = KTree.node D2M8K2.t6898 (nat_lit 14679629) (nat_lit 1762557174) (nat_lit 0) D2M8K2.t6899 from rfl, totK_node, tot6898, tot6899]
  decide +kernel

theorem arows6892 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6892 = true := by
  rw [show D2M8K2.u6892 = KTree.node D2M8K2.t6900 (nat_lit 14681305) (nat_lit 1504782725) (nat_lit 0) D2M8K2.t6901 from rfl, allE_node, rows6900, irow6892, rows6901]
  all_goals rfl

theorem atot6892 : totK PD2M8K2 D2M8K2.u6892 = [0, 263893211406, 745593756646, 575482588735, 183280481406, 15908383818, 0, 0] := by
  rw [show D2M8K2.u6892 = KTree.node D2M8K2.t6900 (nat_lit 14681305) (nat_lit 1504782725) (nat_lit 0) D2M8K2.t6901 from rfl, totK_node, tot6900, tot6901]
  decide +kernel

theorem arows6893 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6893 = true := by
  rw [show D2M8K2.u6893 = KTree.node D2M8K2.t6902 (nat_lit 14682815) (nat_lit 2760538962) (nat_lit 0) D2M8K2.t6903 from rfl, allE_node, rows6902, irow6893, rows6903]
  all_goals rfl

theorem atot6893 : totK PD2M8K2 D2M8K2.u6893 = [0, 169595826744, 728446490016, 763264654302, 127002150737, 1369150432, 0, 0] := by
  rw [show D2M8K2.u6893 = KTree.node D2M8K2.t6902 (nat_lit 14682815) (nat_lit 2760538962) (nat_lit 0) D2M8K2.t6903 from rfl, totK_node, tot6902, tot6903]
  decide +kernel

theorem arows6896 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6896 = true := by
  rw [show D2M8K2.u6896 = KTree.node D2M8K2.t6904 (nat_lit 14688358) (nat_lit 3761356607) (nat_lit 0) D2M8K2.t6905 from rfl, allE_node, rows6904, irow6896, rows6905]
  all_goals rfl

theorem atot6896 : totK PD2M8K2 D2M8K2.u6896 = [0, 308215439601, 864986920194, 578011459327, 59283919837, 0, 0, 0] := by
  rw [show D2M8K2.u6896 = KTree.node D2M8K2.t6904 (nat_lit 14688358) (nat_lit 3761356607) (nat_lit 0) D2M8K2.t6905 from rfl, totK_node, tot6904, tot6905]
  decide +kernel

theorem arows6897 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6897 = true := by
  rw [show D2M8K2.u6897 = KTree.node D2M8K2.t6906 (nat_lit 14689870) (nat_lit 3867413933) (nat_lit 0) D2M8K2.t6907 from rfl, allE_node, rows6906, irow6897, rows6907]
  all_goals rfl

theorem atot6897 : totK PD2M8K2 D2M8K2.u6897 = [0, 106069037658, 638436907133, 837739817343, 193176504787, 5172807878, 0, 0] := by
  rw [show D2M8K2.u6897 = KTree.node D2M8K2.t6906 (nat_lit 14689870) (nat_lit 3867413933) (nat_lit 0) D2M8K2.t6907 from rfl, totK_node, tot6906, tot6907]
  decide +kernel

theorem arows6899 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6899 = true := by
  rw [show D2M8K2.u6899 = KTree.node D2M8K2.t6908 (nat_lit 14691935) (nat_lit 2026048166) (nat_lit 0) D2M8K2.t6909 from rfl, allE_node, rows6908, irow6899, rows6909]
  all_goals rfl

theorem atot6899 : totK PD2M8K2 D2M8K2.u6899 = [0, 311870886881, 869528634743, 554695115546, 56382733122, 0, 0, 0] := by
  rw [show D2M8K2.u6899 = KTree.node D2M8K2.t6908 (nat_lit 14691935) (nat_lit 2026048166) (nat_lit 0) D2M8K2.t6909 from rfl, totK_node, tot6908, tot6909]
  decide +kernel

theorem arows6900 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6900 = true := by
  rw [show D2M8K2.u6900 = KTree.node D2M8K2.t6910 (nat_lit 14693592) (nat_lit 2819035268) (nat_lit 0) D2M8K2.t6911 from rfl, allE_node, rows6910, irow6900, rows6911]
  all_goals rfl

theorem atot6900 : totK PD2M8K2 D2M8K2.u6900 = [0, 80931028606, 592376310672, 885580270510, 218297924052, 5228939780, 0, 0] := by
  rw [show D2M8K2.u6900 = KTree.node D2M8K2.t6910 (nat_lit 14693592) (nat_lit 2819035268) (nat_lit 0) D2M8K2.t6911 from rfl, totK_node, tot6910, tot6911]
  decide +kernel

theorem arows6908 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6908 = true := by
  rw [show D2M8K2.u6908 = KTree.node D2M8K2.t6912 (nat_lit 14695878) (nat_lit 3878967719) (nat_lit 0) D2M8K2.t6913 from rfl, allE_node, rows6912, irow6908, rows6913]
  all_goals rfl

theorem atot6908 : totK PD2M8K2 D2M8K2.u6908 = [0, 308615905909, 897753304728, 516453829116, 44617709067, 0, 0, 0] := by
  rw [show D2M8K2.u6908 = KTree.node D2M8K2.t6912 (nat_lit 14695878) (nat_lit 3878967719) (nat_lit 0) D2M8K2.t6913 from rfl, totK_node, tot6912, tot6913]
  decide +kernel

theorem arows6909 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6909 = true := by
  rw [show D2M8K2.u6909 = KTree.node D2M8K2.t6914 (nat_lit 14698471) (nat_lit 2305037164) (nat_lit 0) D2M8K2.t6915 from rfl, allE_node, rows6914, irow6909, rows6915]
  all_goals rfl

theorem atot6909 : totK PD2M8K2 D2M8K2.u6909 = [0, 247890128457, 792966712008, 664095326656, 93292856345, 1096505104, 0, 0] := by
  rw [show D2M8K2.u6909 = KTree.node D2M8K2.t6914 (nat_lit 14698471) (nat_lit 2305037164) (nat_lit 0) D2M8K2.t6915 from rfl, totK_node, tot6914, tot6915]
  decide +kernel

theorem arows6911 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6911 = true := by
  rw [show D2M8K2.u6911 = KTree.node D2M8K2.t6916 (nat_lit 14699974) (nat_lit 3485877379) (nat_lit 0) D2M8K2.t6917 from rfl, allE_node, rows6916, irow6911, rows6917]
  all_goals rfl

theorem atot6911 : totK PD2M8K2 D2M8K2.u6911 = [0, 177879713851, 745744222964, 741419480652, 129602001667, 1268739303, 0, 0] := by
  rw [show D2M8K2.u6911 = KTree.node D2M8K2.t6916 (nat_lit 14699974) (nat_lit 3485877379) (nat_lit 0) D2M8K2.t6917 from rfl, totK_node, tot6916, tot6917]
  decide +kernel

theorem arows6912 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6912 = true := by
  rw [show D2M8K2.u6912 = KTree.node D2M8K2.t6918 (nat_lit 14701668) (nat_lit 3265186967) (nat_lit 0) D2M8K2.t6919 from rfl, allE_node, rows6918, irow6912, rows6919]
  all_goals rfl

theorem atot6912 : totK PD2M8K2 D2M8K2.u6912 = [0, 0, 387537333498, 957712680817, 395973054486, 22017470223, 0, 0] := by
  rw [show D2M8K2.u6912 = KTree.node D2M8K2.t6918 (nat_lit 14701668) (nat_lit 3265186967) (nat_lit 0) D2M8K2.t6919 from rfl, totK_node, tot6918, tot6919]
  decide +kernel

theorem arows6915 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6915 = true := by
  rw [show D2M8K2.u6915 = KTree.node D2M8K2.t6920 (nat_lit 14703199) (nat_lit 2362243340) (nat_lit 0) D2M8K2.t6921 from rfl, allE_node, rows6920, irow6915, rows6921]
  all_goals rfl

theorem atot6915 : totK PD2M8K2 D2M8K2.u6915 = [0, 0, 253392286388, 810442199032, 560376568992, 85686019091, 1369150432, 0] := by
  rw [show D2M8K2.u6915 = KTree.node D2M8K2.t6920 (nat_lit 14703199) (nat_lit 2362243340) (nat_lit 0) D2M8K2.t6921 from rfl, totK_node, tot6920, tot6921]
  decide +kernel

theorem arows6916 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6916 = true := by
  rw [show D2M8K2.u6916 = KTree.node D2M8K2.t6922 (nat_lit 14708800) (nat_lit 3744896351) (nat_lit 0) D2M8K2.t6923 from rfl, allE_node, rows6922, irow6916, rows6923]
  all_goals rfl

theorem atot6916 : totK PD2M8K2 D2M8K2.u6916 = [0, 0, 248080950320, 874063350225, 582070074628, 41842389954, 0, 0] := by
  rw [show D2M8K2.u6916 = KTree.node D2M8K2.t6922 (nat_lit 14708800) (nat_lit 3744896351) (nat_lit 0) D2M8K2.t6923 from rfl, totK_node, tot6922, tot6923]
  decide +kernel

theorem arows6918 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6918 = true := by
  rw [show D2M8K2.u6918 = KTree.node D2M8K2.t6924 (nat_lit 14710442) (nat_lit 3958944633) (nat_lit 0) D2M8K2.t6925 from rfl, allE_node, rows6924, irow6918, rows6925]
  all_goals rfl

theorem atot6918 : totK PD2M8K2 D2M8K2.u6918 = [0, 0, 384589321889, 962602520266, 404578409093, 16642297958, 0, 0] := by
  rw [show D2M8K2.u6918 = KTree.node D2M8K2.t6924 (nat_lit 14710442) (nat_lit 3958944633) (nat_lit 0) D2M8K2.t6925 from rfl, totK_node, tot6924, tot6925]
  decide +kernel

theorem arows6919 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6919 = true := by
  rw [show D2M8K2.u6919 = KTree.node D2M8K2.t6926 (nat_lit 14713896) (nat_lit 3424999657) (nat_lit 0) D2M8K2.t6927 from rfl, allE_node, rows6926, irow6919, rows6927]
  all_goals rfl

theorem atot6919 : totK PD2M8K2 D2M8K2.u6919 = [0, 0, 364088532316, 961244974340, 400451023350, 16439024909, 0, 0] := by
  rw [show D2M8K2.u6919 = KTree.node D2M8K2.t6926 (nat_lit 14713896) (nat_lit 3424999657) (nat_lit 0) D2M8K2.t6927 from rfl, totK_node, tot6926, tot6927]
  decide +kernel

theorem arows6923 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6923 = true := by
  rw [show D2M8K2.u6923 = KTree.node D2M8K2.t6928 (nat_lit 14719300) (nat_lit 3940170132) (nat_lit 0) D2M8K2.t6929 from rfl, allE_node, rows6928, irow6923, rows6929]
  all_goals rfl

theorem atot6923 : totK PD2M8K2 D2M8K2.u6923 = [0, 0, 374841474747, 959255941985, 402760012524, 14447010309, 0, 0] := by
  rw [show D2M8K2.u6923 = KTree.node D2M8K2.t6928 (nat_lit 14719300) (nat_lit 3940170132) (nat_lit 0) D2M8K2.t6929 from rfl, totK_node, tot6928, tot6929]
  decide +kernel

theorem arows6924 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6924 = true := by
  rw [show D2M8K2.u6924 = KTree.node D2M8K2.t6930 (nat_lit 14726338) (nat_lit 4061605012) (nat_lit 0) D2M8K2.t6931 from rfl, allE_node, rows6930, irow6924, rows6931]
  all_goals rfl

theorem atot6924 : totK PD2M8K2 D2M8K2.u6924 = [0, 182603865993, 625866848932, 728683494424, 265873044813, 17376665387, 0, 0] := by
  rw [show D2M8K2.u6924 = KTree.node D2M8K2.t6930 (nat_lit 14726338) (nat_lit 4061605012) (nat_lit 0) D2M8K2.t6931 from rfl, totK_node, tot6930, tot6931]
  decide +kernel

theorem arows6926 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6926 = true := by
  rw [show D2M8K2.u6926 = KTree.node D2M8K2.t6932 (nat_lit 14727494) (nat_lit 4151327674) (nat_lit 0) D2M8K2.t6933 from rfl, allE_node, rows6932, irow6926, rows6933]
  all_goals rfl

theorem atot6926 : totK PD2M8K2 D2M8K2.u6926 = [0, 260283129798, 768478963435, 592144601127, 187955921009, 21400436502, 0, 0] := by
  rw [show D2M8K2.u6926 = KTree.node D2M8K2.t6932 (nat_lit 14727494) (nat_lit 4151327674) (nat_lit 0) D2M8K2.t6933 from rfl, totK_node, tot6932, tot6933]
  decide +kernel

theorem arows6927 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6927 = true := by
  rw [show D2M8K2.u6927 = KTree.node D2M8K2.t6934 (nat_lit 14728943) (nat_lit 1999886485) (nat_lit 0) D2M8K2.t6935 from rfl, allE_node, rows6934, irow6927, rows6935]
  all_goals rfl

theorem atot6927 : totK PD2M8K2 D2M8K2.u6927 = [0, 67691909564, 441376042394, 883031881021, 385985349819, 16100220446, 0, 0] := by
  rw [show D2M8K2.u6927 = KTree.node D2M8K2.t6934 (nat_lit 14728943) (nat_lit 1999886485) (nat_lit 0) D2M8K2.t6935 from rfl, totK_node, tot6934, tot6935]
  decide +kernel

theorem arows6930 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6930 = true := by
  rw [show D2M8K2.u6930 = KTree.node D2M8K2.t6936 (nat_lit 14730204) (nat_lit 3132893823) (nat_lit 0) D2M8K2.t6937 from rfl, allE_node, rows6936, irow6930, rows6937]
  all_goals rfl

theorem atot6930 : totK PD2M8K2 D2M8K2.u6930 = [0, 349180176492, 937614523465, 508651738636, 38413859319, 0, 0, 0] := by
  rw [show D2M8K2.u6930 = KTree.node D2M8K2.t6936 (nat_lit 14730204) (nat_lit 3132893823) (nat_lit 0) D2M8K2.t6937 from rfl, totK_node, tot6936, tot6937]
  decide +kernel

theorem arows6931 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6931 = true := by
  rw [show D2M8K2.u6931 = KTree.node D2M8K2.t6938 (nat_lit 14731928) (nat_lit 3210629968) (nat_lit 0) D2M8K2.t6939 from rfl, allE_node, rows6938, irow6931, rows6939]
  all_goals rfl

theorem atot6931 : totK PD2M8K2 D2M8K2.u6931 = [0, 52721596474, 523329236943, 927671865229, 277405887172, 9067749566, 0, 0] := by
  rw [show D2M8K2.u6931 = KTree.node D2M8K2.t6938 (nat_lit 14731928) (nat_lit 3210629968) (nat_lit 0) D2M8K2.t6939 from rfl, totK_node, tot6938, tot6939]
  decide +kernel

theorem arows6933 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6933 = true := by
  rw [show D2M8K2.u6933 = KTree.node D2M8K2.t6940 (nat_lit 14733967) (nat_lit 2359552723) (nat_lit 0) D2M8K2.t6941 from rfl, allE_node, rows6940, irow6933, rows6941]
  all_goals rfl

theorem atot6933 : totK PD2M8K2 D2M8K2.u6933 = [0, 332963367616, 911068282348, 541951394137, 45155466116, 0, 0, 0] := by
  rw [show D2M8K2.u6933 = KTree.node D2M8K2.t6940 (nat_lit 14733967) (nat_lit 2359552723) (nat_lit 0) D2M8K2.t6941 from rfl, totK_node, tot6940, tot6941]
  decide +kernel

theorem arows6934 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6934 = true := by
  rw [show D2M8K2.u6934 = KTree.node D2M8K2.t6942 (nat_lit 14735780) (nat_lit 3146640098) (nat_lit 0) D2M8K2.t6943 from rfl, allE_node, rows6942, irow6934, rows6943]
  all_goals rfl

theorem atot6934 : totK PD2M8K2 D2M8K2.u6934 = [0, 89709506736, 565275249569, 878495387976, 270142454808, 9178989717, 0, 0] := by
  rw [show D2M8K2.u6934 = KTree.node D2M8K2.t6942 (nat_lit 14735780) (nat_lit 3146640098) (nat_lit 0) D2M8K2.t6943 from rfl, totK_node, tot6942, tot6943]
  decide +kernel

theorem arows6939 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6939 = true := by
  rw [show D2M8K2.u6939 = KTree.node D2M8K2.t6944 (nat_lit 14737541) (nat_lit 2258829892) (nat_lit 0) D2M8K2.t6945 from rfl, allE_node, rows6944, irow6939, rows6945]
  all_goals rfl

theorem atot6939 : totK PD2M8K2 D2M8K2.u6939 = [0, 240167932337, 857374783250, 670740750271, 74003224541, 0, 0, 0] := by
  rw [show D2M8K2.u6939 = KTree.node D2M8K2.t6944 (nat_lit 14737541) (nat_lit 2258829892) (nat_lit 0) D2M8K2.t6945 from rfl, totK_node, tot6944, tot6945]
  decide +kernel

theorem arows6940 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6940 = true := by
  rw [show D2M8K2.u6940 = KTree.node D2M8K2.t6946 (nat_lit 14740175) (nat_lit 2154287778) (nat_lit 0) D2M8K2.t6947 from rfl, allE_node, rows6946, irow6940, rows6947]
  all_goals rfl

theorem atot6940 : totK PD2M8K2 D2M8K2.u6940 = [0, 264390833004, 784551698575, 644706142913, 116015106206, 1429815836, 0, 0] := by
  rw [show D2M8K2.u6940 = KTree.node D2M8K2.t6946 (nat_lit 14740175) (nat_lit 2154287778) (nat_lit 0) D2M8K2.t6947 from rfl, totK_node, tot6946, tot6947]
  decide +kernel

theorem arows6942 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6942 = true := by
  rw [show D2M8K2.u6942 = KTree.node D2M8K2.t6948 (nat_lit 14741579) (nat_lit 2924946698) (nat_lit 0) D2M8K2.t6949 from rfl, allE_node, rows6948, irow6942, rows6949]
  all_goals rfl

theorem atot6942 : totK PD2M8K2 D2M8K2.u6942 = [0, 162954607221, 691393201367, 764523474464, 180607816903, 4903313894, 0, 0] := by
  rw [show D2M8K2.u6942 = KTree.node D2M8K2.t6948 (nat_lit 14741579) (nat_lit 2924946698) (nat_lit 0) D2M8K2.t6949 from rfl, totK_node, tot6948, tot6949]
  decide +kernel

theorem arows6943 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6943 = true := by
  rw [show D2M8K2.u6943 = KTree.node D2M8K2.t6950 (nat_lit 14743283) (nat_lit 2971816977) (nat_lit 0) D2M8K2.t6951 from rfl, allE_node, rows6950, irow6943, rows6951]
  all_goals rfl

theorem atot6943 : totK PD2M8K2 D2M8K2.u6943 = [0, 195722704776, 644780539691, 677977957334, 241406460530, 17027268164, 0, 0] := by
  rw [show D2M8K2.u6943 = KTree.node D2M8K2.t6950 (nat_lit 14743283) (nat_lit 2971816977) (nat_lit 0) D2M8K2.t6951 from rfl, totK_node, tot6950, tot6951]
  decide +kernel

theorem arows6946 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6946 = true := by
  rw [show D2M8K2.u6946 = KTree.node D2M8K2.t6952 (nat_lit 14765610) (nat_lit 3730200587) (nat_lit 0) D2M8K2.t6953 from rfl, allE_node, rows6952, irow6946, rows6953]
  all_goals rfl

theorem atot6946 : totK PD2M8K2 D2M8K2.u6946 = [0, 211786255742, 763454796180, 681056699060, 110145698840, 1369150432, 0, 0] := by
  rw [show D2M8K2.u6946 = KTree.node D2M8K2.t6952 (nat_lit 14765610) (nat_lit 3730200587) (nat_lit 0) D2M8K2.t6953 from rfl, totK_node, tot6952, tot6953]
  decide +kernel

theorem arows6947 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6947 = true := by
  rw [show D2M8K2.u6947 = KTree.node D2M8K2.t6954 (nat_lit 14767973) (nat_lit 2373471541) (nat_lit 0) D2M8K2.t6955 from rfl, allE_node, rows6954, irow6947, rows6955]
  all_goals rfl

theorem atot6947 : totK PD2M8K2 D2M8K2.u6947 = [0, 250870434209, 828417155574, 674246879405, 73671590882, 0, 0, 0] := by
  rw [show D2M8K2.u6947 = KTree.node D2M8K2.t6954 (nat_lit 14767973) (nat_lit 2373471541) (nat_lit 0) D2M8K2.t6955 from rfl, totK_node, tot6954, tot6955]
  decide +kernel

theorem arows6949 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6949 = true := by
  rw [show D2M8K2.u6949 = KTree.node D2M8K2.t6956 (nat_lit 14769542) (nat_lit 4185429624) (nat_lit 0) D2M8K2.t6957 from rfl, allE_node, rows6956, irow6949, rows6957]
  all_goals rfl

theorem atot6949 : totK PD2M8K2 D2M8K2.u6949 = [0, 168467805187, 647434502026, 706501697880, 275767024620, 23329198674, 0, 0] := by
  rw [show D2M8K2.u6949 = KTree.node D2M8K2.t6956 (nat_lit 14769542) (nat_lit 4185429624) (nat_lit 0) D2M8K2.t6957 from rfl, totK_node, tot6956, tot6957]
  decide +kernel

theorem arows6950 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6950 = true := by
  rw [show D2M8K2.u6950 = KTree.node D2M8K2.t6958 (nat_lit 14770798) (nat_lit 4054937007) (nat_lit 0) D2M8K2.t6959 from rfl, allE_node, rows6958, irow6950, rows6959]
  all_goals rfl

theorem atot6950 : totK PD2M8K2 D2M8K2.u6950 = [0, 175012022416, 619393020264, 735902740243, 267859986533, 9435633141, 0, 0] := by
  rw [show D2M8K2.u6950 = KTree.node D2M8K2.t6958 (nat_lit 14770798) (nat_lit 4054937007) (nat_lit 0) D2M8K2.t6959 from rfl, totK_node, tot6958, tot6959]
  decide +kernel

theorem arows6954 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6954 = true := by
  rw [show D2M8K2.u6954 = KTree.node D2M8K2.t6960 (nat_lit 14772271) (nat_lit 1765382749) (nat_lit 0) D2M8K2.t6961 from rfl, allE_node, rows6960, irow6954, rows6961]
  all_goals rfl

theorem atot6954 : totK PD2M8K2 D2M8K2.u6954 = [0, 265877832960, 817328277112, 633093314088, 89252103674, 1164319620, 0, 0] := by
  rw [show D2M8K2.u6954 = KTree.node D2M8K2.t6960 (nat_lit 14772271) (nat_lit 1765382749) (nat_lit 0) D2M8K2.t6961 from rfl, totK_node, tot6960, tot6961]
  decide +kernel

theorem arows6955 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6955 = true := by
  rw [show D2M8K2.u6955 = KTree.node D2M8K2.t6962 (nat_lit 14773923) (nat_lit 3637699960) (nat_lit 0) D2M8K2.t6963 from rfl, allE_node, rows6962, irow6955, rows6963]
  all_goals rfl

theorem atot6955 : totK PD2M8K2 D2M8K2.u6955 = [0, 118433718873, 600523208693, 815691462176, 240315174132, 11885407614, 0, 0] := by
  rw [show D2M8K2.u6955 = KTree.node D2M8K2.t6962 (nat_lit 14773923) (nat_lit 3637699960) (nat_lit 0) D2M8K2.t6963 from rfl, totK_node, tot6962, tot6963]
  decide +kernel

theorem arows6957 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6957 = true := by
  rw [show D2M8K2.u6957 = KTree.node D2M8K2.t6964 (nat_lit 14779070) (nat_lit 3843185347) (nat_lit 0) D2M8K2.t6965 from rfl, allE_node, rows6964, irow6957, rows6965]
  all_goals rfl

theorem atot6957 : totK PD2M8K2 D2M8K2.u6957 = [0, 223881168048, 805213101257, 687845767965, 93237420020, 1062926506, 0, 0] := by
  rw [show D2M8K2.u6957 = KTree.node D2M8K2.t6964 (nat_lit 14779070) (nat_lit 3843185347) (nat_lit 0) D2M8K2.t6965 from rfl, totK_node, tot6964, tot6965]
  decide +kernel

theorem arows6958 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6958 = true := by
  rw [show D2M8K2.u6958 = KTree.node D2M8K2.t6966 (nat_lit 14781536) (nat_lit 2201496142) (nat_lit 0) D2M8K2.t6967 from rfl, allE_node, rows6966, irow6958, rows6967]
  all_goals rfl

theorem atot6958 : totK PD2M8K2 D2M8K2.u6958 = [0, 262761283625, 789417255982, 637267819361, 114858272961, 3720136285, 0, 0] := by
  rw [show D2M8K2.u6958 = KTree.node D2M8K2.t6966 (nat_lit 14781536) (nat_lit 2201496142) (nat_lit 0) D2M8K2.t6967 from rfl, totK_node, tot6966, tot6967]
  decide +kernel

theorem arows6961 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6961 = true := by
  rw [show D2M8K2.u6961 = KTree.node D2M8K2.t6968 (nat_lit 14783034) (nat_lit 3362168287) (nat_lit 0) D2M8K2.t6969 from rfl, allE_node, rows6968, irow6961, rows6969]
  all_goals rfl

theorem atot6961 : totK PD2M8K2 D2M8K2.u6961 = [0, 164699952579, 717650764533, 771819494640, 150508274818, 1268739303, 0, 0] := by
  rw [show D2M8K2.u6961 = KTree.node D2M8K2.t6968 (nat_lit 14783034) (nat_lit 3362168287) (nat_lit 0) D2M8K2.t6969 from rfl, totK_node, tot6968, tot6969]
  decide +kernel

theorem arows6962 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6962 = true := by
  rw [show D2M8K2.u6962 = KTree.node D2M8K2.t6970 (nat_lit 14784710) (nat_lit 2404256354) (nat_lit 0) D2M8K2.t6971 from rfl, allE_node, rows6970, irow6962, rows6971]
  all_goals rfl

theorem atot6962 : totK PD2M8K2 D2M8K2.u6962 = [0, 0, 350767021609, 933836662634, 448382959809, 26130262030, 0, 0] := by
  rw [show D2M8K2.u6962 = KTree.node D2M8K2.t6970 (nat_lit 14784710) (nat_lit 2404256354) (nat_lit 0) D2M8K2.t6971 from rfl, totK_node, tot6970, tot6971]
  decide +kernel

theorem arows6964 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6964 = true := by
  rw [show D2M8K2.u6964 = KTree.node D2M8K2.t6972 (nat_lit 14786365) (nat_lit 1260410359) (nat_lit 0) D2M8K2.t6973 from rfl, allE_node, rows6972, irow6964, rows6973]
  all_goals rfl

theorem atot6964 : totK PD2M8K2 D2M8K2.u6964 = [0, 0, 213476750728, 811074149615, 603188153652, 71419803840, 1166720416, 0] := by
  rw [show D2M8K2.u6964 = KTree.node D2M8K2.t6972 (nat_lit 14786365) (nat_lit 1260410359) (nat_lit 0) D2M8K2.t6973 from rfl, totK_node, tot6972, tot6973]
  decide +kernel

theorem arows6965 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6965 = true := by
  rw [show D2M8K2.u6965 = KTree.node D2M8K2.t6974 (nat_lit 14788862) (nat_lit 3915131715) (nat_lit 0) D2M8K2.t6975 from rfl, allE_node, rows6974, irow6965, rows6975]
  all_goals rfl

theorem atot6965 : totK PD2M8K2 D2M8K2.u6965 = [0, 0, 415090650940, 939903147266, 448591057985, 24582223136, 0, 0] := by
  rw [show D2M8K2.u6965 = KTree.node D2M8K2.t6974 (nat_lit 14788862) (nat_lit 3915131715) (nat_lit 0) D2M8K2.t6975 from rfl, totK_node, tot6974, tot6975]
  decide +kernel

theorem arows6971 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6971 = true := by
  rw [show D2M8K2.u6971 = KTree.node D2M8K2.t6976 (nat_lit 14792217) (nat_lit 1820878182) (nat_lit 0) D2M8K2.t6977 from rfl, allE_node, rows6976, irow6971, rows6977]
  all_goals rfl

theorem atot6971 : totK PD2M8K2 D2M8K2.u6971 = [0, 0, 351245125507, 932518005298, 459367058000, 31016713962, 0, 0] := by
  rw [show D2M8K2.u6971 = KTree.node D2M8K2.t6976 (nat_lit 14792217) (nat_lit 1820878182) (nat_lit 0) D2M8K2.t6977 from rfl, totK_node, tot6976, tot6977]
  decide +kernel

theorem arows6972 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6972 = true := by
  rw [show D2M8K2.u6972 = KTree.node D2M8K2.t6978 (nat_lit 14793795) (nat_lit 2757384012) (nat_lit 0) D2M8K2.t6979 from rfl, allE_node, rows6978, irow6972, rows6979]
  all_goals rfl

theorem atot6972 : totK PD2M8K2 D2M8K2.u6972 = [0, 0, 95393459994, 651556292663, 806627698309, 173069093918, 5134755853, 0] := by
  rw [show D2M8K2.u6972 = KTree.node D2M8K2.t6978 (nat_lit 14793795) (nat_lit 2757384012) (nat_lit 0) D2M8K2.t6979 from rfl, totK_node, tot6978, tot6979]
  decide +kernel

theorem arows6974 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6974 = true := by
  rw [show D2M8K2.u6974 = KTree.node D2M8K2.t6980 (nat_lit 14799434) (nat_lit 3038470461) (nat_lit 0) D2M8K2.t6981 from rfl, allE_node, rows6980, irow6974, rows6981]
  all_goals rfl

theorem atot6974 : totK PD2M8K2 D2M8K2.u6974 = [0, 0, 439844763277, 969924271343, 324334419485, 9883069468, 0, 0] := by
  rw [show D2M8K2.u6974 = KTree.node D2M8K2.t6980 (nat_lit 14799434) (nat_lit 3038470461) (nat_lit 0) D2M8K2.t6981 from rfl, totK_node, tot6980, tot6981]
  decide +kernel

theorem arows6975 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6975 = true := by
  rw [show D2M8K2.u6975 = KTree.node D2M8K2.t6982 (nat_lit 14803037) (nat_lit 1750719921) (nat_lit 0) D2M8K2.t6983 from rfl, allE_node, rows6982, irow6975, rows6983]
  all_goals rfl

theorem atot6975 : totK PD2M8K2 D2M8K2.u6975 = [0, 89204917003, 433193156039, 813731435136, 430996140582, 33024743369, 0, 0] := by
  rw [show D2M8K2.u6975 = KTree.node D2M8K2.t6982 (nat_lit 14803037) (nat_lit 1750719921) (nat_lit 0) D2M8K2.t6983 from rfl, totK_node, tot6982, tot6983]
  decide +kernel

theorem arows6978 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6978 = true := by
  rw [show D2M8K2.u6978 = KTree.node D2M8K2.t6984 (nat_lit 14806634) (nat_lit 3745570514) (nat_lit 0) D2M8K2.t6985 from rfl, allE_node, rows6984, irow6978, rows6985]
  all_goals rfl

theorem atot6978 : totK PD2M8K2 D2M8K2.u6978 = [0, 306599809091, 908608021180, 525331476031, 35725420150, 0, 0, 0] := by
  rw [show D2M8K2.u6978 = KTree.node D2M8K2.t6984 (nat_lit 14806634) (nat_lit 3745570514) (nat_lit 0) D2M8K2.t6985 from rfl, totK_node, tot6984, tot6985]
  decide +kernel

theorem arows6979 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6979 = true := by
  rw [show D2M8K2.u6979 = KTree.node D2M8K2.t6986 (nat_lit 14808677) (nat_lit 2184421552) (nat_lit 0) D2M8K2.t6987 from rfl, allE_node, rows6986, irow6979, rows6987]
  all_goals rfl

theorem atot6979 : totK PD2M8K2 D2M8K2.u6979 = [0, 162444838759, 686641632309, 816505582798, 144319132492, 1369150432, 0, 0] := by
  rw [show D2M8K2.u6979 = KTree.node D2M8K2.t6986 (nat_lit 14808677) (nat_lit 2184421552) (nat_lit 0) D2M8K2.t6987 from rfl, totK_node, tot6986, tot6987]
  decide +kernel

theorem arows6981 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6981 = true := by
  rw [show D2M8K2.u6981 = KTree.node D2M8K2.t6988 (nat_lit 14810361) (nat_lit 1902180880) (nat_lit 0) D2M8K2.t6989 from rfl, allE_node, rows6988, irow6981, rows6989]
  all_goals rfl

theorem atot6981 : totK PD2M8K2 D2M8K2.u6981 = [0, 245725193174, 811733218968, 610441192753, 143461479245, 13959483670, 0, 0] := by
  rw [show D2M8K2.u6981 = KTree.node D2M8K2.t6988 (nat_lit 14810361) (nat_lit 1902180880) (nat_lit 0) D2M8K2.t6989 from rfl, totK_node, tot6988, tot6989]
  decide +kernel

theorem arows6982 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6982 = true := by
  rw [show D2M8K2.u6982 = KTree.node D2M8K2.t6990 (nat_lit 14811909) (nat_lit 1229570209) (nat_lit 0) D2M8K2.t6991 from rfl, allE_node, rows6990, irow6982, rows6991]
  all_goals rfl

theorem atot6982 : totK PD2M8K2 D2M8K2.u6982 = [0, 84183811908, 452458104494, 842544240914, 397198507099, 18846101665, 0, 0] := by
  rw [show D2M8K2.u6982 = KTree.node D2M8K2.t6990 (nat_lit 14811909) (nat_lit 1229570209) (nat_lit 0) D2M8K2.t6991 from rfl, totK_node, tot6990, tot6991]
  decide +kernel

theorem arows6986 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6986 = true := by
  rw [show D2M8K2.u6986 = KTree.node D2M8K2.t6992 (nat_lit 14816890) (nat_lit 3806569382) (nat_lit 0) D2M8K2.t6993 from rfl, allE_node, rows6992, irow6986, rows6993]
  all_goals rfl

theorem atot6986 : totK PD2M8K2 D2M8K2.u6986 = [0, 341936786603, 931777423486, 518019405672, 38776433826, 0, 0, 0] := by
  rw [show D2M8K2.u6986 = KTree.node D2M8K2.t6992 (nat_lit 14816890) (nat_lit 3806569382) (nat_lit 0) D2M8K2.t6993 from rfl, totK_node, tot6992, tot6993]
  decide +kernel

theorem arows6987 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6987 = true := by
  rw [show D2M8K2.u6987 = KTree.node D2M8K2.t6994 (nat_lit 14818585) (nat_lit 1469827943) (nat_lit 0) D2M8K2.t6995 from rfl, allE_node, rows6994, irow6987, rows6995]
  all_goals rfl

theorem atot6987 : totK PD2M8K2 D2M8K2.u6987 = [0, 34739637443, 487259440891, 937581640254, 305150379436, 13189998508, 0, 0] := by
  rw [show D2M8K2.u6987 = KTree.node D2M8K2.t6994 (nat_lit 14818585) (nat_lit 1469827943) (nat_lit 0) D2M8K2.t6995 from rfl, totK_node, tot6994, tot6995]
  decide +kernel

theorem arows6989 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6989 = true := by
  rw [show D2M8K2.u6989 = KTree.node D2M8K2.t6996 (nat_lit 14823409) (nat_lit 1480710820) (nat_lit 0) D2M8K2.t6997 from rfl, allE_node, rows6996, irow6989, rows6997]
  all_goals rfl

theorem atot6989 : totK PD2M8K2 D2M8K2.u6989 = [0, 379832850419, 936165834990, 472365112938, 36487298412, 0, 0, 0] := by
  rw [show D2M8K2.u6989 = KTree.node D2M8K2.t6996 (nat_lit 14823409) (nat_lit 1480710820) (nat_lit 0) D2M8K2.t6997 from rfl, totK_node, tot6996, tot6997]
  decide +kernel

theorem arows6990 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6990 = true := by
  rw [show D2M8K2.u6990 = KTree.node D2M8K2.t6998 (nat_lit 14825093) (nat_lit 2253118802) (nat_lit 0) D2M8K2.t6999 from rfl, allE_node, rows6998, irow6990, rows6999]
  all_goals rfl

theorem atot6990 : totK PD2M8K2 D2M8K2.u6990 = [0, 8130385210, 507419436074, 957681350787, 291702948332, 8641950322, 0, 0] := by
  rw [show D2M8K2.u6990 = KTree.node D2M8K2.t6998 (nat_lit 14825093) (nat_lit 2253118802) (nat_lit 0) D2M8K2.t6999 from rfl, totK_node, tot6998, tot6999]
  decide +kernel

theorem arows6993 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6993 = true := by
  rw [show D2M8K2.u6993 = KTree.node D2M8K2.t7000 (nat_lit 14826961) (nat_lit 1533549872) (nat_lit 0) D2M8K2.t7001 from rfl, allE_node, rows7000, irow6993, rows7001]
  all_goals rfl

theorem atot6993 : totK PD2M8K2 D2M8K2.u6993 = [0, 0, 370943765030, 952366270161, 403318751809, 21039714487, 0, 0] := by
  rw [show D2M8K2.u6993 = KTree.node D2M8K2.t7000 (nat_lit 14826961) (nat_lit 1533549872) (nat_lit 0) D2M8K2.t7001 from rfl, totK_node, tot7000, tot7001]
  decide +kernel

theorem arows6994 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6994 = true := by
  rw [show D2M8K2.u6994 = KTree.node D2M8K2.t7002 (nat_lit 14828844) (nat_lit 3522838616) (nat_lit 0) D2M8K2.t7003 from rfl, allE_node, rows7002, irow6994, rows7003]
  all_goals rfl

theorem atot6994 : totK PD2M8K2 D2M8K2.u6994 = [0, 0, 145330054972, 763318295348, 744554428133, 90543514911, 1200365979, 0] := by
  rw [show D2M8K2.u6994 = KTree.node D2M8K2.t7002 (nat_lit 14828844) (nat_lit 3522838616) (nat_lit 0) D2M8K2.t7003 from rfl, totK_node, tot7002, tot7003]
  decide +kernel

theorem arows6996 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6996 = true := by
  rw [show D2M8K2.u6996 = KTree.node D2M8K2.t7004 (nat_lit 14831179) (nat_lit 1785918393) (nat_lit 0) D2M8K2.t7005 from rfl, allE_node, rows7004, irow6996, rows7005]
  all_goals rfl

theorem atot6996 : totK PD2M8K2 D2M8K2.u6996 = [0, 0, 464222140208, 971656838987, 368478446022, 16324914380, 0, 0] := by
  rw [show D2M8K2.u6996 = KTree.node D2M8K2.t7004 (nat_lit 14831179) (nat_lit 1785918393) (nat_lit 0) D2M8K2.t7005 from rfl, totK_node, tot7004, tot7005]
  decide +kernel

theorem arows6997 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6997 = true := by
  rw [show D2M8K2.u6997 = KTree.node D2M8K2.t7006 (nat_lit 14837908) (nat_lit 2132769898) (nat_lit 0) D2M8K2.t7007 from rfl, allE_node, rows7006, irow6997, rows7007]
  all_goals rfl

theorem atot6997 : totK PD2M8K2 D2M8K2.u6997 = [0, 0, 268898248115, 829310162692, 585250703946, 70707719937, 1135526696, 0] := by
  rw [show D2M8K2.u6997 = KTree.node D2M8K2.t7006 (nat_lit 14837908) (nat_lit 2132769898) (nat_lit 0) D2M8K2.t7007 from rfl, totK_node, tot7006, tot7007]
  decide +kernel

theorem arows7002 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7002 = true := by
  rw [show D2M8K2.u7002 = KTree.node D2M8K2.t7008 (nat_lit 14839826) (nat_lit 3499277429) (nat_lit 0) D2M8K2.t7009 from rfl, allE_node, rows7008, irow7002, rows7009]
  all_goals rfl

theorem atot7002 : totK PD2M8K2 D2M8K2.u7002 = [0, 0, 169795705981, 748845697071, 702919693798, 134974674067, 4028038878, 0] := by
  rw [show D2M8K2.u7002 = KTree.node D2M8K2.t7008 (nat_lit 14839826) (nat_lit 3499277429) (nat_lit 0) D2M8K2.t7009 from rfl, totK_node, tot7008, tot7009]
  decide +kernel

theorem arows7003 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7003 = true := by
  rw [show D2M8K2.u7003 = KTree.node D2M8K2.t7010 (nat_lit 14845009) (nat_lit 1457557465) (nat_lit 0) D2M8K2.t7011 from rfl, allE_node, rows7010, irow7003, rows7011]
  all_goals rfl

theorem atot7003 : totK PD2M8K2 D2M8K2.u7003 = [0, 141987590768, 546680399146, 734871076463, 351460083544, 26845399556, 0, 0] := by
  rw [show D2M8K2.u7003 = KTree.node D2M8K2.t7010 (nat_lit 14845009) (nat_lit 1457557465) (nat_lit 0) D2M8K2.t7011 from rfl, totK_node, tot7010, tot7011]
  decide +kernel

theorem arows7005 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7005 = true := by
  rw [show D2M8K2.u7005 = KTree.node D2M8K2.t7012 (nat_lit 14889708) (nat_lit 3189829869) (nat_lit 0) D2M8K2.t7013 from rfl, allE_node, rows7012, irow7005, rows7013]
  all_goals rfl

theorem atot7005 : totK PD2M8K2 D2M8K2.u7005 = [0, 271518543262, 844794750024, 573970030641, 73363628052, 1369150432, 0, 0] := by
  rw [show D2M8K2.u7005 = KTree.node D2M8K2.t7012 (nat_lit 14889708) (nat_lit 3189829869) (nat_lit 0) D2M8K2.t7013 from rfl, totK_node, tot7012, tot7013]
  decide +kernel

theorem arows7006 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7006 = true := by
  rw [show D2M8K2.u7006 = KTree.node D2M8K2.t7014 (nat_lit 14891708) (nat_lit 2446798000) (nat_lit 0) D2M8K2.t7015 from rfl, allE_node, rows7014, irow7006, rows7015]
  all_goals rfl

theorem atot7006 : totK PD2M8K2 D2M8K2.u7006 = [0, 180575128572, 749586254680, 787560829208, 102089727844, 0, 0, 0] := by
  rw [show D2M8K2.u7006 = KTree.node D2M8K2.t7014 (nat_lit 14891708) (nat_lit 2446798000) (nat_lit 0) D2M8K2.t7015 from rfl, totK_node, tot7014, tot7015]
  decide +kernel

theorem arows7009 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7009 = true := by
  rw [show D2M8K2.u7009 = KTree.node D2M8K2.t7016 (nat_lit 14893377) (nat_lit 1367166466) (nat_lit 0) D2M8K2.t7017 from rfl, allE_node, rows7016, irow7009, rows7017]
  all_goals rfl

theorem atot7009 : totK PD2M8K2 D2M8K2.u7009 = [0, 243947181647, 755637347791, 607231550643, 186556595434, 16716266525, 0, 0] := by
  rw [show D2M8K2.u7009 = KTree.node D2M8K2.t7016 (nat_lit 14893377) (nat_lit 1367166466) (nat_lit 0) D2M8K2.t7017 from rfl, totK_node, tot7016, tot7017]
  decide +kernel

theorem arows7010 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7010 = true := by
  rw [show D2M8K2.u7010 = KTree.node D2M8K2.t7018 (nat_lit 14894842) (nat_lit 3180784165) (nat_lit 0) D2M8K2.t7019 from rfl, allE_node, rows7018, irow7010, rows7019]
  all_goals rfl

theorem atot7010 : totK PD2M8K2 D2M8K2.u7010 = [0, 84425303906, 471374947620, 855966772557, 353881477646, 13691165764, 0, 0] := by
  rw [show D2M8K2.u7010 = KTree.node D2M8K2.t7018 (nat_lit 14894842) (nat_lit 3180784165) (nat_lit 0) D2M8K2.t7019 from rfl, totK_node, tot7018, tot7019]
  decide +kernel

theorem arows7012 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7012 = true := by
  rw [show D2M8K2.u7012 = KTree.node D2M8K2.t7020 (nat_lit 14896092) (nat_lit 3149023000) (nat_lit 0) D2M8K2.t7021 from rfl, allE_node, rows7020, irow7012, rows7021]
  all_goals rfl

theorem atot7012 : totK PD2M8K2 D2M8K2.u7012 = [0, 337707684021, 927168852928, 519931386329, 38782144780, 0, 0, 0] := by
  rw [show D2M8K2.u7012 = KTree.node D2M8K2.t7020 (nat_lit 14896092) (nat_lit 3149023000) (nat_lit 0) D2M8K2.t7021 from rfl, totK_node, tot7020, tot7021]
  decide +kernel

theorem arows7013 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7013 = true := by
  rw [show D2M8K2.u7013 = KTree.node D2M8K2.t7022 (nat_lit 14897809) (nat_lit 1469321292) (nat_lit 0) D2M8K2.t7023 from rfl, allE_node, rows7022, irow7013, rows7023]
  all_goals rfl

theorem atot7013 : totK PD2M8K2 D2M8K2.u7013 = [0, 64599357384, 516853651001, 909911332562, 261709644550, 8557595888, 0, 0] := by
  rw [show D2M8K2.u7013 = KTree.node D2M8K2.t7022 (nat_lit 14897809) (nat_lit 1469321292) (nat_lit 0) D2M8K2.t7023 from rfl, totK_node, tot7022, tot7023]
  decide +kernel

theorem arows7017 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7017 = true := by
  rw [show D2M8K2.u7017 = KTree.node D2M8K2.t7024 (nat_lit 14899801) (nat_lit 1487561833) (nat_lit 0) D2M8K2.t7025 from rfl, allE_node, rows7024, irow7017, rows7025]
  all_goals rfl

theorem atot7017 : totK PD2M8K2 D2M8K2.u7017 = [0, 337907292303, 921875340542, 511974760762, 38713887288, 0, 0, 0] := by
  rw [show D2M8K2.u7017 = KTree.node D2M8K2.t7024 (nat_lit 14899801) (nat_lit 1487561833) (nat_lit 0) D2M8K2.t7025 from rfl, totK_node, tot7024, tot7025]
  decide +kernel

theorem arows7018 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7018 = true := by
  rw [show D2M8K2.u7018 = KTree.node D2M8K2.t7026 (nat_lit 14901540) (nat_lit 3101139557) (nat_lit 0) D2M8K2.t7027 from rfl, allE_node, rows7026, irow7018, rows7027]
  all_goals rfl

theorem atot7018 : totK PD2M8K2 D2M8K2.u7018 = [0, 78906945190, 529265579131, 879624447903, 261722558216, 8656689423, 0, 0] := by
  rw [show D2M8K2.u7018 = KTree.node D2M8K2.t7026 (nat_lit 14901540) (nat_lit 3101139557) (nat_lit 0) D2M8K2.t7027 from rfl, totK_node, tot7026, tot7027]
  decide +kernel

theorem arows7020 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7020 = true := by
  rw [show D2M8K2.u7020 = KTree.node D2M8K2.t7028 (nat_lit 14906441) (nat_lit 1633260460) (nat_lit 0) D2M8K2.t7029 from rfl, allE_node, rows7028, irow7020, rows7029]
  all_goals rfl

theorem atot7020 : totK PD2M8K2 D2M8K2.u7020 = [0, 364636407204, 948080955318, 497366872319, 38184943845, 0, 0, 0] := by
  rw [show D2M8K2.u7020 = KTree.node D2M8K2.t7028 (nat_lit 14906441) (nat_lit 1633260460) (nat_lit 0) D2M8K2.t7029 from rfl, totK_node, tot7028, tot7029]
  decide +kernel

theorem arows7021 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7021 = true := by
  rw [show D2M8K2.u7021 = KTree.node D2M8K2.t7030 (nat_lit 14908062) (nat_lit 3231166094) (nat_lit 0) D2M8K2.t7031 from rfl, allE_node, rows7030, irow7021, rows7031]
  all_goals rfl

theorem atot7021 : totK PD2M8K2 D2M8K2.u7021 = [0, 0, 490990810404, 987869864721, 298677554110, 8710740030, 0, 0] := by
  rw [show D2M8K2.u7021 = KTree.node D2M8K2.t7030 (nat_lit 14908062) (nat_lit 3231166094) (nat_lit 0) D2M8K2.t7031 from rfl, totK_node, tot7030, tot7031]
  decide +kernel

theorem arows7024 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7024 = true := by
  rw [show D2M8K2.u7024 = KTree.node D2M8K2.t7032 (nat_lit 14909869) (nat_lit 1097811457) (nat_lit 0) D2M8K2.t7033 from rfl, allE_node, rows7032, irow7024, rows7033]
  all_goals rfl

theorem atot7024 : totK PD2M8K2 D2M8K2.u7024 = [0, 0, 358127445995, 933604264586, 416720022663, 23658994969, 0, 0] := by
  rw [show D2M8K2.u7024 = KTree.node D2M8K2.t7032 (nat_lit 14909869) (nat_lit 1097811457) (nat_lit 0) D2M8K2.t7033 from rfl, totK_node, tot7032, tot7033]
  decide +kernel

theorem arows7025 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7025 = true := by
  rw [show D2M8K2.u7025 = KTree.node D2M8K2.t7034 (nat_lit 14911494) (nat_lit 2651469712) (nat_lit 0) D2M8K2.t7035 from rfl, allE_node, rows7034, irow7025, rows7035]
  all_goals rfl

theorem atot7025 : totK PD2M8K2 D2M8K2.u7025 = [0, 0, 119806219995, 691131474539, 815799404009, 119074394429, 1288491354, 0] := by
  rw [show D2M8K2.u7025 = KTree.node D2M8K2.t7034 (nat_lit 14911494) (nat_lit 2651469712) (nat_lit 0) D2M8K2.t7035 from rfl, totK_node, tot7034, tot7035]
  decide +kernel

theorem arows7027 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7027 = true := by
  rw [show D2M8K2.u7027 = KTree.node D2M8K2.t7036 (nat_lit 14913584) (nat_lit 3674878296) (nat_lit 0) D2M8K2.t7037 from rfl, allE_node, rows7036, irow7027, rows7037]
  all_goals rfl

theorem atot7027 : totK PD2M8K2 D2M8K2.u7027 = [0, 0, 396514051518, 947869719863, 437111936777, 33171106730, 0, 0] := by
  rw [show D2M8K2.u7027 = KTree.node D2M8K2.t7036 (nat_lit 14913584) (nat_lit 3674878296) (nat_lit 0) D2M8K2.t7037 from rfl, totK_node, tot7036, tot7037]
  decide +kernel

theorem arows7028 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7028 = true := by
  rw [show D2M8K2.u7028 = KTree.node D2M8K2.t7038 (nat_lit 14916721) (nat_lit 1504877981) (nat_lit 0) D2M8K2.t7039 from rfl, allE_node, rows7038, irow7028, rows7039]
  all_goals rfl

theorem atot7028 : totK PD2M8K2 D2M8K2.u7028 = [0, 0, 408175098976, 959662825993, 387841706972, 18891401791, 0, 0] := by
  rw [show D2M8K2.u7028 = KTree.node D2M8K2.t7038 (nat_lit 14916721) (nat_lit 1504877981) (nat_lit 0) D2M8K2.t7039 from rfl, totK_node, tot7038, tot7039]
  decide +kernel

theorem arows7035 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7035 = true := by
  rw [show D2M8K2.u7035 = KTree.node D2M8K2.t7040 (nat_lit 14918512) (nat_lit 3361669683) (nat_lit 0) D2M8K2.t7041 from rfl, allE_node, rows7040, irow7035, rows7041]
  all_goals rfl

theorem atot7035 : totK PD2M8K2 D2M8K2.u7035 = [0, 0, 82469601113, 634551208711, 820058822080, 168198548117, 4787054165, 0] := by
  rw [show D2M8K2.u7035 = KTree.node D2M8K2.t7040 (nat_lit 14918512) (nat_lit 3361669683) (nat_lit 0) D2M8K2.t7041 from rfl, totK_node, tot7040, tot7041]
  decide +kernel

theorem arows7036 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7036 = true := by
  rw [show D2M8K2.u7036 = KTree.node D2M8K2.t7042 (nat_lit 14920672) (nat_lit 582107707) (nat_lit 0) D2M8K2.t7043 from rfl, allE_node, rows7042, irow7036, rows7043]
  all_goals rfl

theorem atot7036 : totK PD2M8K2 D2M8K2.u7036 = [0, 0, 315072542047, 898716870540, 514274359894, 37590849036, 0, 0] := by
  rw [show D2M8K2.u7036 = KTree.node D2M8K2.t7042 (nat_lit 14920672) (nat_lit 582107707) (nat_lit 0) D2M8K2.t7043 from rfl, totK_node, tot7042, tot7043]
  decide +kernel

theorem arows7038 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7038 = true := by
  rw [show D2M8K2.u7038 = KTree.node D2M8K2.t7044 (nat_lit 14922738) (nat_lit 3262518928) (nat_lit 0) D2M8K2.t7045 from rfl, allE_node, rows7044, irow7038, rows7045]
  all_goals rfl

theorem atot7038 : totK PD2M8K2 D2M8K2.u7038 = [0, 0, 174952877924, 704752255717, 705614201399, 159315983637, 4838243418, 0] := by
  rw [show D2M8K2.u7038 = KTree.node D2M8K2.t7044 (nat_lit 14922738) (nat_lit 3262518928) (nat_lit 0) D2M8K2.t7045 from rfl, totK_node, tot7044, tot7045]
  decide +kernel

theorem arows7039 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7039 = true := by
  rw [show D2M8K2.u7039 = KTree.node D2M8K2.t7046 (nat_lit 14927551) (nat_lit 2437711975) (nat_lit 0) D2M8K2.t7047 from rfl, allE_node, rows7046, irow7039, rows7047]
  all_goals rfl

theorem atot7039 : totK PD2M8K2 D2M8K2.u7039 = [0, 0, 267510892665, 821131224600, 616404755308, 82370010608, 1242138600, 0] := by
  rw [show D2M8K2.u7039 = KTree.node D2M8K2.t7046 (nat_lit 14927551) (nat_lit 2437711975) (nat_lit 0) D2M8K2.t7047 from rfl, totK_node, tot7046, tot7047]
  decide +kernel

theorem arows7042 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7042 = true := by
  rw [show D2M8K2.u7042 = KTree.node D2M8K2.t7048 (nat_lit 14929205) (nat_lit 1068709703) (nat_lit 0) D2M8K2.t7049 from rfl, allE_node, rows7048, irow7042, rows7049]
  all_goals rfl

theorem atot7042 : totK PD2M8K2 D2M8K2.u7042 = [0, 92342479873, 161177781494, 383944541212, 783162630210, 316956160101, 20509029466, 0] := by
  rw [show D2M8K2.u7042 = KTree.node D2M8K2.t7048 (nat_lit 14929205) (nat_lit 1068709703) (nat_lit 0) D2M8K2.t7049 from rfl, totK_node, tot7048, tot7049]
  decide +kernel

theorem arows7043 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7043 = true := by
  rw [show D2M8K2.u7043 = KTree.node D2M8K2.t7050 (nat_lit 14931014) (nat_lit 3052117425) (nat_lit 0) D2M8K2.t7051 from rfl, allE_node, rows7050, irow7043, rows7051]
  all_goals rfl

theorem atot7043 : totK PD2M8K2 D2M8K2.u7043 = [0, 350082612623, 948053701421, 485045888114, 26000953252, 0, 0, 0] := by
  rw [show D2M8K2.u7043 = KTree.node D2M8K2.t7050 (nat_lit 14931014) (nat_lit 3052117425) (nat_lit 0) D2M8K2.t7051 from rfl, totK_node, tot7050, tot7051]
  decide +kernel

theorem arows7045 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7045 = true := by
  rw [show D2M8K2.u7045 = KTree.node D2M8K2.t7052 (nat_lit 14932646) (nat_lit 3600693661) (nat_lit 0) D2M8K2.t7053 from rfl, allE_node, rows7052, irow7045, rows7053]
  all_goals rfl

theorem atot7045 : totK PD2M8K2 D2M8K2.u7045 = [0, 103589792006, 692613776300, 880204424778, 151495808630, 1369150432, 0, 0] := by
  rw [show D2M8K2.u7045 = KTree.node D2M8K2.t7052 (nat_lit 14932646) (nat_lit 3600693661) (nat_lit 0) D2M8K2.t7053 from rfl, totK_node, tot7052, tot7053]
  decide +kernel

theorem arows7046 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7046 = true := by
  rw [show D2M8K2.u7046 = KTree.node D2M8K2.t7054 (nat_lit 14938029) (nat_lit 1492991003) (nat_lit 0) D2M8K2.t7055 from rfl, allE_node, rows7054, irow7046, rows7055]
  all_goals rfl

theorem atot7046 : totK PD2M8K2 D2M8K2.u7046 = [0, 317589496574, 887293242929, 546902698390, 49977582824, 0, 0, 0] := by
  rw [show D2M8K2.u7046 = KTree.node D2M8K2.t7054 (nat_lit 14938029) (nat_lit 1492991003) (nat_lit 0) D2M8K2.t7055 from rfl, totK_node, tot7054, tot7055]
  decide +kernel

theorem arows7050 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7050 = true := by
  rw [show D2M8K2.u7050 = KTree.node D2M8K2.t7056 (nat_lit 14939723) (nat_lit 2091801547) (nat_lit 0) D2M8K2.t7057 from rfl, allE_node, rows7056, irow7050, rows7057]
  all_goals rfl

theorem atot7050 : totK PD2M8K2 D2M8K2.u7050 = [0, 87978670910, 526812005312, 871162881305, 280943300091, 13049727234, 0, 0] := by
  rw [show D2M8K2.u7050 = KTree.node D2M8K2.t7056 (nat_lit 14939723) (nat_lit 2091801547) (nat_lit 0) D2M8K2.t7057 from rfl, totK_node, tot7056, tot7057]
  decide +kernel

theorem arows7051 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7051 = true := by
  rw [show D2M8K2.u7051 = KTree.node D2M8K2.t7058 (nat_lit 14941472) (nat_lit 3791176880) (nat_lit 0) D2M8K2.t7059 from rfl, allE_node, rows7058, irow7051, rows7059]
  all_goals rfl

theorem atot7051 : totK PD2M8K2 D2M8K2.u7051 = [0, 311958211150, 901077166492, 529120880802, 36043066917, 0, 0, 0] := by
  rw [show D2M8K2.u7051 = KTree.node D2M8K2.t7058 (nat_lit 14941472) (nat_lit 3791176880) (nat_lit 0) D2M8K2.t7059 from rfl, totK_node, tot7058, tot7059]
  decide +kernel

theorem arows7053 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7053 = true := by
  rw [show D2M8K2.u7053 = KTree.node D2M8K2.t7060 (nat_lit 14943184) (nat_lit 2789454278) (nat_lit 0) D2M8K2.t7061 from rfl, allE_node, rows7060, irow7053, rows7061]
  all_goals rfl

theorem atot7053 : totK PD2M8K2 D2M8K2.u7053 = [0, 87770539582, 516263505554, 859371513190, 272522079350, 13250685261, 0, 0] := by
  rw [show D2M8K2.u7053 = KTree.node D2M8K2.t7060 (nat_lit 14943184) (nat_lit 2789454278) (nat_lit 0) D2M8K2.t7061 from rfl, totK_node, tot7060, tot7061]
  decide +kernel

theorem arows7054 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7054 = true := by
  rw [show D2M8K2.u7054 = KTree.node D2M8K2.t7062 (nat_lit 14944595) (nat_lit 2865036457) (nat_lit 0) D2M8K2.t7063 from rfl, allE_node, rows7062, irow7054, rows7063]
  all_goals rfl

theorem atot7054 : totK PD2M8K2 D2M8K2.u7054 = [0, 326447002902, 905868576524, 499432049815, 36537328572, 0, 0, 0] := by
  rw [show D2M8K2.u7054 = KTree.node D2M8K2.t7062 (nat_lit 14944595) (nat_lit 2865036457) (nat_lit 0) D2M8K2.t7063 from rfl, totK_node, tot7062, tot7063]
  decide +kernel

theorem arows7057 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7057 = true := by
  rw [show D2M8K2.u7057 = KTree.node D2M8K2.t7064 (nat_lit 14946438) (nat_lit 3878967719) (nat_lit 0) D2M8K2.t7065 from rfl, allE_node, rows7064, irow7057, rows7065]
  all_goals rfl

theorem atot7057 : totK PD2M8K2 D2M8K2.u7057 = [0, 103483345677, 628608698231, 857420275087, 193396134989, 4980514959, 0, 0] := by
  rw [show D2M8K2.u7057 = KTree.node D2M8K2.t7064 (nat_lit 14946438) (nat_lit 3878967719) (nat_lit 0) D2M8K2.t7065 from rfl, totK_node, tot7064, tot7065]
  decide +kernel

theorem arows7058 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7058 = true := by
  rw [show D2M8K2.u7058 = KTree.node D2M8K2.t7066 (nat_lit 14948138) (nat_lit 3974258135) (nat_lit 0) D2M8K2.t7067 from rfl, allE_node, rows7066, irow7058, rows7067]
  all_goals rfl

theorem atot7058 : totK PD2M8K2 D2M8K2.u7058 = [0, 315750996101, 877921314081, 553592308207, 51941542506, 0, 0, 0] := by
  rw [show D2M8K2.u7058 = KTree.node D2M8K2.t7066 (nat_lit 14948138) (nat_lit 3974258135) (nat_lit 0) D2M8K2.t7067 from rfl, totK_node, tot7066, tot7067]
  decide +kernel

theorem arows7060 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7060 = true := by
  rw [show D2M8K2.u7060 = KTree.node D2M8K2.t7068 (nat_lit 14949799) (nat_lit 2380119189) (nat_lit 0) D2M8K2.t7069 from rfl, allE_node, rows7068, irow7060, rows7069]
  all_goals rfl

theorem atot7060 : totK PD2M8K2 D2M8K2.u7060 = [0, 0, 395394518226, 947772261390, 391227925637, 22048779143, 0, 0] := by
  rw [show D2M8K2.u7060 = KTree.node D2M8K2.t7068 (nat_lit 14949799) (nat_lit 2380119189) (nat_lit 0) D2M8K2.t7069 from rfl, totK_node, tot7068, tot7069]
  decide +kernel

theorem arows7061 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7061 = true := by
  rw [show D2M8K2.u7061 = KTree.node D2M8K2.t7070 (nat_lit 14951598) (nat_lit 4071740195) (nat_lit 0) D2M8K2.t7071 from rfl, allE_node, rows7070, irow7061, rows7071]
  all_goals rfl

theorem atot7061 : totK PD2M8K2 D2M8K2.u7061 = [0, 0, 395352289702, 950094733981, 400857719393, 21817061227, 0, 0] := by
  rw [show D2M8K2.u7061 = KTree.node D2M8K2.t7070 (nat_lit 14951598) (nat_lit 4071740195) (nat_lit 0) D2M8K2.t7071 from rfl, totK_node, tot7070, tot7071]
  decide +kernel

theorem arows7066 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7066 = true := by
  rw [show D2M8K2.u7066 = KTree.node D2M8K2.t7072 (nat_lit 14953098) (nat_lit 2115558080) (nat_lit 0) D2M8K2.t7073 from rfl, allE_node, rows7072, irow7066, rows7073]
  all_goals rfl

theorem atot7066 : totK PD2M8K2 D2M8K2.u7066 = [0, 0, 110875124171, 704131189624, 785951966465, 142668472581, 1369150432, 0] := by
  rw [show D2M8K2.u7066 = KTree.node D2M8K2.t7072 (nat_lit 14953098) (nat_lit 2115558080) (nat_lit 0) D2M8K2.t7073 from rfl, totK_node, tot7072, tot7073]
  decide +kernel

theorem arows7067 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7067 = true := by
  rw [show D2M8K2.u7067 = KTree.node D2M8K2.t7074 (nat_lit 14958402) (nat_lit 1365148086) (nat_lit 0) D2M8K2.t7075 from rfl, allE_node, rows7074, irow7067, rows7075]
  all_goals rfl

theorem atot7067 : totK PD2M8K2 D2M8K2.u7067 = [0, 0, 343669936877, 930249635743, 475986032311, 26515491651, 0, 0] := by
  rw [show D2M8K2.u7067 = KTree.node D2M8K2.t7074 (nat_lit 14958402) (nat_lit 1365148086) (nat_lit 0) D2M8K2.t7075 from rfl, totK_node, tot7074, tot7075]
  decide +kernel

theorem arows7069 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7069 = true := by
  rw [show D2M8K2.u7069 = KTree.node D2M8K2.t7076 (nat_lit 14962054) (nat_lit 2465688847) (nat_lit 0) D2M8K2.t7077 from rfl, allE_node, rows7076, irow7069, rows7077]
  all_goals rfl

theorem atot7069 : totK PD2M8K2 D2M8K2.u7069 = [0, 0, 387783257338, 967212548182, 382892503158, 14898038305, 0, 0] := by
  rw [show D2M8K2.u7069 = KTree.node D2M8K2.t7076 (nat_lit 14962054) (nat_lit 2465688847) (nat_lit 0) D2M8K2.t7077 from rfl, totK_node, tot7076, tot7077]
  decide +kernel

theorem arows7070 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7070 = true := by
  rw [show D2M8K2.u7070 = KTree.node D2M8K2.t7078 (nat_lit 14965099) (nat_lit 982558505) (nat_lit 128) D2M8K2.t7079 from rfl, allE_node, rows7078, irow7070, rows7079]
  all_goals rfl

theorem atot7070 : totK PD2M8K2 D2M8K2.u7070 = [0, 0, 368834700872, 920026987049, 424333411715, 27234412507, 0, 0] := by
  rw [show D2M8K2.u7070 = KTree.node D2M8K2.t7078 (nat_lit 14965099) (nat_lit 982558505) (nat_lit 128) D2M8K2.t7079 from rfl, totK_node, tot7078, tot7079]
  decide +kernel

theorem arows7073 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7073 = true := by
  rw [show D2M8K2.u7073 = KTree.node D2M8K2.t7080 (nat_lit 14968397) (nat_lit 1672178660) (nat_lit 514) D2M8K2.t7081 from rfl, allE_node, rows7080, irow7073, rows7081]
  all_goals rfl

theorem atot7073 : totK PD2M8K2 D2M8K2.u7073 = [0, 0, 366104574037, 968236188425, 428268286914, 15776034544, 0, 0] := by
  rw [show D2M8K2.u7073 = KTree.node D2M8K2.t7080 (nat_lit 14968397) (nat_lit 1672178660) (nat_lit 514) D2M8K2.t7081 from rfl, totK_node, tot7080, tot7081]
  decide +kernel

theorem arows7074 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7074 = true := by
  rw [show D2M8K2.u7074 = KTree.node D2M8K2.t7082 (nat_lit 15013108) (nat_lit 3679314139) (nat_lit 0) D2M8K2.t7083 from rfl, allE_node, rows7082, irow7074, rows7083]
  all_goals rfl

theorem atot7074 : totK PD2M8K2 D2M8K2.u7074 = [0, 275066998334, 757345698075, 571025145850, 182796269556, 15168170160, 0, 0] := by
  rw [show D2M8K2.u7074 = KTree.node D2M8K2.t7082 (nat_lit 15013108) (nat_lit 3679314139) (nat_lit 0) D2M8K2.t7083 from rfl, totK_node, tot7082, tot7083]
  decide +kernel

theorem arows7076 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7076 = true := by
  rw [show D2M8K2.u7076 = KTree.node D2M8K2.t7084 (nat_lit 15014660) (nat_lit 3126407821) (nat_lit 0) D2M8K2.t7085 from rfl, allE_node, rows7084, irow7076, rows7085]
  all_goals rfl

theorem atot7076 : totK PD2M8K2 D2M8K2.u7076 = [0, 146406985473, 719624025227, 789246638241, 132302747133, 1369150432, 0, 0] := by
  rw [show D2M8K2.u7076 = KTree.node D2M8K2.t7084 (nat_lit 15014660) (nat_lit 3126407821) (nat_lit 0) D2M8K2.t7085 from rfl, totK_node, tot7084, tot7085]
  decide +kernel

theorem arows7077 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7077 = true := by
  rw [show D2M8K2.u7077 = KTree.node D2M8K2.t7086 (nat_lit 15016966) (nat_lit 3793759291) (nat_lit 0) D2M8K2.t7087 from rfl, allE_node, rows7086, irow7077, rows7087]
  all_goals rfl

theorem atot7077 : totK PD2M8K2 D2M8K2.u7077 = [0, 347345618735, 898165661066, 548900165342, 52648752917, 0, 0, 0] := by
  rw [show D2M8K2.u7077 = KTree.node D2M8K2.t7086 (nat_lit 15016966) (nat_lit 3793759291) (nat_lit 0) D2M8K2.t7087 from rfl, totK_node, tot7086, tot7087]
  decide +kernel

theorem arows7081 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7081 = true := by
  rw [show D2M8K2.u7081 = KTree.node D2M8K2.t7088 (nat_lit 15018762) (nat_lit 2981346924) (nat_lit 0) D2M8K2.t7089 from rfl, allE_node, rows7088, irow7081, rows7089]
  all_goals rfl

theorem atot7081 : totK PD2M8K2 D2M8K2.u7081 = [0, 0, 445891191569, 956837609585, 400853923181, 21623070469, 0, 0] := by
  rw [show D2M8K2.u7081 = KTree.node D2M8K2.t7088 (nat_lit 15018762) (nat_lit 2981346924) (nat_lit 0) D2M8K2.t7089 from rfl, totK_node, tot7088, tot7089]
  decide +kernel

theorem arows7082 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7082 = true := by
  rw [show D2M8K2.u7082 = KTree.node D2M8K2.t7090 (nat_lit 15020352) (nat_lit 3705351137) (nat_lit 0) D2M8K2.t7091 from rfl, allE_node, rows7090, irow7082, rows7091]
  all_goals rfl

theorem atot7082 : totK PD2M8K2 D2M8K2.u7082 = [0, 370065916009, 917817716984, 478024850156, 60757169907, 3060566153, 0, 0] := by
  rw [show D2M8K2.u7082 = KTree.node D2M8K2.t7090 (nat_lit 15020352) (nat_lit 3705351137) (nat_lit 0) D2M8K2.t7091 from rfl, totK_node, tot7090, tot7091]
  decide +kernel

theorem arows7084 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7084 = true := by
  rw [show D2M8K2.u7084 = KTree.node D2M8K2.t7092 (nat_lit 15021873) (nat_lit 1501094430) (nat_lit 0) D2M8K2.t7093 from rfl, allE_node, rows7092, irow7084, rows7093]
  all_goals rfl

theorem atot7084 : totK PD2M8K2 D2M8K2.u7084 = [0, 70796540562, 555657057716, 904991707721, 256692724435, 10568566766, 0, 0] := by
  rw [show D2M8K2.u7084 = KTree.node D2M8K2.t7092 (nat_lit 15021873) (nat_lit 1501094430) (nat_lit 0) D2M8K2.t7093 from rfl, totK_node, tot7092, tot7093]
  decide +kernel

theorem arows7085 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7085 = true := by
  rw [show D2M8K2.u7085 = KTree.node D2M8K2.t7094 (nat_lit 15027118) (nat_lit 3809044947) (nat_lit 0) D2M8K2.t7095 from rfl, allE_node, rows7094, irow7085, rows7095]
  all_goals rfl

theorem atot7085 : totK PD2M8K2 D2M8K2.u7085 = [0, 318886843382, 860466502637, 545508247990, 75647498734, 2481160468, 0, 0] := by
  rw [show D2M8K2.u7085 = KTree.node D2M8K2.t7094 (nat_lit 15027118) (nat_lit 3809044947) (nat_lit 0) D2M8K2.t7095 from rfl, totK_node, tot7094, tot7095]
  decide +kernel

theorem arows7088 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7088 = true := by
  rw [show D2M8K2.u7088 = KTree.node D2M8K2.t7096 (nat_lit 15028732) (nat_lit 3899454054) (nat_lit 0) D2M8K2.t7097 from rfl, allE_node, rows7096, irow7088, rows7097]
  all_goals rfl

theorem atot7088 : totK PD2M8K2 D2M8K2.u7088 = [0, 90852006335, 673219598657, 871805759547, 146824618899, 1096505104, 0, 0] := by
  rw [show D2M8K2.u7088 = KTree.node D2M8K2.t7096 (nat_lit 15028732) (nat_lit 3899454054) (nat_lit 0) D2M8K2.t7097 from rfl, totK_node, tot7096, tot7097]
  decide +kernel

theorem arows7089 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7089 = true := by
  rw [show D2M8K2.u7089 = KTree.node D2M8K2.t7098 (nat_lit 15030675) (nat_lit 3280367583) (nat_lit 128) D2M8K2.t7099 from rfl, allE_node, rows7098, irow7089, rows7099]
  all_goals rfl

theorem atot7089 : totK PD2M8K2 D2M8K2.u7089 = [0, 348636390389, 863767798086, 509563315757, 90987848344, 3884009855, 0, 0] := by
  rw [show D2M8K2.u7089 = KTree.node D2M8K2.t7098 (nat_lit 15030675) (nat_lit 3280367583) (nat_lit 128) D2M8K2.t7099 from rfl, totK_node, tot7098, tot7099]
  decide +kernel

theorem arows7091 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7091 = true := by
  rw [show D2M8K2.u7091 = KTree.node D2M8K2.t7100 (nat_lit 15032228) (nat_lit 2978264774) (nat_lit 0) D2M8K2.t7101 from rfl, allE_node, rows7100, irow7091, rows7101]
  all_goals rfl

theorem atot7091 : totK PD2M8K2 D2M8K2.u7091 = [0, 62729537426, 554140894489, 908070614606, 256418345681, 6032590049, 0, 0] := by
  rw [show D2M8K2.u7091 = KTree.node D2M8K2.t7100 (nat_lit 15032228) (nat_lit 2978264774) (nat_lit 0) D2M8K2.t7101 from rfl, totK_node, tot7100, tot7101]
  decide +kernel

theorem arows7092 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7092 = true := by
  rw [show D2M8K2.u7092 = KTree.node D2M8K2.t7102 (nat_lit 15034223) (nat_lit 1786730508) (nat_lit 0) D2M8K2.t7103 from rfl, allE_node, rows7102, irow7092, rows7103]
  all_goals rfl

theorem atot7092 : totK PD2M8K2 D2M8K2.u7092 = [0, 0, 392590592190, 948211086313, 408097342451, 22540691065, 0, 0] := by
  rw [show D2M8K2.u7092 = KTree.node D2M8K2.t7102 (nat_lit 15034223) (nat_lit 1786730508) (nat_lit 0) D2M8K2.t7103 from rfl, totK_node, tot7102, tot7103]
  decide +kernel

theorem arows7098 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7098 = true := by
  rw [show D2M8K2.u7098 = KTree.node D2M8K2.t7104 (nat_lit 15035522) (nat_lit 2660007903) (nat_lit 0) D2M8K2.t7105 from rfl, allE_node, rows7104, irow7098, rows7105]
  all_goals rfl

theorem atot7098 : totK PD2M8K2 D2M8K2.u7098 = [0, 0, 102372467501, 723505480490, 798956846810, 109170980512, 1206465782, 0] := by
  rw [show D2M8K2.u7098 = KTree.node D2M8K2.t7104 (nat_lit 15035522) (nat_lit 2660007903) (nat_lit 0) D2M8K2.t7105 from rfl, totK_node, tot7104, tot7105]
  decide +kernel

theorem arows7099 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7099 = true := by
  rw [show D2M8K2.u7099 = KTree.node D2M8K2.t7106 (nat_lit 15038235) (nat_lit 3766489105) (nat_lit 0) D2M8K2.t7107 from rfl, allE_node, rows7106, irow7099, rows7107]
  all_goals rfl

theorem atot7099 : totK PD2M8K2 D2M8K2.u7099 = [0, 0, 383523175070, 953967604593, 461156977342, 34481591454, 0, 0] := by
  rw [show D2M8K2.u7099 = KTree.node D2M8K2.t7106 (nat_lit 15038235) (nat_lit 3766489105) (nat_lit 0) D2M8K2.t7107 from rfl, totK_node, tot7106, tot7107]
  decide +kernel

theorem arows7101 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7101 = true := by
  rw [show D2M8K2.u7101 = KTree.node D2M8K2.t7108 (nat_lit 15041213) (nat_lit 2326292714) (nat_lit 0) D2M8K2.t7109 from rfl, allE_node, rows7108, irow7101, rows7109]
  all_goals rfl

theorem atot7101 : totK PD2M8K2 D2M8K2.u7101 = [0, 0, 381508382736, 958213587441, 449143086551, 28288117611, 0, 0] := by
  rw [show D2M8K2.u7101 = KTree.node D2M8K2.t7108 (nat_lit 15041213) (nat_lit 2326292714) (nat_lit 0) D2M8K2.t7109 from rfl, totK_node, tot7108, tot7109]
  decide +kernel

theorem arows7102 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7102 = true := by
  rw [show D2M8K2.u7102 = KTree.node D2M8K2.t7110 (nat_lit 15042880) (nat_lit 3775464034) (nat_lit 0) D2M8K2.t7111 from rfl, allE_node, rows7110, irow7102, rows7111]
  all_goals rfl

theorem atot7102 : totK PD2M8K2 D2M8K2.u7102 = [0, 0, 0, 506528727212, 932207868230, 276217276697, 13016197374, 0] := by
  rw [show D2M8K2.u7102 = KTree.node D2M8K2.t7110 (nat_lit 15042880) (nat_lit 3775464034) (nat_lit 0) D2M8K2.t7111 from rfl, totK_node, tot7110, tot7111]
  decide +kernel

theorem arows7105 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7105 = true := by
  rw [show D2M8K2.u7105 = KTree.node D2M8K2.t7112 (nat_lit 15048048) (nat_lit 3554229906) (nat_lit 0) D2M8K2.t7113 from rfl, allE_node, rows7112, irow7105, rows7113]
  all_goals rfl

theorem atot7105 : totK PD2M8K2 D2M8K2.u7105 = [0, 0, 407645636996, 938794157561, 407496669219, 25373923018, 0, 0] := by
  rw [show D2M8K2.u7105 = KTree.node D2M8K2.t7112 (nat_lit 15048048) (nat_lit 3554229906) (nat_lit 0) D2M8K2.t7113 from rfl, totK_node, tot7112, tot7113]
  decide +kernel

theorem arows7106 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7106 = true := by
  rw [show D2M8K2.u7106 = KTree.node D2M8K2.t7114 (nat_lit 15049842) (nat_lit 2467944486) (nat_lit 0) D2M8K2.t7115 from rfl, allE_node, rows7114, irow7106, rows7115]
  all_goals rfl

theorem atot7106 : totK PD2M8K2 D2M8K2.u7106 = [0, 0, 85071397234, 655777121005, 795418768592, 153919234009, 4574395652, 0] := by
  rw [show D2M8K2.u7106 = KTree.node D2M8K2.t7114 (nat_lit 15049842) (nat_lit 2467944486) (nat_lit 0) D2M8K2.t7115 from rfl, totK_node, tot7114, tot7115]
  decide +kernel

theorem arows7108 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7108 = true := by
  rw [show D2M8K2.u7108 = KTree.node D2M8K2.t7116 (nat_lit 15051726) (nat_lit 3235878806) (nat_lit 0) D2M8K2.t7117 from rfl, allE_node, rows7116, irow7108, rows7117]
  all_goals rfl

theorem atot7108 : totK PD2M8K2 D2M8K2.u7108 = [0, 39708786304, 384518891525, 892857496491, 473614357033, 32133299995, 0, 0] := by
  rw [show D2M8K2.u7108 = KTree.node D2M8K2.t7116 (nat_lit 15051726) (nat_lit 3235878806) (nat_lit 0) D2M8K2.t7117 from rfl, totK_node, tot7116, tot7117]
  decide +kernel

theorem arows7109 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7109 = true := by
  rw [show D2M8K2.u7109 = KTree.node D2M8K2.t7118 (nat_lit 15055338) (nat_lit 3849416377) (nat_lit 0) D2M8K2.t7119 from rfl, allE_node, rows7118, irow7109, rows7119]
  all_goals rfl

theorem atot7109 : totK PD2M8K2 D2M8K2.u7109 = [0, 378044131981, 949963244090, 436591336671, 23644192949, 0, 0, 0] := by
  rw [show D2M8K2.u7109 = KTree.node D2M8K2.t7118 (nat_lit 15055338) (nat_lit 3849416377) (nat_lit 0) D2M8K2.t7119 from rfl, totK_node, tot7118, tot7119]
  decide +kernel

theorem arows7113 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7113 = true := by
  rw [show D2M8K2.u7113 = KTree.node D2M8K2.t7120 (nat_lit 15057027) (nat_lit 3323687551) (nat_lit 0) D2M8K2.t7121 from rfl, allE_node, rows7120, irow7113, rows7121]
  all_goals rfl

theorem atot7113 : totK PD2M8K2 D2M8K2.u7113 = [0, 86950764009, 678535425160, 882092507982, 152300779010, 1369150432, 0, 0] := by
  rw [show D2M8K2.u7113 = KTree.node D2M8K2.t7120 (nat_lit 15057027) (nat_lit 3323687551) (nat_lit 0) D2M8K2.t7121 from rfl, totK_node, tot7120, tot7121]
  decide +kernel

theorem arows7114 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7114 = true := by
  rw [show D2M8K2.u7114 = KTree.node D2M8K2.t7122 (nat_lit 15065856) (nat_lit 3686612343) (nat_lit 0) D2M8K2.t7123 from rfl, allE_node, rows7122, irow7114, rows7123]
  all_goals rfl

theorem atot7114 : totK PD2M8K2 D2M8K2.u7114 = [0, 338816929651, 912900230771, 520759402727, 43972037487, 0, 0, 0] := by
  rw [show D2M8K2.u7114 = KTree.node D2M8K2.t7122 (nat_lit 15065856) (nat_lit 3686612343) (nat_lit 0) D2M8K2.t7123 from rfl, totK_node, tot7122, tot7123]
  decide +kernel

theorem arows7116 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7116 = true := by
  rw [show D2M8K2.u7116 = KTree.node D2M8K2.t7124 (nat_lit 15067530) (nat_lit 3714217506) (nat_lit 0) D2M8K2.t7125 from rfl, allE_node, rows7124, irow7116, rows7125]
  all_goals rfl

theorem atot7116 : totK PD2M8K2 D2M8K2.u7116 = [0, 70826781172, 499121196743, 898086623240, 294564776543, 13250685261, 0, 0] := by
  rw [show D2M8K2.u7116 = KTree.node D2M8K2.t7124 (nat_lit 15067530) (nat_lit 3714217506) (nat_lit 0) D2M8K2.t7125 from rfl, totK_node, tot7124, tot7125]
  decide +kernel

theorem arows7117 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7117 = true := by
  rw [show D2M8K2.u7117 = KTree.node D2M8K2.t7126 (nat_lit 15068982) (nat_lit 2842803436) (nat_lit 0) D2M8K2.t7127 from rfl, allE_node, rows7126, irow7117, rows7127]
  all_goals rfl

theorem atot7117 : totK PD2M8K2 D2M8K2.u7117 = [0, 327263126727, 921558068117, 503873021849, 33740645580, 0, 0, 0] := by
  rw [show D2M8K2.u7117 = KTree.node D2M8K2.t7126 (nat_lit 15068982) (nat_lit 2842803436) (nat_lit 0) D2M8K2.t7127 from rfl, totK_node, tot7126, tot7127]
  decide +kernel

theorem arows7120 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7120 = true := by
  rw [show D2M8K2.u7120 = KTree.node D2M8K2.t7128 (nat_lit 15070869) (nat_lit 1734668475) (nat_lit 0) D2M8K2.t7129 from rfl, allE_node, rows7128, irow7120, rows7129]
  all_goals rfl

theorem atot7120 : totK PD2M8K2 D2M8K2.u7120 = [0, 106934552672, 636231860026, 855692105681, 180572364722, 4980514959, 0, 0] := by
  rw [show D2M8K2.u7120 = KTree.node D2M8K2.t7128 (nat_lit 15070869) (nat_lit 1734668475) (nat_lit 0) D2M8K2.t7129 from rfl, totK_node, tot7128, tot7129]
  decide +kernel

theorem arows7121 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7121 = true := by
  rw [show D2M8K2.u7121 = KTree.node D2M8K2.t7130 (nat_lit 15072619) (nat_lit 1620840820) (nat_lit 0) D2M8K2.t7131 from rfl, allE_node, rows7130, irow7121, rows7131]
  all_goals rfl

theorem atot7121 : totK PD2M8K2 D2M8K2.u7121 = [0, 292673748609, 872918463011, 598073441817, 57893484598, 0, 0, 0] := by
  rw [show D2M8K2.u7121 = KTree.node D2M8K2.t7130 (nat_lit 15072619) (nat_lit 1620840820) (nat_lit 0) D2M8K2.t7131 from rfl, totK_node, tot7130, tot7131]
  decide +kernel

theorem arows7123 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7123 = true := by
  rw [show D2M8K2.u7123 = KTree.node D2M8K2.t7132 (nat_lit 15074450) (nat_lit 2634161186) (nat_lit 0) D2M8K2.t7133 from rfl, allE_node, rows7132, irow7123, rows7133]
  all_goals rfl

theorem atot7123 : totK PD2M8K2 D2M8K2.u7123 = [0, 0, 417464278313, 983925998992, 372728179171, 15385635356, 0, 0] := by
  rw [show D2M8K2.u7123 = KTree.node D2M8K2.t7132 (nat_lit 15074450) (nat_lit 2634161186) (nat_lit 0) D2M8K2.t7133 from rfl, totK_node, tot7132, tot7133]
  decide +kernel

theorem arows7124 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7124 = true := by
  rw [show D2M8K2.u7124 = KTree.node D2M8K2.t7134 (nat_lit 15076305) (nat_lit 1855832370) (nat_lit 0) D2M8K2.t7135 from rfl, allE_node, rows7134, irow7124, rows7135]
  all_goals rfl

theorem atot7124 : totK PD2M8K2 D2M8K2.u7124 = [0, 0, 314361942806, 911208427276, 484197829807, 32407597631, 0, 0] := by
  rw [show D2M8K2.u7124 = KTree.node D2M8K2.t7134 (nat_lit 15076305) (nat_lit 1855832370) (nat_lit 0) D2M8K2.t7135 from rfl, totK_node, tot7134, tot7135]
  decide +kernel

theorem arows7129 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7129 = true := by
  rw [show D2M8K2.u7129 = KTree.node D2M8K2.t7136 (nat_lit 15078365) (nat_lit 2061606479) (nat_lit 0) D2M8K2.t7137 from rfl, allE_node, rows7136, irow7129, rows7137]
  all_goals rfl

theorem atot7129 : totK PD2M8K2 D2M8K2.u7129 = [0, 0, 211300962780, 789416791851, 665685233090, 90996072340, 1239866073, 0] := by
  rw [show D2M8K2.u7129 = KTree.node D2M8K2.t7136 (nat_lit 15078365) (nat_lit 2061606479) (nat_lit 0) D2M8K2.t7137 from rfl, totK_node, tot7136, tot7137]
  decide +kernel

theorem arows7130 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7130 = true := by
  rw [show D2M8K2.u7130 = KTree.node D2M8K2.t7138 (nat_lit 15086961) (nat_lit 1624208752) (nat_lit 0) D2M8K2.t7139 from rfl, allE_node, rows7138, irow7130, rows7139]
  all_goals rfl

theorem atot7130 : totK PD2M8K2 D2M8K2.u7130 = [0, 0, 365087563779, 957560974698, 430792827725, 22816212044, 0, 0] := by
  rw [show D2M8K2.u7130 = KTree.node D2M8K2.t7138 (nat_lit 15086961) (nat_lit 1624208752) (nat_lit 0) D2M8K2.t7139 from rfl, totK_node, tot7138, tot7139]
  decide +kernel

theorem arows7132 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7132 = true := by
  rw [show D2M8K2.u7132 = KTree.node D2M8K2.t7140 (nat_lit 15090086) (nat_lit 4136063774) (nat_lit 0) D2M8K2.t7141 from rfl, allE_node, rows7140, irow7132, rows7141]
  all_goals rfl

theorem atot7132 : totK PD2M8K2 D2M8K2.u7132 = [0, 0, 390414083858, 951239118254, 410769161596, 18743059249, 0, 0] := by
  rw [show D2M8K2.u7132 = KTree.node D2M8K2.t7140 (nat_lit 15090086) (nat_lit 4136063774) (nat_lit 0) D2M8K2.t7141 from rfl, totK_node, tot7140, tot7141]
  decide +kernel

theorem arows7133 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7133 = true := by
  rw [show D2M8K2.u7133 = KTree.node D2M8K2.t7142 (nat_lit 15093458) (nat_lit 3289985481) (nat_lit 0) D2M8K2.t7143 from rfl, allE_node, rows7142, irow7133, rows7143]
  all_goals rfl

theorem atot7133 : totK PD2M8K2 D2M8K2.u7133 = [0, 90861460542, 471361545441, 799321773160, 420151717583, 28887941079, 0, 0] := by
  rw [show D2M8K2.u7133 = KTree.node D2M8K2.t7142 (nat_lit 15093458) (nat_lit 3289985481) (nat_lit 0) D2M8K2.t7143 from rfl, totK_node, tot7142, tot7143]
  decide +kernel

theorem arows7136 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7136 = true := by
  rw [show D2M8K2.u7136 = KTree.node D2M8K2.t7144 (nat_lit 15096965) (nat_lit 2302964739) (nat_lit 0) D2M8K2.t7145 from rfl, allE_node, rows7144, irow7136, rows7145]
  all_goals rfl

theorem atot7136 : totK PD2M8K2 D2M8K2.u7136 = [0, 327933263420, 893098371451, 515668835898, 40787854483, 0, 0, 0] := by
  rw [show D2M8K2.u7136 = KTree.node D2M8K2.t7144 (nat_lit 15096965) (nat_lit 2302964739) (nat_lit 0) D2M8K2.t7145 from rfl, totK_node, tot7144, tot7145]
  decide +kernel

theorem arows7137 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7137 = true := by
  rw [show D2M8K2.u7137 = KTree.node D2M8K2.t7146 (nat_lit 15098768) (nat_lit 3788156863) (nat_lit 0) D2M8K2.t7147 from rfl, allE_node, rows7146, irow7137, rows7147]
  all_goals rfl

theorem atot7137 : totK PD2M8K2 D2M8K2.u7137 = [0, 158665127972, 706878595074, 813610516597, 142558911601, 1369150432, 0, 0] := by
  rw [show D2M8K2.u7137 = KTree.node D2M8K2.t7146 (nat_lit 15098768) (nat_lit 3788156863) (nat_lit 0) D2M8K2.t7147 from rfl, totK_node, tot7146, tot7147]
  decide +kernel

theorem arows7139 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7139 = true := by
  rw [show D2M8K2.u7139 = KTree.node D2M8K2.t7148 (nat_lit 15100639) (nat_lit 2392619845) (nat_lit 0) D2M8K2.t7149 from rfl, allE_node, rows7148, irow7139, rows7149]
  all_goals rfl

theorem atot7139 : totK PD2M8K2 D2M8K2.u7139 = [0, 170964537079, 681924240325, 709157553175, 238615593185, 13908735795, 0, 0] := by
  rw [show D2M8K2.u7139 = KTree.node D2M8K2.t7148 (nat_lit 15100639) (nat_lit 2392619845) (nat_lit 0) D2M8K2.t7149 from rfl, totK_node, tot7148, tot7149]
  decide +kernel

theorem arows7140 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7140 = true := by
  rw [show D2M8K2.u7140 = KTree.node D2M8K2.t7150 (nat_lit 15102851) (nat_lit 2929600355) (nat_lit 0) D2M8K2.t7151 from rfl, allE_node, rows7150, irow7140, rows7151]
  all_goals rfl

theorem atot7140 : totK PD2M8K2 D2M8K2.u7140 = [0, 257037765869, 732574116619, 654729713530, 164170256157, 2554132940, 0, 0] := by
  rw [show D2M8K2.u7140 = KTree.node D2M8K2.t7150 (nat_lit 15102851) (nat_lit 2929600355) (nat_lit 0) D2M8K2.t7151 from rfl, totK_node, tot7150, tot7151]
  decide +kernel

theorem arows7144 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7144 = true := by
  rw [show D2M8K2.u7144 = KTree.node D2M8K2.t7152 (nat_lit 15104428) (nat_lit 3832638052) (nat_lit 0) D2M8K2.t7153 from rfl, allE_node, rows7152, irow7144, rows7153]
  all_goals rfl

theorem atot7144 : totK PD2M8K2 D2M8K2.u7144 = [0, 156854759878, 727228420512, 775104722304, 134189377376, 1164319620, 0, 0] := by
  rw [show D2M8K2.u7144 = KTree.node D2M8K2.t7152 (nat_lit 15104428) (nat_lit 3832638052) (nat_lit 0) D2M8K2.t7153 from rfl, totK_node, tot7152, tot7153]
  decide +kernel

theorem arows7145 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7145 = true := by
  rw [show D2M8K2.u7145 = KTree.node D2M8K2.t7154 (nat_lit 15106275) (nat_lit 2850104512) (nat_lit 0) D2M8K2.t7155 from rfl, allE_node, rows7154, irow7145, rows7155]
  all_goals rfl

theorem atot7145 : totK PD2M8K2 D2M8K2.u7145 = [0, 239754012038, 703213807910, 640673798845, 187707996332, 11885407614, 0, 0] := by
  rw [show D2M8K2.u7145 = KTree.node D2M8K2.t7154 (nat_lit 15106275) (nat_lit 2850104512) (nat_lit 0) D2M8K2.t7155 from rfl, totK_node, tot7154, tot7155]
  decide +kernel

theorem arows7147 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7147 = true := by
  rw [show D2M8K2.u7147 = KTree.node D2M8K2.t7156 (nat_lit 15107961) (nat_lit 1721021997) (nat_lit 0) D2M8K2.t7157 from rfl, allE_node, rows7156, irow7147, rows7157]
  all_goals rfl

theorem atot7147 : totK PD2M8K2 D2M8K2.u7147 = [0, 140433394095, 655064945377, 767631595150, 194805617823, 8214782009, 0, 0] := by
  rw [show D2M8K2.u7147 = KTree.node D2M8K2.t7156 (nat_lit 15107961) (nat_lit 1721021997) (nat_lit 0) D2M8K2.t7157 from rfl, totK_node, tot7156, tot7157]
  decide +kernel

theorem arows7148 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7148 = true := by
  rw [show D2M8K2.u7148 = KTree.node D2M8K2.t7158 (nat_lit 15109859) (nat_lit 2209608127) (nat_lit 0) D2M8K2.t7159 from rfl, allE_node, rows7158, irow7148, rows7159]
  all_goals rfl

theorem atot7148 : totK PD2M8K2 D2M8K2.u7148 = [0, 257539784197, 779233704988, 636311563269, 120216697276, 3581949829, 0, 0] := by
  rw [show D2M8K2.u7148 = KTree.node D2M8K2.t7158 (nat_lit 15109859) (nat_lit 2209608127) (nat_lit 0) D2M8K2.t7159 from rfl, totK_node, tot7158, tot7159]
  decide +kernel

theorem arows7151 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7151 = true := by
  rw [show D2M8K2.u7151 = KTree.node D2M8K2.t7160 (nat_lit 15111042) (nat_lit 2904283101) (nat_lit 0) D2M8K2.t7161 from rfl, allE_node, rows7160, irow7151, rows7161]
  all_goals rfl

theorem atot7151 : totK PD2M8K2 D2M8K2.u7151 = [0, 177806637211, 759491540526, 749767396290, 110990893737, 1096505104, 0, 0] := by
  rw [show D2M8K2.u7151 = KTree.node D2M8K2.t7160 (nat_lit 15111042) (nat_lit 2904283101) (nat_lit 0) D2M8K2.t7161 from rfl, totK_node, tot7160, tot7161]
  decide +kernel

theorem arows7152 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7152 = true := by
  rw [show D2M8K2.u7152 = KTree.node D2M8K2.t7162 (nat_lit 15116761) (nat_lit 1504782725) (nat_lit 0) D2M8K2.t7163 from rfl, allE_node, rows7162, irow7152, rows7163]
  all_goals rfl

theorem atot7152 : totK PD2M8K2 D2M8K2.u7152 = [0, 0, 399879745970, 958970366706, 379238613314, 19598320795, 0, 0] := by
  rw [show D2M8K2.u7152 = KTree.node D2M8K2.t7162 (nat_lit 15116761) (nat_lit 1504782725) (nat_lit 0) D2M8K2.t7163 from rfl, totK_node, tot7162, tot7163]
  decide +kernel

theorem arows7154 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7154 = true := by
  rw [show D2M8K2.u7154 = KTree.node D2M8K2.t7164 (nat_lit 15118356) (nat_lit 3232504522) (nat_lit 0) D2M8K2.t7165 from rfl, allE_node, rows7164, irow7154, rows7165]
  all_goals rfl

theorem atot7154 : totK PD2M8K2 D2M8K2.u7154 = [0, 0, 157928230636, 762760092597, 700642275561, 94370005351, 1138244013, 0] := by
  rw [show D2M8K2.u7154 = KTree.node D2M8K2.t7164 (nat_lit 15118356) (nat_lit 3232504522) (nat_lit 0) D2M8K2.t7165 from rfl, totK_node, tot7164, tot7165]
  decide +kernel

theorem arows7155 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7155 = true := by
  rw [show D2M8K2.u7155 = KTree.node D2M8K2.t7166 (nat_lit 15120840) (nat_lit 2437432902) (nat_lit 0) D2M8K2.t7167 from rfl, allE_node, rows7166, irow7155, rows7167]
  all_goals rfl

theorem atot7155 : totK PD2M8K2 D2M8K2.u7155 = [0, 0, 396864336873, 979142005832, 420313261957, 22765311390, 0, 0] := by
  rw [show D2M8K2.u7155 = KTree.node D2M8K2.t7166 (nat_lit 15120840) (nat_lit 2437432902) (nat_lit 0) D2M8K2.t7167 from rfl, totK_node, tot7166, tot7167]
  decide +kernel

theorem arows7165 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7165 = true := by
  rw [show D2M8K2.u7165 = KTree.node D2M8K2.t7168 (nat_lit 15124188) (nat_lit 3137731528) (nat_lit 0) D2M8K2.t7169 from rfl, allE_node, rows7168, irow7165, rows7169]
  all_goals rfl

theorem atot7165 : totK PD2M8K2 D2M8K2.u7165 = [0, 0, 344163345675, 943919815537, 474698788247, 27177940449, 0, 0] := by
  rw [show D2M8K2.u7165 = KTree.node D2M8K2.t7168 (nat_lit 15124188) (nat_lit 3137731528) (nat_lit 0) D2M8K2.t7169 from rfl, totK_node, tot7168, tot7169]
  decide +kernel

theorem arows7166 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7166 = true := by
  rw [show D2M8K2.u7166 = KTree.node D2M8K2.t7170 (nat_lit 15127896) (nat_lit 3472951092) (nat_lit 0) D2M8K2.t7171 from rfl, allE_node, rows7170, irow7166, rows7171]
  all_goals rfl

theorem atot7166 : totK PD2M8K2 D2M8K2.u7166 = [0, 0, 378480817657, 963763962521, 407251037158, 16280044044, 0, 0] := by
  rw [show D2M8K2.u7166 = KTree.node D2M8K2.t7170 (nat_lit 15127896) (nat_lit 3472951092) (nat_lit 0) D2M8K2.t7171 from rfl, totK_node, tot7170, tot7171]
  decide +kernel

theorem arows7168 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7168 = true := by
  rw [show D2M8K2.u7168 = KTree.node D2M8K2.t7172 (nat_lit 15130985) (nat_lit 1811774984) (nat_lit 0) D2M8K2.t7173 from rfl, allE_node, rows7172, irow7168, rows7173]
  all_goals rfl

theorem atot7168 : totK PD2M8K2 D2M8K2.u7168 = [0, 0, 384415038488, 929239680762, 427540962449, 27782110310, 0, 0] := by
  rw [show D2M8K2.u7168 = KTree.node D2M8K2.t7172 (nat_lit 15130985) (nat_lit 1811774984) (nat_lit 0) D2M8K2.t7173 from rfl, totK_node, tot7172, tot7173]
  decide +kernel

theorem arows7169 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7169 = true := by
  rw [show D2M8K2.u7169 = KTree.node D2M8K2.t7174 (nat_lit 15132698) (nat_lit 4194974439) (nat_lit 0) D2M8K2.t7175 from rfl, allE_node, rows7174, irow7169, rows7175]
  all_goals rfl

theorem atot7169 : totK PD2M8K2 D2M8K2.u7169 = [0, 55323524080, 122531787780, 596925072098, 783033728584, 174222252650, 4977114383, 0] := by
  rw [show D2M8K2.u7169 = KTree.node D2M8K2.t7174 (nat_lit 15132698) (nat_lit 4194974439) (nat_lit 0) D2M8K2.t7175 from rfl, totK_node, tot7174, tot7175]
  decide +kernel

theorem arows7172 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7172 = true := by
  rw [show D2M8K2.u7172 = KTree.node D2M8K2.t7176 (nat_lit 15138268) (nat_lit 3160758127) (nat_lit 0) D2M8K2.t7177 from rfl, allE_node, rows7176, irow7172, rows7177]
  all_goals rfl

theorem atot7172 : totK PD2M8K2 D2M8K2.u7172 = [0, 364088165195, 945045137270, 453488339471, 23633028269, 0, 0, 0] := by
  rw [show D2M8K2.u7172 = KTree.node D2M8K2.t7176 (nat_lit 15138268) (nat_lit 3160758127) (nat_lit 0) D2M8K2.t7177 from rfl, totK_node, tot7176, tot7177]
  decide +kernel

theorem arows7173 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7173 = true := by
  rw [show D2M8K2.u7173 = KTree.node D2M8K2.t7178 (nat_lit 15139970) (nat_lit 2021889793) (nat_lit 0) D2M8K2.t7179 from rfl, allE_node, rows7178, irow7173, rows7179]
  all_goals rfl

theorem atot7173 : totK PD2M8K2 D2M8K2.u7173 = [0, 89458300890, 656577047146, 900730238791, 165392682551, 1369150432, 0, 0] := by
  rw [show D2M8K2.u7173 = KTree.node D2M8K2.t7178 (nat_lit 15139970) (nat_lit 2021889793) (nat_lit 0) D2M8K2.t7179 from rfl, totK_node, tot7178, tot7179]
  decide +kernel

theorem arows7175 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7175 = true := by
  rw [show D2M8K2.u7175 = KTree.node D2M8K2.t7180 (nat_lit 15142211) (nat_lit 2900986281) (nat_lit 0) D2M8K2.t7181 from rfl, allE_node, rows7180, irow7175, rows7181]
  all_goals rfl

theorem atot7175 : totK PD2M8K2 D2M8K2.u7175 = [0, 243394625968, 763956943340, 628770579822, 186989790408, 19836217340, 0, 0] := by
  rw [show D2M8K2.u7175 = KTree.node D2M8K2.t7180 (nat_lit 15142211) (nat_lit 2900986281) (nat_lit 0) D2M8K2.t7181 from rfl, totK_node, tot7180, tot7181]
  decide +kernel

theorem arows7176 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7176 = true := by
  rw [show D2M8K2.u7176 = KTree.node D2M8K2.t7182 (nat_lit 15144037) (nat_lit 1319127410) (nat_lit 0) D2M8K2.t7183 from rfl, allE_node, rows7182, irow7176, rows7183]
  all_goals rfl

theorem atot7176 : totK PD2M8K2 D2M8K2.u7176 = [0, 166218900790, 610039845374, 751541702892, 282305255289, 11191207560, 0, 0] := by
  rw [show D2M8K2.u7176 = KTree.node D2M8K2.t7182 (nat_lit 15144037) (nat_lit 1319127410) (nat_lit 0) D2M8K2.t7183 from rfl, totK_node, tot7182, tot7183]
  decide +kernel

theorem arows7180 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7180 = true := by
  rw [show D2M8K2.u7180 = KTree.node D2M8K2.t7184 (nat_lit 15145596) (nat_lit 2924640070) (nat_lit 0) D2M8K2.t7185 from rfl, allE_node, rows7184, irow7180, rows7185]
  all_goals rfl

theorem atot7180 : totK PD2M8K2 D2M8K2.u7180 = [0, 248844839168, 783211399622, 667809559969, 104874801797, 1164319620, 0, 0] := by
  rw [show D2M8K2.u7180 = KTree.node D2M8K2.t7184 (nat_lit 15145596) (nat_lit 2924640070) (nat_lit 0) D2M8K2.t7185 from rfl, totK_node, tot7184, tot7185]
  decide +kernel

theorem arows7181 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7181 = true := by
  rw [show D2M8K2.u7181 = KTree.node D2M8K2.t7186 (nat_lit 15147317) (nat_lit 2201255366) (nat_lit 0) D2M8K2.t7187 from rfl, allE_node, rows7186, irow7181, rows7187]
  all_goals rfl

theorem atot7181 : totK PD2M8K2 D2M8K2.u7181 = [0, 151718351142, 650651603247, 765534232071, 221762454018, 11879463720, 0, 0] := by
  rw [show D2M8K2.u7181 = KTree.node D2M8K2.t7186 (nat_lit 15147317) (nat_lit 2201255366) (nat_lit 0) D2M8K2.t7187 from rfl, totK_node, tot7186, tot7187]
  decide +kernel

theorem arows7183 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7183 = true := by
  rw [show D2M8K2.u7183 = KTree.node D2M8K2.t7188 (nat_lit 15149117) (nat_lit 1906189095) (nat_lit 0) D2M8K2.t7189 from rfl, allE_node, rows7188, irow7183, rows7189]
  all_goals rfl

theorem atot7183 : totK PD2M8K2 D2M8K2.u7183 = [0, 230246001138, 769977259477, 681330823064, 113192481474, 1198073392, 0, 0] := by
  rw [show D2M8K2.u7183 = KTree.node D2M8K2.t7188 (nat_lit 15149117) (nat_lit 1906189095) (nat_lit 0) D2M8K2.t7189 from rfl, totK_node, tot7188, tot7189]
  decide +kernel

theorem arows7184 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7184 = true := by
  rw [show D2M8K2.u7184 = KTree.node D2M8K2.t7190 (nat_lit 15154578) (nat_lit 3395057874) (nat_lit 0) D2M8K2.t7191 from rfl, allE_node, rows7190, irow7184, rows7191]
  all_goals rfl

theorem atot7184 : totK PD2M8K2 D2M8K2.u7184 = [0, 208109424152, 735234992490, 718984975892, 154132073229, 4257574148, 0, 0] := by
  rw [show D2M8K2.u7184 = KTree.node D2M8K2.t7190 (nat_lit 15154578) (nat_lit 3395057874) (nat_lit 0) D2M8K2.t7191 from rfl, totK_node, tot7190, tot7191]
  decide +kernel

theorem arows7187 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7187 = true := by
  rw [show D2M8K2.u7187 = KTree.node D2M8K2.t7192 (nat_lit 15156057) (nat_lit 1489462598) (nat_lit 0) D2M8K2.t7193 from rfl, allE_node, rows7192, irow7187, rows7193]
  all_goals rfl

theorem atot7187 : totK PD2M8K2 D2M8K2.u7187 = [0, 231594451109, 782595807512, 678906815544, 115835178888, 1268739303, 0, 0] := by
  rw [show D2M8K2.u7187 = KTree.node D2M8K2.t7192 (nat_lit 15156057) (nat_lit 1489462598) (nat_lit 0) D2M8K2.t7193 from rfl, totK_node, tot7192, tot7193]
  decide +kernel

theorem arows7188 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7188 = true := by
  rw [show D2M8K2.u7188 = KTree.node D2M8K2.t7194 (nat_lit 15157738) (nat_lit 4015847179) (nat_lit 0) D2M8K2.t7195 from rfl, allE_node, rows7194, irow7188, rows7195]
  all_goals rfl

theorem atot7188 : totK PD2M8K2 D2M8K2.u7188 = [0, 0, 396310708727, 963020067079, 397412369567, 22149860293, 0, 0] := by
  rw [show D2M8K2.u7188 = KTree.node D2M8K2.t7194 (nat_lit 15157738) (nat_lit 4015847179) (nat_lit 0) D2M8K2.t7195 from rfl, totK_node, tot7194, tot7195]
  decide +kernel

theorem arows7190 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7190 = true := by
  rw [show D2M8K2.u7190 = KTree.node D2M8K2.t7196 (nat_lit 15159252) (nat_lit 3198538790) (nat_lit 0) D2M8K2.t7197 from rfl, allE_node, rows7196, irow7190, rows7197]
  all_goals rfl

theorem atot7190 : totK PD2M8K2 D2M8K2.u7190 = [0, 0, 305459282496, 892404976234, 523178193888, 37640647704, 0, 0] := by
  rw [show D2M8K2.u7190 = KTree.node D2M8K2.t7196 (nat_lit 15159252) (nat_lit 3198538790) (nat_lit 0) D2M8K2.t7197 from rfl, totK_node, tot7196, tot7197]
  decide +kernel

theorem arows7191 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7191 = true := by
  rw [show D2M8K2.u7191 = KTree.node D2M8K2.t7198 (nat_lit 15161262) (nat_lit 4008999428) (nat_lit 0) D2M8K2.t7199 from rfl, allE_node, rows7198, irow7191, rows7199]
  all_goals rfl

theorem atot7191 : totK PD2M8K2 D2M8K2.u7191 = [0, 0, 173716571837, 735212044591, 769591991728, 112946094811, 1310285577, 0] := by
  rw [show D2M8K2.u7191 = KTree.node D2M8K2.t7198 (nat_lit 15161262) (nat_lit 4008999428) (nat_lit 0) D2M8K2.t7199 from rfl, totK_node, tot7198, tot7199]
  decide +kernel

end QECKChecks.D2M8K2
